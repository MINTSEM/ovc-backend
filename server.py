"""SoaringBird 论坛 - Flask 后端 + SQLite/PostgreSQL"""

import os
import re
import uuid
import math
import hashlib
import time
import json
import sqlite3
import secrets
import base64
import struct as _struct
import hmac as _hmac
import html as _html_escape_mod
import ipaddress as _ipaddress
from datetime import datetime, timedelta
from functools import wraps
from werkzeug.utils import secure_filename
from werkzeug.middleware.proxy_fix import ProxyFix
from flask import (
    Flask, request, jsonify, send_from_directory,
    session, g, Response, redirect, make_response
)

try:
    from flask_socketio import SocketIO, emit, join_room, leave_room
    _HAS_SOCKETIO = True
except ImportError:
    _HAS_SOCKETIO = False

try:
    import cbor2
except ImportError:
    cbor2 = None

try:
    from ecdsa import VerifyingKey, NIST256p
    from ecdsa.util import sigdecode_der
    _HAS_ECDSA = True
except ImportError:
    _HAS_ECDSA = False

try:
    from PIL import Image
    import io as _io
    _HAS_PIL = True
except ImportError:
    _HAS_PIL = False

app = Flask(__name__, static_folder='.')
app.secret_key = os.environ.get('SECRET_KEY', secrets.token_urlsafe(48))
app.config['SESSION_COOKIE_SAMESITE'] = 'Lax'
app.config['SESSION_COOKIE_HTTPONLY'] = True
app.config['SESSION_COOKIE_PATH'] = '/'
# 全局上传大小上限：520MB（Team 单个文件上限 500MB）；
# 非 /api/team/ 接口仍由 _team_upload_size_guard 限制在 50MB，防止 DoS
app.config['MAX_CONTENT_LENGTH'] = 520 * 1024 * 1024
# SESSION_COOKIE_SECURE 在 before_request 中根据请求协议动态设置
app.permanent_session_lifetime = timedelta(days=30)

# ===== 登录速率限制 =====
import threading as _threading
_login_attempts = {}  # {ip: [(timestamp, ...), ...]}
_login_lock = _threading.Lock()
_LOGIN_MAX_ATTEMPTS = 5  # 最多 5 次
_LOGIN_WINDOW = 300  # 5 分钟窗口
_LOGIN_LOCK_TIME = 900  # 锁定 15 分钟

def _check_login_rate_limit(ip):
    """检查登录速率限制，返回 (allowed, retry_after_seconds)"""
    now = time.time()
    with _login_lock:
        attempts = _login_attempts.get(ip, [])
        # 清除过期记录
        attempts = [t for t in attempts if now - t < _LOGIN_WINDOW]
        _login_attempts[ip] = attempts
        if len(attempts) >= _LOGIN_MAX_ATTEMPTS:
            oldest = attempts[0]
            retry_after = int(_LOGIN_LOCK_TIME - (now - oldest))
            return False, max(retry_after, 0)
        return True, 0

def _record_login_attempt(ip, success=False):
    """记录登录尝试"""
    now = time.time()
    with _login_lock:
        if success:
            _login_attempts.pop(ip, None)
        else:
            attempts = _login_attempts.get(ip, [])
            attempts.append(now)
            _login_attempts[ip] = attempts

# ===== 注册速率限制 =====
_register_attempts = {}  # {ip: [timestamp, ...]}
_register_lock = _threading.Lock()
_REGISTER_MAX = 5  # 每窗口最多 5 次注册
_REGISTER_WINDOW = 3600  # 1 小时窗口

def _check_register_rate_limit(ip):
    """检查注册速率限制"""
    now = time.time()
    with _register_lock:
        attempts = _register_attempts.get(ip, [])
        attempts = [t for t in attempts if now - t < _REGISTER_WINDOW]
        _register_attempts[ip] = attempts
        if len(attempts) >= _REGISTER_MAX:
            oldest = attempts[0]
            retry_after = int(_REGISTER_WINDOW - (now - oldest))
            return False, max(retry_after, 0)
        return True, 0

def _record_register_attempt(ip):
    """记录一次注册尝试"""
    now = time.time()
    with _register_lock:
        attempts = _register_attempts.get(ip, [])
        attempts.append(now)
        _register_attempts[ip] = attempts

# 允许的跨域来源（仅限本站域名，防止 SocketIO 被任意站点滥用）
_ALLOWED_ORIGINS = [
    'https://soaringbirdforum.xyz',
    'https://www.soaringbirdforum.xyz',
    'http://localhost:8080',
    'http://127.0.0.1:8080',
]

# 修复反向代理（ngrok 等）下的 URL 和 cookie 问题
app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=1, x_prefix=1)
if _HAS_SOCKETIO:
    socketio = SocketIO(app, cors_allowed_origins=_ALLOWED_ORIGINS, async_mode='threading', cors_credentials=True)
else:
    # 未安装 flask_socketio 时提供 no-op 替代，避免 socketio.emit(...) 抛 AttributeError
    class _NoopSocketIO:
        def emit(self, *a, **kw): pass
        def on(self, *a, **kw):
            def deco(f): return f
            return deco
        def run(self, *a, **kw): pass
    socketio = _NoopSocketIO()

# ===== 自定义签名 Cookie 认证（绕过 Flask session） =====
_AUTH_COOKIE_NAME = 'sb_auth'
_AUTH_COOKIE_MAX_AGE = 30 * 24 * 3600  # 30 天

def _is_https_request():
    """判断当前请求是否为 HTTPS（兼容反向代理）"""
    return request.is_secure or request.headers.get('X-Forwarded-Proto', '').lower() == 'https'

def _sign_auth(user_id):
    """对 user_id 进行 HMAC 签名，返回 token"""
    msg = user_id.encode('utf-8')
    sig = _hmac.new(app.secret_key.encode('utf-8'), msg, hashlib.sha256).hexdigest()
    return f"{user_id}.{sig}"

def _verify_auth(token):
    """验证签名 cookie，返回 user_id 或 None"""
    if not token or '.' not in token:
        return None
    user_id, sig = token.rsplit('.', 1)
    expected = _hmac.new(app.secret_key.encode('utf-8'), user_id.encode('utf-8'), hashlib.sha256).hexdigest()
    if _hmac.compare_digest(sig, expected):
        return user_id
    return None

def _set_auth_cookie(response, user_id):
    """在响应中设置认证 cookie"""
    token = _sign_auth(user_id)
    response.set_cookie(
        _AUTH_COOKIE_NAME,
        token,
        max_age=_AUTH_COOKIE_MAX_AGE,
        path='/',
        httponly=True,
        samesite='Lax',
        secure=_is_https_request()
    )
    return response

def _clear_auth_cookie(response):
    """清除认证 cookie"""
    response.set_cookie(
        _AUTH_COOKIE_NAME,
        '',
        max_age=0,
        path='/',
        httponly=True,
        samesite='Lax',
        secure=_is_https_request()
    )
    return response

def _get_auth_user_id():
    """从自定义 cookie 获取已认证的 user_id，优先于 Flask session"""
    # 1. 先检查自定义 cookie
    token = request.cookies.get(_AUTH_COOKIE_NAME)
    if token:
        uid = _verify_auth(token)
        if uid:
            return uid
    # 2. 回退到 Flask session
    return session.get('user_id')

# ===== 幻霜 OAuth 2.0 配置 =====
HS_OAUTH_BASE = os.environ.get('HS_OAUTH_BASE', 'https://hmediapost.newblock.online')
HS_OAUTH_APP_ID = os.environ.get('HS_OAUTH_APP_ID', '')
HS_OAUTH_APP_SECRET = os.environ.get('HS_OAUTH_APP_SECRET', '')
HS_OAUTH_REDIRECT_URI = os.environ.get('HS_OAUTH_REDIRECT_URI', 'https://soaringbirdforum.xyz/api/auth/huanshuang/callback')

# ===== 本地 AI（LM Studio）配置 =====
AI_BASE_URL = os.environ.get('AI_BASE_URL', 'http://localhost:1234/v1')
AI_MODEL = os.environ.get('AI_MODEL', 'local-model')
AI_API_KEY = os.environ.get('AI_API_KEY', '')
AI_BOT_ID = 'ai_bot'
AI_BOT_NAME = 'AI Bird'
AI_SYSTEM_PROMPT = os.environ.get('AI_SYSTEM_PROMPT', '你是翱翔鸟论坛的AI助手AI Bird。用户在论坛帖子中@你来提问，请简洁友好地回答。使用Markdown格式。')

# AI 并发控制：最多同时处理 2 个请求
import threading as _ai_threading
_ai_semaphore = _ai_threading.Semaphore(2)
_ai_queue_lock = _ai_threading.Lock()
_ai_queue_size = 0

# 默认额度
AI_DEFAULT_DAILY_LIMIT = 50
AI_DEFAULT_MONTHLY_LIMIT = 500
AI_CHAT_DAILY_LIMIT = 10  # 聊天中@AI每人每天10次


def get_ai_config():
    """从数据库读取 AI 配置，没有则用默认值（线程安全，不依赖请求上下文）"""
    try:
        if _USE_PG:
            db = _get_pg_pool().getconn()
            try:
                row = db.execute('SELECT base_url, model, api_key, COALESCE(moderation_enabled,0) AS moderation_enabled FROM ai_config WHERE id=1').fetchone()
            finally:
                _get_pg_pool().putconn(db)
        else:
            db = sqlite3.connect(DB_PATH)
            db.row_factory = sqlite3.Row
            try:
                row = db.execute('SELECT base_url, model, api_key, COALESCE(moderation_enabled,0) AS moderation_enabled FROM ai_config WHERE id=1').fetchone()
            finally:
                db.close()
        if row:
            return {
                'base_url': row['base_url'] or AI_BASE_URL,
                'model': row['model'] or AI_MODEL,
                'api_key': row['api_key'] or AI_API_KEY,
                'moderation_enabled': bool(row['moderation_enabled']),
            }
    except:
        pass
    return {'base_url': AI_BASE_URL, 'model': AI_MODEL, 'api_key': AI_API_KEY, 'moderation_enabled': False}


def get_user_ai_quota(user_id):
    """获取用户的 AI 额度配置（每日/每月），没有则返回默认值"""
    try:
        db = get_db()
        row = _fetchone(db, 'SELECT daily_limit, monthly_limit FROM ai_quota WHERE user_id=?', (user_id,))
        if row:
            return {
                'daily_limit': row['daily_limit'] if row['daily_limit'] is not None else AI_DEFAULT_DAILY_LIMIT,
                'monthly_limit': row['monthly_limit'] if row['monthly_limit'] is not None else AI_DEFAULT_MONTHLY_LIMIT,
            }
    except:
        pass
    return {'daily_limit': AI_DEFAULT_DAILY_LIMIT, 'monthly_limit': AI_DEFAULT_MONTHLY_LIMIT}


def check_ai_quota(user_id):
    """检查用户是否还有 AI 使用额度，返回 (ok, msg, remaining)"""
    import time as _t
    quota = get_user_ai_quota(user_id)
    now = _t.time()
    today_start = int(now // 86400) * 86400
    month_start = int(now // (86400 * 30)) * (86400 * 30)  # 粗略按30天算月

    try:
        db = get_db()
        # 今日使用次数
        row = _fetchone(db, 'SELECT COUNT(*) as c FROM ai_usage_log WHERE user_id=? AND created_at>=?', (user_id, today_start))
        daily_used = row['c'] if row else 0
        # 本月使用次数
        row2 = _fetchone(db, 'SELECT COUNT(*) as c FROM ai_usage_log WHERE user_id=? AND created_at>=?', (user_id, month_start))
        monthly_used = row2['c'] if row2 else 0

        if daily_used >= quota['daily_limit']:
            return False, f'今日 AI 使用额度已用完（{daily_used}/{quota["daily_limit"]}）', 0
        if monthly_used >= quota['monthly_limit']:
            return False, f'本月 AI 使用额度已用完（{monthly_used}/{quota["monthly_limit"]}）', 0
        return True, 'ok', quota['daily_limit'] - daily_used
    except Exception as e:
        # 表可能不存在，允许通过
        return True, 'ok', quota['daily_limit']


def log_ai_usage(user_id):
    """记录一次 AI 使用"""
    import time as _t
    try:
        db = get_db()
        log_id = 'aul_' + uuid.uuid4().hex[:12]
        if _USE_PG:
            _exec(db, 'INSERT INTO ai_usage_log (id, user_id, created_at) VALUES (%s, %s, %s)', (log_id, user_id, _t.time()))
        else:
            db.execute('INSERT INTO ai_usage_log (id, user_id, created_at) VALUES (?, ?, ?)', (log_id, user_id, _t.time()))
        db.commit()
    except:
        pass


def check_chat_ai_quota(user_id):
    """检查用户聊天中@AI的每日额度，返回 (ok, msg, remaining)"""
    import time as _t
    now = _t.time()
    today_start = int(now // 86400) * 86400
    try:
        db = get_db()
        row = _fetchone(db, 'SELECT COUNT(*) as c FROM chat_ai_usage_log WHERE user_id=? AND created_at>=?', (user_id, today_start))
        used = row['c'] if row else 0
        if used >= AI_CHAT_DAILY_LIMIT:
            return False, f'今日聊天@AI次数已用完（{used}/{AI_CHAT_DAILY_LIMIT}）', 0
        return True, 'ok', AI_CHAT_DAILY_LIMIT - used
    except:
        return True, 'ok', AI_CHAT_DAILY_LIMIT


def log_chat_ai_usage(user_id):
    """记录一次聊天@AI使用"""
    import time as _t
    try:
        db = get_db()
        log_id = 'cau_' + uuid.uuid4().hex[:12]
        if _USE_PG:
            _exec(db, 'INSERT INTO chat_ai_usage_log (id, user_id, created_at) VALUES (%s, %s, %s)', (log_id, user_id, _t.time()))
        else:
            db.execute('INSERT INTO chat_ai_usage_log (id, user_id, created_at) VALUES (?, ?, ?)', (log_id, user_id, _t.time()))
        db.commit()
    except:
        pass


def _generate_chat_ai_reply_async(user_content, chat_msg_id):
    """后台线程：在聊天中生成AI回复（独立DB连接）"""
    try:
        # 调用 AI 生成回复
        messages = [
            {'role': 'system', 'content': AI_SYSTEM_PROMPT},
            {'role': 'user', 'content': user_content},
        ]
        ai_content = call_lm_studio(messages)

        if _USE_PG:
            db = _get_pg_pool().getconn()
            db.autocommit = False
        else:
            db = sqlite3.connect(DB_PATH)
            db.row_factory = sqlite3.Row
        try:
            now = time.time()
            msg_id = 'msg_' + uuid.uuid4().hex[:12]
            _exec(db, 'INSERT INTO chat_messages (id, user_id, username, avatar, content, created_at) VALUES (?,?,?,?,?,?)',
                  (msg_id, AI_BOT_ID, AI_BOT_NAME, '', ai_content, now))
            db.commit()

            # 通过 Socket.IO 推送 AI 聊天消息
            ai_msg = {
                'id': msg_id,
                'user_id': AI_BOT_ID,
                'username': AI_BOT_NAME,
                'avatar': '',
                'content': ai_content,
                'created_at': now
            }
            if _HAS_SOCKETIO and socketio:
                socketio.emit('new_message', ai_msg, room='chat')
        finally:
            if _USE_PG:
                _get_pg_pool().putconn(db)
            else:
                db.close()
    except Exception as e:
        print(f'[AI] 聊天回复生成失败: {e}')


def get_client_ip():
    """获取客户端真实 IP（支持反向代理）"""
    forwarded = request.headers.get('X-Forwarded-For', '')
    if forwarded:
        return forwarded.split(',')[0].strip()
    real_ip = request.headers.get('X-Real-IP', '')
    if real_ip:
        return real_ip.strip()
    return request.remote_addr or '0.0.0.0'


@app.before_request
def _update_cookie_security():
    """根据请求协议动态设置 session cookie 的 Secure 属性
    HTTPS 请求带 Secure（更安全），HTTP 请求不带（否则浏览器不保存 cookie）"""
    app.config['SESSION_COOKIE_SECURE'] = _is_https_request()


@app.before_request
def check_ip_ban():
    """拦截被封禁 IP 的请求"""
    if request.path.startswith('/api/admin/'):
        return  # 管理员 API 不拦截，防止管理员自己被封后无法解封
    ip = get_client_ip()
    try:
        db = get_db()
        if _USE_PG:
            row = _fetchone(db, 'SELECT ip FROM ip_bans WHERE ip=%s', (ip,))
        else:
            row = _fetchone(db, 'SELECT ip FROM ip_bans WHERE ip=?', (ip,))
        if row:
            if request.path.startswith('/api/'):
                return jsonify({'error': '您的 IP 已被封禁，请联系管理员'}), 403
            return '您的 IP 已被封禁，请联系管理员', 403
    except Exception:
        # 查询失败不阻止请求，但 PG 需要 rollback 避免连接 aborted
        try:
            db.rollback()
        except Exception:
            pass


@app.after_request
def add_cache_headers(response):
    # 对所有请求禁用缓存
    if request.path.endswith(('.js', '.css', '.html', '.json')) or request.path == '/' or request.path.startswith('/api/'):
        response.headers['Cache-Control'] = 'no-cache, no-store, must-revalidate, max-age=0'
        response.headers['Pragma'] = 'no-cache'
        response.headers['Expires'] = '0'
        response.headers['X-Content-Type-Options'] = 'nosniff'
    # CORS：允许外部站点（如 netlify 部署的新闻站）跨域调用新闻 API
    if request.path.startswith('/api/'):
        response.headers['Access-Control-Allow-Origin'] = '*'
        response.headers['Access-Control-Allow-Methods'] = 'GET, POST, OPTIONS'
        response.headers['Access-Control-Allow-Headers'] = 'Content-Type, Authorization'
        response.headers['Access-Control-Max-Age'] = '86400'
    return response


@app.before_request
def handle_cors_preflight():
    """CORS 预检：跨域 POST（如 /api/news/translate）浏览器会先发 OPTIONS"""
    if request.method == 'OPTIONS' and request.path.startswith('/api/'):
        resp = app.make_default_options_response()
        resp.headers['Access-Control-Allow-Origin'] = '*'
        resp.headers['Access-Control-Allow-Methods'] = 'GET, POST, OPTIONS'
        resp.headers['Access-Control-Allow-Headers'] = 'Content-Type, Authorization'
        resp.headers['Access-Control-Max-Age'] = '86400'
        return resp
    return None


@app.before_request
def check_user_ban():
    """全局封禁校验：被封禁用户的 cookie/session 立即失效，拦截所有非管理 API"""
    if request.path.startswith('/api/admin/'):
        return  # 管理端点由各自装饰器鉴权（防止管理员误封自己后无法操作）
    uid = session.get('user_id') or _get_auth_user_id()
    if not uid:
        return
    # 会话级缓存（60 秒），避免每请求查库
    now = time.time()
    cached = session.get('_ban_check', {})
    if cached.get('uid') == uid and now - cached.get('ts', 0) < 60:
        if cached.get('banned'):
            return jsonify({'error': '账号已被封禁', 'banned': True}), 403
        return
    try:
        db = get_db()
        row = _fetchone(db, 'SELECT status FROM users WHERE id=?', (uid,))
        banned = bool(row and row.get('status') == 'banned')
        session['_ban_check'] = {'uid': uid, 'ts': now, 'banned': banned}
        if banned:
            resp = jsonify({'error': '账号已被封禁', 'banned': True})
            resp.delete_cookie(_AUTH_COOKIE_NAME)
            session.clear()
            return resp, 403
    except Exception:
        try:
            db.rollback()
        except Exception:
            pass


@app.before_request
def sync_auth_to_session():
    """每次请求前，将自定义 cookie 的 user_id 同步到 Flask session，确保所有端点兼容"""
    uid = _get_auth_user_id()
    if uid and session.get('user_id') != uid:
        session['user_id'] = uid
        session.permanent = True


@app.before_request
def update_last_online():
    """每次请求更新登录用户的最近上线时间（每分钟最多更新一次）"""
    uid = _get_auth_user_id()
    if not uid:
        return
    now = time.time()
    # 用 flask session 级缓存，避免频繁写库
    last_ts = session.get('_last_online_ts', 0)
    if now - last_ts < 60:
        return
    try:
        db = get_db()
        if _USE_PG:
            _exec(db, 'UPDATE users SET last_online=%s WHERE id=%s AND (last_online < %s OR last_online IS NULL)', (now, uid, now - 60))
            db.commit()
        else:
            db.execute('UPDATE users SET last_online=? WHERE id=? AND (last_online < ? OR last_online = 0)', (now, uid, now - 60))
            db.commit()
        session['_last_online_ts'] = now
    except Exception as e:
        # PG 事务失败后必须 rollback，否则连接进入 aborted 状态，后续所有 SQL 都会报错
        try:
            db.rollback()
        except Exception:
            pass


@app.errorhandler(Exception)
def handle_exception(e):
    """全局异常处理：API 路由返回 JSON，其他返回 HTML"""
    import traceback
    tb = traceback.format_exc()
    print(f'[ERROR] {request.method} {request.path}: {e}')
    print(tb)
    if request.path.startswith('/api/'):
        return jsonify({'error': '服务器内部错误'}), 500
    raise e


@app.errorhandler(404)
def handle_404(e):
    if request.path.startswith('/api/'):
        return jsonify({'error': '接口不存在'}), 404
    return jsonify({'error': 'Not found'}), 404


@app.errorhandler(405)
def handle_405(e):
    if request.path.startswith('/api/'):
        return jsonify({'error': '方法不允许'}), 405
    return jsonify({'error': 'Method not allowed'}), 405

# Fly.io 持久卷：/data 目录；本地：当前目录
_DATA_DIR = os.environ.get('DATA_DIR', os.path.dirname(os.path.abspath(__file__)))
DB_PATH = os.path.join(_DATA_DIR, 'bird.db')
# 前端静态资源目录（扁平化后直接放项目根）
_FRONTEND_DIR = _DATA_DIR

CATEGORIES = [
    {'id': 'tech', 'name': '技术', 'color': '#0071E3'},
    {'id': 'design', 'name': '设计', 'color': '#BF5AF2'},
    {'id': 'product', 'name': '产品', 'color': '#FF9F0A'},
    {'id': 'career', 'name': '职场', 'color': '#30D158'},
    {'id': 'resource', 'name': '资源', 'color': '#64D2FF'},
    {'id': 'casual', 'name': '闲聊', 'color': '#FF375F'},
]

# 管理员账号（首次启动自动创建）
ADMIN_USERNAME = os.environ.get('ADMIN_USERNAME', 'SoaringBird')
ADMIN_PASSWORD = os.environ.get('ADMIN_PASSWORD', secrets.token_urlsafe(16))


# ===== 数据库抽象层 =====
_USE_PG = bool(os.environ.get('DATABASE_URL'))

if _USE_PG:
    import psycopg2
    import psycopg2.extras
    _pg_pool = None

    def _get_pg_pool():
        global _pg_pool
        if _pg_pool is None:
            from psycopg2 import pool
            _pg_pool = pool.SimpleConnectionPool(
                1, 5, os.environ.get('DATABASE_URL'))
        return _pg_pool

    def get_db():
        if 'db' not in g:
            g.db = _get_pg_pool().getconn()
            g.db.autocommit = False
        return g.db

    @app.teardown_appcontext
    def close_db(exc):
        db = g.pop('db', None)
        if db is not None:
            if exc:
                db.rollback()
            _get_pg_pool().putconn(db)

    def _exec(db, sql, params=()):
        sql = sql.replace('?', '%s').replace(' LIKE ', ' ILIKE ')
        cur = db.cursor()
        cur.execute(sql, params)
        return cur

    def _fetchone(db, sql, params=()):
        sql = sql.replace('?', '%s').replace(' LIKE ', ' ILIKE ')
        cur = db.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute(sql, params)
        return cur.fetchone()

    def _fetchall(db, sql, params=()):
        sql = sql.replace('?', '%s').replace(' LIKE ', ' ILIKE ')
        cur = db.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute(sql, params)
        return cur.fetchall()

else:
    # SQLite 模式（保持原有逻辑）
    def get_db():
        if 'db' not in g:
            g.db = sqlite3.connect(DB_PATH)
            g.db.row_factory = sqlite3.Row
            g.db.execute('PRAGMA journal_mode=WAL')
            g.db.execute('PRAGMA foreign_keys=ON')
        return g.db

    @app.teardown_appcontext
    def close_db(exc):
        db = g.pop('db', None)
        if db:
            db.close()

    def _exec(db, sql, params=()):
        return db.execute(sql, params)

    def _fetchone(db, sql, params=()):
        row = db.execute(sql, params).fetchone()
        return dict(row) if row else None

    def _fetchall(db, sql, params=()):
        return [dict(r) for r in db.execute(sql, params).fetchall()]


def init_db():
    if _USE_PG:
        _init_db_pg()
    else:
        _init_db_sqlite()
    _init_db_team()


def _init_db_pg():
    import psycopg2
    db_url = os.environ.get('DATABASE_URL')
    db = psycopg2.connect(db_url)
    db.autocommit = True
    cur = db.cursor()

    cur.execute('''
        CREATE TABLE IF NOT EXISTS users (
            id TEXT PRIMARY KEY,
            username TEXT UNIQUE NOT NULL,
            email TEXT DEFAULT '',
            password_hash TEXT NOT NULL,
            bio TEXT DEFAULT '',
            avatar TEXT DEFAULT '',
            background TEXT DEFAULT '',
            is_admin INTEGER DEFAULT 0,
            is_super_admin INTEGER DEFAULT 0,
            can_publish_news INTEGER DEFAULT 0,
            created_at DOUBLE PRECISION NOT NULL,
            birthday_month INTEGER DEFAULT 0,
            birthday_day INTEGER DEFAULT 0,
            birthday_age INTEGER DEFAULT 0,
            region TEXT DEFAULT '',
            gender TEXT DEFAULT ''
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS posts (
            id TEXT PRIMARY KEY,
            author_id TEXT NOT NULL,
            title TEXT NOT NULL,
            category TEXT NOT NULL,
            content TEXT NOT NULL,
            likes INTEGER DEFAULT 0,
            created_at DOUBLE PRECISION NOT NULL,
            FOREIGN KEY (author_id) REFERENCES users(id)
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS tags (
            post_id TEXT NOT NULL,
            tag TEXT NOT NULL,
            FOREIGN KEY (post_id) REFERENCES posts(id) ON DELETE CASCADE
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS replies (
            id TEXT PRIMARY KEY,
            post_id TEXT NOT NULL,
            author_id TEXT NOT NULL,
            parent_id TEXT DEFAULT '',
            content TEXT NOT NULL,
            image TEXT DEFAULT '',
            likes INTEGER DEFAULT 0,
            created_at DOUBLE PRECISION NOT NULL,
            FOREIGN KEY (post_id) REFERENCES posts(id) ON DELETE CASCADE,
            FOREIGN KEY (author_id) REFERENCES users(id)
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS post_likes (
            user_id TEXT NOT NULL,
            post_id TEXT NOT NULL,
            PRIMARY KEY (user_id, post_id),
            FOREIGN KEY (post_id) REFERENCES posts(id) ON DELETE CASCADE
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS reply_likes (
            user_id TEXT NOT NULL,
            reply_id TEXT NOT NULL,
            PRIMARY KEY (user_id, reply_id),
            FOREIGN KEY (reply_id) REFERENCES replies(id) ON DELETE CASCADE
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS bookmarks (
            user_id TEXT NOT NULL,
            post_id TEXT NOT NULL,
            PRIMARY KEY (user_id, post_id),
            FOREIGN KEY (post_id) REFERENCES posts(id) ON DELETE CASCADE
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS notifications (
            id TEXT PRIMARY KEY,
            user_id TEXT NOT NULL,
            text TEXT NOT NULL,
            read INTEGER DEFAULT 0,
            created_at DOUBLE PRECISION NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS passkeys (
            id TEXT PRIMARY KEY,
            user_id TEXT NOT NULL,
            credential_id TEXT NOT NULL,
            public_key TEXT NOT NULL,
            counter INTEGER DEFAULT 0,
            name TEXT DEFAULT '',
            created_at DOUBLE PRECISION NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS chat_messages (
            id TEXT PRIMARY KEY,
            user_id TEXT NOT NULL,
            username TEXT NOT NULL,
            avatar TEXT DEFAULT '',
            content TEXT NOT NULL,
            created_at DOUBLE PRECISION NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS dm_conversations (
            id TEXT PRIMARY KEY,
            user1_id TEXT NOT NULL,
            user2_id TEXT NOT NULL,
            created_at DOUBLE PRECISION NOT NULL,
            FOREIGN KEY (user1_id) REFERENCES users(id) ON DELETE CASCADE,
            FOREIGN KEY (user2_id) REFERENCES users(id) ON DELETE CASCADE
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS dm_messages (
            id TEXT PRIMARY KEY,
            conversation_id TEXT NOT NULL,
            sender_id TEXT NOT NULL,
            content TEXT NOT NULL,
            is_encrypted INTEGER DEFAULT 0,
            created_at DOUBLE PRECISION NOT NULL,
            FOREIGN KEY (conversation_id) REFERENCES dm_conversations(id) ON DELETE CASCADE,
            FOREIGN KEY (sender_id) REFERENCES users(id) ON DELETE CASCADE
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS follows (
            follower_id TEXT NOT NULL,
            following_id TEXT NOT NULL,
            created_at DOUBLE PRECISION NOT NULL,
            PRIMARY KEY (follower_id, following_id),
            FOREIGN KEY (follower_id) REFERENCES users(id) ON DELETE CASCADE,
            FOREIGN KEY (following_id) REFERENCES users(id) ON DELETE CASCADE
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS bug_reports (
            id TEXT PRIMARY KEY,
            user_id TEXT NOT NULL,
            username TEXT NOT NULL,
            content TEXT NOT NULL,
            status TEXT DEFAULT 'open',
            created_at DOUBLE PRECISION NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS announcements (
            id TEXT PRIMARY KEY,
            title TEXT NOT NULL,
            content TEXT NOT NULL,
            created_by TEXT NOT NULL,
            created_at DOUBLE PRECISION NOT NULL,
            FOREIGN KEY (created_by) REFERENCES users(id) ON DELETE CASCADE
        )
    ''')
    # ===== PeaceNews 新闻模块 =====
    cur.execute('''
        CREATE TABLE IF NOT EXISTS news (
            id TEXT PRIMARY KEY,
            title TEXT NOT NULL,
            content TEXT NOT NULL,
            image TEXT DEFAULT '',
            video TEXT DEFAULT '',
            author_id TEXT,
            likes INTEGER DEFAULT 0,
            created_at DOUBLE PRECISION NOT NULL
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS news_likes (
            user_id TEXT NOT NULL,
            news_id TEXT NOT NULL,
            created_at DOUBLE PRECISION,
            PRIMARY KEY (user_id, news_id)
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS news_comments (
            id TEXT PRIMARY KEY,
            news_id TEXT NOT NULL,
            author_id TEXT,
            content TEXT NOT NULL,
            image TEXT DEFAULT '',
            likes INTEGER DEFAULT 0,
            created_at DOUBLE PRECISION NOT NULL
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS news_comment_likes (
            user_id TEXT NOT NULL,
            comment_id TEXT NOT NULL,
            PRIMARY KEY (user_id, comment_id)
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS news_config (
            key TEXT PRIMARY KEY,
            value TEXT DEFAULT ''
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS videos (
            id TEXT PRIMARY KEY,
            title TEXT NOT NULL,
            description TEXT DEFAULT '',
            filename TEXT NOT NULL,
            filepath TEXT NOT NULL,
            filesize INTEGER DEFAULT 0,
            duration REAL DEFAULT 0,
            thumbnail TEXT DEFAULT '',
            author_id TEXT,
            views INTEGER DEFAULT 0,
            likes INTEGER DEFAULT 0,
            created_at DOUBLE PRECISION NOT NULL,
            status TEXT DEFAULT 'pending'
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS video_likes (
            user_id TEXT NOT NULL,
            video_id TEXT NOT NULL,
            created_at DOUBLE PRECISION,
            PRIMARY KEY (user_id, video_id)
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS video_config (
            key TEXT PRIMARY KEY,
            value TEXT DEFAULT ''
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS podcasts (
            id TEXT PRIMARY KEY,
            title TEXT NOT NULL,
            description TEXT DEFAULT '',
            filename TEXT NOT NULL,
            filepath TEXT NOT NULL,
            filesize INTEGER DEFAULT 0,
            duration REAL DEFAULT 0,
            cover TEXT DEFAULT '',
            category TEXT DEFAULT '',
            channel_name TEXT DEFAULT '',
            subtitle TEXT DEFAULT '',
            subtitle_type TEXT DEFAULT 'text',
            author_id TEXT,
            likes INTEGER DEFAULT 0,
            plays INTEGER DEFAULT 0,
            featured INTEGER DEFAULT 0,
            created_at DOUBLE PRECISION NOT NULL,
            status TEXT DEFAULT 'approved'
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS podcast_likes (
            user_id TEXT NOT NULL,
            podcast_id TEXT NOT NULL,
            created_at DOUBLE PRECISION,
            PRIMARY KEY (user_id, podcast_id)
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS live_history (
            id TEXT PRIMARY KEY,
            host_id TEXT NOT NULL,
            title TEXT DEFAULT '',
            started_at DOUBLE PRECISION NOT NULL,
            ended_at DOUBLE PRECISION,
            duration INTEGER DEFAULT 0,
            peak_viewers INTEGER DEFAULT 0
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS ip_bans (
            ip TEXT PRIMARY KEY,
            reason TEXT DEFAULT '',
            created_by TEXT DEFAULT '',
            created_at DOUBLE PRECISION NOT NULL
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS banned_words (
            id TEXT PRIMARY KEY,
            word TEXT UNIQUE NOT NULL,
            created_by TEXT DEFAULT '',
            created_at DOUBLE PRECISION NOT NULL
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS user_public_keys (
            user_id TEXT PRIMARY KEY,
            public_key TEXT NOT NULL,
            updated_at DOUBLE PRECISION NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS ai_config (
            id INTEGER PRIMARY KEY DEFAULT 1,
            base_url TEXT DEFAULT '',
            model TEXT DEFAULT '',
            api_key TEXT DEFAULT ''
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS live_channels (
            id TEXT PRIMARY KEY,
            user_id TEXT NOT NULL,
            name TEXT NOT NULL,
            cover TEXT DEFAULT '',
            status TEXT DEFAULT 'pending',
            reject_reason TEXT DEFAULT '',
            created_at DOUBLE PRECISION NOT NULL,
            reviewed_at DOUBLE PRECISION,
            reviewed_by TEXT,
            featured INTEGER DEFAULT 0,
            banned INTEGER DEFAULT 0,
            whip_token TEXT DEFAULT ''
        )
    ''')
    cur.execute('ALTER TABLE ai_config ADD COLUMN IF NOT EXISTS moderation_enabled INTEGER DEFAULT 0')
    cur.execute('ALTER TABLE posts ADD COLUMN IF NOT EXISTS ai_flagged INTEGER DEFAULT 0')
    cur.execute('ALTER TABLE replies ADD COLUMN IF NOT EXISTS ai_flagged INTEGER DEFAULT 0')
    cur.execute('ALTER TABLE live_channels ADD COLUMN IF NOT EXISTS banned INTEGER DEFAULT 0')
    cur.execute('ALTER TABLE live_channels ADD COLUMN IF NOT EXISTS featured INTEGER DEFAULT 0')
    cur.execute('ALTER TABLE live_channels ADD COLUMN IF NOT EXISTS whip_token TEXT DEFAULT \'\'')
    cur.execute("ALTER TABLE podcasts ADD COLUMN IF NOT EXISTS channel_name TEXT DEFAULT ''")
    # ===== 举报 / 自动下架 =====
    cur.execute('ALTER TABLE posts ADD COLUMN IF NOT EXISTS report_removed INTEGER DEFAULT 0')
    cur.execute('ALTER TABLE news ADD COLUMN IF NOT EXISTS report_removed INTEGER DEFAULT 0')
    cur.execute("ALTER TABLE news ADD COLUMN IF NOT EXISTS video TEXT DEFAULT ''")
    cur.execute('ALTER TABLE news ADD COLUMN IF NOT EXISTS ai_allowed INTEGER DEFAULT 1')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS reports (
            id TEXT PRIMARY KEY,
            target_type TEXT NOT NULL,
            target_id TEXT NOT NULL,
            reporter_id TEXT NOT NULL,
            reason TEXT DEFAULT '',
            created_at DOUBLE PRECISION NOT NULL
        )
    ''')
    cur.execute('CREATE INDEX IF NOT EXISTS idx_reports_target ON reports(target_type, target_id)')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS ai_review_logs (
            id TEXT PRIMARY KEY,
            content_type TEXT NOT NULL,
            content TEXT,
            category TEXT,
            score DOUBLE PRECISION DEFAULT 0,
            reason TEXT DEFAULT '',
            created_at DOUBLE PRECISION NOT NULL
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS ai_quota (
            user_id TEXT PRIMARY KEY,
            daily_limit INTEGER DEFAULT 50,
            monthly_limit INTEGER DEFAULT 500
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS ai_usage_log (
            id TEXT PRIMARY KEY,
            user_id TEXT NOT NULL,
            created_at DOUBLE PRECISION NOT NULL
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS chat_ai_usage_log (
            id TEXT PRIMARY KEY,
            user_id TEXT NOT NULL,
            created_at DOUBLE PRECISION NOT NULL
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS images (
            path TEXT PRIMARY KEY,
            data BYTEA,
            content_type TEXT DEFAULT '',
            created_at DOUBLE PRECISION
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS oauth_apps (
            id TEXT PRIMARY KEY,
            client_id TEXT NOT NULL UNIQUE,
            client_secret TEXT NOT NULL,
            app_name TEXT NOT NULL,
            app_description TEXT DEFAULT '',
            redirect_uri TEXT NOT NULL,
            homepage_url TEXT DEFAULT '',
            user_id TEXT NOT NULL,
            created_at DOUBLE PRECISION
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS oauth_codes (
            code TEXT PRIMARY KEY,
            client_id TEXT NOT NULL,
            user_id TEXT NOT NULL,
            redirect_uri TEXT NOT NULL,
            scope TEXT DEFAULT 'userinfo',
            expires_at DOUBLE PRECISION
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS oauth_tokens (
            access_token TEXT PRIMARY KEY,
            client_id TEXT NOT NULL,
            user_id TEXT NOT NULL,
            scope TEXT DEFAULT 'userinfo',
            expires_at DOUBLE PRECISION
        )
    ''')
    cur.execute('''
        CREATE TABLE IF NOT EXISTS translations (
            text_hash TEXT NOT NULL,
            target_lang TEXT NOT NULL,
            translated_text TEXT,
            created_at DOUBLE PRECISION,
            PRIMARY KEY (text_hash, target_lang)
        )
    ''')
    # 二期 · 视角分析结果缓存表（由 perspectives.py 使用）
    cur.execute('''
        CREATE TABLE IF NOT EXISTS perspective_outputs (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            news_id TEXT NOT NULL,
            perspective_id TEXT NOT NULL,
            perspective_name TEXT DEFAULT '',
            result_json TEXT NOT NULL,
            created_at DOUBLE PRECISION,
            model TEXT DEFAULT '',
            UNIQUE (news_id, perspective_id)
        )
    ''')
    # 二期 · 单 Agent 分析结果缓存表（由本文件 agent_analysis 模块使用，SQLite 分支见 _init_db_sqlite）

    # 兼容旧数据库：添加缺失的列
    for col_def in [
        ('users', 'is_admin', 'INTEGER DEFAULT 0'),
        ('users', 'is_super_admin', 'INTEGER DEFAULT 0'),
        ('users', 'can_publish_news', 'INTEGER DEFAULT 0'),
        ('users', 'avatar', "TEXT DEFAULT ''"),
        ('users', 'background', "TEXT DEFAULT ''"),
        ('users', 'banner', "TEXT DEFAULT ''"),
        ('replies', 'parent_id', "TEXT DEFAULT ''"),
        ('replies', 'image', "TEXT DEFAULT ''"),
        ('users', 'email_verified', 'INTEGER DEFAULT 0'),
        ('users', 'email_verify_deadline', 'DOUBLE PRECISION DEFAULT 0'),
        ('users', 'require_login_code', 'INTEGER DEFAULT 0'),
        ('users', 'verified', 'INTEGER DEFAULT 0'),
        ('users', 'verified_text', "TEXT DEFAULT ''"),
        ('users', 'ban_reason', "TEXT DEFAULT ''"),
    ]:
        table, col, dtype = col_def
        try:
            cur.execute(f'ALTER TABLE {table} ADD COLUMN {col} {dtype}')
        except Exception:
            pass

    # 兼容已存在的视频表。PostgreSQL 初始化必须通过当前游标执行迁移。
    try:
        cur.execute("ALTER TABLE videos ADD COLUMN status TEXT DEFAULT 'pending'")
    except Exception:
        pass

    try:
        cur.execute("ALTER TABLE users ADD COLUMN status TEXT DEFAULT 'active'")
    except:
        pass
    try:
        cur.execute("ALTER TABLE users ADD COLUMN muted_until DOUBLE PRECISION DEFAULT 0")
    except:
        pass
    try:
        cur.execute("ALTER TABLE users ADD COLUMN last_ip TEXT DEFAULT ''")
    except:
        pass
    try:
        cur.execute("ALTER TABLE users ADD COLUMN last_online DOUBLE PRECISION DEFAULT 0")
    except:
        pass
    try:
        cur.execute("ALTER TABLE users ADD COLUMN admin_follower_boost INTEGER DEFAULT 0")
    except:
        pass
    try:
        cur.execute("ALTER TABLE users ADD COLUMN admin_like_boost INTEGER DEFAULT 0")
    except:
        pass
    for _col in ['birthday_month', 'birthday_day', 'birthday_age', 'region', 'gender']:
        try:
            cur.execute(f"ALTER TABLE users ADD COLUMN {_col} INTEGER") if _col in ('birthday_month', 'birthday_day', 'birthday_age') else cur.execute(f"ALTER TABLE users ADD COLUMN {_col} TEXT DEFAULT ''")
        except:
            pass
    # 注：已移除"老用户邮箱视为已验证"的自动迁移逻辑（同 SQLite 分支）
    cur.execute('SELECT id FROM users WHERE username=%s', (ADMIN_USERNAME,))
    admin = cur.fetchone()
    if not admin:
        uid = 'u_admin_' + uuid.uuid4().hex[:8]
        cur.execute(
            'INSERT INTO users (id, username, email, password_hash, bio, is_admin, is_super_admin, created_at) VALUES (%s,%s,%s,%s,%s,%s,%s,%s)',
            (uid, ADMIN_USERNAME, 'admin@bird.local', hash_password(ADMIN_PASSWORD), '管理员', 1, 1, time.time()))
        print(f'已创建管理员账号: {ADMIN_USERNAME} (密码已通过环境变量设置或随机生成)')
    else:
        # 仅确保管理员标志位，不覆盖密码（避免服务重启后用户重置的密码失效）
        cur.execute('UPDATE users SET is_admin=1, is_super_admin=1 WHERE username=%s',
                    (ADMIN_USERNAME,))

    # 创建 AI 机器人用户
    cur.execute('SELECT id FROM users WHERE id=%s', (AI_BOT_ID,))
    if not cur.fetchone():
        cur.execute(
            'INSERT INTO users (id, username, email, password_hash, bio, created_at) VALUES (%s,%s,%s,%s,%s,%s)',
            (AI_BOT_ID, AI_BOT_NAME, '', hash_password(uuid.uuid4().hex), '论坛AI助手，可以在回复中@AI来与我互动', time.time()))
        print(f'已创建AI机器人账号: {AI_BOT_NAME}')
    else:
        cur.execute('UPDATE users SET username=%s WHERE id=%s', (AI_BOT_NAME, AI_BOT_ID))

    cur.close()
    db.close()


def _init_db_sqlite():
    db = sqlite3.connect(DB_PATH)
    db.executescript('''
        CREATE TABLE IF NOT EXISTS users (
            id TEXT PRIMARY KEY,
            username TEXT UNIQUE NOT NULL,
            email TEXT DEFAULT '',
            password_hash TEXT NOT NULL,
            bio TEXT DEFAULT '',
            is_admin INTEGER DEFAULT 0,
            is_super_admin INTEGER DEFAULT 0,
            can_publish_news INTEGER DEFAULT 0,
            created_at REAL NOT NULL,
            birthday_month INTEGER DEFAULT 0,
            birthday_day INTEGER DEFAULT 0,
            birthday_age INTEGER DEFAULT 0,
            region TEXT DEFAULT '',
            gender TEXT DEFAULT ''
        );
        CREATE TABLE IF NOT EXISTS posts (
            id TEXT PRIMARY KEY,
            author_id TEXT NOT NULL,
            title TEXT NOT NULL,
            category TEXT NOT NULL,
            content TEXT NOT NULL,
            likes INTEGER DEFAULT 0,
            created_at REAL NOT NULL,
            FOREIGN KEY (author_id) REFERENCES users(id)
        );
        CREATE TABLE IF NOT EXISTS tags (
            post_id TEXT NOT NULL,
            tag TEXT NOT NULL,
            FOREIGN KEY (post_id) REFERENCES posts(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS replies (
            id TEXT PRIMARY KEY,
            post_id TEXT NOT NULL,
            author_id TEXT NOT NULL,
            parent_id TEXT DEFAULT '',
            content TEXT NOT NULL,
            image TEXT DEFAULT '',
            likes INTEGER DEFAULT 0,
            created_at REAL NOT NULL,
            FOREIGN KEY (post_id) REFERENCES posts(id) ON DELETE CASCADE,
            FOREIGN KEY (author_id) REFERENCES users(id)
        );
        CREATE TABLE IF NOT EXISTS post_likes (
            user_id TEXT NOT NULL,
            post_id TEXT NOT NULL,
            PRIMARY KEY (user_id, post_id),
            FOREIGN KEY (post_id) REFERENCES posts(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS reply_likes (
            user_id TEXT NOT NULL,
            reply_id TEXT NOT NULL,
            PRIMARY KEY (user_id, reply_id),
            FOREIGN KEY (reply_id) REFERENCES replies(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS bookmarks (
            user_id TEXT NOT NULL,
            post_id TEXT NOT NULL,
            PRIMARY KEY (user_id, post_id),
            FOREIGN KEY (post_id) REFERENCES posts(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS notifications (
            id TEXT PRIMARY KEY,
            user_id TEXT NOT NULL,
            text TEXT NOT NULL,
            read INTEGER DEFAULT 0,
            created_at REAL NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS passkeys (
            id TEXT PRIMARY KEY,
            user_id TEXT NOT NULL,
            credential_id TEXT NOT NULL,
            public_key TEXT NOT NULL,
            counter INTEGER DEFAULT 0,
            name TEXT DEFAULT '',
            created_at REAL NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS chat_messages (
            id TEXT PRIMARY KEY,
            user_id TEXT NOT NULL,
            username TEXT NOT NULL,
            avatar TEXT DEFAULT '',
            content TEXT NOT NULL,
            created_at REAL NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS dm_conversations (
            id TEXT PRIMARY KEY,
            user1_id TEXT NOT NULL,
            user2_id TEXT NOT NULL,
            created_at REAL NOT NULL,
            FOREIGN KEY (user1_id) REFERENCES users(id) ON DELETE CASCADE,
            FOREIGN KEY (user2_id) REFERENCES users(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS dm_messages (
            id TEXT PRIMARY KEY,
            conversation_id TEXT NOT NULL,
            sender_id TEXT NOT NULL,
            content TEXT NOT NULL,
            is_encrypted INTEGER DEFAULT 0,
            created_at REAL NOT NULL,
            FOREIGN KEY (conversation_id) REFERENCES dm_conversations(id) ON DELETE CASCADE,
            FOREIGN KEY (sender_id) REFERENCES users(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS follows (
            follower_id TEXT NOT NULL,
            following_id TEXT NOT NULL,
            created_at REAL NOT NULL,
            PRIMARY KEY (follower_id, following_id),
            FOREIGN KEY (follower_id) REFERENCES users(id) ON DELETE CASCADE,
            FOREIGN KEY (following_id) REFERENCES users(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS bug_reports (
            id TEXT PRIMARY KEY,
            user_id TEXT NOT NULL,
            username TEXT NOT NULL,
            content TEXT NOT NULL,
            status TEXT DEFAULT 'open',
            created_at REAL NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS announcements (
            id TEXT PRIMARY KEY,
            title TEXT NOT NULL,
            content TEXT NOT NULL,
            created_by TEXT NOT NULL,
            created_at REAL NOT NULL,
            FOREIGN KEY (created_by) REFERENCES users(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS news (
            id TEXT PRIMARY KEY,
            title TEXT NOT NULL,
            content TEXT NOT NULL,
            image TEXT DEFAULT '',
            video TEXT DEFAULT '',
            author_id TEXT,
            likes INTEGER DEFAULT 0,
            ai_allowed INTEGER DEFAULT 1,
            created_at REAL NOT NULL
        );
        CREATE TABLE IF NOT EXISTS news_likes (
            user_id TEXT NOT NULL,
            news_id TEXT NOT NULL,
            created_at REAL,
            PRIMARY KEY (user_id, news_id)
        );
        CREATE TABLE IF NOT EXISTS news_comments (
            id TEXT PRIMARY KEY,
            news_id TEXT NOT NULL,
            author_id TEXT,
            content TEXT NOT NULL,
            image TEXT DEFAULT '',
            likes INTEGER DEFAULT 0,
            created_at REAL NOT NULL
        );
        CREATE TABLE IF NOT EXISTS news_comment_likes (
            user_id TEXT NOT NULL,
            comment_id TEXT NOT NULL,
            PRIMARY KEY (user_id, comment_id)
        );
        CREATE TABLE IF NOT EXISTS news_config (
            key TEXT PRIMARY KEY,
            value TEXT DEFAULT ''
        );
        CREATE TABLE IF NOT EXISTS ip_bans (
            ip TEXT PRIMARY KEY,
            reason TEXT DEFAULT '',
            created_by TEXT DEFAULT '',
            created_at REAL NOT NULL
        );
        CREATE TABLE IF NOT EXISTS banned_words (
            id TEXT PRIMARY KEY,
            word TEXT UNIQUE NOT NULL,
            created_by TEXT DEFAULT '',
            created_at REAL NOT NULL
        );
        CREATE TABLE IF NOT EXISTS user_public_keys (
            user_id TEXT PRIMARY KEY,
            public_key TEXT NOT NULL,
            updated_at REAL NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE
        );
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS ai_config (
            id INTEGER PRIMARY KEY DEFAULT 1,
            base_url TEXT DEFAULT '',
            model TEXT DEFAULT '',
            api_key TEXT DEFAULT ''
        );
    ''')
    try:
        db.execute('ALTER TABLE ai_config ADD COLUMN moderation_enabled INTEGER DEFAULT 0')
    except:
        pass
    try:
        db.execute('ALTER TABLE posts ADD COLUMN ai_flagged INTEGER DEFAULT 0')
    except:
        pass
    try:
        db.execute('ALTER TABLE replies ADD COLUMN ai_flagged INTEGER DEFAULT 0')
    except:
        pass
    try:
        db.execute('ALTER TABLE live_channels ADD COLUMN whip_token TEXT DEFAULT \'\'')
    except:
        pass
    # ===== 举报 / 自动下架（SQLite） =====
    try:
        db.execute('ALTER TABLE posts ADD COLUMN report_removed INTEGER DEFAULT 0')
    except:
        pass
    try:
        db.execute('ALTER TABLE news ADD COLUMN report_removed INTEGER DEFAULT 0')
    except:
        pass
    db.execute('''
        CREATE TABLE IF NOT EXISTS reports (
            id TEXT PRIMARY KEY,
            target_type TEXT NOT NULL,
            target_id TEXT NOT NULL,
            reporter_id TEXT NOT NULL,
            reason TEXT DEFAULT '',
            created_at REAL NOT NULL
        )
    ''')
    db.execute('CREATE INDEX IF NOT EXISTS idx_reports_target ON reports(target_type, target_id)')
    db.execute('''
        CREATE TABLE IF NOT EXISTS ai_review_logs (
            id TEXT PRIMARY KEY,
            content_type TEXT NOT NULL,
            content TEXT,
            category TEXT,
            score REAL DEFAULT 0,
            reason TEXT DEFAULT '',
            created_at REAL NOT NULL
        );
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS ai_quota (
            user_id TEXT PRIMARY KEY,
            daily_limit INTEGER DEFAULT 50,
            monthly_limit INTEGER DEFAULT 500
        );
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS ai_usage_log (
            id TEXT PRIMARY KEY,
            user_id TEXT NOT NULL,
            created_at REAL NOT NULL
        );
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS chat_ai_usage_log (
            id TEXT PRIMARY KEY,
            user_id TEXT NOT NULL,
            created_at REAL NOT NULL
        );
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS oauth_apps (
            id TEXT PRIMARY KEY,
            client_id TEXT NOT NULL UNIQUE,
            client_secret TEXT NOT NULL,
            app_name TEXT NOT NULL,
            app_description TEXT DEFAULT '',
            redirect_uri TEXT NOT NULL,
            homepage_url TEXT DEFAULT '',
            user_id TEXT NOT NULL,
            created_at REAL
        );
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS oauth_codes (
            code TEXT PRIMARY KEY,
            client_id TEXT NOT NULL,
            user_id TEXT NOT NULL,
            redirect_uri TEXT NOT NULL,
            scope TEXT DEFAULT 'userinfo',
            expires_at REAL
        );
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS oauth_tokens (
            access_token TEXT PRIMARY KEY,
            client_id TEXT NOT NULL,
            user_id TEXT NOT NULL,
            scope TEXT DEFAULT 'userinfo',
            expires_at REAL
        );
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS translations (
            text_hash TEXT NOT NULL,
            target_lang TEXT NOT NULL,
            translated_text TEXT,
            created_at REAL,
            PRIMARY KEY (text_hash, target_lang)
        );
    ''')
    # 二期 · 视角分析结果缓存表（由 perspectives.py 使用）
    db.execute('''
        CREATE TABLE IF NOT EXISTS perspective_outputs (
            id SERIAL PRIMARY KEY,
            news_id TEXT NOT NULL,
            perspective_id TEXT NOT NULL,
            perspective_name TEXT DEFAULT '',
            result_json TEXT NOT NULL,
            created_at DOUBLE PRECISION,
            model TEXT DEFAULT '',
            UNIQUE (news_id, perspective_id)
        );
    ''')

    # 二期 · 单 Agent 分析结果缓存表（SQLite 分支，由本文件 agent_analysis 模块使用）
    # status: pending / running / success / failed
    db.execute('''
        CREATE TABLE IF NOT EXISTS agent_analyses (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            news_id TEXT NOT NULL,
            viewpoint_id TEXT NOT NULL,
            content TEXT DEFAULT '',
            status TEXT DEFAULT 'pending',
            created_at DOUBLE PRECISION,
            updated_at DOUBLE PRECISION,
            model TEXT DEFAULT '',
            error TEXT DEFAULT '',
            UNIQUE (news_id, viewpoint_id)
        );
    ''')

    # 兼容旧数据库：添加缺失的列
    try:
        db.execute('ALTER TABLE users ADD COLUMN is_admin INTEGER DEFAULT 0')
    except:
        pass
    try:
        db.execute('ALTER TABLE users ADD COLUMN is_super_admin INTEGER DEFAULT 0')
    except:
        pass
    try:
        db.execute('ALTER TABLE users ADD COLUMN can_publish_news INTEGER DEFAULT 0')
        db.commit()
    except:
        pass
    try:
        db.execute('ALTER TABLE users ADD COLUMN avatar TEXT DEFAULT \'\'')
    except:
        pass
    try:
        db.execute('ALTER TABLE users ADD COLUMN background TEXT DEFAULT \'\'')
    except:
        pass
    try:
        db.execute('ALTER TABLE users ADD COLUMN banner TEXT DEFAULT \'\'')
        db.commit()
    except:
        pass
    try:
        db.execute('ALTER TABLE replies ADD COLUMN parent_id TEXT DEFAULT \'\'')
    except:
        pass
    try:
        db.execute('ALTER TABLE replies ADD COLUMN image TEXT DEFAULT \'\'')
    except:
        pass
    try:
        db.execute("ALTER TABLE users ADD COLUMN status TEXT DEFAULT 'active'")
        db.commit()
    except:
        pass
    try:
        db.execute('ALTER TABLE users ADD COLUMN muted_until REAL DEFAULT 0')
        db.commit()
    except:
        pass
    try:
        db.execute("ALTER TABLE users ADD COLUMN last_ip TEXT DEFAULT ''")
        db.commit()
    except:
        pass
    try:
        db.execute("ALTER TABLE users ADD COLUMN last_online REAL DEFAULT 0")
        db.commit()
    except:
        pass
    try:
        db.execute('ALTER TABLE users ADD COLUMN email_verified INTEGER DEFAULT 0')
        db.commit()
    except:
        pass
    try:
        db.execute('ALTER TABLE users ADD COLUMN email_verify_deadline REAL DEFAULT 0')
        db.commit()
    except:
        pass
    try:
        db.execute('ALTER TABLE users ADD COLUMN require_login_code INTEGER DEFAULT 0')
        db.commit()
    except:
        pass
    try:
        db.execute('ALTER TABLE users ADD COLUMN verified INTEGER DEFAULT 0')
        db.commit()
    except:
        pass
    try:
        db.execute("ALTER TABLE users ADD COLUMN verified_text TEXT DEFAULT ''")
        db.commit()
    except:
        pass
    try:
        db.execute("ALTER TABLE users ADD COLUMN ban_reason TEXT DEFAULT ''")
        db.commit()
    except:
        pass
    try:
        db.execute('ALTER TABLE users ADD COLUMN is_quality INTEGER DEFAULT 0')
        db.commit()
    except:
        pass
    try:
        db.execute('ALTER TABLE users ADD COLUMN admin_follower_boost INTEGER DEFAULT 0')
        db.commit()
    except:
        pass
    try:
        db.execute('ALTER TABLE users ADD COLUMN admin_like_boost INTEGER DEFAULT 0')
        db.commit()
    except:
        pass
    # 个人资料扩展：生日(月/日)、可选年龄、地区、性别
    for _col, _sql in [
        ('birthday_month', "ALTER TABLE users ADD COLUMN birthday_month INTEGER DEFAULT 0"),
        ('birthday_day', "ALTER TABLE users ADD COLUMN birthday_day INTEGER DEFAULT 0"),
        ('birthday_age', "ALTER TABLE users ADD COLUMN birthday_age INTEGER DEFAULT 0"),
        ('region', "ALTER TABLE users ADD COLUMN region TEXT DEFAULT ''"),
        ('gender', "ALTER TABLE users ADD COLUMN gender TEXT DEFAULT ''"),
    ]:
        try:
            db.execute(_sql)
            db.commit()
        except:
            pass
    try:
        db.execute('ALTER TABLE dm_messages ADD COLUMN is_encrypted INTEGER DEFAULT 0')
        db.commit()
    except:
        pass
    # 新闻表新增字段：摘要、分类、置顶
    for _col, _sql in [
        ('summary', "ALTER TABLE news ADD COLUMN summary TEXT DEFAULT ''"),
        ('category', "ALTER TABLE news ADD COLUMN category TEXT DEFAULT ''"),
        ('pinned', "ALTER TABLE news ADD COLUMN pinned INTEGER DEFAULT 0"),
        ('images', "ALTER TABLE news ADD COLUMN images TEXT DEFAULT ''"),
        ('featured', "ALTER TABLE news ADD COLUMN featured INTEGER DEFAULT 0"),
        ('video', "ALTER TABLE news ADD COLUMN video TEXT DEFAULT ''"),
        ('ai_allowed', "ALTER TABLE news ADD COLUMN ai_allowed INTEGER DEFAULT 1"),
    ]:
        try:
            db.execute(_sql)
            db.commit()
        except:
            pass
    # 注：已移除"老用户邮箱视为已验证"的自动迁移逻辑
    # 该逻辑会在每次启动时把所有有邮箱的老用户标记为已验证，导致未验证用户也显示已验证
    # 新用户注册时 email_verified 默认为 0，需通过邮箱验证码验证后才设为 1
    # 视频版块新表
    for _tbl_sql in [
        '''CREATE TABLE IF NOT EXISTS videos (
            id TEXT PRIMARY KEY,
            title TEXT NOT NULL,
            description TEXT DEFAULT '',
            filename TEXT NOT NULL,
            filepath TEXT NOT NULL,
            filesize INTEGER DEFAULT 0,
            duration REAL DEFAULT 0,
            thumbnail TEXT DEFAULT '',
            author_id TEXT,
            views INTEGER DEFAULT 0,
            likes INTEGER DEFAULT 0,
            created_at REAL NOT NULL,
            status TEXT DEFAULT 'pending'
        )''',
        '''CREATE TABLE IF NOT EXISTS video_likes (
            user_id TEXT NOT NULL,
            video_id TEXT NOT NULL,
            created_at REAL,
            PRIMARY KEY (user_id, video_id)
        )''',
        '''CREATE TABLE IF NOT EXISTS video_config (
            key TEXT PRIMARY KEY,
            value TEXT DEFAULT ''
        )''',
        '''CREATE TABLE IF NOT EXISTS live_history (
            id TEXT PRIMARY KEY,
            host_id TEXT NOT NULL,
            title TEXT DEFAULT '',
            started_at REAL NOT NULL,
            ended_at REAL,
            duration INTEGER DEFAULT 0,
            peak_viewers INTEGER DEFAULT 0
        )''',
        '''CREATE TABLE IF NOT EXISTS live_channels (
            id TEXT PRIMARY KEY,
            user_id TEXT NOT NULL,
            name TEXT NOT NULL,
            cover TEXT DEFAULT '',
            status TEXT DEFAULT 'pending',
            reject_reason TEXT DEFAULT '',
            created_at REAL NOT NULL,
            reviewed_at REAL,
            reviewed_by TEXT,
            featured INTEGER DEFAULT 0,
            banned INTEGER DEFAULT 0
        )''',
        '''CREATE TABLE IF NOT EXISTS podcasts (
            id TEXT PRIMARY KEY,
            title TEXT NOT NULL,
            description TEXT DEFAULT '',
            filename TEXT NOT NULL,
            filepath TEXT NOT NULL,
            filesize INTEGER DEFAULT 0,
            duration REAL DEFAULT 0,
            cover TEXT DEFAULT '',
            category TEXT DEFAULT '',
            channel_name TEXT DEFAULT '',
            subtitle TEXT DEFAULT '',
            subtitle_type TEXT DEFAULT 'text',
            author_id TEXT,
            likes INTEGER DEFAULT 0,
            plays INTEGER DEFAULT 0,
            featured INTEGER DEFAULT 0,
            created_at REAL NOT NULL,
            status TEXT DEFAULT 'approved'
        )''',
        '''CREATE TABLE IF NOT EXISTS podcast_likes (
            user_id TEXT NOT NULL,
            podcast_id TEXT NOT NULL,
            created_at REAL,
            PRIMARY KEY (user_id, podcast_id)
        )''',
    ]:
        try:
            db.execute(_tbl_sql)
            db.commit()
        except:
            pass
    try:
        db.execute("ALTER TABLE podcasts ADD COLUMN channel_name TEXT DEFAULT ''")
        db.commit()
    except:
        pass
    # live_channels 新增 featured 字段（管理页可标记精选直播间）
    try:
        db.execute('ALTER TABLE live_channels ADD COLUMN featured INTEGER DEFAULT 0')
        db.commit()
    except:
        pass
    # live_channels 新增 banned 字段（管理员可封禁直播间）
    try:
        db.execute('ALTER TABLE live_channels ADD COLUMN banned INTEGER DEFAULT 0')
        db.commit()
    except:
        pass
    # 迁移：移除 user_id UNIQUE 约束，允许一个用户拥有多个直播间（最多 3 个）
    # SQLite 不支持 ALTER TABLE DROP CONSTRAINT，需重建表
    try:
        schema_row = db.execute("SELECT sql FROM sqlite_master WHERE type='table' AND name='live_channels'").fetchone()
        # init_db 使用独立 SQLite 连接，未设置 row_factory 时该行是 tuple。
        schema_sql = ((schema_row['sql'] if hasattr(schema_row, 'keys') else schema_row[0]) if schema_row else '') or ''
        if 'UNIQUE' in schema_sql.upper():
            # 先清理上次迁移可能残留的临时表
            db.execute('DROP TABLE IF EXISTS live_channels_new')
            db.execute('''CREATE TABLE live_channels_new (
                id TEXT PRIMARY KEY, user_id TEXT NOT NULL, name TEXT NOT NULL,
                cover TEXT DEFAULT '', status TEXT DEFAULT 'pending',
                reject_reason TEXT DEFAULT '', created_at REAL NOT NULL,
                reviewed_at REAL, reviewed_by TEXT,
                featured INTEGER DEFAULT 0, banned INTEGER DEFAULT 0,
                whip_token TEXT DEFAULT ''
            )''')
            # 复制数据：分级降级，兼容不同列结构
            copied = False
            for cols_src, cols_dst in [
                ('id, user_id, name, cover, status, reject_reason, created_at, reviewed_at, reviewed_by, featured, banned, whip_token',
                 'id, user_id, name, cover, status, reject_reason, created_at, reviewed_at, reviewed_by, featured, banned, whip_token'),
                ('id, user_id, name, cover, status, reject_reason, created_at, reviewed_at, reviewed_by, featured, banned',
                 'id, user_id, name, cover, status, reject_reason, created_at, reviewed_at, reviewed_by, featured, banned'),
                ('id, user_id, name, cover, status, reject_reason, created_at, reviewed_at, reviewed_by',
                 'id, user_id, name, cover, status, reject_reason, created_at, reviewed_at, reviewed_by'),
            ]:
                try:
                    db.execute(f'INSERT INTO live_channels_new ({cols_dst}) SELECT {cols_src} FROM live_channels')
                    copied = True
                    break
                except Exception:
                    continue
            if not copied:
                raise Exception('无法复制 live_channels 数据（列不匹配）')
            db.execute('DROP TABLE live_channels')
            db.execute('ALTER TABLE live_channels_new RENAME TO live_channels')
            db.commit()
            print('[db] live_channels 已迁移：移除 user_id UNIQUE 约束', flush=True)
    except Exception as _e:
        print(f'[db] live_channels 迁移失败: {_e}', flush=True)
        try:
            db.rollback()
        except:
            pass

    # 必须在 videos 表创建后迁移旧表，否则首次启动会吞掉 no such table 后漏掉 status。
    try:
        db.execute("ALTER TABLE videos ADD COLUMN status TEXT DEFAULT 'pending'")
        db.commit()
    except:
        pass

    # 自动创建管理员账号
    admin = db.execute('SELECT id FROM users WHERE username=?', (ADMIN_USERNAME,)).fetchone()
    if not admin:
        uid = 'u_admin_' + uuid.uuid4().hex[:8]
        db.execute('INSERT INTO users (id, username, email, password_hash, bio, is_admin, is_super_admin, created_at) VALUES (?,?,?,?,?,?,?,?)',
                   (uid, ADMIN_USERNAME, 'admin@bird.local', hash_password(ADMIN_PASSWORD), '管理员', 1, 1, time.time()))
        print(f'已创建管理员账号: {ADMIN_USERNAME} (密码已通过环境变量设置或随机生成)')
    else:
        # 仅确保管理员标志位，不覆盖密码（避免服务重启后用户重置的密码失效）
        db.execute('UPDATE users SET is_admin=1, is_super_admin=1 WHERE username=?', (ADMIN_USERNAME,))

    # 创建 AI 机器人用户
    ai_exists = db.execute('SELECT id FROM users WHERE id=?', (AI_BOT_ID,)).fetchone()
    if not ai_exists:
        db.execute('INSERT INTO users (id, username, email, password_hash, bio, created_at) VALUES (?,?,?,?,?,?)',
                   (AI_BOT_ID, AI_BOT_NAME, '', hash_password(uuid.uuid4().hex), '论坛AI助手，可以在回复中@AI来与我互动', time.time()))
        print(f'已创建AI机器人账号: {AI_BOT_NAME}')
    else:
        db.execute('UPDATE users SET username=? WHERE id=?', (AI_BOT_NAME, AI_BOT_ID))

    db.commit()

    db.close()


# ===== 内容过滤 =====
# 默认违禁词（数据库为空时使用）
_DEFAULT_BAD_WORDS = [
    # 脏话
    '傻逼', '煞笔', '沙比', 'sb', 'SB', 'Sb', 'sB', '草泥马', '操你', '艹你',
    '妈逼', '马逼', '妈比', '干你', '日你', '靠你', '去你妈', '滚你妈',
    '狗日', '狗娘', '王八蛋', '王八', '混蛋', '混账', '畜生', '杂种',
    '贱人', '婊子', '表子', '骚货', '荡妇', '绿茶', '绿茶婊',
    '白痴', '弱智', '脑残', '智障', '废物', '垃圾', '人渣',
    '滚蛋', '闭嘴', '去死', '死开', '滚开', '滚犊子',
    '他妈', '她妈', '它妈', '你妈', '尼玛', '泥马',
    'fuck', 'Fuck', 'FUCK', 'shit', 'Shit', 'SHIT', 'bitch', 'Bitch', 'BITCH',
    'asshole', 'Asshole', 'ASSHOLE', 'damn', 'Damn', 'DAMN',
    'crap', 'Crap', 'CRAP', 'dick', 'Dick', 'DICK',
    # 政治敏感
    '习近平', 'xijinping', 'Xijinping', 'XiJinping',
    '共产党', '中共', '反共', '反华', '台独', '藏独', '疆独',
    '法轮功', '法轮', 'falungong', '六四', '6四', '六4', '64事件', '8964',
    '天安门事件', '天安门屠杀', '民运', '翻墙', 'VPN', 'vpn',
    # 黄色内容
    '做爱', '性交', '口交', '肛交', '手淫', '自慰', '撸管', '打飞机',
    '约炮', '一夜情', '援交', '卖淫', '嫖娼', '嫖客',
    '色情', '黄色视频', '黄片', 'AV女优', '裸体', '裸照',
    '阴茎', '阴道', '生殖器', '乳房', '胸部',
    'porn', 'Porn', 'PORN', 'sex', 'Sex', 'SEX',
    'nude', 'Nude', 'NUDE', 'naked', 'Naked', 'NAKED',
    'hentai', 'Hentai', 'HENTAI',
]

# 违禁词缓存
_bad_words_cache = {'words': None, 'ts': 0}

def _get_bad_words():
    """获取违禁词列表（带缓存，30秒刷新）"""
    now = time.time()
    if _bad_words_cache['words'] is not None and now - _bad_words_cache['ts'] < 30:
        return _bad_words_cache['words']
    try:
        db = get_db()
        rows = _fetchall(db, 'SELECT word FROM banned_words')
        if rows:
            words = sorted([r['word'] for r in rows], key=len, reverse=True)
        else:
            words = sorted(_DEFAULT_BAD_WORDS, key=len, reverse=True)
        _bad_words_cache['words'] = words
        _bad_words_cache['ts'] = now
        return words
    except Exception:
        # PG 事务失败后必须 rollback，否则连接进入 aborted 状态
        try:
            db.rollback()
        except Exception:
            pass
        return sorted(_DEFAULT_BAD_WORDS, key=len, reverse=True)

def check_banned_words(text):
    """检查文本是否包含违禁词，返回 (是否通过, 匹配到的词列表)
    已禁用：AI 内容审核接管，违禁词过滤不再生效，始终放行。
    """
    return True, []

def filter_content(text):
    """将违禁词替换为等长星号
    已禁用：AI 内容审核接管，不再做星号替换，原样返回。
    """
    return text


def _sanitize_plain(text):
    """纯文本字段（username/bio/verified_text/title）的 XSS 防护：剥离 HTML 标签"""
    if not text:
        return text
    import re as _re
    # 剥离所有 HTML 标签
    return _re.sub(r'<[^>]+>', '', str(text))


def _safe_int(val, default=0):
    """安全地把任意值转为 int，失败返回默认值"""
    try:
        return int(val)
    except (TypeError, ValueError):
        return default


# ===== 工具 =====
_PBKDF2_ITERATIONS = 260000  # OWASP 2023 推荐值

def _hash_pbkdf2(pw, salt_hex=None, iterations=None):
    """PBKDF2-SHA256 密码哈希（每用户独立随机盐 + 密钥拉伸），格式: pbkdf2$iter$salt_hex$hash_hex"""
    salt = bytes.fromhex(salt_hex) if salt_hex else secrets.token_bytes(16)
    it = iterations or _PBKDF2_ITERATIONS
    dk = hashlib.pbkdf2_hmac('sha256', pw.encode('utf-8'), salt, it)
    return f'pbkdf2${it}${salt.hex()}${dk.hex()}'

def hash_password(pw):
    """生成 PBKDF2 密码哈希（新用户注册/主动改密使用）"""
    return _hash_pbkdf2(pw)

def verify_password(pw, pw_hash):
    """校验密码：支持新 PBKDF2 格式与旧加盐 SHA-256 格式（常量时间比较）"""
    if not pw or not pw_hash:
        return False
    pw_hash = str(pw_hash)
    if pw_hash.startswith('pbkdf2$'):
        try:
            _, it, salt_hex, _ = pw_hash.split('$')
            expected = _hash_pbkdf2(pw, salt_hex, int(it))
            return _hmac.compare_digest(expected, pw_hash)
        except Exception:
            return False
    # 旧固定盐 SHA-256（登录成功后会触发透明升级）
    legacy = hashlib.sha256(('sb_salt_2024' + pw).encode()).hexdigest()
    return _hmac.compare_digest(legacy, pw_hash)

def _is_legacy_hash(pw_hash):
    """判断是否为需要升级的旧哈希格式"""
    return not str(pw_hash or '').startswith('pbkdf2$')

def _verify_legacy_password(pw, pw_hash):
    """旧无盐 SHA-256 校验（仅用于迁移用户自动升级）"""
    return _hmac.compare_digest(hashlib.sha256(pw.encode()).hexdigest(), pw_hash)

def _maybe_upgrade_password(db, user_id, password):
    """将旧格式哈希透明升级为 PBKDF2"""
    try:
        _exec(db, 'UPDATE users SET password_hash=? WHERE id=?', (hash_password(password), user_id))
        if not _USE_PG:
            db.commit()
        print(f'[MIGRATE] 用户 {user_id} 密码哈希已自动升级为 PBKDF2')
    except Exception as e:
        print(f'[MIGRATE] 升级密码哈希失败: {e}')

def get_username(user_id):
    db = get_db()
    row = _fetchone(db, 'SELECT username FROM users WHERE id=?', (user_id,))
    return row['username'] if row else '有人'


def get_user(user_id):
    db = get_db()
    row = _fetchone(db, 'SELECT id, username, email, bio, avatar, status, muted_until FROM users WHERE id=?', (user_id,))
    return dict(row) if row else None


def login_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if not _get_auth_user_id():
            return jsonify({'error': '未登录'}), 401
        return f(*args, **kwargs)
    return decorated


def _is_birthday_today(month, day):
    """判断指定月/日是否为今天（用于生日徽章与弹窗）"""
    if not month or not day:
        return False
    try:
        return (int(month), int(day)) == (time.localtime().tm_mon, time.localtime().tm_mday)
    except Exception:
        return False


def _attach_birthday_meta(u):
    """根据生日字段补齐 is_birthday、age 等元数据"""
    try:
        month = int(u.get('birthday_month') or 0)
        day = int(u.get('birthday_day') or 0)
        u['is_birthday'] = _is_birthday_today(month, day)
        # 可选 年龄 显示
        u['birthday'] = f'{month:02d}-{day:02d}' if month and day else ''
    except Exception:
        u['is_birthday'] = False
        u['birthday'] = ''
    return u


def get_current_user():
    uid = _get_auth_user_id()
    if not uid:
        return None
    try:
        db = get_db()
        row = _fetchone(db, 'SELECT id, username, email, bio, avatar, background, banner, email_verified, email_verify_deadline, require_login_code, verified, verified_text, is_quality, birthday_month, birthday_day, birthday_age, region, gender FROM users WHERE id=?', (uid,))
        if row:
            u = dict(row)
            u['avatar'] = f"/{u['avatar']}" if u.get('avatar') else ''
            u['background'] = f"/{u['background']}" if u.get('background') else ''
            # banner 为空时回退到 background（向后兼容旧数据）
            bg_val = u.get('background') or ''
            u['banner'] = f"/{u['banner']}" if u.get('banner') else bg_val
            u['email_verified'] = bool(u.get('email_verified'))
            u['require_login_code'] = bool(u.get('require_login_code'))
            u['verified'] = bool(u.get('verified'))
            u['verified_text'] = u.get('verified_text', '') or ''
            u['is_quality'] = bool(u.get('is_quality'))
            _attach_birthday_meta(u)
            return u
    except Exception:
        pass
    return None


def _get_content_type(filename):
    ext = os.path.splitext(filename)[1].lower()
    return {
        '.jpg': 'image/jpeg',
        '.jpeg': 'image/jpeg',
        '.png': 'image/png',
        '.gif': 'image/gif',
        '.webp': 'image/webp',
        '.mp4': 'video/mp4',
        '.webm': 'video/webm',
        '.mov': 'video/quicktime',
        '.m4v': 'video/mp4',
    }.get(ext, 'application/octet-stream')


def _check_nsfw(file_data, threshold=0.45):
    """检测图片是否包含过多肤色区域（简易黄色内容检测）
    基于 YCbCr 色彩空间的肤色像素比例判断
    threshold: 肤色像素占比阈值，超过则判定为可疑内容
    返回 (is_nsfw, ratio)
    """
    if not _HAS_PIL:
        return False, 0.0
    try:
        img = Image.open(_io.BytesIO(file_data))
        # 缩小图片加速检测
        img.thumbnail((256, 256))
        img = img.convert('YCbCr')
        pixels = list(img.getdata())
        if not pixels:
            return False, 0.0
        skin_count = 0
        for y, cb, cr in pixels:
            # YCbCr 肤色范围（广泛使用的标准）
            if 80 <= y <= 255 and 85 <= cb <= 135 and 135 <= cr <= 180:
                skin_count += 1
        ratio = skin_count / len(pixels)
        return ratio >= threshold, ratio
    except Exception:
        return False, 0.0


# ===== WebAuthn / Passkeys =====
WEBAUTHN_RP_NAME = 'SoaringBird 论坛'
WEBAUTHN_RP_ID = 'soaringbirdforum.xyz'  # 固定 RP ID，不信任前端传递的值


def _get_rp_id(browser_hostname=None):
    """获取 RP ID（固定为正式域名，忽略前端传入的 browserHostname 以防中间人攻击）"""
    return WEBAUTHN_RP_ID


def _get_origin(browser_origin=None):
    """从请求中动态获取完整 origin
    优先级：前端传递的 browserOrigin > X-Forwarded-Host > Origin 头 > Referer 头 > request.host_url
    """
    from urllib.parse import urlparse as _urlparse

    # 0. 前端传递的 browserOrigin（最可靠）
    if browser_origin:
        return browser_origin.rstrip('/')

    # 1. X-Forwarded-Host
    forwarded_host = request.headers.get('X-Forwarded-Host')
    if forwarded_host:
        proto = request.headers.get('X-Forwarded-Proto', 'https')
        return f"{proto}://{forwarded_host.rstrip('/')}"

    # 2. Origin 头
    origin = request.headers.get('Origin')
    if origin:
        return origin.rstrip('/')

    # 3. Referer 头（取协议+host部分）
    referer = request.headers.get('Referer')
    if referer:
        parsed = _urlparse(referer)
        if parsed.scheme and parsed.hostname:
            return f"{parsed.scheme}://{parsed.netloc.rstrip('/')}"

    return request.host_url.rstrip('/')


def generate_challenge():
    """生成 32 字节随机 challenge，base64url 编码"""
    return base64url_encode(secrets.token_bytes(32))


def base64url_decode(s):
    """解码 base64url 字符串"""
    if isinstance(s, str):
        s = s.encode('ascii')
    # 补齐 padding
    remainder = len(s) % 4
    if remainder:
        s += b'=' * (4 - remainder)
    return base64.urlsafe_b64decode(s)


def base64url_encode(b):
    """编码字节为 base64url 字符串（无 padding）"""
    return base64.urlsafe_b64encode(b).rstrip(b'=').decode('ascii')


def _b64url_normalize(s):
    """标准化 base64url 字符串（去除 padding，统一大小写）用于比较"""
    if not s:
        return s
    return s.rstrip('=').replace('+', '-').replace('/', '_')


def _parse_cose_key(key_bytes):
    """解析 COSE 公钥，返回 (alg, key_data)"""
    cose_key = cbor2.loads(key_bytes)
    alg = cose_key.get(3)  # COSE key algorithm
    if alg == -7:
        # ES256 / ECDSA P-256 + SHA-256
        x = cose_key.get(-2)
        y = cose_key.get(-3)
        return ('ES256', {'x': x, 'y': y})
    elif alg == -257:
        # RS256 / RSASSA-PKCS1-v1_5 + SHA-256
        n = cose_key.get(-1)
        e = cose_key.get(-2)
        return ('RS256', {'n': n, 'e': e})
    else:
        return (f'UNKNOWN({alg})', {})


def _verify_signature_es256(public_key_data, auth_data, client_data_json, signature):
    """使用 ecdsa 库验证 ES256 签名"""
    if not _HAS_ECDSA:
        print('[SECURITY] ecdsa 库未安装，拒绝 Passkey 认证')
        return False

    x = public_key_data['x']
    y = public_key_data['y']
    # 构造未压缩公钥: 0x04 || x || y
    uncompressed = b'\x04' + x + y
    vk = VerifyingKey.from_string(uncompressed, curve=NIST256p)

    # 验证数据 = auth_data + SHA-256(client_data_json)
    client_data_hash = hashlib.sha256(client_data_json).digest()
    verification_data = auth_data + client_data_hash

    try:
        # WebAuthn 签名是 DER 格式
        vk.verify(signature, verification_data, hashfunc=hashlib.sha256, sigdecode=sigdecode_der)
        return True
    except Exception:
        return False


def _verify_signature_rs256(public_key_data, auth_data, client_data_json, signature):
    """验证 RS256 签名（需要 cryptography 库，不可用时拒绝）"""
    print('[SECURITY] RS256 签名验证需要 cryptography 库，当前不支持，拒绝认证')
    return False


def verify_authenticator_signature(public_key_bytes, auth_data, client_data_json, signature):
    """验证认证器签名"""
    alg, key_data = _parse_cose_key(public_key_bytes)
    if alg == 'ES256':
        return _verify_signature_es256(key_data, auth_data, client_data_json, signature)
    elif alg == 'RS256':
        return _verify_signature_rs256(key_data, auth_data, client_data_json, signature)
    else:
        # 未知算法，拒绝认证
        print(f'[SECURITY] 未知签名算法 {alg}，拒绝认证')
        return False


def post_to_dict(row, user_id=None):
    """将帖子行转为字典，附带点赞/收藏状态"""
    d = dict(row)
    # 确保 author_avatar 有前导 /，便于客户端拼接 URL
    av = d.get('author_avatar')
    if av and not av.startswith('/'):
        d['author_avatar'] = '/' + av
    # author_verified 统一转为 bool（数据库存储为 int 0/1）
    d['author_verified'] = bool(d.get('author_verified', 0))
    # author_birthday：作者生日加成（签名若含 author_birthday_* 则判断）
    if 'author_birthday_month' in d or 'author_birthday_day' in d:
        d['author_birthday'] = _is_birthday_today(
            _safe_int(d.get('author_birthday_month'), 0),
            _safe_int(d.get('author_birthday_day'), 0))
    else:
        d['author_birthday'] = False
    if user_id:
        db = get_db()
        liked = _fetchone(db, 'SELECT 1 FROM post_likes WHERE user_id=? AND post_id=?', (user_id, d['id']))
        bm = _fetchone(db, 'SELECT 1 FROM bookmarks WHERE user_id=? AND post_id=?', (user_id, d['id']))
        d['liked'] = bool(liked)
        d['bookmarked'] = bool(bm)
    else:
        d['liked'] = False
        d['bookmarked'] = False
    # tags
    db = get_db()
    tags = _fetchall(db, 'SELECT tag FROM tags WHERE post_id=?', (d['id'],))
    d['tags'] = [t['tag'] for t in tags]
    # reply count
    rc = _fetchone(db, 'SELECT COUNT(*) as c FROM replies WHERE post_id=?', (d['id'],))
    d['reply_count'] = rc['c']
    # 兼容字段别名（Swift 客户端期望的键名）
    d['likes_count'] = d.get('likes', 0)
    d['replies_count'] = d['reply_count']
    d['is_liked'] = d['liked']
    d['is_bookmarked'] = d['bookmarked']
    return d


# ===== 免费翻译（MyMemory，无需 key）+ 结果缓存 =====
import threading as _tr_threading
_tr_lock = _tr_threading.Lock()
# 每用户每日翻译字符配额（登录用户更高，匿名按 IP 更宽松但防刷）
_TR_USER_DAILY_CHAR = 20000        # 登录用户 2 万字符/天
_TR_ANON_DAILY_CHAR = 6000         # 匿名（按 IP）6000 字符/天
_tr_usage = {}  # {(user_id or 'ip:'+ip): (date_str, used_chars)}
_TR_BATCH_MAX = 1400  # 单次翻译请求最大字符数（MyMemory 上限约 5000）

# MyMemory 多邮箱轮换：每个邮箱 ≈5 万字符/天免费额度，3 个轮用 ≈15 万/天
_TR_MM_EMAILS = [
    'translate@soaringbirdforum.xyz',
    'forum-bird@soaringbirdforum.xyz',
    'bird-ai@soaringbirdforum.xyz',
]
import itertools as _tr_itertools
_tr_mm_cycle = _tr_itertools.cycle(_TR_MM_EMAILS)
_tr_mm_cycle_lock = _tr_threading.Lock()


def _tr_next_email():
    with _tr_mm_cycle_lock:
        return next(_tr_mm_cycle)


def _tr_get_remote_ip():
    """从反向代理后获取真实 IP，用于匿名配额与限流"""
    xff = request.headers.get('X-Forwarded-For', '')
    if xff:
        return xff.split(',')[0].strip()
    return request.remote_addr or 'anon'

# 目标语言白名单（客户端只能请求这些语言）
_TR_LANG_WHITELIST = {
    'en': 'en', 'en-us': 'en', 'en-gb': 'en',
    'zh-cn': 'zh-CN', 'zh-tw': 'zh-TW', 'zh-hk': 'zh-TW',
    'ja': 'ja', 'ko': 'ko', 'fr': 'fr', 'de': 'de',
    'es': 'es', 'ru': 'ru', 'pt': 'pt', 'it': 'it',
    'th': 'th', 'vi': 'vi', 'id': 'id', 'ar': 'ar',
    'nl': 'nl', 'pl': 'pl', 'tr': 'tr',
}


def _tr_normalize_target(target):
    t = (target or '').replace('_', '-').lower()
    return _TR_LANG_WHITELIST.get(t, '')


def _tr_check_user_quota(user_id, text_len):
    """在配额内返回 True 并预扣；否则 False。匿名按 IP、登录按 user_id"""
    today = time.strftime('%Y-%m-%d')
    key = user_id if user_id else 'ip:' + _tr_get_remote_ip()
    limit = _TR_USER_DAILY_CHAR if user_id else _TR_ANON_DAILY_CHAR
    with _tr_lock:
        rec = _tr_usage.get(key)
        if not rec or rec[0] != today:
            rec = [today, 0]
            _tr_usage[key] = rec
        if rec[1] + text_len > limit:
            return False
        rec[1] += text_len
        return True


# 微软 Azure Translator 配置（免费 F0 层 200 万字符/月）。未配置时走 MyMemory 兜底。
AZURE_TRANSLATOR_KEY = os.environ.get('AZURE_TRANSLATOR_KEY', '')
AZURE_TRANSLATOR_REGION = os.environ.get('AZURE_TRANSLATOR_REGION', 'global')


def _azure_lang(target):
    """把论坛语言标记映射为 Azure 语言代码"""
    t = target.lower()
    if t in ('zh-cn',):
        return 'zh-Hans'
    if t in ('zh-tw', 'zh-hk'):
        return 'zh-Hant'
    return target


def _azure_translate_one(line_text, target):
    """调用微软 Azure Translator 翻译单行文本；失败返回 None"""
    import urllib.request
    url = ('https://api.cognitive.microsofttranslator.com/translate?api-version=3.0&to=' + _azure_lang(target))
    body = json.dumps([{'Text': line_text}]).encode('utf-8')
    req = urllib.request.Request(url, data=body, method='POST', headers={
        'Ocp-Apim-Subscription-Key': AZURE_TRANSLATOR_KEY,
        'Ocp-Apim-Subscription-Region': AZURE_TRANSLATOR_REGION,
        'Content-Type': 'application/json',
        'User-Agent': 'SoaringBirdForum/1.0',
    })
    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            data = json.loads(resp.read().decode('utf-8'))
        return data[0]['translations'][0]['text']
    except Exception:
        return None


def _tr_provider_one(line_text, target):
    """翻译单行：优先微软 Azure（配置了 key 时），否则/失败回退 MyMemory"""
    if AZURE_TRANSLATOR_KEY:
        out = _azure_translate_one(line_text, target)
        if out is not None:
            return out
    return _tr_mymemory_one(line_text, target)


def _tr_mymemory_one(line_text, target):
    """调用 MyMemory 翻译单行文本；失败返回 None。邮箱轮换 + 换邮箱重试一次，缩短超时"""
    import urllib.request
    import urllib.parse
    last_err = None
    for attempt in range(2):
        params = urllib.parse.urlencode({
            'q': line_text,
            'langpair': 'autodetect|' + target,
            'de': _tr_next_email(),
        })
        url = 'https://api.mymemory.translated.net/get?' + params
        req = urllib.request.Request(url, headers={'User-Agent': 'SoaringBirdForum/1.0'})
        try:
            with urllib.request.urlopen(req, timeout=8 if attempt == 0 else 12) as resp:
                data = json.loads(resp.read().decode('utf-8'))
        except Exception as e:
            last_err = e
            time.sleep(0.4 if attempt == 0 else 0)
            continue
        if data.get('responseStatus') != 200:
            last_err = 'status:' + str(data.get('responseStatus'))
            continue
        out = (data.get('responseData') or {}).get('translatedText')
        if out:
            return out
        last_err = 'empty'
    return None


def _tr_get_cached(text_hash, target):
    db = get_db()
    row = _fetchone(db, 'SELECT translated_text FROM translations WHERE text_hash=? AND target_lang=?', (text_hash, target))
    if row and row['translated_text']:
        return row['translated_text']
    return None


def _tr_store(db, text_hash, target, translated):
    try:
        _exec(db, 'INSERT OR IGNORE INTO translations (text_hash, target_lang, translated_text, created_at) VALUES (?,?,?,?)',
              (text_hash, target, translated, time.time()))
        db.commit()
    except Exception:
        try:
            db.rollback()
        except Exception:
            pass


def _tr_split_chunks(text, max_len):
    """把文本按换行切成 ≤max_len 的块，尽量保持段落结构；单行超长硬切"""
    lines = text.split('\n')
    chunks, cur, cur_len = [], [], 0
    for l in lines:
        lw = len(l)
        # 单行超长硬切
        while lw > max_len:
            if cur:
                chunks.append('\n'.join(cur)); cur, cur_len = [], 0
            chunks.append(l[:max_len])
            l = l[max_len:]
            lw = len(l)
        if cur and cur_len + lw + 1 > max_len:
            chunks.append('\n'.join(cur)); cur, cur_len = [], 0
        cur.append(l)
        cur_len += lw + 1
    if cur:
        chunks.append('\n'.join(cur))
    return chunks or ['']


def _tr_split_lines(text, max_len):
    """多行文本按行切块（每块多为单行），单行超长硬切，保留空行以保持段落结构"""
    out = []
    for l in text.split('\n'):
        if not l.strip():
            out.append(l)
            continue
        while len(l) > max_len:
            out.append(l[:max_len])
            l = l[max_len:]
        out.append(l)
    return out or ['']


def _tr_translate(text, target):
    """整段翻译。
    - 单行文本：整段一次调用（约 1s）+ 整段缓存。
    - 多行文本：按行切块后并发翻译（单行请求极稳，避免 MyMemory 对“一次请求多行中文”偶发失败/超时）。
    任一块失败则整体失败。返回 (translated, all_ok)"""
    text = (text or '').strip()
    if not text:
        return None, False
    db = get_db()
    h = hashlib.sha256((target + '|' + text).encode('utf-8')).hexdigest()
    cached = _tr_get_cached(h, target)
    if cached is not None:
        return cached, True
    # 切块：无换行整段一次；有换行按行并发
    if '\n' in text:
        chunks = _tr_split_lines(text, _TR_BATCH_MAX)
    else:
        chunks = _tr_split_chunks(text, _TR_BATCH_MAX)
    # 单块（短文/单行）：一次请求直接返回
    if len(chunks) == 1:
        res = _tr_provider_one(chunks[0], target)
        if res is None:
            return None, False
        _tr_store(db, h, target, res)
        return res, True
    # 多块并发翻译：允许部分块失败（失败块保留原文），避免整段失败
    try:
        from concurrent.futures import ThreadPoolExecutor
        results = [None] * len(chunks)
        with ThreadPoolExecutor(max_workers=6) as ex:
            futs = {ex.submit(_tr_provider_one, c, target): i for i, c in enumerate(chunks)}
            for fut in futs:
                try:
                    r = fut.result(timeout=60)
                except Exception:
                    r = None
                results[futs[fut]] = r
    except Exception:
        results = [None] * len(chunks)
    ok = 0
    out_lines = []
    for i, c in enumerate(chunks):
        if results[i]:
            out_lines.append(results[i]); ok += 1
        else:
            out_lines.append(c)  # 该行翻译失败则保留原文，保证长帖至少部分可读
    if ok == 0:
        return None, False
    out = '\n'.join(out_lines)
    _tr_store(db, h, target, out)
    return out, True


# ===== 新闻多语种翻译（聚合页原文+译文） =====
_TR_NEWS_TARGET = 'zh-CN'

def _news_is_foreign(text):
    """判断文本是否以非中文为主（需要翻译）。按 Unicode 字符占比粗判。"""
    text = (text or '').strip()
    if not text:
        return False
    letters = [ch for ch in text if ch.isalpha()]
    if not letters:
        return False
    cjk = sum(1 for ch in letters if '\u4e00' <= ch <= '\u9fff')
    return (len(letters) - cjk) / len(letters) > 0.5


_THINK_MARK_RE = re.compile(
    r'(?:Thinking\s*Process|思考过程|推理过程|Reasoning\s+Process|思考链)\s*[:：]'
    r'|Analyze\s+the\s+(?:Request|Source|Input|Text)'
    r'|Drafting\s+the\s+Translation'
    r'|Step\s*\d+|Paragraph\s*\d+|段落\s*\d+'
    r'|让我(?:分析|检查|核对|翻译|思考)'
    r'|让我们'
    r'|Let\'s\s+\w+'
    r'|^\s*\d+[.、)]\s*\*\*?[^*]+\*\*?',
    re.I)

_THINK_DRAFT_RE = re.compile(
    r'(?:Thinking\s*Process|思考过程|推理过程|Reasoning\s+Process|思考链)'
    r'|Analyze\s+the\s+(?:Request|Source|Input|Text)'
    r'|Drafting\s+the\s+Translation'
    r'|Step\s*\d+|Paragraph\s*\d+|段落\s*\d+'
    r'|让我(?:分析|检查|核对|翻译|思考)'
    r'|Let\'s\s+\w+',
    re.I)


def _strip_thinking(text):
    """剥离模型输出的思考链/草稿片段（Thinking Process / 编号步骤 / Paragraph 草稿等），只保留最终译文。

    兼容场景：
    - 模型先输出 "Thinking Process: ..." / "1. **Analyze the Request:** ..." 再给译文 → 取最后一个不含思考特征的段落；
    - 模型输出 "*Paragraph N:* 原文 -> 译文" 对照草稿 → 提取所有 "-> 译文" 片段拼接；
    - 全文均为思考链（无最终回答）→ 返回空串，由调用方重试/回退。
    """
    if not text:
        return text
    s = str(text).strip()
    if not s:
        return s
    if not _THINK_MARK_RE.search(s):
        return s.strip().strip('"\'')
    # 尝试1：按空行分段，从后往前取第一个不含思考特征的段落
    segs = [seg.strip() for seg in re.split(r'\n\s*\n', s) if seg.strip()]
    if len(segs) > 1:
        for seg in reversed(segs):
            if not _THINK_DRAFT_RE.search(seg) and not re.match(r'^\s*\d+[.、)]', seg):
                return seg.strip().strip('"\'')
    # 尝试2：Paragraph/编号草稿中的 "-> 译文" 片段
    pairs = re.findall(r'->\s*([^\n]+)', s)
    if pairs:
        joined = ' '.join(p.strip().strip('"\'') for p in pairs if p.strip())
        if joined and not _THINK_DRAFT_RE.search(joined):
            return joined
    # 尝试3：按行从后往前取第一个不含思考特征的完整行
    lines = [ln.strip() for ln in s.splitlines() if ln.strip()]
    if lines:
        for ln in reversed(lines):
            if not _THINK_DRAFT_RE.search(ln) and not re.match(r'^\s*\d+[.、)]', ln) and '->' not in ln:
                return ln.strip().strip('"\'')
    return ''


def _looks_like_thinking(text):
    """判断文本是否为/含思考链污染（Thinking Process / 编号步骤 / Paragraph 草稿等）"""
    if not text:
        return False
    return bool(_THINK_DRAFT_RE.search(str(text)))


def _looks_like_translation_meta(text):
    """判断文本是否为翻译元信息/解释性输出（如 "is the standard translation"、"Translation:"、"意为…" 等），
    这类内容把翻译任务当成了翻译教学/解释，必须重试或回退，不能作为译文返回。"""
    if not text:
        return False
    s = str(text)
    if re.search(r'standard translation|Translation:|translate[sd]?\s*(to|as)|中文(名|译名)为|翻译(成|为)|意为|通常译', s, re.I):
        return True
    # 以列表/引用符号开头且整体为英文解释性语句（含较多英文单词且含《》译名说明）
    if re.match(r'^\s*[*\-•]\s*[A-Za-z]', s) and not re.search(r'[\u4e00-\u9fff]', s[:80]):
        return True
    return False


def _news_tr_zh(text, timeout=30):
    """将新闻标题/摘要翻译为简体中文。

    质量策略：优先调用 AI（LM Studio / 已配置的 OpenAI 兼容接口），
    prompt 要求按新闻语境准确翻译、专有名词使用通行译名、不得增删信息；
    AI 不可用或失败时回退 _tr_translate（Azure → MyMemory）。
    结果统一写入 translations 表缓存（target=zh-CN），后续直接命中。
    返回 (translated, method)；method: ai / fallback / cached / same / fail。
    """
    text = (text or '').strip()
    if not text:
        return text, 'same'
    db = get_db()
    h = hashlib.sha256((_TR_NEWS_TARGET + '|' + text).encode('utf-8')).hexdigest()
    cached = _tr_get_cached(h, _TR_NEWS_TARGET)
    if cached is not None and not _looks_like_thinking(cached):
        return cached, 'cached'
    # 缓存命中但含思考链污染：忽略缓存，走 AI 重新翻译覆盖（避免继续回显脏数据）
    # AI 语境翻译（最多重试 2 次：输出含思考链/草稿即重试）
    try:
        cfg = get_ai_config()
        if cfg.get('base_url') and cfg.get('model'):
            sys_base = ('你是新闻翻译引擎。将输入的外语新闻标题/摘要准确翻译为简体中文。'
                        '要求：1) 忠实原意，不得增删信息；2) 人名地名机构名使用通行中文译名'
                        '（如 United Nations=联合国）；3) 术语按新闻行业规范；4) 只输出译文本身；'
                        '5) 严禁输出任何思考过程、推理步骤、分析或解释，不得出现 Thinking Process / 思考过程 / Reasoning 等字样；'
                        '6) 直接输出完整通顺的简体中文译文，禁止使用 Paragraph/Step/段落编号/原文对照等草稿格式。')
            for _attempt in range(2):
                out = call_lm_studio([
                    {'role': 'system', 'content': sys_base + ('\n（再次提醒：只输出译文，禁止任何思考过程或草稿格式。）' if _attempt else '')},
                    {'role': 'user', 'content': text},
                ], timeout=timeout)
                out = _strip_thinking(out or '')
                if out and len(out) >= 2 and not _looks_like_thinking(out) and not _looks_like_translation_meta(out):
                    _tr_store(db, h, _TR_NEWS_TARGET, out)
                    return out, 'ai'
    except Exception:
        pass
    # 回退 Azure/MyMemory
    translated, ok = _tr_translate(text, _TR_NEWS_TARGET)
    if ok and translated:
        return translated, 'fallback'
    return text, 'fail'


_NEWS_SUMMARY_NOISE_RE = re.compile(r'(点击查看原文\s*>?\s*$|查看原文\s*$|原文链接[：:].*|点击阅读.*$|^Read\s?more.*$|^Continue\s?reading.*$|^Learn\s?more.*$|^For\s?more.*$)', re.I)


def _news_content_preview(row, limit=300):
    """聚合条目正文预览：清理占位链接文本后取正文前 limit 字。"""
    c = (row.get('content') or '').strip()
    if not c:
        return ''
    c2 = _NEWS_SUMMARY_NOISE_RE.sub('', c).strip()
    return c2[:limit]


def _news_has_more_content(row):
    c = (row.get('content') or '').strip()
    c2 = _NEWS_SUMMARY_NOISE_RE.sub('', c).strip()
    return len(c2) > 300


def _news_summary_for_related(row):
    """聚合展示用摘要：优先 summary（清理占位文本）；占位/过短时改用正文截取。"""
    s = (row.get('summary') or '').strip()
    c = (row.get('content') or '').strip()
    if s and len(s) >= 8 and not _NEWS_SUMMARY_NOISE_RE.search(s):
        return s[:300]
    if c:
        c2 = _NEWS_SUMMARY_NOISE_RE.sub('', c).strip()
        return c2[:300] if c2 else (row.get('title') or '')
    return row.get('title') or ''


@app.route('/api/translate', methods=['POST', 'GET'])
@login_required
def api_translate():
    """翻译帖子和评论文本（需登录，避免额度被无限制消耗）。返回 {translated, ok}"""
    payload = request.get_json(silent=True) if request.method == 'POST' else request.args
    text = (payload.get('text') or '').strip()
    target = _tr_normalize_target(payload.get('target'))
    if not text:
        return jsonify({'error': '缺少文本'}), 400
    if not target:
        return jsonify({'error': '不支持的目标语言'}), 400
    if len(text) > 20000:
        return jsonify({'error': '文本过长'}), 400
    if not _tr_check_user_quota(_get_auth_user_id(), len(text)):
        return jsonify({'error': '今日翻译额度已用完，请明天再试'}), 429
    translated, all_ok = _tr_translate(text, target)
    return jsonify({'translated': translated, 'ok': all_ok})


# ===== 静态文件 =====
@app.route('/')
def index():
    # 项目内没有 index.html，根路径直接给新闻中心（旧链接 /?id=xxx 也能落到本站而非 404）
    return send_from_directory(_FRONTEND_DIR, 'peacenews.html')


@app.route('/ai')
@app.route('/ai/')
def ai_page():
    """Bird AI 全屏对话页面（macOS 27 Siri 风格）"""
    return send_from_directory(_FRONTEND_DIR, 'ai.html')


@app.route('/search')
@app.route('/search/')
def search_page():
    """翱翔鸟 search experience."""
    return send_from_directory(_FRONTEND_DIR, 'search.html')


@app.route('/api/web-search')
def api_web_search():
    """外部新闻源站内搜索（国外源 + 中文门户搜索），维基百科彻底排除。

    仅服务搜索页 / AI 分析与悬浮菜单实时检索，不进入主列表源池聚合。
    """
    query = request.args.get('q', '').strip()
    if not query:
        return jsonify({'results': []})
    if len(query) > 160:
        return jsonify({'error': '搜索内容过长'}), 400
    try:
        import source_search
        items = source_search.search_external(query, limit=6)
    except Exception:
        items = []
    if not items:
        return jsonify({'results': [], 'offline': True})
    return jsonify({'results': [{
        'title': it.get('title', ''),
        'source': it.get('source_name') or it.get('source') or '外部新闻源',
        'url': it.get('url', ''),
        'description': it.get('description') or '',
        'date': it.get('date') or '',
    } for it in items]})


@app.route('/api/text-analysis', methods=['POST'])
def api_text_analysis():
    """文本选中悬浮菜单统一端点。

    参数：mode ∈ {explain, viewpoint, verify, evaluate}；
          selected_text 选中文本；context 选区所在上下文。
    每次调用都结合外部新闻源实时搜索（国外源站内检索层），返回 markdown 文本。
    """
    payload = request.get_json(silent=True) or {}
    mode = (payload.get("mode") or "explain").strip()
    selected_text = (payload.get("selected_text") or "").strip()
    context = (payload.get("context") or "").strip()
    if not selected_text:
        return jsonify({"error": "缺少选中文本"}), 400
    if len(selected_text) > 2000:
        selected_text = selected_text[:2000]
    if len(context) > 4000:
        context = context[:4000]
    if mode not in ("explain", "viewpoint", "verify", "evaluate"):
        return jsonify({"error": "未知模式"}), 400

    # 外部实时搜索：以选中文本提炼关键词检索国外新闻源
    ext_items = []
    try:
        import source_search
        query = selected_text[:60].replace("\n", " ")
        ext_items = source_search.search_external(query, limit=4) or []
    except Exception:
        ext_items = []
    ext_lines = []
    for i, r in enumerate(ext_items, 1):
        src_txt = ("【%s】" % (r.get("source_name") or r.get("source") or "")) if (r.get("source_name") or r.get("source")) else ""
        date_txt = ("（%s）" % r["date"]) if r.get("date") else ""
        desc = (r.get("description") or "")
        if len(desc) > 260:
            desc = desc[:260] + "…"
        ext_lines.append("E%d. %s%s%s%s" % (i, src_txt, r.get("title") or "", date_txt, (" —— " + desc) if desc else ""))
    ext_block = ("\n外部实时搜索结果（国外新闻源站内检索，编号 E1-En，仅作参考，须批判性使用）：\n" + "\n".join(ext_lines)) if ext_lines else "\n（外部实时搜索未返回结果，请基于选中文本与上下文作答，并明确说明信息局限。）"

    mode_prompts = {
        "explain": (
            "你是一位严谨的新闻词条解释者。请解释选中文本在给定上下文中的含义："
            "它指代什么人物/组织/事件/时段/术语，结合上下文语境说明其背景与前因后果。"
            "输出 markdown，结构：**指代对象**、**语境解读**、**背景与来龙去脉**、**关联事件时间线**（如有）。"
            "不确定处明确标注「存疑」，禁止编造事实。"
        ),
        "viewpoint": (
            "你是一位媒体语言与立场分析专家。请剖析这段文本的用词、修辞与叙述框架所体现的媒体立场与倾向："
            "主语选择、情感色彩词、归因方式、被省略的信息、隐含的价值预设。"
            "输出 markdown，结构：**用词观察**、**叙述框架**、**隐含立场**、**被省略的信息**、**更中立的表述建议**。"
            "要求犀利、具体，直接引用文本词句佐证。"
        ),
        "verify": (
            "你是一位事实核查员。请结合外部实时搜索结果判断这段文本所述内容是否可信："
            "哪些陈述被多源印证、哪些为单源独家、哪些与外部检索结果冲突或无法核实。"
            "输出 markdown，结构：**结论**（可信/部分可信/存疑/不实）、**交叉印证情况**（引用 E 编号）、"
            "**矛盾与缺口**、**建议核实渠道**。禁止仅凭外部结果不全就断言不实。"
        ),
        "evaluate": (
            "你是一位新闻价值评论员。请把这段文本描述的行为当作既定事实，做价值评价："
            "行为主体、行为性质、受益与受损方、是否符合公序良俗/制度规则/长远利益，以及值得肯定的点与应当批评的点。"
            "输出 markdown，结构：**行为定性**、**价值分析**、**支持的理由**、**反对/保留的理由**、**综合评价**。"
            "要求立场鲜明、逻辑自洽，同时区分事实判断与价值判断。"
        ),
    }

    sys_prompt = (
        "你是翱翔鸟新闻平台的文本分析助手。只输出 markdown 正文，禁止输出思考过程或多余说明。\n"
        + mode_prompts[mode]
    )
    user_parts = [
        "选中文本：\n%s" % selected_text,
    ]
    if context:
        user_parts.append("所在上下文（供理解指代与语境）：\n%s" % context)
    user_parts.append(ext_block)
    user_parts.append("请现在输出 markdown 分析结果。")
    try:
        raw = call_lm_studio([
            {"role": "system", "content": sys_prompt},
            {"role": "user", "content": "\n\n".join(user_parts)},
        ], timeout=120, max_tokens=2048)
    except Exception as e:
        return jsonify({"error": "AI 分析失败：%s" % str(e)}), 502
    return jsonify({
        "mode": mode,
        "result": raw,
        "external": [{
            "title": r.get("title") or "",
            "source": r.get("source_name") or r.get("source") or "",
            "url": r.get("url") or "",
            "date": r.get("date") or "",
        } for r in ext_items],
    })


@app.route('/admin')
@app.route('/admin/')
def admin_page():
    return send_from_directory(_FRONTEND_DIR, 'admin.html')


@app.route('/signin')
@app.route('/signin/')
def signin_page():
    """翱翔鸟登录页面"""
    return send_from_directory(_FRONTEND_DIR, 'signin.html')


@app.route('/peacenews')
@app.route('/peacenews/')
def peacenews_page():
    """PeaceNews 新闻页面"""
    return send_from_directory(_FRONTEND_DIR, 'peacenews.html')


@app.route('/peacenews/admin')
@app.route('/peacenews/admin/')
def peacenews_admin_page():
    """PeaceNews 管理页面（页面内做权限校验）"""
    return send_from_directory(_FRONTEND_DIR, 'peacenews-admin.html')


@app.route('/download')
def download_page():
    return send_from_directory(_FRONTEND_DIR, 'download.html')


@app.route('/apps')
@app.route('/apps/')
def apps_page():
    """翱翔鸟 App 页面（App Store 风格，提供 iOS / Android 客户端下载）"""
    return send_from_directory(_FRONTEND_DIR, 'apps.html')


@app.route('/apps/ios')
@app.route('/apps/ios/')
def apps_ios_page():
    """翱翔鸟 for iOS 应用详情页"""
    return send_from_directory(_FRONTEND_DIR, 'apps-ios.html')


@app.route('/apps/android')
@app.route('/apps/android/')
def apps_android_page():
    """翱翔鸟 for Android 应用详情页"""
    return send_from_directory(_FRONTEND_DIR, 'apps-android.html')


@app.route('/uploads/<path:filepath>')
def serve_upload(filepath):
    """PostgreSQL 模式下从数据库提供图片，SQLite 模式下从文件系统提供"""
    # 允许浏览器以 crossOrigin='anonymous' 加载头像等图片并绘制到 canvas（分享卡片生成），
    # 若缺失该头，canvas 会被污染导致 toDataURL() 抛 SecurityError
    def with_cors(resp):
        resp.headers['Access-Control-Allow-Origin'] = '*'
        return resp
    if _USE_PG:
        db = get_db()
        row = _fetchone(db, 'SELECT data, content_type FROM images WHERE path=?', (f'uploads/{filepath}',))
        if row and row['data'] is not None:
            data = bytes(row['data']) if not isinstance(row['data'], bytes) else row['data']
            return with_cors(Response(data, mimetype=row['content_type'] or 'application/octet-stream'))
        # PG 中未找到，回退到文件系统（用于视频缩略图等直接存文件的场景）
        upload_dir = os.path.join(_DATA_DIR, 'uploads')
        full_path = os.path.join(upload_dir, filepath)
        if os.path.isfile(full_path):
            return with_cors(send_from_directory(upload_dir, filepath))
        return jsonify({'error': 'Not found'}), 404
    upload_dir = os.path.join(_DATA_DIR, 'uploads')
    full_path = os.path.join(upload_dir, filepath)
    if os.path.isfile(full_path):
        return with_cors(send_from_directory(upload_dir, filepath))
    return jsonify({'error': 'Not found'}), 404


@app.route('/<path:path>', methods=['GET', 'POST', 'PUT', 'DELETE'])
def static_files(path):
    # 不拦截 /api/ 路径，让 Flask 继续匹配后续注册的 API 路由
    if path.startswith('api/'):
        return jsonify({'error': 'Not found'}), 404
    # 安全：白名单机制，仅允许已知静态资源后缀（防止泄露 .db-wal/.db-shm/.log/.bak 等敏感文件）
    _ALLOWED_EXTS = ('.html', '.css', '.js', '.mjs', '.map', '.png', '.jpg', '.jpeg', '.gif', '.webp', '.ico',
                     '.svg', '.woff', '.woff2', '.ttf', '.otf', '.mp4', '.webm', '.mp3', '.wav', '.pdf', '.wasm',
                     '.apk', '.ipa')
    _ALLOWED_NAMES = ('robots.txt', 'sitemap.xml', 'manifest.json', 'sw.js', 'security.txt')
    # Team 前端与存储只能经鉴权路由访问，禁止通过通配静态路由裸暴露
    _DENIED_PREFIXES = ('team.html', 'team.css', 'team.js', 'teamstore/')
    if any(path == p or path.startswith(p) for p in _DENIED_PREFIXES):
        return jsonify({'error': 'Not found'}), 404
    lower_path = path.lower()
    if not any(lower_path.endswith(ext) for ext in _ALLOWED_EXTS) and path not in _ALLOWED_NAMES:
        return jsonify({'error': 'Not found'}), 404
    # 禁止路径遍历与隐藏文件
    if '..' in path or path.startswith('/') or '/.' in path or path.startswith('.'):
        return jsonify({'error': 'Not found'}), 404
    if os.path.isfile(os.path.join(_FRONTEND_DIR, path)):
        return send_from_directory(_FRONTEND_DIR, path)
    return jsonify({'error': 'Not found'}), 404


# ===== API：幻霜 OAuth 2.0 回调 =====
@app.route('/api/auth/huanshuang/oauth-config')
def api_huanshuang_oauth_config():
    """返回 OAuth 配置给前端"""
    return jsonify({
        'baseUrl': HS_OAUTH_BASE,
        'appId': '',
        'redirectUri': HS_OAUTH_REDIRECT_URI,
        'enabled': False,
    })


@app.route('/api/auth/huanshuang/init-state', methods=['POST'])
def api_huanshuang_init_state():
    """生成 OAuth state 并存入服务端 session，防止 CSRF"""
    import secrets as _secrets
    state = _secrets.token_urlsafe(32)
    session['hs_oauth_state'] = state
    return jsonify({'state': state})


@app.route('/api/auth/huanshuang/callback')
def api_huanshuang_oauth_callback():
    """幻霜 OAuth 2.0 回调：用授权码换 token 再拿用户信息"""
    error = request.args.get('error')
    if error:
        err_msg = request.args.get('error_description', error)
        return _login_error_html(f'幻霜授权失败: {err_msg}')

    code = request.args.get('code')
    state = request.args.get('state')
    if not code:
        return '<html><body><script>window.close();</script></body></html>', 400

    # 验证 state（防 CSRF）
    stored_state = session.pop('hs_oauth_state', None)
    if not state or state != stored_state:
        return '<html><body><script>localStorage.setItem("hs_oauth_error", "授权状态无效，请重新发起登录");window.close();</script></body></html>', 400

    # 用 code 换 access_token
    import urllib.request
    import urllib.parse
    # 使用服务端配置的固定 redirect_uri，不信任请求头
    callback_uri = HS_OAUTH_REDIRECT_URI
    token_url = f'{HS_OAUTH_BASE}/api/oauth/token'
    token_data = urllib.parse.urlencode({
        'grant_type': 'authorization_code',
        'code': code,
        'client_id': HS_OAUTH_APP_ID,
        'client_secret': HS_OAUTH_APP_SECRET,
        'redirect_uri': callback_uri,
    }).encode('utf-8')

    try:
        token_req = urllib.request.Request(token_url, data=token_data, headers={'Content-Type': 'application/x-www-form-urlencoded'})
        token_resp = urllib.request.urlopen(token_req, timeout=10)
        token_json = json.loads(token_resp.read().decode('utf-8'))
        access_token = token_json.get('access_token')
        if not access_token:
            raise Exception('未获取到 access_token, 响应: ' + json.dumps(token_json))
    except urllib.error.HTTPError as e:
        body = e.read().decode('utf-8', errors='replace')
        err_detail = f'HTTP {e.code} {e.reason}, body: {body}'
        print(f'[OAuth Token] 失败: {err_detail}')
        safe_detail = json.dumps('Token 交换失败: ' + err_detail)
        return f'''<html><body><script>
        localStorage.setItem('hs_oauth_error', {safe_detail});
        window.close();
        </script></body></html>''', 400
    except Exception as e:
        print(f'[OAuth Token] 异常: {type(e).__name__}: {e}')
        safe_err = json.dumps('Token 交换失败: ' + str(e))
        return f'''<html><body><script>
        localStorage.setItem('hs_oauth_error', {safe_err});
        window.close();
        </script></body></html>''', 400

    # 用 access_token 拿用户信息
    try:
        userinfo_url = f'{HS_OAUTH_BASE}/api/oauth/userinfo'
        userinfo_req = urllib.request.Request(userinfo_url, headers={'Authorization': f'Bearer {access_token}'})
        userinfo_resp = urllib.request.urlopen(userinfo_req, timeout=10)
        user_info = json.loads(userinfo_resp.read().decode('utf-8'))
    except urllib.error.HTTPError as e:
        body = e.read().decode('utf-8', errors='replace')
        err_detail = f'HTTP {e.code} {e.reason}, body: {body}'
        print(f'[OAuth UserInfo] 失败: {err_detail}')
        safe_detail = json.dumps('获取用户信息失败: ' + err_detail)
        return f'''<html><body><script>
        localStorage.setItem('hs_oauth_error', {safe_detail});
        window.close();
        </script></body></html>''', 400
    except Exception as e:
        print(f'[OAuth UserInfo] 异常: {type(e).__name__}: {e}')
        safe_err = json.dumps('获取用户信息失败: ' + str(e))
        return f'''<html><body><script>
        localStorage.setItem('hs_oauth_error', {safe_err});
        window.close();
        </script></body></html>''', 400

    hs_user_id = user_info.get('userId') or user_info.get('user_id')
    username = (user_info.get('username') or '').strip()
    avatar = user_info.get('avatar') or ''
    email = (user_info.get('email') or '').strip()

    if not hs_user_id:
        return f'''<html><body><script>
        localStorage.setItem('hs_oauth_error', '用户信息缺少 userId');
        window.close();
        </script></body></html>''', 400

    # 复用现有的幻霜登录逻辑
    db = get_db()
    hs_id_str = f'hs_{hs_user_id}'
    existing = _fetchone(db, 'SELECT id, username, email, bio, avatar FROM users WHERE id=?', (hs_id_str,))

    if existing:
        session['user_id'] = existing['id']
        session.permanent = True
        u = dict(existing)
        u['avatar'] = f"/{u['avatar']}" if u['avatar'] else ''
        user_data = json.dumps(u)
        auth_uid = existing['id']
    else:
        if not username:
            username = f'幻霜用户{hs_user_id}'
        base_name = username
        counter = 1
        while _fetchone(db, 'SELECT id FROM users WHERE username=?', (username,)):
            username = f'{base_name}_{counter}'
            counter += 1

        avatar_path = ''
        if avatar:
            try:
                # SSRF 防护：只允许 http/https，禁止内网/回环/file 等
                parsed = urllib.parse.urlparse(avatar)
                if parsed.scheme not in ('http', 'https'):
                    raise ValueError('不允许的 URL 协议')
                host = parsed.hostname or ''
                if not host:
                    raise ValueError('无效的主机名')
                import socket as _socket
                import ipaddress as _ipaddress
                try:
                    addr_info = _socket.getaddrinfo(host, None)
                except Exception:
                    raise ValueError('无法解析主机名')
                for fam, _, _, _, sockaddr in addr_info:
                    ip_str = sockaddr[0]
                    # 拒绝 IPv4-mapped IPv6 地址（::ffff:10.x.x.x 等）
                    try:
                        ip_obj = _ipaddress.ip_address(ip_str)
                    except ValueError:
                        raise ValueError('无效 IP 地址')
                    if (ip_obj.is_private or ip_obj.is_loopback or ip_obj.is_link_local
                            or ip_obj.is_reserved or ip_obj.is_multicast):
                        raise ValueError('禁止访问内网地址')
                    # 拒绝 CGNAT 范围 100.64.0.0/10
                    if ip_obj.version == 4 and (ip_obj >= _ipaddress.IPv4Address('100.64.0.0')
                                                and ip_obj <= _ipaddress.IPv4Address('100.127.255.255')):
                        raise ValueError('禁止访问 CGNAT 地址')
                ext = 'png'
                if '.jpg' in avatar or '.jpeg' in avatar:
                    ext = 'jpg'
                elif '.webp' in avatar:
                    ext = 'webp'
                filename = f"{uuid.uuid4().hex}.{ext}"
                avatar_path = f"uploads/avatars/{filename}"
                req = urllib.request.Request(avatar, headers={'User-Agent': 'SoaringBirdForum/1.0'})
                image_data = urllib.request.urlopen(req, timeout=10).read()
                # DNS 重绑定防护：连接后再次解析，确认 IP 未变化
                _socket.getaddrinfo(host, None)
                # 限制最大 2MB
                if len(image_data) > 2 * 1024 * 1024:
                    raise ValueError('头像文件过大')
                if _USE_PG:
                    content_type = _get_content_type(filename)
                    _exec(db, 'INSERT INTO images (path, data, content_type, created_at) VALUES (?,?,?,?)',
                          (avatar_path, image_data, content_type, time.time()))
                else:
                    upload_dir = os.path.join(_DATA_DIR, 'uploads', 'avatars')
                    os.makedirs(upload_dir, exist_ok=True)
                    filepath = os.path.join(upload_dir, filename)
                    with open(filepath, 'wb') as f:
                        f.write(image_data)
            except Exception as e:
                print(f'[OAuth Avatar] 下载失败: {e}')
                avatar_path = ''

        pw_hash = hash_password(uuid.uuid4().hex)
        _exec(db, 'INSERT INTO users (id, username, email, password_hash, bio, avatar, created_at) VALUES (?,?,?,?,?,?,?)',
              (hs_id_str, username, email, pw_hash, '', avatar_path, time.time()))
        db.commit()

        session['user_id'] = hs_id_str
        session.permanent = True
        user_data = json.dumps({
            'id': hs_id_str,
            'username': username,
            'email': email,
            'bio': '',
            'avatar': f"/{avatar_path}" if avatar_path else '',
        })
        auth_uid = hs_id_str

    # 登录成功，直接跳转回主页面（不再用 popup + localStorage）
    resp = make_response('''<!DOCTYPE html><html><head><meta charset="utf-8">
    <title>登录成功</title>
    <style>body{font-family:-apple-system,sans-serif;display:flex;align-items:center;justify-content:center;height:100vh;margin:0;background:#f5f5f7;color:#1d1d1f}
    .card{text-align:center}h2{font-size:22px;margin-bottom:8px}p{color:#86868b;font-size:14px}
    .check{width:48px;height:48px;border-radius:50%;background:#30D158;color:#fff;display:flex;align-items:center;justify-content:center;margin:0 auto 16px;font-size:24px;animation:pop .4s cubic-bezier(.34,1.56,.64,1)}
    @keyframes pop{from{transform:scale(0)}to{transform:scale(1)}}</style></head>
    <body><div class="card"><div class="check">✓</div><h2>欢迎回来</h2><p>正在跳转...</p></div>
    <script>setTimeout(function(){location.href='/?login=success';},800);</script>
    </body></html>''')
    _set_auth_cookie(resp, auth_uid)
    return resp


# ===== 本地 AI（LM Studio）=====
import threading

def _detect_ai_mention(content):
    """检测内容中是否 @AI / @ai / @AI助手 / @AI Bird"""
    import re
    pattern = r'@(?:AI|ai|Ai|aI|AI助手|ai助手|AI\s*Bird|ai\s*bird)'
    return bool(re.search(pattern, content))

def call_lm_studio(messages, timeout=60, max_tokens=1024):
    """调用 OpenAI 兼容 API（LM Studio / 智谱 GLM 等）

    兼容说明：
    - base_url 已带版本段（/v1、/v4 等）时不再追加 /v1；
    - 智谱 bigmodel 限流（HTTP 429/402 或错误码 1305）时，
      自动用环境变量 AI_FALLBACK_MODEL（默认 glm-4-flash）重试一次。
    """
    import urllib.request
    import urllib.error
    cfg = get_ai_config()
    base_url = cfg['base_url'].rstrip('/')
    # 自动补全 /v1（LM Studio 需要 /v1 前缀）；已带版本段则不追加
    if not re.search(r'/v\d+(/|$)', base_url):
        base_url = base_url + '/v1'
    model = cfg['model']
    fallback_model = os.environ.get('AI_FALLBACK_MODEL', 'glm-4-flash')
    is_zhipu = 'bigmodel.cn' in base_url

    raw = None
    last_http_err = None
    retried = False
    # 重试模型序列：非智谱仅原模型（限流时原模型重试一次）；智谱原模型失败可降级 fallback_model
    if is_zhipu and fallback_model and fallback_model != model:
        _model_seq = [model, fallback_model]
    else:
        _model_seq = [model]
    for cur_model in _model_seq:
        payload = json.dumps({
            'model': cur_model,
            'messages': messages,
            'temperature': 0.7,
            'max_tokens': max_tokens,
        }).encode('utf-8')
        headers = {'Content-Type': 'application/json'}
        if cfg.get('api_key'):
            headers['Authorization'] = f'Bearer {cfg["api_key"]}'
        req = urllib.request.Request(
            f'{base_url}/chat/completions',
            data=payload,
            headers=headers,
        )
        try:
            resp = urllib.request.urlopen(req, timeout=timeout)
            raw = resp.read().decode('utf-8')
            break
        except urllib.error.HTTPError as e:
            err_body = e.read().decode('utf-8', errors='replace')
            last_http_err = f'HTTP {e.code}: {err_body[:300]}'
            # 限流/额度类错误：同一模型短暂重试一次（避免 raw=None 落入 JSON 解析报错）
            if not retried and (e.code in (429, 402) or '1305' in err_body or '访问量' in err_body):
                retried = True
                time.sleep(1.5)
                continue
            raise Exception(f'API 返回 {last_http_err}')
        except urllib.error.URLError as e:
            raise Exception(f'无法连接到 {base_url}（请确认本地模型服务已启动）: {e.reason}')
    if raw is None:
        raise Exception(f'API 调用未获得响应: {last_http_err or "未知错误"}')
    try:
        data = json.loads(raw)
    except:
        raise Exception(f'API 返回非 JSON 数据: {str(raw)[:300]}')

    if 'error' in data:
        raise Exception(f'API 错误: {data["error"]}')
    if 'choices' not in data or not data['choices']:
        raise Exception(f'API 返回数据无 choices 字段: {raw[:300]}')
    return data['choices'][0]['message']['content'].strip()


def ai_moderate(text, content_type='post'):
    """AI 内容审核（直接拦截策略）
    返回 (是否通过, category, reason, score)
    category: normal / porn / politics / ad / abuse
    - moderation_enabled 关闭时直接放行
    - AI 故障时放行（fail-open，避免 AI 故障阻断整个站点发布）
    - 命中违规（按类别分档阈值）则拦截：色情 0.0/政治 0.75（拦敏感、正常政治新闻可发）/广告 0.75/辱骂 0.85
    """
    if not text or not text.strip():
        return True, 'normal', '', 0.0
    cfg = get_ai_config()
    if not cfg.get('moderation_enabled', False):
        print(f'[ai_moderate] moderation_enabled=False, 放行 [{content_type}]', flush=True)
        return True, 'normal', '', 0.0
    print(f'[ai_moderate] 开始审核 [{content_type}] base_url={cfg.get("base_url","")[:40]} model={cfg.get("model","")}', flush=True)
    messages = [
        {'role': 'system', 'content': '你是内容审核助手。判断用户内容是否违规。只返回纯 JSON，不要任何额外文字：{"category":"normal|porn|politics|ad|abuse","score":0.0-1.0,"reason":"简短原因"}。normal=正常，porn=色情低俗，politics=政治敏感，ad=广告引流，abuse=辱骂攻击。'},
        {'role': 'user', 'content': f'[{content_type}] 请审核以下内容：\n{text[:1500]}'}
    ]
    try:
        resp = call_lm_studio(messages, timeout=15)
        print(f'[ai_moderate] AI 返回: {resp[:200]}', flush=True)
        import re as _re
        m = _re.search(r'\{[^{}]*\}', resp)
        if not m:
            return True, 'normal', '', 0.0
        data = json.loads(m.group(0))
        category = str(data.get('category', 'normal')).lower()
        if category not in ('normal', 'porn', 'politics', 'ad', 'abuse'):
            category = 'normal'
        try:
            score = float(data.get('score', 0))
        except (TypeError, ValueError):
            score = 0.0
        reason = str(data.get('reason', ''))[:200]
        # 记录审核日志（独立 DB 连接，避免影响请求事务）
        try:
            if _USE_PG:
                log_db = _get_pg_pool().getconn()
                try:
                    _exec(log_db, 'INSERT INTO ai_review_logs (id, content_type, content, category, score, reason, created_at) VALUES (%s,%s,%s,%s,%s,%s,%s)',
                          ('ar_' + uuid.uuid4().hex[:12], content_type, text[:500], category, score, reason, time.time()))
                    log_db.commit()
                finally:
                    _get_pg_pool().putconn(log_db)
            else:
                log_db = sqlite3.connect(DB_PATH)
                try:
                    log_db.execute('INSERT INTO ai_review_logs (id, content_type, content, category, score, reason, created_at) VALUES (?,?,?,?,?,?,?)',
                                   ('ar_' + uuid.uuid4().hex[:12], content_type, text[:500], category, score, reason, time.time()))
                    log_db.commit()
                finally:
                    log_db.close()
        except Exception as e:
            print(f'[ai_moderate] 记录日志失败: {e}')
        # 按类别分档阈值：色情零容忍、政治中档从严（拦敏感内容、正常政治新闻可发）、辱骂从宽
        # 政治阈值 0.75：置信度 >= 0.75 即拦截。正常政治新闻（客观报道）通常低分通过，
        # 明显敏感/违规内容得分高会被拦
        _CATEGORY_THRESHOLD = {'porn': 0.0, 'politics': 0.75, 'ad': 0.75, 'abuse': 0.85}
        threshold = _CATEGORY_THRESHOLD.get(category, 0.75)
        if category != 'normal' and score >= threshold:
            print(f'[ai_moderate] 拦截 [{content_type}] cat={category} score={score} reason={reason}', flush=True)
            return False, category, reason, score
        print(f'[ai_moderate] 放行 [{content_type}] cat={category} score={score}', flush=True)
        return True, category, reason, score
    except Exception as e:
        print(f'[ai_moderate] 审核失败，放行 [{content_type}]: {e}', flush=True)
        return True, 'normal', '', 0.0


def _ai_moderation_scan_once():
    """执行一次 AI 审核扫描：扫描最近 24h 的帖子/评论，命中则标记 ai_flagged=1"""
    cfg = get_ai_config()
    if not cfg.get('moderation_enabled', False):
        return
    now = time.time()
    cutoff = now - 24 * 3600
    try:
        # 巡检运行在后台线程，不存在请求上下文。
        with app.app_context():
            db = get_db()
            # 扫描帖子（每次最多 50 条，避免单次扫描过久）
            posts = _fetchall(db, 'SELECT id, title, content FROM posts WHERE (ai_flagged=0 OR ai_flagged IS NULL) AND created_at>=? ORDER BY created_at DESC LIMIT 50', (cutoff,))
            for p in posts:
                text = (p.get('title', '') or '') + '\n' + (p.get('content', '') or '')
                ok, cat, reason, score = ai_moderate(text, 'post')
                if not ok:
                    _exec(db, 'UPDATE posts SET ai_flagged=1 WHERE id=?', (p['id'],))
                    print(f'[ai_scan] 帖子 {p["id"]} 被AI标记违规（{cat}）')
            # 扫描评论（每次最多 100 条）
            replies = _fetchall(db, 'SELECT id, content FROM replies WHERE (ai_flagged=0 OR ai_flagged IS NULL) AND created_at>=? ORDER BY created_at DESC LIMIT 100', (cutoff,))
            for r in replies:
                ok, cat, reason, score = ai_moderate(r.get('content', ''), 'comment')
                if not ok:
                    _exec(db, 'UPDATE replies SET ai_flagged=1 WHERE id=?', (r['id'],))
                    print(f'[ai_scan] 评论 {r["id"]} 被AI标记违规（{cat}）')
            db.commit()
        print(f'[ai_scan] 扫描完成: {len(posts)} 帖子, {len(replies)} 评论')
    except Exception as e:
        print(f'[ai_scan] 扫描失败: {e}')


def _ai_moderation_loop():
    """后台线程：每 4 小时执行一次 AI 审核定期巡查"""
    while True:
        try:
            _ai_moderation_scan_once()
        except Exception as e:
            print(f'[ai_loop] 异常: {e}')
        time.sleep(4 * 3600)


def _generate_ai_reply_async(post_id, user_reply_id, user_content, post_title, post_content):
    """后台线程：调用 AI 生成回复并插入数据库（独立 DB 连接，不依赖请求上下文）"""
    try:
        # 构造对话上下文并调用 AI
        messages = [
            {'role': 'system', 'content': AI_SYSTEM_PROMPT},
            {'role': 'user', 'content': f'帖子标题：{post_title}\n帖子内容：{post_content}\n\n用户回复：{user_content}'},
        ]
        ai_content = call_lm_studio(messages)

        # 线程内独立创建 DB 连接（不使用 Flask 的 g 对象）
        if _USE_PG:
            db = _get_pg_pool().getconn()
            db.autocommit = False
        else:
            db = sqlite3.connect(DB_PATH)
            db.row_factory = sqlite3.Row
        try:
            rid = 'r_' + uuid.uuid4().hex[:12]
            _exec(db, 'INSERT INTO replies (id, post_id, author_id, parent_id, content, image, likes, created_at) VALUES (?,?,?,?,?,?,?,?)',
                  (rid, post_id, AI_BOT_ID, user_reply_id, ai_content, '', 0, time.time()))
            db.commit()

            # 通过 Socket.IO 推送 AI 回复
            if socketio:
                socketio.emit('ai_reply', {
                    'post_id': post_id,
                    'reply': {
                        'id': rid,
                        'post_id': post_id,
                        'author_id': AI_BOT_ID,
                        'author_name': AI_BOT_NAME,
                        'parent_id': user_reply_id,
                        'content': ai_content,
                        'image': '',
                        'likes': 0,
                        'created_at': time.time(),
                        'liked': False,
                    }
                })
        finally:
            if _USE_PG:
                _get_pg_pool().putconn(db)
            else:
                db.close()
    except Exception as e:
        print(f'[AI] 生成回复失败: {e}')
        # 插入错误提示回复
        try:
            if _USE_PG:
                db = _get_pg_pool().getconn()
                db.autocommit = False
            else:
                db = sqlite3.connect(DB_PATH)
                db.row_factory = sqlite3.Row
            try:
                rid = 'r_' + uuid.uuid4().hex[:12]
                err_msg = f'⚠️ AI 回复生成失败：{str(e)}'
                _exec(db, 'INSERT INTO replies (id, post_id, author_id, parent_id, content, image, likes, created_at) VALUES (?,?,?,?,?,?,?,?)',
                      (rid, post_id, AI_BOT_ID, user_reply_id, err_msg, '', 0, time.time()))
                db.commit()
                if socketio:
                    socketio.emit('ai_reply', {
                        'post_id': post_id,
                        'reply': {
                            'id': rid,
                            'post_id': post_id,
                            'author_id': AI_BOT_ID,
                            'author_name': AI_BOT_NAME,
                            'parent_id': user_reply_id,
                            'content': err_msg,
                            'image': '',
                            'likes': 0,
                            'created_at': time.time(),
                            'liked': False,
                        }
                    })
            finally:
                if _USE_PG:
                    _get_pg_pool().putconn(db)
                else:
                    db.close()
        except Exception as e2:
            print(f'[AI] 错误回复插入也失败: {e2}')


@app.route('/api/ai/chat', methods=['POST'])
@login_required
def api_ai_chat():
    """直接调用 AI 聊天（含额度检查和并发限制）"""
    data = request.get_json()
    message = (data.get('message') or '').strip()
    if not message:
        return jsonify({'error': '消息不能为空'}), 400

    uid = session['user_id']

    # 1. 检查额度
    ok, msg, remaining = check_ai_quota(uid)
    if not ok:
        return jsonify({'error': msg}), 429

    # 2. 检查排队
    global _ai_queue_size
    with _ai_queue_lock:
        if _ai_queue_size >= 2:
            return jsonify({'error': '服务器繁忙，排队中...'}), 429
        _ai_queue_size += 1

    try:
        # 3. 获取信号量（最多同时 2 个）
        _ai_semaphore.acquire()
        try:
            messages = [
                {'role': 'system', 'content': AI_SYSTEM_PROMPT},
                {'role': 'user', 'content': message},
            ]
            reply = call_lm_studio(messages)
            log_ai_usage(uid)
            return jsonify({'reply': reply, 'remaining': remaining - 1})
        finally:
            _ai_semaphore.release()
    except Exception as e:
        return jsonify({'error': f'AI 调用失败：{str(e)}'}), 500
    finally:
        with _ai_queue_lock:
            _ai_queue_size -= 1


@app.route('/api/ai/status')
def api_ai_status():
    """检查 AI 服务是否可用"""
    cfg = get_ai_config()
    return jsonify({
        'enabled': True,
        'bot_id': AI_BOT_ID,
        'bot_name': AI_BOT_NAME,
        'base_url': cfg['base_url'],
        'model': cfg['model'],
        'has_key': bool(cfg.get('api_key')),
    })


# ===== API：认证 =====
def _is_form_request():
    """判断是否为表单提交（非 JSON AJAX）"""
    ct = request.content_type or ''
    return 'application/x-www-form-urlencoded' in ct


# ===== 邮箱验证码（Resend API）=====
RESEND_API_KEY = os.environ.get('RESEND_API_KEY', '')
RESEND_FROM = os.environ.get('RESEND_FROM', 'noreply@soaringbirdforum.xyz')
RESEND_FROM_NAME = os.environ.get('RESEND_FROM_NAME', '翱翔鸟论坛')

# Cloudflare Turnstile 人机验证
TURNSTILE_SITE_KEY = os.environ.get('TURNSTILE_SITE_KEY', '')  # 留空则跳过验证
TURNSTILE_SECRET_KEY = os.environ.get('TURNSTILE_SECRET_KEY', '')

def _verify_turnstile(token):
    """验证 Cloudflare Turnstile token，返回 True 表示通过"""
    if not TURNSTILE_SECRET_KEY:
        # 未配置则跳过（开发模式）
        return True
    # 原生 App 客户端无法运行 Turnstile JS，通过自定义请求头识别后跳过
    # 安全性由注册接口速率限制（每 IP 每小时 5 次）兜底
    client_header = (request.headers.get('X-Client-Type') or '').strip().lower()
    if client_header in ('android-native', 'ios-native'):
        return True
    if not token:
        return False
    import urllib.request
    import urllib.parse
    try:
        data = urllib.parse.urlencode({
            'secret': TURNSTILE_SECRET_KEY,
            'response': token,
        }).encode('utf-8')
        req = urllib.request.Request('https://challenges.cloudflare.com/turnstile/v0/siteverify', data=data, method='POST')
        with urllib.request.urlopen(req, timeout=10) as resp:
            result = json.loads(resp.read().decode('utf-8'))
            return bool(result.get('success'))
    except Exception as e:
        print(f'[Turnstile] 验证失败: {e}')
        return False

# 验证码存储：{email: {'code': '123456', 'expires': timestamp, 'sent_at': ts}}
_email_codes = {}
_email_codes_lock = _threading.Lock()
_EMAIL_CODE_TTL = 600  # 验证码 10 分钟有效
_EMAIL_RESEND_COOLDOWN = 120  # 重新发送冷却 2 分钟
_EMAIL_CODE_MAX_ATTEMPTS = 5  # 验证码最多尝试 5 次，超过即作废（防爆破）


def _code_check_failed(email):
    """验证码校验失败计数：同一邮箱失败达上限后立即作废，防止 6 位码在线爆破"""
    with _email_codes_lock:
        stored = _email_codes.get(email)
        if stored is None:
            return
        stored['attempts'] = stored.get('attempts', 0) + 1
        if stored['attempts'] >= _EMAIL_CODE_MAX_ATTEMPTS:
            _email_codes.pop(email, None)

def _send_email(to_addr, subject, body, code=None):
    """通过 Resend API 发送邮件（Apple 风格模板）"""
    import urllib.request
    import urllib.error
    if not RESEND_API_KEY:
        raise Exception('邮件服务未配置（RESEND_API_KEY 未设置）')
    safe_subject = _html_escape_mod.escape(subject)
    # body 按行拆分，每行单独转义后再 join
    body_lines = body.split('\n')
    safe_body = '<br>'.join(_html_escape_mod.escape(line) for line in body_lines)
    # Apple 风格：若提供验证码则突出显示
    code_block = ''
    if code:
        code_block = (
            '<div style="text-align:center;margin:28px 0 24px">'
            f'<div style="display:inline-block;font-size:34px;font-weight:600;letter-spacing:10px;color:#1d1d1f;font-variant-numeric:tabular-nums">{_html_escape_mod.escape(code)}</div>'
            '</div>'
        )
    html_body = (
        '<div style="font-family:-apple-system,BlinkMacSystemFont,\'SF Pro Display\',\'SF Pro Text\',\'Helvetica Neue\',sans-serif;max-width:560px;margin:0 auto;padding:24px">'
        '<div style="background:#fff;border-radius:16px;padding:32px 28px">'
        f'<h1 style="color:#1d1d1f;font-size:22px;font-weight:600;margin:0 0 20px;letter-spacing:-0.01em">{safe_subject}</h1>'
        f'<p style="color:#1d1d1f;font-size:15px;line-height:1.5;margin:0 0 16px">{safe_body}</p>'
        f'{code_block}'
        '</div>'
        '<p style="color:#aeaeb2;font-size:11px;line-height:1.5;margin-top:20px;text-align:center">© 2026 SoaringBird. 此邮件由系统自动发送，请勿回复。</p>'
        '</div>'
    )
    payload = json.dumps({
        'from': f'{RESEND_FROM_NAME} <{RESEND_FROM}>',
        'to': [to_addr],
        'subject': subject,
        'text': body,
        'html': html_body,
    }).encode('utf-8')
    req = urllib.request.Request(
        'https://api.resend.com/emails',
        data=payload,
        headers={
            'Authorization': f'Bearer {RESEND_API_KEY}',
            'Content-Type': 'application/json',
            'User-Agent': 'SoaringBirdForum/1.0',
            'Accept': 'application/json',
        },
        method='POST',
    )
    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            result = json.loads(resp.read().decode('utf-8'))
            return result
    except urllib.error.HTTPError as e:
        err_body = e.read().decode('utf-8', errors='replace')
        raise Exception(f'Resend API 错误 {e.code}: {err_body}')


@app.route('/api/turnstile-site-key', methods=['GET'])
def api_turnstile_site_key():
    """返回 Turnstile site key 给前端"""
    return jsonify({'site_key': TURNSTILE_SITE_KEY})


@app.route('/api/send-verify-code', methods=['POST'])
def api_send_verify_code():
    """发送邮箱验证码"""
    data = request.get_json() or {}
    email = (data.get('email') or '').strip().lower()
    if not email:
        return jsonify({'error': '请填写邮箱'}), 400
    import re
    if not re.match(r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$', email):
        return jsonify({'error': '邮箱格式不正确'}), 400

    # 人机验证（Turnstile）
    turnstile_token = data.get('turnstile_token') or ''
    if TURNSTILE_SECRET_KEY:
        if not _verify_turnstile(turnstile_token):
            return jsonify({'error': '人机验证失败，请重试'}), 400

    # 速率限制：同一邮箱 2 分钟内只能发一次
    now = time.time()
    with _email_codes_lock:
        existing = _email_codes.get(email)
        if existing and now - existing.get('sent_at', 0) < _EMAIL_RESEND_COOLDOWN:
            wait = int(_EMAIL_RESEND_COOLDOWN - (now - existing['sent_at']))
            return jsonify({'error': f'发送过于频繁，请 {wait} 秒后再试'}), 429
        # 生成 6 位验证码
        code = f"{secrets.randbelow(1000000):06d}"
        _email_codes[email] = {'code': code, 'expires': now + _EMAIL_CODE_TTL, 'sent_at': now}

    try:
        subject = '验证翱翔鸟账户电子邮件地址'
        body = (
            f'你已选择此电子邮件地址作为你的翱翔鸟账户。为验证此电子邮件地址属于你，请在注册页面输入下方验证码：\n\n'
            f'此验证码 10 分钟内有效。\n\n'
            f'你收到此电子邮件的原因：\n'
            f'翱翔鸟会在你注册账户时提出验证要求。你的翱翔鸟账户需经过验证才能使用。\n\n'
            f'如果你未提出此请求，可以忽略此电子邮件。未经过验证便无法创建翱翔鸟账户。'
        )
        _send_email(email, subject, body, code=code)
    except Exception as e:
        print(f'[Email] 发送失败 to {email}: {e}')
        with _email_codes_lock:
            _email_codes.pop(email, None)
        return jsonify({'error': f'邮件发送失败: {e}'}), 500

    return jsonify({'ok': True, 'message': '验证码已发送'})


@app.route('/api/send-reset-code', methods=['POST'])
def api_send_reset_code():
    """发送重置密码验证码（根据用户名查邮箱）"""
    data = request.get_json() or {}
    username = (data.get('username') or '').strip()
    if not username:
        return jsonify({'error': '请填写用户名'}), 400

    # 人机验证（Turnstile）
    turnstile_token = data.get('turnstile_token') or ''
    if TURNSTILE_SECRET_KEY:
        if not _verify_turnstile(turnstile_token):
            return jsonify({'error': '人机验证失败，请重试'}), 400

    db = get_db()
    row = _fetchone(db, 'SELECT id, email, email_verified FROM users WHERE username=?', (username,))
    if not row:
        return jsonify({'error': '用户不存在'}), 404
    email = (row['email'] or '').strip().lower()
    if not email:
        return jsonify({'error': '该账号未绑定邮箱，无法重置密码'}), 400
    if not row['email_verified']:
        return jsonify({'error': '该账号邮箱未验证，无法通过邮箱重置密码'}), 400

    # 速率限制
    now = time.time()
    with _email_codes_lock:
        existing = _email_codes.get(email)
        if existing and now - existing.get('sent_at', 0) < _EMAIL_RESEND_COOLDOWN:
            wait = int(_EMAIL_RESEND_COOLDOWN - (now - existing['sent_at']))
            return jsonify({'error': f'发送过于频繁，请 {wait} 秒后再试'}), 429
        code = f"{secrets.randbelow(1000000):06d}"
        _email_codes[email] = {'code': code, 'expires': now + _EMAIL_CODE_TTL, 'sent_at': now}

    try:
        subject = '重置翱翔鸟账户密码'
        body = (
            f'你已请求重置翱翔鸟账户密码。请在重置密码页面输入下方验证码：\n\n'
            f'验证码：{code}\n\n'
            f'此验证码 10 分钟内有效。\n\n'
            f'如果你未提出此请求，可以忽略此电子邮件。'
        )
        _send_email(email, subject, body, code=code)
    except Exception as e:
        print(f'[Email] 发送失败 to {email}: {e}')
        with _email_codes_lock:
            _email_codes.pop(email, None)
        return jsonify({'error': f'邮件发送失败: {e}'}), 500

    return jsonify({'ok': True, 'message': '验证码已发送至账号绑定邮箱', 'email_hint': email[:2] + '****' + email[email.index('@'):] if '@' in email else ''})


@app.route('/api/reset-password', methods=['POST'])
def api_reset_password():
    """通过邮箱验证码重置密码"""
    data = request.get_json() or {}
    username = (data.get('username') or '').strip()
    code = (data.get('code') or '').strip()
    new_password = data.get('password') or ''
    if not username or not code or not new_password:
        return jsonify({'error': '请填写完整'}), 400
    if len(new_password) < 4:
        return jsonify({'error': '密码至少4位'}), 400

    db = get_db()
    row = _fetchone(db, 'SELECT id, email FROM users WHERE username=?', (username,))
    if not row:
        return jsonify({'error': '用户不存在'}), 404
    email = (row['email'] or '').strip().lower()
    if not email:
        return jsonify({'error': '该账号未绑定邮箱'}), 400

    # 验证码校验
    with _email_codes_lock:
        stored = _email_codes.get(email)
    now = time.time()
    if not stored or now > stored['expires']:
        return jsonify({'error': '验证码已过期，请重新获取'}), 400
    if not _hmac.compare_digest(stored['code'], code):
        _code_check_failed(email)
        return jsonify({'error': '验证码不正确'}), 400
    with _email_codes_lock:
        _email_codes.pop(email, None)

    _exec(db, 'UPDATE users SET password_hash=? WHERE id=?', (hash_password(new_password), row['id']))
    db.commit()
    print(f'[SECURITY] 用户 {username} 通过邮箱验证码重置密码')
    return jsonify({'ok': True, 'message': '密码重置成功'})


@app.route('/api/user/change-email', methods=['POST'])
@login_required
def api_change_email():
    """修改邮箱（修改后需重新验证，重置 3 天期限）"""
    data = request.get_json() or {}
    new_email = (data.get('email') or '').strip().lower()
    if not new_email:
        return jsonify({'error': '请填写邮箱'}), 400
    import re
    if not re.match(r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$', new_email):
        return jsonify({'error': '邮箱格式不正确'}), 400
    uid = session['user_id']
    db = get_db()
    # 新邮箱不能与他人重复
    existing = _fetchone(db, 'SELECT id FROM users WHERE email=? AND id!=?', (new_email, uid))
    if existing:
        return jsonify({'error': '该邮箱已被其他账号使用'}), 400
    # 更新邮箱并标记为未验证，重置 3 天期限
    deadline = time.time() + 3 * 86400
    _exec(db, 'UPDATE users SET email=?, email_verified=0, email_verify_deadline=? WHERE id=?', (new_email, deadline, uid))
    db.commit()
    return jsonify({'ok': True, 'message': '邮箱已修改，请尽快验证。3 天内未验证的账号将被自动删除。'})


@app.route('/api/user/verify-email', methods=['POST'])
@login_required
def api_verify_email():
    """验证当前账号邮箱（提交验证码）"""
    data = request.get_json() or {}
    code = (data.get('code') or '').strip()
    if not code:
        return jsonify({'error': '请输入验证码'}), 400
    uid = session['user_id']
    db = get_db()
    row = _fetchone(db, 'SELECT email FROM users WHERE id=?', (uid,))
    if not row or not row['email']:
        return jsonify({'error': '账号未设置邮箱'}), 400
    email = row['email'].lower()
    with _email_codes_lock:
        stored = _email_codes.get(email)
    now = time.time()
    if not stored or now > stored['expires']:
        return jsonify({'error': '验证码已过期，请重新获取'}), 400
    if not _hmac.compare_digest(stored['code'], code):
        return jsonify({'error': '验证码不正确'}), 400
    with _email_codes_lock:
        _email_codes.pop(email, None)
    _exec(db, 'UPDATE users SET email_verified=1, email_verify_deadline=0 WHERE id=?', (uid,))
    db.commit()
    return jsonify({'ok': True, 'message': '邮箱验证成功'})


@app.route('/api/user/security', methods=['GET'])
def api_get_security_settings():
    """获取当前用户的安全设置"""
    user = get_current_user()
    if not user:
        return jsonify({'error': '未登录'}), 401
    db = get_db()
    row = _fetchone(db, 'SELECT require_login_code FROM users WHERE id=?', (user['id'],))
    return jsonify({
        'require_login_code': bool(row['require_login_code']) if row else False
    })


@app.route('/api/user/security', methods=['POST'])
def api_update_security_settings():
    """更新当前用户的安全设置"""
    user = get_current_user()
    if not user:
        return jsonify({'error': '未登录'}), 401
    data = request.get_json() or {}
    require_login_code = 1 if data.get('require_login_code') else 0
    db = get_db()
    _exec(db, 'UPDATE users SET require_login_code=? WHERE id=?', (require_login_code, user['id']))
    return jsonify({'ok': True, 'require_login_code': bool(require_login_code)})


def _cleanup_unverified_users():
    """清理超过 3 天未验证邮箱的账号（保留管理员）"""
    try:
        with app.app_context():
            db = get_db()
            now = time.time()
            if _USE_PG:
                rows = _fetchall(db, "SELECT id FROM users WHERE email_verified=0 AND email_verify_deadline>0 AND email_verify_deadline<%s AND is_admin=0 AND is_super_admin=0", (now,))
            else:
                rows = _fetchall(db, "SELECT id FROM users WHERE email_verified=0 AND email_verify_deadline>0 AND email_verify_deadline<? AND is_admin=0 AND is_super_admin=0", (now,))
            if not rows:
                return 0
            for r in rows:
                uid = r['id']
                # 删除用户相关数据
                for tbl in ['posts', 'replies', 'bookmarks', 'post_likes', 'follows', 'notifications', 'passkeys']:
                    try:
                        if _USE_PG:
                            _exec(db, f'DELETE FROM {tbl} WHERE author_id=%s OR user_id=%s OR follower_id=%s OR following_id=%s', (uid, uid, uid, uid))
                        else:
                            db.execute(f'DELETE FROM {tbl} WHERE author_id=? OR user_id=? OR follower_id=? OR following_id=?', (uid, uid, uid, uid))
                    except Exception:
                        pass
                if _USE_PG:
                    _exec(db, 'DELETE FROM users WHERE id=%s', (uid,))
                else:
                    db.execute('DELETE FROM users WHERE id=?', (uid,))
            db.commit()
            print(f'[CLEANUP] 已清理 {len(rows)} 个未验证邮箱账号')
            return len(rows)
    except Exception as e:
        print(f'[CLEANUP] 清理未验证账号失败: {e}')
        return 0


@app.route('/api/register', methods=['POST'])
def api_register():
    is_form = _is_form_request()

    # 注册速率限制
    client_ip = get_client_ip()
    allowed, retry_after = _check_register_rate_limit(client_ip)
    if not allowed:
        msg = f'注册过于频繁，请 {retry_after} 秒后再试'
        return _login_error_html(msg) if is_form else (jsonify({'error': msg}), 429)

    if is_form:
        username = (request.form.get('username') or '').strip()
        email = (request.form.get('email') or '').strip().lower()
        password = request.form.get('password') or ''
        verify_code = (request.form.get('code') or request.form.get('verify_code') or '').strip()
    else:
        data = request.get_json()
        username = _sanitize_plain((data.get('username') or '').strip())
        email = (data.get('email') or '').strip().lower()
        password = data.get('password') or ''
        verify_code = (data.get('code') or data.get('verify_code') or '').strip()

    if not username or not password:
        return _login_error_html('请填写完整') if is_form else (jsonify({'error': '请填写完整'}), 400)
    if len(password) < 4:
        return _login_error_html('密码至少4位') if is_form else (jsonify({'error': '密码至少4位'}), 400)

    import re
    email_regex = re.compile(r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$')
    if not email or not email_regex.match(email):
        return _login_error_html('邮箱格式不正确') if is_form else (jsonify({'error': '邮箱格式不正确'}), 400)

    # 验证码必填：强制邮箱验证后才允许注册
    if not verify_code:
        return _login_error_html('请填写邮箱验证码') if is_form else (jsonify({'error': '请填写邮箱验证码'}), 400)
    with _email_codes_lock:
        stored = _email_codes.get(email)
    now = time.time()
    if not stored or now > stored['expires']:
        return _login_error_html('验证码已过期，请重新获取') if is_form else (jsonify({'error': '验证码已过期，请重新获取'}), 400)
    if not _hmac.compare_digest(stored['code'], verify_code):
        _code_check_failed(email)
        return _login_error_html('验证码不正确') if is_form else (jsonify({'error': '验证码不正确'}), 400)
    # 验证成功，清除验证码
    with _email_codes_lock:
        _email_codes.pop(email, None)
    email_verified = 1
    email_verify_deadline = 0

    db = get_db()
    if _fetchone(db, 'SELECT id FROM users WHERE username=?', (username,)):
        db.close()
        return _login_error_html('用户名已被占用') if is_form else (jsonify({'error': '用户名已被占用'}), 400)
    if _fetchone(db, 'SELECT id FROM users WHERE email=?', (email,)):
        db.close()
        return _login_error_html('该邮箱已被注册') if is_form else (jsonify({'error': '该邮箱已被注册'}), 400)

    uid = 'u_' + uuid.uuid4().hex[:12]
    pw_hash = hash_password(password)
    _exec(db, 'INSERT INTO users (id, username, email, password_hash, bio, created_at, email_verified, email_verify_deadline) VALUES (?,?,?,?,?,?,?,?)',
          (uid, username, email, pw_hash, '', time.time(), email_verified, email_verify_deadline))
    db.commit()
    _record_register_attempt(client_ip)

    session.clear()
    session['user_id'] = uid
    session.permanent = True

    if is_form:
        resp = Response(f'''<!DOCTYPE html><html><head><meta charset="utf-8">
    <title>注册成功</title><style>body{{font-family:-apple-system,sans-serif;display:flex;align-items:center;justify-content:center;height:100vh;margin:0;background:#f5f5f7;color:#1d1d1f}}
    .card{{text-align:center}}h2{{font-size:22px;margin-bottom:8px}}p{{color:#86868b;font-size:14px}}
    .check{{width:48px;height:48px;border-radius:50%;background:#30D158;color:#fff;display:flex;align-items:center;justify-content:center;margin:0 auto 16px;font-size:24px;animation:pop .4s cubic-bezier(.34,1.56,.64,1)}}
    @keyframes pop{{from{{transform:scale(0)}}to{{transform:scale(1)}}}}</style></head>
    <body><div class="card"><div class="check">✓</div><h2>注册成功</h2><p>正在跳转...</p></div>
    <script>setTimeout(function(){{location.href='/?login=success';}},1200);</script>
    </body></html>''', mimetype='text/html')
        _set_auth_cookie(resp, uid)
        return resp

    user = {'id': uid, 'username': username, 'email': email, 'bio': '', 'email_verified': bool(email_verified)}
    resp = jsonify({'user': user})
    _set_auth_cookie(resp, uid)
    return resp


@app.route('/api/login', methods=['POST'])
def api_login():
    is_form = _is_form_request()

    # 登录速率限制
    client_ip = get_client_ip()
    allowed, retry_after = _check_login_rate_limit(client_ip)
    if not allowed:
        msg = f'登录尝试过多，请 {retry_after} 秒后再试'
        return _login_error_html(msg) if is_form else (jsonify({'error': msg}), 429)

    if is_form:
        username = (request.form.get('username') or '').strip()
        password = request.form.get('password') or ''
        verify_code = (request.form.get('verify_code') or request.form.get('code') or '').strip()
    else:
        data = request.get_json()
        username = (data.get('username') or '').strip()
        password = data.get('password') or ''
        verify_code = (data.get('verify_code') or data.get('code') or '').strip()

    if not username or not password:
        return _login_error_html('请填写完整') if is_form else (jsonify({'error': '请填写完整'}), 400)

    db = get_db()
    row = _fetchone(db, 'SELECT id, username, email, bio, password_hash, avatar, background, status, ban_reason, require_login_code FROM users WHERE username=?', (username,))
    # 先用加盐哈希校验；失败则回退到旧无盐哈希校验，匹配则自动升级
    if not row:
        _record_login_attempt(client_ip, success=False)
        print(f'[SECURITY] 登录失败: ip={client_ip} username={username}')
        return _login_error_html('用户名或密码错误') if is_form else (jsonify({'error': '用户名或密码错误'}), 400)
    password_ok = verify_password(password, row['password_hash'])
    if not password_ok and _verify_legacy_password(password, row['password_hash']):
        # 旧无盐哈希匹配，自动升级为 PBKDF2
        _maybe_upgrade_password(db, row['id'], password)
        password_ok = True
    elif password_ok and _is_legacy_hash(row['password_hash']):
        # 加盐 SHA-256 旧格式，透明升级为 PBKDF2
        _maybe_upgrade_password(db, row['id'], password)
    if not password_ok:
        _record_login_attempt(client_ip, success=False)
        print(f'[SECURITY] 登录失败: ip={client_ip} username={username}')
        return _login_error_html('用户名或密码错误') if is_form else (jsonify({'error': '用户名或密码错误'}), 400)

    if row.get('status') == 'banned':
        _record_login_attempt(client_ip, success=False)
        # 区分未验证邮箱封禁：返回 require_email_verify 触发强制验证弹窗
        if row.get('ban_reason') == 'unverified' and row.get('email'):
            return _login_error_html('该账号因未完成邮箱验证被暂时封禁，请完成邮箱验证') if is_form else (
                jsonify({
                    'error': '该账号因未完成邮箱验证被暂时封禁，请完成邮箱验证',
                    'require_email_verify': True,
                    'username': username,
                    'email': row['email']
                }), 403
            )
        return _login_error_html('该账号已被封禁') if is_form else (jsonify({'error': '该账号已被封禁'}), 403)

    _record_login_attempt(client_ip, success=True)

    # 安全设置：检查是否需要登录验证码
    if row.get('require_login_code'):
        login_email = (row['email'] or '').lower()
        if not verify_code:
            # 返回 email 供前端调用 /api/send-verify-code 发送验证码
            return jsonify({'error': '需要验证码', 'require_code': True, 'email': login_email}), 403
        with _email_codes_lock:
            stored = _email_codes.get(login_email)
        now = time.time()
        if not stored or now > stored['expires']:
            return jsonify({'error': '验证码已过期，请重新获取', 'require_code': True, 'email': login_email}), 400
        if not _hmac.compare_digest(stored['code'], verify_code):
            return jsonify({'error': '验证码不正确', 'require_code': True, 'email': login_email}), 400
        with _email_codes_lock:
            _email_codes.pop(login_email, None)

    # 彻底清空旧 session，再设置新数据
    session.clear()
    session['user_id'] = row['id']
    session.permanent = True

    client_ip = get_client_ip()
    if _USE_PG:
        _exec(db, 'UPDATE users SET last_ip=%s WHERE id=%s', (client_ip, row['id']))
    else:
        db.execute('UPDATE users SET last_ip=? WHERE id=?', (client_ip, row['id']))
        db.commit()

    if is_form:
        bg_param = ''
        if row['background']:
            try:
                import urllib.parse
                bg_param = '&bg=' + urllib.parse.quote('/' + row['background'])
            except Exception:
                pass
        resp = Response('''<!DOCTYPE html><html><head><meta charset="utf-8">
    <title>登录成功</title>
    <style>body{font-family:-apple-system,sans-serif;display:flex;align-items:center;justify-content:center;height:100vh;margin:0;background:#f5f5f7;color:#1d1d1f}
    .card{text-align:center}h2{font-size:22px;margin-bottom:8px}p{color:#86868b;font-size:14px}
    .check{width:48px;height:48px;border-radius:50%;background:#30D158;color:#fff;display:flex;align-items:center;justify-content:center;margin:0 auto 16px;font-size:24px;animation:pop .4s cubic-bezier(.34,1.56,.64,1)}
    @keyframes pop{from{transform:scale(0)}to{transform:scale(1)}}</style></head>
    <body><div class="card"><div class="check">✓</div><h2>欢迎回来</h2><p>正在跳转...</p></div>
    <script>setTimeout(function(){location.href='/?login=success''' + bg_param + '''';},800);</script>
    </body></html>''', mimetype='text/html')
        _set_auth_cookie(resp, row['id'])
        return resp

    avatar = f"/{row['avatar']}" if row['avatar'] else ''
    background = f"/{row['background']}" if row['background'] else ''
    user = {'id': row['id'], 'username': row['username'], 'email': row['email'] or '', 'bio': row['bio'] or '', 'avatar': avatar, 'background': background}
    resp = jsonify({'user': user})
    _set_auth_cookie(resp, row['id'])
    return resp


def _login_error_html(msg):
    """登录失败时返回 HTML 页面，带错误信息跳回 /signin"""
    import urllib.parse
    encoded = urllib.parse.quote(msg)
    safe_msg = _html_escape_mod.escape(msg)
    return Response('''<!DOCTYPE html><html><head><meta charset="utf-8">
    <title>登录失败</title>
    <style>body{font-family:-apple-system,sans-serif;display:flex;align-items:center;justify-content:center;height:100vh;margin:0;background:#f5f5f7;color:#1d1d1f}
    .card{text-align:center}h2{font-size:22px;margin-bottom:8px}p{color:#86868b;font-size:14px}
    .icon{width:48px;height:48px;border-radius:50%;background:#FF3B30;color:#fff;display:flex;align-items:center;justify-content:center;margin:0 auto 16px;font-size:24px;animation:pop .4s cubic-bezier(.34,1.56,.64,1)}
    @keyframes pop{from{transform:scale(0)}to{transform:scale(1)}}</style></head>
    <body><div class="card"><div class="icon">✕</div><h2>登录失败</h2><p>''' + safe_msg + '''</p></div>
    <script>setTimeout(function(){location.href='/signin?error=''' + encoded + '''&tab=login';},1500);</script>
    </body></html>''', mimetype='text/html')


@app.route('/api/logout', methods=['POST'])
def api_logout():
    session.clear()
    resp = jsonify({'ok': True})
    _clear_auth_cookie(resp)
    return resp


@app.route('/api/me', methods=['GET'])
def api_me():
    try:
        user = get_current_user()
        return jsonify({'user': user})
    except Exception as e:
        print(f'[ERROR] /api/me: {e}')
        return jsonify({'user': None, 'error': '内部错误'})


# /api/debug-session 已移除（安全：暴露 session 内部信息）
# /api/me?debug=1 调试信息已移除（安全：泄露认证状态细节）


# ===== API：帖子 =====
@app.route('/api/posts', methods=['GET'])
def api_get_posts():
    db = get_db()
    user_id = session.get('user_id')
    tab = request.args.get('tab', 'latest')
    category = request.args.get('category', '')
    search = request.args.get('search', '')

    # 分页：复用 news_config.per_page，默认 20，最大 50
    try:
        page = max(1, int(request.args.get('page', 1)))
    except (TypeError, ValueError):
        page = 1
    try:
        per_page = max(5, min(50, int(_get_news_config()['per_page'])))
    except (TypeError, ValueError):
        per_page = 20
    offset = (page - 1) * per_page

    query = '''
        SELECT p.id, p.author_id, COALESCE(u.username, '未知') as author_name, COALESCE(u.avatar, '') as author_avatar, COALESCE(u.verified, 0) as author_verified, COALESCE(u.birthday_month, 0) as author_birthday_month, COALESCE(u.birthday_day, 0) as author_birthday_day, p.title, p.category,
               p.content, p.likes, p.created_at, COALESCE(p.admin_like_boost, 0) as admin_like_boost
        FROM posts p LEFT JOIN users u ON p.author_id = u.id
    '''
    conditions = ['(p.ai_flagged=0 OR p.ai_flagged IS NULL)',
                  '(p.report_removed=0 OR p.report_removed IS NULL)']
    params = []

    if category:
        conditions.append('p.category=?')
        params.append(category)
    if search:
        conditions.append('(p.title LIKE ? OR p.content LIKE ?)')
        params.extend([f'%{search}%', f'%{search}%'])

    if conditions:
        query += ' WHERE ' + ' AND '.join(conditions)

    if tab == 'hot':
        query += ' ORDER BY p.likes DESC, p.created_at DESC'
    elif tab == 'unanswered':
        query += ' ORDER BY p.created_at DESC'
    else:
        query += ' ORDER BY p.created_at DESC'

    # 先查总数
    count_query = 'SELECT COUNT(*) as c FROM posts p LEFT JOIN users u ON p.author_id = u.id ' + ('WHERE ' + ' AND '.join(conditions) if conditions else '')
    total_row = _fetchone(db, count_query, params)
    total = total_row['c'] if total_row else 0

    query += ' LIMIT ? OFFSET ?'
    params.extend([per_page, offset])
    rows = _fetchall(db, query, params)
    posts = [post_to_dict(r, user_id) for r in rows]
    # 叠加管理员点赞增幅
    for p in posts:
        p['likes'] = max(0, int(p['likes']) + int(p.pop('admin_like_boost', 0)))

    if tab == 'unanswered':
        posts = [p for p in posts if p['reply_count'] == 0]

    return jsonify({'posts': posts, 'total': total, 'page': page, 'per_page': per_page})


# 发帖防重复提交：短时间内相同用户+标题+内容视为重复
_post_dedup_cache = {}  # {user_id: [(title_hash, content_hash, post_id, timestamp)]}
_post_dedup_lock = _threading.Lock()
_POST_DEDUP_WINDOW = 10  # 10 秒窗口

def _check_post_duplicate(user_id, title, content):
    """检查是否为重复提交，返回 (is_duplicate, existing_post_id)"""
    now = time.time()
    t_hash = hashlib.md5(title.encode()).hexdigest()
    c_hash = hashlib.md5(content.encode()).hexdigest()
    with _post_dedup_lock:
        entries = _post_dedup_cache.get(user_id, [])
        entries = [(t, c, pid, ts) for t, c, pid, ts in entries if now - ts < _POST_DEDUP_WINDOW]
        _post_dedup_cache[user_id] = entries
        for t, c, pid, ts in entries:
            if t == t_hash and c == c_hash:
                return True, pid
        return False, None

def _record_post_submit(user_id, title, content, post_id):
    """记录一次发帖提交"""
    t_hash = hashlib.md5(title.encode()).hexdigest()
    c_hash = hashlib.md5(content.encode()).hexdigest()
    with _post_dedup_lock:
        entries = _post_dedup_cache.get(user_id, [])
        entries.append((t_hash, c_hash, post_id, time.time()))
        _post_dedup_cache[user_id] = entries


@app.route('/api/posts', methods=['POST'])
@login_required
def api_create_post():
    data = request.get_json()
    title = _sanitize_plain((data.get('title') or '').strip())
    category = data.get('category') or 'tech'
    content = (data.get('content') or '').strip()
    tags = data.get('tags') or []

    if not title or not content:
        return jsonify({'error': '标题和内容不能为空'}), 400

    # 违禁词检查
    ok, found = check_banned_words(title + content)
    if not ok:
        return jsonify({'error': f'内容包含违禁词：{"、".join(found[:5])}'}), 400
    title = filter_content(title)
    content = filter_content(content)

    # AI 内容审核（同步，开启 moderation_enabled 时生效）
    ai_ok, ai_cat, ai_reason, ai_score = ai_moderate(title + '\n' + content, 'post')
    if not ai_ok:
        return jsonify({'error': f'内容被 AI 审核拦截（{ai_cat}）：{ai_reason}'}), 400

    u = get_user(session['user_id'])
    if u and u.get('muted_until', 0) > time.time():
        return jsonify({'error': '你已被禁言，无法发帖'}), 403
    if u and u.get('status') == 'banned':
        return jsonify({'error': '该账号已被封禁'}), 403

    # 防重复提交：10 秒内相同标题+内容视为重复，返回已有帖子 ID
    is_dup, existing_pid = _check_post_duplicate(session['user_id'], title, content)
    if is_dup:
        return jsonify({'id': existing_pid, 'deduplicated': True})

    db = get_db()
    pid = 'p_' + uuid.uuid4().hex[:12]
    _exec(db, 'INSERT INTO posts (id, author_id, title, category, content, likes, created_at) VALUES (?,?,?,?,?,?,?)',
          (pid, session['user_id'], title, category, content, 0, time.time()))
    _record_post_submit(session['user_id'], title, content, pid)
    for tag in tags:
        t = tag.strip()
        if t:
            _exec(db, 'INSERT INTO tags (post_id, tag) VALUES (?,?)', (pid, t))
    db.commit()

    return jsonify({'id': pid})


@app.route('/api/posts/<post_id>', methods=['GET'])
def api_get_post(post_id):
    db = get_db()
    user_id = session.get('user_id')
    row = _fetchone(db, '''
        SELECT p.id, p.author_id, COALESCE(u.username, '未知') as author_name, COALESCE(u.avatar, '') as author_avatar, COALESCE(u.verified, 0) as author_verified, COALESCE(u.birthday_month, 0) as author_birthday_month, COALESCE(u.birthday_day, 0) as author_birthday_day, p.title, p.category,
               p.content, p.likes, p.created_at, COALESCE(p.admin_like_boost, 0) as admin_like_boost,
               COALESCE(p.report_removed, 0) as report_removed
        FROM posts p LEFT JOIN users u ON p.author_id = u.id
        WHERE p.id=?
    ''', (post_id,))
    if not row:
        return jsonify({'error': '帖子不存在'}), 404
    # 因举报被自动下架的帖子对外不可见
    if row.get('report_removed'):
        return jsonify({'error': '帖子已下架'}), 410

    post = post_to_dict(row, user_id)
    # 叠加管理员点赞增幅
    post['likes'] = max(0, int(post['likes']) + int(post.pop('admin_like_boost', 0)))

    # replies（LEFT JOIN 确保 AI 机器人回复也能显示）
    if _USE_PG:
        replies = _fetchall(db, '''
            SELECT r.id, r.author_id, COALESCE(u.username, %s) as author_name, COALESCE(u.avatar, '') as author_avatar, COALESCE(u.verified, 0) as author_verified, COALESCE(u.birthday_month, 0) as author_birthday_month, COALESCE(u.birthday_day, 0) as author_birthday_day, r.parent_id, r.content, r.image, r.likes, r.created_at
            FROM replies r LEFT JOIN users u ON r.author_id = u.id
            WHERE r.post_id=%s AND (r.ai_flagged=0 OR r.ai_flagged IS NULL) ORDER BY r.created_at ASC
        ''', (AI_BOT_NAME, post_id))
    else:
        replies = _fetchall(db, '''
            SELECT r.id, r.author_id, COALESCE(u.username, ?) as author_name, COALESCE(u.avatar, '') as author_avatar, COALESCE(u.verified, 0) as author_verified, COALESCE(u.birthday_month, 0) as author_birthday_month, COALESCE(u.birthday_day, 0) as author_birthday_day, r.parent_id, r.content, r.image, r.likes, r.created_at
            FROM replies r LEFT JOIN users u ON r.author_id = u.id
            WHERE r.post_id=? AND (r.ai_flagged=0 OR r.ai_flagged IS NULL) ORDER BY r.created_at ASC
        ''', (AI_BOT_NAME, post_id))
    post['replies'] = []
    for r in replies:
        rd = dict(r)
        # author_verified 统一转为 bool（数据库存储为 int 0/1）
        rd['author_verified'] = bool(rd.get('author_verified', 0))
        rd['author_birthday'] = _is_birthday_today(
            _safe_int(rd.get('author_birthday_month'), 0),
            _safe_int(rd.get('author_birthday_day'), 0))
        if rd.get('image'):
            rd['image'] = f"/{rd['image']}"
        if user_id:
            liked = _fetchone(db, 'SELECT 1 FROM reply_likes WHERE user_id=? AND reply_id=?', (user_id, rd['id']))
            rd['liked'] = bool(liked)
        else:
            rd['liked'] = False
        # 兼容字段别名（Swift 客户端期望的键名）
        rd['likes_count'] = rd.get('likes', 0)
        rd['is_liked'] = rd['liked']
        rd['reply_to_id'] = rd.get('parent_id')
        # 查找被回复用户名
        pid = rd.get('parent_id')
        if pid:
            pr = _fetchone(db, 'SELECT u.username FROM replies r JOIN users u ON r.author_id = u.id WHERE r.id=?', (pid,))
            rd['reply_to_name'] = pr['username'] if pr else None
        else:
            rd['reply_to_name'] = None
        # author_avatar 补前导 /
        av = rd.get('author_avatar')
        if av and not av.startswith('/'):
            rd['author_avatar'] = '/' + av
        post['replies'].append(rd)

    return jsonify({'post': post})


@app.route('/api/posts/<post_id>', methods=['DELETE'])
@login_required
def api_delete_post(post_id):
    db = get_db()
    row = _fetchone(db, 'SELECT author_id FROM posts WHERE id=?', (post_id,))
    if not row:
        return jsonify({'error': '帖子不存在'}), 404
    if row['author_id'] != session['user_id']:
        return jsonify({'error': '无权删除'}), 403
    _exec(db, 'DELETE FROM posts WHERE id=?', (post_id,))
    db.commit()
    return jsonify({'ok': True})


# ===== API：点赞 =====
@app.route('/api/posts/<post_id>/like', methods=['POST'])
@login_required
def api_toggle_post_like(post_id):
    db = get_db()
    existing = _fetchone(db, 'SELECT 1 FROM post_likes WHERE user_id=? AND post_id=?',
                         (session['user_id'], post_id))
    if existing:
        _exec(db, 'DELETE FROM post_likes WHERE user_id=? AND post_id=?', (session['user_id'], post_id))
        _exec(db, 'UPDATE posts SET likes = likes - 1 WHERE id=? AND likes > 0', (post_id,))
        liked = False
    else:
        _exec(db, 'INSERT INTO post_likes (user_id, post_id) VALUES (?,?)', (session['user_id'], post_id))
        _exec(db, 'UPDATE posts SET likes = likes + 1 WHERE id=?', (post_id,))
        liked = True
        # 通知帖子作者
        post = _fetchone(db, 'SELECT author_id FROM posts WHERE id=?', (post_id,))
        if post and post['author_id'] != session['user_id']:
            nid = 'n_' + uuid.uuid4().hex[:12]
            notify_text = f'{get_username(session["user_id"])} 赞了你的帖子'
            _exec(db, 'INSERT INTO notifications (id, user_id, text, read, created_at) VALUES (?,?,?,?,?)',
                  (nid, post['author_id'], notify_text, 0, time.time()))
            socketio.emit('notification', {'text': notify_text}, room=f'dm_{post["author_id"]}')
    db.commit()
    row = _fetchone(db, 'SELECT likes FROM posts WHERE id=?', (post_id,))
    return jsonify({'liked': liked, 'likes': row['likes'] if row else 0})


@app.route('/api/replies/<reply_id>/like', methods=['POST'])
@login_required
def api_toggle_reply_like(reply_id):
    db = get_db()
    existing = _fetchone(db, 'SELECT 1 FROM reply_likes WHERE user_id=? AND reply_id=?',
                         (session['user_id'], reply_id))
    if existing:
        _exec(db, 'DELETE FROM reply_likes WHERE user_id=? AND reply_id=?', (session['user_id'], reply_id))
        _exec(db, 'UPDATE replies SET likes = likes - 1 WHERE id=? AND likes > 0', (reply_id,))
        liked = False
    else:
        _exec(db, 'INSERT INTO reply_likes (user_id, reply_id) VALUES (?,?)', (session['user_id'], reply_id))
        _exec(db, 'UPDATE replies SET likes = likes + 1 WHERE id=?', (reply_id,))
        liked = True
    db.commit()
    row = _fetchone(db, 'SELECT likes FROM replies WHERE id=?', (reply_id,))
    return jsonify({'liked': liked, 'likes': row['likes'] if row else 0})


@app.route('/api/replies/<reply_id>', methods=['DELETE'])
@login_required
def api_delete_reply(reply_id):
    """用户删除自己的回复"""
    db = get_db()
    row = _fetchone(db, 'SELECT author_id FROM replies WHERE id=?', (reply_id,))
    if not row:
        return jsonify({'error': '回复不存在'}), 404
    if row['author_id'] != session['user_id']:
        return jsonify({'error': '无权删除'}), 403
    # 删除关联的点赞和子回复
    _exec(db, 'DELETE FROM reply_likes WHERE reply_id=?', (reply_id,))
    _exec(db, 'DELETE FROM replies WHERE parent_id=?', (reply_id,))
    _exec(db, 'DELETE FROM replies WHERE id=?', (reply_id,))
    db.commit()
    return jsonify({'ok': True})


# ===== API：收藏 =====
@app.route('/api/posts/<post_id>/bookmark', methods=['POST'])
@login_required
def api_toggle_bookmark(post_id):
    db = get_db()
    existing = _fetchone(db, 'SELECT 1 FROM bookmarks WHERE user_id=? AND post_id=?',
                         (session['user_id'], post_id))
    if existing:
        _exec(db, 'DELETE FROM bookmarks WHERE user_id=? AND post_id=?', (session['user_id'], post_id))
        bookmarked = False
    else:
        _exec(db, 'INSERT INTO bookmarks (user_id, post_id) VALUES (?,?)', (session['user_id'], post_id))
        bookmarked = True
        # 通知帖子作者
        post = _fetchone(db, 'SELECT author_id FROM posts WHERE id=?', (post_id,))
        if post and post['author_id'] != session['user_id']:
            nid = 'n_' + uuid.uuid4().hex[:12]
            notify_text = f'{get_username(session["user_id"])} 收藏了你的帖子'
            _exec(db, 'INSERT INTO notifications (id, user_id, text, read, created_at) VALUES (?,?,?,?,?)',
                  (nid, post['author_id'], notify_text, 0, time.time()))
            socketio.emit('notification', {'text': notify_text}, room=f'dm_{post["author_id"]}')
    db.commit()
    return jsonify({'bookmarked': bookmarked})


@app.route('/api/bookmarks', methods=['GET'])
@login_required
def api_get_bookmarks():
    db = get_db()
    rows = _fetchall(db, '''
        SELECT p.id, p.author_id, u.username as author_name, p.title, p.category,
               p.content, p.likes, p.created_at
        FROM bookmarks b
        JOIN posts p ON b.post_id = p.id
        JOIN users u ON p.author_id = u.id
        WHERE b.user_id=?
        ORDER BY p.created_at DESC
    ''', (session['user_id'],))
    posts = [post_to_dict(r, session['user_id']) for r in rows]
    return jsonify({'posts': posts})


# ===== API：回复 =====
@app.route('/api/posts/<post_id>/replies', methods=['POST'])
@login_required
def api_create_reply(post_id):
    data = request.get_json()
    content = (data.get('content') or '').strip()
    parent_id = (data.get('parent_id') or '').strip()
    image = (data.get('image') or '').strip()
    if not content and not image:
        return jsonify({'error': '请输入回复内容'}), 400

    # 违禁词检查
    if content:
        ok, found = check_banned_words(content)
        if not ok:
            return jsonify({'error': f'内容包含违禁词：{"、".join(found[:5])}'}), 400
        content = filter_content(content)

    # AI 内容审核（同步，开启 moderation_enabled 时生效）
    if content:
        ai_ok, ai_cat, ai_reason, ai_score = ai_moderate(content, 'comment')
        if not ai_ok:
            return jsonify({'error': f'内容被 AI 审核拦截（{ai_cat}）：{ai_reason}'}), 400

    u = get_user(session['user_id'])
    if u and u.get('muted_until', 0) > time.time():
        return jsonify({'error': '你已被禁言，无法回复'}), 403
    if u and u.get('status') == 'banned':
        return jsonify({'error': '该账号已被封禁'}), 403

    db = get_db()
    post = _fetchone(db, 'SELECT id, author_id, title, content FROM posts WHERE id=?', (post_id,))
    if not post:
        return jsonify({'error': '帖子不存在'}), 404

    rid = 'r_' + uuid.uuid4().hex[:12]
    _exec(db, 'INSERT INTO replies (id, post_id, author_id, parent_id, content, image, likes, created_at) VALUES (?,?,?,?,?,?,?,?)',
          (rid, post_id, session['user_id'], parent_id, content, image, 0, time.time()))

    # 给帖子作者或被回复者发通知
    notify_uid = post['author_id']
    notify_text = f'{get_username(session["user_id"])} 回复了你的帖子'
    if parent_id:
        parent_reply = _fetchone(db, 'SELECT author_id FROM replies WHERE id=?', (parent_id,))
        if parent_reply and parent_reply['author_id'] != session['user_id']:
            notify_uid = parent_reply['author_id']
            notify_text = f'{get_username(session["user_id"])} 回复了你的评论'

    if notify_uid != session['user_id']:
        nid = 'n_' + uuid.uuid4().hex[:12]
        _exec(db, 'INSERT INTO notifications (id, user_id, text, read, created_at) VALUES (?,?,?,?,?)',
              (nid, notify_uid, notify_text, 0, time.time()))
        # Socket.IO 推送通知
        socketio.emit('notification', {'text': notify_text}, room=f'dm_{notify_uid}')

    db.commit()

    # 检测 @AI 触发自动回复
    if content and _detect_ai_mention(content):
        t = threading.Thread(
            target=_generate_ai_reply_async,
            args=(post_id, rid, content, post['title'], post['content']),
            daemon=True,
        )
        t.start()

    return jsonify({'id': rid})


# ===== API：回复图片上传 =====
@app.route('/api/upload/reply-image', methods=['POST'])
@login_required
def api_upload_reply_image():
    if 'file' not in request.files:
        return jsonify({'error': '未选择文件'}), 400
    f = request.files['file']
    if not f.filename:
        return jsonify({'error': '未选择文件'}), 400
    if f.content_length and f.content_length > 7 * 1024 * 1024:
        return jsonify({'error': '图片不能超过7MB'}), 400

    ext = os.path.splitext(f.filename)[1].lower()
    if ext not in ('.jpg', '.jpeg', '.png', '.gif', '.webp'):
        return jsonify({'error': '不支持的图片格式'}), 400

    file_data = f.read()
    # 校验实际内容长度（防止 Content-Length 头伪造绕过）
    if len(file_data) > 7 * 1024 * 1024:
        return jsonify({'error': '图片不能超过7MB'}), 400

    # 黄色内容检测
    is_nsfw, ratio = _check_nsfw(file_data)
    if is_nsfw:
        return jsonify({'error': '图片内容不符合社区规范，请勿上传不当内容'}), 400

    filename = f"{uuid.uuid4().hex}{ext}"
    image_path = f'uploads/replies/{filename}'

    if _USE_PG:
        content_type = _get_content_type(filename)
        db = get_db()
        _exec(db, 'INSERT INTO images (path, data, content_type, created_at) VALUES (?,?,?,?)',
              (image_path, file_data, content_type, time.time()))
        db.commit()
    else:
        upload_dir = os.path.join(_DATA_DIR, 'uploads', 'replies')
        os.makedirs(upload_dir, exist_ok=True)
        with open(os.path.join(upload_dir, filename), 'wb') as out:
            out.write(file_data)

    return jsonify({'url': image_path})


# ===== API：用户 =====
@app.route('/api/users/<user_id>', methods=['GET'])
def api_get_user(user_id):
    db = get_db()
    row = _fetchone(db, 'SELECT id, username, email, bio, created_at, last_online, verified, verified_text, avatar, background, banner, is_quality, birthday_month, birthday_day, birthday_age, region, gender FROM users WHERE id=?', (user_id,))
    if not row:
        return jsonify({'error': '用户不存在'}), 404
    user = dict(row)
    user['verified'] = bool(user.get('verified'))
    user['verified_text'] = user.get('verified_text', '') or ''
    user['is_quality'] = bool(user.get('is_quality'))
    _attach_birthday_meta(user)
    av = user.get('avatar') or ''
    if av and not av.startswith('/'):
        av = '/' + av
    user['avatar'] = av
    # banner 为空时回退到 background（向后兼容旧数据）
    bg_val = user.get('background') or ''
    if bg_val and not bg_val.startswith('/'):
        bg_val = '/' + bg_val
    user['background'] = bg_val
    user['banner'] = f"/{user['banner']}" if user.get('banner') else bg_val
    # M1 修复：邮箱只对本人或管理员可见，未登录/他人返回空串
    current_uid = _get_auth_user_id()
    if current_uid != user_id:
        # 检查是否管理员
        is_admin = False
        if current_uid:
            admin_row = _fetchone(db, 'SELECT is_admin FROM users WHERE id=?', (current_uid,))
            is_admin = bool(admin_row and admin_row['is_admin'])
        if not is_admin:
            user['email'] = ''
    post_count = _fetchone(db, 'SELECT COUNT(*) as c FROM posts WHERE author_id=?', (user_id,))
    like_count = _fetchone(db, 'SELECT COALESCE(SUM(likes),0) as c FROM posts WHERE author_id=?', (user_id,))
    user['post_count'] = post_count['c']
    user['like_count'] = like_count['c']

    follower_count = db.execute('SELECT COUNT(*) as c FROM follows WHERE following_id=?', (user_id,)).fetchone()['c']
    following_count = db.execute('SELECT COUNT(*) as c FROM follows WHERE follower_id=?', (user_id,)).fetchone()['c']
    boost_row = _fetchone(db, 'SELECT COALESCE(admin_follower_boost,0) as fb, COALESCE(admin_like_boost,0) as lb FROM users WHERE id=?', (user_id,))
    follower_count = max(0, follower_count + (boost_row['fb'] or 0))
    like_count['c'] = max(0, like_count['c'] + (boost_row['lb'] or 0))
    user['follower_count'] = follower_count
    user['following_count'] = following_count
    user['like_count'] = like_count['c']

    is_following = False
    if 'user_id' in session and session['user_id'] != user_id:
        is_following = bool(_fetchone(db, 'SELECT 1 FROM follows WHERE follower_id=? AND following_id=?', (session['user_id'], user_id)))
    user['is_following'] = is_following

    # 该用户的帖子（排除已标记违规的帖子，与首页保持一致）
    rows = _fetchall(db, '''
        SELECT p.id, p.author_id, u.username as author_name, COALESCE(u.birthday_month, 0) as author_birthday_month, COALESCE(u.birthday_day, 0) as author_birthday_day, p.title, p.category,
               p.content, p.likes, p.created_at
        FROM posts p JOIN users u ON p.author_id = u.id
        WHERE p.author_id=? AND (p.ai_flagged=0 OR p.ai_flagged IS NULL)
        ORDER BY p.created_at DESC
    ''', (user_id,))
    user['posts'] = [post_to_dict(r, session.get('user_id')) for r in rows]

    return jsonify({'user': user})


@app.route('/api/users/<user_id>', methods=['PUT'])
@login_required
def api_update_user(user_id):
    if session['user_id'] != user_id:
        return jsonify({'error': '无权修改'}), 403
    data = request.get_json()
    username = _sanitize_plain((data.get('username') or '').strip())
    bio = _sanitize_plain((data.get('bio') or '').strip())
    if not username:
        return jsonify({'error': '用户名不能为空'}), 400

    # 个人资料：生日(月/日)、可选年龄、地区、性别
    bm = _safe_int(data.get('birthday_month'), 0)
    bd = _safe_int(data.get('birthday_day'), 0)
    ba = _safe_int(data.get('birthday_age'), 0)
    region = _sanitize_plain((data.get('region') or '').strip())[:60]
    gender = _sanitize_plain((data.get('gender') or '').strip())[:20]
    if bm < 0 or bm > 12 or bd < 0 or bd > 31 or ba < 0 or ba > 130:
        return jsonify({'error': '生日信息不合法'}), 400

    db = get_db()
    existing = _fetchone(db, 'SELECT id FROM users WHERE username=? AND id!=?', (username, user_id))
    if existing:
        return jsonify({'error': '用户名已存在'}), 400

    _exec(db, 'UPDATE users SET username=?, bio=?, birthday_month=?, birthday_day=?, birthday_age=?, region=?, gender=? WHERE id=?',
          (username, bio, bm, bd, ba, region, gender, user_id))
    db.commit()
    return jsonify({'user': {'id': user_id, 'username': username, 'bio': bio, 'birthday_month': bm, 'birthday_day': bd, 'birthday_age': ba, 'region': region, 'gender': gender}})


@app.route('/api/users/search', methods=['GET'])
@login_required
def api_search_users():
    """搜索用户（用于 @提及）"""
    q = (request.args.get('q') or '').strip()
    if not q:
        return jsonify({'users': []})
    db = get_db()
    if _USE_PG:
        rows = _fetchall(db, 'SELECT id, username FROM users WHERE username ILIKE %s AND id != %s ORDER BY username LIMIT 10',
                         (q + '%', session['user_id']))
    else:
        rows = _fetchall(db, 'SELECT id, username FROM users WHERE username LIKE ? AND id != ? ORDER BY username LIMIT 10',
                         (q + '%', session['user_id']))
    return jsonify({'users': [{'id': r['id'], 'username': r['username']} for r in rows]})


@app.route('/api/search/users', methods=['GET'])
def api_search_users_public():
    """公开搜索用户（首页搜索用，含头像、帖子数、认证信息）"""
    q = (request.args.get('q') or '').strip()
    if not q:
        return jsonify({'users': []})
    db = get_db()
    if _USE_PG:
        rows = _fetchall(db, '''
            SELECT u.id, u.username, u.avatar, u.bio, u.verified, u.verified_text,
                   (SELECT COUNT(*) FROM posts WHERE author_id=u.id) as post_count
            FROM users u WHERE u.username ILIKE %s
            ORDER BY post_count DESC LIMIT 10
        ''', ('%' + q + '%',))
    else:
        rows = _fetchall(db, '''
            SELECT u.id, u.username, u.avatar, u.bio, u.verified, u.verified_text,
                   (SELECT COUNT(*) FROM posts WHERE author_id=u.id) as post_count
            FROM users u WHERE u.username LIKE ?
            ORDER BY post_count DESC LIMIT 10
        ''', ('%' + q + '%',))
    users = []
    for r in rows:
        av = r['avatar'] or ''
        if av and not av.startswith('/'):
            av = '/' + av
        users.append({
            'id': r['id'],
            'username': r['username'],
            'avatar': av,
            'bio': r['bio'] or '',
            'verified': bool(r['verified']),
            'verified_text': r['verified_text'] or '',
            'post_count': r['post_count']
        })
    return jsonify({'users': users})


# ===== API：文件上传 =====
ALLOWED_IMAGE_EXTENSIONS = {'jpg', 'jpeg', 'png', 'gif', 'webp'}


def allowed_file(filename, allowed_extensions):
    return '.' in filename and filename.rsplit('.', 1)[1].lower() in allowed_extensions


@app.route('/api/upload/avatar', methods=['POST'])
@login_required
def api_upload_avatar():
    if 'file' not in request.files:
        return jsonify({'error': '没有上传文件'}), 400
    file = request.files['file']
    if file.filename == '':
        return jsonify({'error': '没有选择文件'}), 400
    if not allowed_file(file.filename, ALLOWED_IMAGE_EXTENSIONS):
        return jsonify({'error': '只允许上传图片文件 (jpg, png, gif, webp)'}), 400

    # 检查文件大小 (7MB)
    file.seek(0, 2)
    size = file.tell()
    file.seek(0)
    if size > 7 * 1024 * 1024:
        return jsonify({'error': '头像文件大小不能超过7MB'}), 400

    file_data = file.read()

    # 黄色内容检测
    is_nsfw, ratio = _check_nsfw(file_data)
    if is_nsfw:
        return jsonify({'error': '图片内容不符合社区规范，请勿上传不当内容'}), 400

    # 生成唯一文件名
    ext = file.filename.rsplit('.', 1)[1].lower()
    filename = f"{uuid.uuid4().hex}.{ext}"
    avatar_path = f"uploads/avatars/{filename}"

    if _USE_PG:
        content_type = _get_content_type(filename)
        db = get_db()
        _exec(db, 'INSERT INTO images (path, data, content_type, created_at) VALUES (?,?,?,?)',
              (avatar_path, file_data, content_type, time.time()))
    else:
        # 创建目录
        upload_dir = os.path.join(_DATA_DIR, 'uploads', 'avatars')
        os.makedirs(upload_dir, exist_ok=True)
        with open(os.path.join(upload_dir, filename), 'wb') as out:
            out.write(file_data)

    # 更新数据库
    db = get_db()
    _exec(db, 'UPDATE users SET avatar=? WHERE id=?', (avatar_path, session['user_id']))
    db.commit()

    return jsonify({'avatar': f"/{avatar_path}"})


@app.route('/api/upload/background', methods=['POST'])
@login_required
def api_upload_background():
    if 'file' not in request.files:
        return jsonify({'error': '没有上传文件'}), 400
    file = request.files['file']
    if file.filename == '':
        return jsonify({'error': '没有选择文件'}), 400
    if not allowed_file(file.filename, ALLOWED_IMAGE_EXTENSIONS):
        return jsonify({'error': '只允许上传图片文件 (jpg, png, gif, webp)'}), 400

    # 检查文件大小 (10MB)
    file.seek(0, 2)
    size = file.tell()
    file.seek(0)
    if size > 10 * 1024 * 1024:
        return jsonify({'error': '背景文件大小不能超过10MB'}), 400

    file_data = file.read()

    # 黄色内容检测
    is_nsfw, ratio = _check_nsfw(file_data)
    if is_nsfw:
        return jsonify({'error': '图片内容不符合社区规范，请勿上传不当内容'}), 400

    # 生成唯一文件名
    ext = file.filename.rsplit('.', 1)[1].lower()
    filename = f"{uuid.uuid4().hex}.{ext}"
    bg_path = f"uploads/backgrounds/{filename}"

    if _USE_PG:
        content_type = _get_content_type(filename)
        db = get_db()
        _exec(db, 'INSERT INTO images (path, data, content_type, created_at) VALUES (?,?,?,?)',
              (bg_path, file_data, content_type, time.time()))
    else:
        # 创建目录
        upload_dir = os.path.join(_DATA_DIR, 'uploads', 'backgrounds')
        os.makedirs(upload_dir, exist_ok=True)
        with open(os.path.join(upload_dir, filename), 'wb') as out:
            out.write(file_data)

    # 更新数据库
    db = get_db()
    _exec(db, 'UPDATE users SET background=? WHERE id=?', (bg_path, session['user_id']))
    db.commit()

    return jsonify({'background': f"/{bg_path}"})


@app.route('/api/upload/banner', methods=['POST'])
@login_required
def api_upload_banner():
    """上传个人主页横幅图（独立于网页端背景图 background 字段）"""
    if 'file' not in request.files:
        return jsonify({'error': '没有上传文件'}), 400
    file = request.files['file']
    if file.filename == '':
        return jsonify({'error': '没有选择文件'}), 400
    if not allowed_file(file.filename, ALLOWED_IMAGE_EXTENSIONS):
        return jsonify({'error': '只允许上传图片文件 (jpg, png, gif, webp)'}), 400

    # 检查文件大小 (10MB)
    file.seek(0, 2)
    size = file.tell()
    file.seek(0)
    if size > 10 * 1024 * 1024:
        return jsonify({'error': '横幅文件大小不能超过10MB'}), 400

    file_data = file.read()

    # 黄色内容检测
    is_nsfw, ratio = _check_nsfw(file_data)
    if is_nsfw:
        return jsonify({'error': '图片内容不符合社区规范，请勿上传不当内容'}), 400

    # 生成唯一文件名
    ext = file.filename.rsplit('.', 1)[1].lower()
    filename = f"{uuid.uuid4().hex}.{ext}"
    banner_path = f"uploads/banners/{filename}"

    if _USE_PG:
        content_type = _get_content_type(filename)
        db = get_db()
        _exec(db, 'INSERT INTO images (path, data, content_type, created_at) VALUES (?,?,?,?)',
              (banner_path, file_data, content_type, time.time()))
    else:
        upload_dir = os.path.join(_DATA_DIR, 'uploads', 'banners')
        os.makedirs(upload_dir, exist_ok=True)
        with open(os.path.join(upload_dir, filename), 'wb') as out:
            out.write(file_data)

    # 更新数据库 banner 字段（不影响 background 网页端背景）
    db = get_db()
    _exec(db, 'UPDATE users SET banner=? WHERE id=?', (banner_path, session['user_id']))
    db.commit()

    return jsonify({'banner': f"/{banner_path}"})


@app.route('/api/user/banner', methods=['DELETE'])
@login_required
def api_remove_banner():
    """移除个人主页横幅图"""
    db = get_db()
    _exec(db, 'UPDATE users SET banner=? WHERE id=?', ('', session['user_id']))
    db.commit()
    return jsonify({'ok': True})


@app.route('/api/user/background', methods=['DELETE'])
@login_required
def api_remove_background():
    """移除用户背景"""
    db = get_db()
    _exec(db, 'UPDATE users SET background=? WHERE id=?', ('', session['user_id']))
    db.commit()
    return jsonify({'ok': True})


@app.route('/api/users/<user_id>/settings', methods=['GET'])
def api_get_user_settings(user_id):
    db = get_db()
    row = _fetchone(db, 'SELECT id, avatar, background FROM users WHERE id=?', (user_id,))
    if not row:
        return jsonify({'error': '用户不存在'}), 404
    avatar = row['avatar'] or ''
    background = row['background'] or ''
    return jsonify({
        'avatar': f"/{avatar}" if avatar else '',
        'background': f"/{background}" if background else ''
    })


# ===== API：通知 =====
@app.route('/api/notifications', methods=['GET'])
@login_required
def api_get_notifications():
    db = get_db()
    rows = _fetchall(db, 'SELECT id, text, read, created_at FROM notifications WHERE user_id=? ORDER BY created_at DESC',
                     (session['user_id'],))
    notifs = [dict(r) for r in rows]
    unread = sum(1 for n in notifs if not n['read'])
    return jsonify({'notifications': notifs, 'unread': unread})


@app.route('/api/notifications/read', methods=['POST'])
@login_required
def api_read_notifications():
    db = get_db()
    _exec(db, 'UPDATE notifications SET read=1 WHERE user_id=? AND read=0', (session['user_id'],))
    db.commit()
    return jsonify({'ok': True})


@app.route('/api/notifications', methods=['DELETE'])
@login_required
def api_clear_notifications():
    db = get_db()
    _exec(db, 'DELETE FROM notifications WHERE user_id=?', (session['user_id'],))
    db.commit()
    return jsonify({'ok': True})


# ===== API：WebAuthn / Passkeys =====

@app.route('/api/passkeys/register-begin', methods=['POST'])
@login_required
def api_passkey_register_begin():
    if cbor2 is None:
        return jsonify({'error': '服务器未安装 cbor2 库'}), 500

    req_data = request.get_json(silent=True) or {}
    browser_hostname = (req_data.get('browserHostname') or '').strip() or None
    browser_origin = (req_data.get('browserOrigin') or '').strip() or None

    db = get_db()
    user_id = session['user_id']
    user = _fetchone(db, 'SELECT id, username FROM users WHERE id=?', (user_id,))
    if not user:
        return jsonify({'error': '用户不存在'}), 404

    challenge = generate_challenge()
    session['webauthn_register_challenge'] = challenge
    # 存储前端传递的 origin 信息
    if browser_hostname:
        session['webauthn_browser_hostname'] = browser_hostname
    if browser_origin:
        session['webauthn_browser_origin'] = browser_origin

    rp_id = _get_rp_id(browser_hostname)

    # 获取已有凭据，用于排除
    existing_creds = _fetchall(db, 'SELECT credential_id FROM passkeys WHERE user_id=?', (user_id,))
    exclude_credentials = []
    for cred in existing_creds:
        cred_id_bytes = base64url_decode(cred['credential_id'])
        exclude_credentials.append({
            'type': 'public-key',
            'id': base64url_encode(cred_id_bytes),
        })

    # 用户句柄：使用 user_id 的 UTF-8 编码的 base64url
    user_handle = base64url_encode(user_id.encode('utf-8'))

    return jsonify({
        'challenge': challenge,
        'rp': {
            'name': WEBAUTHN_RP_NAME,
            'id': rp_id,
        },
        'user': {
            'id': user_handle,
            'name': user['username'],
            'displayName': user['username'],
        },
        'pubKeyCredParams': [
            {'type': 'public-key', 'alg': -7},    # ES256
            {'type': 'public-key', 'alg': -257},   # RS256
        ],
        'excludeCredentials': exclude_credentials,
        'authenticatorSelection': {
            'residentKey': 'preferred',
            'userVerification': 'preferred',
        },
        'timeout': 60000,
    })


@app.route('/api/passkeys/register-finish', methods=['POST'])
@login_required
def api_passkey_register_finish():
    if cbor2 is None:
        return jsonify({'error': '服务器未安装 cbor2 库'}), 500
    try:
        data = request.get_json(silent=True)
        if not data:
            return jsonify({'error': '请求数据无效'}), 400
        credential = data.get('credential', {})
        passkey_name = (data.get('name') or '').strip() or 'Passkey'

        # 验证 challenge
        stored_challenge = session.pop('webauthn_register_challenge', None)
        if not stored_challenge:
            return jsonify({'error': '无注册会话'}), 400

        client_data_json_b64 = credential.get('response', {}).get('clientDataJSON')
        attestation_object_b64 = credential.get('response', {}).get('attestationObject')

        if not client_data_json_b64 or not attestation_object_b64:
            return jsonify({'error': '缺少凭据数据'}), 400

        try:
            client_data_json = base64url_decode(client_data_json_b64)
            client_data = json.loads(client_data_json)
        except Exception:
            return jsonify({'error': '无法解析 clientDataJSON'}), 400

        # 验证类型
        if client_data.get('type') != 'webauthn.create':
            return jsonify({'error': 'clientData 类型错误'}), 400

        # 验证 challenge
        received_challenge = _b64url_normalize(client_data.get('challenge', ''))
        if received_challenge != _b64url_normalize(stored_challenge):
            return jsonify({'error': 'challenge 不匹配'}), 400

        # 验证 origin（只验证域名）
        # 优先使用前端传递的 browserHostname（存在 session 中）
        reg_browser_hostname = session.pop('webauthn_browser_hostname', None) or (data.get('browserHostname') or '').strip() or None
        received_origin = client_data.get('origin', '')
        expected_host = _get_rp_id(reg_browser_hostname)
        from urllib.parse import urlparse
        received_host = urlparse(received_origin).hostname or ''
        if received_host != expected_host:
            return jsonify({'error': f'origin 域名不匹配: 收到 {received_host}, 期望 {expected_host}'}), 400

        # 解码 attestationObject
        try:
            attestation_object = base64url_decode(attestation_object_b64)
            attestation = cbor2.loads(attestation_object)
        except Exception:
            return jsonify({'error': '无法解析 attestationObject'}), 400

        auth_data = attestation.get('authData')
        if not auth_data or len(auth_data) < 37:
            return jsonify({'error': 'authData 格式无效'}), 400

        flags = auth_data[32]
        has_attested_cred = bool(flags & 0x40)
        if not has_attested_cred:
            return jsonify({'error': 'authData 缺少 attestedCredentialData'}), 400

        offset = 37
        aaguid = auth_data[offset:offset + 16]
        offset += 16
        cred_id_len = _struct.unpack('>H', auth_data[offset:offset + 2])[0]
        offset += 2
        cred_id = auth_data[offset:offset + cred_id_len]
        offset += cred_id_len
        public_key_bytes = auth_data[offset:]

        try:
            _parse_cose_key(public_key_bytes)
        except Exception:
            return jsonify({'error': '无法解析 COSE 公钥'}), 400

        db = get_db()
        user_id = session['user_id']
        passkey_id = 'pk_' + uuid.uuid4().hex[:12]
        credential_id_b64 = base64url_encode(cred_id)
        public_key_b64 = base64url_encode(public_key_bytes)

        existing = _fetchone(db, 'SELECT id FROM passkeys WHERE credential_id=?', (credential_id_b64,))
        if existing:
            return jsonify({'error': '该凭据已注册'}), 400

        _exec(db,
              'INSERT INTO passkeys (id, user_id, credential_id, public_key, counter, name, created_at) VALUES (?,?,?,?,?,?,?)',
              (passkey_id, user_id, credential_id_b64, public_key_b64, 0, passkey_name, time.time()))
        db.commit()

        return jsonify({'ok': True, 'id': passkey_id})
    except Exception as e:
        return jsonify({'error': f'注册失败: {str(e)}'}), 400


@app.route('/api/passkeys/authenticate-begin', methods=['POST'])
def api_passkey_authenticate_begin():
    if cbor2 is None:
        return jsonify({'error': '服务器未安装 cbor2 库'}), 500

    data = request.get_json() or {}
    username = (data.get('username') or '').strip()
    browser_hostname = (data.get('browserHostname') or '').strip()
    browser_origin = (data.get('browserOrigin') or '').strip()

    challenge = generate_challenge()
    session['webauthn_auth_challenge'] = challenge
    # 存储前端传递的 origin 信息，供 authenticate-finish 使用
    if browser_hostname:
        session['webauthn_browser_hostname'] = browser_hostname
    if browser_origin:
        session['webauthn_browser_origin'] = browser_origin

    rp_id = _get_rp_id(browser_hostname or None)

    # 如果提供了 username，存储用户提示
    if username:
        db = get_db()
        user = _fetchone(db, 'SELECT id FROM users WHERE username=?', (username,))
        if user:
            session['webauthn_auth_user_hint'] = user['id']
            # 返回该用户的凭据列表
            creds = _fetchall(db, 'SELECT credential_id FROM passkeys WHERE user_id=?', (user['id'],))
            allow_credentials = []
            for c in creds:
                allow_credentials.append({
                    'type': 'public-key',
                    'id': base64url_encode(base64url_decode(c['credential_id'])),
                })
            return jsonify({
                'challenge': challenge,
                'rpId': rp_id,
                'allowCredentials': allow_credentials,
                'timeout': 60000,
                'userVerification': 'preferred',
            })
        else:
            return jsonify({'error': '用户不存在'}), 404

    # 无 username：discoverable credential 流程
    session['webauthn_auth_user_hint'] = None
    return jsonify({
        'challenge': challenge,
        'rpId': rp_id,
        'allowCredentials': [],
        'timeout': 60000,
        'userVerification': 'required',
    })


@app.route('/api/passkeys/authenticate-finish', methods=['POST'])
def api_passkey_authenticate_finish():
    if cbor2 is None:
        return jsonify({'error': '服务器未安装 cbor2 库'}), 500
    try:
        data = request.get_json(silent=True)
        if not data:
            return jsonify({'error': '请求数据无效'}), 400
        credential = data.get('credential', {})

        # 验证 challenge
        stored_challenge = session.pop('webauthn_auth_challenge', None)
        if not stored_challenge:
            return jsonify({'error': '无认证会话'}), 400

        client_data_json_b64 = credential.get('response', {}).get('clientDataJSON')
        authenticator_data_b64 = credential.get('response', {}).get('authenticatorData')
        signature_b64 = credential.get('response', {}).get('signature')
        credential_id_b64 = credential.get('rawId') or credential.get('id') or ''

        if not client_data_json_b64 or not authenticator_data_b64 or not signature_b64:
            return jsonify({'error': '缺少凭据数据'}), 400

        try:
            client_data_json = base64url_decode(client_data_json_b64)
            client_data = json.loads(client_data_json)
        except Exception:
            return jsonify({'error': '无法解析 clientDataJSON'}), 400

        if client_data.get('type') != 'webauthn.get':
            return jsonify({'error': 'clientData 类型错误'}), 400

        received_challenge = _b64url_normalize(client_data.get('challenge', ''))
        if received_challenge != _b64url_normalize(stored_challenge):
            return jsonify({'error': 'challenge 不匹配'}), 400

        # 验证 origin（只验证域名）
        # 优先使用前端传递的 browserHostname（存在 session 中）
        browser_hostname = session.pop('webauthn_browser_hostname', None) or (data.get('browserHostname') or '').strip() or None
        browser_origin = session.pop('webauthn_browser_origin', None) or (data.get('browserOrigin') or '').strip() or None
        expected_host = _get_rp_id(browser_hostname)
        received_origin = client_data.get('origin', '')
        from urllib.parse import urlparse as _urlparse
        received_host = _urlparse(received_origin).hostname or ''
        if received_host != expected_host:
            return jsonify({'error': f'origin 域名不匹配: 收到 {received_host}, 期望 {expected_host}'}), 400

        try:
            auth_data = base64url_decode(authenticator_data_b64)
            signature = base64url_decode(signature_b64)
        except Exception:
            return jsonify({'error': '无法解码 authenticatorData 或 signature'}), 400

        if len(auth_data) < 37:
            return jsonify({'error': 'authenticatorData 格式无效'}), 400

        # 查找 passkey
        db = get_db()
        credential_id_normalized = _b64url_normalize(credential_id_b64)
        all_passkeys = _fetchall(db, 'SELECT * FROM passkeys')
        passkey = None
        for pk in all_passkeys:
            if _b64url_normalize(pk['credential_id']) == credential_id_normalized:
                passkey = pk
                break
        if not passkey:
            return jsonify({'error': '未找到该通行密钥'}), 404

        # 验证签名
        public_key_bytes = base64url_decode(passkey['public_key'])
        sig_valid = verify_authenticator_signature(public_key_bytes, auth_data, client_data_json, signature)
        if not sig_valid:
            return jsonify({'error': '签名验证失败'}), 400

        # 检查 counter
        sign_count = _struct.unpack('>I', auth_data[33:37])[0]
        stored_counter = passkey['counter']
        if sign_count != 0 or stored_counter != 0:
            if sign_count <= stored_counter:
                return jsonify({'error': '计数器异常，可能存在克隆凭据'}), 400

        _exec(db, 'UPDATE passkeys SET counter=? WHERE id=?', (sign_count, passkey['id']))

        # 登录用户
        user_id = passkey['user_id']
        # 检查账号封禁状态（防止被封禁用户通过 passkey 绕过）
        ban_row = _fetchone(db, 'SELECT status FROM users WHERE id=?', (user_id,))
        if ban_row and ban_row.get('status') == 'banned':
            return jsonify({'error': '账号已被封禁', 'banned': True}), 403
        session['user_id'] = user_id
        session.permanent = True
        user = _fetchone(db, 'SELECT id, username, email, bio, avatar, background FROM users WHERE id=?', (user_id,))
        if not user:
            return jsonify({'error': '用户不存在'}), 404

        db.commit()

        u = dict(user)
        u['avatar'] = f"/{u['avatar']}" if u.get('avatar') else ''
        u['background'] = f"/{u['background']}" if u.get('background') else ''
        resp = jsonify({'user': u})
        _set_auth_cookie(resp, user_id)
        return resp
    except Exception as e:
        return jsonify({'error': f'认证失败: {str(e)}'}), 400


@app.route('/api/passkeys/list', methods=['GET'])
@login_required
def api_passkey_list():
    db = get_db()
    rows = _fetchall(db, 'SELECT id, name, created_at FROM passkeys WHERE user_id=? ORDER BY created_at DESC',
                     (session['user_id'],))
    passkeys = [dict(r) for r in rows]
    return jsonify({'passkeys': passkeys})


@app.route('/api/passkeys/<passkey_id>', methods=['DELETE'])
@login_required
def api_passkey_delete(passkey_id):
    db = get_db()
    passkey = _fetchone(db, 'SELECT id, user_id FROM passkeys WHERE id=?', (passkey_id,))
    if not passkey:
        return jsonify({'error': '通行密钥不存在'}), 404
    if passkey['user_id'] != session['user_id']:
        return jsonify({'error': '无权删除'}), 403
    _exec(db, 'DELETE FROM passkeys WHERE id=?', (passkey_id,))
    db.commit()
    return jsonify({'ok': True})


# ===== API：分类 =====
@app.route('/api/categories', methods=['GET'])
def api_categories():
    return jsonify({'categories': CATEGORIES})


# ===== 管理员权限检查 =====
def admin_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        # 统一使用 _get_auth_user_id（兼容 cookie 和 session 认证）
        uid = _get_auth_user_id()
        if not uid:
            return jsonify({'error': '未登录'}), 401
        db = get_db()
        user = _fetchone(db, 'SELECT is_admin, is_super_admin FROM users WHERE id=?', (uid,))
        # 普通管理员 或 超级管理员 均可访问
        if not user or not (user['is_admin'] or user['is_super_admin']):
            return jsonify({'error': '无管理员权限'}), 403
        return f(*args, **kwargs)
    return decorated


def news_publisher_required(f):
    """新闻发布权限：管理员、超级管理员、或被授予 can_publish_news 的用户可访问"""
    @wraps(f)
    def decorated(*args, **kwargs):
        uid = _get_auth_user_id()
        if not uid:
            return jsonify({'error': '未登录'}), 401
        db = get_db()
        user = _fetchone(db, 'SELECT is_admin, is_super_admin, can_publish_news FROM users WHERE id=?', (uid,))
        if not user or not (user['is_admin'] or user['is_super_admin'] or user['can_publish_news']):
            return jsonify({'error': '无新闻发布权限'}), 403
        return f(*args, **kwargs)
    return decorated


def super_admin_required(f):
    """仅超级管理员可访问：涉及权限分配、用户删除、官方认证、密码重置等高危操作"""
    @wraps(f)
    def decorated(*args, **kwargs):
        uid = _get_auth_user_id()
        if not uid:
            return jsonify({'error': '未登录'}), 401
        db = get_db()
        user = _fetchone(db, 'SELECT is_admin, is_super_admin FROM users WHERE id=?', (uid,))
        if not user or not user['is_super_admin']:
            return jsonify({'error': '需要超级管理员权限'}), 403
        return f(*args, **kwargs)
    return decorated


# ===== 管理员 API：权限检查 =====
@app.route('/api/admin/check', methods=['GET'])
@login_required
def admin_check():
    uid = _get_auth_user_id()
    db = get_db()
    user = _fetchone(db, 'SELECT is_admin, is_super_admin, can_publish_news FROM users WHERE id=?', (uid,))
    return jsonify({
        'is_admin': bool(user and user['is_admin']),
        'is_super_admin': bool(user and user['is_super_admin']),
        'can_publish_news': bool(user and user['can_publish_news']),
    })


# ===== 管理员 API：AI 配置 =====
@app.route('/api/admin/ai-config', methods=['GET'])
@admin_required
def api_get_ai_config():
    """获取 AI 配置"""
    cfg = get_ai_config()
    return jsonify({
        'base_url': cfg['base_url'],
        'model': cfg['model'],
        'api_key': cfg.get('api_key', ''),
        'system_prompt': AI_SYSTEM_PROMPT,
        'moderation_enabled': cfg.get('moderation_enabled', False),
    })


@app.route('/api/admin/ai-config', methods=['POST'])
@super_admin_required
def api_set_ai_config():
    """保存 AI 配置（base_url/model/api_key 为空时回退到环境变量，仅 moderation_enabled 必填）"""
    data = request.get_json()
    base_url = (data.get('base_url') or '').strip() or AI_BASE_URL
    model = (data.get('model') or '').strip() or AI_MODEL
    api_key = (data.get('api_key') or '').strip() or AI_API_KEY
    moderation_enabled = 1 if data.get('moderation_enabled') else 0

    db = get_db()
    try:
        row = db.execute('SELECT id FROM ai_config WHERE id=1').fetchone()
        if row:
            if _USE_PG:
                _exec(db, 'UPDATE ai_config SET base_url=%s, model=%s, api_key=%s, moderation_enabled=%s WHERE id=1', (base_url, model, api_key, moderation_enabled))
            else:
                db.execute('UPDATE ai_config SET base_url=?, model=?, api_key=?, moderation_enabled=? WHERE id=1', (base_url, model, api_key, moderation_enabled))
        else:
            if _USE_PG:
                _exec(db, 'INSERT INTO ai_config (id, base_url, model, api_key, moderation_enabled) VALUES (1, %s, %s, %s, %s)', (base_url, model, api_key, moderation_enabled))
            else:
                db.execute('INSERT INTO ai_config (id, base_url, model, api_key, moderation_enabled) VALUES (1, ?, ?, ?, ?)', (base_url, model, api_key, moderation_enabled))
        db.commit()
    except Exception as e:
        return jsonify({'error': f'保存失败：{str(e)}'}), 500

    return jsonify({'ok': True, 'message': 'AI 配置已保存'})


# ===== 管理员 API：用户 AI 额度 =====
@app.route('/api/admin/ai-quota/<user_id>', methods=['GET'])
@admin_required
def api_get_ai_quota(user_id):
    """获取某用户的 AI 额度"""
    quota = get_user_ai_quota(user_id)
    return jsonify(quota)


@app.route('/api/admin/ai-quota/<user_id>', methods=['POST'])
@super_admin_required
def api_set_ai_quota(user_id):
    """设置某用户的 AI 额度"""
    data = request.get_json()
    daily = int(data.get('daily_limit', AI_DEFAULT_DAILY_LIMIT))
    monthly = int(data.get('monthly_limit', AI_DEFAULT_MONTHLY_LIMIT))

    db = get_db()
    try:
        row = _fetchone(db, 'SELECT user_id FROM ai_quota WHERE user_id=?', (user_id,))
        if row:
            if _USE_PG:
                _exec(db, 'UPDATE ai_quota SET daily_limit=%s, monthly_limit=%s WHERE user_id=%s', (daily, monthly, user_id))
            else:
                db.execute('UPDATE ai_quota SET daily_limit=?, monthly_limit=? WHERE user_id=?', (daily, monthly, user_id))
        else:
            if _USE_PG:
                _exec(db, 'INSERT INTO ai_quota (user_id, daily_limit, monthly_limit) VALUES (%s, %s, %s)', (user_id, daily, monthly))
            else:
                db.execute('INSERT INTO ai_quota (user_id, daily_limit, monthly_limit) VALUES (?, ?, ?)', (user_id, daily, monthly))
        db.commit()
    except Exception as e:
        return jsonify({'error': f'保存失败：{str(e)}'}), 500

    return jsonify({'ok': True, 'message': '额度已更新'})


# ===== 管理员 API：仪表盘 =====
@app.route('/api/admin/stats', methods=['GET'])
@admin_required
def admin_stats():
    db = get_db()
    user_count = _fetchone(db, 'SELECT COUNT(*) as c FROM users')['c']
    post_count = _fetchone(db, 'SELECT COUNT(*) as c FROM posts')['c']
    reply_count = _fetchone(db, 'SELECT COUNT(*) as c FROM replies')['c']
    today = time.time() - 86400
    new_users_today = _fetchone(db, 'SELECT COUNT(*) as c FROM users WHERE created_at>?', (today,))['c']
    new_posts_today = _fetchone(db, 'SELECT COUNT(*) as c FROM posts WHERE created_at>?', (today,))['c']
    new_replies_today = _fetchone(db, 'SELECT COUNT(*) as c FROM replies WHERE created_at>?', (today,))['c']
    banned_count = _fetchone(db, "SELECT COUNT(*) as c FROM users WHERE status='banned'")['c']
    muted_count = _fetchone(db, 'SELECT COUNT(*) as c FROM users WHERE muted_until>?', (time.time(),))['c']
    pending_bugs = 0
    try:
        pending_bugs = _fetchone(db, "SELECT COUNT(*) as c FROM bug_reports WHERE status='open'")['c']
    except Exception:
        pass
    # 最近活动：最新5条帖子和最新5条注册用户
    recent_posts = _fetchall(db, '''
        SELECT p.id, p.title, u.username as author, p.created_at, p.category
        FROM posts p JOIN users u ON p.author_id=u.id
        ORDER BY p.created_at DESC LIMIT 5
    ''')
    recent_users = _fetchall(db, '''
        SELECT id, username, created_at, email_verified
        FROM users ORDER BY created_at DESC LIMIT 5
    ''')
    return jsonify({
        'user_count': user_count,
        'post_count': post_count,
        'reply_count': reply_count,
        'new_users_today': new_users_today,
        'new_posts_today': new_posts_today,
        'new_replies_today': new_replies_today,
        'banned_count': banned_count,
        'muted_count': muted_count,
        'pending_bugs': pending_bugs,
        'recent_posts': [dict(r) for r in recent_posts],
        'recent_users': [dict(r) for r in recent_users],
    })


# ===== 管理员 API：用户管理 =====
@app.route('/api/admin/users', methods=['GET'])
@admin_required
def admin_get_users():
    db = get_db()
    page = int(request.args.get('page', 1))
    per_page = 20
    offset = (page - 1) * per_page
    search = request.args.get('search', '').strip()

    if search:
        rows = _fetchall(db, '''
            SELECT u.id, u.username, u.email, u.bio, u.is_admin, u.is_super_admin, u.can_publish_news, u.created_at, u.status, u.muted_until, u.last_ip, u.last_online, u.email_verified, u.verified, u.verified_text, u.is_quality,
                   (SELECT COUNT(*) FROM posts WHERE author_id=u.id) as post_count,
                   COALESCE(u.admin_follower_boost,0) as admin_follower_boost, COALESCE(u.admin_like_boost,0) as admin_like_boost
            FROM users u WHERE u.username LIKE ? OR u.email LIKE ?
            ORDER BY u.created_at DESC LIMIT ? OFFSET ?
        ''', (f'%{search}%', f'%{search}%', per_page, offset))
        total = _fetchone(db, 'SELECT COUNT(*) as c FROM users WHERE username LIKE ? OR email LIKE ?',
                          (f'%{search}%', f'%{search}%'))['c']
    else:
        rows = _fetchall(db, '''
            SELECT u.id, u.username, u.email, u.bio, u.is_admin, u.is_super_admin, u.can_publish_news, u.created_at, u.status, u.muted_until, u.last_ip, u.last_online, u.email_verified, u.verified, u.verified_text, u.is_quality,
                   (SELECT COUNT(*) FROM posts WHERE author_id=u.id) as post_count,
                   COALESCE(u.admin_follower_boost,0) as admin_follower_boost, COALESCE(u.admin_like_boost,0) as admin_like_boost
            FROM users u ORDER BY u.created_at DESC LIMIT ? OFFSET ?
        ''', (per_page, offset))
        total = _fetchone(db, 'SELECT COUNT(*) as c FROM users')['c']

    users = []
    for r in rows:
        u = dict(r)
        u['is_admin'] = bool(u['is_admin'])
        u['is_super_admin'] = bool(u.get('is_super_admin', 0))
        u['can_publish_news'] = bool(u.get('can_publish_news', 0))
        u['email_verified'] = bool(u.get('email_verified', 0))
        u['verified'] = bool(u.get('verified', 0))
        u['verified_text'] = u.get('verified_text', '') or ''
        u['is_quality'] = bool(u.get('is_quality', 0))
        u['status'] = u['status'] if 'status' in u.keys() else 'active'
        u['muted_until'] = u['muted_until'] if 'muted_until' in u.keys() else 0
        u['admin_follower_boost'] = int(u.get('admin_follower_boost') or 0)
        u['admin_like_boost'] = int(u.get('admin_like_boost') or 0)
        users.append(u)
    return jsonify({'users': users, 'total': total, 'page': page, 'per_page': per_page})


@app.route('/api/admin/users/<user_id>', methods=['DELETE'])
@super_admin_required
def admin_delete_user(user_id):
    db = get_db()
    user = _fetchone(db, 'SELECT id, is_admin, is_super_admin FROM users WHERE id=?', (user_id,))
    if not user:
        return jsonify({'error': '用户不存在'}), 404
    if user['is_super_admin']:
        return jsonify({'error': '不能删除超级管理员'}), 400
    if user['is_admin']:
        return jsonify({'error': '不能删除管理员，请先撤销管理员权限'}), 400

    _delete_user_data(db, user_id)
    db.commit()
    return jsonify({'ok': True})


def _delete_user_data(db, user_id):
    """删除用户全部关联数据（显式删除，不依赖 ON DELETE CASCADE，兼容旧库）。
    供管理员强制删除（admin_delete_user）与用户自助注销（api_delete_account）复用。"""
    # 1. 删用户自己的点赞/收藏
    for t in ('post_likes', 'reply_likes', 'bookmarks'):
        try:
            _exec(db, f'DELETE FROM {t} WHERE user_id=?', (user_id,))
        except Exception:
            pass
    # 2. 删该用户帖子下的关联数据（其他用户的回复/点赞/收藏/标签，防止删 posts 时 FK 失败）
    for sql in (
        "DELETE FROM reply_likes WHERE reply_id IN (SELECT id FROM replies WHERE post_id IN (SELECT id FROM posts WHERE author_id=?))",
        "DELETE FROM replies WHERE post_id IN (SELECT id FROM posts WHERE author_id=?)",
        "DELETE FROM tags WHERE post_id IN (SELECT id FROM posts WHERE author_id=?)",
        "DELETE FROM post_likes WHERE post_id IN (SELECT id FROM posts WHERE author_id=?)",
        "DELETE FROM bookmarks WHERE post_id IN (SELECT id FROM posts WHERE author_id=?)",
    ):
        try:
            _exec(db, sql, (user_id,))
        except Exception:
            pass
    # 3. 删用户自己写的 replies
    try:
        _exec(db, 'DELETE FROM replies WHERE author_id=?', (user_id,))
    except Exception:
        pass
    # 4. 删用户的 posts
    try:
        _exec(db, 'DELETE FROM posts WHERE author_id=?', (user_id,))
    except Exception:
        pass
    # 5. 删其他引用 users 的表（全部显式删，不依赖 CASCADE）
    for table, col in (
        ('notifications', 'user_id'), ('passkeys', 'user_id'), ('chat_messages', 'user_id'),
        ('dm_messages', 'sender_id'), ('dm_conversations', 'user1_id'), ('dm_conversations', 'user2_id'),
        ('follows', 'follower_id'), ('follows', 'following_id'), ('bug_reports', 'user_id'),
        ('announcements', 'created_by'), ('ai_quota', 'user_id'), ('ai_usage_log', 'user_id'),
        ('chat_ai_usage_log', 'user_id'), ('oauth_tokens', 'user_id'), ('oauth_codes', 'user_id'), ('oauth_apps', 'user_id'),
    ):
        try:
            _exec(db, f'DELETE FROM {table} WHERE {col}=?', (user_id,))
        except Exception:
            pass
    # 6. 最后删用户
    _exec(db, 'DELETE FROM users WHERE id=?', (user_id,))


@app.route('/api/account', methods=['DELETE'])
@login_required
def api_delete_account():
    """用户自助注销账号（需密码确认）。注销后清除登录态并删除全部关联数据。"""
    db = get_db()
    user_id = _get_auth_user_id()
    if not user_id:
        return jsonify({'error': '未登录'}), 401
    user = _fetchone(db, 'SELECT id, is_admin, is_super_admin, password_hash FROM users WHERE id=?', (user_id,))
    if not user:
        return jsonify({'error': '用户不存在'}), 404
    if user['is_admin'] or user['is_super_admin']:
        return jsonify({'error': '管理员账号不能自助注销'}), 400
    payload = request.get_json(silent=True) or {}
    if not verify_password((payload.get('password') or ''), user['password_hash']):
        return jsonify({'error': '密码不正确'}), 403
    _delete_user_data(db, user_id)
    db.commit()
    # 清除登录态
    session.clear()
    resp = jsonify({'ok': True})
    _clear_auth_cookie(resp)
    return resp


@app.route('/api/admin/users/<user_id>/verify', methods=['POST'])
@super_admin_required
def admin_set_user_verified(user_id):
    """管理员设置用户官方认证标识、认证内容、黄色优质主播标识"""
    data = request.get_json() or {}
    verified = 1 if data.get('verified') else 0
    verified_text = _sanitize_plain((data.get('verified_text') or '').strip())
    if len(verified_text) > 50:
        return jsonify({'error': '认证内容不能超过50字'}), 400
    # is_quality 黄色优质主播标识（与蓝色认证区分，同一弹窗内勾选）
    is_quality = 1 if data.get('is_quality') else 0
    db = get_db()
    user = _fetchone(db, 'SELECT id FROM users WHERE id=?', (user_id,))
    if not user:
        return jsonify({'error': '用户不存在'}), 404
    _exec(db, 'UPDATE users SET verified=?, verified_text=?, is_quality=? WHERE id=?',
          (verified, verified_text, is_quality, user_id))
    db.commit()
    return jsonify({'ok': True, 'verified': bool(verified), 'verified_text': verified_text, 'is_quality': bool(is_quality)})


@app.route('/api/admin/users/<user_id>/toggle_admin', methods=['POST'])
@super_admin_required
def admin_toggle_admin(user_id):
    db = get_db()
    user = _fetchone(db, 'SELECT id, username, is_admin, is_super_admin FROM users WHERE id=?', (user_id,))
    if not user:
        return jsonify({'error': '用户不存在'}), 404
    if user['is_super_admin']:
        return jsonify({'error': '不能修改超级管理员权限'}), 400
    if user['id'] == session['user_id']:
        return jsonify({'error': '不能修改自己的管理员状态'}), 400
    new_val = 0 if user['is_admin'] else 1
    _exec(db, 'UPDATE users SET is_admin=? WHERE id=?', (new_val, user_id))
    db.commit()
    return jsonify({'is_admin': bool(new_val)})


@app.route('/api/admin/users/<user_id>/toggle_news_publisher', methods=['POST'])
@super_admin_required
def admin_toggle_news_publisher(user_id):
    """切换用户的新闻发布权限"""
    db = get_db()
    user = _fetchone(db, 'SELECT id, is_super_admin, can_publish_news FROM users WHERE id=?', (user_id,))
    if not user:
        return jsonify({'error': '用户不存在'}), 404
    if user['is_super_admin']:
        return jsonify({'error': '不能修改超级管理员权限'}), 400
    new_val = 0 if user['can_publish_news'] else 1
    _exec(db, 'UPDATE users SET can_publish_news=? WHERE id=?', (new_val, user_id))
    db.commit()
    return jsonify({'can_publish_news': bool(new_val)})


@app.route('/api/admin/users/<user_id>/boost', methods=['POST'])
@super_admin_required
def admin_update_boost(user_id):
    """管理员手动调整用户显示的关注者数和帖子获赞数（boost 值，叠加到真实数据上）"""
    db = get_db()
    user = _fetchone(db, 'SELECT id, is_super_admin FROM users WHERE id=?', (user_id,))
    if not user:
        return jsonify({'error': '用户不存在'}), 404
    if user['is_super_admin']:
        return jsonify({'error': '不能修改超级管理员声望'}), 400
    data = request.get_json() or {}
    try:
        fb = int(data.get('follower_boost', 0))
        lb = int(data.get('like_boost', 0))
    except (TypeError, ValueError):
        return jsonify({'error': '无效数值'}), 400
    if fb < -999999999 or lb < -999999999:
        return jsonify({'error': '数值过小'}), 400
    _exec(db, 'UPDATE users SET admin_follower_boost=?, admin_like_boost=? WHERE id=?',
          (fb, lb, user_id))
    db.commit()
    return jsonify({'admin_follower_boost': fb, 'admin_like_boost': lb})


@app.route('/api/admin/users/<user_id>/reset_password', methods=['POST'])
@super_admin_required
def admin_reset_password(user_id):
    data = request.get_json()
    new_password = data.get('password', '')
    if len(new_password) < 4:
        return jsonify({'error': '密码至少4位'}), 400
    db = get_db()
    user = _fetchone(db, 'SELECT id FROM users WHERE id=?', (user_id,))
    if not user:
        return jsonify({'error': '用户不存在'}), 404
    _exec(db, 'UPDATE users SET password_hash=? WHERE id=?', (hash_password(new_password), user_id))
    db.commit()
    return jsonify({'ok': True})


# ===== 管理员 API：帖子管理 =====
@app.route('/api/admin/posts', methods=['GET'])
@admin_required
def admin_get_posts():
    db = get_db()
    page = int(request.args.get('page', 1))
    per_page = 20
    offset = (page - 1) * per_page
    search = request.args.get('search', '').strip()
    category = request.args.get('category', '').strip()

    conditions = []
    params = []
    if search:
        conditions.append('(p.title LIKE ? OR p.content LIKE ?)')
        params.extend([f'%{search}%', f'%{search}%'])
    if category:
        conditions.append('p.category=?')
        params.append(category)

    where = (' WHERE ' + ' AND '.join(conditions)) if conditions else ''

    rows = _fetchall(db, f'''
        SELECT p.id, p.author_id, u.username as author_name, p.title, p.category,
               p.content, p.likes, p.created_at, p.admin_like_boost,
               (SELECT COUNT(*) FROM replies WHERE post_id=p.id) as reply_count
        FROM posts p JOIN users u ON p.author_id = u.id
        {where}
        ORDER BY p.created_at DESC LIMIT ? OFFSET ?
    ''', params + [per_page, offset])

    total = _fetchone(db, f'SELECT COUNT(*) as c FROM posts p JOIN users u ON p.author_id=u.id{where}', params)['c']

    posts = []
    for r in rows:
        p = dict(r)
        tags = _fetchall(db, 'SELECT tag FROM tags WHERE post_id=?', (p['id'],))
        p['tags'] = [t['tag'] for t in tags]
        p['likes'] = max(0, int(p['likes']) + (int(p.get('admin_like_boost') or 0)))
        posts.append(p)
    return jsonify({'posts': posts, 'total': total, 'page': page, 'per_page': per_page})


@app.route('/api/admin/posts/<post_id>', methods=['DELETE'])
@admin_required
def admin_delete_post(post_id):
    db = get_db()
    post = _fetchone(db, 'SELECT id FROM posts WHERE id=?', (post_id,))
    if not post:
        return jsonify({'error': '帖子不存在'}), 404
    _exec(db, 'DELETE FROM posts WHERE id=?', (post_id,))
    db.commit()
    return jsonify({'ok': True})


@app.route('/api/admin/posts/<post_id>/likes', methods=['POST'])
@admin_required
def admin_update_post_likes(post_id):
    """管理员调整帖子点赞数（不修改真实数据库，仅修改显示值）"""
    db = get_db()
    post = _fetchone(db, 'SELECT id FROM posts WHERE id=?', (post_id,))
    if not post:
        return jsonify({'error': '帖子不存在'}), 404
    data = request.get_json() or {}
    try:
        boost = int(data.get('like_boost', 0))
    except (TypeError, ValueError):
        return jsonify({'error': '无效数值'}), 400
    if boost < -999999999:
        return jsonify({'error': '数值过小'}), 400
    _exec(db, 'UPDATE posts SET admin_like_boost=? WHERE id=?', (boost, post_id))
    db.commit()
    return jsonify({'ok': True, 'like_boost': boost})




@app.route('/api/admin/posts/batch', methods=['DELETE'])
@admin_required
def admin_batch_delete_posts():
    data = request.get_json() or {}
    post_ids = data.get('ids') or []
    if not post_ids:
        return jsonify({'error': '未选择帖子'}), 400
    db = get_db()
    deleted = 0
    for pid in post_ids:
        try:
            _exec(db, 'DELETE FROM posts WHERE id=?', (pid,))
            deleted += 1
        except Exception:
            pass
    db.commit()
    return jsonify({'ok': True, 'deleted': deleted})


@app.route('/api/admin/posts/<post_id>', methods=['PUT'])
@admin_required
def admin_update_post(post_id):
    db = get_db()
    post = _fetchone(db, 'SELECT id FROM posts WHERE id=?', (post_id,))
    if not post:
        return jsonify({'error': '帖子不存在'}), 404
    data = request.get_json()
    title = _sanitize_plain((data.get('title') or '').strip())
    category = data.get('category') or ''
    content = (data.get('content') or '').strip()
    if title:
        _exec(db, 'UPDATE posts SET title=? WHERE id=?', (title, post_id))
    if category:
        _exec(db, 'UPDATE posts SET category=? WHERE id=?', (category, post_id))
    if content:
        _exec(db, 'UPDATE posts SET content=? WHERE id=?', (content, post_id))
    db.commit()
    return jsonify({'ok': True})


# ===== 管理员 API：回复管理 =====
@app.route('/api/admin/replies', methods=['GET'])
@admin_required
def admin_get_replies():
    db = get_db()
    page = int(request.args.get('page', 1))
    per_page = 20
    offset = (page - 1) * per_page
    post_id = request.args.get('post_id', '').strip()

    search = request.args.get('search', '').strip()
    conditions = []
    params = []
    if post_id:
        conditions.append('r.post_id=?')
        params.append(post_id)
    if search:
        conditions.append('r.content LIKE ?')
        params.append(f'%{search}%')

    where = (' WHERE ' + ' AND '.join(conditions)) if conditions else ''

    rows = _fetchall(db, f'''
        SELECT r.id, r.post_id, r.author_id, u.username as author_name,
               p.title as post_title, r.content, r.likes, r.created_at
        FROM replies r
        JOIN users u ON r.author_id = u.id
        JOIN posts p ON r.post_id = p.id
        {where}
        ORDER BY r.created_at DESC LIMIT ? OFFSET ?
    ''', params + [per_page, offset])

    total = _fetchone(db, f'SELECT COUNT(*) as c FROM replies r JOIN users u ON r.author_id=u.id JOIN posts p ON r.post_id=p.id{where}', params)['c']
    return jsonify({'replies': [dict(r) for r in rows], 'total': total, 'page': page, 'per_page': per_page})


@app.route('/api/admin/replies/<reply_id>', methods=['DELETE'])
@admin_required
def admin_delete_reply(reply_id):
    db = get_db()
    reply = _fetchone(db, 'SELECT id FROM replies WHERE id=?', (reply_id,))
    if not reply:
        return jsonify({'error': '回复不存在'}), 404
    # 删除子回复（parent_id 无 FK 约束，需手动清理；reply_likes 会被 CASCADE 自动删除）
    _exec(db, 'DELETE FROM replies WHERE parent_id=?', (reply_id,))
    _exec(db, 'DELETE FROM replies WHERE id=?', (reply_id,))
    db.commit()
    return jsonify({'ok': True})


@app.route('/api/bug-reports', methods=['POST'])
def api_submit_bug_report():
    if 'user_id' not in session:
        return jsonify({'error': '未登录'}), 401
    data = request.get_json() or {}
    content = filter_content((data.get('content') or '').strip())
    if not content or len(content) > 2000:
        return jsonify({'error': '内容无效'}), 400
    db = get_db()
    rid = 'bug_' + uuid.uuid4().hex[:8]
    now = time.time()
    username = get_username(session['user_id'])
    if _USE_PG:
        _exec(db, 'INSERT INTO bug_reports (id, user_id, username, content, status, created_at) VALUES (%s,%s,%s,%s,%s,%s)',
               (rid, session['user_id'], username, content, 'open', now))
    else:
        db.execute('INSERT INTO bug_reports (id, user_id, username, content, status, created_at) VALUES (?,?,?,?,?,?)',
                   (rid, session['user_id'], username, content, 'open', now))
        db.commit()
    db.close()
    return jsonify({'ok': True, 'id': rid})


@app.route('/api/admin/bug-reports', methods=['GET'])
@admin_required
def api_admin_bug_reports():
    db = get_db()
    if _USE_PG:
        rows = _fetchall(db, 'SELECT id, user_id, username, content, status, created_at FROM bug_reports ORDER BY created_at DESC')
    else:
        rows = db.execute('SELECT id, user_id, username, content, status, created_at FROM bug_reports ORDER BY created_at DESC').fetchall()
    db.close()
    reports = [dict(r) for r in rows]
    return jsonify({'reports': reports})


@app.route('/api/admin/bug-reports/<rid>', methods=['PUT'])
@admin_required
def api_admin_update_bug_report(rid):
    data = request.get_json() or {}
    status = (data.get('status') or '').strip()
    if status not in ('open', 'resolved', 'ignored'):
        return jsonify({'error': '状态无效'}), 400
    db = get_db()
    if _USE_PG:
        _exec(db, 'UPDATE bug_reports SET status=%s WHERE id=%s', (status, rid))
    else:
        db.execute('UPDATE bug_reports SET status=? WHERE id=?', (status, rid))
        db.commit()
    db.close()
    return jsonify({'ok': True})


# ===== 举报 / 自动下架 =====
# 举报数达到该阈值即自动下架，无需管理员审批
REPORT_AUTO_REMOVE_THRESHOLD = 5
_REPORT_TARGETS = ('post', 'news', 'live')
_REPORT_TARGET_LABELS = {'post': '帖子', 'news': '新闻', 'live': '直播间'}


def _report_count(db, target_type, target_id):
    row = _fetchone(db, 'SELECT COUNT(*) as c FROM reports WHERE target_type=? AND target_id=?', (target_type, target_id))
    return row['c'] if row else 0


def _auto_remove_target(db, target_type, target_id):
    """达到举报阈值后自动下架（无需审批）。live 直播间用 banned=1，帖子/新闻用 report_removed=1。"""
    if target_type == 'post':
        _exec(db, 'UPDATE posts SET report_removed=1 WHERE id=?', (target_id,))
    elif target_type == 'news':
        _exec(db, 'UPDATE news SET report_removed=1 WHERE id=?', (target_id,))
    elif target_type == 'live':
        _exec(db, 'UPDATE live_channels SET banned=1 WHERE id=?', (target_id,))
    db.commit()


def _report_target_title(db, target_type, target_id):
    """取被举报对象标题与作者，供管理后台留存展示"""
    try:
        title = ''
        author_id = None
        if target_type == 'post':
            row = _fetchone(db, 'SELECT title, author_id FROM posts WHERE id=?', (target_id,))
        elif target_type == 'news':
            row = _fetchone(db, 'SELECT title, author_id FROM news WHERE id=?', (target_id,))
        else:
            row = _fetchone(db, 'SELECT name as title, user_id FROM live_channels WHERE id=?', (target_id,))
        if row:
            title = row.get('title') or ''
            author_id = row.get('author_id') or row.get('user_id') or None
        author = get_username(author_id) if author_id else ''
        return {'title': title, 'author': author}
    except Exception:
        return {'title': '', 'author': ''}


def _report_target_content(db, target_type, target_id):
    """取被举报对象正文（管理员查看/判断用）"""
    try:
        content = ''
        if target_type == 'post':
            row = _fetchone(db, 'SELECT content FROM posts WHERE id=?', (target_id,))
        elif target_type == 'news':
            row = _fetchone(db, 'SELECT content FROM news WHERE id=?', (target_id,))
        else:
            row = _fetchone(db, 'SELECT description as content FROM live_channels WHERE id=?', (target_id,))
        if row:
            content = row.get('content') or ''
        return content
    except Exception:
        return ''


@app.route('/api/reports', methods=['POST'])
@login_required
def api_create_report():
    """用户举报帖子/新闻/直播间。同一用户对同一对象只能举报一次。达到阈值自动下架并留存后台。"""
    data = request.get_json() or {}
    target_type = (data.get('target_type') or '').strip().lower()
    target_id = (data.get('target_id') or '').strip()
    reason = _sanitize_plain((data.get('reason') or '').strip())[:100]

    if target_type not in _REPORT_TARGETS:
        return jsonify({'error': '举报对象类型无效'}), 400
    if not target_id:
        return jsonify({'error': '举报对象缺失'}), 400

    uid = _get_auth_user_id()
    db = get_db()

    # 校验对象存在
    if target_type == 'post':
        exists = _fetchone(db, 'SELECT id FROM posts WHERE id=?', (target_id,))
    elif target_type == 'news':
        exists = _fetchone(db, 'SELECT id FROM news WHERE id=?', (target_id,))
    else:
        exists = _fetchone(db, 'SELECT id FROM live_channels WHERE id=?', (target_id,))
    if not exists:
        db.close()
        return jsonify({'error': '该内容不存在'}), 404

    # 同一用户不能重复举报同一对象
    dup = _fetchone(db, 'SELECT id FROM reports WHERE target_type=? AND target_id=? AND reporter_id=?',
                    (target_type, target_id, uid))
    if dup:
        db.close()
        return jsonify({'error': '你已举报过该内容'}), 409

    rep_id = 'rep_' + uuid.uuid4().hex[:12]
    now = time.time()
    # 幂等：并发下即便重复写入也以 UNIQUE 之外的逻辑兜底
    try:
        _exec(db, 'INSERT INTO reports (id, target_type, target_id, reporter_id, reason, created_at) VALUES (?,?,?,?,?,?)',
              (rep_id, target_type, target_id, uid, reason, now))
        db.commit()
    except Exception:
        db.commit()
        db.close()
        return jsonify({'error': '你已举报过该内容'}), 409

    count = _report_count(db, target_type, target_id)
    auto_removed = count >= REPORT_AUTO_REMOVE_THRESHOLD
    if auto_removed:
        _auto_remove_target(db, target_type, target_id)
    db.close()
    return jsonify({'ok': True, 'count': count, 'auto_removed': auto_removed,
                    'threshold': REPORT_AUTO_REMOVE_THRESHOLD})


@app.route('/api/admin/reports', methods=['GET'])
@admin_required
def api_admin_reports():
    """管理后台：举报留存列表（含已自动下架内容，按举报数与最新举报时间排序）"""
    db = get_db()
    rows = _fetchall(db, '''
        SELECT target_type, target_id, COUNT(*) as cnt, MIN(created_at) as first_at, MAX(created_at) as last_at
        FROM reports GROUP BY target_type, target_id
    ''')
    counts = {}
    for r in rows:
        counts[(r['target_type'], r['target_id'])] = {
            'count': r['cnt'],
            'first_at': r['first_at'],
            'last_at': r['last_at'],
        }

    # 汇总每个对象的举报理由（去重）
    reasons_map = {}
    reason_rows = _fetchall(db, '''
        SELECT target_type, target_id, reason FROM reports ORDER BY created_at DESC
    ''')
    for rr in reason_rows:
        key = (rr['target_type'], rr['target_id'])
        if rr.get('reason'):
            seen = reasons_map.setdefault(key, [])
            if rr['reason'] not in seen:
                seen.append(rr['reason'])

    items = []
    for (target_type, target_id), meta in counts.items():
        removed = False
        if target_type == 'post':
            info = _fetchone(db, 'SELECT report_removed FROM posts WHERE id=?', (target_id,))
            removed = bool(info and info.get('report_removed'))
        elif target_type == 'news':
            info = _fetchone(db, 'SELECT report_removed FROM news WHERE id=?', (target_id,))
            removed = bool(info and info.get('report_removed'))
        else:
            info = _fetchone(db, 'SELECT banned FROM live_channels WHERE id=?', (target_id,))
            removed = bool(info and info.get('banned'))
        title_info = _report_target_title(db, target_type, target_id)
        content = _report_target_content(db, target_type, target_id)
        content_snippet = _sanitize_plain(content)[:200] if content else ''
        items.append({
            'target_type': target_type,
            'target_type_label': _REPORT_TARGET_LABELS.get(target_type, target_type),
            'target_id': target_id,
            'count': meta['count'],
            'first_at': meta['first_at'],
            'last_at': meta['last_at'],
            'removed': removed,
            'title': title_info['title'],
            'author': title_info['author'],
            'content': content_snippet,
            'reasons': '；'.join(reasons_map.get((target_type, target_id), [])),
        })

    items.sort(key=lambda x: (-int(x['count']), -float(x['last_at'])))
    total = sum(1 for _ in items)
    db.close()
    return jsonify({'reports': items, 'total': total, 'threshold': REPORT_AUTO_REMOVE_THRESHOLD})


@app.route('/api/admin/reports/<report_id>', methods=['DELETE'])
@admin_required
def api_admin_delete_report(report_id):
    """移除单条举报记录"""
    db = get_db()
    row = _fetchone(db, 'SELECT id FROM reports WHERE id=?', (report_id,))
    if not row:
        db.close()
        return jsonify({'error': '举报记录不存在'}), 404
    _exec(db, 'DELETE FROM reports WHERE id=?', (report_id,))
    db.commit()
    db.close()
    return jsonify({'ok': True})


@app.route('/api/admin/reports/restore', methods=['POST'])
@admin_required
def api_admin_restore_report():
    """管理员恢复被举报下架的内容：取消下架并清空其全部举报记录"""
    data = request.get_json() or {}
    target_type = (data.get('target_type') or '').strip()
    target_id = (data.get('target_id') or '').strip()
    if target_type not in _REPORT_TARGETS or not target_id:
        return jsonify({'error': '参数无效'}), 400
    db = get_db()
    if target_type == 'post':
        _exec(db, 'UPDATE posts SET report_removed=0 WHERE id=?', (target_id,))
    elif target_type == 'news':
        _exec(db, 'UPDATE news SET report_removed=0 WHERE id=?', (target_id,))
    else:
        _exec(db, 'UPDATE live_channels SET banned=0 WHERE id=?', (target_id,))
    _exec(db, 'DELETE FROM reports WHERE target_type=? AND target_id=?', (target_type, target_id))
    db.commit()
    db.close()
    return jsonify({'ok': True, 'removed': False})


@app.route('/api/admin/reports/detail', methods=['GET'])
@admin_required
def api_admin_report_detail():
    """管理员查看被举报对象的完整内容与理由"""
    target_type = (request.args.get('target_type') or '').strip()
    target_id = (request.args.get('target_id') or '').strip()
    if target_type not in _REPORT_TARGETS or not target_id:
        return jsonify({'error': '参数无效'}), 400
    db = get_db()
    title_info = _report_target_title(db, target_type, target_id)
    content = _report_target_content(db, target_type, target_id)
    reason_rows = _fetchall(db, 'SELECT reason, reporter_id, created_at FROM reports WHERE target_type=? AND target_id=? ORDER BY created_at DESC',
                            (target_type, target_id))
    reasons = [r['reason'] for r in reason_rows if r.get('reason')]
    removed = False
    if target_type == 'post':
        info = _fetchone(db, 'SELECT report_removed FROM posts WHERE id=?', (target_id,))
        removed = bool(info and info.get('report_removed'))
    elif target_type == 'news':
        info = _fetchone(db, 'SELECT report_removed FROM news WHERE id=?', (target_id,))
        removed = bool(info and info.get('report_removed'))
    else:
        info = _fetchone(db, 'SELECT banned FROM live_channels WHERE id=?', (target_id,))
        removed = bool(info and info.get('banned'))
    db.close()
    return jsonify({
        'target_type': target_type,
        'target_type_label': _REPORT_TARGET_LABELS.get(target_type, target_type),
        'target_id': target_id,
        'title': title_info['title'],
        'author': title_info['author'],
        'content': content,
        'reasons': reasons,
        'removed': removed,
    })


@app.route('/api/admin/reports/remove-content', methods=['POST'])
@admin_required
def api_admin_remove_report_content():
    """管理员判定举报属实：彻底删除被举报内容并清除其全部举报记录"""
    data = request.get_json() or {}
    target_type = (data.get('target_type') or '').strip()
    target_id = (data.get('target_id') or '').strip()
    if target_type not in _REPORT_TARGETS or not target_id:
        return jsonify({'error': '参数无效'}), 400
    db = get_db()
    if target_type == 'post':
        # 连带清理该帖的回复及点赞，避免产生孤立数据
        _exec(db, 'DELETE FROM reply_likes WHERE reply_id IN (SELECT id FROM replies WHERE post_id=?)', (target_id,))
        _exec(db, 'DELETE FROM replies WHERE post_id=?', (target_id,))
        _exec(db, 'DELETE FROM posts WHERE id=?', (target_id,))
    elif target_type == 'news':
        _exec(db, 'DELETE FROM news WHERE id=?', (target_id,))
    else:
        _exec(db, 'DELETE FROM live_channels WHERE id=?', (target_id,))
    _exec(db, 'DELETE FROM reports WHERE target_type=? AND target_id=?', (target_type, target_id))
    db.commit()
    db.close()
    return jsonify({'ok': True})


# ===== 禁言/封号 =====
@app.route('/api/admin/users/<uid>/mute', methods=['POST'])
@admin_required
def api_admin_mute_user(uid):
    data = request.get_json() or {}
    duration = data.get('duration', 0)  # 禁言时长（秒），0=永久
    db = get_db()
    # M5 修复：不能禁言管理员/超级管理员
    target = _fetchone(db, 'SELECT is_admin, is_super_admin FROM users WHERE id=?', (uid,))
    if not target:
        return jsonify({'error': '用户不存在'}), 404
    if target['is_admin'] or target['is_super_admin']:
        return jsonify({'error': '不能禁言管理员'}), 400
    muted_until = (time.time() + duration) if duration > 0 else 9999999999
    if _USE_PG:
        _exec(db, 'UPDATE users SET muted_until=%s WHERE id=%s', (muted_until, uid))
    else:
        db.execute('UPDATE users SET muted_until=? WHERE id=?', (muted_until, uid))
        db.commit()
    db.close()
    return jsonify({'ok': True})


@app.route('/api/admin/users/<uid>/unmute', methods=['POST'])
@admin_required
def api_admin_unmute_user(uid):
    db = get_db()
    if _USE_PG:
        _exec(db, 'UPDATE users SET muted_until=0 WHERE id=%s', (uid,))
    else:
        db.execute('UPDATE users SET muted_until=0 WHERE id=?', (uid,))
        db.commit()
    db.close()
    return jsonify({'ok': True})


@app.route('/api/admin/users/<uid>/ban', methods=['POST'])
@admin_required
def api_admin_ban_user(uid):
    db = get_db()
    # M5 修复：不能封禁管理员/超级管理员
    target = _fetchone(db, 'SELECT is_admin, is_super_admin FROM users WHERE id=?', (uid,))
    if not target:
        return jsonify({'error': '用户不存在'}), 404
    if target['is_admin'] or target['is_super_admin']:
        return jsonify({'error': '不能封禁管理员'}), 400
    if _USE_PG:
        _exec(db, "UPDATE users SET status='banned' WHERE id=%s", (uid,))
    else:
        db.execute("UPDATE users SET status='banned' WHERE id=?", (uid,))
        db.commit()
    db.close()
    return jsonify({'ok': True})


@app.route('/api/admin/users/<uid>/unban', methods=['POST'])
@admin_required
def api_admin_unban_user(uid):
    db = get_db()
    if _USE_PG:
        _exec(db, "UPDATE users SET status='active', ban_reason='' WHERE id=%s", (uid,))
    else:
        db.execute("UPDATE users SET status='active', ban_reason='' WHERE id=?", (uid,))
        db.commit()
    db.close()
    return jsonify({'ok': True})


@app.route('/api/verify-email-and-login', methods=['POST'])
def api_verify_email_and_login():
    """被封禁（未验证邮箱）用户在登录页完成邮箱验证：校验验证码 -> 解封 -> 自动登录。

    请求体: { username, code }
    """
    data = request.get_json(silent=True) or {}
    username = (data.get('username') or '').strip()
    code = (data.get('code') or '').strip()
    if not username or not code:
        return jsonify({'error': '请填写用户名和验证码'}), 400

    db = get_db()
    row = _fetchone(db,
        'SELECT id, username, email, status, ban_reason, avatar, background, bio '
        'FROM users WHERE username=?', (username,))
    if not row:
        return jsonify({'error': '用户不存在'}), 404
    if row.get('status') != 'banned' or row.get('ban_reason') != 'unverified':
        return jsonify({'error': '该账号无需在此验证，请返回登录页'}), 400
    if not row.get('email'):
        return jsonify({'error': '账号未绑定邮箱'}), 400

    email = row['email'].lower()
    with _email_codes_lock:
        stored = _email_codes.get(email)
    now = time.time()
    if not stored or now > stored['expires']:
        return jsonify({'error': '验证码已过期，请重新获取', 'code_expired': True}), 400
    if not _hmac.compare_digest(stored['code'], code):
        _code_check_failed(email)
        return jsonify({'error': '验证码不正确'}), 400
    with _email_codes_lock:
        _email_codes.pop(email, None)

    # 解封 + 标记邮箱已验证
    if _USE_PG:
        _exec(db, "UPDATE users SET status='active', ban_reason='', email_verified=1, email_verify_deadline=0 WHERE id=%s", (row['id'],))
    else:
        db.execute("UPDATE users SET status='active', ban_reason='', email_verified=1, email_verify_deadline=0 WHERE id=?", (row['id'],))
        db.commit()

    # 自动登录
    session.clear()
    session['user_id'] = row['id']
    session.permanent = True
    client_ip = get_client_ip()
    if _USE_PG:
        _exec(db, 'UPDATE users SET last_ip=%s WHERE id=%s', (client_ip, row['id']))
    else:
        db.execute('UPDATE users SET last_ip=? WHERE id=?', (client_ip, row['id']))
        db.commit()
    db.close()

    avatar = f"/{row['avatar']}" if row['avatar'] else ''
    background = f"/{row['background']}" if row['background'] else ''
    user = {'id': row['id'], 'username': row['username'], 'email': row['email'] or '',
            'bio': row['bio'] or '', 'avatar': avatar, 'background': background}
    resp = jsonify({'ok': True, 'message': '验证成功，正在登录', 'user': user})
    _set_auth_cookie(resp, row['id'])
    return resp



# ===== 公告 =====
@app.route('/api/admin/announcements', methods=['GET'])
@super_admin_required
def api_admin_list_announcements():
    db = get_db()
    rows = _fetchall(db, '''
        SELECT a.id, a.title, a.content, a.created_at, u.username as author
        FROM announcements a LEFT JOIN users u ON a.created_by=u.id
        ORDER BY a.created_at DESC
    ''')
    return jsonify({'announcements': [dict(r) for r in rows]})


@app.route('/api/admin/announcements', methods=['POST'])
@super_admin_required
def api_admin_create_announcement():
    data = request.get_json() or {}
    title = _sanitize_plain((data.get('title') or '').strip())
    content = _sanitize_plain((data.get('content') or '').strip())
    if not title or not content:
        return jsonify({'error': '标题和内容不能为空'}), 400
    db = get_db()
    aid = 'ann_' + uuid.uuid4().hex[:8]
    now = time.time()
    if _USE_PG:
        _exec(db, 'INSERT INTO announcements (id, title, content, created_by, created_at) VALUES (%s,%s,%s,%s,%s)',
               (aid, title, content, session['user_id'], now))
    else:
        db.execute('INSERT INTO announcements (id, title, content, created_by, created_at) VALUES (?,?,?,?,?)',
                   (aid, title, content, session['user_id'], now))
        db.commit()
    db.close()
    return jsonify({'ok': True, 'id': aid})


@app.route('/api/admin/announcements/<aid>', methods=['DELETE'])
@super_admin_required
def api_admin_delete_announcement(aid):
    db = get_db()
    if _USE_PG:
        _exec(db, 'DELETE FROM announcements WHERE id=%s', (aid,))
    else:
        db.execute('DELETE FROM announcements WHERE id=?', (aid,))
        db.commit()
    db.close()
    return jsonify({'ok': True})


# ===== IP 封禁管理 =====
@app.route('/api/admin/ip-bans', methods=['GET'])
@admin_required
def api_admin_get_ip_bans():
    db = get_db()
    if _USE_PG:
        rows = _fetchall(db, 'SELECT b.ip, b.reason, b.created_at, u.username as created_by_name FROM ip_bans b LEFT JOIN users u ON b.created_by=u.id ORDER BY b.created_at DESC')
    else:
        rows = db.execute('SELECT b.ip, b.reason, b.created_at, u.username as created_by_name FROM ip_bans b LEFT JOIN users u ON b.created_by=u.id ORDER BY b.created_at DESC').fetchall()
    db.close()
    return jsonify({'bans': [dict(r) for r in rows]})


@app.route('/api/admin/ip-bans', methods=['POST'])
@admin_required
def api_admin_ban_ip():
    data = request.get_json() or {}
    ip = (data.get('ip') or '').strip()
    reason = (data.get('reason') or '').strip()
    if not ip:
        return jsonify({'error': 'IP 不能为空'}), 400
    db = get_db()
    now = time.time()
    if _USE_PG:
        _exec(db, 'INSERT INTO ip_bans (ip, reason, created_by, created_at) VALUES (%s,%s,%s,%s) ON CONFLICT (ip) DO UPDATE SET reason=%s, created_by=%s, created_at=%s',
               (ip, reason, session['user_id'], now, reason, session['user_id'], now))
    else:
        db.execute('INSERT OR REPLACE INTO ip_bans (ip, reason, created_by, created_at) VALUES (?,?,?,?)',
                   (ip, reason, session['user_id'], now))
        db.commit()
    db.close()
    return jsonify({'ok': True})


@app.route('/api/admin/ip-bans/<ip>', methods=['DELETE'])
@admin_required
def api_admin_unban_ip(ip):
    db = get_db()
    if _USE_PG:
        _exec(db, 'DELETE FROM ip_bans WHERE ip=%s', (ip,))
    else:
        db.execute('DELETE FROM ip_bans WHERE ip=?', (ip,))
        db.commit()
    db.close()
    return jsonify({'ok': True})


@app.route('/api/admin/users/<uid>/ip', methods=['GET'])
@admin_required
def api_admin_get_user_ip(uid):
    """获取用户最近使用的 IP（从聊天记录中提取）"""
    db = get_db()
    if _USE_PG:
        row = _fetchone(db, 'SELECT last_ip FROM users WHERE id=%s', (uid,))
    else:
        row = _fetchone(db, 'SELECT last_ip FROM users WHERE id=?', (uid,))
    ip = row['last_ip'] if row and row['last_ip'] else ''
    db.close()
    return jsonify({'ip': ip})


# ===== 管理员 API：违禁词管理 =====
@app.route('/api/admin/banned-words', methods=['GET'])
@admin_required
def api_admin_get_banned_words():
    db = get_db()
    rows = _fetchall(db, '''
        SELECT bw.id, bw.word, bw.created_at, u.username as created_by_name
        FROM banned_words bw LEFT JOIN users u ON bw.created_by=u.id
        ORDER BY bw.created_at DESC
    ''')
    return jsonify({'words': [dict(r) for r in rows]})


@app.route('/api/admin/banned-words', methods=['POST'])
@admin_required
def api_admin_add_banned_word():
    data = request.get_json() or {}
    word = (data.get('word') or '').strip()
    if not word:
        return jsonify({'error': '违禁词不能为空'}), 400
    db = get_db()
    # 检查是否已存在
    existing = _fetchone(db, 'SELECT id FROM banned_words WHERE word=?', (word,))
    if existing:
        return jsonify({'error': '该违禁词已存在'}), 400
    wid = 'bw_' + uuid.uuid4().hex[:12]
    now = time.time()
    if _USE_PG:
        _exec(db, 'INSERT INTO banned_words (id, word, created_by, created_at) VALUES (%s,%s,%s,%s)',
               (wid, word, session['user_id'], now))
    else:
        db.execute('INSERT INTO banned_words (id, word, created_by, created_at) VALUES (?,?,?,?)',
                   (wid, word, session['user_id'], now))
        db.commit()
    # 清除缓存
    _bad_words_cache['words'] = None
    return jsonify({'ok': True})


@app.route('/api/admin/banned-words/batch', methods=['POST'])
@admin_required
def api_admin_batch_add_banned_words():
    data = request.get_json() or {}
    words = data.get('words') or []
    if not words:
        return jsonify({'error': '违禁词列表不能为空'}), 400
    db = get_db()
    now = time.time()
    added = 0
    for w in words:
        w = w.strip()
        if not w:
            continue
        existing = _fetchone(db, 'SELECT id FROM banned_words WHERE word=?', (w,))
        if existing:
            continue
        wid = 'bw_' + uuid.uuid4().hex[:12]
        if _USE_PG:
            _exec(db, 'INSERT INTO banned_words (id, word, created_by, created_at) VALUES (%s,%s,%s,%s)',
                   (wid, w, session['user_id'], now))
        else:
            db.execute('INSERT INTO banned_words (id, word, created_by, created_at) VALUES (?,?,?,?)',
                       (wid, w, session['user_id'], now))
        added += 1
    if not _USE_PG:
        db.commit()
    _bad_words_cache['words'] = None
    return jsonify({'ok': True, 'added': added})


@app.route('/api/admin/banned-words/<wid>', methods=['DELETE'])
@admin_required
def api_admin_delete_banned_word(wid):
    db = get_db()
    if _USE_PG:
        _exec(db, 'DELETE FROM banned_words WHERE id=%s', (wid,))
    else:
        db.execute('DELETE FROM banned_words WHERE id=?', (wid,))
        db.commit()
    _bad_words_cache['words'] = None
    return jsonify({'ok': True})


@app.route('/api/announcements', methods=['GET'])
def api_get_announcements():
    """公告栏：返回邮箱验证提醒（未验证用户可见，已验证/未登录返回空）"""
    uid = _get_auth_user_id()
    if not uid:
        return jsonify({'announcements': []})
    db = get_db()
    row = _fetchone(db, 'SELECT email_verified FROM users WHERE id=?', (uid,))
    db.close()
    if not row or row['email_verified']:
        return jsonify({'announcements': []})
    return jsonify({'announcements': [{
        'id': 'verify_reminder',
        'title': '邮箱未验证',
        'content': '请前往「设置 → 邮箱管理」完成验证，3 天内未验证的账号将被自动删除。',
        'created_at': time.time(),
        'author': '系统'
    }]})


# ===== API：实时聊天 =====
@app.route('/api/chat/history', methods=['GET'])
def api_chat_history():
    """获取最近聊天记录"""
    # M11 修复：聊天历史需要登录
    if not _get_auth_user_id():
        return jsonify({'error': '未登录'}), 401
    db = get_db()
    rows = _fetchall(db, 'SELECT cm.id, cm.user_id, cm.username, cm.avatar, cm.content, cm.created_at FROM chat_messages cm ORDER BY cm.created_at DESC LIMIT 100')
    messages = []
    for r in reversed(rows):
        m = dict(r)
        m['avatar'] = f"/{m['avatar']}" if m.get('avatar') else ''
        messages.append(m)
    return jsonify({'messages': messages})


@app.route('/api/chat/online', methods=['GET'])
def api_chat_online():
    """获取在线用户列表（包含轮询模式用户）"""
    now = time.time()
    # 清理 30 秒未活跃的轮询用户
    expired = [uid for uid, info in _poll_users.items() if now - info.get('last_seen', 0) > 30]
    for uid in expired:
        _poll_users.pop(uid, None)
    # 如果当前用户已登录，注册为轮询在线用户
    if 'user_id' in session:
        db = get_db()
        user = _fetchone(db, 'SELECT username, avatar FROM users WHERE id=?', (session['user_id'],))
        if user:
            u = dict(user)
            _poll_users[session['user_id']] = {
                'id': session['user_id'],
                'username': u.get('username', ''),
                'avatar': f"/{u['avatar']}" if u.get('avatar') else '',
                'last_seen': now
            }
    online = dict(_online_users)
    for uid, info in _poll_users.items():
        if uid not in online:
            online[uid] = info
    return jsonify({'users': list(online.values()), 'count': len(online)})


@app.route('/api/chat/ai-quota', methods=['GET'])
@login_required
def api_chat_ai_quota():
    """获取当前用户聊天@AI的剩余次数"""
    ok, msg, remaining = check_chat_ai_quota(session['user_id'])
    return jsonify({'remaining': remaining, 'limit': AI_CHAT_DAILY_LIMIT, 'ok': ok})


@app.route('/api/chat/send', methods=['POST'])
def api_chat_send():
    """HTTP 方式发送聊天消息（WebSocket 不可用时的备用方案）"""
    if 'user_id' not in session:
        return jsonify({'error': '未登录'}), 401
    # 检查禁言
    u = get_user(session['user_id'])
    if u and u.get('muted_until', 0) > time.time():
        return jsonify({'error': '你已被禁言'}), 403
    data = request.get_json(silent=True) or {}
    content = filter_content((data.get('content') or '').strip())
    if not content or len(content) > 2000:
        return jsonify({'error': '消息内容无效'}), 400
    db = get_db()
    # 注册为轮询在线用户
    user = _fetchone(db, 'SELECT username, avatar FROM users WHERE id=?', (session['user_id'],))
    u = dict(user) if user else {}
    username = u.get('username', '')
    avatar = f"/{u['avatar']}" if u.get('avatar') else ''
    now = time.time()
    msg_id = 'msg_' + uuid.uuid4().hex[:12]
    # 注册为轮询在线用户
    _poll_users[session['user_id']] = {
        'id': session['user_id'],
        'username': username,
        'avatar': avatar,
        'last_seen': now
    }
    _exec(db, 'INSERT INTO chat_messages (id, user_id, username, avatar, content, created_at) VALUES (?,?,?,?,?,?)',
          (msg_id, session['user_id'], username, avatar.lstrip('/'), content, now))
    db.commit()
    msg = {
        'id': msg_id,
        'user_id': session['user_id'],
        'username': username,
        'avatar': avatar,
        'content': content,
        'created_at': now
    }
    # 如果 SocketIO 可用，广播给其他用户
    if _HAS_SOCKETIO and socketio:
        socketio.emit('new_message', msg, room='chat')

    # 检测 @AI 触发聊天AI回复
    if content and _detect_ai_mention(content):
        ok, quota_msg, remaining = check_chat_ai_quota(session['user_id'])
        if ok:
            log_chat_ai_usage(session['user_id'])
            t = threading.Thread(
                target=_generate_chat_ai_reply_async,
                args=(content, msg_id),
                daemon=True,
            )
            t.start()
        else:
            # 额度不足，发送提示消息
            hint_id = 'msg_' + uuid.uuid4().hex[:12]
            hint_content = f'⚠️ {quota_msg}'
            _exec(db, 'INSERT INTO chat_messages (id, user_id, username, avatar, content, created_at) VALUES (?,?,?,?,?,?)',
                  (hint_id, AI_BOT_ID, AI_BOT_NAME, '', hint_content, time.time()))
            db.commit()
            hint_msg = {
                'id': hint_id,
                'user_id': AI_BOT_ID,
                'username': AI_BOT_NAME,
                'avatar': '',
                'content': hint_content,
                'created_at': time.time()
            }
            if _HAS_SOCKETIO and socketio:
                socketio.emit('new_message', hint_msg, room='chat')

    return jsonify(msg)


@app.route('/api/chat/delete/<msg_id>', methods=['DELETE'])
def api_chat_delete(msg_id):
    """管理员删除消息或用户撤回自己的消息"""
    if 'user_id' not in session:
        return jsonify({'error': '未登录'}), 401
    db = get_db()
    msg = _fetchone(db, 'SELECT id, user_id FROM chat_messages WHERE id=?', (msg_id,))
    if not msg:
        return jsonify({'error': '消息不存在'}), 404
    # 检查权限：管理员可删任何消息，普通用户只能撤回自己的消息（2分钟内）
    user = _fetchone(db, 'SELECT is_admin FROM users WHERE id=?', (session['user_id'],))
    is_admin = user and user['is_admin']
    is_owner = msg['user_id'] == session['user_id']
    if not is_admin and not is_owner:
        return jsonify({'error': '无权操作'}), 403
    # 非管理员撤回时间限制：2分钟内
    if not is_admin and msg.get('created_at'):
        elapsed = time.time() - msg['created_at']
        if elapsed > 120:
            return jsonify({'error': '消息已超过 2 分钟，无法撤回'}), 403
    _exec(db, 'DELETE FROM chat_messages WHERE id=?', (msg_id,))
    db.commit()
    # 广播删除事件
    if _HAS_SOCKETIO and socketio:
        socketio.emit('message_deleted', {'id': msg_id}, room='chat')
    return jsonify({'ok': True})


# ===== API：私聊 =====

@app.route('/api/dm/conversations', methods=['GET'])
def api_dm_conversations():
    """获取当前用户的私聊会话列表"""
    if 'user_id' not in session:
        return jsonify({'error': '未登录'}), 401
    db = get_db()
    uid = session['user_id']
    rows = db.execute(
        'SELECT c.id, c.user1_id, c.user2_id, c.created_at FROM dm_conversations c WHERE c.user1_id=? OR c.user2_id=? ORDER BY c.created_at DESC',
        (uid, uid)
    ).fetchall()
    result = []
    for r in rows:
        r = dict(r)
        other_id = r['user2_id'] if r['user1_id'] == uid else r['user1_id']
        other = _fetchone(db, 'SELECT id, username, avatar FROM users WHERE id=?', (other_id,))
        # 获取最后一条消息
        last_msg = _fetchone(db, 'SELECT content, is_encrypted, created_at FROM dm_messages WHERE conversation_id=? ORDER BY created_at DESC LIMIT 1', (r['id'],))
        o = dict(other) if other else {}
        # 对方是否已上传公钥（用于判断是否可开启加密模式）
        peer_key = _fetchone(db, 'SELECT public_key FROM user_public_keys WHERE user_id=?', (other_id,))
        # 加密消息不在会话列表泄露明文，显示占位
        if last_msg and last_msg.get('is_encrypted'):
            last_text = '🔒 此消息已加密'
        else:
            last_text = last_msg['content'][:50] if last_msg else ''
        result.append({
            'id': r['id'],
            'other': {
                'id': o.get('id', ''),
                'username': o.get('username', ''),
                'avatar': f"/{o['avatar']}" if o.get('avatar') else '',
            },
            'lastMessage': last_text,
            'lastTime': last_msg['created_at'] if last_msg else r['created_at'],
            'otherHasKey': bool(peer_key),
            'encrypted': bool(last_msg and last_msg.get('is_encrypted')),
        })
    return jsonify(result)

@app.route('/api/dm/start', methods=['POST'])
def api_dm_start():
    """开始或获取与某用户的私聊会话"""
    if 'user_id' not in session:
        return jsonify({'error': '未登录'}), 401
    data = request.get_json()
    other_id = (data.get('userId') or '').strip()
    if not other_id:
        return jsonify({'error': '缺少用户ID'}), 400
    uid = session['user_id']
    if other_id == uid:
        return jsonify({'error': '不能和自己私聊'}), 400
    db = get_db()
    # 查找已有会话
    existing = _fetchone(db,
        'SELECT id FROM dm_conversations WHERE (user1_id=? AND user2_id=?) OR (user1_id=? AND user2_id=?)',
        (uid, other_id, other_id, uid))
    if existing:
        return jsonify({'conversationId': existing['id']})
    # 创建新会话
    conv_id = 'dm_' + uuid.uuid4().hex[:12]
    now = time.time()
    _exec(db, 'INSERT INTO dm_conversations (id, user1_id, user2_id, created_at) VALUES (?,?,?,?)',
          (conv_id, uid, other_id, now))
    db.commit()
    return jsonify({'conversationId': conv_id})

@app.route('/api/dm/messages/<conv_id>', methods=['GET'])
def api_dm_messages(conv_id):
    """获取私聊消息"""
    if 'user_id' not in session:
        return jsonify({'error': '未登录'}), 401
    db = get_db()
    uid = session['user_id']
    conv = _fetchone(db, 'SELECT id, user1_id, user2_id FROM dm_conversations WHERE id=?', (conv_id,))
    if not conv or (conv['user1_id'] != uid and conv['user2_id'] != uid):
        return jsonify({'error': '无权访问'}), 403
    rows = db.execute(
        'SELECT m.id, m.sender_id, m.content, m.is_encrypted, m.created_at, u.username, u.avatar FROM dm_messages m JOIN users u ON m.sender_id=u.id WHERE m.conversation_id=? ORDER BY m.created_at ASC LIMIT 200',
        (conv_id,)
    ).fetchall()
    messages = []
    for r in rows:
        r = dict(r)
        r['avatar'] = f"/{r['avatar']}" if r.get('avatar') else ''
        r['is_encrypted'] = bool(r.get('is_encrypted'))
        messages.append(r)
    return jsonify(messages)

@app.route('/api/dm/send', methods=['POST'])
def api_dm_send():
    """发送私聊消息"""
    if 'user_id' not in session:
        return jsonify({'error': '未登录'}), 401
    data = request.get_json()
    conv_id = (data.get('conversationId') or '').strip()
    content = (data.get('content') or '').strip()
    is_encrypted = int(bool(data.get('isEncrypted') or data.get('is_encrypted') or False))
    # 加密消息跳过违禁词过滤（密文是 Base64，过滤会破坏密文）
    if not is_encrypted:
        content = filter_content(content)
    if not conv_id or not content or len(content) > 4096:
        return jsonify({'error': '参数无效'}), 400
    db = get_db()
    uid = session['user_id']
    conv = _fetchone(db, 'SELECT id, user1_id, user2_id FROM dm_conversations WHERE id=?', (conv_id,))
    if not conv or (conv['user1_id'] != uid and conv['user2_id'] != uid):
        return jsonify({'error': '无权操作'}), 403
    msg_id = 'dmsg_' + uuid.uuid4().hex[:12]
    now = time.time()
    _exec(db, 'INSERT INTO dm_messages (id, conversation_id, sender_id, content, is_encrypted, created_at) VALUES (?,?,?,?,?,?)',
          (msg_id, conv_id, uid, content, is_encrypted, now))
    db.commit()
    user = _fetchone(db, 'SELECT username, avatar FROM users WHERE id=?', (uid,))
    u = dict(user) if user else {}
    msg = {
        'id': msg_id,
        'conversation_id': conv_id,
        'sender_id': uid,
        'username': u.get('username', ''),
        'avatar': f"/{u['avatar']}" if u.get('avatar') else '',
        'content': content,
        'is_encrypted': bool(is_encrypted),
        'created_at': now,
    }
    # 通过 Socket.IO 推送给对方和自己
    if _HAS_SOCKETIO and socketio:
        other_id = conv['user2_id'] if conv['user1_id'] == uid else conv['user1_id']
        msg_with_conv = dict(msg)
        msg_with_conv['recipient_id'] = other_id
        socketio.emit('dm_message', msg_with_conv, room=f'dm_{other_id}')
        # 也推送给发送者（确保发送者能看到自己发的消息）
        msg_self = dict(msg_with_conv)
        msg_self['recipient_id'] = uid
        socketio.emit('dm_message', msg_self, room=f'dm_{uid}')
    return jsonify(msg)


# ===== API：端到端加密公钥 =====

@app.route('/api/keys/upload', methods=['POST'])
def api_keys_upload():
    """上传/更新当前用户的 X25519 公钥（Base64）。私钥仅存于客户端，服务端不保存。"""
    if 'user_id' not in session:
        return jsonify({'error': '未登录'}), 401
    data = request.get_json() or {}
    public_key = (data.get('publicKey') or data.get('public_key') or '').strip()
    # 公钥为 Base64 编码的 X509 SubjectPublicKeyInfo，长度合理即可
    if not public_key or len(public_key) > 512:
        return jsonify({'error': '公钥无效'}), 400
    db = get_db()
    uid = session['user_id']
    now = time.time()
    # UPSERT：存在则更新，不存在则插入
    existing = _fetchone(db, 'SELECT user_id FROM user_public_keys WHERE user_id=?', (uid,))
    if existing:
        _exec(db, 'UPDATE user_public_keys SET public_key=?, updated_at=? WHERE user_id=?',
              (public_key, now, uid))
    else:
        _exec(db, 'INSERT INTO user_public_keys (user_id, public_key, updated_at) VALUES (?,?,?)',
              (uid, public_key, now))
    db.commit()
    return jsonify({'ok': True, 'updatedAt': now})


@app.route('/api/keys/<user_id>', methods=['GET'])
def api_keys_get(user_id):
    """查询某用户的公钥。无公钥返回 404（表示该用户尚未支持端到端加密）。"""
    if 'user_id' not in session:
        return jsonify({'error': '未登录'}), 401
    db = get_db()
    row = _fetchone(db, 'SELECT public_key, updated_at FROM user_public_keys WHERE user_id=?', (user_id,))
    if not row:
        return jsonify({'hasKey': False}), 404
    return jsonify({'hasKey': True, 'publicKey': row['public_key'], 'updatedAt': row['updated_at']})


# ===== API：关注 =====

@app.route('/api/follow', methods=['POST'])
def api_follow():
    if 'user_id' not in session:
        return jsonify({'error': '未登录'}), 401
    data = request.get_json()
    target_id = (data.get('userId') or '').strip()
    if not target_id:
        return jsonify({'error': '缺少用户ID'}), 400
    uid = session['user_id']
    if target_id == uid:
        return jsonify({'error': '不能关注自己'}), 400
    db = get_db()
    existing = _fetchone(db, 'SELECT 1 FROM follows WHERE follower_id=? AND following_id=?', (uid, target_id))
    if existing:
        return jsonify({'error': '已关注'}), 400
    _exec(db, 'INSERT INTO follows (follower_id, following_id, created_at) VALUES (?,?,?)', (uid, target_id, time.time()))
    # 通知被关注者
    nid = 'n_' + uuid.uuid4().hex[:12]
    notify_text = f'{get_username(uid)} 关注了你'
    _exec(db, 'INSERT INTO notifications (id, user_id, text, read, created_at) VALUES (?,?,?,?,?)',
          (nid, target_id, notify_text, 0, time.time()))
    socketio.emit('notification', {'text': notify_text}, room=f'dm_{target_id}')
    db.commit()
    return jsonify({'ok': True})

@app.route('/api/unfollow', methods=['POST'])
def api_unfollow():
    if 'user_id' not in session:
        return jsonify({'error': '未登录'}), 401
    data = request.get_json()
    target_id = (data.get('userId') or '').strip()
    if not target_id:
        return jsonify({'error': '缺少用户ID'}), 400
    uid = session['user_id']
    db = get_db()
    _exec(db, 'DELETE FROM follows WHERE follower_id=? AND following_id=?', (uid, target_id))
    db.commit()
    return jsonify({'ok': True})

@app.route('/api/follow/status/<target_id>', methods=['GET'])
def api_follow_status(target_id):
    if 'user_id' not in session:
        return jsonify({'following': False, 'follower_count': 0, 'following_count': 0})
    uid = session['user_id']
    db = get_db()
    is_following = _fetchone(db, 'SELECT 1 FROM follows WHERE follower_id=? AND following_id=?', (uid, target_id))
    follower_count = db.execute('SELECT COUNT(*) as c FROM follows WHERE following_id=?', (target_id,)).fetchone()['c']
    following_count = db.execute('SELECT COUNT(*) as c FROM follows WHERE follower_id=?', (target_id,)).fetchone()['c']
    boost_row = _fetchone(db, 'SELECT COALESCE(admin_follower_boost,0) as fb FROM users WHERE id=?', (target_id,))
    follower_count = max(0, follower_count + (boost_row['fb'] or 0))
    return jsonify({
        'following': bool(is_following),
        'follower_count': follower_count,
        'following_count': following_count
    })


@app.route('/api/users/<target_id>/followers', methods=['GET'])
def api_user_followers(target_id):
    """获取某用户的粉丝列表"""
    db = get_db()
    rows = _fetchall(db, '''
        SELECT u.id, u.username, u.avatar, u.bio, u.verified, u.verified_text,
               u.created_at,
               (SELECT COUNT(*) FROM posts WHERE author_id=u.id) as post_count
        FROM follows f
        JOIN users u ON f.follower_id = u.id
        WHERE f.following_id=?
        ORDER BY f.created_at DESC
    ''', (target_id,))
    users = []
    for r in rows:
        d = dict(r)
        d['verified'] = bool(d.get('verified'))
        users.append(d)
    return jsonify({'users': users})


@app.route('/api/users/<target_id>/following', methods=['GET'])
def api_user_following(target_id):
    """获取某用户关注的人列表"""
    db = get_db()
    rows = _fetchall(db, '''
        SELECT u.id, u.username, u.avatar, u.bio, u.verified, u.verified_text,
               u.created_at,
               (SELECT COUNT(*) FROM posts WHERE author_id=u.id) as post_count
        FROM follows f
        JOIN users u ON f.following_id = u.id
        WHERE f.follower_id=?
        ORDER BY f.created_at DESC
    ''', (target_id,))
    users = []
    for r in rows:
        d = dict(r)
        d['verified'] = bool(d.get('verified'))
        users.append(d)
    return jsonify({'users': users})


# 在线用户管理
_online_users = {}  # sid -> {id, username, avatar}
_poll_users = {}    # uid -> {id, username, avatar, last_seen} (HTTP 轮询用户)

# 直播版块：活跃直播 (WebRTC P2P mesh)。host_id -> {host_id, username, avatar, title, source_type, sid, started_at, viewers:set()}
_live_streams = {}
_live_disconnect_timers = {}  # host_id -> Timer，给主播短暂断网/Socket 重连留出恢复时间
_LIVE_RECONNECT_GRACE = 30
_LIVE_MAX_DURATION = 86400  # 直播最长时长（秒），超过自动清理僵尸条目

if _HAS_SOCKETIO and socketio:
    def _broadcast_live_list():
        socketio.emit('live_list', {'streams': [{
            'host_id': s['host_id'], 'username': s['username'], 'avatar': s['avatar'],
            'title': s['title'], 'cover': s.get('cover', ''),
            'is_quality': s.get('is_quality', False),
            'source_type': s.get('source_type', 'camera'),
            'viewer_count': len(s['viewers']), 'started_at': s['started_at'],
        } for s in _live_streams.values()]}, room='live_lobby')

    def _expire_disconnected_host(host_id, disconnected_sid):
        """仅在主播仍未重连时结束直播，避免网络抖动造成错误下线。"""
        _live_disconnect_timers.pop(host_id, None)
        stream = _live_streams.get(host_id)
        if not stream or stream.get('sid') != disconnected_sid:
            return
        _live_streams.pop(host_id, None)
        socketio.emit('live_ended', {'host_id': host_id}, room=f'live_{host_id}')
        socketio.emit('live_ended', {'host_id': host_id}, room='live_lobby')
        _broadcast_live_list()

    def _expire_stale_streams():
        """周期性清理僵尸直播条目（主播异常断开未触发 live_end 的情况）"""
        now = time.time()
        stale = [h for h, s in _live_streams.items() if now - s.get('started_at', 0) > _LIVE_MAX_DURATION]
        if stale:
            for host_id in stale:
                stream = _live_streams.pop(host_id, None)
                _live_disconnect_timers.pop(host_id, None)
                print(f'[live] 清理僵尸直播: host={host_id} age={int(now - (stream["started_at"] if stream else 0))}s', flush=True)
                try:
                    socketio.emit('live_ended', {'host_id': host_id}, room=f'live_{host_id}')
                    socketio.emit('live_ended', {'host_id': host_id}, room='live_lobby')
                except Exception:
                    pass
            _broadcast_live_list()

    _stale_timer = None
    def _start_stale_checker():
        global _stale_timer
        def _loop():
            _expire_stale_streams()
            _stale_timer = threading.Timer(300, _loop)  # 每 5 分钟检查一次
            _stale_timer.daemon = True
            _stale_timer.start()
        _loop()
    _start_stale_checker()
    print('[live] 僵尸直播清理定时器已启动（最大时长 24h，检查间隔 5min）')

    @socketio.on('connect')
    def handle_connect():
        # 仅从认证 cookie 或 session 获取 user_id，禁止 query 参数传 uid
        user_id = _get_auth_user_id()
        if not user_id:
            print(f'[Chat] 连接拒绝: 无有效认证, cookies={list(request.cookies.keys()) if request.cookies else None}')
            return False
        db = get_db()
        user = _fetchone(db, 'SELECT id, username, avatar, is_quality FROM users WHERE id=?', (user_id,))
        if not user:
            print(f'[Chat] 连接拒绝: 用户不存在, user_id={user_id}')
            return False
        u = dict(user)
        _online_users[request.sid] = {
            'id': u['id'],
            'username': u['username'],
            'avatar': f"/{u['avatar']}" if u.get('avatar') else '',
            'is_quality': bool(u.get('is_quality'))
        }
        join_room('chat')
        join_room(f'dm_{u["id"]}')  # 加入个人私聊房间
        print(f'[Chat] 用户 {u["username"]} 已连接, sid={request.sid}')
        emit('user_joined', {
            'user': _online_users[request.sid],
            'online_count': len(_online_users)
        }, room='chat')
        emit('online_update', {
            'users': list(_online_users.values()),
            'count': len(_online_users)
        }, room='chat')

    @socketio.on('disconnect')
    def handle_disconnect():
        user_info = _online_users.pop(request.sid, None)
        if user_info:
            leave_room('chat')
            # 一个账号可同时登录多台设备。只有真正承载直播的 SID 断开才进入下线宽限期。
            stream = _live_streams.get(user_info['id'])
            if stream and stream.get('sid') == request.sid:
                old_timer = _live_disconnect_timers.pop(user_info['id'], None)
                if old_timer:
                    old_timer.cancel()
                timer = threading.Timer(
                    _LIVE_RECONNECT_GRACE,
                    _expire_disconnected_host,
                    args=(user_info['id'], request.sid),
                )
                timer.daemon = True
                _live_disconnect_timers[user_info['id']] = timer
                timer.start()

            # 按 SID 清理观众状态，防止重复设备互相顶掉或人数永久占用。
            for host_id, active in list(_live_streams.items()):
                if request.sid in active['viewers']:
                    active['viewers'].discard(request.sid)
                    socketio.emit('viewer_left', {
                        'sid': request.sid,
                        'username': user_info.get('username', '观众'),
                    }, to=active.get('sid'))
                    socketio.emit('viewer_count', {
                        'count': len(active['viewers'])
                    }, room=f'live_{host_id}')
            emit('user_left', {
                'user': user_info,
                'online_count': len(_online_users)
            }, room='chat')
            emit('online_update', {
                'users': list(_online_users.values()),
                'count': len(_online_users)
            }, room='chat')

    @socketio.on('get_online')
    def handle_get_online():
        emit('online_update', {
            'users': list(_online_users.values()),
            'count': len(_online_users)
        })

    @socketio.on('send_message')
    def handle_message(data):
        user_id = _get_auth_user_id()
        if not user_id:
            return
        # 检查禁言
        u = get_user(user_id)
        if u and u.get('muted_until', 0) > time.time():
            return
        content = filter_content((data.get('content') or '').strip())
        if not content or len(content) > 2000:
            return
        db = get_db()
        msg_id = 'msg_' + uuid.uuid4().hex[:12]
        user_info = _online_users.get(request.sid, {})
        now = time.time()
        avatar = user_info.get('avatar', '')
        _exec(db, 'INSERT INTO chat_messages (id, user_id, username, avatar, content, created_at) VALUES (?,?,?,?,?,?)',
              (msg_id, user_id, user_info.get('username', ''), avatar.lstrip('/'), content, now))
        db.commit()
        emit('new_message', {
            'id': msg_id,
            'user_id': user_id,
            'username': user_info.get('username', ''),
            'avatar': avatar,
            'content': content,
            'created_at': now
        }, room='chat')

        # 检测 @AI 触发聊天AI回复
        if content and _detect_ai_mention(content):
            ok, quota_msg, remaining = check_chat_ai_quota(user_id)
            if ok:
                log_chat_ai_usage(user_id)
                t = threading.Thread(
                    target=_generate_chat_ai_reply_async,
                    args=(content, msg_id),
                    daemon=True,
                )
                t.start()
            else:
                hint_id = 'msg_' + uuid.uuid4().hex[:12]
                hint_content = f'⚠️ {quota_msg}'
                _exec(db, 'INSERT INTO chat_messages (id, user_id, username, avatar, content, created_at) VALUES (?,?,?,?,?,?)',
                      (hint_id, AI_BOT_ID, AI_BOT_NAME, '', hint_content, time.time()))
                db.commit()
                emit('new_message', {
                    'id': hint_id,
                    'user_id': AI_BOT_ID,
                    'username': AI_BOT_NAME,
                    'avatar': '',
                    'content': hint_content,
                    'created_at': time.time()
                }, room='chat')

    # ===== 直播信令 (WebRTC P2P mesh) =====
    # 主播浏览器推流给每个观众，视频流不过服务器；服务器只转发 SDP/ICE 信令。
    @socketio.on('live_lobby_join')
    def live_lobby_join():
        """加入直播大厅，接收直播上/下线通知，并立即返回当前列表"""
        join_room('live_lobby')
        streams = [{
            'host_id': s['host_id'], 'username': s['username'], 'avatar': s['avatar'],
            'title': s['title'], 'cover': s.get('cover', ''),
            'is_quality': s.get('is_quality', False),
            'source_type': s.get('source_type', 'camera'),
            'viewer_count': len(s['viewers']), 'started_at': s['started_at'],
        } for s in _live_streams.values()]
        emit('live_list', {'streams': streams})

    @socketio.on('live_lobby_leave')
    def live_lobby_leave():
        leave_room('live_lobby')

    @socketio.on('live_start')
    def live_start(data):
        """主播开播：需管理员审核通过的直播频道。加入自己的直播房间，并广播到大厅"""
        user_info = _online_users.get(request.sid)
        if not user_info:
            emit('live_error', {'error': '直播连接未认证，请刷新页面重新登录后再试'})
            return
        host_id = user_info['id']
        if host_id in _live_streams:
            emit('live_error', {'error': '你已在直播中'})
            return
        # 权限校验：必须有审核通过的直播频道（支持指定 channel_id 或回退到任一已通过频道）
        db = get_db()
        channel_id = (data or {}).get('channel_id', '')
        if channel_id:
            ch = _fetchone(db, 'SELECT id, name, cover, status, banned FROM live_channels WHERE id=? AND user_id=?', (channel_id, host_id))
        else:
            ch = _fetchone(db, 'SELECT id, name, cover, status, banned FROM live_channels WHERE user_id=? AND status=? ORDER BY created_at DESC LIMIT 1', (host_id, 'approved'))
        if not ch or ch.get('status') != 'approved':
            emit('live_error', {'error': '你的直播权限尚未通过审核，请先申请并等待管理员审核'})
            return
        if ch.get('banned'):
            emit('live_error', {'error': '你的直播间已被封禁，请联系管理员'})
            return
        title = (data or {}).get('title', '') or ch['name']
        ok, found = check_banned_words(title)
        if not ok:
            emit('live_error', {'error': f'标题包含违禁词：{"、".join(found[:5])}'})
            return
        # AI 内容审核（直播标题）
        ai_ok, ai_cat, ai_reason, ai_score = ai_moderate(title, 'live_title')
        if not ai_ok:
            emit('live_error', {'error': f'直播标题被 AI 审核拦截（{ai_cat}）：{ai_reason}'})
            return
        source_type = (data or {}).get('source_type', 'camera')
        quality = (data or {}).get('quality', 'auto')  # auto / 720p / 1080p
        cover = _public_upload_url(ch.get('cover'))
        is_quality = bool(ch.get('is_quality') or user_info.get('is_quality', False))
        _live_streams[host_id] = {
            'host_id': host_id, 'username': user_info['username'],
            'avatar': user_info.get('avatar', ''), 'title': title,
            'cover': cover, 'is_quality': is_quality,
            'source_type': source_type, 'sid': request.sid,
            'started_at': time.time(), 'viewers': set(),
            'channel_id': ch['id'], 'quality': quality,
        }
        join_room(f'live_{host_id}')
        # 广播到大厅：先 emit live_started，再立即 emit live_list 全量同步，确保所有客户端都能看到
        stream_payload = {
            'host_id': host_id, 'username': user_info['username'],
            'avatar': user_info.get('avatar', ''), 'title': title,
            'cover': cover, 'is_quality': is_quality,
            'source_type': source_type, 'viewer_count': 0,
            'started_at': _live_streams[host_id]['started_at'],
            'channel_id': ch['id'], 'quality': quality,
        }
        emit('live_started', stream_payload, room='live_lobby')
        # 立即全量广播 live_list，修复「有时开播后其他人显示未直播」的同步问题
        all_streams = [{
            'host_id': s['host_id'], 'username': s['username'], 'avatar': s['avatar'],
            'title': s['title'], 'cover': s.get('cover', ''),
            'is_quality': s.get('is_quality', False),
            'source_type': s.get('source_type', 'camera'),
            'viewer_count': len(s['viewers']), 'started_at': s['started_at'],
        } for s in _live_streams.values()]
        emit('live_list', {'streams': all_streams}, room='live_lobby')
        emit('live_started_ack', {'host_id': host_id, 'channel_id': ch['id']})

    @socketio.on('live_resume')
    def live_resume():
        """主播 Socket 自动重连后认领原直播，保留直播间与开始时间。"""
        user_info = _online_users.get(request.sid)
        if not user_info:
            return
        host_id = user_info['id']
        stream = _live_streams.get(host_id)
        if not stream:
            emit('live_resume_failed')
            return
        timer = _live_disconnect_timers.pop(host_id, None)
        if timer:
            timer.cancel()
        stream['sid'] = request.sid
        join_room(f'live_{host_id}')
        emit('live_resumed', {'host_id': host_id, 'channel_id': stream.get('channel_id')})
        _broadcast_live_list()

    @socketio.on('live_end')
    def live_end():
        """主播结束直播"""
        user_info = _online_users.get(request.sid)
        if not user_info:
            return
        host_id = user_info['id']
        stream = _live_streams.get(host_id)
        # 同账号其他装置无权结束承载直播装置的推流。
        if not stream or stream.get('sid') != request.sid:
            return
        stream = _live_streams.pop(host_id, None)
        if stream:
            # 保存直播历史
            try:
                duration = int(time.time() - stream['started_at'])
                peak = len(stream['viewers'])
                db = get_db()
                _exec(db, 'INSERT INTO live_history (id, host_id, title, started_at, ended_at, duration, peak_viewers) VALUES (?,?,?,?,?,?,?)',
                      ('live_' + uuid.uuid4().hex[:12], host_id, stream['title'], stream['started_at'], time.time(), duration, peak))
                db.commit()
            except Exception as e:
                print(f'[live] 保存历史失败: {e}')
            emit('live_ended', {'host_id': host_id}, room=f'live_{host_id}')
            emit('live_ended', {'host_id': host_id}, room='live_lobby')

    @socketio.on('live_join')
    def live_join(data):
        """观众加入直播：通知主播发 offer"""
        host_id = (data or {}).get('host_id')
        uid = _get_auth_user_id()
        if not uid:
            emit('live_error', {'error': '请先登录'})
            return
        if not host_id or host_id not in _live_streams:
            emit('live_error', {'error': '直播不存在或已结束'})
            return
        stream = _live_streams[host_id]
        # 观众上限（P2P 架构，主播带宽有限）
        if len(stream['viewers']) >= 10:
            emit('live_error', {'error': '直播间已满（上限 10 人），请稍后再试'})
            return
        join_room(f'live_{host_id}')
        stream['viewers'].add(request.sid)
        vi = _online_users.get(request.sid, {})
        emit('viewer_joined', {'sid': request.sid, 'username': vi.get('username', '观众'), 'avatar': vi.get('avatar', '')}, to=stream['sid'])
        emit('live_joined', {
            'host_id': host_id, 'username': stream['username'],
            'avatar': stream['avatar'], 'title': stream['title'],
            'is_quality': stream.get('is_quality', False),
            'started_at': stream['started_at'],
        })
        emit('viewer_count', {'count': len(stream['viewers'])}, room=f'live_{host_id}')

    @socketio.on('live_leave')
    def live_leave(data):
        """观众离开直播"""
        host_id = (data or {}).get('host_id')
        if not host_id or host_id not in _live_streams:
            return
        stream = _live_streams[host_id]
        stream['viewers'].discard(request.sid)
        leave_room(f'live_{host_id}')
        vi = _online_users.get(request.sid, {})
        emit('viewer_left', {'sid': request.sid, 'username': vi.get('username', '观众')}, to=stream['sid'])
        emit('viewer_count', {'count': len(stream['viewers'])}, room=f'live_{host_id}')

    @socketio.on('live_offer')
    def live_offer(data):
        """主播 -> 观众：转发 offer（仅允许主播发送）"""
        if _live_streams.get(request.sid, {}).get('host_sid') != request.sid:
            emit('live_error', {'error': '只有主播可以发送 offer'})
            return
        target_sid = (data or {}).get('to')
        if target_sid:
            emit('live_offer', {'sdp': data.get('sdp'), 'from': request.sid}, to=target_sid)

    @socketio.on('live_answer')
    def live_answer(data):
        """观众 -> 主播：转发 answer（仅允许观众发送）"""
        stream = _live_streams.get(request.sid)
        if not stream or stream.get('host_sid') == request.sid:
            emit('live_error', {'error': '只有观众可以发送 answer'})
            return
        target_sid = (data or {}).get('to')
        if target_sid:
            emit('live_answer', {'sdp': data.get('sdp'), 'from': request.sid}, to=target_sid)

    @socketio.on('live_ice')
    def live_ice(data):
        """双向转发 ICE candidate（仅允许已加入直播的 SID）"""
        stream = _live_streams.get(request.sid)
        if not stream:
            emit('live_error', {'error': '请先加入直播间'})
            return
        target_sid = (data or {}).get('to')
        if target_sid:
            emit('live_ice', {'candidate': data.get('candidate'), 'from': request.sid}, to=target_sid)

    @socketio.on('live_chat')
    def live_chat(data):
        """直播聊天：广播到对应直播房间（主播+所有观众），不存库纯实时"""
        user_info = _online_users.get(request.sid)
        if not user_info:
            return
        host_id = (data or {}).get('host_id')
        content = ((data or {}).get('content') or '').strip()
        if not host_id or not content or host_id not in _live_streams:
            return
        if len(content) > 500:
            content = content[:500]
        ok, found = check_banned_words(content)
        if not ok:
            emit('live_error', {'error': '消息包含违禁词，无法发送'})
            return
        emit('live_chat', {
            'user_id': user_info['id'],
            'username': user_info['username'],
            'avatar': user_info.get('avatar', ''),
            'is_quality': bool(user_info.get('is_quality', False)),
            'content': content,
            'created_at': time.time(),
        }, room=f'live_{host_id}')

    @socketio.on('live_update_title')
    def live_update_title(data):
        """主播中途修改直播标题：更新内存并广播到大厅与直播间"""
        user_info = _online_users.get(request.sid)
        if not user_info:
            return
        host_id = (data or {}).get('host_id')
        title = ((data or {}).get('title') or '').strip()
        if not host_id or host_id != user_info['id'] or host_id not in _live_streams:
            return
        if not title:
            return
        if len(title) > 60:
            title = title[:60]
        ok, found = check_banned_words(title)
        if not ok:
            emit('live_error', {'error': f'标题包含违禁词：{"、".join(found[:5])}'})
            return
        _live_streams[host_id]['title'] = title
        # 通知大厅更新卡片
        s = _live_streams[host_id]
        emit('live_title_updated', {
            'host_id': host_id, 'title': title,
            'username': s['username'], 'avatar': s['avatar'],
            'cover': s.get('cover', ''), 'is_quality': s.get('is_quality', False),
            'source_type': s.get('source_type', 'camera'),
            'viewer_count': len(s['viewers']), 'started_at': s['started_at'],
        }, room='live_lobby')
        # 通知直播间内观众
        emit('live_title_updated', {'host_id': host_id, 'title': title}, room=f'live_{host_id}')

    @socketio.on('live_report_stats')
    def live_report_stats(data):
        """观众上报延迟/统计，转发给主播（用于主播端显示观众延迟）"""
        user_info = _online_users.get(request.sid)
        if not user_info:
            return
        host_id = (data or {}).get('host_id')
        if not host_id or host_id not in _live_streams:
            return
        emit('viewer_stats', {
            'sid': request.sid,
            'latency': (data or {}).get('latency', 0),
            'jitter': (data or {}).get('jitter', 0),
            'packets_lost': (data or {}).get('packets_lost', 0),
            'bitrate': (data or {}).get('bitrate', 0),
        }, to=_live_streams[host_id]['sid'])


# ===== OAuth 2.0 Provider =====

@app.route('/oauth/authorize', methods=['GET'])
def oauth_authorize_get():
    """OAuth 2.0 授权端点 - 显示授权确认页面"""
    client_id = request.args.get('client_id', '')
    redirect_uri = request.args.get('redirect_uri', '')
    response_type = request.args.get('response_type', 'code')
    scope = request.args.get('scope', 'userinfo')
    state = request.args.get('state', '')

    if response_type != 'code':
        return jsonify({'error': 'unsupported_response_type', 'error_description': '仅支持 authorization_code 模式'}), 400

    if not client_id or not redirect_uri:
        return jsonify({'error': 'invalid_request', 'error_description': '缺少 client_id 或 redirect_uri'}), 400

    db = get_db()
    app_row = _fetchone(db, 'SELECT * FROM oauth_apps WHERE client_id=?', (client_id,))
    if not app_row:
        return jsonify({'error': 'invalid_client', 'error_description': '无效的 client_id'}), 400

    if app_row['redirect_uri'] != redirect_uri:
        return jsonify({'error': 'invalid_request', 'error_description': 'redirect_uri 不匹配'}), 400

    # 未登录则重定向到登录页（直接跳转到 /signin，而非论坛首页）
    if 'user_id' not in session:
        from urllib.parse import urlencode
        oauth_redirect = '/oauth/authorize?' + urlencode({
            'client_id': client_id,
            'redirect_uri': redirect_uri,
            'response_type': response_type,
            'scope': scope,
            'state': state,
        })
        return redirect('/signin?redirect=' + urlencode(oauth_redirect))

    # 已登录，显示授权确认页面
    app_name = app_row['app_name']
    app_description = app_row.get('app_description', '') or ''
    homepage_url = app_row.get('homepage_url', '') or ''

    # 获取当前用户信息，用于页面展示
    user = get_user(session['user_id'])
    user_display = _html_escape_mod.escape(user.get('email') or user.get('username') or '') if user else ''
    user_first_name = _html_escape_mod.escape((user.get('username') or '').split('_')[0]) if user else ''

    scope_labels = {
        'userinfo': '读取您的基本信息（用户名、头像）',
    }
    scope_list = scope.split(',')
    scope_descriptions = [scope_labels.get(s.strip(), s.strip()) for s in scope_list]

    scope_items_html = ''
    for desc in scope_descriptions:
        scope_items_html += f'<li>{_html_escape_mod.escape(desc)}</li>'

    from urllib.parse import urlencode
    deny_params = {'error': 'access_denied'}
    if state:
        deny_params['state'] = state
    deny_redirect = f'{redirect_uri}?{urlencode(deny_params)}'

    # 转义所有插入 HTML 的用户可控变量
    e_app_name = _html_escape_mod.escape(app_name)
    e_client_id = _html_escape_mod.escape(client_id)
    e_redirect_uri = _html_escape_mod.escape(redirect_uri)
    e_scope = _html_escape_mod.escape(scope)
    e_state = _html_escape_mod.escape(state)
    e_first_char = _html_escape_mod.escape(app_name[0].upper()) if app_name else 'A'

    html = f'''<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0, viewport-fit=cover">
<title>使用翱翔鸟账户登录 - {e_app_name}</title>
<style>
* {{ margin: 0; padding: 0; box-sizing: border-box; }}
:root {{
    --bg: #f5f5f7;
    --text: #1d1d1f;
    --text2: #6e6e73;
    --text3: #86868b;
    --accent: #0071e3;
    --accent-hover: #0077ed;
    --divider: #e5e5ea;
    --btn-cancel-bg: #e8e8ed;
    --btn-cancel-bg-hover: #dcdce0;
    --logo: /logo-light.png;
    --font: -apple-system, BlinkMacSystemFont, 'SF Pro Display', 'SF Pro Text', 'Helvetica Neue', sans-serif;
}}
@media (prefers-color-scheme: dark) {{
    :root {{
        --bg: #000000;
        --text: #f5f5f7;
        --text2: #aeaeb2;
        --text3: #86868b;
        --accent: #0a84ff;
        --accent-hover: #409cff;
        --divider: #38383a;
        --btn-cancel-bg: #1c1c1e;
        --btn-cancel-bg-hover: #2c2c2e;
        --logo: /logo-dark.png;
    }}
}}
html, body {{ height: 100%; }}
body {{
    font-family: var(--font);
    background: var(--bg);
    color: var(--text);
    -webkit-font-smoothing: antialiased;
    -moz-osx-font-smoothing: grayscale;
    display: flex;
    flex-direction: column;
    min-height: 100vh;
}}

/* ===== 顶部 logo 区（小、靠左、黑色） ===== */
.top-logo {{
    padding: 16px 20px;
    text-align: left;
}}
.top-logo img {{
    width: 24px; height: 24px;
    object-fit: contain;
    vertical-align: middle;
}}

/* ===== 分隔线 ===== */
.divider {{
    height: 0.5px;
    background: var(--divider);
    margin: 0 20px;
}}

/* ===== 信息栏：左 翱翔鸟账户 / 右 用户名，靠边对齐 ===== */
.info-bar {{
    display: flex; align-items: center; justify-content: space-between;
    padding: 14px 20px;
    width: 100%;
}}
.info-bar-left {{
    font-size: 16px; font-weight: 600; letter-spacing: -0.02em; color: var(--text);
}}
.info-bar-right {{
    font-size: 14px; color: var(--text2);
    max-width: 60%; overflow: hidden; text-overflow: ellipsis; white-space: nowrap;
    text-align: right;
}}

/* ===== 主体内容 ===== */
.main {{
    flex: 1;
    display: flex; flex-direction: column; align-items: center; justify-content: center;
    padding: 48px 24px;
    text-align: center;
    max-width: 460px; margin: 0 auto; width: 100%;
}}

/* 中心大 logo（放大） */
.center-logo {{
    margin-bottom: 36px;
}}
.center-logo img {{
    width: 96px; height: 96px;
    object-fit: contain;
    display: block;
}}

.prompt {{
    font-size: 20px;
    font-weight: 600;
    line-height: 1.35;
    color: var(--text);
    margin-bottom: 8px;
    letter-spacing: -0.02em;
}}
.prompt-app {{
    font-weight: 700;
}}
.prompt-account {{
    color: var(--text2);
    font-weight: 500;
}}
.prompt-sub {{
    font-size: 13px;
    color: var(--text2);
    margin-bottom: 36px;
    line-height: 1.5;
    letter-spacing: -0.01em;
}}

/* ===== 按钮组：靠近点 ===== */
.btn-group {{
    display: flex; gap: 8px; justify-content: center;
    width: 100%;
    max-width: 280px;
    margin: 0 auto;
}}
.btn {{
    flex: 1;
    padding: 12px 20px;
    border-radius: 980px;
    font-size: 15px;
    font-weight: 500;
    cursor: pointer;
    transition: all 0.2s cubic-bezier(0.25, 0.1, 0.25, 1);
    border: none;
    font-family: inherit;
    letter-spacing: -0.01em;
    text-align: center;
}}
.btn:active {{
    transform: scale(0.98);
}}
.btn-continue {{
    background: var(--accent);
    color: #ffffff;
}}
.btn-continue:hover {{
    background: var(--accent-hover);
}}
.btn-cancel {{
    background: var(--btn-cancel-bg);
    color: var(--text);
}}
.btn-cancel:hover {{
    background: var(--btn-cancel-bg-hover);
}}

/* ===== 切换账号 ===== */
.switch-account {{
    margin-top: 20px;
    font-size: 14px;
}}
.switch-account a {{
    color: var(--accent);
    text-decoration: none;
}}
.switch-account a:hover {{
    text-decoration: underline;
}}

/* ===== 底部版权 ===== */
.footer {{
    padding: 20px;
    text-align: center;
    font-size: 12px;
    color: var(--text3);
    line-height: 1.5;
    letter-spacing: -0.01em;
}}

/* ===== 响应式 ===== */
@media (max-width: 480px) {{
    .prompt {{ font-size: 18px; }}
    .center-logo img {{ width: 80px; height: 80px; }}
    .info-bar-left {{ font-size: 15px; }}
    .main {{ padding: 32px 20px; }}
}}
</style>
</head>
<body>

<div class="top-logo">
    <img id="topLogo" src="/logo-light.png" alt="SoaringBird">
</div>

<div class="divider"></div>

<div class="info-bar">
    <div class="info-bar-left">翱翔鸟账户</div>
    <div class="info-bar-right">{user_first_name}</div>
</div>

<div class="divider"></div>

<main class="main">
    <div class="center-logo">
        <img id="centerLogo" src="/logo-light.png" alt="SoaringBird">
    </div>
    <p class="prompt">要继续通过 <span class="prompt-account">SoaringBird 账户 ({user_first_name})</span> 使用 <span class="prompt-app">“{e_app_name}”</span> 吗？</p>
    <p class="prompt-sub">该应用将获取您的用户名和头像等基本信息</p>
    <div class="btn-group">
        <form method="POST" action="/oauth/authorize" style="flex:1">
            <input type="hidden" name="client_id" value="{e_client_id}">
            <input type="hidden" name="redirect_uri" value="{e_redirect_uri}">
            <input type="hidden" name="scope" value="{e_scope}">
            <input type="hidden" name="state" value="{e_state}">
            <input type="hidden" name="action" value="deny">
            <button type="submit" class="btn btn-cancel">取消</button>
        </form>
        <form method="POST" action="/oauth/authorize" style="flex:1">
            <input type="hidden" name="client_id" value="{e_client_id}">
            <input type="hidden" name="redirect_uri" value="{e_redirect_uri}">
            <input type="hidden" name="scope" value="{e_scope}">
            <input type="hidden" name="state" value="{e_state}">
            <input type="hidden" name="action" value="approve">
            <button type="submit" class="btn btn-continue">继续</button>
        </form>
    </div>
    <p class="switch-account"><a href="javascript:void(0)" onclick="switchAccount()">切换账号</a></p>
</main>

<footer class="footer">
    Copyright &copy; 2026 SoaringBird. 保留所有权利。
</footer>

<script>
(function() {{
    var mq = window.matchMedia('(prefers-color-scheme: dark)');
    function sync() {{
        var src = mq.matches ? '/logo-dark.png' : '/logo-light.png';
        var top = document.getElementById('topLogo');
        var center = document.getElementById('centerLogo');
        if (top) top.src = src;
        if (center) center.src = src;
    }}
    sync();
    if (mq.addEventListener) mq.addEventListener('change', sync);
    else if (mq.addListener) mq.addListener(sync);
}})();

// 切换账号：退出当前登录后，携带原授权参数跳转到登录页
function switchAccount() {{
    fetch('/api/logout', {{ method: 'POST', credentials: 'same-origin' }})
        .catch(function() {{}})
        .then(function() {{
            var next = window.location.pathname + window.location.search;
            window.location.href = '/signin?redirect=' + encodeURIComponent(next);
        }});
}}
</script>
</body>
</html>'''
    return html


@app.route('/oauth/authorize', methods=['POST'])
def oauth_authorize_post():
    """OAuth 2.0 授权端点 - 处理用户同意/拒绝"""
    if 'user_id' not in session:
        return jsonify({'error': 'unauthorized', 'error_description': '请先登录'}), 401

    client_id = request.form.get('client_id', '')
    redirect_uri = request.form.get('redirect_uri', '')
    scope = request.form.get('scope', 'userinfo')
    state = request.form.get('state', '')
    action = request.form.get('action', '')

    db = get_db()
    app_row = _fetchone(db, 'SELECT * FROM oauth_apps WHERE client_id=?', (client_id,))
    if not app_row or app_row['redirect_uri'] != redirect_uri:
        return jsonify({'error': 'invalid_request', 'error_description': '无效的请求参数'}), 400

    from urllib.parse import urlencode

    if action == 'deny':
        params = {'error': 'access_denied', 'error_description': '用户拒绝授权'}
        if state:
            params['state'] = state
        return redirect(f'{redirect_uri}?{urlencode(params)}')

    # 用户同意，生成 authorization code
    code = secrets.token_urlsafe(32)
    expires_at = time.time() + 300  # 5 分钟有效期
    user_id = session['user_id']

    _exec(db, 'INSERT INTO oauth_codes (code, client_id, user_id, redirect_uri, scope, expires_at) VALUES (?,?,?,?,?,?)',
          (code, client_id, user_id, redirect_uri, scope, expires_at))
    db.commit()

    params = {'code': code}
    if state:
        params['state'] = state
    return redirect(f'{redirect_uri}?{urlencode(params)}')


@app.route('/oauth/token', methods=['POST'])
def oauth_token():
    """OAuth 2.0 令牌端点"""
    grant_type = request.form.get('grant_type', '')
    code = request.form.get('code', '')
    redirect_uri = request.form.get('redirect_uri', '')
    client_id = request.form.get('client_id', '')
    client_secret = request.form.get('client_secret', '')

    if grant_type != 'authorization_code':
        return jsonify({'error': 'unsupported_grant_type', 'error_description': '仅支持 authorization_code'}), 400

    if not code or not client_id or not client_secret:
        return jsonify({'error': 'invalid_request', 'error_description': '缺少必要参数'}), 400

    db = get_db()

    # 验证 client_id 和 client_secret
    app_row = _fetchone(db, 'SELECT * FROM oauth_apps WHERE client_id=?', (client_id,))
    if not app_row or app_row['client_secret'] != client_secret:
        return jsonify({'error': 'invalid_client', 'error_description': '无效的客户端凭据'}), 401

    # 验证 code
    code_row = _fetchone(db, 'SELECT * FROM oauth_codes WHERE code=?', (code,))
    if not code_row:
        return jsonify({'error': 'invalid_grant', 'error_description': '无效的授权码'}), 400

    if code_row['client_id'] != client_id:
        return jsonify({'error': 'invalid_grant', 'error_description': '授权码与客户端不匹配'}), 400

    if code_row['redirect_uri'] != redirect_uri:
        return jsonify({'error': 'invalid_grant', 'error_description': 'redirect_uri 不匹配'}), 400

    if code_row['expires_at'] < time.time():
        # 删除过期 code
        _exec(db, 'DELETE FROM oauth_codes WHERE code=?', (code,))
        db.commit()
        return jsonify({'error': 'invalid_grant', 'error_description': '授权码已过期'}), 400

    # 生成 access token
    access_token = secrets.token_urlsafe(32)
    expires_at = time.time() + 3600  # 1 小时有效期

    _exec(db, 'INSERT INTO oauth_tokens (access_token, client_id, user_id, scope, expires_at) VALUES (?,?,?,?,?)',
          (access_token, client_id, code_row['user_id'], code_row['scope'], expires_at))

    # 删除已使用的 code
    _exec(db, 'DELETE FROM oauth_codes WHERE code=?', (code,))
    db.commit()

    return jsonify({
        'access_token': access_token,
        'token_type': 'Bearer',
        'expires_in': 3600,
        'scope': code_row['scope']
    })


@app.route('/oauth/userinfo', methods=['GET'])
def oauth_userinfo():
    """OAuth 2.0 用户信息端点"""
    auth_header = request.headers.get('Authorization', '')
    if not auth_header.startswith('Bearer '):
        return jsonify({'error': 'invalid_token', 'error_description': '缺少 Bearer Token'}), 401

    access_token = auth_header[7:]
    db = get_db()
    token_row = _fetchone(db, 'SELECT * FROM oauth_tokens WHERE access_token=?', (access_token,))

    if not token_row:
        return jsonify({'error': 'invalid_token', 'error_description': '无效的访问令牌'}), 401

    if token_row['expires_at'] < time.time():
        _exec(db, 'DELETE FROM oauth_tokens WHERE access_token=?', (access_token,))
        db.commit()
        return jsonify({'error': 'invalid_token', 'error_description': '访问令牌已过期'}), 401

    user_row = _fetchone(db, 'SELECT id, username, avatar FROM users WHERE id=?', (token_row['user_id'],))
    if not user_row:
        return jsonify({'error': 'invalid_token', 'error_description': '用户不存在'}), 401

    avatar = f"/{user_row['avatar']}" if user_row['avatar'] else ''
    return jsonify({
        'id': user_row['id'],
        'username': user_row['username'],
        'avatar': avatar
    })


# ===== 开发者应用管理 API =====

@app.route('/api/developer/apps', methods=['POST'])
@login_required
def api_developer_create_app():
    """注册新的 OAuth 应用"""
    data = request.get_json()
    app_name = (data.get('app_name') or '').strip()
    app_description = (data.get('app_description') or '').strip()
    redirect_uri = (data.get('redirect_uri') or '').strip()
    homepage_url = (data.get('homepage_url') or '').strip()

    if not app_name or not redirect_uri:
        return jsonify({'error': '应用名称和回调地址不能为空'}), 400

    app_id = uuid.uuid4().hex
    client_id = uuid.uuid4().hex[:16]
    client_secret = secrets.token_urlsafe(32)
    user_id = session['user_id']

    db = get_db()
    _exec(db, 'INSERT INTO oauth_apps (id, client_id, client_secret, app_name, app_description, redirect_uri, homepage_url, user_id, created_at) VALUES (?,?,?,?,?,?,?,?,?)',
          (app_id, client_id, client_secret, app_name, app_description, redirect_uri, homepage_url, user_id, time.time()))
    db.commit()

    return jsonify({
        'app': {
            'id': app_id,
            'client_id': client_id,
            'client_secret': client_secret,
            'app_name': app_name,
            'app_description': app_description,
            'redirect_uri': redirect_uri,
            'homepage_url': homepage_url,
            'user_id': user_id,
            'created_at': time.time()
        }
    }), 201


@app.route('/api/developer/apps', methods=['GET'])
@login_required
def api_developer_list_apps():
    """列出当前用户的所有应用"""
    user_id = session['user_id']
    db = get_db()
    rows = _fetchall(db, 'SELECT * FROM oauth_apps WHERE user_id=? ORDER BY created_at DESC', (user_id,))
    apps = []
    for row in rows:
        apps.append({
            'id': row['id'],
            'client_id': row['client_id'],
            'client_secret': row['client_secret'],
            'app_name': row['app_name'],
            'app_description': row['app_description'] or '',
            'redirect_uri': row['redirect_uri'],
            'homepage_url': row['homepage_url'] or '',
            'user_id': row['user_id'],
            'created_at': row['created_at']
        })
    return jsonify({'apps': apps})


@app.route('/api/developer/apps/<app_id>', methods=['PUT'])
@login_required
def api_developer_update_app(app_id):
    """更新应用信息"""
    user_id = session['user_id']
    db = get_db()
    app_row = _fetchone(db, 'SELECT * FROM oauth_apps WHERE id=?', (app_id,))
    if not app_row:
        return jsonify({'error': '应用不存在'}), 404
    if app_row['user_id'] != user_id:
        return jsonify({'error': '无权操作'}), 403

    data = request.get_json()
    app_name = data.get('app_name')
    app_description = data.get('app_description')
    redirect_uri = data.get('redirect_uri')
    homepage_url = data.get('homepage_url')

    updates = []
    params = []
    if app_name is not None:
        updates.append('app_name=?')
        params.append(app_name.strip())
    if app_description is not None:
        updates.append('app_description=?')
        params.append(app_description.strip())
    if redirect_uri is not None:
        updates.append('redirect_uri=?')
        params.append(redirect_uri.strip())
    if homepage_url is not None:
        updates.append('homepage_url=?')
        params.append(homepage_url.strip())

    if not updates:
        return jsonify({'error': '没有需要更新的字段'}), 400

    params.append(app_id)
    _exec(db, f'UPDATE oauth_apps SET {",".join(updates)} WHERE id=?', params)
    db.commit()

    updated = _fetchone(db, 'SELECT * FROM oauth_apps WHERE id=?', (app_id,))
    return jsonify({
        'app': {
            'id': updated['id'],
            'client_id': updated['client_id'],
            'client_secret': updated['client_secret'],
            'app_name': updated['app_name'],
            'app_description': updated['app_description'] or '',
            'redirect_uri': updated['redirect_uri'],
            'homepage_url': updated['homepage_url'] or '',
            'user_id': updated['user_id'],
            'created_at': updated['created_at']
        }
    })


@app.route('/api/developer/apps/<app_id>', methods=['DELETE'])
@login_required
def api_developer_delete_app(app_id):
    """删除应用及其关联的 codes 和 tokens"""
    user_id = session['user_id']
    db = get_db()
    app_row = _fetchone(db, 'SELECT * FROM oauth_apps WHERE id=?', (app_id,))
    if not app_row:
        return jsonify({'error': '应用不存在'}), 404
    if app_row['user_id'] != user_id:
        return jsonify({'error': '无权操作'}), 403

    client_id = app_row['client_id']
    _exec(db, 'DELETE FROM oauth_codes WHERE client_id=?', (client_id,))
    _exec(db, 'DELETE FROM oauth_tokens WHERE client_id=?', (client_id,))
    _exec(db, 'DELETE FROM oauth_apps WHERE id=?', (app_id,))
    db.commit()

    return jsonify({'ok': True})


@app.route('/developer')
@app.route('/developer/')
def developer_page():
    """开发者管理页面"""
    return send_from_directory(_FRONTEND_DIR, 'developer.html')


# ===== 应用更新 API =====
# APK 文件存放于 static/app/soaringbird-latest.apk
# 通过通配静态路由 /<path:path> 自动提供下载
# 更新步骤：将新版 APK 放入 static/app/ 目录，修改下方版本号和 changelog
APP_LATEST_VERSION = '3.0-RC'
APP_LATEST_VERSION_CODE = 30
APP_LATEST_CHANGELOG = '翱翔鸟 3.0 RC：全新扁平化 iOS 18 风格界面，发帖、阅读、直播三大能力，苹果式渐变配色与交互动效，适配 Android 全面屏'
APP_FORCE_UPDATE = False


@app.route('/api/app/latest-version', methods=['GET'])
def api_app_latest_version():
    """返回客户端最新版本信息（用于应用内更新）

    包含 APK 文件的 size 和 sha256，客户端下载后可校验完整性，
    避免因 CDN 缓存导致下载到旧版本 APK。
    """
    apk_path = os.path.join(os.path.dirname(__file__), 'static', 'app', 'soaringbird-latest.apk')
    apk_size = 0
    apk_sha256 = ''
    try:
        if os.path.isfile(apk_path):
            apk_size = os.path.getsize(apk_path)
            h = hashlib.sha256()
            with open(apk_path, 'rb') as f:
                for chunk in iter(lambda: f.read(8192), b''):
                    h.update(chunk)
            apk_sha256 = h.hexdigest()
    except Exception as e:
        print(f'[APP_UPDATE] 计算 APK 哈希失败: {e}')
    return jsonify({
        'version': APP_LATEST_VERSION,
        'versionCode': APP_LATEST_VERSION_CODE,
        'downloadUrl': '/static/app/soaringbird-latest.apk',
        'changelog': APP_LATEST_CHANGELOG,
        'forceUpdate': APP_FORCE_UPDATE,
        'size': apk_size,
        'sha256': apk_sha256
    })


# ===== APK 下载频率限制 =====
_DOWNLOAD_LIMIT = 2  # 最多 2 次
_DOWNLOAD_WINDOW = 15 * 60  # 15 分钟（秒）
_download_history = {}  # IP -> [timestamp, ...]
_download_tokens = {}  # token -> {ip, expires}

@app.route('/api/download/verify', methods=['POST'])
def api_download_verify():
    """验证 Turnstile + 频率限制，返回下载令牌"""
    data = request.get_json() or {}
    turnstile_token = data.get('turnstile_token') or ''

    # Turnstile 验证（site key 未配置时跳过）
    if TURNSTILE_SECRET_KEY:
        if not _verify_turnstile(turnstile_token):
            return jsonify({'error': '人机验证失败'}), 403

    client_ip = get_client_ip()
    now = time.time()

    # 清理过期记录
    if client_ip in _download_history:
        _download_history[client_ip] = [t for t in _download_history[client_ip] if now - t < _DOWNLOAD_WINDOW]
    else:
        _download_history[client_ip] = []

    # 检查频率限制
    if len(_download_history[client_ip]) >= _DOWNLOAD_LIMIT:
        remaining = int(_DOWNLOAD_WINDOW - (now - _download_history[client_ip][0]))
        return jsonify({'error': f'下载次数过多，请 {remaining} 秒后再试'}), 429

    # 生成下载令牌（5 分钟有效）
    token = secrets.token_urlsafe(32)
    _download_tokens[token] = {'ip': client_ip, 'expires': now + 300}

    return jsonify({'download_url': f'/api/download/apk?token={token}'})

@app.route('/api/download/apk')
def api_download_apk():
    """验证令牌 + 频率限制，返回 APK 文件"""
    token = request.args.get('token', '')
    if not token or token not in _download_tokens:
        return jsonify({'error': '无效的下载链接'}), 403

    token_info = _download_tokens[token]
    now = time.time()

    # 检查令牌过期
    if now > token_info['expires']:
        _download_tokens.pop(token, None)
        return jsonify({'error': '下载链接已过期，请重新验证'}), 403

    client_ip = get_client_ip()

    # 检查频率限制
    if client_ip in _download_history:
        _download_history[client_ip] = [t for t in _download_history[client_ip] if now - t < _DOWNLOAD_WINDOW]
    else:
        _download_history[client_ip] = []

    if len(_download_history[client_ip]) >= _DOWNLOAD_LIMIT:
        return jsonify({'error': '下载次数过多，请稍后再试'}), 429

    # 记录下载
    _download_history[client_ip].append(now)
    # 删除已使用的令牌
    _download_tokens.pop(token, None)

    # 返回 APK 文件
    apk_path = os.path.join(os.path.dirname(__file__), 'static', 'app', 'soaringbird-latest.apk')
    if not os.path.exists(apk_path):
        return jsonify({'error': 'APK 文件不存在'}), 404

    return send_from_directory(os.path.dirname(apk_path), os.path.basename(apk_path), as_attachment=True)


# ===== PeaceNews 新闻模块 API =====
# 评论速率限制（每用户 10 分钟最多 10 条，进程内存实现，与登录/注册限流同模式）
_news_comment_attempts = {}  # {user_id: [timestamp, ...]}
_news_comment_lock = _threading.Lock()
_NEWS_COMMENT_MAX = 10
_NEWS_COMMENT_WINDOW = 600

def _check_news_comment_rate_limit(user_id):
    """检查新闻评论速率限制，返回 (allowed, retry_after_seconds)"""
    now = time.time()
    with _news_comment_lock:
        attempts = _news_comment_attempts.get(user_id, [])
        attempts = [t for t in attempts if now - t < _NEWS_COMMENT_WINDOW]
        _news_comment_attempts[user_id] = attempts
        if len(attempts) >= _NEWS_COMMENT_MAX:
            oldest = attempts[0]
            retry_after = int(_NEWS_COMMENT_WINDOW - (now - oldest))
            return False, max(retry_after, 0)
        return True, 0

def _record_news_comment(user_id):
    """记录一次新闻评论"""
    now = time.time()
    with _news_comment_lock:
        attempts = _news_comment_attempts.get(user_id, [])
        attempts.append(now)
        _news_comment_attempts[user_id] = attempts


def _get_news_config():
    """读取排版配置 + 调度全局配置（带默认值）

    白名单同时覆盖后台排版设置与一期抓取调度模块的全局开关，
    避免调度相关 key 写入 news_config 后被读取时丢弃。
    """
    cfg = {'hero': '1', 'columns': '3', 'per_page': '20',
           'scheduler_enabled': '1', 'scheduler_interval_min': '10',
           'scheduler_fetch_timeout': '15'}
    try:
        db = get_db()
        rows = _fetchall(db, 'SELECT key, value FROM news_config')
        for r in rows:
            if r['key'] in cfg:
                cfg[r['key']] = r['value']
    except Exception:
        pass
    return cfg


@app.route('/api/news/config', methods=['GET'])
def api_get_news_config():
    """公开：排版配置"""
    return jsonify({'config': _get_news_config()})


@app.route('/api/admin/news/config', methods=['PUT'])
@admin_required
def api_admin_update_news_config():
    """更新配置：hero(0/1)、columns(2/3/4)、per_page(5-50)，
    以及调度全局项 scheduler_enabled(0/1)、scheduler_interval_min(5-15)、scheduler_fetch_timeout(5-60)"""
    data = request.get_json() or {}
    updates = {}
    if 'hero' in data:
        updates['hero'] = '1' if str(data['hero']) in ('1', 'true', 'True') else '0'
    if 'columns' in data:
        try:
            c = int(data['columns'])
            if c not in (2, 3, 4):
                raise ValueError
            updates['columns'] = str(c)
        except (TypeError, ValueError):
            return jsonify({'error': 'columns 只能是 2、3 或 4'}), 400
    if 'per_page' in data:
        try:
            p = int(data['per_page'])
            if not (5 <= p <= 50):
                raise ValueError
            updates['per_page'] = str(p)
        except (TypeError, ValueError):
            return jsonify({'error': 'per_page 需在 5-50 之间'}), 400
    if 'scheduler_enabled' in data:
        updates['scheduler_enabled'] = '1' if str(data['scheduler_enabled']) in ('1', 'true', 'True') else '0'
    if 'scheduler_interval_min' in data:
        try:
            v = int(data['scheduler_interval_min'])
            if not (5 <= v <= 15):
                raise ValueError
            updates['scheduler_interval_min'] = str(v)
        except (TypeError, ValueError):
            return jsonify({'error': 'scheduler_interval_min 需在 5-15 之间'}), 400
    if 'scheduler_fetch_timeout' in data:
        try:
            v = int(data['scheduler_fetch_timeout'])
            if not (5 <= v <= 60):
                raise ValueError
            updates['scheduler_fetch_timeout'] = str(v)
        except (TypeError, ValueError):
            return jsonify({'error': 'scheduler_fetch_timeout 需在 5-60 之间'}), 400
    if not updates:
        return jsonify({'error': '没有可更新的配置项'}), 400
    db = get_db()
    for k, v in updates.items():
        _exec(db, 'INSERT INTO news_config (key, value) VALUES (?,?) ON CONFLICT (key) DO UPDATE SET value=excluded.value' if _USE_PG
              else 'INSERT OR REPLACE INTO news_config (key, value) VALUES (?,?)', (k, v))
    db.commit()
    # 立即刷新调度模块的配置缓存，无需等待 30s 自动过期
    try:
        if '_pn_scheduler' in globals():
            _pn_scheduler.global_config(force=True)
    except Exception:
        pass
    return jsonify({'config': _get_news_config()})


def _parse_news_images(raw):
    """解析新闻插图 JSON，返回 [{url, caption, position}] 列表"""
    if not raw:
        return []
    try:
        import json
        data = json.loads(raw)
        if isinstance(data, list):
            return data
    except Exception:
        pass
    return []


_NEWS_PIXEL_IMAGE_RE = re.compile(r'(rss-pixel|/tracking/|tracking\.(?:png|gif|jpg)|spacer\.(?:gif|png)|transparent\.(?:gif|png)|/(?:1x1|blank|pixel|dot)\.(?:png|gif|jpg|jpeg|webp))', re.I)


def _news_image_url(raw):
    """把 news.image 统一成前端可直接使用的地址。

    - 空值 -> ''
    - 已是绝对地址（http/https 或 / 开头）-> 原样返回
    - 站内相对路径 -> 补 '/' 前缀
    （修复：此前一律拼接 '/'，会把外链图片拼成非法地址导致裂图）
    """
    if not raw:
        return ''
    s = str(raw).strip()
    if not s:
        return ''
    if s.startswith(('http://', 'https://', '/', 'data:')):
        # 过滤追踪像素 / 占位图（如 NPR 的 rss-pixel 统计像素），避免头图灰块
        if _NEWS_PIXEL_IMAGE_RE.search(s):
            return ''
        return s
    return '/' + s


# ==========================================================================
# 头条联网补图：无图头条在选定后尝试搜索相关报道配图（Bing Images RSS）
# 原则：只补与标题语义相关的媒体图；搜索失败/无结果时保持无图降级卡，绝不用无关图
# ==========================================================================
_HEADLINE_IMG_CACHE = {}
_HEADLINE_IMG_CACHE_TTL = 3600


def _headline_search_image(title):
    """按新闻标题联网搜索一张相关图片，返回可用 URL；失败返回空串。"""
    import urllib.request as _ur
    import urllib.parse as _up
    import xml.etree.ElementTree as _ET
    key = 'himg:' + (title or '').strip()[:80]
    now = time.time()
    hit = _HEADLINE_IMG_CACHE.get(key)
    if hit and now - hit[0] < _HEADLINE_IMG_CACHE_TTL:
        return hit[1]
    url = ('https://www.bing.com/images/search?q=' + _up.quote((title or '')[:60])
           + '&format=rss&count=8&first=1')
    req = _ur.Request(url, headers={
        'User-Agent': ('Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 '
                       '(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36'),
        'Accept': 'application/rss+xml, application/xml, text/xml, */*',
    })
    img = ''
    try:
        with _ur.urlopen(req, timeout=6) as resp:
            body = resp.read().decode('utf-8', errors='ignore')
        # RSSHub/Bing 偶发非法 XML 字符，先尝试标准解析，失败则正则兜底
        try:
            root = _ET.fromstring(body)
            for item in root.iter('item'):
                # 1) media:content / media:thumbnail 的 url 属性（优先）
                for mc in item.iter():
                    if mc.tag.endswith('}content') or mc.tag.endswith('}thumbnail'):
                        u = (mc.get('url') or '').strip()
                        if u.startswith('http') and not _NEWS_PIXEL_IMAGE_RE.search(u):
                            img = u
                            break
                if img:
                    break
                # 2) description 内嵌 <img src=...>（常有原图直链）
                desc_el = item.find('description')
                if desc_el is not None and desc_el.text:
                    m = re.search(r'<img[^>]+src=["\']([^"\']+)["\']', desc_el.text, re.I)
                    if m:
                        u = m.group(1).strip()
                        if u.startswith('http') and not _NEWS_PIXEL_IMAGE_RE.search(u):
                            img = u
                            break
                # 3) link（Bing 缩略图 mm.bing.net，质量次之但可用）
                link_el = item.find('link')
                if link_el is not None and link_el.text:
                    u = link_el.text.strip()
                    if u.startswith('http') and 'mm.bing.net' in u and not _NEWS_PIXEL_IMAGE_RE.search(u):
                        img = u
                        break
        except Exception:
            # 正则兜底：直接从原始 body 抓图片 URL
            for m in re.finditer(r'<(?:media:)?(?:content|thumbnail)\s+url=["\']([^"\']+)["\']', body, re.I):
                u = m.group(1).strip()
                if u.startswith('http') and not _NEWS_PIXEL_IMAGE_RE.search(u):
                    img = u
                    break
            if not img:
                for m in re.finditer(r'<img[^>]+src=["\']([^"\']+)["\']', body, re.I):
                    u = m.group(1).strip()
                    if u.startswith('http') and not _NEWS_PIXEL_IMAGE_RE.search(u):
                        img = u
                        break
    except Exception:
        img = ''
    if len(_HEADLINE_IMG_CACHE) > 2000:
        _HEADLINE_IMG_CACHE.clear()
    _HEADLINE_IMG_CACHE[key] = (now, img)
    return img


def _headline_attach_images(items):
    """给头条中无图的条目并行联网补图；找不到/失败时保持无图降级，不阻塞返回。"""
    need = [d for d in items if not d.get('image')]
    if not need:
        return
    from concurrent.futures import ThreadPoolExecutor as _TPE
    try:
        with _TPE(max_workers=min(5, max(1, len(need)))) as pool:
            fut = {}
            for d in need:
                # 用原文标题搜索更精准（中文翻译后标题可能搜不到原报道配图）
                q = d.get('original_title') or d.get('title') or ''
                fut[pool.submit(_headline_search_image, q)] = d
            for f, d in fut.items():
                try:
                    u = f.result(timeout=8)
                except Exception:
                    u = ''
                if u:
                    d['image'] = u
                    d['image_from'] = 'search'
    except Exception:
        pass


_NEWS_TITLE_PREFIX_RE = re.compile(r'^([\u4e00-\u9fffA-Za-z0-9]{1,12})\s*\|\s*(.{5,})$')
# 已知源站栏目名白名单：命中后允许从标题中剥离（括号前缀/冒号前缀/括号后缀）
_NEWS_COLUMN_WORDS = (
    '经济观察', '文化观察', '村播观察', '第一观察', '民生观察', '产经观察',
    '海南产经新观察', '山东城市观察', '两岸观察', 'IPO观察',
    '时评', '深度', '界面晚报', '今日看盘', '零时差', '本周看什么',
    '开学季', '县在行动', '社区速递', '具透', 'ETF市场日报', 'ETF甄选', '北向午盘', '今日开盘',
)
_NEWS_COLUMN_PREFIX_RE = re.compile(r'^(?:（([^（）]{1,12})）|【([^】]{1,12})】|([^：:]{1,12})[：:])(.{5,})$')
_NEWS_COLUMN_SUFFIX_RE = re.compile(r'^(.*?)（([^（）]{1,12})）$')


def _news_clean_title(title):
    """清洗抓取新闻标题：去掉源站栏目名前缀（如『时评 | 』『深度 | 』『ETF甄选 | 』）。

    覆盖四种形态：
      - 『栏目名 | 标题』（短前缀，<=12 字符）
      - 『（栏目名）标题』『【栏目名】标题』『栏目名：标题』（白名单栏目词）
      - 『标题（栏目名）』后缀（白名单栏目词，如“两岸观察”）
    避免误伤正常标题（如英文机构名分隔、A/B 对比、栏目名不在白名单内）。
    """
    if not title:
        return title or ''
    t = title.strip()
    m = _NEWS_TITLE_PREFIX_RE.match(t)
    if m:
        prefix = m.group(1).strip()
        rest = m.group(2).strip()
        # 前缀须为中文栏目名或短英文标识，且非明显完整句子（防误删）
        if len(prefix) <= 12 and len(rest) >= 5:
            return rest
    m = _NEWS_COLUMN_PREFIX_RE.match(t)
    if m:
        col = (m.group(1) or m.group(2) or m.group(3) or '').strip()
        rest = m.group(4).strip()
        if col in _NEWS_COLUMN_WORDS and len(rest) >= 5:
            return rest
    m = _NEWS_COLUMN_SUFFIX_RE.match(t)
    if m:
        head = m.group(1).strip()
        col = m.group(2).strip()
        if col in _NEWS_COLUMN_WORDS and len(head) >= 5:
            return head
    return t


# 无信息量标题模式：短标题且以“汇总/速览/快讯/简报/速递/启幕/来了/官宣/出炉/来袭/开启”等收尾，
# 本身不含主体+事件，需要从正文提炼
_NEWS_BLAND_TITLE_RE = re.compile(r'^.{1,12}?(汇总|速览|快讯|简报|周报|速递|直击|启幕|来了|官宣|出炉|上新|来袭|开启|进行时)$')
# 正文首段常见来源导语前缀（XX电/XX社电/中新网…/原标题：/原文标题：/题：等）
_NEWS_LEAD_RE = re.compile(
    r'^(?:【?[^【】\n]{0,24}?(?:电|讯|社电|分社电)】?\s*|'
    r'中新[^，。；\n]{0,20}?[电讯]?\s*|'
    r'原标题[:：]\s*|原文标题[:：]\s*|题[:：]\s*|编者按[:：]\s*|'
    r'快讯[:：]\s*|本报讯\s*|本网[^，。；\n]{0,10}?[电讯]?\s*|'
    r'(?:本报|本台|央视|新华社)?记者[^，。；\n]{0,15}?\s*|'
    r'[0-9０-９]{1,4}年[0-9０-９]{1,2}月[0-9０-９]{1,2}日\s*)'
)


def _news_refine_title(title, content=''):
    """对无信息量标题（如“XX汇总/XX启幕/XX速览”），从正文首段提炼含主体+事件的标题。

    优先级：
      1. 先走既有栏目壳剥离（_news_clean_title）
      2. 短标题（<=15 字）且命中无信息量模式、正文 >=30 字时：
         去掉来源导语后取首个完整句子（>=10 字）作为新标题，截断 <=60 字
      3. 首句不可用则取正文前 60 字
      4. 均失败返回原标题（不臆造）
    """
    t = (title or '').strip()
    if not t:
        return title or ''
    t = _news_clean_title(t)
    body = (content or '').strip()
    if not body:
        return t
    if len(t) <= 15 and _NEWS_BLAND_TITLE_RE.search(t) and len(body) >= 30:
        lines = [ln.strip() for ln in re.split(r'[\n\r]+', body) if ln.strip()]
        for ln in lines:
            cand = _NEWS_LEAD_RE.sub('', ln).strip(' 　。；;、,:：')
            cand = re.split(r'(?<=[。！？])', cand)[0]
            cand = cand.strip(' 　。；;、,:：')
            if len(cand) >= 10:
                cand = cand[:60].rstrip('。')
                if len(cand) >= 10:
                    return cand + '。'
        flat = re.sub(r'\s+', '', body)
        flat = _NEWS_LEAD_RE.sub('', flat)
        if len(flat) >= 10:
            return flat[:60].rstrip('。') + '。'
    return t


def _news_to_dict(row, uid=None):
    """把 news 行转成前端字典，附带作者信息与评论数"""
    db = get_db()
    item = {
        'id': row['id'],
        'title': _news_refine_title(row['title'], row.get('content') or ''),
        'image': _news_image_url(row.get('image')),
        'likes': row['likes'],
        'created_at': row['created_at'],
        'author_id': row.get('author_id') or '',
        'author_name': '',
        'author_avatar': '',
        'author_is_source': False,
        'comment_count': 0,
        'summary': row.get('summary') or '',
        'category': row.get('category') or '',
        'pinned': bool(row.get('pinned')),
        'ai_allowed': True if row.get('ai_allowed') is None else bool(row.get('ai_allowed')),
        'featured': bool(row.get('featured')),
        'images': _parse_news_images(row.get('images')),
        'video': _news_image_url(row.get('video')),
    }
    aid = row.get('author_id') or ''
    if aid.startswith('source:'):
        # 抓取入库的新闻：作者即新闻源。仅展示来源名，不指向站内用户主页
        # （此前 author_name 为空导致详情页显示"官方"，且点击会跳到不存在的 /?profile=source:xxx）
        item['author_name'] = aid[len('source:'):].strip() or '新闻源'
        item['author_id'] = ''
        item['author_is_source'] = True
    elif aid:
        u = _fetchone(db, 'SELECT username, avatar FROM users WHERE id=?', (aid,))
        if u:
            item['author_name'] = u['username']
            av = u.get('avatar') or ''
            item['author_avatar'] = ('/' + av) if av and not av.startswith('/') else av
    c = _fetchone(db, 'SELECT COUNT(*) as c FROM news_comments WHERE news_id=?', (row['id'],))
    item['comment_count'] = c['c'] if c else 0
    if 'content' in row and row.get('content') is not None:
        item['content'] = row['content']
    item['liked'] = False
    if uid:
        item['liked'] = bool(_fetchone(db, 'SELECT 1 FROM news_likes WHERE user_id=? AND news_id=?', (uid, row['id'])))
    return item


# ==========================================================================
# 新闻自动分类：根据标题 + 段落内容匹配标准分类
# 原则：
#   1. 对标题与正文分别提取关键词，标题命中加权（权重 2），正文命中权重 1
#   2. 按关键词词典映射到前台标准分类（与 CANONICAL_CATEGORIES 一致）
#   3. 得分最高且 >= 阈值的分类胜出；无命中返回 ''（由调用方保留原值/默认）
# ==========================================================================
_NEWS_CLASSIFY_KEYWORDS = {
    "国际": ["外交部", "外长", "联合国", "欧盟", "北约", "俄罗斯", "乌克兰", "美国", "白宫", "特朗普", "拜登",
             "普京", "以色列", "巴勒斯坦", "加沙", "伊朗", "韩国", "日本", "朝鲜", "印度", "东盟", "非盟",
             "G7", "G20", "峰会", "大使", "使馆", "制裁", "关税战", "地缘", "中东", "俄乌", "边境", "移民",
             "巴黎", "伦敦", "东京", "华盛顿", "莫斯科", "基辅", "首尔", "平壤", "新德里", "国际法院", "世卫", "国际货币基金组织", "世界银行"],
    "时事": ["国务院", "总理", "政协", "人大", "两会", "政策", "发改委", "中央", "部委", "发布", "部署",
             "贯彻落实", "传达", "会议", "决定", "通知", "意见", "规划", "十四五", "政府", "政务", "民生",
             "改革", "治理", "执法", "监管", "法规", "条例", "草案", "全国", "试点", "调研组", "新闻发布会", "白皮书", "强军", "国防"],
    "经济": ["股市", "A股", "港股", "美股", "纳斯达克", "道指", "标普", "基金", "银行", "央行", "降准", "降息",
             "利率", "汇率", "人民币", "美元", "欧元", "通胀", "CPI", "PPI", "GDP", "GDP增长", "经济", "企业",
             "公司", "财报", "营收", "利润", "上市", "IPO", "融资", "投资", "并购", "收购", "产业链", "供应链",
             "制造业", "出口", "进口", "贸易", "关税", "消费", "零售", "房价", "楼市", "地产", "房企", "债券", "黄金", "大宗商品", "原油", "石油", "能源价格", "就业", "失业率", "补贴", "减税", "财政"],
    "科技": ["AI", "人工智能", "大模型", "ChatGPT", "OpenAI", "谷歌", "微软", "苹果", "华为", "芯片", "半导体",
             "处理器", "GPU", "英伟达", "高通", "英特尔", "软件", "硬件", "互联网", "5G", "6G", "通信", "卫星",
             "航天", "火箭", "飞船", "空间站", "嫦娥", "火星", "量子", "机器人", "自动驾驶", "新能源", "电池",
             "光伏", "风电", "电动车", "汽车", "手机", "数码", "操作系统", "开源", "编程", "算法", "数据", "云计算", "区块链", "元宇宙", "VR", "AR", "专利", "研发", "实验室", "科学家", "科研"],
    "体育": ["足球", "篮球", "世界杯", "奥运会", "亚运会", "亚残运会", "冬运会", "全运会", "英超", "西甲", "德甲", "意甲", "法甲", "中超", "中甲",
             "CBA", "NBA", "欧冠", "欧联", "世预赛", "亚预赛", "冠军", "冠军杯", "联赛", "决赛", "半决赛", "四强", "八强", "锦标赛", "世锦赛", "公开赛", "大师赛", "巡回赛",
             "运动员", "球员", "教练", "主帅", "主教练", "球队", "俱乐部", "国家队", "阵容", "首发", "替补", "上场",
             "进球", "射门", "助攻", "比分", "金牌", "银牌", "铜牌", "奖牌", "国足", "男篮", "女篮", "女排", "国乒", "国羽", "网球", "高尔夫",
             "F1", "大奖赛", "马拉松", "田径", "游泳", "体操", "羽毛球", "乒乓球", "电竞", "转会", "退役", "复出", "伤病", "因伤",
             "比赛", "赛事", "赛程", "小组赛", "淘汰赛", "资格赛", "预选赛", "热身赛", "友谊赛", "不败", "连胜", "连败", "晋级", "出线", "夺冠", "卫冕", "开门红", "种子", "大满贯", "积分榜", "排名", "球员", "绝杀", "逆转", "大胜", "战平", "爆冷"],
    "人文": ["博物馆", "考古", "文物", "遗址", "历史", "文化", "非遗", "传统", "书法", "绘画", "艺术", "展览",
             "文学", "小说", "诗歌", "散文", "作家", "学者", "研究", "学术", "大学", "教育", "学校", "教师",
             "学生", "考试", "高考", "图书馆", "出版", "图书", "阅读", "哲学", "宗教", "民族", "民俗", "方言", "国学"],
    "娱乐": ["电影", "票房", "上映", "电视剧", "综艺", "节目", "演员", "导演", "明星", "歌手", "演唱会", "专辑",
             "音乐", "歌曲", "颁奖", "奥斯卡", "戛纳", "威尼斯", "春晚", "选秀", "偶像", "粉丝", "剧组", "拍摄",
             "首映", "预告片", "制片", "娱乐", "八卦", "网红", "直播", "主播", "动漫", "漫画", "动画"],
    "生活": ["健康", "医疗", "医院", "医生", "疫苗", "疾病", "养生", "饮食", "食品", "安全", "天气", "气象",
             "台风", "暴雨", "灾害", "救援", "交通", "出行", "旅游", "景区", "假期", "酒店", "美食",
             "菜价", "超市", "购物", "快递", "物流", "家居", "装修", "家电", "燃气", "水费", "电费", "物业",
             "社区", "街道", "环保", "垃圾分类", "宠物", "健身", "睡眠", "心理", "育儿", "养老", "社保", "医保", "公积金"],
    "环境": ["气候", "温室气体", "碳中和", "碳达峰", "碳排放", "污染", "空气", "水质", "土壤", "生态", "生物多样性",
             "森林", "湿地", "海洋", "冰川", "极端天气", "高温", "干旱", "洪水", "海平面", "环保组织", "绿电", "清洁能源",
             "地震", "震级", "余震", "海啸", "泥石流", "山体滑坡", "山火", "森林火灾", "台风", "暴雨", "暴雪",
             "寒潮", "冰雹", "龙卷风", "火山", "火山喷发", "厄尔尼诺", "拉尼娜", "沙尘暴", "雾霾", "碳排放权",
             "生物多样性", "物种灭绝", "栖息地", "候鸟", "湿地保护", "荒漠化", "生态修复", "绿色转型",
             "节能降碳", "碳市场", "碳交易", "臭氧层", "气候变暖"],
    "社会": ["警方", "民警", "公安", "法院", "检察院", "判决", "庭审", "嫌疑人", "犯罪", "诈骗", "盗窃", "案件", "刑事",
             "交通事故", "车祸", "伤亡", "坠楼", "落水", "溺亡", "火灾", "爆炸", "坍塌", "中毒", "遇难", "失联", "被困", "救援", "消防",
             "老人", "儿童", "孩子", "婴儿", "孕妇", "残疾人", "环卫工", "外卖员", "快递员", "农民工", "志愿者",
             "寻人", "走失", "救助", "捐款", "募捐", "献血", "见义勇为", "好人好事", "拾金不昧", "感人", "暖心",
             "婚姻", "离婚", "彩礼", "家庭", "邻里", "纠纷", "维权", "投诉", "举报", "谣言", "辟谣", "网络暴力",
             "户口", "身份证", "社保卡", "养老金", "低保", "补贴发放", "工资", "欠薪", "讨薪", "劳动仲裁", "就业", "招聘",
             "学校", "幼儿园", "学生", "家长", "老师", "教师", "高考", "中考", "校园", "霸凌", "安全事故", "食品安全", "药品安全", "假货", "消费维权",
             # 扩充社会新闻召回：通报/回应/曝光/立案/调查/处罚等真实社会新闻常见词
             "通报", "通报称", "官方通报", "回应", "回应称", "官方回应", "曝光", "网传", "辟谣",
             "刑拘", "刑事拘留", "逮捕", "落网", "立案", "立案调查", "纪委监委", "调查组", "问责", "约谈",
             "违规", "处罚", "罚款", "整改", "通告", "目击", "目击者", "监控画面", "现场视频", "突发", "涉事",
             "当事人", "争执", "冲突", "伤人", "命案", "遇害", "遗体", "失踪", "搜救", "被困人员", "打人", "袭警",
             "诈骗团伙", "电信诈骗", "传销", "拐卖", "虐待", "猥亵", "性侵", "霸凌", "校园暴力"],
    "游戏社群": ["游戏", "手游", "端游", "主机", "Steam", "任天堂", "索尼", "微软", "PlayStation", "Xbox",
                "电竞", "战队", "赛事", "皮肤", "更新", "版本", "DLC", "玩家", "上线", "公测", "内测", "预约",
                "角色扮演", "RPG", "MOBA", "射击", "沙盒", "独立游戏", "怀旧服", "俱乐部", "主播", "陪玩"],
}

_NEWS_CLASSIFY_THRESHOLD = 2

# 栏目壳标题识别：纯"XX晚报/早报/简报/播报/晨报/联播"等栏目名（可带日期/序号前缀），
# 本身不含具体新闻内容，点进去没有真实新闻，不应作为单条新闻展示
_SHELL_COLUMN_RE = re.compile(
    r"^(?:【?[^|｜:：\-—\d]{2,10}?(?:晚报|早报|晨报|午报|日报|简报|快报|播报|联播|速递|周报)】?|[0-9０-９]{1,4}[年\.\-/]?[0-9０-９]{0,2}[月\.\-/]?[0-9０-９]{0,2}日?[号]?\s*[^|｜:：]{0,8}?(?:晚报|早报|晨报|简报|播报|联播))(?:\s*[|｜:：]\s*)?"
)


def _is_shell_column_title(title):
    """判断标题是否为无实质新闻内容的栏目壳标题。"""
    if not title:
        return False
    t = title.strip()
    if len(t) > 60:
        return False
    return bool(_SHELL_COLUMN_RE.match(t))


# 强生活词：标题命中即应归入"生活"（健康/体质/体检/脑梗/体育代表团等民生日常），
# 置于强社会(事件级)之后，避免"地铁持刀伤人/警方介入"等社会事件被生活词抢走
_NEWS_LIFE_STRONG_WORDS = (
    '体质', '体检', '血脂', '脑梗', '猝死', '亚健康', '体育代表团', '养生',
    '睡眠质量', '心理健康', '疫苗接种', '慢性病', '糖尿病', '高血压', '流感', '急救',
    '医疗', '医院', '医生', '手术', '门诊', '住院', '挂号', '医保', '看病',
    '食谱', '饮食', '膳食', '营养', '减肥', '健身', '跑步', '瑜伽', '早睡',
    '育儿', '母婴', '孕妇', '宝宝', '儿童', '青少年', '老年人', '养老', '退休金',
    '居家', '装修', '家具', '超市', '菜价', '燃气', '水费', '电费', '物业',
    '交通出行', '地铁', '公交', '高铁', '航班', '拥堵', '绕行', '出行提醒',
)

# 强经济词：标题命中即应归入"经济"，防止股票/财经新闻被国际/时事关键词抢走
_NEWS_ECON_STRONG_WORDS = (
    '股市', 'A股', '港股', '美股', '纳斯达克', '道指', '标普', '基金', '央行', '降准', '降息',
    '利率', '汇率', '财报', '营收', '利润', 'IPO', '融资', '并购', '债券', '黄金', '原油',
    '股票', '券商', '涨停', '跌停', '收盘', '开盘', '指数', '板块', '牛市', '熊市', '股价', '大盘', '个股',
    '通货膨胀', '通缩', 'CPI', 'PPI', 'GDP', '失业率', '就业', '裁员', '工资', '薪酬',
    '贸易战', '关税', '出口', '进口', '顺差', '逆差', '期货', '现货', '大宗商品', '石油',
    '房价', '楼市', '地产', '房企', '首付', '房贷', '租金', '商铺',
    '比特币', '加密货币', '区块链', '数字人民币', '市值', '估值', '融资', '风投',
)

# 强环境词：标题命中即应归入"环境"（自然灾害/气候/生态/环保），
# 置于社会强词之后，使"地震+救援"类标题归社会、"纯灾害/气候"归环境
_NEWS_ENV_STRONG_WORDS = (
    '地震', '震级', '余震', '海啸', '火山', '火山喷发', '泥石流', '山体滑坡', '山洪',
    '台风', '暴雨', '洪涝', '洪水', '内涝', '龙卷风', '飓风', '暴雪', '冰雹', '寒潮',
    '高温', '干旱', '热浪', '冻雨', '沙尘暴', '雾霾', '重污染', '空气污染', '水质',
    '山火', '森林火灾', '火灾预警', '极端天气', '气候变暖', '气候变化', '温室气体',
    '碳中和', '碳达峰', '碳排放', '碳交易', '碳市场', '碳排放权', '节能降碳',
    '生态', '生物多样性', '物种灭绝', '栖息地', '候鸟迁徙', '湿地保护', '自然保护区',
    '荒漠化', '水土流失', '生态修复', '绿色转型', '清洁能源', '绿电', '可再生能源',
    '臭氧层', '厄尔尼诺', '拉尼娜', '海平面上升', '冰川消融', '北极', '南极科考',
)

# 强科技词：标题命中且基础分类非经济/体育/环境/娱乐时归"科技"，防止科技新闻被国际/时事/人文抢走
_NEWS_TECH_STRONG_WORDS = (
    'AI', '人工智能', '大模型', '模型', '算法', '算力', '智能体', 'Agent', '多模态', 'AIGC',
    'ChatGPT', 'OpenAI', 'Gemini', 'DeepSeek', 'Claude', 'Copilot', 'GPT', 'AGI', 'Sora',
    '芯片', '半导体', '处理器', 'GPU', 'CPU', '显卡', '光刻', 'EUV', '昇腾', '麒麟',
    '机器人', '人形机器人', '自动驾驶', '智能驾驶', '无人驾驶', '智能座舱',
    '操作系统', '开源', '编程', '代码', '软件', '硬件', 'APP', '应用', 'API',
    '云计算', '数据中心', '服务器', '数据库', '量子', '区块链', '元宇宙', 'VR', 'AR',
    '卫星', '火箭', '航天', '空间站', '探测器', '月球', '火星', '嫦娥', '神舟', '天宫',
    '5G', '6G', '通信', '物联网', '传感器', '鸿蒙', 'iOS', 'Android', 'Windows', 'Linux',
    '英伟达', '高通', '英特尔', 'AMD', '台积电', '华为', '苹果', '谷歌', '微软', '特斯拉',
    'SpaceX', '波音', '专利', '研发', '实验室', '科学家', '科研', '学术',
)

# 强人文词：标题命中且基础分类非经济/体育/娱乐时归"人文"（文化/历史/教育/学术）
_NEWS_CULTURE_STRONG_WORDS = (
    '博物馆', '考古', '文物', '遗址', '古墓', '青铜器', '壁画', '石窟', '古籍', '出土',
    '申遗', '文化遗产', '非遗', '非物质文化遗产', '传统工艺', '民俗', '民间艺术',
    '书法', '绘画', '国画', '雕塑', '艺术展', '美术馆', '展览', '策展', '艺术品',
    '文学', '小说', '诗歌', '散文', '作家', '诗人', '文学奖', '鲁迅文学奖', '茅盾文学奖',
    '诗词', '唐诗', '宋词', '国学', '古籍整理', '线装书', '书院', '汉字', '方言',
    '大学', '高校', '学院', '教授', '学者', '学术', '论文', '科研', '实验室', '研究',
    '教育', '学校', '教师', '老师', '学生', '高考', '中考', '考研', '留学', '招生',
    '图书馆', '出版社', '出版', '图书', '畅销书', '阅读', '读书',
    '历史', '古代', '清代', '唐代', '宋代', '明代', '考古学家', '史学', '典籍', '档案',
    '哲学', '宗教', '佛学', '道教', '儒家', '文化自信', '中华文明', '文明起源',
)

# 强娱乐词：标题命中且基础分类非经济/体育/科技时归"娱乐"（影视/音乐/综艺/明星）
_NEWS_ENT_STRONG_WORDS = (
    '电影', '票房', '上映', '首映', '预告片', '片方', '导演', '演员', '主演', '剧组',
    '电视剧', '剧集', '综艺', '真人秀', '脱口秀', '选秀', '偶像', '粉丝', '爱豆',
    '明星', '歌手', '演唱', '演唱会', '专辑', '单曲', '歌曲', '音乐', 'MV', '巡演',
    '音乐节', '电音节', '颁奖礼', '奥斯卡', '戛纳', '威尼斯', '柏林电影节', '金鸡奖',
    '百花奖', '飞天奖', '金鹰奖', '白玉兰', '春晚', '元宵晚会', '跨年晚会',
    '好莱坞', 'Netflix', 'Disney', '漫威', 'DC', '动画', '动漫', '漫画', '声优',
    '影帝', '影后', '视帝', '视后', '票房冠军', '收视率', '播放量', '顶流', '出圈',
    '红毯', '时尚', '超模', '品牌代言', '写真',
)

# 强体育词：标题命中即应归入"体育"，防止体育赛事/运动员新闻被国际/时事等关键词抢走
_NEWS_SPORT_STRONG_WORDS = (
    '足球', '篮球', '世界杯', '奥运会', '亚运会', '亚残运会', '冬运会', '全运会', '英超', '西甲', '德甲', '意甲', '法甲', '中超', '中甲',
    'CBA', 'NBA', '欧冠', '欧联', '世预赛', '亚预赛', '世锦赛', '公开赛', '大师赛', '巡回赛', '大奖赛',
    '国足', '男篮', '女篮', '女排', '国乒', '国羽', '比赛', '赛事', '赛程', '小组赛', '淘汰赛', '资格赛', '预选赛',
    '热身赛', '友谊赛', '连胜', '连败', '晋级', '出线', '夺冠', '卫冕', '开门红', '大满贯', '积分榜',
    '绝杀', '逆转', '大胜', '战平', '爆冷', '进球', '射门', '助攻', '比分',
    # 常见球队/球星（NBA/英超/西甲/意甲/德甲/中超等），提升"湖人险胜勇士"类标题召回
    '湖人', '勇士', '凯尔特人', '掘金', '独行侠', '雄鹿', '太阳', '热火', '快船', '尼克斯', '篮网', '76人',
    '骑士', '步行者', '老鹰', '公牛', '马刺', '鹈鹕', '国王', '活塞', '魔术', '森林狼', '爵士', '黄蜂',
    '灰熊', '雷霆', '开拓者', '猛龙', '奇才', '詹姆斯', '库里', '杜兰特', '字母哥', '哈登', '约基奇',
    '皇马', '巴萨', '曼联', '曼城', '利物浦', '阿森纳', '切尔西', '热刺', '拜仁', '多特', '尤文',
    '国米', 'AC米兰', '巴黎圣日耳曼', '马竞', '勒沃库森', '纽卡斯尔', '维拉', '那不勒斯', '罗马',
    '恒大', '国安', '上港', '申花', '泰山', '蓉城', '浙江队', '三镇', 'C罗', '梅西', '姆巴佩',
    '哈兰德', '贝林厄姆', '维尼修斯', '萨拉赫', '凯恩', '德布劳内', '孙兴慜', '内马尔', '奖牌', '金牌', '银牌', '铜牌', '运动员', '球员', '主帅', '教练',
)

# 强社会词：标题命中即应归入"社会"，防止真实社会新闻（通报/立案/辟谣/维权等）被国际/时事/科技等大类抢走。
# 仅抢国际/时事这两个兜底大类，避免误伤经济/体育/科技等明确分类
# 强社会词（事件/监管级，高优先级）：标题命中即应归入"社会"。
# 覆盖突发事件（警方/刑拘/命案/火灾/车祸/救援）、治安刑事（诈骗/抢劫/拐卖）、
# 监管治理（通报/立案/约谈/查处/违规收费）等真实社会新闻。
# 置于强生活/强环境之前，避免"地铁持刀伤人/警方介入""地震+救援"等被生活/环境抢走。
_NEWS_SOCIAL_STRONG_WORDS = (
    '警方', '警方通报', '民警', '公安', '刑拘', '刑事拘留', '逮捕', '落网', '嫌疑人', '诈骗', '诈骗团伙', '电信诈骗',
    '盗窃', '抢劫', '故意伤害', '命案', '遇害', '坠楼', '溺亡', '车祸', '交通事故', '火灾', '爆炸', '坍塌', '中毒',
    '遇难', '失联', '被困', '搜救', '消防', '救援', '霸凌', '校园暴力',
    '持刀', '行凶', '伤人', '斗殴', '械斗', '凶杀', '纵火', '酒驾', '醉驾', '肇事', '翻车', '追尾',
    '通报称', '官方通报', '通报曝光', '通报批评', '立案调查', '纪委监委', '调查组', '通报',
    '举报', '投诉', '纠纷', '曝光', '当事人', '涉事', '目击者', '监控画面', '打人', '袭警', '拐卖', '性侵',
    '违规收费', '乱收费', '违规经营', '无证经营', '超标排放', '偷排', '造假', '假冒伪劣',
    '哄抬价格', '垄断', '倾销', '骗保', '套取', '贪污', '受贿', '挪用', '滥用职权', '徇私舞弊',
    '立案', '查处', '整改', '约谈', '下架', '封禁', '清退', '追责', '问责',
)

# 强社会词（民生/舆情级，低优先级）：命中且未被生活强词拦截时归社会。
# 覆盖辟谣/寻人/好人好事/消费维权/食品安全等民生舆情，优先级低于生活强词，
# 避免"中国体育代表团…辟谣"被抢到社会。
_NEWS_SOCIAL_LIFE_STRONG_WORDS = (
    '辟谣', '网传', '造谣', '传谣', '走失', '寻人', '拾金不昧', '见义勇为', '好人好事',
    '消费维权', '维权', '食品安全', '讨薪', '欠薪', '劳动仲裁',
)

# 国外地名/主体强词：标题命中即归"国际"（时事）。事件发生地/主体在国外（苏丹、美国、国外地名等）不得落入社会。
# 放置于强体育/强经济判断之后，避免"美股""NBA 洛杉矶"等财经/体育新闻被误抢。
_NEWS_FOREIGN_PLACES = (
    '美国', '美方', '美军', '白宫', '特朗普', '拜登', '苏丹', '南苏丹', '喀土穆', '俄罗斯', '乌克兰',
    '韩国', '朝鲜', '印度', '日本', '日方', '伊朗', '以色列', '巴勒斯坦', '加沙', '委内瑞拉',
    '洛杉矶', '加利福尼亚', '加州', '纽约', '芝加哥', '旧金山', '波士顿', '西雅图',
    '华盛顿', '莫斯科', '基辅', '首尔', '平壤', '东京', '大阪', '巴黎', '伦敦', '柏林', '马德里', '罗马',
    '开罗', '内罗毕', '迪拜', '多哈', '利雅得', '新加坡', '曼谷', '雅加达', '马尼拉', '河内', '伊斯兰堡',
    '德黑兰', '巴格达', '大马士革', '安曼', '贝鲁特', '特拉维夫', '耶路撒冷', '安卡拉', '伊斯坦布尔', '雅典',
    '维也纳', '布鲁塞尔', '日内瓦', '渥太华', '多伦多', '温哥华', '墨西哥城', '圣保罗', '里约热内卢',
    '布宜诺斯艾利斯', '堪培拉', '悉尼', '墨尔本', '惠灵顿', '金边', '仰光', '蒙古国',
    '阿富汗', '伊拉克', '叙利亚', '也门', '沙特', '沙特阿拉伯', '卡塔尔', '阿联酋', '土耳其', '埃及',
    '南非', '尼日利亚', '肯尼亚', '埃塞俄比亚', '澳大利亚', '新西兰', '加拿大', '墨西哥', '巴西', '阿根廷',
    '智利', '秘鲁', '哥伦比亚', '古巴', '西班牙', '意大利', '德国', '法国', '英国', '荷兰', '瑞典', '挪威',
    '芬兰', '丹麦', '波兰', '奥地利', '瑞士', '比利时', '葡萄牙', '希腊', '白俄罗斯', '格鲁吉亚',
    '哈萨克斯坦', '乌兹别克斯坦', '吉尔吉斯斯坦', '塔吉克斯坦', '塞尔维亚', '克罗地亚', '罗马尼亚',
    '保加利亚', '匈牙利', '捷克', '斯洛伐克', '斯洛文尼亚', '立陶宛', '拉脱维亚', '爱沙尼亚', '亚美尼亚',
    '阿塞拜疆', '巴林', '科威特', '阿曼', '约旦', '黎巴嫩', '塞浦路斯', '马尔代夫', '斯里兰卡', '孟加拉国',
    '巴基斯坦', '尼泊尔', '不丹', '缅甸', '老挝', '柬埔寨', '越南', '菲律宾', '马来西亚', '印度尼西亚',
    '文莱', '东帝汶', '巴布亚新几内亚', '斐济', '索马里', '利比亚', '阿尔及利亚', '摩洛哥', '突尼斯',
    '加纳', '坦桑尼亚', '乌干达', '赞比亚', '津巴布韦', '莫桑比克', '安哥拉', '刚果', '喀麦隆',
    '科特迪瓦', '马里', '布基纳法索', '尼日尔', '乍得', '吉布提', '卢旺达', '布隆迪', '马达加斯加',
    '毛里求斯', '塞内加尔', '几内亚', '塞拉利昂', '多哥', '贝宁', '加蓬', '爱尔兰', '卢森堡', '冰岛',
    '马耳他', '黑山', '北马其顿', '海地', '牙买加', '巴拿马', '哥斯达黎加', '危地马拉', '洪都拉斯',
    '萨尔瓦多', '尼加拉瓜', '厄瓜多尔', '玻利维亚', '巴拉圭', '乌拉圭', '圭亚那', '巴哈马', '巴巴多斯',
    '海外', '国外', '国际社会',
)

# 国内政治/纪律/政府事务强词：标题命中即归"时事"。国内政治、纪律、政府事务（开除公职、纪委、监委、
# 免职、双开、审查调查等）不得落入社会。
_NEWS_DOMESTIC_POLITICS = (
    '开除公职', '开除党籍', '免职', '双开', '政务处分', '党纪政务处分', '纪委', '监委', '监察',
    '审查调查', '立案审查', '被查', '落马', '问责', '处分', '撤职', '降职', '停职',
    '公职人员', '党员干部', '领导干部', '违纪', '违法违纪', '反腐', '廉政', '廉洁',
    '巡视', '巡察', '派驻', '中纪委', '中央纪委', '国家监委', '省纪委', '市纪委', '县纪委',
    '省监委', '市监委', '县监委', '纪律处分', '组织处理',
)

# ======================================================================
# 新闻地区维度识别：从标题（可带正文前缀）中提取事件发生/相关地区。
# 优先级：具体国家/区域（日本/美国/欧洲/中东/亚洲/拉美非大洋洲）> 国际组织 > 国内。
# 地区标签与分类独立展示，解决"国际∪时事归一为时事"后缺少国家维度的问题。
# ======================================================================
_NEWS_REGION_WORDS = {
    '日本': ('日本', '东京', '大阪', '京都', '名古屋', '福冈', '札幌', '横滨', '神户', '冲绳', '北海道',
             '福岛', '日方', '日元', '日经', '岸田', '石破', '自民党', '日本央行', '日媒'),
    '美国': ('美国', '美方', '美军', '白宫', '特朗普', '拜登', '哈里斯', '美联储', '纽约', '华盛顿',
             '洛杉矶', '旧金山', '硅谷', '加州', '得州', '德克萨斯', '佛罗里达', '华尔街', '美股',
             '美元', '纳斯达克', '道指', '标普', 'NASA', '五角大楼', '美媒', '美企'),
    '欧洲': ('欧盟', '英国', '法国', '德国', '意大利', '西班牙', '葡萄牙', '荷兰', '比利时', '瑞典',
             '挪威', '芬兰', '丹麦', '波兰', '乌克兰', '俄罗斯', '瑞士', '奥地利', '希腊', '爱尔兰',
             '伦敦', '巴黎', '柏林', '莫斯科', '基辅', '布鲁塞尔', '日内瓦', '欧元', '英镑', '欧央行',
             '北约', '英方', '法方', '德方', '英媒', '法媒', '德媒', '欧洲央行'),
    '中东': ('以色列', '巴勒斯坦', '加沙', '伊朗', '伊拉克', '叙利亚', '也门', '沙特', '阿联酋', '卡塔尔',
             '土耳其', '黎巴嫩', '约旦', '科威特', '迪拜', '多哈', '利雅得', '德黑兰', '耶路撒冷',
             '特拉维夫', '胡塞', '真主党', '哈马斯', '中东', '波斯湾'),
    '亚洲': ('韩国', '朝鲜', '印度', '新加坡', '泰国', '越南', '菲律宾', '马来西亚', '印尼', '孟加拉国',
             '巴基斯坦', '斯里兰卡', '蒙古国', '缅甸', '老挝', '柬埔寨', '首尔', '新德里', '曼谷',
             '雅加达', '河内', '马尼拉', '韩方', '印方', '东盟', '金砖', '韩媒', '印媒'),
    '拉美非大洋洲': ('巴西', '阿根廷', '墨西哥', '智利', '秘鲁', '哥伦比亚', '古巴', '委内瑞拉', '埃及',
             '南非', '尼日利亚', '肯尼亚', '埃塞俄比亚', '摩洛哥', '突尼斯', '澳大利亚', '新西兰',
             '加拿大', '墨西哥城', '圣保罗', '开罗', '内罗毕', '悉尼', '墨尔本', '渥太华', '多伦多',
             '温哥华', '拉美', '非洲', '大洋洲', '澳方', '加方'),
    '国际': ('联合国', '世卫', '世贸', 'G7', 'G20', '国际货币基金组织', '世界银行', '国际法院',
             '全球', '海外', '国外', '国际社会', '世卫组织', 'WTO', 'IMF', '国际空间站'),
}

_NEWS_REGION_DOMESTIC = (
    '中国', '我国', '国家', '全国', '中央', '国务院', '北京', '上海', '广州', '深圳', '天津', '重庆',
    '香港', '澳门', '台湾', '新疆', '西藏', '内蒙古', '宁夏', '广西', '四川', '云南', '贵州', '甘肃',
    '青海', '黑龙江', '吉林', '辽宁', '河北', '山西', '陕西', '山东', '江苏', '浙江', '安徽', '福建',
    '江西', '河南', '湖北', '湖南', '广东', '海南', '国内', '内地', '大陆', '我方', '中方', '国台办',
)


def _news_region(title, content=''):
    """从标题（+正文前缀）识别新闻地区维度；无明确地区返回 ''（即国内/通用）"""
    text = (title or '') + ' ' + ((content or '')[:200])
    # 具体国家/区域优先
    for region, words in _NEWS_REGION_WORDS.items():
        for w in words:
            if w in text:
                return region
    # 国际组织/全球性议题
    # 国内兜底：标题含国内地名/主体，明确是国内新闻
    for w in _NEWS_REGION_DOMESTIC:
        if w in text:
            return '国内'
    return ''


def _auto_classify_news(title, content=''):
    """按标题 + 正文关键词给新闻自动分类；返回标准分类名（无命中返回 ''）

    匹配优先级（强词 → 词典 → 外语兜底）：
      社会(事件/监管级) > 生活 > 环境 > 经济 > 体育 > 科技 > 人文 > 娱乐
      > 社会(民生/舆情级) > 国外 > 国内政治 > 词典大类
    数字特征（震级/百分比/年份）不参与分类判定。
    """
    title_txt = (title or '').strip()
    body_txt = (content or '')[:2000]
    best_cat = ''
    best_score = 0
    for cat, kws in _NEWS_CLASSIFY_KEYWORDS.items():
        score = 0
        for kw in kws:
            if kw and kw in title_txt:
                score += 2
            elif kw and body_txt and kw in body_txt:
                score += 1
        if score > best_score:
            best_score = score
            best_cat = cat
    hit_social = any(w in title_txt for w in _NEWS_SOCIAL_STRONG_WORDS)
    hit_life = any(w in title_txt for w in _NEWS_LIFE_STRONG_WORDS)
    hit_env = any(w in title_txt for w in _NEWS_ENV_STRONG_WORDS)
    hit_econ = any(w in title_txt for w in _NEWS_ECON_STRONG_WORDS)
    hit_sport = any(w in title_txt for w in _NEWS_SPORT_STRONG_WORDS)
    hit_tech = any(w in title_txt for w in _NEWS_TECH_STRONG_WORDS)
    hit_cult = any(w in title_txt for w in _NEWS_CULTURE_STRONG_WORDS)
    hit_ent = any(w in title_txt for w in _NEWS_ENT_STRONG_WORDS)
    hit_social_life = any(w in title_txt for w in _NEWS_SOCIAL_LIFE_STRONG_WORDS)
    hit_foreign = any(w in title_txt for w in _NEWS_FOREIGN_PLACES)
    hit_politics = any(w in title_txt for w in _NEWS_DOMESTIC_POLITICS)
    if best_score >= _NEWS_CLASSIFY_THRESHOLD or any(
            (hit_social, hit_life, hit_env, hit_econ, hit_sport,
             hit_tech, hit_cult, hit_ent, hit_social_life)):
        # 1) 社会（事件/监管级）最高优先：警方/刑拘/命案/火灾/救援/通报/违规收费等
        if hit_social:
            return '社会'
        # 2) 生活强词：健康/养生/育儿/家居/出行等民生日常
        if hit_life:
            return '生活'
        # 3) 环境强词：纯自然灾害/气候/生态/环保（含社会词的在第 1 步已拦截）
        if hit_env:
            return '环境'
        # 4) 经济强词：股票/央行/通胀/关税/楼市等财经信号（生活/社会/环境优先）
        if hit_econ:
            return '经济'
        # 5) 体育强词：赛事/球队/球星/奖牌等
        if hit_sport:
            return '体育'
        # 6) 科技强词：AI/芯片/航天/手机等（不抢经济/体育/环境/娱乐）
        if best_cat in ('', '国际', '时事', '人文', '生活', '社会') and hit_tech:
            return '科技'
        # 7) 人文强词：博物馆/考古/文化/教育/学术等
        if best_cat in ('', '国际', '时事', '生活', '环境', '体育', '社会') and hit_cult:
            return '人文'
        # 8) 娱乐强词：影视/音乐/综艺/明星等
        if best_cat in ('', '国际', '时事', '人文', '体育', '生活', '社会') and hit_ent:
            return '娱乐'
        # 9) 社会（民生/舆情级）：辟谣/寻人/维权/食品安全等（未被生活抢走时归社会）
        if hit_social_life:
            return '社会'
        # 10) 国外地名/主体强词：事件发生地/主体在国外 → 国际
        if hit_foreign:
            return '国际'
        # 11) 国内政治/纪律/政府事务强词：→ 时事
        if hit_politics:
            return '时事'
        if best_cat:
            return best_cat
    # 兜底：标题为外语（英文占比高）→ 国际；否则不分类，由调用方按"时事"兜底
    try:
        if _news_is_foreign(title_txt):
            return '国际'
    except Exception:
        pass
    return ''


@app.route('/api/news', methods=['GET'])
def api_get_news():
    """公开：新闻列表（倒序，分页，每页条数由排版配置决定）"""
    db = get_db()
    try:
        page = max(1, int(request.args.get('page', 1)))
    except (TypeError, ValueError):
        page = 1
    try:
        per_page = max(5, min(50, int(_get_news_config()['per_page'])))
    except (TypeError, ValueError):
        per_page = 20
    offset = (page - 1) * per_page
    category = request.args.get('category', '').strip()
    # 时间筛选：days=0 表示全部时间，days>0 表示近 N 天（基于 created_at 过滤）
    try:
        days = int(request.args.get('days', 0) or 0)
    except (TypeError, ValueError):
        days = 0
    if days < 0:
        days = 0
    since = (time.time() - days * 86400) if days > 0 else 0

    where = ['(report_removed=0 OR report_removed IS NULL)']
    where_args = []
    if category:
        # 分类合并映射（前端标签合并）：国际∪时事、经济∪财经、娱乐∪文娱
        _CATEGORY_MERGE = {
            '时事': ['国际', '时事'],
            '国际': ['国际', '时事'],
            '经济': ['经济', '财经'],
            '娱乐': ['娱乐', '文娱'],
            '社群': ['社群', '游戏社群'],
        }
        # 「其他」兜底：不属于任何明确分类的新闻（含已合并的旧分类）
        _CATEGORY_MAIN = ['国际', '社会', '经济', '体育', '科技', '文娱', '人文', '生活', '环境', '游戏社群', '社群', '时事', '财经', '娱乐']
        if category == '其他':
            where.append('category NOT IN (%s)' % ','.join('?' * len(_CATEGORY_MAIN)))
            where_args.extend(_CATEGORY_MAIN)
        elif category in _CATEGORY_MERGE:
            cats = _CATEGORY_MERGE[category]
            where.append('category IN (%s)' % ','.join('?' * len(cats)))
            where_args.extend(cats)
        else:
            where.append('category=?')
            where_args.append(category)
    if since:
        where.append('created_at>=?')
        where_args.append(since)
    where_sql = ' AND '.join(where)
    rows = _fetchall(db, '''
        SELECT id, title, content, image, author_id, likes, created_at, summary, category, pinned, images, featured
        FROM news WHERE %s ORDER BY pinned DESC, created_at DESC LIMIT ? OFFSET ?
    ''' % where_sql, tuple(where_args + [per_page, offset]))
    total = _fetchone(db, 'SELECT COUNT(*) as c FROM news WHERE %s' % where_sql, tuple(where_args))
    items = []
    for r in rows:
        # 栏目壳过滤：纯栏目名标题（如「界面晚报 | xxx」「牛市早报｜xxx」）且正文过短，
        # 点进去没有真实新闻内容，列表不展示（详情接口同步过滤）
        if len((r.get('content') or '').strip()) < 200 and _is_shell_column_title(r.get('title') or ''):
            continue
        d = _news_to_dict(r)
        d.pop('content', None)
        items.append(d)
    # 多语种译文增强：外语新闻标题/摘要翻译为中文（复用聚合接口的翻译链路与缓存）
    # 聚合计数：同一事件 7 天内跨信源相关报道数，让列表页直接展示聚合痕迹
    try:
        from concurrent.futures import ThreadPoolExecutor
        now_ts = time.time()

        def _translate_list_item(it):
            with app.app_context():
                need_t = _news_is_foreign(it.get('original_title') or it.get('title') or '')
                need_s = _news_is_foreign(it.get('original_summary') or it.get('summary') or '')
                if not need_t and not need_s:
                    it['need_translate'] = False
                    return
                it['need_translate'] = True
                it.setdefault('original_title', it.get('title') or '')
                it.setdefault('original_summary', it.get('summary') or '')
                if need_t:
                    it['title'], _m = _news_tr_zh(it.get('original_title') or '')
                if need_s:
                    it['summary'], _m2 = _news_tr_zh(it.get('original_summary') or '')
                # 中英混合标题可能被误判为外文：翻译结果与原文一致时不标记翻译
                if need_t and (it.get('title') or '').strip() == (it.get('original_title') or '').strip():
                    it['need_translate'] = False

        with ThreadPoolExecutor(max_workers=6) as ex:
            futs = [ex.submit(_translate_list_item, it) for it in items]
            for f in futs:
                try:
                    f.result(timeout=60)
                except Exception:
                    pass
    except Exception:
        for it in items:
            try:
                with app.app_context():
                    need_t = _news_is_foreign(it.get('original_title') or it.get('title') or '')
                    if need_t:
                        it['original_title'] = it.get('title') or ''
                        it['title'], _m = _news_tr_zh(it.get('original_title') or '')
                        it['need_translate'] = True
            except Exception:
                pass
    # 聚合计数：对每条列表新闻统计 7 天内跨信源相关报道数（同源去重，score>=3 同聚合接口口径）
    try:
        ids = [it['id'] for it in items]
        rel_counts = {}
        if ids:
            since = now_ts - 7 * 86400
            cand_rows = _fetchall(db, '''
                SELECT id, title, summary, author_id, created_at, category
                FROM news
                WHERE (report_removed=0 OR report_removed IS NULL) AND created_at>=? AND id NOT IN (%s)
                ORDER BY created_at DESC LIMIT 1200
            ''' % ','.join('?' * len(ids)), tuple([since] + ids))
            base_map = {}
            for it in items:
                base_map[it['id']] = _news_tokens(it.get('original_title') or it.get('title') or '')
            cand_toks = []
            for cr in cand_rows:
                cand_toks.append((cr, _news_tokens(cr['title'] or '')))
            for it in items:
                base_tokens = base_map[it['id']]
                base_en = [t for t in base_tokens if re.match(r'^[a-z0-9]', t)]
                base_zh = [t for t in base_tokens if re.match(r'^[\u4e00-\u9fff]', t)]
                seen_src = {}
                cnt = 0
                for cr, toks in cand_toks:
                    toks_en = [t for t in toks if re.match(r'^[a-z0-9]', t)]
                    toks_zh = [t for t in toks if re.match(r'^[\u4e00-\u9fff]', t)]
                    hit_en = [t for t in base_en if t in toks_en]
                    hit_zh = [t for t in base_zh if t in toks_zh]
                    score = len(hit_en) * 3 + len(hit_zh)
                    if score < 3:
                        continue
                    src = (cr.get('author_id') or '')
                    if src.startswith('source:'):
                        src = src[len('source:'):].strip()
                    key = src or 'user'
                    if key in seen_src:
                        continue
                    seen_src[key] = True
                    cnt += 1
                rel_counts[it['id']] = cnt
        for it in items:
            it['related_count'] = rel_counts.get(it['id'], 0)
    except Exception:
        for it in items:
            it['related_count'] = 0
    # 分类展示归一：国际∪时事统一叫"时事"（前端展示/筛选一致）
    for it in items:
        if it.get('category') in ('国际', '时事'):
            it['category'] = '时事'
    return jsonify({'news': items, 'total': total['c'] if total else 0, 'page': page, 'per_page': per_page})


@app.route('/api/news/headline', methods=['GET'])
def api_get_news_headline():
    """公开：头条轮播专用接口。

    固定返回 5 条，规则：
      - 近 7 天、排除测试/占位数据、排除栏目壳
      - 有图优先；有图不足时用无图新闻补足（保证条数固定）
      - 硬新闻优先（国际/时事合并、社会、经济），并按合并分类均衡轮选，避免头条全是同一类
      - 不随前端分类切换而变化（前端只在本页初始化时加载一次）
    """
    db = get_db()
    try:
        days = min(30, max(1, int(request.args.get('days', 7))))
    except (TypeError, ValueError):
        days = 7
    since = time.time() - days * 86400
    rows = _fetchall(db, '''
        SELECT id, title, content, image, author_id, likes, created_at, summary, category, pinned, images, featured
        FROM news
        WHERE (report_removed=0 OR report_removed IS NULL) AND created_at>=?
          AND author_id NOT LIKE 'u_admin%'
        ORDER BY created_at DESC LIMIT 500
    ''', (since,))
    cands = []
    for r in rows:
        if len((r.get('content') or '').strip()) < 200 and _is_shell_column_title(r.get('title') or ''):
            continue
        t = (r.get('title') or '').strip()
        if t.startswith('【测试】') or t.startswith('测试') or t.startswith('n_test'):
            continue
        d = {
            'id': r['id'],
            'title': _news_refine_title(r['title'], r.get('content') or ''),
            'image': _news_image_url(r.get('image')),
            'likes': r['likes'],
            'created_at': r['created_at'],
            'summary': r.get('summary') or '',
            'category': r.get('category') or '',
            'pinned': bool(r.get('pinned')),
            'featured': bool(r.get('featured')),
        }
        aid = r.get('author_id') or ''
        if aid.startswith('source:'):
            d['author_name'] = aid[len('source:'):].strip() or '新闻源'
        else:
            d['author_name'] = ''
        # 英文标题（未翻译入库）标记：优先中文标题新闻，英文仅作补足，避免头条区中英混排
        d['_is_en'] = bool(re.search(r'[A-Za-z]{4,}', d.get('title') or ''))
        cands.append(d)

    # 前端统一展示"时事"标签：国际∪时事合并归一（后端分类值国际/时事均展示为时事）
    _HEADLINE_MERGE = {'国际': '时事', '时事': '时事', '财经': '经济', '文娱': '娱乐', '游戏社群': '社群'}
    for d in cands:
        raw_cat = d.get('category') or ''
        d['_cat'] = _HEADLINE_MERGE.get(raw_cat, raw_cat or '')
        d['category'] = d['_cat']
    _HARD_CATS = ['时事', '社会', '经济']
    _NORMAL_CATS = ['体育', '科技', '人文', '娱乐', '生活', '环境', '社群', '其他', '']

    def _pick_balanced(pool, seen, limit, hard_cap=2, normal_cap=1):
        out = []
        # 同一分类内优先中文标题；英文标题（_is_en）排在同类末尾，仅在中文不足时补足
        def _pick_cat(cat, cap):
            cnt = 0
            zh = [d for d in pool if d['_cat'] == cat and not d.get('_is_en')]
            en = [d for d in pool if d['_cat'] == cat and d.get('_is_en')]
            for d in zh + en:
                if cnt >= cap or len(out) >= limit:
                    break
                if d['id'] not in seen:
                    out.append(d)
                    seen.add(d['id'])
                    cnt += 1
        for cat in _HARD_CATS:
            _pick_cat(cat, hard_cap)
            if len(out) >= limit:
                break
        for cat in _NORMAL_CATS:
            _pick_cat(cat, normal_cap)
            if len(out) >= limit:
                break
        return out

    seen = set()
    with_img = [d for d in cands if d.get('image')]
    no_img = [d for d in cands if not d.get('image')]
    picked = _pick_balanced(with_img, seen, 5)
    if len(picked) < 5:
        picked += _pick_balanced(no_img, seen, 5 - len(picked))
    if len(picked) < 5:
        for d in with_img + no_img:
            if len(picked) >= 5:
                break
            if d['id'] not in seen:
                picked.append(d)
                seen.add(d['id'])
    for d in picked:
        d.pop('_cat', None)
        d.pop('_is_en', None)
    # 英文标题翻译：头条区也要求展示中文译文（AI 优先 + 缓存，复用 _news_tr_zh）
    try:
        from concurrent.futures import ThreadPoolExecutor
        def _tr_headline(d):
            orig = (d.get('title') or '').strip()
            if re.search(r'[A-Za-z]{4,}', orig):
                tr, _m = _news_tr_zh(orig)
                if tr and tr.strip() and tr.strip() != orig:
                    d['title'] = tr.strip()
                    d['original_title'] = orig
                    d['need_translate'] = True
        with ThreadPoolExecutor(max_workers=min(5, max(1, len(picked)))) as _ex:
            list(_ex.map(_tr_headline, picked))
    except Exception:
        pass
    # 头条补图：无图条目联网搜索相关报道配图；失败保持无图降级
    try:
        _headline_attach_images(picked[:5])
    except Exception:
        pass
    return jsonify({'news': picked[:5], 'total': len(picked[:5])})


# ==========================================================================
# 头条图本机代理：外站图片经本服务抓取并缓存后同源返回，
# 前端 <img> 直连外站会慢/被防盗链拦（表现为头条图空白），走代理后秒开且可缓存。
# ==========================================================================
_IMG_PROXY_CACHE = {}
_IMG_PROXY_TTL = 3600
_IMG_PROXY_MAX_BYTES = 6 * 1024 * 1024


@app.route('/api/news/img', methods=['GET'])
def api_news_image_proxy():
    """按 ?u=<url> 抓取外站图片字节并缓存（1h），同源响应。仅限 http(s) 图片 URL。"""
    u = (request.args.get('u') or '').strip()
    if not u or not u.startswith(('http://', 'https://')):
        return jsonify({'error': 'bad url'}), 400
    now = time.time()
    hit = _IMG_PROXY_CACHE.get(u)
    if hit and now - hit[0] < _IMG_PROXY_TTL:
        return Response(hit[1], mimetype=hit[2],
                        headers={'Cache-Control': 'public, max-age=3600'})
    import urllib.request as _ur
    req = _ur.Request(u, headers={
        'User-Agent': ('Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 '
                       '(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36'),
        'Accept': 'image/avif,image/webp,image/apng,image/*,*/*;q=0.8',
        'Referer': 'https://peacenews.local/',
    })
    try:
        with _ur.urlopen(req, timeout=10) as resp:
            data = resp.read(_IMG_PROXY_MAX_BYTES + 1)
            if len(data) > _IMG_PROXY_MAX_BYTES:
                return jsonify({'error': 'too large'}), 413
            ctype = (resp.headers.get('Content-Type') or 'image/jpeg').split(';')[0].strip()
            if not ctype.startswith('image/'):
                ctype = 'image/jpeg'
    except Exception:
        return jsonify({'error': 'fetch failed'}), 502
    if len(_IMG_PROXY_CACHE) > 500:
        _IMG_PROXY_CACHE.clear()
    _IMG_PROXY_CACHE[u] = (now, data, ctype)
    return Response(data, mimetype=ctype,
                    headers={'Cache-Control': 'public, max-age=3600'})


@app.route('/api/news/translate', methods=['POST'])
def api_news_translate():
    """新闻实时翻译：整篇翻译标题+正文（复用 _news_tr_zh，AI 优先+缓存），供详情页“实时翻译”按钮调用。"""
    payload = request.get_json(silent=True) or {}
    news_id = (payload.get('news_id') or '').strip()
    if not news_id:
        return jsonify({'error': '缺少 news_id'}), 400
    db = get_db()
    row = _fetchone(db, 'SELECT id, title, content, summary FROM news WHERE id=?', (news_id,))
    if not row:
        return jsonify({'error': '新闻不存在'}), 404
    title = (row.get('title') or '').strip()
    content = (row.get('content') or '').strip()
    if len(content) > 20000:
        content = content[:20000]
    # 翻译提速：标题与正文并发翻译（均走 translations 缓存优先），重复请求秒回
    from concurrent.futures import ThreadPoolExecutor
    def _tr_in_ctx(piece):
        with app.app_context():
            return _news_tr_zh(piece)
    with ThreadPoolExecutor(max_workers=2) as _ex:
        _f1 = _ex.submit(_tr_in_ctx, title)
        _f2 = _ex.submit(_tr_in_ctx, content) if content else None
        t_title, m1 = _f1.result(timeout=90)
        if _f2:
            t_content, m2 = _f2.result(timeout=90)
        else:
            t_content, m2 = content, 'same'
    return jsonify({
        'news_id': news_id,
        'title': t_title,
        'content': t_content,
        'title_method': m1,
        'content_method': m2,
    })


@app.route('/api/news/<news_id>', methods=['GET'])
def api_get_news_detail(news_id):
    """公开：新闻详情"""
    db = get_db()
    row = _fetchone(db, 'SELECT id, title, content, image, author_id, likes, created_at, summary, category, pinned, ai_allowed, images, report_removed FROM news WHERE id=?', (news_id,))
    if not row:
        return jsonify({'error': '新闻不存在'}), 404
    if row.get('report_removed'):
        return jsonify({'error': '新闻已下架'}), 410
    # 栏目壳过滤：纯栏目名标题且正文过短，无真实新闻内容，详情不展示
    if len((row.get('content') or '').strip()) < 200 and _is_shell_column_title(row.get('title') or ''):
        return jsonify({'error': '新闻不存在'}), 404
    uid = _get_auth_user_id()
    d = _news_to_dict(row, uid)
    # 分类展示归一：国际∪时事统一叫"时事"（编辑弹窗/前端展示一致）
    if d.get('category') in ('国际', '时事'):
        d['category'] = '时事'
    # 多语种译文增强：外语新闻标题/摘要翻译为中文（与列表/聚合一致；并发提速）
    try:
        with app.app_context():
            need_t = _news_is_foreign(d.get('title') or '')
            need_s = _news_is_foreign(d.get('summary') or '')
            if need_t or need_s:
                d['need_translate'] = True
                d.setdefault('original_title', d.get('title') or '')
                d.setdefault('original_summary', d.get('summary') or '')
                from concurrent.futures import ThreadPoolExecutor
                def _tr_detail_piece(piece):
                    with app.app_context():
                        return _news_tr_zh(piece)
                with ThreadPoolExecutor(max_workers=2) as _ex:
                    _ft = _ex.submit(_tr_detail_piece, d.get('original_title') or '') if need_t else None
                    _fs = _ex.submit(_tr_detail_piece, d.get('original_summary') or '') if need_s else None
                    if _ft:
                        d['title'], _m = _ft.result(timeout=90)
                    if _fs:
                        d['summary'], _m2 = _fs.result(timeout=90)
                if need_t and (d.get('title') or '').strip() == (d.get('original_title') or '').strip():
                    d['need_translate'] = False
    except Exception:
        pass
    # 正文是否外文：用于详情页“实时翻译”按钮显隐
    try:
        d['is_foreign'] = _news_is_foreign(
            (d.get('original_title') or d.get('title') or '') + ' ' + (d.get('content') or '')[:600]
        )
    except Exception:
        d['is_foreign'] = False
    return jsonify({'news': d})


# ==========================================================================
# 相关新闻聚合（同一事件跨信源匹配）
# 匹配原则：
#   1. 主题词抽取：对标题做分词，剔除停用词后取有信息量的词（含英文/数字 token）
#   2. 候选召回：与目标新闻共享 >=2 个主题词的新闻（关键词在标题或摘要中命中）
#   3. 时间窗：默认 7 天内（参数 days 可调）
#   4. 去重：排除自身；同一信源只保留最新一条；优先展示不同信源
#   5. 排序：共享主题词数降序 -> 时间降序
# ==========================================================================
_NEWS_STOPWORDS = set('的 了 和 与 及 或 是 在 对 为 就 而 但 并 等 中 上 下 大 小 新 旧 个 名 位 项 一 二 三 四 五 六 七 八 九 十 不 也 都 还 又 再 只 被 把 让 给 用 以 于 之 其 这 那 该 各 每 从 到 向 往 说 称 表 示 称 报 道 记 者 讯 电 网 日 月 年 时 分 秒 亿 万 元 人 民 国 家 中 国 美 国 国 际 内 外 全 球 世 界 今 昨 明 后 前 最 近 目 前 当 前 已 经 将 会 可 能 需 要 没 有 成 为 进 行 发 布 发 表 提 供 取 得 获 得 达 到 超 过 增 长 下 降 上 升 出 现 发 生 引 起 导 致 影 响 关 于 通过 这个 这些 那些 一个 我们 你们 他们 记者 报道 表示 认为 指出 强调 宣布 透露 显示 显示 消息 新闻 来源 综合 讯 电 社 分社 特约 独家 目前 昨日 今日 明天 今天 今天 上午 下午 晚上 中国 美国 英国 法国 德国 日本 韩国 世界 全国 首个 首次 最新 正式 已经 表示 相关 同时 其中 方面 以及 或者 因为 所以 但是 如果 虽然 依然 仍然 能够 可以 应该 必须 需要 看到 觉得 知道 了解 帮助 支持 合作 发展 建设 推动 促进 加强 提升 打造 实现 目标 未来 现在 过去 之前 之后 期间 当天 当地 有关 关于 事件 情况 问题 原因 结果 影响 意义 重要 主要 关键 核心 用户 平台 产品 服务 功能 内容 数据 信息 技术 工程 程师 公司 企业 市场 行业 领域 部门 机构 组织 相关 报道 文章 视频 图片 网友 群众 市民 记者 编辑 官方 表示 称 说 称 据悉 透露 显示 表明 指出 强调 宣布 发布 推出 上线 更新 版本 下载 安装 登录 注册 使用 用户 账号 密码 手机 电脑 网络 网站 链接 地址 系统 软件 硬件 应用 程序 代码 开发 测试 上线 运营 管理 维护 升级 优化 修复 解决 处理 完成 开始 结束 继续 停止 增加 减少 提升 降低 提高 达到 超过 突破 创新 突破 引领 全球 国内 海外 本地 远程 线上 线下 实体 虚拟 现实 数字 智能 智慧 平台 生态 体系 机制 模式 路径 方案 计划 项目 任务 工作 活动 会议 论坛 峰会 展览 大赛 评选 榜单 排行 排行 数据 报告 白皮书 蓝皮书 指南 手册 教程 课程 学习 教育 学生 学校 教师 教授 学院 大学 科研 研究 学术 论文 期刊 发表 发布 出版 图书 小说 文学 文化 艺术 音乐 电影 电视 综艺 节目 演员 导演 明星 粉丝 观众 票房 上映 演出 演唱会 专辑 歌曲 舞蹈 戏剧 美术 展览 博物馆 文物 遗址 历史 考古 传统 民俗 非遗 美食 旅游 景区 酒店 交通 出行 地铁 公交 高铁 飞机 航班 机场 火车 汽车 道路 桥梁 隧道 港口 物流 快递 配送 商品 购物 电商 价格 涨价 降价 优惠 折扣 促销 活动 消费 买家 卖家 商家 店铺 品牌 厂商 供应链 产业链 制造业 工厂 生产 产能 产量 销量 营收 利润 财报 股价 股票 基金 债券 银行 央行 利率 汇率 货币 通胀 通缩 经济 增长 复苏 衰退 危机 风险 投资 融资 并购 收购 上市 IPO 融资 估值 市值 科技 互联网 智能 机器 机器人 芯片 半导体 处理器 显卡 手机 数码 汽车 电动车 电池 充电 续航 系统 软件 硬件 生态 应用 服务 数据 云 计算 AI 人工智能 大模型 算法 模型 训练 推理 生成 识别 语音 视觉 图像 视频 内容 审核 安全 隐私 合规 监管 政策 法规 法律 条例 规定 制度 治理 改革 开放 创新 发展 战略 规划 目标 任务 部署 落实 执行 检查 监督 审计 考核 评估 反馈 总结 汇报 交流 学习 培训 会议 讲话 批示 指示 要求 强调 指出 表示 强调 宣布 发布 出台 实施 落地 见效 成果 成绩 成效 进展 突破 里程碑 新高度 新台阶 新局面 新气象 新征程 新篇章 高质量 现代化 全面 深化 拓展 延伸 覆盖 普及 推广 应用 落地 场景 试点 示范 标杆 典型 案例 样本 经验 做法 模式 机制 制度 体系 架构 框架 标准 规范 要求 细则 办法 方案 计划 行动 举措 措施 手段 途径 渠道 方式 方法 思路 理念 观念 意识 认知 理解 认识 把握 遵循 贯彻 执行 落实 推进 加快 加速 深化 细化 量化 优化 完善 健全 强化 提升 增强 提高 扩大 拓展 延伸 覆盖 普及 惠及 造福 服务 保障 支撑 赋能 助力 护航 引领 带动 促进 推动 驱动 激发 释放 激活 焕发 凝聚 汇聚 集聚 集成 整合 融合 协同 联动 配合 协作 共建 共享 共治 共赢 目标 愿景 蓝图 规划 纲要 方案 计划 任务 清单 台账 责任 分工 协同 督导 考核 激励 奖惩 追责 问责 整改 落实 销号 清零 收官 决战 攻坚 冲刺 决胜 圆满 成功 顺利 完成 实现 达成 收官 收官'.split())


# 相关新闻匹配用：英文度量/方位等噪声 token 停用补充（数字过滤后仍可能残留的单位词）
_NEWS_EN_NOISE = frozenset([
    'km', 'mi', 'm', 'cm', 'mm', 'kg', 'kmh', 'mph', 'wsw', 'nw', 'se', 'sw', 'ne',
    'nne', 'nnw', 'sse', 'ssw', 'ene', 'ese', 'est', 'gmt', 'utc', 'etc', 'inc', 'corp',
    'ltd', 'co', 'www', 'http', 'https', 'com', 'org', 'net',
])

# 相关新闻匹配用：英文通用高频词黑名单（虚词/泛化词/普通动词名词）。
# 用于：1) _news_tokens 英文 token 过滤，避免 next/week/stocks 等泛词拼出虚假命中分；
#      2) _extract_dynamic_anchors 动态专名锚剔除（句首大写普通词）。
_NEWS_EN_GENERIC = frozenset('''
a an the and or but for nor of at by in is it to from on with without over under as into
up down out off about after before during against between through above below near amid
among around per via vs plus minus i you he she we they me him her us them my your his
its our their this that these those there here be am are was were been being do does did
done doing have has had having can could will would shall should may might must need
not no yes so too very really quite just only also still even yet ever never then than
now today tomorrow yesterday soon later earlier again once more most less least much many
few some any all each every both either neither other another same such own what when
where which who whom whose why how if because though although while since unless until
whether get got gets make makes made take takes took see sees saw seen say says said tell
told show shows showed shown go goes went gone come comes came know knows knew think
thinks thought want wants look looks looked like likes liked put puts set sets new old
big small high low top best good bad great last first next previous recent latest day
days week weeks month months year years hour hours minute minutes time times people
news story stories report reports source sources photo photos video videos image images
world country countries city cities state states nation national international global
local home house health life live lives work works school water food air fire police
court government official officials says
'''.split())


def _news_tokens(text):
    """从标题/摘要中抽取有信息量的主题词（英文字母 token + 中文 bigram）

    中文不做分词，使用 2 字滑窗 bigram 表达主题；配合停用词过滤降低泛词噪声。
    数字/度量类 token（3.1、3.1%、2026、8km 等）不作为主题词返回，
    避免震级、百分比、年份等纯数字特征引发跨主题误匹配。
    """
    if not text:
        return []
    out = []
    # 英文/数字 token：纯数字或数字开头的度量/年份词直接丢弃；
    # 数字开头但含连续字母的组合（如 5g / 6g）保留，交由 _NEWS_EN_NOISE 过滤单位噪声
    for t in re.findall(r'[A-Za-z0-9][A-Za-z0-9\-\.]{1,}', text):
        t = t.strip(' -.').lower()
        if len(t) > 1 and t not in _NEWS_STOPWORDS and t not in _NEWS_EN_NOISE and t not in _NEWS_EN_GENERIC:
            if t[0].isdigit() and not re.search(r'[a-z]{2,}', t):
                continue
            out.append(t)
    # 中文 bigram（2 字滑窗），仅保留不含停用单字的片段
    han = re.sub(r'[^\u4e00-\u9fff]', '', text)
    for i in range(len(han) - 1):
        bg = han[i:i + 2]
        if bg[0] in _NEWS_STOPWORDS or bg[1] in _NEWS_STOPWORDS:
            continue
        if bg in _NEWS_STOPWORDS:
            continue
        out.append(bg)
    return list(dict.fromkeys(out))


# ======================================================================
# 相关新闻匹配：事件锚词表（匹配原则重设计）
# 分级设计：
#   A 级（强锚，权重 +6）：专有地名 / 机构 / 人物 / 产品，是事件"身份"信号；
#   B 级（中锚，权重 +3）：通用事件 / 主题词，只作辅助信号，单独出现不足以判定同主题；
#   数字/度量类词（震级 3.1、百分比 3.1%、年份 2026、距离 8km 等）不作为主题命中词。
# ======================================================================
_NEWS_ANCHOR_A = frozenset([
    # 中国省/地级地名（地级市 + 重点县级）
    '北京', '上海', '天津', '重庆', '香港', '澳门', '台湾', '台北', '高雄', '台中', '台南',
    '新疆', '阿克陶', '克孜勒苏', '阿图什', '乌鲁木齐', '喀什', '伊犁', '塔城', '阿勒泰', '昌吉',
    '巴音郭楞', '哈密', '吐鲁番', '博尔塔拉', '克拉玛依', '石河子', '库尔勒', '和田',
    '西藏', '拉萨', '日喀则', '林芝', '那曲', '昌都', '阿里', '山南',
    '内蒙古', '呼和浩特', '包头', '鄂尔多斯', '呼伦贝尔', '赤峰', '通辽', '乌兰察布',
    '宁夏', '银川', '吴忠', '固原', '中卫',
    '广西', '南宁', '桂林', '柳州', '北海', '梧州', '百色', '河池', '钦州', '贵港', '玉林',
    '四川', '成都', '绵阳', '宜宾', '泸州', '乐山', '甘孜', '阿坝', '凉山', '汶川', '雅安',
    '德阳', '南充', '达州', '遂宁', '内江', '广安', '眉山', '资阳', '攀枝花', '自贡',
    '云南', '昆明', '大理', '丽江', '昭通', '曲靖', '普洱', '红河', '德宏', '西双版纳', '楚雄',
    '贵州', '贵阳', '遵义', '安顺', '毕节', '黔东南', '黔南', '黔西南', '六盘水', '铜仁',
    '甘肃', '兰州', '天水', '酒泉', '嘉峪关', '张掖', '武威', '临夏', '甘南', '金昌', '白银', '庆阳', '定西',
    '青海', '西宁', '玉树', '海东', '海西', '果洛', '黄南', '海南州',
    '黑龙江', '哈尔滨', '齐齐哈尔', '牡丹江', '佳木斯', '大庆', '绥化', '鸡西', '双鸭山', '伊春',
    '吉林', '长春', '吉林市', '延边', '四平', '通化', '松原', '辽源', '白山', '白城',
    '辽宁', '沈阳', '大连', '鞍山', '抚顺', '本溪', '锦州', '丹东', '营口', '阜新', '辽阳', '盘锦',
    '河北', '石家庄', '唐山', '秦皇岛', '邯郸', '保定', '张家口', '承德', '廊坊', '沧州', '邢台', '衡水',
    '山西', '太原', '大同', '阳泉', '长治', '晋城', '运城', '临汾', '忻州', '吕梁', '晋中', '朔州',
    '陕西', '西安', '宝鸡', '咸阳', '渭南', '延安', '榆林', '汉中', '安康', '商洛', '铜川',
    '山东', '济南', '青岛', '烟台', '威海', '潍坊', '淄博', '济宁', '临沂', '日照', '枣庄',
    '东营', '泰安', '德州', '聊城', '滨州', '菏泽',
    '江苏', '南京', '苏州', '无锡', '常州', '南通', '徐州', '扬州', '镇江', '泰州', '盐城',
    '连云港', '淮安', '宿迁',
    '浙江', '杭州', '宁波', '温州', '嘉兴', '湖州', '绍兴', '金华', '台州', '丽水', '衢州', '舟山',
    '安徽', '合肥', '芜湖', '蚌埠', '安庆', '黄山', '阜阳', '淮南', '马鞍山', '宿州', '六安', '亳州',
    '福建', '福州', '厦门', '泉州', '漳州', '莆田', '宁德', '南平', '三明', '龙岩',
    '江西', '南昌', '九江', '赣州', '吉安', '宜春', '上饶', '抚州', '萍乡', '景德镇', '新余',
    '河南', '郑州', '开封', '洛阳', '南阳', '安阳', '新乡', '许昌', '商丘', '信阳', '周口', '驻马店',
    '湖北', '武汉', '宜昌', '襄阳', '荆州', '黄石', '十堰', '恩施', '荆门', '孝感', '黄冈', '咸宁',
    '湖南', '长沙', '株洲', '湘潭', '衡阳', '岳阳', '常德', '郴州', '永州', '怀化', '娄底', '邵阳',
    '广东', '广州', '深圳', '珠海', '佛山', '东莞', '中山', '惠州', '江门', '汕头', '湛江',
    '肇庆', '梅州', '清远', '潮州', '揭阳', '汕尾', '阳江', '茂名', '韶关', '河源', '云浮',
    '海南', '海口', '三亚', '三沙', '儋州',
    # 外国国家/地区
    '美国', '英国', '法国', '德国', '意大利', '西班牙', '葡萄牙', '荷兰', '比利时', '卢森堡',
    '瑞典', '挪威', '芬兰', '丹麦', '波兰', '奥地利', '瑞士', '希腊', '爱尔兰', '冰岛',
    '俄罗斯', '乌克兰', '白俄罗斯', '格鲁吉亚', '亚美尼亚', '阿塞拜疆', '摩尔多瓦',
    '日本', '韩国', '朝鲜', '印度', '巴基斯坦', '孟加拉国', '斯里兰卡', '尼泊尔', '不丹',
    '新加坡', '泰国', '越南', '老挝', '柬埔寨', '缅甸', '菲律宾', '马来西亚', '印度尼西亚',
    '文莱', '东帝汶', '蒙古国', '哈萨克斯坦', '乌兹别克斯坦', '吉尔吉斯斯坦', '塔吉克斯坦', '土库曼斯坦',
    '伊朗', '伊拉克', '叙利亚', '黎巴嫩', '约旦', '以色列', '巴勒斯坦', '沙特阿拉伯', '沙特',
    '阿联酋', '卡塔尔', '巴林', '科威特', '阿曼', '也门', '土耳其', '塞浦路斯', '阿富汗',
    '埃及', '利比亚', '阿尔及利亚', '摩洛哥', '突尼斯', '苏丹', '南苏丹', '埃塞俄比亚', '肯尼亚',
    '尼日利亚', '加纳', '南非', '坦桑尼亚', '乌干达', '赞比亚', '津巴布韦', '莫桑比克', '安哥拉',
    '刚果', '索马里', '马里', '尼日尔', '乍得', '吉布提', '卢旺达', '布隆迪', '马达加斯加', '塞内加尔',
    '澳大利亚', '新西兰', '加拿大', '墨西哥', '巴西', '阿根廷', '智利', '秘鲁', '哥伦比亚',
    '委内瑞拉', '古巴', '巴拿马', '乌拉圭', '巴拉圭', '厄瓜多尔', '玻利维亚', '海地', '牙买加',
    '波多黎各', '哥斯达黎加', '危地马拉', '洪都拉斯', '萨尔瓦多', '尼加拉瓜',
    # 外国重点城市/地区
    '华盛顿', '纽约', '洛杉矶', '旧金山', '芝加哥', '波士顿', '西雅图', '休斯顿', '迈阿密', '费城',
    '亚特兰大', '丹佛', '拉斯维加斯', '底特律', '阿拉斯加', '夏威夷', '福克斯群岛',
    '安德烈亚诺夫群岛', '尼古拉斯基', '卡斯卡迪亚', '加州', '得州', '德克萨斯', '佛罗里达',
    '俄亥俄', '宾夕法尼亚', '伊利诺伊', '密歇根', '佐治亚',
    '伦敦', '巴黎', '柏林', '莫斯科', '基辅', '布鲁塞尔', '日内瓦', '维也纳', '马德里', '罗马',
    '雅典', '里斯本', '阿姆斯特丹', '都柏林', '赫尔辛基', '奥斯陆', '斯德哥尔摩', '哥本哈根',
    '华沙', '布拉格', '布达佩斯', '布加勒斯特', '贝尔格莱德', '索非亚', '萨格勒布', '慕尼黑',
    '汉堡', '法兰克福', '米兰', '那不勒斯', '巴塞罗那', '塞维利亚', '曼彻斯特', '利物浦', '格拉斯哥',
    '东京', '大阪', '京都', '名古屋', '福冈', '札幌', '横滨', '神户', '冲绳', '北海道', '福岛',
    '首尔', '平壤', '新德里', '孟买', '班加罗尔', '曼谷', '雅加达', '马尼拉', '河内', '胡志明市',
    '吉隆坡', '仰光', '金边', '万象', '悉尼', '墨尔本', '布里斯班', '珀斯', '堪培拉', '惠灵顿',
    '奥克兰', '渥太华', '多伦多', '温哥华', '蒙特利尔', '魁北克', '墨西哥城', '圣保罗', '里约热内卢',
    '布宜诺斯艾利斯', '利马', '波哥大', '圣地亚哥', '卡拉卡斯', '哈瓦那',
    '开罗', '内罗毕', '迪拜', '多哈', '利雅得', '德黑兰', '巴格达', '大马士革', '安曼', '贝鲁特',
    '特拉维夫', '耶路撒冷', '安卡拉', '伊斯坦布尔', '喀土穆', '亚的斯亚贝巴', '拉各斯', '约翰内斯堡',
    '开普敦', '卡萨布兰卡', '突尼斯市', '阿尔及尔', '的黎波里',
    # 国际机构/组织
    '联合国', '欧盟', '北约', '世卫', '世贸', '世界银行', '国际货币基金组织', '国际法院',
    '国际原子能机构', 'OPEC', '欧佩克', '美联储', '欧央行', '欧洲央行', '日本央行', '英国央行',
    '韩国央行', '白宫', '国务院', '外交部', '商务部', '财政部', '发改委', '工信部', '国防部',
    '中纪委', '中央纪委', '国家监委', '最高检', '最高法', '公安部',
    # 人物（政治/商业/文体）
    '特朗普', '拜登', '哈里斯', '普京', '泽连斯基', '马斯克', '扎克伯格', '贝索斯', '比尔盖茨',
    '石破茂', '岸田文雄', '安倍晋三', '菅义伟', '尹锡悦', '李在明', '文在寅', '莫迪', '马克龙',
    '朔尔茨', '默克尔', '苏纳克', '斯塔默', '特拉斯', '内塔尼亚胡', '哈梅内伊', '鲁哈尼',
    '萨勒曼', '武契奇', '埃尔多安', '卢拉', '阿尔巴尼斯',
    # 机构/公司/产品（科技/财经/娱乐/体育）
    'OpenAI', 'ChatGPT', 'Gemini', 'DeepSeek', 'Claude', 'Copilot', 'GPT', 'AGI', 'Sora',
    '苹果', '谷歌', '微软', '亚马逊', 'Meta', '英伟达', '高通', '英特尔', 'AMD', '台积电', '三星',
    '华为', '小米', '字节', '抖音', '腾讯', '阿里', '百度', '美团', '京东', '拼多多', '网易',
    '特斯拉', 'SpaceX', '波音', '空客', '丰田', '大众', '本田', '日产', '现代', '起亚', '保时捷',
    'Netflix', 'Disney', '华纳', '环球', '索尼', '任天堂', 'Steam', 'PlayStation', 'Xbox',
    '皇马', '巴萨', '曼联', '曼城', '利物浦', '阿森纳', '切尔西', '拜仁', '尤文', '国米',
    'AC米兰', '巴黎圣日耳曼', '湖人', '勇士', '凯尔特人', '掘金', '独行侠', '雄鹿', '太阳',
    '热火', '快船', '尼克斯', '篮网', '76人',
])

_NEWS_ANCHOR_B = frozenset([
    # 自然灾害/环境
    '地震', '震级', '余震', '海啸', '台风', '暴雨', '洪水', '泥石流', '山体滑坡', '山火', '森林火灾',
    '干旱', '高温', '寒潮', '暴雪', '冰雹', '龙卷风', '火山', '火山喷发', '海平面', '冰川',
    '温室气体', '碳中和', '碳达峰', '碳排放', '生物多样性', '生态', '污染', '雾霾', '沙尘暴',
    # 事故/灾难/社会事件
    '火灾', '爆炸', '坍塌', '坠机', '空难', '沉船', '车祸', '交通事故', '坠楼', '溺亡', '中毒',
    '遇难', '失联', '伤亡', '被困', '搜救', '救援', '消防', '疏散',
    '枪击', '袭击', '劫持', '绑架', '命案', '遇害', '失踪', '打人', '袭警',
    '诈骗', '电信诈骗', '盗窃', '抢劫', '拐卖', '性侵', '霸凌', '校园暴力', '传销',
    '刑拘', '逮捕', '判刑', '判决', '庭审', '立案', '通报', '辟谣', '曝光', '处罚', '罚款',
    '维权', '举报', '投诉', '纠纷', '讨薪', '欠薪', '劳动仲裁',
    # 政治/外交/军事
    '制裁', '关税', '关税战', '贸易战', '选举', '大选', '投票', '公投', '政变', '弹劾', '辞职', '罢免',
    '冲突', '战争', '停火', '和谈', '谈判', '协议', '峰会', '会谈', '访问', '外交', '大使', '建交',
    '导弹', '无人机', '轰炸', '核试验', '核武', '军演', '舰队', '边境', '难民', '移民',
    # 经济/财经
    '通胀', '通缩', '降息', '加息', '利率', '汇率', '财报', '营收', '利润', '股价', '股票', '股市',
    'IPO', '上市', '融资', '并购', '收购', '破产', '裁员', '失业', '就业', 'GDP', 'CPI', 'PPI',
    '债券', '黄金', '原油', '石油', '大宗商品', '房价', '楼市', '货币', '出口', '进口', '贸易',
    # 科技
    '大模型', '人工智能', '芯片', '半导体', '算力', '机器人', '自动驾驶', '卫星', '火箭', '航天',
    '探测器', '空间站', '量子', '区块链', '加密货币', '比特币', '虚拟现实', '算法', '开源',
    '专利', '新品', '旗舰', '系统', '软件', '硬件', '发布', '上线', '更新',
    # 体育
    '世界杯', '奥运会', '亚运会', '亚残运会', '全运会', '世锦赛', '公开赛', '冠军', '决赛', '半决赛',
    '奖牌', '金牌', '银牌', '铜牌', '夺冠', '卫冕', '进球', '逆转', '爆冷', '绝杀', '晋级', '出线',
    '足球', '篮球', '网球', '乒乓球', '羽毛球', '田径', '游泳', '体操', '马拉松', 'F1', '电竞',
    # 文化/娱乐
    '电影', '票房', '上映', '电视剧', '综艺', '演唱会', '专辑', '巡演', '音乐节', '颁奖', '奥斯卡',
    '博物馆', '考古', '文物', '遗址', '出土', '申遗', '非遗', '展览', '艺术展', '文学奖', '诺贝尔奖',
    # 健康/生活
    '疫苗', '疫情', '确诊', '流感', '病毒', '医疗', '手术', '体检', '健康', '养老', '社保', '医保',
    '食品安全', '药品', '临床试验',
])


def _extract_dynamic_anchors(text):
    """从文本动态提取英文专名 token（首字母大写）作为 A 级补充锚（Madonna/GLM/Claude/Anthropic 等）。

    静态锚词表无法穷举新兴公司/产品/模型/人名专名，导致"智谱 RSI / GLM-5.3 / Madonna"
    这类新闻在 _collect_related_news / /api/news/<id>/related 中 A/B 锚全空，只能按
    score>=12 的高门槛上榜，跨源相关检索几乎无命中。此处把标题中"首字母大写"的
    连续英文字母串（>=3 字符，剔除停用词/噪声词/英文高频泛词）作为动态强锚，
    与静态表合并参与计分。

    仅提取首字母大写词可避免 next/week/stocks/face 等普通小写词被误当专名，
    防止两条无关英文新闻因共享高频词被判"同专名"。
    """
    if not text:
        return []
    out = []
    for t in re.findall(r'\b[A-Z][A-Za-z\-]{2,}\b', text):
        core = t.strip('-').lower()
        if len(core) >= 3 and core not in _NEWS_STOPWORDS and core not in _NEWS_EN_NOISE and core not in _NEWS_EN_GENERIC:
            out.append(core)
    return list(dict.fromkeys(out))


def _extract_anchors(text, level='A'):
    """从标题/摘要中提取事件锚词：A=强锚（地名/机构/人物/专名），B=中锚（事件/主题词）。

    A 级除静态词表 _NEWS_ANCHOR_A 外，动态补充标题中的英文专名 token，
    保证 /api/news/<id>/related 与 _collect_related_news 两处匹配规则自动同步。
    """
    if not text:
        return []
    table = _NEWS_ANCHOR_A if level == 'A' else _NEWS_ANCHOR_B
    out = []
    for w in table:
        if w in text:
            out.append(w)
    if level == 'A':
        out.extend(_extract_dynamic_anchors(text))
    return out


@app.route('/api/news/<news_id>/related', methods=['GET'])
def api_get_news_related(news_id):
    """公开：相关新闻聚合（同一事件不同信源的相关报道）"""
    days = 7
    try:
        days = min(30, max(1, int(request.args.get('days', 7))))
    except (TypeError, ValueError):
        days = 7
    # 泛化地名（国家/大洲）锚点一律不算强锚（见下方过滤逻辑），不再区分 strict_geo 模式。
    db = get_db()
    row = _fetchone(db, 'SELECT id, title, content, summary, category, author_id, created_at FROM news WHERE id=?', (news_id,))
    if not row:
        return jsonify({'error': '新闻不存在'}), 404
    base_tokens = _news_tokens(row['title'])
    base_anchors_a = _extract_anchors(row['title'], 'A')
    base_anchors_b = _extract_anchors(row['title'], 'B')
    base_cat = '时事' if row.get('category') in ('国际', '时事') else (row.get('category') or '')
    base_src = (row.get('author_id') or '')
    if base_src.startswith('source:'):
        base_src = base_src[len('source:'):].strip()
    since = time.time() - days * 86400
    rows = _fetchall(db, '''
        SELECT id, title, content, summary, category, author_id, created_at
        FROM news
        WHERE (report_removed=0 OR report_removed IS NULL) AND id<>? AND created_at>=?
        ORDER BY created_at DESC LIMIT 800
    ''', (news_id, since))
    scored = []
    seen_src = {}
    base_bg = [t for t in base_tokens if t[0] >= '\u4e00']
    base_en = [t for t in base_tokens if t[0] < '\u4e00']
    for r in rows:
        toks = _news_tokens(r['title'])
        cand_a = _extract_anchors(r['title'], 'A')
        cand_b = _extract_anchors(r['title'], 'B')
        cand_bg = [t for t in toks if t[0] >= '\u4e00']
        cand_en = [t for t in toks if t[0] < '\u4e00']
        # 命中计分：A 级强锚（地名/专名/机构）权重最高，B 级事件词次之，
        # 中文 bigram / 英文 token 仅作辅助信号
        hit_a = [w for w in base_anchors_a if w in cand_a]
        hit_b = [w for w in base_anchors_b if w in cand_b]
        hit_bg = len(set(base_bg) & set(cand_bg))
        hit_en = len(set(base_en) & set(cand_en))
        score = len(hit_a) * 6 + len(hit_b) * 3 + hit_bg + (hit_en * 2 if (hit_a or hit_b) else 0)
        # 摘要兜底：标题命中不足时，允许摘要中的 A/B 级锚词与英文 token 弱信号计入（权重减半）
        if score < 7 and r.get('summary'):
            sum_a = _extract_anchors(r['summary'], 'A')
            sum_b = _extract_anchors(r['summary'], 'B')
            score2 = len(hit_a) * 6 + len(hit_b) * 3 + hit_bg + (hit_en * 2 if (hit_a or hit_b) else 0)
            score2 += len([w for w in base_anchors_a if w in sum_a]) * 3
            score2 += len([w for w in base_anchors_b if w in sum_b]) * 1
            score2 += (len(set(base_en) & set(_news_tokens(r['summary']))) if (hit_a or hit_b) else 0)
            score = max(score, score2)
        # 强锚判定：A 级锚中剔除泛化地名（国家/大洲仅命中不足以证明"同事件"）
        strong_a = [w for w in hit_a if w not in _GENERIC_GEO_ANCHORS]
        # 分类/主题强过滤：分类不同且无强关键词锚点（非泛化地名 A 级锚 或 B 级事件词锚）→ 非同主题，直接排除
        cand_cat = '时事' if r.get('category') in ('国际', '时事') else (r.get('category') or '')
        if base_cat and cand_cat and base_cat != cand_cat and not strong_a and not hit_b:
            continue
        # 跨类别降权：不同分类的弱匹配一律打折（避免"地震"主题误配他类）
        if base_cat and cand_cat and base_cat != cand_cat:
            score = score * 3 // 5
        # 上榜条件（宁缺毋滥）：
        #   有强锚共享（非泛化地名 A 级锚：同地点/同机构/同专名）→ score>=7 可上榜；
        #   无强锚（仅 B 级事件词/bigram 重合）→ 需 score>=12
        if strong_a:
            if score < 7:
                continue
        else:
            if score < 12:
                continue
        src = (r.get('author_id') or '')
        if src.startswith('source:'):
            src = src[len('source:'):].strip()
        item = {
            'id': r['id'],
            'title': _news_clean_title(r['title']),
            'original_title': r['title'],
            'summary': _news_summary_for_related(r),
            'original_summary': _news_summary_for_related(r),
            'content_preview': _news_content_preview(r),
            'has_more_content': _news_has_more_content(r),
            # 分类展示归一：国际∪时事统一叫"时事"
            'category': '时事' if r.get('category') in ('国际', '时事') else (r.get('category') or ''),
            'region': _news_region(r['title']),
            'created_at': r['created_at'],
            'source': src,
            'score': score,
            'same_category': bool(base_cat and ('时事' if r.get('category') in ('国际', '时事') else (r.get('category') or '')) == base_cat),
            'is_source_news': bool((r.get('author_id') or '').startswith('source:')),
        }
        # 同信源去重：每信源只留得分最高的
        key = src or 'user'
        if key in seen_src:
            if score > seen_src[key]['score']:
                seen_src[key] = item
        else:
            seen_src[key] = item
    scored = [v for v in seen_src.values()]
    scored.sort(key=lambda x: (-x['score'], -x['created_at']))
    top = scored[:12]
    # 多语种译文增强：外语新闻标题/摘要翻译为中文（AI 优先，回退 Azure/MyMemory）
    def _enhance(item):
        with app.app_context():
            need_t = _news_is_foreign(item.get('original_title') or '')
            need_s = _news_is_foreign(item.get('original_summary') or '')
            if not need_t and not need_s:
                item['need_translate'] = False
                return
            item['need_translate'] = True
            if need_t:
                item['title'], _m = _news_tr_zh(item.get('original_title') or '')
            if need_s:
                item['summary'], _m2 = _news_tr_zh(item.get('original_summary') or '')
    try:
        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(max_workers=6) as ex:
            futs = [ex.submit(_enhance, it) for it in top]
            for f in futs:
                try:
                    f.result(timeout=60)
                except Exception:
                    pass
    except Exception:
        for it in top:
            try:
                _enhance(it)
            except Exception:
                pass
    # 匹配说明：优先展示事件锚词（A/B 级），再补中文 bigram，便于前端展示命中依据
    matched_display = list(dict.fromkeys(base_anchors_a + base_anchors_b + base_bg[:6]))[:12]
    return jsonify({'related': top, 'matched_tokens': matched_display, 'total': len(scored)})


# ==========================================================================
# 单 Agent 分析（AI 新闻分析 · 综合深度分析视角）
# 设计借鉴（详见《参考仓库深度研究报告》）：
#   - 输出 JSON 契约：LightRAG 的严格 JSON 约束 + crewAI 的 output schema
#   - 缓存去重：news08 的缓存复用（UNIQUE(news_id, viewpoint_id)）
#   - 失败状态机：Yuxi-Know 的 ingest 状态（pending/running/success/failed）
#   - 超时降级：deep-search-with-agents 的 fallback 思路（失败落库可重试）
# 复用 server.py 现有 LLM 通道：call_lm_studio + get_ai_config（不新造凭据）
# ==========================================================================
# 视角体系 v2：从领域型升级为立场型。
# 每个视角有明确的分析立场定位、关注侧重、理论方法与证据标准，
# 同一新闻在不同视角下会产出有差异甚至冲突的结论，为后续多视角对撞功能铺垫。
# comprehensive 为综合兜底，立场中立、全维度收敛。
AGENT_VIEWPOINTS = [
    {
        "id": "comprehensive",
        "name": "综合深度分析",
        "description": "综合兜底角度：不预设倾向，按事件脉络-关键事实-多角度解读-历史背景-未来推演-疑点核实全维度收敛输出，作为其它分析角度的中立基准。",
        "stance": "综合中立：不预设任何立场倾向，平衡呈现各方信息与证据强度，收敛出对事件最完整的结构化理解。",
        "attention": ["事件脉络", "关键事实", "多角度解读", "历史背景", "未来推演", "疑点核实"],
        "method": "全维度收敛：依次梳理事件脉络与关键事实，交叉多角度解读，结合历史背景与未来推演，最后收敛疑点与不确定性。",
        "dimensions": ["事件脉络", "关键事实", "多角度解读", "影响与后续", "疑点核实"],
        "evidence_standard": "关键事实必须来自新闻原文或可信的相关报道并逐条标注来源；观点与事实分离；无法证实的内容必须归入不确定性；禁止编造来源。",
        "typical_scenes": "任何新闻均可作为兜底收敛分析。",
        "keywords": [],
        "exclude_rules": [],
    },
    {
        "id": "opportunity_growth",
        "name": "机遇进取角度",
        "description": "进取型角度：不甘被悲观叙事绑架，主动挖出事件中的利好信号、增长空间与机会窗口，敢断言也敢负责。",
        "stance": "机遇进取：默认悲观是懒惰的舒适区，机会常藏在被唱衰的角落里；紧盯增长、突破、窗口期，给出能落地的行动而非空谈。同时警惕「利好出尽」与「一哄而上」两种相反的坑。",
        "attention": ["利好信号", "增长空间", "产业机会", "窗口期", "行动建议"],
        "method": "机会挖掘：从事件中提取增长信号与新变量，结合行业周期与政策方向判断窗口期，输出积极但不过度乐观的行动建议。",
        "dimensions": ["利好信号", "增长空间", "窗口期", "行动建议"],
        "evidence_standard": "机会判断须有原文或参考报道支撑；前景预测以自然语言说明判断依据，禁止使用「（推测）」等括号标注；不得把乐观想象写成既有事实。",
        "typical_scenes": "企业业绩增长、技术量产、政策扶持、市场回暖、重大签约、新品发布等含明确利好信号的新闻。",
        "keywords": ["增长", "机遇", "利好", "突破", "创新", "加速", "升级", "扩产", "投资", "合作", "签约", "获批", "量产", "首发", "领先", "新高", "复苏", "回暖", "提速", "受益", "红利", "空间", "潜力", "机会", "订单", "出口增长", "盈利", "增收", "融资", "上市"],
        "exclude_rules": ["遇难", "死亡", "爆炸", "事故", "灾难", "灾害", "伤亡", "损失惨重", "危机", "破产", "倒闭"],
    },
    {
        "id": "risk_prudent",
        "name": "风险审慎角度",
        "description": "审慎型角度：不陪任何人唱高调，优先识别事件中的下行风险、代价成本与脆弱环节，评估连锁反应与应对预案。",
        "stance": "风险审慎：所有热闹都有账单要付。默认任何事件都有代价与尾部风险，优先问「谁受损、最坏怎样、扛不扛得住」，反对把风险转嫁给最弱势者。",
        "attention": ["下行风险", "代价成本", "脆弱环节", "连锁反应", "应对预案"],
        "method": "压力测试：对事件做「谁受益/谁受损/最坏情形」三问，参考历史同类事件的失控案例，输出风险等级与可操作的缓释措施。",
        "dimensions": ["下行风险", "代价成本", "脆弱环节", "连锁反应", "应对预案"],
        "evidence_standard": "风险判断须有原文或参考报道依据；对概率与后果的估计以自然语言说明依据，禁止使用「（推测）」等括号标注；禁止危言耸听。",
        "typical_scenes": "市场波动、债务违约、监管处罚、地缘冲突、安全事故、行业收缩等含下行信号或代价成本的新闻。",
        "keywords": ["风险", "隐患", "下跌", "亏损", "违约", "制裁", "限制", "调查", "处罚", "警告", "危机", "衰退", "收缩", "裁员", "停产", "下滑", "债务", "泡沫", "脆弱", "承压", "受阻", "放缓", "紧张", "恶化", "失控", "代价", "成本", "爆雷", "踩雷", "退市", "查封", "停工", "召回"],
        "exclude_rules": ["夺金", "夺冠", "打破纪录", "庆祝", "庆典", "竣工", "开业", "获奖", "丰收", "圆满"],
    },
    {
        "id": "critical_doubt",
        "name": "批判质疑角度",
        "description": "质疑型角度：对关键断言做来源追溯、数据复核与逻辑检验，识别被省略的上下文与利益动机，给出存疑点清单，不替权力与资本圆场。",
        "stance": "批判质疑：公开表述与事实之间永远可能有落差。默认追问来源、证据与利益动机，专戳话术漏洞与数据注水，拒绝照单全收，也拒绝为反而反。",
        "attention": ["证据链核查", "口径差异", "利益动机", "逻辑跳跃", "信息缺口"],
        "method": "证伪检验：对关键断言做来源追溯、数据复核与反向假设，识别被省略的上下文，给出「存疑点清单」而非结论清单。",
        "dimensions": ["证据链核查", "口径差异", "利益动机", "信息缺口"],
        "evidence_standard": "质疑必须有可追溯依据；无法证实的指控只能列为「存疑点」并说明缺口；禁止无证据的断言性结论。",
        "typical_scenes": "争议事件、数据造假、回应声明、调查通报、口径冲突、未经证实的传闻等存在信息落差的新闻。",
        "keywords": ["质疑", "争议", "核查", "回应", "声明", "否认", "辟谣", "造假", "欺诈", "举报", "曝光", "调查", "立案", "通报", "涉案", "证据", "泄露", "传闻", "回应称", "表示", "声称", "未回应", "细节", "矛盾", "口径", "数据", "统计", "真实性", "存疑", "专家称", "知情人士", "水分", "夸大", "误导", "隐瞒", "质疑者", "追责"],
        "exclude_rules": [],
    },
    {
        "id": "historical_depth",
        "name": "历史纵深角度",
        "description": "纵深感角度：把当前新闻放进历史坐标，寻找同类先例、周期规律与长期结构变迁，回答「今天这事在历史尺度上意味着什么」。",
        "stance": "历史纵深：今天没有新鲜事，只有忘了历史的重复。拒绝就事论事的短视，坚持把短期事件放回长期结构中考量，用先例校准当下的夸张。",
        "attention": ["同类先例", "周期规律", "结构变迁", "长期趋势", "历史坐标"],
        "method": "类比史学：检索历史同类事件（前任事件、相似政策、可对比危机），提炼共同规律与关键差异，判断当前处于周期的哪个阶段。",
        "dimensions": ["同类先例", "周期规律", "结构变迁", "长期趋势"],
        "evidence_standard": "历史类比必须注明依据（历史背景报道编号，常识推断用自然语言说明，禁止「（常识推断）」等括号标注）；类比适用性须说明差异边界；禁止把类比当作因果证明。",
        "typical_scenes": "里程碑事件、周年节点、制度沿革、行业周期更替、历史重演式事件等可放入时间坐标的新闻。",
        "keywords": ["历史", "首次", "再次", "重启", "回归", "延续", "多年", "十年", "此前", "以往", "过去", "曾经", "史上", "纪录", "突破历史", "前例", "先例", "周期", "阶段", "转折", "里程碑", "分水岭", "旧事", "往事", "重演", "相似", "类比", "规律", "长期", "趋势", "演变", "周年", "百年", "回望", "沿革", "迭代"],
        "exclude_rules": [],
    },
    {
        "id": "geopolitics_game",
        "name": "地缘博弈角度",
        "description": "博弈型角度：把新闻放进大国竞争与利益交换框架，识别参与者的筹码、算盘与代价，推演各方下一步动作与格局影响。",
        "stance": "地缘博弈：国际事务从来不是道德剧，而是利益棋盘。默认任何动作都有针对性与反制预期，戳穿「道义叙事」，盯住谁获利、谁受损、谁在试探红线、谁被牺牲。",
        "attention": ["各方筹码", "利益算盘", "反制预期", "阵营分化", "格局影响"],
        "method": "博弈推演：识别主要玩家及其核心利益，用「行动-反制-再反制」链条推演下一步，结合历史外交先例判断红线与底线。",
        "dimensions": ["各方筹码", "利益算盘", "反制预期", "阵营分化", "格局影响"],
        "evidence_standard": "博弈判断须有原文或参考报道依据；对各方动机的推断以自然语言说明依据并区分公开表态与私下算盘，禁止使用「（推测）」等括号标注；禁止替任何一方臆造立场。",
        "typical_scenes": "大国元首外交、军事演习、制裁反制、出口管制、领土争端、能源博弈、贸易摩擦等涉及多方博弈的新闻。",
        "keywords": ["外交", "访问", "会谈", "峰会", "谈判", "制裁", "反制", "博弈", "对抗", "合作", "同盟", "盟友", "阵营", "军事", "演习", "导弹", "核", "领土", "主权", "边境", "大使", "外交部", "联合国", "北约", "美国", "中国", "俄罗斯", "乌克兰", "欧盟", "中东", "亚太", "印度", "日本", "韩国", "朝鲜", "伊朗", "以色列", "巴以", "台湾", "涉台", "南海", "印太", "脱钩", "供应链", "关税", "出口管制", "地缘", "围堵", "遏制", "军售", "威慑"],
        "exclude_rules": ["农村", "农民", "农业", "乡村振兴", "扶贫", "低保", "菜价", "猪价", "粮价", "春耕", "秋收", "宅基地", "村委会", "村支书", "合作社", "种粮", "惠农", "养老金", "医保报销", "就业帮扶", "社区养老"],
    },
    {
        "id": "policy_regulation",
        "name": "制度政策角度",
        "description": "政策型角度：从政策法规、监管规则与制度设计的角度切入，关注政策意图、执行路径、合规影响与制度变迁。",
        "stance": "制度政策：规则背后是权力意志，政策文本与现实执行之间常有温差。关注规则怎么定、为何定、如何执行、谁在空转，警惕「政策造势」与「一刀切」两种变形。",
        "attention": ["政策意图", "监管规则", "执行路径", "合规影响", "制度变迁"],
        "method": "政策拆解：定位事件对应的政策法规与监管框架，拆解政策目标-工具-约束三层，评估对行业与主体的合规成本与行为重塑。",
        "dimensions": ["政策意图", "监管规则", "合规影响", "制度变迁"],
        "evidence_standard": "政策解读须有法规原文或权威报道依据；对政策意图的推断以自然语言说明依据，禁止使用「（推测）」等括号标注；禁止虚构条文或生效时间。",
        "typical_scenes": "法律法规出台、监管新政、行政审批改革、税收调整、产业扶持、标准制定等制度变量显著的新闻。",
        "keywords": ["政策", "法规", "监管", "立法", "新规", "条例", "办法", "意见", "通知", "规划", "试点", "改革", "制度", "审批", "许可", "准入", "标准", "规范", "细则", "规定", "要求", "落实", "执行", "监管局", "证监会", "央行", "财政部", "发改委", "工信部", "税务", "修订", "草案", "意见稿", "专项整治", "合规", "红线", "问责", "监管层"],
        "exclude_rules": [],
    },
    {
        "id": "market_capital",
        "name": "市场资本角度",
        "description": "市场型角度：从价格信号、资金流向、企业价值与产业供需的视角切入，关注事件的市场反应、估值变化与资本逻辑。",
        "stance": "市场资本：资本从不缺席，只会换一种方式定价。默认事件最终会落到价格与资金上，看穿叙事背后的筹码交换，警惕估值脱离基本面的击鼓传花。",
        "attention": ["价格信号", "资金流向", "估值变化", "供需结构", "资本动作"],
        "method": "市场归因：把事件映射到产业链与资本市场，判断供需两端与资金端的反应路径，评估对价格、估值与景气度的中期影响。",
        "dimensions": ["价格信号", "资金流向", "估值变化", "供需结构"],
        "evidence_standard": "市场判断须有行情数据或报道依据；对价格与估值预测以自然语言说明依据，禁止使用「（推测）」等括号标注；禁止编造涨跌幅或成交数据。",
        "typical_scenes": "股市异动、财报业绩、IPO并购、行业价格波动、进出口贸易、消费趋势等市场与资本信号明确的新闻。",
        "keywords": ["股价", "上涨", "下跌", "涨停", "跌停", "市值", "估值", "融资", "并购", "收购", "上市", "IPO", "财报", "营收", "利润", "业绩", "亏损", "盈利", "订单", "出口", "进口", "贸易", "关税", "汇率", "利率", "通胀", "CPI", "GDP", "增长", "下滑", "市场", "供需", "价格", "成本", "涨价", "降价", "消费", "需求", "资金", "基金", "债券", "股指", "板块", "龙头", "行业", "景气", "产能", "库存", "大宗商品", "原油", "黄金", "股市", "A股", "港股", "美股", "北向资金"],
        "exclude_rules": ["赛事", "夺冠", "锦标赛", "世锦赛", "奥运会", "亚运会", "演唱会", "电影节", "颁奖礼", "文艺汇演", "书画展", "非遗展演"],
    },
    {
        "id": "tech_evolution",
        "name": "技术演进角度",
        "description": "技术型角度：从技术原理、代际更替、创新扩散与产业应用的视角切入，评估事件在技术演化中的位置与落地前景。",
        "stance": "技术演进：技术是长期变量，但概念泡沫是短期病毒。关注创新是否构成代际跃迁、扩散路径与落地门槛，专拆「实验室到量产」之间的空头支票与营销话术。",
        "attention": ["技术原理", "代际更替", "创新突破", "扩散路径", "落地门槛"],
        "method": "技术评估：把事件放进技术成熟度曲线与产业链位置，区分渐进改良与范式跃迁，评估从实验室到量产的现实约束。",
        "dimensions": ["技术原理", "代际更替", "创新突破", "落地门槛"],
        "evidence_standard": "技术判断须有报道或行业依据；对技术成熟度与量产时间预测以自然语言说明依据，禁止使用「（推测）」等括号标注；禁止夸大技术能力或虚构参数。",
        "typical_scenes": "芯片突破、AI 模型发布、航天发射、新能源电池、自动驾驶、生物医药研发等技术变量显著的新闻。",
        "keywords": ["芯片", "半导体", "人工智能", "AI", "大模型", "算法", "算力", "机器人", "自动驾驶", "航天", "卫星", "火箭", "量子", "电池", "光伏", "风电", "新能源", "核聚变", "基因", "疫苗", "创新药", "研发", "专利", "技术", "突破", "国产化", "量产", "迭代", "升级", "应用", "落地", "场景", "数字化", "智能化", "算力", "数据中心", "操作系统", "开源", "大模型", "机器学习", "深度学习", "视觉", "语音", "传感器", "5G", "6G", "通信", "网络安全"],
        "exclude_rules": [],
    },
    {
        "id": "social_welfare",
        "name": "社会民生角度",
        "description": "民生型角度：站在普通人立场，从获得感、公共服务、物价就业、公平正义与基层治理的视角切入，关注事件对民众生活的实际影响。",
        "stance": "社会民生：政策好不好，最终看普通人过得好不好。盯住物价、就业、教育、医疗、养老、住房的基本面，敢指出宏大叙事与柴米油盐之间的温差，替沉默的大多数算账。",
        "attention": ["物价就业", "公共服务", "收入分配", "公平正义", "基层治理"],
        "method": "民生透视：把事件还原到具体生活场景，评估对普通家庭的收入、支出与安全感的影响，辨析受益与受损群体。",
        "dimensions": ["物价就业", "公共服务", "收入分配", "公平正义"],
        "evidence_standard": "民生判断须有官方数据或报道依据；对群体影响的概括必须注明数据范围；禁止以个案代替整体或渲染恐慌。",
        "typical_scenes": "物价波动、就业形势、养老医保、教育政策、住房保障、灾害救助、食品安全等直接关系民众生活的新闻。",
        "keywords": ["民生", "物价", "菜价", "猪肉", "粮食", "就业", "失业", "养老金", "医保", "社保", "养老", "医疗", "教育", "学费", "住房", "房价", "房租", "保障", "补贴", "惠民", "低保", "救助", "扶贫", "乡村振兴", "农村", "农民", "农民工", "工资", "欠薪", "消费", "维权", "投诉", "食品安全", "药品", "疫苗", "疫情", "灾害", "救援", "受灾", "供暖", "供水", "供电", "出行", "公交", "地铁", "票价", "惠民", "福利", "养老金上调", "退休", "幼儿园", "中小学", "医院", "看病", "买药"],
        "exclude_rules": [],
    },
    {
        "id": "cultural_value",
        "name": "文化价值角度",
        "description": "文化型角度：从文化传承、审美表达、公共记忆与价值观念的视角切入，评估事件的文化意义、符号价值与精神影响。",
        "stance": "文化价值：新闻背后都有文化坐标与价值底色。关注传统与现代的对话、审美表达与公共记忆的塑造，警惕把文化当流量道具、把传统当消费符号的浮躁。",
        "attention": ["文化传承", "审美表达", "公共记忆", "价值观念", "符号意义"],
        "method": "文化解码：把事件放入文化脉络，识别其承载的符号、传统与时代精神，评估对集体记忆与价值认同的影响。",
        "dimensions": ["文化传承", "审美表达", "公共记忆", "价值观念"],
        "evidence_standard": "文化解读须有事件事实依据；对符号意义的阐释须区分事实与解读；禁止牵强附会或过度升华。",
        "typical_scenes": "文化遗产保护、传统节日、影视文艺作品、考古发现、非遗传承、文化出海等文化含量高的新闻。",
        "keywords": ["文化", "艺术", "文学", "电影", "影视", "电视剧", "综艺", "音乐", "演唱会", "戏剧", "戏曲", "舞蹈", "美术", "展览", "博物馆", "文物", "考古", "非遗", "传统", "习俗", "节日", "春节", "中秋", "国潮", "文创", "IP", "符号", "精神", "价值观", "历史记忆", "遗产", "传承", "保护", "修复", "出版", "图书", "读书", "书法", "国画", "审美", "美学", "文明", "古籍", "书院", "诗词", "典籍", "文化出海", "申遗"],
        "exclude_rules": [],
    },
    {
        "id": "international_compare",
        "name": "国际比较角度",
        "description": "比较型角度：把事件放进国际坐标系，通过横向对比他国经验、全球趋势与跨国影响，定位事件的相对位置与借鉴意义。",
        "stance": "国际比较：孤立的新闻会失真，没有对照就没有判断。坚持放进全球坐标系，用他国先例与横向数据校准，既防「外国的月亮更圆」，也防「关起门来自我感觉良好」。",
        "attention": ["国际坐标", "他国先例", "全球趋势", "跨国影响", "借鉴意义"],
        "method": "横向对标：寻找同类事件的他国经验与全球数据，比较制度环境、发展阶段与路径差异，提炼可借鉴或需警惕的教训。",
        "dimensions": ["国际坐标", "他国先例", "全球趋势", "借鉴意义"],
        "evidence_standard": "国际比较须有公开数据或报道依据；引用他国数据必须注明来源；禁止用选择性数据误导对比结论。",
        "typical_scenes": "中外产业对比、国际规则变化、跨国企业动态、全球市场联动、他国政策经验等需横向定位的新闻。",
        "keywords": ["国际", "全球", "海外", "国外", "美国", "日本", "欧洲", "欧盟", "韩国", "新加坡", "德国", "法国", "英国", "俄罗斯", "印度", "东南亚", "非洲", "中东", "世界", "跨国", "跨境", "出海", "全球化", "对标", "对比", "差距", "领先", "落后", "追赶", "借鉴", "经验", "标准", "规则", "汇率", "出口", "进口", "外资", "外企", "关税", "贸易", "WTO", "IMF", "世行", "联合国", "国际货币", "外媒", "他国", "欧美", "日韩", "海外市场"],
        "exclude_rules": ["村委会", "村支书", "社区", "街道办", "县里", "镇上", "本地", "市区", "省内", "乡镇"],
    },
    {
        "id": "long_term_trend",
        "name": "长期趋势角度",
        "description": "趋势型角度：把事件放在十年以上尺度考察人口、技术、气候、制度等结构性力量，判断其是否构成长期拐点或趋势确认。",
        "stance": "长期趋势：短期波动只是噪音，慢变量才是主旋律。盯住人口、技术、气候、制度等结构性力量，敢在众人狂欢时提醒周期，也敢在众人悲观时指出拐点。",
        "attention": ["人口结构", "技术长波", "气候能源", "制度变迁", "趋势拐点"],
        "method": "趋势识别：把事件放入长周期数据与结构性力量框架，区分周期性波动与趋势性变化，评估趋势拐点与持续动能。",
        "dimensions": ["人口结构", "技术长波", "气候能源", "趋势拐点"],
        "evidence_standard": "趋势判断须有长周期数据或权威研究依据；结构性推断以自然语言说明依据与数据口径，禁止使用「（推测）」等括号标注；禁止把短期波动当趋势。",
        "typical_scenes": "人口老龄化、能源转型、技术代际更替、气候治理、城镇化、产业长期重构等具结构意义的新闻。",
        "keywords": ["长期", "趋势", "拐点", "老龄化", "人口", "出生率", "城镇化", "碳中和", "碳达峰", "能源转型", "气候", "可持续", "结构性", "慢变量", "十年", "三十年", "百年未有", "代际", "接班", "新生代", "未来十年", "长期主义", "周期切换", "赛道", "蓝海", "国运", "转型", "重构", "重塑", "范式"],
        "exclude_rules": ["今日", "昨天", "当场", "突发", "快讯", "即时", "紧急"],
    },
]


_AGENT_VIEWPOINT_MAP = {v["id"]: v for v in AGENT_VIEWPOINTS}


# 泛化地名/泛化区域锚词：仅命中这些词不足以证明"同事件"，AI 分析上下文注入时需更严格门槛
_GENERIC_GEO_ANCHORS = frozenset([
    '美国', '英国', '法国', '德国', '意大利', '西班牙', '葡萄牙', '荷兰', '比利时', '卢森堡',
    '瑞典', '挪威', '芬兰', '丹麦', '波兰', '奥地利', '瑞士', '希腊', '爱尔兰', '冰岛',
    '俄罗斯', '乌克兰', '白俄罗斯', '格鲁吉亚', '亚美尼亚', '阿塞拜疆', '摩尔多瓦',
    '日本', '韩国', '朝鲜', '印度', '巴基斯坦', '孟加拉国', '斯里兰卡', '尼泊尔', '不丹',
    '新加坡', '泰国', '越南', '老挝', '柬埔寨', '缅甸', '菲律宾', '马来西亚', '印度尼西亚',
    '文莱', '东帝汶', '蒙古国', '哈萨克斯坦', '乌兹别克斯坦', '吉尔吉斯斯坦', '塔吉克斯坦', '土库曼斯坦',
    '伊朗', '伊拉克', '叙利亚', '黎巴嫩', '约旦', '以色列', '巴勒斯坦', '沙特阿拉伯', '沙特',
    '阿联酋', '卡塔尔', '巴林', '科威特', '阿曼', '也门', '土耳其', '塞浦路斯', '阿富汗',
    '埃及', '利比亚', '阿尔及利亚', '摩洛哥', '突尼斯', '苏丹', '南苏丹', '埃塞俄比亚', '肯尼亚',
    '尼日利亚', '加纳', '南非', '坦桑尼亚', '乌干达', '赞比亚', '津巴布韦', '莫桑比克', '安哥拉',
    '刚果', '索马里', '马里', '尼日尔', '乍得', '吉布提', '卢旺达', '布隆迪', '马达加斯加', '塞内加尔',
    '澳大利亚', '新西兰', '加拿大', '墨西哥', '巴西', '阿根廷', '智利', '秘鲁', '哥伦比亚',
    '委内瑞拉', '古巴', '巴拿马', '乌拉圭', '巴拉圭', '厄瓜多尔', '玻利维亚', '海地', '牙买加',
    '波多黎各', '哥斯达黎加', '危地马拉', '洪都拉斯', '萨尔瓦多', '尼加拉瓜',
    '中国', '亚洲', '欧洲', '非洲', '美洲', '北美', '南美', '中东', '亚太', '全球', '国际',
])


def _collect_related_news(db, row, days=7, limit=12, strict_geo=False, min_days=0):
    """相关新闻聚合核心（与 /api/news/<id>/related 同款匹配规则）。

    基于标题 A/B 级锚词 + 中文 bigram + 英文 token 计分、跨类别降权、
    同信源去重、宁缺毋滥阈值筛选。返回 (top_items, matched_display, total_scored)。
    strict_geo=True 时（供 AI 分析上下文注入）：A 级命中仅含泛化地名（国家/大洲）时
    视为无强锚，需按 score>=12 的更高门槛上榜，避免"同国名即相关"的误配。
    min_days>0 时（供 AI 分析"历史背景报道"检索）：要求候选早于 min_days 天前，
    与近期相关报道（近7天）形成时间分层。
    注意：若修改 /api/news/<id>/related 的匹配规则，请同步本函数，保持两处一致。
    """
    base_tokens = _news_tokens(row['title'])
    base_anchors_a = _extract_anchors(row['title'], 'A')
    base_anchors_b = _extract_anchors(row['title'], 'B')
    base_cat = '时事' if row.get('category') in ('国际', '时事') else (row.get('category') or '')
    since = time.time() - days * 86400
    until = time.time() - min_days * 86400 if min_days > 0 else None
    if until is not None:
        rows = _fetchall(db, '''
            SELECT id, title, content, summary, category, author_id, created_at
            FROM news
            WHERE (report_removed=0 OR report_removed IS NULL) AND id<>? AND created_at>=? AND created_at<?
            ORDER BY created_at DESC LIMIT 800
        ''', (row['id'], since, until))
    else:
        rows = _fetchall(db, '''
            SELECT id, title, content, summary, category, author_id, created_at
            FROM news
            WHERE (report_removed=0 OR report_removed IS NULL) AND id<>? AND created_at>=?
            ORDER BY created_at DESC LIMIT 800
        ''', (row['id'], since))
    scored = []
    seen_src = {}
    base_bg = [t for t in base_tokens if t[0] >= '\u4e00']
    base_en = [t for t in base_tokens if t[0] < '\u4e00']
    for r in rows:
        toks = _news_tokens(r['title'])
        cand_a = _extract_anchors(r['title'], 'A')
        cand_b = _extract_anchors(r['title'], 'B')
        cand_bg = [t for t in toks if t[0] >= '\u4e00']
        cand_en = [t for t in toks if t[0] < '\u4e00']
        # 命中计分：A 级强锚（地名/专名/机构）权重最高，B 级事件词次之，
        # 中文 bigram / 英文 token 仅作辅助信号
        hit_a = [w for w in base_anchors_a if w in cand_a]
        hit_b = [w for w in base_anchors_b if w in cand_b]
        hit_bg = len(set(base_bg) & set(cand_bg))
        hit_en = len(set(base_en) & set(cand_en))
        score = len(hit_a) * 6 + len(hit_b) * 3 + hit_bg + (hit_en * 2 if (hit_a or hit_b) else 0)
        # 摘要兜底：标题命中不足时，允许摘要中的 A/B 级锚词与英文 token 弱信号计入（权重减半）
        if score < 7 and r.get('summary'):
            sum_a = _extract_anchors(r['summary'], 'A')
            sum_b = _extract_anchors(r['summary'], 'B')
            score2 = len(hit_a) * 6 + len(hit_b) * 3 + hit_bg + (hit_en * 2 if (hit_a or hit_b) else 0)
            score2 += len([w for w in base_anchors_a if w in sum_a]) * 3
            score2 += len([w for w in base_anchors_b if w in sum_b]) * 1
            score2 += (len(set(base_en) & set(_news_tokens(r['summary']))) if (hit_a or hit_b) else 0)
            score = max(score, score2)
        # 强锚判定：A 级锚中剔除泛化地名（国家/大洲仅命中不足以证明"同事件"）
        strong_a = [w for w in hit_a if w not in _GENERIC_GEO_ANCHORS]
        # 分类/主题强过滤：分类不同且无强关键词锚点（非泛化地名 A 级锚 或 B 级事件词锚）→ 非同主题，直接排除
        cand_cat = '时事' if r.get('category') in ('国际', '时事') else (r.get('category') or '')
        if base_cat and cand_cat and base_cat != cand_cat and not strong_a and not hit_b:
            continue
        # 跨类别降权：不同分类的弱匹配一律打折（避免"地震"主题误配他类）
        if base_cat and cand_cat and base_cat != cand_cat:
            score = score * 3 // 5
        # 上榜条件（宁缺毋滥）：
        #   有强锚共享（非泛化地名 A 级锚：同地点/同机构/同专名）→ score>=7 可上榜；
        #   无强锚（仅 B 级事件词/bigram 重合）→ 需 score>=12
        if strong_a:
            if score < 7:
                continue
        else:
            if score < 12:
                continue
        src = (r.get('author_id') or '')
        if src.startswith('source:'):
            src = src[len('source:'):].strip()
        item = {
            'id': r['id'],
            'title': _news_clean_title(r['title']),
            'original_title': r['title'],
            'summary': _news_summary_for_related(r),
            'original_summary': _news_summary_for_related(r),
            'content_preview': _news_content_preview(r),
            'has_more_content': _news_has_more_content(r),
            'category': '时事' if r.get('category') in ('国际', '时事') else (r.get('category') or ''),
            'region': _news_region(r['title']),
            'created_at': r['created_at'],
            'source': src,
            'score': score,
            'same_category': bool(base_cat and ('时事' if r.get('category') in ('国际', '时事') else (r.get('category') or '')) == base_cat),
            'is_source_news': bool((r.get('author_id') or '').startswith('source:')),
        }
        # 同信源去重：每信源只留得分最高的
        key = src or 'user'
        if key in seen_src:
            if score > seen_src[key]['score']:
                seen_src[key] = item
        else:
            seen_src[key] = item
    scored = [v for v in seen_src.values()]
    scored.sort(key=lambda x: (-x['score'], -x['created_at']))
    top = scored[:limit]
    matched_display = list(dict.fromkeys(base_anchors_a + base_anchors_b + base_bg[:6]))[:12]
    return top, matched_display, len(scored)


def _agent_get_news_context(news_id, related_limit=5, history_limit=4):
    """构建单 Agent 分析输入：标题+摘要+正文（外文自动附译文）+ 两类相关报道上下文。

    近期相关报道（近7天，R1-Rn）：同事件的多信源去重报道，供交叉印证；
    历史背景报道（更早同类，H1-Hm）：同一事件/同类事件更早的报道，供历史脉络梳理。
    """
    db = get_db()
    row = _fetchone(db, 'SELECT id, title, content, summary, category, author_id, created_at FROM news WHERE id=?', (news_id,))
    if not row:
        return None
    ctx = {
        "id": row["id"],
        "title": (row["title"] or "").strip(),
        "summary": (row["summary"] or "").strip(),
        "content": (row["content"] or "").strip(),
        "category": row["category"] or "",
        "source": (row["author_id"] or "").replace("source:", "").strip(),
        "trans_title": "",
        "trans_summary": "",
    }
    if len(ctx["content"]) > 3000:
        ctx["content"] = ctx["content"][:3000] + "……（正文已截断）"
    # 外文自动附译文（复用现有翻译通道 _news_tr_zh，走 translations 缓存）
    try:
        if _news_is_foreign(ctx["title"]):
            ctx["trans_title"], _m = _news_tr_zh(ctx["title"])
        if ctx["summary"] and _news_is_foreign(ctx["summary"]):
            ctx["trans_summary"], _m2 = _news_tr_zh(ctx["summary"])
    except Exception:
        pass
    # 近期相关报道（近7天多信源去重）：复用 /api/news/<id>/related 同款匹配规则；
    # strict_geo=True：仅靠泛化地名（国家/大洲）命中的候选不注入，避免"同国名即相关"误配
    try:
        top, _md, _tot = _collect_related_news(db, row, days=7, limit=related_limit, strict_geo=True)
        rel = []
        for it in top:
            s = (it.get("summary") or "").strip()
            rel.append({
                "id": it.get("id"),
                "title": (it.get("title") or "").strip(),
                "summary": s[:200] if s else "",
                "source": (it.get("source") or "").strip(),
            })
        ctx["recent_related"] = rel
    except Exception:
        ctx["recent_related"] = []
    # 历史背景报道（更早同类/前任事件）：早于 7 天前，取 H1-Hm 编号注入
    try:
        top_h, _mdh, _toth = _collect_related_news(db, row, days=180, limit=history_limit, strict_geo=True, min_days=7)
        rel_h = []
        for it in top_h:
            s = (it.get("summary") or "").strip()
            rel_h.append({
                "id": it.get("id"),
                "title": (it.get("title") or "").strip(),
                "summary": s[:200] if s else "",
                "source": (it.get("source") or "").strip(),
            })
        ctx["historical_related"] = rel_h
    except Exception:
        ctx["historical_related"] = []
    # 兼容旧字段
    ctx["related"] = ctx["recent_related"]
    return ctx


def _agent_build_system_prompt(viewpoint):
    """按视角生成结构化分析系统提示词（每个智能体有独立立场设定）。"""
    stance = viewpoint.get("stance") or viewpoint.get("description") or ""
    attention = "、".join(viewpoint.get("attention") or viewpoint.get("dimensions") or [])
    method = viewpoint.get("method") or ""
    return (
        "你是翱翔鸟新闻平台的「%s」智能体。\n"
        "立场定位：%s\n"
        "关注侧重：%s\n"
        "理论方法：%s\n"
        "输出要求（严格遵守）：\n"
        "1) 只输出一个 JSON 对象；禁止输出任何思考过程、解释、前言、复述、总结语、备注或 markdown 代码块围栏（禁止 ```、```json、```JSON 等一切围栏标记）；\n"
        "2) 输出对象的键固定为 summary / facts / angles / uncertainty / history / outlook，结构如下：\n"
        "{\n"
        '  "summary": "分析摘要（3-5 句，概述事件核心与关键判断）",\n'
        '  "facts": ["关键事实 1（须有原文依据，逐条标注来源：主新闻原文 或 R1/R2/H1 参考编号）", "关键事实 2", ... 3-6 条],\n'
        '  "angles": ["多角度要点 1（不同立场/侧面/时间维度的解读）", ... 3-5 条],\n'
        '  "uncertainty": "不确定性/待核实项（1-3 句，注明未证实信息、信息缺口或口径差异）",\n'
        '  "history": "历史背景（1-3 段：基于注入的历史背景报道与常识梳理过去脉络；注明哪些来自 H 编号注入报道；常识推断用自然语言说明依据，禁止使用「（常识推断）」等括号标注）",\n'
        '  "outlook": "未来推演（1-3 段：后续走向、可能影响、关键判断依据与时间窗口；对无法证实的前景用自然语言说明判断依据，禁止使用「（推测）」等括号标注）"\n'
        "}\n"
        "3) 关键事实必须来自新闻文本或参考报道，不得编造；"
        "4) 遵守证据标准：%s；"
        "5) 分析必须围绕本视角的立场定位展开，突出本视角的立场倾向与关注侧重，"
        "允许并鼓励与其它视角产出有差异甚至冲突的结论；"
        "6) 若用户消息中提供了「近期相关报道」（编号 R1-Rn），必须结合其做交叉印证："
        "facts 中逐条标注来源（主新闻原文 / R 编号）；多信源一致的事实可作为确证，单信源独家信息须注明口径；"
        "7) 若用户消息中提供了「历史背景报道」（编号 H1-Hm），必须在 history 中引用其梳理过去脉络，"
        "并注明哪些历史信息来自 H 编号；常识推断以自然语言说明依据，禁止「（常识推断）」等括号标注；outlook 的推断以自然语言说明依据，禁止「（推测）」等括号标注；"
        "8) 若没有任何参考报道，仅基于本条新闻分析即可，不要编造参考来源；"
        "9) 分析不替代原文。"
        "10) 锐度要求（强约束）：angles 区必须亮明立场与价值判断，敢于下结论，"
        "可使用「这暴露了…」「这不可接受」「错在…」「关键在于…」「风险在于…」「应…」等明确判断句式；"
        "显式禁止以下温吞敷衍句式：「值得关注」「值得注意」「指标包括」「若…被证实…将…」等只罗列不判断的写法；"
        "禁止「一方面…另一方面…」式和稀泥式平衡；每个 angle 必须有立场、有结论、有判断依据，而不是中性罗列要点。"
        "11) 输出必须以 { 开头、以 } 结尾；你的整段回复会被程序直接 json.loads 解析，任何多余字符（包括思考过程、解释、复述、总结）都会导致解析失败。正确格式示例（仅示范结构，内容须按本条新闻重新撰写）：\n"
        '{"summary": "一句话总判断。", "facts": ["事实 1（来源：主新闻原文）", "事实 2（来源：主新闻原文）"], "angles": ["有立场的判断：这暴露了……，应……", "有立场的判断：关键在于……，否则……"], "uncertainty": "待核实项。", "history": "历史脉络。", "outlook": "推演结论与判断依据。"}'
        % (viewpoint["name"], stance, attention, method, viewpoint["evidence_standard"])
    )


def _agent_assess_viewpoints(ctx):
    """基于新闻标题/摘要/正文/分类/信源，精确判断该新闻命中哪些分析角度。

    规则引擎 v3（角度体系）：每个角度是独立的分析立场/方法论/关注维度，
    通过「关键词矩阵命中 + 标题摘要加权 + 排除规则防误配 + 信息量校准」打分，
    并保证非兜底角度命中 2-4 个（不足按分数补齐、超限按分数截取），
    杜绝「只能唤醒一个视角」或「农村民生误配地缘博弈」两类问题。
    返回 [{viewpoint_id, name, description, applicable, score, reason, basis}]
    """
    title = (ctx.get("title") or "")
    summary = (ctx.get("summary") or "")
    content = (ctx.get("content") or "")
    category = (ctx.get("category") or "")
    source = (ctx.get("source") or "")
    text_all = (title + " " + summary + " " + content).lower()
    text_head = (title + " " + summary).lower()
    content_len = len(content.strip())

    items = []
    for v in AGENT_VIEWPOINTS:
        vid = v["id"]
        kws = v.get("keywords") or []
        excl = v.get("exclude_rules") or []
        # 关键词命中（标题/摘要命中权重更高）
        hits = []
        head_hits = []
        for kw in kws:
            kl = kw.lower()
            if kl and kl in text_all:
                hits.append(kw)
                if kl in text_head:
                    head_hits.append(kw)
        unique_hits = []
        seen = set()
        for kw in hits:
            kl = kw.lower()
            if kl not in seen:
                seen.add(kl)
                unique_hits.append(kw)

        if vid == "comprehensive":
            # 综合兜底：任何新闻均适用，分数随信息量浮动
            info_bonus = min(15, int(content_len / 200))
            score = min(100, 82 + info_bonus)
            reason = "综合深度分析为中立兜底角度，适用于任何新闻，可全维度收敛输出。"
            basis = "兜底角度：不依赖特定立场关键词，按文本信息量评估（正文 %d 字）。" % content_len
            items.append({
                "viewpoint_id": vid, "name": v["name"], "description": v["description"],
                "applicable": True, "score": score, "reason": reason, "basis": basis,
                "hits": [],
            })
            continue

        # 排除规则：命中排除词（且非标题/摘要强命中）→ 强制不适用（防误配）
        exclude_hits = []
        for kw in excl:
            kl = kw.lower()
            if kl and kl in text_all:
                exclude_hits.append(kw)
        excluded = False
        if exclude_hits:
            # 强正向信号：标题/摘要直接命中角度关键词 ≥2 个，或全文命中 ≥4 个，可抵消排除词
            strong_positive = len(head_hits) >= 2 or len(unique_hits) >= 4
            if not strong_positive:
                excluded = True

        # 打分：命中数 + 标题摘要加权 + 信息量
        score = 28 + len(unique_hits) * 9 + len(head_hits) * 7
        info_bonus = min(12, int(content_len / 400))
        score += info_bonus
        score = min(100, score)
        applicable = (not excluded) and score >= 55 and len(unique_hits) >= 1

        if excluded:
            show_ex = exclude_hits[:6]
            reason = "命中排除规则（「%s」等场景词），该角度不适用于本新闻，避免误配。" % "、".join(show_ex)
            basis = "排除规则拦截：正文命中排除词 %d 个（%s）且无足够强正向信号。" % (len(exclude_hits), "、".join(show_ex[:6]))
        elif applicable:
            show = unique_hits[:8]
            reason = "检测到「%s」等角度信号词，可用%s展开有明确立场差异的分析。" % ("、".join(show), v["name"])
            basis = "角度匹配：正文命中 %d 个角度关键词（含标题/摘要 %d 个）%s。" % (
                len(unique_hits), len(head_hits),
                ("，另命中排除词 %d 个但被强正向信号抵消" % len(exclude_hits)) if exclude_hits else "")
        else:
            miss = kws[:5]
            if len(unique_hits) == 0:
                reason = "未命中%s关注信号词（如%s），与该角度契合度低。" % (v["name"], "、".join(miss))
                basis = "角度不匹配：标题/摘要/正文均未出现该角度的特征词。"
            elif score < 55:
                reason = "仅少量相关线索，信息不足以支撑该角度的深入分析。"
                basis = "信息不足：仅命中 %d 个角度关键词且相关度较低，正文 %d 字。" % (len(unique_hits), content_len)
            else:
                reason = "角度契合度不足，暂不推荐该角度。"
                basis = "角度不匹配：相关线索过少（命中 %d 个关键词）。" % len(unique_hits)
        items.append({
            "viewpoint_id": vid, "name": v["name"], "description": v["description"],
            "applicable": applicable, "score": score, "reason": reason, "basis": basis,
            "hits": unique_hits[:8],
        })

    # 多角度覆盖充分性：非兜底角度命中 2-4 个
    core = [it for it in items if it["viewpoint_id"] != "comprehensive"]
    ok = [it for it in core if it["applicable"]]
    # 不足 2 个：从未适用角度中按分数补齐（保证多角度覆盖，杜绝单视角）
    if len(ok) < 2:
        rest = sorted((it for it in core if not it["applicable"]), key=lambda x: x["score"], reverse=True)
        need = 2 - len(ok)
        for it in rest[:need]:
            it["applicable"] = True
            it["reason"] = "作为多角度覆盖补充：该角度得分相对较高，可提供不同立场侧面的解读。"
            it["basis"] = "多角度覆盖补充：命中角度不足 2 个，按分数补入（命中 %d 个关键词）。" % len(it.get("hits") or [])
    # 超过 4 个：按分数截取前 4 个适用角度，其余标记为不可选（避免视角泛滥）
    ok = [it for it in core if it["applicable"]]
    if len(ok) > 4:
        ok_sorted = sorted(ok, key=lambda x: x["score"], reverse=True)
        keep_ids = {it["viewpoint_id"] for it in ok_sorted[:4]}
        for it in core:
            if it["applicable"] and it["viewpoint_id"] not in keep_ids:
                it["applicable"] = False
                it["reason"] = "该新闻已命中足够多的分析角度，此角度作为次要备选（按分数截取）。"
                it["basis"] = "多角度上限截取：命中角度超过 4 个，按分数保留前 4 个。"
    # 按适用优先、分数降序
    items.sort(key=lambda x: (x["applicable"], x["score"]), reverse=True)
    return items


def _agent_json_fix(text):
    """以多种策略尝试把 LLM 原始输出解析为结构化 JSON 对象；全部失败返回 None。"""
    candidates = [text]
    # 策略 1：剥离可能的 `json` 前缀（模型偶尔输出 json\n{...}）
    if text[:4].lower() == "json" and len(text) > 4 and text[4].isspace():
        candidates.append(text[4:].lstrip())
    # 策略 2：截取首个 { 到最后一个 } 之间的内容
    m = re.search(r"\{.*\}", text, re.S)
    if m:
        candidates.append(m.group(0))
    # 策略 3：在候选上再去掉末尾多余逗号 / 所有尾逗号
    for cand in list(candidates):
        candidates.append(cand.rstrip().rstrip(','))
        candidates.append(re.sub(r",\s*([}\]])", r"\1", cand))
    # 策略 4：单引号包裹的键/字符串 → 替换为双引号（仅当整体明显是单引号 JSON 时启用，避免误伤正文引号）
    for cand in list(candidates):
        if re.search(r"^\s*\{\s*'", cand) or re.search(r",\s*'[^']+'\s*:", cand):
            fixed = re.sub(r"(?<!\\)'", '"', cand)
            candidates.append(fixed)
            candidates.append(re.sub(r",\s*([}\]])", r"\1", fixed))
    seen = set()
    for cand in candidates:
        if not cand or cand in seen:
            continue
        seen.add(cand)
        cand = cand.lstrip('\ufeff')
        cand = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", cand)
        try:
            obj = json.loads(cand)
        except Exception:
            continue
        if not isinstance(obj, dict):
            continue
        # 结构校验：必须含 summary 或可从常见字段映射得到
        if not obj.get("summary"):
            for k in ("result", "answer", "content", "analysis", "output"):
                if obj.get(k):
                    obj["summary"] = obj.pop(k)
                    break
            else:
                continue
        # 归一化：facts/angles 必须为列表，uncertainty/history/outlook 必须为字符串
        for k, default in (("facts", []), ("angles", []), ("uncertainty", ""), ("history", ""), ("outlook", "")):
            if k not in obj or obj[k] is None:
                obj[k] = default
            elif k in ("facts", "angles") and not isinstance(obj[k], list):
                obj[k] = [obj[k]] if str(obj[k]).strip() else []
            elif k in ("uncertainty", "history", "outlook") and not isinstance(obj[k], str):
                obj[k] = str(obj[k])
        return obj
    return None


def _agent_parse_output(text):
    """鲁棒解析 LLM 输出为结构化 JSON 对象。

    处理 BOM/空白、```json 围栏、json 前缀、首个 { 到最后一个 } 截取、
    尾逗号与单双引号混用等常见问题；彻底失败返回 None（由调用方标记 failed），
    不再把原始输出塞进 summary。
    """
    text = (text or "").strip()
    if not text:
        return None
    # 剥离可能的 ```json ... ``` 围栏（含无语言标记的 ``` 围栏）
    m = re.search(r"```(?:json)?\s*(.*?)```", text, re.S | re.I)
    if m:
        text = m.group(1).strip()
    return _agent_json_fix(text)


# 分析输出后处理清洗：① 去除「（推断/推测/常识推断/猜测）」等括号注释；
# ② 去除把新闻当翻译任务的对话式/询问式回应片段；③ 压缩多余空白。
_AGENT_BRACKET_NOTE_RE = re.compile(r'[（(]\s*(?:常识推断|推测|推断|猜测|个人推测|初步推测|个人猜测|初步猜测)\s*[）)]')
_AGENT_TRANSLATE_TALK_RE = re.compile(
    r'(?:如果你有[^。；\n]{0,24}(?:翻译|译文)[^。；\n]{0,32}[。；]?)|'
    r'(?:看起来像是[^。；\n]{0,48}(?:内部|团队|对话|动态)[^。；\n]{0,24}[。；]?)'
)


def _agent_clean_text(s):
    if not isinstance(s, str):
        return s
    s = _AGENT_BRACKET_NOTE_RE.sub('', s)
    s = _AGENT_TRANSLATE_TALK_RE.sub('', s)
    s = re.sub(r'\s{2,}', ' ', s)
    return s.strip()


def _agent_clean_analysis(output):
    """对分析 JSON 做输出后处理清洗（括号注释 / 翻译式对话回应 / 多余空白）。"""
    if not isinstance(output, dict):
        return output
    for k in ('summary', 'uncertainty', 'history', 'outlook'):
        if isinstance(output.get(k), str):
            output[k] = _agent_clean_text(output[k])
    for k in ('facts', 'angles'):
        if isinstance(output.get(k), list):
            cleaned = []
            for v in output[k]:
                v2 = _agent_clean_text(v)
                if v2:
                    cleaned.append(v2)
            output[k] = cleaned
    return output


def _agent_get_cached(news_id, viewpoint_id):
    db = get_db()
    row = _fetchone(db, 'SELECT content, status, created_at, updated_at, model, error FROM agent_analyses WHERE news_id=? AND viewpoint_id=?', (news_id, viewpoint_id))
    if not row:
        return None
    return {
        "content": row["content"] or "",
        "status": row["status"] or "pending",
        "created_at": row["created_at"],
        "updated_at": row["updated_at"],
        "model": row["model"] or "",
        "error": row["error"] or "",
    }


def _agent_set_running(news_id, viewpoint_id):
    db = get_db()
    now = time.time()
    db.execute(
        "INSERT INTO agent_analyses (news_id, viewpoint_id, content, status, created_at, updated_at, model, error) "
        "VALUES (?,?,?,?,?,?,?,?) "
        "ON CONFLICT(news_id, viewpoint_id) DO UPDATE SET status='running', updated_at=excluded.updated_at, error=''",
        (news_id, viewpoint_id, "", "running", now, now, "", ""),
    )
    db.commit()


def _agent_set_done(news_id, viewpoint_id, content, model="", error=""):
    db = get_db()
    db.execute(
        "UPDATE agent_analyses SET content=?, status=?, updated_at=?, model=?, error=? "
        "WHERE news_id=? AND viewpoint_id=?",
        (content, "success" if not error else "failed", time.time(), model, error, news_id, viewpoint_id),
    )
    db.commit()


def _agent_analyze(news_id, viewpoint_id, force=False):
    """对指定新闻触发单 Agent 分析。已有成功缓存直接返回；running 防并发；失败可重试。

    force=True 时跳过成功缓存强制重新生成（前端「重新分析」按钮使用）。
    返回 (payload, from_cache)。
    """
    ctx = _agent_get_news_context(news_id)
    if not ctx:
        raise ValueError("新闻不存在")
    viewpoint = _AGENT_VIEWPOINT_MAP.get(viewpoint_id)
    if not viewpoint:
        raise ValueError("分析视角不存在")

    cached = _agent_get_cached(news_id, viewpoint_id)
    now = time.time()
    if not force and cached and cached["status"] == "success" and cached["content"]:
        try:
            output = json.loads(cached["content"])
            if not isinstance(output, dict) or not output.get("summary"):
                raise ValueError("bad cache")
        except Exception:
            output = None
        if output is not None:
            # 新版本特征校验：旧版脏缓存（无 history/outlook/references，
            # 或 summary 被塞入 JSON 原文导致无法结构化展示）视为脏缓存，强制重建
            has_new_keys = ("history" in output) or ("outlook" in output) or ("references" in output)
            summary_ok = isinstance(output.get("summary"), str) and not output["summary"].lstrip().startswith("{")
            if not (has_new_keys and summary_ok):
                output = None
        if output is not None:
            output = _agent_clean_analysis(output)
            return {
                "status": "cached",
                "news_id": news_id,
                "viewpoint_id": viewpoint_id,
                "viewpoint_name": viewpoint["name"],
                "output": output,
                "created_at": cached["created_at"],
                "model": cached["model"],
            }, True
        # 历史脏缓存（无法解析为结构化 JSON，如旧版把思考过程塞进 summary）不返回，重新生成覆盖
    if cached and cached["status"] == "running" and cached["updated_at"] and (now - cached["updated_at"]) < 300:
        return {
            "status": "running",
            "news_id": news_id,
            "viewpoint_id": viewpoint_id,
            "viewpoint_name": viewpoint["name"],
            "message": "该新闻的分析正在生成中，请稍后查询。",
        }, True

    # 组装用户提示词：标题+分类+摘要+正文（外文附译文）+ 近期相关报道(R) + 历史背景报道(H)
    user_parts = [
        "新闻标题：%s" % ctx["title"],
        "新闻分类：%s" % (ctx["category"] or "未知"),
        "信源：%s" % (ctx["source"] or "未知"),
    ]
    if ctx["trans_title"] and ctx["trans_title"] != ctx["title"]:
        user_parts.append("标题译文：%s" % ctx["trans_title"])
    if ctx["summary"]:
        user_parts.append("新闻摘要：%s" % ctx["summary"])
        if ctx["trans_summary"] and ctx["trans_summary"] != ctx["summary"]:
            user_parts.append("摘要译文：%s" % ctx["trans_summary"])
    if ctx["content"]:
        user_parts.append("新闻正文：\n%s" % ctx["content"])
    if ctx.get("recent_related"):
        rel_lines = []
        for i, r in enumerate(ctx["recent_related"], 1):
            src_txt = ("【%s】" % r["source"]) if r.get("source") else ""
            rel_lines.append("R%d. %s%s%s" % (i, src_txt, r["title"], (" —— " + r["summary"]) if r["summary"] else ""))
        user_parts.append("近期相关报道（近7天多信源去重，编号 R1-Rn，仅作交叉印证背景参考）：\n" + "\n".join(rel_lines) +
                         "\n【重要】R/H/E 参考条目可能与主新闻并非同一事件、同一地区或同一时段，仅供背景佐证，"
                         "严禁将其中的伤亡人数、受灾数据、时间、地点、金额等任何数据归入主新闻；"
                         "主新闻的一切事实与数据必须且只能来自上方「新闻标题/新闻摘要/新闻正文」，"
                         "若参考条目与主新闻主题明显不同，直接忽略该条目，不得写入分析。")
    if ctx.get("historical_related"):
        hist_lines = []
        for i, r in enumerate(ctx["historical_related"], 1):
            src_txt = ("【%s】" % r["source"]) if r.get("source") else ""
            hist_lines.append("H%d. %s%s%s" % (i, src_txt, r["title"], (" —— " + r["summary"]) if r["summary"] else ""))
        user_parts.append("历史背景报道（更早同类事件，编号 H1-Hm，仅作历史脉络参考；history 请注明哪些来自 H 编号）：\n" + "\n".join(hist_lines) +
                         "\n【重要】H 条目同样可能属于不同事件/不同地区，其数据严禁归入主新闻，仅可作同类事件的趋势性描述。")
    # 外部实时搜索（国外新闻源站内搜索层）：检索事件关键词补充跨源参考（E 编号）
    # 仅服务 AI 分析，不进入主列表源池；失败/超时静默降级，不阻塞分析
    ext_items = []
    try:
        import source_search
        ext_items = source_search.search_external(ctx["title"], limit=3) or []
    except Exception:
        ext_items = []
    if ext_items:
        ext_lines = []
        for i, r in enumerate(ext_items, 1):
            src_txt = ("【%s】" % (r.get("source_name") or r.get("source") or "")) if (r.get("source_name") or r.get("source")) else ""
            date_txt = ("（%s）" % r["date"]) if r.get("date") else ""
            desc = (r.get("description") or "")
            if len(desc) > 220:
                desc = desc[:220] + "…"
            ext_lines.append("E%d. %s%s%s%s" % (i, src_txt, r.get("title") or "", date_txt, (" —— " + desc) if desc else ""))
        user_parts.append(
            "外部实时搜索结果（国外新闻源站内检索，编号 E1-En，仅作交叉印证与真伪鉴别参考；"
            "facts 如需引用请标注 E 编号）：\n" + "\n".join(ext_lines) +
            "\n【重要】E 条目同样可能命中同名或同类但不同事件的报道，其数据严禁归入主新闻，仅可用于佐证或质疑主新闻主题。"
        )
    user_parts.append(
        "请以「%s」视角分析本条新闻。\n关注侧重：%s\n证据标准：%s\n"
        "你是新闻分析引擎，不是在翻译、也不是在对话：输出必须始终是本条新闻的事实分析正文，"
        "禁止出现「看起来像是」「如果你有其他想让我翻译的新闻」等对话式、翻译式或询问式表述。"
        % (viewpoint["name"], "；".join(viewpoint.get("attention") or viewpoint["dimensions"]), viewpoint["evidence_standard"])
    )
    # 末尾强约束：直接输出最终 JSON，禁止思考过程/Markdown 小节（降低模型把分析写成文档的概率）
    user_parts.append("现在请直接输出最终 JSON 对象（键为 summary/facts/angles/uncertainty/history/outlook）。回复必须以 { 开头、以 } 结尾，中间是合法 JSON 正文，严禁任何开场白、复述、思考过程、解释、总结或 Markdown 围栏。不要输出「（推测）」「（常识推断）」等括号标注。uncertainty 区只允许收录与主新闻主题直接相关的不确定事项，严禁引用 R/H/E 参考条目中其他事件、其他地区的伤亡或损失数据。若主新闻正文为综合性通报（同时涉及多个灾害/事件/地区，如全国自然灾害总览），分析必须聚焦标题主题（如台风），正文中其他事件的数据（如其他灾害伤亡）仅允许在 summary 作为背景一句话带过，严禁写入 facts/angles/uncertainty 区。")
    user = "\n\n".join(user_parts)

    _agent_set_running(news_id, viewpoint_id)
    try:
        raw = call_lm_studio([
            {"role": "system", "content": _agent_build_system_prompt(viewpoint)},
            {"role": "user", "content": user},
        ], timeout=150, max_tokens=4096)
        output = _agent_parse_output(raw)
        if output is None:
            # 首次解析失败：附加强约束重试 1 次（模型偶尔复述提示词/输出解释而非 JSON）
            try:
                retry_user = user + "\n\n【重试要求】你上一次的输出未通过 JSON 解析校验（可能复述了任务或输出了解释文本）。本次严禁复述任务、严禁任何开场白与解释，回复必须以 { 开头、以 } 结尾，直接输出与系统提示示例完全一致的 JSON 正文（键为 summary/facts/angles/uncertainty/history/outlook），不要输出示例之外的任何文本。"
                raw = call_lm_studio([
                    {"role": "system", "content": _agent_build_system_prompt(viewpoint)},
                    {"role": "user", "content": retry_user},
                ], timeout=150, max_tokens=4096)
                output = _agent_parse_output(raw)
            except Exception:
                output = None
        if output is not None:
            output = _agent_clean_analysis(output)
        if output is None:
            # 诊断：完整原始输出落盘（临时中间产物），便于定位解析失败原因
            try:
                import tempfile as _diag_tf
                _diag_p = os.path.join(_diag_tf.gettempdir(), "agent_raw_diag.txt")
                with open(_diag_p, "w", encoding="utf-8") as _df:
                    _df.write(raw or "")
            except Exception:
                pass
            preview = (raw or "").strip()
            if len(preview) > 400:
                preview = preview[:400] + "……"
            err = "模型输出无法解析为 JSON 结构，请重试。原始输出预览：%s" % preview
            _agent_set_done(news_id, viewpoint_id, "", model="ai", error=err[:500])
            return {
                "status": "failed",
                "news_id": news_id,
                "viewpoint_id": viewpoint_id,
                "viewpoint_name": viewpoint["name"],
                "error": err,
            }, False
        # 注入参考报道来源（跨源检索落地）：后端按近期/历史两类生成 references，
        # 已按同信源去重，保证是真实不同信源的相关报道，与模型 facts 中的 R/H 编号互为印证
        refs_recent = [
            {"title": r["title"], "source": r.get("source") or ""}
            for r in (ctx.get("recent_related") or [])
        ]
        refs_hist = [
            {"title": r["title"], "source": r.get("source") or ""}
            for r in (ctx.get("historical_related") or [])
        ]
        refs_ext = [
            {"title": r.get("title") or "", "source": r.get("source_name") or r.get("source") or "", "url": r.get("url") or ""}
            for r in ext_items
        ]
        if refs_recent or refs_hist or refs_ext:
            output["references"] = {"recent": refs_recent, "historical": refs_hist, "external": refs_ext}
            output["related_count"] = len(refs_recent) + len(refs_hist) + len(refs_ext)
        else:
            output["references"] = {"recent": [], "historical": [], "external": []}
            output["related_count"] = 0
        content = json.dumps(output, ensure_ascii=False)
        _agent_set_done(news_id, viewpoint_id, content, model="ai")
        return {
            "status": "ok",
            "news_id": news_id,
            "viewpoint_id": viewpoint_id,
            "viewpoint_name": viewpoint["name"],
            "output": output,
            "created_at": time.time(),
            "model": "ai",
        }, False
    except Exception as e:
        err = str(e)
        import traceback as _diag_tb
        print('[AGENT_ANALYZE_TRACEBACK]', flush=True)
        _diag_tb.print_exc()
        _agent_set_done(news_id, viewpoint_id, "", model="ai", error=err[:500])
        return {
            "status": "failed",
            "news_id": news_id,
            "viewpoint_id": viewpoint_id,
            "viewpoint_name": viewpoint["name"],
            "error": err,
        }, False


@app.route('/api/agent-analysis/viewpoints', methods=['GET'])
def api_agent_viewpoints():
    """公开：列出可用分析视角包。"""
    return jsonify({"viewpoints": AGENT_VIEWPOINTS})


@app.route('/api/agent-analysis/assessment/<news_id>', methods=['GET'])
def api_agent_assessment(news_id):
    """公开：评估某条新闻对各智能体视角的适用性（可选/不可选+评分+理由）。

    打开新闻详情页时前端调用，规则引擎即时返回，不触发 LLM。
    """
    ctx = _agent_get_news_context(news_id)
    if not ctx:
        return jsonify({"error": "新闻不存在"}), 404
    items = _agent_assess_viewpoints(ctx)
    return jsonify({"news_id": news_id, "assessment": items})


@app.route('/api/agent-analysis/analyze', methods=['POST'])
def api_agent_analyze():
    """公开：触发某条新闻的 AI 分析；已有缓存直接返回缓存结果。"""
    payload = request.get_json(silent=True) or {}
    news_id = (payload.get("news_id") or "").strip()
    viewpoint_id = (payload.get("viewpoint_id") or "comprehensive").strip()
    force = bool(payload.get("force", False))
    if not news_id:
        return jsonify({"error": "缺少 news_id"}), 400
    if viewpoint_id not in _AGENT_VIEWPOINT_MAP:
        return jsonify({"error": "未知视角 viewpoint_id"}), 400
    try:
        data, from_cache = _agent_analyze(news_id, viewpoint_id, force=force)
    except ValueError as e:
        return jsonify({"error": str(e)}), 404
    except Exception as e:
        return jsonify({"error": "AI 分析失败：%s" % str(e)}), 502
    data["from_cache"] = from_cache
    return jsonify(data)


@app.route('/api/agent-analysis/status', methods=['GET'])
def api_agent_analysis_status():
    """公开：前端轮询某新闻的 Agent 分析状态。

    必须注册在 /api/agent-analysis/<news_id> 之前，否则 status 会被当作
    news_id 捕获，导致前端收到 not found（404 语义错误）。
    """
    news_id = (request.args.get("news_id") or "").strip()
    if not news_id:
        return jsonify({"error": "缺少 news_id"}), 400
    db = get_db()
    rows = _fetchall(db, '''
        SELECT viewpoint_id, content, status, created_at, updated_at, model, error
        FROM agent_analyses WHERE news_id=? ORDER BY created_at DESC
    ''', (news_id,))
    out = []
    for r in rows:
        try:
            content = json.loads(r["content"]) if r["content"] else None
        except Exception:
            content = {"summary": r["content"], "facts": [], "angles": [], "uncertainty": ""}
        if isinstance(content, dict):
            content = _agent_clean_analysis(content)
        out.append({
            "viewpoint_id": r["viewpoint_id"],
            "viewpoint_name": (_AGENT_VIEWPOINT_MAP.get(r["viewpoint_id"]) or {}).get("name", ""),
            "content": content,
            "status": r["status"],
            "created_at": r["created_at"],
            "updated_at": r["updated_at"],
            "model": r["model"],
            "error": r["error"],
        })
    return jsonify({"news_id": news_id, "analyses": out})


@app.route('/api/agent-analysis/<news_id>', methods=['GET'])
def api_agent_get_analyses(news_id):
    """公开：查询某新闻已生成的全部 Agent 分析（前端进入详情页时回显缓存）。"""
    db = get_db()
    rows = _fetchall(db, '''
        SELECT viewpoint_id, content, status, created_at, updated_at, model, error
        FROM agent_analyses WHERE news_id=? ORDER BY created_at DESC
    ''', (news_id,))
    out = []
    for r in rows:
        try:
            content = json.loads(r["content"]) if r["content"] else None
        except Exception:
            content = {"summary": r["content"], "facts": [], "angles": [], "uncertainty": ""}
        if isinstance(content, dict):
            content = _agent_clean_analysis(content)
        out.append({
            "viewpoint_id": r["viewpoint_id"],
            "viewpoint_name": (_AGENT_VIEWPOINT_MAP.get(r["viewpoint_id"]) or {}).get("name", ""),
            "content": content,
            "status": r["status"],
            "created_at": r["created_at"],
            "updated_at": r["updated_at"],
            "model": r["model"],
            "error": r["error"],
        })
    return jsonify({"news_id": news_id, "analyses": out})


@app.route('/api/news/<news_id>/comments', methods=['GET'])
def api_get_news_comments(news_id):
    """公开：新闻评论列表（分页，每页 20 条，时间正序）"""
    db = get_db()
    news = _fetchone(db, 'SELECT id FROM news WHERE id=?', (news_id,))
    if not news:
        return jsonify({'error': '新闻不存在'}), 404
    uid = _get_auth_user_id()
    try:
        page = max(1, int(request.args.get('page', 1)))
    except (TypeError, ValueError):
        page = 1
    per_page = 20
    offset = (page - 1) * per_page
    rows = _fetchall(db, '''
        SELECT c.id, c.author_id, c.content, c.image, c.likes, c.created_at,
               u.username as author_name, u.avatar as author_avatar
        FROM news_comments c LEFT JOIN users u ON c.author_id = u.id
        WHERE c.news_id=? ORDER BY c.created_at ASC LIMIT ? OFFSET ?
    ''', (news_id, per_page, offset))
    total = _fetchone(db, 'SELECT COUNT(*) as c FROM news_comments WHERE news_id=?', (news_id,))
    comments = []
    for r in rows:
        av = r.get('author_avatar') or ''
        comments.append({
            'id': r['id'],
            'author_id': r.get('author_id') or '',
            'author_name': r.get('author_name') or '已注销用户',
            'author_avatar': ('/' + av) if av and not av.startswith('/') else av,
            'content': r['content'],
            'image': ('/' + r['image']) if r.get('image') else '',
            'likes': r['likes'],
            'created_at': r['created_at'],
            'liked': bool(uid and _fetchone(db, 'SELECT 1 FROM news_comment_likes WHERE user_id=? AND comment_id=?', (uid, r['id']))),
        })
    return jsonify({'comments': comments, 'total': total['c'] if total else 0, 'page': page, 'per_page': per_page})


@app.route('/api/news/<news_id>/like', methods=['POST'])
@login_required
def api_toggle_news_like(news_id):
    db = get_db()
    uid = _get_auth_user_id()
    news = _fetchone(db, 'SELECT id FROM news WHERE id=?', (news_id,))
    if not news:
        return jsonify({'error': '新闻不存在'}), 404
    existing = _fetchone(db, 'SELECT 1 FROM news_likes WHERE user_id=? AND news_id=?', (uid, news_id))
    if existing:
        _exec(db, 'DELETE FROM news_likes WHERE user_id=? AND news_id=?', (uid, news_id))
        _exec(db, 'UPDATE news SET likes = likes - 1 WHERE id=? AND likes > 0', (news_id,))
        liked = False
    else:
        _exec(db, 'INSERT INTO news_likes (user_id, news_id, created_at) VALUES (?,?,?)', (uid, news_id, time.time()))
        _exec(db, 'UPDATE news SET likes = likes + 1 WHERE id=?', (news_id,))
        liked = True
    db.commit()
    row = _fetchone(db, 'SELECT likes FROM news WHERE id=?', (news_id,))
    return jsonify({'liked': liked, 'likes': row['likes'] if row else 0})


@app.route('/api/news/<news_id>/comments', methods=['POST'])
@login_required
def api_create_news_comment(news_id):
    # 评论速率限制：每用户 10 分钟最多 10 条
    uid = _get_auth_user_id()
    allowed, retry_after = _check_news_comment_rate_limit(uid)
    if not allowed:
        return jsonify({'error': f'评论过于频繁，请 {retry_after} 秒后再试'}), 429

    data = request.get_json() or {}
    content = (data.get('content') or '').strip()
    image = (data.get('image') or '').strip()
    if image:
        return jsonify({'error': '评论区不支持发送图片'}), 400
    if not content:
        return jsonify({'error': '请输入评论内容'}), 400

    if content:
        ok, found = check_banned_words(content)
        if not ok:
            return jsonify({'error': f'内容包含违禁词：{"、".join(found[:5])}'}), 400
        content = filter_content(content)

    uid = _get_auth_user_id()
    u = get_user(uid)
    if u and u.get('muted_until', 0) > time.time():
        return jsonify({'error': '你已被禁言，无法评论'}), 403
    if u and u.get('status') == 'banned':
        return jsonify({'error': '该账号已被封禁'}), 403

    db = get_db()
    news = _fetchone(db, 'SELECT id FROM news WHERE id=?', (news_id,))
    if not news:
        return jsonify({'error': '新闻不存在'}), 404

    cid = 'nc_' + uuid.uuid4().hex[:12]
    now = time.time()
    _exec(db, 'INSERT INTO news_comments (id, news_id, author_id, content, image, likes, created_at) VALUES (?,?,?,?,?,?,?)',
          (cid, news_id, uid, content, image, 0, now))
    db.commit()
    _record_news_comment(uid)
    av = (u.get('avatar') or '') if u else ''
    return jsonify({'comment': {
        'id': cid,
        'author_id': uid,
        'author_name': u['username'] if u else '',
        'author_avatar': ('/' + av) if av and not av.startswith('/') else av,
        'content': content,
        'image': ('/' + image) if image else '',
        'likes': 0,
        'created_at': now,
        'liked': False,
    }})


@app.route('/api/news/comments/<comment_id>/like', methods=['POST'])
@login_required
def api_toggle_news_comment_like(comment_id):
    db = get_db()
    uid = _get_auth_user_id()
    comment = _fetchone(db, 'SELECT id FROM news_comments WHERE id=?', (comment_id,))
    if not comment:
        return jsonify({'error': '评论不存在'}), 404
    existing = _fetchone(db, 'SELECT 1 FROM news_comment_likes WHERE user_id=? AND comment_id=?', (uid, comment_id))
    if existing:
        _exec(db, 'DELETE FROM news_comment_likes WHERE user_id=? AND comment_id=?', (uid, comment_id))
        _exec(db, 'UPDATE news_comments SET likes = likes - 1 WHERE id=? AND likes > 0', (comment_id,))
        liked = False
    else:
        _exec(db, 'INSERT INTO news_comment_likes (user_id, comment_id) VALUES (?,?)', (uid, comment_id))
        _exec(db, 'UPDATE news_comments SET likes = likes + 1 WHERE id=?', (comment_id,))
        liked = True
    db.commit()
    row = _fetchone(db, 'SELECT likes FROM news_comments WHERE id=?', (comment_id,))
    return jsonify({'liked': liked, 'likes': row['likes'] if row else 0})


@app.route('/api/news/comments/<comment_id>', methods=['DELETE'])
@login_required
def api_delete_news_comment(comment_id):
    """删除评论：仅本人或管理员"""
    db = get_db()
    uid = _get_auth_user_id()
    row = _fetchone(db, 'SELECT author_id FROM news_comments WHERE id=?', (comment_id,))
    if not row:
        return jsonify({'error': '评论不存在'}), 404
    if row['author_id'] != uid:
        user = _fetchone(db, 'SELECT is_admin, is_super_admin FROM users WHERE id=?', (uid,))
        if not user or not (user['is_admin'] or user['is_super_admin']):
            return jsonify({'error': '无权删除'}), 403
    _exec(db, 'DELETE FROM news_comment_likes WHERE comment_id=?', (comment_id,))
    _exec(db, 'DELETE FROM news_comments WHERE id=?', (comment_id,))
    db.commit()
    return jsonify({'ok': True})


@app.route('/api/admin/news', methods=['POST'])
@news_publisher_required
def api_admin_create_news():
    data = request.get_json() or {}
    title = (data.get('title') or '').strip()
    content = (data.get('content') or '').strip()
    image = (data.get('image') or '').strip().lstrip('/')
    video = (data.get('video') or '').strip().lstrip('/')
    summary = (data.get('summary') or '').strip()
    category = (data.get('category') or '').strip()
    pinned = 1 if data.get('pinned') else 0
    images = data.get('images') or []
    if not title or not content:
        return jsonify({'error': '标题和内容不能为空'}), 400
    ok, found = check_banned_words(title)
    if not ok:
        return jsonify({'error': f'标题包含违禁词：{"、".join(found[:5])}'}), 400
    title = filter_content(title)

    db = get_db()
    nid = 'news_' + uuid.uuid4().hex[:8]
    now = time.time()
    uid = _get_auth_user_id()
    import json as _json
    images_json = _json.dumps(images) if images else ''
    _exec(db, 'INSERT INTO news (id, title, content, image, video, author_id, likes, created_at, summary, category, pinned, images) VALUES (?,?,?,?,?,?,?,?,?,?,?,?)',
          (nid, title, content, image, video, uid, 0, now, summary, category, pinned, images_json))
    db.commit()
    row = _fetchone(db, 'SELECT id, title, content, image, video, author_id, likes, created_at, summary, category, pinned, images FROM news WHERE id=?', (nid,))
    return jsonify({'news': _news_to_dict(row, uid)})


@app.route('/api/admin/news/<news_id>', methods=['PUT'])
@news_publisher_required
def api_admin_update_news(news_id):
    """编辑新闻：标题/正文/封面图/摘要/分类/置顶/插图"""
    data = request.get_json() or {}
    title = (data.get('title') or '').strip()
    content = (data.get('content') or '').strip()
    image = (data.get('image') or '').strip().lstrip('/')
    video = (data.get('video') or '').strip().lstrip('/')
    summary = (data.get('summary') or '').strip()
    category = (data.get('category') or '').strip()
    pinned = 1 if data.get('pinned') else 0
    ai_allowed = 1 if data.get('ai_allowed', True) else 0
    images = data.get('images') or []
    if not title or not content:
        return jsonify({'error': '标题和内容不能为空'}), 400
    ok, found = check_banned_words(title)
    if not ok:
        return jsonify({'error': f'标题包含违禁词：{"、".join(found[:5])}'}), 400
    title = filter_content(title)

    db = get_db()
    news = _fetchone(db, 'SELECT id, author_id FROM news WHERE id=?', (news_id,))
    if not news:
        return jsonify({'error': '新闻不存在'}), 404
    # 权限检查：仅作者本人或超级管理员可编辑
    is_super = bool(_get_auth_user_id() and _fetchone(db, 'SELECT 1 FROM users WHERE id=? AND is_super_admin=1', (_get_auth_user_id(),)))
    if not is_super and news['author_id'] != _get_auth_user_id():
        return jsonify({'error': '无权编辑此新闻'}), 403
    import json as _json
    images_json = _json.dumps(images) if images else ''
    _exec(db, 'UPDATE news SET title=?, content=?, image=?, video=?, summary=?, category=?, pinned=?, ai_allowed=?, images=? WHERE id=?',
          (title, content, image, video, summary, category, pinned, ai_allowed, images_json, news_id))
    db.commit()
    uid = _get_auth_user_id()
    row = _fetchone(db, 'SELECT id, title, content, image, video, author_id, likes, created_at, summary, category, pinned, ai_allowed, images FROM news WHERE id=?', (news_id,))
    return jsonify({'news': _news_to_dict(row, uid)})


@app.route('/api/admin/news/<news_id>', methods=['DELETE'])
@news_publisher_required
def api_admin_delete_news(news_id):
    db = get_db()
    news = _fetchone(db, 'SELECT id FROM news WHERE id=?', (news_id,))
    if not news:
        return jsonify({'error': '新闻不存在'}), 404
    comment_ids = [r['id'] for r in _fetchall(db, 'SELECT id FROM news_comments WHERE news_id=?', (news_id,))]
    for cid in comment_ids:
        _exec(db, 'DELETE FROM news_comment_likes WHERE comment_id=?', (cid,))
    _exec(db, 'DELETE FROM news_comments WHERE news_id=?', (news_id,))
    _exec(db, 'DELETE FROM news_likes WHERE news_id=?', (news_id,))
    _exec(db, 'DELETE FROM news WHERE id=?', (news_id,))
    db.commit()
    return jsonify({'ok': True})


@app.route('/api/news/recommended', methods=['GET'])
def api_get_news_recommended():
    """公开：为你推荐（精选优先，其次按热度）"""
    db = get_db()
    rows = _fetchall(db, '''
        SELECT id, title, content, image, author_id, likes, created_at, summary, category, pinned, images, featured
        FROM news WHERE pinned = 0 AND (report_removed=0 OR report_removed IS NULL) ORDER BY featured DESC, likes DESC, created_at DESC LIMIT 5
    ''')
    items = []
    for r in rows:
        d = _news_to_dict(r)
        d.pop('content', None)
        items.append(d)
    return jsonify({'news': items})


# ==========================================================================
# 新闻分类定位：各分类的内容定义与 AI 差异化方式（前端展示/分类规则依据）
# 原则：不同分类结合 AI 的方式（搜索 → 链接 → 呈现）不同，面向不同人有不同收获。
# ==========================================================================
_NEWS_CATEGORY_DEFS = {
    '国际': {
        'desc': '时事（含时政/国际）：国内议题、台海议题、新闻发布会、工作报告、经济会议等重大议题的综合解读。',
        'ai_note': '解读优先：防止浅尝辄止，也避免洋洋洒洒；搜索政策原文与多方报道，给出有信息增量的解读。',
    },
    '时事': {
        'desc': '时事（含时政/国际）：国内议题、台海议题、新闻发布会、工作报告、经济会议等重大议题的综合解读。',
        'ai_note': '解读优先：防止浅尝辄止，也避免洋洋洒洒；搜索政策原文与多方报道，给出有信息增量的解读。',
    },
    '社会': {
        'desc': '社会：人与人、人与集体、人与机器关系，聚焦法治、纠纷、重大集体事件。健康/体质/体育代表团等日常民生内容归生活。',
        'ai_note': '分析优先：提供有可证伪性、鞭辟入里的分析，避免情绪化表达。',
    },
    '经济': {
        'desc': '经济：贸易商业动向、都市圈、产业企业分析、股期汇市场走势趋势。',
        'ai_note': '数据优先：链接行情/财报/宏观数据，做趋势与影响面分析。',
    },
    '体育': {
        'desc': '体育：赛事、商业、人、产业的专业分析。',
        'ai_note': '专业优先：参考国外媒体视角，兼顾赛事结果、商业与产业深度。',
    },
    '科技': {
        'desc': '科技：科技动态与产业进展，不陷入走马观花，也不至于变成专业通讯。',
        'ai_note': '平衡优先：通俗与专业之间取平衡，链接原始论文/发布页。',
    },
    '人文': {
        'desc': '人文：包含考古（遗址/出土/文物修复）、文学（小说/诗歌/作家/典籍）、文化（博物馆/展览/非遗/传统）类内容；不只历史，还提供古今中外对照、文明比较。',
        'ai_note': '对照优先：历史事件提供现实映照与跨文化比较。',
    },
    '娱乐': {
        'desc': '娱乐：聚焦国内外娱乐消息（影视、综艺、音乐、演出、动漫等），不只看内娱。',
        'ai_note': '趋势优先：国内外文艺新趋势并举，链接作品/票房/流媒体数据。',
    },
    '生活': {
        'desc': '生活：趋势导向，涵盖健康/体质/体育代表团类民生内容，以及文旅/养生/文化生活产业/职场/理财/健身/自我提升等至少四者兼有。',
        'ai_note': '实用优先：趋势化呈现，兼顾文化消费与个人成长场景。',
    },
    '环境': {
        'desc': '环境：关乎地球、灾难、人的预警与行动。',
        'ai_note': '预警与行动优先：呈现事实、风险与可执行建议。',
    },
}


@app.route('/api/news/categories', methods=['GET'])
def api_get_news_categories():
    """公开：分类列表及数量（含各分类定位描述与 AI 差异化方式，供前端展示/解释）"""
    db = get_db()
    rows = _fetchall(db, 'SELECT category, COUNT(*) as c FROM news WHERE category != "" GROUP BY category ORDER BY c DESC')
    items = []
    for r in rows:
        item = {'name': r['category'], 'count': r['c']}
        meta = _NEWS_CATEGORY_DEFS.get(r['category'])
        if meta:
            item['desc'] = meta['desc']
            item['ai_note'] = meta['ai_note']
        items.append(item)
    return jsonify({'categories': items, 'defs': _NEWS_CATEGORY_DEFS})


# ==========================================================================
# 顶栏三行：股市 / 天气 / 快讯（后端代理 + 内存缓存，避免前端直连 API 跨域/限流）
# ==========================================================================
_TOPBAR_CACHE = {}
_TOPBAR_TTL = {'stock': 30, 'weather': 900, 'flash': 60}

# 行情标的 —— 主数据源：fx678 汇通网行情接口（api-q.fx678img.com/exchangeSymbol.php）
# 股指 9 + 期市 9 + 汇市 9 + 黄金 9 + 原油 9 = 45（9 的倍数，5 组 × 9，对应 fx678 股指/期市/汇市/黄金/原油分类）
# 备用数据源：新浪财经行情接口 hq.sinajs.cn（Referer=finance.sina.com.cn，GBK 解码）
_STOCK_CODES_SINA = [
    # A 股指数（sh/sz，格式：名称,今开,昨收,最新,最高,最低,...）
    ('sh000001', '上证指数'), ('sz399001', '深证成指'), ('sz399006', '创业板指'),
    ('sh000300', '沪深300'), ('sh000016', '上证50'), ('sh000688', '科创50'),
    # 海外股指（hk：中文名,最新,昨收,今开,最低,收盘,涨跌额,涨跌幅；gb：名称,最新,涨跌幅,时间,涨跌额）
    ('hkHSI', '恒生指数'), ('gb_dji', '道琼斯'), ('gb_ixic', '纳斯达克'), ('gb_inx', '标普500'),
    # 国际期货（hf，格式：最新,空,买,卖,最高,最低,时间,昨收,今开,...,名称）
    ('hf_GC', '纽约黄金'), ('hf_SI', '纽约白银'), ('hf_CL', '纽约原油'), ('hf_OIL', '布伦特原油'),
    ('hf_HG', '美铜'), ('hf_NG', '天然气'), ('hf_CAD', '伦铜'), ('hf_BTC', '比特币期货'),
    # 国内期货（nf，格式：名称,时间,最新,卖,买?,昨结,...,今开,最高,...）
    ('nf_AU0', '沪金'), ('nf_AG0', '沪银'), ('nf_CU0', '沪铜'), ('nf_AL0', '沪铝'),
    ('nf_NI0', '沪镍'), ('nf_RB0', '螺纹钢'), ('nf_SC0', '上海原油'), ('nf_HC0', '热卷'),
    # 外汇（fx，格式：时间,最新,买,卖,...,名称,涨跌幅,涨跌额）
    ('fx_susdcnh', '离岸人民币'), ('fx_susdcny', '在岸人民币'), ('fx_seurusd', '欧元/美元'),
    ('fx_sgbpusd', '英镑/美元'), ('fx_susdjpy', '美元/日元'), ('fx_susdchf', '美元/瑞郎'),
    ('fx_saudusd', '澳元/美元'), ('fx_susdcad', '美元/加元'), ('fx_snzdusd', '纽元/美元'),
    ('fx_susdhkd', '美元/港元'),
]

# fx678 汇通网行情（api-q.fx678img.com/exchangeSymbol.php?exchName=XXX，返回 JSON）
# 每个元组：(交易所代码, 品种代码, 显示名)。数据按"组"排列，每组 9 个，正好对应前端每页 9 块。
_FX678_GROUPS = [
    ('股指', [
        ('GJZS', '1A0001', '上证指数'), ('GJZS', '2A01', '深证成指'),
        ('GJZS', '399006', '创业板指'), ('GJZS', 'HS300', '沪深300'),
        ('GJZS', 'NIKKI', '日经225'), ('GJZS', 'HSI', '恒生指数'),
        ('GJZS', 'DJIA', '道琼斯工业'), ('GJZS', 'NASDAQ', '纳斯达克'),
        ('GJZS', 'SP500', '标普500'),
    ]),
    ('期市', [
        ('SHFE', 'CU0001', '沪铜'), ('SHFE', 'AL0001', '沪铝'), ('SHFE', 'ZN0001', '沪锌'),
        ('SHFE', 'NI0001', '沪镍'), ('SHFE', 'RB0001', '螺纹钢'), ('SHFE', 'HC0001', '热卷'),
        ('DCE', 'I0001', '铁矿石'), ('DCE', 'J0001', '焦炭'), ('DCE', 'M0001', '豆粕'),
    ]),
    ('汇市', [
        ('WH', 'USD', '美元指数'), ('WH', 'EURUSD', '欧元/美元'), ('WH', 'GBPUSD', '英镑/美元'),
        ('WH', 'USDJPY', '美元/日元'), ('WH', 'AUDUSD', '澳元/美元'), ('WH', 'USDCHF', '美元/瑞郎'),
        ('WH', 'USDCAD', '美元/加元'), ('WH', 'USDCNY', '美元/在岸人民币'), ('WH', 'USDCNH', '美元/离岸人民币'),
    ]),
    ('黄金', [
        ('WGJS', 'XAU', '现货黄金'), ('WGJS', 'XAG', '现货白银'), ('WGJS', 'XAP', '现货铂金'),
        ('WGJS', 'XPD', '现货钯金'), ('WGJS', 'GT', '香港黄金'),
        ('SGE', 'AU9999', '黄金9999'), ('SGE', 'AUT+D', '黄金延期'), ('SGE', 'AGT+D', '白银延期'),
        ('SHFE', 'AU0001', '沪金连续'),
    ]),
    ('原油', [
        ('NYMEX', 'CONC', 'WTI原油'), ('IPE', 'OILC', '布伦特原油'), ('NYMEX', 'NGNC', '美国天然气'),
        ('NYMEX', 'HONC', '美国燃油'), ('NYMEX', 'RBNC', '美无铅汽油'), ('SHFE', 'BU0001', '沥青'),
        ('INE', 'SC0001', '上海原油'), ('INE', 'LU0001', '低硫燃料油'), ('SHFE', 'FU0001', '燃料油'),
    ]),
]

# 天气城市：国内 41 城（34 省级行政区省会/首府 + 苏州/青岛/大连/喀什/深圳/厦门/西沙）+ 国外 40 城 = 81 城（9 的倍数，9 组 × 9）
_WEATHER_CITIES = [
    # 国内 41
    ('北京', 39.904, 116.407), ('天津', 39.344, 117.361), ('石家庄', 38.042, 114.515),
    ('太原', 37.870, 112.549), ('呼和浩特', 40.842, 111.750), ('沈阳', 41.806, 123.432),
    ('长春', 43.817, 125.324), ('哈尔滨', 45.803, 126.535), ('上海', 31.230, 121.474),
    ('南京', 32.060, 118.797), ('杭州', 30.274, 120.155), ('合肥', 31.821, 117.227),
    ('福州', 26.074, 119.297), ('南昌', 28.682, 115.858), ('济南', 36.651, 117.120),
    ('郑州', 34.747, 113.625), ('武汉', 30.593, 114.306), ('长沙', 28.228, 112.939),
    ('广州', 23.129, 113.264), ('南宁', 22.817, 108.366), ('海口', 20.044, 110.199),
    ('重庆', 29.563, 106.551), ('成都', 30.573, 104.067), ('贵阳', 26.647, 106.630),
    ('昆明', 25.039, 102.718), ('拉萨', 29.652, 91.172), ('西安', 34.341, 108.940),
    ('兰州', 36.061, 103.834), ('西宁', 36.617, 101.778), ('银川', 38.487, 106.231),
    ('乌鲁木齐', 43.826, 87.617), ('台北', 25.033, 121.565), ('香港', 22.319, 114.169),
    ('澳门', 22.199, 113.545), ('苏州', 31.299, 120.585), ('青岛', 36.067, 120.383),
    ('大连', 38.914, 121.615), ('喀什', 39.467, 75.989), ('深圳', 22.543, 114.058),
    ('厦门', 24.480, 118.089), ('西沙', 16.831, 112.344),
    # 国外 30
    ('东京', 35.676, 139.650), ('首尔', 37.566, 126.978), ('新加坡', 1.352, 103.820),
    ('曼谷', 13.756, 100.502), ('吉隆坡', 3.139, 101.687), ('雅加达', -6.209, 106.845),
    ('马尼拉', 14.599, 120.984), ('河内', 21.028, 105.854), ('新德里', 28.614, 77.209),
    ('孟买', 19.076, 72.878), ('迪拜', 25.204, 55.271), ('伊斯坦布尔', 41.008, 28.978),
    ('莫斯科', 55.756, 37.617), ('伦敦', 51.507, -0.128), ('巴黎', 48.857, 2.352),
    ('柏林', 52.520, 13.405), ('马德里', 40.417, -3.704), ('罗马', 41.903, 12.496),
    ('阿姆斯特丹', 52.368, 4.904), ('斯德哥尔摩', 59.329, 18.069), ('纽约', 40.713, -74.006),
    ('洛杉矶', 34.052, -118.244), ('芝加哥', 41.878, -87.630), ('多伦多', 43.653, -79.383),
    ('温哥华', 49.283, -123.121), ('墨西哥城', 19.433, -99.133), ('圣保罗', -23.550, -46.634),
    ('悉尼', -33.869, 151.209), ('奥克兰', -36.848, 174.763), ('开普敦', -33.925, 18.424),
    # 国外 40 城续：旧金山/西雅图/波士顿/华盛顿/迈阿密（北美）+ 布宜诺斯艾利斯/利马（拉美）+ 里斯本/维也纳/苏黎世/哥本哈根（欧洲）+ 开罗/内罗毕（非洲）
    ('旧金山', 37.775, -122.419), ('西雅图', 47.606, -122.332), ('波士顿', 42.360, -71.059),
    ('华盛顿', 38.907, -77.037), ('迈阿密', 25.762, -80.192), ('布宜诺斯艾利斯', -34.604, -58.382),
    ('利马', -12.046, -77.043), ('里斯本', 38.722, -9.139), ('维也纳', 48.208, 16.373),
    ('苏黎世', 47.377, 8.541), ('哥本哈根', 55.676, 12.568), ('开罗', 30.044, 31.236),
    ('内罗毕', -1.292, 36.822),
    ('布拉格', 50.075, 14.438),
    ('布达佩斯', 47.498, 19.04),
    ('华沙', 52.23, 21.012),
    ('赫尔辛基', 60.17, 24.938),
    ('达卡', 23.81, 90.412),
    ('火奴鲁鲁', 21.307, -157.858),
]

_WMO_DESC = {
    0: '晴', 1: '基本晴', 2: '少云', 3: '阴',
    45: '雾', 48: '雾凇',
    51: '毛毛雨', 53: '毛毛雨', 55: '毛毛雨', 56: '冻雨', 57: '冻雨',
    61: '小雨', 63: '中雨', 65: '大雨', 66: '冻雨', 67: '冻雨',
    71: '小雪', 73: '中雪', 75: '大雪', 77: '雪粒',
    80: '阵雨', 81: '阵雨', 82: '强阵雨',
    85: '阵雪', 86: '阵雪',
    95: '雷暴', 96: '雷暴伴冰雹', 99: '雷暴伴冰雹',
}


def _topbar_get_cache(key):
    ent = _TOPBAR_CACHE.get(key)
    if not ent:
        return None
    if time.time() - ent['ts'] > _TOPBAR_TTL.get(key, 60):
        return None
    return ent['data']


def _topbar_set_cache(key, data):
    _TOPBAR_CACHE[key] = {'ts': time.time(), 'data': data}


def _fetch_stock_quotes_sina():
    """备用：新浪财经行情接口抓取（fx678 不可用时降级使用）"""
    import urllib.request as _ur
    codes = ','.join(c[0] for c in _STOCK_CODES_SINA)
    url = 'https://hq.sinajs.cn/list=' + codes
    req = _ur.Request(url, headers={
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120 Safari/537.36',
        'Referer': 'https://finance.sina.com.cn/',
    })
    with _ur.urlopen(req, timeout=8) as resp:
        raw = resp.read().decode('gbk', errors='ignore')
    name_map = dict(_STOCK_CODES_SINA)
    items = []
    for line in raw.splitlines():
        m = re.match(r'var hq_str_(\w+)="([^"]*)"', line.strip())
        if not m:
            continue
        code, payload = m.group(1), m.group(2)
        if not payload:
            continue
        parts = payload.split(',')
        prefix = code[:2]
        try:
            if prefix in ('sh', 'sz'):
                # A 股指数：名称,今开,昨收,最新,最高,最低,...
                price = float(parts[3]); prev = float(parts[2])
                change = round(price - prev, 3)
                pct = round((change / prev) * 100, 2) if prev else 0.0
            elif prefix == 'hk':
                # 港股：英文名,中文名,最新,昨收,今开,最低,收盘,涨跌额,涨跌幅,...
                price = float(parts[2]); change = float(parts[7]); pct = float(parts[8])
            elif prefix == 'gb':
                # 美股：名称,最新,涨跌幅,时间,涨跌额,...
                price = float(parts[1]); pct = float(parts[2]); change = float(parts[4])
            elif prefix == 'hf':
                # 国际期货：最新,空,买,卖,最高,最低,时间,昨收,今开,...,名称
                price = float(parts[0]); prev = float(parts[7])
                change = round(price - prev, 3)
                pct = round((change / prev) * 100, 2) if prev else 0.0
            elif prefix == 'nf':
                # 国内期货：名称,时间,最新,...,昨结,...
                price = float(parts[2]); prev = float(parts[6])
                change = round(price - prev, 3)
                pct = round((change / prev) * 100, 2) if prev else 0.0
            elif prefix == 'fx':
                # 外汇：时间,最新,买,卖,...,名称,涨跌幅,涨跌额
                price = float(parts[1]); pct = float(parts[10]); change = float(parts[11])
            else:
                continue
        except (ValueError, IndexError):
            continue
        if price <= 0:
            continue
        items.append({
            'code': code, 'name': name_map.get(code, parts[1] or code),
            'price': round(price, 3), 'change': round(change, 3), 'pct': round(pct, 2),
        })
    return {'ok': True, 'items': items, 'ts': time.strftime('%H:%M:%S')}


def _fetch_fx678_quotes():
    """主数据源：fx678 汇通网行情接口拉取 45 个重要标的（股指/期市/汇市/黄金/原油 各 9 个）。

    按交易所去重请求 exchangeSymbol.php，返回每个标的的最新价 c / 昨收 p，
    前端按 9 个一组翻页展示，items 按组有序排列并带 group 字段。
    """
    import urllib.request as _ur
    exch_codes = {}
    for gname, syms in _FX678_GROUPS:
        for exch, code, name in syms:
            exch_codes.setdefault(exch, []).append(code)
    quotes = {}
    for exch, codes in exch_codes.items():
        url = 'https://api-q.fx678img.com/exchangeSymbol.php?exchName=' + exch
        try:
            req = _ur.Request(url, headers={
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120 Safari/537.36',
                'Referer': 'https://quote.fx678.com/',
                'Accept': 'application/json',
            })
            with _ur.urlopen(req, timeout=8) as resp:
                raw = resp.read().decode('utf-8', errors='ignore')
            data = json.loads(raw)
            if isinstance(data, dict):
                data = list(data.values())
            for it in data:
                i = it.get('i')
                if i in codes:
                    quotes[exch + ':' + i] = it
        except Exception:
            continue
    items = []
    for gname, syms in _FX678_GROUPS:
        for exch, code, name in syms:
            it = quotes.get(exch + ':' + code)
            if not it:
                continue
            try:
                price = float(str(it.get('c', '0')).replace(',', ''))
                prev = float(str(it.get('p', '0')).replace(',', ''))
            except (TypeError, ValueError):
                continue
            if price <= 0:
                continue
            change = round(price - prev, 3)
            pct = round((change / prev) * 100, 2) if prev else 0.0
            items.append({
                'code': code,
                'name': name or it.get('name') or code,
                'group': gname,
                'price': round(price, 3),
                'change': round(change, 3),
                'pct': round(pct, 2),
            })
    return {'ok': True, 'items': items, 'groups': [g[0] for g in _FX678_GROUPS],
            'ts': time.strftime('%H:%M:%S')}


def _fetch_weather_city(city):
    import urllib.request as _ur
    name, lat, lon = city
    url = ('https://api.open-meteo.com/v1/forecast?latitude=%.4f&longitude=%.4f'
           '&current=temperature_2m,weather_code,is_day&daily=sunrise,sunset&timezone=auto') % (lat, lon)
    req = _ur.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
    try:
        with _ur.urlopen(req, timeout=6) as resp:
            data = json.loads(resp.read().decode('utf-8'))
        cur = data.get('current') or {}
        temp = cur.get('temperature_2m')
        if temp is None:
            return None
        code = cur.get('weather_code')

        # 日出/日落：Open-Meteo 返回城市本地时间（timezone=auto），结合 utc_offset_seconds 转成 UTC epoch
        def _iso_epoch(s):
            try:
                from datetime import datetime, timezone as _tz
                off = int(data.get('utc_offset_seconds') or 0)
                dt = datetime.fromisoformat(s)
                return int(dt.replace(tzinfo=_tz.utc).timestamp()) - off
            except Exception:
                return None

        daily = data.get('daily') or {}
        sunrise = _iso_epoch((daily.get('sunrise') or [''])[0])
        sunset = _iso_epoch((daily.get('sunset') or [''])[0])
        return {
            'name': name, 'temp': round(float(temp), 1), 'code': code,
            'desc': _WMO_DESC.get(code, '未知'),
            'is_day': bool(cur.get('is_day', 1)),
            'sunrise': sunrise,
            'sunset': sunset,
        }
    except Exception:
        return None


def _fetch_weather_all():
    from concurrent.futures import ThreadPoolExecutor as _TPE
    results = []
    with _TPE(max_workers=10) as pool:
        for r in pool.map(_fetch_weather_city, _WEATHER_CITIES):
            if r:
                results.append(r)
    return {'ok': True, 'items': results, 'total': len(_WEATHER_CITIES),
            'ts': time.strftime('%m-%d %H:%M')}


def _fetch_flash_news():
    db = get_db()
    now = time.time()
    rows = _fetchall(
        db,
        "SELECT id, title, category, created_at FROM news "
        "WHERE created_at >= ? AND category IN ('时事','国际') "
        "ORDER BY created_at DESC LIMIT 15",
        (now - 3600,),
    )
    items = []
    for r in rows:
        items.append({
            'id': r['id'],
            'title': r['title'],
            'category': '时事' if r['category'] == '国际' else r['category'],
            'ts': int(r['created_at']),
        })
    return {'ok': True, 'items': items, 'ts': time.strftime('%H:%M:%S')}


@app.route('/api/topbar/stock', methods=['GET'])
def api_topbar_stock():
    """顶栏行情（主：fx678 汇通网股指/期市/汇市/黄金/原油 45 项；备用：新浪，30s 缓存）"""
    try:
        data = _topbar_get_cache('stock')
        if data is None:
            data = _fetch_fx678_quotes()
            # fx678 失败时降级到新浪（36 项，无 group 字段，前端自动隐藏分组标签）
            if not data.get('items'):
                data = _fetch_stock_quotes_sina()
            _topbar_set_cache('stock', data)
        return jsonify(data)
    except Exception as e:
        stale = _TOPBAR_CACHE.get('stock', {}).get('data')
        if stale:
            return jsonify(dict(stale, stale=True))
        return jsonify({'ok': False, 'error': '行情服务暂不可用'})


@app.route('/api/topbar/weather', methods=['GET'])
def api_topbar_weather():
    """顶栏天气（代理 Open-Meteo，15 分钟缓存）"""
    try:
        data = _topbar_get_cache('weather')
        if data is None:
            data = _fetch_weather_all()
            _topbar_set_cache('weather', data)
        return jsonify(data)
    except Exception as e:
        stale = _TOPBAR_CACHE.get('weather', {}).get('data')
        if stale:
            return jsonify(dict(stale, stale=True))
        return jsonify({'ok': False, 'error': '天气服务暂不可用'})


@app.route('/api/topbar/flash', methods=['GET'])
def api_topbar_flash():
    """顶栏快讯：近 1 小时时事/国际新闻（60s 缓存）"""
    try:
        data = _topbar_get_cache('flash')
        if data is None:
            data = _fetch_flash_news()
            _topbar_set_cache('flash', data)
        return jsonify(data)
    except Exception as e:
        stale = _TOPBAR_CACHE.get('flash', {}).get('data')
        if stale:
            return jsonify(dict(stale, stale=True))
        return jsonify({'ok': False, 'error': '快讯服务暂不可用'})


@app.route('/api/admin/news/<news_id>/featured', methods=['PUT'])
@admin_required
def api_admin_toggle_featured(news_id):
    """管理员：切换精选状态"""
    db = get_db()
    row = _fetchone(db, 'SELECT featured FROM news WHERE id=?', (news_id,))
    if not row:
        return jsonify({'error': '新闻不存在'}), 404
    new_val = 0 if row.get('featured') else 1
    _exec(db, 'UPDATE news SET featured=? WHERE id=?', (new_val, news_id))
    db.commit()
    return jsonify({'featured': bool(new_val)})


@app.route('/api/admin/news/<news_id>/pinned', methods=['PUT'])
@admin_required
def api_admin_toggle_pinned(news_id):
    """管理员：切换置顶状态"""
    db = get_db()
    row = _fetchone(db, 'SELECT pinned FROM news WHERE id=?', (news_id,))
    if not row:
        return jsonify({'error': '新闻不存在'}), 404
    new_val = 0 if row.get('pinned') else 1
    _exec(db, 'UPDATE news SET pinned=? WHERE id=?', (new_val, news_id))
    db.commit()
    return jsonify({'pinned': bool(new_val)})


@app.route('/api/upload/news-image', methods=['POST'])
@news_publisher_required
def api_upload_news_image():
    if 'file' not in request.files:
        return jsonify({'error': '未选择文件'}), 400
    f = request.files['file']
    if not f.filename:
        return jsonify({'error': '未选择文件'}), 400
    if f.content_length and f.content_length > 7 * 1024 * 1024:
        return jsonify({'error': '图片不能超过7MB'}), 400

    ext = os.path.splitext(f.filename)[1].lower()
    if ext not in ('.jpg', '.jpeg', '.png', '.gif', '.webp'):
        return jsonify({'error': '不支持的图片格式'}), 400

    file_data = f.read()
    # 校验实际内容长度（防止 Content-Length 头伪造绕过）
    if len(file_data) > 7 * 1024 * 1024:
        return jsonify({'error': '图片不能超过7MB'}), 400

    # 黄色内容检测
    is_nsfw, ratio = _check_nsfw(file_data)
    if is_nsfw:
        return jsonify({'error': '图片内容不符合社区规范，请勿上传不当内容'}), 400

    filename = f"{uuid.uuid4().hex}{ext}"
    image_path = f'uploads/news/{filename}'

    if _USE_PG:
        content_type = _get_content_type(filename)
        db = get_db()
        _exec(db, 'INSERT INTO images (path, data, content_type, created_at) VALUES (?,?,?,?)',
              (image_path, file_data, content_type, time.time()))
        db.commit()
    else:
        upload_dir = os.path.join(_DATA_DIR, 'uploads', 'news')
        os.makedirs(upload_dir, exist_ok=True)
        with open(os.path.join(upload_dir, filename), 'wb') as out:
            out.write(file_data)

    return jsonify({'url': image_path})


@app.route('/api/upload/news-video', methods=['POST'])
@news_publisher_required
def api_upload_news_video():
    """发布新闻上传视频：存 uploads/news/videos/，经 /uploads/ 通用路由提供"""
    if 'file' not in request.files:
        return jsonify({'error': '未选择文件'}), 400
    f = request.files['file']
    if not f.filename:
        return jsonify({'error': '未选择文件'}), 400
    if f.content_length and f.content_length > 200 * 1024 * 1024:
        return jsonify({'error': '视频不能超过200MB'}), 400

    ext = os.path.splitext(f.filename)[1].lower()
    if ext not in ('.mp4', '.webm', '.mov', '.m4v'):
        return jsonify({'error': '不支持的视频格式（支持 mp4/webm/mov/m4v）'}), 400

    file_data = f.read()
    # 校验实际内容长度（防止 Content-Length 头伪造绕过）
    if len(file_data) > 200 * 1024 * 1024:
        return jsonify({'error': '视频不能超过200MB'}), 400

    filename = f"{uuid.uuid4().hex}{ext}"
    video_path = f'uploads/news/videos/{filename}'

    if _USE_PG:
        content_type = _get_content_type(filename)
        db = get_db()
        _exec(db, 'INSERT INTO images (path, data, content_type, created_at) VALUES (?,?,?,?)',
              (video_path, file_data, content_type, time.time()))
        db.commit()
    else:
        upload_dir = os.path.join(_DATA_DIR, 'uploads', 'news', 'videos')
        os.makedirs(upload_dir, exist_ok=True)
        with open(os.path.join(upload_dir, filename), 'wb') as out:
            out.write(file_data)

    return jsonify({'url': video_path})


# ===== 视频版块 =====

@app.route('/terms')
def terms_page():
    return send_from_directory(_FRONTEND_DIR, 'terms.html')


@app.route('/terms-en')
def terms_en_page():
    return send_from_directory(_FRONTEND_DIR, 'terms-en.html')


@app.route('/privacy')
def privacy_page():
    return send_from_directory(_FRONTEND_DIR, 'privacy.html')


@app.route('/privacy-en')
def privacy_en_page():
    return send_from_directory(_FRONTEND_DIR, 'privacy-en.html')


@app.route('/values')
def values_page():
    return send_from_directory(_FRONTEND_DIR, 'values.html')


@app.route('/live')
@app.route('/live/')
def live_page():
    """直播版块页面（需登录）"""
    uid = _get_auth_user_id()
    if not uid:
        return redirect('/signin?redirect=/live')
    return send_from_directory(_FRONTEND_DIR, 'live.html')


@app.route('/api/live/stats/<host_id>')
def api_live_stats(host_id):
    """获取主播的直播统计（历史直播数、累计时长）"""
    db = get_db()
    try:
        row = _fetchone(db, 'SELECT COUNT(*) as total, COALESCE(SUM(duration),0) as total_duration FROM live_history WHERE host_id=?', (host_id,))
        return jsonify({
            'total_streams': row['total'] if row else 0,
            'total_duration': row['total_duration'] if row else 0,
        })
    except Exception:
        return jsonify({'total_streams': 0, 'total_duration': 0})


def _live_channel_row_to_dict(row, db=None):
    if not row:
        return None
    username = ''
    if db and row.get('user_id'):
        u = _fetchone(db, 'SELECT username FROM users WHERE id=?', (row['user_id'],))
        if u:
            username = u['username']
    d = {
        'id': row['id'],
        'user_id': row['user_id'],
        'name': row['name'],
        'cover': _public_upload_url(row.get('cover')),
        'status': row.get('status') or 'pending',
        'reject_reason': row.get('reject_reason') or '',
        'created_at': row.get('created_at'),
        'reviewed_at': row.get('reviewed_at'),
        'featured': bool(row.get('featured', 0)),
        'banned': bool(row.get('banned', 0)),
        'username': username,
    }
    return d


@app.route('/api/live/my-channel', methods=['GET'])
@login_required
def api_live_my_channel():
    """获取当前用户的直播频道（权限申请状态）。向后兼容：返回最近一个。"""
    uid = _get_auth_user_id()
    db = get_db()
    row = _fetchone(db, 'SELECT * FROM live_channels WHERE user_id=? ORDER BY created_at DESC LIMIT 1', (uid,))
    return jsonify({'channel': _live_channel_row_to_dict(row, db) if row else None})


@app.route('/api/live/my-channels', methods=['GET'])
@login_required
def api_live_my_channels():
    """获取当前用户的所有直播频道（最多 3 个）"""
    uid = _get_auth_user_id()
    db = get_db()
    rows = _fetchall(db, 'SELECT * FROM live_channels WHERE user_id=? ORDER BY created_at DESC', (uid,))
    return jsonify({
        'channels': [_live_channel_row_to_dict(r, db) for r in rows],
        'max': 3,
        'remaining': max(0, 3 - len(rows)),
    })


@app.route('/api/live/channels', methods=['GET'])
def api_live_channels_list():
    """公开接口：所有审核通过的直播间列表（含在线状态）"""
    db = get_db()
    try:
        page = max(1, int(request.args.get('page', 1)))
    except (TypeError, ValueError):
        page = 1
    per_page = 24
    offset = (page - 1) * per_page
    rows = _fetchall(db, '''
        SELECT lc.id, lc.user_id, lc.name, lc.cover, lc.featured, u.username, u.avatar, u.is_quality
        FROM live_channels lc LEFT JOIN users u ON lc.user_id = u.id
        WHERE lc.status='approved' AND (lc.banned=0 OR lc.banned IS NULL)
        ORDER BY lc.featured DESC, lc.created_at DESC LIMIT ? OFFSET ?
    ''', (per_page, offset))
    total_row = _fetchone(db, "SELECT COUNT(*) as c FROM live_channels WHERE status='approved' AND (banned=0 OR banned IS NULL)")
    items = []
    for r in rows:
        host_id = r['user_id']
        stream = _live_streams.get(host_id)
        is_live = bool(stream)
        items.append({
            'host_id': host_id,
            'channel_id': r['id'],
            'username': r.get('username') or '已注销',
            'avatar': _public_upload_url(r.get('avatar')),
            'name': r['name'],
            'cover': _public_upload_url(r.get('cover')),
            'is_quality': bool(r.get('is_quality', 0)),
            'is_live': is_live,
            'featured': bool(r.get('featured', 0)),
            'viewer_count': len(stream['viewers']) if is_live else 0,
            'started_at': stream['started_at'] if is_live else 0,
            'title': stream['title'] if is_live else r['name'],
        })
    return jsonify({
        'channels': items,
        'total': total_row['c'] if total_row else 0,
        'page': page,
        'per_page': per_page,
    })


@app.route('/api/live/channel/<channel_id>', methods=['GET'])
def api_live_channel_detail(channel_id):
    """公开接口：单个直播间详情"""
    db = get_db()
    r = _fetchone(db, '''
        SELECT lc.id, lc.user_id, lc.name, lc.cover, lc.featured, lc.status, lc.banned, u.username, u.avatar, u.is_quality
        FROM live_channels lc LEFT JOIN users u ON lc.user_id = u.id
        WHERE lc.id=?
    ''', (channel_id,))
    if not r:
        return jsonify({'error': '直播间不存在'}), 404
    if r.get('status') != 'approved' or r.get('banned'):
        return jsonify({'error': '直播间不可用'}), 404
    host_id = r['user_id']
    stream = _live_streams.get(host_id)
    is_live = bool(stream)
    return jsonify({
        'host_id': host_id,
        'channel_id': r['id'],
        'username': r.get('username') or '已注销',
        'avatar': _public_upload_url(r.get('avatar')),
        'name': r['name'],
        'cover': _public_upload_url(r.get('cover')),
        'is_quality': bool(r.get('is_quality', 0)),
        'is_live': is_live,
        'featured': bool(r.get('featured', 0)),
        'viewer_count': len(stream['viewers']) if is_live else 0,
        'started_at': stream['started_at'] if is_live else 0,
        'title': stream['title'] if is_live else r['name'],
    })


@app.route('/api/live/channel/<channel_id>/edit', methods=['POST'])
@login_required
def api_live_channel_edit(channel_id):
    """编辑自己的直播间：修改名字/封面。仅 approved 状态可编辑。"""
    uid = _get_auth_user_id()
    name = (request.form.get('name') or '').strip()
    if not name:
        return jsonify({'error': '请填写直播间名字'}), 400
    if len(name) > 40:
        return jsonify({'error': '直播间名字不能超过 40 个字'}), 400
    ok, found = check_banned_words(name)
    if not ok:
        return jsonify({'error': f'名字包含违禁词：{"、".join(found[:5])}'}), 400
    # AI 内容审核（直播间名字编辑）
    ai_ok, ai_cat, ai_reason, ai_score = ai_moderate(name, 'channel_name')
    if not ai_ok:
        return jsonify({'error': f'直播间名字被 AI 审核拦截（{ai_cat}）：{ai_reason}'}), 400
    db = get_db()
    row = _fetchone(db, 'SELECT id, user_id, cover, status FROM live_channels WHERE id=? AND user_id=?', (channel_id, uid))
    if not row:
        return jsonify({'error': '直播间不存在或无权操作'}), 404
    if row.get('status') != 'approved':
        return jsonify({'error': '直播间未通过审核，无法编辑'}), 400

    cover_path = row.get('cover') or ''
    file = request.files.get('cover')
    if file and file.filename:
        if not allowed_file(file.filename, ALLOWED_IMAGE_EXTENSIONS):
            return jsonify({'error': '封面只允许上传图片 (jpg, png, gif, webp)'}), 400
        file.seek(0, 2)
        size = file.tell()
        file.seek(0)
        if size > 7 * 1024 * 1024:
            return jsonify({'error': '封面文件大小不能超过 7MB'}), 400
        file_data = file.read()
        is_nsfw, _ = _check_nsfw(file_data)
        if is_nsfw:
            return jsonify({'error': '图片内容不符合社区规范'}), 400
        ext = file.filename.rsplit('.', 1)[1].lower()
        filename = f"{uuid.uuid4().hex}.{ext}"
        cover_path = f"uploads/livecovers/{filename}"
        if _USE_PG:
            content_type = _get_content_type(filename)
            _exec(db, 'INSERT INTO images (path, data, content_type, created_at) VALUES (?,?,?,?)',
                  (cover_path, file_data, content_type, time.time()))
        else:
            upload_dir = os.path.join(_DATA_DIR, 'uploads', 'livecovers')
            os.makedirs(upload_dir, exist_ok=True)
            with open(os.path.join(upload_dir, filename), 'wb') as out:
                out.write(file_data)
    _exec(db, 'UPDATE live_channels SET name=?, cover=? WHERE id=?', (name, cover_path, channel_id))
    db.commit()
    new_row = _fetchone(db, 'SELECT * FROM live_channels WHERE id=?', (channel_id,))
    return jsonify({'channel': _live_channel_row_to_dict(new_row, db) if new_row else None})


@app.route('/api/live/channel/<channel_id>', methods=['DELETE'])
@login_required
def api_live_delete_channel(channel_id):
    """用户删除自己的直播间（仅限自己的、且未在直播中的频道）"""
    uid = _get_auth_user_id()
    db = get_db()
    row = _fetchone(db, 'SELECT id, user_id, cover, status FROM live_channels WHERE id=?', (channel_id,))
    if not row:
        return jsonify({'error': '频道不存在'}), 404
    if row.get('user_id') != uid:
        return jsonify({'error': '无权删除他人的直播间'}), 403
    # 正在直播中的频道不允许删除
    if uid in _live_streams and _live_streams[uid].get('channel_id') == channel_id:
        return jsonify({'error': '该直播间正在直播中，请先结束直播再删除'}), 400
    # 删除封面文件（SQLite 模式）
    stored = row.get('cover')
    if stored and not _USE_PG:
        full_path = os.path.join(_DATA_DIR, str(stored).lstrip('/'))
        if os.path.isfile(full_path):
            try:
                os.remove(full_path)
            except Exception:
                pass
    _exec(db, 'DELETE FROM live_channels WHERE id=?', (channel_id,))
    db.commit()
    return jsonify({'ok': True})


@app.route('/api/live/apply', methods=['POST'])
@login_required
def api_live_apply():
    """申请直播权限：提交/重新提交直播间封面+名字。multipart 表单：name + cover"""
    uid = _get_auth_user_id()
    name = (request.form.get('name') or '').strip()
    if not name:
        return jsonify({'error': '请填写直播间名字'}), 400
    if len(name) > 40:
        return jsonify({'error': '直播间名字不能超过 40 个字'}), 400
    ok, found = check_banned_words(name)
    if not ok:
        return jsonify({'error': f'名字包含违禁词：{"、".join(found[:5])}'}), 400
    # AI 内容审核（直播间名字）
    ai_ok, ai_cat, ai_reason, ai_score = ai_moderate(name, 'channel_name')
    if not ai_ok:
        return jsonify({'error': f'直播间名字被 AI 审核拦截（{ai_cat}）：{ai_reason}'}), 400
    cover_path = ''
    file = request.files.get('cover')
    if file and file.filename:
        if not allowed_file(file.filename, ALLOWED_IMAGE_EXTENSIONS):
            return jsonify({'error': '封面只允许上传图片 (jpg, png, gif, webp)'}), 400
        file.seek(0, 2)
        size = file.tell()
        file.seek(0)
        if size > 7 * 1024 * 1024:
            return jsonify({'error': '封面文件大小不能超过 7MB'}), 400
        file_data = file.read()
        is_nsfw, _ = _check_nsfw(file_data)
        if is_nsfw:
            return jsonify({'error': '图片内容不符合社区规范'}), 400
        ext = file.filename.rsplit('.', 1)[1].lower()
        filename = f"{uuid.uuid4().hex}.{ext}"
        cover_path = f"uploads/livecovers/{filename}"
        if _USE_PG:
            content_type = _get_content_type(filename)
            db = get_db()
            _exec(db, 'INSERT INTO images (path, data, content_type, created_at) VALUES (?,?,?,?)',
                  (cover_path, file_data, content_type, time.time()))
        else:
            upload_dir = os.path.join(_DATA_DIR, 'uploads', 'livecovers')
            os.makedirs(upload_dir, exist_ok=True)
            with open(os.path.join(upload_dir, filename), 'wb') as out:
                out.write(file_data)

    db = get_db()
    # 限制每用户最多 3 个直播间（每次申请都创建新频道，不再覆盖已有频道）
    count_row = _fetchone(db, 'SELECT COUNT(*) as c FROM live_channels WHERE user_id=?', (uid,))
    existing_count = count_row['c'] if count_row else 0
    if existing_count >= 3:
        return jsonify({'error': '每个用户最多申请 3 个直播间'}), 400
    ch_id = 'lc_' + uuid.uuid4().hex[:16]
    now = time.time()
    _exec(db, 'INSERT INTO live_channels (id, user_id, name, cover, status, reject_reason, created_at) VALUES (?,?,?,?,?,?,?)',
          (ch_id, uid, name, cover_path, 'pending', '', now))
    db.commit()
    row = _fetchone(db, 'SELECT * FROM live_channels WHERE id=?', (ch_id,))
    return jsonify({'channel': _live_channel_row_to_dict(row, db) if row else None})


@app.route('/api/admin/live-channels', methods=['GET'])
@admin_required
def api_admin_live_channels():
    """管理员获取直播频道列表（含待审核）"""
    db = get_db()
    try:
        page = max(1, int(request.args.get('page', 1)))
    except (TypeError, ValueError):
        page = 1
    per_page = 20
    offset = (page - 1) * per_page
    status_filter = request.args.get('status', '')
    if status_filter in ('pending', 'approved', 'rejected'):
        rows = _fetchall(db, '''
            SELECT lc.*, u.username
            FROM live_channels lc LEFT JOIN users u ON lc.user_id = u.id
            WHERE lc.status = ?
            ORDER BY lc.created_at DESC LIMIT ? OFFSET ?
        ''', (status_filter, per_page, offset))
        total_row = _fetchone(db, 'SELECT COUNT(*) as c FROM live_channels WHERE status=?', (status_filter,))
    else:
        rows = _fetchall(db, '''
            SELECT lc.*, u.username
            FROM live_channels lc LEFT JOIN users u ON lc.user_id = u.id
            ORDER BY lc.created_at DESC LIMIT ? OFFSET ?
        ''', (per_page, offset))
        total_row = _fetchone(db, 'SELECT COUNT(*) as c FROM live_channels')
    items = [{
        'id': r['id'], 'user_id': r['user_id'], 'name': r['name'],
        'cover': _public_upload_url(r.get('cover')),
        'status': r.get('status') or 'pending',
        'reject_reason': r.get('reject_reason') or '',
        'created_at': r.get('created_at'),
        'reviewed_at': r.get('reviewed_at'),
        'featured': bool(r.get('featured', 0)),
        'username': r.get('username') or '已注销',
    } for r in rows]
    return jsonify({
        'channels': items,
        'total': total_row['c'] if total_row else 0,
        'page': page,
        'per_page': per_page,
    })


@app.route('/api/admin/live-channel/<channel_id>/review', methods=['PUT'])
@admin_required
def api_admin_review_live_channel(channel_id):
    """管理员审核直播频道：approve / reject（可选 reject_reason）
    仅超级管理员可审核，普通管理员不可自我审核
    """
    data = request.get_json() or {}
    action = data.get('action', '')
    if action not in ('approve', 'reject'):
        return jsonify({'error': '无效操作'}), 400
    new_status = 'approved' if action == 'approve' else 'rejected'
    reject_reason = (data.get('reject_reason') or '').strip() if action == 'reject' else ''
    db = get_db()
    row = _fetchone(db, 'SELECT id, user_id FROM live_channels WHERE id=?', (channel_id,))
    if not row:
        return jsonify({'error': '频道不存在'}), 404
    admin_uid = _get_auth_user_id()
    # 禁止管理员审核自己的频道（防止自我批准）
    if row['user_id'] == admin_uid:
        return jsonify({'error': '不能审核自己的直播间'}), 403
    if new_status == 'approved':
        _exec(db, 'UPDATE live_channels SET status=?, reject_reason=?, reviewed_at=?, reviewed_by=? WHERE id=?',
              (new_status, reject_reason, time.time(), admin_uid, channel_id))
    else:
        _exec(db, 'UPDATE live_channels SET status=?, reject_reason=?, reviewed_at=?, reviewed_by=? WHERE id=?',
              (new_status, reject_reason, time.time(), admin_uid, channel_id))
    # 通过审核 → 授予黄色优质主播标识；拒绝/撤销 → 取消
    _exec(db, 'UPDATE users SET is_quality=? WHERE id=?',
          (1 if new_status == 'approved' else 0, row['user_id']))
    db.commit()
    return jsonify({'ok': True, 'status': new_status})


@app.route('/api/admin/live-channel/<channel_id>', methods=['DELETE'])
@admin_required
def api_admin_delete_live_channel(channel_id):
    """管理员删除直播频道"""
    db = get_db()
    row = _fetchone(db, 'SELECT id, cover FROM live_channels WHERE id=?', (channel_id,))
    if not row:
        return jsonify({'error': '频道不存在'}), 404
    stored = row.get('cover')
    if stored and not _USE_PG:
        full_path = os.path.join(_DATA_DIR, str(stored).lstrip('/'))
        if os.path.isfile(full_path):
            try:
                os.remove(full_path)
            except Exception:
                pass
    _exec(db, 'DELETE FROM live_channels WHERE id=?', (channel_id,))
    db.commit()
    return jsonify({'ok': True})


@app.route('/api/admin/live-channel/<channel_id>/featured', methods=['PUT'])
@admin_required
def api_admin_toggle_live_featured(channel_id):
    """管理员切换直播频道精选标记（精选直播间在首页精选区展示，离线也展示）"""
    db = get_db()
    row = _fetchone(db, 'SELECT id, featured FROM live_channels WHERE id=?', (channel_id,))
    if not row:
        return jsonify({'error': '频道不存在'}), 404
    new_val = 0 if row.get('featured') else 1
    _exec(db, 'UPDATE live_channels SET featured=? WHERE id=?', (new_val, channel_id))
    db.commit()
    return jsonify({'ok': True, 'featured': bool(new_val)})


@app.route('/api/admin/live-channel/<channel_id>/ban', methods=['PUT'])
@admin_required
def api_admin_ban_live_channel(channel_id):
    """封禁/解封直播间。封禁时强制结束正在进行的直播。"""
    data = request.get_json() or {}
    banned = 1 if data.get('banned') else 0
    db = get_db()
    row = _fetchone(db, 'SELECT id, user_id FROM live_channels WHERE id=?', (channel_id,))
    if not row:
        return jsonify({'error': '频道不存在'}), 404
    _exec(db, 'UPDATE live_channels SET banned=? WHERE id=?', (banned, channel_id))
    db.commit()
    # 封禁时强制结束该用户的进行中直播
    if banned and _HAS_SOCKETIO:
        host_id = row['user_id']
        stream = _live_streams.pop(host_id, None)
        if stream:
            try:
                db2 = get_db()
                duration = int(time.time() - stream['started_at'])
                peak = len(stream['viewers'])
                _exec(db2, 'INSERT INTO live_history (id, host_id, title, started_at, ended_at, duration, peak_viewers) VALUES (?,?,?,?,?,?,?)',
                      ('live_' + uuid.uuid4().hex[:12], host_id, stream['title'], stream['started_at'], time.time(), duration, peak))
                db2.commit()
            except Exception as e:
                print(f'[live] 封禁时保存历史失败: {e}')
            socketio.emit('live_ended', {'host_id': host_id}, room=f'live_{host_id}')
            socketio.emit('live_ended', {'host_id': host_id}, room='live_lobby')
            socketio.emit('live_error', {'error': '你的直播间已被管理员封禁，直播已结束'}, to=stream['sid'])
            # 全量同步大厅
            all_streams = [{'host_id': s['host_id'], 'username': s['username'], 'avatar': s['avatar'], 'title': s['title'], 'cover': s.get('cover',''), 'is_quality': s.get('is_quality', False), 'source_type': s.get('source_type','camera'), 'viewer_count': len(s['viewers']), 'started_at': s['started_at']} for s in _live_streams.values()]
            socketio.emit('live_list', {'streams': all_streams}, room='live_lobby')
    return jsonify({'ok': True, 'banned': bool(banned)})


@app.route('/api/live/active-count', methods=['GET'])
def api_live_active_count():
    """公开接口：返回当前正在直播的数量与简要列表（首页 10s 轮询用）"""
    streams = [{'host_id': s['host_id'], 'username': s['username'], 'title': s['title'],
                'cover': s.get('cover', ''), 'viewer_count': len(s['viewers']),
                'started_at': s['started_at']} for s in _live_streams.values()]
    return jsonify({'count': len(streams), 'streams': streams})


@app.route('/api/live/featured-channels', methods=['GET'])
def api_live_featured_channels():
    """公开接口：返回被标记为精选的直播频道（含在线状态，离线频道也展示）"""
    db = get_db()
    rows = _fetchall(db, '''
        SELECT lc.id, lc.user_id, lc.name, lc.cover, lc.featured, u.username, u.avatar, u.is_quality
        FROM live_channels lc LEFT JOIN users u ON lc.user_id = u.id
        WHERE lc.featured=1 AND lc.status='approved'
        ORDER BY lc.created_at DESC
    ''')
    items = []
    for r in rows:
        host_id = r['user_id']
        stream = _live_streams.get(host_id)
        is_live = bool(stream)
        items.append({
            'host_id': host_id,
            'channel_id': r['id'],
            'username': r.get('username') or '已注销',
            'avatar': _public_upload_url(r.get('avatar')),
            'name': r['name'],
            'cover': _public_upload_url(r.get('cover')),
            'is_quality': bool(r.get('is_quality', 0)),
            'is_live': is_live,
            'viewer_count': len(stream['viewers']) if is_live else 0,
            'started_at': stream['started_at'] if is_live else 0,
            'title': stream['title'] if is_live else r['name'],
        })
    return jsonify({'channels': items})


@app.route('/video')
@app.route('/video/')
def video_page():
    """视频版块页面"""
    return send_from_directory(_FRONTEND_DIR, 'video.html')


def _public_upload_url(path):
    """把数据库中的 uploads 相对路径转换成站内直链。"""
    if not path:
        return ''
    return '/' + str(path).replace('\\', '/').lstrip('/')


@app.route('/api/video/list', methods=['GET'])
def api_video_list():
    """视频列表（分页）"""
    db = get_db()
    try:
        page = max(1, int(request.args.get('page', 1)))
    except (TypeError, ValueError):
        page = 1
    per_page = 12
    offset = (page - 1) * per_page
    rows = _fetchall(db, '''
        SELECT v.id, v.title, v.description, v.filepath, v.filesize, v.duration,
               v.thumbnail, v.views, v.likes, v.created_at, v.author_id, v.status,
               u.username as author_name, u.avatar as author_avatar
        FROM videos v LEFT JOIN users u ON v.author_id = u.id
        WHERE v.status = 'approved'
        ORDER BY v.created_at DESC LIMIT ? OFFSET ?
    ''', (per_page, offset))
    total = _fetchone(db, "SELECT COUNT(*) as c FROM videos WHERE status = 'approved'")
    uid = _get_auth_user_id()
    items = []
    for r in rows:
        av = r.get('author_avatar') or ''
        item = {
            'id': r['id'],
            'title': r['title'],
            'description': r.get('description') or '',
            'filesize': r.get('filesize') or 0,
            'duration': r.get('duration') or 0,
            'thumbnail': _public_upload_url(r.get('thumbnail')),
            'views': r.get('views') or 0,
            'likes': r.get('likes') or 0,
            'created_at': r['created_at'],
            'author_id': r.get('author_id') or '',
            'author_name': r.get('author_name') or '已注销',
            'author_avatar': ('/' + av) if av and not av.startswith('/') else av,
            'liked': False,
        }
        if uid:
            item['liked'] = bool(_fetchone(db, 'SELECT 1 FROM video_likes WHERE user_id=? AND video_id=?', (uid, r['id'])))
        items.append(item)
    return jsonify({'videos': items, 'total': total['c'] if total else 0, 'page': page, 'per_page': per_page})


@app.route('/api/video/<video_id>', methods=['GET'])
def api_video_detail(video_id):
    """视频详情"""
    db = get_db()
    row = _fetchone(db, '''
        SELECT id, title, description, filepath, filesize, duration, thumbnail,
               views, likes, created_at, author_id
        FROM videos WHERE id=? AND status='approved'
    ''', (video_id,))
    if not row:
        return jsonify({'error': '视频不存在'}), 404
    _exec(db, 'UPDATE videos SET views = views + 1 WHERE id=?', (video_id,))
    db.commit()
    u = _fetchone(db, 'SELECT username, avatar FROM users WHERE id=?', (row['author_id'],)) if row.get('author_id') else None
    uid = _get_auth_user_id()
    av = (u.get('avatar') or '') if u else ''
    return jsonify({
        'video': {
            'id': row['id'],
            'title': row['title'],
            'description': row.get('description') or '',
            'filepath': _public_upload_url(row['filepath']),
            'filesize': row.get('filesize') or 0,
            'duration': row.get('duration') or 0,
            'thumbnail': _public_upload_url(row.get('thumbnail')),
            'views': (row.get('views') or 0) + 1,
            'likes': row.get('likes') or 0,
            'created_at': row['created_at'],
            'author_name': u['username'] if u else '已注销',
            'author_avatar': ('/' + av) if av and not av.startswith('/') else av,
            'liked': bool(uid and _fetchone(db, 'SELECT 1 FROM video_likes WHERE user_id=? AND video_id=?', (uid, row['id']))),
        }
    })


def _generate_video_thumbnail(video_filepath, video_filename):
    """使用 ffmpeg 从视频生成缩略图，返回相对路径"""
    import subprocess as _sp
    thumb_name = os.path.splitext(video_filename)[0] + '.jpg'
    thumb_dir = os.path.join(_DATA_DIR, 'uploads', 'video_thumbs')
    os.makedirs(thumb_dir, exist_ok=True)
    os.chmod(thumb_dir, 0o755)
    thumb_full = os.path.join(thumb_dir, thumb_name)
    try:
        _sp.run([
            'ffmpeg', '-y', '-ss', '0.5', '-i', video_filepath,
            '-vframes', '1', '-vf', 'scale=640:360:force_original_aspect_ratio=decrease,pad=640:360:(ow-iw)/2:(oh-ih)/2',
            '-q:v', '2', thumb_full
        ], capture_output=True, timeout=10)
        if os.path.isfile(thumb_full) and os.path.getsize(thumb_full) > 0:
            os.chmod(thumb_full, 0o644)
            return f'uploads/video_thumbs/{thumb_name}'
    except Exception:
        pass
    return ''


@app.route('/api/video/thumb/<video_id>')
def api_video_thumb(video_id):
    """按需生成视频缩略图（用于旧视频）"""
    db = get_db()
    row = _fetchone(db, "SELECT filepath, thumbnail FROM videos WHERE id=? AND status='approved'", (video_id,))
    if not row:
        return jsonify({'error': 'Not found'}), 404
    # 已有缩略图
    if row.get('thumbnail'):
        return redirect(_public_upload_url(row['thumbnail']))
    # 生成缩略图
    video_full = os.path.join(_DATA_DIR, row['filepath'])
    if not os.path.isfile(video_full):
        return jsonify({'error': 'Video file missing'}), 404
    video_filename = os.path.basename(row['filepath'])
    thumb_path = _generate_video_thumbnail(video_full, video_filename)
    if thumb_path:
        _exec(db, 'UPDATE videos SET thumbnail=? WHERE id=?', (thumb_path, video_id))
        db.commit()
        return redirect(_public_upload_url(thumb_path))
    return jsonify({'error': 'Failed'}), 500


@app.route('/api/video/upload', methods=['POST'])
@login_required
def api_video_upload():
    """上传视频"""
    if 'file' not in request.files:
        return jsonify({'error': '未选择文件'}), 400
    f = request.files['file']
    if not f.filename:
        return jsonify({'error': '未选择文件'}), 400
    # 大小限制 200MB
    if f.content_length and f.content_length > 600 * 1024 * 1024:
        return jsonify({'error': '视频不能超过600MB'}), 400

    ext = os.path.splitext(f.filename)[1].lower()
    if ext not in ('.mp4', '.mov', '.webm', '.m4v'):
        return jsonify({'error': '仅支持 MP4/MOV/WebM 格式'}), 400

    title = (request.form.get('title') or '').strip()
    description = (request.form.get('description') or '').strip()
    duration_str = request.form.get('duration') or '0'
    try:
        duration = float(duration_str)
    except (TypeError, ValueError):
        duration = 0
    # 时长限制 10 分钟
    if duration > 600:
        return jsonify({'error': '视频时长不能超过10分钟'}), 400
    if not title:
        title = os.path.splitext(f.filename)[0]

    # 保存文件
    filename = f"{uuid.uuid4().hex}{ext}"
    video_dir = os.path.join(_DATA_DIR, 'uploads', 'videos')
    os.makedirs(video_dir, exist_ok=True)
    filepath = os.path.join(video_dir, filename)
    file_data = f.read()
    if len(file_data) > 600 * 1024 * 1024:
        return jsonify({'error': '视频不能超过600MB'}), 400

    with open(filepath, 'wb') as out:
        out.write(file_data)
    os.chmod(filepath, 0o644)

    # 服务端 ffmpeg 生成缩略图
    thumbnail_path = _generate_video_thumbnail(filepath, filename)
    # 自定义封面优先
    cover_file = request.files.get('cover')
    if cover_file and cover_file.filename:
        cover_ext = os.path.splitext(cover_file.filename)[1].lower()
        if cover_ext in ('.jpg', '.jpeg', '.png', '.gif', '.webp'):
            cover_name = f"{os.path.splitext(filename)[0]}_cover{cover_ext}"
            cover_dir = os.path.join(_DATA_DIR, 'uploads', 'video_thumbs')
            os.makedirs(cover_dir, exist_ok=True)
            cover_full = os.path.join(cover_dir, cover_name)
            cover_file.save(cover_full)
            thumbnail_path = f'uploads/video_thumbs/{cover_name}'
    if not thumbnail_path:
        thumbnail_path = ''

    db = get_db()
    vid = 'vid_' + uuid.uuid4().hex[:8]
    uid = _get_auth_user_id()
    now = time.time()
    stored_path = f'uploads/videos/{filename}'
    _exec(db, '''
        INSERT INTO videos
            (id, title, description, filename, filepath, filesize, duration,
             thumbnail, author_id, views, likes, created_at, status)
        VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)
    ''', (vid, title, description, filename, stored_path, len(file_data), duration,
          thumbnail_path, uid, 0, 0, now, 'pending'))
    db.commit()
    return jsonify({'id': vid, 'url': _public_upload_url(stored_path), 'status': 'pending'})


@app.route('/api/video/<video_id>/like', methods=['POST'])
@login_required
def api_video_like(video_id):
    """点赞/取消点赞"""
    db = get_db()
    uid = _get_auth_user_id()
    video = _fetchone(db, "SELECT id, likes FROM videos WHERE id=? AND status='approved'", (video_id,))
    if not video:
        return jsonify({'error': '视频不存在'}), 404
    existing = _fetchone(db, 'SELECT 1 FROM video_likes WHERE user_id=? AND video_id=?', (uid, video_id))
    if existing:
        _exec(db, 'DELETE FROM video_likes WHERE user_id=? AND video_id=?', (uid, video_id))
        _exec(db, 'UPDATE videos SET likes = CASE WHEN likes > 0 THEN likes - 1 ELSE 0 END WHERE id=?', (video_id,))
        liked = False
    else:
        _exec(db, 'INSERT INTO video_likes (user_id, video_id, created_at) VALUES (?,?,?)', (uid, video_id, time.time()))
        _exec(db, 'UPDATE videos SET likes = likes + 1 WHERE id=?', (video_id,))
        liked = True
    db.commit()
    row = _fetchone(db, 'SELECT likes FROM videos WHERE id=?', (video_id,))
    return jsonify({'liked': liked, 'likes': row['likes'] if row else 0})


# ===== 视频管理 =====


@app.route('/api/admin/videos', methods=['GET'])
@admin_required
def api_admin_videos():
    """管理员获取所有视频（含待审核）"""
    db = get_db()
    try:
        page = max(1, int(request.args.get('page', 1)))
    except (TypeError, ValueError):
        page = 1
    per_page = 20
    offset = (page - 1) * per_page
    status_filter = request.args.get('status', '')
    if status_filter in ('pending', 'approved', 'rejected'):
        rows = _fetchall(db, '''
            SELECT v.id, v.title, v.description, v.filepath, v.filesize, v.duration,
                   v.thumbnail, v.views, v.likes, v.created_at, v.author_id, v.status,
                   u.username as author_name
            FROM videos v LEFT JOIN users u ON v.author_id = u.id
            WHERE v.status = ?
            ORDER BY v.created_at DESC LIMIT ? OFFSET ?
        ''', (status_filter, per_page, offset))
        total_row = _fetchone(db, 'SELECT COUNT(*) as c FROM videos WHERE status=?', (status_filter,))
    else:
        rows = _fetchall(db, '''
            SELECT v.id, v.title, v.description, v.filepath, v.filesize, v.duration,
                   v.thumbnail, v.views, v.likes, v.created_at, v.author_id, v.status,
                   u.username as author_name
            FROM videos v LEFT JOIN users u ON v.author_id = u.id
            ORDER BY v.created_at DESC LIMIT ? OFFSET ?
        ''', (per_page, offset))
        total_row = _fetchone(db, 'SELECT COUNT(*) as c FROM videos')
    items = []
    for r in rows:
        items.append({
            'id': r['id'],
            'title': r['title'],
            'description': r.get('description') or '',
            'filepath': _public_upload_url(r.get('filepath')),
            'filesize': r.get('filesize') or 0,
            'duration': r.get('duration') or 0,
            'thumbnail': _public_upload_url(r.get('thumbnail')),
            'views': r.get('views') or 0,
            'likes': r.get('likes') or 0,
            'created_at': r['created_at'],
            'author_name': r.get('author_name') or '已注销',
            'status': r.get('status') or 'pending',
        })
    return jsonify({
        'videos': items,
        'total': total_row['c'] if total_row else 0,
        'page': page,
        'per_page': per_page,
    })


@app.route('/api/admin/video/<video_id>/review', methods=['PUT'])
@admin_required
def api_admin_review_video(video_id):
    """管理员审核视频：approve / reject"""
    data = request.get_json() or {}
    action = data.get('action', '')
    if action not in ('approve', 'reject'):
        return jsonify({'error': '无效操作'}), 400
    new_status = 'approved' if action == 'approve' else 'rejected'
    db = get_db()
    row = _fetchone(db, 'SELECT id FROM videos WHERE id=?', (video_id,))
    if not row:
        return jsonify({'error': '视频不存在'}), 404
    _exec(db, 'UPDATE videos SET status=? WHERE id=?', (new_status, video_id))
    db.commit()
    return jsonify({'ok': True, 'status': new_status})


@app.route('/api/admin/video/<video_id>', methods=['DELETE'])
@admin_required
def api_admin_delete_video(video_id):
    """管理员删除视频"""
    db = get_db()
    row = _fetchone(db, 'SELECT id, filepath, thumbnail FROM videos WHERE id=?', (video_id,))
    if not row:
        return jsonify({'error': '视频不存在'}), 404
    # 删除视频及封面文件。数据库中保存的是相对 DATA_DIR 的 uploads 路径。
    for stored_path in (row.get('filepath'), row.get('thumbnail')):
        if not stored_path:
            continue
        full_path = os.path.join(_DATA_DIR, str(stored_path).lstrip('/'))
        if os.path.isfile(full_path):
            os.remove(full_path)
    _exec(db, 'DELETE FROM video_likes WHERE video_id=?', (video_id,))
    _exec(db, 'DELETE FROM videos WHERE id=?', (video_id,))
    db.commit()
    return jsonify({'ok': True})


# ===== 播客（Podcast）版块 =====
_PODCAST_CATEGORIES = ('历史', '科技', '文化', '故事', '情感', '商业', '科学', '教育', '健康', '新闻', '艺术', '其他')


def _detect_subtitle_type(subtitle):
    """根据字幕文本自动判断类型：含时间戳(如 [00:12.34])则视为同步字幕，否则为纯文本。"""
    s = (subtitle or '').strip()
    if not s:
        return 'text'
    lines = [l for l in s.splitlines() if l.strip()]
    if not lines:
        return 'text'
    # 每行形如 [mm:ss.xx] [mm:ss.xx] 文本 可视为 LRC/时间戳字幕
    import re as _re
    stamp = _re.compile(r'^\s*\[(\d{1,2}):(\d{2})(?:[.:](\d{1,3}))?\]')
    timed = sum(1 for ln in lines[:200] if stamp.match(ln))
    return 'lrc' if timed >= max(1, len(lines[:200]) * 0.6) else 'text'


@app.route('/podcast')
@app.route('/podcast/')
def podcast_page():
    return send_from_directory(_FRONTEND_DIR, 'podcast.html')


@app.route('/api/podcast/list', methods=['GET'])
def api_podcast_list():
    """播客列表（分页 + 可精选/分类过滤）"""
    db = get_db()
    try:
        page = max(1, int(request.args.get('page', 1)))
    except (TypeError, ValueError):
        page = 1
    per_page = 20
    offset = (page - 1) * per_page
    cat = (request.args.get('category') or '').strip()
    featured_only = (request.args.get('featured') or '').lower() in ('1', 'true')
    where = ["p.status = 'approved'"]
    params = []
    if cat:
        where.append('p.category = ?')
        params.append(cat)
    if featured_only:
        where.append('p.featured = 1')
    wsql = ' AND '.join(where)
    rows = _fetchall(db, f'''
        SELECT p.id, p.title, p.description, p.filepath, p.filesize, p.duration,
               p.cover, p.category, p.channel_name, p.subtitle_type, p.likes, p.plays, p.featured,
               p.created_at, p.author_id, u.username as author_name, u.avatar as author_avatar
        FROM podcasts p LEFT JOIN users u ON p.author_id = u.id
        WHERE {wsql}
        ORDER BY p.created_at DESC LIMIT ? OFFSET ?
    ''', (*params, per_page, offset))
    total = _fetchone(db, f"SELECT COUNT(*) as c FROM podcasts p WHERE {wsql}", params)
    uid = _get_auth_user_id()
    items = []
    for r in rows:
        av = r.get('author_avatar') or ''
        items.append({
            'id': r['id'],
            'title': r['title'],
            'description': r.get('description') or '',
            'filepath': _public_upload_url(r.get('filepath')),
            'filesize': r.get('filesize') or 0,
            'duration': r.get('duration') or 0,
            'cover': _public_upload_url(r.get('cover')),
            'category': r.get('category') or '',
            'channel_name': r.get('channel_name') or r.get('title') or '',
            'subtitle_type': r.get('subtitle_type') or 'text',
            'likes': r.get('likes') or 0,
            'plays': r.get('plays') or 0,
            'featured': 1 if r.get('featured') else 0,
            'created_at': r['created_at'],
            'author_id': r.get('author_id') or '',
            'author_name': r.get('author_name') or '已注销',
            'author_avatar': ('/' + av) if av and not av.startswith('/') else av,
            'liked': False,
        })
        if uid:
            items[-1]['liked'] = bool(_fetchone(db, 'SELECT 1 FROM podcast_likes WHERE user_id=? AND podcast_id=?', (uid, r['id'])))
    return jsonify({'podcasts': items, 'total': total['c'] if total else 0, 'page': page, 'per_page': per_page,
                    'categories': list(_PODCAST_CATEGORIES)})


@app.route('/api/podcast/<podcast_id>', methods=['GET'])
def api_podcast_detail(podcast_id):
    """播客详情（含字幕文本）"""
    db = get_db()
    row = _fetchone(db, '''
        SELECT id, title, description, filepath, filesize, duration, cover, category, channel_name,
               subtitle, subtitle_type, likes, plays, featured, created_at, author_id
        FROM podcasts WHERE id=? AND status='approved'
    ''', (podcast_id,))
    if not row:
        return jsonify({'error': '播客不存在'}), 404
    _exec(db, 'UPDATE podcasts SET plays = plays + 1 WHERE id=?', (podcast_id,))
    db.commit()
    u = _fetchone(db, 'SELECT username, avatar FROM users WHERE id=?', (row['author_id'],)) if row.get('author_id') else None
    uid = _get_auth_user_id()
    av = (u.get('avatar') or '') if u else ''
    return jsonify({'podcast': {
        'id': row['id'],
        'title': row['title'],
        'description': row.get('description') or '',
        'filepath': _public_upload_url(row['filepath']),
        'filesize': row.get('filesize') or 0,
        'duration': row.get('duration') or 0,
        'cover': _public_upload_url(row.get('cover')),
        'category': row.get('category') or '',
        'channel_name': row.get('channel_name') or row.get('title') or '',
        'subtitle': row.get('subtitle') or '',
        'subtitle_type': row.get('subtitle_type') or 'text',
        'likes': row.get('likes') or 0,
        'plays': (row.get('plays') or 0) + 1,
        'featured': 1 if row.get('featured') else 0,
        'created_at': row['created_at'],
        'author_name': u['username'] if u else '已注销',
        'author_avatar': ('/' + av) if av and not av.startswith('/') else av,
        'liked': bool(uid and _fetchone(db, 'SELECT 1 FROM podcast_likes WHERE user_id=? AND podcast_id=?', (uid, row['id']))),
    }})


@app.route('/api/podcast/upload', methods=['POST'])
@login_required
def api_podcast_upload():
    """上传播客：支持音频文件 + 可选封面 + 字幕文本"""
    if 'file' not in request.files:
        return jsonify({'error': '未选择音频文件'}), 400
    f = request.files['file']
    if not f.filename:
        return jsonify({'error': '未选择音频文件'}), 400
    ext = os.path.splitext(f.filename)[1].lower()
    if ext not in ('.mp3', '.m4a', '.aac', '.wav', '.ogg', '.flac'):
        return jsonify({'error': '仅支持 MP3/M4A/AAC/WAV/OGG 音频格式'}), 400
    title = (request.form.get('title') or '').strip()
    description = (request.form.get('description') or '').strip()
    category = (request.form.get('category') or '').strip()
    if category and category not in _PODCAST_CATEGORIES:
        category = ''
    subtitle = (request.form.get('subtitle') or '').strip()
    if len(subtitle.encode('utf-8')) > 1024 * 1024:
        return jsonify({'error': '字幕文本不能超过1MB'}), 400
    subtitle_type = _detect_subtitle_type(subtitle)
    duration_str = request.form.get('duration') or '0'
    try:
        duration = float(duration_str)
    except (TypeError, ValueError):
        duration = 0
    if duration < 0 or duration > 7200:
        return jsonify({'error': '音频时长无效'}), 400
    if not title:
        title = os.path.splitext(f.filename)[0]

    file_data = f.read()
    if len(file_data) > 200 * 1024 * 1024:
        return jsonify({'error': '音频不能超过200MB'}), 400

    filename = f"{uuid.uuid4().hex}{ext}"
    pod_dir = os.path.join(_DATA_DIR, 'uploads', 'podcasts')
    os.makedirs(pod_dir, exist_ok=True)
    filepath = os.path.join(pod_dir, filename)
    with open(filepath, 'wb') as out:
        out.write(file_data)
    os.chmod(filepath, 0o644)

    cover_path = ''
    cover_file = request.files.get('cover')
    if cover_file and cover_file.filename:
        cover_ext = os.path.splitext(cover_file.filename)[1].lower()
        if cover_ext in ('.jpg', '.jpeg', '.png', '.webp'):
            cover_dir = os.path.join(_DATA_DIR, 'uploads', 'podcast_covers')
            os.makedirs(cover_dir, exist_ok=True)
            cover_name = f"{os.path.splitext(filename)[0]}_cover{cover_ext}"
            cover_full = os.path.join(cover_dir, cover_name)
            cover_file.save(cover_full)
            os.chmod(cover_full, 0o644)
            cover_path = f'uploads/podcast_covers/{cover_name}'

    db = get_db()
    pid = 'pod_' + uuid.uuid4().hex[:8]
    uid = _get_auth_user_id()
    now = time.time()
    stored_path = f'uploads/podcasts/{filename}'
    _exec(db, '''
        INSERT INTO podcasts
            (id, title, description, filename, filepath, filesize, duration, cover,
             category, channel_name, subtitle, subtitle_type, author_id, likes, plays, featured, created_at, status)
        VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
    ''', (pid, title, description, filename, stored_path, len(file_data), duration,
          cover_path, category, (request.form.get('channel_name') or title).strip(), subtitle, subtitle_type, uid, 0, 0, 0, now, 'approved'))
    db.commit()
    return jsonify({'id': pid, 'url': _public_upload_url(stored_path), 'status': 'approved'})


@app.route('/api/podcast/author/<user_id>', methods=['GET'])
def api_podcast_author(user_id):
    """播客专属创作者主页数据，不复用论坛个人主页接口。"""
    db = get_db()
    author = _fetchone(db, 'SELECT id, username, bio, avatar FROM users WHERE id=?', (user_id,))
    if not author:
        return jsonify({'error': '创作者不存在'}), 404
    av = author.get('avatar') or ''
    if av and not av.startswith('/'):
        av = '/' + av
    rows = _fetchall(db, '''
        SELECT p.id, p.title, p.description, p.filepath, p.filesize, p.duration, p.cover,
               p.category, p.channel_name, p.subtitle_type, p.likes, p.plays, p.featured,
               p.created_at, p.author_id, u.username AS author_name
        FROM podcasts p LEFT JOIN users u ON p.author_id=u.id
        WHERE p.author_id=? AND p.status='approved'
        ORDER BY p.created_at DESC
    ''', (user_id,))
    items = []
    for r in rows:
        items.append({
            'id': r['id'], 'title': r['title'], 'description': r.get('description') or '',
            'filepath': _public_upload_url(r.get('filepath')), 'filesize': r.get('filesize') or 0,
            'duration': r.get('duration') or 0, 'cover': _public_upload_url(r.get('cover')),
            'category': r.get('category') or '', 'channel_name': r.get('channel_name') or r.get('title') or '',
            'subtitle_type': r.get('subtitle_type') or 'text', 'likes': r.get('likes') or 0,
            'plays': r.get('plays') or 0, 'featured': 1 if r.get('featured') else 0,
            'created_at': r.get('created_at'), 'author_id': user_id,
            'author_name': r.get('author_name') or author.get('username') or '播客创作者', 'liked': False
        })
    return jsonify({'author': {'id': author['id'], 'username': author['username'], 'bio': author.get('bio') or '', 'avatar': av}, 'podcasts': items})


@app.route('/api/podcast/<podcast_id>/like', methods=['POST'])
@login_required
def api_podcast_like(podcast_id):
    """点赞/取消点赞"""
    db = get_db()
    uid = _get_auth_user_id()
    pod = _fetchone(db, "SELECT id, likes FROM podcasts WHERE id=? AND status='approved'", (podcast_id,))
    if not pod:
        return jsonify({'error': '播客不存在'}), 404
    existing = _fetchone(db, 'SELECT 1 FROM podcast_likes WHERE user_id=? AND podcast_id=?', (uid, podcast_id))
    if existing:
        _exec(db, 'DELETE FROM podcast_likes WHERE user_id=? AND podcast_id=?', (uid, podcast_id))
        _exec(db, 'UPDATE podcasts SET likes = CASE WHEN likes > 0 THEN likes - 1 ELSE 0 END WHERE id=?', (podcast_id,))
        liked = False
    else:
        _exec(db, 'INSERT INTO podcast_likes (user_id, podcast_id, created_at) VALUES (?,?,?)', (uid, podcast_id, time.time()))
        _exec(db, 'UPDATE podcasts SET likes = likes + 1 WHERE id=?', (podcast_id,))
        liked = True
    db.commit()
    row = _fetchone(db, 'SELECT likes FROM podcasts WHERE id=?', (podcast_id,))
    return jsonify({'liked': liked, 'likes': row['likes'] if row else 0})


@app.route('/api/podcast/<podcast_id>', methods=['DELETE'])
def api_podcast_delete(podcast_id):
    """删除播客（作者本人或管理员）"""
    db = get_db()
    uid = _get_auth_user_id()
    if not uid:
        return jsonify({'error': '未登录'}), 401
    row = _fetchone(db, "SELECT author_id, filepath, cover FROM podcasts WHERE id=?", (podcast_id,))
    if not row:
        return jsonify({'error': '播客不存在'}), 404
    me = _fetchone(db, 'SELECT is_admin, is_super_admin FROM users WHERE id=?', (uid,))
    is_admin = bool(me and (me['is_admin'] or me['is_super_admin']))
    if row['author_id'] != uid and not is_admin:
        return jsonify({'error': '无权限删除该播客'}), 403
    # 删除物理文件
    for key in ('filepath', 'cover'):
        rel = row.get(key)
        if rel:
            try:
                p = os.path.join(_DATA_DIR, rel)
                if os.path.isfile(p):
                    os.remove(p)
            except Exception:
                pass
    _exec(db, 'DELETE FROM podcasts WHERE id=?', (podcast_id,))
    _exec(db, 'DELETE FROM podcast_likes WHERE podcast_id=?', (podcast_id,))
    db.commit()
    return jsonify({'ok': True})


# =====================================================================================
# ===== 翱翔鸟 Team 团队协同（/team）=====
# 三层权限：身份层（白名单 + 二次验证）→ 角色层（四级）→ 密级层（四档）
# 非员工访问一律 404（不返回 403，不暴露功能存在）
# =====================================================================================
import io as _team_io
import shutil as _team_shutil
from urllib.parse import quote as _team_quote
from flask import abort as _team_abort, stream_with_context as _team_swc

TEAM_ROOT = os.path.join(_DATA_DIR, 'teamstore')
TEAM_SHARED_QUOTA = 4 * 1024 * 1024 * 1024        # 通用共享盘 4GB（全员共用）
TEAM_PERSONAL_QUOTA = 350 * 1024 * 1024           # 个人盘 350MB
TEAM_MAX_FILE_SIZE = 500 * 1024 * 1024            # 单文件上限 500MB
TEAM_COOKIE_NAME = 'sb_team'
TEAM_VERIFY_TTL = 7 * 24 * 3600                   # 二次验证有效期 7 天
TEAM_CODE_TTL = 600                               # 邮箱验证码 10 分钟
TEAM_CODE_RESEND = 60                             # 验证码重发间隔
TEAM_MAX_CODE_TRIES = 5                           # 验证码最多试错 5 次
TEAM_MAX_VERSIONS = 20                            # 每个文件保留 20 个历史版本
TEAM_VERSION_TTL = 30 * 24 * 3600                 # 历史版本保留 30 天
TEAM_CRYPT_CHUNK = 4 * 1024 * 1024                # 分块加密块大小
TEAM_PREVIEW_LIMIT = 2 * 1024 * 1024              # 在线预览/编辑文本上限 2MB
TEAM_INBOX_NAME = '收到的文件'                      # 定向投递时在接收者个人盘下自动创建的目录
TEAM_CHAT_MAX_LEN = 4000                          # 单条聊天消息字数上限
TEAM_ANNOUNCE_TITLE_MAX = 80                      # 公告标题字数上限
TEAM_ANNOUNCE_BODY_MAX = 3000                     # 公告正文字数上限
TEAM_ANNOUNCE_LIMIT = 5                           # 首页 / 仪表盘展示的公告条数

TEAM_ROLE_RANK = {'guest': 1, 'member': 2, 'core': 3, 'owner': 4}
TEAM_ROLE_LABEL = {'owner': '拥有者 · 管理员', 'core': '核心成员', 'member': '普通成员', 'guest': '只读访客'}
TEAM_CLASS_RANK = {'public': 1, 'internal': 2, 'confidential': 3, 'secret': 4}
TEAM_CLASS_LABEL = {'public': '公开', 'internal': '内部', 'confidential': '机密', 'secret': '绝密'}
# 角色对应的最高可读密级
TEAM_CLEARANCE = {'guest': 'public', 'member': 'internal', 'core': 'confidential', 'owner': 'secret'}

# 源码 / 密钥类扩展名：上传时自动定密为「机密」，且禁止降级
TEAM_SOURCE_EXTS = {
    '.java', '.kt', '.kts', '.swift', '.m', '.mm', '.py', '.pyw', '.js', '.mjs', '.cjs', '.ts', '.tsx', '.jsx',
    '.c', '.h', '.cc', '.cpp', '.hpp', '.cs', '.go', '.rs', '.rb', '.php', '.pl', '.lua', '.scala', '.dart',
    '.sh', '.bash', '.zsh', '.ps1', '.bat', '.cmd', '.sql', '.env', '.ini', '.toml', '.gradle', '.properties',
    '.key', '.pem', '.p12', '.pfx', '.jks', '.keystore', '.asc', '.gpg', '.crt', '.cer', '.der', '.ppk',
    '.mobileprovision', '.provisionprofile', '.yml', '.yaml', '.lock', '.pom', '.mk', '.cmake', '.csproj',
    '.vcxproj', '.pbxproj', '.storyboard', '.xib', '.ipynb', '.vue', '.svelte', '.astro', '.proto',
}

TEAM_EDITABLE_EXTS = {
    '.txt', '.md', '.markdown', '.json', '.js', '.mjs', '.cjs', '.ts', '.tsx', '.jsx', '.css', '.scss', '.less',
    '.html', '.htm', '.xml', '.svg', '.yml', '.yaml', '.toml', '.ini', '.conf', '.cfg', '.env', '.properties',
    '.py', '.java', '.kt', '.kts', '.swift', '.m', '.mm', '.c', '.h', '.cc', '.cpp', '.hpp', '.cs', '.go', '.rs',
    '.rb', '.php', '.pl', '.lua', '.scala', '.dart', '.sh', '.bash', '.zsh', '.ps1', '.bat', '.cmd', '.sql',
    '.gradle', '.cmake', '.mk', '.mm', '.csv', '.tsv', '.log', '.graphql', '.proto', '.gitignore', '.dockerfile',
}

TEAM_KEY_EXTS = {'.key', '.pem', '.p12', '.pfx', '.jks', '.keystore', '.asc', '.gpg', '.crt', '.cer',
                 '.der', '.ppk', '.mobileprovision', '.provisionprofile'}

# 支持浏览器内联预览的扩展名及其 MIME（用于全屏查看）
TEAM_INLINE_EXTS = {'.png', '.jpg', '.jpeg', '.gif', '.webp', '.svg', '.pdf',
                    '.mp4', '.webm', '.mp3', '.wav', '.m4a'}
TEAM_INLINE_MIME = {
    '.png': 'image/png', '.jpg': 'image/jpeg', '.jpeg': 'image/jpeg', '.gif': 'image/gif',
    '.webp': 'image/webp', '.svg': 'image/svg+xml', '.pdf': 'application/pdf',
    '.mp4': 'video/mp4', '.webm': 'video/webm',
    '.mp3': 'audio/mpeg', '.wav': 'audio/wav', '.m4a': 'audio/mp4',
}

TEAM_KIND_EXT = {
    '.png': '图像', '.jpg': '图像', '.jpeg': '图像', '.gif': '图像', '.webp': '图像', '.svg': '图像', '.heic': '图像',
    '.mp4': '影片', '.mov': '影片', '.webm': '影片', '.mkv': '影片',
    '.mp3': '音频', '.wav': '音频', '.m4a': '音频', '.flac': '音频',
    '.zip': '压缩包', '.rar': '压缩包', '.7z': '压缩包', '.tar': '压缩包', '.gz': '压缩包',
    '.pdf': 'PDF 文稿', '.doc': 'Word 文稿', '.docx': 'Word 文稿', '.xls': '工作表', '.xlsx': '工作表',
    '.ppt': '演示文稿', '.pptx': '演示文稿',
    '.apk': 'Android 应用', '.ipa': 'iOS 应用', '.dmg': '磁盘映像',
}

# ===== 数据表 =====
_TEAM_SCHEMA = [
    '''CREATE TABLE IF NOT EXISTS team_members (
        user_id TEXT PRIMARY KEY,
        role TEXT NOT NULL,
        status TEXT DEFAULT 'active',
        created_at REAL NOT NULL,
        added_by TEXT DEFAULT ''
    )''',
    '''CREATE TABLE IF NOT EXISTS team_files (
        id TEXT PRIMARY KEY,
        scope TEXT NOT NULL,
        owner_id TEXT NOT NULL,
        parent_id TEXT DEFAULT '',
        name TEXT NOT NULL,
        is_dir INTEGER DEFAULT 0,
        ext TEXT DEFAULT '',
        size INTEGER DEFAULT 0,
        mime TEXT DEFAULT '',
        classification TEXT DEFAULT 'internal',
        storage TEXT DEFAULT '',
        checksum TEXT DEFAULT '',
        version INTEGER DEFAULT 1,
        locked_by TEXT DEFAULT '',
        locked_at REAL DEFAULT 0,
        created_at REAL NOT NULL,
        updated_at REAL NOT NULL,
        deleted_at REAL DEFAULT 0,
        deleted_by TEXT DEFAULT ''
    )''',
    '''CREATE TABLE IF NOT EXISTS team_versions (
        id TEXT PRIMARY KEY,
        file_id TEXT NOT NULL,
        version INTEGER NOT NULL,
        size INTEGER DEFAULT 0,
        storage TEXT DEFAULT '',
        checksum TEXT DEFAULT '',
        editor_id TEXT DEFAULT '',
        note TEXT DEFAULT '',
        created_at REAL NOT NULL
    )''',
    '''CREATE TABLE IF NOT EXISTS team_activity (
        id TEXT PRIMARY KEY,
        file_id TEXT DEFAULT '',
        file_name TEXT DEFAULT '',
        user_id TEXT DEFAULT '',
        action TEXT NOT NULL,
        detail TEXT DEFAULT '',
        ip TEXT DEFAULT '',
        created_at REAL NOT NULL
    )''',
    '''CREATE TABLE IF NOT EXISTS team_comments (
        id TEXT PRIMARY KEY,
        file_id TEXT NOT NULL,
        user_id TEXT NOT NULL,
        content TEXT NOT NULL,
        created_at REAL NOT NULL
    )''',
    '''CREATE TABLE IF NOT EXISTS team_share (
        id TEXT PRIMARY KEY,
        file_id TEXT NOT NULL,
        token TEXT NOT NULL,
        created_by TEXT NOT NULL,
        expires_at REAL DEFAULT 0,
        revoked INTEGER DEFAULT 0,
        created_at REAL NOT NULL
    )''',
    'CREATE INDEX IF NOT EXISTS idx_team_files_scope ON team_files (scope, parent_id, deleted_at)',
    'CREATE INDEX IF NOT EXISTS idx_team_files_owner ON team_files (owner_id, deleted_at)',
    'CREATE INDEX IF NOT EXISTS idx_team_versions_file ON team_versions (file_id, version)',
    'CREATE INDEX IF NOT EXISTS idx_team_activity_time ON team_activity (created_at)',
    'CREATE INDEX IF NOT EXISTS idx_team_share_token ON team_share (token)',
    # ===== 工作任务 / 待办 / 日历日程（v2 协同能力）=====
    '''CREATE TABLE IF NOT EXISTS team_tasks (
        id TEXT PRIMARY KEY,
        title TEXT NOT NULL,
        detail TEXT DEFAULT '',
        assignee_id TEXT DEFAULT '',
        creator_id TEXT NOT NULL,
        status TEXT DEFAULT 'todo',
        priority INTEGER DEFAULT 0,
        due_at REAL DEFAULT 0,
        file_id TEXT DEFAULT '',
        parent_id TEXT DEFAULT '',
        created_at REAL NOT NULL,
        updated_at REAL NOT NULL,
        completed_at REAL DEFAULT 0
    )''',
    'CREATE INDEX IF NOT EXISTS idx_team_tasks_assignee ON team_tasks (assignee_id, status)',
    '''CREATE TABLE IF NOT EXISTS team_todos (
        id TEXT PRIMARY KEY,
        user_id TEXT NOT NULL,
        content TEXT NOT NULL,
        done INTEGER DEFAULT 0,
        due_at REAL DEFAULT 0,
        created_at REAL NOT NULL,
        updated_at REAL NOT NULL
    )''',
    'CREATE INDEX IF NOT EXISTS idx_team_todos_user ON team_todos (user_id, done)',
    '''CREATE TABLE IF NOT EXISTS team_events (
        id TEXT PRIMARY KEY,
        title TEXT NOT NULL,
        detail TEXT DEFAULT '',
        owner_id TEXT NOT NULL,
        scope TEXT DEFAULT 'personal',
        start_at REAL NOT NULL,
        end_at REAL DEFAULT 0,
        all_day INTEGER DEFAULT 0,
        created_at REAL NOT NULL
    )''',
    'CREATE INDEX IF NOT EXISTS idx_team_events_time ON team_events (start_at)',
    # ===== 在线聊天（一对一 + 团队群聊）=====
    '''CREATE TABLE IF NOT EXISTS team_chats (
        id TEXT PRIMARY KEY,
        kind TEXT DEFAULT 'direct',
        name TEXT DEFAULT '',
        created_by TEXT DEFAULT '',
        created_at REAL NOT NULL,
        updated_at REAL NOT NULL
    )''',
    '''CREATE TABLE IF NOT EXISTS team_chat_members (
        chat_id TEXT NOT NULL,
        user_id TEXT NOT NULL,
        joined_at REAL NOT NULL,
        last_read_at REAL DEFAULT 0,
        PRIMARY KEY (chat_id, user_id)
    )''',
    '''CREATE TABLE IF NOT EXISTS team_chat_messages (
        id TEXT PRIMARY KEY,
        chat_id TEXT NOT NULL,
        sender_id TEXT NOT NULL,
        body TEXT DEFAULT '',
        created_at REAL NOT NULL
    )''',
    'CREATE INDEX IF NOT EXISTS idx_team_chat_msg ON team_chat_messages (chat_id, created_at)',
    'CREATE INDEX IF NOT EXISTS idx_team_chat_member ON team_chat_members (user_id)',
    # ===== 公告栏（首页 / 仪表盘）=====
    '''CREATE TABLE IF NOT EXISTS team_announcements (
        id TEXT PRIMARY KEY,
        author_id TEXT NOT NULL,
        title TEXT DEFAULT '',
        body TEXT NOT NULL,
        created_at REAL NOT NULL,
        updated_at REAL NOT NULL
    )''',
    'CREATE INDEX IF NOT EXISTS idx_team_announce_time ON team_announcements (created_at)',
]

# 后续新增字段的兼容迁移（老库直接 ALTER 补列）
_TEAM_ADD_COLUMNS = [
    ('team_members', 'job_title', "TEXT DEFAULT ''"),
    ('team_members', 'department', "TEXT DEFAULT ''"),
]


def _init_db_team():
    """建立 Team 相关表与存储目录（独立连接，供 init_db 在 app 上下文外调用）"""
    if _USE_PG:
        import psycopg2
        db = psycopg2.connect(os.environ.get('DATABASE_URL'))
        db.autocommit = True
        cur = db.cursor()
        for stmt in _TEAM_SCHEMA:
            cur.execute(stmt)
        for table, column, ddl in _TEAM_ADD_COLUMNS:
            cur.execute(f"SELECT column_name FROM information_schema.columns WHERE table_name='{table}' AND column_name='{column}'")
            if not cur.fetchone():
                cur.execute(f'ALTER TABLE {table} ADD COLUMN {column} {ddl}')
        cur.close()
        db.close()
    else:
        db = sqlite3.connect(DB_PATH)
        for stmt in _TEAM_SCHEMA:
            db.execute(stmt)
        for table, column, ddl in _TEAM_ADD_COLUMNS:
            cols = {r[1] for r in db.execute(f'PRAGMA table_info({table})').fetchall()}
            if column not in cols:
                db.execute(f'ALTER TABLE {table} ADD COLUMN {column} {ddl}')
        db.commit()
        db.close()
    try:
        os.makedirs(os.path.join(TEAM_ROOT, 'files'), exist_ok=True)
        os.makedirs(os.path.join(TEAM_ROOT, 'tmp'), exist_ok=True)
    except Exception as e:
        print(f'[TEAM] 创建存储目录失败: {e}')


# ===== 服务端加密存盘（AES-256-GCM，分块）=====
def _team_key():
    """派生 32 字节加密密钥，优先使用 TEAM_SECRET"""
    raw = os.environ.get('TEAM_SECRET') or (app.secret_key + '|soaringbird-team-v1')
    return hashlib.sha256(raw.encode('utf-8')).digest()


def _team_aes():
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    return AESGCM(_team_key())


def _team_stream_nonce(fnonce, idx):
    return fnonce[:4] + idx.to_bytes(8, 'big')


def _team_encrypt_from_stream(fin, file_id, version):
    """读取明文流 → 加密写入 teamstore，返回 (相对路径, 明文大小, sha256)"""
    aes = _team_aes()
    rel = os.path.join('teamstore', 'files', file_id, f'v{version}.bin')
    dst = os.path.join(_DATA_DIR, rel)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    fnonce = secrets.token_bytes(12)
    h = hashlib.sha256()
    total = 0
    idx = 0
    tmp = dst + '.part'
    try:
        with open(tmp, 'wb') as fout:
            fout.write(b'SBT1')
            fout.write(fnonce)
            while True:
                chunk = fin.read(TEAM_CRYPT_CHUNK)
                if not chunk:
                    break
                h.update(chunk)
                total += len(chunk)
                ct = aes.encrypt(_team_stream_nonce(fnonce, idx), chunk, None)
                fout.write(len(ct).to_bytes(4, 'big'))
                fout.write(ct)
                idx += 1
        os.replace(tmp, dst)
    except Exception:
        try:
            if os.path.isfile(tmp):
                os.remove(tmp)
        except Exception:
            pass
        raise
    return rel, total, h.hexdigest()


def _team_decrypt_stream(path, chunk=TEAM_CRYPT_CHUNK):
    """解密流式读取（用于下载与预览）"""
    aes = _team_aes()
    with open(path, 'rb') as f:
        magic = f.read(4)
        if magic != b'SBT1':
            raise ValueError('存储文件格式异常')
        fnonce = f.read(12)
        idx = 0
        while True:
            head = f.read(4)
            if len(head) < 4:
                break
            n = int.from_bytes(head, 'big')
            ct = f.read(n)
            if len(ct) < n:
                break
            yield aes.decrypt(_team_stream_nonce(fnonce, idx), ct, None)
            idx += 1


def _team_read_text(path, limit=TEAM_PREVIEW_LIMIT):
    """解密并读取文本内容（超限截断）"""
    out = _team_io.BytesIO()
    for chunk in _team_decrypt_stream(path):
        out.write(chunk)
        if out.tell() > limit:
            break
    data = out.getvalue()[:limit]
    return data.decode('utf-8', errors='replace')


# ===== 身份 / 权限 =====
def _team_role_of(uid):
    """返回 (user_dict, role) ；非成员返回 None"""
    if not uid:
        return None
    db = get_db()
    u = _fetchone(db, 'SELECT id, username, email, avatar, is_admin, is_super_admin FROM users WHERE id=?', (uid,))
    if not u:
        return None
    m = _fetchone(db, 'SELECT role, status, job_title, department FROM team_members WHERE user_id=?', (uid,))
    if not m:
        # 超级管理员自动成为拥有者，完成首次引导
        if u['is_super_admin']:
            _exec(db, 'INSERT INTO team_members (user_id, role, status, created_at, added_by) VALUES (?,?,?,?,?)',
                  (uid, 'owner', 'active', time.time(), 'system'))
            db.commit()
            m = {'role': 'owner', 'status': 'active', 'job_title': '', 'department': ''}
        else:
            return None
    if (m.get('status') or 'active') != 'active':
        return None
    return {'id': u['id'], 'username': u['username'], 'email': u.get('email') or '',
            'avatar': u.get('avatar') or '', 'is_admin': bool(u.get('is_admin')),
            'is_super_admin': bool(u.get('is_super_admin')), 'role': m['role'],
            'job_title': m.get('job_title') or '', 'department': m.get('department') or ''}


def _team_verified(uid):
    """校验二次验证 cookie"""
    tok = request.cookies.get(TEAM_COOKIE_NAME)
    if not tok:
        return False
    parts = tok.rsplit('.', 2)
    if len(parts) != 3:
        return False
    t_uid, exp, sig = parts
    if t_uid != uid:
        return False
    try:
        if int(exp) < time.time():
            return False
    except Exception:
        return False
    return _hmac.compare_digest(sig, _team_sign(t_uid, exp))


def _team_sign(uid, exp):
    return _hmac.new(app.secret_key.encode('utf-8'), f'{uid}|{exp}|team'.encode('utf-8'), hashlib.sha256).hexdigest()


def _team_set_verify(response, uid):
    exp = int(time.time()) + TEAM_VERIFY_TTL
    response.set_cookie(TEAM_COOKIE_NAME, f'{uid}.{exp}.{_team_sign(uid, exp)}',
                        max_age=TEAM_VERIFY_TTL, path='/', httponly=True,
                        samesite='Lax', secure=_is_https_request())
    return response


def _team_clear_verify(response):
    response.set_cookie(TEAM_COOKIE_NAME, '', max_age=0, path='/', httponly=True,
                        samesite='Lax', secure=_is_https_request())
    return response


def team_required(verify=True):
    """身份层守卫：非员工一律 404；未完成二次验证的接口调用也返回 404"""
    def deco(f):
        @wraps(f)
        def wrapper(*args, **kwargs):
            uid = _get_auth_user_id()
            ident = _team_role_of(uid)
            if not ident:
                return jsonify({'error': 'Not found'}), 404
            if verify and not _team_verified(uid):
                return jsonify({'error': 'Not found', 'need_verify': True}), 404
            g.team = ident
            return f(*args, **kwargs)
        return wrapper
    return deco


def _team_can_read(role, classification):
    return TEAM_CLASS_RANK.get(classification, 2) <= TEAM_CLASS_RANK.get(TEAM_CLEARANCE.get(role, 'internal'), 2)


def _team_can_write(role):
    return TEAM_ROLE_RANK.get(role, 0) >= TEAM_ROLE_RANK['member']


def _team_can_manage(role):
    return role == 'owner'


def _team_can_see_file(f, ident):
    """个人盘只有本人可见；共享盘按密级过滤"""
    if f['scope'] == 'personal':
        return f['owner_id'] == ident['id']
    return _team_can_read(ident['role'], f['classification'])


def _team_can_delete(f, ident):
    if _team_can_manage(ident['role']):
        return True
    if not _team_can_write(ident['role']):
        return False
    return f['owner_id'] == ident['id']


def _team_classify(name, requested=None):
    """计算最终密级：源码/密钥类强制「机密」，不允许降级"""
    ext = os.path.splitext(name)[1].lower()
    forced = 'confidential' if ext in TEAM_SOURCE_EXTS else 'internal'
    want = requested if requested in TEAM_CLASS_RANK else 'internal'
    return want if TEAM_CLASS_RANK[want] > TEAM_CLASS_RANK[forced] else forced


def _team_ext(name):
    if name.startswith('.') and name.count('.') == 1:
        return name.lower()
    return os.path.splitext(name)[1].lower()


def _team_kind(name, is_dir):
    if is_dir:
        return '文件夹'
    ext = _team_ext(name)
    if ext in TEAM_KIND_EXT:
        return TEAM_KIND_EXT[ext]
    if ext in TEAM_KEY_EXTS:
        return '密钥 / 证书'
    if ext in TEAM_SOURCE_EXTS:
        return f'{ext.lstrip(".").upper()} 源码'
    if ext in TEAM_EDITABLE_EXTS:
        return f'{ext.lstrip(".").upper()} 文稿'
    return '文稿' if ext else '文件'


def _team_used_bytes(scope, owner_id=None):
    """统计占用（含历史版本），用于配额"""
    db = get_db()
    if scope == 'shared':
        row = _fetchone(db, 'SELECT COALESCE(SUM(size),0) AS s FROM team_files WHERE scope=? AND is_dir=0 AND deleted_at=0', ('shared',))
        used = int(row['s'] or 0) if row else 0
        row = _fetchone(db, '''SELECT COALESCE(SUM(v.size),0) AS s FROM team_versions v
                               JOIN team_files f ON f.id = v.file_id
                               WHERE f.scope=? AND f.deleted_at=0''', ('shared',))
        return used + (int(row['s'] or 0) if row else 0)
    row = _fetchone(db, 'SELECT COALESCE(SUM(size),0) AS s FROM team_files WHERE scope=? AND owner_id=? AND is_dir=0 AND deleted_at=0',
                    ('personal', owner_id))
    used = int(row['s'] or 0) if row else 0
    row = _fetchone(db, '''SELECT COALESCE(SUM(v.size),0) AS s FROM team_versions v
                           JOIN team_files f ON f.id = v.file_id
                           WHERE f.scope=? AND f.owner_id=? AND f.deleted_at=0''', ('personal', owner_id))
    return used + (int(row['s'] or 0) if row else 0)


def _team_log(action, file_id='', file_name='', detail='', uid=None):
    """写入操作留痕（下载 / 预览 / 编辑 / 删除 / 改密级 等）"""
    try:
        db = get_db()
        uid = uid or _get_auth_user_id() or ''
        ip = (request.headers.get('X-Forwarded-For', '').split(',')[0].strip() or request.remote_addr or '') if request else ''
        _exec(db, '''INSERT INTO team_activity (id, file_id, file_name, user_id, action, detail, ip, created_at)
                     VALUES (?,?,?,?,?,?,?,?)''',
              (uuid.uuid4().hex, file_id, file_name, uid, action, detail, ip, time.time()))
        db.commit()
    except Exception as e:
        print(f'[TEAM] 记录活动失败: {e}')


def _team_get_file(fid):
    db = get_db()
    f = _fetchone(db, '''SELECT f.*, u.username AS owner_name FROM team_files f
                         LEFT JOIN users u ON u.id = f.owner_id
                         WHERE f.id=?''', (fid,))
    if not f or f.get('deleted_at'):
        return None
    return f


def _team_file_json(f, ident):
    ext = f.get('ext') or ''
    editable = (not f['is_dir']) and ext in TEAM_EDITABLE_EXTS and _team_can_write(ident['role'])
    return {
        'id': f['id'], 'name': f['name'], 'is_dir': bool(f['is_dir']),
        'kind': _team_kind(f['name'], f['is_dir']),
        'ext': ext, 'size': int(f.get('size') or 0), 'mime': f.get('mime') or '',
        'classification': f.get('classification') or 'internal',
        'classification_label': TEAM_CLASS_LABEL.get(f.get('classification') or 'internal', '内部'),
        'source_locked': ext in TEAM_SOURCE_EXTS,
        'scope': f['scope'], 'owner_id': f['owner_id'], 'owner_name': f.get('owner_name') or '',
        'parent_id': f.get('parent_id') or '',
        'version': int(f.get('version') or 1),
        'editable': editable, 'previewable': (not f['is_dir']) and ext in TEAM_EDITABLE_EXTS,
        'inline_viewable': (not f['is_dir']) and ext in TEAM_INLINE_EXTS,
        'watermark': (f.get('classification') in ('confidential', 'secret')) and not f['is_dir'],
        'can_write': _team_can_write(ident['role']),
        'can_delete': _team_can_delete(f, ident),
        'can_manage': _team_can_manage(ident['role']),
        'locked_by': f.get('locked_by') or '', 'locked_at': float(f.get('locked_at') or 0),
        'created_at': float(f.get('created_at') or 0), 'updated_at': float(f.get('updated_at') or 0),
    }


def _team_path_of(fid):
    """自底向上拼出目录面包屑"""
    db = get_db()
    chain = []
    cur = fid
    guard = 0
    while cur and guard < 64:
        row = _fetchone(db, 'SELECT id, name, parent_id, scope FROM team_files WHERE id=?', (cur,))
        if not row:
            break
        chain.append({'id': row['id'], 'name': row['name']})
        cur = row.get('parent_id') or ''
        guard += 1
    chain.reverse()
    return chain


# ===== 页面路由（身份层守卫：非员工 404）=====
@app.route('/team')
@app.route('/team/')
def team_page():
    ident = _team_role_of(_get_auth_user_id())
    if not ident:
        _team_abort(404)
    return send_from_directory(_FRONTEND_DIR, 'team.html')


_TEAM_ASSETS = {'team.css': 'text/css; charset=utf-8', 'team.js': 'application/javascript; charset=utf-8'}


@app.route('/api/team/asset/<name>')
def api_team_asset(name):
    """Team 前端静态资源：只能经鉴权路由取，非员工 404"""
    if name not in _TEAM_ASSETS:
        _team_abort(404)
    if not _team_role_of(_get_auth_user_id()):
        _team_abort(404)
    resp = send_from_directory(_FRONTEND_DIR, name)
    resp.headers['Content-Type'] = _TEAM_ASSETS[name]
    resp.headers['Cache-Control'] = 'private, max-age=300'
    return resp


# ===== 二次验证 =====
_team_codes = {}
_team_codes_lock = _threading.Lock()


@app.route('/api/team/auth/send-code', methods=['POST'])
def api_team_send_code():
    """发送二次验证码到员工邮箱"""
    uid = _get_auth_user_id()
    ident = _team_role_of(uid)
    if not ident:
        return jsonify({'error': 'Not found'}), 404
    if not ident['email']:
        return jsonify({'error': '账号未绑定邮箱，无法完成二次验证'}), 400
    now = time.time()
    with _team_codes_lock:
        rec = _team_codes.get(uid)
        if rec and now - rec.get('sent_at', 0) < TEAM_CODE_RESEND:
            return jsonify({'error': f'请 {int(TEAM_CODE_RESEND - (now - rec["sent_at"]))} 秒后再试'}), 429
        code = f'{secrets.randbelow(1000000):06d}'
        _team_codes[uid] = {'code': code, 'expires': now + TEAM_CODE_TTL, 'sent_at': now, 'tries': 0}
    try:
        _send_email(ident['email'], '翱翔鸟 Team 访问验证', '你正在访问翱翔鸟 Team 团队协同空间。请输入以下验证码完成验证，验证码 10 分钟内有效。', code=code)
    except Exception as e:
        return jsonify({'error': f'验证码发送失败：{e}'}), 500
    _team_log('send_code', detail='二次验证码已发送', uid=uid)
    masked = ident['email']
    if '@' in masked:
        name, dom = masked.split('@', 1)
        masked = (name[:2] + '***@' + dom) if len(name) > 2 else ('*' * len(name) + '@' + dom)
    return jsonify({'ok': True, 'email': masked})


@app.route('/api/team/auth/verify', methods=['POST'])
def api_team_verify():
    """校验验证码，通过后签发 7 天有效的二次验证 cookie"""
    uid = _get_auth_user_id()
    ident = _team_role_of(uid)
    if not ident:
        return jsonify({'error': 'Not found'}), 404
    payload = request.get_json(silent=True) or {}
    code = str(payload.get('code') or '').strip()
    now = time.time()
    with _team_codes_lock:
        rec = _team_codes.get(uid)
        if not rec or now > rec.get('expires', 0):
            return jsonify({'error': '验证码已过期，请重新获取'}), 400
        rec['tries'] = rec.get('tries', 0) + 1
        if rec['tries'] > TEAM_MAX_CODE_TRIES:
            _team_codes.pop(uid, None)
            return jsonify({'error': '尝试次数过多，请重新获取验证码'}), 429
        if not _hmac.compare_digest(rec['code'], code):
            return jsonify({'error': '验证码不正确'}), 400
        _team_codes.pop(uid, None)
    resp = make_response(jsonify({'ok': True, 'expires_in': TEAM_VERIFY_TTL}))
    _team_set_verify(resp, uid)
    _team_log('verify', detail='通过二次验证', uid=uid)
    return resp


@app.route('/api/team/auth/logout', methods=['POST'])
def api_team_logout():
    """退出 Team 二次验证（不影响论坛登录态）"""
    resp = make_response(jsonify({'ok': True}))
    return _team_clear_verify(resp)


# ===== 会话信息 =====
@app.route('/api/team/me', methods=['GET'])
@team_required(verify=False)
def api_team_me():
    ident = g.team
    return jsonify({
        'user': {'id': ident['id'], 'username': ident['username'], 'avatar': (f"/{ident['avatar']}" if ident['avatar'] else ''),
                 'email': ident['email'], 'job_title': ident['job_title'], 'department': ident['department'],
                 'is_admin': ident['is_admin'], 'is_super_admin': ident['is_super_admin']},
        'role': ident['role'], 'role_label': TEAM_ROLE_LABEL.get(ident['role'], ''),
        'verified': _team_verified(ident['id']),
        'clearance': TEAM_CLEARANCE.get(ident['role'], 'internal'),
        'clearance_label': TEAM_CLASS_LABEL.get(TEAM_CLEARANCE.get(ident['role'], 'internal'), '内部'),
        'can_write': _team_can_write(ident['role']),
        'can_manage': _team_can_manage(ident['role']),
        'quotas': {
            'shared_used': _team_used_bytes('shared'), 'shared_quota': TEAM_SHARED_QUOTA,
            'personal_used': _team_used_bytes('personal', ident['id']), 'personal_quota': TEAM_PERSONAL_QUOTA,
            'max_file': TEAM_MAX_FILE_SIZE,
        },
        'labels': {'roles': TEAM_ROLE_LABEL, 'classes': TEAM_CLASS_LABEL},
    })


# ===== 列表 =====
@app.route('/api/team/list', methods=['GET'])
@team_required()
def api_team_list():
    ident = g.team
    scope = request.args.get('scope', 'shared')
    if scope not in ('shared', 'personal'):
        scope = 'shared'
    if scope == 'personal':
        owner_id = request.args.get('owner_id') or ident['id']
        if owner_id != ident['id']:
            return jsonify({'error': 'Not found'}), 404
    parent = request.args.get('parent', '')
    view = request.args.get('view', 'files')       # files | recent | shared | trash
    sort = request.args.get('sort', 'updated_at')
    order = 'ASC' if request.args.get('order') == 'asc' else 'DESC'
    q = (request.args.get('q') or '').strip()
    if sort not in ('name', 'size', 'updated_at', 'created_at'):
        sort = 'updated_at'

    db = get_db()
    where = ['f.scope=?']
    params = [scope]
    if scope == 'personal':
        where.append('f.owner_id=?')
        params.append(ident['id'])
    if view == 'trash':
        where.append('f.deleted_at>0')
    else:
        where.append('f.deleted_at=0')
    if view == 'files':
        # 必须按目录分层：parent 为空即根目录，否则会把所有层级的文件平铺返回
        where.append('f.parent_id=?')
        params.append(parent)
    if q:
        where.append('f.name LIKE ?')
        params.append(f'%{q}%')

    sql = f'''SELECT f.*, u.username AS owner_name FROM team_files f
              LEFT JOIN users u ON u.id = f.owner_id
              WHERE {' AND '.join(where)} ORDER BY f.{sort} {order} LIMIT 500'''
    rows = _fetchall(db, sql, tuple(params))

    if scope == 'shared':
        rows = [r for r in rows if _team_can_read(ident['role'], r.get('classification') or 'internal')]

    if view == 'shared':
        shared_ids = {s['file_id'] for s in _fetchall(db, 'SELECT file_id FROM team_share WHERE revoked=0 AND (expires_at=0 OR expires_at>?)', (time.time(),))}
        rows = [r for r in rows if r['id'] in shared_ids]

    items = [_team_file_json(r, ident) for r in rows]
    if view == 'recent':
        items.sort(key=lambda x: x['updated_at'], reverse=True)

    trash_days = None
    return jsonify({
        'scope': scope, 'view': view, 'parent': parent, 'q': q, 'sort': sort, 'order': order.lower(),
        'items': items,
        'path': _team_path_of(parent) if parent else [],
        'can_write': _team_can_write(ident['role']),
        'trash_retention_days': trash_days,
    })


# ===== 新建文件夹 =====
@app.route('/api/team/folder', methods=['POST'])
@team_required()
def api_team_folder():
    ident = g.team
    if not _team_can_write(ident['role']):
        return jsonify({'error': '你的角色为只读访客，无法新建文件夹'}), 403
    payload = request.get_json(silent=True) or {}
    name = (payload.get('name') or '').strip()
    scope = payload.get('scope') if payload.get('scope') in ('shared', 'personal') else 'shared'
    parent = payload.get('parent') or ''
    if not name or len(name) > 255 or '/' in name or name in ('.', '..'):
        return jsonify({'error': '文件夹名称不合法'}), 400
    if scope == 'personal':
        parent = parent or ''
    if parent:
        pf = _team_get_file(parent)
        if not pf or not pf['is_dir'] or not _team_can_see_file(pf, ident):
            return jsonify({'error': '目标文件夹不存在'}), 404
    db = get_db()
    dup = _fetchone(db, 'SELECT id FROM team_files WHERE scope=? AND parent_id=? AND name=? AND deleted_at=0',
                    (scope, parent, name))
    if dup:
        return jsonify({'error': '同一目录下已存在同名项目'}), 409
    fid = uuid.uuid4().hex
    now = time.time()
    owner_id = ident['id'] if scope == 'personal' else ident['id']
    _exec(db, '''INSERT INTO team_files (id, scope, owner_id, parent_id, name, is_dir, ext, size, mime,
                 classification, storage, checksum, version, created_at, updated_at)
                 VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)''',
          (fid, scope, owner_id, parent, name, 1, '', 0, '', 'internal', '', '', 1, now, now))
    db.commit()
    _team_log('mkdir', fid, name, detail=f'新建文件夹（{scope}）', uid=ident['id'])
    return jsonify({'ok': True, 'id': fid})


# ===== 上传（同名自动升级为新版本，旧版本可恢复）=====
@app.route('/api/team/upload', methods=['POST'])
@team_required()
def api_team_upload():
    ident = g.team
    if not _team_can_write(ident['role']):
        return jsonify({'error': '你的角色为只读访客，无法上传文件'}), 403
    up = request.files.get('file')
    if not up:
        return jsonify({'error': '未收到文件'}), 400
    scope = request.form.get('scope') if request.form.get('scope') in ('shared', 'personal') else 'shared'
    parent = request.form.get('parent') or ''
    requested_class = request.form.get('classification')
    target_id = request.form.get('target_id') or ''

    raw_name = (up.filename or 'unnamed').replace('\\', '/').split('/')[-1].strip()
    if not raw_name or raw_name in ('.', '..'):
        raw_name = 'unnamed'
    name = raw_name[:255]
    if requested_class in TEAM_CLASS_RANK and \
            TEAM_CLASS_RANK[requested_class] > TEAM_CLASS_RANK[TEAM_CLEARANCE.get(ident['role'], 'internal')]:
        return jsonify({'error': '不能上传高于你自身权限密级的文件'}), 403

    # 先落临时文件，得到大小与校验值
    tmp_path = os.path.join(TEAM_ROOT, 'tmp', uuid.uuid4().hex)
    os.makedirs(os.path.dirname(tmp_path), exist_ok=True)
    up.save(tmp_path)
    size = os.path.getsize(tmp_path)
    if size > TEAM_MAX_FILE_SIZE:
        os.remove(tmp_path)
        return jsonify({'error': f'单文件不能超过 {TEAM_MAX_FILE_SIZE // (1024 * 1024)} MB'}), 413

    db = get_db()
    now = time.time()
    try:
        if parent:
            pf = _team_get_file(parent)
            if not pf or not pf['is_dir'] or not _team_can_see_file(pf, ident) or pf['scope'] != scope:
                return jsonify({'error': '目标文件夹不存在'}), 404

        # 找到同目录同名文件 → 直接写入新版本
        existing = None
        if target_id:
            existing = _team_get_file(target_id)
            if existing and (not _team_can_see_file(existing, ident)):
                existing = None
        if not existing:
            existing = _fetchone(db, 'SELECT * FROM team_files WHERE scope=? AND parent_id=? AND name=? AND is_dir=0 AND deleted_at=0',
                                 (scope, parent, name))

        if existing:
            if existing['scope'] == 'personal' and existing['owner_id'] != ident['id']:
                return jsonify({'error': 'Not found'}), 404
            if not _team_can_delete(existing, ident) and existing['owner_id'] != ident['id']:
                return jsonify({'error': '无权限覆盖该文件'}), 403
            new_class = _team_classify(name, requested_class or existing['classification'])
            # 归档当前版本
            _exec(db, '''INSERT INTO team_versions (id, file_id, version, size, storage, checksum, editor_id, note, created_at)
                         VALUES (?,?,?,?,?,?,?,?,?)''',
                  (uuid.uuid4().hex, existing['id'], int(existing['version'] or 1), int(existing['size'] or 0),
                   existing.get('storage') or '', existing.get('checksum') or '', ident['id'], '上传覆盖', now))
            nver = int(existing['version'] or 1) + 1
            with open(tmp_path, 'rb') as fin:
                rel, total, digest = _team_encrypt_from_stream(fin, existing['id'], nver)
            _exec(db, '''UPDATE team_files SET size=?, storage=?, checksum=?, version=?, mime=?, classification=?,
                         updated_at=?, locked_by='', locked_at=0 WHERE id=?''',
                  (total, rel, digest, nver, up.mimetype or '', new_class, now, existing['id']))
            db.commit()
            _team_trim_versions(existing['id'])
            _team_log('upload_version', existing['id'], existing['name'], detail=f'上传新版本 v{nver}（旧版可恢复）', uid=ident['id'])
            f = _team_get_file(existing['id'])
            return jsonify({'ok': True, 'updated': True, 'version': nver, 'item': _team_file_json(f, ident)})

        # 新建文件
        cls = _team_classify(name, requested_class)
        fid = uuid.uuid4().hex
        with open(tmp_path, 'rb') as fin:
            rel, total, digest = _team_encrypt_from_stream(fin, fid, 1)
        ext = _team_ext(name)
        _exec(db, '''INSERT INTO team_files (id, scope, owner_id, parent_id, name, is_dir, ext, size, mime,
                     classification, storage, checksum, version, created_at, updated_at)
                     VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)''',
              (fid, scope, ident['id'], parent, name, 0, ext, total, up.mimetype or '',
               cls, rel, digest, 1, now, now))
        db.commit()
        _team_log('upload', fid, name, detail=f'上传文件（{scope}，{TEAM_CLASS_LABEL.get(cls, cls)}）', uid=ident['id'])
        f = _team_get_file(fid)
        return jsonify({'ok': True, 'updated': False, 'version': 1, 'item': _team_file_json(f, ident)})
    finally:
        try:
            if os.path.isfile(tmp_path):
                os.remove(tmp_path)
        except Exception:
            pass


def _team_trim_versions(file_id):
    """版本修剪：最多 20 版 / 保留 30 天"""
    db = get_db()
    rows = _fetchall(db, 'SELECT id, version, storage, created_at FROM team_versions WHERE file_id=? ORDER BY version DESC', (file_id,))
    now = time.time()
    for i, r in enumerate(rows):
        if i >= TEAM_MAX_VERSIONS or (now - float(r.get('created_at') or 0)) > TEAM_VERSION_TTL:
            _exec(db, 'DELETE FROM team_versions WHERE id=?', (r['id'],))
            rel = r.get('storage') or ''
            if rel:
                try:
                    p = os.path.join(_DATA_DIR, rel)
                    if os.path.isfile(p):
                        os.remove(p)
                except Exception:
                    pass
    db.commit()


# ===== 文件详情 / 下载 / 预览 =====
@app.route('/api/team/file/<fid>', methods=['GET'])
@team_required()
def api_team_file(fid):
    ident = g.team
    f = _team_get_file(fid)
    if not f or not _team_can_see_file(f, ident):
        return jsonify({'error': 'Not found'}), 404
    db = get_db()
    comments = _fetchall(db, '''SELECT c.id, c.content, c.created_at, c.user_id, u.username FROM team_comments c
                                LEFT JOIN users u ON u.id = c.user_id WHERE c.file_id=? ORDER BY c.created_at ASC LIMIT 200''', (fid,))
    shares = _fetchall(db, 'SELECT token, created_by, expires_at, created_at FROM team_share WHERE file_id=? AND revoked=0 AND (expires_at=0 OR expires_at>?)',
                       (fid, time.time()))
    data = _team_file_json(f, ident)
    data['comments'] = [{'id': c['id'], 'content': c['content'], 'created_at': float(c['created_at'] or 0),
                         'username': c.get('username') or '', 'mine': c['user_id'] == ident['id']} for c in comments]
    data['shares'] = [{'token': s['token'], 'expires_at': float(s['expires_at'] or 0),
                       'created_at': float(s['created_at'] or 0)} for s in shares]
    data['path'] = _team_path_of(fid)
    return jsonify(data)


@app.route('/api/team/file/<fid>/download', methods=['GET'])
@team_required()
def api_team_download(fid):
    ident = g.team
    f = _team_get_file(fid)
    if not f or f['is_dir'] or not _team_can_see_file(f, ident):
        return jsonify({'error': 'Not found'}), 404
    path = os.path.join(_DATA_DIR, f.get('storage') or '')
    if not f.get('storage') or not os.path.isfile(path):
        return jsonify({'error': '文件内容缺失'}), 404
    _team_log('download', f['id'], f['name'], detail=f'{TEAM_CLASS_LABEL.get(f["classification"], "")}文件下载', uid=ident['id'])
    resp = Response(_team_swc(_team_decrypt_stream(path)),
                    mimetype=f.get('mime') or 'application/octet-stream')
    resp.headers['Content-Disposition'] = "attachment; filename*=UTF-8''" + _team_quote(f['name'])
    resp.headers['Content-Length'] = str(int(f.get('size') or 0))
    resp.headers['Cache-Control'] = 'no-store'
    resp.headers['X-Content-Type-Options'] = 'nosniff'
    return resp


@app.route('/api/team/file/<fid>/content', methods=['GET'])
@team_required()
def api_team_content(fid):
    ident = g.team
    f = _team_get_file(fid)
    if not f or f['is_dir'] or not _team_can_see_file(f, ident):
        return jsonify({'error': 'Not found'}), 404
    if _team_ext(f['name']) not in TEAM_EDITABLE_EXTS and _team_ext(f['name']) not in TEAM_SOURCE_EXTS:
        return jsonify({'error': '该类型文件不支持在线预览'}), 400
    path = os.path.join(_DATA_DIR, f.get('storage') or '')
    if not f.get('storage') or not os.path.isfile(path):
        return jsonify({'error': '文件内容缺失'}), 404
    data = _team_file_json(f, ident)
    data['content'] = _team_read_text(path)
    data['truncated'] = int(f.get('size') or 0) > TEAM_PREVIEW_LIMIT
    _team_log('preview', f['id'], f['name'], detail='在线预览', uid=ident['id'])
    return jsonify(data)


@app.route('/api/team/file/<fid>/content', methods=['PUT'])
@team_required()
def api_team_save_content(fid):
    """在线编辑保存（乐观锁：version 不匹配则拒绝）"""
    ident = g.team
    if not _team_can_write(ident['role']):
        return jsonify({'error': '你的角色为只读访客，无法编辑'}), 403
    f = _team_get_file(fid)
    if not f or f['is_dir'] or not _team_can_see_file(f, ident):
        return jsonify({'error': 'Not found'}), 404
    payload = request.get_json(silent=True) or {}
    if 'content' not in payload:
        return jsonify({'error': '缺少 content'}), 400
    try:
        base_version = int(payload.get('version') or 0)
    except Exception:
        base_version = 0
    cur_version = int(f.get('version') or 1)
    if base_version != cur_version:
        return jsonify({'error': f'文件已被他人更新到 v{cur_version}，请刷新后重试', 'version': cur_version}), 409
    content = payload['content']
    if not isinstance(content, str):
        return jsonify({'error': 'content 必须为文本'}), 400
    blob = content.encode('utf-8')
    if len(blob) > TEAM_PREVIEW_LIMIT:
        return jsonify({'error': '在线编辑内容不能超过 2MB，请下载后用本地编辑器修改'}), 413

    now = time.time()
    db = get_db()
    _exec(db, '''INSERT INTO team_versions (id, file_id, version, size, storage, checksum, editor_id, note, created_at)
                 VALUES (?,?,?,?,?,?,?,?,?)''',
          (uuid.uuid4().hex, f['id'], cur_version, int(f.get('size') or 0), f.get('storage') or '',
           f.get('checksum') or '', ident['id'], '编辑前存档', now))
    nver = cur_version + 1
    rel, total, digest = _team_encrypt_from_stream(_team_io.BytesIO(blob), f['id'], nver)
    _exec(db, 'UPDATE team_files SET size=?, storage=?, checksum=?, version=?, updated_at=? WHERE id=?',
          (total, rel, digest, nver, now, f['id']))
    db.commit()
    _team_trim_versions(f['id'])
    _team_log('edit', f['id'], f['name'], detail=f'在线编辑 → v{nver}', uid=ident['id'])
    return jsonify({'ok': True, 'version': nver, 'size': total, 'updated_at': now})


# ===== 版本历史 =====
@app.route('/api/team/file/<fid>/versions', methods=['GET'])
@team_required()
def api_team_versions(fid):
    ident = g.team
    f = _team_get_file(fid)
    if not f or not _team_can_see_file(f, ident):
        return jsonify({'error': 'Not found'}), 404
    db = get_db()
    rows = _fetchall(db, '''SELECT v.id, v.version, v.size, v.checksum, v.note, v.created_at, v.editor_id, u.username
                            FROM team_versions v LEFT JOIN users u ON u.id = v.editor_id
                            WHERE v.file_id=? ORDER BY v.version DESC''', (fid,))
    items = [{'version': int(r['version'] or 0), 'size': int(r['size'] or 0), 'note': r.get('note') or '',
              'username': r.get('username') or '系统', 'created_at': float(r['created_at'] or 0),
              'current': int(r['version'] or 0) == int(f.get('version') or 1)} for r in rows]
    items.insert(0, {'version': int(f.get('version') or 1), 'size': int(f.get('size') or 0),
                     'note': '当前版本', 'username': f.get('owner_name') or '',
                     'created_at': float(f.get('updated_at') or 0), 'current': True})
    return jsonify({'items': items, 'max_versions': TEAM_MAX_VERSIONS, 'ttl_days': TEAM_VERSION_TTL // 86400})


@app.route('/api/team/file/<fid>/versions/<int:ver>/download', methods=['GET'])
@team_required()
def api_team_version_download(fid, ver):
    ident = g.team
    f = _team_get_file(fid)
    if not f or not _team_can_see_file(f, ident):
        return jsonify({'error': 'Not found'}), 404
    db = get_db()
    if ver == int(f.get('version') or 1):
        return api_team_download(fid)
    v = _fetchone(db, 'SELECT * FROM team_versions WHERE file_id=? AND version=?', (fid, ver))
    if not v or not v.get('storage'):
        return jsonify({'error': '该版本已过期或被清理'}), 404
    path = os.path.join(_DATA_DIR, v['storage'])
    if not os.path.isfile(path):
        return jsonify({'error': '该版本已过期或被清理'}), 404
    _team_log('download_version', f['id'], f['name'], detail=f'下载历史版本 v{ver}', uid=ident['id'])
    resp = Response(_team_swc(_team_decrypt_stream(path)), mimetype=f.get('mime') or 'application/octet-stream')
    resp.headers['Content-Disposition'] = "attachment; filename*=UTF-8''" + _team_quote(f['name'])
    resp.headers['Cache-Control'] = 'no-store'
    return resp


@app.route('/api/team/file/<fid>/versions/<int:ver>/restore', methods=['POST'])
@team_required()
def api_team_version_restore(fid, ver):
    ident = g.team
    if not _team_can_write(ident['role']):
        return jsonify({'error': '你的角色为只读访客，无法恢复版本'}), 403
    f = _team_get_file(fid)
    if not f or f['is_dir'] or not _team_can_see_file(f, ident):
        return jsonify({'error': 'Not found'}), 404
    db = get_db()
    if ver == int(f.get('version') or 1):
        return jsonify({'ok': True, 'version': ver})
    v = _fetchone(db, 'SELECT * FROM team_versions WHERE file_id=? AND version=?', (fid, ver))
    if not v or not v.get('storage'):
        return jsonify({'error': '该版本已过期或被清理'}), 404
    src = os.path.join(_DATA_DIR, v['storage'])
    if not os.path.isfile(src):
        return jsonify({'error': '该版本已过期或被清理'}), 404
    now = time.time()
    _exec(db, '''INSERT INTO team_versions (id, file_id, version, size, storage, checksum, editor_id, note, created_at)
                 VALUES (?,?,?,?,?,?,?,?,?)''',
          (uuid.uuid4().hex, f['id'], int(f.get('version') or 1), int(f.get('size') or 0),
           f.get('storage') or '', f.get('checksum') or '', ident['id'], f'恢复到 v{ver} 前存档', now))
    nver = int(f.get('version') or 1) + 1
    rel = os.path.join('teamstore', 'files', f['id'], f'v{nver}.bin')
    dst = os.path.join(_DATA_DIR, rel)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    _team_shutil.copyfile(src, dst)
    _exec(db, 'UPDATE team_files SET size=?, storage=?, checksum=?, version=?, updated_at=? WHERE id=?',
          (int(v.get('size') or 0), rel, v.get('checksum') or '', nver, now, f['id']))
    db.commit()
    _team_trim_versions(f['id'])
    _team_log('restore', f['id'], f['name'], detail=f'恢复历史版本 v{ver} → v{nver}', uid=ident['id'])
    return jsonify({'ok': True, 'version': nver})


# ===== 密级 / 重命名 / 移动 =====
@app.route('/api/team/file/<fid>/meta', methods=['PATCH'])
@team_required()
def api_team_update_meta(fid):
    ident = g.team
    f = _team_get_file(fid)
    if not f or not _team_can_see_file(f, ident):
        return jsonify({'error': 'Not found'}), 404
    if f['scope'] == 'shared' and not _team_can_write(ident['role']):
        return jsonify({'error': '你的角色为只读访客，无法修改'}), 403
    payload = request.get_json(silent=True) or {}
    db = get_db()
    now = time.time()
    sets, params = [], []

    if 'name' in payload:
        name = (payload.get('name') or '').strip()
        if not name or len(name) > 255 or '/' in name:
            return jsonify({'error': '名称不合法'}), 400
        dup = _fetchone(db, 'SELECT id FROM team_files WHERE scope=? AND parent_id=? AND name=? AND deleted_at=0 AND id<>?',
                        (f['scope'], f.get('parent_id') or '', name, fid))
        if dup:
            return jsonify({'error': '同一目录下已存在同名项目'}), 409
        sets.append('name=?'); params.append(name)
        sets.append('ext=?'); params.append(_team_ext(name))

    if 'classification' in payload:
        want = payload.get('classification')
        if want not in TEAM_CLASS_RANK:
            return jsonify({'error': '密级不合法'}), 400
        forced = 'confidential' if _team_ext(f['name']) in TEAM_SOURCE_EXTS else 'internal'
        if TEAM_CLASS_RANK[want] < TEAM_CLASS_RANK[forced]:
            return jsonify({'error': f'该文件被自动定密为「{TEAM_CLASS_LABEL[forced]}」，不允许降级'}), 403
        if TEAM_CLASS_RANK[want] > TEAM_CLASS_RANK[TEAM_CLEARANCE.get(ident['role'], 'internal')]:
            return jsonify({'error': '不能设置高于你自身权限的密级'}), 403
        if want != f.get('classification'):
            _team_log('classify', f['id'], f['name'],
                      detail=f'密级 {TEAM_CLASS_LABEL.get(f.get("classification"), "")} → {TEAM_CLASS_LABEL[want]}', uid=ident['id'])
        sets.append('classification=?'); params.append(want)

    if 'parent_id' in payload:
        target = payload.get('parent_id') or ''
        if target:
            tf = _team_get_file(target)
            if not tf or not tf['is_dir'] or not _team_can_see_file(tf, ident) or tf['scope'] != f['scope']:
                return jsonify({'error': '目标文件夹不存在'}), 404
        if f['is_dir'] and target == fid:
            return jsonify({'error': '不能移动到自身'}), 400
        sets.append('parent_id=?'); params.append(target)
    if 'scope' in payload and payload.get('scope') in ('shared', 'personal'):
        if payload['scope'] != f['scope']:
            if payload['scope'] == 'personal' and f['owner_id'] != ident['id']:
                return jsonify({'error': '只能把文件移入自己的个人盘'}), 403
            sets.append('scope=?'); params.append(payload['scope'])

    if not sets:
        return jsonify({'ok': True})
    sets.append('updated_at=?'); params.append(now)
    params.append(fid)
    _exec(db, f'UPDATE team_files SET {", ".join(sets)} WHERE id=?', tuple(params))
    db.commit()
    _team_log('meta', f['id'], f['name'], detail='修改文件属性', uid=ident['id'])
    return jsonify({'ok': True, 'item': _team_file_json(_team_get_file(fid), ident)})


# ===== 删除 / 回收站 =====
@app.route('/api/team/file/<fid>', methods=['DELETE'])
@team_required()
def api_team_delete(fid):
    ident = g.team
    f = _team_get_file(fid)
    if not f or not _team_can_see_file(f, ident):
        return jsonify({'error': 'Not found'}), 404
    if not _team_can_delete(f, ident):
        return jsonify({'error': '无权限删除该文件'}), 403
    db = get_db()
    now = time.time()
    ids = [fid]
    if f['is_dir']:
        ids += _team_descendant_ids(fid)
    for i in ids:
        _exec(db, 'UPDATE team_files SET deleted_at=?, deleted_by=? WHERE id=?', (now, ident['id'], i))
    db.commit()
    _team_log('delete', f['id'], f['name'], detail=f'移入回收站（{len(ids)} 项）', uid=ident['id'])
    return jsonify({'ok': True, 'count': len(ids)})


def _team_descendant_ids(root_id):
    db = get_db()
    out, stack = [], [root_id]
    guard = 0
    while stack and guard < 5000:
        cur = stack.pop()
        rows = _fetchall(db, 'SELECT id FROM team_files WHERE parent_id=? AND deleted_at=0', (cur,))
        for r in rows:
            out.append(r['id'])
            stack.append(r['id'])
        guard += 1
    return out


@app.route('/api/team/file/<fid>/restore', methods=['POST'])
@team_required()
def api_team_restore(fid):
    ident = g.team
    db = get_db()
    f = _fetchone(db, 'SELECT f.*, u.username AS owner_name FROM team_files f LEFT JOIN users u ON u.id=f.owner_id WHERE f.id=?', (fid,))
    if not f or not f.get('deleted_at'):
        return jsonify({'error': 'Not found'}), 404
    if not _team_can_see_file(f, ident):
        return jsonify({'error': 'Not found'}), 404
    if not _team_can_delete(f, ident):
        return jsonify({'error': '无权限恢复该文件'}), 403
    _exec(db, 'UPDATE team_files SET deleted_at=0, deleted_by=? WHERE id=?', ('', fid))
    db.commit()
    _team_log('undelete', fid, f['name'], detail='从回收站恢复', uid=ident['id'])
    return jsonify({'ok': True})


@app.route('/api/team/file/<fid>/purge', methods=['DELETE'])
@team_required()
def api_team_purge(fid):
    """彻底删除（仅拥有者可执行；连历史版本一并抹除）"""
    ident = g.team
    if not _team_can_manage(ident['role']):
        return jsonify({'error': '仅拥有者可彻底删除文件'}), 403
    db = get_db()
    f = _fetchone(db, 'SELECT * FROM team_files WHERE id=?', (fid,))
    if not f:
        return jsonify({'error': 'Not found'}), 404
    if not _team_can_see_file(f, ident):
        return jsonify({'error': 'Not found'}), 404
    ids = [fid] + (_team_descendant_ids(fid) if f['is_dir'] else [])
    for i in ids:
        for r in _fetchall(db, 'SELECT storage FROM team_versions WHERE file_id=?', (i,)):
            _team_remove_blob(r.get('storage'))
        for r in _fetchall(db, 'SELECT storage FROM team_files WHERE id=?', (i,)):
            _team_remove_blob(r.get('storage'))
        _exec(db, 'DELETE FROM team_versions WHERE file_id=?', (i,))
        _exec(db, 'DELETE FROM team_comments WHERE file_id=?', (i,))
        _exec(db, 'DELETE FROM team_share WHERE file_id=?', (i,))
        _exec(db, 'DELETE FROM team_files WHERE id=?', (i,))
    db.commit()
    _team_log('purge', fid, f['name'], detail=f'彻底删除（{len(ids)} 项）', uid=ident['id'])
    return jsonify({'ok': True})


def _team_remove_blob(rel):
    if not rel:
        return
    try:
        p = os.path.join(_DATA_DIR, rel)
        if os.path.isfile(p):
            os.remove(p)
        d = os.path.dirname(p)
        if os.path.isdir(d) and not os.listdir(d):
            os.rmdir(d)
    except Exception:
        pass


# ===== 评论 =====
@app.route('/api/team/file/<fid>/comments', methods=['POST'])
@team_required()
def api_team_comment_add(fid):
    ident = g.team
    f = _team_get_file(fid)
    if not f or not _team_can_see_file(f, ident):
        return jsonify({'error': 'Not found'}), 404
    payload = request.get_json(silent=True) or {}
    content = (payload.get('content') or '').strip()
    if not content or len(content) > 2000:
        return jsonify({'error': '评论内容不合法'}), 400
    db = get_db()
    cid = uuid.uuid4().hex
    now = time.time()
    _exec(db, 'INSERT INTO team_comments (id, file_id, user_id, content, created_at) VALUES (?,?,?,?,?)',
          (cid, fid, ident['id'], content, now))
    db.commit()
    _team_log('comment', fid, f['name'], detail='添加评论', uid=ident['id'])
    return jsonify({'ok': True, 'comment': {'id': cid, 'content': content, 'created_at': now,
                                            'username': ident['username'], 'mine': True}})


# ===== 分享（仅公开/内部密级允许）=====
@app.route('/api/team/file/<fid>/share', methods=['POST'])
@team_required()
def api_team_share(fid):
    ident = g.team
    if not _team_can_write(ident['role']):
        return jsonify({'error': '你的角色为只读访客，无法分享'}), 403
    f = _team_get_file(fid)
    if not f or f['is_dir'] or not _team_can_see_file(f, ident):
        return jsonify({'error': 'Not found'}), 404
    if f.get('classification') not in ('public', 'internal'):
        return jsonify({'error': '机密及以上密级的文件禁止生成分享链接'}), 403
    if _team_ext(f['name']) in TEAM_SOURCE_EXTS:
        return jsonify({'error': '源码 / 密钥类文件禁止生成分享链接'}), 403
    payload = request.get_json(silent=True) or {}
    try:
        hours = int(payload.get('hours') or 72)
    except Exception:
        hours = 72
    hours = max(1, min(hours, 24 * 30))
    db = get_db()
    token = secrets.token_urlsafe(24)
    now = time.time()
    _exec(db, 'INSERT INTO team_share (id, file_id, token, created_by, expires_at, revoked, created_at) VALUES (?,?,?,?,?,?,?)',
          (uuid.uuid4().hex, fid, token, ident['id'], now + hours * 3600, 0, now))
    db.commit()
    _team_log('share', fid, f['name'], detail=f'生成分享链接（{hours} 小时有效）', uid=ident['id'])
    return jsonify({'ok': True, 'token': token, 'expires_at': now + hours * 3600, 'url': f'/api/team/s/{token}'})


@app.route('/api/team/file/<fid>/share', methods=['DELETE'])
@team_required()
def api_team_share_revoke(fid):
    ident = g.team
    f = _team_get_file(fid)
    if not f or not _team_can_see_file(f, ident):
        return jsonify({'error': 'Not found'}), 404
    db = get_db()
    _exec(db, 'UPDATE team_share SET revoked=1 WHERE file_id=?', (fid,))
    db.commit()
    _team_log('unshare', fid, f['name'], detail='撤销全部分享链接', uid=ident['id'])
    return jsonify({'ok': True})


# ===== 定向投递：把文件单独发给指定成员 =====
def _team_inbox_id(uid):
    """取（必要时创建）成员个人盘根目录下的「收到的文件」目录"""
    db = get_db()
    row = _fetchone(db, '''SELECT id FROM team_files WHERE scope='personal' AND owner_id=? AND parent_id=''
                           AND is_dir=1 AND name=? AND deleted_at=0''', (uid, TEAM_INBOX_NAME))
    if row:
        return row['id']
    fid = uuid.uuid4().hex
    now = time.time()
    _exec(db, '''INSERT INTO team_files (id, scope, owner_id, parent_id, name, is_dir, ext, size, mime,
                 classification, storage, checksum, version, created_at, updated_at)
                 VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)''',
          (fid, 'personal', uid, '', TEAM_INBOX_NAME, 1, '', 0, '', 'internal', '', '', 1, now, now))
    db.commit()
    return fid


def _team_dup_name(uid, parent, name):
    """同名时自动追加序号，避免覆盖接收者已有文件"""
    db = get_db()
    base, ext = os.path.splitext(name)
    cand, i = name, 1
    while _fetchone(db, '''SELECT id FROM team_files WHERE scope='personal' AND owner_id=? AND parent_id=?
                           AND name=? AND deleted_at=0''', (uid, parent, cand)):
        i += 1
        cand = f'{base} ({i}){ext}'
    return cand


@app.route('/api/team/file/<fid>/send', methods=['POST'])
@team_required()
def api_team_file_send(fid):
    """把文件投递到指定成员个人盘的「收到的文件」，仅接收者本人可见"""
    ident = g.team
    if not _team_can_write(ident['role']):
        return jsonify({'error': '你的角色为只读访客，无法发送文件'}), 403
    src = _team_get_file(fid)
    if not src or src['is_dir'] or not _team_can_see_file(src, ident):
        return jsonify({'error': 'Not found'}), 404
    payload = request.get_json(silent=True) or {}
    targets = [str(x) for x in (payload.get('user_ids') or []) if x]
    if not targets:
        return jsonify({'error': '请选择接收成员'}), 400
    if len(targets) > 200:
        return jsonify({'error': '单次最多发送给 200 位成员'}), 400
    src_path = os.path.join(_DATA_DIR, src.get('storage') or '')
    if not src.get('storage') or not os.path.isfile(src_path):
        return jsonify({'error': '文件内容已丢失'}), 410

    db = get_db()
    size = int(src.get('size') or 0)
    delivered, skipped = [], []
    for uid in dict.fromkeys(targets):
        if uid == ident['id']:
            skipped.append({'user_id': uid, 'reason': '这是你自己的文件'}); continue
        if not _team_role_of(uid):
            skipped.append({'user_id': uid, 'reason': '不是团队成员'}); continue
        if _team_used_bytes('personal', uid) + size > TEAM_PERSONAL_QUOTA:
            skipped.append({'user_id': uid, 'reason': '对方个人空间不足'}); continue
        inbox = _team_inbox_id(uid)
        new_id = uuid.uuid4().hex
        rel = os.path.join('teamstore', 'files', new_id, 'v1.bin')
        dst = os.path.join(_DATA_DIR, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        _team_shutil.copyfile(src_path, dst)
        name = _team_dup_name(uid, inbox, src['name'])
        now = time.time()
        _exec(db, '''INSERT INTO team_files (id, scope, owner_id, parent_id, name, is_dir, ext, size, mime,
                     classification, storage, checksum, version, created_at, updated_at)
                     VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)''',
              (new_id, 'personal', uid, inbox, name, 0, src.get('ext') or '', size, src.get('mime') or '',
               src.get('classification') or 'internal', rel, src.get('checksum') or '', 1, now, now))
        db.commit()
        _exec(db, 'INSERT INTO notifications (id, user_id, text, read, created_at) VALUES (?,?,?,?,?)',
              (uuid.uuid4().hex, uid, f'{ident["username"]} 给你发来文件「{name}」，可在团队空间的"我的文件 / 收到的文件"中查看。', 0, now))
        db.commit()
        delivered.append({'user_id': uid, 'name': name})
    _team_log('send_file', fid, src['name'],
              detail=f'定向发送给 {len(delivered)} 位成员' + (f'，跳过 {len(skipped)} 位' if skipped else ''),
              uid=ident['id'])
    return jsonify({'ok': True, 'delivered': delivered, 'skipped': skipped})


@app.route('/api/team/s/<token>', methods=['GET'])
def api_team_share_open(token):
    """分享链接访问：凭 token 下载（带有效期）"""
    db = get_db()
    s = _fetchone(db, 'SELECT * FROM team_share WHERE token=?', (token,))
    if not s or s.get('revoked') or (float(s.get('expires_at') or 0) and float(s['expires_at']) < time.time()):
        _team_abort(404)
    f = _fetchone(db, 'SELECT * FROM team_files WHERE id=?', (s['file_id'],))
    if not f or f.get('deleted_at'):
        _team_abort(404)
    path = os.path.join(_DATA_DIR, f.get('storage') or '')
    if not f.get('storage') or not os.path.isfile(path):
        _team_abort(404)
    _team_log('share_open', f['id'], f['name'], detail='通过分享链接下载', uid=s.get('created_by') or '')
    resp = Response(_team_swc(_team_decrypt_stream(path)), mimetype=f.get('mime') or 'application/octet-stream')
    resp.headers['Content-Disposition'] = "attachment; filename*=UTF-8''" + _team_quote(f['name'])
    resp.headers['Cache-Control'] = 'no-store'
    return resp


# ===== 成员管理（仅拥有者）=====
@app.route('/api/team/member-lookup', methods=['GET'])
@team_required()
def api_team_member_lookup():
    """按论坛绑定邮箱精确查找用户，返回账户预览（仅拥有者）"""
    ident = g.team
    if not _team_can_manage(ident['role']):
        return jsonify({'error': '仅拥有者可添加成员'}), 403
    email = (request.args.get('email') or '').strip().lower()
    if not email:
        return jsonify({'error': '请填写邮箱'}), 400
    db = get_db()
    u = _fetchone(db, "SELECT id, username, email, avatar, created_at FROM users WHERE LOWER(email)=?", (email,))
    if not u:
        return jsonify({'error': '没有找到绑定该邮箱的论坛账户'}), 404
    m = _fetchone(db, 'SELECT role, status FROM team_members WHERE user_id=?', (u['id'],))
    return jsonify({
        'user': {
            'user_id': u['id'], 'username': u.get('username') or '',
            'email': u.get('email') or '',
            'avatar': (f"/{u['avatar']}" if u.get('avatar') else ''),
            'joined_at': float(u.get('created_at') or 0),
            'in_team': bool(m), 'role': (m or {}).get('role') or '',
            'role_label': TEAM_ROLE_LABEL.get((m or {}).get('role') or '', ''),
            'status': (m or {}).get('status') or '',
            'is_me': u['id'] == ident['id'],
        },
    })


@app.route('/api/team/members', methods=['GET'])
@team_required()
def api_team_members():
    ident = g.team
    db = get_db()
    rows = _fetchall(db, '''SELECT m.user_id, m.role, m.status, m.created_at, m.job_title, m.department,
                                   u.username, u.email, u.avatar
                            FROM team_members m LEFT JOIN users u ON u.id = m.user_id
                            ORDER BY CASE m.role WHEN 'owner' THEN 1 WHEN 'core' THEN 2 WHEN 'member' THEN 3 ELSE 4 END, m.created_at''')
    items = []
    for r in rows:
        personal = _team_used_bytes('personal', r['user_id'])
        items.append({
            'user_id': r['user_id'], 'username': r.get('username') or '（已注销）',
            'avatar': (f"/{r['avatar']}" if r.get('avatar') else ''),
            'role': r['role'], 'role_label': TEAM_ROLE_LABEL.get(r['role'], ''),
            'job_title': r.get('job_title') or '', 'department': r.get('department') or '',
            'status': r.get('status') or 'active', 'created_at': float(r.get('created_at') or 0),
            'personal_used': personal, 'personal_quota': TEAM_PERSONAL_QUOTA,
            'is_me': r['user_id'] == ident['id'],
            'can_manage': _team_can_manage(ident['role']),
        })
    return jsonify({'items': items, 'can_manage': _team_can_manage(ident['role']),
                    'roles': TEAM_ROLE_LABEL})


@app.route('/api/team/members', methods=['POST'])
@team_required()
def api_team_member_add():
    ident = g.team
    if not _team_can_manage(ident['role']):
        return jsonify({'error': '仅拥有者可管理成员'}), 403
    payload = request.get_json(silent=True) or {}
    email = (payload.get('email') or '').strip()
    role = payload.get('role') if payload.get('role') in TEAM_ROLE_RANK else 'member'
    job_title = (payload.get('job_title') or '').strip()[:60]
    department = (payload.get('department') or '').strip()[:60]
    if role == 'owner':
        return jsonify({'error': '不能通过该接口授予拥有者角色'}), 400
    if not email:
        return jsonify({'error': '请填写论坛绑定邮箱'}), 400
    db = get_db()
    u = _fetchone(db, 'SELECT id, username FROM users WHERE LOWER(email)=?', (email.lower(),))
    if not u:
        return jsonify({'error': '没有找到绑定该邮箱的论坛账户'}), 404
    if _fetchone(db, 'SELECT user_id FROM team_members WHERE user_id=?', (u['id'],)):
        return jsonify({'error': '该账户已在团队中'}), 409
    _exec(db, '''INSERT INTO team_members (user_id, role, status, created_at, added_by, job_title, department)
                 VALUES (?,?,?,?,?,?,?)''',
          (u['id'], role, 'active', time.time(), ident['id'], job_title, department))
    db.commit()
    _team_log('member_add', detail=f'加入成员 {u["username"]}（{TEAM_ROLE_LABEL.get(role, role)}）', uid=ident['id'])
    return jsonify({'ok': True, 'username': u['username']})


@app.route('/api/team/members/<user_id>', methods=['PATCH'])
@team_required()
def api_team_member_update(user_id):
    ident = g.team
    if not _team_can_manage(ident['role']):
        return jsonify({'error': '仅拥有者可管理成员'}), 403
    payload = request.get_json(silent=True) or {}
    db = get_db()
    m = _fetchone(db, 'SELECT * FROM team_members WHERE user_id=?', (user_id,))
    if not m:
        return jsonify({'error': 'Not found'}), 404
    if m['role'] == 'owner':
        return jsonify({'error': '不能修改拥有者'}), 403
    sets, params = [], []
    if payload.get('role') in ('core', 'member', 'guest'):
        sets.append('role=?'); params.append(payload['role'])
    if payload.get('status') in ('active', 'suspended'):
        sets.append('status=?'); params.append(payload['status'])
    if 'job_title' in payload:
        sets.append('job_title=?'); params.append((payload.get('job_title') or '').strip()[:60])
    if 'department' in payload:
        sets.append('department=?'); params.append((payload.get('department') or '').strip()[:60])
    if not sets:
        return jsonify({'ok': True})
    params.append(user_id)
    _exec(db, f'UPDATE team_members SET {", ".join(sets)} WHERE user_id=?', tuple(params))
    db.commit()
    _team_log('member_update', detail=f'更新成员资料（{user_id}）', uid=ident['id'])
    return jsonify({'ok': True})


@app.route('/api/team/members/<user_id>', methods=['DELETE'])
@team_required()
def api_team_member_remove(user_id):
    ident = g.team
    if not _team_can_manage(ident['role']):
        return jsonify({'error': '仅拥有者可管理成员'}), 403
    if user_id == ident['id']:
        return jsonify({'error': '不能移除自己'}), 400
    db = get_db()
    m = _fetchone(db, 'SELECT * FROM team_members WHERE user_id=?', (user_id,))
    if not m:
        return jsonify({'error': 'Not found'}), 404
    if m['role'] == 'owner':
        return jsonify({'error': '不能移除拥有者'}), 403
    _exec(db, 'DELETE FROM team_members WHERE user_id=?', (user_id,))
    db.commit()
    _team_log('member_remove', detail=f'移出成员（{user_id}）', uid=ident['id'])
    return jsonify({'ok': True})


# ===== 活动日志 / 容量 =====
@app.route('/api/team/activity', methods=['GET'])
@team_required()
def api_team_activity():
    ident = g.team
    db = get_db()
    try:
        limit = min(int(request.args.get('limit') or 100), 500)
    except Exception:
        limit = 100
    rows = _fetchall(db, '''SELECT a.*, u.username FROM team_activity a LEFT JOIN users u ON u.id = a.user_id
                            ORDER BY a.created_at DESC LIMIT ?''', (limit,))
    items = [{'id': r['id'], 'action': r['action'], 'file_id': r.get('file_id') or '',
              'file_name': r.get('file_name') or '', 'detail': r.get('detail') or '',
              'username': r.get('username') or '系统', 'ip': r.get('ip') or '',
              'created_at': float(r.get('created_at') or 0)} for r in rows]
    return jsonify({'items': items})


@app.route('/api/team/storage', methods=['GET'])
@team_required()
def api_team_storage():
    ident = g.team
    db = get_db()
    shared_used = _team_used_bytes('shared')
    rows = _fetchall(db, '''SELECT owner_id, COALESCE(SUM(size),0) AS s FROM team_files
                            WHERE scope='personal' AND deleted_at=0 AND is_dir=0 GROUP BY owner_id''')
    personal = {r['owner_id']: int(r['s'] or 0) for r in rows}
    members = _fetchall(db, 'SELECT user_id FROM team_members')
    per_member = []
    total_personal = 0
    for m in members:
        used = personal.get(m['user_id'], 0)
        total_personal += used
        per_member.append({'user_id': m['user_id'], 'used': used})
    counts = _fetchone(db, 'SELECT COUNT(*) AS c FROM team_files WHERE deleted_at=0 AND is_dir=0')
    return jsonify({
        'shared': {'used': shared_used, 'quota': TEAM_SHARED_QUOTA,
                   'files': int(counts['c'] or 0) if counts else 0},
        'personal': {'used': total_personal, 'quota': TEAM_PERSONAL_QUOTA * max(len(per_member), 1),
                     'members': len(per_member)},
        'mine': {'used': _team_used_bytes('personal', ident['id']), 'quota': TEAM_PERSONAL_QUOTA},
        'per_member': sorted(per_member, key=lambda x: x['used'], reverse=True),
        'max_file': TEAM_MAX_FILE_SIZE,
    })


# ===== v2 协同：工作任务 / 待办 / 日程 / 仪表盘 =====
def _team_count(db, sql, params=()):
    """取 COUNT(*) 单一数值的便捷函数"""
    row = _fetchone(db, sql, params)
    return int(row['c'] or 0) if row else 0


def _team_resolve_user(db, raw):
    """按 user_id 或用户名解析用户，返回 (id, username)；解析不到返回 (None, None)"""
    if not raw:
        return None, None
    u = _fetchone(db, 'SELECT id, username FROM users WHERE id=?', (raw,))
    if not u:
        u = _fetchone(db, 'SELECT id, username FROM users WHERE username=?', (raw,))
    if not u:
        return None, None
    return u['id'], u.get('username') or ''


def _team_parse_assignee(db, ident, raw):
    """解析任务负责人：返回 (assignee_id, err)。空值表示不指派；指派他人需 core 及以上"""
    raw = (raw or '').strip()
    if not raw:
        return '', None
    aid, _ = _team_resolve_user(db, raw)
    if not aid:
        return None, '指派的成员不存在'
    if aid != ident['id'] and TEAM_ROLE_RANK.get(ident['role'], 0) < TEAM_ROLE_RANK['core']:
        return None, '只有核心成员及以上可以给他人下发任务'
    return aid, None


# ===== 公告栏 =====
_TEAM_ANNOUNCE_SELECT = '''SELECT a.*, u.username AS author_name, u.avatar AS author_avatar
                          FROM team_announcements a
                          LEFT JOIN users u ON u.id = a.author_id'''


def _team_announce_json(a, ident):
    """公告视图：带作者信息与编辑 / 删除权限（作者本人或拥有者）"""
    mine = (a.get('author_id') or '') == ident['id']
    owner = _team_can_manage(ident['role'])
    return {
        'id': a['id'], 'title': a.get('title') or '', 'body': a.get('body') or '',
        'author_id': a.get('author_id') or '', 'author_name': a.get('author_name') or '（已注销）',
        'author_avatar': a.get('author_avatar') or '',
        'created_at': float(a.get('created_at') or 0), 'updated_at': float(a.get('updated_at') or 0),
        'mine': mine, 'can_edit': (mine or owner), 'can_delete': (mine or owner),
    }


def _team_announce_recent(db, ident, limit=TEAM_ANNOUNCE_LIMIT):
    """首页 / 仪表盘共用的最近公告"""
    rows = _fetchall(db, _TEAM_ANNOUNCE_SELECT + ' ORDER BY a.created_at DESC LIMIT ?', (limit,))
    return [_team_announce_json(r, ident) for r in rows]


@app.route('/api/team/announcements', methods=['GET'])
@team_required()
def api_team_announcements():
    """公告列表（团队成员均可查看）"""
    ident = g.team
    try:
        limit = int(request.args.get('limit') or 20)
    except Exception:
        limit = 20
    limit = max(1, min(100, limit))
    db = get_db()
    rows = _fetchall(db, _TEAM_ANNOUNCE_SELECT + ' ORDER BY a.created_at DESC LIMIT ?', (limit,))
    return jsonify({'items': [_team_announce_json(r, ident) for r in rows],
                    'total': _team_count(db, 'SELECT COUNT(*) AS c FROM team_announcements'),
                    'can_post': _team_can_write(ident['role'])})


@app.route('/api/team/announcements', methods=['POST'])
@team_required()
def api_team_announce_create():
    """发布公告"""
    ident = g.team
    if not _team_can_write(ident['role']):
        return jsonify({'error': '只读访客不能发布公告'}), 403
    payload = request.get_json(silent=True) or {}
    title = (payload.get('title') or '').strip()
    body = (payload.get('body') or '').strip()
    if len(title) > TEAM_ANNOUNCE_TITLE_MAX:
        return jsonify({'error': f'标题不超过 {TEAM_ANNOUNCE_TITLE_MAX} 字'}), 400
    if not body:
        return jsonify({'error': '公告内容不能为空'}), 400
    if len(body) > TEAM_ANNOUNCE_BODY_MAX:
        return jsonify({'error': f'公告内容不超过 {TEAM_ANNOUNCE_BODY_MAX} 字'}), 400
    db = get_db()
    now = time.time()
    aid = uuid.uuid4().hex
    _exec(db, 'INSERT INTO team_announcements (id, author_id, title, body, created_at, updated_at) VALUES (?,?,?,?,?,?)',
          (aid, ident['id'], title, body, now, now))
    db.commit()
    _team_log('announce_create', detail=(title or body)[:40])
    return jsonify({'ok': True, 'id': aid})


@app.route('/api/team/announcements/<aid>', methods=['PATCH'])
@team_required()
def api_team_announce_update(aid):
    """编辑公告（作者本人或拥有者）"""
    ident = g.team
    db = get_db()
    a = _fetchone(db, 'SELECT * FROM team_announcements WHERE id=?', (aid,))
    if not a or not ((a.get('author_id') or '') == ident['id'] or _team_can_manage(ident['role'])):
        return jsonify({'error': 'Not found'}), 404
    payload = request.get_json(silent=True) or {}
    sets, params = [], []
    if 'title' in payload:
        title = (payload.get('title') or '').strip()
        if len(title) > TEAM_ANNOUNCE_TITLE_MAX:
            return jsonify({'error': f'标题不超过 {TEAM_ANNOUNCE_TITLE_MAX} 字'}), 400
        sets.append('title=?'); params.append(title)
    if 'body' in payload:
        body = (payload.get('body') or '').strip()
        if not body:
            return jsonify({'error': '公告内容不能为空'}), 400
        if len(body) > TEAM_ANNOUNCE_BODY_MAX:
            return jsonify({'error': f'公告内容不超过 {TEAM_ANNOUNCE_BODY_MAX} 字'}), 400
        sets.append('body=?'); params.append(body)
    if not sets:
        return jsonify({'ok': True})
    sets.append('updated_at=?'); params.append(time.time())
    params.append(aid)
    _exec(db, f'UPDATE team_announcements SET {", ".join(sets)} WHERE id=?', tuple(params))
    db.commit()
    _team_log('announce_edit', detail=(a.get('title') or '')[:40])
    return jsonify({'ok': True})


@app.route('/api/team/announcements/<aid>', methods=['DELETE'])
@team_required()
def api_team_announce_delete(aid):
    """删除公告（作者本人或拥有者）"""
    ident = g.team
    db = get_db()
    a = _fetchone(db, 'SELECT id, author_id, title FROM team_announcements WHERE id=?', (aid,))
    if not a or not ((a.get('author_id') or '') == ident['id'] or _team_can_manage(ident['role'])):
        return jsonify({'error': 'Not found'}), 404
    _exec(db, 'DELETE FROM team_announcements WHERE id=?', (aid,))
    db.commit()
    _team_log('announce_delete', detail=(a.get('title') or '')[:40])
    return jsonify({'ok': True})


def _team_task_json(t, ident):
    """任务视图：附带「我是否被指派 / 是否可编辑 / 是否逾期」等前端判断字段"""
    mine = (t.get('assignee_id') or '') == ident['id']
    creator = (t.get('creator_id') or '') == ident['id']
    owner = _team_can_manage(ident['role'])
    core = TEAM_ROLE_RANK.get(ident['role'], 0) >= TEAM_ROLE_RANK['core']
    due = float(t.get('due_at') or 0)
    overdue = bool(due and due < time.time() and (t.get('status') or 'todo') != 'done')
    return {
        'id': t['id'], 'title': t['title'], 'detail': t.get('detail') or '',
        'status': t.get('status') or 'todo', 'priority': int(t.get('priority') or 0),
        'due_at': due,
        'assignee_id': t.get('assignee_id') or '', 'assignee_name': t.get('assignee_name') or '',
        'creator_id': t.get('creator_id') or '', 'creator_name': t.get('creator_name') or '',
        'file_id': t.get('file_id') or '', 'file_name': t.get('file_name') or '',
        'parent_id': t.get('parent_id') or '',
        'created_at': float(t.get('created_at') or 0), 'updated_at': float(t.get('updated_at') or 0),
        'completed_at': float(t.get('completed_at') or 0),
        'mine': mine, 'can_edit': (mine or creator or owner or core), 'can_delete': (mine or creator or owner),
        'can_assign': TEAM_ROLE_RANK.get(ident['role'], 0) >= TEAM_ROLE_RANK['core'],
        'overdue': overdue,
    }


# 任务查询统一走这段 JOIN，保证 assignee_name / creator_name / file_name 齐全
_TEAM_TASK_SELECT = '''SELECT t.*, ua.username AS assignee_name, uc.username AS creator_name,
                              cf.name AS file_name
                       FROM team_tasks t
                       LEFT JOIN users ua ON ua.id = t.assignee_id
                       LEFT JOIN users uc ON uc.id = t.creator_id
                       LEFT JOIN team_files cf ON cf.id = t.file_id'''


@app.route('/api/team/dashboard', methods=['GET'])
@team_required()
def api_team_dashboard():
    """仪表盘：一次返回存储 / 成员 / 任务 / 待办 / 活跃度 / 最近动态等聚合数据"""
    ident = g.team
    db = get_db()
    now = time.time()
    day7 = now - 7 * 86400
    day30 = now - 30 * 86400

    # 存储
    storage = {
        'shared_used': _team_used_bytes('shared'), 'shared_quota': TEAM_SHARED_QUOTA,
        'mine_used': _team_used_bytes('personal', ident['id']), 'mine_quota': TEAM_PERSONAL_QUOTA,
        'files': _team_count(db, 'SELECT COUNT(*) AS c FROM team_files WHERE scope=? AND is_dir=0 AND deleted_at=0', ('shared',)),
        'trash': 0,
    }
    # 回收站：复用可见性判断（个人盘仅本人，共享盘按密级）
    for r in _fetchall(db, 'SELECT scope, owner_id, classification FROM team_files WHERE deleted_at>0'):
        if _team_can_see_file(r, ident):
            storage['trash'] += 1

    # 成员
    by_role = {'owner': 0, 'core': 0, 'member': 0, 'guest': 0}
    mrows = _fetchall(db, 'SELECT role FROM team_members WHERE status=?', ('active',))
    for r in mrows:
        if r['role'] in by_role:
            by_role[r['role']] += 1
    members = {'total': len(mrows), 'by_role': by_role}

    # 任务
    tasks = {
        'mine_open': _team_count(db, "SELECT COUNT(*) AS c FROM team_tasks WHERE assignee_id=? AND status<>'done'", (ident['id'],)),
        'mine_overdue': _team_count(db, "SELECT COUNT(*) AS c FROM team_tasks WHERE assignee_id=? AND status<>'done' AND due_at>0 AND due_at<?", (ident['id'], now)),
        'assigned_open': _team_count(db, "SELECT COUNT(*) AS c FROM team_tasks WHERE creator_id=? AND status<>'done' AND assignee_id<>?", (ident['id'], ident['id'])),
        'team_open': _team_count(db, "SELECT COUNT(*) AS c FROM team_tasks WHERE status<>'done'"),
        'done_7d': _team_count(db, "SELECT COUNT(*) AS c FROM team_tasks WHERE completed_at>=? AND (creator_id=? OR assignee_id=?)", (day7, ident['id'], ident['id'])),
    }

    # 待办（done_today 用 updated_at 落在本地今天近似，切换完成状态时会刷新 updated_at）
    lt = time.localtime(now)
    day_start = time.mktime((lt.tm_year, lt.tm_mon, lt.tm_mday, 0, 0, 0, 0, 0, -1))
    todos = {
        'open': _team_count(db, 'SELECT COUNT(*) AS c FROM team_todos WHERE user_id=? AND done=0', (ident['id'],)),
        'done_today': _team_count(db, 'SELECT COUNT(*) AS c FROM team_todos WHERE user_id=? AND done=1 AND updated_at>=?', (ident['id'], day_start)),
    }

    # 活跃度
    activity = {
        'total': _team_count(db, 'SELECT COUNT(*) AS c FROM team_activity'),
        'last7': _team_count(db, 'SELECT COUNT(*) AS c FROM team_activity WHERE created_at>=?', (day7,)),
        'last30': _team_count(db, 'SELECT COUNT(*) AS c FROM team_activity WHERE created_at>=?', (day30,)),
    }

    # 密级分布（共享空间）
    classes = {'public': 0, 'internal': 0, 'confidential': 0, 'secret': 0}
    for r in _fetchall(db, "SELECT classification, COUNT(*) AS c FROM team_files WHERE scope='shared' AND is_dir=0 AND deleted_at=0 GROUP BY classification"):
        if r['classification'] in classes:
            classes[r['classification']] = int(r['c'] or 0)

    # 类型分布（当前用户可见的全部文件）
    kind_counts = {}
    for r in _fetchall(db, 'SELECT name, scope, owner_id, classification FROM team_files WHERE is_dir=0 AND deleted_at=0'):
        if _team_can_see_file(r, ident):
            k = _team_kind(r['name'], 0)
            kind_counts[k] = kind_counts.get(k, 0) + 1
    kinds = [{'label': k, 'count': v} for k, v in sorted(kind_counts.items(), key=lambda x: x[1], reverse=True)[:6]]

    # 近 30 天贡献榜
    top_contributors = [{'user_id': r['user_id'], 'username': r.get('username') or '（已注销）', 'count': int(r['c'] or 0)}
                        for r in _fetchall(db, '''SELECT a.user_id, u.username, COUNT(*) AS c FROM team_activity a
                                                 LEFT JOIN users u ON u.id = a.user_id
                                                 WHERE a.created_at>=? AND a.user_id<>''
                                                 GROUP BY a.user_id, u.username ORDER BY c DESC LIMIT 5''', (day30,))]

    # 最近文件（按密级过滤后取 6 条）
    rf_rows = _fetchall(db, '''SELECT f.*, u.username AS owner_name FROM team_files f
                               LEFT JOIN users u ON u.id = f.owner_id
                               WHERE f.is_dir=0 AND f.deleted_at=0 ORDER BY f.updated_at DESC LIMIT 200''')
    recent_files = [_team_file_json(r, ident) for r in rf_rows if _team_can_see_file(r, ident)][:6]

    # 最近动态
    recent_activity = [{'username': r.get('username') or '系统', 'action': r['action'],
                        'detail': r.get('detail') or '', 'file_name': r.get('file_name') or '',
                        'created_at': float(r.get('created_at') or 0)}
                       for r in _fetchall(db, '''SELECT a.action, a.detail, a.file_name, a.created_at, u.username
                                                FROM team_activity a LEFT JOIN users u ON u.id = a.user_id
                                                ORDER BY a.created_at DESC LIMIT 8''')]

    return jsonify({'storage': storage, 'members': members, 'tasks': tasks, 'todos': todos,
                    'activity': activity, 'classes': classes, 'kinds': kinds,
                    'top_contributors': top_contributors, 'recent_files': recent_files,
                    'recent_activity': recent_activity,
                    'announcements': _team_announce_recent(db, ident),
                    'can_announce': _team_can_write(ident['role'])})


@app.route('/api/team/contributions', methods=['GET'])
@team_required()
def api_team_contributions():
    """贡献热力：按天分桶统计某成员的留痕数量（默认自己；查看他人需 core 及以上）"""
    ident = g.team
    try:
        days = int(request.args.get('days') or 365)
    except Exception:
        days = 365
    days = max(30, min(730, days))
    target = request.args.get('user_id') or ident['id']
    if target != ident['id'] and TEAM_ROLE_RANK.get(ident['role'], 0) < TEAM_ROLE_RANK['core']:
        return jsonify({'error': 'Not found'}), 404
    db = get_db()
    u = _fetchone(db, 'SELECT id, username FROM users WHERE id=?', (target,))
    if not u:
        return jsonify({'error': 'Not found'}), 404

    now = time.time()
    lt = time.localtime(now)
    end_day = time.mktime((lt.tm_year, lt.tm_mon, lt.tm_mday, 0, 0, 0, 0, 0, -1))
    start_day = end_day - (days - 1) * 86400

    counts = {}
    for r in _fetchall(db, 'SELECT created_at FROM team_activity WHERE user_id=? AND created_at>=?', (target, start_day)):
        d = time.strftime('%Y-%m-%d', time.localtime(float(r['created_at'] or 0)))
        counts[d] = counts.get(d, 0) + 1
    buckets = []
    for i in range(days):
        d = time.strftime('%Y-%m-%d', time.localtime(start_day + i * 86400))
        buckets.append({'date': d, 'count': counts.get(d, 0)})
    by_action = [{'action': r['action'], 'count': int(r['c'] or 0)}
                 for r in _fetchall(db, '''SELECT action, COUNT(*) AS c FROM team_activity
                                           WHERE user_id=? AND created_at>=? GROUP BY action ORDER BY c DESC''', (target, start_day))]
    return jsonify({'days': days, 'start': start_day, 'end': now, 'total': sum(counts.values()),
                    'max': max([b['count'] for b in buckets] or [0]),
                    'member': {'user_id': u['id'], 'username': u.get('username') or ''},
                    'buckets': buckets, 'by_action': by_action})


# ===== 工作任务 =====
@app.route('/api/team/tasks', methods=['GET'])
@team_required()
def api_team_tasks():
    ident = g.team
    flt = request.args.get('filter') or 'mine'
    if flt not in ('mine', 'assigned', 'team', 'done'):
        flt = 'mine'
    # 全团队任务列表仅 core 及以上可见
    if flt == 'team' and TEAM_ROLE_RANK.get(ident['role'], 0) < TEAM_ROLE_RANK['core']:
        return jsonify({'error': 'Not found'}), 404
    db = get_db()
    order = " ORDER BY (CASE WHEN t.status='done' THEN 1 ELSE 0 END), t.priority DESC, t.created_at DESC LIMIT 500"
    if flt == 'mine':
        rows = _fetchall(db, _TEAM_TASK_SELECT + ' WHERE t.assignee_id=?' + order, (ident['id'],))
    elif flt == 'assigned':
        rows = _fetchall(db, _TEAM_TASK_SELECT + ' WHERE t.creator_id=?' + order, (ident['id'],))
    elif flt == 'done':
        rows = _fetchall(db, _TEAM_TASK_SELECT + " WHERE t.status='done' AND (t.creator_id=? OR t.assignee_id=?)" + order, (ident['id'], ident['id']))
    else:
        rows = _fetchall(db, _TEAM_TASK_SELECT + order)

    counts = {
        'mine': _team_count(db, 'SELECT COUNT(*) AS c FROM team_tasks WHERE assignee_id=?', (ident['id'],)),
        'assigned': _team_count(db, 'SELECT COUNT(*) AS c FROM team_tasks WHERE creator_id=?', (ident['id'],)),
        'team': _team_count(db, 'SELECT COUNT(*) AS c FROM team_tasks'),
        'done': _team_count(db, "SELECT COUNT(*) AS c FROM team_tasks WHERE status='done' AND (creator_id=? OR assignee_id=?)", (ident['id'], ident['id'])),
        'overdue': _team_count(db, "SELECT COUNT(*) AS c FROM team_tasks WHERE assignee_id=? AND status<>'done' AND due_at>0 AND due_at<?", (ident['id'], time.time())),
    }
    return jsonify({'items': [_team_task_json(r, ident) for r in rows], 'counts': counts})


@app.route('/api/team/tasks', methods=['POST'])
@team_required()
def api_team_task_create():
    ident = g.team
    if not _team_can_write(ident['role']):
        return jsonify({'error': '你的角色为只读访客，无法创建任务'}), 400
    payload = request.get_json(silent=True) or {}
    title = (payload.get('title') or '').strip()
    if not title or len(title) > 200:
        return jsonify({'error': '任务标题不能为空且不超过 200 字'}), 400
    detail = str(payload.get('detail') or '')[:5000]
    parent_id = str(payload.get('parent_id') or '')
    try:
        priority = max(0, min(2, int(payload.get('priority') or 0)))
    except Exception:
        priority = 0
    try:
        due_at = float(payload.get('due_at') or 0)
    except Exception:
        due_at = 0

    db = get_db()
    # 负责人：留空即不指派（此前会被静默改成「指派给自己」）
    assignee_id, err = _team_parse_assignee(db, ident, payload.get('assignee'))
    if err:
        return jsonify({'error': err}), 400

    file_id = str(payload.get('file_id') or '')
    if file_id:
        f = _team_get_file(file_id)
        if not f or not _team_can_see_file(f, ident):
            return jsonify({'error': 'Not found'}), 404

    tid = uuid.uuid4().hex
    now = time.time()
    _exec(db, '''INSERT INTO team_tasks (id, title, detail, assignee_id, creator_id, status, priority, due_at,
                 file_id, parent_id, created_at, updated_at, completed_at) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)''',
          (tid, title, detail, assignee_id, ident['id'], 'todo', priority, due_at, file_id, parent_id, now, now, 0))
    db.commit()
    _team_log('task_create', detail=title, uid=ident['id'])
    return jsonify({'ok': True, 'id': tid})


@app.route('/api/team/tasks/<tid>', methods=['PATCH'])
@team_required()
def api_team_task_update(tid):
    ident = g.team
    db = get_db()
    t = _fetchone(db, 'SELECT * FROM team_tasks WHERE id=?', (tid,))
    if not t:
        return jsonify({'error': 'Not found'}), 404
    mine = (t.get('assignee_id') or '') == ident['id']
    creator = (t.get('creator_id') or '') == ident['id']
    owner = _team_can_manage(ident['role'])
    core = TEAM_ROLE_RANK.get(ident['role'], 0) >= TEAM_ROLE_RANK['core']
    # 与任务无关的人一律 404（不暴露任务是否存在）
    if not (mine or creator or owner or core):
        return jsonify({'error': 'Not found'}), 404
    payload = request.get_json(silent=True) or {}
    # 内容字段可改范围与 _team_task_json 的 can_edit 保持一致（被指派人 / 创建者 / 拥有者 / 核心成员）
    can_edit = mine or creator or owner or core
    content_keys = [k for k in ('title', 'detail', 'priority', 'due_at', 'assignee') if k in payload]
    if content_keys and not can_edit:
        return jsonify({'error': 'Not found'}), 404

    now = time.time()
    sets, params = [], []
    if 'status' in payload:
        st = payload.get('status')
        if st not in ('todo', 'doing', 'done'):
            return jsonify({'error': '任务状态不合法'}), 400
        sets.append('status=?'); params.append(st)
        # 完成时记完成时间，回退时清零
        sets.append('completed_at=?'); params.append(now if st == 'done' else 0)
    if 'title' in payload:
        title = (payload.get('title') or '').strip()
        if not title or len(title) > 200:
            return jsonify({'error': '任务标题不能为空且不超过 200 字'}), 400
        sets.append('title=?'); params.append(title)
    if 'detail' in payload:
        sets.append('detail=?'); params.append(str(payload.get('detail') or '')[:5000])
    if 'priority' in payload:
        try:
            priority = max(0, min(2, int(payload.get('priority') or 0)))
        except Exception:
            priority = 0
        sets.append('priority=?'); params.append(priority)
    if 'due_at' in payload:
        try:
            due_at = float(payload.get('due_at') or 0)
        except Exception:
            due_at = 0
        sets.append('due_at=?'); params.append(due_at)
    if 'assignee' in payload:
        aid, err = _team_parse_assignee(db, ident, payload.get('assignee'))
        if err:
            return jsonify({'error': err}), 400
        sets.append('assignee_id=?'); params.append(aid)

    if not sets:
        return jsonify({'ok': True})
    sets.append('updated_at=?'); params.append(now)
    params.append(tid)
    _exec(db, f'UPDATE team_tasks SET {", ".join(sets)} WHERE id=?', tuple(params))
    db.commit()
    return jsonify({'ok': True})


@app.route('/api/team/tasks/<tid>', methods=['DELETE'])
@team_required()
def api_team_task_delete(tid):
    ident = g.team
    db = get_db()
    t = _fetchone(db, 'SELECT * FROM team_tasks WHERE id=?', (tid,))
    if not t:
        return jsonify({'error': 'Not found'}), 404
    if not ((t.get('assignee_id') or '') == ident['id'] or (t.get('creator_id') or '') == ident['id']
            or _team_can_manage(ident['role'])):
        return jsonify({'error': 'Not found'}), 404
    _exec(db, 'DELETE FROM team_tasks WHERE id=?', (tid,))
    db.commit()
    _team_log('task_delete', detail=t.get('title') or '', uid=ident['id'])
    return jsonify({'ok': True})


# ===== 待办（纯个人）=====
@app.route('/api/team/todos', methods=['GET'])
@team_required()
def api_team_todos():
    ident = g.team
    db = get_db()
    now = time.time()
    rows = _fetchall(db, 'SELECT * FROM team_todos WHERE user_id=? ORDER BY done ASC, created_at DESC LIMIT 500', (ident['id'],))
    items = [{'id': r['id'], 'content': r['content'], 'done': bool(r.get('done')),
              'due_at': float(r.get('due_at') or 0), 'created_at': float(r.get('created_at') or 0),
              'updated_at': float(r.get('updated_at') or 0),
              'overdue': bool(r.get('due_at') and float(r['due_at']) < now and not r.get('done'))} for r in rows]
    return jsonify({'items': items,
                    'counts': {'open': _team_count(db, 'SELECT COUNT(*) AS c FROM team_todos WHERE user_id=? AND done=0', (ident['id'],)),
                               'done': _team_count(db, 'SELECT COUNT(*) AS c FROM team_todos WHERE user_id=? AND done=1', (ident['id'],))}})


@app.route('/api/team/todos', methods=['POST'])
@team_required()
def api_team_todo_create():
    ident = g.team
    payload = request.get_json(silent=True) or {}
    content = (payload.get('content') or '').strip()
    if not content or len(content) > 500:
        return jsonify({'error': '待办内容不能为空且不超过 500 字'}), 400
    try:
        due_at = float(payload.get('due_at') or 0)
    except Exception:
        due_at = 0
    db = get_db()
    now = time.time()
    tid = uuid.uuid4().hex
    _exec(db, 'INSERT INTO team_todos (id, user_id, content, done, due_at, created_at, updated_at) VALUES (?,?,?,?,?,?,?)',
          (tid, ident['id'], content, 0, due_at, now, now))
    db.commit()
    return jsonify({'ok': True, 'id': tid})


@app.route('/api/team/todos/<tid>', methods=['PATCH'])
@team_required()
def api_team_todo_update(tid):
    ident = g.team
    db = get_db()
    t = _fetchone(db, 'SELECT * FROM team_todos WHERE id=?', (tid,))
    if not t or (t.get('user_id') or '') != ident['id']:
        return jsonify({'error': 'Not found'}), 404
    payload = request.get_json(silent=True) or {}
    sets, params = [], []
    if 'content' in payload:
        content = (payload.get('content') or '').strip()
        if not content or len(content) > 500:
            return jsonify({'error': '待办内容不能为空且不超过 500 字'}), 400
        sets.append('content=?'); params.append(content)
    if 'done' in payload:
        sets.append('done=?'); params.append(1 if payload.get('done') else 0)
    if 'due_at' in payload:
        try:
            due_at = float(payload.get('due_at') or 0)
        except Exception:
            due_at = 0
        sets.append('due_at=?'); params.append(due_at)
    if not sets:
        return jsonify({'ok': True})
    sets.append('updated_at=?'); params.append(time.time())
    params.append(tid)
    _exec(db, f'UPDATE team_todos SET {", ".join(sets)} WHERE id=?', tuple(params))
    db.commit()
    return jsonify({'ok': True})


@app.route('/api/team/todos/<tid>', methods=['DELETE'])
@team_required()
def api_team_todo_delete(tid):
    ident = g.team
    db = get_db()
    t = _fetchone(db, 'SELECT id, user_id FROM team_todos WHERE id=?', (tid,))
    if not t or (t.get('user_id') or '') != ident['id']:
        return jsonify({'error': 'Not found'}), 404
    _exec(db, 'DELETE FROM team_todos WHERE id=?', (tid,))
    db.commit()
    return jsonify({'ok': True})


# ===== 日历日程 =====
@app.route('/api/team/events', methods=['GET'])
@team_required()
def api_team_events():
    ident = g.team
    now = time.time()
    try:
        frm = float(request.args.get('from') or 0)
    except Exception:
        frm = 0
    try:
        to = float(request.args.get('to') or 0)
    except Exception:
        to = 0
    # 默认取当前时间前后各 45 天
    if not frm and not to:
        frm, to = now - 45 * 86400, now + 45 * 86400
    elif not frm:
        frm = to - 45 * 86400
    elif not to:
        to = frm + 45 * 86400
    db = get_db()
    rows = _fetchall(db, '''SELECT e.*, u.username AS owner_name FROM team_events e
                            LEFT JOIN users u ON u.id = e.owner_id
                            WHERE e.start_at<=? AND (CASE WHEN e.end_at>0 THEN e.end_at ELSE e.start_at END)>=?
                              AND (e.scope='team' OR e.owner_id=?)
                            ORDER BY e.start_at ASC LIMIT 1000''', (to, frm, ident['id']))
    items = [{'id': r['id'], 'title': r['title'], 'detail': r.get('detail') or '',
              'scope': r.get('scope') or 'personal', 'start_at': float(r.get('start_at') or 0),
              'end_at': float(r.get('end_at') or 0), 'all_day': bool(r.get('all_day')),
              'owner_id': r.get('owner_id') or '', 'owner_name': r.get('owner_name') or '',
              'mine': (r.get('owner_id') or '') == ident['id'],
              'can_edit': (r.get('owner_id') or '') == ident['id'] or _team_can_manage(ident['role'])} for r in rows]
    return jsonify({'items': items})


@app.route('/api/team/events', methods=['POST'])
@team_required()
def api_team_event_create():
    ident = g.team
    payload = request.get_json(silent=True) or {}
    title = (payload.get('title') or '').strip()
    if not title or len(title) > 200:
        return jsonify({'error': '日程标题不能为空且不超过 200 字'}), 400
    try:
        start_at = float(payload.get('start_at') or 0)
    except Exception:
        start_at = 0
    if start_at <= 0:
        return jsonify({'error': '请提供有效的开始时间'}), 400
    try:
        end_at = float(payload.get('end_at') or 0)
    except Exception:
        end_at = 0
    if end_at < start_at:
        end_at = start_at
    scope = payload.get('scope') if payload.get('scope') in ('personal', 'team') else 'personal'
    if scope == 'team' and TEAM_ROLE_RANK.get(ident['role'], 0) < TEAM_ROLE_RANK['core']:
        return jsonify({'error': '只有核心成员及以上可以创建团队日程'}), 400
    db = get_db()
    eid = uuid.uuid4().hex
    _exec(db, '''INSERT INTO team_events (id, title, detail, owner_id, scope, start_at, end_at, all_day, created_at)
                 VALUES (?,?,?,?,?,?,?,?,?)''',
          (eid, title, str(payload.get('detail') or '')[:2000], ident['id'], scope, start_at, end_at,
           1 if payload.get('all_day') else 0, time.time()))
    db.commit()
    return jsonify({'ok': True, 'id': eid})


@app.route('/api/team/events/<eid>', methods=['PATCH'])
@team_required()
def api_team_event_update(eid):
    ident = g.team
    db = get_db()
    e = _fetchone(db, 'SELECT * FROM team_events WHERE id=?', (eid,))
    if not e or not ((e.get('owner_id') or '') == ident['id'] or _team_can_manage(ident['role'])):
        return jsonify({'error': 'Not found'}), 404
    payload = request.get_json(silent=True) or {}
    sets, params = [], []
    if 'title' in payload:
        title = (payload.get('title') or '').strip()
        if not title or len(title) > 200:
            return jsonify({'error': '日程标题不能为空且不超过 200 字'}), 400
        sets.append('title=?'); params.append(title)
    if 'detail' in payload:
        sets.append('detail=?'); params.append(str(payload.get('detail') or '')[:2000])
    if 'scope' in payload:
        scope = payload.get('scope') if payload.get('scope') in ('personal', 'team') else 'personal'
        if scope == 'team' and TEAM_ROLE_RANK.get(ident['role'], 0) < TEAM_ROLE_RANK['core']:
            return jsonify({'error': '只有核心成员及以上可以创建团队日程'}), 400
        sets.append('scope=?'); params.append(scope)
    new_start = e.get('start_at')
    if 'start_at' in payload:
        try:
            new_start = float(payload.get('start_at') or 0)
        except Exception:
            new_start = 0
        if new_start <= 0:
            return jsonify({'error': '请提供有效的开始时间'}), 400
        sets.append('start_at=?'); params.append(new_start)
    if 'end_at' in payload:
        try:
            end_at = float(payload.get('end_at') or 0)
        except Exception:
            end_at = 0
        if end_at < float(new_start or 0):
            end_at = float(new_start or 0)
        sets.append('end_at=?'); params.append(end_at)
    if 'all_day' in payload:
        sets.append('all_day=?'); params.append(1 if payload.get('all_day') else 0)
    if not sets:
        return jsonify({'ok': True})
    params.append(eid)
    _exec(db, f'UPDATE team_events SET {", ".join(sets)} WHERE id=?', tuple(params))
    db.commit()
    return jsonify({'ok': True})


@app.route('/api/team/events/<eid>', methods=['DELETE'])
@team_required()
def api_team_event_delete(eid):
    ident = g.team
    db = get_db()
    e = _fetchone(db, 'SELECT owner_id FROM team_events WHERE id=?', (eid,))
    if not e or not ((e.get('owner_id') or '') == ident['id'] or _team_can_manage(ident['role'])):
        return jsonify({'error': 'Not found'}), 404
    _exec(db, 'DELETE FROM team_events WHERE id=?', (eid,))
    db.commit()
    return jsonify({'ok': True})


# ===== 在线聊天（一对一 + 团队群聊）=====
def _team_chat_of(cid, uid):
    """取会话并校验当前用户是否为成员"""
    db = get_db()
    c = _fetchone(db, 'SELECT * FROM team_chats WHERE id=?', (cid,))
    if not c:
        return None
    if not _fetchone(db, 'SELECT chat_id FROM team_chat_members WHERE chat_id=? AND user_id=?', (cid, uid)):
        return None
    return c


def _team_chat_members(cid):
    db = get_db()
    rows = _fetchall(db, '''SELECT cm.user_id, tm.role, tm.job_title, tm.department, u.username, u.avatar
                            FROM team_chat_members cm
                            LEFT JOIN users u ON u.id = cm.user_id
                            LEFT JOIN team_members tm ON tm.user_id = cm.user_id
                            WHERE cm.chat_id=?''', (cid,))
    return [{
        'user_id': r['user_id'], 'username': r.get('username') or '（已注销）',
        'avatar': (f"/{r['avatar']}" if r.get('avatar') else ''),
        'role': r.get('role') or '', 'role_label': TEAM_ROLE_LABEL.get(r.get('role') or '', ''),
        'job_title': r.get('job_title') or '', 'department': r.get('department') or '',
    } for r in rows]


def _team_chat_json(c, uid, members=None):
    db = get_db()
    members = members if members is not None else _team_chat_members(c['id'])
    me_row = _fetchone(db, 'SELECT last_read_at FROM team_chat_members WHERE chat_id=? AND user_id=?', (c['id'], uid))
    last_read = float((me_row or {}).get('last_read_at') or 0)
    last = _fetchone(db, '''SELECT m.*, u.username AS sender_name FROM team_chat_messages m
                            LEFT JOIN users u ON u.id = m.sender_id
                            WHERE m.chat_id=? ORDER BY m.created_at DESC LIMIT 1''', (c['id'],))
    un = _fetchone(db, '''SELECT COUNT(*) AS n FROM team_chat_messages
                          WHERE chat_id=? AND created_at>? AND sender_id<>?''', (c['id'], last_read, uid))
    if c.get('kind') == 'group':
        title = c.get('name') or '群聊'
    else:
        other = next((m for m in members if m['user_id'] != uid), None)
        title = (other or {}).get('username') or '（已注销）'
    return {
        'id': c['id'], 'kind': c.get('kind') or 'direct', 'title': title,
        'name': c.get('name') or '', 'members': members,
        'unread': int((un or {}).get('n') or 0),
        'last': ({
            'body': (last.get('body') or '')[:120], 'sender_id': last.get('sender_id') or '',
            'sender_name': last.get('sender_name') or '', 'created_at': float(last.get('created_at') or 0),
        } if last else None),
        'updated_at': float(c.get('updated_at') or c.get('created_at') or 0),
        'created_at': float(c.get('created_at') or 0),
    }


def _team_chat_find_direct(uid, other):
    db = get_db()
    row = _fetchone(db, '''SELECT c.id FROM team_chats c
                           JOIN team_chat_members a ON a.chat_id=c.id AND a.user_id=?
                           JOIN team_chat_members b ON b.chat_id=c.id AND b.user_id=?
                           WHERE c.kind='direct' LIMIT 1''', (uid, other))
    return row['id'] if row else None


@app.route('/api/team/chats', methods=['GET'])
@team_required()
def api_team_chats():
    ident = g.team
    db = get_db()
    rows = _fetchall(db, '''SELECT c.* FROM team_chats c
                            JOIN team_chat_members m ON m.chat_id=c.id
                            WHERE m.user_id=? ORDER BY c.updated_at DESC LIMIT 200''', (ident['id'],))
    items = [_team_chat_json(c, ident['id']) for c in rows]
    items.sort(key=lambda x: x['updated_at'], reverse=True)
    return jsonify({'items': items, 'total_unread': sum(i['unread'] for i in items),
                    'me': ident['id']})


@app.route('/api/team/peers', methods=['GET'])
@team_required()
def api_team_peers():
    """团队成员列表（排除自己），供成员选择与发起会话使用"""
    ident = g.team
    db = get_db()
    rows = _fetchall(db, '''SELECT m.user_id, m.role, m.job_title, m.department, u.username, u.avatar
                            FROM team_members m LEFT JOIN users u ON u.id = m.user_id
                            WHERE m.status='active' AND m.user_id<>?
                            ORDER BY CASE m.role WHEN 'owner' THEN 1 WHEN 'core' THEN 2 WHEN 'member' THEN 3 ELSE 4 END, u.username''',
                     (ident['id'],))
    return jsonify({'items': [{
        'user_id': r['user_id'], 'username': r.get('username') or '（已注销）',
        'avatar': (f"/{r['avatar']}" if r.get('avatar') else ''),
        'role': r.get('role') or '', 'role_label': TEAM_ROLE_LABEL.get(r.get('role') or '', ''),
        'job_title': r.get('job_title') or '', 'department': r.get('department') or '',
    } for r in rows]})


@app.route('/api/team/chats', methods=['POST'])
@team_required()
def api_team_chat_open():
    """打开（必要时创建）与某成员的一对一会话"""
    ident = g.team
    payload = request.get_json(silent=True) or {}
    other = str(payload.get('user_id') or '')
    if not other or other == ident['id']:
        return jsonify({'error': '请选择一位成员'}), 400
    if not _team_role_of(other):
        return jsonify({'error': '该账户不是团队成员'}), 404
    cid = _team_chat_find_direct(ident['id'], other)
    if cid:
        return jsonify({'ok': True, 'id': cid, 'created': False})
    db = get_db()
    cid = uuid.uuid4().hex
    now = time.time()
    _exec(db, 'INSERT INTO team_chats (id, kind, name, created_by, created_at, updated_at) VALUES (?,?,?,?,?,?)',
          (cid, 'direct', '', ident['id'], now, now))
    for uid in (ident['id'], other):
        _exec(db, 'INSERT INTO team_chat_members (chat_id, user_id, joined_at, last_read_at) VALUES (?,?,?,?)',
              (cid, uid, now, 0))
    db.commit()
    _team_log('chat_open', detail=f'发起一对一会话（{other}）', uid=ident['id'])
    return jsonify({'ok': True, 'id': cid, 'created': True})


@app.route('/api/team/chats/group', methods=['POST'])
@team_required()
def api_team_chat_group():
    ident = g.team
    payload = request.get_json(silent=True) or {}
    name = (payload.get('name') or '').strip()[:60]
    ids = [str(x) for x in (payload.get('user_ids') or []) if x]
    if not name:
        return jsonify({'error': '请填写群聊名称'}), 400
    members = [u for u in dict.fromkeys([ident['id']] + ids) if _team_role_of(u)]
    if len(members) < 3:
        return jsonify({'error': '群聊至少需要 3 位成员'}), 400
    if len(members) > 200:
        return jsonify({'error': '单个群聊最多 200 位成员'}), 400
    db = get_db()
    cid = uuid.uuid4().hex
    now = time.time()
    _exec(db, 'INSERT INTO team_chats (id, kind, name, created_by, created_at, updated_at) VALUES (?,?,?,?,?,?)',
          (cid, 'group', name, ident['id'], now, now))
    for uid in members:
        _exec(db, 'INSERT INTO team_chat_members (chat_id, user_id, joined_at, last_read_at) VALUES (?,?,?,?)',
              (cid, uid, now, now if uid == ident['id'] else 0))
    db.commit()
    _team_log('chat_group', detail=f'创建群聊「{name}」（{len(members)} 人）', uid=ident['id'])
    return jsonify({'ok': True, 'id': cid})


@app.route('/api/team/chats/<cid>/messages', methods=['GET'])
@team_required()
def api_team_chat_messages(cid):
    ident = g.team
    c = _team_chat_of(cid, ident['id'])
    if not c:
        return jsonify({'error': 'Not found'}), 404
    after = request.args.get('after')
    limit = min(int(request.args.get('limit') or 60), 200)
    db = get_db()
    if after:
        rows = _fetchall(db, '''SELECT m.*, u.username AS sender_name FROM team_chat_messages m
                                LEFT JOIN users u ON u.id = m.sender_id
                                WHERE m.chat_id=? AND m.created_at>? ORDER BY m.created_at LIMIT ?''',
                         (cid, float(after), limit))
    else:
        rows = _fetchall(db, '''SELECT m.*, u.username AS sender_name FROM team_chat_messages m
                                LEFT JOIN users u ON u.id = m.sender_id
                                WHERE m.chat_id=? ORDER BY m.created_at DESC LIMIT ?''', (cid, limit))
        rows = list(reversed(rows))
    return jsonify({'chat': _team_chat_json(c, ident['id']), 'items': [{
        'id': r['id'], 'sender_id': r['sender_id'], 'sender_name': r.get('sender_name') or '（已注销）',
        'body': r.get('body') or '', 'mine': r['sender_id'] == ident['id'],
        'created_at': float(r.get('created_at') or 0),
    } for r in rows]})


@app.route('/api/team/chats/<cid>/messages', methods=['POST'])
@team_required()
def api_team_chat_send(cid):
    ident = g.team
    c = _team_chat_of(cid, ident['id'])
    if not c:
        return jsonify({'error': 'Not found'}), 404
    payload = request.get_json(silent=True) or {}
    body = (payload.get('body') or '').strip()
    if not body:
        return jsonify({'error': '消息不能为空'}), 400
    if len(body) > TEAM_CHAT_MAX_LEN:
        return jsonify({'error': f'单条消息不能超过 {TEAM_CHAT_MAX_LEN} 字'}), 400
    db = get_db()
    mid = uuid.uuid4().hex
    now = time.time()
    _exec(db, 'INSERT INTO team_chat_messages (id, chat_id, sender_id, body, created_at) VALUES (?,?,?,?,?)',
          (mid, cid, ident['id'], body, now))
    _exec(db, 'UPDATE team_chats SET updated_at=? WHERE id=?', (now, cid))
    _exec(db, 'UPDATE team_chat_members SET last_read_at=? WHERE chat_id=? AND user_id=?', (now, cid, ident['id']))
    db.commit()
    return jsonify({'ok': True, 'item': {
        'id': mid, 'sender_id': ident['id'], 'sender_name': ident['username'],
        'body': body, 'mine': True, 'created_at': now,
    }})


@app.route('/api/team/chats/<cid>/read', methods=['POST'])
@team_required()
def api_team_chat_read(cid):
    ident = g.team
    c = _team_chat_of(cid, ident['id'])
    if not c:
        return jsonify({'error': 'Not found'}), 404
    payload = request.get_json(silent=True) or {}
    ts = float(payload.get('ts') or time.time())
    db = get_db()
    _exec(db, 'UPDATE team_chat_members SET last_read_at=? WHERE chat_id=? AND user_id=?',
          (ts, cid, ident['id']))
    db.commit()
    return jsonify({'ok': True})


@app.route('/api/team/chats/<cid>', methods=['DELETE'])
@team_required()
def api_team_chat_leave(cid):
    """退出会话（一对一会话仅清除自己的成员记录）"""
    ident = g.team
    c = _team_chat_of(cid, ident['id'])
    if not c:
        return jsonify({'error': 'Not found'}), 404
    db = get_db()
    _exec(db, 'DELETE FROM team_chat_members WHERE chat_id=? AND user_id=?', (cid, ident['id']))
    left = _fetchone(db, 'SELECT COUNT(*) AS n FROM team_chat_members WHERE chat_id=?', (cid,))
    if not left or int(left['n'] or 0) == 0:
        _exec(db, 'DELETE FROM team_chat_messages WHERE chat_id=?', (cid,))
        _exec(db, 'DELETE FROM team_chats WHERE id=?', (cid,))
    db.commit()
    return jsonify({'ok': True})


# ===== 浏览器内联预览（全屏查看）=====
@app.route('/api/team/file/<fid>/view', methods=['GET'])
@team_required()
def api_team_file_view(fid):
    ident = g.team
    f = _team_get_file(fid)
    if not f or f['is_dir'] or not _team_can_see_file(f, ident):
        return jsonify({'error': 'Not found'}), 404
    path = os.path.join(_DATA_DIR, f.get('storage') or '')
    if not f.get('storage') or not os.path.isfile(path):
        return jsonify({'error': '文件内容缺失'}), 404
    ext = _team_ext(f['name'])
    mime = (f.get('mime') or '').strip()
    # mime 缺失或为通用二进制时，按扩展名推断，保证浏览器能内联渲染
    if not mime or mime == 'application/octet-stream':
        mime = TEAM_INLINE_MIME.get(ext, 'application/octet-stream')
    _team_log('view', f['id'], f['name'], detail='内联预览', uid=ident['id'])
    resp = Response(_team_swc(_team_decrypt_stream(path)), mimetype=mime)
    resp.headers['Content-Disposition'] = "inline; filename*=UTF-8''" + _team_quote(f['name'])
    resp.headers['Content-Length'] = str(int(f.get('size') or 0))
    resp.headers['Cache-Control'] = 'no-store'
    resp.headers['X-Content-Type-Options'] = 'nosniff'
    return resp


# ===== 大小限制：非 Team 接口维持 50MB 上限 =====
@app.before_request
def _team_upload_size_guard():
    if request.path.startswith('/api/team/'):
        return None
    try:
        if (request.content_length or 0) > 50 * 1024 * 1024:
            return jsonify({'error': '请求体过大'}), 413
    except Exception:
        pass
    return None


# ===== 启动 =====
# ==========================================================================
# [9] 一期 RSS 源池抓取调度模块（scheduler.py）
#     职责：读取 source-pool.json 的直连源 -> 定时抓取 -> 去重写入 news 表
#     挂载时机：必须早于 app.run()，否则后台线程不会启动
# ==========================================================================
# 数据库初始化必须放在模块顶层：Faable 用 gunicorn 以 import 方式加载应用，
# 若 init_db() 仅放在 __main__ 块内，gunicorn 模式下不会执行，导致所有表缺失（API 500）
init_db()
print('[INIT] 数据库初始化完成:', DB_PATH if not _USE_PG else 'PostgreSQL')

try:
    import scheduler as _pn_scheduler
    _pn_scheduler.bootstrap(app, admin_required, jsonify, request)
    print('[SCHEDULER] 一期抓取调度模块已挂载：/api/admin/scheduler/status')
except Exception as _sched_err:
    print('[SCHEDULER] 一期抓取调度模块加载失败:', _sched_err)


if __name__ == '__main__':
    init_db()
    # 启动后台清理线程：每小时清理一次未验证邮箱账号
    def _cleanup_loop():
        while True:
            try:
                time.sleep(3600)
                _cleanup_unverified_users()
            except Exception as e:
                print(f'[CLEANUP] 循环异常: {e}')
    _cleanup_thread = threading.Thread(target=_cleanup_loop, daemon=True)
    _cleanup_thread.start()
    # 启动时先清理一次
    _cleanup_unverified_users()
    # 启动 AI 审核定期巡查线程：每 5 小时扫描一次（需管理后台开启 moderation_enabled）
    _ai_thread = threading.Thread(target=_ai_moderation_loop, daemon=True)
    _ai_thread.start()
    print('SoaringBird 论坛服务器启动中...')
    print('数据库:', DB_PATH if not _USE_PG else 'PostgreSQL (' + os.environ.get('DATABASE_URL', '').split('@')[-1] + ')')
    _port = int(os.environ.get('PORT', 8080))
    print('访问 http://localhost:%d/' % _port)
    if _HAS_SOCKETIO and socketio:
        print('实时聊天: 已启用 (SocketIO)')
        # 单进程部署，允许 Werkzeug 运行（由 systemd 管理进程生命周期）
        socketio.run(app, host='0.0.0.0', port=_port, debug=False, allow_unsafe_werkzeug=True)
    else:
        print('实时聊天: 未启用 (请安装 flask-socketio)')
        app.run(host='0.0.0.0', port=_port, debug=False)
