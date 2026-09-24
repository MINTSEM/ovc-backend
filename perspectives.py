# -*- coding: utf-8 -*-
"""翱翔鸟二期前半 · 视角分析模块（perspectives.py）

职责：
- 预置 5 个视角包（经济 / 科技 / 国际 / 深度调查 / 社会民生），每个含
  名称、描述、关注维度（分析要点）、证据标准（一句话）。
- 复用与 server.py 翻译通道一致的 LLM/API 通道（bird.db ai_config 表 +
  OpenAI 兼容协议），对指定新闻生成结构化分析：
  视角摘要 + 关键事实 + 多角度要点 + 不确定性说明。
- 分析结果落库 perspective_outputs 表；已分析过的直接返回缓存，避免重复生成。
- 提供 3 个 API：列出视角 / 触发视角分析 / 查询某新闻的分析结果。

不承载"观点对撞"（stancePanel 仍为死 UI，保持不动）。
"""

import json
import os
import re
import sqlite3
import time
import urllib.error
import urllib.request

BASE_DIR = os.path.dirname(os.path.abspath(__file__))  # 扁平化后位于项目根
DB_PATH = os.environ.get("BIRD_DB", os.path.join(BASE_DIR, "bird.db"))

AI_BASE_URL = os.environ.get("AI_BASE_URL", "http://localhost:1234/v1")
AI_MODEL = os.environ.get("AI_MODEL", "local-model")
AI_API_KEY = os.environ.get("AI_API_KEY", "")

_TABLE_SQL = """
CREATE TABLE IF NOT EXISTS perspective_outputs (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    news_id TEXT NOT NULL,
    perspective_id TEXT NOT NULL,
    perspective_name TEXT DEFAULT '',
    result_json TEXT NOT NULL,
    created_at REAL,
    model TEXT DEFAULT '',
    UNIQUE (news_id, perspective_id)
)
"""

# ----------------------------------------------------------------------
# 视角包定义（轻量落地：领域知识 + 理论方法 + 证据标准）
# ----------------------------------------------------------------------
PERSPECTIVES = [
    {
        "id": "economy",
        "name": "经济视角",
        "description": "用经济学与市场逻辑解读新闻：数据、价格、供需、政策与资本流动。",
        "dimensions": [
            "经济数据与宏观指标",
            "市场反应与资本流动",
            "产业链与供需影响",
            "政策与监管含义",
        ],
        "evidence_standard": "凡涉及数据、金额、增速等必须引用原文数字并注明口径，禁止估算替代。",
    },
    {
        "id": "tech",
        "name": "科技视角",
        "description": "关注技术进展、产品创新与产业竞争，判断新闻中的科技变量。",
        "dimensions": [
            "核心技术突破与原理",
            "产品发布与商业化进展",
            "产业竞争与生态格局",
            "对公众与社会的技术影响",
        ],
        "evidence_standard": "技术事实以原文或通行技术常识为准，无法确认的技术细节标注为存疑。",
    },
    {
        "id": "world",
        "name": "国际视角",
        "description": "从地缘政治与国际关系出发，梳理各方立场、互动与区域影响。",
        "dimensions": [
            "涉及国家/组织与各方立场",
            "地缘政治与外交互动",
            "区域局势与国际机制",
            "对国际秩序与周边的影响",
        ],
        "evidence_standard": "引用各方表态须区分「当事方说法」与「可证实事实」，不混合转述。",
    },
    {
        "id": "deep",
        "name": "深度调查视角",
        "description": "以调查报道的方法追问：事实是否核实、信源是否交叉、背后有无利益链条。",
        "dimensions": [
            "事实核查与信源交叉验证",
            "时间线与因果链条",
            "利益相关方与动机",
            "疑点、矛盾与信息缺口",
        ],
        "evidence_standard": "未交叉验证的信息必须单列标注为「待证实」，不得写入关键事实。",
    },
    {
        "id": "society",
        "name": "社会民生视角",
        "description": "聚焦民生影响、公共政策与社会公平，评估事件对普通人生活的意义。",
        "dimensions": [
            "民生影响与利益攸关方",
            "公共政策与治理含义",
            "社会公平与公众反应",
            "风险提示与后续建议",
        ],
        "evidence_standard": "涉及人群、区域、制度时须有原文依据，个案不得推广为普遍结论。",
    },
]


def _connect():
    conn = sqlite3.connect(DB_PATH, timeout=15)
    conn.row_factory = sqlite3.Row
    return conn


def init_table():
    """建表（幂等），由 server.init_db 或本模块挂载时调用。"""
    conn = _connect()
    try:
        conn.execute(_TABLE_SQL)
        conn.commit()
    finally:
        conn.close()


def get_ai_config():
    """从 ai_config 表读取配置（与 server.get_ai_config 相同逻辑，避免循环依赖）。"""
    try:
        conn = _connect()
        try:
            row = conn.execute(
                "SELECT base_url, model, api_key, COALESCE(moderation_enabled,0) AS moderation_enabled "
                "FROM ai_config WHERE id=1"
            ).fetchone()
        finally:
            conn.close()
        if row:
            return {
                "base_url": row["base_url"] or AI_BASE_URL,
                "model": row["model"] or AI_MODEL,
                "api_key": row["api_key"] or AI_API_KEY,
            }
    except Exception:
        pass
    return {"base_url": AI_BASE_URL, "model": AI_MODEL, "api_key": AI_API_KEY}


def call_lm(system, user, timeout=90):
    """OpenAI 兼容 chat/completions 调用（与 server.call_lm_studio 同协议）。"""
    cfg = get_ai_config()
    base_url = cfg["base_url"].rstrip("/")
    if not re.search(r"/v\d+(/|$)", base_url):
        base_url = base_url + "/v1"
    payload = json.dumps({
        "model": cfg["model"],
        "messages": [
            {"role": "system", "content": system},
            {"role": "user", "content": user},
        ],
        "temperature": 0.4,
        "max_tokens": 1800,
    }).encode("utf-8")
    headers = {"Content-Type": "application/json"}
    if cfg.get("api_key"):
        headers["Authorization"] = "Bearer " + cfg["api_key"]
    req = urllib.request.Request(base_url + "/chat/completions", data=payload, headers=headers)
    try:
        resp = urllib.request.urlopen(req, timeout=timeout)
        raw = resp.read().decode("utf-8")
    except urllib.error.HTTPError as e:
        body = e.read().decode("utf-8", errors="replace")
        raise Exception("视角分析 API 返回 HTTP %s: %s" % (e.code, body[:300]))
    except urllib.error.URLError as e:
        raise Exception("无法连接 AI 服务（%s），请确认本地模型服务已启动" % (base_url,))
    try:
        data = json.loads(raw)
    except Exception:
        raise Exception("视角分析 API 返回非 JSON 数据: %s" % raw[:300])
    if "error" in data:
        raise Exception("视角分析 API 错误: %s" % data["error"])
    choices = data.get("choices") or []
    if not choices:
        raise Exception("视角分析 API 返回无 choices 字段")
    return (choices[0].get("message") or {}).get("content") or ""


# ----------------------------------------------------------------------
# 分析生成与缓存
# ----------------------------------------------------------------------
_SYSTEM_PROMPT = (
    "你是翱翔鸟新闻平台的「视角分析器」。根据给定的新闻文本和指定视角，"
    "生成一份结构化中文分析。输出必须是合法 JSON，结构如下：\n"
    "{\n"
    '  "summary": "视角摘要（3-5 句，概述该视角下本条新闻的核心判断）",\n'
    '  "facts": ["关键事实 1（须有原文依据）", "关键事实 2", ...3-6 条],\n'
    '  "angles": ["多角度要点 1（不同立场/侧面/时间维度的解读）", ...3-5 条],\n'
    '  "uncertainty": "不确定性说明（1-3 句，注明未证实信息、信息缺口或口径差异）"\n'
    "}\n"
    "要求：1) 只输出 JSON，不要输出解释或 markdown 代码块；"
    "2) 关键事实必须来自给定新闻文本，不得编造；"
    "3) 遵守该视角的证据标准；4) 事实与观点分离，分析不替代原文。"
)


def _parse_output(text):
    text = (text or "").strip()
    # 剥离可能的 ```json ... ``` 围栏
    m = re.search(r"```(?:json)?\s*(.*?)```", text, re.S)
    if m:
        text = m.group(1).strip()
    # 直接解析；失败时尝试提取首个 { ... } 块
    try:
        return json.loads(text)
    except Exception:
        pass
    m = re.search(r"\{.*\}", text, re.S)
    if m:
        try:
            return json.loads(m.group(0))
        except Exception:
            pass
    # 兜底：整体作为摘要保存
    return {"summary": text, "facts": [], "angles": [], "uncertainty": "原始输出无法结构化解析，已按原文保留。"}


def _get_news_context(news_id):
    conn = _connect()
    try:
        row = conn.execute(
            "SELECT id, title, content, summary, category FROM news WHERE id=?",
            (news_id,),
        ).fetchone()
    finally:
        conn.close()
    if not row:
        return None
    title = (row["title"] or "").strip()
    summary = (row["summary"] or "").strip()
    content = (row["content"] or "").strip()
    if len(content) > 3000:
        content = content[:3000] + "……（正文已截断）"
    return {
        "title": title,
        "summary": summary,
        "content": content,
        "category": row["category"] or "",
    }


def _get_cached(news_id, perspective_id):
    conn = _connect()
    try:
        row = conn.execute(
            "SELECT result_json, created_at, model FROM perspective_outputs "
            "WHERE news_id=? AND perspective_id=?",
            (news_id, perspective_id),
        ).fetchone()
    finally:
        conn.close()
    if not row:
        return None
    try:
        return {
            "output": json.loads(row["result_json"]),
            "created_at": row["created_at"],
            "model": row["model"] or "",
        }
    except Exception:
        return None


def _store(news_id, perspective_id, perspective_name, output, model=""):
    conn = _connect()
    try:
        conn.execute(
            "INSERT OR REPLACE INTO perspective_outputs "
            "(news_id, perspective_id, perspective_name, result_json, created_at, model) "
            "VALUES (?,?,?,?,?,?)",
            (news_id, perspective_id, perspective_name,
             json.dumps(output, ensure_ascii=False), time.time(), model),
        )
        conn.commit()
    finally:
        conn.close()


def analyze_news(news_id, perspective_id):
    """对指定新闻按视角生成分析。已有缓存直接返回；否则调用 LLM 生成并落库。

    返回 (payload, from_cache)：payload 含 status/output/created_at/model。
    """
    ctx = _get_news_context(news_id)
    if not ctx:
        raise ValueError("新闻不存在")
    persp = next((p for p in PERSPECTIVES if p["id"] == perspective_id), None)
    if not persp:
        raise ValueError("视角不存在")
    cached = _get_cached(news_id, perspective_id)
    if cached:
        return {
            "status": "cached",
            "news_id": news_id,
            "perspective_id": perspective_id,
            "perspective_name": persp["name"],
            "output": cached["output"],
            "created_at": cached["created_at"],
            "model": cached["model"],
        }, True
    user = (
        "新闻标题：%s\n新闻分类：%s\n新闻摘要：%s\n新闻正文：\n%s\n\n"
        "请以「%s」视角分析本条新闻。\n关注维度：%s\n证据标准：%s"
        % (
            ctx["title"],
            ctx["category"] or "未知",
            ctx["summary"] or "（无摘要）",
            ctx["content"] or "（无正文）",
            persp["name"],
            "；".join(persp["dimensions"]),
            persp["evidence_standard"],
        )
    )
    raw = call_lm(_SYSTEM_PROMPT, user)
    output = _parse_output(raw)
    _store(news_id, perspective_id, persp["name"], output, "ai")
    return {
        "status": "ok",
        "news_id": news_id,
        "perspective_id": perspective_id,
        "perspective_name": persp["name"],
        "output": output,
        "created_at": time.time(),
        "model": "ai",
    }, False


def list_outputs(news_id):
    """查询某新闻已生成的全部视角分析结果。"""
    conn = _connect()
    try:
        rows = conn.execute(
            "SELECT perspective_id, perspective_name, result_json, created_at, model "
            "FROM perspective_outputs WHERE news_id=? ORDER BY created_at DESC",
            (news_id,),
        ).fetchall()
    finally:
        conn.close()
    out = []
    for r in rows:
        try:
            out.append({
                "perspective_id": r["perspective_id"],
                "perspective_name": r["perspective_name"] or "",
                "output": json.loads(r["result_json"]),
                "created_at": r["created_at"],
                "model": r["model"] or "",
            })
        except Exception:
            continue
    return out


# ----------------------------------------------------------------------
# 路由挂载（由 server.py 调用）
# ----------------------------------------------------------------------
def register_routes(app, jsonify, request):
    init_table()

    @app.route("/api/perspectives", methods=["GET"])
    def api_list_perspectives():
        """列出可用视角包。"""
        return jsonify({"perspectives": PERSPECTIVES})

    @app.route("/api/perspectives/analyze", methods=["POST"])
    def api_trigger_perspective():
        """对某条新闻触发视角分析；已有缓存直接返回。"""
        payload = request.get_json(silent=True) or {}
        news_id = (payload.get("news_id") or "").strip()
        perspective_id = (payload.get("perspective_id") or "").strip()
        if not news_id or not perspective_id:
            return jsonify({"error": "缺少 news_id 或 perspective_id"}), 400
        try:
            data, from_cache = analyze_news(news_id, perspective_id)
        except ValueError as e:
            return jsonify({"error": str(e)}), 404
        except Exception as e:
            return jsonify({"error": "视角分析失败：%s" % str(e)}), 502
        data["from_cache"] = from_cache
        return jsonify(data)

    @app.route("/api/perspectives/<news_id>", methods=["GET"])
    def api_get_news_perspectives(news_id):
        """查询某新闻已生成的全部视角分析结果（前端进入详情页时批量回显缓存）。"""
        return jsonify({"news_id": news_id, "outputs": list_outputs(news_id)})

    print("[PERSPECTIVES] 二期视角分析模块已挂载：/api/perspectives")
    return app
