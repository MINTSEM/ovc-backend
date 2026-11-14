# -*- coding: utf-8 -*-
"""块四 · eastwind-orchestrator 后端模块挂载进 ovc-backend（Flask 蓝图）

ovc-backend 的 server.py 为 Flask 应用（app = Flask(__name__, static_folder='.')，
监听 8080，已提供 /api/news 读 bird.db）。本模块把 eastwind 侧的后端能力
（cold_start / breakfiller / pipeline）以 Flask 蓝图形式挂载到同一进程，
避免多起一个服务：

    在 server.py 的 `if __name__ == '__main__':` 块内、app.run/socketio.run
    之前插入：

        try:
            from eastwind_mount import register as _register_eastwind
            _register_eastwind(app)
            print('[EASTWIND] 东广视模块已挂载 (/api/eastwind/*)')
        except Exception as _e:
            print('[EASTWIND] 挂载失败:', _e)

前置：pip install flask（ovc-backend 已有）；把 eastwind-orchestrator 项目根
加到 PYTHONPATH，或在 server.py 中 os.sys.path.insert(0, '<eastwind-orchestrator 根>')。

路由：
    POST /api/eastwind/cold-start/start   前端打点触发冷启动+半试跑
    GET  /api/eastwind/cold-start/status  查询冷启动状态
    GET  /api/eastwind/breakfiller/latest 生成/返回最近 breakfiller 简报
    POST /api/eastwind/pipeline/run       触发编排流水线（默认 dry-run）
"""
from __future__ import annotations

import os
import sys
import time

# eastwind-orchestrator 项目根
# 1) 环境变量 EASTWIND_REPO_ROOT 优先（本模块被复制到 ovc-backend 后由 server.py 注入）；
# 2) 回退：本文件位于 <根>/scripts/ 下。
_EW_ROOT = os.environ.get("EASTWIND_REPO_ROOT") or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _EW_ROOT not in sys.path:
    sys.path.insert(0, _EW_ROOT)

# 延迟导入：避免 ovc-backend 启动时因缺依赖整体失败
_engine = None  # cold_start.engine.ColdStartEngine 单例


def _get_engine():
    global _engine
    if _engine is None:
        from cold_start.engine import ColdStartEngine
        _engine = ColdStartEngine()
    return _engine


def _get_news_url() -> str:
    """返回当前新闻数据源描述（仅诊断展示，不含品牌）。"""
    from slot_agents import config as _cfg
    return _cfg.NEWS_HTTP_URL or "(未配置，走本地 bird.db/降级)"


def register(app) -> None:
    """在 Flask app 上挂载东广视后端路由。"""
    try:
        from flask import Blueprint, jsonify, request
    except Exception as exc:  # pragma: no cover
        print(f"[EASTWIND] flask 不可用，跳过挂载: {exc}")
        return

    bp = Blueprint("eastwind", __name__, url_prefix="/api/eastwind")

    @bp.route("/cold-start/start", methods=["POST"])
    def cold_start_start():
        body = request.get_json(silent=True) or {}
        source_page = body.get("source", "index.html")
        origin = request.headers.get("Origin", "")
        from cold_start import config as _cs_cfg
        if origin and origin not in _cs_cfg.ALLOWED_ORIGINS:
            return jsonify({"ok": False, "reason": "origin_not_allowed"})
        report = _get_engine().trigger_cold_start(source_page=source_page)
        return jsonify({"ok": True, "data": report})

    @bp.route("/cold-start/status", methods=["GET"])
    def cold_start_status():
        return jsonify({"ok": True, "data": _get_engine().get_status()})

    @bp.route("/breakfiller/latest", methods=["GET"])
    def breakfiller_latest():
        try:
            from breakfiller.news_feed import build_live_breakfiller
            limit = request.args.get("limit", default=8, type=int)
            out_path, source = build_live_breakfiller(limit=min(limit, 20))
            return jsonify({"ok": True, "file": out_path, "source": source})
        except Exception as exc:
            return jsonify({"ok": False, "reason": str(exc)}), 500

    @bp.route("/pipeline/run", methods=["POST"])
    def pipeline_run():
        body = request.get_json(silent=True) or {}
        news_limit = int(body.get("news_limit", 6))
        live = bool(body.get("live", False))
        source_page = body.get("source_page", "news.html")
        if live:
            # 真实录制属高风险动作：默认拒绝，需显式 X-Eastwind-Live: 1 且来源受信
            if request.headers.get("X-Eastwind-Live") != "1":
                return jsonify({"ok": False, "reason": "live_requires_flag"}), 403
        from scripts.pipeline import run_pipeline
        log = run_pipeline(news_limit=news_limit, live=live, source_page=source_page)
        return jsonify({"ok": True, "data": log})

    app.register_blueprint(bp)
    # 输出诊断（不暴露品牌与密钥）
    try:
        print(f"[EASTWIND] 新闻数据源: {_get_news_url()}")
    except Exception:
        pass


if __name__ == "__main__":
    # 本地冒烟：语法 + 依赖可达性验证（不起 web 服务）
    t0 = time.time()
    engine = _get_engine()
    st = engine.get_status()
    print("cold_start engine OK:", st.get("status"))
    print(f"smoke done in {time.time() - t0:.2f}s")
