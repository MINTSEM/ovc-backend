# -*- coding: utf-8 -*-
"""翱翔鸟 peacenews 外部搜索层（source-search-adapter）

服务 AI 跨源检索与文本选中悬浮菜单（块一），与主新闻列表 source-pool/scheduler 完全隔离：
绝不写入主列表抓取聚合。维基百科彻底排除。

适配器清单（实测可用，2026-09 探测）：
  - netease163 网易新闻站内搜索（www.163.com/search?keyword=，解析 /dy/article/ 链接，
              关键词精确命中，聚合大量外媒译文转载，可搜历史）
  - zaobao    联合早报搜索页（站点搜索为 JS 渲染空壳，降级取热门外媒转载 story 链接 +
              标题关键词过滤，中文外媒视角）
  - guancha   观察者网搜索页（同样 JS 渲染，降级取热门 .shtml 链接 + 标题关键词过滤）
  - france24  France24 官方 RSS（直连可用，关键词过滤）
  - sixthtone Sixth Tone 官方 RSS（直连可用，关键词过滤）
  - bing      Bing RSS 端点兜底（format=rss 真实链接、无 key；实测 cn.bing.com
              强制中文本地化故定位中文查询兜底；对国外源 AP/Reuters/BBC/Guardian/
              NYT/AlJazeera/DW/NHK/AFP/NewsMinimalist 用「关键词+源名」查询 +
              结果 URL 域名白名单过滤等效伪 site:）
失败一律跳过不阻塞主链路。
"""
import re
import time
import html as _h
from urllib.parse import quote, urlparse

try:
    import requests
except ImportError:  # pragma: no cover
    requests = None

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36")
TIMEOUT = 8

# 国外源 → 目标域名白名单（Bing 兜底域名过滤用）
FOREIGN_DOMAINS = {
    "AP": ["apnews.com"],
    "Reuters": ["reuters.com"],
    "AFP": ["afp.com", "news.yahoo.com"],
    "BBC": ["bbc.com", "bbc.co.uk", "bbcchinese.com"],
    "Guardian": ["theguardian.com"],
    "NYT": ["nytimes.com", "cn.nytimes.com"],
    "AlJazeera": ["aljazeera.com", "aljazeera.net"],
    "DW": ["dw.com"],
    "NHK": ["nhk.or.jp", "www3.nhk.or.jp"],
    "France24": ["france24.com"],
    "SixthTone": ["sixthtone.com"],
    "NewsMinimalist": ["newsminimalist.com"],
}

SOURCE_META = {
    "netease163": "网易新闻",
    "zaobao": "联合早报",
    "guancha": "观察者网",
    "france24": "France24",
    "sixthtone": "Sixth Tone",
    "bing": "Bing 搜索兜底",
}

_WIKI_BLOCK = re.compile(r"wikipedia\.org|wikimedia", re.I)

# 简单内存缓存（60s TTL），避免 analyze / 悬浮菜单频繁请求同一查询
_CACHE = {}
_CACHE_TTL = 60


def _cache_get(key):
    v = _CACHE.get(key)
    if v and (time.time() - v[0]) < _CACHE_TTL:
        return v[1]
    return None


def _cache_set(key, val):
    _CACHE[key] = (time.time(), val)
    if len(_CACHE) > 200:
        for k in list(_CACHE.keys())[:50]:
            _CACHE.pop(k, None)


def _get(url, params=None, headers=None, timeout=TIMEOUT):
    if requests is None:
        return None
    h = {"User-Agent": UA, "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
         "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"}
    if headers:
        h.update(headers)
    try:
        r = requests.get(url, params=params, headers=h, timeout=timeout,
                         allow_redirects=True)
        # 部分站点（如 zaobao）响应头未声明 charset，requests 误判为
        # ISO-8859-1 导致中文乱码：用内容嗅探的编码覆盖
        try:
            if r.encoding and r.encoding.lower() in ("iso-8859-1",
                                                      "iso8859-1"):
                r.encoding = r.apparent_encoding or "utf-8"
        except Exception:
            pass
        return r
    except Exception:
        return None


def _clean(t):
    if not t:
        return ""
    t = re.sub(r"<[^>]+>", "", t)
    return _h.unescape(re.sub(r"\s+", " ", t)).strip()


def _dedup(items):
    seen, out = set(), []
    for it in items:
        u = it.get("url") or ""
        if not u or u in seen:
            continue
        seen.add(u)
        out.append(it)
    return out


def _rank(query, items):
    ql = (query or "").lower()

    def _score(it):
        s = 0
        tl = (it.get("title") or "").lower()
        dl = (it.get("description") or "").lower()
        if ql and ql in tl:
            s += 3
        if ql and ql in dl:
            s += 1
        return s
    items.sort(key=_score, reverse=True)
    return items


# ---------- 适配器 1：网易新闻站内搜索（可搜历史，聚合外媒译文转载） ----------
def search_netease163(query, limit=6):
    r = _get("https://www.163.com/search", params={"keyword": query})
    if not r or r.status_code != 200:
        return []
    text = r.text
    items, seen = [], set()
    for m in re.finditer(
            r'<a[^>]*href="(https?://www\.163\.com/dy/article/[^"]+)"[^>]*>(.*?)</a>',
            text, re.S):
        link, t = m.group(1), _clean(m.group(2))
        if len(t) < 6:
            continue
        link = link.split("?")[0]
        if link in seen:
            continue
        seen.add(link)
        items.append({"title": t, "url": link, "source": "netease163",
                      "source_name": SOURCE_META["netease163"],
                      "date": "", "description": ""})
        if len(items) >= limit:
            break
    return items


# ---------- 适配器 2：联合早报（热门外媒转载 + 标题过滤） ----------
def search_zaobao(query, limit=6):
    r = _get("https://www.zaobao.com/sitesearch", params={"keyword": query})
    if not r or r.status_code != 200:
        return []
    text = r.text
    items, seen = [], set()
    for m in re.finditer(
            r'href="(/news/[^"]*?story(\d{8})-(\d+))"[^>]*>(.*?)</a>',
            text, re.S):
        link, date8 = m.group(1), m.group(2)
        t = _clean(m.group(4))
        if len(t) < 4 or t in ("中国", "国际", "本地", "财经"):
            continue
        if link in seen:
            continue
        seen.add(link)
        date = "%s-%s-%s" % (date8[:4], date8[4:6], date8[6:8])
        items.append({"title": t,
                      "url": "https://www.zaobao.com" + link,
                      "source": "zaobao", "source_name": SOURCE_META["zaobao"],
                      "date": date, "description": ""})
        if len(items) >= limit:
            break
    return items


# ---------- 适配器 2：观察者网站内搜索 ----------
def search_guancha(query, limit=6):
    r = _get("https://www.guancha.cn/search", params={"keyword": query})
    if not r or r.status_code != 200:
        return []
    text = r.text
    items, seen = [], set()
    for m in re.finditer(
            r'href="(/(?:[A-Za-z]+)/\d{4}_\d{2}_\d{2}_\d+\.shtml)"[^>]*>(.*?)</a>',
            text, re.S):
        link, t = m.group(1), _clean(m.group(2))
        if len(t) < 4 or t in ("中国", "国际", "观察者网", "首页"):
            continue
        if link in seen:
            continue
        seen.add(link)
        dm = re.search(r"/(\d{4})_(\d{2})_(\d{2})_", link)
        date = ""
        if dm:
            date = "%s-%s-%s" % (dm.group(1), dm.group(2), dm.group(3))
        items.append({"title": t,
                      "url": "https://www.guancha.cn" + link,
                      "source": "guancha", "source_name": SOURCE_META["guancha"],
                      "date": date, "description": ""})
        if len(items) >= limit:
            break
    return items


# ---------- 适配器 3/4：France24 / Sixth Tone RSS（直连，关键词过滤） ----------
def _search_rss(rss_url, query, source, source_name, limit=5):
    r = _get(rss_url)
    if not r or r.status_code != 200:
        return []
    text = r.text
    items = []
    for m in re.finditer(r"<item>(.*?)</item>", text, re.S):
        body = m.group(1)
        tm = re.search(r"<title>(.*?)</title>", body, re.S)
        lm = re.search(r"<link>(.*?)</link>", body, re.S)
        dm = re.search(r"<pubDate>(.*?)</pubDate>", body, re.S)
        desc_m = re.search(r"<description>(.*?)</description>", body, re.S)
        t = _clean(tm.group(1)) if tm else ""
        link = (_clean(lm.group(1)) if lm else "")
        desc = (_clean(desc_m.group(1)) if desc_m else "")
        date = ""
        if dm:
            try:
                from email.utils import parsedate_to_datetime
                date = parsedate_to_datetime(dm.group(1)).strftime("%Y-%m-%d")
            except Exception:
                date = ""
        if not t or not link:
            continue
        items.append({"title": t, "url": link, "source": source,
                      "source_name": source_name, "date": date,
                      "description": desc[:200]})
    # 关键词精确匹配优先；无命中时返回最近报道（上层噪音控制会每源保留 1 条）
    ql = query.lower()
    if ql:
        hit = [it for it in items
               if ql in (it["title"] or "").lower()
               or ql in (it["description"] or "").lower()]
        if hit:
            return hit[:limit]
    return items[:limit]


def search_france24(query, limit=5):
    return _search_rss("https://www.france24.com/en/rss", query,
                       "france24", SOURCE_META["france24"], limit)


def search_sixthtone(query, limit=5):
    return _search_rss("https://www.sixthtone.com/rss", query,
                       "sixthtone", SOURCE_META["sixthtone"], limit)


# ---------- 适配器 5：Bing RSS 兜底（format=rss 返回真实 URL，域名过滤等效伪 site:） ----------
def search_bing_fallback(query, source_key=None, limit=6):
    """Bing 搜索结果 RSS 端点（format=rss），返回真实 URL 无需解码。

    实测（2026-09）：cn.bing.com 强制中文本地化，英文查询会被污染为本地站点，
    因此本适配器定位为中文查询兜底；英文源检索由 France24 / Sixth Tone RSS 与
    各站站内搜索承担。指定国外源 key 时以「关键词+源名」查询并按目标域名白名单
    过滤（等效伪 site:）。
    """
    domains = []
    hint = ""
    if source_key and source_key in FOREIGN_DOMAINS:
        domains = FOREIGN_DOMAINS[source_key]
        hint = " " + source_key
    q = query + hint
    r = _get("https://www.bing.com/search", params={"q": q, "format": "rss"})
    if not r or r.status_code != 200:
        return []
    text = r.text
    items = []
    for block in re.findall(r"<item>(.*?)</item>", text, re.S):
        tm = re.search(r"<title>(.*?)</title>", block, re.S)
        lm = re.search(r"<link>(.*?)</link>", block, re.S)
        dm = re.search(r"<description>(.*?)</description>", block, re.S)
        title = _clean(tm.group(1)) if tm else ""
        url = _clean(lm.group(1)) if lm else ""
        desc = _clean(dm.group(1)) if dm else ""
        if not title or not url or _WIKI_BLOCK.search(url):
            continue
        dom = (urlparse(url).netloc or "").lower()
        if domains and not any(d in dom for d in domains):
            continue
        items.append({"title": title, "url": url,
                      "source": source_key or "bing",
                      "source_name": SOURCE_META.get(source_key,
                                                     "Bing 搜索兜底"),
                      "date": "", "description": desc[:200]})
        if len(items) >= limit:
            break
    return items


# ---------- 统一入口 ----------
def search_external(query, sources=None, source_filter=None, limit=8):
    """外部跨源搜索入口（供 /api/web-search、_agent_analyze、/api/text-analysis 使用）。

    参数：
      query         搜索关键词
      sources       要检索的源 key 列表（默认 zaobao/guancha/france24/sixthtone/bing）
      source_filter 指定单个源 key（如 bbc）→ 走 Bing 域名过滤兜底
      limit         每源条数上限
    返回 [{title,url,source,source_name,date,description}]，失败跳过不阻塞。
    """
    query = (query or "").strip()
    if not query:
        return []
    if len(query) > 120:
        query = query[:120]
    cache_key = (query, tuple(sources or []), source_filter, limit)
    cached = _cache_get(cache_key)
    if cached is not None:
        return cached

    if source_filter:
        keys = [source_filter]
    else:
        keys = sources or ["netease163", "zaobao", "guancha", "france24",
                           "sixthtone", "bing"]

    results = []
    for key in keys:
        try:
            if key == "netease163":
                items = search_netease163(query, limit)
            elif key == "zaobao":
                items = search_zaobao(query, limit)
            elif key == "guancha":
                items = search_guancha(query, limit)
            elif key == "france24":
                items = search_france24(query, limit)
            elif key == "sixthtone":
                items = search_sixthtone(query, limit)
            elif key == "bing":
                items = search_bing_fallback(query, None, limit)
            elif key in FOREIGN_DOMAINS:
                items = search_bing_fallback(query, key, limit)
            else:
                items = []
            results.extend(items or [])
        except Exception:
            continue
    results = _dedup(results)
    results = _rank(query, results)
    # 控制噪音：关键词命中（title/desc）全部保留；未命中的每源最多留 1 条作"该源最近报道"参考
    ql = query.lower()
    kept, no_hit_kept = [], {}
    for it in results:
        tl = (it.get("title") or "").lower()
        dl = (it.get("description") or "").lower()
        if ql and (ql in tl or ql in dl):
            kept.append(it)
        else:
            src = it.get("source") or "?"
            if src not in no_hit_kept:
                no_hit_kept[src] = it
    out = kept + list(no_hit_kept.values())
    _cache_set(cache_key, out)
    return out
