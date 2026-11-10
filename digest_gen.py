# -*- coding: utf-8 -*-
"""
东广视「要闻速览」生成器（本地 Qwen 版）
========================================
用途：从线上后端拉取新闻 → 按时段规则筛选聚合去重 → 本地 Ollama Qwen3 精炼成
     中文标题+摘要 → 写出 digest_cache/digest_YYYYMMDD_HH.json 缓存文件。
      缓存随仓库部署后，线上 /api/news/digest 直接读缓存返回（cached=true）。

依赖：本机 Ollama（默认 http://127.0.0.1:11435，模型 qwen3:4b）
用法：
  python digest_gen.py                     # 生成全部时段
  python digest_gen.py --hours 8,12        # 只生成指定时段
  python digest_gen.py --hours 8 --dry     # 只打印不写盘
"""
import argparse
from datetime import datetime, timedelta, timezone
import json
import os
import re
import sys
import time
import urllib.parse
import urllib.request

API_BASE = os.environ.get('OVC_API_BASE', 'https://ovc-backend-uaant.faable.link')
QWEN_URL = os.environ.get('QWEN_URL', 'http://127.0.0.1:11435/api/generate')
QWEN_MODEL = os.environ.get('QWEN_MODEL', 'qwen3:4b')
CACHE_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'digest_cache')

# 与 server.py 的 _DIGEST_HOUR_RULES 保持一致
HOUR_RULES = {
    6:  {'label': '早安·民生文体速览', 'cats': ['社会', '生活', '经济', '体育', '科技', '人文', '娱乐']},
    17: {'label': '晚间·民生文体速览', 'cats': ['社会', '生活', '经济', '体育', '科技', '人文', '娱乐']},
    8:  {'label': '早间·时事速览', 'cats': ['时事', '国际']},
    12: {'label': '午间·时事速览', 'cats': ['时事', '国际']},
    18: {'label': '晚间·时事速览', 'cats': ['时事', '国际']},
    22: {'label': '夜间·时事速览', 'cats': ['时事', '国际']},
    13: {'label': '全球文体科技消费速览', 'cats': ['人文', '体育', '科技', '娱乐', '生活']},
    10: {'label': '财经速览', 'cats': ['经济']},
    15: {'label': '财经速览', 'cats': ['经济']},
    21: {'label': '财经速览', 'cats': ['经济']},
    19: {'label': '深度·社会观察速览', 'cats': ['社会']},
    20: {'label': '时政·产经国际速览', 'cats': ['时事', '国际', '经济']},
}

NOISE_SUMMARY = ('点击查看原文', '原文链接', '阅读原文', '查看更多', '详见')


def http_json(url, timeout=60):
    req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0 (digest-gen)'})
    return json.loads(urllib.request.urlopen(req, timeout=timeout).read().decode('utf-8'))


def fetch_news(pages=8, per_page=50):
    """分页拉取线上新闻，返回去掉重复 id 的列表（按 created_at 倒序）。"""
    out, seen = [], set()
    for p in range(1, pages + 1):
        url = '%s/api/news?page=%d&per_page=%d' % (API_BASE, p, per_page)
        try:
            d = http_json(url)
        except Exception as e:
            print('  [warn] 拉取第 %d 页失败: %s' % (p, e))
            break
        rows = d.get('news') or []
        if not rows:
            break
        before = len(out)
        for r in rows:
            if r.get('id') not in seen:
                seen.add(r.get('id'))
                out.append(r)
        # 服务端 per_page 固定 20，停止条件用「本页无新增」而非条数比较
        if len(out) == before:
            break
    out.sort(key=lambda x: -(x.get('created_at') or 0))
    return out


def clean_text(s, limit=200):
    t = (s or '').strip()
    t = re.sub(r'<[^>]*>', ' ', t)
    t = re.sub(r'https?://\S+', ' ', t)
    t = re.sub(r'[<>&>＞]+', ' ', t)
    t = re.sub(r'\s+', ' ', t).strip()
    return t[:limit]


def usable(r, days=7, now=None):
    now = now or time.time()
    ts = r.get('created_at') or 0
    if ts < now - days * 86400:
        return False
    title = (r.get('title') or '').strip()
    if not title:
        return False
    if any(k in title for k in ('新闻速递', 'RSS', '订阅源')):
        return False
    return True


def bigrams(t):
    norm = re.sub(r"[\s\u3000，。；：、！？“”‘’（）【】《》·—…,.!?;:()\[\]{}'\"\-]", '', (t or '')).lower()
    return set(norm[i:i + 2] for i in range(len(norm) - 1)) if len(norm) >= 2 else set()


def cluster(records, sim=0.5):
    """标题 bigram Jaccard 聚类，同一事件归组，保留组内信息量最大的代表。"""
    groups = []
    for rec in records:
        bg = rec['bg']
        hit = None
        for g in groups:
            if not g['bg'] or not bg:
                continue
            u = len(bg | g['bg'])
            if u and len(bg & g['bg']) / u >= sim:
                hit = g
                break
        if hit:
            hit['recs'].append(rec)
            hit['bg'] |= bg
        else:
            groups.append({'bg': set(bg), 'recs': [rec]})
    return groups


def pick_representative(group):
    recs = group['recs']
    zh = [x for x in recs if re.search(r'[\u4e00-\u9fff]', x['title'])]
    pool = zh or recs
    rep = max(pool, key=lambda x: (len(x['summary']), x['created_at']))
    sources = []
    for x in recs:
        if x['source'] and x['source'] not in sources:
            sources.append(x['source'])
    rep = dict(rep)
    rep['sources'] = ' / '.join(sources[:3])
    return rep


def qwen(prompt, num_predict=1200, timeout=300):
    body = json.dumps({
        'model': QWEN_MODEL, 'prompt': prompt, 'stream': False, 'think': False, 'format': 'json',
        'options': {'num_ctx': 12288, 'num_predict': num_predict, 'temperature': 0.25},
    }).encode('utf-8')
    req = urllib.request.Request(QWEN_URL, data=body, headers={'Content-Type': 'application/json'})
    r = json.loads(urllib.request.urlopen(req, timeout=timeout).read().decode('utf-8'))
    return r.get('response', '')


SYS_PROMPT = (
    '你是资深中文新闻编辑，为「要闻速览」卡片撰写条目。硬性要求：\n'
    '1) 标题：一行，18-32 个汉字，写清主体与事件核心，不写日期、不用书名号、不加【】；\n'
    '2) 摘要：一行，45-70 个汉字，讲清发生了什么与关键数字/结论，不重复标题原句；\n'
    '3) 同一条素材只输出一条；不要编造素材里没有的事实与数字；\n'
    '4) 严禁空摘要，严禁输出“新闻源”“外媒要闻”等占位词；\n'
    '5) 只输出 JSON：{"items":[{"title":"...","summary":"..."}]}，禁止 JSON 以外的任何文本。'
)


def build_materials(records, hour, max_n=12):
    """按时段规则筛素材，返回聚类后的代表条目（供 AI 精炼）。"""
    rule = HOUR_RULES[hour]
    cats = rule_cats(hour)
    recs = []
    for r in records:
        if not usable(r):
            continue
        if r.get('category') not in cats:
            continue
        title = clean_text(r.get('title'), 120)
        summary = clean_text(r.get('summary'), 240)
        if any(k in summary for k in NOISE_SUMMARY):
            summary = ''
        src = clean_text(r.get('author_name') or '', 16) or '新闻源'
        recs.append({'id': r.get('id'), 'title': title, 'summary': summary,
                     'category': r.get('category') or '', 'source': src,
                     'created_at': r.get('created_at') or 0, 'bg': bigrams(title)})
    groups = cluster(recs)
    reps = [pick_representative(g) for g in groups]
    reps.sort(key=lambda x: -x['created_at'])
    return rule, reps[:max_n]


def gen_hour(records, hour, limit=8, dry=False):
    rule, reps = build_materials(records, hour)
    if not reps:
        print('  [skip] hour=%d 无可用素材' % hour)
        return None
    lines = []
    for i, r in enumerate(reps):
        lines.append('[%d] 来源:%s 分类:%s 标题:%s 摘要:%s' % (
            i, r['source'], r['category'], r['title'], r['summary'] or '（无摘要，需据标题概括）'))
    prompt = SYS_PROMPT + '\n\n原始素材：\n' + '\n'.join(lines) + '\n\n请输出 %d 条速览（若素材不足 %d 条则按实际条数）。' % (limit, limit)
    t0 = time.time()
    try:
        raw = qwen(prompt)
        data = json.loads(raw)
        items = data.get('items') or []
    except Exception as e:
        print('  [warn] hour=%d AI 生成失败: %s' % (hour, e))
        return None
    digest = []
    for i, it in enumerate(items[:limit]):
        title = clean_text(it.get('title'), 60)
        summary = clean_text(it.get('summary'), 120)
        if not title or not summary:
            continue
        src_rec = reps[i] if i < len(reps) else reps[0]
        digest.append({
            'id': src_rec['id'], 'title': title, 'summary': summary,
            'category': src_rec['category'], 'source': src_rec['sources'] or src_rec['source'],
            'created_at': src_rec['created_at'],
        })
    print('  [ok] hour=%2d %-14s %d 条  耗时 %.1fs' % (hour, rule['label'], len(digest), time.time() - t0))
    payload = {'hour': hour, 'label': rule['label'], 'digest': digest, 'generated_at': time.time(),
               'generator': 'qwen3:4b@local'}
    if dry:
        for it in digest:
            print('       ·', it['title'], '｜', it['summary'][:40], '｜', it['source'])
        return payload
    os.makedirs(CACHE_DIR, exist_ok=True)
    p = os.path.join(CACHE_DIR, 'digest_%s_%02d.json' % (datetime.now(timezone(timedelta(hours=8))).strftime('%Y%m%d'), hour))
    with open(p, 'w', encoding='utf-8') as f:
        json.dump(payload, f, ensure_ascii=False, indent=1)
    print('       写入', os.path.basename(p))
    return payload


# 线上新闻实际分类：时事/财经/娱乐/科技/环境/体育/人文；旧分类名需映射
CAT_ALIAS = {'经济': '财经', '社会': '时事', '生活': '人文', '国际': '时事', '国际新闻': '时事'}


def rule_cats(hour):
    """时段规则分类 → 线上真实分类集合（已做别名映射与去重）。"""
    out = []
    for c in HOUR_RULES[hour]['cats']:
        cc = CAT_ALIAS.get(c, c)
        if cc not in out:
            out.append(cc)
    return set(out or ['时事'])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--hours', default='')
    ap.add_argument('--pages', type=int, default=8)
    ap.add_argument('--limit', type=int, default=8)
    ap.add_argument('--dry', action='store_true')
    a = ap.parse_args()
    hours = [int(x) for x in a.hours.split(',') if x.strip().isdigit()] or sorted(HOUR_RULES.keys())
    print('拉取线上新闻 ...')
    records = fetch_news(pages=a.pages)
    print('获得 %d 条新闻（去重后），最新 %s' % (
        len(records), time.strftime('%m-%d %H:%M', time.localtime(records[0]['created_at'])) if records else '-'))
    ok = 0
    for h in hours:
        if h not in HOUR_RULES:
            print('  [skip] 无该时段规则:', h)
            continue
        if gen_hour(records, h, limit=a.limit, dry=a.dry):
            ok += 1
    print('\n完成 %d/%d 个时段' % (ok, len(hours)))


if __name__ == '__main__':
    main()
