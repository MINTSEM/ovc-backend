# -*- coding: utf-8 -*-
"""
翱翔鸟 PeaceNews —— 一期 RSS 源池抓取调度模块
====================================================================

职责
----
1. 从 source-pool.json 读取源池，过滤 status_code == "ok" 的直连源
2. 按「分类 + 源配置」生成抓取任务队列
3. 常驻后台线程定时轮询（默认 5 分钟一轮），抓取后写入 bird.db 的 news 表
   （复用现有表结构；id 采用 news_<8位hex>；title / content / category 必填）
4. 入库前做标题去重（同标题 24 小时内不重复入库）
5. 单源超时 15s 跳过，失败不阻塞其他源，并保留每个源的最近状态
6. 对外提供 /api/admin/scheduler/status 与 /api/admin/scheduler/sources 管理接口

设计约束
--------
* 不新增数据库表、不修改 news 表结构，完全复用现有列。
* 不直接 import server.py，避免循环依赖；由 server.py 在启动时调用
  ``register_routes(app, admin_required)`` 与 ``start()`` 完成挂载。
* 运行期源注册表写入 scheduler-sources.json（首次由 source-pool.json 播种），
  便于后台通过 API 增删改而不破坏原始归档文档。
"""

import json
import logging
import os
import re
import sqlite3
import threading
import time
import uuid
from collections import OrderedDict, deque
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import urljoin, urlparse

import requests
import urllib3
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

logger = logging.getLogger("peacenews.scheduler")
if not logger.handlers:
    _h = logging.StreamHandler()
    _h.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] scheduler: %(message)s"))
    logger.addHandler(_h)
    logger.setLevel(logging.INFO)

# ----------------------------------------------------------------------
# 路径与常量
# ----------------------------------------------------------------------
BASE_DIR = Path(__file__).resolve().parent  # 扁平化后位于项目根
CONFIG_DIR = BASE_DIR                        # 扁平化后配置文件放根目录
SOURCE_POOL_FILE = CONFIG_DIR / "source-pool.json"        # 归档源池（只读）
SOURCES_FILE = CONFIG_DIR / "scheduler-sources.json"      # 运行期源注册表（可读写）
BIRD_DB = BASE_DIR / "bird.db"

# ======================================================================
# 新闻自动分类词典：按标题 + 段落内容关键词匹配前台标准分类
# 权重：标题命中 +2，正文命中 +1；得分 >= 阈值即胜出
# 无命中时返回 ''，由调用方决定兜底策略
# ======================================================================
_AUTO_CATEGORY_KEYWORDS = {
    "国际": ["外交部", "外长", "联合国", "欧盟", "北约", "俄罗斯", "乌克兰", "美国", "白宫", "特朗普", "拜登",
             "普京", "以色列", "巴勒斯坦", "加沙", "伊朗", "韩国", "日本", "朝鲜", "印度", "东盟", "非盟",
             "G7", "G20", "峰会", "大使", "使馆", "制裁", "关税战", "地缘", "中东", "俄乌", "边境", "移民",
             "巴黎", "伦敦", "东京", "华盛顿", "莫斯科", "基辅", "首尔", "平壤", "新德里", "国际法院", "世卫",
             "国际货币基金组织", "世界银行"],
    "时事": ["国务院", "总理", "政协", "人大", "两会", "政策", "发改委", "中央", "部委", "发布", "部署",
             "贯彻落实", "传达", "会议", "决定", "通知", "意见", "规划", "十四五", "政府", "政务", "民生",
             "改革", "治理", "执法", "监管", "法规", "条例", "草案", "全国", "试点", "调研组", "新闻发布会",
             "白皮书", "强军", "国防"],
    "经济": ["股市", "A股", "港股", "美股", "纳斯达克", "道指", "标普", "基金", "银行", "央行", "降准", "降息",
             "利率", "汇率", "人民币", "美元", "欧元", "通胀", "CPI", "PPI", "GDP", "经济", "企业",
             "公司", "财报", "营收", "利润", "上市", "IPO", "融资", "投资", "并购", "收购", "产业链", "供应链",
             "制造业", "出口", "进口", "贸易", "关税", "消费", "零售", "房价", "楼市", "地产", "房企", "债券",
             "黄金", "大宗商品", "原油", "石油", "能源价格", "就业", "失业率", "补贴", "减税", "财政"],
    "科技": ["AI", "人工智能", "大模型", "ChatGPT", "OpenAI", "谷歌", "微软", "苹果", "华为", "芯片", "半导体",
             "处理器", "GPU", "英伟达", "高通", "英特尔", "软件", "硬件", "互联网", "5G", "6G", "通信", "卫星",
             "航天", "火箭", "飞船", "空间站", "嫦娥", "火星", "量子", "机器人", "自动驾驶", "新能源", "电池",
             "光伏", "风电", "电动车", "汽车", "手机", "数码", "操作系统", "开源", "编程", "算法", "数据",
             "云计算", "区块链", "元宇宙", "VR", "AR", "专利", "研发", "实验室", "科学家", "科研"],
    "体育": ["足球", "篮球", "世界杯", "奥运会", "亚运会", "亚残运会", "冬运会", "全运会", "英超", "西甲", "德甲", "意甲", "法甲", "中超", "中甲",
             "CBA", "NBA", "欧冠", "欧联", "世预赛", "亚预赛", "冠军", "冠军杯", "联赛", "决赛", "半决赛", "四强", "八强", "锦标赛", "世锦赛", "公开赛", "大师赛", "巡回赛",
             "运动员", "球员", "教练", "主帅", "主教练", "球队", "俱乐部", "国家队", "阵容", "首发", "替补", "上场",
             "进球", "射门", "助攻", "比分", "金牌", "银牌", "铜牌", "奖牌", "国足", "男篮", "女篮", "女排", "国乒", "国羽", "网球", "高尔夫",
             "F1", "大奖赛", "马拉松", "田径", "游泳", "体操", "羽毛球", "乒乓球", "电竞", "转会", "退役", "复出", "伤病", "因伤",
             "比赛", "赛事", "赛程", "小组赛", "淘汰赛", "资格赛", "预选赛", "热身赛", "友谊赛", "不败", "连胜", "连败", "晋级", "出线", "夺冠", "卫冕", "开门红", "种子", "大满贯", "积分榜", "排名", "绝杀", "逆转", "大胜", "战平", "爆冷"],
    "人文": ["博物馆", "考古", "文物", "遗址", "历史", "文化", "非遗", "传统", "书法", "绘画", "艺术", "展览",
             "文学", "小说", "诗歌", "散文", "作家", "学者", "研究", "学术", "大学", "教育", "学校", "教师",
             "学生", "考试", "高考", "图书馆", "出版", "图书", "阅读", "哲学", "宗教", "民族", "民俗", "方言", "国学"],
    "娱乐": ["电影", "票房", "上映", "电视剧", "综艺", "节目", "演员", "导演", "明星", "歌手", "演唱会", "专辑",
             "音乐", "歌曲", "颁奖", "奥斯卡", "戛纳", "威尼斯", "春晚", "选秀", "偶像", "粉丝", "剧组", "拍摄",
             "首映", "预告片", "制片", "娱乐", "八卦", "网红", "直播", "主播", "动漫", "漫画", "动画"],
    "生活": ["健康", "医疗", "医院", "医生", "疫苗", "疾病", "养生", "饮食", "食品", "安全", "天气", "气象",
             "台风", "暴雨", "地震", "灾害", "救援", "交通", "出行", "旅游", "景区", "假期", "酒店", "美食",
             "菜价", "超市", "购物", "快递", "物流", "家居", "装修", "家电", "燃气", "水费", "电费", "物业",
             "社区", "街道", "垃圾分类", "宠物", "健身", "睡眠", "心理", "育儿", "养老", "社保", "医保", "公积金",
             "体质", "体检", "血脂", "脑梗", "猝死", "亚健康", "体育代表团", "代表团"],
    "环境": ["气候", "温室气体", "碳中和", "碳达峰", "碳排放", "污染", "空气", "水质", "土壤", "生态", "生物多样性",
             "森林", "湿地", "海洋", "冰川", "极端天气", "高温", "干旱", "洪水", "海平面", "环保组织", "绿电", "清洁能源",
             # 正向扩充：环保/生态修复/新能源/气候行动（避免环境分类只剩地震等灾难负面）
             "环保", "生态修复", "植树造林", "国土绿化", "荒漠化", "治沙", "固沙", "湿地保护", "自然保护区", "国家公园",
             "野生动植物", "候鸟", "节能减排", "碳市场", "碳交易", "碳捕集", "零碳", "低碳", "净零", "绿色转型",
             "绿色能源", "可再生能源", "氢能", "储能", "光伏治沙", "绿色出行", "节能", "无废"],
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


# 强生活词：标题命中即应归入"生活"（健康/体质/体检/脑梗/体育代表团等民生日常），
# 置于强体育/强社会之前，避免"中国体育代表团…辟谣"等被体育/社会强词抢走
_LIFE_STRONG_WORDS = (
    "体质", "体检", "血脂", "脑梗", "猝死", "亚健康", "体育代表团", "养生",
    "睡眠质量", "心理健康", "疫苗接种", "慢性病", "糖尿病", "高血压", "流感", "急救",
)

# 强经济词：标题命中即应归入"经济"，防止股票/财经新闻被国际/时事关键词抢走
_ECON_STRONG_WORDS = (
    "股市", "A股", "港股", "美股", "纳斯达克", "道指", "标普", "基金", "央行", "降准", "降息",
    "利率", "汇率", "财报", "营收", "利润", "IPO", "融资", "并购", "债券", "黄金", "原油",
    "股票", "券商", "涨停", "跌停", "收盘", "开盘", "指数", "板块", "牛市", "熊市", "股价", "大盘", "个股",
)

# 强体育词：标题命中即应归入"体育"，防止体育赛事/运动员新闻被国际/时事等关键词抢走
_SPORT_STRONG_WORDS = (
    "足球", "篮球", "世界杯", "奥运会", "亚运会", "亚残运会", "冬运会", "全运会", "英超", "西甲", "德甲", "意甲", "法甲", "中超", "中甲",
    "CBA", "NBA", "欧冠", "欧联", "世预赛", "亚预赛", "世锦赛", "公开赛", "大师赛", "巡回赛", "大奖赛",
    "国足", "男篮", "女篮", "女排", "国乒", "国羽", "比赛", "赛事", "赛程", "小组赛", "淘汰赛", "资格赛", "预选赛",
    "热身赛", "友谊赛", "连胜", "连败", "晋级", "出线", "夺冠", "卫冕", "开门红", "大满贯", "积分榜",
    "绝杀", "逆转", "大胜", "战平", "爆冷", "进球", "射门", "助攻", "比分", "奖牌", "金牌", "银牌", "铜牌", "运动员", "球员", "主帅", "教练",
)

# 强社会词：标题命中即应归入"社会"，防止真实社会新闻（通报/立案/辟谣/维权等）被国际/时事等兜底大类抢走
_SOCIAL_STRONG_WORDS = (
    "警方", "警方通报", "民警", "公安", "刑拘", "刑事拘留", "逮捕", "落网", "嫌疑人", "诈骗", "诈骗团伙", "电信诈骗",
    "盗窃", "抢劫", "故意伤害", "命案", "遇害", "坠楼", "溺亡", "车祸", "交通事故", "火灾", "爆炸", "坍塌", "中毒",
    "遇难", "失联", "被困", "搜救", "消防", "救援", "辟谣", "网传", "造谣", "传谣",
    "讨薪", "欠薪", "劳动仲裁", "霸凌", "校园暴力", "食品安全", "消费维权", "维权",
    "走失", "寻人", "拾金不昧", "见义勇为", "好人好事",
    "通报称", "官方通报", "通报曝光", "通报批评", "立案调查", "纪委监委", "调查组",
    "举报", "投诉", "纠纷", "曝光", "当事人", "涉事", "目击者", "监控画面", "打人", "袭警", "拐卖", "性侵",
)

# 国外地名/主体强词：标题命中即归"国际"（时事）。事件发生地/主体在国外（苏丹、美国、国外地名等）不得落入社会。
# 放置于强体育/强经济判断之后，避免"美股""NBA 洛杉矶"等财经/体育新闻被误抢。
_FOREIGN_PLACES = (
    "美国", "美方", "美军", "白宫", "特朗普", "拜登", "苏丹", "南苏丹", "喀土穆", "俄罗斯", "乌克兰",
    "韩国", "朝鲜", "印度", "日本", "日方", "伊朗", "以色列", "巴勒斯坦", "加沙", "委内瑞拉",
    "洛杉矶", "加利福尼亚", "加州", "纽约", "芝加哥", "旧金山", "波士顿", "西雅图",
    "华盛顿", "莫斯科", "基辅", "首尔", "平壤", "东京", "大阪", "巴黎", "伦敦", "柏林", "马德里", "罗马",
    "开罗", "内罗毕", "迪拜", "多哈", "利雅得", "新加坡", "曼谷", "雅加达", "马尼拉", "河内", "伊斯兰堡",
    "德黑兰", "巴格达", "大马士革", "安曼", "贝鲁特", "特拉维夫", "耶路撒冷", "安卡拉", "伊斯坦布尔", "雅典",
    "维也纳", "布鲁塞尔", "日内瓦", "渥太华", "多伦多", "温哥华", "墨西哥城", "圣保罗", "里约热内卢",
    "布宜诺斯艾利斯", "堪培拉", "悉尼", "墨尔本", "惠灵顿", "金边", "仰光", "蒙古国",
    "阿富汗", "伊拉克", "叙利亚", "也门", "沙特", "沙特阿拉伯", "卡塔尔", "阿联酋", "土耳其", "埃及",
    "南非", "尼日利亚", "肯尼亚", "埃塞俄比亚", "澳大利亚", "新西兰", "加拿大", "墨西哥", "巴西", "阿根廷",
    "智利", "秘鲁", "哥伦比亚", "古巴", "西班牙", "意大利", "德国", "法国", "英国", "荷兰", "瑞典", "挪威",
    "芬兰", "丹麦", "波兰", "奥地利", "瑞士", "比利时", "葡萄牙", "希腊", "白俄罗斯", "格鲁吉亚",
    "哈萨克斯坦", "乌兹别克斯坦", "吉尔吉斯斯坦", "塔吉克斯坦", "塞尔维亚", "克罗地亚", "罗马尼亚",
    "保加利亚", "匈牙利", "捷克", "斯洛伐克", "斯洛文尼亚", "立陶宛", "拉脱维亚", "爱沙尼亚", "亚美尼亚",
    "阿塞拜疆", "巴林", "科威特", "阿曼", "约旦", "黎巴嫩", "塞浦路斯", "马尔代夫", "斯里兰卡", "孟加拉国",
    "巴基斯坦", "尼泊尔", "不丹", "缅甸", "老挝", "柬埔寨", "越南", "菲律宾", "马来西亚", "印度尼西亚",
    "文莱", "东帝汶", "巴布亚新几内亚", "斐济", "索马里", "利比亚", "阿尔及利亚", "摩洛哥", "突尼斯",
    "加纳", "坦桑尼亚", "乌干达", "赞比亚", "津巴布韦", "莫桑比克", "安哥拉", "刚果", "喀麦隆",
    "科特迪瓦", "马里", "布基纳法索", "尼日尔", "乍得", "吉布提", "卢旺达", "布隆迪", "马达加斯加",
    "毛里求斯", "塞内加尔", "几内亚", "塞拉利昂", "多哥", "贝宁", "加蓬", "爱尔兰", "卢森堡", "冰岛",
    "马耳他", "黑山", "北马其顿", "海地", "牙买加", "巴拿马", "哥斯达黎加", "危地马拉", "洪都拉斯",
    "萨尔瓦多", "尼加拉瓜", "厄瓜多尔", "玻利维亚", "巴拉圭", "乌拉圭", "圭亚那", "巴哈马", "巴巴多斯",
    "海外", "国外", "国际社会",
)

# 国内政治/纪律/政府事务强词：标题命中即归"时事"。国内政治、纪律、政府事务（开除公职、纪委、监委、
# 免职、双开、审查调查等）不得落入社会。
_DOMESTIC_POLITICS = (
    "开除公职", "开除党籍", "免职", "双开", "政务处分", "党纪政务处分", "纪委", "监委", "监察",
    "审查调查", "立案审查", "被查", "落马", "问责", "处分", "撤职", "降职", "停职",
    "公职人员", "党员干部", "领导干部", "违纪", "违法违纪", "反腐", "廉政", "廉洁",
    "巡视", "巡察", "派驻", "中纪委", "中央纪委", "国家监委", "省纪委", "市纪委", "县纪委",
    "省监委", "市监委", "县监委", "纪律处分", "组织处理",
)

# 政府-企业合作签约/战略合作类新闻：标题同时命中签约动作词与政府机构词 → 过滤不展示
# （如"浪潮集团与枣庄市人民政府签署合作协议"，属于政务活动软文，不入新闻流）
_GOV_SIGN_ACTION = (
    "签署合作协议", "签订合作协议", "签署战略合作", "签订战略合作", "战略合作协议",
    "签约仪式", "达成合作", "合作签约", "合作框架协议", "框架合作协议",
    "签署合作备忘录", "签订合作备忘录", "签署合作框架",
)
_GOV_AGENCY_WORDS = (
    "人民政府", "市政府", "省政府", "区政府", "县政府", "政府",
    "发改委", "工信部", "商务部", "财政部", "住建部", "国资委", "交通运输部",
    "农业农村部", "文化和旅游部", "文旅厅", "教育厅", "科技厅", "省委", "县委", "镇委",
)


def _is_gov_sign_news(title):
    """政府-企业合作签约/战略合作类新闻判定：命中即不应展示。"""
    if not title:
        return False
    t = str(title).strip()
    if not any(k in t for k in _GOV_SIGN_ACTION):
        return False
    if any(k in t for k in _GOV_AGENCY_WORDS):
        return True
    # 形如「XX市/省/区/县人民政府」的显式政府机构
    if re.search(r'[一-龥]{2,10}?(?:市|省|区|县)人民政府', t):
        return True
    return False


# 无实际新闻内容/地区政府活动软文类标题过滤（命中即不入库）：
# - 直播海报、直播预告/回放入口、节目单等栏目壳/宣传物料
# - 「乡村行/调研行/蹲点记」等走基层系列专题
# - 「XX地举办/举行/开幕XX大会/交流会/论坛/峰会/博览会/大赛」等地区政府活动软文
_NON_NEWS_RE = re.compile(
    r'(直播海报|直播预告|直播回放|直播入口|观看直播|节目单|开播提示|直播访谈)'
    r'|(乡村行|调研行|蹲点记|基层行)'
    r'|(举办|举行|开幕|启动|召开|拉开帷幕|正式启动).{0,18}(大会|交流会|论坛|峰会|洽谈会|博览会|推介会|大赛|活动周|启动仪式|发布会|庙会|文化节|座谈会|研讨会|推进会|部署会|总结会|工作会|招商会|对接会)'
    r'|(大会|交流会|论坛|峰会|洽谈会|博览会|推介会|大赛|启动仪式|座谈会|研讨会|推进会|部署会).{0,12}(举办|举行|开幕|启动|召开)'
)


def _is_non_news_title(title):
    """判定是否为应过滤的非新闻/地区政务软文标题。"""
    if not title:
        return True
    t = str(title).strip()
    if len(t) < 4:
        return True
    return bool(_NON_NEWS_RE.search(t))


# 数码评测/促销广告特征：命中后禁止归入"生活"（防止数码源/评测软文污染生活分类）
# 中文侧重评测/种草/促销，英文侧重 deal/review/gift guide/best ... for 等消费导购标题
_DIGITAL_AD_RE = re.compile(
    r"(评测|开箱|上手体验|种草|好物|安利|数码|智能手表|降噪耳机|真无线|"
    r"\b(deals?|discounts?|review|reviews|gift guide|the best|best [a-z ]{2,30}?(for|of) |"
    r"clearance|on sale|prime day|black friday|cyber monday|top 10|best products)\b)",
    re.I,
)


def auto_classify_news(title, content=""):
    """按标题 + 正文关键词自动分类；返回标准分类名（无命中返回 ''）"""
    title_txt = (title or "").strip()
    body_txt = (content or "")[:2000]
    best_cat, best_score = "", 0
    for cat, kws in _AUTO_CATEGORY_KEYWORDS.items():
        score = 0
        for kw in kws:
            if kw and kw in title_txt:
                score += 2
            elif kw and body_txt and kw in body_txt:
                score += 1
        if score > best_score:
            best_score, best_cat = score, cat
    if best_score >= 2:
        # 强生活词优先：命中即归生活（健康/体质/体检/脑梗/体育代表团等），避免被体育/社会强词抢走
        if any(w in title_txt for w in _LIFE_STRONG_WORDS):
            return "生活"
        # 强经济词优先：命中即归经济，避免股票/财经新闻被误分到国际/时事
        if best_cat in ("国际", "时事") and any(w in title_txt for w in _ECON_STRONG_WORDS):
            return "经济"
        # 强体育词优先：命中即归体育，避免体育赛事被国际/时事/生活/人文抢走
        if any(w in title_txt for w in _SPORT_STRONG_WORDS):
            return "体育"
        # 国外地名/主体强词：事件发生地/主体在国外 → 归国际（时事），不得落入社会
        if any(w in title_txt for w in _FOREIGN_PLACES):
            return "国际"
        # 国内政治/纪律/政府事务强词：归时事，不得落入社会
        if any(w in title_txt for w in _DOMESTIC_POLITICS):
            return "时事"
        # 强社会词：抢国际/时事兜底大类，让真实社会新闻归入社会
        if best_cat in ("国际", "时事") and any(w in title_txt for w in _SOCIAL_STRONG_WORDS):
            return "社会"
        return best_cat
    return ""


# 无信息量标题模式：短标题且以“汇总/速览/快讯/简报/速递/启幕/来了/官宣/出炉/来袭/开启”等收尾，
# 本身不含主体+事件，需要从正文提炼
_BLAND_TITLE_RE = re.compile(r"^.{1,12}?(汇总|速览|快讯|简报|周报|速递|直击|启幕|来了|官宣|出炉|上新|来袭|开启|进行时)$")
# 正文首段常见来源导语前缀（XX电/XX社电/中新网…/原标题：/原文标题：/题：等）
_LEAD_RE = re.compile(
    r"^(?:【?[^【】\n]{0,24}?(?:电|讯|社电|分社电)】?\s*|"
    r"中新[^，。；\n]{0,20}?[电讯]?\s*|"
    r"原标题[:：]\s*|原文标题[:：]\s*|题[:：]\s*|编者按[:：]\s*|"
    r"快讯[:：]\s*|本报讯\s*|本网[^，。；\n]{0,10}?[电讯]?\s*|"
    r"(?:本报|本台|央视|新华社)?记者[^，。；\n]{0,15}?\s*|"
    r"[0-9０-９]{1,4}年[0-9０-９]{1,2}月[0-9０-９]{1,2}日\s*)"
)


def refine_title(title, content=""):
    """对无信息量标题（如“XX汇总/XX启幕/XX速览”），从正文首段提炼含主体+事件的标题。

    返回空串表示无需改写（原标题保留）。
    """
    t = (title or "").strip()
    if not t:
        return ""
    body = (content or "").strip()
    if not body:
        return ""
    if len(t) <= 15 and _BLAND_TITLE_RE.search(t) and len(body) >= 30:
        lines = [ln.strip() for ln in re.split(r"[\n\r]+", body) if ln.strip()]
        for ln in lines:
            cand = _LEAD_RE.sub("", ln).strip(" 　。；;、,:：")
            cand = re.split(r"(?<=[。！？])", cand)[0]
            cand = cand.strip(" 　。；;、,:：")
            if len(cand) >= 10:
                cand = cand[:60].rstrip("。")
                if len(cand) >= 10:
                    return cand + "。"
        flat = re.sub(r"\s+", "", body)
        flat = _LEAD_RE.sub("", flat)
        if len(flat) >= 10:
            return flat[:60].rstrip("。") + "。"
    return ""


FETCH_TIMEOUT = 15                # 单源超时（秒）
DEFAULT_INTERVAL_MIN = 10         # 默认轮询间隔（分钟），取值范围 5~15
MIN_INTERVAL_MIN = 5
MAX_INTERVAL_MIN = 15
SCHEDULER_TICK = 30               # 调度循环心跳（秒）
MAX_WORKERS = 6                   # 并发抓取线程数
PER_SOURCE_LIMIT = 15             # 单源单轮最多入库条数
DEDUP_WINDOW_SEC = 24 * 3600      # 标题去重窗口：24 小时
MAX_ARTICLE_AGE_SEC = 30 * 86400  # 早于 30 天的条目视为历史归档，不入库（保障"近30天"筛选有数据）
STATUS_HISTORY = 30               # 每个源保留的最近执行记录条数

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36")

# ----------------------------------------------------------------------
# news_config 全局配置（与后台排版设置共用同一张表；白名单与 server.py 保持同步）
# 可选键：scheduler_enabled(0/1) / scheduler_interval_min(5~15) / scheduler_fetch_timeout(5~60)
# ----------------------------------------------------------------------
SCHEDULER_CONFIG_KEYS = ("scheduler_enabled", "scheduler_interval_min", "scheduler_fetch_timeout")
_GLOBAL_CONFIG_CACHE = {"at": 0.0, "cfg": {}}


def global_config(force=False):
    """读取 news_config 中的全局调度配置；读取失败时回退到模块默认值。"""
    now = time.time()
    if not force and now - _GLOBAL_CONFIG_CACHE["at"] < 30:
        return _GLOBAL_CONFIG_CACHE["cfg"]
    cfg = {"scheduler_enabled": "1",
           "scheduler_interval_min": str(DEFAULT_INTERVAL_MIN),
           "scheduler_fetch_timeout": str(FETCH_TIMEOUT)}
    try:
        conn = sqlite3.connect(str(BIRD_DB))
        conn.row_factory = sqlite3.Row
        for r in conn.execute("SELECT key, value FROM news_config"):
            if r["key"] in cfg:
                cfg[r["key"]] = str(r["value"])
        conn.close()
    except Exception as ex:
        logger.warning("读取 news_config 全局调度配置失败：%s", ex)
    _GLOBAL_CONFIG_CACHE.update({"at": now, "cfg": cfg})
    return cfg


def _int_cfg(cfg, key, default, lo, hi):
    try:
        return max(lo, min(hi, int(cfg.get(key, default))))
    except (TypeError, ValueError):
        return default


def effective_timeout(src):
    """单源超时：源自身配置 > news_config 全局配置 > 模块默认（15s）"""
    t = src.get("timeout_s") if isinstance(src, dict) else None
    if not t:
        t = global_config().get("scheduler_fetch_timeout")
    try:
        t = int(t)
    except (TypeError, ValueError):
        t = FETCH_TIMEOUT
    return max(5, min(60, t))

# 前台分类胶囊栏使用的标准分类（顺序与页面一致）
CANONICAL_CATEGORIES = ["国际", "社会", "经济", "体育", "科技", "人文",
                        "娱乐", "生活", "环境", "时事", "游戏社群"]

# 分类别名归一化：源池 / 历史数据的写法 → 前台标准分类
CATEGORY_ALIAS = {
    "时事 / 时政": "时事",
    "时事/时政": "时事",
    "时政": "时事",
    "要闻": "时事",
    "热点": "时事",
    "国内": "时事",
    "国际": "国际",
    "海外": "国际",
    "全球": "国际",
    "经济": "经济",
    "财经": "经济",
    "金融": "经济",
    "商业": "经济",
    "科技": "科技",
    "数码": "科技",
    "互联网": "科技",
    "人文": "人文",
    "文化": "人文",
    "历史": "人文",
    "娱乐": "娱乐",
    "文娱": "娱乐",
    "影视": "娱乐",
    "音乐": "娱乐",
    "生活": "生活",
    "社会": "社会",
    "体育": "体育",
    "运动": "体育",
    "环境": "环境",
    "游戏社群": "游戏社群",
    "游戏": "游戏社群",
}


def normalize_category(raw):
    """把任意写法的分类归一到前台标准分类；无法识别时保留原值。"""
    if not raw:
        return ""
    key = str(raw).strip()
    if key in CANONICAL_CATEGORIES:
        return key
    if key in CATEGORY_ALIAS:
        return CATEGORY_ALIAS[key]
    # 去掉空白后二次匹配（兼容 "时事 / 时政"）
    squashed = re.sub(r"\s+", "", key)
    for alias, canon in CATEGORY_ALIAS.items():
        if re.sub(r"\s+", "", alias) == squashed:
            return canon
    for canon in CANONICAL_CATEGORIES:
        if canon and canon in key:
            return canon
    return key


# 栏目壳标题识别：纯"XX晚报/早报/简报/播报/晨报/联播/午报/日报"等栏目名（可带日期/序号前缀），
# 本身不含具体新闻内容，多为栏目导语或聚合壳，点进去没有真实新闻，不应作为单条新闻入库展示
_SHELL_COLUMN_RE = re.compile(
    r"^(?:【?[^|｜:：\-—\d]{2,10}?(?:晚报|早报|晨报|午报|日报|简报|快报|播报|联播|速递|周报)】?|[0-9０-９]{1,4}[年\.\-/]?[0-9０-９]{0,2}[月\.\-/]?[0-9０-９]{0,2}日?[号]?\s*[^|｜:：]{0,8}?(?:晚报|早报|晨报|简报|播报|联播))(?:\s*[|｜:：]\s*)?"
)


def _is_shell_column_title(title):
    """判断标题是否为无实质新闻内容的栏目壳标题。

    匹配形如「界面晚报 | 平陆运河正式通航」「9月15日东方财富财经晚报（附新闻联播）」
    「牛市早报｜电子信息制造业」「【子午播报】2026年9月15日」等标题：
    - 形如「XX晚报/早报/简报/播报」的栏目名出现在标题开头（含 | ： 等分隔符或直接跟正文）
    - 且标题较短（栏目壳通常只有栏目名+极少正文），避免误伤「某早报报道：xxx」这类含正文标题
    """
    if not title:
        return False
    t = title.strip()
    if len(t) > 60:
        return False
    return bool(_SHELL_COLUMN_RE.match(t))


# ----------------------------------------------------------------------
# HTML 文本清洗工具
# ----------------------------------------------------------------------
_TAG_RE = re.compile(r"<[^>]+>")
_SCRIPT_RE = re.compile(r"<(script|style)[^>]*>.*?</\1>", re.S | re.I)
_IMG_SRC_RE = re.compile(r"<img[^>]+src=[\"']([^\"']+)[\"']", re.I)
_WS_RE = re.compile(r"[ \t\u3000]+")


def strip_html(raw):
    """把 HTML 片段转成纯文本（保留段落换行）"""
    if not raw:
        return ""
    s = _SCRIPT_RE.sub("", str(raw))
    s = re.sub(r"<br\s*/?>", "\n", s, flags=re.I)
    s = re.sub(r"</(p|div|li|h[1-6])>", "\n", s, flags=re.I)
    s = _TAG_RE.sub("", s)
    s = (s.replace("&nbsp;", " ").replace("&amp;", "&").replace("&lt;", "<")
          .replace("&gt;", ">").replace("&quot;", '"').replace("&#39;", "'")
          .replace("&ldquo;", "“").replace("&rdquo;", "”")
          .replace("&mdash;", "—").replace("&hellip;", "…"))
    s = _WS_RE.sub(" ", s)
    s = re.sub(r"\n{3,}", "\n\n", s)
    return s.strip()


_PIXEL_IMAGE_RE = re.compile(r'(rss-pixel|/tracking/|tracking\.(?:png|gif|jpg)|spacer\.(?:gif|png)|transparent\.(?:gif|png)|/(?:1x1|blank|pixel|dot)\.(?:png|gif|jpg|jpeg|webp))', re.I)


def first_image(raw, base_url=""):
    """从 HTML 片段中抽取第一张图片的绝对地址（过滤追踪像素/占位图）"""
    if not raw:
        return ""
    m = _IMG_SRC_RE.search(str(raw))
    if not m:
        return ""
    src = m.group(1).strip()
    if _PIXEL_IMAGE_RE.search(src):
        return ""
    if src.startswith("//"):
        return "https:" + src
    if src.startswith("http://") or src.startswith("https://"):
        return src
    if base_url:
        try:
            return urljoin(base_url, src)
        except Exception:
            return ""
    return ""


def make_news_id():
    """生成 news_<8位hex> 形式的新闻 ID（与现有数据格式一致）"""
    return "news_" + uuid.uuid4().hex[:8]


def to_epoch(value):
    """把多种时间表示统一成 Unix 时间戳（秒）"""
    if value is None or value == "":
        return time.time()
    if isinstance(value, (int, float)):
        v = float(value)
        if v > 1e11:      # 毫秒
            v /= 1000.0
        return v
    s = str(value).strip()
    if not s:
        return time.time()
    # ISO8601 / RFC822
    try:
        from email.utils import parsedate_to_datetime
        return parsedate_to_datetime(s).timestamp()
    except Exception:
        pass
    for fmt in ("%Y-%m-%dT%H:%M:%S%z", "%Y-%m-%dT%H:%M:%SZ", "%Y-%m-%d %H:%M:%S",
                "%Y-%m-%d", "%Y/%m/%d %H:%M:%S", "%Y/%m/%d"):
        try:
            dt = datetime.strptime(s, fmt)
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            return dt.timestamp()
        except Exception:
            continue
    try:
        return datetime.fromisoformat(s.replace("Z", "+00:00")).timestamp()
    except Exception:
        return time.time()


# ----------------------------------------------------------------------
# 源注册表
# ----------------------------------------------------------------------
class SourceRegistry:
    """运行期源注册表：首次从 source-pool.json 播种，之后可增删改。"""

    def __init__(self, pool_file=SOURCE_POOL_FILE, store_file=SOURCES_FILE):
        self.pool_file = Path(pool_file)
        self.store_file = Path(store_file)
        self._lock = threading.RLock()
        self.sources = []
        self._dirty = False
        self._load()

    # ---------- 读取 ----------
    def _load(self):
        with self._lock:
            if self.store_file.exists():
                try:
                    data = json.loads(self.store_file.read_text(encoding="utf-8"))
                    self.sources = data.get("sources", [])
                    self._dirty = False
                    logger.info("源注册表已加载：%d 条", len(self.sources))
                    return
                except Exception as e:
                    logger.warning("源注册表解析失败，回退到源池文件：%s", e)
            self.sources = self._seed_from_pool()
            self._save_locked()

    def _seed_from_pool(self):
        """从 source-pool.json 中提取 status_code == ok 的直连源。

        注意：源池中部分条目的 url 记录的是「版面描述」而非真实 Feed 地址
        （如 "gov.cn 政策 / 新闻页面"），这类条目无法抓取，必须过滤掉，
        否则每轮都会产生无意义的失败记录。
        """
        if not self.pool_file.exists():
            logger.error("源池文件不存在：%s", self.pool_file)
            return []
        pool = json.loads(self.pool_file.read_text(encoding="utf-8"))
        out = []
        skipped_invalid = 0
        for item in pool.get("sources", []):
            if item.get("status_code") != "ok":
                continue
            url = str(item.get("url", "")).strip()
            if not re.match(r"^https?://", url):
                skipped_invalid += 1
                logger.info("跳过无有效 Feed 地址的源：%s（%s）", item.get("name"), url[:40])
                continue
            src_type = item.get("type", "rss")
            if src_type == "proxy":
                src_type = "rss"          # 中转型 RSSHub 实例按 RSS 处理
            out.append(OrderedDict([
                ("id", uuid.uuid4().hex[:12]),
                ("name", item.get("name", "")),
                ("category", normalize_category(item.get("category"))),
                ("type", src_type),
                ("url", url),
                ("language", item.get("language", "")),
                ("update_freq", item.get("update_freq", "")),
                ("enabled", True),
                ("interval_min", DEFAULT_INTERVAL_MIN),
                ("timeout_s", FETCH_TIMEOUT),
                ("is_new", bool(item.get("is_new"))),
                ("origin", "source-pool.json"),
                ("status", "pending"),
                ("last_run", 0),
                ("last_result", ""),
                ("last_error", ""),
                ("success_count", 0),
                ("fail_count", 0),
                ("inserted_total", 0),
                ("history", []),
            ]))
        logger.info("源池播种完成：%d 条直连源（跳过 %d 条无有效 Feed 地址的条目）",
                    len(out), skipped_invalid)
        return out

    # ---------- 写入 ----------
    def _save_locked(self):
        payload = {
            "generated_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "total": len(self.sources),
            "sources": self.sources,
        }
        tmp = self.store_file.with_suffix(".json.tmp")
        tmp.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
        os.replace(str(tmp), str(self.store_file))

    def save(self):
        with self._lock:
            self._save_locked()
            self._dirty = False

    def flush(self):
        """把内存中的运行时状态落盘（仅在确有变更时写文件）"""
        with self._lock:
            if self._dirty:
                self._save_locked()
                self._dirty = False

    def _sanitize(self, item, base=None):
        """校验并规范化一条源配置"""
        base = base or {}
        name = str(item.get("name", base.get("name", ""))).strip()
        url = str(item.get("url", base.get("url", ""))).strip()
        if not name:
            raise ValueError("name 不能为空")
        if not url or not re.match(r"^https?://", url):
            raise ValueError("url 必须以 http:// 或 https:// 开头")
        src_type = str(item.get("type", base.get("type", "rss"))).strip().lower()
        if src_type not in ("rss", "json", "html", "html_article"):
            raise ValueError("type 只能是 rss / json / html / html_article")
        try:
            interval = int(item.get("interval_min", base.get("interval_min", DEFAULT_INTERVAL_MIN)))
        except (TypeError, ValueError):
            raise ValueError("interval_min 必须是整数")
        interval = max(MIN_INTERVAL_MIN, min(MAX_INTERVAL_MIN, interval))
        try:
            timeout_s = int(item.get("timeout_s", base.get("timeout_s", FETCH_TIMEOUT)))
        except (TypeError, ValueError):
            timeout_s = FETCH_TIMEOUT
        timeout_s = max(5, min(60, timeout_s))
        enabled = item.get("enabled", base.get("enabled", True))
        enabled = bool(enabled) if not isinstance(enabled, str) else enabled.lower() in ("1", "true", "yes")
        return {
            "name": name,
            "url": url,
            "type": src_type,
            "category": normalize_category(item.get("category", base.get("category", ""))),
            "language": item.get("language", base.get("language", "")),
            "update_freq": item.get("update_freq", base.get("update_freq", "")),
            "enabled": enabled,
            "interval_min": interval,
            "timeout_s": timeout_s,
        }

    def list(self):
        with self._lock:
            return list(self.sources)

    def get(self, sid):
        with self._lock:
            for s in self.sources:
                if s["id"] == sid:
                    return s
        return None

    def add(self, item):
        with self._lock:
            clean = self._sanitize(item)
            if any(s["url"] == clean["url"] for s in self.sources):
                raise ValueError("该 url 已存在")
            rec = OrderedDict([
                ("id", uuid.uuid4().hex[:12]),
                ("name", clean["name"]),
                ("category", clean["category"] or "时事"),
                ("type", clean["type"]),
                ("url", clean["url"]),
                ("language", clean["language"]),
                ("update_freq", clean["update_freq"]),
                ("enabled", clean["enabled"]),
                ("interval_min", clean["interval_min"]),
                ("timeout_s", clean["timeout_s"]),
                ("is_new", True),
                ("origin", "api"),
                ("status", "pending"),
                ("last_run", 0),
                ("last_result", ""),
                ("last_error", ""),
                ("success_count", 0),
                ("fail_count", 0),
                ("inserted_total", 0),
                ("history", []),
            ])
            self.sources.append(rec)
            self._save_locked()
            return rec

    def update(self, sid, item):
        with self._lock:
            for idx, s in enumerate(self.sources):
                if s["id"] == sid:
                    clean = self._sanitize(item, base=s)
                    for u in self.sources:
                        if u["id"] != sid and u["url"] == clean["url"]:
                            raise ValueError("该 url 已被其他源占用")
                    s.update(clean)
                    self.sources[idx] = s
                    self._save_locked()
                    return s
        return None

    def remove(self, sid):
        with self._lock:
            for idx, s in enumerate(self.sources):
                if s["id"] == sid:
                    self.sources.pop(idx)
                    self._save_locked()
                    return True
        return False

    def record_result(self, sid, state, inserted, error=""):
        """记录一次抓取结果"""
        with self._lock:
            for s in self.sources:
                if s["id"] != sid:
                    continue
                s["status"] = state
                s["last_run"] = time.time()
                s["last_result"] = f"{state}:{inserted}"
                s["last_error"] = error or ""
                if state == "ok":
                    s["success_count"] = int(s.get("success_count", 0)) + 1
                    s["inserted_total"] = int(s.get("inserted_total", 0)) + int(inserted)
                else:
                    s["fail_count"] = int(s.get("fail_count", 0)) + 1
                hist = deque(s.get("history") or [], maxlen=STATUS_HISTORY)
                hist.append({"ts": round(time.time(), 1), "state": state,
                             "inserted": int(inserted), "error": (error or "")[:200]})
                s["history"] = list(hist)
                self._dirty = True
                break

    def to_public(self, s):
        """对外暴露的源视图（含运行时状态）"""
        now = time.time()
        last = s.get("last_run") or 0
        return {
            "id": s["id"],
            "name": s["name"],
            "category": s["category"],
            "type": s["type"],
            "url": s["url"],
            "language": s.get("language", ""),
            "update_freq": s.get("update_freq", ""),
            "enabled": bool(s.get("enabled", True)),
            "interval_min": s.get("interval_min", DEFAULT_INTERVAL_MIN),
            "timeout_s": s.get("timeout_s", FETCH_TIMEOUT),
            "is_new": bool(s.get("is_new")),
            "origin": s.get("origin", ""),
            "status": s.get("status", "pending"),
            "last_run": last,
            "last_run_ago": round(now - last, 1) if last else None,
            "last_result": s.get("last_result", ""),
            "last_error": s.get("last_error", ""),
            "success_count": int(s.get("success_count", 0)),
            "fail_count": int(s.get("fail_count", 0)),
            "inserted_total": int(s.get("inserted_total", 0)),
        }


# ----------------------------------------------------------------------
# 抓取器
# ----------------------------------------------------------------------
class NewsFetcher:
    """按源类型抓取并解析为统一的新闻条目"""

    def __init__(self, registry):
        self.registry = registry

    # ---------- HTTP ----------
    def _get(self, url, timeout, accept):
        headers = {"User-Agent": UA, "Accept": accept,
                   "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8"}
        resp = requests.get(url, headers=headers, timeout=timeout,
                            allow_redirects=True, verify=False)
        return resp

    # ---------- 各类型解析 ----------
    def fetch_rss(self, src):
        import feedparser
        resp = self._get(src["url"], effective_timeout(src),
                         "application/rss+xml, application/atom+xml, application/xml, text/xml, */*")
        if resp.status_code != 200:
            raise RuntimeError(f"HTTP {resp.status_code}")
        parsed = feedparser.parse(resp.content)
        entries = []
        for e in parsed.entries[:PER_SOURCE_LIMIT]:
            title = strip_html(e.get("title", "")).strip()
            if not title:
                continue
            raw_html = ""
            if e.get("content"):
                raw_html = e["content"][0].get("value", "")
            if not raw_html:
                raw_html = e.get("summary", "") or e.get("description", "") or ""
            body = strip_html(raw_html)
            if len(body) > 4000:
                body = body[:4000] + "…"
            if e.get("link"):
                body = f"{body}\n\n原文链接：{e['link']}"
            entries.append({
                "title": title[:200],
                "content": body or title,
                "summary": strip_html(raw_html)[:120] or title[:80],
                "image": first_image(raw_html, e.get("link") or src["url"]),
                "published_at": to_epoch(e.get("published") or e.get("updated")),
                "source": src["name"],
                "category": src["category"],
            })
        return entries

    def fetch_json(self, src):
        resp = self._get(src["url"], effective_timeout(src),
                         "application/json, text/plain, */*")
        if resp.status_code != 200:
            raise RuntimeError(f"HTTP {resp.status_code}")
        data = resp.json()
        items = []
        if isinstance(data, list):
            items = data
        elif isinstance(data, dict):
            for key in ("items", "data", "results", "articles", "news", "list", "posts"):
                v = data.get(key)
                if isinstance(v, list):
                    items = v
                    break
                if isinstance(v, dict):
                    for k2 in ("items", "list", "data"):
                        if isinstance(v.get(k2), list):
                            items = v[k2]
                            break
                    if items:
                        break
            if not items and isinstance(data, dict):
                # GeoJSON：features 为对象数组时取 properties
                if isinstance(data.get("features"), list):
                    items = [p.get("properties", {}) if isinstance(p, dict) else p
                             for p in data.get("features", [])]
                else:
                    # 形如 No1/No2/... 的编号条目字典（如 CENC 地震速报）
                    numbered = [v for k, v in data.items()
                                if re.match(r'^[A-Za-z]{1,4}\d+$', k) and isinstance(v, dict)]
                    if numbered:
                        items = numbered
            if not items:
                items = [data]
        entries = []
        for it in items[:PER_SOURCE_LIMIT]:
            if not isinstance(it, dict):
                continue
            title = strip_html(it.get("title") or it.get("headline") or it.get("name") or "").strip()
            if not title:
                # 地震速报类：地点 + 震级合成标题
                loc = it.get("placeName") or it.get("place") or it.get("location") or ""
                mag = it.get("magnitude") or it.get("mag") or ""
                if loc:
                    title = (f"{loc}发生{mag}级地震" if mag else f"{loc}地震")
            if not title:
                continue
            raw = it.get("content") or it.get("description") or it.get("summary") or it.get("abstract") or ""
            if isinstance(raw, (dict, list)):
                raw = json.dumps(raw, ensure_ascii=False)
            body = strip_html(raw)[:4000] or title
            link = it.get("url") or it.get("link") or it.get("source_url") or ""
            if link:
                body = f"{body}\n\n原文链接：{link}"
            img = it.get("image") or it.get("thumbnail") or it.get("cover") or ""
            if isinstance(img, dict):
                img = img.get("url") or ""
            if not img:
                img = first_image(raw, link or src["url"])
            entries.append({
                "title": title[:200],
                "content": body,
                "summary": strip_html(raw)[:120] or title[:80],
                "image": img if str(img).startswith("http") else "",
                "published_at": to_epoch(it.get("published_at") or it.get("pubDate")
                                         or it.get("pubTime") or it.get("showTime")
                                         or it.get("ctime")
                                         or it.get("time") or it.get("date") or it.get("timestamp")),
                "source": src["name"],
                "category": src["category"],
            })
        return entries

    def fetch_html(self, src):
        """HTML 列表页的保守解析：优先 <article> 内的链接标题；失败即视为无数据。"""
        from bs4 import BeautifulSoup
        resp = self._get(src["url"], effective_timeout(src),
                         "text/html,application/xhtml+xml,*/*")
        if resp.status_code != 200:
            raise RuntimeError(f"HTTP {resp.status_code}")
        if not resp.encoding or resp.encoding.lower() in ("iso-8859-1",):
            resp.encoding = resp.apparent_encoding
        soup = BeautifulSoup(resp.text, "lxml")
        scope = soup.find("article") or soup.find("main") or soup.body
        if scope is None:
            return []
        entries = []
        seen = set()
        for a in scope.find_all("a", href=True):
            title = strip_html(a.get_text(" ", strip=True))
            if len(title) < 8 or len(title) > 120:
                continue
            href = urljoin(src["url"], a["href"])
            if not href.startswith("http") or href in seen:
                continue
            seen.add(href)
            entries.append({
                "title": title[:200],
                "content": f"{title}\n\n原文链接：{href}",
                "summary": title[:80],
                "image": "",
                "published_at": time.time(),
                "source": src["name"],
                "category": src["category"],
            })
            if len(entries) >= PER_SOURCE_LIMIT:
                break
        return entries

    def fetch(self, src):
        t = src.get("type", "rss")
        if t == "json":
            return self.fetch_json(src)
        if t == "html":
            return self.fetch_html(src)
        if t == "html_article":
            return self.fetch_html_article(src)
        return self.fetch_rss(src)

    def fetch_html_article(self, src):
        """正文页直抓：对 article_url 模板逐个抓取正文页，按 selectors 提取标题/正文/时间。

        源配置示例：
        {
          "type": "html_article",
          "url": "https://example.com/latest",          # 列表页
          "article_url": "https://example.com/news/{id}", # 正文页模板，{id} 由 list 选择器给出
          "list": "ul.news-list li a",                    # 列表链接选择器
          "selectors": {"title": "h1.article-title", "content": "div.article-body", "time": "time.article-time"},
          "max_articles": 5
        }
        """
        from bs4 import BeautifulSoup
        resp = self._get(src["url"], effective_timeout(src),
                         "text/html,application/xhtml+xml,*/*")
        if resp.status_code != 200:
            raise RuntimeError(f"HTTP {resp.status_code}")
        if not resp.encoding or resp.encoding.lower() in ("iso-8859-1",):
            resp.encoding = resp.apparent_encoding
        soup = BeautifulSoup(resp.text, "lxml")
        list_sel = src.get("list") or "article a[href], .news-list a[href]"
        scope = soup.select_one("article") or soup.select_one("main") or soup
        links = scope.select(list_sel) if list_sel else []
        if not links:
            links = soup.select(list_sel)
        sel = src.get("selectors") or {}
        t_sel = sel.get("title") or "h1, .title"
        c_sel = sel.get("content") or "article, .content, .article-content"
        time_sel = sel.get("time") or "time, .date, .pub-date"
        entries = []
        seen = set()
        max_n = int(src.get("max_articles") or 5)
        for a in links[:max_n * 3]:
            href = urljoin(src["url"], a["href"]) if a.get("href") else ""
            if not href.startswith("http") or href in seen:
                continue
            seen.add(href)
            try:
                ar = self._get(href, effective_timeout(src),
                               "text/html,application/xhtml+xml,*/*")
                if ar.status_code != 200:
                    continue
                if not ar.encoding or ar.encoding.lower() in ("iso-8859-1",):
                    ar.encoding = ar.apparent_encoding
                asoup = BeautifulSoup(ar.text, "lxml")
                tel = asoup.select_one(t_sel)
                cel = asoup.select_one(c_sel)
                if not tel or not cel:
                    continue
                title = strip_html(tel.get_text(" ", strip=True)).strip()
                content = strip_html(cel.get_text("\n", strip=True)).strip()
                if len(title) < 8 or len(content) < 50:
                    continue
                time_raw = ""
                timel = asoup.select_one(time_sel) if time_sel else None
                if timel:
                    time_raw = timel.get("datetime") or timel.get_text(" ", strip=True)
                published = to_epoch(time_raw) if time_raw else time.time()
                entries.append({
                    "title": title[:200],
                    "content": content[:5000],
                    "summary": title[:80],
                    "image": "",
                    "published_at": published,
                    "source": src["name"],
                    "category": src["category"],
                    "link": href,
                })
            except Exception as ex:
                logger.debug("正文页直抓失败 %s: %s", href, ex)
            if len(entries) >= max_n:
                break
        return entries


# ----------------------------------------------------------------------
# 入库器
# ----------------------------------------------------------------------
class NewsWriter:
    """负责标题去重与写入 bird.db 的 news 表（复用现有表结构）"""

    def __init__(self, db_path=BIRD_DB):
        self.db_path = str(db_path)
        self._lock = threading.Lock()

    def _conn(self):
        conn = sqlite3.connect(self.db_path, timeout=15)
        conn.row_factory = sqlite3.Row
        return conn

    def exists_same_title(self, conn, title, window=None):
        """同标题去重。

        news.created_at 存的是「文章发布时间」，因此以 24h 为窗口比对会导致
        发布超过 24h 的条目在每轮轮询中被反复重新入库。这里把比对窗口取为
        「24h 与可入库最大文章年龄（7 天）中的较大者」——只要该标题在可入库
        时间范围内已存在，就视为重复，从而保证 24h 内绝不重复、且旧文不会
        被每轮重复灌入。
        """
        window = window or max(DEDUP_WINDOW_SEC, MAX_ARTICLE_AGE_SEC)
        start = time.time() - window
        row = conn.execute(
            "SELECT id FROM news WHERE title = ? AND created_at >= ? LIMIT 1",
            (title, start)).fetchone()
        return row is not None

    def save(self, entries):
        """批量入库，返回 (inserted, skipped, failed)"""
        inserted = skipped = failed = 0
        if not entries:
            return inserted, skipped, failed
        with self._lock:
            conn = self._conn()
            try:
                for e in entries:
                    title = (e.get("title") or "").strip()
                    content = (e.get("content") or "").strip()
                    if not title or not content:
                        failed += 1
                        continue
                    # 栏目壳过滤：纯"XX晚报/早报/简报/播报/晨报/联播"标题且正文过短的条目
                    # （多为栏目导语/聚合壳，点进去没有真实新闻内容），直接跳过不入库
                    if len(content) < 200 and _is_shell_column_title(title):
                        skipped += 1
                        continue
                    # 标题精炼：无信息量标题（XX汇总/启幕/速览等）从正文提炼，原标题保留进摘要作副标题
                    orig_title = title
                    refined = refine_title(title, content)
                    if refined:
                        title = refined
                    category = normalize_category(e.get("category"))
                    if category:
                        # 源给过显式分类时也做强词修正：命中强体育词/强经济词则以强词为准，
                        # 避免国际/时事/生活源把体育赛事、财经新闻归错类
                        if any(w in title for w in _SPORT_STRONG_WORDS):
                            category = "体育"
                        elif any(w in title for w in _ECON_STRONG_WORDS):
                            category = "经济"
                        elif any(w in title for w in _FOREIGN_PLACES):
                            # 事件发生地/主体在国外 → 国际（时事），不得落入社会
                            category = "国际"
                        elif any(w in title for w in _DOMESTIC_POLITICS):
                            # 国内政治/纪律/政府事务 → 时事，不得落入社会
                            category = "时事"
                    else:
                        # 无显式分类时，按标题 + 正文关键词自动分类；仍无命中则归入"时事"兜底
                        category = auto_classify_news(title, content) or "时事"
                    # 数码评测/促销广告排除：命中特征词不得误入"生活"（消费电子内容归科技）
                    if category == "生活" and _DIGITAL_AD_RE.search(title):
                        category = "科技"
                    # 政府-企业合作签约/战略合作类新闻过滤：政务活动软文一律不展示
                    if _is_gov_sign_news(title) or _is_gov_sign_news(orig_title):
                        skipped += 1
                        continue
                    # 非新闻/地区政务活动软文标题过滤（直播海报、乡村行、XX地举办XX大会等）
                    if _is_non_news_title(title) or _is_non_news_title(orig_title):
                        skipped += 1
                        continue
                    try:
                        if self.exists_same_title(conn, title):
                            skipped += 1
                            continue
                        created = to_epoch(e.get("published_at"))
                        # 发布时间超过 7 天的条目视为历史归档，不入库
                        # （避免旧闻被重新盖上"最新"时间戳误导读者）
                        if created < time.time() - MAX_ARTICLE_AGE_SEC:
                            skipped += 1
                            continue
                        nid = make_news_id()
                        while conn.execute("SELECT 1 FROM news WHERE id=?", (nid,)).fetchone():
                            nid = make_news_id()
                        conn.execute(
                            "INSERT INTO news (id, title, content, image, author_id, likes, "
                            "created_at, report_removed, summary, category, pinned, images, featured) "
                            "VALUES (?,?,?,?,?,0,?,0,?,?,0,'',0)",
                            (nid, title, content, e.get("image") or "",
                             "source:" + (e.get("source") or "rss"),
                             created,
                             e.get("summary") or (("原标题：" + orig_title[:80]) if refined else orig_title[:80]),
                             category))
                        inserted += 1
                    except Exception as ex:
                        failed += 1
                        logger.debug("单条入库失败：%s", ex)
                conn.commit()
            except Exception as ex:
                conn.rollback()
                logger.error("批量入库失败：%s", ex)
            finally:
                conn.close()
        return inserted, skipped, failed


# ----------------------------------------------------------------------
# 调度器
# ----------------------------------------------------------------------
class FetchScheduler:
    """按 interval_min 轮询所有启用的源"""

    def __init__(self, registry=None, fetcher=None, writer=None):
        self.registry = registry or SourceRegistry()
        self.fetcher = fetcher or NewsFetcher(self.registry)
        self.writer = writer or NewsWriter()
        self._thread = None
        self._stop = threading.Event()
        self._round_lock = threading.Lock()
        self.started_at = 0
        self.last_round_at = 0
        self.last_round_stats = {"fetched": 0, "inserted": 0, "skipped": 0, "failed": 0,
                                 "sources_ok": 0, "sources_failed": 0, "elapsed": 0}
        self.round_count = 0
        self.running = False
        self.last_error = ""

    # ---------- 单源抓取 ----------
    def run_one(self, src):
        name = src.get("name", "?")
        try:
            entries = self.fetcher.fetch(src)
        except requests.exceptions.Timeout:
            self.registry.record_result(src["id"], "timeout", 0, "请求超时")
            logger.warning("源超时跳过：%s", name)
            return 0, 0, 0, "timeout"
        except requests.exceptions.RequestException as ex:
            self.registry.record_result(src["id"], "failed", 0, str(ex)[:180])
            logger.warning("源请求失败：%s -> %s", name, str(ex)[:120])
            return 0, 0, 0, "failed"
        except Exception as ex:
            self.registry.record_result(src["id"], "failed", 0, str(ex)[:180])
            logger.warning("源解析失败：%s -> %s", name, str(ex)[:120])
            return 0, 0, 0, "failed"

        if not entries:
            self.registry.record_result(src["id"], "empty", 0, "本轮无新条目")
            return 0, 0, 0, "empty"

        ins, skip, fail = self.writer.save(entries)
        self.registry.record_result(src["id"], "ok", ins, "")
        logger.info("源抓取完成：%s 解析 %d 条 / 入库 %d 条 / 去重跳过 %d 条",
                    name, len(entries), ins, skip)
        return ins, skip, fail, "ok"

    # ---------- 一轮调度 ----------
    def due_sources(self, now=None):
        now = now or time.time()
        cfg = global_config()
        base = _int_cfg(cfg, "scheduler_interval_min", DEFAULT_INTERVAL_MIN,
                        MIN_INTERVAL_MIN, MAX_INTERVAL_MIN)
        due = []
        for s in self.registry.list():
            if not s.get("enabled", True):
                continue
            try:
                own = int(s.get("interval_min") or base)
            except (TypeError, ValueError):
                own = base
            interval = max(MIN_INTERVAL_MIN, min(MAX_INTERVAL_MIN, own)) * 60
            if now - float(s.get("last_run") or 0) >= interval:
                due.append(s)
        return due

    def run_round(self, force=False, only_ids=None):
        """执行一轮抓取；force=True 时忽略间隔立即抓取"""
        if not self._round_lock.acquire(blocking=False):
            logger.info("上一轮抓取仍在进行，本轮跳过")
            return self.last_round_stats
        try:
            now = time.time()
            # 全局开关（news_config.scheduler_enabled=0 时暂停自动轮询；手动 force 运行不受限）
            if not force and global_config().get("scheduler_enabled", "1") == "0":
                logger.info("全局调度开关 scheduler_enabled=0，本轮自动轮询跳过")
                stats = {"fetched": 0, "inserted": 0, "skipped": 0, "failed": 0,
                         "sources_ok": 0, "sources_failed": 0, "elapsed": 0.0,
                         "paused": True}
                self.last_round_stats = stats
                return stats
            targets = self.registry.list() if force else self.due_sources(now)
            if only_ids:
                targets = [s for s in targets if s["id"] in only_ids]
            targets = [s for s in targets if s.get("enabled", True) or force]
            t0 = time.time()
            stats = {"fetched": 0, "inserted": 0, "skipped": 0, "failed": 0,
                     "sources_ok": 0, "sources_failed": 0, "elapsed": 0}
            if not targets:
                stats["elapsed"] = round(time.time() - t0, 2)
                self.last_round_stats = stats
                return stats

            logger.info("开始抓取：本轮 %d 个源", len(targets))
            with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
                futures = {pool.submit(self.run_one, s): s for s in targets}
                for fut in futures:
                    src = futures[fut]
                    try:
                        ins, skip, fail, state = fut.result()
                    except Exception as ex:
                        ins = skip = fail = 0
                        state = "failed"
                        self.registry.record_result(src["id"], "failed", 0, str(ex)[:180])
                    stats["inserted"] += ins
                    stats["skipped"] += skip
                    stats["failed"] += fail
                    if state == "ok":
                        stats["sources_ok"] += 1
                    else:
                        stats["sources_failed"] += 1
            stats["fetched"] = len(targets)
            stats["elapsed"] = round(time.time() - t0, 2)
            self.last_round_stats = stats
            self.last_round_at = time.time()
            self.round_count += 1
            logger.info("本轮完成：%d 源 / 入库 %d / 去重 %d / 失败 %d / 耗时 %.1fs",
                        stats["fetched"], stats["inserted"], stats["skipped"],
                        stats["failed"], stats["elapsed"])
            return stats
        finally:
            self.registry.flush()
            self._round_lock.release()

    # ---------- 常驻线程 ----------
    def _loop(self):
        self.running = True
        self.started_at = time.time()
        logger.info("调度线程启动，心跳 %ds", SCHEDULER_TICK)
        # 启动后延迟 5 秒做首轮，避免与 Web 服务初始化争抢
        if self._stop.wait(5):
            self.running = False
            return
        while not self._stop.is_set():
            try:
                self.run_round()
            except Exception as ex:
                self.last_error = str(ex)
                logger.error("调度轮次异常：%s", ex)
            if self._stop.wait(SCHEDULER_TICK):
                break
        self.running = False
        logger.info("调度线程已退出")

    def start(self):
        if self._thread and self._thread.is_alive():
            return self
        self._stop.clear()
        self._thread = threading.Thread(target=self._loop, name="peacenews-scheduler", daemon=True)
        self._thread.start()
        return self

    def stop(self):
        self._stop.set()
        if self._thread:
            self._thread.join(timeout=8)
        return self

    # ---------- 状态 ----------
    def status(self):
        now = time.time()
        by_cat = OrderedDict()
        srcs = self.registry.list()
        cfg = global_config(force=True)
        for s in srcs:
            by_cat.setdefault(s.get("category") or "未分类", [])
            by_cat[s.get("category") or "未分类"].append(self.registry.to_public(s))
        return {
            "running": bool(self.running),
            "started_at": self.started_at,
            "uptime_s": round(now - self.started_at, 1) if self.started_at else 0,
            "tick_s": SCHEDULER_TICK,
            "default_interval_min": DEFAULT_INTERVAL_MIN,
            "interval_range_min": [MIN_INTERVAL_MIN, MAX_INTERVAL_MIN],
            "timeout_s": FETCH_TIMEOUT,
            "global_config": cfg,
            "config_keys": list(SCHEDULER_CONFIG_KEYS),
            "dedup_window_h": DEDUP_WINDOW_SEC // 3600,
            "round_count": self.round_count,
            "last_round_at": self.last_round_at,
            "last_round_ago": round(now - self.last_round_at, 1) if self.last_round_at else None,
            "last_round_stats": self.last_round_stats,
            "last_error": self.last_error,
            "total_sources": len(srcs),
            "enabled_sources": sum(1 for s in srcs if s.get("enabled", True)),
            "by_category": {k: len(v) for k, v in by_cat.items()},
            "sources_by_category": by_cat,
            "db_path": str(BIRD_DB),
            "sources_file": str(SOURCES_FILE),
        }


# ----------------------------------------------------------------------
# 全局单例
# ----------------------------------------------------------------------
_scheduler = None
_scheduler_lock = threading.Lock()


def get_scheduler():
    global _scheduler
    with _scheduler_lock:
        if _scheduler is None:
            _scheduler = FetchScheduler()
    return _scheduler


def get_status():
    return get_scheduler().status()


def start(force_first_round=False):
    sched = get_scheduler()
    sched.start()
    return sched


def stop():
    global _scheduler
    with _scheduler_lock:
        if _scheduler is not None:
            _scheduler.stop()
    return True


def run_now(force=True):
    return get_scheduler().run_round(force=force)


# ----------------------------------------------------------------------
# Flask 路由注册
# ----------------------------------------------------------------------
def register_routes(app, admin_required, jsonify, request):
    """把调度管理接口挂到主应用的 Flask 实例上。"""

    @app.route('/api/admin/scheduler/status', methods=['GET'])
    @admin_required
    def api_admin_scheduler_status():
        """调度状态：运行信息 + 每个源的最近状态"""
        try:
            return jsonify(get_status())
        except Exception as ex:
            logger.error("调度状态查询失败：%s", ex)
            return jsonify({'error': '调度状态查询失败'}), 500

    @app.route('/api/admin/scheduler/sources', methods=['GET'])
    @admin_required
    def api_admin_scheduler_sources_list():
        """源列表（可按 category / enabled 过滤）"""
        sched = get_scheduler()
        cat = request.args.get('category', '').strip()
        enabled_raw = request.args.get('enabled', '').strip().lower()
        items = []
        for s in sched.registry.list():
            pub = sched.registry.to_public(s)
            if cat and pub['category'] != cat:
                continue
            if enabled_raw in ('1', 'true', 'yes') and not pub['enabled']:
                continue
            if enabled_raw in ('0', 'false', 'no') and pub['enabled']:
                continue
            items.append(pub)
        return jsonify({'sources': items, 'total': len(items),
                        'categories': CANONICAL_CATEGORIES})

    @app.route('/api/admin/scheduler/sources', methods=['POST'])
    @admin_required
    def api_admin_scheduler_sources_create():
        """新增源"""
        data = request.get_json(silent=True) or {}
        try:
            rec = get_scheduler().registry.add(data)
        except ValueError as ex:
            return jsonify({'error': str(ex)}), 400
        except Exception as ex:
            logger.error("新增源失败：%s", ex)
            return jsonify({'error': '新增源失败'}), 500
        return jsonify({'source': get_scheduler().registry.to_public(rec)}), 201

    @app.route('/api/admin/scheduler/sources/<sid>', methods=['GET'])
    @admin_required
    def api_admin_scheduler_sources_get(sid):
        """查看单个源"""
        rec = get_scheduler().registry.get(sid)
        if not rec:
            return jsonify({'error': '源不存在'}), 404
        return jsonify({'source': get_scheduler().registry.to_public(rec)})

    @app.route('/api/admin/scheduler/sources/<sid>', methods=['PUT', 'PATCH'])
    @admin_required
    def api_admin_scheduler_sources_update(sid):
        """更新源（可只传部分字段）"""
        data = request.get_json(silent=True) or {}
        try:
            rec = get_scheduler().registry.update(sid, data)
        except ValueError as ex:
            return jsonify({'error': str(ex)}), 400
        except Exception as ex:
            logger.error("更新源失败：%s", ex)
            return jsonify({'error': '更新源失败'}), 500
        if not rec:
            return jsonify({'error': '源不存在'}), 404
        return jsonify({'source': get_scheduler().registry.to_public(rec)})

    @app.route('/api/admin/scheduler/sources/<sid>', methods=['DELETE'])
    @admin_required
    def api_admin_scheduler_sources_delete(sid):
        """删除源（仅从调度注册表移除，不影响已入库新闻）"""
        ok = get_scheduler().registry.remove(sid)
        if not ok:
            return jsonify({'error': '源不存在'}), 404
        return jsonify({'ok': True, 'id': sid})

    @app.route('/api/admin/scheduler/run', methods=['POST'])
    @admin_required
    def api_admin_scheduler_run():
        """手动触发一轮抓取；可传 ids=[...] 只跑指定源"""
        data = request.get_json(silent=True) or {}
        only = data.get('ids') or None
        try:
            stats = get_scheduler().run_round(force=True, only_ids=only)
        except Exception as ex:
            logger.error("手动抓取失败：%s", ex)
            return jsonify({'error': '手动抓取失败'}), 500
        return jsonify({'ok': True, 'stats': stats})

    logger.info("调度管理路由已注册：/api/admin/scheduler/*")
    return True


def bootstrap(app=None, admin_required=None, jsonify=None, request=None):
    """server.py 启动时调用：注册路由并拉起后台调度线程。"""
    if app is not None and admin_required is not None:
        try:
            register_routes(app, admin_required, jsonify, request)
        except Exception as ex:
            logger.error("调度路由注册失败：%s", ex)
    try:
        start()
    except Exception as ex:
        logger.error("调度线程启动失败：%s", ex)
    return get_scheduler()
