# -*- coding: utf-8 -*-
"""表情包图库（只读）：扫 meme-packs / 按 tag 抽图 / 缩略图缩放缓存。

从 桌宠.py 拆出来（2026-10-23）。这里只碰文件系统和 QPixmap，不依赖主窗口；
`root=None` 时用本模块的 MEME_ROOT，主程序会把桌宠.MEME_ROOT 传进来，
这样老测试 monkeypatch 桌宠.MEME_ROOT 仍然生效。
"""
import os
import random
import sqlite3

from PySide6.QtCore import Qt
from PySide6.QtGui import QPixmap


# ---------- 表情包图库（只读） ----------
# 图库是用户自己攒的，放在 %USERPROFILE%\.dsh\meme-packs 下，**不进仓库**：
# 几百张图几十 MB，进仓库会把每次 clone 拖慢；而且用户随时会加包 / 删图，
# 代码只负责"按情绪随机抽一张"，不维护副本、也不往图库目录写任何索引。
MEME_ROOT = os.path.join(os.path.expanduser("~"), ".dsh", "meme-packs")
# 六种情绪：(index.db 里的 tag, 右键菜单上的中文)
MEME_TAGS = (("happy", "开心"), ("angry", "生气"), ("sad", "难过"),
             ("shy", "害羞"), ("confused", "困惑"), ("daily", "日常"))
MEME_EXTS = (".png", ".jpg", ".jpeg", ".webp", ".gif")
MEME_MAX_H = 96          # 表情图最大高度（px）
MEME_MAX_W = 240         # 表情图最大宽度（px；实际还要跟窗口宽度取小）
MEME_SECONDS = 5.0       # 表情在头顶挂多久
MEME_GAP = 4             # 图片和 caption 之间的间距
MEME_PAD = 5             # 表情气泡的内边距
# 表情斗图：主人发来一张后，她按"相近情绪"回一张（参考 dsh-meme 的一来一回）
MEME_REPLY_TAGS = {
    "happy": ("happy", "daily", "shy"),
    "angry": ("sad", "shy", "confused"),
    "sad": ("happy", "daily", "shy"),
    "shy": ("happy", "shy", "daily"),
    "confused": ("confused", "daily", "happy"),
    "daily": ("happy", "daily", "confused"),
}
MEME_REPLY_DELAY_MS = 1200     # 自己那张先挂 1.2 秒，再换成她回的
MEME_USER_SECONDS = 1.2        # 主人发的那张在头顶停留多久（之后被回复替换）

# 索引缓存：{"root": 上次扫的根目录, "items": [(绝对路径, tag, caption, keywords), ...]}
# 一个进程只扫一次；根目录被换掉（测试 monkeypatch MEME_ROOT）才会重扫。
_meme_index_cache = {"root": None, "items": None}
# 缩放缓存：{(路径, 目标宽, 目标高): QPixmap 或 False}。每帧都要画，
# 绝不能每帧重新解码 PNG（100 帧/秒会卡）；留最近几张就够用。
_meme_pix_cache = {}
_MEME_PIX_CACHE_MAX = 8


def _meme_root(root=None):
    """图库根目录（每次现读 MEME_ROOT：测试里会 monkeypatch 它）。"""
    return os.path.realpath(os.path.expanduser(str(root if root is not None else MEME_ROOT)))


def _meme_db_uri(path):
    """sqlite 的**只读** URI。Windows 反斜杠要转成 /，空格 / 中文要百分号转义。"""
    from urllib.parse import quote
    return "file:" + quote(os.path.abspath(path).replace("\\", "/")) + "?mode=ro"


def _meme_abs_inside(root, pack, rel):
    """把 index.db 里的相对路径拼成绝对路径；越界 / 后缀不对 → None。

    `path` 是相对**包目录**的（例如 memes/sad/xxx.png）。这一行是数据库内容，
    不可信：`../` 能爬到图库外面，所以拼完必须再验一次"还在 MEME_ROOT 里"。
    """
    try:
        rel = str(rel or "").strip()
    except Exception:
        return None
    if not rel:
        return None
    if os.path.splitext(rel)[1].lower() not in MEME_EXTS:
        return None
    abs_path = os.path.realpath(os.path.join(pack, rel))
    try:
        # Windows 路径大小写不敏感：两边都 normcase 再比
        root_c = os.path.normcase(os.path.realpath(root))
        abs_c = os.path.normcase(abs_path)
        inside = os.path.commonpath([root_c, abs_c]) == root_c
    except (ValueError, OSError):
        inside = False
    return abs_path if inside else None


def _meme_path_ok(path, root=None):
    """一条**绝对路径**能不能当表情显示：后缀对、文件在、而且还在图库根目录里。

    表情抽屉是点哪张显示哪张（`show_meme_path`），所以入口再验一遍：不信任调用方传进来的路径。
    """
    try:
        p = os.path.realpath(str(path or ""))
    except (TypeError, ValueError, OSError):
        return False
    if not p or not os.path.isfile(p):
        return False
    if os.path.splitext(p)[1].lower() not in MEME_EXTS:
        return False
    try:
        root = os.path.normcase(_meme_root(root))
        return os.path.commonpath([root, os.path.normcase(p)]) == root
    except (ValueError, OSError):
        return False


def _scan_meme_packs(root):
    """扫所有包的 index.db，返回 [(绝对路径, tag, caption, keywords), ...]。

    没有 index.db 的包（只有图）直接跳过；读不动的库 / 坏行也跳过，不抛异常。
    keywords 一起读出来给聊天面板的搜索用（按 caption + keywords 子串匹配）。
    """
    items = []
    try:
        names = sorted(os.listdir(root))
    except OSError:
        return items
    for name in names:
        pack = os.path.join(root, name)
        if not os.path.isdir(pack):
            continue
        db = os.path.join(pack, "index.db")
        if not os.path.isfile(db):
            continue
        try:
            con = sqlite3.connect(_meme_db_uri(db), uri=True, timeout=1.0)
        except sqlite3.Error:
            continue
        try:
            rows = con.execute(
                "SELECT path, tag, caption, keywords FROM memes").fetchall()
        except sqlite3.Error:
            # 很老的包可能没有 keywords 列：退回去读三列，搜索就只搜 caption
            try:
                rows = [(p, t, c, "") for p, t, c in con.execute(
                    "SELECT path, tag, caption FROM memes").fetchall()]
            except sqlite3.Error:
                rows = []
        finally:
            try:
                con.close()
            except sqlite3.Error:
                pass
        for rel, tag, caption, keywords in rows:
            abs_path = _meme_abs_inside(root, pack, rel)
            if abs_path is None:
                continue
            # 索引里可能留着已经被删掉的图（用户手动清理过）：扫的时候就跳过
            if not os.path.isfile(abs_path):
                continue
            items.append((abs_path, (tag or "").strip(), (caption or "").strip(),
                          (keywords or "").strip()))
    return items


def _meme_items(force=False, root=None):
    """索引（进程内缓存）。force=True 强制重扫一次（图被删了的时候用）。"""
    root = _meme_root(root)
    cache = _meme_index_cache
    if force or cache["items"] is None or cache["root"] != root:
        cache["root"] = root
        cache["items"] = _scan_meme_packs(root)
    return cache["items"]


def pick_meme(tag=None, root=None):
    """按情绪抽一张表情：返回 (绝对路径, caption) 或 None。

    - 该 tag 一张都没有 → 退回全库随机（用户图库里某一类可能是空的）
    - 文件已经不在了 → 跳过；一张可用的都没有就重扫一次索引再试
    """
    tag = str(tag or "").strip().lower()
    for force in (False, True):
        try:
            items = _meme_items(force=force, root=root)
        except Exception:
            items = []
        usable = [it for it in items if os.path.isfile(it[0])]
        same_tag = [it for it in usable if it[1] == tag] if tag else []
        pool = same_tag or usable
        if pool:
            abs_path, _tag, caption, _keywords = random.choice(pool)
            return abs_path, caption
    return None


def search_or_pick_meme(tag=None, keyword=None, root=None):
    """根据 tag 和 keyword 优先匹配表情包：
    1. 如果给定了 keyword，优先在 items 的 (caption + " " + keywords) 中匹配；
       - 若同时指定了 tag，优先在满足 tag 的子集中匹配；
       - 若未在当前 tag 命中，在全库包含 keyword 的表情中匹配；
    2. 如果未指定 keyword 或关键词未命中，退回到按 tag 随机抽图；
    3. 如果 tag 也没有匹配，则在全库随机抽一张；
    返回 (abs_path, caption) 或 None。
    """
    tag = str(tag or "").strip().lower()
    keyword = str(keyword or "").strip().lower()

    if keyword:
        for force in (False, True):
            try:
                items = _meme_items(force=force, root=root)
            except Exception:
                items = []
            usable = [it for it in items if os.path.isfile(it[0])]
            if not usable:
                continue

            if tag:
                tag_kw = [it for it in usable if it[1] == tag and (keyword in it[2].lower() or keyword in it[3].lower())]
                if tag_kw:
                    abs_path, _t, caption, _k = random.choice(tag_kw)
                    return abs_path, caption

            any_kw = [it for it in usable if (keyword in it[2].lower() or keyword in it[3].lower())]
            if any_kw:
                abs_path, _t, caption, _k = random.choice(any_kw)
                return abs_path, caption
            break

    return pick_meme(tag=tag, root=root)


def load_meme_pixmap(path, max_w=MEME_MAX_W, max_h=MEME_MAX_H):
    """把表情缩放到 max_w × max_h 里（等比、保 alpha），按 (路径, 目标尺寸) 缓存。"""
    max_w, max_h = max(1, int(max_w)), max(1, int(max_h))
    key = (path, max_w, max_h)
    hit = _meme_pix_cache.get(key)
    if hit is not None:
        return hit if hit is not False else None
    pm = QPixmap(path)
    if pm.isNull():
        _meme_pix_cache[key] = False        # 坏图 / 读不动：也记一笔，别每帧重试
        return None
    if pm.width() > max_w or pm.height() > max_h:
        # SmoothTransformation 保住透明通道（带 alpha 的 PNG 不能变黑底）
        pm = pm.scaled(int(max_w), int(max_h), Qt.AspectRatioMode.KeepAspectRatio,
                       Qt.TransformationMode.SmoothTransformation)
    if len(_meme_pix_cache) >= _MEME_PIX_CACHE_MAX:
        for old in list(_meme_pix_cache)[: max(1, _MEME_PIX_CACHE_MAX // 2)]:
            _meme_pix_cache.pop(old, None)
    _meme_pix_cache[key] = pm
    return pm