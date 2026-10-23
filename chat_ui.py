# -*- coding: utf-8 -*-
"""聊天面板 / 表情抽屉的界面层：粉彩聊天面板、左右消息气泡、头像、5 列格子池。

从 桌宠.py 拆出来（2026-10-23）。本模块不 import 桌宠.py，只反过来被它 import；
需要桌宠的东西（字体 / 形象 / 发消息）全部通过 `self.pet` 调，
表情索引通过 `pet.meme_items()`（这样 monkeypatch 桌宠.MEME_ROOT 仍然生效）。
"""
from collections import OrderedDict
import datetime
import math

from PySide6.QtCore import (Qt, QTimer, QPoint, QPointF, QRect, QRectF, QSize,
                            Signal, QEvent)
from PySide6.QtGui import (QPainter, QPixmap, QImage, QImageReader, QFont, QColor,
                           QIcon, QFontMetrics, QPen, QPalette, QPainterPath,
                           QLinearGradient, QTextDocument, QActionGroup)
from PySide6.QtWidgets import (QApplication, QWidget, QLabel, QToolButton, QLineEdit,
                               QScrollArea, QFrame, QVBoxLayout, QPushButton, QMenu,
                               QTextEdit)

from meme_store import MEME_TAGS


# ---------- 聊天面板 + 表情抽屉 ----------
# 面板是无边框置顶小窗：星空底 + 一行输入；点 😊 往下展开一块表情网格（5 列）。
# 网格只在 paintEvent 里解码"可见 + 上下各预取 1 行"的缩略图，缓存 LRU 80 张 ——
# 434 张图一次性解码会卡住界面好几秒，这条是硬约束。
CHAT_PANEL_W = 420
CHAT_HEADER_H = 58
CHAT_LOG_H = 210
CHAT_PANEL_H = CHAT_HEADER_H + CHAT_LOG_H + 78   # 346
CHAT_DRAWER_H = 320
CHAT_ROW_Y = CHAT_HEADER_H + CHAT_LOG_H + 8      # 276
CHAT_INPUT_H = 62
CHAT_ROW_H = 34
CHAT_RADIUS = 20
MEME_GRID_COLS = 5
MEME_CELL = 62
MEME_GRID_GAP = 6
MEME_GRID_LIMIT = 200            # 一次最多渲染 200 个格子（再多也没人翻）
MEME_THUMB_CACHE_MAX = 80        # 缩略图 LRU 上限
MEME_GRID_W = MEME_GRID_COLS * MEME_CELL + (MEME_GRID_COLS - 1) * MEME_GRID_GAP

_PANEL_FG = QColor(15, 23, 42)
_PANEL_DIM = QColor(100, 116, 139)
_PANEL_CELL_BG = QColor(255, 255, 255, 120)
_PANEL_CELL_HOVER = QColor(99, 102, 241, 220)

_CHAT_INPUT_QSS = (
    "QLineEdit, QTextEdit { background: rgba(241, 245, 249, 235);"
    " border: 1px solid rgba(226, 232, 240, 255); border-radius: 22px;"
    " color: #0F172A; padding-left: 12px; padding-right: 12px;"
    " selection-background-color: #C7D2FE; }"
    "QLineEdit:focus, QTextEdit:focus { border: 1px solid rgba(99, 102, 241, 200); }"
    "QTextEdit QScrollBar:vertical { background: transparent; width: 5px; margin: 0; }"
    "QTextEdit QScrollBar::handle:vertical { background: rgba(148, 163, 184, 140);"
    " border-radius: 2px; min-height: 18px; }"
    "QTextEdit QScrollBar::add-line:vertical, QTextEdit QScrollBar::sub-line:vertical"
    " { height: 0; }")
_CHAT_BTN_QSS = (
    "QToolButton { background: rgba(255, 255, 255, 210);"
    " border: 1px solid rgba(226, 232, 240, 255); border-radius: 17px;"
    " color: #475569; padding: 0px; }"
    "QToolButton:hover { background: rgba(238, 242, 255, 255);"
    " color: #4F46E5; }"
    "QToolButton:pressed { background: rgba(224, 231, 255, 255); }")
_CHAT_SEND_QSS = (
    "QToolButton { background: qlineargradient(x1:0, y1:0, x2:1, y2:1,"
    " stop:0 #6366F1, stop:1 #8B5CF6);"
    " border: 1px solid rgba(99, 102, 241, 180); border-radius: 18px;"
    " color: #FFFFFF; padding: 0px; }"
    "QToolButton:hover { background: qlineargradient(x1:0, y1:0, x2:1, y2:1,"
    " stop:0 #818CF8, stop:1 #A78BFA); }"
    "QToolButton:pressed { background: #4F46E5; }")
_CHAT_SCROLL_QSS = (
    "QScrollArea { background: transparent; border: none; }"
    "QScrollBar:vertical { background: transparent; width: 6px; margin: 0; }"
    "QScrollBar::handle:vertical { background: rgba(148, 163, 184, 130);"
    " border-radius: 3px; min-height: 28px; }"
    "QScrollBar::handle:vertical:hover { background: rgba(99, 102, 241, 190); }"
    "QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; }"
    "QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical { background: none; }")

# 聊天记录里的两种气泡（左：她，右：我）
_PET_BUBBLE_QSS = (
    "QLabel { background: rgba(255, 255, 255, 236);"
    " border: 1px solid rgba(203, 213, 225, 230);"
    " border-top-left-radius: 16px; border-top-right-radius: 16px;"
    " border-bottom-right-radius: 16px; border-bottom-left-radius: 5px;"
    " color: #334155; padding: 8px 11px; }")
_USER_BUBBLE_QSS = (
    "QLabel { background: qlineargradient(x1:0, y1:0, x2:1, y2:1,"
    " stop:0 #6366F1, stop:1 #8B5CF6);"
    " border: 1px solid rgba(255, 255, 255, 140);"
    " border-top-left-radius: 16px; border-top-right-radius: 16px;"
    " border-bottom-left-radius: 16px; border-bottom-right-radius: 5px;"
    " color: #FFFFFF; padding: 8px 11px; }")
# 表情图片卡：图片 + 一条 caption
_PET_CARD_QSS = (
    "QWidget#card { background: rgba(255, 255, 255, 236);"
    " border: 1px solid rgba(203, 213, 225, 230);"
    " border-top-left-radius: 16px; border-top-right-radius: 16px;"
    " border-bottom-right-radius: 16px; border-bottom-left-radius: 5px; }")
_USER_CARD_QSS = (
    "QWidget#card { background: qlineargradient(x1:0, y1:0, x2:1, y2:1,"
    " stop:0 #6366F1, stop:1 #8B5CF6);"
    " border: 1px solid rgba(255, 255, 255, 140);"
    " border-top-left-radius: 16px; border-top-right-radius: 16px;"
    " border-bottom-left-radius: 16px; border-bottom-right-radius: 5px; }")

_CHAT_IMG_CACHE = {}


def chat_image_pixmap(path, max_w=220, max_h=150):
    """聊天记录里的表情大图（只缓存最近 20 张）。"""
    key = (str(path), int(max_w), int(max_h))
    if key in _CHAT_IMG_CACHE:
        return _CHAT_IMG_CACHE[key]
    pm = QPixmap(str(path))
    if pm.isNull():
        _CHAT_IMG_CACHE[key] = None
        return None
    pm = pm.scaled(int(max_w), int(max_h),
                   Qt.AspectRatioMode.KeepAspectRatio,
                   Qt.TransformationMode.SmoothTransformation)
    if len(_CHAT_IMG_CACHE) >= 20:
        _CHAT_IMG_CACHE.pop(next(iter(_CHAT_IMG_CACHE)))
    _CHAT_IMG_CACHE[key] = pm
    return pm


def smiley_pixmap(size=22):
    """画一个 😊 当表情键的图标（不依赖 Segoe UI Emoji 有没有装 / 能不能彩色渲染）。"""
    pm = QPixmap(int(size), int(size))
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setPen(Qt.PenStyle.NoPen)
    p.setBrush(QColor(255, 206, 84))
    p.drawEllipse(1, 1, int(size) - 2, int(size) - 2)
    p.setBrush(QColor(58, 44, 22))
    r = max(1.2, size * 0.085)
    p.drawEllipse(QPointF(size * 0.34, size * 0.40), r, r)
    p.drawEllipse(QPointF(size * 0.66, size * 0.40), r, r)
    pen = QPen(QColor(58, 44, 22), max(1.4, size * 0.075))
    pen.setCapStyle(Qt.PenCapStyle.RoundCap)
    p.setPen(pen)
    p.setBrush(Qt.BrushStyle.NoBrush)
    p.drawArc(QRectF(size * 0.26, size * 0.42, size * 0.48, size * 0.36),
              200 * 16, 140 * 16)
    p.end()
    return pm


class MemeThumbCache:
    """表情缩略图缓存：按需解码 + LRU 80 张。

    `loads` / `hits` 是给回归测试看的计数（真实解码 vs 缓存命中）。
    """

    def __init__(self, limit=MEME_THUMB_CACHE_MAX):
        self.limit = max(1, int(limit))
        self._data = OrderedDict()
        self.loads = 0
        self.hits = 0

    def get(self, path, size=MEME_CELL):
        key = (str(path), int(size))
        if key in self._data:
            self._data.move_to_end(key)
            self.hits += 1
            return self._data[key]
        pm = self._decode(path, int(size))
        self.loads += 1
        self._data[key] = pm
        while len(self._data) > self.limit:
            self._data.popitem(last=False)        # 最久没用到的先淘汰
        return pm

    @staticmethod
    def _decode(path, size):
        """解码成"填满 size×size"的 cover 缩略图（等比放大后居中裁掉多余部分）。"""
        try:
            reader = QImageReader(str(path))
            reader.setAutoTransform(True)
            src = reader.size()
            if src.isValid() and src.width() > 0 and src.height() > 0:
                # 先算目标尺寸再让 reader 只解这么多像素，比读完原图再缩快得多
                scale = max(size / float(src.width()), size / float(src.height()))
                reader.setScaledSize(QSize(max(1, round(src.width() * scale)),
                                           max(1, round(src.height() * scale))))
                img = reader.read()
            else:
                img = QImage(str(path))
            if img.isNull():
                return None
            pm = QPixmap.fromImage(img)
            if pm.isNull():
                return None
            x = max(0, (pm.width() - size) // 2)
            y = max(0, (pm.height() - size) // 2)
            return pm.copy(x, y, min(size, pm.width()), min(size, pm.height()))
        except Exception:
            return None


class MemeCell(QWidget):
    """池里的一个格子：滚动时循环复用，只有内容真的换了才重绘 / 换图。"""

    def __init__(self, grid, parent=None):
        super().__init__(parent)
        self.grid = grid
        self._index = -1
        self._path = None
        self._pm = None
        self._hover = False
        self.content_changes = 0        # 内容真换了几次（回归测试用）
        self.setFixedSize(MEME_CELL, MEME_CELL)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setAutoFillBackground(False)
        self.setAttribute(Qt.WidgetAttribute.WA_NoSystemBackground, True)

    def set_item(self, index, item):
        self._index = int(index)
        path = item[0]
        if path != self._path:
            # 只有换了图才重新取缩略图 / update；滚动一行时大部分格子停在同一张
            self._path = path
            self._pm = self.grid.thumbs.get(path, MEME_CELL)
            self.content_changes += 1
            self.update()

    def clear_item(self):
        if self._index != -1 or self._path is not None:
            self._index = -1
            self._path = None
            self._pm = None
            self.update()

    def paintEvent(self, _ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        rect = QRectF(self.rect())
        path = QPainterPath()
        path.addRoundedRect(rect, 8, 8)
        p.setPen(Qt.PenStyle.NoPen)
        p.fillPath(path, _PANEL_CELL_BG)
        if self._pm is not None and not self._pm.isNull():
            p.setClipPath(path)
            dx = (self.width() - self._pm.width()) // 2
            dy = (self.height() - self._pm.height()) // 2
            p.drawPixmap(dx, dy, self._pm)
        else:
            p.setPen(_PANEL_DIM)
            p.drawText(rect, Qt.AlignmentFlag.AlignCenter, "?")
        if self._hover:
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.setPen(QPen(_PANEL_CELL_HOVER, 2))
            p.drawPath(path)
        p.end()

    def enterEvent(self, ev):
        self._hover = True
        self.update()                   # 只重绘这一格，不动整个网格
        super().enterEvent(ev)

    def leaveEvent(self, ev):
        self._hover = False
        self.update()
        super().leaveEvent(ev)

    def mousePressEvent(self, ev):
        if ev.button() == Qt.MouseButton.LeftButton and self._index >= 0:
            self.grid._cell_clicked(self._index)
            return
        super().mousePressEvent(ev)


class MemeGrid(QWidget):
    """固定格子池的 5 列网格：控件数由视口大小决定，滚动时循环复用。

    池子大小 = 5 列 ×（可见行数 + 2 行缓冲）。滚出屏幕的格子不销毁，
    改装新露出来的那一行；同一格内容没变就不换图、不重绘。
    """

    cellClicked = Signal(int)

    def __init__(self, thumbs, parent=None):
        super().__init__(parent)
        self._thumbs = thumbs
        self._items = []
        self._viewport = None
        self._pool = []
        self._pool_rows = 0
        self._cells = {}               # 当前可见：index -> MemeCell
        self.setFixedWidth(MEME_GRID_W)
        self.setAutoFillBackground(False)
        self.setAttribute(Qt.WidgetAttribute.WA_NoSystemBackground, True)

    @property
    def thumbs(self):
        return self._thumbs

    def set_items(self, items):
        self._items = list(items or [])
        rows = (len(self._items) + MEME_GRID_COLS - 1) // MEME_GRID_COLS
        h = rows * MEME_CELL + max(0, rows - 1) * MEME_GRID_GAP
        self.setFixedHeight(max(0, h))
        # 筛选/搜索变了：整页内容都换了，池子里的内容全部作废
        for cell in self._pool:
            cell.clear_item()
            cell.hide()
        self._cells = {}
        self.sync_pool()

    def items(self):
        return list(self._items)

    def set_viewport(self, widget):
        self._viewport = widget

    def cell_rect(self, index):
        row, col = divmod(int(index), MEME_GRID_COLS)
        x = col * (MEME_CELL + MEME_GRID_GAP)
        y = row * (MEME_CELL + MEME_GRID_GAP)
        return QRect(x, y, MEME_CELL, MEME_CELL)

    def cell_widget(self, index):
        """当前可见的格子控件（测试 / 调试用；不可见返回 None）。"""
        return self._cells.get(int(index))

    def index_at(self, pos):
        x, y = int(pos.x()), int(pos.y())
        if x < 0 or y < 0:
            return -1
        step = MEME_CELL + MEME_GRID_GAP
        col, row = x // step, y // step
        if col >= MEME_GRID_COLS:
            return -1
        if x - col * step >= MEME_CELL or y - row * step >= MEME_CELL:
            return -1
        idx = row * MEME_GRID_COLS + col
        return idx if idx < len(self._items) else -1

    def _viewport_rect(self):
        if self._viewport is not None:
            try:
                origin = self.mapFrom(self._viewport, QPoint(0, 0))
                return QRect(origin, self._viewport.size()).intersected(self.rect())
            except Exception:
                return self.rect()
        return self.rect()

    def _row_span(self):
        vis = self._viewport_rect()
        step = MEME_CELL + MEME_GRID_GAP
        rows = (len(self._items) + MEME_GRID_COLS - 1) // MEME_GRID_COLS
        if vis.isEmpty() or rows <= 0:
            return 0, -1, 0, -1, rows
        first_vis = max(0, vis.top() // step)
        last_vis = min(rows - 1, vis.bottom() // step)
        first = max(0, first_vis - 1)          # 上面多备 1 行
        last = min(rows - 1, last_vis + 1)     # 下面多备 1 行
        return first_vis, last_vis, first, last, rows

    def _pool_row_count(self):
        """池子行数 = 视口能放下的行数 + 2 行缓冲（由窗口大小决定）。"""
        vis = self._viewport_rect()
        step = MEME_CELL + MEME_GRID_GAP
        if vis.isEmpty() or vis.height() <= 0:
            return 6
        rows = int(math.ceil(vis.height() / float(step)))
        return max(2, min(12, rows)) + 2

    def _ensure_pool(self):
        need = MEME_GRID_COLS * self._pool_row_count()
        if len(self._pool) == need:
            return
        for cell in self._pool:
            cell.hide()
            cell.deleteLater()
        self._pool = [MemeCell(self, self) for _ in range(need)]
        for cell in self._pool:
            cell.hide()
        self._cells = {}
        self._pool_rows = need // MEME_GRID_COLS

    def _visible_range(self):
        """要绑定的序号闭区间（可见行 ±1 行缓冲）。"""
        _fv, _lv, first, last, _rows = self._row_span()
        if last < first:
            return 0, -1
        return (first * MEME_GRID_COLS,
                min(len(self._items) - 1, last * MEME_GRID_COLS + MEME_GRID_COLS - 1))

    def sync_pool(self):
        """把可见（含缓冲）的格子绑到池子里的控件上；没变的不碰。"""
        if not self._items:
            for cell in self._pool:
                cell.clear_item()
                cell.hide()
            self._cells = {}
            return
        vis = self._viewport_rect()
        if vis.isEmpty():
            return
        self._ensure_pool()
        _fv, _lv, first, last, _rows = self._row_span()
        if last < first:
            return
        bound = set()
        new_cells = {}
        for row in range(first, last + 1):
            for col in range(MEME_GRID_COLS):
                idx = row * MEME_GRID_COLS + col
                if idx >= len(self._items):
                    continue
                slot = (row % self._pool_rows) * MEME_GRID_COLS + col
                cell = self._pool[slot]
                if cell._index != idx:
                    cell.set_item(idx, self._items[idx])
                rect = self.cell_rect(idx)
                if cell.geometry() != rect:
                    cell.setGeometry(rect)
                if not cell.isVisible():
                    cell.show()
                bound.add(id(cell))
                new_cells[idx] = cell
        for cell in self._pool:
            if id(cell) not in bound:
                cell.clear_item()
                cell.hide()
        self._cells = new_cells

    def resizeEvent(self, ev):
        self.sync_pool()
        super().resizeEvent(ev)

    def showEvent(self, ev):
        self.sync_pool()
        super().showEvent(ev)

    def _cell_clicked(self, index):
        self.cellClicked.emit(int(index))

class ChatInput(QTextEdit):
    """多行输入框：Enter 发送、Shift+Enter 换行、Esc 交给面板处理。"""

    sendRequested = Signal()
    escapePressed = Signal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setAcceptRichText(False)
        self.setTabChangesFocus(True)
        self.setFrameShape(QFrame.Shape.NoFrame)
        self.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

    def keyPressEvent(self, ev):
        if ev.key() in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
            if ev.modifiers() & Qt.KeyboardModifier.ShiftModifier:
                super().keyPressEvent(ev)      # Shift+Enter：正常换行
            else:
                self.sendRequested.emit()       # Enter：发送
            return
        if ev.key() == Qt.Key.Key_Escape:
            self.escapePressed.emit()
            return
        super().keyPressEvent(ev)


_PET_AVATAR_CACHE = []


def pet_avatar_pixmap(source, size=36):
    """聊天记录里她的小头像：从桌宠立绘裁一个圆头像（source 由 PetWindow 提供）。"""
    if source is None or source.isNull():
        return None
    size = int(size)
    if _PET_AVATAR_CACHE and _PET_AVATAR_CACHE[0].width() == size:
        return _PET_AVATAR_CACHE[0]
    pm = source
    # 只取头部那一块（整只 chibi 塞进圆头像会太小），再等比缩放到头像大小
    side = max(1, min(pm.width(), int(pm.height() * 0.62)))
    x = max(0, (pm.width() - side) // 2)
    y = max(0, int(pm.height() * 0.03))
    pm = pm.copy(x, y, side, side)
    pm = pm.scaled(size, size, Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                   Qt.TransformationMode.SmoothTransformation)
    x = max(0, (pm.width() - size) // 2)
    y = max(0, (pm.height() - size) // 2)
    pm = pm.copy(x, y, min(size, pm.width()), min(size, pm.height()))
    _PET_AVATAR_CACHE[:] = [pm]
    return pm


class AvatarWidget(QWidget):
    """圆形头像：她 = 现有立绘；我 = 粉蓝渐变 + 「你」。"""

    def __init__(self, role, size=36, parent=None, avatar_pm=None):
        super().__init__(parent)
        self.role = role
        self._size = int(size)
        self.setFixedSize(self._size, self._size)
        self._pm = avatar_pm if role == "pet" else None

    def paintEvent(self, _ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        rect = QRectF(1, 1, self._size - 2, self._size - 2)
        path = QPainterPath()
        path.addEllipse(rect)
        p.setClipPath(path)
        if self._pm is not None and not self._pm.isNull():
            p.fillPath(path, QColor(255, 236, 246))
            p.drawPixmap(0, 0, self._pm)
        else:
            grad = QLinearGradient(0, 0, self._size, self._size)
            grad.setColorAt(0.0, QColor(99, 102, 241))
            grad.setColorAt(1.0, QColor(139, 92, 246))
            p.fillPath(path, grad)
            f = QFont(self.font())
            f.setPointSizeF(10.5)
            f.setBold(True)
            p.setFont(f)
            p.setPen(QColor(255, 255, 255))
            p.drawText(rect, Qt.AlignmentFlag.AlignCenter, "你")
        p.setClipping(False)
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(QPen(QColor(255, 255, 255, 230), 2))
        p.drawEllipse(rect)
        p.end()


class ChatMessageRow(QWidget):
    """聊天记录的一行：左边她（白气泡）、右边我（靛紫渐变）+ 圆头像。

    有 `image` 时画成图片卡（表情包 + caption），没有就画普通文字气泡。
    """

    def __init__(self, role, text, font, parent=None, avatar_pm=None,
                 image=None, timestamp=""):
        super().__init__(parent)
        self.role = role
        self.image = image
        self.avatar = AvatarWidget(role, 36, self, avatar_pm=avatar_pm)
        f = QFont(font)
        f.setPointSizeF(10.5)
        self._font = f
        if image:
            self._build_image_row(role, str(text or ""), f)
        else:
            self.label = QLabel(str(text or ""), self)
            self.label.setWordWrap(True)
            self.label.setFont(f)
            self.label.setStyleSheet(_PET_BUBBLE_QSS if role == "pet"
                                     else _USER_BUBBLE_QSS)
            self.label.setAlignment(Qt.AlignmentFlag.AlignLeft
                                    | Qt.AlignmentFlag.AlignVCenter)
            self.bubble = self.label
            self._bw, self._bh = self._measure(str(text or ""), f)
            self.label.setFixedSize(self._bw, self._bh)
        self._time_h = 0
        self.time_label = QLabel(str(timestamp or ""), self)
        f_time = QFont(f)
        f_time.setPointSizeF(8.0)
        self.time_label.setFont(f_time)
        self.time_label.setStyleSheet(
            "background: transparent; color: #94A3B8; border: none;")
        if timestamp:
            self._time_h = 14
            self.time_label.show()
        else:
            self.time_label.hide()
        self.setFixedHeight(max(36, self._bh + self._time_h + 4) + 8)
        self._place()

    @staticmethod
    def _add_glow(widget):
        # 曾经用 QGraphicsDropShadowEffect 做发光；40 行一起滚动时太重（用户反馈很卡），
        # 现在只用渐变 + 边框，效果差一点但滚动顺。
        return

    def _build_image_row(self, role, caption, font):
        pm = chat_image_pixmap(self.image)
        img_w = pm.width() if pm is not None else 0
        img_h = pm.height() if pm is not None else 0
        fm = QFontMetrics(font)
        cap_w = (min(220, max(70, fm.horizontalAdvance(caption) + 8))
                 if caption else 0)
        box_w = min(262, max(img_w, cap_w) + 12)
        cap_h = 0
        if caption:
            doc = QTextDocument()
            doc.setDefaultFont(font)
            doc.setPlainText(caption)
            doc.setTextWidth(max(20, box_w - 12))
            cap_h = int(doc.size().height()) + 2
        box_h = img_h + (cap_h + 4 if caption else 0) + 12
        self.container = QWidget(self)
        self.container.setObjectName("card")
        self.container.setStyleSheet(_PET_CARD_QSS if role == "pet"
                                     else _USER_CARD_QSS)
        lay = QVBoxLayout(self.container)
        lay.setContentsMargins(6, 6, 6, 6)
        lay.setSpacing(3)
        self.image_label = QLabel(self.container)
        self.image_label.setStyleSheet("background: transparent; border: none;")
        if pm is not None and not pm.isNull():
            self.image_label.setPixmap(pm)
            self.image_label.setFixedSize(pm.size())
        else:
            self.image_label.setText("图片没找到")
            self.image_label.setStyleSheet(
                "background: transparent; color: #94A3B8; border: none;")
        lay.addWidget(self.image_label, 0, Qt.AlignmentFlag.AlignHCenter)
        self.label = QLabel(caption, self.container)
        self.label.setWordWrap(True)
        self.label.setFont(font)
        self.label.setStyleSheet(
            "background: transparent; border: none; color: %s;"
            % ("#FFFFFF" if role == "user" else "#64748B"))
        if caption:
            self.label.setFixedWidth(max(20, box_w - 12))
            self.label.setFixedHeight(cap_h)
            lay.addWidget(self.label)
        else:
            self.label.hide()
        self.container.setFixedSize(box_w, box_h)
        self.bubble = self.container
        self._bw, self._bh = box_w, box_h

    @staticmethod
    def _measure(text, font):
        fm = QFontMetrics(font)
        max_w = 262
        if not text:
            return 70, fm.height() + 22
        text_w = min(max_w, fm.horizontalAdvance(text) + 44)
        text_w = max(92, text_w)
        doc = QTextDocument()
        doc.setDefaultFont(font)
        doc.setPlainText(text)
        doc.setTextWidth(max(20, text_w - 26))
        return text_w, int(doc.size().height()) + 22

    def _place(self):
        if self.role == "pet":
            self.avatar.move(4, 4)
            self.bubble.move(48, 4)
            self.time_label.move(48, 4 + self._bh + 2)
            self.time_label.setGeometry(48, 4 + self._bh + 2, self._bw, 14)
            self.time_label.setAlignment(Qt.AlignmentFlag.AlignLeft)
        else:
            self.avatar.move(max(4, self.width() - 40), 4)
            bx = max(4, self.width() - 46 - self._bw)
            self.bubble.move(bx, 4)
            self.time_label.setGeometry(bx, 4 + self._bh + 2, self._bw, 14)
            self.time_label.setAlignment(Qt.AlignmentFlag.AlignRight)

    def resizeEvent(self, ev):
        self._place()
        super().resizeEvent(ev)


class ChatPanel(QWidget):
    """QQ 风聊天面板：粉彩天空 + 左右消息气泡 + 头像 + 😊 表情抽屉（非模态）。"""

    def __init__(self, pet):
        super().__init__(None, Qt.WindowType.FramelessWindowHint
                         | Qt.WindowType.Tool
                         | Qt.WindowType.WindowStaysOnTopHint)
        self.pet = pet
        self._avatar_pm = None
        try:
            self._avatar_pm = pet.chat_avatar_pixmap(36)
        except Exception:
            pass
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setWindowTitle("聊天")
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.setFixedWidth(CHAT_PANEL_W)
        self._drawer_open = False
        self._tag = ""
        self._filtered = []
        self._shown = []
        self._guard = None
        self._thumbs = MemeThumbCache()
        self._last_pos = None
        self._persona_cache = ""
        self._font_sig = None
        self._pinned = False
        self._dragging = False
        self._drag_off = None
        self._build_ui()
        self.resize(CHAT_PANEL_W, CHAT_PANEL_H)
        self._relayout()

    # ---------- 界面 ----------
    def _build_ui(self):
        self._header_avatar = AvatarWidget("pet", 40, self, avatar_pm=self._avatar_pm)
        self._header_avatar.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)

        self._title = QLabel("小鲸鱼娘", self)
        self._title.setStyleSheet("background: transparent; color: #0F172A;")
        self._title.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        self._title.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)

        self._badge = QLabel("桌面小鲸鱼", self)
        self._badge.setStyleSheet(
            "background: rgba(238, 242, 255, 255); color: #4F46E5;"
            " border: 1px solid rgba(199, 210, 254, 255); border-radius: 10px;"
            " padding: 1px 7px;")
        self._badge.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._badge.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)

        self._persona = QLabel("温柔 · 在线", self)
        self._persona.setStyleSheet("background: transparent; color: #059669;")
        self._persona.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        self._persona.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)

        # 聊天记录（左她右我）
        self._log_scroll = QScrollArea(self)
        self._log_scroll.setFrameShape(QFrame.Shape.NoFrame)
        self._log_scroll.setWidgetResizable(True)
        self._log_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self._log_scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self._log_scroll.setStyleSheet(_CHAT_SCROLL_QSS)
        self._log_scroll.viewport().setAutoFillBackground(False)
        self._log_body = QWidget()
        self._log_body.setAutoFillBackground(False)
        self._log_body.setAttribute(Qt.WidgetAttribute.WA_NoSystemBackground, True)
        self._log_lay = QVBoxLayout(self._log_body)
        self._log_lay.setContentsMargins(2, 2, 2, 2)
        self._log_lay.setSpacing(8)
        self._date_label = QLabel("今天")
        self._date_label.setStyleSheet(
            "background: rgba(226, 232, 240, 210); color: #64748B;"
            " border-radius: 10px; padding: 2px 10px;")
        self._date_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._log_lay.addWidget(self._date_label, 0, Qt.AlignmentFlag.AlignHCenter)
        self._log_lay.addStretch(1)
        self._log_scroll.setWidget(self._log_body)
        self._log_rows = []
        self._typing_row = None

        self._input = ChatInput(self)
        self._input.setPlaceholderText("跟小鲸鱼娘说点什么…")
        self._input.setStyleSheet(_CHAT_INPUT_QSS)
        self._input.sendRequested.connect(self._send)
        self._input.escapePressed.connect(self._handle_escape)

        self._meme_btn = QToolButton(self)
        self._meme_btn.setText("")
        self._meme_btn.setIcon(QIcon(smiley_pixmap(22)))
        self._meme_btn.setIconSize(QSize(22, 22))
        self._meme_btn.setToolTip("表情")
        self._meme_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self._meme_btn.setStyleSheet(_CHAT_BTN_QSS)
        self._meme_btn.clicked.connect(self.toggle_drawer)

        self._send_btn = QToolButton(self)
        self._send_btn.setText("➤")
        self._send_btn.setToolTip("发送（Enter）")
        self._send_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self._send_btn.setStyleSheet(_CHAT_SEND_QSS)
        self._send_btn.clicked.connect(self._send)

        self._close_btn = QToolButton(self)
        self._close_btn.setText("×")
        self._close_btn.setToolTip("关闭（Esc）")
        self._close_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self._close_btn.setStyleSheet(_CHAT_BTN_QSS)
        self._close_btn.clicked.connect(self.close_panel)

        # 表情抽屉
        self._search = QLineEdit(self)
        self._search.setPlaceholderText("搜索描述 / 关键词…")
        self._search.setStyleSheet(_CHAT_INPUT_QSS)
        self._search.installEventFilter(self)
        self._search.textChanged.connect(self._on_search_changed)

        self._filter_btn = QToolButton(self)
        self._filter_btn.setText("筛选 ▾")
        self._filter_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self._filter_btn.setStyleSheet(_CHAT_BTN_QSS)
        self._filter_btn.clicked.connect(self._show_filter_menu)
        self._filter_actions = {}
        self._filter_menu = QMenu(self)
        group = QActionGroup(self._filter_menu)
        group.setExclusive(True)
        for tag, label in (("", "全部"),) + tuple(MEME_TAGS):
            act = self._filter_menu.addAction(label)
            act.setCheckable(True)
            act.setChecked(tag == "")
            act.triggered.connect(lambda _=False, t=tag: self._set_tag(t))
            group.addAction(act)
            self._filter_actions[tag] = act

        self._count = QLabel("共 0 张", self)
        self._count.setStyleSheet("background: transparent; color: #64748B;")
        self._count.setAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)

        self._scroll = QScrollArea(self)
        self._scroll.setFrameShape(QFrame.Shape.NoFrame)
        self._scroll.setWidgetResizable(True)
        self._scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self._scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self._scroll.setStyleSheet(_CHAT_SCROLL_QSS)
        self._scroll.viewport().setAutoFillBackground(False)
        self._scroll.verticalScrollBar().valueChanged.connect(self._sync_grid_pool)

        self._grid = MemeGrid(self._thumbs)
        self._grid.set_viewport(self._scroll.viewport())
        self._grid.cellClicked.connect(self._on_cell_clicked)
        self._grid_holder = QWidget()
        self._grid_holder.setAutoFillBackground(False)
        self._grid_holder.setAttribute(Qt.WidgetAttribute.WA_NoSystemBackground, True)
        holder_lay = QVBoxLayout(self._grid_holder)
        holder_lay.setContentsMargins(0, 0, 0, 0)
        holder_lay.setSpacing(0)
        holder_lay.addWidget(self._grid, 0, Qt.AlignmentFlag.AlignHCenter)
        holder_lay.addStretch(1)
        self._scroll.setWidget(self._grid_holder)
        self._footer_visible = False

        self._footer = QLabel("", self)
        self._footer.setStyleSheet("background: transparent; color: #64748B;")
        self._footer.setWordWrap(True)
        self._footer.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)

        self._empty_label = QLabel("没找到这类表情", self)
        self._empty_label.setStyleSheet("background: transparent; color: #64748B;")
        self._empty_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._empty_btn = QPushButton("清空筛选", self)
        self._empty_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self._empty_btn.setStyleSheet(
            "QPushButton { background: rgba(255, 255, 255, 170);"
            " border: 1px solid rgba(206, 184, 232, 210); border-radius: 9px;"
            " color: #5A4368; padding: 4px 10px; }"
            "QPushButton:hover { background: rgba(255, 255, 255, 235); }")
        self._empty_btn.clicked.connect(self._clear_filters)

        self._search_timer = QTimer(self)
        self._search_timer.setSingleShot(True)
        self._search_timer.setInterval(200)
        self._search_timer.timeout.connect(self._refresh)

        # placeholder 在浅色底上要压暗一点（QSS 的 color 管不到 placeholder）
        for edit in (self._input, self._search):
            pal = edit.palette()
            pal.setColor(QPalette.ColorRole.PlaceholderText, QColor(150, 132, 172, 190))
            edit.setPalette(pal)

        # 抽屉关着时先把这些收起来
        for w in self._drawer_widgets():
            w.hide()

    def _drawer_widgets(self):
        return (self._search, self._filter_btn, self._count, self._scroll,
                self._footer, self._empty_label, self._empty_btn)

    # ---------- 聊天记录（左她 / 右我） ----------
    def _clear_log_rows(self):
        for row in list(self._log_rows):
            try:
                row.setParent(None)
                row.deleteLater()
            except Exception:
                pass
        self._log_rows = []
        if self._typing_row is not None:
            try:
                self._typing_row.setParent(None)
                self._typing_row.deleteLater()
            except Exception:
                pass
            self._typing_row = None

    def _scroll_log_bottom(self):
        bar = self._log_scroll.verticalScrollBar()

        def go():
            try:
                bar.setValue(bar.maximum())
            except Exception:
                pass

        # 布局还没算完时 maximum 还是 0：隔一帧、40ms 各补一次，保证停在最新一条
        QTimer.singleShot(0, go)
        QTimer.singleShot(40, go)

    def add_message(self, role, text, image=None):
        row = ChatMessageRow(role, text, self.pet.bubble_font, self._log_body,
                             avatar_pm=self._avatar_pm, image=image,
                             timestamp=datetime.datetime.now().strftime("%H:%M"))
        self._log_lay.insertWidget(self._log_lay.count() - 1, row)
        self._log_rows.append(row)
        while len(self._log_rows) > 40:
            old = self._log_rows.pop(0)
            try:
                old.setParent(None)
                old.deleteLater()
            except Exception:
                pass
        if self._typing_row is not None:      # 「正在输入…」永远排最后
            self._log_lay.removeWidget(self._typing_row)
            self._log_lay.insertWidget(self._log_lay.count() - 1, self._typing_row)
        self._scroll_log_bottom()
        return row

    def set_log(self, messages):
        self._clear_log_rows()
        for item in list(messages or [])[-40:]:
            try:
                role, text = item.get("role"), item.get("text")
                image = item.get("image")
                stamp = item.get("time") or ""
            except AttributeError:
                continue
            if role in ("pet", "user") and (text or image):
                row = ChatMessageRow(role, text, self.pet.bubble_font,
                                     self._log_body, avatar_pm=self._avatar_pm,
                                     image=image, timestamp=stamp)
                self._log_lay.insertWidget(self._log_lay.count() - 1, row)
                self._log_rows.append(row)
        self._scroll_log_bottom()

    def set_typing(self, on):
        if on:
            if self._typing_row is None:
                self._typing_row = ChatMessageRow(
                    "pet", "正在输入…", self.pet.bubble_font, self._log_body,
                    avatar_pm=self._avatar_pm)
                self._log_lay.insertWidget(self._log_lay.count() - 1,
                                          self._typing_row)
                self._scroll_log_bottom()
        elif self._typing_row is not None:
            row, self._typing_row = self._typing_row, None
            try:
                row.setParent(None)
                row.deleteLater()
            except Exception:
                pass

    def _apply_fonts(self):
        base = QFont(self.pet.bubble_font) if getattr(self.pet, "bubble_font", None) \
            else QFont()
        base.setPointSizeF(11.5)
        self._input.setFont(base)
        f_small = QFont(base)
        f_small.setPointSizeF(9.0)
        f_title = QFont(base)
        f_title.setPointSizeF(16.0)
        f_title.setBold(True)
        self._title.setFont(f_title)
        self._persona.setFont(f_small)
        f_search = QFont(base)
        f_search.setPointSizeF(9.5)
        self._search.setFont(f_search)
        f_btn = QFont(f_small)
        for b in (self._filter_btn, self._send_btn, self._close_btn):
            b.setFont(f_btn)
        self._count.setFont(f_small)
        self._footer.setFont(f_small)
        self._empty_label.setFont(f_small)
        self._empty_btn.setFont(f_small)
        f_close = QFont(f_small)
        f_close.setPointSizeF(15.0)
        self._close_btn.setFont(f_close)
        f_badge = QFont(f_small)
        f_badge.setPointSizeF(8.5)
        self._badge.setFont(f_badge)
        f_date = QFont(f_small)
        f_date.setPointSizeF(8.5)
        self._date_label.setFont(f_date)

    def _relayout(self):
        w = self.width()
        self._header_avatar.setGeometry(14, 8, 40, 40)
        self._title.setGeometry(66, 7, 126, 26)
        self._badge.setGeometry(194, 10, 90, 21)
        self._persona.setGeometry(66, 33, 240, 17)
        self._close_btn.setGeometry(w - 32, 9, 22, 22)
        self._log_scroll.setGeometry(10, CHAT_HEADER_H, w - 20, CHAT_LOG_H)
        emoji_x = w - 10 - 36 - 6 - 34
        self._meme_btn.setGeometry(emoji_x, CHAT_ROW_Y + 14, 34, CHAT_ROW_H)
        self._send_btn.setGeometry(w - 10 - 36, CHAT_ROW_Y + 13, 36, 36)
        self._input.setGeometry(14, CHAT_ROW_Y, max(60, emoji_x - 6 - 14),
                                CHAT_INPUT_H)
        # 表情抽屉（面板向下展开的那一块）
        search_y = CHAT_PANEL_H + 10
        self._search.setGeometry(14, search_y, 230, 28)
        self._filter_btn.setGeometry(250, search_y, 80, 28)
        self._count.setGeometry(336, search_y, 70, 28)
        scroll_y = search_y + 36
        footer_visible = bool(self._footer_visible)
        scroll_h = CHAT_PANEL_H + CHAT_DRAWER_H - 10 - scroll_y
        if footer_visible:
            scroll_h -= 22
        self._scroll.setGeometry(14, scroll_y, w - 28, scroll_h)
        self._footer.setGeometry(14, scroll_y + scroll_h + 2, w - 28, 18)
        self._empty_label.setGeometry(14, scroll_y + 70, w - 28, 24)
        self._empty_btn.setGeometry(14 + (w - 28 - 92) // 2, scroll_y + 108, 92, 30)
        if getattr(self, "_grid", None) is not None:
            self._grid.sync_pool()

    def _apply_height(self):
        h = CHAT_PANEL_H + (CHAT_DRAWER_H if self._drawer_open else 0)
        self.resize(CHAT_PANEL_W, h)
        self._relayout()
        if self.isVisible():
            self._place(keep_top=True)
        if getattr(self, "_grid", None) is not None:
            QTimer.singleShot(0, self._grid.sync_pool)

    # ---------- 开关 / 跟随 ----------
    def refresh_persona(self):
        name = self.pet.chat_persona_name()
        font_sig = str(getattr(self.pet, "bubble_font_key", ""))
        if name != self._persona_cache:
            self._persona_cache = name
            self._persona.setText(name + " · 在线")
        if font_sig != self._font_sig:
            self._font_sig = font_sig
            self._apply_fonts()
            self.set_log(getattr(self.pet, "_chat_ui_log", []))

    def show_panel(self):
        self.refresh_persona()
        if self._guard is None:
            self._guard = self.pet._ui_guard()
            self._guard.__enter__()
        if not self.isVisible():
            self._apply_height()
            self._place(keep_top=False)
            self.show()
        else:
            self._apply_height()
        self.set_log(getattr(self.pet, "_chat_ui_log", []))
        if not self._log_rows:
            self.add_message("pet", "主人，今天想聊点什么呀？")
        self.set_typing(bool(getattr(self.pet, "_chat_ui_typing", False)))
        if self._drawer_open:
            self._refresh()
            self._search.setFocus()
        else:
            self._input.setFocus()
        self.raise_()
        self.activateWindow()
        self.update()

    def close_panel(self):
        self._search_timer.stop()
        if self.isVisible():
            self.hide()
        self._pinned = False
        self._release_guard()

    def _release_guard(self):
        guard, self._guard = self._guard, None
        if guard is not None:
            try:
                guard.__exit__(None, None, None)
            except Exception:
                pass

    def toggle_drawer(self):
        self._drawer_open = not self._drawer_open
        if self._drawer_open:
            self._search.show()
            self._filter_btn.show()
            self._count.show()
            self._refresh()
            self._search.setFocus()
        else:
            for w in self._drawer_widgets():
                w.hide()
            self._input.setFocus()
        self._apply_height()

    def follow_pet(self):
        if self.isVisible():
            self._place(keep_top=False)

    def tick_follow(self):
        """主循环每帧调一次：跟着桌宠走 / 桌宠藏了就收起来 / 性格换了就更新名字。"""
        if not self.isVisible():
            return
        if not self.pet.isVisible():
            self.close_panel()
            return
        self.refresh_persona()
        # 展开表情抽屉 / 手动拖过之后不再自动回到"桌宠上方"，免得一点 😊 就跳到下面
        self._place(keep_top=self._drawer_open or self._pinned)

    def _place(self, keep_top=False):
        pet = self.pet
        try:
            screen = pet.screen() or QApplication.primaryScreen()
            geo = screen.availableGeometry()
        except Exception:
            return
        w, h = self.width(), self.height()
        if keep_top:
            x, y = self.x(), self.y()
        else:
            x = pet.x() + pet.width() // 2 - w // 2
            y = pet.y() - h - 6
            if y < geo.top():
                y = pet.y() + pet.height() + 6
        x = max(geo.left(), min(geo.right() - w + 1, x))
        y = max(geo.top(), min(geo.bottom() - h + 1, y))
        if (x, y) != (self.x(), self.y()):
            self.move(int(x), int(y))
        self._last_pos = (pet.x(), pet.y())

    # ---------- 搜索 / 筛选 ----------
    def _on_search_changed(self, _text):
        self._search_timer.start()

    def _sync_grid_pool(self, *_args):
        grid = getattr(self, "_grid", None)
        if grid is not None:
            grid.sync_pool()

    def _show_filter_menu(self):
        self._filter_menu.popup(self._filter_btn.mapToGlobal(
            QPoint(0, self._filter_btn.height() + 2)))

    def _set_tag(self, tag):
        self._tag = tag or ""
        for t, act in self._filter_actions.items():
            act.setChecked(t == self._tag)
        self._refresh()

    def _clear_filters(self):
        self._search.blockSignals(True)
        self._search.clear()
        self._search.blockSignals(False)
        self._search_timer.stop()
        self._tag = ""
        for t, act in self._filter_actions.items():
            act.setChecked(t == "")
        self._refresh()

    def _refresh(self):
        """按（tag + 关键词）过滤内存里的索引；一次最多交给网格 200 张。"""
        try:
            items = self.pet.meme_items()
        except Exception:
            items = []
        tag = self._tag
        needle = self._search.text().strip().lower()
        matched = []
        for item in items:
            if tag and item[1] != tag:
                continue
            if needle:
                hay = (item[2] + " " + item[3]).lower()
                if needle not in hay:
                    continue
            matched.append(item)
        self._filtered = matched
        total = len(matched)
        self._shown = matched[:MEME_GRID_LIMIT]
        self._grid.set_items(self._shown)
        self._count.setText("共 %d 张" % total)
        extra = total - len(self._shown)
        self._footer_visible = extra > 0
        if self._footer_visible:
            self._footer.setText(
                "只画了前 %d 张，还有 %d 张 —— 用搜索或筛选取一部分"
                % (len(self._shown), extra))
        self._footer.setVisible(self._footer_visible)
        empty = total == 0
        self._scroll.setVisible(not empty)
        self._empty_label.setVisible(empty)
        self._empty_btn.setVisible(empty)
        self._relayout()

    # ---------- 发送 / 点表情 ----------
    def _send(self):
        text = self._input.toPlainText().strip()
        if not text:
            return
        self._input.clear()
        self.pet.send_chat(text)
        self._input.setFocus()

    def _on_cell_clicked(self, index):
        if 0 <= index < len(self._shown):
            path, _tag, caption, _keywords = self._shown[index]
            # 先把自己发的这张挂出来，过一会儿她回一张（不污染聊天历史）
            self.pet.send_meme(path, caption)

    # ---------- 键盘 ----------
    def _handle_escape(self):
        if self._drawer_open:
            self.toggle_drawer()
            self._input.setFocus()
        else:
            self.close_panel()

    def keyPressEvent(self, ev):
        if ev.key() == Qt.Key.Key_Escape:
            self._handle_escape()
            return
        super().keyPressEvent(ev)

    def eventFilter(self, obj, ev):
        if ev.type() == QEvent.Type.KeyPress and ev.key() == Qt.Key.Key_Escape:
            self.keyPressEvent(ev)
            return True
        if obj is self._search and ev.type() == QEvent.Type.KeyPress \
                and ev.key() in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
            self._search_timer.stop()
            self._refresh()
            return True
        return super().eventFilter(obj, ev)

    # ---------- 拖动（整个标题区） ----------
    def mousePressEvent(self, ev):
        if ev.button() == Qt.MouseButton.LeftButton \
                and ev.position().y() <= CHAT_HEADER_H:
            self._dragging = True
            self._pinned = True              # 手动挪过之后就不再自动跟着桌宠跑
            self._drag_off = (ev.globalPosition().toPoint()
                              - self.frameGeometry().topLeft())
            ev.accept()
            return
        super().mousePressEvent(ev)

    def mouseMoveEvent(self, ev):
        if self._dragging:
            self.move(ev.globalPosition().toPoint() - self._drag_off)
            ev.accept()
            return
        super().mouseMoveEvent(ev)

    def mouseReleaseEvent(self, ev):
        if ev.button() == Qt.MouseButton.LeftButton and self._dragging:
            self._dragging = False
            ev.accept()
            return
        super().mouseReleaseEvent(ev)

    # ---------- 绘制 ----------
    def paintEvent(self, _ev):
        """白玻璃底 + 很淡的靛紫光晕 + 圆角描边（照着 modern_chat_interface 的感觉）。"""
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        rect = QRectF(self.rect()).adjusted(0.5, 0.5, -0.5, -0.5)
        path = QPainterPath()
        path.addRoundedRect(rect, CHAT_RADIUS, CHAT_RADIUS)
        grad = QLinearGradient(0, 0, 0, self.height())
        grad.setColorAt(0.0, QColor(255, 255, 255, 246))
        grad.setColorAt(0.55, QColor(248, 250, 252, 243))
        grad.setColorAt(1.0, QColor(241, 245, 249, 244))
        p.fillPath(path, grad)
        p.save()
        p.setClipPath(path)
        w, h = float(self.width()), float(self.height())
        p.setPen(Qt.PenStyle.NoPen)
        # 背景里两团很淡的靛紫光（替代插画背景）
        for cx, cy, rr, col in ((0.20, 0.18, 150, QColor(99, 102, 241, 20)),
                                (0.82, 0.10, 130, QColor(139, 92, 246, 18)),
                                (0.52, 0.46, 180, QColor(59, 130, 246, 12))):
            p.setBrush(col)
            p.drawEllipse(QPointF(w * cx, h * cy), rr, rr)
        p.fillRect(QRectF(0, 0, w, CHAT_HEADER_H), QColor(255, 255, 255, 90))
        p.restore()
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(QPen(QColor(203, 213, 225, 230), 1.2))
        p.drawPath(path)
        p.setPen(QPen(QColor(226, 232, 240, 255), 1))
        p.drawLine(QPointF(16, CHAT_HEADER_H - 1), QPointF(w - 16, CHAT_HEADER_H - 1))
        p.end()

    def resizeEvent(self, ev):
        self._relayout()
        super().resizeEvent(ev)

    def closeEvent(self, ev):
        self._search_timer.stop()
        self._release_guard()
        super().closeEvent(ev)


