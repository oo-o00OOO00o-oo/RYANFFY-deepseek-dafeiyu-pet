# -*- coding: utf-8 -*-
"""聊天面板 / 表情抽屉的界面层：星空幻彩/粉彩双风格聊天面板、立体阴影、左右消息气泡、头像、5 列格子池。

从 桌宠.py 拆出来（2026-10-23）。本模块不 import 桌宠.py，只反过来被它 import；
需要桌宠的东西（字体 / 形象 / 发消息 / 气泡主题）全部通过 `self.pet` 调，
表情索引通过 `pet.meme_items()`（这样 monkeypatch 桌宠.MEME_ROOT 仍然生效）。
"""
from collections import OrderedDict
import datetime
import math
import os

from PySide6.QtCore import (Qt, QTimer, QPoint, QPointF, QRect, QRectF, QSize,
                            Signal, QEvent)
from PySide6.QtGui import (QPainter, QPixmap, QImage, QImageReader, QFont, QColor,
                           QIcon, QFontMetrics, QPen, QPalette, QPainterPath,
                           QLinearGradient, QTextDocument, QActionGroup, QPolygonF)
from PySide6.QtWidgets import (QApplication, QWidget, QLabel, QToolButton, QLineEdit,
                               QScrollArea, QFrame, QVBoxLayout, QPushButton, QMenu,
                               QTextEdit)

from meme_store import MEME_TAGS


# ---------- 聊天面板 + 表情抽屉 ----------
# 面板是无边框置顶小窗：星空夜空/梦幻粉彩底板 + 胶囊输入栏；点 😊 往下展开表情网格（5 列）。
# 网格只在 paintEvent 里解码"可见 + 上下各预取 1 行"的缩略图，缓存 LRU 80 张 ——
# 434 张图一次性解码会卡住界面好几秒，这条是硬约束。
CHAT_PANEL_W = 440
CHAT_HEADER_H = 64
CHAT_LOG_H = 340
CHAT_INPUT_H = 50
CHAT_ROW_Y = CHAT_HEADER_H + CHAT_LOG_H + 12   # 64 + 340 + 12 = 416
CHAT_ROW_H = 36
CHAT_PANEL_H = CHAT_ROW_Y + CHAT_INPUT_H + 16  # 416 + 50 + 16 = 482
CHAT_DRAWER_H = 320
CHAT_RADIUS = 20
SHADOW_PAD = 12

MEME_GRID_COLS = 5
MEME_CELL = 66
MEME_GRID_GAP = 8
MEME_GRID_LIMIT = 200            # 一次最多渲染 200 个格子（再多也没人翻）
MEME_THUMB_CACHE_MAX = 80        # 缩略图 LRU 上限
MEME_GRID_W = MEME_GRID_COLS * MEME_CELL + (MEME_GRID_COLS - 1) * MEME_GRID_GAP  # 362

# 确定性星空散点与星芒（保证重绘时不闪烁）
_STARRY_STARS = (
    (0.06, 0.08, 2.0, 220, True),
    (0.15, 0.05, 1.4, 180, False),
    (0.24, 0.12, 1.8, 210, False),
    (0.38, 0.06, 2.6, 255, True),
    (0.52, 0.10, 1.6, 190, False),
    (0.65, 0.04, 2.2, 230, True),
    (0.76, 0.12, 1.5, 170, False),
    (0.88, 0.06, 2.4, 240, True),
    (0.94, 0.14, 1.6, 180, False),
    (0.08, 0.22, 1.6, 170, False),
    (0.18, 0.32, 2.2, 220, True),
    (0.82, 0.22, 2.0, 210, True),
    (0.92, 0.30, 1.5, 160, False),
    (0.05, 0.45, 1.8, 190, False),
    (0.95, 0.48, 2.0, 220, True),
    (0.07, 0.65, 2.2, 230, True),
    (0.93, 0.66, 1.8, 180, False),
    (0.12, 0.82, 2.0, 200, True),
    (0.25, 0.92, 1.6, 180, False),
    (0.42, 0.85, 2.4, 240, True),
    (0.60, 0.94, 1.5, 170, False),
    (0.78, 0.88, 2.2, 220, True),
    (0.90, 0.84, 1.8, 190, False),
)

_CHAT_IMG_CACHE = {}


class OpaqueViewport(QWidget):
    """聊天记录的滚动视口：自己把底色画满。

    透明顶层窗口 + QScrollArea 在 Windows 上会把 viewport 没画到的像素留成 alpha=0，
    桌面/别的窗口就直接透出来（用户看到的「镂空」）。这里不依赖 palette / 样式表，
    每次 paintEvent 先填实色，保证聊天记录区永远不透明。
    """

    def __init__(self, parent=None, color=None):
        super().__init__(parent)
        self._color = QColor(color) if color is not None else QColor(12, 15, 38)
        self.setAutoFillBackground(False)
        self.setAttribute(Qt.WidgetAttribute.WA_OpaquePaintEvent, True)

    def set_color(self, color):
        self._color = QColor(color)
        self.update()

    def paintEvent(self, ev):
        p = QPainter(self)
        p.fillRect(self.rect(), self._color)
        p.end()
        super().paintEvent(ev)


class OpaqueScrollArea(QScrollArea):
    """带自定义不透明 viewport 的 QScrollArea（见 OpaqueViewport 的说明）。"""

    def __init__(self, parent=None):
        super().__init__(parent)
        self._bg = QColor(12, 15, 38)
        self.setViewport(OpaqueViewport(self, self._bg))

    def set_background(self, color):
        self._bg = QColor(color)
        self.viewport().set_color(color)
        self.viewport().update()

    def paintEvent(self, ev):
        p = QPainter(self)
        p.fillRect(self.rect(), self._bg)
        p.end()
        super().paintEvent(ev)


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


def smiley_pixmap(size=24):
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
    """表情缩略图缓存：按需解码 + LRU 80 张。"""

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
            self._data.popitem(last=False)
        return pm

    @staticmethod
    def _decode(path, size):
        try:
            reader = QImageReader(str(path))
            reader.setAutoTransform(True)
            src = reader.size()
            if src.isValid() and src.width() > 0 and src.height() > 0:
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
        self.content_changes = 0
        self.setFixedSize(MEME_CELL, MEME_CELL)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setAutoFillBackground(False)
        self.setAttribute(Qt.WidgetAttribute.WA_NoSystemBackground, True)

    def set_item(self, index, item):
        self._index = int(index)
        path = item[0]
        if path != self._path:
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
        path.addRoundedRect(rect, 10, 10)
        p.setPen(Qt.PenStyle.NoPen)
        # 兼容深色/浅色底色
        starry = self.grid.is_starry()
        cell_bg = QColor(25, 30, 72, 210) if starry else QColor(255, 255, 255, 235)
        p.fillPath(path, cell_bg)
        if self._pm is not None and not self._pm.isNull():
            p.setClipPath(path)
            dx = (self.width() - self._pm.width()) // 2
            dy = (self.height() - self._pm.height()) // 2
            p.drawPixmap(dx, dy, self._pm)
        else:
            p.setPen(QColor(148, 163, 184))
            p.drawText(rect, Qt.AlignmentFlag.AlignCenter, "?")
        if self._hover:
            p.setBrush(Qt.BrushStyle.NoBrush)
            hover_border = QColor(165, 180, 252, 240) if starry else QColor(99, 102, 241, 230)
            p.setPen(QPen(hover_border, 2.0))
            p.drawPath(path)
        else:
            p.setBrush(Qt.BrushStyle.NoBrush)
            edge_border = QColor(147, 165, 245, 60) if starry else QColor(226, 232, 240, 200)
            p.setPen(QPen(edge_border, 1.0))
            p.drawPath(path)
        p.end()

    def enterEvent(self, ev):
        self._hover = True
        self.update()
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
    """固定格子池的 5 列网格：控件数由视口大小决定，滚动时循环复用。"""

    cellClicked = Signal(int)

    def __init__(self, thumbs, parent=None):
        super().__init__(parent)
        self._thumbs = thumbs
        self._items = []
        self._viewport = None
        self._pool = []
        self._pool_rows = 0
        self._cells = {}
        self.setFixedWidth(MEME_GRID_W)
        self.setAutoFillBackground(False)
        self.setAttribute(Qt.WidgetAttribute.WA_OpaquePaintEvent, True)
        self.setAttribute(Qt.WidgetAttribute.WA_NoSystemBackground, False)

    @property
    def thumbs(self):
        return self._thumbs

    def is_starry(self):
        p = self.parent()
        while p is not None:
            if hasattr(p, "_is_starry_theme"):
                return p._is_starry_theme()
            p = p.parent()
        return True

    def set_items(self, items):
        self._items = list(items or [])
        rows = (len(self._items) + MEME_GRID_COLS - 1) // MEME_GRID_COLS
        h = rows * MEME_CELL + max(0, rows - 1) * MEME_GRID_GAP
        self.setFixedHeight(max(0, h))
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
        first = max(0, first_vis - 1)
        last = min(rows - 1, last_vis + 1)
        return first_vis, last_vis, first, last, rows

    def _pool_row_count(self):
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

    def sync_pool(self):
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

    def paintEvent(self, _ev):
        # 格子之间的空隙也要填实色：透明窗口下不填会直接看到桌面。
        p = QPainter(self)
        p.fillRect(self.rect(),
                   QColor(12, 15, 38) if self.is_starry() else QColor(248, 250, 252))
        p.end()

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
                super().keyPressEvent(ev)
            else:
                self.sendRequested.emit()
            return
        if ev.key() == Qt.Key.Key_Escape:
            self.escapePressed.emit()
            return
        super().keyPressEvent(ev)


_PET_AVATAR_CACHE = []


def pet_avatar_pixmap(source, size=40):
    """聊天记录里她的小头像：从桌宠立绘裁一个圆头像（source 由 PetWindow 提供）。"""
    if source is None or source.isNull():
        return None
    size = int(size)
    if _PET_AVATAR_CACHE and _PET_AVATAR_CACHE[0].width() == size:
        return _PET_AVATAR_CACHE[0]
    pm = source
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
    """圆形头像：她 = 现有立绘；我 = 现代清爽渐变 + 「你」。"""

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
            p.fillPath(path, QColor(30, 36, 78))
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
        p.setPen(QPen(QColor(165, 180, 252, 220), 2.0))
        p.drawEllipse(rect)
        p.end()


class ChatMessageRow(QWidget):
    """聊天记录的一行：左边她、右边我 + 圆头像。支持文本气泡与表情卡片。"""

    def __init__(self, role, text, font, parent=None, avatar_pm=None,
                 image=None, timestamp=""):
        super().__init__(parent)
        self.role = role
        self.image = image
        self.avatar = AvatarWidget(role, 38, self, avatar_pm=avatar_pm)
        f = QFont(font)
        f.setPointSizeF(11.0)
        self._font = f
        
        starry = True
        p_obj = parent
        while p_obj is not None:
            if hasattr(p_obj, "_is_starry_theme"):
                starry = p_obj._is_starry_theme()
                break
            p_obj = p_obj.parent()

        if image:
            self._build_image_row(role, str(text or ""), f, starry)
        else:
            self.label = QLabel(str(text or ""), self)
            self.label.setWordWrap(True)
            self.label.setFont(f)
            if starry:
                self.label.setStyleSheet(
                    "QLabel { background: rgba(30, 36, 78, 240);"
                    " border: 1px solid rgba(147, 165, 245, 0.45);"
                    " border-top-left-radius: 4px; border-top-right-radius: 16px;"
                    " border-bottom-right-radius: 16px; border-bottom-left-radius: 16px;"
                    " color: #F1F5F9; padding: 9px 13px; font-size: 13px; }"
                    if role == "pet" else
                    "QLabel { background: qlineargradient(x1:0, y1:0, x2:1, y2:1,"
                    " stop:0 #6366F1, stop:1 #8B5CF6);"
                    " border: 1px solid rgba(255, 255, 255, 0.40);"
                    " border-top-left-radius: 16px; border-top-right-radius: 4px;"
                    " border-bottom-left-radius: 16px; border-bottom-right-radius: 16px;"
                    " color: #FFFFFF; padding: 9px 13px; font-size: 13px; }")
            else:
                self.label.setStyleSheet(
                    "QLabel { background: #FFFFFF; border: 1px solid #E2E8F0;"
                    " border-top-left-radius: 4px; border-top-right-radius: 16px;"
                    " border-bottom-right-radius: 16px; border-bottom-left-radius: 16px;"
                    " color: #1E293B; padding: 9px 13px; font-size: 13px; }"
                    if role == "pet" else
                    "QLabel { background: qlineargradient(x1:0, y1:0, x2:1, y2:1,"
                    " stop:0 #3B82F6, stop:1 #2563EB); border: none;"
                    " border-top-left-radius: 16px; border-top-right-radius: 4px;"
                    " border-bottom-left-radius: 16px; border-bottom-right-radius: 16px;"
                    " color: #FFFFFF; padding: 9px 13px; font-size: 13px; }")
            self.label.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
            self.bubble = self.label
            self._bw, self._bh = self._measure(str(text or ""), f)
            self.label.setFixedSize(self._bw, self._bh)

        self._time_h = 0
        self.time_label = QLabel(str(timestamp or ""), self)
        f_time = QFont(f)
        f_time.setPointSizeF(8.5)
        self.time_label.setFont(f_time)
        self.time_label.setStyleSheet("background: transparent; color: #94A3B8; border: none;")
        if timestamp:
            self._time_h = 14
            self.time_label.show()
        else:
            self.time_label.hide()
        self.setFixedHeight(max(40, self._bh + self._time_h + 4) + 8)
        self._place()

    def _build_image_row(self, role, caption, font, starry):
        pm = chat_image_pixmap(self.image)
        img_w = pm.width() if pm is not None else 0
        img_h = pm.height() if pm is not None else 0
        fm = QFontMetrics(font)
        cap_w = (min(240, max(70, fm.horizontalAdvance(caption) + 12)) if caption else 0)
        box_w = min(270, max(img_w, cap_w) + 16)
        cap_h = 0
        if caption:
            doc = QTextDocument()
            doc.setDefaultFont(font)
            doc.setPlainText(caption)
            doc.setTextWidth(max(20, box_w - 16))
            cap_h = int(doc.size().height()) + 2
        box_h = img_h + (cap_h + 6 if caption else 0) + 16

        self.container = QWidget(self)
        self.container.setObjectName("card")
        if starry:
            card_qss = (
                "QWidget#card { background: rgba(30, 36, 78, 240);"
                " border: 1px solid rgba(147, 165, 245, 0.45);"
                " border-top-left-radius: 4px; border-top-right-radius: 16px;"
                " border-bottom-right-radius: 16px; border-bottom-left-radius: 16px; }"
                if role == "pet" else
                "QWidget#card { background: qlineargradient(x1:0, y1:0, x2:1, y2:1,"
                " stop:0 #6366F1, stop:1 #8B5CF6);"
                " border: 1px solid rgba(255, 255, 255, 0.40);"
                " border-top-left-radius: 16px; border-top-right-radius: 4px;"
                " border-bottom-left-radius: 16px; border-bottom-right-radius: 16px; }")
        else:
            card_qss = (
                "QWidget#card { background: #FFFFFF; border: 1px solid #E2E8F0;"
                " border-top-left-radius: 4px; border-top-right-radius: 16px;"
                " border-bottom-right-radius: 16px; border-bottom-left-radius: 16px; }"
                if role == "pet" else
                "QWidget#card { background: qlineargradient(x1:0, y1:0, x2:1, y2:1,"
                " stop:0 #3B82F6, stop:1 #2563EB); border: none;"
                " border-top-left-radius: 16px; border-top-right-radius: 4px;"
                " border-bottom-left-radius: 16px; border-bottom-right-radius: 16px; }")
        self.container.setStyleSheet(card_qss)

        lay = QVBoxLayout(self.container)
        lay.setContentsMargins(8, 8, 8, 8)
        lay.setSpacing(4)
        self.image_label = QLabel(self.container)
        self.image_label.setStyleSheet("background: transparent; border: none;")
        if pm is not None and not pm.isNull():
            self.image_label.setPixmap(pm)
            self.image_label.setFixedSize(pm.size())
        else:
            self.image_label.setText("图片未找到")
            self.image_label.setStyleSheet("background: transparent; color: #94A3B8; border: none;")
        lay.addWidget(self.image_label, 0, Qt.AlignmentFlag.AlignHCenter)

        self.label = QLabel(caption, self.container)
        self.label.setWordWrap(True)
        self.label.setFont(font)
        self.label.setStyleSheet("background: transparent; border: none; color: %s;"
                                 % ("#FFFFFF" if role == "user" else ("#F1F5F9" if starry else "#64748B")))
        if caption:
            self.label.setFixedWidth(max(20, box_w - 16))
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
        max_w = 265
        if not text:
            return 70, fm.height() + 20
        text_w = min(max_w, fm.horizontalAdvance(text) + 40)
        text_w = max(86, text_w)
        doc = QTextDocument()
        doc.setDefaultFont(font)
        doc.setPlainText(text)
        doc.setTextWidth(max(20, text_w - 24))
        return text_w, int(doc.size().height()) + 20

    def _place(self):
        if self.role == "pet":
            self.avatar.move(6, 4)
            self.bubble.move(50, 4)
            self.time_label.move(54, 4 + self._bh + 2)
            self.time_label.setGeometry(54, 4 + self._bh + 2, self._bw, 14)
            self.time_label.setAlignment(Qt.AlignmentFlag.AlignLeft)
        else:
            self.avatar.move(max(6, self.width() - 44), 4)
            bx = max(6, self.width() - 52 - self._bw)
            self.bubble.move(bx, 4)
            self.time_label.setGeometry(bx, 4 + self._bh + 2, self._bw - 4, 14)
            self.time_label.setAlignment(Qt.AlignmentFlag.AlignRight)

    def resizeEvent(self, ev):
        self._place()
        super().resizeEvent(ev)


class ChatPanel(QWidget):
    """QQ/微信风现代亚克力星空聊天面板：双风格星空/梦幻渐变底板 + 舒适视界 + 左右气泡 + 头像 + 😊 表情抽屉（非模态）。"""

    def __init__(self, pet):
        super().__init__(None, Qt.WindowType.FramelessWindowHint
                         | Qt.WindowType.Tool
                         | Qt.WindowType.WindowStaysOnTopHint)
        self.pet = pet
        self._avatar_pm = None
        try:
            self._avatar_pm = pet.chat_avatar_pixmap(40)
        except Exception:
            pass
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setWindowOpacity(1.0)
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
        self._starry_tile_cache = None
        
        self._build_ui()
        self.resize(CHAT_PANEL_W, CHAT_PANEL_H)
        self._apply_theme_styles()
        self._relayout()

    def _is_starry_theme(self):
        """检测当前是否使用星空主题风格。默认与桌宠气泡风格保持一致。"""
        try:
            if hasattr(self.pet, "_bubble_theme") and callable(self.pet._bubble_theme):
                return self.pet._bubble_theme() == "starry"
            return getattr(self.pet, "bubble_style", "starry") == "starry"
        except Exception:
            return True

    def _starry_tile_pixmap(self):
        """加载桌宠自带的星空平铺图。"""
        if self._starry_tile_cache is not None:
            return self._starry_tile_cache if self._starry_tile_cache is not False else None
        tile = None
        try:
            for p in (
                os.path.join(os.path.dirname(os.path.abspath(__file__)), "assets", "bubble", "starry_tile.png"),
                os.path.join(os.path.dirname(os.path.abspath(__file__)), "bubble", "starry_tile.png"),
            ):
                if os.path.isfile(p):
                    pm = QPixmap(p)
                    if not pm.isNull():
                        tile = pm
                        break
        except Exception:
            pass
        self._starry_tile_cache = tile if tile is not None else False
        return tile

    # ---------- 界面 ----------
    def _build_ui(self):
        self._header_avatar = AvatarWidget("pet", 40, self, avatar_pm=self._avatar_pm)
        self._header_avatar.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)

        self._title = QLabel("小鲸鱼娘", self)
        self._title.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        self._title.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)

        self._badge = QLabel("桌宠伴侣", self)
        self._badge.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._badge.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)

        self._persona = QLabel("● 在线 · 温柔模式", self)
        self._persona.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        self._persona.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)

        # 聊天记录区域
        self._log_scroll = OpaqueScrollArea(self)
        self._log_scroll.setFrameShape(QFrame.Shape.NoFrame)
        self._log_scroll.setWidgetResizable(True)
        self._log_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self._log_scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self._log_scroll.setStyleSheet(
            "QScrollArea { background: transparent; border: none; }"
            "QScrollBar:vertical { background: transparent; width: 6px; margin: 2px 0px; }"
            "QScrollBar::handle:vertical { background: rgba(147, 165, 245, 0.40); border-radius: 3px; min-height: 28px; }"
            "QScrollBar::handle:vertical:hover { background: rgba(165, 180, 252, 0.80); }"
            "QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; }"
            "QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical { background: none; }")
        # 聊天记录区用实色背景，不能依赖父控件 paintEvent 衬底，否则在某些 Qt 风格 /
        # 透明窗口组合下会透出背景图或桌面。
        self._log_scroll.viewport().setObjectName("logViewport")
        self._log_scroll.viewport().setAutoFillBackground(True)
        self._log_body = QWidget()
        self._log_body.setObjectName("logBody")
        self._log_body.setAutoFillBackground(True)
        # 关键：这里不能设 WA_OpaquePaintEvent。设了之后 Qt 认为 body 会自己画满，
        # 但 body 只画了消息行，空出来的区域 alpha=0，透明窗口就把桌面透出来了。
        self._log_body.setAttribute(Qt.WidgetAttribute.WA_OpaquePaintEvent, False)
        self._log_body.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, False)
        self._log_lay = QVBoxLayout(self._log_body)
        self._log_lay.setContentsMargins(4, 4, 4, 4)
        self._log_lay.setSpacing(10)
        self._date_label = QLabel("今天")
        self._date_label.setObjectName("dateLabel")
        self._date_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._log_lay.addWidget(self._date_label, 0, Qt.AlignmentFlag.AlignHCenter)
        self._log_lay.addStretch(1)
        self._log_scroll.setWidget(self._log_body)
        self._log_rows = []
        self._typing_row = None

        # 底部统一输入胶囊底座
        self._input_capsule = QFrame(self)
        self._input_capsule.setObjectName("inputCapsule")

        self._input = ChatInput(self)
        self._input.setPlaceholderText("跟小鲸鱼娘聊点什么吧… (Enter发送, Shift+Enter换行)")
        self._input.sendRequested.connect(self._send)
        self._input.escapePressed.connect(self._handle_escape)

        self._meme_btn = QToolButton(self)
        self._meme_btn.setText("")
        self._meme_btn.setIcon(QIcon(smiley_pixmap(24)))
        self._meme_btn.setIconSize(QSize(24, 24))
        self._meme_btn.setToolTip("表情包")
        self._meme_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self._meme_btn.clicked.connect(self.toggle_drawer)

        self._send_btn = QToolButton(self)
        self._send_btn.setText("➤")
        self._send_btn.setToolTip("发送（Enter）")
        self._send_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self._send_btn.clicked.connect(self._send)

        self._close_btn = QToolButton(self)
        self._close_btn.setText("×")
        self._close_btn.setToolTip("关闭（Esc）")
        self._close_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self._close_btn.clicked.connect(self.close_panel)

        self._clear_btn = QToolButton(self)
        self._clear_btn.setText("🧹")
        self._clear_btn.setToolTip("清空聊天记忆")
        self._clear_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self._clear_btn.clicked.connect(self._confirm_clear_history)

        # 表情抽屉
        self._search = QLineEdit(self)
        self._search.setPlaceholderText("搜索表情关键词…")
        self._search.installEventFilter(self)
        self._search.textChanged.connect(self._on_search_changed)

        self._filter_btn = QToolButton(self)
        self._filter_btn.setText("筛选 ▾")
        self._filter_btn.setCursor(Qt.CursorShape.PointingHandCursor)
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
        self._count.setAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)

        self._scroll = OpaqueScrollArea(self)
        self._scroll.setFrameShape(QFrame.Shape.NoFrame)
        self._scroll.setWidgetResizable(True)
        self._scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self._scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self._scroll.setStyleSheet(
            "QScrollArea { background: transparent; border: none; }"
            "QScrollBar:vertical { background: transparent; width: 6px; margin: 2px 0px; }"
            "QScrollBar::handle:vertical { background: rgba(147, 165, 245, 0.40); border-radius: 3px; min-height: 28px; }"
            "QScrollBar::handle:vertical:hover { background: rgba(165, 180, 252, 0.80); }"
            "QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; }"
            "QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical { background: none; }")
        self._scroll.viewport().setAutoFillBackground(False)
        self._scroll.verticalScrollBar().valueChanged.connect(self._sync_grid_pool)

        self._grid = MemeGrid(self._thumbs)
        self._grid.set_viewport(self._scroll.viewport())
        self._grid.cellClicked.connect(self._on_cell_clicked)
        self._grid_holder = QWidget()
        self._grid_holder.setObjectName("gridHolder")
        self._grid_holder.setAutoFillBackground(True)
        self._grid_holder.setAttribute(Qt.WidgetAttribute.WA_NoSystemBackground, False)
        holder_lay = QVBoxLayout(self._grid_holder)
        holder_lay.setContentsMargins(0, 0, 0, 0)
        holder_lay.setSpacing(0)
        holder_lay.addWidget(self._grid, 0, Qt.AlignmentFlag.AlignHCenter)
        holder_lay.addStretch(1)
        self._scroll.setWidget(self._grid_holder)
        self._footer_visible = False

        self._footer = QLabel("", self)
        self._footer.setWordWrap(True)
        self._footer.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)

        self._empty_label = QLabel("没有找到相关表情", self)
        self._empty_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._empty_btn = QPushButton("清空筛选", self)
        self._empty_btn.setObjectName("emptyBtn")
        self._empty_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self._empty_btn.clicked.connect(self._clear_filters)

        self._search_timer = QTimer(self)
        self._search_timer.setSingleShot(True)
        self._search_timer.setInterval(200)
        self._search_timer.timeout.connect(self._refresh)

        # 抽屉关着时隐藏抽屉控件
        for w in self._drawer_widgets():
            w.hide()

    def _set_log_bg(self, color):
        """给聊天记录滚动区及其内容容器一个实色背景，防止透出父窗口或背景图。"""
        for w in (self._log_scroll.viewport(), self._log_body):
            if w is None:
                continue
            pal = w.palette()
            pal.setColor(QPalette.ColorRole.Window, color)
            pal.setColor(QPalette.ColorRole.Base, color)
            w.setPalette(pal)
            w.setAutoFillBackground(True)

    def _apply_theme_styles(self):
        starry = self._is_starry_theme()
        if starry:
            # 星空主题
            self._title.setStyleSheet("background: transparent; color: #FFFFFF; font-weight: bold;")
            self._badge.setStyleSheet(
                "background: rgba(99, 102, 241, 0.35); color: #C7D2FE;"
                " border: 1px solid rgba(165, 180, 252, 0.55); border-radius: 10px;"
                " font-size: 10px; font-weight: 500; padding: 1px 7px;")
            self._persona.setStyleSheet("background: transparent; color: #4ADE80; font-size: 11px;")
            self._close_btn.setStyleSheet(
                "QToolButton { background: rgba(255, 255, 255, 0.12);"
                " border: 1px solid rgba(165, 180, 252, 0.35); border-radius: 13px;"
                " color: #CBD5E1; font-size: 16px; font-weight: bold; padding: 0px; }"
                "QToolButton:hover { background: rgba(239, 68, 68, 0.40); color: #FFAAAA; border-color: rgba(239, 68, 68, 0.80); }"
                "QToolButton:pressed { background: rgba(239, 68, 68, 0.60); }")
            self._clear_btn.setStyleSheet(
                "QToolButton { background: rgba(255, 255, 255, 0.12);"
                " border: 1px solid rgba(165, 180, 252, 0.35); border-radius: 13px;"
                " color: #CBD5E1; font-size: 13px; font-weight: bold; padding: 0px; }"
                "QToolButton:hover { background: rgba(245, 158, 11, 0.35); color: #FDE68A; border-color: rgba(245, 158, 11, 0.70); }"
                "QToolButton:pressed { background: rgba(245, 158, 11, 0.55); }")
            self._date_label.setStyleSheet(
                "QLabel#dateLabel { background: rgba(30, 36, 78, 200); color: #94A3B8;"
                " border: 1px solid rgba(147, 165, 245, 0.30);"
                " border-radius: 11px; padding: 2px 14px; font-size: 11px; font-weight: 500; }")
            self._input_capsule.setStyleSheet(
                "QFrame#inputCapsule { background: rgba(20, 24, 56, 230);"
                " border: 1.5px solid rgba(147, 165, 245, 0.45); border-radius: 25px; }"
                "QFrame#inputCapsule:focus-within { background: rgba(26, 32, 72, 245);"
                " border: 1.5px solid rgba(165, 180, 252, 0.90); }")
            self._input.setStyleSheet(
                "QLineEdit, QTextEdit { background: transparent;"
                " border: none; color: #F8FAFC; padding: 4px 6px; font-size: 13px;"
                " selection-background-color: #6366F1; }"
                "QTextEdit QScrollBar:vertical { background: transparent; width: 4px; margin: 0; }"
                "QTextEdit QScrollBar::handle:vertical { background: rgba(148, 163, 184, 120);"
                " border-radius: 2px; min-height: 18px; }"
                "QTextEdit QScrollBar::add-line:vertical, QTextEdit QScrollBar::sub-line:vertical { height: 0; }")
            self._meme_btn.setStyleSheet(
                "QToolButton { background: transparent; border: none; border-radius: 17px; padding: 0px; }"
                "QToolButton:hover { background: rgba(165, 180, 252, 0.25); }"
                "QToolButton:pressed { background: rgba(165, 180, 252, 0.40); }")
            self._send_btn.setStyleSheet(
                "QToolButton { background: qlineargradient(x1:0, y1:0, x2:1, y2:1,"
                " stop:0 #6366F1, stop:1 #8B5CF6);"
                " border: 1px solid rgba(165, 180, 252, 0.6); border-radius: 18px;"
                " color: #FFFFFF; font-size: 15px; font-weight: bold; padding: 0px; }"
                "QToolButton:hover { background: qlineargradient(x1:0, y1:0, x2:1, y2:1,"
                " stop:0 #818CF8, stop:1 #A78BFA); border-color: #FFFFFF; }"
                "QToolButton:pressed { background: #4F46E5; }")
            self._search.setStyleSheet(
                "QLineEdit { background: rgba(20, 24, 56, 230);"
                " border: 1.5px solid rgba(147, 165, 245, 0.45); border-radius: 15px;"
                " color: #F8FAFC; padding: 3px 12px; font-size: 12px; selection-background-color: #6366F1; }"
                "QLineEdit:focus { border: 1.5px solid rgba(165, 180, 252, 0.90); }")
            self._set_log_bg(QColor(12, 15, 38))
            self._filter_btn.setStyleSheet(
                "QToolButton { background: rgba(30, 36, 78, 220);"
                " border: 1.5px solid rgba(147, 165, 245, 0.45); border-radius: 15px;"
                " color: #C7D2FE; padding: 0px 8px; font-size: 12px; font-weight: 500; }"
                "QToolButton:hover { background: rgba(45, 52, 105, 240); border-color: rgba(165, 180, 252, 0.8); color: #FFFFFF; }"
                "QToolButton:pressed { background: rgba(26, 32, 72, 255); }")
            self._count.setStyleSheet("background: transparent; color: #94A3B8; font-size: 11px;")
            self._footer.setStyleSheet("background: transparent; color: #94A3B8; font-size: 11px;")
            self._empty_label.setStyleSheet("background: transparent; color: #94A3B8; font-size: 12px;")
            self._empty_btn.setStyleSheet(
                "QPushButton#emptyBtn { background: rgba(45, 52, 105, 220); border: 1.5px solid rgba(147, 165, 245, 0.6);"
                " border-radius: 14px; color: #E0E7FF; font-size: 12px; font-weight: 500; padding: 4px 12px; }"
                "QPushButton#emptyBtn:hover { background: rgba(65, 75, 145, 240); border-color: #FFFFFF; }")
            for edit in (self._input, self._search):
                pal = edit.palette()
                pal.setColor(QPalette.ColorRole.PlaceholderText, QColor(148, 163, 184, 180))
                edit.setPalette(pal)
        else:
            # 浅色日间主题
            self._title.setStyleSheet("background: transparent; color: #1E293B; font-weight: bold;")
            self._badge.setStyleSheet(
                "background: rgba(238, 242, 255, 240); color: #4F46E5;"
                " border: 1px solid rgba(199, 210, 254, 255); border-radius: 10px;"
                " font-size: 10px; font-weight: 500; padding: 1px 7px;")
            self._persona.setStyleSheet("background: transparent; color: #059669; font-size: 11px;")
            self._close_btn.setStyleSheet(
                "QToolButton { background: rgba(241, 245, 249, 220);"
                " border: 1px solid rgba(226, 232, 240, 255); border-radius: 13px;"
                " color: #64748B; font-size: 16px; font-weight: bold; padding: 0px; }"
                "QToolButton:hover { background: rgba(239, 68, 68, 30); color: #EF4444; border-color: rgba(239, 68, 68, 80); }"
                "QToolButton:pressed { background: rgba(239, 68, 68, 50); }")
            self._clear_btn.setStyleSheet(
                "QToolButton { background: rgba(241, 245, 249, 220);"
                " border: 1px solid rgba(226, 232, 240, 255); border-radius: 13px;"
                " color: #64748B; font-size: 13px; font-weight: bold; padding: 0px; }"
                "QToolButton:hover { background: rgba(245, 158, 11, 30); color: #D97706; border-color: rgba(245, 158, 11, 80); }"
                "QToolButton:pressed { background: rgba(245, 158, 11, 50); }")
            self._date_label.setStyleSheet(
                "QLabel#dateLabel { background: rgba(241, 245, 249, 220); color: #94A3B8;"
                " border-radius: 11px; padding: 2px 14px; font-size: 11px; font-weight: 500; }")
            self._input_capsule.setStyleSheet(
                "QFrame#inputCapsule { background: rgba(241, 245, 249, 235);"
                " border: 1.5px solid rgba(226, 232, 240, 255); border-radius: 25px; }"
                "QFrame#inputCapsule:focus-within { background: #FFFFFF;"
                " border: 1.5px solid rgba(99, 102, 241, 200); }")
            self._input.setStyleSheet(
                "QLineEdit, QTextEdit { background: transparent; border: none; color: #0F172A; padding: 4px 6px; font-size: 13px;"
                " selection-background-color: #C7D2FE; }"
                "QTextEdit QScrollBar:vertical { background: transparent; width: 4px; margin: 0; }"
                "QTextEdit QScrollBar::handle:vertical { background: rgba(148, 163, 184, 120); border-radius: 2px; min-height: 18px; }"
                "QTextEdit QScrollBar::add-line:vertical, QTextEdit QScrollBar::sub-line:vertical { height: 0; }")
            self._meme_btn.setStyleSheet(
                "QToolButton { background: transparent; border: none; border-radius: 17px; padding: 0px; }"
                "QToolButton:hover { background: rgba(226, 232, 240, 200); }"
                "QToolButton:pressed { background: rgba(203, 213, 225, 220); }")
            self._send_btn.setStyleSheet(
                "QToolButton { background: qlineargradient(x1:0, y1:0, x2:1, y2:1, stop:0 #3B82F6, stop:1 #2563EB);"
                " border: none; border-radius: 18px; color: #FFFFFF; font-size: 15px; font-weight: bold; padding: 0px; }"
                "QToolButton:hover { background: qlineargradient(x1:0, y1:0, x2:1, y2:1, stop:0 #60A5FA, stop:1 #3B82F6); }"
                "QToolButton:pressed { background: #1D4ED8; }")
            self._search.setStyleSheet(
                "QLineEdit { background: rgba(241, 245, 249, 235); border: 1.5px solid rgba(226, 232, 240, 255);"
                " border-radius: 15px; color: #0F172A; padding: 3px 12px; font-size: 12px; selection-background-color: #C7D2FE; }"
                "QLineEdit:focus { background: #FFFFFF; border: 1.5px solid rgba(99, 102, 241, 200); }")
            self._set_log_bg(QColor(248, 250, 252))
            self._filter_btn.setStyleSheet(
                "QToolButton { background: rgba(255, 255, 255, 240); border: 1.5px solid rgba(226, 232, 240, 255);"
                " border-radius: 15px; color: #475569; padding: 0px 8px; font-size: 12px; font-weight: 500; }"
                "QToolButton:hover { background: #FFFFFF; border-color: #CBD5E1; color: #1E293B; }"
                "QToolButton:pressed { background: #F1F5F9; }")
            self._count.setStyleSheet("background: transparent; color: #94A3B8; font-size: 11px;")
            self._footer.setStyleSheet("background: transparent; color: #94A3B8; font-size: 11px;")
            self._empty_label.setStyleSheet("background: transparent; color: #64748B; font-size: 12px;")
            self._empty_btn.setStyleSheet(
                "QPushButton#emptyBtn { background: #EEF2FF; border: 1.5px solid #C7D2FE;"
                " border-radius: 14px; color: #4F46E5; font-size: 12px; font-weight: 500; padding: 4px 12px; }"
                "QPushButton#emptyBtn:hover { background: #E0E7FF; border-color: #A5B4FC; }")
            for edit in (self._input, self._search):
                pal = edit.palette()
                pal.setColor(QPalette.ColorRole.PlaceholderText, QColor(148, 163, 184, 200))
                edit.setPalette(pal)

        # 聊天记录区不能用默认白底：透明窗口 + QScrollArea 在某些 Qt 风格下会把背景
        # 留成白洞/直接透出桌面（用户看到的"镂空"）。这里用和 paintEvent 里 log_rect
        # 一致的实色喂给 viewport / body，滚动时也不会闪。
        self._apply_log_palette()

    def _apply_log_palette(self):
        col = QColor(12, 15, 38) if self._is_starry_theme() else QColor(248, 250, 252)
        self._log_scroll.set_background(col)
        self._scroll.set_background(col)
        self._log_scroll.viewport().setStyleSheet(
            "QWidget#logViewport { background: %s; }" % col.name())
        self._log_body.setStyleSheet(
            "QWidget#logBody { background: %s; }" % col.name())
        self._grid_holder.setStyleSheet(
            "QWidget#gridHolder { background: %s; }" % col.name())
        for widget in (self._log_scroll.viewport(), self._log_body):
            pal = widget.palette()
            pal.setColor(QPalette.ColorRole.Window, col)
            pal.setColor(QPalette.ColorRole.Base, col)
            widget.setPalette(pal)
            widget.setAutoFillBackground(True)

    def _drawer_widgets(self):
        return (self._search, self._filter_btn, self._count, self._scroll,
                self._footer, self._empty_label, self._empty_btn)

    def _confirm_clear_history(self):
        from PySide6.QtWidgets import QMessageBox
        box = QMessageBox(self)
        box.setWindowTitle("清空记忆")
        box.setText("要清空与小鲸鱼娘的历史聊天记录与记忆吗？\n（清空后将从零开始新的记忆）")
        box.setIcon(QMessageBox.Icon.Question)
        box.setStandardButtons(QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No)
        box.setDefaultButton(QMessageBox.StandardButton.No)
        box.setWindowFlag(Qt.WindowType.WindowStaysOnTopHint, True)
        if box.exec() == QMessageBox.StandardButton.Yes:
            if hasattr(self.pet, "clear_chat_history"):
                self.pet.clear_chat_history()
            else:
                self.set_log([])

    # ---------- 聊天记录 ----------
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

        QTimer.singleShot(0, go)
        QTimer.singleShot(40, go)

    def add_message(self, role, text, image=None):
        row = ChatMessageRow(role, text, self.pet.bubble_font, self._log_body,
                             avatar_pm=self._avatar_pm, image=image,
                             timestamp=datetime.datetime.now().strftime("%H:%M"))
        self._log_lay.insertWidget(self._log_lay.count() - 1, row)
        self._log_rows.append(row)
        while len(self._log_rows) > 100:
            old = self._log_rows.pop(0)
            try:
                old.setParent(None)
                old.deleteLater()
            except Exception:
                pass
        if self._typing_row is not None:
            self._log_lay.removeWidget(self._typing_row)
            self._log_lay.insertWidget(self._log_lay.count() - 1, self._typing_row)
        self._scroll_log_bottom()
        return row

    def set_log(self, messages):
        self._clear_log_rows()
        for item in list(messages or [])[-100:]:
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
                    "pet", "小鲸鱼娘 正在输入…", self.pet.bubble_font, self._log_body,
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
            else QFont("Microsoft YaHei UI", 10)
        base.setPointSizeF(11.0)
        self._input.setFont(base)
        f_small = QFont(base)
        f_small.setPointSizeF(9.5)
        f_title = QFont(base)
        f_title.setPointSizeF(14.0)
        f_title.setBold(True)
        self._title.setFont(f_title)
        self._persona.setFont(f_small)
        f_search = QFont(base)
        f_search.setPointSizeF(9.5)
        self._search.setFont(f_search)
        f_btn = QFont(f_small)
        for b in (self._filter_btn, self._send_btn, self._close_btn, getattr(self, "_clear_btn", None)):
            if b is not None:
                b.setFont(f_btn)
        self._count.setFont(f_small)
        self._footer.setFont(f_small)
        self._empty_label.setFont(f_small)
        self._empty_btn.setFont(f_small)
        f_close = QFont(f_small)
        f_close.setPointSizeF(14.0)
        f_close.setBold(True)
        self._close_btn.setFont(f_close)
        f_badge = QFont(f_small)
        f_badge.setPointSizeF(8.5)
        self._badge.setFont(f_badge)
        f_date = QFont(f_small)
        f_date.setPointSizeF(8.5)
        self._date_label.setFont(f_date)

    def _relayout(self):
        w = self.width()
        pad = SHADOW_PAD
        card_w = w - 2 * pad
        card_left = pad
        card_top = pad

        self._header_avatar.setGeometry(card_left + 16, card_top + 11, 42, 42)
        title_text = self._title.text() or "小鲸鱼娘"
        fm_title = self._title.fontMetrics()
        title_w = max(50, fm_title.horizontalAdvance(title_text))
        self._title.setGeometry(card_left + 68, card_top + 11, title_w + 4, 24)
        self._badge.setGeometry(card_left + 68 + title_w + 8, card_top + 13, 76, 20)
        self._persona.setGeometry(card_left + 68, card_top + 35, 240, 18)
        self._close_btn.setGeometry(card_left + card_w - 38, card_top + 16, 26, 26)
        if hasattr(self, "_clear_btn"):
            self._clear_btn.setGeometry(card_left + card_w - 68, card_top + 16, 26, 26)

        self._log_scroll.setGeometry(card_left + 12, card_top + CHAT_HEADER_H + 4, card_w - 24, CHAT_LOG_H)

        dock_x = card_left + 12
        dock_y = card_top + CHAT_ROW_Y
        dock_w = card_w - 24
        dock_h = CHAT_INPUT_H
        self._input_capsule.setGeometry(dock_x, dock_y, dock_w, dock_h)
        self._input.setGeometry(dock_x + 8, dock_y + 5, dock_w - 90, dock_h - 10)
        self._meme_btn.setGeometry(dock_x + dock_w - 78, dock_y + 8, 34, 34)
        self._send_btn.setGeometry(dock_x + dock_w - 40, dock_y + 7, 36, 36)

        # 表情抽屉（面板向下展开的那一块）
        search_y = card_top + (CHAT_PANEL_H - 2 * pad) + 8
        self._search.setGeometry(card_left + 14, search_y, 230, 30)
        self._filter_btn.setGeometry(card_left + 250, search_y, 80, 30)
        self._count.setGeometry(card_left + 336, search_y, card_w - 336 - 14, 30)
        
        scroll_y = search_y + 38
        footer_visible = bool(self._footer_visible)
        drawer_inner_h = CHAT_DRAWER_H - 12
        scroll_h = drawer_inner_h - 52
        if footer_visible:
            scroll_h -= 22
        self._scroll.setGeometry(card_left + 14, scroll_y, card_w - 28, max(20, scroll_h))
        self._footer.setGeometry(card_left + 14, scroll_y + scroll_h + 2, card_w - 28, 18)
        self._empty_label.setGeometry(card_left + 14, scroll_y + 70, card_w - 28, 24)
        self._empty_btn.setGeometry(card_left + 14 + (card_w - 28 - 92) // 2, scroll_y + 108, 92, 30)
        
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
            self._persona.setText(f"● 在线 · {name}模式")
        if font_sig != self._font_sig:
            self._font_sig = font_sig
            self._apply_fonts()
            self.set_log(getattr(self.pet, "_chat_ui_log", []))
        self._apply_theme_styles()

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
        self._drawer_open = False
        for w in self._drawer_widgets():
            w.hide()
        self._apply_height()
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
        if not self.isVisible():
            return
        if not self.pet.isVisible():
            self.close_panel()
            return
        self.refresh_persona()
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
                "只展示前 %d 张，还有 %d 张 —— 可输入关键词筛选"
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
        pad = SHADOW_PAD
        if ev.button() == Qt.MouseButton.LeftButton \
                and ev.position().y() <= pad + CHAT_HEADER_H:
            self._dragging = True
            self._pinned = True
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
    def _draw_starfield(self, p, rect):
        """绘制璀璨星空背景（星点与十字星芒）。"""
        p.save()
        w = float(rect.width())
        h = float(rect.height())
        rx = float(rect.left())
        ry = float(rect.top())

        for fx, fy, radius, alpha, is_twinkle in _STARRY_STARS:
            cx = rx + w * fx
            cy = ry + h * fy
            col = QColor(230, 238, 255, alpha)
            if is_twinkle:
                # 绘制小十字星芒
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(col)
                span = radius * 3.0
                thin = max(0.8, radius * 0.45)
                poly = QPolygonF([
                    QPointF(cx, cy - span),
                    QPointF(cx + thin, cy - thin),
                    QPointF(cx + span, cy),
                    QPointF(cx + thin, cy + thin),
                    QPointF(cx, cy + span),
                    QPointF(cx - thin, cy + thin),
                    QPointF(cx - span, cy),
                    QPointF(cx - thin, cy - thin)
                ])
                p.drawPolygon(poly)
                p.drawEllipse(QPointF(cx, cy), radius * 0.7, radius * 0.7)
            else:
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(col)
                p.drawEllipse(QPointF(cx, cy), radius, radius)
        p.restore()

    def _draw_custom_backdrop(self, p, rect):
        """如果专门配置了聊天面板背景图，只淡淡叠在标题区当装饰，不盖聊天记录。

        注意：不再 fallback 读取 `console_bg_path`——那是设置窗口的背景，
        套到聊天面板会整张图铺满，把聊天记录衬得花到看不清。
        """
        try:
            bg_path = str(self.pet.cfg.get("chat_bg_path") or "").strip()
            if bg_path and os.path.isfile(bg_path):
                img = QPixmap(bg_path)
                if not img.isNull():
                    header_h = CHAT_HEADER_H
                    scaled = img.scaled(int(rect.width()), int(header_h),
                                        Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                                        Qt.TransformationMode.SmoothTransformation)
                    x = int(rect.left() + (rect.width() - scaled.width()) / 2)
                    y = int(rect.top() + (header_h - scaled.height()) / 2)
                    p.save()
                    p.setOpacity(0.15)
                    p.drawPixmap(x, y, scaled)
                    p.restore()
        except Exception:
            pass

    def paintEvent(self, _ev):
        """精美星空/粉彩双主题背景 + 外部立体投影 + 磨砂玻璃头部 + 消息台衬底。"""
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)

        pad = SHADOW_PAD
        rect = QRectF(pad, pad, self.width() - 2 * pad, self.height() - 2 * pad)
        starry = self._is_starry_theme()

        # 先铺一层与主题同色的实色底，防止半透明窗口透出桌面
        base_path = QPainterPath()
        base_path.addRoundedRect(QRectF(self.rect()),
                                 CHAT_RADIUS + pad, CHAT_RADIUS + pad)
        p.fillPath(base_path,
                   QColor(14, 18, 44, 255) if starry else QColor(248, 250, 255, 255))

        # 1. 绘制外部多层柔和立体投影 (Drop Shadow)
        shadow_base = QColor(10, 8, 28, 45) if starry else QColor(30, 41, 59, 25)
        for step in range(pad, 0, -2):
            alpha = int(shadow_base.alpha() * (1.0 - step / pad) * 1.5)
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor(shadow_base.red(), shadow_base.green(), shadow_base.blue(), alpha))
            p.drawRoundedRect(rect.adjusted(-step, -step + 2, step, step + 2),
                              CHAT_RADIUS + step, CHAT_RADIUS + step)

        # 2. 绘制面板背景轮廓路径
        path = QPainterPath()
        path.addRoundedRect(rect, CHAT_RADIUS, CHAT_RADIUS)

        # 3. 填充面板主背景
        p.save()
        p.setClipPath(path)

        if starry:
            # 深邃星空紫蓝渐变
            grad = QLinearGradient(rect.left(), rect.top(), rect.left(), rect.bottom())
            grad.setColorAt(0.0, QColor(14, 18, 44, 255))
            grad.setColorAt(0.5, QColor(22, 24, 62, 255))
            grad.setColorAt(1.0, QColor(36, 26, 74, 255))
            p.fillPath(path, grad)
            self._draw_custom_backdrop(p, rect)   # 新增：先盖图，后面衬底压它

            # 星空星点平铺 (如果本地有 starry_tile.png)
            tile = self._starry_tile_pixmap()
            if tile is not None and not tile.isNull():
                tw, th = tile.width(), tile.height()
                x0 = int(math.floor(rect.left() / tw)) * tw
                y0 = int(math.floor(rect.top() / th)) * th
                x1 = int(math.ceil(rect.right()))
                y1 = int(math.ceil(rect.bottom()))
                p.setOpacity(0.65)
                for ty in range(y0, y1, th):
                    for tx in range(x0, x1, tw):
                        p.drawPixmap(tx, ty, tile)
                p.setOpacity(1.0)

            # 星云辉光 (柔和青色与紫红色漫反射)
            p.setPen(Qt.PenStyle.NoPen)
            for cx, cy, rr, col in ((0.22, 0.20, 160, QColor(56, 189, 248, 22)),
                                    (0.85, 0.28, 180, QColor(168, 85, 247, 28)),
                                    (0.48, 0.72, 200, QColor(99, 102, 241, 24))):
                p.setBrush(col)
                p.drawEllipse(QPointF(rect.left() + rect.width() * cx,
                                     rect.top() + rect.height() * cy), rr, rr)

            # 璀璨星点与十字星芒
            self._draw_starfield(p, rect)

            # 头部高光磨砂层
            p.fillRect(QRectF(rect.left(), rect.top(), rect.width(), CHAT_HEADER_H),
                       QColor(255, 255, 255, 15))

            # 聊天记录区域凹槽衬底 (让气泡更分明)
            log_rect = QRectF(rect.left() + 10, rect.top() + CHAT_HEADER_H + 4,
                              rect.width() - 20, CHAT_LOG_H)
            p.setPen(QPen(QColor(147, 165, 245, 50), 1))
            p.setBrush(QColor(12, 15, 38, 255))
            p.drawRoundedRect(log_rect, 14, 14)

        else:
            # 清爽浅色梦幻渐变
            grad = QLinearGradient(rect.left(), rect.top(), rect.left(), rect.bottom())
            grad.setColorAt(0.0, QColor(248, 250, 255, 255))
            grad.setColorAt(0.5, QColor(240, 244, 254, 255))
            grad.setColorAt(1.0, QColor(245, 238, 252, 255))
            p.fillPath(path, grad)
            self._draw_custom_backdrop(p, rect)

            # 柔和云彩/光晕
            for cx, cy, rr, col in ((0.20, 0.18, 140, QColor(99, 102, 241, 22)),
                                    (0.82, 0.25, 160, QColor(236, 72, 153, 18)),
                                    (0.50, 0.65, 180, QColor(59, 130, 246, 16))):
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(col)
                p.drawEllipse(QPointF(rect.left() + rect.width() * cx,
                                     rect.top() + rect.height() * cy), rr, rr)

            # 头部卡片高光层
            p.fillRect(QRectF(rect.left(), rect.top(), rect.width(), CHAT_HEADER_H),
                       QColor(255, 255, 255, 180))

            # 聊天记录衬底
            log_rect = QRectF(rect.left() + 10, rect.top() + CHAT_HEADER_H + 4,
                              rect.width() - 20, CHAT_LOG_H)
            p.setPen(QPen(QColor(226, 232, 240, 180), 1))
            p.setBrush(QColor(248, 250, 252, 245))
            p.drawRoundedRect(log_rect, 14, 14)

        p.restore()

        # 4. 外轮廓边框
        p.setBrush(Qt.BrushStyle.NoBrush)
        border_col = QColor(150, 168, 248, 180) if starry else QColor(203, 213, 225, 220)
        p.setPen(QPen(border_col, 1.4))
        p.drawPath(path)

        # 5. 头部与聊天记录的分割细线
        sep_col = QColor(165, 180, 252, 90) if starry else QColor(226, 232, 240, 220)
        p.setPen(QPen(sep_col, 1))
        p.drawLine(QPointF(rect.left() + 16, rect.top() + CHAT_HEADER_H),
                   QPointF(rect.right() - 16, rect.top() + CHAT_HEADER_H))

        # 若抽屉打开，在聊天面板与抽屉之间画分割线
        if self._drawer_open:
            p.setPen(QPen(sep_col, 1))
            p.drawLine(QPointF(rect.left() + 16, rect.top() + (CHAT_PANEL_H - 2 * pad)),
                       QPointF(rect.right() - 16, rect.top() + (CHAT_PANEL_H - 2 * pad)))

        p.end()

    def resizeEvent(self, ev):
        self._relayout()
        super().resizeEvent(ev)

    def closeEvent(self, ev):
        self._search_timer.stop()
        self._release_guard()
        super().closeEvent(ev)

