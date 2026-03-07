"""
Canvas Widget — PyQt6 port of the React canvas from euclid-merged.jsx.

QGraphicsScene-based interactive geometry canvas supporting:
  • Point placement, dragging, and labelling
  • Segment / ray / circle / angle / perpendicular drawing
  • Pan tool + middle-click pan + scroll zoom + toolbar zoom controls
  • Snap-to-existing-point, snap-to-segment, snap-to-circle-boundary
  • Circle-circle & segment-circle intersection snapping
  • Circle defined by center + radius point (drag resizes)
  • Intersection-point drags both parent circles
  • Equality assertion tool with tick marks
  • Angle measurement display; right-angle ±5° validation
  • Label tool with inline popover
  • Delete tool with cascade removal
  • Reset (restore given objects)
  • Undo / redo (30 levels) + Ctrl+Z / Ctrl+Y
  • Pending-click highlight for multi-click tools
"""
from __future__ import annotations

import math
from typing import Dict, List, Optional, Tuple

from PyQt6.QtCore import Qt, QPointF, QRectF, pyqtSignal
from PyQt6.QtGui import (
    QBrush, QColor, QFont, QPainter, QPen,
    QPainterPath, QTransform, QKeySequence, QShortcut,
)
from PyQt6.QtWidgets import (
    QGraphicsScene, QGraphicsView, QGraphicsEllipseItem,
    QGraphicsLineItem, QGraphicsTextItem, QGraphicsItem,
    QGraphicsPathItem, QGraphicsProxyWidget,
    QWidget, QVBoxLayout, QHBoxLayout, QLineEdit, QPushButton, QLabel,
)

from ..engine.constraints import (
    circle_intersections as _circle_ix,
    line_circle_intersections as _line_circle_ix,
    distance as _dist,
    angle_at_vertex as _angle_at_vertex,
)


# ═══════════════════════════════════════════════════════════════════════════
# CONSTANTS
# ═══════════════════════════════════════════════════════════════════════════

POINT_RADIUS = 5
SNAP_DISTANCE = 15
UNDO_LIMIT = 30
RIGHT_ANGLE_TOL = 5.0  # degrees tolerance for perpendicular tool

COLORS = {
    "point": QColor("#2d70b3"),
    "point_label": QColor("#1a1a2e"),
    "segment": QColor("#2d70b3"),
    "circle": QColor("#2d70b3"),
    "angle": QColor("#c9a84c"),
    "grid": QColor("#e5e7eb"),
    "highlight": QColor("#ff6b6b"),
    "pending": QColor("#ffa500"),
    "snap_indicator": QColor("#888888"),
    "equality_tick": QColor("#c9a84c"),
}

# User-selectable drawing colours (matches React screenshot)
COLOR_PALETTE = [
    QColor("#2d70b3"),  # blue (default)
    QColor("#cc3333"),  # red
    QColor("#2d8659"),  # green (dark)
    QColor("#43a047"),  # green (light)
    QColor("#7b1fa2"),  # purple
    QColor("#f57c00"),  # orange
    QColor("#1a1a2e"),  # black
    QColor("#00897b"),  # teal
]

LABEL_CHARS = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"


# ═══════════════════════════════════════════════════════════════════════════
# SCENE ITEMS
# ═══════════════════════════════════════════════════════════════════════════

class PointItem(QGraphicsEllipseItem):
    """A labelled draggable point."""

    def __init__(self, label: str, x: float, y: float):
        r = POINT_RADIUS
        super().__init__(-r, -r, 2 * r, 2 * r)
        self.label = label
        self.setBrush(QBrush(COLORS["point"]))
        self.setPen(QPen(Qt.PenStyle.NoPen))
        self.setPos(x, y)
        self.setFlag(QGraphicsItem.GraphicsItemFlag.ItemIsMovable, True)
        self.setFlag(QGraphicsItem.GraphicsItemFlag.ItemSendsGeometryChanges, True)
        self.setZValue(10)
        self._text = QGraphicsTextItem(label, self)
        self._text.setDefaultTextColor(COLORS["point_label"])
        self._text.setFont(QFont("Segoe UI", 10, QFont.Weight.Bold))
        self._text.setPos(r + 2, -r - 4)
        # Internal (unlabelled) points start with '_' and hide the label
        self._label_visible = not label.startswith("_")
        self._text.setVisible(self._label_visible)
        # Intersection tracking: which circles define this point
        self.intersection_circles: List["CircleItem"] = []
        # Segment constraint: if set, point is constrained to this segment
        self.segment_constraint: Optional["SegmentItem"] = None
        self.segment_t: float = 0.5  # t-parameter (0..1) along constrained segment
        self._drag_started = False

    def set_label(self, new_label: str):
        self.label = new_label
        self._label_visible = not new_label.startswith("_")
        self._text.setPlainText(new_label if self._label_visible else "")
        self._text.setDefaultTextColor(COLORS["point_label"])
        self._text.setVisible(self._label_visible)

    def set_highlight(self, on: bool):
        self.setBrush(QBrush(COLORS["pending"] if on else COLORS["point"]))

    def shape(self):
        """Enlarge the clickable area so small points are easier to grab."""
        from PyQt6.QtGui import QPainterPath
        path = QPainterPath()
        grab = SNAP_DISTANCE
        scene = self.scene()
        if scene and scene.views():
            scale = scene.views()[0].transform().m11()
            if scale > 0:
                grab = max(grab, grab / scale)
        path.addEllipse(-grab, -grab, 2 * grab, 2 * grab)
        return path

    def itemChange(self, change, value):
        if change == QGraphicsItem.GraphicsItemChange.ItemPositionChange:
            # Push undo once per drag
            scene = self.scene()
            if isinstance(scene, GeometryScene) and not self._drag_started:
                self._drag_started = True
                scene.push_undo()
            # Constrain to segment if set
            if self.segment_constraint:
                seg = self.segment_constraint
                ax, ay = seg.p1.pos().x(), seg.p1.pos().y()
                bx, by = seg.p2.pos().x(), seg.p2.pos().y()
                dx, dy = bx - ax, by - ay
                len_sq = dx * dx + dy * dy
                if len_sq > 0:
                    new_pos = value
                    t = ((new_pos.x() - ax) * dx + (new_pos.y() - ay) * dy) / len_sq
                    t = max(0.0, min(1.0, t))
                    self.segment_t = t
                    return QPointF(ax + t * dx, ay + t * dy)
        if change == QGraphicsItem.GraphicsItemChange.ItemPositionHasChanged:
            scene = self.scene()
            if isinstance(scene, GeometryScene):
                scene.on_point_moved(self)
        return super().itemChange(change, value)


class SegmentItem(QGraphicsLineItem):
    """A line segment between two points."""

    def __init__(self, p1: PointItem, p2: PointItem):
        super().__init__()
        self.p1 = p1
        self.p2 = p2
        self.setPen(QPen(COLORS["segment"], 2))
        self.setZValue(1)
        # Tick marks for equality groups
        self.tick_count = 0
        self._tick_items: List[QGraphicsLineItem] = []
        self.update_position()

    def update_position(self):
        self.setLine(self.p1.pos().x(), self.p1.pos().y(),
                     self.p2.pos().x(), self.p2.pos().y())
        self._update_ticks()

    def set_ticks(self, count: int):
        self.tick_count = count
        self._update_ticks()

    def _update_ticks(self):
        for t in self._tick_items:
            if t.scene():
                t.scene().removeItem(t)
        self._tick_items.clear()
        if self.tick_count <= 0 or not self.scene():
            return
        mx = (self.p1.pos().x() + self.p2.pos().x()) / 2
        my = (self.p1.pos().y() + self.p2.pos().y()) / 2
        dx = self.p2.pos().x() - self.p1.pos().x()
        dy = self.p2.pos().y() - self.p1.pos().y()
        length = math.hypot(dx, dy) or 1
        nx, ny = -dy / length, dx / length  # perpendicular
        pen = QPen(COLORS["equality_tick"], 2)
        spacing = 5
        for i in range(self.tick_count):
            offset = (i - (self.tick_count - 1) / 2) * spacing
            cx = mx + dx / length * offset
            cy = my + dy / length * offset
            tick = QGraphicsLineItem(cx + nx * 6, cy + ny * 6, cx - nx * 6, cy - ny * 6)
            tick.setPen(pen)
            tick.setZValue(5)
            self.scene().addItem(tick)
            self._tick_items.append(tick)


class RayItem(QGraphicsLineItem):
    """A ray from p1 through p2, extending far beyond p2."""

    RAY_EXTEND = 4000  # extend far past p2

    def __init__(self, p1: PointItem, p2: PointItem):
        super().__init__()
        self.p1 = p1
        self.p2 = p2
        self.setPen(QPen(COLORS["segment"], 2))
        self.setZValue(1)
        self.update_position()

    def update_position(self):
        x1, y1 = self.p1.pos().x(), self.p1.pos().y()
        x2, y2 = self.p2.pos().x(), self.p2.pos().y()
        dx, dy = x2 - x1, y2 - y1
        length = math.hypot(dx, dy)
        if length > 0:
            ux, uy = dx / length, dy / length
            ex = x1 + ux * self.RAY_EXTEND
            ey = y1 + uy * self.RAY_EXTEND
        else:
            ex, ey = x2, y2
        self.setLine(x1, y1, ex, ey)


class CircleItem(QGraphicsEllipseItem):
    """A circle defined by center + radius point."""

    def __init__(self, center: PointItem, radius_pt: Optional[PointItem], radius: float):
        super().__init__()
        self.center_pt = center
        self.radius_pt = radius_pt
        self.radius = radius
        self.setPen(QPen(COLORS["circle"], 2))
        self.setBrush(QBrush(Qt.BrushStyle.NoBrush))
        self.setZValue(0)
        self.update_position()

    def update_position(self):
        if self.radius_pt:
            self.radius = math.hypot(
                self.center_pt.pos().x() - self.radius_pt.pos().x(),
                self.center_pt.pos().y() - self.radius_pt.pos().y(),
            )
        cx, cy = self.center_pt.pos().x(), self.center_pt.pos().y()
        r = self.radius
        self.setRect(cx - r, cy - r, 2 * r, 2 * r)


class AngleMarkItem(QGraphicsPathItem):
    """A small arc indicating an angle at a vertex, with degree display."""

    def __init__(self, from_pt: PointItem, vertex: PointItem, to_pt: PointItem,
                 is_right: bool = False):
        super().__init__()
        self.from_pt = from_pt
        self.vertex_pt = vertex
        self.to_pt = to_pt
        self.is_right = is_right
        self.setPen(QPen(COLORS["angle"], 2))
        self.setZValue(2)
        self._deg_text: Optional[QGraphicsTextItem] = None
        self.update_position()

    def update_position(self):
        v = self.vertex_pt.pos()
        a = self.from_pt.pos()
        b = self.to_pt.pos()
        r = 25

        # Compute angle in degrees
        va = (a.x() - v.x(), a.y() - v.y())
        vb = (b.x() - v.x(), b.y() - v.y())
        dot = va[0] * vb[0] + va[1] * vb[1]
        mag_a = math.hypot(*va) or 1
        mag_b = math.hypot(*vb) or 1
        cos_val = max(-1.0, min(1.0, dot / (mag_a * mag_b)))
        deg = math.degrees(math.acos(cos_val))

        if self.is_right:
            ua = (va[0] / mag_a * r, va[1] / mag_a * r)
            ub = (vb[0] / mag_b * r, vb[1] / mag_b * r)
            path = QPainterPath()
            p1 = QPointF(v.x() + ua[0], v.y() + ua[1])
            p2 = QPointF(v.x() + ua[0] + ub[0], v.y() + ua[1] + ub[1])
            p3 = QPointF(v.x() + ub[0], v.y() + ub[1])
            path.moveTo(p1)
            path.lineTo(p2)
            path.lineTo(p3)
            self.setPath(path)
        else:
            a1 = math.degrees(math.atan2(-(a.y() - v.y()), a.x() - v.x()))
            a2 = math.degrees(math.atan2(-(b.y() - v.y()), b.x() - v.x()))
            span = (a2 - a1) % 360
            if span > 180:
                a1, span = a2, 360 - span
            path = QPainterPath()
            path.arcMoveTo(QRectF(v.x() - r, v.y() - r, 2 * r, 2 * r), a1)
            path.arcTo(QRectF(v.x() - r, v.y() - r, 2 * r, 2 * r), a1, span)
            self.setPath(path)

        # Degree label
        mid_angle_rad = math.atan2(va[1] / mag_a + vb[1] / mag_b,
                                   va[0] / mag_a + vb[0] / mag_b)
        tx = v.x() + math.cos(mid_angle_rad) * (r + 12)
        ty = v.y() + math.sin(mid_angle_rad) * (r + 12)
        if self._deg_text is None:
            self._deg_text = QGraphicsTextItem(self)
            self._deg_text.setDefaultTextColor(COLORS["angle"])
            self._deg_text.setFont(QFont("Segoe UI", 8))
            self._deg_text.setZValue(3)
        self._deg_text.setPlainText(f"{deg:.0f}°")
        self._deg_text.setPos(tx - 10, ty - 8)


class SnapIndicator(QGraphicsTextItem):
    """Temporary indicator showing snap type (on-circle, + on-segment, × intersection)."""
    def __init__(self, text: str, pos: QPointF):
        super().__init__(text)
        self.setDefaultTextColor(COLORS["snap_indicator"])
        self.setFont(QFont("Segoe UI", 8))
        self.setPos(pos.x() + 8, pos.y() - 16)
        self.setZValue(50)


# ═══════════════════════════════════════════════════════════════════════════
# GEOMETRY SCENE
# ═══════════════════════════════════════════════════════════════════════════

class GeometryScene(QGraphicsScene):
    point_added = pyqtSignal(str, float, float)
    segment_added = pyqtSignal(str, str)
    circle_added = pyqtSignal(str, float)
    object_deleted = pyqtSignal()
    canvas_changed = pyqtSignal()

    def __init__(self):
        super().__init__()
        self.setSceneRect(-2000, -2000, 4000, 4000)
        self.setBackgroundBrush(QBrush(QColor("#fafbfc")))
        self._draw_grid()
        self._points: Dict[str, PointItem] = {}
        self._segments: List[SegmentItem] = []
        self._circles: List[CircleItem] = []
        self._rays: List[RayItem] = []
        self._angles: List[AngleMarkItem] = []
        self._next_label = 0
        self._next_internal = 0
        self._tool = "select"
        self._pending: List[PointItem] = []
        self._updating_points = False  # recursion guard for on_point_moved
        # Undo / redo
        self._undo_stack: List[dict] = []
        self._redo_stack: List[dict] = []
        # Equality groups: list of (tick_count, list of segment labels)
        self._equality_groups: List[Tuple[int, List[Tuple[str, str]]]] = []
        self._next_tick = 1
        # Equality selection
        self._eq_selection: List[SegmentItem] = []
        # Snap indicator
        self._snap_indicator: Optional[SnapIndicator] = None
        # Label popover
        self._label_proxy: Optional[QGraphicsProxyWidget] = None
        # Active drawing colour
        self._draw_color: QColor = COLOR_PALETTE[0]
        # Circle boundary resize tracking
        self._resize_circle: Optional[CircleItem] = None
        self._resize_start: Optional[QPointF] = None
        # Circle radius preview (dotted line + outline while drawing)
        self._circle_preview_line: Optional[QGraphicsLineItem] = None
        self._circle_preview_circle: Optional[QGraphicsEllipseItem] = None
        # General tool preview line (segment, ray, angle)
        self._tool_preview_line: Optional[QGraphicsLineItem] = None

    def _draw_grid(self):
        grid_color = QColor("#e8eaed")
        grid_color_major = QColor("#d0d3d8")
        pen = QPen(grid_color, 0.5)
        pen_major = QPen(grid_color_major, 1.0)
        step = 40
        lo, hi = -2000, 2000
        for x in range(lo, hi + 1, step):
            p = pen_major if x % (step * 5) == 0 else pen
            self.addLine(x, lo, x, hi, p).setZValue(-100)
        for y in range(lo, hi + 1, step):
            p = pen_major if y % (step * 5) == 0 else pen
            self.addLine(lo, y, hi, y, p).setZValue(-100)

    def objects_bounding_rect(self) -> QRectF:
        """Return the bounding rect of geometric objects only (points,
        segments, circles, angles), excluding background grid lines."""
        rect = QRectF()
        for pt in self._points.values():
            rect = rect.united(pt.sceneBoundingRect())
        for seg in self._segments:
            rect = rect.united(seg.sceneBoundingRect())
        for circ in self._circles:
            rect = rect.united(circ.sceneBoundingRect())
        for ang in self._angles:
            rect = rect.united(ang.sceneBoundingRect())
        return rect

    def _next_point_label(self) -> str:
        idx = self._next_label
        self._next_label += 1
        if idx < len(LABEL_CHARS):
            return LABEL_CHARS[idx]
        return LABEL_CHARS[idx % len(LABEL_CHARS)] + str(idx // len(LABEL_CHARS))

    def _next_internal_label(self) -> str:
        """Generate an internal ID for unlabelled points (e.g. _p0, _p1)."""
        lbl = "_p" + str(self._next_internal)
        self._next_internal += 1
        return lbl

    # ── Undo / Redo ───────────────────────────────────────────────────

    def _snapshot(self) -> dict:
        # Build constraint data: point_label -> (seg_p1_label, seg_p2_label, t)
        constraints = {}
        for p in self._points.values():
            if p.segment_constraint:
                constraints[p.label] = (p.segment_constraint.p1.label,
                                        p.segment_constraint.p2.label,
                                        p.segment_t)
        return {
            "points": [(p.label, p.pos().x(), p.pos().y(), p._label_visible) for p in self._points.values()],
            "segments": [(s.p1.label, s.p2.label) for s in self._segments],
            "rays": [(r.p1.label, r.p2.label) for r in self._rays],
            "circles": [(c.center_pt.label, c.radius_pt.label if c.radius_pt else None, c.radius) for c in self._circles],
            "angles": [(a.from_pt.label, a.vertex_pt.label, a.to_pt.label, a.is_right) for a in self._angles],
            "next_label": self._next_label,
            "next_internal": self._next_internal,
            "equality_groups": list(self._equality_groups),
            "next_tick": self._next_tick,
            "segment_constraints": constraints,
        }

    def push_undo(self):
        self._undo_stack.append(self._snapshot())
        if len(self._undo_stack) > UNDO_LIMIT:
            self._undo_stack.pop(0)
        self._redo_stack.clear()

    def undo(self):
        if not self._undo_stack:
            return
        self._redo_stack.append(self._snapshot())
        self._restore(self._undo_stack.pop())

    def redo(self):
        if not self._redo_stack:
            return
        self._undo_stack.append(self._snapshot())
        self._restore(self._redo_stack.pop())

    def _restore(self, snap: dict):
        for item in list(self._points.values()):
            self.removeItem(item)
        for item in self._segments:
            item.set_ticks(0)  # remove tick items
            self.removeItem(item)
        for item in self._rays:
            self.removeItem(item)
        for item in self._circles:
            self.removeItem(item)
        for item in self._angles:
            self.removeItem(item)
        self._points.clear()
        self._segments.clear()
        self._rays.clear()
        self._circles.clear()
        self._angles.clear()
        self._pending.clear()
        self._next_label = snap["next_label"]
        self._next_internal = snap.get("next_internal", 0)
        self._equality_groups = list(snap.get("equality_groups", []))
        self._next_tick = snap.get("next_tick", 1)
        for entry in snap["points"]:
            if len(entry) == 4:
                lbl, x, y, vis = entry
            else:
                lbl, x, y = entry
                vis = not lbl.startswith("_")
            pt = PointItem(lbl, x, y)
            pt._label_visible = vis
            pt._text.setVisible(vis)
            pt._text.setPlainText(lbl if vis else "")
            pt.setFlag(QGraphicsItem.GraphicsItemFlag.ItemIsMovable, self._tool == "select")
            self.addItem(pt)
            self._points[lbl] = pt
        for fl, tl in snap["segments"]:
            p1, p2 = self._points.get(fl), self._points.get(tl)
            if p1 and p2:
                seg = SegmentItem(p1, p2)
                self.addItem(seg)
                self._segments.append(seg)
        for fl, tl in snap.get("rays", []):
            p1, p2 = self._points.get(fl), self._points.get(tl)
            if p1 and p2:
                ray = RayItem(p1, p2)
                self.addItem(ray)
                self._rays.append(ray)
        for cl, rpl, rad in snap["circles"]:
            cpt = self._points.get(cl)
            rpt = self._points.get(rpl) if rpl else None
            if cpt:
                circ = CircleItem(cpt, rpt, rad)
                self.addItem(circ)
                self._circles.append(circ)
        for fl, vl, tl, is_right in snap["angles"]:
            f, v, t = self._points.get(fl), self._points.get(vl), self._points.get(tl)
            if f and v and t:
                am = AngleMarkItem(f, v, t, is_right)
                self.addItem(am)
                self._angles.append(am)
        self._apply_equality_ticks()
        # Restore segment constraints
        for pt_label, (sp1, sp2, t) in snap.get("segment_constraints", {}).items():
            pt = self._points.get(pt_label)
            if pt:
                for seg in self._segments:
                    if (seg.p1.label == sp1 and seg.p2.label == sp2) or \
                       (seg.p1.label == sp2 and seg.p2.label == sp1):
                        pt.segment_constraint = seg
                        pt.segment_t = t
                        break
        self.canvas_changed.emit()

    # ── Equality groups ───────────────────────────────────────────────

    def _apply_equality_ticks(self):
        """Reapply tick marks on segments from equality groups."""
        # Clear all ticks
        for seg in self._segments:
            seg.set_ticks(0)
        # Set from groups
        for tick_count, pairs in self._equality_groups:
            for lbl_a, lbl_b in pairs:
                for seg in self._segments:
                    if (seg.p1.label == lbl_a and seg.p2.label == lbl_b) or \
                       (seg.p1.label == lbl_b and seg.p2.label == lbl_a):
                        seg.set_ticks(tick_count)

    def _segment_length(self, seg: SegmentItem) -> float:
        return math.hypot(seg.p1.pos().x() - seg.p2.pos().x(),
                          seg.p1.pos().y() - seg.p2.pos().y())

    def assert_segments_equal(self, seg_a: SegmentItem, seg_b: SegmentItem):
        """Assert two segments as equal and add tick marks.
        Only succeeds if the segments are approximately the same length."""
        len_a = self._segment_length(seg_a)
        len_b = self._segment_length(seg_b)
        tol = max(3.0, 0.02 * max(len_a, len_b))
        if abs(len_a - len_b) > tol:
            return  # segments are not equal — reject silently
        self.push_undo()
        pair_a = (seg_a.p1.label, seg_a.p2.label)
        pair_b = (seg_b.p1.label, seg_b.p2.label)
        # Check if either segment already in a group
        for i, (tc, pairs) in enumerate(self._equality_groups):
            labels = [(a, b) for a, b in pairs]
            if pair_a in labels or (pair_a[1], pair_a[0]) in labels:
                pairs.append(pair_b)
                self._apply_equality_ticks()
                self.canvas_changed.emit()
                return
            if pair_b in labels or (pair_b[1], pair_b[0]) in labels:
                pairs.append(pair_a)
                self._apply_equality_ticks()
                self.canvas_changed.emit()
                return
        # New group
        self._equality_groups.append((self._next_tick, [pair_a, pair_b]))
        self._next_tick += 1
        self._apply_equality_ticks()
        self.canvas_changed.emit()

    def _validate_equality_groups(self):
        """Remove segments from equality groups whose lengths no longer match.
        Called after point drags to keep tick marks honest."""
        changed = False
        new_groups = []
        for tick_count, pairs in self._equality_groups:
            if not pairs:
                continue
            # Compute lengths for each pair
            pair_lengths = []
            for lbl_a, lbl_b in pairs:
                seg = None
                for s in self._segments:
                    if (s.p1.label == lbl_a and s.p2.label == lbl_b) or \
                       (s.p1.label == lbl_b and s.p2.label == lbl_a):
                        seg = s
                        break
                if seg:
                    pair_lengths.append((lbl_a, lbl_b, self._segment_length(seg)))
                # If segment no longer exists, drop the pair
            if len(pair_lengths) < 2:
                if pairs:
                    changed = True
                continue
            # Keep only pairs whose length matches the first
            ref_len = pair_lengths[0][2]
            kept = []
            for a, b, length in pair_lengths:
                tol = max(3.0, 0.02 * max(ref_len, length))
                if abs(length - ref_len) <= tol:
                    kept.append((a, b))
                else:
                    changed = True
            if len(kept) >= 2:
                new_groups.append((tick_count, kept))
            else:
                changed = True
        if changed:
            self._equality_groups = new_groups
            self._apply_equality_ticks()

    # ── Tool / API ────────────────────────────────────────────────────

    def set_draw_color(self, color: QColor):
        self._draw_color = color

    def set_tool(self, tool: str):
        self._clear_pending_highlight()
        self._dismiss_label_popover()
        self._clear_snap_indicator()
        self._clear_circle_preview()
        self._clear_tool_preview()
        self._eq_selection.clear()
        self._tool = tool
        self._pending.clear()
        for p in self._points.values():
            p.setFlag(QGraphicsItem.GraphicsItemFlag.ItemIsMovable, tool == "select")

    def _clear_pending_highlight(self):
        for p in self._pending:
            p.set_highlight(False)

    def _clear_snap_indicator(self):
        if self._snap_indicator:
            self.removeItem(self._snap_indicator)
            self._snap_indicator = None

    def _clear_circle_preview(self):
        if self._circle_preview_line:
            self.removeItem(self._circle_preview_line)
            self._circle_preview_line = None
        if self._circle_preview_circle:
            self.removeItem(self._circle_preview_circle)
            self._circle_preview_circle = None

    def _clear_tool_preview(self):
        if self._tool_preview_line:
            self.removeItem(self._tool_preview_line)
            self._tool_preview_line = None

    def _show_snap_indicator(self, text: str, pos: QPointF):
        self._clear_snap_indicator()
        self._snap_indicator = SnapIndicator(text, pos)
        self.addItem(self._snap_indicator)

    # ── Label tool popover ────────────────────────────────────────────

    def _show_label_popover(self, pt: PointItem):
        self._dismiss_label_popover()
        container = QWidget()
        container.setStyleSheet("background: white; border: 1px solid #2d70b3; border-radius: 4px;")
        lay = QHBoxLayout(container)
        lay.setContentsMargins(4, 4, 4, 4)
        lay.setSpacing(4)
        # For unlabelled points, suggest the next available letter
        if pt._label_visible:
            display_label = pt.label
        else:
            display_label = self._next_point_label()
            self._next_label -= 1  # roll back; only advance on accept
        inp = QLineEdit(display_label)
        inp.setMaximumWidth(60)
        inp.setMinimumHeight(24)
        inp.setStyleSheet("color: #000000; font-size: 13px; font-weight: bold; padding: 2px 4px;")
        inp.selectAll()
        btn_ok = QPushButton("\u2713")
        btn_ok.setFixedSize(24, 24)
        btn_ok.setStyleSheet("background: #2d70b3; color: white; border: none; border-radius: 3px; font-size: 12px;")
        btn_cancel = QPushButton("\u2715")
        btn_cancel.setFixedSize(24, 24)
        btn_cancel.setStyleSheet("background: #d32f2f; color: white; border: none; border-radius: 3px; font-size: 12px;")
        lay.addWidget(inp)
        lay.addWidget(btn_ok)
        lay.addWidget(btn_cancel)
        container.setFixedSize(container.sizeHint())

        self._label_proxy = self.addWidget(container)
        self._label_proxy.setZValue(100)
        self._label_proxy.setPos(pt.pos().x() + 10, pt.pos().y() - 30)

        def accept():
            new_label = inp.text().strip()
            if new_label and new_label != pt.label:
                old = pt.label
                if new_label not in self._points:
                    self.push_undo()
                    del self._points[old]
                    pt.set_label(new_label)
                    self._points[new_label] = pt
                    # Advance the letter counter past this label
                    if new_label[0] in LABEL_CHARS:
                        idx = LABEL_CHARS.index(new_label[0]) + 1
                        self._next_label = max(self._next_label, idx)
                    self.canvas_changed.emit()
            self._dismiss_label_popover()

        def cancel():
            self._dismiss_label_popover()

        btn_ok.clicked.connect(accept)
        btn_cancel.clicked.connect(cancel)
        inp.returnPressed.connect(accept)
        inp.setFocus()

    def _dismiss_label_popover(self):
        if self._label_proxy:
            self.removeItem(self._label_proxy)
            self._label_proxy = None

    # ── Add / query API ───────────────────────────────────────────────

    def add_point(self, label: str, x: float, y: float) -> PointItem:
        if label in self._points:
            return self._points[label]
        pt = PointItem(label, x, y)
        pt.setFlag(QGraphicsItem.GraphicsItemFlag.ItemIsMovable, self._tool == "select")
        self.addItem(pt)
        self._points[label] = pt
        self._next_label = max(self._next_label,
                               LABEL_CHARS.index(label[0]) + 1 if label and label[0] in LABEL_CHARS else self._next_label)
        self.point_added.emit(label, x, y)
        self.canvas_changed.emit()
        return pt

    def add_segment(self, from_label: str, to_label: str) -> Optional[SegmentItem]:
        p1 = self._points.get(from_label)
        p2 = self._points.get(to_label)
        if not p1 or not p2:
            return None
        # Prevent duplicate segment
        for s in self._segments:
            if (s.p1 is p1 and s.p2 is p2) or (s.p1 is p2 and s.p2 is p1):
                return s
        seg = SegmentItem(p1, p2)
        seg.setPen(QPen(self._draw_color, 2))
        self.addItem(seg)
        self._segments.append(seg)
        self.segment_added.emit(from_label, to_label)
        self.canvas_changed.emit()
        return seg

    def add_circle_by_radius_pt(self, center_label: str, edge_label: str) -> Optional[CircleItem]:
        cpt = self._points.get(center_label)
        ept = self._points.get(edge_label)
        if not cpt or not ept:
            return None
        r = math.hypot(cpt.pos().x() - ept.pos().x(), cpt.pos().y() - ept.pos().y())
        circ = CircleItem(cpt, ept, r)
        circ.setPen(QPen(self._draw_color, 2))
        self.addItem(circ)
        self._circles.append(circ)
        self.circle_added.emit(center_label, r)
        self.canvas_changed.emit()
        return circ

    def add_ray(self, from_label: str, through_label: str) -> Optional[RayItem]:
        p1 = self._points.get(from_label)
        p2 = self._points.get(through_label)
        if not p1 or not p2:
            return None
        ray = RayItem(p1, p2)
        ray.setPen(QPen(self._draw_color, 2))
        self.addItem(ray)
        self._rays.append(ray)
        self.canvas_changed.emit()
        return ray

    def add_circle(self, center_label: str, radius: float) -> Optional[CircleItem]:
        cpt = self._points.get(center_label)
        if not cpt:
            return None
        circ = CircleItem(cpt, None, radius)
        circ.setPen(QPen(self._draw_color, 2))
        self.addItem(circ)
        self._circles.append(circ)
        self.circle_added.emit(center_label, radius)
        self.canvas_changed.emit()
        return circ

    def add_angle_mark(self, from_l: str, vertex_l: str, to_l: str,
                       is_right: bool = False) -> Optional[AngleMarkItem]:
        f, v, t = self._points.get(from_l), self._points.get(vertex_l), self._points.get(to_l)
        if not all([f, v, t]):
            return None
        am = AngleMarkItem(f, v, t, is_right)
        self.addItem(am)
        self._angles.append(am)
        self.canvas_changed.emit()
        return am

    def _move_point_silently(self, pt: PointItem, x: float, y: float):
        """Move a point without triggering undo or recursive on_point_moved."""
        pt._drag_started = True  # prevent undo push
        saved_ix = pt.intersection_circles
        pt.intersection_circles = []  # prevent intersection cascade
        saved_sc = pt.segment_constraint
        pt.segment_constraint = None  # prevent segment constraint
        pt.setPos(x, y)
        pt.intersection_circles = saved_ix
        pt.segment_constraint = saved_sc

    def on_point_moved(self, pt: PointItem):
        if self._updating_points:
            return
        self._updating_points = True
        try:
            self._on_point_moved_inner(pt)
        finally:
            self._updating_points = False

    def _on_point_moved_inner(self, pt: PointItem):
        for seg in self._segments:
            if seg.p1 is pt or seg.p2 is pt:
                seg.update_position()
                self._update_constrained_points(seg)
        for ray in self._rays:
            if ray.p1 is pt or ray.p2 is pt:
                ray.update_position()
        # Track which circles changed
        changed_circles = set()
        for circ in self._circles:
            if circ.center_pt is pt or circ.radius_pt is pt:
                circ.update_position()
                changed_circles.add(id(circ))
        for am in self._angles:
            if pt in (am.from_pt, am.vertex_pt, am.to_pt):
                am.update_position()
        # Remove equality assertions for segments that are no longer equal
        self._validate_equality_groups()
        # Intersection drag: if THE DRAGGED point is at an intersection, scale both
        if pt.intersection_circles and len(pt.intersection_circles) >= 2:
            c1, c2 = pt.intersection_circles[0], pt.intersection_circles[1]
            # Pre-compute all new radii and radius-pt targets BEFORE moving anything,
            # because moving a radius_pt of one circle may shift the center of another.
            updates = []
            for circ in (c1, c2):
                cx = circ.center_pt.pos().x()
                cy = circ.center_pt.pos().y()
                new_r = math.hypot(pt.pos().x() - cx, pt.pos().y() - cy)
                rp_target = None
                if new_r > 5 and circ.radius_pt and circ.radius_pt is not pt:
                    rpx = circ.radius_pt.pos().x()
                    rpy = circ.radius_pt.pos().y()
                    d = math.hypot(rpx - cx, rpy - cy) or 1
                    rp_target = (cx + (rpx - cx) / d * new_r,
                                 cy + (rpy - cy) / d * new_r)
                updates.append((circ, new_r, rp_target))
            # Now apply all changes
            moved_pts = set()
            for circ, new_r, rp_target in updates:
                if new_r > 5:
                    circ.radius = new_r
                    if rp_target:
                        self._move_point_silently(circ.radius_pt, rp_target[0], rp_target[1])
                        moved_pts.add(id(circ.radius_pt))
                    circ.update_position()
                    changed_circles.add(id(circ))
            # Update geometry attached to radius points that were moved
            for circ, new_r, rp_target in updates:
                if rp_target and id(circ.radius_pt) in moved_pts:
                    rp = circ.radius_pt
                    for seg in self._segments:
                        if seg.p1 is rp or seg.p2 is rp:
                            seg.update_position()
                    for ray in self._rays:
                        if ray.p1 is rp or ray.p2 is rp:
                            ray.update_position()
                    for am in self._angles:
                        if rp in (am.from_pt, am.vertex_pt, am.to_pt):
                            am.update_position()
        # Reposition OTHER intersection points whose parent circles changed
        if changed_circles:
            for other_pt in list(self._points.values()):
                if other_pt is pt:
                    continue
                if not other_pt.intersection_circles or len(other_pt.intersection_circles) < 2:
                    continue
                oc1, oc2 = other_pt.intersection_circles[0], other_pt.intersection_circles[1]
                if id(oc1) not in changed_circles and id(oc2) not in changed_circles:
                    continue
                oc1_dict = {"x": oc1.center_pt.pos().x(), "y": oc1.center_pt.pos().y()}
                oc2_dict = {"x": oc2.center_pt.pos().x(), "y": oc2.center_pt.pos().y()}
                ixs = _circle_ix(oc1_dict, oc1.radius, oc2_dict, oc2.radius)
                if ixs:
                    best = min(ixs, key=lambda ip: math.hypot(
                        ip["x"] - other_pt.pos().x(), ip["y"] - other_pt.pos().y()))
                    self._move_point_silently(other_pt, best["x"], best["y"])
                    # Update segments/rays/angles attached to this point
                    for seg in self._segments:
                        if seg.p1 is other_pt or seg.p2 is other_pt:
                            seg.update_position()
                    for ray in self._rays:
                        if ray.p1 is other_pt or ray.p2 is other_pt:
                            ray.update_position()
                    for am in self._angles:
                        if other_pt in (am.from_pt, am.vertex_pt, am.to_pt):
                            am.update_position()
        self.canvas_changed.emit()

    def _update_constrained_points(self, seg: SegmentItem):
        """Slide points constrained to *seg* to their stored t-parameter position."""
        ax, ay = seg.p1.pos().x(), seg.p1.pos().y()
        bx, by = seg.p2.pos().x(), seg.p2.pos().y()
        for cp in self._points.values():
            if cp.segment_constraint is seg:
                t = cp.segment_t
                new_x = ax + t * (bx - ax)
                new_y = ay + t * (by - ay)
                # Temporarily disable constraint to avoid recursion
                cp.segment_constraint = None
                cp.setPos(new_x, new_y)
                cp.segment_constraint = seg

    def clear_all(self):
        for item in list(self._points.values()):
            self.removeItem(item)
        for item in self._segments:
            item.set_ticks(0)
            self.removeItem(item)
        for item in self._rays:
            self.removeItem(item)
        for item in self._circles:
            self.removeItem(item)
        for item in self._angles:
            self.removeItem(item)
        self._points.clear()
        self._segments.clear()
        self._rays.clear()
        self._circles.clear()
        self._angles.clear()
        self._next_label = 0
        self._next_internal = 0
        self._pending.clear()
        self._undo_stack.clear()
        self._redo_stack.clear()
        self._equality_groups.clear()
        self._next_tick = 1
        self._eq_selection.clear()
        self._dismiss_label_popover()
        self._clear_snap_indicator()

    def get_state(self) -> dict:
        return {
            "points": [{"label": p.label, "x": p.pos().x(), "y": p.pos().y()} for p in self._points.values()],
            "segments": [{"from": s.p1.label, "to": s.p2.label} for s in self._segments],
            "circles": [{"center": c.center_pt.label, "radius": c.radius,
                         "radius_point": c.radius_pt.label if c.radius_pt else None} for c in self._circles],
            "angle_marks": [{"from": a.from_pt.label, "vertex": a.vertex_pt.label,
                             "to": a.to_pt.label, "is_right": a.is_right} for a in self._angles],
            "equality_groups": [(tc, pairs) for tc, pairs in self._equality_groups],
        }

    # ── Snap helpers ──────────────────────────────────────────────────

    def _effective_snap(self) -> float:
        """Snap distance in scene coords, scaled so it's always >= SNAP_DISTANCE screen px."""
        views = self.views()
        if views:
            scale = views[0].transform().m11()
            if scale > 0:
                return max(SNAP_DISTANCE, SNAP_DISTANCE / scale)
        return SNAP_DISTANCE

    def _snap_to_point(self, pos: QPointF) -> Optional[PointItem]:
        # Points get 2× snap radius so they're hard to miss even near segments/circles
        snap = self._effective_snap() * 2
        best, best_d = None, snap
        for pt in self._points.values():
            d = math.hypot(pt.pos().x() - pos.x(), pt.pos().y() - pos.y())
            if d < best_d:
                best, best_d = pt, d
        return best

    def _snap_to_segment(self, pos: QPointF) -> Optional[QPointF]:
        """Find nearest point on any segment within snap distance."""
        snap = self._effective_snap()
        best_pt, best_d = None, snap
        for seg in self._segments:
            p = self._nearest_point_on_segment(pos, seg)
            if p:
                d = math.hypot(p.x() - pos.x(), p.y() - pos.y())
                if d < best_d:
                    best_pt, best_d = p, d
        return best_pt

    def _snap_to_circle(self, pos: QPointF) -> Optional[QPointF]:
        """Find nearest point on any circle boundary within snap distance."""
        snap = self._effective_snap()
        best_pt, best_d = None, snap
        for circ in self._circles:
            cx, cy = circ.center_pt.pos().x(), circ.center_pt.pos().y()
            dx, dy = pos.x() - cx, pos.y() - cy
            dist_to_center = math.hypot(dx, dy)
            if dist_to_center < 1:
                continue
            dist_to_edge = abs(dist_to_center - circ.radius)
            if dist_to_edge < best_d:
                # Project onto circle boundary
                scale = circ.radius / dist_to_center
                best_pt = QPointF(cx + dx * scale, cy + dy * scale)
                best_d = dist_to_edge
        return best_pt

    def _snap_to_intersection(self, pos: QPointF) -> Optional[Tuple[QPointF, List[CircleItem]]]:
        """Find nearest circle-circle intersection within snap distance."""
        snap = self._effective_snap()
        best_pt, best_d, best_circs = None, snap, []
        for i, c1 in enumerate(self._circles):
            for c2 in self._circles[i + 1:]:
                c1_dict = {"x": c1.center_pt.pos().x(), "y": c1.center_pt.pos().y()}
                c2_dict = {"x": c2.center_pt.pos().x(), "y": c2.center_pt.pos().y()}
                pts = _circle_ix(c1_dict, c1.radius, c2_dict, c2.radius)
                for ip in pts:
                    d = math.hypot(ip["x"] - pos.x(), ip["y"] - pos.y())
                    if d < best_d:
                        best_pt = QPointF(ip["x"], ip["y"])
                        best_d = d
                        best_circs = [c1, c2]
        # Also check segment-circle intersections
        for seg in self._segments:
            for circ in self._circles:
                p1 = {"x": seg.p1.pos().x(), "y": seg.p1.pos().y()}
                p2 = {"x": seg.p2.pos().x(), "y": seg.p2.pos().y()}
                center = {"x": circ.center_pt.pos().x(), "y": circ.center_pt.pos().y()}
                pts = _line_circle_ix(p1, p2, center, circ.radius)
                for ip in pts:
                    d = math.hypot(ip["x"] - pos.x(), ip["y"] - pos.y())
                    if d < best_d:
                        best_pt = QPointF(ip["x"], ip["y"])
                        best_d = d
                        best_circs = [circ]
        if best_pt:
            return best_pt, best_circs
        return None

    @staticmethod
    def _nearest_point_on_segment(pos: QPointF, seg: SegmentItem) -> Optional[QPointF]:
        ax, ay = seg.p1.pos().x(), seg.p1.pos().y()
        bx, by = seg.p2.pos().x(), seg.p2.pos().y()
        dx, dy = bx - ax, by - ay
        len_sq = dx * dx + dy * dy
        if len_sq < 1:
            return None
        t = ((pos.x() - ax) * dx + (pos.y() - ay) * dy) / len_sq
        t = max(0.0, min(1.0, t))
        return QPointF(ax + t * dx, ay + t * dy)

    def _find_snap(self, pos: QPointF) -> Tuple[QPointF, str, List[CircleItem]]:
        """Multi-priority snap: points > intersections > segment > circle > raw pos.
        Returns (snapped_pos, snap_type, associated_circles)."""
        # 1. Existing point
        pt = self._snap_to_point(pos)
        if pt:
            return pt.pos(), "point", []
        # 2. Circle-circle / segment-circle intersection
        ix = self._snap_to_intersection(pos)
        if ix:
            return ix[0], "intersection", ix[1]
        # 3. On-segment
        sp = self._snap_to_segment(pos)
        if sp:
            return sp, "on-segment", []
        # 4. On-circle boundary
        cp = self._snap_to_circle(pos)
        if cp:
            return cp, "on-circle", []
        return pos, "none", []

    def _get_or_create_point(self, pos: QPointF) -> PointItem:
        """Snap to existing point or create a new one at best snap location."""
        existing = self._snap_to_point(pos)
        if existing:
            return existing
        snapped, snap_type, circles = self._find_snap(pos)
        # Safety: if the snapped position is very close to an existing point, use it
        for ep in self._points.values():
            if math.hypot(ep.pos().x() - snapped.x(), ep.pos().y() - snapped.y()) < POINT_RADIUS * 3:
                return ep
        label = self._next_internal_label()
        pt = self.add_point(label, snapped.x(), snapped.y())
        if snap_type == "intersection" and circles:
            pt.intersection_circles = circles
        elif snap_type == "on-segment":
            # Constrain this point to the segment it was placed on
            for seg in self._segments:
                p = self._nearest_point_on_segment(pos, seg)
                if p and math.hypot(p.x() - snapped.x(), p.y() - snapped.y()) < 1:
                    pt.segment_constraint = seg
                    # Compute initial t-parameter
                    ax, ay = seg.p1.pos().x(), seg.p1.pos().y()
                    bx, by = seg.p2.pos().x(), seg.p2.pos().y()
                    dx, dy = bx - ax, by - ay
                    len_sq = dx * dx + dy * dy
                    if len_sq > 0:
                        pt.segment_t = ((snapped.x() - ax) * dx + (snapped.y() - ay) * dy) / len_sq
                    break
        return pt

    # ── Mouse interaction ─────────────────────────────────────────────

    def mousePressEvent(self, event):
        pos = event.scenePos()

        if self._tool == "select":
            # Use a tight radius for point detection in select mode so
            # clicks on circle boundaries aren't stolen by nearby points.
            tight_snap = self._effective_snap()  # 1× (not the 2× used by drawing tools)
            clicked_pt = None
            best_d = tight_snap
            for p in self._points.values():
                d = math.hypot(p.pos().x() - pos.x(), p.pos().y() - pos.y())
                if d < best_d:
                    clicked_pt = p
                    best_d = d
            if clicked_pt:
                clicked_pt._drag_started = False
            # Circle boundary drag-to-resize: if clicking near a circle boundary
            # (not a point), start resizing by adjusting the circle's radius.
            if clicked_pt is None:
                snap = self._effective_snap()
                for circ in self._circles:
                    if not circ.radius_pt:
                        continue
                    cx = circ.center_pt.pos().x()
                    cy = circ.center_pt.pos().y()
                    dist = math.hypot(pos.x() - cx, pos.y() - cy)
                    if abs(dist - circ.radius) < snap:
                        self.push_undo()
                        self._resize_circle = circ
                        self._resize_start = pos
                        return
            super().mousePressEvent(event)
            return

        if self._tool == "pan":
            return

        if self._tool == "label":
            xf = self.views()[0].transform() if self.views() else QTransform()
            item = self.itemAt(pos, xf)
            while item and not isinstance(item, PointItem):
                item = item.parentItem()
            if isinstance(item, PointItem):
                self._show_label_popover(item)
            return

        if self._tool == "equal":
            xf = self.views()[0].transform() if self.views() else QTransform()
            item = self.itemAt(pos, xf)
            while item and not isinstance(item, SegmentItem):
                item = item.parentItem()
            if isinstance(item, SegmentItem):
                if item in self._eq_selection:
                    item.setPen(QPen(COLORS["segment"], 2))
                    self._eq_selection.remove(item)
                else:
                    item.setPen(QPen(COLORS["equality_tick"], 3))
                    self._eq_selection.append(item)
                if len(self._eq_selection) == 2:
                    self.assert_segments_equal(self._eq_selection[0], self._eq_selection[1])
                    for s in self._eq_selection:
                        s.setPen(QPen(COLORS["segment"], 2))
                    self._eq_selection.clear()
            return

        if self._tool == "delete":
            xf = self.views()[0].transform() if self.views() else QTransform()
            item = self.itemAt(pos, xf)
            while item and not isinstance(item, (PointItem, SegmentItem, CircleItem, AngleMarkItem)):
                item = item.parentItem()
            if isinstance(item, PointItem):
                self.push_undo()
                self._remove_point(item)
                self.canvas_changed.emit()
            elif isinstance(item, (SegmentItem, CircleItem, AngleMarkItem)):
                self.push_undo()
                self._remove_item(item)
                self.canvas_changed.emit()
            return

        if self._tool == "point":
            self.push_undo()
            self._get_or_create_point(pos)
            return

        # Two/three-click tools
        if self._tool in ("segment", "ray", "circle", "angle", "perpendicular"):
            # Angle / perpendicular tools only work on existing points
            if self._tool in ("angle", "perpendicular"):
                clicked = self._snap_to_point(pos)
                if clicked is None:
                    return  # ignore clicks on empty space
            else:
                clicked = self._get_or_create_point(pos)
            clicked.set_highlight(True)
            self._pending.append(clicked)

            if self._tool == "segment" and len(self._pending) == 2:
                self.push_undo()
                self.add_segment(self._pending[0].label, self._pending[1].label)
                self._clear_pending_highlight()
                self._pending.clear()
                self._clear_tool_preview()
            elif self._tool == "ray" and len(self._pending) == 2:
                self.push_undo()
                self.add_ray(self._pending[0].label, self._pending[1].label)
                self._clear_pending_highlight()
                self._pending.clear()
                self._clear_tool_preview()
            elif self._tool == "circle" and len(self._pending) == 2:
                self.push_undo()
                self.add_circle_by_radius_pt(self._pending[0].label, self._pending[1].label)
                self._clear_pending_highlight()
                self._pending.clear()
                self._clear_circle_preview()
                self._clear_tool_preview()
            elif self._tool in ("angle", "perpendicular") and len(self._pending) == 3:
                is_right = self._tool == "perpendicular"
                # Validate ±5° of 90 for perpendicular tool
                if is_right:
                    v_dict = {"x": self._pending[1].pos().x(), "y": self._pending[1].pos().y()}
                    a_dict = {"x": self._pending[0].pos().x(), "y": self._pending[0].pos().y()}
                    b_dict = {"x": self._pending[2].pos().x(), "y": self._pending[2].pos().y()}
                    ang = _angle_at_vertex(a_dict, v_dict, b_dict)
                    if ang is not None:
                        deg = math.degrees(ang)
                        if abs(deg - 90) > RIGHT_ANGLE_TOL:
                            # Not close enough to 90° — reject silently
                            self._clear_pending_highlight()
                            self._pending.clear()
                            self._clear_tool_preview()
                            return
                self.push_undo()
                self.add_angle_mark(
                    self._pending[0].label, self._pending[1].label, self._pending[2].label,
                    is_right=is_right,
                )
                self._clear_pending_highlight()
                self._pending.clear()
                self._clear_tool_preview()

    def mouseMoveEvent(self, event):
        """Show snap indicators as cursor moves."""
        pos = event.scenePos()
        # Circle boundary drag-to-resize
        if hasattr(self, '_resize_circle') and self._resize_circle:
            circ = self._resize_circle
            cx, cy = circ.center_pt.pos().x(), circ.center_pt.pos().y()
            new_radius = math.hypot(pos.x() - cx, pos.y() - cy)
            if new_radius > 5:
                circ.radius = new_radius
                circ.update_position()
                # Move radius point to match new radius
                if circ.radius_pt:
                    dx, dy = pos.x() - cx, pos.y() - cy
                    dist = math.hypot(dx, dy) or 1
                    circ.radius_pt.setPos(
                        cx + dx / dist * new_radius,
                        cy + dy / dist * new_radius,
                    )
            return
        if self._tool in ("point", "segment", "ray", "circle", "angle", "perpendicular"):
            # For angle/perpendicular: highlight nearest existing point
            if self._tool in ("angle", "perpendicular"):
                nearest = self._snap_to_point(pos)
                if nearest:
                    self._show_snap_indicator("●", nearest.pos())
                else:
                    self._clear_snap_indicator()
            else:
                _, snap_type, _ = self._find_snap(pos)
                if snap_type == "on-circle":
                    self._show_snap_indicator("on-circle", pos)
                elif snap_type == "on-segment":
                    self._show_snap_indicator("+", pos)
                elif snap_type == "intersection":
                    self._show_snap_indicator("×", pos)
                else:
                    self._clear_snap_indicator()
            # Circle radius preview: dotted line + outline while awaiting 2nd click
            if self._tool == "circle" and len(self._pending) == 1:
                center = self._pending[0]
                cx, cy = center.pos().x(), center.pos().y()
                mx, my = pos.x(), pos.y()
                r = math.hypot(mx - cx, my - cy)
                # Dotted radius line
                if not self._circle_preview_line:
                    self._circle_preview_line = QGraphicsLineItem()
                    dash_pen = QPen(QColor("#2d70b3"), 1.5, Qt.PenStyle.DashLine)
                    self._circle_preview_line.setPen(dash_pen)
                    self._circle_preview_line.setZValue(20)
                    self.addItem(self._circle_preview_line)
                self._circle_preview_line.setLine(cx, cy, mx, my)
                # Preview circle outline
                if not self._circle_preview_circle:
                    self._circle_preview_circle = QGraphicsEllipseItem()
                    prev_pen = QPen(QColor("#2d70b3"), 1.5, Qt.PenStyle.DashLine)
                    self._circle_preview_circle.setPen(prev_pen)
                    self._circle_preview_circle.setBrush(QBrush(Qt.BrushStyle.NoBrush))
                    self._circle_preview_circle.setZValue(20)
                    self.addItem(self._circle_preview_circle)
                self._circle_preview_circle.setRect(cx - r, cy - r, 2 * r, 2 * r)
            else:
                self._clear_circle_preview()
            # Segment / ray / angle preview: dotted line from last pending to cursor
            if self._tool in ("segment", "ray", "angle", "perpendicular") and self._pending:
                anchor = self._pending[-1]
                ax, ay = anchor.pos().x(), anchor.pos().y()
                mx, my = pos.x(), pos.y()
                if not self._tool_preview_line:
                    self._tool_preview_line = QGraphicsLineItem()
                    dash_pen = QPen(QColor("#2d70b3"), 1.5, Qt.PenStyle.DashLine)
                    self._tool_preview_line.setPen(dash_pen)
                    self._tool_preview_line.setZValue(20)
                    self.addItem(self._tool_preview_line)
                self._tool_preview_line.setLine(ax, ay, mx, my)
            else:
                self._clear_tool_preview()
        else:
            self._clear_snap_indicator()
            self._clear_circle_preview()
            self._clear_tool_preview()
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if hasattr(self, '_resize_circle') and self._resize_circle:
            self._resize_circle = None
            self._resize_start = None
            self.canvas_changed.emit()
        super().mouseReleaseEvent(event)

    def keyPressEvent(self, event):
        if event.key() == Qt.Key.Key_Escape:
            self._clear_pending_highlight()
            self._pending.clear()
            self._eq_selection.clear()
            self._dismiss_label_popover()
            self._clear_circle_preview()
            self._clear_tool_preview()
        super().keyPressEvent(event)

    def _remove_point(self, pt: PointItem):
        segs_to_rm = [s for s in self._segments if s.p1 is pt or s.p2 is pt]
        for s in segs_to_rm:
            s.set_ticks(0)
            self._segments.remove(s)
            self.removeItem(s)
        rays_to_rm = [r for r in self._rays if r.p1 is pt or r.p2 is pt]
        for r in rays_to_rm:
            self._rays.remove(r)
            self.removeItem(r)
        angles_to_rm = [a for a in self._angles if pt in (a.from_pt, a.vertex_pt, a.to_pt)]
        for a in angles_to_rm:
            self._angles.remove(a)
            self.removeItem(a)
        circs_to_rm = [c for c in self._circles if c.center_pt is pt or c.radius_pt is pt]
        for c in circs_to_rm:
            self._circles.remove(c)
            self.removeItem(c)
        del self._points[pt.label]
        self.removeItem(pt)
        self.object_deleted.emit()

    def _remove_item(self, item):
        if isinstance(item, SegmentItem) and item in self._segments:
            item.set_ticks(0)
            self._segments.remove(item)
        elif isinstance(item, RayItem) and item in self._rays:
            self._rays.remove(item)
        elif isinstance(item, CircleItem) and item in self._circles:
            self._circles.remove(item)
        elif isinstance(item, AngleMarkItem) and item in self._angles:
            self._angles.remove(item)
        self.removeItem(item)
        self.object_deleted.emit()


# ═══════════════════════════════════════════════════════════════════════════
# CANVAS VIEW (zoom / pan wrapper with zoom controls)
# ═══════════════════════════════════════════════════════════════════════════

class CanvasWidget(QWidget):
    """Wrapper: GeometryScene + zoomable/pannable QGraphicsView + zoom toolbar."""

    def __init__(self):
        super().__init__()
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        self._scene = GeometryScene()
        self._view = QGraphicsView(self._scene)
        self._view.setRenderHint(QPainter.RenderHint.Antialiasing)
        self._view.setDragMode(QGraphicsView.DragMode.NoDrag)
        self._view.setTransformationAnchor(QGraphicsView.ViewportAnchor.AnchorUnderMouse)
        self._view.setStyleSheet("border: none; background: #fafbfc;")
        layout.addWidget(self._view)

        self._pan_active = False
        self._pan_start = QPointF()
        self._view.viewport().installEventFilter(self)

        # Keyboard shortcuts
        sc_undo = QShortcut(QKeySequence("Ctrl+Z"), self)
        sc_undo.activated.connect(self.undo)
        sc_redo = QShortcut(QKeySequence("Ctrl+Y"), self)
        sc_redo.activated.connect(self.redo)
        sc_redo2 = QShortcut(QKeySequence("Ctrl+Shift+Z"), self)
        sc_redo2.activated.connect(self.redo)
        sc_esc = QShortcut(QKeySequence("Escape"), self)
        sc_esc.activated.connect(self._cancel_pending)

        # Signal emitted after any zoom change
        self.zoom_changed = None  # callback slot, set externally

    @property
    def scene(self) -> GeometryScene:
        return self._scene

    def _cancel_pending(self):
        self._scene._clear_pending_highlight()
        self._scene._pending.clear()
        self._scene._eq_selection.clear()
        self._scene._dismiss_label_popover()

    def eventFilter(self, obj, event):
        if obj is self._view.viewport():
            # Scroll wheel zoom
            if event.type() == event.Type.Wheel:
                factor = 1.15 if event.angleDelta().y() > 0 else 1 / 1.15
                self._view.scale(factor, factor)
                if self.zoom_changed:
                    self.zoom_changed()
                return True

            # Middle-click pan (always available)
            if event.type() == event.Type.MouseButtonPress and event.button() == Qt.MouseButton.MiddleButton:
                self._pan_active = True
                self._pan_start = event.pos()
                self._view.setCursor(Qt.CursorShape.ClosedHandCursor)
                return True

            # Pan tool: left-click pan
            if (event.type() == event.Type.MouseButtonPress
                    and event.button() == Qt.MouseButton.LeftButton
                    and self._scene._tool == "pan"):
                self._pan_active = True
                self._pan_start = event.pos()
                self._view.setCursor(Qt.CursorShape.ClosedHandCursor)
                return True

            if event.type() == event.Type.MouseMove and self._pan_active:
                delta = event.pos() - self._pan_start
                self._pan_start = event.pos()
                hs = self._view.horizontalScrollBar()
                vs = self._view.verticalScrollBar()
                hs.setValue(hs.value() - int(delta.x()))
                vs.setValue(vs.value() - int(delta.y()))
                return True

            if event.type() == event.Type.MouseButtonRelease and self._pan_active:
                if (event.button() == Qt.MouseButton.MiddleButton
                        or (event.button() == Qt.MouseButton.LeftButton and self._scene._tool == "pan")):
                    self._pan_active = False
                    self._view.setCursor(Qt.CursorShape.ArrowCursor)
                    return True

        return super().eventFilter(obj, event)

    # ── Zoom controls ─────────────────────────────────────────────────

    def zoom_in(self):
        self._view.scale(1.25, 1.25)

    def zoom_out(self):
        self._view.scale(1 / 1.25, 1 / 1.25)

    def zoom_reset(self):
        self._view.resetTransform()

    def zoom_percent(self) -> int:
        return int(self._view.transform().m11() * 100)

    # ── Public API ────────────────────────────────────────────────────

    def set_tool(self, tool: str):
        self._scene.set_tool(tool)
        cursors = {
            "select": Qt.CursorShape.ArrowCursor,
            "pan": Qt.CursorShape.OpenHandCursor,
            "delete": Qt.CursorShape.ForbiddenCursor,
            "label": Qt.CursorShape.IBeamCursor,
            "equal": Qt.CursorShape.PointingHandCursor,
        }
        self._view.setCursor(cursors.get(tool, Qt.CursorShape.CrossCursor))

    def set_draw_color(self, color: QColor):
        self._scene.set_draw_color(color)

    def add_point(self, label: str, x: float, y: float):
        self._scene.add_point(label, x, y)

    def add_segment(self, from_label: str, to_label: str):
        self._scene.add_segment(from_label, to_label)

    def add_circle(self, center_label: str, radius: float):
        self._scene.add_circle(center_label, radius)

    def clear(self):
        self._scene.clear_all()

    def fit_to_contents(self):
        """Reset zoom to 100% and centre the view on the loaded objects
        (ignoring background grid lines)."""
        self._view.resetTransform()
        rect = self._scene.objects_bounding_rect()
        if not rect.isNull() and not rect.isEmpty():
            self._view.centerOn(rect.center())
        if self.zoom_changed:
            self.zoom_changed()

    def get_state(self) -> dict:
        return self._scene.get_state()

    def undo(self):
        self._scene.undo()

    def redo(self):
        self._scene.redo()
