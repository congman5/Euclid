"""
proof_panel.py — Fitch-style proof view (read-only display + interactive selection).

Layout per line (left to right):
  [line#] [scope bars...] [formula                  ] [status] [justification : refs]

Features:
  • Vertical teal scope bars for subproof nesting
  • Assumption lines marked with ▼ and faint background
  • Invalid lines highlighted red/pink
  • Click to select → highlights cited lines
  • Inline diagnostic tooltips
"""
from __future__ import annotations

import math
from typing import Dict, List, Optional, Tuple

from PyQt6.QtCore import Qt, QRect, QRectF, QSize, pyqtSignal, QPoint
from PyQt6.QtGui import (
    QColor, QFont, QFontMetrics, QPainter, QPen, QBrush,
    QMouseEvent, QPaintEvent, QResizeEvent, QWheelEvent,
)
from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QScrollArea, QFrame, QLabel, QSizePolicy,
    QToolTip,
)

from .fitch_theme import C, Fonts, Sp, Sym


# ═══════════════════════════════════════════════════════════════════════════
# DATA STRUCTURES
# ═══════════════════════════════════════════════════════════════════════════

class ProofLineData:
    """Flat representation of a proof line for display."""
    __slots__ = (
        "line_id", "depth", "formula_text", "justification", "refs",
        "is_assumption", "status", "diagnostics", "is_goal_line",
    )

    def __init__(
        self,
        line_id: int,
        depth: int,
        formula_text: str,
        justification: str,
        refs: List[int],
        is_assumption: bool = False,
        status: str = "pending",   # "valid", "invalid", "pending"
        diagnostics: List[dict] | None = None,
        is_goal_line: bool = False,
    ):
        self.line_id = line_id
        self.depth = depth
        self.formula_text = formula_text
        self.justification = justification
        self.refs = refs
        self.is_assumption = is_assumption
        self.status = status
        self.diagnostics = diagnostics or []
        self.is_goal_line = is_goal_line


# ═══════════════════════════════════════════════════════════════════════════
# PROOF VIEW WIDGET — Custom-painted Fitch proof display
# ═══════════════════════════════════════════════════════════════════════════

class FitchProofView(QWidget):
    """Custom-painted proof line display, modeled after the Fitch proof tool."""

    line_selected = pyqtSignal(int)       # emits line_id
    line_double_clicked = pyqtSignal(int)

    def __init__(self, parent=None):
        super().__init__(parent)
        self._lines: List[ProofLineData] = []
        self._selected_id: int = -1
        self._hovered_row: int = -1
        self._line_rects: List[QRect] = []
        self._max_depth: int = 0
        self._scope_ranges: List[Tuple[int, int, int]] = []  # (depth, start_row, end_row)

        self.setMouseTracking(True)
        self.setFocusPolicy(Qt.FocusPolicy.ClickFocus)
        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)

        self._font_formula = Fonts.formula(14)
        self._font_just = Fonts.ui(12)
        self._font_lineno = Fonts.line_number(11)
        self._font_status = Fonts.ui_bold(13)

    # ── Public API ────────────────────────────────────────────────────

    def set_lines(self, lines: List[ProofLineData]):
        self._lines = lines
        self._max_depth = max((l.depth for l in lines), default=0)
        self._compute_scope_ranges()
        self._selected_id = -1
        self._hovered_row = -1
        h = len(lines) * Sp.line_height + Sp.padding * 2
        self.setMinimumHeight(max(h, 100))
        self.setFixedHeight(max(h, 100))
        self.update()

    def select_line(self, line_id: int):
        self._selected_id = line_id
        self.line_selected.emit(line_id)
        self.update()

    def get_selected_id(self) -> int:
        return self._selected_id

    # ── Scope computation ─────────────────────────────────────────────

    def _compute_scope_ranges(self):
        """Compute contiguous depth ranges for drawing scope bars."""
        self._scope_ranges = []
        if not self._lines:
            return
        # For each depth d > 0, find contiguous runs of lines at depth >= d
        for d in range(1, self._max_depth + 1):
            start = None
            for i, line in enumerate(self._lines):
                if line.depth >= d:
                    if start is None:
                        start = i
                else:
                    if start is not None:
                        self._scope_ranges.append((d, start, i - 1))
                        start = None
            if start is not None:
                self._scope_ranges.append((d, start, len(self._lines) - 1))

    # ── Geometry helpers ──────────────────────────────────────────────

    def _row_y(self, row: int) -> int:
        return Sp.padding + row * Sp.line_height

    def _formula_x(self, depth: int) -> int:
        return Sp.line_number_width + Sp.scope_indent * (depth + 1) + Sp.padding

    def _just_x(self) -> int:
        return max(self.width() - Sp.just_min_width - Sp.padding, self.width() // 2)

    def _row_at(self, y: int) -> int:
        row = (y - Sp.padding) // Sp.line_height
        return max(0, min(row, len(self._lines) - 1))

    # ── Paint ─────────────────────────────────────────────────────────

    def paintEvent(self, event: QPaintEvent):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)

        # Background
        p.fillRect(self.rect(), QColor(C.surface))

        if not self._lines:
            p.setFont(Fonts.ui(13))
            p.setPen(QColor(C.text_muted))
            p.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter, "No proof loaded")
            p.end()
            return

        fm_formula = QFontMetrics(self._font_formula)
        fm_just = QFontMetrics(self._font_just)
        fm_lineno = QFontMetrics(self._font_lineno)
        just_x = self._just_x()

        self._line_rects = []
        cited_ids = set()
        if self._selected_id >= 0:
            sel_line = next((l for l in self._lines if l.line_id == self._selected_id), None)
            if sel_line:
                cited_ids = set(sel_line.refs)

        for row, line in enumerate(self._lines):
            y = self._row_y(row)
            rect = QRect(0, y, self.width(), Sp.line_height)
            self._line_rects.append(rect)

            # ── Row background ────────────────────────────────────
            if line.line_id == self._selected_id:
                p.fillRect(rect, QColor(C.surface_selected))
            elif line.line_id in cited_ids:
                p.fillRect(rect, QColor("#f0f8ff"))
            elif row == self._hovered_row:
                p.fillRect(rect, QColor(C.surface_hover))
            elif line.status == "invalid":
                p.fillRect(rect, QColor(C.error_bg))
            elif line.is_assumption:
                p.fillRect(rect, QColor(C.assumption_bg))

            # ── Scope bars ────────────────────────────────────────
            for depth, s_start, s_end in self._scope_ranges:
                if s_start <= row <= s_end:
                    bar_x = Sp.line_number_width + Sp.scope_indent * depth + Sp.padding_sm
                    bar_y_top = self._row_y(s_start)
                    bar_y_bot = self._row_y(s_end) + Sp.line_height
                    # Only draw segment within this row's paint area for efficiency
                    p.setPen(QPen(QColor(C.scope_bar), Sp.scope_bar_width))
                    seg_top = max(bar_y_top, y)
                    seg_bot = min(bar_y_bot, y + Sp.line_height)
                    p.drawLine(bar_x, seg_top, bar_x, seg_bot)
                    # Horizontal tick at assumption start
                    if row == s_start:
                        p.drawLine(bar_x, bar_y_top, bar_x + 10, bar_y_top)

            # ── Line number ───────────────────────────────────────
            p.setFont(self._font_lineno)
            p.setPen(QColor(C.text_muted))
            ln_rect = QRect(0, y, Sp.line_number_width, Sp.line_height)
            p.drawText(ln_rect, Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter,
                       str(line.line_id) + ".")

            # ── Assumption indicator ──────────────────────────────
            formula_x = self._formula_x(line.depth)
            if line.is_assumption:
                p.setFont(self._font_status)
                p.setPen(QColor(C.scope_bar))
                p.drawText(formula_x - 16, y, 16, Sp.line_height,
                           Qt.AlignmentFlag.AlignCenter, Sym.assumption)

            # ── Formula text ──────────────────────────────────────
            p.setFont(self._font_formula)
            p.setPen(QColor(C.text_formula))
            formula_rect = QRect(formula_x, y, just_x - formula_x - 8, Sp.line_height)
            elided = fm_formula.elidedText(line.formula_text, Qt.TextElideMode.ElideRight, formula_rect.width())
            p.drawText(formula_rect, Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter, elided)

            # ── Status icon ───────────────────────────────────────
            status_x = just_x - Sp.status_width - 4
            p.setFont(self._font_status)
            if line.status == "valid":
                p.setPen(QColor(C.valid))
                p.drawText(status_x, y, Sp.status_width, Sp.line_height,
                           Qt.AlignmentFlag.AlignCenter, Sym.check)
            elif line.status == "invalid":
                p.setPen(QColor(C.invalid))
                p.drawText(status_x, y, Sp.status_width, Sp.line_height,
                           Qt.AlignmentFlag.AlignCenter, Sym.cross)
            else:
                p.setPen(QColor(C.pending))
                p.drawText(status_x, y, Sp.status_width, Sp.line_height,
                           Qt.AlignmentFlag.AlignCenter, Sym.pending)

            # ── Justification + refs ──────────────────────────────
            p.setFont(self._font_just)
            p.setPen(QColor(C.text_just))
            just_text = line.justification
            if line.refs:
                just_text += "  :" + ",".join(str(r) for r in line.refs)
            just_rect = QRect(just_x, y, self.width() - just_x - Sp.padding, Sp.line_height)
            p.drawText(just_rect, Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter, just_text)

            # ── Bottom border ─────────────────────────────────────
            p.setPen(QPen(QColor(C.border_light), 1))
            p.drawLine(0, y + Sp.line_height - 1, self.width(), y + Sp.line_height - 1)

        p.end()

    # ── Mouse interaction ─────────────────────────────────────────────

    def mousePressEvent(self, event: QMouseEvent):
        if event.button() == Qt.MouseButton.LeftButton:
            row = self._row_at(event.pos().y())
            if 0 <= row < len(self._lines):
                self.select_line(self._lines[row].line_id)

    def mouseDoubleClickEvent(self, event: QMouseEvent):
        if event.button() == Qt.MouseButton.LeftButton:
            row = self._row_at(event.pos().y())
            if 0 <= row < len(self._lines):
                self.line_double_clicked.emit(self._lines[row].line_id)

    def mouseMoveEvent(self, event: QMouseEvent):
        row = self._row_at(event.pos().y())
        if row != self._hovered_row:
            self._hovered_row = row
            self.update()
        # Tooltip for diagnostics
        if 0 <= row < len(self._lines):
            line = self._lines[row]
            if line.diagnostics:
                tip = "\n".join(f"[{d.get('code','')}] {d.get('message','')}" for d in line.diagnostics)
                QToolTip.showText(event.globalPosition().toPoint(), tip, self)
            else:
                QToolTip.hideText()

    def leaveEvent(self, event):
        self._hovered_row = -1
        self.update()


# ═══════════════════════════════════════════════════════════════════════════
# GOALS PANEL — Shows proof goal and its verification status
# ═══════════════════════════════════════════════════════════════════════════

class GoalsPanel(QFrame):
    """Bottom panel showing the proof goal (like Fitch's Goals section)."""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setStyleSheet(f"""
            GoalsPanel {{
                background: {C.goal_bg};
                border-top: 1px solid {C.goal_border};
            }}
        """)
        layout = QVBoxLayout(self)
        layout.setContentsMargins(Sp.padding, Sp.padding_sm, Sp.padding, Sp.padding_sm)
        layout.setSpacing(4)

        header = QLabel("Goals")
        header.setFont(Fonts.heading(11))
        header.setStyleSheet(f"color: {C.text_secondary};")
        header.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(header)

        self._goal_row = QWidget()
        gl = _GoalLineLayout(self._goal_row)
        self._goal_label = gl.formula_label
        self._goal_status = gl.status_label
        layout.addWidget(self._goal_row)

    def set_goal(self, goal_text: str, achieved: bool | None = None):
        self._goal_label.setText(f"{Sym.turnstile}  {goal_text}")
        self._goal_label.setFont(Fonts.formula(14))
        if achieved is True:
            self._goal_status.setText(Sym.check)
            self._goal_status.setStyleSheet(f"color: {C.valid}; font-size: 16px; font-weight: bold;")
        elif achieved is False:
            self._goal_status.setText(Sym.cross)
            self._goal_status.setStyleSheet(f"color: {C.invalid}; font-size: 16px; font-weight: bold;")
        else:
            self._goal_status.setText("")


class _GoalLineLayout:
    def __init__(self, parent):
        layout = QHBoxLayout(parent)
        layout.setContentsMargins(Sp.padding_lg, Sp.padding_sm, Sp.padding_lg, Sp.padding_sm)
        self.formula_label = QLabel()
        self.formula_label.setFont(Fonts.formula(14))
        self.formula_label.setStyleSheet(f"color: {C.text_formula};")
        layout.addWidget(self.formula_label, stretch=1)
        self.status_label = QLabel()
        layout.addWidget(self.status_label)


# ═══════════════════════════════════════════════════════════════════════════
# COMPOSITE PROOF PANEL (scroll area + goals)
# ═══════════════════════════════════════════════════════════════════════════

from PyQt6.QtWidgets import QHBoxLayout


class ProofPanel(QWidget):
    """Complete proof display: scrollable Fitch view + goals panel at bottom."""

    line_selected = pyqtSignal(int)

    def __init__(self, parent=None):
        super().__init__(parent)
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Scrollable proof view
        self._scroll = QScrollArea()
        self._scroll.setWidgetResizable(True)
        self._scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self._proof_view = FitchProofView()
        self._proof_view.line_selected.connect(self.line_selected.emit)
        self._scroll.setWidget(self._proof_view)
        layout.addWidget(self._scroll, stretch=1)

        # Goals panel
        self._goals = GoalsPanel()
        layout.addWidget(self._goals)

    @property
    def proof_view(self) -> FitchProofView:
        return self._proof_view

    @property
    def goals_panel(self) -> GoalsPanel:
        return self._goals

    def set_proof_data(self, lines: List[ProofLineData], goal_text: str = "",
                       goal_achieved: bool | None = None):
        self._proof_view.set_lines(lines)
        self._goals.set_goal(goal_text, goal_achieved)

    def scroll_to_line(self, line_id: int):
        for i, ld in enumerate(self._proof_view._lines):
            if ld.line_id == line_id:
                y = self._proof_view._row_y(i)
                self._scroll.ensureVisible(0, y, 0, Sp.line_height * 2)
                break
