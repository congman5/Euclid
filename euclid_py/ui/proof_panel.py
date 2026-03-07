"""Proof Panel -- PyQt6 Fitch-style proof journal.

True Fitch-style proof display:
  - Each proof line is an inline-editable widget row
  - Scope bars painted on the left for subproof nesting
  - Rule dropdown on each line opens a popup picker (System E rules)
  - Refs box next to the rule on each line
  - Insert bar between lines to add new steps
  - Subproofs: button opens a new scope with Assume line
  - Predicate palette aligned to System E syntax (§3.3-§3.7)
  - Declarations row (Points / Lines)
  - Premises section with formal predicates
  - Goals / conclusion with turnstile
  - Eval Step / Eval All wired to verifier via unified_checker
  - Undo / redo (30 levels)
  - Save / Load proof JSON

Phase 9.1 of the implementation plan.
"""
from __future__ import annotations

import json
import re
from collections import OrderedDict
from typing import Dict, List, Optional

from PyQt6.QtCore import Qt, pyqtSignal, QSize, QTimer
from PyQt6.QtGui import (
    QColor, QFont, QPainter, QPen, QShortcut, QKeySequence,
    QFontMetrics, QBrush, QPalette,
)
from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QGridLayout, QLabel, QPushButton,
    QLineEdit, QComboBox, QListWidget, QListWidgetItem,
    QFrame, QScrollArea, QMenu, QFileDialog,
    QSizePolicy, QApplication, QAbstractItemView,
)


# ===================================================================
# RULE CATALOGUE — System E axioms grouped by paper section
# ===================================================================

def _build_rule_groups():
    """Build rule groups from System E axioms via unified_checker."""
    from verifier.unified_checker import get_available_rules
    rules = get_available_rules()
    # Group by category, preserving paper section order
    _CAT_LABELS = OrderedDict([
        ("construction", "Construction (§3.3)"),
        ("diagrammatic", "Diagrammatic (§3.4)"),
        ("metric", "Metric (§3.5)"),
        ("transfer", "Transfer (§3.6)"),
        ("superposition", "Superposition (§3.7)"),
        ("proposition", "Propositions"),
    ])
    groups = OrderedDict()
    for cat, label in _CAT_LABELS.items():
        names = [r.name for r in rules if r.category == cat]
        if names:
            groups[label] = names
    return groups


_RULE_KIND_MAP = {}  # Kept empty — legacy mapping no longer needed

RULE_GROUPS = _build_rule_groups()

ALL_RULE_NAMES = []
for _rules in RULE_GROUPS.values():
    ALL_RULE_NAMES.extend(_rules)


# ===================================================================
# PREDICATE PALETTE
# ===================================================================

CONNECTIVES = ["\u2227", "\u2228", "\u00ac", "\u2194",
               "\u22a5", "=", "\u2260", "\u2203", "\u2203!", "\u2200", "(", ")", ","]
CONNECTIVE_MAP = {
    "\u2227": " \u2227 ", "\u2228": " \u2228 ", "\u00ac": "\u00ac",
    "\u2194": " \u2194 ",
    "\u22a5": "\u22a5", "=": " = ", "\u2260": " \u2260 ",
    "\u2203": "\u2203", "\u2203!": "\u2203!",
    "\u2200": "\u2200",
    "(": "(", ")": ")", ",": ", ",
}

PREDICATES = [
    # Incidence (§3.4)
    ("on(a,L)", "on(,)"), ("on(a,α)", "on(,)"),
    ("center(a,α)", "center(,)"),
    ("inside(a,α)", "inside(,)"),
    # Betweenness & collinearity (§3.4)
    ("between", "between(,,)"),
    ("same-side", "same-side(,,)"),
    # Constructions (§3.3)
    ("let L=line", "let L be line(,)"),
    ("let α=circle", "let α be circle(,)"),
    ("intersects", "intersects(,)"),
    # Equality / inequality
    ("a≠b", "¬( = )"), ("a=b", " = "),
    # Metric predicates (§3.5)
    ("ab=cd", " = "), ("ab<cd", " < "),
    ("∠abc=∠def", "∠ = ∠"),
    ("∠abc<∠def", "∠ < ∠"),
    # Special
    ("¬intersects", "¬intersects(,)"),
    ("right∠", "right-angle"),
    ("△", "△"),
]

# Greek letters for geometric proofs (circles, angles, etc.)
GREEK_LETTERS = [
    "α", "β", "γ", "δ", "ε", "ζ", "η", "θ",
    "ι", "κ", "λ", "μ", "ν", "ξ", "ρ",
    "σ", "τ", "φ", "χ", "ψ", "ω",
]


# ===================================================================
# DATA
# ===================================================================

class ProofStep:
    def __init__(self, line_number, text, justification, refs, depth=0):
        self.line_number = line_number
        self.text = text
        self.justification = justification
        self.refs = refs
        self.depth = depth
        self.status = "?"


UNDO_LIMIT = 30

_FONT = QFont("Segoe UI", 11)
_FONT.setStyleHint(QFont.StyleHint.SansSerif)
_FONT_SMALL = QFont("Segoe UI", 10)
_FONT_SMALL.setStyleHint(QFont.StyleHint.SansSerif)
_FONT_BOLD = QFont("Segoe UI", 11, QFont.Weight.Bold)
_HEADER_FONT = QFont("Segoe UI", 12, QFont.Weight.Bold)

_SCOPE_BAR_COLOR = QColor("#388c6b")
_BG_PANEL = "#f0f1f3"
_BG_LINE = "#f7f8fa"
_BG_WHITE = "#ffffff"
_BORDER_LINE = "#dcdee3"
_TEXT_DARK = "#1a1a2e"
_TEXT_GREEN = "#2e8b57"
_SEL_BG = "#dce8f7"


# ===================================================================
# FITCH LINE WIDGET
# ===================================================================

class FitchLineWidget(QFrame):
    """One proof line: scope bars | line# | formula | status | rule :refs"""

    text_changed = pyqtSignal(int)
    rule_changed = pyqtSignal(int)
    refs_changed = pyqtSignal(int)
    selected = pyqtSignal(int)
    delete_requested = pyqtSignal(int)

    SCOPE_BAR_W = 14

    def __init__(self, step, parent=None):
        super().__init__(parent)
        self.step = step
        self._is_selected = False
        self.setFrameShape(QFrame.Shape.NoFrame)
        self.setCursor(Qt.CursorShape.ArrowCursor)
        self.setMinimumHeight(34)
        self.setSizePolicy(QSizePolicy.Policy.Expanding,
                           QSizePolicy.Policy.Fixed)

        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 6, 0)
        lay.setSpacing(0)

        # Scope bar spacer
        self._bar_spacer = QWidget()
        bar_w = max(8, self.SCOPE_BAR_W * step.depth + 8)
        self._bar_spacer.setFixedWidth(bar_w)
        self._bar_spacer.setMinimumHeight(34)
        lay.addWidget(self._bar_spacer)

        # Line number
        self._num_label = QLabel(str(step.line_number) + ".")
        self._num_label.setFont(_FONT_SMALL)
        self._num_label.setFixedWidth(28)
        self._num_label.setAlignment(
            Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
        self._num_label.setStyleSheet(
            "color:#888; padding-right:4px; background:transparent;")
        lay.addWidget(self._num_label)

        # Formula text (inline editable)
        self._text_edit = QLineEdit(step.text)
        self._text_edit.setFont(_FONT)
        self._text_edit.setFrame(False)
        self._text_edit.setObjectName("fitch_formula")
        self._text_edit.setStyleSheet(
            "#fitch_formula { background:transparent; color:" + _TEXT_DARK + ";"
            " padding:4px 6px; border:none; }"
            "#fitch_formula:focus { background:" + _BG_WHITE + ";"
            " border:1px solid #5ca4e6; border-radius:2px; }")
        self._text_edit.textChanged.connect(self._on_text_changed)
        lay.addWidget(self._text_edit, stretch=1)

        # Status indicator
        self._status_label = QLabel(self._status_char())
        self._status_label.setFont(_FONT_BOLD)
        self._status_label.setFixedWidth(22)
        self._status_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._status_label.setStyleSheet("background:transparent;")
        self._update_status_style()
        lay.addWidget(self._status_label)

        is_assume = step.justification == "Assume"

        # Rule dropdown button (visible arrow)
        self._rule_btn = QPushButton("\u25bc")
        self._rule_btn.setFont(_FONT_SMALL)
        self._rule_btn.setFixedSize(22, 22)
        self._rule_btn.setObjectName("rule_drop_btn")
        self._rule_btn.setStyleSheet(
            "#rule_drop_btn { background:#e8ede8; border:1px solid #c8d0c8;"
            " border-radius:3px; color:" + _TEXT_GREEN + "; font-size:10px; }"
            "#rule_drop_btn:hover { background:#d0e0d0;"
            " border-color:#388c6b; }")
        self._rule_btn.clicked.connect(self._show_rule_menu)
        if is_assume:
            self._rule_btn.setVisible(False)
        lay.addWidget(self._rule_btn)

        # Rule label
        rule_display = step.justification if not is_assume else ""
        self._rule_label = QLabel(rule_display)
        self._rule_label.setFont(_FONT_SMALL)
        self._rule_label.setStyleSheet(
            "color:" + _TEXT_GREEN + "; padding:0 2px;"
            " background:transparent;")
        self._rule_label.setMinimumWidth(40)
        if is_assume:
            self._rule_label.setVisible(False)
        lay.addWidget(self._rule_label)

        # Colon
        self._colon_label = QLabel(":")
        self._colon_label.setFont(_FONT_SMALL)
        self._colon_label.setStyleSheet(
            "color:" + _TEXT_GREEN + "; background:transparent;")
        self._colon_label.setFixedWidth(8)
        if is_assume:
            self._colon_label.setVisible(False)
        lay.addWidget(self._colon_label)

        # Refs box
        refs_text = ",".join(str(r) for r in step.refs) if step.refs else ""
        self._refs_edit = QLineEdit(refs_text)
        self._refs_edit.setFont(_FONT_SMALL)
        self._refs_edit.setFixedWidth(56)
        self._refs_edit.setFrame(False)
        self._refs_edit.setObjectName("fitch_refs")
        self._refs_edit.setStyleSheet(
            "#fitch_refs { background:transparent; color:" + _TEXT_GREEN + ";"
            " padding:2px 4px; border:none; }"
            "#fitch_refs:focus { background:" + _BG_WHITE + ";"
            " border:1px solid #5ca4e6; border-radius:2px; }")
        self._refs_edit.textChanged.connect(self._on_refs_changed)
        if is_assume:
            self._refs_edit.setVisible(False)
        lay.addWidget(self._refs_edit)

        # Delete button (✕) on each line
        self._del_btn = QPushButton("\u2715")
        self._del_btn.setFont(_FONT_SMALL)
        self._del_btn.setFixedSize(20, 20)
        self._del_btn.setObjectName("line_del_btn")
        self._del_btn.setStyleSheet(
            "#line_del_btn { background:transparent; color:#bbb;"
            " border:none; font-size:11px; padding:0; }"
            "#line_del_btn:hover { color:#d32f2f; }")
        self._del_btn.setToolTip("Delete this line")
        self._del_btn.clicked.connect(
            lambda: self.delete_requested.emit(self.step.line_number))
        lay.addWidget(self._del_btn)

        self._apply_base_style()

    def _status_char(self):
        return self.step.status

    def _update_status_style(self):
        s = self.step.status
        if s == "\u2713":
            color = "#2e8b57"
        elif s == "\u2717":
            color = "#cc3333"
        else:
            color = "#999"
        self._status_label.setText(self._status_char())
        self._status_label.setStyleSheet(
            "color:" + color + "; font-weight:bold;")

    def _apply_base_style(self):
        if self._is_selected:
            self.setStyleSheet(
                "FitchLineWidget { background:#e8e0f0;"
                " border-bottom:1px solid " + _BORDER_LINE + "; }"
                " FitchLineWidget QLabel { background:transparent; }"
                " FitchLineWidget QLineEdit { background:transparent; }")
        else:
            self.setStyleSheet(
                "FitchLineWidget { background:" + _BG_LINE + ";"
                " border-bottom:1px solid " + _BORDER_LINE + "; }"
                " FitchLineWidget QLabel { background:transparent; }"
                " FitchLineWidget QLineEdit { background:transparent; }")

    def set_selected(self, sel):
        self._is_selected = sel
        self._apply_base_style()
        self.update()  # repaint for red arrow

    def refresh_from_step(self):
        self._num_label.setText(str(self.step.line_number) + ".")
        if self._text_edit.text() != self.step.text:
            self._text_edit.blockSignals(True)
            self._text_edit.setText(self.step.text)
            self._text_edit.blockSignals(False)
        self._update_status_style()
        is_assume = self.step.justification == "Assume"
        self._rule_label.setText(
            self.step.justification if not is_assume else "")
        self._rule_btn.setVisible(not is_assume)
        self._rule_label.setVisible(not is_assume)
        self._colon_label.setVisible(not is_assume)
        self._refs_edit.setVisible(not is_assume)
        bar_w = max(8, self.SCOPE_BAR_W * self.step.depth + 8)
        self._bar_spacer.setFixedWidth(bar_w)

    def focus_text(self):
        self._text_edit.setFocus()
        self._text_edit.selectAll()

    def insert_at_cursor(self, text):
        cur = self._text_edit.cursorPosition()
        existing = self._text_edit.text()
        new = existing[:cur] + text + existing[cur:]
        self._text_edit.setText(new)
        paren_idx = text.find("(")
        if paren_idx >= 0:
            self._text_edit.setCursorPosition(cur + paren_idx + 1)
        else:
            self._text_edit.setCursorPosition(cur + len(text))
        self._text_edit.setFocus()

    def text_field(self):
        return self._text_edit

    def mousePressEvent(self, event):
        self.selected.emit(self.step.line_number)
        super().mousePressEvent(event)

    def paintEvent(self, event):
        super().paintEvent(event)
        painter = QPainter(self)
        h = self.height()
        # Always draw a continuous left border
        pen_border = QPen(QColor(_BORDER_LINE), 1)
        painter.setPen(pen_border)
        painter.drawLine(0, 0, 0, h)
        # Draw red arrow for selected line
        if self._is_selected:
            painter.setRenderHint(QPainter.RenderHint.Antialiasing)
            painter.setPen(Qt.PenStyle.NoPen)
            painter.setBrush(QBrush(QColor("#d32f2f")))
            cy = h // 2
            from PyQt6.QtGui import QPolygonF
            from PyQt6.QtCore import QPointF
            tri = QPolygonF([
                QPointF(2, cy - 6),
                QPointF(10, cy),
                QPointF(2, cy + 6),
            ])
            painter.drawPolygon(tri)
            painter.setRenderHint(QPainter.RenderHint.Antialiasing, False)
        # Draw scope bars for depth — no antialiasing for crisp straight lines
        if self.step.depth > 0:
            pen = QPen(_SCOPE_BAR_COLOR, 2)
            painter.setPen(pen)
            x_start = 4
            for d in range(self.step.depth):
                x = x_start + d * self.SCOPE_BAR_W
                painter.drawLine(x, 0, x, h)
            if self.step.justification == "Assume":
                x_left = x_start + (self.step.depth - 1) * self.SCOPE_BAR_W
                x_right = self.width() - 4
                y_bar = h - 2
                pen2 = QPen(_SCOPE_BAR_COLOR, 3)
                painter.setPen(pen2)
                painter.drawLine(x_left, y_bar, x_right, y_bar)
        painter.end()

    def _on_text_changed(self, txt):
        self.step.text = txt
        self.text_changed.emit(self.step.line_number)

    def _on_refs_changed(self, txt):
        parts = [p.strip() for p in txt.replace(";", ",").split(",")
                 if p.strip()]
        self.step.refs = [int(p) for p in parts if p.isdigit()]
        self.refs_changed.emit(self.step.line_number)

    def _show_rule_menu(self):
        menu = QMenu(self)
        menu.setStyleSheet(
            "QMenu { background:#fff; border:1px solid #ccc;"
            " padding:4px; font-size:12px; color:#1a1a2e; }"
            "QMenu::item { padding:4px 16px; color:#1a1a2e; }"
            "QMenu::item:selected { background:#e0ebff; color:#1a1a2e; }")
        for grp, rules in RULE_GROUPS.items():
            sub = menu.addMenu(grp)
            for r in rules:
                act = sub.addAction(r)
                act.triggered.connect(
                    lambda checked, rule=r: self._set_rule(rule))
        # Lemmas submenu
        panel = self._find_proof_panel()
        if panel and panel._lemmas:
            lemma_sub = menu.addMenu("Lemmas")
            lemma_sub.setStyleSheet(
                "QMenu { background:#fff; border:1px solid #ccc;"
                " padding:4px; font-size:12px; color:#1a1a2e; }"
                "QMenu::item { padding:4px 16px; color:#1a1a2e; }"
                "QMenu::item:selected { background:#e0ebff; color:#1a1a2e; }")
            for lem in panel._lemmas:
                act = lemma_sub.addAction(lem.display_name())
                act.setToolTip(lem.schema_text())
                act.triggered.connect(
                    lambda checked, rule=lem.rule_name: self._set_rule(rule))
        menu.exec(self._rule_btn.mapToGlobal(
            self._rule_btn.rect().bottomLeft()))

    def _find_proof_panel(self):
        """Walk up the widget tree to find the parent ProofPanel."""
        w = self.parent()
        while w is not None:
            if isinstance(w, ProofPanel):
                return w
            w = w.parent()
        return None

    def _set_rule(self, rule):
        self.step.justification = rule
        is_assume = rule == "Assume"
        self._rule_label.setText(rule if not is_assume else "")
        self._rule_btn.setVisible(not is_assume)
        self._rule_label.setVisible(not is_assume)
        self._colon_label.setVisible(not is_assume)
        self._refs_edit.setVisible(not is_assume)
        self.rule_changed.emit(self.step.line_number)


# ===================================================================
# INSERT BAR
# ===================================================================

class InsertBar(QFrame):
    """Thin bar between proof lines. Hover shows +; click inserts."""

    insert_requested = pyqtSignal(int)
    SCOPE_BAR_W = 14

    def __init__(self, position, depth=0, parent=None):
        super().__init__(parent)
        self._position = position
        self._depth = depth
        self.setFixedHeight(2)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setStyleSheet("InsertBar { background:transparent; }")
        self.setMouseTracking(True)

    def enterEvent(self, event):
        self.setFixedHeight(14)
        self.setStyleSheet(
            "InsertBar { background:#388c6b; border-radius:2px; }")
        self.update()

    def leaveEvent(self, event):
        self.setFixedHeight(2)
        self.setStyleSheet("InsertBar { background:transparent; }")
        self.update()

    def paintEvent(self, event):
        super().paintEvent(event)
        p = QPainter(self)
        h = self.height()
        # Always draw left border
        p.setPen(QPen(QColor(_BORDER_LINE), 1))
        p.drawLine(0, 0, 0, h)
        # Draw scope bars to match adjacent lines — no antialiasing
        if self._depth > 0:
            pen = QPen(_SCOPE_BAR_COLOR, 2)
            p.setPen(pen)
            x_start = 4
            for d in range(self._depth):
                x = x_start + d * self.SCOPE_BAR_W
                p.drawLine(x, 0, x, h)
        if h > 10:
            p.setRenderHint(QPainter.RenderHint.Antialiasing)
            p.setPen(QPen(QColor("#ffffff"), 2))
            cx = self.width() // 2
            cy = h // 2
            p.drawLine(cx - 5, cy, cx + 5, cy)
            p.drawLine(cx, cy - 5, cx, cy + 5)
        p.end()

    def mousePressEvent(self, event):
        self.insert_requested.emit(self._position)


# ===================================================================
# FITCH BAR — thick line between premises and proof body
# ===================================================================

class FitchBar(QFrame):
    """Thick horizontal bar separating premises from proof steps (Fitch convention)."""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setFixedHeight(4)
        self.setStyleSheet("FitchBar { background:#1a1a2e; }")


# ===================================================================
# ADD LINE BAR — permanent bottom row for adding new lines
# ===================================================================

class AddLineBar(QFrame):
    """Clickable row at the bottom of the proof to add a new line."""

    add_requested = pyqtSignal()

    def __init__(self, hover_text="+ Click to add a new line", parent=None):
        super().__init__(parent)
        self._hover_text = hover_text
        self.setFixedHeight(32)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setStyleSheet(
            "AddLineBar { background:transparent;"
            " border-bottom:1px solid " + _BORDER_LINE + "; }")
        self.setMouseTracking(True)
        lay = QHBoxLayout(self)
        lay.setContentsMargins(12, 0, 12, 0)
        self._label = QLabel("")
        self._label.setFont(_FONT_SMALL)
        self._label.setStyleSheet("color:#aaa; background:transparent;")
        lay.addWidget(self._label)
        lay.addStretch()

    def enterEvent(self, event):
        self._label.setText(self._hover_text)
        self._label.setStyleSheet("color:#388c6b; background:transparent;")
        self.setStyleSheet(
            "AddLineBar { background:#f0f8f0;"
            " border-bottom:1px solid " + _BORDER_LINE + "; }")

    def leaveEvent(self, event):
        self._label.setText("")
        self._label.setStyleSheet("color:#aaa; background:transparent;")
        self.setStyleSheet(
            "AddLineBar { background:transparent;"
            " border-bottom:1px solid " + _BORDER_LINE + "; }")

    def mousePressEvent(self, event):
        self.add_requested.emit()


# ===================================================================
# PROOF PANEL WIDGET
# ===================================================================

# ===================================================================
# LEMMA DATA
# ===================================================================

class LoadedLemma:
    """A previously-verified proof loaded as a reusable lemma."""
    def __init__(self, name, premises, goal, file_path):
        self.name = name
        self.premises = premises  # list of formula strings
        self.goal = goal          # conclusion formula string
        self.file_path = file_path
        self.rule_name = "Lemma:" + name  # justification name

    def display_name(self):
        return self.name

    def schema_text(self):
        if self.premises:
            return ", ".join(self.premises) + "  \u2192  " + self.goal
        return "\u2014  \u2192  " + self.goal


class ProofPanel(QWidget):
    """Fitch-style proof journal sidebar."""

    step_changed = pyqtSignal()

    def __init__(self):
        super().__init__()
        self._steps = []
        self._premises = []
        self._conclusion = ""
        self._proof_name = "workspace_proof"
        self._selected = -1
        self._selected_prem = -1  # index into self._premises
        self._current_depth = 0
        self._undo_stack = []
        self._redo_stack = []
        self._decl_points = []
        self._decl_lines = []
        self._line_widgets = []
        self._prem_widgets = []
        self._focused_text_field = None
        self._lemmas: List[LoadedLemma] = []
        self.setMinimumWidth(380)
        self.setStyleSheet(
            "ProofPanel { background:" + _BG_PANEL + ";"
            " border-left:1px solid #c0c2c8; }")

        root = QVBoxLayout(self)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)

        # -- Header --
        header = QFrame()
        header.setObjectName("proof_header")
        header.setStyleSheet(
            "#proof_header { background:" + _BG_PANEL + ";"
            " border-bottom:2px solid #388c6b; }"
            "#proof_header QLabel { background:transparent; }")
        hvbox = QVBoxLayout(header)
        hvbox.setContentsMargins(10, 4, 10, 4)
        hvbox.setSpacing(2)
        # Row 1: title + eval buttons
        row1 = QHBoxLayout()
        row1.setSpacing(4)
        lbl = QLabel("Proof Journal")
        lbl.setFont(_HEADER_FONT)
        lbl.setStyleSheet("color:#1a1a2e;")
        row1.addWidget(lbl)
        row1.addStretch()
        for text, tip, cb in [
            ("Eval", "Evaluate selected step", self._eval_selected),
            ("All", "Evaluate all steps", self._eval_all),
        ]:
            b = QPushButton(text)
            b.setFont(_FONT_SMALL)
            b.setStyleSheet(
                "QPushButton{background:#388c6b;color:white;border:none;"
                "border-radius:3px;padding:3px 10px;font-size:11px;}"
                "QPushButton:hover{background:#2e7358;}")
            b.clicked.connect(cb)
            row1.addWidget(b)
        self._count_label = QLabel("")
        self._count_label.setFont(_FONT_SMALL)
        self._count_label.setStyleSheet(
            "color:#5a5a72;font-size:11px;padding:0 4px;")
        row1.addWidget(self._count_label)
        hvbox.addLayout(row1)
        # Row 2: file / edit buttons
        row2 = QHBoxLayout()
        row2.setSpacing(3)
        row2.addStretch()
        _btn_style = (
            "QPushButton{background:transparent;color:#5a5a72;"
            "border:1px solid #c0c2c8;border-radius:3px;"
            "padding:2px 6px;font-size:10px;}"
            "QPushButton:hover{background:#e0e2e8;"
            "border-color:#888;}")
        for text_label, tip, cb in [
            ("Undo", "Undo (Ctrl+Z)", self._undo),
            ("Redo", "Redo (Ctrl+Y)", self._redo),
            ("Save", "Save proof JSON (Ctrl+S)", self._save_proof),
            ("Load", "Load proof JSON", self._load_proof),
            ("Lemma", "Load a verified proof as a lemma", self._load_lemma),
        ]:
            b = QPushButton(text_label)
            b.setFont(QFont("Segoe UI", 9))
            b.setToolTip(tip)
            b.setFixedHeight(22)
            b.setStyleSheet(_btn_style)
            b.clicked.connect(cb)
            row2.addWidget(b)
        hvbox.addLayout(row2)
        root.addWidget(header)

        # -- Predicate palette --
        palette = QFrame()
        palette.setObjectName("pred_palette")
        palette.setStyleSheet(
            "#pred_palette { background:#e8eaee;"
            " border-bottom:1px solid #c0c2c8; }"
            "#pred_palette QPushButton { background:#f7f8fa; color:#1a1a2e;"
            " border:1px solid #c0c2c8; border-radius:3px;"
            " padding:0px 3px; font-size:10px; min-width:0px; }"
            "#pred_palette QPushButton:hover { background:#dce0e8;"
            " border-color:#888; }")
        pl = QVBoxLayout(palette)
        pl.setContentsMargins(4, 3, 4, 3)
        pl.setSpacing(1)

        # Grid for connectives + Greek letters (compact)
        sym_grid = QGridLayout()
        sym_grid.setSpacing(2)
        sym_grid.setContentsMargins(0, 0, 0, 0)
        col = 0
        for sym in CONNECTIVES:
            b = QPushButton(sym)
            b.setFixedHeight(20)
            b.setFont(_FONT_SMALL)
            ins = CONNECTIVE_MAP.get(sym, sym)
            b.clicked.connect(
                lambda _, t=ins: self._insert_into_focused(t))
            sym_grid.addWidget(b, 0, col)
            col += 1
        cols_per_row = col  # number of columns established by connectives
        col = 0
        for letter in GREEK_LETTERS:
            b = QPushButton(letter)
            b.setFixedHeight(20)
            b.setFont(_FONT_SMALL)
            b.setToolTip(letter)
            b.clicked.connect(
                lambda _, t=letter: self._insert_into_focused(t))
            row = 1 + col // cols_per_row
            sym_grid.addWidget(b, row, col % cols_per_row)
            col += 1
        pl.addLayout(sym_grid)

        # Grid for predicates (use fewer columns so buttons aren't squished)
        pred_cols = min(cols_per_row, 5)
        pred_grid = QGridLayout()
        pred_grid.setSpacing(2)
        pred_grid.setContentsMargins(0, 0, 0, 0)
        for i, (name, tmpl) in enumerate(PREDICATES):
            b = QPushButton(name)
            b.setToolTip(tmpl)
            b.setFont(QFont("Segoe UI", 8))
            b.setFixedHeight(18)
            b.setSizePolicy(QSizePolicy.Policy.Preferred,
                            QSizePolicy.Policy.Fixed)
            b.setMinimumWidth(b.fontMetrics().horizontalAdvance(name) + 12)
            b.clicked.connect(
                lambda _, t=tmpl: self._insert_into_focused(t))
            pred_grid.addWidget(b, i // pred_cols, i % pred_cols)
        pl.addLayout(pred_grid)
        root.addWidget(palette)

        # -- Lemma section (collapsible list of loaded lemmas) --
        self._lemma_frame = QFrame()
        self._lemma_frame.setObjectName("lemma_frame")
        self._lemma_frame.setStyleSheet(
            "#lemma_frame { background:#eef0f5;"
            " border-bottom:1px solid #c0c2c8; }"
            "#lemma_frame QLabel { background:transparent; }")
        self._lemma_layout = QVBoxLayout(self._lemma_frame)
        self._lemma_layout.setContentsMargins(8, 4, 8, 4)
        self._lemma_layout.setSpacing(2)
        lemma_header = QLabel("Lemmas")
        lemma_header.setFont(QFont("Segoe UI", 10))
        lemma_header.setStyleSheet("color:#5a5a72;")
        self._lemma_layout.addWidget(lemma_header)
        self._lemma_list_container = QVBoxLayout()
        self._lemma_list_container.setSpacing(2)
        self._lemma_layout.addLayout(self._lemma_list_container)
        self._lemma_empty_label = QLabel("No lemmas loaded. Click Lemma to add one.")
        self._lemma_empty_label.setFont(QFont("Segoe UI", 9))
        self._lemma_empty_label.setStyleSheet("color:#aaa; font-style:italic;")
        self._lemma_list_container.addWidget(self._lemma_empty_label)
        root.addWidget(self._lemma_frame)

        # -- Declarations (hidden, used internally for verifier) --
        self._points_input = QLineEdit()
        self._points_input.setVisible(False)
        self._lines_input = QLineEdit()
        self._lines_input.setVisible(False)

        # -- Proof lines scroll area (premises + Fitch bar + proof steps) --
        self._scroll = QScrollArea()
        self._scroll.setObjectName("proof_scroll")
        self._scroll.setWidgetResizable(True)
        self._scroll.setStyleSheet(
            "#proof_scroll { border:none; background:" + _BG_PANEL + "; }")
        self._lines_container = QWidget()
        self._lines_container.setObjectName("proof_lines_container")
        self._lines_container.setStyleSheet(
            "#proof_lines_container { background:" + _BG_PANEL + "; }")
        self._lines_layout = QVBoxLayout(self._lines_container)
        self._lines_layout.setContentsMargins(0, 0, 0, 0)
        self._lines_layout.setSpacing(0)
        self._lines_layout.addStretch()
        self._scroll.setWidget(self._lines_container)
        root.addWidget(self._scroll, stretch=1)

        # -- Bottom toolbar --
        btm = QFrame()
        btm.setObjectName("proof_btm_bar")
        btm.setStyleSheet(
            "#proof_btm_bar { background:#e4e6ea;"
            " border-top:1px solid #c0c2c8; }")
        bl = QHBoxLayout(btm)
        bl.setContentsMargins(10, 4, 10, 4)
        bl.setSpacing(8)
        btn_sub = QPushButton("\u25b6 Subproof")
        btn_sub.setObjectName("btn_subproof")
        btn_sub.setFont(_FONT_SMALL)
        btn_sub.setStyleSheet(
            "#btn_subproof{background:" + _BG_LINE + ";border:1px solid #388c6b;"
            "border-radius:3px;padding:3px 10px;"
            "font-size:11px;color:#388c6b;}"
            "#btn_subproof:hover{background:#d8eed8;}")
        btn_sub.clicked.connect(self._open_subproof)
        btn_close = QPushButton("\u25c0 Close")
        btn_close.setObjectName("btn_close_sub")
        btn_close.setFont(_FONT_SMALL)
        btn_close.setStyleSheet(
            "#btn_close_sub{background:" + _BG_LINE + ";border:1px solid #c0c2c8;"
            "border-radius:3px;padding:3px 10px;font-size:11px;}"
            "#btn_close_sub:hover{background:#e0e2e8;}")
        btn_close.clicked.connect(self._close_subproof)
        bl.addWidget(btn_sub)
        bl.addWidget(btn_close)
        bl.addStretch()
        root.addWidget(btm)

        # -- Goals --
        goal_frame = QFrame()
        goal_frame.setObjectName("goal_frame")
        goal_frame.setStyleSheet(
            "#goal_frame { background:#e8e8ee;"
            " border-top:1px solid #c0c2c8; }"
            "#goal_frame QLabel { background:transparent; }")
        gl = QVBoxLayout(goal_frame)
        gl.setContentsMargins(10, 6, 10, 6)
        gh = QLabel("Goals")
        gh.setFont(QFont("Segoe UI", 10))
        gh.setStyleSheet("color:#5a5a72;")
        gh.setAlignment(Qt.AlignmentFlag.AlignCenter)
        gl.addWidget(gh)
        # Goal row with turnstile and status
        goal_row = QHBoxLayout()
        goal_row.setSpacing(8)
        # Turnstile image-like label
        turnstile = QLabel("\u22a2")
        turnstile.setFont(QFont("Segoe UI", 16))
        turnstile.setStyleSheet("color:#888; background:transparent;")
        turnstile.setFixedWidth(28)
        goal_row.addWidget(turnstile)
        self._goal_edit = QLineEdit("")
        self._goal_edit.setFont(_FONT)
        self._goal_edit.setFrame(False)
        self._goal_edit.setObjectName("goal_edit")
        self._goal_edit.setPlaceholderText("Enter goal formula...")
        self._goal_edit.setStyleSheet(
            "#goal_edit { background:transparent; color:" + _TEXT_DARK + ";"
            " padding:4px 6px; border:none; }"
            "#goal_edit:focus { background:" + _BG_WHITE + ";"
            " border:1px solid #5ca4e6; border-radius:2px; }")
        self._goal_edit.textChanged.connect(self._on_goal_changed)
        # Track focus for palette insertion
        orig_goal_fi = self._goal_edit.focusInEvent

        def _track_goal(event):
            self._focused_text_field = self._goal_edit
            orig_goal_fi(event)

        self._goal_edit.focusInEvent = _track_goal
        goal_row.addWidget(self._goal_edit, stretch=1)
        self._goal_status = QLabel("")
        self._goal_status.setFont(_FONT_BOLD)
        self._goal_status.setFixedWidth(22)
        self._goal_status.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._goal_status.setStyleSheet("color:#999; background:transparent;")
        goal_row.addWidget(self._goal_status)
        gl.addLayout(goal_row)
        root.addWidget(goal_frame)

        # -- Detail --
        self._detail = QLabel()
        self._detail.setWordWrap(True)
        self._detail.setFont(_FONT_SMALL)
        self._detail.setMinimumHeight(36)
        self._detail.setTextInteractionFlags(
            Qt.TextInteractionFlag.TextSelectableByMouse)
        self._detail.setStyleSheet(
            "padding:6px 12px; color:#5a5a72; font-size:11px;"
            " background:#e4e6ea; border-top:1px solid #c0c2c8;")
        root.addWidget(self._detail)

        QShortcut(QKeySequence("Ctrl+Z"), self, self._undo)
        QShortcut(QKeySequence("Ctrl+Y"), self, self._redo)
        QShortcut(QKeySequence("Ctrl+Shift+Z"), self, self._redo)
        QShortcut(QKeySequence("Ctrl+S"), self, self._save_proof)

    @staticmethod
    def _make_flow_row():
        r = QHBoxLayout()
        r.setSpacing(3)
        r.setContentsMargins(0, 0, 0, 0)
        return r

    # ===============================================================
    # SYNTAX TRANSLATION (System E → legacy display format)
    # ===============================================================

    @staticmethod
    def _to_verifier_syntax(expr: str) -> str:
        """Translate a System E formula string to legacy verifier syntax.

        Used by tests to confirm that the UI palette's E-syntax input
        can round-trip to the legacy predicate format.

        Handles comma-separated conjunctions: ``"ab = ac, ab = bc"``
        becomes ``"Equal(AB,AC) ∧ Equal(AB,BC)"``.
        """
        parts = ProofPanel._split_top_level(expr)
        if len(parts) > 1:
            translated = [ProofPanel._translate_one(p) for p in parts]
            return " ∧ ".join(translated)
        return ProofPanel._translate_one(expr)

    @staticmethod
    def _split_top_level(expr: str) -> list:
        """Split on commas that are NOT inside parentheses."""
        parts = []
        depth = 0
        current = []
        for ch in expr:
            if ch == '(':
                depth += 1
                current.append(ch)
            elif ch == ')':
                depth -= 1
                current.append(ch)
            elif ch == ',' and depth == 0:
                parts.append(''.join(current).strip())
                current = []
            else:
                current.append(ch)
        parts.append(''.join(current).strip())
        return [p for p in parts if p]

    @staticmethod
    def _translate_one(expr: str) -> str:
        """Translate a single System E literal to legacy syntax."""
        expr = expr.strip()

        # between(a, b, c) → Between(A,B,C)
        m = re.match(r'between\(\s*(\w)\s*,\s*(\w)\s*,\s*(\w)\s*\)', expr)
        if m:
            return "Between(%s,%s,%s)" % (
                m.group(1).upper(), m.group(2).upper(), m.group(3).upper())

        # on(a, L) → OnLine(A,l)
        m = re.match(r'on\(\s*(\w)\s*,\s*(\w)\s*\)', expr)
        if m:
            pt, ln = m.group(1), m.group(2)
            return "OnLine(%s,%s)" % (pt.upper(), ln.lower())

        # same-side(a, b, L) → SameSide(A,B,L)
        m = re.match(
            r'same-side\(\s*(\w)\s*,\s*(\w)\s*,\s*(\w)\s*\)', expr)
        if m:
            return "SameSide(%s,%s,%s)" % (
                m.group(1).upper(), m.group(2).upper(),
                m.group(3).upper())

        # ¬(a = b) → A != B
        m = re.match(r'[¬!]\(\s*(\w)\s*=\s*(\w)\s*\)', expr)
        if m:
            return "%s != %s" % (m.group(1).upper(), m.group(2).upper())

        # ∠bac = right-angle → RightAngle(B,A,C)
        m = re.match(r'[∠∡](\w)(\w)(\w)\s*=\s*right-angle', expr)
        if m:
            return "RightAngle(%s,%s,%s)" % (
                m.group(1).upper(), m.group(2).upper(),
                m.group(3).upper())

        # ∠abc = ∠def → EqualAngle(A,B,C,D,E,F)
        m = re.match(
            r'[∠∡](\w)(\w)(\w)\s*=\s*[∠∡](\w)(\w)(\w)', expr)
        if m:
            return "EqualAngle(%s,%s,%s,%s,%s,%s)" % tuple(
                g.upper() for g in m.groups())

        # △abc = △def → Congruent(A,B,C,D,E,F)
        m = re.match(r'[△▵](\w)(\w)(\w)\s*=\s*[△▵](\w)(\w)(\w)', expr)
        if m:
            return "Congruent(%s,%s,%s,%s,%s,%s)" % tuple(
                g.upper() for g in m.groups())

        # cd < ab → Greater(AB,CD)
        m = re.match(r'(\w)(\w)\s*<\s*(\w)(\w)', expr)
        if m:
            lesser = m.group(1).upper() + m.group(2).upper()
            greater = m.group(3).upper() + m.group(4).upper()
            return "Greater(%s,%s)" % (greater, lesser)

        # ab = cd → Equal(AB,CD)
        m = re.match(r'(\w)(\w)\s*=\s*(\w)(\w)', expr)
        if m:
            return "Equal(%s%s,%s%s)" % (
                m.group(1).upper(), m.group(2).upper(),
                m.group(3).upper(), m.group(4).upper())

        return expr

    # ===============================================================
    # PUBLIC API
    # ===============================================================

    def add_step(self, text, justification, refs, depth=None):
        self._push_undo()
        ln = len(self._premises) + len(self._steps) + 1
        d = depth if depth is not None else self._current_depth
        step = ProofStep(ln, text, justification, refs, d)
        self._steps.append(step)
        self._rebuild_lines()
        self.step_changed.emit()

    def insert_step_at(self, position, text="",
                       justification="", refs=None, depth=None):
        self._push_undo()
        d = depth if depth is not None else self._current_depth
        step = ProofStep(0, text, justification, refs or [], d)
        self._steps.insert(position, step)
        self._renumber()
        self._rebuild_lines()
        self.step_changed.emit()
        if 0 <= position < len(self._line_widgets):
            QTimer.singleShot(
                50, self._line_widgets[position].focus_text)

    def add_premise_text(self, text):
        if text and text not in self._premises:
            self._premises.append(text)
            self._renumber()
            self._refresh_premises()

    def set_proof_name(self, name):
        """Set the proof name (used in save/export and lemma references)."""
        self._proof_name = name or "workspace_proof"

    def set_conclusion(self, text):
        self._conclusion = text
        self._goal_edit.setText(text if text else "")
        self._goal_status.setText("")
        self._goal_status.setStyleSheet("color:#999; background:transparent;")

    def set_declarations(self, points, lines):
        self._decl_points = list(points)
        self._decl_lines = list(lines)
        self._points_input.setText(", ".join(points))
        self._lines_input.setText(", ".join(lines))

    def reset_evaluations(self):
        for s in self._steps:
            s.status = "?"
        for w in self._line_widgets:
            try:
                w.refresh_from_step()
            except RuntimeError:
                pass  # widget already deleted by C++
        self._update_counts()

    def clear(self):
        self._steps = []
        self._premises = []
        self._conclusion = ""
        self._proof_name = "workspace_proof"
        self._current_depth = 0
        self._decl_points = []
        self._decl_lines = []
        self._selected = -1
        self._selected_prem = -1
        self._goal_edit.setText("")
        self._goal_status.setText("")
        self._detail.setText("")
        self._undo_stack = []
        self._redo_stack = []
        self._count_label.setText("")
        self._points_input.clear()
        self._lines_input.clear()
        self._rebuild_lines()

    def get_steps(self):
        return [{"lineNumber": s.line_number, "text": s.text,
                 "justification": s.justification,
                 "dependencies": s.refs,
                 "depth": s.depth, "status": s.status}
                for s in self._steps]

    # ===============================================================
    # LINE REBUILD
    # ===============================================================

    def _rebuild_lines(self):
        self._line_widgets = []
        self._prem_widgets = []
        while self._lines_layout.count():
            item = self._lines_layout.takeAt(0)
            if item.widget():
                w = item.widget()
                w.setParent(None)
                w.deleteLater()

        # -- Premise lines (depth 0, with InsertBars, above the Fitch bar) --
        for i, prem_text in enumerate(self._premises):
            # InsertBar before each premise
            pbar = InsertBar(i, depth=0)
            pbar.insert_requested.connect(self._on_insert_premise_bar)
            self._lines_layout.addWidget(pbar)

            prem_line_num = i + 1
            prem_step = ProofStep(prem_line_num, prem_text, "Given", [], 0)
            prem_step.status = "\u2713"  # premises are always true
            pw = FitchLineWidget(prem_step)
            pw._rule_label.setVisible(False)
            pw._rule_btn.setVisible(False)
            pw._colon_label.setVisible(False)
            pw._refs_edit.setVisible(False)
            pw._status_label.setVisible(False)
            # Track text changes for premise editing
            idx = i

            def _make_prem_change(index):
                def _on_change(ln):
                    if index < len(self._premises):
                        self._premises[index] = self._prem_widgets[index].step.text
                return _on_change

            pw.text_changed.connect(_make_prem_change(idx))
            # Selection tracking for premises
            def _make_prem_select(index):
                def _on_sel(ln):
                    self._on_premise_selected(index)
                return _on_sel

            pw.selected.connect(_make_prem_select(idx))
            pw.set_selected(self._selected_prem == idx)
            # Connect delete for premise lines
            def _make_prem_delete(index):
                def _on_del(ln):
                    self._delete_premise(index)
                return _on_del

            pw.delete_requested.connect(_make_prem_delete(idx))
            # Track focus for palette insertion
            orig_fi = pw.text_field().focusInEvent

            def make_tracker(field, orig):
                def tracked(event):
                    self._focused_text_field = field
                    orig(event)
                return tracked

            pw.text_field().focusInEvent = make_tracker(
                pw.text_field(), orig_fi)
            self._prem_widgets.append(pw)
            self._lines_layout.addWidget(pw)

        # -- InsertBar at end of premises (to add new premise at the end) --
        pbar_end = InsertBar(len(self._premises), depth=0)
        pbar_end.insert_requested.connect(self._on_insert_premise_bar)
        self._lines_layout.addWidget(pbar_end)

        # -- Fitch bar --
        fbar = FitchBar()
        self._lines_layout.addWidget(fbar)

        # -- Proof lines --
        for i, step in enumerate(self._steps):
            # InsertBar inherits depth from the line below it
            bar = InsertBar(i, depth=step.depth)
            bar.insert_requested.connect(self._on_insert_bar)
            self._lines_layout.addWidget(bar)

            lw = FitchLineWidget(step)
            lw.text_changed.connect(self._on_line_text_changed)
            lw.rule_changed.connect(self._on_line_rule_changed)
            lw.refs_changed.connect(self._on_line_refs_changed)
            lw.selected.connect(self._on_line_selected)
            lw.delete_requested.connect(self._on_line_delete)
            lw.set_selected(step.line_number == self._selected)
            orig_fi = lw.text_field().focusInEvent

            def make_tracker(field, orig):
                def tracked(event):
                    self._focused_text_field = field
                    orig(event)
                return tracked

            lw.text_field().focusInEvent = make_tracker(
                lw.text_field(), orig_fi)
            self._line_widgets.append(lw)
            self._lines_layout.addWidget(lw)

        # Final insert bar: depth = last step's depth or 0
        last_depth = self._steps[-1].depth if self._steps else 0
        bar = InsertBar(len(self._steps), depth=last_depth)
        bar.insert_requested.connect(self._on_insert_bar)
        self._lines_layout.addWidget(bar)

        self._lines_layout.addStretch()

    # ===============================================================
    # PALETTE INSERT
    # ===============================================================

    def _insert_into_focused(self, text):
        field = self._focused_text_field
        # Try the tracked field first (survives button-click focus steal)
        if field is not None:
            try:
                if field is self._goal_edit:
                    cur = field.cursorPosition()
                    existing = field.text()
                    field.setText(existing[:cur] + text + existing[cur:])
                    paren_idx = text.find("(")
                    if paren_idx >= 0:
                        field.setCursorPosition(cur + paren_idx + 1)
                    else:
                        field.setCursorPosition(cur + len(text))
                    field.setFocus()
                    return
                # Must be a proof-line or premise text field
                for lw in self._line_widgets:
                    if lw.text_field() is field:
                        lw.insert_at_cursor(text)
                        return
                for pw in self._prem_widgets:
                    if pw.text_field() is field:
                        pw.insert_at_cursor(text)
                        return
            except RuntimeError:
                pass  # widget deleted
        # Fallback: insert into the selected proof line
        if self._selected > 0:
            for lw in self._line_widgets:
                if lw.step.line_number == self._selected:
                    lw.insert_at_cursor(text)
                    return

    # ===============================================================
    # LINE EVENTS
    # ===============================================================

    def _on_insert_bar(self, position):
        self.insert_step_at(position, "", "Given", [])

    def _on_add_line_bar(self):
        """Add a new empty line at the end of the proof."""
        self.insert_step_at(
            len(self._steps), "", "", [],
            depth=self._current_depth)

    def _on_add_premise_bar(self):
        """Add a new empty premise above the Fitch bar."""
        self._push_undo()
        self._premises.append("")
        self._selected_prem = len(self._premises) - 1
        self._selected = -1
        self._renumber()
        self._rebuild_lines()
        # Focus the new premise widget for immediate typing
        if self._prem_widgets:
            QTimer.singleShot(
                50, self._prem_widgets[-1].focus_text)

    def _on_insert_premise_bar(self, position):
        """Insert a new empty premise at the given position."""
        self._push_undo()
        self._premises.insert(position, "")
        self._selected_prem = position
        self._selected = -1
        self._renumber()
        self._rebuild_lines()
        if 0 <= position < len(self._prem_widgets):
            QTimer.singleShot(
                50, self._prem_widgets[position].focus_text)

    def _on_premise_selected(self, index):
        """Track which premise is selected (for delete, etc.)."""
        prem_line_num = index + 1
        # If a refs field is focused, append this premise's line number
        if self._append_ref_to_focused(prem_line_num):
            return
        self._selected_prem = index
        self._selected = -1  # deselect proof lines
        for lw in self._line_widgets:
            lw.set_selected(False)
        for j, pw in enumerate(self._prem_widgets):
            pw.set_selected(j == index)
        self._detail.setText(
            "Line " + str(prem_line_num)
            + "  |  " + (self._premises[index] if index < len(self._premises) else ""))

    def _on_line_text_changed(self, ln):
        self.step_changed.emit()

    def _on_goal_changed(self, text):
        self._conclusion = text

    def _on_line_delete(self, ln):
        """Delete a proof line by its line number (from per-line ✕ button)."""
        idx = None
        for i, s in enumerate(self._steps):
            if s.line_number == ln:
                idx = i
                break
        if idx is not None:
            self._push_undo()
            self._steps.pop(idx)
            self._renumber()
            self._selected = -1
            self._rebuild_lines()
            self.step_changed.emit()

    def _delete_premise(self, index):
        """Delete a premise by its index (from per-line ✕ button)."""
        if 0 <= index < len(self._premises):
            self._push_undo()
            self._premises.pop(index)
            self._selected_prem = -1
            self._renumber()
            self._rebuild_lines()
            self.step_changed.emit()

    def _on_line_rule_changed(self, ln):
        self.step_changed.emit()

    def _on_line_refs_changed(self, ln):
        self.step_changed.emit()

    def _append_ref_to_focused(self, line_num):
        """If a refs field is focused, append line_num to it."""
        for lw in self._line_widgets:
            if lw._refs_edit.hasFocus():
                cur = lw._refs_edit.text().strip()
                if cur:
                    lw._refs_edit.setText(cur + "," + str(line_num))
                else:
                    lw._refs_edit.setText(str(line_num))
                return True
        return False

    def _on_line_selected(self, ln):
        # If a refs field is focused, append this line number as a reference
        if self._append_ref_to_focused(ln):
            return
        self._selected = ln
        self._selected_prem = -1  # deselect premises
        for lw in self._line_widgets:
            lw.set_selected(lw.step.line_number == ln)
        for pw in self._prem_widgets:
            pw.set_selected(False)
        step = None
        for s in self._steps:
            if s.line_number == ln:
                step = s
                break
        if step:
            self._detail.setText(
                "Line " + str(step.line_number)
                + "  |  Depth " + str(step.depth)
                + "  |  " + step.justification
                + "  |  Refs: " + str(step.refs)
                + "  |  Status: " + step.status)

    # ===============================================================
    # UNDO / REDO
    # ===============================================================

    def _snapshot(self):
        return {
            "steps": [
                (s.line_number, s.text, s.justification,
                 list(s.refs), s.depth, s.status)
                for s in self._steps],
            "depth": self._current_depth,
        }

    def _push_undo(self):
        self._undo_stack.append(self._snapshot())
        if len(self._undo_stack) > UNDO_LIMIT:
            self._undo_stack.pop(0)
        self._redo_stack = []

    def _restore(self, snap):
        self._steps = []
        for ln, txt, just, refs, depth, status in snap["steps"]:
            s = ProofStep(ln, txt, just, refs, depth)
            s.status = status
            self._steps.append(s)
        self._current_depth = snap["depth"]
        self._rebuild_lines()
        self.step_changed.emit()

    def _undo(self):
        if not self._undo_stack:
            return
        self._redo_stack.append(self._snapshot())
        self._restore(self._undo_stack.pop())

    def _redo(self):
        if not self._redo_stack:
            return
        self._undo_stack.append(self._snapshot())
        self._restore(self._redo_stack.pop())

    # ===============================================================
    # HELPERS
    # ===============================================================

    def _renumber(self):
        offset = len(self._premises)
        for i, s in enumerate(self._steps):
            s.line_number = offset + i + 1

    def _add_premise(self):
        pass  # Premises are now added via add_premise_text() API

    def _refresh_premises(self):
        self._rebuild_lines()

    def _delete_selected(self):
        # Delete selected premise
        if self._selected_prem >= 0:
            if self._selected_prem < len(self._premises):
                self._push_undo()
                self._premises.pop(self._selected_prem)
                self._selected_prem = -1
                self._rebuild_lines()
                self.step_changed.emit()
            return
        # Delete selected proof line
        if self._selected <= 0:
            return
        idx = None
        for i, s in enumerate(self._steps):
            if s.line_number == self._selected:
                idx = i
                break
        if idx is not None:
            self._push_undo()
            self._steps.pop(idx)
            self._renumber()
            self._selected = -1
            self._rebuild_lines()
            self.step_changed.emit()

    def _open_subproof(self):
        self._current_depth += 1
        pos = len(self._steps)
        if self._selected > 0:
            for i, s in enumerate(self._steps):
                if s.line_number == self._selected:
                    pos = i + 1
                    break
        self.insert_step_at(
            pos, "", "Assume", [], self._current_depth)

    def _close_subproof(self):
        if self._current_depth > 0:
            self._current_depth -= 1

    # ===============================================================
    # EVAL
    # ===============================================================

    def _eval_selected(self):
        self._eval_all()

    def _eval_all(self):
        # If there are no proof steps yet, skip verification entirely
        # and show a neutral prompt instead of a confusing parse error.
        if not self._steps:
            self._detail.setText(
                "Add proof steps and click Eval to verify.")
            self._detail.setStyleSheet(
                "padding:6px 12px; color:#5a5a72;"
                " font-size:11px; background:#f5f6fa;"
                " border-top:1px solid #e0e0e8;")
            self._update_counts()
            return

        proof_json = self._build_proof_json()
        try:
            from verifier.unified_checker import verify_e_proof_json
            result = verify_e_proof_json(proof_json)
        except Exception as exc:
            err_msg = str(exc)
            if "Unexpected token" in err_msg or "parse" in err_msg.lower():
                self._detail.setText(
                    "Some formulas use syntax not yet supported by "
                    "the verifier.  Check premises and conclusion.")
            else:
                self._detail.setText("Verifier error: " + err_msg)
            self._detail.setStyleSheet(
                "padding:6px 12px; color:#cc8800;"
                " font-size:11px; background:#fffbf0;"
                " border-top:1px solid #e0e0e8;")
            return

        error_ids: set = set()
        for lid, lr in result.line_results.items():
            if not lr.valid:
                error_ids.add(lid)

        for s in self._steps:
            lid = s.line_number
            if lid in error_ids:
                s.status = "\u2717"
            elif lid in result.derived:
                s.status = "\u2713"
            else:
                s.status = "?"

        for lw in self._line_widgets:
            lw.refresh_from_step()

        if self._conclusion:
            # Validate goal formula syntax using System E parser
            goal_syntax_ok = False
            try:
                from verifier.unified_checker import parse_e_formula
                parsed = parse_e_formula(self._conclusion)
                goal_syntax_ok = parsed is not None and len(parsed) > 0
            except Exception:
                goal_syntax_ok = False

            if result.accepted:
                self._goal_status.setText("\u2713")
                self._goal_status.setStyleSheet(
                    "color:#2e8b57; font-weight:bold;"
                    " background:transparent;")
            elif not goal_syntax_ok:
                self._goal_status.setText("\u2717")
                self._goal_status.setStyleSheet(
                    "color:#cc3333; font-weight:bold;"
                    " background:transparent;")
                self._detail.setText(
                    "Goal formula is not valid syntax. "
                    "Use connectives: \u2227  \u2228  \u00ac(  \u2194  \u22a5  \u2260  \u2203  \u2203!  \u2200  "
                    "and System E predicates: on(a,L)  between(a,b,c)  "
                    "ab = cd  \u2220abc = \u2220def  etc.")
                self._detail.setStyleSheet(
                    "padding:6px 12px; color:#cc3333;"
                    " font-size:11px; background:#fff5f5;"
                    " border-top:1px solid #e0e0e8;")
            else:
                self._goal_status.setText("\u2717")
                self._goal_status.setStyleSheet(
                    "color:#cc3333; font-weight:bold;"
                    " background:transparent;")

        self._update_counts()

        if self._selected > 0:
            step = None
            for s in self._steps:
                if s.line_number == self._selected:
                    step = s
                    break
            if step:
                lr = result.line_results.get(step.line_number)
                msgs = lr.errors if lr and lr.errors else []
                if msgs:
                    self._detail.setText("\n".join(msgs))
                    self._detail.setStyleSheet(
                        "padding:6px 12px; color:#cc3333;"
                        " font-size:11px; background:#fff5f5;"
                        " border-top:1px solid #e0e0e8;")
                else:
                    self._detail.setText(
                        "Line " + str(step.line_number)
                        + ": " + step.status)
                    self._detail.setStyleSheet(
                        "padding:6px 12px; color:#5a5a72;"
                        " font-size:11px; background:#f5f6fa;"
                        " border-top:1px solid #e0e0e8;")
        elif result.errors:
            self._detail.setText(result.errors[0])
            self._detail.setStyleSheet(
                "padding:6px 12px; color:#cc3333;"
                " font-size:11px; background:#fff5f5;"
                " border-top:1px solid #e0e0e8;")
        else:
            if result.accepted:
                txt = "ACCEPTED \u2713"
                col = "#2e8b57"
            else:
                txt = "REJECTED \u2717"
                col = "#cc3333"
            self._detail.setText(txt)
            self._detail.setStyleSheet(
                "padding:6px 12px; color:" + col + ";"
                " font-size:11px; background:#f5faf5;"
                " border-top:1px solid #e0e0e8;")

    def _build_proof_json(self):
        pts_raw = self._points_input.text().strip()
        lns_raw = self._lines_input.text().strip()
        points = ([p.strip() for p in pts_raw.split(",")
                   if p.strip()] if pts_raw else [])
        lines_decl = ([el.strip() for el in lns_raw.split(",")
                       if el.strip()] if lns_raw else [])

        proof_lines = []
        # Premises become numbered Given lines (1, 2, ...)
        all_premise_stmts = []
        for i, p in enumerate(self._premises):
            all_premise_stmts.append(p)
            proof_lines.append({
                "id": i + 1, "depth": 0,
                "statement": p,
                "justification": "Given",
                "refs": [],
            })
        # Proof steps follow premises
        for s in self._steps:
            entry = {
                "id": s.line_number, "depth": s.depth,
                "statement": s.text,
                "justification": s.justification,
                "refs": s.refs,
            }
            proof_lines.append(entry)

        # Auto-declare symbols from premises
        points_set = set(points)
        lines_set = set(lines_decl)
        for stmt in all_premise_stmts:
            for sym in self._extract_symbols(stmt):
                if sym in points_set or sym in lines_set:
                    continue  # Already explicitly declared
                # System E convention: uppercase single letter = line,
                # everything else (lowercase, Greek, multi-char) = point.
                if len(sym) == 1 and sym.isupper():
                    lines_set.add(sym)
                else:
                    points_set.add(sym)
        points = list(points_set)
        lines_decl = list(lines_set)

        # Build lemma metadata for the verifier
        lemma_defs = []
        for lem in self._lemmas:
            lemma_defs.append({
                "name": lem.name,
                "premises": lem.premises,
                "goal": lem.goal,
            })

        out = {
            "name": self._proof_name,
            "declarations": {
                "points": points, "lines": lines_decl},
            "premises": all_premise_stmts,
            "goal": self._conclusion,
            "lines": proof_lines,
        }
        if lemma_defs:
            out["lemmas"] = lemma_defs
        return out

    @staticmethod
    def _extract_symbols(stmt: str) -> list:
        """Extract bare symbol names from a formula string.

        Uses a regex scan for identifiers that look like point or line
        names in System E syntax.
        """
        # Extract identifiers from predicate arguments (inside parens)
        syms = re.findall(r'(?<=[\(,])\s*([A-Za-z_]\w*)\s*(?=[,\)])', stmt)
        # Also extract standalone identifiers (for a ≠ b style)
        syms += re.findall(r'\b([A-Za-z])\b', stmt)
        return list(set(syms))

    def _update_counts(self):
        valid = sum(
            1 for s in self._steps if s.status == "\u2713")
        invalid = sum(
            1 for s in self._steps if s.status == "\u2717")
        pending = sum(
            1 for s in self._steps if s.status == "?")
        parts = []
        if valid:
            parts.append("\u2713" + str(valid))
        if invalid:
            parts.append("\u2717" + str(invalid))
        if pending:
            parts.append("?" + str(pending))
        self._count_label.setText("  ".join(parts))

    # ===============================================================
    # SAVE / LOAD
    # ===============================================================

    def _save_proof(self):
        proof_json = self._build_proof_json()
        path, _ = QFileDialog.getSaveFileName(
            self, "Save Proof JSON", "",
            "JSON Files (*.json);;All Files (*)")
        if path:
            try:
                with open(path, "w", encoding="utf-8") as f:
                    json.dump(proof_json, f, indent=2,
                              ensure_ascii=False)
            except Exception as exc:
                self._detail.setText("Save error: " + str(exc))

    # ===============================================================
    # LEMMA MANAGEMENT
    # ===============================================================

    def _load_lemma(self):
        """Load a verified proof JSON as a reusable lemma."""
        path, _ = QFileDialog.getOpenFileName(
            self, "Load Proof as Lemma", "",
            "JSON Files (*.json);;All Files (*)")
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception as exc:
            self._detail.setText("Lemma load error: " + str(exc))
            return
        name = data.get("name", "unnamed")
        goal = data.get("goal", "")
        premises = data.get("premises", [])
        if not goal:
            self._detail.setText("Lemma has no goal — cannot use as a rule.")
            return
        # Verify the proof first
        try:
            from verifier.unified_checker import verify_e_proof_json
            result = verify_e_proof_json(data)
        except Exception as exc:
            self._detail.setText("Lemma verification error: " + str(exc))
            return
        if not result.accepted:
            msgs = result.errors[:3] if result.errors else []
            self._detail.setText(
                "Lemma rejected — proof is not valid.\n"
                + "\n".join(msgs))
            self._detail.setStyleSheet(
                "padding:6px 12px; color:#cc3333;"
                " font-size:11px; background:#fff5f5;"
                " border-top:1px solid #e0e0e8;")
            return
        # Check for duplicates
        for existing in self._lemmas:
            if existing.name == name:
                self._detail.setText(
                    "Lemma '" + name + "' already loaded.")
                return
        lemma = LoadedLemma(name, premises, goal, path)
        self._lemmas.append(lemma)
        self._rebuild_lemma_ui()
        self._detail.setText(
            "Lemma '" + name + "' loaded \u2713  Goal: " + goal)
        self._detail.setStyleSheet(
            "padding:6px 12px; color:#2e8b57;"
            " font-size:11px; background:#f0faf0;"
            " border-top:1px solid #e0e0e8;")

    def _remove_lemma(self, index):
        """Remove a loaded lemma by index."""
        if 0 <= index < len(self._lemmas):
            removed = self._lemmas.pop(index)
            self._unregister_lemma_rule(removed)
            self._rebuild_lemma_ui()
            self._detail.setText(
                "Lemma '" + removed.name + "' removed.")

    def _rebuild_lemma_ui(self):
        """Rebuild the lemma list display."""
        while self._lemma_list_container.count():
            item = self._lemma_list_container.takeAt(0)
            if item.widget():
                item.widget().deleteLater()
        if not self._lemmas:
            empty = QLabel("No lemmas loaded. Click Lemma to add one.")
            empty.setFont(QFont("Segoe UI", 9))
            empty.setStyleSheet("color:#aaa; font-style:italic;")
            self._lemma_list_container.addWidget(empty)
            return
        for i, lem in enumerate(self._lemmas):
            row = QFrame()
            row.setStyleSheet(
                "QFrame { background:#f7f8fa;"
                " border:1px solid #dcdee3; border-radius:3px;"
                " padding:2px 4px; }")
            rl = QHBoxLayout(row)
            rl.setContentsMargins(4, 2, 4, 2)
            rl.setSpacing(6)
            name_lbl = QLabel(lem.display_name())
            name_lbl.setFont(QFont("Segoe UI", 10, QFont.Weight.Bold))
            name_lbl.setStyleSheet("color:#1a1a2e;")
            rl.addWidget(name_lbl)
            schema_lbl = QLabel(lem.schema_text())
            schema_lbl.setFont(QFont("Segoe UI", 9))
            schema_lbl.setStyleSheet("color:#5a5a72;")
            schema_lbl.setWordWrap(True)
            rl.addWidget(schema_lbl, stretch=1)
            rm_btn = QPushButton("\u2715")
            rm_btn.setFixedSize(18, 18)
            rm_btn.setFont(QFont("Segoe UI", 9))
            rm_btn.setStyleSheet(
                "QPushButton { background:transparent; color:#bbb;"
                " border:none; font-size:11px; }"
                "QPushButton:hover { color:#d32f2f; }")
            rm_btn.setToolTip("Remove lemma")
            idx = i
            rm_btn.clicked.connect(
                lambda checked, index=idx: self._remove_lemma(index))
            rl.addWidget(rm_btn)
            self._lemma_list_container.addWidget(row)

    def _register_lemma_rules(self):
        """Register all loaded lemmas (no-op, lemmas are resolved at eval time)."""
        pass

    def _unregister_lemma_rules(self):
        """Remove all lemma rules (no-op)."""
        pass

    @staticmethod
    def _unregister_lemma_rule(lem):
        """Remove a single lemma rule (no-op)."""
        pass

    def _load_proof(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Open Proof JSON", "",
            "JSON Files (*.json);;All Files (*)")
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception as exc:
            self._detail.setText("Load error: " + str(exc))
            return
        self._push_undo()
        self._steps = []
        self._premises = []
        self._conclusion = ""
        self._current_depth = 0
        self._proof_name = data.get("name", "workspace_proof")
        decl = data.get("declarations", {})
        self.set_declarations(
            decl.get("points", []), decl.get("lines", []))
        for p in data.get("premises", []):
            self._premises.append(p)
        self._refresh_premises()
        self.set_conclusion(data.get("goal", ""))
        num_premises = len(self._premises)
        for ld in data.get("lines", []):
            # Skip premise lines (they're already loaded from "premises")
            if ld.get("id", 0) <= num_premises and ld.get("justification") == "Given":
                continue
            s = ProofStep(
                line_number=ld["id"],
                text=ld.get("statement", ""),
                justification=ld.get("justification", ""),
                refs=ld.get("refs", []),
                depth=ld.get("depth", 0),
            )
            self._steps.append(s)
        self._rebuild_lines()
        self.step_changed.emit()
