"""Proof Panel -- PyQt6 Fitch-style proof journal.

Direct-style proof display for System E (no subproofs needed):
  - Each proof line is an inline-editable widget row
  - Rule dropdown on each line opens a popup picker (System E rules)
  - Refs box next to the rule on each line
  - Insert bar between lines to add new steps
  - Predicate palette aligned to System E syntax (§3.3-§3.7)
  - Declarations row (Points / Lines)
  - Premises section with formal predicates
  - Goals / conclusion with turnstile
  - Eval Step / Eval All wired to verifier via unified_checker
  - Undo / redo (30 levels)

Phase 9.1 of the implementation plan.
"""
from __future__ import annotations

import json
import logging
import os
import re
import traceback
from collections import OrderedDict
from typing import Dict, List, Optional

from PyQt6.QtCore import Qt, pyqtSignal, QSize, QTimer, QThread, QObject
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
# CRASH LOGGER — writes to euclid_crash.log for post-mortem debugging
# ===================================================================

_LOG_FILENAME = "euclid_crash.log"

def _get_crash_logger() -> logging.Logger:
    """Return (and lazily configure) the proof-panel crash logger.

    Writes timestamped entries to ``euclid_crash.log`` in the workspace
    root directory so the user can attach the file when reporting bugs.
    """
    logger = logging.getLogger("euclid.proof_panel")
    if not logger.handlers:
        logger.setLevel(logging.DEBUG)
        try:
            # Place the log next to the running script / workspace root
            log_dir = os.path.dirname(os.path.abspath(__file__))
            # Walk up from euclid_py/ui/ to the workspace root
            log_dir = os.path.normpath(os.path.join(log_dir, "..", ".."))
            log_path = os.path.join(log_dir, _LOG_FILENAME)
            fh = logging.FileHandler(log_path, encoding="utf-8")
            fh.setLevel(logging.DEBUG)
            fmt = logging.Formatter(
                "%(asctime)s [%(levelname)s] %(message)s",
                datefmt="%Y-%m-%d %H:%M:%S",
            )
            fh.setFormatter(fmt)
            logger.addHandler(fh)
        except Exception:
            # If we can't write a log file, at least log to stderr
            sh = logging.StreamHandler()
            sh.setLevel(logging.WARNING)
            logger.addHandler(sh)
    return logger


# ===================================================================
# RULE CATALOGUE — System E axioms grouped by paper section
# ===================================================================

def _build_rule_groups():
    """Build rule groups from System E axioms via unified_checker.

    Filters out sub-axioms that proof authors never directly cite,
    keeping the rule dropdown manageable.
    """
    from verifier.unified_checker import get_available_rules
    rules = get_available_rules()

    # Rules hidden from the dropdown — individual diagrammatic sub-axioms,
    # rarely-used metric rules, and transfer axiom variants that are
    # subsumed by more common ones.
    _HIDDEN_PREFIXES = (
        "Betweenness 2", "Betweenness 3", "Betweenness 4",
        "Betweenness 5", "Betweenness 7",
        "Same-side ", "Pasch ", "Triple incidence ",
        "Circle 2", "Circle 3", "Circle 4",
        "Intersection 1", "Intersection 2a", "Intersection 2b",
        "Intersection 2d", "Intersection 3", "Intersection 4",
        "Generality 2", "Generality 4", "Generality 5", "Generality 6",
    )
    _HIDDEN_EXACT = {
        "M2 — Non-negative", "M5 — Angle bounds",
        "M6 — Degenerate area", "M7 — Non-negative area",
        "M9 — Congruence → area", "CN2 — Addition",
        "Order transitivity", "Addition preserves order",
        "Segment transfer 2",
        "Angle transfer 1a", "Angle transfer 1b", "Angle transfer 1c",
        "Angle transfer 2b", "Angle transfer 2c",
        "Angle transfer 3b", "Angle transfer 5a", "Angle transfer 5b",
        "Area transfer 1b", "Area transfer 1c",
    }

    def _visible(name):
        if name in _HIDDEN_EXACT:
            return False
        for prefix in _HIDDEN_PREFIXES:
            if name.startswith(prefix):
                return False
        return True

    _CAT_LABELS = OrderedDict([
        ("construction", "Construction"),
        ("diagrammatic", "Diagrammatic"),
        ("metric", "Metric"),
        ("transfer", "Transfer"),
        ("superposition", "Superposition"),
        ("structural", "Structural"),
        ("proposition", "Propositions"),
    ])
    groups = OrderedDict()
    for cat, label in _CAT_LABELS.items():
        names = [r.name for r in rules
                 if r.category == cat and _visible(r.name)]
        if names:
            groups[label] = names
    return groups


RULE_GROUPS = _build_rule_groups()

ALL_RULE_NAMES = []
for _rules in RULE_GROUPS.values():
    ALL_RULE_NAMES.extend(_rules)


# ===================================================================
# PREDICATE PALETTE
# ===================================================================

CONNECTIVES = ["\u2227", "\u00ac",
               "=", "\u2260", "<",
               "(", ")",
               "\u25b3", "\u221f", "\u2220"]
CONNECTIVE_MAP = {
    "\u2227": " \u2227 ", "\u00ac": "\u00ac",
    "=": " = ", "\u2260": " \u2260 ",
    "<": " < ",
    "(": "(", ")": ")",
    "\u25b3": "\u25b3",
    "\u221f": "right-angle",
    "\u2220": "\u2220",
}

PREDICATES = [
    # Incidence (§3.4)
    ("on(a,L)", "on(,)"), ("on(a,α)", "on(,)"),
    ("center(a,α)", "center(,)"),
    ("inside(a,α)", "inside(,)"),
    # Betweenness & collinearity (§3.4)
    ("between(a,b,c)", "between(,,)"),
    ("same-side(a,b,L)", "same-side(,,)"),
    # Constructions (§3.3)
    ("let-line", "on(,), on(,)"),
    ("let-circle", "center(,), on(,)"),
    ("intersects(L,α)", "intersects(,)"),
    # Equality / inequality
    ("a≠b", "¬( = )"), ("a=b", " = "),
    # Metric predicates (§3.5)
    ("ab=cd", " = "), ("ab<cd", " < "),
    ("∠abc=∠def", "∠ = ∠"),
    ("∠abc<∠def", "∠ < ∠"),
    # Special
    ("¬intersects", "¬intersects(,)"),
    ("∟", "∟"),
    ("△", "△"),
]

# Greek letters for circle naming in System E
GREEK_LETTERS = ["α", "β", "γ", "δ"]


# ===================================================================
# BACKGROUND VERIFICATION WORKER
# ===================================================================

class _CancelledError(Exception):
    """Raised inside the verifier callback when cancellation is requested."""
    pass


class _VerifyWorker(QObject):
    """Runs verify_e_proof_json on a background thread to avoid UI freeze."""
    finished = pyqtSignal(object)  # emits PanelCheckResult or Exception
    line_checked = pyqtSignal(int, bool, list)  # (line_id, valid, errors)

    def __init__(self, proof_json: dict):
        super().__init__()
        self._proof_json = proof_json
        self._cancelled = False

    def cancel(self):
        """Request cancellation — checked between verification steps."""
        self._cancelled = True

    def _on_line_checked(self, line_id: int, valid: bool, errors: list):
        if self._cancelled:
            raise _CancelledError()
        self.line_checked.emit(line_id, valid, errors)
        # Give the main thread time to process the queued signal and
        # repaint the UI before we continue verifying the next line.
        # Without this, all signals pile up and get painted in one batch.
        import time
        time.sleep(0.03)

    def run(self):
        try:
            from verifier.unified_checker import verify_e_proof_json
            result = verify_e_proof_json(
                self._proof_json,
                on_line_checked=self._on_line_checked)
            if not self._cancelled:
                self.finished.emit(result)
        except _CancelledError:
            pass  # silently abort
        except Exception as exc:
            log = _get_crash_logger()
            log.error(
                "Verifier thread exception:\n%s",
                traceback.format_exc(),
            )
            if not self._cancelled:
                self.finished.emit(exc)


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
        self._text_edit.installEventFilter(self)
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
        self._rule_btn = QPushButton("\u25be")
        self._rule_btn.setFont(_FONT_SMALL)
        self._rule_btn.setFixedSize(22, 22)
        self._rule_btn.setObjectName("rule_drop_btn")
        self._rule_btn.setStyleSheet(
            "#rule_drop_btn{background:#e8ede8;border:1px solid #c8d0c8;"
            "border-radius:3px;color:" + _TEXT_GREEN + ";font-size:12px;"
            "padding:0px;}"
            "#rule_drop_btn:hover{background:#d0e0d0;"
            "border-color:#388c6b;}")
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

    def eventFilter(self, obj, event):
        """Intercept clicks on the text field: if the line isn't selected
        yet, select it first instead of entering edit mode."""
        if obj is self._text_edit and event.type() == event.Type.MouseButtonPress:
            if not self._is_selected:
                self.selected.emit(self.step.line_number)
                return True  # consume the click
        return super().eventFilter(obj, event)

    def mousePressEvent(self, event):
        if self._is_selected:
            self._text_edit.setFocus()
        else:
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
        self.setFixedHeight(40)
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
        self._verified = False     # True once bg verification passes
        self._verifying = False    # True while bg verification running
        self._verifier_data = None # temp: data being verified
        self._thread = None        # bg thread ref (prevent GC)
        self._worker = None        # bg worker ref (prevent GC)

    def display_name(self):
        if self._verifying:
            return "\u23f3 " + self.name
        if self._verified:
            return "\u2713 " + self.name
        return "\u2717 " + self.name

    def schema_text(self):
        if self._verifying:
            status = "  (verifying\u2026)"
        elif self._verified:
            status = ""
        else:
            status = "  (INVALID)"
        base = (", ".join(self.premises) + "  \u2192  " + self.goal
                if self.premises
                else "\u2014  \u2192  " + self.goal)
        return base + status


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
        self._undo_stack = []
        self._redo_stack = []
        self._decl_points = []
        self._decl_lines = []
        self._line_widgets = []
        self._prem_widgets = []
        self._focused_text_field = None
        self._lemmas: List[LoadedLemma] = []
        self._verify_thread: Optional[QThread] = None
        self._verify_worker: Optional[_VerifyWorker] = None
        self._eval_buttons: List[QPushButton] = []
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
        self._count_label = QLabel("")
        self._count_label.setFont(_FONT_SMALL)
        self._count_label.setStyleSheet(
            "color:#5a5a72;font-size:11px;padding:0 4px;")
        row1.addWidget(self._count_label)
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
            self._eval_buttons.append(b)
        hvbox.addLayout(row1)

        # Row 2: undo/redo, begin/end subproof, lemma (single row)
        row2 = QHBoxLayout()
        row2.setSpacing(3)
        _btn_style = (
            "QPushButton{background:transparent;color:#5a5a72;"
            "border:1px solid #c0c2c8;border-radius:3px;"
            "padding:2px 6px;font-size:10px;}"
            "QPushButton:hover{background:#e0e2e8;"
            "border-color:#888;}")
        for text_label, tip, cb in [
            ("Undo", "Undo (Ctrl+Z)", self._undo),
            ("Redo", "Redo (Ctrl+Y)", self._redo),
            ("Begin Subproof",
             "Open a subproof: inserts an Assume line at depth+1",
             self._begin_subproof),
            ("End Subproof",
             "Close a subproof: inserts a Reductio line at depth\u22121, "
             "referencing the Assume line",
             self._end_subproof),
        ]:
            b = QPushButton(text_label)
            b.setFont(QFont("Segoe UI", 9))
            b.setToolTip(tip)
            b.setFixedHeight(22)
            b.setStyleSheet(_btn_style)
            b.clicked.connect(cb)
            row2.addWidget(b)
        row2.addStretch()
        b = QPushButton("Lemma")
        b.setFont(QFont("Segoe UI", 9))
        b.setToolTip("Load a verified proof as a lemma")
        b.setFixedHeight(22)
        b.setStyleSheet(_btn_style)
        b.clicked.connect(self._load_lemma)
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
            b.setStyleSheet(
                "padding:0px 3px;font-size:11px;min-width:0px;")
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
            b.setStyleSheet(
                "padding:0px 3px;font-size:11px;min-width:0px;")
            b.clicked.connect(
                lambda _, t=letter: self._insert_into_focused(t))
            row = 1 + col // cols_per_row
            sym_grid.addWidget(b, row, col % cols_per_row)
            col += 1
        pl.addLayout(sym_grid)
        root.addWidget(palette)

        # -- Predicate glossary (System E, always visible) --
        self._glossary_frame = QFrame()
        self._glossary_frame.setObjectName("glossary_frame")
        self._glossary_frame.setStyleSheet(
            "#glossary_frame { background:#eef0f5;"
            " border-bottom:1px solid #c0c2c8; }"
            "#glossary_frame QLabel { background:transparent; }"
            "#glossary_frame QPushButton { background:#f7f8fa; color:#1a1a2e;"
            " border:1px solid #c0c2c8; border-radius:3px;"
            " padding:0px 3px; font-size:10px; min-width:0px; }"
            "#glossary_frame QPushButton:hover { background:#dce0e8;"
            " border-color:#888; }")
        glossary_vbox = QVBoxLayout(self._glossary_frame)
        glossary_vbox.setContentsMargins(8, 4, 8, 4)
        glossary_vbox.setSpacing(0)

        # ── Flow layout helper ──
        from PyQt6.QtWidgets import QLayout as _QLayout
        from PyQt6.QtCore import QRect as _QRect, QSize as _QSize

        class _FlowLayout(_QLayout):
            """Flow layout that wraps widgets to the next row."""
            def __init__(self, parent=None, h_spacing=4, v_spacing=4):
                super().__init__(parent)
                self._items = []
                self._h_sp = h_spacing
                self._v_sp = v_spacing

            def addItem(self, item):
                self._items.append(item)

            def count(self):
                return len(self._items)

            def itemAt(self, index):
                if 0 <= index < len(self._items):
                    return self._items[index]
                return None

            def takeAt(self, index):
                if 0 <= index < len(self._items):
                    return self._items.pop(index)
                return None

            def hasHeightForWidth(self):
                return True

            def heightForWidth(self, width):
                return self._do_layout(_QRect(0, 0, width, 0), True)

            def setGeometry(self, rect):
                super().setGeometry(rect)
                self._do_layout(rect, False)

            def sizeHint(self):
                return self.minimumSize()

            def minimumSize(self):
                s = _QSize(0, 0)
                for item in self._items:
                    s = s.expandedTo(item.minimumSize())
                return s

            def _do_layout(self, rect, test):
                x = rect.x()
                y = rect.y()
                row_h = 0
                for item in self._items:
                    w = item.sizeHint().width()
                    h = item.sizeHint().height()
                    if x + w > rect.right() and row_h > 0:
                        x = rect.x()
                        y += row_h + self._v_sp
                        row_h = 0
                    if not test:
                        item.setGeometry(_QRect(x, y, w, h))
                    x += w + self._h_sp
                    row_h = max(row_h, h)
                return y + row_h - rect.y()

        # ── System E predicate buttons ──
        _e_buttons = [
            ("on(a,L)",              "on(,)"),
            ("on(a,\u03b1)",         "on(,)"),
            ("center(a,\u03b1)",     "center(,)"),
            ("inside(a,\u03b1)",     "inside(,)"),
            ("between(a,b,c)",       "between(,,)"),
            ("same-side(a,b,L)",     "same-side(,,)"),
            ("diff-side(a,b,L)",     "diff-side(,,)"),
            ("intersects(L,\u03b1)", "intersects(,)"),
            ("\u00acintersects(L,\u03b1)", "\u00acintersects(,)"),
            ("let-line",             "on(,), on(,)"),
            ("let-circle",           "center(,), on(,)"),
        ]
        _e_flow = _FlowLayout(None, h_spacing=4, v_spacing=4)
        for label, tmpl in _e_buttons:
            b = QPushButton(label)
            b.setToolTip(tmpl)
            b.setFont(_FONT_SMALL)
            b.setFixedHeight(20)
            b.clicked.connect(
                lambda _, t=tmpl: self._insert_into_focused(t))
            _e_flow.addWidget(b)
        _e_body = QWidget()
        _e_body.setLayout(_e_flow)
        glossary_vbox.addWidget(_e_body)

        root.addWidget(self._glossary_frame)

        # -- Lemma section (collapsible, matching glossary style) --
        self._lemma_frame = QFrame()
        self._lemma_frame.setObjectName("lemma_frame")
        self._lemma_frame.setStyleSheet(
            "#lemma_frame { background:#eef0f5;"
            " border-bottom:1px solid #c0c2c8; }"
            "#lemma_frame QLabel { background:transparent; }")
        lemma_outer = QVBoxLayout(self._lemma_frame)
        lemma_outer.setContentsMargins(8, 4, 8, 4)
        lemma_outer.setSpacing(0)

        # Clickable header row
        lemma_hdr = QFrame()
        lemma_hdr.setCursor(
            __import__("PyQt6.QtGui", fromlist=["QCursor"]).QCursor(
                Qt.CursorShape.PointingHandCursor))
        lemma_hdr.setStyleSheet("background:transparent;")
        lhdr_row = QHBoxLayout(lemma_hdr)
        lhdr_row.setContentsMargins(0, 2, 0, 2)
        lhdr_row.setSpacing(4)
        self._lemma_arrow = QLabel("\u25b8")
        self._lemma_arrow.setFont(QFont("Segoe UI", 10))
        self._lemma_arrow.setStyleSheet("color:#5a5a72;")
        self._lemma_arrow.setFixedWidth(14)
        lhdr_row.addWidget(self._lemma_arrow)
        lemma_title = QLabel("Lemmas")
        lemma_title.setFont(QFont("Segoe UI", 10))
        lemma_title.setStyleSheet("color:#5a5a72;")
        lhdr_row.addWidget(lemma_title)
        lhdr_row.addStretch()
        lemma_outer.addWidget(lemma_hdr)

        # Collapsible body (starts hidden)
        self._lemma_body = QWidget()
        self._lemma_body.setVisible(False)
        self._lemma_layout = QVBoxLayout(self._lemma_body)
        self._lemma_layout.setContentsMargins(0, 4, 0, 2)
        self._lemma_layout.setSpacing(2)
        self._lemma_list_container = QVBoxLayout()
        self._lemma_list_container.setSpacing(2)
        self._lemma_layout.addLayout(self._lemma_list_container)
        self._lemma_empty_label = QLabel(
            "No lemmas loaded. Click Lemma to add one.")
        self._lemma_empty_label.setFont(QFont("Segoe UI", 9))
        self._lemma_empty_label.setStyleSheet(
            "color:#aaa; font-style:italic;")
        self._lemma_list_container.addWidget(self._lemma_empty_label)
        lemma_outer.addWidget(self._lemma_body)

        def _toggle_lemmas(event=None):
            vis = not self._lemma_body.isVisible()
            self._lemma_body.setVisible(vis)
            self._lemma_arrow.setText("\u25be" if vis else "\u25b8")

        lemma_hdr.mousePressEvent = _toggle_lemmas
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

        # -- Goal (single compact row: label ⊢ input status) --
        goal_frame = QFrame()
        goal_frame.setObjectName("goal_frame")
        goal_frame.setStyleSheet(
            "#goal_frame { background:#e8e8ee;"
            " border-top:1px solid #c0c2c8; }"
            "#goal_frame QLabel { background:transparent; }")
        goal_row = QHBoxLayout(goal_frame)
        goal_row.setContentsMargins(8, 4, 8, 4)
        goal_row.setSpacing(4)
        goal_lbl = QLabel("\u22a2")
        goal_lbl.setFont(QFont("Segoe UI", 14))
        goal_lbl.setStyleSheet("color:#5a5a72;")
        goal_lbl.setFixedWidth(22)
        goal_lbl.setToolTip("Goal / conclusion")
        goal_row.addWidget(goal_lbl)
        self._goal_edit = QLineEdit("")
        self._goal_edit.setFont(_FONT)
        self._goal_edit.setFrame(False)
        self._goal_edit.setObjectName("goal_edit")
        self._goal_edit.setPlaceholderText("Goal formula...")
        self._goal_edit.setStyleSheet(
            "#goal_edit { background:transparent; color:" + _TEXT_DARK + ";"
            " padding:2px 4px; border:none; }"
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
        root.addWidget(goal_frame)

        QShortcut(QKeySequence("Ctrl+Z"), self, self._undo)
        QShortcut(QKeySequence("Ctrl+Y"), self, self._redo)
        QShortcut(QKeySequence("Ctrl+Shift+Z"), self, self._redo)

    @staticmethod
    def _make_flow_row():
        r = QHBoxLayout()
        r.setSpacing(3)
        r.setContentsMargins(0, 0, 0, 0)
        return r

    # ===============================================================
    # PUBLIC API
    # ===============================================================

    def add_step(self, text, justification, refs, depth=None):
        self._push_undo()
        ln = len(self._premises) + len(self._steps) + 1
        d = depth if depth is not None else 0
        step = ProofStep(ln, text, justification, refs, d)
        self._steps.append(step)
        self._rebuild_lines()
        self.step_changed.emit()

    def insert_step_at(self, position, text="",
                       justification="", refs=None, depth=None):
        self._push_undo()
        d = depth if depth is not None else 0
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
        self._cancel_verification()
        self._steps = []
        self._premises = []
        self._conclusion = ""
        self._proof_name = "workspace_proof"
        self._decl_points = []
        self._decl_lines = []
        self._selected = -1
        self._selected_prem = -1
        self._goal_edit.setText("")
        self._goal_status.setText("")
        self._undo_stack = []
        self._redo_stack = []
        self._count_label.setText("")
        self._points_input.clear()
        self._lines_input.clear()
        self._rebuild_lines()

    def _cancel_verification(self):
        """Cancel any in-flight background verification.

        Disconnects signals so the stale result is not applied after a
        system switch or other state change, then tears down the thread.
        """
        if self._verify_thread is not None:
            # Disconnect so _on_verify_finished is NOT called with stale data
            try:
                self._verify_worker.finished.disconnect(self._on_verify_finished)
            except (TypeError, RuntimeError):
                pass
            self._verify_thread.quit()
            if not self._verify_thread.wait(3000):
                # Thread didn't stop in time — force-terminate to avoid
                # "QThread: Destroyed while thread is still running" crash.
                self._verify_thread.terminate()
                self._verify_thread.wait(1000)
            self._verify_thread.deleteLater()
            self._verify_thread = None
            self._verify_worker = None
        # Re-enable eval buttons in case they were disabled
        for btn in self._eval_buttons:
            try:
                btn.setEnabled(True)
            except RuntimeError:
                pass

    def get_steps(self):
        return [{"lineNumber": s.line_number, "text": s.text,
                 "justification": s.justification,
                 "dependencies": s.refs,
                 "depth": s.depth, "status": s.status}
                for s in self._steps]

    def get_journal_state(self) -> dict:
        """Return the full proof journal state for file serialization."""
        state = {
            "name": self._proof_name,
            "premises": list(self._premises),
            "goal": self._conclusion,
            "declarations": {
                "points": list(self._decl_points),
                "lines": list(self._decl_lines),
            },
            "steps": self.get_steps(),
        }
        if self._lemmas:
            state["lemmas"] = [
                {"name": lem.name, "file_path": lem.file_path,
                 "premises": lem.premises, "goal": lem.goal,
                 "verified": lem._verified}
                for lem in self._lemmas
            ]
        return state

    def restore_journal_state(self, state: dict):
        """Restore the full proof journal from a deserialized state dict."""
        self._proof_name = state.get("name", "workspace_proof")
        self._premises = list(state.get("premises", []))
        self._conclusion = state.get("goal", "")
        decl = state.get("declarations", {})
        self.set_declarations(
            decl.get("points", []), decl.get("lines", []))
        self._goal_edit.setText(self._conclusion)
        self._steps = []
        for step in state.get("steps", []):
            s = ProofStep(
                line_number=step.get("lineNumber", 0),
                text=step.get("text", ""),
                justification=step.get("justification", ""),
                refs=step.get("dependencies", []),
                depth=step.get("depth", 0),
            )
            s.status = step.get("status", "?")
            self._steps.append(s)
        self._rebuild_lines()
        self._update_counts()
        # Restore lemmas if saved
        for lem_data in state.get("lemmas", []):
            name = lem_data.get("name", "unnamed")
            # Skip duplicates
            if any(l.name == name for l in self._lemmas):
                continue
            lemma = LoadedLemma(
                name,
                lem_data.get("premises", []),
                lem_data.get("goal", ""),
                lem_data.get("file_path", ""),
            )
            lemma._verified = lem_data.get("verified", False)
            lemma._verifying = False
            self._lemmas.append(lemma)
            # Re-verify if the lemma file still exists
            if not lemma._verified and lemma.file_path and os.path.exists(lemma.file_path):
                try:
                    with open(lemma.file_path, "r", encoding="utf-8") as f:
                        data = json.load(f)
                    if "proof" in data and "steps" in data.get("proof", {}):
                        lemma._verifier_data = self._euclid_to_verifier(data)
                    else:
                        lemma._verifier_data = data
                    lemma._verifying = True
                    self._verify_lemma_bg(lemma)
                except Exception:
                    pass
        if state.get("lemmas"):
            self._rebuild_lemma_ui()

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
            depth=0)

    def _begin_subproof(self):
        """Open a subproof by inserting an Assume line at depth+1.

        If a line is selected, the Assume is inserted after it and
        inherits its depth + 1.  Otherwise it is appended at the end.
        """
        self._push_undo()
        # Determine insertion point and depth
        if self._selected > 0:
            idx = None
            for i, s in enumerate(self._steps):
                if s.line_number == self._selected:
                    idx = i
                    break
            if idx is not None:
                current_depth = self._steps[idx].depth
                pos = idx + 1
            else:
                current_depth = self._steps[-1].depth if self._steps else 0
                pos = len(self._steps)
        else:
            current_depth = self._steps[-1].depth if self._steps else 0
            pos = len(self._steps)

        new_depth = current_depth + 1
        step = ProofStep(0, "", "Assume", [], new_depth)
        self._steps.insert(pos, step)
        self._renumber()
        self._rebuild_lines()
        self.step_changed.emit()
        # Focus the new Assume line for typing
        if 0 <= pos < len(self._line_widgets):
            QTimer.singleShot(
                50, self._line_widgets[pos].focus_text)

    def _end_subproof(self):
        """Close a subproof by inserting a Reductio line at depth\u22121.

        Finds the nearest Assume line above the current position and
        inserts a Reductio line referencing it.
        """
        self._push_undo()
        # Find the most recent Assume line (searching backward)
        assume_idx = None
        assume_line_num = None
        assume_depth = 0
        search_from = len(self._steps) - 1
        if self._selected > 0:
            for i, s in enumerate(self._steps):
                if s.line_number == self._selected:
                    search_from = i
                    break
        for i in range(search_from, -1, -1):
            if self._steps[i].justification == "Assume":
                assume_idx = i
                assume_line_num = self._steps[i].line_number
                assume_depth = self._steps[i].depth
                break

        if assume_idx is None:
            return  # no Assume to close

        # Insert Reductio at depth - 1, after the selected line (or end)
        outer_depth = max(0, assume_depth - 1)
        pos = search_from + 1 if self._selected > 0 else len(self._steps)
        step = ProofStep(0, "", "Reductio", [assume_line_num], outer_depth)
        self._steps.insert(pos, step)
        self._renumber()
        self._rebuild_lines()
        self.step_changed.emit()
        # Focus the new Reductio line for typing the conclusion
        if 0 <= pos < len(self._line_widgets):
            QTimer.singleShot(
                50, self._line_widgets[pos].focus_text)

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

    # ===============================================================
    # UNDO / REDO
    # ===============================================================

    def _snapshot(self):
        return {
            "steps": [
                (s.line_number, s.text, s.justification,
                 list(s.refs), s.depth, s.status)
                for s in self._steps],
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

    # ===============================================================
    # EVAL
    # ===============================================================

    def _eval_selected(self):
        """Evaluate only the currently selected step.

        Builds a truncated proof containing premises + steps up to and
        including the selected line so the verifier processes only the
        minimum context required.
        """
        if self._selected < 0 or not self._steps:
            return
        # Find the selected step object
        sel_step = None
        for s in self._steps:
            if s.line_number == self._selected:
                sel_step = s
                break
        if sel_step is None:
            return

        # Ignore if a verification is already running
        if self._verify_thread is not None:
            return

        # Auto-fill the selected step if empty
        if sel_step.text.strip() == "" and sel_step.justification.strip() != "":
            try:
                filled = self._generate_autofill(sel_step)
            except Exception:
                filled = self._AUTOFILL_FAIL
            if filled is self._AUTOFILL_FAIL:
                sel_step.status = "\u2717"
                sel_step._autofill_error = "Incorrect justification"
                for lw in self._line_widgets:
                    if lw.step.line_number == sel_step.line_number:
                        lw.refresh_from_step()
                        lw.setToolTip(sel_step._autofill_error)
                return
            elif filled:
                sel_step.text = filled
                for lw in self._line_widgets:
                    if lw.step.line_number == sel_step.line_number:
                        lw.refresh_from_step()

        # Build truncated proof JSON (premises + steps up to selected)
        proof_json = self._build_proof_json_up_to(sel_step.line_number)
        self._eval_target_lid = sel_step.line_number

        try:
            app = QApplication.instance()
            if app is None or not app.property("_euclid_event_loop_running"):
                from verifier.unified_checker import verify_e_proof_json
                result = verify_e_proof_json(proof_json)
                self._on_verify_selected_finished(result)
                return

            for btn in self._eval_buttons:
                btn.setEnabled(False)

            self._verify_thread = QThread()
            self._verify_worker = _VerifyWorker(proof_json)
            self._verify_worker.moveToThread(self._verify_thread)
            self._verify_thread.started.connect(self._verify_worker.run)
            self._verify_worker.line_checked.connect(
                self._on_line_checked_progressive,
                Qt.ConnectionType.QueuedConnection)
            self._verify_worker.finished.connect(
                self._on_verify_selected_finished)
            self._verify_worker.finished.connect(self._verify_thread.quit)
            self._verify_thread.start()
        except Exception as exc:
            log = _get_crash_logger()
            log.error("Unhandled exception in _eval_selected:\n%s",
                      traceback.format_exc())

    def _on_verify_selected_finished(self, result_or_exc):
        """Handle verification result for single-step eval."""
        # Clean up thread
        if self._verify_thread is not None:
            self._verify_thread.quit()
            self._verify_thread.wait(2000)
            self._verify_thread.deleteLater()
        self._verify_thread = None
        self._verify_worker = None

        for btn in self._eval_buttons:
            try:
                btn.setEnabled(True)
            except RuntimeError:
                pass

        lid = getattr(self, '_eval_target_lid', None)
        if lid is None:
            return

        if isinstance(result_or_exc, Exception):
            # Mark selected step with warning
            for s in self._steps:
                if s.line_number == lid:
                    s.status = "\u2717"
                    break
            for lw in self._line_widgets:
                if lw.step.line_number == lid:
                    lw.refresh_from_step()
                    lw.setToolTip(f"Verifier error: {result_or_exc}")
            return

        result = result_or_exc

        # Apply result only to the selected step
        lr = result.line_results.get(lid)
        for s in self._steps:
            if s.line_number == lid:
                if lr and not lr.valid:
                    s.status = "\u2717"
                elif lid in result.derived:
                    s.status = "\u2713"
                else:
                    s.status = "?"
                break

        for lw in self._line_widgets:
            if lw.step.line_number == lid:
                try:
                    lw.refresh_from_step()
                    if lr and lr.errors:
                        lw.setToolTip(lr.errors[0])
                    elif lw.step.status == "\u2713":
                        lw.setToolTip("Verified")
                    else:
                        lw.setToolTip("")
                except RuntimeError:
                    pass

    def _build_proof_json_up_to(self, target_lid):
        """Build proof JSON with only premises + steps up to target_lid."""
        pts_raw = self._points_input.text().strip()
        lns_raw = self._lines_input.text().strip()
        points = ([p.strip() for p in pts_raw.split(",")
                   if p.strip()] if pts_raw else [])
        lines_decl = ([el.strip() for el in lns_raw.split(",")
                       if el.strip()] if lns_raw else [])

        proof_lines = []
        all_premise_stmts = []
        for i, p in enumerate(self._premises):
            all_premise_stmts.append(p)
            proof_lines.append({
                "id": i + 1, "depth": 0,
                "statement": p,
                "justification": "Given",
                "refs": [],
            })
        for s in self._steps:
            proof_lines.append({
                "id": s.line_number, "depth": s.depth,
                "statement": s.text,
                "justification": s.justification,
                "refs": s.refs,
            })
            if s.line_number == target_lid:
                break  # stop after the selected step

        points_set = set(points)
        lines_set = set(lines_decl)
        for stmt in all_premise_stmts:
            for sym in self._extract_symbols(stmt):
                if sym in points_set or sym in lines_set:
                    continue
                if len(sym) == 1 and sym.isupper():
                    lines_set.add(sym)
                else:
                    points_set.add(sym)

        lemma_defs = []
        for lem in self._lemmas:
            if lem._verified:
                lemma_defs.append({
                    "name": lem.name,
                    "premises": lem.premises,
                    "goal": lem.goal,
                })

        out = {
            "name": self._proof_name,
            "declarations": {
                "points": list(points_set),
                "lines": list(lines_set)},
            "premises": all_premise_stmts,
            "goal": "",
            "lines": proof_lines,
        }
        if lemma_defs:
            out["lemmas"] = lemma_defs
        return out

    def _eval_all(self):
        if not self._steps:
            self._goal_status.setText("")
            self._goal_status.setToolTip(
                "Add proof steps and click Eval to verify.")
            self._update_counts()
            return

        # Ignore if a verification is already running
        if self._verify_thread is not None:
            return

        try:
            self._eval_all_inner()
        except Exception as exc:
            log = _get_crash_logger()
            log.error(
                "Unhandled exception in _eval_all:\n%s",
                traceback.format_exc(),
            )
            self._goal_status.setText("\u26a0")
            self._goal_status.setStyleSheet(
                "color:#cc8800; font-weight:bold;"
                " background:transparent;")
            self._goal_status.setToolTip(
                f"Internal error: {type(exc).__name__}: {exc}\n"
                f"See {_LOG_FILENAME} for details.")

    def _eval_all_inner(self):

        # ── Auto-fill: populate empty sentences before verification ──
        autofill_changed = False
        autofill_failed = False
        for step in self._steps:
            if step.text.strip() == "" and step.justification.strip() != "":
                try:
                    filled = self._generate_autofill(step)
                except Exception as exc:
                    log = _get_crash_logger()
                    log.warning(
                        "Autofill exception for step %d "
                        "(just=%r, refs=%r):\n%s",
                        step.line_number, step.justification,
                        step.refs, traceback.format_exc(),
                    )
                    filled = self._AUTOFILL_FAIL
                if filled is self._AUTOFILL_FAIL:
                    # Known rule/theorem but matching failed
                    step.status = "\u2717"
                    step._autofill_error = "Incorrect justification"
                    autofill_failed = True
                elif filled:
                    step.text = filled
                    autofill_changed = True
        if autofill_changed or autofill_failed:
            for lw in self._line_widgets:
                lw.refresh_from_step()
                if lw.step.status == "\u2717" and hasattr(lw.step, '_autofill_error'):
                    lw.setToolTip(lw.step._autofill_error)

        proof_json = self._build_proof_json()

        # When no event loop is running (e.g. tests), fall back to
        # synchronous verification to avoid hanging.
        app = QApplication.instance()
        if app is None or not app.property("_euclid_event_loop_running"):
            try:
                from verifier.unified_checker import verify_e_proof_json
                result = verify_e_proof_json(proof_json)
            except Exception as exc:
                err_msg = str(exc)
                self._goal_status.setText("\u26a0")
                self._goal_status.setStyleSheet(
                    "color:#cc8800; font-weight:bold;"
                    " background:transparent;")
                self._goal_status.setToolTip("Verifier error: " + err_msg)
                return
            self._on_verify_finished(result)
            return

        # Disable eval buttons and show a busy indicator
        for btn in self._eval_buttons:
            btn.setEnabled(False)
        self._goal_status.setText("\u23f3")
        self._goal_status.setStyleSheet(
            "color:#888; font-weight:bold; background:transparent;")
        self._goal_status.setToolTip("Verifying\u2026")

        # Set all non-autofill-failed steps to pending (?)
        for s in self._steps:
            if s.status != "\u2717":  # preserve autofill failures
                s.status = "?"
        for lw in self._line_widgets:
            try:
                lw.refresh_from_step()
            except RuntimeError:
                pass

        # Run verification on a background thread
        self._verify_thread = QThread()
        self._verify_worker = _VerifyWorker(proof_json)
        self._verify_worker.moveToThread(self._verify_thread)
        self._verify_thread.started.connect(self._verify_worker.run)
        self._verify_worker.line_checked.connect(
            self._on_line_checked_progressive,
            Qt.ConnectionType.QueuedConnection)
        self._verify_worker.finished.connect(self._on_verify_finished)
        self._verify_worker.finished.connect(self._verify_thread.quit)
        self._verify_thread.start()

    def _on_line_checked_progressive(self, line_id: int, valid: bool,
                                      errors: list):
        """Update a single step widget as verification progresses."""
        status = "\u2713" if valid else "\u2717"
        for s in self._steps:
            if s.line_number == line_id:
                s.status = status
                break
        for lw in self._line_widgets:
            try:
                if lw.step.line_number == line_id:
                    lw.refresh_from_step()
                    break
            except RuntimeError:
                pass

    def _on_verify_finished(self, result_or_exc):
        """Handle verification result delivered from the background thread."""
        try:
            self._on_verify_finished_inner(result_or_exc)
        except Exception as exc:
            log = _get_crash_logger()
            log.error(
                "Unhandled exception in _on_verify_finished:\n%s",
                traceback.format_exc(),
            )
            try:
                self._goal_status.setText("\u26a0")
                self._goal_status.setStyleSheet(
                    "color:#cc8800; font-weight:bold;"
                    " background:transparent;")
                self._goal_status.setToolTip(
                    f"Internal error: {type(exc).__name__}: {exc}\n"
                    f"See {_LOG_FILENAME} for details.")
            except RuntimeError:
                pass  # widget deleted

    def _on_verify_finished_inner(self, result_or_exc):
        """Inner implementation — unwrapped for crash logging."""
        # Clean up thread references — wait for the thread to fully exit
        # before destroying it to avoid "QThread: Destroyed while still
        # running" crashes.
        if self._verify_thread is not None:
            self._verify_thread.quit()
            self._verify_thread.wait(2000)
            self._verify_thread.deleteLater()
        self._verify_thread = None
        self._verify_worker = None

        # Re-enable eval buttons
        for btn in self._eval_buttons:
            try:
                btn.setEnabled(True)
            except RuntimeError:
                pass  # widget already deleted by C++

        # Handle verifier exception
        if isinstance(result_or_exc, Exception):
            err_msg = str(result_or_exc)
            self._goal_status.setText("\u26a0")
            self._goal_status.setStyleSheet(
                "color:#cc8800; font-weight:bold;"
                " background:transparent;")
            self._goal_status.setToolTip("Verifier error: " + err_msg)
            return

        result = result_or_exc

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
            try:
                lw.refresh_from_step()
            except RuntimeError:
                pass  # widget already deleted by C++

        if self._conclusion:
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
                self._goal_status.setToolTip("ACCEPTED")
            elif not goal_syntax_ok:
                self._goal_status.setText("\u2717")
                self._goal_status.setStyleSheet(
                    "color:#cc3333; font-weight:bold;"
                    " background:transparent;")
                self._goal_status.setToolTip(
                    "Goal formula is not valid syntax.")
            else:
                self._goal_status.setText("\u2717")
                self._goal_status.setStyleSheet(
                    "color:#cc3333; font-weight:bold;"
                    " background:transparent;")
                if result.errors:
                    self._goal_status.setToolTip(result.errors[0])
                else:
                    self._goal_status.setToolTip("REJECTED")
        else:
            if result.accepted:
                self._goal_status.setText("\u2713")
                self._goal_status.setStyleSheet(
                    "color:#2e8b57; font-weight:bold;"
                    " background:transparent;")
                self._goal_status.setToolTip("ACCEPTED")
            elif result.errors:
                self._goal_status.setText("\u2717")
                self._goal_status.setStyleSheet(
                    "color:#cc3333; font-weight:bold;"
                    " background:transparent;")
                self._goal_status.setToolTip(result.errors[0])

        self._update_counts()

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

        # Build lemma metadata for the verifier (only verified lemmas)
        lemma_defs = []
        for lem in self._lemmas:
            if lem._verified:
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
        # Extract identifiers from predicate arguments (inside parens).
        # Include Greek letters (U+0370–U+03FF) and other Unicode letters
        # so that circle names like α, β are detected.
        syms = re.findall(
            r'(?<=[\(,])\s*([A-Za-z\u0370-\u03ff_]\w*)\s*(?=[,\)])', stmt)
        # Also extract standalone identifiers (for a ≠ b style)
        syms += re.findall(r'(?<![A-Za-z\u0370-\u03ff_])'
                           r'([A-Za-z\u0370-\u03ff])'
                           r'(?![A-Za-z\u0370-\u03ff\w])', stmt)
        return list(set(syms))

    # ===============================================================
    # AUTO-FILL ENGINE
    # ===============================================================

    # Sentinel returned when autofill detects the justification or refs
    # are incorrect and the step should be marked ✗ immediately.
    _AUTOFILL_FAIL = object()

    def _generate_autofill(self, step):
        """Generate sentence text for a step from its justification and refs.

        Called when the user has filled in a justification (and optionally
        refs) but left the sentence empty, then pressed Eval.  Returns:
          - A non-empty string on success (the generated formula text).
          - ``None`` if auto-fill is not applicable (e.g. empty or
            unrecognised justification like ``Diagrammatic``).
          - ``_AUTOFILL_FAIL`` if the justification names a known rule
            or theorem but the prerequisite / hypothesis matching failed
            (wrong refs, missing refs, etc.).

        Prerequisite matching mirrors the verifier: all known facts from
        premises and prior accepted steps are available for matching,
        with ref'd literals prioritised for variable-binding order.
        """
        just = step.justification.strip()
        if not just:
            return None

        # Collect parsed literals from all referenced lines (prioritised)
        ref_lits = self._parse_ref_literals(step.refs)

        # Collect ALL known literals from premises + prior steps so that
        # prerequisite matching mirrors the verifier (which checks against
        # the full known-fact set, not just cited refs).
        all_known = self._collect_known_literals(step.line_number)

        # ── Construction rules ────────────────────────────────────
        try:
            from verifier.e_construction import CONSTRUCTION_RULE_BY_NAME
            rule = CONSTRUCTION_RULE_BY_NAME.get(just)
            if rule is not None:
                result = self._autofill_construction(
                    step, rule, ref_lits, all_known)
                # None from a known construction rule means matching failed
                return result if result is not None else self._AUTOFILL_FAIL
        except ImportError:
            pass

        # ── Theorem application (Prop.I.x) ────────────────────────
        if just.startswith("Prop.") or just.startswith("prop."):
            result = self._autofill_theorem(
                step, just, ref_lits, all_known)
            # None from a recognised theorem name means matching failed
            return result if result is not None else self._AUTOFILL_FAIL

        # ── Metric inference ──────────────────────────────────────
        if just in ("Metric", "metric"):
            result = self._autofill_metric(step, ref_lits, all_known)
            return result if result is not None else self._AUTOFILL_FAIL

        # ── Superposition (SAS / SSS) ────────────────────────────
        if just in ("SAS", "SSS", "SAS Superposition",
                     "SSS Superposition", "SAS-elim", "SSS-elim"):
            result = self._autofill_superposition(
                step, just, ref_lits, all_known)
            return result if result is not None else self._AUTOFILL_FAIL

        # ── Diagrammatic / Transfer / Metric named axioms ─────────
        # Justifications like "Generality 3", "Intersection 3",
        # "Segment transfer 1", etc.
        result = self._autofill_named_axiom(
            step, just, ref_lits, all_known)
        if result is not None:
            return result

        return None

    def _collect_known_literals(self, before_line):
        """Parse all premises and prior step texts into a flat literal list.

        Returns literals from every line whose line_number < *before_line*,
        mirroring the verifier's known-fact accumulation.  Ref'd literals
        are NOT deduplicated here — callers merge them as needed.
        """
        try:
            from verifier.e_parser import parse_literal_list, EParseError
        except ImportError:
            return []
        lits = []
        for prem in self._premises:
            try:
                lits.extend(parse_literal_list(prem))
            except EParseError:
                pass
        for s in self._steps:
            if s.line_number >= before_line:
                break
            if s.text.strip():
                try:
                    lits.extend(parse_literal_list(s.text))
                except EParseError:
                    pass
        return lits

    def _parse_ref_literals(self, refs):
        """Parse all referenced lines into a flat list of AST Literals."""
        try:
            from verifier.e_parser import parse_literal_list, EParseError
        except ImportError:
            return []
        lits = []
        for ref in refs:
            text = self._get_line_text(ref)
            if not text:
                continue
            try:
                parsed = parse_literal_list(text)
                lits.extend(parsed)
            except EParseError:
                pass
        return lits

    def _autofill_construction(self, step, rule, ref_lits, all_known):
        """Auto-fill a construction step by matching prerequisite patterns
        against known facts to derive a var_map, then substituting into
        the conclusion pattern.

        Ref'd literals are tried first (user intent), then remaining
        known facts are used as a fallback pool — mirroring the verifier
        which checks prerequisites against ALL known facts.

        Returns the generated text, or None if matching failed.
        """
        from verifier.e_ast import substitute_literal, literal_vars

        if not rule.conclusion_pattern:
            return None

        # Build candidate pool: ref'd literals first (priority), then
        # the remaining known facts (deduped) so binding order reflects
        # the user's cited refs.
        ref_set = set(id(l) for l in ref_lits)
        extra = [l for l in all_known if id(l) not in ref_set]
        candidate_pool = list(ref_lits) + extra

        # Match candidate pool against the rule's prereq pattern
        bindings, matched = self._match_hypotheses(
            rule.prereq_pattern, candidate_pool)

        # All prerequisite patterns must match for a valid autofill
        if matched < len(rule.prereq_pattern):
            return None

        # For new_vars (the constructed objects), pick fresh names
        # if not already bound from prereqs
        used_names = set(bindings.values())
        # Also include all names already in the proof so we don't
        # reuse e.g. α when it was already introduced by a prior step.
        for prem in self._premises:
            used_names.update(self._extract_symbols(prem))
        for s in self._steps:
            if s.text.strip():
                used_names.update(self._extract_symbols(s.text))
        for name, sort in rule.new_vars:
            if name not in bindings:
                fresh = self._pick_fresh_name(name, sort, used_names)
                bindings[name] = fresh
                used_names.add(fresh)

        # Generate conclusion text
        parts = []
        for lit in rule.conclusion_pattern:
            inst = substitute_literal(lit, bindings)
            parts.append(repr(inst))
        return ", ".join(parts)

    def _autofill_theorem(self, step, theorem_name, ref_lits, all_known):
        """Auto-fill a theorem application step by matching known facts
        against the theorem's hypotheses to derive a var_map, then
        substituting into the conclusions.

        Ref'd literals are tried first, with remaining known facts as
        fallback — mirroring the verifier.

        Returns the generated text, or None if matching failed.
        """
        try:
            from verifier.e_library import E_THEOREM_LIBRARY
            from verifier.e_ast import substitute_literal
        except ImportError:
            return None

        thm = E_THEOREM_LIBRARY.get(theorem_name)
        if thm is None:
            return None

        # Build candidate pool: ref'd literals first, then known facts
        ref_set = set(id(l) for l in ref_lits)
        extra = [l for l in all_known if id(l) not in ref_set]
        candidate_pool = list(ref_lits) + extra

        # Match candidate pool against the theorem's hypotheses
        bindings, matched = self._match_hypotheses(
            thm.sequent.hypotheses, candidate_pool)

        # All hypothesis patterns must match for a valid autofill
        if matched < len(thm.sequent.hypotheses):
            return None

        # For existential vars, pick fresh names that don't collide
        used_names = set(bindings.values())
        # Also include all names already in the proof
        for prem in self._premises:
            used_names.update(self._extract_symbols(prem))
        for s in self._steps:
            if s.text.strip():
                used_names.update(self._extract_symbols(s.text))

        for name, sort in thm.sequent.exists_vars:
            if name not in bindings:
                fresh = self._pick_fresh_name(name, sort, used_names)
                bindings[name] = fresh
                used_names.add(fresh)

        # Generate substituted conclusion text
        parts = []
        for conc in thm.sequent.conclusions:
            inst = substitute_literal(conc, bindings)
            parts.append(repr(inst))
        return ", ".join(parts)

    # ── Named axiom index (lazy-initialised) ─────────────────────
    _AXIOM_BY_NAME: Optional[dict] = None

    @classmethod
    def _get_axiom_by_name(cls) -> dict:
        """Build or return the cached name→Clause index for all named
        diagrammatic, transfer and metric axioms.

        Keys are the rule names shown in the UI dropdown, e.g.
        ``"Generality 3"``, ``"Segment transfer 3b"``.

        Paper-label suffixes are used for groups whose axioms have
        sub-labels (e.g. B1a-d, C2a-d).  Legacy sequential names
        (e.g. ``"Betweenness 4"`` for B1d) are kept as aliases so that
        older saved proofs still resolve.
        """
        if cls._AXIOM_BY_NAME is not None:
            return cls._AXIOM_BY_NAME
        try:
            from verifier.e_axioms import (
                GENERALITY_AXIOMS, BETWEEN_AXIOMS, SAME_SIDE_AXIOMS,
                PASCH_AXIOMS, TRIPLE_INCIDENCE_AXIOMS, CIRCLE_AXIOMS,
                INTERSECTION_AXIOMS,
                DIAGRAM_SEGMENT_TRANSFER, DIAGRAM_ANGLE_TRANSFER,
                DIAGRAM_AREA_TRANSFER,
            )
        except ImportError:
            cls._AXIOM_BY_NAME = {}
            return cls._AXIOM_BY_NAME

        # Paper-label suffixes for non-sequential axiom groups.
        # Groups that ARE sequential use None (label == str(i+1)).
        _BETWEEN_LABELS = ["1a", "1b", "1c", "1d", "2", "3", "4", "5", "6", "7"]
        _CIRCLE_LABELS  = ["1", "2a", "2b", "2c", "2d", "3a", "3b", "3c", "3d", "4"]
        _INTER_LABELS   = ["1", "2a", "2b", "2c", "2d", "3", "4a", "4b", "5"]
        _SEG_LABELS     = ["1", "2", "3a", "3b", "4a", "4b", "4c", "4d"]
        _ANG_LABELS     = ["1a", "1b", "1c", "2a", "2b", "2c", "3a", "3b", "4", "5a", "5b"]
        _AREA_LABELS    = ["1a", "1b", "1c", "2"]

        groups = [
            ("Generality", GENERALITY_AXIOMS, None),
            ("Betweenness", BETWEEN_AXIOMS, _BETWEEN_LABELS),
            ("Same-side", SAME_SIDE_AXIOMS, None),
            ("Pasch", PASCH_AXIOMS, None),
            ("Triple incidence", TRIPLE_INCIDENCE_AXIOMS, None),
            ("Circle", CIRCLE_AXIOMS, _CIRCLE_LABELS),
            ("Intersection", INTERSECTION_AXIOMS, _INTER_LABELS),
            ("Segment transfer", DIAGRAM_SEGMENT_TRANSFER, _SEG_LABELS),
            ("Angle transfer", DIAGRAM_ANGLE_TRANSFER, _ANG_LABELS),
            ("Area transfer", DIAGRAM_AREA_TRANSFER, _AREA_LABELS),
        ]
        idx: dict = {}
        for group_name, axioms, labels in groups:
            for i, ax in enumerate(axioms):
                label = labels[i] if labels else str(i + 1)
                canonical = f"{group_name} {label}"
                idx[canonical] = ax
                # Legacy alias: if the paper label differs from the
                # sequential index, also register "Group N" so that
                # older proofs still resolve.
                seq_name = f"{group_name} {i + 1}"
                if seq_name != canonical and seq_name not in idx:
                    idx[seq_name] = ax
        cls._AXIOM_BY_NAME = idx
        return idx

    def _autofill_named_axiom(self, step, just, ref_lits, all_known):
        """Auto-fill a step justified by a named axiom clause.

        Named axioms are clauses ``{¬P₁, ¬P₂, …, Q}`` where the negated
        literals are prerequisites and the remaining positive literals are
        the conclusion.  We match known facts against the prerequisites
        (with polarity flipped) to derive bindings, then substitute into
        the conclusion.

        Ref'd literals are tried first, with remaining known facts as
        fallback — mirroring the verifier.

        Returns the generated text, ``_AUTOFILL_FAIL`` if the justification
        names a known axiom but matching failed, or ``None`` if the
        justification is not a known named axiom.
        """
        from verifier.unified_checker import _try_match_literal
        from verifier.e_ast import substitute_literal, Literal

        ax_index = self._get_axiom_by_name()
        clause = ax_index.get(just)
        if clause is None:
            return None  # not a known named axiom

        # Split clause into prereqs (negated) and conclusions (positive).
        # In the clause representation, prerequisites appear as negative
        # literals (their negation must be true in the known facts).
        prereqs = []
        conclusions = []
        for lit in clause.literals:
            if not lit.polarity:
                # Negative literal in clause → prerequisite
                # The positive version is what we match against known facts
                prereqs.append(Literal(lit.atom, polarity=True))
            else:
                conclusions.append(lit)

        if not conclusions:
            return self._AUTOFILL_FAIL

        # For disjunctive clauses with multiple positive literals,
        # we cannot determine which conclusion the user intends.
        # Skip autofill and let the user type the statement manually.
        if len(conclusions) > 1:
            return None

        # Clause.literals is a frozenset, so iteration order is
        # non-deterministic.  Sort prereqs so that ``On`` patterns bind
        # primary variables (point + object) before ``Inside`` patterns,
        # which prevents circle-name swaps in axioms like Intersection 9
        # where on(a,α) and inside(b,α) share schema variable α.
        from verifier.e_ast import On, Inside
        _ATOM_PRIORITY = {On: 0, Inside: 1}
        prereqs.sort(key=lambda l: (
            _ATOM_PRIORITY.get(type(l.atom), 2), repr(l)))

        # Build candidate pool: ref'd literals first, then known facts
        ref_set = set(id(l) for l in ref_lits)
        extra = [l for l in all_known if id(l) not in ref_set]
        candidate_pool = list(ref_lits) + extra

        # Match candidate pool against prereqs to derive bindings
        bindings: dict = {}
        remaining = list(candidate_pool)
        matched = 0
        for pat in prereqs:
            for i, conc in enumerate(remaining):
                result = _try_match_literal(pat, conc, bindings)
                if result is not None:
                    bindings = result
                    remaining.pop(i)
                    matched += 1
                    break

        if matched < len(prereqs):
            return self._AUTOFILL_FAIL

        # Substitute bindings into conclusions
        parts = []
        for conc in conclusions:
            inst = substitute_literal(conc, bindings)
            parts.append(repr(inst))
        return ", ".join(parts)

    def _autofill_metric(self, step, ref_lits, all_known):
        """Auto-fill a step justified by ``Metric``.

        Uses a sequential pattern-matching strategy, trying the most
        specific patterns first:

        1. **Multi-ref transitivity** – when ≥ 2 ref lines are cited,
           derive the cross-ref equality connecting terms from
           different references (CN1).
        2. **Angle M4-both-sides rewrite** – for single-ref steps
           containing angle equalities, apply M4 to both sides
           simultaneously to produce a novel textual variant.
        3. **Pure swap** – for single-ref equalities, produce
           ``Y = X`` from ``X = Y``.  Skipped when the same canonical
           equality already appears in a non-ref prior step.
        4. **M1 disequality** – derive ``¬(p = q)`` from segment
           nonzero.
        5. **Angle consequences (M9)** – derive angle equalities from
           segment equalities, preferring angles whose vertex is
           the shared endpoint of the referenced segment terms.

        Returns the generated text, ``_AUTOFILL_FAIL`` if no new metric
        facts can be derived, or ``None`` if the engine is unavailable.
        """
        try:
            from verifier.e_metric import MetricEngine
            from verifier.e_ast import (
                Literal, Equals, LessThan, SegmentTerm, AngleTerm,
                AreaTerm, literal_vars, Term,
            )
            from verifier.e_parser import parse_literal_list, EParseError
        except ImportError:
            return None

        from itertools import permutations

        known_set = set(all_known)

        # Exact-text set of every already-stated literal.
        known_texts = set()
        for lit in all_known:
            known_texts.add(repr(lit))
        for prem in self._premises:
            known_texts.add(prem.strip())
        for s in self._steps:
            if s.line_number < step.line_number and s.text.strip():
                known_texts.add(s.text.strip())

        # Canonical-form helpers for semantic redundancy detection.
        def _term_canon(t):
            if isinstance(t, SegmentTerm):
                return ("seg", frozenset([t.p1, t.p2]))
            if isinstance(t, AngleTerm):
                return ("ang", t.p2, frozenset([t.p1, t.p3]))
            if isinstance(t, AreaTerm):
                return ("area", frozenset([t.p1, t.p2, t.p3]))
            return ("pt", t) if isinstance(t, str) else ("o", repr(t))

        def _eq_canon(atom):
            return frozenset(
                [_term_canon(atom.left), _term_canon(atom.right)])

        known_eq_canons = set()
        known_diseq_canons = set()
        for lit in all_known:
            if isinstance(lit.atom, Equals):
                c = _eq_canon(lit.atom)
                if lit.polarity:
                    known_eq_canons.add(c)
                else:
                    known_diseq_canons.add(c)

        # Canonical eq forms from non-ref prior steps (not premises
        # or Given steps).  Detects when a swap would be redundant
        # because the equality was already independently stated in
        # the proof.  "Given" steps restate premises and must be
        # excluded just like premises themselves.
        non_ref_eq_canons = set()
        ref_set = set(step.refs)
        for s in self._steps:
            if (s.line_number < step.line_number
                    and s.line_number not in ref_set
                    and s.text.strip()
                    and s.justification.strip() != "Given"):
                try:
                    for lit in parse_literal_list(s.text):
                        if (isinstance(lit.atom, Equals) and lit.polarity
                                and isinstance(lit.atom.left,
                                               (SegmentTerm, AngleTerm,
                                                AreaTerm))):
                            non_ref_eq_canons.add(_eq_canon(lit.atom))
                except (EParseError, Exception):
                    pass

        # ── Build the metric engine from ALL known facts ──────────
        engine = MetricEngine()
        engine.process_literals(known_set)

        # Helper: M3/M4/M8 textual variants of a magnitude term
        def _variants(t):
            out = [t]
            if isinstance(t, SegmentTerm):
                out.append(SegmentTerm(t.p2, t.p1))
            elif isinstance(t, AngleTerm):
                out.append(AngleTerm(t.p3, t.p2, t.p1))
            elif isinstance(t, AreaTerm):
                out.append(AreaTerm(t.p3, t.p1, t.p2))
                out.append(AreaTerm(t.p1, t.p3, t.p2))
            return out

        # Collect ref equalities as (left_term, right_term) pairs
        ref_eqs = []
        for lit in ref_lits:
            if not lit.polarity or not isinstance(lit.atom, Equals):
                continue
            a = lit.atom
            if isinstance(a.left, (SegmentTerm, AngleTerm, AreaTerm)):
                ref_eqs.append((a.left, a.right))

        if not ref_eqs:
            return self._AUTOFILL_FAIL

        # Preload ref-term variants into engine
        for left, right in ref_eqs:
            for t in _variants(left) + _variants(right):
                engine.state.add_term(t)
        engine._apply_rules()

        # Multi-ref means the user cited ≥ 2 distinct reference lines
        # with ≥ 2 magnitude equalities → transitivity.
        multi_ref = len(step.refs) >= 2 and len(ref_eqs) >= 2

        def _is_novel(text):
            return text not in known_texts

        # ══════════════════════════════════════════════════════════
        # PATTERN 1: Multi-ref transitivity (CN1)
        # Cross-ref original-term pairings.  Skip trivial M3/M4
        # self-identities.  Prefer alphabetically first.
        # ══════════════════════════════════════════════════════════
        if multi_ref:
            trans_candidates = []
            for i in range(len(ref_eqs)):
                for j in range(i + 1, len(ref_eqs)):
                    li, ri = ref_eqs[i]
                    lj, rj = ref_eqs[j]
                    cross_pairs = [
                        (li, lj), (lj, li),
                        (li, rj), (rj, li),
                        (ri, lj), (lj, ri),
                        (ri, rj), (rj, ri),
                    ]
                    for a, b in cross_pairs:
                        if not engine.state.are_equal(a, b):
                            continue
                        if _term_canon(a) == _term_canon(b):
                            continue
                        lit = Literal(Equals(a, b))
                        text = repr(lit)
                        if _is_novel(text):
                            trans_candidates.append(text)
            if trans_candidates:
                trans_candidates.sort()
                return trans_candidates[0]

        # ══════════════════════════════════════════════════════════
        # PATTERN 2: Angle M4-both-sides rewrite (reversed order)
        # Only for AngleTerm.  Process in reverse so the last angle
        # equality (most useful from SAS/SSS conclusions) is first.
        # ══════════════════════════════════════════════════════════
        if not multi_ref:
            for left, right in reversed(ref_eqs):
                if not isinstance(left, AngleTerm):
                    continue
                lv = _variants(left)
                rv = _variants(right)
                angle_results = []
                for vi in range(1, min(len(lv), len(rv))):
                    for a, b in [(lv[vi], rv[vi]),
                                 (rv[vi], lv[vi])]:
                        lit = Literal(Equals(a, b))
                        text = repr(lit)
                        if _is_novel(text):
                            angle_results.append(text)
                if angle_results:
                    return angle_results[0]

        # ══════════════════════════════════════════════════════════
        # PATTERN 3: Pure swap  (Y = X  from  X = Y)
        # Skip if the same canonical equality already appears in a
        # non-ref prior step (the fact is already known elsewhere).
        # ══════════════════════════════════════════════════════════
        if not multi_ref:
            swap_results = []
            for left, right in ref_eqs:
                lit = Literal(Equals(right, left))
                text = repr(lit)
                if not _is_novel(text):
                    continue
                canon = _eq_canon(lit.atom)
                if canon in non_ref_eq_canons:
                    continue
                swap_results.append(text)
            if swap_results:
                return swap_results[0]

        # ══════════════════════════════════════════════════════════
        # PATTERN 4: M1 disequality (one per canonical point pair)
        # Try (p2, p1) order first for conventional form.
        # ══════════════════════════════════════════════════════════
        diseq_results = []
        seen_diseq_canons = set()
        for left, right in ref_eqs:
            for t in [left, right]:
                if isinstance(t, SegmentTerm) and t.p1 != t.p2:
                    for p, q in [(t.p2, t.p1), (t.p1, t.p2)]:
                        lit = Literal(Equals(p, q), polarity=False)
                        text = repr(lit)
                        canon = _eq_canon(lit.atom)
                        if canon in known_diseq_canons:
                            continue
                        if canon in seen_diseq_canons:
                            continue
                        if _is_novel(text) and engine._check_literal(lit):
                            seen_diseq_canons.add(canon)
                            diseq_results.append(text)
        if diseq_results:
            return diseq_results[0]

        # ══════════════════════════════════════════════════════════
        # PATTERN 5: Angle consequences from segment equalities (M9)
        # Prefer angles whose vertex is the shared point of ref
        # segment terms.
        # ══════════════════════════════════════════════════════════
        ref_points = set()
        for left, right in ref_eqs:
            for t in [left, right]:
                if isinstance(t, SegmentTerm):
                    ref_points.add(t.p1)
                    ref_points.add(t.p2)
                elif isinstance(t, AngleTerm):
                    ref_points.update([t.p1, t.p2, t.p3])

        # Find shared point(s) among ref segment terms
        shared_points = set()
        seg_terms = [t for l, r in ref_eqs
                     for t in [l, r] if isinstance(t, SegmentTerm)]
        if len(seg_terms) >= 2:
            point_sets = [frozenset([t.p1, t.p2]) for t in seg_terms]
            shared_points = point_sets[0]
            for ps in point_sets[1:]:
                shared_points = shared_points & ps
        elif len(seg_terms) == 1:
            shared_points = {seg_terms[0].p1, seg_terms[0].p2}

        if len(ref_points) >= 3:
            angle_terms = []
            angle_reprs = set()
            for perm in permutations(sorted(ref_points), 3):
                at = AngleTerm(perm[0], perm[1], perm[2])
                r = repr(at)
                if r not in angle_reprs:
                    angle_reprs.add(r)
                    angle_terms.append(at)
                    engine.state.add_term(at)

            engine._apply_rules()

            angle_candidates = []
            seen_angle_canons = set()
            for i, a1 in enumerate(angle_terms):
                for a2 in angle_terms[i + 1:]:
                    if not engine.state.are_equal(a1, a2):
                        continue
                    canon = _eq_canon(Equals(a1, a2))
                    if canon in known_eq_canons:
                        continue
                    if canon in seen_angle_canons:
                        continue
                    seen_angle_canons.add(canon)
                    for a_left, a_right in [(a1, a2), (a2, a1)]:
                        lit = Literal(Equals(a_left, a_right))
                        text = repr(lit)
                        if _is_novel(text):
                            score = 0
                            if a_left.p2 in shared_points:
                                score += 1
                            if a_right.p2 in shared_points:
                                score += 1
                            angle_candidates.append((score, text))
                            break
            if angle_candidates:
                angle_candidates.sort(key=lambda x: (-x[0], x[1]))
                return angle_candidates[0][1]

        return self._AUTOFILL_FAIL

    def _autofill_superposition(self, step, just, ref_lits, all_known):
        """Auto-fill a SAS or SSS superposition step.

        Identifies the two triangles from segment and angle equalities
        in the known facts, then delegates to the verifier's
        ``apply_sas_superposition`` or ``apply_sss_superposition``
        to derive the congruence conclusions.

        Returns the generated text, ``_AUTOFILL_FAIL`` if the required
        hypotheses are not met, or ``None`` if the engine is unavailable.
        """
        try:
            from verifier.e_superposition import (
                apply_sas_superposition, apply_sss_superposition,
            )
            from verifier.e_ast import (
                Literal, Equals, SegmentTerm, AngleTerm, AreaTerm,
                literal_vars,
            )
        except ImportError:
            return None

        is_sas = just in ("SAS", "SAS Superposition", "SAS-elim")

        known_set = set(all_known)

        # Collect segment equalities and angle equalities from known facts
        seg_eqs = []   # (p1, p2, q1, q2) meaning p1p2 = q1q2
        angle_eqs = []  # (p1,p2,p3, q1,q2,q3) meaning ∠p1p2p3 = ∠q1q2q3

        for lit in (list(ref_lits) + list(all_known)):
            if not lit.polarity:
                continue
            if not isinstance(lit.atom, Equals):
                continue
            a = lit.atom
            if isinstance(a.left, SegmentTerm) and isinstance(a.right, SegmentTerm):
                seg_eqs.append((a.left.p1, a.left.p2,
                                a.right.p1, a.right.p2))
            elif isinstance(a.left, AngleTerm) and isinstance(a.right, AngleTerm):
                angle_eqs.append((a.left.p1, a.left.p2, a.left.p3,
                                  a.right.p1, a.right.p2, a.right.p3))

        if is_sas:
            # SAS: need an angle equality ∠bac = ∠edf and two segment
            # equalities ab = de, ac = df where a,d are the angle vertices.
            for (ap1, ap2, ap3, aq1, aq2, aq3) in angle_eqs:
                # ap2 is vertex of triangle 1, aq2 is vertex of triangle 2
                # The sides from vertex are: ap2→ap1 and ap2→ap3
                # Need: seg(ap2,ap1) = seg(aq2,aq1) and
                #        seg(ap2,ap3) = seg(aq2,aq3)
                a, b, c = ap2, ap1, ap3
                d, e, f = aq2, aq1, aq3
                # Skip self-congruence where both triangles are the same
                if {a, b, c} == {d, e, f}:
                    continue
                result = apply_sas_superposition(known_set, a, b, c, d, e, f)
                if result.valid:
                    parts = [repr(lit) for lit in result.derived]
                    return ", ".join(parts)
            return self._AUTOFILL_FAIL
        else:
            # SSS: need three segment equalities covering all three sides.
            # Try to identify the triangles from the segment equalities.
            # Strategy: find two segment equalities sharing a "side mapping"
            # pattern, then search for the third.
            from itertools import combinations
            # Try all triples of segment equalities
            seen = set()
            for combo in combinations(range(len(seg_eqs)), 3):
                eqs = [seg_eqs[i] for i in combo]
                # Extract all points on each "side" of the equalities
                left_pts = set()
                right_pts = set()
                for (p1, p2, q1, q2) in eqs:
                    left_pts.update([p1, p2])
                    right_pts.update([q1, q2])
                # For SSS we need exactly 3 points on each side
                if len(left_pts) != 3 or len(right_pts) != 3:
                    continue
                # Skip self-congruence
                if left_pts == right_pts:
                    continue
                # Try to establish vertex correspondence from the equalities
                # Build a correspondence map from the segment equalities
                tri1 = sorted(left_pts)
                tri2 = sorted(right_pts)
                key = (tuple(tri1), tuple(tri2))
                if key in seen:
                    continue
                seen.add(key)
                # Try all possible orderings: the first segment eq gives
                # vertex correspondence a↔d, b↔e, then verify the third
                for (p1, p2, q1, q2) in eqs:
                    for a, b in [(p1, p2), (p2, p1)]:
                        for d, e in [(q1, q2), (q2, q1)]:
                            c_set = left_pts - {a, b}
                            f_set = right_pts - {d, e}
                            if len(c_set) != 1 or len(f_set) != 1:
                                continue
                            c = c_set.pop()
                            f = f_set.pop()
                            result = apply_sss_superposition(
                                known_set, a, b, c, d, e, f)
                            if result.valid:
                                parts = [repr(lit) for lit in result.derived]
                                return ", ".join(parts)
            return self._AUTOFILL_FAIL

    @staticmethod
    def _match_hypotheses(patterns, concrete_lits):
        """Match a list of pattern literals against concrete literals
        to derive variable bindings, using the same algorithm as
        the verifier's _try_match_literal.

        Returns a tuple ``(bindings, matched_count)`` where *bindings*
        maps template variable names to concrete names and
        *matched_count* is how many patterns were successfully matched.
        """
        from verifier.unified_checker import _try_match_literal
        bindings = {}
        matched = 0
        remaining = list(concrete_lits)
        for pat in patterns:
            for i, conc in enumerate(remaining):
                result = _try_match_literal(pat, conc, bindings)
                if result is not None:
                    bindings = result
                    remaining.pop(i)
                    matched += 1
                    break
        return bindings, matched

    @staticmethod
    def _pick_fresh_name(template_name, sort, used_names):
        """Pick a fresh variable name that doesn't collide with used_names.

        Follows System E naming conventions:
          - Points: lowercase single letters (a, b, c, ...)
          - Lines: uppercase single letters (L, M, N, ...)
          - Circles: Greek letters (α, β, γ, ...)
        """
        from verifier.e_ast import Sort

        if sort == Sort.LINE:
            candidates = [chr(c) for c in range(ord('L'), ord('Z') + 1)]
        elif sort == Sort.CIRCLE:
            candidates = ["\u03b1", "\u03b2", "\u03b3", "\u03b4",
                          "\u03b5", "\u03b6", "\u03b7", "\u03b8"]
        else:
            # Point: try the template name first, then a-z
            candidates = [template_name] + [
                chr(c) for c in range(ord('a'), ord('z') + 1)]

        for name in candidates:
            if name not in used_names:
                return name
        # Fallback: numbered names
        for i in range(1, 100):
            candidate = template_name + str(i)
            if candidate not in used_names:
                return candidate
        return template_name

    def _get_line_text(self, line_number):
        """Return the text of a proof line or premise by line number."""
        # Check premises first
        if 1 <= line_number <= len(self._premises):
            return self._premises[line_number - 1]
        # Then proof steps
        for s in self._steps:
            if s.line_number == line_number:
                return s.text
        return None

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
    # LEMMA MANAGEMENT
    # ===============================================================

    # ── Lemma helpers ────────────────────────────────────────────

    @staticmethod
    def _euclid_to_verifier(data: dict) -> dict:
        """Convert a .euclid file to the flat verifier JSON format.

        .euclid files nest proof data under a ``proof`` key with
        ``steps`` (using ``lineNumber``, ``text``, ``dependencies``)
        instead of the verifier's ``lines`` (``id``, ``statement``,
        ``refs``).  Given lines are reconstructed from ``premises``.
        """
        proof = data.get("proof", {})
        steps = proof.get("steps", [])
        premises = proof.get("premises", [])
        goal = proof.get("goal", "")
        name = proof.get("name", data.get("name", "unnamed"))

        lines = []
        for i, p in enumerate(premises, 1):
            lines.append({
                "id": i, "depth": 0,
                "statement": p, "justification": "Given", "refs": []})
        for s in steps:
            lines.append({
                "id": s["lineNumber"],
                "depth": s.get("depth", 0),
                "statement": s["text"],
                "justification": s["justification"],
                "refs": s.get("dependencies", [])})
        return {
            "name": name,
            "premises": premises,
            "goal": goal,
            "lines": lines,
        }

    def _load_lemma(self):
        """Load a verified proof (.euclid or .json) as a reusable lemma."""
        from .main_window import _OpenFileDialog
        dlg = _OpenFileDialog(self)
        dlg.setWindowTitle("Load Proof as Lemma")
        if dlg.exec() != _OpenFileDialog.DialogCode.Accepted:
            return
        path = dlg.selected_path
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception as exc:
            self._goal_status.setToolTip(
                "Lemma load error: " + str(exc))
            return

        # Detect .euclid format (has a "proof" sub-object with "steps")
        if "proof" in data and "steps" in data.get("proof", {}):
            verifier_data = self._euclid_to_verifier(data)
        else:
            verifier_data = data

        name = verifier_data.get("name", "unnamed")
        goal = verifier_data.get("goal", "")
        premises = verifier_data.get("premises", [])
        if not goal:
            self._goal_status.setToolTip(
                "Lemma has no goal \u2014 cannot use as a rule.")
            return

        # Check for duplicates
        for existing in self._lemmas:
            if existing.name == name:
                self._goal_status.setToolTip(
                    "Lemma '" + name + "' already loaded.")
                return

        # Add the lemma immediately as "verifying" so it appears in the UI
        lemma = LoadedLemma(name, premises, goal, path)
        lemma._verified = False
        lemma._verifying = True
        lemma._verifier_data = verifier_data
        self._lemmas.append(lemma)
        self._rebuild_lemma_ui()
        self._goal_status.setToolTip(
            "Verifying lemma '" + name + "'\u2026")

        # Run verification in a background thread
        self._verify_lemma_bg(lemma)

    def _verify_lemma_bg(self, lemma):
        """Run lemma verification on a background thread."""
        class _LemmaWorker(QObject):
            finished = pyqtSignal(object)  # True/False/Exception

            def __init__(self, verifier_data):
                super().__init__()
                self._data = verifier_data

            def run(self):
                try:
                    from verifier.unified_checker import verify_e_proof_json
                    result = verify_e_proof_json(self._data)
                    self.finished.emit(result.accepted)
                except Exception as exc:
                    self.finished.emit(exc)

        thread = QThread()
        worker = _LemmaWorker(lemma._verifier_data)
        worker.moveToThread(thread)
        thread.started.connect(worker.run)

        def _on_done(result_or_exc):
            thread.quit()
            thread.wait(2000)
            thread.deleteLater()
            lemma._verifying = False

            if isinstance(result_or_exc, Exception):
                lemma._verified = False
                self._goal_status.setToolTip(
                    "Lemma '" + lemma.name
                    + "' verification error: " + str(result_or_exc))
            elif result_or_exc:
                lemma._verified = True
                self._goal_status.setToolTip(
                    "Lemma '" + lemma.name
                    + "' loaded \u2713  Goal: " + lemma.goal)
            else:
                lemma._verified = False
                self._goal_status.setToolTip(
                    "Lemma '" + lemma.name
                    + "' rejected \u2014 proof is not valid.")
            # Clean up cached verifier data
            lemma._verifier_data = None
            self._rebuild_lemma_ui()

        worker.finished.connect(
            _on_done, Qt.ConnectionType.QueuedConnection)
        thread.start()

        # Keep references so they aren't GC'd
        lemma._thread = thread
        lemma._worker = worker

    def _remove_lemma(self, index):
        """Remove a loaded lemma by index."""
        if 0 <= index < len(self._lemmas):
            removed = self._lemmas.pop(index)
            self._unregister_lemma_rule(removed)
            self._rebuild_lemma_ui()

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
            if lem._verifying:
                bg, border = "#fffde7", "#fff59d"   # yellow – verifying
            elif lem._verified:
                bg, border = "#e8f5e9", "#a5d6a7"   # green – valid
            else:
                bg, border = "#ffebee", "#ef9a9a"   # red – invalid
            row.setStyleSheet(
                f"QFrame {{ background:{bg};"
                f" border:1px solid {border}; border-radius:3px;"
                f" padding:2px 4px; }}")
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
