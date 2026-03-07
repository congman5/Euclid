"""
summary_panel.py — Proof metadata and status panel (left sidebar).

Shows:
  • Proof name
  • Declarations (points, lines)
  • Premises
  • Goal
  • Verification status badge (accepted / rejected)
  • First failing line, error count, line count
  • Kernel vs derived rule usage counts
"""
from __future__ import annotations

from typing import Dict, List, Optional

from PyQt6.QtCore import Qt
from PyQt6.QtGui import QColor
from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QLabel, QFrame,
    QScrollArea, QSizePolicy,
)

from .fitch_theme import C, Fonts, Sp, Sym


class SummaryPanel(QWidget):
    """Left sidebar showing proof metadata and verification summary."""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setMinimumWidth(220)
        self.setMaximumWidth(320)

        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        outer.setSpacing(0)

        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        scroll.setStyleSheet(f"QScrollArea {{ border: none; background: {C.surface}; }}")

        container = QWidget()
        layout = QVBoxLayout(container)
        layout.setContentsMargins(Sp.padding, Sp.padding, Sp.padding, Sp.padding)
        layout.setSpacing(Sp.padding)

        # ── Status badge ──────────────────────────────────────────
        self._status_badge = QLabel()
        self._status_badge.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._status_badge.setFont(Fonts.ui_bold(14))
        self._status_badge.setFixedHeight(40)
        self._status_badge.setStyleSheet(f"""
            background: {C.text_muted};
            color: white;
            border-radius: 6px;
            padding: 4px 16px;
        """)
        layout.addWidget(self._status_badge)

        # ── Proof name ────────────────────────────────────────────
        self._name_label = _section(layout, "PROOF")
        self._name_value = _value(layout)

        # ── Declarations ──────────────────────────────────────────
        _section(layout, "DECLARATIONS")
        self._decl_points = _kv_row(layout, "Points")
        self._decl_lines = _kv_row(layout, "Lines")

        # ── Premises ──────────────────────────────────────────────
        _section(layout, "PREMISES")
        self._premises_container = QVBoxLayout()
        self._premises_container.setSpacing(2)
        layout.addLayout(self._premises_container)

        # ── Goal ──────────────────────────────────────────────────
        _section(layout, "GOAL")
        self._goal_value = QLabel()
        self._goal_value.setFont(Fonts.formula(12))
        self._goal_value.setWordWrap(True)
        self._goal_value.setStyleSheet(f"color: {C.text_formula}; padding: 2px 0;")
        layout.addWidget(self._goal_value)

        # ── Statistics ────────────────────────────────────────────
        _section(layout, "STATISTICS")
        self._stat_lines = _kv_row(layout, "Lines")
        self._stat_errors = _kv_row(layout, "Errors")
        self._stat_first_error = _kv_row(layout, "First error")
        self._stat_goal_line = _kv_row(layout, "Goal on line")

        # ── Rule usage ────────────────────────────────────────────
        _section(layout, "RULES USED")
        self._rules_container = QVBoxLayout()
        self._rules_container.setSpacing(1)
        layout.addLayout(self._rules_container)

        layout.addStretch()
        scroll.setWidget(container)
        outer.addWidget(scroll)

    # ── Public API ────────────────────────────────────────────────

    def set_proof_info(
        self,
        name: str = "",
        points: List[str] | None = None,
        lines_decl: List[str] | None = None,
        premises: List[str] | None = None,
        goal: str = "",
    ):
        self._name_value.setText(name or "untitled")
        self._decl_points.setText(", ".join(points) if points else "—")
        self._decl_lines.setText(", ".join(lines_decl) if lines_decl else "—")
        self._goal_value.setText(goal or "—")
        # Clear old premise labels
        while self._premises_container.count():
            w = self._premises_container.takeAt(0).widget()
            if w:
                w.deleteLater()
        for p in (premises or []):
            lbl = QLabel(p)
            lbl.setFont(Fonts.formula(11))
            lbl.setStyleSheet(f"color: {C.text_formula}; padding: 1px 0;")
            lbl.setWordWrap(True)
            self._premises_container.addWidget(lbl)

    def set_result(
        self,
        accepted: bool,
        num_lines: int = 0,
        num_errors: int = 0,
        first_error_line: int | None = None,
        goal_derived_on: int | None = None,
        rule_counts: Dict[str, int] | None = None,
    ):
        if accepted:
            self._status_badge.setText(f"{Sym.check}  ACCEPTED")
            self._status_badge.setStyleSheet(f"""
                background: {C.valid};
                color: white;
                border-radius: 6px;
                padding: 4px 16px;
                font-size: 14px;
                font-weight: bold;
            """)
        else:
            self._status_badge.setText(f"{Sym.cross}  REJECTED")
            self._status_badge.setStyleSheet(f"""
                background: {C.invalid};
                color: white;
                border-radius: 6px;
                padding: 4px 16px;
                font-size: 14px;
                font-weight: bold;
            """)
        self._stat_lines.setText(str(num_lines))
        self._stat_errors.setText(str(num_errors))
        self._stat_first_error.setText(str(first_error_line) if first_error_line else "—")
        self._stat_goal_line.setText(str(goal_derived_on) if goal_derived_on else "—")

        # Rule usage
        while self._rules_container.count():
            w = self._rules_container.takeAt(0).widget()
            if w:
                w.deleteLater()
        if rule_counts:
            for rule_name, count in sorted(rule_counts.items()):
                row = QWidget()
                rl = QHBoxLayout(row)
                rl.setContentsMargins(0, 0, 0, 0)
                rl.setSpacing(4)
                nm = QLabel(rule_name)
                nm.setFont(Fonts.ui(11))
                nm.setStyleSheet(f"color: {C.text};")
                cnt = QLabel(str(count))
                cnt.setFont(Fonts.ui(11))
                cnt.setStyleSheet(f"color: {C.text_muted};")
                cnt.setAlignment(Qt.AlignmentFlag.AlignRight)
                rl.addWidget(nm, stretch=1)
                rl.addWidget(cnt)
                self._rules_container.addWidget(row)

    def clear(self):
        self._status_badge.setText("—")
        self._status_badge.setStyleSheet(f"""
            background: {C.text_muted};
            color: white;
            border-radius: 6px;
            padding: 4px 16px;
        """)
        self._name_value.setText("")
        self._decl_points.setText("—")
        self._decl_lines.setText("—")
        self._goal_value.setText("—")
        self._stat_lines.setText("—")
        self._stat_errors.setText("—")
        self._stat_first_error.setText("—")
        self._stat_goal_line.setText("—")
        while self._premises_container.count():
            w = self._premises_container.takeAt(0).widget()
            if w:
                w.deleteLater()
        while self._rules_container.count():
            w = self._rules_container.takeAt(0).widget()
            if w:
                w.deleteLater()


# ── Helpers ───────────────────────────────────────────────────────────

def _section(parent_layout: QVBoxLayout, text: str) -> QLabel:
    lbl = QLabel(text)
    lbl.setFont(Fonts.heading(10))
    lbl.setStyleSheet(f"color: {C.text_muted}; padding-top: 8px;")
    parent_layout.addWidget(lbl)
    return lbl


def _value(parent_layout: QVBoxLayout) -> QLabel:
    lbl = QLabel()
    lbl.setFont(Fonts.ui_bold(13))
    lbl.setStyleSheet(f"color: {C.text};")
    lbl.setWordWrap(True)
    parent_layout.addWidget(lbl)
    return lbl


def _kv_row(parent_layout: QVBoxLayout, key: str) -> QLabel:
    row = QWidget()
    rl = QHBoxLayout(row)
    rl.setContentsMargins(0, 0, 0, 0)
    rl.setSpacing(4)
    k = QLabel(key)
    k.setFont(Fonts.ui(11))
    k.setStyleSheet(f"color: {C.text_secondary};")
    v = QLabel("—")
    v.setFont(Fonts.ui(11))
    v.setStyleSheet(f"color: {C.text};")
    v.setAlignment(Qt.AlignmentFlag.AlignRight)
    rl.addWidget(k, stretch=1)
    rl.addWidget(v)
    parent_layout.addWidget(row)
    return v
