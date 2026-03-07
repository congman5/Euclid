"""
proof_editor.py — Structured proof editing support.

Provides a toolbar / panel for:
  • Adding new proof lines (formula + justification + refs + depth)
  • Inserting lines at a position
  • Deleting lines
  • Opening / closing subproofs (depth control)
  • Justification picker with the verifier's rule catalog
  • Reference entry with validation
  • Exporting edited proof back to JSON

This is designed to sit below or alongside the FitchProofView.
"""
from __future__ import annotations

import json
from typing import Dict, List, Optional, Callable

from PyQt6.QtCore import Qt, pyqtSignal
from PyQt6.QtGui import QFont
from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QLabel, QPushButton,
    QLineEdit, QComboBox, QSpinBox, QFrame, QFileDialog,
    QMessageBox,
)

from .fitch_theme import C, Fonts, Sp

# ── Rule names from the verifier registry ─────────────────────────────

_RULE_GROUPS = {
    "Logical": [
        "Given", "Assume", "Reit",
        "AndIntro", "AndElimL", "AndElimR",
        "OrIntroL", "OrIntroR",
        "IffElimLR", "IffElimRL",
        "EqSym", "EqTrans",
        "ContrIntro", "ContrElim",
        "RAA",
        "ExactlyOneContradiction",
    ],
    "Geometric": [
        "Inc1", "Inc2", "Inc3",
        "Ord1", "Ord2", "Ord3", "Ord4",
        "Pasch",
        "Cong1", "Cong2", "Cong3", "Cong4",
        "SAS", "Parallel",
    ],
    "Proof Admin": [
        "Witness", "WitnessUnique", "UniqueElim",
    ],
    "Derived": [
        "CongruenceElim", "SSS", "Midpoint", "Perpendicular",
    ],
}


class ProofEditor(QFrame):
    """Compact editing toolbar for proof construction."""

    proof_changed = pyqtSignal(dict)  # emits full proof dict when modified

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setStyleSheet(f"""
            ProofEditor {{
                background: {C.surface};
                border-top: 1px solid {C.border};
            }}
        """)
        self._proof_data: dict = {
            "name": "untitled",
            "declarations": {"points": [], "lines": []},
            "premises": [],
            "goal": "",
            "lines": [],
        }

        layout = QVBoxLayout(self)
        layout.setContentsMargins(Sp.padding, Sp.padding_sm, Sp.padding, Sp.padding_sm)
        layout.setSpacing(Sp.padding_sm)

        # ── Header ────────────────────────────────────────────────
        header = QLabel("EDIT PROOF LINE")
        header.setFont(Fonts.heading(10))
        header.setStyleSheet(f"color: {C.text_muted};")
        layout.addWidget(header)

        # ── Formula input ─────────────────────────────────────────
        row1 = QHBoxLayout()
        row1.setSpacing(8)

        self._formula_input = QLineEdit()
        self._formula_input.setPlaceholderText("Formula  (e.g.  A != B, OnLine(A, l), ...)")
        self._formula_input.setFont(Fonts.formula(13))
        self._formula_input.setMinimumHeight(32)
        self._formula_input.setStyleSheet(f"""
            QLineEdit {{
                border: 1px solid {C.border};
                border-radius: 4px;
                padding: 4px 10px;
                background: {C.surface};
            }}
            QLineEdit:focus {{
                border-color: {C.primary};
            }}
        """)
        row1.addWidget(self._formula_input, stretch=2)

        # Justification combo
        self._just_combo = QComboBox()
        self._just_combo.setMinimumWidth(160)
        for group, rules in _RULE_GROUPS.items():
            for r in rules:
                self._just_combo.addItem(f"{r}  ({group})", r)
        self._just_combo.setStyleSheet(f"""
            QComboBox {{
                border: 1px solid {C.border};
                border-radius: 4px;
                padding: 4px 8px;
                min-height: 28px;
            }}
        """)
        row1.addWidget(self._just_combo, stretch=1)
        layout.addLayout(row1)

        # ── Refs + depth ──────────────────────────────────────────
        row2 = QHBoxLayout()
        row2.setSpacing(8)

        row2.addWidget(QLabel("Refs:"))
        self._refs_input = QLineEdit()
        self._refs_input.setPlaceholderText("e.g. 1,3")
        self._refs_input.setMaximumWidth(120)
        self._refs_input.setStyleSheet(f"border: 1px solid {C.border}; border-radius: 3px; padding: 4px 8px;")
        row2.addWidget(self._refs_input)

        row2.addWidget(QLabel("Depth:"))
        self._depth_spin = QSpinBox()
        self._depth_spin.setRange(0, 20)
        self._depth_spin.setValue(0)
        self._depth_spin.setFixedWidth(60)
        row2.addWidget(self._depth_spin)

        row2.addStretch()

        # Buttons
        btn_add = QPushButton("+ Add Line")
        btn_add.setObjectName("primary_btn")
        btn_add.clicked.connect(self._add_line)
        row2.addWidget(btn_add)

        btn_insert = QPushButton("Insert Before")
        btn_insert.clicked.connect(self._insert_before)
        row2.addWidget(btn_insert)

        btn_delete = QPushButton("Delete Selected")
        btn_delete.setStyleSheet(f"color: {C.invalid}; border: 1px solid {C.invalid}; border-radius: 4px; padding: 4px 12px;")
        btn_delete.clicked.connect(self._delete_selected)
        row2.addWidget(btn_delete)

        layout.addLayout(row2)

        # ── Subproof shortcuts ────────────────────────────────────
        row3 = QHBoxLayout()
        row3.setSpacing(8)

        btn_open_sub = QPushButton("Open Subproof (Assume)")
        btn_open_sub.setToolTip("Add an Assume line at depth+1")
        btn_open_sub.clicked.connect(self._open_subproof)
        row3.addWidget(btn_open_sub)

        btn_close_sub = QPushButton("Close Subproof")
        btn_close_sub.setToolTip("Set depth back to previous level")
        btn_close_sub.clicked.connect(self._close_subproof)
        row3.addWidget(btn_close_sub)

        row3.addStretch()

        btn_export = QPushButton("Export JSON")
        btn_export.clicked.connect(self._export_json)
        row3.addWidget(btn_export)

        layout.addLayout(row3)

        self._selected_line_idx: int = -1

    # ── Public API ────────────────────────────────────────────────

    def set_proof_data(self, data: dict):
        self._proof_data = data

    def set_selected_line(self, line_id: int):
        """Called when a line is selected in the proof view."""
        for i, ld in enumerate(self._proof_data.get("lines", [])):
            if ld["id"] == line_id:
                self._selected_line_idx = i
                self._formula_input.setText(ld.get("statement", ""))
                self._just_combo.setCurrentText(
                    next((self._just_combo.itemText(j) for j in range(self._just_combo.count())
                          if self._just_combo.itemData(j) == ld.get("justification", "")), "")
                )
                refs_str = ",".join(str(r) for r in ld.get("refs", []))
                self._refs_input.setText(refs_str)
                self._depth_spin.setValue(ld.get("depth", 0))
                return
        self._selected_line_idx = -1

    # ── Internal ──────────────────────────────────────────────────

    def _parse_refs(self) -> List[int]:
        raw = self._refs_input.text().strip()
        if not raw:
            return []
        parts = [p.strip() for p in raw.replace(";", ",").split(",") if p.strip()]
        refs = []
        for p in parts:
            try:
                refs.append(int(p))
            except ValueError:
                pass
        return refs

    def _next_id(self) -> int:
        lines = self._proof_data.get("lines", [])
        return max((ld["id"] for ld in lines), default=0) + 1

    def _build_line_dict(self) -> dict:
        return {
            "id": self._next_id(),
            "depth": self._depth_spin.value(),
            "statement": self._formula_input.text().strip(),
            "justification": self._just_combo.currentData() or "Given",
            "refs": self._parse_refs(),
        }

    def _add_line(self):
        formula = self._formula_input.text().strip()
        if not formula:
            return
        ld = self._build_line_dict()
        self._proof_data.setdefault("lines", []).append(ld)
        self._formula_input.clear()
        self._refs_input.clear()
        self.proof_changed.emit(self._proof_data)

    def _insert_before(self):
        formula = self._formula_input.text().strip()
        if not formula or self._selected_line_idx < 0:
            return
        ld = self._build_line_dict()
        self._proof_data["lines"].insert(self._selected_line_idx, ld)
        # Renumber
        for i, line in enumerate(self._proof_data["lines"]):
            line["id"] = i + 1
        self._formula_input.clear()
        self._refs_input.clear()
        self.proof_changed.emit(self._proof_data)

    def _delete_selected(self):
        if self._selected_line_idx < 0:
            return
        lines = self._proof_data.get("lines", [])
        if 0 <= self._selected_line_idx < len(lines):
            lines.pop(self._selected_line_idx)
            for i, line in enumerate(lines):
                line["id"] = i + 1
            self._selected_line_idx = -1
            self.proof_changed.emit(self._proof_data)

    def _open_subproof(self):
        """Add an Assume line at current depth + 1."""
        formula = self._formula_input.text().strip()
        if not formula:
            formula = "?"
        current_depth = self._depth_spin.value()
        ld = {
            "id": self._next_id(),
            "depth": current_depth + 1,
            "statement": formula,
            "justification": "Assume",
            "refs": [],
        }
        self._proof_data.setdefault("lines", []).append(ld)
        self._depth_spin.setValue(current_depth + 1)
        self._formula_input.clear()
        self.proof_changed.emit(self._proof_data)

    def _close_subproof(self):
        current = self._depth_spin.value()
        if current > 0:
            self._depth_spin.setValue(current - 1)

    def _export_json(self):
        path, _ = QFileDialog.getSaveFileName(
            self, "Export Proof JSON", "", "JSON Files (*.json)"
        )
        if path:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(self._proof_data, f, indent=2)
            QMessageBox.information(self, "Exported", f"Proof saved to {path}")
