"""
diagnostics_panel.py — Error summary sidebar for proof diagnostics.

Shows:
  • Total error count with badge
  • List of diagnostics: line number, code, message
  • Click to navigate to failing line
  • One-click copy of diagnostic text
"""
from __future__ import annotations

from typing import List

from PyQt6.QtCore import Qt, pyqtSignal
from PyQt6.QtGui import QColor, QFont
from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QLabel, QPushButton,
    QListWidget, QListWidgetItem, QFrame, QApplication,
)

from .fitch_theme import C, Fonts, Sp, Sym


class DiagnosticItem:
    """One diagnostic entry."""
    __slots__ = ("line", "code", "message")

    def __init__(self, line: int, code: str, message: str):
        self.line = line
        self.code = code
        self.message = message


class DiagnosticsPanel(QWidget):
    """Diagnostics / error panel — right sidebar or lower panel."""

    navigate_to_line = pyqtSignal(int)  # emits line_id to jump to

    def __init__(self, parent=None):
        super().__init__(parent)
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # ── Header with error count badge ─────────────────────────
        header = QFrame()
        header.setStyleSheet(f"background: {C.surface}; border-bottom: 1px solid {C.border};")
        hl = QHBoxLayout(header)
        hl.setContentsMargins(Sp.padding, Sp.padding_sm, Sp.padding, Sp.padding_sm)

        title = QLabel("Diagnostics")
        title.setFont(Fonts.heading(11))
        title.setStyleSheet(f"color: {C.text_secondary};")
        hl.addWidget(title)
        hl.addStretch()

        self._count_badge = QLabel("0")
        self._count_badge.setFont(Fonts.ui_bold(10))
        self._count_badge.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._count_badge.setFixedSize(24, 20)
        self._count_badge.setStyleSheet(f"""
            background: {C.text_muted};
            color: white;
            border-radius: 10px;
            font-size: 10px;
        """)
        hl.addWidget(self._count_badge)

        self._copy_btn = QPushButton("Copy")
        self._copy_btn.setFixedHeight(24)
        self._copy_btn.setStyleSheet(f"""
            QPushButton {{ border: 1px solid {C.border}; border-radius: 3px; padding: 2px 8px; font-size: 11px; color: {C.text_secondary}; background: transparent; }}
            QPushButton:hover {{ background: {C.surface_hover}; }}
        """)
        self._copy_btn.clicked.connect(self._copy_all)
        hl.addWidget(self._copy_btn)

        layout.addWidget(header)

        # ── Diagnostic list ───────────────────────────────────────
        self._list = QListWidget()
        self._list.setStyleSheet(f"""
            QListWidget {{
                border: none;
                background: {C.surface};
                font-size: 12px;
            }}
            QListWidget::item {{
                padding: 8px 12px;
                border-bottom: 1px solid {C.border_light};
            }}
            QListWidget::item:hover {{
                background: {C.error_bg};
            }}
            QListWidget::item:selected {{
                background: {C.error_bg_deep};
            }}
        """)
        self._list.itemClicked.connect(self._on_click)
        layout.addWidget(self._list)

        # ── Empty state ───────────────────────────────────────────
        self._empty = QLabel("No errors")
        self._empty.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._empty.setFont(Fonts.ui(12))
        self._empty.setStyleSheet(f"color: {C.valid}; padding: 24px;")
        layout.addWidget(self._empty)

        self._items: List[DiagnosticItem] = []

    def set_diagnostics(self, diags: List[dict]):
        """Load diagnostics from verifier result dicts."""
        self._items = [DiagnosticItem(d["line"], d["code"], d["message"]) for d in diags]
        self._list.clear()

        for d in self._items:
            text = f"Line {d.line}  [{d.code}]\n{d.message}"
            item = QListWidgetItem(text)
            item.setForeground(QColor(C.invalid))
            item.setData(Qt.ItemDataRole.UserRole, d.line)
            self._list.addItem(item)

        count = len(self._items)
        self._count_badge.setText(str(count))
        if count > 0:
            self._count_badge.setStyleSheet(f"""
                background: {C.invalid};
                color: white;
                border-radius: 10px;
                font-size: 10px;
            """)
            self._empty.hide()
            self._list.show()
        else:
            self._count_badge.setStyleSheet(f"""
                background: {C.valid};
                color: white;
                border-radius: 10px;
                font-size: 10px;
            """)
            self._empty.show()
            self._list.hide()

    def _on_click(self, item: QListWidgetItem):
        line_id = item.data(Qt.ItemDataRole.UserRole)
        if line_id is not None:
            self.navigate_to_line.emit(line_id)

    def _copy_all(self):
        if not self._items:
            return
        text = "\n".join(f"Line {d.line} [{d.code}]: {d.message}" for d in self._items)
        QApplication.clipboard().setText(text)
