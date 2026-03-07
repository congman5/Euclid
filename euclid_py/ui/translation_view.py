"""
translation_view.py — Read-only H/T Translation View.

Shows the same theorem in all three formal notations side-by-side:
  System E (primary), System T (Tarski bridge), System H (Hilbert).

This is a **display** feature, not a verification path.
Phase 9.3 of the implementation plan.
"""
from __future__ import annotations

from PyQt6.QtCore import Qt
from PyQt6.QtGui import QFont
from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QLabel, QFrame,
    QScrollArea,
)

from .fitch_theme import C, Fonts, Sp


# ── Badge colours for each system ─────────────────────────────────────

_SYSTEM_COLORS = {
    "E": "#2e7d32",   # green
    "T": "#1565c0",   # blue
    "H": "#6a1b9a",   # purple
}


class TranslationView(QWidget):
    """Read-only panel showing E / T / H notations for one proposition."""

    def __init__(self, parent=None):
        super().__init__(parent)
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # ── Header ────────────────────────────────────────────────
        header = QFrame()
        header.setStyleSheet(
            f"background: {C.header_bg};"
            f"border-bottom: 1px solid {C.border};")
        hl = QHBoxLayout(header)
        hl.setContentsMargins(Sp.padding, 10, Sp.padding, 10)
        title = QLabel("E / T / H Translation View")
        title.setFont(Fonts.heading(12))
        title.setStyleSheet(f"color: {C.header_text};")
        hl.addWidget(title)
        layout.addWidget(header)

        # ── Scroll area ──────────────────────────────────────────
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setHorizontalScrollBarPolicy(
            Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        scroll.setStyleSheet(f"""
            QScrollArea {{ border: none; background: {C.bg}; }}
            QScrollBar:vertical {{
                width: 6px; background: transparent;
            }}
            QScrollBar::handle:vertical {{
                background: {C.border}; border-radius: 3px; min-height: 30px;
            }}
            QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {{
                height: 0;
            }}
        """)

        self._container = QWidget()
        self._container_layout = QVBoxLayout(self._container)
        self._container_layout.setContentsMargins(0, 0, 0, 0)
        self._container_layout.setSpacing(0)
        scroll.setWidget(self._container)
        layout.addWidget(scroll)

        # Show placeholder
        self._show_placeholder()

    # ── Public API ───────────────────────────────────────────────

    def set_proposition(self, prop):
        """Update the view for a Proposition object.

        Fetches E, T, and H sequents via the proposition's library
        accessors and displays them side-by-side.
        """
        self._clear()

        name = getattr(prop, "name", "")
        e_thm = prop.get_e_theorem() if hasattr(prop, "get_e_theorem") else None
        h_thm = prop.get_h_theorem() if hasattr(prop, "get_h_theorem") else None

        if e_thm is None and h_thm is None:
            self._show_placeholder(
                f"No formal library entry for {name}.")
            return

        # Title
        title = QLabel(name)
        title.setFont(Fonts.ui_bold(13))
        title.setStyleSheet(
            f"color: {C.text}; background: transparent;"
            f"padding: 12px 12px 2px 12px;")
        self._container_layout.addWidget(title)

        # Statement
        stmt = ""
        if e_thm is not None:
            stmt = getattr(e_thm, 'statement', '') or ''
        if stmt:
            stmt_lbl = QLabel(stmt)
            stmt_lbl.setFont(Fonts.ui(10))
            stmt_lbl.setWordWrap(True)
            stmt_lbl.setStyleSheet(
                f"color: {C.text_muted}; background: transparent;"
                f"padding: 0px 12px 8px 12px; font-style: italic;")
            self._container_layout.addWidget(stmt_lbl)

        # System E
        if e_thm is not None:
            e_text = str(e_thm.sequent)
            self._add_system_card("E", "System E  (Euclid)", e_text)

            # System T — translate via π
            t_text = self._translate_to_t(e_thm.sequent)
            if t_text:
                self._add_system_card("T", "System T  (Tarski)", t_text)

        # System H
        if h_thm is not None:
            h_text = str(h_thm.sequent)
            self._add_system_card("H", "System H  (Hilbert)", h_text)

        self._container_layout.addStretch()

    def clear(self):
        """Reset to placeholder state."""
        self._clear()
        self._show_placeholder()

    # ── Internals ────────────────────────────────────────────────

    def _clear(self):
        while self._container_layout.count():
            item = self._container_layout.takeAt(0)
            w = item.widget()
            if w:
                w.deleteLater()

    def _show_placeholder(self, msg: str = ""):
        self._clear()
        text = msg or "Open a proposition to see E / T / H translations."
        lbl = QLabel(text)
        lbl.setFont(Fonts.ui(11))
        lbl.setStyleSheet(
            f"color: {C.text_muted}; padding: 24px; font-style: italic;")
        lbl.setWordWrap(True)
        lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._container_layout.addWidget(lbl)
        self._container_layout.addStretch()

    def _add_system_card(self, system_key: str, label: str, sequent_text: str):
        """Add one system card (badge + sequent text)."""
        card = QFrame()
        card.setObjectName("system_card")
        badge_color = _SYSTEM_COLORS.get(system_key, C.primary)
        card.setStyleSheet(f"""
            QFrame#system_card {{
                background: {C.surface};
                border-bottom: 1px solid {C.border};
                border-left: 3px solid {badge_color};
            }}
            QFrame#system_card:hover {{
                background: {C.surface_hover};
            }}
        """)
        vl = QVBoxLayout(card)
        vl.setContentsMargins(14, 10, 12, 10)
        vl.setSpacing(6)

        # Top row: badge + system label
        top = QHBoxLayout()
        top.setSpacing(8)

        badge = QLabel(system_key)
        badge.setFont(Fonts.ui(9))
        badge.setFixedHeight(18)
        badge.setStyleSheet(f"""
            background: {badge_color};
            color: white;
            border-radius: 3px;
            padding: 1px 8px;
            font-size: 10px;
            font-weight: bold;
        """)
        top.addWidget(badge)

        sys_label = QLabel(label)
        sys_label.setFont(Fonts.ui_bold(11))
        sys_label.setStyleSheet(f"color: {C.text}; background: transparent;")
        top.addWidget(sys_label)
        top.addStretch()
        vl.addLayout(top)

        # Sequent text (formula font, selectable, with background)
        seq = QLabel(sequent_text)
        seq.setFont(Fonts.formula(11))
        seq.setStyleSheet(f"""
            color: {C.text};
            padding: 8px 10px;
            background: {C.bg};
            border: 1px solid {C.border_light};
            border-radius: 4px;
        """)
        seq.setWordWrap(True)
        seq.setTextInteractionFlags(
            Qt.TextInteractionFlag.TextSelectableByMouse)
        vl.addWidget(seq)

        self._container_layout.addWidget(card)

    @staticmethod
    def _translate_to_t(e_sequent):
        """Translate an E sequent to T notation via π. Returns str or None."""
        try:
            from verifier.t_pi_translation import pi_sequent
            t_seq, _ = pi_sequent(e_sequent)
            return str(t_seq)
        except Exception:
            return None
