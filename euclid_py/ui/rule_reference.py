"""
rule_reference.py — Rule catalog sidebar / reference panel.

Sources rules from verifier.unified_checker.get_available_rules(),
which returns System E axioms grouped by paper sections (§3.3–§3.7)
plus proposition theorems from e_library.  Includes a dynamic Lemmas
section, collapsible groups, and search filtering.

Phase 9.4 of the implementation plan.
"""
from __future__ import annotations

from PyQt6.QtCore import Qt, QPropertyAnimation, QEasingCurve
from PyQt6.QtGui import QFont, QCursor
from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QLabel, QFrame,
    QScrollArea, QLineEdit, QSizePolicy,
)

from .fitch_theme import C, Fonts, Sp

# ── Section ordering (category → display header) ─────────────────────

_SECTION_ORDER = [
    ("construction", "Construction Rules", "§3.3"),
    ("diagrammatic", "Diagrammatic Axioms", "§3.4"),
    ("metric", "Metric Axioms", "§3.5"),
    ("transfer", "Transfer Axioms", "§3.6"),
    ("superposition", "Superposition", "§3.7"),
    ("proposition", "Propositions", "Book I"),
]

_BADGE_COLORS = {
    "construction": "#2e7d32",
    "diagrammatic": C.scope_bar,
    "metric": "#1565c0",
    "transfer": "#6a1b9a",
    "superposition": "#e65100",
    "proposition": "#6b4c8a",
    "lemma": "#8b5e3c",
}


def _build_rules():
    """Build the rule list from System E axioms via unified_checker."""
    from verifier.unified_checker import get_available_rules
    return get_available_rules()


_RULES = _build_rules()


class RuleReferencePanel(QWidget):
    """Rule catalog reference panel — System E axioms grouped by paper section."""

    def __init__(self, parent=None):
        super().__init__(parent)
        self._lemma_entries = []  # list of (name, description)
        self._sections = {}  # cat -> _SectionGroup
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # ── Header ────────────────────────────────────────────────
        header = QFrame()
        header.setStyleSheet(
            f"background: {C.header_bg};"
            f"border-bottom: 1px solid {C.border};"
        )
        hl = QHBoxLayout(header)
        hl.setContentsMargins(Sp.padding, 10, Sp.padding, 10)
        title = QLabel("Rule Reference")
        title.setFont(Fonts.heading(12))
        title.setStyleSheet(f"color: {C.header_text};")
        hl.addWidget(title)
        hl.addStretch()
        count_lbl = QLabel(f"{len(_RULES)} rules")
        count_lbl.setFont(Fonts.ui(10))
        count_lbl.setStyleSheet(f"color: rgba(255,255,255,0.65);")
        hl.addWidget(count_lbl)
        layout.addWidget(header)

        # ── Search ────────────────────────────────────────────────
        search_frame = QFrame()
        search_frame.setStyleSheet(
            f"background: {C.surface};"
            f"border-bottom: 1px solid {C.border};"
        )
        sf_layout = QHBoxLayout(search_frame)
        sf_layout.setContentsMargins(Sp.padding, 8, Sp.padding, 8)
        self._search = QLineEdit()
        self._search.setPlaceholderText("\U0001f50d  Filter rules\u2026")
        self._search.setClearButtonEnabled(True)
        self._search.setStyleSheet(f"""
            QLineEdit {{
                border: 1px solid {C.border};
                border-radius: 4px;
                padding: 6px 10px;
                font-size: 12px;
                background: {C.bg};
            }}
            QLineEdit:focus {{
                border-color: {C.primary};
            }}
        """)
        self._search.textChanged.connect(self._filter)
        sf_layout.addWidget(self._search)
        layout.addWidget(search_frame)

        # ── Scrollable rule list ──────────────────────────────────
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
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
        self._container.setStyleSheet(f"background: {C.bg};")
        self._container_layout = QVBoxLayout(self._container)
        self._container_layout.setContentsMargins(0, 0, 0, 0)
        self._container_layout.setSpacing(0)
        scroll.setWidget(self._container)
        layout.addWidget(scroll)

        self._build_list()

    # ── Public API for dynamic lemma display ────────────────────────

    def set_lemmas(self, lemmas):
        """Update the lemma entries and rebuild.

        *lemmas* is a list of objects with .display_name(), .schema_text(),
        and .premises / .goal attributes.
        """
        self._lemma_entries = []
        for lem in lemmas:
            prem_str = ", ".join(lem.premises) if lem.premises else "\u2014"
            self._lemma_entries.append(
                (lem.display_name(), f"{prem_str} \u21d2 {lem.goal}"))
        self._build_list(self._search.text())

    # ── Build ───────────────────────────────────────────────────────

    def _build_list(self, filter_text: str = ""):
        # Clear
        while self._container_layout.count():
            w = self._container_layout.takeAt(0).widget()
            if w:
                w.deleteLater()
        self._sections.clear()

        ft = filter_text.lower()

        for cat, section_title, section_ref in _SECTION_ORDER:
            section_rules = [r for r in _RULES if r.category == cat]
            if not section_rules:
                continue

            # Filter rules
            if ft:
                filtered = [r for r in section_rules
                            if ft in r.name.lower()
                            or ft in r.description.lower()
                            or ft in r.category.lower()]
            else:
                filtered = section_rules

            if not filtered:
                continue

            group = _SectionGroup(
                section_title, section_ref, cat,
                len(filtered), len(section_rules),
            )
            self._sections[cat] = group
            self._container_layout.addWidget(group)

            for rule in filtered:
                card = _RuleCard(
                    rule.name, rule.category, rule.section,
                    rule.description,
                )
                group.add_card(card)

        # Lemma section
        if self._lemma_entries:
            lemma_filtered = []
            for lem_name, lem_desc in self._lemma_entries:
                if ft and ft not in lem_name.lower() and ft not in lem_desc.lower():
                    continue
                lemma_filtered.append((lem_name, lem_desc))

            if lemma_filtered:
                group = _SectionGroup(
                    "Lemmas", "", "lemma",
                    len(lemma_filtered), len(self._lemma_entries),
                )
                self._container_layout.addWidget(group)
                for lem_name, lem_desc in lemma_filtered:
                    card = _RuleCard(lem_name, "lemma", "", lem_desc)
                    group.add_card(card)

        self._container_layout.addStretch()

    def _filter(self, text: str):
        self._build_list(text)


# ═══════════════════════════════════════════════════════════════════════
# COLLAPSIBLE SECTION GROUP
# ═══════════════════════════════════════════════════════════════════════

class _SectionGroup(QWidget):
    """Collapsible section with a clickable header and card container."""

    def __init__(
        self, title: str, section_ref: str, category: str,
        visible_count: int, total_count: int, parent=None,
    ):
        super().__init__(parent)
        self._collapsed = False
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # ── Header bar ────────────────────────────────────────────
        self._header = QFrame()
        self._header.setCursor(QCursor(Qt.CursorShape.PointingHandCursor))
        badge_color = _BADGE_COLORS.get(category, C.primary)
        self._header.setStyleSheet(f"""
            QFrame {{
                background: {C.surface};
                border-bottom: 1px solid {C.border};
                border-left: 3px solid {badge_color};
            }}
            QFrame:hover {{
                background: {C.surface_hover};
            }}
        """)
        hdr_layout = QHBoxLayout(self._header)
        hdr_layout.setContentsMargins(Sp.padding, 8, Sp.padding, 8)
        hdr_layout.setSpacing(8)

        # Collapse indicator
        self._arrow = QLabel("\u25BE")  # ▾
        self._arrow.setFont(Fonts.ui(11))
        self._arrow.setStyleSheet(f"color: {C.text_muted};")
        self._arrow.setFixedWidth(14)
        hdr_layout.addWidget(self._arrow)

        # Title
        title_lbl = QLabel(title)
        title_lbl.setFont(Fonts.heading(11))
        title_lbl.setStyleSheet(f"color: {C.text};")
        hdr_layout.addWidget(title_lbl)

        # Section reference
        if section_ref:
            ref_lbl = QLabel(section_ref)
            ref_lbl.setFont(Fonts.ui(10))
            ref_lbl.setStyleSheet(f"color: {C.text_muted};")
            hdr_layout.addWidget(ref_lbl)

        hdr_layout.addStretch()

        # Count badge
        if visible_count < total_count:
            count_text = f"{visible_count}/{total_count}"
        else:
            count_text = str(total_count)
        count_badge = QLabel(count_text)
        count_badge.setFont(Fonts.ui(9))
        count_badge.setStyleSheet(f"""
            background: {C.border};
            color: {C.text_secondary};
            border-radius: 8px;
            padding: 2px 8px;
        """)
        hdr_layout.addWidget(count_badge)

        self._header.mousePressEvent = self._toggle
        layout.addWidget(self._header)

        # ── Card container ────────────────────────────────────────
        self._card_container = QWidget()
        self._card_layout = QVBoxLayout(self._card_container)
        self._card_layout.setContentsMargins(0, 0, 0, 0)
        self._card_layout.setSpacing(0)
        layout.addWidget(self._card_container)

    def add_card(self, card: QWidget):
        self._card_layout.addWidget(card)

    def _toggle(self, event=None):
        self._collapsed = not self._collapsed
        self._card_container.setVisible(not self._collapsed)
        self._arrow.setText("\u25B8" if self._collapsed else "\u25BE")  # ▸ / ▾


# ═══════════════════════════════════════════════════════════════════════
# RULE CARD
# ═══════════════════════════════════════════════════════════════════════

class _RuleCard(QFrame):
    """A single rule display card with proper hover effect."""

    def __init__(self, name: str, category: str, section: str,
                 description: str, parent=None):
        super().__init__(parent)
        self.setObjectName("rule_card")
        self.setStyleSheet(f"""
            QFrame#rule_card {{
                background: {C.surface};
                border-bottom: 1px solid {C.border_light};
            }}
            QFrame#rule_card:hover {{
                background: {C.surface_hover};
            }}
        """)
        layout = QVBoxLayout(self)
        layout.setContentsMargins(Sp.padding + 14, 6, Sp.padding, 6)
        layout.setSpacing(2)

        # Top row: name + category badge
        top = QHBoxLayout()
        top.setSpacing(6)

        nm = QLabel(name)
        nm.setFont(Fonts.ui_bold(11))
        nm.setStyleSheet(f"color: {C.text}; background: transparent;")
        top.addWidget(nm)

        badge_color = _BADGE_COLORS.get(category, C.primary)
        badge = QLabel(category.upper())
        badge.setFont(Fonts.ui(8))
        badge.setFixedHeight(16)
        badge.setStyleSheet(f"""
            background: {badge_color};
            color: white;
            border-radius: 3px;
            padding: 1px 5px;
        """)
        top.addWidget(badge)
        top.addStretch()
        layout.addLayout(top)

        # Description — handle multi-line (propositions have statement + sequent)
        lines = description.split("\n")
        if category == "proposition" and len(lines) >= 2:
            # Line 1: natural language statement
            stmt = QLabel(lines[0])
            stmt.setFont(Fonts.ui(10))
            stmt.setStyleSheet(
                f"color: {C.text_secondary}; background: transparent;"
            )
            stmt.setWordWrap(True)
            layout.addWidget(stmt)
            # Line 2: formal sequent (smaller, muted)
            seq = QLabel(lines[1])
            seq.setFont(Fonts.formula(9))
            seq.setStyleSheet(
                f"color: {C.text_muted}; background: transparent;"
            )
            seq.setWordWrap(True)
            layout.addWidget(seq)
        else:
            desc_lbl = QLabel(description)
            desc_lbl.setFont(Fonts.formula(10))
            desc_lbl.setStyleSheet(
                f"color: {C.text_secondary}; background: transparent;"
            )
            desc_lbl.setWordWrap(True)
            layout.addWidget(desc_lbl)

        self.setToolTip(f"{name} ({category})\n{description}")
