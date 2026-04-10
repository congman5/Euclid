"""
rule_reference.py — Rule catalog sidebar / reference panel.

Sources rules from verifier.unified_checker.get_available_rules(),
which returns System E axioms grouped by paper sections (§3.3–§3.7)
plus proposition theorems from e_library.  Includes a dynamic Lemmas
section, collapsible groups, and search filtering.

Phase 9.4 of the implementation plan.
"""
from __future__ import annotations

import re

from PyQt6.QtCore import Qt, QPropertyAnimation, QEasingCurve, QTimer
from PyQt6.QtGui import QFont, QCursor
from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QLabel, QFrame,
    QScrollArea, QLineEdit, QSizePolicy, QApplication, QPushButton,
)

from .fitch_theme import C, Fonts, Sp

# ── Section ordering (category → display header) ─────────────────────

_SECTION_ORDER = [
    ("construction", "Construction Rules", "§3.3"),
    ("diagrammatic", "Diagrammatic Axioms", "§3.4"),
    ("metric", "Metric Axioms", "§3.5"),
    ("transfer", "Transfer Axioms", "§3.6"),
    ("superposition", "Superposition", "§3.7"),
    ("structural", "Structural Rules", "§3.2"),
    ("proposition", "Propositions", "Book I"),
]

_BADGE_COLORS = {
    "construction": "#2e7d32",
    "diagrammatic": C.scope_bar,
    "metric": "#1565c0",
    "transfer": "#6a1b9a",
    "superposition": "#e65100",
    "structural": "#546e7a",
    "proposition": "#6b4c8a",
    "lemma": "#8b5e3c",
}


def _build_rules():
    """Build the rule list from System E axioms via unified_checker."""
    from verifier.unified_checker import get_available_rules
    return get_available_rules()


_RULES = _build_rules()

# ── Predicate matching for "applicable rules" filter ──────────────────

# Predicate names that appear in System E axiom descriptions.
_PRED_RE = re.compile(
    r'(?:on|center|inside|between|same-side|intersects|¬on|¬center'
    r'|¬inside|¬between|¬same-side|¬intersects)\s*\(')

# Metric patterns: segment equality/order, angle, area, right-angle
_METRIC_RE = re.compile(
    r'(?:[a-z][a-z]?\s*[+]?\s*[a-z][a-z]?\s*[=<]'  # ab = cd, ab < cd
    r'|∠[a-z]+\s*[=<]'                               # ∠abc = ...
    r'|△[a-z]+\s*[=≠]'                               # △abc = 0
    r'|∟)')                                           # right-angle


def _extract_pred_names(text: str) -> set[str]:
    """Extract predicate functor names from a description string.

    Returns a set like {"on", "between", "same-side", "≠"} representing
    the kinds of predicates that appear in the hypothesis portion.
    """
    names: set[str] = set()
    for m in _PRED_RE.finditer(text):
        token = m.group(0).rstrip("( ")
        # Strip leading ¬ — ¬on still means the rule involves "on"
        if token.startswith("¬"):
            token = token[1:]
        names.add(token)
    # Detect equality / inequality
    if "≠" in text:
        names.add("≠")
    if _METRIC_RE.search(text):
        names.add("metric")
    return names


def _extract_pred_names_from_fact(fact: str) -> set[str]:
    """Extract predicate names from a single proof fact string."""
    names: set[str] = set()
    names.update(_extract_pred_names(fact))
    # Also catch bare equality like "a = b" or "L = M"
    if "≠" in fact:
        names.add("≠")
    if re.search(r'[a-zA-Zα-ωΑ-Ω]\s*=\s*[a-zA-Zα-ωΑ-Ω]', fact):
        names.add("=")
    return names


def _rule_is_applicable(description: str, proof_facts: set[str]) -> bool:
    """Return True if a rule's hypotheses overlap with known proof facts.

    Extracts predicate functors from the hypothesis side (left of ⇒) of
    the rule description and checks if any match functors found in the
    proof's known facts.  Construction rules (which introduce new objects)
    and structural rules are always shown.
    """
    # Construction and structural rules are always applicable
    if "⊢" in description or "Γ" in description:
        return True

    # Split on ⇒ to get hypotheses only
    parts = description.split("⇒")
    if len(parts) < 2:
        # No implication arrow — show it (e.g. construction rules)
        return True
    hypothesis = parts[0]

    rule_preds = _extract_pred_names(hypothesis)
    if not rule_preds:
        return True  # Can't parse — show it

    # Build the set of predicate names present in proof facts
    fact_preds: set[str] = set()
    for fact in proof_facts:
        fact_preds.update(_extract_pred_names_from_fact(fact))

    # Rule is applicable if ANY hypothesis predicate matches a known fact
    return bool(rule_preds & fact_preds)


class RuleReferencePanel(QWidget):
    """Rule catalog reference panel — System E axioms grouped by paper section."""

    def __init__(self, parent=None):
        super().__init__(parent)
        self._lemma_entries = []  # list of (name, description)
        self._sections = {}  # cat -> _SectionGroup
        self._proof_facts: set[str] = set()  # known predicates from proof
        self._applicable_active = False
        self._facts_provider = None  # callable returning set[str]
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
        self._count_lbl = count_lbl
        hl.addWidget(count_lbl)
        layout.addWidget(header)

        # ── Search + Applicable toggle ────────────────────────────
        search_frame = QFrame()
        search_frame.setStyleSheet(
            f"background: {C.surface};"
            f"border-bottom: 1px solid {C.border};"
        )
        sf_layout = QHBoxLayout(search_frame)
        sf_layout.setContentsMargins(Sp.padding, 8, Sp.padding, 8)
        sf_layout.setSpacing(6)
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

        self._applicable_btn = QPushButton("\u2714 Applicable")
        self._applicable_btn.setCheckable(True)
        self._applicable_btn.setFont(Fonts.ui(9))
        self._applicable_btn.setCursor(
            QCursor(Qt.CursorShape.PointingHandCursor))
        self._applicable_btn.setToolTip(
            "Show only rules whose hypotheses match known proof facts")
        self._applicable_btn.setStyleSheet(f"""
            QPushButton {{
                border: 1px solid {C.border};
                border-radius: 4px;
                padding: 4px 10px;
                font-size: 11px;
                background: {C.bg};
                color: {C.text_secondary};
            }}
            QPushButton:hover {{
                background: {C.surface_hover};
                border-color: {C.primary};
            }}
            QPushButton:checked {{
                background: {C.primary};
                color: white;
                border-color: {C.primary};
            }}
        """)
        self._applicable_btn.toggled.connect(self._on_applicable_toggled)
        sf_layout.addWidget(self._applicable_btn)
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

    # ── Public API for applicable-rules filtering ───────────────────

    def set_facts_provider(self, provider):
        """Register a callable that returns the current proof facts.

        *provider* is a no-arg callable returning ``set[str]``.
        Called eagerly whenever the applicable filter needs fresh data.
        """
        self._facts_provider = provider

    def set_proof_facts(self, facts: set[str]):
        """Update the set of known proof predicates.

        *facts* is a set of predicate strings from the proof panel,
        e.g. {"on(a,L)", "between(a,b,c)", "a ≠ b"}.
        Only triggers a rebuild when the applicable filter is active.
        """
        if facts == self._proof_facts:
            return
        self._proof_facts = facts
        if self._applicable_active:
            self._build_list(self._search.text())

    def _refresh_facts(self):
        """Pull fresh facts from the provider if available."""
        if self._facts_provider is not None:
            self._proof_facts = self._facts_provider()

    def _on_applicable_toggled(self, checked: bool):
        self._applicable_active = checked
        if checked:
            self._refresh_facts()
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
        total_shown = 0

        for cat, section_title, section_ref in _SECTION_ORDER:
            section_rules = [r for r in _RULES if r.category == cat]
            if not section_rules:
                continue

            # Text filter
            if ft:
                filtered = [r for r in section_rules
                            if ft in r.name.lower()
                            or ft in r.description.lower()
                            or ft in r.category.lower()]
            else:
                filtered = section_rules

            # Applicable filter
            if self._applicable_active and self._proof_facts:
                filtered = [r for r in filtered
                            if _rule_is_applicable(r.description,
                                                   self._proof_facts)]

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
            total_shown += len(filtered)

        # Lemma section
        if self._lemma_entries:
            lemma_filtered = []
            for lem_name, lem_desc in self._lemma_entries:
                if ft and ft not in lem_name.lower() and ft not in lem_desc.lower():
                    continue
                if (self._applicable_active and self._proof_facts
                        and not _rule_is_applicable(lem_desc,
                                                    self._proof_facts)):
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
                total_shown += len(lemma_filtered)

        self._container_layout.addStretch()

        # Update header counter
        if self._applicable_active or ft:
            self._count_lbl.setText(f"{total_shown}/{len(_RULES)} rules")
        else:
            self._count_lbl.setText(f"{len(_RULES)} rules")

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
        self._collapsed = True
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
                border-left: 4px solid {badge_color};
            }}
            QFrame:hover {{
                background: {C.surface_hover};
            }}
        """)
        hdr_layout = QHBoxLayout(self._header)
        hdr_layout.setContentsMargins(16, 8, Sp.padding, 8)
        hdr_layout.setSpacing(8)

        # Collapse indicator
        self._arrow = QLabel("\u25B8")  # ▸ (starts collapsed)
        self._arrow.setFont(Fonts.ui(11))
        self._arrow.setStyleSheet(
            f"color: {C.text_muted}; background: transparent;"
            f" border: none;"
        )
        self._arrow.setFixedWidth(14)
        hdr_layout.addWidget(self._arrow)

        # Title
        title_lbl = QLabel(title)
        title_lbl.setFont(Fonts.heading(11))
        title_lbl.setStyleSheet(
            f"color: {C.text}; background: transparent;"
            f" border: none;"
        )
        hdr_layout.addWidget(title_lbl)

        # Section reference — styled pill so it doesn't run into the title
        if section_ref:
            ref_lbl = QLabel(section_ref)
            ref_lbl.setFont(Fonts.ui(9))
            ref_lbl.setStyleSheet(f"""
                color: {C.text_muted};
                background: {C.bg};
                border: 1px solid {C.border};
                border-radius: 3px;
                padding: 1px 6px;
            """)
            hdr_layout.addWidget(ref_lbl)

        hdr_layout.addStretch()

        # Count badge
        if visible_count < total_count:
            count_text = f"{visible_count}/{total_count}"
        else:
            count_text = str(total_count)
        count_badge = QLabel(count_text)
        count_badge.setFont(Fonts.ui(9))
        count_badge.setAlignment(Qt.AlignmentFlag.AlignCenter)
        count_badge.setMinimumWidth(28)
        count_badge.setFixedHeight(20)
        count_badge.setStyleSheet(f"""
            background: {badge_color};
            color: white;
            border: none;
            border-radius: 10px;
            padding: 0px 8px;
        """)
        hdr_layout.addWidget(count_badge)

        self._header.mousePressEvent = self._toggle
        layout.addWidget(self._header)

        # ── Card container ────────────────────────────────────────
        self._card_container = QWidget()
        self._card_container.setVisible(False)
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
    """A single rule display card — click to copy rule name."""

    def __init__(self, name: str, category: str, section: str,
                 description: str, parent=None):
        super().__init__(parent)
        self._rule_name = name
        self.setObjectName("rule_card")
        self.setCursor(QCursor(Qt.CursorShape.PointingHandCursor))
        self._default_style = f"""
            QFrame#rule_card {{
                background: {C.surface};
                border-bottom: 1px solid {C.border_light};
            }}
            QFrame#rule_card:hover {{
                background: {C.surface_hover};
            }}
        """
        self._copied_style = f"""
            QFrame#rule_card {{
                background: {C.primary_light};
                border-bottom: 1px solid {C.primary};
            }}
        """
        self.setStyleSheet(self._default_style)
        badge_color = _BADGE_COLORS.get(category, C.primary)

        layout = QVBoxLayout(self)
        layout.setContentsMargins(20, 6, Sp.padding, 6)
        layout.setSpacing(3)

        # Top row: letter badge + name + section ref
        top = QHBoxLayout()
        top.setSpacing(6)

        _CAT_LETTERS = {
            "construction": "C",
            "diagrammatic": "D",
            "metric": "M",
            "transfer": "T",
            "superposition": "S",
            "proposition": "P",
            "lemma": "L",
        }
        letter = _CAT_LETTERS.get(category, "?")
        badge = QLabel(letter)
        badge.setFont(Fonts.ui(8))
        badge.setFixedWidth(18)
        badge.setFixedHeight(18)
        badge.setAlignment(Qt.AlignmentFlag.AlignCenter)
        badge.setStyleSheet(
            f"background: {badge_color}; color: white;"
            f" border-radius: 3px; font-weight: bold;"
        )
        top.addWidget(badge)

        nm = QLabel(name)
        nm.setFont(Fonts.ui_bold(10))
        nm.setStyleSheet(f"color: {C.text}; background: transparent;")
        top.addWidget(nm)

        if section:
            sec_lbl = QLabel(section)
            sec_lbl.setFont(Fonts.ui(8))
            sec_lbl.setStyleSheet(
                f"color: {C.text_muted}; background: transparent;"
            )
            top.addWidget(sec_lbl)

        top.addStretch()
        layout.addLayout(top)

        # Description — handle multi-line (propositions have statement + sequent)
        lines = description.split("\n")
        if category == "proposition" and len(lines) >= 2:
            # Line 1: natural language statement
            stmt = QLabel(lines[0])
            stmt.setFont(Fonts.ui(10))
            stmt.setStyleSheet(
                f"color: {C.text}; background: transparent;"
                f" padding-left: 24px;"
            )
            stmt.setWordWrap(True)
            layout.addWidget(stmt)
            # Line 2+: formal sequent (smaller, muted)
            seq = QLabel("\n".join(lines[1:]))
            seq.setFont(Fonts.formula(9))
            seq.setStyleSheet(
                f"color: {C.text_muted}; background: transparent;"
                f" padding-left: 24px;"
            )
            seq.setWordWrap(True)
            layout.addWidget(seq)
        else:
            desc_lbl = QLabel(description)
            desc_lbl.setFont(Fonts.ui(10))
            desc_lbl.setStyleSheet(
                f"color: {C.text}; background: transparent;"
                f" padding-left: 24px;"
            )
            desc_lbl.setWordWrap(True)
            layout.addWidget(desc_lbl)

        self.setToolTip(f"Click to copy \u2022 {name} ({category})\n{description}")

    def mousePressEvent(self, event):
        """Copy rule name to clipboard and show brief visual feedback."""
        if event.button() == Qt.MouseButton.LeftButton:
            clipboard = QApplication.clipboard()
            if clipboard:
                clipboard.setText(self._rule_name)
            self.setStyleSheet(self._copied_style)
            QTimer.singleShot(400, lambda: self.setStyleSheet(self._default_style))
        super().mousePressEvent(event)
