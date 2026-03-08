"""
translation_view.py — Read-only E / T / H Translation View.

Shows the same theorem in all three formal notations side-by-side:
  System E (primary), System T (Tarski bridge), System H (Hilbert).

Each system card formats hypotheses and conclusions on separate lines
with human-readable annotations (e.g. "point a lies on line L") so
the formal notation is easier to understand.

This is a **display** feature, not a verification path.
Phase 9.3 of the implementation plan.
"""
from __future__ import annotations

from PyQt6.QtCore import Qt, pyqtSignal
from PyQt6.QtGui import QCursor, QFont
from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QLabel, QFrame,
    QScrollArea, QPushButton,
)

from .fitch_theme import C, Fonts, Sp


# ── Badge colours for each system ─────────────────────────────────────

_SYSTEM_COLORS = {
    "E": "#2d70b3",   # blue   (matches proof panel)
    "T": "#7b3fa0",   # purple (matches proof panel)
    "H": "#c06020",   # orange (matches proof panel)
}

# ── Tint backgrounds per system (very light) ─────────────────────────

_SYSTEM_TINTS = {
    "E": "#f0f4fc",   # light blue tint
    "T": "#f6f0fa",   # light purple tint
    "H": "#fdf5ef",   # light orange tint
}

# ── Human-readable annotations for E predicates ──────────────────────

_E_ANNOTATIONS = {
    "on":        "lies on",
    "between":   "is strictly between",
    "same-side": "is on the same side of",
    "center":    "is the centre of",
    "inside":    "is inside",
    "intersects": "intersects",
}

_T_ANNOTATIONS = {
    "B":        "is between (nonstrict)",
    "Cong":     "is equidistant to",
    "Eq":       "equals",
    "Neq":      "is distinct from",
    "NotB":     "is not between",
    "NotCong":  "is not equidistant to",
}

_H_ANNOTATIONS = {
    "IncidL":   "lies on line",
    "IncidP":   "lies on plane",
    "BetH":     "is strictly between",
    "CongH":    "is congruent (segment)",
    "CongaH":   "is congruent (angle)",
    "ColH":     "are collinear",
    "EqPt":     "equals (point)",
    "EqL":      "equals (line)",
    "Para":     "is parallel to",
}


def _humanize(literal_text: str) -> str:
    """Translate a single formal literal into readable English.

    Examples::

        on(a, L)              →  point a lies on line L
        between(a, b, c)      →  b is strictly between a and c
        ab = cd               →  segment ab = segment cd
        ∠abc = ∠def           →  angle ∠abc = angle ∠def
        △abc = △def           →  area △abc = area △def
        ¬(a = b)              →  a ≠ b
        same-side(a, b, L)    →  a, b are on the same side of L
        intersects(L, M)      →  L and M intersect
        ¬intersects(L, M)     →  L ∥ M  (do not intersect)
        right-angle           →  a right angle
        Cong(a,b,c,d)         →  ab ≅ cd
        B(a,b,c)              →  b is between a and c
        Neq(a,b) / a ≠ b     →  a ≠ b
        CongH(a,b,c,d)        →  ab ≅ cd
        BetH(a,b,c)           →  b is between a and c
        IncidL(a,l)           →  point a lies on line l
        CongaH(a,b,c,d,e,f)  →  ∠abc ≅ ∠def
        ColH(a,b,c)           →  a, b, c are collinear
        Para(l,m)             →  l ∥ m
    """
    import re
    s = literal_text.strip()

    # ── Negations ─────────────────────────────────────────────────
    # ¬(a = b)  →  a ≠ b
    m = re.match(r"[¬!]?\(?¬\(?\s*(\w+)\s*=\s*(\w+)\s*\)?\)?$", s)
    if not m:
        m = re.match(r"¬\(\s*(\w+)\s*=\s*(\w+)\s*\)$", s)
    if m:
        return f"{m.group(1)} ≠ {m.group(2)}"

    # ¬intersects(X, Y) or ¬(intersects(X, Y))  →  X ∥ Y (parallel)
    m = re.match(r"¬\(?intersects\(\s*(\w+)\s*,\s*(\w+)\s*\)\)?$", s)
    if m:
        return f"{m.group(1)} ∥ {m.group(2)}  (parallel)"

    # ¬(ColH(a,b,c))  →  a, b, c form a proper triangle
    m = re.match(r"¬\(\s*ColH\(\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*\)\s*\)$", s)
    if m:
        return f"{m.group(1)}, {m.group(2)}, {m.group(3)} form a triangle  (non-collinear)"

    # ¬(same-side(a, b, L))  →  a, b are NOT on the same side of L
    m = re.match(r"¬\(\s*same-side\(\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*\)\s*\)$", s)
    if m:
        return f"{m.group(1)}, {m.group(2)} are on opposite sides of {m.group(3)}"

    # General ¬(X)  →  not X  (recurse on inner)
    m = re.match(r"¬\(\s*(.+)\s*\)$", s)
    if m:
        inner = _humanize(m.group(1))
        return f"not ({inner})"

    # ── System E predicates ───────────────────────────────────────
    # on(a, L)
    m = re.match(r"on\(\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"point {m.group(1)} lies on {m.group(2)}"

    # between(a, b, c)
    m = re.match(r"between\(\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"{m.group(2)} is strictly between {m.group(1)} and {m.group(3)}"

    # same-side(a, b, L)
    m = re.match(r"same-side\(\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"{m.group(1)}, {m.group(2)} are on the same side of {m.group(3)}"

    # diff-side(a, b, L)
    m = re.match(r"diff-side\(\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"{m.group(1)}, {m.group(2)} are on opposite sides of {m.group(3)}"

    # center(a, α)
    m = re.match(r"center\(\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"{m.group(1)} is the centre of circle {m.group(2)}"

    # inside(a, α)
    m = re.match(r"inside\(\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"{m.group(1)} is inside circle {m.group(2)}"

    # intersects(X, Y)
    m = re.match(r"intersects\(\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"{m.group(1)} and {m.group(2)} intersect"

    # right-angle (bare constant)
    if s == "right-angle":
        return "a right angle"

    # ── Metric: ∠abc = ∠def / ∠abc < ∠def ────────────────────────
    m = re.match(r"(∠\w+)\s*=\s*right-angle$", s)
    if m:
        return f"{m.group(1)} is a right angle"

    m = re.match(r"(∠\w+)\s*([=<>])\s*(∠\w+)$", s)
    if m:
        op = {"=": "=", "<": "<", ">": ">"}[m.group(2)]
        return f"angle {m.group(1)} {op} angle {m.group(3)}"

    # ── Metric: △abc = △def ───────────────────────────────────────
    m = re.match(r"(△\w+)\s*=\s*(△\w+)$", s)
    if m:
        return f"area {m.group(1)} = area {m.group(2)}"

    # ── Metric: magnitude addition (△X + △Y) = (△Z + △W) ────────
    if "△" in s and "+" in s:
        return f"{s}  (area sum)"

    # ── Metric: segment ab = cd / ab < cd ─────────────────────────
    # Match patterns like "ab = cd", "ab < cd"
    m = re.match(r"(\w{2,})\s*([=<>])\s*(\w{2,})$", s)
    if m:
        left, op, right = m.group(1), m.group(2), m.group(3)
        # Only treat as segment equality if both sides look like
        # 2-letter point-pair names (lowercase)
        if len(left) == 2 and len(right) == 2:
            op_word = {"=": "≅", "<": "<", ">": ">"}[op]
            return f"segment {left} {op_word} segment {right}"

    # ── Point equality: a = b ─────────────────────────────────────
    m = re.match(r"(\w+)\s*=\s*(\w+)$", s)
    if m:
        left, right = m.group(1), m.group(2)
        if len(left) == 1 and len(right) == 1:
            return f"{left} = {right}  (same point)"
        return f"{left} = {right}"

    # ── System T predicates ───────────────────────────────────────
    # Cong(a,b,c,d) → segment ab ≅ segment cd
    m = re.match(r"Cong\(\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return (f"segment {m.group(1)}{m.group(2)} ≅ "
                f"segment {m.group(3)}{m.group(4)}")

    # B(a,b,c) → b is between a and c
    m = re.match(r"B\(\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"{m.group(2)} is between {m.group(1)} and {m.group(3)}"

    # Eq(a,b) → a = b
    m = re.match(r"Eq\(\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"{m.group(1)} = {m.group(2)}"

    # Neq(a,b) / a ≠ b
    m = re.match(r"Neq\(\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"{m.group(1)} ≠ {m.group(2)}"
    m = re.match(r"(\w+)\s*≠\s*(\w+)$", s)
    if m:
        return f"{m.group(1)} ≠ {m.group(2)}"

    # NotB(a,b,c) → b is NOT between a and c
    m = re.match(r"NotB\(\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"{m.group(2)} is not between {m.group(1)} and {m.group(3)}"

    # NotCong(a,b,c,d) → segment ab ≇ segment cd
    m = re.match(r"NotCong\(\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return (f"segment {m.group(1)}{m.group(2)} ≇ "
                f"segment {m.group(3)}{m.group(4)}")

    # ── System H predicates ───────────────────────────────────────
    # IncidL(a, l) → point a lies on line l
    m = re.match(r"IncidL\(\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"point {m.group(1)} lies on line {m.group(2)}"

    # BetH(a,b,c) → b is between a and c
    m = re.match(r"BetH\(\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"{m.group(2)} is between {m.group(1)} and {m.group(3)}"

    # CongH(a,b,c,d) → segment ab ≅ segment cd
    m = re.match(r"CongH\(\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return (f"segment {m.group(1)}{m.group(2)} ≅ "
                f"segment {m.group(3)}{m.group(4)}")

    # CongaH(a,b,c,d,e,f) → ∠abc ≅ ∠def
    m = re.match(
        r"CongaH\(\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*,"
        r"\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return (f"∠{m.group(1)}{m.group(2)}{m.group(3)} ≅ "
                f"∠{m.group(4)}{m.group(5)}{m.group(6)}")

    # ColH(a,b,c) → a, b, c are collinear
    m = re.match(r"ColH\(\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"{m.group(1)}, {m.group(2)}, {m.group(3)} are collinear"

    # SameSideH(a,b,l) → a, b on same side of l
    m = re.match(r"SameSideH\(\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"{m.group(1)}, {m.group(2)} are on the same side of {m.group(3)}"

    # Para(l, m) → l ∥ m
    m = re.match(r"Para\(\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"{m.group(1)} ∥ {m.group(2)}  (parallel)"

    # EqPt(a,b) → a = b
    m = re.match(r"EqPt\(\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"{m.group(1)} = {m.group(2)}  (same point)"

    # EqL(l,m) → l = m
    m = re.match(r"EqL\(\s*(\w+)\s*,\s*(\w+)\s*\)$", s)
    if m:
        return f"{m.group(1)} = {m.group(2)}  (same line)"

    # ── Fallback: return as-is ────────────────────────────────────
    return s


def _humanize_exists(exist_prefix: str) -> str:
    """Rewrite an existential prefix into plain English.

    Input:  ``∃c:POINT, d:POINT.``
    Output: ``there exist points c, d such that``
    """
    import re
    # Strip the leading ∃ and trailing dot
    body = exist_prefix.strip()
    if body.startswith("∃"):
        body = body[1:]
    body = body.rstrip(".")

    vars_by_sort: dict[str, list[str]] = {}
    for part in body.split(","):
        part = part.strip()
        if ":" in part:
            name, sort = part.split(":", 1)
            sort = sort.strip()
        else:
            name, sort = part, "POINT"
        name = name.strip()
        # Filter out internal pi-variables
        if name.startswith("_pi_"):
            continue
        vars_by_sort.setdefault(sort, []).append(name)

    if not vars_by_sort:
        return ""

    chunks = []
    _SORT_NAMES = {
        "POINT": ("point", "points"),
        "LINE": ("line", "lines"),
        "CIRCLE": ("circle", "circles"),
    }
    for sort, names in vars_by_sort.items():
        singular, plural = _SORT_NAMES.get(sort, (sort.lower(), sort.lower() + "s"))
        word = plural if len(names) > 1 else singular
        chunks.append(f"{word} {', '.join(names)}")

    return "there exist " + " and ".join(chunks) + " such that"


def _format_sequent_lines(sequent_text: str) -> str:
    """Break a sequent string into readable, humanized lines.

    Input looks like:
        hyp1, hyp2, ... ⇒ ∃vars. conc1, conc2
    Output:
        <b>Given:</b>
          • hyp1 in English
          • hyp2 in English
        <b>Then there exist points c, d such that:</b>
          • conc1 in English
          • conc2 in English
    """
    text = sequent_text.strip()

    # Split on the sequent arrow ⇒
    if "\u21d2" in text:
        left, right = text.split("\u21d2", 1)
    elif "=>" in text:
        left, right = text.split("=>", 1)
    else:
        # No arrow — just display the whole thing
        return text

    left = left.strip()
    right = right.strip()

    # Parse existential prefix from the conclusion side
    exist_prefix = ""
    concl_body = right
    if right.startswith("\u2203"):
        # ∃x:POINT, y:POINT. concl1, concl2
        dot_idx = right.find(".")
        if dot_idx >= 0:
            exist_prefix = right[:dot_idx + 1].strip()
            concl_body = right[dot_idx + 1:].strip()

    # Split hypotheses and conclusions on top-level commas
    hyps = _split_top_level(left) if left and left != "\u2014" else []
    concs = _split_top_level(concl_body) if concl_body else []

    lines = []
    if hyps:
        lines.append("<b>Given:</b>")
        for h in hyps:
            lines.append(f"  \u2022 {_humanize(h.strip())}")
    if concs:
        if exist_prefix:
            human_exists = _humanize_exists(exist_prefix)
            if human_exists:
                lines.append(f"<b>Then {human_exists}:</b>")
            else:
                lines.append("<b>Prove:</b>")
        else:
            lines.append("<b>Prove:</b>")
        for c in concs:
            lines.append(f"  \u2022 {_humanize(c.strip())}")
    return "\n".join(lines)


def _split_top_level(s: str) -> list[str]:
    """Split on commas not inside parentheses."""
    parts = []
    depth = 0
    cur = []
    for ch in s:
        if ch in ("(", "["):
            depth += 1
            cur.append(ch)
        elif ch in (")", "]"):
            depth -= 1
            cur.append(ch)
        elif ch == "," and depth == 0:
            parts.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    if cur:
        parts.append("".join(cur))
    return [p for p in parts if p.strip()]


class TranslationView(QWidget):
    """Read-only panel showing E / T / H notations for one proposition.

    Emits ``system_selected(str)`` when the user clicks a system badge,
    allowing the proof panel to switch notation.
    """

    system_selected = pyqtSignal(str)  # "E", "T", or "H"

    def __init__(self, parent=None):
        super().__init__(parent)
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
        title = QLabel("E / T / H Translation View")
        title.setFont(Fonts.heading(12))
        title.setStyleSheet(
            f"color: {C.header_text}; background: transparent;"
        )
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
        self._container.setStyleSheet(f"background: {C.bg};")
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
        title.setFont(Fonts.heading(14))
        title.setStyleSheet(
            f"color: {C.text}; background: transparent;"
            f" padding: 14px {Sp.padding}px 4px {Sp.padding}px;"
        )
        self._container_layout.addWidget(title)

        # Statement (natural language)
        stmt = ""
        if e_thm is not None:
            stmt = getattr(e_thm, 'statement', '') or ''
        if stmt:
            stmt_lbl = QLabel(stmt)
            stmt_lbl.setFont(Fonts.ui(10))
            stmt_lbl.setWordWrap(True)
            stmt_lbl.setStyleSheet(
                f"color: {C.text_secondary}; background: transparent;"
                f" padding: 0px {Sp.padding}px 10px {Sp.padding}px;"
                f" font-style: italic;"
            )
            self._container_layout.addWidget(stmt_lbl)

        # System E
        if e_thm is not None:
            e_text = str(e_thm.sequent)
            self._add_system_card(
                "E", "System E (Euclid)", e_text,
                "The primary proof language from Avigad, Dean & Mumma (2009)."
            )

            # System T — translate via π
            t_text = self._translate_to_t(e_thm.sequent)
            if t_text:
                self._add_system_card(
                    "T", "System T (Tarski)", t_text,
                    "Tarski\u2019s axioms \u2014 uses only points with "
                    "betweenness (B) and equidistance (\u2261)."
                )

        # System H
        if h_thm is not None:
            h_text = str(h_thm.sequent)
            self._add_system_card(
                "H", "System H (Hilbert)", h_text,
                "Hilbert\u2019s axioms from the Grundlagen der Geometrie."
            )

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
        text = msg or "Select a proposition to see E / T / H translations."
        lbl = QLabel(text)
        lbl.setFont(Fonts.ui(11))
        lbl.setStyleSheet(
            f"color: {C.text_muted}; background: transparent;"
            f" padding: 24px; font-style: italic;"
        )
        lbl.setWordWrap(True)
        lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._container_layout.addWidget(lbl)
        self._container_layout.addStretch()

    def _add_system_card(
        self, system_key: str, label: str, sequent_text: str,
        subtitle: str = "",
    ):
        """Add one system card with structured layout."""
        card = QFrame()
        card.setObjectName("system_card")
        badge_color = _SYSTEM_COLORS.get(system_key, C.primary)
        tint = _SYSTEM_TINTS.get(system_key, C.surface)
        card.setStyleSheet(f"""
            QFrame#system_card {{
                background: {C.surface};
                border-left: 4px solid {badge_color};
                margin: 6px {Sp.padding}px;
                border-radius: 6px;
                border: 1px solid {C.border_light};
                border-left: 4px solid {badge_color};
            }}
        """)
        vl = QVBoxLayout(card)
        vl.setContentsMargins(14, 10, 12, 10)
        vl.setSpacing(4)

        # Top row: badge + system label
        top = QHBoxLayout()
        top.setSpacing(8)

        badge = QPushButton(system_key)
        badge.setFont(Fonts.ui(9))
        badge.setFixedHeight(22)
        badge.setFixedWidth(28)
        badge.setCursor(QCursor(Qt.CursorShape.PointingHandCursor))
        badge.setToolTip(f"Switch proof to {label} notation")
        badge.setStyleSheet(
            f"QPushButton{{background:{badge_color};color:white;border:none;"
            f"border-radius:3px;font-weight:bold;font-size:11px;"
            f"padding:0px;}}"
            f"QPushButton:hover{{background:{C.text};}}"
        )
        badge.clicked.connect(
            lambda _, sk=system_key: self.system_selected.emit(sk))
        top.addWidget(badge)

        sys_label = QLabel(label)
        sys_label.setFont(Fonts.heading(11))
        sys_label.setStyleSheet(
            f"color: {C.text}; background: transparent;"
        )
        top.addWidget(sys_label)
        top.addStretch()
        vl.addLayout(top)

        # Subtitle (system description)
        if subtitle:
            sub_lbl = QLabel(subtitle)
            sub_lbl.setFont(Fonts.ui(9))
            sub_lbl.setWordWrap(True)
            sub_lbl.setStyleSheet(
                f"color: {C.text_muted}; background: transparent;"
                f" padding-left: 32px;"
            )
            vl.addWidget(sub_lbl)

        # Structured sequent display
        formatted = _format_sequent_lines(sequent_text)
        seq = QLabel(formatted)
        seq.setFont(Fonts.formula(10))
        seq.setStyleSheet(f"""
            color: {C.text};
            padding: 8px 10px;
            background: {tint};
            border: 1px solid {C.border_light};
            border-radius: 4px;
            line-height: 1.5;
        """)
        seq.setWordWrap(True)
        seq.setTextFormat(Qt.TextFormat.RichText)
        seq.setTextInteractionFlags(
            Qt.TextInteractionFlag.TextSelectableByMouse
        )
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


# ═══════════════════════════════════════════════════════════════════════
# GLOSSARY PANEL — Primitives reference
# ═══════════════════════════════════════════════════════════════════════

# Each entry: (formal, english, example)
_E_GLOSSARY = [
    ("on(a, L)",           "Point a lies on line L",
     "on(a, L)"),
    ("on(a, \u03b1)",      "Point a lies on circle \u03b1",
     "on(a, \u03b1)"),
    ("between(a, b, c)",   "b is strictly between a and c on a line",
     "between(a, b, c)"),
    ("same-side(a, b, L)", "a and b are on the same side of line L",
     "same-side(p, q, L)"),
    ("diff-side(a, b, L)", "a and b are on opposite sides of line L",
     "diff-side(p, q, L)"),
    ("center(a, \u03b1)",  "Point a is the centre of circle \u03b1",
     "center(a, \u03b1)"),
    ("inside(a, \u03b1)",  "Point a is inside circle \u03b1",
     "inside(a, \u03b1)"),
    ("intersects(L, \u03b1)", "Line L intersects circle \u03b1",
     "intersects(L, \u03b1)"),
    ("\u00acintersects(L, \u03b1)", "Line L does not intersect circle \u03b1",
     "\u00acintersects(L, \u03b1)"),
    ("right-angle",        "A right angle (90\u00b0)",
     "\u2220abc = right-angle"),
    ("let L = line(a, b)", "Construct the line through a and b",
     "let L be line(a, b)"),
    ("let \u03b1 = circle(a, b)", "Construct circle centred a through b",
     "let \u03b1 be circle(a, b)"),
    ("ab = cd",            "Segment ab equals segment cd",
     "ab = cd"),
    ("ab < cd",            "Segment ab is shorter than segment cd",
     "ab < cd"),
    ("ab + bc = ac",       "Segment addition",
     "ab + bc = ac"),
    ("\u2220abc = \u2220def", "Angle abc equals angle def",
     "\u2220abc = \u2220def"),
    ("\u2220abc < \u2220def", "Angle abc is less than angle def",
     "\u2220abc < \u2220def"),
    ("\u25b3abc = \u25b3def", "Area of triangle abc equals area of triangle def",
     "\u25b3abc = \u25b3def"),
    ("\u00ac(a = b)",       "Points a and b are distinct (a \u2260 b)",
     "\u00ac(a = b)"),
]

_T_GLOSSARY = [
    ("B(a, b, c)",         "b is between a and c (nonstrict \u2014 allows a=b or b=c)",
     "B(a, b, c)"),
    ("Cong(a, b, c, d)",   "Segment ab is congruent to segment cd (ab \u2261 cd)",
     "Cong(a, b, c, d)"),
    ("Eq(a, b)",           "Point a equals point b",
     "Eq(a, b)"),
    ("Neq(a, b)",          "Point a is distinct from point b (a \u2260 b)",
     "Neq(a, b)"),
    ("NotB(a, b, c)",      "b is NOT between a and c",
     "NotB(a, b, c)"),
    ("NotCong(a, b, c, d)","Segment ab is NOT congruent to segment cd",
     "NotCong(a, b, c, d)"),
]

_H_GLOSSARY = [
    ("IncidL(a, l)",       "Point a lies on line l (incidence)",
     "IncidL(a, l)"),
    ("BetH(a, b, c)",      "b is strictly between a and c",
     "BetH(a, b, c)"),
    ("CongH(a, b, c, d)",  "Segment ab is congruent to segment cd",
     "CongH(a, b, c, d)"),
    ("CongaH(a, b, c, d, e, f)",
     "Angle \u2220abc is congruent to angle \u2220def",
     "CongaH(a, b, c, d, e, f)"),
    ("ColH(a, b, c)",      "Points a, b, c are collinear",
     "ColH(a, b, c)"),
    ("EqPt(a, b)",         "Point a equals point b",
     "EqPt(a, b)"),
    ("EqL(l, m)",          "Line l equals line m",
     "EqL(l, m)"),
    ("Para(l, m)",         "Line l is parallel to line m",
     "Para(l, m)"),
    ("SameSideH(a, b, l)", "a and b are on the same side of line l",
     "SameSideH(a, b, l)"),
]


class GlossaryPanel(QWidget):
    """Reference panel explaining every primitive in Systems E, T, and H."""

    def __init__(self, parent=None):
        super().__init__(parent)
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
        title = QLabel("Primitives Glossary")
        title.setFont(Fonts.heading(12))
        title.setStyleSheet(
            f"color: {C.header_text}; background: transparent;"
        )
        hl.addWidget(title)
        hl.addStretch()
        count = len(_E_GLOSSARY) + len(_T_GLOSSARY) + len(_H_GLOSSARY)
        count_lbl = QLabel(f"{count} primitives")
        count_lbl.setFont(Fonts.ui(10))
        count_lbl.setStyleSheet("color: rgba(255,255,255,0.65);")
        hl.addWidget(count_lbl)
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
        container = QWidget()
        container.setStyleSheet(f"background: {C.bg};")
        cl = QVBoxLayout(container)
        cl.setContentsMargins(0, 0, 0, 0)
        cl.setSpacing(0)
        scroll.setWidget(container)
        layout.addWidget(scroll)

        # ── Build sections ────────────────────────────────────────
        self._add_section(cl, "E", "System E (Euclid)",
                          "Primary proof language \u2014 points, lines, circles",
                          _E_GLOSSARY)
        self._add_section(cl, "T", "System T (Tarski)",
                          "Bridge system \u2014 points only, with B and \u2261",
                          _T_GLOSSARY)
        self._add_section(cl, "H", "System H (Hilbert)",
                          "Alternative display \u2014 Grundlagen der Geometrie",
                          _H_GLOSSARY)
        cl.addStretch()

    def _add_section(self, parent_layout, sys_key, title, subtitle, entries):
        """Add one collapsible glossary section."""
        badge_color = _SYSTEM_COLORS.get(sys_key, C.primary)
        tint = _SYSTEM_TINTS.get(sys_key, C.surface)

        group = QWidget()
        group_layout = QVBoxLayout(group)
        group_layout.setContentsMargins(0, 0, 0, 0)
        group_layout.setSpacing(0)

        # ── Clickable header ──────────────────────────────────────
        hdr = QFrame()
        hdr.setCursor(QCursor(Qt.CursorShape.PointingHandCursor))
        hdr.setStyleSheet(f"""
            QFrame {{
                background: {C.surface};
                border-bottom: 1px solid {C.border};
                border-left: 4px solid {badge_color};
            }}
            QFrame:hover {{
                background: {C.surface_hover};
            }}
        """)
        hl = QHBoxLayout(hdr)
        hl.setContentsMargins(16, 10, Sp.padding, 10)
        hl.setSpacing(8)

        # Collapse arrow (starts collapsed)
        arrow = QLabel("\u25B8")  # ▸
        arrow.setFont(Fonts.ui(11))
        arrow.setStyleSheet(
            f"color: {C.text_muted}; background: transparent;"
            f" border: none;"
        )
        arrow.setFixedWidth(14)
        hl.addWidget(arrow)

        badge = QLabel(sys_key)
        badge.setFont(Fonts.ui(9))
        badge.setFixedHeight(20)
        badge.setFixedWidth(24)
        badge.setAlignment(Qt.AlignmentFlag.AlignCenter)
        badge.setStyleSheet(f"""
            background: {badge_color};
            color: white;
            border: none;
            border-radius: 4px;
            font-weight: bold;
        """)
        hl.addWidget(badge)

        title_lbl = QLabel(title)
        title_lbl.setFont(Fonts.heading(11))
        title_lbl.setStyleSheet(
            f"color: {C.text}; background: transparent;"
            f" border: none;"
        )
        hl.addWidget(title_lbl)
        hl.addStretch()

        count_badge = QLabel(str(len(entries)))
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
        hl.addWidget(count_badge)
        group_layout.addWidget(hdr)

        # ── Collapsible body ──────────────────────────────────────
        body = QWidget()
        body.setVisible(False)
        body_layout = QVBoxLayout(body)
        body_layout.setContentsMargins(0, 0, 0, 0)
        body_layout.setSpacing(0)

        # Subtitle
        if subtitle:
            sub = QLabel(subtitle)
            sub.setFont(Fonts.ui(9))
            sub.setStyleSheet(
                f"color: {C.text_muted}; background: {C.surface};"
                f" padding: 2px {Sp.padding}px 6px 44px;"
                f" border-bottom: 1px solid {C.border_light};"
            )
            body_layout.addWidget(sub)

        # Entries
        for formal, english, _example in entries:
            self._add_entry(body_layout, formal, english, tint)

        group_layout.addWidget(body)

        # ── Toggle handler ────────────────────────────────────────
        def toggle(event=None, _body=body, _arrow=arrow):
            vis = not _body.isVisible()
            _body.setVisible(vis)
            _arrow.setText("\u25BE" if vis else "\u25B8")

        hdr.mousePressEvent = toggle
        parent_layout.addWidget(group)

    @staticmethod
    def _add_entry(parent_layout, formal, english, tint):
        """Add one glossary row: formal notation → English meaning."""
        row = QFrame()
        row.setObjectName("glossary_row")
        row.setStyleSheet(f"""
            QFrame#glossary_row {{
                background: {C.surface};
                border-bottom: 1px solid {C.border_light};
            }}
            QFrame#glossary_row:hover {{
                background: {C.surface_hover};
            }}
        """)
        rl = QVBoxLayout(row)
        rl.setContentsMargins(20, 6, Sp.padding, 6)
        rl.setSpacing(2)

        # Formal notation (code-like)
        code = QLabel(formal)
        code.setFont(Fonts.formula(10))
        code.setStyleSheet(f"""
            color: {C.text};
            background: {tint};
            border: 1px solid {C.border_light};
            border-radius: 3px;
            padding: 3px 8px;
        """)
        rl.addWidget(code)

        # English meaning
        eng = QLabel(english)
        eng.setFont(Fonts.ui(10))
        eng.setWordWrap(True)
        eng.setStyleSheet(
            f"color: {C.text_secondary}; background: transparent;"
            f" padding-left: 4px;"
        )
        rl.addWidget(eng)

        parent_layout.addWidget(row)
