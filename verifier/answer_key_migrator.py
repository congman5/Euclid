"""
answer_key_migrator.py — Translate legacy answer keys to System E format.

Phase 6.5.2 of the implementation plan.

Converts each of the 48 answer keys in ``legacy JS/answer-keys.json``
from old predicate-based notation to System E literals, producing
``answer-keys-e.json``.

Predicate mapping (old → System E):
  Segment(A,B)            →  a ≠ b
  Point(A)                →  (no literal; just declares variable)
  Circle(A,B)             →  center(a,α_i), on(b,α_i)   [fresh circle]
  OnCircle(P,C,Q)         →  on(p,α_j)
  Between(A,B,C)          →  between(a,b,c)
  Equal(XY,ZW)            →  xy = zw   (segment equality)
  EqualAngle(A,B,C,D,E,F) → ∠abc = ∠def
  Congruent(A,B,C,D,E,F)  →  ab=de, ac=df, bc=ef, ∠bac=∠edf, ∠abc=∠def, ∠acb=∠dfe
  Equilateral(A,B,C)      →  ab=bc, bc=ca
  RightAngle(A,B,C)       →  ∠abc = R
  Collinear(A,B,C)        →  on(b,L) with a,c on L and between(a,b,c) or variants
  Parallel(XY,CD)         →  ¬intersects(L_xy, L_cd)
  SameSide(A,B,L)         →  sameSide(a,b,L)
  Longer(X,Y)             →  x < y  (or y < x — contextual)
  EqualArea(X,Y)          →  area equality via AreaTerm + MagAdd
  Square(A,B,C,D)         →  ab=bc, bc=cd, cd=da, ∠abc=R, ...
  Meet(L,M,P)             →  on(p,L), on(p,M)

Each migrated answer key contains:
  - name: "Prop.I.N"
  - premises: list of E-literal dicts
  - proof_steps: list of {text, e_literals, rule, cites}
  - conclusion: list of E-literal dicts
  - variables: {name: sort}
"""
from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple


# ═══════════════════════════════════════════════════════════════════════
# Literal serialisation helpers
# ═══════════════════════════════════════════════════════════════════════

def _seg(a: str, b: str) -> dict:
    """Segment term {a,b}."""
    return {"type": "segment", "p1": a.lower(), "p2": b.lower()}


def _angle(a: str, b: str, c: str) -> dict:
    """Angle term ∠abc."""
    return {"type": "angle", "p1": a.lower(), "vertex": b.lower(), "p3": c.lower()}


def _area(a: str, b: str, c: str) -> dict:
    """Area term △abc."""
    return {"type": "area", "p1": a.lower(), "p2": b.lower(), "p3": c.lower()}


def _right_angle() -> dict:
    return {"type": "right_angle"}


def _zero(sort: str) -> dict:
    return {"type": "zero", "sort": sort}


def _mag_add(left: dict, right: dict) -> dict:
    return {"type": "mag_add", "left": left, "right": right}


def _eq(left, right, positive: bool = True) -> dict:
    """Equality literal.  *left* and *right* are term dicts or str."""
    return {"atom": "equals", "left": left, "right": right, "positive": positive}


def _on(point: str, obj: str, positive: bool = True) -> dict:
    return {"atom": "on", "point": point.lower(), "obj": obj.lower(), "positive": positive}


def _between(a: str, b: str, c: str, positive: bool = True) -> dict:
    return {"atom": "between", "a": a.lower(), "b": b.lower(), "c": c.lower(), "positive": positive}


def _same_side(a: str, b: str, line: str, positive: bool = True) -> dict:
    return {"atom": "same_side", "a": a.lower(), "b": b.lower(), "line": line.lower(), "positive": positive}


def _intersects(l1: str, l2: str, positive: bool = True) -> dict:
    return {"atom": "intersects", "l1": l1.lower(), "l2": l2.lower(), "positive": positive}


def _neq(a: str, b: str) -> dict:
    """a ≠ b — expressed as Equals(a,b) with polarity=False."""
    return _eq(a.lower(), b.lower(), positive=False)


def _less_than(left: dict, right: dict, positive: bool = True) -> dict:
    return {"atom": "less_than", "left": left, "right": right, "positive": positive}


# ═══════════════════════════════════════════════════════════════════════
# Variable tracking
# ═══════════════════════════════════════════════════════════════════════

class _VarTracker:
    """Track declared variables and allocate fresh circles/lines."""

    def __init__(self) -> None:
        self.vars: Dict[str, str] = {}   # name → sort
        self._circle_idx = 0
        self._line_idx = 0

    def point(self, name: str) -> str:
        n = name.lower()
        self.vars[n] = "point"
        return n

    def line(self, name: str) -> str:
        n = name.lower()
        self.vars[n] = "line"
        return n

    def fresh_circle(self) -> str:
        self._circle_idx += 1
        name = f"circ_{self._circle_idx}"
        self.vars[name] = "circle"
        return name

    def fresh_line(self, tag: str = "") -> str:
        self._line_idx += 1
        name = f"line_{tag}_{self._line_idx}" if tag else f"line_{self._line_idx}"
        self.vars[name] = "line"
        return name

    def ensure_line_for_segment(self, a: str, b: str) -> str:
        """Return a line name for the segment ab, reusing if possible."""
        key = f"line_{min(a,b)}_{max(a,b)}"
        if key not in self.vars:
            self.vars[key] = "line"
        return key


# ═══════════════════════════════════════════════════════════════════════
# Predicate parser
# ═══════════════════════════════════════════════════════════════════════

_PRED_RE = re.compile(r'^(\w+)\((.*)\)$')


def _split_args(s: str) -> List[str]:
    """Split comma-separated arguments respecting nested parentheses."""
    args = []
    depth = 0
    current: List[str] = []
    for ch in s:
        if ch == '(':
            depth += 1
            current.append(ch)
        elif ch == ')':
            depth -= 1
            current.append(ch)
        elif ch == ',' and depth == 0:
            args.append(''.join(current).strip())
            current = []
        else:
            current.append(ch)
    if current:
        args.append(''.join(current).strip())
    return args


def _parse_pred(text: str) -> Tuple[str, List[str]]:
    """Parse ``Name(arg1, arg2, ...)`` → (name, [arg1, arg2, ...]).

    Handles nested parentheses (e.g. ``Equal(SumAngle(CBA, ABD), TwoRight)``).
    """
    text = text.strip()
    m = _PRED_RE.match(text)
    if not m:
        return (text, [])
    name = m.group(1)
    args = _split_args(m.group(2))
    return (name, args)


# ═══════════════════════════════════════════════════════════════════════
# Translate a single predicate text → list of E-literal dicts
# ═══════════════════════════════════════════════════════════════════════

def translate_predicate(text: str, vt: _VarTracker) -> List[dict]:
    """Translate one old-format predicate string into E-literal dicts.

    Returns a (possibly empty) list of literal dicts.
    """
    pred, args = _parse_pred(text)

    if pred == "Segment":
        # Segment(A,B) → a ≠ b
        a, b = args[0], args[1]
        vt.point(a); vt.point(b)
        return [_neq(a, b)]

    if pred == "Point":
        # Point(A) → just declare variable
        vt.point(args[0])
        return []

    if pred == "Circle":
        # Circle(A,B) → center(a,α), on(b,α)
        a, b = args[0], args[1]
        vt.point(a); vt.point(b)
        circ = vt.fresh_circle()
        return [
            {"atom": "center", "point": a.lower(), "circle": circ, "positive": True},
            _on(b, circ),
        ]

    if pred == "OnCircle":
        # OnCircle(P, C, Q) → on(p, α) where α is the circle centered at C through Q
        # Simplified: just on(p, circ)
        p = args[0]
        vt.point(p)
        circ = vt.fresh_circle()
        return [_on(p, circ)]

    if pred == "Between":
        a, b, c = args[0], args[1], args[2]
        vt.point(a); vt.point(b); vt.point(c)
        return [_between(a, b, c)]

    if pred == "Equal":
        # Equal(XY, ZW) — segment names are concatenated point pairs
        return _translate_equal(args, vt)

    if pred == "EqualAngle":
        # EqualAngle(A,B,C,D,E,F) → ∠abc = ∠def  (standard 6-arg)
        # EqualAngle(A,B,C, expr)  → ∠abc = expr  (4-arg compound)
        if len(args) >= 6:
            a, b, c, d, e, f = args[:6]
            for p in [a,b,c,d,e,f]: vt.point(p)
            return [_eq(_angle(a,b,c), _angle(d,e,f))]
        elif len(args) == 4:
            a, b, c = args[0], args[1], args[2]
            for p in [a,b,c]: vt.point(p)
            right = _parse_magnitude_term(args[3], vt)
            return [_eq(_angle(a,b,c), right)]
        else:
            return [{"atom": "opaque", "text": text, "positive": True}]

    if pred == "Congruent":
        # Congruent(A,B,C,D,E,F) → full triangle congruence
        a, b, c, d, e, f = args[:6]
        for p in [a,b,c,d,e,f]: vt.point(p)
        return [
            _eq(_seg(a,b), _seg(d,e)),
            _eq(_seg(b,c), _seg(e,f)),
            _eq(_seg(a,c), _seg(d,f)),
            _eq(_angle(b,a,c), _angle(e,d,f)),
            _eq(_angle(a,b,c), _angle(d,e,f)),
            _eq(_angle(a,c,b), _angle(d,f,e)),
        ]

    if pred == "Equilateral":
        a, b, c = args[:3]
        for p in [a,b,c]: vt.point(p)
        return [
            _eq(_seg(a,b), _seg(b,c)),
            _eq(_seg(b,c), _seg(c,a)),
        ]

    if pred == "RightAngle":
        a, b, c = args[:3]
        for p in [a,b,c]: vt.point(p)
        return [_eq(_angle(a,b,c), _right_angle())]

    if pred == "Collinear":
        a, b, c = args[:3]
        for p in [a,b,c]: vt.point(p)
        line = vt.ensure_line_for_segment(a, c)
        return [_on(a, line), _on(b, line), _on(c, line)]

    if pred == "Parallel":
        # Parallel(XY, CD) — extract point pairs from the arg strings
        seg1, seg2 = args[0], args[1]
        pts1 = _seg_points(seg1, vt)
        pts2 = _seg_points(seg2, vt)
        l1 = vt.ensure_line_for_segment(pts1[0], pts1[1])
        l2 = vt.ensure_line_for_segment(pts2[0], pts2[1])
        return [_intersects(l1, l2, positive=False)]

    if pred == "NotParallel":
        seg1, seg2 = args[0], args[1]
        pts1 = _seg_points(seg1, vt)
        pts2 = _seg_points(seg2, vt)
        l1 = vt.ensure_line_for_segment(pts1[0], pts1[1])
        l2 = vt.ensure_line_for_segment(pts2[0], pts2[1])
        return [_intersects(l1, l2, positive=True)]

    if pred == "SameSide":
        a, b, l = args[0], args[1], args[2]
        vt.point(a); vt.point(b)
        line = vt.ensure_line_for_segment(l[0], l[1]) if len(l) >= 2 else vt.line(l)
        return [_same_side(a, b, line)]

    if pred == "Longer":
        # Longer(X, Y) — X and Y can be segment names or compound expressions
        return _translate_longer(args, vt)

    if pred == "NotLonger":
        return _translate_not_longer(args, vt)

    if pred == "Meet":
        # Meet(L, M, P) → on(p, L), on(p, M)
        l, m, p = args[0], args[1], args[2]
        vt.point(p)
        l_line = vt.line(l) if len(l) == 1 else vt.ensure_line_for_segment(l[0], l[1])
        m_line = vt.line(m) if len(m) == 1 else vt.ensure_line_for_segment(m[0], m[1])
        return [_on(p, l_line), _on(p, m_line)]

    if pred == "EqualArea":
        return _translate_equal_area(args, vt)

    if pred == "Square":
        return _translate_square(args, vt)

    if pred in ("Assume",):
        # Assume(X) → translate X and return as hypothetical assertion
        if args:
            inner_text = ', '.join(args)  # reassemble the inner predicate
            return translate_predicate(inner_text, vt)
        return []

    if pred == "Contradiction":
        # Proof-level marker, not translatable to E literals
        return []

    if pred == "NotEqual":
        # NotEqual(A, B) → a ≠ b
        a, b = args[0], args[1]
        vt.point(a); vt.point(b)
        return [_neq(a, b)]

    if pred == "NotCollinear":
        # NotCollinear(A, B, C) → ¬on(b, L_ac) (not all on same line)
        a, b, c = args[0], args[1], args[2]
        for p in [a,b,c]: vt.point(p)
        line = vt.ensure_line_for_segment(a, c)
        return [_on(a, line), _on(c, line), _on(b, line, positive=False)]

    if pred == "NotEqualAngle":
        # NotEqualAngle(A,B,C,D,E,F) → ¬(∠abc = ∠def)
        a, b, c, d, e, f = args[:6]
        for p in [a,b,c,d,e,f]: vt.point(p)
        return [_eq(_angle(a,b,c), _angle(d,e,f), positive=False)]

    # Fallback: store as opaque annotation
    return [{"atom": "opaque", "text": text, "positive": True}]


# ═══════════════════════════════════════════════════════════════════════
# Helper translators for compound predicates
# ═══════════════════════════════════════════════════════════════════════

def _seg_points(name: str, vt: _VarTracker) -> Tuple[str, str]:
    """Extract two point names from a segment name like 'AB' or 'A, B'."""
    name = name.strip()
    if ',' in name:
        parts = [p.strip() for p in name.split(',')]
        vt.point(parts[0]); vt.point(parts[1])
        return (parts[0], parts[1])
    # Single-letter points: AB → (A, B); multi-char possible
    if len(name) == 2:
        vt.point(name[0]); vt.point(name[1])
        return (name[0], name[1])
    if len(name) >= 2:
        # Try splitting at midpoint
        mid = len(name) // 2
        a, b = name[:mid], name[mid:]
        vt.point(a); vt.point(b)
        return (a, b)
    vt.point(name)
    return (name, name)


def _translate_equal(args: List[str], vt: _VarTracker) -> List[dict]:
    """Translate Equal(X, Y) where X,Y are segment-name expressions."""
    if len(args) == 4:
        # Equal(A, B, C, D) → legacy 4-arg form: AB = CD
        a, b, c, d = args
        for p in [a,b,c,d]: vt.point(p)
        return [_eq(_seg(a,b), _seg(c,d))]

    left_str, right_str = args[0].strip(), args[1].strip()

    # Single-letter args: Equal(C, D) → point equality c = d
    if len(left_str) == 1 and left_str.isalpha() and len(right_str) == 1 and right_str.isalpha():
        vt.point(left_str); vt.point(right_str)
        return [_eq(left_str.lower(), right_str.lower())]

    # Try parsing as compound (SumAngle, TwoRight, etc.)
    left_term = _parse_magnitude_term(left_str, vt)
    right_term = _parse_magnitude_term(right_str, vt)

    return [_eq(left_term, right_term)]


def _parse_magnitude_term(s: str, vt: _VarTracker) -> Any:
    """Parse a magnitude term string into a term dict.

    Handles: AB (segment), SumAngle(...), TwoRight, SumSeg(...),
    SumArea(...), Angle..., named areas (Par, Tri, Sq, Rect, Comp, Recti,
    HalfPar), CoInterior, Double..., etc.
    """
    s = s.strip()

    if s == "TwoRight":
        return _mag_add(_right_angle(), _right_angle())

    if s == "CoInterior":
        # Co-interior angles sum to two right angles — treated as a
        # named magnitude constant (same as TwoRight in context)
        return _mag_add(_right_angle(), _right_angle())

    # Function-form: Name(args...)
    m = re.match(r'^(\w+)\((.+)\)$', s)
    if m:
        fname = m.group(1)
        inner_args = _split_args(m.group(2))
        if fname in ("SumAngle", "SumAngles"):
            if len(inner_args) == 6:
                # SumAngle(A,B,C,D,E,F) → ∠ABC + ∠DEF
                for p in inner_args: vt.point(p)
                left = _angle(inner_args[0], inner_args[1], inner_args[2])
                right = _angle(inner_args[3], inner_args[4], inner_args[5])
                return _mag_add(left, right)
            elif len(inner_args) == 2:
                left = _parse_magnitude_term(inner_args[0], vt)
                right = _parse_magnitude_term(inner_args[1], vt)
                return _mag_add(left, right)
            else:
                # Try as two compound expressions
                left = _parse_magnitude_term(inner_args[0], vt)
                right = _parse_magnitude_term(inner_args[1], vt)
                return _mag_add(left, right)
        if fname == "SumSeg":
            if len(inner_args) == 4:
                # SumSeg(A,B,C,D) → AB + CD
                for p in inner_args: vt.point(p)
                left = _seg(inner_args[0], inner_args[1])
                right = _seg(inner_args[2], inner_args[3])
                return _mag_add(left, right)
            elif len(inner_args) == 2:
                left = _parse_magnitude_term(inner_args[0], vt)
                right = _parse_magnitude_term(inner_args[1], vt)
                return _mag_add(left, right)
            else:
                left = _parse_magnitude_term(inner_args[0], vt)
                right = _parse_magnitude_term(inner_args[1], vt)
                return _mag_add(left, right)
        if fname == "SumArea":
            left = _parse_magnitude_term(inner_args[0], vt)
            right = _parse_magnitude_term(inner_args[1], vt)
            return _mag_add(left, right)
        # Unknown function — try parsing args and wrap as opaque
        return {"type": "opaque", "text": s}

    # Double prefix: DoubleTriEBC → tri+tri
    m = re.match(r'^Double(.+)$', s)
    if m:
        inner = _parse_magnitude_term(m.group(1), vt)
        return _mag_add(inner, inner)

    # Angle name: e.g. AngleABC → ∠ABC
    m = re.match(r'^Angle(\w)(\w)(\w)$', s)
    if m:
        for p in m.groups(): vt.point(p)
        return _angle(m.group(1), m.group(2), m.group(3))

    # Named area references (parallelogram, triangle, square, rect, etc.)
    m = re.match(r'^(?:Par|Tri|Sq|Rect|Comp|Recti|HalfPar)(\w+)$', s)
    if m:
        return _parse_area_name(s, vt)

    # Segment name: two chars → segment term
    if len(s) == 2 and s.isalpha():
        vt.point(s[0]); vt.point(s[1])
        return _seg(s[0], s[1])

    # Bare 3-letter angle name: CBA → ∠CBA (used inside SumAngle etc.)
    if len(s) == 3 and s.isalpha():
        for p in s: vt.point(p)
        return _angle(s[0], s[1], s[2])

    # Single letter: e.g. just a point name — treat as opaque
    # (should not normally appear as a magnitude term)
    return {"type": "opaque", "text": s}


def _parse_area_name(s: str, vt: _VarTracker) -> dict:
    """Parse named area references like ParABCD, TriABC, SqABCD, RectABCD, HalfParABCD."""
    m = re.match(r'^Tri(\w)(\w)(\w)$', s)
    if m:
        a, b, c = m.groups()
        for p in [a,b,c]: vt.point(p)
        return _area(a, b, c)

    m = re.match(r'^Par(\w)(\w)(\w)(\w)$', s)
    if m:
        a, b, c, d = m.groups()
        for p in [a,b,c,d]: vt.point(p)
        return _mag_add(_area(a, b, c), _area(a, c, d))

    m = re.match(r'^Sq(\w)(\w)(\w)(\w)$', s)
    if m:
        a, b, c, d = m.groups()
        for p in [a,b,c,d]: vt.point(p)
        return _mag_add(_area(a, b, c), _area(a, c, d))

    m = re.match(r'^Rect(\w)(\w)(\w)(\w)$', s)
    if m:
        a, b, c, d = m.groups()
        for p in [a,b,c,d]: vt.point(p)
        return _mag_add(_area(a, b, c), _area(a, c, d))

    m = re.match(r'^HalfPar(\w)(\w)(\w)(\w)$', s)
    if m:
        # Half of a parallelogram = one triangle diagonal
        a, b, c, d = m.groups()
        for p in [a,b,c,d]: vt.point(p)
        return _area(a, b, c)

    m = re.match(r'^Comp(\w+)$', s)
    if m:
        pts = list(m.group(1))
        for p in pts: vt.point(p)
        if len(pts) == 4:
            a, b, c, d = pts
            return _mag_add(_area(a, b, c), _area(a, c, d))
        return {"type": "opaque", "text": s}

    m = re.match(r'^Recti(\w)(\w)(\w)(\w)$', s)
    if m:
        a, b, c, d = m.groups()
        for p in [a,b,c,d]: vt.point(p)
        return _mag_add(_area(a, b, c), _area(a, c, d))

    return {"type": "opaque", "text": s}


def _translate_longer(args: List[str], vt: _VarTracker) -> List[dict]:
    """Translate Longer(X, Y) → X < Y as magnitude less-than."""
    right_term = _parse_magnitude_term(args[0], vt)
    left_term = _parse_magnitude_term(args[1], vt)
    # Longer(X,Y) means X > Y, i.e. Y < X
    return [_less_than(left_term, right_term)]


def _translate_not_longer(args: List[str], vt: _VarTracker) -> List[dict]:
    """Translate NotLonger(X, Y) → ¬(Y < X)."""
    right_term = _parse_magnitude_term(args[0], vt)
    left_term = _parse_magnitude_term(args[1], vt)
    return [_less_than(left_term, right_term, positive=False)]


def _translate_equal_area(args: List[str], vt: _VarTracker) -> List[dict]:
    """Translate EqualArea(X, Y) → area equality."""
    left = _parse_magnitude_term(args[0].strip(), vt)
    right = _parse_magnitude_term(args[1].strip(), vt)
    return [_eq(left, right)]


def _translate_square(args: List[str], vt: _VarTracker) -> List[dict]:
    """Translate Square(A,B,C,D) → 4 equal sides + 4 right angles."""
    a, b, c, d = args[:4]
    for p in [a,b,c,d]: vt.point(p)
    return [
        _eq(_seg(a,b), _seg(b,c)),
        _eq(_seg(b,c), _seg(c,d)),
        _eq(_seg(c,d), _seg(d,a)),
        _eq(_angle(d,a,b), _right_angle()),
        _eq(_angle(a,b,c), _right_angle()),
        _eq(_angle(b,c,d), _right_angle()),
        _eq(_angle(c,d,a), _right_angle()),
    ]


# ═══════════════════════════════════════════════════════════════════════
# Full answer-key migrator
# ═══════════════════════════════════════════════════════════════════════

def migrate_answer_key(key: str, entry: dict) -> dict:
    """Migrate one answer key from old format to System E format.

    Args:
        key: e.g. "euclid-I.1"
        entry: dict with title, premises, proof, conclusion

    Returns:
        Migrated dict with E-literal representation.
    """
    vt = _VarTracker()

    # ── Premises ──────────────────────────────────────────────────
    e_premises: List[dict] = []
    for p in entry.get("premises", []):
        e_premises.extend(translate_predicate(p, vt))

    # ── Proof steps ───────────────────────────────────────────────
    e_steps: List[dict] = []
    for step in entry.get("proof", []):
        lits = translate_predicate(step["text"], vt)
        e_steps.append({
            "text": step["text"],
            "e_literals": lits,
            "rule": step.get("rule", ""),
            "cite": step.get("cite", []),
        })

    # ── Conclusion ────────────────────────────────────────────────
    conclusion_text = entry.get("conclusion", "")
    e_conclusion = translate_predicate(conclusion_text, vt) if conclusion_text else []

    # ── Prop name ─────────────────────────────────────────────────
    # "euclid-I.1" → "Prop.I.1"
    num = key.replace("euclid-", "")
    prop_name = f"Prop.{num}"

    return {
        "name": prop_name,
        "title": entry.get("title", ""),
        "variables": dict(vt.vars),
        "premises": e_premises,
        "proof_steps": e_steps,
        "conclusion": e_conclusion,
    }


def migrate_all(input_path: str = "legacy JS/answer-keys.json",
                output_path: str = "answer-keys-e.json") -> dict:
    """Migrate all 48 answer keys and write to output file.

    Returns the migrated dict.
    """
    with open(input_path, encoding="utf-8") as f:
        data = json.load(f)

    result = {
        "_description": (
            "System E answer keys — migrated from legacy predicate format. "
            "Each entry uses System E literals (on, between, equals, etc.) "
            "with segment/angle/area magnitude terms."
        ),
    }

    for key in sorted(data.keys()):
        if not key.startswith("euclid-"):
            continue
        result[key] = migrate_answer_key(key, data[key])

    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(result, f, indent=2, ensure_ascii=False)

    return result


# ═══════════════════════════════════════════════════════════════════════
# CLI entry point
# ═══════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    result = migrate_all()
    count = sum(1 for k in result if k.startswith("euclid-"))
    print(f"Migrated {count} answer keys to answer-keys-e.json")
