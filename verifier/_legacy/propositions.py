"""
propositions.py — Baked-in proposition rules for Euclid Book I.

Each proposition that has a formal conclusion_predicate is registered
as a derived rule in ALL_RULES.  The checker treats them like any
other derived rule — matching premises against referenced lines
and verifying the conclusion pattern.

Propositions without a formalized conclusion are not registered;
users can still prove them from axioms and load them as lemmas.
"""
from __future__ import annotations

from .rules import RuleSchema, RuleKind, ALL_RULES
from .parser import parse_formula as _p

# ── Proposition rule definitions ─────────────────────────────────────
# Each entry: (rule_name, [premise_formulas], conclusion_formula)
#
# Premises mirror the formal given objects for each proposition.
# Conclusions use the conclusion_predicate from proposition_data.py.

_PROP_RULES = [
    # I.1 — Equilateral Triangle Construction
    # Given: Segment(A,B)
    # Conclusion: Equal(AB,AC) ∧ Equal(AB,BC)
    ("Prop.I.1",
     ["Segment(A, B)"],
     "Equal(AB, AC) \u2227 Equal(AB, BC)"),

    # I.2 — Transfer a Length to a Point
    # Given: Point(A), Segment(B,C)
    # Conclusion: Equal(AL,BC) — segment from A equal to given segment
    ("Prop.I.2",
     ["Point(A)", "Segment(B, C)"],
     "Equal(AL, BC)"),

    # I.3 — Cut Off Equal Length
    # Given: Segment(A,B), Segment(C,D)  (AB > CD)
    # Conclusion: Equal(AE,CD) — cut-off on AB equal to CD
    ("Prop.I.3",
     ["Segment(A, B)", "Segment(C, D)"],
     "Equal(AE, CD)"),

    # I.4 — SAS Congruence
    # Given: Equal(AB,DE), Equal(AC,DF), EqualAngle(B,A,C,E,D,F)
    # Conclusion: Congruent(A,B,C,D,E,F)
    ("Prop.I.4",
     ["Equal(AB, DE)", "Equal(AC, DF)", "EqualAngle(B, A, C, E, D, F)"],
     "Congruent(A, B, C, D, E, F)"),

    # I.5 — Isosceles Base Angles
    # Given: Equal(AB,AC) (isosceles)
    # Conclusion: EqualAngle(A,B,C,A,C,B)
    ("Prop.I.5",
     ["Equal(AB, AC)"],
     "EqualAngle(A, B, C, A, C, B)"),

    # I.6 — Converse of Isosceles Base Angles
    # Given: EqualAngle(A,B,C,A,C,B)
    # Conclusion: Equal(AB,AC)
    ("Prop.I.6",
     ["EqualAngle(A, B, C, A, C, B)"],
     "Equal(AB, AC)"),

    # I.7 — Unique Triangle on Segment
    # Given: Segment(A,B), Equal(AC,AD), Equal(BC,BD)
    # Conclusion: C = D
    ("Prop.I.7",
     ["Segment(A, B)", "Equal(AC, AD)", "Equal(BC, BD)"],
     "C = D"),

    # I.8 — SSS Congruence
    # Given: Equal(AB,DE), Equal(BC,EF), Equal(CA,FD)
    # Conclusion: Congruent(A,B,C,D,E,F)
    ("Prop.I.8",
     ["Equal(AB, DE)", "Equal(BC, EF)", "Equal(CA, FD)"],
     "Congruent(A, B, C, D, E, F)"),

    # I.27 — Alternate Interior Angles Imply Parallel
    # Given: Transversal cutting lines, EqualAngle (alternate interior)
    # Conclusion: Parallel(l,m)
    ("Prop.I.27",
     ["EqualAngle(A, E, F, E, F, D)"],
     "Parallel(AB, CD)"),

    # I.28 — Exterior Angle Equals Opposite Interior Implies Parallel
    ("Prop.I.28",
     ["EqualAngle(G, E, B, E, F, D)"],
     "Parallel(AB, CD)"),

    # I.30 — Lines Parallel to Same Line Are Parallel
    # Given: Parallel(AB,EF), Parallel(CD,EF)
    # Conclusion: Parallel(AB,CD)
    ("Prop.I.30",
     ["Parallel(AB, EF)", "Parallel(CD, EF)"],
     "Parallel(AB, CD)"),

    # I.48 — Converse Pythagorean Theorem
    # Given: Triangle with square on hypotenuse = sum of squares on legs
    # Conclusion: Right angle
    ("Prop.I.48",
     ["Triangle(A, B, C)", "Equal(BC_sq, AB_sq_plus_AC_sq)"],
     "Perpendicular(BA, AC)"),
]


def _register_propositions():
    """Register all proposition rules as derived rules."""
    for name, premise_strs, concl_str in _PROP_RULES:
        if name in ALL_RULES:
            continue
        try:
            premises = [_p(s) for s in premise_strs]
            conclusion = _p(concl_str)
            n = len(premises)
            schema = RuleSchema(name, RuleKind.DERIVED,
                                premises, conclusion, n, n)
            ALL_RULES[name] = schema
        except Exception:
            pass  # skip if formula doesn't parse


_register_propositions()
