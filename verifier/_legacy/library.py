"""
library.py — Derived rules. Explicitly separated from kernel.
"""
from .rules import RuleSchema, RuleKind, ALL_RULES
from .parser import parse_formula as _p

_DERIVED = [
    # ── Triangle congruence ────────────────────────────────────────────
    RuleSchema("CongruenceElim", RuleKind.DERIVED,
               [_p("Congruent(A, B, C, D, E, F)")],
               _p("Equal(AB, DE) \u2227 Equal(BC, EF) \u2227 Equal(AC, DF) \u2227 EqualAngle(A, B, C, D, E, F)"),
               1, 1),
    RuleSchema("SSS", RuleKind.DERIVED,
               [_p("Equal(AB, DE)"), _p("Equal(BC, EF)"), _p("Equal(CA, FD)")],
               _p("Congruent(A, B, C, D, E, F)"), 3, 3),
    RuleSchema("ASA", RuleKind.DERIVED,
               [_p("EqualAngle(A, B, C, D, E, F)"),
                _p("EqualAngle(A, C, B, D, F, E)"),
                _p("Equal(BC, EF)")],
               _p("Congruent(A, B, C, D, E, F)"), 3, 3),

    # ── Circle construction & intersection ─────────────────────────────
    RuleSchema("Post3", RuleKind.DERIVED,
               [_p("Segment(A, B)")],
               _p("Circle(C, D)"), 1, 1),
    RuleSchema("CircleCircleIntersect", RuleKind.DERIVED,
               [_p("Circle(A, B)"), _p("Circle(B, A)")],
               _p("\u2203X(OnCircle(X, A, B) \u2227 OnCircle(X, B, A))"), 2, 2),
    RuleSchema("TriangleFromCircleIntersect", RuleKind.DERIVED,
               [_p("OnCircle(C, A, B)"), _p("OnCircle(C, B, A)")],
               _p("Triangle(A, B, C)"), 2, 2),
    RuleSchema("RadiusEquality", RuleKind.DERIVED,
               [_p("Circle(A, B)"), _p("OnCircle(C, A, B)")],
               _p("Equal(AC, AB)"), 2, 2),

    # ── Segment equality helpers ───────────────────────────────────────
    RuleSchema("EqSymSeg", RuleKind.DERIVED,
               [_p("Equal(AB, CD)")],
               _p("Equal(CD, AB)"), 1, 1),
    RuleSchema("EqReflSeg", RuleKind.DERIVED,
               [], _p("Equal(AB, BA)"), 0, 0),
    RuleSchema("CongruenceSymChain", RuleKind.DERIVED,
               [_p("Equal(AC, AB)"), _p("Equal(BC, BA)")],
               _p("Equal(AB, AC) \u2227 Equal(AB, BC)"), 2, 2),

    # ── Congruence extraction helpers ──────────────────────────────────
    RuleSchema("ExtractAngleFromCongruence", RuleKind.DERIVED,
               [_p("Equal(AB, AC) \u2227 Equal(BC, CB) \u2227 Equal(AC, AB) \u2227 EqualAngle(A, B, C, A, C, B)")],
               _p("EqualAngle(A, B, C, A, C, B)"), 1, 1),
    RuleSchema("ExtractSegFromCongruence", RuleKind.DERIVED,
               [_p("Equal(AB, AC) \u2227 Equal(BC, CB) \u2227 Equal(AC, AB) \u2227 EqualAngle(A, B, C, A, C, B)")],
               _p("Equal(AB, AC)"), 1, 1),
    RuleSchema("ExtractMiddleConj", RuleKind.DERIVED,
               [_p("phi \u2227 psi \u2227 chi")],
               _p("psi"), 1, 1),
    RuleSchema("ExtractFirstConj", RuleKind.DERIVED,
               [_p("phi \u2227 psi \u2227 chi")],
               _p("phi"), 1, 1),

    # ── Angle helpers ──────────────────────────────────────────────────
    RuleSchema("AngleCongSym", RuleKind.DERIVED,
               [_p("EqualAngle(A, B, C, D, E, F)")],
               _p("EqualAngle(D, E, F, A, B, C)"), 1, 1),
    RuleSchema("AngleBisectorReindex", RuleKind.DERIVED,
               [_p("EqualAngle(B, A, C, B, A, E)")],
               _p("EqualAngle(B, A, E, E, A, C)"), 1, 1),
    RuleSchema("AngleSideChoice", RuleKind.DERIVED,
               [_p("Angle(B, A, C)"), _p("Ray(A, B)")],
               _p("ChosenSide(C, Line(A, B))"), 2, 2),

    # ── Segment/point construction ─────────────────────────────────────
    RuleSchema("Post1", RuleKind.DERIVED,
               [_p("Point(A)"), _p("Point(B)")],
               _p("Segment(A, B)"), 2, 2),
    RuleSchema("GreaterCutoff", RuleKind.DERIVED,
               [_p("Greater(AB, CD)"),
                _p("OnRay(E, A, B) \u2227 Equal(AE, CD)"),
                _p("Equal(AE, CD)")],
               _p("Between(A, E, B)"), 3, 3),
    RuleSchema("UniqueEuclideanPointConstruction", RuleKind.DERIVED,
               [_p("SameSide(C, D, Line(A, B))"), _p("Congruent(A, C, B, A, D, B)")],
               _p("C = D"), 2, 2),

    # ── Midpoint ───────────────────────────────────────────────────────
    RuleSchema("Midpoint", RuleKind.DERIVED,
               [_p("A \u2260 B")],
               _p("\u2203M(Between(A, M, B) \u2227 Equal(AM, MB))"), 1, 1),
    RuleSchema("Perpendicular", RuleKind.DERIVED,
               [_p("Point(P)"), _p("Line(l)")],
               _p("\u2203m(OnLine(P, m) \u2227 Perpendicular(m, l))"), 2, 2),

    # ── Circle-line intersection ───────────────────────────────────────
    RuleSchema("CircleLineIntersect", RuleKind.DERIVED,
               [_p("Circle(O, P)"), _p("Line(l)"),
                _p("CircleLineIntersectionConditions(O, P, l)")],
               _p("\u2203X(OnCircle(X, O, P) \u2227 OnLine(X, l))"), 3, 3),

    # ── Segment congruence transitivity ────────────────────────────────
    RuleSchema("CongTransSeg", RuleKind.DERIVED,
               [_p("Equal(AB, CD)"), _p("Equal(CD, EF)")],
               _p("Equal(AB, EF)"), 2, 2),

    # ── Angle congruence helpers ───────────────────────────────────────
    RuleSchema("AngRefl", RuleKind.DERIVED,
               [_p("Angle(A, B, C)")],
               _p("EqualAngle(A, B, C, A, B, C)"), 1, 1),
    RuleSchema("AngTrans", RuleKind.DERIVED,
               [_p("EqualAngle(A, B, C, D, E, F)"),
                _p("EqualAngle(D, E, F, G, H, I)")],
               _p("EqualAngle(A, B, C, G, H, I)"), 2, 2),

    # ── Segment arithmetic ─────────────────────────────────────────────
    RuleSchema("SegAdd", RuleKind.DERIVED,
               [_p("Between(A, B, C)"), _p("Between(D, E, F)"),
                _p("Equal(AB, DE)"), _p("Equal(BC, EF)")],
               _p("Equal(AC, DF)"), 4, 4),
    RuleSchema("SegSub", RuleKind.DERIVED,
               [_p("Between(A, B, C)"), _p("Between(D, E, F)"),
                _p("Equal(AC, DF)"), _p("Equal(AB, DE)")],
               _p("Equal(BC, EF)"), 4, 4),

    # ── Right-angle rules ──────────────────────────────────────────────
    RuleSchema("RightAngleCongruence", RuleKind.DERIVED,
               [_p("RightAngle(A, B, C)")],
               _p("EqualAngle(A, B, C, C, B, A)"), 1, 1),
    RuleSchema("AngleCongruentToRightAngleIsRight", RuleKind.DERIVED,
               [_p("RightAngle(A, B, C)"),
                _p("EqualAngle(A, B, C, D, E, F)")],
               _p("RightAngle(D, E, F)"), 2, 2),
    RuleSchema("PerpendicularImpliesRightAngle", RuleKind.DERIVED,
               [_p("Perpendicular(l, m)"), _p("OnLine(A, l)"),
                _p("OnLine(B, l)"), _p("OnLine(B, m)"), _p("OnLine(C, m)")],
               _p("RightAngle(A, B, C)"), 5, 5),
    RuleSchema("RightAngleImpliesPerpendicular", RuleKind.DERIVED,
               [_p("RightAngle(A, B, C)"), _p("OnLine(A, l)"),
                _p("OnLine(B, l)"), _p("OnLine(B, m)"), _p("OnLine(C, m)")],
               _p("Perpendicular(l, m)"), 5, 5),
    RuleSchema("AllRightAnglesCongruent", RuleKind.DERIVED,
               [_p("RightAngle(A, B, C)"), _p("RightAngle(D, E, F)")],
               _p("EqualAngle(A, B, C, D, E, F)"), 2, 2),

    # ── Parallel-angle rules ───────────────────────────────────────────
    RuleSchema("AltInteriorEqualImpliesParallel", RuleKind.DERIVED,
               [_p("Transversal(t, l, m)"),
                _p("EqualAngle(A, B, C, D, E, F)")],
               _p("Parallel(l, m)"), 2, 2),
    RuleSchema("ParallelImpliesAltInteriorEqual", RuleKind.DERIVED,
               [_p("Parallel(l, m)"), _p("Transversal(t, l, m)")],
               _p("EqualAngle(A, B, C, D, E, F)"), 2, 2),
    RuleSchema("SameSideInteriorSupplementaryImpliesParallel", RuleKind.DERIVED,
               [_p("Transversal(t, l, m)"),
                _p("Supplementary(A, B, C, D, E, F)")],
               _p("Parallel(l, m)"), 2, 2),
    RuleSchema("ParallelTransversalAngleTransfer", RuleKind.DERIVED,
               [_p("Parallel(l, m)"), _p("Transversal(t, l, m)"),
                _p("EqualAngle(A, B, C, D, E, F)")],
               _p("EqualAngle(G, H, I, J, K, L)"), 3, 3),
]

for rule in _DERIVED:
    ALL_RULES[rule.name] = rule

# Import propositions module to register Prop.I.N rules alongside derived rules
import verifier._legacy.propositions  # noqa: F401, E402
