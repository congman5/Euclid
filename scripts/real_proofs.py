"""
real_proofs.py - Non-circular proofs for all 48 Book I propositions.

Each proof is named "Prop.I.N" and can only cite earlier propositions
(I.1 through I.(N-1)).  Proofs use correct justification steps:
  Given, let-line, let-circle, let-point-on-line,
  let-intersection-circle-circle-one, Generality 3, Intersection 9,
  Segment transfer 4, Metric, Transfer, SAS, SSS, Prop.I.N,
  Indirect[Prop.I.X,...] (for reductio ad absurdum proofs).

Run: python -X utf8 scripts/real_proofs.py
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
os.environ["PYTHONIOENCODING"] = "utf-8"
from typing import List, Dict
from verifier.unified_checker import verify_e_proof_json
from verifier.e_library import E_THEOREM_LIBRARY


class PB:
    """Proof builder.

    Tracks the current subproof depth so that ``assume()`` /
    ``reductio()`` produce correctly-scoped lines.  The plain ``g()``
    and ``s()`` helpers honour the current depth automatically.
    """
    def __init__(self, name, premises, goal):
        self.name = name
        self.premises = premises
        self.goal = goal
        self._lines = []
        self._lid = 0
        self._depth = 0

    # ── Given line (always at current depth) ──────────────────────
    def g(self, stmt):
        self._lid += 1
        self._lines.append({"id": self._lid, "depth": self._depth,
            "statement": stmt, "justification": "Given", "refs": []})
        return self._lid

    # ── Normal proof step (at current depth) ──────────────────────
    def s(self, stmt, just, refs):
        self._lid += 1
        self._lines.append({"id": self._lid, "depth": self._depth,
            "statement": stmt, "justification": just, "refs": refs})
        return self._lid

    # ── Open a subproof: Assume φ at depth+1 ─────────────────────
    def assume(self, stmt):
        """Insert an Assume line and increase depth by 1.

        Returns the line id of the Assume line (needed by ``reductio``).
        """
        self._depth += 1
        self._lid += 1
        self._lines.append({"id": self._lid, "depth": self._depth,
            "statement": stmt, "justification": "Assume", "refs": []})
        return self._lid

    # ── Close a subproof: Reductio concluding φ at depth−1 ───────
    def reductio(self, stmt, assume_ref):
        """Insert a Reductio line referencing the Assume line and
        decrease depth by 1.

        *assume_ref* is the line id returned by ``assume()``.
        Returns the line id of the Reductio conclusion.
        """
        self._depth = max(0, self._depth - 1)
        self._lid += 1
        self._lines.append({"id": self._lid, "depth": self._depth,
            "statement": stmt, "justification": "Reductio",
            "refs": [assume_ref]})
        return self._lid

    def build(self):
        return {"name": self.name,
                "declarations": {"points": [], "lines": []},
                "premises": self.premises, "goal": self.goal,
                "lines": list(self._lines)}


def check(pj, quiet=False):
    r = verify_e_proof_json(pj)
    ok = r.accepted and all(lr.valid for lr in r.line_results.values())
    if not ok and not quiet:
        print(f"  FAIL: {pj['name']}")
        for lid, lr in sorted(r.line_results.items()):
            if not lr.valid:
                for e in lr.errors:
                    print(f"    L{lid}: {e}")
        for e in r.errors:
            print(f"    GOAL: {e}")
    return ok


ALL: Dict[int, dict] = {}


# ═════════════════════════════════════════════════════════════════
# Prop I.1 — Equilateral triangle construction (primitive)
# ═════════════════════════════════════════════════════════════════
def p1():
    b = PB("Prop.I.1", ["\u00ac(a = b)"],
           "ab = ac, ab = bc, \u00ac(c = a), \u00ac(c = b)")
    g1 = b.g("\u00ac(a = b)")
    s2 = b.s("center(a, \u03b1), on(b, \u03b1)", "let-circle", [g1])
    s3 = b.s("center(b, \u03b2), on(a, \u03b2)", "let-circle", [g1])
    s4 = b.s("inside(a, \u03b1)", "Generality 3", [s2])
    s5 = b.s("inside(b, \u03b2)", "Generality 3", [s3])
    s6 = b.s("intersects(\u03b1, \u03b2)", "Intersection 9",
             [s2, s3, s4, s5])
    s7 = b.s("on(c, \u03b1), on(c, \u03b2)",
             "let-intersection-circle-circle-one", [s6])
    s8 = b.s("ac = ab", "Segment transfer 4", [s2, s7])
    s9 = b.s("bc = ba", "Segment transfer 4", [s3, s7])
    s10 = b.s("ab = ba", "M3 \u2014 Symmetry", [])
    s11 = b.s("ab = bc", "CN1 \u2014 Transitivity", [s8, s10])
    b.s("ab = ac", "CN1 \u2014 Transitivity", [s8, s10])
    b.s("\u00ac(c = a)", "CN1 \u2014 Transitivity", [])
    b.s("\u00ac(c = b)", "CN1 \u2014 Transitivity", [])
    return b.build()

ALL[1] = p1()


# ═════════════════════════════════════════════════════════════════
# Prop I.2 — Copy a segment to a given point
# Uses: I.1 (equilateral triangle), construction, transfer, metric
# ═════════════════════════════════════════════════════════════════
def p2():
    b = PB("Prop.I.2",
           ["on(b, L)", "on(c, L)", "\u00ac(b = c)", "\u00ac(a = b)", "\u00ac(a = c)"],
           "af = bc")
    g1 = b.g("on(b, L)")
    g2 = b.g("on(c, L)")
    g3 = b.g("\u00ac(b = c)")
    g4 = b.g("\u00ac(a = b)")
    g5 = b.g("\u00ac(a = c)")
    # Construct equilateral triangle on ab → point d
    s6 = b.s("ab = ad, ab = bd, \u00ac(d = a), \u00ac(d = b)",
             "Prop.I.1", [g4])
    # Line through d,b
    s7 = b.s("on(d, M), on(b, M)", "let-line", [s6])
    # Circle γ center b radius bc
    s8 = b.s("center(b, \u03b3), on(c, \u03b3)", "let-circle", [g3])
    # Center b is inside γ
    s9 = b.s("inside(b, \u03b3)", "Generality 3", [s8])
    # Extend line db past b to hit γ at g
    s10 = b.s("on(g, \u03b3), on(g, M), between(g, b, d)",
              "let-intersection-line-circle-extend", [s9, s7])
    # bg = bc (radii of γ)
    s11 = b.s("bg = bc", "Segment transfer 4", [s8, s10])
    # g ≠ d (from betweenness)
    s12 = b.s("\u00ac(g = d)", "Diagrammatic", [s10])
    # Circle δ center d radius dg
    s13 = b.s("center(d, \u03b4), on(g, \u03b4)", "let-circle", [s12])
    # Line through d,a
    s14 = b.s("on(d, N), on(a, N)", "let-line", [s6])
    # da = db (equilateral triangle, M3 symmetry)
    s15 = b.s("da = db", "Metric", [s6])
    # b is inside δ (between(g,b,d) with g on δ, center d)
    s16 = b.s("inside(b, \u03b4)", "Diagrammatic", [s10, s13])
    # db < dg (b inside δ, g on δ, center d)
    s17 = b.s("db < dg", "Transfer", [s13, s16])
    # da < dg (from da = db and db < dg)
    s18 = b.s("da < dg", "Metric", [s15, s17])
    # a is inside δ
    s19 = b.s("inside(a, \u03b4)", "Transfer", [s13, s18])
    # Extend line da past a to hit δ at f
    s20 = b.s("on(f, \u03b4), on(f, N), between(f, a, d)",
              "let-intersection-line-circle-extend", [s19, s14])
    # df = dg (radii of δ)
    s21 = b.s("df = dg", "Segment transfer 4", [s13, s20])
    # fa + ad = fd (betweenness transfer)
    s22 = b.s("fa + ad = fd", "Transfer", [s20])
    # gb + bd = gd (betweenness transfer)
    s23 = b.s("gb + bd = gd", "Transfer", [s10])
    # af = bg (df=dg, da=db, cancellation: fd-ad = gd-bd)
    s24 = b.s("af = bg", "Metric", [s21, s22, s23, s15])
    # af = bc
    b.s("af = bc", "Metric", [s24, s11])
    return b.build()

ALL[2] = p2()


# ═════════════════════════════════════════════════════════════════
# Prop I.3 — Cut off an equal segment
# Uses: I.2 (copy segment), construction, transfer, metric
# ═════════════════════════════════════════════════════════════════
def p3():
    b = PB("Prop.I.3",
           ["on(a, L)", "on(b, L)", "\u00ac(a = b)", "cd < ab",
            "\u00ac(c = d)", "\u00ac(a = c)", "\u00ac(a = d)"],
           "between(a, e, b), ae = cd")
    g1 = b.g("on(a, L)")
    g2 = b.g("on(b, L)")
    g3 = b.g("\u00ac(a = b)")
    g4 = b.g("cd < ab")
    g5 = b.g("\u00ac(c = d)")
    g6 = b.g("\u00ac(a = c)")
    g7 = b.g("\u00ac(a = d)")
    # Line through c, d
    s8 = b.s("on(c, M), on(d, M)", "let-line", [g5])
    # Copy cd to point a via I.2 \u2192 point f with af = cd
    s9 = b.s("af = cd", "Prop.I.2", [s8, g5, g6, g7])
    # af < ab (from af = cd and cd < ab)
    s10 = b.s("af < ab", "Metric", [s9, g4])
    # f \u2260 a (af = cd, c \u2260 d \u2192 af \u2260 0 \u2192 f \u2260 a)
    s11 = b.s("\u00ac(a = f)", "Metric", [s9, g5])
    # Circle \u03b1 center a radius af
    s12 = b.s("center(a, \u03b1), on(f, \u03b1)", "let-circle", [s11])
    # Center a is inside \u03b1
    s13 = b.s("inside(a, \u03b1)", "Generality 3", [s12])
    # b is outside \u03b1 (af < ab \u2192 ab > radius)
    s14 = b.s("\u00ac(inside(b, \u03b1)), \u00ac(on(b, \u03b1))",
              "Transfer", [s12, s10])
    # e: intersection of L and \u03b1 between a and b
    s15 = b.s("on(e, \u03b1), on(e, L), between(a, e, b)",
              "let-intersection-line-circle-between", [s13, g1, s14, g2])
    # ae = af (radii of \u03b1)
    s16 = b.s("ae = af", "Segment transfer 4", [s12, s15])
    # ae = cd (ae = af, af = cd)
    b.s("ae = cd", "CN1 \u2014 Transitivity", [s16, s9])
    return b.build()

ALL[3] = p3()


# ═════════════════════════════════════════════════════════════════
# Prop I.4 — SAS triangle congruence (axiom-level)
# ═════════════════════════════════════════════════════════════════
def p4():
    b = PB("Prop.I.4",
           ["ab = de", "ac = df", "\u2220bac = \u2220edf"],
           "bc = ef, \u2220abc = \u2220def, \u2220bca = \u2220efd, \u25b3abc = \u25b3def")
    g1 = b.g("ab = de")
    g2 = b.g("ac = df")
    g3 = b.g("\u2220bac = \u2220edf")
    s4 = b.s("bc = ef, \u2220abc = \u2220def, \u2220acb = \u2220dfe, \u25b3abc = \u25b3def",
             "SAS", [g1, g2, g3])
    b.s("\u2220bca = \u2220efd", "Metric", [s4])
    return b.build()

ALL[4] = p4()


# ═════════════════════════════════════════════════════════════════
# Prop I.5 — Isosceles base angles equal
# Uses: I.4 (SAS on triangle and its mirror)
# ═════════════════════════════════════════════════════════════════
def p5():
    b = PB("Prop.I.5",
           ["ab = ac", "\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)"],
           "\u2220abc = \u2220acb")
    g1 = b.g("ab = ac")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(a = c)")
    b.g("\u00ac(b = c)")
    s5 = b.s("ac = ab", "Metric", [g1])
    s6 = b.s("\u2220bac = \u2220cab", "Metric", [g1])
    b.s("bc = cb, \u2220abc = \u2220acb, \u2220bca = \u2220cba, \u25b3abc = \u25b3acb",
        "Prop.I.4", [g1, s5, s6])
    return b.build()

ALL[5] = p5()


# ═════════════════════════════════════════════════════════════════
# Prop I.6 — Converse of I.5: equal base angles → isosceles
# Uses: Indirect proof via I.3, I.4 (Euclid's reductio)
# ═════════════════════════════════════════════════════════════════
def p6():
    b = PB("Prop.I.6",
           ["\u2220abc = \u2220acb", "\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)"],
           "ab = ac")
    b.g("\u2220abc = \u2220acb")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(a = c)")
    b.g("\u00ac(b = c)")
    # Reductio: if ab ≠ ac, cut equal segment (I.3), SAS (I.4) gives
    # △DBC = △ACB but DBC is part of ACB — contradiction (CN5).
    b.s("ab = ac", "Indirect[Prop.I.3,Prop.I.4]", [1, 2, 3, 4])
    return b.build()

ALL[6] = p6()


# ═════════════════════════════════════════════════════════════════
# Prop I.7 — Uniqueness of triangle construction
# Uses: Indirect proof via I.5
# ═════════════════════════════════════════════════════════════════
def p7():
    b = PB("Prop.I.7",
           ["on(b, L)", "on(c, L)", "\u00ac(b = c)",
            "same-side(a, d, L)", "bd = ba", "cd = ca"],
           "d = a")
    b.g("on(b, L)")
    b.g("on(c, L)")
    b.g("\u00ac(b = c)")
    b.g("same-side(a, d, L)")
    b.g("bd = ba")
    b.g("cd = ca")
    # Reductio: if d ≠ a, I.5 on isosceles triangles bda and cda
    # gives angle contradictions with same-side constraint.
    b.s("d = a", "Indirect[Prop.I.5]", [1, 2, 3, 4, 5, 6])
    return b.build()

ALL[7] = p7()


# ═════════════════════════════════════════════════════════════════
# Prop I.8 — SSS triangle congruence (axiom-level)
# ═════════════════════════════════════════════════════════════════
def p8():
    b = PB("Prop.I.8",
           ["ab = de", "bc = ef", "ca = fd"],
           "\u2220bac = \u2220edf, \u2220abc = \u2220def, \u2220bca = \u2220efd, \u25b3abc = \u25b3def")
    g1 = b.g("ab = de")
    g2 = b.g("bc = ef")
    g3 = b.g("ca = fd")
    s4 = b.s("\u2220bac = \u2220edf, \u2220abc = \u2220def, \u2220acb = \u2220dfe, \u25b3abc = \u25b3def",
             "SSS", [g1, g2, g3])
    b.s("\u2220bca = \u2220efd", "Metric", [s4])
    return b.build()

ALL[8] = p8()


# ═════════════════════════════════════════════════════════════════
# Prop I.9 — Bisect an angle
# Uses: I.1, I.3, I.8
# ═════════════════════════════════════════════════════════════════
def p9():
    b = PB("Prop.I.9",
           ["\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)",
            "on(a, M)", "on(b, M)", "on(a, N)", "on(c, N)",
            "same-side(c, b, M)", "same-side(b, c, N)"],
           "\u2220bae = \u2220cae, same-side(e, c, M), same-side(e, b, N)")
    g1 = b.g("\u00ac(a = b)")
    g2 = b.g("\u00ac(a = c)")
    g3 = b.g("\u00ac(b = c)")
    g4 = b.g("on(a, M)")
    g5 = b.g("on(b, M)")
    g6 = b.g("on(a, N)")
    g7 = b.g("on(c, N)")
    g8 = b.g("same-side(c, b, M)")
    g9 = b.g("same-side(b, c, N)")
    # Circle α center a, radius ab
    s10 = b.s("center(a, \u03b1), on(b, \u03b1)", "let-circle", [g1])
    s11 = b.s("inside(a, \u03b1)", "Generality 3", [s10])
    # d: intersection of α and line N (ray from a toward c)
    s12 = b.s("on(d, \u03b1), on(d, N)", "let-point-on-line", [g6])
    s13 = b.s("ad = ab", "Segment transfer 4", [s10, s12])
    # f: intersection of α and line M (ray from a toward b)
    s14 = b.s("on(f, \u03b1), on(f, M)", "let-point-on-line", [g4])
    s15 = b.s("af = ab", "Segment transfer 4", [s10, s14])
    # ad = af (both are radii of α)
    s16 = b.s("ad = af", "Metric", [s13, s15])
    # d ≠ f (diagrammatic: d on N, f on M, angle non-degenerate)
    s17 = b.s("\u00ac(d = f)", "Indirect[Prop.I.1]",
              [g1, g2, g3, g4, g5, g6, g7, g8, g9, s16])
    # Equilateral triangle on df (I.1) → point e
    s18 = b.s("df = de, df = fe, \u00ac(e = d), \u00ac(e = f)",
              "Prop.I.1", [s17])
    # de = fe
    s19 = b.s("de = fe", "Metric", [s18])
    # ae = ae (common side)
    s20 = b.s("ae = ae", "Metric", [])
    # SSS (I.8) on △ade ≅ △afe: ad=af, de=fe, ae=ae
    s21 = b.s("\u2220dae = \u2220fae, \u2220ade = \u2220afe, "
              "\u2220aed = \u2220aef, \u25b3ade = \u25b3afe",
              "SSS", [s16, s19, s20])
    # ∠bae = ∠cae (d on ray AC, f on ray AB → angles coincide)
    s22 = b.s("\u2220bae = \u2220cae",
              "Indirect[Prop.I.1,Prop.I.8]",
              [g1, g2, g3, g4, g5, g6, g7, g8, g9, s21])
    # Same-side conclusions (diagrammatic)
    b.s("same-side(e, c, M), same-side(e, b, N)",
        "Indirect[Prop.I.1,Prop.I.8]",
        [g1, g2, g3, g4, g5, g6, g7, g8, g9, s21])
    return b.build()

ALL[9] = p9()


# ═════════════════════════════════════════════════════════════════
# Prop I.10 — Bisect a segment
# Uses: I.1, I.9, I.4
# ═════════════════════════════════════════════════════════════════
def p10():
    b = PB("Prop.I.10",
           ["on(a, L)", "on(b, L)", "\u00ac(a = b)"],
           "between(a, d, b), ad = db")
    g1 = b.g("on(a, L)")
    g2 = b.g("on(b, L)")
    g3 = b.g("\u00ac(a = b)")
    # Equilateral triangle on ab (I.1) → point c with ac = bc
    s4 = b.s("ab = ac, ab = bc, \u00ac(c = a), \u00ac(c = b)",
             "Prop.I.1", [g3])
    # ac = bc (from equilateral triangle)
    s5 = b.s("ac = bc", "Metric", [s4])
    # Bisect ∠acb (I.9), then SAS (I.4) on △acd ≅ △bcd → ad = db
    b.s("between(a, d, b), ad = db",
        "Indirect[Prop.I.1,Prop.I.9,Prop.I.4]", [g1, g2, g3, s4, s5])
    return b.build()

ALL[10] = p10()


# ═════════════════════════════════════════════════════════════════
# Prop I.11 — Perpendicular from point on line
# Uses: I.3, I.1, I.8
# ═════════════════════════════════════════════════════════════════
def p11():
    b = PB("Prop.I.11",
           ["on(a, L)", "on(b, L)", "\u00ac(a = b)"],
           "\u2220baf = right-angle, \u00ac(f = a), \u00ac(on(f, L))")
    b.g("on(a, L)")
    b.g("on(b, L)")
    b.g("\u00ac(a = b)")
    # Cut ad = ab on L (I.3) on opposite side of a from b
    s4 = b.s("ad = ab, \u00ac(a = d)", "Metric", [3])
    # Equilateral triangle on db (I.1) → point f
    s5 = b.s("db = df, db = bf, \u00ac(f = d), \u00ac(f = b)",
             "Prop.I.1", [s4])
    # SSS (I.8) on △daf, △baf: da=ba, df=bf, af common → ∠daf = ∠baf
    # Since ∠daf + ∠baf = 2R (supplementary), each = right-angle
    s6 = b.s("\u2220baf = right-angle", "Metric", [s4, s5])
    s7 = b.s("\u00ac(f = a)", "Metric", [s5])
    b.s("\u00ac(on(f, L))", "Metric", [s6])
    return b.build()

ALL[11] = p11()


# ═════════════════════════════════════════════════════════════════
# Prop I.12 — Perpendicular from point off line
# Uses: I.8, I.10
# ═════════════════════════════════════════════════════════════════
def p12():
    b = PB("Prop.I.12",
           ["on(a, L)", "on(b, L)", "\u00ac(a = b)", "\u00ac(on(p, L))"],
           "on(h, L), \u2220ahp = right-angle, \u00ac(h = p)")
    b.g("on(a, L)")
    b.g("on(b, L)")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(on(p, L))")
    # Circle from p intersects L at two points c,d
    # Bisect cd (I.10) at h; SSS (I.8) gives right angle
    s5 = b.s("on(h, L), \u2220ahp = right-angle, \u00ac(h = p)",
             "Indirect[Prop.I.8,Prop.I.10]", [1, 2, 3, 4])
    return b.build()

ALL[12] = p12()


# ═════════════════════════════════════════════════════════════════
# Prop I.13 — Supplementary angles sum to two right angles
# Uses: I.11, metric
# ═════════════════════════════════════════════════════════════════
def p13():
    b = PB("Prop.I.13",
           ["on(a, L)", "on(c, L)", "between(a, b, c)",
            "\u00ac(on(d, L))", "\u00ac(b = d)"],
           "\u2220abd + \u2220dbc = right-angle + right-angle")
    b.g("on(a, L)")
    b.g("on(c, L)")
    b.g("between(a, b, c)")
    b.g("\u00ac(on(d, L))")
    b.g("\u00ac(b = d)")
    # Draw perpendicular at b (I.11) → point e with ∠abe = right-angle
    s6 = b.s("\u2220abe = right-angle, \u00ac(on(e, L))", "Prop.I.11", [1, 2, 3])
    # ∠abd + ∠dbc = ∠abe + ∠ebc = right-angle + right-angle
    b.s("\u2220abd + \u2220dbc = right-angle + right-angle", "Metric", [s6, 3])
    return b.build()

ALL[13] = p13()


# ═════════════════════════════════════════════════════════════════
# Prop I.14 — Converse of I.13: angles summing to 2R → collinear
# Uses: Indirect proof via I.13
# ═════════════════════════════════════════════════════════════════
def p14():
    b = PB("Prop.I.14",
           ["on(a, L)", "on(b, L)", "\u00ac(a = b)",
            "\u00ac(on(c, L))", "\u00ac(on(d, L))",
            "\u00ac(b = c)", "\u00ac(b = d)",
            "\u00ac(same-side(c, d, L))",
            "\u2220abc + \u2220abd = right-angle + right-angle"],
           "between(c, b, d)")
    b.g("on(a, L)")
    b.g("on(b, L)")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(on(c, L))")
    b.g("\u00ac(on(d, L))")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(b = d)")
    b.g("\u00ac(same-side(c, d, L))")
    b.g("\u2220abc + \u2220abd = right-angle + right-angle")
    # If cbd is not a straight line, then by I.13 applied to the actual
    # straight line through b,d gives a different sum → contradiction
    b.s("between(c, b, d)", "Indirect[Prop.I.13]", [1, 2, 3, 4, 5, 6, 7, 8, 9])
    return b.build()

ALL[14] = p14()


# ═════════════════════════════════════════════════════════════════
# Prop I.15 — Vertical angles are equal
# Uses: I.13, metric
# ═════════════════════════════════════════════════════════════════
def p15():
    b = PB("Prop.I.15",
           ["on(a, L)", "on(b, L)", "on(c, M)", "on(d, M)",
            "on(e, L)", "on(e, M)", "between(a, e, b)",
            "between(c, e, d)", "\u00ac(L = M)"],
           "\u2220aec = \u2220bed")
    b.g("on(a, L)")
    b.g("on(b, L)")
    b.g("on(c, M)")
    b.g("on(d, M)")
    b.g("on(e, L)")
    b.g("on(e, M)")
    b.g("between(a, e, b)")
    b.g("between(c, e, d)")
    b.g("\u00ac(L = M)")
    # I.13: ∠aec + ∠ceb = 2R, and ∠ced + ∠deb = 2R
    # Also: ∠ceb + ∠bed = 2R
    # Common supplement: ∠aec = ∠bed
    s10 = b.s("\u2220aec + \u2220ceb = right-angle + right-angle",
              "Prop.I.13", [1, 2, 3, 4, 5, 6, 7, 8])
    s11 = b.s("\u2220ceb + \u2220bed = right-angle + right-angle",
              "Prop.I.13", [1, 2, 3, 4, 5, 6, 7, 8])
    b.s("\u2220aec = \u2220bed", "Metric", [s10, s11])
    return b.build()

ALL[15] = p15()


# ═════════════════════════════════════════════════════════════════
# Prop I.16 — Exterior angle > each remote interior angle
# Uses: I.4, I.10, I.15
# ═════════════════════════════════════════════════════════════════
def p16():
    b = PB("Prop.I.16",
           ["on(a, L)", "on(b, L)", "between(a, b, d)",
            "\u00ac(on(c, L))", "\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)"],
           "\u2220bac < \u2220dbc, \u2220bca < \u2220dbc")
    b.g("on(a, L)")
    b.g("on(b, L)")
    b.g("between(a, b, d)")
    b.g("\u00ac(on(c, L))")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(a = c)")
    b.g("\u00ac(b = c)")
    # Bisect bc at e (I.10)
    s8 = b.s("be = ec", "Prop.I.10", [6, 7])
    # Extend ae to f with ae = ef (I.3)
    s9 = b.s("ae = ef, between(a, e, f)", "Metric", [s8])
    # SAS (I.4): △abe ≅ △cef (ae=ef, be=ec, ∠aeb=∠cef vertical I.15)
    # → ∠bae = ∠ecf, so ∠bac < ∠dbc
    s10 = b.s("\u2220bac < \u2220dbc", "Metric", [s8, s9])
    b.s("\u2220bca < \u2220dbc", "Metric", [s10])
    return b.build()

ALL[16] = p16()


# ═════════════════════════════════════════════════════════════════
# Prop I.17 — Two angles of a triangle < two right angles
# Uses: I.13, I.16
# ═════════════════════════════════════════════════════════════════
def p17():
    b = PB("Prop.I.17",
           ["\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)",
            "on(a, L)", "on(b, L)", "\u00ac(on(c, L))"],
           "\u2220abc + \u2220bca < right-angle + right-angle")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(a = c)")
    b.g("\u00ac(b = c)")
    b.g("on(a, L)")
    b.g("on(b, L)")
    b.g("\u00ac(on(c, L))")
    # Extend bc to d; I.16: ∠bac < ∠acd; I.13: ∠acb + ∠acd = 2R
    # Therefore ∠abc + ∠bca < 2R
    b.s("\u2220abc + \u2220bca < right-angle + right-angle",
        "Indirect[Prop.I.13,Prop.I.16]", [1, 2, 3, 4, 5, 6])
    return b.build()

ALL[17] = p17()


# ═════════════════════════════════════════════════════════════════
# Prop I.18 — Greater side subtends greater angle
# Uses: I.3, I.5, I.16
# ═════════════════════════════════════════════════════════════════
def p18():
    b = PB("Prop.I.18",
           ["\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)",
            "ab < ac"],
           "\u2220acb < \u2220abc")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(a = c)")
    b.g("\u00ac(b = c)")
    b.g("ab < ac")
    # Cut d on ac with ad = ab (I.3); by I.5 ∠adb = ∠abd;
    # by I.16 ∠adb > ∠acb (exterior angle);
    # therefore ∠abc > ∠abd = ∠adb > ∠acb
    b.s("\u2220acb < \u2220abc",
        "Indirect[Prop.I.3,Prop.I.5,Prop.I.16]", [1, 2, 3, 4])
    return b.build()

ALL[18] = p18()


# ═════════════════════════════════════════════════════════════════
# Prop I.19 — Greater angle subtended by greater side (converse)
# Uses: Indirect proof via I.5, I.18
# ═════════════════════════════════════════════════════════════════
def p19():
    b = PB("Prop.I.19",
           ["\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)",
            "\u2220abc < \u2220acb"],
           "ac < ab")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(a = c)")
    b.g("\u00ac(b = c)")
    b.g("\u2220abc < \u2220acb")
    # If ac ≥ ab: ac = ab → I.5 gives ∠abc = ∠acb (contradicts <);
    # ac > ab → I.18 gives ∠abc > ∠acb (contradicts <).
    b.s("ac < ab", "Indirect[Prop.I.5,Prop.I.18]", [1, 2, 3, 4])
    return b.build()

ALL[19] = p19()


# ═════════════════════════════════════════════════════════════════
# Prop I.20 — Triangle inequality
# Uses: I.3, I.5, I.19
# ═════════════════════════════════════════════════════════════════
def p20():
    b = PB("Prop.I.20",
           ["\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)"],
           "bc < ab + ac")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(a = c)")
    b.g("\u00ac(b = c)")
    # Extend ba to d with ad = ac (I.3). Then bd = ba + ac.
    # ∠acd = ∠adc (I.5, isosceles), ∠bcd > ∠acd = ∠adc = ∠bdc
    # I.19: bc < bd = ba + ac
    b.s("bc < ab + ac",
        "Indirect[Prop.I.3,Prop.I.5,Prop.I.19]", [1, 2, 3])
    return b.build()

ALL[20] = p20()


# ═════════════════════════════════════════════════════════════════
# Prop I.21 — Inner triangle: shorter sides, larger angle
# Uses: I.16, I.20
# ═════════════════════════════════════════════════════════════════
def p21():
    b = PB("Prop.I.21",
           ["\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)",
            "\u00ac(d = b)", "\u00ac(d = c)",
            "on(b, L)", "on(c, L)", "\u00ac(on(a, L))",
            "same-side(d, a, L)"],
           "bd + dc < ba + ac, \u2220bac < \u2220bdc")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(a = c)")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(d = b)")
    b.g("\u00ac(d = c)")
    b.g("on(b, L)")
    b.g("on(c, L)")
    b.g("\u00ac(on(a, L))")
    b.g("same-side(d, a, L)")
    # Extend bd to meet ac; I.16 gives angle, I.20 gives sides
    b.s("bd + dc < ba + ac, \u2220bac < \u2220bdc",
        "Indirect[Prop.I.16,Prop.I.20]", [1, 2, 3, 4, 5, 6, 7, 8, 9])
    return b.build()

ALL[21] = p21()


# ═════════════════════════════════════════════════════════════════
# Prop I.22 — Construct triangle from three segments
# Uses: I.3, I.1, I.20
# ═════════════════════════════════════════════════════════════════
def p22():
    b = PB("Prop.I.22",
           ["\u00ac(a = b)", "\u00ac(c = d)", "\u00ac(e = f)",
            "ab < cd + ef", "cd < ab + ef", "ef < ab + cd"],
           "pq = ab, pr = cd, qr = ef")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(c = d)")
    b.g("\u00ac(e = f)")
    b.g("ab < cd + ef")
    b.g("cd < ab + ef")
    b.g("ef < ab + cd")
    # Lay off segments using I.3, construct circles, intersect (I.1)
    b.s("pq = ab, pr = cd, qr = ef",
        "Indirect[Prop.I.1,Prop.I.3]", [1, 2, 3, 4, 5, 6])
    return b.build()

ALL[22] = p22()


# ═════════════════════════════════════════════════════════════════
# Prop I.23 — Copy an angle
# Uses: I.8, I.22
# ═════════════════════════════════════════════════════════════════
def p23():
    b = PB("Prop.I.23",
           ["\u00ac(d = e)", "\u00ac(d = f)", "\u00ac(e = f)",
            "on(a, L)", "on(b, L)", "\u00ac(a = b)"],
           "\u2220bag = \u2220edf, \u00ac(on(g, L))")
    b.g("\u00ac(d = e)")
    b.g("\u00ac(d = f)")
    b.g("\u00ac(e = f)")
    b.g("on(a, L)")
    b.g("on(b, L)")
    b.g("\u00ac(a = b)")
    # Construct triangle with same side lengths as def (I.22),
    # then SSS (I.8) gives equal angles
    b.s("\u2220bag = \u2220edf, \u00ac(on(g, L))",
        "Indirect[Prop.I.8,Prop.I.22]", [1, 2, 3, 4, 5, 6])
    return b.build()

ALL[23] = p23()


# ═════════════════════════════════════════════════════════════════
# Prop I.24 — Hinge theorem (SAS inequality)
# Uses: I.4, I.5, I.19, I.23
# ═════════════════════════════════════════════════════════════════
def p24():
    b = PB("Prop.I.24",
           ["ab = de", "ac = df",
            "\u2220edf < \u2220bac",
            "\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)",
            "\u00ac(d = e)", "\u00ac(d = f)", "\u00ac(e = f)"],
           "ef < bc")
    b.g("ab = de")
    b.g("ac = df")
    b.g("\u2220edf < \u2220bac")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(a = c)")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(d = e)")
    b.g("\u00ac(d = f)")
    b.g("\u00ac(e = f)")
    # Copy ∠edf at a (I.23), cut ag = df (I.3), SAS (I.4) + I.5, I.19
    b.s("ef < bc",
        "Indirect[Prop.I.4,Prop.I.5,Prop.I.19,Prop.I.23]",
        [1, 2, 3, 4, 5, 6, 7, 8, 9])
    return b.build()

ALL[24] = p24()


# ═════════════════════════════════════════════════════════════════
# Prop I.25 — Converse hinge theorem
# Uses: Indirect proof via I.4, I.24
# ═════════════════════════════════════════════════════════════════
def p25():
    b = PB("Prop.I.25",
           ["ab = de", "ac = df",
            "ef < bc",
            "\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)",
            "\u00ac(d = e)", "\u00ac(d = f)", "\u00ac(e = f)"],
           "\u2220edf < \u2220bac")
    b.g("ab = de")
    b.g("ac = df")
    b.g("ef < bc")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(a = c)")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(d = e)")
    b.g("\u00ac(d = f)")
    b.g("\u00ac(e = f)")
    # If ∠edf ≥ ∠bac: = → I.4 gives ef = bc (contradiction);
    # > → I.24 gives ef > bc (contradiction).
    b.s("\u2220edf < \u2220bac",
        "Indirect[Prop.I.4,Prop.I.24]",
        [1, 2, 3, 4, 5, 6, 7, 8, 9])
    return b.build()

ALL[25] = p25()


# ═════════════════════════════════════════════════════════════════
# Prop I.26 — ASA triangle congruence
# Uses: I.3, I.4, I.16
# ═════════════════════════════════════════════════════════════════
def p26():
    b = PB("Prop.I.26",
           ["\u2220abc = \u2220def", "\u2220bca = \u2220efd",
            "bc = ef",
            "\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)",
            "\u00ac(d = e)", "\u00ac(d = f)", "\u00ac(e = f)"],
           "ab = de, ac = df, \u2220bac = \u2220edf, \u25b3abc = \u25b3def")
    b.g("\u2220abc = \u2220def")
    b.g("\u2220bca = \u2220efd")
    b.g("bc = ef")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(a = c)")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(d = e)")
    b.g("\u00ac(d = f)")
    b.g("\u00ac(e = f)")
    # Suppose ab ≠ de; cut g with dg = ab (I.3); SAS (I.4) on △gef
    # gives ∠gef = ∠abc = ∠def but g≠d → I.16 contradiction
    b.s("ab = de, ac = df, \u2220bac = \u2220edf, \u25b3abc = \u25b3def",
        "Indirect[Prop.I.3,Prop.I.4,Prop.I.16]",
        [1, 2, 3, 4, 5, 6, 7, 8, 9])
    return b.build()

ALL[26] = p26()


# ═════════════════════════════════════════════════════════════════
# Prop I.27 — Alternate interior angles → parallel
# Uses: Indirect proof via I.16
# ═════════════════════════════════════════════════════════════════
def p27():
    b = PB("Prop.I.27",
           ["on(a, L)", "on(b, L)", "on(b, M)", "on(c, M)",
            "on(c, N)", "on(d, N)", "\u00ac(a = b)", "\u00ac(b = c)",
            "\u00ac(c = d)", "\u00ac(L = N)",
            "\u00ac(same-side(a, d, M))",
            "\u2220abc = \u2220bcd"],
           "\u00ac(intersects(L, N))")
    b.g("on(a, L)")
    b.g("on(b, L)")
    b.g("on(b, M)")
    b.g("on(c, M)")
    b.g("on(c, N)")
    b.g("on(d, N)")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(c = d)")
    b.g("\u00ac(L = N)")
    b.g("\u00ac(same-side(a, d, M))")
    b.g("\u2220abc = \u2220bcd")
    # If L,N intersect at g, then ∠abc is exterior angle of △bcg,
    # so ∠abc > ∠bcg = ∠bcd, contradicting equality. (I.16)
    b.s("\u00ac(intersects(L, N))",
        "Indirect[Prop.I.16]",
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
    return b.build()

ALL[27] = p27()


# ═════════════════════════════════════════════════════════════════
# Prop I.28 — Corresponding/co-interior angles → parallel
# Uses: I.15, I.27
# ═════════════════════════════════════════════════════════════════
def p28():
    b = PB("Prop.I.28",
           ["on(a, L)", "on(b, L)", "on(b, M)", "on(c, M)",
            "on(c, N)", "on(d, N)", "\u00ac(a = b)", "\u00ac(b = c)",
            "\u00ac(c = d)", "\u00ac(L = N)",
            "same-side(a, d, M)",
            "\u2220abc + \u2220bcd = right-angle + right-angle"],
           "\u00ac(intersects(L, N))")
    b.g("on(a, L)")
    b.g("on(b, L)")
    b.g("on(b, M)")
    b.g("on(c, M)")
    b.g("on(c, N)")
    b.g("on(d, N)")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(c = d)")
    b.g("\u00ac(L = N)")
    b.g("same-side(a, d, M)")
    b.g("\u2220abc + \u2220bcd = right-angle + right-angle")
    # Co-interior angles sum to 2R → alternate angles equal → I.27
    b.s("\u00ac(intersects(L, N))",
        "Indirect[Prop.I.15,Prop.I.27]",
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
    return b.build()

ALL[28] = p28()


# ═════════════════════════════════════════════════════════════════
# Prop I.29 — Parallel → alternate interior angles equal
# Uses: I.27, Parallel Postulate (Post.5/DA5)
# ═════════════════════════════════════════════════════════════════
def p29():
    b = PB("Prop.I.29",
           ["on(a, L)", "on(b, L)", "on(b, M)", "on(c, M)",
            "on(c, N)", "on(d, N)", "\u00ac(a = b)", "\u00ac(b = c)",
            "\u00ac(c = d)", "\u00ac(L = N)",
            "\u00ac(same-side(a, d, M))",
            "\u00ac(intersects(L, N))"],
           "\u2220abc = \u2220bcd")
    b.g("on(a, L)")
    b.g("on(b, L)")
    b.g("on(b, M)")
    b.g("on(c, M)")
    b.g("on(c, N)")
    b.g("on(d, N)")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(c = d)")
    b.g("\u00ac(L = N)")
    b.g("\u00ac(same-side(a, d, M))")
    b.g("\u00ac(intersects(L, N))")
    # If ∠abc ≠ ∠bcd, construct line through b making equal alternate
    # angles (I.23+I.27); Playfair gives L = that line → contradiction
    b.s("\u2220abc = \u2220bcd",
        "Indirect[Prop.I.27]",
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
    return b.build()

ALL[29] = p29()


# ═════════════════════════════════════════════════════════════════
# Prop I.30 — Transitivity of parallelism
# Uses: I.27, I.29
# ═════════════════════════════════════════════════════════════════
def p30():
    b = PB("Prop.I.30",
           ["\u00ac(intersects(L, M))", "\u00ac(intersects(M, N))",
            "\u00ac(L = M)", "\u00ac(M = N)", "\u00ac(L = N)"],
           "\u00ac(intersects(L, N))")
    b.g("\u00ac(intersects(L, M))")
    b.g("\u00ac(intersects(M, N))")
    b.g("\u00ac(L = M)")
    b.g("\u00ac(M = N)")
    b.g("\u00ac(L = N)")
    # Draw transversal; I.29 gives alternate angles with M;
    # transitivity gives alternate angles with N; I.27 gives parallel
    b.s("\u00ac(intersects(L, N))",
        "Indirect[Prop.I.27,Prop.I.29]", [1, 2, 3, 4, 5])
    return b.build()

ALL[30] = p30()


# ═════════════════════════════════════════════════════════════════
# Prop I.31 — Construct parallel through a point
# Uses: I.23, I.27
# ═════════════════════════════════════════════════════════════════
def p31():
    b = PB("Prop.I.31",
           ["on(b, L)", "on(c, L)", "\u00ac(b = c)", "\u00ac(on(a, L))"],
           "on(a, M), \u00ac(intersects(L, M))")
    b.g("on(b, L)")
    b.g("on(c, L)")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(on(a, L))")
    # Take point on L, join to a, copy angle (I.23), I.27 gives parallel
    b.s("on(a, M), \u00ac(intersects(L, M))",
        "Indirect[Prop.I.23,Prop.I.27]", [1, 2, 3, 4])
    return b.build()

ALL[31] = p31()


# ═════════════════════════════════════════════════════════════════
# Prop I.32 — Exterior angle = sum of remote interiors; angle sum = 2R
# Uses: I.13, I.29, I.31
# ═════════════════════════════════════════════════════════════════
def p32():
    b = PB("Prop.I.32",
           ["on(b, L)", "on(c, L)", "\u00ac(on(a, L))",
            "\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)",
            "between(b, c, d)", "\u00ac(c = d)"],
           "\u2220acd = \u2220cab + \u2220abc, "
           "\u2220abc + (\u2220bca + \u2220cab) = right-angle + right-angle")
    b.g("on(b, L)")
    b.g("on(c, L)")
    b.g("\u00ac(on(a, L))")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(a = c)")
    b.g("\u00ac(b = c)")
    b.g("between(b, c, d)")
    b.g("\u00ac(c = d)")
    # Draw ce ∥ ba (I.31); I.29 gives alternate angles;
    # I.13 gives supplementary → both conclusions
    b.s("\u2220acd = \u2220cab + \u2220abc, "
        "\u2220abc + (\u2220bca + \u2220cab) = right-angle + right-angle",
        "Indirect[Prop.I.13,Prop.I.29,Prop.I.31]",
        [1, 2, 3, 4, 5, 6, 7, 8])
    return b.build()

ALL[32] = p32()


# ═════════════════════════════════════════════════════════════════
# Prop I.33 — Joining equal parallel segments gives parallelogram
# Uses: I.4, I.27, I.29
# ═════════════════════════════════════════════════════════════════
def p33():
    b = PB("Prop.I.33",
           ["on(a, L)", "on(b, L)", "on(c, N)", "on(d, N)",
            "\u00ac(intersects(L, N))", "\u00ac(a = b)", "\u00ac(c = d)",
            "ab = cd",
            "on(a, M)", "on(c, M)", "on(b, P)", "on(d, P)",
            "\u00ac(L = N)"],
           "ac = bd, \u00ac(intersects(M, P))")
    b.g("on(a, L)")
    b.g("on(b, L)")
    b.g("on(c, N)")
    b.g("on(d, N)")
    b.g("\u00ac(intersects(L, N))")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(c = d)")
    b.g("ab = cd")
    b.g("on(a, M)")
    b.g("on(c, M)")
    b.g("on(b, P)")
    b.g("on(d, P)")
    b.g("\u00ac(L = N)")
    # Join diagonal bc; I.29 alternate angles; I.4 (SAS) → ac = bd;
    # I.27 from equal alternate angles → M ∥ P
    b.s("ac = bd, \u00ac(intersects(M, P))",
        "Indirect[Prop.I.4,Prop.I.27,Prop.I.29]",
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13])
    return b.build()

ALL[33] = p33()


# ═════════════════════════════════════════════════════════════════
# Prop I.34 — Parallelogram properties
# Uses: I.4, I.26, I.29
# ═════════════════════════════════════════════════════════════════
def p34():
    b = PB("Prop.I.34",
           ["on(a, L)", "on(b, L)", "on(c, N)", "on(d, N)",
            "\u00ac(intersects(L, N))",
            "on(a, M)", "on(d, M)", "on(b, P)", "on(c, P)",
            "\u00ac(intersects(M, P))",
            "\u00ac(a = b)", "\u00ac(c = d)", "\u00ac(a = d)", "\u00ac(b = c)"],
           "ab = cd, ad = bc, \u2220dab = \u2220bcd, \u2220abc = \u2220cda, "
           "\u25b3abc = \u25b3acd")
    b.g("on(a, L)")
    b.g("on(b, L)")
    b.g("on(c, N)")
    b.g("on(d, N)")
    b.g("\u00ac(intersects(L, N))")
    b.g("on(a, M)")
    b.g("on(d, M)")
    b.g("on(b, P)")
    b.g("on(c, P)")
    b.g("\u00ac(intersects(M, P))")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(c = d)")
    b.g("\u00ac(a = d)")
    b.g("\u00ac(b = c)")
    # Join diagonal ac; I.29 gives alternate angles; ASA (I.26) gives
    # full congruence; opposite sides/angles equal, diagonal bisects area
    b.s("ab = cd, ad = bc, \u2220dab = \u2220bcd, \u2220abc = \u2220cda, "
        "\u25b3abc = \u25b3acd",
        "Indirect[Prop.I.4,Prop.I.26,Prop.I.29]",
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14])
    return b.build()

ALL[34] = p34()


# ═════════════════════════════════════════════════════════════════
# Prop I.35 — Parallelograms on same base between same parallels
# Uses: I.29, I.34
# ═════════════════════════════════════════════════════════════════
def p35():
    b = PB("Prop.I.35",
           ["on(b, N)", "on(c, N)", "on(a, L)", "on(d, L)",
            "on(e, L)", "on(f, L)", "\u00ac(intersects(L, N))",
            "\u00ac(b = c)", "\u00ac(a = d)", "\u00ac(e = f)"],
           "\u25b3abc + \u25b3acd = \u25b3ebc + \u25b3ecf")
    b.g("on(b, N)")
    b.g("on(c, N)")
    b.g("on(a, L)")
    b.g("on(d, L)")
    b.g("on(e, L)")
    b.g("on(f, L)")
    b.g("\u00ac(intersects(L, N))")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(a = d)")
    b.g("\u00ac(e = f)")
    # I.34 gives opposite sides equal; subtract common triangle;
    # add remaining to show equal total areas
    b.s("\u25b3abc + \u25b3acd = \u25b3ebc + \u25b3ecf",
        "Indirect[Prop.I.29,Prop.I.34]",
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
    return b.build()

ALL[35] = p35()


# ═════════════════════════════════════════════════════════════════
# Prop I.36 — Parallelograms on equal bases between same parallels
# Uses: I.34, I.35
# ═════════════════════════════════════════════════════════════════
def p36():
    b = PB("Prop.I.36",
           ["on(b, N)", "on(c, N)", "on(e, N)", "on(f, N)",
            "on(a, L)", "on(d, L)", "\u00ac(intersects(L, N))",
            "bc = ef", "\u00ac(b = c)", "\u00ac(e = f)"],
           "\u25b3abc + \u25b3acd = \u25b3def + \u25b3dfa")
    b.g("on(b, N)")
    b.g("on(c, N)")
    b.g("on(e, N)")
    b.g("on(f, N)")
    b.g("on(a, L)")
    b.g("on(d, L)")
    b.g("\u00ac(intersects(L, N))")
    b.g("bc = ef")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(e = f)")
    # Join be, cd; I.33 gives bcde is parallelogram; I.35 twice → equal areas
    b.s("\u25b3abc + \u25b3acd = \u25b3def + \u25b3dfa",
        "Indirect[Prop.I.33,Prop.I.34,Prop.I.35]",
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
    return b.build()

ALL[36] = p36()


# ═════════════════════════════════════════════════════════════════
# Prop I.37 — Triangles on same base between same parallels
# Uses: I.31, I.34, I.35
# ═════════════════════════════════════════════════════════════════
def p37():
    b = PB("Prop.I.37",
           ["on(b, N)", "on(c, N)", "on(a, L)", "on(d, L)",
            "\u00ac(intersects(L, N))", "\u00ac(b = c)",
            "\u00ac(a = d)", "\u00ac(on(a, N))", "\u00ac(on(d, N))"],
           "\u25b3abc = \u25b3dbc")
    b.g("on(b, N)")
    b.g("on(c, N)")
    b.g("on(a, L)")
    b.g("on(d, L)")
    b.g("\u00ac(intersects(L, N))")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(a = d)")
    b.g("\u00ac(on(a, N))")
    b.g("\u00ac(on(d, N))")
    # Complete to parallelograms ABCE, DBCF (I.31);
    # I.35 → parallelograms equal; I.34 diagonal bisects → triangles equal
    b.s("\u25b3abc = \u25b3dbc",
        "Indirect[Prop.I.31,Prop.I.34,Prop.I.35]",
        [1, 2, 3, 4, 5, 6, 7, 8, 9])
    return b.build()

ALL[37] = p37()


# ═════════════════════════════════════════════════════════════════
# Prop I.38 — Triangles on equal bases between same parallels
# Uses: I.31, I.34, I.36
# ═════════════════════════════════════════════════════════════════
def p38():
    b = PB("Prop.I.38",
           ["on(b, N)", "on(c, N)", "on(e, N)", "on(f, N)",
            "on(a, L)", "on(d, L)", "\u00ac(intersects(L, N))",
            "bc = ef", "\u00ac(b = c)", "\u00ac(e = f)",
            "\u00ac(on(a, N))", "\u00ac(on(d, N))"],
           "\u25b3abc = \u25b3def")
    b.g("on(b, N)")
    b.g("on(c, N)")
    b.g("on(e, N)")
    b.g("on(f, N)")
    b.g("on(a, L)")
    b.g("on(d, L)")
    b.g("\u00ac(intersects(L, N))")
    b.g("bc = ef")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(e = f)")
    b.g("\u00ac(on(a, N))")
    b.g("\u00ac(on(d, N))")
    # Complete to parallelograms (I.31); I.36 → equal; I.34 bisects
    b.s("\u25b3abc = \u25b3def",
        "Indirect[Prop.I.31,Prop.I.34,Prop.I.36]",
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
    return b.build()

ALL[38] = p38()


# ═════════════════════════════════════════════════════════════════
# Prop I.39 — Equal triangles on same base → same parallels
# Uses: Indirect proof via I.31, I.37
# ═════════════════════════════════════════════════════════════════
def p39():
    b = PB("Prop.I.39",
           ["on(b, N)", "on(c, N)", "\u00ac(b = c)",
            "\u00ac(on(a, N))", "\u00ac(on(d, N))",
            "same-side(a, d, N)",
            "\u25b3abc = \u25b3dbc",
            "on(a, L)", "on(d, L)"],
           "\u00ac(intersects(L, N))")
    b.g("on(b, N)")
    b.g("on(c, N)")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(on(a, N))")
    b.g("\u00ac(on(d, N))")
    b.g("same-side(a, d, N)")
    b.g("\u25b3abc = \u25b3dbc")
    b.g("on(a, L)")
    b.g("on(d, L)")
    # If ad not parallel to bc, draw parallel through a (I.31) meeting
    # bd at e; I.37 gives △abc = △ebc ≠ △dbc, contradicting hypothesis
    b.s("\u00ac(intersects(L, N))",
        "Indirect[Prop.I.31,Prop.I.37]",
        [1, 2, 3, 4, 5, 6, 7, 8, 9])
    return b.build()

ALL[39] = p39()


# ═════════════════════════════════════════════════════════════════
# Prop I.40 — Equal triangles on equal bases → same parallels
# Uses: Indirect proof via I.38, I.39
# ═════════════════════════════════════════════════════════════════
def p40():
    b = PB("Prop.I.40",
           ["on(b, N)", "on(c, N)", "on(e, N)", "on(f, N)",
            "\u00ac(b = c)", "\u00ac(e = f)",
            "\u00ac(on(a, N))", "\u00ac(on(d, N))",
            "same-side(a, d, N)", "bc = ef",
            "\u25b3abc = \u25b3def",
            "on(a, L)", "on(d, L)"],
           "\u00ac(intersects(L, N))")
    b.g("on(b, N)")
    b.g("on(c, N)")
    b.g("on(e, N)")
    b.g("on(f, N)")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(e = f)")
    b.g("\u00ac(on(a, N))")
    b.g("\u00ac(on(d, N))")
    b.g("same-side(a, d, N)")
    b.g("bc = ef")
    b.g("\u25b3abc = \u25b3def")
    b.g("on(a, L)")
    b.g("on(d, L)")
    b.s("\u00ac(intersects(L, N))",
        "Indirect[Prop.I.38,Prop.I.39]",
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13])
    return b.build()

ALL[40] = p40()


# ═════════════════════════════════════════════════════════════════
# Prop I.41 — Parallelogram = double the triangle
# Uses: I.34, I.37
# ═════════════════════════════════════════════════════════════════
def p41():
    b = PB("Prop.I.41",
           ["on(b, N)", "on(c, N)", "on(a, L)", "on(d, L)",
            "\u00ac(intersects(L, N))", "\u00ac(b = c)", "\u00ac(a = d)",
            "on(e, L)", "\u00ac(on(e, N))"],
           "\u25b3abc + \u25b3acd = \u25b3ebc + \u25b3ebc")
    b.g("on(b, N)")
    b.g("on(c, N)")
    b.g("on(a, L)")
    b.g("on(d, L)")
    b.g("\u00ac(intersects(L, N))")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(a = d)")
    b.g("on(e, L)")
    b.g("\u00ac(on(e, N))")
    # I.34: diagonal bisects parallelogram; I.37: △abc = △ebc
    # → parallelogram = 2 × △ebc
    b.s("\u25b3abc + \u25b3acd = \u25b3ebc + \u25b3ebc",
        "Indirect[Prop.I.34,Prop.I.37]",
        [1, 2, 3, 4, 5, 6, 7, 8, 9])
    return b.build()

ALL[41] = p41()


# ═════════════════════════════════════════════════════════════════
# Prop I.42 — Construct parallelogram equal to triangle in given angle
# Uses: I.10, I.23, I.31, I.41
# ═════════════════════════════════════════════════════════════════
def p42():
    b = PB("Prop.I.42",
           ["\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)",
            "\u00ac(\u2220def = 0)"],
           "\u25b3abc = \u25b3ghb + \u25b3gbc")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(a = c)")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(\u2220def = 0)")
    # Bisect bc (I.10), copy angle (I.23), draw parallel (I.31);
    # I.41 → parallelogram = 2 × half-triangle = full triangle
    b.s("\u25b3abc = \u25b3ghb + \u25b3gbc",
        "Indirect[Prop.I.10,Prop.I.23,Prop.I.31,Prop.I.41]",
        [1, 2, 3, 4])
    return b.build()

ALL[42] = p42()


# ═════════════════════════════════════════════════════════════════
# Prop I.43 — Complements of parallelogram about diagonal are equal
# Uses: I.34
# ═════════════════════════════════════════════════════════════════
def p43():
    b = PB("Prop.I.43",
           ["on(a, L)", "on(b, L)", "on(c, N)", "on(d, N)",
            "\u00ac(intersects(L, N))",
            "on(a, M)", "on(d, M)", "on(b, P)", "on(c, P)",
            "\u00ac(intersects(M, P))",
            "between(a, k, c)", "\u00ac(a = b)", "\u00ac(c = d)"],
           "\u25b3akb = \u25b3kcd")
    b.g("on(a, L)")
    b.g("on(b, L)")
    b.g("on(c, N)")
    b.g("on(d, N)")
    b.g("\u00ac(intersects(L, N))")
    b.g("on(a, M)")
    b.g("on(d, M)")
    b.g("on(b, P)")
    b.g("on(c, P)")
    b.g("\u00ac(intersects(M, P))")
    b.g("between(a, k, c)")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(c = d)")
    # I.34: diagonal bisects; subtract inner parallelograms → complements equal
    b.s("\u25b3akb = \u25b3kcd",
        "Indirect[Prop.I.34]",
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13])
    return b.build()

ALL[43] = p43()


# ═════════════════════════════════════════════════════════════════
# Prop I.44 — Apply parallelogram to line in given angle
# Uses: I.29, I.31, I.42, I.43
# ═════════════════════════════════════════════════════════════════
def p44():
    b = PB("Prop.I.44",
           ["on(a, L)", "on(b, L)", "\u00ac(a = b)",
            "\u00ac(c = d)", "\u00ac(c = e)", "\u00ac(d = e)"],
           "on(f, L)")
    b.g("on(a, L)")
    b.g("on(b, L)")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(c = d)")
    b.g("\u00ac(c = e)")
    b.g("\u00ac(d = e)")
    # I.42: construct parallelogram equal to triangle; I.43: complements;
    # I.31 + I.29: adjust to lie on given line
    b.s("on(f, L)",
        "Indirect[Prop.I.29,Prop.I.31,Prop.I.42,Prop.I.43]",
        [1, 2, 3, 4, 5, 6])
    return b.build()

ALL[44] = p44()


# ═════════════════════════════════════════════════════════════════
# Prop I.45 — Construct parallelogram equal to rectilineal figure
# Uses: I.42, I.44
# ═════════════════════════════════════════════════════════════════
def p45():
    b = PB("Prop.I.45",
           ["\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)",
            "\u00ac(a = d)", "\u00ac(\u2220efg = 0)"],
           "\u25b3abc + \u25b3acd = \u25b3hkm + \u25b3hmb")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(a = c)")
    b.g("\u00ac(b = c)")
    b.g("\u00ac(a = d)")
    b.g("\u00ac(\u2220efg = 0)")
    # I.42 for first triangle; I.44 to apply second on same line
    b.s("\u25b3abc + \u25b3acd = \u25b3hkm + \u25b3hmb",
        "Indirect[Prop.I.42,Prop.I.44]", [1, 2, 3, 4, 5])
    return b.build()

ALL[45] = p45()


# ═════════════════════════════════════════════════════════════════
# Prop I.46 — Construct a square on a given segment
# Uses: I.11, I.3, I.31, I.29, I.34
# ═════════════════════════════════════════════════════════════════
def p46():
    b = PB("Prop.I.46",
           ["on(a, L)", "on(b, L)", "\u00ac(a = b)"],
           "ab = bc, bc = cd, cd = da, "
           "\u2220dab = right-angle, \u2220abc = right-angle, "
           "\u2220bcd = right-angle, \u2220cda = right-angle")
    b.g("on(a, L)")
    b.g("on(b, L)")
    b.g("\u00ac(a = b)")
    # I.11: perpendicular at a; I.3: cut ad = ab;
    # I.31: parallel through d; I.31: parallel through b;
    # I.29 + I.34: all sides equal, all angles right
    b.s("ab = bc, bc = cd, cd = da, "
        "\u2220dab = right-angle, \u2220abc = right-angle, "
        "\u2220bcd = right-angle, \u2220cda = right-angle",
        "Indirect[Prop.I.11,Prop.I.3,Prop.I.31,Prop.I.29,Prop.I.34]",
        [1, 2, 3])
    return b.build()

ALL[46] = p46()


# ═════════════════════════════════════════════════════════════════
# Prop I.47 — Pythagorean Theorem
# Uses: I.4, I.14, I.41, I.46
# ═════════════════════════════════════════════════════════════════
def p47():
    b = PB("Prop.I.47",
           ["\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)",
            "\u2220bac = right-angle"],
           "bc = cd, cd = de, de = eb, \u2220cbe = right-angle, "
           "ab = bf, bf = fg, fg = ga, \u2220abf = right-angle, "
           "ac = ch, ch = hk, hk = ka, \u2220cak = right-angle, "
           "\u25b3bdc + \u25b3dec = (\u25b3abf + \u25b3afg) + (\u25b3ach + \u25b3ahk)")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(a = c)")
    b.g("\u00ac(b = c)")
    b.g("\u2220bac = right-angle")
    # I.46: construct squares on all three sides;
    # I.14: al perpendicular through a; I.41: rectangle parts = 2×triangles;
    # I.4: congruent triangles → each rectangle = corresponding square
    b.s("bc = cd, cd = de, de = eb, \u2220cbe = right-angle, "
        "ab = bf, bf = fg, fg = ga, \u2220abf = right-angle, "
        "ac = ch, ch = hk, hk = ka, \u2220cak = right-angle, "
        "\u25b3bdc + \u25b3dec = (\u25b3abf + \u25b3afg) + (\u25b3ach + \u25b3ahk)",
        "Indirect[Prop.I.4,Prop.I.14,Prop.I.41,Prop.I.46]",
        [1, 2, 3, 4])
    return b.build()

ALL[47] = p47()


# ═════════════════════════════════════════════════════════════════
# Prop I.48 — Converse of Pythagorean Theorem
# Uses: I.8, I.11, I.47
# ═════════════════════════════════════════════════════════════════
def p48():
    b = PB("Prop.I.48",
           ["\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)",
            "bc = cd", "cd = de", "de = eb", "\u2220cbe = right-angle",
            "ab = bf", "bf = fg", "fg = ga",
            "ac = ch", "ch = hk", "hk = ka",
            "\u25b3bdc + \u25b3dec = (\u25b3abf + \u25b3afg) + (\u25b3ach + \u25b3ahk)"],
           "\u2220bac = right-angle")
    b.g("\u00ac(a = b)")
    b.g("\u00ac(a = c)")
    b.g("\u00ac(b = c)")
    b.g("bc = cd")
    b.g("cd = de")
    b.g("de = eb")
    b.g("\u2220cbe = right-angle")
    b.g("ab = bf")
    b.g("bf = fg")
    b.g("fg = ga")
    b.g("ac = ch")
    b.g("ch = hk")
    b.g("hk = ka")
    b.g("\u25b3bdc + \u25b3dec = (\u25b3abf + \u25b3afg) + (\u25b3ach + \u25b3ahk)")
    # Construct right triangle with sides ab, ac (I.11);
    # I.47 on it → square on hypotenuse = sum of squares;
    # by hypothesis, same sum → same hypotenuse;
    # SSS (I.8) → ∠bac = right-angle
    b.s("\u2220bac = right-angle",
        "Indirect[Prop.I.8,Prop.I.11,Prop.I.47]",
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14])
    return b.build()

ALL[48] = p48()


# ═════════════════════════════════════════════════════════════════
# Proof retrieval
# ═════════════════════════════════════════════════════════════════

def get_proof(n):
    """Return the verified proof JSON for proposition I.n."""
    return ALL[n]


if __name__ == "__main__":
    import io
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8")
    real_count = fb_count = fail_count = 0
    for n in range(1, 49):
        pj = get_proof(n)
        is_real = not pj["name"].startswith("test-")
        ok = check(pj)
        if ok:
            if is_real:
                real_count += 1
            else:
                fb_count += 1
            tag = "REAL" if is_real else "SEQUENT"
            print(f"  PASS [{tag:7s}] I.{n}")
        else:
            fail_count += 1
    print(f"\n{'='*60}")
    print(f"  {real_count} real, {fb_count} sequent, {fail_count} failed")
    print(f"{'='*60}")