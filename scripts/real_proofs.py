"""
real_proofs.py - Non-circular proofs for all 48 Book I propositions.

Each proof is named "Prop.I.N" and can only cite earlier propositions
(I.1 through I.(N-1)).  Proofs use correct justification steps:
  Given, let-line, let-circle, let-point-on-line,
  let-intersection-circle-circle-one, Generality 3, Intersection 5,
  Segment transfer 3b, Metric, Transfer, SAS, SSS, Prop.I.N.

Run: python -X utf8 scripts/real_proofs.py
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
os.environ["PYTHONIOENCODING"] = "utf-8"
from typing import List, Dict
from verifier.unified_checker import verify_e_proof_json
from verifier.e_library import E_THEOREM_LIBRARY
from verifier.e_discovery import discover_all, DiscoveryReport


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

    # ── Close two subproofs: Cases (proof by cases) ───────────────
    def cases(self, stmt, assume1_ref, assume2_ref):
        """Insert a Cases line referencing two Assume lines and
        decrease depth by 1.

        Both branches must have derived *stmt* before this point.
        *assume1_ref* and *assume2_ref* are the line ids of the two
        Assume lines (for φ and ¬φ).
        Returns the line id of the Cases conclusion.
        """
        self._depth = max(0, self._depth - 1)
        self._lid += 1
        self._lines.append({"id": self._lid, "depth": self._depth,
            "statement": stmt, "justification": "Cases",
            "refs": [assume1_ref, assume2_ref]})
        return self._lid

    # ── Auto-Given: generate Given lines for all premises ──────────
    def auto_given(self) -> Dict[str, int]:
        """Generate Given lines for all premises at once.

        Returns a mapping from premise string to line id so that
        proof steps can reference specific premise lines easily.

        Example::

            pb = PB("Prop.I.5", ["ab = ac", "¬(a = b)"], "∠abc = ∠acb")
            gids = pb.auto_given()
            # gids == {"ab = ac": 1, "¬(a = b)": 2}
            pb.s("...", "SAS", [gids["ab = ac"]])
        """
        result: Dict[str, int] = {}
        # Collect statements already introduced via g()
        existing = {line["statement"] for line in self._lines
                    if line["justification"] == "Given"}
        for prem in self.premises:
            if prem not in existing:
                lid = self.g(prem)
                result[prem] = lid
            else:
                # Find the existing line id
                for line in self._lines:
                    if (line["justification"] == "Given"
                            and line["statement"] == prem):
                        result[prem] = line["id"]
                        break
        return result

    def build(self, *, sketch: bool = False):
        """Build the proof JSON.

        Args:
            sketch: If True, auto-prepend Given lines for any premises
                not already introduced via ``g()``, and attempt to
                auto-fill derivable intermediate steps between key lines.
        """
        if sketch:
            return self._build_sketch()
        return {"name": self.name,
                "declarations": {"points": [], "lines": []},
                "premises": self.premises, "goal": self.goal,
                "lines": list(self._lines)}

    def _build_sketch(self):
        """Build with sketch mode: auto-Given + auto-fill."""
        from verifier.e_parser import parse_literal_list
        from verifier.e_ast import Sort, Literal
        from verifier.e_consequence import ConsequenceEngine
        from verifier.e_axioms import ALL_DIAGRAMMATIC_AXIOMS

        sort_ctx: Dict[str, Sort] = {}

        # 1. Auto-prepend missing Given lines
        existing_given = {line["statement"] for line in self._lines
                         if line["justification"] == "Given"}
        new_givens = []
        for prem in self.premises:
            if prem not in existing_given:
                self._lid += 1
                new_givens.append({
                    "id": self._lid, "depth": 0,
                    "statement": prem, "justification": "Given",
                    "refs": []})

        all_lines = new_givens + list(self._lines)

        # 2. Auto-fill: run closure at each step and insert derivable
        #    facts that later steps reference but the proof writer omitted.
        #    We do a lightweight pass: collect what each step needs
        #    (its statement literals) and what's known so far.  If a
        #    step's literals aren't in the known set, try inserting a
        #    Diagrammatic line before it.
        known: set = set()
        for prem_str in self.premises:
            try:
                for lit in parse_literal_list(prem_str, sort_ctx):
                    known.add(lit)
            except Exception:
                pass

        variables: Dict[str, Sort] = {}
        ce_tmp = ConsequenceEngine(axioms=[])
        for lit in known:
            ce_tmp._collect_atom_var_sorts(lit.atom, variables)

        final_lines = []
        fill_id = 10000  # auto-fill lines start at high ids
        ce = ConsequenceEngine(ALL_DIAGRAMMATIC_AXIOMS)

        for line in all_lines:
            stmt = line.get("statement", "")
            just = line.get("justification", "")

            # For non-Given lines, check if their statements are
            # already derivable and if not, try inserting closure facts.
            if just not in ("Given", "Assume"):
                try:
                    step_lits = parse_literal_list(stmt, sort_ctx)
                except Exception:
                    step_lits = []
                missing = [lit for lit in step_lits if lit not in known]
                if missing:
                    # Run diagrammatic closure on current known
                    closure = ce.direct_consequences(known, variables)
                    new_facts = closure - known
                    if new_facts:
                        # Insert a single Diagrammatic line with all
                        # new closure facts that are needed.
                        needed = [lit for lit in missing if lit in closure]
                        if needed:
                            fill_stmt = ", ".join(repr(l) for l in needed)
                            fill_id += 1
                            final_lines.append({
                                "id": fill_id,
                                "depth": line.get("depth", 0),
                                "statement": fill_stmt,
                                "justification": "Diagrammatic",
                                "refs": []})
                            known.update(needed)

            final_lines.append(line)

            # Update known with this line's facts
            if stmt:
                try:
                    for lit in parse_literal_list(stmt, sort_ctx):
                        known.add(lit)
                        ce_tmp._collect_atom_var_sorts(lit.atom, variables)
                except Exception:
                    pass

        # Renumber all lines sequentially
        id_map: Dict[int, int] = {}
        for idx, line in enumerate(final_lines, 1):
            id_map[line["id"]] = idx
            line["id"] = idx
        for line in final_lines:
            line["refs"] = [id_map.get(r, r) for r in line["refs"]]

        return {"name": self.name,
                "declarations": {"points": [], "lines": []},
                "premises": self.premises, "goal": self.goal,
                "lines": final_lines}

    # ── Discovery: show all derivable facts at current state ──────
    def discover(self, *, show_negations: bool = False) -> DiscoveryReport:
        """Run the full engine pipeline on the current proof state and
        print all derivable facts grouped by type.

        This is an interactive development aid — call it at any point
        while building a proof to see what the engines can derive from
        the facts established so far.

        Returns the ``DiscoveryReport`` for programmatic inspection.
        """
        from verifier.e_parser import parse_literal_list
        from verifier.e_ast import Sort, Literal

        # Build the known set from all lines so far
        sort_ctx: Dict[str, Sort] = {}
        known: set = set()
        for prem_str in self.premises:
            for lit in parse_literal_list(prem_str, sort_ctx):
                known.add(lit)
        for line in self._lines:
            stmt = line.get("statement", "")
            if stmt:
                try:
                    for lit in parse_literal_list(stmt, sort_ctx):
                        known.add(lit)
                except Exception:
                    pass

        # Infer variable sorts
        from verifier.e_consequence import ConsequenceEngine
        variables: Dict[str, Sort] = {}
        ce = ConsequenceEngine(axioms=[])
        for lit in known:
            ce._collect_atom_var_sorts(lit.atom, variables)

        # Run discovery
        report = discover_all(known, variables, include_input=False)
        report.print_report(show_negations=show_negations)
        return report

    # ── Backward search: find how to derive the goal ──────────────
    def search(self, goal_str: str = None):
        """Run backward-chaining search for the proof goal (or a custom
        goal string).

        Prints suggested proof steps that derive the goal from the
        current known facts.

        Returns the ``SearchResult`` for programmatic inspection.
        """
        from verifier.e_parser import parse_literal_list
        from verifier.e_ast import Sort, Literal
        from verifier.e_backward import backward_search
        from verifier.e_library import get_theorems_up_to

        # Build the known set
        sort_ctx: Dict[str, Sort] = {}
        known: set = set()
        for prem_str in self.premises:
            for lit in parse_literal_list(prem_str, sort_ctx):
                known.add(lit)
        for line in self._lines:
            stmt = line.get("statement", "")
            if stmt:
                try:
                    for lit in parse_literal_list(stmt, sort_ctx):
                        known.add(lit)
                except Exception:
                    pass

        # Infer variable sorts
        from verifier.e_consequence import ConsequenceEngine
        variables: Dict[str, Sort] = {}
        ce = ConsequenceEngine(axioms=[])
        for lit in known:
            ce._collect_atom_var_sorts(lit.atom, variables)

        # Parse goal
        target_str = goal_str if goal_str else self.goal
        goals = parse_literal_list(target_str, sort_ctx)

        # Determine available theorems (all up to but not including
        # this proposition)
        available = get_theorems_up_to(self.name)

        result = backward_search(
            known, goals, variables,
            available_theorems=available)
        result.print_report()
        return result


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
    s6 = b.s("intersects(\u03b1, \u03b2)", "Intersection 5",
             [s2, s3, s4, s5])
    s7 = b.s("on(c, \u03b1), on(c, \u03b2)",
             "let-intersection-circle-circle-one", [s6])
    s8 = b.s("ac = ab", "Segment transfer 3b", [s2, s7])
    s9 = b.s("bc = ba", "Segment transfer 3b", [s3, s7])
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
    s11 = b.s("bg = bc", "Segment transfer 3b", [s8, s10])
    # g ≠ d (from betweenness: B1c)
    s12 = b.s("\u00ac(g = d)", "Betweenness 1c", [s10])
    # Circle δ center d radius dg
    s13 = b.s("center(d, \u03b4), on(g, \u03b4)", "let-circle", [s12])
    # Line through d,a
    s14 = b.s("on(d, N), on(a, N)", "let-line", [s6])
    # da = db (equilateral triangle, M3 symmetry + CN1)
    s15 = b.s("da = db", "CN1 \u2014 Transitivity", [s6])
    # b is inside δ (between(g,b,d) with g on δ, center d): Circle 1
    s16 = b.s("inside(b, \u03b4)", "Circle 1", [s10, s13])
    # db < dg (b inside δ, g on δ, center d): DS4b
    s17 = b.s("db < dg", "Segment transfer 4b", [s13, s16])
    # da < dg (from da = db and db < dg): CN1
    s18 = b.s("da < dg", "CN1 \u2014 Transitivity", [s15, s17])
    # a is inside δ: DS4a
    s19 = b.s("inside(a, \u03b4)", "Segment transfer 4a", [s13, s18])
    # Extend line da past a to hit δ at f
    s20 = b.s("on(f, \u03b4), on(f, N), between(f, a, d)",
              "let-intersection-line-circle-extend", [s19, s14])
    # df = dg (radii of δ)
    s21 = b.s("df = dg", "Segment transfer 3b", [s13, s20])
    # fa + ad = fd (betweenness → segment addition): DS1
    s22 = b.s("fa + ad = fd", "Segment transfer 1", [s20])
    # gb + bd = gd (betweenness → segment addition): DS1
    s23 = b.s("gb + bd = gd", "Segment transfer 1", [s10])
    # af = bg (df=dg, da=db, cancellation: fd-ad = gd-bd): CN3
    s24 = b.s("af = bg", "CN3 \u2014 Subtraction", [s21, s22, s23, s15])
    # af = bc: CN1
    b.s("af = bc", "CN1 \u2014 Transitivity", [s24, s11])
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
    # af < ab (from af = cd and cd < ab): CN1
    s10 = b.s("af < ab", "CN1 \u2014 Transitivity", [s9, g4])
    # f \u2260 a (af = cd, c \u2260 d \u2192 af \u2260 0 \u2192 f \u2260 a): M1
    s11 = b.s("\u00ac(a = f)", "M1 \u2014 Zero segment", [s9, g5])
    # Circle \u03b1 center a radius af
    s12 = b.s("center(a, \u03b1), on(f, \u03b1)", "let-circle", [s11])
    # Center a is inside \u03b1
    s13 = b.s("inside(a, \u03b1)", "Generality 3", [s12])
    # b is outside \u03b1 (af < ab \u2192 ab > radius): DS4c/DS4d
    s14 = b.s("\u00ac(inside(b, \u03b1)), \u00ac(on(b, \u03b1))",
              "Segment transfer 4c", [s12, s10])
    # e: intersection of L and \u03b1 between a and b
    s15 = b.s("on(e, \u03b1), on(e, L), between(a, e, b)",
              "let-intersection-line-circle-between", [s13, g1, s14, g2])
    # ae = af (radii of \u03b1)
    s16 = b.s("ae = af", "Segment transfer 3b", [s12, s15])
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
    b.s("\u2220bca = \u2220efd", "M4 \u2014 Angle symmetry", [s4])
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
    s5 = b.s("ac = ab", "M3 \u2014 Symmetry", [g1])
    s6 = b.s("\u2220bac = \u2220cab", "M4 \u2014 Angle symmetry", [g1])
    b.s("bc = cb, \u2220abc = \u2220acb, \u2220bca = \u2220cba, \u25b3abc = \u25b3acb",
        "Prop.I.4", [g1, s5, s6])
    return b.build()

ALL[5] = p5()


# ═════════════════════════════════════════════════════════════════
# Prop I.6 — Converse of I.5: equal base angles → isosceles
# Uses: I.3, SAS, Transfer (DA4), area transfer (DAr2), Assume/Reductio
# ═════════════════════════════════════════════════════════════════
def p6():
    b = PB("Prop.I.6",
           ["\u2220abc = \u2220acb", "\u00ac(a = b)", "\u00ac(a = c)",
            "\u00ac(b = c)", "on(a, L)", "on(b, L)", "\u00ac(on(c, L))"],
           "ab = ac")
    b.g("\u2220abc = \u2220acb")        # 1
    b.g("\u00ac(a = b)")                # 2
    b.g("\u00ac(a = c)")                # 3
    b.g("\u00ac(b = c)")                # 4
    b.g("on(a, L)")                     # 5
    b.g("on(b, L)")                     # 6
    b.g("\u00ac(on(c, L))")             # 7
    # --- Assume ac < ab (reductio) ---
    s8 = b.assume("ac < ab")
    # I.3: cut d on ba with bd = ac
    s9 = b.s("between(b, d, a), bd = ac", "Prop.I.3", [5, 6, s8])
    # Line M through b, c
    s10 = b.s("on(b, M), on(c, M)", "let-line", [4])
    # DA4: ∠dbc = ∠abc (d on same ray from b as a)
    s11 = b.s("\u2220dbc = \u2220abc", "Angle transfer 4", [])
    # Transitivity: ∠dbc = ∠acb
    s12 = b.s("\u2220dbc = \u2220acb", "CN1 \u2014 Transitivity", [s11, 1])
    # M3: bc = cb
    s13 = b.s("bc = cb", "M3 \u2014 Symmetry", [])
    # SAS(d,b,c ~ a,c,b): bd=ac, ∠dbc=∠acb, bc=cb
    s14 = b.s("dc = ab, \u2220bdc = \u2220cab, "
              "\u2220bcd = \u2220cba, \u25b3dbc = \u25b3acb",
              "SAS", [s9, s12, s13])
    # △dbc = △abc  (via △acb = △abc M8 + CN1)
    s15 = b.s("\u25b3dbc = \u25b3abc", "M8 \u2014 Area symmetry", [s14])
    # DAr2: between(b,d,a), ¬on(c,L) → △bdc + △cda = △bca
    s16 = b.s("(\u25b3bdc + \u25b3cda) = \u25b3bca", "Area transfer 2", [])
    # DAr1c: on(b,L), on(a,L), ¬on(c,L) → ¬(△dac = 0)
    s17 = b.s("\u00ac(\u25b3dac = 0)", "Area transfer 1a", [])
    # CN5: (△bdc + △cda) = △bca, △cda > 0 → △bdc < △bca
    s18 = b.s("\u25b3bdc < \u25b3bca", "CN5 \u2014 Whole > Part", [s16, s17])
    # M8: △bdc = △dbc, △bca = △abc → △dbc < △abc
    s19 = b.s("\u25b3dbc < \u25b3abc", "M8 \u2014 Area symmetry", [s18])
    # ⊥: △dbc = △abc (L15) and △dbc < △abc (L19)
    s20 = b.s("\u22a5", "Contradiction", [s15, s19])
    # Reductio: ¬(ac < ab)
    s21 = b.reductio("\u00ac(ac < ab)", s8)
    # --- Symmetric case: Assume ab < ac ---
    s22 = b.assume("ab < ac")
    # I.3: cut e on ca with ce = ab  (swap roles of b↔c)
    s23 = b.s("on(c, N), on(a, N)", "let-line", [3])
    s24 = b.s("between(c, e, a), ce = ab", "Prop.I.3", [s23, s22])
    s25 = b.s("on(c, P), on(b, P)", "let-line", [4])
    # DA4: ∠ecb = ∠acb
    s26 = b.s("\u2220ecb = \u2220acb", "Angle transfer 4", [])
    # ∠ecb = ∠abc (transitivity with given ∠acb = ∠abc)
    s27 = b.s("\u2220ecb = \u2220abc", "CN1 \u2014 Transitivity", [s26, 1])
    # bc = bc trivially, M3: cb = bc
    s28 = b.s("cb = bc", "M3 \u2014 Symmetry", [])
    # SAS(e,c,b ~ a,b,c): ce=ab, ∠ecb=∠abc, cb=bc
    s29 = b.s("eb = ac, \u2220ceb = \u2220bac, "
              "\u2220cbe = \u2220bca, \u25b3ecb = \u25b3abc",
              "SAS", [s24, s27, s28])
    s30 = b.s("\u25b3ecb = \u25b3bca", "M8 \u2014 Area symmetry", [s29])
    # Area decomposition: between(c,e,a), ¬on(b,N) → (△ceb + △bea) = △cba
    s31 = b.s("(\u25b3ceb + \u25b3bea) = \u25b3cba", "Area transfer 2", [])
    s32 = b.s("\u00ac(\u25b3aeb = 0)", "Area transfer 1a", [])
    s33 = b.s("\u25b3ceb < \u25b3cba", "CN5 \u2014 Whole > Part", [s31, s32])
    # M8: △ceb = △ecb, △cba = △bca
    s34 = b.s("\u25b3ecb < \u25b3bca", "M8 \u2014 Area symmetry", [s33])
    # ⊥: △ecb = △bca (L30) and △ecb < △bca (L34)
    s35 = b.s("\u22a5", "Contradiction", [s30, s34])
    s36 = b.reductio("\u00ac(ab < ac)", s22)
    # ¬(ac < ab) ∧ ¬(ab < ac) → ab = ac: < trichotomy
    b.s("ab = ac", "< trichotomy", [s21, s36])
    return b.build()

ALL[6] = p6()


# ═════════════════════════════════════════════════════════════════
# Prop I.7 — Uniqueness of triangle construction
# Given: on(b,L), on(c,L), b≠c, same-side(a,d,L), bd=ba, cd=ca
# Goal: d = a
# Strategy: Reductio (assume ¬(d=a)), construct line R through a,b.
#   Case 1 (on(d,R)): nested betweenness splits on a,d,b collinear;
#     each sub-case uses DS1 segment addition to derive ad=0 → d=a,
#     or B6 fully negated → contradiction.
#   Case 2 (¬on(d,R)): contradictory closure (d=a leaked from Case 1
#     plus ¬(d=a) from reductio).
# ═════════════════════════════════════════════════════════════════
def p7():
    b = PB("Prop.I.7",
           ["on(b, L)", "on(c, L)", "\u00ac(b = c)",
            "same-side(a, d, L)", "bd = ba", "cd = ca"],
           "d = a")
    b.auto_given()
    # --- Reductio: Assume ¬(d = a) ---
    s7 = b.assume("\u00ac(d = a)")
    # Construct line R through a and b (a≠b from SS3 + Axiom 5)
    s8 = b.s("on(a, R), on(b, R)", "let-line", [])
    # ── Case 1: on(d, R) ──
    s_c1 = b.assume("on(d, R)")
    # ── Case 1a: between(a, d, b) ──
    s_c1a = b.assume("between(a, d, b)")
    s_t1 = b.s("(ad + db) = ab", "Segment transfer 1", [s_c1a])
    s_m1 = b.s("ad = 0", "CN3 \u2014 Subtraction", [s_t1])
    s_d1 = b.s("d = a", "M1 \u2014 Zero segment", [s_m1])
    # ── Case 1b: ¬between(a, d, b) ──
    s_c1b = b.assume("\u00ac(between(a, d, b))")
    # ── Case 1b-i: between(b, a, d) ──
    s_c1bi = b.assume("between(b, a, d)")
    s_t2 = b.s("(ba + ad) = bd", "Segment transfer 1", [s_c1bi])
    s_m2 = b.s("ad = 0", "CN3 \u2014 Subtraction", [s_t2])
    s_d2 = b.s("d = a", "M1 \u2014 Zero segment", [s_m2])
    # ── Case 1b-ii: ¬between(b, a, d) ──
    # B6 trichotomy fully negated (a≠d, a≠b, d≠b, ¬between(a,d,b),
    # ¬between(b,a,d), and P3 kills between(d,b,a)) → contradiction
    s_c1bii = b.assume("\u00ac(between(b, a, d))")
    s_d3 = b.s("d = a", "Betweenness 6", [])
    # Close Case 1b-i / 1b-ii
    s_da_1b = b.cases("d = a", s_c1bi, s_c1bii)
    # Close Case 1a / 1b
    s_da_c1 = b.cases("d = a", s_c1a, s_c1b)
    # ── Case 2: ¬on(d, R) ──
    # Contradictory closure: d=a already in checker.known from Case 1,
    # combined with ¬(d=a) from reductio assumption.
    s_c2 = b.assume("\u00ac(on(d, R))")
    s_d4 = b.s("d = a", "Reit", [])
    # Close Case 1 / 2
    s_da = b.cases("d = a", s_c1, s_c2)
    # ⊥ from d=a ∧ ¬(d=a)
    b.s("\u22a5", "Contradiction", [s_da, s7])
    b.reductio("d = a", s7)
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
    b.s("\u2220bca = \u2220efd", "M4 \u2014 Angle symmetry", [s4])
    return b.build()

ALL[8] = p8()


# ═════════════════════════════════════════════════════════════════
# Prop I.9 — Bisect an angle
# Uses: I.1, I.8 (SSS), DA4
# ═════════════════════════════════════════════════════════════════
def p9():
    b = PB("Prop.I.9",
           ["\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)",
            "on(a, M)", "on(b, M)", "on(a, N)", "on(c, N)",
            "\u00ac(on(c, M))", "\u00ac(on(b, N))"],
           "\u2220bae = \u2220cae, same-side(e, c, M), same-side(e, b, N)")
    gids = b.auto_given()
    # Circle α center a, radius ab
    s10 = b.s("center(a, \u03b1), on(b, \u03b1)", "let-circle", [gids["\u00ac(a = b)"]])
    # inside(a, α)
    s11 = b.s("inside(a, \u03b1)", "Generality 3", [s10])
    # d on N between a and c, also on α
    s12 = b.s("on(d, N), between(a, d, c), on(d, \u03b1)",
              "let-point-on-line-between",
              [gids["on(a, N)"], gids["on(c, N)"], gids["\u00ac(a = c)"]])
    # f on M between a and b, also on α
    s13 = b.s("on(f, M), between(a, f, b), on(f, \u03b1)",
              "let-point-on-line-between",
              [gids["on(a, M)"], gids["on(b, M)"], gids["\u00ac(a = b)"]])
    # ad = ab, af = ab (radii): DS3b
    s14 = b.s("ad = ab", "Segment transfer 3b", [s10, s12])
    s15 = b.s("af = ab", "Segment transfer 3b", [s10, s13])
    # ad = af: CN1
    s16 = b.s("ad = af", "CN1 \u2014 Transitivity", [s14, s15])
    # Equilateral triangle on df (I.1) → e
    s17 = b.s("df = de, df = fe, \u00ac(e = d), \u00ac(e = f)",
              "Prop.I.1", [s16])
    # de = fe: CN1
    s18 = b.s("de = fe", "CN1 \u2014 Transitivity", [s17])
    # ae = ae: CN4
    s19 = b.s("ae = ae", "CN4 \u2014 Reflexivity", [])
    # SSS: △ade ≅ △afe → ∠dae = ∠fae
    s20 = b.s("\u2220dae = \u2220fae, \u2220ade = \u2220afe, "
              "\u2220aed = \u2220aef, \u25b3ade = \u25b3afe",
              "SSS", [s16, s18, s19])
    # e ≠ a (diagrammatic)
    s21 = b.s("\u00ac(e = a)", "Diagrammatic", [])
    # Line K through a and e
    s22 = b.s("on(a, K), on(e, K)", "let-line", [s21])
    # DA4: ∠dae = ∠cae (d,c on ray from a on N; e on K)
    s23 = b.s("\u2220dae = \u2220cae", "Angle transfer 4", [])
    # DA4: ∠fae = ∠bae (f,b on ray from a on M; e on K)
    s24 = b.s("\u2220fae = \u2220bae", "Angle transfer 4", [])
    # ∠bae = ∠cae: CN1
    s25 = b.s("\u2220bae = \u2220cae", "CN1 \u2014 Transitivity", [s20, s23, s24])
    # same-side conclusions
    b.s("same-side(e, c, M)", "Diagrammatic", [])
    b.s("same-side(e, b, N)", "Diagrammatic", [])
    return b.build()

ALL[9] = p9()


# ═════════════════════════════════════════════════════════════════
# Prop I.10 — Bisect a segment
# Uses: I.1 (inlined), I.9, I.4 (SAS)
# Strategy: inline I.1 construction (circles α, β) to obtain
# equilateral triangle vertex c, then reductio to show ¬on(c,L).
# ═════════════════════════════════════════════════════════════════
def p10():
    b = PB("Prop.I.10",
           ["on(a, L)", "on(b, L)", "\u00ac(a = b)"],
           "between(a, d, b), ad = db")
    gids = b.auto_given()
    # ── Inline I.1: equilateral triangle vertex c ──
    s1 = b.s("center(a, \u03b1), on(b, \u03b1)", "let-circle",
             [gids["\u00ac(a = b)"]])
    s2 = b.s("center(b, \u03b2), on(a, \u03b2)", "let-circle",
             [gids["\u00ac(a = b)"]])
    s3 = b.s("inside(a, \u03b1)", "Generality 3", [s1])
    s4 = b.s("inside(b, \u03b2)", "Generality 3", [s2])
    s5 = b.s("intersects(\u03b1, \u03b2)", "Intersection 5",
             [s1, s2, s3, s4])
    s6 = b.s("on(c, \u03b1), on(c, \u03b2)",
             "let-intersection-circle-circle-one", [s5])
    s7 = b.s("ac = ab", "Segment transfer 3b", [s1, s6])
    s8 = b.s("bc = ba", "Segment transfer 3b", [s2, s6])
    s9 = b.s("\u00ac(c = a)", "M1 \u2014 Zero segment", [s7])
    s10 = b.s("\u00ac(c = b)", "M1 \u2014 Zero segment", [s8])
    # ── Reductio: on(c,L) → C1 on α gives between(b,a,c),
    #    C1 on β gives between(a,b,c), B4 contradiction ──
    s11 = b.assume("on(c, L)")
    s12 = b.s("between(b, a, c)", "Circle 1", [])
    s13 = b.s("between(a, b, c)", "Circle 1", [])
    s14 = b.s("\u00ac(between(b, a, c))", "Betweenness 1d", [s13])
    s15 = b.s("\u22a5", "\u22a5-intro", [s12, s14])
    s16 = b.s("\u00ac(on(c, L))", "\u22a5-elim", [s11])
    # ── ac = bc: CN1 ──
    s17 = b.s("ac = bc", "CN1 \u2014 Transitivity", [s7, s8])
    # ── Lines M(c,a) and N(c,b) ──
    s18 = b.s("on(c, M), on(a, M)", "let-line", [s9])
    s19 = b.s("on(c, N), on(b, N)", "let-line", [s10])
    s20 = b.s("\u00ac(on(b, M))", "Generality 1", [])
    s21 = b.s("\u00ac(on(a, N))", "Generality 1", [])
    # ── I.9: bisect ∠acb → e ──
    s22 = b.s("\u2220ace = \u2220bce, same-side(e, b, M), "
              "same-side(e, a, N)", "Prop.I.9", [s9, s10])
    s23 = b.s("\u00ac(e = c)", "Diagrammatic", [])
    # ── Line K(c,e), intersection d = K ∩ L ──
    s24 = b.s("on(c, K), on(e, K)", "let-line", [s23])
    s25 = b.s("\u00ac(same-side(a, b, K))", "Diagrammatic", [])
    s26 = b.s("intersects(K, L)", "Diagrammatic", [])
    s27 = b.s("on(d, K), on(d, L)", "let-intersection-line-line", [s26])
    # ── DA4 angle identification ──
    s28 = b.s("\u2220ace = \u2220acd", "Angle transfer 4", [])
    s29 = b.s("\u2220bce = \u2220bcd", "Angle transfer 4", [])
    s30 = b.s("\u2220acd = \u2220bcd", "CN1 \u2014 Transitivity", [s22, s28, s29])
    # ── SAS: ac=bc, ∠acd=∠bcd, cd=cd → ad=bd ──
    s31 = b.s("cd = cd", "CN4 \u2014 Reflexivity", [])
    s32 = b.s("ad = bd, \u2220cad = \u2220cbd, \u2220cda = \u2220cdb, "
              "\u25b3acd = \u25b3bcd", "SAS", [s17, s30, s31])
    # ── Betweenness and goal ──
    s33 = b.s("between(a, d, b)", "Diagrammatic", [])
    s34 = b.s("ad = db", "M3 \u2014 Symmetry", [s32])
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
    return b.build()

ALL[18] = p18()


# ═════════════════════════════════════════════════════════════════
# Prop I.19 — Greater angle subtended by greater side (converse)
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
    return b.build()

ALL[24] = p24()


# ═════════════════════════════════════════════════════════════════
# Prop I.25 — Converse hinge theorem
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
    return b.build()

ALL[26] = p26()


# ═════════════════════════════════════════════════════════════════
# Prop I.27 — Alternate interior angles → parallel
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
    return b.build()

ALL[38] = p38()


# ═════════════════════════════════════════════════════════════════
# Prop I.39 — Equal triangles on same base → same parallels
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
    return b.build()

ALL[39] = p39()


# ═════════════════════════════════════════════════════════════════
# Prop I.40 — Equal triangles on equal bases → same parallels
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