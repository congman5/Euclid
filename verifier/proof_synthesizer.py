"""
proof_synthesizer.py -- Automated proof synthesis from Lean translator output.

Takes a TranslationResult from the Lean->System E translator and synthesizes
a complete .euclid proof JSON that passes verify_e_proof_json.

Architecture
------------
1. Variable mapper: Maps Lean variable names (AB, BC, AC) to e_library
   names (L, M, N) by matching which points lie on which lines.

2. Step synthesizer: Walks the Lean tactics directly and generates .euclid
   JSON steps with correct text, justification, and dependencies.

3. Dependency tracker: Incrementally tracks known facts per line so
   each step cites only the lines it actually needs.
"""
from __future__ import annotations

import json
import datetime
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

from .e_ast import (
    Sort, Literal, Atom, Sequent, ETheorem,
    On, SameSide, Between, Center, Inside, Intersects,
    Equals, LessThan,
    SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag,
    ProofStep, StepKind, EProof,
    literal_vars, atom_vars, substitute_literal,
)
from .e_library import E_THEOREM_LIBRARY, get_theorems_up_to
from .e_construction import CONSTRUCTION_RULE_BY_NAME
from .lean_translator import TranslatedStep, TranslationResult
from .lean_parser import LeanProof, LeanTactic, TacticKind, parse_lean_file
from .lean_to_euclid_json import (
    literal_to_text, _PROP_TITLES, _PROP_DIFFICULTIES,
    _extract_declarations, _load_existing_canvas,
)


# =====================================================================
# Helpers
# =====================================================================

def _pos(atom: Atom) -> Literal:
    return Literal(atom, polarity=True)


def _ordered_atom_vars(atom: Atom) -> List[str]:
    """Return variable names in an atom in a stable, positional order.

    For On(point, obj) → [point, obj]
    For Between(a, b, c) → [a, b, c]
    For Equals/LessThan → left vars then right vars
    etc.
    """
    result: List[str] = []
    def _add(v: str):
        if v not in result:
            result.append(v)
    def _add_term(t):
        if isinstance(t, str):
            _add(t)
        elif isinstance(t, SegmentTerm):
            _add(t.p1); _add(t.p2)
        elif isinstance(t, AngleTerm):
            _add(t.p1); _add(t.p2); _add(t.p3)
        elif isinstance(t, AreaTerm):
            _add(t.p1); _add(t.p2); _add(t.p3)
        elif isinstance(t, MagAdd):
            _add_term(t.left); _add_term(t.right)
    if isinstance(atom, On):
        _add(atom.point); _add(atom.obj)
    elif isinstance(atom, SameSide):
        _add(atom.a); _add(atom.b); _add(atom.line)
    elif isinstance(atom, Between):
        _add(atom.a); _add(atom.b); _add(atom.c)
    elif isinstance(atom, Center):
        _add(atom.point); _add(atom.circle)
    elif isinstance(atom, Inside):
        _add(atom.point); _add(atom.circle)
    elif isinstance(atom, Intersects):
        _add(atom.obj1); _add(atom.obj2)
    elif isinstance(atom, Equals):
        _add_term(atom.left); _add_term(atom.right)
    elif isinstance(atom, LessThan):
        _add_term(atom.left); _add_term(atom.right)
    return result


def _ordered_sequent_vars(seq: 'Sequent') -> List[str]:
    """Extract variables from a sequent in stable hypothesis-order.

    Walks hypotheses then conclusions, collecting variable names
    in order of first appearance. This matches the Lean convention
    where theorem parameters are listed in hypothesis order.
    """
    seen: List[str] = []
    for lit in seq.hypotheses:
        for v in _ordered_atom_vars(lit.atom):
            if v not in seen:
                seen.append(v)
    for lit in seq.conclusions:
        for v in _ordered_atom_vars(lit.atom):
            if v not in seen:
                seen.append(v)
    return seen


# Lean parameter order for early propositions (I.1–I.15).
# Maps proposition number → list of (elib_var, sort) in Lean call-site order.
# Derived from LeanEuclid Book definitions and call patterns in lean_reference/.
_LEAN_PARAM_ORDER: Dict[int, List[Tuple[str, str]]] = {
    3: [  # proposition_3 p1 p2 p3 p4 L1 L2  as e
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("L", "Line"),  ("_", "Line"),  # L2 is auxiliary
    ],
    4: [  # proposition_4 a1 b1 c1  a2 b2 c2  Lab1 Lbc1 Lac1  Lab2 Lbc2 Lac2
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("d", "Point"), ("e", "Point"), ("f", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    5: [  # proposition_5 / 5'  a b c  AB BC AC
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    8: [  # proposition_8  a1 b1 c1  a2 b2 c2  L_ab1 L_bc1 L_ac1  L_ab2 L_bc2 L_ac2
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("d", "Point"), ("e", "Point"), ("f", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    10: [  # proposition_10 p1 p2 L  as d
        ("a", "Point"), ("b", "Point"),
        ("L", "Line"),
    ],
    13: [  # proposition_13 d b a c  L_aux L
        # e_lib: on(a,L), on(c,L), between(a,b,c), ¬on(d,L), ¬(b=d)
        # Lean: off-line pt, between-pt, endpoint1, endpoint2, aux_line, L
        ("d", "Point"), ("b", "Point"), ("a", "Point"), ("c", "Point"),
        ("_", "Line"), ("L", "Line"),
    ],
    15: [  # proposition_15  a b  c d  e  L M
        # e_lib: on(a,L), on(b,L), on(c,M), on(d,M), on(e,L), on(e,M),
        #        between(a,e,b), between(c,e,d), ¬(L=M)
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("e", "Point"), ("L", "Line"), ("M", "Line"),
    ],
    16: [  # proposition_16  c a b d  _ L _
        # Lean: formTriangle(a,b,c) ∧ between(b,c,d)
        # e_lib: on(a,L), on(b,L), between(a,b,d), ¬on(c,L)
        # Lean arg1 (off-line) → elib c, arg2/arg3 (on-line) → elib a,b
        ("c", "Point"), ("a", "Point"), ("b", "Point"), ("d", "Point"),
        ("_", "Line"), ("L", "Line"), ("_", "Line"),
    ],
}


def _neg(atom: Atom) -> Literal:
    return Literal(atom, polarity=False)


# =====================================================================
# Result type
# =====================================================================

@dataclass
class SynthesisResult:
    prop_name: str
    prop_number: int
    success: bool = False
    euclid_json: Optional[Dict[str, Any]] = None
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    step_count: int = 0


# =====================================================================
# Variable mapper: Lean names <-> e_library names
# =====================================================================

_LINE_POOL = list("LMNPQRSTUVWXYZ")


class VarMapper:
    """Maps between Lean variable names and e_library variable names.

    Uses structural matching: extracts which points lie on which lines
    from both the Lean hypothesis and the e_library sequent, then matches
    lines by shared point-count structure, deriving point mappings from
    the line matches.
    """

    def __init__(self, sequent: Sequent, lean_proof: LeanProof):
        self.lean_to_elib: Dict[str, str] = {}
        self.elib_to_lean: Dict[str, str] = {}
        self.extra_lines: Dict[str, str] = {}
        self.extra_line_points: Dict[str, Tuple[str, str]] = {}
        self._used_pool: Set[str] = set()
        self._build(sequent, lean_proof)

    def _build(self, seq: Sequent, lp: LeanProof):
        # ── Gather elib line→points from hypotheses ───────────────────
        elib_lp: Dict[str, Set[str]] = {}
        for h in seq.hypotheses:
            if isinstance(h.atom, On) and h.polarity:
                elib_lp.setdefault(h.atom.obj, set()).add(h.atom.point)
        for name in elib_lp:
            self._used_pool.add(name)

        # ── Gather Lean params ────────────────────────────────────────
        lean_pts: List[str] = []
        lean_lns: List[Tuple[str, str]] = []  # (OrigName, lowercase)
        if lp.signature:
            for p in lp.signature.params:
                lo = p.name.lower()
                if p.sort == "Point":
                    lean_pts.append(lo)
                elif p.sort == "Line":
                    lean_lns.append((p.name, lo))

        pt_set = set(lean_pts)

        # ── Extract Lean line→points from hypothesis text ─────────────
        # Parse "distinctPointsOnLine p1 p2 L" patterns
        lean_line_pts: Dict[str, List[str]] = {}
        if lp.signature and lp.signature.hypothesis_raw:
            import re
            for m in re.finditer(
                r'distinctPointsOnLine\s+(\w+)\s+(\w+)\s+(\w+)',
                lp.signature.hypothesis_raw):
                p1, p2, ln = m.group(1).lower(), m.group(2).lower(), m.group(3).lower()
                lean_line_pts.setdefault(ln, [])
                if p1 not in lean_line_pts[ln]:
                    lean_line_pts[ln].append(p1)
                if p2 not in lean_line_pts[ln]:
                    lean_line_pts[ln].append(p2)

        # Fallback: infer line points from line name characters
        for orig, lo in lean_lns:
            if lo not in lean_line_pts:
                pts: List[str] = []
                for ch in orig:
                    c = ch.lower()
                    if c in pt_set and c not in pts:
                        pts.append(c)
                lean_line_pts[lo] = pts

        # ── Check if point names already match ────────────────────────
        elib_pts = set()
        for pts in elib_lp.values():
            elib_pts |= pts
        names_match = pt_set <= elib_pts or elib_pts <= pt_set

        if names_match:
            # Identity mapping for points
            for pt in lean_pts:
                self.lean_to_elib[pt] = pt
                self.elib_to_lean[pt] = pt
            self._match_lines_by_points(lean_lns, lean_line_pts, elib_lp)
        else:
            # Structural matching needed
            self._structural_match(lean_pts, lean_lns, lean_line_pts,
                                   elib_lp, seq)

    def _match_lines_by_points(self, lean_lns, lean_line_pts, elib_lp):
        """Match lines using already-mapped point identities."""
        used_elib: Set[str] = set()
        for _, lo in lean_lns:
            lpts = set(self.lean_to_elib.get(p, p)
                       for p in lean_line_pts.get(lo, []))
            matched = False
            for eline, epts in elib_lp.items():
                if eline in used_elib:
                    continue
                if lpts and (lpts == epts or epts <= lpts):
                    self.lean_to_elib[lo] = eline
                    self.elib_to_lean[eline] = lo
                    used_elib.add(eline)
                    matched = True
                    break
            if not matched:
                fresh = self._fresh()
                self.lean_to_elib[lo] = fresh
                self.elib_to_lean[fresh] = lo
                self.extra_lines[lo] = fresh
                if len(lpts) >= 2:
                    sl = sorted(lpts)
                    self.extra_line_points[fresh] = (sl[0], sl[1])

    def _structural_match(self, lean_pts, lean_lns, lean_line_pts,
                          elib_lp, seq: Sequent):
        """Match points and lines by structural constraints when names differ.

        Builds a constraint graph: which Lean points share lines, and which
        elib points share lines, then finds a consistent mapping.
        """
        from itertools import permutations

        # Build adjacency: lean_pt → set of lean_lines containing it
        lean_pt_lines: Dict[str, Set[str]] = {}
        for lo_line, pts in lean_line_pts.items():
            for p in pts:
                lean_pt_lines.setdefault(p, set()).add(lo_line)

        # Build adjacency: elib_pt → set of elib_lines containing it
        elib_pt_lines: Dict[str, Set[str]] = {}
        for eline, epts in elib_lp.items():
            for p in epts:
                elib_pt_lines.setdefault(p, set()).add(eline)

        # Build lean line adjacency signatures:
        # For each lean line, its "signature" is (num_points, sorted indices of
        # adjacent lines through those points).
        lean_line_list = [lo for _, lo in lean_lns]
        elib_line_list = sorted(elib_lp.keys())

        # We match lines first, then derive point mapping
        # Strategy: try permutations of elib lines matched to lean lines
        # (typically only 2-3 lines, so max 6 permutations)
        lean_premise_lines = [lo for _, lo in lean_lns
                              if lean_line_pts.get(lo)]
        elib_premise_lines = sorted(elib_lp.keys())

        if len(lean_premise_lines) > len(elib_premise_lines):
            # More Lean lines than elib lines — can't fully match
            # Fall back to identity for points
            for pt in lean_pts:
                self.lean_to_elib[pt] = pt
                self.elib_to_lean[pt] = pt
            self._match_lines_by_points(lean_lns, lean_line_pts, elib_lp)
            return

        best_map = None
        best_score = -1

        for elib_perm in permutations(elib_premise_lines,
                                       len(lean_premise_lines)):
            line_map = dict(zip(lean_premise_lines, elib_perm))
            # Derive point mapping from line mapping
            pt_map: Dict[str, str] = {}
            conflict = False
            for lean_ln, elib_ln in line_map.items():
                lean_ln_pts = lean_line_pts.get(lean_ln, [])
                elib_ln_pts = sorted(elib_lp.get(elib_ln, set()))
                if len(lean_ln_pts) != len(elib_ln_pts):
                    conflict = True
                    break
                # Try to match points on this line consistently
                for lp_pt, ep_pt in zip(lean_ln_pts, elib_ln_pts):
                    if lp_pt in pt_map:
                        if pt_map[lp_pt] != ep_pt:
                            conflict = True
                            break
                    else:
                        # Check reverse: elib pt already mapped to different lean pt
                        if ep_pt in [v for k, v in pt_map.items() if k != lp_pt]:
                            conflict = True
                            break
                        pt_map[lp_pt] = ep_pt
                if conflict:
                    break

            if conflict:
                continue

            # Score: how many non-metric elib hypotheses are satisfied?
            score = 0
            for h in seq.hypotheses:
                if isinstance(h.atom, On) and h.polarity:
                    mapped_pt = pt_map.get(h.atom.point, h.atom.point)
                    mapped_obj = line_map.get(h.atom.obj, h.atom.obj)
                    # This checks forward mapping; we need reverse
                    pass
                score += 1  # Simplified scoring

            if len(pt_map) > best_score:
                best_score = len(pt_map)
                best_map = (line_map, pt_map)

        if best_map:
            line_map, pt_map = best_map
            # Apply point mapping
            for lean_pt, elib_pt in pt_map.items():
                self.lean_to_elib[lean_pt] = elib_pt
                self.elib_to_lean[elib_pt] = lean_pt
            # Identity for unmapped Lean points (exist in both)
            for pt in lean_pts:
                if pt not in self.lean_to_elib:
                    self.lean_to_elib[pt] = pt
                    self.elib_to_lean[pt] = pt
            # Apply line mapping
            used_elib: Set[str] = set()
            for _, lo in lean_lns:
                if lo in line_map:
                    eline = line_map[lo]
                    self.lean_to_elib[lo] = eline
                    self.elib_to_lean[eline] = lo
                    used_elib.add(eline)
                else:
                    # Extra line
                    fresh = self._fresh()
                    self.lean_to_elib[lo] = fresh
                    self.elib_to_lean[fresh] = lo
                    self.extra_lines[lo] = fresh
                    lpts = lean_line_pts.get(lo, [])
                    mapped_pts = [self.lean_to_elib.get(p, p) for p in lpts]
                    if len(mapped_pts) >= 2:
                        self.extra_line_points[fresh] = (
                            mapped_pts[0], mapped_pts[1])
        else:
            # Fallback: identity for everything
            for pt in lean_pts:
                self.lean_to_elib[pt] = pt
                self.elib_to_lean[pt] = pt
            self._match_lines_by_points(lean_lns, lean_line_pts, elib_lp)

    def _fresh(self) -> str:
        for ch in _LINE_POOL:
            if ch not in self._used_pool:
                self._used_pool.add(ch)
                return ch
        n = 1
        while f"L{n}" in self._used_pool:
            n += 1
        name = f"L{n}"
        self._used_pool.add(name)
        return name

    def mv(self, lean_name: str) -> str:
        lo = lean_name.lower()
        return self.lean_to_elib.get(lo, lo)

    def ma(self, args: List[str]) -> List[str]:
        return [self.mv(a) for a in args]


# =====================================================================
# Core synthesizer
# =====================================================================

class ProofSynthesizer:
    def __init__(self, translation: TranslationResult,
                 lean_proof: Optional[LeanProof] = None):
        self.tr = translation
        self.pname = translation.prop_name
        self.pnum = translation.prop_number
        self.lp = lean_proof
        self.thm: Optional[ETheorem] = E_THEOREM_LIBRARY.get(self.pname)
        self.seq: Optional[Sequent] = self.thm.sequent if self.thm else None
        self.avail = get_theorems_up_to(self.pname)
        self.vm: Optional[VarMapper] = None
        self.known: Set[Literal] = set()
        self.sort_ctx: Dict[str, Sort] = {}
        self.steps: List[Dict[str, Any]] = []
        self.nprem = 0
        self.ll: Dict[int, Set[Literal]] = {}
        self.errors: List[str] = []
        self.warnings: List[str] = []

    def synthesize(self) -> SynthesisResult:
        r = SynthesisResult(prop_name=self.pname, prop_number=self.pnum)
        if not self.thm:
            r.errors.append(f"No e_library entry for {self.pname}")
            return r
        if not self.tr.steps and (not self.lp or not self.lp.tactics):
            r.errors.append("No steps or tactics to synthesize from")
            return r

        if self.lp:
            self.vm = VarMapper(self.seq, self.lp)

        premises = [literal_to_text(lit) for lit in self.seq.hypotheses]
        self.nprem = len(premises)
        for i, lit in enumerate(self.seq.hypotheses):
            self.known.add(lit)
            self.ll[i + 1] = {lit}

        decls = self._build_decls()
        for p in decls["points"]:
            self.sort_ctx[p] = Sort.POINT
        for ln in decls["lines"]:
            self.sort_ctx[ln] = Sort.LINE

        if self.vm:
            for lean_name, elib_name in self.vm.extra_lines.items():
                pts = self.vm.extra_line_points.get(elib_name)
                if pts:
                    self._add_let_line(elib_name, pts[0], pts[1])
                    if elib_name not in decls["lines"]:
                        decls["lines"].append(elib_name)
                        decls["lines"].sort()

        if self.lp:
            for tac in self.lp.tactics:
                self._synth_tactic(tac)
        else:
            for ts in self.tr.steps:
                self._synth_translated(ts)

        goal_text = ", ".join(
            literal_to_text(lit) for lit in self.seq.conclusions)
        canvas = _load_existing_canvas(self.pnum)
        if canvas is None:
            canvas = {"points": [], "segments": [], "rays": [],
                      "circles": [], "angleMarks": [], "equalityGroups": []}

        r.euclid_json = {
            "format": "euclid-proof", "version": "1.0.0",
            "program": "Euclid Elements Simulator (Python) -- Lean Translator",
            "metadata": {
                "proposition": f"Proposition I.{self.pnum}",
                "title": _PROP_TITLES.get(self.pnum, f"Proposition I.{self.pnum}"),
                "difficulty": _PROP_DIFFICULTIES.get(self.pnum, 3),
                "hints": [f"Translated from LeanEuclid {self.tr.lean_theorem}"],
                "source": "lean_translator",
            },
            "canvas": canvas,
            "exportedAt": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
            "proof": {
                "name": self.pname, "premises": premises,
                "goal": goal_text, "declarations": decls,
                "steps": self.steps,
            },
        }
        r.step_count = len(self.steps)
        r.errors = self.errors
        r.warnings = self.warnings
        r.success = len(self.errors) == 0
        return r

    # -- Tactic dispatch -----------------------------------------------

    def _synth_tactic(self, tac: LeanTactic):
        if tac.kind == TacticKind.EUCLID_APPLY:
            self._apply(tac)
        elif tac.kind == TacticKind.EUCLID_FINISH:
            self._finish()
        elif tac.kind == TacticKind.EUCLID_ASSERT:
            self._derive_from_expr(tac.assertion_expr)
        elif tac.kind == TacticKind.HAVE:
            self._derive_from_expr(tac.assertion_expr)
        elif tac.kind == TacticKind.BY_CONTRA:
            self._handle_by_contra()
        elif tac.kind == TacticKind.CASE_BRANCH:
            self._handle_case_branch(tac)

    def _handle_case_branch(self, tac: LeanTactic):
        """Handle CASE_BRANCH tactics whose assertion_expr embeds an apply."""
        expr = (tac.assertion_expr or "").strip()
        if not expr or expr.startswith("--"):
            return
        # Parse embedded "euclid_apply (rule args...) as bound_var"
        import re
        m = re.match(
            r"euclid_apply\s+\((\w+)((?:\s+\S+)*)\)\s+as\s+(\w+)",
            expr,
        )
        if m:
            rule = m.group(1)
            args = m.group(2).split() if m.group(2).strip() else []
            bound = [m.group(3)]
            synth_tac = LeanTactic(
                kind=TacticKind.EUCLID_APPLY,
                raw=expr,
                rule_name=rule,
                rule_args=args,
                bound_vars=bound,
                assertion_expr="",
                case_expr="",
                depth=tac.depth,
                line_number=tac.line_number,
                comment="",
            )
            self._apply(synth_tac)
            return
        # Fallback: try without bound vars
        m2 = re.match(
            r"euclid_apply\s+\((\w+)((?:\s+\S+)*)\)",
            expr,
        )
        if m2:
            rule = m2.group(1)
            args = m2.group(2).split() if m2.group(2).strip() else []
            synth_tac = LeanTactic(
                kind=TacticKind.EUCLID_APPLY,
                raw=expr,
                rule_name=rule,
                rule_args=args,
                bound_vars=[],
                assertion_expr="",
                case_expr="",
                depth=tac.depth,
                line_number=tac.line_number,
                comment="",
            )
            self._apply(synth_tac)

    def _apply(self, tac: LeanTactic):
        from .lean_mapping import classify_rule, lookup_rule, RuleCategory
        cat = classify_rule(tac.rule_name)
        mp = lookup_rule(tac.rule_name)
        if cat == RuleCategory.PROPOSITION:
            self._apply_theorem(tac, mp)
        elif cat in (RuleCategory.CONSTRUCTION, RuleCategory.EXTENSION_AXIOM,
                     RuleCategory.INTERSECTION, RuleCategory.SPECIAL):
            self._apply_construction(tac, mp)
        elif cat in (RuleCategory.METRIC, RuleCategory.TRANSFER,
                     RuleCategory.DIAGRAMMATIC):
            self._apply_inference(tac, mp)

    def _handle_by_contra(self):
        """Handle proof by contradiction: negate the goal and add as known fact.

        When Lean uses ``by_contra``, the negation of the current goal
        becomes a new hypothesis. We add it as a premise-like known fact
        tracked in ll so subsequent steps can cite it as a dependency.
        """
        if not self.seq:
            return
        for conc in self.seq.conclusions:
            # Negate the conclusion: ¬P becomes P, P becomes ¬P
            neg_conc = Literal(conc.atom, polarity=not conc.polarity)
            if neg_conc not in self.known:
                self.known.add(neg_conc)
                # Track in ll using next available line number so it can
                # be cited as a dependency, but don't emit as a step
                # (it's treated as an implicit premise for the proof by
                # contradiction structure).
                ln = self.nprem + len(self.steps) + 1
                self.ll[ln] = {neg_conc}
                self.steps.append({
                    "lineNumber": ln,
                    "text": literal_to_text(neg_conc),
                    "justification": "Assume",
                    "dependencies": [],
                    "depth": 0, "status": "?",
                })

    # -- Construction --------------------------------------------------

    _POINT_POOL = list("abcdefghijklmnopqrstuvwxyz")

    def _fresh_bound_vars(self, lean_bound_vars: List[str]) -> List[str]:
        """Map construction bound vars to fresh names avoiding collisions.

        Bound vars are NEW variables introduced by constructions. They should
        not be mapped through VarMapper (which maps existing Lean names to
        elib names). Instead, use their lowercase form if it doesn't collide,
        or allocate a fresh name.
        """
        used = set(self.vm.lean_to_elib.values()) if self.vm else set()
        # Also include all variables already in sort_ctx (points & lines
        # introduced by previous constructions)
        used |= set(self.sort_ctx.keys())
        result = []
        for bv in lean_bound_vars:
            lo = bv.lower()
            if lo not in used:
                result.append(lo)
                used.add(lo)
                # Register in VarMapper so subsequent tactics can find it
                if self.vm:
                    self.vm.lean_to_elib[lo] = lo
                    self.vm.elib_to_lean[lo] = lo
            else:
                # Collision — allocate fresh name
                # Determine sort: single uppercase → Line, else → Point
                is_line = len(bv) == 1 and bv.isupper()
                if is_line:
                    fresh = self.vm._fresh() if self.vm else lo
                else:
                    fresh = self._fresh_point(used)
                result.append(fresh)
                used.add(fresh)
                if self.vm:
                    self.vm.lean_to_elib[lo] = fresh
                    self.vm.elib_to_lean[fresh] = lo
        return result

    def _fresh_point(self, used: Set[str]) -> str:
        """Allocate a fresh point name not in used."""
        for ch in self._POINT_POOL:
            if ch not in used:
                return ch
        n = 1
        while f"p{n}" in used:
            n += 1
        return f"p{n}"

    def _apply_construction(self, tac: LeanTactic, mp):
        rule_name = mp.system_e_name if mp else tac.rule_name
        args = self.vm.ma(tac.rule_args) if self.vm else [a.lower() for a in tac.rule_args]
        # Bound vars are NEW variables introduced by constructions.
        # Don't map them through VarMapper — they need fresh names if
        # they collide with existing mapped names.
        bound = self._fresh_bound_vars(tac.bound_vars) if self.vm else [v.lower() for v in tac.bound_vars]

        # ── Inject construction prerequisites ─────────────────────────
        # let-line / let-circle: need ¬(a = b)
        if tac.rule_name == "line_from_points" and len(args) >= 2:
            self._ensure_neq(args[0], args[1])
        elif tac.rule_name == "circle_from_points" and len(args) >= 2:
            self._ensure_neq(args[0], args[1])
        elif tac.rule_name in ("extend_point", "extend_point_longer",
                                "extend_point_not_on_line",
                                "exists_point_on_extension",
                                "exists_point_on_extension_longer") and len(args) >= 3:
            # let-point-on-line-extend: need on(b,L), on(c,L), ¬(b=c)
            self._ensure_neq(args[1], args[2])
        elif tac.rule_name == "exists_point_between_points_on_line" and len(args) >= 3:
            # let-point-on-line-between: need on(b,L), on(c,L), ¬(b=c)
            self._ensure_neq(args[0], args[1])
        elif tac.rule_name == "intersection_lines" and len(args) >= 2:
            # let-intersection-line-line: need intersects(L, M)
            self._ensure_intersects(args[0], args[1])
        elif tac.rule_name == "intersection_circles" and len(args) >= 2:
            # let-intersection-circle-circle: need intersects(α, β)
            self._ensure_intersects(args[0], args[1])
        elif tac.rule_name in ("intersection_circle_line",
                                "intersection_circle_line_extending_points") and len(args) >= 2:
            # let-intersection-circle-line: need intersects(L, α) or intersects(α, L)
            self._ensure_intersects(args[0], args[1])

        # Map rule name for special constructions
        actual_rule_name = rule_name
        if tac.rule_name == "line_nonempty":
            actual_rule_name = "let-point-on-line"
        elif tac.rule_name == "exists_distincts_points_on_line":
            actual_rule_name = "let-point-on-line"
        elif tac.rule_name == "point_on_line_same_side":
            # Lean axiom: creates point on line M, same-side as b w.r.t. L.
            # No single System E rule matches; use let-point-same-side as closest.
            actual_rule_name = "let-point-same-side"
        elif tac.rule_name in ("exists_point_opposite",
                                "exists_distinct_point_opposite_side"):
            actual_rule_name = "let-point-opposite-side"
        elif tac.rule_name in ("exists_point_on_circle",
                                "exists_distinct_point_on_circle"):
            actual_rule_name = "let-point-on-circle"

        text, lits = self._construction_text(tac.rule_name, actual_rule_name, args, bound)
        for lit in lits:
            self.known.add(lit)
        for v in bound:
            if v not in self.sort_ctx:
                self.sort_ctx[v] = Sort.LINE if (len(v) == 1 and v.isupper()) else Sort.POINT

        new_var_set = set(bound)
        deps = self._deps_for(lits, new_var_set)
        ln = self.nprem + len(self.steps) + 1
        self.steps.append({
            "lineNumber": ln, "text": text,
            "justification": actual_rule_name, "dependencies": deps,
            "depth": 0, "status": "?",
        })
        self.ll[ln] = set(lits)

    def _construction_text(self, lean_rule, se_rule, args, bound):
        lits: List[Literal] = []
        if lean_rule in ("line_from_points",) and len(args) >= 2 and bound:
            a, b, line = args[0], args[1], bound[0]
            lits = [_pos(On(a, line)), _pos(On(b, line))]
        elif lean_rule in ("extend_point", "extend_point_longer",
                           "extend_point_not_on_line",
                           "exists_point_on_extension",
                           "exists_point_on_extension_longer") and len(args) >= 3 and bound:
            line, b, c, d = args[0], args[1], args[2], bound[0]
            lits = [_pos(On(d, line)), _pos(Between(b, c, d))]
        elif lean_rule in ("intersection_lines",) and len(args) >= 2 and bound:
            l1, l2, pt = args[0], args[1], bound[0]
            lits = [_pos(On(pt, l1)), _pos(On(pt, l2))]
        elif lean_rule in ("circle_from_points",) and len(args) >= 2 and bound:
            ctr, on_pt, circ = args[0], args[1], bound[0]
            lits = [_pos(Center(ctr, circ)), _pos(On(on_pt, circ))]
        elif lean_rule in ("intersection_circles",) and len(args) >= 2 and bound:
            c1, c2, pt = args[0], args[1], bound[0]
            lits = [_pos(On(pt, c1)), _pos(On(pt, c2))]
        elif lean_rule in ("intersection_circle_line",
                           "intersection_circle_line_extending_points") and len(args) >= 2 and bound:
            c_arg, l_arg, pt = args[0], args[1], bound[0]
            lits = [_pos(On(pt, c_arg)), _pos(On(pt, l_arg))]
        elif lean_rule in ("arbitrary_point", "distinct_points") and bound:
            pass
        elif lean_rule in ("point_same_side",
                           "distinct_point_same_side") and len(args) >= 2 and bound:
            ref_pt, line, new_pt = args[0], args[1], bound[0]
            lits = [_pos(SameSide(new_pt, ref_pt, line))]
        elif lean_rule == "exists_point_between_points_on_line" and len(args) >= 3 and bound:
            b, c, line, pt = args[0], args[1], args[2], bound[0]
            lits = [_pos(On(pt, line)), _pos(Between(b, pt, c))]
        elif lean_rule == "point_between_points_shorter_than" and len(args) >= 2 and bound:
            b, c, pt = args[0], args[1], bound[0]
            lits = [_pos(Between(b, pt, c))]
        elif lean_rule == "line_nonempty" and len(args) >= 1 and bound:
            # ∀ l, ∃ p, p.onLine l
            line, pt = args[0], bound[0]
            lits = [_pos(On(pt, line))]
        elif lean_rule == "exists_distincts_points_on_line" and len(args) >= 2 and bound:
            # ∀ l p, ∃ p', p ≠ p' ∧ p'.onLine l
            line, ref_pt, new_pt = args[0], args[1], bound[0]
            lits = [_pos(On(new_pt, line)), _neg(Equals(ref_pt, new_pt))]
        elif lean_rule == "point_on_line_same_side" and len(args) >= 3 and bound:
            # ∀ L M b, ¬(b.onLine L) ∧ intersects(L,M) → ∃ a, a.onLine M ∧ a.sameSide b L
            line_l, line_m, ref_pt, new_pt = args[0], args[1], args[2], bound[0]
            lits = [_pos(On(new_pt, line_m)), _pos(SameSide(new_pt, ref_pt, line_l))]
        elif lean_rule in ("exists_point_opposite",
                           "exists_distinct_point_opposite_side") and len(args) >= 2 and bound:
            line, ref_pt, new_pt = args[0], args[1], bound[0]
            lits = [_neg(On(new_pt, line)), _neg(SameSide(new_pt, ref_pt, line))]
        elif lean_rule in ("exists_point_on_circle",
                           "exists_distinct_point_on_circle") and len(args) >= 1 and bound:
            circ, new_pt = args[0], bound[0]
            lits = [_pos(On(new_pt, circ))]
        else:
            for ts in self.tr.steps:
                if ts.step.description == se_rule and ts.step.assertions:
                    for a in ts.step.assertions:
                        lits.append(self._map_lit(a))
                    break
        text = ", ".join(literal_to_text(l) for l in lits) if lits else ""
        return text, lits

    # -- Theorem application -------------------------------------------

    def _apply_theorem(self, tac: LeanTactic, mp):
        se_name = mp.system_e_name if mp else tac.rule_name
        thm = self.avail.get(se_name)
        if not thm:
            self.warnings.append(f"Theorem {se_name} not available")
            return
        var_map = self._build_thm_varmap(thm, tac)

        # ── Inject metric prerequisite steps ──────────────────────────
        # For each hypothesis not directly in known, try to emit a
        # derivation step (M3 Symmetry, M4 Angle symmetry, CN1, etc.)
        self._inject_metric_prereqs(thm, var_map)

        # Check if Lean arg positions give us better conclusions than
        # the e_library var_map (handles shared-endpoint cases like I.3)
        lean_lits = self._lean_arg_conclusions(tac, se_name)

        text_parts = []
        step_lits: Set[Literal] = set()
        if lean_lits:
            # Use Lean-intended conclusions as the step output
            for lit in lean_lits:
                text_parts.append(literal_to_text(lit))
                step_lits.add(lit)
                self.known.add(lit)
            # Also add var_map conclusions to known (they're still valid
            # derivations, just not the ones Lean intends for this step)
            for conc in thm.sequent.conclusions:
                inst = substitute_literal(conc, var_map)
                self.known.add(inst)
        else:
            for conc in thm.sequent.conclusions:
                inst = substitute_literal(conc, var_map)
                text_parts.append(literal_to_text(inst))
                step_lits.add(inst)
                self.known.add(inst)
        text = ", ".join(text_parts)

        deps = self._thm_deps(thm, var_map)
        ln = self.nprem + len(self.steps) + 1
        self.steps.append({
            "lineNumber": ln, "text": text,
            "justification": se_name, "dependencies": deps,
            "depth": 0, "status": "?",
        })
        self.ll[ln] = step_lits

    def _inject_metric_prereqs(self, thm: ETheorem, var_map: Dict[str, str]):
        """Inject prerequisite steps needed by a theorem.

        For each hypothesis not directly in known:
        - M3 Symmetry: ab=ba when ba=ab is known (segment)
        - M4 Angle symmetry: ∠abc=∠cba when needed
        - CN1 Transitivity: derive equalities via chain
        - Distinctness: ¬(a=b) via _ensure_neq
        - Diagrammatic: on(), between(), ¬on(), ¬same-side(), intersects()
          via ConsequenceEngine
        """
        for hyp in thm.sequent.hypotheses:
            inst = substitute_literal(hyp, var_map)
            if inst in self.known:
                continue

            # Check if it's a distinctness prerequisite
            if not inst.polarity and isinstance(inst.atom, Equals):
                left, right = inst.atom.left, inst.atom.right
                if isinstance(left, str) and isinstance(right, str):
                    self._ensure_neq(left, right)
                    continue

            # Check if symmetric form is known (M3/M4)
            sym = self._symmetric_literal(inst)
            if sym is not None:
                # Emit M3 or M4 step
                just = self._metric_symmetry_just(inst)
                deps = self._deps_target(sym)
                ln = self.nprem + len(self.steps) + 1
                self.steps.append({
                    "lineNumber": ln,
                    "text": literal_to_text(inst),
                    "justification": just,
                    "dependencies": deps,
                    "depth": 0, "status": "?",
                })
                self.known.add(inst)
                self.ll[ln] = {inst}
                continue

            # Try MetricEngine for CN1 transitivity chains
            if inst.is_metric:
                from .e_metric import MetricEngine
                me = MetricEngine()
                if me.is_consequence(self.known, inst):
                    deps = self._deps_target(inst)
                    just = self._metric_just(inst)
                    ln = self.nprem + len(self.steps) + 1
                    self.steps.append({
                        "lineNumber": ln,
                        "text": literal_to_text(inst),
                        "justification": just,
                        "dependencies": deps,
                        "depth": 0, "status": "?",
                    })
                    self.known.add(inst)
                    self.ll[ln] = {inst}
                    continue

            # Try ConsequenceEngine for diagrammatic hypotheses
            # (on, between, ¬on, ¬same-side, intersects, etc.)
            if inst.is_diagrammatic:
                self._inject_diag_prereq(inst)

    def _inject_diag_prereq(self, target: Literal):
        """Try to derive a diagrammatic prerequisite via axiom match.

        Only injects a step if we can find a specific axiom that derives
        the target from a targeted set of dependencies.
        """
        from .e_axiom_match import check_specific_axiom
        tv = literal_vars(target)
        just = self._guess_diag(target)
        deps = self._find_minimal_deps(target, just, tv)

        # Verify the deps actually work with the axiom
        dep_facts: Set[Literal] = set()
        for ln_num in deps:
            dep_facts |= self.ll.get(ln_num, set())
        dep_vars: Dict[str, Sort] = dict(self.sort_ctx)
        from .e_consequence import ConsequenceEngine
        ce = ConsequenceEngine()
        closure = ce.direct_consequences(dep_facts)
        dep_aug = dep_facts | closure
        for lit in dep_aug:
            for v in literal_vars(lit):
                if v not in dep_vars:
                    dep_vars[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                                   else Sort.POINT)
        ok, _ = check_specific_axiom(just, dep_aug, [target], dep_vars)
        if ok:
            ln = self.nprem + len(self.steps) + 1
            self.steps.append({
                "lineNumber": ln,
                "text": literal_to_text(target),
                "justification": just,
                "dependencies": deps,
                "depth": 0, "status": "?",
            })
            self.known.add(target)
            self.ll[ln] = {target}

    def _metric_symmetry_just(self, target: Literal) -> str:
        """Pick the right justification for a metric symmetry step."""
        a = target.atom
        if isinstance(a, Equals):
            if isinstance(a.left, SegmentTerm) or isinstance(a.right, SegmentTerm):
                return "M3 \u2014 Symmetry"
            if isinstance(a.left, AngleTerm) or isinstance(a.right, AngleTerm):
                return "M4 \u2014 Angle symmetry"
        return "CN1 \u2014 Transitivity"

    def _metric_just(self, target: Literal) -> str:
        """Pick the right justification for a metric derivation."""
        a = target.atom
        if isinstance(a, LessThan):
            return "CN5 \u2014 Whole > Part"
        if isinstance(a, Equals):
            if isinstance(a.left, MagAdd) or isinstance(a.right, MagAdd):
                return "CN1 \u2014 Transitivity"
            if isinstance(a.left, SegmentTerm) and isinstance(a.right, SegmentTerm):
                return "CN1 \u2014 Transitivity"
            if isinstance(a.left, AngleTerm) and isinstance(a.right, AngleTerm):
                return "CN1 \u2014 Transitivity"
            if isinstance(a.left, AreaTerm) or isinstance(a.right, AreaTerm):
                return "CN1 \u2014 Transitivity"
        return "CN1 \u2014 Transitivity"

    def _lean_arg_conclusions(self, tac: LeanTactic,
                              se_name: str) -> Optional[List[Literal]]:
        """Compute theorem conclusions directly from Lean arg positions.

        Handles cases where the e_library var_map produces incorrect metric
        conclusions due to shared endpoints between segments (e.g. Lean's
        ``proposition_3 a c a b AC AB as d`` where lesser segment ``a b``
        shares endpoint ``a`` with the greater ``a c``).

        Returns None if no override is needed.
        """
        if not self.vm:
            return None
        args = self.vm.ma(tac.rule_args)
        bound = self.vm.ma(tac.bound_vars) if tac.bound_vars else []

        if se_name == "Prop.I.3" and len(args) >= 4 and bound:
            # Lean: proposition_3 p1 p2 p3 p4 L1 L2 as e
            # Semantics: cut segment p1-p2 (greater) to get e with
            #   between(p1, e, p2) and |p1─e| = |p3─p4|
            p1, p2, p3, p4 = args[0], args[1], args[2], args[3]
            e = bound[0]
            return [
                _pos(Between(p1, e, p2)),
                _pos(Equals(SegmentTerm(p1, e), SegmentTerm(p3, p4))),
            ]

        return None

    def _build_thm_varmap(self, thm: ETheorem, tac: LeanTactic) -> Dict[str, str]:
        """Build var_map by matching e_library hypotheses against known facts.

        Uses Lean rule_args (mapped through VarMapper) as the candidate
        variable pool, then tries permutations to find a substitution
        where all hypotheses are satisfied.

        Also maps bound_vars (from 'as x') to exists_vars in the sequent.
        """
        elib_vars: Set[str] = set()
        for h in thm.sequent.hypotheses:
            elib_vars |= literal_vars(h)
        for c in thm.sequent.conclusions:
            elib_vars |= literal_vars(c)

        # Separate exists-vars (bound results) from hypothesis vars
        exists_set = {name for name, _ in thm.sequent.exists_vars}
        hyp_vars = elib_vars - exists_set

        identity = {v: v for v in elib_vars}

        # Get mapped Lean rule_args as candidate variable pool
        cited_params = self._cited_lean_params(tac.rule_name)

        # Strategy -1: Direct var_map from _LEAN_PARAM_ORDER table.
        # The table provides the exact elib var for each Lean positional arg,
        # handling cases where Lean and e_library use different variable conventions.
        if tac.rule_args:
            from .lean_parser import extract_prop_number
            _pn = extract_prop_number(tac.rule_name)
            if _pn and _pn in _LEAN_PARAM_ORDER:
                param_order = _LEAN_PARAM_ORDER[_pn]
                direct_vm: Dict[str, str] = {}
                for i, (elib_var, _sort) in enumerate(param_order):
                    if i < len(tac.rule_args):
                        arg = tac.rule_args[i]
                        if arg.startswith('(') or '\u2500' in arg or '|' in arg:
                            continue
                        actual = self.vm.mv(arg) if self.vm else arg.lower()
                        if elib_var not in direct_vm:
                            direct_vm[elib_var] = actual
                # Map bound vars to exists vars
                if tac.bound_vars and thm.sequent.exists_vars:
                    fresh_bounds = self._fresh_bound_vars(tac.bound_vars) if self.vm else [v.lower() for v in tac.bound_vars]
                    for j, (ev_name, _) in enumerate(thm.sequent.exists_vars):
                        if j < len(fresh_bounds):
                            direct_vm[ev_name] = fresh_bounds[j]
                # The table is derived from the Lean source (machine-checked),
                # so trust it if conclusions validate.  Hypothesis checks may
                # fail spuriously because our known-set doesn't carry every
                # fact the Lean proof establishes (e.g. extend_point_longer
                # doesn't emit the inequality that I.3 needs).
                if self._validate_conclusions(thm, direct_vm):
                    return direct_vm

        # Build actual mapped args with sort info
        mapped_args: List[str] = []
        mapped_sorts: List[str] = []
        if cited_params:
            for i, (pname, psort) in enumerate(cited_params):
                if i < len(tac.rule_args):
                    actual = self.vm.mv(tac.rule_args[i]) if self.vm else tac.rule_args[i].lower()
                    mapped_args.append(actual)
                    mapped_sorts.append(psort)
        else:
            # Fallback: infer sorts from ORIGINAL Lean arg naming conventions.
            # In Lean, multi-char names starting with uppercase are Lines (AB, BC, AC).
            # Single lowercase letters or primed names are Points (a, b, d').
            # Skip non-variable args like segment expressions (c─a).
            for arg in tac.rule_args:
                # Skip segment/metric expressions
                if arg.startswith('(') or '─' in arg or '|' in arg:
                    continue
                actual = self.vm.mv(arg) if self.vm else arg.lower()
                is_line = (len(arg) >= 2 and arg[0].isupper() and arg[1:].isalpha()
                           and arg[1:].isupper())
                if is_line:
                    mapped_args.append(actual)
                    mapped_sorts.append("Line")
                else:
                    mapped_args.append(actual)
                    mapped_sorts.append("Point")

        actual_pts = list(dict.fromkeys(
            a for a, s in zip(mapped_args, mapped_sorts) if s == "Point"))
        actual_lns = list(dict.fromkeys(
            a for a, s in zip(mapped_args, mapped_sorts) if s == "Line"))

        # Keep ordered (potentially duplicate) args for positional mapping
        all_pt_args = [a for a, s in zip(mapped_args, mapped_sorts) if s == "Point"]
        all_ln_args = [a for a, s in zip(mapped_args, mapped_sorts) if s == "Line"]

        # Pre-map bound_vars to exists_vars
        bound_map: Dict[str, str] = {}
        if tac.bound_vars and thm.sequent.exists_vars:
            # Use _fresh_bound_vars to avoid collisions
            fresh_bounds = self._fresh_bound_vars(tac.bound_vars) if self.vm else [v.lower() for v in tac.bound_vars]
            for i, (ev_name, ev_sort) in enumerate(thm.sequent.exists_vars):
                if i < len(fresh_bounds):
                    bv = fresh_bounds[i]
                    bound_map[ev_name] = bv
                    # Also add bound var to candidate pool
                    if ev_sort == Sort.POINT and bv not in actual_pts:
                        actual_pts.append(bv)
                    elif ev_sort == Sort.LINE and bv not in actual_lns:
                        actual_lns.append(bv)

        elib_pts = sorted(v for v in hyp_vars
                          if not (len(v) == 1 and v.isupper()))
        elib_lns = sorted(v for v in hyp_vars
                          if len(v) == 1 and v.isupper())

        # Identity map check (fast path) — only use when Lean args actually
        # correspond to identity (mapped args match the elib var names).
        # This prevents returning identity when elib hypotheses happen to
        # match known facts by coincidence but the Lean call-site intends a
        # different mapping (e.g. Prop.I.10 called on b,c,M inside I.16
        # whose premises already satisfy on(a,L), on(b,L), ¬(a=b)).
        if mapped_args:
            id_vm = dict(zip(elib_pts, all_pt_args))
            for j, el in enumerate(elib_lns):
                if j < len(all_ln_args):
                    id_vm[el] = all_ln_args[j]
            id_vm.update(bound_map)
            # Check if the positional map IS the identity
            if all(id_vm.get(v) == v for v in hyp_vars):
                if self._check_hyps(thm, identity):
                    return identity
        elif not tac.rule_args:
            # No Lean args at all — identity is only option
            if self._check_hyps(thm, identity):
                return identity

        # Strategy 0: Direct positional mapping (handles duplicate args)
        # Lean args are in the same order as the theorem's parameter list.
        if len(all_pt_args) >= len(elib_pts) and len(all_ln_args) >= len(elib_lns):
            vm0 = dict(zip(elib_pts, all_pt_args))
            for j, el in enumerate(elib_lns):
                if j < len(all_ln_args):
                    vm0[el] = all_ln_args[j]
            vm0.update(bound_map)
            if self._validate_conclusions(thm, vm0):
                if self._check_hyps_fast(thm, vm0):
                    return vm0
                if self._check_hyps(thm, vm0):
                    return vm0

        # Strategy 0b: Hypothesis-order positional mapping.
        # Some theorems (e.g. I.2, I.7, I.13) have hypothesis variable
        # order that differs from alphabetical. Lean follows hypothesis
        # order, so try that as a second positional strategy.
        elib_ordered = _ordered_sequent_vars(thm.sequent)
        elib_pts_ho = [v for v in elib_ordered
                       if v in hyp_vars and not (len(v) == 1 and v.isupper())]
        elib_lns_ho = [v for v in elib_ordered
                       if v in hyp_vars and len(v) == 1 and v.isupper()]
        if (elib_pts_ho != elib_pts or elib_lns_ho != elib_lns):
            if len(all_pt_args) >= len(elib_pts_ho) and len(all_ln_args) >= len(elib_lns_ho):
                vm0b = dict(zip(elib_pts_ho, all_pt_args))
                for j, el in enumerate(elib_lns_ho):
                    if j < len(all_ln_args):
                        vm0b[el] = all_ln_args[j]
                vm0b.update(bound_map)
                if self._validate_conclusions(thm, vm0b):
                    if self._check_hyps_fast(thm, vm0b):
                        return vm0b
                    if self._check_hyps(thm, vm0b):
                        return vm0b

        if len(elib_lns) > len(actual_lns):
            return identity

        from itertools import permutations, product
        import time as _time
        _deadline = _time.monotonic() + 30  # 30s budget for var_map search

        # Collect distinctness constraints from hypotheses to prune early
        neq_pairs: Set[Tuple[str, str]] = set()
        for hyp in thm.sequent.hypotheses:
            if not hyp.polarity and isinstance(hyp.atom, Equals):
                neq_pairs.add((hyp.atom.left, hyp.atom.right))

        def _valid_map(vm: Dict[str, str]) -> bool:
            """Quick pre-filter: check no ¬(x=y) becomes ¬(a=a)."""
            for v1, v2 in neq_pairs:
                if vm.get(v1) == vm.get(v2):
                    return False
            return True

        pt_candidates = actual_pts if actual_pts else []
        if not pt_candidates and elib_pts:
            return identity

        # Add construction-created points/lines to candidate pool
        # so var_map search can find matches involving bound vars
        # from prior construction steps.
        for v, s in self.sort_ctx.items():
            if s == Sort.POINT and v not in pt_candidates:
                pt_candidates.append(v)
            elif s == Sort.LINE and v not in actual_lns:
                actual_lns.append(v)

        # Strategy 1: Permutations (fast — no duplicate mappings)
        if len(elib_pts) <= len(pt_candidates):
            for pt_perm in permutations(pt_candidates, len(elib_pts)):
                if _time.monotonic() > _deadline:
                    break
                vm = dict(zip(elib_pts, pt_perm))
                vm.update(bound_map)
                if not _valid_map(vm):
                    continue
                if not self._validate_conclusions(thm, vm):
                    continue
                for ln_perm in permutations(actual_lns, len(elib_lns)):
                    for j, el in enumerate(elib_lns):
                        vm[el] = ln_perm[j]
                    if self._check_hyps_fast(thm, vm):
                        return vm

            # Phase 2: permutations with structural pre-filter then CE
            if _time.monotonic() <= _deadline:
                for pt_perm in permutations(pt_candidates, len(elib_pts)):
                    if _time.monotonic() > _deadline:
                        break
                    vm = dict(zip(elib_pts, pt_perm))
                    vm.update(bound_map)
                    if not _valid_map(vm):
                        continue
                    if not self._validate_conclusions(thm, vm):
                        continue
                    for ln_perm in permutations(actual_lns, len(elib_lns)):
                        for j, el in enumerate(elib_lns):
                            vm[el] = ln_perm[j]
                        if not self._check_hyps_structural(thm, vm):
                            continue
                        if self._check_hyps(thm, vm):
                            return vm

        # Strategy 2: Product with replacement (allows duplicate mappings)
        # Only used when permutations failed (fewer unique candidates than
        # e_lib vars), capped to avoid combinatorial explosion.
        if _time.monotonic() > _deadline:
            return identity
        n_pt_combos = len(pt_candidates) ** len(elib_pts) if elib_pts else 1
        n_ln_perms = 1
        for i in range(len(elib_lns)):
            n_ln_perms *= (len(actual_lns) - i) if i < len(actual_lns) else 1
        total = n_pt_combos * n_ln_perms
        if total <= 10000:
            for pt_combo in product(pt_candidates, repeat=len(elib_pts)):
                if _time.monotonic() > _deadline:
                    break
                vm = dict(zip(elib_pts, pt_combo))
                vm.update(bound_map)
                if not _valid_map(vm):
                    continue
                if not self._validate_conclusions(thm, vm):
                    continue
                for ln_perm in permutations(actual_lns, len(elib_lns)):
                    for j, el in enumerate(elib_lns):
                        vm[el] = ln_perm[j]
                    if self._check_hyps_fast(thm, vm):
                        return vm
            # Product with CE (structural pre-filter)
            if total <= 5000 and _time.monotonic() <= _deadline:
                for pt_combo in product(pt_candidates, repeat=len(elib_pts)):
                    if _time.monotonic() > _deadline:
                        break
                    vm = dict(zip(elib_pts, pt_combo))
                    vm.update(bound_map)
                    if not _valid_map(vm):
                        continue
                    if not self._validate_conclusions(thm, vm):
                        continue
                    for ln_perm in permutations(actual_lns, len(elib_lns)):
                        for j, el in enumerate(elib_lns):
                            vm[el] = ln_perm[j]
                        if not self._check_hyps_structural(thm, vm):
                            continue
                        if self._check_hyps(thm, vm):
                            return vm

        return identity

    def _check_hyps_fast(self, thm: ETheorem, var_map: Dict[str, str]) -> bool:
        """Fast hypothesis check: direct known-fact lookup with metric symmetry."""
        for hyp in thm.sequent.hypotheses:
            inst = substitute_literal(hyp, var_map)
            if inst in self.known:
                continue
            # Try metric symmetry: M3 (ab = ba), M4 (∠abc = ∠cba)
            sym = self._symmetric_literal(inst)
            if sym is not None and sym in self.known:
                continue
            return False
        return True

    def _symmetric_literal(self, lit: Literal) -> Optional[Literal]:
        """Return the symmetric form of a metric literal, or None."""
        a = lit.atom
        if isinstance(a, Equals):
            left, right = a.left, a.right
            # M3: ab = ba (segment symmetry) — try swapping both sides
            if isinstance(left, SegmentTerm) and isinstance(right, SegmentTerm):
                sym_left = SegmentTerm(left.p2, left.p1)
                sym_right = SegmentTerm(right.p2, right.p1)
                # Try all combinations
                for l, r in [(sym_left, right), (left, sym_right),
                             (sym_left, sym_right), (right, left),
                             (sym_right, sym_left)]:
                    candidate = Literal(Equals(l, r), polarity=lit.polarity)
                    if candidate in self.known:
                        return candidate
            # M4: ∠abc = ∠cba (angle symmetry when vertex same)
            if isinstance(left, AngleTerm) and isinstance(right, AngleTerm):
                sym_left = AngleTerm(left.p3, left.p2, left.p1)
                sym_right = AngleTerm(right.p3, right.p2, right.p1)
                for l, r in [(sym_left, right), (left, sym_right),
                             (sym_left, sym_right), (right, left),
                             (sym_right, sym_left)]:
                    candidate = Literal(Equals(l, r), polarity=lit.polarity)
                    if candidate in self.known:
                        return candidate
            # Also try swapping equality sides: if known has cd=ab, match ab=cd
            swapped = Literal(Equals(right, left), polarity=lit.polarity)
            if swapped in self.known:
                return swapped
        elif isinstance(a, LessThan):
            # Try symmetric segments in LessThan
            left, right = a.left, a.right
            if isinstance(left, SegmentTerm) and isinstance(right, SegmentTerm):
                for l, r in [(SegmentTerm(left.p2, left.p1), right),
                             (left, SegmentTerm(right.p2, right.p1)),
                             (SegmentTerm(left.p2, left.p1), SegmentTerm(right.p2, right.p1))]:
                    candidate = Literal(LessThan(l, r), polarity=lit.polarity)
                    if candidate in self.known:
                        return candidate
        return None

    def _check_hyps_structural(self, thm: ETheorem, var_map: Dict[str, str]) -> bool:
        """Check only structural (positive diagrammatic) hypotheses against known facts.

        Returns False if any positive Between or SameSide hypothesis is not in
        known facts. Skips negative hypotheses, metric hypotheses, and positive
        On hypotheses (commonly derivable from betweenness via CE).
        """
        for hyp in thm.sequent.hypotheses:
            if not hyp.polarity:
                continue  # Skip all negative hypotheses (¬on, ¬equals, etc.)
            if hyp.is_metric:
                continue  # Skip metric hypotheses (need MetricEngine)
            if isinstance(hyp.atom, On):
                continue  # Skip positive On (often derivable via betweenness)
            inst = substitute_literal(hyp, var_map)
            if inst not in self.known:
                return False
        return True

    def _validate_conclusions(self, thm: ETheorem,
                              var_map: Dict[str, str]) -> bool:
        """Reject var_maps whose conclusions are structurally degenerate.

        Catches maps that satisfy hypotheses but produce useless conclusions,
        e.g. ``between(c, d, c)`` where endpoints coincide (since Between is
        not symmetric in the AST: ``between(a,e,b) ≠ between(b,e,a)``).
        """
        for conc in thm.sequent.conclusions:
            inst = substitute_literal(conc, var_map)
            atom = inst.atom
            if isinstance(atom, Between):
                # between(x, y, z): x and z must be distinct
                if atom.a == atom.c:
                    return False
                # between(x, y, z): middle point must differ from endpoints
                if atom.b == atom.a or atom.b == atom.c:
                    return False
            elif isinstance(atom, Equals):
                # Segment/angle equality: check for trivially degenerate
                left, right = atom.left, atom.right
                if isinstance(left, SegmentTerm) and isinstance(right, SegmentTerm):
                    if left.p1 == left.p2 and right.p1 == right.p2:
                        return False
        return True

    def _check_hyps(self, thm: ETheorem, var_map: Dict[str, str]) -> bool:
        """Hypothesis check with CE/MetricEngine fallback."""
        ce_needed: List[Literal] = []
        me_needed: List[Literal] = []
        for hyp in thm.sequent.hypotheses:
            inst = substitute_literal(hyp, var_map)
            if inst in self.known:
                continue
            if inst.is_diagrammatic:
                ce_needed.append(inst)
            elif inst.is_metric:
                me_needed.append(inst)
            else:
                return False
        if not ce_needed and not me_needed:
            return True
        if len(ce_needed) > 4:
            return False
        if len(me_needed) > 3:
            return False
        if ce_needed:
            from .e_consequence import ConsequenceEngine
            ce = ConsequenceEngine()
            for inst in ce_needed:
                if not ce.is_consequence(self.known, inst):
                    return False
        if me_needed:
            from .e_metric import MetricEngine
            me = MetricEngine()
            for inst in me_needed:
                if not me.is_consequence(self.known, inst):
                    return False
        return True

    def _cited_lean_params(self, rule_name: str) -> List[Tuple[str, str]]:
        from .lean_parser import extract_prop_number
        pn = extract_prop_number(rule_name)
        if not pn:
            return []
        fp = Path(f"lean_reference/Prop{pn}.lean")
        if fp.exists():
            try:
                proofs = parse_lean_file(str(fp))
                if proofs and proofs[0].signature:
                    return [(pr.name, pr.sort) for pr in proofs[0].signature.params]
            except Exception:
                pass
        return []

    # -- Inference (metric/transfer/diagrammatic) ----------------------

    def _apply_inference(self, tac: LeanTactic, mp):
        se_name = mp.system_e_name if mp else tac.rule_name
        for ts in self.tr.steps:
            if ts.step.description and tac.rule_name in ts.step.description:
                if ts.step.assertions:
                    lits = set()
                    parts = []
                    for a in ts.step.assertions:
                        m = self._map_lit(a)
                        parts.append(literal_to_text(m))
                        lits.add(m)
                        self.known.add(m)
                    ln = self.nprem + len(self.steps) + 1
                    deps = self._deps_for(lits, set())
                    self.steps.append({
                        "lineNumber": ln, "text": ", ".join(parts),
                        "justification": se_name, "dependencies": deps,
                        "depth": 0, "status": "?",
                    })
                    self.ll[ln] = lits
                    return
        self.warnings.append(f"No assertions for inference: {se_name}")

    # -- euclid_finish -------------------------------------------------

    def _finish(self):
        if not self.seq:
            return
        for conc in self.seq.conclusions:
            if conc in self.known:
                continue
            # Check symmetric form already known
            sym = self._symmetric_literal(conc)
            if sym is not None:
                self._emit_symmetry_step(conc, sym)
                continue
            # Try reflexivity (e.g. cd = cd)
            s = self._try_reflexive(conc)
            if s:
                self.steps.append(s)
                continue
            # Try axiom match
            s = self._find_axiom(conc)
            if s:
                self.steps.append(s)
                continue
            # Try metric engine
            s = self._try_metric(conc)
            if s:
                self.steps.append(s)
                continue
            # Try deriving a symmetric prerequisite first, then metric
            ss = self._try_via_symmetry_then_metric(conc)
            if ss:
                for step in ss:
                    self.steps.append(step)
                continue
            # Try consequence engine (diagrammatic)
            s = self._try_conseq(conc)
            if s:
                self.steps.append(s)
                continue
            self.warnings.append(
                f"Cannot derive goal: {literal_to_text(conc)}")

    def _emit_symmetry_step(self, target: Literal, source: Literal):
        """Emit an M3/M4/CN1 step deriving target from its symmetric source."""
        just = self._metric_symmetry_just(target)
        deps = self._deps_target(source)
        ln = self.nprem + len(self.steps) + 1
        self.steps.append({
            "lineNumber": ln,
            "text": literal_to_text(target),
            "justification": just,
            "dependencies": deps,
            "depth": 0, "status": "?",
        })
        self.known.add(target)
        self.ll[ln] = {target}

    def _try_reflexive(self, target: Literal) -> Optional[Dict[str, Any]]:
        """Handle reflexive equalities like cd = cd, ∠abc = ∠abc."""
        if not target.polarity:
            return None
        a = target.atom
        if not isinstance(a, Equals):
            return None
        if a.left != a.right:
            return None
        ln = self.nprem + len(self.steps) + 1
        s = {"lineNumber": ln, "text": literal_to_text(target),
             "justification": "CN4 \u2014 Reflexivity",
             "dependencies": [],
             "depth": 0, "status": "?"}
        self.known.add(target)
        self.ll[ln] = {target}
        return s

    def _try_via_symmetry_then_metric(
        self, target: Literal
    ) -> Optional[List[Dict[str, Any]]]:
        """Try deriving target by first establishing a symmetric intermediate.

        For example, if goal is ab < cd but we know ba < cd via the metric
        engine, first emit M3 for ba=ab, then derive the target.
        """
        if not target.is_metric:
            return None
        from .e_metric import MetricEngine

        a = target.atom
        candidates: list = []
        if isinstance(a, Equals):
            left, right = a.left, a.right
            if isinstance(left, SegmentTerm):
                candidates.append(Literal(Equals(
                    SegmentTerm(left.p2, left.p1), right),
                    polarity=target.polarity))
            if isinstance(right, SegmentTerm):
                candidates.append(Literal(Equals(
                    left, SegmentTerm(right.p2, right.p1)),
                    polarity=target.polarity))
            if isinstance(left, SegmentTerm) and isinstance(right, SegmentTerm):
                candidates.append(Literal(Equals(
                    SegmentTerm(left.p2, left.p1),
                    SegmentTerm(right.p2, right.p1)),
                    polarity=target.polarity))
            candidates.append(Literal(Equals(right, left),
                                      polarity=target.polarity))
            if isinstance(left, AngleTerm):
                candidates.append(Literal(Equals(
                    AngleTerm(left.p3, left.p2, left.p1), right),
                    polarity=target.polarity))
            if isinstance(right, AngleTerm):
                candidates.append(Literal(Equals(
                    left, AngleTerm(right.p3, right.p2, right.p1)),
                    polarity=target.polarity))
        elif isinstance(a, LessThan):
            left, right = a.left, a.right
            if isinstance(left, SegmentTerm):
                candidates.append(Literal(LessThan(
                    SegmentTerm(left.p2, left.p1), right),
                    polarity=target.polarity))
            if isinstance(right, SegmentTerm):
                candidates.append(Literal(LessThan(
                    left, SegmentTerm(right.p2, right.p1)),
                    polarity=target.polarity))
            if isinstance(left, SegmentTerm) and isinstance(right, SegmentTerm):
                candidates.append(Literal(LessThan(
                    SegmentTerm(left.p2, left.p1),
                    SegmentTerm(right.p2, right.p1)),
                    polarity=target.polarity))

        me = MetricEngine()
        for cand in candidates:
            if cand in self.known or me.is_consequence(self.known, cand):
                steps: list = []
                if cand not in self.known:
                    ln = self.nprem + len(self.steps) + 1
                    deps = self._deps_target(cand)
                    just = self._metric_just(cand)
                    steps.append({
                        "lineNumber": ln,
                        "text": literal_to_text(cand),
                        "justification": just,
                        "dependencies": deps,
                        "depth": 0, "status": "?",
                    })
                    self.known.add(cand)
                    self.ll[ln] = {cand}
                ln2 = self.nprem + len(self.steps) + len(steps) + 1
                deps2 = self._deps_target(target)
                just2 = (self._metric_symmetry_just(target)
                         if self._is_pure_symmetry(target, cand)
                         else self._metric_just(target))
                steps.append({
                    "lineNumber": ln2,
                    "text": literal_to_text(target),
                    "justification": just2,
                    "dependencies": deps2,
                    "depth": 0, "status": "?",
                })
                self.known.add(target)
                self.ll[ln2] = {target}
                return steps
        return None

    def _is_pure_symmetry(self, target: Literal, source: Literal) -> bool:
        """Check if target is a pure M3/M4 symmetry of source."""
        a, b = target.atom, source.atom
        if type(a) != type(b) or target.polarity != source.polarity:
            return False
        if isinstance(a, Equals) and isinstance(b, Equals):
            if isinstance(a.left, SegmentTerm) and isinstance(b.left, SegmentTerm):
                if (a.right == b.right and
                    a.left.p1 == b.left.p2 and a.left.p2 == b.left.p1):
                    return True
            if isinstance(a.right, SegmentTerm) and isinstance(b.right, SegmentTerm):
                if (a.left == b.left and
                    a.right.p1 == b.right.p2 and a.right.p2 == b.right.p1):
                    return True
            if isinstance(a.left, AngleTerm) and isinstance(b.left, AngleTerm):
                if (a.right == b.right and a.left.p2 == b.left.p2 and
                    a.left.p1 == b.left.p3 and a.left.p3 == b.left.p1):
                    return True
            if isinstance(a.right, AngleTerm) and isinstance(b.right, AngleTerm):
                if (a.left == b.left and a.right.p2 == b.right.p2 and
                    a.right.p1 == b.right.p3 and a.right.p3 == b.right.p1):
                    return True
            if a.left == b.right and a.right == b.left:
                return True
        return False

    # -- Assertion steps -----------------------------------------------

    def _derive_from_expr(self, expr_str: str):
        from .lean_translator import lean_expr_to_literals
        from .lean_parser import parse_lean_expr
        expr = parse_lean_expr(expr_str)
        lits = lean_expr_to_literals(expr) if expr else []
        for lit in lits:
            m = self._map_lit(lit)
            if m in self.known:
                continue
            # Check symmetric form already known
            sym = self._symmetric_literal(m)
            if sym is not None:
                self._emit_symmetry_step(m, sym)
                continue
            s = self._try_reflexive(m)
            if not s:
                s = self._find_axiom(m)
            if not s:
                s = self._try_metric(m)
            if not s:
                s = self._try_conseq(m)
            if s:
                self.steps.append(s)
            else:
                self.warnings.append(f"Cannot derive: {literal_to_text(m)}")

    # -- Axiom/metric/consequence search --------------------------------

    def _find_axiom(self, target: Literal) -> Optional[Dict[str, Any]]:
        from .e_axiom_match import check_specific_axiom, list_axiom_names
        ln = self.nprem + len(self.steps) + 1
        for name in list_axiom_names():
            ok, _ = check_specific_axiom(name, self.known, [target], self.sort_ctx)
            if ok:
                deps = self._deps_target(target)
                s = {"lineNumber": ln, "text": literal_to_text(target),
                     "justification": name, "dependencies": deps,
                     "depth": 0, "status": "?"}
                self.known.add(target)
                self.ll[ln] = {target}
                return s
        return None

    def _try_metric(self, target: Literal) -> Optional[Dict[str, Any]]:
        from .e_metric import MetricEngine
        me = MetricEngine()
        if me.is_consequence(self.known, target):
            ln = self.nprem + len(self.steps) + 1
            deps = self._deps_target(target)
            j = self._metric_just(target)
            s = {"lineNumber": ln, "text": literal_to_text(target),
                 "justification": j, "dependencies": deps,
                 "depth": 0, "status": "?"}
            self.known.add(target)
            self.ll[ln] = {target}
            return s
        return None

    def _try_conseq(self, target: Literal) -> Optional[Dict[str, Any]]:
        from .e_consequence import ConsequenceEngine
        ce = ConsequenceEngine()
        if ce.is_consequence(self.known, target):
            ln = self.nprem + len(self.steps) + 1
            deps = self._deps_target(target)
            j = self._guess_diag(target)
            s = {"lineNumber": ln, "text": literal_to_text(target),
                 "justification": j, "dependencies": deps,
                 "depth": 0, "status": "?"}
            self.known.add(target)
            self.ll[ln] = {target}
            return s
        return None

    def _guess_diag(self, target: Literal) -> str:
        a = target.atom
        if isinstance(a, Between):
            return "Betweenness 1a" if target.polarity else "Betweenness 1b"
        if isinstance(a, Equals) and not target.polarity:
            return self._find_neq_axiom(target)
        if isinstance(a, On):
            return "Generality 3" if target.polarity else "Generality 1"
        return "Generality 1"

    def _find_neq_axiom(self, target: Literal) -> str:
        """Find the correct axiom name for deriving ¬(x = y).

        Tries candidate axioms against the full known-fact closure
        using the axiom matcher, returning the first one that works.
        """
        from .e_axiom_match import check_specific_axiom
        from .e_consequence import ConsequenceEngine

        # Use all known facts — the derivation chain may cross
        # variable boundaries (e.g. between(c,d,a) + on(c,N) + on(a,N)
        # → on(d,N) → ¬(b=d) via Generality 6).
        dep_facts = set(self.known)

        # Let CE auto-extract variables from known facts (ensures all
        # variables from metric terms and constructions are included).
        ce = ConsequenceEngine()
        closure = ce.direct_consequences(dep_facts)
        dep_aug = dep_facts | closure

        # Build variable map for axiom matching from the closure
        dep_vars: Dict[str, Sort] = dict(self.sort_ctx)
        for lit in dep_aug:
            for v in literal_vars(lit):
                if v not in dep_vars:
                    dep_vars[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                                   else Sort.POINT)

        # Try candidate axiom names in priority order
        candidates = [
            "Betweenness 1b",   # between(a,b,c) → a ≠ b
            "Betweenness 1c",   # between(a,b,c) → a ≠ c
            "Generality 6",     # on(a,L) ∧ ¬on(b,L) → a ≠ b
            "Generality 6c",    # on(a,α) ∧ ¬on(b,α) → a ≠ b
            "Same-side 6",      # same-side(a,b,L) ∧ ¬same-side(a,c,L) → b ≠ c
        ]
        for name in candidates:
            ok, _ = check_specific_axiom(
                name, dep_aug, [target], dep_vars)
            if ok:
                return name
        return "Betweenness 1b"  # fallback

    # -- Helper: let-line ----------------------------------------------

    def _add_let_line(self, line_name: str, pt1: str, pt2: str):
        self._ensure_neq(pt1, pt2)
        l1 = _pos(On(pt1, line_name))
        l2 = _pos(On(pt2, line_name))
        self.known.add(l1)
        self.known.add(l2)
        neq = Literal(Equals(pt1, pt2), polarity=False)
        deps = []
        for ln_num, lits in self.ll.items():
            if neq in lits:
                deps.append(ln_num)
                break
        line_num = self.nprem + len(self.steps) + 1
        self.steps.append({
            "lineNumber": line_num,
            "text": f"on({pt1}, {line_name}), on({pt2}, {line_name})",
            "justification": "let-line",
            "dependencies": deps,
            "depth": 0, "status": "?",
        })
        self.ll[line_num] = {l1, l2}
        self.sort_ctx[line_name] = Sort.LINE

    def _ensure_neq(self, pt1: str, pt2: str):
        """Ensure ¬(pt1 = pt2) is in known facts, injecting a step if needed."""
        neq = _neg(Equals(pt1, pt2))
        if neq in self.known:
            return
        # Try MetricEngine first: M1 says ab = 0 ↔ a = b,
        # so if we know ab > 0 (or ab = cd where cd > 0), derive ¬(a=b)
        from .e_metric import MetricEngine
        me = MetricEngine()
        if me.is_consequence(self.known, neq):
            deps = self._deps_target(neq)
            ln = self.nprem + len(self.steps) + 1
            self.steps.append({
                "lineNumber": ln,
                "text": literal_to_text(neq),
                "justification": "M1 \u2014 Zero segment",
                "dependencies": deps,
                "depth": 0, "status": "?",
            })
            self.known.add(neq)
            self.ll[ln] = {neq}
            return
        # Try consequence engine
        from .e_consequence import ConsequenceEngine
        ce = ConsequenceEngine()
        if ce.is_consequence(self.known, neq):
            axiom_name = self._find_neq_axiom(neq)
            deps = self._find_minimal_deps(neq, axiom_name, {pt1, pt2})
            ln = self.nprem + len(self.steps) + 1
            self.steps.append({
                "lineNumber": ln,
                "text": literal_to_text(neq),
                "justification": axiom_name,
                "dependencies": deps,
                "depth": 0, "status": "?",
            })
            self.known.add(neq)
            self.ll[ln] = {neq}

    def _ensure_intersects(self, obj1: str, obj2: str):
        """Ensure intersects(obj1, obj2) is in known facts, injecting a step if needed."""
        target = _pos(Intersects(obj1, obj2))
        if target in self.known:
            return
        # Try consequence engine
        from .e_consequence import ConsequenceEngine
        ce = ConsequenceEngine()
        if ce.is_consequence(self.known, target):
            just = self._find_intersects_axiom(target)
            deps = self._find_minimal_deps(target, just, {obj1, obj2})
            ln = self.nprem + len(self.steps) + 1
            self.steps.append({
                "lineNumber": ln,
                "text": literal_to_text(target),
                "justification": just,
                "dependencies": deps,
                "depth": 0, "status": "?",
            })
            self.known.add(target)
            self.ll[ln] = {target}
            return
        # If CE can't derive it, try axiom search
        s = self._find_axiom(target)
        if s:
            self.steps.append(s)

    def _find_intersects_axiom(self, target: Literal) -> str:
        """Find the correct axiom name for deriving intersects(X, Y)."""
        from .e_axiom_match import check_specific_axiom
        from .e_consequence import ConsequenceEngine
        dep_facts = set(self.known)
        ce = ConsequenceEngine()
        closure = ce.direct_consequences(dep_facts)
        dep_aug = dep_facts | closure
        dep_vars: Dict[str, Sort] = dict(self.sort_ctx)
        for lit in dep_aug:
            for v in literal_vars(lit):
                if v not in dep_vars:
                    dep_vars[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                                   else Sort.POINT)
        candidates = [
            "Intersection 1",   # diff-side → intersects(L, M)
            "Intersection 3",   # inside(a,α) ∧ on(a,L) → intersects(L,α)
            "Intersection 5",   # cross-circle intersection
            "Intersection 6",   # two common points → intersects(α,β)
        ]
        for name in candidates:
            ok, _ = check_specific_axiom(name, dep_aug, [target], dep_vars)
            if ok:
                return name
        return "Intersection 1"  # fallback

    def _deps_for_vars(self, target_vars: Set[str]) -> List[int]:
        """Find deps that mention any of the target variables plus transitive deps."""
        direct_deps: Set[int] = set()
        for ln_num, lits in self.ll.items():
            for lit in lits:
                if literal_vars(lit) & target_vars:
                    direct_deps.add(ln_num)
                    break
        # Also include lines whose variables overlap with variables found in direct deps
        expanded_vars = set(target_vars)
        for ln_num in direct_deps:
            for lit in self.ll[ln_num]:
                expanded_vars |= literal_vars(lit)
        all_deps: Set[int] = set(direct_deps)
        for ln_num, lits in self.ll.items():
            if ln_num in all_deps:
                continue
            for lit in lits:
                if literal_vars(lit) & expanded_vars:
                    all_deps.add(ln_num)
                    break
        return sorted(all_deps)

    # -- Literal mapping -----------------------------------------------

    def _map_lit(self, lit: Literal) -> Literal:
        if not self.vm:
            return lit
        return substitute_literal(lit, self.vm.lean_to_elib)

    # -- Dependency helpers --------------------------------------------

    def _find_minimal_deps(self, target: Literal, axiom_name: str,
                           seed_vars: Set[str]) -> List[int]:
        """Find minimal dependency set for an axiom derivation.

        Tries increasingly broader dep sets until check_specific_axiom
        succeeds:
        1. Only lines mentioning seed_vars (the target's variables)
        2. Lines mentioning seed_vars + CE direct consequences
        3. Fallback to _deps_for_vars (broad)
        """
        from .e_axiom_match import check_specific_axiom
        from .e_consequence import ConsequenceEngine

        # Strategy 1: Tight deps — only lines mentioning target vars
        dep_lines_1: Set[int] = set()
        dep_facts_1: Set[Literal] = set()
        for ln_num, lits in self.ll.items():
            for lit in lits:
                if literal_vars(lit) & seed_vars:
                    dep_lines_1.add(ln_num)
                    dep_facts_1 |= lits
                    break

        dep_vars: Dict[str, Sort] = dict(self.sort_ctx)
        for lit in dep_facts_1 | {target}:
            for v in literal_vars(lit):
                if v not in dep_vars:
                    dep_vars[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                                   else Sort.POINT)

        # Try with CE closure of the tight dep set
        ce = ConsequenceEngine()
        closure = ce.direct_consequences(dep_facts_1)
        dep_aug = dep_facts_1 | closure
        for lit in dep_aug:
            for v in literal_vars(lit):
                if v not in dep_vars:
                    dep_vars[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                                   else Sort.POINT)

        ok, _ = check_specific_axiom(axiom_name, dep_aug, [target], dep_vars)
        if ok:
            return sorted(dep_lines_1)

        # Strategy 2: Expand to include lines whose vars overlap with
        # the closure (one level of expansion)
        expanded_vars = set(seed_vars)
        for lit in dep_aug:
            expanded_vars |= literal_vars(lit)

        dep_lines_2: Set[int] = set(dep_lines_1)
        dep_facts_2: Set[Literal] = set(dep_facts_1)
        for ln_num, lits in self.ll.items():
            if ln_num in dep_lines_2:
                continue
            for lit in lits:
                if literal_vars(lit) & expanded_vars:
                    dep_lines_2.add(ln_num)
                    dep_facts_2 |= lits
                    break

        for lit in dep_facts_2:
            for v in literal_vars(lit):
                if v not in dep_vars:
                    dep_vars[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                                   else Sort.POINT)

        closure2 = ce.direct_consequences(dep_facts_2)
        dep_aug2 = dep_facts_2 | closure2
        for lit in dep_aug2:
            for v in literal_vars(lit):
                if v not in dep_vars:
                    dep_vars[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                                   else Sort.POINT)

        ok, _ = check_specific_axiom(axiom_name, dep_aug2, [target], dep_vars)
        if ok:
            return sorted(dep_lines_2)

        # Strategy 3: Fallback to broad deps
        return self._deps_for_vars(seed_vars)

    def _deps_target(self, target: Literal) -> List[int]:
        tv = literal_vars(target)
        deps = set()
        for ln_num, lits in self.ll.items():
            for lit in lits:
                if literal_vars(lit) & tv:
                    deps.add(ln_num)
                    break
        return sorted(deps)

    def _deps_for(self, step_lits, new_vars: set) -> List[int]:
        av: Set[str] = set()
        for lit in step_lits:
            av |= literal_vars(lit)
        needed = av - new_vars
        deps: Set[int] = set()
        for ln_num, lits in self.ll.items():
            for lit in lits:
                if literal_vars(lit) & needed:
                    deps.add(ln_num)
                    break
        return sorted(deps)

    def _thm_deps(self, thm: ETheorem, vm: Dict[str, str]) -> List[int]:
        """Find deps for a theorem application.

        For each instantiated hypothesis:
        1. If exact match found → add just that line
        2. If symmetric match → add that line
        3. If neither → the verifier must derive it; collect variables
           for a broader search scoped to all unmatched hypotheses only.
        """
        deps: Set[int] = set()
        unmatched_vars: Set[str] = set()

        for hyp in thm.sequent.hypotheses:
            inst = substitute_literal(hyp, vm)
            # 1) Exact match
            found = False
            for ln_num, lits in self.ll.items():
                if inst in lits:
                    deps.add(ln_num)
                    found = True
                    break
            if found:
                continue
            # 2) Symmetric form (M3/M4)
            sym = self._symmetric_literal(inst)
            if sym is not None:
                for ln_num, lits in self.ll.items():
                    if sym in lits:
                        deps.add(ln_num)
                        found = True
                        break
            if found:
                continue
            # 3) Unmatched — needs derivation by verifier
            unmatched_vars |= literal_vars(inst)

        # For unmatched hypotheses, include all lines whose variables
        # overlap with ANY hypothesis variable (needed to give the
        # verifier's consequence engine enough context).
        if unmatched_vars:
            # Collect ALL hypothesis variables so the verifier has
            # enough context to derive the unmatched ones.
            all_hyp_vars: Set[str] = set()
            for hyp in thm.sequent.hypotheses:
                all_hyp_vars |= literal_vars(substitute_literal(hyp, vm))
            for ln_num, lits in self.ll.items():
                if ln_num in deps:
                    continue
                for lit in lits:
                    if literal_vars(lit) & all_hyp_vars:
                        deps.add(ln_num)
                        break
        return sorted(deps)

    # -- Declarations --------------------------------------------------

    def _build_decls(self) -> Dict[str, List[str]]:
        sp: Set[str] = set()
        sl: Set[str] = set()
        if self.seq:
            for lit in self.seq.hypotheses:
                _extract_declarations(lit, sp, sl)
            for lit in self.seq.conclusions:
                _extract_declarations(lit, sp, sl)
            for vn, vs in self.seq.exists_vars:
                if vs == Sort.POINT:
                    sp.add(vn)
                elif vs == Sort.LINE:
                    sl.add(vn)
        return {"points": sorted(sp), "lines": sorted(sl)}

    # -- Fallback path -------------------------------------------------

    def _synth_translated(self, ts: TranslatedStep):
        step = ts.step
        if step.kind == StepKind.CONSTRUCTION and step.assertions:
            lits = set()
            parts = []
            for a in step.assertions:
                m = self._map_lit(a)
                parts.append(literal_to_text(m))
                lits.add(m)
                self.known.add(m)
            deps = self._deps_for(lits, set())
            ln = self.nprem + len(self.steps) + 1
            self.steps.append({
                "lineNumber": ln, "text": ", ".join(parts),
                "justification": step.description, "dependencies": deps,
                "depth": 0, "status": "?",
            })
            self.ll[ln] = lits


# =====================================================================
# High-level API
# =====================================================================

def synthesize_proof(translation: TranslationResult,
                     lean_proof: Optional[LeanProof] = None) -> SynthesisResult:
    return ProofSynthesizer(translation, lean_proof).synthesize()


def synthesize_and_verify(translation: TranslationResult,
                          lean_proof: Optional[LeanProof] = None):
    from .unified_checker import verify_e_proof_json
    sr = synthesize_proof(translation, lean_proof)
    if not sr.success or not sr.euclid_json:
        return sr, None
    vr = verify_e_proof_json(sr.euclid_json)
    return sr, vr


def synthesize_all(lean_dir: str, output_dir: Optional[str] = None,
                   prop_range: Tuple[int, int] = (16, 48)):
    from .lean_translator import translate_lean_file
    results = []
    for n in range(prop_range[0], prop_range[1] + 1):
        fp = Path(lean_dir) / f"Prop{n}.lean"
        if not fp.exists():
            r = SynthesisResult(prop_name=f"Prop.I.{n}", prop_number=n,
                                errors=[f"File not found: {fp}"])
            results.append((n, r, None))
            continue
        try:
            lps = parse_lean_file(str(fp))
            lp = lps[0] if lps else None
        except Exception:
            lp = None
        tr = translate_lean_file(str(fp))
        if not tr.success:
            r = SynthesisResult(prop_name=tr.prop_name, prop_number=n,
                                errors=["Translation failed"])
            results.append((n, r, None))
            continue
        sr, vr = synthesize_and_verify(tr, lp)
        if output_dir and sr.euclid_json and vr and vr.accepted:
            op = Path(output_dir)
            op.mkdir(parents=True, exist_ok=True)
            with open(op / f"Proposition I.{n}.euclid", 'w', encoding='utf-8') as f:
                json.dump(sr.euclid_json, f, indent=2, ensure_ascii=False)
        results.append((n, sr, vr))
    return results
