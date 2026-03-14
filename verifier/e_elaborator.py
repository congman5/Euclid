"""
e_elaborator.py — Proof elaboration layer (tactic engine) for System E.

Transforms high-level proof steps into fully explicit primitive steps
that the strict checker can verify.  This is the bridge between
human-readable proofs ("Metric", "Angle transfer 9") and the
machine-checkable primitive justifications ("M3 — Symmetry", "CN1",
"Segment transfer 4").

Design:
  - Elaboration runs BEFORE strict checking.
  - The strict checker only sees primitive steps; it does not change.
  - If elaboration fails, the original step is preserved and the strict
    checker will report the real error.  This means elaboration bugs
    cause failures, never unsoundness.
  - Each tactic is idempotent: if a step is already primitive, it passes
    through unchanged.

Usage:
    elaborated = elaborate_proof(proof_json)
    result = verify_e_proof_json(elaborated)
"""
from __future__ import annotations

import copy
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple

from .e_ast import (
    Sort, Literal, Equals, LessThan,
    SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag,
    On, Between, SameSide, Center, Inside, Intersects,
    substitute_literal, literal_vars, atom_vars,
)
from .e_consequence import ConsequenceEngine
from .e_metric import MetricEngine
from .e_transfer import TransferEngine
from .e_axioms import ALL_DIAGRAMMATIC_AXIOMS, ALL_TRANSFER_AXIOMS
from .e_parser import parse_literal_list, EParseError


# ═══════════════════════════════════════════════════════════════════════
# Elaboration result
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class ElaborationResult:
    """Result of elaborating a proof."""
    proof_json: dict  # The elaborated proof JSON
    elaborated: bool = False  # True if any lines were expanded
    original_to_elaborated: Dict[int, List[int]] = field(
        default_factory=dict)  # original line id -> elaborated line ids
    notes: List[str] = field(default_factory=list)


# ═══════════════════════════════════════════════════════════════════════
# Core elaboration engine
# ═══════════════════════════════════════════════════════════════════════

class ElaborationEngine:
    """Expands high-level proof steps into primitive steps.

    The engine maintains a running state of known facts (mirroring
    what the strict checker would see) so that each tactic can reason
    about what's available.
    """

    def __init__(self):
        self.sort_ctx: Dict[str, Sort] = {}
        self.known: Set[Literal] = set()
        self.variables: Dict[str, Sort] = {}
        self.consequence_engine = ConsequenceEngine(ALL_DIAGRAMMATIC_AXIOMS)
        self.metric_engine = MetricEngine()
        self.transfer_engine = TransferEngine()
        self._next_id = 10000  # elaborated lines get high IDs to avoid clashes

    def _fresh_id(self) -> int:
        """Generate a fresh line ID for elaborated steps."""
        self._next_id += 1
        return self._next_id

    def elaborate(self, proof_json: dict) -> ElaborationResult:
        """Elaborate a full proof JSON, expanding high-level steps.

        Returns an ElaborationResult with the elaborated proof and
        a mapping from original line IDs to elaborated line IDs.
        """
        result = ElaborationResult(proof_json=copy.deepcopy(proof_json))
        self._init_state(result.proof_json)

        new_lines: List[dict] = []
        for line in result.proof_json.get("lines", []):
            expanded = self._elaborate_line(line)
            if expanded is None:
                # No elaboration needed or possible; keep original
                new_lines.append(line)
                self._update_known(line)
                result.original_to_elaborated[line["id"]] = [line["id"]]
            else:
                result.elaborated = True
                elab_ids = []
                for eline in expanded:
                    new_lines.append(eline)
                    self._update_known(eline)
                    elab_ids.append(eline["id"])
                result.original_to_elaborated[line["id"]] = elab_ids
                result.notes.append(
                    f"Line {line['id']} [{line.get('justification', '')}] "
                    f"elaborated into {len(expanded)} steps")

        result.proof_json["lines"] = new_lines
        return result

    def _init_state(self, proof_json: dict) -> None:
        """Initialize state from proof declarations and premises."""
        decl = proof_json.get("declarations", {})
        for p in decl.get("points", []):
            self.sort_ctx[p] = Sort.POINT
            self.variables[p] = Sort.POINT
        for ln in decl.get("lines", []):
            self.sort_ctx[ln] = Sort.LINE
            self.variables[ln] = Sort.LINE

        for prem_str in proof_json.get("premises", []):
            try:
                lits = parse_literal_list(prem_str, self.sort_ctx)
                for lit in lits:
                    self.known.add(lit)
                    self._register_vars(lit)
            except EParseError:
                pass

    def _register_vars(self, lit: Literal) -> None:
        """Register variables from a literal into sort context."""
        for vname in atom_vars(lit.atom):
            if vname not in self.variables:
                self.variables[vname] = _infer_sort(vname, self.sort_ctx)
            if vname not in self.sort_ctx:
                self.sort_ctx[vname] = _infer_sort(vname, self.sort_ctx)

    def _update_known(self, line: dict) -> None:
        """Add a line's literals to the known set (for subsequent lines)."""
        stmt = line.get("statement", "")
        try:
            lits = parse_literal_list(stmt, self.sort_ctx)
            for lit in lits:
                self.known.add(lit)
                self._register_vars(lit)
        except EParseError:
            pass

    def _elaborate_line(self, line: dict) -> Optional[List[dict]]:
        """Try to elaborate a single proof line.

        Returns None if the line is already primitive or can't be
        elaborated.  Returns a list of replacement lines otherwise.
        """
        just = line.get("justification", "")
        stmt = line.get("statement", "")
        refs = line.get("refs", [])
        depth = line.get("depth", 0)
        lid = line.get("id", 0)

        try:
            target_lits = parse_literal_list(stmt, self.sort_ctx)
        except EParseError:
            return None

        if not target_lits:
            return None

        # Dispatch to the appropriate tactic
        if just == "Metric":
            return self._elaborate_metric(
                lid, depth, target_lits, refs, stmt)
        elif just.startswith("Angle transfer"):
            return self._elaborate_angle_transfer(
                lid, depth, target_lits, refs, stmt)
        elif just.startswith("Area transfer"):
            return self._elaborate_area_transfer(
                lid, depth, target_lits, refs, stmt)
        elif just.startswith("Prop.") or just.startswith("prop."):
            return self._elaborate_theorem(
                lid, depth, target_lits, refs, stmt, just)
        elif just in ("Diagrammatic", "diagrammatic"):
            return self._elaborate_diagrammatic(
                lid, depth, target_lits, refs, stmt)
        elif just in ("⊥-intro", "Contradiction"):
            return self._elaborate_bot_intro(
                lid, depth, target_lits, refs, stmt)

        # Already primitive or unrecognized — pass through
        return None

    # ══════════════════════════════════════════════════════════════════
    # Metric elaboration tactic
    # ══════════════════════════════════════════════════════════════════

    def _elaborate_metric(
        self, lid: int, depth: int,
        targets: List[Literal], refs: List[int], stmt: str,
    ) -> Optional[List[dict]]:
        """Elaborate a bare 'Metric' step into specific metric axiom steps.

        Checks each target literal against the metric engine.  If
        derivable, emits the most specific justification possible:
          - M3 for segment symmetry (ab = ba)
          - M4 for angle vertex symmetry (∠abc = ∠cba)
          - M8 for area symmetry (△abc = △cab)
          - CN1 for transitivity (a = b, b = c → a = c)
          - CN4 for reflexivity (a = a)
          - CN5 for whole > part
          - M1 for zero segment / point disequality
          - < trichotomy for equality from ¬(a<b) and ¬(b<a)
        """
        me = MetricEngine()
        me.process_literals(self.known)

        elaborated = []
        for lit in targets:
            specific_just = self._identify_metric_rule(lit, me)
            if specific_just is None:
                # Can't determine specific rule; check if at least derivable
                if me.is_consequence(self.known, lit):
                    specific_just = "Metric"
                else:
                    # Not derivable — leave original for error reporting
                    return None

            elaborated.append({
                "id": lid if len(targets) == 1 else self._fresh_id(),
                "depth": depth,
                "statement": str(lit),
                "justification": specific_just,
                "refs": refs,
            })

        # If we emitted multiple lines for a multi-literal statement,
        # use the original ID for the last one (the one the goal checks)
        if len(elaborated) > 1:
            elaborated[-1]["id"] = lid

        return elaborated

    def _identify_metric_rule(
        self, lit: Literal, me: MetricEngine
    ) -> Optional[str]:
        """Identify the most specific metric axiom rule for a literal."""
        atom = lit.atom

        # Point disequality: ¬(a = b) from nonzero segment
        if (not lit.polarity and isinstance(atom, Equals)
                and isinstance(atom.left, str)
                and isinstance(atom.right, str)):
            # Check if derivable via M1 (segment nonzero)
            seg = SegmentTerm(atom.left, atom.right)
            if me._check_literal(Literal(Equals(seg, ZeroMag(Sort.SEGMENT)),
                                         polarity=False)):
                return "M1 — Zero segment"
            # Also check via metric consequence
            if me.is_consequence(self.known, lit):
                return "M1 — Zero segment"
            return None

        # Point equality: a = b
        if (lit.polarity and isinstance(atom, Equals)
                and isinstance(atom.left, str)
                and isinstance(atom.right, str)):
            # Check < trichotomy: ¬(a < b) ∧ ¬(b < a) → a = b
            neg_lt1 = Literal(LessThan(
                SegmentTerm(atom.left, atom.right),
                SegmentTerm(atom.right, atom.left)), polarity=False)
            neg_lt2 = Literal(LessThan(
                SegmentTerm(atom.right, atom.left),
                SegmentTerm(atom.left, atom.right)), polarity=False)
            # Actually for point equality we can't use segment trichotomy
            # Check metric engine
            if me.is_consequence(self.known, lit):
                return "Metric"
            return None

        if not isinstance(atom, (Equals, LessThan)):
            return None

        # Diagrammatic literal showing up in metric context
        if lit.is_diagrammatic:
            return None

        # Metric equality: x = y
        if lit.polarity and isinstance(atom, Equals):
            left, right = atom.left, atom.right

            # CN4 reflexivity: x = x
            if left == right:
                return "CN4 — Reflexivity"

            # M3 segment symmetry: ab = ba
            if (isinstance(left, SegmentTerm)
                    and isinstance(right, SegmentTerm)
                    and left.p1 == right.p2 and left.p2 == right.p1):
                return "M3 — Symmetry"

            # M4 angle vertex symmetry: ∠abc = ∠cba
            if (isinstance(left, AngleTerm)
                    and isinstance(right, AngleTerm)
                    and left.p1 == right.p3 and left.p2 == right.p2
                    and left.p3 == right.p1):
                return "M4 — Angle symmetry"

            # M8 area symmetry
            if (isinstance(left, AreaTerm)
                    and isinstance(right, AreaTerm)):
                if (left.p1 == right.p3 and left.p2 == right.p1
                        and left.p3 == right.p2):
                    return "M8 — Area symmetry"
                if (left.p1 == right.p1 and left.p2 == right.p3
                        and left.p3 == right.p2):
                    return "M8 — Area symmetry"

            # CN1 transitivity: if x = z and z = y both known
            me_copy = MetricEngine()
            me_copy.process_literals(self.known)
            if me_copy._check_literal(lit):
                return "CN1 — Transitivity"

            # General metric consequence
            if me.is_consequence(self.known, lit):
                return "Metric"

        # Metric inequality: x < y
        if lit.polarity and isinstance(atom, LessThan):
            # CN5 whole > part: if a + b = c and b > 0 then a < c
            me_copy = MetricEngine()
            me_copy.process_literals(self.known)
            if me_copy._check_literal(lit):
                return "CN5 — Whole > Part"
            if me.is_consequence(self.known, lit):
                return "Metric"

        # Negated metric: ¬(x = y) for magnitude terms
        if not lit.polarity and isinstance(atom, Equals):
            if me.is_consequence(self.known, lit):
                return "Metric"

        # < trichotomy: ab = cd from ¬(ab < cd) ∧ ¬(cd < ab)
        if (lit.polarity and isinstance(atom, Equals)
                and not isinstance(atom.left, str)):
            neg1 = Literal(LessThan(atom.left, atom.right), polarity=False)
            neg2 = Literal(LessThan(atom.right, atom.left), polarity=False)
            if neg1 in self.known and neg2 in self.known:
                return "< trichotomy"
            if me.is_consequence(self.known, lit):
                return "< trichotomy"

        return None

    # ══════════════════════════════════════════════════════════════════
    # Angle transfer elaboration tactic
    # ══════════════════════════════════════════════════════════════════

    def _elaborate_angle_transfer(
        self, lid: int, depth: int,
        targets: List[Literal], refs: List[int], stmt: str,
    ) -> Optional[List[dict]]:
        """Elaborate an 'Angle transfer N' step.

        The core issue: DA4 (same-ray angle equality) requires both
        angle arms to be on named lines through the vertex.  When
        the proof says "∠bae = ∠cae" but the SSS result gives
        "∠dae = ∠fae", we need:
          1. Derive missing point disequalities via M1
          2. Construct intermediate line if needed
          3. Apply DA4 for each arm substitution
          4. Chain via CN1 transitivity

        If the target is directly derivable by the transfer engine,
        emit it with the original justification.  Otherwise, emit
        the multi-step chain.
        """
        # First: compute diagrammatic closure + metric expansion
        # (mirrors what the strict checker does for transfer steps)
        closure = self.consequence_engine.direct_consequences(
            self.known, self.variables)
        augmented = self.known | closure

        diagram_known = {l for l in augmented if l.is_diagrammatic}
        metric_known = {l for l in augmented if l.is_metric}

        # Run the transfer engine with metric expansion
        derived = self.transfer_engine.apply_transfers(
            diagram_known, metric_known, self.variables)

        # Check if target is directly derivable
        all_targets_ok = all(
            t in self.known or t in derived for t in targets)
        if all_targets_ok:
            # Already derivable — no elaboration needed
            return None

        # Target not directly derivable.  Try the DA4 multi-hop approach.
        elaborated = self._try_da4_chain(
            lid, depth, targets, refs, augmented, derived)
        if elaborated is not None:
            return elaborated

        # Can't elaborate — return None to let strict checker report error
        return None

    def _try_da4_chain(
        self, lid: int, depth: int,
        targets: List[Literal], refs: List[int],
        augmented: Set[Literal], derived: Set[Literal],
    ) -> Optional[List[dict]]:
        """Try to derive angle equality via DA4 same-ray chain.

        If ∠bae = ∠cae is needed and ∠dae = ∠fae is known, where
        b/f are on the same ray (same line, not between) and c/d are
        on the same ray, emit:
          1. M1 disequality steps (if needed)
          2. DA4: ∠bae = ∠fae  (replacing f→b on their shared line)
          3. DA4: ∠dae = ∠cae  (replacing d→c on their shared line)
          4. CN1: ∠bae = ∠fae = ∠dae = ∠cae
        """
        for target in targets:
            if not (target.polarity and isinstance(target.atom, Equals)
                    and isinstance(target.atom.left, AngleTerm)
                    and isinstance(target.atom.right, AngleTerm)):
                continue

            want_l: AngleTerm = target.atom.left
            want_r: AngleTerm = target.atom.right

            # Check vertex is the same
            if want_l.p2 != want_r.p2:
                continue
            vertex = want_l.p2

            # Search for a known angle equality with the same vertex
            # that can bridge via DA4 substitutions
            for known_lit in self.known | derived:
                if not (known_lit.polarity
                        and isinstance(known_lit.atom, Equals)
                        and isinstance(known_lit.atom.left, AngleTerm)
                        and isinstance(known_lit.atom.right, AngleTerm)):
                    continue

                have_l: AngleTerm = known_lit.atom.left
                have_r: AngleTerm = known_lit.atom.right
                if have_l.p2 != vertex or have_r.p2 != vertex:
                    continue

                # Check if we can DA4-substitute:
                # want ∠(b, vertex, e) = ∠(c, vertex, e)
                # have ∠(f, vertex, e) = ∠(d, vertex, e)
                # Need: b,f on same ray from vertex; c,d on same ray
                chain = self._build_da4_substitution_chain(
                    lid, depth, refs,
                    want_l, want_r, have_l, have_r,
                    vertex, augmented, known_lit)
                if chain is not None:
                    return chain

        return None

    def _build_da4_substitution_chain(
        self, lid: int, depth: int, refs: List[int],
        want_l: AngleTerm, want_r: AngleTerm,
        have_l: AngleTerm, have_r: AngleTerm,
        vertex: str, augmented: Set[Literal],
        known_eq: Literal,
    ) -> Optional[List[dict]]:
        """Build the DA4 substitution chain for angle equality."""
        steps: List[dict] = []

        # want: ∠(w1, v, w3) = ∠(w1', v, w3')
        # have: ∠(h1, v, h3) = ∠(h1', v, h3')
        w1, w3 = want_l.p1, want_l.p3
        w1p, w3p = want_r.p1, want_r.p3
        h1, h3 = have_l.p1, have_l.p3
        h1p, h3p = have_r.p1, have_r.p3

        # Check same-ray conditions for left arm: w1 and h1 on same ray
        # and right arm: w3 and h3 on same point or same ray
        # Also check cross: maybe w1↔h1' and w1'↔h1 (arms swapped)

        # Strategy: try both orientations of the known equality
        for kl, kr in [(have_l, have_r), (have_r, have_l)]:
            kl1, kl3 = kl.p1, kl.p3
            kr1, kr3 = kr.p1, kr.p3

            left_ok = (w1 == kl1) or self._same_ray(vertex, w1, kl1, augmented)
            right_ok = (w3 == kl3) or self._same_ray(vertex, w3, kl3, augmented)
            left_ok2 = (w1p == kr1) or self._same_ray(vertex, w1p, kr1, augmented)
            right_ok2 = (w3p == kr3) or self._same_ray(vertex, w3p, kr3, augmented)

            if left_ok and right_ok and left_ok2 and right_ok2:
                # Build the chain
                # Step 1: needed disequalities
                diseq_steps = self._emit_needed_diseq(
                    depth, vertex, [w1, w3, w1p, w3p, kl1, kl3, kr1, kr3])
                steps.extend(diseq_steps)

                # Step 2: DA4 for left arm substitution (if needed)
                if w1 != kl1 or w3 != kl3:
                    intermediate = AngleTerm(w1, vertex, w3)
                    have_side = AngleTerm(kl1, vertex, kl3)
                    da4_step = {
                        "id": self._fresh_id(),
                        "depth": depth,
                        "statement": f"∠{w1}{vertex}{w3} = ∠{kl1}{vertex}{kl3}",
                        "justification": "Angle transfer 4",
                        "refs": refs,
                    }
                    steps.append(da4_step)

                if w1p != kr1 or w3p != kr3:
                    da4_step2 = {
                        "id": self._fresh_id(),
                        "depth": depth,
                        "statement": f"∠{kr1}{vertex}{kr3} = ∠{w1p}{vertex}{w3p}",
                        "justification": "Angle transfer 4",
                        "refs": refs,
                    }
                    steps.append(da4_step2)

                # Final step: the target equality with CN1 transitivity
                final_step = {
                    "id": lid,
                    "depth": depth,
                    "statement": str(targets[0]) if len(targets) == 1 else stmt,
                    "justification": "CN1 — Transitivity",
                    "refs": refs + [s["id"] for s in steps],
                }
                steps.append(final_step)
                return steps

        return None

    def _same_ray(
        self, vertex: str, p1: str, p2: str, known: Set[Literal]
    ) -> bool:
        """Check if p1 and p2 are on the same ray from vertex.

        Same ray means: on the same line through vertex, and
        ¬between(vertex, p1, p2) — i.e., neither is between vertex
        and the other (they're on the same side of vertex).
        """
        if p1 == p2:
            return True

        # Find a common line through vertex, p1, p2
        for lit in known:
            if not lit.polarity or not isinstance(lit.atom, On):
                continue
            if lit.atom.point != vertex:
                continue
            line = lit.atom.obj
            # Check p1 and p2 are also on this line
            on_p1 = Literal(On(p1, line), polarity=True) in known
            on_p2 = Literal(On(p2, line), polarity=True) in known
            if on_p1 and on_p2:
                # Check ¬between(vertex, p1, p2) and ¬between(vertex, p2, p1)
                nb1 = Literal(Between(vertex, p1, p2), polarity=False) in known
                nb2 = Literal(Between(vertex, p2, p1), polarity=False) in known
                if nb1 or nb2:
                    return True
                # Also check the other direction: ¬between(p1, vertex, p2)
                # which would mean they're on opposite sides
                opp = Literal(Between(p1, vertex, p2), polarity=False) in known
                # Actually for same ray we need them NOT separated by vertex
                # ¬between(vertex, p1, p2) means p2 is not between vertex and... 
                # no. between(vertex, p1, p2) means p1 is between vertex and p2.
                # For same ray: we need ¬between(p1, vertex, p2) — vertex is NOT
                # between them. This comes from the diagrammatic closure.
                # Also: between(vertex, p1, p2) or between(vertex, p2, p1) both
                # mean same ray (one is further than the other).
                # So actually same ray = on same line AND 
                #   (between(vertex, p1, p2) OR between(vertex, p2, p1) OR
                #    ¬between(p1, vertex, p2))
                bet1 = Literal(Between(vertex, p1, p2), polarity=True) in known
                bet2 = Literal(Between(vertex, p2, p1), polarity=True) in known
                if bet1 or bet2:
                    return True

        return False

    def _emit_needed_diseq(
        self, depth: int, vertex: str, points: List[str]
    ) -> List[dict]:
        """Emit M1 disequality steps for point≠vertex facts not yet known."""
        steps = []
        me = MetricEngine()
        me.process_literals(self.known)

        seen = set()
        for p in points:
            if p == vertex:
                continue
            pair = frozenset({p, vertex})
            if pair in seen:
                continue
            seen.add(pair)
            diseq = Literal(Equals(p, vertex), polarity=False)
            diseq2 = Literal(Equals(vertex, p), polarity=False)
            if diseq not in self.known and diseq2 not in self.known:
                # Check if derivable
                if me._check_literal(diseq) or me._check_literal(diseq2):
                    steps.append({
                        "id": self._fresh_id(),
                        "depth": depth,
                        "statement": f"¬({vertex} = {p})"
                                     if vertex < p
                                     else f"¬({p} = {vertex})",
                        "justification": "M1 — Zero segment",
                        "refs": [],
                    })
        return steps

    # ══════════════════════════════════════════════════════════════════
    # Area transfer elaboration tactic
    # ══════════════════════════════════════════════════════════════════

    def _elaborate_area_transfer(
        self, lid: int, depth: int,
        targets: List[Literal], refs: List[int], stmt: str,
    ) -> Optional[List[dict]]:
        """Elaborate an 'Area transfer N' step.

        Similar to angle transfer: compute closure, run transfer engine,
        check derivability.
        """
        closure = self.consequence_engine.direct_consequences(
            self.known, self.variables)
        augmented = self.known | closure

        diagram_known = {l for l in augmented if l.is_diagrammatic}
        metric_known = {l for l in augmented if l.is_metric}
        derived = self.transfer_engine.apply_transfers(
            diagram_known, metric_known, self.variables)

        all_ok = all(t in self.known or t in derived for t in targets)
        if all_ok:
            return None  # Already derivable

        return None  # Can't elaborate

    # ══════════════════════════════════════════════════════════════════
    # Theorem elaboration tactic
    # ══════════════════════════════════════════════════════════════════

    def _elaborate_theorem(
        self, lid: int, depth: int,
        targets: List[Literal], refs: List[int], stmt: str,
        just: str,
    ) -> Optional[List[dict]]:
        """Elaborate a theorem application by pre-deriving missing hypotheses.

        When the strict checker rejects a theorem application because
        a hypothesis isn't met (e.g. same-side(b,a,M) not in known),
        the elaborator tries to derive the missing fact and emits it
        as an explicit step before the theorem application.
        """
        from .e_library import E_THEOREM_LIBRARY, get_theorems_up_to

        thm = E_THEOREM_LIBRARY.get(just)
        if thm is None:
            return None

        # Derive variable mapping (same logic as unified_checker)
        from .unified_checker import _match_theorem_var_map
        var_map = _match_theorem_var_map(thm, targets, known=self.known)

        # Check each hypothesis
        missing_hyps: List[Literal] = []
        for hyp in thm.sequent.hypotheses:
            inst = substitute_literal(hyp, var_map)
            if inst in self.known:
                continue
            # Try consequence engines
            if inst.is_diagrammatic:
                ok = self.consequence_engine.is_consequence(
                    self.known, inst)
            elif inst.is_metric:
                me = MetricEngine()
                ok = me.is_consequence(self.known, inst)
            else:
                ok = False
            if not ok:
                missing_hyps.append(inst)

        if not missing_hyps:
            return None  # All hypotheses met

        # Try to derive missing hypotheses
        pre_steps: List[dict] = []
        for missing in missing_hyps:
            derived_step = self._try_derive_hypothesis(missing, depth)
            if derived_step is None:
                return None  # Can't derive; let strict checker report
            pre_steps.append(derived_step)

        # Emit: pre-derivation steps + original theorem application
        pre_refs = [s["id"] for s in pre_steps]
        thm_step = {
            "id": lid,
            "depth": depth,
            "statement": stmt,
            "justification": just,
            "refs": refs + pre_refs,
        }
        return pre_steps + [thm_step]

    def _try_derive_hypothesis(
        self, target: Literal, depth: int
    ) -> Optional[dict]:
        """Try to derive a missing theorem hypothesis as an explicit step."""

        # Point disequality via M1
        if (not target.polarity and isinstance(target.atom, Equals)
                and isinstance(target.atom.left, str)
                and isinstance(target.atom.right, str)):
            me = MetricEngine()
            if me.is_consequence(self.known, target):
                return {
                    "id": self._fresh_id(),
                    "depth": depth,
                    "statement": str(target),
                    "justification": "M1 — Zero segment",
                    "refs": [],
                }

        # Diagrammatic fact via consequence engine
        if target.is_diagrammatic:
            closure = self.consequence_engine.direct_consequences(
                self.known, self.variables)
            if target in closure:
                # Identify specific axiom
                just = self._identify_diag_rule(target, closure)
                return {
                    "id": self._fresh_id(),
                    "depth": depth,
                    "statement": str(target),
                    "justification": just,
                    "refs": [],
                }

        # Same-side facts
        if (target.polarity and isinstance(target.atom, SameSide)):
            # Try SS2 symmetry: same-side(a,b,L) from same-side(b,a,L)
            sym = Literal(SameSide(target.atom.b, target.atom.a,
                                   target.atom.line), polarity=True)
            if sym in self.known:
                return {
                    "id": self._fresh_id(),
                    "depth": depth,
                    "statement": str(target),
                    "justification": "Same-side 2",
                    "refs": [],
                }

        # Metric fact via metric engine
        if target.is_metric:
            me = MetricEngine()
            if me.is_consequence(self.known, target):
                return {
                    "id": self._fresh_id(),
                    "depth": depth,
                    "statement": str(target),
                    "justification": "Metric",
                    "refs": [],
                }

        return None

    def _identify_diag_rule(
        self, target: Literal, closure: Set[Literal]
    ) -> str:
        """Identify which diagrammatic axiom produced a literal."""
        atom = target.atom
        if isinstance(atom, On):
            return "Betweenness 6"  # most common for derived on-line facts
        elif isinstance(atom, Between):
            return "Betweenness 2"
        elif isinstance(atom, SameSide):
            return "Same-side 2"
        elif isinstance(atom, Intersects):
            return "Intersection 9"
        # Negated
        if not target.polarity:
            if isinstance(atom, Equals):
                return "Betweenness 2"
            if isinstance(atom, SameSide):
                return "Same-side 3"
            if isinstance(atom, On):
                return "Diagrammatic"
        return "Diagrammatic"

    # ══════════════════════════════════════════════════════════════════
    # Diagrammatic elaboration tactic
    # ══════════════════════════════════════════════════════════════════

    def _elaborate_diagrammatic(
        self, lid: int, depth: int,
        targets: List[Literal], refs: List[int], stmt: str,
    ) -> Optional[List[dict]]:
        """Elaborate a bare 'Diagrammatic' step.

        Runs the consequence engine and identifies specific axioms.
        """
        closure = self.consequence_engine.direct_consequences(
            self.known, self.variables)
        all_ok = all(t in self.known or t in closure for t in targets)
        if all_ok:
            return None  # Already derivable with current justification

        return None

    # ══════════════════════════════════════════════════════════════════
    # ⊥-intro elaboration tactic
    # ══════════════════════════════════════════════════════════════════

    def _elaborate_bot_intro(
        self, lid: int, depth: int,
        targets: List[Literal], refs: List[int], stmt: str,
    ) -> Optional[List[dict]]:
        """Elaborate ⊥-intro by ensuring the contradiction is visible.

        If the contradiction involves a metric fact (X = Y and X < Y)
        that's not directly in the ref lines but is derivable, emit
        the metric derivation steps first.
        """
        # Collect ref literals
        ref_lits: Set[Literal] = set()
        # We can't directly access line_lits here since we're in the
        # elaborator, not the checker.  Instead, we check self.known
        # for contradictions.

        # Check for direct contradiction in known
        for kf in self.known:
            if kf.negated() in self.known:
                return None  # Contradiction exists, no elaboration needed

        # Check for metric contradiction derivable from known
        me = MetricEngine()
        me.process_literals(self.known)

        metric_lits = [l for l in self.known if l.is_metric]
        for m1 in metric_lits:
            for m2 in metric_lits:
                if m1 == m2:
                    continue
                if (m1.polarity and m2.polarity
                        and isinstance(m1.atom, Equals)
                        and isinstance(m2.atom, LessThan)):
                    if (m1.atom.left == m2.atom.left
                            and m1.atom.right == m2.atom.right):
                        return None  # Already visible
                    # Check via metric engine symmetry
                    eq_sym = Literal(Equals(m2.atom.left, m2.atom.right))
                    if me._check_literal(eq_sym):
                        # The equality is derivable but in different form
                        steps = [{
                            "id": self._fresh_id(),
                            "depth": depth,
                            "statement": str(eq_sym),
                            "justification": "CN1 — Transitivity",
                            "refs": refs,
                        }]
                        steps.append({
                            "id": lid,
                            "depth": depth,
                            "statement": stmt,
                            "justification": "⊥-intro",
                            "refs": refs + [steps[0]["id"]],
                        })
                        return steps

        return None


# ═══════════════════════════════════════════════════════════════════════
# Public API
# ═══════════════════════════════════════════════════════════════════════

def elaborate_proof(proof_json: dict) -> ElaborationResult:
    """Elaborate a proof JSON, expanding high-level steps.

    This is the main entry point for the elaboration layer.
    """
    engine = ElaborationEngine()
    return engine.elaborate(proof_json)


# ═══════════════════════════════════════════════════════════════════════
# Sort inference helper (shared with unified_checker)
# ═══════════════════════════════════════════════════════════════════════

def _infer_sort(name: str, sort_ctx: Dict[str, Sort]) -> Sort:
    """Infer the sort of a variable from its name or context."""
    if name in sort_ctx:
        return sort_ctx[name]
    # Greek letters → circle
    if any(c in name for c in "αβγδεζηθικλμνξοπρστυφχψω"):
        return Sort.CIRCLE
    # Uppercase single letter → line (unless in point context)
    if len(name) == 1 and name.isupper():
        return Sort.LINE
    return Sort.POINT
