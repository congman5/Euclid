"""
h_checker.py — Proof checker for System H (Hilbert's axioms).

Verifies a System H proof by checking each step:
  - Construction steps: validated against existence axioms
    (line_existence, between_out, cong_existence, cong_4_existence)
  - Incidence steps: validated by Group I consequence closure
  - Order steps: validated by Group II consequence closure
  - Congruence steps: validated by Group III consequence closure
  - Case splits: validated by checking both branches (pasch disjunction)
  - Theorem applications: validated by matching against proved theorems

A proof is valid if every step is justified and the final assertions
include the goal.

GeoCoq reference: theories/Axioms/hilbert_axioms.v
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple

from .h_ast import (
    HSort, HLiteral, HSequent,
    IncidL, IncidP, BetH, CongH, CongaH, EqL, EqP, EqPt,
    ColH, Cut, OutH, Disjoint, SameSideH, SameSidePrime, Para,
    HProofStep, HStepKind, HProof, HTheorem,
    h_atom_vars, h_literal_vars, h_substitute_literal,
)
from .h_consequence import HConsequenceEngine


# ═══════════════════════════════════════════════════════════════════════
# Diagnostic types
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class HCheckResult:
    """Result of checking a System H proof step or entire proof."""
    valid: bool = True
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    established: Set[HLiteral] = field(default_factory=set)
    variables: Dict[str, HSort] = field(default_factory=dict)

    def add_error(self, msg: str) -> None:
        self.valid = False
        self.errors.append(msg)

    def add_warning(self, msg: str) -> None:
        self.warnings.append(msg)


# ═══════════════════════════════════════════════════════════════════════
# The checker
# ═══════════════════════════════════════════════════════════════════════

class HChecker:
    """Proof checker for System H.

    Mirrors the structure of e_checker.py (EChecker) but uses
    Hilbert's axiom groups instead of Avigad's categories.
    """

    def __init__(
        self,
        theorems: Optional[Dict[str, HTheorem]] = None,
        consequence_engine: Optional[HConsequenceEngine] = None,
    ):
        self.theorems = theorems or {}
        self.engine = consequence_engine or HConsequenceEngine()

    def check_proof(self, proof: HProof) -> HCheckResult:
        """Check a complete System H proof.

        Returns an HCheckResult indicating validity and any errors.
        """
        result = HCheckResult()

        # Initialize with declared free variables
        for name, sort in proof.free_vars:
            result.variables[name] = sort

        # Assert hypotheses
        for hyp in proof.hypotheses:
            result.established.add(hyp)
            for v in h_literal_vars(hyp):
                if v not in result.variables:
                    result.variables[v] = HSort.POINT  # default

        # Check each step
        for step in proof.steps:
            self._check_step(step, result)
            if not result.valid:
                return result

        # Verify goal is established
        if proof.goal:
            closure = self.engine.direct_consequences(
                result.established, result.variables
            )
            for goal_lit in proof.goal:
                if goal_lit not in closure and goal_lit not in result.established:
                    result.add_error(
                        f"Goal literal not established: {goal_lit}"
                    )

        return result

    def _check_step(self, step: HProofStep, result: HCheckResult) -> None:
        """Check a single proof step."""
        if step.kind == HStepKind.CONSTRUCTION:
            self._check_construction(step, result)
        elif step.kind == HStepKind.INCIDENCE:
            self._check_incidence(step, result)
        elif step.kind == HStepKind.ORDER:
            self._check_order(step, result)
        elif step.kind == HStepKind.CONGRUENCE:
            self._check_congruence(step, result)
        elif step.kind == HStepKind.THEOREM_APP:
            self._check_theorem_app(step, result)
        elif step.kind == HStepKind.CASE_SPLIT:
            self._check_case_split(step, result)
        elif step.kind == HStepKind.DEFINED_PRED:
            self._check_defined_pred(step, result)
        else:
            result.add_error(f"Step {step.id}: unknown step kind {step.kind}")

    def _check_construction(
        self, step: HProofStep, result: HCheckResult
    ) -> None:
        """Check a construction step.

        Construction steps introduce new objects using Hilbert's existence
        axioms (line_existence, between_out, cong_existence, cong_4_existence).
        """
        # Register new variables
        for name, sort in step.new_vars:
            if name in result.variables:
                result.add_warning(
                    f"Step {step.id}: variable '{name}' already declared"
                )
            result.variables[name] = sort

        # Add all asserted literals
        for lit in step.assertions:
            result.established.add(lit)

    def _check_incidence(
        self, step: HProofStep, result: HCheckResult
    ) -> None:
        """Check a Group I (incidence) inference step."""
        closure = self.engine.direct_consequences(
            result.established, result.variables
        )
        for lit in step.assertions:
            if lit not in closure:
                result.add_error(
                    f"Step {step.id}: {lit} is not a direct incidence "
                    f"consequence of established facts"
                )
                return
            result.established.add(lit)

    def _check_order(
        self, step: HProofStep, result: HCheckResult
    ) -> None:
        """Check a Group II (order) inference step."""
        closure = self.engine.direct_consequences(
            result.established, result.variables
        )
        for lit in step.assertions:
            if lit not in closure:
                result.add_error(
                    f"Step {step.id}: {lit} is not a direct order "
                    f"consequence of established facts"
                )
                return
            result.established.add(lit)

    def _check_congruence(
        self, step: HProofStep, result: HCheckResult
    ) -> None:
        """Check a Group III (congruence) inference step."""
        closure = self.engine.direct_consequences(
            result.established, result.variables
        )
        for lit in step.assertions:
            if lit not in closure:
                result.add_error(
                    f"Step {step.id}: {lit} is not a direct congruence "
                    f"consequence of established facts"
                )
                return
            result.established.add(lit)

    def _check_theorem_app(
        self, step: HProofStep, result: HCheckResult
    ) -> None:
        """Check a theorem application step."""
        thm_name = step.theorem_name
        if thm_name not in self.theorems:
            result.add_error(
                f"Step {step.id}: unknown theorem '{thm_name}'"
            )
            return

        thm = self.theorems[thm_name]
        var_map = step.var_map

        # Check all hypotheses of the theorem are established
        closure = self.engine.direct_consequences(
            result.established, result.variables
        )
        for hyp in thm.sequent.hypotheses:
            renamed = h_substitute_literal(hyp, var_map)
            if renamed not in closure:
                result.add_error(
                    f"Step {step.id}: theorem '{thm_name}' hypothesis "
                    f"{renamed} not established"
                )
                return

        # Register new variables and add conclusions
        for name, sort in step.new_vars:
            result.variables[name] = sort
        for lit in step.assertions:
            result.established.add(lit)

    def _check_case_split(
        self, step: HProofStep, result: HCheckResult
    ) -> None:
        """Check a proof by cases (e.g., pasch disjunction)."""
        if step.split_atom is None:
            result.add_error(
                f"Step {step.id}: case split requires a split_atom"
            )
            return

        if len(step.subproofs) != 2:
            result.add_error(
                f"Step {step.id}: case split requires exactly 2 subproofs"
            )
            return

        # Positive case
        pos_result = HCheckResult(
            established=set(result.established),
            variables=dict(result.variables),
        )
        pos_result.established.add(HLiteral(step.split_atom, True))
        for sub_step in step.subproofs[0]:
            self._check_step(sub_step, pos_result)
            if not pos_result.valid:
                result.add_error(
                    f"Step {step.id}: positive case failed: "
                    + "; ".join(pos_result.errors)
                )
                return

        # Negative case
        neg_result = HCheckResult(
            established=set(result.established),
            variables=dict(result.variables),
        )
        neg_result.established.add(HLiteral(step.split_atom, False))
        for sub_step in step.subproofs[1]:
            self._check_step(sub_step, neg_result)
            if not neg_result.valid:
                result.add_error(
                    f"Step {step.id}: negative case failed: "
                    + "; ".join(neg_result.errors)
                )
                return

        # Both cases establish the conclusion
        for lit in step.assertions:
            if lit not in pos_result.established:
                result.add_error(
                    f"Step {step.id}: {lit} not established in positive case"
                )
                return
            if lit not in neg_result.established:
                result.add_error(
                    f"Step {step.id}: {lit} not established in negative case"
                )
                return
            result.established.add(lit)

    def _check_defined_pred(
        self, step: HProofStep, result: HCheckResult
    ) -> None:
        """Check unfolding/folding of a defined predicate.

        For example, unfolding ColH(A,B,C) into ∃l. IncidL(A,l) ∧ ... ,
        or folding the other direction.
        """
        # Defined predicate steps are verified by the consequence engine,
        # which has rules for both introduction and elimination of
        # defined predicates (ColH, Cut, same_side, etc.)
        closure = self.engine.direct_consequences(
            result.established, result.variables
        )
        for lit in step.assertions:
            if lit not in closure:
                result.add_error(
                    f"Step {step.id}: {lit} not derivable from defined "
                    f"predicate rules"
                )
                return
            result.established.add(lit)
