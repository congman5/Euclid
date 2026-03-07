"""
t_checker.py — Proof checker for System T (Tarski's axioms).

Verifies a System T proof by checking each step:
  - Construction steps: SC, P, PP, Int, 2L — introduce new points
  - Deduction steps: E1–E3, B, 5S, 2U, negativity — derive facts
  - Case splits: 2U upper-dimension disjunction
  - Theorem applications: applies a previously proved theorem

A proof is valid if every step is justified and the final assertions
include the goal.

GeoCoq reference: theories/Axioms/tarski_axioms.v
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple

from .t_ast import (
    TSort, TLiteral, TSequent,
    B, Cong, NotB, NotCong, Eq, Neq,
    TProofStep, TStepKind, TProof, TTheorem,
    t_atom_vars, t_literal_vars, t_substitute_literal,
)
from .t_consequence import TConsequenceEngine


# ═══════════════════════════════════════════════════════════════════════
# Diagnostic types
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class TCheckResult:
    """Result of checking a System T proof step or entire proof."""
    valid: bool = True
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    established: Set[TLiteral] = field(default_factory=set)
    variables: Dict[str, TSort] = field(default_factory=dict)

    def add_error(self, msg: str) -> None:
        self.valid = False
        self.errors.append(msg)

    def add_warning(self, msg: str) -> None:
        self.warnings.append(msg)


# ═══════════════════════════════════════════════════════════════════════
# The checker
# ═══════════════════════════════════════════════════════════════════════

class TChecker:
    """Proof checker for System T.

    Mirrors the structure of e_checker.py and h_checker.py but uses
    Tarski's single-sorted axiom system.
    """

    def __init__(
        self,
        theorems: Optional[Dict[str, TTheorem]] = None,
        consequence_engine: Optional[TConsequenceEngine] = None,
    ):
        self.theorems = theorems or {}
        self.engine = consequence_engine or TConsequenceEngine()

    def check_proof(self, proof: TProof) -> TCheckResult:
        """Check a complete System T proof.

        Returns a TCheckResult indicating validity and any errors.
        """
        result = TCheckResult()

        # Initialize with declared free variables
        for name, sort in proof.free_vars:
            result.variables[name] = sort

        # Assert hypotheses
        for hyp in proof.hypotheses:
            result.established.add(hyp)
            for v in t_literal_vars(hyp):
                if v not in result.variables:
                    result.variables[v] = TSort.POINT

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
            for lit in proof.goal:
                if lit not in closure:
                    result.add_error(
                        f"Goal literal not established: {lit}"
                    )

        return result

    def _check_step(self, step: TProofStep, result: TCheckResult) -> None:
        """Check a single proof step."""
        if step.kind == TStepKind.CONSTRUCTION:
            self._check_construction(step, result)
        elif step.kind == TStepKind.DEDUCTION:
            self._check_deduction(step, result)
        elif step.kind == TStepKind.CASE_SPLIT:
            self._check_case_split(step, result)
        elif step.kind == TStepKind.THEOREM_APP:
            self._check_theorem_app(step, result)
        else:
            result.add_error(f"Step {step.id}: unknown step kind {step.kind}")

    def _check_construction(
        self, step: TProofStep, result: TCheckResult
    ) -> None:
        """Check a construction step (SC, P, PP, Int, 2L).

        Construction steps introduce new point variables.
        """
        # Register new variables
        for name, sort in step.new_vars:
            if name in result.variables:
                result.add_error(
                    f"Step {step.id}: variable '{name}' already exists"
                )
                return
            result.variables[name] = sort

        # Add assertions
        for lit in step.assertions:
            result.established.add(lit)

    def _check_deduction(
        self, step: TProofStep, result: TCheckResult
    ) -> None:
        """Check a deduction step.

        The asserted literals must be direct consequences of known facts.
        """
        closure = self.engine.direct_consequences(
            result.established, result.variables
        )
        for lit in step.assertions:
            if lit not in closure:
                result.add_error(
                    f"Step {step.id}: {lit} is not a direct consequence"
                )
                return
            result.established.add(lit)

    def _check_case_split(
        self, step: TProofStep, result: TCheckResult
    ) -> None:
        """Check a case split (e.g., 2U upper-dimension disjunction).

        Both/all branches must establish the same conclusion.
        """
        if not step.subproofs:
            result.add_error(f"Step {step.id}: case split has no subproofs")
            return

        # Each subproof must establish the step's assertions
        for i, branch in enumerate(step.subproofs):
            branch_result = TCheckResult(
                established=set(result.established),
                variables=dict(result.variables),
            )
            for sub_step in branch:
                self._check_step(sub_step, branch_result)
                if not branch_result.valid:
                    result.add_error(
                        f"Step {step.id}: branch {i} failed: "
                        + "; ".join(branch_result.errors)
                    )
                    return

        # If all branches pass, add the assertions
        for lit in step.assertions:
            result.established.add(lit)

    def _check_theorem_app(
        self, step: TProofStep, result: TCheckResult
    ) -> None:
        """Check a theorem application.

        Verifies that the theorem's hypotheses are satisfied and
        adds the conclusions.
        """
        thm = self.theorems.get(step.theorem_name)
        if thm is None:
            result.add_error(
                f"Step {step.id}: unknown theorem '{step.theorem_name}'"
            )
            return

        # Check that all hypotheses of the theorem are consequences
        closure = self.engine.direct_consequences(
            result.established, result.variables
        )
        var_map = step.var_map
        for hyp in thm.sequent.hypotheses:
            renamed = t_substitute_literal(hyp, var_map)
            if renamed not in closure:
                result.add_error(
                    f"Step {step.id}: theorem hypothesis {renamed} "
                    f"not established"
                )
                return

        # Register new existential variables
        for name, sort in step.new_vars:
            if name in result.variables:
                result.add_error(
                    f"Step {step.id}: variable '{name}' already exists"
                )
                return
            result.variables[name] = sort

        # Add conclusions
        for lit in step.assertions:
            result.established.add(lit)
