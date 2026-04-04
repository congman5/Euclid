"""
lean_translator.py — Core engine for translating LeanEuclid proofs to System E.

Takes parsed LeanProof objects and produces:
  - Lists of ProofStep objects matching e_proofs.py conventions
  - EProof objects ready for the checker
  - Translation reports showing the mapping for each step

This is the heart of the translator tool described in Track B of euclid-plan.md.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

from .lean_parser import (
    LeanProof, LeanTactic, LeanTheoremSig, LeanParam,
    TacticKind, LeanExpr, parse_lean_expr, parse_lean_file,
    extract_prop_number, prop_system_e_name,
)
from .lean_mapping import (
    RuleCategory, RuleMapping, lookup_rule, classify_rule,
    category_to_step_kind_name, PROP_DEPS, map_sort,
    ALL_RULES, CONSTRUCTION_RULES, PROPOSITION_RULES,
)
from .e_ast import (
    Sort, Literal, Sequent,
    On, SameSide, Between, Center, Inside, Intersects,
    Equals, LessThan,
    SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag,
    ProofStep, StepKind, EProof,
    literal_vars,
)


# ═══════════════════════════════════════════════════════════════════════
# Translation result types
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class TranslatedStep:
    """A single translated proof step with provenance."""
    step: ProofStep
    source_tactics: List[LeanTactic] = field(default_factory=list)
    notes: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)


@dataclass
class TranslationResult:
    """Complete result of translating a LeanEuclid proof."""
    prop_number: int
    prop_name: str                   # e.g. "Prop.I.16"
    lean_theorem: str                # e.g. "proposition_16"
    steps: List[TranslatedStep] = field(default_factory=list)
    eproof: Optional[EProof] = None
    warnings: List[str] = field(default_factory=list)
    stats: Dict[str, int] = field(default_factory=dict)

    @property
    def success(self) -> bool:
        return self.eproof is not None and len(self.steps) > 0


@dataclass
class TranslationReport:
    """Report for translating multiple propositions."""
    results: List[TranslationResult] = field(default_factory=list)
    total_lean_tactics: int = 0
    total_system_e_steps: int = 0
    total_warnings: int = 0

    def summary(self) -> str:
        lines = ["=" * 60, "Lean→System E Translation Report", "=" * 60]
        for r in self.results:
            status = "✓" if r.success else "✗"
            lines.append(
                f"  {status} {r.prop_name}: {len(r.steps)} steps, "
                f"{len(r.warnings)} warnings"
            )
        lines.append("-" * 60)
        lines.append(
            f"Total: {len(self.results)} propositions, "
            f"{self.total_system_e_steps} steps, "
            f"{self.total_warnings} warnings"
        )
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════
# Helper: build AST objects from parsed Lean expressions
# ═══════════════════════════════════════════════════════════════════════

def _pos(atom) -> Literal:
    return Literal(atom, polarity=True)


def _neg(atom) -> Literal:
    return Literal(atom, polarity=False)


def lean_expr_to_literals(expr: LeanExpr) -> List[Literal]:
    """Convert a parsed LeanExpr into System E Literal(s)."""
    if expr.kind == "eq":
        left_term = _expr_to_term(expr.children[0])
        right_term = _expr_to_term(expr.children[1])
        if left_term is not None and right_term is not None:
            return [_pos(Equals(left_term, right_term))]

    if expr.kind == "gt":
        left_term = _expr_to_term(expr.children[0])
        right_term = _expr_to_term(expr.children[1])
        if left_term is not None and right_term is not None:
            return [_pos(LessThan(right_term, left_term))]

    if expr.kind == "lt":
        left_term = _expr_to_term(expr.children[0])
        right_term = _expr_to_term(expr.children[1])
        if left_term is not None and right_term is not None:
            return [_pos(LessThan(left_term, right_term))]

    if expr.kind == "neg":
        inner_lits = lean_expr_to_literals(expr.children[0])
        return [lit.negated() for lit in inner_lits]

    if expr.kind == "on_line":
        return [_pos(On(expr.points[0], expr.value))]

    if expr.kind == "same_side":
        return [_pos(SameSide(expr.points[0], expr.points[1], expr.value))]

    return []


def _expr_to_term(expr: LeanExpr):
    """Convert a LeanExpr to a System E term (segment, angle, area, etc.)."""
    if expr.kind == "segment":
        return SegmentTerm(expr.points[0], expr.points[1])
    if expr.kind == "angle":
        return AngleTerm(expr.points[0], expr.points[1], expr.points[2])
    if expr.kind == "area":
        return AreaTerm(expr.points[0], expr.points[1], expr.points[2])
    if expr.kind == "right_angle":
        return RightAngle()
    if expr.kind == "add":
        left = _expr_to_term(expr.children[0])
        right = _expr_to_term(expr.children[1])
        if left is not None and right is not None:
            return MagAdd(left, right)
    if expr.kind == "zero":
        return ZeroMag(Sort.SEGMENT)
    if expr.kind == "var":
        return expr.value  # raw variable name (for point equality)
    if expr.kind == "mul":
        # For area expressions like |a|*|a|, simplify
        left = _expr_to_term(expr.children[0])
        right = _expr_to_term(expr.children[1])
        if left is not None and right is not None:
            return MagAdd(left, right)  # approximate: treat mul as add for areas
    return None


# ═══════════════════════════════════════════════════════════════════════
# Core translator: LeanProof → list of ProofSteps
# ═══════════════════════════════════════════════════════════════════════

_SORT_MAP = {
    "Point": Sort.POINT,
    "Line": Sort.LINE,
    "Circle": Sort.CIRCLE,
}


class LeanToSystemETranslator:
    """Translates a single LeanEuclid proof into System E ProofSteps."""

    def __init__(self, lean_proof: LeanProof):
        self.lean_proof = lean_proof
        self.prop_num = extract_prop_number(lean_proof.theorem_name)
        self.prop_name = prop_system_e_name(self.prop_num) if self.prop_num else ""
        self.steps: List[TranslatedStep] = []
        self.warnings: List[str] = []
        self.step_id = 0
        self._known_vars: Set[str] = set()
        self._var_sorts: Dict[str, Sort] = {}

    def translate(self) -> TranslationResult:
        """Run the full translation."""
        result = TranslationResult(
            prop_number=self.prop_num or 0,
            prop_name=self.prop_name,
            lean_theorem=self.lean_proof.theorem_name,
        )

        # Initialize known variables from theorem parameters
        if self.lean_proof.signature:
            for param in self.lean_proof.signature.params:
                self._known_vars.add(param.name)
                sort = _SORT_MAP.get(param.sort, Sort.POINT)
                self._var_sorts[param.name] = sort

        # Translate each tactic
        for tactic in self.lean_proof.tactics:
            translated = self._translate_tactic(tactic)
            if translated:
                self.steps.extend(translated)

        result.steps = self.steps
        result.warnings = self.warnings
        result.stats = {
            "lean_tactics": len(self.lean_proof.tactics),
            "system_e_steps": len(self.steps),
            "constructions": sum(1 for s in self.steps
                                 if s.step.kind == StepKind.CONSTRUCTION),
            "theorem_apps": sum(1 for s in self.steps
                                if s.step.kind == StepKind.THEOREM_APP),
            "metric_steps": sum(1 for s in self.steps
                                if s.step.kind in (StepKind.METRIC,
                                                    StepKind.DIAGRAMMATIC,
                                                    StepKind.TRANSFER)),
        }

        # Build EProof
        result.eproof = self._build_eproof()
        return result

    def _next_id(self) -> int:
        self.step_id += 1
        return self.step_id

    def _translate_tactic(self, tactic: LeanTactic) -> List[TranslatedStep]:
        """Translate a single LeanTactic into zero or more TranslatedSteps."""
        if tactic.kind == TacticKind.EUCLID_INTROS:
            return []  # No System E equivalent

        if tactic.kind == TacticKind.COMMENT:
            return []  # Skip comments

        if tactic.kind == TacticKind.CONSTRUCTOR:
            return []  # Lean-specific, no System E equivalent

        if tactic.kind == TacticKind.CASE_BRANCH:
            return []  # Case branch markers don't produce steps

        if tactic.kind == TacticKind.USE:
            return []  # 'use' is Lean's existential witness — handled via constructions

        if tactic.kind == TacticKind.SPLIT_ORS:
            return []  # Lean-specific

        if tactic.kind == TacticKind.EUCLID_APPLY:
            return self._translate_euclid_apply(tactic)

        if tactic.kind == TacticKind.EUCLID_ASSERT:
            return self._translate_euclid_assert(tactic)

        if tactic.kind == TacticKind.EUCLID_FINISH:
            return self._translate_euclid_finish(tactic)

        if tactic.kind == TacticKind.BY_CONTRA:
            return self._translate_by_contra(tactic)

        if tactic.kind == TacticKind.BY_CASES:
            return self._translate_by_cases(tactic)

        if tactic.kind == TacticKind.HAVE:
            return self._translate_have(tactic)

        return []

    def _translate_euclid_apply(self, tactic: LeanTactic) -> List[TranslatedStep]:
        """Translate euclid_apply into CONSTRUCTION, THEOREM_APP, or axiom step."""
        rule_name = tactic.rule_name
        mapping = lookup_rule(rule_name)
        category = classify_rule(rule_name)

        # Register bound variables
        new_vars = []
        for var in tactic.bound_vars:
            var_lower = var.lower()
            sort = self._infer_sort_from_context(var, tactic)
            new_vars.append((var_lower, sort))
            self._known_vars.add(var_lower)
            self._var_sorts[var_lower] = sort

        step_id = self._next_id()

        if category == RuleCategory.PROPOSITION:
            # Theorem application
            prop_num = extract_prop_number(rule_name)
            se_name = prop_system_e_name(prop_num) if prop_num else rule_name
            # Build var_map from positional arguments
            var_map = self._build_var_map(rule_name, tactic.rule_args)

            step = ProofStep(
                id=step_id,
                kind=StepKind.THEOREM_APP,
                description=f"{se_name} ({rule_name})",
                theorem_name=se_name,
                var_map=var_map,
                new_vars=new_vars,
                assertions=[],  # Will be filled by checker or post-processing
            )
            return [TranslatedStep(step=step, source_tactics=[tactic],
                                   notes=[f"Maps to {se_name}"])]

        if category in (RuleCategory.CONSTRUCTION, RuleCategory.EXTENSION_AXIOM,
                        RuleCategory.INTERSECTION, RuleCategory.SPECIAL):
            se_desc = mapping.system_e_name if mapping else rule_name
            assertions = self._infer_construction_assertions(
                rule_name, tactic.rule_args, tactic.bound_vars)

            step = ProofStep(
                id=step_id,
                kind=StepKind.CONSTRUCTION,
                description=se_desc,
                new_vars=new_vars,
                assertions=assertions,
                theorem_name=self.prop_name if self.prop_name else "",
            )
            return [TranslatedStep(step=step, source_tactics=[tactic],
                                   notes=[f"Construction: {se_desc}"])]

        if category in (RuleCategory.METRIC, RuleCategory.TRANSFER,
                        RuleCategory.DIAGRAMMATIC):
            kind_map = {
                RuleCategory.METRIC: StepKind.METRIC,
                RuleCategory.TRANSFER: StepKind.TRANSFER,
                RuleCategory.DIAGRAMMATIC: StepKind.DIAGRAMMATIC,
            }
            step = ProofStep(
                id=step_id,
                kind=kind_map[category],
                description=f"{rule_name} ({', '.join(tactic.rule_args)})",
                assertions=[],
                theorem_name=self.prop_name if self.prop_name else "",
            )
            return [TranslatedStep(step=step, source_tactics=[tactic],
                                   notes=[f"Inference: {rule_name}"])]

        # Fallback
        self.warnings.append(
            f"Unknown rule '{rule_name}' at line {tactic.line_number}")
        step = ProofStep(
            id=step_id,
            kind=StepKind.METRIC,
            description=f"[TODO] {rule_name} ({', '.join(tactic.rule_args)})",
            assertions=[],
            theorem_name=self.prop_name,
        )
        return [TranslatedStep(step=step, source_tactics=[tactic],
                               warnings=[f"Unknown rule: {rule_name}"])]

    def _translate_euclid_assert(self, tactic: LeanTactic) -> List[TranslatedStep]:
        """Translate euclid_assert into a METRIC assertion step."""
        expr = parse_lean_expr(tactic.assertion_expr)
        assertions = lean_expr_to_literals(expr) if expr else []

        step = ProofStep(
            id=self._next_id(),
            kind=StepKind.METRIC,
            description=f"assert: {tactic.assertion_expr}",
            assertions=assertions,
            theorem_name=self.prop_name,
        )
        return [TranslatedStep(step=step, source_tactics=[tactic],
                               notes=["Metric assertion"])]

    def _translate_euclid_finish(self, tactic: LeanTactic) -> List[TranslatedStep]:
        """Translate euclid_finish into a closure step.

        In LeanEuclid, euclid_finish dispatches to an SMT solver.
        In System E, this becomes an explicit METRIC/DIAGRAMMATIC step
        that the e_consequence engine must verify.
        """
        step = ProofStep(
            id=self._next_id(),
            kind=StepKind.METRIC,
            description="[euclid_finish] closure — verify via e_consequence",
            assertions=[],  # Conclusions filled from theorem sequent
            theorem_name=self.prop_name,
        )
        return [TranslatedStep(step=step, source_tactics=[tactic],
                               notes=["euclid_finish → explicit closure step"],
                               warnings=["euclid_finish needs manual assertion filling"])]

    def _translate_by_contra(self, tactic: LeanTactic) -> List[TranslatedStep]:
        """Translate by_contra into a note about contradiction proof structure."""
        step = ProofStep(
            id=self._next_id(),
            kind=StepKind.BOT_INTRO,
            description="[by_contra] assume negation for contradiction",
            assertions=[],
            theorem_name=self.prop_name,
        )
        return [TranslatedStep(step=step, source_tactics=[tactic],
                               notes=["Contradiction proof: assume negation"])]

    def _translate_by_cases(self, tactic: LeanTactic) -> List[TranslatedStep]:
        """Translate by_cases into a CASE_SPLIT step."""
        expr = parse_lean_expr(tactic.case_expr)
        assertions = lean_expr_to_literals(expr) if expr else []

        step = ProofStep(
            id=self._next_id(),
            kind=StepKind.CASE_SPLIT_ELIM,
            description=f"[by_cases] {tactic.case_expr}",
            assertions=[],
            theorem_name=self.prop_name,
        )
        return [TranslatedStep(step=step, source_tactics=[tactic],
                               notes=[f"Case split on: {tactic.case_expr}"])]

    def _translate_have(self, tactic: LeanTactic) -> List[TranslatedStep]:
        """Translate have into an intermediate assertion."""
        expr = parse_lean_expr(tactic.assertion_expr)
        assertions = lean_expr_to_literals(expr) if expr else []

        step = ProofStep(
            id=self._next_id(),
            kind=StepKind.METRIC,
            description=f"have: {tactic.assertion_expr}",
            assertions=assertions,
            theorem_name=self.prop_name,
        )
        return [TranslatedStep(step=step, source_tactics=[tactic],
                               notes=["Intermediate assertion"])]

    # ── Helpers ──────────────────────────────────────────────────────

    def _infer_sort_from_context(self, var_name: str, tactic: LeanTactic) -> Sort:
        """Infer the sort of a bound variable from naming conventions and context."""
        name_upper = var_name.upper()
        # Lines are typically uppercase or multi-char uppercase
        if len(var_name) >= 2 and var_name[0].isupper() and var_name[1].isupper():
            return Sort.LINE
        if var_name in ('L', 'M', 'N', 'P', 'Q', 'R', 'S', 'T'):
            return Sort.LINE
        # Check the rule for hints
        rule = tactic.rule_name
        if rule in ('line_from_points',):
            return Sort.LINE
        if rule in ('circle_from_points',):
            return Sort.CIRCLE
        # Greek letters → circles
        if any(c in var_name for c in ('α', 'β', 'γ', 'δ', 'epsilon')):
            return Sort.CIRCLE
        return Sort.POINT

    def _build_var_map(self, rule_name: str, args: List[str]) -> Dict[str, str]:
        """Build a var_map from rule arguments by mapping to theorem parameters."""
        var_map = {}
        for i, arg in enumerate(args):
            arg_lower = arg.lower()
            # Map the argument to its position-based parameter name
            # This is a heuristic — for proposition applications, the
            # parameters are typically the point/line names from the theorem
            var_map[arg_lower] = arg_lower
        return var_map

    def _infer_construction_assertions(
        self, rule_name: str, args: List[str], bound_vars: List[str]
    ) -> List[Literal]:
        """Infer assertions produced by a construction rule."""
        assertions = []

        if rule_name == "line_from_points" and len(args) >= 2:
            line_var = bound_vars[0].lower() if bound_vars else "L"
            a, b = args[0].lower(), args[1].lower()
            assertions.append(_pos(On(a, line_var)))
            assertions.append(_pos(On(b, line_var)))

        elif rule_name == "extend_point" and len(args) >= 2:
            # extend_point L a b → ∃ c. on(c, L) ∧ between(a, b, c)
            if bound_vars:
                new_pt = bound_vars[0].lower()
                line_arg = args[0].lower()
                a = args[1].lower()
                b = args[2].lower() if len(args) > 2 else a
                assertions.append(_pos(On(new_pt, line_arg)))
                assertions.append(_pos(Between(a, b, new_pt)))

        elif rule_name == "extend_point_longer" and len(args) >= 2:
            if bound_vars:
                new_pt = bound_vars[0].lower()
                line_arg = args[0].lower()
                a = args[1].lower()
                b = args[2].lower() if len(args) > 2 else a
                assertions.append(_pos(On(new_pt, line_arg)))
                assertions.append(_pos(Between(a, b, new_pt)))

        elif rule_name == "intersection_lines" and len(args) >= 2:
            if bound_vars:
                pt = bound_vars[0].lower()
                l1 = args[0].lower()
                l2 = args[1].lower()
                assertions.append(_pos(On(pt, l1)))
                assertions.append(_pos(On(pt, l2)))

        elif rule_name == "intersection_circles" and len(args) >= 2:
            if bound_vars:
                pt = bound_vars[0].lower()
                c1 = args[0].lower()
                c2 = args[1].lower()
                assertions.append(_pos(On(pt, c1)))
                assertions.append(_pos(On(pt, c2)))

        elif rule_name == "circle_from_points" and len(args) >= 2:
            if bound_vars:
                circle = bound_vars[0].lower()
                center = args[0].lower()
                on_pt = args[1].lower()
                assertions.append(_pos(Center(center, circle)))
                assertions.append(_pos(On(on_pt, circle)))

        return assertions

    def _build_eproof(self) -> Optional[EProof]:
        """Build an EProof from translated steps."""
        if not self.steps:
            return None

        proof_steps = [ts.step for ts in self.steps]

        # Infer free variables from parameters
        free_vars = []
        if self.lean_proof.signature:
            for param in self.lean_proof.signature.params:
                sort = _SORT_MAP.get(param.sort, Sort.POINT)
                free_vars.append((param.name.lower(), sort))

        return EProof(
            name=self.prop_name,
            free_vars=free_vars,
            hypotheses=[],   # Filled from library sequent
            exists_vars=[],  # Filled from library sequent
            goal=[],         # Filled from library sequent
            steps=proof_steps,
        )


# ═══════════════════════════════════════════════════════════════════════
# Batch translation: translate all propositions in a directory
# ═══════════════════════════════════════════════════════════════════════

def translate_lean_file(filepath: str) -> TranslationResult:
    """Translate a single LeanEuclid .lean file."""
    proofs = parse_lean_file(filepath)
    if not proofs:
        return TranslationResult(prop_number=0, prop_name="",
                                 lean_theorem="",
                                 warnings=["No theorems found in file"])

    # Translate the first (main) theorem
    translator = LeanToSystemETranslator(proofs[0])
    result = translator.translate()

    # Add variant info
    for variant in proofs[0].variants:
        vt = LeanToSystemETranslator(variant)
        vr = vt.translate()
        result.warnings.append(
            f"Variant {variant.theorem_name}: {len(vr.steps)} steps")

    return result


def translate_all_propositions(lean_dir: str,
                                prop_range: Tuple[int, int] = (1, 48)
                                ) -> TranslationReport:
    """Translate all propositions in a directory of .lean files."""
    report = TranslationReport()
    start, end = prop_range

    for n in range(start, end + 1):
        filepath = Path(lean_dir) / f"Prop{n}.lean"
        if not filepath.exists():
            filepath = Path(lean_dir) / f"Prop{n:02d}.lean"
        if not filepath.exists():
            report.results.append(TranslationResult(
                prop_number=n,
                prop_name=prop_system_e_name(n),
                lean_theorem=f"proposition_{n}",
                warnings=[f"File not found: {filepath}"],
            ))
            continue

        result = translate_lean_file(str(filepath))
        report.results.append(result)
        report.total_lean_tactics += result.stats.get("lean_tactics", 0)
        report.total_system_e_steps += result.stats.get("system_e_steps", 0)
        report.total_warnings += len(result.warnings)

    return report


# ═══════════════════════════════════════════════════════════════════════
# Utility: generate translation diff against existing e_proofs.py
# ═══════════════════════════════════════════════════════════════════════

def compare_with_existing(result: TranslationResult) -> Dict[str, Any]:
    """Compare a translation result with the existing proof in e_proofs.py."""
    try:
        from .e_proofs import get_proof
        existing = get_proof(result.prop_name)
    except (KeyError, ImportError):
        return {"status": "no_existing", "prop": result.prop_name}

    return {
        "status": "compared",
        "prop": result.prop_name,
        "existing_steps": len(existing.steps),
        "translated_steps": len(result.steps),
        "existing_kinds": [s.kind.name for s in existing.steps],
        "translated_kinds": [ts.step.kind.name for ts in result.steps],
    }
