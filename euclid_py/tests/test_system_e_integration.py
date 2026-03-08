"""
test_system_e_integration.py — Phase 9.5 integration tests.

Validates the full System E verification pipeline through the UI:
  • Smoke tests: all 48 propositions open without errors
  • UI interaction: add/remove steps, verify construction syntax
  • Integration: complete proof verified via E checker through UI
  • Negative: invalid proofs rejected with E-language diagnostics

Reference: IMPLEMENTATION_PLAN.md §9.5
"""
from __future__ import annotations

import pytest


# ═══════════════════════════════════════════════════════════════════════
# SMOKE TESTS — every proposition opens cleanly via E checker
# ═══════════════════════════════════════════════════════════════════════

class TestSmokeAllPropositions:
    """Open each proposition and verify no verifier errors appear."""

    def test_all_48_open_without_verifier_error(self):
        """Opening each of the 48 propositions must never show
        'Verifier error' in the detail bar."""
        from euclid_py.engine.proposition_data import PROPOSITIONS
        from euclid_py.ui.main_window import MainWindow

        w = MainWindow()
        pp = w._workspace._proof_panel

        errors = []
        for p in PROPOSITIONS:
            w.open_proposition(p)
            pp._eval_all()
            detail = pp._detail.text()
            if "Verifier error" in detail:
                errors.append(f"{p.name}: {detail[:80]}")

        assert errors == [], (
            f"{len(errors)} proposition(s) show verifier errors:\n"
            + "\n".join(errors)
        )

    def test_all_48_premises_are_system_e_syntax(self):
        """Premises for every proposition must not use old Hilbert syntax."""
        from euclid_py.engine.proposition_data import PROPOSITIONS
        from euclid_py.ui.main_window import MainWindow

        old_patterns = ["Point(", "Segment(", "Circle(", "OnLine(",
                        "Equal(", "Congruent(", "EqualAngle("]
        w = MainWindow()
        pp = w._workspace._proof_panel

        errors = []
        for p in PROPOSITIONS:
            w.open_proposition(p)
            for prem in pp._premises:
                for pat in old_patterns:
                    if pat in prem:
                        errors.append(f"{p.name} premise: {prem}")

        assert errors == [], (
            f"{len(errors)} old-syntax premise(s) found:\n"
            + "\n".join(errors)
        )

    def test_all_48_conclusions_are_system_e_syntax(self):
        """Conclusions for every proposition must not use old Hilbert syntax."""
        from euclid_py.engine.proposition_data import PROPOSITIONS
        from euclid_py.ui.main_window import MainWindow

        old_patterns = ["Triangle(", "Congruent(", "EqualAngle(",
                        "Parallel(", "Perpendicular("]
        w = MainWindow()
        pp = w._workspace._proof_panel

        errors = []
        for p in PROPOSITIONS:
            w.open_proposition(p)
            conc = pp._conclusion
            if conc:
                for pat in old_patterns:
                    if pat in conc:
                        errors.append(f"{p.name} goal: {conc[:60]}")

        assert errors == [], (
            f"{len(errors)} old-syntax conclusion(s) found:\n"
            + "\n".join(errors)
        )

    def test_all_48_have_e_library_entry(self):
        """Every Euclid proposition has an E library theorem."""
        from euclid_py.engine.proposition_data import PROPOSITIONS

        missing = []
        for p in PROPOSITIONS:
            if p.source == "euclid" and p.get_e_theorem() is None:
                missing.append(p.name)

        assert missing == [], f"Missing E library entries: {missing}"

    def test_all_48_have_h_library_entry(self):
        """Every Euclid proposition has an H library theorem."""
        from euclid_py.engine.proposition_data import PROPOSITIONS

        missing = []
        for p in PROPOSITIONS:
            if p.source == "euclid" and p.get_h_theorem() is None:
                missing.append(p.name)

        assert missing == [], f"Missing H library entries: {missing}"


# ═══════════════════════════════════════════════════════════════════════
# UI INTERACTION TESTS — add/remove steps, construction syntax
# ═══════════════════════════════════════════════════════════════════════

class TestUiInteraction:
    """Verify UI proof panel handles step manipulation correctly."""

    def test_add_step(self):
        """Adding a step increments the step count."""
        from euclid_py.ui.proof_panel import ProofPanel
        p = ProofPanel()
        p.set_declarations(["A", "B", "C"], [])
        assert len(p._steps) == 0
        p.add_step("Between(A,B,C)", "Given", [])
        assert len(p._steps) == 1
        assert p._steps[0].text == "Between(A,B,C)"

    def test_add_multiple_steps(self):
        """Multiple steps are numbered sequentially."""
        from euclid_py.ui.proof_panel import ProofPanel
        p = ProofPanel()
        p.set_declarations(["A", "B", "C"], [])
        p.add_step("Between(A,B,C)", "Given", [])
        p.add_step("Between(C,B,A)", "Diagrammatic", [1])
        assert len(p._steps) == 2
        assert p._steps[1].line_number == 2

    def test_add_premise_text(self):
        """add_premise_text populates the premise list."""
        from euclid_py.ui.proof_panel import ProofPanel
        p = ProofPanel()
        p.add_premise_text("¬(a = b)")
        assert "¬(a = b)" in p._premises

    def test_add_premise_no_duplicate(self):
        """Adding the same premise twice does not create duplicates."""
        from euclid_py.ui.proof_panel import ProofPanel
        p = ProofPanel()
        p.add_premise_text("¬(a = b)")
        p.add_premise_text("¬(a = b)")
        assert p._premises.count("¬(a = b)") == 1

    def test_set_conclusion(self):
        """set_conclusion sets the goal formula."""
        from euclid_py.ui.proof_panel import ProofPanel
        p = ProofPanel()
        p.set_conclusion("ab = ac, ab = bc")
        assert p._conclusion == "ab = ac, ab = bc"

    def test_clear_resets_everything(self):
        """clear() removes all premises, steps, and conclusion."""
        from euclid_py.ui.proof_panel import ProofPanel
        p = ProofPanel()
        p.add_premise_text("¬(a = b)")
        p.add_step("Between(A,B,C)", "Given", [])
        p.set_conclusion("ab = cd")
        p.clear()
        assert len(p._premises) == 0
        assert len(p._steps) == 0
        assert p._conclusion == ""

    def test_insert_step_at_position(self):
        """insert_step_at inserts a step at the given index."""
        from euclid_py.ui.proof_panel import ProofPanel
        p = ProofPanel()
        p.add_step("A", "Given", [])
        p.add_step("C", "Given", [])
        p.insert_step_at(1, "B", "Given", [])
        assert len(p._steps) == 3
        assert p._steps[1].text == "B"

    def test_steps_with_premises_numbered_correctly(self):
        """Proof steps are numbered after premises."""
        from euclid_py.ui.proof_panel import ProofPanel
        p = ProofPanel()
        p.add_premise_text("A != B")
        p.add_premise_text("Between(A,B,C)")
        p.add_step("Between(C,B,A)", "Diagrammatic", [1])
        # 2 premises → step starts at line 3
        assert p._steps[0].line_number == 3


# ═══════════════════════════════════════════════════════════════════════
# INTEGRATION TESTS — complete proof verified through UI pipeline
# ═══════════════════════════════════════════════════════════════════════

class TestIntegrationProof:
    """Verify complete proofs through the UI's _eval_all pipeline."""

    def test_simple_between_symmetry_accepted(self):
        """Between(A,B,C) ⊢ Between(C,B,A) is accepted by the verifier."""
        from euclid_py.ui.proof_panel import ProofPanel
        p = ProofPanel()
        p.set_declarations(["A", "B", "C"], [])
        p.add_premise_text("Between(A,B,C)")
        p.set_conclusion("Between(C,B,A)")
        p.add_step("Between(C,B,A)", "Diagrammatic", [1])
        p._eval_all()
        assert any(s.status == "✓" for s in p._steps), \
            f"Expected ✓ step, got: {[s.status for s in p._steps]}"

    def test_simple_proof_goal_accepted(self):
        """A simple derivation marks the goal as accepted."""
        from euclid_py.ui.proof_panel import ProofPanel
        p = ProofPanel()
        p.set_declarations(["A", "B", "C"], [])
        p.add_premise_text("Between(A,B,C)")
        p.set_conclusion("Between(C,B,A)")
        p.add_step("Between(C,B,A)", "Diagrammatic", [1])
        p._eval_all()
        goal_text = p._goal_status.text()
        assert goal_text == "✓", f"Goal status: {goal_text!r}"

    def test_e_checker_verify_proof_api(self):
        """verify_proof accepts a valid E proof with diagrammatic step."""
        from verifier.unified_checker import verify_proof
        from verifier.e_ast import (
            EProof, Sort, Literal, ProofStep, StepKind,
            Center, Inside,
        )

        proof = EProof(
            name="center-inside",
            free_vars=[("a", Sort.POINT), ("α", Sort.CIRCLE)],
            hypotheses=[Literal(Center("a", "α"))],
            goal=[Literal(Inside("a", "α"))],
            steps=[
                ProofStep(
                    id=1,
                    kind=StepKind.DIAGRAMMATIC,
                    assertions=[Literal(Inside("a", "α"))],
                ),
            ],
        )
        result = verify_proof(proof)
        assert result.valid
        assert result.engine == "e"

    def test_verify_named_proof_returns_result(self):
        """verify_named_proof returns a UnifiedResult for each proposition."""
        from verifier.unified_checker import verify_named_proof

        result = verify_named_proof("Prop.I.1")
        assert result is not None
        assert result.e_result is not None
        # The proof may not pass (encoded proof needs improvement),
        # but the pipeline must not crash.

    def test_no_steps_shows_neutral_prompt(self):
        """With no steps, _eval_all shows a neutral prompt, not an error."""
        from euclid_py.ui.proof_panel import ProofPanel
        p = ProofPanel()
        p.set_declarations(["A", "B"], [])
        p.add_premise_text("¬(a = b)")
        p.set_conclusion("ab = ac")
        p._eval_all()
        detail = p._detail.text()
        assert "Verifier error" not in detail
        assert "Add proof steps" in detail


# ═══════════════════════════════════════════════════════════════════════
# NEGATIVE TESTS — invalid proofs rejected with E-language diagnostics
# ═══════════════════════════════════════════════════════════════════════

class TestNegativeProofs:
    """Invalid proofs must be rejected, not silently accepted."""

    def test_wrong_justification_rejected(self):
        """A step citing the wrong rule is marked as invalid."""
        from euclid_py.ui.proof_panel import ProofPanel
        p = ProofPanel()
        p.set_declarations(["A", "B", "C"], [])
        p.add_premise_text("Between(A,B,C)")
        # Ord1 doesn't give you Between(C,B,A) — that's Ord2.
        p.add_step("Between(C,B,A)", "Ord1", [1])
        p.set_conclusion("Between(C,B,A)")
        p._eval_all()
        step = p._steps[0]
        assert step.status != "✓", \
            f"Wrong-rule step should not be ✓, got: {step.status}"

    def test_goal_not_derived_shown(self):
        """If goal is not derived, the goal status shows ✗."""
        from euclid_py.ui.proof_panel import ProofPanel
        p = ProofPanel()
        p.set_declarations(["A", "B", "C"], [])
        p.add_premise_text("Between(A,B,C)")
        p.set_conclusion("Between(A,C,B)")  # not derivable from Between(A,B,C)
        p.add_step("Between(C,B,A)", "Ord2", [1])
        p._eval_all()
        goal_text = p._goal_status.text()
        assert goal_text == "✗", f"Goal should be ✗, got: {goal_text!r}"

    def test_invalid_e_proof_rejected(self):
        """An E proof with an unjustified assertion is rejected."""
        from verifier.unified_checker import verify_proof
        from verifier.e_ast import (
            EProof, Sort, Literal, ProofStep, StepKind, On,
        )

        # Claim on(a, L) without any justification
        proof = EProof(
            name="unjustified",
            free_vars=[("a", Sort.POINT), ("L", Sort.LINE)],
            hypotheses=[],
            goal=[Literal(On("a", "L"))],
            steps=[],
        )
        result = verify_proof(proof)
        assert not result.valid

    def test_empty_proof_with_goal_rejected(self):
        """An empty proof with a non-trivial goal is rejected."""
        from verifier.unified_checker import verify_proof
        from verifier.e_ast import (
            EProof, Sort, Literal, On,
        )

        proof = EProof(
            name="empty-with-goal",
            free_vars=[("a", Sort.POINT), ("L", Sort.LINE)],
            hypotheses=[],
            goal=[Literal(On("a", "L"))],
            steps=[],
        )
        result = verify_proof(proof)
        assert not result.valid
        assert len(result.errors) > 0

    def test_rejected_proof_has_e_language_diagnostics(self):
        """Rejected proofs produce diagnostics in E-language, not T or H."""
        from verifier.unified_checker import verify_proof
        from verifier.e_ast import (
            EProof, Sort, Literal, On,
        )

        proof = EProof(
            name="bad-proof",
            free_vars=[("a", Sort.POINT), ("L", Sort.LINE)],
            hypotheses=[],
            goal=[Literal(On("a", "L"))],
            steps=[],
        )
        result = verify_proof(proof)
        assert not result.valid
        # Errors should reference E-language concepts, not Tarski
        all_text = " ".join(result.errors + result.diagnostics)
        assert "Cong(" not in all_text, "Diagnostics leak T-language"
        assert "BetS(" not in all_text, "Diagnostics leak T-language"
        assert "IncidL(" not in all_text, "Diagnostics leak H-language"

    def test_ui_invalid_proof_detail_no_crash(self):
        """UI _eval_all with an invalid proof must not crash."""
        from euclid_py.ui.proof_panel import ProofPanel
        p = ProofPanel()
        p.set_declarations(["A", "B"], [])
        p.add_premise_text("A != B")
        p.set_conclusion("B != A")
        # Wrong rule for this derivation
        p.add_step("B != A", "Between(X,Y,Z)", [1])
        p._eval_all()
        # Must not crash; detail bar should show something
        detail = p._detail.text()
        assert detail is not None
        assert len(detail) > 0
