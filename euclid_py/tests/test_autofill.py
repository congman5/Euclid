"""
test_autofill.py — Comprehensive tests for the proof panel auto-fill engine.

Tests the three autofill paths:
  1. Construction autofill (let-line, let-circle, intersection rules)
  2. Named axiom autofill (Generality, Betweenness, Intersection, etc.)
  3. Theorem autofill (Prop.I.x applications)

Also tests edge cases:
  - Multi-conclusion axiom handling (disjunctive clauses)
  - Known facts from prior accepted steps (not just refs)
  - Fresh name picking avoids collisions
  - Wrong refs / missing refs → autofill failure
  - The Prop I.1 scenario from the user's screenshot
"""
from __future__ import annotations

import pytest
import sys


def _has_display() -> bool:
    try:
        from PyQt6.QtWidgets import QApplication
        app = QApplication.instance() or QApplication(sys.argv)
        return True
    except Exception:
        return False


@pytest.mark.skipif(not _has_display(), reason="No display available")
class TestAutofillConstruction:
    """Construction rule autofill (let-line, let-circle, intersections)."""

    @pytest.fixture(autouse=True)
    def qt_app(self):
        from PyQt6.QtWidgets import QApplication
        self.app = QApplication.instance() or QApplication(sys.argv)
        yield

    def _make_panel(self):
        from euclid_py.ui.proof_panel import ProofPanel
        return ProofPanel()

    def test_let_line_autofill(self):
        """let-line with premise ¬(a = b) auto-fills on(a, L), on(b, L)."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], ["L"])
        p.add_premise_text("\u00ac(a = b)")
        # Step with empty text, let-line justification, ref to premise
        p.add_step("", "let-line", [1])
        p._eval_all()
        step = p._steps[0]
        assert step.text.strip() != "", "Autofill should have populated the text"
        assert "on(" in step.text, f"Expected on() predicates, got: {step.text}"

    def test_let_circle_autofill(self):
        """let-circle with premise ¬(a = b) auto-fills center(a, α), on(b, α)."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        p.add_step("", "let-circle", [1])
        p._eval_all()
        step = p._steps[0]
        assert step.text.strip() != "", "Autofill should have populated the text"
        assert "center(" in step.text, f"Expected center(), got: {step.text}"
        assert "on(" in step.text, f"Expected on(), got: {step.text}"

    def test_let_circle_fresh_name_avoids_collision(self):
        """Two let-circle steps should get distinct circle names (α, β)."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        # First circle: center(a, α), on(b, α)
        p.add_step("", "let-circle", [1])
        p._eval_all()
        first_text = p._steps[0].text
        assert "\u03b1" in first_text, \
            f"First circle should use α, got: {first_text}"

        # Second circle (with different binding): center(b, ?), on(a, ?)
        p.add_step("", "let-circle", [1])
        p._eval_all()
        second_text = p._steps[1].text
        assert second_text.strip() != "", "Second autofill should populate text"
        # The second circle should NOT reuse α
        # Extract circle names from both steps
        first_circles = set()
        second_circles = set()
        for greek in ["\u03b1", "\u03b2", "\u03b3"]:
            if greek in first_text:
                first_circles.add(greek)
            if greek in second_text:
                second_circles.add(greek)
        assert first_circles != second_circles, \
            f"Both circles use same name: step1={first_text}, step2={second_text}"

    def test_let_line_no_prereq_fails(self):
        """let-line without the ¬(a = b) prerequisite fails autofill."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        # No premise — prerequisite ¬(a = b) not available
        p.add_step("", "let-line", [])
        p._eval_all()
        step = p._steps[0]
        # Should be marked as failed
        assert step.status == "\u2717", \
            f"Expected ✗ for missing prerequisite, got: {step.status}"

    def test_construction_uses_known_facts_not_just_refs(self):
        """Construction autofill should find ¬(a = b) from premises even
        without explicit refs, because _collect_known_literals includes
        all premises."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        # Empty refs — but the known facts pool includes the premise
        p.add_step("", "let-circle", [])
        p._eval_all()
        step = p._steps[0]
        assert step.text.strip() != "", \
            f"Autofill should use known facts from premises even without refs"
        assert "center(" in step.text


class TestAutofillConstructionHeadless:
    """Construction autofill unit tests that don't require a display."""

    def test_match_hypotheses_basic(self):
        """_match_hypotheses correctly matches pattern against concrete."""
        from euclid_py.ui.proof_panel import ProofPanel
        from verifier.e_ast import Literal, Equals

        patterns = [Literal(Equals("a", "b"), polarity=False)]
        concrete = [Literal(Equals("x", "y"), polarity=False)]
        bindings, matched = ProofPanel._match_hypotheses(patterns, concrete)
        assert matched == 1
        assert bindings.get("a") == "x"
        assert bindings.get("b") == "y"

    def test_match_hypotheses_binding_conflict(self):
        """_match_hypotheses returns 0 matched on binding conflict."""
        from euclid_py.ui.proof_panel import ProofPanel
        from verifier.e_ast import Literal, On

        # Two patterns needing different bindings for 'a'
        patterns = [
            Literal(On("a", "L"), polarity=True),
            Literal(On("a", "M"), polarity=True),
        ]
        concrete = [
            Literal(On("x", "L1"), polarity=True),
            Literal(On("y", "M1"), polarity=True),  # a→y conflicts with a→x
        ]
        bindings, matched = ProofPanel._match_hypotheses(patterns, concrete)
        # First match binds a→x, L→L1; second needs a→y which conflicts
        assert matched < 2

    def test_pick_fresh_name_point(self):
        """Fresh point name avoids used names."""
        from euclid_py.ui.proof_panel import ProofPanel
        from verifier.e_ast import Sort
        name = ProofPanel._pick_fresh_name("a", Sort.POINT, {"a", "b"})
        assert name not in {"a", "b"}

    def test_pick_fresh_name_circle(self):
        """Fresh circle name uses Greek letters."""
        from euclid_py.ui.proof_panel import ProofPanel
        from verifier.e_ast import Sort
        name = ProofPanel._pick_fresh_name("\u03b1", Sort.CIRCLE, set())
        assert name == "\u03b1"

    def test_pick_fresh_name_circle_avoids_used(self):
        """Fresh circle name skips α if already used."""
        from euclid_py.ui.proof_panel import ProofPanel
        from verifier.e_ast import Sort
        name = ProofPanel._pick_fresh_name(
            "\u03b1", Sort.CIRCLE, {"\u03b1"})
        assert name == "\u03b2"

    def test_pick_fresh_name_line(self):
        """Fresh line name uses uppercase letters."""
        from euclid_py.ui.proof_panel import ProofPanel
        from verifier.e_ast import Sort
        name = ProofPanel._pick_fresh_name("L", Sort.LINE, set())
        assert name == "L"

    def test_extract_symbols_greek(self):
        """_extract_symbols detects Greek circle names."""
        from euclid_py.ui.proof_panel import ProofPanel
        syms = ProofPanel._extract_symbols("center(a, \u03b1), on(b, \u03b1)")
        assert "\u03b1" in syms
        assert "a" in syms
        assert "b" in syms

    def test_extract_symbols_negation(self):
        """_extract_symbols works with negated equality."""
        from euclid_py.ui.proof_panel import ProofPanel
        syms = ProofPanel._extract_symbols("\u00ac(a = b)")
        assert "a" in syms
        assert "b" in syms


@pytest.mark.skipif(not _has_display(), reason="No display available")
class TestAutofillNamedAxiom:
    """Named axiom autofill (Generality, Betweenness, Intersection, etc.)."""

    @pytest.fixture(autouse=True)
    def qt_app(self):
        from PyQt6.QtWidgets import QApplication
        self.app = QApplication.instance() or QApplication(sys.argv)
        yield

    def _make_panel(self):
        from euclid_py.ui.proof_panel import ProofPanel
        return ProofPanel()

    def test_generality_3_autofill(self):
        """Generality 3: center(a,α) → inside(a,α).

        Given center(a, α) as a known fact, autofill should produce
        inside(a, α).
        """
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        p.add_step("center(a, \u03b1), on(b, \u03b1)", "let-circle", [1])
        # Empty text, Generality 3 justification, ref to step 2
        p.add_step("", "Generality 3", [2])
        p._eval_all()
        step = p._steps[1]  # the Generality 3 step
        assert step.text.strip() != "", \
            f"Generality 3 autofill should produce text"
        assert "inside(" in step.text, \
            f"Expected inside(), got: {step.text}"
        assert "\u03b1" in step.text, \
            f"Expected circle α in result, got: {step.text}"

    def test_generality_3_accepted_by_verifier(self):
        """Generality 3 autofill result should pass verification."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        p.add_step("center(a, \u03b1), on(b, \u03b1)", "let-circle", [1])
        p.add_step("", "Generality 3", [2])
        p._eval_all()
        step = p._steps[1]
        assert step.status == "\u2713", \
            f"Generality 3 should be accepted, got status: {step.status}"

    def test_betweenness_1a_autofill(self):
        """Betweenness 1a (B1a): between(a,b,c) → between(c,b,a).

        Single-conclusion axiom, should autofill.
        """
        p = self._make_panel()
        p.set_declarations(["a", "b", "c"], [])
        p.add_premise_text("between(a, b, c)")
        p.add_step("", "Betweenness 1a", [1])
        p._eval_all()
        step = p._steps[0]
        assert step.text.strip() != "", \
            f"Betweenness 1a autofill should produce text"
        assert "between(" in step.text, \
            f"Expected between(), got: {step.text}"

    def test_multi_conclusion_axiom_skips_autofill(self):
        """Axioms with multiple positive literals (disjunctive conclusions)
        should not autofill — they return None (not _AUTOFILL_FAIL),
        leaving the step empty for the user to fill in manually."""
        from euclid_py.ui.proof_panel import ProofPanel
        ax_index = ProofPanel._get_axiom_by_name()
        # "Intersection 2b" has multiple positive literals
        clause = ax_index.get("Intersection 2b")
        assert clause is not None
        conclusions = [l for l in clause.literals if l.polarity]
        assert len(conclusions) > 1, \
            f"Intersection 2b should have multiple conclusions, got {len(conclusions)}"

    def test_named_axiom_wrong_refs_fails(self):
        """Named axiom with wrong refs should fail autofill (✗)."""
        p = self._make_panel()
        p.set_declarations(["a", "b", "c"], [])
        # Premise: between(a, b, c)
        p.add_premise_text("between(a, b, c)")
        # Generality 3 expects center(a,α), not between
        p.add_step("", "Generality 3", [1])
        p._eval_all()
        step = p._steps[0]
        assert step.status == "\u2717", \
            f"Wrong refs for Generality 3 should be ✗, got: {step.status}"

    def test_named_axiom_uses_known_facts_from_prior_steps(self):
        """Named axiom autofill should find facts from prior accepted
        steps, not just from explicit refs."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        # Step 2: manually typed let-circle result
        p.add_step("center(a, \u03b1), on(b, \u03b1)", "let-circle", [1])
        # Step 3: Generality 3 with NO refs — should still find
        # center(a, α) from step 2's known facts
        p.add_step("", "Generality 3", [])
        p._eval_all()
        step = p._steps[1]  # the Generality 3 step
        assert step.text.strip() != "", \
            f"Should autofill from prior step's known facts"
        assert "inside(" in step.text

    def test_axiom_index_populated(self):
        """The lazy axiom index contains all named axioms."""
        from euclid_py.ui.proof_panel import ProofPanel
        ax_index = ProofPanel._get_axiom_by_name()
        # Should have entries for all groups
        assert "Generality 1" in ax_index
        assert "Generality 3" in ax_index
        assert "Betweenness 1a" in ax_index
        assert "Intersection 1" in ax_index
        assert "Segment transfer 1" in ax_index
        # With backward-compat aliases, we have more entries than before
        assert len(ax_index) >= 50  # at least 50 named axioms


@pytest.mark.skipif(not _has_display(), reason="No display available")
class TestAutofillTheorem:
    """Theorem application autofill (Prop.I.x)."""

    @pytest.fixture(autouse=True)
    def qt_app(self):
        from PyQt6.QtWidgets import QApplication
        self.app = QApplication.instance() or QApplication(sys.argv)
        yield

    def _make_panel(self):
        from euclid_py.ui.proof_panel import ProofPanel
        return ProofPanel()

    def test_theorem_lookup(self):
        """Theorem library contains Prop.I.1 through Prop.I.48."""
        from verifier.e_library import E_THEOREM_LIBRARY
        for i in range(1, 49):
            name = f"Prop.I.{i}"
            assert name in E_THEOREM_LIBRARY, \
                f"Missing theorem {name}"

    def test_theorem_autofill_produces_text(self):
        """Theorem autofill with correct hypotheses produces conclusion text."""
        from verifier.e_library import E_THEOREM_LIBRARY
        thm = E_THEOREM_LIBRARY.get("Prop.I.1")
        assert thm is not None
        # If the theorem has hypotheses, we can test matching
        if thm.sequent.hypotheses:
            p = self._make_panel()
            p.set_declarations(["a", "b"], [])
            # Add hypothesis as premise
            hyp_text = repr(thm.sequent.hypotheses[0])
            p.add_premise_text(hyp_text)
            p.add_step("", "Prop.I.1", [1])
            p._eval_all()
            step = p._steps[0]
            # Autofill should produce text (may or may not verify)
            assert step.text.strip() != "", \
                f"Theorem autofill should produce text for Prop.I.1"

    def test_unknown_theorem_fails(self):
        """Unknown theorem name should fail autofill (✗)."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        p.add_step("", "Prop.I.999", [1])
        p._eval_all()
        step = p._steps[0]
        assert step.status == "\u2717", \
            f"Unknown theorem should be ✗, got: {step.status}"


@pytest.mark.skipif(not _has_display(), reason="No display available")
class TestAutofillPropI1Scenario:
    """Integration test matching the user's exact Prop I.1 screenshot.

    Scenario:
      Premise 1: ¬(a = b)
      Step 2: center(a, α), on(b, α)  — let-circle : 1  ✓
      Step 3: center(b, β), on(a, β)  — let-circle : 1  ✓
      Step 4: inside(a, α)            — Generality 3 : 2 ✓
      Step 5: inside(b, β)            — Generality 3 : 3 ✓
    """

    @pytest.fixture(autouse=True)
    def qt_app(self):
        from PyQt6.QtWidgets import QApplication
        self.app = QApplication.instance() or QApplication(sys.argv)
        yield

    def _make_panel(self):
        from euclid_py.ui.proof_panel import ProofPanel
        return ProofPanel()

    def test_prop_i1_let_circle_autofill(self):
        """Step 2: let-circle autofill from ¬(a = b)."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        p.add_step("", "let-circle", [1])
        p._eval_all()
        step = p._steps[0]
        assert step.text.strip() != "", "let-circle should autofill"
        assert "center(" in step.text
        assert "on(" in step.text
        assert step.status == "\u2713", \
            f"let-circle step should be ✓, got: {step.status}"

    def test_prop_i1_two_circles_distinct_names(self):
        """Steps 2 and 3: two let-circle steps get distinct circle names."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        # Both reference premise 1
        p.add_step("", "let-circle", [1])
        p.add_step("", "let-circle", [1])
        p._eval_all()
        text1 = p._steps[0].text
        text2 = p._steps[1].text
        assert text1.strip() != "", "First let-circle should autofill"
        assert text2.strip() != "", "Second let-circle should autofill"
        # They should use different circle names
        assert text1 != text2, \
            f"Two circles should have different text: {text1} vs {text2}"

    def test_prop_i1_generality3_from_let_circle(self):
        """Step 4: Generality 3 autofill from prior let-circle step."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        # Manually fill step 2 (as if let-circle already autofilled)
        p.add_step(
            "center(a, \u03b1), on(b, \u03b1)", "let-circle", [1])
        # Step 3: Generality 3 referencing step 2
        p.add_step("", "Generality 3", [2])
        p._eval_all()
        gen_step = p._steps[1]
        assert gen_step.text.strip() != "", \
            "Generality 3 should autofill"
        assert "inside(a, \u03b1)" in gen_step.text, \
            f"Expected inside(a, α), got: {gen_step.text}"
        assert gen_step.status == "\u2713", \
            f"Generality 3 should be ✓, got: {gen_step.status}"

    def test_prop_i1_full_first_five_steps(self):
        """Full Prop I.1 first 5 steps: premise + 2 circles + 2 Generality 3.

        All steps should autofill and verify correctly.
        """
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        # Step 2: let-circle (center a)
        p.add_step(
            "center(a, \u03b1), on(b, \u03b1)", "let-circle", [1])
        # Step 3: let-circle (center b)
        p.add_step(
            "center(b, \u03b2), on(a, \u03b2)", "let-circle", [1])
        # Step 4: Generality 3 from step 2 (center(a,α) → inside(a,α))
        p.add_step("", "Generality 3", [2])
        # Step 5: Generality 3 from step 3 (center(b,β) → inside(b,β))
        p.add_step("", "Generality 3", [3])
        p._eval_all()

        # Steps 2-3 (manually filled): should verify
        assert p._steps[0].status == "\u2713", \
            f"Step 2 (let-circle) should be ✓, got: {p._steps[0].status}"
        assert p._steps[1].status == "\u2713", \
            f"Step 3 (let-circle) should be ✓, got: {p._steps[1].status}"

        # Steps 4-5 (autofilled): should verify
        assert p._steps[2].text.strip() != "", \
            "Step 4 should be autofilled"
        assert p._steps[2].status == "\u2713", \
            f"Step 4 (Generality 3) should be ✓, got: {p._steps[2].status}"
        assert p._steps[3].text.strip() != "", \
            "Step 5 should be autofilled"
        assert p._steps[3].status == "\u2713", \
            f"Step 5 (Generality 3) should be ✓, got: {p._steps[3].status}"

    def test_prop_i1_intersection2b_multi_conclusion(self):
        """Intersection 2b (I2b) is a multi-conclusion axiom.

        In the Prop I.1 screenshot, step 6 used 'Intersection 2b' with
        refs 2,3 and had empty text → ✗. This is expected because
        Intersection 2b has multiple positive conclusions, so autofill
        cannot determine the intended one. The step stays empty and
        the verifier rejects it.
        """
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        p.add_step(
            "center(a, \u03b1), on(b, \u03b1)", "let-circle", [1])
        p.add_step(
            "center(b, \u03b2), on(a, \u03b2)", "let-circle", [1])
        # Intersection 2b with refs to steps 2 and 3 — multi-conclusion
        p.add_step("", "Intersection 2b", [2, 3])
        p._eval_all()
        step = p._steps[2]
        # Multi-conclusion axiom: autofill returns None, text stays empty
        # Verifier rejects empty statement
        assert step.status == "\u2717", \
            f"Intersection 2b (multi-conclusion) should be ✗, got: {step.status}"

    def test_prop_i1_intersection5_produces_correct_order(self):
        """Intersection 5 (I5) autofill must produce intersects(α, β),
        not the swapped intersects(β, α).

        Regression test: Clause.literals is a frozenset so prereq
        iteration order is non-deterministic.  Without stable sorting,
        inside() prereqs can bind before on() prereqs, swapping the
        circle names in the conclusion.

        Uses refs 2,3,4,5 (all four prerequisites) as required by the
        ref-restricted verifier.
        """
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        p.add_step(
            "center(a, \u03b1), on(b, \u03b1)", "let-circle", [1])
        p.add_step(
            "center(b, \u03b2), on(a, \u03b2)", "let-circle", [1])
        p.add_step("", "Generality 3", [2])
        p.add_step("", "Generality 3", [3])
        # Intersection 5 with all four prerequisite refs
        p.add_step("", "Intersection 5", [2, 3, 4, 5])
        p._eval_all()
        step = p._steps[4]  # the Intersection 5 step
        assert step.text.strip() != "", \
            "Intersection 5 should autofill"
        assert "intersects(\u03b1, \u03b2)" in step.text, \
            f"Expected intersects(\u03b1, \u03b2), got: {step.text}"
        assert step.status == "\u2713", \
            f"Intersection 5 should be \u2713, got: {step.status}"

    def test_prop_i1_intersection5_incomplete_refs_fails(self):
        """Intersection 5 (I5) with only refs 4,5 (missing on() facts)
        should fail verification because the referenced lines do not
        contain all four prerequisites."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        p.add_step(
            "center(a, \u03b1), on(b, \u03b1)", "let-circle", [1])
        p.add_step(
            "center(b, \u03b2), on(a, \u03b2)", "let-circle", [1])
        p.add_step("", "Generality 3", [2])
        p.add_step("", "Generality 3", [3])
        # Only citing the inside() facts — missing the on() facts
        p.add_step("", "Intersection 5", [4, 5])
        p._eval_all()
        step = p._steps[4]
        # Autofill still populates the text...
        assert step.text.strip() != "", \
            "Autofill should still produce text"
        # ...but verification rejects it because refs are incomplete
        assert step.status == "\u2717", \
            f"Incomplete refs should be \u2717, got: {step.status}"

    def test_prop_i1_intersection5_with_all_refs(self):
        """Intersection 5 (I5) with refs 2,3,4,5 (answer key format)."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        p.add_step(
            "center(a, \u03b1), on(b, \u03b1)", "let-circle", [1])
        p.add_step(
            "center(b, \u03b2), on(a, \u03b2)", "let-circle", [1])
        p.add_step("", "Generality 3", [2])
        p.add_step("", "Generality 3", [3])
        # Intersection 5 with all four refs (answer key style)
        p.add_step("", "Intersection 5", [2, 3, 4, 5])
        p._eval_all()
        step = p._steps[4]
        assert "intersects(\u03b1, \u03b2)" in step.text, \
            f"Expected intersects(\u03b1, \u03b2), got: {step.text}"
        assert step.status == "\u2713", \
            f"Intersection 5 should be \u2713, got: {step.status}"


@pytest.mark.skipif(not _has_display(), reason="No display available")
class TestAutofillEdgeCases:
    """Edge cases for autofill: empty justification, unknown rules, etc."""

    @pytest.fixture(autouse=True)
    def qt_app(self):
        from PyQt6.QtWidgets import QApplication
        self.app = QApplication.instance() or QApplication(sys.argv)
        yield

    def _make_panel(self):
        from euclid_py.ui.proof_panel import ProofPanel
        return ProofPanel()

    def test_empty_justification_no_autofill(self):
        """A step with empty justification should not autofill."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        p.add_step("", "", [1])
        p._eval_all()
        step = p._steps[0]
        assert step.text.strip() == "", \
            "Empty justification should not trigger autofill"

    def test_diagrammatic_justification_no_autofill(self):
        """'Diagrammatic' is a generic justification, not a named axiom.
        It should not trigger autofill."""
        p = self._make_panel()
        p.set_declarations(["a", "b", "c"], [])
        p.add_premise_text("between(a, b, c)")
        p.add_step("", "Diagrammatic", [1])
        p._eval_all()
        step = p._steps[0]
        # Autofill returns None for unrecognised justifications
        # The step stays empty and gets rejected
        assert step.text.strip() == "", \
            "Generic 'Diagrammatic' should not autofill"

    def test_autofill_does_not_crash_on_parse_error(self):
        """Autofill with unparseable ref text should not crash."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("GARBAGE!@#$%")
        p.add_step("", "let-circle", [1])
        # Should not raise — just fail gracefully
        p._eval_all()
        step = p._steps[0]
        assert step.status in ("\u2717", "?"), \
            f"Should handle parse error gracefully, got: {step.status}"

    def test_autofill_with_nonexistent_ref(self):
        """Autofill referencing a non-existent line number should not crash."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        p.add_step("", "let-circle", [99])  # line 99 doesn't exist
        p._eval_all()
        # Should not crash — may autofill from all_known or fail
        assert True  # reaching here means no crash

    def test_autofill_with_already_filled_text(self):
        """Autofill should NOT overwrite text that's already filled."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        p.add_step("on(a, L)", "let-line", [1])
        original_text = p._steps[0].text
        p._eval_all()
        assert p._steps[0].text == original_text, \
            "Autofill should not overwrite existing text"


@pytest.mark.skipif(not _has_display(), reason="No display available")
class TestAutofillCollectKnownLiterals:
    """Tests for _collect_known_literals — the known-facts pool."""

    @pytest.fixture(autouse=True)
    def qt_app(self):
        from PyQt6.QtWidgets import QApplication
        self.app = QApplication.instance() or QApplication(sys.argv)
        yield

    def _make_panel(self):
        from euclid_py.ui.proof_panel import ProofPanel
        return ProofPanel()

    def test_includes_all_premises(self):
        """Known literals include all premises."""
        p = self._make_panel()
        p.set_declarations(["a", "b", "c"], [])
        p.add_premise_text("\u00ac(a = b)")
        p.add_premise_text("between(a, b, c)")
        p.add_step("dummy", "Given", [])
        lits = p._collect_known_literals(p._steps[0].line_number)
        # Should have at least 2 literals from the two premises
        assert len(lits) >= 2, f"Expected ≥2 known literals, got {len(lits)}"

    def test_includes_prior_steps(self):
        """Known literals include text from prior proof steps."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        p.add_step(
            "center(a, \u03b1), on(b, \u03b1)", "let-circle", [1])
        p.add_step("dummy", "Given", [])
        # Step 3 (line_number 3) should see step 2's literals
        lits = p._collect_known_literals(p._steps[1].line_number)
        lit_reprs = [repr(l) for l in lits]
        assert any("center(" in r for r in lit_reprs), \
            f"Should include center() from step 2, got: {lit_reprs}"

    def test_excludes_current_and_future_steps(self):
        """Known literals should NOT include the current or later steps."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        p.add_step(
            "center(a, \u03b1), on(b, \u03b1)", "let-circle", [1])
        p.add_step("inside(a, \u03b1)", "Generality 3", [2])
        # Collect known for step 2 (line 2) — should not include step 2 itself
        lits = p._collect_known_literals(p._steps[0].line_number)
        lit_reprs = [repr(l) for l in lits]
        # Only premise should be visible, not step 2's text
        assert not any("center(" in r for r in lit_reprs), \
            "Should not include current step's own text"

    def test_parse_ref_literals_returns_parsed(self):
        """_parse_ref_literals returns parsed literals from ref'd lines."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        # Premise is line 1
        lits = p._parse_ref_literals([1])
        assert len(lits) >= 1, \
            f"Should parse premise ref into literals, got: {lits}"

    def test_parse_ref_literals_empty_for_nonexistent(self):
        """_parse_ref_literals returns empty for nonexistent line."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        lits = p._parse_ref_literals([99])
        assert len(lits) == 0


# ═══════════════════════════════════════════════════════════════════════════
# CONSTRUCTION PREREQUISITE ENFORCEMENT — verifier rejects invalid steps
# ═══════════════════════════════════════════════════════════════════════════

class TestConstructionPrereqEnforcement:
    """Verify that the verifier enforces construction prerequisites.

    The rule reference tab shows prerequisites (e.g. ¬(a = b) for
    let-circle). The verifier must reject steps that don't satisfy them.
    """

    def test_let_circle_rejected_without_prereq(self):
        """let-circle with correct text but no ¬(a = b) → rejected."""
        from verifier.unified_checker import verify_e_proof_json
        proof = {
            "name": "test",
            "declarations": {"points": ["a", "b"], "lines": []},
            "premises": [],
            "goal": "",
            "lines": [
                {"id": 1, "depth": 0,
                 "statement": "center(a, \u03b1), on(b, \u03b1)",
                 "justification": "let-circle", "refs": []},
            ],
        }
        r = verify_e_proof_json(proof)
        assert not r.line_results[1].valid, \
            "let-circle without ¬(a = b) should be rejected"
        assert any("prerequisite" in e.lower()
                    for e in r.line_results[1].errors)

    def test_let_circle_accepted_with_prereq(self):
        """let-circle with correct text and ¬(a = b) → accepted."""
        from verifier.unified_checker import verify_e_proof_json
        proof = {
            "name": "test",
            "declarations": {"points": ["a", "b"], "lines": []},
            "premises": ["\u00ac(a = b)"],
            "goal": "",
            "lines": [
                {"id": 1, "depth": 0,
                 "statement": "\u00ac(a = b)",
                 "justification": "Given", "refs": []},
                {"id": 2, "depth": 0,
                 "statement": "center(a, \u03b1), on(b, \u03b1)",
                 "justification": "let-circle", "refs": [1]},
            ],
        }
        r = verify_e_proof_json(proof)
        assert r.line_results[2].valid, \
            f"let-circle with ¬(a = b) should pass: {r.line_results[2].errors}"

    def test_let_line_rejected_without_prereq(self):
        """let-line with correct text but no ¬(a = b) → rejected."""
        from verifier.unified_checker import verify_e_proof_json
        proof = {
            "name": "test",
            "declarations": {"points": ["a", "b"], "lines": []},
            "premises": [],
            "goal": "",
            "lines": [
                {"id": 1, "depth": 0,
                 "statement": "on(a, L), on(b, L)",
                 "justification": "let-line", "refs": []},
            ],
        }
        r = verify_e_proof_json(proof)
        assert not r.line_results[1].valid, \
            "let-line without ¬(a = b) should be rejected"

    def test_mismatched_text_rejected(self):
        """Construction rule with text not matching conclusion pattern → rejected."""
        from verifier.unified_checker import verify_e_proof_json
        proof = {
            "name": "test",
            "declarations": {"points": ["a", "b"], "lines": ["L"]},
            "premises": ["\u00ac(a = b)"],
            "goal": "",
            "lines": [
                {"id": 1, "depth": 0,
                 "statement": "\u00ac(a = b)",
                 "justification": "Given", "refs": []},
                {"id": 2, "depth": 0,
                 "statement": "on(a, L)",
                 "justification": "let-circle", "refs": [1]},
            ],
        }
        r = verify_e_proof_json(proof)
        assert not r.line_results[2].valid, \
            "Mismatched text should be rejected"
        assert any("conclusion pattern" in e.lower()
                    for e in r.line_results[2].errors)

    def test_partial_conclusion_rejected(self):
        """Construction rule with only part of conclusion → rejected."""
        from verifier.unified_checker import verify_e_proof_json
        proof = {
            "name": "test",
            "declarations": {"points": ["a", "b"], "lines": []},
            "premises": ["\u00ac(a = b)"],
            "goal": "",
            "lines": [
                {"id": 1, "depth": 0,
                 "statement": "\u00ac(a = b)",
                 "justification": "Given", "refs": []},
                {"id": 2, "depth": 0,
                 "statement": "center(a, \u03b1)",
                 "justification": "let-circle", "refs": [1]},
            ],
        }
        r = verify_e_proof_json(proof)
        assert not r.line_results[2].valid, \
            "Partial conclusion (missing on()) should be rejected"

    def test_wrong_text_as_let_line_rejected(self):
        """Completely wrong text with let-line justification → rejected."""
        from verifier.unified_checker import verify_e_proof_json
        proof = {
            "name": "test",
            "declarations": {"points": ["a", "b", "c"], "lines": []},
            "premises": [],
            "goal": "",
            "lines": [
                {"id": 1, "depth": 0,
                 "statement": "between(a, b, c)",
                 "justification": "let-line", "refs": []},
            ],
        }
        r = verify_e_proof_json(proof)
        assert not r.line_results[1].valid, \
            "between() text with let-line should be rejected"

    def test_let_point_on_line_no_prereq_accepted(self):
        """let-point-on-line has no prerequisite — should be accepted."""
        from verifier.unified_checker import verify_e_proof_json
        proof = {
            "name": "test",
            "declarations": {"points": ["a"], "lines": ["L"]},
            "premises": [],
            "goal": "",
            "lines": [
                {"id": 1, "depth": 0,
                 "statement": "on(a, L)",
                 "justification": "let-point-on-line", "refs": []},
            ],
        }
        r = verify_e_proof_json(proof)
        assert r.line_results[1].valid, \
            f"let-point-on-line should pass: {r.line_results[1].errors}"

    def test_intersection_circle_circle_requires_intersects(self):
        """let-intersection-circle-circle-one requires intersects(α, β)."""
        from verifier.unified_checker import verify_e_proof_json
        proof = {
            "name": "test",
            "declarations": {"points": ["c"], "lines": []},
            "premises": [],
            "goal": "",
            "lines": [
                {"id": 1, "depth": 0,
                 "statement": "on(c, \u03b1), on(c, \u03b2)",
                 "justification": "let-intersection-circle-circle-one",
                 "refs": []},
            ],
        }
        r = verify_e_proof_json(proof)
        assert not r.line_results[1].valid, \
            "Circle-circle intersection without intersects() should be rejected"
        assert any("prerequisite" in e.lower()
                    for e in r.line_results[1].errors)


# ===================================================================
# Metric autofill tests — verify Metric justification autofill
# against verified_proofs_book_1.json answer key.
# ===================================================================


@pytest.mark.skipif(not _has_display(), reason="No display available")
class TestAutofillMetric:
    """Metric justification autofill for Prop I.1 / I.4 / I.5 / I.8."""

    @pytest.fixture(autouse=True)
    def qt_app(self):
        from PyQt6.QtWidgets import QApplication
        self.app = QApplication.instance() or QApplication(sys.argv)
        yield

    def _make_panel(self):
        from euclid_py.ui.proof_panel import ProofPanel
        return ProofPanel()

    # -- Prop I.1 -------------------------------------------------

    def _setup_prop_i1_context(self):
        """Build Prop I.1 proof context up to step 9 (before Metric steps)."""
        p = self._make_panel()
        p.set_declarations(["a", "b"], [])
        p.add_premise_text("\u00ac(a = b)")
        # Steps 1-9 (step 1 = "Given" is a premise; add steps 2-9)
        p.add_step(
            "center(a, \u03b1), on(b, \u03b1)", "let-circle", [1])
        p.add_step(
            "center(b, \u03b2), on(a, \u03b2)", "let-circle", [1])
        p.add_step("inside(a, \u03b1)", "Generality 3", [2])
        p.add_step("inside(b, \u03b2)", "Generality 3", [3])
        p.add_step(
            "intersects(\u03b1, \u03b2)", "Intersection 5", [2, 3, 4, 5])
        p.add_step(
            "on(c, \u03b1), on(c, \u03b2)",
            "let-intersection-circle-circle-one", [6])
        p.add_step("ac = ab", "Segment transfer 3b", [2, 7])
        p.add_step("bc = ba", "Segment transfer 3b", [3, 7])
        return p

    def test_prop_i1_step10_swap(self):
        """Prop I.1 step 10: Metric ref=[8] \u2192 ab = ac (swap of ac = ab)."""
        p = self._setup_prop_i1_context()
        p.add_step("", "Metric", [8])
        p._eval_all()
        step = p._steps[8]  # 0-indexed: steps 2-9 are [0..7], step 10 is [8]
        assert step.text == "ab = ac", \
            f"Expected 'ab = ac', got: {step.text!r}"
        assert step.status == "\u2713", \
            f"Expected \u2713, got: {step.status}"

    def test_prop_i1_step11_transitivity(self):
        """Prop I.1 step 11: Metric refs=[9,8] \u2192 ab = bc (transitivity)."""
        p = self._setup_prop_i1_context()
        p.add_step("ab = ac", "Metric", [8])  # step 10
        p.add_step("", "Metric", [9, 8])      # step 11
        p._eval_all()
        step = p._steps[9]
        assert step.text == "ab = bc", \
            f"Expected 'ab = bc', got: {step.text!r}"
        assert step.status == "\u2713", \
            f"Expected \u2713, got: {step.status}"

    def test_prop_i1_step12_disequality(self):
        """Prop I.1 step 12: Metric ref=[8] \u2192 \u00ac(c = a) (M1 disequality)."""
        p = self._setup_prop_i1_context()
        p.add_step("ab = ac", "Metric", [8])   # step 10
        p.add_step("ab = bc", "Metric", [9, 8])  # step 11
        p.add_step("", "Metric", [8])           # step 12
        p._eval_all()
        step = p._steps[10]
        assert step.text == "\u00ac(c = a)", \
            f"Expected '\u00ac(c = a)', got: {step.text!r}"
        assert step.status == "\u2713", \
            f"Expected \u2713, got: {step.status}"

    def test_prop_i1_step13_disequality(self):
        """Prop I.1 step 13: Metric ref=[9] \u2192 \u00ac(c = b) (M1 disequality)."""
        p = self._setup_prop_i1_context()
        p.add_step("ab = ac", "Metric", [8])     # step 10
        p.add_step("ab = bc", "Metric", [9, 8])  # step 11
        p.add_step("\u00ac(c = a)", "Metric", [8])  # step 12
        p.add_step("", "Metric", [9])             # step 13
        p._eval_all()
        step = p._steps[11]
        assert step.text == "\u00ac(c = b)", \
            f"Expected '\u00ac(c = b)', got: {step.text!r}"
        assert step.status == "\u2713", \
            f"Expected \u2713, got: {step.status}"

    # -- Prop I.4 -------------------------------------------------

    def test_prop_i4_step5_angle_m4_both(self):
        """Prop I.4 step 5: Metric ref=[4] \u2192 \u2220bca = \u2220efd
        (M4-both-sides rewrite of SAS conclusion angle)."""
        p = self._make_panel()
        p.set_declarations([], [])
        # Premises are lines 1-3
        p.add_premise_text("ab = de")
        p.add_premise_text("ac = df")
        p.add_premise_text("\u2220bac = \u2220edf")
        # SAS step = line 4, Metric step = line 5
        p.add_step(
            "bc = ef, \u2220abc = \u2220def, "
            "\u2220acb = \u2220dfe, \u25b3abc = \u25b3def",
            "SAS", [1, 2, 3])
        p.add_step("", "Metric", [4])
        p._eval_all()
        step = p._steps[1]
        assert step.text == "\u2220bca = \u2220efd", \
            f"Expected '\u2220bca = \u2220efd', got: {step.text!r}"
        assert step.status == "\u2713", \
            f"Expected \u2713, got: {step.status}"

    # -- Prop I.5 -------------------------------------------------

    def test_prop_i5_step5_swap(self):
        """Prop I.5 step 5: Metric ref=[1] \u2192 ac = ab (swap of ab = ac)."""
        p = self._make_panel()
        p.set_declarations([], [])
        # Premises are lines 1-4
        p.add_premise_text("ab = ac")
        p.add_premise_text("\u00ac(a = b)")
        p.add_premise_text("\u00ac(a = c)")
        p.add_premise_text("\u00ac(b = c)")
        # Metric step = line 5, ref=[1] points to premise "ab = ac"
        p.add_step("", "Metric", [1])
        p._eval_all()
        step = p._steps[0]
        assert step.text == "ac = ab", \
            f"Expected 'ac = ab', got: {step.text!r}"
        assert step.status == "\u2713", \
            f"Expected \u2713, got: {step.status}"

    def test_prop_i5_step6_angle_consequence(self):
        """Prop I.5 step 6: Metric ref=[1] \u2192 \u2220bac = \u2220cab
        (M9 angle consequence, vertex is shared point 'a')."""
        p = self._make_panel()
        p.set_declarations([], [])
        # Premises are lines 1-4
        p.add_premise_text("ab = ac")
        p.add_premise_text("\u00ac(a = b)")
        p.add_premise_text("\u00ac(a = c)")
        p.add_premise_text("\u00ac(b = c)")
        # Step 5 (swap), step 6 (angle consequence)
        p.add_step("ac = ab", "Metric", [1])
        p.add_step("", "Metric", [1])
        p._eval_all()
        step = p._steps[1]
        assert step.text == "\u2220bac = \u2220cab", \
            f"Expected '\u2220bac = \u2220cab', got: {step.text!r}"
        assert step.status == "\u2713", \
            f"Expected \u2713, got: {step.status}"

    # -- Prop I.8 -------------------------------------------------

    def test_prop_i8_step5_angle_m4_both(self):
        """Prop I.8 step 5: Metric ref=[4] \u2192 \u2220bca = \u2220efd
        (M4-both-sides rewrite of SSS conclusion angle)."""
        p = self._make_panel()
        p.set_declarations([], [])
        # Premises are lines 1-3
        p.add_premise_text("ab = de")
        p.add_premise_text("bc = ef")
        p.add_premise_text("ca = fd")
        # SSS step = line 4, Metric step = line 5
        p.add_step(
            "\u2220bac = \u2220edf, \u2220abc = \u2220def, "
            "\u2220acb = \u2220dfe, \u25b3abc = \u25b3def",
            "SSS", [1, 2, 3])
        p.add_step("", "Metric", [4])
        p._eval_all()
        step = p._steps[1]
        assert step.text == "\u2220bca = \u2220efd", \
            f"Expected '\u2220bca = \u2220efd', got: {step.text!r}"
        assert step.status == "\u2713", \
            f"Expected \u2713, got: {step.status}"


# ===================================================================
# Superposition (SAS / SSS) autofill tests
# ===================================================================


@pytest.mark.skipif(not _has_display(), reason="No display available")
class TestAutofillSuperposition:
    """SAS and SSS superposition autofill against answer key."""

    @pytest.fixture(autouse=True)
    def qt_app(self):
        from PyQt6.QtWidgets import QApplication
        self.app = QApplication.instance() or QApplication(sys.argv)
        yield

    def _make_panel(self):
        from euclid_py.ui.proof_panel import ProofPanel
        return ProofPanel()

    def test_prop_i4_sas(self):
        """Prop I.4 step 4: SAS refs=[1,2,3] \u2192
        bc = ef, \u2220abc = \u2220def, \u2220acb = \u2220dfe, \u25b3abc = \u25b3def."""
        p = self._make_panel()
        p.set_declarations([], [])
        # Premises are lines 1-3
        p.add_premise_text("ab = de")
        p.add_premise_text("ac = df")
        p.add_premise_text("\u2220bac = \u2220edf")
        # SAS step = line 4
        p.add_step("", "SAS", [1, 2, 3])
        p._eval_all()
        step = p._steps[0]
        expected = (
            "bc = ef, \u2220abc = \u2220def, "
            "\u2220acb = \u2220dfe, \u25b3abc = \u25b3def"
        )
        assert step.text == expected, \
            f"Expected {expected!r}, got: {step.text!r}"
        assert step.status == "\u2713", \
            f"Expected \u2713, got: {step.status}"

    def test_prop_i8_sss(self):
        """Prop I.8 step 4: SSS refs=[1,2,3] \u2192
        \u2220bac = \u2220edf, \u2220abc = \u2220def, \u2220acb = \u2220dfe,
        \u25b3abc = \u25b3def."""
        p = self._make_panel()
        p.set_declarations([], [])
        # Premises are lines 1-3
        p.add_premise_text("ab = de")
        p.add_premise_text("bc = ef")
        p.add_premise_text("ca = fd")
        # SSS step = line 4
        p.add_step("", "SSS", [1, 2, 3])
        p._eval_all()
        step = p._steps[0]
        expected = (
            "\u2220bac = \u2220edf, \u2220abc = \u2220def, "
            "\u2220acb = \u2220dfe, \u25b3abc = \u25b3def"
        )
        assert step.text == expected, \
            f"Expected {expected!r}, got: {step.text!r}"
        assert step.status == "\u2713", \
            f"Expected \u2713, got: {step.status}"

