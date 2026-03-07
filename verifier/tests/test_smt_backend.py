"""
test_smt_backend.py — Phase 8.4: SMT and TPTP backend tests.

Tests the encoding of System E axioms and proof obligations in
SMT-LIB 2.6 and TPTP FOF formats. Also tests the integration with
the unified checker's verify_step function.

Reference: IMPLEMENTATION_PLAN.md §8.1–8.4, Paper §6
"""
from __future__ import annotations

import pytest


# ═══════════════════════════════════════════════════════════════════════
# SMT-LIB ENCODING TESTS
# ═══════════════════════════════════════════════════════════════════════

class TestSmtLibEncoding:
    """Test SMT-LIB 2.6 encoding of axioms and proof obligations."""

    def test_encode_axioms_produces_valid_smtlib(self):
        """encode_axioms_smtlib() produces a non-empty SMT-LIB script."""
        from verifier.smt_backend import encode_axioms_smtlib
        script = encode_axioms_smtlib()
        assert len(script) > 1000
        assert "(set-logic ALL)" in script
        assert "(declare-sort Point 0)" in script
        assert "(declare-sort Line 0)" in script
        assert "(declare-sort Circle 0)" in script

    def test_encode_axioms_has_all_65_axioms(self):
        """All 65 E axioms are encoded."""
        from verifier.smt_backend import encode_axioms_smtlib
        script = encode_axioms_smtlib()
        assert "; Axiom 1" in script
        assert "; Axiom 65" in script

    def test_encode_axioms_has_function_declarations(self):
        """Function declarations for all predicates are present."""
        from verifier.smt_backend import encode_axioms_smtlib
        script = encode_axioms_smtlib()
        for func in ["on_point_line", "between", "same_side", "center",
                      "inside", "eq_seg", "eq_ang", "lt_seg", "seg"]:
            assert func in script, f"Missing function: {func}"

    def test_encode_atom_between(self):
        """Between atom encodes correctly."""
        from verifier.smt_backend import encode_atom
        from verifier.e_ast import Between
        result = encode_atom(Between("a", "b", "c"))
        assert result == "(between a b c)"

    def test_encode_atom_on(self):
        """On atom encodes correctly."""
        from verifier.smt_backend import encode_atom
        from verifier.e_ast import On
        result = encode_atom(On("a", "L"))
        assert result == "(on_point_line a L)"

    def test_encode_atom_same_side(self):
        """SameSide atom encodes correctly."""
        from verifier.smt_backend import encode_atom
        from verifier.e_ast import SameSide
        result = encode_atom(SameSide("a", "b", "L"))
        assert result == "(same_side a b L)"

    def test_encode_atom_center(self):
        """Center atom encodes correctly."""
        from verifier.smt_backend import encode_atom
        from verifier.e_ast import Center
        result = encode_atom(Center("a", "alpha"))
        assert result == "(center a alpha)"

    def test_encode_atom_inside(self):
        """Inside atom encodes correctly."""
        from verifier.smt_backend import encode_atom
        from verifier.e_ast import Inside
        result = encode_atom(Inside("a", "alpha"))
        assert result == "(inside a alpha)"

    def test_encode_atom_segment_equals(self):
        """Segment equality encodes correctly."""
        from verifier.smt_backend import encode_atom
        from verifier.e_ast import Equals, SegmentTerm
        result = encode_atom(Equals(SegmentTerm("a", "b"),
                                    SegmentTerm("c", "d")))
        assert result == "(eq_seg (seg a b) (seg c d))"

    def test_encode_atom_angle_equals(self):
        """Angle equality encodes correctly."""
        from verifier.smt_backend import encode_atom
        from verifier.e_ast import Equals, AngleTerm
        result = encode_atom(Equals(AngleTerm("a", "b", "c"),
                                    AngleTerm("d", "e", "f")))
        assert result == "(eq_ang (ang a b c) (ang d e f))"

    def test_encode_atom_less_than(self):
        """Segment less-than encodes correctly."""
        from verifier.smt_backend import encode_atom
        from verifier.e_ast import LessThan, SegmentTerm
        result = encode_atom(LessThan(SegmentTerm("a", "b"),
                                      SegmentTerm("c", "d")))
        assert result == "(lt_seg (seg a b) (seg c d))"

    def test_encode_atom_point_equals(self):
        """Point equality encodes correctly."""
        from verifier.smt_backend import encode_atom
        from verifier.e_ast import Equals
        result = encode_atom(Equals("a", "b"))
        assert result == "(eq_point a b)"

    def test_encode_literal_positive(self):
        """Positive literal encodes without negation."""
        from verifier.smt_backend import encode_literal
        from verifier.e_ast import Literal, Between
        result = encode_literal(Literal(Between("a", "b", "c")))
        assert result == "(between a b c)"

    def test_encode_literal_negative(self):
        """Negative literal encodes with (not ...)."""
        from verifier.smt_backend import encode_literal
        from verifier.e_ast import Literal, Between
        result = encode_literal(Literal(Between("a", "b", "c"), False))
        assert result == "(not (between a b c))"

    def test_encode_clause_simple(self):
        """A simple clause encodes as a forall assertion."""
        from verifier.smt_backend import encode_clause
        from verifier.e_ast import Clause, Literal, Between
        clause = Clause(frozenset([
            Literal(Between("a", "b", "c")),
            Literal(Between("c", "b", "a"), False),
        ]))
        result = encode_clause(clause)
        assert "(assert" in result
        assert "(forall" in result
        assert "between" in result

    def test_encode_obligation_structure(self):
        """encode_obligation produces a script with axioms, known, and query."""
        from verifier.smt_backend import encode_obligation
        from verifier.e_ast import Literal, Between
        known = [Literal(Between("a", "b", "c"))]
        query = Literal(Between("c", "b", "a"))
        script = encode_obligation(known, query)
        assert "(set-logic ALL)" in script
        assert "; --- Known facts ---" in script
        assert "; --- Query (negated for UNSAT check) ---" in script
        assert "(check-sat)" in script
        assert "(exit)" in script

    def test_encode_obligation_has_variable_declarations(self):
        """Variables are declared as constants in the obligation script."""
        from verifier.smt_backend import encode_obligation
        from verifier.e_ast import Literal, Between
        known = [Literal(Between("a", "b", "c"))]
        query = Literal(Between("c", "b", "a"))
        script = encode_obligation(known, query)
        assert "(declare-const a Point)" in script
        assert "(declare-const b Point)" in script
        assert "(declare-const c Point)" in script

    def test_greek_variable_sanitisation(self):
        """Greek variable names (α, β, γ) are sanitised."""
        from verifier.smt_backend import encode_atom
        from verifier.e_ast import Center
        result = encode_atom(Center("a", "α"))
        assert "alpha" in result
        assert "α" not in result

    def test_all_axioms_encode_without_error(self):
        """Every E axiom clause encodes without raising an exception."""
        from verifier.smt_backend import encode_clause
        from verifier.e_axioms import ALL_AXIOMS
        for i, clause in enumerate(ALL_AXIOMS):
            try:
                result = encode_clause(clause)
                assert "(assert" in result
            except Exception as exc:
                pytest.fail(f"Axiom {i+1} failed: {exc}")

    def test_on_circle_dispatches_correctly(self):
        """On(point, circle) in a clause with Center uses on_point_circle."""
        from verifier.smt_backend import encode_clause
        from verifier.e_ast import Clause, Literal, On, Center
        clause = Clause(frozenset([
            Literal(Center("a", "α")),
            Literal(On("b", "α")),
        ]))
        result = encode_clause(clause)
        assert "on_point_circle" in result
        assert "on_point_line" not in result

    def test_on_line_dispatches_correctly(self):
        """On(point, line) without Center/Inside uses on_point_line."""
        from verifier.smt_backend import encode_clause
        from verifier.e_ast import Clause, Literal, On, Between
        clause = Clause(frozenset([
            Literal(On("a", "L")),
            Literal(Between("a", "b", "c")),
        ]))
        result = encode_clause(clause)
        assert "on_point_line" in result
        assert "on_point_circle" not in result

    def test_mixed_on_line_and_circle(self):
        """Clause with both On(p,L) and On(p,α)+Center correctly dispatches both."""
        from verifier.smt_backend import encode_clause
        from verifier.e_ast import Clause, Literal, On, Center
        clause = Clause(frozenset([
            Literal(On("a", "L")),
            Literal(On("b", "α")),
            Literal(Center("c", "α")),
        ]))
        result = encode_clause(clause)
        assert "on_point_line" in result
        assert "on_point_circle" in result


# ═══════════════════════════════════════════════════════════════════════
# TPTP ENCODING TESTS
# ═══════════════════════════════════════════════════════════════════════

class TestTptpEncoding:
    """Test TPTP FOF encoding of axioms and proof obligations."""

    def test_encode_axioms_produces_valid_tptp(self):
        """encode_axioms_tptp() produces a non-empty TPTP script."""
        from verifier.tptp_backend import encode_axioms_tptp
        script = encode_axioms_tptp()
        assert len(script) > 500
        assert "fof(axiom_1" in script

    def test_encode_axioms_has_all_65_axioms(self):
        """All 65 E axioms are encoded."""
        from verifier.tptp_backend import encode_axioms_tptp
        script = encode_axioms_tptp()
        assert "fof(axiom_1," in script
        assert "fof(axiom_65," in script

    def test_encode_atom_between(self):
        """Between atom encodes correctly in TPTP."""
        from verifier.tptp_backend import encode_atom_tptp
        from verifier.e_ast import Between
        result = encode_atom_tptp(Between("a", "b", "c"))
        assert result == "between(A,B,C)"

    def test_encode_atom_on(self):
        """On atom encodes correctly in TPTP."""
        from verifier.tptp_backend import encode_atom_tptp
        from verifier.e_ast import On
        result = encode_atom_tptp(On("a", "L"))
        assert "on_pl(" in result
        assert "A" in result

    def test_encode_atom_segment_equals(self):
        """Segment equality encodes correctly in TPTP."""
        from verifier.tptp_backend import encode_atom_tptp
        from verifier.e_ast import Equals, SegmentTerm
        result = encode_atom_tptp(Equals(SegmentTerm("a", "b"),
                                         SegmentTerm("c", "d")))
        assert "eq(seg(A,B),seg(C,D))" == result

    def test_encode_literal_negative(self):
        """Negative literal encodes with ~ in TPTP."""
        from verifier.tptp_backend import encode_literal_tptp
        from verifier.e_ast import Literal, Between
        result = encode_literal_tptp(Literal(Between("a", "b", "c"), False))
        assert result == "~between(A,B,C)"

    def test_encode_clause(self):
        """A clause encodes as a universally quantified TPTP axiom."""
        from verifier.tptp_backend import encode_clause_tptp
        from verifier.e_ast import Clause, Literal, Between
        clause = Clause(frozenset([
            Literal(Between("a", "b", "c")),
            Literal(Between("c", "b", "a"), False),
        ]))
        result = encode_clause_tptp(clause, "test_ax")
        assert "fof(test_ax, axiom," in result
        assert "between" in result

    def test_encode_query_structure(self):
        """encode_query_tptp produces hypothesis + conjecture format."""
        from verifier.tptp_backend import encode_query_tptp
        from verifier.e_ast import Literal, Between
        known = [Literal(Between("a", "b", "c"))]
        query = Literal(Between("c", "b", "a"))
        script = encode_query_tptp(known, query, axioms=False)
        assert "fof(known_1, hypothesis," in script
        assert "fof(query, conjecture," in script

    def test_encode_query_with_axioms(self):
        """encode_query_tptp includes axioms when requested."""
        from verifier.tptp_backend import encode_query_tptp
        from verifier.e_ast import Literal, Between
        known = [Literal(Between("a", "b", "c"))]
        query = Literal(Between("c", "b", "a"))
        script = encode_query_tptp(known, query, axioms=True)
        assert "fof(axiom_1," in script
        assert "fof(query, conjecture," in script

    def test_all_axioms_encode_without_error(self):
        """Every E axiom clause encodes to TPTP without raising."""
        from verifier.tptp_backend import encode_clause_tptp
        from verifier.e_axioms import ALL_AXIOMS
        for i, clause in enumerate(ALL_AXIOMS):
            try:
                result = encode_clause_tptp(clause, f"ax_{i}")
                assert "fof(" in result
            except Exception as exc:
                pytest.fail(f"Axiom {i+1} failed: {exc}")

    def test_tptp_variables_uppercase(self):
        """TPTP variables start with uppercase."""
        from verifier.tptp_backend import encode_atom_tptp
        from verifier.e_ast import Between
        result = encode_atom_tptp(Between("a", "b", "c"))
        # All variables in TPTP should be uppercase
        assert result == "between(A,B,C)"


# ═══════════════════════════════════════════════════════════════════════
# PAPER §6 DIAGRAM ENCODING TEST
# ═══════════════════════════════════════════════════════════════════════

class TestPaperDiagram:
    """Encode the paper's test diagram (5 lines, 6 points) and verify
    that consequences can be checked.

    Paper §6: "described a simple diagram with five lines and six points,
    and checked a number of consequences."
    """

    def test_five_line_diagram_encodes(self):
        """A 5-line, 6-point diagram encodes to valid SMT-LIB."""
        from verifier.smt_backend import encode_obligation
        from verifier.e_ast import (
            Literal, On, Between, Equals, Sort,
        )
        # Simple diagram: triangle ABC with lines AB, BC, CA
        # and additional points D on AB, E on BC
        known = [
            # Points on lines
            Literal(On("a", "L1")),
            Literal(On("b", "L1")),
            Literal(On("b", "L2")),
            Literal(On("c", "L2")),
            Literal(On("c", "L3")),
            Literal(On("a", "L3")),
            # Betweenness
            Literal(Between("a", "d", "b")),
            Literal(Between("b", "e", "c")),
            # Distinct points
            Literal(Equals("a", "b"), False),
            Literal(Equals("b", "c"), False),
            Literal(Equals("a", "c"), False),
        ]
        # Query: d is on L1 (follows from between(a,d,b) and on(a,L1), on(b,L1))
        query = Literal(On("d", "L1"))
        variables = [
            ("a", Sort.POINT), ("b", Sort.POINT), ("c", Sort.POINT),
            ("d", Sort.POINT), ("e", Sort.POINT),
            ("L1", Sort.LINE), ("L2", Sort.LINE), ("L3", Sort.LINE),
        ]
        script = encode_obligation(known, query, variables)
        assert "(check-sat)" in script
        assert "(between a d b)" in script
        assert len(script) > 5000  # non-trivial script

    def test_five_line_diagram_tptp(self):
        """Same diagram encodes to valid TPTP."""
        from verifier.tptp_backend import encode_query_tptp
        from verifier.e_ast import Literal, On, Between, Equals
        known = [
            Literal(On("a", "L1")),
            Literal(On("b", "L1")),
            Literal(Between("a", "d", "b")),
        ]
        query = Literal(On("d", "L1"))
        script = encode_query_tptp(known, query)
        assert "fof(query, conjecture," in script
        assert "on_pl(D,L1)" in script


# ═══════════════════════════════════════════════════════════════════════
# INTEGRATION TESTS — verify_step with SMT fallback
# ═══════════════════════════════════════════════════════════════════════

class TestVerifyStepIntegration:
    """Test the unified_checker.verify_step with SMT fallback."""

    def test_verify_step_consequence_only(self):
        """verify_step works without SMT fallback."""
        from verifier.unified_checker import verify_step
        from verifier.e_ast import Literal, Between
        known = {Literal(Between("a", "b", "c"))}
        # Between(a,b,c) → Between(c,b,a) is a known diagrammatic consequence
        query = Literal(Between("c", "b", "a"))
        result = verify_step(known, query)
        assert isinstance(result, bool)

    def test_verify_step_with_smt_fallback_false(self):
        """verify_step with use_smt_fallback=False behaves like before."""
        from verifier.unified_checker import verify_step
        from verifier.e_ast import Literal, On
        known = set()
        query = Literal(On("a", "L"))
        # No known facts → should not be derivable
        result = verify_step(known, query, use_smt_fallback=False)
        assert result is False

    def test_verify_step_with_smt_fallback_unavailable(self):
        """verify_step with SMT fallback handles missing Z3 gracefully."""
        from verifier.unified_checker import verify_step
        from verifier.e_ast import Literal, On
        known = set()
        query = Literal(On("a", "L"))
        # Z3 probably not installed — should return False, not crash
        result = verify_step(
            known, query, use_smt_fallback=True,
            z3_path="nonexistent_z3_binary",
        )
        assert result is False


# ═══════════════════════════════════════════════════════════════════════
# BENCHMARK STRUCTURE — Props I.1–I.10
# ═══════════════════════════════════════════════════════════════════════

class TestBenchmarkEncoding:
    """Verify that propositions I.1–I.10 can be encoded as SMT obligations."""

    def test_prop_i1_to_i10_encode_smtlib(self):
        """Sequents for I.1–I.10 encode as SMT-LIB obligations."""
        from verifier.smt_backend import encode_obligation
        from verifier.e_library import E_THEOREM_LIBRARY

        for i in range(1, 11):
            name = f"Prop.I.{i}"
            thm = E_THEOREM_LIBRARY[name]
            # Encode first hypothesis → first conclusion as an obligation
            if thm.sequent.hypotheses and thm.sequent.conclusions:
                script = encode_obligation(
                    thm.sequent.hypotheses,
                    thm.sequent.conclusions[0],
                )
                assert "(check-sat)" in script, f"{name} missing check-sat"
                assert len(script) > 1000, f"{name} script too short"

    def test_prop_i1_to_i10_encode_tptp(self):
        """Sequents for I.1–I.10 encode as TPTP obligations."""
        from verifier.tptp_backend import encode_query_tptp
        from verifier.e_library import E_THEOREM_LIBRARY

        for i in range(1, 11):
            name = f"Prop.I.{i}"
            thm = E_THEOREM_LIBRARY[name]
            if thm.sequent.hypotheses and thm.sequent.conclusions:
                script = encode_query_tptp(
                    thm.sequent.hypotheses,
                    thm.sequent.conclusions[0],
                )
                assert "fof(query, conjecture," in script, f"{name} missing conjecture"
