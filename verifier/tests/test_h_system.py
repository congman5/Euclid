"""
Tests for System H (Hilbert's axiom system).

Tests cover:
  - AST types (h_ast.py)
  - Axiom clause counts (h_axioms.py)
  - Consequence engine (h_consequence.py)
  - Bridge translations (h_bridge.py)
  - Theorem library (h_library.py)
  - Checker basics (h_checker.py)
"""
import pytest
from verifier.h_ast import (
    HSort,
    IncidL, IncidP, BetH, CongH, CongaH, EqL, EqP, EqPt,
    ColH, Cut, OutH, Disjoint, SameSideH, SameSidePrime, Para, IncidLP,
    HLiteral, HClause, HSequent, HStepKind,
    h_atom_vars, h_literal_vars, h_substitute_literal, h_substitute_atom,
)


# ═══════════════════════════════════════════════════════════════════════
# AST unit tests
# ═══════════════════════════════════════════════════════════════════════

class TestHSorts:
    def test_sorts_exist(self):
        assert HSort.POINT is not None
        assert HSort.LINE is not None
        assert HSort.PLANE is not None


class TestHAtoms:
    def test_incidl_repr(self):
        assert repr(IncidL("A", "l")) == "IncidL(A, l)"

    def test_incidp_repr(self):
        assert repr(IncidP("A", "p")) == "IncidP(A, p)"

    def test_beth_repr(self):
        assert repr(BetH("A", "B", "C")) == "BetH(A, B, C)"

    def test_congh_repr(self):
        assert repr(CongH("A", "B", "C", "D")) == "CongH(A, B, C, D)"

    def test_congah_repr(self):
        r = repr(CongaH("A", "B", "C", "D", "E", "F"))
        assert r == "CongaH(A, B, C, D, E, F)"

    def test_eql_repr(self):
        assert repr(EqL("l", "m")) == "EqL(l, m)"

    def test_eqp_repr(self):
        assert repr(EqP("p", "q")) == "EqP(p, q)"

    def test_eqpt_repr(self):
        assert repr(EqPt("A", "B")) == "A = B"

    def test_colh_repr(self):
        assert repr(ColH("A", "B", "C")) == "ColH(A, B, C)"

    def test_cut_repr(self):
        assert repr(Cut("l", "A", "B")) == "cut(l, A, B)"

    def test_outh_repr(self):
        assert repr(OutH("P", "A", "B")) == "outH(P, A, B)"

    def test_disjoint_repr(self):
        assert repr(Disjoint("A", "B", "C", "D")) == "disjoint(A, B, C, D)"

    def test_same_side_repr(self):
        assert repr(SameSideH("A", "B", "l")) == "same_side(A, B, l)"

    def test_same_side_prime_repr(self):
        r = repr(SameSidePrime("A", "B", "X", "Y"))
        assert r == "same_side'(A, B, X, Y)"

    def test_para_repr(self):
        assert repr(Para("l", "m")) == "Para(l, m)"


class TestHLiterals:
    def test_positive(self):
        lit = HLiteral(IncidL("A", "l"))
        assert lit.is_positive
        assert not lit.is_negative
        assert lit.is_incidence

    def test_negative(self):
        lit = HLiteral(BetH("A", "B", "C"), polarity=False)
        assert not lit.is_positive
        assert lit.is_negative
        assert lit.is_order

    def test_negated(self):
        lit = HLiteral(IncidL("A", "l"))
        neg = lit.negated()
        assert neg.is_negative
        assert neg.atom == lit.atom
        assert neg.negated() == lit

    def test_congruence_classification(self):
        lit = HLiteral(CongH("A", "B", "C", "D"))
        assert lit.is_congruence

    def test_repr_positive(self):
        lit = HLiteral(IncidL("A", "l"))
        assert repr(lit) == "IncidL(A, l)"

    def test_repr_negative(self):
        lit = HLiteral(IncidL("A", "l"), polarity=False)
        assert repr(lit) == "\u00ac(IncidL(A, l))"


# ═══════════════════════════════════════════════════════════════════════
# Utility function tests
# ═══════════════════════════════════════════════════════════════════════

class TestHAtomVars:
    def test_incidl_vars(self):
        assert h_atom_vars(IncidL("A", "l")) == {"A", "l"}

    def test_beth_vars(self):
        assert h_atom_vars(BetH("A", "B", "C")) == {"A", "B", "C"}

    def test_congh_vars(self):
        assert h_atom_vars(CongH("A", "B", "C", "D")) == {"A", "B", "C", "D"}

    def test_congah_vars(self):
        v = h_atom_vars(CongaH("A", "B", "C", "D", "E", "F"))
        assert v == {"A", "B", "C", "D", "E", "F"}

    def test_colh_vars(self):
        assert h_atom_vars(ColH("A", "B", "C")) == {"A", "B", "C"}

    def test_cut_vars(self):
        assert h_atom_vars(Cut("l", "A", "B")) == {"l", "A", "B"}

    def test_para_vars(self):
        assert h_atom_vars(Para("l", "m")) == {"l", "m"}


class TestHSubstitution:
    def test_substitute_incidl(self):
        atom = IncidL("A", "l")
        result = h_substitute_atom(atom, {"A": "X", "l": "m"})
        assert result == IncidL("X", "m")

    def test_substitute_beth(self):
        atom = BetH("A", "B", "C")
        result = h_substitute_atom(atom, {"B": "X"})
        assert result == BetH("A", "X", "C")

    def test_substitute_literal(self):
        lit = HLiteral(IncidL("A", "l"), polarity=False)
        result = h_substitute_literal(lit, {"A": "B"})
        assert result == HLiteral(IncidL("B", "l"), polarity=False)


# ═══════════════════════════════════════════════════════════════════════
# Axiom clause count tests
# ═══════════════════════════════════════════════════════════════════════

class TestHAxiomCounts:
    def test_incidence_axiom_count(self):
        from verifier.h_axioms import ALL_INCIDENCE_AXIOMS
        assert len(ALL_INCIDENCE_AXIOMS) > 0
        # 10 incidence + 4 collinearity = 14
        # (LOWER_DIM_AXIOMS excluded: axiom constants, not schema variables)
        assert len(ALL_INCIDENCE_AXIOMS) == 14

    def test_order_axiom_count(self):
        from verifier.h_axioms import ALL_ORDER_AXIOMS
        assert len(ALL_ORDER_AXIOMS) > 0
        # 6 between + 3 cut + 2 pasch = 11
        assert len(ALL_ORDER_AXIOMS) == 11

    def test_congruence_axiom_count(self):
        from verifier.h_axioms import ALL_CONGRUENCE_AXIOMS
        assert len(ALL_CONGRUENCE_AXIOMS) > 0
        # 5 segment + 1 addition + 4 angle + 1 SAS + 2 same_side = 13
        assert len(ALL_CONGRUENCE_AXIOMS) == 13

    def test_parallel_axiom_count(self):
        from verifier.h_axioms import PARALLEL_AXIOMS
        assert len(PARALLEL_AXIOMS) == 1

    def test_total_axiom_count(self):
        from verifier.h_axioms import ALL_H_AXIOMS
        # 14 + 11 + 13 + 1 = 39
        assert len(ALL_H_AXIOMS) == 39


# ═══════════════════════════════════════════════════════════════════════
# Consequence engine tests
# ═══════════════════════════════════════════════════════════════════════

class TestHConsequenceEngine:
    def test_engine_creation(self):
        from verifier.h_consequence import HConsequenceEngine
        engine = HConsequenceEngine()
        assert engine.axioms is not None
        assert len(engine.axioms) > 0

    def test_between_comm(self):
        """BetH(A,B,C) should give BetH(C,B,A) as a consequence."""
        from verifier.h_consequence import HConsequenceEngine
        engine = HConsequenceEngine()
        known = {HLiteral(BetH("A", "B", "C"))}
        variables = {"A": HSort.POINT, "B": HSort.POINT, "C": HSort.POINT}
        result = engine.direct_consequences(known, variables)
        assert HLiteral(BetH("C", "B", "A")) in result

    def test_between_diff(self):
        """BetH(A,B,C) should give A ≠ C."""
        from verifier.h_consequence import HConsequenceEngine
        engine = HConsequenceEngine()
        known = {HLiteral(BetH("A", "B", "C"))}
        variables = {"A": HSort.POINT, "B": HSort.POINT, "C": HSort.POINT}
        result = engine.direct_consequences(known, variables)
        assert HLiteral(EqPt("A", "C"), polarity=False) in result

    def test_between_col(self):
        """BetH(A,B,C) should give ColH(A,B,C)."""
        from verifier.h_consequence import HConsequenceEngine
        engine = HConsequenceEngine()
        known = {HLiteral(BetH("A", "B", "C"))}
        variables = {"A": HSort.POINT, "B": HSort.POINT, "C": HSort.POINT}
        result = engine.direct_consequences(known, variables)
        assert HLiteral(ColH("A", "B", "C")) in result

    def test_between_only_one(self):
        """BetH(A,B,C) should give ¬BetH(B,C,A)."""
        from verifier.h_consequence import HConsequenceEngine
        engine = HConsequenceEngine()
        known = {HLiteral(BetH("A", "B", "C"))}
        variables = {"A": HSort.POINT, "B": HSort.POINT, "C": HSort.POINT}
        result = engine.direct_consequences(known, variables)
        assert HLiteral(BetH("B", "C", "A"), polarity=False) in result

    def test_cong_symmetry(self):
        """CongH(A,B,C,D) should give CongH(C,D,A,B)."""
        from verifier.h_consequence import HConsequenceEngine
        engine = HConsequenceEngine()
        known = {HLiteral(CongH("A", "B", "C", "D"))}
        variables = {
            "A": HSort.POINT, "B": HSort.POINT,
            "C": HSort.POINT, "D": HSort.POINT,
        }
        result = engine.direct_consequences(known, variables)
        assert HLiteral(CongH("C", "D", "A", "B")) in result

    def test_cong_permr(self):
        """CongH(A,B,C,D) should give CongH(A,B,D,C)."""
        from verifier.h_consequence import HConsequenceEngine
        engine = HConsequenceEngine()
        known = {HLiteral(CongH("A", "B", "C", "D"))}
        variables = {
            "A": HSort.POINT, "B": HSort.POINT,
            "C": HSort.POINT, "D": HSort.POINT,
        }
        result = engine.direct_consequences(known, variables)
        assert HLiteral(CongH("A", "B", "D", "C")) in result

    def test_incidence_line_uniqueness(self):
        """Two distinct points on two lines implies lines are equal."""
        from verifier.h_consequence import HConsequenceEngine
        engine = HConsequenceEngine()
        known = {
            HLiteral(EqPt("A", "B"), polarity=False),  # A ≠ B
            HLiteral(IncidL("A", "l")),
            HLiteral(IncidL("B", "l")),
            HLiteral(IncidL("A", "m")),
            HLiteral(IncidL("B", "m")),
        }
        variables = {
            "A": HSort.POINT, "B": HSort.POINT,
            "l": HSort.LINE, "m": HSort.LINE,
        }
        result = engine.direct_consequences(known, variables)
        assert HLiteral(EqL("l", "m")) in result

    def test_is_consequence_api(self):
        from verifier.h_consequence import is_h_consequence
        known = {HLiteral(BetH("A", "B", "C"))}
        assert is_h_consequence(known, HLiteral(BetH("C", "B", "A")))

    def test_collinearity_from_incidence(self):
        """Three points on the same line are collinear."""
        from verifier.h_consequence import HConsequenceEngine
        engine = HConsequenceEngine()
        known = {
            HLiteral(IncidL("A", "l")),
            HLiteral(IncidL("B", "l")),
            HLiteral(IncidL("C", "l")),
        }
        variables = {
            "A": HSort.POINT, "B": HSort.POINT,
            "C": HSort.POINT, "l": HSort.LINE,
        }
        result = engine.direct_consequences(known, variables)
        assert HLiteral(ColH("A", "B", "C")) in result


# ═══════════════════════════════════════════════════════════════════════
# Bridge translation tests
# ═══════════════════════════════════════════════════════════════════════

class TestHBridge:
    def test_e_on_to_h_incidl(self):
        from verifier.e_ast import On, Literal as ELiteral
        from verifier.h_bridge import e_literal_to_h
        e_lit = ELiteral(On("a", "L"))
        h_lit = e_literal_to_h(e_lit)
        assert h_lit is not None
        assert h_lit.atom == IncidL("a", "L")
        assert h_lit.is_positive

    def test_e_between_to_h_beth(self):
        from verifier.e_ast import Between, Literal as ELiteral
        from verifier.h_bridge import e_literal_to_h
        e_lit = ELiteral(Between("a", "b", "c"))
        h_lit = e_literal_to_h(e_lit)
        assert h_lit is not None
        assert h_lit.atom == BetH("a", "b", "c")

    def test_e_segment_eq_to_h_congh(self):
        from verifier.e_ast import Equals as EEquals, SegmentTerm
        from verifier.e_ast import Literal as ELiteral
        from verifier.h_bridge import e_literal_to_h
        e_lit = ELiteral(EEquals(SegmentTerm("a", "b"), SegmentTerm("c", "d")))
        h_lit = e_literal_to_h(e_lit)
        assert h_lit is not None
        assert h_lit.atom == CongH("a", "b", "c", "d")

    def test_e_angle_eq_to_h_congah(self):
        from verifier.e_ast import Equals as EEquals, AngleTerm
        from verifier.e_ast import Literal as ELiteral
        from verifier.h_bridge import e_literal_to_h
        e_lit = ELiteral(EEquals(AngleTerm("a", "b", "c"),
                                  AngleTerm("d", "e", "f")))
        h_lit = e_literal_to_h(e_lit)
        assert h_lit is not None
        assert h_lit.atom == CongaH("a", "b", "c", "d", "e", "f")

    def test_e_circle_returns_none(self):
        from verifier.e_ast import Center, Literal as ELiteral
        from verifier.h_bridge import e_literal_to_h
        e_lit = ELiteral(Center("a", "\u03b1"))
        h_lit = e_literal_to_h(e_lit)
        assert h_lit is None

    def test_h_incidl_to_e_on(self):
        from verifier.h_bridge import h_literal_to_e
        from verifier.e_ast import On
        h_lit = HLiteral(IncidL("a", "L"))
        e_lit = h_literal_to_e(h_lit)
        assert e_lit is not None
        assert e_lit.atom == On("a", "L")

    def test_h_congh_to_e_segment_eq(self):
        from verifier.h_bridge import h_literal_to_e
        from verifier.e_ast import Equals as EEquals, SegmentTerm
        h_lit = HLiteral(CongH("a", "b", "c", "d"))
        e_lit = h_literal_to_e(h_lit)
        assert e_lit is not None
        assert e_lit.atom == EEquals(SegmentTerm("a", "b"),
                                     SegmentTerm("c", "d"))

    def test_roundtrip_on(self):
        """E → H → E should preserve on() literals."""
        from verifier.e_ast import On, Literal as ELiteral
        from verifier.h_bridge import e_literal_to_h, h_literal_to_e
        original = ELiteral(On("a", "L"))
        h = e_literal_to_h(original)
        back = h_literal_to_e(h)
        assert back == original


# ═══════════════════════════════════════════════════════════════════════
# Library tests
# ═══════════════════════════════════════════════════════════════════════

class TestHLibrary:
    def test_library_has_theorems(self):
        from verifier.h_library import H_THEOREM_LIBRARY
        assert len(H_THEOREM_LIBRARY) >= 5

    def test_prop_i1_structure(self):
        from verifier.h_library import PROP_I_1
        assert PROP_I_1.name == "Prop.I.1"
        assert len(PROP_I_1.sequent.hypotheses) == 1
        assert len(PROP_I_1.sequent.exists_vars) == 1
        assert PROP_I_1.sequent.exists_vars[0][1] == HSort.POINT
        assert len(PROP_I_1.sequent.conclusions) == 5

    def test_prop_i4_structure(self):
        from verifier.h_library import PROP_I_4
        assert PROP_I_4.name == "Prop.I.4"
        assert len(PROP_I_4.sequent.hypotheses) == 5
        assert len(PROP_I_4.sequent.exists_vars) == 0
        assert len(PROP_I_4.sequent.conclusions) == 2

    def test_get_theorems_up_to(self):
        from verifier.h_library import get_h_theorems_up_to
        before_i4 = get_h_theorems_up_to("Prop.I.4")
        assert "Prop.I.1" in before_i4
        assert "Prop.I.2" in before_i4
        assert "Prop.I.3" in before_i4
        assert "Prop.I.4" not in before_i4

    def test_get_theorems_up_to_first(self):
        from verifier.h_library import get_h_theorems_up_to
        before_i1 = get_h_theorems_up_to("Prop.I.1")
        assert len(before_i1) == 0


# ═══════════════════════════════════════════════════════════════════════
# Checker basic tests
# ═══════════════════════════════════════════════════════════════════════

class TestHChecker:
    def test_checker_creation(self):
        from verifier.h_checker import HChecker
        checker = HChecker()
        assert checker is not None

    def test_empty_proof_valid(self):
        from verifier.h_checker import HChecker
        from verifier.h_ast import HProof
        checker = HChecker()
        proof = HProof(name="empty")
        result = checker.check_proof(proof)
        assert result.valid

    def test_check_with_system_h_api(self):
        from verifier.h_bridge import check_with_system_h
        result = check_with_system_h({})
        assert result["valid"] is True
        assert result["system"] == "H"
