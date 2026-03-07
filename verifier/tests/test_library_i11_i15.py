"""
Tests for Props I.6, I.7, I.9, I.11–I.15 in both System E and System H
libraries, and proof encodings in e_proofs.

Covers Phase 6.1 of the implementation plan.
"""
import pytest
from verifier.e_ast import (
    Sort, Literal, Sequent,
    On, SameSide, Between, Equals, LessThan,
    SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag,
    StepKind,
)
from verifier.h_ast import HSort, HLiteral, HSequent


# ═══════════════════════════════════════════════════════════════════════
# System E library tests — new propositions
# ═══════════════════════════════════════════════════════════════════════

class TestELibraryNewProps:
    """Tests for Props I.6, I.7, I.9, I.11–I.15 in e_library."""

    def test_library_has_at_least_15_theorems(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        assert len(E_THEOREM_LIBRARY) >= 15

    def test_ordered_names_complete(self):
        from verifier.e_library import get_theorems_up_to
        # Before I.15, should have I.1–I.14
        before_i15 = get_theorems_up_to("Prop.I.15")
        assert len(before_i15) == 14
        assert "Prop.I.15" not in before_i15

    def test_prop_i6_sequent(self):
        from verifier.e_library import PROP_I_6
        seq = PROP_I_6.sequent
        # Hypotheses: ∠abc = ∠acb, a≠b, a≠c, b≠c
        assert len(seq.hypotheses) == 4
        # No existential
        assert len(seq.exists_vars) == 0
        # Conclusion: ab = ac
        assert len(seq.conclusions) == 1
        assert seq.conclusions[0].is_positive

    def test_prop_i7_sequent(self):
        from verifier.e_library import PROP_I_7
        seq = PROP_I_7.sequent
        # Hypotheses: on(b,L), on(c,L), b≠c, same-side(a,d,L), bd=ba, cd=ca
        assert len(seq.hypotheses) == 6
        assert len(seq.exists_vars) == 0
        # Conclusion: d = a
        assert len(seq.conclusions) == 1

    def test_prop_i9_sequent(self):
        from verifier.e_library import PROP_I_9
        seq = PROP_I_9.sequent
        # Hypotheses: distinctness + incidence + same-side conditions
        assert len(seq.hypotheses) >= 5
        # Existential: ∃e
        assert len(seq.exists_vars) == 1
        assert seq.exists_vars[0][1] == Sort.POINT
        # Conclusion: angle bisection + side conditions
        assert len(seq.conclusions) >= 2

    def test_prop_i11_sequent(self):
        from verifier.e_library import PROP_I_11
        seq = PROP_I_11.sequent
        # Hypotheses: on(a,L), on(b,L), a≠b
        assert len(seq.hypotheses) == 3
        # ∃f such that ∠baf = right-angle
        assert len(seq.exists_vars) == 1
        assert seq.exists_vars[0] == ("f", Sort.POINT)
        assert len(seq.conclusions) == 3

    def test_prop_i12_sequent(self):
        from verifier.e_library import PROP_I_12
        seq = PROP_I_12.sequent
        # Hypotheses: on(a,L), on(b,L), a≠b, ¬on(p,L)
        assert len(seq.hypotheses) == 4
        # ∃h: on(h,L), ∠ahp = right-angle
        assert len(seq.exists_vars) == 1
        assert seq.exists_vars[0] == ("h", Sort.POINT)
        assert len(seq.conclusions) == 3

    def test_prop_i13_sequent(self):
        from verifier.e_library import PROP_I_13
        seq = PROP_I_13.sequent
        # Hypotheses: on(a,L), on(c,L), between(a,b,c), ¬on(d,L), b≠d
        assert len(seq.hypotheses) == 5
        assert len(seq.exists_vars) == 0
        # Conclusion: ∠abd + ∠dbc = 2·right
        assert len(seq.conclusions) == 1

    def test_prop_i14_sequent(self):
        from verifier.e_library import PROP_I_14
        seq = PROP_I_14.sequent
        # Hypotheses include same-side negation and angle sum
        assert len(seq.hypotheses) >= 7
        assert len(seq.exists_vars) == 0
        # Conclusion: between(c,b,d)
        assert len(seq.conclusions) == 1

    def test_prop_i15_sequent(self):
        from verifier.e_library import PROP_I_15
        seq = PROP_I_15.sequent
        # Hypotheses: two lines through e, betweenness, L≠M
        assert len(seq.hypotheses) >= 7
        assert len(seq.exists_vars) == 0
        # Conclusion: ∠aec = ∠bed
        assert len(seq.conclusions) == 1
        assert seq.conclusions[0].is_positive

    def test_get_theorems_before_i11(self):
        from verifier.e_library import get_theorems_up_to
        before = get_theorems_up_to("Prop.I.11")
        assert "Prop.I.1" in before
        assert "Prop.I.3" in before
        assert "Prop.I.10" in before
        assert "Prop.I.11" not in before

    def test_get_theorems_before_i6(self):
        from verifier.e_library import get_theorems_up_to
        before = get_theorems_up_to("Prop.I.6")
        assert "Prop.I.5" in before
        assert "Prop.I.6" not in before


# ═══════════════════════════════════════════════════════════════════════
# System H library tests — new propositions
# ═══════════════════════════════════════════════════════════════════════

class TestHLibraryNewProps:
    """Tests for Props I.6–I.15 in h_library."""

    def test_h_library_has_at_least_15_theorems(self):
        from verifier.h_library import H_THEOREM_LIBRARY
        assert len(H_THEOREM_LIBRARY) >= 15

    def test_h_theorem_order_includes_i15(self):
        from verifier.h_library import H_THEOREM_ORDER
        assert len(H_THEOREM_ORDER) >= 15
        assert H_THEOREM_ORDER[0] == "Prop.I.1"
        assert "Prop.I.15" in H_THEOREM_ORDER

    def test_h_prop_i6_sequent(self):
        from verifier.h_library import PROP_I_6
        seq = PROP_I_6.sequent
        assert len(seq.hypotheses) == 2  # ¬ColH, CongaH
        assert len(seq.exists_vars) == 0
        assert len(seq.conclusions) == 1  # CongH

    def test_h_prop_i7_sequent(self):
        from verifier.h_library import PROP_I_7
        seq = PROP_I_7.sequent
        assert len(seq.hypotheses) == 6
        assert len(seq.conclusions) == 1

    def test_h_prop_i8_sequent(self):
        from verifier.h_library import PROP_I_8
        seq = PROP_I_8.sequent
        # ¬ColH×2, CongH×3
        assert len(seq.hypotheses) == 5
        # CongaH×3
        assert len(seq.conclusions) == 3

    def test_h_prop_i9_sequent(self):
        from verifier.h_library import PROP_I_9
        seq = PROP_I_9.sequent
        assert len(seq.hypotheses) == 1  # ¬ColH
        assert len(seq.exists_vars) == 1  # e
        assert seq.exists_vars[0][1] == HSort.POINT

    def test_h_prop_i10_sequent(self):
        from verifier.h_library import PROP_I_10
        seq = PROP_I_10.sequent
        assert len(seq.hypotheses) == 3
        assert len(seq.exists_vars) == 1
        assert len(seq.conclusions) == 2  # BetH, CongH

    def test_h_prop_i11_sequent(self):
        from verifier.h_library import PROP_I_11
        seq = PROP_I_11.sequent
        assert len(seq.exists_vars) == 1
        assert seq.exists_vars[0] == ("f", HSort.POINT)

    def test_h_prop_i12_sequent(self):
        from verifier.h_library import PROP_I_12
        seq = PROP_I_12.sequent
        # ¬IncidL(p,l) in hypotheses
        assert any(
            h.is_negative for h in seq.hypotheses
        )
        assert len(seq.exists_vars) == 1

    def test_h_prop_i13_sequent(self):
        from verifier.h_library import PROP_I_13
        seq = PROP_I_13.sequent
        assert len(seq.hypotheses) == 2  # BetH, ¬ColH
        assert len(seq.exists_vars) == 0

    def test_h_prop_i14_sequent(self):
        from verifier.h_library import PROP_I_14
        seq = PROP_I_14.sequent
        assert len(seq.conclusions) == 1  # BetH(c,b,d)

    def test_h_prop_i15_sequent(self):
        from verifier.h_library import PROP_I_15
        seq = PROP_I_15.sequent
        assert len(seq.hypotheses) == 3  # 2 BetH + ¬ColH
        assert len(seq.conclusions) == 1  # CongaH

    def test_get_h_theorems_up_to_i11(self):
        from verifier.h_library import get_h_theorems_up_to
        before = get_h_theorems_up_to("Prop.I.11")
        assert "Prop.I.10" in before
        assert "Prop.I.11" not in before
        assert len(before) == 10


# ═══════════════════════════════════════════════════════════════════════
# Proof encodings tests — I.9, I.11, I.13, I.15
# ═══════════════════════════════════════════════════════════════════════

class TestEProofsNewProps:
    """Tests for proof encodings of I.9, I.11, I.13, I.15."""

    def test_proof_catalogue_has_new_entries(self):
        from verifier.e_proofs import E_PROOFS
        assert "Prop.I.9" in E_PROOFS
        assert "Prop.I.11" in E_PROOFS
        assert "Prop.I.13" in E_PROOFS
        assert "Prop.I.15" in E_PROOFS

    def test_prop_i9_proof_structure(self):
        from verifier.e_proofs import get_proof
        proof = get_proof("Prop.I.9")
        assert proof.name == "Prop.I.9"
        assert len(proof.steps) >= 5
        # Should have construction and metric steps
        kinds = {s.kind for s in proof.steps}
        assert StepKind.CONSTRUCTION in kinds

    def test_prop_i11_proof_structure(self):
        from verifier.e_proofs import get_proof
        proof = get_proof("Prop.I.11")
        assert proof.name == "Prop.I.11"
        assert len(proof.steps) >= 4
        # Should reference I.1 or I.8
        theorem_refs = [s.theorem_name for s in proof.steps if s.theorem_name]
        assert len(theorem_refs) >= 1

    def test_prop_i13_proof_structure(self):
        from verifier.e_proofs import get_proof
        proof = get_proof("Prop.I.13")
        assert proof.name == "Prop.I.13"
        assert len(proof.steps) >= 2
        # Should reference I.11
        theorem_refs = [s.theorem_name for s in proof.steps if s.theorem_name]
        assert "Prop.I.11" in theorem_refs

    def test_prop_i15_proof_structure(self):
        from verifier.e_proofs import get_proof
        proof = get_proof("Prop.I.15")
        assert proof.name == "Prop.I.15"
        assert len(proof.steps) >= 3
        # Should reference I.13
        theorem_refs = [s.theorem_name for s in proof.steps if s.theorem_name]
        assert "Prop.I.13" in theorem_refs

    def test_prop_i11_constructs_perpendicular_point(self):
        from verifier.e_proofs import get_proof
        proof = get_proof("Prop.I.11")
        # Goal includes right angle
        right_angle_in_goal = any(
            isinstance(getattr(lit.atom, 'right', None), type(None))
            or "right-angle" in repr(lit)
            for lit in proof.goal
        )
        assert right_angle_in_goal

    def test_prop_i15_goal_is_angle_equality(self):
        from verifier.e_proofs import get_proof
        proof = get_proof("Prop.I.15")
        # Goal should be a single angle equality
        assert len(proof.goal) == 1
        assert proof.goal[0].is_positive


# ═══════════════════════════════════════════════════════════════════════
# Cross-library consistency tests
# ═══════════════════════════════════════════════════════════════════════

class TestCrossLibraryConsistency:
    """Verify that E and H libraries agree on proposition names and counts."""

    def test_same_proposition_names(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        from verifier.h_library import H_THEOREM_LIBRARY
        e_names = set(E_THEOREM_LIBRARY.keys())
        h_names = set(H_THEOREM_LIBRARY.keys())
        assert e_names == h_names

    def test_all_theorems_have_names(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        from verifier.h_library import H_THEOREM_LIBRARY
        for name, thm in E_THEOREM_LIBRARY.items():
            assert thm.name == name
        for name, thm in H_THEOREM_LIBRARY.items():
            assert thm.name == name

    def test_all_e_theorems_have_sequents(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        for name, thm in E_THEOREM_LIBRARY.items():
            assert thm.sequent is not None
            assert isinstance(thm.sequent, Sequent)

    def test_all_h_theorems_have_sequents(self):
        from verifier.h_library import H_THEOREM_LIBRARY
        for name, thm in H_THEOREM_LIBRARY.items():
            assert thm.sequent is not None
            assert isinstance(thm.sequent, HSequent)
