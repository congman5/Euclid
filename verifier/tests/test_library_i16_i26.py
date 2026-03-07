"""
Tests for Props I.16–I.26 in both System E and System H libraries,
and proof encodings in e_proofs.

Covers Phase 6.2 of the implementation plan.
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
# System E library tests — Props I.16–I.26
# ═══════════════════════════════════════════════════════════════════════

class TestELibraryI16I26:
    """Tests for Props I.16–I.26 in e_library."""

    def test_library_has_at_least_26_theorems(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        assert len(E_THEOREM_LIBRARY) >= 26

    def test_ordered_names_complete(self):
        from verifier.e_library import get_theorems_up_to
        before_i26 = get_theorems_up_to("Prop.I.26")
        assert len(before_i26) == 25
        assert "Prop.I.26" not in before_i26
        assert "Prop.I.25" in before_i26

    def test_prop_i16_sequent(self):
        from verifier.e_library import PROP_I_16
        seq = PROP_I_16.sequent
        # Has betweenness (extension) and distinctness in hypotheses
        assert len(seq.hypotheses) >= 5
        assert len(seq.exists_vars) == 0
        # Two inequality conclusions (∠bac < ∠dbc, ∠bca < ∠dbc)
        assert len(seq.conclusions) == 2
        for c in seq.conclusions:
            assert c.is_positive

    def test_prop_i17_sequent(self):
        from verifier.e_library import PROP_I_17
        seq = PROP_I_17.sequent
        assert len(seq.hypotheses) >= 4
        assert len(seq.exists_vars) == 0
        assert len(seq.conclusions) == 1

    def test_prop_i18_sequent(self):
        from verifier.e_library import PROP_I_18
        seq = PROP_I_18.sequent
        # Hypotheses include segment inequality
        assert len(seq.hypotheses) == 4
        # Conclusion: angle inequality
        assert len(seq.conclusions) == 1

    def test_prop_i19_sequent(self):
        from verifier.e_library import PROP_I_19
        seq = PROP_I_19.sequent
        # Converse of I.18: angle < → segment <
        assert len(seq.hypotheses) == 4
        assert len(seq.conclusions) == 1

    def test_prop_i18_i19_are_converses(self):
        from verifier.e_library import PROP_I_18, PROP_I_19
        # I.18 hypothesis has segment inequality, conclusion has angle inequality
        # I.19 hypothesis has angle inequality, conclusion has segment inequality
        i18_hyp_types = {type(h.atom).__name__ for h in PROP_I_18.sequent.hypotheses
                         if h.is_positive}
        i19_hyp_types = {type(h.atom).__name__ for h in PROP_I_19.sequent.hypotheses
                         if h.is_positive}
        assert "LessThan" in i18_hyp_types
        assert "LessThan" in i19_hyp_types

    def test_prop_i20_sequent(self):
        from verifier.e_library import PROP_I_20
        seq = PROP_I_20.sequent
        # Only distinctness hypotheses
        assert len(seq.hypotheses) == 3
        assert all(h.is_negative for h in seq.hypotheses)
        # Conclusion: bc < ab + ac (uses MagAdd)
        assert len(seq.conclusions) == 1

    def test_prop_i21_sequent(self):
        from verifier.e_library import PROP_I_21
        seq = PROP_I_21.sequent
        # Point d inside triangle
        assert len(seq.hypotheses) >= 6
        # Two conclusions: sum comparison and angle comparison
        assert len(seq.conclusions) == 2

    def test_prop_i22_sequent(self):
        from verifier.e_library import PROP_I_22
        seq = PROP_I_22.sequent
        # 3 distinctness + 3 triangle-inequality prerequisites
        assert len(seq.hypotheses) == 6
        # Constructs 3 new points
        assert len(seq.exists_vars) == 3
        # 3 segment equalities
        assert len(seq.conclusions) == 3

    def test_prop_i23_sequent(self):
        from verifier.e_library import PROP_I_23
        seq = PROP_I_23.sequent
        # Given an angle def and a line L with point a
        assert len(seq.hypotheses) >= 5
        # Construct point g
        assert len(seq.exists_vars) == 1
        assert seq.exists_vars[0] == ("g", Sort.POINT)
        # Conclusion: angle copy + not on line
        assert len(seq.conclusions) == 2

    def test_prop_i24_sequent(self):
        from verifier.e_library import PROP_I_24
        seq = PROP_I_24.sequent
        # Hinge theorem: 2 segment eq + 1 angle ineq + 6 distinctness
        assert len(seq.hypotheses) == 9
        assert len(seq.conclusions) == 1

    def test_prop_i25_sequent(self):
        from verifier.e_library import PROP_I_25
        seq = PROP_I_25.sequent
        # Converse hinge: 2 seg eq + 1 seg ineq + 6 distinctness
        assert len(seq.hypotheses) == 9
        assert len(seq.conclusions) == 1

    def test_prop_i24_i25_are_converses(self):
        from verifier.e_library import PROP_I_24, PROP_I_25
        # I.24: angle inequality → segment inequality
        # I.25: segment inequality → angle inequality
        i24_conc = PROP_I_24.sequent.conclusions[0]
        i25_conc = PROP_I_25.sequent.conclusions[0]
        # Both use LessThan but on different magnitude types
        assert type(i24_conc.atom).__name__ == "LessThan"
        assert type(i25_conc.atom).__name__ == "LessThan"

    def test_prop_i26_sequent(self):
        from verifier.e_library import PROP_I_26
        seq = PROP_I_26.sequent
        # ASA: 2 angle eq + 1 segment eq + 6 distinctness
        assert len(seq.hypotheses) == 9
        assert len(seq.exists_vars) == 0
        # Conclusions: 2 segment eq + 1 angle eq + 1 area eq
        assert len(seq.conclusions) == 4

    def test_get_theorems_before_i16(self):
        from verifier.e_library import get_theorems_up_to
        before = get_theorems_up_to("Prop.I.16")
        assert "Prop.I.15" in before
        assert "Prop.I.16" not in before
        assert len(before) == 15

    def test_get_theorems_before_i20(self):
        from verifier.e_library import get_theorems_up_to
        before = get_theorems_up_to("Prop.I.20")
        assert "Prop.I.19" in before
        assert "Prop.I.20" not in before


# ═══════════════════════════════════════════════════════════════════════
# System H library tests — Props I.16–I.26
# ═══════════════════════════════════════════════════════════════════════

class TestHLibraryI16I26:
    """Tests for Props I.16–I.26 in h_library."""

    def test_h_library_has_at_least_26_theorems(self):
        from verifier.h_library import H_THEOREM_LIBRARY
        assert len(H_THEOREM_LIBRARY) >= 26

    def test_h_theorem_order_complete(self):
        from verifier.h_library import H_THEOREM_ORDER
        assert len(H_THEOREM_ORDER) >= 26
        assert H_THEOREM_ORDER[0] == "Prop.I.1"
        assert "Prop.I.26" in H_THEOREM_ORDER

    def test_h_prop_i16_sequent(self):
        from verifier.h_library import PROP_I_16
        seq = PROP_I_16.sequent
        # Non-collinear + betweenness
        assert len(seq.hypotheses) == 2

    def test_h_prop_i20_sequent(self):
        from verifier.h_library import PROP_I_20
        seq = PROP_I_20.sequent
        # Triangle inequality — non-collinear hypothesis
        assert len(seq.hypotheses) >= 1

    def test_h_prop_i22_sequent(self):
        from verifier.h_library import PROP_I_22
        seq = PROP_I_22.sequent
        # Constructs 3 points
        assert len(seq.exists_vars) == 3
        # Conclusions include CongH and ¬ColH
        assert len(seq.conclusions) == 4

    def test_h_prop_i23_sequent(self):
        from verifier.h_library import PROP_I_23
        seq = PROP_I_23.sequent
        assert len(seq.exists_vars) == 1
        assert seq.exists_vars[0] == ("g", HSort.POINT)
        # CongaH conclusion
        assert len(seq.conclusions) == 2

    def test_h_prop_i26_sequent(self):
        from verifier.h_library import PROP_I_26
        seq = PROP_I_26.sequent
        # ¬ColH×2, CongaH×2, CongH (bc=ef)
        assert len(seq.hypotheses) == 5
        # CongH×2, CongaH
        assert len(seq.conclusions) == 3

    def test_get_h_theorems_up_to_i26(self):
        from verifier.h_library import get_h_theorems_up_to
        before = get_h_theorems_up_to("Prop.I.26")
        assert "Prop.I.25" in before
        assert "Prop.I.26" not in before
        assert len(before) == 25

    def test_get_h_theorems_up_to_i16(self):
        from verifier.h_library import get_h_theorems_up_to
        before = get_h_theorems_up_to("Prop.I.16")
        assert len(before) == 15


# ═══════════════════════════════════════════════════════════════════════
# Proof encodings tests — I.16, I.20, I.26
# ═══════════════════════════════════════════════════════════════════════

class TestEProofsI16I26:
    """Tests for proof encodings of I.16, I.20, I.26."""

    def test_proof_catalogue_has_new_entries(self):
        from verifier.e_proofs import E_PROOFS
        assert "Prop.I.16" in E_PROOFS
        assert "Prop.I.20" in E_PROOFS
        assert "Prop.I.26" in E_PROOFS

    def test_proof_catalogue_total(self):
        from verifier.e_proofs import _STRUCTURED_PROOFS
        assert len(_STRUCTURED_PROOFS) == 48

    def test_prop_i16_proof_structure(self):
        from verifier.e_proofs import get_proof
        proof = get_proof("Prop.I.16")
        assert proof.name == "Prop.I.16"
        assert len(proof.steps) >= 5
        # Should reference I.10 (bisection) and I.4 (SAS)
        theorem_refs = [s.theorem_name for s in proof.steps if s.theorem_name]
        assert "Prop.I.10" in theorem_refs
        assert "Prop.I.4" in theorem_refs

    def test_prop_i16_has_construction_steps(self):
        from verifier.e_proofs import get_proof
        proof = get_proof("Prop.I.16")
        kinds = {s.kind for s in proof.steps}
        assert StepKind.CONSTRUCTION in kinds
        assert StepKind.DIAGRAMMATIC in kinds

    def test_prop_i20_proof_structure(self):
        from verifier.e_proofs import get_proof
        proof = get_proof("Prop.I.20")
        assert proof.name == "Prop.I.20"
        assert len(proof.steps) >= 4
        # Should reference I.5 and I.19
        theorem_refs = [s.theorem_name for s in proof.steps if s.theorem_name]
        assert "Prop.I.5" in theorem_refs
        assert "Prop.I.19" in theorem_refs

    def test_prop_i20_goal_uses_magadd(self):
        from verifier.e_proofs import get_proof
        proof = get_proof("Prop.I.20")
        # Goal should involve magnitude addition (bc < ab + ac)
        goal_repr = " ".join(repr(g) for g in proof.goal)
        assert "+" in goal_repr

    def test_prop_i26_proof_structure(self):
        from verifier.e_proofs import get_proof
        proof = get_proof("Prop.I.26")
        assert proof.name == "Prop.I.26"
        assert len(proof.steps) >= 2
        # Should reference I.4 (SAS) and I.3 (cut segment)
        theorem_refs = [s.theorem_name for s in proof.steps if s.theorem_name]
        assert "Prop.I.4" in theorem_refs
        assert "Prop.I.3" in theorem_refs

    def test_prop_i26_concludes_full_congruence(self):
        from verifier.e_proofs import get_proof
        proof = get_proof("Prop.I.26")
        # Goal should include segment eq, angle eq, and area eq
        assert len(proof.goal) == 4
        goal_types = [type(g.atom).__name__ for g in proof.goal]
        assert goal_types.count("Equals") == 4


# ═══════════════════════════════════════════════════════════════════════
# Cross-library consistency — updated for 26 propositions
# ═══════════════════════════════════════════════════════════════════════

class TestCrossLibraryI16I26:
    """Verify E and H libraries agree on proposition names."""

    def test_same_proposition_names(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        from verifier.h_library import H_THEOREM_LIBRARY
        e_names = set(E_THEOREM_LIBRARY.keys())
        h_names = set(H_THEOREM_LIBRARY.keys())
        assert e_names == h_names

    def test_all_props_i1_through_i26(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        for i in range(1, 27):
            name = f"Prop.I.{i}"
            assert name in E_THEOREM_LIBRARY, f"Missing {name} from E library"

    def test_all_h_props_i1_through_i26(self):
        from verifier.h_library import H_THEOREM_LIBRARY
        for i in range(1, 27):
            name = f"Prop.I.{i}"
            assert name in H_THEOREM_LIBRARY, f"Missing {name} from H library"

    def test_all_theorems_have_statements(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        from verifier.h_library import H_THEOREM_LIBRARY
        for name, thm in E_THEOREM_LIBRARY.items():
            assert thm.statement, f"{name} E has no statement"
        for name, thm in H_THEOREM_LIBRARY.items():
            assert thm.statement, f"{name} H has no statement"
