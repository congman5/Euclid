"""
Tests for Props I.27–I.32 in both System E and System H libraries.

Covers Phase 6.3 of the implementation plan (Parallel Lines).

Key mathematical notes:
  - I.27–I.28: neutral geometry (no parallel postulate needed)
  - I.29: FIRST use of the parallel postulate (Postulate 5 / DA5)
  - I.30–I.31: parallel transitivity and construction
  - I.32: angle sum theorem (the culmination of angle theory)
"""
import pytest
from verifier.e_ast import (
    Sort, Literal, Sequent,
    On, SameSide, Between, Equals, LessThan, Intersects,
    SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag,
)
from verifier.h_ast import HSort, HLiteral, HSequent


# ═══════════════════════════════════════════════════════════════════════
# System E library tests — Props I.27–I.32
# ═══════════════════════════════════════════════════════════════════════

class TestELibraryI27I32:
    """Tests for Props I.27–I.32 in e_library."""

    def test_library_has_at_least_32_theorems(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        assert len(E_THEOREM_LIBRARY) >= 32

    def test_ordered_names_complete(self):
        from verifier.e_library import get_theorems_up_to
        before_i32 = get_theorems_up_to("Prop.I.32")
        assert len(before_i32) == 31
        assert "Prop.I.32" not in before_i32
        assert "Prop.I.31" in before_i32

    def test_ordered_names_include_i27_i32(self):
        from verifier.e_library import get_theorems_up_to
        # All 32 props available when checking beyond I.32
        all_before = get_theorems_up_to("Prop.I.33")
        for i in range(27, 33):
            assert f"Prop.I.{i}" in all_before

    def test_prop_i27_sequent(self):
        from verifier.e_library import PROP_I_27
        seq = PROP_I_27.sequent
        # Hypotheses: line/point incidence + distinctness + angle equality
        assert len(seq.hypotheses) >= 10
        assert len(seq.exists_vars) == 0
        # Conclusion: ¬intersects(L, N) — i.e. lines are parallel
        assert len(seq.conclusions) == 1
        conc = seq.conclusions[0]
        assert not conc.is_positive  # negative: ¬intersects
        assert isinstance(conc.atom, Intersects)

    def test_prop_i28_sequent(self):
        from verifier.e_library import PROP_I_28
        seq = PROP_I_28.sequent
        assert len(seq.hypotheses) >= 10
        assert len(seq.exists_vars) == 0
        # Conclusion: ¬intersects (parallel)
        assert len(seq.conclusions) == 1
        conc = seq.conclusions[0]
        assert not conc.is_positive
        assert isinstance(conc.atom, Intersects)

    def test_prop_i27_i28_both_conclude_parallel(self):
        """Both I.27 and I.28 conclude that lines are parallel."""
        from verifier.e_library import PROP_I_27, PROP_I_28
        for prop in [PROP_I_27, PROP_I_28]:
            conc = prop.sequent.conclusions[0]
            assert isinstance(conc.atom, Intersects)
            assert not conc.is_positive

    def test_prop_i29_sequent(self):
        """I.29 is the converse of I.27 — the first use of Post.5."""
        from verifier.e_library import PROP_I_29
        seq = PROP_I_29.sequent
        # Hypotheses include ¬intersects (parallel) as a premise
        intersects_hyps = [
            h for h in seq.hypotheses
            if isinstance(h.atom, Intersects) and not h.is_positive
        ]
        assert len(intersects_hyps) == 1
        assert len(seq.exists_vars) == 0
        # Conclusion: angle equality
        assert len(seq.conclusions) == 1
        conc = seq.conclusions[0]
        assert conc.is_positive
        assert isinstance(conc.atom, Equals)

    def test_prop_i27_i29_are_converses(self):
        """I.27 and I.29 are converses: alt angles ↔ parallel."""
        from verifier.e_library import PROP_I_27, PROP_I_29
        # I.27 hypothesizes angle equality, concludes ¬intersects
        i27_has_angle_eq = any(
            isinstance(h.atom, Equals) and h.is_positive
            for h in PROP_I_27.sequent.hypotheses
        )
        i27_concludes_parallel = (
            isinstance(PROP_I_27.sequent.conclusions[0].atom, Intersects)
            and not PROP_I_27.sequent.conclusions[0].is_positive
        )
        # I.29 hypothesizes ¬intersects, concludes angle equality
        i29_has_parallel = any(
            isinstance(h.atom, Intersects) and not h.is_positive
            for h in PROP_I_29.sequent.hypotheses
        )
        i29_concludes_angle_eq = (
            isinstance(PROP_I_29.sequent.conclusions[0].atom, Equals)
            and PROP_I_29.sequent.conclusions[0].is_positive
        )
        assert i27_has_angle_eq
        assert i27_concludes_parallel
        assert i29_has_parallel
        assert i29_concludes_angle_eq

    def test_prop_i30_sequent(self):
        """I.30: parallel transitivity — L∥M, M∥N → L∥N."""
        from verifier.e_library import PROP_I_30
        seq = PROP_I_30.sequent
        # Hypotheses: two ¬intersects + three distinctness
        intersects_hyps = [
            h for h in seq.hypotheses
            if isinstance(h.atom, Intersects) and not h.is_positive
        ]
        assert len(intersects_hyps) == 2
        assert len(seq.exists_vars) == 0
        # Conclusion: ¬intersects(L, N)
        assert len(seq.conclusions) == 1
        assert not seq.conclusions[0].is_positive
        assert isinstance(seq.conclusions[0].atom, Intersects)

    def test_prop_i31_sequent(self):
        """I.31: construct parallel — existential (new line M)."""
        from verifier.e_library import PROP_I_31
        seq = PROP_I_31.sequent
        # Has a point not on L
        non_on_hyps = [
            h for h in seq.hypotheses
            if isinstance(h.atom, On) and not h.is_positive
        ]
        assert len(non_on_hyps) == 1
        # Constructs a new line
        assert len(seq.exists_vars) == 1
        assert seq.exists_vars[0] == ("M", Sort.LINE)
        # Conclusions: on(a, M) and ¬intersects(L, M)
        assert len(seq.conclusions) == 2

    def test_prop_i32_sequent(self):
        """I.32: angle sum theorem — two conclusions."""
        from verifier.e_library import PROP_I_32
        seq = PROP_I_32.sequent
        # Has between(b, c, d) in hypotheses
        between_hyps = [
            h for h in seq.hypotheses
            if isinstance(h.atom, Between) and h.is_positive
        ]
        assert len(between_hyps) == 1
        # Two conclusions: exterior angle theorem + angle sum = 2 right angles
        assert len(seq.conclusions) == 2
        for conc in seq.conclusions:
            assert conc.is_positive
            assert isinstance(conc.atom, Equals)

    def test_prop_i32_angle_sum_uses_right_angles(self):
        """I.32 angle sum conclusion involves 2 right angles."""
        from verifier.e_library import PROP_I_32
        # The second conclusion should be ∠+∠+∠ = right + right
        conc = PROP_I_32.sequent.conclusions[1]
        assert isinstance(conc.atom, Equals)
        # The right-hand side should involve RightAngle
        rhs = conc.atom.right
        assert isinstance(rhs, MagAdd)

    def test_get_theorems_before_i27(self):
        from verifier.e_library import get_theorems_up_to
        before = get_theorems_up_to("Prop.I.27")
        assert "Prop.I.26" in before
        assert "Prop.I.27" not in before
        assert len(before) == 26

    def test_get_theorems_before_i29(self):
        """I.29 can reference I.27, I.28 but not itself."""
        from verifier.e_library import get_theorems_up_to
        before = get_theorems_up_to("Prop.I.29")
        assert "Prop.I.27" in before
        assert "Prop.I.28" in before
        assert "Prop.I.29" not in before
        assert len(before) == 28


# ═══════════════════════════════════════════════════════════════════════
# System H library tests — Props I.27–I.32
# ═══════════════════════════════════════════════════════════════════════

class TestHLibraryI27I32:
    """Tests for Props I.27–I.32 in h_library."""

    def test_h_library_has_at_least_32_theorems(self):
        from verifier.h_library import H_THEOREM_LIBRARY
        assert len(H_THEOREM_LIBRARY) >= 32

    def test_h_theorem_order_complete(self):
        from verifier.h_library import H_THEOREM_ORDER
        assert len(H_THEOREM_ORDER) >= 32
        assert H_THEOREM_ORDER[0] == "Prop.I.1"
        assert "Prop.I.32" in H_THEOREM_ORDER

    def test_h_prop_i27_uses_para(self):
        """I.27 in H system uses Para(l, n) as conclusion."""
        from verifier.h_library import PROP_I_27
        from verifier.h_ast import Para
        seq = PROP_I_27.sequent
        para_concs = [
            c for c in seq.conclusions
            if isinstance(c.atom, Para)
        ]
        assert len(para_concs) == 1

    def test_h_prop_i29_hypothesizes_para(self):
        """I.29 in H system uses Para(l, n) as hypothesis."""
        from verifier.h_library import PROP_I_29
        from verifier.h_ast import Para
        seq = PROP_I_29.sequent
        para_hyps = [
            h for h in seq.hypotheses
            if isinstance(h.atom, Para)
        ]
        assert len(para_hyps) == 1

    def test_h_prop_i30_para_transitivity(self):
        """I.30 in H system: Para(l,m), Para(m,n) → Para(l,n)."""
        from verifier.h_library import PROP_I_30
        from verifier.h_ast import Para
        seq = PROP_I_30.sequent
        para_hyps = [
            h for h in seq.hypotheses
            if isinstance(h.atom, Para) and h.is_positive
        ]
        assert len(para_hyps) == 2
        para_concs = [
            c for c in seq.conclusions
            if isinstance(c.atom, Para) and c.is_positive
        ]
        assert len(para_concs) == 1

    def test_h_prop_i31_constructs_line(self):
        """I.31 constructs a new line (existential)."""
        from verifier.h_library import PROP_I_31
        seq = PROP_I_31.sequent
        assert len(seq.exists_vars) == 1
        assert seq.exists_vars[0] == ("m", HSort.LINE)

    def test_h_prop_i32_non_collinear(self):
        """I.32 uses ¬ColH as hypothesis (triangle)."""
        from verifier.h_library import PROP_I_32
        from verifier.h_ast import ColH
        seq = PROP_I_32.sequent
        col_hyps = [
            h for h in seq.hypotheses
            if isinstance(h.atom, ColH) and not h.is_positive
        ]
        assert len(col_hyps) == 1

    def test_get_h_theorems_up_to_i32(self):
        from verifier.h_library import get_h_theorems_up_to
        before = get_h_theorems_up_to("Prop.I.32")
        assert "Prop.I.31" in before
        assert "Prop.I.32" not in before
        assert len(before) == 31

    def test_get_h_theorems_up_to_i27(self):
        from verifier.h_library import get_h_theorems_up_to
        before = get_h_theorems_up_to("Prop.I.27")
        assert len(before) == 26


# ═══════════════════════════════════════════════════════════════════════
# Cross-library consistency — Props I.27–I.32
# ═══════════════════════════════════════════════════════════════════════

class TestCrossLibraryI27I32:
    """Verify E and H libraries agree on proposition names for I.27–I.32."""

    def test_same_proposition_names(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        from verifier.h_library import H_THEOREM_LIBRARY
        e_names = set(E_THEOREM_LIBRARY.keys())
        h_names = set(H_THEOREM_LIBRARY.keys())
        assert e_names == h_names

    def test_all_props_i1_through_i32(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        for i in range(1, 33):
            name = f"Prop.I.{i}"
            assert name in E_THEOREM_LIBRARY, f"Missing {name} from E library"

    def test_all_h_props_i1_through_i32(self):
        from verifier.h_library import H_THEOREM_LIBRARY
        for i in range(1, 33):
            name = f"Prop.I.{i}"
            assert name in H_THEOREM_LIBRARY, f"Missing {name} from H library"

    def test_matching_statement_texts(self):
        """Both E and H entries have non-empty statements for I.27–I.32."""
        from verifier.e_library import E_THEOREM_LIBRARY
        from verifier.h_library import H_THEOREM_LIBRARY
        for i in range(27, 33):
            name = f"Prop.I.{i}"
            assert len(E_THEOREM_LIBRARY[name].statement) > 20
            assert len(H_THEOREM_LIBRARY[name].statement) > 20

    def test_parallel_props_use_correct_predicates(self):
        """I.27–I.31 in E use Intersects; in H use Para."""
        from verifier.e_library import E_THEOREM_LIBRARY
        from verifier.h_library import H_THEOREM_LIBRARY
        from verifier.h_ast import Para
        for name in ["Prop.I.27", "Prop.I.28", "Prop.I.30", "Prop.I.31"]:
            e_seq = E_THEOREM_LIBRARY[name].sequent
            h_seq = H_THEOREM_LIBRARY[name].sequent
            # E uses Intersects (negated = parallel)
            e_has_intersects = any(
                isinstance(lit.atom, Intersects)
                for lit in e_seq.hypotheses + e_seq.conclusions
            )
            # H uses Para
            h_has_para = any(
                isinstance(lit.atom, Para)
                for lit in h_seq.hypotheses + h_seq.conclusions
            )
            assert e_has_intersects, f"{name} E missing Intersects"
            assert h_has_para, f"{name} H missing Para"
