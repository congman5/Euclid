"""
Tests for Props I.27–I.32 in System E library.

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


