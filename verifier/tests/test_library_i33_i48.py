"""
Tests for Props I.33–I.48 in both System E and System H libraries.

Covers Phase 6.4 of the implementation plan (Parallelograms, Area,
Pythagorean Theorem).

Key mathematical notes:
  - I.33–I.34: Parallelogram properties (sides, angles, diagonal)
  - I.35–I.41: Area theory (parallelograms and triangles between parallels)
  - I.42–I.45: Constructing parallelograms with given area
  - I.46: Construct a square
  - I.47: The Pythagorean Theorem
  - I.48: Converse of the Pythagorean Theorem
"""
import pytest
from verifier.e_ast import (
    Sort, Literal, Sequent,
    On, SameSide, Between, Equals, LessThan, Intersects,
    SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag,
)
from verifier.h_ast import HSort, HLiteral, HSequent


# ═══════════════════════════════════════════════════════════════════════
# System E library tests — Props I.33–I.48
# ═══════════════════════════════════════════════════════════════════════

class TestELibraryI33I48:
    """Tests for Props I.33–I.48 in e_library."""

    def test_library_has_48_theorems(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        assert len(E_THEOREM_LIBRARY) == 48

    def test_ordered_names_complete(self):
        from verifier.e_library import get_theorems_up_to
        # Requesting beyond I.48 should return all 48
        before_i49 = get_theorems_up_to("Prop.I.49")
        assert len(before_i49) == 48

    def test_get_theorems_before_i33(self):
        from verifier.e_library import get_theorems_up_to
        before = get_theorems_up_to("Prop.I.33")
        assert "Prop.I.32" in before
        assert "Prop.I.33" not in before
        assert len(before) == 32

    def test_get_theorems_before_i47(self):
        from verifier.e_library import get_theorems_up_to
        before = get_theorems_up_to("Prop.I.47")
        assert "Prop.I.46" in before
        assert "Prop.I.47" not in before
        assert len(before) == 46

    # ── I.33–I.34: Parallelogram properties ──────────────────────────

    def test_prop_i33_sequent(self):
        from verifier.e_library import PROP_I_33
        seq = PROP_I_33.sequent
        # Hypotheses include parallel lines and segment equality
        assert len(seq.hypotheses) >= 8
        assert len(seq.exists_vars) == 0
        # Conclusions: segment equality + parallelism
        assert len(seq.conclusions) == 2

    def test_prop_i34_sequent(self):
        from verifier.e_library import PROP_I_34
        seq = PROP_I_34.sequent
        # Full parallelogram: 4 lines, 4 points, 2 parallel pairs
        assert len(seq.hypotheses) >= 10
        assert len(seq.exists_vars) == 0
        # Conclusions: opposite sides equal, opposite angles equal, area bisection
        assert len(seq.conclusions) == 5

    def test_prop_i34_includes_area(self):
        """I.34 diagonal bisects area — conclusion uses AreaTerm."""
        from verifier.e_library import PROP_I_34
        area_concs = [
            c for c in PROP_I_34.sequent.conclusions
            if isinstance(c.atom, Equals)
            and isinstance(c.atom.left, AreaTerm)
        ]
        assert len(area_concs) >= 1

    # ── I.35–I.41: Area theory ───────────────────────────────────────

    def test_prop_i35_area_equality(self):
        """I.35: parallelograms on same base between same parallels."""
        from verifier.e_library import PROP_I_35
        seq = PROP_I_35.sequent
        # Has ¬intersects (parallel) in hypotheses
        intersects_hyps = [
            h for h in seq.hypotheses
            if isinstance(h.atom, Intersects) and not h.is_positive
        ]
        assert len(intersects_hyps) == 1
        # Conclusion: area equality using MagAdd
        assert len(seq.conclusions) == 1
        conc = seq.conclusions[0]
        assert isinstance(conc.atom, Equals)

    def test_prop_i37_triangle_area(self):
        """I.37: triangles on same base between same parallels."""
        from verifier.e_library import PROP_I_37
        seq = PROP_I_37.sequent
        assert len(seq.conclusions) == 1
        conc = seq.conclusions[0]
        assert isinstance(conc.atom, Equals)
        assert isinstance(conc.atom.left, AreaTerm)

    def test_prop_i41_double_area(self):
        """I.41: parallelogram is double the triangle."""
        from verifier.e_library import PROP_I_41
        seq = PROP_I_41.sequent
        assert len(seq.conclusions) == 1
        conc = seq.conclusions[0]
        assert isinstance(conc.atom, Equals)
        # Both sides should use MagAdd (sum of areas)
        assert isinstance(conc.atom.left, MagAdd)
        assert isinstance(conc.atom.right, MagAdd)

    # ── I.42–I.45: Parallelogram constructions ──────────────────────

    def test_prop_i42_existential(self):
        """I.42: construct parallelogram — has existential vars."""
        from verifier.e_library import PROP_I_42
        seq = PROP_I_42.sequent
        assert len(seq.exists_vars) == 2

    def test_prop_i44_existential(self):
        from verifier.e_library import PROP_I_44
        seq = PROP_I_44.sequent
        assert len(seq.exists_vars) == 2

    def test_prop_i45_existential(self):
        from verifier.e_library import PROP_I_45
        seq = PROP_I_45.sequent
        assert len(seq.exists_vars) == 3

    # ── I.46: Square construction ────────────────────────────────────

    def test_prop_i46_square(self):
        """I.46: square has 4 equal sides and 4 right angles."""
        from verifier.e_library import PROP_I_46
        seq = PROP_I_46.sequent
        # Constructs 2 new points
        assert len(seq.exists_vars) == 2
        # 3 side equalities + 4 right angles = 7 conclusions
        assert len(seq.conclusions) == 7
        # All conclusions are positive equalities
        for conc in seq.conclusions:
            assert conc.is_positive
            assert isinstance(conc.atom, Equals)

    def test_prop_i46_right_angles(self):
        """I.46: all four angles are right angles."""
        from verifier.e_library import PROP_I_46
        right_angle_concs = [
            c for c in PROP_I_46.sequent.conclusions
            if isinstance(c.atom, Equals)
            and isinstance(c.atom.right, type(RightAngle()))
        ]
        assert len(right_angle_concs) == 4

    # ── I.47: Pythagorean Theorem ────────────────────────────────────

    def test_prop_i47_sequent(self):
        """I.47: right triangle → squares on sides with area equality."""
        from verifier.e_library import PROP_I_47
        seq = PROP_I_47.sequent
        # Hypotheses: triangle distinctness + right angle
        assert len(seq.hypotheses) == 4
        right_angle_hyps = [
            h for h in seq.hypotheses
            if isinstance(h.atom, Equals) and h.is_positive
            and isinstance(h.atom.right, type(RightAngle()))
        ]
        assert len(right_angle_hyps) == 1
        # 6 existential points for 3 squares (2 per square)
        assert len(seq.exists_vars) == 6
        # 13 conclusions: 4 per square (3 side equalities + 1 right angle)
        # + 1 area equality
        assert len(seq.conclusions) == 13
        for c in seq.conclusions:
            assert c.is_positive

    def test_prop_i47_conclusion_uses_magadd(self):
        """I.47 final conclusion involves MagAdd (sum of square areas)."""
        from verifier.e_library import PROP_I_47
        # The last conclusion is the area equality
        conc = PROP_I_47.sequent.conclusions[-1]
        assert isinstance(conc.atom, Equals)
        assert isinstance(conc.atom.left, MagAdd)
        assert isinstance(conc.atom.right, MagAdd)

    # ── I.48: Converse Pythagorean ───────────────────────────────────

    def test_prop_i48_sequent(self):
        """I.48: converse — square area condition → right angle."""
        from verifier.e_library import PROP_I_48
        seq = PROP_I_48.sequent
        # Hypotheses: 3 distinctness + 10 square conditions + 1 area equality
        assert len(seq.hypotheses) == 14
        assert len(seq.conclusions) == 1
        conc = seq.conclusions[0]
        assert isinstance(conc.atom, Equals)
        # Conclusion angle = right angle
        assert isinstance(conc.atom.right, type(RightAngle()))

    def test_prop_i47_i48_are_converses(self):
        """I.47 and I.48 are converses of each other."""
        from verifier.e_library import PROP_I_47, PROP_I_48
        # I.47 hypothesis: right angle → area relation
        # I.48 hypothesis: area relation → right angle
        i47_has_right_angle_hyp = any(
            isinstance(h.atom, Equals) and h.is_positive
            and isinstance(h.atom.right, type(RightAngle()))
            for h in PROP_I_47.sequent.hypotheses
        )
        i48_has_right_angle_conc = any(
            isinstance(c.atom, Equals) and c.is_positive
            and isinstance(c.atom.right, type(RightAngle()))
            for c in PROP_I_48.sequent.conclusions
        )
        assert i47_has_right_angle_hyp
        assert i48_has_right_angle_conc


# ═══════════════════════════════════════════════════════════════════════
# System H library tests — Props I.33–I.48
# ═══════════════════════════════════════════════════════════════════════

class TestHLibraryI33I48:
    """Tests for Props I.33–I.48 in h_library."""

    def test_h_library_has_48_theorems(self):
        from verifier.h_library import H_THEOREM_LIBRARY
        assert len(H_THEOREM_LIBRARY) == 48

    def test_h_theorem_order_complete(self):
        from verifier.h_library import H_THEOREM_ORDER
        assert len(H_THEOREM_ORDER) == 48
        assert H_THEOREM_ORDER[0] == "Prop.I.1"
        assert H_THEOREM_ORDER[-1] == "Prop.I.48"

    def test_h_prop_i33_uses_para(self):
        from verifier.h_library import PROP_I_33
        from verifier.h_ast import Para
        para_hyps = [
            h for h in PROP_I_33.sequent.hypotheses
            if isinstance(h.atom, Para)
        ]
        assert len(para_hyps) == 1

    def test_h_prop_i34_parallelogram(self):
        from verifier.h_library import PROP_I_34
        from verifier.h_ast import Para, CongH, CongaH
        seq = PROP_I_34.sequent
        # Two Para hypotheses (opposite sides)
        para_hyps = [
            h for h in seq.hypotheses if isinstance(h.atom, Para)
        ]
        assert len(para_hyps) == 2
        # CongH and CongaH conclusions
        assert len(seq.conclusions) == 3

    def test_h_prop_i46_square(self):
        from verifier.h_library import PROP_I_46
        from verifier.h_ast import CongH
        seq = PROP_I_46.sequent
        assert len(seq.exists_vars) == 2
        cong_concs = [
            c for c in seq.conclusions if isinstance(c.atom, CongH)
        ]
        assert len(cong_concs) == 3

    def test_h_prop_i47_non_collinear(self):
        from verifier.h_library import PROP_I_47
        from verifier.h_ast import ColH
        col_hyps = [
            h for h in PROP_I_47.sequent.hypotheses
            if isinstance(h.atom, ColH) and not h.is_positive
        ]
        assert len(col_hyps) == 1

    def test_get_h_theorems_up_to_i48(self):
        from verifier.h_library import get_h_theorems_up_to
        before = get_h_theorems_up_to("Prop.I.48")
        assert "Prop.I.47" in before
        assert "Prop.I.48" not in before
        assert len(before) == 47

    def test_get_h_theorems_up_to_i33(self):
        from verifier.h_library import get_h_theorems_up_to
        before = get_h_theorems_up_to("Prop.I.33")
        assert len(before) == 32


# ═══════════════════════════════════════════════════════════════════════
# Cross-library consistency — all 48 propositions
# ═══════════════════════════════════════════════════════════════════════

class TestCrossLibraryI33I48:
    """Verify E and H libraries agree on all 48 proposition names."""

    def test_same_proposition_names(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        from verifier.h_library import H_THEOREM_LIBRARY
        e_names = set(E_THEOREM_LIBRARY.keys())
        h_names = set(H_THEOREM_LIBRARY.keys())
        assert e_names == h_names

    def test_all_props_i1_through_i48(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        for i in range(1, 49):
            name = f"Prop.I.{i}"
            assert name in E_THEOREM_LIBRARY, f"Missing {name} from E library"

    def test_all_h_props_i1_through_i48(self):
        from verifier.h_library import H_THEOREM_LIBRARY
        for i in range(1, 49):
            name = f"Prop.I.{i}"
            assert name in H_THEOREM_LIBRARY, f"Missing {name} from H library"

    def test_all_statements_nonempty(self):
        """All 48 propositions have non-empty statement text."""
        from verifier.e_library import E_THEOREM_LIBRARY
        from verifier.h_library import H_THEOREM_LIBRARY
        for i in range(1, 49):
            name = f"Prop.I.{i}"
            assert len(E_THEOREM_LIBRARY[name].statement) > 10, \
                f"{name} E statement too short"
            assert len(H_THEOREM_LIBRARY[name].statement) > 10, \
                f"{name} H statement too short"

    def test_area_props_use_area_term(self):
        """I.35–I.41 in E use AreaTerm in hypotheses or conclusions."""
        from verifier.e_library import E_THEOREM_LIBRARY

        def _has_area(seq):
            for lit in seq.hypotheses + seq.conclusions:
                if isinstance(lit.atom, Equals):
                    if isinstance(lit.atom.left, AreaTerm):
                        return True
                    if isinstance(lit.atom.left, MagAdd):
                        return True
                    if isinstance(lit.atom.right, AreaTerm):
                        return True
            return False

        for i in [35, 37, 38, 41]:
            name = f"Prop.I.{i}"
            seq = E_THEOREM_LIBRARY[name].sequent
            assert _has_area(seq), f"{name} should use AreaTerm"

    def test_pythagorean_pair(self):
        """I.47 (Pythagorean) and I.48 (converse) are both present."""
        from verifier.e_library import E_THEOREM_LIBRARY
        assert "Prop.I.47" in E_THEOREM_LIBRARY
        assert "Prop.I.48" in E_THEOREM_LIBRARY
        assert "Pythagorean" in E_THEOREM_LIBRARY["Prop.I.47"].statement \
            or "right-angled" in E_THEOREM_LIBRARY["Prop.I.47"].statement
