"""
Tests for Phase 6.5.3: Proposition Data ↔ E/H Library linkage.

Validates that every Euclid Book I proposition in proposition_data.py
has a valid link to both the System E and System H theorem libraries,
and that all helper functions work correctly.
"""
import pytest

from euclid_py.engine.proposition_data import (
    PROPOSITIONS, ALL_PROPOSITIONS, Proposition,
    get_proposition, get_e_sequent, get_h_sequent, get_all_formal_links,
)


# ═══════════════════════════════════════════════════════════════════════
# e_library_name property
# ═══════════════════════════════════════════════════════════════════════

class TestELibraryName:
    """Verify the e_library_name property on all propositions."""

    def test_all_euclid_have_e_library_name(self):
        for p in PROPOSITIONS:
            assert p.e_library_name is not None, f"{p.id} missing e_library_name"
            assert p.e_library_name.startswith("Prop.I."), f"{p.id}: {p.e_library_name}"

    def test_correct_format(self):
        p = get_proposition("euclid-I.1")
        assert p.e_library_name == "Prop.I.1"
        p47 = get_proposition("euclid-I.47")
        assert p47.e_library_name == "Prop.I.47"

    def test_textbook_returns_none(self):
        p = get_proposition("tb-thm-2.1")
        assert p.e_library_name is None

    def test_all_48_unique(self):
        names = [p.e_library_name for p in PROPOSITIONS]
        assert len(set(names)) == 48


# ═══════════════════════════════════════════════════════════════════════
# get_e_theorem / get_h_theorem
# ═══════════════════════════════════════════════════════════════════════

class TestGetETheorem:
    """Every Euclid proposition has a linked E theorem."""

    def test_all_48_have_e_theorem(self):
        for p in PROPOSITIONS:
            thm = p.get_e_theorem()
            assert thm is not None, f"{p.id} has no E theorem"
            assert thm.name == p.e_library_name, (
                f"{p.id}: E theorem name {thm.name} != {p.e_library_name}"
            )

    def test_e_theorem_has_sequent(self):
        for p in PROPOSITIONS:
            thm = p.get_e_theorem()
            assert thm.sequent is not None, f"{p.id} E theorem has no sequent"

    def test_textbook_returns_none(self):
        p = get_proposition("tb-thm-2.1")
        assert p.get_e_theorem() is None


class TestGetHTheorem:
    """Every Euclid proposition has a linked H theorem."""

    def test_all_48_have_h_theorem(self):
        for p in PROPOSITIONS:
            thm = p.get_h_theorem()
            assert thm is not None, f"{p.id} has no H theorem"
            assert thm.name == p.e_library_name, (
                f"{p.id}: H theorem name {thm.name} != {p.e_library_name}"
            )

    def test_h_theorem_has_sequent(self):
        for p in PROPOSITIONS:
            thm = p.get_h_theorem()
            assert thm.sequent is not None, f"{p.id} H theorem has no sequent"

    def test_textbook_returns_none(self):
        p = get_proposition("tb-thm-4.1")
        assert p.get_h_theorem() is None


# ═══════════════════════════════════════════════════════════════════════
# formal_sequent property
# ═══════════════════════════════════════════════════════════════════════

class TestFormalSequent:
    """The formal_sequent property returns a non-empty string for all 48 props."""

    def test_all_48_have_formal_sequent(self):
        for p in PROPOSITIONS:
            seq = p.formal_sequent
            assert seq is not None, f"{p.id} has no formal_sequent"
            assert len(seq) > 10, f"{p.id} formal_sequent too short: {seq}"

    def test_contains_arrow(self):
        """Sequents should contain the ⇒ symbol."""
        for p in PROPOSITIONS:
            seq = p.formal_sequent
            assert "⇒" in seq, f"{p.id} formal_sequent missing ⇒: {seq}"

    def test_textbook_returns_none(self):
        p = get_proposition("tb-thm-2.1")
        assert p.formal_sequent is None


# ═══════════════════════════════════════════════════════════════════════
# Module-level helper functions
# ═══════════════════════════════════════════════════════════════════════

class TestModuleHelpers:
    """Test get_e_sequent, get_h_sequent, get_all_formal_links."""

    def test_get_e_sequent(self):
        seq = get_e_sequent("euclid-I.1")
        assert seq is not None
        assert "⇒" in seq

    def test_get_e_sequent_missing(self):
        assert get_e_sequent("nonexistent") is None

    def test_get_h_sequent(self):
        seq = get_h_sequent("euclid-I.1")
        assert seq is not None
        assert "⇒" in seq

    def test_get_h_sequent_missing(self):
        assert get_h_sequent("nonexistent") is None

    def test_get_all_formal_links_count(self):
        links = get_all_formal_links()
        assert len(links) == 48

    def test_get_all_formal_links_all_have_e(self):
        links = get_all_formal_links()
        for prop_id, data in links.items():
            assert data["e_name"] is not None, f"{prop_id} missing e_name"
            assert data["e_sequent"] is not None, f"{prop_id} missing e_sequent"

    def test_get_all_formal_links_all_have_h(self):
        links = get_all_formal_links()
        for prop_id, data in links.items():
            assert data["h_sequent"] is not None, f"{prop_id} missing h_sequent"


# ═══════════════════════════════════════════════════════════════════════
# Spot-checks for specific propositions
# ═══════════════════════════════════════════════════════════════════════

class TestSpecificLinks:
    """Spot-check known propositions have correct formal content."""

    def test_i1_sequent_mentions_equilateral(self):
        seq = get_e_sequent("euclid-I.1")
        # Equilateral: ab = ac and ab = bc
        assert "ab = ac" in seq or "ab=ac" in seq.replace(" ", "")

    def test_i4_sas(self):
        seq = get_e_sequent("euclid-I.4")
        # SAS should mention angle
        assert "∠" in seq or "angle" in seq.lower() or "Angle" in seq

    def test_i47_pythagorean(self):
        seq = get_e_sequent("euclid-I.47")
        # Should mention area (uses △ symbol for AreaTerm)
        assert "△" in seq or "Area" in seq or "MagAdd" in seq

    def test_i48_converse(self):
        seq = get_e_sequent("euclid-I.48")
        # Converse: conclusion should be a right angle
        assert "RightAngle" in seq or "right" in seq.lower() or "∠" in seq
