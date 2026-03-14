"""
test_geocoq_compat.py — Phase 10.3: GeoCoq Statement Comparison Tests.

Validates that our System E library entries align with GeoCoq's formulations
of Euclid's Book I propositions.

Reference: IMPLEMENTATION_PLAN.md §10.3, GeoCoq Elements/Statements/Book_1.v
"""
from __future__ import annotations

import pytest


# ═══════════════════════════════════════════════════════════════════════
# NAME MAPPING TESTS
# ═══════════════════════════════════════════════════════════════════════

class TestNameMappings:
    """Test our-name ↔ GeoCoq-name conversion."""

    def test_our_name_to_geocoq_prop_i1(self):
        from verifier.geocoq_compat import our_name_to_geocoq
        assert our_name_to_geocoq("Prop.I.1") == "proposition_1"

    def test_our_name_to_geocoq_prop_i47(self):
        from verifier.geocoq_compat import our_name_to_geocoq
        assert our_name_to_geocoq("Prop.I.47") == "proposition_47"

    def test_our_name_to_geocoq_all_48(self):
        from verifier.geocoq_compat import our_name_to_geocoq
        for i in range(1, 49):
            result = our_name_to_geocoq(f"Prop.I.{i}")
            assert result == f"proposition_{i}", f"Prop.I.{i} mapped wrong"

    def test_geocoq_to_our_name_prop_1(self):
        from verifier.geocoq_compat import geocoq_to_our_name
        assert geocoq_to_our_name("proposition_1") == "Prop.I.1"

    def test_geocoq_to_our_name_all_48(self):
        from verifier.geocoq_compat import geocoq_to_our_name
        for i in range(1, 49):
            result = geocoq_to_our_name(f"proposition_{i}")
            assert result == f"Prop.I.{i}"

    def test_unknown_name_returns_none(self):
        from verifier.geocoq_compat import our_name_to_geocoq
        assert our_name_to_geocoq("Prop.I.99") is None

    def test_roundtrip_all_48(self):
        from verifier.geocoq_compat import our_name_to_geocoq, geocoq_to_our_name
        for i in range(1, 49):
            our = f"Prop.I.{i}"
            gc = our_name_to_geocoq(our)
            back = geocoq_to_our_name(gc)
            assert back == our


# ═══════════════════════════════════════════════════════════════════════
# PREDICATE MAPPING TESTS
# ═══════════════════════════════════════════════════════════════════════

class TestPredicateMappings:
    """Test predicate name mappings are complete and consistent."""

    def test_e_predicates_non_empty(self):
        from verifier.geocoq_compat import E_PREDICATE_MAPPINGS
        assert len(E_PREDICATE_MAPPINGS) >= 10

    def test_all_predicates_have_geocoq_names(self):
        from verifier.geocoq_compat import ALL_PREDICATE_MAPPINGS
        for pm in ALL_PREDICATE_MAPPINGS:
            assert pm.geocoq_name, f"{pm.our_name} missing GeoCoq name"
            assert pm.geocoq_module.endswith(".v"), (
                f"{pm.our_name} bad module: {pm.geocoq_module}"
            )


# ═══════════════════════════════════════════════════════════════════════
# AXIOM MAPPING TESTS
# ═══════════════════════════════════════════════════════════════════════

class TestAxiomMappings:
    """Test axiom name mappings."""

    def test_e_axiom_groups_mapped(self):
        from verifier.geocoq_compat import E_AXIOM_MAPPINGS
        names = {m.our_name for m in E_AXIOM_MAPPINGS}
        for expected in ["Construction", "Diagrammatic", "Metric",
                         "Transfer", "SAS Superposition"]:
            assert expected in names, f"Missing E axiom group: {expected}"


# ═══════════════════════════════════════════════════════════════════════
# PROPOSITION COMPARISON STRUCTURE TESTS
# ═══════════════════════════════════════════════════════════════════════

class TestPropositionComparisons:
    """Test the 48 proposition comparison records."""

    def test_exactly_48_comparisons(self):
        from verifier.geocoq_compat import PROPOSITION_COMPARISONS
        assert len(PROPOSITION_COMPARISONS) == 48

    def test_numbers_1_through_48(self):
        from verifier.geocoq_compat import PROPOSITION_COMPARISONS
        numbers = {p.number for p in PROPOSITION_COMPARISONS}
        assert numbers == set(range(1, 49))

    def test_all_have_euclid_description(self):
        from verifier.geocoq_compat import PROPOSITION_COMPARISONS
        for p in PROPOSITION_COMPARISONS:
            assert len(p.euclid_description) > 10, (
                f"{p.our_name} has empty description"
            )

    def test_constructions_have_existentials(self):
        from verifier.geocoq_compat import PROPOSITION_COMPARISONS
        constructions = [p for p in PROPOSITION_COMPARISONS
                         if p.kind == "construction"]
        assert len(constructions) >= 10  # I.1,2,3,9,10,11,12,22,23,31,...
        for p in constructions:
            assert p.has_existentials, (
                f"{p.our_name} is construction but has_existentials=False"
            )

    def test_kind_is_valid(self):
        from verifier.geocoq_compat import PROPOSITION_COMPARISONS
        for p in PROPOSITION_COMPARISONS:
            assert p.kind in ("construction", "theorem"), (
                f"{p.our_name} has invalid kind: {p.kind}"
            )

    def test_key_predicates_non_empty(self):
        from verifier.geocoq_compat import PROPOSITION_COMPARISONS
        for p in PROPOSITION_COMPARISONS:
            assert len(p.key_predicates) >= 1, (
                f"{p.our_name} has no key predicates"
            )

    def test_pythagorean_theorem_is_prop_47(self):
        from verifier.geocoq_compat import get_comparison
        c = get_comparison("Prop.I.47")
        assert c is not None
        assert "Pythagorean" in c.euclid_description or "hypotenuse" in c.euclid_description
        assert c.kind == "theorem"


# ═══════════════════════════════════════════════════════════════════════
# E LIBRARY ALIGNMENT TESTS
# ═══════════════════════════════════════════════════════════════════════

class TestELibraryAlignment:
    """Validate E library against GeoCoq reference descriptions."""

    def test_e_library_has_all_48(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        assert len(E_THEOREM_LIBRARY) == 48

    def test_e_library_alignment_no_issues(self):
        """validate_library_alignment() returns no issues."""
        from verifier.geocoq_compat import validate_library_alignment
        issues = validate_library_alignment()
        assert issues == [], f"Alignment issues: {issues}"

    def test_constructions_have_exists_vars(self):
        """Every construction proposition has ≥1 existential variable in E."""
        from verifier.geocoq_compat import PROPOSITION_COMPARISONS
        from verifier.e_library import E_THEOREM_LIBRARY
        for comp in PROPOSITION_COMPARISONS:
            if comp.kind == "construction":
                thm = E_THEOREM_LIBRARY[comp.our_name]
                assert len(thm.sequent.exists_vars) >= 1, (
                    f"{comp.our_name}: construction with no ∃ vars"
                )

    def test_sas_is_theorem_not_construction(self):
        """I.4 (SAS) is a theorem (no construction step needed)."""
        from verifier.geocoq_compat import get_comparison
        from verifier.e_library import E_THEOREM_LIBRARY
        comp = get_comparison("Prop.I.4")
        assert comp.kind == "theorem"
        thm = E_THEOREM_LIBRARY["Prop.I.4"]
        assert len(thm.sequent.exists_vars) == 0

    def test_prop_i1_structure(self):
        """I.1 (equilateral triangle): 1 hyp, ≥2 conclusions, ∃c."""
        from verifier.e_library import E_THEOREM_LIBRARY
        seq = E_THEOREM_LIBRARY["Prop.I.1"].sequent
        assert len(seq.hypotheses) >= 1
        assert len(seq.conclusions) >= 2
        assert len(seq.exists_vars) == 1

    def test_prop_i47_structure(self):
        """I.47 (Pythagorean): theorem, ≥3 hyps, ≥1 conclusion, 6 evars."""
        from verifier.e_library import E_THEOREM_LIBRARY
        seq = E_THEOREM_LIBRARY["Prop.I.47"].sequent
        assert len(seq.hypotheses) >= 3
        assert len(seq.conclusions) >= 1
        # 6 existential vars for the square vertices (d,e,f,g,h,k)
        assert len(seq.exists_vars) == 6



