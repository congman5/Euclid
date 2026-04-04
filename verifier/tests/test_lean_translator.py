"""
test_lean_translator.py — Tests for the LeanEuclid→System E translator pipeline.

Tests cover:
  - lean_parser: parsing .lean files into IR
  - lean_mapping: rule lookup and classification
  - lean_translator: translating parsed proofs to System E steps
  - lean_to_python: Python code generation
  - lean_to_euclid_json: JSON output
"""
import pytest
import os
from pathlib import Path

# ── lean_parser tests ─────────────────────────────────────────────────

from verifier.lean_parser import (
    TacticKind, LeanTactic, LeanTheoremSig, LeanProof,
    parse_lean_source, parse_lean_file,
    extract_prop_number, prop_system_e_name,
)


LEAN_REFERENCE_DIR = Path(__file__).resolve().parent.parent.parent / "lean_reference"


class TestExtractPropNumber:
    def test_basic(self):
        assert extract_prop_number("proposition_16") == 16

    def test_large(self):
        assert extract_prop_number("proposition_48") == 48

    def test_none(self):
        assert extract_prop_number("some_lemma") is None


class TestPropSystemEName:
    def test_format(self):
        assert prop_system_e_name(1) == "Prop.I.1"
        assert prop_system_e_name(47) == "Prop.I.47"


class TestParseLeanSource:
    """Parse Lean source text into LeanProof objects."""

    SAMPLE_LEAN = """\
theorem proposition_16 : ∀ (a b c d : Point) (L M : Line),
    formTriangle a b c →
    distinctPointsOnLine a b M →
    between a b d →
    ¬ (∠ a:b:c = ∠ b:c:d) := by
  euclid_intros
  euclid_apply (midpoint_of_segment b c) as e
  euclid_apply (extend_point_to_length b e b e) as f
  euclid_assert (△ b:c:e ≅ △ f:e:c)
  euclid_finish
"""

    def test_parse_finds_theorem(self):
        proofs = parse_lean_source(self.SAMPLE_LEAN)
        assert len(proofs) >= 1

    def test_theorem_name(self):
        proofs = parse_lean_source(self.SAMPLE_LEAN)
        assert proofs[0].theorem_name == "proposition_16"

    def test_tactic_count(self):
        proofs = parse_lean_source(self.SAMPLE_LEAN)
        # Should find: euclid_intros, euclid_apply x2, euclid_assert, euclid_finish
        kinds = [t.kind for t in proofs[0].tactics]
        assert TacticKind.EUCLID_APPLY in kinds
        assert TacticKind.EUCLID_FINISH in kinds


# ── lean_mapping tests ────────────────────────────────────────────────

from verifier.lean_mapping import (
    RuleCategory, lookup_rule, classify_rule, PROP_DEPS,
    ALL_RULES, CONSTRUCTION_RULES, PROPOSITION_RULES,
    category_to_step_kind_name,
)


class TestLookupRule:
    def test_known_construction(self):
        r = lookup_rule("line_from_points")
        assert r is not None
        assert r.category == RuleCategory.CONSTRUCTION

    def test_known_proposition(self):
        r = lookup_rule("proposition_4")
        assert r is not None
        assert r.category == RuleCategory.PROPOSITION

    def test_unknown(self):
        r = lookup_rule("nonexistent_rule_xyz")
        assert r is None


class TestClassifyRule:
    def test_construction(self):
        cat = classify_rule("line_from_points")
        assert cat == RuleCategory.CONSTRUCTION

    def test_proposition(self):
        cat = classify_rule("proposition_16")
        assert cat == RuleCategory.PROPOSITION


class TestPropDeps:
    def test_prop_16_deps(self):
        deps = PROP_DEPS.get(16, [])
        assert isinstance(deps, list)

    def test_prop_47_deps(self):
        deps = PROP_DEPS.get(47, [])
        assert isinstance(deps, list)
        assert len(deps) > 0


class TestCategoryToStepKindName:
    def test_construction(self):
        name = category_to_step_kind_name(RuleCategory.CONSTRUCTION)
        assert "CONSTRUCTION" in name

    def test_proposition(self):
        name = category_to_step_kind_name(RuleCategory.PROPOSITION)
        assert "THEOREM" in name


# ── lean_translator tests ────────────────────────────────────────────

from verifier.lean_translator import (
    LeanToSystemETranslator,
    TranslationResult,
    translate_lean_file,
    translate_all_propositions,
    compare_with_existing,
)
from verifier.e_ast import StepKind


@pytest.mark.skipif(
    not (LEAN_REFERENCE_DIR / "Prop16.lean").exists(),
    reason="lean_reference/Prop16.lean not found"
)
class TestTranslateLeanFile:
    """Test translating actual .lean files."""

    def test_translate_prop16(self):
        result = translate_lean_file(str(LEAN_REFERENCE_DIR / "Prop16.lean"))
        assert result.prop_number == 16
        assert result.prop_name == "Prop.I.16"
        assert len(result.steps) > 0

    def test_translate_prop47(self):
        path = LEAN_REFERENCE_DIR / "Prop47.lean"
        if not path.exists():
            pytest.skip("Prop47.lean not found")
        result = translate_lean_file(str(path))
        assert result.prop_number == 47
        assert len(result.steps) > 0

    def test_steps_have_valid_kinds(self):
        result = translate_lean_file(str(LEAN_REFERENCE_DIR / "Prop16.lean"))
        for ts in result.steps:
            assert isinstance(ts.step.kind, StepKind)
            assert ts.step.id > 0


@pytest.mark.skipif(
    not (LEAN_REFERENCE_DIR / "Prop16.lean").exists(),
    reason="lean_reference directory not found"
)
class TestTranslateAllPropositions:
    def test_range_16_to_20(self):
        report = translate_all_propositions(
            str(LEAN_REFERENCE_DIR), prop_range=(16, 20)
        )
        assert len(report.results) == 5
        for r in report.results:
            assert r.prop_number >= 16
            assert r.prop_number <= 20


@pytest.mark.skipif(
    not (LEAN_REFERENCE_DIR / "Prop16.lean").exists(),
    reason="lean_reference directory not found"
)
class TestCompareWithExisting:
    def test_compare_prop16(self):
        result = translate_lean_file(str(LEAN_REFERENCE_DIR / "Prop16.lean"))
        diff = compare_with_existing(result)
        assert diff["status"] in ("compared", "no_existing")
        assert diff["prop"] == "Prop.I.16"


# ── lean_to_python tests ─────────────────────────────────────────────

from verifier.lean_to_python import (
    translation_to_python,
    translation_to_python_with_comments,
    generate_proofs_module,
    _literal_to_src,
    _atom_to_src,
    _term_to_src,
)
from verifier.e_ast import (
    Literal, On, Equals, SegmentTerm, AngleTerm, Sort,
)


class TestLiteralToSrc:
    def test_pos_on(self):
        lit = Literal(On("a", "L"), polarity=True)
        src = _literal_to_src(lit)
        assert src == '_pos(On("a", "L"))'

    def test_neg_equals(self):
        lit = Literal(Equals("a", "b"), polarity=False)
        src = _literal_to_src(lit)
        assert "_neg(" in src
        assert "Equals(" in src

    def test_segment_equals(self):
        lit = Literal(
            Equals(SegmentTerm("a", "b"), SegmentTerm("c", "d")),
            polarity=True,
        )
        src = _literal_to_src(lit)
        assert "SegmentTerm" in src
        assert '_pos(' in src


class TestAtomToSrc:
    def test_on(self):
        assert _atom_to_src(On("p", "L")) == 'On("p", "L")'

    def test_equals_segment(self):
        src = _atom_to_src(Equals(SegmentTerm("a", "b"), SegmentTerm("c", "d")))
        assert 'Equals(SegmentTerm("a", "b"), SegmentTerm("c", "d"))' == src


@pytest.mark.skipif(
    not (LEAN_REFERENCE_DIR / "Prop16.lean").exists(),
    reason="lean_reference/Prop16.lean not found"
)
class TestTranslationToPython:
    def test_generates_function(self):
        result = translate_lean_file(str(LEAN_REFERENCE_DIR / "Prop16.lean"))
        code = translation_to_python(result)
        assert "def _make_prop_i16():" in code
        assert "_proof_from_sequent" in code

    def test_generates_module(self):
        result = translate_lean_file(str(LEAN_REFERENCE_DIR / "Prop16.lean"))
        module = generate_proofs_module([result])
        assert "TRANSLATED_PROOFS" in module
        assert "from __future__" in module


# ── lean_to_euclid_json tests ────────────────────────────────────────

from verifier.lean_to_euclid_json import (
    literal_to_text,
    translation_to_euclid_json,
)


class TestLiteralToText:
    def test_on(self):
        lit = Literal(On("a", "L"), polarity=True)
        assert literal_to_text(lit) == "on(a, L)"

    def test_negated(self):
        lit = Literal(Equals("a", "b"), polarity=False)
        text = literal_to_text(lit)
        assert text.startswith("¬(")


@pytest.mark.skipif(
    not (LEAN_REFERENCE_DIR / "Prop16.lean").exists(),
    reason="lean_reference/Prop16.lean not found"
)
class TestTranslationToEuclidJson:
    def test_produces_valid_json_structure(self):
        result = translate_lean_file(str(LEAN_REFERENCE_DIR / "Prop16.lean"))
        data = translation_to_euclid_json(result)
        assert "proof" in data
        assert "name" in data["proof"]
        assert "steps" in data["proof"]
        assert "16" in data["proof"]["name"]


# ── proof_synthesizer tests ───────────────────────────────────────────

from verifier.proof_synthesizer import (
    synthesize_proof, synthesize_and_verify, SynthesisResult, VarMapper,
)


@pytest.mark.skipif(
    not (LEAN_REFERENCE_DIR / "Prop17.lean").exists(),
    reason="lean_reference/Prop17.lean not found"
)
class TestVarMapper:
    def test_maps_lean_lines_to_elib(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        seq = E_THEOREM_LIBRARY["Prop.I.17"].sequent
        proofs = parse_lean_file(str(LEAN_REFERENCE_DIR / "Prop17.lean"))
        vm = VarMapper(seq, proofs[0])
        # AB should map to L (e_library line through a,b)
        assert vm.mv("AB") == "L"
        # BC should be an extra line (not in e_library)
        assert "bc" in vm.extra_lines
        # Point names should be identity
        assert vm.mv("a") == "a"
        assert vm.mv("b") == "b"
        assert vm.mv("c") == "c"

    def test_extra_line_points(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        seq = E_THEOREM_LIBRARY["Prop.I.17"].sequent
        proofs = parse_lean_file(str(LEAN_REFERENCE_DIR / "Prop17.lean"))
        vm = VarMapper(seq, proofs[0])
        bc_elib = vm.extra_lines["bc"]
        assert bc_elib in vm.extra_line_points
        pts = vm.extra_line_points[bc_elib]
        assert set(pts) == {"b", "c"}


@pytest.mark.skipif(
    not (LEAN_REFERENCE_DIR / "Prop17.lean").exists(),
    reason="lean_reference/Prop17.lean not found"
)
class TestSynthesizer:
    def test_synthesis_succeeds(self):
        result = translate_lean_file(
            str(LEAN_REFERENCE_DIR / "Prop17.lean"))
        proofs = parse_lean_file(
            str(LEAN_REFERENCE_DIR / "Prop17.lean"))
        sr = synthesize_proof(result, proofs[0])
        assert sr.success
        assert sr.step_count > 0
        assert sr.euclid_json is not None

    def test_json_structure(self):
        result = translate_lean_file(
            str(LEAN_REFERENCE_DIR / "Prop17.lean"))
        proofs = parse_lean_file(
            str(LEAN_REFERENCE_DIR / "Prop17.lean"))
        sr = synthesize_proof(result, proofs[0])
        proof = sr.euclid_json["proof"]
        assert proof["name"] == "Prop.I.17"
        assert len(proof["premises"]) == 6
        assert "steps" in proof
        for step in proof["steps"]:
            assert "lineNumber" in step
            assert "text" in step
            assert "justification" in step
            assert "dependencies" in step

    @pytest.mark.slow
    def test_verifier_accepts_i17(self):
        """Full end-to-end: synthesize I.17 and verify it passes."""
        result = translate_lean_file(
            str(LEAN_REFERENCE_DIR / "Prop17.lean"))
        proofs = parse_lean_file(
            str(LEAN_REFERENCE_DIR / "Prop17.lean"))
        sr, vr = synthesize_and_verify(result, proofs[0])
        assert sr.success
        assert vr is not None
        assert vr.accepted, (
            "Verifier rejected: " +
            str({lid: lr.errors
                 for lid, lr in vr.line_results.items()
                 if not lr.valid})
        )
