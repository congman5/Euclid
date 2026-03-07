"""
Tests for the answer key migration (Phase 6.5.2).

Validates that all 48 legacy answer keys are correctly migrated to
System E literal format with no opaque/untranslated literals.
"""
import json
from pathlib import Path

import pytest

from verifier.answer_key_migrator import (
    migrate_answer_key, migrate_all, translate_predicate, _VarTracker,
    _parse_pred, _split_args, _parse_magnitude_term,
)


# ═══════════════════════════════════════════════════════════════════════
# Fixture: load answer keys
# ═══════════════════════════════════════════════════════════════════════

@pytest.fixture(scope="module")
def legacy_keys():
    path = Path("legacy JS/answer-keys.json")
    if not path.exists():
        pytest.skip("legacy JS/answer-keys.json not present (migration already complete)")
    with open(path, encoding="utf-8") as f:
        return json.load(f)


@pytest.fixture(scope="module")
def migrated_keys():
    path = Path("answer-keys-e.json")
    with open(path, encoding="utf-8") as f:
        return json.load(f)


# ═══════════════════════════════════════════════════════════════════════
# Helper: detect opaque literals
# ═══════════════════════════════════════════════════════════════════════

def _has_opaque(obj) -> bool:
    """Recursively check if any dict has type/atom == 'opaque'."""
    if isinstance(obj, dict):
        if obj.get("type") == "opaque" or obj.get("atom") == "opaque":
            return True
        return any(_has_opaque(v) for v in obj.values())
    if isinstance(obj, list):
        return any(_has_opaque(v) for v in obj)
    return False


# ═══════════════════════════════════════════════════════════════════════
# Structural tests
# ═══════════════════════════════════════════════════════════════════════

class TestMigratedFileStructure:
    """Validate the overall migrated JSON structure."""

    def test_file_exists(self):
        assert Path("answer-keys-e.json").exists()

    def test_has_48_keys(self, migrated_keys):
        count = sum(1 for k in migrated_keys if k.startswith("euclid-"))
        assert count == 48

    def test_all_keys_have_name(self, migrated_keys):
        for k, v in migrated_keys.items():
            if not k.startswith("euclid-"):
                continue
            assert "name" in v, f"{k} missing 'name'"
            assert v["name"].startswith("Prop.I.")

    def test_all_keys_have_variables(self, migrated_keys):
        for k, v in migrated_keys.items():
            if not k.startswith("euclid-"):
                continue
            assert "variables" in v, f"{k} missing 'variables'"
            assert len(v["variables"]) > 0, f"{k} has empty variables"

    def test_all_keys_have_premises(self, migrated_keys):
        for k, v in migrated_keys.items():
            if not k.startswith("euclid-"):
                continue
            assert "premises" in v, f"{k} missing 'premises'"

    def test_all_keys_have_proof_steps(self, migrated_keys):
        for k, v in migrated_keys.items():
            if not k.startswith("euclid-"):
                continue
            assert "proof_steps" in v, f"{k} missing 'proof_steps'"
            assert len(v["proof_steps"]) > 0, f"{k} has no proof steps"

    def test_all_keys_have_conclusion(self, migrated_keys):
        for k, v in migrated_keys.items():
            if not k.startswith("euclid-"):
                continue
            assert "conclusion" in v, f"{k} missing 'conclusion'"
            assert len(v["conclusion"]) > 0, f"{k} has empty conclusion"


# ═══════════════════════════════════════════════════════════════════════
# No-opaque validation — every key fully translated
# ═══════════════════════════════════════════════════════════════════════

class TestNoOpaqueLiterals:
    """Every answer key must be fully translated with zero opaque terms."""

    def test_no_opaque_in_premises(self, migrated_keys):
        for k, v in migrated_keys.items():
            if not k.startswith("euclid-"):
                continue
            assert not _has_opaque(v.get("premises", [])), (
                f"{k} premises contain opaque literals"
            )

    def test_no_opaque_in_proof_steps(self, migrated_keys):
        for k, v in migrated_keys.items():
            if not k.startswith("euclid-"):
                continue
            for i, step in enumerate(v.get("proof_steps", [])):
                assert not _has_opaque(step.get("e_literals", [])), (
                    f"{k} step {i} has opaque literals: {step['text']}"
                )

    def test_no_opaque_in_conclusions(self, migrated_keys):
        for k, v in migrated_keys.items():
            if not k.startswith("euclid-"):
                continue
            assert not _has_opaque(v.get("conclusion", [])), (
                f"{k} conclusion contains opaque literals"
            )


# ═══════════════════════════════════════════════════════════════════════
# Specific proposition validations
# ═══════════════════════════════════════════════════════════════════════

class TestSpecificPropositions:
    """Spot-check known propositions for correct translation."""

    def test_i1_equilateral(self, migrated_keys):
        """I.1: premise a≠b, conclusion has segment equalities."""
        entry = migrated_keys["euclid-I.1"]
        assert entry["name"] == "Prop.I.1"
        # Premise: a ≠ b
        assert len(entry["premises"]) == 1
        p = entry["premises"][0]
        assert p["atom"] == "equals"
        assert p["positive"] is False

    def test_i4_sas(self, migrated_keys):
        """I.4: conclusion is Congruent → 6 literals."""
        entry = migrated_keys["euclid-I.4"]
        conc = entry["conclusion"]
        # Congruent(A,B,C,D,E,F) → 6 equalities
        assert len(conc) == 6
        for lit in conc:
            assert lit["atom"] == "equals"

    def test_i7_point_equality(self, migrated_keys):
        """I.7: conclusion Equal(C, D) → point equality c = d."""
        entry = migrated_keys["euclid-I.7"]
        conc = entry["conclusion"]
        assert len(conc) == 1
        assert conc[0]["left"] == "c"
        assert conc[0]["right"] == "d"
        assert conc[0]["positive"] is True

    def test_i11_right_angle(self, migrated_keys):
        """I.11: conclusion is a right angle."""
        entry = migrated_keys["euclid-I.11"]
        conc = entry["conclusion"]
        assert len(conc) == 1
        assert conc[0]["atom"] == "equals"
        assert conc[0]["right"]["type"] == "right_angle"

    def test_i27_parallel(self, migrated_keys):
        """I.27: conclusion is ¬intersects (parallel)."""
        entry = migrated_keys["euclid-I.27"]
        conc = entry["conclusion"]
        assert len(conc) == 1
        assert conc[0]["atom"] == "intersects"
        assert conc[0]["positive"] is False

    def test_i35_equal_area(self, migrated_keys):
        """I.35: conclusion is area equality for parallelograms."""
        entry = migrated_keys["euclid-I.35"]
        conc = entry["conclusion"]
        assert len(conc) == 1
        assert conc[0]["atom"] == "equals"

    def test_i46_square(self, migrated_keys):
        """I.46: conclusion is Square → 4 sides + 4 right angles."""
        entry = migrated_keys["euclid-I.46"]
        conc = entry["conclusion"]
        # Square(A,D,E,B) → 3 side equalities + 4 right angles = 7
        assert len(conc) == 7

    def test_i47_pythagorean(self, migrated_keys):
        """I.47: conclusion is area equality with MagAdd."""
        entry = migrated_keys["euclid-I.47"]
        conc = entry["conclusion"]
        assert len(conc) == 1
        assert conc[0]["atom"] == "equals"
        # Left side: SqBCDE as MagAdd
        assert conc[0]["left"]["type"] == "mag_add"
        # Right side: SumArea(SqABFG, SqACHK) as MagAdd
        assert conc[0]["right"]["type"] == "mag_add"

    def test_i48_right_angle_converse(self, migrated_keys):
        """I.48: conclusion is a right angle."""
        entry = migrated_keys["euclid-I.48"]
        conc = entry["conclusion"]
        assert len(conc) == 1
        assert conc[0]["atom"] == "equals"
        assert conc[0]["right"]["type"] == "right_angle"


# ═══════════════════════════════════════════════════════════════════════
# Parser unit tests
# ═══════════════════════════════════════════════════════════════════════

class TestParser:
    """Unit tests for the predicate/magnitude parsers."""

    def test_split_args_simple(self):
        assert _split_args("A, B, C") == ["A", "B", "C"]

    def test_split_args_nested(self):
        assert _split_args("SumAngle(CBA, ABD), TwoRight") == [
            "SumAngle(CBA, ABD)", "TwoRight"
        ]

    def test_parse_pred_empty_args(self):
        name, args = _parse_pred("Contradiction()")
        assert name == "Contradiction"
        assert args == []  # empty parens → no args

    def test_parse_pred_nested(self):
        name, args = _parse_pred("Equal(SumAngle(CBA, ABD), TwoRight)")
        assert name == "Equal"
        assert len(args) == 2
        assert args[0] == "SumAngle(CBA, ABD)"
        assert args[1] == "TwoRight"

    def test_translate_segment(self):
        vt = _VarTracker()
        result = translate_predicate("Segment(A, B)", vt)
        assert len(result) == 1
        assert result[0]["atom"] == "equals"
        assert result[0]["positive"] is False

    def test_translate_between(self):
        vt = _VarTracker()
        result = translate_predicate("Between(A, B, C)", vt)
        assert len(result) == 1
        assert result[0]["atom"] == "between"

    def test_translate_circle(self):
        vt = _VarTracker()
        result = translate_predicate("Circle(A, B)", vt)
        assert len(result) == 2
        assert result[0]["atom"] == "center"
        assert result[1]["atom"] == "on"

    def test_translate_congruent(self):
        vt = _VarTracker()
        result = translate_predicate("Congruent(A, B, C, D, E, F)", vt)
        assert len(result) == 6

    def test_translate_assume_unwraps(self):
        vt = _VarTracker()
        result = translate_predicate("Assume(Longer(AB, CD))", vt)
        assert len(result) >= 1
        assert result[0]["atom"] == "less_than"

    def test_magnitude_angle_3letter(self):
        vt = _VarTracker()
        term = _parse_magnitude_term("CBA", vt)
        assert term["type"] == "angle"
        assert term["p1"] == "c"
        assert term["vertex"] == "b"
        assert term["p3"] == "a"

    def test_magnitude_sum_angle_6arg(self):
        vt = _VarTracker()
        term = _parse_magnitude_term("SumAngle(A, B, C, D, E, F)", vt)
        assert term["type"] == "mag_add"

    def test_magnitude_two_right(self):
        vt = _VarTracker()
        term = _parse_magnitude_term("TwoRight", vt)
        assert term["type"] == "mag_add"
        assert term["left"]["type"] == "right_angle"

    def test_magnitude_rect(self):
        vt = _VarTracker()
        term = _parse_magnitude_term("RectBDLM", vt)
        assert term["type"] == "mag_add"

    def test_magnitude_half_par(self):
        vt = _VarTracker()
        term = _parse_magnitude_term("HalfParEBCA", vt)
        assert term["type"] == "area"


# ═══════════════════════════════════════════════════════════════════════
# Round-trip: migrate_answer_key matches the generated file
# ═══════════════════════════════════════════════════════════════════════

class TestRoundTrip:
    """Verify that migrate_answer_key produces the same results as the file."""

    def test_i1_round_trip(self, legacy_keys, migrated_keys):
        result = migrate_answer_key("euclid-I.1", legacy_keys["euclid-I.1"])
        assert result["name"] == migrated_keys["euclid-I.1"]["name"]
        assert result["title"] == migrated_keys["euclid-I.1"]["title"]
        assert len(result["premises"]) == len(migrated_keys["euclid-I.1"]["premises"])
        assert len(result["proof_steps"]) == len(migrated_keys["euclid-I.1"]["proof_steps"])
        assert len(result["conclusion"]) == len(migrated_keys["euclid-I.1"]["conclusion"])
