"""
test_proof_builder.py — Tests for the EuclidProofBuilder.

Validates the builder by:
1. Reconstructing solved Proposition I.15 with the builder
2. Verifying it passes verify_e_proof_json
3. Testing builder mechanics (line numbering, etc.)
"""
import pytest
import json


class TestProofBuilderMechanics:
    """Test basic builder mechanics."""

    def test_premise_numbering(self):
        from verifier.euclid_proof_builder import EuclidProofBuilder
        b = EuclidProofBuilder("Test")
        b.premise("¬(a = b)")
        b.premise("on(a, L)")
        b.premise("on(b, L)")
        assert b.line == 4  # next step would be line 4

    def test_step_numbering(self):
        from verifier.euclid_proof_builder import EuclidProofBuilder
        b = EuclidProofBuilder("Test")
        b.premise("¬(a = b)")
        ln = b.let_line("on(a, L), on(b, L)", refs=[1])
        assert ln == 2
        ln2 = b.axiom("ab = ba", "M3 — Symmetry", refs=[])
        assert ln2 == 3

    def test_build_has_correct_structure(self):
        from verifier.euclid_proof_builder import EuclidProofBuilder
        b = EuclidProofBuilder("Prop.I.1")
        b.premise("¬(a = b)")
        b.goal("ab = ac")
        b.declare_points("a", "b")
        doc = b.build()
        assert doc["format"] == "euclid-proof"
        assert doc["proof"]["name"] == "Prop.I.1"
        assert doc["proof"]["premises"] == ["¬(a = b)"]
        assert doc["proof"]["goal"] == "ab = ac"
        assert doc["proof"]["declarations"]["points"] == ["a", "b"]

    def test_last_property(self):
        from verifier.euclid_proof_builder import EuclidProofBuilder
        b = EuclidProofBuilder("Test")
        b.premise("¬(a = b)")
        b.premise("on(a, L)")
        assert b.last == 2  # last premise line
        b.let_line("on(a, M), on(b, M)", refs=[1])
        assert b.last == 3


class TestProofBuilderI15:
    """Reconstruct solved Proposition I.15 and verify it passes."""

    def _build_i15(self):
        """Build I.15 proof matching the solved_proofs version exactly."""
        from verifier.euclid_proof_builder import EuclidProofBuilder

        b = EuclidProofBuilder("Prop.I.15")
        # 9 premises (lines 1-9)
        b.premises(
            "on(a, L)",       # 1
            "on(b, L)",       # 2
            "on(c, M)",       # 3
            "on(d, M)",       # 4
            "on(e, L)",       # 5
            "on(e, M)",       # 6
            "between(a, e, b)",  # 7
            "between(c, e, d)",  # 8
            "¬(L = M)",       # 9
        )
        b.goal("∠aec = ∠bed")
        b.declare_points("a", "b", "c", "d", "e")
        b.declare_lines("L", "M")

        # Step 10: ¬(c = e) from between(c, e, d)
        b.betweenness("1b", "¬(c = e)", refs=[8])
        # Step 11: ¬on(c, L)
        b.generality("1", "¬on(c, L)", refs=[5, 6, 3, 9, 10])
        # Step 12: between(b, e, a) — reverse of between(a, e, b)
        b.betweenness("1a", "between(b, e, a)", refs=[7])
        # Step 13: ¬(b = e)
        b.betweenness("1b", "¬(b = e)", refs=[12])
        # Step 14: ¬on(b, M)
        b.generality("1", "¬on(b, M)", refs=[5, 6, 2, 9, 13])
        # Step 15: supplementary angles on line L
        ln15 = b.angle_transfer("6",
                                "(∠bec + ∠cea) = (∟ + ∟)",
                                refs=[2, 1, 12, 11, 10])
        # Step 16: supplementary angles on line M
        ln16 = b.angle_transfer("6",
                                "(∠ceb + ∠bed) = (∟ + ∟)",
                                refs=[3, 4, 8, 14, 13])
        # Step 17: transitivity
        b.cn1("(∠bec + ∠cea) = (∠ceb + ∠bed)", refs=[ln15, ln16])
        # Step 18: subtraction → vertical angles equal
        b.cn3("∠aec = ∠bed", refs=[17])

        return b

    def test_i15_builds_valid_json(self):
        """Verify I.15 produces valid JSON structure."""
        b = self._build_i15()
        doc = b.build()
        assert doc["proof"]["name"] == "Prop.I.15"
        assert len(doc["proof"]["premises"]) == 9
        assert len(doc["proof"]["steps"]) == 9  # steps 10-18
        assert doc["proof"]["steps"][0]["lineNumber"] == 10
        assert doc["proof"]["steps"][-1]["lineNumber"] == 18
        assert doc["proof"]["steps"][-1]["text"] == "∠aec = ∠bed"

    def test_i15_passes_verifier(self):
        """Verify I.15 passes the real verifier."""
        b = self._build_i15()
        result = b.verify()
        if not result.accepted:
            # Print diagnostic info
            for lid, lr in result.line_results.items():
                if not lr.valid:
                    print(f"  Line {lid}: FAIL — {lr.errors}")
            for err in result.errors:
                print(f"  Error: {err}")
        assert result.accepted, (
            f"I.15 failed verification: {result.errors}")

    def test_i15_matches_solved_proof(self):
        """Compare builder output structure against the solved proof file."""
        b = self._build_i15()
        doc = b.build()
        # Check steps match expected justifications
        justifications = [s["justification"] for s in doc["proof"]["steps"]]
        expected = [
            "Betweenness 1b", "Generality 1", "Betweenness 1a",
            "Betweenness 1b", "Generality 1", "Angle transfer 6",
            "Angle transfer 6", "CN1 — Transitivity", "CN3 — Subtraction",
        ]
        assert justifications == expected


class TestProofBuilderI1:
    """Reconstruct solved Proposition I.1 and verify it passes."""

    def _build_i1(self):
        from verifier.euclid_proof_builder import EuclidProofBuilder

        b = EuclidProofBuilder("Prop.I.1")
        b.premise("¬(a = b)")
        b.goal("ab = ac, ab = bc, ¬(c = a), ¬(c = b)")
        b.declare_points("A", "B")

        # Line 2: let-circle α centered at a through b
        b.let_circle("center(a, α), on(b, α)", refs=[1])
        # Line 3: let-circle β centered at b through a
        b.let_circle("center(b, β), on(a, β)", refs=[1])
        # Line 4: inside(a, α) — center is inside its circle
        b.generality("3", "inside(a, α)", refs=[2])
        # Line 5: inside(b, β) — center is inside its circle
        b.generality("3", "inside(b, β)", refs=[3])
        # Line 6: intersects(α, β)
        b.intersection_axiom("5", "intersects(α, β)", refs=[2, 3, 4, 5])
        # Line 7: c on both circles
        b.let_intersection_circle_circle_one(
            "on(c, α), on(c, β)", refs=[6])
        # Line 8: ac = ab (radii of α)
        b.segment_transfer("3b", "ac = ab", refs=[2, 7])
        # Line 9: bc = ba (radii of β)
        b.segment_transfer("3b", "bc = ba", refs=[3, 7])
        # Line 10: ab = ba
        b.m3("ab = ba", refs=[])
        # Line 11: ab = ac
        b.cn1("ab = ac", refs=[8])
        # Line 12: ab = bc
        b.cn1("ab = bc", refs=[9, 10])
        # Line 13: ¬(c = a) — from nonzero radius
        b.m1("¬(c = a)", refs=[1, 8])
        # Line 14: ¬(c = b)
        b.m1("¬(c = b)", refs=[1, 9, 10])

        return b

    def test_i1_passes_verifier(self):
        """Verify I.1 passes the real verifier."""
        b = self._build_i1()
        result = b.verify()
        if not result.accepted:
            for lid, lr in result.line_results.items():
                if not lr.valid:
                    print(f"  Line {lid}: FAIL — {lr.errors}")
            for err in result.errors:
                print(f"  Error: {err}")
        assert result.accepted, (
            f"I.1 failed verification: {result.errors}")
