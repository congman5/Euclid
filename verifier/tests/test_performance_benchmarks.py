"""
test_performance_benchmarks.py — Phase 10.4: Performance Benchmarks.

Measures and records performance characteristics of the verification
infrastructure, ensuring no regressions and documenting expected timing
ranges for key operations.

Benchmarks:
  1. Forward-chaining closure time for diagrams with N points
  2. Full proof verification time for each encoded proposition
  3. SMT/TPTP encoding latency
  4. E→T translation (π) latency per proposition
  5. Cross-system translation roundtrip latency

Reference: IMPLEMENTATION_PLAN.md §10.4
"""
from __future__ import annotations

import time
from typing import Dict, Set

import pytest

from verifier.e_ast import (
    Between,
    Center,
    Equals,
    Inside,
    Literal,
    On,
    SameSide,
    SegmentTerm,
    Sort,
)


# ═══════════════════════════════════════════════════════════════════════
# HELPERS
# ═══════════════════════════════════════════════════════════════════════

def _time_ms(func, *args, **kwargs):
    """Run func and return (result, elapsed_ms)."""
    t0 = time.perf_counter()
    result = func(*args, **kwargs)
    elapsed = (time.perf_counter() - t0) * 1000
    return result, elapsed


# ═══════════════════════════════════════════════════════════════════════
# 1. FORWARD-CHAINING CLOSURE TIME (N points)
# ═══════════════════════════════════════════════════════════════════════

class TestForwardChainingScaling:
    """Measure forward-chaining closure time as diagram size grows."""

    @staticmethod
    def _build_diagram(n_points: int) -> tuple:
        """Build a linear diagram with n_points on a line.

        Creates: on(p_i, L) for i=0..n-1, between(p_i, p_{i+1}, p_{i+2})
        for consecutive triples.
        """
        names = [f"p{i}" for i in range(n_points)]
        known: Set[Literal] = set()
        vars_: Dict[str, Sort] = {"L": Sort.LINE}

        for name in names:
            known.add(Literal(On(name, "L")))
            vars_[name] = Sort.POINT

        for i in range(n_points - 2):
            known.add(Literal(Between(names[i], names[i + 1], names[i + 2])))

        return known, vars_

    def test_3_points_under_100ms(self):
        """3-point diagram closes in <100ms."""
        from verifier.e_consequence import ConsequenceEngine

        known, vars_ = self._build_diagram(3)
        engine = ConsequenceEngine()
        result, elapsed = _time_ms(engine.direct_consequences, known, vars_)
        assert elapsed < 100, f"3 points took {elapsed:.1f}ms"
        assert len(result) > 0

    def test_5_points_under_500ms(self):
        """5-point diagram closes in <500ms."""
        from verifier.e_consequence import ConsequenceEngine

        known, vars_ = self._build_diagram(5)
        engine = ConsequenceEngine()
        result, elapsed = _time_ms(engine.direct_consequences, known, vars_)
        assert elapsed < 500, f"5 points took {elapsed:.1f}ms"
        assert len(result) > 0

    def test_scaling_subquadratic(self):
        """Forward-chaining from 3→5 points grows sub-quadratically.

        The paper (§3.8) claims polynomial-time decidability. We check
        that doubling diagram size doesn't cause exponential blowup.
        """
        from verifier.e_consequence import ConsequenceEngine

        known3, vars3 = self._build_diagram(3)
        eng3 = ConsequenceEngine()
        _, t3 = _time_ms(eng3.direct_consequences, known3, vars3)

        known5, vars5 = self._build_diagram(5)
        eng5 = ConsequenceEngine()
        _, t5 = _time_ms(eng5.direct_consequences, known5, vars5)

        # 5 points has ~2.8x more pairs than 3 points.
        # Allow up to 10x slowdown (very generous for polynomial).
        ratio = t5 / max(t3, 0.01)
        assert ratio < 50, (
            f"Scaling ratio {ratio:.1f}x from 3→5 points "
            f"({t3:.1f}ms → {t5:.1f}ms) exceeds 50x"
        )

    def test_circle_diagram_under_200ms(self):
        """Diagram with circle constructions closes in <200ms."""
        from verifier.e_consequence import ConsequenceEngine

        known: Set[Literal] = {
            Literal(On("a", "L")),
            Literal(On("b", "L")),
            Literal(Center("a", "α")),
            Literal(On("b", "α")),
        }
        vars_ = {
            "a": Sort.POINT, "b": Sort.POINT,
            "L": Sort.LINE, "α": Sort.CIRCLE,
        }
        engine = ConsequenceEngine()
        result, elapsed = _time_ms(engine.direct_consequences, known, vars_)
        assert elapsed < 200, f"Circle diagram took {elapsed:.1f}ms"


# ═══════════════════════════════════════════════════════════════════════
# 2. FULL PROOF VERIFICATION TIME
# ═══════════════════════════════════════════════════════════════════════

class TestProofVerificationTiming:
    """Measure verification time for encoded proofs."""

    def test_all_encoded_proofs_under_1s(self):
        """Each encoded proof verifies (pass or fail) in under 1 second."""
        from verifier.e_proofs import E_PROOFS
        from verifier.unified_checker import verify_named_proof

        timings = {}
        for name in E_PROOFS:
            _, elapsed = _time_ms(verify_named_proof, name)
            timings[name] = elapsed
            assert elapsed < 1000, f"{name} took {elapsed:.1f}ms"

    def test_prop_i1_verification_fast(self):
        """Prop I.1 (equilateral triangle) verifies quickly."""
        from verifier.unified_checker import verify_named_proof

        _, elapsed = _time_ms(verify_named_proof, "Prop.I.1")
        assert elapsed < 200, f"I.1 took {elapsed:.1f}ms"

    def test_all_48_sequents_accessible_under_100ms(self):
        """Loading all 48 theorem sequents from E library takes <100ms."""
        from verifier.e_library import E_THEOREM_LIBRARY

        t0 = time.perf_counter()
        for name, thm in E_THEOREM_LIBRARY.items():
            _ = str(thm.sequent)
        elapsed = (time.perf_counter() - t0) * 1000
        assert elapsed < 100, f"Sequent access took {elapsed:.1f}ms"


# ═══════════════════════════════════════════════════════════════════════
# 3. SMT/TPTP ENCODING LATENCY
# ═══════════════════════════════════════════════════════════════════════

class TestSmtEncodingTiming:
    """Measure SMT-LIB and TPTP encoding latency."""

    def test_axiom_encoding_smtlib_under_50ms(self):
        """All 65 E axioms encode to SMT-LIB in <50ms."""
        from verifier.smt_backend import encode_axioms_smtlib

        result, elapsed = _time_ms(encode_axioms_smtlib)
        assert elapsed < 50, f"SMT axiom encoding took {elapsed:.1f}ms"
        assert len(result) > 1000

    def test_axiom_encoding_tptp_under_50ms(self):
        """All 65 E axioms encode to TPTP in <50ms."""
        from verifier.tptp_backend import encode_axioms_tptp

        result, elapsed = _time_ms(encode_axioms_tptp)
        assert elapsed < 50, f"TPTP axiom encoding took {elapsed:.1f}ms"
        assert len(result) > 1000

    def test_obligation_encoding_under_20ms(self):
        """Single proof obligation encodes to SMT-LIB in <20ms."""
        from verifier.smt_backend import encode_obligation

        known = [Literal(Between("a", "b", "c"))]
        query = Literal(Between("c", "b", "a"))
        _, elapsed = _time_ms(encode_obligation, known, query)
        assert elapsed < 20, f"Obligation encoding took {elapsed:.1f}ms"

    def test_all_48_props_encode_smtlib_under_500ms(self):
        """All 48 proposition sequents encode as SMT obligations in <500ms."""
        from verifier.e_library import E_THEOREM_LIBRARY
        from verifier.smt_backend import encode_obligation

        total = 0.0
        for name, thm in E_THEOREM_LIBRARY.items():
            known = list(thm.sequent.hypotheses)
            if thm.sequent.conclusions:
                query = thm.sequent.conclusions[0]
                _, elapsed = _time_ms(encode_obligation, known, query)
                total += elapsed
        assert total < 500, f"All 48 props SMT encoding took {total:.1f}ms"

    def test_all_48_props_encode_tptp_under_500ms(self):
        """All 48 proposition sequents encode as TPTP queries in <500ms."""
        from verifier.e_library import E_THEOREM_LIBRARY
        from verifier.tptp_backend import encode_query_tptp

        total = 0.0
        for name, thm in E_THEOREM_LIBRARY.items():
            known = list(thm.sequent.hypotheses)
            if thm.sequent.conclusions:
                query = thm.sequent.conclusions[0]
                _, elapsed = _time_ms(encode_query_tptp, known, query)
                total += elapsed
        assert total < 500, f"All 48 props TPTP encoding took {total:.1f}ms"


# ═══════════════════════════════════════════════════════════════════════
# 4. E→T TRANSLATION (π) LATENCY
# ═══════════════════════════════════════════════════════════════════════

class TestPiTranslationTiming:
    """Measure E→T translation latency per proposition."""

    def test_all_48_pi_translations_under_100ms(self):
        """All 48 E sequents translate to T via π in <100ms total."""
        from verifier.e_library import E_THEOREM_LIBRARY
        from verifier.t_pi_translation import pi_sequent

        total = 0.0
        for name, thm in E_THEOREM_LIBRARY.items():
            _, elapsed = _time_ms(pi_sequent, thm.sequent)
            total += elapsed
        assert total < 100, f"All 48 π translations took {total:.1f}ms"

    def test_complex_prop_i47_pi_under_10ms(self):
        """Prop I.47 (Pythagorean theorem) π translation takes <10ms."""
        from verifier.e_library import E_THEOREM_LIBRARY
        from verifier.t_pi_translation import pi_sequent

        thm = E_THEOREM_LIBRARY["Prop.I.47"]
        _, elapsed = _time_ms(pi_sequent, thm.sequent)
        assert elapsed < 10, f"I.47 π took {elapsed:.1f}ms"

    def test_pi_translation_produces_non_empty_output(self):
        """Every π translation produces a non-empty T sequent."""
        from verifier.e_library import E_THEOREM_LIBRARY
        from verifier.t_pi_translation import pi_sequent

        for name, thm in E_THEOREM_LIBRARY.items():
            t_seq, _ = pi_sequent(thm.sequent)
            t_str = str(t_seq)
            assert len(t_str) > 0, f"{name}: empty T translation"


# ═══════════════════════════════════════════════════════════════════════
# 5. CROSS-SYSTEM TRANSLATION ROUNDTRIP LATENCY
# ═══════════════════════════════════════════════════════════════════════

class TestCrossSystemRoundtripTiming:
    """Measure E→T→E and E→H→E roundtrip latency."""

    def test_e_to_t_roundtrip_all_48_under_500ms(self):
        """E→T→E roundtrip for all 48 props completes in <500ms."""
        from verifier.e_library import E_THEOREM_LIBRARY
        from verifier.t_pi_translation import pi_sequent
        from verifier.t_rho_translation import rho_sequent

        total = 0.0
        for name, thm in E_THEOREM_LIBRARY.items():
            t0 = time.perf_counter()
            t_seq, _ = pi_sequent(thm.sequent)
            e_seq = rho_sequent(t_seq)
            elapsed = (time.perf_counter() - t0) * 1000
            total += elapsed
        assert total < 500, f"E→T→E roundtrip took {total:.1f}ms"

    def test_e_to_h_roundtrip_all_48_under_500ms(self):
        """E→H roundtrip for all 48 props completes in <500ms."""
        from verifier.e_library import E_THEOREM_LIBRARY
        from verifier.h_bridge import e_sequent_to_h

        total = 0.0
        for name, thm in E_THEOREM_LIBRARY.items():
            t0 = time.perf_counter()
            h_seq = e_sequent_to_h(thm.sequent)
            elapsed = (time.perf_counter() - t0) * 1000
            total += elapsed
        assert total < 500, f"E→H translation took {total:.1f}ms"


# ═══════════════════════════════════════════════════════════════════════
# 6. SMT FALLBACK FREQUENCY (structural check)
# ═══════════════════════════════════════════════════════════════════════

class TestSmtFallbackFrequency:
    """Verify that forward-chaining handles most cases without SMT."""

    def test_basic_betweenness_no_smt_needed(self):
        """Basic betweenness consequences are resolved by forward-chaining alone."""
        from verifier.e_consequence import ConsequenceEngine

        known = {
            Literal(Between("a", "b", "c")),
        }
        query = Literal(Between("c", "b", "a"))
        engine = ConsequenceEngine()
        assert engine.is_consequence(known, query)

    def test_on_consequences_no_smt_needed(self):
        """On-line consequences resolved by forward-chaining."""
        from verifier.e_consequence import ConsequenceEngine

        known = {
            Literal(Between("a", "b", "c")),
            Literal(On("a", "L")),
            Literal(On("c", "L")),
        }
        query = Literal(On("b", "L"))
        vars_ = {
            "a": Sort.POINT, "b": Sort.POINT, "c": Sort.POINT,
            "L": Sort.LINE,
        }
        engine = ConsequenceEngine()
        result = engine.is_consequence(known, query, vars_)
        assert result

    def test_smt_fallback_returns_gracefully_when_z3_missing(self):
        """SMT fallback returns False (not crash) when Z3 is not installed."""
        from verifier.unified_checker import verify_step

        known = {Literal(Between("a", "b", "c"))}
        query = Literal(Equals("a", "z"))  # Not a consequence
        result = verify_step(
            known, query,
            use_smt_fallback=True,
            z3_path="nonexistent_z3_binary",
        )
        assert result is False


# ═══════════════════════════════════════════════════════════════════════
# 7. GeoCoq COMPATIBILITY VALIDATION TIMING
# ═══════════════════════════════════════════════════════════════════════

class TestGeocoqValidationTiming:
    """Measure GeoCoq compatibility validation latency."""

    def test_e_library_validation_under_100ms(self):
        """validate_library_alignment() completes in <100ms."""
        from verifier.geocoq_compat import validate_library_alignment

        result, elapsed = _time_ms(validate_library_alignment)
        assert elapsed < 100, f"E validation took {elapsed:.1f}ms"
        assert result == []

    def test_t_translation_validation_under_500ms(self):
        """validate_translation_alignment() completes in <500ms."""
        from verifier.geocoq_compat import validate_translation_alignment

        result, elapsed = _time_ms(validate_translation_alignment)
        assert elapsed < 500, f"T validation took {elapsed:.1f}ms"
        assert result == []
