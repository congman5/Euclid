# Euclid Verifier — Formal Proof Engine

The core verification engine for the Euclid Elements Simulator. Implements **System E** (Avigad, Dean, Mumma 2009) as the sole formal axiom system.

**Sole engine**: System E (Avigad, Dean, Mumma 2009)

## Quick Start

```bash
# Run all verifier tests
python -m pytest verifier/tests/ -v

# Verify a proof via CLI
python -m verifier.cli verifier/examples/valid_inc1.json

# Use the unified checker from Python
from verifier.unified_checker import verify_proof, verify_e_proof_json
```

## Architecture

All verification routes through `unified_checker.py` — the single entry point:

```
verifier/
├── unified_checker.py        ★ Single entry point for all verification
│
├── System E (Sole System — Paper §3)
│   ├── e_ast.py              Sorts: POINT, LINE, CIRCLE
│   ├── e_axioms.py           Construction (§3.3), Diagrammatic (§3.4),
│   │                         Metric (§3.5), Transfer (§3.6)
│   ├── e_consequence.py      Forward-chaining consequence engine (§3.8)
│   ├── e_construction.py     Line, circle, intersection rules
│   ├── e_metric.py           Segment/angle/area congruence
│   ├── e_transfer.py         Cross-predicate transfer
│   ├── e_superposition.py    SAS/SSS superposition (§3.7)
│   ├── e_checker.py          Step-by-step proof checker
│   ├── e_bridge.py           Legacy format ↔ System E
│   ├── e_library.py          All 48 theorem sequents (I.1–I.48)
│   ├── e_proofs.py           Encoded proof steps
│   └── e_parser.py           System E formula parser
│
├── diagnostics.py            Shared error codes and result types
├── _legacy/                  Deprecated Fitch checker (reference only)
├── examples/                 Example proof JSON files
└── tests/                    Pytest test suite
```

## Verification Pipeline

```
unified_checker.verify_proof(eproof)
  → EChecker validates via e_consequence + e_construction + e_metric
  → Returns UnifiedResult (valid, engine, diagnostics)
```

### API

```python
from verifier.unified_checker import (
    verify_proof,           # Verify a System E proof
    verify_e_proof_json,    # Verify proof from UI JSON format
    verify_named_proof,     # Verify a named proof (e.g. "Prop.I.1")
    verify_step,            # Single-step consequence check
    get_available_rules,    # Rule catalogue for UI
    get_theorem,            # Retrieve a theorem by name
)
```

## System E Proof Syntax

Theorems are sequents: `hypotheses ⇒ ∃vars. conclusions`

| Predicate | Meaning |
|-----------|---------|
| `on(a, L)` | Point on line |
| `between(a, b, c)` | Strict betweenness |
| `same-side(a, b, L)` | Same side of line |
| `on(a, α)` / `inside(a, α)` / `center(a, α)` | Circle predicates |
| `ab = cd` | Segment equality |
| `∠abc = ∠def` | Angle equality |
| `ab < cd` / `∠abc < ∠def` | Magnitude ordering |

### Construction Steps

```
let L be line(a, b)       — construct the line through a, b
let α be circle(a, b)     — construct the circle with center a through b
let p be intersection(...)— construct an intersection point
```

## Legacy Format (Deprecated)

The old Fitch-style proof format (`Point(A)`, `Segment(A,B)`, `Equal(AB,CD)`) is still supported through `verify_old_proof_json()` but is deprecated. New proofs should use System E syntax. The old checker files are preserved in `_legacy/` for reference.

## Theorem Library

All 48 propositions of Book I are in `e_library.py`:

```python
from verifier.e_library import E_THEOREM_LIBRARY
thm = E_THEOREM_LIBRARY["Prop.I.1"]
print(thm.sequent)
# ¬(a = b) ⇒ ∃c:POINT. ab = ac, ab = bc, ¬(c = a), ¬(c = b)
```

## Running Tests

```bash
python -m pytest verifier/tests/ -v                        # All verifier tests
python -m pytest verifier/tests/test_unified_checker.py -v # Unified checker
python -m pytest verifier/tests/test_all_48_proofs.py -v   # All 48 Book I proofs
python -m pytest verifier/tests/test_soundness.py -v       # Soundness test suite
```

## References

- Avigad, Dean, Mumma (2009). "A Formal System for Euclid's Elements."
- [GeoCoq](https://geocoq.github.io/GeoCoq/) — Coq formalization of geometry.
- Negri (2003). Contraction-free sequent calculi for geometric theories.
