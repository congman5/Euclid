# Euclid Elements Simulator

A formal proof verifier for Euclid's *Elements* Book I, implementing three axiom systems with automatic bridge translations — inspired by the [GeoCoq](https://geocoq.github.io/GeoCoq/) project.

**Reference paper**: Avigad, Dean, Mumma (2009), *"A Formal System for Euclid's Elements"*

## Quick Start

```bash
# Install dependencies
pip install -r requirements.txt

# Run all tests (639 tests)
python -m pytest verifier/tests/ euclid_py/tests/ -v

# Launch the PyQt6 UI
python -m euclid_py

# Verify a proof from the command line
python -m verifier.cli verifier/examples/valid_inc1.json
```

## Architecture

The project implements three axiom systems bridged through Tarski's system, following GeoCoq's approach where Tarski is the computational foundation and Euclid/Hilbert are theorem-level overlays:

```
┌─────────────────────────────────────────────────────────────┐
│                    euclid_py (PyQt6 UI)                     │
│  main_window → proof_panel → proof_view → diagnostics_panel │
│  canvas_widget → rule_reference → summary_panel             │
├─────────────────────────────────────────────────────────────┤
│                  unified_checker.py                          │
│           Single entry point for all verification            │
├─────────────────┬──────────────────┬────────────────────────┤
│    System E     │    System T      │     System H           │
│  (Primary)      │  (Bridge)        │  (Display)             │
│  e_ast          │  t_ast           │  h_ast                 │
│  e_axioms       │  t_axioms        │  h_axioms              │
│  e_consequence  │  t_consequence   │  h_consequence         │
│  e_construction │  t_bridge (E↔T)  │  h_bridge (E↔H)       │
│  e_metric       │  t_checker       │  h_checker             │
│  e_transfer     │  t_completeness  │  h_library             │
│  e_superposition│  t_cut_elim      │                        │
│  e_checker      │  t_pi / t_rho    │                        │
│  e_library      │                  │                        │
│  e_proofs       │                  │                        │
├─────────────────┴──────────────────┴────────────────────────┤
│              _legacy/ (deprecated Fitch checker)             │
└─────────────────────────────────────────────────────────────┘
```

### The Three Systems

| System | Sorts | Primitives | Role | Paper Reference |
|--------|-------|-----------|------|-----------------|
| **System E** (Euclid) | Points, Lines, Circles | `on`, `between`, `same-side`, `center`, `inside`, `intersects`, `=` (segment/angle/area) | Primary proof language — what users write in | Sections 3.3–3.8 |
| **System T** (Tarski) | Points only | `B` (betweenness), `Cong` (equidistance) | Internal bridge for completeness checking — invisible to users | Section 5.2 |
| **System H** (Hilbert) | Points, Lines | `IncidL`, `BetH`, `CongH`, `CongaH` | Alternative display format | Hilbert's *Grundlagen* |

### Verification Pipeline

```
User writes proof in System E syntax
  → e_checker validates (e_consequence + e_construction + e_metric)
  → If inconclusive → automatic π → T → t_consequence → ρ → E
  → Result shown to user as ✓/✗ with E-language diagnostics
```

The T and H translations happen **invisibly** — the user never sees Tarski's system. This follows GeoCoq's design where proofs are written in Euclid's style but verified through Tarski's axiom system automatically.

## Proposition Library

All 48 propositions of Euclid's *Elements* Book I are formalized in both System E and System H:

| Range | Topic | Key Propositions |
|-------|-------|-----------------|
| I.1–I.3 | Basic constructions | Equilateral triangle, segment transfer, cut-off |
| I.4–I.8 | Triangle congruence | SAS (I.4), isosceles (I.5–I.6), SSS (I.8) |
| I.9–I.12 | Bisection & perpendiculars | Angle bisector (I.9), midpoint (I.10) |
| I.13–I.15 | Angles on a line | Supplementary angles, vertical angles |
| I.16–I.26 | Triangle inequalities | Exterior angle (I.16), ASA/AAS (I.26) |
| I.27–I.32 | Parallel lines | Alternate angles (I.27–I.29), angle sum (I.32) |
| I.33–I.45 | Parallelograms & area | Area equality, parallelogram constructions |
| I.46–I.48 | Pythagorean theorem | Square (I.46), Pythagoras (I.47), converse (I.48) |

## System E Proof Syntax

System E uses the formal language from Avigad, Dean, Mumma (2009):

| Predicate | Meaning | Example |
|-----------|---------|---------|
| `on(a, L)` | Point `a` lies on line `L` | `on(a, L)` |
| `between(a, b, c)` | `b` is strictly between `a` and `c` | `between(a, b, c)` |
| `same-side(a, b, L)` | `a` and `b` are on the same side of `L` | `same-side(p, q, L)` |
| `on(a, α)` | Point `a` lies on circle `α` | `on(a, α)` |
| `inside(a, α)` | Point `a` is inside circle `α` | `inside(a, α)` |
| `center(a, α)` | Point `a` is center of circle `α` | `center(a, α)` |
| `ab = cd` | Segment `ab` equals segment `cd` | `ab = cd` |
| `∠abc = ∠def` | Angle `abc` equals angle `def` | `∠abc = ∠def` |
| `ab < cd` | Segment `ab` is less than `cd` | `ab < cd` |

### Sequent Format

Theorems are expressed as sequents: `hypotheses ⇒ ∃vars. conclusions`

```
Prop I.1:  ¬(a = b) ⇒ ∃c:POINT. ab = ac, ab = bc, ¬(c = a), ¬(c = b)
Prop I.4:  ¬(a = b), ..., ∠abc = ∠def ⇒ ac = df, ∠bac = ∠edf, ∠bca = ∠efd
Prop I.47: ¬(a = b), ..., ∠bac = right-angle ⇒ (△bcb + △bcb) = ((△aba + △aba) + (△aca + △aca))
```

## Project Structure

```
Euclid/
├── README.md                     # This file
├── requirements.txt              # Python dependencies (PyQt6, pytest)
├── IMPLEMENTATION_PLAN.md        # Comprehensive development plan (Phases 4–10)
├── AUDIT.md                      # Architecture audit against GeoCoq
├── change-log.md                 # Changelog
├── answer-keys-e.json            # All 48 answer keys in System E format
├── formal_system_extracted.txt   # Reference paper text
│
├── verifier/                     # Core verification engine
│   ├── unified_checker.py        # ★ Single entry point for all verification
│   │
│   ├── e_ast.py                  # System E AST (sorts, literals, sequents)
│   ├── e_axioms.py               # System E axioms (§3.4–3.6)
│   ├── e_consequence.py          # Forward-chaining consequence engine (§3.8)
│   ├── e_construction.py         # Construction rules (§3.3)
│   ├── e_metric.py               # Metric axioms (§3.5)
│   ├── e_transfer.py             # Transfer axioms (§3.6)
│   ├── e_superposition.py        # Superposition rule (§3.7)
│   ├── e_checker.py              # System E proof checker
│   ├── e_bridge.py               # Old format ↔ System E translation
│   ├── e_library.py              # All 48 theorem sequents
│   ├── e_proofs.py               # Encoded proofs for I.1–I.48
│   ├── e_parser.py               # System E formula parser
│   │
│   ├── t_ast.py                  # System T AST (points only, B + ≡)
│   ├── t_axioms.py               # 11 Tarski axioms as GRS clauses
│   ├── t_consequence.py          # T forward-chaining engine
│   ├── t_checker.py              # T proof checker
│   ├── t_bridge.py               # E ↔ T translations (π, ρ)
│   ├── t_completeness.py         # Completeness pipeline (Theorem 5.1)
│   ├── t_cut_elimination.py      # Cut elimination for GRS
│   ├── t_pi_translation.py       # Full π: E → T
│   ├── t_rho_translation.py      # Full ρ: T → E
│   │
│   ├── h_ast.py                  # System H AST (Hilbert's axioms)
│   ├── h_axioms.py               # 39 Hilbert axiom clauses
│   ├── h_consequence.py          # H forward-chaining engine
│   ├── h_checker.py              # H proof checker
│   ├── h_bridge.py               # E ↔ H translations
│   ├── h_library.py              # All 48 theorems in H notation
│   │
│   ├── diagnostics.py            # Shared diagnostic codes and results
│   ├── _legacy/                  # Deprecated Fitch-style checker (reference only)
│   ├── examples/                 # Example proof JSON files
│   └── tests/                    # ~590 pytest tests
│
├── euclid_py/                    # PyQt6 desktop application
│   ├── __main__.py               # App entry point
│   ├── ui/
│   │   ├── main_window.py        # Main application window
│   │   ├── proof_panel.py        # Interactive proof editor
│   │   ├── proof_view.py         # Proof display widget
│   │   ├── canvas_widget.py      # Geometry diagram canvas
│   │   ├── rule_reference.py     # Rule reference panel
│   │   ├── diagnostics_panel.py  # Error/warning display
│   │   └── summary_panel.py      # Proof summary
│   ├── engine/
│   │   ├── proposition_data.py   # UI metadata linked to e_library.py
│   │   ├── constraints.py        # Diagram constraints
│   │   └── file_format.py        # Proof file I/O
│   └── tests/                    # ~49 pytest tests
│
└── legacy JS/                    # ⚠️ Deprecated React/Vite web app
```

## Axiom Systems

### System E Axioms (Paper §3.3–3.7)

| Group | Count | Paper Section | Description |
|-------|-------|---------------|-------------|
| Construction | 6 | §3.3 | `line(a,b)`, `circle(a,b)`, intersection rules |
| Diagrammatic | ~30 | §3.4 | Betweenness, same-side, Pasch, circle, incidence |
| Metric | ~12 | §3.5 | Segment/angle/area congruence and ordering |
| Transfer | ~8 | §3.6 | Betweenness → segment, angle → ordering |
| Superposition | 2 | §3.7 | SAS, SSS |

### System T Axioms (Paper §5.2)

| Axiom | Description |
|-------|-------------|
| E1–E3 | Equidistance: symmetry, transitivity, identity |
| B | Betweenness |
| SC | Segment construction (existential) |
| 5S | Five-segment |
| P | Pasch (existential) |
| 2L/2U | Dimension axioms (lower/upper 2D) |
| PP | Parallel postulate (existential) |
| Int | Intersection (existential) |
| + 6 negativity axioms |

### System H Axioms (Hilbert's *Grundlagen*)

Groups I–IV: Incidence (8), Order (4), Congruence (6), Parallels (1) + derived — 39 clauses total.

## Running Tests

```bash
# All tests
python -m pytest verifier/tests/ euclid_py/tests/ -v

# Just the verifier
python -m pytest verifier/tests/ -v

# Just the UI tests
python -m pytest euclid_py/tests/ -v

# Specific system
python -m pytest verifier/tests/test_t_system.py -v        # Tarski
python -m pytest verifier/tests/test_completeness.py -v     # Completeness
python -m pytest verifier/tests/test_unified_checker.py -v  # Unified checker
```

## References

- Avigad, Dean, Mumma (2009). "A Formal System for Euclid's Elements." *Review of Symbolic Logic* 2(4): 700–768.
- [GeoCoq](https://geocoq.github.io/GeoCoq/) — Coq formalization of geometry foundations (Tarski, Hilbert, Euclid).
- Hilbert (1899). *Grundlagen der Geometrie*.
- Tarski (1959). "What is Elementary Geometry?"
