<div align="center">

# 📐 Euclid Elements Simulator

**A formal proof verifier & interactive geometry workbench for Euclid's *Elements* Book I**

[![Python 3.12+](https://img.shields.io/badge/Python-3.12%2B-3776AB?logo=python&logoColor=white)](#requirements)
[![PyQt6](https://img.shields.io/badge/GUI-PyQt6-41CD52?logo=qt&logoColor=white)](#features)
[![Tests](https://img.shields.io/badge/Tests-~890_passing-brightgreen)](#running-tests)
[![License](https://img.shields.io/badge/License-MIT-blue)](#license)

Implements three axiom systems (**Euclid E**, **Tarski T**, **Hilbert H**) with automatic bridge translations, all 48 Book I propositions formalized and verified, and a desktop GUI for constructing and checking proofs interactively.

*Inspired by [GeoCoq](https://geocoq.github.io/GeoCoq/) · Based on Avigad, Dean & Mumma (2009), ["A Formal System for Euclid's Elements"](https://doi.org/10.1017/S1755020309990098)*

</div>

---

## ✨ Highlights

- **All 48 propositions** of Book I — from equilateral triangle construction (I.1) to the Pythagorean theorem (I.47) — formalized with hand-written, machine-verified proofs
- **Three axiom systems** (E / T / H) connected by automatic π and ρ translations — users write in Euclid's style, verification falls back through Tarski invisibly
- **Interactive desktop app** with a geometry canvas, step-by-step proof editor, real-time diagnostics, a 152-rule reference catalog, and E/T/H translation view
- **~890 automated tests** covering all three axiom systems, the completeness pipeline, theorem application, and the UI layer

---

## 🚀 Quick Start

```bash
# Clone the repository
git clone https://github.com/<your-username>/euclid-elements-simulator.git
cd euclid-elements-simulator

# Install dependencies (Python 3.12+)
pip install -r requirements.txt

# Launch the desktop GUI
python -m euclid_py

# Or verify a proof from the command line
python -m verifier.cli verifier/examples/valid_inc1.json

# Run the full test suite
python -m pytest verifier/tests/ euclid_py/tests/ -v
```

---

## 🏗️ Architecture

The project follows GeoCoq's layered design: proofs are authored in **System E** (Euclid's geometric language), with **System T** (Tarski) acting as an invisible computational bridge for completeness, and **System H** (Hilbert) available as an alternative notation.

```
┌───────────────────────────────────────────────────────────────┐
│                     euclid_py  (PyQt6 UI)                     │
│   main_window · proof_panel · canvas_widget · diagnostics     │
│   rule_reference · translation_view · summary_panel           │
├───────────────────────────────────────────────────────────────┤
│                    unified_checker.py                          │
│             Single entry point for all verification            │
├──────────────────┬───────────────────┬────────────────────────┤
│   System E       │   System T        │   System H             │
│   (Primary)      │   (Bridge)        │   (Display)            │
│                  │                   │                        │
│   e_ast          │   t_ast           │   h_ast                │
│   e_axioms       │   t_axioms        │   h_axioms             │
│   e_consequence  │   t_consequence   │   h_consequence        │
│   e_construction │   t_bridge (E↔T)  │   h_bridge (E↔H)      │
│   e_metric       │   t_checker       │   h_checker            │
│   e_transfer     │   t_completeness  │   h_library            │
│   e_superposition│   t_cut_elim      │                        │
│   e_checker      │   t_pi / t_rho    │                        │
│   e_library      │                   │                        │
│   e_proofs       │                   │                        │
└──────────────────┴───────────────────┴────────────────────────┘
```

### The Three Systems

| System | Sorts | Primitives | Role |
|--------|-------|-----------|------|
| **E** (Euclid) | Points, Lines, Circles | `on`, `between`, `same-side`, `center`, `inside`, `intersects`, `=` | Primary proof language — what users write in |
| **T** (Tarski) | Points only | `B` (betweenness), `Cong` (equidistance) | Invisible bridge for completeness verification |
| **H** (Hilbert) | Points, Lines | `IncidL`, `BetH`, `CongH`, `CongaH` | Alternative display notation |

### Verification Pipeline

```
User writes proof in System E
  → e_checker validates (consequence + construction + metric engines)
  → If inconclusive → automatic π translation → Tarski T → ρ back to E
  → Result: ✓ / ✗ with diagnostics in E notation
```

> **Invisible bridging** — The user never sees Tarski's system. Cross-system facts are automatically translated via `t_bridge` (E↔T) and `h_bridge` (E↔H).

---

## 🖥️ Desktop Application

The PyQt6 GUI provides a complete workbench for exploring Euclidean proofs:

| Feature | Description |
|---------|-------------|
| **Geometry Canvas** | Interactive diagram — draw points, segments, circles, angle marks; drag to reshape; snap-to-point with visual indicators |
| **Proof Editor** | Step-by-step proof journal with premises, goal, declarations; symbol palette for connectives & Greek letters; rule dropdown per line |
| **Diagnostics** | Real-time ✓/✗ status per step with detailed error messages and goal verification |
| **Rule Reference** | Searchable catalog of all 152 axiom rules (§3.3–§3.7) plus 48 proposition sequents |
| **E / T / H View** | Side-by-side translation of the current proposition across all three systems with human-readable "Given / Prove" formatting |
| **Glossary** | Every formal predicate across E, T, and H with plain English translations |
| **File I/O** | Save/load `.euclid` files — canvas only, proof only, or both; smart format detection on open |

---

## 📖 Proposition Library

All **48 propositions** of Euclid's *Elements* Book I are formalized with hand-written, machine-verified proofs:

| Range | Topic | Key Propositions |
|-------|-------|-----------------|
| I.1 – I.3 | Basic constructions | Equilateral triangle, segment transfer, cut-off |
| I.4 – I.8 | Triangle congruence | SAS (I.4), isosceles (I.5–I.6), SSS (I.8) |
| I.9 – I.12 | Bisection & perpendiculars | Angle bisector, midpoint, perpendicular drop |
| I.13 – I.15 | Angles on a line | Supplementary angles, vertical angles |
| I.16 – I.26 | Triangle inequalities | Exterior angle (I.16), ASA/AAS (I.26) |
| I.27 – I.32 | Parallel lines | Alternate angles (I.27–I.29), angle sum (I.32) |
| I.33 – I.45 | Parallelograms & area | Area equality, parallelogram constructions |
| I.46 – I.48 | Pythagorean theorem | Square (I.46), Pythagoras (I.47), converse (I.48) |

> 28 propositions are **neutral geometry** (no parallel postulate); 20 require **Euclid's fifth postulate** (first used at I.29).

---

## 📝 System E Proof Syntax

Proofs use the formal language from Avigad, Dean & Mumma (2009):

| Predicate | Meaning |
|-----------|---------|
| `on(a, L)` | Point *a* lies on line *L* |
| `between(a, b, c)` | *b* is strictly between *a* and *c* |
| `same-side(a, b, L)` | *a* and *b* are on the same side of line *L* |
| `center(a, α)` | *a* is the center of circle *α* |
| `inside(a, α)` | *a* is inside circle *α* |
| `ab = cd` | Segment *ab* equals segment *cd* |
| `∠abc = ∠def` | Angle *abc* equals angle *def* |
| `ab < cd` | Segment *ab* is less than *cd* |
| `△abc = △def` | Area of triangle *abc* equals area of *def* |

### Constructions

```
let L = line(a, b)            — line through a, b
let α = circle(a, b)          — circle centered at a through b
let p = intersection(...)     — intersection point
```

### Sequent Format

Theorems are expressed as sequents: **hypotheses ⇒ ∃vars. conclusions**

```
Prop I.1 :  ¬(a = b)  ⇒  ∃c. ab = ac ∧ ab = bc ∧ c ≠ a ∧ c ≠ b
Prop I.4 :  SAS hypotheses  ⇒  ac = df ∧ ∠bac = ∠edf ∧ ∠bca = ∠efd
Prop I.47:  right-angle triangle  ⇒  BC² = AB² + AC²  (via area decomposition)
```

---

## ⚙️ Axiom Systems

### System E — Euclid (Paper §3.3–3.7)

| Group | Count | Section | Description |
|-------|-------|---------|-------------|
| Construction | 6 | §3.3 | `line`, `circle`, intersection rules |
| Diagrammatic | ~30 | §3.4 | Betweenness, same-side, Pasch, incidence |
| Metric | ~12 | §3.5 | Segment/angle/area congruence & ordering |
| Transfer | ~8 | §3.6 | Cross-predicate transfer rules |
| Superposition | 2 | §3.7 | SAS, SSS |

### System T — Tarski (Paper §5.2)

11 axioms + 6 negativity clauses (30 GRS clauses total). Sorts: **POINT** only. Primitives: `B` (betweenness), `Cong` (equidistance).

### System H — Hilbert (*Grundlagen der Geometrie*)

40 clauses across Groups I–IV: Incidence (8), Order (4), Congruence (6), Parallels (1) + derived theorems.

---

## 📁 Project Structure

```
Euclid/
├── requirements.txt               # Dependencies: PyQt6, pytest
├── change-log.md                  # Detailed changelog
├── answer-keys-e.json             # All 48 answer keys (System E)
│
├── verifier/                      # ── Core verification engine ──
│   ├── unified_checker.py         # ★ Single entry point for all verification
│   ├── e_*.py                     # System E  (AST, axioms, consequence, …)
│   ├── t_*.py                     # System T  (AST, axioms, bridge, π/ρ, …)
│   ├── h_*.py                     # System H  (AST, axioms, bridge, …)
│   ├── diagnostics.py             # Shared error codes & result types
│   ├── examples/                  # Example proof JSON files
│   └── tests/                     # ~790 pytest tests
│
├── euclid_py/                     # ── PyQt6 desktop application ──
│   ├── __main__.py                # App entry point
│   ├── ui/
│   │   ├── main_window.py         # Main window & toolbar
│   │   ├── proof_panel.py         # Interactive proof editor
│   │   ├── canvas_widget.py       # Geometry diagram canvas
│   │   ├── rule_reference.py      # Rule reference panel (152 rules)
│   │   ├── translation_view.py    # E/T/H translation + glossary
│   │   ├── diagnostics_panel.py   # Error/warning display
│   │   └── summary_panel.py       # Proof summary
│   ├── engine/
│   │   ├── proposition_data.py    # UI metadata for all 48 propositions
│   │   ├── constraints.py         # Diagram constraints
│   │   └── file_format.py         # .euclid file I/O
│   └── tests/                     # ~100 pytest tests
│
└── proofs/                        # Saved proof files (.euclid / .json)
```
---

## 🧪 Running Tests

```bash
# Full suite (~890 tests)
python -m pytest verifier/tests/ euclid_py/tests/ -v

# Verifier only (~790 tests)
python -m pytest verifier/tests/ -v

# UI tests
python -m pytest euclid_py/tests/ -v

# Specific subsystems
python -m pytest verifier/tests/test_t_system.py -v         # Tarski axioms
python -m pytest verifier/tests/test_completeness.py -v      # Completeness pipeline
python -m pytest verifier/tests/test_unified_checker.py -v   # Unified checker
python -m pytest verifier/tests/test_e_system.py -v          # All 48 propositions
```

---

## 🔧 Requirements

- **Python 3.12+**
- **PyQt6** ≥ 6.6.0 — desktop GUI framework
- **pytest** ≥ 7.0.0 — test runner

Install with:
```bash
pip install -r requirements.txt
```

---

## 🧑‍💻 Usage Examples

### Python API

```python
from verifier.unified_checker import verify_proof, verify_named_proof, get_theorem

# Verify a named proposition
result = verify_named_proof("Prop.I.1")
print(result.valid)   # True
print(result.engine)  # 'E'

# Look up a theorem sequent
thm = get_theorem("Prop.I.47")
print(thm.sequent)
# ¬(a = b), ... ⇒ ∃d,e,f,g,h,k. (area decomposition)
```

### Command Line

```bash
# Verify a proof JSON file
python -m verifier.cli verifier/examples/valid_inc1.json

# Launch the GUI and load a file
python -m euclid_py proofs/Prop_I_1_H.json
```

---

## 📚 References

- Avigad, J., Dean, E., & Mumma, J. (2009). "A Formal System for Euclid's Elements." *Review of Symbolic Logic*, 2(4), 700–768.
- [GeoCoq](https://geocoq.github.io/GeoCoq/) — Coq formalization of geometry (Tarski, Hilbert, Euclid).
- Hilbert, D. (1899). *Grundlagen der Geometrie*.
- Tarski, A. (1959). "What is Elementary Geometry?"
- Negri, S. (2003). "Contraction-free sequent calculi for geometric theories."

---

## 📄 License

This project is provided for educational and research purposes. See the repository for license details.
