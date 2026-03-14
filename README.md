<div align="center">

<img src="Euclid Logo.png" alt="Euclid Logo" width="120">

# Euclid

**The first 48 propositions of Euclid's *Elements*, machine-verified — with an interactive desktop workbench to explore, construct, and check proofs yourself.**

[![Python 3.12+](https://img.shields.io/badge/Python-3.12%2B-3776AB?logo=python&logoColor=white)](#-requirements)
[![PyQt6](https://img.shields.io/badge/GUI-PyQt6-41CD52?logo=qt&logoColor=white)](#-the-desktop-app)
[![997 Tests](https://img.shields.io/badge/Tests-997_passing-brightgreen)](#-testing)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue)](#-license)

[Getting Started](#-getting-started) · [The Desktop App](#-the-desktop-app) · [How It Works](#%EF%B8%8F-how-it-works) · [All 48 Propositions](#-all-48-propositions) · [For Developers](#-for-developers)

*Based on Avigad, Dean & Mumma (2009), ["A Formal System for Euclid's Elements"](https://doi.org/10.1017/S1755020309990098)*

</div>

<br>

## What is this?

This project does something nobody else has done in quite this way: it takes all 48 propositions from Book I of Euclid's *Elements* — from constructing an equilateral triangle (I.1) all the way to the Pythagorean theorem (I.47) and its converse (I.48) — and verifies every single one with a machine-checked formal proof system called **System E**.

It's also a **desktop app** where you can draw diagrams, write proofs step-by-step, and watch the verifier accept or reject each line in real time.

> **28** propositions are pure neutral geometry (no parallel postulate).
> **20** require Euclid's fifth postulate, first invoked at Proposition I.29.

---

## 🚀 Getting Started

### Option A — Download the `.exe` (Windows, no install needed)

Grab **`Euclid.exe`** from the [latest release](https://github.com/congman5/Euclid/releases/latest). Double-click. That's it.

### Option B — Run from source

```bash
git clone https://github.com/congman5/Euclid.git
cd Euclid

pip install -r requirements.txt      # or: pip install -e .
python -m euclid_py                  # launch the GUI
```

### Option C — Build your own `.exe`

```bash
pip install -e .[dev]          # installs PyInstaller
python build_exe.py            # → dist/Euclid/Euclid.exe
python build_exe.py --onefile  # → dist/Euclid.exe (single portable file)
```

---

## 🖥️ The Desktop App

The PyQt6 GUI is a full workbench for Euclidean proof construction:

| | |
|---|---|
| **📐 Geometry Canvas** | Draw points, lines, segments, circles, and angle marks. Drag to reshape. Snap-to-point with visual guides. |
| **📝 Proof Editor** | Fitch-style step-by-step proof journal. Premises, goal, declarations, subproofs with assume/reductio. Symbol palette for `∠`, `△`, Greek letters, connectives. |
| **✅ Live Verification** | Every line shows ✓ or ✗ in real time. Click **Eval** for single-step checking or **All** for the full proof. Detailed diagnostics explain *why* a step fails. |
| **🧠 Smart Autofill** | Leave a step blank with the right justification and references — the engine infers Metric equalities, SAS/SSS congruence conclusions, and named axiom results automatically. |
| **📖 Rule Reference** | Searchable catalog of all **152 rules**: construction (§3.3), diagrammatic (§3.4), metric (§3.5), transfer (§3.6), superposition (§3.7), plus all 48 proposition sequents. |
| **💾 File I/O** | Save and load `.euclid` files — canvas only, proof only, or both. Smart format detection on open. |

---

## ⚙️ How It Works

Everything is built on **System E**, the formal axiom system from [Avigad, Dean & Mumma (2009)](https://doi.org/10.1017/S1755020309990098). It's the only axiom system — no Hilbert, no Tarski, just Euclid's own geometric language made rigorous.

### The Language

| Predicate | Meaning |
|-----------|---------|
| `on(a, L)` | Point *a* lies on line *L* |
| `between(a, b, c)` | *b* is strictly between *a* and *c* |
| `same-side(a, b, L)` | *a*, *b* are on the same side of *L* |
| `center(a, α)` | *a* is the center of circle *α* |
| `inside(a, α)` | *a* is strictly inside circle *α* |
| `intersects(L, α)` | Line *L* meets circle *α* |
| `ab = cd` | Segment *ab* equals segment *cd* |
| `∠abc = ∠def` | Angle equality |
| `△abc = △def` | Area equality |
| `ab < cd` | Strict segment ordering |

### The Axiom Groups

| Group | Rules | Paper § | What they do |
|-------|------:|---------|-------------|
| **Construction** | 6 | §3.3 | Create lines, circles, intersection points |
| **Diagrammatic** | 62 | §3.4 | Betweenness, same-side, Pasch, incidence, circle interior |
| **Metric** | 17 | §3.5 | Segment/angle/area congruence, ordering, common notions |
| **Transfer** | 23 | §3.6 | Bridge diagram facts ↔ metric facts (segment addition, angle addition, area decomposition) |
| **Superposition** | 2 | §3.7 | SAS and SSS triangle congruence |
| **Structural** | 8 | — | Given, Reit, ⊥-intro, ⊥-elim, Cases, Assume |

> Axiom names match the paper exactly — e.g. "Betweenness 3" is B3, "Segment transfer 3b" is DS3b, "Angle transfer 4" is DA4.

### Constructions

```
let L  = line(a, b)                    — line through two distinct points
let α  = circle(a, b)                  — circle centered at a, passing through b
let p  = point-on-line(L)              — fresh point on L
let c  = intersection-cc(α, β)        — intersection of two circles
let c  = intersection-lc(L, α)        — intersection of a line and circle
```

### How a Proof Looks

Theorems are sequents:  **premises ⇒ ∃witnesses. conclusions**

```
Prop I.1:   ¬(a = b)
            ⇒ ∃c.  ab = ac,  ab = bc,  c ≠ a,  c ≠ b

Prop I.4:   ab = de, ac = df, ∠bac = ∠edf        (SAS hypotheses)
            ⇒ bc = ef, ∠abc = ∠def, ∠acb = ∠dfe

Prop I.47:  ∠bac = right-angle                     (Pythagoras)
            ⇒ ∃squares.  BC² = AB² + AC²           (via area decomposition)
```

### Verification Pipeline

```
                 ┌──────────────────────────────────────────────┐
User writes      │               unified_checker.py              │
proof steps  ──▶ │  ┌─────────┐ ┌──────────┐ ┌──────────────┐  │ ──▶  ✓ / ✗
                 │  │ e_conse- │ │ e_metric │ │ e_superpos-  │  │    + diagnostics
                 │  │ quence   │ │          │ │ ition        │  │
                 │  └─────────┘ └──────────┘ └──────────────┘  │
                 │  ┌──────────────┐  ┌───────────────────┐    │
                 │  │ e_construction│  │ e_transfer        │    │
                 │  └──────────────┘  └───────────────────┘    │
                 └──────────────────────────────────────────────┘
```

---

## 📖 All 48 Propositions

Every proposition in Book I — hand-written proofs, machine-verified:

| # | Proposition | Type |
|---|------------|------|
| **I.1** | Construct an equilateral triangle | Construction |
| **I.2** | Transfer a segment to a given point | Construction |
| **I.3** | Cut off a segment equal to a shorter one | Construction |
| **I.4** | **SAS** — Side-Angle-Side congruence | Congruence |
| **I.5** | Base angles of an isosceles triangle are equal | Triangle |
| **I.6** | Equal base angles imply isosceles | Triangle |
| **I.7** | Uniqueness of triangle construction | Triangle |
| **I.8** | **SSS** — Side-Side-Side congruence | Congruence |
| **I.9** | Bisect an angle | Construction |
| **I.10** | Bisect a segment (find midpoint) | Construction |
| **I.11** | Erect a perpendicular from a point on a line | Construction |
| **I.12** | Drop a perpendicular from a point to a line | Construction |
| **I.13** | Supplementary angles sum to two right angles | Angles |
| **I.14** | Angles summing to two right angles form a straight line | Angles |
| **I.15** | Vertical angles are equal | Angles |
| **I.16** | Exterior angle > either remote interior angle | Inequality |
| **I.17** | Two angles of a triangle sum to less than two right angles | Inequality |
| **I.18** | Greater side opposite greater angle | Inequality |
| **I.19** | Greater angle opposite greater side | Inequality |
| **I.20** | Triangle inequality: sum of two sides > third | Inequality |
| **I.21** | Triangle within triangle: shorter sides, larger angle | Inequality |
| **I.22** | Construct triangle from three segments | Construction |
| **I.23** | Copy an angle | Construction |
| **I.24** | SAS inequality (open hinge) | Inequality |
| **I.25** | SAS inequality converse (converse hinge) | Inequality |
| **I.26** | **ASA / AAS** congruence | Congruence |
| **I.27** | Alternate interior angles ⇒ parallel | Parallels |
| **I.28** | Exterior angle = remote interior ⇒ parallel | Parallels |
| **I.29** | Parallel ⇒ alternate angles equal *(uses Postulate 5)* | Parallels |
| **I.30** | Lines parallel to the same line are parallel | Parallels |
| **I.31** | Construct a parallel through a point | Construction |
| **I.32** | Exterior angle = sum of remote interiors; angle sum = 2R | Angle Sum |
| **I.33** | Joining equal parallel segments gives a parallelogram | Parallelograms |
| **I.34** | Opposite sides/angles of a parallelogram are equal | Parallelograms |
| **I.35** | Parallelograms on same base, between parallels → equal area | Area |
| **I.36** | Parallelograms on equal bases, between parallels → equal area | Area |
| **I.37** | Triangles on same base, between parallels → equal area | Area |
| **I.38** | Triangles on equal bases, between parallels → equal area | Area |
| **I.39** | Equal triangles on same base → between same parallels | Area |
| **I.40** | Equal triangles on equal bases → between same parallels | Area |
| **I.41** | Parallelogram = 2× triangle (same base, same parallels) | Area |
| **I.42** | Construct parallelogram equal to triangle in given angle | Construction |
| **I.43** | Complements of a parallelogram about the diagonal are equal | Area |
| **I.44** | Apply a parallelogram to a segment in a given angle | Construction |
| **I.45** | Construct parallelogram equal to a rectilineal figure | Construction |
| **I.46** | Construct a square on a given segment | Construction |
| **I.47** | **Pythagorean theorem** 🎉 | Area |
| **I.48** | Converse of the Pythagorean theorem | Area |

---

## 💻 Python API

```python
from verifier.unified_checker import verify_named_proof, get_theorem

# Verify any of the 48 propositions
result = verify_named_proof("Prop.I.1")
print(result.valid)    # True
print(result.engine)   # 'E'

# Look up the formal sequent
thm = get_theorem("Prop.I.47")
print(thm.sequent)
# ¬(a = b), ∠bac = right-angle, ...
# ⇒ ∃d,e,f,g,h,k. (area decomposition proving a² + b² = c²)
```

```bash
# Verify a proof JSON from the command line
python -m verifier.cli verifier/examples/valid_inc1.json

# Launch the GUI and open a file
python -m euclid_py path/to/proof.euclid
```

---

## 🧪 Testing

**997 tests** across the verifier engine and UI layer:

```bash
python -m pytest                                            # everything
python -m pytest verifier/tests/ -v                         # 844 verifier tests
python -m pytest euclid_py/tests/ -v                        # 153 UI tests
python -m pytest verifier/tests/test_e_system.py -v         # all 48 propositions
python -m pytest euclid_py/tests/test_autofill.py -v        # autofill engine
```

---

## 📁 Project Structure

```
Euclid/
│
├── pyproject.toml                 # pip install -e . (entry point: euclid)
├── requirements.txt               # pip install -r requirements.txt
├── build_exe.py                   # → dist/Euclid/Euclid.exe
├── euclid.spec                    # PyInstaller config
├── launch_euclid.pyw              # Windowless launcher (no console)
│
├── euclid_py/                     # ── Desktop application (PyQt6) ──
│   ├── __main__.py                # python -m euclid_py
│   ├── resources.py               # Bundled resource path resolver
│   ├── ui/
│   │   ├── main_window.py         # Main window, toolbar, sidebar
│   │   ├── proof_panel.py         # Proof editor + autofill engine
│   │   ├── canvas_widget.py       # Interactive geometry canvas
│   │   ├── rule_reference.py      # Searchable 152-rule catalog
│   │   ├── diagnostics_panel.py   # Error / warning display
│   │   └── summary_panel.py       # Proof summary view
│   ├── engine/
│   │   ├── proposition_data.py    # UI metadata for 48 propositions
│   │   ├── constraints.py         # Diagram constraint solver
│   │   └── file_format.py         # .euclid save / load
│   └── tests/                     # 153 pytest tests
│
├── verifier/                      # ── Formal verification engine ──
│   ├── unified_checker.py         # ★ Single entry point
│   ├── e_ast.py                   # Sorts, literals, sequents
│   ├── e_axioms.py                # All axiom clauses (paper §3.3–3.7)
│   ├── e_consequential.sh         # Forward-chaining engine (§3.8)
│   ├── e_construction.py          # Line, circle, intersection rules
│   ├── e_metric.py                # Segment / angle / area congruence
│   ├── e_transfer.py              # Diagram ↔ metric transfer
│   ├── e_superposition.py         # SAS / SSS
│   ├── e_checker.py               # Step-by-step proof checker
│   ├── e_library.py               # 48 theorem sequents
│   ├── e_proofs.py                # Encoded proof steps
│   ├── e_parser.py                # System E formula parser
│   └── tests/                     # 844 pytest tests
│
└── scripts/
    └── real_proofs.py             # All Book I proofs (executable)
```

---

## 🔧 Requirements

| Dependency | Version | Purpose |
|-----------|---------|---------|
| **Python** | ≥ 3.12 | Runtime |
| **PyQt6** | ≥ 6.6.0 | Desktop GUI |
| **pytest** | ≥ 7.0.0 | Testing (dev) |
| **PyInstaller** | ≥ 6.0 | `.exe` packaging (dev) |

```bash
pip install -r requirements.txt        # core + test
pip install -e .[dev]                   # everything including PyInstaller
```

---

## 📚 References

- Avigad, J., Dean, E., & Mumma, J. (2009). [A Formal System for Euclid's Elements.](https://doi.org/10.1017/S1755020309990098) *Review of Symbolic Logic*, 2(4), 700–768.
- Avigad, J., Dean, E., & Mumma, J. (2009). [A Formal System for Euclid's Elements](https://www.andrew.cmu.edu/user/avigad/Papers/formal_system_for_euclid.pdf) (preprint PDF).
- [GeoCoq](https://geocoq.github.io/GeoCoq/) — Coq formalization of geometry (Tarski axiom system).

---

## 📄 License

MIT — see [LICENSE](LICENSE) for details.

<div align="center">
<br>
<sub>Built with 📐 and probably too much caffeine.</sub>
</div>
