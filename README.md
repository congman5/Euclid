<div align="center">

<img src="Euclid Logo.png" alt="Euclid Logo" width="120">

# Euclid

**A formal proof verifier and interactive workbench for Book I of Euclid's *Elements*.**

[![Python 3.12+](https://img.shields.io/badge/Python-3.12%2B-3776AB?logo=python&logoColor=white)](#-requirements)
[![PyQt6](https://img.shields.io/badge/GUI-PyQt6-41CD52?logo=qt&logoColor=white)](#%EF%B8%8F-the-desktop-app)
[![667 Tests](https://img.shields.io/badge/Tests-667_passing-brightgreen)](#-testing)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue)](#-license)

[Getting Started](#-getting-started) · [The Desktop App](#%EF%B8%8F-the-desktop-app) · [How It Works](#%EF%B8%8F-how-it-works) · [Propositions](#-all-48-propositions) · [Project Structure](#-project-structure) · [Architecture Docs](docs/verifier-architecture.md)

*Built on **System E** — Avigad, Dean & Mumma (2009), ["A Formal System for Euclid's Elements"](https://doi.org/10.1017/S1755020309990098)*

</div>

---

## What is this?

Euclid is two things:

1. **A machine-checked proof verifier** for the formal system described in Avigad, Dean & Mumma (2009). It encodes all 48 propositions from Book I of Euclid's *Elements* — from constructing an equilateral triangle (I.1) to the Pythagorean theorem (I.47) and its converse (I.48). **15 propositions (I.1–I.15)** ship with complete, verified `.euclid` proof files.

2. **A desktop application** where you can draw diagrams on a geometry canvas, write Fitch-style proofs step by step, and see the verifier accept or reject each line in real time.

> **28** propositions are pure neutral geometry (no parallel postulate).
> **20** require Euclid's fifth postulate, first invoked at Proposition I.29.
>
> **v1.0** will be released when all 48 propositions of Book I are correctly implemented and verified.

---

## 🚀 Getting Started

### Download the `.exe` (Windows)

Grab **`Euclid.exe`** from the [latest release](https://github.com/congman5/Euclid/releases/latest). Double-click to run — no install needed.

### Run from source

```bash
git clone https://github.com/congman5/Euclid.git
cd Euclid
pip install -r requirements.txt
python -m euclid_py
```

### Build your own `.exe`

```bash
pip install -e .[dev]
python build_exe.py            # → dist/Euclid/Euclid.exe
python build_exe.py --onefile  # → dist/Euclid.exe (single file)
```

---

## 🖥️ The Desktop App

| Feature | Description |
|---|---|
| **📐 Geometry Canvas** | Draw points, segments, circles, and angle marks. Drag to reshape. Snap-to-point with visual guides. Select-then-construct workflow for propositions (equilateral triangle, angle bisector, perpendicular, etc.). |
| **📝 Proof Journal** | Fitch-style proof editor with premises, goal, declarations, and subproofs (assume / reductio). Symbol palette for `∠`, `△`, `¬`, `∧`, `∨`, Greek letters. |
| **✅ Live Verification** | Every line shows ✓ or ✗ in real time. Click **Eval** for a single step or **All** for the full proof. Diagnostics explain exactly why a step fails. |
| **🧠 Autofill** | Leave a statement blank with the right justification and references — the engine infers metric equalities, SAS/SSS conclusions, and named axiom results automatically. |
| **📖 Rule Reference** | Searchable catalog of all rules: construction, diagrammatic, metric, transfer, superposition, plus all 48 proposition sequents. |
| **🔨 Lemma System** | Load previously verified proofs as reusable lemmas. Background verification confirms soundness before the lemma becomes available. |
| **💾 File I/O** | Save and load `.euclid` files — canvas, proof, or both. |

---

## ⚙️ How It Works

Everything is built on **System E**, the formal axiom system from [Avigad, Dean & Mumma (2009)](https://doi.org/10.1017/S1755020309990098).

### The Language

| Predicate | Meaning |
|-----------|---------|
| `on(a, L)` | Point *a* lies on line *L* |
| `between(a, b, c)` | *b* is strictly between *a* and *c* |
| `same-side(a, b, L)` | *a*, *b* on the same side of line *L* |
| `center(a, α)` | *a* is the center of circle *α* |
| `inside(a, α)` | *a* is strictly inside circle *α* |
| `intersects(L, α)` | Line *L* meets circle *α* |
| `ab = cd` | Segment equality |
| `∠abc = ∠def` | Angle equality |
| `△abc = △def` | Area equality |
| `ab < cd` | Strict segment ordering |

### Axiom Groups

| Group | Clauses | Paper § | Purpose |
|-------|--------:|---------|---------|
| **Construction** | 21 | §3.3 | Create lines, circles, intersection points |
| **Diagrammatic** | 52 | §3.4 | Betweenness, same-side, Pasch, incidence, circle interior |
| **Transfer** | 25 | §3.6 | Bridge diagram ↔ metric facts (segment addition, angle addition, area decomposition) |
| **Superposition** | 2 | §3.7 | SAS and SSS triangle congruence |

> Axiom names follow the paper — e.g. "Betweenness 3" → B3, "Segment transfer 3b" → DS3b, "Angle transfer 4" → DA4.

### Constructions

```
let L  = line(a, b)                              — line through two distinct points
let α  = circle(a, b)                            — circle centered at a through b
let p  = point-on-line(L)                        — fresh point on L
let c  = intersection-cc(α, β)                   — intersection of two circles
let c  = intersection-lc(L, α)                   — line–circle intersection
let c  = intersection-lc-other(L, α, d)          — second line–circle intersection (given first)
```

### How a Proof Looks

Theorems are sequents:  **premises ⇒ ∃ witnesses. conclusions**

```
Prop I.1:   ¬(a = b)
            ⇒ ∃c.  ab = ac, ab = bc, c ≠ a, c ≠ b

Prop I.4:   ab = de, ac = df, ∠bac = ∠edf
            ⇒ bc = ef, ∠abc = ∠def, ∠acb = ∠dfe

Prop I.47:  ∠bac = right-angle, ...
            ⇒ ∃squares. BC² = AB² + AC²  (area decomposition)
```

### Verification Pipeline

```
                 ┌──────────────────────────────────────────────┐
User writes      │              unified_checker.py               │
proof steps  ──▶ │  ┌────────────┐ ┌──────────┐ ┌────────────┐ │ ──▶ ✓ / ✗
                 │  │ e_conse-   │ │ e_metric │ │ e_superpos- │ │   + diagnostics
                 │  │ quence     │ │          │ │ ition       │ │
                 │  └────────────┘ └──────────┘ └────────────┘ │
                 │  ┌───────────────┐  ┌──────────────────┐    │
                 │  │e_construction │  │ e_transfer       │    │
                 │  └───────────────┘  └──────────────────┘    │
                 └──────────────────────────────────────────────┘
```

---

## 📖 All 48 Propositions

| # | Proposition | Type | Proof |
|---|------------|------|:-----:|
| **I.1** | Construct an equilateral triangle | Construction | ✅ |
| **I.2** | Transfer a segment to a given point | Construction | ✅ |
| **I.3** | Cut off a segment equal to a shorter one | Construction | ✅ |
| **I.4** | **SAS** — Side-Angle-Side congruence | Congruence | ✅ |
| **I.5** | Base angles of an isosceles triangle are equal | Triangle | ✅ |
| **I.6** | Equal base angles imply isosceles | Triangle | ✅ |
| **I.7** | Uniqueness of triangle construction | Triangle | ✅ |
| **I.8** | **SSS** — Side-Side-Side congruence | Congruence | ✅ |
| **I.9** | Bisect an angle | Construction | ✅ |
| **I.10** | Bisect a segment (find midpoint) | Construction | ✅ |
| **I.11** | Erect a perpendicular from a point on a line | Construction | ✅ |
| **I.12** | Drop a perpendicular from a point to a line | Construction | ✅ |
| **I.13** | Supplementary angles sum to two right angles | Angles | ✅ |
| **I.14** | Angles summing to two right angles form a straight line | Angles | ✅ |
| **I.15** | Vertical angles are equal | Angles | ✅ |
| **I.16** | Exterior angle > either remote interior angle | Inequality | |
| **I.17** | Two angles of a triangle < two right angles | Inequality | |
| **I.18** | Greater side opposite greater angle | Inequality | |
| **I.19** | Greater angle opposite greater side | Inequality | |
| **I.20** | Triangle inequality | Inequality | |
| **I.21** | Triangle within triangle: shorter sides, larger angle | Inequality | |
| **I.22** | Construct triangle from three segments | Construction | |
| **I.23** | Copy an angle | Construction | |
| **I.24** | Open hinge inequality | Inequality | |
| **I.25** | Converse hinge inequality | Inequality | |
| **I.26** | **ASA / AAS** congruence | Congruence | |
| **I.27** | Alternate interior angles ⇒ parallel | Parallels | |
| **I.28** | Exterior angle = remote interior ⇒ parallel | Parallels | |
| **I.29** | Parallel ⇒ alternate angles equal *(Postulate 5)* | Parallels | |
| **I.30** | Lines parallel to the same line are parallel | Parallels | |
| **I.31** | Construct a parallel through a point | Construction | |
| **I.32** | Exterior angle = sum of remote interiors; angle sum = 2R | Angle Sum | |
| **I.33** | Joining equal parallel segments → parallelogram | Parallelograms | |
| **I.34** | Opposite sides/angles of a parallelogram are equal | Parallelograms | |
| **I.35** | Parallelograms on same base, same parallels → equal area | Area | |
| **I.36** | Parallelograms on equal bases, same parallels → equal area | Area | |
| **I.37** | Triangles on same base, same parallels → equal area | Area | |
| **I.38** | Triangles on equal bases, same parallels → equal area | Area | |
| **I.39** | Equal triangles on same base → same parallels | Area | |
| **I.40** | Equal triangles on equal bases → same parallels | Area | |
| **I.41** | Parallelogram = 2× triangle (same base, same parallels) | Area | |
| **I.42** | Construct parallelogram equal to triangle in given angle | Construction | |
| **I.43** | Complements about the diagonal are equal | Area | |
| **I.44** | Apply parallelogram to segment in given angle | Construction | |
| **I.45** | Construct parallelogram equal to rectilineal figure | Construction | |
| **I.46** | Construct a square on a given segment | Construction | |
| **I.47** | **Pythagorean theorem** 🎉 | Area | |
| **I.48** | Converse of the Pythagorean theorem | Area | |

---

## 💻 Python API

```python
from verifier.unified_checker import verify_named_proof, get_theorem

result = verify_named_proof("Prop.I.1")
print(result.valid)   # True
print(result.engine)  # 'E'

thm = get_theorem("Prop.I.47")
print(thm.sequent)
```

```bash
# Verify a proof file from the command line
python -m verifier.cli proof.json

# Launch the GUI
python -m euclid_py
```

---

## 🧪 Testing

**667+ tests** across the verifier engine and UI layer:

```bash
python -m pytest                                   # everything
python -m pytest verifier/tests/ -v                # 667 verifier tests
python -m pytest euclid_py/tests/ -v               # UI tests
python -m pytest verifier/tests/test_e_system.py   # all 48 propositions
```

---

## 📁 Project Structure

```
Euclid/
├── run_euclid.py                  # App entry point
├── launch_euclid.pyw              # Windowless launcher (no console)
├── build_exe.py                   # PyInstaller build script
├── euclid.spec                    # PyInstaller config
├── pyproject.toml                 # Project metadata & dependencies
├── requirements.txt               # pip install -r requirements.txt
│
├── euclid_py/                     # ── Desktop application (PyQt6) ──
│   ├── __main__.py                # python -m euclid_py
│   ├── resources.py               # Bundled resource path resolver
│   ├── ui/
│   │   ├── main_window.py         # Main window, toolbar, sidebar
│   │   ├── proof_panel.py         # Proof editor + autofill engine
│   │   ├── proof_editor.py        # Proof text editing widget
│   │   ├── proof_view.py          # Proof rendering view
│   │   ├── canvas_widget.py       # Interactive geometry canvas
│   │   ├── rule_reference.py      # Searchable rule catalog
│   │   ├── diagnostics_panel.py   # Error / warning display
│   │   ├── summary_panel.py       # Proof summary view
│   │   └── fitch_theme.py         # Theming constants
│   ├── engine/
│   │   ├── proposition_data.py    # UI metadata for 48 propositions
│   │   ├── constraints.py         # Diagram constraint solver
│   │   ├── file_format.py         # .euclid save / load
│   │   ├── predicates.py          # Predicate helpers
│   │   └── rules.py               # Rule definitions
│   └── tests/                     # 154 pytest tests
│
├── verifier/                      # ── Formal verification engine ──
│   ├── unified_checker.py         # ★ Main entry point
│   ├── e_ast.py                   # Sorts, literals, sequents
│   ├── e_axioms.py                # All axiom clauses (§3.4–3.6)
│   ├── e_axiom_match.py           # Named axiom matching
│   ├── e_consequence.py           # Forward-chaining engine (§3.8)
│   ├── e_construction.py          # Construction rules (21 rules)
│   ├── e_metric.py                # Segment / angle / area congruence
│   ├── e_transfer.py              # Diagram ↔ metric transfer
│   ├── e_superposition.py         # SAS / SSS
│   ├── e_checker.py               # Step-by-step proof checker
│   ├── e_library.py               # 48 theorem sequents
│   ├── e_proofs.py                # Encoded proof steps
│   ├── e_parser.py                # Formula parser
│   ├── e_elaborator.py            # Proof elaboration
│   ├── e_backward.py              # Backward reasoning
│   ├── e_discovery.py             # Axiom discovery
│   ├── cli.py                     # Command-line interface
│   ├── smt_backend.py             # SMT solver integration
│   ├── tptp_backend.py            # TPTP export
│   └── tests/                     # 862 pytest tests
│
├── docs/
│   └── verifier-architecture.md   # Verifier architecture documentation
│
├── solved_proofs/                 # 15 verified .euclid proof files (I.1–I.15)
├── unsolved_proofs/               # Starter .euclid files for all 48 propositions
├── lemmas/                        # 6 reusable lemma proofs
├── ref/                           # Reference PDFs and extracted text
└── scripts/                       # Utility scripts
    ├── test_all_solved.py         # Verify all solved proofs
    ├── real_proofs.py             # Book I proofs (executable)
    └── identify_axioms.py         # Axiom identification tool
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
pip install -r requirements.txt
pip install -e .[dev]             # includes PyInstaller
```

---

## 📚 References

- Avigad, J., Dean, E., & Mumma, J. (2009). [A Formal System for Euclid's Elements.](https://doi.org/10.1017/S1755020309990098) *Review of Symbolic Logic*, 2(4), 700–768.
- Beeson, M., Narboux, J., & Wiedijk, F. (2018). [Proof-checking Euclid.](https://doi.org/10.1007/s10472-018-9606-x) *Annals of Mathematics and Artificial Intelligence*.

---

## 📄 License

MIT — see [LICENSE](LICENSE) for details.

<div align="center">
<br>
<sub>Made with probably too much caffeine.</sub>
</div>
