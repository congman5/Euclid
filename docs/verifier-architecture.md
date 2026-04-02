# System E Verifier — Architecture Documentation

Technical documentation for the formal proof verifier implementing System E
(Avigad, Dean & Mumma 2009, *"A Formal System for Euclid's Elements"*).

---

## Table of Contents

1. [Overview](#1-overview)
2. [Theoretical Foundation](#2-theoretical-foundation)
3. [AST and Formal Language — `e_ast.py`](#3-ast-and-formal-language)
4. [Axiom System — `e_axioms.py`](#4-axiom-system)
5. [Construction Rules — `e_construction.py`](#5-construction-rules)
6. [Consequence Engine — `e_consequence.py`](#6-consequence-engine)
7. [Metric Engine — `e_metric.py`](#7-metric-engine)
8. [Transfer Engine — `e_transfer.py`](#8-transfer-engine)
9. [Superposition — `e_superposition.py`](#9-superposition)
10. [Proof Checker Pipeline — `e_checker.py`, `unified_checker.py`](#10-proof-checker-pipeline)
11. [Theorem Library — `e_library.py`](#11-theorem-library)
12. [Proof Encodings — `e_proofs.py`](#12-proof-encodings)
13. [Parser — `e_parser.py`](#13-parser)
14. [Elaborator — `e_elaborator.py`](#14-elaborator)
15. [Axiom Matching — `e_axiom_match.py`](#15-axiom-matching)
16. [Additional Components](#16-additional-components)
17. [Extensions Beyond the Paper](#17-extensions-beyond-the-paper)
18. [Test Suite](#18-test-suite)
19. [References](#19-references)

---

## 1. Overview

The verifier is a self-contained Python package (`verifier/`) that checks
formal proofs in System E — the axiom system for Euclid's plane geometry
described in Avigad, Dean & Mumma (2009). It encodes all 48 propositions from
Book I of Euclid's *Elements* as formal sequents and ships with verified proofs
for Propositions I.1–I.15.

### Design Principles

1. **Faithfulness to the paper.** Sorts, predicates, axiom clauses, and
   inference rules map directly to Sections 3.3–3.8 of the paper. Variable
   naming conventions follow the paper's schema notation.

2. **Separation of concerns.** Each inference mode (diagrammatic, metric,
   transfer, superposition) lives in its own module with a clear API.  The
   proof checker composes them without any module knowing about the others.

3. **Soundness over convenience.** The checker never accepts a step just
   because the result "looks right." Every assertion must be justified by an
   explicit axiom clause, a metric derivation, a transfer rule, or a
   previously proved theorem.

4. **Two checker tiers.** The *standard checker* (`e_checker.py`) allows
   theorem-justified steps where assertions are accepted on the authority of a
   cited proposition. The *kernel checker* (`kernel_checker.py`) is strictly
   primitive — every step must cite an exact rule.

### Module Dependency Graph

```
e_ast.py                     ← Pure data: sorts, terms, atoms, literals, clauses, sequents
   │
   ├── e_axioms.py           ← Axiom clauses (§3.4–3.6) built from AST types
   │     │
   │     ├── e_consequence.py ← Forward-chaining closure (§3.8)
   │     ├── e_transfer.py    ← Diagram ↔ metric bridge
   │     └── e_axiom_match.py ← Named axiom lookup
   │
   ├── e_construction.py     ← 21 construction rules (§3.3)
   ├── e_metric.py           ← Magnitude reasoning (§3.5, CN1–CN5, M1–M9)
   ├── e_superposition.py    ← SAS / SSS triangle congruence (§3.7)
   ├── e_parser.py           ← Text → AST
   │
   ├── e_checker.py          ← Step-by-step proof checker (composes all engines)
   ├── kernel_checker.py     ← Strict primitive-only checker
   │
   ├── e_library.py          ← 48 theorem sequents (Γ ⇒ ∃x̄. Δ)
   ├── e_proofs.py           ← Proof step encodings for all 48 propositions
   │
   ├── e_elaborator.py       ← Tactic engine: high-level → primitive steps
   ├── e_backward.py         ← Backward proof search (prototype)
   ├── e_discovery.py        ← "What can I derive?" oracle
   │
   ├── unified_checker.py    ← ★ Main entry point (routes EProof + JSON proofs)
   │
   ├── smt_backend.py        ← SMT-LIB 2.6 encoding (Z3 / CVC5)
   ├── tptp_backend.py       ← TPTP FOF encoding (E-prover / Vampire)
   └── geocoq_compat.py      ← GeoCoq name mapping
```

---

## 2. Theoretical Foundation

System E (Avigad, Dean & Mumma 2009) formalizes the style of reasoning in
Euclid's *Elements* by separating geometric inference into four layers:

| Layer | Decides | Engine |
|-------|---------|--------|
| **Diagrammatic** | Incidence, betweenness, same-side, circle interiority | `e_consequence.py` |
| **Metric** | Segment / angle / area congruence and ordering | `e_metric.py` |
| **Transfer** | Bridge between diagram and metric facts | `e_transfer.py` |
| **Superposition** | SAS and SSS triangle congruence | `e_superposition.py` |

A proof in System E is a sequence of steps, each of which:
- **Constructs** new objects (points, lines, circles), or
- **Derives** new assertions about existing objects using one of the four layers, or
- **Applies** a previously proved proposition.

Theorems are sequents of the form:

```
Γ  ⇒  ∃x̄. Δ
```

where Γ (hypotheses) and Δ (conclusions) are sets of literals, and x̄ are
existentially quantified variables introduced by construction steps.

### Soundness

The paper proves (Theorem 5.3) that System E is sound with respect to
ruler-and-compass constructions: anything provable in E is true in every
Euclidean plane. The bridge goes through Tarski's axiom system, which is also
the foundation of the GeoCoq library in Coq.

---

## 3. AST and Formal Language

**File:** `verifier/e_ast.py`

The AST defines the six-sorted language of System E.

### 3.1 Sorts

```python
class Sort(Enum):
    POINT   = auto()   # Geometric points: a, b, c, ...
    LINE    = auto()   # Straight lines: L, M, N, ...
    CIRCLE  = auto()   # Circles: α, β, γ, ...
    SEGMENT = auto()   # Magnitude sort: segment lengths
    ANGLE   = auto()   # Magnitude sort: angle measures
    AREA    = auto()   # Magnitude sort: triangle areas
```

The first three are *diagram sorts* (have variables); the last three are
*magnitude sorts* (constructed from point terms).

### 3.2 Terms

| Type | Notation | Normalization | Paper rule |
|------|----------|---------------|------------|
| `SegmentTerm(a, b)` | `ab` | `ab = ba` (sorted pair) | M3 |
| `AngleTerm(a, b, c)` | `∠abc` | `∠abc = ∠cba` (vertex fixed, endpoints sorted) | M4 |
| `AreaTerm(a, b, c)` | `△abc` | All 6 permutations equal (sorted triple) | M8 |
| `MagAdd(left, right)` | `x + y` | — | §3.5 |
| `RightAngle()` | `∟` | Constant | §3.5 |
| `ZeroMag(sort)` | `0` | Per-sort zero | §3.5 |

Normalization is built into `__eq__` and `__hash__` via `_canonical()` methods,
so `SegmentTerm("a","b") == SegmentTerm("b","a")` automatically.

### 3.3 Atomic Formulas

| Atom | Arity | Symmetry | Domain |
|------|------:|----------|--------|
| `On(point, obj)` | 2 | — | point × (line ∪ circle) |
| `SameSide(a, b, line)` | 3 | `ss(a,b,L) = ss(b,a,L)` | point × point × line |
| `Between(a, b, c)` | 3 | — | point × point × point |
| `Center(point, circle)` | 2 | — | point × circle |
| `Inside(point, circle)` | 2 | — | point × circle |
| `Intersects(obj1, obj2)` | 2 | symmetric | (line∪circle) × (line∪circle) |
| `Equals(left, right)` | 2 | symmetric | any sort |
| `LessThan(left, right)` | 2 | — | magnitude × magnitude |

### 3.4 Literals and Clauses

A **literal** is an atom with a polarity (positive or negative):

```python
@dataclass(frozen=True)
class Literal:
    atom: Atom
    polarity: bool = True  # True = asserted, False = negated
```

A **clause** is a frozen set of literals, read disjunctively. The axiom
"if φ₁ ∧ … ∧ φₙ then ψ" is encoded as the clause `{¬φ₁, …, ¬φₙ, ψ}`.
This form enables contrapositive forward-chaining: if all but one literal's
negation is known, the remaining literal is derived.

### 3.5 Sequents and Proofs

```python
@dataclass
class Sequent:
    hypotheses: List[Literal]      # Γ
    exists_vars: List[(str, Sort)] # x̄ (existential witnesses)
    conclusions: List[Literal]     # Δ

class StepKind(Enum):
    CONSTRUCTION        # Introduce new objects
    AXIOM_ELIM          # Derive from axiom schemas
    SUPERPOSITION_SAS   # SAS triangle congruence
    SUPERPOSITION_SSS   # SSS triangle congruence
    THEOREM_APP         # Apply a proved proposition
    BOT_INTRO           # ⊥-introduction (contradiction)
    BOT_ELIM            # ⊥-elimination (discharge assumption)
    CASE_SPLIT_ELIM     # Case analysis
```

An `EProof` bundles free variables, hypotheses, existential witnesses, goal
literals, and a list of `ProofStep` objects.

---

## 4. Axiom System

**File:** `verifier/e_axioms.py`

All axioms from §3.4–3.6 of the paper, encoded as clauses. Each axiom is a
*schema* — the variables (`a`, `b`, `L`, `α`, …) are instantiated with
actual names during forward-chaining.

### 4.1 Diagrammatic Axioms (§3.4) — 52 clauses

| Group | Label | Clauses | Key content |
|-------|-------|--------:|-------------|
| Generalities | G1–G6 | 9 | Two points determine a line; points on a line; distinctness |
| Betweenness | B1a–d, B2–B7 | 10 | Strict betweenness, symmetry, collinearity, Pasch-like properties |
| Same-side | SS1–SS5 | 6 | Reflexivity, symmetry, transitivity, relationship to betweenness |
| Pasch | P1–P4 | 4 | Pasch's axiom variants (line crossing a triangle side) |
| Triple incidence | TI1–TI3 | 3 | Three collinear points on two lines ⇒ lines equal |
| Circle | C1–C4 | 10 | Center uniqueness, inside/on/outside trichotomy, interiority |
| Intersection | I1–I5 | 10 | Line–line, line–circle, circle–circle intersection existence |

### 4.2 Transfer Axioms (§3.6) — 25 clauses

| Group | Label | Clauses | Key content |
|-------|-------|--------:|-------------|
| Segment transfer | DS1–DS4d | 8 | `between(a,b,c) → ab + bc = ac`; circle radius equalities |
| Angle transfer | DA1a–DA6 | 13 | Angle addition from betweenness and same-side; supplementary angles |
| Area transfer | DAr1a–DAr2 | 4 | Triangle area decomposition from betweenness |

### 4.3 Encoding Pattern

Every axiom "if φ₁ ∧ … ∧ φₙ then ψ₁ ∨ … ∨ ψₘ" becomes one or more clauses:

```python
# B3: between(a,b,c) → between(c,b,a)   (symmetry)
_clause(_neg(Between("a","b","c")), _pos(Between("c","b","a")))

# B6: a ≠ b ∧ a ≠ c ∧ on(a,L) ∧ on(b,L) ∧ on(c,L) →
#     between(a,b,c) ∨ between(b,c,a) ∨ between(a,c,b)
# Split into three clauses (one per disjunct):
_clause(_pos(Equals("a","b")), _pos(Equals("a","c")),
        _neg(On("a","L")), _neg(On("b","L")), _neg(On("c","L")),
        _pos(Between("a","b","c")),
        _pos(Between("b","c","a")),
        _pos(Between("a","c","b")))
```

Multi-conclusion axioms produce clauses with multiple positive literals.
The forward-chaining engine handles these via the "all-but-one negated"
contrapositive rule.

---

## 5. Construction Rules

**File:** `verifier/e_construction.py`

Construction rules are the *only* way to introduce new objects into a proof.
There are **21 rules** in three categories.

### 5.1 Point Construction (9 rules)

| Rule | Prerequisites | Introduces | Conclusions |
|------|--------------|------------|-------------|
| `let-point` | — | point `a` | — |
| `let-point-on-line` | — | point `a` | `on(a, L)` |
| `let-point-on-line-between` | `on(b,L), on(c,L), b≠c` | point `a` | `on(a,L), between(b,a,c)` |
| `let-point-on-line-extend` | `on(b,L), on(c,L), b≠c` | point `a` | `on(a,L), between(b,c,a)` |
| `let-point-same-side` | `¬on(b,L)` | point `a` | `same-side(a,b,L)` |
| `let-point-opposite-side` | `¬on(b,L)` | point `a` | `¬same-side(a,b,L), ¬on(a,L)` |
| `let-point-on-circle` | — | point `a` | `on(a, α)` |
| `let-point-inside-circle` | — | point `a` | `inside(a, α)` |
| `let-point-outside-circle` | — | point `a` | `¬on(a,α), ¬inside(a,α)` |

### 5.2 Line and Circle Construction (2 rules)

| Rule | Prerequisites | Introduces | Conclusions |
|------|--------------|------------|-------------|
| `let-line` | `a ≠ b` | line `L` | `on(a,L), on(b,L)` |
| `let-circle` | `a ≠ b` | circle `α` | `center(a,α), on(b,α)` |

### 5.3 Intersection Construction (10 rules)

| Rule | Prerequisites | Introduces | Key conclusions |
|------|--------------|------------|-----------------|
| `let-intersection-line-line` | `intersects(L,M)` | point `a` | `on(a,L), on(a,M)` |
| `let-intersection-circle-line-one` | `intersects(L,α)` | point `a` | `on(a,L), on(a,α)` |
| `let-intersection-circle-line-two` | `intersects(L,α)` | points `a,b` | `on(a,α), on(b,α), on(a,L), on(b,L), a≠b` |
| `let-intersection-line-circle-between` | `on(c,α), on(c,L), on(b,L), inside(b,α), b≠c` | point `a` | `on(a,α), on(a,L), between(a,b,c)` |
| `let-intersection-line-circle-extend` | `on(c,α), on(c,L), on(b,L), inside(b,α)` | point `a` | `on(a,α), on(a,L), between(c,b,a)` |
| `let-intersection-line-circle-other` | `on(c,α), on(c,L), inside(b,α), on(b,L)` | point `a` | `on(a,α), on(a,L), between(c,b,a)` |
| `let-intersection-circle-circle-one` | `intersects(α,β)` | point `a` | `on(a,α), on(a,β)` |
| `let-intersection-circle-circle-two` | `intersects(α,β)` | points `a,b` | `on(a,α), on(a,β), on(b,α), on(b,β), a≠b` |
| `let-intersection-circle-circle-same-side` | `intersects(α,β), on(c,L), on(d,L), center(c,α), center(d,β), ¬on(e,L)` | point `a` | `on(a,α), on(a,β), same-side(a,e,L)` |
| `let-intersection-circle-circle-opposite-side` | (same as above) | point `a` | `on(a,α), on(a,β), ¬same-side(a,e,L), ¬on(a,L)` |

### 5.4 Implementation

Each rule is a `ConstructionRule` dataclass with pattern-based prerequisite
matching. The checker validates that prerequisites are satisfied by known
facts before registering the new variables and adding conclusion literals.

```python
@dataclass
class ConstructionRule:
    name: str                             # Lookup key (e.g. "let-line")
    category: str                         # "point", "line_circle", "intersection"
    prereq_pattern: List[Literal]         # Must be satisfied
    new_vars: List[Tuple[str, Sort]]      # Fresh variables introduced
    conclusion_pattern: List[Literal]     # Added to known facts
```

`CONSTRUCTION_RULE_BY_NAME` is the dict used for O(1) rule lookup by the
checker.

---

## 6. Consequence Engine

**File:** `verifier/e_consequence.py`

Implements the polynomial-time forward-chaining algorithm from Proposition 3.2
of the paper (§3.8). This is the core of diagrammatic reasoning.

### 6.1 Algorithm

Given a set Δ of known literals and axiom clauses S:

1. **Ground** all axiom schemas over the current variables (points, lines,
   circles), producing a set of ground clauses.
2. **Compile** clauses into an indexed format: for each clause, pre-compute
   the negated literals and build resolution/satisfaction indices.
3. **Seed** structural truths (degenerate betweenness — see §6.3).
4. **Worklist loop**: pop a literal from the worklist; for each clause where
   this literal resolves a position, check if all other literals' negations
   are known. If so, derive the remaining literal and add it to the
   worklist.
5. **Fixpoint**: stop when no new literals are derived, or when a
   contradiction is found (both φ and ¬φ in the closure).

### 6.2 Performance Optimizations

- **Pre-compiled clauses**: Ground clauses are compiled into tuples of
  `(literal, negated_literal)` pairs with pre-computed hash lookups.
- **Resolution index**: `res_index[f]` maps a literal `f` to the clause
  indices where knowing `f` resolves a position.
- **Satisfaction index**: `sat_index[L]` maps a literal `L` to clause indices
  it satisfies (early-exit when a clause is already satisfied).
- **Satisfaction bitvector**: A `bytearray` tracks which clauses are already
  satisfied, avoiding redundant work.
- **Ground cache**: Ground clauses are cached keyed on `frozenset(variables.items())`
  to avoid regeneration when variables haven't changed.

### 6.3 Degenerate Betweenness Seeding

At the start of closure, the engine seeds `¬between(x, y, x)` for all
point pairs. This is a structural truth (betweenness with identical endpoints
is absurd) that the axiom clauses alone cannot derive, since B1c's
contrapositive requires knowing `a ≠ a` which is never in the fact set. The
seeding is necessary for angle transfer axiom DA4, which has
`¬between(a, c, a)` as a hypothesis.

### 6.4 Leibniz E2 Equality Substitution

When a point equality `a = b` is known, every diagrammatic literal `φ(a)` in
the closure also yields `φ(b)` and vice versa. The engine tracks equality
pairs and applies substitution to both existing closure literals and newly
derived ones. This extends the standard forward-chaining with an equality
reasoning layer that the paper leaves implicit under "Leibniz rule E2."

### 6.5 Contradiction Detection

Two mechanisms:
1. **Direct**: If both φ and ¬φ are in the closure, BOTTOM is injected and
   the closure becomes trivially contradictory (everything follows).
2. **Clause exhaustion**: If all disjuncts of a ground clause are negated
   in the closure, a `_CLAUSE_CONTRADICTION` sentinel triggers BOTTOM
   injection. This handles cases like B6 betweenness trichotomy where all
   three orderings are negated.

---

## 7. Metric Engine

**File:** `verifier/e_metric.py`

Handles reasoning about magnitudes (segments, angles, areas) in a
non-negative ordered abelian group ⟨ℝ⁺, 0, +, <⟩.

### 7.1 Architecture

The engine uses two core data structures:

- **Union-find** for equality classes of magnitude terms. When `ab = cd` is
  known, `SegmentTerm("a","b")` and `SegmentTerm("c","d")` are merged into
  the same equivalence class.
- **Inequality set** for strict orderings `a < b`, with consistency checks
  against known equalities.

### 7.2 Supported Rules

| Rule | Paper | Description |
|------|-------|-------------|
| CN1 | §3.5 | Transitivity: `a = b ∧ b = c → a = c` (via union-find) |
| CN2 | §3.5 | Addition: `a = b ∧ c = d → a+c = b+d` |
| CN3 | §3.5 | Subtraction/cancellation: `a+c = b+c → a = b` |
| CN4 | §3.5 | Reflexivity: `a = a` |
| CN5 | §3.5 | Whole > part: `0 < y → z < y + z` |
| M1 | §3.5 | `ab = 0 ↔ a = b` (segment zero ↔ point equality) |
| M3 | §3.5 | `ab = ba` (built into `SegmentTerm` normalization) |
| M4 | §3.5 | `∠abc = ∠cba` (built into `AngleTerm` normalization) |
| M8 | §3.5 | `△abc = △cab = △acb = …` (built into `AreaTerm` normalization) |
| M9 | §3.5 | Full congruence → equal areas |

### 7.3 API

```python
class MetricEngine:
    def process_literals(self, literals: Set[Literal]) -> None
    def is_consequence(self, query: Literal) -> bool
    def reset(self) -> None
```

The engine processes all known metric literals at once (loading equalities
and inequalities into the union-find and inequality set), then answers
queries by checking if the query can be read off from the resulting state.

---

## 8. Transfer Engine

**File:** `verifier/e_transfer.py`

Transfer axioms bridge diagrammatic and metric facts. They have diagrammatic
hypotheses and metric conclusions (or vice versa).

### 8.1 Examples

| Axiom | Direction | Statement |
|-------|-----------|-----------|
| DS1 | Diagram → Metric | `between(a,b,c) → ab + bc = ac` |
| DS3b | Diagram → Metric | `center(a,α) ∧ on(b,α) ∧ on(c,α) → ab = ac` |
| DS4a | Metric → Diagram | `center(a,α) ∧ on(b,α) ∧ ab = ac → on(c,α)` |
| DA4 | Diagram → Metric | `on(c,L) ∧ on(c,M) ∧ L≠M ∧ ¬between(a,c,a) ∧ … → ∠acb = ∠dcb` |
| DA6 | Mixed | Supplementary angle relationships |

### 8.2 Implementation

The `TransferEngine` reuses the consequence engine's forward-chaining
infrastructure but operates over transfer axiom clauses instead of
diagrammatic ones. It takes both a diagrammatic fact set and a metric fact set,
and returns newly derivable literals.

```python
class TransferEngine:
    def apply_transfers(
        self,
        diagram_known: Set[Literal],
        metric_known: Set[Literal],
        variables: Dict[str, Sort],
    ) -> Set[Literal]
```

---

## 9. Superposition

**File:** `verifier/e_superposition.py`

Superposition provides SAS (Proposition I.4) and SSS (Proposition I.8)
triangle congruence as elimination rules (§3.7 of the paper).

### 9.1 Conceptual Model

Superposition allows one to "act as though" a congruent copy of a triangle
has been constructed, but only for deriving facts about *existing* objects.
This avoids actually constructing the copy (which would require fresh
variables and change the diagram).

### 9.2 SAS Superposition

Given triangles △abc and △def with:
- `ab = de`, `ac = df`, `∠bac = ∠edf`

Derives:
- `bc = ef`, `∠abc = ∠def`, `∠acb = ∠dfe`, `△abc = △def`

### 9.3 SSS Superposition

Given triangles △abc and △def with:
- `ab = de`, `bc = ef`, `ca = fd`

Derives:
- `∠bac = ∠edf`, `∠abc = ∠def`, `∠acb = ∠dfe`, `∠bca = ∠efd`, `△abc = △def`

### 9.4 Implementation

```python
def apply_sas_superposition(known: Set[Literal], hyp: SuperpositionHypotheses) -> Set[Literal]
def apply_sss_superposition(known: Set[Literal], hyp: SuperpositionHypotheses) -> Set[Literal]
```

Both functions validate hypotheses against the known set, then return the
derived equalities. Segment equality checking accounts for all symmetry
variants (ab=cd, ba=cd, ab=dc, ba=dc).

---

## 10. Proof Checker Pipeline

### 10.1 Standard Checker — `e_checker.py`

The `EChecker` class composes all engines to check a complete `EProof`:

```python
class EChecker:
    def __init__(self, theorems: Dict[str, ETheorem]):
        self.consequence_engine = ConsequenceEngine()
        self.metric_engine = MetricEngine()
        self.transfer_engine = TransferEngine()
        self.known: Set[Literal] = set()
        self.variables: Dict[str, Sort] = {}

    def check_proof(self, proof: EProof) -> ECheckResult:
        # 1. Register free variables
        # 2. Load hypotheses into known
        # 3. Check each step:
        #    - CONSTRUCTION: validate rule or theorem justification
        #    - DIAGRAMMATIC/AXIOM_ELIM: verify via consequence engine
        #    - METRIC: verify via metric engine
        #    - TRANSFER: verify via transfer engine
        #    - SUPERPOSITION_SAS/SSS: verify via superposition
        #    - THEOREM_APP: validate hypotheses against known
        #    - BOT_INTRO: check for contradiction
        #    - CASE_SPLIT: check both branches
        # 4. Verify goal is established
```

#### Step Validation Modes

**Construction steps** have two modes:
1. **Primitive**: `description` matches a construction rule name → validate
   prerequisites against the rule pattern.
2. **Theorem-justified**: `theorem_name` is set → assertions accepted on the
   authority of the cited proposition (existential witness).

**Diagrammatic/Metric/Transfer steps**:
- If `theorem_name` is set: assertions accepted (theorem-justified).
- Otherwise: each assertion is checked against the relevant engine.

**⊥-intro** (contradiction): Triple-enhanced detection:
1. Direct literal pair: ψ and ¬ψ both in known.
2. Metric ordering: `X < Y` and `Y < X` both in known.
3. Consequence engine closure: running diagrammatic closure detects
   contradictions from axiom clause exhaustion.

### 10.2 Unified Checker — `unified_checker.py`

The main entry point that routes verification through two pathways:

#### Pathway 1: EProof objects (used by `e_proofs.py` tests)

```python
def verify_proof(proof: EProof, theorems=None) -> UnifiedResult
def verify_named_proof(proof_name: str) -> UnifiedResult
```

`verify_named_proof` loads the proof from `e_proofs.py`, retrieves the
available theorem library (excluding the proposition being proved to prevent
circularity), and runs it through `EChecker.check_proof()`.

#### Pathway 2: JSON proofs (used by the GUI proof panel)

```python
def verify_e_proof_json(proof_json: dict, on_line_checked=None) -> PanelCheckResult
```

This pathway:
1. Parses each proof line's statement string via `e_parser.py`.
2. Classifies the justification string to determine the step kind.
3. For **construction** steps: looks up the rule in `CONSTRUCTION_RULE_BY_NAME`.
4. For **axiom** steps: uses `e_axiom_match.py` to verify the *specific*
   named axiom (not just "some axiom from the category").
5. For **SAS/SSS**: invokes the superposition engine.
6. For **theorem applications**: substitutes and validates hypotheses.
7. For **⊥-intro** and **⊥-elim**: handles Fitch-style subproof discharge.
8. Provides per-line results with error messages for the UI.

### 10.3 Kernel Checker — `kernel_checker.py`

A strictly primitive checker that accepts *only* exact rule applications — no
consequence-closure fallback, no "some axiom from the category" shortcuts.
Every step must cite the specific rule it uses. This is the highest assurance
tier.

---

## 11. Theorem Library

**File:** `verifier/e_library.py`

Contains all 48 propositions from Book I as `ETheorem` objects. Each theorem
has:

- **name**: `"Prop.I.1"` through `"Prop.I.48"`
- **statement**: Euclid's natural-language statement
- **sequent**: The formal `Sequent` object with hypotheses, existential
  variables, and conclusions

### 11.1 Ordering

Propositions are ordered so that each one may only cite earlier ones.
The ordering is stored in `solved_proofs/.euclid_order.json` and enforced by
`get_theorems_up_to(name)`, which returns only theorems preceding `name`.

Notable ordering decision: **I.10 precedes I.9**. This breaks the historical
circular dependency where I.9 (bisect angle) used I.10 (bisect segment) and
vice versa. Following Beeson, Narboux & Wiedijk (2019), I.10 is proved
independently using the Gupta (1965) method, then I.9 invokes I.10.

### 11.2 Example Sequent

```
Prop I.4 (SAS):
  Hypotheses: ab = de, ac = df, ∠bac = ∠edf,
              a ≠ b, a ≠ c, d ≠ e, d ≠ f
  Conclusions: bc = ef, ∠abc = ∠def, ∠acb = ∠dfe, △abc = △def
```

---

## 12. Proof Encodings

**File:** `verifier/e_proofs.py`

Contains machine-checked proof outlines for all 48 propositions.
Each proof is a factory function returning an `EProof`:

```python
_STRUCTURED_PROOFS = {
    "Prop.I.1":  make_prop_i1_proof,   # Fully primitive (circles + intersection)
    "Prop.I.2":  _make_prop_i2,        # Cites I.1
    ...
    "Prop.I.48": _make_prop_i48,       # Cites I.47
}
```

### 12.1 Proof I.1 — Fully Primitive

The only proof that uses no previously proved theorems. It constructs two
circles, derives their intersection, and uses transfer axioms to establish
segment equalities:

```
1. let-circle α centered at a through b
2. let-circle β centered at b through a
3. Diagrammatic: inside(a,α), inside(b,β), intersects(α,β)
4. let-intersection-circle-circle-one c on α and β
5. Transfer: ac = ab (radii of α)
6. Transfer: bc = ba (radii of β)
7–10. Metric: ab = ac, ab = bc, c ≠ a, c ≠ b
```

### 12.2 Proof I.10 — Gupta Method

Proved independently (no I.9 dependency):

```
1. Construct circles α(a,ab) and β(b,ba), intersection c,e via circle-circle-two
2. Line K through c,e; intersection d with L; between(a,d,b)
3. SSS on △ace ≅ △bce → ∠ace = ∠bce
4. DA4 angle transfer + SAS on △acd ≅ △bcd → ad = db
```

### 12.3 Proof I.9 — Via I.10

```
1. Circle α(a,ab), intersections g,d on ray N
2. Prop.I.10 bisects bd → midpoint e with between(b,e,d), be = ed
3. SSS on △abe ≅ △ade → ∠bae = ∠dae
4. DA6 supplementary angles → ∠bae = ∠cae
5. Same-side conclusions via Pasch
```

### 12.4 Verification

All 48 proof outlines are validated by `verify_named_proof()` in the test
suite. Construction steps use either primitive rule names or `theorem_name`
for theorem-justified acceptance. Metric and diagrammatic steps that would
require the full engine to verify use `theorem_name` as well (the outline
captures the proof *structure*, not every primitive step).

---

## 13. Parser

**File:** `verifier/e_parser.py`

Parses the literal language of System E from text strings into AST objects.

### 13.1 Supported Syntax

```
on(a, L)                    → On("a", "L")
between(a, b, c)            → Between("a", "b", "c")
same-side(a, b, L)          → SameSide("a", "b", "L")
center(a, α)                → Center("a", "α")
inside(a, α)                → Inside("a", "α")
intersects(L, α)            → Intersects("L", "α")
ab = cd                     → Equals(SegmentTerm("a","b"), SegmentTerm("c","d"))
∠abc = ∠def                 → Equals(AngleTerm("a","b","c"), AngleTerm("d","e","f"))
△abc = △def                 → Equals(AreaTerm("a","b","c"), AreaTerm("d","e","f"))
ab < cd                     → LessThan(SegmentTerm("a","b"), SegmentTerm("c","d"))
ab + cd = ef                → Equals(MagAdd(...), SegmentTerm("e","f"))
¬on(a, L)                   → Literal(On("a","L"), polarity=False)
a ≠ b                       → Literal(Equals("a","b"), polarity=False)
right-angle                 → RightAngle()
```

### 13.2 Sort Inference

The parser uses a `SortContext` to track which identifiers are points, lines,
or circles. Sort is inferred from position in predicates (e.g., the first
argument of `on(_, _)` is a point; the second is a line or circle).

---

## 14. Elaborator

**File:** `verifier/e_elaborator.py`

The elaborator is a *tactic engine* that transforms high-level proof steps
into fully explicit primitive steps.

### 14.1 Design Contract

- Elaboration runs **before** strict checking.
- The strict checker only sees primitive steps.
- If elaboration fails, the original step is preserved — the checker reports
  the real error. This means elaboration bugs cause failures, **never
  unsoundness**.

### 14.2 Tactic Examples

| High-level justification | Elaboration |
|--------------------------|-------------|
| `"Metric"` | Identify which CN/M rule applies, fill in the specific axiom |
| `"Diagrammatic"` | Run consequence closure, identify the deriving axiom |
| `"Transfer"` | Run transfer engine, identify the specific DS/DA rule |
| `"SAS"` / `"SSS"` | Find triangle correspondence, invoke superposition |

---

## 15. Axiom Matching

**File:** `verifier/e_axiom_match.py`

When a proof step cites a specific axiom by name (e.g., "Pasch 3" or
"Segment transfer 4"), this module verifies that the *exact* cited axiom
derives the claimed conclusion from the cited dependency lines.

### 15.1 Axiom Registry

All axioms are registered under paper-label names:

```
"Generality 1" through "Generality 6"     (G1–G6)
"Betweenness 1a" through "Betweenness 7"  (B1a–d, B2–B7)
"Same-side 1" through "Same-side 5"       (SS1–SS5)
"Pasch 1" through "Pasch 4"               (P1–P4)
...
```

Sequential numeric aliases are also registered for backward compatibility
(e.g., "Betweenness 4" maps to B1d when the sequential index differs from
the label).

### 15.2 Matching Algorithm

```python
def check_specific_axiom(
    axiom_name: str,
    ref_facts: Set[Literal],
    target: Literal,
    variables: Dict[str, Sort],
) -> bool
```

1. Look up the clause for `axiom_name`.
2. Ground the clause over all variable substitutions.
3. For each ground instance: check if all but one literal's negation is in
   `ref_facts`, and the remaining literal matches `target`.

---

## 16. Additional Components

### 16.1 Backward Search — `e_backward.py`

A depth-limited backward-chaining proof search prototype. Given premises and
goals, it searches backward through axioms and theorems to find a derivation
path. **Does not handle constructions** — the proof writer must supply
`let-line`, `let-circle`, and `let-intersection-*` steps manually.

### 16.2 Discovery Tool — `e_discovery.py`

An oracle that runs the full pipeline (diagrammatic closure → transfer →
metric) and reports *all* derivable facts, grouped by type. Designed to
help proof writers understand what follows from the current proof state.

### 16.3 SMT Backend — `smt_backend.py`

Encodes System E axioms and proof obligations in SMT-LIB 2.6 format for
Z3 and CVC5. The paper (§6) notes that most inferences are instantaneous
under SMT solvers.

### 16.4 TPTP Backend — `tptp_backend.py`

Encodes axioms in TPTP first-order format (FOF) for E-prover, SPASS, and
Vampire.

### 16.5 GeoCoq Compatibility — `geocoq_compat.py`

Maps System E predicate and axiom names to their GeoCoq Coq identifiers.
GeoCoq provides machine-checked proofs of the equivalence between System E
and Tarski's axiom system (`euclidean_axioms.v`, `tarski_to_euclid.v`).

### 16.6 CLI — `verifier/cli.py`

Command-line interface for verifying proof files:

```bash
python -m verifier.cli proof.json
```

---

## 17. Extensions Beyond the Paper

The implementation includes several extensions not present in Avigad, Dean &
Mumma (2009):

### 17.1 Degenerate Betweenness Seeding

The consequence engine seeds `¬between(x, y, x)` for all point pairs.
This structural truth is needed for DA4 angle transfer but is not derivable
from the axiom clauses alone.

### 17.2 Leibniz E2 Equality Substitution

The consequence engine applies Leibniz substitution when point equalities
are known. The paper mentions this rule but does not detail how it interacts
with forward-chaining.

### 17.3 Enhanced ⊥-intro

The contradiction handler supports three detection modes (literal pair,
metric ordering contradiction, and consequence engine clause exhaustion).
The paper only specifies the first.

### 17.4 Construction Rule Extensions

The paper defines 6 basic construction forms; the implementation provides 21
rules, including:
- Directed intersection (`let-intersection-line-circle-between/extend/other`)
- Same-side/opposite-side circle–circle intersection
- Point placement (`let-point-same-side`, `let-point-opposite-side`, etc.)

### 17.5 I.10/I.9 Ordering Resolution

Following Beeson, Narboux & Wiedijk (2019), the implementation proves I.10
independently (Gupta 1965 method) and then I.9 from I.10, avoiding the
historical circular dependency.

### 17.6 Theorem-Justified Construction Steps

The checker allows construction steps to cite a previously proved theorem
(via `theorem_name`) instead of a primitive rule. This enables multi-step
constructions to be summarized as a single step justified by the existence
guarantee of an earlier proposition.

---

## 18. Test Suite

**667 verifier tests** organized across multiple files:

| File | Tests | Scope |
|------|------:|-------|
| `test_e_system.py` | ~180 | All 48 propositions: sequent shape, proof validity, axiom counts |
| `test_unified_checker.py` | ~120 | JSON proof pathway, per-line verification, axiom matching |
| `test_all_48_proofs.py` | 48 | Each proposition verified end-to-end |
| `test_library_i11_i15.py` | ~50 | Propositions I.6–I.15: sequents, ordering, proof structure |
| `test_library_i16_i26.py` | ~50 | Propositions I.16–I.26 |
| `test_library_i27_i32.py` | ~40 | Propositions I.27–I.32 |
| `test_library_i33_i48.py` | ~60 | Propositions I.33–I.48 |
| `test_soundness.py` | ~40 | Axiom soundness checks, invalid proof rejection |
| `test_smt_backend.py` | ~40 | SMT-LIB and TPTP encoding |
| `test_geocoq_compat.py` | ~20 | GeoCoq name mapping |
| `test_performance_benchmarks.py` | ~10 | Forward-chaining timing (≤700ms for 5 points) |

### 18.1 Running Tests

```bash
python -m pytest verifier/tests/ -v              # All verifier tests
python -m pytest verifier/tests/test_e_system.py  # All 48 propositions
PYTHONHASHSEED=0 python -m pytest                 # Deterministic ordering
```

---

## 19. References

1. Avigad, J., Dean, E., & Mumma, J. (2009). *A Formal System for Euclid's
   Elements.* Review of Symbolic Logic, 2(4), 700–768.
   [DOI](https://doi.org/10.1017/S1755020309990098)

2. Beeson, M., Narboux, J., & Wiedijk, F. (2019). *Proof-checking Euclid.*
   Annals of Mathematics and Artificial Intelligence.
   [DOI](https://doi.org/10.1007/s10472-018-9606-x)

3. Gupta, H. N. (1965). *Contributions to the Axiomatic Foundations of
   Geometry.* PhD thesis, University of California, Berkeley.

4. GeoCoq. *A formalization of geometry in Coq based on Tarski's axiom system.*
   [https://geocoq.github.io/GeoCoq/](https://geocoq.github.io/GeoCoq/)
