# Euclid Project — Comprehensive Implementation Plan (Phases 4–10)

## Current State Summary

### Completed Phases
| Phase | Version | Description | Files | Tests |
|-------|---------|-------------|-------|-------|
| **Phase 1** | 4.8.x | Core verifier: Fitch-style checker, parser, AST, rules, UI (PyQt6), 48 propositions | `verifier/{ast,parser,checker,rules,library}.py`, `euclid_py/` | ~144 |
| **Phase 2** | 5.0.0 | System E (Avigad, Dean, Mumma 2009): e_ast, e_axioms (Sections 3.4–3.6), e_consequence (Section 3.8), e_construction (Section 3.3), e_metric (Section 3.5), e_transfer (Section 3.6), e_superposition (Section 3.7), e_checker, e_bridge, e_library (I.1–I.10), e_proofs (I.1) | `verifier/e_*.py` | ~260 |
| **Phase 3** | 5.1.0 | System H (Hilbert's axioms): h_ast, h_axioms (Groups I–IV, 39 clauses), h_consequence, h_checker, h_bridge (E↔H), h_library (I.1–I.5) | `verifier/h_*.py` | ~298 |

### Architecture
```
┌─────────────────────────────────────────────────────────────┐
│                    euclid_py (PyQt6 UI)                     │
│  main_window → proof_panel → proof_view → diagnostics_panel │
│  canvas_widget → rule_reference                             │
├─────────────────┬──────────────────┬────────────────────────┤
│   Old Verifier  │    System E      │     System H           │
│  ast/checker/   │  e_ast/e_axioms/ │  h_ast/h_axioms/       │
│  parser/rules/  │  e_consequence/  │  h_consequence/        │
│  library        │  e_construction/ │  h_checker/            │
│                 │  e_metric/       │  h_bridge (E↔H)        │
│                 │  e_transfer/     │  h_library             │
│                 │  e_superposition/│                        │
│                 │  e_checker/      │                        │
│                 │  e_bridge/       │                        │
│                 │  e_library/      │                        │
│                 │  e_proofs        │                        │
├─────────────────┴──────────────────┴────────────────────────┤
│              ❌ MISSING: Tarski Bridge (T)                   │
│              System E ↔ Tarski (T) ↔ System H               │
└─────────────────────────────────────────────────────────────┘
```

### Reference Materials
- **Paper**: Avigad, Dean, Mumma (2009), "A Formal System for Euclid's Elements" — `formal_system_extracted.txt`
- **GeoCoq**: https://geocoq.github.io/GeoCoq/ — Coq formalization of geometry foundations
  - `euclidean_axioms.v` → System E axioms
  - `hilbert_axioms.v` → System H axioms
  - `tarski_axioms.v` → Tarski's axioms (the bridge)
  - `tarski_to_euclid.v` / `euclid_to_tarski.v` → T↔E translations
  - `tarski_to_hilbert.v` / `hilbert_to_tarski.v` → T↔H translations
  - `Elements/OriginalProofs/` → Coq proofs of Book I
  - `Elements/Statements/Book_1.html` → Formal statements

---

## Phase 4: Tarski System (T) — The Missing Bridge Link
**Version**: 5.2.0  
**Reference**: Paper Section 5.2, GeoCoq `tarski_axioms.v`

The paper's completeness proof (Section 5, Theorem 5.1) goes through Tarski's system as the intermediate representation: E ↔ T ↔ H. Tarski's system uses **only points** with two primitives (betweenness B and equidistance ≡), making it the simplest formal bridge.

### 4.1 — AST (`verifier/t_ast.py` — new)

| Component | Description | Reference |
|-----------|-------------|-----------|
| **Sort** | `TSort.POINT` — single sort | Tarski uses only points |
| **Primitives** | `B(a,b,c)` — nonstrict betweenness; `Cong(a,b,c,d)` — equidistance | Paper Section 5.2; GeoCoq `tarski_axioms.v` |
| **Negations** | `NotB(a,b,c)`, `NotCong(a,b,c,d)`, `Neq(a,b)` — explicit negation predicates | Paper Section 5.2: "expand language L(T) by adding predicates ≠ and B̄ and ≢" |
| **TLiteral** | Polarity-tagged atoms | Same pattern as `ELiteral`, `HLiteral` |
| **TClause** | Disjunctive clause | Same pattern as `Clause`, `HClause` |
| **TSequent** | Γ ⇒ ∃x̄. Δ | Same form as `Sequent`, `HSequent` |
| **TTheorem, TProof, TProofStep** | Proof infrastructure | Same pattern as E/H |
| **Utilities** | `t_atom_vars`, `t_literal_vars`, `t_substitute_atom`, `t_substitute_literal` | Same pattern |

### 4.2 — Axioms as Geometric Rule Schemes (`verifier/t_axioms.py` — new)

Encode all 11 Tarski axioms (paper Section 5.2) as clauses suitable for the contrapositive forward-chaining engine. Include the negativity axioms that make the system geometric.

| Axiom | Name | Clause Form | Paper Ref |
|-------|------|-------------|-----------|
| E1 | Equidistance symmetry | `Cong(a,b,b,a)` always | §5.2 |
| E2 | Equidistance transitivity | `¬Cong(a,b,p,q) ∨ ¬Cong(a,b,r,s) ∨ Cong(p,q,r,s)` | §5.2 |
| E3 | Identity of equidistance | `¬Cong(a,b,c,c) ∨ Eq(a,b)` | §5.2 |
| B | Betweenness axiom | `¬B(a,b,d) ∨ ¬B(b,c,d) ∨ B(a,b,c)` | §5.2 |
| SC | Segment construction | `∃x. B(q,a,x) ∧ Cong(a,x,b,c)` | §5.2 |
| 5S | Five-segment | `Eq(a,b) ∨ ¬B(a,b,c) ∨ ¬B(p,q,r) ∨ ¬Cong(a,b,p,q) ∨ ¬Cong(b,c,q,r) ∨ ¬Cong(a,d,p,s) ∨ ¬Cong(b,d,q,s) ∨ Cong(c,d,r,s)` | §5.2 |
| P | Pasch | `¬B(a,p,c) ∨ ¬B(q,c,b) ∨ ∃x. B(a,x,q) ∧ B(b,p,x)` | §5.2 |
| 2L | Lower 2D | `∃a,b,c. NotB(a,b,c) ∧ NotB(b,c,a) ∧ NotB(c,a,b)` | §5.2 |
| 2U | Upper 2D | Disjunctive: 3-way case split on betweenness | §5.2 |
| PP | Parallel postulate | `¬B(a,d,t) ∨ ¬B(b,d,c) ∨ Eq(a,d) ∨ ∃x,y. B(a,b,x) ∧ B(a,c,y) ∧ B(y,t,x)` | §5.2 |
| Int | Intersection | `¬Cong(a,x,a,x') ∨ ¬Cong(a,z,a,z') ∨ ¬B(a,x,z) ∨ ¬B(x,y,z) ∨ ∃y'. Cong(a,y,a,y') ∧ B(x',y',z')` | §5.2 |
| **Negativity** | 6 clauses for Eq/Neq, B/NotB, Cong/NotCong | `(Eq ∨ Neq)`, `(Eq ∧ Neq → ⊥)`, etc. | §5.2 |

**Total**: ~17 axiom clauses + 6 negativity = ~23 clauses in `ALL_T_AXIOMS`.

### 4.3 — Consequence Engine (`verifier/t_consequence.py` — new)

Same forward-chaining closure as `e_consequence.py` and `h_consequence.py`, adapted for Tarski's single-sorted language. Only needs POINT pool for grounding.

### 4.4 — Proof Checker (`verifier/t_checker.py` — new)

Validates Tarski-style proofs step by step. Construction steps use SC, P, PP, Int, 2L axioms. Deduction steps use E1–E3, B, 5S, 2U, negativity.

### 4.5 — E↔T Translation (`verifier/t_bridge.py` — new)

Implement the translation functions π (E→T) and ρ (T→E) from Paper Section 5.3–5.4.

| E Literal | T Translation (π) | Paper Ref |
|-----------|-------------------|-----------|
| `on(p, N)` | `∃a,b. Neq(a,b) ∧ ζ(c₁ᴺ,c₂ᴺ,p,a,b)` where ζ encodes perpendicular bisector membership | §5.3 |
| `¬on(p, N)` | `B̄(c₁ᴺ,c₂ᴺ,p) ∧ B̄(c₁ᴺ,p,c₂ᴺ) ∧ B̄(p,c₁ᴺ,c₂ᴺ)` | §5.3 |
| `between(p,q,r)` | `B(p,q,r) ∧ Neq(p,q) ∧ Neq(q,r) ∧ Neq(p,r)` | §5.3 |
| `on(p,γ)` | `Cong(c₁ᵧ,p,c₁ᵧ,c₂ᵧ)` | §5.3 |
| `inside(p,γ)` | `∃x. B(c₁ᵧ,p,x) ∧ Neq(p,x) ∧ Cong(c₁ᵧ,x,c₁ᵧ,c₂ᵧ)` | §5.3 |
| `same-side(p,q,N)` | Complex: ∃r,s,t,a,b with ζ and χ formulas | §5.3 |
| Segment `ab = cd` | Lay segments side-by-side: `∃a₀...aₖ,b₀...bₘ. B-chain ∧ Cong-chain ∧ Eq(a₀,b₀) ∧ Eq(aₖ,bₘ)` | §5.3 |
| Angle `∠xyz = ∠x'y'z'` | `∃u,v,u',v'. ξ(...) ∧ Cong(u,v,u',v')` | §5.3 |

The ρ (T→E) translation (Section 5.4):
| T Atom | E Translation (ρ) |
|--------|-------------------|
| `B(p,q,r)` | `∃L,a,b. on-chain ∧ between-placement` (nonstrict→strict conversion) |
| `B̄(p,q,r)` | `¬between(p,q,r) ∧ Neq(p,q) ∧ Neq(q,r)` |
| `Cong(x,y,v,u)` | `xy = vu` |
| `NotCong(x,y,v,u)` | `xy ≠ vu` |

### 4.6 — H↔T Translation (extend `verifier/h_bridge.py`)

Add `h_to_t` and `t_to_h` functions completing the full triangle: E↔T↔H.

### 4.7 — Tests (`verifier/tests/test_t_system.py` — new)

| Test Class | Count | Coverage |
|------------|-------|----------|
| `TestTSorts` | 1 | Sort existence |
| `TestTAtoms` | 6 | All atom repr |
| `TestTLiterals` | 6 | Polarity, negation, repr |
| `TestTAtomVars` | 4 | Variable extraction |
| `TestTSubstitution` | 3 | Atom/literal substitution |
| `TestTAxiomCounts` | 3 | Per-group and total counts |
| `TestTConsequence` | 8 | Forward-chaining: E1/E2/E3/B symmetry, transitivity, segment construction |
| `TestTBridgeET` | 8 | E→T, T→E translations, roundtrip |
| `TestTBridgeHT` | 6 | H→T, T→H translations |
| `TestTChecker` | 4 | Checker creation, empty proof, basic step |
| **Total** | ~49 | |

---

## Phase 5: Completeness Infrastructure — Section 5 Translation Pipeline
**Version**: 5.3.0  
**Reference**: Paper Section 5, Theorem 5.1

This phase implements the actual completeness proof pipeline: given a valid sequent, translate it through E→T→(cut-free proof)→T→E. This is the mathematical core proving that System E captures exactly ruler-and-compass geometry.

### 5.1 — Cut Elimination (`verifier/t_cut_elimination.py` — new)

Implement Negri's Theorem 5.3 for geometric rule schemes. Given a proof with cuts in T, produce a cut-free proof.

| Component | Description | Reference |
|-----------|-------------|-----------|
| `is_geometric_sequent(seq)` | Check if a sequent has geometric form | §5.2, Definition (⋆) |
| `is_regular_sequent(seq)` | Check if geometric with single disjunct | §5.2 |
| `cut_eliminate(proof)` | Remove cuts preserving validity | Theorem 5.3 (Negri 2003) |

### 5.2 — π Translation Engine (`verifier/t_pi_translation.py` — new)

Full implementation of the E→T translation map π from Section 5.3, building on the literal-level translations in `t_bridge.py`.

| Function | Description | Reference |
|----------|-------------|-----------|
| `pi_literal(lit)` | Translate one E literal to positive-primitive T formula | §5.3 all cases |
| `pi_sequent(seq)` | Translate a full E sequent to regular T sequent | §5.3, definition of π |
| `pi_preserves_semantics(seq)` | (Test helper) Check that π preserves ruler-and-compass validity | Lemma 5.5 |

### 5.3 — ρ Translation Engine (`verifier/t_rho_translation.py` — new)

Full implementation of the T→E retranslation ρ from Section 5.4.

| Function | Description | Reference |
|----------|-------------|-----------|
| `rho_atom(atom)` | Translate one T atom to E literal set | §5.4 |
| `rho_sequent(seq)` | Translate full T sequent back to E | §5.4 |
| **Key lemmas** | `e_proves_rho_pi(seq)` — Lemma 5.8 | §5.4 |

### 5.4 — Completeness Checker (`verifier/t_completeness.py` — new)

Orchestrates the full pipeline: given an E sequent, check if it's valid by translating to T, finding a cut-free proof, and translating back.

```
E sequent → π → T sequent → cut-free proof in T → ρ → E proof
```

| Function | Description | Reference |
|----------|-------------|-----------|
| `is_valid_for_ruler_compass(seq)` | Full completeness check | Theorem 5.1 |
| `find_e_proof(seq)` | If valid, construct an E proof | Proof of Theorem 5.1 |

### 5.5 — Tests (`verifier/tests/test_completeness.py` — new)

| Test | Description |
|------|-------------|
| `test_pi_on_literal` | π translates each E literal type correctly |
| `test_pi_roundtrip_semantics` | Lemma 5.5: π preserves validity |
| `test_rho_on_atom` | ρ translates each T atom correctly |
| `test_rho_pi_identity` | Lemma 5.7/5.8: E proves ρ(π(Γ⇒Δ)) implies E proves Γ⇒Δ |
| `test_completeness_prop_i1` | Full pipeline for Prop I.1 |
| `test_completeness_prop_i4` | Full pipeline for SAS |
| `test_incompleteness_trisection` | Angle trisection correctly fails |
| **Total** | ~12 |

---

## Phase 6: Extended Proposition Library — Book I, Props I.11–I.48
**Version**: 5.4.0–5.6.0 (incremental)  
**Reference**: Paper Section 4, GeoCoq `Elements/OriginalProofs/`

Extend both the System E and System H theorem libraries to cover all 48 propositions. Group by dependency chains.

### 6.1 — Props I.11–I.15 (Perpendiculars and Vertical Angles)

| Prop | Statement | E Sequent | Dependencies |
|------|-----------|-----------|--------------|
| I.11 | Draw perpendicular from point on line | `on(a,L), on(b,L), a≠b ⇒ ∃c. ∠bac = right-angle` | I.1, I.3 |
| I.12 | Drop perpendicular from point off line | `¬on(p,L) ⇒ ∃M. perp(M,L)` | I.8, I.10 |
| I.13 | Adjacent angles on a line sum to 2 right angles | `between(a,c,b), ¬on(d,L) ⇒ ∠acd + ∠dcb = 2·right-angle` | I.11 |
| I.14 | Converse of I.13 — angles summing to 2 right angles form a line | | I.13 |
| I.15 | Vertical angles are equal | `intersects(L,M) ⇒ ∠aeb = ∠ced` | I.13 |

**Files**: Add to `e_library.py`, `h_library.py`, `e_proofs.py`

### 6.2 — Props I.16–I.26 (Triangle Inequalities, Parallels, ASA/AAS)

| Prop | Statement | Key Feature |
|------|-----------|-------------|
| I.16 | Exterior angle > either remote interior | First use of extension construction |
| I.17 | Two angles of a triangle sum < 2 right angles | Corollary of I.16 |
| I.18 | Greater side opposite greater angle | |
| I.19 | Greater angle opposite greater side | Converse of I.18 |
| I.20 | Triangle inequality | |
| I.21 | Inner triangle sides shorter but angles larger | |
| I.22 | Construct triangle from three segments | Triangle inequality prerequisite |
| I.23 | Copy an angle | I.8, I.22 |
| I.24 | SAS inequality (hinge theorem) | |
| I.25 | Converse hinge theorem | |
| I.26 | ASA and AAS congruence | |

### 6.3 — Props I.27–I.32 (Parallel Lines)

| Prop | Statement | Key Feature |
|------|-----------|-------------|
| I.27 | Alternate interior angles → parallel | First parallel proposition |
| I.28 | Corresponding angles → parallel | |
| I.29 | Parallel → alternate interior angles equal | **First use of Postulate 5** (parallel postulate) |
| I.30 | Transitivity of parallelism | |
| I.31 | Construct parallel through a point | |
| I.32 | Exterior angle = sum of remote interior; angle sum = 2 right angles | Culmination of angle theory |

### 6.4 — Props I.33–I.48 (Parallelograms, Area, Pythagorean Theorem)

| Prop | Statement | Key Feature |
|------|-----------|-------------|
| I.33–I.34 | Parallelogram properties | |
| I.35–I.41 | Area theory: equal parallelograms, triangle area | Requires area transfer axioms |
| I.42–I.45 | Constructing parallelograms with given area | Paper §4.3: parallel postulate needed |
| I.46 | Construct a square | |
| I.47 | **Pythagorean theorem** | Area decomposition |
| I.48 | Converse of Pythagorean theorem | |

**⚠️ Area axioms prerequisite**: Props I.35+ require area axioms (DA5–DA6 from Paper §3.4) to be added to `e_axioms.py` before encoding. These are not yet implemented. Add as sub-phase 6.3.1.

### 6.5A — Proof Encodings (`verifier/e_proofs.py` — extend)

For each proposition, encode the System E proof following the paper's Section 4.2 style. Each proof is a sequence of `ProofStep` objects matching the paper's presentation.

### 6.6 — Tests

Each batch of propositions gets integration tests verifying:
- Sequent structure (correct hypotheses/conclusions)
- Proof step count and kinds
- Full verification via `e_checker`
- Cross-verification via `h_checker` (for translatable propositions)

---

## Phase 7: GeoCoq-Aligned Proof Export
**Version**: 5.7.0  
**Reference**: GeoCoq `Elements/OriginalProofs/`, `euclidean_axioms.v`

### 7.1 — Coq Term Generator (`verifier/coq_export.py` — new)

| Function | Description |
|----------|-------------|
| `e_proof_to_coq(proof)` | Convert an `EProof` to a Coq proof script using GeoCoq's `euclidean_axioms.v` API |
| `t_proof_to_coq(proof)` | Convert a `TProof` to Coq using `tarski_axioms.v` |
| `h_proof_to_coq(proof)` | Convert an `HProof` to Coq using `hilbert_axioms.v` |

### 7.2 — GeoCoq Compatibility Layer (`verifier/geocoq_compat.py` — new)

Map our axiom/theorem names to GeoCoq's Coq identifiers:

| Our Name | GeoCoq Coq Name |
|----------|-----------------|
| `On(a, L)` | `IncidL a l` |
| `Between(a,b,c)` | `BetS A B C` |
| `Cong(a,b,c,d)` | `Cong A B C D` |
| `Prop.I.1` | `proposition_1` |
| SAS superposition | `axiom_5_line` |

### 7.3 — Tests

- Export Prop I.1 to Coq, check syntax validity
- Round-trip: export then parse back
- Verify GeoCoq name mappings cover all axioms

---

## Phase 8: Automated Reasoning Backend (Section 6) ✅
**Version**: 7.1.0  
**Reference**: Paper Section 6, SMT/SAT solvers

### 8.1 — SMT-LIB Encoding (`verifier/smt_backend.py`) ✅

Encode System E axioms and proof obligations in SMT-LIB 2.6 format for Z3/CVC5.

| Component | Description | Reference |
|-----------|-------------|-----------|
| `encode_axioms_smtlib()` | All diagrammatic + metric + transfer axioms | §6 |
| `encode_obligation(known, query)` | Given known facts, check if query follows | §6 |
| `check_with_z3(obligation)` | Call Z3 via subprocess or z3-solver package | §6 |

### 8.2 — TPTP Encoding (`verifier/tptp_backend.py`) ✅

Encode in TPTP format for first-order provers (E-prover, SPASS).

| Component | Description | Reference |
|-----------|-------------|-----------|
| `encode_axioms_tptp()` | All axioms in TPTP FOF format | §6: "entered our betweenness, same-side, and Pasch axioms in TPTP format" |
| `encode_query_tptp(known, query)` | Conjecture encoding | §6 |

### 8.3 — Proof Checker Backend Integration ✅

Replace or augment the polynomial-time forward-chaining engine with an SMT fallback for complex diagrams.

| Function | Description |
|----------|-------------|
| `try_consequence_then_smt(known, query)` | Try forward-chaining first; if inconclusive, query SMT solver |
| `incremental_smt_session()` | Push/pop SMT state for suppositional reasoning (§6: "push the state ... temporarily assert the local hypothesis") |

### 8.4 — Tests ✅

- Encode the paper's test diagram (5 lines, 6 points) in SMT-LIB and TPTP
- Verify all diagrammatic consequences instantaneously (§6 claim)
- Benchmark forward-chaining vs. SMT on Props I.1–I.10

---

## Phase 6.5: Legacy System Deprecation — Replace Old Checker with E/H/T
**Version**: 5.7.0  
**Reference**: AUDIT.md (Critical gaps C1–C7)

The old verifier (`verifier/ast.py`, `checker.py`, `parser.py`, `rules.py`, `library.py`, `propositions.py`, `matcher.py`, `scope.py`) must be completely replaced by Systems E/H/T. GeoCoq does not offer "classic vs modern" — it uses Tarski as the computational foundation with Euclid/Hilbert as theorem-level overlays. Our project must do the same.

### 6.5.1 — Unified Checker (`verifier/unified_checker.py` — new)

Single entry point that routes all verification through System E, with automatic T bridge fallback for completeness.

| Function | Description |
|----------|-------------|
| `verify_proof(proof_json)` | Parse proof from JSON → EProof → e_checker. If inconclusive, invoke t_completeness. |
| `verify_step(known, query)` | Single-step verification via e_consequence + automatic T fallback. |
| `get_available_rules()` | Return all E axioms + H axioms formatted for UI display. |

### 6.5.2 — Migrate Answer Keys (`answer-keys-e.json` — new)

Convert all 48 answer keys from old predicate format to System E proof format:
- `Segment(A,B)` → `a ≠ b` (distinct points)
- `Circle(A,B)` → construction: `center(a, α) ∧ on(b, α)`
- `Equal(AB, CD)` → `ab = cd`
- `Congruent(A,B,C,D,E,F)` → SAS/SSS sequent from `e_library`
- `Between(A,B,C)` → `between(a, b, c)`
- `OnCircle(P, C)` → `on(p, α)`
- Each answer key → `EProof` in `e_proofs.py`

### 6.5.3 — Link Proposition Data to E Library

Make `euclid_py/engine/proposition_data.py` reference `e_library.py` for formal content (sequents, theorems). Keep display metadata (canvas layout, colors) in `proposition_data.py`.

### 6.5.4 — Rewrite UI Imports

Replace all old verifier imports in `euclid_py/`:
- `from verifier.checker import ProofChecker` → `from verifier.unified_checker import verify_proof`
- `from verifier.rules import ALL_RULES` → `from verifier.e_axioms import ALL_E_AXIOMS`
- `from verifier.parser import parse_formula` → `from verifier.e_parser import parse_e_formula`
- `from verifier.library import ...` → removed (E axioms are the library)

### 6.5.5 — Move Legacy Files to `verifier/_legacy/`

| File | Disposition |
|------|-------------|
| `verifier/ast.py` | → `verifier/_legacy/ast.py` |
| `verifier/checker.py` | → `verifier/_legacy/checker.py` |
| `verifier/parser.py` | → `verifier/_legacy/parser.py` (keep `e_parser.py` as primary) |
| `verifier/rules.py` | → `verifier/_legacy/rules.py` |
| `verifier/library.py` | → `verifier/_legacy/library.py` |
| `verifier/propositions.py` | → `verifier/_legacy/propositions.py` |
| `verifier/matcher.py` | → `verifier/_legacy/matcher.py` |
| `verifier/scope.py` | → `verifier/_legacy/scope.py` |
| `verifier/diagnostics.py` | → keep (shared by both old and new) |
| `euclid_py/engine/rules.py` | → removed (replaced by e_axioms.py wrapper) |

### 6.5.6 — Update Legacy JS Frontend

Either:
- **Option A**: Port `legacy JS/src/proof/` to call System E Python backend via API.
- **Option B**: Declare `legacy JS/` fully deprecated, make `euclid_py/` the primary app.
- **Option C**: Build new web frontend mirroring `euclid_py/` UI.

### 6.5.7 — Update README

Rewrite to reflect:
- System E as the proof language (not `Point(A)`, `Segment(A,B)` predicates)
- Python verifier as the primary engine
- E↔T↔H bridge architecture
- PyQt6 as the primary UI (or web if Option A/C chosen)

### 6.5.8 — Tests

| Test | Description |
|------|-------------|
| `test_unified_checker_accepts_e_proof` | EProof verified through unified checker |
| `test_unified_checker_rejects_invalid` | Invalid sequent rejected |
| `test_old_imports_removed` | No remaining `from verifier.checker` in `euclid_py/` |
| `test_proposition_data_links_e_library` | All 48 propositions linked to E library |
| `test_answer_keys_migration` | All 48 answer keys parse as EProof |
| **Total** | ~10 |

---

## Phase 9: UI Integration — System E as Default Engine (REVISED)
**Version**: 6.1.0  
**Reference**: `euclid_py/ui/proof_panel.py`, `proof_view.py`, AUDIT.md

GeoCoq uses Tarski internally and presents Euclid-style theorems at the surface. The user never picks "which system." We follow the same approach: System E is the default and only proof language, T is the invisible bridge, H is an optional display format.

### 9.1 — System E as Default Proof Engine

`proof_panel.py` calls `e_checker` directly (no system selector dropdown):
- Predicate palette shows E syntax: `on(a,L)`, `between(a,b,c)`, `ab = cd`, `∠abc < ∠def`
- Construction steps: `let α be circle(a, b)`, `let L be line(a, b)`
- Justification rules sourced from `e_axioms.py`
- No "Classic" mode — old checker is gone

### 9.2 — Automatic T Bridge (Invisible to User)

When `e_checker` cannot fully verify a step:
1. Automatically invoke `t_completeness.is_valid_for_ruler_compass()`
2. If T bridge succeeds, show ✓ with E-language diagnostics
3. If both fail, show ✗ with E-language error messages
4. User never sees "System T" — it's an internal fallback

### 9.3 — H/T Translation View (Read-Only Tab)

Optional tab showing the same theorem in all three notations:
```
System E: a≠b ⇒ ∃c. ab=ac ∧ ab=bc
System T: Neq(a,b) ⇒ ∃c. Cong(a,b,a,c) ∧ Cong(a,b,b,c)  
System H: a≠b, IncidL(a,L) ⇒ ∃c. CongH(a,b,a,c)
```
This is a **display** feature, not a separate verification path.

### 9.4 — Rule Reference Panel Update

Source rules from `e_axioms.py` grouped by paper sections:
- Construction axioms (§3.3): line, circle, intersection
- Diagrammatic axioms (§3.4): ordering, betweenness, same-side, Pasch
- Metric axioms (§3.5): segment/angle/area congruence, addition
- Transfer axioms (§3.6): betweenness→segment, angle→ordering
- Superposition (§3.7): SAS

Show Hilbert equivalents inline via `h_bridge.py`.

### 9.5 — Tests

- Smoke tests: open each proposition, verify via E checker
- UI interaction tests: add/remove steps, verify construction syntax
- Integration: verify Prop I.1 proof via UI using System E
- Negative: invalid proof rejected with E-language diagnostics

---

## Phase 10: Cross-System Verification & Validation
**Version**: 7.0.0  
**Reference**: Paper Section 5 (soundness/completeness), GeoCoq equivalence proofs

### 10.1 — Cross-Verification Suite (`verifier/tests/test_cross_system.py`) ✅

For each proposition I.1–I.48:
1. ✅ Verify the E proof in the E checker (8 encoded proofs)
2. ✅ Translate the E sequent to T via π, verify the translated sequent
3. ✅ Translate the E sequent to H via the bridge, verify in H
4. ✅ Check that all three systems agree on invalid assertion rejection

### 10.2 — Equivalence Regression Tests ✅

| Test | Description | Status |
|------|-------------|--------|
| `test_e_to_t_to_e_roundtrip` | For all 48 theorems, E→T→E completes without error | ✅ |
| `test_e_to_h_to_e_roundtrip` | For all 48 theorems, E→H→E completes without error | ✅ |
| `test_h_to_t_literal_translation` | H→T literal roundtrip for translatable literals | ✅ |
| `test_invalid_sequent_rejected_all_systems` | Invalid assertion rejected by E, T, and H | ✅ |

### 10.3 — GeoCoq Statement Comparison ✅

Compare our formal statements with GeoCoq's `Elements/Statements/Book_1.html` to verify alignment:
- ✅ Map all 48 proposition names (our → GeoCoq Coq identifiers)
- ✅ Map all E/T/H predicates to GeoCoq equivalents
- ✅ Map 11 Tarski axioms to GeoCoq names
- ✅ Validate E library: 0 alignment issues
- ✅ Validate T translation: 0 issues (Tarski-only primitives)
- ✅ 42 comparison tests passing

### 10.4 — Performance Benchmarks ✅

| Benchmark | Metric | Budget | Status |
|-----------|--------|--------|--------|
| Forward-chaining closure time for diagrams with N points | Time vs N | <500ms for 5 points | ✅ |
| Full proof verification time for each proposition | Time per prop | <1s each | ✅ |
| SMT/TPTP encoding latency | ms per encoding | <50ms axioms, <20ms obligations | ✅ |
| E→T π translation latency | ms per prop | <100ms all 48 | ✅ |
| Cross-system roundtrip latency | ms total | <500ms all 48 | ✅ |
| SMT fallback frequency | structural | Forward-chaining resolves basic cases | ✅ |

---

## Dependency Graph

```
Phase 4 (Tarski T) ✅
    ├── Phase 5 (Completeness) ✅ — requires T bridge
    ├── Phase 8 (SMT Backend) — uses T encoding for benchmarks
    └── Phase 10 (Cross-System) — requires all three systems
Phase 6 (Extended Library)
    ├── Phase 6.1–6.2 ✅ (Props I.1–I.26)
    ├── Phase 6.3–6.4 ✅ (Props I.27–I.48 + area axioms)
    └── Phase 6.5 ✅ (Legacy Deprecation) — old checker replaced
        └── Phase 9* (UI) — System E as sole engine
            └── Phase 10 (Cross-System) — full validation
Phase 8 (SMT Backend) — optimization, after UI works
Phase 7 (Coq Export) — optional interoperability
```

### Recommended Execution Order (REVISED per AUDIT.md)
1. ~~**Phase 4** (Tarski) — unlocks the bridge~~ ✅ DONE
2. ~~**Phase 6.1–6.2** (Props I.11–I.26) — expand library~~ ✅ DONE
3. ~~**Phase 5** (Completeness) — mathematical core~~ ✅ DONE
4. ~~**Phase 6.3–6.4** (Props I.27–I.48 + area axioms) — complete library~~ ✅ DONE
5. ~~**Phase 6.5** (Legacy Deprecation) — replace old checker with E/H/T~~ ✅ DONE
6. **Phase 9** (UI Integration) — System E as sole engine, T invisible ~~⚠️ REVISED~~ ✅ DONE
7. ~~**Phase 8** (SMT) — automated reasoning fallback~~ ✅ DONE
8. **Phase 10** (Cross-System) — final validation ✅ DONE (10.1–10.4 all complete)
9. **Phase 7** (Coq Export) — interoperability (optional)

---

## File Summary

### New Files (Phases 4–10)

| File | Phase | Purpose | Status |
|------|-------|---------|--------|
| `verifier/t_ast.py` | 4.1 | Tarski AST (single-sorted, B + ≡) | ✅ |
| `verifier/t_axioms.py` | 4.2 | 11 Tarski axioms as GRS clauses | ✅ |
| `verifier/t_consequence.py` | 4.3 | Forward-chaining for T | ✅ |
| `verifier/t_checker.py` | 4.4 | Tarski proof checker | ✅ |
| `verifier/t_bridge.py` | 4.5 | E↔T translations (π, ρ) | ✅ |
| `verifier/tests/test_t_system.py` | 4.7 | Tarski system tests | ✅ |
| `verifier/t_cut_elimination.py` | 5.1 | Cut elimination for GRS | ✅ |
| `verifier/t_pi_translation.py` | 5.2 | Full π: E→T | ✅ |
| `verifier/t_rho_translation.py` | 5.3 | Full ρ: T→E | ✅ |
| `verifier/t_completeness.py` | 5.4 | Completeness pipeline | ✅ |
| `verifier/tests/test_completeness.py` | 5.5 | Completeness tests | ✅ |
| `verifier/unified_checker.py` | 6.5.1 | Single entry point: E default + T fallback | ✅ |
| `answer-keys-e.json` | 6.5.2 | Migrated answer keys in E proof format | ✅ |
| `verifier/coq_export.py` | 7.1 | Coq proof script generator | |
| `verifier/geocoq_compat.py` | 7.2/10.3 | GeoCoq name mapping + statement comparison | ✅ |
| `verifier/smt_backend.py` | 8.1 | SMT-LIB encoding | ✅ |
| `verifier/tptp_backend.py` | 8.2 | TPTP encoding | ✅ |
| `verifier/tests/test_cross_system.py` | 10.1 | Cross-system verification | ✅ |
| `verifier/tests/test_smt_backend.py` | 8.4 | SMT/TPTP backend tests | ✅ |
| `verifier/tests/test_geocoq_compat.py` | 10.3 | GeoCoq comparison tests | ✅ |
| `verifier/tests/test_performance_benchmarks.py` | 10.4 | Performance benchmark tests | ✅ |

### Modified Files (Phases 4–10)

| File | Phase | Change |
|------|-------|--------|
| `verifier/e_library.py` | 6 | Add Props I.11–I.48 (48/48 done) |
| `verifier/h_library.py` | 6 | Add Props I.11–I.48 (H system, 48/48 done) |
| `verifier/e_proofs.py` | 6 | Add proof encodings for I.2–I.48 (8/48 done) |
| `verifier/e_axioms.py` | 6.3 | Add area axioms (DA5–DA6) for Props I.35+ |
| `verifier/h_bridge.py` | 4.6 | Add H↔T translation |
| `euclid_py/ui/proof_panel.py` | 6.5/9 | Replace old checker with `e_checker`, E syntax palette | 6.5 ✅ |
| `euclid_py/ui/main_window.py` | 6.5/9 | Remove old `ProofChecker` import, use `unified_checker` | 6.5 ✅ |
| `euclid_py/ui/rule_reference.py` | 9 | Source from `e_axioms.py`, grouped by paper sections | 6.5 ✅ |
| `euclid_py/engine/proposition_data.py` | 6.5 | Link to `e_library.py` for formal content | ✅ |
| `README.md` | 6.5 | Rewrite for E/H/T architecture | ✅ |
| `change-log.md` | all | Changelog entries per phase |

### Deprecated Files (Phase 6.5 → `verifier/_legacy/`)

| File | Replacement |
|------|-------------|
| `verifier/ast.py` | `verifier/e_ast.py` |
| `verifier/checker.py` | `verifier/e_checker.py` + `verifier/unified_checker.py` |
| `verifier/parser.py` | `verifier/e_parser.py` |
| `verifier/rules.py` | `verifier/e_axioms.py` |
| `verifier/library.py` | `verifier/e_library.py` |
| `verifier/propositions.py` | `verifier/e_library.py` + `verifier/e_proofs.py` |
| `verifier/matcher.py` | `verifier/e_consequence.py` |
| `verifier/scope.py` | `verifier/e_checker.py` (scope built into checker) |
| `euclid_py/engine/rules.py` | Thin wrapper around `e_axioms.py` |
