# Implementation Plan Audit — GeoCoq Alignment & Legacy Removal

**Date**: 2025-XX-XX  
**Audited against**: GeoCoq (https://geocoq.github.io/GeoCoq/), IMPLEMENTATION_PLAN.md, current codebase  
**Request**: Ensure the plan (a) copies GeoCoq's approach properly, (b) completely replaces the old formal system with E/H/T, (c) systems are used automatically like GeoCoq.

---

## Executive Summary

The plan has **7 critical gaps** and **5 moderate issues**. The biggest problem: **Phase 9 adds E/H/T as optional extras alongside the old system, but the user wants the old system fully replaced.** GeoCoq doesn't offer a "classic vs modern" toggle — it uses Tarski as the foundation and translates transparently. The plan needs a new **Phase 6.5: Legacy Deprecation** and a rewritten **Phase 9** that removes the old checker entirely.

---

## CRITICAL GAPS

### C1. No Legacy Removal Phase
**Problem**: The plan never removes the old verifier (`verifier/ast.py`, `checker.py`, `parser.py`, `rules.py`, `library.py`, `propositions.py`, `matcher.py`, `scope.py`). Phase 9.1 keeps "Classic" as an option.  
**GeoCoq approach**: GeoCoq has ONE axiom system (Tarski) as the computational foundation, with Hilbert and Euclid as theorem-level overlays translated through Tarski. There is no "classic mode."  
**Required fix**: Add **Phase 6.5 — Legacy System Deprecation**:
1. Create `verifier/unified_checker.py` — single entry point using System E as default, with T bridge for completeness and H bridge for Hilbert-style display.
2. Rewrite `euclid_py/ui/proof_panel.py` to use `e_checker` + `e_bridge` instead of `checker.py` + `rules.py`.
3. Rewrite `euclid_py/ui/rule_reference.py` to source rules from `e_axioms.py` / `h_axioms.py` / `t_axioms.py`.
4. Migrate `verifier/propositions.py` → `e_library.py` (already 26/48 done).
5. Migrate `answer-keys.json` proof format → System E proof format.
6. Move old files to `verifier/_legacy/` (don't delete — keep for reference).
7. Update all `euclid_py/` imports.

### C2. Phase 9.1 System Selector Is Wrong
**Problem**: Plan adds a dropdown: Classic / System E / System H / System T. This means 4 parallel verification paths.  
**GeoCoq approach**: GeoCoq uses Tarski internally and presents Euclid-style theorems at the surface level. The user never picks "which system" — the system translates automatically.  
**Required fix**: Remove the system selector dropdown. Instead:
- System E is the **default proof language** (what users write in).
- System T is used **internally** for completeness checking (invisible).
- System H is available as an **alternative display mode** (not a separate checker).
- The UI shows "System E" proof entry but can toggle to show the same theorem in H/T notation (read-only translation view).

### C3. `answer-keys.json` Uses Old Predicate Language
**Problem**: The 48 answer keys use the legacy predicate syntax (`Segment(A,B)`, `Circle(A,B)`, `Equal(AB,CD)`, `Congruent(A,B,C,D,E,F)`) which maps to the old `verifier/ast.py` + `checker.py`. None of these map to E/H/T.  
**GeoCoq approach**: GeoCoq's proofs use a uniform Coq syntax based on Tarski predicates (`Cong`, `BetS`, `Col`, etc.) with Euclidean theorems stated in those terms.  
**Required fix**: Add a migration step to convert answer keys to System E sequent format:
- `Segment(A,B)` → `a ≠ b` (distinct points)
- `Circle(A,B)` → construction step: `let α be circle(a, b)` → `center(a, α) ∧ on(b, α)`
- `Equal(AB, CD)` → `ab = cd` (segment equality in E)
- `Congruent(A,B,C,D,E,F)` → SAS/SSS/ASA sequent from `e_library`
- `Between(A,B,C)` → `between(a, b, c)`
- `OnCircle(P, C)` → `on(p, α)`
- Each answer key becomes an `EProof` object in `e_proofs.py`

### C4. Legacy JS Frontend Not Addressed
**Problem**: The `legacy JS/` directory contains the original React/Vite web app (`euclid-merged.jsx`, `FitchProofPanel.jsx`, `src/proof/*.js`). The README still describes this as the primary app (`npm run dev`). The plan only addresses the PyQt6 `euclid_py/` UI.  
**Required fix**: Either:
- **Option A**: Port the React frontend to use E/H/T (new `src/proof/` modules calling Python backend via WebSocket/REST).
- **Option B**: Declare the React app legacy and make the PyQt6 app primary. Update README accordingly.
- **Option C**: Build a new web frontend that mirrors the PyQt6 verifier UI.

The plan currently ignores this entirely. Phase 9 only modifies `euclid_py/`.

### C5. `euclid_py/engine/rules.py` Duplicates Old Verifier
**Problem**: `euclid_py/engine/rules.py` contains a separate rule system that duplicates `verifier/rules.py`:
```
euclid_py/engine/rules.py      — rules for the PyQt6 proof panel  
verifier/rules.py               — rules for the old Fitch checker
verifier/e_axioms.py            — System E axioms (the new system)
```
**GeoCoq approach**: One axiom system, one rule set.  
**Required fix**: `euclid_py/engine/rules.py` should be replaced by a thin wrapper around `e_axioms.py` that formats E axioms for display in the UI.

### C6. Proof Entry Syntax Not Migrated
**Problem**: Plan Phase 9.3 says "adapt the Fitch proof panel to accept System E proof syntax" but doesn't address that:
- The current parser (`verifier/parser.py`) handles the old AST syntax.
- The current `euclid_py/ui/proof_panel.py` sends text to `verifier/parser.py` → `verifier/checker.py`.
- System E proofs use `e_parser.py` which has a completely different grammar.
**Required fix**: 
1. Replace `verifier/parser.py` usage in `proof_panel.py` with `e_parser.py`.
2. Update the predicate palette in the UI to show E predicates: `on(a,L)`, `between(a,b,c)`, `ab = cd`, `∠abc = ∠def`.
3. Update sentence evaluation to use `e_checker.py`.

### C7. Missing GeoCoq-Style Automatic Translation
**Problem**: GeoCoq's key innovation is that proofs written in Euclid's style are **automatically verified** through Tarski's axiom system — the user doesn't think about Tarski at all. The plan treats translation as a manual/diagnostic feature (Phase 9.4 cross-system view).  
**Required fix**: The verification pipeline should be:
```
User writes proof in E-style syntax
    → e_parser → EProof
    → e_checker validates (uses e_consequence + e_construction + e_metric)
    → If e_checker needs completeness help → automatic π → T → consequence → ρ → E
    → Result shown to user as ✓/✗ with E-language diagnostics
```
The T and H translations happen invisibly. The cross-system view (Phase 9.4) is nice-to-have, not the core pathway.

---

## MODERATE ISSUES

### M1. Phase 7 (Coq Export) Is Nice-to-Have, Not Core
**Problem**: GeoCoq exports to Coq because it IS Coq. Our project is Python — Coq export is a bonus, not a requirement for "copying GeoCoq properly."  
**Recommendation**: Move Phase 7 to Phase 11 (post-validation). Focus on having E/H/T work correctly first.

### M2. Phase 8 (SMT Backend) Before UI Integration
**Problem**: The plan puts SMT solvers (Phase 8) before UI integration (Phase 9). SMT is an optimization; UI integration is essential.  
**Recommendation**: Swap: do Phase 9 (UI with E/H/T) before Phase 8 (SMT fallback).

### M3. `euclid_py/engine/proposition_data.py` vs `e_library.py`
**Problem**: Proposition metadata lives in two places:
- `euclid_py/engine/proposition_data.py` — display metadata (title, statement, given, canvas objects)
- `verifier/e_library.py` — formal sequents (E theorems)
These are not linked. The UI reads from `proposition_data.py`, the new verifier from `e_library.py`.  
**Required fix**: `proposition_data.py` should reference `e_library.py` for formal content, keeping only display-specific metadata (canvas layout, colors).

### M4. README Describes Legacy Architecture
**Problem**: The README documents the React app structure (`src/`, `euclid-merged.jsx`) and legacy predicate language (`Point(A)`, `Segment(A,B)`), not the E/H/T systems.  
**Required fix**: Phase 9 or the legacy deprecation phase must update README to describe:
- The Python verifier as the primary engine
- System E proof syntax as the proof language
- The E↔T↔H bridge architecture
- PyQt6 (or updated web) as the primary UI

### M5. Phase 6.3–6.4 (Props I.27–I.48) Blocked by Missing Infrastructure
**Problem**: Props I.35–I.48 require area theory. The E AST has `AreaTerm` but no area axioms are encoded in `e_axioms.py`. The plan acknowledges "Requires area transfer axioms" for I.35–I.41 but doesn't specify when/how these are added.  
**Required fix**: Add a sub-phase 6.3.1 that adds area axioms (DA5–DA6 from Paper §3.4) to `e_axioms.py` before encoding I.35+.

---

## CORRECT ELEMENTS (No Changes Needed)

| Aspect | Status | Notes |
|--------|--------|-------|
| E↔T↔H bridge architecture | ✅ Correct | Matches GeoCoq's `tarski_to_euclid.v` / `euclid_to_tarski.v` / `tarski_to_hilbert.v` |
| Tarski as the bridge system | ✅ Correct | GeoCoq uses Tarski as the foundational system for all translations |
| Forward-chaining consequence engine | ✅ Correct | Matches Paper §3.8, polynomial-time decidability |
| Completeness pipeline (Phase 5) | ✅ Correct | Correctly implements Theorem 5.1 via π/ρ/cut-elimination |
| Axiom encoding as GRS clauses | ✅ Correct | All three systems use geometric rule schemes |
| GeoCoq name mapping (Phase 7.2) | ✅ Correct | Useful for Coq interop |
| Cross-system verification (Phase 10) | ✅ Correct | E→T→E, E→H→E roundtrip regression tests |

---

## REVISED EXECUTION ORDER

```
1.  Phase 6.3–6.4  (Props I.27–I.48 + area axioms) — complete the library
2.  Phase 6.5*     (Legacy Deprecation) — replace old checker with E/H/T   [NEW]
3.  Phase 9*       (UI Integration) — connect E/H/T to UI, remove old system
4.  Phase 8        (SMT Backend) — automated reasoning fallback
5.  Phase 10       (Cross-System Verification) — full validation
6.  Phase 7        (Coq Export) — interoperability (optional)
```

*Phases 6.5 and 9 are the critical missing pieces.

---

## PROPOSED PHASE 6.5: Legacy System Deprecation

### 6.5.1 — Create Unified Checker (`verifier/unified_checker.py`)
Single entry point that routes to `e_checker` (default), with automatic `t_bridge` fallback for completeness.

### 6.5.2 — Migrate Answer Keys  
Convert `answer-keys.json` from old predicate format to `EProof` objects in `e_proofs.py`.

### 6.5.3 — Migrate Proposition Data
Link `euclid_py/engine/proposition_data.py` to `e_library.py` for formal content.

### 6.5.4 — Rewrite UI Imports
Replace all `from verifier.checker import ProofChecker` with `from verifier.e_checker import EChecker` in `euclid_py/`.

### 6.5.5 — Move Legacy Files
Move `verifier/ast.py`, `checker.py`, `parser.py`, `rules.py`, `library.py`, `propositions.py`, `matcher.py`, `scope.py`, `diagnostics.py` to `verifier/_legacy/`.

### 6.5.6 — Update README
Rewrite project structure, predicate language, and getting-started sections.

---

## PROPOSED PHASE 9 REVISION: UI Integration (Replaces Old Plan)

### 9.1 — System E as Default Proof Engine
- `proof_panel.py` calls `e_checker` directly (no system selector dropdown).
- Predicate palette shows E syntax: `on(a,L)`, `between(a,b,c)`, `ab = cd`, `∠abc < ∠def`.
- Construction steps: `let α be circle(a, b)`, `let L be line(a, b)`.

### 9.2 — Automatic T Bridge (Invisible)
- When `e_checker` cannot fully verify a step, automatically invoke `t_completeness.is_valid_for_ruler_compass()`.
- Show diagnostics from whichever engine produced the result.
- User never sees "System T" — it's an internal fallback.

### 9.3 — H/T Translation View (Read-Only Tab)
- Optional tab showing the same theorem in all three systems.
- NOT a separate verification mode — just a display of the automatic translations.

### 9.4 — Rule Reference Panel Update
- Source rules from `e_axioms.py` grouped by: Construction (§3.3), Diagrammatic (§3.4), Metric (§3.5), Transfer (§3.6), Superposition (§3.7).
- Show Hilbert equivalents inline (from `h_axioms.py` via `h_bridge.py`).

### 9.5 — Remove Dual-Check Mode
- No dual checking — E is the only checker. T is the internal bridge. H is a display format.
