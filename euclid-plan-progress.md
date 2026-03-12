# Euclid Plan — Progress Tracker

> **Goal**: Prove all 13 books of Euclid's Elements using formal System E.
> **Source**: `Euclid Plan.docx`

---

## Phase 1: Remove Systems T (Tarski) and H (Hilbert)

Make System E the sole formal system. Remove T and H from the UI, verifier, and all dependencies. Retain any code integral to the E verifier (reworked if needed).

| # | Task | Status | Notes |
|---|------|--------|-------|
| 1.1 | Remove T/H predicate palette buttons from proof panel | ⬜ Not Started | `euclid_py/ui/proof_panel.py` — System T and System H collapsible sections in glossary |
| 1.2 | Remove E/T/H system switcher buttons from proof panel | ⬜ Not Started | `euclid_py/ui/proof_panel.py` — Row 2 buttons "E", "T", "H" |
| 1.3 | Remove `switch_system` / `_switch_system_inner` methods | ⬜ Not Started | `euclid_py/ui/proof_panel.py` — bridge-based notation rewriting |
| 1.4 | Remove Glossary tab and E/T/H Translation tab from main window | ⬜ Not Started | `euclid_py/ui/main_window.py` — both Verifier and Workspace screens |
| 1.5 | Refactor `translation_view.py` — remove T/H content, keep E glossary | ⬜ Not Started | `euclid_py/ui/translation_view.py` — GlossaryPanel and TranslationView |
| 1.6 | Remove T/H cross-system engines from `unified_checker.py` | ⬜ Not Started | Lines 319-347: T/H engine init, bridge imports, helper functions |
| 1.7 | Remove T-bridge fallback from `verify_proof` and `verify_named_proof` | ⬜ Not Started | `use_t_fallback` parameter, `_try_t_fallback` function |
| 1.8 | Delete System T verifier modules | ⬜ Not Started | `t_ast.py`, `t_axioms.py`, `t_bridge.py`, `t_checker.py`, `t_completeness.py`, `t_consequence.py`, `t_cut_elimination.py`, `t_pi_translation.py`, `t_rho_translation.py` |
| 1.9 | Delete System H verifier modules | ⬜ Not Started | `h_ast.py`, `h_axioms.py`, `h_bridge.py`, `h_checker.py`, `h_consequence.py`, `h_library.py` |
| 1.10 | Delete T/H test files | ⬜ Not Started | `test_t_system.py`, `test_h_system.py`, `test_cross_system.py` |
| 1.11 | Update `README.md` — System E-only architecture | ⬜ Not Started | Remove three-system table, update architecture diagram |
| 1.12 | Update `change-log.md` | ⬜ Not Started | Document all removals |
| 1.13 | Run full test suite — verify no breakage | ⬜ Not Started | `pytest verifier/tests/ euclid_py/tests/ -v` |

---

## Phase 2: Polish the Verifier

Build a small set of fundamental propositions to test all verifier features. Include negative testing and edge cases (false rule application, improper citations, etc.). Remove any remaining T/H references discovered.

| # | Task | Status | Notes |
|---|------|--------|-------|
| 2.1 | Audit verifier for remaining T/H imports or dead code | ⬜ Not Started | Grep for `t_bridge`, `h_bridge`, `Tarski`, `Hilbert`, etc. |
| 2.2 | Build core proposition test set (I.1–I.5, I.8) | ⬜ Not Started | These exercise construction, metric, transfer, superposition |
| 2.3 | Add negative tests — false rule application | ⬜ Not Started | Wrong axiom names, mismatched prerequisites, improper subproofs |
| 2.4 | Add negative tests — improper citation usage | ⬜ Not Started | Self-citation, forward references, wrong refs |
| 2.5 | Add edge case tests | ⬜ Not Started | Empty proofs, malformed JSON, duplicate lines |
| 2.6 | Fix any verifier bugs discovered | ⬜ Not Started | As encountered |

---

## Phase 3: Proof Writing Tools

Develop proof generator capable of producing formal proofs for Book I, designed for extensibility to all 13 books.

| # | Task | Status | Notes |
|---|------|--------|-------|
| 3.1 | Design proof generator architecture | ⬜ Not Started | Must be extensible for Books II–XIII |
| 3.2 | Implement generator for Book I propositions | ⬜ Not Started | Algorithmically produce verifier-compatible proofs |
| 3.3 | Generate all 48 Book I proofs | ⬜ Not Started | |
| 3.4 | Verify all generated proofs pass the verifier | ⬜ Not Started | |

---

## Phase 4: UI Integration Verification

Run generated proofs through the verifier UI to check for inconsistencies.

| # | Task | Status | Notes |
|---|------|--------|-------|
| 4.1 | Load generated proofs into UI | ⬜ Not Started | |
| 4.2 | Verify UI displays correct results | ⬜ Not Started | |
| 4.3 | Fix any UI / verification integration issues | ⬜ Not Started | |

---

## Phase 5: Manual Review

Manual check of all Book I proofs.

| # | Task | Status | Notes |
|---|------|--------|-------|
| 5.1 | Manual review of all 48 Book I proofs | ⬜ Not Started | Owner will verify |

---

## Legend

| Symbol | Meaning |
|--------|---------|
| ⬜ | Not Started |
| 🔄 | In Progress |
| ✅ | Complete |
| ❌ | Blocked / Failed |
| ⏭️ | Skipped |
