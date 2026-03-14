# Euclid Plan — Progress Tracker

Euclid Plan

To prove all 13 books of Euclid’s elements first the verification engine must be polished and run perfectly. This can be verified by passing through all the proofs from book 1 to start with and then each subsequent book. Instead of writing each of the proofs by hand it is easier to instead write a proof writing tool that will be used to write all of the proofs algorithmically, which will also ensure that they are written strictly correctly and in accordance with the formal system E. 

The implementation of system H and T becomes excessive and extra since it does not add any substance to the proof writing. Making E the primary system and removing Hilbert’s system and Tarski’s system will give the software a more straightforward approach. Since this is foundational this step should be done very first since it will help with polishing the verifier. 

To summarize:
Remove systems T and H from the UI (glossary tab, and buttons in the proof journal), remove the feature set from the verifier and from any other dependencies. Any code which is integral to the verifier should stay or be reworked if possible.
Polish the verifier – chicken and egg problem – need written proofs to make verifier work correctly but need verifier to work correctly to make proofs. This can be solved by making a small set of fundamental propositions that test for all the features that are needed to fully polish the verifier. Negative testing and edge case testing should also be implemented to check for false rule application, improper citation usage, or other strange occurrences. If there is any code which references systems T or H which are not integral to the app, revert to step 1.
Once verifier is running very smoothly proof writing tools should be developed to be capable of generating formal proof based off the verifier for the first book of the elements. The generator should be constructed with the notion in mind that the other 12 books will be added to the software, and adding new features axioms and propositions from those books should be simple. If the verifier does not run smoothly or runs into glaring issues revert to step 2.
The proofs should be verified by putting them into the verifier UI method to make sure there are no inconsistencies with the UI and verification / proof integration. If this step fails step 3 should be reworked to generate proof that pass correctly, or the UI integration should be reworked.
I will manually check all proofs in book 1 and see if I encounter any issues that you may have missed.


---

## Phase 1: Remove Systems T (Tarski) and H (Hilbert)

Make System E the sole formal system. Remove T and H from the UI, verifier, and all dependencies. Retain any code integral to the E verifier (reworked if needed).

| # | Task | Status | Notes |
|---|------|--------|-------|
| 1.1 | Remove T/H predicate palette buttons from proof panel | ✅ Complete | Removed in v8.0.0 — System T and System H collapsible glossary sections deleted |
| 1.2 | Remove E/T/H system switcher buttons from proof panel | ✅ Complete | Removed in v8.0.0 — Row 2 "E", "T", "H" buttons deleted |
| 1.3 | Remove `switch_system` / `_switch_system_inner` methods | ✅ Complete | Removed in v8.0.0 — bridge-based notation rewriting deleted; `_SYS_NAMES` dict cleaned to E-only |
| 1.4 | Remove Glossary tab and E/T/H Translation tab from main window | ✅ Complete | Removed in v8.0.0 — both Verifier and Workspace screens |
| 1.5 | Refactor `translation_view.py` — remove T/H content, keep E glossary | ✅ Complete | Entire file deleted in v8.0.0 — `TranslationView` and `GlossaryPanel` removed |
| 1.6 | Remove T/H cross-system engines from `unified_checker.py` | ✅ Complete | All T/H engine init, bridge imports, helper functions, `use_t_fallback` param, `_try_t_fallback` call, and Tarski docstrings removed |
| 1.7 | Remove T-bridge fallback from `verify_proof` and `verify_named_proof` | ✅ Complete | `use_t_fallback` parameter, `_try_t_fallback` call site, and all Tarski docstring references removed from `verify_proof` |
| 1.8 | Delete System T verifier modules | ✅ Complete | All 9 `.py` files deleted — only stale `.pyc` caches remain in `__pycache__/` |
| 1.9 | Delete System H verifier modules | ✅ Complete | All 6 `.py` files deleted — only stale `.pyc` caches remain in `__pycache__/` |
| 1.10 | Delete T/H test files | ✅ Complete | `test_t_system.py`, `test_h_system.py`, `test_cross_system.py` all deleted |
| 1.11 | Update `README.md` — System E-only architecture | ✅ Complete | Top-level `README.md` and `verifier/README.md` both updated to System E-only architecture |
| 1.12 | Update `change-log.md` | ✅ Complete | v8.0.0 section documents all removals |
| 1.13 | Run full test suite — verify no breakage | ✅ Complete | 831 passed, 144 skipped, 4 xfailed, 8 pre-existing failures (I.3, I.6–I.10 proof issues). Zero regressions from Phase 1 cleanup. |

---

## Phase 2: Polish the Verifier

Build a small set of fundamental propositions to test all verifier features. Include negative testing and edge cases (false rule application, improper citations, etc.). Remove any remaining T/H references discovered.

| # | Task | Status | Notes |
|---|------|--------|-------|
| 2.1 | Audit verifier for remaining T/H imports or dead code | ✅ Complete | All T/H references removed: `unified_checker.py` (docstrings, params), `verifier/README.md` (module trees), `proof_panel.py` (`_SYS_NAMES` dict). No T/H imports remain in any `.py` source file. |
| 2.2 | Build core proposition test set (I.1–I.5, I.8) | ✅ Complete | `scripts/real_proofs.py` has hand-written proofs for I.1–I.5, I.8–I.11, I.13, I.15–I.16; `test_all_48_proofs.py` (48 parametrised tests); `test_soundness.py` L6 integration tests |
| 2.3 | Add negative tests — false rule application | ✅ Complete | `test_soundness.py` L2 (engine isolation, wrong axiom names, mismatched prereqs), L5 adversarial (polarity inversion, unknown rules); `test_autofill.py` (38 tests including wrong-refs failure) |
| 2.4 | Add negative tests — improper citation usage | ✅ Complete | `test_soundness.py` L3 (circular theorem dependency), L4 (self-availability check for all 48); answer key negative tests (self-citation, canvas-as-justification) |
| 2.5 | Add edge case tests | ✅ Complete | `test_soundness.py` L5 (empty proofs, malformed JSON, duplicate line IDs, zero IDs, very long statements, unparseable goals) |
| 2.6 | Fix any verifier bugs discovered | ✅ Complete | SSS/SAS dispatch fix (distinct enum values), Indirect justification completely removed, plus extensive v7.9.2–v8.0.0 fixes: sort inference, M1 forward direction, CN5/CN2/monotonicity, `is_less` stale rep bug, var_map hypothesis matching, ZeroMag sort, construction prereq validation, theorem var substitution, duplicate literal consumption |

---

## Phase 3: Proof Writing Tools

Develop proof generator capable of producing formal proofs for Book I, designed for extensibility to all 13 books.

### 3A — Foundational Infrastructure

| # | Task | Status | Notes |
|---|------|--------|-------|
| 3.1 | Design proof generator architecture | ✅ Complete | `scripts/real_proofs.py` with `PB` (Proof Builder) class supporting `g()` (Given), `s()` (step), `assume()`, `reductio()`, `cases()`, depth-based scoping; `scripts/generate_answer_key.py` for text output |
| 3.2 | Implement generator for Book I propositions | 🔄 In Progress | All 48 propositions have Given steps in `real_proofs.py`; 7 pass verification (I.1–I.6, I.8); 6 fail (I.7, I.9–I.11, I.13, I.15–I.16); 35 are incomplete stubs. |

### 3B — Transfer Oracle / Discovery Tool

Add a helper that, given a set of known facts, runs the full diagrammatic closure + transfer pipeline and reports ALL derivable facts grouped by type. Eliminates the "guess the exact structural form" problem that blocks proof writing.

| # | Task | Status | Notes |
|---|------|--------|-------|
| 3.3 | Implement `discover()` function in transfer engine | ✅ Complete | `verifier/e_discovery.py`: `discover_all()` runs closure + transfer + metric, returns `DiscoveryReport` with facts grouped by: on_facts, same_side, between, circle_facts, diag_equalities, diag_negations, angle_sums, segment_sums, area_decomps, nonzero, angle/segment/area_equalities, inequalities, metric_derived. |
| 3.4 | Add `PB.discover()` integration | ✅ Complete | `PB.discover()` snapshots current known set from premises + lines, infers variable sorts, calls `discover_all()`, and prints grouped report. Interactive proof development aid. |

### 3C — Metric Term Normalization (M8 Symmetries)

The metric engine should automatically treat `△abc = △bac = △cab` etc. as equivalent. Currently proof writers must use the exact structural form the engine produces, causing mysterious failures.

| # | Task | Status | Notes |
|---|------|--------|-------|
| 3.5 | Normalize AngleTerm ordering (M4 symmetry: ∠abc = ∠cba) | ✅ Complete | `AngleTerm._canonical()` sorts ray endpoints (vertex fixed). `frozen=True, eq=False` with custom `__eq__`/`__hash__`. |
| 3.6 | Normalize AreaTerm ordering (M8 symmetry: 6 permutations) | ✅ Complete | `AreaTerm._canonical()` sorts all 3 vertices. All 6 permutations structurally equal. |
| 3.7 | Normalize SegmentTerm ordering (M3 symmetry: ab = ba) | ✅ Complete | `SegmentTerm._canonical()` sorts endpoints. `ab` and `ba` are structurally equal. MagAdd commutativity deferred — metric engine handles it. |

### 3D — Auto-Chaining (Transfer ↔ Metric fallback)

When a Transfer step fails, try running the metric engine on transfer-derived facts. When a Metric step fails, try running transfer first to produce intermediate facts. Eliminates many manual intermediate steps.

| # | Task | Status | Notes |
|---|------|--------|-------|
| 3.8 | Transfer step fallback: run metric engine on derived facts | ✅ Complete | Transfer handler in `unified_checker.py` falls back to metric engine on combined transfer-derived + known facts. Lazy evaluation avoids perf regression. |
| 3.9 | Metric step fallback: run transfer engine first | ✅ Complete | Metric handler in `unified_checker.py` falls back to closure → transfer → metric pipeline when basic check fails. Fresh MetricEngine instance avoids state pollution. |
| 3.10 | Diagrammatic step auto-closure | ✅ Complete | Already handled by existing ConsequenceEngine — "Diagrammatic" justification runs full closure on known set. No additional work needed. |

### 3E — Proof Sketch Mode

Instead of writing every line, write only key construction/theorem steps. The system fills in Given lines, derivable diagrammatic facts, metric symmetry/transitivity chains, and available transfer conclusions.

| # | Task | Status | Notes |
|---|------|--------|-------|
| 3.11 | Auto-generate Given lines from premises in PB | ✅ Complete | `PB.auto_given()` generates Given lines for all premises, returns `Dict[str, int]` mapping premise → line id. `PB.build(sketch=True)` auto-prepends missing Given lines. |
| 3.12 | Auto-fill derivable intermediate steps | ✅ Complete | `PB._build_sketch()` runs diagrammatic closure at each step and inserts Diagrammatic lines for missing facts. Renumbers all lines and remaps refs. Tested with I.1 and I.4 in sketch mode. |

### 3F — Backward-Chaining Proof Search

Goal-directed search from conclusion to premises. Depth-limited search over construction rules, theorem applications, transfer axioms, and metric inferences.

| # | Task | Status | Notes |
|---|------|--------|-------|
| 3.13 | Implement backward-chaining prototype | ✅ Complete | `verifier/e_backward.py`: `backward_search()` with depth-limited recursive search. Checks: diagrammatic closure, transfer, metric, transfer→metric chain, SAS/SSS superposition, theorem application with sub-goal recursion. `SearchResult` with `ProofHint` suggestions. |
| 3.14 | Integrate search with PB proof builder | ✅ Complete | `PB.search(goal_str=None)` runs backward search from current proof state. Auto-detects available theorems via `get_theorems_up_to()`. Tested on I.4 (SAS), I.5 (theorem+metric), I.8 (SSS). |

### 3G — Proof Completion

| # | Task | Status | Notes |
|---|------|--------|-------|
| 3.15 | Complete all 48 Book I proofs | ⬜ | Using tools from 3B–3F to generate correct proofs. `answer_key_book_1.json` and `answer-key-book-I.txt` synced. |
| 3.16 | Verify all generated proofs pass the verifier | 🔄 In Progress | 7 of 48 pass verification (I.1–I.6, I.8). Test suite: 801 passed, 0 failed, 42 xfailed. |

---

## Phase 4: UI Integration Verification

Run generated proofs through the verifier UI to check for inconsistencies.

| # | Task | Status | Notes |
|---|------|--------|-------|
| 4.1 | Load generated proofs into UI | 🔄 In Progress | 2 solved proof files exist (`solved_proofs/Proposition I.1.euclid`, `solved_proofs/Proposition 1.2 Canvas.euclid` - only canvas); remaining 46 not yet loaded as `.euclid` files |
| 4.2 | Verify UI displays correct results | 🔄 In Progress | `test_soundness.py` L6 runs Proposition I.1 `.euclid` file through verifier end-to-end; bulk UI verification not yet done |
| 4.3 | Fix any UI / verification integration issues | 🔄 In Progress | Multiple UI fixes applied (QThread crash, autofill, background verification, two-click editing); further issues may surface with remaining propositions |

---

## Phase 5: Manual Review

Manual check of all Book I proofs.

| # | Task | Status | Notes |
|---|------|--------|-------|
| 5.1 | Manual review of all 48 Book I proofs | ⬜ Not Started | Owner will verify — blocked on 4 unverified proofs (I.11, I.13, I.15, I.16) |

---

## Legend

| Symbol | Meaning |
|--------|---------|
| ⬜ | Not Started |
| 🔄 | In Progress |
| ✅ | Complete |
| ❌ | Blocked / Failed |
| ⏭️ | Skipped |
