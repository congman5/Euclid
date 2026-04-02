# Euclid Implementation Plan

> Master roadmap for completing all 48 propositions of Euclid's Elements Book I,
> plus the Tarski axiomatic foundation.  This plan is backed by verified source
> code from **LeanEuclid** (Lean 4) and **GeoCoq** (Coq).
> Generated from instructions.txt file with links at the end of that document and this one

---

## Architecture Overview

```
Layer 0  Tarski Axioms (T1-T11)          -- Track A
Layer 1  System E Axioms (~52 rules)     -- already in e_axioms.py
Layer 2  Euclid Book I (I.1-I.48)        -- Track B
```

**Track A** derives System E axioms from Tarski, proving soundness.
**Track B** fills out the 33 remaining proposition proofs (I.16-I.48).

The two tracks are independen.

---

## Reference Repositories

| Repo | Language | Role | Path Pattern |
|------|----------|------|-------------|
| LeanEuclid | Lean 4 | System E proofs for all 48 props | `Book/Prop01.lean` - `Book/Prop48.lean` |
| GeoCoq | Coq | Tarski foundation (Ch02-Ch13) + Book I | `Tarski_dev/Ch02_cong.v` - `Ch13_3.v`, `Elements/` |
| IsaGeoCoq | Isabelle | Declarative Isar port of GeoCoq | AFP browser |

---

## LeanEuclid Translation Rules

| LeanEuclid Construct | Our System Equivalent | Notes |
|-----------------------|----------------------|-------|
| `euclid_apply proposition_N` | `StepKind.THEOREM_APP` with `theorem_name="Prop.I.N"` | Must supply `var_map` |
| `euclid_apply construction_rule` | `StepKind.CONSTRUCTION` | `new_vars` for created objects |
| `euclid_assert <metric>` | `StepKind.METRIC` assertion | Segment/angle equalities |
| `euclid_finish` | `e_consequence.py` closure | Our engine checks all rules; no SMT |
| `by_contra h` | Fitch subproof (depth + 1) | Assume negation, derive contradiction |
| `by_cases` | Case split | Two subproofs joined |
| `have` / `obtain` | Intermediate assertions | Map to ProofStep assertions |

---

## Axiom Correspondence: LeanEuclid vs Our System

### Diagrammatic Inference (TI, CA, IA)

| LeanEuclid (Diagrammatic.lean) | Our e_axioms.py | Status |
|---------------------------------|-----------------|--------|
| `transfer_inferences` (TI1-TI7) | `_TI_*` rules | MATCH |
| `circle_axiom` (CA1-CA3) | `_CA_*` rules | MATCH |
| `intersection_axiom` (IA1-IA6) | `_IA_*` rules | MATCH |
| `intersection_lines_common_point` | -- | EXTENSION (not in Avigad) |
| `parallel_line_unique` | -- | EXTENSION |
| `parallelogram_same_side` | -- | EXTENSION |

### Metric Inference (M1-M9)

| LeanEuclid (Metric.lean) | Our e_axioms.py | Status |
|---------------------------|-----------------|--------|
| M1: `segment_addition` | `_M1_*` | MATCH |
| M2: `angle_addition` | `_M2_*` | MATCH |
| M3: `area_addition` | `_M3_*` | MATCH |
| M4: `segment_symmetric` | `_M4_*` | MATCH |
| M5: `angle_symmetric` | `_M5_*` | MATCH |
| M6: `zero_segment` | `_M6_*` | MATCH |
| M7: `zero_angle` | `_M7_*` | MATCH |
| M8: `zero_area` | `_M8_*` | MATCH |
| M9: `degenerate_area` | `_M9_*` | MATCH |

### Transfer Inference (DA5-DA7, DAr1-DAr2)

| LeanEuclid (Transfer.lean) | Our e_axioms.py | Status |
|-----------------------------|-----------------|--------|
| DA5: `lines_intersect` | `_DA5_lines_intersect` (line 532) | MATCH |
| DA6: `supplementary_angles` | `_DA6_*` | MATCH |
| DA7: `perpendicular_angles` | `_DA7_*` | MATCH |
| DAr1: `area_congruence` | `_DAr1_*` | MATCH |
| DAr2: `triangle_area` | `_DAr2_*` | MATCH |
| `parallelogram_area` | -- | EXTENSION (I.35-I.47) |
| `sum_parallelograms_area` | -- | EXTENSION (I.47) |
| `rectangle_area` | -- | EXTENSION (I.47) |

### Superposition (SAS + SSS)

| LeanEuclid (Superposition.lean) | Our e_axioms.py | Status |
|----------------------------------|-----------------|--------|
| `superposition` (combined SAS+SSS) | `_SAS_*` + `_SSS_*` (split) | MATCH (split into two) |

### Construction (G-axioms)

| LeanEuclid (Points.lean) | Our e_axioms.py | Status |
|---------------------------|-----------------|--------|
| G1-G8 construction rules | `_G*_*` construction rules | MATCH |
| `point_between_points_shorter_than` | -- | EXTENSION |
| `extend_point_longer` | -- | EXTENSION |

---

## Non-Standard LeanEuclid Extensions

These 7 axioms are used by LeanEuclid but are NOT in Avigad et al. (2009).
They must be either **derived as lemmas** from standard System E or
**added as justified extensions** before implementing the propositions that need them.

| Extension Axiom | First Used In | Strategy |
|----------------|--------------|----------|
| `intersection_lines_common_point` | I.27 (parallel proof) | Derive from IA axioms |
| `parallel_line_unique` | I.30 | Derive from I.27-I.29 |
| `parallelogram_same_side` | I.34 | Derive from TI + Between |
| `point_between_points_shorter_than` | I.20 | Derive from G-axioms |
| `extend_point_longer` | I.20 | Derive from G-axioms |
| `parallelogram_area` | I.35 | Derive from DAr1 + DAr2 |
| `sum_parallelograms_area` | I.47 | Derive from M3 area addition |
| `rectangle_area` | I.47 | Derive from parallelogram_area |

**Strategy:** Before implementing Groups B7-B9, create `e_extension_lemmas.py`
that derives these from standard axioms and registers them as available theorems.

---

## Track B: Proposition Implementation Guide

### Dependency Map (from e_proofs.py _DEPS)

```
I.1 (primitive)
I.2 <- I.1
I.3 <- I.2
I.4 (SAS - axiom)
I.5 <- I.4, I.3
...
I.15 <- I.13
--- UNSOLVED BOUNDARY ---
I.16 <- I.4, I.10, I.15
I.17 <- I.16
...
I.47 <- I.4, I.14, I.41, I.46
I.48 <- I.8, I.47
```

All propositions I.1 through I.15 already have working proofs.
Propositions I.16 through I.48 currently use `_fallback_proof` stubs.

### Group B1: Exterior Angle & Inequalities (I.16-I.21)

#### Proposition I.16 — Exterior Angle Theorem
- **LeanEuclid source**: `Book/Prop16.lean`
- **Dependencies**: I.3, I.4, I.10, I.15
- **LeanEuclid proof structure**: Two parts (16 and 16'), ~15 `euclid_apply` calls total
- **Key steps**:
  - `euclid_apply proposition_10` (bisect BC -> E)
  - `euclid_apply proposition_3` (cut AE to get F)
  - `euclid_apply proposition_4` (SAS: triangle ABE = triangle DCE... wait no)
  - `euclid_apply proposition_15` (vertical angles)
  - Part 2 (16'): uses the alternate exterior angle
- **Estimated ProofStep count**: ~12
- **Translation notes**: The two-part structure means we may want a helper lemma
  or two THEOREM_APP chains

#### Proposition I.17 — Two Angles of Triangle < Two Right Angles
- **LeanEuclid source**: `Book/Prop17.lean`
- **Dependencies**: I.16
- **Estimated ProofStep count**: ~4
- **Translation notes**: Short proof using I.16 + I.13 (supplementary)

#### Proposition I.18 — Greater Side Opposite Greater Angle
- **LeanEuclid source**: `Book/Prop18.lean`
- **Dependencies**: I.5, I.16
- **Estimated ProofStep count**: ~5

#### Proposition I.19 — Greater Angle Opposite Greater Side
- **LeanEuclid source**: `Book/Prop19.lean`
- **Dependencies**: I.5, I.18
- **Estimated ProofStep count**: ~5
- **Translation notes**: Proof by contradiction (by_contra)

#### Proposition I.20 — Triangle Inequality
- **LeanEuclid source**: `Book/Prop20.lean`
- **Dependencies**: I.5, I.19
- **Estimated ProofStep count**: ~6
- **Translation notes**: Uses `extend_point_longer` extension axiom

#### Proposition I.21 — Triangle Within Triangle
- **LeanEuclid source**: `Book/Prop21.lean`
- **Dependencies**: I.16, I.20
- **Estimated ProofStep count**: ~8

**Group B1 Total: ~40 steps**

### Group B2: Triangle Construction (I.22-I.23)

#### Proposition I.22 — Construct Triangle from Three Segments
- **LeanEuclid source**: `Book/Prop22.lean`
- **Dependencies**: I.1, I.3, I.20
- **Estimated ProofStep count**: ~10
- **Translation notes**: Multiple constructions; uses circle-circle intersection

#### Proposition I.23 — Copy Angle
- **LeanEuclid source**: `Book/Prop23.lean`
- **Dependencies**: I.8, I.22
- **Estimated ProofStep count**: ~8
- **Translation notes**: Construct triangle with SSS then use I.8

**Group B2 Total: ~18 steps**

### Group B3: Angle-Side Congruence (I.24-I.26)

#### Proposition I.24 — SAS Inequality (Open Jaw)
- **LeanEuclid source**: `Book/Prop24.lean`
- **Dependencies**: I.4, I.5, I.19
- **Estimated ProofStep count**: ~10
- **Translation notes**: Has case analysis

#### Proposition I.25 — Converse of I.24
- **LeanEuclid source**: `Book/Prop25.lean`
- **Dependencies**: I.4, I.24
- **Estimated ProofStep count**: ~5
- **Translation notes**: Proof by contradiction

#### Proposition I.26 — ASA and AAS Congruence
- **LeanEuclid source**: `Book/Prop26.lean`
- **Dependencies**: I.4, I.16
- **Estimated ProofStep count**: ~12
- **Translation notes**: Two cases (ASA and AAS), both by contradiction

**Group B3 Total: ~27 steps**

### Group B4: Parallel Lines (I.27-I.31)

#### Proposition I.27 — Alternate Interior Angles Imply Parallel
- **LeanEuclid source**: `Book/Prop27.lean`
- **Dependencies**: I.16
- **LeanEuclid proof pattern**:
  ```
  euclid_apply proposition_16  -- exterior angle
  by_contra                     -- assume lines meet
  euclid_finish                 -- derive contradiction
  ```
- **Estimated ProofStep count**: ~6
- **Translation notes**: Proof by contradiction; needs `by_cases` for
  which side the intersection falls on

#### Proposition I.28 — Exterior Angle + Parallel (Two Forms)
- **LeanEuclid source**: `Book/Prop28.lean`
- **Dependencies**: I.27
- **Estimated ProofStep count**: ~6

#### Proposition I.29 — Parallel Implies Alternate Angles (CONVERSE)
- **LeanEuclid source**: `Book/Prop29.lean`
- **Dependencies**: I.27 (+ implicitly DA5 / parallel postulate)
- **LeanEuclid proof pattern**:
  ```
  euclid_apply proposition_13   -- supplementary angles
  euclid_apply proposition_27   -- if alternate then parallel
  euclid_finish                 -- uses DA5 implicitly
  ```
- **CRITICAL**: This is where the parallel postulate (DA5) enters.
  `euclid_finish` discharges it via SMT. In our system, DA5 must be
  cited explicitly as a TRANSFER step.
- **Variants**: LeanEuclid defines 5 convenience variants:
  - `proposition_29'` through `proposition_29'''''`
  - These are used extensively by I.30-I.48
  - We should implement them as separate library entries
- **Estimated ProofStep count**: ~8 (base) + ~3 each variant

#### Proposition I.30 — Transitivity of Parallelism
- **LeanEuclid source**: `Book/Prop30.lean`
- **Dependencies**: I.27, I.29
- **Estimated ProofStep count**: ~5

#### Proposition I.31 — Construct Parallel Through Point
- **LeanEuclid source**: `Book/Prop31.lean`
- **Dependencies**: I.23, I.27
- **Estimated ProofStep count**: ~5

**Group B4 Total: ~45 steps (including I.29 variants)**

### Group B5: Angle Sum & Parallelograms (I.32-I.34)

#### Proposition I.32 — Angle Sum of Triangle = Two Right Angles
- **LeanEuclid source**: `Book/Prop32.lean`
- **Dependencies**: I.13, I.29, I.31
- **LeanEuclid proof pattern**:
  ```
  euclid_apply proposition_31   -- construct parallel
  euclid_apply proposition_29   -- alternate angles
  euclid_apply proposition_29'  -- variant
  euclid_apply proposition_13   -- supplementary
  euclid_finish
  ```
- **Estimated ProofStep count**: ~6

#### Proposition I.33 — Joining Ends of Equal Parallel Segments
- **LeanEuclid source**: `Book/Prop33.lean`
- **Dependencies**: I.4, I.27, I.29
- **Estimated ProofStep count**: ~6

#### Proposition I.34 — Properties of Parallelograms
- **LeanEuclid source**: `Book/Prop34.lean`
- **Dependencies**: I.4, I.26, I.29
- **LeanEuclid proof pattern**:
  ```
  euclid_apply proposition_29   -- alternate angles (twice)
  euclid_apply proposition_26   -- ASA congruence
  euclid_finish
  ```
- **Variants**: `proposition_34'` (congruent triangles form)
- **Estimated ProofStep count**: ~5
- **Translation notes**: Very clean, only 3 `euclid_apply` + `euclid_finish`.
  Uses `parallelogram_same_side` extension axiom.

**Group B5 Total: ~17 steps**

### Group B6: Area Foundations (I.35-I.38)

**NOTE**: Area propositions introduce the `parallelogram_area` extension axiom.
Must implement extension lemmas before this group.

#### Proposition I.35 — Parallelograms on Same Base, Same Parallels
- **LeanEuclid source**: `Book/Prop35.lean`
- **Dependencies**: I.29, I.34
- **LeanEuclid proof pattern**:
  ```
  -- General case with by_cases on point ordering
  by_cases h : ...
  -- Case 1: simple overlap
  euclid_apply proposition_34  -- parallelogram properties
  euclid_apply proposition_29  -- alternate angles
  euclid_finish
  -- Case 2: complex overlap
  euclid_apply proposition_4   -- SAS
  euclid_finish
  ```
- **Estimated ProofStep count**: ~10 (due to case split)
- **Translation notes**: Has a general case with `by_cases` branching.
  The two cases handle different point orderings.

#### Proposition I.36 — Parallelograms on Equal Bases, Same Parallels
- **LeanEuclid source**: `Book/Prop36.lean`
- **Dependencies**: I.34, I.35
- **Estimated ProofStep count**: ~6

#### Proposition I.37 — Triangles on Same Base, Same Parallels
- **LeanEuclid source**: `Book/Prop37.lean`
- **Dependencies**: I.31, I.35
- **Variants**: `proposition_37'`
- **Estimated ProofStep count**: ~6

#### Proposition I.38 — Triangles on Equal Bases, Same Parallels
- **LeanEuclid source**: `Book/Prop38.lean`
- **Dependencies**: I.31, I.36
- **Estimated ProofStep count**: ~6

**Group B6 Total: ~28 steps**

### Group B7: Area Converses (I.39-I.41)

#### Proposition I.39 — Equal Triangles on Same Base -> Same Parallels
- **LeanEuclid source**: `Book/Prop39.lean`
- **Dependencies**: I.31, I.37
- **Estimated ProofStep count**: ~5
- **Translation notes**: Proof by contradiction

#### Proposition I.40 — Equal Triangles on Equal Bases -> Same Parallels
- **LeanEuclid source**: `Book/Prop40.lean`
- **Dependencies**: I.38, I.39
- **Estimated ProofStep count**: ~5

#### Proposition I.41 — Parallelogram = 2x Triangle (Same Base & Parallels)
- **LeanEuclid source**: `Book/Prop41.lean`
- **Dependencies**: I.34, I.37
- **LeanEuclid proof pattern**:
  ```
  euclid_apply proposition_37'  -- triangles equal
  euclid_apply proposition_34'  -- parallelogram bisected
  euclid_finish                 -- area arithmetic
  ```
- **Estimated ProofStep count**: ~5

**Group B7 Total: ~15 steps**

### Group B8: Applied Constructions (I.42-I.45)

#### Proposition I.42 — Construct Parallelogram = Given Triangle
- **LeanEuclid source**: `Book/Prop42.lean`
- **Dependencies**: I.23, I.31, I.41
- **Estimated ProofStep count**: ~8

#### Proposition I.43 — Complements of Parallelogram Are Equal
- **LeanEuclid source**: `Book/Prop43.lean`
- **Dependencies**: I.34
- **Estimated ProofStep count**: ~6

#### Proposition I.44 — Apply Parallelogram to Line
- **LeanEuclid source**: `Book/Prop44.lean`
- **Dependencies**: I.42, I.43
- **Estimated ProofStep count**: ~10

#### Proposition I.45 — Construct Parallelogram = Given Polygon
- **LeanEuclid source**: `Book/Prop45.lean`
- **Dependencies**: I.42, I.44
- **Estimated ProofStep count**: ~12

**Group B8 Total: ~36 steps**

### Group B9: Pythagorean Theorem (I.46-I.48)

#### Proposition I.46 — Construct Square on Segment
- **LeanEuclid source**: `Book/Prop46.lean`
- **Dependencies**: I.11, I.31, I.34
- **LeanEuclid proof pattern**:
  ```
  euclid_apply proposition_11   -- perpendicular
  euclid_apply proposition_3    -- cut to length
  euclid_apply proposition_31   -- parallel
  euclid_apply proposition_31   -- parallel again
  euclid_apply proposition_34   -- parallelogram check
  euclid_finish
  ```
- **Variants**: `proposition_46'` (alternate form needed by I.47)
- **Estimated ProofStep count**: ~10

#### Proposition I.47 — Pythagorean Theorem
- **LeanEuclid source**: `Book/Prop47.lean`
- **Dependencies**: I.4, I.14, I.41, I.46
- **CRITICAL**: This is the LONGEST proof in Book I.
- **LeanEuclid uses `set_option maxHeartbeats 0`** (infinite solver time)
- **LeanEuclid proof has**:
  - ~30 `euclid_apply` calls
  - 6 "Missed by Euclid" facts (things Euclid assumed but didn't prove)
  - Uses `rectangle_area`, `sum_parallelograms_area`, `parallelogram_area`
    (all non-standard extensions)
- **Key LeanEuclid steps**:
  ```
  euclid_apply proposition_46   -- square on AB
  euclid_apply proposition_46   -- square on BC
  euclid_apply proposition_46   -- square on AC
  euclid_apply proposition_14   -- straight line
  euclid_apply proposition_4    -- SAS (multiple times)
  euclid_apply proposition_41   -- parallelogram = 2x triangle (x2)
  euclid_apply rectangle_area   -- EXTENSION
  euclid_apply sum_parallelograms_area -- EXTENSION
  euclid_finish
  ```
- **Estimated ProofStep count**: ~25
- **Translation notes**: Must implement all 3 area extension axioms first.
  Consider breaking into sub-lemmas for manageability.

#### Proposition I.48 — Converse of Pythagorean Theorem
- **LeanEuclid source**: `Book/Prop48.lean`
- **Dependencies**: I.8, I.47
- **LeanEuclid proof pattern**:
  ```
  euclid_apply proposition_11   -- perpendicular at A
  euclid_apply proposition_3    -- cut to length
  euclid_apply proposition_47   -- apply Pythagorean theorem
  euclid_apply proposition_8    -- SSS congruence
  euclid_finish
  ```
- **Estimated ProofStep count**: ~10

**Group B9 Total: ~45 steps**

---

## Step Count Summary

| Group | Propositions | Estimated Steps | Key Difficulty |
|-------|-------------|----------------|----------------|
| B1 | I.16-I.21 | ~40 | Multi-part proofs, case analysis |
| B2 | I.22-I.23 | ~18 | Circle constructions |
| B3 | I.24-I.26 | ~27 | Contradiction proofs |
| B4 | I.27-I.31 | ~45 | Parallel postulate (DA5), I.29 variants |
| B5 | I.32-I.34 | ~17 | Clean, short proofs |
| B6 | I.35-I.38 | ~28 | Area extension axioms needed |
| B7 | I.39-I.41 | ~15 | Area converses |
| B8 | I.42-I.45 | ~36 | Complex constructions |
| B9 | I.46-I.48 | ~45 | Pythagorean theorem (longest) |
| **TOTAL** | **I.16-I.48** | **~271** | |

Plus ~30 steps for I.29 variants = **~300 total ProofStep objects**.

---

## Proposition Variants Catalog

LeanEuclid defines convenience variants used by later propositions.
These should be registered as separate entries in `e_library.py`.

| Variant | Base | Used By | Description |
|---------|------|---------|-------------|
| `proposition_29'` | I.29 | I.30, I.32, I.33 | Alternate form of angle equality |
| `proposition_29''` | I.29 | I.34, I.35 | Corresponding angles form |
| `proposition_29'''` | I.29 | I.36 | Interior angles supplementary |
| `proposition_29''''` | I.29 | I.44, I.45 | Rearranged hypotheses |
| `proposition_29'''''` | I.29 | I.46 | Further rearrangement |
| `proposition_34'` | I.34 | I.41, I.43 | Diagonal bisects parallelogram |
| `proposition_35'` | I.35 | I.36 | Equal bases form |
| `proposition_37'` | I.37 | I.41 | Area form |
| `proposition_46'` | I.46 | I.47 | Alternate square construction |

---

## Track A: Tarski Foundation

### Overview

Derive System E's ~52 axioms from Tarski's 11 axioms (T1-T11),
using GeoCoq (Ch02-Ch13) and IsaGeoCoq as mathematical oracles.

### Tarski Axioms (T1-T11)

| Axiom | Name | Statement |
|-------|------|-----------|
| T1 | Identity of Betweenness | Bet(A,B,A) -> A=B |
| T2 | Transitivity of Betweenness | Bet(A,B,D) & Bet(B,C,D) -> Bet(A,B,C) |
| T3 | Identity of Congruence | Cong(A,B,C,C) -> A=B |
| T4 | Transitivity of Congruence | Cong(A,B,P,Q) & Cong(A,B,R,S) -> Cong(P,Q,R,S) |
| T5 | Segment Construction | exists E: Bet(A,B,E) & Cong(B,E,C,D) |
| T6 | Five-Segment | (see Avigad 2009) |
| T7 | Pasch's Axiom | (inner form) |
| T8 | Lower Dimension | exists A,B,C: not-collinear |
| T9 | Upper Dimension | (2D constraint) |
| T10 | Euclid's Axiom | (parallel postulate equivalent) |
| T11 | Continuity | Circle-circle / line-circle |

### Milestone M0: Tarski Infrastructure

- **New file**: `verifier/tarski_axioms.py`
  - Define `Bet(A,B,C)` and `Cong(A,B,C,D)` as primitive predicates
  - Encode T1-T11 as axiom schemas
- **New file**: `verifier/tarski_proofs.py`
  - Proof infrastructure for Tarski-level derivations
- **GeoCoq reference**: `Tarski_dev/Ch02_cong.v` (segment congruence basics)
- **LOC estimate**: ~400

### Milestone M3: Betweenness & Segment Theorems (GeoCoq Ch02-Ch05)

- Derive: segment ordering, midpoint existence, Pasch consequences
- **GeoCoq files**: Ch02_cong.v, Ch03_bet.v, Ch04_col.v, Ch05_bet_le.v
- **IsaGeoCoq**: Chap02-05 (declarative Isar proofs, closest to our format)
- **LOC estimate**: ~800

### Milestone M6: Angle & Perpendicular Theorems (GeoCoq Ch06-Ch10)

- Derive: angle congruence, perpendicularity, right angles
- Bridge to System E angle axioms (M5, M7, DA7)
- **GeoCoq files**: Ch06_out_lines.v through Ch10_line_reflexivity.v
- **LOC estimate**: ~1200

### Milestone M7: Parallel & Area (GeoCoq Ch11-Ch13)

- Derive: parallel postulate equivalence, area axioms
- Bridge to System E parallel (DA5) and area (DAr1, DAr2) axioms
- **GeoCoq files**: Ch11_angles.v, Ch12_parallel.v, Ch13_3.v
- **LOC estimate**: ~1000

---

## Track B: Implementation Milestones

### Milestone M1: Foundation Props (I.16-I.26) — Groups B1+B2+B3

**Prerequisites**: All of I.1-I.15 (already done)

**Implementation order** (respecting dependencies):
1. I.16 (exterior angle) <- I.4, I.10, I.15
2. I.17 <- I.16
3. I.18 <- I.5, I.16
4. I.19 <- I.5, I.18
5. I.20 <- I.5, I.19
6. I.21 <- I.16, I.20
7. I.22 <- I.1, I.3, I.20
8. I.23 <- I.8, I.22
9. I.24 <- I.4, I.5, I.19
10. I.25 <- I.4, I.24
11. I.26 <- I.4, I.16

**Estimated total**: ~85 ProofStep objects
**Files to modify**: `verifier/e_proofs.py` (replace 11 `_fallback_proof` stubs)
**Test**: Each proposition should pass `test_verify_all_propositions`

### Milestone M2: Parallel Theory (I.27-I.31) — Group B4

**Prerequisites**: M1 complete, I.29 variants defined

**Implementation order**:
1. I.27 <- I.16
2. I.28 <- I.27
3. I.29 <- I.27 (+ DA5 explicit) **CRITICAL: parallel postulate**
4. I.29 variants (5 convenience forms)
5. I.30 <- I.27, I.29
6. I.31 <- I.23, I.27

**Estimated total**: ~45 ProofStep objects
**Files to modify**: `verifier/e_proofs.py`, `verifier/e_library.py` (variant entries)
**Key risk**: DA5 must be explicitly cited; `euclid_finish` hides it in LeanEuclid

### Milestone M4: Core Theorems (I.32-I.34) — Group B5

**Prerequisites**: M2 complete

**Estimated total**: ~17 ProofStep objects
**Files to modify**: `verifier/e_proofs.py`

### Milestone M5: Area Propositions (I.35-I.45) — Groups B6+B7+B8

**Prerequisites**: M4 complete, extension lemmas for area axioms

**Pre-work**: Create `verifier/e_extension_lemmas.py` with:
- `parallelogram_area` derived from DAr1 + DAr2
- `parallelogram_same_side` derived from TI axioms
- `sum_parallelograms_area` derived from M3

**Implementation order**:
1. Extension lemmas (pre-work)
2. I.35 <- I.29, I.34
3. I.36 <- I.34, I.35
4. I.37 <- I.31, I.35
5. I.38 <- I.31, I.36
6. I.39 <- I.31, I.37
7. I.40 <- I.38, I.39
8. I.41 <- I.34, I.37
9. I.42 <- I.23, I.31, I.41
10. I.43 <- I.34
11. I.44 <- I.42, I.43
12. I.45 <- I.42, I.44

**Estimated total**: ~79 ProofStep objects
**Files to modify**: `verifier/e_proofs.py`, new `verifier/e_extension_lemmas.py`

### Milestone M8: Pythagorean Theorem (I.46-I.48) — Group B9

**Prerequisites**: M5 complete, all extension axioms available

**Implementation order**:
1. I.46 (construct square)
2. I.46' (variant)
3. I.47 (Pythagorean theorem) **HARDEST PROOF IN BOOK I**
4. I.48 (converse)

**Estimated total**: ~45 ProofStep objects
**Key risk**: I.47 needs `rectangle_area` and `sum_parallelograms_area` extensions
**Files to modify**: `verifier/e_proofs.py`, `verifier/e_library.py` (I.46' entry)

---

## File Structure

```
verifier/
  e_axioms.py           -- System E axioms (complete, verified)
  e_library.py          -- Proposition sequent signatures (extend for variants)
  e_proofs.py           -- Hand-written proofs (33 stubs to fill)
  e_consequence.py      -- Diagrammatic closure engine (complete)
  e_ast.py              -- AST types including ProofStep, StepKind
  e_extension_lemmas.py -- NEW: derived extension axioms for area props
  tarski_axioms.py      -- NEW: Tarski T1-T11 (Track A)
  tarski_proofs.py      -- NEW: Tarski derivations (Track A)
  geocoq_compat.py      -- GeoCoq predicate mappings (exists)

solved_proofs/
  Proposition I.1.euclid  -- Reference format for .euclid JSON files

unsolved_proofs/
  Proposition I.16.euclid -- through I.48: canvas/premises/goal, empty steps
```

---

## Implementation Workflow Per Proposition

For each proposition I.N:

1. **Read LeanEuclid** `Book/PropN.lean` — count `euclid_apply` calls, note construction steps
2. **Map variables** — LeanEuclid uses single letters; map to our naming
3. **Write ProofStep list** — translate each `euclid_apply` to the appropriate StepKind
4. **Handle `euclid_finish`** — replace with explicit METRIC/TRANSFER/DIAGRAMMATIC steps
5. **Handle `by_contra`** — convert to Fitch subproof with negated assumption
6. **Register in `_make_prop_iN()`** — replace the fallback stub
7. **Run tests** — verify the proposition passes verification
8. **Update .euclid file** — fill in the steps array in `unsolved_proofs/`

---

## Risk Register

| Risk | Impact | Mitigation |
|------|--------|------------|
| `euclid_finish` hides complex reasoning | Steps may be incomplete | Check e_consequence.py closure covers all cases |
| Extension axioms not derivable | Blocks I.35-I.48 | Prove them early; fall back to justified axiom if needed |
| I.47 proof too long for manual transcription | Errors likely | Break into sub-lemmas; test incrementally |
| I.29 variants used inconsistently | Later props may fail | Define all 5 variants before starting M2 |
| DA5 implicit in LeanEuclid | I.29+ may silently fail | Always cite DA5 explicitly in TRANSFER steps |

---

## Success Criteria

- All 48 propositions pass `test_verify_all_propositions`
- No `_fallback_proof` stubs remain in `e_proofs.py`
- Each proof uses only axioms, constructions, and earlier propositions
- Area propositions (I.35-I.48) have explicit extension lemma justifications
- I.29 correctly cites DA5 (parallel postulate) as a TRANSFER step
- All .euclid files in `unsolved_proofs/` have non-empty steps arrays

---
https://geocoq.github.io/GeoCoq/
https://www.academia.edu/75503662/Formalization_of_the_arithmetization_of_Euclidean_plane_geometry_and_applications
https://github.com/GeoCoq/GeoCoq/releases
https://www.isa-afp.org/browser_info/current/AFP/IsaGeoCoq/outline.pdf
https://lists.cam.ac.uk/sympa/
https://github.com/loganrjmurphy/LeanEuclid
https://arxiv.org/html/2508.14644v1
https://arxiv.org/pdf/2508.14644
https://leanprover-community.github.io/archive/stream/116395-maths/topic/tarski.20axiom.20geometry.html

*Plan version 2.0 — Enhanced with LeanEuclid source code verification*
*Last updated: Session 3*
