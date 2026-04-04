# Lean → .euclid Translation Map

## Construction Rules
| Lean tactic | .euclid justification | Notes |
|---|---|---|
| `line_from_points a b` | `let-line` | prereq: ¬(a=b) |
| `circle_from_points a b` | `let-circle` | prereq: ¬(a=b) |
| `extend_point L a b` | `let-point-on-line-extend` | on(a,L), on(b,L), ¬(a=b) → new pt c: on(c,L), between(a,b,c) |
| `extend_point_longer L a b s` | `let-point-on-line-extend` | same as above |
| `exists_point_between_points_on_line L b c` | `let-point-on-line-between` | |
| `intersection_lines L M` | `let-intersection-line-line` | prereq: intersects(L,M) |
| `intersection_circle_line_extending_points α L b c` | `let-intersection-line-circle-extend` | prereq: inside(b,α), on(b,L), ¬(c=b), on(c,L) |

## Theorems
| Lean | .euclid | Key conclusions |
|---|---|---|
| `proposition_3 a b c d L M` | `Prop.I.3` | between(a,e,b), ae=cd |
| `proposition_4 a b c d e f ...` | `Prop.I.4` (SAS) | bc=ef, ∠abc=∠def, ∠bca=∠efd, △abc=△def |
| `proposition_5' a b c AB BC AC` | `Prop.I.5` | ∠abc=∠acb |
| `proposition_10 a b L` | `Prop.I.10` | between(a,d,b), ad=db |
| `proposition_13 a b c d AB CD` | `Prop.I.13` | ∠abd+∠dbc = ∟+∟ |
| `proposition_15 a b c d e L M` | `Prop.I.15` | ∠aec=∠bed |
| `proposition_16 a b c d AB BC AC` | `Prop.I.16` | ∠bac<∠dbc, ∠bca<∠dbc |

## Axioms  
| Lean axiom | .euclid justification |
|---|---|
| `between_symm` | `Betweenness 1a` |
| `between_same_line_out` | `Betweenness 2` |
| `between_same_line_in` | `Betweenness 3` |
| `between_trans_in` | `Betweenness 4` |
| `between_trans_out` | `Betweenness 5` |
| `between_points` | `Betweenness 6` |
| `two_points_determine_line` | `Generality 1` |
| `centre_unique` | `Generality 2` |
| `center_inside_circle` | `Generality 3` |
| `inside_not_on_circle` | `Generality 4` |
| `same_side_rfl` | `Same-side 1` |
| `same_side_symm` | `Same-side 2` |
| `same_side_not_on_line` | `Same-side 3` |
| `same_side_trans` | `Same-side 4` |
| `pasch_1` | `Pasch 1` |
| `pasch_2` | `Pasch 2` |
| `pasch_3` | `Pasch 3` |
| `pasch_4` | `Pasch 4` |
| `triple_incidence_1` | `Triple incidence 1` |
| `triple_incidence_2` | `Triple incidence 2` |
| `triple_incidence_3` | `Triple incidence 3` |
| `segment_symmetric` | `M3 — Symmetry` |
| `angle_symm` | `M4 — Angle symmetry` |
| `sum_angles_onlyif` (→ ∠bac = ∠bad+∠dac) | `Angle transfer 2a` |
| `sum_angles_if` (→ same-side facts) | `Angle transfer 2b` or `2c` |
| `between_if` (→ ab+bc=ac) | `Segment transfer 1` |
| `point_on_circle_onlyif` (center+on → equal radii) | `Segment transfer 3b` |
| `parallel_line_unique` | `Intersection` axiom (custom) |

## formTriangle Expansion
`formTriangle a b c AB BC AC` expands to:
- on(a, AB), on(b, AB), a≠b
- on(b, BC), on(c, BC)  
- on(c, AC), on(a, AC)
- AB≠BC, BC≠AC, AC≠AB

## Our .euclid Premise Conventions
Our e_library sequents use different variable arrangements than Lean.
Must check each PROP_I_N.sequent to see the exact hypothesis structure.

## Key Differences
1. Lean's `euclid_finish` uses SMT → must manually supply intermediate axiom steps
2. Lean's `formTriangle` bundles many premises → our proofs list them individually  
3. Lean variable order may differ from our e_library sequent → check each case
4. Lean can use `by_contra` / `by_cases` → maps to Assume/⊥-intro/⊥-elim/Cases
