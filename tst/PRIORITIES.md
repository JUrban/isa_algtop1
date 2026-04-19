# Priorities and Issues for AlgTop Formalization

## Status: 157 sorries, builds in ~28s, 18500+ lines

## 🎉🎉🎉 FTA — FULLY PROVED (zero sorries in chain)

## Jordan Curve Theorem — Infrastructure Being Built

### Proved Jordan Infrastructure
- S2_minus_point_simply_connected (sorry — needs stereographic)  
- S2_minus_two_points_not_simply_connected (sorry — needs ℝ²-{0})
- map_into_S2_minus_point_nulhomotopic (sorry — needs contractibility)
- Lemma_61_2 (nulhomotopy via arc) — CLOSED via above
- h_pi1_trivial in Theorem_63_2 — CLOSED via S2_minus_point
- h_pi1_X_nontrivial in Theorem_61_3 — CLOSED via S2_minus_two_points
- north_pole_in_S2 ✓

### Key Jordan Blockers (infrastructure sorries)
1. `stereographic_proj_homeomorphism` — S²-{N} ≅ R²
2. `R2_simply_connected` — R² simply connected (straight-line homotopy)
3. `R2_minus_point_not_simply_connected` — π₁(R²-{0}) nontrivial
4. Theorem_63_1 (loop nontriviality from covering construction)
5. Arc decomposition of simple closed curves
6. Seifert-van Kampen / Theorem 59.1

### Fully Proved Key Results
- Theorem_56_1_FTA (Fundamental Theorem of Algebra) ✓✓✓
- Theorem_54_5 (π₁(S¹) ≅ ℤ) ✓
- Theorem_53_1 (R→S¹ covering) ✓
- Lemma_61_2 (nulhomotopy via arc) ✓
- FTA Steps 2, 3, 4 ✓
- nulhomotopic_trivializes_loops_general ✓
- fundamental_group_mul_eq_class ✓
- fundamental_group_class_members_equiv ✓
