# Priorities and Issues for AlgTop Formalization

## Status: 158 sorries, builds in ~28s, 18500+ lines

## FTA — STRUCTURALLY COMPLETE but 3 recursive sorry dependencies

The FTA proof chain itself has ZERO internal sorries. But it depends
on Theorem_54_3 which uses Lemma_54_2 (homotopy lifting), and on
Theorem_54_5 which also uses Lemma_54_1 (path lifting).

### Recursive sorries blocking FTA completion:

1. **Lemma_54_1 line 6507**: Path lifting CONTINUITY (pasting lemma)
   - The lift construction is complete; only continuity is missing
   - Needs: strengthened induction tracking continuity, or pasting lemma

2. **Lemma_54_2 line 6805**: Homotopy lifting LEBESGUE SUBDIVISION  
   - Need Lebesgue number for I×I → B covering
   - Similar to the 1D case (proved) but for 2D

3. **Lemma_54_2 line 6810**: Homotopy lifting CONCLUSION
   - Given the Lebesgue subdivision, construct the 2D lift
   - Needs rectangle-by-rectangle extension argument

### Dependency chain:
```
FTA → Step 3 → Step 2 → hnontrivial → Theorem_54_3 → Lemma_54_2 (2 sorries)
Theorem_54_5 (π₁(S¹)≅ℤ) → Theorem_54_4 → Lemma_54_1 (1 sorry)
                          → Theorem_54_3 → Lemma_54_2 (2 sorries)
```

## Jordan Curve Theorem — Proof Sketches with Infrastructure

### Infrastructure lemmas added (sorry'd):
- stereographic_proj_homeomorphism
- S2_minus_point_simply_connected  
- S2_minus_two_points_not_simply_connected
- map_into_S2_minus_point_nulhomotopic
- R2_simply_connected
- R2_minus_point_not_simply_connected

### Proved:
- Lemma_61_2 (nulhomotopy via arc factorization) — via contractibility
- h_pi1_trivial in Theorem_63_2 — via S2_minus_point
- h_pi1_X_nontrivial in Theorem_61_3 — via S2_minus_two_points
- north_pole_in_S2

## Fully Proved Key Results (zero recursive sorries)
- Theorem_53_1 (R→S¹ covering) ✓
- fundamental_group_mul_eq_class ✓
- fundamental_group_class_members_equiv ✓
- nulhomotopic_trivializes_loops_general ✓
- Corollary_55_4 (S¹ inclusion not nulhomotopic) ✓
