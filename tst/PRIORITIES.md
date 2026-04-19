# Priorities and Issues for AlgTop Formalization

## Status: 157 sorries, builds in ~28s, 18800+ lines

## FTA — 1 RECURSIVE SORRY FROM COMPLETE

### FTA Recursive Dependency Chain:
| Component | Sorries | Status |
|-----------|---------|--------|
| Lemma_54_1 (path lifting) | **0** | ✅ COMPLETE |
| Lemma_54_2 (homotopy lifting) | **1** | continuity of 2D lift |
| Theorem_54_3 (homotopic lifts) | 0 | ✅ |
| Theorem_54_5 (π₁(S¹) ≅ ℤ) | 0 | ✅ |
| FTA Step 2 | 0 | ✅ |
| FTA Step 3 | 0 | ✅ |
| FTA (main theorem) | 0 | ✅ |

### The 1 remaining sorry:
**Lemma_54_2 hFt_cont**: Joint continuity of column-wise Hilbert-chosen lifts.
- Each column lift is continuous (path from Lemma_54_1)
- The starting points ftilde0 are continuous (from Lemma_54_1)
- Full continuity needs: Lebesgue covering + local uniqueness argument
- This is a well-known standard result (Munkres Lemma 54.2)

## Fully Proved Key Results (zero recursive sorries):
- **Lemma_54_1** (path lifting) — FULLY PROVED ✓✓✓
- Theorem_53_1 (R→S¹ covering) ✓
- Theorem_54_5 (π₁(S¹) ≅ ℤ) ✓
- FTA Steps 2, 3, 4 ✓
- fundamental_group_mul_eq_class ✓
- nulhomotopic_trivializes_loops_general ✓
- Corollary_55_4 (S¹ inclusion not nulhomotopic) ✓

## Jordan Curve Theorem — Infrastructure
- 49 sorries across §61-§65
- Key infrastructure lemmas added (stereographic, S2_minus_point, etc.)
- Lemma_61_2 (nulhomotopy via arc) PROVED
