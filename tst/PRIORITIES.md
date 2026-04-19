# Priorities and Issues for AlgTop Formalization

## Status: 156 sorries, builds in ~31s, 18900+ lines

## FTA — 2 RECURSIVE SORRIES FROM COMPLETE

### FTA Recursive Dependency Chain:
| Component | Sorries | Status |
|-----------|---------|--------|
| Lemma_54_1 (path lifting) | **0** | ✅ COMPLETE |
| Lemma_54_2 (homotopy lifting) | **2** | local agreement + local→global |
| Theorem_54_3 (homotopic lifts) | 0 | ✅ |
| Theorem_54_5 (π₁(S¹) ≅ ℤ) | 0 | ✅ |
| FTA Step 2 | 0 | ✅ |
| FTA Step 3 | 0 | ✅ |
| FTA (main theorem) | 0 | ✅ |

### The 2 remaining Lemma_54_2 sorries:
1. Local agreement: Ftilde = inv_into V₀ p ∘ F on neighborhoods
2. Local→global: locally continuous ⟹ continuous

## Jordan Chain — Infrastructure + R²-{0} Progress

### R2_minus_origin_not_simply_connected (nearly done):
- Standard loop on S¹ and R²-{0}: PROVED ✓
- Covering lift argument (1=0 contradiction): PROVED ✓
- Retraction transfer via r(x)=x/|x|: structured, 2 sorries (norm algebra + continuity)

### Infrastructure:
- S2_minus_point_simply_connected (sorry)
- stereographic_proj_homeomorphism (sorry)
- simple_closed_curve_subset: PROVED ✓
- Lemma_61_2 (nulhomotopy via arc): PROVED ✓

## Fully Proved Key Results:
- **Lemma_54_1** (path lifting): ZERO SORRIES ✓✓✓
- **Theorem_54_5** (π₁(S¹) ≅ ℤ): ZERO SORRIES ✓
- **FTA** Steps 2, 3, 4: ZERO SORRIES ✓
- **Theorem_53_1** (R→S¹ covering): ZERO SORRIES ✓
- Corollary_55_4, nulhomotopic_trivializes: ZERO SORRIES ✓
