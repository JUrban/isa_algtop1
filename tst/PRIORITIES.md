# Priorities and Issues for AlgTop Formalization

## Status: 155 sorries, builds in ~30s, 19500+ lines

## FTA — 2 RECURSIVE SORRIES FROM COMPLETE

### FTA Recursive Dependency Chain:
| Component | Sorries | Status |
|-----------|---------|--------|
| Lemma_54_1 (path lifting) | **0** | ✅ COMPLETE |
| Lemma_54_2 (homotopy lifting) | **2** | Lebesgue grid + base continuity |
| homotopy_lifting_rectangle_step | **0** | ✅ COMPLETE |
| Theorem_54_3 (homotopic lifts) | 0 | ✅ |
| Theorem_54_5 (π₁(S¹) ≅ ℤ) | 0 | ✅ |
| FTA Step 2 | 0 | ✅ |
| FTA Step 3 | 0 | ✅ |
| FTA (main theorem) | 0 | ✅ |

### The 2 remaining Lemma_54_2 sorries:
1. **Lebesgue grid existence**: N>0 with each 1/N-rectangle mapping into evenly covered U
   (requires Lebesgue number lemma for compact metric space I×I)
2. **Base case continuity** (hFt0_cont): Ft0 continuous on L-shape (edges)
   (needs pasting_lemma_two_closed on left_lift∘snd and bot_lift∘fst)

### Recently proved in Lemma_54_2:
- ✅ hsubs (II_topology elements ⊆ I×I)
- ✅ hAR_sub (A_k ∪ R ⊆ I×I)  
- ✅ hR_closed (rectangle closed via closedin_II_rectangle helper)
- ✅ hA_closed (A_k closed via finite union of closed)
- ✅ hC_ne (boundary nonempty via corner point)
- ✅ hC_eq (A_k ∩ R = L-shape via grid non-overlap)
- ✅ hC_conn (L-shape connected via Theorem_23_3 + edge connectedness)
- ✅ A(m*n) = I×I (via increasing_interval_cover pigeonhole helper)
- ✅ subspace_topology self-equality
- ✅ Grid derivation (subdivision from N-based grid)

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
- **homotopy_lifting_rectangle_step**: ZERO SORRIES ✓✓✓
- **Theorem_54_5** (π₁(S¹) ≅ ℤ): ZERO SORRIES ✓
- **FTA** Steps 2, 3, 4: ZERO SORRIES ✓
- **Theorem_53_1** (R→S¹ covering): ZERO SORRIES ✓
- Corollary_55_4, nulhomotopic_trivializes: ZERO SORRIES ✓

## Helper lemmas added:
- closedin_I_sub_interval: closed sub-intervals of I are closed in I_top
- closedin_II_rectangle: closed rectangles are closed in II_topology
- increasing_interval_cover: pigeonhole for monotone subdivisions
