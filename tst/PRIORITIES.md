# Priorities and Issues for AlgTop Formalization

## Status: 159 sorries, builds in ~35s

## 🎉 Fully Proved Theorems/Lemmas (key selection)

- **Theorem_53_1** — R→S¹ covering map (all 4 arcs)
- **Theorem_80_1** — universal covering uniqueness
- **nulhomotopic_trivializes_loops** — S¹ → S¹ version
- **nulhomotopic_trivializes_loops_general** — arbitrary X → Y version
- **simply_connected_trivial_image** — SC ⟹ trivial π₁ image  
- **Theorem_54_5** — π₁(S¹) ≅ ℤ bijection
- **Lemma_54_1_uniqueness** — path lifting uniqueness
- **Theorem_54_3** — path-homotopic paths lift path-homotopically
- **Corollary_59_2** — simply connected union
- **FTA Steps 3-4** — polynomial root finding

## Critical Path to FTA

```
Theorem_53_1 ✓ → Lemma_54_1 (path lifting) ❌
  → Theorem_54_5_iso (homomorphism) ❌ → FTA Step 1 ❌ → Step 2 ❌
  → Steps 3-4 ✓ → FTA ✓
```

### Remaining blockers:
1. **Path lifting Lebesgue step** — bridge compact_Icc to top1 framework
2. **Lift construction** — induction + pasting lemma  
3. **π₁(S¹) homomorphism** — translated lift concatenation
4. **FTA Step 1** — z^n injectivity on π₁(S¹)
5. **FTA Step 2** — partially expanded:
   - hnul_all ✓ (via general nulhomotopic lemma)
   - hTS1c, hTC0 ✓
   - hg_cont ✓ (z^n: S¹→C-{0})
   - hznf_loop, hconst_loop ✓
   - hnul_S1 ✓ (modulo hj_inj sorry)
   - Remaining: hj_inj (retraction), hnontrivial (π₁ nontriviality)

## Sorry Count: 159
