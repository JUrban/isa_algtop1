# Priorities and Issues for AlgTop Formalization

## Status: 159 sorries, builds in ~27s

## 🎉 Fully Proved Theorems (key selection)

- **Theorem_53_1** — R→S¹ covering map (all 4 arcs, ~800 lines)
- **Theorem_80_1** — universal covering uniqueness
- **nulhomotopic_trivializes_loops_general** — arbitrary X→Y version
- **simply_connected_trivial_image** — SC ⟹ trivial π₁ image
- **Theorem_54_5** — π₁(S¹) ≅ ℤ bijection
- **Lemma_54_1_uniqueness** — path lifting uniqueness
- **Theorem_54_3** — path-homotopic paths lift path-homotopically
- **FTA Steps 3-4** — polynomial root finding

## Critical Path to FTA

```
Theorem_53_1 ✓ → Lemma_54_1 (path lifting) ❌ [Lebesgue]
  → Theorem_54_5_iso (homomorphism) ❌
  → FTA Step 1 ❌ → Step 2 (partially expanded) → Steps 3-4 ✓ → FTA ✓
```

### FTA Step 2 status:
- hnul_all ✓, hTS1c ✓, hTC0 ✓, hg_cont ✓
- hznf_loop ✓, hconst_loop ✓, hnul_S1 ✓
- Remaining: hj_inj (retraction), hnontrivial (π₁ nontriviality)

### Build time optimizations:
- §51 Theorem_51_2 hg_beta pattern: ~8s saved
- Case-split for G∘β path products: ~2s saved
- Total: ~27s (down from ~35s)

## Sorry Count: 159
