# Priorities and Issues for AlgTop Formalization

## Status: 160 sorries, builds in ~30s, 17500+ lines

## 🎉🎉 MAJOR: Lebesgue Subdivision FULLY PROVED!

The Lebesgue subdivision step in Lemma_54_1 — previously THE key
bottleneck blocking path lifting, π₁(S¹)≅ℤ, FTA, and Jordan —
is now fully proved via:

1. `open_cover_subdivision_01` ✓ (creeping lemma, Sup-based)
2. `top1_continuous_preimage_ball` ✓ (top1→HOL bridge)
3. `hpointwise` ✓ (covering map + bridge)
4. `heps_spec` ✓ (someI_ex)
5. `hcov_hyp` ✓ (bexI + assumption)
6. Cover transfer ✓ (image monotonicity)

## Remaining in Lemma_54_1

```
Lebesgue subdivision ✓✓✓ (COMPLETE!)
Lift construction ← 3 structured sorries:
  1. Induction (extend lift by one interval)
  2. Specialization (k=n gives full lift)
  3. Continuity (pasting lemma)
```

## Sorry Distribution: 160

- §51-§54: 7 (lift construction + product covering)
- §55: 1 (k continuous on B²)
- §56 FTA: 4 (Steps 1-2)
- §57 Borsuk-Ulam: 9 (covering theory)
- §58: 1 (pre-existing timeout)
- §59: 2 (Lebesgue for Theorem_59_1)
- §61-§85: 136 (deep downstream results)

## Build Time Critical

File at 17500+ lines, build ~30s. The §51 `define g51` optimization
saved ~10s CPU. Further code additions risk cascading timeouts.
