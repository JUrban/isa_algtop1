# Priorities and Issues for AlgTop Formalization

## Status: 159 sorries, builds in ~27s

## 🎉 Major Milestones Completed

- **Theorem_53_1** (R→S¹ covering map) — FULLY PROVED (all 4 arcs)
- **Theorem_80_1** (universal covering uniqueness) — FULLY PROVED
- **nulhomotopic_trivializes_loops** — FULLY PROVED
- **simply_connected_trivial_image** — FULLY PROVED

## Critical Path: FTA and Jordan

Both FTA and Jordan depend on the **Lebesgue number argument** for path lifting:

```
Theorem_53_1 ✓
  → Lemma_54_1 (path lifting) ← LEBESGUE NUMBER SORRY
    → Theorem_54_3 (homotopic lifts)
      → Theorem_54_5_iso (π₁(S¹)≅ℤ homomorphism) ← SORRY
        → Step 1 (z^n injectivity) ← SORRY
          → Step 2 ← SORRY
            → Steps 3-4 ✓ → FTA ✓

Theorem_53_1 ✓
  → Lemma_54_1 ← SAME BLOCKER
    → ... → Theorem_59_1 (Seifert-van Kampen)
      → Corollary_59_2 ✓ → §61-63 → Jordan
```

### B1. Path Lifting (Lemma 54.1) — HIGHEST PRIORITY

The Lebesgue number lemma `top1_lebesgue_number` exists in Top0 library.
Needs: bridge [0,1] as metric space → apply lemma → get subdivision.
Then: interval-by-interval lift construction (induction + pasting lemma).

### B2. π₁(S¹)≅ℤ Homomorphism

φ bijective ✓. Homomorphism needs: translated-lift concatenation.
Key helper available: `top1_R_to_S1_int_shift`.

### B3. FTA Steps 1-2

Step 1: z^n injectivity on π₁(S¹) — needs homomorphism.
Step 2: z^n not nulhomotopic in C-{0} — needs Step 1 + retraction.

## Work Order

1. **Path lifting Lebesgue step** (B1) — unblocks everything
2. **Lift construction** (B1 Step 2) — induction + pasting
3. **Homomorphism** (B2) — translated lifts
4. **FTA Steps 1-2** (B3) — covering theory applications
