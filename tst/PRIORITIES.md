# Priorities and Issues for AlgTop Formalization

## Status: ~159 sorries, builds in ~30s, 18000+ lines

## FTA Critical Path — FOCUS

The Fundamental Theorem of Algebra proof has 4 steps. Steps 3-4 are fully proved.
The remaining sorries in Steps 1-2 depend on π₁(S¹) ≅ ℤ (Theorem 54.5).

### Theorem 54.5 (π₁(S¹) ≅ ℤ) — 3 sorries remain

**Bijection φ: π₁(S¹) → ℤ** — PROVED (via lifting correspondence + floor)
**Injectivity** — PROVED (via Theorem 54.3 + simply_connected_paths_homotopic + class equality)
**Homomorphism φ(c·d) = φ(c) + φ(d)** — Nearly complete (3 structural sorries):
  1. `tgt_def sorry` — Translation by constant is continuous (need top1_continuous_map_on proof)
  2. `mul = class sorry` — Fundamental group mul equals equivalence class of f*g
  3. `loop_equiv sorry` — Two elements of same class are loop-equivalent

### FTA Step 1 (hinj) — 1 sorry
  - z^n induces injective map on π₁(S¹). Needs π₁(S¹) ≅ ℤ fully.

### FTA Step 2 — 2 sorries
  - `hj_inj` — PROVED (retraction r=sgn transfers homotopy C-{0}→S¹)
  - `hnontrivial` — z^n not nulhomotopic. Skeleton written, needs:
    - Standard loop p₀ = cis(2πs) is a loop on S¹_complex (sorry)  
    - n-fold winding non-contractible via covering theory (sorry)
    - Bridge between complex S¹ and real S¹ covering theory

## Lemma 54.1 Path Lifting — 1 sorry (continuity/pasting lemma)

Entire lift construction proved EXCEPT continuity of the piecewise lift.
Needs strengthening the induction to track continuity, or a pasting lemma
for finitely many closed intervals.

## Sorry Distribution: ~159

- §53: 1 (product covering map)
- §54: ~7 (continuity + homotopy lifting + Theorem 54.5 structural)
- §55: 1 (k continuous on B²)
- §56 FTA: ~3 (Steps 1-2, depend on π₁ theory)
- §57 Borsuk-Ulam: ~9 (covering theory)
- §59: ~5 (Lebesgue for Theorem_59_1)
- §60+: ~133 (downstream results)

## Fully Proved Key Results

- Theorem_53_1 (R→S¹ covering)
- open_cover_subdivision_01 (creeping lemma)
- top1_continuous_preimage_ball (bridge)
- nulhomotopic_trivializes_loops_general
- Theorem_80_1 (universal covering uniqueness)
- Theorem_54_5 bijection + injectivity
- FTA Steps 3-4
- hj_inj (retraction argument for FTA Step 2)
