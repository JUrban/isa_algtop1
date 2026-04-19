# Priorities and Issues for AlgTop Formalization

## Status: 154 sorries, builds in ~27s, 18400+ lines

## 🎉 FTA — 1 sorry from complete!

### FTA Step 1 (hinj) — THE remaining blocker
  - z^n induces injective map on π₁(S¹)
  - Needs: z^n ∘ standard-loop lifts to s↦ns (winding number n)
  - Needs: complex↔real S¹ bridge (partially built via ψ=(Re,Im))
  - Needs: φ(z^n∘f) = n·φ(f) for the isomorphism φ from Thm 54.5

### ✅ FTA Step 2 — FULLY PROVED
  - hj_inj: retraction sgn transfers homotopy C-{0}→S¹ ✓
  - hnontrivial: z^n not nulhomotopic (covering lift to n≠0) ✓

### ✅ FTA Steps 3-4 — FULLY PROVED

## 🎉 π₁(S¹) ≅ ℤ (Theorem 54.5) — FULLY PROVED
  - Bijection φ via lifting correspondence + floor ✓
  - Injectivity via Theorem 54.3 + class equality ✓
  - Homomorphism via translated lift concatenation + R_to_S1 periodicity ✓
  - fundamental_group_class_members_equiv ✓
  - fundamental_group_mul_eq_class ✓

## Sorry Distribution: 154

- §53: 1 (product covering map)
- §54: ~4 (continuity + homotopy lifting)
- §55: 1 (k continuous on B²)
- §56 FTA: 1 (Step 1 hinj only!)
- §57 Borsuk-Ulam: ~9
- §59-§85: ~138 (downstream results)

## Fully Proved Key Results

- Theorem_53_1 (R→S¹ covering) ✓
- Theorem_54_5 (π₁(S¹) ≅ ℤ) ✓ 
- open_cover_subdivision_01 (creeping lemma) ✓
- nulhomotopic_trivializes_loops_general ✓
- Theorem_80_1 (universal covering uniqueness) ✓
- FTA Steps 2, 3, 4 ✓
- fundamental_group_mul_eq_class ✓
- fundamental_group_class_members_equiv ✓
