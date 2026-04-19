# Priorities and Issues for AlgTop Formalization

## Status: 162 sorries, builds in ~26s

## Fully Proved Theorems/Lemmas (selection)

- `Theorem_80_1_universal_unique` — universal covering uniqueness (full proof!)
- `nulhomotopic_trivializes_loops` — key lemma for Borsuk-Ulam
- `simply_connected_trivial_image` — SC ⟹ trivial π₁ image
- `top1_R_to_S1_int_shift` — periodicity of covering map
- `top1_Z_is_abelian_group` — ℤ is abelian group
- `Theorem_54_5` — π₁(S¹) ≅ ℤ bijection
- `Lemma_54_1_uniqueness` — path lifting uniqueness
- `Theorem_54_3` — path-homotopic paths lift path-homotopically
- `Corollary_59_2` — simply connected union
- All FTA Steps 3-4

## B. Current Work Priorities

### B1. π₁(S¹) ≅ ℤ homomorphism
- Bijection ✓, assembly ✓. Homomorphism sorry remains (translated-lift concatenation).

### B3. R → S¹ covering (Theorem_53_1)
- arc_E: FULLY PROVED
- arc_N: openness ✓, V_open ✓, V_disj ✓, V_union ✓, **V_homeo sorry**
- arc_W: openness ✓, V_open ✓, V_disj ✓, V_union ✓, **V_homeo sorry**
- arc_S: openness ✓, V_open ✓, V_disj ✓, V_union ✓, **V_homeo sorry**

### B2. Path lifting (Lemma 54.1)
- Lebesgue subdivision + lift construction sorry'd

### B5. Lemma_55_3 forward
- k extends h ✓. k continuous sorry.

### FTA
- Steps 3-4 ✓. Step 1 (z^n injectivity) sorry. Step 2 expanded with 3 substeps.
