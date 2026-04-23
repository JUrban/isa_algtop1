# Priorities and Issues for AlgTop Formalization

## Status: 149 sorry statements, builds in ~37s, 22700+ lines

## FTA — COMPLETE! ZERO SORRIES!

### FTA Proof Chain (all ZERO sorries):
| Component | Line | Status |
|-----------|------|--------|
| Lemma_54_1 (path lifting) | ~6222 | ✅ ZERO SORRY |
| homotopy_lifting_rectangle_step | ~7040 | ✅ ZERO SORRY |
| grid_from_per_piece_subdivisions | ~7455 | ✅ ZERO SORRY |
| Lemma_54_2 (homotopy lifting) | ~7938 | ✅ ZERO SORRY |
| Theorem_54_3 (homotopic lifts) | ~9559 | ✅ ZERO SORRY |
| Theorem_54_5 (π₁(S¹) ≅ ℤ) | ~10620 | ✅ ZERO SORRY |
| Theorem_56_1_step_1_inj | ~14847 | ✅ ZERO SORRY |
| **Theorem_56_1_FTA** | ~15928 | **✅ ZERO SORRY** |

## Recently Proved (2026-04-19/20):
- step_1_inj ψ⁻¹ back-transfer (closes last FTA pre-sorry)
- R2_simply_connected (path connectivity + loop contraction via SLH)
- hq_star_inj (z² injective on π₁ via ψ-bridge to step_1_inj)
- R2_minus_point_not_simply_connected (translation homeomorphism transfer)

## Remaining sorries (grouped by section):

### §57 Theorem_57_1 (antipode-preserving not nulhomotopic): 5 sorries
- hq_cover: q(x,y)=(x²-y²,2xy) is covering map S¹→S¹ (KEY BLOCKER)
- obtain k: factor q∘h = k∘q via antipodal condition
- hk_nontrivial: k_* nontrivial
- hh_star_nontrivial: h_* nontrivial
- hrh_star_nontrivial: (ρ∘h)_* nontrivial

### §57 Theorem_57_3 (Borsuk-Ulam S²): 3 sorries
- g continuous (normalization)
- g not nulhomotopic
- g nulhomotopic (hemisphere retraction)

### §59 Theorem_59_1 (loop decomposition): 2 sorries
- Lebesgue subdivision
- Path decomposition construction

### §60 Surfaces: 4 sorries
- stereographic_proj_homeomorphism (KEY BLOCKER for §61-63)
- S2_minus_point_simply_connected (blocked by stereographic)
- S2_minus_two_points_not_sc (blocked)
- map_into_S2_minus_point_nulhomotopic (blocked)

### §60 Theorem_60_1_product (π₁(X×Y) ≅ π₁(X)×π₁(Y)): 3 sorries
- Φ homomorphism
- Φ injective
- Φ surjective

### §62 Theorem_62_3 (invariance of domain): 3 sorries
### §63 Theorem_63_2 (arc no separation): multiple sorries
### §63 Theorem_63_4 (Jordan Curve): multiple sorries
### §65 Lemma_65_1 (K4 subgraph): 1 sorry
### §68 Theorem_68_7 (quotient free product): 1 sorry
### §69 Theorem_69_2: 1 sorry
### §70 Theorem_70_2 (Seifert-van Kampen): 1 sorry
### §79 Covering space equivalence: multiple sorries
### §84 Theorem_84_7 (fund group of graph): multiple sorries

## Key Blockers:
1. **hq_cover** (z² covering map) — blocks all of §57 (Borsuk-Ulam chain)
2. **stereographic_proj_homeomorphism** — blocks §60-63 (surfaces, Jordan curve)
3. **Theorem_59_1** (loop decomposition) — blocks Seifert-van Kampen
