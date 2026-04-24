# Jordan Curve Theorem Formalization Progress Report

## Overall: 139 sorries (down from 153 = 14 net closed)

## Build: 14s (16K lines cached in Top0 session)

## Complete Zero-Sorry Infrastructure

### S² Topology (8 lemmas)
- `stereographic_proj_homeomorphism` — S²-{N} ≅ R² (with explicit inverse)
- `stereographic_inv_in_S2`, `stereographic_inv_not_north`
- `stereographic_proj_inv`, `stereographic_inv_proj`
- `householder_S2_homeo` — Householder reflection S²-{b} → S²-{N} (350 lines)
- `S2_minus_point_simply_connected` — S²-{b} sc for ALL b
- `S2_minus_north_pole_simply_connected`

### Derived S² Results (3 lemmas)
- `S2_minus_point_homeo_R2` — S²-{b} ≅ R² (Householder + stereographic)
- `S2_minus_two_points_not_simply_connected` — S²-{a,b} not sc
- `R2_minus_point_not_simply_connected` — R²-{p} not sc

### Nulhomotopy (3 lemmas)
- `map_into_R2_nulhomotopic` — R² contractible (straight-line homotopy)
- `map_into_S2_minus_point_nulhomotopic` — any map into S²-{b} nulhomotopic
- `nulhomotopic_transfer` — transfer nulhomotopy through homeomorphism

### Homeomorphism Infrastructure (7 lemmas)
- `homeomorphism_inverse` — inverse of homeomorphism
- `homeomorphism_comp` — composition of homeomorphisms
- `homeomorphism_restrict_point` — restricting to X-{p} → Y-{h(p)}
- `homeomorphism_preserves_simply_connected`
- `homeomorphism_preserves_simply_connected_forward`
- `homeomorphism_reflects_simply_connected`
- `top1_mult_continuous_R2` — multiplication R²→R continuous

### Theorem 61.3 Partial (6 facts proved)
- `hA1_closed`, `hA2_closed` — arcs closed in S² (compact in Hausdorff)
- `hU_open`, `hV_open` — complements of arcs open in X
- `hC_sub` — simple closed curve subset of S²
- Arc compactness via `compact_Icc` + `top1_compact_on_continuous_image`

### Theorem 63.1 Step 3 (complete modulo steps 1-2)
- Uses `Theorem_54_3` (unique lift endpoints, cached in Top0)
- Derives e1 = e0 contradiction from covering space lift

### Other (from earlier sessions)
- `R2_simply_connected` — R² simply connected
- `hq_star_inj` — z² injective on π₁(S¹)
- `step_1_inj` ψ⁻¹ back-transfer (FTA chain)

## Remaining Deep Sorries

### Critical Path for Jordan:
1. **Theorem 63.1 steps 1-2** (covering space construction)
   - Need: E = ℤ × (U⊔V)/~ as covering of X = U∪V
   - Type issue: E :: 'a set requires encoding ℤ×bool×'a into 'a
   - Step 3 (contradiction) already PROVED using Theorem_54_3

2. **Theorem 59.1** (loop decomposition, 2 sorries)
   - Step 1: Lebesgue subdivision (`top1_lebesgue_number` available in Top0)
   - Step 2: Path decomposition (path algebra)
   - Both doable but each ~100 lines

3. **Theorem 61.3** (Jordan separation, 4 sorries)
   - Arc decomposition of simple closed curve
   - U∩V path-connected (connected + locally path-connected)
   - ∃ x₀ ∈ U∩V (S²-C nonempty)
   - π₁(X) trivial (uses Theorems 59.1 + 63.1)

4. **Theorem 63.2** (arc no separation, 3 sorries)
   - Arc splitting at midpoint
   - Separation → component extraction
   - π₁ nontrivial (uses Theorem 63.1)

5. **Theorem 63.4** (Jordan Curve Theorem, 8 sorries)
   - Separation (uses Theorem 61.3)
   - Exactly 2 components (uses Theorem 63.5)
   - Path-connected, bounded/unbounded, boundary

### Key Techniques Used
- `define` for fraction opacity (Householder algebra)
- `divide_eq_eq` (subst) for denominator clearing
- `Theorem_18_4` for component-wise continuity
- `product_topology_on_open_sets` for R² topology bridge
- `top1_compact_on_continuous_image` for compact image
- `compact_in_strict_hausdorff_closedin_on` for arcs closed
- `subspace_topology_self_carrier` for self-subspace
- `inv_into_f_eq` / `inv_into_f_f` for inverse computations
