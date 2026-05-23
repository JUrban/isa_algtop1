# Revised Polygon-to-Disk Proposal: Recovering the Cone Decomposition

## What we actually had (and deleted)

In `bck0107`, the old `polygon_homeomorphic_to_disk` was **1156 lines** with **166 proved facts** and only **5 sorrys**:

1. **D > 0** (line 3813): `cross2(v_i - c, v_{i+1} - c) > 0`
2. **β'+γ' ≤ 1** (line 3929): barycentric coordinate bound
3. **ψ continuous** (line 4079): piecewise continuous on finite closed cover
4. **ψ surjective** (line 4083): image covers B²
5. **ψ injective** (line 4087): no two points map to the same image

### What was proved (key infrastructure):

- **Centroid in P** (hc_in_P): coefficients 1/n
- **Cone decomposition** (hP_cones): every z ∈ P lies in some cone (263 lines of cross product analysis, cyclic sign change, Cramer's rule)
- **Barycentric coordinates via Cramer**: β' = cross2(z-c, v_{i+1}-c)/D, γ' = cross2(v_i-c, z-c)/D
- **β' ≥ 0, γ' > 0**: from cross product signs at the sign-change sector
- **Cramer verification** (hzc_x, hzc_y): z-c = β'·(v_i-c) + γ'·(v_{i+1}-c) (50+ lines of algebra)
- **cone_map definition**: normalized — divides by √(fst²+snd²), so maps to S¹ (not inscribed polygon)
- **ψ definition**: via SOME for cone index + coordinates
- **Theorem 26.6 bridge**: continuous bijection compact→Hausdorff = homeomorphism

### What was NOT proved (the 5 sorrys):

**Sorry 1 (D > 0)**: Cross product of consecutive vertex vectors from centroid is positive. This requires vertices to be in CCW order. **We now have the CCW condition in the cached definition.** So this sorry becomes:

```
have hD_pos: "?D > 0"
  using hccw[rule_format, OF hi] unfolding cross2_def by (by100 simp)
```

Essentially a 1-line proof.

**Sorry 2 (β'+γ' ≤ 1)**: z ∈ P implies the barycentric coordinates sum to at most 1. Previous analysis showed: β'+γ' = 1 + cross2(z-v_i, v_{i+1}-v_i)/D. For z inside P (on the "inside" of edge i), cross2(z-v_i, v_{i+1}-v_i) ≤ 0 when D > 0. This follows from z being in the convex hull + all vertices on the same side of each edge (convexity + CCW). Estimated: **30-50 lines** using the hull condition.

**Sorry 3 (ψ continuous)**: The reviewer correctly says: use pasting lemma on the cones as a finite closed cover. Each cone_map is continuous (polynomial + sqrt normalization, with D_i > 0 ensuring the denominator is nonzero). Adjacent cones agree on shared edges. The current code defines ψ via SOME (bad for continuity). **Fix**: define ψ as SOME y where all local maps agree, then show uniqueness. Or: define ψ directly using the cone_map + Cramer coordinates (polynomial in z). Estimated: **60-80 lines**.

**Sorry 4 (ψ surjective)**: For any point s·(cos θ, sin θ) ∈ B², find the sector i containing angle θ, invert the cone_map. Since cone_map is normalized, this is an explicit construction. Estimated: **40-60 lines**.

**Sorry 5 (ψ injective)**: If ψ(z₁) = ψ(z₂), they must be in the same or adjacent cones. Within a cone, cone_map is injective (non-degenerate affine + normalization). Between cones, images are in different sectors. Estimated: **40-60 lines**.

## The reviewer's key recommendations vs our situation

### 1. "Do not define sector with THE" — AGREE
The old code used SOME for cone index. The reviewer says use local maps + gluing. This is correct. But the OLD CODE already has the local maps (cone_map) and the Cramer coordinates (β', γ'). We just need the gluing step.

### 2. "Verify polygon vertex order" — ALREADY DONE
The reviewer didn't see our CCW addition to the cached definition. We have:
```
∀i<n. (vx i - cx)·(vy_{i+1} - cy) - (vy i - cy)·(vx_{i+1} - cx) > 0
```
This gives D > 0 immediately. **This blocker is solved.**

### 3. "Use pasting lemma" — AGREE
The continuity proof should use `closed_cover_continuous` or similar. The cones C_i are closed (convex hull of 3 points), cover P, and the local maps agree on overlaps. This is the standard approach.

### 4. "HOL-Analysis shortcut" — NOT AVAILABLE
We import Complex_Main, not HOL-Analysis. The `homeomorphic_convex_compact_sets_eq` theorem is not accessible. And it wouldn't give boundary correspondence anyway.

### 5. "Effort estimate 400-800 lines" — PARTIALLY AGREE
Starting from SCRATCH: yes, 400-800. But we're NOT starting from scratch. The old code has 1156 lines with 166 proved facts. The cone decomposition, Cramer coordinates, cross product analysis, centroid properties — all proved. We need to:
- Add CCW → close D > 0 (~5 lines)
- Prove β'+γ' ≤ 1 (~40 lines)
- Restructure ψ for pasting lemma + close continuity (~80 lines)
- Close surjectivity (~50 lines)  
- Close injectivity (~50 lines)

**Estimated: ~225 lines of NEW proof** on top of the existing 1156 lines.

## Proposed plan

### Step 1: Recover the old code
Copy lines 2974-4129 from bck0107 back into AlgTop.thy, placing it before polygon_homeomorphic_to_disk_with_boundary. Keep the new radial version too (it provides boundary correspondence).

### Step 2: Close D > 0 (1 line)
The CCW condition in the definition gives this directly:
```
using hccw[rule_format, OF hi] unfolding cross2_def by simp
```

But wait — the old code extracts from `top1_is_polygonal_region_on`, not from the scheme definition. The CCW condition is in `top1_quotient_of_scheme_on`, not `top1_is_polygonal_region_on`. So the old standalone lemma doesn't have CCW.

**Options:**
a) Add CCW as an assumption to the old lemma (like we did for the new one)
b) Add CCW to `top1_is_polygonal_region_on` in the cached definition

Option (a) is simpler and mirrors what we did for the new lemma.

### Step 3: Close β'+γ' ≤ 1 (~40 lines)
With D > 0, show cross2(z-v_i, v_{i+1}-v_i) ≤ 0 for z ∈ P. This uses:
- z = Σ coeffs·v_k (from hull)
- cross2 is linear in first argument
- Each cross2(v_k - v_i, v_{i+1} - v_i) ≤ 0 for k ≠ i, i+1 (all vertices on same side of edge, from convexity + CCW)
- The sum is ≤ 0

### Step 4: Restructure ψ definition for pasting (~20 lines)
Instead of SOME for cone index, define:
```
ψ z = cone_map (SOME i. i < n ∧ in_cone i z) α β γ
```
where α, β, γ are the Cramer coordinates for that cone. The key: prove that for z in the overlap of two cones, cone_map gives the same value. Then SOME gives a well-defined result.

Actually, the reviewer's suggestion is better: define local maps ψ_i on each cone C_i, prove they agree on overlaps, then define ψ as the unique common value. But this requires restructuring the existing code.

**Simpler alternative**: keep SOME but prove that the result is UNIQUE (any two cones give the same ψ value). Then continuity follows from the pasting lemma applied to ψ_i = cone_map restricted to C_i.

### Step 5: Close continuity (~80 lines)
- Define C_i = {z | in_cone i z} (closed — convex hull of 3 points)
- Show C_i is closed (compact, hence closed in Hausdorff R²)
- Show P = ∪C_i (from hP_cones)
- Show cone_map_i is continuous on C_i (polynomial + sqrt, D_i > 0)
- Show cone_map_i = cone_map_j on C_i ∩ C_j (overlap is an edge, both maps give the same linear interpolation on S¹)
- Pasting lemma → ψ continuous on P

### Step 6: Close surjectivity (~50 lines)
For (r·cos θ, r·sin θ) ∈ B² with 0 ≤ r ≤ 1:
- Find sector i containing angle θ (between angles of q_i and q_{i+1})
- Invert the normalization: find β, γ with β·q_i + γ·q_{i+1} normalized = (cos θ, sin θ)
- Set α = 1 - r·(β+γ)/normalized_factor
- Then z = α·c + β·v_i + γ·v_{i+1} maps to the target

### Step 7: Close injectivity (~50 lines)
If ψ(z₁) = ψ(z₂):
- The normalized direction determines the sector (angle on S¹)
- The radius determines s = 1-α
- So α₁ = α₂, and the boundary points match
- Since cone_map is affine (hence injective) on each cone with D > 0, z₁ = z₂

## Risk assessment

**Low risk:**
- D > 0: trivial from CCW
- Cone cover (hP_cones): already proved (263 lines!)
- Cramer coordinates: already proved

**Medium risk:**
- β'+γ' ≤ 1: needs convex hull + CCW argument (~40 lines)
- Continuity pasting: standard but needs care at cone boundaries (~80 lines)
- Surjectivity: explicit but needs angle calculations (~50 lines)

**Main risk:**
- The ψ definition uses SOME which the reviewer warned against. If the "prove SOME gives unique value" approach doesn't work cleanly, we may need the full local-map restructuring (adds ~50 lines).
- The boundary correspondence (ψ(BdP) = S¹) is NOT in the old lemma's conclusion. We still need the new lemma for that. The old lemma gives the bare homeomorphism; the new lemma adds boundary.

## Alternative: two-lemma approach

Instead of one big lemma, use two:
1. **Old lemma** (recovered, augmented with CCW): bare homeomorphism P → B²
2. **New lemma** (current, using old lemma): adds boundary correspondence

The new lemma calls the old one to get ψ, then proves ψ(BdP) = S¹ separately. This separation of concerns might be cleaner.

But the boundary correspondence proof still needs to know HOW ψ is constructed (cone_map with normalization). So it can't be fully black-box.

## Bottom line

Recovering the old cone decomposition and adding CCW is the FASTEST path. We have 1156 lines of proved infrastructure. With CCW, sorry 1 becomes trivial. Sorry 2 needs ~40 lines. Sorrys 3-5 need the pasting lemma restructuring (~180 lines). Total new work: **~225 lines**.

The reviewer's concern about vertex ordering is already addressed. The concern about THE/SOME is valid but manageable — we prove uniqueness rather than restructuring to local maps.
