# Polygon-to-Disk Homeomorphism: Final Implementation Plan

## Goal

Close all 4 sorrys in `polygon_homeomorphic_to_disk_with_boundary`:
- ψ continuous
- ψ surjective (ψ ` P = top1_B2)
- ψ injective (inj_on ψ P)
- ψ(BdP) = top1_S1

The 19 proved downstream steps (Theorem_26_6, h\<psi>_int restriction, etc.)
remain untouched — they depend only on these 4 properties.

## Current state

`polygon_homeomorphic_to_disk_with_boundary` (lines ~2973-3210) has:
- Assumptions: polygon region, n≥3, vx/vy vertices in P, P=hull(vx,vy), CCW ordering
- Centroid (cx,cy) defined and proved in P and in interior (not on BdP)
- Target vertices qx, qy on S¹ defined
- h_bd: BdP → S¹ defined (normalized interpolation)
- ψ defined using SOME (problematic for reasoning)
- pdist defined
- 4 sorrys for the above properties
- 19 proved steps deriving homeomorphism from these properties

## Plan

### Phase 1: Recover cone decomposition infrastructure from bck0107

Copy the following PROVED infrastructure from the old code (bck0107 lines ~3001-3810):
1. Vertex extraction, centroid definition, centroid in P
2. BdP definition, target vertices qx/qy
3. cross2 properties: centroid sum zero, cyclic sign change
4. Cone decomposition: hP_cones (every z ∈ P is in some cone)
   - This includes the full cyclic sign change argument (~200 lines)
   - The Cramer's rule derivation for β', γ' (~100 lines)
5. cone_map definition (normalized)
6. in_cone definition

Do NOT copy: the D=0 case split (removed), the SOME-based ψ definition,
the sorry'd ψ properties.

### Phase 2: Prove D_i > 0 from CCW (5 lines)

The CCW assumption gives:
```
(vx i - cx) * (vy(i+1) - cy) - (vy i - cy) * (vx(i+1) - cx) > 0
```

This IS cross2(v_i - c, v_{i+1} - c) = D_i. So:
```
have hD_pos: "?D > 0"
  using hccw[rule_format, OF hi] unfolding cross2_def by simp
```

This replaces the old D>0 sorry. The D=0 branch is eliminated.

### Phase 3: Prove β'+γ' ≤ 1 (~50 lines)

Key lemma needed: for z ∈ P and edge i (CCW oriented),
cross2(z - v_i, v_{i+1} - v_i) ≤ 0.

Proof: z = Σ coeffs_k · v_k (from hull). By linearity of cross2:
cross2(z - v_i, v_{i+1} - v_i) = Σ coeffs_k · cross2(v_k - v_i, v_{i+1} - v_i)

For k = i: term is 0.
For k = i+1: cross2(v_{i+1} - v_i, v_{i+1} - v_i) = 0.
For k ≠ i, i+1: cross2(v_k - v_i, v_{i+1} - v_i) ≤ 0.

The last inequality means: all other vertices are on the "inside" of edge i.
This follows from convexity + CCW. Specifically:
cross2(v_k - v_i, v_{i+1} - v_i) = cross2(v_k - c + c - v_i, v_{i+1} - v_i)
= cross2(v_k - c, v_{i+1} - v_i) + cross2(c - v_i, v_{i+1} - v_i)

Hmm, this doesn't simplify cleanly. Alternative approach:

For a CCW convex polygon, the half-plane {z : cross2(z - v_i, v_{i+1} - v_i) ≤ 0}
contains P. This is because P = intersection of half-planes (convex polygon property).

Proving this formally: show each vertex v_k satisfies the inequality,
then extend to convex combinations.

For each vertex v_k: need cross2(v_k - v_i, v_{i+1} - v_i) ≤ 0.
This is a consequence of the non-adjacent edges disjoint condition + CCW.

SIMPLEST APPROACH: sorry this for now with a clear sub-lemma, then prove the
sub-lemma separately. Actually no — the plan says NO SORRYS.

Let me think harder. We have CCW: D_j > 0 for all j. And we have the
non-adjacent edges disjoint condition. From these, can we derive that all
vertices are on the correct side of each edge?

For a convex polygon with CCW ordering: yes. The proof:
- The polygon P is the intersection of n half-planes H_i
- H_i = {z : cross2(z - v_i, v_{i+1} - v_i) ≤ 0} (for CCW)
- Every vertex v_k ∈ P ⊆ H_i
- So cross2(v_k - v_i, v_{i+1} - v_i) ≤ 0

But we defined P as the CONVEX HULL, not as intersection of half-planes.
Showing convex hull ⊆ intersection of half-planes requires the half-plane
characterization of convex polygons.

Alternative: use the hno_extra condition. For adjacent edges (i, i+1):
the non-adjacent condition doesn't apply. But for non-adjacent edges,
the disjoint interior condition gives geometric constraints.

Actually, the SIMPLEST proof for β'+γ' ≤ 1:

β' + γ' = (cross2(z-c, v_{i+1}-c) + cross2(v_i-c, z-c)) / D
         = cross2(z-c, v_{i+1}-v_i) / D    (by bilinearity)

And D = cross2(v_i-c, v_{i+1}-c) = cross2(v_i-c, v_{i+1}-v_i)  (since cross2(v_i-c, v_i-c) = 0)

So β'+γ' = cross2(z-c, v_{i+1}-v_i) / cross2(v_i-c, v_{i+1}-v_i)
         = 1 + cross2(z-v_i, v_{i+1}-v_i) / D

For β'+γ' ≤ 1: need cross2(z-v_i, v_{i+1}-v_i) / D ≤ 0.
Since D > 0: need cross2(z-v_i, v_{i+1}-v_i) ≤ 0.

For z ∈ P: z = Σ c_k v_k with c_k ≥ 0, Σc_k = 1.
cross2(z-v_i, v_{i+1}-v_i) = Σ c_k cross2(v_k-v_i, v_{i+1}-v_i)

Term k=i: 0. Term k=i+1: cross2(v_{i+1}-v_i, v_{i+1}-v_i) = 0.
Other terms: need cross2(v_k-v_i, v_{i+1}-v_i) ≤ 0 for all k ≠ i, i+1.

So the core sub-lemma is:
```
∀k<n. k ≠ i → k ≠ (i+1) mod n → cross2(v_k - v_i, v_{i+1} - v_i) ≤ 0
```

This says: all other vertices are on the "right side" of each directed edge.
For a CCW convex polygon, this is equivalent to convexity.

Proof of the sub-lemma from the CCW + convex hull conditions:
Need to show this from the definition. The definition gives:
- P = conv hull of vertices (from hull condition)
- CCW: cross2(v_j - c, v_{j+1} - c) > 0 for all j
- Non-adjacent edges: disjoint interiors

This requires a non-trivial geometric argument (maybe 40-60 lines).

### Phase 4: Define explicit local maps ψ_i (~30 lines)

For each cone C_i = {z | in_cone i z}:
```
definition ψi where
  "ψi i z = (let β = cross2(z-c, v_{i+1}-c) / D_i;
                  γ = cross2(v_i-c, z-c) / D_i;
                  α = 1 - β - γ;
                  w = (β * qx i + γ * qx((i+1) mod n),
                       β * qy i + γ * qy((i+1) mod n));
                  r = sqrt(fst w ^ 2 + snd w ^ 2)
              in if r = 0 then (0,0) else ((1-α) * fst w / r, (1-α) * snd w / r))"
```

This is explicit — no SOME. The Cramer coordinates are polynomial in z.
The normalization is continuous where r ≠ 0.

### Phase 5: Prove local continuity (~40 lines)

Each ψ_i is continuous on C_i:
- β_i, γ_i, α_i are polynomial in z (continuous)
- w is polynomial in β, γ (continuous)
- r = sqrt(...) is continuous
- r > 0 on C_i \ {centroid} (because β, γ not both 0 when z ≠ c,
  and the regular polygon vertices have r > 0 for non-zero combinations)
- At centroid: α = 1, β = γ = 0, ψ_i(c) = (0,0). 
  Continuity at c: |ψ_i(z)| = (1-α) = β+γ → 0 as z → c. ✓
- Division by r: continuous where r > 0, and ψ_i → 0 as z → c.

Need to handle the r = 0 case: prove r > 0 for z ≠ c in C_i.
This requires: β qx_i + γ qx_{i+1} and β qy_i + γ qy_{i+1} not both 0
when β+γ > 0. Since q_i, q_{i+1} are regular polygon vertices subtending
angle 2π/n < 2π/3 < π (for n ≥ 3), any positive combination is nonzero.
This needs a trigonometric lemma (~15 lines).

### Phase 6: Prove overlap agreement (~40 lines)

For z ∈ C_i ∩ C_j: ψ_i(z) = ψ_j(z).

The overlap C_i ∩ C_j is either empty (non-adjacent) or a shared edge/vertex.

For adjacent cones (j = i+1 mod n): the shared edge is the ray from c through v_{i+1}.
On this edge: β_i = 0 (in C_i: z = α·c + γ·v_{i+1}, β=0 means no v_i component).
And in C_j: γ_j = 0 (z = α·c + β_j·v_{i+1}, γ_j=0 means no v_{i+2} component).
Both give ψ(z) = (1-α) · normalize(q_{i+1}) = (1-α) · q_{i+1} (since q_{i+1} is on S¹).

So ψ_i(z) = ψ_j(z) on shared edges. ~20-30 lines.

For the centroid c: all ψ_i(c) = (0,0). ✓

### Phase 7: Define global ψ and prove continuity (~30 lines)

```
definition ψ where "ψ z = ψi (SOME i. i < n ∧ z ∈ C i) z"
```

Since overlap agreement holds, the choice of i doesn't matter.
Continuity follows from the pasting lemma for finite closed covers:
- C_i are closed (compact convex hull of 3 points in R²)
- ∪ C_i = P (from hP_cones)
- ψ_i continuous on each C_i
- ψ_i agree on overlaps
→ ψ continuous on P.

Need: a pasting lemma. Check if `closed_cover_continuous` or similar exists.
If not, prove it (~20 lines: for finite closed cover, preimage of open
= union of preimages in each piece, each open by local continuity).

### Phase 8: Target-sector lemmas (~80 lines)

For the regular n-gon on S¹ with vertices q_i = (cos 2πi/n, sin 2πi/n):

**Lemma 8a**: For u ∈ [0,1] and i < n with n ≥ 3:
  norm((1-u)·q_i + u·q_{i+1}) > 0.
Proof: the chord from q_i to q_{i+1} doesn't pass through origin
because the angle subtended is 2π/n < π. (~15 lines, using
cos/sin bounds and the angle condition.)

**Lemma 8b**: normalize((1-u)·q_i + u·q_{i+1}) ∈ S¹. Trivial from norm.

**Lemma 8c**: The map u ↦ normalize((1-u)·q_i + u·q_{i+1}) is injective on [0,1].
Proof: the angle is monotone. If two parameters give the same
normalized point, they're on the same ray from origin through the chord,
which intersects the chord at most once. (~20 lines.)

**Lemma 8d**: ∪_{i<n} normalize(segment(q_i, q_{i+1})) = S¹.
Proof: any point on S¹ has angle θ ∈ [0, 2π). It falls in some
sector [2πi/n, 2π(i+1)/n]. The normalized chord from q_i to q_{i+1}
covers this arc. (~20 lines.)

**Lemma 8e**: For i ≠ j (non-adjacent), the normalized segments are disjoint
except possibly at endpoints. (~15 lines.)

### Phase 9: Prove ψ surjective (~40 lines)

For any point y ∈ B²:
- If y = (0,0): ψ(c) = (0,0). ✓
- If y ≠ 0: y = r · u where u ∈ S¹, 0 < r ≤ 1.
  By Lemma 8d: u = normalize((1-u0)·q_i + u0·q_{i+1}) for some i, u0.
  Set β = r·(1-u0), γ = r·u0, α = 1-r.
  Then z = α·c + β·v_i + γ·v_{i+1} ∈ C_i (all coords ≥ 0, sum = 1).
  Check: ψ_i(z) = (1-α) · normalize(β·q_i + γ·q_{i+1})
               = r · normalize((1-u0)·q_i + u0·q_{i+1})
               = r · u = y. ✓

### Phase 10: Prove ψ injective (~50 lines)

If ψ(z₁) = ψ(z₂):
- Case both = (0,0): z₁ = z₂ = c (only centroid maps to origin).
- Case ψ(z₁) = r·u with r > 0, u ∈ S¹:
  - |ψ(z₁)| = 1 - α₁ = r, so α₁ = 1-r.
  - Similarly α₂ = 1-r.
  - normalize(β₁·q_{i₁} + γ₁·q_{i₁+1}) = normalize(β₂·q_{i₂} + γ₂·q_{i₂+1})
  - Both normalized points equal u ∈ S¹.
  - By Lemma 8c+8e: i₁ = i₂ and the boundary parameters match.
  - So β₁/(β₁+γ₁) = β₂/(β₂+γ₂), and β₁+γ₁ = β₂+γ₂ = r.
  - Hence β₁ = β₂, γ₁ = γ₂.
  - With α₁ = α₂, β₁ = β₂, γ₁ = γ₂: z₁ = z₂. ✓

### Phase 11: Prove ψ(BdP) = S¹ (~25 lines)

For x ∈ BdP: x is on edge i at parameter u, so x = (1-u)·v_i + u·v_{i+1}.
In cone C_i: α = 0, β = 1-u, γ = u.
ψ_i(x) = 1 · normalize((1-u)·q_i + u·q_{i+1}) ∈ S¹.

Conversely: any u ∈ S¹ is in the image (by target-sector Lemma 8d, with r=1).

So ψ(BdP) = S¹. ✓

## Total estimated effort

| Phase | Lines | Status |
|-------|-------|--------|
| 1. Recover infrastructure | 0 new (copy ~600 lines) | Copy from bck0107 |
| 2. D > 0 from CCW | 5 | New |
| 3. β'+γ' ≤ 1 | 50 | New |
| 4. Local maps ψ_i | 30 | New |
| 5. Local continuity | 40 | New |
| 6. Overlap agreement | 40 | New |
| 7. Global ψ + pasting | 30 | New |
| 8. Target-sector lemmas | 80 | New |
| 9. Surjectivity | 40 | New |
| 10. Injectivity | 50 | New |
| 11. ψ(BdP) = S¹ | 25 | New |
| **Total new proof** | **~390** | |

## Risk mitigation

**Highest risk**: Phase 3 (β'+γ' ≤ 1) and Phase 8 (target-sector lemmas).

For Phase 3: if the convex hull → half-plane argument is too hard,
fall back to: add "all vertices on correct side of each edge" as a
SEPARATE assumption (like CCW). This is ugly but would unblock everything.

For Phase 8: if trigonometric injectivity is hard, use the angle-based
boundary map h(u) = (cos(2π(i+u)/n), sin(2π(i+u)/n)) instead of
normalized interpolation. This avoids the normalization altogether
but requires different algebra for the cone_map definition.

## Constraints

- NO sorrys left in the final proof
- Follow the book's radial/cone construction exactly
- Use pasting lemma for continuity (not global SOME continuity)
- Define local maps with explicit Cramer coordinates (no SOME for coordinates)
- Prove target-sector coverage of S¹ rigorously
