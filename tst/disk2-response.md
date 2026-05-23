## Verdict

The updated plan is **mathematically much better** than the previous versions: it now uses explicit local cone maps, avoids `SOME` for barycentric coordinates, uses pasting for continuity, and correctly treats normalized target sectors as the core of surjectivity/injectivity. That is the right architecture. 

But against the **current raw URL you gave**, the plan still has a major repo-state mismatch: I do **not** see `polygon_homeomorphic_to_disk_with_boundary` in `main/tst/AlgTop.thy`, and I also found no occurrences of `h_bd` or `pdist`. The current raw file has only `polygon_homeomorphic_to_disk`, starting around line 211, and `scheme_quotient_CW_data` still calls that bare theorem rather than a boundary-preserving theorem. ([GitHub][1])

So my assessment is: **the plan is a good design for the theorem you want, but it is not yet a faithful patch plan for the current public `main` file.** It either assumes a local/unpushed version, or the theorem needs to be added/reintroduced first.

---

## What the current raw file actually has

The current `polygon_homeomorphic_to_disk` already contains much of the “recover from bck0107” cone infrastructure: it extracts vertices, defines centroid data, defines `BdP`, defines regular target vertices `qx/qy`, defines a normalized `cone_map`, defines `in_cone`, and proves/attempts `hP_cones`. ([GitHub][1])

It still has more than the four sorries listed in the plan. Inside the cone decomposition, the current file has a `D = 0` branch left as `sorry`, then `hD_pos: ?D > 0` as `sorry`, then `hsum_le: β' + γ' ≤ 1` as `sorry`; after defining `ψ` with `SOME`, it has `h_cont`, `h_surj`, and `h_inj` as `sorry`. ([GitHub][1])

The downstream `scheme_quotient_CW_data` still obtains only a bare homeomorphism from `polygon_homeomorphic_to_disk`, then has separate proof gaps for Hausdorffness, boundary path-connectedness, the interior homeomorphism, and `h \` S¹ ⊆ A`. ([GitHub][1])

That means the plan’s statement that “the 19 proved downstream steps remain untouched” is probably true only for a local version containing `polygon_homeomorphic_to_disk_with_boundary`; it is not true of the current raw `main` file.

---

## What is genuinely improved in this plan

The strongest improvement is that it now proposes explicit local maps

```isabelle
ψi i z = ...
```

using Cramer coordinates, rather than trying to prove continuity of a global `SOME` or `THE` sector choice. That is the right formalization shape. 

The surjectivity construction is also now clean: for target `y = r · u`, choose a target arc parameter `u0`, set

```text
α = 1 - r
β = r * (1 - u0)
γ = r * u0
z = α·c + β·v_i + γ·v_{i+1}
```

and then check `ψ_i z = y`. This avoids the earlier confusing “normalized_factor” inversion. 

The plan also correctly identifies the two true hard spots: the half-plane/edge-side lemma needed for `β' + γ' ≤ 1`, and the target-sector lemmas for normalized chords on `S¹`. 

---

## Main remaining problem: CCW is still not visible in current `main`

The plan’s Phase 2 says `D_i > 0` is a 5-line proof from a CCW assumption. That is correct **if** the theorem context really contains

```isabelle
∀i<n. cross2 (v_i - c) (v_{i+1} - c) > 0
```

But in the current raw `main` file, I found no `hccw` and no textual occurrence of `CCW`. The current theorem `polygon_homeomorphic_to_disk` assumes only `top1_is_polygonal_region_on P n` and `n ≥ 3`; it extracts `vx/vy` from `top1_is_polygonal_region_on_def`, not from an ordered-polygon predicate. ([GitHub][1])

So Phase 2 is conditionally fine, but it is not currently applicable to the public theorem. I would add a separate ordered theorem rather than silently strengthen `top1_is_polygonal_region_on`:

```isabelle
lemma ordered_polygon_homeomorphic_to_disk_with_boundary:
  assumes poly: "top1_is_polygonal_region_on P n"
  assumes n3: "n ≥ 3"
  assumes verts: "... vx/vy are the chosen boundary vertices ..."
  assumes ccw: "∀i<n. cross2 (v i - c) (v ((i+1) mod n) - c) > 0"
  assumes edge_side:
    "∀i<n. ∀k<n.
       cross2 (v k - v i) (v ((i+1) mod n) - v i) ≤ 0"
  shows "∃ψ. ... ∧ ψ ` BdP = top1_S1 ∧ ..."
```

Then use that theorem in the scheme setting, where the ordered boundary vertices are meaningful.

---

## Phase 3 is still under-specified

The plan correctly reduces `β' + γ' ≤ 1` to the side-of-edge fact

```isabelle
cross2 (z - v_i) (v_{i+1} - v_i) ≤ 0
```

for `z ∈ P`, and then to the vertex inequalities

```isabelle
cross2 (v_k - v_i) (v_{i+1} - v_i) ≤ 0
```

for all vertices `v_k`. 

But the plan also admits the key issue: `P` is defined as a convex hull, not as an intersection of edge half-planes, so the half-plane characterization is not immediately available. 

I would not leave this as “~50 lines” unless the repo already has a reusable convex polygon half-plane lemma. The practical fix is to add the edge-side condition as a theorem assumption for the ordered-polygon lemma. Then `β' + γ' ≤ 1` really does become a short convex-combination proof. Without that assumption, this phase can easily become one of the longest parts of the patch.

---

## Phase 6 overlap agreement needs one correction

The plan says non-adjacent cone overlaps are empty, with centroid handled separately. Strictly, **every cone contains the centroid**, so non-adjacent overlaps are not empty. In a well-ordered strictly convex fan, the expected result is:

```text
C_i ∩ C_j =
  shared radial edge, if i and j are adjacent;
  {c}, if i and j are non-adjacent;
  C_i, if i = j.
```

That classification is important for the gluing proof and for injectivity. The plan’s adjacent-edge argument is right, but the overlap lemma should be stated with the centroid case built in, not as an afterthought. 

A robust overlap theorem would be:

```isabelle
lemma cone_overlap_agree:
  assumes "i < n" "j < n" "z ∈ C i" "z ∈ C j"
  shows "ψi i z = ψi j z"
```

Then prove it by cases internally. This avoids exposing too much overlap classification to the rest of the proof.

---

## Injectivity needs endpoint cases

The Phase 10 injectivity sketch is nearly right, but this step is too strong:

> “By Lemma 8c+8e: i₁ = i₂ and the boundary parameters match.”

At target arc endpoints, adjacent arcs overlap at the same regular vertex. So the sector index need not be literally equal. For example, the same target direction `q_i` may be represented as the endpoint of arc `i-1` or the start of arc `i`.

The correct conclusion is not “same index,” but:

```text
the same target boundary point is represented;
if the indices differ, the representations are adjacent endpoint representations;
the corresponding source point is the same polygon vertex;
therefore z₁ = z₂ once the common radius is fixed.
```

This is a standard formal trap. The plan’s proof will work, but only if the target-sector uniqueness lemma is stated “unique up to adjacent endpoints,” not as plain index uniqueness. 

---

## Continuity estimate is optimistic

The local continuity proof is conceptually right, but “~40 lines” is optimistic in Isabelle. The function

```isabelle
if r = 0 then (0,0) else (1-α) *\<^sub>R (w / r)
```

is continuous away from `r = 0` by composition, but continuity at the centroid needs a separate bound. The plan suggests using

```text
|ψ_i(z)| = 1 - α = β + γ → 0
```

which is the right idea. 

The useful lemma to prove once is:

```isabelle
lemma cone_map_continuous_on_Ci:
  assumes "D i > 0"
  assumes "target_chord_nonzero i"
  shows "continuous_on (C i) (ψi i)"
```

Inside that lemma, split `{c}` and `C_i - {c}`, or prove an `eventually`/epsilon bound at `c`. Do not expect `continuous_intros` to finish the centroid case automatically.

---

## Target-sector lemmas are the other big cost

The plan’s Phase 8 is exactly the right lemma package, but 80 lines is probably low. Proving normalized chord coverage/injectivity over all of `S¹` can be surprisingly expensive because it mixes modular arithmetic, trigonometry, endpoint cases, and normalization. 

A useful algebraic lemma for nonzero chords is:

```text
‖(1-u)q_i + u q_{i+1}‖²
= (1-u)² + u² + 2u(1-u) cos(2π/n)
```

For `n ≥ 3`, the angle gap is at most `2π/3 < π`, so the chord does not pass through the origin. That handles nonzero denominators. But coverage and injectivity still need either angle-range lemmas or a geometric “ray intersects chord once” lemma.

The plan’s fallback—using an angle-based boundary map

```isabelle
h_i u = (cos (2*pi*(real i + u)/real n),
         sin (2*pi*(real i + u)/real n))
```

—is worth considering earlier, not only as a fallback. It shifts the hard work from normalized-chord algebra to angle-interval arithmetic, which may be easier to organize.

---

## Boundary image is not enough for downstream unless you prove the equivalence

The plan proves `ψ(BdP) = S¹`. That is necessary, but downstream interior claims usually need the pointwise equivalence:

```isabelle
z ∈ P ⟹ (z ∈ BdP ⟷ ψ z ∈ top1_S1)
```

or at least:

```isabelle
ψ ` (P - BdP) = top1_B2 - top1_S1
```

The plan’s Phase 11 gives the forward and surjective boundary image argument.  But for `scheme_quotient_CW_data`, especially with `inv_into P ψ`, you will need the reverse direction: if `z ∈ S¹`, then `inv_into P ψ z ∈ BdP`. This follows from injectivity plus `ψ ` BdP = S¹`, but it should be packaged as a lemma.

I would make the theorem return:

```isabelle
∃ψ.
  top1_homeomorphism_on P TP top1_B2 top1_B2_topology ψ
∧ ψ ` BdP = top1_S1
∧ ψ ` (P - BdP) = top1_B2 - top1_S1
∧ (∀z∈P. z ∈ BdP ⟷ ψ z ∈ top1_S1)
```

That will make the CW-data proof much easier.

---

## Recommended adjustment to the plan

I would revise the implementation plan as follows:

1. **First reconcile repo state.** Either push/add `polygon_homeomorphic_to_disk_with_boundary`, or patch the current `polygon_homeomorphic_to_disk` and then add a separate stronger theorem. The theorem described in the plan is not present in the current raw URL. ([GitHub][1])

2. **Introduce an ordered-polygon theorem.** Do not try to prove `D_i > 0` from bare `top1_is_polygonal_region_on`; current `main` has no visible CCW assumption. ([GitHub][1])

3. **Add or prove an edge-side assumption.** This is the cleanest way to finish `β' + γ' ≤ 1`. Treat it as part of the ordered-convex-polygon data.

4. **Define local maps `ψi` and global `ψ` via unique local value.** Avoid `ψ z = ψi (SOME i ...) z` if possible; if you keep it, prove a restriction lemma `z ∈ C i ⟹ ψ z = ψi i z`.

5. **Package target-sector facts with endpoint-aware uniqueness.** Do not state arc injectivity as “same index”; state it as uniqueness modulo adjacent endpoints.

6. **Return boundary/interior equivalences, not only boundary image.** This is what the downstream CW-data proof actually wants.

---

## Effort estimate

The plan’s new estimate of **~390 lines** is much more realistic than the earlier 200-line estimate.  I would still adjust it upward depending on the starting point:

If the local version really already has `polygon_homeomorphic_to_disk_with_boundary` with CCW and ordered vertices, then **390–600 new proof lines** is plausible.

Against the current raw `main` file, I would expect **600–1200 lines including integration**, because the theorem is not present, CCW is not visible, the current theorem still has the `D = 0` branch and `hD_pos/hsum_le` gaps, and downstream still calls the bare theorem. ([GitHub][1])

## Bottom line

I would proceed with this plan’s architecture, but not exactly as written. The right next move is to add an **ordered, boundary-preserving polygon-to-disk theorem** with explicit local cone maps and endpoint-aware gluing. The current public `main` file is not yet in the state the plan assumes, so the first implementation task is to align the theorem statement and assumptions before working on the four advertised proof obligations.

[1]: https://github.com/JUrban/isa_algtop1/raw/refs/heads/main/tst/AlgTop.thy "raw.githubusercontent.com"
