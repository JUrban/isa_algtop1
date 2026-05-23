## Verdict

The revised plan is **much closer to the right path** than the first one, but against the current `main/tst/AlgTop.thy` it is still **partly stale and too optimistic**.

The current repo is not in the state described by the earlier plan: `polygon_homeomorphic_to_disk_with_boundary` is **not present** in the current raw file, and a search for that name returns no match. The current file has only the bare theorem `polygon_homeomorphic_to_disk`, whose conclusion is just an existential homeomorphism `P → B²`. ([GitHub][1]) ([GitHub][1])

Also, the current code already contains a cone-style construction: it defines `cone_map`, `in_cone`, proves/attempts `hP_cones`, and defines `ψ` using `SOME` over a cone index and barycentric coordinates. ([GitHub][1]) ([GitHub][1]) So “recovering the old cone decomposition” is directionally right, but it is not simply a matter of pasting in a missing block before a current boundary theorem; the current file has a compressed/reworked version of that construction already.

---

## Current repo-state mismatches

The revised plan says the old `bck0107` version had five remaining sorries: `D > 0`, `β'+γ' ≤ 1`, continuity, surjectivity, and injectivity.  In the current `AlgTop.thy`, the polygon theorem has at least these proof gaps inside or immediately after the cone construction:

1. A degenerate `D = 0` branch in `hP_cones` is still a `sorry`. ([GitHub][1])
2. `hD_pos: ?D > 0` is still a `sorry`. ([GitHub][1])
3. `hsum_le: β' + γ' ≤ 1` is still a `sorry`. ([GitHub][1])
4. `h_cont`, `h_surj`, and `h_inj` are still `sorry`s. ([GitHub][1])

So the current theorem is not down to the old five gaps; it has the same core gaps plus the degenerate branch. If you prove `D > 0` globally before the case split, the `D = 0` branch should disappear rather than be proved.

The downstream `scheme_quotient_CW_data` also still has independent gaps: `hX_haus`, `hBdP_pc`, the interior homeomorphism, and `h \` S¹ ⊆ A`are still`sorry`s. :contentReference[oaicite:9]{index=9} :contentReference[oaicite:10]{index=10} :contentReference[oaicite:11]{index=11} This matters because a bare `polygon_homeomorphic_to_disk` theorem is insufficient for the downstream interior/boundary obligations.

---

## On the CCW claim

The plan’s strongest claim is that the vertex-order blocker is solved by a cached CCW condition:

```isabelle
∀i<n. cross2 (v_i - c) (v_{i+1} - c) > 0
```

It also correctly notices a problem: the old standalone lemma extracts only from `top1_is_polygonal_region_on`, whereas the claimed CCW condition is said to live in `top1_quotient_of_scheme_on`. 

Against the current `AlgTop.thy`, I would treat the CCW issue as **not yet solved for `polygon_homeomorphic_to_disk`**. The theorem’s assumptions are only:

```isabelle
top1_is_polygonal_region_on P n
n ≥ 3
```

and the proof extracts `vx vy` from `top1_is_polygonal_region_on_def` without binding any `hccw` assumption. ([GitHub][1]) The current file also has no textual occurrence of `CCW`, and `hD_pos` remains a `sorry`. ([GitHub][1]) ([GitHub][1])

The right fix is probably **not** to silently strengthen `top1_is_polygonal_region_on`. That predicate appears to be used as a general convex-hull/polygonal-region predicate. Strengthening it with a specific cyclic orientation condition may break existing uses or make the predicate semantically odd.

I would instead introduce a stronger, witness-based lemma:

```isabelle
lemma ordered_polygon_homeomorphic_to_disk:
  assumes poly: "top1_is_polygonal_region_on P n"
  assumes n3: "n ≥ 3"
  assumes verts: "... vx vy are the chosen cyclic vertices for P ..."
  assumes ccw: "∀i<n. cross2 (vx i - cx, vy i - cy)
                         (vx ((i+1) mod n) - cx,
                          vy ((i+1) mod n) - cy) > 0"
  shows "∃ψ. top1_homeomorphism_on P ?TP top1_B2 top1_B2_topology ψ"
```

Then derive the bare theorem separately only if you can prove/order the vertices. For the scheme quotient case, use the ordered lemma directly because the scheme already supplies an edge order.

---

## The `SOME` strategy is workable, but only in a narrow form

The revised plan now agrees not to use a global `THE sector`; that is good. It suggests keeping `SOME` but proving the chosen value is unique. 

That can work, but the uniqueness must be about the **output value**, not the cone index. Cone index is not unique on overlaps: the centroid and rays through vertices belong to multiple cones. The current `ψ` definition chooses:

```isabelle
i = SOME i. i < n ∧ in_cone i z
β = SOME β. ...
γ = SOME γ. ...
α = 1 - β - γ
```

and then applies `cone_map`. ([GitHub][1])

For continuity by pasting, you need lemmas of this shape:

```isabelle
C i = {z. in_cone i z}

ψi i z = cone_map i (αi z) (βi z) (γi z)

z ∈ C i ⟹ ψ z = ψi i z
z ∈ C i ⟹ z ∈ C j ⟹ ψi i z = ψi j z
```

The first lemma is the hard one if `ψ` is still defined using `SOME i`; it requires proving that every possible chosen cone gives the same `cone_map` value. That is possible, but it is exactly the gluing proof.

My recommendation remains: define explicit local maps first, then define global `ψ` by unique local value:

```isabelle
definition ψ where
  "ψ z = (SOME y. ∃i<n. z ∈ C i ∧ y = ψi i z)"
```

This uses `SOME` only after proving uniqueness of `y`. It avoids trying to reason about the continuity of the selected index.

---

## Important correction: the normalized cone map is not affine

The plan’s Step 7 says:

> “Since cone_map is affine (hence injective) on each cone with D > 0...”

That is false for the current `cone_map`. It divides by

```isabelle
sqrt (fst w ^ 2 + snd w ^ 2)
```

so it is a radial normalization, not an affine map. ([GitHub][1]) The current file itself has a comment noticing that the affine map only reaches the inscribed polygon and that the normalized formula is the alternative that reaches disk sectors. ([GitHub][1])

This changes the injectivity proof. You should not prove “affine bijection on each cone.” Instead prove:

```isabelle
ψi i z = r *\<^sub>R normalize (boundary_combo_i z)
```

where

```isabelle
r = βi z + γi z = 1 - αi z
```

Then injectivity on a cone follows from:

1. norm of the image gives `r`;
2. normalized direction gives the boundary parameter `γ / (β + γ)`;
3. `α = 1 - r`, `β = r * (1-u)`, `γ = r * u`;
4. barycentric coordinates recover `z`.

This is not huge, but it is not a one-line affine-injectivity argument.

---

## Surjectivity: simplify the construction

The revised plan proposes solving surjectivity by choosing an angle and “inverting the normalization,” with a formula involving a `normalized_factor`.  I would avoid that formulation.

For the current `cone_map`, the image radius is `1 - α`, not the Euclidean norm of `β q_i + γ q_{i+1}`. So for a target point `y = r * u`, with `u ∈ S¹`, the clean construction is:

1. find `i` and `u0 ∈ [0,1]` such that
   `u = normalize ((1-u0) q_i + u0 q_{i+1})`;
2. set
   `α = 1 - r`,
   `β = r * (1-u0)`,
   `γ = r * u0`;
3. use
   `z = α*c + β*v_i + γ*v_{i+1}`.

Then `α+β+γ=1`, all coordinates are nonnegative, and `cone_map i α β γ = r*u`.

This shifts the work into a reusable **target-sector lemma**:

```isabelle
⋃ i<n. normalize ` segment(q_i, q_{i+1}) = top1_S1
```

with uniqueness/disjointness up to endpoints.

---

## Boundary correspondence cannot be black-boxed

The plan’s “two-lemma approach” says:

1. old lemma: bare homeomorphism `P → B²`;
2. new lemma: adds boundary correspondence, perhaps using the old one. 

The plan immediately notes the problem: the boundary proof needs to know how `ψ` is constructed. That diagnosis is right. A black-box homeomorphism from `P` to `B²` does not tell you that polygon boundary maps to `S¹`.

The current downstream code confirms this. `scheme_quotient_CW_data` obtains `ψ` from the bare `polygon_homeomorphic_to_disk`, defines `h = q ∘ inv_into P ψ`, and then leaves the interior homeomorphism and `h \` S¹ ⊆ A`as`sorry`s. ([GitHub][1]) ([GitHub][1])

So the useful theorem should return the boundary behavior directly:

```isabelle
∃ψ.
  top1_homeomorphism_on P ?TP top1_B2 top1_B2_topology ψ
∧ ψ ` BdP = top1_S1
∧ ψ ` (P - BdP) = top1_B2 - top1_S1
∧ inj_on ψ P
```

Even better, prove the pointwise equivalence:

```isabelle
z ∈ P ⟹ (z ∈ BdP ⟷ ψ z ∈ top1_S1)
```

That is exactly what `scheme_quotient_CW_data` needs for the `inv_into` arguments.

---

## Revised implementation plan I would use

### Step 1: Split the theorem

Create a witness-based ordered-polygon theorem first. Do not try to prove everything from bare `top1_is_polygonal_region_on P n` until the vertex-order story is settled.

```isabelle
lemma ordered_polygon_homeomorphic_to_disk_with_boundary:
  fixes vx vy :: "nat ⇒ real"
  assumes n3: "n ≥ 3"
  assumes poly_hull: "P = ..."
  assumes verts_in_P: "∀i<n. (vx i, vy i) ∈ P"
  assumes ccw: "∀i<n. cross2 (...) (...) > 0"
  assumes BdP_def: "BdP = ..."
  shows "∃ψ. ..."
```

Then later wrap it into the old theorem if needed.

### Step 2: Prove `D_i > 0` once, before Cramer

With `ccw`, do:

```isabelle
have D_pos: "i < n ⟹ D i > 0" for i
  using ccw ...
```

Then delete the `D = 0` branch. The current branch exists only because the proof has not established orientation early enough. ([GitHub][1])

### Step 3: Replace existential barycentric coordinates by explicit functions

Define:

```isabelle
D i = cross2 (v i - c) (v (Suc i mod n) - c)

βi i z = cross2 (z - c) (v (Suc i mod n) - c) / D i
γi i z = cross2 (v i - c) (z - c) / D i
αi i z = 1 - βi i z - γi i z
```

Then define:

```isabelle
C i = {z. αi i z ≥ 0 ∧ βi i z ≥ 0 ∧ γi i z ≥ 0}
```

or equivalently as a convex-hull/cone set. This makes continuity local and computational.

### Step 4: Finish the real geometry gap: `β+γ ≤ 1`

The plan estimates 30–50 lines for this.  That is plausible only if you already have a lemma saying every vertex lies on the same side of every oriented edge. Otherwise this is a nontrivial convex-polygon lemma.

The lemma you want is:

```isabelle
i < n ⟹ z ∈ P ⟹
cross2 (z - v i) (v ((i+1) mod n) - v i) ≤ 0
```

assuming the orientation convention used in the file. Then derive:

```isabelle
βi i z + γi i z ≤ 1
```

The proof by expanding `z` as a convex combination of vertices is sound, but only after proving the side-of-edge inequality for every vertex.

### Step 5: Define local maps and glue

```isabelle
ψi i z =
  let β = βi i z;
      γ = γi i z;
      α = 1 - β - γ;
      w = β *\<^sub>R q i + γ *\<^sub>R q ((i+1) mod n);
      ρ = norm w
  in if ρ = 0 then 0 else (1 - α) *\<^sub>R (w /\<^sub>R ρ)
```

Then prove:

```isabelle
continuous_on (C i) (ψi i)
z ∈ C i ∩ C j ⟹ ψi i z = ψi j z
P = ⋃ i<n. C i
```

Use a finite closed-cover pasting lemma to get global continuity.

### Step 6: Prove target-sector lemmas once

You need these for both surjectivity and injectivity:

```isabelle
norm ((1-u) *\<^sub>R q i + u *\<^sub>R q ((i+1) mod n)) ≠ 0
  for u ∈ [0,1]

normalize ` segment(q i, q (i+1)) = circular_arc_i

⋃ i<n. circular_arc_i = top1_S1

circular_arc_i ∩ circular_arc_j
  is empty or endpoint-only, depending on i,j
```

This is where a lot of the actual formal work lives. The plan recognizes the angle calculations as medium risk, which is right. 

### Step 7: Prove boundary and interior equivalence directly

For `z ∈ C i`:

```isabelle
z ∈ BdP     ⟹ αi i z = 0
z ∈ P-BdP   ⟹ αi i z > 0
norm (ψ z) = 1 - αi i z
```

Then:

```isabelle
z ∈ BdP ⟹ ψ z ∈ top1_S1
z ∈ P - BdP ⟹ ψ z ∈ top1_B2 - top1_S1
```

This gives the downstream `inv_into` facts needed by `scheme_quotient_CW_data`.

---

## Effort estimate

The revised plan’s **~225 new lines** is possible only under optimistic assumptions: the old 1156-line block imports cleanly, the CCW witness is already in the exact theorem context, and target-sector lemmas already exist. 

Against the current raw file, I would estimate:

* **Bare `polygon_homeomorphic_to_disk` only:** 200–400 lines if you add an ordered witness assumption and avoid boundary.
* **Boundary-preserving version usable by `scheme_quotient_CW_data`:** 400–800 lines.
* **If `top1_is_polygonal_region_on` does not provide cyclic vertices and you need to derive/reorder them:** likely more than that.

The biggest hidden costs are not Cramer algebra; that is mostly present. The costs are ordered-edge half-space facts, normalized target-sector coverage/injectivity, overlap agreement, and the pointwise boundary/interior equivalence.

---

## Bottom line

I would adopt the revised plan’s core direction—recover/use the cone decomposition, prove local maps, use finite closed-cover gluing—but I would change four things:

1. **Do not rely on the current bare theorem assumptions for CCW.** Add an ordered-polygon witness theorem or a separate ordered predicate.
2. **Prove `D_i > 0` before the Cramer case split**, then remove the `D = 0` branch.
3. **Do not describe `cone_map` as affine.** It is normalized; injectivity and surjectivity need radius-plus-direction proofs.
4. **Do not try to black-box boundary correspondence from the bare homeomorphism.** The boundary-preserving theorem must expose the constructed `ψ` and prove `ψ \` BdP = S¹`and preferably`z ∈ BdP ↔ ψ z ∈ S¹`.

So the revised plan is substantially better, but the current repo state suggests it is still underestimating the geometry needed to make the normalized cone map and boundary behavior formal.

[1]: https://github.com/JUrban/isa_algtop1/raw/refs/heads/main/tst/AlgTop.thy "raw.githubusercontent.com"
