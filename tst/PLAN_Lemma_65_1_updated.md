# PLAN: Prove Lemma 65.1 — Updated 2026-05-11

## Goal

Close the 2 sorrys in `Lemma_65_1` (hj_surj, hj_inj).

## Approach: Follow algtop.tex EXACTLY

The textbook constructs SPECIFIC paths α, β along C edges. The cached
`Lemma_65_1_K4_subgraph` uses ARBITRARY paths (from path-connectedness),
so its loop does NOT lie in C. We must NOT rely on the cached proof for
the isomorphism — we construct α, β ourselves.

## Textbook proof (Munkres p.393), step by step:

### Already proved:
- C ⊆ X = S²-{p,q} (hC_sub_X) ✓
- j_* is a homomorphism (hj_hom) ✓
- p ≠ q (hp_ne_q) ✓
- C is a simple closed curve (hC_scc) ✓
- π₁(X) is infinite cyclic (hX_inf_cyc) ✓

### Step 1: Construct D₁, D₂, U, V

D₁ = arc from p to q through a₃, a₂ (sub-arcs of e13, e23, e24)
D₂ = arc from q to p through a₄, a₁ (sub-arcs of e24, e41, e13)

More precisely, using arc_split_at_given_point:
- Split e13 at p: get arc from a1 to p and arc from p to a3
- Split e24 at q: get arc from a2 to q and arc from q to a4
- D₁ = (p-to-a3 piece of e13) ∪ e23 ∪ (a2-to-q piece of e24)
  Concatenate three arcs sharing endpoints: p→a3, a3→a2 (=e23), a2→q
- D₂ = (q-to-a4 piece of e24) ∪ e41 ∪ (a1-to-p piece of e13)
  Concatenate: q→a4, a4→a1 (=e41), a1→p

U = S²-D₁, V = S²-D₂, X = U ∪ V

### Step 2: Construct specific α, β along C edges

Pick x ∈ interior of e12, y ∈ interior of e34.
(These exist because arcs have more than 2 points.)

α = path from x to y traversing e12 (x→a1) then e41 (a1→a4) then e34 (a4→y)
  = concatenation of three sub-arc paths, all in C
  α lies in U because α avoids D₁ (which goes through a3, a2)

β = path from y to x traversing e34 (y→a3) then e23 (a3→a2) then e12 (a2→x)
  = concatenation of three sub-arc paths, all in C
  β lies in V because β avoids D₂ (which goes through a4, a1)

KEY: α*β lies in C (traverses e12∪e41∪e34∪e23 = C)

### Step 3: Apply Theorem 63.1

U∩V = S²-D where D = D₁∪D₂ is a simple closed curve.
By JCT: U∩V has two components A, B.
x ∈ A, y ∈ B (by part (a) of Lemma 65.1, applied to the "other" K4 cycle).
α is a path in U from x to y, β is a path in V from y to x.
By Theorem_63_1_loop_nontrivial: α*β is nontrivial in X.

### Step 4: α*β is a generator of π₁(X)

"Because π₁(X) is infinite cyclic, α*β represents a generator."

The textbook asserts this without detailed proof. The formal argument:
π₁(X) ≅ ℤ (hX_inf_cyc). [α*β] ≠ 0. Say [α*β] = gen^n (n ≠ 0).
If |n| > 1: decompose gen as γ*δ (γ in U, δ in V, through a'∈A).
Then (α*β)^1 ≃ (γ*δ)^n. By Theorem_63_1_c_subgroups_trivial: 1 = 0. ⊥.
Hence n = ±1 and [α*β] is a generator.

NOTE: This step requires showing gen decomposes as γ*δ through a'∈A,
which needs a path-decomposition argument. This can be sorry'd as
a single clean sorry if needed.

### Step 5: Surjectivity

α*β ∈ C and [α*β] generates π₁(X).
[α*β]_C is an element of π₁(C, x).
j_*([α*β]_C) = [α*β]_X = generator of π₁(X).
Since [α*β]_C generates π₁(C) ≅ ℤ (it traverses C once),
j_* maps generator to generator, hence surjective.

### Step 6: Injectivity

Surjective hom ℤ → ℤ is injective (maps ±1 to ±1, hence bijective).

## Available infrastructure:
- arc_split_at_given_point: split arc at interior point
- arcs_concatenation_is_arc: two arcs sharing endpoint form arc
- Theorem_63_1_loop_nontrivial: nontriviality from 63.1 setup
- Theorem_63_1_c_subgroups_trivial: independence of 63.1 pairs
- pi1_S2_minus_two_points_infinite_cyclic: π₁(X) ≅ ℤ
- Theorem_54_5_iso: π₁(S¹) ≅ ℤ
- Lemma_64_3_K4_four_components: K4 separation
- subspace_inclusion_induced_hom: inclusion induces hom
- inclusion_induced_class: j_*([g]_C) = [g]_X

## Implementation order:
1. Construct D₁, D₂ using arc_split_at_given_point + arcs_concatenation
2. Construct α, β as concatenated sub-arc paths
3. Show α ∈ U, β ∈ V, α*β ∈ C
4. Show U∩V has two components with x, y separated
5. Apply Theorem_63_1 → nontriviality
6. Apply generator argument (possibly sorry the decomposition step)
7. Derive surjectivity from α*β ∈ C + generator
8. Derive injectivity from surjectivity + ℤ→ℤ
