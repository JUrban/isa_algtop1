# Plan 10: Close the 75.3 chain — witnessed finite wedge theorem

## What the expert found wrong

1. **`wedge_pi1_generated_by_loop_classes` is FALSE as stated.**
   The lemma takes arbitrary `loop_class` without connecting it to the actual
   circles. Counterexample: identity class + trivial H. Must be scrapped.

2. **Hopfian approach is wrong.** Not the book proof. Expert rejected it 5+ times.
   Must use SvK + Theorem 69.2 generator tracking (the book proof).

3. **Hidden dependency on Theorem_71_3 infinite case sorry.**
   Must use finite-only `Theorem_71_1_wedge_of_circles_finite` from cache.

## What to do (following Munkres 71.1 exactly)

### Step 1: Prove `finite_wedge_pi1_free_with_chosen_loops`

This is the WITNESSED version of Theorem 71.1. Statement:

```isabelle
lemma finite_wedge_pi1_free_with_chosen_loops:
  fixes X :: "'a set" and TX and J :: "nat set" and p :: 'a
    and C :: "nat ⇒ 'a set" and g :: "nat ⇒ real × real ⇒ 'a"
  assumes "finite J"
  assumes "∀j∈J. C j ⊆ X ∧ p ∈ C j"
  assumes "(⋃j∈J. C j) = X"
  assumes "∀i∈J. ∀j∈J. i ≠ j → C i ∩ C j = {p}"
  assumes "∀j∈J. top1_homeomorphism_on top1_S1 top1_S1_topology
      (C j) (subspace_topology X TX (C j)) (g j)"
  assumes "∀j∈J. g j (1,0) = p"
  assumes coherent topology condition
  defines "loop_class j = {ℓ. top1_loop_equiv_on X TX p
      (λt. g j (cos(2*pi*t), sin(2*pi*t))) ℓ}"
  shows "∃(F::int set) mul e invg (η::nat ⇒ int) Φ.
      top1_is_free_group_full_on F mul e invg η J
    ∧ top1_group_iso_on F mul π₁(X,p) Φ
    ∧ (∀j∈J. Φ (η j) = loop_class j)"
```

### Step 2: Proof by induction on |J| (following Munkres 71.1)

**Base (|J| = 0):** X = {p}, π₁ trivial, free on empty set.

**Base (|J| = 1):** X = C(j₀) ≅ S¹. π₁(X) ≅ Z. The loop f₁ generates.
Use the existing `Theorem_54_5_S1_fundamental_group_Z` or equivalent.

**Inductive step (|J| → |J|+1):** Following Munkres exactly:
1. Pick j₀ ∈ J. Set J' = J \ {j₀}.
2. Choose q_j ∈ C_j \ {p} for each j.
3. Set W_j = C_j \ {q_j}. Define:
   U = C(j₀) ∪ ⋃_{j∈J'} W_j
   V = W(j₀) ∪ ⋃_{j∈J'} C_j
4. U ∩ V = ⋃_j W_j is simply connected (deformation retract to p).
   **USE: S1_minus_point_simply_connected (proved in AlgTopSvK)
   + the deformation retraction construction from AlgTopCached:33225-33690.**
5. By SvK (Corollary_70_3): π₁(X) ≅ FP (free product of π₁(U) and π₁(V)).
   **The SvK iso IS the compatible one (from the universal property).
   This is where svk_generation_sc helps for the generation half.**
6. S₁ is deformation retract of U → π₁(U) ≅ Z with generator [f₁].
   S₂∪...∪S_n is deformation retract of V → by IH, π₁(V) free on [f₂],...,[f_n].
7. By Theorem_69_2 (fully proved, WITH generator tracking):
   FP is free on [f₁],...,[f_n] with explicit ιS12 correspondence.
8. Compose the isomorphisms to get Φ with Φ(η j) = loop_class j.

### Step 3: Replace `wedge_circle_loops_free_generators` and `wedge_pi1_generated`

In `Theorem_74_2`, replace the current construction with:
- Extract circle data from the wedge predicate
- Apply `finite_wedge_pi1_free_with_chosen_loops`
- Get F, Φ with iso + generator correspondence
- h_bij is IMMEDIATE from iso (no Hopfian needed)

### Step 4: Remove Theorem_71_3 dependency

Use `Theorem_71_1_wedge_of_circles_finite` (cached, finite only, no sorry)
instead of `Theorem_71_3_wedge_of_circles_general` (infinite case sorry).

## What this plan does NOT do

- Does NOT use Hopfian property (follows the book instead)
- Does NOT invent new proof strategies
- Does NOT modify cached sessions
- DOES follow Munkres 71.1 step by step
- DOES use existing proved tools: svk_generation_sc, S1_minus_point_simply_connected,
  Theorem_69_2, Corollary_70_3, Theorem_58_3

## Key tools already available

- `Theorem_69_2` (AlgTopCached): free product of free groups, WITH generator tracking
- `Corollary_70_3_simply_connected_intersection_param` (AlgTopCached): SvK for SC intersection
- `Theorem_58_3` (AlgTop_JCT_Base0): deformation retract gives π₁ iso
- `svk_generation_sc` (AlgTopSvK): generation half of SvK
- `S1_minus_point_simply_connected` (AlgTopSvK): arcs are simply connected
- `Theorem_71_1_wedge_of_circles_finite` (AlgTopCached): finite wedge π₁ free (abstract)

## Estimated effort

The inductive proof is ~200-300 lines. The main work is:
- Deformation retraction construction at each step (~50 lines, following cache:33225)
- Composing isomorphisms through SvK + Theorem_69_2 (~50 lines)
- Tracking generator correspondence through compositions (~50 lines)
- The rest is boilerplate (openness, path-connectedness — mostly proved)
