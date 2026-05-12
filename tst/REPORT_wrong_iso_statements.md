# Report: Fixed Isomorphism Statements — Status Update

## Summary

`fi/AlgIsoFixed.thy` contains correctly-stated versions of theorems that had
too-weak "abstract isomorphism" conclusions. The file proves that the SPECIFIC
induced map is the isomorphism, not just that some isomorphism exists.

## Key Results PROVED (sorry-free)

- **Theorem_58_7_fixed**: Homotopy equivalence f: X→Y induces π₁ isomorphism
  f_*: π₁(X,x0) → π₁(Y,f(x0)). Full bijectivity: injectivity via g∘f≃id
  basepoint change, surjectivity via f∘g≃id + double basepoint change.

- **Theorem_58_2_inclusion_iso_fixed**: The inclusion j: S1 → R²-{0} induces
  a π₁ isomorphism. Proof: S1 is a deformation retract of R²-{0}
  (via H(x,t)=(1-t)x+t·x/|x|), giving homotopy equivalence (j,r), then
  apply Theorem_58_7_fixed.

- **Lemma_65_1_fixed**: The inclusion j: C → S²-{p,q} induces a group
  isomorphism of π₁ at ANY basepoint c0 ∈ C. Proof: surjectivity at
  K4-generator basepoint x, SCC path-connectivity to transfer to c0,
  surj_hom_infinite_cyclic_inj for injectivity.

- **Lemma_65_1_fixed_exists_basepoint**: Same as above at an existential basepoint.

- **surj_hom_infinite_cyclic_inj**, **K4_generator_loop_in_C**,
  **K4_nonadjacent_edges_different_components**, **K4_cycle_is_SCC**,
  **SCC_pi1_iso_Z**, **Theorem_63_1_b_generation**: All sorry-free.

## Remaining Sorry (1)

1. **Theorem_65_2_fixed** — General SCC version of Lemma 65.1. Given any SCC C
   on S² with p,q in different components of S²-C, the inclusion C → S²-{p,q}
   induces a π₁ isomorphism. Needs: constructing a K4 subgraph from a general
   SCC (Munkres Theorem 65.2, Steps 1-4: take 4 points on C, connect
   non-adjacent pairs through the two components of S²-C).

## File Statistics

- 6499 lines
- 1 sorry
- 20+ sorry-free lemmas
- Builds in ~37s (clean) or 5s (cached)
