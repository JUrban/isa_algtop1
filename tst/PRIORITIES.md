# Priorities for AlgTop Jordan Curve Theorem

## Status: 144 sorries, builds in ~15s, 10K lines

## COMPLETE Infrastructure (Zero Sorry):

### S² Topology
- stereographic_proj_homeomorphism (S²-{N} ≅ R²)
- householder_S2_homeo (Householder homeo S²-{b} → S²-{N})
- S2_minus_point_simply_connected (all b ∈ S²)
- S2_minus_point_homeo_R2 (S²-{b} ≅ R²)
- S2_minus_two_points_not_simply_connected
- R2_simply_connected, R2_minus_point_not_sc

### Homeomorphism Infrastructure
- homeomorphism_{inverse, comp, restrict_point}
- homeomorphism_{preserves, reflects}_simply_connected

### Nulhomotopy Infrastructure
- map_into_S2_minus_point_nulhomotopic
- nulhomotopic_transfer
- Lemma_61_2_nulhomotopy (uses above)

### Theorem 61.3 Partial
- hA1_closed, hA2_closed (arcs closed in Hausdorff S²)
- hU_open, hV_open (complements of closed arcs open)
- hC_sub (simple closed curve subset)

## Remaining Jordan Chain Sorries:

### Shallow (topology infrastructure):
- map_into_R2_nulhomotopic: F jointly continuous (1 sorry)
- Arc decomposition of simple closed curve (S¹ → 2 arcs)
- S²-C nonempty when C is simple closed curve
- ¬separates → path-connected complement (connected + locally path-connected)
- "arc is compact" pattern already proved; can be reused

### Deep (fundamental group theory):
- **Theorem 59.1** (loop decomposition via Lebesgue number): 2 sorries
- **Theorem 63.1** (loop nontrivial via covering space): 3 sorries
- **Theorem 61.3** π₁(X) trivial: uses 59.1 + 61.2
- **Theorem 63.2** arc no separation: uses 63.1
- **Theorem 63.3** general non-separation: uses 63.1
- **Theorem 63.4** Jordan Curve Theorem: uses 61.3 + 63.2 + 63.5

## FTA — COMPLETE! ZERO SORRIES!
All FTA chain verified by thm_oracles, cached in Top0.
