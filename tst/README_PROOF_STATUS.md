# Proof Status: Munkres Algebraic Topology Formalization

## Authoritative Sessions and Files

| Session | Directory | Key File | Status |
|---------|-----------|----------|--------|
| Top0 | `i/` | Top1_Ch2..Ch9_13.thy | Chapters 2-8 (general topology). Cached. |
| AlgTopBase0 | `b0/` | AlgTop_JCT_Base0.thy | JCT infrastructure (Thm 58.7, etc). Cached. |
| AlgTopBase | `b/` | AlgTop_JCT_Base.thy | JCT + homeomorphism helpers. Cached. |
| AlgTop0 | `a0/` | AlgTop0.thy | §51-§63 foundations. 1 proof gap (pi1_iso_Z, proved in AlgTopC). |
| AlgTopC | `ac/` | AlgTopCached.thy | Cached infrastructure. Oracle-clean. |
| AlgIsoFixedBase | `fib/` | AlgIsoFixedBase.thy | §65 helpers (K4, SCC_pi1, generation). Oracle-clean. |
| AlgIsoFixed | `fi/` | AlgIsoFixed.thy | **Thm 58.7, Lemma 65.1, Thm 65.2. Oracle-clean.** |
| AlgTop | `.` | AlgTop.thy | §64, §67-§85. Has proof gaps (see below). |
| K5 | `k5/` | K5_nonplanar.thy | Thm 64.4 (K5). 2 proof gaps. |

## Session Dependency Chain

```
Top0 → AlgTopBase0 → AlgTopBase → AlgTop0 → AlgTopC
  → AlgIsoFixedBase → AlgIsoFixed → AlgTop
  → K5
```

## Current Sorry Count: ~15 executable (7 blocking + 8 surface)

### Non-surface blocking sorrys:

| # | Location | Description | Status |
|---|----------|-------------|--------|
| 1 | sc_graph_no_cycle | A1 merge (iterative arc_merge_at_endpoint) | Sorry |
| 2 | sc_graph_no_cycle | A1 ∩ A2 = {a_start, a_end} | Sorry (depends on #1) |
| 3 | sc_graph_no_cycle | A2 endpoints = {a_start, a_end} | Sorry (depends on #1) |
| 4 | sc_graph_no_cycle | C retract of T | Sorry (hardest) |
| 5 | tree_leaf_existence_bridge | j-i=2 subdivision case | Sorry |

### PROVED in recent sessions (formerly sorry):
- ✅ sc_graph_no_cycle f continuity (via loop_factors_through_S1)
- ✅ sc_graph_no_cycle f injectivity (semicircle case analysis)
- ✅ two_arcs_same_endpoints_sc_false: ZERO SORRY (full SCC via loop factoring)
- ✅ Walk proof: hws_adj_card, hws_vdist, vertex distinctness all PROVED

### Surface classification sorrys (8): Theorems 75.4, 76, 77.5, 78.1, 78.2

### Orphan sorrys (2): forest_euler_formula (walk+pigeonhole, leaf induction)

## FULLY PROVED (modulo sc_graph_no_cycle):

### Walk proof in tree_leaf_existence_bridge: j-i≥3 case ZERO SORRY
- Walk definition, properties, unfold lemmas
- Pigeonhole (vertex revisit), shortest revisit (LEAST)
- Arc adjacency (hws_adj), card=1 (hws_adj_card), distinctness (hws_dist)
- Shared vertex distinctness (hws_vdist), hacyclic application

### Non-surface proof chain:
```
sc_graph_no_cycle [4 sorrys] + walk j-i=2 [1 sorry]
  → tree_leaf_existence_bridge [PROVED modulo above]
    → tree_euler_from_leaf [PROVED]
      → tree_euler_from_sc [PROVED]
        → finite_tree_has_leaf [PROVED]
          → tree_euler_and_leaf_combined [PROVED]
            → tree_euler_number_one [PROVED]
              → covering_graph_pi1_rank [PROVED]
                → Theorem_85_3_Schreier_index [PROVED]
```

### Key infrastructure PROVED:
- graph_euler_invariance: V-E invariant under decomposition change
- graph_coherent_any_decomposition: coherent topology from graph conditions
- arc_merge_at_endpoint: two arcs sharing 1 endpoint → arc (ZERO SORRY)
- two_arcs_same_endpoints_sc_false: 2 arcs same endpoints → False (ZERO SORRY)
- loop_factors_through_S1: loop factoring for SCC construction
- All covering infrastructure, §64, §67-§73, §79-§85

## Build Command

```bash
cd /project/tst && /project/bin/isabelle build -D .
```

## Files to Ignore

- `archive/` — old backups and stale files.
- `bck*`, `*_old.thy`, `*_bak.thy` — stale backups.
- `CHANGES*` files — incremental changelog snapshots.
