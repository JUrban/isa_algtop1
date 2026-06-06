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

## Current Sorry Count: ~16 executable (8 blocking + 8 surface)

### Non-surface blocking sorrys (8, all in sc_graph_no_cycle):
These block the ENTIRE chain from tree_euler_from_sc through Theorem_85_3_Schreier_index.

| # | Description | Type |
|---|-------------|------|
| 1 | A1 merge (iterative arc_merge_at_endpoint) | SCC construction |
| 2 | A1 ∩ A2 = {a_start, a_end} | SCC construction |
| 3 | A2 endpoints | SCC construction |
| 4 | f: S¹ → T continuous | SCC construction |
| 5 | f injective | SCC construction |
| 6 | card ≠ 2 in walk adjacency | Walk proof |
| 7 | C retract of T | Retraction |

### Surface classification sorrys (8): Theorems 75.4, 76, 77.5, 78.1, 78.2

### Orphan sorrys (4): forest_euler_formula (2) + helpers (2)

## FULLY PROVED (modulo sc_graph_no_cycle):

### Walk proof: ZERO SORRY
- Walk definition, properties, unfold lemmas
- Pigeonhole (vertex revisit), shortest revisit (LEAST)
- Arc adjacency, surjectivity, distinctness, hacyclic application

### Non-surface proof chain:
```
sc_graph_no_cycle [8 sorrys]
  → tree_leaf_existence_bridge [PROVED]
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
- arc_merge_at_endpoint: two arcs sharing 1 endpoint → arc
- All covering infrastructure, §64, §67-§73, §79-§85

## Build Command

```bash
cd /project/tst && /project/bin/isabelle build -D .
```

## Files to Ignore

- `archive/` — old backups and stale files.
- `bck*`, `*_old.thy`, `*_bak.thy` — stale backups.
- `CHANGES*` files — incremental changelog snapshots.
