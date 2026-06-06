# AlgTop.thy Sorry Audit (2026-06-06, session 1355)

## Summary: ~12 executable sorrys (4 non-surface [1 orphan], 8 surface)

Build: `/project/bin/isabelle build -D .` — ~22s, clean. 10942 lines.

## Non-surface proof chain: PROVED modulo 3 sorrys

```
sc_graph_no_cycle [SORRY: topological bridge]
  + forest_euler_formula [2 SORRYS: leaf from acyclicity + leaf induction]
  → tree_leaf_existence_bridge [PROVED: case split on acyclicity]
    → tree_euler_from_leaf [PROVED]
      → tree_euler_from_sc [PROVED via graph_coherent_any_decomposition]
        → finite_tree_has_leaf [PROVED]
          → tree_euler_and_leaf_combined [PROVED]
            → tree_euler_number_one [PROVED]
              → covering_graph_pi1_rank [PROVED]
                → Theorem_85_3_Schreier_index [PROVED]
```

## Non-surface sorrys (4):
| # | Lemma | Type | Description |
|---|-------|------|-------------|
| 1 | sc_graph_no_cycle | TOPOLOGICAL | Cycle in SC graph → False (Munkres 84.7) |
| 2 | forest_euler_formula (leaf) | COMBINATORIAL | Acyclic → leaf exists (walk+pigeonhole) |
| 3 | forest_euler_formula (induction) | COMBINATORIAL | Leaf induction: V ≥ E+1 |
| 4 | two_arcs_same_endpoints_sc_false | ORPHAN | SCC construction (unused) |

**tree_leaf_existence_bridge** proof (no sorry!):
- Case A (acyclic): forest_euler gives V ≥ E+1; degree counting gives E ≥ V → contradiction
- Case B (has cycle): sc_graph_no_cycle → contradiction
- All degree counting, vertex finiteness, etc. FULLY PROVED

## Surface sorrys (8): Theorems 75.4, 76, 77.5, 78.1, 78.2

## Key infrastructure PROVED:
- graph_coherent_any_decomposition: coherent topology from graph conditions
- graph_euler_invariance: V-E invariant under decomposition change
- arc_merge_at_endpoint: two arcs sharing 1 endpoint → arc (mostly proved)
- double_counting_sum: degree sum = 2E
- All covering infrastructure, §64-§85
