# AlgTop.thy Sorry Audit (2026-06-06, session 1354)

## Summary: 10 executable sorrys (2 non-surface [1 orphan], 8 surface)

Build: `/project/bin/isabelle build -D .` — ~21s, clean. 10672 lines.

## tree_euler_from_sc: PROVED modulo single sorry

**tree_euler_from_sc** proof structure:
1. `graph_coherent_any_decomposition` [PROVED] — derives coherent topology
2. `tree_leaf_existence_bridge` [1 SORRY] — leaf existence (Munkres 84.2)
3. `tree_euler_from_leaf` [PROVED] — V = E + 1 by induction
4. Instantiation [PROVED]

**tree_leaf_existence_bridge** proof structure:
1. No-leaf assumption → all degrees ≥ 2 [PROVED]
2. Each arc has 2 endpoints [PROVED]  
3. Vertex set finite and non-empty [PROVED]
4. Walk + CREP + Theorem 84.7 → False [SORRY]

## Non-surface sorrys (2):
| # | Line | Lemma | Status |
|---|------|-------|--------|
| 1 | ~L4663 | tree_leaf_existence_bridge | **BLOCKING** — topological bridge |
| 2 | ~L4693 | two_arcs_same_endpoints_sc_false | ORPHAN — not used |

The topological bridge (Munkres 84.2 + 84.7): walk+pigeonhole gives CREP in the graph.
CREP corresponds to non-trivial π₁ element (Theorem 84.7). SC → π₁ = 1. Contradiction.

## Surface sorrys (8): Theorems 75.4, 76, 77.5, 78.1, 78.2

## Proof chain (all PROVED modulo tree_leaf_existence_bridge):
```
graph_coherent_any_decomposition [PROVED]
  + tree_leaf_existence_bridge [1 SORRY]
  + tree_euler_from_leaf [PROVED]
  → tree_euler_from_sc [PROVED]
    → finite_tree_has_leaf [PROVED]
      → tree_euler_and_leaf_combined [PROVED]
        → tree_euler_number_one [PROVED]
          → covering_graph_pi1_rank [PROVED]
            → Theorem_85_3_Schreier_index [PROVED]
```
