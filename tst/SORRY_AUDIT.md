# AlgTop.thy Sorry Audit (2026-06-06, session 1357)

## Summary: ~12 executable sorrys (4 non-surface [3 orphan], 8 surface)

Build: `/project/bin/isabelle build -D .` — ~22s, clean.

## Non-surface proof chain: PROVED modulo 2 sorrys

**Walk construction NEARLY COMPLETE:**
✅ Walk definition (rec_nat + SOME)
✅ Walk properties hwalk_props (full induction)
✅ Walk unfold lemmas, hnext_arc, hother_endpt, hwalk_shared
✅ Pigeonhole (vertex revisit via card_inj_on_le)
✅ Shortest revisit (LEAST on nat set)
✅ j-i ≥ 2 (other_endpt)
✅ hws_nth (nth_map + nth_upt)  
✅ hws_adj (consecutive arcs share vertex, full case analysis)
✅ hws_sub (arcs ⊆ 𝒜)
✅ Vertex distinctness hv_distinct (from shortest revisit)
✅ hacyclic application
❌ Arc distinctness hws_dist (endpoint pair analysis — 1 micro-sorry)

## Non-surface blocking sorrys (2):
| # | Lemma | Type | Description |
|---|-------|------|-------------|
| 1 | sc_graph_no_cycle | TOPOLOGICAL | Cycle in SC graph → False |
| 2 | hws_dist (in tree_leaf_existence_bridge) | COMBINATORIAL | Same arc → same endpoint pair → vertex equality |

## Orphan sorrys (3):
- forest_euler_formula (2 sorrys, not in main chain)
- two_arcs_same_endpoints_sc_false (1 sorry, not used)

## Surface sorrys (8): Theorems 75.4, 76, 77.5, 78.1, 78.2

## Complete proof chain:
```
sc_graph_no_cycle [SORRY: cycle case]
  + walk (1 micro-sorry: arc distinctness)
  → tree_leaf_existence_bridge [case split proved]
    → tree_euler_from_leaf [PROVED]
      → tree_euler_from_sc [PROVED]
        → ... → Theorem_85_3_Schreier_index [PROVED]
```
