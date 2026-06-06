# AlgTop.thy Sorry Audit (2026-06-06, session 1358)

## Summary: ~12 executable sorrys (4 non-surface [3 orphan], 8 surface)

Build: `/project/bin/isabelle build -D .` — ~21s, clean. 11523 lines.

## Walk construction: NEARLY COMPLETE (1 micro-sorry)

✅ Walk definition, properties, unfold lemmas
✅ hnext_arc, hother_endpt, hwalk_shared
✅ Pigeonhole (vertex revisit via card_inj_on_le)
✅ Shortest revisit (LEAST on nat set)
✅ j-i ≥ 2, hws_nth, hws_adj, hws_sub
✅ Vertex distinctness hv_distinct
✅ hnonback (non-backtracking)
✅ hkl_ne_1 (|k-l| ≠ 1 from hnonback)
✅ Arc distinctness Case 1 (same arrived-at vertices)
✅ hacyclic application
❌ Arc distinctness Case 2 boundary (1 micro-sorry: nat arithmetic)

## Non-surface blocking sorrys (2):
| # | Lemma | Type | Description |
|---|-------|------|-------------|
| 1 | sc_graph_no_cycle | TOPOLOGICAL | Cycle in SC graph → False |
| 2 | hws_dist Case 2 | COMBINATORIAL | Boundary nat arithmetic in cross-matching |

## Orphan sorrys (3): forest_euler_formula (2) + two_arcs_same_endpoints_sc_false (1)
## Surface sorrys (8): Theorems 75.4, 76, 77.5, 78.1, 78.2

## Proof chain:
```
sc_graph_no_cycle [SORRY: cycle case]
  + walk (1 micro-sorry: Case 2 boundary arithmetic)
  → tree_leaf_existence_bridge [case split proved]
    → tree_euler_from_leaf [PROVED]
      → tree_euler_from_sc [PROVED]
        → ... → Theorem_85_3_Schreier_index [PROVED]
```
