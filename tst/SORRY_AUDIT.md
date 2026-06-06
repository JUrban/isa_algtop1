# AlgTop.thy Sorry Audit (2026-06-06, session 1359)

## Summary: 12 executable sorrys (1 blocking non-surface + 3 orphan + 8 surface)

Build: `/project/bin/isabelle build -D .` — ~21s, clean.

## 🎉 Walk proof COMPLETE — acyclic case ZERO SORRY!

The walk construction in tree_leaf_existence_bridge is FULLY PROVED:
✅ Walk definition (rec_nat + SOME)
✅ Walk properties (hwalk_props: full induction)
✅ Helper lemmas (hnext_arc, hother_endpt, hwalk_shared, hnonback)
✅ Pigeonhole (card_inj_on_le)
✅ Shortest revisit (LEAST)
✅ Cycle length ≥ 2
✅ hws_nth (nth_map + nth_upt)
✅ hws_adj (consecutive arcs share vertex)
✅ hws_sub (arcs ⊆ 𝒜)
✅ hws_dist (arc distinctness — Case 1 + Case 2 boundary)
✅ hv_distinct (vertex distinctness from shortest revisit)
✅ hkl_ne_1 (|k-l| ≠ 1 from hnonback)
✅ hacyclic application

## ONLY 1 BLOCKING NON-SURFACE SORRY:

| Lemma | Type | Description |
|-------|------|-------------|
| sc_graph_no_cycle (L4580) | TOPOLOGICAL | Cycle in SC graph → False (Munkres 84.7) |

**If this one sorry is proved, the ENTIRE non-surface chain completes:**
```
sc_graph_no_cycle [1 SORRY]
  → tree_leaf_existence_bridge [PROVED: acyclic case ZERO SORRY + cycle case via sc_graph_no_cycle]
    → tree_euler_from_leaf [PROVED]
      → tree_euler_from_sc [PROVED]
        → finite_tree_has_leaf [PROVED]
          → tree_euler_and_leaf_combined [PROVED]
            → tree_euler_number_one [PROVED]
              → covering_graph_pi1_rank [PROVED]
                → Theorem_85_3_Schreier_index [PROVED]
```

## Orphan sorrys (3): forest_euler_formula (2) + two_arcs_same_endpoints_sc_false (1)
## Surface sorrys (8): Theorems 75.4, 76, 77.5, 78.1, 78.2
