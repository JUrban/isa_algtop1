# AlgTop.thy Sorry Audit (2026-06-06, session 1356)

## Summary: ~13 executable sorrys (5 non-surface [3 orphan], 8 surface)

Build: `/project/bin/isabelle build -D .` — ~20s, clean. 11173 lines.

## Non-surface proof chain: PROVED modulo 3 sorrys

The walk construction is now MOSTLY proved:

**PROVED in tree_leaf_existence_bridge:**
- No-leaf → all degrees ≥ 2 (hshared)
- Each arc has 2 endpoints (h2ep)  
- Vertex set finite and non-empty (hV_fin, x0)
- hshared_arc: at every vertex, there's another arc (step function)
- hnext_arc: SOME gives valid next arc
- hother_endpt: SOME gives the other endpoint
- hwalk_props: walk stays in V and 𝒜 (full induction proof)
- hwalk_suc_fst/snd: walk unfold lemmas
- hwalk_shared: walk vertex is in both current and next arc
- Pigeonhole: walk must revisit a vertex (card_inj_on_le)
- j-i ≥ 2: cycle has ≥ 2 arcs (other_endpt gives different vertex)
- hacyclic application: blast instantiates universal

**Remaining sorrys in walk proof (2 micro-sorrys):**
- hws_adj: consecutive arcs share vertex (conceptually proved via hwalk_shared, needs nth_map_upt)
- hws_dist: arcs are distinct (needs shortest revisit argument)

## Non-surface sorrys:
| # | Line | Lemma | Status |
|---|------|-------|--------|  
| 1 | L4580 | sc_graph_no_cycle | BLOCKING: topological bridge (cycle case) |
| 2 | ~L5060 | tree_leaf_existence_bridge | BLOCKING: hws_adj (nth_map lemma) |
| 3 | ~L5062 | tree_leaf_existence_bridge | BLOCKING: hws_dist (shortest revisit) |
| 4 | L4731 | forest_euler_formula | ORPHAN: not in main chain |
| 5 | L4738 | forest_euler_formula | ORPHAN: not in main chain |

Plus two_arcs_same_endpoints_sc_false (orphan).

## Surface sorrys (8): Theorems 75.4, 76, 77.5, 78.1, 78.2

## Complete proof chain:
```
sc_graph_no_cycle [SORRY: cycle case]
  + walk construction [2 micro-sorrys: adj + distinct]  
  → tree_leaf_existence_bridge [case split proved]
    → tree_euler_from_leaf [PROVED]
      → tree_euler_from_sc [PROVED]
        → ... → Theorem_85_3_Schreier_index [PROVED]
```
