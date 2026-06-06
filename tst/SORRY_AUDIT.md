# AlgTop.thy Sorry Audit (2026-06-06, final)

## Summary: 9 executable sorrys (1 non-surface, 8 surface)

Build: `/project/bin/isabelle build -D .` — ~30s, clean. 10077 lines. 2165 theorem entries.

## FULLY PROVED (ZERO SORRY) — Complete Euler invariance chain:
1. **graph_euler_invariance** — V-E invariant under decomposition change
2. **graph_iterated_subdivision_exists** — iterated arc subdivision (induction on card P)
3. **graph_same_vertices_same_arcs** — same vertex set → same arcs (both directions)
4. **graph_arc_containment_via_open_interior** — A ⊆ B via connectedness of (0,1)
5. **graph_coherent_any_decomposition** — coherent topology for any finite decomposition
6. **graph_arc_interior_open** — arc interiors open in coherent topology
7. **graph_subdivision_preserves_euler** — single subdivision preserves V-E
8. **closed_set_first_entry** — boundary point in connected space
9. **All covering infrastructure** (𝒜_L conditions, multiplicity, etc.)
10. **All §64, §67-§73, §79-§85 infrastructure**

## Non-surface sorrys (1):
| # | Line | Lemma | Description |
|---|------|-------|-------------|
| 1 | L2676 | finite_tree_has_leaf | SC + all vertices degree≥2 → False |

This is the SC → no-CREP topological bridge. Blocks tree Euler (V=E+1),
which blocks covering_graph_pi1_rank → Theorem_85_3_Schreier_index.
Equivalent to: "in an SC graph, V = E + 1 for any decomposition."
Deep circular dependency: V = E + 1 needs leaf existence needs V = E + 1.

## Surface sorrys (8): L9785-L10073 (Theorems 75.4, 76, 77.5, 78.1, 78.2)

## Complete proof chain (modulo finite_tree_has_leaf):
```
graph_euler_invariance [PROVED]
  → covering_graph_pi1_rank [modulo tree Euler]
    → Theorem_85_3_Schreier_index [modulo tree Euler]

tree_euler_number_one [modulo finite_tree_has_leaf]
  → covering_graph_pi1_rank

finite_tree_has_leaf [SORRY: topological bridge SC → no CREP]
```
