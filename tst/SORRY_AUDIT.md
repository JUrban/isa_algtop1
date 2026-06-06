# AlgTop.thy Sorry Audit (2026-06-06, session 1362)

## Summary: ~16 executable sorrys (7 blocking in sc_graph_no_cycle + 1 orphan A2_ep + 3 orphan formula/helper + 8 surface)

Build: clean. ~21s.

## sc_graph_no_cycle: SCC + retraction decomposed

**PROVED in SCC construction:**
✅ A1 ∪ A2 = C (set(butlast ws) ∪ {last ws} = set ws)
✅ hA orientation (doubleton_eq_iff + reversal)
✅ hB orientation (doubleton_eq_iff + reversal, modulo A2 endpoint sorry)
✅ f boundary values (f(1,0) = a_start, f(-1,0) = a_end)
✅ SCC application (from continuity + injectivity + surjectivity)
✅ scc_in_sc_false application (from SC + SCC + retract)

**Remaining sorrys in sc_graph_no_cycle (7):**
| # | Description | Difficulty |
|---|-------------|-----------|
| 1 | A1 merge (iterative arc_merge_at_endpoint) | Medium |
| 2 | A1 ∩ A2 = {a_start, a_end} | Medium |
| 3 | A2 endpoints = {a_end, a_start} | Medium |
| 4 | f continuity (pasting lemma on semicircles) | Medium |
| 5 | f injectivity (sector analysis) | Medium |
| 6 | f surjectivity (semicircle parametrization) | Medium |
| 7 | C retract of T (tree-branch collapse) | Hard |

## Proof chain (all PROVED modulo sc_graph_no_cycle):
```
sc_graph_no_cycle [7 sorrys]
  → tree_leaf_existence_bridge [PROVED: walk ZERO SORRY + cycle case]
    → tree_euler_from_leaf [PROVED]
      → tree_euler_from_sc [PROVED]
        → ... → Theorem_85_3_Schreier_index [PROVED]
```

## Orphan sorrys (4): forest_euler_formula (2) + two_arcs_helper (1) + A2_ep (1)
## Surface sorrys (8): Theorems 75.4, 76, 77.5, 78.1, 78.2
