# Proof Status: Munkres Algebraic Topology Formalization

## Current Sorry Count: 21 word-matches (~13 executable)

### Non-surface blocking sorrys:

| # | Location | Description | Status |
|---|----------|-------------|--------|
| 1 | sc_graph_no_cycle | Retraction (general case with non-cycle arcs) | **THE blocker** |
| 2 | tree_leaf_existence_bridge | j-i=2 subdivision case | Delegates to sc_graph_no_cycle |
| 3 | forest_euler_formula | Walk + pigeonhole | Orphan |
| 4 | forest_euler_formula | Leaf induction | Orphan |

### FULLY PROVED in sc_graph_no_cycle:
- ✅ shared_v extraction + distinctness
- ✅ harc_ep (each arc's endpoints = adjacent shared vertices)
- ✅ hdisjoint_non_adj (non-adjacent arcs disjoint)
- ✅ A1 merge (iterative arc_merge_at_endpoint induction via merge_chain)
- ✅ A1 ∩ A2 intersection
- ✅ A2 endpoints
- ✅ SCC construction via loop_factors_through_S1
- ✅ f injectivity + surjectivity
- ✅ Base case (𝒜 = set ws → identity retraction → scc_in_sc_false)
- 🔲 General case retraction (non-cycle arcs exist)

### Surface classification sorrys (8): Theorems 75.4, 76, 77.5, 78.1, 78.2

### Non-surface proof chain:
```
sc_graph_no_cycle [1 sorry: retraction]
  → tree_leaf_existence_bridge [PROVED modulo above + j-i=2]
    → ... → Theorem_85_3_Schreier_index [PROVED]
```

## Build: ~45s (cached) or ~24s (fresh)
```bash
cd /project/tst && /project/bin/isabelle build -D .
```
