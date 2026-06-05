# AlgTop.thy Sorry Audit (2026-06-06, updated)

## Summary: 11 executable sorrys, 8 comment-only occurrences

Build: `/project/bin/isabelle build -D .` — 17s, clean.

## Non-surface sorrys (3):

| # | Line | Lemma | Category | Description |
|---|------|-------|----------|-------------|
| 1 | L2676 | finite_tree_has_leaf | Tree/Euler | SC + all vertices degree≥2 → False (topological bridge) |
| 2 | L4079 | graph_euler_invariance | Euler invariance | V₁-E₁ = V₂-E₂ for two decompositions (common refinement) |
| 3 | L5797 | covering_graph_pi1_rank | Euler invariance | V_L-card(𝒜_L) = V_G-card(𝒜_G) (instance of #2) |

## Surface sorrys (8):

| # | Line | Theorem | Description |
|---|------|---------|-------------|
| 4 | L7556 | Theorem 75.4 | 1-skeleton is wedge of circles |
| 5 | L7646 | Theorem 76 | Elementary scheme operation induction |
| 6 | L7688 | Theorem 75.4 | Abelianization + Smith normal form |
| 7 | L7750 | Theorem 78.1 | Disjoint simplex copies + pasting |
| 8 | L7786 | Theorem 78.2 | Iterative merging construction |
| 9 | L7826 | Theorem 77.5 | Polygonal region → edge scheme |
| 10 | L7842 | Theorem 77.5 | Normal form reduction |
| 11 | L7844 | Theorem 77.5 | Normal form → homeomorphism type |

## Dependency chain:
```
finite_tree_has_leaf (#1)
  → tree_euler_and_leaf_combined → tree_euler_from_leaf → tree_euler_number_one
    → covering_graph_pi1_rank:
      hrank_X_formula [PROVED from tree_euler + V_eq + partition]
      hchi_X [PROVED by linarith]
      hchi_L [PROVED from multiplicity]
      hrank_E_raw [PROVED from tree_euler_number_one on TE_raw]
      heuler_inv: needs graph_euler_invariance (#2) + instance (#3)
      → hrank_E_formula → card(SE_raw) = k*n+1 [PROVED]
        → Theorem_85_3_Schreier_index

Surface (#4-#11): independent of #1-#3.
```

## Fully proved infrastructure (highlights):
- Covering lifted arc family interface (all 3 clauses: surj+inj+endpoints, coverage, disjointness)
- Covering arc/vertex multiplicity
- Injectivity via Theorem 54.3 + arc simply connected
- Free group transfer to nat basis (free_group_full_reindex)
- Max conn comp helpers (h_mcc_disjoint, h_mcc_absorb)
- Graph arc containment (A⊆B → A=B for arcs)
- Euler characteristic arithmetic (linarith chain)
- Vertex set equality V_X = V_Tw, V_E_raw = V(tree_arcs_E)
- Subgraph coherent topology (for Tw and TE_raw)
- Double counting sum, degree sum leaf
- Tree Euler for X (via tree_euler_number_one)
- Tree Euler for E (via tree_euler_number_one on TE_raw)
- 𝒜E_raw finiteness (via finite_covering_compact)
- All hbig_E conjuncts extracted as named facts
