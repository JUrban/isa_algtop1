# AlgTop.thy Sorry Audit (2026-06-06)

## Summary: 10 executable sorrys, 5 comment-only occurrences

Build: `cd /project/tst && /project/bin/isabelle build -D .` — 14s, clean.

## Non-surface sorrys (2):

| # | Line | Lemma | Category | Description | Blocked by |
|---|------|-------|----------|-------------|------------|
| 1 | L2676 | finite_tree_has_leaf | Tree/Euler | SC + all vertices degree≥2 → False | Topological bridge: cycle → non-trivial loop in SC |
| 2 | L5512 | covering_graph_pi1_rank | Euler invariance | rank + card V_L = card 𝒜_L + 1 | Witness drift: 𝒜_L ≠ 𝒜E_raw vertex sets |

## Surface sorrys (8):

| # | Line | Theorem | Description |
|---|------|---------|-------------|
| 3 | L7266 | Theorem 75.4 | 1-skeleton is wedge of circles |
| 4 | L7356 | Theorem 76 | Elementary scheme operation induction (8 cases) |
| 5 | L7398 | Theorem 75.4 | Abelianization + Smith normal form |
| 6 | L7460 | Theorem 78.1 | Disjoint simplex copies + pasting |
| 7 | L7496 | Theorem 78.2 | Iterative merging construction |
| 8 | L7536 | Theorem 77.5 | Polygonal region → edge scheme |
| 9 | L7552 | Theorem 77.5 | Normal form reduction |
| 10 | L7554 | Theorem 77.5 | Normal form → homeomorphism type |

## Dependency chain:
```
finite_tree_has_leaf (#1)
  → tree_euler_and_leaf_combined (hleaf_universal)
    → tree_euler_from_leaf (Euler by leaf induction)
      → tree_euler_number_one
        → covering_graph_pi1_rank (hrank_X_formula)
          → Schreier chain (hchi_X → hchi_L → hrank_E)
            → covering_graph_pi1_rank (#2: hrank_E_formula)
              → Theorem_85_3_Schreier_index

Surface (#3-#10): independent of #1-#2.
```

## Fully proved infrastructure (highlights):
- Covering lifted arc family interface (all 3 clauses: surj+inj+endpoints, coverage, disjointness)
- Covering arc/vertex multiplicity (card 𝒜_L = k * card 𝒜w, card V_L = k * card V_X)
- Injectivity via Theorem 54.3 + arc simply connected
- Free group transfer to nat basis (free_group_full_reindex)
- Max conn comp helpers (h_mcc_disjoint, h_mcc_absorb)
- Graph arc containment (A⊆B → A=B for arcs)
- Euler characteristic arithmetic (linarith chain)
- Vertex set equality V_X = V_Tw
- Subgraph coherent topology
- Double counting sum, degree sum leaf
