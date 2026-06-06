# AlgTop.thy Sorry Audit (2026-06-06, session 1363)

## Summary: ~15 executable sorrys (6 blocking + 1 orphan A2_ep + 3 orphan formula/helper + 8 surface)

Build: clean. ~21s.

## sc_graph_no_cycle: SCC surjectivity PROVED!

**PROVED in SCC construction:**
✅ A1 ∪ A2 = C (set theory)
✅ hA orientation (doubleton_eq_iff + reversal)
✅ hB orientation (modulo A2 endpoint sorry)
✅ f boundary values
✅ **f surjectivity (f ` S¹ = C)** — full proof with semicircle parametrization
✅ SCC application
✅ scc_in_sc_false application

**Remaining sorrys in sc_graph_no_cycle (6):**
| # | Description | Status |
|---|-------------|--------|
| 1 | A1 merge (iterative arc_merge_at_endpoint) | Sorry |
| 2 | A1 ∩ A2 = {a_start, a_end} | Sorry |
| 3 | A2 endpoints = {a_end, a_start} | Sorry |
| 4 | f continuity (pasting lemma) | Sorry |
| 5 | f injectivity (case analysis) | Sorry (infrastructure ready) |
| 6 | C retract of T | Sorry |

## Proof chain:
```
sc_graph_no_cycle [6 sorrys]
  → tree_leaf_existence_bridge [PROVED]
    → ... → Theorem_85_3_Schreier_index [PROVED]
```

## Orphan sorrys (4) + Surface sorrys (8)
