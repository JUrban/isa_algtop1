# AlgTop.thy Sorry Audit (2026-06-06, session 1368)

## Summary: ~18 executable sorrys (9 blocking + 1 orphan A2_ep + 3 orphan formula + 8 surface)

Build: clean. 12146 lines.

## Progress: card ≠ 2 infrastructure + hinter_eq_ep PROVED

**Key progress in card ≠ 2 for j-i ≥ 3:**
✅ hpred_in_ep: walk predecessor vertex in ep of first arc
✅ hinter_eq_ep: intersection = ep (via card_subset_eq with named intermediates)
✅ Walk vertex in intersection → in ep of second arc (non-wrap case)
❌ Wrap case (idx = j-i-1): walk_v at position Suc j vs Suc i
❌ Final element analysis: walk_v in 2-element ep → equality → hv_distinct contradiction

## Remaining blocking sorrys:

### In sc_graph_no_cycle (7):
| # | Description |
|---|-------------|
| 1 | A1 merge (iterative arc_merge_at_endpoint) |
| 2 | A1 ∩ A2 = {a_start, a_end} |
| 3 | A2 endpoints |
| 4 | f continuity (pasting lemma) |
| 5 | f injectivity |
| 6 | C retract of T |

### In tree_leaf_existence_bridge walk (2):
| # | Description |
|---|-------------|
| 7 | card ≠ 2 for j-i ≥ 3 (2 sub-sorrys: wrap + final) |
| 8 | j-i = 2 case (SCC + retraction for 2 arcs) |

## Chain: all PROVED modulo these sorrys
```
sc_graph_no_cycle + walk sorrys
  → tree_leaf_existence_bridge [PROVED]
    → ... → Theorem_85_3_Schreier_index [PROVED]
```

## Orphan: 4 + Surface: 8
