# AlgTop.thy Sorry Audit (2026-06-06, session 1366)

## Summary: ~16 executable sorrys (8 blocking + 3 orphan + 8 surface)

Build: clean.

## sc_graph_no_cycle: 7 blocking sorrys

**PROVED in sc_graph_no_cycle:**
✅ A1 ∪ A2 = C, hA/hB orientations, f boundary values
✅ f surjectivity (f ` S¹ = C), SCC application, scc_in_sc_false
✅ hws_adj_card: card ≥ 1, card ≤ 2 infrastructure

**Remaining sorrys (7):**
| # | Description | Difficulty |
|---|-------------|-----------|
| 1 | A1 merge | Medium |
| 2 | A1 ∩ A2 | Medium |
| 3 | A2 endpoints | Medium |
| 4 | f continuity | Medium |
| 5 | f injectivity | Medium |
| 6 | C retract of T | Hard |
| 7 | card ≠ 2 in hws_adj_card | Medium |

**BUG FIX**: sc_graph_no_cycle condition changed from `≠ {}` to `card = 1`
to exclude star graphs (Y-shape) which are valid trees but satisfied the old condition.

## Chain: all PROVED modulo sc_graph_no_cycle
## Orphan: 4 (forest_euler 2 + two_arcs 1 + A2_ep 1)
## Surface: 8
