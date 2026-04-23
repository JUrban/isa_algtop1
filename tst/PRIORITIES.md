# Priorities and Issues for AlgTop Formalization

## Status: 146 sorry statements, builds in ~12s, ~7500 lines

## Session 2026-04-23 Progress:
- **stereographic_proj_homeomorphism: ZERO SORRY** (key Jordan blocker removed)
- **homeomorphism_preserves_simply_connected: ZERO SORRY** (general transfer lemma)
- **S2_minus_north_pole_simply_connected: ZERO SORRY** (direct from stereographic + R2_sc)
- Also proved: step_1_inj ψ⁻¹ transfer, R2_simply_connected, hq_star_inj, R2_minus_point_not_sc
- Cached: 16K lines of sorry-free proofs moved to Top0 (AlgTop builds in 12s)

## KEY BLOCKER: S² Rotation
- `S2_minus_point_simply_connected` (general b) needs rotation of S² sending b → north_pole
- This blocks: S2_minus_two_points_not_sc, map_into_S2_minus_point_nulhomotopic
- These block: Theorem_61_3, Theorem_63_2, and ultimately Jordan Curve Theorem
- **Solution needed**: either general rotation matrix on S², or generalized stereographic projection

## Jordan Chain Status:
| Theorem | Sorries | Status |
|---------|---------|--------|
| stereographic_proj_homeomorphism | 0 | ✅ DONE |
| R2_simply_connected | 0 | ✅ DONE |
| homeomorphism_preserves_sc | 0 | ✅ DONE |
| S2_minus_north_pole_sc | 0 | ✅ DONE |
| S2_minus_point_sc (general) | 1 | **BLOCKED by rotation** |
| S2_minus_two_points_not_sc | 1 | BLOCKED by general sc |
| map_into_S2_minus_point_nulhomo | 1 | BLOCKED by general sc |
| Theorem_57_1 (antipode not nulhomo) | 4 | hq_cover + other |
| Theorem_61_3 (Jordan separation) | 6 | BLOCKED |
| Theorem_63_1 (loop nontrivial) | 3 | covering space construction |
| Theorem_63_2 (arc no separation) | 3 | BLOCKED |
| Theorem_63_4 (Jordan Curve) | 8 | BLOCKED |

## FTA — COMPLETE! ZERO SORRIES!
All FTA chain verified by thm_oracles, cached in Top0.
