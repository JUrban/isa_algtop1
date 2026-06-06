# Proof Status: Munkres Algebraic Topology Formalization

## Authoritative Sessions and Files

| Session | Directory | Key File | Status |
|---------|-----------|----------|--------|
| Top0 | `i/` | Top1_Ch2..Ch9_13.thy | Chapters 2-8 (general topology). Cached. |
| AlgTopBase0 | `b0/` | AlgTop_JCT_Base0.thy | JCT infrastructure (Thm 58.7, etc). Cached. |
| AlgTopBase | `b/` | AlgTop_JCT_Base.thy | JCT + homeomorphism helpers. Cached. |
| AlgTop0 | `a0/` | AlgTop0.thy | §51-§63 foundations. 1 proof gap (pi1_iso_Z, proved in AlgTopC). |
| AlgTopC | `ac/` | AlgTopCached.thy | Cached infrastructure. Oracle-clean. |
| AlgIsoFixedBase | `fib/` | AlgIsoFixedBase.thy | §65 helpers (K4, SCC_pi1, generation). Oracle-clean. |
| AlgIsoFixed | `fi/` | AlgIsoFixed.thy | **Thm 58.7, Lemma 65.1, Thm 65.2. Oracle-clean.** |
| AlgTop | `.` | AlgTop.thy | §64, §67-§85. Has proof gaps (see below). |
| K5 | `k5/` | K5_nonplanar.thy | Thm 64.4 (K5). 2 proof gaps. |

## Session Dependency Chain

```
Top0 → AlgTopBase0 → AlgTopBase → AlgTop0 → AlgTopC
  → AlgIsoFixedBase → AlgIsoFixed → AlgTop
  → K5
```

## Key Theorems (oracle-clean, no proof gaps)

All verified with `thm_oracles` returning empty (no `skip_proof`):

- `Theorem_58_7` — Homotopy equivalence induces π₁ iso (specific map)
- `Lemma_65_1` — K4 inclusion induces π₁ iso (via inclusion map id)
- `Lemma_65_1_exists_basepoint` — Basepoint-flexible version
- `Theorem_65_2` — SCC inclusion induces π₁ iso (Munkres §65 main result)
- `move_one_puncture` — Step 4: moving punctures preserves iso
- `Munkres_Step_4_move_punctures` — Full Step 4
- `pi1_S2_minus_two_points_iso_Z_proved` — π₁(S²-{p}-{q}) ≅ Z

These are in `fi/AlgIsoFixed.thy` and `ac/AlgTopCached.thy`.

## Proof Gaps

### AlgTop0.thy (1 gap)
- `pi1_S2_minus_two_points_iso_Z` — proved in AlgTopCached as `_proved` variant.
  Cannot close at AlgTop0 level (infrastructure not available upstream).

### K5_nonplanar.thy (2 gaps)
- K4 4-component separation — all premises proved individually, but Isabelle
  OF-chain with 35 premises exceeds timeout.
- Main contradiction — needs component boundary infrastructure.

### AlgTop.thy (9 executable gaps, updated 2026-06-06)

**Non-surface (1 gap):**
- `finite_tree_has_leaf` (L2676): SC + all vertices degree≥2 → False (topological bridge)

**Surface classification (8 gaps):**
- Theorem 75.4: 1-skeleton is wedge of circles (L9785)
- Theorem 76: Elementary scheme operation induction (L9875)
- Theorem 75.4: Abelianization + Smith normal form (L9917)
- Theorem 78.1: Disjoint simplex copies + pasting (L9979)
- Theorem 78.2: Iterative merging construction (L10015)
- Theorem 77.5: Polygonal region → edge scheme (L10055)
- Theorem 77.5: Normal form reduction (L10071)
- Theorem 77.5: Normal form → homeomorphism type (L10073)

**FULLY PROVED infrastructure (major lemmas, zero sorry):**
- **graph_euler_invariance**: V-E invariant under decomposition change
- **graph_iterated_subdivision_exists**: iterated arc subdivision
- **graph_same_vertices_same_arcs**: same vertex set → same arcs
- **graph_arc_containment_via_open_interior**: arc containment via connectedness
- **graph_coherent_any_decomposition**: coherent topology for any finite decomposition
- **graph_arc_interior_open**: arc interiors open in coherent topology
- **graph_subdivision_preserves_euler**: single subdivision preserves V-E
- **closed_set_first_entry**: boundary point in connected space
- Covering lifted arc family interface (all 3 clauses)
- 𝒜_L conditions: arc, cover, intersection, finiteness — ALL PROVED
- Covering arc/vertex multiplicity, free group transfer, max conn comp helpers
- All §64, §67-§73, §79-§85 infrastructure

See `SORRY_AUDIT.md` for detailed dependency analysis.

## Build Command

```bash
cd /project/tst && /project/bin/isabelle build -D .
```

## Files to Ignore

- `archive/` — old backups and stale files. Not part of the active formalization.
- `bck*`, `*_old.thy`, `*_bak.thy` — if any remain, they are stale backups.
- `CHANGES*` files — incremental changelog snapshots.
