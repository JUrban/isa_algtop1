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

### AlgTop.thy (23 gaps)
- §64: K5/K33 non-planarity (2 gaps, partially addressed in K5 session)
- §67-§68: Free abelian group rank uniqueness (1 gap)
- §69: Free group independence (1 gap)
- §71: Free group of infinite wedge (1 gap)
- §73: Torus/dunce cap fundamental groups (4 gaps)
- §74: Surface fundamental groups (5 gaps)
- §75-§78: Surface classification (5 gaps)
- §79-§82: Covering space existence (2 gaps)
- §83-§84: Graph covering / free subgroup (4 gaps)
- §85: Nielsen-Schreier rank formula (3 gaps)

## Build Command

```bash
cd /project/tst && /project/bin/isabelle build -D .
```

## Files to Ignore

- `archive/` — old backups and stale files. Not part of the active formalization.
- `bck*`, `*_old.thy`, `*_bak.thy` — if any remain, they are stale backups.
- `CHANGES*` files — incremental changelog snapshots.
