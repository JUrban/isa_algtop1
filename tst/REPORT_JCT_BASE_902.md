# Report: JCT_Base:902 `nulhomotopic_loop_path_homotopic_constant`

## Executive Summary

The lemma is **commented out**, **not used** anywhere, and **has a wrong statement**. However, the *correct* version of this result (Munkres Lemma 55.3) **is already fully formalized** in `Top1_Ch9_13.thy` as `Lemma_55_3_nulhomotopic_characterization` and `nulhomotopic_trivializes_loops_general`. No new work is needed.

---

## 1. Current Status

```
b/AlgTop_JCT_Base.thy:6:  DISABLED: commented out inside (* ... *)
b/AlgTop_JCT_Base.thy:902: sorry  (inside commented-out block)
```

- **Not compiled** (inside `(* ... *)`)
- **Not used** by any active theory file (checked AlgTop.thy, AlgTop0.thy, JCT_Base0.thy)
- **Zero downstream impact**

---

## 2. The Statement Bug

The lemma assumed:
```isabelle
top1_nulhomotopic_on I_set I_top X TX f
```

This says f: [0,1] -> X is nulhomotopic. But [0,1] is contractible, so **every** continuous f: [0,1] -> X is nulhomotopic. The hypothesis is vacuously true. Under this hypothesis, the conclusion ("every loop is contractible") would be false.

Munkres' actual statement (Lemma 55.3) uses **S^1 as domain**, not [0,1]:

> **Lemma 55.3** (Munkres). For h: S^1 -> X continuous, the following are equivalent:
> 1. h is nulhomotopic (as a map S^1 -> X)
> 2. h extends to a continuous map k: B^2 -> X
> 3. h_* is the trivial homomorphism of fundamental groups

---

## 3. The Existing Formalization Already Has This

The correct Munkres result is **fully proved** in `i/Top1_Ch9_13.thy`:

### Lemma_55_3_nulhomotopic_characterization (line 12500)
```isabelle
lemma Lemma_55_3_nulhomotopic_characterization:
  assumes "top1_continuous_map_on top1_S1 top1_S1_topology X TX h"
      and "is_topology_on X TX"
  shows "top1_nulhomotopic_on top1_S1 top1_S1_topology X TX h
      <-> (EX k. top1_continuous_map_on top1_B2 top1_B2_topology X TX k
               & (ALL x:top1_S1. k x = h x))"
```
**Status: FULLY PROVED** (both directions). This is Munkres (1) <-> (2).

### Lemma_55_3_backward (line 12324)
```isabelle
lemma Lemma_55_3_backward:
  -- "extension to B^2 implies nulhomotopic"
  assumes "top1_continuous_map_on top1_S1 top1_S1_topology X TX h"
      and "is_topology_on X TX"
      and "top1_continuous_map_on top1_B2 top1_B2_topology X TX k"
      and "ALL x:top1_S1. k x = h x"
  shows "top1_nulhomotopic_on top1_S1 top1_S1_topology X TX h"
```
**Status: FULLY PROVED.** This is Munkres (2) => (1).

### nulhomotopic_trivializes_loops_general (line 14652)
```isabelle
lemma nulhomotopic_trivializes_loops_general:
  assumes "is_topology_on X TX" and "is_topology_on Y TY"
      and "top1_continuous_map_on X TX Y TY g"
      and "top1_nulhomotopic_on X TX Y TY g"
      and "g x0 = y0" and "x0 : X"
      and "top1_is_loop_on X TX x0 f"
  shows "top1_path_homotopic_on Y TY y0 y0 (g o f) (top1_constant_path y0)"
```
**Status: FULLY PROVED.** This is Munkres Corollary 58.6 generalized. It says: if g: X -> Y is nulhomotopic and f is a loop at x0, then g o f is path-homotopic to the constant loop at g(x0). Specializing to X = S^1 gives the (1) => (3) direction of Lemma 55.3.

### Usage pattern (already deployed in the formalization)

The standard Munkres pattern "map extends to B^2 => loop is trivial" is used via:
```
Lemma_55_3_backward  -->  nulhomotopic_trivializes_loops_general
```

This chain is already applied in:
- `Top1_Ch9_13.thy:12988` (Theorem 55.2 no-retraction)  
- `Top1_Ch9_13.thy:13587` (Brouwer fixed-point)
- `AlgTop_JCT_Base0.thy:4020` (Borsuk-Ulam setup)
- `Top1_Ch9_13.thy:15401` (winding number applications)

---

## 4. What Munkres Does and Where We Stand

| Munkres Result | Formalized? | Location |
|---------------|------------|----------|
| Lemma 55.3 (1) <-> (2): nulhomotopic <-> extends to B^2 | **YES** | `Lemma_55_3_nulhomotopic_characterization` |
| Lemma 55.3 (2) => (3): extension => trivial h_* | **YES** | `nulhomotopic_trivializes_loops_general` |
| Lemma 55.3 (3) => (1): trivial h_* => nulhomotopic | **YES** | proved in Ch9_13 (line ~13094+) |
| Corollary 58.6: nulhomotopic => trivial h_* | **YES** | `nulhomotopic_trivializes_loops_general` |

All three directions of Lemma 55.3 are formalized and proved. The JCT_Base:902 sorry was an **independent, incorrectly-stated attempt** to redo part of this — not a gap.

---

## 5. Recommendation

**No action needed.** The disabled lemma with the wrong statement should remain commented out. The correct Munkres formulation is already fully proved and actively used in the formalization. Attempting to "fix" the JCT_Base lemma would be redundant.

If you want a clean-up:
- Delete the commented-out block (lines 11-912 of `b/AlgTop_JCT_Base.thy`)
- Update the `nulhomotopic_loop_DISABLED: True` placeholder to reference the correct existing lemmas

This is a 5-minute cleanup, not a multi-day effort.

---

## 6. Correction to REPORT_260429.md

The report's recommendation:

> **Close JCT_Base:902 sorry** -- medium difficulty, impacts downstream

is **incorrect**. The sorry:
- Has zero downstream impact (lemma is commented out and unused)
- Has a wrong statement (vacuously true hypothesis)
- The correct version is already fully proved in Ch9_13

The report was written before the lemma was disabled and before the correct formalization was verified.
