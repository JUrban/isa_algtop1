# Errata and Update to REPORT_260429.md

**Date:** 2026-04-29 (end of session)

---

## 1. Corrected Numbers

| Metric | Report said | Actual now |
|--------|-------------|------------|
| Sorries in AlgTop.thy | 81 | **74** |
| Sorries in JCT_Base | 1 | **0** (deleted wrong lemma) |
| Sorries in Ch5_8 | 1 | 1 (unchanged) |
| **Total project-wide** | **83** | **75** |

---

## 2. Wrong Recommendation: JCT_Base:902

The report said:
> **Close JCT_Base:902 sorry** -- medium difficulty, impacts downstream

**This was wrong on all counts:**
- The lemma had a **wrong statement** (`nulhomotopic_on I_set` is vacuously true since I is contractible)
- The correct version (Munkres Lemma 55.3) was **already fully proved** in `Top1_Ch9_13.thy`
- The lemma was **never used** downstream
- It has been **deleted** (895 lines of dead code removed)

See `REPORT_JCT_BASE_902.md` for full analysis.

---

## 3. Wrong Recommendation: Commutator Subgroup Normal

The report said:
> **Prove commutator subgroup normal** -- enables §75 abelianization (5 sorries)

**Already done:** `commutator_subgroup_is_normal` was proved in a prior session. Additionally, the full quotient group infrastructure and `Theorem_75_1_H1_abelianization` are now **fully proved** (0 sorry).

---

## 4. Theorem Status Updates (changed since report)

| Result | Report said | Actual now |
|--------|-------------|------------|
| Theorem 75.1 (H₁ = abelianization) | SORRY(2) | **PROVED** |
| Theorem 72.1 (attaching 2-cell) | SORRY(5) | **SORRY(1)** (h_ι_cont proved) |
| Theorem 78.1 (triangulable → polygonal) | SORRY(2) | **SORRY(1)** (simplex proved) |
| Theorem 80.3 (universal factors through) | SORRY(3) | **SORRY(2)** (obtain steps proved) |
| Theorem 80.1 (universal unique) | not mentioned | **PROVED** (was already proved) |

---

## 5. Results Missing from the Report (73 items)

The report covered ~67 of ~140 numbered results from algtop.tex. Missing items fall into categories:

### A. Actually formalized but not listed in the report (7 found)

| Result | Status | Location |
|--------|--------|----------|
| Lemma 58.1 (deformation retract) | PROVED | JCT_Base0 |
| Corollary 58.5 | PROVED | JCT_Base0 |
| Corollary 59.2 | PROVED | JCT_Base |
| Lemma 61.1 (nulhomotopy lemma) | PROVED | JCT_Base |
| Lemma 61.2 | PROVED | JCT_Base |
| Theorem 63.5 | PROVED | AlgTop0 |
| Theorem 80.1 (universal unique) | PROVED | AlgTop |

### B. Intentionally skipped (§64, §66) — 8 results

§64 (Imbedding graphs in plane) and §66 (Cauchy integral formula) are not on the algebraic topology critical path and were intentionally omitted.

### C. Not formalized and not listed — ~58 results

These are a mix of:
- Minor corollaries that follow trivially from stated theorems
- Exercises (many "Theorem X.Y" in algtop.tex are exercises)
- Results in §77-§85 where only the main theorem was formalized, not supporting lemmas
- Results in §67-§69 where definitions were stated but supporting lemmas skipped

The most notable gaps (results that matter for downstream work):

| Result | What it is | Impact |
|--------|-----------|--------|
| Lemma 68.1 (reduced words) | Free product normal form | Needed for 68.4 uniqueness |
| Lemma 68.3 (extension property) | Free product universal property | Needed for 68.4 |
| Lemma 69.1 (free group exists) | Existence via reduced words | Foundation for §69 |
| Lemma 69.3 (universal property) | Free group characterization | Needed for 69.4 |
| Lemma 79.1 (lifting criterion) | When lifts exist | Key for §79-§82 |
| Lemma 79.3 (conjugacy) | Basepoint change for coverings | Key for 79.4 |
| Lemma 80.1-80.2 (universal props) | Universal covering construction | Key for §80 |
| Lemma 81.1 (covering action) | Group action on fiber | Key for 81.2 |

---

## 6. New Infrastructure (proved since report, not in any Munkres section)

| Lemma | What it does |
|-------|-------------|
| `coset_self_mem` | g ∈ coset(g) |
| `coset_e_is_N` | coset(e) = N for subgroup N |
| `normal_coset_eq` | coset(g) = coset(h) ↔ invg(g)*h ∈ N |
| `normal_coset_mul_eq` | (gN)(hN) = (gh)N for normal N |
| `quotient_projection_properties` | Natural projection: hom + surj + kernel=N |
| `quotient_by_commutator_is_abelian` | G/[G,G] is abelian |
| `quotient_group_is_group` | G/N is a group when N normal |
| `first_isomorphism_theorem` | Surj hom with kernel N gives G/N ≅ H |
| `abelianization_concrete` | G/[G,G] satisfies abelianization predicate |
| `standard_simplex_is_polygonal_region` | Standard triangle is 3-sided polygonal region |
| `commutator_subgroup_is_normal` | [G,G] is normal in G |

---

## 7. Corrected Recommendations

1. ~~Close JCT_Base:902~~ **DONE** (deleted, was wrong statement)
2. **Prove SvK kernel computation** — still the critical blocker for §71-§77. But note the proof sketch has a structural issue: `hj_surj` and `hker` introduce separate existential `j`'s that need merging.
3. ~~Prove commutator subgroup normal~~ **DONE**
4. **Work on covering existence (§82)** — still needed, but requires Lemma 79.1 (lifting criterion) which is not formalized.
5. ~~Consider importing HOL-Analysis~~ — still valid but low priority given current progress.
6. **NEW: Prove Lemma 68.3 (extension property)** — key missing piece for free product uniqueness (Theorem 68.4, currently 1 sorry).
7. **NEW: Formalize Lemma 79.1 (lifting criterion)** — blocks all of §79-§82.
