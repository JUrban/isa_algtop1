# Priorities and Issues for AlgTop Formalization

## A. Statement/Definitional Fixes Needed

### A1. Theorem_80_1_universal_unique: Missing basepoint membership — **DONE**
### A2. Theorem_57_1 (Borsuk-Ulam): WLOG rotation — **DONE** (case split + rotation)
### A3. `top1_separates_on` definition: No C ⊆ X condition (COSMETIC, low priority)

---

## B. Top Priorities for Proof Progress

### B1. π₁(S¹) ≅ ℤ as a group isomorphism (HIGHEST PRIORITY)

**Status:** Bijection proved (φ = floor ∘ lifting correspondence). Homomorphism sorry remains.
**Recent progress:**
- Proved `top1_R_to_S1_int_shift`: p(x + n) = p(x) for integer n
- Proved φ bijective via `bij_betw_trans` (floor on Z is bijective)
- Proved assembly (exists iso with bij + hom)
- Added translated-lift helper lemmas
**What's still needed:**
- Homomorphism: φ(c·d) = φ(c) + φ(d) via translated-lift concatenation

### B2. Covering space path lifting (Lemma 54.1)

**Status:** Proof sketch expanded with Lebesgue subdivision comments.
**What's needed:** Lebesgue number argument + interval-by-interval lift construction.

### B3. R → S¹ is a covering map (Theorem 53.1)

**Status:** arc_E fully proved (220 lines). 3 symmetric arcs (N, W, S) remain sorry'd.
**What's needed:** Replicate arc_E proof with adapted coordinates.

### B4. `hh_star_trivial` from nulhomotopy (Theorem 57.1) — **DONE** for h(1,0)=(1,0) case

### B5. Lemma_55_3 forward (nulhomotopic → B² extension)

**Status:** Construction k(y) = H(y/|y|, 1-|y|) defined. k extends h proved.
**What's needed:** k is continuous (composition on B²-{0}, limit at 0).

### B6. Simply connected covering image = trivial (§80)

**Status:** carrier = {id} proved. p_*(id_E) = id_B forward direction needs
  continuous_preserves + transitivity. Backward direction done.
**Used by:** Theorem_80_1_universal_unique (hH_trivial, hH'_trivial now proved via this lemma).

---

## C. Verified Correct (No Fixes Needed)

- All definitions match Munkres.
- FTA Steps 3-4, Theorem_58_7: Fully proved.
- Type separation (complex vs real×real): Deliberate design choice.
- Z group definitions moved before §54 (resolved forward reference).

---

## D. Recommended Work Order

1. ~~Fix A1~~ — **DONE**
2. ~~Fix A2~~ — **DONE**
3. ~~Prove B4~~ — **DONE**
4. ~~Prove Theorem_53_2~~ — **DONE**
5. ~~Prove φ bijective in Theorem_54_5_iso~~ — **DONE**
6. ~~Prove k extends h in Lemma_55_3~~ — **DONE**
7. ~~Prove π₁ carrier singleton (simply_connected_trivial_image)~~ — **DONE**
8. **Prove B3 arcs** (N, W, S) — symmetric to arc_E
9. **Prove B2** (path lifting) — Lebesgue number argument
10. **Prove B1 homomorphism** — translated-lift concatenation
11. **Close B6 forward direction** — continuous_preserves_path_homotopic application

**Current sorry count: 163**
