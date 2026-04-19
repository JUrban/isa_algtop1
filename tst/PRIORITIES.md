# Priorities and Issues for AlgTop Formalization

## A. Statement/Definitional Fixes — ALL DONE

### A1. Theorem_80_1_universal_unique: Missing basepoint membership — **DONE**
### A2. Theorem_57_1 (Borsuk-Ulam): WLOG rotation — **DONE**
### A3. `top1_separates_on`: No C ⊆ X condition (COSMETIC, low priority)

---

## B. Top Priorities for Proof Progress

### B1. π₁(S¹) ≅ ℤ as a group isomorphism (HIGHEST PRIORITY)

**Status:** Bijection proved. Assembly proved. Homomorphism sorry remains.
**What's still needed:**
- Homomorphism: φ(c·d) = φ(c) + φ(d) via translated-lift concatenation
- Key helper available: `top1_R_to_S1_int_shift` (periodicity)

### B2. Covering space path lifting (Lemma 54.1)

**Status:** Proof sketch expanded. Lebesgue subdivision + lift construction sorry'd.

### B3. R → S¹ is a covering map (Theorem 53.1)

**Status:**
- arc_E: FULLY PROVED (220 lines)
- arc_N: openness ✓, V_open ✓, V_disj ✓, V_union ✓, V_homeo sorry
- arc_W: openness ✓, V_open ✓, V_disj ✓, V_union sorry, V_homeo sorry
- arc_S: openness ✓, V_open ✓, V_disj ✓, V_union sorry, V_homeo sorry

### B4. `hh_star_trivial` / `nulhomotopic_trivializes_loops` — **FULLY PROVED**

### B5. Lemma_55_3 forward (nulhomotopic → B² extension)

**Status:** k extends h proved. k continuous sorry.

### B6. Simply connected covering image = trivial — **FULLY PROVED**

### B7. Theorem_80_1 universal uniqueness

**Status:** hH_trivial/hH'_trivial ✓ (via B6). Assembly ✓.
Two algebraic sorries remain: invg(id) = id and mul(id,id) = id.

---

## C. Fully Proved Lemmas (no sorries)

- `top1_R_to_S1_int_shift` / `_int_shift'` / `_translate_lift`
- `nulhomotopic_trivializes_loops`
- `simply_connected_trivial_image`
- `top1_S1_fundamental_group_nontrivial`
- `Theorem_54_5` (bijection)
- `Lemma_54_1_uniqueness`
- `Theorem_54_3` (path-homotopic paths lift to path-homotopic)
- `continuous_preserves_path_homotopic`
- `Corollary_59_2`
- `top1_Z_is_abelian_group`
- All FTA Steps 3-4, Theorem_58_7

---

## D. Work Order

1-7: DONE (see above)
8. **Close arc_W/S V_union** — same trig analysis as arc_N
9. **Close arc V_homeo** — needs inverse construction per arc
10. **Close B1 homomorphism** — translated-lift concatenation
11. **Close B2 (path lifting)** — Lebesgue number argument

**Current sorry count: 164**
