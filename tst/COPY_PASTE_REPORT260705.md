# Copy-Paste Clone Analysis Report

**Date:** 2026-07-05
**Source:** `/project/tst/AACLONES` (CPD output)
**Project:** AlgTop Isabelle/HOL formalization

---

## 1. Summary

| Metric | Value |
|--------|-------|
| Total clone pairs | 254 |
| Token range | 100-1099 |
| Average tokens/clone | 159 |
| Total duplicated tokens | 40,603 |
| Files involved | 9 |

### Clones by file (occurrence count)

| File | Occurrences | Notes |
|------|-------------|-------|
| ac/AlgTopCached.thy | 363 | ~73% of all clones |
| a0/AlgTop0.thy | 49 | |
| i/Top1_Ch4.thy | 47 | |
| i/Top1_Ch2.thy | 40 | |
| b0/AlgTop_JCT_Base0.thy | 36 | |
| i/Top1_Ch9_13.thy | 30 | |
| b/AlgTop_JCT_Base.thy | 15 | |
| i/Top1_Ch5_8.thy | 14 | |
| i/Top1_Ch3.thy | 4 | |

---

## 2. Top Clone Pairs (by token count)

### Clone 1: Path lifting in helix covering (1099 tokens, 122 lines)
- **Files:** `a0/AlgTop0.thy:2314` vs `a0/AlgTop0.thy:2685`
- **Theorems:** `Theorem_63_1_c_subgroups_trivial` vs `Theorem_63_1_c_subgroups_trivial_reverse`
- **Pattern:** Defines `gamma_lift` and `delta_lift` as lifted paths in covering space E, then proves both are paths in E. Identical proof structure for the "left" and "right" products alpha*beta vs beta*alpha.
- **Refactoring:** Extract a `helix_lift_path_in_E` lemma parameterized by the path and integer label.
- **Difficulty:** Medium. The two copies differ only in which integer slices they use (0 vs -2 vs -1).

### Clone 2: Covering space angle/sheet extraction (1067 tokens, 142 lines)
- **Files:** `ac/AlgTopCached.thy:34609` vs `ac/AlgTopCached.thy:37644`
- **Theorem:** Both inside `Theorem_71_1_wedge_of_circles_finite` (two phases of the same proof)
- **Pattern:** Extracts angle coordinates and evenly covered neighborhoods for points on S1, then finds matching sheets. Used for two different covering maps (one for each index alpha).
- **Refactoring:** Extract `covering_sheet_angle_extraction` lemma. Takes a covering map, a point, and returns the angle/sheet structure.
- **Difficulty:** Hard (deep context dependency).

### Clone 3: Subdivision parameter bound proof (499 tokens, 54 lines)
- **Files:** `ac/AlgTopCached.thy:26125` vs `ac/AlgTopCached.thy:26183`
- **Theorem:** `Theorem_70_2_SvK_parameterized`
- **Pattern:** Proves that a subdivision parameter `sub i + t * (sub (Suc i) - sub i)` lies in the correct interval. Identical arithmetic for two different sub-intervals (U vs V case).
- **Refactoring:** Extract `subdivision_param_in_interval` lemma.
- **Difficulty:** Easy. Pure real arithmetic, no context dependency.

### Clone 4: S1 angle extraction (422 tokens, 50 lines)
- **Files:** `ac/AlgTopCached.thy:33848` vs `ac/AlgTopCached.thy:36747`
- **Theorem:** `Theorem_71_1_wedge_of_circles_finite`
- **Pattern:** Given a point on S1, extracts an angle theta using `sincos_total_2pi` and `R_to_S1`, then finds a second angle in a specific range. Two copies for two different points (p' vs q').
- **Refactoring:** Extract `S1_angle_in_range` lemma: given p on S1 and reference angle theta0, find theta with R_to_S1(theta)=p and theta0 < theta < theta0+1.
- **Difficulty:** Easy-Medium. Standard S1 arithmetic.

### Clone 5: Basepoint change set equality (359 tokens, 39 lines)
- **Files:** `ac/AlgTopCached.thy:47901` vs `ac/AlgTopCached.thy:47949`
- **Theorem:** `Theorem_72_1_attaching_two_cell`
- **Pattern:** Proves that applying the basepoint-change homomorphism Phi to a class x gives {k. loop_equiv(bc(f), k)} via set_eqI with loop_equiv_on_trans in both directions.
- **Refactoring:** Extract `basepoint_change_class_eq` lemma.
- **Difficulty:** Medium (needs topology context).

### Clone 6: Covering sheet neighborhood (346 tokens, 24 lines)
- **Files:** `ac/AlgTopCached.thy:33907` vs `ac/AlgTopCached.thy:36811`
- **Theorem:** `Theorem_71_1_wedge_of_circles_finite`
- **Pattern:** Similar to Clone 2 but shorter: sheet extraction from evenly covered neighborhoods.

### Clone 7: Helix covering construction (343 tokens, 27 lines)
- **Files:** `a0/AlgTop0.thy:1144` vs `a0/AlgTop0.thy:1887`
- **Theorems:** `helix_g_lift_is_loop` vs `Theorem_63_1_c_subgroups_trivial`
- **Pattern:** Defines the helix covering space E, topology TE, projection p0, and basepoint e0. Identical setup in two different theorems.
- **Refactoring:** Extract `helix_covering_setup` that returns (E, TE, p0, e0) with all basic properties.
- **Difficulty:** Easy. Just move the definitions and basic facts into a shared block.

### Clone 8: Product topology density argument (341 tokens, 80 lines)
- **Files:** `i/Top1_Ch2.thy:11137` vs `i/Top1_Ch2.thy:11446`
- **Theorems:** `Theorem_19_5_box` vs `Theorem_19_5_product`
- **Pattern:** Proves density in product topology by choosing points in basic open sets. Same argument for box vs product topology.
- **Refactoring:** Extract common density argument parameterized by which topology.
- **Difficulty:** Medium.

### Clone 9: Bounded metric / compact convergence (340 tokens, 85 lines)
- **Files:** `i/Top1_Ch5_8.thy:17215` vs `i/Top1_Ch5_8.thy:17537`
- **Theorems:** `top1_uniform_topology_on_superset_compact_convergence` vs `Theorem_46_7_finer_than_on`
- **Pattern:** Proves bounded metric properties and supremum arguments for function spaces.
- **Refactoring:** Extract `bounded_metric_sup_argument` lemma.
- **Difficulty:** Medium-Hard.

### Clone 10: SvK subdivision case analysis (324 tokens, 35 lines)
- **Files:** `ac/AlgTopCached.thy:18934` vs `ac/AlgTopCached.thy:18976`
- **Theorem:** `Theorem_70_1_universal_property`
- **Pattern:** Similar to Clone 3: proves subdivision parameter bounds for merged intervals.
- **Refactoring:** Same `subdivision_param_in_interval` lemma as Clone 3.

### Clone 13: Product topology basis (316 tokens, 72 lines) -- CROSS-FILE
- **Files:** `i/Top1_Ch2.thy:402` vs `i/Top1_Ch4.thy:873`
- **Theorems:** `Theorem_30_2_first_countable_product` (Ch4) reuses pattern from Ch2
- **Pattern:** Constructs basic open sets in product topology from factor opens. Proves membership via Pi-extensionality.
- **Refactoring:** Extract `product_topology_basic_open_membership` lemma.
- **Difficulty:** Easy-Medium. Only cross-file clone.

---

## 3. Pattern Categories

### A. Covering space sheet/angle extraction (Clones 2, 4, 6)
**Total:** ~1835 tokens
**Location:** `Theorem_71_1_wedge_of_circles_finite`
**Action:** Extract `S1_point_to_angle` and `covering_sheet_at_point` lemmas.

### B. Helix covering construction + path lifting (Clones 1, 7)
**Total:** ~1442 tokens
**Location:** `a0/AlgTop0.thy`
**Action:** Extract `helix_covering_setup` (returns E,TE,p0,e0) and `helix_lift_is_path` (generic path lifting in helix).

### C. Subdivision parameter bounds (Clones 3, 10)
**Total:** ~823 tokens
**Location:** SvK proofs in `AlgTopCached.thy`
**Action:** Extract `affine_param_in_subinterval`:
```
lemma affine_param_in_subinterval:
  assumes "a < b" "0 <= t" "t <= 1" "a >= lo" "b <= hi"
  shows "lo <= a + t * (b - a)" "a + t * (b - a) <= hi"
```

### D. Basepoint change class manipulation (Clone 5)
**Total:** ~359 tokens
**Location:** `Theorem_72_1_attaching_two_cell`
**Action:** Extract `basepoint_change_induced_class_eq`.

### E. Product topology basis membership (Clones 8, 13)
**Total:** ~657 tokens
**Location:** `Top1_Ch2.thy`, `Top1_Ch4.thy`
**Action:** Extract `product_topology_basis_membership` into a shared utility.

---

## 4. Recommendations

### Priority 1: Easy wins (can do now)
1. **`affine_param_in_subinterval`** (Category C) -- Pure real arithmetic, no context dependency. Extract from SvK proofs. ~30 lines, saves ~800 tokens.
2. **`helix_covering_setup`** (Category B, Clone 7) -- Move shared definitions (E, TE, p0, e0) to a single place. ~30 lines, saves ~340 tokens.
3. **`S1_point_to_angle`** (Category A, Clone 4) -- Given p on S1, get theta with R_to_S1(theta)=p. ~25 lines, saves ~420 tokens.

### Priority 2: Medium effort
4. **`helix_lift_is_path`** (Category B, Clone 1) -- Parameterize the path lifting by integer label and path direction. ~60 lines, saves ~1100 tokens.
5. **`basepoint_change_induced_class_eq`** (Category D) -- ~40 lines, saves ~360 tokens.
6. **`covering_sheet_at_point`** (Category A) -- ~50 lines, saves ~700 tokens.

### Priority 3: Hard (deep context)
7. **Angle/sheet extraction in Thm 71.1** (Clone 2) -- Deeply embedded in proof, hard to extract.
8. **Product topology density** (Clone 8) -- Requires parameterizing over box/product topology.
9. **Bounded metric sup** (Clone 9) -- Complex analysis context.

### Risk assessment
- Clones in **cached sessions** (Top0, AlgTopBase, AlgTopCached): Modifying these triggers full rebuild (~2+ min). Only refactor if the savings are significant.
- Clones in **AlgTop.thy**: Can modify freely (10s build).
- **Cross-file clone** (Clone 13, Ch2 vs Ch4): Requires adding to Ch2 and using from Ch4. Triggers Top0 rebuild.

### Estimated total savings
If priorities 1-6 are implemented: ~3700 tokens saved, 6 reusable lemmas added, improved maintainability.

---

## 5. Files to touch

| Lemma | Add to | Used by | Rebuild cost |
|-------|--------|---------|-------------|
| affine_param_in_subinterval | AlgTopCached.thy | SvK, Thm 70.1 | AlgTopC (~97s first time) |
| helix_covering_setup | a0/AlgTop0.thy | helix_g_lift, Thm 63.1 | AlgTop0 (~30s) |
| S1_point_to_angle | ac/AlgTopCached.thy | Thm 71.1 | AlgTopC |
| helix_lift_is_path | a0/AlgTop0.thy | Thm 63.1 variants | AlgTop0 |
| basepoint_change_induced_class_eq | ac/AlgTopCached.thy | Thm 72.1 | AlgTopC |
| covering_sheet_at_point | ac/AlgTopCached.thy | Thm 71.1 | AlgTopC |
