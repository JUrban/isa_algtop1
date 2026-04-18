# Priorities and Issues for AlgTop Formalization

## A. Statement/Definitional Fixes Needed

### A1. Theorem_80_1_universal_unique: Missing basepoint membership (BLOCKING)

**Location:** Line 14081  
**Issue:** The theorem assumes `p e0 = b0` and `p' e0' = b0` but does NOT assume `e0 ∈ E` or `e0' ∈ E'`. Since functions in HOL are total, `p e0 = b0` alone doesn't guarantee `e0 ∈ E`. This makes `b0 ∈ B` underivable, blocking the fundamental group image computation.

**Fix:** Add assumptions:
```isabelle
and "e0 ∈ E" and "e0' ∈ E'"
```

**Impact:** Unblocks the trivial-subgroup computation and the Theorem_79_4 application.

### A2. Theorem_57_1 (Borsuk-Ulam): Missing WLOG h(b₀) = b₀ (IMPORTANT)

**Location:** Line 8422  
**Issue:** Munkres' proof says "WLOG h(b₀) = b₀" by rotation. The formalization skips this step. The `hh_star_trivial` fact (line 8452) uses `const (h (1,0))` as the target, but `path_homotopic_on` at basepoint `(1,0)` requires `h(1,0) = (1,0)` for the `is_path_on` conditions to hold. Without this, `hh_star_trivial` is unprovable.

**Fix (option 1):** Add WLOG reduction. Before the main proof, show that if Theorem_57_1 fails, there exists an antipode-preserving h' with h'(1,0) = (1,0) that is also nulhomotopic, and derive contradiction for h'.

**Fix (option 2):** Add assumption `h (1,0) = (1,0)` and adjust the overall Borsuk-Ulam argument to rotate first.

**Impact:** Unblocks the 6 sorries in Theorem_57_1.

### A3. `top1_separates_on` definition: No C ⊆ X condition (COSMETIC)

**Location:** Line ~11479  
**Current:** `¬ connected(X - C)` without requiring `C ⊆ X`.  
**Munkres:** Separates requires C ⊆ X.  
**Impact:** The definition works correctly (if C ⊄ X, the result is still well-defined), but some proofs may need `C ⊆ X` explicitly. Currently handled ad-hoc. Low priority.

---

## B. Top Priorities for Proof Progress

### B1. π₁(S¹) ≅ ℤ as a group isomorphism (HIGHEST PRIORITY)

**Location:** Line 5841  
**Status:** Bijection exists (Theorem_54_5). Homomorphism property needed.  
**What's needed:**
- Formalize that the lift of f*g equals the concatenation of lift(f) with translated-lift(g)
- Specifically: if lift(f,0) ends at n and lift(g,0) ends at m, then lift(f*g,0) ends at n+m
- This requires a lemma about `p(n + x) = p(x)` for the covering map p: ℝ → S¹

**Unblocks:** FTA Steps 1-2 (3 sorries), Theorem 57.1 chain (6+ sorries), total ~10 sorries.

### B2. Covering space path lifting (Lemma 54.1)

**Location:** Lines 4496, 4502  
**What's needed:** Lebesgue number argument for subdividing [0,1] so each subinterval maps into an evenly covered set, then lift interval-by-interval.  
**Unblocks:** Path lifting uniqueness, homotopy lifting, π₁(S¹) computation.

### B3. R → S¹ is a covering map (Theorem 53.1)

**Location:** Line 4190  
**What's needed:** Show every point of S¹ has an evenly covered neighborhood under p(t) = (cos 2πt, sin 2πt). Requires constructing the 4 standard open arcs.  
**Unblocks:** All covering space applications for S¹.

### B4. `hh_star_trivial` from nulhomotopy (Theorem 57.1)

**Location:** Line 8455  
**Status:** Nearly provable using `homotopy_induced_basepoint_change` + path algebra.  
**Prerequisite:** Fix A2 (WLOG h(b₀)=b₀) first.  
**Unblocks:** Theorem 57.1, which unblocks Borsuk-Ulam (57.3) and its applications.

---

## C. Verified Correct (No Fixes Needed)

- **`hj_inj` statement (line 8027):** CORRECT. j_* injective means "homotopic in C-{0} ⟹ homotopic in S¹" (not reversed).
- **All definitions** (`nulhomotopic_on`, `homotopic_on`, `separates_on`, `simple_closed_curve_on`, `universal_covering_on`): Match Munkres.
- **FTA Step 3-4:** Fully proved, no issues.
- **Theorem_58_7:** Fully proved, no issues.
- **Type separation** (complex vs real×real for S¹): Deliberate design choice, not a bug. Creates duplicate work but is structurally sound.

---

## D. Recommended Work Order

1. **Fix A1** (Theorem_80_1 assumptions) — 5 min, unblocks Ch. 13
2. **Fix A2** (Theorem_57_1 WLOG) — 30 min, unblocks Borsuk-Ulam chain
3. **Prove B4** (hh_star_trivial) — 1 hour, uses existing infrastructure
4. **Prove B3** (R→S¹ covering) — 2-3 hours, foundational
5. **Prove B2** (path lifting) — 2-3 hours, foundational
6. **Prove B1** (π₁(S¹) homomorphism) — 3-4 hours, the key domino
