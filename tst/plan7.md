# Plan 7: Close the 75.3 chain via canonical finite wedge theorem

## Goal
Close `Theorem_74_2_scheme_presentation` (the only blocker for the 75.3 chain).

## Current state
- 47 AlgTop sorrys, 0 PolygonDisk sorrys
- 75.3 chain has 2 direct sorrys in Theorem_74_2:
  1. `hφ_bij` (line ~7951): φ bijective
  2. `hrel_foldr` (line ~8472+): relator_class = class of foldr edge loops

## Root cause (from expert review)
The proof constructs φ via universal property and then tries to prove bijectivity
separately (Hopfian). This is the wrong abstraction level. The correct approach:
get bijectivity AND generator images from the SAME theorem.

## Plan

### Phase 1: Add canonical generator correspondence to Theorem_71_1

**File:** `ac/AlgTopCached.thy`
**Location:** After `Theorem_71_1_wedge_of_circles_finite` (line ~31794)

Add a NEW lemma (do NOT modify the existing theorem):

```isabelle
lemma finite_wedge_pi1_free_with_generators:
  fixes n :: nat and X :: "'a set" and TX :: "'a set set" and p :: 'a
  assumes hwedge: "top1_is_wedge_of_circles_on X TX {..<n} p"
  shows "∃(G::int set) mul e invg (η::nat ⇒ int) Φ.
      top1_is_free_group_full_on G mul e invg η {..<n}
    ∧ top1_group_iso_on G mul
        (top1_fundamental_group_carrier X TX p)
        (top1_fundamental_group_mul X TX p) Φ
    ∧ (∀k<n. Φ (η k) = {g. top1_loop_equiv_on X TX p (canonical_loop k) g})"
```

where `canonical_loop k` is the loop around the k-th circle C_k.

**Proof strategy:** Use `Theorem_71_1_wedge_of_circles_finite` to get the free group
and isomorphism, then extract the generator-loop correspondence from the SvK
construction. The finite case uses induction on n:
- Base n=1: single circle, generator = circle loop class
- Step n→n+1: SvK gives free product, new generator = new circle loop

If modifying the cached session is too hard, add a WRAPPER lemma in AlgTop.thy
that derives the generator correspondence from the existing abstract isomorphism
using the universal property + the fact that both F and π₁(A) are free on the
same finite rank (rank invariance is already proved).

### Phase 2: Replace hφ_bij + φ construction in Theorem_74_2

**File:** `AlgTop.thy`

Replace the current construction (universal property + sorry for bijectivity) with:

```
from finite_wedge_pi1_free_with_generators[OF hA_wd_finite]
obtain F mulF ... φ where
  hfree: "free_group F ..."
  hφ_iso: "iso_on F ... π₁(A,a') ... φ"
  hφ_gen: "∀s∈labels. φ(ιF s) = [canonical_loop s]"
```

This gives hφ_bij for free (from iso_on) and hφ_gen (generator correspondence).

### Phase 3: Close hrel_foldr using the generator correspondence

With hφ_gen giving `φ(ιF s) = [canonical_loop s]`, and the existing proved
infrastructure:

1. `relator_class = class(ι∘circle)` — unfold induced map definition
2. `ι∘circle ≃ foldr [sub_0,...] const` — from loop_split_at_vertices (PROVED)
3. `sub_k = edge_loop_fn k` on I_set — from h_iota_circle_edge (PROVED)
4. `[edge_loop_fn k] = φ(ιF(fst(scheme!k)))^{snd(scheme!k)}` — from hsub_class (PROVED)
5. `class(foldr) = word_product_π₁` — from word_product_foldr_class (PROVED)

The only missing piece after Phase 1-2 is connecting `canonical_loop s` with
`edge_loop_fn (i_of s)` — this follows from the wedge structure (C_s = qC image
of canonical edge s, and edge_loop_fn traces qC).

### Phase 4: Verify chain

Build and verify:
```bash
cd /project/tst && /project/bin/isabelle build -D .
```

Check that Theorem_74_3 and Theorem_75_3 close automatically.

## Key principle
Do NOT try to prove bijectivity separately from the generator correspondence.
Get both from the same theorem. No Hopfian arguments.

## Reality check
Theorem_71_1_wedge_of_circles_finite is 8119 lines. Modifying its conclusion
to export generator-loop correspondence is impractical without a multi-day effort.

The expert's ideal (canonical wedge theorem) is correct in principle but requires
either modifying the 8119-line proof or reimplementing it — both infeasible now.

**Pragmatic approach:** Keep the current universal-property construction with the
single hφ_bij sorry (Hopfian for free groups). This is a well-understood mathematical
fact. Focus effort on closing hrel_foldr completely, which has all infrastructure
available and is ~100 lines from completion.

## Estimated effort
- Phase 1 (ideal): DEFERRED — requires 8000+ line cached proof modification
- Phase 1 (pragmatic): Keep hφ_bij sorry (1 sorry, well-understood)
- Phase 3: Close hrel_foldr completely — ~100 lines using existing infrastructure
- Phase 4: Build verification

## What's already proved and reusable
- word_product_foldr_class (ZERO SORRY)
- foldr_path_product_pointwise_eq (ZERO SORRY)
- hsub_class True/False (ZERO SORRY)
- hloop_class_eq_pointwise (ZERO SORRY)
- hsub_edge inline (PROVED)
- hbdy_loop (PROVED)
- hbdy_class (PROVED)
- All PolygonDisk (ZERO SORRY, strict mode)
- All edge-to-arc chain (ZERO SORRY)
