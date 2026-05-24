# Plan 8: Reduce Theorem_74_2 to one sorry, then prove the missing wedge generator theorem

## Honest status

- 46 AlgTop sorrys, 0 PolygonDisk sorrys
- 75.3 chain has 3 direct sorrys in Theorem_74_2:
  1. `hφ_bij` (~7992): φ bijective — the HARD remaining problem
  2. Two small `hrel_eq` sorrys (~8507, ~8517): λ/comp form conversion — bookkeeping
- Closing hrel_eq does NOT close the 75.3 chain. hφ_bij remains.
- Closing hφ_bij requires a witnessed finite wedge generator theorem that does not exist yet.

## What this plan actually does

**Phase A**: Close the two hrel_eq bookkeeping sorrys (λ/comp conversion).
This reduces Theorem_74_2 from 3 chain sorrys to 1 (hφ_bij only).

**Phase B**: Prove the missing wedge generator theorem. This is the REAL work.
Without it, the 75.3 chain stays open.

**Phase C**: Derive hφ_bij from Phase B. Remove quick_and_dirty. Verify strict build.

## Phase A: Close hrel_eq (bookkeeping)

The two remaining hrel_eq sorrys are about converting between
`λs. ι(circle s)` and `ι ∘ circle` forms in loop_equiv_on.
Both functions agree pointwise. The tool `hloop_class_eq_pointwise` handles
pointwise-equal functions on I_set, but the issue is that `λs. ι(f s)` and
`ι ∘ f` are not syntactically equal in Isabelle (though extensionally equal).

Fix: prove `∀t. (λs. ι(circle s)) t = (ι ∘ circle) t` by unfolding comp_def,
then use `ext` to get extensional equality, then substitute.

Estimated: ~20 lines.

## Phase B: Prove the witnessed wedge generator theorem

This is the theorem the expert identified as missing. It says:
given explicit circle data (C_k, homeomorphisms g_k, basepoints),
the loop classes form a free basis of π₁(A, a).

### Option B1: Prove locally inside Theorem_74_2

Add a local `have` that proves the edge loop classes form a free basis,
using the SvK decomposition of the wedge A = C_0 ∪ ... ∪ C_{n-1}.

This requires finite induction on the number of circles:
- Base (1 circle): π₁(C_0) ≅ Z, generator = circle loop class.
- Step (n circles → n+1): A_{n+1} = A_n ∪ C_n. By SvK (intersection = {a},
  simply connected), π₁(A_{n+1}) ≅ π₁(A_n) * π₁(C_n). By IH, π₁(A_n) is
  free on loops 0..n-1. π₁(C_n) ≅ Z on loop n. Free product = free on 0..n.
  The isomorphism maps each generator to the corresponding loop class because
  the SvK construction uses the inclusion-induced maps.

The key difficulty: the SvK theorem (Theorem 70.2 / Corollary 70.3) in the
formalization returns an abstract free product isomorphism. Tracking where
generators go through the SvK construction requires either:
(a) Modifying the SvK output to also state generator images, or
(b) Using the universal property of free products to reconstruct the mapping.

Approach (b) is feasible without modifying cached sessions:
- SvK gives π₁(A) ≅ π₁(A') * π₁(C_n) (abstract)
- The inclusion maps ι₁: A' → A and ι₂: C_n → A induce homomorphisms
  on π₁ that compose with the SvK isomorphism
- The universal property of the free product says the induced maps
  determine the isomorphism uniquely
- Since the induced maps send loop classes to loop classes, the
  SvK isomorphism maps generators to loop classes

This is ~200-400 lines of new proof. It is the REAL remaining work.

### Option B2: Add standalone lemma before Theorem_74_2

Prove `finite_wedge_pi1_free_with_chosen_loops` as a standalone lemma.
Same proof as B1 but reusable. Better software engineering but same effort.

### Honest estimate

Phase B is 200-400 lines of nontrivial algebraic topology. It requires:
- Understanding the SvK free product construction in the formalization
- Tracking inclusion-induced maps through the construction
- Finite induction with generator correspondence at each step

This is the LAST real mathematical gap in the 75.3 chain.

## Phase C: Integration and verification

1. Derive hφ_bij from Phase B result (trivial: the theorem gives both
   bijectivity and generator images).
2. Remove `quick_and_dirty` from AlgTop session in ROOT.
3. Build strict: `cd /project/tst && /project/bin/isabelle build -D .`
4. Verify: `grep -c "sorry" AlgTop.thy` shows reduction.

## What this plan does NOT promise

- It does NOT promise to close the entire 75.3 chain in one session.
  Phase B is ~200-400 lines of nontrivial proof that may take multiple sessions.
- It does NOT use the Hopfian property. The generator correspondence
  comes FROM the SvK construction, not from a separate injectivity argument.
- It does NOT modify AlgTopCached.thy (the 8000-line cached session).

## What IS already proved (not re-proved)

- word_product_foldr_class (ZERO SORRY)
- foldr_path_product_pointwise_eq (ZERO SORRY)
- hsub_class True/False (ZERO SORRY)
- hloop_class_eq_pointwise (ZERO SORRY)
- continuous_preserves_path_homotopic (in Top1_Ch9_13)
- fundamental_group_invg_class (in AlgTopCached)
- top1_fundamental_group_mul_class (in Top1_Ch9_13)
- All PolygonDisk (ZERO SORRY, strict mode)
- All edge-to-arc chain (ZERO SORRY)
- hbdy_loop, hvertex, hbdy_split, hbdy_class, hsub_edge (PROVED)
