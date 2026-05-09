# Plan: Fix Lemma_65_1 Statement and Proof

## Problem (Reviewer Criticism)

The cached `Lemma_65_1_K4_subgraph` (AlgTopCached.thy:55058) has a **too-weak conclusion**:

```isabelle
shows "\<exists>x \<in> C. \<exists>g. top1_is_loop_on ... x g
  \<and> \<not> top1_path_homotopic_on ... x x g (top1_constant_path x)"
```

This only says "there exists some nontrivial loop at some point of C."

**Textbook (Munkres Lemma 65.1):** The inclusion j: C -> S^2-{p,q} induces an **isomorphism** of fundamental groups. The proof constructs alpha*beta traversing C and shows it **generates** pi_1(S^2-{p,q}).

## What the Textbook Proof Actually Does

From algtop.tex lines 2397-2435:

1. **Part (a):** p and q lie in different components of S^2-C.
   (Uses theta space C cup a1a3, Lemma 64.1.)

2. **Part (b):** Define:
   - x = interior point of e12, y = interior point of e34
   - alpha = path x->a1->a4->y (in U = S^2-D1)
   - beta = path y->a3->a2->x (in V = S^2-D2)
   - D1 = arc p->a3->a2->q (subarc of e13 + e23 + subarc of e24)
   - D2 = arc q->a4->a1->p (subarc of e24 + e41 + subarc of e13)
   - U = S^2-D1, V = S^2-D2

   Then X = S^2-{p,q} = U cup V. U cap V = S^2-D where D = D1 cup D2 is a
   simple closed curve. By JCT, U cap V has two components. By part (a),
   x and y lie in different components.

   By Theorem 63.1: alpha*beta is nontrivial. Since pi_1(X) is infinite
   cyclic, alpha*beta represents a **generator**. Since alpha*beta lies in C,
   j_*: pi_1(C,x) -> pi_1(X,x) is surjective, hence an isomorphism.

## What the Existing Proof Establishes

The ~1500-line cached proof (lines 55100-58707) DOES:
- Construct alpha, beta as paths traversing parts of C
- Construct the decomposition X = U' cup V' where U' = X cap (S^2-e13), V' = X cap (S^2-e24)
- Show U' cap V' has two components A, B with x in A, y in B
- Apply `Theorem_63_1_loop_nontrivial` to get alpha*beta nontrivial
- Show alpha*beta is a loop at x with image in C

But it ONLY concludes "exists nontrivial loop" -- discarding the structural info.

## Correct Conclusion

The conclusion should be the isomorphism:

```isabelle
shows "top1_groups_isomorphic_on
  (top1_fundamental_group_carrier C
    (subspace_topology top1_S2 top1_S2_topology C) c0)
  (top1_fundamental_group_mul C
    (subspace_topology top1_S2 top1_S2_topology C) c0)
  (top1_fundamental_group_carrier (top1_S2 - {p} - {q})
    (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0)
  (top1_fundamental_group_mul (top1_S2 - {p} - {q})
    (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0)"
```

where c0 is any point of C (the basepoint).

## Implementation Plan

### Phase 1: New Lemma Statement (in AlgTop.thy)

Add `Lemma_65_1_K4_isomorphism` with the correct conclusion (isomorphism).
Keep the same K4 assumptions as the existing cached version.
Add `c0 \<in> C` as an assumption for the basepoint.

### Phase 2: Proof Strategy (following algtop.tex)

The proof derives the isomorphism from the existing nontriviality + SvK structure.

**Step 1: Surjectivity of j_*.**

Key available lemma: `SvK_simply_connected_V_surj_kernel` (AlgTopCached.thy:42587):
```
When V simply connected, U cap V path-connected, U path-connected:
  i_U_*: pi_1(U,x0) -> pi_1(X,x0) is SURJECTIVE
```

Apply with U = S^2-D1, V = S^2-D2 (following textbook):
- Need: V = S^2-D2 is simply connected (S^2 minus an arc)
- Need: U = S^2-D1 is path-connected
- Need: U cap V path-connected
- C subset U (since C avoids D1 except at vertices, which are not in D1)

Then i_U surjective. Since C subset U and the inclusion C -> X factors
through U, j_* surjective follows if we show i_C->U is surjective.

Actually, a simpler approach: both U and V are simply connected
(S^2 minus an arc is simply connected, by `Corollary_59_2` or direct
argument). Then by `Corollary_70_3_simply_connected_intersection`:
pi_1(X) is isomorphic to the free product of pi_1(U)*pi_1(V) = {1}*{1}.
But U cap V has two components, so pi_1(X) = Z (free group on one
generator). And the generator is [alpha*beta].

Even simpler: use `SvK_simply_connected_V_surj_kernel` with one of U, V
simply connected. Then the OTHER inclusion is surjective. Since C lies
in the other set, j_* is surjective.

**Step 2: Injectivity of j_*.**

Since pi_1(C) ~ Z and pi_1(X) ~ Z, and j_* is a surjective homomorphism
Z -> Z, it must map generator to +/-generator, hence injective.

Alternatively: any surjective homomorphism Z -> Z is an isomorphism.

**Step 3: Combine.**

j_* is a group homomorphism (functoriality of pi_1) + surjective + injective
= isomorphism.

### Phase 3: Prerequisites

Need to establish:
1. S^2 minus an arc is simply connected (may need a helper lemma)
2. D1 and D2 ARE arcs (sub-arcs of the K4 edges, concatenated)
3. C subset S^2-{p}-{q} (follows from intersection assumptions)
4. The decomposition X = U cup V with U cap V having two components

Items 1-2 may need significant infrastructure.
Item 3 should follow from the existing K4 intersection conditions.
Item 4 is partially available from the existing cached proof.

### Phase 4: Integration

Once Lemma_65_1_K4_isomorphism is proved, use it to close the
hj_surj and hj_inj sorrys in Theorem_65_2 (or merge the two).

## Dependencies

- `Theorem_63_1_loop_nontrivial` (available in AlgTop0)
- `SvK_simply_connected_V_surj_kernel` (available in AlgTopCached)
- `Corollary_70_3_simply_connected_intersection` (available in AlgTopCached)
- S^2 minus arc is simply connected (may need to prove)
- `top1_groups_isomorphic_on` composition/transfer lemmas

## Risk Assessment

- **High risk:** S^2 minus an arc simply connected -- may need substantial work
- **Medium risk:** D1, D2 construction as arcs from sub-arcs of K4 edges
- **Low risk:** Surjectivity/injectivity once SvK applied correctly
- **Low risk:** Integration with Theorem_65_2

## Estimated Effort

- Phase 1 (statement): ~20 lines
- Phase 2 (surjectivity via SvK): ~100-150 lines
- Phase 2 (injectivity): ~30 lines
- Phase 3 (prerequisites): ~50-200 lines (depending on S^2 minus arc)
- Phase 4 (integration): ~20 lines
- Total: ~220-420 lines
