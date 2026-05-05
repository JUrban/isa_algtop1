# Response to Expert Review — 2026-05-05

## Finding 1: `top1_free_group_universal_prop` is vacuous
**REAL but UNUSED.** The `<->` with `->` makes it vacuously true when H is not a group.
Also missing `G is group` and `iota(S) subset G` preconditions.

However: this definition is **never used in any proved theorem**. The only reference
is in a comment at AlgTop.thy:229. The actual free group definition used everywhere is
`top1_is_free_group_full_on` (AlgTopCached:6844) which is defined via reduced words
and IS well-formed (requires G is group, iota injective, iota(S) subset G, etc.).

**Verdict: Real bug in an unused definition. Should be fixed for hygiene, but no
theorems are affected.**

## Finding 2: Free abelian group SOME ordering
**REAL concern, logically sound.** The definition (AlgTopCached:6874) uses
`SOME xs. set xs = {s in S. c s != 0} /\ distinct xs` then `foldr mul (map ...) e`.

In an abelian group, `foldr mul` over any permutation gives the same result
(commutativity + associativity). But this needs to be PROVED as a separate lemma
for each use — the definition doesn't "know" this automatically.

The definition IS correct: the SOME picks a deterministic ordering for each c,
and since abelian laws hold (required by `top1_is_abelian_group_on`), any ordering
would give the same value. No theorem could be incorrect because of this.

**Verdict: Valid design concern (fragile, non-canonical), but not a soundness bug.
Using finsum/multiset would be cleaner but doesn't affect correctness.**

## Finding 3: Group presentation type restriction
**PARTIALLY REAL.** The reviewer raised two issues:

(a) Identity: `top1_group_kernel_on F e pi` uses `e` as the codomain identity.
Since `e` comes from `top1_is_group_on G mul e invg`, this is the G-identity. CORRECT.

(b) Type: `F :: 'g set` forces the free group to have the same carrier type as G.
This IS an artificial restriction — a free group on generators S normally has a
different type (word lists) than the presented group.

In practice: the existential `exists (F::'g set)...` can be satisfied when G's type
is rich enough (e.g., G = Z/nZ can use F as a subset of the same int type). But for
more complex presentations this type restriction could block instantiation.

**Verdict: The identity is correct. The same-type restriction is a real limitation
that could block some constructions, similar to the oops'd Theorem_70_2_SvK.**

## Finding 4: Free product misses factor group axioms
**REAL but benign.** The definition `top1_is_free_product_on` (AlgTopCached:6919)
requires `iota_fam` to be homomorphic and injective, but does NOT require
`top1_is_group_on (GG alpha) ...` as a conjunct.

The reduced-word condition checks `iota_fam(alpha)(word!i) != e` (ambient identity,
not factor identity). This is equivalent to `word!i != e_alpha` ONLY IF the homomorphism
preserves identities — which follows from group-hom + injectivity, BUT the definition
doesn't state GG(alpha) is a group!

In practice: EVERY theorem that uses this definition also provides the group axioms
for GG(alpha) as a separate assumption (e.g., `Theorem_68_2` at AlgTopCached:9600).
So no proved theorem is incorrect.

**Verdict: Missing group precondition makes the definition weaker than intended.
All theorems separately assume it, so no soundness issue.**

## Finding 5: Winding number partial/underspecified
**REAL but UNUSED.** `top1_winding_number_on` (AlgTopCached:6029) uses `SOME n`
which gives garbage for invalid inputs (f hitting origin, non-loops, etc.).

This definition is **never used in any theorem** — it's only the definition itself.
No lemma or theorem references `top1_winding_number_on` anywhere.

**Verdict: Real design flaw in an unused definition. No impact on any theorem.**

## Finding 6: Borsuk/invariance specialized
**VALID observation, not a bug.** `Lemma_62_1` and `Theorem_62_3` are for R^2 only.
The textbook results hold for R^n. This is a deliberate specialization sufficient
for the Jordan curve theorem (our main application). The comments don't explicitly
flag this as R^2-only.

**Verdict: Valid observation. Comments should note the R^2 specialization.**

## Finding 7: `frontier` is ambient-UNIV only
**VALID observation, not currently a bug.** The `frontier` definition (AlgTopCached:3578)
uses `open U` and complement `- S` in the type universe, not relative to a subspace.

Currently `frontier` is ONLY used in the invariance-of-domain proof (AlgTopCached:3582-5000)
which works in R^2 (full ambient space). No subspace-relative frontier is needed.

If future proofs need relative frontier (e.g., frontier in a subspace), this definition
would be wrong. But no current theorem is affected.

**Verdict: Correct for current use. Would need a relative version for subspace arguments.**

## Finding 8: SvK oops
**Already documented.** The oops'd `Theorem_70_2_SvK` is not used by any downstream
theorem. The parameterized version `Theorem_70_2_SvK_parameterized` (AlgTopCached:25801)
is fully proved and used instead.

**Verdict: Known, documented, no impact.**

## Finding 9: Theorem 70.1 uniqueness
**Already documented and addressed.** `Theorem_70_1_uniqueness` stated at AlgTop.thy:11
with sorry. Proof via Theorem 59.1.

**Verdict: Known, fix in progress.**

## Finding 10: Polygonal quotient under-specifies equivalence relation
**PARTIALLY REAL.** The definition (AlgTop.thy:389) constrains:
- Same-label edges identified (lines 409-418)
- Interior points have singleton q-fiber (lines 420-423)

But does NOT say boundary points on DIFFERENT-label edges must NOT be identified.
A quotient map q that makes additional boundary identifications beyond the scheme
would still satisfy the definition, producing a different (more collapsed) space.

However:
1. The definition is used as a HYPOTHESIS in theorems ("if X is a polygonal quotient,
   then..."). A permissive hypothesis makes theorems WEAKER, not incorrect.
2. Specific surface definitions (torus, projective, dunce cap) include the scheme
   explicitly, further constraining the quotient.
3. In practice, the quotient map from a compact polygon with the specified edge IDs
   and interior injectivity is essentially unique up to homeomorphism.

**Verdict: The definition admits non-standard quotients, making some theorems
slightly weaker than they need to be. Not a soundness bug — theorems proved
about polygonal quotients apply to more spaces than intended, not fewer.
Could be strengthened by adding: "q identifies boundary points ONLY as required
by the scheme."**

---

## Summary: Impact Classification

| # | Finding | Real? | Affects Theorems? | Priority |
|---|---------|-------|-------------------|----------|
| 1 | free_group_universal_prop vacuous | Yes | **No** (unused def) | Low |
| 2 | free abelian SOME ordering | Design concern | No (abelian laws suffice) | Low |
| 3 | presentation type restriction | Yes (type issue) | **Possibly** (blocks some) | Medium |
| 4 | free product missing group axiom | Yes (weak def) | No (all uses provide it) | Low |
| 5 | winding number partial | Yes | **No** (unused def) | Low |
| 6 | Borsuk/invariance R^2 only | Valid | No (deliberate) | Low |
| 7 | frontier ambient-UNIV | Valid | No (current use OK) | Low |
| 8 | SvK oops | Known | No | Already addressed |
| 9 | 70.1 uniqueness | Known | Yes (weakened thm) | **High** |
| 10 | polygonal quotient permissive | Partially | Weakens theorems | Medium |

**Bottom line:** Findings 1, 4, 5 are real bugs in definitions that are either unused or
whose weakness is compensated by extra assumptions at every use site. Finding 9 is already
addressed. Finding 3 and 10 are the ones most worth fixing — the type restriction in
presentations parallels the oops'd SvK issue, and the polygonal quotient could be
tightened with one extra conjunct.
