Yes — the plan is directionally good, but I would not let the worker implement it literally without tightening several statements first. My comments for him would be:

---

## Overall verdict

The plan has the right strategic diagnosis: **fix interfaces first, expose index sets/carriers, and stop optimizing for raw `sorry` count**. That is exactly the right standard for a zero-sorry finish. In particular, the guiding principles about avoiding polymorphic existential type escapes, preserving graph generator index sets, and building bottom-up infrastructure are sound. 

But the plan currently has several places where the proposed Isabelle objects are still too informal or type-confused. The most important corrections are:

1. The proposed `top1_is_graph_with_arcs_on X TX A` mixes up **a set of arcs** and **an indexed arc family**.
2. The graph fundamental-group theorem must have both a **finite-indexed theorem** and a **general arbitrary-index theorem**; the finite reindexing trick cannot prove the uncountable case.
3. The Euler characteristic definitions must use total edge count and integer arithmetic, not cotree-edge count and `nat` subtraction.
4. The claims “Theorem 82.1 packaging fixed” and “Nielsen-Schreier packaging fixed” look stale relative to the current live `AlgTop.thy`, where the §85 covering and transfer steps still contain executable `sorry`s. ([GitHub][1])
5. The surface-classification phase is conceptually right but under-specified; it needs a valid-scheme predicate and carefully separated combinatorial/topological layers.

The live `ROOT` still has the final `AlgTop` session under `options [quick_and_dirty, timeout = 600]`, so the plan’s final goal “compile without `quick_and_dirty`” remains essential, not optional. ([GitHub][2])

---

## 1. Add a Phase 0 before Phase A

Before adding `ac10`, the worker should add a small reproducibility/checking phase.

The current tree has many cache and backup-style directories, and the active `ROOT` imports the chain through `AlgTopCached9` before final `AlgTop`. ([GitHub][3]) So the first task should be:

```bash
grep -R --line-number '\bsorry\b\|\boops\b' tst \
  --include='*.thy'

grep -R --line-number 'quick_and_dirty' tst/ROOT
```

Then also run a **comment-stripping** count, because raw grep overcounts comments. The plan says “24 executable sorrys in `AlgTop.thy`, 2 oops in `ac/`,” which matched my audit at that time, but current comments/status blocks are already drifting. The worker should regenerate a machine-readable blocker table after every commit.

Recommended Phase 0 deliverables:

```text
BLOCKERS_CURRENT.md
  - exact commit SHA
  - exact Isabelle version
  - exact ROOT session used
  - executable sorry/oops count after comment stripping
  - theorem names containing each executable sorry
  - whether each one is statement-level, proof-level, or dependency-level
```

Do not trust the “Current status” section of the plan after further commits; regenerate it.

---

## 2. Phase A.1: fix the graph-with-arcs predicate before using it

The plan’s A.1 is right in spirit but type-wrong as written.

It proposes:

```isabelle
definition top1_is_graph_with_arcs_on X TX A where
  "top1_is_graph_with_arcs_on X TX A <->
     ...
     (ALL i : A. A i <= X & ...)
     Union (A ` UNIV) = X
     ..."
```

Here `A` is used both as:

```isabelle
A :: 'i set
```

and as:

```isabelle
A :: 'i ⇒ 'a set
```

That will not survive Isabelle type checking.

The current cached graph definition uses an **existential collection of arcs** inside `top1_is_graph_on`; it does not expose an external index family. ([GitHub][4]) Also, the active final file currently has no `top1_is_graph_with_arcs_on` symbol. ([GitHub][1])

I would implement two levels, not one.

### Low-risk compatibility predicate

First expose the old hidden collection:

```isabelle
definition top1_is_graph_with_arcset_on ::
  "'a set ⇒ 'a set set ⇒ 'a set set ⇒ bool"
where
  "top1_is_graph_with_arcset_on X TX 𝒜 ⟷
     is_topology_on_strict X TX ∧
     is_hausdorff_on X TX ∧
     (∀A∈𝒜. A ⊆ X ∧ top1_is_arc_on A (subspace_topology X TX A)) ∧
     ⋃𝒜 = X ∧
     (∀A∈𝒜. ∀B∈𝒜.
        A ≠ B ⟶
        A ∩ B ⊆ top1_arc_endpoints_on A (subspace_topology X TX A) ∩
                top1_arc_endpoints_on B (subspace_topology X TX B) ∧
        finite (A ∩ B) ∧ card (A ∩ B) ≤ 2) ∧
     (∀C⊆X.
        closedin_on X TX C ⟷
        (∀A∈𝒜. closedin_on A (subspace_topology X TX A) (A ∩ C)))"
```

Then prove:

```isabelle
lemma graph_with_arcset_imp_graph:
  "top1_is_graph_with_arcset_on X TX 𝒜 ⟹ top1_is_graph_on X TX"

lemma graph_imp_ex_graph_with_arcset:
  "top1_is_graph_on X TX ⟹ ∃𝒜. top1_is_graph_with_arcset_on X TX 𝒜"
```

Do **not** immediately use an iff as a simp rule everywhere. It may explode proof search by unfolding the existential graph structure.

### Proper indexed locale

For graph π₁ and Euler/rank, use an indexed version:

```isabelle
locale top1_graph_arcs =
  fixes X :: "'a set"
    and TX :: "'a set set"
    and I :: "'i set"
    and A :: "'i ⇒ 'a set"
  assumes strict: "is_topology_on_strict X TX"
    and haus: "is_hausdorff_on X TX"
    and arcs:
      "i ∈ I ⟹ A i ⊆ X ∧
        top1_is_arc_on (A i) (subspace_topology X TX (A i))"
    and cover: "⋃ (A ` I) = X"
    and inj_arcs: "inj_on A I"
    and intersections:
      "⟦i ∈ I; j ∈ I; i ≠ j⟧ ⟹
        A i ∩ A j ⊆
          top1_arc_endpoints_on (A i) (subspace_topology X TX (A i)) ∩
          top1_arc_endpoints_on (A j) (subspace_topology X TX (A j)) ∧
        finite (A i ∩ A j) ∧ card (A i ∩ A j) ≤ 2"
    and coherent_closed:
      "C ⊆ X ⟹
        closedin_on X TX C ⟷
        (∀i∈I. closedin_on (A i) (subspace_topology X TX (A i)) (A i ∩ C))"
```

The `inj_on A I` assumption is important. Without it, the same geometric arc can appear under two different indices, and then “free on cotree arcs” counts duplicate generators.

The conversion from the old existential set-of-arcs predicate can use the arc set itself as the index type:

```isabelle
I = 𝒜
A = id
```

This is the safest bridge from old code to new code.

---

## 3. Phase A.2: graph π₁ indexing needs two theorem layers

The plan’s finite reindexing idea is good, but it only fixes the **finite** theorem. It cannot be the general graph theorem.

The current live proof still has the old `idx`/`the_inv_into` style reindexing machinery near the graph π₁ proof, and the earlier `nat` basis issue is precisely what we want to remove. ([GitHub][1]) The current cache also already uses a `free_group_full_reindex` lemma in the SvK assembly, so the worker should reuse or generalize that instead of creating a duplicate with a slightly different API. ([GitHub][5])

The theorem structure should be:

```isabelle
theorem graph_pi1_free_finite_indexed:
  assumes "top1_graph_arcs X TX I A"
      and "top1_connected_on X TX"
      and "x0 ∈ X"
      and "finite I"
      and "T ⊆ I"
      and "top1_is_spanning_tree_indices X TX I A T"
  obtains gen where
    "top1_is_free_group_full_on
       (top1_fundamental_group_carrier X TX x0)
       (top1_fundamental_group_mul X TX x0)
       (top1_fundamental_group_id X TX x0)
       (top1_fundamental_group_invg X TX x0)
       gen
       (I - T)"
```

and separately:

```isabelle
theorem graph_pi1_free_indexed:
  assumes "top1_graph_arcs X TX I A"
      and "top1_connected_on X TX"
      and "x0 ∈ X"
      and "T ⊆ I"
      and "top1_is_spanning_tree_indices X TX I A T"
  obtains gen where
    "top1_is_free_group_full_on
       (top1_fundamental_group_carrier X TX x0)
       (top1_fundamental_group_mul X TX x0)
       (top1_fundamental_group_id X TX x0)
       (top1_fundamental_group_invg X TX x0)
       gen
       (I - T)"
```

The finite theorem can be obtained from the existing finite SvK proof plus a bijection:

```isabelle
lemma free_group_full_reindex_bij:
  assumes h:
    "top1_is_free_group_full_on G mul e invg gen_old J"
  assumes bij:
    "bij_betw f I J"
  shows
    "top1_is_free_group_full_on G mul e invg (gen_old ∘ f) I"
```

But the general theorem requires the direct-limit/finite-support argument:

1. Every loop image is compact.
2. Every compact loop image is contained in a finite subgraph.
3. Word nontriviality is checked in a finite subgraph.
4. Inclusion from finite subgraph into larger graph is injective.
5. Therefore the full group is free on all cotree indices.

The plan mentions “infinite case skeleton,” but it should state explicitly that **no nat reindexing is allowed in the infinite theorem**.

---

## 4. Phase A.3: graph semilocal simple-connectedness is still more open than the plan says

The plan says the interior case already works and the vertex case needs `arc_sub_arc_covering_compact`. That looks stale.

In the current live `AlgTop.thy`, `arc_locally_path_connected` still has a `sorry` for `[0,1]` local path-connectedness, and `graph_semilocally_simply_connected` still has separate `sorry`s for the interior and vertex cases. ([GitHub][1])

So the immediate order should be:

1. Extract the existing `[0,1]` lpc proof into a reusable theorem:

   ```isabelle
   lemma I_set_locally_path_connected:
     "top1_locally_path_connected_on I_set I_top"
   ```

2. Replace the local `sorry` inside:

   ```isabelle
   lemma arc_locally_path_connected:
     assumes "top1_is_arc_on A (subspace_topology X TX A)"
         and "is_topology_on X TX"
         and "A ⊆ X"
     shows "top1_locally_path_connected_on A (subspace_topology X TX A)"
   ```

3. Only then close the interior chart case.

4. Then work on vertex stars.

For the vertex star, the plan’s compactness argument needs to be formalized very carefully. “A compact loop image meets finitely many arcs” is not a free theorem unless the graph definition gives you a discrete selection set. The existing cached infrastructure includes a `graph_selection_set_discrete`-style lemma and compact-discrete-finite machinery, which is the right path. ([GitHub][4])

A robust lemma target is:

```isabelle
lemma compact_graph_image_meets_finitely_many_arcs_away_from_base:
  assumes "top1_graph_arcs X TX I A"
      and "top1_compact_on K (subspace_topology X TX K)"
      and "K ⊆ X"
  shows "finite {i∈I. K ∩ relative_interior_arc (A i) ≠ {}}"
```

For the interval endpoint sublemma, use a precise real-analysis lemma:

```isabelle
lemma compact_subset_I_less_than_1_has_bound:
  assumes "compact K"
      and "K ⊆ {0..<1::real}"
  shows "∃r<1. K ⊆ {0..r}"
```

Handle `K = {}` separately; for nonempty `K`, use compactness to get `Sup K ∈ K`, hence `Sup K < 1`.

---

## 5. Phase A.4: Euler characteristic definitions need correction

The proposed definitions are not yet mathematically safe:

```isabelle
definition top1_graph_edge_count X TX A = card {i. A i not in T}
definition top1_graph_euler_char X TX A = card(vertices) - card(edges)
```

Problems:

1. `card {i. A i not in T}` is **cotree edge count**, i.e. rank, not total edge count.
2. Euler characteristic is `#vertices - #edges`, using total edges.
3. In Isabelle, `card V - card E` is `nat` subtraction and truncates at zero. For graphs with more edges than vertices, this destroys the negative Euler characteristic needed for Schreier.
4. `T` should not appear in the definition of edge count or Euler characteristic.

Use `int`:

```isabelle
definition graph_vertex_set where
  "graph_vertex_set I A =
     ⋃ i∈I. top1_arc_endpoints_on (A i) ..."

definition graph_edge_count where
  "graph_edge_count I = card I"

definition graph_euler_char where
  "graph_euler_char I A =
     int (card (graph_vertex_set I A)) - int (card I)"
```

Then prove rank as an integer/nat bridge:

```isabelle
lemma finite_connected_graph_cotree_card:
  assumes "finite I"
      and "finite V"
      and "top1_is_spanning_tree_indices X TX I A T"
      and "top1_connected_on X TX"
  shows "card (I - T) = card I - card V + 1"
```

and:

```isabelle
lemma finite_connected_graph_pi1_rank:
  assumes ...
  obtains gen where
    "top1_is_free_group_full_on ... gen (I - T)"
    "card (I - T) = card I - card V + 1"
```

This avoids a separate abstract “rank invariant of free groups” in the Schreier proof.

---

## 6. Phase A.5: graph covering counts need a precise finite-sheeted API

The plan’s covering-count lemmas are correct as book mathematics, but the Isabelle target is too compressed.

Do not try to prove:

```isabelle
k-sheeted covering of graph with v vertices, e edges
-> covering has k*v vertices, k*e edges
```

as one giant theorem. Split it:

```isabelle
definition top1_k_sheeted_covering_on where
  "top1_k_sheeted_covering_on E TE X TX p k ⟷
     top1_covering_map_on E TE X TX p ∧
     (∀x∈X. finite (p -` {x} ∩ E) ∧ card (p -` {x} ∩ E) = k)"
```

Then:

```isabelle
lemma covering_vertex_fibers_card:
  assumes "top1_k_sheeted_covering_on E TE X TX p k"
      and "v ∈ graph_vertex_set I A"
  shows "card (p -` {v} ∩ E) = k"
```

For edges, be careful: the preimage of a closed base arc should split into `k` lifted arcs only after you use the covering trivialization over the arc and connectedness/path lifting. The clean target is:

```isabelle
lemma covering_arc_lifts_card:
  assumes "top1_k_sheeted_covering_on E TE X TX p k"
      and "i ∈ I"
      and "top1_graph_arcs X TX I A"
  shows "card {lifted_arc. lifted_arc_lies_over p (A i) lifted_arc} = k"
```

Then sum over finite `I`.

Also, the plan says `graph_covering_is_graph` is done in `ac3`, but I would ask the worker to verify the exact theorem name and source location. The live final file calls `graph_covering_is_graph` in §85, but the visible `ac3/AlgTopCached3.thy` excerpt is primarily the §83 graph definition plus early §84 infrastructure. ([GitHub][1])

---

## 7. Phase B: canonical covering carrier is the correct fix, but status is stale

The plan’s B.2 is one of the best parts:

```isabelle
lemma covering_for_subgroup:
  assumes graph X, connected X, lpc X, ssc X, subgroup H of pi1(X)
  obtains E TE p e0 where
    "covering_map E TE X TX p"
    "connected E TE"
    "p_*(pi1(E,e0)) = H"
```

But it should not be graph-specific. First prove the general theorem:

```isabelle
lemma covering_for_pi1_subgroup_canonical:
  fixes X :: "'a set"
    and TX :: "'a set set"
    and x0 :: 'a
    and H :: "(real ⇒ 'a) set set set"  (* whatever the actual pi1 carrier element type is *)
  assumes "is_topology_on_strict X TX"
      and "top1_path_connected_on X TX"
      and "top1_locally_path_connected_on X TX"
      and "top1_semilocally_simply_connected_on X TX"
      and "x0 ∈ X"
      and "top1_subgroup_on
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)
             H"
  obtains E TE p e0 where
      "E = top1_covering_path_class_carrier X TX x0 H"
      "top1_covering_map_on E TE X TX p"
      "e0 ∈ E"
      "p e0 = x0"
      "top1_fundamental_group_induced_on E TE e0 X TX x0 p `
         top1_fundamental_group_carrier E TE e0 = H"
```

Then add a graph wrapper:

```isabelle
lemma covering_for_graph_subgroup:
  assumes "top1_is_graph_on X TX"
      and "top1_connected_on X TX"
      and "x0 ∈ X"
      and "top1_subgroup_on (pi1 X TX x0) ... H"
  obtains E TE p e0 where ...
```

The current source still has §85 covering-existence `sorry`s, including an `obtain E' :: 'b set ... sorry`, which is exactly the type-escape pattern the plan says to eliminate. ([GitHub][1])

So B.1 should not be marked “DONE” unless the worker has a newer local commit not visible in the live source. In the visible source, §85 still needs this abstraction.

---

## 8. Phase C.1: Nielsen-Schreier needs arbitrary wedge realization, not just Theorem 71.3

The book proof route is correct:

```text
free group G on S
→ realize G as π₁ of wedge of circles indexed by S
→ subgroup H corresponds to covering
→ covering of graph is graph
→ graph π₁ is free
→ transfer freeness to H
```

But the plan underestimates the first step.

For finite `S`, the existing planar wedge construction is probably enough. For arbitrary `S`, do **not** try to embed one geometric circle per generator in `real × real`. That only works for some cardinalities and is not the right abstraction. Use the abstract wedge machinery from Theorem 71.3. The cached `ac9` file advertises a sorry-free Munkres 71.3-style theorem for wedge fundamental groups, which is exactly the right dependency. ([GitHub][6])

The missing lemma should look like:

```isabelle
lemma free_group_realized_by_abstract_wedge:
  assumes "top1_is_free_group_full_on G mul e invg gen S"
  obtains X TX x0 I A iso
  where
    "top1_graph_arcs X TX I A"
    "top1_connected_on X TX"
    "x0 ∈ X"
    "bij_betw some_index S I"
    "top1_group_iso_on
       G mul
       (top1_fundamental_group_carrier X TX x0)
       (top1_fundamental_group_mul X TX x0)
       iso"
```

Then the finite planar wedge theorem becomes only a corollary/special case.

The current final file still has a `sorry` exactly at the “wedge of |S| circles realizes G” step for Nielsen-Schreier. ([GitHub][1])

Also, the final `show ?thesis sorry` in Nielsen-Schreier is still the type-variable escape problem:

```text
Type variable 'b from covering space can't escape to polymorphic γ.
```

That means the plan’s “Nielsen-Schreier packaging fixed” status is not current for the visible source. ([GitHub][1])

The fix is simple conceptually: do not try to return a basis indexed by the covering-space type if the theorem conclusion asks for an arbitrary hidden type. Let the existential choose the covering-space-derived basis type directly:

```isabelle
shows "∃genH SH. top1_is_free_group_full_on H mul e invg genH SH"
```

where `SH` can be `S_E`, and `genH` is transported along the proved iso.

If Isabelle still complains because `S_E :: 'b set set`, then the problem is the surrounding theorem’s fixed type variables. The covering carrier must be canonical in the theorem, not arbitrary `'b`.

---

## 9. Phase C.2: Schreier index should avoid abstract rank invariance if possible

The plan lists:

```text
Rank = card of free basis: rank invariant for finitely generated free groups.
```

That is a serious algebra theorem. It usually goes through abelianization and dimension/rank of free abelian groups. If this is not already available, it can become a major detour.

A better route is to avoid rank invariance entirely:

1. Construct the covering graph.

2. Prove it has exactly `k` lifted vertices and `k * (n + 1)` lifted edges.

3. Choose a spanning tree in the finite connected covering graph.

4. The graph π₁ theorem returns an explicit free basis indexed by cotree edges.

5. Prove:

   ```isabelle
   card cotree_edges = k * (n + 1) - k + 1 = k * n + 1
   ```

6. Transfer that specific basis across the group isomorphism to `H`.

Then the conclusion is obtained with the actual transferred basis set, not by invoking a global invariant of free groups.

Also note that the live final file appears to contain more than one Schreier-related block: an older block around the current line 791 has a `k * (n - 1) + 1`-style formula, while the later theorem states the book-faithful `card S = n + 1` and conclusion `k * n + 1`. ([GitHub][1]) The worker should remove or quarantine duplicate/older theorem statements before proving downstream lemmas, otherwise time will be wasted proving the wrong formulation.

---

## 10. Phase D: surface classification is right conceptually, but needs validity predicates

The plan is right that §74-78 should start with a scheme language, not with more `sorry` skeletons. The current final source still has undefined-looking surface scheme predicates inside the classification skeleton, such as `top1_is_torus_scheme`, `top1_is_projective_scheme`, and `top1_elementary_scheme_equiv`. ([GitHub][1])

But the datatype alone is not enough:

```isabelle
datatype 'e signed_edge = Pos 'e | Neg 'e
```

Add a validity predicate:

```isabelle
definition valid_edge_scheme where
  "valid_edge_scheme w ⟷
     finite (set (map edge_of w)) ∧
     (∀e∈set (map edge_of w). count_list (map edge_of w) e = 2) ∧
     even (length w)"
```

Probably also distinguish:

```isabelle
orientable_scheme w
nonorientable_scheme w
scheme_vertices w
one_vertex_scheme w
```

The normal-form theorem should be stated for valid schemes:

```isabelle
theorem scheme_normal_form:
  assumes "valid_edge_scheme w"
  shows
    "scheme_equiv w [] ∨
     (∃n w'. n > 0 ∧ torus_scheme w' n ∧ scheme_equiv w w') ∨
     (∃m w'. m > 0 ∧ projective_scheme w' m ∧ scheme_equiv w w')"
```

The quotient-preservation layer should be separate:

```isabelle
lemma elementary_scheme_move_preserves_quotient_homeomorphism:
  assumes "top1_elementary_scheme_move w w'"
      and "top1_quotient_of_scheme_on X TX w"
      and "top1_quotient_of_scheme_on Y TY w'"
  shows "∃h. top1_homeomorphism_on X TX Y TY h"
```

Do not mix normal-form list rewriting with quotient-map topology in the same proof. That will become unmaintainable.

---

## 11. Phase E: deck transformations are important, but should not block §85

The plan puts deck transformations after surfaces. I would move §81 either:

* after the covering-subgroup canonical carrier lemma, or
* after §85 if §85 is the immediate target.

It is not needed for Nielsen-Schreier or Schreier index. The §85 proof needs covering existence, graph-covering, graph π₁, and counting. It does **not** need the full normalizer quotient theorem for deck transformations.

So the worker should not let Theorem 81.2 delay §85 unless the project goal is literally “zero sorry everywhere in order.”

The current §81 theorem still has a `sorry` in the normalizer quotient/deck transformation assembly. ([GitHub][1]) It should eventually be proved, but it is not on the critical path for Munkres §85.

---

## 12. Revised execution order I would give the worker

I would revise the plan’s order as follows:

```text
Phase 0: Verification hygiene
  - comment-stripped sorry/oops count
  - exact SHA and ROOT session
  - CI command without quick_and_dirty
  - blocker table regenerated after every commit

Phase 1: Immediate local proof closures
  - I_set_locally_path_connected
  - arc_locally_path_connected
  - graph_ssc interior case
  - graph_ssc vertex-star infrastructure

Phase 2: Graph interface repair
  - top1_is_graph_with_arcset_on
  - top1_graph_arcs locale/predicate with index set I and arc map A
  - conversion lemmas to/from old top1_is_graph_on

Phase 3: Graph π₁ theorem repair
  - finite indexed theorem using existing finite SvK proof
  - free_group_full_reindex_bij if not already adequate
  - arbitrary indexed theorem via finite-support/direct-limit argument
  - remove nat-indexed general theorem

Phase 4: Covering-subgroup canonical carrier
  - general covering_for_pi1_subgroup_canonical
  - graph-specific wrapper
  - eliminate all arbitrary 'b covering-existence obtains in §85

Phase 5: Nielsen-Schreier
  - arbitrary abstract wedge realization using cached Theorem 71.3
  - covering application
  - graph covering is graph
  - graph π₁ free
  - transfer freeness to H

Phase 6: Schreier index
  - finite rose structure
  - finite-sheeted covering/coset count
  - vertex and edge lift counts
  - finite connected graph cotree-card/rank theorem
  - transfer explicit basis to H

Phase 7: Deck transformations
  - path-lift product law
  - fiber action
  - normalizer quotient
  - theorem assembly

Phase 8: Surface classification
  - scheme datatype and valid_scheme
  - elementary moves
  - combinatorial normal forms
  - quotient preservation
  - final classification assembly

Phase 9: Release cleanup
  - remove ac/oops
  - remove duplicate stale theorem blocks
  - delete or demote stale reports
  - build final session without quick_and_dirty
```

This differs from the plan mostly by moving **surface classification later** and prioritizing **§85 unblockers** first.

---

## 13. The two most important concrete warnings

First: do not implement A.1 as written. Use either a set-of-arcs predicate or an indexed family, not both at once. For graph π₁ and Euler counts, use the indexed locale.

Second: do not try to prove the general graph π₁ theorem by reindexing into `nat`. That only proves the countable/finite corollary. The book-faithful theorem is free on the actual cotree arc index set. The plan acknowledges this at a high level, but the finite reindexing subsection could easily tempt someone back into the old bug.

My recommended message to the worker would be:

> The plan is approved as a strategy, but please revise the Isabelle-level interfaces before coding. Start by adding the indexed graph locale, the canonical covering-subgroup theorem, and the finite/general split for graph π₁. Treat the current status claims as stale until a fresh comment-stripped blocker table confirms them. Do not spend time on surfaces or deck transformations until §85 no longer has type-packaging and graph-index blockers.

[1]: https://raw.githubusercontent.com/JUrban/isa_algtop1/main/tst/AlgTop.thy "raw.githubusercontent.com"
[2]: https://raw.githubusercontent.com/JUrban/isa_algtop1/main/tst/ROOT "raw.githubusercontent.com"
[3]: https://github.com/JUrban/isa_algtop1/tree/main/tst "isa_algtop1/tst at main · JUrban/isa_algtop1 · GitHub"
[4]: https://raw.githubusercontent.com/JUrban/isa_algtop1/main/tst/ac3/AlgTopCached3.thy "raw.githubusercontent.com"
[5]: https://raw.githubusercontent.com/JUrban/isa_algtop1/main/tst/ac7/AlgTopCached7.thy "raw.githubusercontent.com"
[6]: https://raw.githubusercontent.com/JUrban/isa_algtop1/main/tst/ac9/AlgTopCached9.thy "raw.githubusercontent.com"
