# Plan: Zero-sorry formalization of Munkres §51-85

Based on the expert audit (isa_algtop1_algtop_blocker_audit_2026-06-03.md)
and the current state (24 executable sorrys in AlgTop.thy, 2 oops in ac/).

## Guiding principles

1. **Fix statements first, then prove.** Most blockers are statement-level type
   mismatches, not missing proof ideas. Fix the interfaces before grinding on proofs.

2. **Expose all index types and carriers.** Never hide a constructed type behind a
   polymorphic existential. Use canonical types (path-class sets for covering spaces,
   non-tree arcs for graph generators).

3. **Introduce an explicit graph-with-arcs predicate.** The current `top1_is_graph_on`
   hides the arc family behind an existential. Many proofs need the arcs. Define
   `top1_is_graph_with_arcs_on X TX A` (or a locale) that makes the arc family visible.

4. **Work bottom-up along the dependency chain.** Prove infrastructure lemmas in cache
   files before using them in AlgTop.thy.

5. **Every theorem's final form must compile without `quick_and_dirty`.**

---

## Phase A: Graph infrastructure (cached)

These go into a new cache file `ac10/AlgTopCached10.thy` (or extend ac7).

### A.1 Explicit graph-with-arcs predicate

```
definition top1_is_graph_with_arcs_on X TX A where
  "top1_is_graph_with_arcs_on X TX A <->
     is_topology_on_strict X TX & is_hausdorff_on X TX &
     (ALL i : A. A i <= X & top1_is_arc_on (A i) (subspace_topology X TX (A i))) &
     Union (A ` UNIV) = X &    (* or Union (range A) *)
     pairwise intersection <= endpoints &
     coherent topology"
```

Add corollary: `top1_is_graph_on X TX <-> (EX A. top1_is_graph_with_arcs_on X TX A)`.

### A.2 Graph pi1 theorem with explicit non-tree arc index

Restate `graph_pi1_free_weak_finite` to return generators indexed by
non-tree arcs, not by nat. The current version in ac7 produces nat-indexed
generators via SvK induction. The fix:

1. Keep the induction proof as-is (nat-indexed).
2. Add a `free_group_full_reindex_bij` lemma (audit's recommendation).
3. The finite case constructs a bijection `non_tree_arcs <-> {0..<card}`.
4. Compose to get non-tree-arc-indexed generators.

Output:
```
lemma graph_pi1_free_indexed_finite:
  assumes "top1_is_graph_with_arcs_on X TX A"
      and T maximal tree, finite non-tree arcs...
  shows "top1_is_free_group_full_on (pi1 X TX x0) ... gen (non_tree_arcs A T)"
```

### A.3 Graph ssc: two standalone lemmas

Following the audit exactly:

**Interior chart lemma:**
```
lemma graph_ssc_interior_chart:
  -- homeomorphism h : I_set -> A(i), t0 with h(t0) = x, 0 < t0 < 1
  -- U = h ` {t in I_set. |t - t0| < eps}
  -- U open in X by coherent, SC by convexity
```

**Vertex star contraction lemma:**
```
lemma graph_vertex_star_open:
  -- star = Union {A(i) - far_ep(A(i)) : x in A(i)}  
  -- star open in X by coherent (already proved)

lemma graph_vertex_star_ssc:
  -- for each loop f in star:
  -- f(I_set) compact, meets finitely many arcs (selection set argument, proved)
  -- those arcs form finite star, DR to {x}, SC
  -- loop null-homotopic in star, transfer to X (proved)
```

The interior case already works. The vertex case needs `arc_sub_arc_covering_compact`
which requires showing that a compact set in [0,1) not reaching 1 has sup < 1.
This uses `closed_contains_Sup` from HOL-Analysis.

### A.4 Euler characteristic for graphs

New definitions and lemmas:

```
definition top1_graph_vertices X TX A = Union {endpoints(A i) : i in I}
definition top1_graph_edge_count X TX A = card {i. A i not in T}  
definition top1_graph_euler_char X TX A = card(vertices) - card(edges)

lemma connected_graph_rank:
  "connected graph, finite -> rank(pi1) = 1 - euler_char = edges - vertices + 1"
```

### A.5 Graph covering counting

```
lemma graph_covering_vertex_edge_count:
  "k-sheeted covering of graph with v vertices, e edges
   -> covering has k*v vertices, k*e edges"

lemma rose_graph_structure:
  "wedge of n+1 circles has 1 vertex and n+1 edges"
```

---

## Phase B: Covering space architecture (cached + AlgTop)

### B.1 Theorem 82.1 with canonical carrier (DONE in AlgTop.thy)

Already fixed: conclusion uses `E :: (real => 'a) set set` (path-class sets).
The proof was already complete; only the packaging sorry needed fixing.

### B.2 Covering space application lemma

```
lemma covering_for_subgroup:
  assumes graph X, connected X, lpc X, ssc X, subgroup H of pi1(X)
  obtains E TE p e0 where
    "covering_map E TE X TX p" "connected E TE"
    "p_*(pi1(E,e0)) = H" -- up to the iso
```

This composes: transfer H to subgroup of pi1(X) via iso, apply Thm 82.1,
get covering with canonical carrier type.

### B.3 Theorem 81.2: deck transformation group

The proof sketch exists. Needs:
- Lemma 81.1: fiber action
- Path-lift product law
- Normalizer quotient construction
- Iso assembly from psi-injectivity + image characterization

This is independent of the type fixes above.

---

## Phase C: Section 85 (Nielsen-Schreier, Schreier index)

### C.1 Nielsen-Schreier (Theorem 85.1)

Book proof: G free on S -> G = pi1(X) for wedge X of |S| circles ->
H <= G corresponds to covering E -> E is graph -> pi1(E) free -> H free.

Steps:
1. **Wedge realization:** For finite S: `free_group_realized_by_wedge` (done).
   For infinite S: need infinite wedge. The audit says use Theorem 71.3 (cached in ac9).
   Theorem 71.3 gives pi1(wedge) free on the circles. With the graph-with-arcs predicate,
   the wedge is a graph.

2. **Covering from subgroup:** Apply B.2 above. With canonical carrier, no type escape.

3. **Covering is graph:** `graph_covering_is_graph` (done in ac3).

4. **Graph pi1 is free:** Theorem 84.7 = `graph_pi1_free_weak` with proper types.

5. **Transfer freeness:** `free_group_iso_transfer` (done). With canonical types, the
   existential packaging works.

### C.2 Schreier index formula (Theorem 85.3)

Book proof: Same as 85.1 but with a finite-index subgroup of a finitely-generated free group.

Additional needs:
1. **Rose structure:** wedge of n+1 circles has 1 vertex, n+1 edges (A.5).
2. **Finite-sheet covering:** index k -> k-sheeted covering (from Theorem 54.4).
3. **Covering vertex/edge count:** k*1 vertices, k*(n+1) edges (A.5).
4. **Graph rank:** k*(n+1) - k + 1 = k*n + 1 (A.4).
5. **Rank = card of free basis:** rank invariant for finitely generated free groups.

---

## Phase D: Section 74-78 (Surface classification)

This is the largest remaining block (8 sorrys). Following the audit:

### D.1 Scheme language (new definitions)

```
datatype 'e signed_edge = Pos 'e | Neg 'e

inductive top1_elementary_scheme_move :: ... where
  rotate | inverse | relabel | cancel | cut_paste

definition top1_elementary_scheme_equiv =
  top1_elementary_scheme_move^^**
```

### D.2 Combinatorial normal form (pure list combinatorics)

Prove: every scheme is equivalent to one of:
- Empty scheme (sphere)
- a1 b1 a1^-1 b1^-1 ... an bn an^-1 bn^-1 (orientable genus n)
- a1 a1 ... am am (non-orientable genus m)

This is a purely combinatorial theorem about formal words, independent of topology.

### D.3 Quotient preservation under elementary moves

For each elementary move, prove that the resulting quotient space is homeomorphic.
This requires:
- Quotient map theory (from general topology)
- Polygon/simplex homeomorphism theory
- Pasting lemma for continuous maps

### D.4 Assembly

- Theorem 78.1: triangulable surface -> simplex quotient
- Theorem 78.2: connected -> single polygon quotient  
- Theorem 76: elementary operations preserve quotient
- Theorem 77.5: classification = normal form + quotient preservation
- Theorem 75.4: homology computation from normal form

---

## Phase E: Section 81 (Deck transformations)

### E.1 Lemma 81.1: fiber action characterization

### E.2 Path-lift product law

### E.3 Normalizer quotient construction

### E.4 Theorem 81.2 assembly

---

## Execution order (by dependency)

```
Week 1-2: Phase A (graph infrastructure)
  A.1  graph-with-arcs predicate (small, enables everything)
  A.3  graph ssc standalone lemmas (close arc_sub_arc_covering_compact)
  A.2  graph pi1 with explicit index (modify ac7 or add ac10)
  
Week 2-3: Phase B (covering architecture)
  B.1  already done
  B.2  covering application lemma
  A.4  Euler characteristic
  A.5  graph covering counting

Week 3-4: Phase C (section 85)
  C.1  Nielsen-Schreier (connects B.2 + A.2 + 71.3)
  C.2  Schreier index (connects C.1 + A.4 + A.5)

Week 4-6: Phase D (surface classification)
  D.1  scheme language
  D.2  combinatorial normal form
  D.3  quotient preservation
  D.4  assembly

Week 6-7: Phase E (deck transformations)
  E.1-E.4

Week 7-8: Final cleanup
  - Remove all oops from ac/
  - Build without quick_and_dirty
  - Regenerate indexes
  - Final audit
```

---

## What NOT to do

- Do NOT keep using polymorphic existentials for covering spaces.
- Do NOT try to reindex nat -> 'a set set with type hacks.
- Do NOT add more sorry-first skeletons for surface classification
  without introducing the scheme datatype first.
- Do NOT work on downstream theorems before their infrastructure is solid.
- Do NOT optimize for sorry count; optimize for correct statement interfaces.

---

## Current status (as of 2026-06-03)

- **Proved (no sorry):** §51-70 (general topology, cached), §82 proof body,
  graph_lpc, I_set_lpc, graph_ssc interior case, wedge construction,
  most of graph_pi1 (finite case fully proved in ac7, infinite case skeleton)
  
- **Sorry but close:** graph_ssc vertex (1 sorry: arc_sub_arc_covering_compact),
  Theorem 82.1 packaging (FIXED), Nielsen-Schreier packaging (FIXED)

- **Sorry and blocked by interfaces:** graph_pi1 reindex (needs A.2),
  §85 Euler (needs A.4+A.5), §85 covering application (needs B.2)

- **Sorry and deep math:** §74-78 surface classification (8 sorrys, needs D.1-D.4),
  §81 deck transformations (1 sorry, needs E.1-E.4)
