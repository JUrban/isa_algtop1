---
title: "Repeat audit of JUrban/isa_algtop1 tst/AlgTop"
subtitle: "Blocker-focused audit of the algebraic topology formalization, with last-five-day commit review"
author: "OpenAI GPT-5.5 Pro"
date: "2026-06-03"
geometry: margin=0.9in
fontsize: 11pt
toc: true
numbersections: true
colorlinks: true
mainfont: DejaVu Serif
monofont: DejaVu Sans Mono
---

# Executive summary

This report is a fresh repeat audit of the live `tst` tree of `JUrban/isa_algtop1`, focused on the algebraic-topology formalization rather than the general-topology development.  The audit was performed against the current raw Isabelle source and the visible recent commit history, not against the generated repository reports.  I treated `tst/AlgTop.thy`, the `ROOT` session file, and the imported cache chain `ac` through `ac9` as the authoritative material.  The current active final session imports `AlgTopCached9` and then checks `AlgTop.thy` under `quick_and_dirty`; therefore the final target is still a draft target rather than a certified release target.

The most important reconciliation with the pasted blocker report is this: the live source currently contains **24 executable `sorry` commands** in `AlgTop.thy` after stripping Isabelle block comments and `\<comment>` cartouches, not 22.  The discrepancy is not just cosmetic.  The latest commit extracted `arc_locally_path_connected` and introduced a new executable `sorry` for local path connectedness of `I_set`; also the graph semilocal simple connectivity interior case is still present as an executable `sorry`.  The pasted report says the interior case was closed; the current source disagrees.

The highest-priority mathematical blocker remains Theorem 82.1, the covering-space existence theorem.  The proof constructs a concrete coset/path-class carrier, but the theorem statement asks Isabelle/HOL to package that construction into an arbitrary, unconstrained result type.  HOL does not existentially quantify over types.  This is not a proof-search issue and not an arithmetic issue.  It is a theorem-statement issue.  The correct Isabelle repair is to state the theorem using a canonical carrier type, such as sets of basepoint paths modulo the subgroup relation, or to introduce a fixed locale/typedef wrapper with the carrier visible in the theorem.  Once Theorem 82.1 is repaired this way, most of the Nielsen-Schreier and Schreier-index packaging holes become ordinary constructions instead of impossible type escapes.

The second highest-priority semantic blocker is the graph fundamental group theorem.  The old false countability step has mostly been removed from executable code, but the remaining theorem still hides the arc family behind `top1_is_graph_on` and then tries to reindex a finite helper.  The book-faithful statement should preserve the actual non-tree arc index set.  A `nat`-indexed finite helper is useful only as a corollary, not as the main theorem.  The right Isabelle theorem should use an explicit graph-with-arcs predicate or locale and state that the basis is indexed by cotree arcs.

The third priority is graph semilocal simple connectivity.  Recent commits are strong and have turned `graph_locally_path_connected` into a zero-sorry lemma.  The remaining graph-SSC holes are tractable if the proof is reorganized around two explicit lemmas: an interior-chart lemma using an actual interval in the arc parameter, and a vertex-star contraction lemma using all incident subarcs.  The current comments are close, but the interior proof should not try to use an arbitrary locally path connected neighborhood `V0` because it may contain endpoints or other arc-intersection points.  Use the interval coordinate directly.

The fourth priority is Munkres Section 85.  The user specifically mentioned the Euler characteristic line as possibly elementary arithmetic.  In the current source the corresponding line is 16285, but it is not ready to be solved by arithmetic alone.  It becomes a small `simp` or `linarith` step only after three prerequisite lemmas exist: finite-sheeted covering graphs multiply vertex and edge counts by the sheet number, finite connected graph rank is `edges - vertices + 1`, and the rose representing a free group on `n+1` generators has one vertex and `n+1` edges.  Without those facts in the context, the line is not an arithmetic hole; it is a missing graph-covering/Euler infrastructure hole.

The surface-classification section remains a high-risk skeleton.  Several predicate names used in the classification theorem are not defined before use in the active source; they occur only inside a `sorry` block.  The classification theorem should be decomposed into a genuine scheme datatype, primitive elementary scheme moves, a reflexive-transitive closure relation, normal-form combinatorics, and quotient-preservation lemmas.  The current monolithic theorem shape is not audit-ready.

Finally, the cache tree now has `ac2`, `ac3`, and `ac9` present in the visible `tst` tree, so the earlier transient reproducibility problem around missing `ac2`/`ac3` is fixed.  However, the old huge cache `ac/AlgTopCached.thy` still contains two executable `oops` terminations.  Isabelle accepts `oops` as an abandoned theorem attempt, but for a project audit this should be treated as a failed certification signal unless those blocks are moved to a scratch theory or deleted.


# Source scope and method

The source basis of this audit is:

- `tst/ROOT`, current raw file, observed with final session `AlgTop = AlgTopCached9 + options [quick_and_dirty, timeout = 600]`.
- `tst/AlgTop.thy`, current raw active final theory, 16,764 physical lines in the downloaded copy used for static analysis.
- `tst/ac/AlgTopCached.thy` and `tst/ac2` through `tst/ac9`, because the final session imports the cache chain and because stale/duplicate/backup material can still affect the session graph.
- The visible GitHub commit history for `tst`, especially commits on 2026-06-03 and the immediately preceding page of history that includes Jun 2 work.

No trust was placed in generated theorem reports except as evidence of documentation drift.  The reports can be useful navigational aids, but they are not authoritative.  In particular, any stale `sorry` count in a regenerated statement index is less reliable than a direct scan of the raw Isabelle source with comment stripping.

This was a static source audit.  I did not run `isabelle build`, because the execution environment used for this report does not contain an Isabelle installation.  Therefore I do not claim kernel certification of any proposed snippet.  The recommendations are theorem-statement and proof-architecture fixes designed to be carried into an Isabelle development environment and checked there.  The final acceptance criterion for every proposed fix is an Isabelle build with `quick_and_dirty` disabled and no executable `sorry`/`oops` in the certified target.

The comment-stripping scan preserved physical line numbers and ignored both nested Isabelle block comments `(* ... *)` and cartouche comments of the form `\<comment> \<open>...\<close>`.  Under that definition, an executable `sorry` is a `sorry` token remaining in the command stream, not a word in a prose comment.

## Active ROOT excerpt

```isabelle
session AlgTopCached9 in ac9 = AlgTopCached8 +
  options [timeout = 600]
  theories
    AlgTopCached9

session AlgTop = AlgTopCached9 +
  options [quick_and_dirty, timeout = 600]
  theories
    AlgTop
```

The final `quick_and_dirty` option must be interpreted strictly.  A theory checked with `quick_and_dirty` is not a release theorem base, even if all non-final cache sessions happen to build.  It is acceptable for a draft session, but a $200k formalization deliverable needs a second certified session that imports the same code without `quick_and_dirty`.

# Current source metrics

- **File:** tst/AlgTop.thy; **Physical lines:** 16764; **All sorry words:** 30; **Executable sorrys:** 24; **Executable oops:** 0; **Audit note:** active final theory; imports ac9 chain; quick_and_dirty session
- **File:** tst/ac/AlgTopCached.thy; **Physical lines:** 58993; **All sorry words:** 0; **Executable sorrys:** 0; **Executable oops:** 2; **Audit note:** very large cache; two exploratory oops blocks remain
- **File:** tst/ac2/AlgTopCached2.thy; **Physical lines:** 1361; **All sorry words:** 0; **Executable sorrys:** 0; **Executable oops:** 0; **Audit note:** cache chain, graph predicate source
- **File:** tst/ac3/AlgTopCached3.thy; **Physical lines:** 1169; **All sorry words:** 0; **Executable sorrys:** 0; **Executable oops:** 0; **Audit note:** cache chain
- **File:** tst/ac4/AlgTopCached4.thy; **Physical lines:** 5244; **All sorry words:** 0; **Executable sorrys:** 0; **Executable oops:** 0; **Audit note:** cache chain
- **File:** tst/ac5/AlgTopCached5.thy; **Physical lines:** 2826; **All sorry words:** 1; **Executable sorrys:** 0; **Executable oops:** 0; **Audit note:** comment-only sorry word
- **File:** tst/ac6/AlgTopCached6.thy; **Physical lines:** 5219; **All sorry words:** 5; **Executable sorrys:** 0; **Executable oops:** 0; **Audit note:** comment-only sorry words
- **File:** tst/ac7/AlgTopCached7.thy; **Physical lines:** 8805; **All sorry words:** 5; **Executable sorrys:** 0; **Executable oops:** 0; **Audit note:** comment-only sorry words; finite graph pi1 helper
- **File:** tst/ac8/AlgTopCached8.thy; **Physical lines:** 8490; **All sorry words:** 3; **Executable sorrys:** 0; **Executable oops:** 0; **Audit note:** comment-only sorry words
- **File:** tst/ac9/AlgTopCached9.thy; **Physical lines:** 2855; **All sorry words:** 2; **Executable sorrys:** 0; **Executable oops:** 0; **Audit note:** comment-only sorry words; Theorem 71.3 cache

The headline count is **24 executable `sorry`s in `tst/AlgTop.thy`** and **2 executable `oops` blocks in `tst/ac/AlgTopCached.thy`**.  The cache files `ac2` through `ac9` contain no executable `sorry` or `oops` after comment stripping; their remaining `sorry` words are prose in comments.

# Reconciliation with the pasted blocker report

- **Pasted blocker location/category:** L6327; **Current location:** 6327; **Status:** same; **Audit interpretation:** Theorem 82.1 packaging. Real blocker in current form; fix by canonical carrier statement.
- **Pasted blocker location/category:** L16280; **Current location:** 16064 / 16278; **Status:** line drift plus split; **Audit interpretation:** Current source has one Nielsen type escape at 16064 and a Schreier transfer packaging hole at 16278.
- **Pasted blocker location/category:** L16494; **Current location:** 16283; **Status:** line drift; **Audit interpretation:** Current source has existential extraction after hH_free at 16283.
- **Pasted blocker location/category:** L16499; **Current location:** not exactly current; **Status:** line drift / merged category; **Audit interpretation:** The remaining nearby holes are 16285 Euler and 16291 finite/existential finish; only 16283 is a type extraction hole.
- **Pasted blocker location/category:** Surface L231, L304, L346, L408, L444, L484, L500, L502; **Current location:** same current lines; **Status:** same; **Audit interpretation:** The eight surface skeleton holes remain executable.
- **Pasted blocker location/category:** Deck L1060; **Current location:** 1060; **Status:** same; **Audit interpretation:** Deck transformation theorem remains an executable sorry.
- **Pasted blocker location/category:** graph_ssc vertex L8721; **Current location:** 8505; **Status:** line drift; **Audit interpretation:** Vertex star case remains; source moved upward after simplification.
- **Pasted blocker location/category:** §85/Euler L8837, L8848; **Current location:** 8621, 8632; **Status:** line drift; **Audit interpretation:** Early schreier_rank_formula helper still has covering and Euler/rank holes.
- **Pasted blocker location/category:** §85/Euler L16044, L16060, L16341, L16501, L16507; **Current location:** 15828, 15844, 16125, 16285, 16291; **Status:** line drift; **Audit interpretation:** The same conceptual blockers remain, with current line numbers listed in the executable-sorry table.
- **Pasted blocker location/category:** graph_pi1 reindex L9826; **Current location:** 9610; **Status:** line drift; **Audit interpretation:** Finite reindex hole remains and should be solved by strengthening the finite graph theorem.

The pasted blocker report is directionally useful, but it is not current enough to drive work without rechecking the raw source.  It misses the current `arc_locally_path_connected` proof hole and it describes the graph-SSC interior case as closed, whereas the live source still has an executable `sorry` at line 8496.  It also over-labels several type-packaging issues as permanently blocked.  They are permanently blocked only if the current theorem statements are preserved unchanged.  If the canonical carrier is exposed, the same mathematical proof becomes expressible.

# Last-five-day commit audit

- **Date:** 2026-06-03; **Commit:** 5d98ab1; **Visible title / theme:** Extract arc_locally_path_connected as standalone lemma; **Audit reading:** Positive extraction, but it adds one executable sorry for I_set local path connectedness. This should be closed by moving the already-proved hI_lpc proof out of graph_locally_path_connected.
- **Date:** 2026-06-03; **Commit:** a184d42; **Visible title / theme:** graph_ssc interior simplified to one sorry; **Audit reading:** Good direction: large brittle proof shrunk. The remaining interior case still needs an explicit chart interval and coherent-open proof.
- **Date:** 2026-06-03; **Commit:** a5188a5; **Visible title / theme:** graph_locally_path_connected ZERO SORRY; **Audit reading:** Strong progress; it proves the interval local-path-connected proof that should now be factored as a reusable lemma.
- **Date:** 2026-06-03; **Commit:** 1e38152; **Visible title / theme:** hI_lpc ZERO SORRY; **Audit reading:** Important because it likely contains exactly the proof needed for arc_locally_path_connected.
- **Date:** 2026-06-03; **Commit:** 656b51d / 9821531; **Visible title / theme:** wedge-is-graph and coherent topology fully proved in the free-group realization area; **Audit reading:** Very positive, but the finite realization remains too narrow for arbitrary-basis Nielsen-Schreier unless connected to arbitrary wedge Theorem 71.3.
- **Date:** 2026-06-03; **Commit:** 3ca0ae0 / 066eff1 / 4ba48b1; **Visible title / theme:** n=0 free_group_realized_by_wedge work; **Audit reading:** Correctly handles the trivial free group. The audit still recommends replacing arbitrary-carrier conclusions with a canonical finite wedge carrier.
- **Date:** 2026-06-02 and recent chain; **Commit:** multiple; **Visible title / theme:** covering-space construction and wedge assembly work; **Audit reading:** Substantial progress, but the central Theorem 82.1 statement still cannot package the constructed concrete carrier into an arbitrary HOL type.

The recent work is concentrated in exactly the right areas: graph local path connectedness, graph semilocal simple connectivity, wedge-of-circles graph structure, the zero-generator wedge/free-group case, and covering-space infrastructure.  The work is not merely churn.  Several commits close real proof obligations, especially the `graph_locally_path_connected` and `[0,1]` local-path-connected chain.  The risk is that the project is now solving local lemmas faster than it is correcting global theorem interfaces.  Unless the interfaces are corrected, closed local proofs will continue to feed into `sorry` barriers caused by type packaging and hidden index sets.

The most recent commit explicitly says that `arc_locally_path_connected` was extracted from the `graph_lpc` proof body and that one `sorry` remains for `I_set` local path connectedness.  This is good extraction but it should be finished immediately, because the previous `graph_lpc` chain already contains the needed proof.  Another recent commit says `graph_ssc interior` was simplified to one `sorry`, not eliminated.  That matches the current source.

The wedge/free-group realization work is also positive.  The zero-generator case `F={e}` is important, because many formalizations accidentally mishandle the free group on an empty basis.  However, the finite wedge realization is not enough for Nielsen-Schreier over an arbitrary free group.  Munkres uses arbitrary free groups, and the formalization already has a stronger Theorem 71.3 cache stating freeness on the actual wedge index set.  Section 85 should connect to that arbitrary-index theorem instead of building everything through finite/nat wrappers.


# Full executable-sorry audit

The following table is the current active blocker list for `tst/AlgTop.thy`.  The source line numbers are physical line numbers in the raw file downloaded during this audit.  They are more reliable than generated report line numbers because the generated indexes can lag behind active source edits.

- **Line:** 231; **Command context:** m_projective_scheme_CW_data; **Immediate issue:** 1-skeleton of projective scheme quotient is wedge of m circles; **Area:** surface-presentation infrastructure; **Severity:** High; **Recommended repair:** Define explicit polygon edge-scheme quotient and prove vertex collapse plus same-label edge circle lemma.
- **Line:** 304; **Command context:** Theorem_76_elementary_operations; **Immediate issue:** elementary scheme operation preserves quotient homeomorphism; **Area:** surface elementary moves; **Severity:** High; **Recommended repair:** Replace monolithic theorem with primitive move lemmas and rtranclp closure theorem.
- **Line:** 346; **Command context:** Theorem_75_4_H1_m_projective; **Immediate issue:** abelianization / Smith normal form for projective surface; **Area:** algebraic invariant; **Severity:** Medium; **Recommended repair:** Move abelianized presentation and integer-matrix normal form to algebra lemma; then instantiate 74.4 presentation.
- **Line:** 408; **Command context:** Theorem_78_1_triangulable_surface; **Immediate issue:** triangulable compact surface is quotient of disjoint simplex copies; **Area:** surface construction; **Severity:** High; **Recommended repair:** Make finite simplex-copy disjoint sum, boundary pairing, quotient map, and finite CW carrier explicit.
- **Line:** 444; **Command context:** Theorem_78_2_connected_polygonal_quotient; **Immediate issue:** merge finite triangulation into a single polygon; **Area:** surface construction; **Severity:** High; **Recommended repair:** Formalize dual graph, choose spanning tree, prove triangle-pasting preserves quotient type.
- **Line:** 484; **Command context:** Theorem_77_5_classification; **Immediate issue:** extract edge scheme from polygon quotient; **Area:** classification setup; **Severity:** Critical; **Recommended repair:** Introduce actual scheme extraction relation; do not obtain a free list from an undefined convention.
- **Line:** 500; **Command context:** Theorem_77_5_classification; **Immediate issue:** normal-form reduction by elementary operations; **Area:** classification combinatorics; **Severity:** Critical; **Recommended repair:** Define torus/projective schemes and prove combinatorial normal form independent of topology.
- **Line:** 502; **Command context:** Theorem_77_5_classification; **Immediate issue:** normal form implies standard surface homeomorphism type; **Area:** classification conclusion; **Severity:** Critical; **Recommended repair:** Prove quotient of normal scheme is sphere/torus/projective standard model.
- **Line:** 1060; **Command context:** Theorem_81_2_covering_group_iso; **Immediate issue:** deck transformation group is N(H)/H; **Area:** covering transformations; **Severity:** High; **Recommended repair:** Split into Lemma 81.1 fiber action, path-lift product law, normalizer quotient construction, and iso assembly.
- **Line:** 6327; **Command context:** Theorem_82_1_covering_existence; **Immediate issue:** pack canonical coset path-space construction into polymorphic existential; **Area:** covering existence / type packaging; **Severity:** Critical; **Recommended repair:** Restate theorem with canonical carrier type (path-class sets) or a fixed typedef locale; HOL cannot existentially quantify over a fresh type.
- **Line:** 8337; **Command context:** arc_locally_path_connected; **Immediate issue:** [0,1] locally path-connected extraction; **Area:** graph lpc/ssc recent blocker; **Severity:** Low; **Recommended repair:** Extract the already-proved hI_lpc proof from graph_locally_path_connected into I_set_locally_path_connected.
- **Line:** 8496; **Command context:** graph_semilocally_simply_connected; **Immediate issue:** interior point of an arc has a simply connected neighborhood; **Area:** graph ssc; **Severity:** Medium; **Recommended repair:** Use explicit interval chart around h^{-1} x and coherent topology; avoid arbitrary lpc V0 that might hit endpoints.
- **Line:** 8505; **Command context:** graph_semilocally_simply_connected; **Immediate issue:** vertex star neighborhood is simply connected; **Area:** graph ssc; **Severity:** High; **Recommended repair:** Define full incident-star from subarcs and prove contraction; avoid finite-valence assumption unless added explicitly.
- **Line:** 8621; **Command context:** schreier_rank_formula; **Immediate issue:** obtain covering corresponding to subgroup H; **Area:** early Schreier helper; **Severity:** Critical; **Recommended repair:** Depends on canonical Theorem 82.1 and isomorphism transfer of H into pi1 of a rose.
- **Line:** 8632; **Command context:** schreier_rank_formula; **Immediate issue:** E is graph and Euler/rank count; **Area:** early Schreier helper; **Severity:** High; **Recommended repair:** Move after graph-pi1 theorem; use graph covering, finite-sheet edge/vertex count, and rank = edges - vertices + 1.
- **Line:** 9610; **Command context:** graph_pi1_free_weak; **Immediate issue:** finite non-tree arcs reindexed from nat to hidden set type; **Area:** graph fundamental group; **Severity:** Critical; **Recommended repair:** Strengthen finite lemma to return generators indexed by non-tree arcs; add free_group_full_reindex_bij only as corollary.
- **Line:** 15828; **Command context:** Theorem_85_1_Nielsen_Schreier; **Immediate issue:** realize arbitrary free group as graph fundamental group; **Area:** Nielsen-Schreier; **Severity:** Critical; **Recommended repair:** Use wedge on the actual basis S for arbitrary S, relying on Theorem 71.3 and explicit graph arcs; finite-only wedge is insufficient.
- **Line:** 15844; **Command context:** Theorem_85_1_Nielsen_Schreier; **Immediate issue:** covering existence for subgroup image; **Area:** Nielsen-Schreier / covering existence; **Severity:** Critical; **Recommended repair:** Use canonical covering existence after transporting subgroup along the free-group/pi1 isomorphism.
- **Line:** 16064; **Command context:** Theorem_85_1_Nielsen_Schreier; **Immediate issue:** internal covering type escapes into polymorphic existential; **Area:** Nielsen-Schreier type packaging; **Severity:** Critical; **Recommended repair:** Restate freeness over a visible canonical index/carrier or use obtains inside the same context; do not existentially demand arbitrary type b.
- **Line:** 16125; **Command context:** Theorem_85_3_Schreier_index; **Immediate issue:** covering existence plus graph covering plus H correspondence; **Area:** Schreier index theorem; **Severity:** Critical; **Recommended repair:** Depends on fixed Theorem 82.1, graph-covering-is-graph, and finite sheet count.
- **Line:** 16278; **Command context:** Theorem_85_3_Schreier_index; **Immediate issue:** free-group transfer existential packaging; **Area:** Schreier index theorem; **Severity:** Critical; **Recommended repair:** Return the concrete basis set for the covering graph; transfer freeness without changing the index type.
- **Line:** 16283; **Command context:** Theorem_85_3_Schreier_index; **Immediate issue:** extract basis from existential hH_free; **Area:** Schreier index theorem; **Severity:** High; **Recommended repair:** Once the previous theorem returns a fixed SH, this extraction becomes ordinary obtain.
- **Line:** 16285; **Command context:** Theorem_85_3_Schreier_index; **Immediate issue:** Euler characteristic cardinal arithmetic card SH = k*n + 1; **Area:** Schreier index theorem; **Severity:** Medium; **Recommended repair:** Not pure arithmetic until vertex/edge multiplication and rank/Euler lemmas are available.
- **Line:** 16291; **Command context:** Theorem_85_3_Schreier_index; **Immediate issue:** show final existential and finite SH; **Area:** Schreier index theorem; **Severity:** Medium; **Recommended repair:** Derive finite SH from finite-sheet finite-rose cover before final blast/simp.

## Line 231: `m_projective_scheme_CW_data`

**Area.** surface-presentation infrastructure.  **Severity.** High.  **Immediate hole.** 1-skeleton of projective scheme quotient is wedge of m circles.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Define explicit polygon edge-scheme quotient and prove vertex collapse plus same-label edge circle lemma.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

The surface-classification region should be treated as a separate combinatorial/topological subproject.  The current theorem block uses scheme predicate names before they have real definitions in active code.  The right fix is not to add more local proof text; it is to introduce the scheme language.

Suggested starting API:

```isabelle
datatype 'e signed_edge = Pos 'e | Neg 'e

definition inverse_edge where
  "inverse_edge a = (case a of Pos e => Neg e | Neg e => Pos e)"

inductive top1_elementary_scheme_move :: "'e signed_edge list => 'e signed_edge list => bool" where
  rotate: "top1_elementary_scheme_move (u @ v) (v @ u)" |
  inverse: "top1_elementary_scheme_move w (rev (map inverse_edge w))" |
  relabel: "bij f (set (map edge_name w)) (set (map edge_name w')) ==>
            top1_elementary_scheme_move w (map_signed f w)" |
  cancel: "top1_elementary_scheme_move (u @ [a, inverse_edge a] @ v) (u @ v)" |
  cut_paste: "top1_scheme_cut_paste_condition u v w z ==>
              top1_elementary_scheme_move (u @ v @ w @ z) (u @ w @ v @ z)"

definition top1_elementary_scheme_equiv where
  "top1_elementary_scheme_equiv = top1_elementary_scheme_move^^**"
```

After these definitions, prove two independent chains: (1) combinatorial normal form under `top1_elementary_scheme_move` closure, and (2) topological invariance of the quotient space under each primitive move.  The classification theorem should then be a short assembly theorem.


## Line 304: `Theorem_76_elementary_operations`

**Area.** surface elementary moves.  **Severity.** High.  **Immediate hole.** elementary scheme operation preserves quotient homeomorphism.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Replace monolithic theorem with primitive move lemmas and rtranclp closure theorem.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

The surface-classification region should be treated as a separate combinatorial/topological subproject.  The current theorem block uses scheme predicate names before they have real definitions in active code.  The right fix is not to add more local proof text; it is to introduce the scheme language.

Suggested starting API:

```isabelle
datatype 'e signed_edge = Pos 'e | Neg 'e

definition inverse_edge where
  "inverse_edge a = (case a of Pos e => Neg e | Neg e => Pos e)"

inductive top1_elementary_scheme_move :: "'e signed_edge list => 'e signed_edge list => bool" where
  rotate: "top1_elementary_scheme_move (u @ v) (v @ u)" |
  inverse: "top1_elementary_scheme_move w (rev (map inverse_edge w))" |
  relabel: "bij f (set (map edge_name w)) (set (map edge_name w')) ==>
            top1_elementary_scheme_move w (map_signed f w)" |
  cancel: "top1_elementary_scheme_move (u @ [a, inverse_edge a] @ v) (u @ v)" |
  cut_paste: "top1_scheme_cut_paste_condition u v w z ==>
              top1_elementary_scheme_move (u @ v @ w @ z) (u @ w @ v @ z)"

definition top1_elementary_scheme_equiv where
  "top1_elementary_scheme_equiv = top1_elementary_scheme_move^^**"
```

After these definitions, prove two independent chains: (1) combinatorial normal form under `top1_elementary_scheme_move` closure, and (2) topological invariance of the quotient space under each primitive move.  The classification theorem should then be a short assembly theorem.


## Line 346: `Theorem_75_4_H1_m_projective`

**Area.** algebraic invariant.  **Severity.** Medium.  **Immediate hole.** abelianization / Smith normal form for projective surface.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Move abelianized presentation and integer-matrix normal form to algebra lemma; then instantiate 74.4 presentation.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

The surface-classification region should be treated as a separate combinatorial/topological subproject.  The current theorem block uses scheme predicate names before they have real definitions in active code.  The right fix is not to add more local proof text; it is to introduce the scheme language.

Suggested starting API:

```isabelle
datatype 'e signed_edge = Pos 'e | Neg 'e

definition inverse_edge where
  "inverse_edge a = (case a of Pos e => Neg e | Neg e => Pos e)"

inductive top1_elementary_scheme_move :: "'e signed_edge list => 'e signed_edge list => bool" where
  rotate: "top1_elementary_scheme_move (u @ v) (v @ u)" |
  inverse: "top1_elementary_scheme_move w (rev (map inverse_edge w))" |
  relabel: "bij f (set (map edge_name w)) (set (map edge_name w')) ==>
            top1_elementary_scheme_move w (map_signed f w)" |
  cancel: "top1_elementary_scheme_move (u @ [a, inverse_edge a] @ v) (u @ v)" |
  cut_paste: "top1_scheme_cut_paste_condition u v w z ==>
              top1_elementary_scheme_move (u @ v @ w @ z) (u @ w @ v @ z)"

definition top1_elementary_scheme_equiv where
  "top1_elementary_scheme_equiv = top1_elementary_scheme_move^^**"
```

After these definitions, prove two independent chains: (1) combinatorial normal form under `top1_elementary_scheme_move` closure, and (2) topological invariance of the quotient space under each primitive move.  The classification theorem should then be a short assembly theorem.


## Line 408: `Theorem_78_1_triangulable_surface`

**Area.** surface construction.  **Severity.** High.  **Immediate hole.** triangulable compact surface is quotient of disjoint simplex copies.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Make finite simplex-copy disjoint sum, boundary pairing, quotient map, and finite CW carrier explicit.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

The surface-classification region should be treated as a separate combinatorial/topological subproject.  The current theorem block uses scheme predicate names before they have real definitions in active code.  The right fix is not to add more local proof text; it is to introduce the scheme language.

Suggested starting API:

```isabelle
datatype 'e signed_edge = Pos 'e | Neg 'e

definition inverse_edge where
  "inverse_edge a = (case a of Pos e => Neg e | Neg e => Pos e)"

inductive top1_elementary_scheme_move :: "'e signed_edge list => 'e signed_edge list => bool" where
  rotate: "top1_elementary_scheme_move (u @ v) (v @ u)" |
  inverse: "top1_elementary_scheme_move w (rev (map inverse_edge w))" |
  relabel: "bij f (set (map edge_name w)) (set (map edge_name w')) ==>
            top1_elementary_scheme_move w (map_signed f w)" |
  cancel: "top1_elementary_scheme_move (u @ [a, inverse_edge a] @ v) (u @ v)" |
  cut_paste: "top1_scheme_cut_paste_condition u v w z ==>
              top1_elementary_scheme_move (u @ v @ w @ z) (u @ w @ v @ z)"

definition top1_elementary_scheme_equiv where
  "top1_elementary_scheme_equiv = top1_elementary_scheme_move^^**"
```

After these definitions, prove two independent chains: (1) combinatorial normal form under `top1_elementary_scheme_move` closure, and (2) topological invariance of the quotient space under each primitive move.  The classification theorem should then be a short assembly theorem.


## Line 444: `Theorem_78_2_connected_polygonal_quotient`

**Area.** surface construction.  **Severity.** High.  **Immediate hole.** merge finite triangulation into a single polygon.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Formalize dual graph, choose spanning tree, prove triangle-pasting preserves quotient type.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

The surface-classification region should be treated as a separate combinatorial/topological subproject.  The current theorem block uses scheme predicate names before they have real definitions in active code.  The right fix is not to add more local proof text; it is to introduce the scheme language.

Suggested starting API:

```isabelle
datatype 'e signed_edge = Pos 'e | Neg 'e

definition inverse_edge where
  "inverse_edge a = (case a of Pos e => Neg e | Neg e => Pos e)"

inductive top1_elementary_scheme_move :: "'e signed_edge list => 'e signed_edge list => bool" where
  rotate: "top1_elementary_scheme_move (u @ v) (v @ u)" |
  inverse: "top1_elementary_scheme_move w (rev (map inverse_edge w))" |
  relabel: "bij f (set (map edge_name w)) (set (map edge_name w')) ==>
            top1_elementary_scheme_move w (map_signed f w)" |
  cancel: "top1_elementary_scheme_move (u @ [a, inverse_edge a] @ v) (u @ v)" |
  cut_paste: "top1_scheme_cut_paste_condition u v w z ==>
              top1_elementary_scheme_move (u @ v @ w @ z) (u @ w @ v @ z)"

definition top1_elementary_scheme_equiv where
  "top1_elementary_scheme_equiv = top1_elementary_scheme_move^^**"
```

After these definitions, prove two independent chains: (1) combinatorial normal form under `top1_elementary_scheme_move` closure, and (2) topological invariance of the quotient space under each primitive move.  The classification theorem should then be a short assembly theorem.


## Line 484: `Theorem_77_5_classification`

**Area.** classification setup.  **Severity.** Critical.  **Immediate hole.** extract edge scheme from polygon quotient.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Introduce actual scheme extraction relation; do not obtain a free list from an undefined convention.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

The surface-classification region should be treated as a separate combinatorial/topological subproject.  The current theorem block uses scheme predicate names before they have real definitions in active code.  The right fix is not to add more local proof text; it is to introduce the scheme language.

Suggested starting API:

```isabelle
datatype 'e signed_edge = Pos 'e | Neg 'e

definition inverse_edge where
  "inverse_edge a = (case a of Pos e => Neg e | Neg e => Pos e)"

inductive top1_elementary_scheme_move :: "'e signed_edge list => 'e signed_edge list => bool" where
  rotate: "top1_elementary_scheme_move (u @ v) (v @ u)" |
  inverse: "top1_elementary_scheme_move w (rev (map inverse_edge w))" |
  relabel: "bij f (set (map edge_name w)) (set (map edge_name w')) ==>
            top1_elementary_scheme_move w (map_signed f w)" |
  cancel: "top1_elementary_scheme_move (u @ [a, inverse_edge a] @ v) (u @ v)" |
  cut_paste: "top1_scheme_cut_paste_condition u v w z ==>
              top1_elementary_scheme_move (u @ v @ w @ z) (u @ w @ v @ z)"

definition top1_elementary_scheme_equiv where
  "top1_elementary_scheme_equiv = top1_elementary_scheme_move^^**"
```

After these definitions, prove two independent chains: (1) combinatorial normal form under `top1_elementary_scheme_move` closure, and (2) topological invariance of the quotient space under each primitive move.  The classification theorem should then be a short assembly theorem.


## Line 500: `Theorem_77_5_classification`

**Area.** classification combinatorics.  **Severity.** Critical.  **Immediate hole.** normal-form reduction by elementary operations.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Define torus/projective schemes and prove combinatorial normal form independent of topology.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

The surface-classification region should be treated as a separate combinatorial/topological subproject.  The current theorem block uses scheme predicate names before they have real definitions in active code.  The right fix is not to add more local proof text; it is to introduce the scheme language.

Suggested starting API:

```isabelle
datatype 'e signed_edge = Pos 'e | Neg 'e

definition inverse_edge where
  "inverse_edge a = (case a of Pos e => Neg e | Neg e => Pos e)"

inductive top1_elementary_scheme_move :: "'e signed_edge list => 'e signed_edge list => bool" where
  rotate: "top1_elementary_scheme_move (u @ v) (v @ u)" |
  inverse: "top1_elementary_scheme_move w (rev (map inverse_edge w))" |
  relabel: "bij f (set (map edge_name w)) (set (map edge_name w')) ==>
            top1_elementary_scheme_move w (map_signed f w)" |
  cancel: "top1_elementary_scheme_move (u @ [a, inverse_edge a] @ v) (u @ v)" |
  cut_paste: "top1_scheme_cut_paste_condition u v w z ==>
              top1_elementary_scheme_move (u @ v @ w @ z) (u @ w @ v @ z)"

definition top1_elementary_scheme_equiv where
  "top1_elementary_scheme_equiv = top1_elementary_scheme_move^^**"
```

After these definitions, prove two independent chains: (1) combinatorial normal form under `top1_elementary_scheme_move` closure, and (2) topological invariance of the quotient space under each primitive move.  The classification theorem should then be a short assembly theorem.


## Line 502: `Theorem_77_5_classification`

**Area.** classification conclusion.  **Severity.** Critical.  **Immediate hole.** normal form implies standard surface homeomorphism type.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Prove quotient of normal scheme is sphere/torus/projective standard model.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

The surface-classification region should be treated as a separate combinatorial/topological subproject.  The current theorem block uses scheme predicate names before they have real definitions in active code.  The right fix is not to add more local proof text; it is to introduce the scheme language.

Suggested starting API:

```isabelle
datatype 'e signed_edge = Pos 'e | Neg 'e

definition inverse_edge where
  "inverse_edge a = (case a of Pos e => Neg e | Neg e => Pos e)"

inductive top1_elementary_scheme_move :: "'e signed_edge list => 'e signed_edge list => bool" where
  rotate: "top1_elementary_scheme_move (u @ v) (v @ u)" |
  inverse: "top1_elementary_scheme_move w (rev (map inverse_edge w))" |
  relabel: "bij f (set (map edge_name w)) (set (map edge_name w')) ==>
            top1_elementary_scheme_move w (map_signed f w)" |
  cancel: "top1_elementary_scheme_move (u @ [a, inverse_edge a] @ v) (u @ v)" |
  cut_paste: "top1_scheme_cut_paste_condition u v w z ==>
              top1_elementary_scheme_move (u @ v @ w @ z) (u @ w @ v @ z)"

definition top1_elementary_scheme_equiv where
  "top1_elementary_scheme_equiv = top1_elementary_scheme_move^^**"
```

After these definitions, prove two independent chains: (1) combinatorial normal form under `top1_elementary_scheme_move` closure, and (2) topological invariance of the quotient space under each primitive move.  The classification theorem should then be a short assembly theorem.


## Line 1060: `Theorem_81_2_covering_group_iso`

**Area.** covering transformations.  **Severity.** High.  **Immediate hole.** deck transformation group is N(H)/H.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Split into Lemma 81.1 fiber action, path-lift product law, normalizer quotient construction, and iso assembly.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

The deck-transformation theorem should be split into four named lemmas.  First, define the action of deck transformations on the fiber over `b0`.  Second, prove the Munkres Lemma 81.1 characterization of which fiber points are reached by loops in the normalizer.  Third, build the quotient group `N(H)/H` with an explicit carrier and multiplication.  Fourth, prove that the path-lift endpoint map is a group isomorphism.  This prevents the final theorem from carrying all lifting-product details inside one giant proof.


## Line 6327: `Theorem_82_1_covering_existence`

**Area.** covering existence / type packaging.  **Severity.** Critical.  **Immediate hole.** pack canonical coset path-space construction into polymorphic existential.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Restate theorem with canonical carrier type (path-class sets) or a fixed typedef locale; HOL cannot existentially quantify over a fresh type.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

This is the central HOL type-packaging blocker.  The local proof already reaches an existential over `TE`, `p`, and `e0` for the concrete carrier `?E`.  The theorem conclusion, however, is polymorphic over a result type that was not chosen by the theorem statement.  Isabelle/HOL cannot introduce a fresh type as an existential witness.  A proof method cannot fix this.  The theorem statement must expose the constructed carrier.

Recommended replacement statement:

```isabelle
type_synonym 'b top1_path = "real => 'b"
type_synonym 'b top1_path_class = "('b top1_path) set"

abbreviation top1_covering_coset_space ::
  "'b set => 'b topology => 'b => (('b top1_path) set) set => 'b top1_path_class set" where
  "top1_covering_coset_space B TB b0 H ==
     (top1_path_coset_class B TB b0 H) ` top1_basepoint_paths B TB b0"

theorem Theorem_82_1_covering_existence_canonical:
  fixes B :: "'b set" and TB :: "'b topology" and b0 :: 'b
  assumes "is_topology_on_strict B TB"
      and "top1_path_connected_on B TB"
      and "top1_locally_path_connected_on B TB"
      and "top1_semilocally_simply_connected_on B TB"
      and "b0 in B"
      and "H subseteq top1_fundamental_group_carrier B TB b0"
      and "group_on H (top1_fundamental_group_mul B TB b0) ..."
  shows "let E = top1_covering_coset_space B TB b0 H in
    exists TE p e0.
      is_topology_on_strict E TE &
      top1_covering_map_on E TE B TB (p :: 'b top1_path_class => 'b) &
      top1_path_connected_on E TE &
      top1_locally_path_connected_on E TE &
      e0 in E & p e0 = b0 &
      top1_fundamental_group_image_hom E TE e0 B TB b0 p = H"
```

After this replacement, downstream Section 85 theorems should refer to the canonical `E`, not to an arbitrary type variable.  If a prettier abstract covering type is wanted, introduce it as an explicit locale parameter or as a typedef in a separate construction theory; do not hide it behind an unconstrained existential.


## Line 8337: `arc_locally_path_connected`

**Area.** graph lpc/ssc recent blocker.  **Severity.** Low.  **Immediate hole.** [0,1] locally path-connected extraction.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Extract the already-proved hI_lpc proof from graph_locally_path_connected into I_set_locally_path_connected.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

For graph semilocal simple connectivity, prefer named geometric lemmas over a long local proof.  The current graph definition hides the arc family, so the cleanest version first introduces an explicit arc-family predicate or locale.

Interior case target:

```isabelle
lemma graph_ssc_interior_chart:
  assumes graph: "top1_is_graph_with_arcs_on X TX I A"
      and i0: "i0 in I"
      and x: "x in A i0"
      and xint: "x notin top1_arc_endpoints_on (A i0) (subspace_topology X TX (A i0))"
  obtains U where
      "x in U" "U in TX" "U subseteq A i0"
      "top1_simply_connected_on U (subspace_topology X TX U)"
proof -
  -- "Choose a homeomorphism h : I_set -> A i0 and t0 with h t0 = x."
  -- "Use xint to get 0 < t0 and t0 < 1. Pick eps with closed ball inside (0,1)."
  -- "Let J = {t in I_set. abs(t - t0) < eps}; let U = h ` J."
  -- "U is open in A i0 and simply connected because J is convex."
  -- "U avoids endpoints, hence avoids every other arc by the graph intersection axiom."
  -- "Coherent topology gives U in TX."
qed
```

Vertex case target:

```isabelle
definition graph_vertex_star where
  "graph_vertex_star X TX I A x eps =
     Union ((\<lambda>i. top1_initial_subarc_towards_endpoint X TX (A i) x eps) ` {i in I. x in A i})"

lemma graph_vertex_star_contractible:
  assumes graph: "top1_is_graph_with_arcs_on X TX I A"
      and vertex: "top1_graph_vertex X TX I A x"
      and eps: "0 < eps" "eps < 1/2"
  shows "top1_deformation_retract_of_on
           (graph_vertex_star X TX I A x eps)
           (subspace_topology X TX (graph_vertex_star X TX I A x eps))
           {x}"
```

The vertex proof should not silently assume finite valence.  If the formal graph definition includes finite valence, state and use it.  If it does not, the star construction must be the full incident star and the contraction proof must work for an arbitrary incident family under the coherent topology.


## Line 8496: `graph_semilocally_simply_connected`

**Area.** graph ssc.  **Severity.** Medium.  **Immediate hole.** interior point of an arc has a simply connected neighborhood.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Use explicit interval chart around h^{-1} x and coherent topology; avoid arbitrary lpc V0 that might hit endpoints.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

For graph semilocal simple connectivity, prefer named geometric lemmas over a long local proof.  The current graph definition hides the arc family, so the cleanest version first introduces an explicit arc-family predicate or locale.

Interior case target:

```isabelle
lemma graph_ssc_interior_chart:
  assumes graph: "top1_is_graph_with_arcs_on X TX I A"
      and i0: "i0 in I"
      and x: "x in A i0"
      and xint: "x notin top1_arc_endpoints_on (A i0) (subspace_topology X TX (A i0))"
  obtains U where
      "x in U" "U in TX" "U subseteq A i0"
      "top1_simply_connected_on U (subspace_topology X TX U)"
proof -
  -- "Choose a homeomorphism h : I_set -> A i0 and t0 with h t0 = x."
  -- "Use xint to get 0 < t0 and t0 < 1. Pick eps with closed ball inside (0,1)."
  -- "Let J = {t in I_set. abs(t - t0) < eps}; let U = h ` J."
  -- "U is open in A i0 and simply connected because J is convex."
  -- "U avoids endpoints, hence avoids every other arc by the graph intersection axiom."
  -- "Coherent topology gives U in TX."
qed
```

Vertex case target:

```isabelle
definition graph_vertex_star where
  "graph_vertex_star X TX I A x eps =
     Union ((\<lambda>i. top1_initial_subarc_towards_endpoint X TX (A i) x eps) ` {i in I. x in A i})"

lemma graph_vertex_star_contractible:
  assumes graph: "top1_is_graph_with_arcs_on X TX I A"
      and vertex: "top1_graph_vertex X TX I A x"
      and eps: "0 < eps" "eps < 1/2"
  shows "top1_deformation_retract_of_on
           (graph_vertex_star X TX I A x eps)
           (subspace_topology X TX (graph_vertex_star X TX I A x eps))
           {x}"
```

The vertex proof should not silently assume finite valence.  If the formal graph definition includes finite valence, state and use it.  If it does not, the star construction must be the full incident star and the contraction proof must work for an arbitrary incident family under the coherent topology.


## Line 8505: `graph_semilocally_simply_connected`

**Area.** graph ssc.  **Severity.** High.  **Immediate hole.** vertex star neighborhood is simply connected.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Define full incident-star from subarcs and prove contraction; avoid finite-valence assumption unless added explicitly.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

For graph semilocal simple connectivity, prefer named geometric lemmas over a long local proof.  The current graph definition hides the arc family, so the cleanest version first introduces an explicit arc-family predicate or locale.

Interior case target:

```isabelle
lemma graph_ssc_interior_chart:
  assumes graph: "top1_is_graph_with_arcs_on X TX I A"
      and i0: "i0 in I"
      and x: "x in A i0"
      and xint: "x notin top1_arc_endpoints_on (A i0) (subspace_topology X TX (A i0))"
  obtains U where
      "x in U" "U in TX" "U subseteq A i0"
      "top1_simply_connected_on U (subspace_topology X TX U)"
proof -
  -- "Choose a homeomorphism h : I_set -> A i0 and t0 with h t0 = x."
  -- "Use xint to get 0 < t0 and t0 < 1. Pick eps with closed ball inside (0,1)."
  -- "Let J = {t in I_set. abs(t - t0) < eps}; let U = h ` J."
  -- "U is open in A i0 and simply connected because J is convex."
  -- "U avoids endpoints, hence avoids every other arc by the graph intersection axiom."
  -- "Coherent topology gives U in TX."
qed
```

Vertex case target:

```isabelle
definition graph_vertex_star where
  "graph_vertex_star X TX I A x eps =
     Union ((\<lambda>i. top1_initial_subarc_towards_endpoint X TX (A i) x eps) ` {i in I. x in A i})"

lemma graph_vertex_star_contractible:
  assumes graph: "top1_is_graph_with_arcs_on X TX I A"
      and vertex: "top1_graph_vertex X TX I A x"
      and eps: "0 < eps" "eps < 1/2"
  shows "top1_deformation_retract_of_on
           (graph_vertex_star X TX I A x eps)
           (subspace_topology X TX (graph_vertex_star X TX I A x eps))
           {x}"
```

The vertex proof should not silently assume finite valence.  If the formal graph definition includes finite valence, state and use it.  If it does not, the star construction must be the full incident star and the contraction proof must work for an arbitrary incident family under the coherent topology.


## Line 8621: `schreier_rank_formula`

**Area.** early Schreier helper.  **Severity.** Critical.  **Immediate hole.** obtain covering corresponding to subgroup H.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Depends on canonical Theorem 82.1 and isomorphism transfer of H into pi1 of a rose.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

For Section 85, the proof should be rebuilt around a fixed rose/wedge model and a canonical covering carrier.  Once the covering graph is concrete, the Euler calculation becomes a short final step.  Until then, it is not a simple arithmetic proof.

Recommended finite-rank spine:

```isabelle
lemma rose_covering_rank_count:
  assumes rose: "top1_is_rose_graph_on X TX x0 S" and finiteS: "finite S"
      and cover: "top1_finite_sheeted_graph_covering_on E TE X TX p k"
      and conn: "top1_connected_on E TE"
  obtains SH gen where
      "top1_is_free_group_full_on (pi1 E TE e0) (pi1_mul E TE e0) ... gen SH"
      "finite SH"
      "card SH = k * card S - k + 1"

corollary Theorem_85_3_Schreier_index_fixed:
  assumes "top1_is_free_group_full_on F mul e inv gen S"
      and "finite S" "card S = n + 1"
      and "top1_subgroup_on H F mul e inv" "top1_group_index F mul H = k"
  obtains genH SH where
      "top1_is_free_group_full_on H mul e inv genH SH"
      "finite SH" "card SH = k * n + 1"
```

The crucial prerequisite is a graph-covering counting theorem: vertices in the covering are counted sheetwise over base vertices, and edges in the covering are counted sheetwise over base edges.  With a base rose having one vertex and `n+1` edges, the covering has `k` vertices and `k*(n+1)` edges, so the connected graph rank is `k*(n+1) - k + 1 = k*n + 1`.


## Line 8632: `schreier_rank_formula`

**Area.** early Schreier helper.  **Severity.** High.  **Immediate hole.** E is graph and Euler/rank count.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Move after graph-pi1 theorem; use graph covering, finite-sheet edge/vertex count, and rank = edges - vertices + 1.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

For Section 85, the proof should be rebuilt around a fixed rose/wedge model and a canonical covering carrier.  Once the covering graph is concrete, the Euler calculation becomes a short final step.  Until then, it is not a simple arithmetic proof.

Recommended finite-rank spine:

```isabelle
lemma rose_covering_rank_count:
  assumes rose: "top1_is_rose_graph_on X TX x0 S" and finiteS: "finite S"
      and cover: "top1_finite_sheeted_graph_covering_on E TE X TX p k"
      and conn: "top1_connected_on E TE"
  obtains SH gen where
      "top1_is_free_group_full_on (pi1 E TE e0) (pi1_mul E TE e0) ... gen SH"
      "finite SH"
      "card SH = k * card S - k + 1"

corollary Theorem_85_3_Schreier_index_fixed:
  assumes "top1_is_free_group_full_on F mul e inv gen S"
      and "finite S" "card S = n + 1"
      and "top1_subgroup_on H F mul e inv" "top1_group_index F mul H = k"
  obtains genH SH where
      "top1_is_free_group_full_on H mul e inv genH SH"
      "finite SH" "card SH = k * n + 1"
```

The crucial prerequisite is a graph-covering counting theorem: vertices in the covering are counted sheetwise over base vertices, and edges in the covering are counted sheetwise over base edges.  With a base rose having one vertex and `n+1` edges, the covering has `k` vertices and `k*(n+1)` edges, so the connected graph rank is `k*(n+1) - k + 1 = k*n + 1`.


## Line 9610: `graph_pi1_free_weak`

**Area.** graph fundamental group.  **Severity.** Critical.  **Immediate hole.** finite non-tree arcs reindexed from nat to hidden set type.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Strengthen finite lemma to return generators indexed by non-tree arcs; add free_group_full_reindex_bij only as corollary.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

The current proof tries to reindex a finite `nat`-indexed helper back to a hidden set type.  This is structurally backwards.  The graph theorem should first produce a basis indexed by the non-tree arcs.  Only then should a finite or countable corollary reindex to `nat`.

Recommended theorem shape:

```isabelle
theorem graph_pi1_free_indexed:
  assumes "top1_is_graph_with_arcs_on X TX I A"
      and "top1_connected_on X TX"
      and "x0 in X"
  obtains T gen where
      "top1_is_spanning_tree_for_arcs X TX I A T"
      "top1_is_free_group_full_on
          (top1_fundamental_group_carrier X TX x0)
          (top1_fundamental_group_mul X TX x0)
          (top1_fundamental_group_id X TX x0)
          (top1_fundamental_group_invg X TX x0)
          gen {i in I. i notin T}"
```

A general reindex lemma is still useful, but it must be used after the source and target basis sets are known to be bijective:

```isabelle
lemma free_group_full_reindex_bij:
  assumes hfree: "top1_is_free_group_full_on G mul e inv i S"
      and hb: "bij_betw b S' S"
  shows "top1_is_free_group_full_on G mul e inv (\<lambda>s'. i (b s')) S'"
proof -
  -- "Unfold top1_is_free_group_full_on_def."
  -- "Use inj_on_comp plus bij_betw_imp_inj_on for generator injectivity."
  -- "Use b ` S' = S for generated subgroup equality."
  -- "Translate every reduced word over S' by map b; non-empty and reducedness are preserved by injectivity."
  -- "Apply hfree to the translated word, then rewrite evaluation by composition."
qed
```


## Line 15828: `Theorem_85_1_Nielsen_Schreier`

**Area.** Nielsen-Schreier.  **Severity.** Critical.  **Immediate hole.** realize arbitrary free group as graph fundamental group.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Use wedge on the actual basis S for arbitrary S, relying on Theorem 71.3 and explicit graph arcs; finite-only wedge is insufficient.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

For Section 85, the proof should be rebuilt around a fixed rose/wedge model and a canonical covering carrier.  Once the covering graph is concrete, the Euler calculation becomes a short final step.  Until then, it is not a simple arithmetic proof.

Recommended finite-rank spine:

```isabelle
lemma rose_covering_rank_count:
  assumes rose: "top1_is_rose_graph_on X TX x0 S" and finiteS: "finite S"
      and cover: "top1_finite_sheeted_graph_covering_on E TE X TX p k"
      and conn: "top1_connected_on E TE"
  obtains SH gen where
      "top1_is_free_group_full_on (pi1 E TE e0) (pi1_mul E TE e0) ... gen SH"
      "finite SH"
      "card SH = k * card S - k + 1"

corollary Theorem_85_3_Schreier_index_fixed:
  assumes "top1_is_free_group_full_on F mul e inv gen S"
      and "finite S" "card S = n + 1"
      and "top1_subgroup_on H F mul e inv" "top1_group_index F mul H = k"
  obtains genH SH where
      "top1_is_free_group_full_on H mul e inv genH SH"
      "finite SH" "card SH = k * n + 1"
```

The crucial prerequisite is a graph-covering counting theorem: vertices in the covering are counted sheetwise over base vertices, and edges in the covering are counted sheetwise over base edges.  With a base rose having one vertex and `n+1` edges, the covering has `k` vertices and `k*(n+1)` edges, so the connected graph rank is `k*(n+1) - k + 1 = k*n + 1`.


## Line 15844: `Theorem_85_1_Nielsen_Schreier`

**Area.** Nielsen-Schreier / covering existence.  **Severity.** Critical.  **Immediate hole.** covering existence for subgroup image.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Use canonical covering existence after transporting subgroup along the free-group/pi1 isomorphism.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

For Section 85, the proof should be rebuilt around a fixed rose/wedge model and a canonical covering carrier.  Once the covering graph is concrete, the Euler calculation becomes a short final step.  Until then, it is not a simple arithmetic proof.

Recommended finite-rank spine:

```isabelle
lemma rose_covering_rank_count:
  assumes rose: "top1_is_rose_graph_on X TX x0 S" and finiteS: "finite S"
      and cover: "top1_finite_sheeted_graph_covering_on E TE X TX p k"
      and conn: "top1_connected_on E TE"
  obtains SH gen where
      "top1_is_free_group_full_on (pi1 E TE e0) (pi1_mul E TE e0) ... gen SH"
      "finite SH"
      "card SH = k * card S - k + 1"

corollary Theorem_85_3_Schreier_index_fixed:
  assumes "top1_is_free_group_full_on F mul e inv gen S"
      and "finite S" "card S = n + 1"
      and "top1_subgroup_on H F mul e inv" "top1_group_index F mul H = k"
  obtains genH SH where
      "top1_is_free_group_full_on H mul e inv genH SH"
      "finite SH" "card SH = k * n + 1"
```

The crucial prerequisite is a graph-covering counting theorem: vertices in the covering are counted sheetwise over base vertices, and edges in the covering are counted sheetwise over base edges.  With a base rose having one vertex and `n+1` edges, the covering has `k` vertices and `k*(n+1)` edges, so the connected graph rank is `k*(n+1) - k + 1 = k*n + 1`.


## Line 16064: `Theorem_85_1_Nielsen_Schreier`

**Area.** Nielsen-Schreier type packaging.  **Severity.** Critical.  **Immediate hole.** internal covering type escapes into polymorphic existential.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Restate freeness over a visible canonical index/carrier or use obtains inside the same context; do not existentially demand arbitrary type b.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

For Section 85, the proof should be rebuilt around a fixed rose/wedge model and a canonical covering carrier.  Once the covering graph is concrete, the Euler calculation becomes a short final step.  Until then, it is not a simple arithmetic proof.

Recommended finite-rank spine:

```isabelle
lemma rose_covering_rank_count:
  assumes rose: "top1_is_rose_graph_on X TX x0 S" and finiteS: "finite S"
      and cover: "top1_finite_sheeted_graph_covering_on E TE X TX p k"
      and conn: "top1_connected_on E TE"
  obtains SH gen where
      "top1_is_free_group_full_on (pi1 E TE e0) (pi1_mul E TE e0) ... gen SH"
      "finite SH"
      "card SH = k * card S - k + 1"

corollary Theorem_85_3_Schreier_index_fixed:
  assumes "top1_is_free_group_full_on F mul e inv gen S"
      and "finite S" "card S = n + 1"
      and "top1_subgroup_on H F mul e inv" "top1_group_index F mul H = k"
  obtains genH SH where
      "top1_is_free_group_full_on H mul e inv genH SH"
      "finite SH" "card SH = k * n + 1"
```

The crucial prerequisite is a graph-covering counting theorem: vertices in the covering are counted sheetwise over base vertices, and edges in the covering are counted sheetwise over base edges.  With a base rose having one vertex and `n+1` edges, the covering has `k` vertices and `k*(n+1)` edges, so the connected graph rank is `k*(n+1) - k + 1 = k*n + 1`.


## Line 16125: `Theorem_85_3_Schreier_index`

**Area.** Schreier index theorem.  **Severity.** Critical.  **Immediate hole.** covering existence plus graph covering plus H correspondence.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Depends on fixed Theorem 82.1, graph-covering-is-graph, and finite sheet count.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

For Section 85, the proof should be rebuilt around a fixed rose/wedge model and a canonical covering carrier.  Once the covering graph is concrete, the Euler calculation becomes a short final step.  Until then, it is not a simple arithmetic proof.

Recommended finite-rank spine:

```isabelle
lemma rose_covering_rank_count:
  assumes rose: "top1_is_rose_graph_on X TX x0 S" and finiteS: "finite S"
      and cover: "top1_finite_sheeted_graph_covering_on E TE X TX p k"
      and conn: "top1_connected_on E TE"
  obtains SH gen where
      "top1_is_free_group_full_on (pi1 E TE e0) (pi1_mul E TE e0) ... gen SH"
      "finite SH"
      "card SH = k * card S - k + 1"

corollary Theorem_85_3_Schreier_index_fixed:
  assumes "top1_is_free_group_full_on F mul e inv gen S"
      and "finite S" "card S = n + 1"
      and "top1_subgroup_on H F mul e inv" "top1_group_index F mul H = k"
  obtains genH SH where
      "top1_is_free_group_full_on H mul e inv genH SH"
      "finite SH" "card SH = k * n + 1"
```

The crucial prerequisite is a graph-covering counting theorem: vertices in the covering are counted sheetwise over base vertices, and edges in the covering are counted sheetwise over base edges.  With a base rose having one vertex and `n+1` edges, the covering has `k` vertices and `k*(n+1)` edges, so the connected graph rank is `k*(n+1) - k + 1 = k*n + 1`.


## Line 16278: `Theorem_85_3_Schreier_index`

**Area.** Schreier index theorem.  **Severity.** Critical.  **Immediate hole.** free-group transfer existential packaging.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Return the concrete basis set for the covering graph; transfer freeness without changing the index type.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

For Section 85, the proof should be rebuilt around a fixed rose/wedge model and a canonical covering carrier.  Once the covering graph is concrete, the Euler calculation becomes a short final step.  Until then, it is not a simple arithmetic proof.

Recommended finite-rank spine:

```isabelle
lemma rose_covering_rank_count:
  assumes rose: "top1_is_rose_graph_on X TX x0 S" and finiteS: "finite S"
      and cover: "top1_finite_sheeted_graph_covering_on E TE X TX p k"
      and conn: "top1_connected_on E TE"
  obtains SH gen where
      "top1_is_free_group_full_on (pi1 E TE e0) (pi1_mul E TE e0) ... gen SH"
      "finite SH"
      "card SH = k * card S - k + 1"

corollary Theorem_85_3_Schreier_index_fixed:
  assumes "top1_is_free_group_full_on F mul e inv gen S"
      and "finite S" "card S = n + 1"
      and "top1_subgroup_on H F mul e inv" "top1_group_index F mul H = k"
  obtains genH SH where
      "top1_is_free_group_full_on H mul e inv genH SH"
      "finite SH" "card SH = k * n + 1"
```

The crucial prerequisite is a graph-covering counting theorem: vertices in the covering are counted sheetwise over base vertices, and edges in the covering are counted sheetwise over base edges.  With a base rose having one vertex and `n+1` edges, the covering has `k` vertices and `k*(n+1)` edges, so the connected graph rank is `k*(n+1) - k + 1 = k*n + 1`.


## Line 16283: `Theorem_85_3_Schreier_index`

**Area.** Schreier index theorem.  **Severity.** High.  **Immediate hole.** extract basis from existential hH_free.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Once the previous theorem returns a fixed SH, this extraction becomes ordinary obtain.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

For Section 85, the proof should be rebuilt around a fixed rose/wedge model and a canonical covering carrier.  Once the covering graph is concrete, the Euler calculation becomes a short final step.  Until then, it is not a simple arithmetic proof.

Recommended finite-rank spine:

```isabelle
lemma rose_covering_rank_count:
  assumes rose: "top1_is_rose_graph_on X TX x0 S" and finiteS: "finite S"
      and cover: "top1_finite_sheeted_graph_covering_on E TE X TX p k"
      and conn: "top1_connected_on E TE"
  obtains SH gen where
      "top1_is_free_group_full_on (pi1 E TE e0) (pi1_mul E TE e0) ... gen SH"
      "finite SH"
      "card SH = k * card S - k + 1"

corollary Theorem_85_3_Schreier_index_fixed:
  assumes "top1_is_free_group_full_on F mul e inv gen S"
      and "finite S" "card S = n + 1"
      and "top1_subgroup_on H F mul e inv" "top1_group_index F mul H = k"
  obtains genH SH where
      "top1_is_free_group_full_on H mul e inv genH SH"
      "finite SH" "card SH = k * n + 1"
```

The crucial prerequisite is a graph-covering counting theorem: vertices in the covering are counted sheetwise over base vertices, and edges in the covering are counted sheetwise over base edges.  With a base rose having one vertex and `n+1` edges, the covering has `k` vertices and `k*(n+1)` edges, so the connected graph rank is `k*(n+1) - k + 1 = k*n + 1`.


## Line 16285: `Theorem_85_3_Schreier_index`

**Area.** Schreier index theorem.  **Severity.** Medium.  **Immediate hole.** Euler characteristic cardinal arithmetic card SH = k*n + 1.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Not pure arithmetic until vertex/edge multiplication and rank/Euler lemmas are available.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

For Section 85, the proof should be rebuilt around a fixed rose/wedge model and a canonical covering carrier.  Once the covering graph is concrete, the Euler calculation becomes a short final step.  Until then, it is not a simple arithmetic proof.

Recommended finite-rank spine:

```isabelle
lemma rose_covering_rank_count:
  assumes rose: "top1_is_rose_graph_on X TX x0 S" and finiteS: "finite S"
      and cover: "top1_finite_sheeted_graph_covering_on E TE X TX p k"
      and conn: "top1_connected_on E TE"
  obtains SH gen where
      "top1_is_free_group_full_on (pi1 E TE e0) (pi1_mul E TE e0) ... gen SH"
      "finite SH"
      "card SH = k * card S - k + 1"

corollary Theorem_85_3_Schreier_index_fixed:
  assumes "top1_is_free_group_full_on F mul e inv gen S"
      and "finite S" "card S = n + 1"
      and "top1_subgroup_on H F mul e inv" "top1_group_index F mul H = k"
  obtains genH SH where
      "top1_is_free_group_full_on H mul e inv genH SH"
      "finite SH" "card SH = k * n + 1"
```

The crucial prerequisite is a graph-covering counting theorem: vertices in the covering are counted sheetwise over base vertices, and edges in the covering are counted sheetwise over base edges.  With a base rose having one vertex and `n+1` edges, the covering has `k` vertices and `k*(n+1)` edges, so the connected graph rank is `k*(n+1) - k + 1 = k*n + 1`.


## Line 16291: `Theorem_85_3_Schreier_index`

**Area.** Schreier index theorem.  **Severity.** Medium.  **Immediate hole.** show final existential and finite SH.

**Why this matters.**  This line is not just a local proof interruption.  It either blocks a named Munkres theorem, blocks a later theorem that depends on the named theorem, or hides a theorem-interface mismatch that will reappear downstream.  In an Isabelle development with `quick_and_dirty` disabled, every theorem depending on this command must be considered uncertified.

**Root cause.**  Derive finite SH from finite-sheet finite-rose cover before final blast/simp.  The surrounding proof comments are useful, but they are not sufficient as a certification artifact.  The code should be reorganized so that the mathematical invariant being used at this line is already available as a named lemma with explicit assumptions.

**Concrete repair path.**

1. Extract the mathematical subclaim into its own lemma with all carriers and index sets explicit.
2. Prove the subclaim in the smallest possible theory before the large Munkres theorem.
3. Replace the local `sorry` by a one-line call to that lemma, so future audits can check the theorem dependency graph.
4. Add the lemma to the statement index only after it builds without `sorry` and without `quick_and_dirty`.

**Audit acceptance test.**  The line should disappear from the executable-sorry scan, the new lemma should have a theorem name, and the resulting theorem should remain stable if generated reports are deleted and regenerated from the certified build.

For Section 85, the proof should be rebuilt around a fixed rose/wedge model and a canonical covering carrier.  Once the covering graph is concrete, the Euler calculation becomes a short final step.  Until then, it is not a simple arithmetic proof.

Recommended finite-rank spine:

```isabelle
lemma rose_covering_rank_count:
  assumes rose: "top1_is_rose_graph_on X TX x0 S" and finiteS: "finite S"
      and cover: "top1_finite_sheeted_graph_covering_on E TE X TX p k"
      and conn: "top1_connected_on E TE"
  obtains SH gen where
      "top1_is_free_group_full_on (pi1 E TE e0) (pi1_mul E TE e0) ... gen SH"
      "finite SH"
      "card SH = k * card S - k + 1"

corollary Theorem_85_3_Schreier_index_fixed:
  assumes "top1_is_free_group_full_on F mul e inv gen S"
      and "finite S" "card S = n + 1"
      and "top1_subgroup_on H F mul e inv" "top1_group_index F mul H = k"
  obtains genH SH where
      "top1_is_free_group_full_on H mul e inv genH SH"
      "finite SH" "card SH = k * n + 1"
```

The crucial prerequisite is a graph-covering counting theorem: vertices in the covering are counted sheetwise over base vertices, and edges in the covering are counted sheetwise over base edges.  With a base rose having one vertex and `n+1` edges, the covering has `k` vertices and `k*(n+1)` edges, so the connected graph rank is `k*(n+1) - k + 1 = k*n + 1`.


# Architecture findings and fixes

## The final session is still a draft session

The active `ROOT` shows that the final target `AlgTop` is built on `AlgTopCached9` with `options [quick_and_dirty, timeout = 600]`.  This should be changed by adding a certified target, not by removing the draft target immediately.  The practical split should be:

```isabelle
session AlgTopDraft = AlgTopCached9 +
  options [quick_and_dirty, timeout = 600]
  theories AlgTop

session AlgTopCertified = AlgTopCached9 +
  options [timeout = 1800]
  theories AlgTop
```

The draft target may remain useful for interactive development.  The certified target should be what CI runs and what reports are generated from.  No theorem report should be accepted unless it records the exact session name, the exact commit SHA, and whether `quick_and_dirty` was false.

## The graph predicate hides the arc family

The current graph convenience predicate is existential in spirit:

```isabelle
definition top1_is_graph_on :: "'a set => 'a topology => bool" where
  "top1_is_graph_on X TX <->
     is_topology_on_strict X TX &
     is_hausdorff_on X TX &
     (exists A. ... arc family A ... union A = X ... coherent topology ...)"
```

That is convenient for saying that a space is some graph, but it is bad for the main theorems.  Munkres graph theorems depend on the specific arc family and on the selected maximal tree.  Hiding the family forces later proofs either to recover arbitrary witnesses or to reindex into artificial types.  This is the root cause behind the graph-pi1 reindex blocker.

Recommended API:

```isabelle
definition top1_is_graph_with_arcs_on :
  "'x set => 'x topology => 'arc set => ('arc => 'x set) => bool" where
  "top1_is_graph_with_arcs_on X TX I A <->
      is_topology_on_strict X TX &
      is_hausdorff_on X TX &
      (forall i in I. A i subseteq X &
          top1_is_arc_on (A i) (subspace_topology X TX (A i))) &
      X = (Union i in I. A i) &
      top1_graph_arc_intersection_axioms X TX I A &
      top1_graph_coherent_topology X TX I A"

definition top1_is_graph_on where
  "top1_is_graph_on X TX <-> (exists I A. top1_is_graph_with_arcs_on X TX I A)"
```

Serious theorems should use the explicit predicate or a locale:

```isabelle
locale top1_graph =
  fixes X :: "'x set" and TX :: "'x topology"
    and I :: "'i set" and A :: "'i => 'x set"
  assumes graph: "top1_is_graph_with_arcs_on X TX I A"
```

Then the spanning tree theorem should return a subset of `I`, and the fundamental-group theorem should return a free basis indexed by `{i in I. i notin T}`.  This preserves the book's basis set and eliminates the false-countability/nat-indexing failure mode.

## The covering-existence theorem must expose its carrier

The current Theorem 82.1 is mathematically close but formally over-polymorphic.  The construction follows the Munkres coset-of-paths construction: points of the covering space are equivalence classes of paths starting at `b0`, with equivalence determined by endpoint agreement and subgroup membership of the loop product.  This is the correct construction.  The defect is that the final theorem wants an arbitrary result type rather than the constructed type.

The fix is to expose a canonical carrier.  In Isabelle/HOL, this is not optional.  One can still later derive an isomorphic abstract covering-space theorem, but only after the concrete theorem exists.

Minimal replacement statement:

```isabelle
type_synonym 'b top1_path = "real => 'b"
type_synonym 'b top1_path_class = "('b top1_path) set"

abbreviation top1_covering_coset_space ::
  "'b set => 'b topology => 'b => (('b top1_path) set) set => 'b top1_path_class set" where
  "top1_covering_coset_space B TB b0 H ==
     (top1_path_coset_class B TB b0 H) ` top1_basepoint_paths B TB b0"

theorem Theorem_82_1_covering_existence_canonical:
  fixes B :: "'b set" and TB :: "'b topology" and b0 :: 'b
  assumes "is_topology_on_strict B TB"
      and "top1_path_connected_on B TB"
      and "top1_locally_path_connected_on B TB"
      and "top1_semilocally_simply_connected_on B TB"
      and "b0 in B"
      and "H subseteq top1_fundamental_group_carrier B TB b0"
      and "group_on H (top1_fundamental_group_mul B TB b0) ..."
  shows "let E = top1_covering_coset_space B TB b0 H in
    exists TE p e0.
      is_topology_on_strict E TE &
      top1_covering_map_on E TE B TB (p :: 'b top1_path_class => 'b) &
      top1_path_connected_on E TE &
      top1_locally_path_connected_on E TE &
      e0 in E & p e0 = b0 &
      top1_fundamental_group_image_hom E TE e0 B TB b0 p = H"
```

The old theorem should be demoted to a corollary only if its result type is explicitly fixed by an isomorphism or by a type definition.  A statement of the form `exists E :: 'e set` for an unconstrained `'e` cannot be obtained from a construction whose elements are path classes of type `('b path) set`.

## The graph fundamental group theorem should be indexed by cotree arcs

The current live code has removed the old executable assertion that every set can be bijected with a `nat set`, but the reindexing smell remains.  The book theorem is not a theorem about `nat`; it is a theorem about the free group on the set of non-tree edges.  A finite helper may use `nat` internally if desired, but the public theorem should expose the cotree index set.

Recommended public theorem:

```isabelle
theorem graph_pi1_free_indexed:
  assumes "top1_is_graph_with_arcs_on X TX I A"
      and "top1_connected_on X TX"
      and "x0 in X"
  obtains T gen where
      "top1_is_spanning_tree_for_arcs X TX I A T"
      "top1_is_free_group_full_on
          (top1_fundamental_group_carrier X TX x0)
          (top1_fundamental_group_mul X TX x0)
          (top1_fundamental_group_id X TX x0)
          (top1_fundamental_group_invg X TX x0)
          gen {i in I. i notin T}"
```

Then finite/countable/nat-indexed statements are corollaries:

```isabelle
theorem finite_graph_pi1_free_nat:
  assumes "top1_is_graph_with_arcs_on X TX I A" "finite I" "top1_connected_on X TX" "x0 in X"
  shows "exists iota :: nat => _. exists S :: nat set. top1_is_free_group_full_on ... iota S"

theorem countable_graph_pi1_free_nat:
  assumes "top1_is_graph_with_arcs_on X TX I A" "countable I" "top1_connected_on X TX" "x0 in X"
  shows "exists iota :: nat => _. exists S :: nat set. top1_is_free_group_full_on ... iota S"
```

The countable corollary must explicitly assume countability.  It should not appear in the unrestricted graph theorem.

## The free-group predicate needs a universal-property companion

`top1_is_free_group_full_on` appears to encode freeness by group axioms, generator injection, generation, and absence of non-empty reduced words evaluating to identity.  This is often enough for book-style arguments, but it is fragile for transfer, quotient, and rank uniqueness.  The project should add and use a universal-property theorem:

```isabelle
theorem top1_free_group_full_on_universal_property:
  assumes "top1_is_free_group_full_on G mul e inv i S"
  shows "for every group K and every function f from S to carrier K,
         there exists a unique group hom F from G to K extending f along i"
```

Once this is available, many isomorphism-transfer steps become standard.  It also makes rank-invariance lemmas cleaner, because isomorphism of free groups can be characterized through the universal property rather than by low-level reduced-word manipulations.

## Surface-classification statements are still placeholders

The surface section currently tries to use names such as `top1_is_torus_scheme`, `top1_is_projective_scheme`, and `top1_elementary_scheme_equiv` in the classification proof.  In the active source, those names do not appear as real prior definitions.  That is a serious audit issue because a theorem statement inside a `sorry` block can refer to undefined intended concepts without forcing the project to settle their exact meaning.

The right split is:

1. A signed-edge word datatype.
2. A quotient-space construction from a polygon plus a signed-edge word.
3. Primitive elementary moves.
4. Reflexive-transitive closure of primitive moves.
5. A theorem that each primitive move preserves quotient homeomorphism.
6. A combinatorial normal-form theorem.
7. Identification of normal forms with sphere, torus sums, and projective-plane sums.

Only after this split should Theorem 77.5 be stated as a final classification theorem.

## Cache files and duplicate risk

The cache chain is now visibly complete through `ac9`, including `ac2` and `ac3`.  That fixes the earlier reproducibility fault.  The remaining risk is maintainability.  `ac/AlgTopCached.thy` is nearly 59,000 lines, while the final active `AlgTop.thy` is over 16,000 lines.  A reviewer cannot reliably tell which names are canonical, which are weaker historical variants, and which are abandoned experiments without automated duplicate and dependency reports.

The two `oops` blocks in `ac/AlgTopCached.thy` should be handled before certification.  The options are simple:

- finish the theorem and give it a name;
- move the exploratory attempt into a `Scratch` session not imported by any certified target;
- delete it if it is obsolete.

Leaving `oops` in an imported session is not unsound, because `oops` does not introduce a theorem, but it is audit-hostile.  It looks like an abandoned claim in the trusted tree.


# Blocker unblocking plan

## Priority 0: create a certified build target

Before editing individual proof holes, create a CI target that runs without `quick_and_dirty`.  A project can keep the draft target, but every status count must be against the certified target.  The current counts are useful only as draft progress metrics.

Acceptance criteria:

- `AlgTopDraft` may use `quick_and_dirty`.
- `AlgTopCertified` must not use `quick_and_dirty`.
- Generated statement reports must include the session name and head SHA.
- CI fails on executable `sorry`, `oops`, and `quick_and_dirty` in certified sessions.

CI skeleton:

```bash
#!/usr/bin/env bash
set -euo pipefail
isabelle build -d tst AlgTopCertified
python3 tools/check_isabelle_holes.py tst --forbid-sorry --forbid-oops --forbid-quick-and-dirty
python3 tools/check_duplicate_theorems.py tst/ac tst/ac2 tst/ac3 tst/ac4 tst/ac5 tst/ac6 tst/ac7 tst/ac8 tst/ac9 tst/AlgTop.thy
python3 tools/check_placeholder_names.py tst/AlgTop.thy top1_is_torus_scheme top1_is_projective_scheme top1_elementary_scheme_equiv
```

## Priority 1: repair Theorem 82.1

This is the single highest leverage change.  The line-6327 blocker is not solved by more `blast`, `metis`, or `simp`.  The proof has the wrong target.  Make the coset/path-class space the public result.  After that, the proof can end by showing the constructed `?E`, `?TE`, `?p`, and `?e0` satisfy the theorem.

A good engineering target is:

```isabelle
theorem covering_existence_coset_model:
  ...
  shows "top1_is_covering_model_for_subgroup B TB b0 H
           (top1_covering_coset_space B TB b0 H)
           (top1_covering_coset_topology B TB b0 H)
           (top1_covering_coset_projection B TB b0 H)
           (top1_covering_coset_basepoint B TB b0 H)"
```

Then define `top1_is_covering_model_for_subgroup` as the conjunction that is currently in Theorem 82.1.  This shortens the final theorem and makes the result reusable by Sections 83 and 85.

## Priority 2: introduce explicit graph-with-arcs locale

The project needs a canonical graph locale.  Once it exists, rewrite graph local path connectedness, graph semilocal simple connectivity, graph-covering-is-graph, graph-pi1-free, and finite covering count lemmas in that locale.  Keep `top1_is_graph_on` only as a convenience wrapper.

The key theorem should be the indexed theorem over cotree arcs.  This removes the need for the line-9610 reindex proof and prevents a recurrence of the false countability bug.

## Priority 3: close the easy graph-LPC extraction

Line 8337 should be a fast fix.  Search the proof body of `graph_locally_path_connected` from the `a5188a5`/`1e38152` era for the local proof of `top1_locally_path_connected_on I_set I_top`; move it into a standalone lemma:

```isabelle
lemma I_set_locally_path_connected:
  "top1_locally_path_connected_on I_set I_top"
```

Then line 8337 becomes:

```isabelle
have "top1_locally_path_connected_on I_set I_top"
  by (rule I_set_locally_path_connected)
```

This is a pure refactor; no new topology should be invented.

## Priority 4: finish graph semilocal simple connectivity

The interior case should use a chart interval.  The current proof starts from local path connectedness of the whole arc and obtains an arbitrary `V0`.  That is weaker than what the proof needs.  An arbitrary open subset of an arc around an interior point can still contain endpoints if it is large; then it can meet other arcs.  Choose a small interval in the parameter coordinate instead.

The vertex case should use a star.  The proof comments mention sub-arcs and deformation retracts.  That is correct, but the exact proof depends on whether the graph definition has finite valence.  If valence is not finite, the star must include all incident arcs and the contraction must be defined by arc coordinates on each incident subarc.  This is still the book proof for a graph as a one-dimensional CW-like object, but it needs a coherent topology lemma for the union of the star subarcs.

## Priority 5: rebuild Section 85 on the canonical covering model

Do not try to solve the Euler line first.  The current line 16285 has too little data in context.  The right order is:

1. Prove arbitrary-basis free group realization by wedge/rose, preferably using cached Theorem 71.3.
2. Transport the subgroup through the isomorphism to the rose pi1.
3. Apply canonical Theorem 82.1.
4. Prove the covering of a graph is a graph with lifted arc family.
5. Prove finite-sheeted covering graph counts.
6. Apply graph-pi1-free indexed by cotree arcs.
7. Derive Euler/rank arithmetic.

After steps 1-6, line 16285 is a short arithmetic proof:

```isabelle
have "card SH = card E_edges - card E_vertices + 1" by (rule finite_connected_graph_rank)
also have "... = k * (n + 1) - k + 1" using covering_edge_count covering_vertex_count by simp
also have "... = k * n + 1" by (simp add: algebra_simps)
finally show "card SH = k * n + 1" .
```

## Priority 6: isolate surface classification as its own milestone

The surface classification block is too large to finish by local proof automation.  Treat it as an independent milestone with explicit definitions and intermediate theorems.  Do not let it block graph/covering/Schreier work.  Conversely, do not mark the classification theorem as meaningful until the placeholder scheme names are defined and the normal-form theorem is certified.

## Priority 7: deck transformations

The Section 81 deck theorem depends on path lifting and normalizer algebra.  It should be split before attempting a final proof.  The theorem is important, but it does not block graph-pi1 or Section 85 as directly as Theorem 82.1 does.  It should be worked after the covering construction API is stabilized.


# Book-alignment audit

## Munkres Section 71: wedge of circles

The `ac9/AlgTopCached9.thy` cache is a strong positive point.  It contains the improved Theorem 71.3 direction: the fundamental group of a wedge of circles is free on the wedge index set, not on an artificial integer wrapper.  This is exactly the direction required to make later graph and Nielsen-Schreier statements faithful for arbitrary basis sets.  The audit recommendation is to promote this style throughout the graph and Section 85 code.

Risk: later code still often falls back to finite/nat-indexed helpers.  That risks weakening a book theorem or making an unrestricted theorem false.  The public theorem should preserve the basis type; the nat version should be a corollary under finite or countability assumptions.

## Munkres Sections 74-78: compact surfaces

The current source sketches the right narrative: projective schemes, elementary scheme operations, triangulable surfaces, polygonal quotients, and classification.  The problem is that the formal objects are not yet explicit enough.  A textbook paragraph can say "edge scheme" and rely on pictures; Isabelle needs a datatype, equivalence relation, quotient construction, and normal forms.

Book-faithful repair means proving normal-form combinatorics separately from topological quotient invariance.  The normal-form theorem should not mention topological spaces.  The quotient-preservation theorem should not perform the normal-form algorithm.  The final classification theorem should combine them.

## Munkres Section 81: covering transformations

The book proof identifies deck transformations with the normalizer quotient by examining how deck transformations move a chosen lift of the basepoint.  In Isabelle, this proof should not be a single theorem.  Define the fiber action, prove the image is exactly the normalizer quotient, then prove the group operation correspondence.

The quotient group `N(H)/H` needs a concrete carrier.  Avoid vague predicates such as "normalizer quotient exists" unless they reduce to an explicit set of cosets and a multiplication with a proved well-definedness lemma.

## Munkres Section 82: existence of covering spaces

The book constructs a covering space from path classes.  The formalization appears to follow this construction.  The missing Isabelle step is not mathematical existence but type representation.  The book can say "let E be the set of equivalence classes"; Isabelle needs the type of elements of `E` to be visible.  Use a set of sets of paths.

## Munkres Section 84: fundamental group of a graph

The book theorem is indexed by edges not in a maximal tree.  Formal theorem statements should reflect that.  A graph with uncountably many edges can have an uncountably generated free fundamental group.  Therefore an unrestricted theorem with a `nat`-indexed basis would be false.  The current executable code no longer contains the old false countability assertion, but the theorem should still be strengthened to preserve cotree indices.

## Munkres Section 85: Nielsen-Schreier and Schreier formula

Nielsen-Schreier is a theorem about every subgroup of a free group.  A finite wedge realization is insufficient unless the theorem assumes a finite basis.  If the theorem is intended in full generality, use the arbitrary-index wedge theorem and covering existence.  If the theorem is intended only for finite-rank free groups, say so explicitly and rename it accordingly.

The Schreier formula is finite-index and finite-rank.  Here the graph model can be a finite rose, and the Euler calculation is book-faithful.  The formula should be proved through a finite-sheeted graph-covering count, not by manipulating `card SH` without knowing what `SH` is.


# Detailed dependency blueprint

This section gives a proposed dependency order that avoids circularity and avoids proving large theorems before their carriers and index sets are stable.

## Layer 1: algebra and free groups

1. Finalize `top1_is_free_group_full_on` as the operational predicate.
2. Prove closure under isomorphism with the same index type.
3. Prove closure under reindexing by explicit bijection.
4. Prove a universal-property companion theorem.
5. Prove rank invariance for finite bases only under an explicit finite-basis hypothesis.

Do not use rank invariance for infinite bases.  Do not turn arbitrary bases into `nat` unless a countability assumption is present.  Keep all generators indexed by the original set whenever possible.

## Layer 2: graph structure

1. Define `top1_is_graph_with_arcs_on` and make `top1_is_graph_on` a wrapper.
2. Define graph vertices and arc endpoints relative to the explicit family.
3. Define graph trees and spanning trees as subsets of the arc index set.
4. Prove existence of maximal/spanning tree for connected graphs under the exact assumptions used by Munkres.
5. Prove local path connectedness and semilocal simple connectivity in the graph locale.
6. Prove graph-covering-is-graph with lifted arc family.
7. Prove graph-pi1-free indexed by cotree arcs.

This order prevents the graph-pi1 theorem from needing to recover hidden witnesses or invent basis index types.

## Layer 3: covering spaces

1. Define the path equivalence relation for a subgroup `H` of `pi1(B,b0)`.
2. Define the canonical carrier as the image of the path-class map.
3. Define the projection using endpoint of any representative; prove well-definedness.
4. Define basis neighborhoods and topology on the carrier.
5. Prove projection is a covering map.
6. Prove connectedness and local path connectedness of the constructed covering.
7. Prove the induced subgroup is exactly `H`.
8. Package as `covering_existence_coset_model`.

Only after this layer is complete should downstream code state `obtain E TE p e0` for a covering.  In Isabelle, that obtain must either use the canonical type or occur inside a locale where the covering carrier type is already fixed.

## Layer 4: Sections 81 and 85

Section 81 uses covering transformations and normalizers.  Section 85 uses covering existence and graph coverings.  Both should depend on Layer 3, but they should not define their own ad hoc covering carriers.

For Nielsen-Schreier:

1. Start from a free group on basis `S`.
2. Realize it as the fundamental group of a wedge/rose with circles indexed by `S`.
3. Transport subgroup `H` through the isomorphism.
4. Apply canonical covering existence.
5. Prove covering of a graph is a graph.
6. Apply graph-pi1-free.
7. Transfer freeness back to `H`.

For Schreier finite index formula:

1. Add finite `S` and `card S = n+1` assumptions.
2. Use a finite rose graph.
3. Use a k-sheeted covering from the finite index subgroup.
4. Count lifted vertices and edges.
5. Use rank/Euler theorem for finite connected graphs.
6. Transfer rank across the subgroup isomorphism.

## Layer 5: surfaces

The surface work can proceed independently of graph/covering work.  It should not depend on Section 85.  It should be separated so that progress on graph and covering theorems does not get blocked by surface-classification skeletons.

Surface dependency order:

1. Signed-edge words and inverse operation.
2. Polygon quotient from a scheme word.
3. Primitive scheme moves and their quotient homeomorphism lemmas.
4. Scheme equivalence as reflexive-transitive closure.
5. Vertex-reduction theorem.
6. Normal-form theorem: sphere, torus product, projective product.
7. Standard-surface recognition theorem.
8. Classification theorem.
9. Homology/fundamental-group consequences.

## Layer 6: reports and CI

Generated reports must never be manually trusted.  They should be machine products of the certified build.  The report generator should fail if it sees draft-only sessions, `quick_and_dirty`, executable `sorry`, executable `oops`, or placeholder theorem names in active final statements.


# Risk matrix

- **Theorem 82.1 remains impossible under the current polymorphic statement.** Probability: high. Impact: critical. Current evidence: line 6327 reaches a concrete construction and then comments that packaging is a type blocker. Mitigation: restate with a canonical coset/path-class carrier.
- **The graph-pi1 theorem loses the correct basis index set.** Probability: high. Impact: critical. Current evidence: line 9610 tries to reindex from a nat helper. Mitigation: introduce an explicit graph-with-arcs locale and prove the cotree-index theorem.
- **The Section 85 Euler line is attacked before prerequisites.** Probability: high. Impact: high. Current evidence: line 16285 has no finite covering count facts in context. Mitigation: prove finite graph covering counts first.
- **Surface classification uses undefined scheme predicates.** Probability: high. Impact: high. Current evidence: scheme names occur only inside the current skeleton block. Mitigation: add a signed-edge scheme datatype and primitive move API.
- **A draft session is mistaken for a certified theorem base.** Probability: high. Impact: critical. Current evidence: the final ROOT session uses quick_and_dirty. Mitigation: add AlgTopCertified and enforce CI.
- **Cache duplicates hide weaker or stale theorem variants.** Probability: medium. Impact: high. Current evidence: the old ac cache is huge and many backups/reports remain under tst. Mitigation: run duplicate theorem checking and move scratch code out of imported sessions.
- **The graph-SSC vertex proof accidentally assumes finite valence.** Probability: medium. Impact: high. Current evidence: comments mention star subarcs but not the exact incidence assumption. Mitigation: prove arbitrary incident-star contraction or add a finite-valence assumption explicitly.
- **Generated reports drift from source.** Probability: high. Impact: medium. Current evidence: the pasted blocker count differs from the current source scan. Mitigation: regenerate reports only from a certified build and include the SHA.


# Concrete recommendations

1. **Stop adding downstream proofs on top of the old Theorem 82.1 statement.**  Every hour spent trying to package the canonical covering into an arbitrary type is wasted.  Change the theorem statement first.

2. **Close line 8337 immediately by extraction.**  This is a low-risk proof refactor.  It will simplify graph-SSC and remove one new `sorry` introduced by the latest commit.

3. **Rewrite graph-SSC around two lemmas.**  The interior lemma should use a chart interval; the vertex lemma should use a star.  The current local proof is close but has the wrong intermediate object for the interior case.

4. **Replace `top1_is_graph_on` in serious graph theorems.**  Keep it as a convenience predicate, but main theorems need explicit arcs.  This one change will improve graph-pi1, graph coverings, and Schreier formula.

5. **Strengthen the finite graph-pi1 helper.**  It must state that its basis corresponds to non-tree arcs, or at least return a cardinal equality sufficient for a bijection.  The best fix is cotree-indexed output.

6. **Do not solve the Schreier Euler line in isolation.**  First prove finite covering graph counts.  Then the arithmetic is one line.

7. **Split Section 85 into finite-rank and arbitrary-rank results if necessary.**  Full Nielsen-Schreier requires arbitrary basis realization.  Schreier formula is finite-rank/finite-index.  Keep those assumptions separate.

8. **Move or remove `oops` blocks from imported cache.**  They are not unsound, but they are unacceptable in a certified audit target.

9. **Create a theorem-status script that preserves line numbers.**  It should strip comments while preserving newlines, exactly as this audit did, to avoid mismatches between prose `sorry` words and executable proof holes.

10. **Pin reports to commit SHA.**  The report generator should print the SHA, session target, Isabelle version, `quick_and_dirty` status, and exact executable-sorry count.


# Appendix A: exact executable-sorry list

```
AlgTop.thy:231: m_projective_scheme_CW_data -- 1-skeleton of projective scheme quotient is wedge of m circles
AlgTop.thy:304: Theorem_76_elementary_operations -- elementary scheme operation preserves quotient homeomorphism
AlgTop.thy:346: Theorem_75_4_H1_m_projective -- abelianization / Smith normal form for projective surface
AlgTop.thy:408: Theorem_78_1_triangulable_surface -- triangulable compact surface is quotient of disjoint simplex copies
AlgTop.thy:444: Theorem_78_2_connected_polygonal_quotient -- merge finite triangulation into a single polygon
AlgTop.thy:484: Theorem_77_5_classification -- extract edge scheme from polygon quotient
AlgTop.thy:500: Theorem_77_5_classification -- normal-form reduction by elementary operations
AlgTop.thy:502: Theorem_77_5_classification -- normal form implies standard surface homeomorphism type
AlgTop.thy:1060: Theorem_81_2_covering_group_iso -- deck transformation group is N(H)/H
AlgTop.thy:6327: Theorem_82_1_covering_existence -- pack canonical coset path-space construction into polymorphic existential
AlgTop.thy:8337: arc_locally_path_connected -- [0,1] locally path-connected extraction
AlgTop.thy:8496: graph_semilocally_simply_connected -- interior point of an arc has a simply connected neighborhood
AlgTop.thy:8505: graph_semilocally_simply_connected -- vertex star neighborhood is simply connected
AlgTop.thy:8621: schreier_rank_formula -- obtain covering corresponding to subgroup H
AlgTop.thy:8632: schreier_rank_formula -- E is graph and Euler/rank count
AlgTop.thy:9610: graph_pi1_free_weak -- finite non-tree arcs reindexed from nat to hidden set type
AlgTop.thy:15828: Theorem_85_1_Nielsen_Schreier -- realize arbitrary free group as graph fundamental group
AlgTop.thy:15844: Theorem_85_1_Nielsen_Schreier -- covering existence for subgroup image
AlgTop.thy:16064: Theorem_85_1_Nielsen_Schreier -- internal covering type escapes into polymorphic existential
AlgTop.thy:16125: Theorem_85_3_Schreier_index -- covering existence plus graph covering plus H correspondence
AlgTop.thy:16278: Theorem_85_3_Schreier_index -- free-group transfer existential packaging
AlgTop.thy:16283: Theorem_85_3_Schreier_index -- extract basis from existential hH_free
AlgTop.thy:16285: Theorem_85_3_Schreier_index -- Euler characteristic cardinal arithmetic card SH = k*n + 1
AlgTop.thy:16291: Theorem_85_3_Schreier_index -- show final existential and finite SH
```

# Appendix B: exact executable-oops list

```
tst/ac/AlgTopCached.thy:14170
tst/ac/AlgTopCached.thy:27165
```

These `oops` commands do not add axioms, but they do represent abandoned proof attempts in an imported session.  Move them to a non-imported scratch theory or finish/delete them.

# Appendix C: proposed theorem/API snippets

## Canonical covering carrier

```isabelle
type_synonym 'b top1_path = "real => 'b"
type_synonym 'b top1_path_class = "('b top1_path) set"

abbreviation top1_covering_coset_space ::
  "'b set => 'b topology => 'b => (('b top1_path) set) set => 'b top1_path_class set" where
  "top1_covering_coset_space B TB b0 H ==
     (top1_path_coset_class B TB b0 H) ` top1_basepoint_paths B TB b0"

theorem Theorem_82_1_covering_existence_canonical:
  fixes B :: "'b set" and TB :: "'b topology" and b0 :: 'b
  assumes "is_topology_on_strict B TB"
      and "top1_path_connected_on B TB"
      and "top1_locally_path_connected_on B TB"
      and "top1_semilocally_simply_connected_on B TB"
      and "b0 in B"
      and "H subseteq top1_fundamental_group_carrier B TB b0"
      and "group_on H (top1_fundamental_group_mul B TB b0) ..."
  shows "let E = top1_covering_coset_space B TB b0 H in
    exists TE p e0.
      is_topology_on_strict E TE &
      top1_covering_map_on E TE B TB (p :: 'b top1_path_class => 'b) &
      top1_path_connected_on E TE &
      top1_locally_path_connected_on E TE &
      e0 in E & p e0 = b0 &
      top1_fundamental_group_image_hom E TE e0 B TB b0 p = H"
```

## Explicit graph-with-arcs API

```isabelle
definition top1_is_graph_with_arcs_on :
  "'x set => 'x topology => 'arc set => ('arc => 'x set) => bool" where
  "top1_is_graph_with_arcs_on X TX I A <->
      is_topology_on_strict X TX &
      is_hausdorff_on X TX &
      (forall i in I. A i subseteq X &
          top1_is_arc_on (A i) (subspace_topology X TX (A i))) &
      X = (Union i in I. A i) &
      top1_graph_arc_intersection_axioms X TX I A &
      top1_graph_coherent_topology X TX I A"

definition top1_is_graph_on where
  "top1_is_graph_on X TX <-> (exists I A. top1_is_graph_with_arcs_on X TX I A)"
```

## Graph-pi1 indexed theorem

```isabelle
theorem graph_pi1_free_indexed:
  assumes "top1_is_graph_with_arcs_on X TX I A"
      and "top1_connected_on X TX"
      and "x0 in X"
  obtains T gen where
      "top1_is_spanning_tree_for_arcs X TX I A T"
      "top1_is_free_group_full_on
          (top1_fundamental_group_carrier X TX x0)
          (top1_fundamental_group_mul X TX x0)
          (top1_fundamental_group_id X TX x0)
          (top1_fundamental_group_invg X TX x0)
          gen {i in I. i notin T}"
```

## Reindex lemma

```isabelle
lemma free_group_full_reindex_bij:
  assumes hfree: "top1_is_free_group_full_on G mul e inv i S"
      and hb: "bij_betw b S' S"
  shows "top1_is_free_group_full_on G mul e inv (\<lambda>s'. i (b s')) S'"
proof -
  -- "Unfold top1_is_free_group_full_on_def."
  -- "Use inj_on_comp plus bij_betw_imp_inj_on for generator injectivity."
  -- "Use b ` S' = S for generated subgroup equality."
  -- "Translate every reduced word over S' by map b; non-empty and reducedness are preserved by injectivity."
  -- "Apply hfree to the translated word, then rewrite evaluation by composition."
qed
```

## Interior graph-SSC chart lemma

```isabelle
lemma graph_ssc_interior_chart:
  assumes graph: "top1_is_graph_with_arcs_on X TX I A"
      and i0: "i0 in I"
      and x: "x in A i0"
      and xint: "x notin top1_arc_endpoints_on (A i0) (subspace_topology X TX (A i0))"
  obtains U where
      "x in U" "U in TX" "U subseteq A i0"
      "top1_simply_connected_on U (subspace_topology X TX U)"
proof -
  -- "Choose a homeomorphism h : I_set -> A i0 and t0 with h t0 = x."
  -- "Use xint to get 0 < t0 and t0 < 1. Pick eps with closed ball inside (0,1)."
  -- "Let J = {t in I_set. abs(t - t0) < eps}; let U = h ` J."
  -- "U is open in A i0 and simply connected because J is convex."
  -- "U avoids endpoints, hence avoids every other arc by the graph intersection axiom."
  -- "Coherent topology gives U in TX."
qed
```

## Vertex star contraction lemma

```isabelle
definition graph_vertex_star where
  "graph_vertex_star X TX I A x eps =
     Union ((\<lambda>i. top1_initial_subarc_towards_endpoint X TX (A i) x eps) ` {i in I. x in A i})"

lemma graph_vertex_star_contractible:
  assumes graph: "top1_is_graph_with_arcs_on X TX I A"
      and vertex: "top1_graph_vertex X TX I A x"
      and eps: "0 < eps" "eps < 1/2"
  shows "top1_deformation_retract_of_on
           (graph_vertex_star X TX I A x eps)
           (subspace_topology X TX (graph_vertex_star X TX I A x eps))
           {x}"
```

## Schreier formula spine

```isabelle
lemma rose_covering_rank_count:
  assumes rose: "top1_is_rose_graph_on X TX x0 S" and finiteS: "finite S"
      and cover: "top1_finite_sheeted_graph_covering_on E TE X TX p k"
      and conn: "top1_connected_on E TE"
  obtains SH gen where
      "top1_is_free_group_full_on (pi1 E TE e0) (pi1_mul E TE e0) ... gen SH"
      "finite SH"
      "card SH = k * card S - k + 1"

corollary Theorem_85_3_Schreier_index_fixed:
  assumes "top1_is_free_group_full_on F mul e inv gen S"
      and "finite S" "card S = n + 1"
      and "top1_subgroup_on H F mul e inv" "top1_group_index F mul H = k"
  obtains genH SH where
      "top1_is_free_group_full_on H mul e inv genH SH"
      "finite SH" "card SH = k * n + 1"
```

## Surface scheme API

```isabelle
datatype 'e signed_edge = Pos 'e | Neg 'e

definition inverse_edge where
  "inverse_edge a = (case a of Pos e => Neg e | Neg e => Pos e)"

inductive top1_elementary_scheme_move :: "'e signed_edge list => 'e signed_edge list => bool" where
  rotate: "top1_elementary_scheme_move (u @ v) (v @ u)" |
  inverse: "top1_elementary_scheme_move w (rev (map inverse_edge w))" |
  relabel: "bij f (set (map edge_name w)) (set (map edge_name w')) ==>
            top1_elementary_scheme_move w (map_signed f w)" |
  cancel: "top1_elementary_scheme_move (u @ [a, inverse_edge a] @ v) (u @ v)" |
  cut_paste: "top1_scheme_cut_paste_condition u v w z ==>
              top1_elementary_scheme_move (u @ v @ w @ z) (u @ w @ v @ z)"

definition top1_elementary_scheme_equiv where
  "top1_elementary_scheme_equiv = top1_elementary_scheme_move^^**"
```

# Appendix D: suggested issue tracker labels

Use labels that reflect mathematical dependencies rather than file locations:

- `certification`: quick_and_dirty, sorry/oops, generated-report trust.
- `covering-existence`: Theorem 82.1, canonical coset carrier, path lifting.
- `graph-api`: explicit arcs, spanning tree, cotree indices, graph coverings.
- `graph-ssc`: local path connectedness extraction, interior chart, vertex star.
- `free-groups`: universal property, reindexing, rank invariance.
- `surface-classification`: scheme datatype, elementary moves, normal forms.
- `nielsen-schreier`: arbitrary wedge realization, covering graph, finite-index count.

# Appendix E: final acceptance checklist

A release-quality version of the algebraic-topology formalization should satisfy all of the following:

1. `AlgTopCertified` builds without `quick_and_dirty`.
2. Executable `sorry` count is zero in all certified sessions.
3. Executable `oops` count is zero in all certified sessions.
4. Theorem 82.1 is stated with a visible carrier type.
5. Graph fundamental group theorem preserves the cotree arc index set.
6. Nat-indexed graph corollaries assume finite or countable graph arcs.
7. Surface scheme predicates are real definitions before being used in classification statements.
8. Nielsen-Schreier full theorem uses arbitrary-index free group realization, or is renamed as finite-rank if restricted.
9. Schreier formula proof obtains `finite SH` before using `card SH`.
10. Generated reports record commit SHA, session, and certification mode.

# Closing assessment

The project has made real progress in the last five days, especially in graph local path connectedness and wedge/free-group infrastructure.  The remaining blockers are not random.  They cluster around three architectural mismatches: hidden graph arc families, hidden covering-space carriers, and monolithic surface-classification skeletons.  Fix those interfaces first.  After that, several current `sorry`s should collapse into manageable named lemmas, and the Section 85 Euler arithmetic will become genuinely elementary.
