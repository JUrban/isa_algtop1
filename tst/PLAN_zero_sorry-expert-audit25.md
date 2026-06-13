# Fresh audit of `JUrban/isa_algtop1`

## Executive assessment

The latest pushed state is a meaningful advance, but it also shows why the worker feels stuck. The project has moved from “prove the scheme language and normal forms” to the last hard formal-geometry layer: **canonical scheme quotients, cancellation/spur collapse, cut-paste, polygon-pasting, and final classification assembly**. The current commit history shows the latest head as `fe5917e`, “Document compact_surj_quotient proof strategy,” with the worker explicitly stuck on the standard topology fact that a continuous surjection from compact polygonal region to Hausdorff polygonal region is a quotient map. The latest commit reports **30 sorry words and a 12s build**. ([GitHub][1])

The good news is that the recent work has clearly improved the proof architecture. The current live `AlgTop.thy` imports `AlgTopCached14`, whose opening comments say that valid-operation reverse, valid-equivalence symmetry, and the §77 valid normal-form chain are cached. The live file is now only 440 raw lines, so the active proof is finally concentrated on the last surface-geometry layer rather than dragging the whole book proof around. ([GitHub][2])

The important correction is that the project is **not at “almost just cleanup”**. It is now down to a smaller but more delicate set of theorems. In particular, the final proof still contains executable admits for cut-paste, cancellation/uncancellation, `v_context_left` subcases, compact-surjection quotient-map topology, spur-collapse/fibre matching, the type bridge, Theorem 78.2’s polygon-pasting induction, the scheme-extraction step of Theorem 77.5, and sphere realization. The source also still keeps an old book-form Theorem 76 with a `sorry`, explicitly saying the live proof is via the valid-equivalence route instead. ([GitHub][2])

My current verdict is:

```text
Done or effectively cached:
  §75.4 algebraic computation
  §85 Schreier/Nielsen-Schreier path
  §77 valid normal form and valid-equivalence infrastructure

Still live:
  canonical quotient/topology infrastructure
  front cancel / uncancel by spur collapse
  cut-paste geometry
  context-left/contextual closure issue
  §78.2 polygon-pasting induction
  §77.5 scheme extraction and sphere realization
  final no-quick_and_dirty certification
```

The final `ROOT` still builds the final `AlgTop` session with `options [quick_and_dirty, timeout = 600]`, so the repository is not yet release-certified. ([GitHub][3])

---

## 1. How the old plan has played out

The original zero-sorry plan was correct in its main principles: fix statements before grinding proofs, expose carriers and witnesses, avoid hidden polymorphic existentials, work bottom-up through cache files, and require the final theorem to compile without `quick_and_dirty`. It also explicitly identified the surface phase as a separate stack involving scheme syntax, normal form, quotient preservation, and final classification assembly. ([GitHub][4])

That plan has mostly been executed. Earlier audits complained about graph witnesses, covering multiplicities, Nielsen–Schreier, and Theorem 75.4. Those are no longer the live problem: the current statement index still shows the large graph/free-group machinery in cached theories, while the live file now focuses on scheme quotients, valid operation preservation, Theorem 78.2, and Theorem 77.5. ([GitHub][5])

The stale documentation should not guide the worker anymore. `README_PROOF_STATUS.md` still talks about old `sc_graph_no_cycle` blockers and claims an older surface gap shape, while `SORRY_AUDIT.md` is explicitly a June 6/session-1368 snapshot. Both are now obsolete relative to the current §76/§78/§77.5-focused file. ([GitHub][6])

---

## 2. What has genuinely improved recently

### 2.1 `scheme_quotient_exists` is now a serious construction

Earlier, the canonical scheme quotient attempt was dangerous because the quotient map was effectively a placeholder. The current source is much more serious. It defines a regular `n`-gon, defines canonical and non-canonical edges, uses partner-edge data from the proper scheme condition, and constructs a quotient map `q` that sends vertices to vertex-class representatives and non-canonical edge-interior points to their partner edge with either the same or reversed parameter. The later assembly then proves the topology and quotient-of-scheme conditions from named C-conditions. ([GitHub][2])

This is a major step. If this theorem is genuinely complete, it gives a canonical quotient realization for every proper scheme of length at least three. That can be used to avoid many ad hoc “construct a new polygon” arguments later. The current source’s final assembly of `scheme_quotient_exists` shows the right shape: it supplies `P`, `q`, `vx`, `vy`, proves the quotient map, boundary identification condition, interior-injectivity, non-adjacent edge disjointness, counterclockwise/strict edge conditions, and packages them into `top1_quotient_of_scheme_on`. ([GitHub][2])

There is still a separate `regular_ngon_polygonal_region` helper at the top with a `sorry`, even though its comment says the regular polygon facts are proved inside `scheme_quotient_exists` and should be extractable. That is now technical debt: either extract it from the canonical quotient proof or delete it if unused. ([GitHub][2])

### 2.2 The worker is now using the right front-cancel strategy

The old subpolygon approach to cancellation was removed after the worker realized it was flawed. The current proof route for `front_cancel_proper` is much better: obtain canonical quotients of the extended scheme `[a,a⁻¹] @ w` and of `w`, use uniqueness/homeomorphism to compare arbitrary and canonical quotients, then prove a spur-collapse homeomorphism between the canonical extended quotient and the canonical shorter quotient. Recent commits explicitly show the worker added `front_cancel_proper`, moved it after uniqueness, proved the properness structure, removed an 823-line old subpolygon attempt, and then structured the proof around `quotient_same_fibres_homeomorphic`. ([GitHub][1])

The current source has the right decomposition for this proof: it extracts polygon witnesses and quotient maps from the extended and shorter scheme quotients, plans a map `f : P_ext → P_w`, proves that `q_w ∘ f` is a quotient map using a compact-surjection helper, and then wants fibre equivalence between `q_ext` and `q_w ∘ f`. ([GitHub][2])

### 2.3 The worker has identified the correct current standard-topology lemma

The latest commit isolates `compact_surj_quotient`: a continuous surjection between polygonal regions is a quotient map. The commit message says it should follow by compactness of polygonal regions, Hausdorffness of the target subspace, continuous image of compact sets being compact, compact subsets of Hausdorff spaces being closed, and closed surjection implying quotient map. ([GitHub][7])

That is the right lemma to isolate. The worker should not keep reproving quotient-map topology inside the spur-collapse proof. Prove this once as a general topology lemma and reuse it.

---

## 3. Current blocker map

The current live gaps fall into a smaller number of coherent groups.

First, there are remaining old or broad §76/cut-paste admits: `quotient_scheme_edge_permutation`, `quotient_of_scheme_cut_paste`, `quotient_of_scheme_cut_paste2`, and `quotient_of_scheme_cut_paste_opp` still contain `sorry`s. Some of these still attempt same-space preservation even though the final target should be homeomorphic realization. ([GitHub][2])

Second, the front-cancel/uncancel chain still has core admits: a general `front_cancel_realization_homeo`, `front_uncancel_realization_homeo`, `quotient_of_scheme_uncancel_front`, the short-cancel case, reverse cut-paste cases, and many `v_context_left` subcases. The current source explicitly notes that some of these cases are false or not generally expressible without extra properness/length/context assumptions. ([GitHub][2])

Third, `front_cancel_proper` is now structured but still blocked by three serious proof obligations: the compact-surjection quotient-map lemma, construction/fibre matching of the spur-collapse map, and the type bridge that transfers a real-typed canonical quotient back to the polymorphic `'a` carrier of the original quotient. ([GitHub][2])

Fourth, Theorem 78.2 still has the same book-level induction gap: in the `card 𝒯 > 1` case, it must find adjacent regions/triangles, paste them, reduce the number of regions, and repeat. The base case is developed, but the induction step is still admitted. ([GitHub][2])

Fifth, Theorem 77.5 still has the scheme-extraction and sphere-realization admits. It obtains a single polygon quotient from Theorem 78.2, then admits the construction of a proper edge scheme, and in the sphere normal-form case it still admits that the sphere scheme quotient is homeomorphic to `S²`. ([GitHub][2])

Finally, the projective `m = 1` branch is still conceptually wrong: the current proof derives a contradiction from the fact that the two-letter projective scheme cannot be a strict polygonal quotient. That may close the branch syntactically, but it is not a faithful classification proof of the projective plane case. The final realization layer needs to handle `m = 1` via a projective-plane/dunce-cap model or avoid reducing to an unrealizable two-edge quotient. ([GitHub][2])

---

## 4. Immediate advice on the current stuck point: `compact_surj_quotient`

The worker is stuck at the right local lemma. I would split it into two lemmas instead of trying to prove the full statement directly.

First prove a general closed-surjection quotient lemma:

```isabelle
lemma closed_surjective_imp_quotient_map:
  assumes Xtop: "is_topology_on X TX"
      and Ytop: "is_topology_on Y TY"
      and cont: "top1_continuous_map_on X TX Y TY f"
      and surj: "f ` X = Y"
      and closedmap:
        "⋀C. closedin_on X TX C ⟹ closedin_on Y TY (f ` C)"
  shows "top1_quotient_map_on X TX Y TY f"
```

The proof is direct. For the quotient-topology reverse direction, assume `V ⊆ Y` and `f -` V`is open in`X`. Then `X - f -` V` is closed; its image is closed by `closedmap`; by surjectivity, that image is exactly `Y - V`; hence `V` is open. This avoids compactness entirely in the quotient-map proof.

Then prove the compact-Hausdorff closed-map lemma specialized to polygonal regions:

```isabelle
lemma compact_polygon_continuous_image_closed:
  assumes "top1_is_polygonal_region_on P1 n1"
      and "top1_is_polygonal_region_on P2 n2"
      and "top1_continuous_map_on P1 TP1 P2 TP2 f"
      and "closedin_on P1 TP1 C"
  shows "closedin_on P2 TP2 (f ` C)"
```

Use `polygonal_region_compact`, compactness of closed subsets of compact spaces, continuity, and Hausdorffness of the `ℝ²` subspace. The commit message says the available infrastructure includes `polygonal_region_compact` and `compact_hausdorff_continuous_closed_map`; use that if it matches the local topology predicates. ([GitHub][7])

Then `compact_surj_quotient` is a wrapper:

```isabelle
compact_surj_quotient:
  polygonal P1 n1 ⟹ polygonal P2 n2 ⟹
  continuous_on P1 f ⟹ f ` P1 = P2 ⟹
  top1_quotient_map_on P1 TP1 P2 TP2 f
```

Do not keep this proof embedded in `front_cancel_proper`. The source currently introduces it as a local helper inside the spur-collapse proof; it should become a named global lemma. ([GitHub][7])

---

## 5. Advice on spur collapse

The current source correctly reduces the hard part of front cancellation to constructing a map

```text
f : P_ext → P_w
```

such that `f` is continuous, surjective, and

```text
q_ext x = q_ext y  ⇔  q_w (f x) = q_w (f y).
```

Then `q_w ∘ f` is a quotient map and `quotient_same_fibres_homeomorphic` can give the homeomorphism between the two quotient spaces. ([GitHub][2])

The worker should not try to define `f` directly on arbitrary polygons. Define it in disk coordinates.

The proof should be packaged as:

```isabelle
lemma spur_collapse_on_disk:
  assumes "n = length ([a,a⁻¹] @ w)"
      and "m = length w"
      and "m ≥ 3"
  obtains c where
    "continuous_on top1_closed_disk c"
    "c ` top1_closed_disk = top1_closed_disk"
    "c collapses the first two boundary arcs"
    "c maps boundary arc (i+2) of the n-gon model to boundary arc i of the m-gon model"
    "c preserves exactly the scheme fibres after cancel"
```

Then use the existing polygon-to-disk homeomorphisms to transport `c` to arbitrary polygon witnesses:

```text
P_ext --ψ_ext--> disk --c--> disk --ψ_w⁻¹--> P_w
```

The current comments already describe exactly this construction. The important thing is to prove the disk boundary-arc fibre statement once, not to expand it inside `front_cancel_proper`. ([GitHub][2])

The map is not a homeomorphism on polygon domains; it is a continuous surjection/quotient map. That is why `compact_surj_quotient` is the right preliminary lemma. The quotient spaces are homeomorphic because the fibres match, not because the polygon domains are homeomorphic. ([GitHub][2])

---

## 6. Advice on the type bridge

The current source has a `sorry` for the type bridge after constructing the canonical real-typed quotient of `w`. The comment says: build an `'a`-typed quotient of `w` by composing `q_w` with the inverse of the homeomorphism from the old quotient space to the canonical quotient. ([GitHub][2])

This should be a reusable theorem:

```isabelle
lemma quotient_of_scheme_transport_homeomorphism:
  assumes qZ: "top1_quotient_of_scheme_on Z TZ w"
      and h:  "top1_homeomorphism_on Y TY Z TZ h"
  shows "top1_quotient_of_scheme_on Y TY w"
```

Proof idea: if `qZ : P → Z` is the quotient map witnessing `w`, define

```isabelle
qY p = inv_into Y h (qZ p)
```

The quotient-map condition transfers because composition with a homeomorphism inverse preserves quotient maps. The scheme boundary conditions transfer because equality of `qY` values is equivalent to equality of `qZ` values, by injectivity of the inverse homeomorphism. The polygon witnesses `P`, `vx`, `vy` are unchanged.

This lemma would solve more than the current front-cancel bridge. It will also help compare canonical quotients to arbitrary quotients in cut-paste and final normal-form realization.

---

## 7. Advice on cancellation and short schemes

The current `valid_operation_preserves_quotient_homeo` still has a short-cancel case that the source itself acknowledges is genuinely false for a target of length two: the target cannot satisfy `top1_quotient_of_scheme_on` because the strict polygon predicate requires length at least three. ([GitHub][2])

This should not remain as a `sorry`. There are only two honest fixes.

The fastest fix is to strengthen the valid cancel operation with a side condition:

```isabelle
length (u @ v) ≥ 3
```

or make the preservation theorem require the target scheme be proper/realisable:

```isabelle
top1_proper_scheme t ⟹
top1_valid_scheme_operation s t ⟹
...
```

The cleaner but larger fix is to replace `top1_quotient_of_scheme_on` by a more general `top1_realizes_scheme_on` predicate that handles degenerate normal forms of length zero or two. Given the current state of the project, the side-condition route is probably better.

For uncancel, do not build a second geometry proof if possible. Once front cancel is proved and `scheme_quotient_exists`/uniqueness/transport are stable, derive uncancel from cancel plus existence of the extended quotient and symmetry of homeomorphism. The current source already says this is the intended route. ([GitHub][2])

---

## 8. Advice on `v_context_left`

The worker is still paying for the decision to include `v_context_left` as a primitive valid operation. The source has many `v_context_left` subcases, including inner rotate, inner cancel, inner invert, inner cut-paste, and inner flip-label cases. Some are admitted with comments saying they are not exercised by the normal-form chain or require properness assumptions. ([GitHub][2])

This remains a design problem. `context_left` is not a Munkres primitive polygon operation; it is closure infrastructure saying that a move can be applied inside a larger word.

The best fix is to split the relation:

```text
primitive_valid_operation:
  rotate, invert, fresh relabel, flip, cancel, uncancel, cut-paste...

valid_contextual_equiv:
  symmetric/transitive/contextual closure of primitive_valid_operation
```

Then prove:

```text
primitive moves preserve quotient realization;
contextual closure preserves it by induction.
```

If the worker does not want to refactor, then weaken the theorem to the actual use case: contextual moves inside proper schemes where the whole prefixed scheme remains proper and the target remains realizable. That will eliminate the false short-cancel and non-fresh prefix cases. But continuing to prove a completely general `v_context_left` case is likely to waste time.

---

## 9. Advice on cut-paste

The source still has admits for the three cut-paste variants. Some are currently formulated as same-space quotient preservation; the comments say they should be handled by polygon cut/reglue or edge permutation. ([GitHub][2])

Do not prove arbitrary `quotient_scheme_edge_permutation` unless it is genuinely needed. A general edge permutation is stronger than Munkres’ moves and can fail to preserve polygon boundary adjacency in a simple way. The live helper `quotient_scheme_edge_permutation` is broad and currently admitted; it should not become a new central blocker. ([GitHub][2])

The better theorem is one geometric cut-reglue lemma:

```isabelle
lemma polygon_cut_reglue_preserves_quotient_homeo:
  assumes "top1_quotient_of_scheme_on X TX old_scheme"
      and "cut_reglue_move old_scheme new_scheme"
  shows "∃Y TY h.
           top1_quotient_of_scheme_on Y TY new_scheme ∧
           top1_homeomorphism_on X TX Y TY h"
```

Then instantiate it for `cut_paste`, `cut_paste2`, and `cut_paste_opp`.

The canonical quotient machinery may make this easier:

```text
old realization
→ canonical quotient of old scheme
→ explicit cut-reglue homeomorphism between canonical quotients
→ canonical quotient of new scheme
→ transport back if needed
```

This is more robust than trying to mutate the same quotient witness.

---

## 10. Theorem 78.2 and scheme extraction should be merged

Theorem 78.2 still returns only a polygonal region and a quotient map. Then Theorem 77.5 immediately needs a proper scheme extracted from that polygon quotient and leaves that step admitted. ([GitHub][2])

That is the wrong data flow. The edge labels should be carried during polygon-pasting, not reconstructed later from an opaque quotient map.

Introduce a stronger theorem:

```isabelle
theorem connected_triangulable_surface_has_proper_scheme_quotient:
  assumes "top1_is_surface_on X TX"
      and "top1_connected_on X TX"
      and "top1_is_triangulable_on X TX"
  obtains scheme where
    "top1_quotient_of_scheme_on X TX scheme"
    "∀label. card {i. i < length scheme ∧ fst (scheme ! i) = label} ∈ {0, 2}"
```

Then Theorem 77.5 does not need the current scheme-extraction `sorry`.

The proof should use the dual graph/spanning-tree picture that Munkres uses informally:

```text
triangulation of connected surface
→ connected dual graph
→ choose a spanning tree
→ paste triangles along tree edges
→ one polygon remains
→ remaining boundary edges are paired by the surface identifications
→ labels and orientations are recorded during construction
```

The current Theorem 78.2 proof already has the base case and states this induction plan in comments; the `card 𝒯 > 1` induction step is the missing formalization. ([GitHub][2])

---

## 11. Sphere realization and projective `m = 1`

Theorem 77.5 still has a sphere-case `sorry` after obtaining a quotient of the normal form

```isabelle
[(a, True), (a, False), (b, True), (b, False)]
```

The proof needs a named lemma:

```isabelle
lemma sphere_scheme_realizes_sphere:
  assumes "a ≠ b"
      and "top1_quotient_of_scheme_on Y TY
             [(a, True), (a, False), (b, True), (b, False)]"
  shows "∃h. top1_homeomorphism_on Y TY top1_S2 top1_S2_topology h"
```

Do not prove this inline. This is one of the standard normal-form realization theorems and should be reusable. ([GitHub][2])

The projective `m = 1` handling is still problematic. The current final theorem derives a contradiction because `top1_m_projective_scheme 1` has length two and `top1_quotient_of_scheme_on` requires at least three polygon sides. That is not a faithful classification proof: the projective plane is a real case. ([GitHub][2])

Fix this by changing the normal-form realization layer, not by contradiction. Either make the projective normal form for `m = 1` a realizable four-edge/dunce-cap model, or introduce a realization predicate that handles the two-edge `aa` word via the projective-plane model. The final classification should prove that `m = 1` gives `RP²`, not that the case is impossible.

---

## 12. Certification and hygiene

The project still has a draft final session. The `ROOT` file ends with:

```isabelle
session AlgTop = AlgTopCached14 +
  options [quick_and_dirty, timeout = 600]
  theories AlgTop
```

so the final proof is not certified even if the visible `sorry` count eventually reaches zero. ([GitHub][3])

The final release gate should be:

```bash
grep -RIn --include='*.thy' '\bsorry\b\|\boops\b' tst
isabelle build -D tst -o quick_and_dirty=false
```

Then classify every hit as active executable gap, comment-only occurrence, obsolete scratch material outside the final dependency chain, or historical `oops`. A “dead” executable `sorry` inside an imported theory is still not acceptable for the final formalization.

---

## Recommended completion order

I would advise the worker to proceed in this order.

1. **Finish `compact_surj_quotient` as two lemmas:** closed surjection implies quotient map; continuous map from compact polygon to Hausdorff polygon is closed. This is the current local blocker and should be made global. ([GitHub][8])

2. **Extract `regular_ngon_polygonal_region` from `scheme_quotient_exists` or delete it.** Its content appears to be proved inside the canonical quotient theorem; it should not remain as a standalone executable `sorry`. ([GitHub][2])

3. **Package the type bridge as `quotient_of_scheme_transport_homeomorphism`.** If `Z` realizes a scheme and `Y ≅ Z`, then `Y` realizes the same scheme via `inv_into` composed with the quotient map. This will solve the polymorphic bridge in front cancel and later uniqueness/canonical quotient uses. ([GitHub][2])

4. **Prove spur collapse on the disk, then transport to polygons.** Use `quotient_same_fibres_homeomorphic`; do not try to show the polygon-domain collapse is a homeomorphism. The fibre-equivalence statement is the real theorem. ([GitHub][2])

5. **Handle short cancellation honestly.** Add a length/properness side condition or change the preservation theorem to only cover realizable targets. Do not leave the acknowledged false length-two case as a theorem-level admit. ([GitHub][2])

6. **Refactor or restrict `v_context_left`.** Prefer contextual closure outside primitive operations. If keeping it, add global properness/freshness assumptions so bad subcases are impossible. ([GitHub][2])

7. **Replace the cut-paste admits by one cut-reglue theorem.** Avoid proving arbitrary edge permutation unless the exact theorem is actually needed. ([GitHub][2])

8. **Strengthen §78.2 to return a proper scheme quotient.** This should eliminate the scheme-extraction `sorry` in Theorem 77.5. ([GitHub][2])

9. **Prove `sphere_scheme_realizes_sphere` and fix projective `m = 1`.** The final theorem should realize `RP²`, not rule out the case by a length contradiction. ([GitHub][2])

10. **Remove `quick_and_dirty` and run the certified build.** Regenerate `STMT_INDEX`, README status, and the sorry audit from the final SHA. ([GitHub][3])

---

## Direct advice to the worker

You are stuck in a reasonable place: `compact_surj_quotient` is exactly the kind of “obvious topology” lemma that Munkres uses implicitly and Isabelle makes explicit. Prove it as a general closed-surjection quotient lemma plus a compact-Hausdorff closed-map lemma, not inside the spur-collapse proof.

The canonical quotient construction is a major win. Now stabilize it by extracting reusable lemmas and deleting the redundant regular-ngon helper. Then finish front cancel through:

```text
canonical quotients
→ compact-surjection quotient map
→ spur-collapse fibre equivalence
→ quotient_same_fibres_homeomorphic
→ type-transport along homeomorphism
```

Do not spend much more time on arbitrary edge permutations or same-space cut-paste. The final route should be homeomorphic realization, not same-space preservation.

The last book-level tasks are now very concrete:

```text
front cancel / uncancel,
cut-paste,
78.2 polygon-pasting with scheme labels,
sphere realization,
projective m=1 realization,
certified build.
```

The project is much closer than the raw `sorry` count suggests, but the remaining gaps are all high-value geometric interface lemmas.

[1]: https://github.com/JUrban/isa_algtop1/commits/main/tst?utm_source=chatgpt.com "History for tst - JUrban/isa_algtop1 · GitHub"
[2]: https://raw.githubusercontent.com/JUrban/isa_algtop1/refs/heads/main/tst/AlgTop.thy?utm_source=chatgpt.com "raw.githubusercontent.com"
[3]: https://raw.githubusercontent.com/JUrban/isa_algtop1/main/tst/ROOT?utm_source=chatgpt.com "raw.githubusercontent.com"
[4]: https://raw.githubusercontent.com/JUrban/isa_algtop1/refs/heads/main/tst/PLAN_zero_sorry.md?utm_source=chatgpt.com "raw.githubusercontent.com"
[5]: https://raw.githubusercontent.com/JUrban/isa_algtop1/refs/heads/main/tst/STMT_INDEX.txt?utm_source=chatgpt.com "raw.githubusercontent.com"
[6]: https://raw.githubusercontent.com/JUrban/isa_algtop1/main/tst/README_PROOF_STATUS.md?utm_source=chatgpt.com "raw.githubusercontent.com"
[7]: https://github.com/JUrban/isa_algtop1/commit/6687d6c770f09ca87e9a3463bf27819ab4052f41?utm_source=chatgpt.com "Extract compact_surj_quotient helper; derive hf_quot from it · JUrban/isa_algtop1@6687d6c · GitHub"
[8]: https://github.com/JUrban/isa_algtop1/commit/fe5917e4ab19f24951aee0cce45f82f7b3402f0f?utm_source=chatgpt.com "Document compact_surj_quotient proof strategy (Munkres Cor. 22.3) · JUrban/isa_algtop1@fe5917e · GitHub"
