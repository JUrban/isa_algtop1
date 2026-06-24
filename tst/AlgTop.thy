theory AlgTop
  imports "AlgTopCached19.AlgTopCached19"
begin

method_setup by20000 =
  \<open>
    Method.text_closure >> (fn text => fn ctxt => fn facts =>
      let
        val limit = Time.fromMilliseconds 20000
        fun timed_seq name lim seq =
          Seq.make (fn () =>
            (case
               (Timeout.apply lim (fn () => Seq.pull seq) ()
                 handle Timeout.TIMEOUT _ =>
                   error (name ^ ": timeout after " ^
                     string_of_int (Time.toMilliseconds lim) ^ " ms"))
             of
               NONE => NONE
             | SOME (st, seq') => SOME (st, timed_seq name lim seq')))
        fun method_evaluate_rt text' ctxt' facts' =
          NO_CONTEXT_TACTIC ctxt' (Method.evaluate_runtime text' ctxt' facts')
        fun tac st = timed_seq "by20000" limit (method_evaluate_rt text ctxt facts st)
      in
        SIMPLE_METHOD tac facts
      end)
  \<close>
  "Apply method with 20000ms timeout"

\<comment> \<open>SORRY ANALYSIS (as of 2026-06-26):

24 sorry proof commands in AlgTop + 4 in AlgTopCached19 = 28 total. Build ~26s.

CATEGORY BREAKDOWN:
  1 PASTE CHAIN (geometric core): theorem\\_76\\_1\\_paste\\_chain existential.
  5 CUT-PASTE VARIANTS: cut\\_paste2, cut\\_paste\\_opp, general cancel, fresh label, relabel.
    All depend on theorem\\_76\\_1\\_paste\\_chain.
  1 SPUR CONSTRUCTION: general uncancel (proper version IS proved).
  14 VALID\\_OPERATION: context-left structural, reverse ops, false cases.
    NOT on classification critical path.
  3 ASSEMBLY: Theorem 78.2 induction, extract scheme, sphere realization.

PROVED INFRASTRUCTURE:
  paste\\_chain\\_boundary\\_C7: ZERO SORRY (~800 lines, all 5 cases).
  paste\\_chain\\_target\\_label: label correspondence for target scheme.
  paste\\_chain\\_sigma\\_x/y: boundary edge-correspondence map definitions.
  paste\\_sigma\\_c\\_edge, \\_inv\\_u2\\_edge, \\_v\\_edge: edge correspondence lemmas.
  nth\\_append\\_first/second: list indexing helpers.

GEOMETRIC CORE (THE blocker):
  Define g = q2 composed with phi piecewise on P2 (phi is DISCONTINUOUS but q2 o phi
  is continuous because C7 absorbs the jumps at the dividing line v0-v(k+1)).
  Left half: phi\\_L reverses vertex order in Q1 (barycentric extension).
  Right half: phi\\_R shifts vertices in Q2 (barycentric extension).
  At dividing line: g\\_left = q2(edge\\_0(s)), g\\_right = q2(edge\\_k(s)).
  These match by C7 for a-pair: q2(edge\\_0(s)) = q2(edge\\_k(s)).
  C7 for w': from paste\\_chain\\_boundary\\_C7 (PROVED).
  C8: each half maps bijectively to sub-polygon interior, q2 injective there.
  C9: edges map to distinct original edges, q2 separates them.
  Approach: adapt spur\\_collapse fan-map infrastructure (sector detection + Cramer coords).

CRITICAL BUG (session 1673): quotient\\_rearrangement\\_homeomorphism is FALSE!
  Counterexample: [(a,T),(b,T),(a,F),(b,F)] (Klein bottle) vs [(a,T),(a,F),(b,T),(b,F)] (sphere).
  Same fst multiset but different Euler characteristic (0 vs 2). NOT homeomorphic!
  Proper cut-paste proofs still route through this FALSE lemma via sorry propagation.
  Their CONCLUSIONS are correct but proof routes need restructuring.
  Correct approach: multi-polygon paste (Theorem 76.1, per-polygon-op invariance).

PROVED (sessions 1664-1677):
  - spur\\_arc\\_match\\_forces\\_edge: weakened (false case removed)
  - cut\\_paste\\_opp\\_proper: hlabel+hbij PROVED (depends on rearrangement lemma)
  - cut\\_paste\\_proper: hlabel+hbij PROVED (depends on rearrangement lemma)
  - Lemma\\_77\\_1\\_step1: PROVED as corollary of cut\\_paste
  - suffix\\_rotate, multi\\_polygon\\_paste\\_flip: DELETED (unused + sorry'd/false)

SORRY INVENTORY (23 in AlgTop):
A. FALSE LEMMA (1): quotient\\_rearrangement\\_homeomorphism (line ~558). UNCLOSEABLE.
   Proper cut-paste proofs depend on it. Needs replacement with multi-polygon paste.
B. NON-PROPER CUT-PASTE (5): cut\\_paste, cut\\_paste2, cut\\_paste\\_opp, cancel, uncancel.
   Need multi-polygon infrastructure or general scheme\\_quotient\\_exists.
C. GENUINELY FALSE (2): v\\_cancel short (len=2), v\\_context\\_left+v\\_cancel short.
   Never arise in classification chain (proper schemes have even length \\<ge> 4).
D. REVERSE OPERATIONS (3): v\\_cut\\_paste\\_reverse, v\\_cut\\_paste2\\_reverse, context\\_left+reverse.
E. CONTEXT-LEFT STRUCTURAL (8): various inner ops can't be expressed as full-scheme ops.
   NOT on classification critical path (chain only uses v\\_relabel fresh = PROVED).
F. UNUSED BOOK THEOREM (1): Theorem\\_76 relabel freshness gap.
G. ASSEMBLY (3): Theorem\\_78\\_2 induction, extract scheme, sphere realization.

CLASSIFICATION CHAIN: scheme\\_normal\\_form\\_valid uses rotate(25), flip(22), cancel(13),
  cut\\_paste\\_opp(11), cut\\_paste(11), relabel(8), invert(4), context\\_left(4 with v\\_relabel),
  uncancel(3), cut\\_paste\\_reverse(2), cancel\\_reverse(2).
  PROVED: rotate, flip, cancel(proper+fresh), uncancel(proper+fresh), invert, relabel(fresh),
  context\\_left(v\\_relabel fresh), cut\\_paste\\_opp\\_proper, cut\\_paste\\_proper.
  SORRY: quotient\\_rearrangement\\_homeomorphism (core), reverse ops, assembly (3).
   CRITICAL PATH for v\\_cut\\_paste/v\\_cut\\_paste\\_opp operations.
C. PER-POLYGON ROTATION (2 sorrys, L9962/10010):
   Proper versions need geometric arc-permutation construction.
   CRITICAL PATH.
D. CONTEXT-LEFT + STRUCTURAL (7 sorrys, various):
   NOT on critical path. Only v\\_relabel (fresh) used by classification chain = PROVED.
E. FINAL ASSEMBLY (2 sorrys, L10695/10753):
   Extraction: construct edge scheme from polygonal quotient.
   Sphere: quotient of [(a,T),(a,F),(b,T),(b,F)] \\<cong> S2.

DEPENDENCY TREE FOR CANCEL CHAIN:
  spur\\_collapse\\_cancel\\_homeo (phi construction, ~2 sorry proof commands)
    phi\\_fn: piecewise-affine fan extension from v\\_1 to centroid(P\\_w)
    PROVED: hdet\\_general, huniq\\_lt/huniq\\_gt, hfan\\_cover,
            prop1 (range), prop2 (continuity), prop3 (surjectivity),
            hphi\\_affine\\_on\\_sector (boundary matching), hPe\\_compact,
            centroid properties, sector determinants > 0,
            all edge helpers, arc-not-on-edge, hjv\\_eq,
            phi\\_s2/phi\\_t2 decomposition, cyclic\\_sign\\_change
    REMAINING: prop10 (interior injectivity), prop12 (spur\\<noteq>int)
    PROVED STANDALONE: cramer\\_injective, triangle\\_coords\\_injective,
            same\\_sector\\_affine\\_injective, centroid\\_weight\\_not\\_on\\_edge
    <- front\\_cancel\\_proper\\_direct (0 sorry)
      <- front\\_cancel\\_proper (0 sorry)
      <- quotient\\_of\\_scheme\\_uncancel\\_front\\_proper (0 sorry)
      <- front\\_cancel\\_realization\\_homeo\\_proper (0 sorry)

PHI CONSTRUCTION (session 1550): piecewise-affine star extension from v\\_1.
  Fan triangulation of P\\_e from v\\_1 into nw sectors.
  Sector j = conv(v\\_1, v\\_{j+2}, v\\_{j+3}) maps affinely to (c\\_w, u\\_j, u\\_{j+1}).
  Spur edges -> arc from u\\_0 to centroid. Non-spur edges -> linear.
  Interior maps injectively to interior (sectors -> centroid-cone sectors of P\\_w).
  C4/C5/C10/C11 extracted for both P\\_e and P\\_w.

SORRY CATEGORIES:
A. GEOMETRIC CORE (1): spur collapse g construction (line ~1825).
B. CUT-PASTE PROPER (2): per-polygon rotation (lines ~2369, 2417).
   Same approach as cancel: fibre matching between canonical quotients.
C. CUT-PASTE SAME-SPACE (3): FALSE as stated (lines 569, 581, 625).
   Need restructuring to homeomorphic-realization form.
D. CUT-PASTE REVERSE (2): FALSE as stated (lines 2605, 2612).
E. GENERAL CANCEL/UNCANCEL (2): no properness (lines 655, 749).
F. VERTEX UNIQUENESS (4): need C12 (lines 1193, 1200, 1338, 1452).
G. CONTEXT-LEFT (11): structural completeness, mostly NOT on critical path.
   Only v\\_relabel (fresh prefix) is used by classification chain = PROVED.
H. GENUINELY FALSE (2): short scheme (lines 2572, 2739).
I. MISC (3): edge-perm (FALSE) + relabel freshness.
J. FINAL ASSEMBLY (3): Thm 78.2 + extraction + sphere.

CRITICAL PATH:
1. spur\\_collapse\\_cancel\\_homeo (A) -> cancel chain -> v\\_cancel in valid chain
2. cut-paste proper (B) -> v\\_cut\\_paste, v\\_cut\\_paste\\_opp in valid chain
3. cut-paste same-space (C) needs restructuring to use proper versions
4. Thm 78.2 (J) + extraction (J) + sphere (J)

FOR CLASSIFICATION CHAIN ONLY: items C, D, E, F, G, H, I are mostly dead code.
The chain uses only: cancel (proper+fresh), cut-paste (proper), rotate, invert,
relabel (fresh), flip-label, and context-left with inner v\\_relabel (all PROVED
except cancel and cut-paste geometric cores).

KEY PROVED INFRASTRUCTURE:
- scheme\\_quotient\\_exists(1,2), scheme\\_quotient\\_uniqueness
- front\\_cancel\\_proper, quotient\\_of\\_scheme\\_uncancel\\_front\\_proper
- front\\_cancel\\_proper\\_direct, spur\\_collapse\\_cancel\\_homeo (surrounding only)
- front\\_cancel\\_realization\\_homeo\\_proper
- polygon\\_sub\\_rearrange\\_sigma\\_props (sigma permutation properties)
- scheme\\_normal\\_form\\_valid (cached)
- phi\\_bdy + junction continuity + spur-non-spur separation (for spur collapse)\<close>
\<comment> \<open>PROVABLY FALSE (2026-06-14): arbitrary edge permutation does NOT preserve the quotient space.
   Counterexample: s = [a,b,a\<inverse>,b\<inverse>] (torus) permuted to s' = [a,a\<inverse>,b,b\<inverse>] (sphere).
   Same multiset of labelled edges, but the ORDERING matters for the identification pattern.
   Only CYCLIC permutation (operation (iv) in Munkres §76) preserves the quotient space.
   See quotient\\_of\\_scheme\\_rotate (AlgTopCached13) for the correct cyclic version.
   The sorrys that referenced this lemma need alternative approaches:
   cut-paste operations need Munkres' 3-step cut-combine-paste (requires multi-polygon quotients).\<close>
\<comment> \<open>DELETED: quotient\\_of\\_scheme\\_edge\\_permutation.
   This was PROVABLY FALSE — counterexample: torus [a,b,a⁻¹,b⁻¹] vs sphere [a,a⁻¹,b,b⁻¹].
   Same multiset but different quotient spaces. Only CYCLIC permutation is valid (§76 op (iv)).
   All sorrys that depended on this need the multi-polygon approach instead.\<close>

\<comment> \<open>Munkres Theorem 76.1 and multi-polygon quotients.

   The book's §76 operations (cut, paste, cancel) use MULTI-POLYGON quotients:
   given m polygonal regions with labelling schemes w1,...,wm, the quotient space X
   is obtained by identifying edges with matching labels across ALL polygons.

   Theorem 76.1: if X is the quotient of (y0 y1, w2,...,wm), then X is also the
   quotient of (y0 c^{-1}, c y1, w2,...,wm) where c is fresh. And conversely.

   KEY INSIGHT FOR FORMALIZATION: a multi-polygon scheme (w1, w2) with a shared
   label c connecting them is EQUIVALENT to the single-polygon scheme w1 @ w2
   (concatenation), because the c-identification in the single polygon does the
   same job as the cross-polygon pasting.

   Specifically: multi(y0 c^{-1}, c y1) = single(y0 @ [c^{-1}, c] @ y1)
   when c is fresh. This is because C7 in the single-polygon quotient identifies
   the [c^{-1}] edge with the [c] edge (opposite direction), which pasts the
   two "halves" together -- exactly what multi-polygon pasting does.

   Therefore: Theorem 76.1 in the SINGLE-POLYGON view is:
   quotient(y0 @ y1) = quotient(y0 @ [c^{-1}, c] @ y1) for fresh c.
   This is the UNCANCEL theorem (CUT direction) and CANCEL theorem (PASTE direction).

   The CUT-PASTE OPERATIONS (moving blocks past identified pairs) use:
   1. CUT: y0 y1 -> multi(y0 c^{-1}, c y1) = single(y0 [c^{-1},c] y1)  [UNCANCEL c]
   2. PER-POLYGON OPERATIONS: rotate/flip one polygon independently
      In multi-polygon: trivial (each polygon is separate)
      In single-polygon: these are SUFFIX operations (rotate/flip the part after c)
      which CANNOT be expressed as full-scheme operations.
   3. PASTE: multi -> single  [CANCEL c]

   Step 2 (per-polygon rotation) is where multi-polygon reasoning is needed.
   In the MULTI-POLYGON view: rotating one polygon's scheme just renumbers
   its vertices, which doesn't change the quotient (book operation (iv)).
   The identification depends on LABELS, not on edge ORDER within a polygon.

   In the SINGLE-POLYGON view: suffix rotation changes POSITIONS of
   cross-separator labels, seemingly changing the quotient. But Theorem 76.1
   connects the multi-polygon and single-polygon quotients via DIFFERENT
   polygons (CUT/PASTE changes the polygon, not just the labels).

   CORRECT APPROACH (expert audit §6): prove homeomorphism Y\\_old \\<cong> Y\\_new
   between quotients of DIFFERENT polygons (from scheme\\_quotient\\_exists for
   the old and new schemes). The homeomorphism exists because both
   single-polygon quotients equal the same multi-polygon quotient, which is
   invariant under per-polygon rotation.

   For CANCEL: front\\_cancel\\_proper is proved via uncancel+uniqueness.
   For CUT-PASTE: the quotient-level homeomorphism is still sorry'd.\<close>

\<comment> \<open>Two-polygon quotient (Munkres §76, Theorem 76.1).

   The book's approach: the quotient space X of a multi-polygon labelling scheme
   is obtained by identifying matching-label edges across ALL polygons.

   FORMALIZATION APPROACH: instead of defining multi-polygon quotients explicitly,
   we express Theorem 76.1 using TWO calls to scheme\\_quotient\\_exists plus a
   quotient-of-quotient argument.

   Theorem 76.1 says: quotient(y0 y1) = quotient of two-polygon (y0 c^{-1}, c y1).
   In our formalization: the two-polygon quotient is expressed as follows:
   1. Get Y1 = canonical quotient of (y0 @ [c^{-1}]) by scheme\\_quotient\\_exists
   2. Get Y2 = canonical quotient of ([c] @ y1) by scheme\\_quotient\\_exists
   3. The "two-polygon quotient" is the quotient of Y1 \\<squnion> Y2 (disjoint union)
      by the cross-polygon c-identification
   4. Theorem 76.1: this quotient = the canonical quotient of (y0 @ y1)

   For per-polygon rotation (operation iv): rotating one polygon's scheme
   preserves the multi-polygon quotient because:
   - The identification depends on LABELS, not edge ORDER
   - Rotation preserves labels (just reorders them within the polygon)
   - The cross-polygon identifications are unchanged

   HOWEVER: expressing this in the single-polygon formalization requires
   showing that quotient(y0 @ y1) = quotient(y0 @ rotate(y1)), which is NOT
   true in the single-polygon view (different edge positions).

   The resolution: CUT + ROTATE + PASTE operates through DIFFERENT polygons.
   The CUT gives two polygons. ROTATE one. PASTE back. The result is a
   DIFFERENT polygon (not the original) with a DIFFERENT scheme (not a rotation
   of the original). But the quotient space is the SAME.

   For the cut-paste operations: we need to show that the quotient of the
   original scheme equals the quotient of the rearranged scheme, where both
   are quotients of DIFFERENT polygons (from scheme\\_quotient\\_exists).\<close>

\<comment> \<open>Munkres Theorem 76.1: two-polygon quotient formalization.

   The book defines the quotient of m polygonal regions by a labelling scheme.
   Our formalization uses SINGLE-POLYGON quotients (top1\\_quotient\\_of\\_scheme\\_on).

   Theorem 76.1 in single-polygon view: quotient(y0@y1) = quotient(y0@[c^{-1},c]@y1)
   for fresh c. This is the UNCANCEL/CANCEL pair (both PROVED for proper+fresh).

   For CUT-PASTE operations: the book uses CUT + per-polygon ROTATE + PASTE.
   The per-polygon ROTATE changes the edge ORDER within one polygon.
   In single-polygon view, this changes edge POSITIONS (and the quotient).
   In multi-polygon view, this just renumbers vertices (quotient unchanged).

   The resolution (Munkres §76 operation iv): "Permute. One can replace
   any one of the schemes wi by a cyclic permutation of wi. This amounts to
   renumbering the vertices of the polygonal region Pi so as to begin with
   a different vertex; it does not affect the resulting quotient space."

   For proper schemes: each polygon in the multi-polygon scheme has its own
   INDEPENDENT vertex numbering. Rotating one polygon is just changing which
   vertex is "first". The identification pattern (by labels) is the same.

   KEY FACT: same multiset does NOT suffice for homeomorphism.
   Counterexample: torus [a,b,a^{-1},b^{-1}] vs sphere [a,a^{-1},b,b^{-1}].
   The homeomorphism depends on the SPECIFIC CUT position and rotation amount.\<close>

\<comment> \<open>KEY LEMMA (Munkres Theorem 76.1, single-polygon formulation):
   The two-polygon quotient of (y0 c^{-1}, c y1) equals the single-polygon
   quotient of y0 y1 (when c is fresh).

   In our formalization: this is expressed as
   quotient(y0 @ [c^{-1}, c] @ y1) = quotient(y0 @ y1)
   which is the CANCEL/UNCANCEL pair.

   CUT direction (= UNCANCEL): proved as quotient\\_of\\_scheme\\_uncancel\\_proved.
   PASTE direction (= CANCEL): proved as front\\_cancel\\_proper (for proper+fresh).

   Per-polygon operations (book's operations applied to individual polygons
   in the multi-polygon setting) correspond to SUFFIX operations on the
   single-polygon scheme y0 @ [c^{-1}, c] @ y1. These require:
   - Suffix rotate: rotate the [c] @ y1 portion independently
   - Suffix flip: flip the [c] @ y1 portion independently
   These CANNOT be reduced to full-scheme operations and require either:
   (a) Formal multi-polygon quotient infrastructure, OR
   (b) Geometric polygon rearrangement homeomorphism.

   The cut-paste sorrys below are pending this infrastructure.\<close>

\<comment> \<open>Multi-polygon quotient infrastructure (Munkres §76).

   Model: two disjoint polygons P1, P2 with schemes w1, w2.
   The multi-polygon quotient X is obtained by identifying all
   matching-label edges across both polygons.

   Formally: given Y1 = quotient(P1, w1) and Y2 = quotient(P2, w2),
   the multi-polygon quotient X is obtained by further identifying
   the boundary equivalence classes of Y1 and Y2 that share labels.

   Theorem 76.1: X is homeomorphic to the single-polygon quotient
   of the scheme y0@y1 (obtained by pasting P1 and P2 along c).

   Per-polygon rotation: rotating w2 to rotate(w2) preserves X because
   each polygon is a SEPARATE object with its own vertex numbering.
   Rotating one polygon just changes which vertex is "first" -- the
   identification pattern (by labels) is unchanged.\<close>

\<comment> \<open>PROVABLY FALSE (2026-06-16): per\\_polygon\\_rotation\\_homeo IS FALSE.
   Counterexample: y0=[(1,T)], c=3, u=[(2,T)], v=[(1,F),(2,F)].
   s1 = [(1,T),(3,F),(3,T),(2,T),(1,F),(2,F)] -> cancel c -> torus
   s2 = [(1,T),(3,F),(3,T),(1,F),(2,F),(2,T)] -> cancel c -> sphere
   TORUS \\<noteq> SPHERE.

   The error: suffix rotation in a CONCATENATED scheme changes cross-boundary
   label positions, which genuinely changes the quotient space.
   The book's operation (iv) "Permute" means RENUMBERING VERTICES of a
   polygon (same polygon, same labels, same edges), NOT suffix rotation in
   a concatenated scheme. Renumbering vertices = cyclic rotation = quotient\\_of\\_scheme\\_rotate (PROVED).

   The cut-paste operations require the actual MULTI-POLYGON operations
   (CUT + per-polygon ROTATE/FLIP + PASTE) formalized with SEPARATE
   polygon objects, not concatenated schemes on a single polygon.\<close>

\<comment> \<open>DELETED: suffix\\_rotate\\_via\\_separator and per\\_polygon\\_rotation\\_homeo are FALSE.
   See counterexample above. Suffix rotation in concatenated schemes changes the quotient.

   CORRECT MULTI-POLYGON APPROACH (Munkres §76):
   The book's cut-paste operations use SEPARATE polygons with INDEPENDENT vertex numbering.
   Per-polygon operations (ROTATE, FLIP) are quotient\\_of\\_scheme\\_rotate and
   quotient\\_of\\_scheme\\_invert applied to individual polygons (PROVED).
   Cross-polygon joining (PASTE) identifies matching-label edges between separate polygons.

   The multi-polygon quotient is NOT the same as the quotient of a concatenated scheme.
   It requires SEPARATE polygon objects joined by label matching.

   Current status: the cut-paste-proper sorrys at lines ~1430/1480 require
   the genuine multi-polygon joining operation. This is ~500 lines of infrastructure
   that needs to be built following the book's Theorem 76.1 exactly.\<close>

\<comment> \<open>MULTI-POLYGON PASTE (Munkres §76, Theorem 76.1).
   Given two DISJOINT polygons P1, P2 with schemes w1, w2, and a shared label c
   (c^{-1} in w1, c in w2), the PASTE operation joins P1 and P2 along c-edges
   to form a single polygon P with scheme y0@y1 (where w1 = y0@[c^{-1}], w2 = [c]@y1).

   Formal model: P1 and P2 are disjoint subsets of R^2. The combined quotient of
   P1 \\<union> P2 by ALL identifications (within-P1, within-P2, cross-polygon c) is Z.
   Z is homeomorphic to the single-polygon quotient of y0@y1 (by Theorem 76.1).

   This is proved in two parts:
   (a) Define the combined quotient of P1 \\<union> P2 (multi-polygon quotient Z)
   (b) Show Z \\<cong> quotient(y0@y1) (Theorem 76.1)

   For the cut-paste operations: the book uses CUT (= split single polygon into P1, P2),
   per-polygon ROTATE/FLIP (= quotient\\_of\\_scheme\\_rotate/invert on individual Pi),
   and PASTE (= join back). The key: per-polygon operations on SEPARATE polygons
   preserve the multi-polygon quotient Z (because each polygon has independent vertices).\<close>

\<comment> \<open>Theorem 76.1 (multi-polygon paste = single-polygon quotient).
   The combined quotient of two disjoint polygons (joined along c-edges)
   is homeomorphic to the single-polygon quotient of the combined scheme.

   In our formalization: this follows from the "composite of quotient maps" principle.
   Pasting P1 and P2 along c-edges is a quotient map (identifying the c-boundary).
   The result P = P1 \\<union> P2 / c-identification is a single polygon.
   Then the remaining identifications (from y0, y1 labels) give the final quotient.

   This is PROVED by the cancel/uncancel pair:
   - CUT direction: quotient(y0@y1) = quotient(y0@[c^{-1},c]@y1) [UNCANCEL, PROVED]
   - PASTE direction: quotient(y0@[c^{-1},c]@y1) \\<cong> quotient(y0@y1) [CANCEL, PROVED]

   The multi-polygon quotient Z is the SAME as quotient(y0@[c^{-1},c]@y1) when
   the identification is on a single polygon. But when P1 and P2 are SEPARATE
   polygons with independent vertices, Z involves a DIFFERENT construction:
   the c-identification joins the BOUNDARY of P1 to the BOUNDARY of P2,
   creating a new polygon P whose internal structure is different from the
   concatenated scheme polygon.

   The KEY FACT we need (but don't yet have): the multi-polygon quotient Z
   (with SEPARATE polygons) is homeomorphic to the single-polygon quotient
   of y0@y1 (where P is the PASTED polygon). This is a GEOMETRIC fact about
   joining convex polygons along shared edges.\<close>

\<comment> \<open>Multi-polygon paste homeomorphism (Munkres Theorem 76.1).
   Given:
   - Y1 with topology TY1, a quotient of proper scheme w1 (containing c^{-1})
   - Y2 with topology TY2, a quotient of proper scheme w2 (containing c)
   - c is the ONLY shared label between w1 and w2
   - Y_combined is the quotient of the combined scheme (y0@y1 where w1=y0@[c^{-1}], w2=[c]@y1)

   Then: there exists a homeomorphism h: Y_combined \\<to> Z
   where Z is the multi-polygon quotient of (Y1, Y2) joined along c.

   This is the GEOMETRIC form of Theorem 76.1.\<close>

\<comment> \<open>For the cut-paste operations: the KEY THEOREM is:
   If I CUT a polygon along a diagonal (= UNCANCEL c), do per-polygon operations
   (ROTATE/FLIP = quotient\\_of\\_scheme\\_rotate/invert on individual polygons), and
   PASTE back (= CANCEL c), the result is homeomorphic to the original.

   The per-polygon operations are ALREADY PROVED (rotate, flip, relabel on individual polygons).
   The CUT and PASTE are PROVED (cancel/uncancel).
   The MISSING LINK: showing that CUT + per-polygon op + PASTE gives a valid
   sequence that preserves the quotient homeomorphism type.

   This requires the multi-polygon paste homeomorphism (Theorem 76.1) plus the
   per-polygon rotation/flip invariance of the multi-polygon quotient.\<close>

\<comment> \<open>Multi-polygon paste result: the key lemma connecting multi-polygon and single-polygon quotients.
   Given two proper sub-schemes w1, w2 sharing label c (and only c),
   the single-polygon quotient of y0@y1 (where w1=y0@[c^{-1}], w2=[c]@y1)
   is homeomorphic to the quotient obtained by:
   1. Take quotient Y1 of w1 (on its own polygon P1)
   2. Take quotient Y2 of w2 (on its own polygon P2)
   3. Apply quotient\\_of\\_scheme\\_rotate on Y2 (per-polygon operation)
   4. Paste the rotated Y2 back with Y1 along c
   5. The result is the quotient of a DIFFERENT single polygon by a DIFFERENT scheme

   The result of steps 1-5 is homeomorphic to a single-polygon quotient of the
   rearranged scheme. This is the formal content of the book's CUT+ROTATE+PASTE argument.\<close>

\<comment> \<open>Munkres Lemma 77.1 Step 1: a[y1]a[y2] ~ aa[y1^{-1} y2].
   MOVED after quotient\\_of\\_scheme\\_cut\\_paste (see below).\<close>

\<comment> \<open>For the cut-paste-opp operation specifically:
   old = u0@u1@(a,T)@u2@(a,F)@u3
   new = u0@(a,T)@u2@(a,F)@u1@u3

   Book's derivation: this is achieved by a SEQUENCE of elementary operations:
   1. CUT between u0 and u1 (introduce c)
   2. Per-polygon FLIP of P1 (if needed)
   3. Per-polygon ROTATE of P2
   4. PASTE along a different label (not c!)
   5. CANCEL, RELABEL, etc.

   Each individual step uses PROVED operations on SEPARATE polygons.
   The combination gives the cut-paste rearrangement.

   STATUS: the exact sequence for cut-paste-opp needs to be worked out.
   The individual operations are proved; the composition is the gap.\<close>

\<comment> \<open>MULTI-POLYGON QUOTIENT: formal definition and per-polygon invariance.

   Given two proper sub-schemes w1, w2 with a shared connecting label c:
   w1 = y0 @ [(c\\_label, False)]   (P1's scheme, c^{-1} at end)
   w2 = [(c\\_label, True)] @ y1     (P2's scheme, c at start)

   The multi-polygon quotient Z is defined as:
   Z = quotient(y0 @ y1) (the pasted single-polygon quotient)

   By Theorem 76.1 (= cancel/uncancel, PROVED):
   Z = quotient(y0 @ y1) \\<cong> quotient(y0 @ [(c,F),(c,T)] @ y1)
   The latter is the quotient of the concatenated scheme w1 @ w2 on a single polygon.

   PER-POLYGON INVARIANCE: if we apply FLIP to P1 and ROTATE to P2:
   w1' = flip(w1), w2' = rotate(w2)
   Then the NEW pasted scheme y0' @ y1' gives the SAME multi-polygon quotient:
   Z = quotient(y0 @ y1) = quotient(y0' @ y1')

   This is NOT the same as saying quotient(w1@w2) = quotient(w1'@w2')
   (which is FALSE for cross-boundary labels). The key: the multi-polygon
   quotient Z is defined via PASTING (removing c), not concatenation.

   The per-polygon operations (flip P1, rotate P2) are applied to SEPARATE
   polygons with INDEPENDENT vertex numbering. The PASTE merges them along c.
   The result is a DIFFERENT pasted polygon with a DIFFERENT scheme.\<close>

\<comment> \<open>Per-polygon invariance (the core missing lemma).
   The multi-polygon quotient Z = quotient(y0@y1) is unchanged when we
   apply per-polygon flip/rotate to the sub-schemes, provided c is fresh
   and the sub-schemes are proper.

   Formally: quotient(y0@y1) \\<cong> quotient(y0'@y1')
   where y0' comes from flipping y0@[c^{-1}] and removing the flipped c,
   and y1' comes from rotating [c]@y1 and removing the rotated c.

   This encapsulates the entire multi-polygon argument in a SINGLE lemma.\<close>
\<comment> \<open>Multi-polygon quotient construction.
   Given two proper sub-schemes w1, w2 with fresh c connecting them:
   w1 = y0 @ [(c,F)]  and  w2 = [(c,T)] @ y1

   Step 1: Get canonical polygons P1, P2 for w1, w2 from scheme\\_quotient\\_exists.
   Step 2: Translate P2 by (10,0) to ensure P1 \\<inter> translate(P2) = \\<emptyset>.
   Step 3: Define the multi-polygon quotient Z as the quotient of P1 \\<union> translate(P2)
           by the combined identification (within-P1 by w1, within-P2 by w2,
           cross-polygon: c-edge of P1 identified with c-edge of P2).
   Step 4: Show Z \\<cong> quotient(y0 @ y1) (Theorem 76.1).

   The per-polygon operations (FLIP, ROTATE) are homeomorphisms of individual
   polygons that map old identifications to new identifications. The combined
   homeomorphism (op1 on P1, op2 on P2) preserves the multi-polygon quotient Z
   because P1 and P2 are disjoint (no interaction at the polygon level).\<close>

\<comment> \<open>The concrete multi-polygon paste lemma.
   Given Y1 \\<mapsto> y0@y1 (single-polygon quotient), and per-polygon FLIP of the y0-part:
   quotient(y0@y1) \\<cong> quotient(y0^{-1}@y1).

   Proof via multi-polygon quotient Z:
   1. Z = multi-polygon quotient of (P1 with w1=y0@[c^{-1}], P2 with w2=[c]@y1)
   2. Z \\<cong> quotient(y0@y1) [Theorem 76.1 = cancel c, PROVED]
   3. FLIP P1: w1' = flip(w1) = [c]@y0^{-1}. Paste: y0^{-1}@y1.
      Z' = multi-polygon quotient of (P1' with w1', P2 with w2)
   4. Z' \\<cong> quotient(y0^{-1}@y1) [Theorem 76.1 = cancel c, PROVED]
   5. Z = Z' [per-polygon FLIP invariance: FLIP P1 is a homeomorphism of P1,
      the combined (flip, id) on P1 \\<squnion> P2 preserves Z]
   6. Compose: quotient(y0@y1) \\<cong> Z = Z' \\<cong> quotient(y0^{-1}@y1)

   Step 5 is the KEY: the multi-polygon quotient is invariant under per-polygon
   homeomorphisms. This follows from: (flip, id): P1\\<union>P2 \\<to> P1\\<union>P2 maps
   old identifications to new identifications, so the quotient is preserved.\<close>
\<comment> \<open>multi\\_polygon\\_paste\\_flip: DELETED (was sorry'd and UNUSED).
   States: quotient(y0@y1) \\<cong> quotient(y0^{-1}@y1). True but needs multi-polygon infrastructure.
   Would follow from quotient\\_rearrangement\\_homeomorphism (core geometric lemma).\<close>

\<comment> \<open>suffix\\_rotate\\_via\\_separator: DELETED. Was FALSE as stated and UNUSED.
   The same-space claim is wrong (sub-polygon rotation doesn't preserve same space).
   Per-polygon rotation preserves HOMEOMORPHISM TYPE but not same-space.\<close>

\<comment> \<open>Generalized transfer: bijection + relative orientation (not exact match).
   Combines quotient\\_of\\_scheme\\_transfer\\_bij (bijection) with quotient\\_of\\_scheme\\_transfer (relative snd).\<close>
lemma quotient_of_scheme_transfer_bij_rel:
  assumes "top1_quotient_of_scheme_on Y TY w"
      and "length w' = length w"
      and "bij_betw \<sigma> {..<length w} {..<length w}"
      and "\<And>i. i < length w \<Longrightarrow> fst (w'!i) = fst (w!(\<sigma> i))"
      and "\<And>i j. \<lbrakk>i < length w; j < length w; fst (w!(\<sigma> i)) = fst (w!(\<sigma> j))\<rbrakk> \<Longrightarrow>
           (snd (w'!i) = snd (w'!j)) = (snd (w!(\<sigma> i)) = snd (w!(\<sigma> j)))"
      and "\<And>i. i < length w \<Longrightarrow> Suc (\<sigma> i) mod (length w) = \<sigma> (Suc i mod (length w))"
  shows "top1_quotient_of_scheme_on Y TY w'"
proof -
  \<comment> \<open>Two-step: w \\<to> w\\_\\<sigma> (bij reindexing) \\<to> w' (relative orientation transfer).\<close>
  define w_\<sigma> where "w_\<sigma> = map (\<lambda>i. w ! (\<sigma> i)) [0..<length w]"
  have hlen_w\<sigma>: "length w_\<sigma> = length w" unfolding w_\<sigma>_def by (by100 simp)
  have hnth_w\<sigma>: "\<And>i. i < length w \<Longrightarrow> w_\<sigma> ! i = w ! (\<sigma> i)"
    unfolding w_\<sigma>_def by (by100 simp)
  \<comment> \<open>Step 1: w \\<to> w\\_\\<sigma> via quotient\\_of\\_scheme\\_transfer\\_bij (exact match).\<close>
  have h_step1: "top1_quotient_of_scheme_on Y TY w_\<sigma>"
  proof (rule quotient_of_scheme_transfer_bij[OF assms(1) hlen_w\<sigma> assms(3)])
    fix i assume "i < length w"
    thus "fst (w_\<sigma>!i) = fst (w!(\<sigma> i))" using hnth_w\<sigma> by (by100 simp)
  next
    fix i assume "i < length w"
    thus "snd (w_\<sigma>!i) = snd (w!(\<sigma> i))" using hnth_w\<sigma> by (by100 simp)
  next
    fix i assume "i < length w" from assms(6)[OF this] show "Suc (\<sigma> i) mod length w = \<sigma> (Suc i mod length w)" .
  qed
  \<comment> \<open>Step 2: w\\_\\<sigma> \\<to> w' via quotient\\_of\\_scheme\\_transfer (same-position, relative snd).\<close>
  have hfst_w\<sigma>: "\<And>i. i < length w \<Longrightarrow> fst (w'!i) = fst (w_\<sigma>!i)"
    using assms(4) hnth_w\<sigma> by (by100 simp)
  have hsnd_w\<sigma>: "\<And>i j. \<lbrakk>i < length w; j < length w; fst (w_\<sigma>!i) = fst (w_\<sigma>!j)\<rbrakk> \<Longrightarrow>
       (snd (w'!i) = snd (w'!j)) = (snd (w_\<sigma>!i) = snd (w_\<sigma>!j))"
    using assms(5) hnth_w\<sigma> by (by100 simp)
  from quotient_of_scheme_transfer[OF h_step1 assms(2)[unfolded hlen_w\<sigma>[symmetric]]
      hfst_w\<sigma>[unfolded hlen_w\<sigma>[symmetric]] hsnd_w\<sigma>[unfolded hlen_w\<sigma>[symmetric]]]
  show ?thesis .
qed

\<comment> \<open>quotient\\_rearrangement\\_homeomorphism DELETED (was FALSE).
   Counterexample: Klein bottle (\\<chi>=0) vs sphere (\\<chi>=2), same fst multiset.
   The proper cut-paste lemmas that used it are also deleted (were dead code).
   Correct approach: theorem\\_76\\_1\\_paste\\_chain (multi-polygon paste).\<close>

\<comment> \<open>The one-vertex-class lemma above is NOT needed! Key discovery:
   For the CUT-PASTE specifically, the piecewise quotient map q': P' \\<to> Y IS continuous
   WITHOUT any one-vertex-class condition, because:
   - Internal junction (former a-edges): C7(1-s) gives
     q(first\\_a(1-s)) = q(second\\_a(1-s)) at every parameter. \\<checkmark>
   - Paste vertices: C7(t=0) gives q(v\\_0) = q(v\\_{1+|u2|}), and
     C7(t=1) gives q(v\\_1) = q(v\\_{2+|u2|}). \\<checkmark>
   So theorem\\_76\\_1\\_paste\\_chain is correct as stated (no extra conditions).
   The proof constructs P' from Q1-flipped \\<union> Q2-permuted and defines q' piecewise.\<close>

\<comment> \<open>CORRECT replacement for the false lemma above: multi-polygon paste.
   The book's Theorem 76.1 CUT+FLIP+PERMUTE+PASTE argument for same-direction cut-paste.
   Given Y quotient of a@y1@[d\\<inverse>,d]@a@y2, the per-polygon FLIP of P1=(a,y1,d\\<inverse>)
   and PERMUTE of P2=(d,a,y2) gives the SAME quotient Y, which is also a quotient of
   the pasted scheme d@y1\\<inverse>@[a\\<inverse>,a]@y2@d (with a-pair NOW ADJACENT).
   Then CANCEL the adjacent a-pair to get d@y1\\<inverse>@y2@d.
   Statement (kept as comment, not as lemma to avoid unused sorry):
     lemma multi\\_polygon\\_flip\\_permute\\_paste:
       fixes a\\_label d\\_label :: nat and y1 y2 :: "(nat \\<times> bool) list"
       assumes "quotient Y TY ([(a,T)] @ y1 @ [(d,F),(d,T),(a,T)] @ y2)"
       shows "quotient Y TY ([(d,T)] @ inv(y1) @ [(a,F),(a,T)] @ y2 @ [(d,T)])"
   Proof needs: per-polygon ops preserve multi-polygon quotient + Theorem 76.1 paste.\<close>

\<comment> \<open>Multi-flip: flip snd for ALL labels in a finite set. Same-space preservation.
   Proved by finite induction: each individual flip is quotient\\_scheme\\_flip\\_label.\<close>
lemma quotient_scheme_flip_labels:
  assumes "top1_quotient_of_scheme_on Y TY w"
      and "finite S"
  shows "top1_quotient_of_scheme_on Y TY (map (\<lambda>(l,b). (l, if l \<in> S then \<not>b else b)) w)"
  using assms(2,1)
proof (induction S arbitrary: w rule: finite_induct)
  case empty
  hence "map (\<lambda>(l,b). (l, if l \<in> {} then \<not>b else b)) w = w"
    by (induction w) (by100 auto)+
  thus ?case using empty.prems by simp
next
  case (insert a S)
  \<comment> \<open>IH: flipping S preserves quotient. Then flip a on top.\<close>
  let ?flip_S = "map (\<lambda>(l,b). (l, if l \<in> S then \<not>b else b)) w"
  have hS: "top1_quotient_of_scheme_on Y TY ?flip_S"
    using insert.IH[OF insert.prems] .
  \<comment> \<open>Now flip label a on top of ?flip\\_S.\<close>
  from quotient_scheme_flip_label[OF hS, of a]
  have "top1_quotient_of_scheme_on Y TY (map (\<lambda>(l,b). (l, if l = a then \<not>b else b)) ?flip_S)" .
  moreover have "map (\<lambda>(l,b). (l, if l = a then \<not>b else b)) ?flip_S =
      map (\<lambda>(l,b). (l, if l \<in> insert a S then \<not>b else b)) w"
  proof (induction w)
    case Nil show ?case by simp
  next
    case (Cons x xs)
    obtain l bo where hx: "x = (l, bo)" by (cases x) simp
    have hhead: "(\<lambda>(l,b). (l, if l = a then \<not>b else b)) ((\<lambda>(l,b). (l, if l \<in> S then \<not>b else b)) (l, bo))
        = (\<lambda>(l,b). (l, if l \<in> insert a S then \<not>b else b)) (l, bo)"
      using insert.hyps(2) by (cases "l = a") simp_all
    have "map (\<lambda>(l,b). (l, if l = a then \<not>b else b))
        (map (\<lambda>(l,b). (l, if l \<in> S then \<not>b else b)) (x # xs))
      = (\<lambda>(l,b). (l, if l = a then \<not>b else b)) ((\<lambda>(l,b). (l, if l \<in> S then \<not>b else b)) x)
        # map (\<lambda>(l,b). (l, if l = a then \<not>b else b)) (map (\<lambda>(l,b). (l, if l \<in> S then \<not>b else b)) xs)"
      by simp
    also have "\<dots> = (\<lambda>(l,b). (l, if l \<in> insert a S then \<not>b else b)) x
        # map (\<lambda>(l,b). (l, if l \<in> insert a S then \<not>b else b)) xs"
      using hhead hx Cons.IH by simp
    finally show ?case by simp
  qed
  ultimately show ?case by metis
qed

\<comment> \<open>Reversal preserves quotient: rev(w) has the same quotient as w.
   Proof: INVERT gives rev(inv w) same space. FLIP\\_ALL restores snd values.
   So rev(w) = flip\\_all(rev(inv w)) = flip\\_all(invert(w)) has same quotient.\<close>
lemma quotient_of_scheme_reverse:
  assumes "top1_quotient_of_scheme_on Y TY w"
  shows "top1_quotient_of_scheme_on Y TY (rev w)"
proof -
  \<comment> \<open>Step 1: INVERT gives Y quotient of rev(inv w).\<close>
  have h1: "top1_quotient_of_scheme_on Y TY (rev (map top1_inverse_edge w))"
    using quotient_of_scheme_invert[OF assms] .
  \<comment> \<open>Step 2: FLIP ALL labels restores snd values: rev(inv w) → rev(w).\<close>
  let ?S = "fst ` set w"
  have hfin: "finite ?S" by simp
  from quotient_scheme_flip_labels[OF h1 hfin]
  have h2: "top1_quotient_of_scheme_on Y TY
    (map (\<lambda>(l,b). (l, if l \<in> ?S then \<not>b else b)) (rev (map top1_inverse_edge w)))" .
  \<comment> \<open>Step 3: flip\\_S(inv w) = w because inv flips snd and flip\\_S flips it back.\<close>
  have hpointwise: "\<And>x. x \<in> set w \<Longrightarrow>
      (\<lambda>(l,b). (l, if l \<in> ?S then \<not>b else b)) (top1_inverse_edge x) = x"
    unfolding top1_inverse_edge_def by (auto split: prod.split)
  have "map ((\<lambda>(l,b). (l, if l \<in> ?S then \<not>b else b)) \<circ> top1_inverse_edge) w = map id w"
    by (rule list.map_cong0) (use hpointwise in auto)
  hence heq_flat: "map (\<lambda>(l,b). (l, if l \<in> ?S then \<not>b else b)) (map top1_inverse_edge w) = w"
    by (simp add: map_map)
  have "map (\<lambda>(l,b). (l, if l \<in> ?S then \<not>b else b)) (rev (map top1_inverse_edge w))
      = rev (map (\<lambda>(l,b). (l, if l \<in> ?S then \<not>b else b)) (map top1_inverse_edge w))"
    by (simp add: rev_map)
  hence heq: "map (\<lambda>(l,b). (l, if l \<in> ?S then \<not>b else b)) (rev (map top1_inverse_edge w)) = rev w"
    using heq_flat by simp
  from h2 this show ?thesis by simp
qed

\<comment> \<open>Helper for nth extraction from appended lists: skip a prefix of known length.\<close>
lemma nth_append_skip: "\<lbrakk>i \<ge> length xs\<rbrakk> \<Longrightarrow> (xs @ ys) ! i = ys ! (i - length xs)"
  by (simp add: nth_append)

lemma nth_append_take: "\<lbrakk>i < length xs\<rbrakk> \<Longrightarrow> (xs @ ys) ! i = xs ! i"
  by (simp add: nth_append)

\<comment> \<open>CARD-FILTER EQUIVALENCE: card {i < n. xs!i = x} = length(filter ((=) x) xs).\<close>
lemma card_filter_nth_eq:
  "card {i. i < length xs \<and> xs ! i = x} = length (filter ((=) x) xs)"
proof (induction xs rule: rev_induct)
  case Nil show ?case by (by100 simp)
next
  case (snoc y ys)
  have h1: "{i. i < length (ys @ [y]) \<and> (ys @ [y]) ! i = x}
      = {i. i < length ys \<and> ys ! i = x} \<union> (if y = x then {length ys} else {})"
  proof (rule set_eqI)
    fix i
    show "(i \<in> {i. i < length (ys @ [y]) \<and> (ys @ [y]) ! i = x}) =
          (i \<in> {i. i < length ys \<and> ys ! i = x} \<union> (if y = x then {length ys} else {}))"
      by (cases "i < length ys") (auto simp: nth_append)
  qed
  have h2: "length (filter ((=) x) (ys @ [y])) = length (filter ((=) x) ys) + (if y = x then 1 else 0)"
    by (by100 simp)
  have hfin: "finite {i. i < length ys \<and> ys ! i = x}" by (by100 auto)
  have hdisj: "{i. i < length ys \<and> ys ! i = x} \<inter> (if y = x then {length ys} else {}) = {}"
    by (by100 auto)
  show ?case using snoc.IH h1 h2 hfin hdisj card_Un_disjoint
    by (by100 simp)
qed

\<comment> \<open>PROPERNESS PRESERVATION under label substitution.
   If source scheme is proper (each label 0 or 2 times) and c is fresh,
   then replacing a by c preserves properness.\<close>
lemma proper_scheme_subst:
  fixes a c :: "'b" and u2 v :: "('b \<times> bool) list"
  assumes hproper: "\<forall>label. card {i. i < length ([(a, True)] @ u2 @ [(a, True)] @ v)
            \<and> fst (([(a, True)] @ u2 @ [(a, True)] @ v) ! i) = label} \<in> {0, 2}"
      and hfresh: "c \<notin> fst ` set ([(a, True)] @ u2 @ [(a, True)] @ v)"
  shows "\<forall>label. card {i. i < length ([(c, True)] @ rev (map top1_inverse_edge u2) @ v @ [(c, True)])
            \<and> fst (([(c, True)] @ rev (map top1_inverse_edge u2) @ v @ [(c, True)]) ! i) = label} \<in> {0, 2}"
proof -
  let ?w = "[(a, True)] @ u2 @ [(a, True)] @ v"
  let ?w' = "[(c, True)] @ rev (map top1_inverse_edge u2) @ v @ [(c, True)]"
  \<comment> \<open>Convert card-set to filter-length for easier reasoning.\<close>
  have hfst_inv: "map fst (rev (map top1_inverse_edge u2)) = rev (map fst u2)"
  proof -
    have "\<And>x. fst (top1_inverse_edge x) = fst x"
      unfolding top1_inverse_edge_def by (by100 auto)
    hence "map fst (map top1_inverse_edge u2) = map fst u2"
      by (induction u2) (by100 auto)+
    have "map fst (map top1_inverse_edge u2) = map fst u2"
      unfolding top1_inverse_edge_def by (induction u2) (by100 auto)+
    hence "rev (map fst (map top1_inverse_edge u2)) = rev (map fst u2)" by (by100 simp)
    moreover have "rev (map fst (map top1_inverse_edge u2)) = map fst (rev (map top1_inverse_edge u2))"
      by (rule rev_map)
    moreover have "rev (map fst u2) = map fst (rev u2)"
      by (rule rev_map)
    ultimately show ?thesis by (by100 simp)
  qed
  have hfst_w: "map fst ?w = [a] @ map fst u2 @ [a] @ map fst v" by (by100 simp)
  have hfst_w': "map fst ?w' = [c] @ rev (map fst u2) @ map fst v @ [c]"
    using hfst_inv by (by100 simp)
  have hc_ne_a: "c \<noteq> a" using hfresh by (by100 auto)
  have hc_notin_u2: "c \<notin> fst ` set u2" using hfresh by (by100 auto)
  have hc_notin_v: "c \<notin> fst ` set v" using hfresh by (by100 auto)
  \<comment> \<open>For any label l: count in source = 2*(l=a) + count\\_u2(l) + count\\_v(l).\<close>
  define cnt where "cnt l xs = length (filter (\<lambda>x. fst x = l) xs)" for l :: "'b" and xs :: "('b \<times> bool) list"
  \<comment> \<open>Bridge: card {i < n. fst(xs!i) = l} = cnt l xs.\<close>
  have hcard_cnt: "\<And>l. \<And>xs :: ('b \<times> bool) list.
      card {i. i < length xs \<and> fst (xs ! i) = l} = cnt l xs"
  proof -
    fix l and xs :: "('b \<times> bool) list"
    have "{i. i < length xs \<and> fst (xs ! i) = l} = {i. i < length (map fst xs) \<and> (map fst xs) ! i = l}"
      by (by100 auto)
    hence "card {i. i < length xs \<and> fst (xs ! i) = l} = card {i. i < length (map fst xs) \<and> (map fst xs) ! i = l}"
      by (by100 simp)
    also have "\<dots> = length (filter ((=) l) (map fst xs))"
      by (rule card_filter_nth_eq)
    also have "\<dots> = cnt l xs"
    proof -
      have "length (filter ((=) l) (map fst xs)) = length (filter (((=) l) \<circ> fst) xs)"
        by (rule length_filter_map)
      also have "(((=) l) \<circ> fst) = (\<lambda>x :: 'b \<times> bool. fst x = l)" by (by100 auto)
      finally show ?thesis unfolding cnt_def by (by100 simp)
    qed
    finally show "card {i. i < length xs \<and> fst (xs ! i) = l} = cnt l xs" .
  qed
  \<comment> \<open>Helper: filter on rev preserves length.\<close>
  have hcnt_rev: "\<And>l. \<And>xs :: ('b \<times> bool) list. cnt l (rev xs) = cnt l xs"
  proof -
    fix l and xs :: "('b \<times> bool) list"
    have "filter (\<lambda>x. fst x = l) (rev xs) = rev (filter (\<lambda>x. fst x = l) xs)"
      using rev_filter[of "\<lambda>x. fst x = l" xs] by (by100 simp)
    thus "cnt l (rev xs) = cnt l xs" unfolding cnt_def by (by100 simp)
  qed
  \<comment> \<open>Source count decomposition.\<close>
  have hcnt_w: "\<And>l. cnt l ?w = (if l = a then 1 else 0) + cnt l u2 + (if l = a then 1 else 0) + cnt l v"
    unfolding cnt_def by (by100 simp)
  \<comment> \<open>Target count decomposition.\<close>
  have hcnt_w': "\<And>l. cnt l ?w' = (if l = c then 1 else 0) + cnt l (rev (map top1_inverse_edge u2)) + cnt l v + (if l = c then 1 else 0)"
    unfolding cnt_def by (by100 simp)
  \<comment> \<open>cnt of inv(u2) = cnt of u2 (since fst preserved by inv).\<close>
  have hcnt_inv: "\<And>l. cnt l (rev (map top1_inverse_edge u2)) = cnt l u2"
  proof -
    fix l
    have "cnt l (rev (map top1_inverse_edge u2)) = cnt l (map top1_inverse_edge u2)"
      using hcnt_rev by (by100 blast)
    also have "\<dots> = cnt l u2"
      unfolding cnt_def top1_inverse_edge_def by (induction u2) (by100 auto)+
    finally show "cnt l (rev (map top1_inverse_edge u2)) = cnt l u2" .
  qed
  \<comment> \<open>Source properness via cnt.\<close>
  have hproper_cnt: "\<And>l. cnt l ?w \<in> {0, 2}"
  proof -
    fix l
    from hproper[rule_format, of l]
    have "card {i. i < length ?w \<and> fst (?w ! i) = l} \<in> {0, 2}" .
    moreover have "card {i. i < length ?w \<and> fst (?w ! i) = l} = cnt l ?w"
      using hcard_cnt .
    ultimately show "cnt l ?w \<in> {0, 2}" by (by100 simp)
  qed
  show ?thesis
  proof (rule allI)
    fix label
    have hcnt_target: "cnt label ?w' = (if label = c then 2 else 0) + cnt label u2 + cnt label v"
      using hcnt_w' hcnt_inv by (by100 simp)
    show "card {i. i < length ?w' \<and> fst (?w' ! i) = label} \<in> {0, 2}"
    proof (cases "label = c")
      case True
      have "cnt c u2 = 0" using hc_notin_u2 unfolding cnt_def
        by (induction u2) (by100 auto)+
      moreover have "cnt c v = 0" using hc_notin_v unfolding cnt_def
        by (induction v) (by100 auto)+
      ultimately have hcnt_eq: "cnt label ?w' = 2" using hcnt_target True by (by100 simp)
      have "card {i. i < length ?w' \<and> fst (?w' ! i) = label} = cnt label ?w'"
        using hcard_cnt .
      thus ?thesis using hcnt_eq by (by100 simp)
    next
      case False
      have hcnt_src: "cnt label ?w = (if label = a then 2 else 0) + cnt label u2 + cnt label v"
        using hcnt_w by (by100 simp)
      have hcnt_src_in: "cnt label ?w \<in> {0, 2}" using hproper_cnt .
      have "cnt label ?w' = cnt label u2 + cnt label v"
        using hcnt_target False by (by100 simp)
      also have "\<dots> = cnt label ?w - (if label = a then 2 else 0)"
        using hcnt_src by (by100 simp)
      finally have "cnt label ?w' = cnt label ?w - (if label = a then 2 else 0)" .
      hence "cnt label ?w' \<in> {0, 2}" using hcnt_src_in by (by100 auto)
      moreover have "card {i. i < length ?w' \<and> fst (?w' ! i) = label} = cnt label ?w'"
        using hcard_cnt .
      ultimately show ?thesis by (by100 simp)
    qed
  qed
qed

\<comment> \<open>SUB-POLYGON INCLUSION: convex hull of a subset of vertices is contained in the polygon.
   If P is a convex polygon with vertices v\\_0,...,v\\_{n-1}, then for any k+1 consecutive
   vertices v\\_0,...,v\\_k, the convex hull Q1 = {\\<Sum> c\\_i * v\\_i | i \\<le> k, c\\_i \\<ge> 0, \\<Sum> c\\_i = 1}
   is contained in P = {\\<Sum> c\\_i * v\\_i | i < n, c\\_i \\<ge> 0, \\<Sum> c\\_i = 1}.
   This is immediate: extend any convex combination over {0,...,k} to {0,...,n-1}
   by setting c\\_{k+1} = ... = c\\_{n-1} = 0.\<close>
lemma sub_polygon_in_polygon:
  fixes vx vy :: "nat \<Rightarrow> real" and n k :: nat
  assumes "k < n" "k \<ge> 2"
  shows "{(x::real,y::real). \<exists>coeffs. (\<forall>i\<le>k. coeffs i \<ge> 0)
                     \<and> (\<Sum>i\<le>k. coeffs i) = 1
                     \<and> x = (\<Sum>i\<le>k. coeffs i * vx i)
                     \<and> y = (\<Sum>i\<le>k. coeffs i * vy i)}
       \<subseteq> {(x,y). \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<n. coeffs i) = 1
                     \<and> x = (\<Sum>i<n. coeffs i * vx i)
                     \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
proof (rule subsetI)
  fix p assume "p \<in> {(x::real,y::real). \<exists>coeffs. (\<forall>i\<le>k. coeffs i \<ge> 0)
                     \<and> (\<Sum>i\<le>k. coeffs i) = 1
                     \<and> x = (\<Sum>i\<le>k. coeffs i * vx i)
                     \<and> y = (\<Sum>i\<le>k. coeffs i * vy i)}"
  then obtain x y where hp: "p = (x, y)" and "\<exists>coeffs. (\<forall>i\<le>k. coeffs i \<ge> 0)
      \<and> (\<Sum>i\<le>k. coeffs i) = 1 \<and> x = (\<Sum>i\<le>k. coeffs i * vx i) \<and> y = (\<Sum>i\<le>k. coeffs i * vy i)"
    by (by100 auto)
  then obtain coeffs where hc: "\<forall>i\<le>k. coeffs i \<ge> 0"
      and hsum: "(\<Sum>i\<le>k. coeffs i) = 1"
      and hx: "fst p = (\<Sum>i\<le>k. coeffs i * vx i)"
      and hy: "snd p = (\<Sum>i\<le>k. coeffs i * vy i)"
    using hp by (by100 auto)
  \<comment> \<open>Define extended coefficients: zero beyond k.\<close>
  define coeffs' where "coeffs' i = (if i \<le> k then coeffs i else 0)" for i
  have hc': "\<forall>i<n. coeffs' i \<ge> 0"
    using hc assms(1) unfolding coeffs'_def by (by100 auto)
  have hzero: "\<And>i. i > k \<Longrightarrow> i < n \<Longrightarrow> coeffs' i = 0" unfolding coeffs'_def by (by100 auto)
  have hsame: "\<And>i. i \<le> k \<Longrightarrow> coeffs' i = coeffs i" unfolding coeffs'_def by (by100 simp)
  have hsplit: "{..<n} = {..k} \<union> {Suc k..<n}" using assms(1) by (by100 auto)
  have hdisj: "{..k} \<inter> {Suc k..<n} = {}" by (by100 auto)
  have hsum': "(\<Sum>i<n. coeffs' i) = 1"
  proof -
    have "(\<Sum>i<n. coeffs' i) = (\<Sum>i\<in>{..k} \<union> {Suc k..<n}. coeffs' i)"
      using hsplit by (by100 simp)
    also have "\<dots> = (\<Sum>i\<le>k. coeffs' i) + (\<Sum>i\<in>{Suc k..<n}. coeffs' i)"
      using hdisj by (rule sum.union_disjoint[OF finite_atMost finite_atLeastLessThan])
    also have "(\<Sum>i\<in>{Suc k..<n}. coeffs' i) = 0"
      using hzero by (by100 simp)
    also have "(\<Sum>i\<le>k. coeffs' i) = (\<Sum>i\<le>k. coeffs i)"
      using hsame by (by100 auto)
    finally show ?thesis using hsum by (by100 simp)
  qed
  have hx': "fst p = (\<Sum>i<n. coeffs' i * vx i)"
  proof -
    have "(\<Sum>i<n. coeffs' i * vx i) = (\<Sum>i\<in>{..k} \<union> {Suc k..<n}. coeffs' i * vx i)"
      using hsplit by (by100 simp)
    also have "\<dots> = (\<Sum>i\<le>k. coeffs' i * vx i) + (\<Sum>i\<in>{Suc k..<n}. coeffs' i * vx i)"
      using hdisj by (rule sum.union_disjoint[OF finite_atMost finite_atLeastLessThan])
    also have "(\<Sum>i\<in>{Suc k..<n}. coeffs' i * vx i) = 0"
      using hzero by (by100 simp)
    also have "(\<Sum>i\<le>k. coeffs' i * vx i) = (\<Sum>i\<le>k. coeffs i * vx i)"
      using hsame by (by100 auto)
    finally show ?thesis using hx by (by100 simp)
  qed
  have hy': "snd p = (\<Sum>i<n. coeffs' i * vy i)"
  proof -
    have "(\<Sum>i<n. coeffs' i * vy i) = (\<Sum>i\<in>{..k} \<union> {Suc k..<n}. coeffs' i * vy i)"
      using hsplit by (by100 simp)
    also have "\<dots> = (\<Sum>i\<le>k. coeffs' i * vy i) + (\<Sum>i\<in>{Suc k..<n}. coeffs' i * vy i)"
      using hdisj by (rule sum.union_disjoint[OF finite_atMost finite_atLeastLessThan])
    also have "(\<Sum>i\<in>{Suc k..<n}. coeffs' i * vy i) = 0"
      using hzero by (by100 simp)
    also have "(\<Sum>i\<le>k. coeffs' i * vy i) = (\<Sum>i\<le>k. coeffs i * vy i)"
      using hsame by (by100 auto)
    finally show ?thesis using hy by (by100 simp)
  qed
  show "p \<in> {(x,y). \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<n. coeffs i) = 1
                     \<and> x = (\<Sum>i<n. coeffs i * vx i)
                     \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
    using hc' hsum' hx' hy' by (by100 auto)
qed

\<comment> \<open>DIAGONAL IN POLYGON: the line segment from v\\_0 to v\\_k is inside P.
   Follows directly from convexity of polygonal regions (polygonal\\_region\\_convex\\_combo).\<close>
lemma polygon_diagonal_in_region:
  fixes vx vy :: "nat \<Rightarrow> real" and n k :: nat
  assumes hP: "top1_is_polygonal_region_on P n" and hn: "n \<ge> 3"
    and hk: "k < n" and hk2: "k \<ge> 2"
    and hv0: "(vx 0, vy 0) \<in> P" and hvk: "(vx k, vy k) \<in> P"
    and ht: "0 \<le> t" "t \<le> 1"
  shows "((1-t) * vx 0 + t * vx k, (1-t) * vy 0 + t * vy k) \<in> P"
  using polygonal_region_convex_combo[OF hP hn hv0 hvk assms(7,8)] by simp

\<comment> \<open>EDGE PARAMETRIZATION: same-direction a-pair identification gives a continuous
   matching of the two a-edge parametrizations in the quotient.
   For t ranging over [0,1]:
     q(first\\_a(t)) = q(second\\_a(t))      [same direction, same parameter]
   After FLIP of one piece:
     q(first\\_a(1-t)) = q(second\\_a(1-t))  [reversed parameter]
   So q(first\\_a\\_flipped(t)) = q(second\\_a(1-t))
   This ensures CONTINUITY at the paste junction: the two approaching
   limits in Y agree at every parameter.\<close>

\<comment> \<open>QUOTIENT MAP EDGE IDENTIFICATION AT DIAGONAL.
   When the a-pair in scheme a@u2@a@v has same direction (both True),
   C7 gives: q(edge\\_0(t)) = q(edge\\_{1+|u2|}(t)) for all t.
   This identifies the first and second a-edge point-by-point.\<close>
lemma scheme_a_pair_identification:
  fixes a :: "'b" and u2 v :: "('b \<times> bool) list"
  assumes hq: "top1_quotient_of_scheme_on Y TY ([(a, True)] @ u2 @ [(a, True)] @ v)"
  obtains P q vx vy where
    "top1_is_polygonal_region_on P (length ([(a, True)] @ u2 @ [(a, True)] @ v))"
    "top1_quotient_map_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) Y TY q"
    "\<forall>i<length ([(a, True)] @ u2 @ [(a, True)] @ v). (vx i, vy i) \<in> P"
    "\<forall>t\<in>I_set.
       q ((1-t) * vx 0 + t * vx 1, (1-t) * vy 0 + t * vy 1)
     = q ((1-t) * vx (1 + length u2) + t * vx (Suc (1 + length u2) mod length ([(a, True)] @ u2 @ [(a, True)] @ v)),
          (1-t) * vy (1 + length u2) + t * vy (Suc (1 + length u2) mod length ([(a, True)] @ u2 @ [(a, True)] @ v)))"
proof -
  let ?w = "[(a, True)] @ u2 @ [(a, True)] @ v"
  let ?n = "length ?w"
  from quotient_of_scheme_extract_vx[OF hq]
  obtain P q vx vy where
      hC1: "top1_is_polygonal_region_on P ?n"
    and hC2: "top1_quotient_map_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) Y TY q"
    and hC4: "\<forall>i<?n. (vx i, vy i) \<in> P"
    and hC7: "\<forall>i<?n. \<forall>j<?n. fst (?w!i) = fst (?w!j) \<longrightarrow>
        (\<forall>t\<in>I_set.
           q ((1-t) * vx i + t * vx (Suc i mod ?n),
              (1-t) * vy i + t * vy (Suc i mod ?n))
         = (if snd (?w!i) = snd (?w!j)
            then q ((1-t) * vx j + t * vx (Suc j mod ?n),
                    (1-t) * vy j + t * vy (Suc j mod ?n))
            else q (t * vx j + (1-t) * vx (Suc j mod ?n),
                    t * vy j + (1-t) * vy (Suc j mod ?n))))"
    by (rule quotient_of_scheme_extract_vx[OF hq])
  \<comment> \<open>Apply C7 with i=0, j=1+|u2|.\<close>
  have h0: "0 < ?n" by (by100 simp)
  have hj: "1 + length u2 < ?n" by (by100 simp)
  have hfst: "fst (?w ! 0) = fst (?w ! (1 + length u2))"
    by (by100 simp)
  have hsnd: "snd (?w ! 0) = snd (?w ! (1 + length u2))"
    by (by100 simp)
  have hsuc0: "Suc 0 mod ?n = 1" by (by100 simp)
  have hn_ge3: "?n \<ge> 3" using quotient_scheme_length_ge3[OF hq] .
  \<comment> \<open>Suc(1+|u2|) mod n = 2+|u2| if v \\<noteq> [], = 0 if v = [].
     When v = []: n = 2+|u2|, so edge 1+|u2| wraps to vertex 0.\<close>
  from hC7[rule_format, OF h0 hj hfst]
  have hident: "\<forall>t\<in>I_set.
       q ((1-t) * vx 0 + t * vx (Suc 0 mod ?n),
          (1-t) * vy 0 + t * vy (Suc 0 mod ?n))
     = q ((1-t) * vx (1 + length u2) + t * vx (Suc (1 + length u2) mod ?n),
          (1-t) * vy (1 + length u2) + t * vy (Suc (1 + length u2) mod ?n))"
    using hsnd by (by100 simp)
  have hsuc0': "Suc 0 mod ?n = 1" using hsuc0 .
  \<comment> \<open>For the case v \\<noteq> []: Suc(1+|u2|) mod n = 2+|u2|.
     For v = []: Suc(1+|u2|) mod n = 0 (wrap around).
     In both cases, derive the identification.\<close>
  have hident': "\<forall>t\<in>I_set.
       q ((1-t) * vx 0 + t * vx 1, (1-t) * vy 0 + t * vy 1)
     = q ((1-t) * vx (1 + length u2) + t * vx (Suc (1 + length u2) mod ?n),
          (1-t) * vy (1 + length u2) + t * vy (Suc (1 + length u2) mod ?n))"
    using hident hsuc0' by (by100 simp)
  show ?thesis using hC1 hC2 hC4 hident' by (rule that)
qed

\<comment> \<open>POLYGON PASTE ALONG SHARED EDGE (Munkres Theorem 76.1 core geometric fact).
   Given two disjoint polygonal regions Q1 (scheme w1) and Q2 (scheme w2) where:
   - Q1 has an edge labeled (a,F) at its last position
   - Q2 has an edge labeled (a,T) at its first position
   - label a appears nowhere else in w1 or w2
   Then pasting Q1 and Q2 along the a-edges gives a single polygon P with scheme
   (w1 minus last) @ (w2 minus first), and the quotient of P under this scheme
   (with remaining identifications) gives the same space as the two-polygon quotient.

   This is the GEOMETRIC HEART of Theorem 76.1. The proof uses:
   1. The pasted polygon P = Q1 \\<union>\\_{a-edges} Q2 is a valid polygonal region
   2. The quotient map factors: Q1 \\<squnion> Q2 \\<to> P \\<to> Y (composition of quotient maps)
   3. Applying top1\\_quotient\\_map\\_on\\_comp.\<close>

\<comment> \<open>THEOREM 76.1 PASTE (simplified for the cut-paste application).
   Given polygon P with scheme y0@y1 and quotient Y:
   - CUT P along diagonal from v\\_0 to v\\_{|y0|} into Q1 and Q2
   - The quotient of Q1 \\<squnion> Q2 (identifying all labels including c on the diagonal) = Y
   - Per-polygon operations on Q1 and Q2 preserve the quotient Y
   - PASTE Q1 and Q2 along a DIFFERENT shared edge gives a new polygon
     whose quotient under the combined scheme = Y

   The full chain: CUT \\<to> per-polygon ops \\<to> PASTE preserves the quotient space.
   This is the content of Munkres Theorem 76.1.

   Formal statement: if Y is quotient of [(a,T)]@u2@[(a,T)]@v, then
   Y is ALSO quotient of [(c,T)]@inv(u2)@v@[(c,T)] (for any fresh c).
   The proof constructs a new polygon P' and quotient map q': P' \\<to> Y
   via the CUT+FLIP+PASTE chain, using top1\\_quotient\\_map\\_on\\_comp.\<close>
\<comment> \<open>The same-space claim IS CORRECT when all vertices are in one equivalence class
   (one vertex class), which is the standard condition in the book's classification proof.
   Under one vertex class: v\\_0, v\\_1, v\\_{1+|u2|}, v\\_{2+|u2|} are ALL identified in Y,
   so the paste identification (v\\_0 \\<leftrightarrow> v\\_{2+|u2|}, v\\_1 \\<leftrightarrow> v\\_{1+|u2|}) doesn't create
   any NEW identifications beyond what Y already has.
   Without one vertex class: the paste may create coarser identifications.\<close>

\<comment> \<open>Helper: label at position i in the target scheme w' = c@inv(u2)@v@c.\<close>
lemma paste_chain_target_label:
  fixes a c :: "'b" and u2 v :: "('b \<times> bool) list"
  defines "w \<equiv> [(a, True)] @ u2 @ [(a, True)] @ v"
  defines "w' \<equiv> [(c, True)] @ rev (map top1_inverse_edge u2) @ v @ [(c, True)]"
  assumes "length w = length w'"
  shows "length w' = length w"
    and "i < length w' \<Longrightarrow> i = 0 \<Longrightarrow> fst (w' ! i) = c \<and> snd (w' ! i) = True"
    and "i < length w' \<Longrightarrow> i = length w' - 1 \<Longrightarrow> length w' \<ge> 2 \<Longrightarrow>
         fst (w' ! i) = c \<and> snd (w' ! i) = True"
    and "i < length w' \<Longrightarrow> 1 \<le> i \<Longrightarrow> i \<le> length u2 \<Longrightarrow>
         fst (w' ! i) = fst (u2 ! (length u2 - i)) \<and>
         snd (w' ! i) = (\<not> snd (u2 ! (length u2 - i)))"
    and "i < length w' \<Longrightarrow> length u2 + 1 \<le> i \<Longrightarrow> i \<le> length w' - 2 \<Longrightarrow>
         fst (w' ! i) = fst (v ! (i - length u2 - 1)) \<and>
         snd (w' ! i) = snd (v ! (i - length u2 - 1))"
proof -
  show "length w' = length w" using assms(3) by simp
next
  assume "i < length w'" "i = 0"
  thus "fst (w' ! i) = c \<and> snd (w' ! i) = True" unfolding w'_def by (by100 simp)
next
  assume hi: "i < length w'" and hlast: "i = length w' - 1" and hge: "length w' \<ge> 2"
  have "w' \<noteq> []" using hge unfolding w'_def by (by100 simp)
  hence "last w' = w' ! (length w' - 1)" using last_conv_nth by (by100 blast)
  hence "w' ! i = last w'" using hlast by simp
  moreover have "last w' = (c, True)" unfolding w'_def by (by100 simp)
  ultimately show "fst (w' ! i) = c \<and> snd (w' ! i) = True" by (by100 simp)
next
  assume hi: "i < length w'" and h1: "1 \<le> i" and hk: "i \<le> length u2"
  have hiu: "i - 1 < length u2" using h1 hk by (by100 linarith)
  have "w' ! i = ([(c, True)] @ (rev (map top1_inverse_edge u2) @ v @ [(c, True)])) ! i"
    unfolding w'_def by simp
  also have "\<dots> = (rev (map top1_inverse_edge u2) @ v @ [(c, True)]) ! (i - 1)"
    using h1 by simp
  also have "\<dots> = rev (map top1_inverse_edge u2) ! (i - 1)"
  proof -
    have "i - 1 < length (rev (map top1_inverse_edge u2))" using hiu by simp
    thus ?thesis
      apply (simp only: nth_append)
      apply (by100 simp)
      done
  qed
  finally have "w' ! i = rev (map top1_inverse_edge u2) ! (i - 1)" .
  also have "\<dots> = (map top1_inverse_edge u2) ! (length (map top1_inverse_edge u2) - Suc (i - 1))"
  proof -
    have "i - 1 < length (map top1_inverse_edge u2)" using hiu by (by100 simp)
    from rev_nth[OF this] show ?thesis .
  qed
  also have "length (map top1_inverse_edge u2) - Suc (i - 1) = length u2 - i"
    using h1 hk by (by100 simp)
  also have "(map top1_inverse_edge u2) ! (length u2 - i) = top1_inverse_edge (u2 ! (length u2 - i))"
  proof (rule nth_map)
    show "length u2 - i < length u2" using h1 hk by (by100 linarith)
  qed
  finally have heq: "w' ! i = top1_inverse_edge (u2 ! (length u2 - i))" .
  show "fst (w' ! i) = fst (u2 ! (length u2 - i)) \<and> snd (w' ! i) = (\<not> snd (u2 ! (length u2 - i)))"
  proof -
    obtain l b where hlb: "u2 ! (length u2 - i) = (l, b)" by (cases "u2 ! (length u2 - i)")
    have "top1_inverse_edge (l, b) = (l, \<not>b)" unfolding top1_inverse_edge_def by simp
    with heq hlb show ?thesis by simp
  qed
next
  assume hi: "i < length w'" and hlo: "length u2 + 1 \<le> i" and hhi: "i \<le> length w' - 2"
  have hlen_rev: "length (rev (map top1_inverse_edge u2)) = length u2" by (by100 simp)
  have hlen_w': "length w' = 2 + length u2 + length v" unfolding w'_def by (by100 simp)
  have hoff: "i - 1 - length u2 < length v"
    using hlo hhi hlen_w' by (by100 linarith)
  have hoff2: "i - 1 \<ge> length u2" using hlo by (by100 linarith)
  have "w' ! i = (rev (map top1_inverse_edge u2) @ v @ [(c, True)]) ! (i - 1)"
    unfolding w'_def using hlo by (by100 simp)
  also have "\<dots> = (v @ [(c, True)]) ! (i - 1 - length u2)"
    using hoff2 hlen_rev
    apply (simp only: nth_append)
    apply (by100 simp)
    done
  also have "\<dots> = v ! (i - 1 - length u2)"
    using hoff
    apply (simp only: nth_append)
    apply (by100 simp)
    done
  finally have "w' ! i = v ! (i - 1 - length u2)" .
  moreover have "i - 1 - length u2 = i - length u2 - 1" by (by100 linarith)
  ultimately show "fst (w' ! i) = fst (v ! (i - length u2 - 1)) \<and> snd (w' ! i) = snd (v ! (i - length u2 - 1))"
    by simp
qed

\<comment> \<open>Helper: nth of append when index is in the first list.\<close>
lemma nth_append_first: "n < length xs \<Longrightarrow> (xs @ ys) ! n = xs ! n"
  by (simp add: nth_append)

\<comment> \<open>Helper: nth of append when index is in the second list.\<close>
lemma nth_append_second: "n \<ge> length xs \<Longrightarrow> (xs @ ys) ! n = ys ! (n - length xs)"
  by (simp add: nth_append)

\<comment> \<open>DEFINITION: the boundary edge-correspondence map for the paste chain.
   Maps target edge (i, t) coordinates to a point in the ORIGINAL polygon P.
   This is the key ingredient of the quotient map g = q2 o sigma.\<close>
definition paste_chain_sigma_x ::
  "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real" where
  "paste_chain_sigma_x vx k n i t =
     (if i = 0 \<or> i = n - 1
      then (1-t)*vx 0 + t*vx k
      else if i \<le> k - 1
      then t*vx(k-i) + (1-t)*vx(k+1-i)
      else (1-t)*vx(i+1) + t*vx(Suc(i+1) mod n))"

definition paste_chain_sigma_y ::
  "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real" where
  "paste_chain_sigma_y vy k n i t =
     (if i = 0 \<or> i = n - 1
      then (1-t)*vy 0 + t*vy k
      else if i \<le> k - 1
      then t*vy(k-i) + (1-t)*vy(k+1-i)
      else (1-t)*vy(i+1) + t*vy(Suc(i+1) mod n))"

\<comment> \<open>Abbreviation: sigma maps target edge (i,t) to a point in P.\<close>
abbreviation paste_sigma where
  "paste_sigma vx vy k n i t \<equiv>
     (paste_chain_sigma_x vx k n i t, paste_chain_sigma_y vy k n i t)"

\<comment> \<open>DEFINITION: the new quotient map g = q2 composed with sigma on boundary edges.
   g(edge'(i, t)) = q2(sigma(i, t)). Interior: to be extended separately.\<close>

\<comment> \<open>KEY LEMMA: sigma on inv(u2) edges equals original edge at reversed parameter.
   sigma(i, t) for 1 <= i <= k-1 = edge\\_orig(k-i, 1-t).\<close>
lemma paste_sigma_inv_u2_edge:
  fixes vx vy :: "nat \<Rightarrow> real" and k n i :: nat and t :: real
  assumes "1 \<le> i" "i \<le> k - 1" "k \<ge> 2" "n \<ge> 3" "k < n"
      and "Suc (k - i) mod n = k + 1 - i"
  shows "paste_chain_sigma_x vx k n i t = (1-(1-t))*vx(k-i) + (1-t)*vx(k+1-i)"
    and "paste_chain_sigma_y vy k n i t = (1-(1-t))*vy(k-i) + (1-t)*vy(k+1-i)"
proof -
  from assms have "i \<noteq> 0" "i \<noteq> n - 1" "i \<le> k - 1" by linarith+
  thus "paste_chain_sigma_x vx k n i t = (1-(1-t))*vx(k-i) + (1-t)*vx(k+1-i)"
    unfolding paste_chain_sigma_x_def by simp
  from \<open>i \<noteq> 0\<close> \<open>i \<noteq> n - 1\<close> \<open>i \<le> k - 1\<close>
  show "paste_chain_sigma_y vy k n i t = (1-(1-t))*vy(k-i) + (1-t)*vy(k+1-i)"
    unfolding paste_chain_sigma_y_def by simp
qed

\<comment> \<open>KEY LEMMA: sigma on v edges equals original edge at same parameter.
   sigma(i, t) for k <= i <= n-2 = edge\\_orig(i+1, t).\<close>
lemma paste_sigma_v_edge:
  fixes vx vy :: "nat \<Rightarrow> real" and k n i :: nat and t :: real
  assumes "k \<le> i" "i \<le> n - 2" "k \<ge> 1" "n \<ge> 3"
  shows "paste_chain_sigma_x vx k n i t = (1-t)*vx(i+1) + t*vx(Suc(i+1) mod n)"
    and "paste_chain_sigma_y vy k n i t = (1-t)*vy(i+1) + t*vy(Suc(i+1) mod n)"
proof -
  from assms have "i \<noteq> 0" "i \<noteq> n - 1" "\<not>(i \<le> k - 1)" by linarith+
  thus "paste_chain_sigma_x vx k n i t = (1-t)*vx(i+1) + t*vx(Suc(i+1) mod n)"
    unfolding paste_chain_sigma_x_def by simp
  from \<open>i \<noteq> 0\<close> \<open>i \<noteq> n - 1\<close> \<open>\<not>(i \<le> k - 1)\<close>
  show "paste_chain_sigma_y vy k n i t = (1-t)*vy(i+1) + t*vy(Suc(i+1) mod n)"
    unfolding paste_chain_sigma_y_def by simp
qed

\<comment> \<open>KEY LEMMA: sigma on c-edges (i=0 or i=n-1) equals diagonal point.
   sigma(0, t) = sigma(n-1, t) = ((1-t)*vx 0 + t*vx k, ...).\<close>
lemma paste_sigma_c_edge:
  fixes vx vy :: "nat \<Rightarrow> real" and k n :: nat and t :: real
  assumes "n \<ge> 3"
  shows "paste_chain_sigma_x vx k n 0 t = (1-t)*vx 0 + t*vx k"
    and "paste_chain_sigma_y vy k n 0 t = (1-t)*vy 0 + t*vy k"
    and "paste_chain_sigma_x vx k n (n-1) t = (1-t)*vx 0 + t*vx k"
    and "paste_chain_sigma_y vy k n (n-1) t = (1-t)*vy 0 + t*vy k"
  unfolding paste_chain_sigma_x_def paste_chain_sigma_y_def
  using assms by simp_all

\<comment> \<open>BOUNDARY C7 for the target scheme: the key algebraic lemma.
   Shows that q2 composed with sigma satisfies C7 for the target scheme w'.
   The proof is pure index arithmetic + the original C7 for the source scheme w.
   Cases: c-pair (trivial), inv(u2) pair (double negation), v pair (direct),
   cross pair inv(u2)-v (double negation), c vs non-c (impossible by freshness).\<close>
lemma paste_chain_boundary_C7:
  fixes a c :: "'b" and u2 v :: "('b \<times> bool) list"
    and vx vy :: "nat \<Rightarrow> real" and q2 :: "real \<times> real \<Rightarrow> 'a"
  defines "w \<equiv> [(a, True)] @ u2 @ [(a, True)] @ v"
  defines "w' \<equiv> [(c, True)] @ rev (map top1_inverse_edge u2) @ v @ [(c, True)]"
  defines "k \<equiv> 1 + length u2"
  defines "\<sigma> \<equiv> \<lambda>i t. paste_sigma vx vy k (length w) i t"
  assumes hlen3: "length w \<ge> 3"
      and hfresh: "c \<notin> fst ` set w"
      and hC7_orig: "\<forall>i<length w. \<forall>j<length w. fst (w!i) = fst (w!j) \<longrightarrow>
          (\<forall>t\<in>I_set. q2 ((1-t)*vx i + t*vx(Suc i mod length w),
                          (1-t)*vy i + t*vy(Suc i mod length w))
           = (if snd(w!i) = snd(w!j)
              then q2 ((1-t)*vx j + t*vx(Suc j mod length w),
                        (1-t)*vy j + t*vy(Suc j mod length w))
              else q2 (t*vx j + (1-t)*vx(Suc j mod length w),
                        t*vy j + (1-t)*vy(Suc j mod length w))))"
  shows "\<forall>i<length w'. \<forall>j<length w'. fst (w'!i) = fst (w'!j) \<longrightarrow>
      (\<forall>t\<in>I_set. q2 (\<sigma> i t)
       = (if snd(w'!i) = snd(w'!j)
          then q2 (\<sigma> j t)
          else q2 (\<sigma> j (1-t))))"
proof (intro allI impI ballI)
  fix i j t
  assume hi: "i < length w'" and hj: "j < length w'"
    and hlabel: "fst (w'!i) = fst (w'!j)" and ht: "t \<in> I_set"
  let ?n = "length w"
  have hlen: "length w' = ?n" unfolding w_def w'_def by (by100 simp)
  have hn3: "?n \<ge> 3" using hlen3 by simp
  have hk_eq: "k = Suc (length u2)" unfolding k_def by simp
  have hk_pos: "k \<ge> 1" unfolding k_def by simp
  have hk_lt: "k < ?n" unfolding w_def k_def by (by100 simp)
  \<comment> \<open>Freshness consequences.\<close>
  have hc_ne_a: "c \<noteq> a" using hfresh unfolding w_def by (by100 auto)
  have hc_not_u2: "c \<notin> fst ` set u2" using hfresh unfolding w_def by (by100 auto)
  have hc_not_v: "c \<notin> fst ` set v" using hfresh unfolding w_def by (by100 auto)
  \<comment> \<open>Target label at middle positions (1..n-2) is never c.\<close>
  have hfst_mid_ne_c: "\<And>m. 1 \<le> m \<Longrightarrow> m \<le> ?n - 2 \<Longrightarrow> fst (w'!m) \<noteq> c"
  proof -
    fix m assume hm1: "(1::nat) \<le> m" and hm2: "m \<le> ?n - 2"
    \<comment> \<open>m is in the middle of w'. w' = [c] @ rev(inv u2) @ v @ [c].
       Middle positions 1..n-2 have labels from inv(u2) or v, not c.\<close>
    have "fst (w'!m) \<in> fst ` set (rev (map top1_inverse_edge u2) @ v)"
    proof -
      let ?mid = "rev (map top1_inverse_edge u2) @ v"
      have hlen_mid: "length ?mid = length u2 + length v" by (by100 simp)
      have hlen_n: "?n = 2 + length u2 + length v" unfolding w_def by (by100 simp)
      have hm1_lt: "m - 1 < length ?mid" using hm1 hm2 hlen_mid hlen_n by (by100 linarith)
      have h1: "w'!m = (?mid @ [(c, True)])!(m - 1)"
        unfolding w'_def using hm1 by (by100 simp)
      have h2: "(?mid @ [(c, True)])!(m - 1) = ?mid!(m - 1)"
        by (rule nth_append_first[OF hm1_lt])
      have h3: "?mid!(m - 1) \<in> set ?mid" using nth_mem[OF hm1_lt] .
      from h1 h2 h3 show ?thesis by (by100 auto)
    qed
    moreover have "c \<notin> fst ` set (rev (map top1_inverse_edge u2) @ v)"
    proof -
      have "fst ` set (rev (map top1_inverse_edge u2)) = fst ` set u2"
        unfolding top1_inverse_edge_def by (by100 force)
      hence "fst ` set (rev (map top1_inverse_edge u2) @ v) = fst ` set u2 \<union> fst ` set v"
        by (by100 auto)
      with hc_not_u2 hc_not_v show ?thesis by (by100 blast)
    qed
    ultimately show "fst (w'!m) \<noteq> c" by (by100 blast)
  qed
  \<comment> \<open>Case split: is i a c-edge (0 or n-1) or a middle edge (1..n-2)?\<close>
  show "q2 (\<sigma> i t) = (if snd(w'!i) = snd(w'!j)
          then q2 (\<sigma> j t) else q2 (\<sigma> j (1-t)))"
  proof (cases "i = 0 \<or> i = ?n - 1")
    case True
    \<comment> \<open>i is a c-edge. Label = c. Since c fresh, j must also be c-edge.\<close>
    have hfst_i_c: "fst (w'!i) = c"
    proof (cases "i = 0")
      case True thus ?thesis unfolding w'_def by (by100 simp)
    next
      case False
      with True have hi_last: "i = ?n - 1" by simp
      have "w' \<noteq> []" using hn3 hlen by (by100 auto)
      hence "w'!i = last w'" using hi_last hlen last_conv_nth[of w'] by (by100 simp)
      moreover have "last w' = (c, True)" unfolding w'_def by (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    have hfst_j_c: "fst (w'!j) = c" using hlabel hfst_i_c by simp
    have hj_c: "j = 0 \<or> j = ?n - 1"
    proof (rule ccontr)
      assume "\<not>(j = 0 \<or> j = ?n - 1)"
      hence "1 \<le> j" "j \<le> ?n - 2" using hj hlen by linarith+
      from hfst_mid_ne_c[OF this] hfst_j_c show False by simp
    qed
    \<comment> \<open>Both c-edges: sigma(0,t) = sigma(n-1,t) (same diagonal).\<close>
    have h\<sigma>_eq: "\<sigma> i t = \<sigma> j t"
    proof -
      from True hj_c
      show ?thesis
        unfolding \<sigma>_def paste_chain_sigma_x_def paste_chain_sigma_y_def
        by (by100 auto)
    qed
    have hsnd_eq: "snd(w'!i) = snd(w'!j)"
    proof -
      have "snd(w'!i) = True"
      proof (cases "i = 0")
        case True thus ?thesis unfolding w'_def by (by100 simp)
      next
        case False
        with \<open>i = 0 \<or> i = ?n - 1\<close> have "i = ?n - 1" by simp
        have "w' \<noteq> []" using hn3 hlen by (by100 auto)
        hence "w'!i = last w'" using \<open>i = ?n - 1\<close> hlen last_conv_nth[of w'] by (by100 simp)
        moreover have "last w' = (c, True)" unfolding w'_def by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      moreover have "snd(w'!j) = True"
      proof (cases "j = 0")
        case True thus ?thesis unfolding w'_def by (by100 simp)
      next
        case False
        with hj_c have "j = ?n - 1" by simp
        have "w' \<noteq> []" using hn3 hlen by (by100 auto)
        hence "w'!j = last w'" using \<open>j = ?n - 1\<close> hlen last_conv_nth[of w'] by (by100 simp)
        moreover have "last w' = (c, True)" unfolding w'_def by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      ultimately show ?thesis by simp
    qed
    thus ?thesis using h\<sigma>_eq hsnd_eq by (by100 simp)
  next
    case False
    \<comment> \<open>i is a middle edge (1..n-2). Label \\<noteq> c. So j is also middle.\<close>
    have hi_mid: "1 \<le> i" "i \<le> ?n - 2" using hi hlen False by linarith+
    have hfst_i_ne_c: "fst (w'!i) \<noteq> c" using hfst_mid_ne_c[OF hi_mid] .
    have hfst_j_ne_c: "fst (w'!j) \<noteq> c" using hlabel hfst_i_ne_c by simp
    have hj_not_c: "j \<noteq> 0 \<and> j \<noteq> ?n - 1"
    proof (intro conjI)
      show "j \<noteq> 0"
      proof
        assume "j = 0" hence "fst (w'!j) = c" unfolding w'_def by (by100 simp)
        with hfst_j_ne_c show False by simp
      qed
      show "j \<noteq> ?n - 1"
      proof
        assume "j = ?n - 1"
        have "w' \<noteq> []" using hn3 hlen by (by100 auto)
        hence "w'!j = last w'" using \<open>j = ?n - 1\<close> hlen last_conv_nth[of w'] by (by100 simp)
        moreover have "last w' = (c, True)" unfolding w'_def by (by100 simp)
        ultimately have "fst (w'!j) = c" by (by100 simp)
        with hfst_j_ne_c show False by simp
      qed
    qed
    have hj_mid: "1 \<le> j" "j \<le> ?n - 2" using hj hlen hj_not_c by linarith+
    \<comment> \<open>Both middle edges. Further case split: inv(u2) range or v range.\<close>
    \<comment> \<open>The boundary between inv(u2) and v ranges is at position k = 1 + length u2.
       inv(u2): positions 1..k-1 = 1..length u2.
       v: positions k..n-2 = (length u2 + 1)..n-2.\<close>
    show ?thesis
    proof (cases "i \<le> length u2 \<and> j \<le> length u2")
      case True
      \<comment> \<open>CASE: both in inv(u2) range.\<close>
      \<comment> \<open>sigma(i,t) = edge\\_orig(k-i, 1-t), sigma(j,t) = edge\\_orig(k-j, 1-t).
         Original C7 at indices (k-i), (k-j) with param (1-t) gives the result.
         The double negation: reversed param (1-t) + flipped exponent (\\<not>snd) cancel.\<close>
      \<comment> \<open>Both i,j in inv(u2) range: i,j \\<le> length u2.
         sigma(i,t) = edge\\_orig(k-i, 1-t). sigma(j,t) = edge\\_orig(k-j, 1-t).
         Target label w'!i = inv of w!(k-i), so fst same, snd flipped.
         Original C7 at (k-i),(k-j) with param (1-t) + double negation gives result.\<close>
      have hii: "i \<le> length u2" and hjj: "j \<le> length u2" using True by simp_all
      \<comment> \<open>sigma(i,t) = (t*vx(k-i)+(1-t)*vx(k+1-i), ...).\<close>
      \<comment> \<open>sigma(i,t) = ((1-(1-t))*vx(k-i) + (1-t)*vx(k+1-i), ...) = (t*vx(k-i) + (1-t)*vx(k+1-i), ...).\<close>
      have hii_k: "i \<le> k - 1" using hii hk_eq by linarith
      have hjj_k: "j \<le> k - 1" using hjj hk_eq by linarith
      have hk2: "k \<ge> 2" using hi_mid(1) hii_k by linarith
      have h\<sigma>i: "\<sigma> i t = (t*vx(k-i)+(1-t)*vx(k+1-i), t*vy(k-i)+(1-t)*vy(k+1-i))"
      proof -
        have "Suc (k - i) mod ?n = k + 1 - i"
          using hi_mid(1) hii_k hk_lt by (by100 simp)
        from paste_sigma_inv_u2_edge(1)[OF hi_mid(1) hii_k hk2 hn3 hk_lt this]
             paste_sigma_inv_u2_edge(2)[OF hi_mid(1) hii_k hk2 hn3 hk_lt this]
        show ?thesis unfolding \<sigma>_def by (by100 simp)
      qed
      have h\<sigma>j: "\<sigma> j t = (t*vx(k-j)+(1-t)*vx(k+1-j), t*vy(k-j)+(1-t)*vy(k+1-j))"
      proof -
        have "Suc (k - j) mod ?n = k + 1 - j"
          using hj_mid(1) hjj_k hk_lt by (by100 simp)
        from paste_sigma_inv_u2_edge(1)[OF hj_mid(1) hjj_k hk2 hn3 hk_lt this]
             paste_sigma_inv_u2_edge(2)[OF hj_mid(1) hjj_k hk2 hn3 hk_lt this]
        show ?thesis unfolding \<sigma>_def by (by100 simp)
      qed
      \<comment> \<open>Rewrite: sigma(i,t) = edge\\_orig(k-i) at param (1-t).\<close>
      \<comment> \<open>edge\\_orig(m, s) = (1-s)*vx(m) + s*vx(Suc m mod n), similarly y.\<close>
      \<comment> \<open>At s=1-t: (1-(1-t))*vx(m) + (1-t)*vx(Suc m mod n) = t*vx(m)+(1-t)*vx(Suc m mod n).\<close>
      \<comment> \<open>So sigma(i,t) = edge\\_orig(k-i, 1-t) when Suc(k-i) mod n = k+1-i.\<close>
      \<comment> \<open>Original C7 at (k-i, k-j): fst(w!(k-i)) = fst(w!(k-j)) from hlabel + label correspondence.\<close>
      have hki_lt: "k-i < ?n" using hii_k hk_lt by (by100 linarith)
      have hkj_lt: "k-j < ?n" using hjj_k hk_lt by (by100 linarith)
      \<comment> \<open>Label correspondence: fst(w'!i) = fst(u2!(k-1-i)) and fst(w!(k-i)) = fst(u2!(k-i-1)).
         Since k = 1+|u2|: k-i-1 = |u2|-i = k-1-i. Both equal fst(u2!(|u2|-i)).\<close>
      have hlabel_orig: "fst(w!(k-i)) = fst(w!(k-j))"
      proof -
        \<comment> \<open>w!(k-i) is in the u2 block. Position k-i in w = [(a,T)]@u2@[(a,T)]@v.
           k-i \\<ge> 1 (from i \\<le> k-1 and k \\<ge> 2) and k-i \\<le> k-1 < k = 1+|u2|.
           So w!(k-i) = ([(a,T)]@u2@[(a,T)]@v)!(k-i) = u2!(k-i-1).
           Similarly fst(w'!i) = fst(u2!(k-1-i)) via rev(inv u2).
           And k-i-1 = k-1-i. So fst(w!(k-i)) = fst(u2!(k-1-i)) = fst(w'!i).\<close>
        have hki_ge1: "k - i \<ge> 1" using hii_k hk2 by linarith
        have hki_le: "k - i \<le> length u2" using hi_mid(1) hk_eq by (by100 simp)
        have hwki: "w!(k-i) = u2!(k-i-1)"
        proof -
          have "w!(k-i) = (u2 @ [(a, True)] @ v)!(k-i-1)"
            unfolding w_def using \<open>k-i \<ge> 1\<close> by (by100 simp)
          also have "k-i-1 < length u2" using \<open>k-i \<le> length u2\<close> \<open>k-i \<ge> 1\<close> by linarith
          hence "(u2 @ [(a, True)] @ v)!(k-i-1) = u2!(k-i-1)"
            by (rule nth_append_first)
          finally show ?thesis .
        qed
        have hwkj: "w!(k-j) = u2!(k-j-1)"
        proof -
          have "k - j \<ge> 1" using hjj_k hk2 by linarith
          have "k - j \<le> length u2" using hj_mid(1) hk_eq by (by100 simp)
          have "w!(k-j) = (u2 @ [(a, True)] @ v)!(k-j-1)"
            unfolding w_def using \<open>k-j \<ge> 1\<close> by (by100 simp)
          also have "k-j-1 < length u2" using \<open>k-j \<le> length u2\<close> \<open>k-j \<ge> 1\<close> by linarith
          hence "(u2 @ [(a, True)] @ v)!(k-j-1) = u2!(k-j-1)"
            by (rule nth_append_first)
          finally show ?thesis .
        qed
        \<comment> \<open>Similarly for w'!i and w'!j via rev(inv u2).\<close>
        have hw'i: "fst(w'!i) = fst(u2!(k-1-i))"
        proof -
          let ?rivu = "rev (map top1_inverse_edge u2)"
          have h2: "i - 1 < length ?rivu" using hii hi_mid(1) by (by100 simp)
          have s1: "w'!i = ?rivu!(i-1)"
            using nth_append_first[OF h2] unfolding w'_def using hi_mid(1) by (by100 simp)
          have h4: "i - 1 < length (map top1_inverse_edge u2)" using h2 by (by100 simp)
          have s2: "?rivu!(i-1) = (map top1_inverse_edge u2)!(length (map top1_inverse_edge u2) - Suc(i-1))"
            using h4 by (rule rev_nth)
          have s3: "length (map top1_inverse_edge u2) - Suc(i-1) = length u2 - i"
            using hi_mid(1) hii by (by100 simp)
          have s4: "length u2 - i < length u2" using hi_mid(1) hii by (by100 linarith)
          have s5: "(map top1_inverse_edge u2)!(length u2 - i) = top1_inverse_edge (u2!(length u2 - i))"
            using s4 by (by100 simp)
          have s6: "fst (top1_inverse_edge (u2!(length u2 - i))) = fst (u2!(length u2 - i))"
            unfolding top1_inverse_edge_def by (cases "u2!(length u2 - i)") simp
          have s7: "length u2 - i = k - 1 - i" using hk_eq by (by100 simp)
          from s1 s2 s3 s5 s6 s7 show ?thesis by simp
        qed
        have hw'j: "fst(w'!j) = fst(u2!(k-1-j))"
        proof -
          let ?rivu = "rev (map top1_inverse_edge u2)"
          have h2: "j - 1 < length ?rivu" using hjj hj_mid(1) by (by100 simp)
          have s1: "w'!j = ?rivu!(j-1)"
            using nth_append_first[OF h2] unfolding w'_def using hj_mid(1) by (by100 simp)
          have h4: "j - 1 < length (map top1_inverse_edge u2)" using h2 by (by100 simp)
          have s2: "?rivu!(j-1) = (map top1_inverse_edge u2)!(length (map top1_inverse_edge u2) - Suc(j-1))"
            using h4 by (rule rev_nth)
          have s3: "length (map top1_inverse_edge u2) - Suc(j-1) = length u2 - j"
            using hj_mid(1) hjj by (by100 simp)
          have s4: "length u2 - j < length u2" using hj_mid(1) hjj by (by100 linarith)
          have s5: "(map top1_inverse_edge u2)!(length u2 - j) = top1_inverse_edge (u2!(length u2 - j))"
            using s4 by (by100 simp)
          have s6: "fst (top1_inverse_edge (u2!(length u2 - j))) = fst (u2!(length u2 - j))"
            unfolding top1_inverse_edge_def by (cases "u2!(length u2 - j)") simp
          have s7: "length u2 - j = k - 1 - j" using hk_eq by (by100 simp)
          from s1 s2 s3 s5 s6 s7 show ?thesis by simp
        qed
        have "k-i-1 = k-1-i" using hi_mid(1) hii_k by linarith
        have "k-j-1 = k-1-j" using hj_mid(1) hjj_k by linarith
        from hlabel hw'i hw'j hwki hwkj \<open>k-i-1 = k-1-i\<close> \<open>k-j-1 = k-1-j\<close>
        show ?thesis by simp
      qed
      \<comment> \<open>Need 1-t \\<in> I\\_set.\<close>
      have ht_1mt: "1-t \<in> I_set" using ht unfolding top1_unit_interval_def by (by100 auto)
      from hC7_orig[rule_format, OF hki_lt hkj_lt hlabel_orig ht_1mt]
      have hC7_app: "q2 ((1-(1-t))*vx(k-i) + (1-t)*vx(Suc(k-i) mod ?n),
                          (1-(1-t))*vy(k-i) + (1-t)*vy(Suc(k-i) mod ?n))
        = (if snd(w!(k-i)) = snd(w!(k-j))
           then q2 ((1-(1-t))*vx(k-j) + (1-t)*vx(Suc(k-j) mod ?n),
                     (1-(1-t))*vy(k-j) + (1-t)*vy(Suc(k-j) mod ?n))
           else q2 ((1-t)*vx(k-j) + (1-(1-t))*vx(Suc(k-j) mod ?n),
                     (1-t)*vy(k-j) + (1-(1-t))*vy(Suc(k-j) mod ?n)))" .
      \<comment> \<open>Assembly: translate hC7\\_app to target scheme via sigma, Suc mod, double negation.\<close>
      have hsuci: "Suc (k-i) mod ?n = k+1-i"
        using hi_mid(1) hii_k hk_lt by (by100 simp)
      have hsucj: "Suc (k-j) mod ?n = k+1-j"
        using hj_mid(1) hjj_k hk_lt by (by100 simp)
      have hLHS: "q2 (\<sigma> i t) = q2 ((1-(1-t))*vx(k-i) + (1-t)*vx(Suc(k-i) mod ?n),
                                     (1-(1-t))*vy(k-i) + (1-t)*vy(Suc(k-i) mod ?n))"
        using h\<sigma>i hsuci by (by100 simp)
      have hTHEN: "q2 (\<sigma> j t) = q2 ((1-(1-t))*vx(k-j) + (1-t)*vx(Suc(k-j) mod ?n),
                                       (1-(1-t))*vy(k-j) + (1-t)*vy(Suc(k-j) mod ?n))"
        using h\<sigma>j hsucj by (by100 simp)
      have hELSE: "q2 (\<sigma> j (1-t)) = q2 ((1-t)*vx(k-j) + (1-(1-t))*vx(Suc(k-j) mod ?n),
                                           (1-t)*vy(k-j) + (1-(1-t))*vy(Suc(k-j) mod ?n))"
      proof -
        have "paste_chain_sigma_x vx k ?n j (1-t) = (1-(1-(1-t)))*vx(k-j) + (1-(1-t))*vx(k+1-j)"
          using paste_sigma_inv_u2_edge(1)[OF hj_mid(1) hjj_k hk2 hn3 hk_lt hsucj] by simp
        hence hx: "paste_chain_sigma_x vx k ?n j (1-t) = (1-t)*vx(k-j) + t*vx(k+1-j)"
          by (by100 simp)
        have "paste_chain_sigma_y vy k ?n j (1-t) = (1-(1-(1-t)))*vy(k-j) + (1-(1-t))*vy(k+1-j)"
          using paste_sigma_inv_u2_edge(2)[OF hj_mid(1) hjj_k hk2 hn3 hk_lt hsucj] by simp
        hence hy: "paste_chain_sigma_y vy k ?n j (1-t) = (1-t)*vy(k-j) + t*vy(k+1-j)"
          by (by100 simp)
        show ?thesis using hx hy hsucj unfolding \<sigma>_def by (by100 simp)
      qed
      \<comment> \<open>Double negation: snd(w'!i) = \\<not>snd(u2!(k-1-i)), snd(w!(k-i)) = snd(u2!(k-i-1)) = snd(u2!(k-1-i)).
         So snd(w'!i) = \\<not>snd(w!(k-i)). Hence (snd(w'!i)=snd(w'!j)) = (snd(w!(k-i))=snd(w!(k-j))).\<close>
      have hdouble_neg: "(snd(w'!i) = snd(w'!j)) = (snd(w!(k-i)) = snd(w!(k-j)))"
      proof -
        \<comment> \<open>snd(w'!i) = \\<not>snd(u2!(length u2 - i)) by same decomposition as hw'i.\<close>
        let ?rivu = "rev (map top1_inverse_edge u2)"
        have hi2: "i - 1 < length ?rivu" using hii hi_mid(1) by (by100 simp)
        have si1: "w'!i = ?rivu!(i-1)"
          using nth_append_first[OF hi2] unfolding w'_def using hi_mid(1) by (by100 simp)
        have si4: "i - 1 < length (map top1_inverse_edge u2)" using hi2 by (by100 simp)
        have si5: "?rivu!(i-1) = (map top1_inverse_edge u2)!(length u2 - i)"
          using rev_nth[OF si4] hi_mid(1) hii by (by100 simp)
        have si6: "length u2 - i < length u2" using hi_mid(1) hii by (by100 linarith)
        have si7: "(map top1_inverse_edge u2)!(length u2 - i) = top1_inverse_edge (u2!(length u2 - i))"
          using si6 by (by100 simp)
        have si8: "snd (w' ! i) = (\<not> snd (u2 ! (length u2 - i)))"
        proof -
          obtain l b where hlb: "u2!(length u2 - i) = (l, b)" by (cases "u2!(length u2 - i)")
          have "top1_inverse_edge (l, b) = (l, \<not>b)" unfolding top1_inverse_edge_def by simp
          with si1 si5 si7 hlb show ?thesis by simp
        qed
        \<comment> \<open>snd(w'!j) = \\<not>snd(u2!(length u2 - j)) by same decomposition.\<close>
        have hj2: "j - 1 < length ?rivu" using hjj hj_mid(1) by (by100 simp)
        have sj1: "w'!j = ?rivu!(j-1)"
          using nth_append_first[OF hj2] unfolding w'_def using hj_mid(1) by (by100 simp)
        have sj4: "j - 1 < length (map top1_inverse_edge u2)" using hj2 by (by100 simp)
        have sj5: "?rivu!(j-1) = (map top1_inverse_edge u2)!(length u2 - j)"
          using rev_nth[OF sj4] hj_mid(1) hjj by (by100 simp)
        have sj6: "length u2 - j < length u2" using hj_mid(1) hjj by (by100 linarith)
        have sj7: "(map top1_inverse_edge u2)!(length u2 - j) = top1_inverse_edge (u2!(length u2 - j))"
          using sj6 by (by100 simp)
        have sj8: "snd (w' ! j) = (\<not> snd (u2 ! (length u2 - j)))"
        proof -
          obtain l b where hlb: "u2!(length u2 - j) = (l, b)" by (cases "u2!(length u2 - j)")
          have "top1_inverse_edge (l, b) = (l, \<not>b)" unfolding top1_inverse_edge_def by simp
          with sj1 sj5 sj7 hlb show ?thesis by simp
        qed
        \<comment> \<open>snd(w!(k-i)) = snd(u2!(k-i-1)) = snd(u2!(length u2 - i)).\<close>
        have hki_ge1': "k - i \<ge> 1" using hii_k hk2 by linarith
        have hki_le': "k - i \<le> length u2" using hi_mid(1) hk_eq by (by100 simp)
        have "w!(k-i) = (u2 @ [(a, True)] @ v)!(k-i-1)"
          unfolding w_def using hki_ge1' by (by100 simp)
        also have "k-i-1 < length u2" using hki_le' hki_ge1' by linarith
        hence "(u2 @ [(a, True)] @ v)!(k-i-1) = u2!(k-i-1)"
          by (rule nth_append_first)
        finally have "w!(k-i) = u2!(k-i-1)" .
        have "k-i-1 = length u2 - i" using hk_eq hi_mid(1) by (by100 simp)
        hence swi: "snd(w!(k-i)) = snd(u2!(length u2 - i))" using \<open>w!(k-i) = u2!(k-i-1)\<close> by simp
        \<comment> \<open>snd(w!(k-j)) = snd(u2!(length u2 - j)).\<close>
        have hkj_ge1: "k - j \<ge> 1" using hjj_k hk2 by linarith
        have hkj_le: "k - j \<le> length u2" using hj_mid(1) hk_eq by (by100 simp)
        have "w!(k-j) = (u2 @ [(a, True)] @ v)!(k-j-1)"
          unfolding w_def using hkj_ge1 by (by100 simp)
        also have "k-j-1 < length u2" using hkj_le hkj_ge1 by linarith
        hence "(u2 @ [(a, True)] @ v)!(k-j-1) = u2!(k-j-1)"
          by (rule nth_append_first)
        finally have "w!(k-j) = u2!(k-j-1)" .
        have "k-j-1 = length u2 - j" using hk_eq hj_mid(1) by (by100 simp)
        hence swj: "snd(w!(k-j)) = snd(u2!(length u2 - j))" using \<open>w!(k-j) = u2!(k-j-1)\<close> by simp
        \<comment> \<open>Combine: \\<not>a = \\<not>b iff a = b.\<close>
        from si8 sj8 swi swj show ?thesis by (by100 auto)
      qed
      from hLHS hC7_app hTHEN hELSE hdouble_neg
      show ?thesis by (by100 auto)
    next
      case False
      show ?thesis
      proof (cases "\<not>(i \<le> length u2) \<and> \<not>(j \<le> length u2)")
        case True
        \<comment> \<open>CASE: both in v range.\<close>
        \<comment> \<open>Both i,j in v range: \\<not>(i \\<le> length u2) and \\<not>(j \\<le> length u2).
           sigma(i,t) = edge\\_orig(i+1, t) and sigma(j,t) = edge\\_orig(j+1, t).
           Target label w'!i = w!(i+1) and exponent w'!i = w!(i+1).
           Direct application of original C7 at indices (i+1), (j+1).\<close>
        have hiv: "\<not>(i \<le> length u2)" and hjv: "\<not>(j \<le> length u2)" using True by simp_all
        \<comment> \<open>sigma(i,t) = ((1-t)*vx(i+1) + t*vx(Suc(i+1) mod n), same for y).\<close>
        have hki: "k \<le> i" using hiv hk_eq by linarith
        have hkj: "k \<le> j" using hjv hk_eq by linarith
        have h\<sigma>i: "\<sigma> i t = ((1-t)*vx(i+1) + t*vx(Suc(i+1) mod ?n),
                              (1-t)*vy(i+1) + t*vy(Suc(i+1) mod ?n))"
          using paste_sigma_v_edge(1)[OF hki hi_mid(2) hk_pos hn3]
                paste_sigma_v_edge(2)[OF hki hi_mid(2) hk_pos hn3]
          unfolding \<sigma>_def by (by100 simp)
        have h\<sigma>j: "\<sigma> j t = ((1-t)*vx(j+1) + t*vx(Suc(j+1) mod ?n),
                              (1-t)*vy(j+1) + t*vy(Suc(j+1) mod ?n))"
          using paste_sigma_v_edge(1)[OF hkj hj_mid(2) hk_pos hn3]
                paste_sigma_v_edge(2)[OF hkj hj_mid(2) hk_pos hn3]
          unfolding \<sigma>_def by (by100 simp)
        \<comment> \<open>Labels and exponents match original at shifted index.\<close>
        \<comment> \<open>Both w'!i and w!(i+1) equal v!(i-length u2-1). Similarly for j.\<close>
        have hlen_w: "?n = 2 + length u2 + length v" unfolding w_def by (by100 simp)
        have hvi: "i - length u2 - 1 < length v"
        proof -
          have "i \<le> length u2 + length v" using hi_mid hlen_w by linarith
          moreover have "i > length u2" using hiv by linarith
          ultimately show ?thesis by linarith
        qed
        have hvj: "j - length u2 - 1 < length v"
        proof -
          have "j \<le> length u2 + length v" using hj_mid hlen_w by linarith
          moreover have "j > length u2" using hjv by linarith
          ultimately show ?thesis by linarith
        qed
        \<comment> \<open>List indexing: w'!i and w!(i+1) both equal v!(i-|u2|-1).\<close>
        \<comment> \<open>List indexing via step-by-step append decomposition.\<close>
        \<comment> \<open>List indexing: w'!i and w!(i+1) both = v!(i-|u2|-1) for v-range positions.
           Proof: step-by-step append decomposition (nth\\_append at each level).
           Same for j. Sorry'd pending process\\_theories run.\<close>
        have hw'_i_eq: "w'!i = v!(i - length u2 - 1)"
        proof -
          have s1: "w'!i = (rev (map top1_inverse_edge u2) @ v @ [(c, True)])!(i - 1)"
            unfolding w'_def using hi_mid by (by100 simp)
          have "i - 1 \<ge> length (rev (map top1_inverse_edge u2))"
            using hiv by (by100 simp)
          hence s2: "(rev (map top1_inverse_edge u2) @ v @ [(c, True)])!(i - 1)
              = (v @ [(c, True)])!(i - 1 - length (rev (map top1_inverse_edge u2)))"
            by (rule nth_append_second)
          have "i - 1 - length (rev (map top1_inverse_edge u2)) = i - 1 - length u2"
            by (by100 simp)
          hence s3: "(v @ [(c, True)])!(i - 1 - length (rev (map top1_inverse_edge u2)))
              = (v @ [(c, True)])!(i - 1 - length u2)" by simp
          have hvi2: "i - 1 - length u2 < length v" using hvi by (by100 simp)
          hence s4: "(v @ [(c, True)])!(i - 1 - length u2) = v!(i - 1 - length u2)"
            by (rule nth_append_first)
          have "i - 1 - length u2 = i - length u2 - 1" using hiv by (by100 linarith)
          with s1 s2 s3 s4 show ?thesis by simp
        qed
        have hw_i1_eq: "w!(i+1) = v!(i - length u2 - 1)"
          using hi_mid hiv hvi unfolding w_def by (simp add: nth_append_skip)
        have hw'_j_eq: "w'!j = v!(j - length u2 - 1)"
        proof -
          have s1: "w'!j = (rev (map top1_inverse_edge u2) @ v @ [(c, True)])!(j - 1)"
            unfolding w'_def using hj_mid by (by100 simp)
          have "j - 1 \<ge> length (rev (map top1_inverse_edge u2))"
            using hjv by (by100 simp)
          hence s2: "(rev (map top1_inverse_edge u2) @ v @ [(c, True)])!(j - 1)
              = (v @ [(c, True)])!(j - 1 - length (rev (map top1_inverse_edge u2)))"
            by (rule nth_append_second)
          have "j - 1 - length (rev (map top1_inverse_edge u2)) = j - 1 - length u2"
            by (by100 simp)
          hence s3: "(v @ [(c, True)])!(j - 1 - length (rev (map top1_inverse_edge u2)))
              = (v @ [(c, True)])!(j - 1 - length u2)" by simp
          have hvj2: "j - 1 - length u2 < length v" using hvj by (by100 simp)
          hence s4: "(v @ [(c, True)])!(j - 1 - length u2) = v!(j - 1 - length u2)"
            by (rule nth_append_first)
          have "j - 1 - length u2 = j - length u2 - 1" using hjv by (by100 linarith)
          with s1 s2 s3 s4 show ?thesis by simp
        qed
        have hw_j1_eq: "w!(j+1) = v!(j - length u2 - 1)"
          using hj_mid hjv hvj unfolding w_def by (simp add: nth_append_skip)
        have hfst_match_i: "fst(w'!i) = fst(w!(i+1))" using hw'_i_eq hw_i1_eq by simp
        have hfst_match_j: "fst(w'!j) = fst(w!(j+1))" using hw'_j_eq hw_j1_eq by simp
        have hsnd_match_i: "snd(w'!i) = snd(w!(i+1))" using hw'_i_eq hw_i1_eq by simp
        have hsnd_match_j: "snd(w'!j) = snd(w!(j+1))" using hw'_j_eq hw_j1_eq by simp
        \<comment> \<open>Apply original C7.\<close>
        have hi1_lt: "i+1 < ?n" using hi_mid by linarith
        have hj1_lt: "j+1 < ?n" using hj_mid by linarith
        have hlabel_orig: "fst(w!(i+1)) = fst(w!(j+1))"
          using hlabel hfst_match_i hfst_match_j by simp
        from hC7_orig[rule_format, OF hi1_lt hj1_lt hlabel_orig ht]
        have hC7_app: "q2 ((1-t)*vx(i+1) + t*vx(Suc(i+1) mod ?n),
                            (1-t)*vy(i+1) + t*vy(Suc(i+1) mod ?n))
          = (if snd(w!(i+1)) = snd(w!(j+1))
             then q2 ((1-t)*vx(j+1) + t*vx(Suc(j+1) mod ?n),
                       (1-t)*vy(j+1) + t*vy(Suc(j+1) mod ?n))
             else q2 (t*vx(j+1) + (1-t)*vx(Suc(j+1) mod ?n),
                       t*vy(j+1) + (1-t)*vy(Suc(j+1) mod ?n)))" .
        \<comment> \<open>Translate back to sigma and target labels.\<close>
        have h\<sigma>j_1mt: "\<sigma> j (1-t) = (t*vx(j+1) + (1-t)*vx(Suc(j+1) mod ?n),
                                      t*vy(j+1) + (1-t)*vy(Suc(j+1) mod ?n))"
        proof -
          have "paste_chain_sigma_x vx k ?n j (1-t) = (1-(1-t))*vx(j+1) + (1-t)*vx(Suc(j+1) mod ?n)"
            using paste_sigma_v_edge(1)[OF hkj hj_mid(2) hk_pos hn3] by simp
          hence hx: "paste_chain_sigma_x vx k ?n j (1-t) = t*vx(j+1) + (1-t)*vx(Suc(j+1) mod ?n)"
            by (by100 simp)
          have "paste_chain_sigma_y vy k ?n j (1-t) = (1-(1-t))*vy(j+1) + (1-t)*vy(Suc(j+1) mod ?n)"
            using paste_sigma_v_edge(2)[OF hkj hj_mid(2) hk_pos hn3] by simp
          hence hy: "paste_chain_sigma_y vy k ?n j (1-t) = t*vy(j+1) + (1-t)*vy(Suc(j+1) mod ?n)"
            by (by100 simp)
          show ?thesis using hx hy unfolding \<sigma>_def by (by100 simp)
        qed
        show ?thesis using hC7_app h\<sigma>i h\<sigma>j h\<sigma>j_1mt hsnd_match_i hsnd_match_j by (by100 auto)
      next
        case False
        \<comment> \<open>CASE: one in inv(u2), other in v (cross pair).\<close>
        \<comment> \<open>CROSS PAIR: one in inv(u2), other in v.
           From the two False cases: \\<not>(both inv) and \\<not>(both v).
           So exactly one of i,j is \\<le> length u2 and the other is not.\<close>
        from \<open>\<not>(i \<le> length u2 \<and> j \<le> length u2)\<close> False
        have hcross: "(i \<le> length u2 \<and> \<not>(j \<le> length u2)) \<or> (\<not>(i \<le> length u2) \<and> j \<le> length u2)"
          by (by100 auto)
        show ?thesis
        proof (cases "i \<le> length u2")
          case True note hi_inv = this
          hence hj_v: "\<not>(j \<le> length u2)" using hcross by (by100 auto)
          \<comment> \<open>i in inv(u2): sigma(i,t) = edge\\_orig(k-i, 1-t).
             j in v: sigma(j,t) = edge\\_orig(j+1, t).
             Need original C7 at (k-i, j+1).
             Single negation: snd(w'!i) = \\<not>snd(w!(k-i)), snd(w'!j) = snd(w!(j+1)).
             So (snd(w'!i) = snd(w'!j)) iff (snd(w!(k-i)) \\<noteq> snd(w!(j+1))).
             This SWAPS the then/else branches of original C7.\<close>
          \<comment> \<open>Setup: sigma(i,t) for inv range, sigma(j,t) for v range.\<close>
          have hii_k: "i \<le> k - 1" using hi_inv hk_eq by linarith
          have hk2: "k \<ge> 2" using hi_mid(1) hii_k by linarith
          have hsuci: "Suc (k-i) mod ?n = k+1-i" using hi_mid(1) hii_k hk_lt by (by100 simp)
          have h\<sigma>i: "\<sigma> i t = (t*vx(k-i)+(1-t)*vx(k+1-i), t*vy(k-i)+(1-t)*vy(k+1-i))"
          proof -
            from paste_sigma_inv_u2_edge(1)[OF hi_mid(1) hii_k hk2 hn3 hk_lt hsuci]
                 paste_sigma_inv_u2_edge(2)[OF hi_mid(1) hii_k hk2 hn3 hk_lt hsuci]
            show ?thesis unfolding \<sigma>_def by (by100 simp)
          qed
          have hkv: "k \<le> j" using hj_v hk_eq by linarith
          have h\<sigma>j: "\<sigma> j t = ((1-t)*vx(j+1)+t*vx(Suc(j+1) mod ?n), (1-t)*vy(j+1)+t*vy(Suc(j+1) mod ?n))"
            using paste_sigma_v_edge(1)[OF hkv hj_mid(2) hk_pos hn3]
                  paste_sigma_v_edge(2)[OF hkv hj_mid(2) hk_pos hn3]
            unfolding \<sigma>_def by (by100 simp)
          \<comment> \<open>sigma(j, 1-t) for v range.\<close>
          have h\<sigma>j_1mt: "\<sigma> j (1-t) = (t*vx(j+1)+(1-t)*vx(Suc(j+1) mod ?n), t*vy(j+1)+(1-t)*vy(Suc(j+1) mod ?n))"
          proof -
            have "paste_chain_sigma_x vx k ?n j (1-t) = (1-(1-t))*vx(j+1) + (1-t)*vx(Suc(j+1) mod ?n)"
              using paste_sigma_v_edge(1)[OF hkv hj_mid(2) hk_pos hn3] by simp
            hence hx: "paste_chain_sigma_x vx k ?n j (1-t) = t*vx(j+1) + (1-t)*vx(Suc(j+1) mod ?n)"
              by (by100 simp)
            have "paste_chain_sigma_y vy k ?n j (1-t) = (1-(1-t))*vy(j+1) + (1-t)*vy(Suc(j+1) mod ?n)"
              using paste_sigma_v_edge(2)[OF hkv hj_mid(2) hk_pos hn3] by simp
            hence hy: "paste_chain_sigma_y vy k ?n j (1-t) = t*vy(j+1) + (1-t)*vy(Suc(j+1) mod ?n)"
              by (by100 simp)
            show ?thesis using hx hy unfolding \<sigma>_def by (by100 simp)
          qed
          \<comment> \<open>Original C7 at (k-i, j+1) with param 1-t.\<close>
          have hki_lt: "k-i < ?n" using hii_k hk_lt by (by100 linarith)
          have hj1_lt: "j+1 < ?n" using hj_mid by linarith
          \<comment> \<open>Label correspondence.\<close>
          have hlabel_orig_cross: "fst(w!(k-i)) = fst(w!(j+1))"
          proof -
            \<comment> \<open>fst(w'!i) = fst(w!(k-i)): inv(u2) decomposition (same as hw'i in inv case).\<close>
            let ?rivu = "rev (map top1_inverse_edge u2)"
            have h_i2: "i - 1 < length ?rivu" using hi_inv hi_mid(1) by (by100 simp)
            have "w'!i = ?rivu!(i-1)"
              using nth_append_first[OF h_i2] unfolding w'_def using hi_mid(1) by (by100 simp)
            also have h_i4: "i - 1 < length (map top1_inverse_edge u2)" using h_i2 by (by100 simp)
            have "?rivu!(i-1) = (map top1_inverse_edge u2)!(length (map top1_inverse_edge u2) - Suc(i-1))"
              using h_i4 by (rule rev_nth)
            also have "length (map top1_inverse_edge u2) - Suc(i-1) = length u2 - i"
              using hi_mid(1) hi_inv by (by100 simp)
            also have "length u2 - i < length u2" using hi_mid(1) hi_inv by (by100 linarith)
            hence "(map top1_inverse_edge u2)!(length u2 - i) = top1_inverse_edge (u2!(length u2 - i))"
              by (by100 simp)
            finally have "w'!i = top1_inverse_edge (u2!(length u2 - i))" by simp
            hence hfst_w'i_u2: "fst(w'!i) = fst(u2!(length u2 - i))"
              unfolding top1_inverse_edge_def by (cases "u2!(length u2 - i)") simp
            \<comment> \<open>w!(k-i) = u2!(k-i-1) = u2!(length u2 - i).\<close>
            have "k - i \<ge> 1" using hii_k hk2 by linarith
            have "w!(k-i) = (u2 @ [(a, True)] @ v)!(k-i-1)"
              unfolding w_def using \<open>k-i \<ge> 1\<close> by (by100 simp)
            also have "k-i-1 < length u2" using hi_mid(1) hk_eq hi_inv by (by100 simp)
            hence "(u2 @ [(a, True)] @ v)!(k-i-1) = u2!(k-i-1)" by (rule nth_append_first)
            finally have "w!(k-i) = u2!(k-i-1)" .
            have "k-i-1 = length u2 - i" using hk_eq hi_mid(1) by (by100 simp)
            hence hfst_wki: "fst(w!(k-i)) = fst(u2!(length u2 - i))" using \<open>w!(k-i) = u2!(k-i-1)\<close> by simp
            hence hfst_link_i: "fst(w'!i) = fst(w!(k-i))" using hfst_w'i_u2 by simp
            \<comment> \<open>fst(w'!j) = fst(w!(j+1)): v range (same as v case).\<close>
            have hlen_w_val: "?n = 2 + length u2 + length v" unfolding w_def by (by100 simp)
            have hvj_lt: "j - length u2 - 1 < length v" using hj_mid hj_v hlen_w_val by linarith
            have hjrivu: "j - 1 \<ge> length ?rivu" using hj_v by (by100 simp)
            have "w'!j = (?rivu @ v @ [(c, True)])!(j-1)"
              unfolding w'_def using hj_mid(1) by (by100 simp)
            also have "(?rivu @ v @ [(c, True)])!(j-1) = (v @ [(c, True)])!(j-1-length ?rivu)"
              using nth_append_second[OF hjrivu] .
            also have "j-1-length ?rivu = j-1-length u2" by (by100 simp)
            hence "(v @ [(c, True)])!(j-1-length ?rivu) = (v @ [(c, True)])!(j-1-length u2)" by simp
            also have "j-1-length u2 < length v" using hvj_lt hj_v by (by100 simp)
            hence "(v @ [(c, True)])!(j-1-length u2) = v!(j-1-length u2)" by (rule nth_append_first)
            finally have hw'j_val: "w'!j = v!(j-1-length u2)" .
            have hw_j1_val: "w!(j+1) = v!(j - length u2 - 1)"
              using hj_mid hj_v hvj_lt unfolding w_def by (simp add: nth_append_skip)
            have "j-1-length u2 = j-length u2-1" using hj_v by (by100 linarith)
            hence hfst_link_j: "fst(w'!j) = fst(w!(j+1))" using hw'j_val hw_j1_val by simp
            from hlabel hfst_link_i hfst_link_j show ?thesis by simp
          qed
          have ht_1mt: "1-t \<in> I_set" using ht unfolding top1_unit_interval_def by (by100 auto)
          from hC7_orig[rule_format, OF hki_lt hj1_lt hlabel_orig_cross ht_1mt]
          have hC7_cross: "q2 ((1-(1-t))*vx(k-i) + (1-t)*vx(Suc(k-i) mod ?n),
                                (1-(1-t))*vy(k-i) + (1-t)*vy(Suc(k-i) mod ?n))
            = (if snd(w!(k-i)) = snd(w!(j+1))
               then q2 ((1-(1-t))*vx(j+1) + (1-t)*vx(Suc(j+1) mod ?n),
                         (1-(1-t))*vy(j+1) + (1-t)*vy(Suc(j+1) mod ?n))
               else q2 ((1-t)*vx(j+1) + (1-(1-t))*vx(Suc(j+1) mod ?n),
                         (1-t)*vy(j+1) + (1-(1-t))*vy(Suc(j+1) mod ?n)))" .
          \<comment> \<open>Translate to sigma.\<close>
          have hLHS: "q2 (\<sigma> i t) = q2 ((1-(1-t))*vx(k-i) + (1-t)*vx(Suc(k-i) mod ?n),
                                         (1-(1-t))*vy(k-i) + (1-t)*vy(Suc(k-i) mod ?n))"
            using h\<sigma>i hsuci by (by100 simp)
          have hTHEN_cross: "q2 (\<sigma> j (1-t)) = q2 ((1-(1-t))*vx(j+1) + (1-t)*vx(Suc(j+1) mod ?n),
                                                      (1-(1-t))*vy(j+1) + (1-t)*vy(Suc(j+1) mod ?n))"
            using h\<sigma>j_1mt by (by100 simp)
          have hELSE_cross: "q2 (\<sigma> j t) = q2 ((1-t)*vx(j+1) + (1-(1-t))*vx(Suc(j+1) mod ?n),
                                                  (1-t)*vy(j+1) + (1-(1-t))*vy(Suc(j+1) mod ?n))"
            using h\<sigma>j by (by100 simp)
          \<comment> \<open>Single negation: snd(w'!i) = \\<not>snd(w!(k-i)), snd(w'!j) = snd(w!(j+1)).
             So (snd(w'!i)=snd(w'!j)) = (snd(w!(k-i)) \\<noteq> snd(w!(j+1))).
             This SWAPS the then/else branches.\<close>
          have hsingle_neg: "(snd(w'!i) = snd(w'!j)) = (snd(w!(k-i)) \<noteq> snd(w!(j+1)))"
          proof -
            \<comment> \<open>snd(w'!i) = \\<not>snd(w!(k-i)): inv side flips snd.\<close>
            \<comment> \<open>Reuse: w'!i = inv(u2!(length u2-i)) and w!(k-i) = u2!(length u2-i) from hlabel proof.\<close>
            let ?rivu = "rev (map top1_inverse_edge u2)"
            have h_i2: "i - 1 < length ?rivu" using hi_inv hi_mid(1) by (by100 simp)
            have "w'!i = ?rivu!(i-1)"
              using nth_append_first[OF h_i2] unfolding w'_def using hi_mid(1) by (by100 simp)
            also have h_i4: "i - 1 < length (map top1_inverse_edge u2)" using h_i2 by (by100 simp)
            have "?rivu!(i-1) = (map top1_inverse_edge u2)!(length (map top1_inverse_edge u2) - Suc(i-1))"
              using h_i4 by (rule rev_nth)
            also have "length (map top1_inverse_edge u2) - Suc(i-1) = length u2 - i"
              using hi_mid(1) hi_inv by (by100 simp)
            also have "length u2 - i < length u2" using hi_mid(1) hi_inv by (by100 linarith)
            hence "(map top1_inverse_edge u2)!(length u2 - i) = top1_inverse_edge (u2!(length u2 - i))"
              by (by100 simp)
            finally have hw'i_val: "w'!i = top1_inverse_edge (u2!(length u2 - i))" by simp
            obtain li bi where hlbi: "u2!(length u2 - i) = (li, bi)" by (cases "u2!(length u2 - i)")
            have "snd (top1_inverse_edge (li, bi)) = (\<not>bi)" unfolding top1_inverse_edge_def by simp
            hence hsnd_w'i: "snd(w'!i) = (\<not>bi)" using hw'i_val hlbi by simp
            \<comment> \<open>snd(w!(k-i)) = bi.\<close>
            have "k - i \<ge> 1" using hii_k hk2 by linarith
            have "w!(k-i) = (u2 @ [(a, True)] @ v)!(k-i-1)"
              unfolding w_def using \<open>k-i \<ge> 1\<close> by (by100 simp)
            also have "k-i-1 < length u2" using hi_mid(1) hk_eq hi_inv by (by100 simp)
            hence "(u2 @ [(a, True)] @ v)!(k-i-1) = u2!(k-i-1)" by (rule nth_append_first)
            finally have "w!(k-i) = u2!(k-i-1)" .
            have "k-i-1 = length u2 - i" using hk_eq hi_mid(1) by (by100 simp)
            hence hsnd_wki: "snd(w!(k-i)) = bi" using \<open>w!(k-i) = u2!(k-i-1)\<close> hlbi by simp
            \<comment> \<open>snd(w'!j) = snd(w!(j+1)): v side no flip.\<close>
            have hlen_w_val: "?n = 2 + length u2 + length v" unfolding w_def by (by100 simp)
            have hvj_lt: "j - length u2 - 1 < length v" using hj_mid hj_v hlen_w_val by linarith
            have hjrivu: "j - 1 \<ge> length ?rivu" using hj_v by (by100 simp)
            have "w'!j = (?rivu @ v @ [(c, True)])!(j-1)"
              unfolding w'_def using hj_mid(1) by (by100 simp)
            also have "(?rivu @ v @ [(c, True)])!(j-1) = (v @ [(c, True)])!(j-1-length ?rivu)"
              using nth_append_second[OF hjrivu] .
            also have "j-1-length ?rivu = j-1-length u2" by (by100 simp)
            hence "(v @ [(c, True)])!(j-1-length ?rivu) = (v @ [(c, True)])!(j-1-length u2)" by simp
            also have "j-1-length u2 < length v" using hvj_lt hj_v by (by100 simp)
            hence "(v @ [(c, True)])!(j-1-length u2) = v!(j-1-length u2)" by (rule nth_append_first)
            finally have hw'j_val: "w'!j = v!(j-1-length u2)" .
            have hw_j1_val: "w!(j+1) = v!(j - length u2 - 1)"
              using hj_mid hj_v hvj_lt unfolding w_def by (simp add: nth_append_skip)
            have "j-1-length u2 = j-length u2-1" using hj_v by (by100 linarith)
            hence hsnd_w'j_eq: "snd(w'!j) = snd(w!(j+1))" using hw'j_val hw_j1_val by simp
            \<comment> \<open>Combine: snd(w'!i)=snd(w'!j) iff \\<not>bi=snd(w!(j+1)) iff bi\\<noteq>snd(w!(j+1)).\<close>
            from hsnd_w'i hsnd_wki hsnd_w'j_eq show ?thesis by (by100 auto)
          qed
          from hLHS hC7_cross hTHEN_cross hELSE_cross hsingle_neg
          show ?thesis by (by100 auto)
        next
          case False note hi_v = this
          hence hj_inv: "j \<le> length u2" using hcross by (by100 auto)
          \<comment> \<open>Symmetric: i in v, j in inv(u2). Same proof with i,j roles swapped.\<close>
          have hjj_k: "j \<le> k - 1" using hj_inv hk_eq by linarith
          have hk2': "k \<ge> 2" using hj_mid(1) hjj_k by linarith
          have hsucj': "Suc (k-j) mod ?n = k+1-j" using hj_mid(1) hjj_k hk_lt by (by100 simp)
          have h\<sigma>j': "\<sigma> j t = (t*vx(k-j)+(1-t)*vx(k+1-j), t*vy(k-j)+(1-t)*vy(k+1-j))"
          proof -
            from paste_sigma_inv_u2_edge(1)[OF hj_mid(1) hjj_k hk2' hn3 hk_lt hsucj']
                 paste_sigma_inv_u2_edge(2)[OF hj_mid(1) hjj_k hk2' hn3 hk_lt hsucj']
            show ?thesis unfolding \<sigma>_def by (by100 simp)
          qed
          have hkv': "k \<le> i" using hi_v hk_eq by linarith
          have h\<sigma>i': "\<sigma> i t = ((1-t)*vx(i+1)+t*vx(Suc(i+1) mod ?n), (1-t)*vy(i+1)+t*vy(Suc(i+1) mod ?n))"
            using paste_sigma_v_edge(1)[OF hkv' hi_mid(2) hk_pos hn3]
                  paste_sigma_v_edge(2)[OF hkv' hi_mid(2) hk_pos hn3]
            unfolding \<sigma>_def by (by100 simp)
          \<comment> \<open>sigma(j, 1-t) for inv range.\<close>
          have h\<sigma>j'_1mt: "\<sigma> j (1-t) = ((1-t)*vx(k-j)+t*vx(k+1-j), (1-t)*vy(k-j)+t*vy(k+1-j))"
          proof -
            have "paste_chain_sigma_x vx k ?n j (1-t) = (1-(1-(1-t)))*vx(k-j) + (1-(1-t))*vx(k+1-j)"
              using paste_sigma_inv_u2_edge(1)[OF hj_mid(1) hjj_k hk2' hn3 hk_lt hsucj'] by simp
            hence hx: "paste_chain_sigma_x vx k ?n j (1-t) = (1-t)*vx(k-j) + t*vx(k+1-j)"
              by (by100 simp)
            have "paste_chain_sigma_y vy k ?n j (1-t) = (1-(1-(1-t)))*vy(k-j) + (1-(1-t))*vy(k+1-j)"
              using paste_sigma_inv_u2_edge(2)[OF hj_mid(1) hjj_k hk2' hn3 hk_lt hsucj'] by simp
            hence hy: "paste_chain_sigma_y vy k ?n j (1-t) = (1-t)*vy(k-j) + t*vy(k+1-j)"
              by (by100 simp)
            show ?thesis using hx hy unfolding \<sigma>_def by (by100 simp)
          qed
          \<comment> \<open>Original C7 at (i+1, k-j) with param t.\<close>
          have hi1_lt: "i+1 < ?n" using hi_mid by linarith
          have hkj_lt': "k-j < ?n" using hjj_k hk_lt by (by100 linarith)
          have hlabel_cross2: "fst(w!(i+1)) = fst(w!(k-j))"
          proof -
            \<comment> \<open>fst(w'!i) = fst(w!(i+1)) from v range.\<close>
            have hlen_w_val: "?n = 2 + length u2 + length v" unfolding w_def by (by100 simp)
            have hvi_lt: "i - length u2 - 1 < length v" using hi_mid hi_v hlen_w_val by linarith
            let ?rivu = "rev (map top1_inverse_edge u2)"
            have hirivu: "i - 1 \<ge> length ?rivu" using hi_v by (by100 simp)
            have "w'!i = (?rivu @ v @ [(c, True)])!(i-1)"
              unfolding w'_def using hi_mid(1) by (by100 simp)
            also have "(?rivu @ v @ [(c, True)])!(i-1) = (v @ [(c, True)])!(i-1-length ?rivu)"
              using nth_append_second[OF hirivu] .
            also have "i-1-length ?rivu = i-1-length u2" by (by100 simp)
            hence "(v @ [(c, True)])!(i-1-length ?rivu) = (v @ [(c, True)])!(i-1-length u2)" by simp
            also have "i-1-length u2 < length v" using hvi_lt hi_v by (by100 simp)
            hence "(v @ [(c, True)])!(i-1-length u2) = v!(i-1-length u2)" by (rule nth_append_first)
            finally have hw'i_val: "w'!i = v!(i-1-length u2)" .
            have hw_i1_val: "w!(i+1) = v!(i-length u2-1)"
              using hi_mid hi_v hvi_lt unfolding w_def by (simp add: nth_append_skip)
            have "i-1-length u2 = i-length u2-1" using hi_v by (by100 linarith)
            hence hfst_i_link: "fst(w'!i) = fst(w!(i+1))" using hw'i_val hw_i1_val by simp
            \<comment> \<open>fst(w'!j) = fst(w!(k-j)) from inv range.\<close>
            have h_j2: "j - 1 < length ?rivu" using hj_inv hj_mid(1) by (by100 simp)
            have "w'!j = ?rivu!(j-1)"
              using nth_append_first[OF h_j2] unfolding w'_def using hj_mid(1) by (by100 simp)
            also have h_j4: "j - 1 < length (map top1_inverse_edge u2)" using h_j2 by (by100 simp)
            have "?rivu!(j-1) = (map top1_inverse_edge u2)!(length (map top1_inverse_edge u2) - Suc(j-1))"
              using h_j4 by (rule rev_nth)
            also have "length (map top1_inverse_edge u2) - Suc(j-1) = length u2 - j"
              using hj_mid(1) hj_inv by (by100 simp)
            also have "length u2 - j < length u2" using hj_mid(1) hj_inv by (by100 linarith)
            hence "(map top1_inverse_edge u2)!(length u2 - j) = top1_inverse_edge (u2!(length u2 - j))"
              by (by100 simp)
            finally have "w'!j = top1_inverse_edge (u2!(length u2 - j))" by simp
            hence hfst_w'j_u2: "fst(w'!j) = fst(u2!(length u2 - j))"
              unfolding top1_inverse_edge_def by (cases "u2!(length u2 - j)") simp
            have "k - j \<ge> 1" using hjj_k hk2' by linarith
            have "w!(k-j) = (u2 @ [(a, True)] @ v)!(k-j-1)"
              unfolding w_def using \<open>k-j \<ge> 1\<close> by (by100 simp)
            also have "k-j-1 < length u2" using hj_mid(1) hk_eq hj_inv by (by100 simp)
            hence "(u2 @ [(a, True)] @ v)!(k-j-1) = u2!(k-j-1)" by (rule nth_append_first)
            finally have "w!(k-j) = u2!(k-j-1)" .
            have "k-j-1 = length u2 - j" using hk_eq hj_mid(1) by (by100 simp)
            hence hfst_j_link: "fst(w'!j) = fst(w!(k-j))" using hfst_w'j_u2 \<open>w!(k-j) = u2!(k-j-1)\<close> by simp
            from hlabel hfst_i_link hfst_j_link show ?thesis by simp
          qed
          from hC7_orig[rule_format, OF hi1_lt hkj_lt' hlabel_cross2 ht]
          have hC7_cross2: "q2 ((1-t)*vx(i+1) + t*vx(Suc(i+1) mod ?n),
                                 (1-t)*vy(i+1) + t*vy(Suc(i+1) mod ?n))
            = (if snd(w!(i+1)) = snd(w!(k-j))
               then q2 ((1-t)*vx(k-j) + t*vx(Suc(k-j) mod ?n),
                         (1-t)*vy(k-j) + t*vy(Suc(k-j) mod ?n))
               else q2 (t*vx(k-j) + (1-t)*vx(Suc(k-j) mod ?n),
                         t*vy(k-j) + (1-t)*vy(Suc(k-j) mod ?n)))" .
          \<comment> \<open>Translate sigma.\<close>
          have hLHS2: "q2 (\<sigma> i t) = q2 ((1-t)*vx(i+1) + t*vx(Suc(i+1) mod ?n),
                                          (1-t)*vy(i+1) + t*vy(Suc(i+1) mod ?n))"
            using h\<sigma>i' by (by100 simp)
          \<comment> \<open>sigma(j,t) for inv range = (t*vx(k-j)+(1-t)*vx(k+1-j), ...).\<close>
          have hTHEN2: "q2 (\<sigma> j t) = q2 (t*vx(k-j) + (1-t)*vx(Suc(k-j) mod ?n),
                                           t*vy(k-j) + (1-t)*vy(Suc(k-j) mod ?n))"
            using h\<sigma>j' hsucj' by (by100 simp)
          \<comment> \<open>sigma(j,1-t) for inv range = ((1-t)*vx(k-j)+t*vx(k+1-j), ...).\<close>
          have hELSE2: "q2 (\<sigma> j (1-t)) = q2 ((1-t)*vx(k-j) + t*vx(Suc(k-j) mod ?n),
                                                (1-t)*vy(k-j) + t*vy(Suc(k-j) mod ?n))"
            using h\<sigma>j'_1mt hsucj' by (by100 simp)
          \<comment> \<open>Single negation (j side flipped, i side not).\<close>
          have hsingle_neg2: "(snd(w'!i) = snd(w'!j)) = (snd(w!(i+1)) \<noteq> snd(w!(k-j)))"
          proof -
            \<comment> \<open>snd(w'!j) = \\<not>snd(w!(k-j)): j in inv range, snd flipped.\<close>
            let ?rivu = "rev (map top1_inverse_edge u2)"
            have h_j2': "j - 1 < length ?rivu" using hj_inv hj_mid(1) by (by100 simp)
            have "w'!j = ?rivu!(j-1)"
              using nth_append_first[OF h_j2'] unfolding w'_def using hj_mid(1) by (by100 simp)
            also have h_j4': "j - 1 < length (map top1_inverse_edge u2)" using h_j2' by (by100 simp)
            have "?rivu!(j-1) = (map top1_inverse_edge u2)!(length (map top1_inverse_edge u2) - Suc(j-1))"
              using h_j4' by (rule rev_nth)
            also have "length (map top1_inverse_edge u2) - Suc(j-1) = length u2 - j"
              using hj_mid(1) hj_inv by (by100 simp)
            also have "length u2 - j < length u2" using hj_mid(1) hj_inv by (by100 linarith)
            hence "(map top1_inverse_edge u2)!(length u2 - j) = top1_inverse_edge (u2!(length u2 - j))"
              by (by100 simp)
            finally have hw'j_val: "w'!j = top1_inverse_edge (u2!(length u2 - j))" by simp
            obtain lj bj where hlbj: "u2!(length u2 - j) = (lj, bj)" by (cases "u2!(length u2 - j)")
            have "snd (top1_inverse_edge (lj, bj)) = (\<not>bj)" unfolding top1_inverse_edge_def by simp
            hence hsnd_w'j: "snd(w'!j) = (\<not>bj)" using hw'j_val hlbj by simp
            have "k - j \<ge> 1" using hjj_k hk2' by linarith
            have "w!(k-j) = (u2 @ [(a, True)] @ v)!(k-j-1)"
              unfolding w_def using \<open>k-j \<ge> 1\<close> by (by100 simp)
            also have "k-j-1 < length u2" using hj_mid(1) hk_eq hj_inv by (by100 simp)
            hence "(u2 @ [(a, True)] @ v)!(k-j-1) = u2!(k-j-1)" by (rule nth_append_first)
            finally have "w!(k-j) = u2!(k-j-1)" .
            have "k-j-1 = length u2 - j" using hk_eq hj_mid(1) by (by100 simp)
            hence hsnd_wkj: "snd(w!(k-j)) = bj" using \<open>w!(k-j) = u2!(k-j-1)\<close> hlbj by simp
            \<comment> \<open>snd(w'!i) = snd(w!(i+1)): i in v range, no flip.\<close>
            have hlen_w_val: "?n = 2 + length u2 + length v" unfolding w_def by (by100 simp)
            have hvi_lt: "i - length u2 - 1 < length v" using hi_mid hi_v hlen_w_val by linarith
            have hirivu: "i - 1 \<ge> length ?rivu" using hi_v by (by100 simp)
            have "w'!i = (?rivu @ v @ [(c, True)])!(i-1)"
              unfolding w'_def using hi_mid(1) by (by100 simp)
            also have "(?rivu @ v @ [(c, True)])!(i-1) = (v @ [(c, True)])!(i-1-length ?rivu)"
              using nth_append_second[OF hirivu] .
            also have "i-1-length ?rivu = i-1-length u2" by (by100 simp)
            hence "(v @ [(c, True)])!(i-1-length ?rivu) = (v @ [(c, True)])!(i-1-length u2)" by simp
            also have "i-1-length u2 < length v" using hvi_lt hi_v by (by100 simp)
            hence "(v @ [(c, True)])!(i-1-length u2) = v!(i-1-length u2)" by (rule nth_append_first)
            finally have hw'i_val: "w'!i = v!(i-1-length u2)" .
            have hw_i1_val: "w!(i+1) = v!(i-length u2-1)"
              using hi_mid hi_v hvi_lt unfolding w_def by (simp add: nth_append_skip)
            have "i-1-length u2 = i-length u2-1" using hi_v by (by100 linarith)
            hence hsnd_w'i_eq: "snd(w'!i) = snd(w!(i+1))" using hw'i_val hw_i1_val by simp
            from hsnd_w'i_eq hsnd_w'j hsnd_wkj show ?thesis by (by100 auto)
          qed
          from hLHS2 hC7_cross2 hTHEN2 hELSE2 hsingle_neg2
          show ?thesis by (by100 auto)
        qed
      qed
    qed
  qed
qed

\<comment> \<open>NOTE: paste\\_chain\\_polygon\\_self\\_homeomorphism was REMOVED because phi is actually
   DISCONTINUOUS at the dividing line. Only q\\_w \\<circ> phi is continuous (C7 absorbs jumps).
   The correct formulation is directly: top1\\_quotient\\_of\\_scheme\\_on Y\\_w TY\\_w w'.
   This is stated as hYw\\_w' in the proof of theorem\\_76\\_1\\_paste\\_chain\\_proper.
   The proof defines g = q\\_w \\<circ> phi (piecewise: q\\_w \\<circ> phi\\_left on Q1, q\\_w \\<circ> phi\\_right on Q2)
   and verifies that g satisfies all C1-C11 conditions for scheme w':
   - Continuity at dividing line: left gives q\\_w(edge\\_0(s)), right gives q\\_w(edge\\_k(s)),
     matched by C7 for the a-pair.
   - C7 for w': from paste\\_chain\\_boundary\\_C7 (PROVED).
   - C8: each half maps bijectively to a sub-polygon interior, q\\_w injective there.
   - C9: edges map to distinct original edges, q\\_w separates them.\<close>

lemma theorem_76_1_paste_chain:
  assumes hq: "top1_quotient_of_scheme_on Y TY ([(a, True)] @ u2 @ [(a, True)] @ v)"
      and hfresh_c: "c \<notin> fst ` set ([(a, True)] @ u2 @ [(a, True)] @ v)"
  shows "top1_quotient_of_scheme_on Y TY
    ([(c, True)] @ rev (map top1_inverse_edge u2) @ v @ [(c, True)])"
proof -
  let ?w = "[(a, True)] @ u2 @ [(a, True)] @ v"
  let ?n = "length ?w"
  let ?k = "1 + length u2"  \<comment> \<open>Position of the diagonal cut: v\\_0 to v\\_{?k}.\<close>
  let ?w' = "[(c, True)] @ rev (map top1_inverse_edge u2) @ v @ [(c, True)]"
  \<comment> \<open>Step 1: Extract polygon P with vertices vx/vy and quotient map q.\<close>
  from scheme_a_pair_identification[OF hq]
  obtain P q vx vy where
      hP: "top1_is_polygonal_region_on P ?n"
    and hqmap: "top1_quotient_map_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) Y TY q"
    and hv_in: "\<forall>i<?n. (vx i, vy i) \<in> P"
    and hC7_a: "\<forall>t\<in>I_set.
       q ((1-t) * vx 0 + t * vx 1, (1-t) * vy 0 + t * vy 1)
     = q ((1-t) * vx ?k + t * vx (Suc ?k mod ?n),
          (1-t) * vy ?k + t * vy (Suc ?k mod ?n))"
    by (by100 blast)
  \<comment> \<open>Step 2: Vertex identifications from the a-pair.
     q(v\\_0) = q(v\\_{?k}) and q(v\\_1) = q(v\\_{Suc ?k mod n}).\<close>
  have h0_in: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
  have h1_in: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
  have hq_v0: "q (vx 0, vy 0) = q (vx ?k, vy ?k)"
    using hC7_a[rule_format, OF h0_in] by (by100 simp)
  have hq_v1: "q (vx 1, vy 1) = q (vx (Suc ?k mod ?n), vy (Suc ?k mod ?n))"
    using hC7_a[rule_format, OF h1_in] by (by100 simp)
  \<comment> \<open>Step 3: Construct pasted polygon P' for the target scheme w'.
     P' is obtained by cutting P along diagonal v\\_0 to v\\_{?k},
     flipping Q1, permuting Q2, and pasting along the a-edges.
     Geometrically: the two sub-polygons are rearranged and combined.
     For formalization: use scheme\\_quotient\\_exists for proper schemes,
     or construct P' directly as a regular n-gon.\<close>
  \<comment> \<open>Step 4: Define quotient map q': P' \\<to> Y.
     q' is defined piecewise on the two halves of P'
     (separated by the diagonal of P' from the paste junction):
     - On Q1-flipped half: q' = q \\<circ> (un-flip back to Q1 \\<subset> P)
     - On Q2-permuted half: q' = q \\<circ> (un-permute back to Q2 \\<subset> P)
     At the junction (former a-edges): both pieces give the same q-value
     by the a-pair identification (hC7\\_a).
     At the c-edges (diagonal): both pieces map to the diagonal of P,
     approaching from opposite sides.\<close>
  \<comment> \<open>Step 5: Verify that q' is a valid quotient map for scheme w' on P'.
     C1: P' is a valid polygon (from construction)
     C2: q' is a quotient map (continuous closed surjection from compact to Hausdorff)
     C7: edge identifications match w' (c-pair from diagonal, other labels from original)
     C8: interior injectivity (from q's C8 + disjointness of the two halves)
     C9: edge-interior (from original C9 + the piecewise construction)\<close>
  \<comment> \<open>KEY DISCOVERY: The piecewise map IS continuous WITHOUT one-vertex-class.
     At internal junction (former a-edges): C7 with parameter (1-s) gives
       q(first\\_a(1-s)) = q(second\\_a(1-s)), which is exactly what the paste matching needs.
     At paste vertices: C7(t=0) gives q(v\\_0) = q(v\\_{1+|u2|}) and
       C7(t=1) gives q(v\\_1) = q(v\\_{2+|u2| mod n}),
     which are exactly the vertex pairs created by the opposite-exponent paste.\<close>
  \<comment> \<open>The full geometric construction of P' and q' requires:
     1. Define Q1 = sub-polygon {v\\_0,...,v\\_{1+|u2|}} and Q2 = sub-polygon {v\\_{1+|u2|},...,v\\_0}
     2. Q1 and Q2 are valid polygonal regions (from sub\\_polygon\\_in\\_polygon + convexity)
     3. Define pasted polygon P' by geometric placement of Q1-flipped next to Q2-permuted
     4. Define q': P' \\<to> Y piecewise (Q1 half \\<to> Q1 \\<subset> P, Q2 half \\<to> Q2 \\<subset> P)
     5. Verify C1-C11 for P', q', target scheme w'
     The continuity at junctions follows from hC7\\_a (steps hq\\_v0, hq\\_v1 above).\<close>
  \<comment> \<open>Step 6: Extract full C1-C11 from P to get all conditions needed.\<close>
  from quotient_of_scheme_extract_vx[OF hq]
  obtain P2 q2 vx2 vy2 where
      hP2: "top1_is_polygonal_region_on P2 ?n"
    and hq2: "top1_quotient_map_on P2
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P2) Y TY q2"
    and hC3_2: "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> (vx2 i, vy2 i) \<noteq> (vx2 j, vy2 j)"
    and hv2_in: "\<forall>i<?n. (vx2 i, vy2 i) \<in> P2"
    and hC5_2: "P2 = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx2 i)
                     \<and> y = (\<Sum>i<?n. coeffs i * vy2 i)}"
    and hC7_2: "\<forall>i<?n. \<forall>j<?n. fst (?w!i) = fst (?w!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q2 ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))
         = (if snd(?w!i) = snd(?w!j)
            then q2 ((1-t)*vx2 j + t*vx2(Suc j mod ?n), (1-t)*vy2 j + t*vy2(Suc j mod ?n))
            else q2 (t*vx2 j + (1-t)*vx2(Suc j mod ?n), t*vy2 j + (1-t)*vy2(Suc j mod ?n))))"
    and hC8_2: "\<forall>p\<in>P2. (\<forall>i<?n. \<forall>t\<in>I_set.
              p \<noteq> ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)))
           \<longrightarrow> (\<forall>p'\<in>P2. q2 p = q2 p' \<longrightarrow> p = p')"
    and hC9_2: "\<forall>i<?n. \<forall>j<?n. \<forall>t\<in>{0<..<(1::real)}. \<forall>s\<in>{0<..<(1::real)}.
          q2 ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))
        = q2 ((1-s)*vx2 j + s*vx2(Suc j mod ?n), (1-s)*vy2 j + s*vy2(Suc j mod ?n))
        \<longrightarrow> (i = j \<and> t = s) \<or> (fst(?w!i) = fst(?w!j) \<and>
              (if snd(?w!i) = snd(?w!j) then s = t else s = 1 - t))"
    by (rule quotient_of_scheme_extract_vx[OF hq])
  \<comment> \<open>PROOF OF THEOREM 76.1 (CUT+FLIP+PASTE CHAIN).
     Strategy: use SAME polygon P2 with vertices vx2/vy2 as witness for scheme w'.
     Define new quotient map g: P2 \\<to> Y that follows the target scheme w'.

     BOUNDARY MAP g (edge-by-edge):
     - Edge 0 of P2 at param t (c,T): g = q2(diagonal from v\\_0 to v\\_{k+1} at param t)
       = q2((1-t)*vx2 0+t*vx2(k+1), (1-t)*vy2 0+t*vy2(k+1))
     - Edge i (1\\<le>i\\<le>k) at param t (inv(u2)): g = q2(REVERSED edge k+1-i at param 1-t)
       = q2(t*vx2(k+1-i)+(1-t)*vx2(k+2-i), t*vy2(k+1-i)+(1-t)*vy2(k+2-i))
     - Edge i (k+1\\<le>i\\<le>n-2) at param t (v): g = q2(original edge i+1 at param t)
       = q2((1-t)*vx2(i+1)+t*vx2(Suc(i+1) mod n), (1-t)*vy2(i+1)+t*vy2(Suc(i+1) mod n))
     - Edge n-1 at param t (c,T): SAME as edge 0 (same diagonal, same parameter)
       = q2((1-t)*vx2 0+t*vx2(k+1), (1-t)*vy2 0+t*vy2(k+1))

     INTERIOR: half-and-half extension via sub-polygon homeomorphisms.
     Left half (edges 0..k + dividing line) maps to Q1 = conv(v\\_0,...,v\\_{k+1}).
     Right half (edges k+1..n-1 + dividing line) maps to Q2 = conv(v\\_{k+1},...,v\\_0).
     At dividing line: left gives q2(edge\\_0(s)), right gives q2(edge\\_{k+1}(s)).
     These match by C7 for the a-pair (hC7\\_a at param s). \\<checkmark>

     JUNCTION CONTINUITY (all verified):
     v'(0): edge(n-1,1)=q2(v(k+1)), edge(0,0)=q2(v(0)). Match by hq\\_v0.
     v'(1): edge(0,1)=q2(v(k+1)), edge(1,0)=q2(v(k+1)).
     v'(i) (2<=i<=k): edge(i-1,1)=q2(v(k+2-i)), edge(i,0)=q2(v(k+2-i)).
     v'(k+1): edge(k,1)=q2(v(1)), edge(k+1,0)=q2(v(k+2)). Match by hq\\_v1.
     v'(i) (k+2<=i<=n-2): edge(i-1,1)=q2(v(i+1)), edge(i,0)=q2(v(i+1)).
     v'(n-1): edge(n-2,1)=q2(v(0)), edge(n-1,0)=q2(v(0)).

     C7 (target scheme w'):
     - c-pair (0,n-1): both map to q2(diagonal(t)). Same exponent \\<to> same param. \\<checkmark>
     - inv(u2) pairs: target param t \\<to> original param (1-t). Double negation
       (reversed param + flipped exponent) makes C7 work. \\<checkmark>
     - v pairs: direct from original C7 at shifted indices. \\<checkmark>
     - Cross pairs (inv(u2) vs v): reversed param + flipped exponent cancel. \\<checkmark>
     - c vs non-c: can't have same label (c is fresh). \\<checkmark>

     C8 (interior injectivity): half-and-half maps each half injectively.
     Interior Q1 and Q2 are disjoint. q2 injective on interior by C8. \\<checkmark>

     C9 (edge-edge injectivity):
     - c vs non-c: diagonal is interior, edges are boundary. C8 separates. \\<checkmark>
     - c vs c: q2 injective on diagonal (interior). \\<checkmark>
     - non-c pairs: follows from original C9. \\<checkmark>\<close>
  \<comment> \<open>Step 10: Construct the witness for top1\\_quotient\\_of\\_scheme\\_on Y TY w'.
     WITNESS: P = P2 (same polygon), vx = vx2, vy = vy2.
     Need a new quotient map g: P2 \\<to> Y defined piecewise.
     BOUNDARY MAP g(edge'(i, t)):
     - i = 0 or n-1 (c-pair): q2((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k) [diagonal]
     - 1 \\<le> i \\<le> |u2| (inv(u2)): q2(t*vx2(?k-i) + (1-t)*vx2(?k+1-i), ...) [reversed u2 edge]
     - |u2|+1 \\<le> i \\<le> n-2 (v): q2((1-t)*vx2(i+1) + t*vx2(Suc(i+1) mod n), ...) [original v edge]
     INTERIOR: half-and-half piecewise extension through sub-polygons Q1, Q2.\<close>
  \<comment> \<open>CONSTRUCTION: define boundary map g on P2 (same polygon, new quotient map).
     g(edge\\_i, t) for target scheme w':
     - i = 0 or n-1 (c-pair): q2((1-t)*v0 + t*v(k), (1-t)*vy0 + t*vy(k))
     - 1 \\<le> i \\<le> |u2| (inv(u2)): q2(t*v(k-i) + (1-t)*v(k+1-i), ...)
     - |u2|+1 \\<le> i \\<le> n-2 (v): q2((1-t)*v(i+1) + t*v(Suc(i+1) mod n), ...)
     Interior: half-and-half via sub-polygon homeomorphisms (Q1 left, Q2 right).
     All junction continuity, C7, C8, C9 verified mathematically (see comments above).\<close>
  \<comment> \<open>Step 11: Extract topology\\_on\\_strict from hq.\<close>
  have htopo_Y: "is_topology_on_strict Y TY"
    using hq unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  have hlen_eq: "length ?w' = ?n" by (by100 simp)
  \<comment> \<open>Step 12: Construct the map g: P2 -> Y satisfying C7/C8/C9 for scheme w'.
     g is defined piecewise on the boundary:
     - c-edges (0, n-1): map to the diagonal q2(v0..v(k+1))
     - inv(u2) edges (1..k): map to reversed original u2 edges
     - v edges (k+1..n-2): map to original v edges
     Interior: half-and-half extension through sub-polygons.
     The construction and verification of all conditions uses the half-and-half
     approach documented in the PROOF OF THEOREM 76.1 comment block above.\<close>
  \<comment> \<open>For now: sorry the full construction. The mathematical proof is complete
     (all junction continuity, C7 cases, C8, C9 verified in comments above).
     The formal verification requires defining g, proving continuity,
     and verifying C7/C8/C9 as separate sub-goals (~380 lines total).

     KEY FACT: the proof uses ONLY the following from the original quotient:
     - hC7\\_2: edge identifications for scheme w (especially the a-pair)
     - hC8\\_2: interior injectivity of q2
     - hC9\\_2: edge-edge injectivity of q2
     - hq\\_v0, hq\\_v1: vertex identifications from the a-pair
     All other conditions (C1-C6, C10, C11) are pure polygon properties
     inherited from P2 unchanged.\<close>
  \<comment> \<open>Unfold the definition and provide witnesses.\<close>
  show "top1_quotient_of_scheme_on Y TY ?w'"
    unfolding top1_quotient_of_scheme_on_def
  proof (intro conjI)
    show "is_topology_on_strict Y TY" by (rule htopo_Y)
  next
    \<comment> \<open>Need: \\<exists>P q vx vy. C1 \\<and> C2 \\<and> ... \\<and> C11 for scheme w' on P with map q.
       Witness: P = P2, q = g (piecewise map), vx = vx2, vy = vy2.
       g is defined by the half-and-half construction:
       - On boundary: edge-by-edge map to original polygon (diagonal for c-edges)
       - On interior: piecewise extension through sub-polygon homeomorphisms\<close>
    \<comment> \<open>Witness: P = P2 (same polygon), vx = vx2, vy = vy2.
       g = the half-and-half piecewise quotient map (construction sorry'd).
       C1, C3-C6, C10, C11: inherit from P2 via hlen\\_eq (length w' = length w = n).
       C2, C7, C8, C9: need the new map g.\<close>
    \<comment> \<open>Inherit polygon properties from P2 (same polygon, same vertices, same length).\<close>
    have hC1': "top1_is_polygonal_region_on P2 (length ?w')"
      using hP2 hlen_eq by simp
    have hC3': "\<forall>i<length ?w'. \<forall>j<length ?w'. i \<noteq> j \<longrightarrow> (vx2 i, vy2 i) \<noteq> (vx2 j, vy2 j)"
      using hC3_2 hlen_eq by simp
    have hC4': "\<forall>i<length ?w'. (vx2 i, vy2 i) \<in> P2"
      using hv2_in hlen_eq by simp
    have hC5': "P2 = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<length ?w'. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<length ?w'. coeffs i) = 1
                     \<and> x = (\<Sum>i<length ?w'. coeffs i * vx2 i)
                     \<and> y = (\<Sum>i<length ?w'. coeffs i * vy2 i)}"
      using hC5_2 hlen_eq by simp
    \<comment> \<open>C2 (quotient map g: P2 -> Y), C7, C8, C9 for scheme w' with map g.
       These require the full geometric half-and-half construction.
       Sorry'd: the mathematical argument is complete (see comments above).\<close>
    \<comment> \<open>The existential needs a quotient map q on P2 satisfying C2+C7+C8+C9.
       C7 is now proved (paste\\_chain\\_boundary\\_C7). C2/C8/C9 need the geometric construction.
       The geometric part requires defining q on the interior of P2 via half-and-half
       extension, proving continuity, surjectivity, and injectivity properties.
       For now: sorry the full existential. The C7 part can be closed once q is defined.\<close>
    show "\<exists>P q (vx::nat\<Rightarrow>real) vy.
        top1_is_polygonal_region_on P (length ?w')
      \<and> top1_quotient_map_on P
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) Y TY q
      \<and> (\<forall>i<length ?w'. \<forall>j<length ?w'. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j))
      \<and> (\<forall>i<length ?w'. (vx i, vy i) \<in> P)
      \<and> P = {(x, y) | x y.
                \<exists>coeffs. (\<forall>i<length ?w'. coeffs i \<ge> 0)
                       \<and> (\<Sum>i<length ?w'. coeffs i) = 1
                       \<and> x = (\<Sum>i<length ?w'. coeffs i * vx i)
                       \<and> y = (\<Sum>i<length ?w'. coeffs i * vy i)}
      \<and> (\<forall>i<length ?w'. \<forall>j<length ?w'.
            i \<noteq> j \<longrightarrow> Suc i mod length ?w' \<noteq> j \<longrightarrow> i \<noteq> Suc j mod length ?w' \<longrightarrow>
            (\<forall>s\<in>{0<..<1}. \<forall>t\<in>{0<..<1}.
               ((1-s) * vx i + s * vx (Suc i mod length ?w'),
                (1-s) * vy i + s * vy (Suc i mod length ?w'))
             \<noteq> ((1-t) * vx j + t * vx (Suc j mod length ?w'),
                (1-t) * vy j + t * vy (Suc j mod length ?w'))))
      \<and> (\<forall>i<length ?w'. \<forall>j<length ?w'. fst (?w'!i) = fst (?w'!j) \<longrightarrow>
            (\<forall>t\<in>I_set.
               q ((1-t) * vx i + t * vx (Suc i mod length ?w'),
                  (1-t) * vy i + t * vy (Suc i mod length ?w'))
             = (if snd (?w'!i) = snd (?w'!j)
                then q ((1-t) * vx j + t * vx (Suc j mod length ?w'),
                        (1-t) * vy j + t * vy (Suc j mod length ?w'))
                else q (t * vx j + (1-t) * vx (Suc j mod length ?w'),
                        t * vy j + (1-t) * vy (Suc j mod length ?w')))))
      \<and> (\<forall>p\<in>P. (\<forall>i<length ?w'. \<forall>t\<in>I_set.
                    p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length ?w'),
                          (1-t) * vy i + t * vy (Suc i mod length ?w')))
               \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p'))
      \<and> (\<forall>i<length ?w'. \<forall>j<length ?w'. \<forall>t\<in>{0<..<(1::real)}. \<forall>s\<in>{0<..<(1::real)}.
              q ((1-t) * vx i + t * vx (Suc i mod length ?w'),
                 (1-t) * vy i + t * vy (Suc i mod length ?w'))
            = q ((1-s) * vx j + s * vx (Suc j mod length ?w'),
                 (1-s) * vy j + s * vy (Suc j mod length ?w'))
            \<longrightarrow> (i = j \<and> t = s)
              \<or> (fst (?w'!i) = fst (?w'!j) \<and>
                 (if snd (?w'!i) = snd (?w'!j) then s = t else s = 1 - t)))
      \<and> (\<forall>i<length ?w'. let cx = (\<Sum>j<length ?w'. vx j) / real (length ?w');
                               cy = (\<Sum>j<length ?w'. vy j) / real (length ?w')
           in (vx i - cx) * (vy (Suc i mod length ?w') - cy)
            - (vy i - cy) * (vx (Suc i mod length ?w') - cx) > 0)
      \<and> (\<forall>i<length ?w'. \<forall>k<length ?w'.
            k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod length ?w' \<longrightarrow>
            (vx k - vx i) * (vy (Suc i mod length ?w') - vy i)
            - (vy k - vy i) * (vx (Suc i mod length ?w') - vx i) < 0)"
      sorry \<comment> \<open>REMAINING SORRY: existential witness with geometric map.
         C1,C3,C4,C5: proved (hC1',hC3',hC4',hC5').
         C6,C10,C11: can be inherited from P2 via hlen\\_eq.
         C7: PROVED as paste\\_chain\\_boundary\\_C7 (needs instantiation with q).
         C2,C8,C9: require defining q on interior (half-and-half construction).
         The C7 proof is a major algebraic result (~800 lines).
         Once q is defined, C7 follows from the proved lemma.\<close>
  qed
qed

\<comment> \<open>PROPER VERSION of theorem\\_76\\_1\\_paste\\_chain.
   For proper nat schemes: uses scheme\\_quotient\\_exists for target scheme,
   constructs homeomorphism via piecewise map \\<psi>: P' \\<to> P2 (regular n-gon to source polygon),
   then transfers quotient via scheme\\_quotient\\_transfer\\_along\\_homeomorphism.
   This avoids constructing the geometric paste polygon entirely!\<close>
\<comment> \<open>PROPER VERSION: delegates to general theorem\\_76\\_1\\_paste\\_chain.
   The properness assumption could enable an alternative proof via
   scheme\\_quotient\\_exists + uniqueness if the general version were unavailable.\<close>
lemma theorem_76_1_paste_chain_proper:
  fixes a c :: nat and u2 v :: "(nat \<times> bool) list"
  assumes hq: "top1_quotient_of_scheme_on Y TY ([(a, True)] @ u2 @ [(a, True)] @ v)"
      and hfresh_c: "c \<notin> fst ` set ([(a, True)] @ u2 @ [(a, True)] @ v)"
      and hproper: "\<forall>label. card {i. i < length ([(a, True)] @ u2 @ [(a, True)] @ v)
            \<and> fst (([(a, True)] @ u2 @ [(a, True)] @ v) ! i) = label} \<in> {0, 2}"
  shows "top1_quotient_of_scheme_on Y TY
    ([(c, True)] @ rev (map top1_inverse_edge u2) @ v @ [(c, True)])"
  using theorem_76_1_paste_chain[OF hq hfresh_c] .

\<comment> \<open>MULTI-POLYGON CUT-FLIP-PASTE CORE (Munkres Theorem 76.1 application).
   Proof chain (book-faithful, step by step):
   1. Extract polygon P, vertices vx/vy, quotient map q from the given quotient
   2. CUT P along diagonal from v\\_0 to v\\_{1+|u2|}:
      Q1 = sub-polygon with edges [(a,T)] @ u2 @ [(c,F)]  (k1 = |u2|+2 edges)
      Q2 = sub-polygon with edges [(c,T)] @ [(a,T)] @ v   (k2 = |v|+2 edges)
   3. Define two-polygon quotient map f: Q1 \\<squnion> Q2 \\<to> Y via q restricted to each piece
   4. FLIP Q1: scheme becomes [(c,T)] @ inv(u2) @ [(a,F)]
      (geometrically: reverse Q1's boundary traversal, flip exponents)
   5. PERMUTE Q2: scheme becomes [(a,T)] @ v @ [(c,T)]
      (geometrically: cyclic rotation of Q2's vertex numbering)
   6. PASTE along a: merge Q1' and Q2' identifying (a,F) and (a,T) edges
      Result: single polygon P' with scheme [(c,T)] @ inv(u2) @ v @ [(c,T)]
      Quotient: the composed map P' \\<to> Y is a valid quotient map (Theorem 76.1)
   7. RELABEL c\\<to>a: same quotient Y for scheme [(a,T)] @ inv(u2) @ v @ [(a,T)]
   8. ROTATE: same quotient Y for scheme [(a,T),(a,T)] @ inv(u2) @ v\<close>
lemma cut_flip_paste_core:
  assumes "top1_quotient_of_scheme_on Y TY ([(a, True)] @ u2 @ [(a, True)] @ v)"
  shows "top1_quotient_of_scheme_on Y TY ([(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ v)"
proof -
  \<comment> \<open>Step 1: Apply Theorem 76.1 paste chain to get quotient of c@inv(u2)@v@c.\<close>
  let ?labels = "fst ` set ([(a, True)] @ u2 @ [(a, True)] @ v)"
  have hfin: "finite ?labels" by (by100 simp)
  obtain c :: "'b" where hfresh: "c \<notin> ?labels"
    sorry \<comment> \<open>Fresh label exists. For nat: pick max+1. For general 'b: needs infinite type.\<close>
  from theorem_76_1_paste_chain[OF assms hfresh]
  have h1: "top1_quotient_of_scheme_on Y TY
    ([(c, True)] @ rev (map top1_inverse_edge u2) @ v @ [(c, True)])" .
  \<comment> \<open>Step 2: RELABEL c \\<to> a. Fresh since a \\<notin> labels of c@inv(u2)@v@c
     (because a only appeared in the two explicit positions, now replaced by c).\<close>
  \<comment> \<open>Actually: a MAY appear in u2 or v! For properness, a appears exactly twice
     (the two explicit positions). So a \\<notin> fst ` set u2 and a \\<notin> fst ` set v.
     Hence a \\<notin> fst ` set (inv(u2)) and a \\<notin> fst ` set v.
     So a \\<notin> fst ` set (c@inv(u2)@v@c) (since c \\<noteq> a by freshness of c).
     Therefore relabel c\\<to>a is fresh.\<close>
  \<comment> \<open>For the general case (non-proper): a might appear in u2 or v.
     In that case, relabel c\\<to>a creates non-fresh relabeling.
     For now: sorry this step and handle properness separately.\<close>
  have h2: "top1_quotient_of_scheme_on Y TY
    ([(a, True)] @ rev (map top1_inverse_edge u2) @ v @ [(a, True)])"
    sorry \<comment> \<open>RELABEL c\\<to>a on scheme from h1. Needs freshness of a in the c-scheme.\<close>
  \<comment> \<open>Step 3: ROTATE: move last element to second position.\<close>
  from quotient_of_scheme_rotate[OF h2]
  have h3: "top1_quotient_of_scheme_on Y TY
    (rev (map top1_inverse_edge u2) @ v @ [(a, True)] @ [(a, True)])" by simp
  from quotient_of_scheme_rotate[OF h3]
  have h4: "top1_quotient_of_scheme_on Y TY
    (v @ [(a, True)] @ [(a, True)] @ rev (map top1_inverse_edge u2))" by simp
  from quotient_of_scheme_rotate[OF h4]
  have h5: "top1_quotient_of_scheme_on Y TY
    ([(a, True)] @ [(a, True)] @ rev (map top1_inverse_edge u2) @ v)" by simp
  thus ?thesis by simp
qed
\<comment> \<open>NOTE: cut\\_flip\\_paste\\_core uses two sorrys:
   1. theorem\\_76\\_1\\_paste\\_chain (Theorem 76.1 paste)
   2. Fresh label existence + RELABEL step
   The RELABEL sorry can be closed for proper schemes (a \\<notin> fst ` set u2 \\<union> fst ` set v).\<close>

\<comment> \<open>PROPER VERSION: for nat-typed proper schemes where a appears only at the two
   explicit positions, the fresh label and relabel steps can be closed.
   Only theorem\\_76\\_1\\_paste\\_chain remains as sorry.\<close>
lemma cut_flip_paste_core_proper:
  fixes a :: nat
  assumes hq: "top1_quotient_of_scheme_on Y TY ([(a, True)] @ u2 @ [(a, True)] @ v)"
      and ha_fresh_u2: "a \<notin> fst ` set u2"
      and ha_fresh_v: "a \<notin> fst ` set v"
      and hproper_src: "\<forall>label. card {i. i < length ([(a, True)] @ u2 @ [(a, True)] @ v)
            \<and> fst (([(a, True)] @ u2 @ [(a, True)] @ v) ! i) = label} \<in> {0, 2}"
  shows "top1_quotient_of_scheme_on Y TY ([(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ v)"
proof -
  let ?w = "[(a, True)] @ u2 @ [(a, True)] @ v"
  let ?labels = "fst ` set ?w"
  \<comment> \<open>Step 1: Get fresh label c (nat, so infinite UNIV).\<close>
  have hfin: "finite ?labels" by (by100 simp)
  from ex_new_if_finite[OF infinite_UNIV_nat hfin]
  obtain c :: nat where hfresh_c: "c \<notin> ?labels" by (by100 blast)
  \<comment> \<open>Step 2: Apply theorem\\_76\\_1\\_paste\\_chain\\_proper (uses scheme\\_quotient\\_exists).\<close>
  from theorem_76_1_paste_chain_proper[OF hq hfresh_c hproper_src]
  have h1: "top1_quotient_of_scheme_on Y TY
    ([(c, True)] @ rev (map top1_inverse_edge u2) @ v @ [(c, True)])" .
  \<comment> \<open>Step 3: RELABEL c \\<to> a. Fresh because a \\<notin> labels of c-scheme.\<close>
  have ha_ne_c: "a \<noteq> c" using hfresh_c by (by100 auto)
  have hfst_inv: "\<And>e. e \<in> set u2 \<Longrightarrow> fst (top1_inverse_edge e) = fst e"
    unfolding top1_inverse_edge_def by (by100 auto)
  have hfst_inv_set: "fst ` set (map top1_inverse_edge u2) = fst ` set u2"
    unfolding top1_inverse_edge_def by (by100 force)
  have ha_fresh_inv: "a \<notin> fst ` set (rev (map top1_inverse_edge u2))"
    using ha_fresh_u2 hfst_inv_set by (by100 simp)
  have ha_fresh_w': "a \<notin> fst ` set ([(c, True)] @ rev (map top1_inverse_edge u2) @ v @ [(c, True)])"
    using ha_ne_c ha_fresh_inv ha_fresh_v by (by100 auto)
  from quotient_of_scheme_relabel_fresh[OF h1 ha_fresh_w' ha_ne_c]
  have h2: "top1_quotient_of_scheme_on Y TY
    (map (\<lambda>(l,b). (if l = c then a else l, b)) ([(c, True)] @ rev (map top1_inverse_edge u2) @ v @ [(c, True)]))" .
  \<comment> \<open>Simplify: relabeling c\\<to>a changes only the c entries.\<close>
  have hmap_eq: "map (\<lambda>(l,b). (if l = c then a else l, b))
    ([(c, True)] @ rev (map top1_inverse_edge u2) @ v @ [(c, True)])
    = [(a, True)] @ rev (map top1_inverse_edge u2) @ v @ [(a, True)]"
  proof -
    have hmap_c: "map (\<lambda>(l,b). (if l = c then a else l, b)) [(c, True)] = [(a, True)]"
      by (by100 simp)
    have hmap_inv: "map (\<lambda>(l,b). (if l = c then a else l, b)) (rev (map top1_inverse_edge u2))
        = rev (map top1_inverse_edge u2)"
    proof (rule map_idI)
      fix x assume "x \<in> set (rev (map top1_inverse_edge u2))"
      hence "fst x \<in> fst ` set (rev (map top1_inverse_edge u2))" by (by100 auto)
      hence "fst x \<noteq> c"
      proof -
        have "c \<notin> fst ` set (rev (map top1_inverse_edge u2))"
        proof -
          have "fst ` set (rev (map top1_inverse_edge u2)) = fst ` set (map top1_inverse_edge u2)"
            by (by100 simp)
          also have "\<dots> = fst ` set u2"
          proof (rule set_eqI)
            fix x show "x \<in> fst ` set (map top1_inverse_edge u2) \<longleftrightarrow> x \<in> fst ` set u2"
              unfolding top1_inverse_edge_def by (by100 force)
          qed
          also have "c \<notin> \<dots>" using hfresh_c by (by100 auto)
          finally show ?thesis .
        qed
        thus ?thesis using \<open>fst x \<in> fst ` set (rev (map top1_inverse_edge u2))\<close> by (by100 blast)
      qed
      thus "(case x of (l, b) \<Rightarrow> (if l = c then a else l, b)) = x"
        using \<open>fst x \<noteq> c\<close> by (cases x) (by100 simp)
    qed
    have hmap_v: "map (\<lambda>(l,b). (if l = c then a else l, b)) v = v"
    proof (rule map_idI)
      fix x assume "x \<in> set v"
      hence "fst x \<in> fst ` set v" by (by100 auto)
      hence "fst x \<noteq> c" using hfresh_c by (by100 auto)
      thus "(case x of (l, b) \<Rightarrow> (if l = c then a else l, b)) = x"
        using \<open>fst x \<noteq> c\<close> by (cases x) (by100 simp)
    qed
    show ?thesis using hmap_c hmap_inv hmap_v by (by100 simp)
  qed
  from h2[unfolded hmap_eq]
  have h3: "top1_quotient_of_scheme_on Y TY
    ([(a, True)] @ rev (map top1_inverse_edge u2) @ v @ [(a, True)])" .
  \<comment> \<open>Step 4: ROTATE to final form.\<close>
  from quotient_of_scheme_rotate[OF h3]
  have "top1_quotient_of_scheme_on Y TY
    (rev (map top1_inverse_edge u2) @ v @ [(a, True)] @ [(a, True)])" by simp
  from quotient_of_scheme_rotate[OF this]
  have "top1_quotient_of_scheme_on Y TY
    (v @ [(a, True)] @ [(a, True)] @ rev (map top1_inverse_edge u2))" by simp
  from quotient_of_scheme_rotate[OF this]
  have "top1_quotient_of_scheme_on Y TY
    ([(a, True)] @ [(a, True)] @ rev (map top1_inverse_edge u2) @ v)" by simp
  thus ?thesis by simp
qed

lemma quotient_of_scheme_cut_paste:
  assumes "top1_quotient_of_scheme_on Y TY (u1 @ [(a, True)] @ u2 @ [(a, True)] @ u3)"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' (u1 @ [(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3) \<and>
    top1_homeomorphism_on Y TY Y' TY' h"
proof -
  \<comment> \<open>Reduce to the u1=[] case via ROTATE.
     ROTATE: u1@a@u2@a@u3 to a@u2@a@u3@u1.
     Apply CUT-PASTE (u1=[]) to get: a@a@inv(u2)@u3@u1.
     ROTATE back: u1@a@a@inv(u2)@u3.\<close>
  have hrot: "top1_quotient_of_scheme_on Y TY ([(a, True)] @ u2 @ [(a, True)] @ u3 @ u1)"
    using quotient_of_scheme_rotate[OF assms] by simp
  \<comment> \<open>Apply CUT-PASTE for the u1=[] case.
     Need: Y quotient of a@u2@a@(u3@u1) implies Y quotient of a@a@inv(u2)@(u3@u1).\<close>
  have hcore: "top1_quotient_of_scheme_on Y TY
      ([(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3 @ u1)"
    by (rule cut_flip_paste_core[OF hrot])
  \<comment> \<open>Step C: ROTATE back to get u1 to the front.\<close>
  have hrewrite: "([(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3 @ u1)
      = ([(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3) @ u1"
    by simp
  from quotient_of_scheme_rotate[OF hcore[unfolded hrewrite]]
  have "top1_quotient_of_scheme_on Y TY
      (u1 @ ([(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3))"
    by simp
  hence "top1_quotient_of_scheme_on Y TY
      (u1 @ [(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3)"
    by simp
  thus ?thesis by (rule same_space_implies_homeo_realization_early)
qed

\<comment> \<open>Munkres Lemma 77.1 Step 1: a[y1]a[y2] ~ aa[y1^{-1} y2].
   This is quotient\\_of\\_scheme\\_cut\\_paste with u1=[], u2=y1, u3=y2.\<close>
lemma Lemma_77_1_step1:
  fixes a_label :: nat and y1 y2 :: "(nat \<times> bool) list"
  assumes hq: "top1_quotient_of_scheme_on Y TY
      ([(a_label, True)] @ y1 @ [(a_label, True)] @ y2)"
      and hlen: "length y1 \<ge> 1" "length y2 \<ge> 1"
      and hproper: "\<forall>label. card {i. i < length ([(a_label, True)] @ y1 @ [(a_label, True)] @ y2)
          \<and> fst (([(a_label, True)] @ y1 @ [(a_label, True)] @ y2) ! i) = label} \<in> {0, 2}"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY'
      ([(a_label, True), (a_label, True)] @ rev (map top1_inverse_edge y1) @ y2) \<and>
    top1_homeomorphism_on Y TY Y' TY' h"
proof -
  \<comment> \<open>Delegates to quotient\\_of\\_scheme\\_cut\\_paste with u1=[], u2=y1, u3=y2.\<close>
  have "top1_quotient_of_scheme_on Y TY ([] @ [(a_label, True)] @ y1 @ [(a_label, True)] @ y2)"
    using hq by simp
  from quotient_of_scheme_cut_paste[OF this]
  show ?thesis by simp
qed

lemma quotient_of_scheme_cut_paste2:
  assumes "top1_quotient_of_scheme_on Y TY (u0 @ [(a, True)] @ u1 @ [(a, True)] @ u2)"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' ([(b, True)] @ u2 @ [(b, True)] @ u1 @ rev (map top1_inverse_edge u0)) \<and>
    top1_homeomorphism_on Y TY Y' TY' h"
proof -
  \<comment> \<open>Derivation via multi-polygon CUT+FLIP+PASTE (Figure 77.2):
     CUT at position |u0|: P1 = u0@c^{-1}, P2 = c@a@u1@a@u2
     FLIP P1: c@inv(u0)
     Apply cut\\_flip\\_paste\\_core to P2 (treating c as prefix): c@a@a@inv(u1)@u2
     Wait - can't apply single-polygon cut-paste to P2 in a multi-polygon context.
     Need direct multi-polygon argument for Figure 77.2.\<close>
  have "top1_quotient_of_scheme_on Y TY ([(b, True)] @ u2 @ [(b, True)] @ u1 @ rev (map top1_inverse_edge u0))"
    sorry \<comment> \<open>CUT-PASTE variant 2 (Figure 77.2). Needs own multi-polygon chain:
       CUT between u0 and first a, FLIP Q1, PERMUTE both, PASTE along a.
       Same fundamental technique as cut\\_flip\\_paste\\_core but different cut position.\<close>
  thus ?thesis by (rule same_space_implies_homeo_realization_early)
qed

lemma quotient_of_scheme_cut_paste_opp:
  assumes "top1_quotient_of_scheme_on Y TY (u0 @ u1 @ [(a, True)] @ u2 @ [(a, False)] @ u3)"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' (u0 @ [(a, True)] @ u2 @ [(a, False)] @ u1 @ u3) \<and>
    top1_homeomorphism_on Y TY Y' TY' h"
proof -
  \<comment> \<open>Multi-polygon CUT+PERMUTE+PASTE for opposite-direction labels.
     CUT between u0@u1 and [(a,T)]:
       P1 = u0@u1@c^{-1}, P2 = c@[(a,T)]@u2@[(a,F)]@u3
     PERMUTE P2 to rotate u1's worth of material:
       P2 rotated = [(a,T)]@u2@[(a,F)]@u3@c  (move c from front to end)
     Wait: pasting P1@c^{-1} with c@... gives back original.
     Instead: PERMUTE P2 = u3@c@[(a,T)]@u2@[(a,F)] (different rotation)
     Then PASTE: u0@u1@u3@[(a,T)]@u2@[(a,F)] (wrong).
     The correct approach for cut-paste-opp uses PASTE along c AFTER permuting.\<close>
  have "top1_quotient_of_scheme_on Y TY (u0 @ [(a, True)] @ u2 @ [(a, False)] @ u1 @ u3)"
    sorry \<comment> \<open>Multi-polygon CUT+PERMUTE+PASTE for opposite-direction cut-paste.
       Same fundamental technique as cut\\_flip\\_paste\\_core.\<close>
  thus ?thesis by (rule same_space_implies_homeo_realization_early)
qed

\<comment> \<open>Scheme quotient existence: every scheme of length \\<ge> 3 has a quotient realization.
   Construction: regular n-gon P with vertices at (cos(2\\<pi>k/n), sin(2\\<pi>k/n)).
   Quotient map q identifies boundary edges according to the scheme.
   This is a key missing lemma — once proved, all geometric gaps become easy.\<close>
\<comment> \<open>Previously sorry. Now follows directly from scheme\\_quotient\\_exists(2).
     The vertex-edge separation follows from hnotvertex\\_gen: the q image of a vertex is
     (vx(vtgt k), vy(vtgt k)) which is a vertex, while q image of edge\\_pt(j,s) is an edge point.
     By edge\\_interior\\_not\\_vertex, these are disjoint.
     TO PROVE: need to modify scheme\\_quotient\\_exists to output the extra property,
     or duplicate enough of the construction to derive it.
     from hnotvertex\\_gen applied to the 3-branch q definition.\<close>

\<comment> \<open>front\\_cancel\\_proper is defined after scheme\\_quotient\\_uniqueness (line ~4828).\<close>

\<comment> \<open>Cancel at front — homeomorphic-realization form (per expert audit 21 step 4).
   Given quotient of [a,inv a]@w, produce a (possibly different) quotient of w
   that is homeomorphic. This is WEAKER than same-space preservation.\<close>
lemma front_cancel_realization_homeo:
  fixes Y :: "'a set" and TY :: "'a set set"
  assumes "top1_quotient_of_scheme_on Y TY ([a, top1_inverse_edge a] @ w)"
      and "length w \<ge> 3"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' w \<and>
    top1_homeomorphism_on Y TY Y' TY' h"
  sorry \<comment> \<open>General cancel (no properness/freshness).
     For proper + fresh: use front\\_cancel\\_proper (PROVED, defined later in file).
     For non-proper or non-fresh: sorry pending.\<close>

\<comment> \<open>Uncancel same-space: if Y is quotient of w, then Y is also quotient of [a,inv a]@w.
   The additional cancelling pair creates a spur that collapses to nothing.
   Proof deferred — needs geometric spur insertion or canonical quotients + transfer lemma.\<close>
lemma quotient_of_scheme_uncancel_front:
  assumes "top1_quotient_of_scheme_on Y TY w"
      and "length w \<ge> 3"
  shows "top1_quotient_of_scheme_on Y TY ([a, top1_inverse_edge a] @ w)"
proof -
  let ?n = "length w"
  let ?ext = "[a, top1_inverse_edge a] @ w"
  \<comment> \<open>Step 1: Extract polygon P, quotient map q, and full C1-C11 from Y quotient of w.\<close>
  from quotient_of_scheme_extract_vx[OF assms(1)]
  obtain P q vx vy where
      hC1: "top1_is_polygonal_region_on P ?n"
    and hC2: "top1_quotient_map_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) Y TY q"
    and hC3: "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)"
    and hC4: "\<forall>i<?n. (vx i, vy i) \<in> P"
    and hC5: "P = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx i)
                     \<and> y = (\<Sum>i<?n. coeffs i * vy i)}"
    and hC6: "\<forall>i<?n. \<forall>j<?n.
          i \<noteq> j \<longrightarrow> Suc i mod ?n \<noteq> j \<longrightarrow> i \<noteq> Suc j mod ?n \<longrightarrow>
          (\<forall>s\<in>{0<..<1::real}. \<forall>t\<in>{0<..<1::real}.
             ((1-s) * vx i + s * vx (Suc i mod ?n),
              (1-s) * vy i + s * vy (Suc i mod ?n))
           \<noteq> ((1-t) * vx j + t * vx (Suc j mod ?n),
               (1-t) * vy j + t * vy (Suc j mod ?n)))"
    and hC7: "\<forall>i<?n. \<forall>j<?n. fst (w!i) = fst (w!j) \<longrightarrow>
        (\<forall>t\<in>I_set.
           q ((1-t) * vx i + t * vx (Suc i mod ?n),
              (1-t) * vy i + t * vy (Suc i mod ?n))
         = (if snd (w!i) = snd (w!j)
            then q ((1-t) * vx j + t * vx (Suc j mod ?n),
                    (1-t) * vy j + t * vy (Suc j mod ?n))
            else q (t * vx j + (1-t) * vx (Suc j mod ?n),
                    t * vy j + (1-t) * vy (Suc j mod ?n))))"
    and hC8: "\<forall>p\<in>P. (\<forall>i<?n. \<forall>t\<in>I_set.
                p \<noteq> ((1-t) * vx i + t * vx (Suc i mod ?n),
                      (1-t) * vy i + t * vy (Suc i mod ?n)))
             \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
    and hC9: "\<forall>i<?n. \<forall>j<?n. \<forall>t\<in>{0<..<(1::real)}. \<forall>s\<in>{0<..<(1::real)}.
            q ((1-t) * vx i + t * vx (Suc i mod ?n),
               (1-t) * vy i + t * vy (Suc i mod ?n))
          = q ((1-s) * vx j + s * vx (Suc j mod ?n),
               (1-s) * vy j + s * vy (Suc j mod ?n))
          \<longrightarrow> (i = j \<and> t = s)
            \<or> (fst (w!i) = fst (w!j) \<and>
               (if snd (w!i) = snd (w!j) then s = t else s = 1 - t))"
    and hC10: "\<forall>i<?n. let cx = (\<Sum>j<?n. vx j) / real ?n;
                           cy = (\<Sum>j<?n. vy j) / real ?n
         in (vx i - cx) * (vy (Suc i mod ?n) - cy)
          - (vy i - cy) * (vx (Suc i mod ?n) - cx) > 0"
    and hC11: "\<forall>i<?n. \<forall>k<?n.
          k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
          (vx k - vx i) * (vy (Suc i mod ?n) - vy i)
          - (vy k - vy i) * (vx (Suc i mod ?n) - vx i) < 0"
    by (rule quotient_of_scheme_extract_vx[OF assms(1)])
  \<comment> \<open>Step 2: Construct the (n+2)-gon P' with spur at the front.
     P' has vertices: v'\\_0 (spur start), v'\\_1 (spur tip), v\\_0, v\\_1, ..., v\\_{n-1}.
     The spur tip v'\\_1 is placed very close to v\\_0 but outside P.
     The spur start v'\\_0 is between v'\\_1 and v\\_{n-1}.\<close>
  have hn3: "?n \<ge> 3" using assms(2) .
  \<comment> \<open>Outward normal direction at vertex 0: perpendicular to edge 0, pointing away from P.\<close>
  \<comment> \<open>Choose epsilon small enough that the spur vertices are close to v\\_0.\<close>
  \<comment> \<open>Define the extended polygon vertices.\<close>
  let ?n' = "?n + 2"
  \<comment> \<open>For the extended scheme, we need a valid (n+2)-sided polygon with the spur.
     APPROACH: use the regular (n+2)-gon (from scheme\\_quotient\\_exists if proper,
     or construct directly) and define q' = q o (spur\\_collapse\\_map).
     The spur\\_collapse\\_map: P' -> P collapses the first two edges to vertex v\\_0.\<close>
  \<comment> \<open>Step 3: Define the spur collapse map phi: P' -> P.
     On edge 0 (v'\\_0 -> v'\\_1): phi(pt) = (vx 0, vy 0) [collapse to v\\_0]
     On edge 1 (v'\\_1 -> v\\_0): phi(pt) = (vx 0, vy 0) [collapse to v\\_0]
     On edge k+2 (v\\_k -> v\\_{k+1 mod n}): phi maps linearly to the same edge of P
     On interior: extend by cone from centroid of P' to boundary.\<close>
  \<comment> \<open>Step 4: Define q' = q o phi: P' -> Y.
     q' is continuous (composition of continuous maps if phi is continuous).
     q' maps P' surjectively to Y (since q is surjective and phi maps onto P).\<close>
  \<comment> \<open>Step 5: Show q' is a quotient map P' -> Y satisfying C1-C11 for [a, a^{-1}] @ w.
     C7 for a-pair: edges 0,1 both collapse to q(v\\_0), so identified. CHECK.
     C7 for w-labels: inherited from C7 of q via phi. CHECK.
     C8 (interior injectivity): interior of P' maps to interior of P (via phi),
       where q is injective by original C8. CHECK.
     C9 (edge-interior injectivity): from original C9 via phi mapping. CHECK.\<close>
  \<comment> \<open>PROOF: use regular (n+2)-gon P' and spur collapse map \\<phi>: P'\\<to>P.
     q' = q \\<circ> \\<phi> is a quotient map (composition of closed continuous surjections).
     \\<phi> collapses edges 0,1 to v\\_0 and maps edge k+2 linearly to edge k.\<close>
  \<comment> \<open>Step 2: Construct P' = regular (n+2)-gon and define vertex coordinates.\<close>
  define vx' where "vx' k = cos (2 * pi * real k / real ?n')" for k
  define vy' where "vy' k = sin (2 * pi * real k / real ?n')" for k
  define P' where "P' = {(x::real,y::real). \<exists>coeffs. (\<forall>i<?n'. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<?n'. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n'. coeffs i * vx' i)
                     \<and> y = (\<Sum>i<?n'. coeffs i * vy' i)}"
  \<comment> \<open>Step 3: Define spur collapse \\<phi>: P' \\<to> P.
     On boundary: edges 0,1 map to v\\_0; edge k+2 maps linearly to edge k.
     On interior: cone extension from centroid.\<close>
  \<comment> \<open>Step 4: Define q' = q \\<circ> \\<phi>.\<close>
  \<comment> \<open>Step 5: Verify C1-C11 for P', q', [a,inv a]@w.\<close>
  \<comment> \<open>The full construction requires ~300 lines of geometric reasoning.
     Key facts: P' is a valid polygon (C1,C3-C6,C10,C11 from regularity).
     q' is a quotient map (C2 from composition of closed continuous surjections).
     C7 for a-pair: \\<phi> maps both spur edges to v\\_0, so q'(edge0(t)) = q(v\\_0) = q'(edge1(1-t)).
     C7 for w-labels: inherited from q via \\<phi>.
     C8: interior of P' maps injectively to interior of P where q is injective.
     C9: edge-interior identification from original C9 via \\<phi>.
     For now: sorry the full verification.\<close>
  show ?thesis sorry
qed

\<comment> \<open>Uncancel at front — homeomorphic realization.
   Derived from quotient\\_of\\_scheme\\_uncancel\\_front (same-space version).\<close>
lemma front_uncancel_realization_homeo:
  fixes Y :: "'a set" and TY :: "'a set set"
  assumes "top1_quotient_of_scheme_on Y TY w"
      and "length w \<ge> 3"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' ([a, top1_inverse_edge a] @ w) \<and>
    top1_homeomorphism_on Y TY Y' TY' h"
proof -
  \<comment> \<open>Y is already a quotient of [a,inv a]@w by the same-space uncancel.\<close>
  from quotient_of_scheme_uncancel_front[OF assms(1) assms(2), of a]
  have "top1_quotient_of_scheme_on Y TY ([a, top1_inverse_edge a] @ w)" .
  \<comment> \<open>Take Y' = Y with identity homeomorphism.\<close>
  thus ?thesis by (rule same_space_implies_homeo_realization_early)
qed

\<comment> \<open>Uncancel (proved via reduction to front-uncancel + rotation).\<close>
lemma quotient_of_scheme_uncancel_proved:
  assumes "top1_quotient_of_scheme_on Y TY (u @ v)"
  shows "top1_quotient_of_scheme_on Y TY (u @ [a, top1_inverse_edge a] @ v)"
proof -
  have hvu: "top1_quotient_of_scheme_on Y TY (v @ u)"
    using quotient_of_scheme_rotate[OF assms] by simp
  have hlen: "length (v @ u) \<ge> 3"
    using quotient_scheme_length_ge3[OF hvu] .
  from quotient_of_scheme_uncancel_front[OF hvu hlen, of a]
  have h1: "top1_quotient_of_scheme_on Y TY ([a, top1_inverse_edge a] @ v @ u)" .
  \<comment> \<open>Rotate: [a,inv a] @ (v@u) -> (v@u) @ [a,inv a].\<close>
  from quotient_of_scheme_rotate[OF h1]
  have h2: "top1_quotient_of_scheme_on Y TY ((v @ u) @ [a, top1_inverse_edge a])" by simp
  \<comment> \<open>Rewrite: (v@u)@[a,inv a] = v @ (u @ [a,inv a]).\<close>
  hence h3: "top1_quotient_of_scheme_on Y TY (v @ (u @ [a, top1_inverse_edge a]))" by simp
  \<comment> \<open>Rotate: v @ (u@[a,inv a]) -> (u@[a,inv a]) @ v.\<close>
  from quotient_of_scheme_rotate[OF h3]
  have h4: "top1_quotient_of_scheme_on Y TY ((u @ [a, top1_inverse_edge a]) @ v)" by simp
  \<comment> \<open>Rewrite: (u@[a,inv a])@v = u@[a,inv a]@v.\<close>
  thus ?thesis by simp
qed

\<comment> \<open>Elementary operations preserve quotient\_of\_scheme\_on for the SAME space.
   If Y is a quotient of scheme s, and s \<rightarrow> t via an elementary operation,
   then Y is also a quotient of scheme t (same polygon, adjusted vertex labeling).\<close>
\<comment> \<open>elementary\\_operation\\_preserves\\_quotient, relabel\\_reverse, scheme\\_equiv\\_preserves\\_quotient:
   DELETED (dead old chain, per expert audit 21).\<close>

\<comment> \<open>Old chain (relabel\\_reverse, elementary\\_operation\\_reverse, scheme\\_equiv\\_sym,
   scheme\\_equiv\\_preserves\\_quotient): ALL DELETED per expert audit 21 step 1.
   Valid versions in cached session: valid\\_relabel\\_reverse, valid\\_equiv\\_sym.\<close>

\<comment> \<open>Same-space preservation implies homeomorphic-realization preservation (take Y=X, h=id).\<close>
\<comment> \<open>Identity is a homeomorphism on any topological space.\<close>

\<comment> \<open>Standalone lemma: spur arc and interior phi image differ.
   If Q = \\<alpha>*cw + s*u\\_j + t*u\\_{j+1} = (1-r)*u\\_0 + r*cw with \\<alpha>,s,t \\<ge> 0,
   \\<alpha>+s+t=1, \\<alpha>>0, and C10 holds, then j=0 implies t=0, j+1=0 implies s=0.
   NOTE: the j\\<noteq>0,j+1\\<noteq>0 case (s=t=0) is GENUINELY FALSE (see CHANGES0179)
   and UNUSED, so the conclusion is conditional on which boundary case applies.\<close>
lemma spur_arc_match_forces_edge:
  fixes nw :: nat and vxw vyw :: "nat \<Rightarrow> real" and cxw cyw :: real
  assumes hnw: "nw \<ge> 3"
      and hC10: "\<forall>i<nw. (vxw i - cxw) * (vyw(Suc i mod nw) - cyw) -
          (vyw i - cyw) * (vxw(Suc i mod nw) - cxw) > 0"
      and hC11: "\<forall>i<nw. \<forall>k<nw. k\<noteq>i \<longrightarrow> k\<noteq>Suc i mod nw \<longrightarrow>
          (vxw k-vxw i)*(vyw(Suc i mod nw)-vyw i)-(vyw k-vyw i)*(vxw(Suc i mod nw)-vxw i) < 0"
      and hj: "j_sec < nw"
      and halpha: "\<alpha> > 0" and hs: "s_v \<ge> 0" and ht: "t_v \<ge> 0"
      and habg: "\<alpha> + s_v + t_v = 1"
      and hx: "\<alpha>*cxw + s_v*vxw j_sec + t_v*vxw(Suc j_sec mod nw) = r*cxw + (1-r)*vxw 0"
      and hy: "\<alpha>*cyw + s_v*vyw j_sec + t_v*vyw(Suc j_sec mod nw) = r*cyw + (1-r)*vyw 0"
      and hr0: "r \<ge> 0" and hr1: "r \<le> 1"
  shows "(j_sec = 0 \<longrightarrow> t_v = 0) \<and> (Suc j_sec mod nw = 0 \<longrightarrow> s_v = 0)"
proof -
  \<comment> \<open>From the equations: s*(u\\_j - u\\_0) + t*(u\\_{j+1} - u\\_0) + (\\<alpha>-r)*(cw - u\\_0) = 0.\<close>
  have hx3: "s_v*(vxw j_sec - vxw 0) + t_v*(vxw(Suc j_sec mod nw) - vxw 0) + (\<alpha>-r)*(cxw - vxw 0) = 0"
    using hx habg by (by100 algebra)
  have hy3: "s_v*(vyw j_sec - vyw 0) + t_v*(vyw(Suc j_sec mod nw) - vyw 0) + (\<alpha>-r)*(cyw - vyw 0) = 0"
    using hy habg by (by100 algebra)
  show ?thesis
  proof (cases "j_sec = 0")
    case True
    \<comment> \<open>u\\_j = u\\_0, so s*(0) + t*(u\\_1 - u\\_0) + (\\<alpha>-r)*(cw-u\\_0) = 0.\<close>
    from hx3 True have "t_v*(vxw(Suc 0 mod nw) - vxw 0) + (\<alpha>-r)*(cxw - vxw 0) = 0" by simp
    from hy3 True have "t_v*(vyw(Suc 0 mod nw) - vyw 0) + (\<alpha>-r)*(cyw - vyw 0) = 0" by simp
    \<comment> \<open>This is a 2x2 system in (t\\_v, \\<alpha>-r). We need to show t\\_v = 0.
       The det is det(u\\_1-u\\_0, cw-u\\_0). From C10, this is \\<noteq> 0.\<close>
    \<comment> \<open>j=0: Cramer on t\\_v*(u\\_1-u\\_0) + (\\<alpha>-r)*(cw-u\\_0) = 0.\<close>
    have h1mod: "Suc 0 mod nw = 1" using hnw by simp
    from hx3[unfolded True] h1mod have hx0: "t_v*(vxw 1 - vxw 0) + (\<alpha>-r)*(cxw - vxw 0) = 0" by simp
    from hy3[unfolded True] h1mod have hy0: "t_v*(vyw 1 - vyw 0) + (\<alpha>-r)*(cyw - vyw 0) = 0" by simp
    define u1x where "u1x = vxw 1 - vxw 0"
    define u1y where "u1y = vyw 1 - vyw 0"
    define cwx where "cwx = cxw - vxw 0"
    define cwy where "cwy = cyw - vyw 0"
    define ar where "ar = \<alpha> - r"
    have h1: "t_v*u1x + ar*cwx = 0" using hx0 unfolding u1x_def cwx_def ar_def by linarith
    have h2: "t_v*u1y + ar*cwy = 0" using hy0 unfolding u1y_def cwy_def ar_def by linarith
    have "t_v*(u1x*cwy - u1y*cwx) = (t_v*u1x)*cwy - (t_v*u1y)*cwx" by (by100 algebra)
    also have "(t_v*u1x) = -(ar*cwx)" using h1 by linarith
    also have "(t_v*u1y) = -(ar*cwy)" using h2 by linarith
    finally have "t_v*(u1x*cwy - u1y*cwx) = -(ar*cwx)*cwy - (-(ar*cwy))*cwx" by simp
    hence ht_det: "t_v*(u1x*cwy - u1y*cwx) = 0" by (by100 algebra)
    from hC10[rule_format, of 0] hnw h1mod
    have hC10_0: "(vxw 0-cxw)*(vyw 1-cyw)-(vyw 0-cyw)*(vxw 1-cxw) > 0" by simp
    have hdet_eq: "u1x*cwy - u1y*cwx = (vxw 0-cxw)*(vyw 1-cyw)-(vyw 0-cyw)*(vxw 1-cxw)"
      unfolding u1x_def u1y_def cwx_def cwy_def by (simp add: algebra_simps)
    have "u1x*cwy - u1y*cwx \<noteq> 0" using hdet_eq hC10_0 by linarith
    from ht_det this have "t_v = 0" by simp
    have h_suc_ne: "Suc 0 mod nw \<noteq> 0" using hnw by simp
    from \<open>t_v = 0\<close> True h_suc_ne show ?thesis by simp
  next
    case False note hj_ne0 = this
    show ?thesis
    proof (cases "Suc j_sec mod nw = 0")
      case True
      \<comment> \<open>j+1=0 mod nw: u\\_{j+1} = u\\_0. Cramer: s\\_v = 0.\<close>
      from True have hvxk: "vxw(Suc j_sec mod nw) = vxw 0" "vyw(Suc j_sec mod nw) = vyw 0" by auto
      from hx3 hvxk have hx0: "s_v*(vxw j_sec - vxw 0) + (\<alpha>-r)*(cxw - vxw 0) = 0" by simp
      from hy3 hvxk have hy0: "s_v*(vyw j_sec - vyw 0) + (\<alpha>-r)*(cyw - vyw 0) = 0" by simp
      define ujx where "ujx = vxw j_sec - vxw 0"
      define ujy where "ujy = vyw j_sec - vyw 0"
      define cwx where "cwx = cxw - vxw 0"
      define cwy where "cwy = cyw - vyw 0"
      define ar where "ar = \<alpha> - r"
      have h1: "s_v*ujx + ar*cwx = 0" using hx0 unfolding ujx_def cwx_def ar_def by linarith
      have h2: "s_v*ujy + ar*cwy = 0" using hy0 unfolding ujy_def cwy_def ar_def by linarith
      have "s_v*(ujx*cwy - ujy*cwx) = (s_v*ujx)*cwy - (s_v*ujy)*cwx" by (by100 algebra)
      also have "(s_v*ujx) = -(ar*cwx)" using h1 by linarith
      also have "(s_v*ujy) = -(ar*cwy)" using h2 by linarith
      finally have "s_v*(ujx*cwy - ujy*cwx) = -(ar*cwx)*cwy - (-(ar*cwy))*cwx" by simp
      hence hs_det: "s_v*(ujx*cwy - ujy*cwx) = 0" by (by100 algebra)
      \<comment> \<open>det(u\\_j-u\\_0, cw-u\\_0) = det(u\\_0-cw, u\\_j-cw) from C10 at j\\_sec (with u\\_{j+1}=u\\_0).\<close>
      from hC10[rule_format, OF hj] hvxk
      have hC10_j: "(vxw j_sec-cxw)*(vyw 0-cyw)-(vyw j_sec-cyw)*(vxw 0-cxw) > 0" by simp
      \<comment> \<open>Identity: det(A-B,C-B) = det(B-C,A-C). Here A=u\\_j, B=u\\_0, C=cw.\<close>
      have hdet_ne: "ujx*cwy - ujy*cwx \<noteq> 0"
      proof -
        \<comment> \<open>Use cross\\_product\\_cyclic: det(uj-u0, cw-u0) = det(u0-cw, uj-cw) = -C10.\<close>
        have hcross: "(vxw j_sec-vxw 0)*(cyw-vyw 0)-(vyw j_sec-vyw 0)*(cxw-vxw 0)
            = (vxw 0-cxw)*(vyw j_sec-cyw)-(vyw 0-cyw)*(vxw j_sec-cxw)"
          by (rule cross_product_cyclic)
        have hneg_C10: "(vxw 0-cxw)*(vyw j_sec-cyw)-(vyw 0-cyw)*(vxw j_sec-cxw)
            = -(((vxw j_sec-cxw)*(vyw 0-cyw)-(vyw j_sec-cyw)*(vxw 0-cxw)))"
          by (by100 algebra)
        have h_unfold: "ujx*cwy - ujy*cwx = (vxw j_sec-vxw 0)*(cyw-vyw 0)-(vyw j_sec-vyw 0)*(cxw-vxw 0)"
          unfolding ujx_def ujy_def cwx_def cwy_def by simp
        from h_unfold hcross have h_eq_neg: "ujx*cwy - ujy*cwx =
            (vxw 0-cxw)*(vyw j_sec-cyw)-(vyw 0-cyw)*(vxw j_sec-cxw)" by linarith
        from hneg_C10 have h_neg: "(vxw 0-cxw)*(vyw j_sec-cyw)-(vyw 0-cyw)*(vxw j_sec-cxw) < 0"
          using hC10_j by linarith
        from h_eq_neg h_neg have "ujx*cwy - ujy*cwx < 0" by linarith
        thus ?thesis by linarith
      qed
      from hs_det hdet_ne have "s_v = 0" by simp
      from \<open>s_v = 0\<close> True hj_ne0 show ?thesis by simp
    next
      case False note hsi_ne0 = this
      \<comment> \<open>j \\<noteq> 0, j+1 \\<noteq> 0: both implications are vacuously true.\<close>
      from hj_ne0 hsi_ne0 show ?thesis by simp
    qed
  qed
qed



\<comment> \<open>Non-adjacent centroid-cone disjointness. For a convex polygon with C10/C11 and centroid at
   origin with vertices on unit circle: a point in sector jp can't be in non-adjacent sector jp'.\<close>
lemma non_adjacent_cone_disjoint:
  fixes nw :: nat and vxw vyw :: "nat \<Rightarrow> real"
  assumes hnw: "nw \<ge> 3"
      and hC10: "\<forall>i<nw. vxw i * vyw(Suc i mod nw) - vyw i * vxw(Suc i mod nw) > 0"
      and hC11: "\<forall>i<nw. \<forall>k<nw. k\<noteq>i \<longrightarrow> k\<noteq>Suc i mod nw \<longrightarrow>
          (vxw k-vxw i)*(vyw(Suc i mod nw)-vyw i)-(vyw k-vyw i)*(vxw(Suc i mod nw)-vxw i) < 0"
      and hunit: "\<forall>j<nw. (vxw j)^2 + (vyw j)^2 = 1"
      and hsum_x: "(\<Sum>j<nw. vxw j) = 0" and hsum_y: "(\<Sum>j<nw. vyw j) = 0"
      and hjp: "jp < nw" and hjp': "jp' < nw"
      and hne: "jp \<noteq> jp'" and hne_adj1: "jp' \<noteq> Suc jp mod nw" and hne_adj2: "jp \<noteq> Suc jp' mod nw"
      and hsp: "sp \<ge> 0" and htp: "tp \<ge> 0" and hst: "sp + tp > 0"
      \<comment> \<open>q = sp*u\\_jp + tp*u\\_{jp+1} (centroid=0).\<close>
      \<comment> \<open>Cone jp' first condition: cross(u\\_{jp'}, q) \\<ge> 0.\<close>
      and hcone1: "vxw jp' * (sp*vyw jp + tp*vyw(Suc jp mod nw)) -
          vyw jp' * (sp*vxw jp + tp*vxw(Suc jp mod nw)) \<ge> 0"
      \<comment> \<open>Cone jp' second condition: cross(q, u\\_{jp'+1}) \\<ge> 0.\<close>
      and hcone2: "(sp*vxw jp + tp*vxw(Suc jp mod nw)) * vyw(Suc jp' mod nw) -
          (sp*vyw jp + tp*vyw(Suc jp mod nw)) * vxw(Suc jp' mod nw) \<ge> 0"
  shows False
proof -
  \<comment> \<open>Complex number setup: u\\_j = Complex(vxw j, vyw j) on unit circle.\<close>
  define uw :: "nat \<Rightarrow> complex" where "uw j = Complex (vxw j) (vyw j)" for j
  have huw_ne: "\<forall>j<nw. uw j \<noteq> 0"
  proof (intro allI impI)
    fix j assume "j < nw"
    from hunit[rule_format, OF this] have "(vxw j)^2 + (vyw j)^2 = 1" .
    hence "cmod (uw j) = 1" unfolding uw_def cmod_def by (by100 simp)
    thus "uw j \<noteq> 0" by (by100 auto)
  qed
  have hmod_eq: "\<forall>j<nw. cmod (uw j) = 1"
  proof (intro allI impI)
    fix j assume "j < nw"
    from hunit[rule_format, OF this] show "cmod (uw j) = 1"
      unfolding uw_def cmod_def by (by100 simp)
  qed
  \<comment> \<open>C10 gives Im(cnj(uw j) * uw(j+1)) > 0, i.e., consecutive vertices CCW.\<close>
  have hC10_im: "\<forall>j<nw. Im (cnj (uw j) * uw (Suc j mod nw)) > 0"
  proof (intro allI impI)
    fix j assume hj: "j < nw"
    have "Im (cnj (uw j) * uw (Suc j mod nw)) =
        vxw j * vyw(Suc j mod nw) - vyw j * vxw(Suc j mod nw)"
      unfolding uw_def by (by100 simp)
    with hC10[rule_format, OF hj] show "Im (cnj (uw j) * uw (Suc j mod nw)) > 0" by linarith
  qed
  \<comment> \<open>Define theta (angular steps) and alpha (cumulative angle).\<close>
  define theta where "theta j = Arg (uw (Suc j mod nw) / uw j)" for j
  define alpha where "alpha m = (\<Sum>j<m. theta j)" for m
  \<comment> \<open>theta\\_j \\<in> (0, \\<pi>) from C10 (same derivation as spur\\_arc\\_target\\_sector).\<close>
  have htheta_pos: "\<forall>j<nw. theta j > 0 \<and> theta j < pi"
  proof (intro allI impI conjI)
    fix j assume hj: "j < nw"
    have hzj_ne: "uw j \<noteq> 0" using huw_ne hj by (by100 auto)
    have hSj: "Suc j mod nw < nw" using hnw by (by100 simp)
    have hratio_ne: "uw (Suc j mod nw) / uw j \<noteq> 0"
      using huw_ne[rule_format, OF hSj] hzj_ne by (by100 auto)
    have hsin_pos: "Im (uw (Suc j mod nw) / uw j) > 0"
    proof -
      have hmod_j: "cmod (uw j) = 1" using hmod_eq hj by (by100 auto)
      have "cnj (uw j) * uw (Suc j mod nw) = cnj (uw j) * uw j * (uw (Suc j mod nw) / uw j)"
        using hzj_ne by (by100 simp)
      also have "cnj (uw j) * uw j = of_real ((cmod (uw j))^2)"
        using complex_norm_square by (by100 simp)
      finally have "cnj (uw j) * uw (Suc j mod nw) = of_real 1 * (uw (Suc j mod nw) / uw j)"
        using hmod_j by (by100 simp)
      hence "Im (cnj (uw j) * uw (Suc j mod nw)) = Im (uw (Suc j mod nw) / uw j)"
        by (by100 simp)
      with hC10_im[rule_format, OF hj] show ?thesis by linarith
    qed
    have harg_bound: "- pi < Arg (uw (Suc j mod nw) / uw j)" "Arg (uw (Suc j mod nw) / uw j) \<le> pi"
      using Arg_bounded[of "uw (Suc j mod nw) / uw j"] by auto
    have hsin_arg: "sin (Arg (uw (Suc j mod nw) / uw j)) > 0"
    proof -
      from sin_Arg[of "uw (Suc j mod nw) / uw j"] hratio_ne
      have "sin (Arg (uw (Suc j mod nw) / uw j)) = Im (uw (Suc j mod nw) / uw j) / cmod (uw (Suc j mod nw) / uw j)"
        by (by100 simp)
      moreover have "cmod (uw (Suc j mod nw) / uw j) > 0" using hratio_ne by (by100 simp)
      ultimately show ?thesis using hsin_pos by (by100 simp)
    qed
    show "theta j > 0" unfolding theta_def
    proof (rule ccontr)
      assume "\<not> 0 < Arg (uw (Suc j mod nw) / uw j)"
      hence "Arg (uw (Suc j mod nw) / uw j) \<le> 0" by linarith
      with harg_bound(1) have "Arg (uw (Suc j mod nw) / uw j) \<in> {-pi<..0}" by (by100 auto)
      hence "sin (Arg (uw (Suc j mod nw) / uw j)) \<le> 0"
      proof -
        from \<open>Arg _ \<le> 0\<close> have "- Arg (uw (Suc j mod nw) / uw j) \<ge> 0" by linarith
        moreover from harg_bound(1) have "- Arg (uw (Suc j mod nw) / uw j) < pi" by linarith
        ultimately have "sin(- Arg (uw (Suc j mod nw) / uw j)) \<ge> 0"
          using sin_ge_zero[of "- Arg (uw (Suc j mod nw) / uw j)"] by linarith
        moreover have "sin(- Arg (uw (Suc j mod nw) / uw j)) = - sin(Arg (uw (Suc j mod nw) / uw j))"
          using sin_minus[of "Arg (uw (Suc j mod nw) / uw j)"] by (by100 metis)
        ultimately show ?thesis by linarith
      qed
      with hsin_arg show False by linarith
    qed
    show "theta j < pi" unfolding theta_def
    proof -
      from harg_bound(2) have "Arg (uw (Suc j mod nw) / uw j) \<le> pi" .
      moreover have "Arg (uw (Suc j mod nw) / uw j) \<noteq> pi"
      proof
        assume "Arg (uw (Suc j mod nw) / uw j) = pi"
        hence "sin(Arg (uw (Suc j mod nw) / uw j)) = 0" by (by100 simp)
        with hsin_arg show False by linarith
      qed
      ultimately show "Arg (uw (Suc j mod nw) / uw j) < pi" by linarith
    qed
  qed
  \<comment> \<open>alpha is strictly increasing.\<close>
  have halpha_strict: "\<forall>j<nw. alpha j < alpha (Suc j)"
  proof (intro allI impI)
    fix j assume "j < nw"
    have "alpha (Suc j) = alpha j + theta j" unfolding alpha_def
      using lessThan_Suc by (by100 simp)
    with htheta_pos[rule_format, OF \<open>j < nw\<close>] show "alpha j < alpha (Suc j)" by linarith
  qed
  \<comment> \<open>Cross product = Im(cnj(uw i) * q) where q = sp*uw(jp)+tp*uw(jp+1).\<close>
  define q where "q = of_real sp * uw jp + of_real tp * uw (Suc jp mod nw)"
  have hq_ne: "q \<noteq> 0"
  proof
    assume "q = 0"
    hence "of_real sp * uw jp = -(of_real tp * uw (Suc jp mod nw))" unfolding q_def by (by100 algebra)
    \<comment> \<open>With sp,tp \\<ge> 0 and uw on unit circle: sp*uw(jp) = -tp*uw(jp+1) impossible unless sp=tp=0.\<close>
    \<comment> \<open>q=0: Im(cnj(uw jp)*q) = 0 = tp*C10\\_im. Since C10\\_im > 0: tp = 0. Similarly sp = 0.\<close>
    have "Im (cnj (uw jp) * q) = tp * Im (cnj (uw jp) * uw (Suc jp mod nw))"
    proof -
      have "cnj (uw jp) * q = of_real sp * (cnj (uw jp) * uw jp) + of_real tp * (cnj (uw jp) * uw (Suc jp mod nw))"
        unfolding q_def by (by100 algebra)
      moreover have "Im (cnj (uw jp) * uw jp) = 0"
      proof -
        have "cnj (uw jp) * uw jp = uw jp * cnj (uw jp)" by (by100 algebra)
        also have "Im \<dots> = 0" by (rule complex_In_mult_cnj_zero)
        finally show ?thesis .
      qed
      ultimately show ?thesis by (by100 simp)
    qed
    hence "tp * Im (cnj (uw jp) * uw (Suc jp mod nw)) = 0"
      using \<open>q = 0\<close> by (by100 simp)
    hence "tp = 0" using hC10_im[rule_format, OF hjp] by (by100 simp)
    \<comment> \<open>Similarly: from q=0 and tp=0: sp*uw(jp) = 0. Since uw(jp) \\<noteq> 0: sp = 0.\<close>
    from \<open>q = 0\<close> \<open>tp = 0\<close> have "of_real sp * uw jp = 0" unfolding q_def by (by100 simp)
    hence "sp = 0" using huw_ne[rule_format, OF hjp] by (by100 simp)
    with \<open>tp = 0\<close> hst show False by linarith
  qed
  \<comment> \<open>hcone1: Im(cnj(uw jp') * q) \\<ge> 0.\<close>
  have hcone1_im: "Im (cnj (uw jp') * q) \<ge> 0"
  proof -
    have "Im (cnj (uw jp') * q) = vxw jp' * Im q - vyw jp' * Re q"
      unfolding uw_def by (by100 simp)
    also have "Re q = sp * vxw jp + tp * vxw(Suc jp mod nw)"
      unfolding q_def uw_def by (by100 simp)
    also have "Im q = sp * vyw jp + tp * vyw(Suc jp mod nw)"
      unfolding q_def uw_def by (by100 simp)
    finally show ?thesis using hcone1 by (by100 simp)
  qed
  \<comment> \<open>hcone2: Im(cnj q * uw(jp'+1)) \\<ge> 0, i.e., Im(q * cnj(uw(jp'+1))) \\<le> 0... actually
     cross(q, u\\_{jp'+1}) = Im(cnj q * uw(jp'+1)) \\<ge> 0? Let me check.\<close>
  \<comment> \<open>cross(a, b) = ax*by - ay*bx = Im(cnj(a)*b). So cross(q, u\\_{jp'+1}) = Im(cnj q * uw(jp'+1)).\<close>
  have hcone2_im: "Im (cnj q * uw (Suc jp' mod nw)) \<ge> 0"
  proof -
    have hRe_q: "Re q = sp*vxw jp + tp*vxw(Suc jp mod nw)" unfolding q_def uw_def by (by100 simp)
    have hIm_q: "Im q = sp*vyw jp + tp*vyw(Suc jp mod nw)" unfolding q_def uw_def by (by100 simp)
    have hRe_jp': "Re (uw (Suc jp' mod nw)) = vxw (Suc jp' mod nw)" unfolding uw_def by (by100 simp)
    have hIm_jp': "Im (uw (Suc jp' mod nw)) = vyw (Suc jp' mod nw)" unfolding uw_def by (by100 simp)
    have "Im (cnj q * uw (Suc jp' mod nw)) = Re q * Im (uw (Suc jp' mod nw)) - Im q * Re (uw (Suc jp' mod nw))"
      by (by100 simp)
    also have "\<dots> = (sp*vxw jp + tp*vxw(Suc jp mod nw)) * vyw(Suc jp' mod nw) -
        (sp*vyw jp + tp*vyw(Suc jp mod nw)) * vxw(Suc jp' mod nw)"
      using hRe_q hIm_q hRe_jp' hIm_jp' by (by100 algebra)
    finally show ?thesis using hcone2 by linarith
  qed
  \<comment> \<open>From the angular partition: Arg(q) \\<in> (Arg(uw jp), Arg(uw(jp+1))) but
     cone jp' needs Arg(q) \\<in> (Arg(uw jp'), Arg(uw(jp'+1))). Non-adjacent \\<to> disjoint \\<to> False.\<close>
  \<comment> \<open>The detailed angular argument uses the cumulative angle alpha.\<close>
  \<comment> \<open>Use unit\\_circle\\_cross\\_cis to get the cumulative angle alpha.\<close>
  from unit_circle_cross_cis[OF hnw hC10 hC11 hunit hjp hjp']
  obtain alpha where
    halpha_cis: "\<forall>j<nw. \<forall>j'<nw. cnj (Complex (vxw j) (vyw j)) * Complex (vxw j') (vyw j') =
      cis (alpha j' - alpha j)"
    and halpha_strict: "\<forall>j<nw. alpha j < alpha (Suc j)"
    and halpha_0: "alpha 0 = 0"
    and halpha_nw: "alpha nw = 2*pi"
    by (by100 blast)
  \<comment> \<open>hcone1\\_im: Im(cnj(uw jp')*q) \\<ge> 0 \\<to> Im(cis(Arg(q/uw0)-alpha\\_{jp'})) \\<ge> 0 \\<to> sin(...) \\<ge> 0.\<close>
  \<comment> \<open>From hcone1\\_im and the cis representation: q must have angle in [alpha\\_{jp'}, alpha\\_{jp'+1}].
     From q = sp*uw(jp)+tp*uw(jp+1): q has angle in [alpha\\_jp, alpha\\_{jp+1}].
     Non-adjacent: intervals disjoint \\<to> contradiction.\<close>
  \<comment> \<open>Alpha strictly increasing: alpha\\_0 < alpha\\_1 < ... < alpha\\_nw = 2\\<pi>.
     For non-adjacent jp, jp': [alpha\\_jp, alpha\\_{jp+1}] \\<cap> [alpha\\_{jp'}, alpha\\_{jp'+1}] = \\<emptyset>.\<close>
  \<comment> \<open>Cross product via cis: cnj(uw i)*uw j = cis(alpha\\_j - alpha\\_i). So Im = sin(alpha\\_j-alpha\\_i).\<close>
  \<comment> \<open>From hcone1\\_im \\<ge> 0: sp*sin(alpha\\_jp-alpha\\_{jp'})+tp*sin(alpha\\_{jp+1}-alpha\\_{jp'}) \\<ge> 0.\<close>
  have hcone1_sin: "sp * sin(alpha jp - alpha jp') + tp * sin(alpha(Suc jp mod nw) - alpha jp') \<ge> 0"
  proof -
    have "Im (cnj (Complex (vxw jp') (vyw jp')) * q) =
      sp * Im (cis (alpha jp - alpha jp')) + tp * Im (cis (alpha (Suc jp mod nw) - alpha jp'))"
    proof -
      have "cnj (Complex (vxw jp') (vyw jp')) * q =
        of_real sp * (cnj (Complex (vxw jp') (vyw jp')) * Complex (vxw jp) (vyw jp)) +
        of_real tp * (cnj (Complex (vxw jp') (vyw jp')) * Complex (vxw (Suc jp mod nw)) (vyw (Suc jp mod nw)))"
        unfolding q_def uw_def by (by100 algebra)
      also have "cnj (Complex (vxw jp') (vyw jp')) * Complex (vxw jp) (vyw jp) = cis (alpha jp - alpha jp')"
        using halpha_cis[rule_format, OF hjp' hjp] by (by100 simp)
      also have "cnj (Complex (vxw jp') (vyw jp')) * Complex (vxw (Suc jp mod nw)) (vyw (Suc jp mod nw)) =
        cis (alpha (Suc jp mod nw) - alpha jp')"
      proof -
        have "Suc jp mod nw < nw" using hnw by (by100 simp)
        from halpha_cis[rule_format, OF hjp' this] show ?thesis by (by100 simp)
      qed
      finally show ?thesis by (by100 simp)
    qed
    moreover have "Im (cnj (Complex (vxw jp') (vyw jp')) * q) = Im (cnj (uw jp') * q)"
      unfolding uw_def by (by100 simp)
    ultimately have "Im (cnj (uw jp') * q) = sp*sin(alpha jp-alpha jp') + tp*sin(alpha(Suc jp mod nw)-alpha jp')"
      by (by100 simp)
    with hcone1_im show ?thesis by linarith
  qed
  \<comment> \<open>From hcone2\\_im \\<ge> 0: similarly for the second condition.\<close>
  have hcone2_sin: "sp * sin(alpha(Suc jp' mod nw) - alpha jp) + tp * sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) \<ge> 0"
  proof -
    have hSjp': "Suc jp' mod nw < nw" using hnw by (by100 simp)
    have hSjp: "Suc jp mod nw < nw" using hnw by (by100 simp)
    have "Im (cnj q * uw (Suc jp' mod nw)) =
      sp * Im (cnj (uw jp) * uw (Suc jp' mod nw)) + tp * Im (cnj (uw (Suc jp mod nw)) * uw (Suc jp' mod nw))"
    proof -
      have "cnj q = of_real sp * cnj (uw jp) + of_real tp * cnj (uw (Suc jp mod nw))"
        unfolding q_def by (by100 simp)
      hence "cnj q * uw (Suc jp' mod nw) =
        of_real sp * (cnj (uw jp) * uw (Suc jp' mod nw)) +
        of_real tp * (cnj (uw (Suc jp mod nw)) * uw (Suc jp' mod nw))"
        by (by100 algebra)
      thus ?thesis by (by100 simp)
    qed
    also have "Im (cnj (uw jp) * uw (Suc jp' mod nw)) = sin(alpha(Suc jp' mod nw) - alpha jp)"
    proof -
      have "cnj (uw jp) * uw (Suc jp' mod nw) = cis (alpha(Suc jp' mod nw) - alpha jp)"
        using halpha_cis[rule_format, OF hjp hSjp'] unfolding uw_def by (by100 simp)
      thus ?thesis by (by100 simp)
    qed
    also have "Im (cnj (uw (Suc jp mod nw)) * uw (Suc jp' mod nw)) = sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw))"
    proof -
      have "cnj (uw (Suc jp mod nw)) * uw (Suc jp' mod nw) = cis (alpha(Suc jp' mod nw) - alpha(Suc jp mod nw))"
        using halpha_cis[rule_format, OF hSjp hSjp'] unfolding uw_def by (by100 simp)
      thus ?thesis by (by100 simp)
    qed
    finally show ?thesis using hcone2_im by linarith
  qed
  \<comment> \<open>Use C11 to derive that uw(jp) and uw(jp+1) are on the wrong side of edge (jp', jp'+1).\<close>
  have hSjp: "Suc jp mod nw < nw" using hnw by (by100 simp)
  have hSjp': "Suc jp' mod nw < nw" using hnw by (by100 simp)
  \<comment> \<open>C11 with edge jp', vertex jp: cross(uw(jp)-uw(jp'), uw(jp'+1)-uw(jp')) < 0.\<close>
  have hC11_jp: "(vxw jp - vxw jp')*(vyw(Suc jp' mod nw) - vyw jp') -
      (vyw jp - vyw jp')*(vxw(Suc jp' mod nw) - vxw jp') < 0"
    using hC11[rule_format, OF hjp' hjp hne hne_adj2] by (by100 auto)
  \<comment> \<open>C11 with edge jp', vertex Suc jp mod nw: cross(uw(jp+1)-uw(jp'), uw(jp'+1)-uw(jp')) < 0.\<close>
  have hne2: "Suc jp mod nw \<noteq> jp'"
    using hne_adj1 by (by100 auto)
  have hne2b: "Suc jp mod nw \<noteq> Suc jp' mod nw"
  proof
    assume h: "Suc jp mod nw = Suc jp' mod nw"
    have "Suc jp mod nw = (if jp = nw - 1 then 0 else Suc jp)"
      using hjp hnw by (by100 auto)
    moreover have "Suc jp' mod nw = (if jp' = nw - 1 then 0 else Suc jp')"
      using hjp' hnw by (by100 auto)
    ultimately have "jp = jp'"
    proof (cases "jp = nw - 1")
      case True
      show ?thesis
      proof (cases "jp' = nw - 1")
        case True with \<open>jp = nw - 1\<close> show ?thesis by (by100 simp)
      next
        case False
        hence "Suc jp' mod nw = Suc jp'" using hjp' hnw by (by100 auto)
        moreover have "Suc jp mod nw = 0" using \<open>jp = nw - 1\<close> hnw by (by100 auto)
        ultimately have "Suc jp' = 0" using h by linarith
        thus ?thesis by (by100 simp)
      qed
    next
      case False
      hence "Suc jp mod nw = Suc jp" using hjp hnw by (by100 auto)
      show ?thesis
      proof (cases "jp' = nw - 1")
        case True
        hence "Suc jp' mod nw = 0" using hnw by (by100 auto)
        with h \<open>Suc jp mod nw = Suc jp\<close> have "Suc jp = 0" by linarith
        thus ?thesis by (by100 simp)
      next
        case False
        hence "Suc jp' mod nw = Suc jp'" using hjp' hnw by (by100 auto)
        with h \<open>Suc jp mod nw = Suc jp\<close> show ?thesis by linarith
      qed
    qed
    with hne show False by (by100 auto)
  qed
  have hC11_jp1: "(vxw(Suc jp mod nw) - vxw jp')*(vyw(Suc jp' mod nw) - vyw jp') -
      (vyw(Suc jp mod nw) - vyw jp')*(vxw(Suc jp' mod nw) - vxw jp') < 0"
    using hC11[rule_format, OF hjp' hSjp hne2 hne2b] by (by100 auto)
  \<comment> \<open>Weighted sum: sp*C11\\_jp + tp*C11\\_jp1 < 0.\<close>
  have hweighted: "sp * ((vxw jp - vxw jp')*(vyw(Suc jp' mod nw) - vyw jp') -
      (vyw jp - vyw jp')*(vxw(Suc jp' mod nw) - vxw jp')) +
    tp * ((vxw(Suc jp mod nw) - vxw jp')*(vyw(Suc jp' mod nw) - vyw jp') -
      (vyw(Suc jp mod nw) - vyw jp')*(vxw(Suc jp' mod nw) - vxw jp')) < 0"
  proof -
    define xjp where "xjp = (vxw jp - vxw jp')*(vyw(Suc jp' mod nw) - vyw jp') -
        (vyw jp - vyw jp')*(vxw(Suc jp' mod nw) - vxw jp')"
    define xjp1 where "xjp1 = (vxw(Suc jp mod nw) - vxw jp')*(vyw(Suc jp' mod nw) - vyw jp') -
        (vyw(Suc jp mod nw) - vyw jp')*(vxw(Suc jp' mod nw) - vxw jp')"
    have hxjp: "xjp < 0" using hC11_jp unfolding xjp_def by linarith
    have hxjp1: "xjp1 < 0" using hC11_jp1 unfolding xjp1_def by linarith
    have "xjp \<le> 0" using hxjp by linarith
    have hC11_jp_le: "sp * xjp \<le> 0"
      using mult_nonneg_nonpos[OF hsp \<open>xjp \<le> 0\<close>] .
    have "xjp1 \<le> 0" using hxjp1 by linarith
    moreover have hC11_jp1_le: "tp * xjp1 \<le> 0"
      using mult_nonneg_nonpos[OF htp \<open>xjp1 \<le> 0\<close>] .
    moreover have "sp * xjp + tp * xjp1 < 0"
    proof (cases "sp > 0")
      case True
      from mult_pos_neg[OF this hxjp] have "sp * xjp < 0" .
      with hC11_jp1_le show ?thesis by linarith
    next
      case False hence "sp = 0" using hsp by linarith
      hence "sp * xjp = 0" by (by100 simp)
      moreover have "tp > 0" using hst \<open>sp = 0\<close> by linarith
      from mult_pos_neg[OF this hxjp1] have "tp * xjp1 < 0" .
      with \<open>sp * xjp = 0\<close> show ?thesis by linarith
    qed
    thus ?thesis unfolding xjp_def xjp1_def by linarith
  qed
  \<comment> \<open>Expand: sp*cross(uw(jp)-uw(jp'), dir) + tp*cross(uw(jp+1)-uw(jp'), dir)
     = cross(q - (sp+tp)*uw(jp'), dir) where dir = uw(jp'+1) - uw(jp').
     = cross(q, dir) - (sp+tp)*cross(uw(jp'), dir)
     = [cross(q, uw(jp'+1)) - cross(q, uw(jp'))] - (sp+tp)*[cross(uw(jp'), uw(jp'+1)) - 0]
     = [hcone2 + hcone1] - (sp+tp)*C10(jp') where we use cross(q, uw(jp')) = -hcone1.
     Hmm: cross(q, uw(jp')) = Im(cnj q * uw(jp')). And hcone1 = Im(cnj(uw jp')*q).
     Im(cnj q * uw(jp')) = Re(q)*Im(uw jp') - Im(q)*Re(uw jp').
     Im(cnj(uw jp')*q) = Re(uw jp')*Im(q) - Im(uw jp')*Re(q) = -(Re(q)*Im(uw jp') - Im(q)*Re(uw jp')).
     So cross(q, uw(jp')) = -hcone1.
     cross(q, uw(jp'+1)) = Im(cnj q * uw(jp'+1)) = hcone2.
     cross(uw(jp'), uw(jp'+1)) = Im(cnj(uw jp')*uw(jp'+1)) = C10(jp') > 0.\<close>
  \<comment> \<open>So the weighted sum = hcone2 - (-hcone1) - (sp+tp)*C10\\_jp' = hcone1 + hcone2 - (sp+tp)*C10\\_jp'.\<close>
  \<comment> \<open>But this only gives hcone1 + hcone2 < (sp+tp)*C10(jp'). Not a contradiction since LHS \\<ge> 0, RHS > 0.\<close>
  \<comment> \<open>We need to expand the weighted sum in coordinates and relate to hcone1, hcone2, C10 directly.\<close>
  \<comment> \<open>Alternative approach: the weighted sum equals the cross product of
     (q - (sp+tp)*centroid\\_of\\_jp') with (edge direction of jp').
     Since centroid is at origin: q - (sp+tp)*0 = q. No, that's wrong.
     Actually it's q - (sp+tp)*uw(jp'), not q itself.\<close>
  \<comment> \<open>KEY: directly expand and combine with hcone1 and hcone2 to get contradiction.
     The weighted sum in coordinates:\<close>
  have hexpand: "sp * ((vxw jp - vxw jp')*(vyw(Suc jp' mod nw) - vyw jp') -
      (vyw jp - vyw jp')*(vxw(Suc jp' mod nw) - vxw jp')) +
    tp * ((vxw(Suc jp mod nw) - vxw jp')*(vyw(Suc jp' mod nw) - vyw jp') -
      (vyw(Suc jp mod nw) - vyw jp')*(vxw(Suc jp' mod nw) - vxw jp'))
    = (sp*vxw jp + tp*vxw(Suc jp mod nw) - (sp+tp)*vxw jp') * (vyw(Suc jp' mod nw) - vyw jp') -
      (sp*vyw jp + tp*vyw(Suc jp mod nw) - (sp+tp)*vyw jp') * (vxw(Suc jp' mod nw) - vxw jp')"
    by (by100 algebra)
  \<comment> \<open>Also expand hcone1 and hcone2 in similar terms.\<close>
  \<comment> \<open>hcone1 = vxw jp' * (sp*vyw jp + tp*vyw(Suc jp)) - vyw jp' * (sp*vxw jp + tp*vxw(Suc jp))
     = vxw jp' * qy - vyw jp' * qx where qx = sp*vxw jp + tp*vxw(Suc jp), qy = sp*vyw jp + tp*vyw(Suc jp).
     hcone2 = qx * vyw(Suc jp') - qy * vxw(Suc jp').\<close>
  \<comment> \<open>The weighted C11 sum = (qx - (sp+tp)*vxw jp') * (vyw(Suc jp') - vyw jp')
     - (qy - (sp+tp)*vyw jp') * (vxw(Suc jp') - vxw jp')
     = qx*vyw(Suc jp') - qx*vyw jp' - (sp+tp)*vxw jp'*vyw(Suc jp') + (sp+tp)*vxw jp'*vyw jp'
     - qy*vxw(Suc jp') + qy*vxw jp' + (sp+tp)*vyw jp'*vxw(Suc jp') - (sp+tp)*vyw jp'*vxw jp'
     = [qx*vyw(Suc jp') - qy*vxw(Suc jp')] + [qy*vxw jp' - qx*vyw jp']
     - (sp+tp)*[vxw jp'*vyw(Suc jp') - vyw jp'*vxw(Suc jp')]
     = hcone2 + (-hcone1) ... wait:
     hcone1 = vxw jp'*qy - vyw jp'*qx. So qy*vxw jp' - qx*vyw jp' = hcone1 (reorder).
     Hmm: hcone1 = vxw jp' * qy - vyw jp' * qx = qy*vxw jp' - qx*vyw jp'. Yes!
     Wait, that's wrong. vxw jp' * qy - vyw jp' * qx \\<noteq> qy*vxw jp' - qx*vyw jp'. They're the same: commutative.
     So: qy*vxw jp' - qx*vyw jp' = hcone1? No: hcone1 = vxw jp'*qy - vyw jp'*qx which IS qy*vxw jp' - qx*vyw jp'. Wait no, multiplication is commutative so vxw jp' * qy = qy * vxw jp'. So hcone1 = qy*vxw jp' - qx*vyw jp'. And in the expansion: qy*vxw jp' - qx*vyw jp' = hcone1. But with opposite sign compared to cross(q, uw(jp')): cross(q, uw(jp')) = qx*vyw jp' - qy*vxw jp' = -hcone1. So the term is -cross(q, uw jp') = hcone1.

     So the expansion is: hcone2 + hcone1 - (sp+tp)*C10\\_jp'.
     And this < 0 from the weighted C11.
     So: hcone1 + hcone2 < (sp+tp)*C10\\_jp'. \\<checkmark> Known bound, not contradictory.\<close>
  \<comment> \<open>This approach alone doesn't give a contradiction. We need the dual C11 for edge (jp, jp+1).\<close>
  \<comment> \<open>TAKE 2: Use C11 with edge (jp, jp+1) and vertices jp', jp'+1.\<close>
  have hne3: "jp' \<noteq> jp" using hne by (by100 auto)
  have hne3b: "jp' \<noteq> Suc jp mod nw" using hne_adj1 by (by100 auto)
  have hC11_jp'_on_jp: "(vxw jp' - vxw jp)*(vyw(Suc jp mod nw) - vyw jp) -
      (vyw jp' - vyw jp)*(vxw(Suc jp mod nw) - vxw jp) < 0"
    using hC11[rule_format, OF hjp hjp' hne3 hne3b] by (by100 auto)
  have hne4: "Suc jp' mod nw \<noteq> jp" using hne_adj2 by (by100 auto)
  have hne2b_sym: "Suc jp' mod nw \<noteq> Suc jp mod nw" using hne2b by (by100 auto)
  have hC11_jp1'_on_jp: "(vxw(Suc jp' mod nw) - vxw jp)*(vyw(Suc jp mod nw) - vyw jp) -
      (vyw(Suc jp' mod nw) - vyw jp)*(vxw(Suc jp mod nw) - vxw jp) < 0"
    using hC11[rule_format, OF hjp hSjp' hne4 hne2b_sym] by (by100 auto)
  \<comment> \<open>Hmm but hne2b was Suc jp mod nw \\<noteq> Suc jp' mod nw. Need: Suc jp' mod nw \\<noteq> Suc jp mod nw.
     That's the same as hne2b by symmetry.\<close>
  \<comment> \<open>Now: C11[i=jp, k=jp'] gives cross(uw(jp')-uw(jp), uw(jp+1)-uw(jp)) < 0.
     Expanding: Im(cnj(uw jp')*uw(jp+1)) - Im(cnj(uw jp')*uw(jp)) - Im(cnj(uw jp)*uw(jp+1)) < 0.
     = sin(b) - sin(a) - sin\\_theta\\_jp < 0. (sin\\_theta\\_jp = sin of theta jp, which is > 0.)
     Where sin\\_theta\\_jp = Im(cnj(uw jp)*uw(jp+1)) = the C10 value for edge jp.\<close>
  \<comment> \<open>Similarly C11[i=jp, k=Suc jp'] gives:
     sin(d') - sin(c') - sin\\_theta\\_jp < 0 where appropriate... need careful indices.
     Actually: sin(alpha(jp+1) - alpha(Suc jp')) - sin(alpha(jp) - alpha(Suc jp')) - sin(theta jp) < 0.
     = sin(-d) - sin(-c) - sin(theta jp) = -sin(d) + sin(c) - sin(theta jp) < 0.
     i.e., sin(c) - sin(d) < sin(theta jp).\<close>
  \<comment> \<open>So we get 4 C11 inequalities:
     (I) sin(a) + sin(c) < sin(\\<theta>\\_{jp'})     [C11 edge jp', vertex jp]
     (II) sin(b) + sin(d) < sin(\\<theta>\\_{jp'})    [C11 edge jp', vertex jp+1]
     (III) sin(b) - sin(a) < sin(\\<theta>\\_jp)   [C11 edge jp, vertex jp']
     (IV) sin(c) - sin(d) < sin(\\<theta>\\_jp)    [C11 edge jp, vertex jp'+1]

     And cone conditions:
     (H1) sp*sin(a) + tp*sin(b) \\<ge> 0
     (H2) sp*sin(c) + tp*sin(d) \\<ge> 0

     Take sp*(I) + tp*(II): sp*sin(a) + sp*sin(c) + tp*sin(b) + tp*sin(d) < (sp+tp)*sin(\\<theta>\\_{jp'}).
     = (H1) + (H2) < (sp+tp)*sin(\\<theta>\\_{jp'}).

     Take tp*(III) + sp*(IV): tp*sin(b) - tp*sin(a) + sp*sin(c) - sp*sin(d) < (sp+tp)*sin(\\<theta>\\_jp).
     = (H1) - (H2) + 2*(sp*sin(c) - tp*sin(a)) ... hmm not clean.
     Actually: tp*sin(b) - tp*sin(a) + sp*sin(c) - sp*sin(d)
     = (sp*sin(c) + tp*sin(b)) - (tp*sin(a) + sp*sin(d))

     From (H1)+(H2) \\<ge> 0 and < (sp+tp)*sin(\\<theta>\\_{jp'}): nothing new.

     Take sp*(III) + tp*(IV): sp*sin(b) - sp*sin(a) + tp*sin(c) - tp*sin(d) < (sp+tp)*sin(\\<theta>\\_jp).
     = (sp*sin(b) + tp*sin(c)) - (sp*sin(a) + tp*sin(d)) < (sp+tp)*sin(\\<theta>\\_jp).

     Hmm, let me define X = sp*sin(a) + tp*sin(d) and Y = sp*sin(b) + tp*sin(c).
     Then: X + Y = (H1) + (H2) \\<ge> 0.
     Y - X < (sp+tp)*sin(\\<theta>\\_jp) from sp*(III) + tp*(IV).
     X + Y < (sp+tp)*sin(\\<theta>\\_{jp'}) from sp*(I) + tp*(II).

     Also: determinant condition. sin(a)*sin(d) - sin(b)*sin(c) < 0.

     From the Cauchy-like computation:
     (H1)*(H2) = (sp*sin(a)+tp*sin(b))*(sp*sin(c)+tp*sin(d))
     = sp^2*sin(a)*sin(c) + sp*tp*sin(a)*sin(d) + sp*tp*sin(b)*sin(c) + tp^2*sin(b)*sin(d)
     \\<ge> 0 (since both factors \\<ge> 0).

     (sp*sin(b)+tp*sin(c))*(sp*sin(a)+tp*sin(d)) = X*Y... hmm.

     sp^2*sin(a)*sin(b) + sp*tp*sin(b)*sin(d) + sp*tp*sin(a)*sin(c) + tp^2*sin(c)*sin(d).

     (H1)*(H2) - X*Y = sp*tp*(sin(a)*sin(d)+sin(b)*sin(c)) - sp*tp*(sin(b)*sin(d)+sin(a)*sin(c))
     = sp*tp*(sin(a)*sin(d) + sin(b)*sin(c) - sin(b)*sin(d) - sin(a)*sin(c))
     = sp*tp*(sin(a)*(sin(d)-sin(c)) + sin(b)*(sin(c)-sin(d)))
     = sp*tp*(sin(a)-sin(b))*(sin(d)-sin(c)).

     So (H1)*(H2) = X*Y + sp*tp*(sin(a)-sin(b))*(sin(d)-sin(c)).

     Not sure this helps.\<close>
  \<comment> \<open>FINAL APPROACH: Direct coordinate computation with the cone + C11 + non-adjacency.\<close>
  \<comment> \<open>Key algebraic identity: hweighted = hcone1 + hcone2 - (sp+tp)*C10(jp'). Since hweighted < 0:
     hcone1 + hcone2 < (sp+tp)*C10(jp'). Similarly, hW2 expands to another bound.
     Together with hcone1, hcone2 \\<ge> 0 and C10 > 0, these force sp = tp = 0. Contradiction.\<close>
  \<comment> \<open>hweighted = sp*C11(jp',jp) + tp*C11(jp',jp+1) < 0 (already proved).
     Expanding in coordinates: it equals (qx - (sp+tp)*x\\_{jp'}) * \\<Delta>y' - (qy - (sp+tp)*y\\_{jp'}) * \\<Delta>x'.
     = hcone2 + hcone1 - (sp+tp)*C10'. But NOT via subtraction - via expansion.
     Actually: the expansion gives hcone1+hcone2 < (sp+tp)*C10' which is not False.
     Similarly for the other edge. The TWO bounds together don't directly force False either.
     We need the cross-term: combine cone1 with C11 on edge jp and cone2 with C11 on edge jp'.\<close>
  \<comment> \<open>DIRECT PROOF: From hcone1 \\<ge> 0 and C11(jp, jp') < 0, derive a bound on sp*sin(b).
     From hcone2 \\<ge> 0 and C11(jp', jp+1) < 0, derive a bound on tp*sin(d).
     Together with the weighted C11 sums, derive sp = tp = 0.\<close>
  have hcone1_plus_hcone2: "vxw jp' * (sp*vyw jp + tp*vyw(Suc jp mod nw)) -
          vyw jp' * (sp*vxw jp + tp*vxw(Suc jp mod nw)) +
      ((sp*vxw jp + tp*vxw(Suc jp mod nw)) * vyw(Suc jp' mod nw) -
          (sp*vyw jp + tp*vyw(Suc jp mod nw)) * vxw(Suc jp' mod nw))
    < (sp+tp) * (vxw jp' * vyw(Suc jp' mod nw) - vyw jp' * vxw(Suc jp' mod nw))"
    using hweighted hcone1 hcone2 by (by100 argo)
  \<comment> \<open>Now derive hcone1 + hcone2 < (sp+tp)*C10(jp'). This is bound (A).\<close>
  \<comment> \<open>Similarly derive bound (B) from the dual C11 weighted sum.\<close>
  \<comment> \<open>The two bounds together with hcone1, hcone2 \\<ge> 0 should give the contradiction.\<close>
  \<comment> \<open>Actually, we already have the hweighted < 0 which gives the bound. The question is how
     to combine with the dual bound to get False. Let me try sledgehammer on show False
     with all available facts.\<close>
  \<comment> \<open>Dual weighted C11 for edge jp.\<close>
  have hweighted2: "sp * ((vxw jp' - vxw jp)*(vyw(Suc jp mod nw) - vyw jp) -
      (vyw jp' - vyw jp)*(vxw(Suc jp mod nw) - vxw jp)) +
    tp * ((vxw(Suc jp' mod nw) - vxw jp)*(vyw(Suc jp mod nw) - vyw jp) -
      (vyw(Suc jp' mod nw) - vyw jp)*(vxw(Suc jp mod nw) - vxw jp)) < 0"
  proof -
    define xjp2 where "xjp2 = (vxw jp' - vxw jp)*(vyw(Suc jp mod nw) - vyw jp) -
        (vyw jp' - vyw jp)*(vxw(Suc jp mod nw) - vxw jp)"
    define xjp12 where "xjp12 = (vxw(Suc jp' mod nw) - vxw jp)*(vyw(Suc jp mod nw) - vyw jp) -
        (vyw(Suc jp' mod nw) - vyw jp)*(vxw(Suc jp mod nw) - vxw jp)"
    have hxjp2: "xjp2 < 0" using hC11_jp'_on_jp unfolding xjp2_def by linarith
    have hxjp12: "xjp12 < 0" using hC11_jp1'_on_jp unfolding xjp12_def by linarith
    have "sp * xjp2 + tp * xjp12 < 0"
    proof (cases "sp > 0")
      case True
      from mult_pos_neg[OF this hxjp2] have "sp * xjp2 < 0" .
      moreover have "xjp12 \<le> 0" using hxjp12 by linarith
      from mult_nonneg_nonpos[OF htp this] have "tp * xjp12 \<le> 0" .
      ultimately show ?thesis by linarith
    next
      case False hence "sp = 0" using hsp by linarith
      hence "tp > 0" using hst by linarith
      from mult_pos_neg[OF this hxjp12] have "tp * xjp12 < 0" .
      moreover have "sp * xjp2 = 0" using \<open>sp = 0\<close> by (by100 simp)
      ultimately show ?thesis by linarith
    qed
    thus ?thesis unfolding xjp2_def xjp12_def by linarith
  qed
  \<comment> \<open>Derive analogous bound from hweighted2: cross of (sp*uw(jp')+tp*uw(jp'+1)) with edge jp.\<close>
  have hbound_B: "sp * (vxw jp' * vyw(Suc jp mod nw) - vyw jp' * vxw(Suc jp mod nw)) +
      tp * (vxw(Suc jp' mod nw) * vyw(Suc jp mod nw) - vyw(Suc jp' mod nw) * vxw(Suc jp mod nw))
    - sp * (vxw jp' * vyw jp - vyw jp' * vxw jp)
    - tp * (vxw(Suc jp' mod nw) * vyw jp - vyw(Suc jp' mod nw) * vxw jp)
    < (sp+tp) * (vxw jp * vyw(Suc jp mod nw) - vyw jp * vxw(Suc jp mod nw))"
    using hweighted2 by (by100 argo)
  \<comment> \<open>Express using cross products: sp*cross(jp',jp+1) + tp*cross(jp'+1,jp+1)
     - sp*cross(jp',jp) - tp*cross(jp'+1,jp) < (sp+tp)*C10(jp).\<close>
  \<comment> \<open>Note: cross(a,b) = -cross(b,a). So this becomes:
     sp*[-Im(cnj(uw(jp+1))*uw(jp'))] + tp*[-Im(cnj(uw(jp+1))*uw(jp'+1))]
     + sp*Im(cnj(uw jp)*uw(jp')) + tp*Im(cnj(uw jp)*uw(jp'+1))
     < (sp+tp)*C10(jp).
     i.e., sp*[Im(cnj(uw jp)*uw(jp')) - Im(cnj(uw(jp+1))*uw(jp'))]
     + tp*[Im(cnj(uw jp)*uw(jp'+1)) - Im(cnj(uw(jp+1))*uw(jp'+1))]
     < (sp+tp)*C10(jp).

     The terms are:
     Im(cnj(uw jp)*uw(jp')) - Im(cnj(uw(jp+1))*uw(jp')) = -[hcone1 with q=(1,0,...) version]. Hmm not clear.

     Actually: sp*cross(jp',jp+1) - sp*cross(jp',jp) = sp*cross(jp', jp+1-jp) = sp*cross(jp', uw(jp+1)-uw(jp)).
     And the RHS involves (sp+tp)*cross(jp, jp+1-jp) = (sp+tp)*cross(jp, uw(jp+1)-uw(jp)).
     But cross(jp, uw(jp+1)-uw(jp)) = cross(uw jp, uw(jp+1)) - cross(uw jp, uw jp) = C10(jp).

     So the inequality is: sp*cross(uw(jp'), uw(jp+1)-uw(jp)) + tp*cross(uw(jp'+1), uw(jp+1)-uw(jp))
     < (sp+tp)*C10(jp).

     Now: cross(uw(jp'), uw(jp+1)-uw(jp)) = -hcone_jp'(cone condition using edge jp direction).
     And cross(uw(jp'+1), uw(jp+1)-uw(jp)) = -hcone_jp'+1(similar).

     These relate to how far uw(jp') and uw(jp'+1) are from the edge (jp, jp+1).\<close>
  \<comment> \<open>Use hcone1\\_sin, hcone2\\_sin and the C11 bounds in sin form to derive contradiction.\<close>
  \<comment> \<open>Abbreviations for the sine arguments.\<close>
  define sa where "sa = sin(alpha jp - alpha jp')"
  define sb where "sb = sin(alpha (Suc jp mod nw) - alpha jp')"
  define sc where "sc = sin(alpha (Suc jp' mod nw) - alpha jp)"
  define sd where "sd = sin(alpha (Suc jp' mod nw) - alpha (Suc jp mod nw))"
  have hcone1_ab: "sp * sa + tp * sb \<ge> 0"
    using hcone1_sin unfolding sa_def sb_def by (by100 simp)
  have hcone2_cd: "sp * sc + tp * sd \<ge> 0"
    using hcone2_sin unfolding sc_def sd_def by (by100 simp)
  \<comment> \<open>C11 in sin form via halpha\\_cis:
     C11(jp', jp) gives: cross(uw(jp)-uw(jp'), uw(jp'+1)-uw(jp')) < 0.
     In cis form: Im(cnj(uw jp)*uw(jp'+1)) + Im(cnj(uw jp')*uw(jp)) - Im(cnj(uw jp')*uw(jp'+1)) < 0.
     = sin(alpha(Suc jp')-alpha(jp)) + sin(alpha(jp)-alpha(jp')) - sin(alpha(Suc jp')-alpha(jp')) < 0
     Wait: Im(cnj(uw jp)*uw(jp'+1)): in the halpha\\_cis framework, this is sin(alpha(Suc jp')-alpha(jp)).
     But halpha\\_cis uses the RAW cis values, not the alpha-based ones necessarily.
     Actually: from halpha\\_cis: cnj(Complex(vxw j)(vyw j))*Complex(vxw j')(vyw j') = cis(alpha j' - alpha j).
     So Im = sin(alpha j' - alpha j).
     Thus Im(cnj(uw jp)*uw(jp'+1)) = sin(alpha(Suc jp' mod nw) - alpha jp) = sc.
     Im(cnj(uw jp')*uw(jp)) = sin(alpha jp - alpha jp') = sa.
     Im(cnj(uw jp')*uw(jp'+1)) = sin(alpha(Suc jp' mod nw) - alpha jp') = sin of theta jp' (mod 2\\<pi>).

     So C11(jp',jp) in sin form: sc + sa - sin(\\<theta>) < 0 where sin(\\<theta>) = sin(alpha(Suc jp' mod nw) - alpha jp').
     I.e., sa + sc < sin(\\<theta>).

     But sin(\\<theta>) is NOT directly sin(theta jp') because of the wrapping issue with alpha(Suc jp' mod nw).
     HOWEVER, from hsin\\_ac\\_pos (proved earlier): sin(alpha(Suc jp' mod nw) - alpha jp') > 0.
     And this IS the same as the C10 value.\<close>
  define stheta' where "stheta' = sin(alpha(Suc jp' mod nw) - alpha jp')"
  define stheta where "stheta = sin(alpha(Suc jp mod nw) - alpha jp)"
  have hstheta'_pos: "stheta' > 0"
  proof -
    have "Im (cnj (uw jp') * uw (Suc jp' mod nw)) > 0" using hC10_im hjp' by (by100 auto)
    moreover have "cnj (uw jp') * uw (Suc jp' mod nw) = cis(alpha(Suc jp' mod nw) - alpha jp')"
    proof -
      from halpha_cis[rule_format, OF hjp' hSjp']
      show ?thesis unfolding uw_def by (by100 simp)
    qed
    ultimately show ?thesis unfolding stheta'_def by (by100 simp)
  qed
  have hstheta_pos: "stheta > 0"
  proof -
    have "Im (cnj (uw jp) * uw (Suc jp mod nw)) > 0" using hC10_im hjp by (by100 auto)
    moreover have "cnj (uw jp) * uw (Suc jp mod nw) = cis(alpha(Suc jp mod nw) - alpha jp)"
    proof -
      from halpha_cis[rule_format, OF hjp hSjp]
      show ?thesis unfolding uw_def by (by100 simp)
    qed
    ultimately show ?thesis unfolding stheta_def by (by100 simp)
  qed
  \<comment> \<open>C11 bounds in sin form:\<close>
  \<comment> \<open>(I) sa + sc < stheta'   [from C11(jp',jp)]\<close>
  \<comment> \<open>(II) sb + sd < stheta'  [from C11(jp',jp+1)]\<close>
  \<comment> \<open>(III) sb - sa < stheta  [from C11(jp,jp')]\<close>
  \<comment> \<open>(IV) sc - sd < stheta   [from C11(jp,jp'+1)]\<close>
  \<comment> \<open>C11 bounds in sin form (not directly used in current proof).\<close>
  \<comment> \<open>Now derive the contradiction from hcone1\\_ab, hcone2\\_cd, C11 bounds, and non-adjacency.
     The proof:
     Case 1: sa \\<le> 0 and sb \\<le> 0. Then sp*sa+tp*sb \\<le> 0. With sp+tp>0 and one < 0: < 0. Contradicts hcone1 \\<ge> 0.
     Case 2: sa \\<le> 0 and sb > 0. From (III): sb < sa + stheta \\<le> stheta.
       From (I): sc < stheta' - sa. Since sa \\<le> 0: sc < stheta' + |sa|.
       Also sd = sc - stheta + ... hmm, sd is not simply expressible.
       Use determinant: det = sa*sd - sb*sc = -(stheta'*stheta) [per the identity].
       ... still complex.
     Actually, just use sp*(I) + tp*(II): sp*(sa+sc) + tp*(sb+sd) < (sp+tp)*stheta'.
       = hcone1\\_ab + hcone2\\_cd < (sp+tp)*stheta'. But \\<ge> 0 and < positive. No contradiction.
     AND sp*(III) + tp*(IV): sp*(sb-sa) + tp*(sc-sd) < (sp+tp)*stheta.
       = (sp*sb+tp*sc) - (sp*sa+tp*sd) < (sp+tp)*stheta.

     Define X = sp*sa + tp*sd, Y = sp*sb + tp*sc.
     X + Y = hcone1 + hcone2 \\<ge> 0.
     Y - X < (sp+tp)*stheta.
     X + Y < (sp+tp)*stheta'.

     So: Y < ((sp+tp)*stheta' + (sp+tp)*stheta)/2 = (sp+tp)*(stheta'+stheta)/2.
     And: X > Y - (sp+tp)*stheta. From X + Y \\<ge> 0: X \\<ge> -Y. If Y > 0: X could be negative.

     Now from the determinant: sa*sd - sb*sc = -(stheta'*stheta) < 0.
     H1*H2 = (sp*sa+tp*sb)*(sp*sc+tp*sd) \\<ge> 0.
     Y^2 - X^2 = (Y+X)(Y-X) = (H1+H2)(Y-X) < (H1+H2)*(sp+tp)*stheta.
     And Y^2 - X^2 = (sp*sb+tp*sc)^2 - (sp*sa+tp*sd)^2.
     = sp^2*(sb^2-sa^2) + 2*sp*tp*(sb*sc-sa*sd) + tp^2*(sc^2-sd^2).
     = sp^2*(sb-sa)*(sb+sa) + 2*sp*tp*(sb*sc-sa*sd) + tp^2*(sc-sd)*(sc+sd).

     This is getting nowhere. Let me just try the specific approach:
     For ALL non-adjacent sectors, sa \\<le> 0 and sb \\<le> 0 (when jp < jp', non-wrapping).
     This gives immediate contradiction.\<close>
  \<comment> \<open>From non-adjacency: there are at least 2 sectors between jp and jp' (in one direction).
     For jp < jp': alpha(jp+1) < alpha(jp') (since non-adjacent).
     So alpha(jp+1) - alpha(jp') < 0 \\<to> sb is sin of a negative angle.
     And alpha(jp) - alpha(jp') < alpha(jp+1) - alpha(jp') < 0 \\<to> sa is sin of a negative angle.
     BUT: sin of negative angle is not always negative! sin(-x) = -sin(x), but sin(x+2\\<pi>) = sin(x).
     The issue is that alpha(jp) - alpha(jp') could be < -\\<pi> (wrapping), making sin positive.

     From alpha ordering: alpha(0) = 0, ..., alpha(nw) = 2\\<pi>.
     For jp < jp': alpha(jp) \\<in> [0, alpha(jp')), alpha(jp') \\<in> (alpha(jp+1), 2\\<pi>).
     alpha(jp) - alpha(jp') \\<in> (-2\\<pi>, 0).
     alpha(jp+1) - alpha(jp') \\<in> (-2\\<pi>+theta\\_jp, 0).

     sin(alpha(jp)-alpha(jp')) < 0 when alpha(jp)-alpha(jp') \\<in> (-\\<pi>, 0).
     This holds when alpha(jp') - alpha(jp) < \\<pi>.

     If alpha(jp') - alpha(jp) \\<ge> \\<pi>: sa = sin(alpha(jp)-alpha(jp')) = sin(negative > -2\\<pi>) could be positive.

     In this case, use the dual C11 for edge jp: sb - sa < stheta. This bounds sb relative to sa.

     If sa > 0 (large gap case): sb = sin(alpha(jp+1)-alpha(jp')) where alpha(jp+1)-alpha(jp') < 0.
     sin(alpha(jp+1)-alpha(jp')) could be < 0 (if gap < \\<pi>) or \\<ge> 0 (if gap > \\<pi>).

     From (III): sb - sa < stheta. sa > 0: sb < sa + stheta.
     We need sb \\<le> 0 for hcone1 contradiction. sb < sa + stheta doesn't give sb \\<le> 0 directly.

     BUT: from (I): sa + sc < stheta'. Since sa > 0 and stheta' < \\<pi> (actually stheta' = sin(\\<theta>\\_{jp'}) > 0):
     sc < stheta' - sa. If sa \\<ge> stheta': sc < 0.

     For non-wrapping jp < jp': alpha(jp+1) \\<le> alpha(jp'-1) < alpha(jp') (non-adjacent).
     alpha(jp) < alpha(jp+1) < alpha(jp').
     sa > 0 requires alpha(jp') - alpha(jp) > \\<pi>.
     alpha(Suc jp' mod nw) - alpha(jp) = alpha(jp'+1) - alpha(jp) = (alpha(jp')-alpha(jp)) + theta\\_{jp'}.
     If alpha(jp')-alpha(jp) > \\<pi>: sc = sin(alpha(jp'+1)-alpha(jp)) = sin(something > \\<pi>).
     If alpha(jp'+1)-alpha(jp) < 2\\<pi> (always true for valid polygon): sc = sin(something in (\\<pi>, 2\\<pi>)) < 0. \\<checkmark>!

     Similarly: sd = sin(alpha(jp'+1) - alpha(jp+1)). alpha(jp'+1) - alpha(jp+1) = (alpha(jp')-alpha(jp+1)) + theta\\_{jp'}.
     alpha(jp')-alpha(jp+1) > 0 (non-adjacent). So alpha(jp'+1)-alpha(jp+1) > theta\\_{jp'} > 0.
     If alpha(jp'+1)-alpha(jp+1) > \\<pi>: sd = sin(something > \\<pi>) < 0 (if < 2\\<pi>).
     alpha(jp'+1)-alpha(jp+1) < 2\\<pi> (always). So sd could be < 0.
     But alpha(jp'+1)-alpha(jp+1) could be \\<le> \\<pi>: sd \\<ge> 0.

     When sd \\<ge> 0: sc < 0 (proved above). hcone2 = sp*sc + tp*sd.
     If sc < 0 and sd \\<ge> 0: hcone2 could be \\<ge> 0 (tp*sd compensates sp*sc).
     Use determinant: det = sa*sd - sb*sc. And... still the same issues.

     OK let me just try: for the case sa > 0 (large gap, alpha(jp')-alpha(jp) > \\<pi>):
     sc < 0 (proved: alpha(jp'+1)-alpha(jp) > \\<pi> so sin < 0).
     From hcone2 \\<ge> 0: sp*sc + tp*sd \\<ge> 0. sc < 0: tp*sd \\<ge> -sp*sc > 0 (if sp > 0).
     So tp*sd > 0 \\<to> tp > 0 and sd > 0 (or sp = 0).

     Sub-case sd > 0 and tp > 0:
     From (II): sb + sd < stheta'. sd > 0: sb < stheta' - sd < stheta'.
     From (III): sb - sa < stheta. sa > 0: sb < sa + stheta. Not useful for sb \\<le> 0.
     From hcone1: sp*sa + tp*sb \\<ge> 0. sa > 0: this is fine even if sb < 0.
     From determinant: sa*sd - sb*sc < 0. sa > 0, sd > 0: sa*sd > 0. sb*sc: sc < 0, so sb*sc has sign -sb.
     sa*sd < sb*sc = sb*(negative) = -sb*|sc|. So sa*sd < -sb*|sc|. sa*sd > 0 \\<to> -sb*|sc| > 0 \\<to> sb < 0. \\<checkmark>!

     So sb < 0! Now: sp*sa + tp*sb \\<ge> 0 and sp*sc + tp*sd \\<ge> 0.
     sa > 0, sb < 0, sc < 0, sd > 0. The determinant tells us sa*sd < sb*sc (both products negative?).
     sa > 0, sd > 0: sa*sd > 0. sb < 0, sc < 0: sb*sc > 0. So sa*sd < sb*sc means sa*sd < sb*sc.
     Both positive. This is a magnitude condition.

     Use: multiply hcone1 by sd > 0: sp*sa*sd + tp*sb*sd \\<ge> 0.
     Multiply hcone2 by (-sb) > 0: -sp*sc*sb - tp*sd*sb \\<ge> 0 i.e. sp*(-sc)*sb + tp*(-sd)*sb... hmm signs.
     Actually: (-sb)*(sp*sc + tp*sd) \\<ge> 0 since -sb > 0 and hcone2 \\<ge> 0.
     = -sp*sb*sc - tp*sb*sd \\<ge> 0.

     Adding: sp*sa*sd + tp*sb*sd - sp*sb*sc - tp*sb*sd \\<ge> 0.
     = sp*(sa*sd - sb*sc) \\<ge> 0.
     = sp*det \\<ge> 0. But det < 0 and sp \\<ge> 0: sp*det \\<le> 0.
     So sp*det = 0 \\<to> sp = 0 (since det \\<noteq> 0).

     With sp = 0: hcone1 = tp*sb \\<ge> 0. sb < 0, tp \\<ge> 0: tp*sb \\<le> 0. So tp*sb = 0.
     tp > 0 (from earlier): sb = 0. But we derived sb < 0. Contradiction!

     FANTASTIC! This works! The key was:
     1. From sa > 0 and alpha constraints: sc < 0.
     2. From determinant + sa > 0, sd > 0, sc < 0: sb < 0.
     3. Determinant argument with weights sd and -sb: sp = 0.
     4. Then tp*sb = 0 with sb < 0 forces tp = 0. sp+tp = 0. Contradiction.

     Sub-case sd \\<le> 0: sc < 0 and sd \\<le> 0. hcone2 = sp*sc + tp*sd \\<le> 0 (since sp,tp \\<ge> 0 and sc,sd \\<le> 0).
     With sp+tp > 0 and sc < 0 or sd < 0: hcone2 < 0. Contradicts hcone2 \\<ge> 0. \\<checkmark>

     So for sa > 0: the argument works in all sub-cases! \\<checkmark>

     For sa \\<le> 0 (small gap, alpha(jp')-alpha(jp) \\<le> \\<pi>):
     sb = sin(alpha(jp+1)-alpha(jp')). alpha(jp+1)-alpha(jp') < 0 (non-adjacent).
     If alpha(jp')-alpha(jp+1) \\<le> \\<pi>: alpha(jp+1)-alpha(jp') \\<ge> -\\<pi>. sin \\<le> 0. So sb \\<le> 0. \\<checkmark>
     If alpha(jp')-alpha(jp+1) > \\<pi>: sb = sin(alpha(jp+1)-alpha(jp')) where alpha(jp+1)-alpha(jp') < -\\<pi>.
     sin > 0. So sb > 0. But alpha(jp')-alpha(jp+1) > \\<pi> AND alpha(jp')-alpha(jp) \\<le> \\<pi>:
     alpha(jp+1)-alpha(jp) = theta\\_jp < \\<pi>. So alpha(jp')-alpha(jp+1) = (alpha(jp')-alpha(jp)) - theta\\_jp.
     alpha(jp')-alpha(jp) \\<le> \\<pi> and theta\\_jp > 0: alpha(jp')-alpha(jp+1) < \\<pi>. Contradiction!
     So alpha(jp')-alpha(jp+1) \\<le> \\<pi>, hence sb \\<le> 0.

     With sa \\<le> 0 and sb \\<le> 0: hcone1 = sp*sa + tp*sb \\<le> 0. With sp+tp > 0:
     If sa < 0 or sb < 0: hcone1 < 0. Contradicts hcone1 \\<ge> 0. \\<checkmark>
     If sa = 0 and sb = 0: sp*0 + tp*0 = 0 \\<ge> 0. \\<checkmark> (no contradiction from hcone1 alone).
     But sa = 0 means alpha(jp) = alpha(jp') (mod \\<pi>). Since both \\<in> [0, 2\\<pi>): sa = 0 implies
     alpha(jp) = alpha(jp') or alpha(jp) = alpha(jp') + \\<pi>.
     The first: jp = jp' (alpha increasing). Contradicts hne. \\<checkmark>
     The second: alpha(jp) = alpha(jp') + \\<pi>. Then sb = sin(alpha(jp+1) - alpha(jp') - \\<pi> + \\<pi>)... hmm.
     Actually sa = sin(alpha(jp)-alpha(jp')) = 0 means alpha(jp)-alpha(jp') = k*\\<pi>.
     k = 0: jp = jp'. Contradiction.
     k = -1: alpha(jp')-alpha(jp) = \\<pi>.
     Then sb = sin(alpha(jp+1)-alpha(jp')) = sin(theta\\_jp - \\<pi>) = -sin(\\<pi>-theta\\_jp) = -sin(theta\\_jp) < 0 (since theta\\_jp \\<in> (0,\\<pi>), sin(theta\\_jp) > 0, wait: sin(theta\\_jp - \\<pi>) = -sin(\\<pi> - theta\\_jp) = -sin(theta\\_jp)... hmm.
     Actually sin(x - \\<pi>) = -sin(\\<pi> - x) for x \\<in> (0,\\<pi>)? No: sin(x - \\<pi>) = sin(x)*cos(\\<pi>) - cos(x)*sin(\\<pi>) = -sin(x). So sin(theta\\_jp - \\<pi>) = -sin(theta\\_jp) < 0. sb < 0.
     Then hcone1 = sp*0 + tp*(-sin(theta\\_jp)) < 0 (since tp \\<ge> 0, sin > 0). Wait: tp*sb = tp*(-sin(theta\\_jp)) \\<le> 0 (tp \\<ge> 0). If tp > 0: < 0. Contradicts hcone1 \\<ge> 0.
     If tp = 0: sp > 0 (from hst). hcone1 = 0 \\<ge> 0 \\<checkmark>. hcone2 = sp*sc + 0 \\<ge> 0 \\<to> sc \\<ge> 0.
     sc = sin(alpha(jp'+1)-alpha(jp)) = sin(alpha(jp') + theta\\_{jp'} - alpha(jp)) = sin(\\<pi> + theta\\_{jp'}).
     sin(\\<pi> + theta\\_{jp'}) = -sin(theta\\_{jp'}) < 0. So sc < 0. Contradicts sc \\<ge> 0. \\<checkmark>

     So sa = 0 also leads to contradiction (in all sub-cases).

     Therefore: for jp < jp' (non-wrapping), the contradiction is established.

     For jp > jp' or wrapping cases: symmetric argument (swap roles of the two sectors).
     Actually, the same argument applies because the C11 bounds are symmetric:
     the angular gap from the OTHER direction (jp' to jp going CCW) has similar bounds.\<close>
  \<comment> \<open>OK, the proof strategy for the show False:
     CASE 1 (sa \\<le> 0):
       Show sb \\<le> 0 (from non-adjacency + theta \\<in> (0,\\<pi>)).
       Sub-case sb < 0 or sa < 0: hcone1 < 0. Contradiction.
       Sub-case sa = 0 and sb = 0: derive further contradiction from hcone2.
     CASE 2 (sa > 0):
       Show sc < 0 (from non-adjacency + alpha bounds).
       Sub-case sd \\<le> 0: sc < 0 and sd \\<le> 0 \\<to> hcone2 < 0. Contradiction.
       Sub-case sd > 0: determinant argument (multiply hcone1*sd, hcone2*(-sb)) \\<to> sp=0, tp=0.\<close>
  have halpha_mono: "\<And>m n. m < n \<Longrightarrow> n \<le> nw \<Longrightarrow> alpha m < alpha n"
  proof -
    fix m n :: nat assume "m < n" "n \<le> nw"
    thus "alpha m < alpha n"
    proof (induct "n - Suc m" arbitrary: n)
      case 0
      hence "n = Suc m" by linarith
      with 0 halpha_strict show ?case by (by100 simp)
    next
      case (Suc k)
      have hn1: "n - 1 < nw" using Suc by linarith
      have hn_suc: "Suc(n-1) = n" using Suc by linarith
      have "alpha(n-1) < alpha n"
        using halpha_strict[rule_format, of "n-1"] hn1 hn_suc by (by100 simp)
      moreover have "alpha m < alpha(n-1)"
        using Suc(1)[of "n-1"] Suc(2-4) by linarith
      ultimately show ?case by linarith
    qed
  qed
  \<comment> \<open>Determinant identity (used in both cases).\<close>
  have hdet_neg: "sin(alpha jp - alpha jp') * sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw))
      - sin(alpha(Suc jp mod nw) - alpha jp') * sin(alpha(Suc jp' mod nw) - alpha jp) < 0"
  proof -
    define sa where "sa = alpha jp - alpha jp'"
    define sb where "sb = alpha(Suc jp mod nw) - alpha jp'"
    define sc where "sc = alpha(Suc jp' mod nw) - alpha jp"
    define sd where "sd = alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)"
    have hsd_eq: "sd = (sa + sc) - sb" unfolding sa_def sb_def sc_def sd_def by (by100 simp)
    have "sin sa * sin sd - sin sb * sin sc =
      sin sa * sin((sa+sc) - sb) - sin sb * sin((sa+sc) - sa)"
      using hsd_eq by (by100 simp)
    also have "\<dots> = sin(sa+sc) * sin(sa - sb)"
    proof -
      have e1: "sin((sa+sc) - sb) = sin(sa+sc)*cos sb - cos(sa+sc)*sin sb"
        using sin_diff[of "sa+sc" sb] by (by100 simp)
      have e2: "sin((sa+sc) - sa) = sin(sa+sc)*cos sa - cos(sa+sc)*sin sa"
        using sin_diff[of "sa+sc" sa] by (by100 simp)
      have "sin sa * sin((sa+sc) - sb) - sin sb * sin((sa+sc) - sa) =
        sin sa * (sin(sa+sc)*cos sb - cos(sa+sc)*sin sb)
        - sin sb * (sin(sa+sc)*cos sa - cos(sa+sc)*sin sa)"
        using e1 e2 by (by100 simp)
      also have "\<dots> = sin(sa+sc) * (sin sa * cos sb - sin sb * cos sa)"
        by (by100 algebra)
      also have "\<dots> = sin(sa+sc) * sin(sa - sb)"
        using sin_diff[of sa sb] by (by100 simp)
      finally show ?thesis by (by100 simp)
    qed
    also have "\<dots> = -(sin(sa+sc) * sin(sb - sa))"
    proof -
      have "sin(sa - sb) = -sin(sb - sa)" using sin_minus[of "sb - sa"] by (by100 simp)
      thus ?thesis by (by100 algebra)
    qed
    finally have "sin sa * sin sd - sin sb * sin sc = -(sin(sa+sc) * sin(sb - sa))" .
    moreover have "sin(sa + sc) > 0"
    proof -
      have "sa + sc = alpha(Suc jp' mod nw) - alpha jp'" unfolding sa_def sc_def by (by100 simp)
      thus ?thesis using hstheta'_pos stheta'_def by (by100 simp)
    qed
    moreover have "sin(sb - sa) > 0"
    proof -
      have "sb - sa = alpha(Suc jp mod nw) - alpha jp" unfolding sb_def sa_def by (by100 simp)
      thus ?thesis using hstheta_pos stheta_def by (by100 simp)
    qed
    ultimately have "sin sa * sin sd - sin sb * sin sc < 0"
    proof -
      assume h1: "sin sa * sin sd - sin sb * sin sc = -(sin(sa+sc) * sin(sb - sa))"
      assume h2: "sin(sa + sc) > 0"
      assume h3: "sin(sb - sa) > 0"
      from mult_pos_pos[OF h2 h3] have "sin(sa+sc) * sin(sb-sa) > 0" .
      with h1 show ?thesis by linarith
    qed
    thus ?thesis unfolding sa_def sb_def sc_def sd_def by linarith
  qed
  show False
  proof (cases "jp < jp'")
    case hjp_lt: True
    have hjp_lt_nw1: "jp < nw - 1" using hjp_lt hjp' by linarith
    have hSjp_eq: "Suc jp mod nw = Suc jp" using hjp_lt_nw1 hnw by (by100 auto)
    have hjp1_lt_jp': "Suc jp < jp'" using hjp_lt hne_adj1 hSjp_eq by linarith
    have halpha_gap: "alpha(Suc jp) < alpha jp'"
      using halpha_mono[of "Suc jp" jp'] hjp1_lt_jp' hjp' by linarith
    show False
    proof (cases "alpha jp' - alpha jp \<le> pi")
      case hcase1: True
      have hgap_small: "alpha jp' - alpha(Suc jp) < pi"
      proof -
        have "alpha(Suc jp) - alpha jp > 0" using halpha_strict[rule_format, OF hjp] by linarith
        with hcase1 show ?thesis by linarith
      qed
      have hsb_neg: "sin(alpha(Suc jp) - alpha jp') < 0"
        using halpha_gap hgap_small sin_gt_zero[of "alpha jp' - alpha(Suc jp)"]
              sin_minus[of "alpha jp' - alpha(Suc jp)"] by (by100 simp)
      have hsa_nonpos: "sin(alpha jp - alpha jp') \<le> 0"
        using hcase1 halpha_mono[of jp jp'] hjp_lt hjp'
              sin_ge_zero[of "alpha jp' - alpha jp"]
              sin_minus[of "alpha jp' - alpha jp"] by (by100 simp)
      show False
      proof (cases "tp > 0")
        case True
        have "tp * sin(alpha(Suc jp) - alpha jp') < 0"
          using mult_pos_neg[OF True hsb_neg] .
        moreover have "sp * sin(alpha jp - alpha jp') \<le> 0"
          using mult_nonneg_nonpos[OF hsp hsa_nonpos] .
        ultimately have "sp * sin(alpha jp - alpha jp') + tp * sin(alpha(Suc jp) - alpha jp') < 0"
          by linarith
        hence "sp * sin(alpha jp - alpha jp') + tp * sin(alpha(Suc jp mod nw) - alpha jp') < 0"
          using hSjp_eq by (by100 simp)
        with hcone1_sin show False by linarith
      next
        case False hence "tp = 0" using htp by linarith
        hence "sp > 0" using hst by linarith
        show False
        proof (cases "alpha jp' - alpha jp < pi")
          case True
          have "sin(alpha jp' - alpha jp) > 0"
            using sin_gt_zero[of "alpha jp' - alpha jp"]
                  halpha_mono[of jp jp'] hjp_lt hjp' True by linarith
          hence "sin(alpha jp - alpha jp') < 0"
            using sin_minus[of "alpha jp' - alpha jp"] by (by100 simp)
          from mult_pos_neg[OF \<open>sp > 0\<close> this]
          have "sp * sin(alpha jp - alpha jp') < 0" .
          hence "sp * sin(alpha jp - alpha jp') + tp * sin(alpha(Suc jp mod nw) - alpha jp') < 0"
            using \<open>tp = 0\<close> by (by100 simp)
          with hcone1_sin show False by linarith
        next
          case False
          hence "alpha jp' - alpha jp = pi" using hcase1 by linarith
          \<comment> \<open>gap = pi, tp = 0. hcone2 = sp*sc. sc = sin(alpha(jp'+1)-alpha(jp)).
             alpha(jp'+1)-alpha(jp) = pi + theta'. \\<in> (pi, 2pi). sin < 0. hcone2 < 0.\<close>
          have hsc_here: "sin(alpha(Suc jp' mod nw) - alpha jp) < 0"
          proof -
            have "alpha(Suc jp' mod nw) - alpha jp =
                  (alpha(Suc jp' mod nw) - alpha jp') + pi"
              using \<open>alpha jp' - alpha jp = pi\<close> by linarith
            hence "sin(alpha(Suc jp' mod nw) - alpha jp) =
                  sin((alpha(Suc jp' mod nw) - alpha jp') + pi)" by (by100 metis)
            also have "\<dots> = -sin(alpha(Suc jp' mod nw) - alpha jp')"
              using sin_periodic_pi[of "alpha(Suc jp' mod nw) - alpha jp'"] by (by100 metis)
            finally show ?thesis using hstheta'_pos stheta'_def by linarith
          qed
          from mult_pos_neg[OF \<open>sp > 0\<close> hsc_here]
          have "sp * sin(alpha(Suc jp' mod nw) - alpha jp) < 0" .
          hence "sp * sin(alpha(Suc jp' mod nw) - alpha jp) +
              tp * sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) < 0"
            using \<open>tp = 0\<close> by (by100 simp)
          with hcone2_sin show False by linarith
        qed
      qed
    next
      case hcase2: False
      hence hbig: "alpha jp' - alpha jp > pi" by linarith
      have hsc_neg: "sin(alpha(Suc jp' mod nw) - alpha jp) < 0"
      proof (cases "jp' < nw - 1")
        case True
        hence hSjp'_eq: "Suc jp' mod nw = Suc jp'" using hnw by (by100 auto)
        have "alpha(Suc jp') > alpha jp'" using halpha_strict[rule_format, OF hjp'] by linarith
        hence "alpha(Suc jp') - alpha jp > pi" using hbig by linarith
        hence hlb: "alpha(Suc jp' mod nw) - alpha jp > pi" using hSjp'_eq by (by100 simp)
        have "alpha(Suc jp') < alpha nw"
          using halpha_mono[of "Suc jp'" nw] True hnw by linarith
        moreover have "alpha jp \<ge> 0"
        proof (cases "jp = 0")
          case True with halpha_0 show ?thesis by (by100 simp)
        next
          case False
          from halpha_mono[of 0 jp] False hjp show ?thesis using halpha_0 by linarith
        qed
        ultimately have "alpha(Suc jp') - alpha jp < 2*pi"
          using halpha_nw by linarith
        hence hub: "alpha(Suc jp' mod nw) - alpha jp < 2*pi"
          using hSjp'_eq by (by100 simp)
        from sin_lt_zero[of "alpha(Suc jp' mod nw) - alpha jp"] hlb hub show ?thesis by linarith
      next
        case False
        hence hjp'_last: "jp' = nw - 1" using hjp' by linarith
        hence "Suc jp' mod nw = 0" using hnw by (by100 auto)
        hence hval: "alpha(Suc jp' mod nw) = 0" using halpha_0 by (by100 simp)
        have "jp > 0" using hne_adj2 \<open>Suc jp' mod nw = 0\<close> by linarith
        hence "alpha jp > 0" using halpha_mono[of 0 jp] hjp halpha_0 by linarith
        moreover have "alpha jp < pi"
        proof -
          have "alpha jp' < 2*pi" using halpha_mono[of jp' nw] hjp' halpha_nw by linarith
          with hbig show ?thesis by linarith
        qed
        ultimately have "sin(alpha jp) > 0" using sin_gt_zero[of "alpha jp"] by linarith
        hence "- sin(alpha jp) < 0" by linarith
        hence "sin(-alpha jp) < 0" using sin_minus[of "alpha jp"] by (by100 metis)
        with hval show ?thesis by (by100 simp)
      qed
      show False
      proof (cases "sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) \<le> 0")
        case hsd_nonpos: True
        show False
        proof -
          have hsc_le: "sin(alpha(Suc jp' mod nw) - alpha jp) \<le> 0" using hsc_neg by linarith
          have h1: "sp * sin(alpha(Suc jp' mod nw) - alpha jp) \<le> 0"
            using mult_nonneg_nonpos[OF hsp hsc_le] .
          have h2: "tp * sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) \<le> 0"
            using mult_nonneg_nonpos[OF htp hsd_nonpos] .
          have "sp * sin(alpha(Suc jp' mod nw) - alpha jp) +
              tp * sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) \<le> 0"
            using h1 h2 by linarith
          moreover have "sp * sin(alpha(Suc jp' mod nw) - alpha jp) +
              tp * sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) \<ge> 0"
            using hcone2_sin by linarith
          ultimately have hsum: "sp * sin(alpha(Suc jp' mod nw) - alpha jp) +
              tp * sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) = 0" by linarith
          hence heq1: "sp * sin(alpha(Suc jp' mod nw) - alpha jp) = 0" using h1 h2 by linarith
          have heq2: "tp * sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) = 0" using hsum heq1 by linarith
          show False
          proof (cases "sp > 0")
            case True
            from mult_pos_neg[OF True hsc_neg] heq1 show False by linarith
          next
            case False hence "sp = 0" using hsp by linarith
            hence "tp > 0" using hst by linarith
            from heq2 have "tp * sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) = 0" .
            hence "sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) = 0"
              using \<open>tp > 0\<close> by (by100 simp)
            \<comment> \<open>sd = 0. From det identity: -sb*sc < 0, sc < 0 \\<to> sb < 0. Then hcone1 < 0.\<close>
            have hdet: "sin(alpha jp - alpha jp') * sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw))
                - sin(alpha(Suc jp mod nw) - alpha jp') * sin(alpha(Suc jp' mod nw) - alpha jp) < 0"
              using hdet_neg .
            hence "- sin(alpha(Suc jp mod nw) - alpha jp') * sin(alpha(Suc jp' mod nw) - alpha jp) < 0"
              using \<open>sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) = 0\<close> by (by100 simp)
            hence hsb_sc_pos: "sin(alpha(Suc jp mod nw) - alpha jp') * sin(alpha(Suc jp' mod nw) - alpha jp) > 0"
              by linarith
            have "sin(alpha(Suc jp mod nw) - alpha jp') < 0"
            proof (rule ccontr)
              assume "\<not> sin(alpha(Suc jp mod nw) - alpha jp') < 0"
              hence "sin(alpha(Suc jp mod nw) - alpha jp') \<ge> 0" by linarith
              from mult_nonneg_nonpos[OF this hsc_le]
              have "sin(alpha(Suc jp mod nw) - alpha jp') * sin(alpha(Suc jp' mod nw) - alpha jp) \<le> 0" .
              with hsb_sc_pos show False by linarith
            qed
            from mult_pos_neg[OF \<open>tp > 0\<close> this]
            have "tp * sin(alpha(Suc jp mod nw) - alpha jp') < 0" .
            hence "sp * sin(alpha jp - alpha jp') + tp * sin(alpha(Suc jp mod nw) - alpha jp') < 0"
              using \<open>sp = 0\<close> by (by100 simp)
            with hcone1_sin show False by linarith
          qed
        qed
      next
        case hsd_pos: False
        hence "sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) > 0" by linarith
        have hsa_pos: "sin(alpha jp - alpha jp') > 0"
        proof -
          \<comment> \<open>alpha jp - alpha jp' \\<in> (-2pi, -pi). sin > 0 on (-2pi, -pi).
             Use sin(x + 2pi) = sin(x): sin(alpha jp - alpha jp') = sin(alpha jp - alpha jp' + 2pi).
             alpha jp - alpha jp' + 2pi \\<in> (0, pi). sin > 0.\<close>
          have h1: "alpha jp - alpha jp' + 2*pi > 0"
          proof -
            have "alpha jp \<ge> 0"
            proof (cases "jp = 0")
              case True with halpha_0 show ?thesis by (by100 simp)
            next
              case False from halpha_mono[of 0 jp] False hjp show ?thesis using halpha_0 by linarith
            qed
            moreover have "alpha jp' < 2*pi"
              using halpha_mono[of jp' nw] hjp' halpha_nw by linarith
            ultimately show ?thesis by linarith
          qed
          have h2: "alpha jp - alpha jp' + 2*pi < pi" using hbig by linarith
          have "sin(alpha jp - alpha jp' + 2*pi) > 0"
            using sin_gt_zero[of "alpha jp - alpha jp' + 2*pi"] h1 h2 by linarith
          moreover have "sin(alpha jp - alpha jp') = sin(alpha jp - alpha jp' + 2*pi)"
            using sin_periodic[of "alpha jp - alpha jp'"] by (by100 simp)
          ultimately show ?thesis by linarith
        qed
        have hsb_neg: "sin(alpha(Suc jp mod nw) - alpha jp') < 0"
        proof (rule ccontr)
          assume "\<not> sin(alpha(Suc jp mod nw) - alpha jp') < 0"
          hence "sin(alpha(Suc jp mod nw) - alpha jp') \<ge> 0" by linarith
          have hsc_le: "sin(alpha(Suc jp' mod nw) - alpha jp) \<le> 0" using hsc_neg by linarith
          from mult_nonneg_nonpos[OF \<open>sin(alpha(Suc jp mod nw) - alpha jp') \<ge> 0\<close> hsc_le]
          have "sin(alpha(Suc jp mod nw) - alpha jp') * sin(alpha(Suc jp' mod nw) - alpha jp) \<le> 0" .
          moreover from mult_pos_pos[OF hsa_pos \<open>sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) > 0\<close>]
          have "sin(alpha jp - alpha jp') * sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) > 0" .
          ultimately have "sin(alpha jp - alpha jp') * sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw))
              - sin(alpha(Suc jp mod nw) - alpha jp') * sin(alpha(Suc jp' mod nw) - alpha jp) > 0"
            by linarith
          with hdet_neg show False by linarith
        qed
        have "sp = 0"
        proof -
          define sa where "sa = sin(alpha jp - alpha jp')"
          define sb where "sb = sin(alpha(Suc jp mod nw) - alpha jp')"
          define sc where "sc = sin(alpha(Suc jp' mod nw) - alpha jp)"
          define sd where "sd = sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw))"
          have hsa': "sa > 0" using hsa_pos unfolding sa_def by linarith
          have hsb': "sb < 0" using hsb_neg unfolding sb_def by linarith
          have hsc': "sc < 0" using hsc_neg unfolding sc_def by linarith
          have hsd': "sd > 0" using \<open>sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) > 0\<close>
            unfolding sd_def by linarith
          have hh1: "sp * sa + tp * sb \<ge> 0" using hcone1_sin unfolding sa_def sb_def by (by100 simp)
          have hh2: "sp * sc + tp * sd \<ge> 0" using hcone2_sin unfolding sc_def sd_def by (by100 simp)
          have hdet': "sa * sd - sb * sc < 0" using hdet_neg unfolding sa_def sb_def sc_def sd_def by linarith
          \<comment> \<open>sd * hh1 + (-sb) * hh2 = sp*(sa*sd - sb*sc) = sp*det \\<ge> 0.\<close>
          have "sd * (sp * sa + tp * sb) + (-sb) * (sp * sc + tp * sd) \<ge> 0"
          proof -
            have "sd \<ge> 0" using hsd' by linarith
            from mult_nonneg_nonneg[OF this hh1] have "sd * (sp * sa + tp * sb) \<ge> 0" .
            moreover have "-sb \<ge> 0" using hsb' by linarith
            from mult_nonneg_nonneg[OF this hh2] have "(-sb) * (sp * sc + tp * sd) \<ge> 0" .
            ultimately show ?thesis by linarith
          qed
          moreover have "sd * (sp * sa + tp * sb) + (-sb) * (sp * sc + tp * sd) =
              sp * (sa * sd - sb * sc)" by (by100 algebra)
          ultimately have "sp * (sa * sd - sb * sc) \<ge> 0" by linarith
          with hdet' have "sp \<le> 0"
          proof -
            assume hge: "sp * (sa * sd - sb * sc) \<ge> 0"
            assume hlt: "sa * sd - sb * sc < 0"
            show "sp \<le> 0"
            proof (rule ccontr)
              assume "\<not> sp \<le> 0" hence "sp > 0" by linarith
              from mult_pos_neg[OF this hlt] have "sp * (sa * sd - sb * sc) < 0" .
              with hge show False by linarith
            qed
          qed
          with hsp show ?thesis by linarith
        qed
        hence "tp > 0" using hst by linarith
        from hcone1_sin \<open>sp = 0\<close> have "tp * sin(alpha(Suc jp mod nw) - alpha jp') \<ge> 0"
          by (by100 simp)
        hence "tp * sin(alpha(Suc jp mod nw) - alpha jp') \<ge> 0" .
        moreover from mult_pos_neg[OF \<open>tp > 0\<close> hsb_neg]
        have "tp * sin(alpha(Suc jp mod nw) - alpha jp') < 0" .
        ultimately show False by linarith
      qed
    qed
  next
    case False
    hence hjp_gt: "jp > jp'" using hne by linarith
    \<comment> \<open>Symmetric to jp < jp'. Same argument on hcone2 via c/d angles.\<close>
    have hjp'_lt_nw1: "jp' < nw - 1" using hjp_gt hjp by linarith
    have hSjp'_eq: "Suc jp' mod nw = Suc jp'" using hjp'_lt_nw1 hnw by (by100 auto)
    have hjp1'_lt_jp: "Suc jp' < jp" using hjp_gt hne_adj2 hSjp'_eq by linarith
    have halpha_gap': "alpha(Suc jp') < alpha jp"
      using halpha_mono[of "Suc jp'" jp] hjp1'_lt_jp hjp by linarith
    show False
    proof (cases "alpha jp - alpha jp' \<le> pi")
      case hc1: True
      \<comment> \<open>Small gap: sc < 0, sd \\<le> 0 \\<to> hcone2 \\<le> 0 \\<to> False (with sp+tp > 0).\<close>
      have hsc': "sin(alpha(Suc jp' mod nw) - alpha jp) < 0"
      proof -
        have "0 < alpha jp - alpha(Suc jp')" using halpha_gap' by linarith
        moreover have "alpha jp - alpha(Suc jp') < pi"
        proof -
          have "alpha(Suc jp') > alpha jp'" using halpha_strict[rule_format, OF hjp'] by linarith
          with hc1 show ?thesis by linarith
        qed
        ultimately have "sin(alpha jp - alpha(Suc jp')) > 0"
          using sin_gt_zero[of "alpha jp - alpha(Suc jp')"] by linarith
        thus ?thesis using hSjp'_eq sin_minus[of "alpha jp - alpha(Suc jp')"] by (by100 simp)
      qed
      have hsc_le: "sin(alpha(Suc jp' mod nw) - alpha jp) \<le> 0" using hsc' by linarith
      show False
      proof (cases "sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) \<le> 0")
        case hsd_neg: True
        \<comment> \<open>sd \\<le> 0 and sc < 0: same argument as before.\<close>
        have "sp * sin(alpha(Suc jp' mod nw) - alpha jp) +
            tp * sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) \<le> 0"
          using mult_nonneg_nonpos[OF hsp hsc_le] mult_nonneg_nonpos[OF htp hsd_neg] by linarith
        moreover have "sp * sin(alpha(Suc jp' mod nw) - alpha jp) +
            tp * sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) \<ge> 0"
          using hcone2_sin by linarith
        ultimately have hsum0: "sp * sin(alpha(Suc jp' mod nw) - alpha jp) +
            tp * sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) = 0" by linarith
        hence heq1: "sp * sin(alpha(Suc jp' mod nw) - alpha jp) = 0"
          using mult_nonneg_nonpos[OF hsp hsc_le] mult_nonneg_nonpos[OF htp hsd_neg] by linarith
        show False
        proof (cases "sp > 0")
          case True from mult_pos_neg[OF True hsc'] heq1 show False by linarith
        next
          case False hence "sp = 0" using hsp by linarith
          hence "tp > 0" using hst by linarith
          have "tp * sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) = 0"
            using hsum0 heq1 by linarith
          hence "sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) = 0"
            using \<open>tp > 0\<close> by (by100 simp)
          \<comment> \<open>sd = 0. From det: sb*sc > 0, sc < 0 \\<to> sb < 0. hcone1 = tp*sb < 0.\<close>
          hence "- sin(alpha(Suc jp mod nw) - alpha jp') * sin(alpha(Suc jp' mod nw) - alpha jp) < 0"
            using hdet_neg by (by100 simp)
          hence hsb_sc: "sin(alpha(Suc jp mod nw) - alpha jp') * sin(alpha(Suc jp' mod nw) - alpha jp) > 0"
            by linarith
          have "sin(alpha(Suc jp mod nw) - alpha jp') < 0"
          proof (rule ccontr)
            assume "\<not> sin(alpha(Suc jp mod nw) - alpha jp') < 0"
            hence "sin(alpha(Suc jp mod nw) - alpha jp') \<ge> 0" by linarith
            from mult_nonneg_nonpos[OF this hsc_le]
            have "sin(alpha(Suc jp mod nw) - alpha jp') * sin(alpha(Suc jp' mod nw) - alpha jp) \<le> 0" .
            with hsb_sc show False by linarith
          qed
          from mult_pos_neg[OF \<open>tp > 0\<close> this]
          have "tp * sin(alpha(Suc jp mod nw) - alpha jp') < 0" .
          hence "sp * sin(alpha jp - alpha jp') + tp * sin(alpha(Suc jp mod nw) - alpha jp') < 0"
            using \<open>sp = 0\<close> by (by100 simp)
          with hcone1_sin show False by linarith
        qed
      next
        case hsd_pos: False
        hence "sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) > 0" by linarith
        \<comment> \<open>sd > 0, sc < 0. Same Cramer argument as jp < jp' case.\<close>
        \<comment> \<open>Cramer: sd*hcone2 + (-sc)*hcone1 = tp*(-det) \\<ge> 0. But -sc > 0.
           Wait: sd*(sp*sc+tp*sd) + (-sc)*(sp*sa+tp*sb) = tp*(sc*sb - sa*sd) + sp*(sd*sc - sc*sa)
           = ... let me just use the same pattern.
           Actually: sd*hcone2 + (-sc)*hcone1 = sp*(sd*sc - sc*sa) + tp*(sd^2 - sc*sb)... too complex.
           Use define with abbreviations.\<close>
        have "tp = 0"
        proof -
          define sa' where "sa' = sin(alpha jp - alpha jp')"
          define sb' where "sb' = sin(alpha(Suc jp mod nw) - alpha jp')"
          define sc' where "sc' = sin(alpha(Suc jp' mod nw) - alpha jp)"
          define sd' where "sd' = sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw))"
          have hsc'': "sc' < 0" using hsc' unfolding sc'_def by linarith
          have hsd'': "sd' > 0" using \<open>sin(alpha(Suc jp' mod nw) - alpha(Suc jp mod nw)) > 0\<close>
            unfolding sd'_def by linarith
          have hh1: "sp * sa' + tp * sb' \<ge> 0" using hcone1_sin unfolding sa'_def sb'_def by (by100 simp)
          have hh2: "sp * sc' + tp * sd' \<ge> 0" using hcone2_sin unfolding sc'_def sd'_def by (by100 simp)
          have hdet': "sa' * sd' - sb' * sc' < 0" using hdet_neg
            unfolding sa'_def sb'_def sc'_def sd'_def by linarith
          \<comment> \<open>Key: sa' \\<ge> 0 (gap \\<in> (0, pi], sin \\<ge> 0). Use Cramer: (-sc')*hh1 + sa'*hh2 = tp*(-det') \\<ge> 0.
             Both (-sc') > 0 and sa' \\<ge> 0. hh1, hh2 \\<ge> 0. Sum \\<ge> 0.
             And = tp*(-det') \\<ge> 0. tp \\<ge> 0, -det' > 0 \\<to> tp*(-det') \\<ge> 0 always.
             But also: (-sc')*hh1 + sa'*hh2 = tp*(-det'). Both sides \\<ge> 0.
             From the Cramer: sa'*hh2 - sc'*hh1 = tp*det'. And det' < 0 \\<to> tp*det' \\<le> 0.
             So sa'*hh2 - sc'*hh1 \\<le> 0. With (-sc')*hh1 \\<ge> 0 and sa'*hh2 \\<ge> 0 (sa' \\<ge> 0):
             sa'*hh2 \\<le> sc'*hh1 ... sc' < 0 \\<to> sc'*hh1 \\<le> 0. So sa'*hh2 \\<le> 0.
             If sa' > 0: hh2 \\<le> 0 AND hh2 \\<ge> 0 \\<to> hh2 = 0 \\<to> sp*sc'+tp*sd' = 0 \\<to> sp=0 and tp=0. Contradiction!
             If sa' = 0: from det: -sb'*sc' < 0, sc' < 0 \\<to> sb' < 0. hh1 = sp*0+tp*sb' = tp*sb' \\<ge> 0. tp*sb' \\<ge> 0 with sb' < 0 \\<to> tp \\<le> 0 \\<to> tp = 0.
             sp + tp = 0. Contradiction!\<close>
          have hsa_ge: "sa' \<ge> 0"
          proof -
            have "alpha jp - alpha jp' > 0" using halpha_mono[of jp' jp] hjp_gt hjp by linarith
            moreover have "alpha jp - alpha jp' \<le> pi" using hc1 by linarith
            ultimately have "sin(alpha jp - alpha jp') \<ge> 0"
              using sin_ge_zero[of "alpha jp - alpha jp'"] by linarith
            thus ?thesis unfolding sa'_def by linarith
          qed
          \<comment> \<open>Cramer identity: sa'*hh2 - sc'*hh1 = tp*det'.\<close>
          have hcramer: "sa' * (sp * sc' + tp * sd') - sc' * (sp * sa' + tp * sb') = tp * (sa' * sd' - sb' * sc')"
            by (by100 algebra)
          hence "tp * (sa' * sd' - sb' * sc') = sa' * (sp * sc' + tp * sd') + (-sc') * (sp * sa' + tp * sb')"
            by linarith
          hence htp_det: "tp * (sa' * sd' - sb' * sc') \<le> 0"
          proof -
            assume h: "tp * (sa' * sd' - sb' * sc') = sa' * (sp * sc' + tp * sd') + (-sc') * (sp * sa' + tp * sb')"
            have "sa' * (sp * sc' + tp * sd') \<ge> 0"
              using mult_nonneg_nonneg[OF hsa_ge hh2] .
            moreover have "(-sc') > 0" using hsc'' by linarith
            have "(-sc') \<ge> 0" using hsc'' by linarith
            from mult_nonneg_nonneg[OF this hh1]
            have "(-sc') * (sp * sa' + tp * sb') \<ge> 0" .
            ultimately have "sa' * (sp * sc' + tp * sd') + (-sc') * (sp * sa' + tp * sb') \<ge> 0" by linarith
            have "sa' * sd' - sb' * sc' \<le> 0" using hdet' by linarith
            from mult_nonneg_nonpos[OF htp this]
            show ?thesis .
          qed
          \<comment> \<open>tp \\<ge> 0 and det' < 0: tp * det' \\<le> 0 always. But we also derived it \\<ge> 0 from Cramer.
             Wait: we derived the RHS \\<ge> 0 AND = tp*det'. So tp*det' \\<ge> 0.
             With det' < 0: tp \\<le> 0. With tp \\<ge> 0: tp = 0.\<close>
          show ?thesis
          proof -
            from htp_det have "tp * (sa' * sd' - sb' * sc') \<le> 0" .
            moreover from hcramer hsa_ge hh2 hsc'' hh1
            have "sa' * (sp * sc' + tp * sd') + (-sc') * (sp * sa' + tp * sb') \<ge> 0"
              using mult_nonneg_nonneg[OF hsa_ge hh2]
                    mult_nonneg_nonneg[of "-sc'" "sp * sa' + tp * sb'"] hsc'' hh1 by linarith
            ultimately have "tp * (sa' * sd' - sb' * sc') \<ge> 0" using hcramer by linarith
            with htp_det have "tp * (sa' * sd' - sb' * sc') = 0" by linarith
            with hdet' show "tp = 0" by (by100 simp)
          qed
        qed
        \<comment> \<open>tp = 0. From hcone1: sp*sa \\<ge> 0. sa could be < 0 or \\<ge> 0.\<close>
        hence "sp > 0" using hst by linarith
        from hcone2_sin \<open>tp = 0\<close> have "sp * sin(alpha(Suc jp' mod nw) - alpha jp) \<ge> 0" by (by100 simp)
        from mult_pos_neg[OF \<open>sp > 0\<close> hsc']
        have "sp * sin(alpha(Suc jp' mod nw) - alpha jp) < 0" .
        with \<open>sp * sin(alpha(Suc jp' mod nw) - alpha jp) \<ge> 0\<close> show False by linarith
      qed
    next
      case hc2: False
      hence hbig': "alpha jp - alpha jp' > pi" by linarith
      \<comment> \<open>Big gap. sa < 0 (in (pi, 2pi)). sb < 0 (in (pi, 2pi) for non-wrapping, or (0, pi) negated for wrapping).
         hcone1 = sp*sa + tp*sb < 0.\<close>
      have hsa_neg: "sin(alpha jp - alpha jp') < 0"
      proof -
        have "alpha jp < 2*pi" using halpha_mono[of jp nw] hjp halpha_nw by linarith
        have "alpha jp' \<ge> 0"
        proof (cases "jp' = 0")
          case True with halpha_0 show ?thesis by (by100 simp)
        next
          case False from halpha_mono[of 0 jp'] False hjp' show ?thesis using halpha_0 by linarith
        qed
        hence "alpha jp - alpha jp' < 2*pi" using \<open>alpha jp < 2*pi\<close> by linarith
        with hbig' show ?thesis using sin_lt_zero[of "alpha jp - alpha jp'"] by linarith
      qed
      have hsb_neg: "sin(alpha(Suc jp mod nw) - alpha jp') < 0"
      proof (cases "jp < nw - 1")
        case True
        hence hSjp_eq: "Suc jp mod nw = Suc jp" using hnw by (by100 auto)
        \<comment> \<open>alpha(Suc jp) - alpha jp' > pi (big gap + theta > 0) and < 2pi.\<close>
        have "alpha(Suc jp) - alpha jp' > pi"
        proof -
          have "alpha(Suc jp) > alpha jp" using halpha_strict[rule_format, OF hjp] by linarith
          with hbig' show ?thesis by linarith
        qed
        moreover have "alpha(Suc jp) - alpha jp' < 2*pi"
        proof -
          have "alpha(Suc jp) < alpha nw" using halpha_mono[of "Suc jp" nw] True hnw by linarith
          have "alpha jp' \<ge> 0"
          proof (cases "jp' = 0")
            case True with halpha_0 show ?thesis by (by100 simp)
          next
            case False from halpha_mono[of 0 jp'] False hjp' show ?thesis using halpha_0 by linarith
          qed
          with \<open>alpha(Suc jp) < alpha nw\<close> halpha_nw show ?thesis by linarith
        qed
        ultimately show ?thesis using hSjp_eq sin_lt_zero[of "alpha(Suc jp) - alpha jp'"] by (by100 simp)
      next
        case False
        hence "jp = nw - 1" using hjp by linarith
        hence "Suc jp mod nw = 0" using hnw by (by100 auto)
        hence hval: "alpha(Suc jp mod nw) = 0" using halpha_0 by (by100 simp)
        \<comment> \<open>sb = sin(-alpha jp'). alpha jp' < pi (from big gap: alpha jp' < alpha jp - pi < 2pi - pi = pi).\<close>
        have "alpha jp' < pi"
        proof -
          have "alpha jp < 2*pi" using halpha_mono[of jp nw] hjp halpha_nw by linarith
          with hbig' show ?thesis by linarith
        qed
        moreover have "alpha jp' > 0"
        proof -
          have "jp' \<noteq> 0" using hne_adj1 \<open>Suc jp mod nw = 0\<close> by linarith
          from halpha_mono[of 0 jp'] this hjp' show ?thesis using halpha_0 by linarith
        qed
        ultimately have "sin(alpha jp') > 0" using sin_gt_zero[of "alpha jp'"] by linarith
        hence "sin(-alpha jp') < 0" using sin_minus[of "alpha jp'"] by linarith
        with hval show ?thesis by (by100 simp)
      qed
      \<comment> \<open>sa < 0 and sb < 0 \\<to> hcone1 < 0.\<close>
      have hsa_le: "sin(alpha jp - alpha jp') \<le> 0" using hsa_neg by linarith
      have hsb_le: "sin(alpha(Suc jp mod nw) - alpha jp') \<le> 0" using hsb_neg by linarith
      have "sp * sin(alpha jp - alpha jp') + tp * sin(alpha(Suc jp mod nw) - alpha jp') < 0"
      proof (cases "sp > 0")
        case True from mult_pos_neg[OF True hsa_neg]
        have "sp * sin(alpha jp - alpha jp') < 0" .
        moreover have "tp * sin(alpha(Suc jp mod nw) - alpha jp') \<le> 0"
          using mult_nonneg_nonpos[OF htp hsb_le] .
        ultimately show ?thesis by linarith
      next
        case False hence "sp = 0" using hsp by linarith
        hence "tp > 0" using hst by linarith
        from mult_pos_neg[OF this hsb_neg]
        have "tp * sin(alpha(Suc jp mod nw) - alpha jp') < 0" .
        with \<open>sp = 0\<close> show ?thesis by (by100 simp)
      qed
      with hcone1_sin show False by linarith
    qed
  qed
qed

\<comment> \<open>Adjacent centroid-cone injectivity. If phi(p)=phi(p') with p in sector jp, p' in sector jp+1,
   sp\\_v = 0 (from cross product = 0), centroid at origin, C10: then p = p'.
   The argument: 2D linear independence gives tp\\_v'=0 and sp\\_v'=tp\\_v.
   Then Cramer with sp=0 (for p) and tp'=0 (for p') give the same source diagonal parameter.\<close>
lemma adjacent_cone_diagonal_injective:
  fixes det_s sp_v tp_v sp_v' tp_v' :: real
    and vxw vyw :: "nat \<Rightarrow> real"
    and ex_s ey_s fx_s fy_s :: real
    and ex_s' ey_s' fx_s' fy_s' :: real
  assumes hsp0: "sp_v = 0" and htp_ge: "tp_v \<ge> 0"
      and hdet_pos: "ex_s*fy_s - ey_s*fx_s > 0"
      and htp_v_det: "tp_v*(ex_s*fy_s-ey_s*fx_s) = ex_s*dy - ey_s*dx"
      and hsp_zero: "fy_s*dx - fx_s*dy = 0"
      \<comment> \<open>phi(p) = tp\\_v * u\\_{jp+1} = sp\\_v' * u\\_{jp+1} + tp\\_v' * u\\_{jp+2} (centroid=0).\<close>
      and hphi_x: "tp_v * ux1 = sp_v' * ux1 + tp_v' * ux2"
      and hphi_y: "tp_v * uy1 = sp_v' * uy1 + tp_v' * uy2"
      and hC10_ne: "ux1*uy2 - uy1*ux2 \<noteq> 0"
      \<comment> \<open>p' Cramer: ex\\_s' = fx\\_s, ey\\_s' = fy\\_s (shared diagonal direction).\<close>
      and hex': "ex_s' = fx_s" and hey': "ey_s' = fy_s"
      and hdet'_pos: "ex_s'*fy_s' - ey_s'*fx_s' > 0"
      and hsp_v'_det: "sp_v'*(ex_s'*fy_s'-ey_s'*fx_s') = fy_s'*dx' - fx_s'*dy'"
      and htp_v'_det: "tp_v'*(ex_s'*fy_s'-ey_s'*fx_s') = ex_s'*dy' - ey_s'*dx'"
  shows "dx = dx' \<and> dy = dy'"
proof -
  \<comment> \<open>Step 1: tp\\_v' = 0 and sp\\_v' = tp\\_v from 2D linear independence.\<close>
  have "tp_v' * (ux1*uy2 - uy1*ux2) = 0"
    using hphi_x hphi_y by (by100 algebra)
  hence "tp_v' = 0" using hC10_ne by (by100 simp)
  from hphi_x \<open>tp_v' = 0\<close> have "(tp_v - sp_v') * ux1 = 0" by (by100 algebra)
  from hphi_y \<open>tp_v' = 0\<close> have "(tp_v - sp_v') * uy1 = 0" by (by100 algebra)
  have "ux1 \<noteq> 0 \<or> uy1 \<noteq> 0" using hC10_ne by (by100 auto)
  with \<open>(tp_v-sp_v')*ux1=0\<close> \<open>(tp_v-sp_v')*uy1=0\<close>
  have "sp_v' = tp_v" by (by100 auto)
  \<comment> \<open>Step 2: From sp\\_v=0 and Cramer: dx = tp\\_v*fx\\_s, dy = tp\\_v*fy\\_s.\<close>
  have "ex_s*(fy_s*dx-fx_s*dy) + fx_s*(ex_s*dy-ey_s*dx) = (ex_s*fy_s-ey_s*fx_s)*dx"
    by (by100 algebra)
  hence "(ex_s*fy_s-ey_s*fx_s)*dx = ex_s*0 + fx_s*(tp_v*(ex_s*fy_s-ey_s*fx_s))"
    using hsp_zero htp_v_det by (by100 simp)
  hence "(ex_s*fy_s-ey_s*fx_s)*dx = tp_v*fx_s*(ex_s*fy_s-ey_s*fx_s)" by (by100 algebra)
  hence hdx: "dx = tp_v*fx_s" using hdet_pos by (by100 simp)
  have "ey_s*(fy_s*dx-fx_s*dy) + fy_s*(ex_s*dy-ey_s*dx) = (ex_s*fy_s-ey_s*fx_s)*dy"
    by (by100 algebra)
  hence "(ex_s*fy_s-ey_s*fx_s)*dy = ey_s*0 + fy_s*(tp_v*(ex_s*fy_s-ey_s*fx_s))"
    using hsp_zero htp_v_det by (by100 simp)
  hence "(ex_s*fy_s-ey_s*fx_s)*dy = tp_v*fy_s*(ex_s*fy_s-ey_s*fx_s)" by (by100 algebra)
  hence hdy: "dy = tp_v*fy_s" using hdet_pos by (by100 simp)
  \<comment> \<open>Step 3: From tp\\_v'=0 and Cramer for p': dx' = sp\\_v'*ex\\_s' = sp\\_v'*fx\\_s = tp\\_v*fx\\_s.\<close>
  have htp_zero_eq: "ex_s'*dy' - ey_s'*dx' = 0"
    using htp_v'_det \<open>tp_v' = 0\<close> hdet'_pos by (by100 simp)
  hence htp_zero_eq': "fx_s*dy' - fy_s*dx' = 0"
    using hex' hey' by (by100 simp)
  have "fx_s*(fy_s'*dx'-fx_s'*dy') + fx_s'*(fx_s*dy'-fy_s*dx') = (fx_s*fy_s'-fy_s*fx_s')*dx'"
    by (by100 algebra)
  hence "(fx_s*fy_s'-fy_s*fx_s')*dx' = fx_s*(sp_v'*(ex_s'*fy_s'-ey_s'*fx_s')) + fx_s'*0"
    using hsp_v'_det htp_zero_eq' by (by100 simp)
  hence "(ex_s'*fy_s'-ey_s'*fx_s')*dx' = sp_v'*(ex_s'*fy_s'-ey_s'*fx_s')*fx_s"
    using hex' hey' by (by100 algebra)
  hence "dx' = sp_v'*fx_s" using hdet'_pos hex' hey' by (by100 simp)
  hence "dx' = tp_v*fx_s" using \<open>sp_v' = tp_v\<close> by (by100 simp)
  with hdx have "dx = dx'" by (by100 simp)
  \<comment> \<open>Similarly for dy.\<close>
  have "fy_s*(fy_s'*dx'-fx_s'*dy') + fy_s'*(fx_s*dy'-fy_s*dx') = (fx_s*fy_s'-fy_s*fx_s')*dy'"
    by (by100 algebra)
  hence "(fx_s*fy_s'-fy_s*fx_s')*dy' = fy_s*(sp_v'*(ex_s'*fy_s'-ey_s'*fx_s')) + fy_s'*0"
    using hsp_v'_det htp_zero_eq' by (by100 simp)
  hence "(ex_s'*fy_s'-ey_s'*fx_s')*dy' = sp_v'*(ex_s'*fy_s'-ey_s'*fx_s')*fy_s"
    using hex' hey' by (by100 algebra)
  hence "dy' = sp_v'*fy_s" using hdet'_pos hex' hey' by (by100 simp)
  hence "dy' = tp_v*fy_s" using \<open>sp_v' = tp_v\<close> by (by100 simp)
  with hdy have "dy = dy'" by (by100 simp)
  with \<open>dx = dx'\<close> show ?thesis by (by100 simp)
qed

\<comment> \<open>Symmetric version for tp = 0 (p on LEFT boundary).\<close>
lemma adjacent_cone_diagonal_injective_tp:
  fixes det_s sp_v tp_v sp_v' tp_v' :: real
    and ex_s ey_s fx_s fy_s :: real
    and fx_s' fy_s' ex_s' ey_s' :: real
  assumes htp0: "tp_v = 0" and hsp_ge: "sp_v \<ge> 0"
      and hdet_pos: "ex_s*fy_s - ey_s*fx_s > 0"
      and hsp_v_det: "sp_v*(ex_s*fy_s-ey_s*fx_s) = fy_s*dx - fx_s*dy"
      and htp_zero: "ex_s*dy - ey_s*dx = 0"
      \<comment> \<open>phi matching: sp\\_v*u\\_jp = tp\\_v'*u\\_jp + sp\\_v'*u\\_{jp-1} (centroid=0).\<close>
      and hphi_x: "sp_v * ux1 = tp_v' * ux1 + sp_v' * ux0"
      and hphi_y: "sp_v * uy1 = tp_v' * uy1 + sp_v' * uy0"
      and hC10_ne: "ux0*uy1 - uy0*ux1 \<noteq> 0"
      \<comment> \<open>p' Cramer: fx\\_s' = ex\\_s, fy\\_s' = ey\\_s (shared diagonal direction).\<close>
      and hfx': "fx_s' = ex_s" and hfy': "fy_s' = ey_s"
      and hdet'_pos: "ex_s'*fy_s' - ey_s'*fx_s' > 0"
      and hsp_v'_det: "sp_v'*(ex_s'*fy_s'-ey_s'*fx_s') = fy_s'*dx' - fx_s'*dy'"
      and htp_v'_det: "tp_v'*(ex_s'*fy_s'-ey_s'*fx_s') = ex_s'*dy' - ey_s'*dx'"
  shows "dx = dx' \<and> dy = dy'"
proof -
  \<comment> \<open>Step 1: sp\\_v' = 0 and tp\\_v' = sp\\_v from 2D linear independence.\<close>
  have "sp_v' * (ux0*uy1 - uy0*ux1) = 0"
    using hphi_x hphi_y by (by100 algebra)
  hence "sp_v' = 0" using hC10_ne by (by100 simp)
  from hphi_x \<open>sp_v' = 0\<close> have "(sp_v - tp_v') * ux1 = 0" by (by100 algebra)
  from hphi_y \<open>sp_v' = 0\<close> have "(sp_v - tp_v') * uy1 = 0" by (by100 algebra)
  have "ux1 \<noteq> 0 \<or> uy1 \<noteq> 0" using hC10_ne by (by100 auto)
  with \<open>(sp_v-tp_v')*ux1=0\<close> \<open>(sp_v-tp_v')*uy1=0\<close>
  have "tp_v' = sp_v" by (by100 auto)
  \<comment> \<open>Step 2: From tp\\_v=0 and Cramer: dx = sp\\_v*ex\\_s, dy = sp\\_v*ey\\_s.\<close>
  have "ex_s*(fy_s*dx-fx_s*dy) + fx_s*(ex_s*dy-ey_s*dx) = (ex_s*fy_s-ey_s*fx_s)*dx"
    by (by100 algebra)
  hence "(ex_s*fy_s-ey_s*fx_s)*dx = ex_s*(sp_v*(ex_s*fy_s-ey_s*fx_s)) + fx_s*0"
    using hsp_v_det htp_zero by (by100 simp)
  hence "(ex_s*fy_s-ey_s*fx_s)*dx = sp_v*ex_s*(ex_s*fy_s-ey_s*fx_s)" by (by100 algebra)
  hence hdx: "dx = sp_v*ex_s" using hdet_pos by (by100 simp)
  have "ey_s*(fy_s*dx-fx_s*dy) + fy_s*(ex_s*dy-ey_s*dx) = (ex_s*fy_s-ey_s*fx_s)*dy"
    by (by100 algebra)
  hence "(ex_s*fy_s-ey_s*fx_s)*dy = ey_s*(sp_v*(ex_s*fy_s-ey_s*fx_s)) + fy_s*0"
    using hsp_v_det htp_zero by (by100 simp)
  hence "(ex_s*fy_s-ey_s*fx_s)*dy = sp_v*ey_s*(ex_s*fy_s-ey_s*fx_s)" by (by100 algebra)
  hence hdy: "dy = sp_v*ey_s" using hdet_pos by (by100 simp)
  \<comment> \<open>Step 3: From sp\\_v'=0 and Cramer for p': dx' = tp\\_v'*fx\\_s' = sp\\_v*ex\\_s.\<close>
  have hsp_zero_eq': "fy_s'*dx' - fx_s'*dy' = 0"
    using hsp_v'_det \<open>sp_v' = 0\<close> hdet'_pos by (by100 simp)
  hence "fy_s'*dx' = fx_s'*dy'" by linarith
  hence hex_eq: "ey_s*dx' = ex_s*dy'"
    using hfx' hfy' by (by100 simp)
  have "(ex_s'*fy_s'-ey_s'*fx_s')*dx' = ex_s'*(fy_s'*dx'-fx_s'*dy') + fx_s'*(ex_s'*dy'-ey_s'*dx')"
    by (by100 algebra)
  hence "(ex_s'*fy_s'-ey_s'*fx_s')*dx' = ex_s'*0 + fx_s'*(tp_v'*(ex_s'*fy_s'-ey_s'*fx_s'))"
    using hsp_zero_eq' htp_v'_det by (by100 simp)
  hence "dx' = tp_v'*fx_s'" using hdet'_pos by (by100 simp)
  hence "dx' = sp_v*ex_s" using \<open>tp_v' = sp_v\<close> hfx' by (by100 simp)
  with hdx have "dx = dx'" by (by100 simp)
  have "(ex_s'*fy_s'-ey_s'*fx_s')*dy' = ey_s'*(fy_s'*dx'-fx_s'*dy') + fy_s'*(ex_s'*dy'-ey_s'*dx')"
    by (by100 algebra)
  hence "(ex_s'*fy_s'-ey_s'*fx_s')*dy' = ey_s'*0 + fy_s'*(tp_v'*(ex_s'*fy_s'-ey_s'*fx_s'))"
    using hsp_zero_eq' htp_v'_det by (by100 simp)
  hence "dy' = tp_v'*fy_s'" using hdet'_pos by (by100 simp)
  hence "dy' = sp_v*ey_s" using \<open>tp_v' = sp_v\<close> hfy' by (by100 simp)
  with hdy have "dy = dy'" by (by100 simp)
  with \<open>dx = dx'\<close> show ?thesis by (by100 simp)
qed

\<comment> \<open>Standalone lemma: a point with positive centroid weight is not on any polygon edge.
   If q = \\<alpha>*cw + \\<beta>*u\\_j + \\<gamma>*u\\_{j+1} with \\<alpha> > 0 and
   the centroid satisfies C10 (strictly interior to each edge),
   then q is NOT equal to any edge point.\<close>
lemma centroid_weight_not_on_edge:
  fixes nw :: nat and vxw vyw :: "nat \<Rightarrow> real"
  assumes hnw: "nw \<ge> 3"
      and hC10: "\<forall>i<nw. (vxw i - cxw) * (vyw(Suc i mod nw) - cyw) -
          (vyw i - cyw) * (vxw(Suc i mod nw) - cxw) > 0"
      and hC11: "\<forall>i<nw. \<forall>k<nw. k\<noteq>i \<longrightarrow> k\<noteq>Suc i mod nw \<longrightarrow>
          (vxw k-vxw i)*(vyw(Suc i mod nw)-vyw i)-(vyw k-vyw i)*(vxw(Suc i mod nw)-vxw i) < 0"
      and hj_lt: "j_sec < nw"
      and halpha: "\<alpha> > 0" and hbeta: "\<beta> \<ge> 0" and hgamma: "\<gamma> \<ge> 0"
      and habg: "\<alpha> + \<beta> + \<gamma> = 1"
      and hqx: "fst q = \<alpha>*cxw + \<beta>*vxw j_sec + \<gamma>*vxw(Suc j_sec mod nw)"
      and hqy: "snd q = \<alpha>*cyw + \<beta>*vyw j_sec + \<gamma>*vyw(Suc j_sec mod nw)"
      and hk_lt: "k_edge < nw"
      and hsx: "fst (edge_q :: real \<times> real) = (1-t_e)*vxw k_edge + t_e*vxw(Suc k_edge mod nw)"
      and hsy: "snd edge_q = (1-t_e)*vyw k_edge + t_e*vyw(Suc k_edge mod nw)"
  shows "q \<noteq> edge_q"
proof
  assume heq: "q = edge_q"
  \<comment> \<open>Edge cross product at edge k: det(u\\_{k+1}-u\\_k, q-u\\_k).
     For edge\\_q: this is 0 (edge\\_q lies on edge k).
     For q = \\<alpha>*cw + \\<beta>*u\\_j + \\<gamma>*u\\_{j+1}:
       = \\<alpha>*det(u\\_{k+1}-u\\_k, cw-u\\_k) + \\<beta>*det(u\\_{k+1}-u\\_k, u\\_j-u\\_k) + \\<gamma>*det(u\\_{k+1}-u\\_k, u\\_{j+1}-u\\_k)
     The \\<alpha> term is > 0 (from C10) and the \\<beta>,\\<gamma> terms are \\<ge> 0 (from C10/C11).
     So the total > 0. But edge\\_q has cross = 0. Contradiction.\<close>
  let ?dx_k = "vxw(Suc k_edge mod nw)-vxw k_edge"
  let ?dy_k = "vyw(Suc k_edge mod nw)-vyw k_edge"
  \<comment> \<open>Edge cross at edge\\_q = 0.\<close>
  have hedge_zero: "?dx_k*(snd edge_q-vyw k_edge)-?dy_k*(fst edge_q-vxw k_edge) = 0"
  proof -
    have "snd edge_q - vyw k_edge = t_e*?dy_k" using hsy by (by100 algebra)
    moreover have "fst edge_q - vxw k_edge = t_e*?dx_k" using hsx by (by100 algebra)
    ultimately show ?thesis by (by100 algebra)
  qed
  \<comment> \<open>Edge cross at q > 0 (from centroid weight).\<close>
  have "snd q - vyw k_edge = \<alpha>*(cyw-vyw k_edge) + \<beta>*(vyw j_sec-vyw k_edge) + \<gamma>*(vyw(Suc j_sec mod nw)-vyw k_edge)"
    using hqy habg by (by100 algebra)
  moreover have "fst q - vxw k_edge = \<alpha>*(cxw-vxw k_edge) + \<beta>*(vxw j_sec-vxw k_edge) + \<gamma>*(vxw(Suc j_sec mod nw)-vxw k_edge)"
    using hqx habg by (by100 algebra)
  ultimately have hcross_expand: "?dx_k*(snd q-vyw k_edge)-?dy_k*(fst q-vxw k_edge) =
      \<alpha>*(?dx_k*(cyw-vyw k_edge)-?dy_k*(cxw-vxw k_edge)) +
      \<beta>*(?dx_k*(vyw j_sec-vyw k_edge)-?dy_k*(vxw j_sec-vxw k_edge)) +
      \<gamma>*(?dx_k*(vyw(Suc j_sec mod nw)-vyw k_edge)-?dy_k*(vxw(Suc j_sec mod nw)-vxw k_edge))"
  proof -
    assume hsndq: "snd q - vyw k_edge = \<alpha>*(cyw-vyw k_edge) + \<beta>*(vyw j_sec-vyw k_edge) + \<gamma>*(vyw(Suc j_sec mod nw)-vyw k_edge)"
    assume hfstq: "fst q - vxw k_edge = \<alpha>*(cxw-vxw k_edge) + \<beta>*(vxw j_sec-vxw k_edge) + \<gamma>*(vxw(Suc j_sec mod nw)-vxw k_edge)"
    \<comment> \<open>Substitute and distribute.\<close>
    define sy where "sy = snd q - vyw k_edge"
    define sx where "sx = fst q - vxw k_edge"
    define ca where "ca = cyw-vyw k_edge"
    define cb where "cb = cxw-vxw k_edge"
    define ja where "ja = vyw j_sec-vyw k_edge"
    define jb where "jb = vxw j_sec-vxw k_edge"
    define sa where "sa = vyw(Suc j_sec mod nw)-vyw k_edge"
    define sb where "sb = vxw(Suc j_sec mod nw)-vxw k_edge"
    from hsndq have hsy: "sy = \<alpha>*ca + \<beta>*ja + \<gamma>*sa" unfolding sy_def ca_def ja_def sa_def .
    from hfstq have hsx: "sx = \<alpha>*cb + \<beta>*jb + \<gamma>*sb" unfolding sx_def cb_def jb_def sb_def .
    have "?dx_k*sy - ?dy_k*sx = ?dx_k*(\<alpha>*ca + \<beta>*ja + \<gamma>*sa) - ?dy_k*(\<alpha>*cb + \<beta>*jb + \<gamma>*sb)"
      using hsy hsx by simp
    also have "\<dots> = \<alpha>*(?dx_k*ca - ?dy_k*cb) + \<beta>*(?dx_k*ja - ?dy_k*jb) + \<gamma>*(?dx_k*sa - ?dy_k*sb)"
      by (by100 algebra)
    finally show ?thesis
      unfolding sy_def sx_def ca_def cb_def ja_def jb_def sa_def sb_def .
  qed
  \<comment> \<open>C10 term: det(u\\_{k+1}-u\\_k, cw-u\\_k) > 0.\<close>
  have hcw_term: "?dx_k*(cyw-vyw k_edge)-?dy_k*(cxw-vxw k_edge) > 0"
  proof -
    \<comment> \<open>From C10 at edge k: det(u\\_k-cw, u\\_{k+1}-cw) > 0.
       This equals det(u\\_{k+1}-u\\_k, cw-u\\_k) by the algebraic identity.\<close>
    from hC10[rule_format, OF hk_lt]
    have "(vxw k_edge - cxw) * (vyw(Suc k_edge mod nw) - cyw) -
        (vyw k_edge - cyw) * (vxw(Suc k_edge mod nw) - cxw) > 0" .
    \<comment> \<open>det(u\\_k-cw, u\\_{k+1}-cw) = det(u\\_{k+1}-u\\_k, cw-u\\_k) (algebraic identity).\<close>
    \<comment> \<open>det(A-C, B-C) = det(B-A, C-A) where A=u\\_k, B=u\\_{k+1}, C=cw.\<close>
    hence hC10_inst: "(vxw k_edge - cxw) * (vyw(Suc k_edge mod nw) - cyw) -
        (vyw k_edge - cyw) * (vxw(Suc k_edge mod nw) - cxw) > 0" .
    define ax where "ax = vxw k_edge"
    define ay where "ay = vyw k_edge"
    define bx where "bx = vxw(Suc k_edge mod nw)"
    define by' where "by' = vyw(Suc k_edge mod nw)"
    define cx' where "cx' = cxw"
    define cy' where "cy' = cyw"
    have "(bx-ax)*(cy'-ay)-(by'-ay)*(cx'-ax) = (ax-cx')*(by'-cy')-(ay-cy')*(bx-cx')"
      by (by100 algebra)
    thus ?thesis using hC10_inst
      unfolding ax_def ay_def bx_def by'_def cx'_def cy'_def by linarith
  qed
  \<comment> \<open>\\<beta>, \\<gamma> terms are \\<ge> 0.\<close>
  \<comment> \<open>For any vertex m: det(u\\_{k+1}-u\\_k, u\\_m-u\\_k) \\<ge> 0.
     = 0 when m = k or m = Suc k mod nw.
     > 0 when m \\<noteq> k and m \\<noteq> Suc k mod nw (from C11 + sign reversal).\<close>
  have hvertex_cross_ge: "\<forall>m<nw. ?dx_k*(vyw m-vyw k_edge)-?dy_k*(vxw m-vxw k_edge) \<ge> 0"
  proof (intro allI impI)
    fix m assume hm: "m < nw"
    show "?dx_k*(vyw m-vyw k_edge)-?dy_k*(vxw m-vxw k_edge) \<ge> 0"
    proof (cases "m = k_edge \<or> m = Suc k_edge mod nw")
      case True thus ?thesis by (elim disjE) simp_all
    next
      case False hence "m \<noteq> k_edge" "m \<noteq> Suc k_edge mod nw" by auto
      \<comment> \<open>From C10 at edge k, applied to vertex m: det(u\\_k-cw, u\\_{k+1}-cw) > 0
         gives det(u\\_{k+1}-u\\_k, u\\_m-u\\_k) > 0 by C10+C11 argument.
         Actually use the C10 identity directly: det(u\\_{k+1}-u\\_k, u\\_m-u\\_k) = -det(u\\_m-u\\_k, u\\_{k+1}-u\\_k).
         C11 gives det(u\\_m-u\\_k, u\\_{k+1}-u\\_k) < 0, hence our term > 0.\<close>
      from hC11[rule_format, OF hk_lt hm \<open>m \<noteq> k_edge\<close> \<open>m \<noteq> Suc k_edge mod nw\<close>]
      have "(vxw m-vxw k_edge)*(vyw(Suc k_edge mod nw)-vyw k_edge)-
          (vyw m-vyw k_edge)*(vxw(Suc k_edge mod nw)-vxw k_edge) < 0" .
      \<comment> \<open>Negate: det(B-A, M-A) = -det(M-A, B-A).\<close>
      define ax where "ax = vxw k_edge"
      define ay where "ay = vyw k_edge"
      define bx where "bx = vxw(Suc k_edge mod nw)"
      define by' where "by' = vyw(Suc k_edge mod nw)"
      define mx where "mx = vxw m"
      define my' where "my' = vyw m"
      have "(bx-ax)*(my'-ay)-(by'-ay)*(mx-ax) = -((mx-ax)*(by'-ay)-(my'-ay)*(bx-ax))"
        by (by100 algebra)
      thus ?thesis using \<open>(vxw m-vxw k_edge)*(vyw(Suc k_edge mod nw)-vyw k_edge)-
          (vyw m-vyw k_edge)*(vxw(Suc k_edge mod nw)-vxw k_edge) < 0\<close>
        unfolding ax_def ay_def bx_def by'_def mx_def my'_def by linarith
    qed
  qed
  have hbeta_term: "\<beta>*(?dx_k*(vyw j_sec-vyw k_edge)-?dy_k*(vxw j_sec-vxw k_edge)) \<ge> 0"
    using hbeta hvertex_cross_ge[rule_format, OF hj_lt] by (intro mult_nonneg_nonneg)
  have hgamma_term: "\<gamma>*(?dx_k*(vyw(Suc j_sec mod nw)-vyw k_edge)-?dy_k*(vxw(Suc j_sec mod nw)-vxw k_edge)) \<ge> 0"
  proof -
    have "Suc j_sec mod nw < nw" using hnw by simp
    from hvertex_cross_ge[rule_format, OF this]
    show ?thesis using hgamma by (intro mult_nonneg_nonneg)
  qed
  \<comment> \<open>Total edge cross > 0.\<close>
  have halpha_cw: "\<alpha>*(?dx_k*(cyw-vyw k_edge)-?dy_k*(cxw-vxw k_edge)) > 0"
    using halpha hcw_term by (by100 simp)
  have "?dx_k*(snd q-vyw k_edge)-?dy_k*(fst q-vxw k_edge) > 0"
    using hcross_expand halpha_cw hbeta_term hgamma_term by linarith
  \<comment> \<open>But edge cross at edge\\_q = 0.\<close>
  hence "?dx_k*(snd edge_q-vyw k_edge)-?dy_k*(fst edge_q-vxw k_edge) > 0"
    using heq by simp
  with hedge_zero show False by linarith
qed

lemma spur_collapse_cancel_homeo:
  fixes w :: "(nat \<times> bool) list" and a :: "nat \<times> bool"
  assumes hlen: "length w \<ge> 3"
      and hproper: "\<forall>label. card {i. i < length w \<and> fst (w ! i) = label} \<in> {0, 2}"
      and hfresh: "fst a \<notin> fst ` set w"
      and hY_ef: "top1_quotient_of_scheme_on Y_ef TY_ef ([a, top1_inverse_edge a] @ w)"
      and hY_wf: "top1_quotient_of_scheme_on Y_wf TY_wf w"
  shows "\<exists>h. top1_homeomorphism_on Y_ef TY_ef Y_wf TY_wf h"
proof -
  \<comment> \<open>Both quotient spaces are compact Hausdorff (polygon quotients).\<close>
  have htopo_ef: "is_topology_on_strict Y_ef TY_ef"
    using hY_ef unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  have htopo_wf: "is_topology_on_strict Y_wf TY_wf"
    using hY_wf unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  \<comment> \<open>Step 1: Both polygons are homeomorphic to B2 with boundary on S1.
     Use polygon\\_homeomorphic\\_to\\_disk\\_with\\_boundary for both P\\_ef and P\\_wf.
     This gives homeomorphisms psi\\_ef: P\\_ef -> B2 and psi\\_wf: P\\_wf -> B2
     mapping boundary to S1.\<close>
  \<comment> \<open>Step 2: In B2, the spur collapse is: identify two adjacent S1 arcs
     (corresponding to edges 0,1 of the a-pair) by the C7 identification.
     Since the identification is in opposite direction and the arcs are adjacent,
     the result is B2 with the two arcs collapsed to a point.
     B2 / (arc collapse) is homeomorphic to B2 (standard topology fact).\<close>
  \<comment> \<open>Step 3: Construct g: P\\_ef -> Y\\_wf (continuous surjection with matching fibres).
     g = q\\_wf composed with (psi\\_wf inverse) composed with (spur\\_collapse on B2) composed with psi\\_ef.
     This is a composition of continuous maps.\<close>
  \<comment> \<open>Step 4: Verify fibre matching and apply quotient\\_same\\_fibres\\_homeomorphic.\<close>
  \<comment> \<open>Step 2: Extract full conditions for both quotients.\<close>
  let ?ext = "[a, top1_inverse_edge a] @ w"
  let ?ne = "length ?ext"
  let ?nw = "length w"
  have hlen_ext: "length ?ext \<ge> 3" using hlen by (by100 simp)
  have hproper_ext: "\<forall>label. card {i. i < length ?ext \<and> fst (?ext ! i) = label} \<in> {0, 2}"
    by (rule cancel_pair_prepend_proper[OF hproper hfresh])
  from scheme_quotient_exists(2)[OF hlen_ext hproper_ext]
  obtain P_e :: "(real \<times> real) set" and q_e :: "real \<times> real \<Rightarrow> real \<times> real"
    and vxe vye :: "nat \<Rightarrow> real"
    and Y_e :: "(real \<times> real) set" and TY_e :: "(real \<times> real) set set"
    and vtgt_e :: "nat \<Rightarrow> nat"
    where hY_e: "top1_quotient_of_scheme_on Y_e TY_e ?ext"
    and hC2_e: "top1_quotient_map_on P_e
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_e)
        Y_e TY_e q_e"
    and hC3_e: "\<forall>i<?ne. \<forall>j<?ne. i \<noteq> j \<longrightarrow> (vxe i, vye i) \<noteq> (vxe j, vye j)"
    and hC7_e: "\<forall>i<?ne. \<forall>j<?ne. fst (?ext!i) = fst (?ext!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q_e ((1-t)*vxe i+t*vxe(Suc i mod ?ne),
            (1-t)*vye i+t*vye(Suc i mod ?ne))
         = (if snd (?ext!i) = snd (?ext!j)
            then q_e ((1-t)*vxe j+t*vxe(Suc j mod ?ne),
                    (1-t)*vye j+t*vye(Suc j mod ?ne))
            else q_e (t*vxe j+(1-t)*vxe(Suc j mod ?ne),
                    t*vye j+(1-t)*vye(Suc j mod ?ne))))"
    and hC8_e: "\<forall>p\<in>P_e. (\<forall>i<?ne. \<forall>t\<in>I_set.
          p \<noteq> ((1-t)*vxe i+t*vxe(Suc i mod ?ne),
                (1-t)*vye i+t*vye(Suc i mod ?ne)))
       \<longrightarrow> (\<forall>p'\<in>P_e. q_e p = q_e p' \<longrightarrow> p = p')"
    and hC9_e: "\<forall>i<?ne. \<forall>j<?ne. \<forall>t\<in>{0<..<(1::real)}. \<forall>s'\<in>{0<..<(1::real)}.
        q_e ((1-t)*vxe i+t*vxe(Suc i mod ?ne),
            (1-t)*vye i+t*vye(Suc i mod ?ne))
      = q_e ((1-s')*vxe j+s'*vxe(Suc j mod ?ne),
            (1-s')*vye j+s'*vye(Suc j mod ?ne))
      \<longrightarrow> (i=j \<and> t=s') \<or> (fst(?ext!i)=fst(?ext!j) \<and>
          (if snd(?ext!i)=snd(?ext!j) then s'=t else s'=1-t))"
    and hC12_e: "\<forall>k<?ne. \<forall>j<?ne. \<forall>s'\<in>{0<..<(1::real)}.
        q_e (vxe k, vye k) \<noteq> q_e ((1-s')*vxe j + s'*vxe(Suc j mod ?ne),
                               (1-s')*vye j + s'*vye(Suc j mod ?ne))"
    and hfan_det_e: "\<forall>m n. 2 \<le> m \<longrightarrow> m < n \<longrightarrow> n < ?ne \<longrightarrow>
        (vxe m - vxe 1) * (vye n - vye 1) - (vye m - vye 1) * (vxe n - vxe 1) > 0"
    and hC4_e: "\<forall>i<?ne. (vxe i, vye i) \<in> P_e"
    and hC5_e: "P_e = {(x, y) | x y. \<exists>coeffs. (\<forall>i<?ne. coeffs i \<ge> 0)
                   \<and> (\<Sum>i<?ne. coeffs i) = 1
                   \<and> x = (\<Sum>i<?ne. coeffs i * vxe i)
                   \<and> y = (\<Sum>i<?ne. coeffs i * vye i)}"
    and hC10_e: "\<forall>i<?ne. let cx = (\<Sum>j<?ne. vxe j) / real ?ne;
                             cy = (\<Sum>j<?ne. vye j) / real ?ne
         in (vxe i - cx) * (vye(Suc i mod ?ne) - cy) - (vye i - cy) * (vxe(Suc i mod ?ne) - cx) > 0"
    and hC11_e: "\<forall>i<?ne. \<forall>k<?ne. k\<noteq>i \<longrightarrow> k\<noteq>Suc i mod ?ne \<longrightarrow>
        (vxe k-vxe i)*(vye(Suc i mod ?ne)-vye i)-(vye k-vye i)*(vxe(Suc i mod ?ne)-vxe i) < 0"
    and hPR_e: "top1_is_polygonal_region_on P_e ?ne"
    and hvtgt_e_bound: "\<forall>k<?ne. vtgt_e k < ?ne"
    and hvtgt_e: "\<forall>k<?ne. q_e (vxe k, vye k) = (vxe (vtgt_e k), vye (vtgt_e k))"
    and hvtgt_e_chain: "\<forall>k<?ne. \<forall>l<?ne. vtgt_e k = vtgt_e l \<longrightarrow>
        (k, l) \<in> {(a, b). \<exists>i<?ne. \<exists>j<?ne. i \<noteq> j
          \<and> fst (?ext ! i) = fst (?ext ! j)
          \<and> ((snd (?ext ! i) = snd (?ext ! j) \<and> a = i \<and> b = j)
           \<or> (snd (?ext ! i) = snd (?ext ! j) \<and> a = Suc i mod ?ne \<and> b = Suc j mod ?ne)
           \<or> (snd (?ext ! i) \<noteq> snd (?ext ! j) \<and> a = i \<and> b = Suc j mod ?ne)
           \<or> (snd (?ext ! i) \<noteq> snd (?ext ! j) \<and> a = Suc i mod ?ne \<and> b = j))}\<^sup>*"
    by (elim exE conjE) (rule that, assumption+)
  from scheme_quotient_exists(2)[OF hlen hproper]
  obtain P_w :: "(real \<times> real) set" and q_w :: "real \<times> real \<Rightarrow> real \<times> real"
    and vxw vyw :: "nat \<Rightarrow> real"
    and Y_w :: "(real \<times> real) set" and TY_w :: "(real \<times> real) set set"
    and vtgt_w :: "nat \<Rightarrow> nat"
    where hY_w: "top1_quotient_of_scheme_on Y_w TY_w w"
    and hC2_w: "top1_quotient_map_on P_w
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_w)
        Y_w TY_w q_w"
    and hC7_w: "\<forall>i<?nw. \<forall>j<?nw. fst (w!i) = fst (w!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q_w ((1-t)*vxw i+t*vxw(Suc i mod ?nw),
            (1-t)*vyw i+t*vyw(Suc i mod ?nw))
         = (if snd (w!i) = snd (w!j)
            then q_w ((1-t)*vxw j+t*vxw(Suc j mod ?nw),
                    (1-t)*vyw j+t*vyw(Suc j mod ?nw))
            else q_w (t*vxw j+(1-t)*vxw(Suc j mod ?nw),
                    t*vyw j+(1-t)*vyw(Suc j mod ?nw))))"
    and hC8_w: "\<forall>p\<in>P_w. (\<forall>i<?nw. \<forall>t\<in>I_set.
          p \<noteq> ((1-t)*vxw i+t*vxw(Suc i mod ?nw),
                (1-t)*vyw i+t*vyw(Suc i mod ?nw)))
       \<longrightarrow> (\<forall>p'\<in>P_w. q_w p = q_w p' \<longrightarrow> p = p')"
    and hC9_w: "\<forall>i<?nw. \<forall>j<?nw. \<forall>t\<in>{0<..<(1::real)}. \<forall>s'\<in>{0<..<(1::real)}.
        q_w ((1-t)*vxw i+t*vxw(Suc i mod ?nw),
            (1-t)*vyw i+t*vyw(Suc i mod ?nw))
      = q_w ((1-s')*vxw j+s'*vxw(Suc j mod ?nw),
            (1-s')*vyw j+s'*vyw(Suc j mod ?nw))
      \<longrightarrow> (i=j \<and> t=s') \<or> (fst(w!i)=fst(w!j) \<and>
          (if snd(w!i)=snd(w!j) then s'=t else s'=1-t))"
    and hC12_w: "\<forall>k<?nw. \<forall>j<?nw. \<forall>s'\<in>{0<..<(1::real)}.
        q_w (vxw k, vyw k) \<noteq> q_w ((1-s')*vxw j + s'*vxw(Suc j mod ?nw),
                               (1-s')*vyw j + s'*vyw(Suc j mod ?nw))"
    and hC3_w: "\<forall>i<?nw. \<forall>j<?nw. i \<noteq> j \<longrightarrow> (vxw i, vyw i) \<noteq> (vxw j, vyw j)"
    and hC4_w: "\<forall>i<?nw. (vxw i, vyw i) \<in> P_w"
    and hC5_w: "P_w = {(x, y) | x y. \<exists>coeffs. (\<forall>i<?nw. coeffs i \<ge> 0)
                   \<and> (\<Sum>i<?nw. coeffs i) = 1
                   \<and> x = (\<Sum>i<?nw. coeffs i * vxw i)
                   \<and> y = (\<Sum>i<?nw. coeffs i * vyw i)}"
    and hfan_det_w: "\<forall>m n. 2 \<le> m \<longrightarrow> m < n \<longrightarrow> n < ?nw \<longrightarrow>
        (vxw m - vxw 1) * (vyw n - vyw 1) - (vyw m - vyw 1) * (vxw n - vxw 1) > 0"
    and hC10_w: "\<forall>i<?nw. let cx = (\<Sum>j<?nw. vxw j) / real ?nw;
                             cy = (\<Sum>j<?nw. vyw j) / real ?nw
         in (vxw i - cx) * (vyw(Suc i mod ?nw) - cy) - (vyw i - cy) * (vxw(Suc i mod ?nw) - cx) > 0"
    and hC11_w: "\<forall>i<?nw. \<forall>k<?nw. k\<noteq>i \<longrightarrow> k\<noteq>Suc i mod ?nw \<longrightarrow>
        (vxw k-vxw i)*(vyw(Suc i mod ?nw)-vyw i)-(vyw k-vyw i)*(vxw(Suc i mod ?nw)-vxw i) < 0"
    and hPR_w: "top1_is_polygonal_region_on P_w ?nw"
    and hvtgt_w_bound: "\<forall>k<?nw. vtgt_w k < ?nw"
    and hvtgt_w: "\<forall>k<?nw. q_w (vxw k, vyw k) = (vxw (vtgt_w k), vyw (vtgt_w k))"
    and hvtgt_w_chain: "\<forall>k<?nw. \<forall>l<?nw. vtgt_w k = vtgt_w l \<longrightarrow>
        (k, l) \<in> {(a, b). \<exists>i<?nw. \<exists>j<?nw. i \<noteq> j
          \<and> fst (w ! i) = fst (w ! j)
          \<and> ((snd (w ! i) = snd (w ! j) \<and> a = i \<and> b = j)
           \<or> (snd (w ! i) = snd (w ! j) \<and> a = Suc i mod ?nw \<and> b = Suc j mod ?nw)
           \<or> (snd (w ! i) \<noteq> snd (w ! j) \<and> a = i \<and> b = Suc j mod ?nw)
           \<or> (snd (w ! i) \<noteq> snd (w ! j) \<and> a = Suc i mod ?nw \<and> b = j))}\<^sup>*"
    and hsum_vxw_0: "(\<Sum>k<?nw. vxw k) = 0"
    and hsum_vyw_0: "(\<Sum>k<?nw. vyw k) = 0"
    and hunit_circle_w: "\<forall>j<?nw. (vxw j)^2 + (vyw j)^2 = 1"
    by (elim exE conjE) (rule that, assumption+)
  define cxw where "cxw = (\<Sum>j<?nw. vxw j) / real ?nw"
  define cyw where "cyw = (\<Sum>j<?nw. vyw j) / real ?nw"
  have hcxw_0: "cxw = 0" unfolding cxw_def using hsum_vxw_0 by (by100 simp)
  have hcyw_0: "cyw = 0" unfolding cyw_def using hsum_vyw_0 by (by100 simp)
  have hregular_w: "\<exists>r>(0::real). \<forall>j<?nw. (vxw j - cxw)^2 + (vyw j - cyw)^2 = r^2"
  proof (rule exI[of _ 1], intro conjI)
    show "(0::real) < 1" by (by100 simp)
    show "\<forall>j<?nw. (vxw j - cxw)^2 + (vyw j - cyw)^2 = 1^2"
      using hunit_circle_w hcxw_0 hcyw_0 by (by100 simp)
  qed
  let ?cxw = "(\<Sum>j<?nw. vxw j) / real ?nw"
  let ?cyw = "(\<Sum>j<?nw. vyw j) / real ?nw"
  have htopo_e: "is_topology_on_strict Y_e TY_e"
    using hY_e unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  have htopo_w: "is_topology_on_strict Y_w TY_w"
    using hY_w unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  \<comment> \<open>Step 3: Define g: P\\_e -> Y\\_w by cone construction.
     Centroids of both polygons:\<close>
  let ?cx_e = "(\<Sum>j<?ne. vxe j) / real ?ne"
  let ?cy_e = "(\<Sum>j<?ne. vye j) / real ?ne"
  let ?cx_w = "(\<Sum>j<?nw. vxw j) / real ?nw"
  let ?cy_w = "(\<Sum>j<?nw. vyw j) / real ?nw"
  \<comment> \<open>Boundary map phi: boundary(P\\_e) -> P\\_w.
     - On spur edges (0,1): phi maps to vertex u\\_0 = (vxw 0, vyw 0)
     - On edge k+2 at parameter t: phi maps to the corresponding point on edge k of P\\_w
     Interior: for x = (1-s)*centroid\\_e + s*b where b is on boundary:
       g(x) = q\\_w((1-s)*(cx\\_w, cy\\_w) + s*phi(b))
     This is a well-defined continuous map from P\\_e to Y\\_w.\<close>
  \<comment> \<open>Step 4: g factors through q\\_e (constant on q\\_e-fibres).
     Forward: q\\_e(x) = q\\_e(y) implies g(x) = g(y).
     Cases:
     - Interior: C8 gives x = y, so g(x) = g(y) trivially.
     - Both on spur: g is constant q\\_w(vxw 0, vyw 0) on spur. CHECK.
     - Matched non-spur edges: C7 for ext at indices i+2, j+2 gives
       the same identification as C7 for w at indices i, j. CHECK.
     - Spur vertex to non-spur vertex: q\\_e(v\\_0) = q\\_e(v\\_2) by C7 for a-pair.
       g(v\\_0) = q\\_w(vxw 0, vyw 0), g(v\\_2) = q\\_w(vxw 0, vyw 0). CHECK.
     - Vertex-edge: impossible by C12. CHECK.\<close>
  \<comment> \<open>Step 5: g is surjective and continuous.
     Surjectivity: the non-spur cone sectors cover all of P\\_w (via the affine sector maps).
     Continuity: phi is continuous on boundary (piecewise linear, agrees at junctions).
       The cone extension is continuous (convex combination with continuous coefficients).\<close>
  \<comment> \<open>Step 6: Theorem 22.2 gives f: Y\\_e -> Y\\_w. Then f is bijective and continuous.
     Bijectivity: f is injective because g-fibres = q\\_e-fibres (backward direction).
     Backward: g(x) = g(y) implies q\\_e(x) = q\\_e(y).
     - Interior: q\\_w injective by C8\\_w, cone map injective on non-spur sectors -> x = y.
     - Both spur: q\\_e identifies all spur points. CHECK.
     - Non-spur edge pair: q\\_w C9 gives label match -> q\\_e C7 gives identification.
     - One spur, one non-spur: g(spur) = q\\_w(vertex), g(non-spur edge) = q\\_w(edge\\_interior).
       C12\\_w: vertex != edge\\_interior. So g(spur) != g(non-spur edge). Contradiction.
     - One spur, one interior: g(spur) = q\\_w(vertex), g(interior) = q\\_w(interior\\_point).
       q\\_w(vertex) != q\\_w(interior\\_point) by C8\\_w (interior injective) + topology. CHECK.\<close>
  \<comment> \<open>Step 7: f is continuous bijection, compact to Hausdorff -> homeomorphism.
     Y\\_e compact Hausdorff from Theorem\\_74\\_1.
     Apply Theorem 26.6.\<close>
  \<comment> \<open>Step 8: Bridge Y\\_ef to Y\\_e and Y\\_w to Y\\_wf using uniqueness.\<close>
  from scheme_quotient_uniqueness[OF htopo_ef htopo_e hY_ef hY_e]
  obtain h1 where hh1: "top1_homeomorphism_on Y_ef TY_ef Y_e TY_e h1"
    by (by100 blast)
  \<comment> \<open>PROOF OF SPUR-COLLAPSE HOMEOMORPHISM.
     Define g: P\\_e -> Y\\_w by piecewise:
     - On non-spur cone sectors: g = q\\_w composed with sector-affine map to P\\_w
     - On spur cone: g = q\\_w(u\\_0) (constant, vertex image)
     g is continuous because at spur-non-spur junction, both sides approach q\\_w(u\\_0).
     g factors through q\\_e by fibre matching (C7/C8/C12).
     The induced f: Y\\_e -> Y\\_w is continuous (Theorem 22.2), bijective (fibre matching),
     and Y\\_e is compact Hausdorff (Theorem 74.1), so Theorem 26.6 gives homeomorphism.\<close>
  \<comment> \<open>Step A: Y\\_e is compact and Hausdorff.\<close>
  have hpoly_e: "top1_is_polygonal_quotient_on Y_e TY_e"
    unfolding top1_is_polygonal_quotient_on_def using htopo_e hY_e by (by100 blast)
  have hpoly_w: "top1_is_polygonal_quotient_on Y_w TY_w"
    unfolding top1_is_polygonal_quotient_on_def using htopo_w hY_w by (by100 blast)
  from Theorem_74_1_polygon_quotient_compact_hausdorff[OF htopo_e hpoly_e]
  have hcompact_e: "top1_compact_on Y_e TY_e" and hhaus_e: "is_hausdorff_on Y_e TY_e"
    by (by100 blast)+
  from Theorem_74_1_polygon_quotient_compact_hausdorff[OF htopo_w hpoly_w]
  have hcompact_w: "top1_compact_on Y_w TY_w" and hhaus_w: "is_hausdorff_on Y_w TY_w"
    by (by100 blast)+
  \<comment> \<open>Step B: Define g: P\\_e -> Y\\_w (continuous, constant on q\\_e-fibres).
     g is defined piecewise on cone sectors from centroid.
     On non-spur sector k (for edge k+2): affine map to corresponding sector in P\\_w,
     then compose with q\\_w.
     On spur sectors (for edges 0,1): constant q\\_w(vxw 0, vyw 0).\<close>
  \<comment> \<open>Define g: P\\_e -> Y\\_w explicitly.
     For each point p in P\\_e, determine which cone sector from centroid it belongs to.
     - Spur sectors (behind edges 0,1): g(p) = q\\_w(vxw 0, vyw 0)
     - Non-spur sector k+2 (behind edge k+2 of P\\_e):
       g(p) = q\\_w(corresponding point in sector k of P\\_w)
     The sector map is an affine map from triangle (centroid\\_e, v\\_{k+2}, v\\_{k+3})
     to triangle (centroid\\_w, u\\_k, u\\_{k+1}).\<close>
  define edge_pt_e where "edge_pt_e i t = ((1-t)*vxe i+t*vxe(Suc i mod ?ne),
                                            (1-t)*vye i+t*vye(Suc i mod ?ne))" for i t
  define edge_pt_w where "edge_pt_w i t = ((1-t)*vxw i+t*vxw(Suc i mod ?nw),
                                            (1-t)*vyw i+t*vyw(Suc i mod ?nw))" for i t
  \<comment> \<open>Label correspondence: ext[k+2] = w[k] for all k < nw.\<close>
  have hlabel_corr: "\<forall>k<?nw. ?ext ! (k+2) = w ! k"
  proof (intro allI impI)
    fix k assume hk: "k < ?nw"
    show "?ext ! (k+2) = w ! k" using hk by (by100 simp)
  qed
  have hspur0: "?ext ! 0 = a" by (by100 simp)
  have hspur1: "?ext ! 1 = top1_inverse_edge a" by (by100 simp)
  have hne_eq: "?ne = ?nw + 2" by (by100 simp)
  \<comment> \<open>Define g: P\\_e -> Y\\_w.
     On non-spur boundary edge k+2 at parameter t: g maps to q\\_w(edge\\_pt\\_w(k, t)).
     On spur boundary (edges 0,1): g maps to q\\_w(vxw 0, vyw 0) (the vertex image).
     On interior: g maps via piecewise affine sector map from P\\_e to P\\_w, composed with q\\_w.
     This requires defining the sector decomposition and the affine maps.
     For now: assert existence with required properties.\<close>
  have "\<exists>g. (\<forall>p \<in> P_e. g p \<in> Y_w)
      \<and> top1_continuous_map_on P_e
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_e)
          Y_w TY_w g
      \<and> g ` P_e = Y_w
      \<and> (\<forall>x\<in>P_e. \<forall>y\<in>P_e. q_e x = q_e y \<longrightarrow> g x = g y)
      \<and> (\<forall>x\<in>P_e. \<forall>y\<in>P_e. g x = g y \<longrightarrow> q_e x = q_e y)"
  proof -
    \<comment> \<open>Key boundary property: the w-polygon vertex u\\_0 is the endpoint of edges 0 and n-1.
       This ensures g is continuous at the spur-non-spur junction.\<close>
    have hu0_edge0: "edge_pt_w 0 0 = (vxw 0, vyw 0)"
      unfolding edge_pt_w_def by (by100 simp)
    have hu0_edgen: "edge_pt_w (?nw - 1) 1 = (vxw (Suc (?nw - 1) mod ?nw), vyw (Suc (?nw - 1) mod ?nw))"
      unfolding edge_pt_w_def by (by100 simp)
    have hnw_pos: "?nw > 0" using hlen by (by100 linarith)
    have hnw_mod: "Suc (?nw - 1) mod ?nw = 0"
    proof -
      have "Suc (?nw - 1) = ?nw" using hnw_pos by (by100 simp)
      thus ?thesis by (by100 simp)
    qed
    have hu0_edgen': "edge_pt_w (?nw - 1) 1 = (vxw 0, vyw 0)"
      using hu0_edgen hnw_mod by (by100 simp)
    \<comment> \<open>Define the boundary map phi: boundary(P\\_e) -> P\\_w.\<close>
    define phi_bdy :: "nat \<Rightarrow> real \<Rightarrow> real \<times> real" where
      "phi_bdy i t = (if i < 2 then (vxw 0, vyw 0)
                      else edge_pt_w (i - 2) t)" for i t
    \<comment> \<open>phi\\_bdy maps spur edges to u\\_0, non-spur edge k+2 to edge\\_w(k, t).\<close>
    have hphi_spur: "\<forall>i<2. \<forall>t. phi_bdy i t = (vxw 0, vyw 0)"
      unfolding phi_bdy_def by (by100 simp)
    have hphi_nonspur: "\<forall>k<?nw. \<forall>t. phi_bdy (k+2) t = edge_pt_w k t"
      unfolding phi_bdy_def by (by100 simp)
    \<comment> \<open>Continuity at junction v\\_2 (edge 1 -> edge 2):
       phi\\_bdy(1, 1) = (vxw 0, vyw 0) [spur edge 1 at t=1]
       phi\\_bdy(2, 0) = edge\\_pt\\_w(0, 0) = (vxw 0, vyw 0) [non-spur edge 2 at t=0]
       These agree. CHECK.\<close>
    have hjunction_v2: "phi_bdy 1 1 = phi_bdy 2 0"
    proof -
      have "phi_bdy 1 1 = (vxw 0, vyw 0)" unfolding phi_bdy_def by (by100 simp)
      also have "(vxw 0, vyw 0) = edge_pt_w 0 0" unfolding edge_pt_w_def by (by100 simp)
      also have "edge_pt_w 0 0 = phi_bdy 2 0" unfolding phi_bdy_def by (by100 simp)
      finally show ?thesis .
    qed
    \<comment> \<open>Continuity at junction v\\_0 (edge n+1 -> edge 0):
       phi\\_bdy(?ne-1, 1) = edge\\_pt\\_w(?nw-1, 1) = (vxw 0, vyw 0) [last non-spur edge at t=1]
       phi\\_bdy(0, 0) = (vxw 0, vyw 0) [spur edge 0 at t=0]
       These agree. CHECK.\<close>
    have hjunction_v0: "phi_bdy (?ne - 1) 1 = phi_bdy 0 0"
    proof -
      have hne_ge3: "?ne - 1 \<ge> 2" using hlen hne_eq by (by100 linarith)
      have hne_sub: "(?ne - 1) - 2 = ?nw - 1"
      proof -
        have "?ne = ?nw + 2" using hne_eq .
        hence "?ne - 1 = ?nw + 1" using hnw_pos by (by100 linarith)
        hence "(?ne - 1) - 2 = ?nw - 1" using hnw_pos by (by100 linarith)
        thus ?thesis .
      qed
      have hne_not_lt2: "\<not> (?ne - 1 < 2)" using hne_ge3 by (by100 linarith)
      have h1: "phi_bdy (?ne - 1) 1 = edge_pt_w ((?ne - 1) - 2) 1"
        unfolding phi_bdy_def using hne_not_lt2 by (by100 simp)
      have h2: "phi_bdy (?ne - 1) 1 = edge_pt_w (?nw - 1) 1"
        using h1 hne_sub by (by100 simp)
      have h3: "phi_bdy 0 0 = (vxw 0, vyw 0)" unfolding phi_bdy_def by (by100 simp)
      show ?thesis using h2 hu0_edgen' h3 by (by100 simp)
    qed
    \<comment> \<open>Spur-non-spur separation: q\\_e never identifies spur edge-interior with non-spur edge-interior.
       Follows from C9 + freshness of a.\<close>
    have hspur_sep: "\<forall>t\<in>{0<..<(1::real)}. \<forall>k<?nw. \<forall>s\<in>{0<..<(1::real)}.
        q_e (edge_pt_e 0 t) \<noteq> q_e (edge_pt_e (k+2) s)"
    proof (intro ballI allI impI)
      fix t s :: real and k :: nat
      assume ht: "t \<in> {0<..<(1::real)}" and hk: "k < ?nw" and hs: "s \<in> {0<..<(1::real)}"
      have h0_lt: "0 < ?ne" using hlen hne_eq by (by100 linarith)
      have hk2_lt: "k+2 < ?ne" using hk hne_eq by (by100 linarith)
      \<comment> \<open>Labels don't match: ext[0] = a (fresh label), ext[k+2] = w[k] (no a label).\<close>
      have "fst (?ext ! 0) = fst a" using hspur0 by (by100 simp)
      moreover have "fst (?ext ! (k+2)) = fst (w ! k)"
      proof -
        from hlabel_corr have "?ext ! (k+2) = w ! k" using hk by (by100 blast)
        thus ?thesis by (by100 simp)
      qed
      moreover have hfst_neq: "fst a \<noteq> fst (w ! k)"
      proof
        assume "fst a = fst (w ! k)"
        have "w ! k \<in> set w" using hk by (by100 simp)
        hence "fst (w ! k) \<in> fst ` set w" by (by100 blast)
        hence "fst a \<in> fst ` set w" using \<open>fst a = fst (w ! k)\<close> by (by100 simp)
        thus False using hfresh by (by100 blast)
      qed
      ultimately have hlabel_neq: "fst (?ext ! 0) \<noteq> fst (?ext ! (k+2))" by (by100 simp)
      \<comment> \<open>By C9: if q\\_e identifies edge-interiors, labels must match. Contradiction.\<close>
      show "q_e (edge_pt_e 0 t) \<noteq> q_e (edge_pt_e (k+2) s)"
      proof
        assume heq: "q_e (edge_pt_e 0 t) = q_e (edge_pt_e (k+2) s)"
        have hC9_inst: "q_e ((1-t)*vxe 0+t*vxe(Suc 0 mod ?ne),
            (1-t)*vye 0+t*vye(Suc 0 mod ?ne))
          = q_e ((1-s)*vxe (k+2)+s*vxe(Suc (k+2) mod ?ne),
            (1-s)*vye (k+2)+s*vye(Suc (k+2) mod ?ne))"
          using heq unfolding edge_pt_e_def by (by100 simp)
        from hC9_e[rule_format, OF h0_lt hk2_lt ht hs] hC9_inst
        have "(0 = k+2 \<and> t = s) \<or> (fst(?ext!0) = fst(?ext!(k+2)) \<and>
            (if snd(?ext!0)=snd(?ext!(k+2)) then s=t else s=1-t))"
          by (by100 blast)
        thus False
        proof (elim disjE conjE)
          assume "0 = k+2" thus False by (by100 simp)
        next
          assume "fst(?ext!0) = fst(?ext!(k+2))"
          thus False using hlabel_neq by (by100 simp)
        qed
      qed
    qed
    \<comment> \<open>Similarly for edge 1 vs non-spur:\<close>
    have hspur_sep1: "\<forall>t\<in>{0<..<(1::real)}. \<forall>k<?nw. \<forall>s\<in>{0<..<(1::real)}.
        q_e (edge_pt_e 1 t) \<noteq> q_e (edge_pt_e (k+2) s)"
    proof (intro ballI allI impI)
      fix t s :: real and k :: nat
      assume ht: "t \<in> {0<..<(1::real)}" and hk: "k < ?nw" and hs: "s \<in> {0<..<(1::real)}"
      have h1_lt: "1 < ?ne" using hlen hne_eq by (by100 linarith)
      have hk2_lt: "k+2 < ?ne" using hk hne_eq by (by100 linarith)
      have "fst (?ext ! 1) = fst (top1_inverse_edge a)" using hspur1 by (by100 simp)
      hence hfst1: "fst (?ext ! 1) = fst a" unfolding top1_inverse_edge_def by (by100 simp)
      have "fst (?ext ! (k+2)) = fst (w ! k)"
      proof -
        from hlabel_corr have "?ext ! (k+2) = w ! k" using hk by (by100 blast)
        thus ?thesis by (by100 simp)
      qed
      have hfst_neq1: "fst a \<noteq> fst (w ! k)"
      proof
        assume "fst a = fst (w ! k)"
        have "w ! k \<in> set w" using hk by (by100 simp)
        hence "fst (w ! k) \<in> fst ` set w" by (by100 blast)
        hence "fst a \<in> fst ` set w" using \<open>fst a = fst (w ! k)\<close> by (by100 simp)
        thus False using hfresh by (by100 blast)
      qed
      have hlabel_neq1: "fst (?ext ! 1) \<noteq> fst (?ext ! (k+2))"
        using hfst1 \<open>fst (?ext ! (k+2)) = fst (w ! k)\<close> hfst_neq1 by (by100 simp)
      show "q_e (edge_pt_e 1 t) \<noteq> q_e (edge_pt_e (k+2) s)"
      proof
        assume heq: "q_e (edge_pt_e 1 t) = q_e (edge_pt_e (k+2) s)"
        have hC9_inst: "q_e ((1-t)*vxe 1+t*vxe(Suc 1 mod ?ne),
            (1-t)*vye 1+t*vye(Suc 1 mod ?ne))
          = q_e ((1-s)*vxe (k+2)+s*vxe(Suc (k+2) mod ?ne),
            (1-s)*vye (k+2)+s*vye(Suc (k+2) mod ?ne))"
          using heq unfolding edge_pt_e_def by (by100 simp)
        from hC9_e[rule_format, OF h1_lt hk2_lt ht hs] hC9_inst
        have "(1 = k+2 \<and> t = s) \<or> (fst(?ext!1) = fst(?ext!(k+2)) \<and>
            (if snd(?ext!1)=snd(?ext!(k+2)) then s=t else s=1-t))"
          by (by100 blast)
        thus False
        proof (elim disjE conjE)
          assume "1 = k+2" thus False by (by100 simp)
        next
          assume "fst(?ext!1) = fst(?ext!(k+2))"
          thus False using hlabel_neq1 by (by100 simp)
        qed
      qed
    qed
    \<comment> \<open>TOPOLOGICAL FACT: there exists a continuous surjection phi: P\\_e -> P\\_w
       that maps:
       - Non-spur edges of P\\_e to corresponding edges of P\\_w (linearly)
       - Spur edges of P\\_e to an ARC in P\\_w from u\\_0 into the interior
         (matching the C7 identification: phi(edge(0,t)) = phi(edge(1,1-t)))
       - Interior of P\\_e to interior of P\\_w (injectively)
       The ARC goes from boundary vertex u\\_0 into the interior of P\\_w.
       For t in (0,1): the arc point is in the interior of P\\_w (not on any edge).
       The function g = q\\_w o phi: P\\_e -> Y\\_w then has EXACT fibre matching.\<close>
    obtain phi :: "real \<times> real \<Rightarrow> real \<times> real" where
        hphi_range: "\<forall>p \<in> P_e. phi p \<in> P_w"
      and hphi_cont: "top1_continuous_map_on P_e
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_e)
          P_w (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_w) phi"
      and hphi_surj: "phi ` P_e = P_w"
      and hphi_spur_match: "\<forall>t\<in>I_set. phi (edge_pt_e 0 t) = phi (edge_pt_e 1 (1-t))"
      and hphi_spur_endpoints: "phi (edge_pt_e 0 0) = (vxw 0, vyw 0)"
      and hphi_spur_int: "\<forall>t\<in>{0<..<(1::real)}.
          (\<forall>j<?nw. \<forall>s\<in>I_set. phi (edge_pt_e 0 t) \<noteq> edge_pt_w j s)"
      and hphi_spur_tip_int: "\<forall>j<?nw. \<forall>s\<in>I_set. phi (edge_pt_e 0 1) \<noteq> edge_pt_w j s"
      and hphi_spur_inj: "\<forall>t\<in>I_set. \<forall>s\<in>I_set.
          phi (edge_pt_e 0 t) = phi (edge_pt_e 0 s) \<longrightarrow> t = s"
      and hphi_nonspur: "\<forall>k<?nw. \<forall>t\<in>I_set.
          phi (edge_pt_e (k+2) t) = edge_pt_w k t"
      and hphi_int_inj: "\<forall>p\<in>P_e. \<forall>p'\<in>P_e.
          (\<forall>i<?ne. \<forall>t\<in>I_set. p \<noteq> edge_pt_e i t) \<longrightarrow>
          (\<forall>i<?ne. \<forall>t\<in>I_set. p' \<noteq> edge_pt_e i t) \<longrightarrow>
          phi p = phi p' \<longrightarrow> p = p'"
      and hphi_int_to_int: "\<forall>p\<in>P_e.
          (\<forall>i<?ne. \<forall>t\<in>I_set. p \<noteq> edge_pt_e i t) \<longrightarrow>
          (\<forall>j<?nw. \<forall>s\<in>I_set. phi p \<noteq> edge_pt_w j s)"
      and hphi_spur_not_int: "\<forall>t\<in>I_set. \<forall>p\<in>P_e.
          (\<forall>i<?ne. \<forall>s\<in>I_set. p \<noteq> edge_pt_e i s) \<longrightarrow>
          phi (edge_pt_e 0 t) \<noteq> phi p"
    \<comment> \<open>PHI CONSTRUCTION: piecewise-affine star extension from v\\_1 = (vxe 1, vye 1).
       Fan triangulation of P\\_e from v\\_1 into nw sectors.
       Sector j = triangle(v\\_1, v\\_{j+2}, v\\_{j+3}).
       Affine map: v\\_1 -> centroid(P\\_w), v\\_{j+2} -> u\\_j, v\\_{j+3} -> u\\_{j+1}.
       Non-spur edges map linearly. Spur edges map to arc from u\\_0 to centroid.
       Interior maps injectively to interior (sectors map to centroid-cone sectors of P\\_w).\<close>
    proof -
      let ?cxw = "(\<Sum>j<?nw. vxw j) / real ?nw"
      let ?cyw = "(\<Sum>j<?nw. vyw j) / real ?nw"
      \<comment> \<open>Cross product from v\\_1: determines sector membership.\<close>
      define cross_v1 where "cross_v1 j p =
        (vxe j - vxe 1) * (snd p - vye 1) - (vye j - vye 1) * (fst p - vxe 1)" for j p
      \<comment> \<open>Sector test: p is in fan triangle T\\_j = conv(v\\_1, v\\_{j+2}, v\\_{j+3}).\<close>
      define in_sector where "in_sector j p =
        (cross_v1 (j+2) p \<ge> 0 \<and> cross_v1 (Suc(j+2) mod ?ne) p \<le> 0)" for j p
      \<comment> \<open>Define phi: for p in sector j, apply the affine map.\<close>
      define phi_fn where "phi_fn p = (
        if p = (vxe 1, vye 1) then (?cxw, ?cyw)
        else let j = (LEAST j. j < ?nw \<and> in_sector j p) in
             let ex = vxe(j+2) - vxe 1; ey = vye(j+2) - vye 1;
                 fx = vxe(Suc(j+2) mod ?ne) - vxe 1; fy = vye(Suc(j+2) mod ?ne) - vye 1;
                 det = ex*fy - ey*fx;
                 dx = fst p - vxe 1; dy = snd p - vye 1;
                 s = (fy*dx - fx*dy) / det;
                 t_par = (ex*dy - ey*dx) / det in
             ((1-s-t_par)*?cxw + s*vxw j + t_par*vxw(Suc j mod ?nw),
              (1-s-t_par)*?cyw + s*vyw j + t_par*vyw(Suc j mod ?nw)))" for p
      \<comment> \<open>Named sector computation functions (for avoiding let-expression blowup).\<close>
      \<comment> \<open>phi\\_s2/phi\\_t2 take explicit vertex indices m, m' to avoid (j+2) nat issues.\<close>
      define phi_s2 :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
        "phi_s2 m m' dx dy = (let ex = vxe m-vxe 1; ey = vye m-vye 1;
                                  fx = vxe m'-vxe 1; fy = vye m'-vye 1;
                                  det = ex*fy-ey*fx in (fy*dx-fx*dy)/det)" for m m' dx dy
      define phi_t2 :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
        "phi_t2 m m' dx dy = (let ex = vxe m-vxe 1; ey = vye m-vye 1;
                                  fx = vxe m'-vxe 1; fy = vye m'-vye 1;
                                  det = ex*fy-ey*fx in (ex*dy-ey*dx)/det)" for m m' dx dy
      \<comment> \<open>phi\\_s/phi\\_t in terms of phi\\_s2/phi\\_t2:\<close>
      have hphi_s_eq: "\<And>j dx dy. phi_s2 (j+2) (Suc(j+2) mod ?ne) dx dy =
        (let ex = vxe(j+2)-vxe 1; ey = vye(j+2)-vye 1;
             fx = vxe(Suc(j+2) mod ?ne)-vxe 1; fy = vye(Suc(j+2) mod ?ne)-vye 1;
             det = ex*fy-ey*fx in (fy*dx-fx*dy)/det)"
        unfolding phi_s2_def by (by100 simp)
      have hphi_t_eq: "\<And>j dx dy. phi_t2 (j+2) (Suc(j+2) mod ?ne) dx dy =
        (let ex = vxe(j+2)-vxe 1; ey = vye(j+2)-vye 1;
             fx = vxe(Suc(j+2) mod ?ne)-vxe 1; fy = vye(Suc(j+2) mod ?ne)-vye 1;
             det = ex*fy-ey*fx in (ex*dy-ey*dx)/det)"
        unfolding phi_t2_def by (by100 simp)
      \<comment> \<open>phi\\_fn in terms of phi\\_s/phi\\_t:\<close>
      have hphi_fn_decomp: "\<And>a b j. (a, b) \<noteq> (vxe 1, vye 1) \<Longrightarrow>
        (LEAST j'. j' < ?nw \<and> in_sector j' (a, b)) = j \<Longrightarrow>
        phi_fn (a, b) = ((1 - phi_s2 (j+2) (Suc(j+2) mod ?ne) (a-vxe 1) (b-vye 1)
                           - phi_t2 (j+2) (Suc(j+2) mod ?ne) (a-vxe 1) (b-vye 1))*?cxw
                         + phi_s2 (j+2) (Suc(j+2) mod ?ne) (a-vxe 1) (b-vye 1)*vxw j
                         + phi_t2 (j+2) (Suc(j+2) mod ?ne) (a-vxe 1) (b-vye 1)*vxw(Suc j mod ?nw),
                         (1 - phi_s2 (j+2) (Suc(j+2) mod ?ne) (a-vxe 1) (b-vye 1)
                           - phi_t2 (j+2) (Suc(j+2) mod ?ne) (a-vxe 1) (b-vye 1))*?cyw
                         + phi_s2 (j+2) (Suc(j+2) mod ?ne) (a-vxe 1) (b-vye 1)*vyw j
                         + phi_t2 (j+2) (Suc(j+2) mod ?ne) (a-vxe 1) (b-vye 1)*vyw(Suc j mod ?nw))"
        unfolding phi_fn_def phi_s2_def phi_t2_def Let_def by (by100 simp)
      \<comment> \<open>Key helpers about the centroid of P\\_w.\<close>
      have hcw_in_Pw: "(?cxw, ?cyw) \<in> P_w"
      proof -
        define coeffs :: "nat \<Rightarrow> real" where "coeffs i = 1 / real ?nw" for i
        have hnn: "\<forall>i<?nw. coeffs i \<ge> 0"
          unfolding coeffs_def using hnw_pos by (by100 auto)
        have hsum: "(\<Sum>i<?nw. coeffs i) = 1"
          unfolding coeffs_def using hnw_pos by (by100 simp)
        have hx: "?cxw = (\<Sum>i<?nw. coeffs i * vxw i)"
        proof -
          have "(\<Sum>i<?nw. coeffs i * vxw i) = (\<Sum>i<?nw. (1/real ?nw) * vxw i)"
            unfolding coeffs_def by (by100 simp)
          also have "\<dots> = (1/real ?nw) * (\<Sum>i<?nw. vxw i)"
            using sum_distrib_left[of "1/real ?nw" vxw "{..<?nw}", symmetric] by (by100 simp)
          also have "\<dots> = ?cxw" by (by100 simp)
          finally show ?thesis by (by100 simp)
        qed
        have hy: "?cyw = (\<Sum>i<?nw. coeffs i * vyw i)"
        proof -
          have "(\<Sum>i<?nw. coeffs i * vyw i) = (\<Sum>i<?nw. (1/real ?nw) * vyw i)"
            unfolding coeffs_def by (by100 simp)
          also have "\<dots> = (1/real ?nw) * (\<Sum>i<?nw. vyw i)"
            using sum_distrib_left[of "1/real ?nw" vyw "{..<?nw}", symmetric] by (by100 simp)
          also have "\<dots> = ?cyw" by (by100 simp)
          finally show ?thesis by (by100 simp)
        qed
        show ?thesis unfolding hC5_w using hnn hsum hx hy by (by100 auto)
      qed
      have hcw_neq_u0: "(?cxw, ?cyw) \<noteq> (vxw 0, vyw 0)"
      proof
        assume heq: "(?cxw, ?cyw) = (vxw 0, vyw 0)"
        hence "?cxw = vxw 0" and "?cyw = vyw 0" by (by100 simp)+
        have h0_lt: "(0::nat) < ?nw" using hnw_pos by (by100 simp)
        from hC10_w[rule_format, OF h0_lt]
        have "let cx = ?cxw; cy = ?cyw
          in (vxw 0 - cx) * (vyw(Suc 0 mod ?nw) - cy) - (vyw 0 - cy) * (vxw(Suc 0 mod ?nw) - cx) > 0"
          by (by100 simp)
        hence "(vxw 0 - ?cxw) * (vyw(Suc 0 mod ?nw) - ?cyw) -
               (vyw 0 - ?cyw) * (vxw(Suc 0 mod ?nw) - ?cxw) > 0"
          by (by100 simp)
        hence "(vxw 0 - vxw 0) * (vyw(Suc 0 mod ?nw) - vyw 0) -
               (vyw 0 - vyw 0) * (vxw(Suc 0 mod ?nw) - vxw 0) > 0"
          using \<open>?cxw = vxw 0\<close> \<open>?cyw = vyw 0\<close> by (by100 simp)
        thus False by (by100 simp)
      qed
      have hcw_not_edge: "\<forall>j<?nw. \<forall>t\<in>I_set. (?cxw, ?cyw) \<noteq> edge_pt_w j t"
      proof (intro allI ballI impI)
        fix j :: nat and t :: real
        assume hj: "j < ?nw" and ht: "t \<in> I_set"
        show "(?cxw, ?cyw) \<noteq> edge_pt_w j t"
        proof
          assume heq: "(?cxw, ?cyw) = edge_pt_w j t"
          hence hcx_eq: "?cxw = (1-t)*vxw j + t*vxw(Suc j mod ?nw)"
            and hcy_eq: "?cyw = (1-t)*vyw j + t*vyw(Suc j mod ?nw)"
            unfolding edge_pt_w_def by (by100 simp)+
          \<comment> \<open>From C10 at i=j: cross product of (v\\_j - centroid, v\\_{j+1} - centroid) > 0.
             But if centroid is on edge j, this cross product is 0. Contradiction.\<close>
          from hC10_w[rule_format, OF hj]
          have hcr: "let cx = ?cxw; cy = ?cyw
            in (vxw j - cx) * (vyw(Suc j mod ?nw) - cy) - (vyw j - cy) * (vxw(Suc j mod ?nw) - cx) > 0"
            by (by100 simp)
          hence hcr': "(vxw j - ?cxw) * (vyw(Suc j mod ?nw) - ?cyw) -
                       (vyw j - ?cyw) * (vxw(Suc j mod ?nw) - ?cxw) > 0"
            by (by100 simp)
          \<comment> \<open>If centroid = (1-t)*v\\_j + t*v\\_{j+1}, then v\\_j - centroid = -t*(v\\_{j+1}-v\\_j)
             and v\\_{j+1} - centroid = (1-t)*(v\\_{j+1}-v\\_j). Cross product = -t*(1-t)*0 = 0.\<close>
          have hvj_cx: "vxw j - ?cxw = -t * (vxw(Suc j mod ?nw) - vxw j)"
            using hcx_eq by (by100 algebra)
          have hvj_cy: "vyw j - ?cyw = -t * (vyw(Suc j mod ?nw) - vyw j)"
            using hcy_eq by (by100 algebra)
          have hvs_cx: "vxw(Suc j mod ?nw) - ?cxw = (1-t) * (vxw(Suc j mod ?nw) - vxw j)"
            using hcx_eq by (by100 algebra)
          have hvs_cy: "vyw(Suc j mod ?nw) - ?cyw = (1-t) * (vyw(Suc j mod ?nw) - vyw j)"
            using hcy_eq by (by100 algebra)
          have "(vxw j - ?cxw) * (vyw(Suc j mod ?nw) - ?cyw) -
                (vyw j - ?cyw) * (vxw(Suc j mod ?nw) - ?cxw)
              = (-t * (vxw(Suc j mod ?nw) - vxw j)) * ((1-t) * (vyw(Suc j mod ?nw) - vyw j)) -
                (-t * (vyw(Suc j mod ?nw) - vyw j)) * ((1-t) * (vxw(Suc j mod ?nw) - vxw j))"
            using hvj_cx hvj_cy hvs_cx hvs_cy by (by100 simp)
          also have "\<dots> = 0" by (by100 algebra)
          finally show False using hcr' by (by100 linarith)
        qed
      qed
      \<comment> \<open>General signed area: det(v\\_m-v\\_1, v\\_n-v\\_1) > 0 for 2 \\<le> m < n < ne.\<close>
      have hdet_general: "\<forall>m n. 2 \<le> m \<longrightarrow> m < n \<longrightarrow> n < ?ne \<longrightarrow>
        (vxe m - vxe 1) * (vye n - vye 1) - (vye m - vye 1) * (vxe n - vxe 1) > 0"
        using hfan_det_e .
      \<comment> \<open>Helper: det(v\\_k - v\\_1, v\\_0 - v\\_1) > 0 for k \\<in> {2,...,ne-1}.\<close>
      have hdet_from_v1: "\<forall>k. 2 \<le> k \<longrightarrow> k < ?ne \<longrightarrow>
        (vxe k - vxe 1) * (vye 0 - vye 1) - (vye k - vye 1) * (vxe 0 - vxe 1) > 0"
      proof (intro allI impI)
        fix k assume hk2: "(2::nat) \<le> k" and hk_lt: "k < ?ne"
        have h0_lt: "(0::nat) < ?ne" using hlen hne_eq by (by100 linarith)
        have hk_ne0: "k \<noteq> 0" using hk2 by (by100 linarith)
        have hk_ne1: "k \<noteq> Suc 0 mod ?ne"
        proof -
          have "Suc 0 mod ?ne = 1" using hlen hne_eq by (by100 simp)
          thus ?thesis using hk2 by (by100 linarith)
        qed
        from hC11_e[rule_format, OF h0_lt hk_lt hk_ne0 hk_ne1]
        have hC11_at0: "(vxe k-vxe 0)*(vye(Suc 0 mod ?ne)-vye 0)-(vye k-vye 0)*(vxe(Suc 0 mod ?ne)-vxe 0) < 0" .
        have hsuc0: "Suc 0 mod ?ne = 1" using hlen hne_eq by (by100 simp)
        have "(vxe k - vxe 1) * (vye 0 - vye 1) - (vye k - vye 1) * (vxe 0 - vxe 1)
          = -((vxe k-vxe 0)*(vye 1-vye 0)-(vye k-vye 0)*(vxe 1-vxe 0))"
          by (by100 algebra)
        also have "\<dots> > 0"
        proof -
          from hC11_at0 hsuc0 have "(vxe k-vxe 0)*(vye 1-vye 0)-(vye k-vye 0)*(vxe 1-vxe 0) < 0"
            by (by100 simp)
          thus ?thesis by (by100 linarith)
        qed
        finally show "(vxe k - vxe 1) * (vye 0 - vye 1) - (vye k - vye 1) * (vxe 0 - vxe 1) > 0" .
      qed
      \<comment> \<open>Key helper: fan from v\\_1 covers P\\_e.\<close>
      have hfan_cover: "\<forall>p\<in>P_e. p = (vxe 1, vye 1) \<or> (\<exists>j<?nw. in_sector j p)"
      proof (intro ballI)
        fix p assume hp: "p \<in> P_e"
        show "p = (vxe 1, vye 1) \<or> (\<exists>j<?nw. in_sector j p)"
        proof (cases "p = (vxe 1, vye 1)")
          case True thus ?thesis by (by100 blast)
        next
          case False
          \<comment> \<open>cross\\_v1(k, p) = \\<Sum>i<ne. \\<lambda>\\_i * det(v\\_k-v\\_1, v\\_i-v\\_1) for p = \\<Sum> \\<lambda>\\_i v\\_i.\<close>
          from hp obtain coeffs where hcoeffs: "(\<forall>i<?ne. coeffs i \<ge> 0)"
            "(\<Sum>i<?ne. coeffs i) = 1" "fst p = (\<Sum>i<?ne. coeffs i * vxe i)" "snd p = (\<Sum>i<?ne. coeffs i * vye i)"
            using hC5_e by (by100 auto)
          \<comment> \<open>cross\\_v1(k, p) = \\<Sum> \\<lambda>\\_i * cross\\_v1(k, v\\_i) by linearity.\<close>
          have hcross_sum: "\<And>k. cross_v1 k p = (\<Sum>i<?ne. coeffs i * cross_v1 k (vxe i, vye i))"
          proof -
            fix k
            have "cross_v1 k p = (vxe k - vxe 1) * (snd p - vye 1) - (vye k - vye 1) * (fst p - vxe 1)"
              unfolding cross_v1_def by simp
            also have "snd p = (\<Sum>i<?ne. coeffs i * vye i)" using hcoeffs(4) .
            also have "fst p = (\<Sum>i<?ne. coeffs i * vxe i)" using hcoeffs(3) .
            finally have "cross_v1 k p =
              (vxe k - vxe 1) * ((\<Sum>i<?ne. coeffs i * vye i) - vye 1) -
              (vye k - vye 1) * ((\<Sum>i<?ne. coeffs i * vxe i) - vxe 1)" by simp
            also have "\<dots> = (\<Sum>i<?ne. coeffs i * ((vxe k - vxe 1) * (vye i - vye 1) - (vye k - vye 1) * (vxe i - vxe 1)))"
            proof -
              have hsy: "(\<Sum>i<?ne. coeffs i * vye i) - vye 1 = (\<Sum>i<?ne. coeffs i * (vye i - vye 1))"
              proof -
                have "(\<Sum>i<?ne. coeffs i * (vye i - vye 1)) = (\<Sum>i<?ne. (coeffs i * vye i - coeffs i * vye 1))"
                  by (rule sum.cong) (simp_all add: algebra_simps)
                also have "\<dots> = (\<Sum>i<?ne. coeffs i * vye i) - (\<Sum>i<?ne. coeffs i * vye 1)"
                  by (rule sum_subtractf)
                also have "(\<Sum>i<?ne. coeffs i * vye 1) = vye 1"
                proof -
                  have "(\<Sum>i<?ne. coeffs i * vye 1) = (\<Sum>i<?ne. coeffs i) * vye 1"
                    using sum_distrib_right[symmetric, of coeffs "vye 1" "{..<?ne}"]
                      sum_distrib_right[symmetric, of coeffs "vxe 1" "{..<?ne}"]
                    by (by100 simp)
                  also have "\<dots> = vye 1" using hcoeffs(2) by simp
                  finally show ?thesis .
                qed
                finally show ?thesis by simp
              qed
              have hsx: "(\<Sum>i<?ne. coeffs i * vxe i) - vxe 1 = (\<Sum>i<?ne. coeffs i * (vxe i - vxe 1))"
              proof -
                have "(\<Sum>i<?ne. coeffs i * (vxe i - vxe 1)) = (\<Sum>i<?ne. (coeffs i * vxe i - coeffs i * vxe 1))"
                  by (rule sum.cong) (simp_all add: algebra_simps)
                also have "\<dots> = (\<Sum>i<?ne. coeffs i * vxe i) - (\<Sum>i<?ne. coeffs i * vxe 1)"
                  by (rule sum_subtractf)
                also have "(\<Sum>i<?ne. coeffs i * vxe 1) = vxe 1"
                proof -
                  have "(\<Sum>i<?ne. coeffs i * vxe 1) = (\<Sum>i<?ne. coeffs i) * vxe 1"
                    using sum_distrib_right[symmetric, of coeffs "vye 1" "{..<?ne}"]
                      sum_distrib_right[symmetric, of coeffs "vxe 1" "{..<?ne}"]
                    by (by100 simp)
                  also have "\<dots> = vxe 1" using hcoeffs(2) by simp
                  finally show ?thesis .
                qed
                finally show ?thesis by simp
              qed
              have "(vxe k - vxe 1) * (\<Sum>i<?ne. coeffs i * (vye i - vye 1))
                = (\<Sum>i<?ne. (vxe k - vxe 1) * (coeffs i * (vye i - vye 1)))"
                by (rule sum_distrib_left)
              have "(vye k - vye 1) * (\<Sum>i<?ne. coeffs i * (vxe i - vxe 1))
                = (\<Sum>i<?ne. (vye k - vye 1) * (coeffs i * (vxe i - vxe 1)))"
                by (rule sum_distrib_left)
              have hlhs: "(vxe k - vxe 1) * ((\<Sum>i<?ne. coeffs i * vye i) - vye 1) -
                (vye k - vye 1) * ((\<Sum>i<?ne. coeffs i * vxe i) - vxe 1)
                = (\<Sum>i<?ne. (vxe k - vxe 1) * (coeffs i * (vye i - vye 1))) -
                  (\<Sum>i<?ne. (vye k - vye 1) * (coeffs i * (vxe i - vxe 1)))"
                using hsy hsx
                  \<open>(vxe k - vxe 1) * (\<Sum>i<?ne. coeffs i * (vye i - vye 1))
                    = (\<Sum>i<?ne. (vxe k - vxe 1) * (coeffs i * (vye i - vye 1)))\<close>
                  \<open>(vye k - vye 1) * (\<Sum>i<?ne. coeffs i * (vxe i - vxe 1))
                    = (\<Sum>i<?ne. (vye k - vye 1) * (coeffs i * (vxe i - vxe 1)))\<close>
                by simp
              have "(\<Sum>i<?ne. (vxe k - vxe 1) * (coeffs i * (vye i - vye 1))) -
                (\<Sum>i<?ne. (vye k - vye 1) * (coeffs i * (vxe i - vxe 1)))
                = (\<Sum>i<?ne. ((vxe k - vxe 1) * (coeffs i * (vye i - vye 1)) -
                             (vye k - vye 1) * (coeffs i * (vxe i - vxe 1))))"
                using sum_subtractf[of "\<lambda>i. (vxe k-vxe 1)*(coeffs i*(vye i-vye 1))"
                  "\<lambda>i. (vye k-vye 1)*(coeffs i*(vxe i-vxe 1))" "{..<?ne}"] by (by5000 simp)
              also have "\<dots> = (\<Sum>i<?ne. coeffs i * ((vxe k - vxe 1) * (vye i - vye 1) - (vye k - vye 1) * (vxe i - vxe 1)))"
              proof -
                have "\<And>i. (vxe k - vxe 1) * (coeffs i * (vye i - vye 1)) -
                  (vye k - vye 1) * (coeffs i * (vxe i - vxe 1)) =
                  coeffs i * ((vxe k - vxe 1) * (vye i - vye 1) - (vye k - vye 1) * (vxe i - vxe 1))"
                  by (by100 algebra)
                thus ?thesis by simp
              qed
              finally show ?thesis using hlhs by simp
            qed
            also have "\<dots> = (\<Sum>i<?ne. coeffs i * cross_v1 k (vxe i, vye i))"
              unfolding cross_v1_def by simp
            finally show "cross_v1 k p = (\<Sum>i<?ne. coeffs i * cross_v1 k (vxe i, vye i))" .
          qed
          \<comment> \<open>Step 1: cross\\_v1(2, p) \\<ge> 0.\<close>
          have hcross2_ge: "cross_v1 2 p \<ge> 0"
          proof -
            have "\<forall>i<?ne. coeffs i * cross_v1 2 (vxe i, vye i) \<ge> 0"
            proof (intro allI impI)
              fix i assume hi: "i < ?ne"
              show "coeffs i * cross_v1 2 (vxe i, vye i) \<ge> 0"
              proof (cases "i = 1 \<or> i = 2")
                case True
                hence "cross_v1 2 (vxe i, vye i) = 0" unfolding cross_v1_def
                  by (elim disjE) (simp add: algebra_simps)+
                thus ?thesis by simp
              next
                case False hence "i \<noteq> 1" "i \<noteq> 2" by auto
                have hcv_pos: "cross_v1 2 (vxe i, vye i) > 0"
                proof (cases "i = 0")
                  case True
                  from hdet_from_v1[rule_format, of 2]
                  have "(vxe 2-vxe 1)*(vye 0-vye 1)-(vye 2-vye 1)*(vxe 0-vxe 1) > 0"
                    using hlen hne_eq by linarith
                  thus ?thesis unfolding cross_v1_def using True by simp
                next
                  case False hence "i > 2" using \<open>i \<noteq> 1\<close> \<open>i \<noteq> 2\<close> by linarith
                  from hdet_general[rule_format, of 2 i]
                  have "(vxe 2-vxe 1)*(vye i-vye 1)-(vye 2-vye 1)*(vxe i-vxe 1) > 0"
                    using \<open>i > 2\<close> hi by linarith
                  thus ?thesis unfolding cross_v1_def by simp
                qed
                thus ?thesis using hcoeffs(1)[rule_format, OF hi] by (simp add: mult_nonneg_nonneg)
              qed
            qed
            have "(\<Sum>i<?ne. coeffs i * cross_v1 2 (vxe i, vye i)) \<ge> 0"
              by (intro sum_nonneg) (use \<open>\<forall>i<?ne. coeffs i * cross_v1 2 (vxe i, vye i) \<ge> 0\<close> in \<open>by100 blast\<close>)
            thus ?thesis using hcross_sum[of 2] by linarith
          qed
          \<comment> \<open>Step 2: cross\\_v1(0, p) \\<le> 0 (using hdet\\_from\\_v1 reversed: det(v\\_0-v\\_1, v\\_i-v\\_1) < 0 for i \\<ge> 2).\<close>
          have hcross0_le: "cross_v1 0 p \<le> 0"
          proof -
            have "\<forall>i<?ne. coeffs i * cross_v1 0 (vxe i, vye i) \<le> 0"
            proof (intro allI impI)
              fix i assume hi: "i < ?ne"
              show "coeffs i * cross_v1 0 (vxe i, vye i) \<le> 0"
              proof (cases "i \<le> 1")
                case True
                hence "cross_v1 0 (vxe i, vye i) = 0"
                proof (cases "i = 0")
                  case True thus ?thesis unfolding cross_v1_def by simp
                next
                  case False hence "i = 1" using True by linarith
                  thus ?thesis unfolding cross_v1_def by simp
                qed
                thus ?thesis by simp
              next
                case False hence "i \<ge> 2" by linarith
                from hdet_from_v1[rule_format, OF \<open>i \<ge> 2\<close> hi]
                have "(vxe i-vxe 1)*(vye 0-vye 1)-(vye i-vye 1)*(vxe 0-vxe 1) > 0" .
                have "(vxe 0-vxe 1)*(vye i-vye 1)-(vye 0-vye 1)*(vxe i-vxe 1) =
                  -((vxe i-vxe 1)*(vye 0-vye 1)-(vye i-vye 1)*(vxe 0-vxe 1))"
                  by (by100 algebra)
                hence "(vxe 0-vxe 1)*(vye i-vye 1)-(vye 0-vye 1)*(vxe i-vxe 1) < 0"
                  using \<open>(vxe i-vxe 1)*(vye 0-vye 1)-(vye i-vye 1)*(vxe 0-vxe 1) > 0\<close> by linarith
                hence "cross_v1 0 (vxe i, vye i) < 0"
                  unfolding cross_v1_def by simp
                thus ?thesis using hcoeffs(1)[rule_format, OF hi]
                  by (simp add: mult_nonneg_nonpos)
              qed
            qed
            have "(\<Sum>i<?ne. coeffs i * cross_v1 0 (vxe i, vye i)) \<le> 0"
              by (intro sum_nonpos) (use \<open>\<forall>i<?ne. coeffs i * cross_v1 0 (vxe i, vye i) \<le> 0\<close> in \<open>by100 blast\<close>)
            thus ?thesis using hcross_sum[of 0] by linarith
          qed
          \<comment> \<open>Step 3: discrete IVT. Sequence from cross\\_v1(2,p)\\<ge>0 to cross\\_v1(0,p)\\<le>0.\<close>
          have "\<exists>j<?nw. cross_v1 (j+2) p \<ge> 0 \<and> cross_v1 (Suc(j+2) mod ?ne) p \<le> 0"
          proof -
            \<comment> \<open>Define f(j) = cross\\_v1(j+2, p) for j = 0, ..., nw.\<close>
            define f where "f j = cross_v1 (j+2) p" for j
            have hf0: "f 0 \<ge> 0" using hcross2_ge unfolding f_def
              by (simp add: numeral_2_eq_2)
            have "Suc(?nw-1+2) mod ?ne = Suc (?nw+1) mod ?ne" using hnw_pos by simp
            also have "\<dots> = (?nw + 2) mod ?ne" by simp
            also have "\<dots> = ?ne mod ?ne" using hne_eq by simp
            also have "\<dots> = 0" by simp
            finally have hmod_nw: "Suc((?nw-1)+2) mod ?ne = 0" .
            have hfnw: "cross_v1 (Suc((?nw-1)+2) mod ?ne) p \<le> 0"
              using hcross0_le hmod_nw by simp
            \<comment> \<open>Find the sign change by taking the largest j with f(j) \\<ge> 0.\<close>
            \<comment> \<open>Discrete IVT by strong induction on nw.\<close>
            show ?thesis
            proof (cases "f (?nw - 1) \<ge> 0")
              case True \<comment> \<open>Last sector boundary \\<ge> 0: j = nw-1 works.\<close>
              have "?nw-1 < ?nw" using hnw_pos by linarith
              moreover have "cross_v1 ((?nw-1)+2) p \<ge> 0" using True unfolding f_def .
              moreover have "cross_v1 (Suc((?nw-1)+2) mod ?ne) p \<le> 0" using hfnw .
              ultimately show ?thesis by (by100 blast)
            next
              case False hence hfnw1_neg: "f (?nw - 1) < 0" by linarith
              \<comment> \<open>f(0)\\<ge>0 and f(nw-1)<0. Find the sign change.\<close>
              have "\<exists>j. j < ?nw - 1 \<and> f j \<ge> 0 \<and> f (Suc j) < 0"
              proof (rule ccontr)
                assume hno: "\<not>(\<exists>j. j < ?nw - 1 \<and> f j \<ge> 0 \<and> f (Suc j) < 0)"
                hence hall: "\<forall>j<?nw - 1. f j \<ge> 0 \<longrightarrow> f (Suc j) \<ge> 0" by force
                have "\<forall>j<?nw. f j \<ge> 0"
                proof (intro allI impI)
                  fix j assume "j < ?nw"
                  thus "f j \<ge> 0"
                  proof (induct j)
                    case 0 thus ?case using hf0 by simp
                  next
                    case (Suc j') hence "j' < ?nw - 1" by linarith
                    moreover have "f j' \<ge> 0" using Suc by linarith
                    ultimately show ?case using hall by blast
                  qed
                qed
                hence "f (?nw - 1) \<ge> 0"
                proof -
                  have "?nw - 1 < ?nw" using hnw_pos by linarith
                  with \<open>\<forall>j<?nw. f j \<ge> 0\<close> show ?thesis by blast
                qed
                thus False using hfnw1_neg by linarith
              qed
              then obtain j where hj: "j < ?nw - 1" "f j \<ge> 0" "f (Suc j) < 0" by blast
              have hj_lt: "j < ?nw" using hj(1) by linarith
              have "cross_v1 (j+2) p \<ge> 0" using hj(2) unfolding f_def .
              moreover have "cross_v1 (Suc(j+2) mod ?ne) p \<le> 0"
              proof -
                have "j + 3 < ?ne" using hj(1) hne_eq by linarith
                hence "Suc(j+2) mod ?ne = j+3" by simp
                also have "j+3 = Suc j + 2" by simp
                finally have "Suc(j+2) mod ?ne = Suc j + 2" .
                hence "cross_v1 (Suc(j+2) mod ?ne) p = f (Suc j)" unfolding f_def by simp
                thus ?thesis using hj(3) by linarith
              qed
              ultimately show ?thesis using hj_lt by (by100 blast)
            qed
          qed
          thus ?thesis unfolding in_sector_def by (by100 blast)
        qed
      qed
      \<comment> \<open>Key helper: sector determinants are positive (non-degenerate triangles).\<close>
      have hdet_pos: "\<forall>j<?nw.
        let ex = vxe(j+2) - vxe 1; ey = vye(j+2) - vye 1;
            fx = vxe(Suc(j+2) mod ?ne) - vxe 1; fy = vye(Suc(j+2) mod ?ne) - vye 1
        in ex*fy - ey*fx > 0"
      proof (intro allI impI)
        fix j assume hj: "j < ?nw"
        let ?i = "j + 2"
        let ?si = "Suc ?i mod ?ne"
        have hi: "?i < ?ne" using hj hne_eq by (by100 linarith)
        have h1: "(1::nat) < ?ne" using hlen hne_eq by (by100 linarith)
        have h1_ne_i: "(1::nat) \<noteq> ?i" by (by100 simp)
        have h1_ne_si: "(1::nat) \<noteq> ?si"
        proof (cases "Suc ?i < ?ne")
          case True hence "?si = Suc ?i" by (by100 simp)
          thus ?thesis using hi by (by100 linarith)
        next
          case False hence "Suc ?i = ?ne" using hi by (by100 linarith)
          hence "?si = 0" by (by100 simp)
          thus ?thesis by (by100 simp)
        qed
        \<comment> \<open>From C11\\_e at i=j+2, k=1: cross product from edge j+2 gives v\\_1 is strictly inside.\<close>
        from hC11_e[rule_format, OF hi h1 h1_ne_i h1_ne_si]
        have hC11_inst: "(vxe 1-vxe ?i)*(vye ?si-vye ?i)-(vye 1-vye ?i)*(vxe ?si-vxe ?i) < 0" .
        \<comment> \<open>The determinant det(v\\_{j+2}-v\\_1, v\\_{j+3}-v\\_1) = -(C11 cross product).
           Algebraically: let a = vxe(j+2)-vxe 1, b = vye(j+2)-vye 1,
             c = vxe(si)-vxe(j+2), d = vye(si)-vye(j+2).
           C11 says: (-a)*d - (-b)*c = bc - ad < 0, so ad - bc > 0.
           det = a*(b+d) - b*(a+c) = ad - bc.\<close>
        show "let ex = vxe ?i - vxe 1; ey = vye ?i - vye 1;
                  fx = vxe ?si - vxe 1; fy = vye ?si - vye 1
              in ex*fy - ey*fx > 0"
        proof -
          let ?ex = "vxe ?i - vxe 1"
          let ?ey = "vye ?i - vye 1"
          let ?fx = "vxe ?si - vxe 1"
          let ?fy = "vye ?si - vye 1"
          have "?ex*?fy - ?ey*?fx = -((vxe 1-vxe ?i)*(vye ?si-vye ?i)-(vye 1-vye ?i)*(vxe ?si-vxe ?i))"
            by (by100 algebra)
          also have "\<dots> > 0" using hC11_inst by (by100 linarith)
          finally show ?thesis by (by100 simp)
        qed
      qed
      \<comment> \<open>Key helper: phi on spur edge 0 gives the arc from u\\_0 to centroid.\<close>
      \<comment> \<open>Helper: phi\\_fn at known sector. When p \\<noteq> v\\_1 and LEAST = j, the value is determined.\<close>
      have hphi_fn_sector: "\<And>p j. p \<noteq> (vxe 1, vye 1) \<Longrightarrow>
        (LEAST j'. j' < ?nw \<and> in_sector j' p) = j \<Longrightarrow>
        phi_fn p = (let ex = vxe(j+2) - vxe 1; ey = vye(j+2) - vye 1;
                        fx = vxe(Suc(j+2) mod ?ne) - vxe 1; fy = vye(Suc(j+2) mod ?ne) - vye 1;
                        det = ex*fy - ey*fx;
                        dx = fst p - vxe 1; dy = snd p - vye 1;
                        s = (fy*dx - fx*dy) / det;
                        t_par = (ex*dy - ey*dx) / det in
                    ((1-s-t_par)*?cxw + s*vxw j + t_par*vxw(Suc j mod ?nw),
                     (1-s-t_par)*?cyw + s*vyw j + t_par*vyw(Suc j mod ?nw)))"
        unfolding phi_fn_def Let_def by (by100 simp)
      \<comment> \<open>Specialized version: phi\\_fn at a specific pair (a,b) with dx=a-vxe 1, dy=b-vye 1.\<close>
      have hphi_fn_at_pair: "\<And>a b j. (a, b) \<noteq> (vxe 1, vye 1) \<Longrightarrow>
        (LEAST j'. j' < ?nw \<and> in_sector j' (a, b)) = j \<Longrightarrow>
        phi_fn (a, b) = (let ex = vxe(j+2)-vxe 1; ey = vye(j+2)-vye 1;
                             fx = vxe(Suc(j+2) mod ?ne)-vxe 1; fy = vye(Suc(j+2) mod ?ne)-vye 1;
                             det = ex*fy-ey*fx;
                             dx = a-vxe 1; dy = b-vye 1;
                             s = (fy*dx-fx*dy)/det; t_par = (ex*dy-ey*dx)/det in
                         ((1-s-t_par)*?cxw + s*vxw j + t_par*vxw(Suc j mod ?nw),
                          (1-s-t_par)*?cyw + s*vyw j + t_par*vyw(Suc j mod ?nw)))"
        unfolding phi_fn_def Let_def by (by100 simp)
      \<comment> \<open>Key helper: phi on spur edge 0 gives the arc from u\\_0 to centroid.\<close>
      have hphi_on_spur0: "\<forall>t\<in>I_set.
        phi_fn (edge_pt_e 0 t) = ((1-t)*vxw 0 + t*?cxw, (1-t)*vyw 0 + t*?cyw)"
      proof (intro ballI)
        fix t assume ht: "t \<in> I_set"
        show "phi_fn (edge_pt_e 0 t) = ((1-t)*vxw 0 + t*?cxw, (1-t)*vyw 0 + t*?cyw)"
        proof (cases "t = 1")
          case True
          have "Suc 0 mod ?ne = 1" using hlen hne_eq by (by100 simp)
          hence "edge_pt_e 0 1 = ((1-1)*vxe 0 + 1*vxe 1, (1-1)*vye 0 + 1*vye 1)"
            unfolding edge_pt_e_def by (by100 simp)
          hence "edge_pt_e 0 1 = (vxe 1, vye 1)" by (by100 simp)
          hence hpt_v1: "edge_pt_e 0 t = (vxe 1, vye 1)" using True by (by100 simp)
          hence "phi_fn (edge_pt_e 0 t) = (?cxw, ?cyw)" unfolding phi_fn_def using hpt_v1 by (by100 simp)
          moreover have "((1-t)*vxw 0 + t*?cxw, (1-t)*vyw 0 + t*?cyw) = (?cxw, ?cyw)"
            using True by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        next
          case False
          \<comment> \<open>t < 1, so edge\\_pt\\_e(0, t) \\<noteq> v\\_1. The LEAST sector with in\\_sector gives nw-1.
             Barycentric computation: s = 0, t\\_par = 1-t (weight on v\\_0).
             Affine map: (1-(0)-(1-t))*c\\_w + 0*u\\_{nw-1} + (1-t)*u\\_0 = t*c\\_w + (1-t)*u\\_0.\<close>
          have ht_lt1: "t < 1" using False ht unfolding top1_unit_interval_def by (by100 auto)
          have hp_ne_v1: "edge_pt_e 0 t \<noteq> (vxe 1, vye 1)"
          proof
            assume "edge_pt_e 0 t = (vxe 1, vye 1)"
            hence h_eq_x: "(1-t)*vxe 0 + t*vxe(Suc 0 mod ?ne) = vxe 1"
              and h_eq_y: "(1-t)*vye 0 + t*vye(Suc 0 mod ?ne) = vye 1"
              unfolding edge_pt_e_def by (by100 simp)+
            have hsuc0: "Suc 0 mod ?ne = 1" using hlen hne_eq by (by100 simp)
            from h_eq_x hsuc0 have hvx: "(1-t)*vxe 0 + t*vxe 1 = vxe 1" by (by100 simp)
            hence hvx': "(1-t)*(vxe 0 - vxe 1) = 0"
            proof -
              from hvx have "(1-t)*vxe 0 = vxe 1 - t*vxe 1" by (by100 linarith)
              hence "(1-t)*vxe 0 = (1-t)*vxe 1" by (by100 algebra)
              thus ?thesis by (by100 algebra)
            qed
            from h_eq_y hsuc0 have hvy: "(1-t)*vye 0 + t*vye 1 = vye 1" by (by100 simp)
            hence hvy': "(1-t)*(vye 0 - vye 1) = 0"
            proof -
              from hvy have "(1-t)*vye 0 = vye 1 - t*vye 1" by (by100 linarith)
              hence "(1-t)*vye 0 = (1-t)*vye 1" by (by100 algebra)
              thus ?thesis by (by100 algebra)
            qed
            from hvx' hvy'
            have "(1-t) = 0 \<or> (vxe 0 = vxe 1 \<and> vye 0 = vye 1)" by (by100 algebra)
            thus False
            proof (elim disjE)
              assume "1-t = 0" thus False using ht_lt1 by (by100 simp)
            next
              assume "vxe 0 = vxe 1 \<and> vye 0 = vye 1"
              hence "(vxe 0, vye 0) = (vxe 1, vye 1)" by (by100 simp)
              have "(0::nat) < ?ne" using hlen hne_eq by (by100 linarith)
              moreover have "(1::nat) < ?ne" using hlen hne_eq by (by100 linarith)
              moreover have "(0::nat) \<noteq> 1" by (by100 simp)
              ultimately have "(vxe 0, vye 0) \<noteq> (vxe 1, vye 1)"
                using hC3_e by (by100 blast)
              thus False using \<open>(vxe 0, vye 0) = (vxe 1, vye 1)\<close> by (by100 simp)
            qed
          qed
          \<comment> \<open>The edge point is in sector nw-1 of the fan.\<close>
          have hin_sec: "in_sector (?nw - 1) (edge_pt_e 0 t)"
          proof -
            have hnw1: "?nw - 1 < ?nw" using hnw_pos by (by100 simp)
            have hnw1_plus2: "(?nw - 1) + 2 = ?nw + 1" using hnw_pos by (by100 simp)
            have hne_rel: "?ne = ?nw + 2" using hne_eq by (by100 simp)
            have hsuc0: "Suc 0 mod ?ne = 1" using hlen hne_eq by (by100 simp)
            \<comment> \<open>Suc((?nw-1)+2) mod ne = Suc(nw+1) mod (nw+2) = (nw+2) mod (nw+2) = 0.\<close>
            have hsuc_nw1: "Suc((?nw - 1) + 2) mod ?ne = 0"
            proof -
              have "Suc((?nw-1)+2) = ?nw + 2" using hnw_pos by (by100 simp)
              also have "\<dots> = ?ne" using hne_rel by (by100 simp)
              finally show ?thesis by (by100 simp)
            qed
            \<comment> \<open>edge\\_pt\\_e(0, t) coordinates.\<close>
            have hpt_x: "fst (edge_pt_e 0 t) = (1-t)*vxe 0 + t*vxe 1"
              unfolding edge_pt_e_def using hsuc0 by (by100 simp)
            have hpt_y: "snd (edge_pt_e 0 t) = (1-t)*vye 0 + t*vye 1"
              unfolding edge_pt_e_def using hsuc0 by (by100 simp)
            \<comment> \<open>Condition 1: cross\\_v1((?nw-1)+2, p) = cross\\_v1(nw+1, p) \\<ge> 0.
               This equals (1-t) * det(sector nw-1) \\<ge> 0 since det > 0 and 1-t \\<ge> 0.\<close>
            have hcross1: "cross_v1 ((?nw-1)+2) (edge_pt_e 0 t) \<ge> 0"
            proof -
              have "cross_v1 ((?nw-1)+2) (edge_pt_e 0 t) =
                (vxe((?nw-1)+2) - vxe 1) * ((1-t)*vye 0 + t*vye 1 - vye 1) -
                (vye((?nw-1)+2) - vye 1) * ((1-t)*vxe 0 + t*vxe 1 - vxe 1)"
                unfolding cross_v1_def using hpt_x hpt_y by (by100 simp)
              also have "\<dots> = (vxe(?nw+1) - vxe 1) * ((1-t)*(vye 0 - vye 1)) -
                              (vye(?nw+1) - vye 1) * ((1-t)*(vxe 0 - vxe 1))"
              proof -
                have hsubst: "(?nw-1)+2 = ?nw+1" using hnw_pos by (by100 simp)
                show ?thesis unfolding hsubst by (by100 algebra)
              qed
              also have "\<dots> = (1-t) * ((vxe(?nw+1) - vxe 1) * (vye 0 - vye 1) -
                              (vye(?nw+1) - vye 1) * (vxe 0 - vxe 1))"
                by (by100 algebra)
              finally have hcv: "cross_v1 ((?nw-1)+2) (edge_pt_e 0 t) =
                (1-t) * ((vxe(?nw+1) - vxe 1) * (vye 0 - vye 1) -
                         (vye(?nw+1) - vye 1) * (vxe 0 - vxe 1))" .
              \<comment> \<open>The factor in brackets is the sector nw-1 determinant, which is > 0.\<close>
              from hdet_pos[rule_format, OF hnw1]
              have hdet_nw1: "(vxe((?nw-1)+2) - vxe 1) * (vye(Suc((?nw-1)+2) mod ?ne) - vye 1) -
                (vye((?nw-1)+2) - vye 1) * (vxe(Suc((?nw-1)+2) mod ?ne) - vxe 1) > 0"
                by (by100 simp)
              have hdet_val: "(vxe(?nw+1) - vxe 1) * (vye 0 - vye 1) -
                     (vye(?nw+1) - vye 1) * (vxe 0 - vxe 1) > 0"
              proof -
                have "(?nw-1)+2 = ?nw+1" using hnw_pos by (by100 simp)
                moreover have "Suc((?nw-1)+2) mod ?ne = 0" using hsuc_nw1 .
                ultimately show ?thesis using hdet_nw1 by (by100 simp)
              qed
              moreover have "(1-t) \<ge> 0" using ht unfolding top1_unit_interval_def by (by100 auto)
              ultimately have h_factor_pos: "(vxe(?nw+1) - vxe 1) * (vye 0 - vye 1) -
                     (vye(?nw+1) - vye 1) * (vxe 0 - vxe 1) > 0"
                and h1mt: "(1-t) \<ge> 0" by (by100 simp)+
              have "(1-t) * ((vxe(?nw+1) - vxe 1) * (vye 0 - vye 1) -
                     (vye(?nw+1) - vye 1) * (vxe 0 - vxe 1)) \<ge> 0"
              proof -
                have "0 \<le> (1 - t)" and "0 \<le> ((vxe(?nw+1) - vxe 1) * (vye 0 - vye 1) -
                     (vye(?nw+1) - vye 1) * (vxe 0 - vxe 1))"
                  using h1mt h_factor_pos by (by100 linarith)+
                from mult_nonneg_nonneg[OF this]
                show ?thesis .
              qed
              thus ?thesis using hcv by (by100 linarith)
            qed
            \<comment> \<open>Condition 2: cross\\_v1(Suc((?nw-1)+2) mod ne, p) = cross\\_v1(0, p) \\<le> 0.
               This equals (1-t)*cross(v\\_0-v\\_1, v\\_0-v\\_1) = 0.\<close>
            have hcross2: "cross_v1 (Suc((?nw-1)+2) mod ?ne) (edge_pt_e 0 t) \<le> 0"
            proof -
              have "cross_v1 0 (edge_pt_e 0 t) =
                (vxe 0 - vxe 1) * ((1-t)*vye 0 + t*vye 1 - vye 1) -
                (vye 0 - vye 1) * ((1-t)*vxe 0 + t*vxe 1 - vxe 1)"
                unfolding cross_v1_def using hpt_x hpt_y by (by100 simp)
              also have "\<dots> = (vxe 0 - vxe 1) * ((1-t)*(vye 0 - vye 1)) -
                              (vye 0 - vye 1) * ((1-t)*(vxe 0 - vxe 1))"
                by (by100 algebra)
              also have "\<dots> = 0" by (by100 algebra)
              finally have "cross_v1 0 (edge_pt_e 0 t) = 0" .
              thus ?thesis using hsuc_nw1 by (by100 simp)
            qed
            show ?thesis unfolding in_sector_def using hcross1 hcross2 by (by100 simp)
          qed
          \<comment> \<open>The LEAST j with in\\_sector selects some j \\<le> nw-1.\<close>
          obtain j_sel where hj_sel: "j_sel = (LEAST j. j < ?nw \<and> in_sector j (edge_pt_e 0 t))"
            by (by100 blast)
          have hj_sel_valid: "j_sel < ?nw \<and> in_sector j_sel (edge_pt_e 0 t)"
          proof -
            have "\<exists>j. j < ?nw \<and> in_sector j (edge_pt_e 0 t)"
            proof -
              have "?nw - 1 < ?nw \<and> in_sector (?nw - 1) (edge_pt_e 0 t)"
                using hin_sec hnw_pos by (by100 linarith)
              thus ?thesis by (by100 blast)
            qed
            from LeastI_ex[OF this]
            show ?thesis unfolding hj_sel[symmetric] .
          qed
          \<comment> \<open>Regardless of which sector j\\_sel is chosen, the affine map on the edge point
             (which lies on the boundary v\\_0->v\\_1) gives the same result.
             This is because on boundary edges shared between sectors, the affine maps agree.\<close>
          \<comment> \<open>Computation: LEAST picks nw-1 (or any valid j). The barycentric formula gives s=0, t\\_par=1-t.\<close>
          \<comment> \<open>Step 1: phi\\_fn uses the else branch (since p \\<noteq> v\\_1).\<close>
          \<comment> \<open>Step 1: Show LEAST = nw-1 by ruling out all j < nw-1.\<close>
          have hno_smaller: "\<forall>j'<?nw - 1. \<not> in_sector j' (edge_pt_e 0 t)"
          proof (intro allI impI)
            fix j' assume hj'_lt: "j' < ?nw - 1"
            hence hj'3_lt: "j' + 3 < ?ne" using hne_eq by (by100 linarith)
            hence hj'3_ge: "j' + 3 \<ge> 2" by (by100 simp)
            have hmod_eq: "Suc(j'+2) mod ?ne = j' + 3"
            proof -
              have "j' + 3 < ?ne" using hj'3_lt .
              thus ?thesis by (by100 simp)
            qed
            \<comment> \<open>cross\\_v1(j'+3, p) = (1-t) * det(v\\_{j'+3}-v\\_1, v\\_0-v\\_1) > 0.\<close>
            from hdet_from_v1[rule_format, OF hj'3_ge hj'3_lt]
            have hdet_pos': "(vxe(j'+3) - vxe 1) * (vye 0 - vye 1) -
              (vye(j'+3) - vye 1) * (vxe 0 - vxe 1) > 0" .
            have "cross_v1 (j'+3) (edge_pt_e 0 t) =
              (1-t) * ((vxe(j'+3) - vxe 1) * (vye 0 - vye 1) -
                       (vye(j'+3) - vye 1) * (vxe 0 - vxe 1))"
            proof -
              have hsuc0': "Suc 0 mod ?ne = 1" using hlen hne_eq by (by100 simp)
              have "fst (edge_pt_e 0 t) = (1-t)*vxe 0 + t*vxe 1"
                unfolding edge_pt_e_def using hsuc0' by (by100 simp)
              moreover have "snd (edge_pt_e 0 t) = (1-t)*vye 0 + t*vye 1"
                unfolding edge_pt_e_def using hsuc0' by (by100 simp)
              ultimately show ?thesis unfolding cross_v1_def by (by100 algebra)
            qed
            hence hcross_pos: "cross_v1 (Suc(j'+2) mod ?ne) (edge_pt_e 0 t) > 0"
            proof -
              assume hcv: "cross_v1 (j'+3) (edge_pt_e 0 t) =
                (1-t) * ((vxe(j'+3) - vxe 1) * (vye 0 - vye 1) -
                         (vye(j'+3) - vye 1) * (vxe 0 - vxe 1))"
              have "(1-t) > 0" using ht_lt1 by (by100 simp)
              hence "(1-t) * ((vxe(j'+3) - vxe 1) * (vye 0 - vye 1) -
                         (vye(j'+3) - vye 1) * (vxe 0 - vxe 1)) > 0"
                using hdet_pos' by (rule mult_pos_pos)
              hence "cross_v1 (j'+3) (edge_pt_e 0 t) > 0" using hcv by (by100 linarith)
              thus ?thesis unfolding hmod_eq[symmetric] by (by100 simp)
            qed
            show "\<not> in_sector j' (edge_pt_e 0 t)"
              unfolding in_sector_def using hcross_pos by (by100 linarith)
          qed
          \<comment> \<open>Step 2: Therefore LEAST = nw-1.\<close>
          have hj_is_nw1: "j_sel = ?nw - 1"
          proof -
            have hj_sel_le: "j_sel \<ge> ?nw - 1"
            proof (rule ccontr)
              assume "\<not> j_sel \<ge> ?nw - 1"
              hence "j_sel < ?nw - 1" by (by100 simp)
              hence "\<not> in_sector j_sel (edge_pt_e 0 t)" using hno_smaller by (by100 blast)
              thus False using hj_sel_valid by (by100 simp)
            qed
            moreover have "j_sel < ?nw" using hj_sel_valid by (by100 simp)
            ultimately show "j_sel = ?nw - 1" by (by100 linarith)
          qed
          \<comment> \<open>Step 3: Compute the barycentric coordinates for sector nw-1.
             With j\\_sel = nw-1, the formula in phi\\_fn\\_def evaluates correctly.\<close>
          \<comment> \<open>The key substitutions:
             j = nw-1. (j+2 = nw+1, Suc(j+2) mod ne = 0, Suc j mod nw = 0).
             ex = vxe(nw+1) - vxe 1, fx = vxe 0 - vxe 1.
             dx = (1-t)*(vxe 0 - vxe 1) (parallel to fx).
             s = (fy*dx - fx*dy) / det = 0.
             t\\_par = (ex*dy - ey*dx) / det = (1-t).
             Result: t*cxw + (1-t)*vxw 0.\<close>
          \<comment> \<open>Step 3: Use hphi\\_fn\\_sector with j = nw-1.\<close>
          have hLEAST_eq: "(LEAST j'. j' < ?nw \<and> in_sector j' (edge_pt_e 0 t)) = ?nw - 1"
            using hj_sel hj_is_nw1 by (by100 simp)
          from hphi_fn_sector[OF hp_ne_v1 hLEAST_eq]
          have hphi_val: "phi_fn (edge_pt_e 0 t) =
            (let ex = vxe((?nw-1)+2) - vxe 1; ey = vye((?nw-1)+2) - vye 1;
                 fx = vxe(Suc((?nw-1)+2) mod ?ne) - vxe 1; fy = vye(Suc((?nw-1)+2) mod ?ne) - vye 1;
                 det = ex*fy - ey*fx;
                 dx = fst (edge_pt_e 0 t) - vxe 1; dy = snd (edge_pt_e 0 t) - vye 1;
                 s = (fy*dx - fx*dy) / det;
                 t_par = (ex*dy - ey*dx) / det in
             ((1-s-t_par)*?cxw + s*vxw(?nw-1) + t_par*vxw(Suc (?nw-1) mod ?nw),
              (1-s-t_par)*?cyw + s*vyw(?nw-1) + t_par*vyw(Suc (?nw-1) mod ?nw)))" .
          \<comment> \<open>Simplify the modular indices and compute s=0, t\\_par=1-t.\<close>
          have hnw1_plus2: "(?nw - 1) + 2 = ?nw + 1" using hnw_pos by (by100 simp)
          have hsuc_nw1_e: "Suc((?nw-1)+2) mod ?ne = 0"
          proof -
            have "Suc((?nw-1)+2) = ?nw + 2" using hnw_pos by (by100 simp)
            thus ?thesis using hne_eq by (by100 simp)
          qed
          have hsuc_nw1_w: "Suc (?nw - 1) mod ?nw = 0"
          proof -
            have "Suc(?nw-1) = ?nw" using hnw_pos by (by100 simp)
            thus ?thesis by (by100 simp)
          qed
          have hsuc0: "Suc 0 mod ?ne = 1" using hlen hne_eq by (by100 simp)
          have hfx: "vxe(Suc((?nw-1)+2) mod ?ne) - vxe 1 = vxe 0 - vxe 1"
            using hsuc_nw1_e by (by100 simp)
          have hfy: "vye(Suc((?nw-1)+2) mod ?ne) - vye 1 = vye 0 - vye 1"
            using hsuc_nw1_e by (by100 simp)
          have hdx: "fst (edge_pt_e 0 t) - vxe 1 = (1-t)*(vxe 0 - vxe 1)"
          proof -
            have "fst (edge_pt_e 0 t) = (1-t)*vxe 0 + t*vxe 1"
              unfolding edge_pt_e_def using hsuc0 by (by100 simp)
            thus ?thesis by (by100 algebra)
          qed
          have hdy: "snd (edge_pt_e 0 t) - vye 1 = (1-t)*(vye 0 - vye 1)"
          proof -
            have "snd (edge_pt_e 0 t) = (1-t)*vye 0 + t*vye 1"
              unfolding edge_pt_e_def using hsuc0 by (by100 simp)
            thus ?thesis by (by100 algebra)
          qed
          \<comment> \<open>s = (fy*dx - fx*dy)/det = ((vye 0-vye 1)*(1-t)*(vxe 0-vxe 1) -
             (vxe 0-vxe 1)*(1-t)*(vye 0-vye 1))/det = 0.\<close>
          have hs_zero: "(vye 0-vye 1)*((1-t)*(vxe 0-vxe 1)) -
            (vxe 0-vxe 1)*((1-t)*(vye 0-vye 1)) = 0" by (by100 algebra)
          \<comment> \<open>Compute t\\_par = (1-t)*det/det = 1-t (if det \\<noteq> 0).\<close>
          have hdet_nw1_pos: "(vxe(?nw+1)-vxe 1)*(vye 0-vye 1) - (vye(?nw+1)-vye 1)*(vxe 0-vxe 1) > 0"
            using hdet_from_v1[rule_format, of "?nw+1"] hlen hne_eq by (by100 linarith)
          have hdet_ne0: "(vxe(?nw+1)-vxe 1)*(vye 0-vye 1) - (vye(?nw+1)-vye 1)*(vxe 0-vxe 1) \<noteq> 0"
            using hdet_nw1_pos by (by100 linarith)
          \<comment> \<open>The ex*dy - ey*dx factor:\<close>
          have htpar_num: "(vxe(?nw+1)-vxe 1)*((1-t)*(vye 0-vye 1)) -
            (vye(?nw+1)-vye 1)*((1-t)*(vxe 0-vxe 1)) =
            (1-t)*((vxe(?nw+1)-vxe 1)*(vye 0-vye 1) - (vye(?nw+1)-vye 1)*(vxe 0-vxe 1))"
            by (by100 algebra)
          \<comment> \<open>So t\\_par = (1-t)*det/det = 1-t.\<close>
          have htpar_val: "(1-t)*((vxe(?nw+1)-vxe 1)*(vye 0-vye 1) - (vye(?nw+1)-vye 1)*(vxe 0-vxe 1)) /
            ((vxe(?nw+1)-vxe 1)*(vye 0-vye 1) - (vye(?nw+1)-vye 1)*(vxe 0-vxe 1)) = 1 - t"
            using hdet_ne0 by (by100 simp)
          \<comment> \<open>Now assemble: with s=0, t\\_par=1-t, Suc(nw-1) mod nw = 0:
             result = (1-0-(1-t))*cxw + 0*vxw(nw-1) + (1-t)*vxw 0 = t*cxw + (1-t)*vxw 0.\<close>
          \<comment> \<open>Manually expand the let-expression in hphi\\_val using known substitutions.\<close>
          have hphi_expanded: "phi_fn (edge_pt_e 0 t) =
            (let s = ((vye 0-vye 1)*((1-t)*(vxe 0-vxe 1)) - (vxe 0-vxe 1)*((1-t)*(vye 0-vye 1))) /
                     ((vxe(?nw+1)-vxe 1)*(vye 0-vye 1) - (vye(?nw+1)-vye 1)*(vxe 0-vxe 1));
                 t_par = ((vxe(?nw+1)-vxe 1)*((1-t)*(vye 0-vye 1)) - (vye(?nw+1)-vye 1)*((1-t)*(vxe 0-vxe 1))) /
                     ((vxe(?nw+1)-vxe 1)*(vye 0-vye 1) - (vye(?nw+1)-vye 1)*(vxe 0-vxe 1)) in
             ((1-s-t_par)*?cxw + s*vxw(?nw-1) + t_par*vxw 0,
              (1-s-t_par)*?cyw + s*vyw(?nw-1) + t_par*vyw 0))"
            using hphi_val hnw1_plus2 hsuc_nw1_e hsuc_nw1_w hfx hfy hdx hdy
            unfolding Let_def by (by5000 simp)
          \<comment> \<open>Now substitute s=0 and t\\_par=1-t.\<close>
          hence "phi_fn (edge_pt_e 0 t) =
            ((1-0-(1-t))*?cxw + 0*vxw(?nw-1) + (1-t)*vxw 0,
             (1-0-(1-t))*?cyw + 0*vyw(?nw-1) + (1-t)*vyw 0)"
            using hs_zero htpar_num htpar_val unfolding Let_def by (by100 simp)
          hence "phi_fn (edge_pt_e 0 t) = (t*?cxw + (1-t)*vxw 0, t*?cyw + (1-t)*vyw 0)"
            by (by100 simp)
          thus ?thesis
          proof -
            assume h: "phi_fn (edge_pt_e 0 t) = (t*?cxw + (1-t)*vxw 0, t*?cyw + (1-t)*vyw 0)"
            have "t*?cxw + (1-t)*vxw 0 = (1-t)*vxw 0 + t*?cxw" by (by100 algebra)
            moreover have "t*?cyw + (1-t)*vyw 0 = (1-t)*vyw 0 + t*?cyw" by (by100 algebra)
            ultimately show ?thesis using h by (by100 simp)
          qed
        qed
      qed
      \<comment> \<open>Key helper: phi on spur edge 1 gives the arc in reverse.\<close>
      \<comment> \<open>SYMMETRIC APPROACH: Both spur1 and nonspur follow the same argument as spur0.
         The key difficulty is numeral conversion (Suc(Suc 0) vs 2, etc.) in the
         phi\\_fn\\_def unfolding. For now, sorry these pending process\\_theories run.\<close>
      have hphi_on_spur1: "\<forall>t\<in>I_set.
        phi_fn (edge_pt_e 1 t) = (t*vxw 0 + (1-t)*?cxw, t*vyw 0 + (1-t)*?cyw)"
      proof (intro ballI)
        fix t assume ht: "t \<in> I_set"
        show "phi_fn (edge_pt_e 1 t) = (t*vxw 0 + (1-t)*?cxw, t*vyw 0 + (1-t)*?cyw)"
        proof (cases "t = 0")
          case True
          \<comment> \<open>At t=0: edge\\_pt\\_e(1, 0) = v\\_1. phi\\_fn(v\\_1) = c\\_w. And 0*u\\_0 + 1*c\\_w = c\\_w.\<close>
          have "Suc 1 mod ?ne = 2"
          proof -
            have "(2::nat) < ?ne" using hlen hne_eq by (by100 linarith)
            thus ?thesis by (by100 simp)
          qed
          have "edge_pt_e 1 0 = (vxe 1, vye 1)"
            unfolding edge_pt_e_def using \<open>Suc 1 mod ?ne = 2\<close> by (by100 simp)
          hence "phi_fn (edge_pt_e 1 0) = (?cxw, ?cyw)" unfolding phi_fn_def by (by100 simp)
          thus ?thesis using True by (by100 simp)
        next
          case False
          \<comment> \<open>At t > 0: edge point in sector 0, compute via barycentric formula.
             Use hphi\\_fn\\_sector with j=0: phi\\_fn = (1-s-tpar)*c\\_w + s*u\\_0 + tpar*u\\_1.
             With s=t, tpar=0: result = (1-t)*c\\_w + t*u\\_0.\<close>
          have ht_pos: "t > 0" using False ht unfolding top1_unit_interval_def by (by100 auto)
          have hSuc1: "Suc 1 mod ?ne = 2"
          proof -
            have "(2::nat) < ?ne" using hlen hne_eq by (by100 linarith)
            thus ?thesis by (by100 simp)
          qed
          \<comment> \<open>p \\<noteq> v\\_1.\<close>
          have hp_ne_v1: "edge_pt_e 1 t \<noteq> (vxe 1, vye 1)"
          proof
            assume "edge_pt_e 1 t = (vxe 1, vye 1)"
            hence "(1-t)*vxe 1 + t*vxe 2 = vxe 1"
              unfolding edge_pt_e_def using hSuc1 by (by100 simp)
            hence "vxe 1 - t*vxe 1 + t*vxe 2 = vxe 1"
            proof -
              assume "(1-t)*vxe 1 + t*vxe 2 = vxe 1"
              have "(1-t)*vxe 1 = vxe 1 - t*vxe 1" by (by100 algebra)
              thus ?thesis using \<open>(1-t)*vxe 1 + t*vxe 2 = vxe 1\<close> by (by100 linarith)
            qed
            hence "t*vxe 2 - t*vxe 1 = 0" by (by100 linarith)
            hence htx: "t*(vxe 2 - vxe 1) = 0" by (by100 algebra)
            hence "t = 0 \<or> vxe 2 = vxe 1" by (by100 algebra)
            moreover from \<open>edge_pt_e 1 t = (vxe 1, vye 1)\<close>
            have "(1-t)*vye 1 + t*vye 2 = vye 1"
              unfolding edge_pt_e_def using hSuc1 by (by100 simp)
            hence "vye 1 - t*vye 1 + t*vye 2 = vye 1"
            proof -
              assume "(1-t)*vye 1 + t*vye 2 = vye 1"
              have "(1-t)*vye 1 = vye 1 - t*vye 1" by (by100 algebra)
              thus ?thesis using \<open>(1-t)*vye 1 + t*vye 2 = vye 1\<close> by (by100 linarith)
            qed
            hence "t*vye 2 - t*vye 1 = 0" by (by100 linarith)
            hence hty: "t*(vye 2 - vye 1) = 0" by (by100 algebra)
            hence "t = 0 \<or> vye 2 = vye 1" by (by100 algebra)
            from htx hty have "t = 0 \<or> (vxe 2 = vxe 1 \<and> vye 2 = vye 1)" by (by100 algebra)
            thus False
            proof (elim disjE)
              assume "t = 0" thus False using ht_pos by (by100 simp)
            next
              assume "vxe 2 = vxe 1 \<and> vye 2 = vye 1"
              have "(2::nat) < ?ne" using hlen hne_eq by (by100 linarith)
              moreover have "(1::nat) < ?ne" using hlen hne_eq by (by100 linarith)
              moreover have "(2::nat) \<noteq> 1" by (by100 simp)
              ultimately have "(vxe 2, vye 2) \<noteq> (vxe 1, vye 1)"
                using hC3_e[rule_format] by (by100 blast)
              thus False using \<open>vxe 2 = vxe 1 \<and> vye 2 = vye 1\<close> by (by100 simp)
            qed
          qed
          \<comment> \<open>In sector 0. LEAST = 0 (trivially smallest).\<close>
          have "in_sector 0 (edge_pt_e 1 t)"
          proof -
            have hpt_x: "fst(edge_pt_e 1 t) = (1-t)*vxe 1 + t*vxe 2"
              unfolding edge_pt_e_def using hSuc1 by (by100 simp)
            have hpt_y: "snd(edge_pt_e 1 t) = (1-t)*vye 1 + t*vye 2"
              unfolding edge_pt_e_def using hSuc1 by (by100 simp)
            \<comment> \<open>cross\\_v1(2, p) = 0: parallel to edge direction.\<close>
            have hcr2: "cross_v1 2 (edge_pt_e 1 t) = 0"
              unfolding cross_v1_def using hpt_x hpt_y by (by100 algebra)
            \<comment> \<open>cross\\_v1(3, p) = t * det(v\\_3-v\\_1, v\\_2-v\\_1) \\<le> 0.
               det(v\\_3-v\\_1, v\\_2-v\\_1) = -(det(v\\_2-v\\_1, v\\_3-v\\_1)) < 0 by hdet\\_pos.\<close>
            have hcr3_expr: "cross_v1 3 (edge_pt_e 1 t) =
              t * ((vxe 3-vxe 1)*(vye 2-vye 1)-(vye 3-vye 1)*(vxe 2-vxe 1))"
              unfolding cross_v1_def using hpt_x hpt_y by (by100 algebra)
            have hdet0_pos: "(vxe 2-vxe 1)*(vye 3-vye 1)-(vye 2-vye 1)*(vxe 3-vxe 1) > 0"
            proof -
              from hdet_pos[rule_format, of 0] hnw_pos
              have "let ex = vxe(0+2) - vxe 1; ey = vye(0+2) - vye 1;
                        fx = vxe(Suc(0+2) mod ?ne) - vxe 1; fy = vye(Suc(0+2) mod ?ne) - vye 1
                    in ex*fy - ey*fx > 0" by (by100 simp)
              hence "(vxe(0+2)-vxe 1)*(vye(Suc(0+2) mod ?ne)-vye 1) -
                     (vye(0+2)-vye 1)*(vxe(Suc(0+2) mod ?ne)-vxe 1) > 0"
                unfolding Let_def .
              moreover have "(0::nat)+2 = 2" by (by100 simp)
              moreover have "Suc((0::nat)+2) mod ?ne = 3"
              proof -
                have "(3::nat) < ?ne" using hlen hne_eq by (by100 linarith)
                thus ?thesis by (by100 simp)
              qed
              ultimately show ?thesis by (simp add: numeral_2_eq_2 numeral_3_eq_3)
            qed
            hence "(vxe 3-vxe 1)*(vye 2-vye 1)-(vye 3-vye 1)*(vxe 2-vxe 1) < 0"
            proof -
              have "(vxe 3-vxe 1)*(vye 2-vye 1)-(vye 3-vye 1)*(vxe 2-vxe 1) =
                -((vxe 2-vxe 1)*(vye 3-vye 1)-(vye 2-vye 1)*(vxe 3-vxe 1))"
                by (by100 algebra)
              thus ?thesis using hdet0_pos by (by100 linarith)
            qed
            hence hfactor_le: "(vxe 3-vxe 1)*(vye 2-vye 1)-(vye 3-vye 1)*(vxe 2-vxe 1) \<le> 0"
              by (by100 linarith)
            have ht_ge: "t \<ge> 0" using ht unfolding top1_unit_interval_def by (by100 auto)
            from mult_nonneg_nonpos[OF ht_ge hfactor_le]
            have hcr3_le: "cross_v1 3 (edge_pt_e 1 t) \<le> 0"
              using hcr3_expr by (by100 linarith)
            \<comment> \<open>Assemble in\\_sector with numeral conversion.\<close>
            have hcr2': "cross_v1 (Suc(Suc 0)) (edge_pt_e 1 t) = 0"
              using hcr2 by (simp add: numeral_2_eq_2)
            have "Suc(Suc(Suc 0)) mod ?ne = 3"
            proof -
              have "(3::nat) < ?ne" using hlen hne_eq by (by100 linarith)
              thus ?thesis by (simp add: numeral_3_eq_3)
            qed
            hence hcr3': "cross_v1 (Suc(Suc(Suc 0)) mod ?ne) (edge_pt_e 1 t) \<le> 0"
              using hcr3_le by (simp add: numeral_3_eq_3)
            show "in_sector 0 (edge_pt_e 1 t)"
              unfolding in_sector_def using hcr2' hcr3' by (by100 simp)
          qed
          hence hLEAST_0: "(LEAST j'. j' < ?nw \<and> in_sector j' (edge_pt_e 1 t)) = 0"
          proof (intro Least_equality)
            show "0 < ?nw \<and> in_sector 0 (edge_pt_e 1 t)" using hnw_pos \<open>in_sector 0 (edge_pt_e 1 t)\<close> by (by100 simp)
          next
            fix j' assume "j' < ?nw \<and> in_sector j' (edge_pt_e 1 t)" thus "0 \<le> j'" by (by100 simp)
          qed
          \<comment> \<open>Apply hphi\\_fn\\_sector and compute the value.\<close>
          from hphi_fn_sector[OF hp_ne_v1 hLEAST_0]
          have hphi_val: "phi_fn (edge_pt_e 1 t) =
            (let ex = vxe(0+2) - vxe 1; ey = vye(0+2) - vye 1;
                 fx = vxe(Suc(0+2) mod ?ne) - vxe 1; fy = vye(Suc(0+2) mod ?ne) - vye 1;
                 det = ex*fy - ey*fx;
                 dx = fst (edge_pt_e 1 t) - vxe 1; dy = snd (edge_pt_e 1 t) - vye 1;
                 s = (fy*dx - fx*dy) / det;
                 t_par = (ex*dy - ey*dx) / det in
             ((1-s-t_par)*?cxw + s*vxw 0 + t_par*vxw(Suc 0 mod ?nw),
              (1-s-t_par)*?cyw + s*vyw 0 + t_par*vyw(Suc 0 mod ?nw)))" .
          \<comment> \<open>Simplify: 0+2=2, Suc(0+2)=3, dx=t*(vxe 2-vxe 1), dy=t*(vye 2-vye 1).
             s = t*(fy*(vxe 2-vxe 1)-fx*(vye 2-vye 1))/det = t*det/det = t (since fx is v\\_3-v\\_1 direction).
             t\\_par = 0 (ex*dy-ey*dx = ex*t*ey-ey*t*ex = 0).
             Result = (1-t)*c\\_w + t*u\\_0.\<close>
          \<comment> \<open>Compute dx, dy, s, t\\_par.\<close>
          have hpt_x: "fst(edge_pt_e 1 t) - vxe 1 = t*(vxe 2-vxe 1)"
          proof -
            have "fst(edge_pt_e 1 t) = (1-t)*vxe 1 + t*vxe 2"
              unfolding edge_pt_e_def using hSuc1 by (by100 simp)
            thus ?thesis by (by100 algebra)
          qed
          have hpt_y: "snd(edge_pt_e 1 t) - vye 1 = t*(vye 2-vye 1)"
          proof -
            have "snd(edge_pt_e 1 t) = (1-t)*vye 1 + t*vye 2"
              unfolding edge_pt_e_def using hSuc1 by (by100 simp)
            thus ?thesis by (by100 algebra)
          qed
          \<comment> \<open>t\\_par numerator = ex*dy - ey*dx = (vxe 2-vxe 1)*t*(vye 2-vye 1) - (vye 2-vye 1)*t*(vxe 2-vxe 1) = 0.\<close>
          have h02: "(0::nat)+2 = 2" by (by100 simp)
          have htpar_zero: "(vxe(0+2)-vxe 1)*(t*(vye 2-vye 1)) -
            (vye(0+2)-vye 1)*(t*(vxe 2-vxe 1)) = 0" unfolding h02 by (by100 algebra)
          \<comment> \<open>s numerator = fy*dx - fx*dy.  s = t*det/det = t (when det \\<noteq> 0).\<close>
          have hSuc02: "Suc(0+2) mod ?ne = 3"
          proof -
            have "(3::nat) < ?ne" using hlen hne_eq by (by100 linarith)
            thus ?thesis by (by100 simp)
          qed
          have hSuc0w: "Suc 0 mod ?nw = 1"
          proof -
            have "?nw \<ge> 3" using hlen by (by100 simp)
            thus ?thesis by (by100 simp)
          qed
          have hs_num: "(vye(Suc(0+2) mod ?ne)-vye 1)*(t*(vxe 2-vxe 1)) -
            (vxe(Suc(0+2) mod ?ne)-vxe 1)*(t*(vye 2-vye 1)) =
            t * ((vxe(0+2)-vxe 1)*(vye(Suc(0+2) mod ?ne)-vye 1) - (vye(0+2)-vye 1)*(vxe(Suc(0+2) mod ?ne)-vxe 1))"
            unfolding h02 hSuc02 by (by100 algebra)
          have hdet_ne0: "(vxe(0+2)-vxe 1)*(vye(Suc(0+2) mod ?ne)-vye 1) -
            (vye(0+2)-vye 1)*(vxe(Suc(0+2) mod ?ne)-vxe 1) \<noteq> 0"
          proof -
            from hdet_pos[rule_format, of 0] hnw_pos
            show ?thesis unfolding Let_def by (by100 linarith)
          qed
          have hs_val: "t * ((vxe(0+2)-vxe 1)*(vye(Suc(0+2) mod ?ne)-vye 1) -
            (vye(0+2)-vye 1)*(vxe(Suc(0+2) mod ?ne)-vxe 1)) /
            ((vxe(0+2)-vxe 1)*(vye(Suc(0+2) mod ?ne)-vye 1) -
            (vye(0+2)-vye 1)*(vxe(Suc(0+2) mod ?ne)-vxe 1)) = t"
            using hdet_ne0 by (by100 simp)
          \<comment> \<open>Skip the intermediate let-expansion. Instead compute directly:
             phi\\_fn value from hphi\\_val has 0+2 numerals.
             The s and tpar computations work directly with these numerals.\<close>
          \<comment> \<open>tpar = 0: (vxe(0+2)-vxe 1)*dy - (vye(0+2)-vye 1)*dx = 0.\<close>
          have htpar_zero_raw: "((vxe(0+2)-vxe 1)*(t*(vye 2-vye 1)) - (vye(0+2)-vye 1)*(t*(vxe 2-vxe 1))) = 0"
            unfolding h02 by (by100 algebra)
          \<comment> \<open>s = t*det/det = t.\<close>
          have hs_num_raw: "(vye(Suc(0+2) mod ?ne)-vye 1)*(t*(vxe 2-vxe 1)) - (vxe(Suc(0+2) mod ?ne)-vxe 1)*(t*(vye 2-vye 1))
            = t * ((vxe(0+2)-vxe 1)*(vye(Suc(0+2) mod ?ne)-vye 1) - (vye(0+2)-vye 1)*(vxe(Suc(0+2) mod ?ne)-vxe 1))"
            unfolding h02 hSuc02 by (by100 algebra)
          have hdet_ne0_raw: "(vxe(0+2)-vxe 1)*(vye(Suc(0+2) mod ?ne)-vye 1) - (vye(0+2)-vye 1)*(vxe(Suc(0+2) mod ?ne)-vxe 1) \<noteq> 0"
          proof -
            from hdet_pos[rule_format, of 0] hnw_pos
            show ?thesis unfolding Let_def by (by100 linarith)
          qed
          have hs_val_raw: "t * ((vxe(0+2)-vxe 1)*(vye(Suc(0+2) mod ?ne)-vye 1) - (vye(0+2)-vye 1)*(vxe(Suc(0+2) mod ?ne)-vxe 1)) /
            ((vxe(0+2)-vxe 1)*(vye(Suc(0+2) mod ?ne)-vye 1) - (vye(0+2)-vye 1)*(vxe(Suc(0+2) mod ?ne)-vxe 1)) = t"
            using hdet_ne0_raw by (by100 simp)
          \<comment> \<open>Assemble: phi\\_fn = (1-t-0)*cxw + t*vxw 0 + 0*vxw(Suc 0 mod nw), ...\<close>
          from hphi_val have "phi_fn (edge_pt_e 1 t) = ((1-t-0)*?cxw + t*vxw 0 + 0*vxw(Suc 0 mod ?nw),
            (1-t-0)*?cyw + t*vyw 0 + 0*vyw(Suc 0 mod ?nw))"
            using hpt_x hpt_y htpar_zero_raw hs_num_raw hs_val_raw
            unfolding Let_def
            by (metis (no_types, lifting) divide_eq_0_iff) \<comment> \<open>found by sledgehammer\<close>
          hence "phi_fn (edge_pt_e 1 t) = (t*vxw 0 + (1-t)*?cxw, t*vyw 0 + (1-t)*?cyw)"
            by (by100 simp)
          thus ?thesis by (by100 simp)
        qed
      qed
      \<comment> \<open>Helper: phi at non-spur vertices. phi\\_fn(v\\_{k+2}) = u\\_k for k < nw.
         Sorry'd: the LEAST-based computation at vertices is complex due to
         multiple valid sectors sharing the vertex. The answer is always u\\_k
         regardless of which sector LEAST picks.\<close>
      have hphi_at_vertex: "\<forall>k<?nw. phi_fn (vxe(k+2), vye(k+2)) = (vxw k, vyw k)"
      proof (intro allI impI)
        fix k assume hk: "k < ?nw"
        have hk2: "k+2 < ?ne" using hk hne_eq by (by100 linarith)
        have hp_ne_v1: "(vxe(k+2), vye(k+2)) \<noteq> (vxe 1, vye 1)"
        proof -
          have "(1::nat) < ?ne" using hlen hne_eq by (by100 linarith)
          have "(k+2::nat) \<noteq> 1" by (by100 simp)
          from hC3_e[rule_format, OF hk2 \<open>(1::nat) < ?ne\<close> this]
          show ?thesis .
        qed
        \<comment> \<open>in\\_sector(k) holds at vertex.\<close>
        let ?si = "Suc(k+2) mod ?ne"
        have hin: "in_sector k (vxe(k+2), vye(k+2))"
        proof -
          have hcr1: "cross_v1 (k+2) (vxe(k+2), vye(k+2)) = 0"
            unfolding cross_v1_def by (by100 simp)
          from hdet_pos[rule_format, OF hk]
          have hdet_k: "(vxe(k+2)-vxe 1)*(vye ?si-vye 1)-(vye(k+2)-vye 1)*(vxe ?si-vxe 1) > 0"
            unfolding Let_def .
          have "cross_v1 ?si (vxe(k+2), vye(k+2)) < 0"
          proof -
            have "cross_v1 ?si (vxe(k+2), vye(k+2)) =
              -((vxe(k+2)-vxe 1)*(vye ?si-vye 1)-(vye(k+2)-vye 1)*(vxe ?si-vxe 1))"
              unfolding cross_v1_def by (by100 simp)
            thus ?thesis using hdet_k by (by100 linarith)
          qed
          thus ?thesis unfolding in_sector_def using hcr1 by (by100 linarith)
        qed
        \<comment> \<open>LEAST picks some sector containing v\\_{k+2}. Use sector k.\<close>
        have hexists: "\<exists>j. j < ?nw \<and> in_sector j (vxe(k+2), vye(k+2))"
          using hin hk by (by100 blast)
        have hLEAST_le_k: "(LEAST j. j < ?nw \<and> in_sector j (vxe(k+2), vye(k+2))) \<le> k"
          using Least_le[of "\<lambda>j. j < ?nw \<and> in_sector j (vxe(k+2), vye(k+2))" k]
                hin hk by (by100 simp)
        from LeastI_ex[OF hexists]
        have hLEAST_valid: "(LEAST j. j < ?nw \<and> in_sector j (vxe(k+2), vye(k+2))) < ?nw"
          by (by100 simp)
        \<comment> \<open>Key: pre-compute dx = vxe(k+2)-vxe 1, dy = vye(k+2)-vye 1.\<close>
        define dx where "dx = vxe(k+2) - vxe 1"
        define dy where "dy = vye(k+2) - vye 1"
        have hdx: "fst (vxe(k+2), vye(k+2)) - vxe 1 = dx" unfolding dx_def by (by100 simp)
        have hdy: "snd (vxe(k+2), vye(k+2)) - vye 1 = dy" unfolding dy_def by (by100 simp)
        \<comment> \<open>The phi\\_fn value via hphi\\_fn\\_sector:\<close>
        define j_v where "j_v = (LEAST j. j < ?nw \<and> in_sector j (vxe(k+2), vye(k+2)))"
        have hj_eq_v: "(LEAST j. j < ?nw \<and> in_sector j (vxe(k+2), vye(k+2))) = j_v"
          unfolding j_v_def by (by100 simp)
        \<comment> \<open>The computation: s and tpar for sector j\\_v at vertex v\\_{k+2}.
           v\\_{k+2} is at barycentric (0,1,0) in sector k, or (0,0,1) in sector k-1.
           In sector j\\_v: dx = vxe(k+2)-vxe 1, dy = vye(k+2)-vye 1.
           ex = vxe(j\\_v+2)-vxe 1, ey = vye(j\\_v+2)-vye 1.
           fx = vxe(si\\_jv)-vxe 1, fy = vye(si\\_jv)-vye 1.
           s = (fy*dx-fx*dy)/det, tpar = (ex*dy-ey*dx)/det.
           Result = (1-s-tpar)*cxw + s*vxw(j\\_v) + tpar*vxw(Suc j\\_v mod nw).\<close>
        \<comment> \<open>Use hphi\\_fn\\_at\\_pair with sector k (in\\_sector(k) proved).\<close>
        \<comment> \<open>Step through phi\\_fn\\_def manually using apply-style.\<close>
        \<comment> \<open>Use decomposed form: phi\\_fn = (1-s-t)*cxw + s*vxw(j\\_v) + t*vxw(Suc j\\_v).\<close>
        let ?m = "j_v + 2" and ?m' = "Suc(j_v+2) mod ?ne"
        from hphi_fn_decomp[OF hp_ne_v1 hj_eq_v]
        have hphi_decomp: "phi_fn (vxe(k+2), vye(k+2)) =
          ((1 - phi_s2 ?m ?m' dx dy - phi_t2 ?m ?m' dx dy)*?cxw
           + phi_s2 ?m ?m' dx dy*vxw j_v + phi_t2 ?m ?m' dx dy*vxw(Suc j_v mod ?nw),
           (1 - phi_s2 ?m ?m' dx dy - phi_t2 ?m ?m' dx dy)*?cyw
           + phi_s2 ?m ?m' dx dy*vyw j_v + phi_t2 ?m ?m' dx dy*vyw(Suc j_v mod ?nw))"
          unfolding dx_def dy_def by (by100 simp)
        \<comment> \<open>Now compute phi\\_s and phi\\_t at vertex (dx = ex direction).\<close>
        show "phi_fn (vxe(k+2), vye(k+2)) = (vxw k, vyw k)"
        proof -
          \<comment> \<open>Compute phi\\_t at vertex: tpar = (ex*dy - ey*dx)/det.
             dx = vxe(k+2)-vxe 1 = ex(k), dy = vye(k+2)-vye 1 = ey(k).
             For sector j\\_v: ex*ey - ey*ex = 0 when j\\_v = k (same vectors).
             For j\\_v = k-1: ex*(vye(k+2)-vye 1) - ey*(vxe(k+2)-vye 1) = det\\_jv.\<close>
          \<comment> \<open>Split on j\\_v = k or j\\_v < k.\<close>
          have hjv_le: "j_v \<le> k" using hLEAST_le_k unfolding j_v_def by (by100 simp)
          have "j_v = k \<or> j_v < k" using hjv_le by (by100 linarith)
          thus ?thesis
          proof (elim disjE)
            assume hjvk: "j_v = k"
            \<comment> \<open>When j\\_v = k: dx = ex, dy = ey. s = det/det = 1, t = 0.\<close>
            have "phi_t2 (k+2) ?si dx dy = 0"
              unfolding phi_t2_def dx_def dy_def Let_def by (by100 simp)
            moreover have "phi_s2 (k+2) ?si dx dy = 1"
            proof -
              from hdet_pos[rule_format, OF hk]
              have hdet_ne0: "(vxe(k+2)-vxe 1)*(vye ?si-vye 1)-(vye(k+2)-vye 1)*(vxe ?si-vxe 1) \<noteq> 0"
                unfolding Let_def by (by100 linarith)
              show ?thesis unfolding phi_s2_def dx_def dy_def Let_def using hdet_ne0 by (by100 simp)
            qed
            moreover have "?m = k+2 \<and> ?m' = ?si" using hjvk by (by100 simp)
            ultimately show ?thesis using hphi_decomp by (by100 simp)
          next
            assume hjvlt: "j_v < k"
            \<comment> \<open>When j\\_v < k: vertex v\\_{k+2} must be the third vertex of sector j\\_v,
               i.e., Suc(j\\_v+2) mod ne = k+2. This forces j\\_v = k-1.\<close>
            have hjv_eq: "j_v = k - 1"
            proof -
              \<comment> \<open>j\\_v < k and in\\_sector(j\\_v, v\\_{k+2}) holds. The second condition of in\\_sector
                 requires cross\\_v1(Suc(j\\_v+2) mod ne, v\\_{k+2}) \\<le> 0.
                 For j\\_v < k-1: Suc(j\\_v+2) mod ne = j\\_v+3 \\<le> k. Then
                 cross\\_v1(j\\_v+3, v\\_{k+2}) = det(v\\_{j\\_v+3}-v\\_1, v\\_{k+2}-v\\_1) > 0 by C11 at edge 0.
                 Contradiction with \\<le> 0.\<close>
              show "j_v = k - 1"
              proof (rule ccontr)
                assume "j_v \<noteq> k - 1"
                hence hjv_lt: "j_v < k - 1" using hjvlt by (by100 linarith)
                hence "j_v + 3 \<le> k + 1" by (by100 linarith)
                hence hjv3_lt: "j_v + 3 < ?ne" using hk hne_eq by (by100 linarith)
                have hmod_eq: "Suc(j_v+2) mod ?ne = j_v + 3" using hjv3_lt by (by100 simp)
                \<comment> \<open>cross\\_v1(j\\_v+3, v\\_{k+2}) = det(v\\_{j\\_v+3}-v\\_1, v\\_{k+2}-v\\_1).\<close>
                have hcross: "cross_v1 (j_v+3) (vxe(k+2), vye(k+2)) =
                  (vxe(j_v+3)-vxe 1)*(vye(k+2)-vye 1) - (vye(j_v+3)-vye 1)*(vxe(k+2)-vxe 1)"
                  unfolding cross_v1_def by (by100 simp)
                \<comment> \<open>This det > 0 from C11 at edge 0, vertex j\\_v+3 applied with argument
                   det(v\\_{j\\_v+3}-v\\_1, v\\_{k+2}-v\\_1) > 0.
                   We use hdet\\_from\\_v1 type argument but for general pair, not just v\\_0.\<close>
                have hdet_pos_jv3: "(vxe(j_v+3)-vxe 1)*(vye(k+2)-vye 1) -
                  (vye(j_v+3)-vye 1)*(vxe(k+2)-vxe 1) > 0"
                proof -
                  have "j_v + 3 < k + 2" using hjv_lt by (by100 linarith)
                  moreover have "k + 2 < ?ne" using hk hne_eq by (by100 linarith)
                  ultimately show ?thesis using hdet_general[rule_format, of "j_v+3" "k+2"]
                    by (by100 linarith)
                qed
                \<comment> \<open>But in\\_sector requires this \\<le> 0. Contradiction.\<close>
                from LeastI_ex[OF hexists]
                have "in_sector j_v (vxe(k+2), vye(k+2))" unfolding j_v_def by (by100 simp)
                hence "cross_v1 (Suc(j_v+2) mod ?ne) (vxe(k+2), vye(k+2)) \<le> 0"
                  unfolding in_sector_def by (by100 simp)
                hence "cross_v1 (j_v+3) (vxe(k+2), vye(k+2)) \<le> 0" using hmod_eq by (by100 simp)
                thus False using hcross hdet_pos_jv3 by (by100 linarith)
              qed
            qed
            \<comment> \<open>In sector k-1: fx = vxe(k+2)-vxe 1 = dx, fy = vye(k+2)-vye 1 = dy.\<close>
            \<comment> \<open>j\\_v = k-1 means ?m = j\\_v+2 = k+1, ?m' = Suc(j\\_v+2) mod ne = k+2.\<close>
            have hm_eq: "?m = k+1" using hjv_eq hjvlt by (by100 linarith)
            have hm'_eq: "?m' = k+2"
            proof -
              have "Suc(j_v+2) = k+2" using hjv_eq hjvlt by (by100 linarith)
              moreover have "k+2 < ?ne" using hk hne_eq by (by100 linarith)
              ultimately show ?thesis by (by100 simp)
            qed
            have "phi_s2 (k+1) (k+2) dx dy = 0"
              unfolding phi_s2_def dx_def dy_def Let_def by (by100 simp)
            hence hphi_s_val: "phi_s2 ?m ?m' dx dy = 0"
              using hm_eq hm'_eq by (by100 simp)
            have hdet_km1_ne0: "(vxe(k+1)-vxe 1)*(vye(k+2)-vye 1)-(vye(k+1)-vye 1)*(vxe(k+2)-vxe 1) \<noteq> 0"
            proof -
              \<comment> \<open>Use hdet\\_from\\_v1 at k+2 instead of hdet\\_pos at k-1.\<close>
              have "k \<ge> 1" using hjvlt by (by100 linarith)
              have "2 \<le> k+1" using \<open>k \<ge> 1\<close> by (by100 linarith)
              have hk1_lt: "k+1 < ?ne" using hk hne_eq by (by100 linarith)
              from hdet_from_v1[rule_format, OF \<open>2 \<le> k+1\<close> hk1_lt]
              have "(vxe(k+1)-vxe 1)*(vye 0-vye 1)-(vye(k+1)-vye 1)*(vxe 0-vxe 1) > 0" .
              \<comment> \<open>Use hdet\\_pos at j\\_v (which IS k-1 but we don't need nat subtraction).\<close>
              from LeastI_ex[OF hexists] hLEAST_le_k
              have "j_v < ?nw" unfolding j_v_def by (by100 simp)
              from hdet_pos[rule_format, OF this]
              have "let ex = vxe(j_v+2)-vxe 1; ey = vye(j_v+2)-vye 1;
                        fx = vxe(Suc(j_v+2) mod ?ne)-vxe 1; fy = vye(Suc(j_v+2) mod ?ne)-vye 1
                    in ex*fy-ey*fx > 0" .
              hence "(vxe(j_v+2)-vxe 1)*(vye(Suc(j_v+2) mod ?ne)-vye 1)-
                     (vye(j_v+2)-vye 1)*(vxe(Suc(j_v+2) mod ?ne)-vxe 1) > 0"
                unfolding Let_def .
              \<comment> \<open>j\\_v+2 = k+1 and Suc(j\\_v+2) mod ne = k+2 from hm\\_eq and hm'\\_eq.\<close>
              hence "(vxe(k+1)-vxe 1)*(vye(k+2)-vye 1)-(vye(k+1)-vye 1)*(vxe(k+2)-vxe 1) > 0"
                using hm_eq hm'_eq by (by100 simp)
              thus ?thesis by (by100 linarith)
            qed
            have "phi_t2 (k+1) (k+2) dx dy = 1"
              unfolding phi_t2_def dx_def dy_def Let_def using hdet_km1_ne0 by (by100 simp)
            hence hphi_t_val: "phi_t2 ?m ?m' dx dy = 1"
              using hm_eq hm'_eq by (by100 simp)
            moreover have "Suc (k-1) mod ?nw = k"
            proof -
              have "Suc (k-1) = k" using hjvlt by (by100 linarith)
              moreover have "k < ?nw" using hk .
              ultimately show ?thesis by (by100 simp)
            qed
            moreover have "Suc j_v mod ?nw = k"
            proof -
              have "Suc j_v = k" using hjv_eq hjvlt by (by100 simp)
              thus ?thesis using hk by (by100 simp)
            qed
            ultimately show ?thesis using hphi_decomp hphi_s_val hphi_t_val by (by100 simp)
          qed
        qed
      qed
      \<comment> \<open>Key helper: phi on non-spur edges is linear.\<close>
      have hphi_on_nonspur: "\<forall>k<?nw. \<forall>t\<in>I_set.
        phi_fn (edge_pt_e (k+2) t) = edge_pt_w k t"
      proof (intro allI ballI impI)
        fix k t assume hk: "k < ?nw" and ht: "t \<in> I_set"
        \<comment> \<open>edge\\_pt\\_e(k+2, t) = (1-t)*v\\_{k+2} + t*v\\_{k+3}. In sector k of the fan.
           Phi maps this to (1-t)*u\\_k + t*u\\_{k+1} = edge\\_pt\\_w(k, t).\<close>
        have hk2: "k+2 < ?ne" using hk hne_eq by (by100 linarith)
        let ?si = "Suc(k+2) mod ?ne"
        have hsi: "?si < ?ne" using hnw_pos by (by100 simp)
        \<comment> \<open>edge\\_pt\\_e(k+2, t) \\<noteq> v\\_1 (since k+2 \\<ge> 2 \\<noteq> 1).\<close>
        have hp_ne_v1: "edge_pt_e (k+2) t \<noteq> (vxe 1, vye 1)"
        proof
          assume heq: "edge_pt_e (k+2) t = (vxe 1, vye 1)"
          \<comment> \<open>v\\_1 is strictly on one side of edge k+2 (by C11). So v\\_1 cannot be ON the edge.\<close>
          have h1_lt: "(1::nat) < ?ne" using hlen hne_eq by (by100 linarith)
          have h1_ne_k2: "(1::nat) \<noteq> k+2" by (by100 simp)
          have h1_ne_si: "(1::nat) \<noteq> ?si"
          proof (cases "k + 3 < ?ne")
            case True hence "?si = k + 3" by (by100 simp)
            thus ?thesis using True by (by100 linarith)
          next
            case False hence "k + 3 = ?ne" using hk hne_eq by (by100 linarith)
            hence "?si = 0" by (by100 simp)
            thus ?thesis by (by100 simp)
          qed
          \<comment> \<open>C11: v\\_1 is strictly on one side of edge k+2.\<close>
          from hC11_e[rule_format, OF hk2 h1_lt h1_ne_k2 h1_ne_si]
          have hside: "(vxe 1-vxe(k+2))*(vye ?si-vye(k+2))-(vye 1-vye(k+2))*(vxe ?si-vxe(k+2)) < 0" .
          \<comment> \<open>But if edge\\_pt\\_e(k+2,t) = v\\_1, then v\\_1 = (1-t)*v\\_{k+2} + t*v\\_{k+3}.
             So v\\_1 - v\\_{k+2} = t*(v\\_{k+3} - v\\_{k+2}).
             The C11 expression becomes t*(v\\_{k+3}-v\\_{k+2}) x (v\\_{k+3}-v\\_{k+2}) = 0. Contradiction.\<close>
          from heq have "fst (edge_pt_e (k+2) t) = vxe 1" "snd (edge_pt_e (k+2) t) = vye 1"
            by (by100 simp)+
          hence "vxe 1 = (1-t)*vxe(k+2) + t*vxe ?si" "vye 1 = (1-t)*vye(k+2) + t*vye ?si"
            unfolding edge_pt_e_def by (by100 simp)+
          hence "vxe 1 - vxe(k+2) = t*(vxe ?si - vxe(k+2))" "vye 1 - vye(k+2) = t*(vye ?si - vye(k+2))"
            by (by100 algebra)+
          hence "(vxe 1-vxe(k+2))*(vye ?si-vye(k+2))-(vye 1-vye(k+2))*(vxe ?si-vxe(k+2)) =
            t*(vxe ?si-vxe(k+2))*(vye ?si-vye(k+2)) - t*(vye ?si-vye(k+2))*(vxe ?si-vxe(k+2))"
            by (by100 simp)
          hence "(vxe 1-vxe(k+2))*(vye ?si-vye(k+2))-(vye 1-vye(k+2))*(vxe ?si-vxe(k+2)) = 0"
            by (by100 algebra)
          thus False using hside by (by100 linarith)
        qed
        \<comment> \<open>In sector k: cross\\_v1(k+2, p) = 0, cross\\_v1(Suc(k+2) mod ne, p) \\<le> 0.\<close>
        have hin_sec_k: "in_sector k (edge_pt_e (k+2) t)"
        proof -
          have hpt_x: "fst(edge_pt_e (k+2) t) = (1-t)*vxe(k+2) + t*vxe ?si"
            unfolding edge_pt_e_def by (by100 simp)
          have hpt_y: "snd(edge_pt_e (k+2) t) = (1-t)*vye(k+2) + t*vye ?si"
            unfolding edge_pt_e_def by (by100 simp)
          \<comment> \<open>cross\\_v1(k+2, p) = t * det(sector k) \\<ge> 0.\<close>
          have hcr_k2_expr: "cross_v1 (k+2) (edge_pt_e (k+2) t) =
            t * ((vxe(k+2)-vxe 1)*(vye ?si-vye 1) - (vye(k+2)-vye 1)*(vxe ?si-vxe 1))"
          proof -
            have "cross_v1 (k+2) (edge_pt_e (k+2) t) =
              (vxe(k+2)-vxe 1)*((1-t)*vye(k+2)+t*vye ?si-vye 1) -
              (vye(k+2)-vye 1)*((1-t)*vxe(k+2)+t*vxe ?si-vxe 1)"
              unfolding cross_v1_def using hpt_x hpt_y by (by100 simp)
            also have "\<dots> = t*((vxe(k+2)-vxe 1)*(vye ?si-vye 1)-(vye(k+2)-vye 1)*(vxe ?si-vxe 1))"
              by (by100 algebra)
            finally show ?thesis .
          qed
          from hdet_pos[rule_format, OF hk]
          have hdet_k: "(vxe(k+2)-vxe 1)*(vye ?si-vye 1) - (vye(k+2)-vye 1)*(vxe ?si-vxe 1) > 0"
            unfolding Let_def .
          have ht_ge: "t \<ge> 0" using ht unfolding top1_unit_interval_def by (by100 auto)
          have hcr_k2_ge: "cross_v1 (k+2) (edge_pt_e (k+2) t) \<ge> 0"
          proof -
            have "t * ((vxe(k+2)-vxe 1)*(vye ?si-vye 1)-(vye(k+2)-vye 1)*(vxe ?si-vxe 1)) \<ge> 0"
            proof -
              have "((vxe(k+2)-vxe 1)*(vye ?si-vye 1)-(vye(k+2)-vye 1)*(vxe ?si-vxe 1)) \<ge> 0"
                using hdet_k by (by100 linarith)
              from mult_nonneg_nonneg[OF ht_ge this] show ?thesis .
            qed
            thus ?thesis using hcr_k2_expr by (by100 linarith)
          qed
          \<comment> \<open>cross\\_v1(?si, p): direction from v\\_1 to v\\_{k+3} crossed with edge direction.
             = t * det(v\\_{k+3}-v\\_1, v\\_{k+2}-v\\_1+v\\_{k+3}-v\\_{k+2}) ... complicated.
             Simpler: = t * cross(v\\_{k+3}-v\\_1, v\\_{k+2}-v\\_1) + (1-t) * cross(v\\_{k+3}-v\\_1, v\\_{k+3}-v\\_1)
             = t * (-(det sector k)) + 0 = -t * hdet\\_pos(k) \\<le> 0.\<close>
          have hcr_si: "cross_v1 ?si (edge_pt_e (k+2) t) \<le> 0"
          proof -
            have hcr_expr: "cross_v1 ?si (edge_pt_e (k+2) t) =
              (1-t) * ((vxe ?si-vxe 1)*(vye(k+2)-vye 1) - (vye ?si-vye 1)*(vxe(k+2)-vxe 1))"
            proof -
              have "cross_v1 ?si (edge_pt_e (k+2) t) =
                (vxe ?si-vxe 1)*((1-t)*vye(k+2)+t*vye ?si-vye 1) -
                (vye ?si-vye 1)*((1-t)*vxe(k+2)+t*vxe ?si-vxe 1)"
                unfolding cross_v1_def using hpt_x hpt_y by (by100 simp)
              also have "\<dots> = (1-t)*((vxe ?si-vxe 1)*(vye(k+2)-vye 1) - (vye ?si-vye 1)*(vxe(k+2)-vxe 1))"
                by (by100 algebra)
              finally show ?thesis .
            qed
            \<comment> \<open>The factor is -det(v\\_{k+2}-v\\_1, v\\_{k+3}-v\\_1) = -hdet\\_pos(k) < 0.\<close>
            hence hfactor_neg: "(vxe ?si-vxe 1)*(vye(k+2)-vye 1) - (vye ?si-vye 1)*(vxe(k+2)-vxe 1) < 0"
            proof -
              have "(vxe ?si-vxe 1)*(vye(k+2)-vye 1) - (vye ?si-vye 1)*(vxe(k+2)-vxe 1) =
                -((vxe(k+2)-vxe 1)*(vye ?si-vye 1) - (vye(k+2)-vye 1)*(vxe ?si-vxe 1))"
                by (by100 algebra)
              thus ?thesis using hdet_k by (by100 linarith)
            qed
            have h1mt: "(1-t) \<ge> 0" using ht unfolding top1_unit_interval_def by (by100 auto)
            have hfactor_le: "(vxe ?si-vxe 1)*(vye(k+2)-vye 1) - (vye ?si-vye 1)*(vxe(k+2)-vxe 1) \<le> 0"
              using hfactor_neg by (by100 linarith)
            from mult_nonneg_nonpos[OF h1mt hfactor_le]
            show ?thesis using hcr_expr by (by100 linarith)
          qed
          show ?thesis unfolding in_sector_def using hcr_k2_ge hcr_si by (by100 simp)
        qed
        \<comment> \<open>LEAST picks some j \\<le> k.\<close>
        have "\<exists>j. j < ?nw \<and> in_sector j (edge_pt_e (k+2) t)"
          using hin_sec_k hk by (by100 blast)
        from LeastI_ex[OF this]
        have hLEAST_valid: "(LEAST j'. j' < ?nw \<and> in_sector j' (edge_pt_e (k+2) t)) < ?nw \<and>
          in_sector (LEAST j'. j' < ?nw \<and> in_sector j' (edge_pt_e (k+2) t)) (edge_pt_e (k+2) t)" .
        \<comment> \<open>For the non-spur case, ANY valid sector j containing the edge point gives the same result
           because the point is on the boundary between sectors (on edge k+2) and the affine maps
           agree on shared boundaries. The computation with sector k gives:
           s = 1-t (weight on v\\_{k+2}), tpar = t (weight on v\\_{k+3}).
           Result = 0*cxw + (1-t)*vxw k + t*vxw(k+1) = edge\\_pt\\_w(k, t).\<close>
        \<comment> \<open>Apply hphi\\_fn\\_sector at the sector selected by LEAST.\<close>
        let ?j = "(LEAST j'. j' < ?nw \<and> in_sector j' (edge_pt_e (k+2) t))"
        define j_least where "j_least = (LEAST j'. j' < ?nw \<and> in_sector j' (edge_pt_e (k+2) t))"
        have hj_eq: "(LEAST j'. j' < ?nw \<and> in_sector j' (edge_pt_e (k+2) t)) = j_least"
          unfolding j_least_def by (by100 simp)
        from hphi_fn_sector[OF hp_ne_v1 hj_eq]
        have hphi_val: "phi_fn (edge_pt_e (k+2) t) =
          (let ex = vxe(j_least+2)-vxe 1; ey = vye(j_least+2)-vye 1;
               fx = vxe(Suc(j_least+2) mod ?ne)-vxe 1; fy = vye(Suc(j_least+2) mod ?ne)-vye 1;
               det = ex*fy - ey*fx;
               dx = fst(edge_pt_e (k+2) t)-vxe 1; dy = snd(edge_pt_e (k+2) t)-vye 1;
               s = (fy*dx-fx*dy)/det; t_par = (ex*dy-ey*dx)/det in
           ((1-s-t_par)*?cxw + s*vxw j_least + t_par*vxw(Suc j_least mod ?nw),
            (1-s-t_par)*?cyw + s*vyw j_least + t_par*vyw(Suc j_least mod ?nw)))" .
        \<comment> \<open>Show LEAST = k: for t \\<in> (0,1), no j < k satisfies in\\_sector.
           At t=0/t=1, the point is a vertex shared by adjacent sectors,
           but ANY valid sector gives the same answer at vertices.\<close>
        \<comment> \<open>Use hphi\\_fn\\_sector with j = k (after showing LEAST = k).\<close>
        \<comment> \<open>Case split on t boundary values.\<close>
        show "phi_fn (edge_pt_e (k+2) t) = edge_pt_w k t"
        proof (cases "0 < t \<and> t < 1")
          case True \<comment> \<open>t \\<in> (0,1): only sector k works. LEAST = k.\<close>
          have hLEAST_k: "j_least = k"
          proof -
            \<comment> \<open>For t \\<in> (0,1), show j\\_least = k using hdet\\_general to exclude all j' \\<noteq> k.\<close>
            have ht_pos: "t > 0" and ht_lt1: "t < 1" using True by (by100 simp)+
            \<comment> \<open>cross\\_v1 decomposition at edge point.\<close>
            have hpt_x: "fst(edge_pt_e (k+2) t) = (1-t)*vxe(k+2)+t*vxe ?si"
              unfolding edge_pt_e_def by (by100 simp)
            have hpt_y: "snd(edge_pt_e (k+2) t) = (1-t)*vye(k+2)+t*vye ?si"
              unfolding edge_pt_e_def by (by100 simp)
            \<comment> \<open>The cross product of direction m with the edge point from v\\_1.\<close>
            have hcross_decomp: "\<And>m. cross_v1 m (edge_pt_e (k+2) t) =
              (1-t)*((vxe m-vxe 1)*(vye(k+2)-vye 1)-(vye m-vye 1)*(vxe(k+2)-vxe 1)) +
              t*((vxe m-vxe 1)*(vye ?si-vye 1)-(vye m-vye 1)*(vxe ?si-vxe 1))"
              unfolding cross_v1_def using hpt_x hpt_y by (by100 algebra)
            \<comment> \<open>All j' \\<noteq> k fail in\\_sector: for j'<k the second in\\_sector cond fails,
               for j'>k the first cond fails. Uses hdet\\_general.\<close>
            \<comment> \<open>For j'<k: cross\\_v1(j'+3) > 0 (from hdet\\_general), contradicting in\\_sector \\<le> 0.\<close>
            have huniq_lt: "\<forall>j'<?nw. j' < k \<longrightarrow> \<not>in_sector j' (edge_pt_e (k+2) t)"
            proof (intro allI impI)
              fix j' assume hj'nw: "j' < ?nw" and hj'k: "j' < k"
              have hj'3: "j' + 3 \<le> k + 2" using hj'k by linarith
              have hj'3_lt_ne: "j' + 3 < ?ne" using hj'k hk hne_eq by linarith
              have hj'3_ge2: "(2::nat) \<le> j' + 3" by linarith
              have hmod_eq: "Suc(j'+2) mod ?ne = j'+3"
                using hj'3_lt_ne by simp
              \<comment> \<open>cross\\_v1(j'+3, p) = (1-t)*det\\_A + t*det\\_B where both terms \\<ge> 0 and at least one > 0.\<close>
              have hdet_A: "(vxe(j'+3)-vxe 1)*(vye(k+2)-vye 1)-(vye(j'+3)-vye 1)*(vxe(k+2)-vxe 1) \<ge> 0"
              proof (cases "j'+3 < k+2")
                case True
                from hdet_general[rule_format, of "j'+3" "k+2"]
                show ?thesis using True hj'3_ge2 hk hne_eq by linarith
              next
                case False hence heq: "j'+3 = k+2" using hj'3 by linarith
                show ?thesis unfolding heq by simp
              qed
              have hsi_eq: "?si = Suc(k+2) mod ?ne" by simp
              have hdet_B: "(vxe(j'+3)-vxe 1)*(vye ?si-vye 1)-(vye(j'+3)-vye 1)*(vxe ?si-vxe 1) > 0"
              proof (cases "Suc(k+2) < ?ne")
                case True hence hsi_val: "?si = k+3" by simp
                show ?thesis
                proof (cases "j'+3 < k+3")
                  case True
                  from hdet_general[rule_format, of "j'+3" "k+3"]
                  have "(vxe(j'+3)-vxe 1)*(vye(k+3)-vye 1)-(vye(j'+3)-vye 1)*(vxe(k+3)-vxe 1) > 0"
                    using True hj'3_ge2 hk hne_eq \<open>Suc(k+2) < ?ne\<close> by linarith
                  thus ?thesis using hsi_val by simp
                next
                  case False hence "j'+3 = k+3" using hj'3 by linarith
                  hence "j' = k" by linarith
                  thus ?thesis using hj'k by linarith
                qed
              next
                case False
                hence "k + 3 = ?ne" using hk hne_eq by linarith
                hence hsi_val: "?si = 0" by simp
                from hdet_from_v1[rule_format, OF hj'3_ge2 hj'3_lt_ne]
                show ?thesis using hsi_val by simp
              qed
              have hcross_pos: "cross_v1 (j'+3) (edge_pt_e (k+2) t) > 0"
              proof -
                from hcross_decomp[of "j'+3"]
                have "cross_v1 (j'+3) (edge_pt_e (k+2) t) =
                  (1-t)*((vxe(j'+3)-vxe 1)*(vye(k+2)-vye 1)-(vye(j'+3)-vye 1)*(vxe(k+2)-vxe 1)) +
                  t*((vxe(j'+3)-vxe 1)*(vye ?si-vye 1)-(vye(j'+3)-vye 1)*(vxe ?si-vxe 1))" .
                moreover have "(1-t) \<ge> 0" using ht_lt1 by linarith
                moreover have "t > 0" using ht_pos .
                ultimately show ?thesis using hdet_A hdet_B
                  by (smt (verit) mult_nonneg_nonneg mult_pos_pos)
              qed
              have "cross_v1 (Suc(j'+2) mod ?ne) (edge_pt_e (k+2) t) > 0"
                using hcross_pos hmod_eq by simp
              thus "\<not>in_sector j' (edge_pt_e (k+2) t)"
                unfolding in_sector_def by linarith
            qed
            \<comment> \<open>For j'>k: cross\\_v1(j'+2) < 0 (from hdet\\_general reversed), contradicting \\<ge> 0.\<close>
            have huniq_gt: "\<forall>j'<?nw. j' > k \<longrightarrow> \<not>in_sector j' (edge_pt_e (k+2) t)"
            proof (intro allI impI)
              fix j' assume hj'nw: "j' < ?nw" and hj'k: "j' > k"
              have hj'2_ge2: "(2::nat) \<le> j'+2" by linarith
              have hj'2_gt_k2: "j'+2 > k+2" using hj'k by linarith
              have hj'2_lt_ne: "j'+2 < ?ne" using hj'nw hne_eq by linarith
              have hk2_ge2: "(2::nat) \<le> k+2" by linarith
              have hk2_lt_ne: "k+2 < ?ne" using hk hne_eq by linarith
              \<comment> \<open>det\\_A = det(v\\_{j'+2}-v\\_1, v\\_{k+2}-v\\_1) < 0 (reverse of hdet\\_general).\<close>
              have hdet_A_neg: "(vxe(j'+2)-vxe 1)*(vye(k+2)-vye 1)-(vye(j'+2)-vye 1)*(vxe(k+2)-vxe 1) < 0"
              proof -
                from hdet_general[rule_format, of "k+2" "j'+2"]
                have hpos: "(vxe(k+2)-vxe 1)*(vye(j'+2)-vye 1)-(vye(k+2)-vye 1)*(vxe(j'+2)-vxe 1) > 0"
                  using hk2_ge2 hj'2_gt_k2 hj'2_lt_ne by linarith
                have "(vxe(j'+2)-vxe 1)*(vye(k+2)-vye 1)-(vye(j'+2)-vye 1)*(vxe(k+2)-vxe 1) =
                  -((vxe(k+2)-vxe 1)*(vye(j'+2)-vye 1)-(vye(k+2)-vye 1)*(vxe(j'+2)-vxe 1))"
                  by (by100 algebra)
                thus ?thesis using hpos by linarith
              qed
              \<comment> \<open>si = k+3 (k < nw-1 since j'>k and j'<nw forces k \\<le> nw-2).\<close>
              have hk_lt_nw1: "k < ?nw - 1" using hj'k hj'nw by linarith
              hence hsi_lt: "Suc(k+2) < ?ne" using hne_eq by linarith
              hence hsi_val: "?si = k+3" by simp
              \<comment> \<open>det\\_B = det(v\\_{j'+2}-v\\_1, v\\_{k+3}-v\\_1) \\<le> 0.\<close>
              have hdet_B_le: "(vxe(j'+2)-vxe 1)*(vye ?si-vye 1)-(vye(j'+2)-vye 1)*(vxe ?si-vxe 1) \<le> 0"
              proof (cases "j'+2 > k+3")
                case True
                from hdet_general[rule_format, of "k+3" "j'+2"]
                have "(vxe(k+3)-vxe 1)*(vye(j'+2)-vye 1)-(vye(k+3)-vye 1)*(vxe(j'+2)-vxe 1) > 0"
                  using True hj'2_lt_ne hsi_lt by linarith
                have "(vxe(j'+2)-vxe 1)*(vye(k+3)-vye 1)-(vye(j'+2)-vye 1)*(vxe(k+3)-vxe 1) =
                  -((vxe(k+3)-vxe 1)*(vye(j'+2)-vye 1)-(vye(k+3)-vye 1)*(vxe(j'+2)-vxe 1))"
                  by (by100 algebra)
                hence "(vxe(j'+2)-vxe 1)*(vye(k+3)-vye 1)-(vye(j'+2)-vye 1)*(vxe(k+3)-vxe 1) < 0"
                  using \<open>(vxe(k+3)-vxe 1)*(vye(j'+2)-vye 1)-(vye(k+3)-vye 1)*(vxe(j'+2)-vxe 1) > 0\<close> by linarith
                thus ?thesis using hsi_val by simp
              next
                case False hence heq: "j'+2 = k+3" using hj'k by linarith
                show ?thesis unfolding heq hsi_val by simp
              qed
              \<comment> \<open>cross\\_v1(j'+2, p) = (1-t)*det\\_A + t*det\\_B < 0.\<close>
              have hcross_neg: "cross_v1 (j'+2) (edge_pt_e (k+2) t) < 0"
              proof -
                from hcross_decomp[of "j'+2"]
                have "cross_v1 (j'+2) (edge_pt_e (k+2) t) =
                  (1-t)*((vxe(j'+2)-vxe 1)*(vye(k+2)-vye 1)-(vye(j'+2)-vye 1)*(vxe(k+2)-vxe 1)) +
                  t*((vxe(j'+2)-vxe 1)*(vye ?si-vye 1)-(vye(j'+2)-vye 1)*(vxe ?si-vxe 1))" .
                moreover have "(1-t) > 0" using ht_pos ht_lt1 by linarith
                moreover have "t \<ge> 0" using ht_pos by linarith
                ultimately show ?thesis using hdet_A_neg hdet_B_le
                  by (smt (verit) mult_pos_neg mult_nonneg_nonpos)
              qed
              show "\<not>in_sector j' (edge_pt_e (k+2) t)"
                unfolding in_sector_def using hcross_neg by linarith
            qed
            have huniq: "\<forall>j'. j' < ?nw \<and> in_sector j' (edge_pt_e (k+2) t) \<longrightarrow> j' = k"
              using huniq_lt huniq_gt by (by100 fastforce)
            from LeastI_ex[OF \<open>\<exists>j. j < ?nw \<and> in_sector j (edge_pt_e (k+2) t)\<close>]
            show "j_least = k" using huniq unfolding j_least_def by (by100 blast)
          qed
          have hLEAST_is_k: "(LEAST j'. j' < ?nw \<and> in_sector j' (edge_pt_e (k+2) t)) = k"
            using hj_eq hLEAST_k by (by100 simp)
          from hphi_fn_sector[OF hp_ne_v1 hLEAST_is_k]
          have hphi_at_k: "phi_fn (edge_pt_e (k+2) t) =
            (let ex = vxe(k+2)-vxe 1; ey = vye(k+2)-vye 1;
                 fx = vxe ?si-vxe 1; fy = vye ?si-vye 1;
                 det = ex*fy - ey*fx;
                 dx = fst(edge_pt_e (k+2) t)-vxe 1; dy = snd(edge_pt_e (k+2) t)-vye 1;
                 s = (fy*dx-fx*dy)/det; t_par = (ex*dy-ey*dx)/det in
             ((1-s-t_par)*?cxw + s*vxw k + t_par*vxw(Suc k mod ?nw),
              (1-s-t_par)*?cyw + s*vyw k + t_par*vyw(Suc k mod ?nw)))" .
          have hpt_x2: "fst(edge_pt_e (k+2) t)-vxe 1 = (1-t)*(vxe(k+2)-vxe 1)+t*(vxe ?si-vxe 1)"
          proof -
            have "fst(edge_pt_e (k+2) t) = (1-t)*vxe(k+2) + t*vxe ?si"
              unfolding edge_pt_e_def by (by100 simp)
            thus ?thesis by (by100 algebra)
          qed
          have hpt_y2: "snd(edge_pt_e (k+2) t)-vye 1 = (1-t)*(vye(k+2)-vye 1)+t*(vye ?si-vye 1)"
          proof -
            have "snd(edge_pt_e (k+2) t) = (1-t)*vye(k+2) + t*vye ?si"
              unfolding edge_pt_e_def by (by100 simp)
            thus ?thesis by (by100 algebra)
          qed
          have hdet_k_ne0: "(vxe(k+2)-vxe 1)*(vye ?si-vye 1)-(vye(k+2)-vye 1)*(vxe ?si-vxe 1) \<noteq> 0"
          proof -
            from hdet_pos[rule_format, OF hk] show ?thesis unfolding Let_def by (by100 linarith)
          qed
          have hs_num: "(vye ?si-vye 1)*((1-t)*(vxe(k+2)-vxe 1)+t*(vxe ?si-vxe 1)) -
              (vxe ?si-vxe 1)*((1-t)*(vye(k+2)-vye 1)+t*(vye ?si-vye 1)) =
              (1-t)*((vxe(k+2)-vxe 1)*(vye ?si-vye 1)-(vye(k+2)-vye 1)*(vxe ?si-vxe 1))"
            by (by100 algebra)
          have htpar_num: "(vxe(k+2)-vxe 1)*((1-t)*(vye(k+2)-vye 1)+t*(vye ?si-vye 1)) -
              (vye(k+2)-vye 1)*((1-t)*(vxe(k+2)-vxe 1)+t*(vxe ?si-vxe 1)) =
              t*((vxe(k+2)-vxe 1)*(vye ?si-vye 1)-(vye(k+2)-vye 1)*(vxe ?si-vxe 1))"
            by (by100 algebra)
          show ?thesis
            using hphi_at_k hpt_x2 hpt_y2 hs_num htpar_num hdet_k_ne0
            unfolding edge_pt_w_def Let_def
            by (by5000 simp)
        next
          case False \<comment> \<open>t = 0 or t = 1: boundary vertices.\<close>
          hence "t = 0 \<or> t = 1" using ht unfolding top1_unit_interval_def by (by100 auto)
          thus ?thesis
          proof (elim disjE)
            assume "t = 0"
            hence "edge_pt_e (k+2) t = (vxe(k+2), vye(k+2))"
              unfolding edge_pt_e_def by (by100 simp)
            hence "phi_fn (edge_pt_e (k+2) t) = phi_fn (vxe(k+2), vye(k+2))" by (by100 simp)
            also have "\<dots> = (vxw k, vyw k)" using hphi_at_vertex hk by (by100 blast)
            also have "(vxw k, vyw k) = edge_pt_w k 0" unfolding edge_pt_w_def by (by100 simp)
            finally show ?thesis using \<open>t = 0\<close> by (by100 simp)
          next
            assume "t = 1"
            hence "edge_pt_e (k+2) t = (vxe ?si, vye ?si)"
              unfolding edge_pt_e_def by (by100 simp)
            \<comment> \<open>phi\\_fn(v\\_{si}) = u\\_{k+1 mod nw}. This uses hphi\\_at\\_vertex or similar.\<close>
            \<comment> \<open>phi(v\\_{si}) = u\\_{k+1 mod nw}. Case: si = k+3 (k < nw-1) or si = 0 (k = nw-1).\<close>
            show ?thesis
            proof (cases "k + 3 < ?ne")
              case True \<comment> \<open>si = k+3, so v\\_{si} = v\\_{(k+1)+2}.\<close>
              hence hsi_eq: "?si = k + 3" by (by100 simp)
              hence "k + 1 < ?nw" using True hne_eq by (by100 linarith)
              have hk1_eq: "(k+1)+2 = k+3" by (by100 simp)
              from hphi_at_vertex[rule_format, OF \<open>k + 1 < ?nw\<close>]
              have "phi_fn (vxe((k+1)+2), vye((k+1)+2)) = (vxw(k+1), vyw(k+1))" .
              hence hphi_at_k3: "phi_fn (vxe(k+3), vye(k+3)) = (vxw(k+1), vyw(k+1))"
                unfolding hk1_eq by (by100 simp)
              hence "phi_fn (vxe ?si, vye ?si) = (vxw(k+1), vyw(k+1))" using hsi_eq by (by100 simp)
              moreover have "edge_pt_w k 1 = (vxw(Suc k mod ?nw), vyw(Suc k mod ?nw))"
                unfolding edge_pt_w_def by (by100 simp)
              moreover have "Suc k mod ?nw = k + 1"
                using \<open>k + 1 < ?nw\<close> by (by100 simp)
              ultimately have "phi_fn (vxe ?si, vye ?si) = edge_pt_w k 1" by (by100 simp)
              moreover have "edge_pt_e (k+2) 1 = (vxe ?si, vye ?si)"
                unfolding edge_pt_e_def by (by100 simp)
              ultimately show ?thesis using \<open>t = 1\<close> by (by100 simp)
            next
              case False \<comment> \<open>k+3 = ne, so si = 0 and v\\_{si} = v\\_0.\<close>
              hence "k + 3 = ?ne" using hk hne_eq by (by100 linarith)
              hence hsi_eq: "?si = 0" by (by100 simp)
              \<comment> \<open>phi(v\\_0) = (vxw 0, vyw 0) from hphi\\_on\\_spur0 at t=0.\<close>
              have "0 \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
              from hphi_on_spur0[rule_format, OF this]
              have "phi_fn (edge_pt_e 0 0) = ((1-0)*vxw 0 + 0*?cxw, (1-0)*vyw 0 + 0*?cyw)" .
              hence hphi_v0: "phi_fn (edge_pt_e 0 0) = (vxw 0, vyw 0)" by (by100 simp)
              have "Suc 0 mod ?ne = 1" using hlen hne_eq by (by100 simp)
              hence "edge_pt_e 0 0 = (vxe 0, vye 0)" unfolding edge_pt_e_def by (by100 simp)
              hence "phi_fn (vxe 0, vye 0) = (vxw 0, vyw 0)" using hphi_v0 by (by100 simp)
              hence "phi_fn (vxe ?si, vye ?si) = (vxw 0, vyw 0)" using hsi_eq by (by100 simp)
              moreover have "edge_pt_w k 1 = (vxw(Suc k mod ?nw), vyw(Suc k mod ?nw))"
                unfolding edge_pt_w_def by (by100 simp)
              moreover have "Suc k mod ?nw = 0"
              proof -
                have "k = ?nw - 1" using \<open>k + 3 = ?ne\<close> hne_eq by (by100 linarith)
                hence "Suc k = ?nw" using hnw_pos by (by100 linarith)
                thus ?thesis by (by100 simp)
              qed
              ultimately have "phi_fn (vxe ?si, vye ?si) = edge_pt_w k 1" by (by100 simp)
              moreover have "edge_pt_e (k+2) 1 = (vxe ?si, vye ?si)"
                unfolding edge_pt_e_def by (by100 simp)
              ultimately show ?thesis using \<open>t = 1\<close> by (by100 simp)
            qed
          qed
        qed
      qed
      \<comment> \<open>Now prove all 12 properties of phi\\_fn.\<close>
      have prop1: "\<forall>p \<in> P_e. phi_fn p \<in> P_w"
      proof (intro ballI)
        fix p assume hp: "p \<in> P_e"
        from hfan_cover[rule_format, OF hp]
        show "phi_fn p \<in> P_w"
        proof (elim disjE exE conjE)
          assume "p = (vxe 1, vye 1)"
          hence "phi_fn p = (?cxw, ?cyw)" unfolding phi_fn_def by (by100 simp)
          thus ?thesis using hcw_in_Pw by simp
        next
          fix j0 assume hj0: "j0 < ?nw" and hin0: "in_sector j0 p"
          show "phi_fn p \<in> P_w"
          proof (cases "p = (vxe 1, vye 1)")
            case True
            hence "phi_fn p = (?cxw, ?cyw)" unfolding phi_fn_def by (by100 simp)
            thus ?thesis using hcw_in_Pw by simp
          next
            case False
            hence hp_ne_v1: "p \<noteq> (vxe 1, vye 1)" .
          have hexist: "\<exists>j'. j' < ?nw \<and> in_sector j' p" using hj0 hin0 by blast
          define j where "j = (LEAST j'. j' < ?nw \<and> in_sector j' p)"
          from LeastI_ex[OF hexist] have hj: "j < ?nw" and hin: "in_sector j p"
            unfolding j_def by auto
          let ?si = "Suc(j+2) mod ?ne"
          let ?dx = "fst p - vxe 1" and ?dy = "snd p - vye 1"
          let ?s = "phi_s2 (j+2) ?si ?dx ?dy"
          let ?t = "phi_t2 (j+2) ?si ?dx ?dy"
          \<comment> \<open>From in\\_sector: cross\\_v1(j+2,p) \\<ge> 0 and cross\\_v1(si,p) \\<le> 0.\<close>
          from hin have hcr_ge: "cross_v1 (j+2) p \<ge> 0" and hcr_le: "cross_v1 ?si p \<le> 0"
            unfolding in_sector_def by auto
          \<comment> \<open>det > 0.\<close>
          from hdet_pos[rule_format, OF hj]
          have hdet_pos_j: "(vxe(j+2)-vxe 1)*(vye ?si-vye 1)-(vye(j+2)-vye 1)*(vxe ?si-vxe 1) > 0"
            by (by100 simp)
          \<comment> \<open>t\\_par = cross\\_v1(j+2, p) / det \\<ge> 0.\<close>
          have ht_ge: "?t \<ge> 0"
          proof -
            have "?t = cross_v1 (j+2) p / ((vxe(j+2)-vxe 1)*(vye ?si-vye 1)-(vye(j+2)-vye 1)*(vxe ?si-vxe 1))"
              unfolding phi_t2_def cross_v1_def Let_def by (by100 simp)
            thus ?thesis using hcr_ge hdet_pos_j using divide_nonneg_pos by (by100 simp)
          qed
          \<comment> \<open>s = -cross\\_v1(si, p) / det \\<ge> 0.\<close>
          have hs_ge: "?s \<ge> 0"
          proof -
            have heq: "?s = -cross_v1 ?si p / ((vxe(j+2)-vxe 1)*(vye ?si-vye 1)-(vye(j+2)-vye 1)*(vxe ?si-vxe 1))"
              unfolding phi_s2_def cross_v1_def Let_def by (by100 algebra)
            have "-cross_v1 ?si p \<ge> 0" using hcr_le by linarith
            from divide_nonneg_pos[OF this hdet_pos_j]
            show ?thesis using heq by linarith
          qed
          \<comment> \<open>1-s-t \\<ge> 0: p is on the v\\_1 side of edge v\\_{j+2}v\\_{si}.\<close>
          have hst_le: "?s + ?t \<le> 1"
          proof -
            let ?det = "(vxe(j+2)-vxe 1)*(vye ?si-vye 1)-(vye(j+2)-vye 1)*(vxe ?si-vxe 1)"
            have hst_expr: "?s + ?t = (cross_v1 (j+2) p - cross_v1 ?si p) / ?det"
            proof -
              have "?t = cross_v1 (j+2) p / ?det"
                unfolding phi_t2_def cross_v1_def Let_def by (by100 simp)
              moreover have "?s = -cross_v1 ?si p / ?det"
                unfolding phi_s2_def cross_v1_def Let_def by (by100 algebra)
              ultimately show ?thesis
                using diff_divide_distrib[of "cross_v1 (j+2) p" "cross_v1 ?si p" ?det, symmetric]
                by linarith
            qed
            \<comment> \<open>1-s-t \\<ge> 0 via C11 at edge j+2: all vertices on correct side.
               edge\\_cross(p) = det(v\\_{si}-v\\_{j+2}, p-v\\_{j+2}) \\<ge> 0 by C11 + linearity.
               Algebraically: cross\\_v1(j+2,p) - cross\\_v1(si,p) - det = -edge\\_cross(p) \\<le> 0.\<close>
            have hgoal: "cross_v1 (j+2) p - cross_v1 ?si p \<le> ?det"
            proof -
              from hp obtain coeffs where hcoeffs: "(\<forall>i<?ne. coeffs i \<ge> 0)"
                "(\<Sum>i<?ne. coeffs i) = 1" "fst p = (\<Sum>i<?ne. coeffs i * vxe i)"
                "snd p = (\<Sum>i<?ne. coeffs i * vye i)"
                using hC5_e by (by100 auto)
              have hj2_lt: "j+2 < ?ne" using hj hne_eq by linarith
              \<comment> \<open>C11 at edge j+2 gives: for all i \\<noteq> j+2, i \\<noteq> si:
                 det(v\\_{si}-v\\_{j+2}, v\\_i-v\\_{j+2}) > 0.\<close>
              have hedge: "\<forall>i<?ne. (vxe ?si-vxe(j+2))*(vye i-vye(j+2))-(vye ?si-vye(j+2))*(vxe i-vxe(j+2)) \<ge> 0"
              proof (intro allI impI)
                fix i assume hi: "i < ?ne"
                show "(vxe ?si-vxe(j+2))*(vye i-vye(j+2))-(vye ?si-vye(j+2))*(vxe i-vxe(j+2)) \<ge> 0"
                proof (cases "i = j+2 \<or> i = ?si")
                  case True thus ?thesis by (elim disjE) simp_all
                next
                  case False hence "i \<noteq> j+2" "i \<noteq> Suc(j+2) mod ?ne" by auto
                  from hC11_e[rule_format, OF hj2_lt hi this]
                  have hC11_inst: "(vxe i-vxe(j+2))*(vye(Suc(j+2) mod ?ne)-vye(j+2))-(vye i-vye(j+2))*(vxe(Suc(j+2) mod ?ne)-vxe(j+2)) < 0" .
                  have "(vxe ?si-vxe(j+2))*(vye i-vye(j+2))-(vye ?si-vye(j+2))*(vxe i-vxe(j+2))
                    = -((vxe i-vxe(j+2))*(vye(Suc(j+2) mod ?ne)-vye(j+2))-(vye i-vye(j+2))*(vxe(Suc(j+2) mod ?ne)-vxe(j+2)))"
                    by (by100 algebra)
                  thus ?thesis using hC11_inst by linarith
                qed
              qed
              \<comment> \<open>edge\\_cross(p) \\<ge> 0 by linearity.\<close>
              have hedge_p: "(vxe ?si-vxe(j+2))*(snd p-vye(j+2))-(vye ?si-vye(j+2))*(fst p-vxe(j+2)) \<ge> 0"
              proof -
                \<comment> \<open>edge\\_cross(p) = \\<Sum> \\<lambda>\\_i * edge\\_cross(v\\_i).\<close>
                let ?a = "vxe ?si - vxe(j+2)" and ?b = "vye ?si - vye(j+2)"
                have hedy: "snd p - vye(j+2) = (\<Sum>i<?ne. coeffs i * (vye i - vye(j+2)))"
                proof -
                  have "(\<Sum>i<?ne. coeffs i * (vye i - vye(j+2)))
                    = (\<Sum>i<?ne. coeffs i * vye i) - (\<Sum>i<?ne. coeffs i * vye(j+2))"
                    by (simp add: sum_subtractf right_diff_distrib)
                  also have "(\<Sum>i<?ne. coeffs i * vye(j+2)) = (\<Sum>i<?ne. coeffs i) * vye(j+2)"
                    by (simp add: sum_distrib_right[symmetric])
                  finally show ?thesis using hcoeffs(2,4) by simp
                qed
                have hedx: "fst p - vxe(j+2) = (\<Sum>i<?ne. coeffs i * (vxe i - vxe(j+2)))"
                proof -
                  have "(\<Sum>i<?ne. coeffs i * (vxe i - vxe(j+2)))
                    = (\<Sum>i<?ne. coeffs i * vxe i) - (\<Sum>i<?ne. coeffs i * vxe(j+2))"
                    by (simp add: sum_subtractf right_diff_distrib)
                  also have "(\<Sum>i<?ne. coeffs i * vxe(j+2)) = (\<Sum>i<?ne. coeffs i) * vxe(j+2)"
                    by (simp add: sum_distrib_right[symmetric])
                  finally show ?thesis using hcoeffs(2,3) by simp
                qed
                have "?a * (snd p - vye(j+2)) - ?b * (fst p - vxe(j+2))
                  = ?a * (\<Sum>i<?ne. coeffs i * (vye i - vye(j+2)))
                  - ?b * (\<Sum>i<?ne. coeffs i * (vxe i - vxe(j+2)))" using hedy hedx by simp
                also have "\<dots> = (\<Sum>i<?ne. ?a * (coeffs i * (vye i - vye(j+2))))
                  - (\<Sum>i<?ne. ?b * (coeffs i * (vxe i - vxe(j+2))))"
                  by (simp add: sum_distrib_left[symmetric])
                also have "\<dots> = (\<Sum>i<?ne. ?a * (coeffs i * (vye i - vye(j+2)))
                                          - ?b * (coeffs i * (vxe i - vxe(j+2))))"
                  using sum_subtractf[of "\<lambda>i. ?a*(coeffs i*(vye i-vye(j+2)))"
                    "\<lambda>i. ?b*(coeffs i*(vxe i-vxe(j+2)))" "{..<?ne}"] by (by100 simp)
                also have "\<dots> = (\<Sum>i<?ne. coeffs i * (?a * (vye i - vye(j+2)) - ?b * (vxe i - vxe(j+2))))"
                proof -
                  have "\<And>i. ?a * (coeffs i * (vye i - vye(j+2))) - ?b * (coeffs i * (vxe i - vxe(j+2)))
                    = coeffs i * (?a * (vye i - vye(j+2)) - ?b * (vxe i - vxe(j+2)))"
                    by (by100 algebra)
                  thus ?thesis by simp
                qed
                finally have hlin: "?a * (snd p - vye(j+2)) - ?b * (fst p - vxe(j+2))
                  = (\<Sum>i<?ne. coeffs i * (?a * (vye i - vye(j+2)) - ?b * (vxe i - vxe(j+2))))" .
                \<comment> \<open>Each term = coeffs i * edge\\_cross(v\\_i) \\<ge> 0.\<close>
                have hterms: "\<forall>i<?ne. coeffs i * (?a * (vye i - vye(j+2)) - ?b * (vxe i - vxe(j+2))) \<ge> 0"
                proof (intro allI impI)
                  fix i assume "i < ?ne"
                  from hedge[rule_format, OF this]
                  have "0 \<le> (vxe ?si-vxe(j+2))*(vye i-vye(j+2))-(vye ?si-vye(j+2))*(vxe i-vxe(j+2))" by linarith
                  hence "0 \<le> ?a * (vye i - vye(j+2)) - ?b * (vxe i - vxe(j+2))" by simp
                  from mult_nonneg_nonneg[OF hcoeffs(1)[rule_format, OF \<open>i < ?ne\<close>] this]
                  show "coeffs i * (?a * (vye i - vye(j+2)) - ?b * (vxe i - vxe(j+2))) \<ge> 0" .
                qed
                hence "(\<Sum>i<?ne. coeffs i * (?a * (vye i - vye(j+2)) - ?b * (vxe i - vxe(j+2)))) \<ge> 0"
                  by (intro sum_nonneg) blast
                thus ?thesis using hlin by linarith
              qed
              \<comment> \<open>Algebraically: diff - det = -edge\\_cross(p).\<close>
              have "cross_v1 (j+2) p - cross_v1 ?si p - ?det
                = -((vxe ?si-vxe(j+2))*(snd p-vye(j+2))-(vye ?si-vye(j+2))*(fst p-vxe(j+2)))"
                unfolding cross_v1_def by (by100 algebra)
              thus ?thesis using hedge_p by linarith
            qed
            have "(cross_v1 (j+2) p - cross_v1 ?si p) / ?det \<le> 1"
              using hgoal hdet_pos_j pos_divide_le_eq[of ?det] by (by100 simp)
            thus ?thesis using hst_expr by linarith
          qed
          \<comment> \<open>phi\\_fn(p) is a convex combination of vertices of P\\_w -> \\<in> P\\_w.\<close>
          \<comment> \<open>phi\\_fn(p) = (1-s-t)*centroid + s*u\\_j + t*u\\_{j+1} where centroid \\<in> P\\_w.\<close>
          \<comment> \<open>Since centroid = (1/nw)*\\<Sum> u\\_i, phi\\_fn(p) = \\<Sum> c\\_i * u\\_i with c\\_i \\<ge> 0, \\<Sum> = 1.\<close>
          \<comment> \<open>Use hphi\\_fn\\_decomp with LEAST = j.\<close>
          obtain a b where hab: "p = (a, b)" by (cases p) auto
          have hab_ne: "(a, b) \<noteq> (vxe 1, vye 1)" using hp_ne_v1 hab by simp
          have hLEAST_j: "(LEAST j'. j' < ?nw \<and> in_sector j' (a, b)) = j"
            unfolding j_def using hab by simp
          from hphi_fn_decomp[OF hab_ne hLEAST_j]
          have hphi_eq_ab: "phi_fn (a, b) = ((1 - phi_s2 (j+2) ?si (a-vxe 1) (b-vye 1)
                           - phi_t2 (j+2) ?si (a-vxe 1) (b-vye 1))*?cxw
                         + phi_s2 (j+2) ?si (a-vxe 1) (b-vye 1)*vxw j
                         + phi_t2 (j+2) ?si (a-vxe 1) (b-vye 1)*vxw(Suc j mod ?nw),
                         (1 - phi_s2 (j+2) ?si (a-vxe 1) (b-vye 1)
                           - phi_t2 (j+2) ?si (a-vxe 1) (b-vye 1))*?cyw
                         + phi_s2 (j+2) ?si (a-vxe 1) (b-vye 1)*vyw j
                         + phi_t2 (j+2) ?si (a-vxe 1) (b-vye 1)*vyw(Suc j mod ?nw))" .
          \<comment> \<open>Since p=(a,b): phi\\_s2(..., a-vxe 1, b-vye 1) = ?s, similarly for t.\<close>
          have hs_eq: "phi_s2 (j+2) ?si (a-vxe 1) (b-vye 1) = ?s" using hab by simp
          have ht_eq: "phi_t2 (j+2) ?si (a-vxe 1) (b-vye 1) = ?t" using hab by simp
          have hphi_eq: "phi_fn p = ((1-?s-?t)*?cxw + ?s*vxw j + ?t*vxw(Suc j mod ?nw),
                                     (1-?s-?t)*?cyw + ?s*vyw j + ?t*vyw(Suc j mod ?nw))"
            using hphi_eq_ab hs_eq ht_eq hab by simp
          \<comment> \<open>Construct convex hull coefficients for P\\_w.\<close>
          have h1st: "1 - ?s - ?t \<ge> 0" using hst_le hs_ge ht_ge by linarith
          \<comment> \<open>centroid \\<in> P\\_w, u\\_j \\<in> P\\_w, u\\_{j+1} \\<in> P\\_w.\<close>
          have huj: "(vxw j, vyw j) \<in> P_w" using hC4_w hj by (by100 blast)
          have hjm: "Suc j mod ?nw < ?nw" using hnw_pos by simp
          have huj1: "(vxw (Suc j mod ?nw), vyw (Suc j mod ?nw)) \<in> P_w"
            using hC4_w hjm by (by100 blast)
          \<comment> \<open>Convex combination of three P\\_w elements with non-negative weights summing to 1.\<close>
          \<comment> \<open>centroid \\<in> P\\_w gives \\<exists>coeffs\\_c. u\\_j \\<in> P\\_w gives \\<exists>coeffs\\_j. Combine.\<close>
          \<comment> \<open>Construct explicit convex hull coefficients for phi\\_fn(p) \\<in> P\\_w.\<close>
          \<comment> \<open>centroid = (1/nw) * \\<Sum> u\\_i. So phi\\_fn(p) = \\<Sum> c\\_i * u\\_i where
             c\\_i = (1-s-t)/nw + s*(if i=j then 1 else 0) + t*(if i=Suc j mod nw then 1 else 0).\<close>
          define c_w where "c_w i = (1-?s-?t)/(real ?nw) + (if i=j then ?s else 0)
            + (if i = Suc j mod ?nw then ?t else 0)" for i
          have hcw_nn: "\<forall>i<?nw. c_w i \<ge> 0"
          proof (intro allI impI)
            fix i assume "i < ?nw"
            have "(1-?s-?t) / real ?nw \<ge> 0" using h1st hnw_pos by (by100 simp)
            moreover have "(if i=j then ?s else 0) \<ge> 0" using hs_ge by simp
            moreover have "(if i = Suc j mod ?nw then ?t else 0) \<ge> 0" using ht_ge by simp
            ultimately show "c_w i \<ge> 0" unfolding c_w_def by linarith
          qed
          have hcw_sum: "(\<Sum>i<?nw. c_w i) = 1"
          proof -
            have "(\<Sum>i<?nw. c_w i) = (\<Sum>i<?nw. (1-?s-?t)/(real ?nw))
              + (\<Sum>i<?nw. (if i=j then ?s else 0))
              + (\<Sum>i<?nw. (if i = Suc j mod ?nw then ?t else 0))"
              unfolding c_w_def by (simp add: sum.distrib)
            also have "(\<Sum>i<?nw. (1-?s-?t)/(real ?nw)) = (1-?s-?t)"
              using hnw_pos by simp
            also have "(\<Sum>i<?nw. (if i=j then ?s else 0)) = ?s"
              using hj by simp
            also have "(\<Sum>i<?nw. (if i = Suc j mod ?nw then ?t else 0)) = ?t"
              using hjm by simp
            finally show ?thesis by simp
          qed
          have hcw_x: "fst(phi_fn p) = (\<Sum>i<?nw. c_w i * vxw i)"
          proof -
            have "(\<Sum>i<?nw. c_w i * vxw i) = (\<Sum>i<?nw. ((1-?s-?t)/(real ?nw)) * vxw i)
              + (\<Sum>i<?nw. (if i=j then ?s else 0) * vxw i)
              + (\<Sum>i<?nw. (if i = Suc j mod ?nw then ?t else 0) * vxw i)"
              unfolding c_w_def by (simp add: sum.distrib algebra_simps)
            also have "(\<Sum>i<?nw. ((1-?s-?t)/(real ?nw)) * vxw i) = (1-?s-?t) * ?cxw"
            proof -
              have "(\<Sum>i<?nw. ((1-?s-?t)/(real ?nw)) * vxw i) = ((1-?s-?t)/(real ?nw)) * (\<Sum>i<?nw. vxw i)"
                by (simp add: sum_distrib_left)
              also have "\<dots> = (1-?s-?t) * ((\<Sum>i<?nw. vxw i) / real ?nw)" by (by100 simp)
              finally show ?thesis by simp
            qed
            also have "(\<Sum>i<?nw. (if i=j then ?s else 0) * vxw i) = ?s * vxw j"
            proof -
              have "(\<Sum>i<?nw. (if i=j then ?s else 0) * vxw i) = (\<Sum>i\<in>{j}. ?s * vxw i)"
                using hj by (intro sum.mono_neutral_cong_right) auto
              also have "\<dots> = ?s * vxw j" by simp
              finally show ?thesis .
            qed
            also have "(\<Sum>i<?nw. (if i = Suc j mod ?nw then ?t else 0) * vxw i) = ?t * vxw(Suc j mod ?nw)"
            proof -
              have "(\<Sum>i<?nw. (if i = Suc j mod ?nw then ?t else 0) * vxw i) = (\<Sum>i\<in>{Suc j mod ?nw}. ?t * vxw i)"
                using hjm by (intro sum.mono_neutral_cong_right) auto
              also have "\<dots> = ?t * vxw(Suc j mod ?nw)" by simp
              finally show ?thesis .
            qed
            finally show ?thesis using hphi_eq by simp
          qed
          have hcw_y: "snd(phi_fn p) = (\<Sum>i<?nw. c_w i * vyw i)"
          proof -
            have "(\<Sum>i<?nw. c_w i * vyw i) = (\<Sum>i<?nw. ((1-?s-?t)/(real ?nw)) * vyw i)
              + (\<Sum>i<?nw. (if i=j then ?s else 0) * vyw i)
              + (\<Sum>i<?nw. (if i = Suc j mod ?nw then ?t else 0) * vyw i)"
              unfolding c_w_def by (simp add: sum.distrib algebra_simps)
            also have "(\<Sum>i<?nw. ((1-?s-?t)/(real ?nw)) * vyw i) = (1-?s-?t) * ?cyw"
            proof -
              have "(\<Sum>i<?nw. ((1-?s-?t)/(real ?nw)) * vyw i) = ((1-?s-?t)/(real ?nw)) * (\<Sum>i<?nw. vyw i)"
                by (simp add: sum_distrib_left)
              also have "\<dots> = (1-?s-?t) * ((\<Sum>i<?nw. vyw i) / real ?nw)" by (by100 simp)
              finally show ?thesis by simp
            qed
            also have "(\<Sum>i<?nw. (if i=j then ?s else 0) * vyw i) = ?s * vyw j"
            proof -
              have "(\<Sum>i<?nw. (if i=j then ?s else 0) * vyw i) = (\<Sum>i\<in>{j}. ?s * vyw i)"
                using hj by (intro sum.mono_neutral_cong_right) auto
              also have "\<dots> = ?s * vyw j" by simp
              finally show ?thesis .
            qed
            also have "(\<Sum>i<?nw. (if i = Suc j mod ?nw then ?t else 0) * vyw i) = ?t * vyw(Suc j mod ?nw)"
            proof -
              have "(\<Sum>i<?nw. (if i = Suc j mod ?nw then ?t else 0) * vyw i) = (\<Sum>i\<in>{Suc j mod ?nw}. ?t * vyw i)"
                using hjm by (intro sum.mono_neutral_cong_right) auto
              also have "\<dots> = ?t * vyw(Suc j mod ?nw)" by simp
              finally show ?thesis .
            qed
            finally show ?thesis using hphi_eq by simp
          qed
          show ?thesis unfolding hC5_w
            using hcw_nn hcw_sum hcw_x hcw_y by (by100 auto)
          qed
        qed
      qed
      \<comment> \<open>phi\\_fn on sector j equals the affine map for ALL p in sector j.\<close>
      have hphi_affine_on_sector: "\<forall>j<?nw. \<forall>p\<in>P_e. in_sector j p \<longrightarrow>
        phi_fn (fst p, snd p) = (let ex = vxe(j+2)-vxe 1; ey = vye(j+2)-vye 1;
            fx = vxe(Suc(j+2) mod ?ne)-vxe 1; fy = vye(Suc(j+2) mod ?ne)-vye 1;
            det = ex*fy-ey*fx; dx = fst p-vxe 1; dy = snd p-vye 1;
            s = (fy*dx-fx*dy)/det; t_par = (ex*dy-ey*dx)/det
        in ((1-s-t_par)*?cxw + s*vxw j + t_par*vxw(Suc j mod ?nw),
            (1-s-t_par)*?cyw + s*vyw j + t_par*vyw(Suc j mod ?nw)))"
      proof (intro allI ballI impI)
        fix j p assume hj: "j < ?nw" and hp: "p \<in> P_e" and hin: "in_sector j p"
        show "phi_fn (fst p, snd p) = (let ex = vxe(j+2)-vxe 1; ey = vye(j+2)-vye 1;
            fx = vxe(Suc(j+2) mod ?ne)-vxe 1; fy = vye(Suc(j+2) mod ?ne)-vye 1;
            det = ex*fy-ey*fx; dx = fst p-vxe 1; dy = snd p-vye 1;
            s = (fy*dx-fx*dy)/det; t_par = (ex*dy-ey*dx)/det
        in ((1-s-t_par)*?cxw + s*vxw j + t_par*vxw(Suc j mod ?nw),
            (1-s-t_par)*?cyw + s*vyw j + t_par*vyw(Suc j mod ?nw)))"
        proof (cases "(fst p, snd p) = (vxe 1, vye 1)")
          case True
          \<comment> \<open>At v\\_1: dx=0, dy=0, s=0, t=0. phi\\_fn = centroid = (1-0-0)*cxw+0+0.\<close>
          have "phi_fn (vxe 1, vye 1) = (?cxw, ?cyw)" unfolding phi_fn_def by (by100 simp)
          moreover have "(let ex = vxe(j+2)-vxe 1; ey = vye(j+2)-vye 1;
              fx = vxe(Suc(j+2) mod ?ne)-vxe 1; fy = vye(Suc(j+2) mod ?ne)-vye 1;
              det = ex*fy-ey*fx; dx = 0::real; dy = 0::real;
              s = (fy*dx-fx*dy)/det; t_par = (ex*dy-ey*dx)/det
          in ((1-s-t_par)*?cxw + s*vxw j + t_par*vxw(Suc j mod ?nw),
              (1-s-t_par)*?cyw + s*vyw j + t_par*vyw(Suc j mod ?nw))) = (?cxw, ?cyw)"
            unfolding Let_def by (by100 simp)
          ultimately show ?thesis using True by simp
        next
          case False
          hence hp_ne: "(fst p, snd p) \<noteq> (vxe 1, vye 1)" .
          \<comment> \<open>LEAST sector for p. Since in\\_sector j p, LEAST \\<le> j.\<close>
          have hexist: "\<exists>j'. j' < ?nw \<and> in_sector j' (fst p, snd p)"
            using hj hin by auto
          define jm where "jm = (LEAST j'. j' < ?nw \<and> in_sector j' (fst p, snd p))"
          from LeastI_ex[OF hexist]
          have hjm: "jm < ?nw" and hinm: "in_sector jm (fst p, snd p)" unfolding jm_def by auto
          have hjm_le: "jm \<le> j"
            unfolding jm_def by (rule Least_le) (use hj hin in auto)
          \<comment> \<open>phi\\_fn uses LEAST = jm.\<close>
          have hphi_jm: "phi_fn (fst p, snd p) = (let ex = vxe(jm+2)-vxe 1; ey = vye(jm+2)-vye 1;
              fx = vxe(Suc(jm+2) mod ?ne)-vxe 1; fy = vye(Suc(jm+2) mod ?ne)-vye 1;
              det = ex*fy-ey*fx; dx = fst p-vxe 1; dy = snd p-vye 1;
              s = (fy*dx-fx*dy)/det; t_par = (ex*dy-ey*dx)/det
          in ((1-s-t_par)*?cxw + s*vxw jm + t_par*vxw(Suc jm mod ?nw),
              (1-s-t_par)*?cyw + s*vyw jm + t_par*vyw(Suc jm mod ?nw)))"
          proof -
            have hjm_least: "(LEAST j'. j' < ?nw \<and> in_sector j' (fst p, snd p)) = jm"
              unfolding jm_def by simp
            from hphi_fn_sector[OF hp_ne hjm_least]
            show ?thesis unfolding Let_def by (by100 simp)
          qed
          show ?thesis
          proof (cases "jm = j")
            case True from hphi_jm show ?thesis unfolding True .
          next
            case False hence hjm_lt: "jm < j" using hjm_le by linarith
            \<comment> \<open>jm < j: p is on boundary between sectors. Affine maps agree.\<close>
            \<comment> \<open>Sectors must be consecutive: j = jm+1 (at most 2 sectors overlap at p \\<noteq> v\\_1).
               Proof: if j > jm+1, p is on ray v\\_1\\<to>v\\_{jm+3}, and cross\\_v1(j+2,p) < 0,
               contradicting in\\_sector j p. Then cross\\_v1(j+2,p) = 0 at boundary,
               giving affine\\_{jm}(s=0) = affine\\_j(t=0) = (1-\\<lambda>)*centroid+\\<lambda>*u\\_{jm+1}.\<close>
            have hj_eq: "j = jm + 1"
            proof (rule ccontr)
              assume hne: "j \<noteq> jm + 1"
              hence hjm2: "jm + 2 \<le> j" using hjm_lt by linarith
              \<comment> \<open>From in\\_sector jm: cross\\_v1(jm+3, p) \\<le> 0. Also cross\\_v1(jm+3, p) \\<ge> 0
                 (from in\\_sector(jm+1) if it existed... actually from a different argument).\<close>
              \<comment> \<open>cross\\_v1(jm+3, (fst p, snd p)) \\<le> 0 from in\\_sector jm.\<close>
              have hjm3_lt: "jm + 3 < ?ne" using hjm2 hj hne_eq by linarith
              have hjm3_mod: "Suc(jm+2) mod ?ne = jm + 3" using hjm3_lt by simp
              from hinm have hcr_le: "cross_v1 (jm+3) (fst p, snd p) \<le> 0"
                unfolding in_sector_def using hjm3_mod by simp
              \<comment> \<open>cross\\_v1(j+2, p) \\<ge> 0 from in\\_sector j.\<close>
              from hin have hcr_ge: "cross_v1 (j+2) p \<ge> 0"
                unfolding in_sector_def by auto
              \<comment> \<open>jm+3 \\<le> j+1 < j+2. hdet\\_general gives det(v\\_{jm+3}-v\\_1, v\\_{j+2}-v\\_1) > 0.\<close>
              have hjm3_lt_j2: "jm + 3 < j + 2" using hjm2 by linarith
              have hjm3_ge2: "(2::nat) \<le> jm + 3" by linarith
              have hj2_lt_ne: "j + 2 < ?ne" using hj hne_eq by linarith
              from hdet_general[rule_format, of "jm+3" "j+2"]
              have hdet_pos2: "(vxe(jm+3)-vxe 1)*(vye(j+2)-vye 1)-(vye(jm+3)-vye 1)*(vxe(j+2)-vxe 1) > 0"
                using hjm3_ge2 hjm3_lt_j2 hj2_lt_ne by linarith
              \<comment> \<open>p is on ray v\\_1\\<to>v\\_{jm+3} (from cross\\_v1(jm+3, p) \\<le> 0 + hfan\\_cover context).
                 Actually: cross\\_v1(jm+2, p) \\<ge> 0 (from in\\_sector jm) and cross\\_v1(jm+3, p) \\<le> 0.
                 By hdet\\_general decomposition of cross\\_v1(j+2, p) at the edge point,
                 cross\\_v1(j+2, p) can't be \\<ge> 0 simultaneously.\<close>
              \<comment> \<open>cross\\_v1(j+2, p) = cross\\_v1(j+2, v\\_1) + (cross involving p-v\\_1 direction).
                 For p with cross\\_v1(jm+3, p) \\<le> 0 and cross\\_v1(jm+2, p) \\<ge> 0:
                 p is "between" directions jm+2 and jm+3. Then cross\\_v1(j+2, p) has the
                 sign of det(v\\_{j+2}-v\\_1, p-v\\_1) which is negative when p is in the
                 angular range [jm+2, jm+3] and j+2 > jm+3.\<close>
              \<comment> \<open>fan\\_wedge gives cross(j+2,p) \\<le> 0.\<close>
              from hinm have hcr_jm2: "cross_v1 (jm+2) (fst p, snd p) \<ge> 0"
                unfolding in_sector_def by auto
              have hcr_jm2_exp: "(vxe(jm+2)-vxe 1)*(snd p-vye 1)-(vye(jm+2)-vye 1)*(fst p-vxe 1) \<ge> 0"
                using hcr_jm2 unfolding cross_v1_def by (cases p) simp
              have hcr_jm3_exp: "(vxe(jm+3)-vxe 1)*(snd p-vye 1)-(vye(jm+3)-vye 1)*(fst p-vxe 1) \<le> 0"
                using hcr_le unfolding cross_v1_def by (cases p) simp
              have hne5: "?ne \<ge> 5" using hlen hne_eq by linarith
              have hjm2_ge: "(2::nat) \<le> jm + 2" by linarith
              \<comment> \<open>Direct: multiply cross(j+2,p) by det\\_{jm} > 0, decompose via sector jm.\<close>
              have hcr_j2_le: "(vxe(j+2)-vxe 1)*(snd p-vye 1)-(vye(j+2)-vye 1)*(fst p-vxe 1) \<le> 0"
              proof -
                let ?ex = "vxe(jm+2)-vxe 1" and ?ey = "vye(jm+2)-vye 1"
                let ?fx = "vxe(jm+3)-vxe 1" and ?fy = "vye(jm+3)-vye 1"
                let ?det = "?ex*?fy-?ey*?fx"
                let ?dx = "fst p - vxe 1" and ?dy = "snd p - vye 1"
                let ?sn = "?fy*?dx-?fx*?dy" and ?tn = "?ex*?dy-?ey*?dx"
                from hdet_pos[rule_format, OF hjm]
                have hd: "?det > 0" using hjm3_mod by (by100 simp)
                \<comment> \<open>s\\_num \\<ge> 0 from cross(jm+3) \\<le> 0, t\\_num \\<ge> 0 from cross(jm+2) \\<ge> 0.\<close>
                have hsn: "?sn \<ge> 0" using hcr_jm3_exp by linarith
                have htn: "?tn \<ge> 0" using hcr_jm2_exp by linarith
                \<comment> \<open>Algebraic identity: det * cross(j+2,p) = sn * cross(j+2,v\\_{jm+2}) + tn * cross(j+2,v\\_{jm+3}).
                   This avoids division entirely.\<close>
                let ?A = "vxe(j+2)-vxe 1" and ?B = "vye(j+2)-vye 1"
                have hdecomp: "?det * (?A*?dy - ?B*?dx) = ?sn*(?A*?ey-?B*?ex) + ?tn*(?A*?fy-?B*?fx)"
                  by (by100 algebra)
                \<comment> \<open>cross(j+2, v\\_{jm+2}) < 0: (A*ey-B*ex) = -(ex*B-ey*A) = -det(jm+2,j+2) < 0.\<close>
                have hjm2_lt: "jm+2 < j+2" using hjm_lt by linarith
                from hdet_general[rule_format, of "jm+2" "j+2"]
                have "?ex*?B-?ey*?A > 0" using hjm2_lt hj2_lt_ne by linarith
                have "?A*?ey-?B*?ex = -(?ex*?B-?ey*?A)" by (by100 algebra)
                hence hcv2: "?A*?ey-?B*?ex < 0" using \<open>?ex*?B-?ey*?A > 0\<close> by linarith
                \<comment> \<open>cross(j+2, v\\_{jm+3}) < 0: same argument.\<close>
                from hdet_general[rule_format, of "jm+3" "j+2"]
                have "?fx*?B-?fy*?A > 0" using hjm3_lt_j2 hj2_lt_ne by linarith
                have "?A*?fy-?B*?fx = -(?fx*?B-?fy*?A)" by (by100 algebra)
                hence hcv3: "?A*?fy-?B*?fx < 0" using \<open>?fx*?B-?fy*?A > 0\<close> by linarith
                \<comment> \<open>sn*(neg) \\<le> 0 and tn*(neg) \\<le> 0.\<close>
                have hcv2_le: "?A*?ey-?B*?ex \<le> 0" using hcv2 by linarith
                have hcv3_le: "?A*?fy-?B*?fx \<le> 0" using hcv3 by linarith
                from mult_nonneg_nonpos[OF hsn hcv2_le]
                have "?sn*(?A*?ey-?B*?ex) \<le> 0" .
                moreover from mult_nonneg_nonpos[OF htn hcv3_le]
                have "?tn*(?A*?fy-?B*?fx) \<le> 0" .
                ultimately have hsum_le: "?sn*(?A*?ey-?B*?ex) + ?tn*(?A*?fy-?B*?fx) \<le> 0"
                  using add_nonpos_nonpos by (by100 blast)
                define lhs where "lhs = ?sn*(?A*?ey-?B*?ex) + ?tn*(?A*?fy-?B*?fx)"
                have "?det * (?A*?dy - ?B*?dx) = lhs" using hdecomp unfolding lhs_def by linarith
                moreover have "lhs \<le> 0" using hsum_le unfolding lhs_def by linarith
                ultimately have "?det * (?A*?dy - ?B*?dx) \<le> 0" by linarith
                \<comment> \<open>det > 0 and det*X \\<le> 0 => X \\<le> 0.\<close>
                show ?thesis
                proof (rule ccontr)
                  assume "\<not>(?A*?dy - ?B*?dx \<le> 0)"
                  hence "?A*?dy - ?B*?dx > 0" by linarith
                  from mult_pos_pos[OF hd this]
                  have "?det * (?A*?dy - ?B*?dx) > 0" .
                  with \<open>?det * (?A*?dy - ?B*?dx) \<le> 0\<close> show False by linarith
                qed
              qed
              \<comment> \<open>But in\\_sector j: cross(j+2,p) \\<ge> 0. So = 0.\<close>
              have hcr_j2_exp: "(vxe(j+2)-vxe 1)*(snd p-vye 1)-(vye(j+2)-vye 1)*(fst p-vxe 1) \<ge> 0"
                using hcr_ge unfolding cross_v1_def by (cases p) simp
              have hcr_j2_eq: "(vxe(j+2)-vxe 1)*(snd p-vye 1) = (vye(j+2)-vye 1)*(fst p-vxe 1)"
                using hcr_j2_le hcr_j2_exp by linarith
              \<comment> \<open>Cramer: hdet\\_pos2*(fst p - vxe 1) = (vxe(j+2)-vxe 1)*cross(jm+3).\<close>
              have hcramer1: "((vxe(jm+3)-vxe 1)*(vye(j+2)-vye 1)-(vye(jm+3)-vye 1)*(vxe(j+2)-vxe 1)) * (fst p-vxe 1)
                = (vxe(j+2)-vxe 1) * ((vxe(jm+3)-vxe 1)*(snd p-vye 1)-(vye(jm+3)-vye 1)*(fst p-vxe 1))"
                using hcr_j2_eq by (by100 algebra)
              \<comment> \<open>det > 0, RHS = (vxe(j+2)-vxe 1)*cross(jm+3) \\<le> 0. So det*dx \\<le> 0, dx \\<le> 0.\<close>
              \<comment> \<open>Similarly with jm+2: det22*dx = (vxe(j+2)-vxe 1)*cross(jm+2) \\<ge> 0. So dx \\<ge> 0.\<close>
              have hcramer2: "((vxe(jm+2)-vxe 1)*(vye(j+2)-vye 1)-(vye(jm+2)-vye 1)*(vxe(j+2)-vxe 1)) * (fst p-vxe 1)
                = (vxe(j+2)-vxe 1) * ((vxe(jm+2)-vxe 1)*(snd p-vye 1)-(vye(jm+2)-vye 1)*(fst p-vxe 1))"
                using hcr_j2_eq by (by100 algebra)
              from hdet_general[rule_format, of "jm+2" "j+2"]
              have hdet22: "(vxe(jm+2)-vxe 1)*(vye(j+2)-vye 1)-(vye(jm+2)-vye 1)*(vxe(j+2)-vxe 1) > 0"
                using hjm3_lt_j2 hj2_lt_ne by linarith
              \<comment> \<open>dx = 0 (from opposing sign constraints), then dy = 0, p = v\\_1.\<close>
              let ?det32 = "(vxe(jm+3)-vxe 1)*(vye(j+2)-vye 1)-(vye(jm+3)-vye 1)*(vxe(j+2)-vxe 1)"
              let ?det22 = "(vxe(jm+2)-vxe 1)*(vye(j+2)-vye 1)-(vye(jm+2)-vye 1)*(vxe(j+2)-vxe 1)"
              have hdx0: "fst p - vxe 1 = 0"
              proof (cases "vxe(j+2) - vxe 1 \<ge> 0")
                case True \<comment> \<open>C \\<ge> 0: det32*dx = C*cross(jm+3) \\<le> 0, det22*dx = C*cross(jm+2) \\<ge> 0.\<close>
                have "?det32 * (fst p - vxe 1) = (vxe(j+2)-vxe 1) * ((vxe(jm+3)-vxe 1)*(snd p-vye 1)-(vye(jm+3)-vye 1)*(fst p-vxe 1))"
                  using hcramer1 by simp
                moreover have "(vxe(j+2)-vxe 1) * ((vxe(jm+3)-vxe 1)*(snd p-vye 1)-(vye(jm+3)-vye 1)*(fst p-vxe 1)) \<le> 0"
                  using mult_nonneg_nonpos[OF True hcr_jm3_exp] .
                ultimately have h1: "?det32 * (fst p - vxe 1) \<le> 0" by linarith
                have "?det22 * (fst p - vxe 1) = (vxe(j+2)-vxe 1) * ((vxe(jm+2)-vxe 1)*(snd p-vye 1)-(vye(jm+2)-vye 1)*(fst p-vxe 1))"
                  using hcramer2 by simp
                moreover have "(vxe(j+2)-vxe 1) * ((vxe(jm+2)-vxe 1)*(snd p-vye 1)-(vye(jm+2)-vye 1)*(fst p-vxe 1)) \<ge> 0"
                  using mult_nonneg_nonneg[OF True hcr_jm2_exp] .
                ultimately have h2: "?det22 * (fst p - vxe 1) \<ge> 0" by linarith
                show ?thesis
                proof (rule ccontr)
                  assume "fst p - vxe 1 \<noteq> 0"
                  hence "fst p - vxe 1 > 0 \<or> fst p - vxe 1 < 0" by linarith
                  thus False
                  proof
                    assume "fst p - vxe 1 > 0"
                    from mult_pos_pos[OF hdet_pos2 this] h1 show False by linarith
                  next
                    assume "fst p - vxe 1 < 0"
                    from mult_pos_neg[OF hdet22 this] h2 show False by linarith
                  qed
                qed
              next
                case False hence hC_neg: "vxe(j+2) - vxe 1 < 0" by linarith
                have hC_le: "vxe(j+2) - vxe 1 \<le> 0" using hC_neg by linarith
                have h1: "?det32 * (fst p - vxe 1) \<ge> 0"
                proof -
                  have "?det32 * (fst p - vxe 1) = (vxe(j+2)-vxe 1) * ((vxe(jm+3)-vxe 1)*(snd p-vye 1)-(vye(jm+3)-vye 1)*(fst p-vxe 1))"
                    using hcramer1 by simp
                  also have "\<dots> \<ge> 0" using mult_nonpos_nonpos[OF hC_le hcr_jm3_exp] .
                  finally show ?thesis .
                qed
                have h2: "?det22 * (fst p - vxe 1) \<le> 0"
                proof -
                  have "?det22 * (fst p - vxe 1) = (vxe(j+2)-vxe 1) * ((vxe(jm+2)-vxe 1)*(snd p-vye 1)-(vye(jm+2)-vye 1)*(fst p-vxe 1))"
                    using hcramer2 by simp
                  also have "\<dots> \<le> 0" using mult_nonpos_nonneg[OF hC_le hcr_jm2_exp] .
                  finally show ?thesis .
                qed
                show ?thesis
                proof (rule ccontr)
                  assume "fst p - vxe 1 \<noteq> 0"
                  hence "fst p - vxe 1 > 0 \<or> fst p - vxe 1 < 0" by linarith
                  thus False
                  proof
                    assume "fst p - vxe 1 > 0"
                    from mult_pos_pos[OF hdet22 this] h2 show False by linarith
                  next
                    assume "fst p - vxe 1 < 0"
                    from mult_pos_neg[OF hdet_pos2 this] h1 show False by linarith
                  qed
                qed
              qed
              have hdy0: "snd p - vye 1 = 0"
              proof -
                from hcr_j2_eq hdx0 have "(vxe(j+2)-vxe 1) * (snd p - vye 1) = 0" by simp
                moreover have "vxe(j+2) - vxe 1 \<noteq> 0 \<or> vye(j+2) - vye 1 \<noteq> 0"
                proof -
                  have "j+2 < ?ne" using hj hne_eq by linarith
                  have "(1::nat) < ?ne" using hlen hne_eq by linarith
                  have "(1::nat) \<noteq> j+2" by linarith
                  from hC3_e[rule_format, OF \<open>1 < ?ne\<close> \<open>j+2 < ?ne\<close> \<open>1 \<noteq> j+2\<close>]
                  have "(vxe 1, vye 1) \<noteq> (vxe(j+2), vye(j+2))" .
                  thus ?thesis by auto
                qed
                ultimately show ?thesis
                proof (elim disjE)
                  assume "vxe(j+2) - vxe 1 \<noteq> 0"
                  with \<open>(vxe(j+2)-vxe 1) * (snd p - vye 1) = 0\<close>
                  show ?thesis by (by100 simp)
                next
                  assume hvye_ne: "vye(j+2) - vye 1 \<noteq> 0"
                  \<comment> \<open>vxe(j+2) - vxe 1 could be 0. Use cross constraints with dx=0.\<close>
                  from hcr_jm3_exp hdx0
                  have "((vxe(jm+3)-vxe 1))*(snd p - vye 1) \<le> 0" by simp
                  moreover from hcr_jm2_exp hdx0
                  have "((vxe(jm+2)-vxe 1))*(snd p - vye 1) \<ge> 0" by simp
                  \<comment> \<open>If both coefficients same sign: dy forced to 0.
                     If different signs: also forced to 0.\<close>
                  ultimately show ?thesis
                  proof (cases "vxe(j+2) - vxe 1 = 0")
                    case True \<comment> \<open>vxe(j+2)=vxe 1 and vye(j+2)\\<noteq>vye 1.\<close>
                    \<comment> \<open>det32 = (vxe(jm+3)-vxe 1)*(vye(j+2)-vye 1) > 0 (from True).\<close>
                    from hdet_pos2 True
                    have h32: "(vxe(jm+3)-vxe 1)*(vye(j+2)-vye 1) > 0" by simp
                    \<comment> \<open>det22 = (vxe(jm+2)-vxe 1)*(vye(j+2)-vye 1) > 0.\<close>
                    from hdet22 True
                    have h22: "(vxe(jm+2)-vxe 1)*(vye(j+2)-vye 1) > 0" by simp
                    \<comment> \<open>Both (vxe(jm+3)-vxe 1) and (vxe(jm+2)-vxe 1) have same sign as (vye(j+2)-vye 1).\<close>
                    show ?thesis
                    proof (cases "vye(j+2) - vye 1 > 0")
                      case True2: True
                      have hA_pos: "vxe(jm+3) - vxe 1 > 0"
                      proof (rule ccontr)
                        assume "\<not>(vxe(jm+3) - vxe 1 > 0)"
                        hence "vxe(jm+3) - vxe 1 \<le> 0" by linarith
                        have "vye(j+2) - vye 1 \<ge> 0" using True2 by linarith
                        from mult_nonpos_nonneg[OF \<open>vxe(jm+3)-vxe 1 \<le> 0\<close> this]
                        have "(vxe(jm+3)-vxe 1)*(vye(j+2)-vye 1) \<le> 0" .
                        thus False using h32 by linarith
                      qed
                      have hB_pos: "vxe(jm+2) - vxe 1 > 0"
                      proof (rule ccontr)
                        assume "\<not>(vxe(jm+2) - vxe 1 > 0)"
                        hence "vxe(jm+2) - vxe 1 \<le> 0" by linarith
                        have "vye(j+2) - vye 1 \<ge> 0" using True2 by linarith
                        from mult_nonpos_nonneg[OF \<open>vxe(jm+2)-vxe 1 \<le> 0\<close> this]
                        have "(vxe(jm+2)-vxe 1)*(vye(j+2)-vye 1) \<le> 0" .
                        thus False using h22 by linarith
                      qed
                      have "snd p - vye 1 \<le> 0"
                      proof (rule ccontr)
                        assume "\<not>(snd p - vye 1 \<le> 0)"
                        hence "snd p - vye 1 > 0" by linarith
                        from mult_pos_pos[OF hA_pos this]
                        have "(vxe(jm+3)-vxe 1)*(snd p-vye 1) > 0" .
                        with \<open>(vxe(jm+3)-vxe 1)*(snd p-vye 1) \<le> 0\<close> show False by linarith
                      qed
                      moreover have "snd p - vye 1 \<ge> 0"
                      proof (rule ccontr)
                        assume "\<not>(snd p - vye 1 \<ge> 0)"
                        hence "snd p - vye 1 < 0" by linarith
                        from mult_pos_neg[OF hB_pos this]
                        have "(vxe(jm+2)-vxe 1)*(snd p-vye 1) < 0" .
                        with \<open>(vxe(jm+2)-vxe 1)*(snd p-vye 1) \<ge> 0\<close> show False by linarith
                      qed
                      ultimately show ?thesis by linarith
                    next
                      case False2: False hence hvye_neg: "vye(j+2) - vye 1 < 0" using hvye_ne by linarith
                      have hA_neg: "vxe(jm+3) - vxe 1 < 0"
                      proof (rule ccontr)
                        assume "\<not>(vxe(jm+3) - vxe 1 < 0)"
                        hence "vxe(jm+3) - vxe 1 \<ge> 0" by linarith
                        have "vye(j+2) - vye 1 \<le> 0" using hvye_neg by linarith
                        from mult_nonneg_nonpos[OF \<open>vxe(jm+3)-vxe 1 \<ge> 0\<close> this]
                        have "(vxe(jm+3)-vxe 1)*(vye(j+2)-vye 1) \<le> 0" .
                        thus False using h32 by linarith
                      qed
                      have hB_neg: "vxe(jm+2) - vxe 1 < 0"
                      proof (rule ccontr)
                        assume "\<not>(vxe(jm+2) - vxe 1 < 0)"
                        hence "vxe(jm+2) - vxe 1 \<ge> 0" by linarith
                        have "vye(j+2) - vye 1 \<le> 0" using hvye_neg by linarith
                        from mult_nonneg_nonpos[OF \<open>vxe(jm+2)-vxe 1 \<ge> 0\<close> this]
                        have "(vxe(jm+2)-vxe 1)*(vye(j+2)-vye 1) \<le> 0" .
                        thus False using h22 by linarith
                      qed
                      have "snd p - vye 1 \<ge> 0"
                      proof (rule ccontr)
                        assume "\<not>(snd p - vye 1 \<ge> 0)"
                        hence "snd p - vye 1 < 0" by linarith
                        from mult_neg_neg[OF hA_neg this]
                        have "(vxe(jm+3)-vxe 1)*(snd p-vye 1) > 0" .
                        with \<open>(vxe(jm+3)-vxe 1)*(snd p-vye 1) \<le> 0\<close> show False by linarith
                      qed
                      moreover have "snd p - vye 1 \<le> 0"
                      proof (rule ccontr)
                        assume "\<not>(snd p - vye 1 \<le> 0)"
                        hence "snd p - vye 1 > 0" by linarith
                        from mult_neg_pos[OF hB_neg this]
                        have "(vxe(jm+2)-vxe 1)*(snd p-vye 1) < 0" .
                        with \<open>(vxe(jm+2)-vxe 1)*(snd p-vye 1) \<ge> 0\<close> show False by linarith
                      qed
                      ultimately show ?thesis by linarith
                    qed
                  next
                    case False \<comment> \<open>vxe(j+2) \\<noteq> vxe 1: already handled by first disjE branch.\<close>
                    with \<open>(vxe(j+2)-vxe 1) * (snd p - vye 1) = 0\<close>
                    show ?thesis by (by100 simp)
                  qed
                qed
              qed
              have "fst p - vxe 1 = 0 \<and> snd p - vye 1 = 0" using hdx0 hdy0 by simp
              hence "(fst p, snd p) = (vxe 1, vye 1)" by (by100 simp)
              thus False using hp_ne by simp
            qed
            have hcross_zero: "cross_v1 (j+2) p = 0"
            proof -
              from hinm have hle: "cross_v1 (Suc(jm+2) mod ?ne) (fst p, snd p) \<le> 0"
                unfolding in_sector_def by auto
              have hjm3: "Suc(jm+2) mod ?ne = jm + 3"
              proof -
                have "jm + 3 \<le> j + 2" using hj_eq by linarith
                also have "\<dots> < ?ne" using hj hne_eq by linarith
                finally show ?thesis by simp
              qed
              have "Suc(jm+2) mod ?ne = j + 2" using hjm3 hj_eq by linarith
              hence "cross_v1 (j+2) (fst p, snd p) \<le> 0" using hle by simp
              hence hle2: "cross_v1 (j+2) p \<le> 0"
                by (cases p) simp
              from hin have "cross_v1 (j+2) p \<ge> 0" unfolding in_sector_def by auto
              with hle2 show ?thesis by linarith
            qed
            \<comment> \<open>Algebraic boundary matching: affine\\_{jm}(s=0) = affine\\_j(t=0).\<close>
            \<comment> \<open>From hcross\\_zero: cross\\_v1(j+2,p) = 0.
               In sector jm formula: s\\_{jm} depends on cross\\_v1(jm+3,p) = cross\\_v1(j+2,p) = 0 (via hj\\_eq).
               In sector j formula: t\\_j depends on cross\\_v1(j+2,p) = 0.
               Both formulas reduce to (1-\\<lambda>)*centroid + \\<lambda>*u\\_{jm+1} for the same \\<lambda>.\<close>
            \<comment> \<open>Step 1: Suc(jm+2) mod ne = j+2 (from hj\\_eq).\<close>
            have hjm3_eq: "Suc(jm+2) mod ?ne = j + 2"
            proof -
              have "jm + 3 \<le> j + 2" using hj_eq by linarith
              also have "\<dots> < ?ne" using hj hne_eq by linarith
              finally show ?thesis using hj_eq by simp
            qed
            \<comment> \<open>Step 2: Suc jm mod nw = j (from hj\\_eq and j < nw).\<close>
            have hjm_suc: "Suc jm mod ?nw = j"
              using hj_eq hj by simp
            \<comment> \<open>Step 3: s\\_{jm} = 0 (cross\\_v1(j+2, p) = 0 kills the s numerator).\<close>
            let ?dx = "fst p - vxe 1" and ?dy = "snd p - vye 1"
            have hcross_expand: "(vxe(j+2)-vxe 1)*?dy - (vye(j+2)-vye 1)*?dx = 0"
              using hcross_zero unfolding cross_v1_def by (cases p) simp
            \<comment> \<open>s\\_{jm} = (fy\\_{jm}*dx - fx\\_{jm}*dy) / det\\_{jm} where fx\\_{jm}=vxe(j+2)-vxe 1, fy\\_{jm}=vye(j+2)-vye 1.\<close>
            \<comment> \<open>s\\_{jm} numerator = (vye(j+2)-vye 1)*dx - (vxe(j+2)-vxe 1)*dy = -cross = 0.\<close>
            have hs_jm_zero: "phi_s2 (jm+2) (Suc(jm+2) mod ?ne) ?dx ?dy = 0"
            proof -
              have "phi_s2 (jm+2) (Suc(jm+2) mod ?ne) ?dx ?dy =
                phi_s2 (jm+2) (j+2) ?dx ?dy" using hjm3_eq by simp
              also have "\<dots> = ((vye(j+2)-vye 1)*?dx - (vxe(j+2)-vxe 1)*?dy) /
                ((vxe(jm+2)-vxe 1)*(vye(j+2)-vye 1)-(vye(jm+2)-vye 1)*(vxe(j+2)-vxe 1))"
                unfolding phi_s2_def Let_def by simp
              also have "(vye(j+2)-vye 1)*?dx - (vxe(j+2)-vxe 1)*?dy = 0"
                using hcross_expand by linarith
              finally show ?thesis by simp
            qed
            \<comment> \<open>Step 4: t\\_j = 0 (cross\\_v1(j+2, p) = 0 kills the t numerator).\<close>
            have ht_j_zero: "phi_t2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy = 0"
            proof -
              have "phi_t2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy =
                ((vxe(j+2)-vxe 1)*?dy - (vye(j+2)-vye 1)*?dx) /
                ((vxe(j+2)-vxe 1)*(vye(Suc(j+2) mod ?ne)-vye 1)-(vye(j+2)-vye 1)*(vxe(Suc(j+2) mod ?ne)-vxe 1))"
                unfolding phi_t2_def Let_def by simp
              also have "(vxe(j+2)-vxe 1)*?dy - (vye(j+2)-vye 1)*?dx = 0"
                using hcross_expand by linarith
              finally show ?thesis by simp
            qed
            \<comment> \<open>Step 5: t\\_{jm} = s\\_j (both = \\<lambda> on the ray).\<close>
            \<comment> \<open>Step 5+6: Show phi\\_fn(p) = sector j formula directly.\<close>
            \<comment> \<open>From hphi\\_fn\\_decomp for sector jm: phi\\_fn = decomp\\_{jm} with s\\_{jm}=0.
               After simplification: phi\\_fn = (1-t\\_{jm})*cxw + t\\_{jm}*vxw j.
               The sector j let-expression with t\\_j=0 gives (1-s\\_j)*cxw + s\\_j*vxw j.
               Both t\\_{jm} and s\\_j equal \\<lambda> on the ray cross(j+2)=0.
               So phi\\_fn matches the sector j formula.\<close>
            have hjm_least2: "(LEAST j'. j' < ?nw \<and> in_sector j' (fst p, snd p)) = jm"
              unfolding jm_def by simp
            from hphi_fn_decomp[OF hp_ne hjm_least2]
            have hphi_decomp_jm: "phi_fn (fst p, snd p) =
              ((1 - phi_s2 (jm+2) (Suc(jm+2) mod ?ne) ?dx ?dy
                 - phi_t2 (jm+2) (Suc(jm+2) mod ?ne) ?dx ?dy)*?cxw
              + phi_s2 (jm+2) (Suc(jm+2) mod ?ne) ?dx ?dy*vxw jm
              + phi_t2 (jm+2) (Suc(jm+2) mod ?ne) ?dx ?dy*vxw(Suc jm mod ?nw),
              (1 - phi_s2 (jm+2) (Suc(jm+2) mod ?ne) ?dx ?dy
                 - phi_t2 (jm+2) (Suc(jm+2) mod ?ne) ?dx ?dy)*?cyw
              + phi_s2 (jm+2) (Suc(jm+2) mod ?ne) ?dx ?dy*vyw jm
              + phi_t2 (jm+2) (Suc(jm+2) mod ?ne) ?dx ?dy*vyw(Suc jm mod ?nw))"
              by simp
            hence hphi_simplified: "phi_fn (fst p, snd p) =
              ((1 - phi_t2 (jm+2) (j+2) ?dx ?dy)*?cxw
              + phi_t2 (jm+2) (j+2) ?dx ?dy*vxw j,
              (1 - phi_t2 (jm+2) (j+2) ?dx ?dy)*?cyw
              + phi_t2 (jm+2) (j+2) ?dx ?dy*vyw j)"
              using hs_jm_zero hjm3_eq hjm_suc by simp
            \<comment> \<open>phi\\_t2(jm+2, j+2, dx, dy) = ((vxe(jm+2)-vxe 1)*dy-(vye(jm+2)-vye 1)*dx) / det\\_{jm}.
               With cross(j+2)=0: C*dy = D*dx. So numerator = ex*dy-ey*dx where
               ex=vxe(jm+2)-vxe 1, ey=vye(jm+2)-vye 1.
               phi\\_s2(j+2, si, dx, dy) = ((vye(si)-vye 1)*dx-(vxe(si)-vxe 1)*dy) / det\\_j.
               Both equal \\<lambda> on the ray.\<close>
            \<comment> \<open>Goal: phi\\_fn(p) = let-expr for sector j.\<close>
            \<comment> \<open>Strategy: show fst and snd components match separately.\<close>
            \<comment> \<open>Prove t\\_{jm} = s\\_j via cross-multiplication (avoids division).\<close>
            have ht_jm_eq_s_j: "phi_t2 (jm+2) (j+2) ?dx ?dy =
              phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy"
            proof -
              let ?ex = "vxe(jm+2)-vxe 1" and ?ey = "vye(jm+2)-vye 1"
              let ?A = "vxe(j+2)-vxe 1" and ?B = "vye(j+2)-vye 1"
              let ?fx2 = "vxe(Suc(j+2) mod ?ne)-vxe 1" and ?fy2 = "vye(Suc(j+2) mod ?ne)-vye 1"
              let ?det_jm = "?ex*?B-?ey*?A" and ?det_j = "?A*?fy2-?B*?fx2"
              \<comment> \<open>Both dets > 0.\<close>
              have hjm2_lt: "jm+2 < j+2" using hjm_lt by linarith
              have hj2_lt: "j+2 < ?ne" using hj hne_eq by linarith
              from hdet_general[rule_format, of "jm+2" "j+2"]
              have hd1: "?det_jm > 0" using hjm2_lt hj2_lt by linarith
              from hdet_pos[rule_format, OF hj]
              have hd2: "?det_j > 0" by (by100 simp)
              \<comment> \<open>LHS = (?ex*dy-?ey*dx)/?det\\_jm, RHS = (?fy2*dx-?fx2*dy)/?det\\_j.\<close>
              have lhs_def: "phi_t2 (jm+2) (j+2) ?dx ?dy = (?ex*?dy-?ey*?dx)/?det_jm"
                unfolding phi_t2_def Let_def by simp
              have rhs_def: "phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy = (?fy2*?dx-?fx2*?dy)/?det_j"
                unfolding phi_s2_def Let_def by simp
              \<comment> \<open>Cross-multiply: (?ex*dy-?ey*dx)*det\\_j = (?fy2*dx-?fx2*dy)*det\\_jm.\<close>
              \<comment> \<open>With constraint A*dy = B*dx, this is an algebraic identity.\<close>
              have hcross_mult: "(?ex*?dy-?ey*?dx)*?det_j = (?fy2*?dx-?fx2*?dy)*?det_jm"
                using hcross_expand by (by100 algebra)
              \<comment> \<open>Both dets > 0, so a/d1 = b/d2 iff a*d2 = b*d1.\<close>
              have hd1ne: "?det_jm \<noteq> 0" using hd1 by linarith
              have hd2ne: "?det_j \<noteq> 0" using hd2 by linarith
              \<comment> \<open>a/b = c/d from a*d = c*b, b\\<noteq>0, d\\<noteq>0.\<close>
              have "(?ex*?dy-?ey*?dx) * ?det_j = (?fy2*?dx-?fx2*?dy) * ?det_jm"
                using hcross_mult .
              hence heq_div: "(?ex*?dy-?ey*?dx) / ?det_jm = (?fy2*?dx-?fx2*?dy) / ?det_j"
                using frac_eq_from_cross_mult[OF _ hd1ne hd2ne] by (by100 simp)
              show ?thesis using lhs_def rhs_def heq_div by simp
            qed
            \<comment> \<open>Now assemble: phi\\_fn = (1-t\\_{jm})*c+t\\_{jm}*u\\_j = (1-s\\_j)*c+s\\_j*u\\_j = sector j formula.\<close>
            show ?thesis
            proof -
              \<comment> \<open>hphi\\_simplified: phi\\_fn = (1-phi\\_t2(jm+2,j+2,dx,dy))*c + phi\\_t2*uj.\<close>
              \<comment> \<open>Substitute phi\\_t2 = phi\\_s2 and reconstruct the let-expression.\<close>
              from hphi_simplified have hphi_s_form: "phi_fn (fst p, snd p) =
                ((1 - phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy)*?cxw
                + phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy*vxw j,
                (1 - phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy)*?cyw
                + phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy*vyw j)"
                using ht_jm_eq_s_j hjm3_eq by simp
              \<comment> \<open>Convert goal let-expr to phi\\_s2/phi\\_t2 form (reverse of hphi\\_fn\\_decomp).\<close>
              have hlet_to_decomp: "(let ex = vxe(j+2)-vxe 1; ey = vye(j+2)-vye 1;
                  fx = vxe(Suc(j+2) mod ?ne)-vxe 1; fy = vye(Suc(j+2) mod ?ne)-vye 1;
                  det = ex*fy-ey*fx; dx = fst p - vxe 1; dy = snd p - vye 1;
                  s = (fy*dx-fx*dy)/det; t_par = (ex*dy-ey*dx)/det
              in ((1-s-t_par)*?cxw + s*vxw j + t_par*vxw(Suc j mod ?nw),
                  (1-s-t_par)*?cyw + s*vyw j + t_par*vyw(Suc j mod ?nw)))
              = ((1 - phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy
                 - phi_t2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy)*?cxw
              + phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy*vxw j
              + phi_t2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy*vxw(Suc j mod ?nw),
              (1 - phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy
                 - phi_t2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy)*?cyw
              + phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy*vyw j
              + phi_t2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy*vyw(Suc j mod ?nw))"
                unfolding phi_s2_def phi_t2_def Let_def by (by100 simp)
              \<comment> \<open>With t\\_j=0, the decomp form = our phi\\_s form.\<close>
              have hdecomp_simplified: "((1 - phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy - 0)*?cxw
              + phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy*vxw j + 0*vxw(Suc j mod ?nw),
              (1 - phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy - 0)*?cyw
              + phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy*vyw j + 0*vyw(Suc j mod ?nw))
              = ((1 - phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy)*?cxw
              + phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy*vxw j,
              (1 - phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy)*?cyw
              + phi_s2 (j+2) (Suc(j+2) mod ?ne) ?dx ?dy*vyw j)"
                by (by100 simp)
              from hphi_s_form hlet_to_decomp ht_j_zero hdecomp_simplified
              show ?thesis by (by5000 metis) \<comment> \<open>Was bare simp (~30s). Now metis.\<close>
            qed
          qed
        qed
      qed
      \<comment> \<open>Define sector sets for the pasting lemma.\<close>
      define sector_set where "sector_set j = {p \<in> P_e. in_sector j p}" for j
      \<comment> \<open>Sector sets cover P\\_e (from hfan\\_cover: every p is v\\_1 or in some sector).\<close>
      have hsector_cover: "P_e = (\<Union>j<?nw. sector_set j)"
      proof (rule set_eqI, rule iffI)
        fix p assume hp: "p \<in> P_e"
        from hfan_cover[rule_format, OF hp]
        show "p \<in> (\<Union>j<?nw. sector_set j)"
        proof (elim disjE exE conjE)
          assume "p = (vxe 1, vye 1)"
          \<comment> \<open>v\\_1 is in sector nw-1 (and sector 0). Choose sector 0.\<close>
          have "in_sector 0 (vxe 1, vye 1)" unfolding in_sector_def cross_v1_def by simp
          hence "p \<in> sector_set 0" using hp \<open>p = (vxe 1, vye 1)\<close>
            unfolding sector_set_def by simp
          thus ?thesis using hnw_pos by (by100 blast)
        next
          fix j assume "j < ?nw" "in_sector j p"
          hence "p \<in> sector_set j" using hp unfolding sector_set_def by simp
          thus ?thesis using \<open>j < ?nw\<close> by (by100 blast)
        qed
      next
        fix p assume "p \<in> (\<Union>j<?nw. sector_set j)"
        thus "p \<in> P_e" unfolding sector_set_def by (by100 blast)
      qed
      \<comment> \<open>Step A: Each sector\\_set j is closed in R^2 (P\\_e is compact hence closed,
         half-planes are closed, intersection of closed sets is closed).\<close>
      have hsector_R2_closed: "\<forall>j<?nw. closed (sector_set j)"
      proof (intro allI impI)
        fix j assume hj: "j < ?nw"
        \<comment> \<open>sector\\_set j = {p \\<in> P\\_e. cross\\_v1(j+2,p) \\<ge> 0 \\<and> cross\\_v1(si,p) \\<le> 0}.\<close>
        \<comment> \<open>P\\_e is compact (finite convex hull) hence closed.\<close>
        have hPe_closed: "closed P_e"
        proof -
          \<comment> \<open>P\\_e is compact: it's the convex hull of finitely many points.\<close>
          \<comment> \<open>Show P\\_e \\<subseteq> convex hull of vertices (from hC5\\_e definition).\<close>
          \<comment> \<open>Show convex hull \\<subseteq> P\\_e (vertices are in P\\_e by hC4\\_e, P\\_e is convex).\<close>
          have hPe_compact: "compact P_e"
          proof -
            have hne_ge1: "?ne \<ge> 1" using hlen_ext by (by100 linarith)
            have "P_e = {(x, y). \<exists>coeffs. (\<forall>i<?ne. (coeffs i :: real) \<ge> 0) \<and> (\<Sum>i<?ne. coeffs i) = 1
                \<and> x = (\<Sum>i<?ne. coeffs i * vxe i) \<and> y = (\<Sum>i<?ne. coeffs i * vye i)}"
              using hC5_e by auto
            moreover have "compact {(x, y). \<exists>coeffs. (\<forall>i<?ne. (coeffs i :: real) \<ge> 0) \<and> (\<Sum>i<?ne. coeffs i) = 1
                \<and> x = (\<Sum>i<?ne. coeffs i * vxe i) \<and> y = (\<Sum>i<?ne. coeffs i * vye i)}"
              by (rule convex_hull_compact_general[OF hne_ge1])
            ultimately show ?thesis by simp
          qed
          from compact_imp_closed[OF hPe_compact] show ?thesis .
        qed
        \<comment> \<open>The half-plane {p. cross\\_v1(j+2, p) \\<ge> 0} is closed (preimage of [0,\\<infinity>) under continuous linear).\<close>
        have hH1_closed: "closed {p :: real \<times> real. (vxe(j+2)-vxe 1)*(snd p-vye 1)-(vye(j+2)-vye 1)*(fst p-vxe 1) \<ge> 0}"
        proof -
          have "closed {p :: real \<times> real. 0 \<le> (vxe(j+2)-vxe 1)*(snd p-vye 1)-(vye(j+2)-vye 1)*(fst p-vxe 1)}"
            by (intro closed_Collect_le continuous_intros)
          thus ?thesis by (by100 simp)
        qed
        have hH2_closed: "closed {p :: real \<times> real. (vxe(Suc(j+2) mod ?ne)-vxe 1)*(snd p-vye 1)-(vye(Suc(j+2) mod ?ne)-vye 1)*(fst p-vxe 1) \<le> 0}"
          by (intro closed_Collect_le continuous_intros)
        \<comment> \<open>sector\\_set j = P\\_e \\<inter> H1 \\<inter> H2, intersection of closed sets.\<close>
        have "sector_set j = P_e \<inter> {p. (vxe(j+2)-vxe 1)*(snd p-vye 1)-(vye(j+2)-vye 1)*(fst p-vxe 1) \<ge> 0}
          \<inter> {p. (vxe(Suc(j+2) mod ?ne)-vxe 1)*(snd p-vye 1)-(vye(Suc(j+2) mod ?ne)-vye 1)*(fst p-vxe 1) \<le> 0}"
          unfolding sector_set_def in_sector_def cross_v1_def by auto
        from closed_Int[OF hH1_closed hH2_closed]
        have hH12: "closed ({p :: real \<times> real. (vxe(j+2)-vxe 1)*(snd p-vye 1)-(vye(j+2)-vye 1)*(fst p-vxe 1) \<ge> 0}
          \<inter> {p. (vxe(Suc(j+2) mod ?ne)-vxe 1)*(snd p-vye 1)-(vye(Suc(j+2) mod ?ne)-vye 1)*(fst p-vxe 1) \<le> 0})" .
        from closed_Int[OF hPe_closed hH12]
        have "closed (P_e \<inter> ({p. (vxe(j+2)-vxe 1)*(snd p-vye 1)-(vye(j+2)-vye 1)*(fst p-vxe 1) \<ge> 0}
          \<inter> {p. (vxe(Suc(j+2) mod ?ne)-vxe 1)*(snd p-vye 1)-(vye(Suc(j+2) mod ?ne)-vye 1)*(fst p-vxe 1) \<le> 0}))" .
        moreover have "sector_set j = P_e \<inter> ({p. (vxe(j+2)-vxe 1)*(snd p-vye 1)-(vye(j+2)-vye 1)*(fst p-vxe 1) \<ge> 0}
          \<inter> {p. (vxe(Suc(j+2) mod ?ne)-vxe 1)*(snd p-vye 1)-(vye(Suc(j+2) mod ?ne)-vye 1)*(fst p-vxe 1) \<le> 0})"
          unfolding sector_set_def in_sector_def cross_v1_def by auto
        ultimately show "closed (sector_set j)" by simp
      qed
      \<comment> \<open>Step B: phi\\_fn is continuous\\_on each sector (affine function of (fst p, snd p)).\<close>
      have hsector_cont_on: "\<forall>j<?nw. continuous_on (sector_set j) phi_fn"
      proof (intro allI impI)
        fix j assume hj: "j < ?nw"
        \<comment> \<open>phi\\_fn = affine\\_j on sector\\_set j (from hphi\\_affine\\_on\\_sector).\<close>
        let ?si = "Suc(j+2) mod ?ne"
        \<comment> \<open>Define the affine formula as a function.\<close>
        define affine_j where "affine_j p = (let ex = vxe(j+2)-vxe 1; ey = vye(j+2)-vye 1;
            fx = vxe ?si-vxe 1; fy = vye ?si-vye 1;
            det = ex*fy-ey*fx; dx = fst p-vxe 1; dy = snd p-vye 1;
            s = (fy*dx-fx*dy)/det; t_par = (ex*dy-ey*dx)/det
        in ((1-s-t_par)*?cxw + s*vxw j + t_par*vxw(Suc j mod ?nw),
            (1-s-t_par)*?cyw + s*vyw j + t_par*vyw(Suc j mod ?nw)))" for p
        \<comment> \<open>phi\\_fn = affine\\_j on sector\\_set j.\<close>
        have hphi_eq: "\<forall>p \<in> sector_set j. phi_fn p = affine_j p"
        proof (intro ballI)
          fix p assume "p \<in> sector_set j"
          hence hp: "p \<in> P_e" and hin: "in_sector j p" unfolding sector_set_def by auto
          from hphi_affine_on_sector[rule_format, OF hj hp hin]
          have "phi_fn (fst p, snd p) = (let ex = vxe(j+2)-vxe 1; ey = vye(j+2)-vye 1;
              fx = vxe ?si-vxe 1; fy = vye ?si-vye 1;
              det = ex*fy-ey*fx; dx = fst p-vxe 1; dy = snd p-vye 1;
              s = (fy*dx-fx*dy)/det; t_par = (ex*dy-ey*dx)/det
          in ((1-s-t_par)*?cxw + s*vxw j + t_par*vxw(Suc j mod ?nw),
              (1-s-t_par)*?cyw + s*vyw j + t_par*vyw(Suc j mod ?nw)))" .
          hence "phi_fn p = (let ex = vxe(j+2)-vxe 1; ey = vye(j+2)-vye 1;
              fx = vxe ?si-vxe 1; fy = vye ?si-vye 1;
              det = ex*fy-ey*fx; dx = fst p-vxe 1; dy = snd p-vye 1;
              s = (fy*dx-fx*dy)/det; t_par = (ex*dy-ey*dx)/det
          in ((1-s-t_par)*?cxw + s*vxw j + t_par*vxw(Suc j mod ?nw),
              (1-s-t_par)*?cyw + s*vyw j + t_par*vyw(Suc j mod ?nw)))"
            by (cases p) (simp add: Let_def) \<comment> \<open>Was bare (cases p) simp (~25s).\<close>
          thus "phi_fn p = affine_j p" unfolding affine_j_def Let_def by (by100 simp)
        qed
        \<comment> \<open>affine\\_j is continuous (affine function of fst p, snd p).\<close>
        have haffine_cont: "continuous_on (sector_set j) affine_j"
        proof -
          \<comment> \<open>Expand affine\\_j to a direct formula (no let), then apply continuous\\_intros.\<close>
          let ?ex = "vxe(j+2)-vxe 1" and ?ey = "vye(j+2)-vye 1"
          let ?fx = "vxe ?si-vxe 1" and ?fy = "vye ?si-vye 1"
          let ?det = "?ex*?fy-?ey*?fx"
          have hdet_ne: "?det \<noteq> 0"
          proof -
            from hdet_pos[rule_format, OF hj] have "?det > 0" by (by100 simp)
            thus ?thesis by linarith
          qed
          \<comment> \<open>affine\\_j p = explicit formula in fst p, snd p.\<close>
          have haffine_expand: "\<And>p. affine_j p =
            (let dx = fst p-vxe 1; dy = snd p-vye 1;
                 s = (?fy*dx-?fx*dy)/?det; t = (?ex*dy-?ey*dx)/?det
            in ((1-s-t)*?cxw + s*vxw j + t*vxw(Suc j mod ?nw),
                (1-s-t)*?cyw + s*vyw j + t*vyw(Suc j mod ?nw)))"
            unfolding affine_j_def Let_def by simp
          \<comment> \<open>Each component is continuous (affine in fst p, snd p with constant det).\<close>
          have "continuous_on (sector_set j) (\<lambda>p. affine_j p)"
            unfolding haffine_expand Let_def using hdet_ne
            by (intro continuous_intros) auto
          thus ?thesis by simp
        qed
        \<comment> \<open>phi\\_fn = affine\\_j on sector => phi\\_fn continuous on sector.\<close>
        have "continuous_on (sector_set j) phi_fn \<longleftrightarrow> continuous_on (sector_set j) affine_j"
          by (rule continuous_on_cong) (use hphi_eq in auto)
        thus "continuous_on (sector_set j) phi_fn" using haffine_cont by simp
      qed
      \<comment> \<open>Step C: continuous\\_on\\_closed\\_Union gives continuous\\_on P\\_e phi\\_fn.\<close>
      have hcont_on: "continuous_on P_e phi_fn"
      proof -
        have "P_e = (\<Union>j\<in>{..<?nw}. sector_set j)" using hsector_cover by simp
        moreover have "finite {..<?nw}" by simp
        moreover have "\<And>j. j \<in> {..<?nw} \<Longrightarrow> closed (sector_set j)"
          using hsector_R2_closed by (by100 simp)
        moreover have "\<And>j. j \<in> {..<?nw} \<Longrightarrow> continuous_on (sector_set j) phi_fn"
          using hsector_cont_on by (by100 simp)
        ultimately show ?thesis
          using continuous_on_closed_Union[of "{..<?nw}" sector_set phi_fn] by simp
      qed
      \<comment> \<open>Step D: Transfer from continuous\\_on to top1\\_continuous\\_map\\_on via bridge lemma.\<close>
      have prop2: "top1_continuous_map_on P_e
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_e)
          P_w (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_w) phi_fn"
        using top1_continuous_map_on_real2_subspace_general[of P_e phi_fn P_w]
          prop1 hcont_on by (by100 blast)
      have prop3: "phi_fn ` P_e = P_w"
      proof (rule set_eqI, rule iffI)
        \<comment> \<open>\\<subseteq>: from prop1.\<close>
        fix q assume "q \<in> phi_fn ` P_e"
        then obtain p where "p \<in> P_e" "phi_fn p = q" by blast
        from prop1[rule_format, OF \<open>p \<in> P_e\<close>] show "q \<in> P_w" using \<open>phi_fn p = q\<close> by simp
      next
        \<comment> \<open>\\<supseteq>: construct preimage for each q \\<in> P\\_w.\<close>
        fix q assume hq: "q \<in> P_w"
        \<comment> \<open>Every edge point of P\\_w has a preimage via hphi\\_on\\_nonspur.\<close>
        \<comment> \<open>The centroid has preimage v\\_1.\<close>
        \<comment> \<open>General: use inverse affine map on each sector.\<close>
        \<comment> \<open>Construct preimage: express q in centroid-cone sector j of P\\_w,
           then define p = (1-s-t)*v\\_1 + s*v\\_{j+2} + t*v\\_{si} in corresponding source sector.
           phi\\_fn(p) = q by the affine formula, p \\<in> P\\_e by convex combination.\<close>
        \<comment> \<open>Step 1: q is on some edge or in some sector of P\\_w.\<close>
        \<comment> \<open>Case: q is on edge k of P\\_w. Preimage: edge\\_pt\\_e(k+2, t).\<close>
        \<comment> \<open>Case: q = centroid. Preimage: v\\_1.\<close>
        \<comment> \<open>Case: q is in interior of sector j. Preimage: inverse affine in source sector j.\<close>
        \<comment> \<open>Construct preimage via sector inverse.
           q \\<in> P\\_w = conv(u\\_0,...,u\\_{nw-1}). Express q = \\<Sum> \\<mu>\\_k * u\\_k.
           Define p = (1-\\<Sum>\\<mu>)*v\\_1 + \\<Sum> \\<mu>\\_k * v\\_{k+2}. Then p \\<in> P\\_e.
           BUT phi\\_fn(p) \\<noteq> q since phi\\_fn is piecewise, not global.
           Instead: find the sector j containing q (target fan cover), then
           invert the j-th affine map: p = (1-s-t)*v\\_1 + s*v\\_{j+2} + t*v\\_{si}
           where (s,t) are barycentric coords of q in conv(centroid, u\\_j, u\\_{j+1}).\<close>
        \<comment> \<open>Target fan cover: every q \\<in> P\\_w lies in some centroid-cone sector.
           I.e. \\<exists> j < nw. \\<exists> s t. s \\<ge> 0 \\<and> t \\<ge> 0 \\<and> s+t \\<le> 1 \\<and>
           q = (1-s-t)*(cxw,cyw) + s*(vxw j,vyw j) + t*(vxw(Suc j mod nw),vyw(Suc j mod nw)).
           Proof: define cross\\_cw j q analogously to cross\\_v1.
           The centroid is strictly interior (from hC10\\_w), so the fan from cw covers P\\_w.
           The same discrete IVT argument as hfan\\_cover applies.\<close>
        have htarget_fan: "\<exists>j<?nw. \<exists>s t::real. s \<ge> 0 \<and> t \<ge> 0 \<and> s + t \<le> 1 \<and>
            fst q = (1-s-t)*?cxw + s*vxw j + t*vxw(Suc j mod ?nw) \<and>
            snd q = (1-s-t)*?cyw + s*vyw j + t*vyw(Suc j mod ?nw)"
        proof -
          \<comment> \<open>Define target cross product from centroid:\<close>
          define cross_cw where "cross_cw j q' =
            (vxw j - ?cxw) * (snd q' - ?cyw) - (vyw j - ?cyw) * (fst q' - ?cxw)" for j q'
          \<comment> \<open>Target sector test: q' is in centroid-cone sector j.\<close>
          define in_tsector where "in_tsector j q' =
            (cross_cw j q' \<ge> 0 \<and> cross_cw (Suc j mod ?nw) q' \<le> 0)" for j q'
          \<comment> \<open>The target determinant at sector j is > 0 (from hC10\\_w).\<close>
          have hdet_w_pos: "\<forall>j<?nw. (vxw j - ?cxw) * (vyw(Suc j mod ?nw) - ?cyw) -
              (vyw j - ?cyw) * (vxw(Suc j mod ?nw) - ?cxw) > 0"
          proof (intro allI impI)
            fix j assume "j < ?nw"
            from hC10_w[rule_format, OF this] show "(vxw j - ?cxw) * (vyw(Suc j mod ?nw) - ?cyw) -
                (vyw j - ?cyw) * (vxw(Suc j mod ?nw) - ?cxw) > 0" by (by100 simp)
          qed
          \<comment> \<open>Every q \\<in> P\\_w is either the centroid or in some target sector.
             (Discrete IVT on cross\\_cw, analogous to hfan\\_cover.)\<close>
          have hq_cw_or_sector: "q = (?cxw, ?cyw) \<or> (\<exists>j<?nw. in_tsector j q)"
          proof (cases "q = (?cxw, ?cyw)")
            case True thus ?thesis by simp
          next
            case False
            \<comment> \<open>q \\<noteq> centroid. Find sector j with cross\\_cw(j,q) \\<ge> 0 and cross\\_cw(j+1,q) \\<le> 0.\<close>
            \<comment> \<open>Key: the cross products cycle around. There exists j with cross\\_cw(j) \\<ge> 0 (since
               not all can be < 0: that would put q outside P\\_w). Among all such j, the LEAST
               one with j < nw has cross\\_cw(Suc j mod nw) \\<le> 0 by the cyclic ordering.\<close>
            \<comment> \<open>Approach: express cross\\_cw as sum of vertex contributions.
               For k=j: cross\\_cw(j, u\\_j) = 0. For k=j+1: cross\\_cw(j, u\\_{j+1}) = C10 > 0.
               For other k: depends on position. Sum over all k with coefficients \\<mu>\\_k.
               Since cross\\_cw(j, q) depends linearly on q, and vertices go around the centroid,
               there's always a sign change.\<close>
            \<comment> \<open>For now: sorry the discrete IVT. This mirrors hfan\\_cover (~200 lines).\<close>
            \<comment> \<open>Express cross\\_cw as linear combination of vertex cross products.\<close>
            from hq obtain coeffs_q where hcq: "(\<forall>i<?nw. coeffs_q i \<ge> 0)"
              "(\<Sum>i<?nw. coeffs_q i) = 1" "fst q = (\<Sum>i<?nw. coeffs_q i * vxw i)"
              "snd q = (\<Sum>i<?nw. coeffs_q i * vyw i)" using hC5_w by (by100 auto)
            \<comment> \<open>cross\\_cw(j, u\\_j) = 0, cross\\_cw(j, u\\_{j+1}) > 0 (from C10\\_w),
               cross\\_cw(j, u\\_k) for other k can be positive or negative.
               Key: since q \\<noteq> centroid and q \\<in> P\\_w, there exist j1 with cross\\_cw(j1,q) > 0
               and j2 with cross\\_cw(j2,q) < 0. By cyclic IVT, there's a consecutive sign change.\<close>
            \<comment> \<open>cross\\_cw(j, q) is linear in q: cross\\_cw(j, q) = \\<Sum> \\<mu>\\_k * cross\\_cw(j, u\\_k).\<close>
            \<comment> \<open>For the cyclic IVT, we need: \\<exists>j. cross\\_cw(j,q) \\<ge> 0 \\<and> cross\\_cw(Suc j mod nw, q) \\<le> 0.\<close>
            \<comment> \<open>This is a discrete IVT on a cyclic sequence. The proof mirrors hfan\\_cover.\<close>
            \<comment> \<open>Cyclic discrete IVT: \\<Sum> cross\\_cw(j, q) = 0 (centroid = mean of vertices).
               So not all cross\\_cw(j,q) have the same sign. Find consecutive sign change.\<close>
            have hsum_cross_zero: "(\<Sum>j<?nw. cross_cw j q) = 0"
            proof -
              \<comment> \<open>cross\\_cw(j, q) = (vxw j-cxw)*(snd q-cyw) - (vyw j-cyw)*(fst q-cxw).
                 Sum over j: (\\<Sum>(vxw j-cxw))*(snd q-cyw) - (\\<Sum>(vyw j-cyw))*(fst q-cxw).
                 \\<Sum>(vxw j-cxw) = \\<Sum> vxw j - nw*cxw = nw*cxw - nw*cxw = 0.\<close>
              have "(\<Sum>j<?nw. cross_cw j q) =
                  (\<Sum>j<?nw. (vxw j-?cxw))*(snd q-?cyw) - (\<Sum>j<?nw. (vyw j-?cyw))*(fst q-?cxw)"
              proof -
                have "(\<Sum>j<?nw. cross_cw j q) =
                    (\<Sum>j<?nw. ((vxw j-?cxw)*(snd q-?cyw) - (vyw j-?cyw)*(fst q-?cxw)))"
                  unfolding cross_cw_def by simp
                also have "\<dots> = (\<Sum>j<?nw. (vxw j-?cxw)*(snd q-?cyw)) - (\<Sum>j<?nw. (vyw j-?cyw)*(fst q-?cxw))"
                  by (rule sum_subtractf)
                also have "(\<Sum>j<?nw. (vxw j-?cxw)*(snd q-?cyw)) = (\<Sum>j<?nw. (vxw j-?cxw))*(snd q-?cyw)"
                  by (simp add: sum_distrib_right)
                also have "(\<Sum>j<?nw. (vyw j-?cyw)*(fst q-?cxw)) = (\<Sum>j<?nw. (vyw j-?cyw))*(fst q-?cxw)"
                  by (simp add: sum_distrib_right)
                finally show ?thesis .
              qed
              moreover have "(\<Sum>j<?nw. (vxw j-?cxw)) = 0"
              proof -
                have "(\<Sum>j<?nw. (vxw j-?cxw)) = (\<Sum>j<?nw. vxw j) - ?nw*?cxw"
                  by (simp add: sum_subtractf)
                also have "?nw*?cxw = (\<Sum>j<?nw. vxw j)"
                  using hnw_pos by (by100 simp)
                finally show ?thesis by simp
              qed
              moreover have "(\<Sum>j<?nw. (vyw j-?cyw)) = 0"
              proof -
                have "(\<Sum>j<?nw. (vyw j-?cyw)) = (\<Sum>j<?nw. vyw j) - ?nw*?cyw"
                  by (simp add: sum_subtractf)
                also have "?nw*?cyw = (\<Sum>j<?nw. vyw j)"
                  using hnw_pos by (by100 simp)
                finally show ?thesis by simp
              qed
              ultimately show ?thesis by simp
            qed
            \<comment> \<open>q \\<noteq> cw, so not all cross\\_cw = 0. With sum = 0, both signs exist.\<close>
            have hhas_pos: "\<exists>j<?nw. cross_cw j q > 0"
            proof (rule ccontr)
              assume "\<not>(\<exists>j<?nw. cross_cw j q > 0)"
              hence hall_le: "\<forall>j<?nw. cross_cw j q \<le> 0"
                by (by100 fastforce)
              \<comment> \<open>Sum \\<le> 0, but sum = 0, so all = 0.\<close>
              hence "(\<Sum>j<?nw. cross_cw j q) \<le> 0" by (intro sum_nonpos) auto
              with hsum_cross_zero have "(\<Sum>j<?nw. cross_cw j q) = 0" by linarith
              \<comment> \<open>All \\<le> 0 and sum = 0 implies all = 0.\<close>
              \<comment> \<open>All \\<le> 0 and sum = 0 implies all = 0.\<close>
              have "\<forall>j<?nw. -(cross_cw j q) \<ge> 0" using hall_le by auto
              hence "(\<Sum>j<?nw. -(cross_cw j q)) \<ge> 0" by (intro sum_nonneg) auto
              hence "(\<Sum>j<?nw. -(cross_cw j q)) = 0" using hsum_cross_zero
                by (simp add: sum_negf)
              hence "\<forall>j\<in>{..<?nw}. -(cross_cw j q) = 0"
                using sum_nonneg_eq_0_iff[of "{..<?nw}" "\<lambda>j. -(cross_cw j q)"]
                  \<open>\<forall>j<?nw. -(cross_cw j q) \<ge> 0\<close> by auto
              hence "\<forall>j<?nw. cross_cw j q = 0" by auto
              \<comment> \<open>All cross products = 0 means q lies on all rays from cw, hence q = cw.
                 cross\\_cw(0,q) = 0 and cross\\_cw(1,q) = 0 gives a 2x2 system.
                 det of system = det(u\\_0-cw, u\\_1-cw) > 0 (from C10 at j=0).
                 So unique solution: fst q = cxw, snd q = cyw.\<close>
              hence "q = (?cxw, ?cyw)"
              proof -
                assume hall: "\<forall>j<?nw. cross_cw j q = 0"
                have h0: "0 < ?nw" using hnw_pos .
                have h1: "1 < ?nw" using hlen by linarith
                from hall[rule_format, OF h0] have "cross_cw 0 q = 0" .
                hence heq0: "(vxw 0-?cxw)*(snd q-?cyw) = (vyw 0-?cyw)*(fst q-?cxw)"
                  unfolding cross_cw_def by linarith
                from hall[rule_format, OF h1] have "cross_cw 1 q = 0" .
                hence heq1: "(vxw 1-?cxw)*(snd q-?cyw) = (vyw 1-?cyw)*(fst q-?cxw)"
                  unfolding cross_cw_def by linarith
                \<comment> \<open>2x2 system with det = C10 at j=0 > 0.\<close>
                have hmod1: "Suc 0 mod ?nw = 1" using hlen by simp
                from hC10_w[rule_format, OF h0]
                have "(vxw 0 - ?cxw) * (vyw(Suc 0 mod ?nw) - ?cyw) -
                    (vyw 0 - ?cyw) * (vxw(Suc 0 mod ?nw) - ?cxw) > 0" by (by100 simp)
                hence hdet01: "(vxw 0-?cxw)*(vyw 1-?cyw)-(vyw 0-?cyw)*(vxw 1-?cxw) > 0"
                  using hmod1 by simp
                \<comment> \<open>Cramer: from 2x2 system with nonzero det, solve fst q = cxw, snd q = cyw.\<close>
                have hdet_ne: "(vxw 0-?cxw)*(vyw 1-?cyw)-(vyw 0-?cyw)*(vxw 1-?cxw) \<noteq> 0"
                  using hdet01 by linarith
                \<comment> \<open>From heq0 and heq1: (a0*(snd q-cyw) = b0*(fst q-cxw)) and
                   (a1*(snd q-cyw) = b1*(fst q-cxw)) where det(a,b) \\<noteq> 0.
                   Cross: a0*b1*(fst q-cxw) = a0*(snd q-cyw)*... -> (fst q-cxw)*det = 0.\<close>
                have "fst q = ?cxw \<and> snd q = ?cyw"
                proof -
                  define a0 where "a0 = vxw 0 - ?cxw"
                  define b0 where "b0 = vyw 0 - ?cyw"
                  define a1 where "a1 = vxw 1 - ?cxw"
                  define b1 where "b1 = vyw 1 - ?cyw"
                  define dx where "dx = fst q - ?cxw"
                  define dy where "dy = snd q - ?cyw"
                  from heq0 have h0': "a0*dy = b0*dx"
                    unfolding a0_def b0_def dx_def dy_def by linarith
                  from heq1 have h1': "a1*dy = b1*dx"
                    unfolding a1_def b1_def dx_def dy_def by linarith
                  have hD: "a0*b1 - b0*a1 > 0" using hdet01
                    unfolding a0_def b0_def a1_def b1_def by simp
                  \<comment> \<open>Cramer: (a0*b1-b0*a1)*dy = a0*b1*dy - b0*a1*dy
                     = b1*(a0*dy) - a1*(b0*dy) = b1*(b0*dx) - a1*(b0*dy)
                     = b0*(b1*dx - a1*dy) = b0*(a1*dy - a1*dy) ... hmm.
                     Better: a0*dy = b0*dx and a1*dy = b1*dx.
                     So (a0*b1)*dy = b0*b1*dx and (b0*a1)*dy = b0*b1*dx.
                     Hence (a0*b1-b0*a1)*dy = 0.\<close>
                  have "(a0*b1)*dy = b1*(a0*dy)" by (by100 algebra)
                  also have "\<dots> = b1*(b0*dx)" using h0' by simp
                  finally have hA: "(a0*b1)*dy = b1*b0*dx" by (by100 algebra)
                  have "(b0*a1)*dy = b0*(a1*dy)" by (by100 algebra)
                  also have "\<dots> = b0*(b1*dx)" using h1' by simp
                  finally have hB: "(b0*a1)*dy = b0*b1*dx" by (by100 algebra)
                  have "(a0*b1-b0*a1)*dy = a0*b1*dy - b0*a1*dy" by (by100 algebra)
                  also have "\<dots> = b1*b0*dx - b0*b1*dx" using hA hB by linarith
                  also have "\<dots> = 0" by (by100 algebra)
                  finally have "(a0*b1-b0*a1)*dy = 0" .
                  hence "dy = 0" using hD by (by100 simp)
                  hence "dx = 0"
                  proof -
                    assume "dy = 0"
                    from h0' \<open>dy = 0\<close> have "b0*dx = 0" by simp
                    hence "b0 = 0 \<or> dx = 0" by (by100 auto)
                    thus "dx = 0"
                    proof
                      assume "b0 = 0"
                      from hD \<open>b0 = 0\<close> have "a0*b1 > 0" by simp
                      hence "b1 \<noteq> 0" by auto
                      from h1' \<open>dy = 0\<close> have "b1*dx = 0" by simp
                      with \<open>b1 \<noteq> 0\<close> show "dx = 0" by simp
                    next
                      assume "dx = 0" thus ?thesis .
                    qed
                  qed
                  from \<open>dx = 0\<close> \<open>dy = 0\<close> show ?thesis
                    unfolding dx_def dy_def by auto
                qed
                thus ?thesis by (cases q) auto
              qed
              with False show False by simp
            qed
            have hhas_neg: "\<exists>j<?nw. cross_cw j q < 0"
            proof (rule ccontr)
              assume "\<not>(\<exists>j<?nw. cross_cw j q < 0)"
              hence hall_ge: "\<forall>j<?nw. cross_cw j q \<ge> 0" by (by100 fastforce)
              hence "(\<Sum>j<?nw. cross_cw j q) \<ge> 0" by (intro sum_nonneg) auto
              hence "(\<Sum>j<?nw. cross_cw j q) = 0" using hsum_cross_zero by simp
              hence "\<forall>j\<in>{..<?nw}. cross_cw j q = 0"
                using sum_nonneg_eq_0_iff[of "{..<?nw}" "\<lambda>j. cross_cw j q"] hall_ge by auto
              hence hall: "\<forall>j<?nw. cross_cw j q = 0" by auto
              hence "q = (?cxw, ?cyw)"
              proof -
                have h0: "0 < ?nw" using hnw_pos .
                have h1: "1 < ?nw" using hlen by linarith
                from hall[rule_format, OF h0] have "cross_cw 0 q = 0" .
                hence heq0: "(vxw 0-?cxw)*(snd q-?cyw) = (vyw 0-?cyw)*(fst q-?cxw)"
                  unfolding cross_cw_def by linarith
                from hall[rule_format, OF h1] have "cross_cw 1 q = 0" .
                hence heq1: "(vxw 1-?cxw)*(snd q-?cyw) = (vyw 1-?cyw)*(fst q-?cxw)"
                  unfolding cross_cw_def by linarith
                have hmod1': "Suc 0 mod ?nw = 1" using hlen by simp
                from hC10_w[rule_format, OF h0]
                have "(vxw 0 - ?cxw) * (vyw(Suc 0 mod ?nw) - ?cyw) -
                    (vyw 0 - ?cyw) * (vxw(Suc 0 mod ?nw) - ?cxw) > 0" by (by100 simp)
                hence hdet01: "(vxw 0-?cxw)*(vyw 1-?cyw)-(vyw 0-?cyw)*(vxw 1-?cxw) > 0"
                  using hmod1' by simp
                \<comment> \<open>Same Cramer argument as in hhas\\_pos.\<close>
                have "fst q = ?cxw \<and> snd q = ?cyw"
                proof -
                  define a0 where "a0 = vxw 0 - ?cxw"
                  define b0 where "b0 = vyw 0 - ?cyw"
                  define a1 where "a1 = vxw 1 - ?cxw"
                  define b1 where "b1 = vyw 1 - ?cyw"
                  define dx where "dx = fst q - ?cxw"
                  define dy where "dy = snd q - ?cyw"
                  from heq0 have h0': "a0*dy = b0*dx"
                    unfolding a0_def b0_def dx_def dy_def by linarith
                  from heq1 have h1': "a1*dy = b1*dx"
                    unfolding a1_def b1_def dx_def dy_def by linarith
                  have hD: "a0*b1 - b0*a1 > 0" using hdet01
                    unfolding a0_def b0_def a1_def b1_def by simp
                  have "(a0*b1)*dy = b1*(a0*dy)" by (by100 algebra)
                  also have "\<dots> = b1*(b0*dx)" using h0' by simp
                  finally have hA: "(a0*b1)*dy = b1*b0*dx" by (by100 algebra)
                  have "(b0*a1)*dy = b0*(a1*dy)" by (by100 algebra)
                  also have "\<dots> = b0*(b1*dx)" using h1' by simp
                  finally have hB: "(b0*a1)*dy = b0*b1*dx" by (by100 algebra)
                  have "(a0*b1-b0*a1)*dy = a0*b1*dy - b0*a1*dy" by (by100 algebra)
                  also have "\<dots> = b1*b0*dx - b0*b1*dx" using hA hB by linarith
                  also have "\<dots> = 0" by (by100 algebra)
                  finally have "(a0*b1-b0*a1)*dy = 0" .
                  hence "dy = 0" using hD by (by100 simp)
                  hence "dx = 0"
                  proof -
                    assume "dy = 0"
                    from h0' \<open>dy = 0\<close> have "b0*dx = 0" by simp
                    hence "b0 = 0 \<or> dx = 0" by (by100 auto)
                    thus "dx = 0"
                    proof
                      assume "b0 = 0"
                      from hD \<open>b0 = 0\<close> have "a0*b1 > 0" by simp
                      hence "b1 \<noteq> 0" by auto
                      from h1' \<open>dy = 0\<close> have "b1*dx = 0" by simp
                      with \<open>b1 \<noteq> 0\<close> show "dx = 0" by simp
                    next
                      assume "dx = 0" thus ?thesis .
                    qed
                  qed
                  from \<open>dx = 0\<close> \<open>dy = 0\<close> show ?thesis
                    unfolding dx_def dy_def by auto
                qed
                thus ?thesis by (cases q) auto
              qed
              with False show False by simp
            qed
            \<comment> \<open>Cyclic IVT: there's a consecutive sign change \\<ge>0 then \\<le>0.\<close>
            from hhas_neg obtain j2 where hj2: "j2 < ?nw" and hj2_neg: "cross_cw j2 q < 0"
              by blast
            \<comment> \<open>Walk backwards from j2 until we find j with cross\\_cw(j,q) \\<ge> 0.\<close>
            \<comment> \<open>The predecessor (j2-1) mod nw either has cross\\_cw \\<ge> 0 (done) or < 0 (continue).
               Since there exists j1 with cross\\_cw > 0, we must find one within nw steps.\<close>
            have "\<exists>j<?nw. cross_cw j q \<ge> 0 \<and> cross_cw (Suc j mod ?nw) q \<le> 0"
              by (rule cyclic_sign_change[OF _ hhas_pos hhas_neg]) (use hnw_pos in linarith)
            thus ?thesis unfolding in_tsector_def by auto
          qed
          \<comment> \<open>Convert sector membership to barycentric coordinates.\<close>
          show ?thesis
          proof (cases "q = (?cxw, ?cyw)")
            case True
            \<comment> \<open>q = centroid: take j=0, s=0, t=0.\<close>
            have "0 < ?nw" using hnw_pos .
            moreover have "(0::real) \<ge> 0" "(0::real) \<ge> 0" "(0::real) + (0::real) \<le> 1" by auto
            moreover have "fst q = (1-0-0)*?cxw + 0*vxw 0 + 0*vxw(Suc 0 mod ?nw)"
              using True by simp
            moreover have "snd q = (1-0-0)*?cyw + 0*vyw 0 + 0*vyw(Suc 0 mod ?nw)"
              using True by simp
            ultimately show ?thesis by (by100 blast)
          next
            case False
            from hq_cw_or_sector False obtain jw where hjw: "jw < ?nw" and hin: "in_tsector jw q"
              by blast
            \<comment> \<open>Extract cross product signs.\<close>
            from hin have hcross_ge: "cross_cw jw q \<ge> 0"
              and hcross_le: "cross_cw (Suc jw mod ?nw) q \<le> 0"
              unfolding in_tsector_def by auto
            \<comment> \<open>Compute barycentric coords via Cramer.\<close>
            let ?ew_x = "vxw jw - ?cxw" and ?ew_y = "vyw jw - ?cyw"
            let ?fw_x = "vxw(Suc jw mod ?nw) - ?cxw"
            let ?fw_y = "vyw(Suc jw mod ?nw) - ?cyw"
            let ?detw = "?ew_x*?fw_y - ?ew_y*?fw_x"
            have hdetw_pos: "?detw > 0"
              using hdet_w_pos[rule_format, OF hjw] by simp
            have hdetw_ne: "?detw \<noteq> 0" using hdetw_pos by linarith
            let ?dxw = "fst q - ?cxw" and ?dyw = "snd q - ?cyw"
            define sw where "sw = (?fw_y*?dxw - ?fw_x*?dyw) / ?detw"
            define tw where "tw = (?ew_x*?dyw - ?ew_y*?dxw) / ?detw"
            \<comment> \<open>sw = cross\\_cw(jw, q) / detw \\<ge> 0.\<close>
            have hsw_ge: "sw \<ge> 0"
            proof -
              \<comment> \<open>numerator of sw = -cross\\_cw(Suc jw mod nw, q) \\<ge> 0.\<close>
              have "?fw_y*?dxw - ?fw_x*?dyw = -(cross_cw (Suc jw mod ?nw) q)"
                unfolding cross_cw_def by (by100 algebra)
              hence "?fw_y*?dxw - ?fw_x*?dyw \<ge> 0" using hcross_le by linarith
              thus ?thesis unfolding sw_def using hdetw_pos by (by100 simp)
            qed
            have htw_ge: "tw \<ge> 0"
            proof -
              \<comment> \<open>numerator of tw = cross\\_cw(jw, q) \\<ge> 0.\<close>
              have "?ew_x*?dyw - ?ew_y*?dxw = cross_cw jw q"
                unfolding cross_cw_def by (by100 simp)
              hence "?ew_x*?dyw - ?ew_y*?dxw \<ge> 0" using hcross_ge by linarith
              thus ?thesis unfolding tw_def using hdetw_pos by (by100 simp)
            qed
            \<comment> \<open>Cramer inverse: sw*detw = fw\\_y*dxw-fw\\_x*dyw, tw*detw = ew\\_x*dyw-ew\\_y*dxw.\<close>
            have hsw_mul: "sw*?detw = ?fw_y*?dxw-?fw_x*?dyw"
              unfolding sw_def using hdetw_ne by simp
            have htw_mul: "tw*?detw = ?ew_x*?dyw-?ew_y*?dxw"
              unfolding tw_def using hdetw_ne by simp
            have hst_le: "sw + tw \<le> 1"
            proof -
              \<comment> \<open>Sufficient: (1-sw-tw)*detw \\<ge> 0. Since detw > 0, this gives 1-sw-tw \\<ge> 0.\<close>
              \<comment> \<open>(1-sw-tw)*detw = detw - sw*detw - tw*detw
                 = (ew\\_x*fw\\_y-ew\\_y*fw\\_x) - (fw\\_y*dxw-fw\\_x*dyw) - (ew\\_x*dyw-ew\\_y*dxw)
                 = cross product from edge u\\_j->u\\_{j+1} at q relative to centroid.
                 This equals det(u\\_{j+1}-u\\_j, q-u\\_j) which is non-negative for q \\<in> P\\_w
                 by C11 and convexity.\<close>
              \<comment> \<open>Name all values to avoid expansion of sum/div expressions.\<close>
              define ex_val where "ex_val = ?ew_x"
              define ey_val where "ey_val = ?ew_y"
              define fx_val where "fx_val = ?fw_x"
              define fy_val where "fy_val = ?fw_y"
              define detw_val where "detw_val = ex_val*fy_val - ey_val*fx_val"
              define dxw_val where "dxw_val = ?dxw"
              define dyw_val where "dyw_val = ?dyw"
              have hdetw_eq: "detw_val = ?detw" unfolding detw_val_def ex_val_def ey_val_def fx_val_def fy_val_def by simp
              have hdetw_val_pos: "detw_val > 0" using hdetw_pos hdetw_eq by simp
              have hsw_m: "sw*detw_val = fy_val*dxw_val-fx_val*dyw_val"
                using hsw_mul hdetw_eq unfolding dxw_val_def dyw_val_def fx_val_def fy_val_def by simp
              have htw_m: "tw*detw_val = ex_val*dyw_val-ey_val*dxw_val"
                using htw_mul hdetw_eq unfolding dxw_val_def dyw_val_def ex_val_def ey_val_def by simp
              \<comment> \<open>(1-sw-tw)*D = det(u\\_{jw+1}-u\\_jw, q-u\\_jw) \\<ge> 0 by C11 + convexity.\<close>
              \<comment> \<open>Fact: for all k, det(u\\_{jw+1}-u\\_jw, u\\_k-u\\_jw) \\<ge> 0.\<close>
              have hec_vertex: "\<forall>k<?nw. (vxw(Suc jw mod ?nw)-vxw jw)*(vyw k-vyw jw)-
                  (vyw(Suc jw mod ?nw)-vyw jw)*(vxw k-vxw jw) \<ge> 0"
              proof (intro allI impI)
                fix k assume hk: "k < ?nw"
                show "(vxw(Suc jw mod ?nw)-vxw jw)*(vyw k-vyw jw)-
                    (vyw(Suc jw mod ?nw)-vyw jw)*(vxw k-vxw jw) \<ge> 0"
                proof (cases "k = jw \<or> k = Suc jw mod ?nw")
                  case True thus ?thesis by (elim disjE) simp_all
                next
                  case False hence "k \<noteq> jw" "k \<noteq> Suc jw mod ?nw" by auto
                  \<comment> \<open>C11: det(u\\_k-u\\_jw, u\\_{jw+1}-u\\_jw) < 0.
                     So det(u\\_{jw+1}-u\\_jw, u\\_k-u\\_jw) = -det(u\\_k-u\\_jw, u\\_{jw+1}-u\\_jw) > 0.\<close>
                  from hC11_w[rule_format, OF hjw hk \<open>k \<noteq> jw\<close> \<open>k \<noteq> Suc jw mod ?nw\<close>]
                  have hC11_inst: "(vxw k-vxw jw)*(vyw(Suc jw mod ?nw)-vyw jw)-
                      (vyw k-vyw jw)*(vxw(Suc jw mod ?nw)-vxw jw) < 0" .
                  \<comment> \<open>Negation: det(B-A, C-A) = -det(C-A, B-A).\<close>
                  let ?ax = "vxw jw" and ?ay = "vyw jw"
                  let ?bx = "vxw(Suc jw mod ?nw)" and ?by' = "vyw(Suc jw mod ?nw)"
                  let ?kx = "vxw k" and ?ky = "vyw k"
                  have "(?bx-?ax)*(?ky-?ay)-(?by'-?ay)*(?kx-?ax) =
                      -((?kx-?ax)*(?by'-?ay)-(?ky-?ay)*(?bx-?ax))" by (by100 algebra)
                  hence "(vxw(Suc jw mod ?nw)-vxw jw)*(vyw k-vyw jw)-
                      (vyw(Suc jw mod ?nw)-vyw jw)*(vxw k-vxw jw) > 0"
                    using hC11_inst by linarith
                  thus ?thesis by linarith
                qed
              qed
              \<comment> \<open>ec(q) = \\<Sum> \\<mu>\\_k * ec(u\\_k) \\<ge> 0.\<close>
              from hq obtain coeffs_w where hcw_c: "(\<forall>i<?nw. coeffs_w i \<ge> 0)"
                "(\<Sum>i<?nw. coeffs_w i) = 1" "fst q = (\<Sum>i<?nw. coeffs_w i * vxw i)"
                "snd q = (\<Sum>i<?nw. coeffs_w i * vyw i)"
                using hC5_w by (by100 auto)
              \<comment> \<open>ec(q) \\<ge> 0: by linearity over convex combination.\<close>
              let ?dx_ew = "vxw(Suc jw mod ?nw)-vxw jw"
              let ?dy_ew = "vyw(Suc jw mod ?nw)-vyw jw"
              have hec_at_k: "\<forall>k<?nw. coeffs_w k * (?dx_ew*(vyw k-vyw jw)-?dy_ew*(vxw k-vxw jw)) \<ge> 0"
              proof (intro allI impI)
                fix k assume "k < ?nw"
                from hec_vertex[rule_format, OF this]
                have "?dx_ew*(vyw k-vyw jw)-?dy_ew*(vxw k-vxw jw) \<ge> 0" .
                thus "coeffs_w k * (?dx_ew*(vyw k-vyw jw)-?dy_ew*(vxw k-vxw jw)) \<ge> 0"
                  using hcw_c(1)[rule_format, OF \<open>k < ?nw\<close>]
                  by (intro mult_nonneg_nonneg)
              qed
              \<comment> \<open>ec(q) = \\<Sum> coeffs\\_w k * ec(u\\_k) by linearity.\<close>
              have hec_sum: "?dx_ew*(snd q-vyw jw)-?dy_ew*(fst q-vxw jw) =
                  (\<Sum>k<?nw. coeffs_w k * (?dx_ew*(vyw k-vyw jw)-?dy_ew*(vxw k-vxw jw)))"
              proof -
                \<comment> \<open>Step 1: snd q - vyw jw = \\<Sum> coeffs\\_w k * (vyw k - vyw jw).\<close>
                have hsy: "snd q - vyw jw = (\<Sum>k<?nw. coeffs_w k * (vyw k - vyw jw))"
                proof -
                  have "(\<Sum>k<?nw. coeffs_w k * (vyw k - vyw jw)) =
                      (\<Sum>k<?nw. coeffs_w k * vyw k) - (\<Sum>k<?nw. coeffs_w k * vyw jw)"
                  proof -
                    have "\<And>k. coeffs_w k * (vyw k - vyw jw) = coeffs_w k * vyw k - coeffs_w k * vyw jw"
                      by (by100 algebra)
                    hence "(\<Sum>k<?nw. coeffs_w k * (vyw k - vyw jw)) =
                        (\<Sum>k<?nw. (coeffs_w k * vyw k - coeffs_w k * vyw jw))" by simp
                    also have "\<dots> = (\<Sum>k<?nw. coeffs_w k * vyw k) - (\<Sum>k<?nw. coeffs_w k * vyw jw)"
                      by (rule sum_subtractf)
                    finally show ?thesis .
                  qed
                  also have "(\<Sum>k<?nw. coeffs_w k * vyw jw) = vyw jw"
                  proof -
                    have "(\<Sum>k<?nw. coeffs_w k * vyw jw) = (\<Sum>k<?nw. coeffs_w k) * vyw jw"
                      by (simp add: sum_distrib_right)
                    also have "\<dots> = vyw jw" using hcw_c(2) by simp
                    finally show ?thesis .
                  qed
                  finally show ?thesis using hcw_c(4) by simp
                qed
                \<comment> \<open>Step 2: fst q - vxw jw = \\<Sum> coeffs\\_w k * (vxw k - vxw jw).\<close>
                have hsx: "fst q - vxw jw = (\<Sum>k<?nw. coeffs_w k * (vxw k - vxw jw))"
                proof -
                  have "(\<Sum>k<?nw. coeffs_w k * (vxw k - vxw jw)) =
                      (\<Sum>k<?nw. coeffs_w k * vxw k) - (\<Sum>k<?nw. coeffs_w k * vxw jw)"
                  proof -
                    have "\<And>k. coeffs_w k * (vxw k - vxw jw) = coeffs_w k * vxw k - coeffs_w k * vxw jw"
                      by (by100 algebra)
                    hence "(\<Sum>k<?nw. coeffs_w k * (vxw k - vxw jw)) =
                        (\<Sum>k<?nw. (coeffs_w k * vxw k - coeffs_w k * vxw jw))" by simp
                    also have "\<dots> = (\<Sum>k<?nw. coeffs_w k * vxw k) - (\<Sum>k<?nw. coeffs_w k * vxw jw)"
                      by (rule sum_subtractf)
                    finally show ?thesis .
                  qed
                  also have "(\<Sum>k<?nw. coeffs_w k * vxw jw) = vxw jw"
                  proof -
                    have "(\<Sum>k<?nw. coeffs_w k * vxw jw) = (\<Sum>k<?nw. coeffs_w k) * vxw jw"
                      by (simp add: sum_distrib_right)
                    also have "\<dots> = vxw jw" using hcw_c(2) by simp
                    finally show ?thesis .
                  qed
                  finally show ?thesis using hcw_c(3) by simp
                qed
                \<comment> \<open>Step 3: Distribute dx\\_ew and dy\\_ew through sums.\<close>
                have "?dx_ew*(snd q-vyw jw) = (\<Sum>k<?nw. ?dx_ew*(coeffs_w k*(vyw k-vyw jw)))"
                  using hsy sum_distrib_left[of ?dx_ew "\<lambda>k. coeffs_w k*(vyw k-vyw jw)" "{..<?nw}"]
                  by simp
                moreover have "?dy_ew*(fst q-vxw jw) = (\<Sum>k<?nw. ?dy_ew*(coeffs_w k*(vxw k-vxw jw)))"
                  using hsx sum_distrib_left[of ?dy_ew "\<lambda>k. coeffs_w k*(vxw k-vxw jw)" "{..<?nw}"]
                  by simp
                ultimately have "?dx_ew*(snd q-vyw jw)-?dy_ew*(fst q-vxw jw) =
                    (\<Sum>k<?nw. ?dx_ew*(coeffs_w k*(vyw k-vyw jw))) -
                    (\<Sum>k<?nw. ?dy_ew*(coeffs_w k*(vxw k-vxw jw)))" by simp
                also have "\<dots> = (\<Sum>k<?nw. (?dx_ew*(coeffs_w k*(vyw k-vyw jw)) -
                    ?dy_ew*(coeffs_w k*(vxw k-vxw jw))))"
                  by (rule sum_subtractf[symmetric])
                also have "\<dots> = (\<Sum>k<?nw. coeffs_w k * (?dx_ew*(vyw k-vyw jw)-?dy_ew*(vxw k-vxw jw)))"
                proof (rule sum.cong)
                  fix k assume "k \<in> {..<?nw}"
                  show "?dx_ew*(coeffs_w k*(vyw k-vyw jw)) - ?dy_ew*(coeffs_w k*(vxw k-vxw jw))
                      = coeffs_w k * (?dx_ew*(vyw k-vyw jw)-?dy_ew*(vxw k-vxw jw))"
                    by (by100 algebra)
                qed simp
                finally show ?thesis .
              qed
              have hec_q: "?dx_ew*(snd q-vyw jw)-?dy_ew*(fst q-vxw jw) \<ge> 0"
              proof -
                from hec_sum have "?dx_ew*(snd q-vyw jw)-?dy_ew*(fst q-vxw jw) =
                    (\<Sum>k<?nw. coeffs_w k * (?dx_ew*(vyw k-vyw jw)-?dy_ew*(vxw k-vxw jw)))" .
                also have "\<dots> \<ge> 0" by (rule sum_nonneg) (use hec_at_k in auto)
                finally show ?thesis .
              qed
              \<comment> \<open>Show (1-sw-tw)*detw\\_val = ec(q).\<close>
              have hec_eq: "(1-sw-tw)*detw_val =
                  (vxw(Suc jw mod ?nw)-vxw jw)*(snd q-vyw jw)-
                  (vyw(Suc jw mod ?nw)-vyw jw)*(fst q-vxw jw)"
              proof -
                \<comment> \<open>Express ec(q) using named variables.\<close>
                have hfx_ex: "fx_val - ex_val = vxw(Suc jw mod ?nw) - vxw jw"
                  unfolding fx_val_def ex_val_def by (by100 simp)
                have hfy_ey: "fy_val - ey_val = vyw(Suc jw mod ?nw) - vyw jw"
                  unfolding fy_val_def ey_val_def by (by100 simp)
                have hdxw_ex: "dxw_val - ex_val = fst q - vxw jw"
                  unfolding dxw_val_def ex_val_def by (by100 simp)
                have hdyw_ey: "dyw_val - ey_val = snd q - vyw jw"
                  unfolding dyw_val_def ey_val_def by (by100 simp)
                \<comment> \<open>(1-sw-tw)*D = D - sw*D - tw*D.\<close>
                have h1: "(1-sw-tw)*detw_val = detw_val - sw*detw_val - tw*detw_val"
                  by (by100 algebra)
                \<comment> \<open>Substitute Cramer.\<close>
                hence h2: "(1-sw-tw)*detw_val = detw_val -
                    (fy_val*dxw_val - fx_val*dyw_val) - (ex_val*dyw_val - ey_val*dxw_val)"
                  using hsw_m htw_m by linarith
                \<comment> \<open>ec(q) in named variables.\<close>
                have hec: "(fx_val-ex_val)*(dyw_val-ey_val) - (fy_val-ey_val)*(dxw_val-ex_val) =
                    (vxw(Suc jw mod ?nw)-vxw jw)*(snd q-vyw jw) -
                    (vyw(Suc jw mod ?nw)-vyw jw)*(fst q-vxw jw)"
                  using hfx_ex hfy_ey hdxw_ex hdyw_ey by simp
                \<comment> \<open>Key algebraic identity: D - (fy*dx-fx*dy) - (ex*dy-ey*dx) = (fx-ex)*(dy-ey)-(fy-ey)*(dx-ex).\<close>
                have "detw_val - (fy_val*dxw_val - fx_val*dyw_val) - (ex_val*dyw_val - ey_val*dxw_val)
                    = (fx_val-ex_val)*(dyw_val-ey_val) - (fy_val-ey_val)*(dxw_val-ex_val)"
                  unfolding detw_val_def by (by100 algebra)
                with h2 hec show ?thesis by simp
              qed
              have "(1-sw-tw)*detw_val \<ge> 0" using hec_eq hec_q by linarith
              hence "1 - sw - tw \<ge> 0"
              proof -
                assume h: "0 \<le> (1 - sw - tw) * detw_val"
                show "1 - sw - tw \<ge> 0"
                proof (rule ccontr)
                  assume "\<not> (1 - sw - tw \<ge> 0)"
                  hence "1 - sw - tw < 0" by simp
                  hence "(1-sw-tw)*detw_val < 0"
                    using hdetw_val_pos mult_neg_pos by (by100 blast)
                  with h show False by linarith
                qed
              qed
              thus ?thesis by linarith
            qed
            \<comment> \<open>Cramer inverse: dxw = sw*ew\\_x + tw*fw\\_x, dyw = sw*ew\\_y + tw*fw\\_y.\<close>
            have hdxw_eq: "?dxw = sw*?ew_x + tw*?fw_x"
            proof -
              have "(sw*?ew_x + tw*?fw_x)*?detw =
                  ?ew_x*(sw*?detw) + ?fw_x*(tw*?detw)" by (by100 algebra)
              also have "\<dots> = ?ew_x*(?fw_y*?dxw-?fw_x*?dyw) + ?fw_x*(?ew_x*?dyw-?ew_y*?dxw)"
                using hsw_mul htw_mul by simp
              also have "\<dots> = ?dxw*(?ew_x*?fw_y-?ew_y*?fw_x)" by (by100 algebra)
              finally have "(sw*?ew_x + tw*?fw_x)*?detw = ?dxw*?detw" by simp
              thus ?thesis using hdetw_ne by (by100 simp)
            qed
            have hdyw_eq: "?dyw = sw*?ew_y + tw*?fw_y"
            proof -
              have "(sw*?ew_y + tw*?fw_y)*?detw =
                  ?ew_y*(sw*?detw) + ?fw_y*(tw*?detw)" by (by100 algebra)
              also have "\<dots> = ?ew_y*(?fw_y*?dxw-?fw_x*?dyw) + ?fw_y*(?ew_x*?dyw-?ew_y*?dxw)"
                using hsw_mul htw_mul by simp
              also have "\<dots> = ?dyw*(?ew_x*?fw_y-?ew_y*?fw_x)" by (by100 algebra)
              finally have "(sw*?ew_y + tw*?fw_y)*?detw = ?dyw*?detw" by simp
              thus ?thesis using hdetw_ne by (by100 simp)
            qed
            have hqx_eq: "fst q = (1-sw-tw)*?cxw + sw*vxw jw + tw*vxw(Suc jw mod ?nw)"
            proof -
              have "fst q = ?cxw + ?dxw" by simp
              also have "?dxw = sw*(vxw jw - ?cxw) + tw*(vxw(Suc jw mod ?nw) - ?cxw)"
                using hdxw_eq by simp
              finally show ?thesis by (by100 algebra)
            qed
            have hqy_eq: "snd q = (1-sw-tw)*?cyw + sw*vyw jw + tw*vyw(Suc jw mod ?nw)"
            proof -
              have "snd q = ?cyw + ?dyw" by simp
              also have "?dyw = sw*(vyw jw - ?cyw) + tw*(vyw(Suc jw mod ?nw) - ?cyw)"
                using hdyw_eq by simp
              finally show ?thesis by (by100 algebra)
            qed
            from hjw hsw_ge htw_ge hst_le hqx_eq hqy_eq
            show ?thesis by (by100 blast)
          qed
        qed
        then obtain j s t where hj: "j < ?nw" and hs: "s \<ge> 0" and ht: "t \<ge> 0"
            and hst: "s + t \<le> 1" and hqx: "fst q = (1-s-t)*?cxw + s*vxw j + t*vxw(Suc j mod ?nw)"
            and hqy: "snd q = (1-s-t)*?cyw + s*vyw j + t*vyw(Suc j mod ?nw)" by blast
        \<comment> \<open>Define preimage p using same barycentric coords in source sector j.\<close>
        let ?si = "Suc(j+2) mod ?ne"
        define p where "p = ((1-s-t)*vxe 1 + s*vxe(j+2) + t*vxe ?si,
                              (1-s-t)*vye 1 + s*vye(j+2) + t*vye ?si)"
        \<comment> \<open>p \\<in> P\\_e: it's a convex combination of vertices of P\\_e.\<close>
        have hp_in: "p \<in> P_e"
        proof -
          \<comment> \<open>p is a convex combination of v\\_1, v\\_{j+2}, v\\_{si} (all vertices of P\\_e).\<close>
          have hj2_lt: "j + 2 < ?ne" using hj hne_eq by linarith
          have hsi_lt: "?si < ?ne" using hj2_lt by simp
          have h1_lt: "1 < ?ne" using hlen_ext by linarith
          \<comment> \<open>Key: j+2 \\<noteq> 1 and si \\<noteq> 1 (since j+2 \\<ge> 2 and si \\<ge> 2 or si = 0).\<close>
          have hj2_ne1: "j + 2 \<noteq> 1" by simp
          have hsi_ne_j2: "?si \<noteq> j + 2"
          proof -
            have "?ne \<ge> 3" using hlen_ext by linarith
            hence "Suc(j+2) mod ?ne \<noteq> j+2"
            proof (cases "Suc(j+2) < ?ne")
              case True
              hence "Suc(j+2) mod ?ne = Suc(j+2)" by simp
              thus ?thesis by simp
            next
              case False
              hence "Suc(j+2) \<ge> ?ne" by simp
              moreover have "Suc(j+2) \<le> ?ne" using hj2_lt by simp
              ultimately have "Suc(j+2) = ?ne" by simp
              hence "Suc(j+2) mod ?ne = 0" by simp
              moreover have "j+2 \<ge> 2" by simp
              ultimately show ?thesis by simp
            qed
            thus ?thesis .
          qed
          \<comment> \<open>Define coefficients: 1-s-t at index 1, s at j+2, t at si, 0 elsewhere.\<close>
          define coeffs where "coeffs i = (if i = (1::nat) then 1-s-t
              else if i = j+2 then s else if i = ?si then t else 0)" for i
          have hnn: "\<forall>i<?ne. coeffs i \<ge> 0"
          proof (intro allI impI)
            fix i assume "i < ?ne"
            show "coeffs i \<ge> 0" unfolding coeffs_def using hs ht hst by (by100 simp)
          qed
          \<comment> \<open>Shared index facts for sum splitting.\<close>
          have hfin: "finite ({..<?ne})" by simp
          have h1_in: "1 \<in> {..<?ne}" using h1_lt by simp
          have hj2_in: "j+2 \<in> {..<?ne}" using hj2_lt by simp
          have hsi_in: "?si \<in> {..<?ne}" using hsi_lt by simp
          have hsi_ne1: "?si \<noteq> (1::nat)"
          proof -
            have "?ne \<ge> 5" using hlen_ext hne_eq hlen by linarith
            show ?thesis
            proof (cases "Suc(j+2) < ?ne")
              case True thus ?thesis by simp
            next
              case False
              hence "Suc(j+2) \<ge> ?ne" by simp
              moreover have "Suc(j+2) \<le> ?ne" using hj2_lt by simp
              ultimately have "Suc(j+2) = ?ne" by simp
              thus ?thesis by simp
            qed
          qed
          have hj2_in2: "j+2 \<in> {..<?ne} - {1}" using hj2_in hj2_ne1 by auto
          have hsi_in2: "?si \<in> {..<?ne} - {1} - {j+2}" using hsi_in hsi_ne1 hsi_ne_j2 by auto
          have hsum: "(\<Sum>i<?ne. coeffs i) = 1"
          proof -
            have "(\<Sum>i<?ne. coeffs i) = coeffs 1 + coeffs (j+2) + coeffs ?si +
                (\<Sum>i \<in> {..<?ne} - {1, j+2, ?si}. coeffs i)"
            proof -
              have s1: "(\<Sum>i<?ne. coeffs i) = coeffs 1 + (\<Sum>i \<in> {..<?ne} - {1}. coeffs i)"
                using sum.remove[OF hfin h1_in, of coeffs] by simp
              have s2: "(\<Sum>i \<in> {..<?ne} - {1}. coeffs i) = coeffs (j+2) + (\<Sum>i \<in> {..<?ne} - {1} - {j+2}. coeffs i)"
                using sum.remove[of "{..<?ne} - {1}" "j+2" coeffs] hj2_in2 by simp
              have s3: "(\<Sum>i \<in> {..<?ne} - {1} - {j+2}. coeffs i) = coeffs ?si + (\<Sum>i \<in> {..<?ne} - {1} - {j+2} - {?si}. coeffs i)"
                using sum.remove[of "{..<?ne} - {1} - {j+2}" ?si coeffs] hsi_in2 by simp
              have "({..<?ne} - {1} - {j+2} - {?si}) = ({..<?ne} - {1, j+2, ?si})" by auto
              from s1 s2 s3 this show ?thesis by simp
            qed
            also have "(\<Sum>i \<in> {..<?ne} - {1, j+2, ?si}. coeffs i) = 0"
              unfolding coeffs_def by (rule sum.neutral) auto
            also have "coeffs 1 + coeffs (j+2) + coeffs ?si + 0 = (1-s-t) + s + t"
              unfolding coeffs_def using hj2_ne1 hsi_ne_j2 hsi_ne1 by simp
            finally show ?thesis by simp
          qed
          have hx: "fst p = (\<Sum>i<?ne. coeffs i * vxe i)"
          proof -
            have "(\<Sum>i<?ne. coeffs i * vxe i) = coeffs 1 * vxe 1 + coeffs (j+2) * vxe (j+2) +
                coeffs ?si * vxe ?si + (\<Sum>i \<in> {..<?ne} - {1, j+2, ?si}. coeffs i * vxe i)"
            proof -
              have s1: "(\<Sum>i<?ne. coeffs i * vxe i) = coeffs 1 * vxe 1 + (\<Sum>i \<in> {..<?ne} - {1}. coeffs i * vxe i)"
                using sum.remove[OF hfin h1_in, of "\<lambda>i. coeffs i * vxe i"] by simp
              have s2: "(\<Sum>i \<in> {..<?ne} - {1}. coeffs i * vxe i) = coeffs (j+2) * vxe (j+2) + (\<Sum>i \<in> {..<?ne} - {1} - {j+2}. coeffs i * vxe i)"
                using sum.remove[of "{..<?ne} - {1}" "j+2" "\<lambda>i. coeffs i * vxe i"] hj2_in2 by simp
              have s3: "(\<Sum>i \<in> {..<?ne} - {1} - {j+2}. coeffs i * vxe i) = coeffs ?si * vxe ?si + (\<Sum>i \<in> {..<?ne} - {1} - {j+2} - {?si}. coeffs i * vxe i)"
                using sum.remove[of "{..<?ne} - {1} - {j+2}" ?si "\<lambda>i. coeffs i * vxe i"] hsi_in2 by simp
              have "({..<?ne} - {1} - {j+2} - {?si}) = ({..<?ne} - {1, j+2, ?si})" by auto
              from s1 s2 s3 this show ?thesis by simp
            qed
            also have "(\<Sum>i \<in> {..<?ne} - {1, j+2, ?si}. coeffs i * vxe i) = 0"
              unfolding coeffs_def by (rule sum.neutral) auto
            also have "coeffs 1 * vxe 1 + coeffs (j+2) * vxe (j+2) + coeffs ?si * vxe ?si + 0
                = (1-s-t) * vxe 1 + s * vxe (j+2) + t * vxe ?si"
              unfolding coeffs_def using hj2_ne1 hsi_ne_j2 hsi_ne1 by simp
            finally show ?thesis unfolding p_def by (by100 simp)
          qed
          have hy: "snd p = (\<Sum>i<?ne. coeffs i * vye i)"
          proof -
            have "(\<Sum>i<?ne. coeffs i * vye i) = coeffs 1 * vye 1 + coeffs (j+2) * vye (j+2) +
                coeffs ?si * vye ?si + (\<Sum>i \<in> {..<?ne} - {1, j+2, ?si}. coeffs i * vye i)"
            proof -
              have s1: "(\<Sum>i<?ne. coeffs i * vye i) = coeffs 1 * vye 1 + (\<Sum>i \<in> {..<?ne} - {1}. coeffs i * vye i)"
                using sum.remove[OF hfin h1_in, of "\<lambda>i. coeffs i * vye i"] by simp
              have s2: "(\<Sum>i \<in> {..<?ne} - {1}. coeffs i * vye i) = coeffs (j+2) * vye (j+2) + (\<Sum>i \<in> {..<?ne} - {1} - {j+2}. coeffs i * vye i)"
                using sum.remove[of "{..<?ne} - {1}" "j+2" "\<lambda>i. coeffs i * vye i"] hj2_in2 by simp
              have s3: "(\<Sum>i \<in> {..<?ne} - {1} - {j+2}. coeffs i * vye i) = coeffs ?si * vye ?si + (\<Sum>i \<in> {..<?ne} - {1} - {j+2} - {?si}. coeffs i * vye i)"
                using sum.remove[of "{..<?ne} - {1} - {j+2}" ?si "\<lambda>i. coeffs i * vye i"] hsi_in2 by simp
              have "({..<?ne} - {1} - {j+2} - {?si}) = ({..<?ne} - {1, j+2, ?si})" by auto
              from s1 s2 s3 this show ?thesis by simp
            qed
            also have "(\<Sum>i \<in> {..<?ne} - {1, j+2, ?si}. coeffs i * vye i) = 0"
              unfolding coeffs_def by (rule sum.neutral) auto
            also have "coeffs 1 * vye 1 + coeffs (j+2) * vye (j+2) + coeffs ?si * vye ?si + 0
                = (1-s-t) * vye 1 + s * vye (j+2) + t * vye ?si"
              unfolding coeffs_def using hj2_ne1 hsi_ne_j2 hsi_ne1 by simp
            finally show ?thesis unfolding p_def by (by100 simp)
          qed
          show ?thesis unfolding hC5_e using hnn hsum hx hy by (by5000 auto)
        qed
        \<comment> \<open>phi\\_fn(p) = q: p is in source sector j, so phi\\_fn uses sector j affine formula.\<close>
        have hphi_eq: "phi_fn p = q"
        proof (cases "s = 0 \<and> t = 0")
          case True
          \<comment> \<open>p = v\\_1, phi\\_fn(v\\_1) = centroid = q.\<close>
          hence "p = (vxe 1, vye 1)" unfolding p_def by simp
          hence "phi_fn p = (?cxw, ?cyw)" unfolding phi_fn_def by simp
          moreover from True hqx hqy have "fst q = ?cxw" "snd q = ?cyw" by auto
          ultimately show ?thesis by (cases q) simp
        next
          case False
          hence hp_ne_v1: "p \<noteq> (vxe 1, vye 1)"
          proof -
            assume hst_ne: "\<not>(s = 0 \<and> t = 0)"
            \<comment> \<open>p - v\\_1 = s*(v\\_{j+2}-v\\_1) + t*(v\\_{si}-v\\_1). If p = v\\_1, both terms = 0.
               Since det(v\\_{j+2}-v\\_1, v\\_{si}-v\\_1) > 0, the vectors are LI.
               So s*(v\\_{j+2}-v\\_1) + t*(v\\_{si}-v\\_1) = 0 implies s = 0 and t = 0.\<close>
            show ?thesis
            proof (rule ccontr)
              assume "\<not> p \<noteq> (vxe 1, vye 1)"
              hence hp_eq: "p = (vxe 1, vye 1)" by simp
              have hfst_p: "fst p = (1-s-t)*vxe 1 + s*vxe(j+2) + t*vxe ?si"
                unfolding p_def by simp
              have hsnd_p: "snd p = (1-s-t)*vye 1 + s*vye(j+2) + t*vye ?si"
                unfolding p_def by simp
              from hp_eq have "fst p = vxe 1" "snd p = vye 1" by auto
              have "vxe 1 = (1-s-t)*vxe 1 + s*vxe(j+2) + t*vxe ?si"
                using \<open>fst p = vxe 1\<close> hfst_p by simp
              hence "0 = s*(vxe(j+2) - vxe 1) + t*(vxe ?si - vxe 1)"
                by (by100 algebra)
              hence hdx0: "s*(vxe(j+2)-vxe 1) + t*(vxe ?si-vxe 1) = 0"
                by (by100 algebra)
              have "vye 1 = (1-s-t)*vye 1 + s*vye(j+2) + t*vye ?si"
                using \<open>snd p = vye 1\<close> hsnd_p by simp
              hence "0 = s*(vye(j+2) - vye 1) + t*(vye ?si - vye 1)"
                by (by100 algebra)
              hence hdy0: "s*(vye(j+2)-vye 1) + t*(vye ?si-vye 1) = 0"
                by (by100 algebra)
              let ?ex = "vxe(j+2)-vxe 1" and ?ey = "vye(j+2)-vye 1"
              let ?fx = "vxe ?si-vxe 1" and ?fy = "vye ?si-vye 1"
              let ?det = "?ex*?fy-?ey*?fx"
              have hdet_pos_j: "?det > 0" using hdet_pos[rule_format, OF hj] by simp
              \<comment> \<open>From hdx0: s*ex = -(t*fx). From hdy0: s*ey = -(t*fy).\<close>
              from hdx0 have hsx: "s*?ex = -(t*?fx)" by linarith
              from hdy0 have hsy: "s*?ey = -(t*?fy)" by linarith
              \<comment> \<open>s * det = s*ex*fy - s*ey*fx = -(t*fx)*fy - (-(t*fy))*fx = 0.\<close>
              have hsdet: "s*?det = (s*?ex)*?fy - (s*?ey)*?fx" by (by100 algebra)
              also have "\<dots> = (-(t*?fx))*?fy - (-(t*?fy))*?fx"
                using hsx hsy by simp
              also have "\<dots> = 0" by (by100 algebra)
              finally have "s * ?det = 0" .
              hence hs0: "s = 0" using hdet_pos_j by (by100 simp)
              from hdx0 hs0 have "t*?fx = 0" by simp
              from hdy0 hs0 have "t*?fy = 0" by simp
              \<comment> \<open>t = 0 since t*fx=0, t*fy=0, and (fx,fy) \\<noteq> (0,0).\<close>
              \<comment> \<open>Simpler: from t*fx=0 and t*fy=0, if fx\\<noteq>0 or fy\\<noteq>0 then t=0.
                 But det > 0 means (ex,ey) and (fx,fy) are not parallel.\<close>
              have "t = 0"
              proof (rule ccontr)
                assume "t \<noteq> 0"
                from \<open>t*?fx = 0\<close> \<open>t \<noteq> 0\<close> have "?fx = 0" by simp
                from \<open>t*?fy = 0\<close> \<open>t \<noteq> 0\<close> have "?fy = 0" by simp
                hence "?det = 0" using \<open>?fx = 0\<close> by (by100 simp)
                thus False using hdet_pos_j by linarith
              qed
              from \<open>s = 0\<close> \<open>t = 0\<close> show False using hst_ne by simp
            qed
          qed
          \<comment> \<open>Show p is in sector j.\<close>
          have hin_sector: "in_sector j p"
          proof -
            let ?ex = "vxe(j+2)-vxe 1" and ?ey = "vye(j+2)-vye 1"
            let ?fx = "vxe ?si-vxe 1" and ?fy = "vye ?si-vye 1"
            let ?det = "?ex*?fy-?ey*?fx"
            have hdet_pos_j: "?det > 0" using hdet_pos[rule_format, OF hj] by simp
            \<comment> \<open>dx = fst p - vxe 1 = s*ex + t*fx.\<close>
            have hdx: "fst p - vxe 1 = s*?ex + t*?fx"
            proof -
              have "fst p = (1-s-t)*vxe 1 + s*vxe(j+2) + t*vxe ?si" unfolding p_def by simp
              thus ?thesis by (by100 algebra)
            qed
            have hdy: "snd p - vye 1 = s*?ey + t*?fy"
            proof -
              have "snd p = (1-s-t)*vye 1 + s*vye(j+2) + t*vye ?si" unfolding p_def by simp
              thus ?thesis by (by100 algebra)
            qed
            \<comment> \<open>cross\\_v1(j+2, p) = t * det \\<ge> 0.\<close>
            have hcross_j2: "cross_v1 (j+2) p = t * ?det"
            proof -
              have "cross_v1 (j+2) p = ?ex * (snd p - vye 1) - ?ey * (fst p - vxe 1)"
                unfolding cross_v1_def by simp
              also have "\<dots> = ?ex * (s*?ey + t*?fy) - ?ey * (s*?ex + t*?fx)"
                using hdx hdy by simp
              also have "\<dots> = t * (?ex*?fy - ?ey*?fx)" by (by100 algebra)
              finally show ?thesis by simp
            qed
            have "cross_v1 (j+2) p \<ge> 0" using hcross_j2 ht hdet_pos_j
              by (by100 simp)
            \<comment> \<open>cross\\_v1(si, p) = -s * det \\<le> 0.\<close>
            moreover have hcross_si: "cross_v1 ?si p = -(s * ?det)"
            proof -
              have "cross_v1 ?si p = ?fx * (snd p - vye 1) - ?fy * (fst p - vxe 1)"
                unfolding cross_v1_def by simp
              also have "\<dots> = ?fx * (s*?ey + t*?fy) - ?fy * (s*?ex + t*?fx)"
                using hdx hdy by simp
              also have "\<dots> = -(s * (?ex*?fy - ?ey*?fx))" by (by100 algebra)
              finally show ?thesis by simp
            qed
            hence "cross_v1 ?si p \<le> 0" using hs hdet_pos_j
              by (by100 simp)
            ultimately show ?thesis unfolding in_sector_def by auto
          qed
          \<comment> \<open>Apply hphi\\_affine\\_on\\_sector to get phi\\_fn p in terms of Cramer formula.\<close>
          from hphi_affine_on_sector[rule_format, OF hj hp_in hin_sector]
          have hphi_val: "phi_fn (fst p, snd p) = (let ex = vxe(j+2)-vxe 1; ey = vye(j+2)-vye 1;
              fx = vxe ?si-vxe 1; fy = vye ?si-vye 1;
              det = ex*fy-ey*fx; dx = fst p-vxe 1; dy = snd p-vye 1;
              s' = (fy*dx-fx*dy)/det; t' = (ex*dy-ey*dx)/det
          in ((1-s'-t')*?cxw + s'*vxw j + t'*vxw(Suc j mod ?nw),
              (1-s'-t')*?cyw + s'*vyw j + t'*vyw(Suc j mod ?nw)))" .
          \<comment> \<open>The Cramer formula recovers s and t.\<close>
          let ?ex = "vxe(j+2)-vxe 1" and ?ey = "vye(j+2)-vye 1"
          let ?fx = "vxe ?si-vxe 1" and ?fy = "vye ?si-vye 1"
          let ?det = "?ex*?fy-?ey*?fx"
          have hdet_pos_j: "?det > 0" using hdet_pos[rule_format, OF hj] by simp
          have hdet_ne: "?det \<noteq> 0" using hdet_pos_j by linarith
          have hdx: "fst p - vxe 1 = s*?ex + t*?fx"
          proof -
            have "fst p = (1-s-t)*vxe 1 + s*vxe(j+2) + t*vxe ?si" unfolding p_def by simp
            thus ?thesis by (by100 algebra)
          qed
          have hdy: "snd p - vye 1 = s*?ey + t*?fy"
          proof -
            have "snd p = (1-s-t)*vye 1 + s*vye(j+2) + t*vye ?si" unfolding p_def by simp
            thus ?thesis by (by100 algebra)
          qed
          have hs_recover: "(?fy*(fst p-vxe 1)-?fx*(snd p-vye 1))/?det = s"
          proof -
            have "?fy*(fst p-vxe 1)-?fx*(snd p-vye 1) = ?fy*(s*?ex+t*?fx)-?fx*(s*?ey+t*?fy)"
              using hdx hdy by simp
            also have "\<dots> = s*(?ex*?fy-?ey*?fx)" by (by100 algebra)
            finally have heq_s: "?fy*(fst p-vxe 1)-?fx*(snd p-vye 1) = s * ?det" by simp
            hence "(?fy*(fst p-vxe 1)-?fx*(snd p-vye 1)) / ?det = s"
              using hdet_ne by (by100 simp)
            thus ?thesis .
          qed
          have ht_recover: "(?ex*(snd p-vye 1)-?ey*(fst p-vxe 1))/?det = t"
          proof -
            have "?ex*(snd p-vye 1)-?ey*(fst p-vxe 1) = ?ex*(s*?ey+t*?fy)-?ey*(s*?ex+t*?fx)"
              using hdx hdy by simp
            also have "\<dots> = t*(?ex*?fy-?ey*?fx)" by (by100 algebra)
            finally have heq_t: "?ex*(snd p-vye 1)-?ey*(fst p-vxe 1) = t * ?det" by simp
            hence "(?ex*(snd p-vye 1)-?ey*(fst p-vxe 1)) / ?det = t"
              using hdet_ne by (by100 simp)
            thus ?thesis .
          qed
          \<comment> \<open>Substitute back into the formula.\<close>
          \<comment> \<open>hphi\\_val gives phi\\_fn in terms of Cramer. hs/ht\\_recover show Cramer = s/t.\<close>
          have "phi_fn p = ((1-s-t)*?cxw + s*vxw j + t*vxw(Suc j mod ?nw),
              (1-s-t)*?cyw + s*vyw j + t*vyw(Suc j mod ?nw))"
          proof -
            \<comment> \<open>Expand hphi\\_val with Let\\_def.\<close>
            let ?s' = "(?fy*(fst p-vxe 1)-?fx*(snd p-vye 1))/?det"
            let ?t' = "(?ex*(snd p-vye 1)-?ey*(fst p-vxe 1))/?det"
            from hphi_val have hval: "phi_fn (fst p, snd p) =
                ((1-?s'-?t')*?cxw + ?s'*vxw j + ?t'*vxw(Suc j mod ?nw),
                 (1-?s'-?t')*?cyw + ?s'*vyw j + ?t'*vyw(Suc j mod ?nw))"
              unfolding Let_def by simp
            have "?s' = s" using hs_recover by simp
            moreover have "?t' = t" using ht_recover by simp
            ultimately have "phi_fn (fst p, snd p) =
                ((1-s-t)*?cxw + s*vxw j + t*vxw(Suc j mod ?nw),
                 (1-s-t)*?cyw + s*vyw j + t*vyw(Suc j mod ?nw))"
              using hval by simp
            thus ?thesis by simp
          qed
          moreover have "q = (fst q, snd q)" by simp
          ultimately show ?thesis using hqx hqy by simp
        qed
        from hp_in hphi_eq show "q \<in> phi_fn ` P_e" by (by100 blast)
      qed
      have prop4: "\<forall>t\<in>I_set. phi_fn (edge_pt_e 0 t) = phi_fn (edge_pt_e 1 (1-t))"
      proof (intro ballI)
        fix t assume ht: "t \<in> I_set"
        have h0: "phi_fn (edge_pt_e 0 t) = ((1-t)*vxw 0 + t*?cxw, (1-t)*vyw 0 + t*?cyw)"
          using hphi_on_spur0 ht by (by100 blast)
        have "1-t \<in> I_set" using ht unfolding top1_unit_interval_def by (by100 auto)
        hence h1: "phi_fn (edge_pt_e 1 (1-t)) = ((1-t)*vxw 0 + (1-(1-t))*?cxw,
            (1-t)*vyw 0 + (1-(1-t))*?cyw)"
          using hphi_on_spur1 by (by100 blast)
        show "phi_fn (edge_pt_e 0 t) = phi_fn (edge_pt_e 1 (1-t))"
          using h0 h1 by (by100 simp)
      qed
      have prop5: "phi_fn (edge_pt_e 0 0) = (vxw 0, vyw 0)"
      proof -
        have "0 \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        hence "phi_fn (edge_pt_e 0 0) = ((1-0)*vxw 0 + 0*?cxw, (1-0)*vyw 0 + 0*?cyw)"
          using hphi_on_spur0 by (by100 blast)
        thus ?thesis by (by100 simp)
      qed
      have prop6: "\<forall>t\<in>{0<..<(1::real)}.
          (\<forall>j<?nw. \<forall>s\<in>I_set. phi_fn (edge_pt_e 0 t) \<noteq> edge_pt_w j s)"
      proof (intro ballI allI impI)
        fix t :: real and j :: nat and s :: real
        assume ht: "t \<in> {0<..<(1::real)}" and hj: "j < ?nw" and hs: "s \<in> I_set"
        have ht_I: "t \<in> I_set" using ht unfolding top1_unit_interval_def by (by100 auto)
        have hval: "phi_fn (edge_pt_e 0 t) = ((1-t)*vxw 0 + t*?cxw, (1-t)*vyw 0 + t*?cyw)"
          using hphi_on_spur0 ht_I by (by100 blast)
        \<comment> \<open>The spur arc point is a strict convex combo of u\\_0 (boundary) and centroid (interior).
           For t > 0, this is in the interior of P\\_w, hence not on any edge.\<close>
        \<comment> \<open>The spur arc point ((1-t)*u\\_0 + t*c\\_w) is NOT on any w-edge.
           Uses the same C10 cross product argument as hcw\\_not\\_edge.
           The centroid lies strictly inside, and the convex combo with t > 0
           keeps the point off the boundary.\<close>
        have harc_not_edge: "((1-t)*vxw 0 + t*?cxw, (1-t)*vyw 0 + t*?cyw) \<noteq> edge_pt_w j s"
        proof -
          have ht_pos: "t > 0" using ht by (by100 simp)
          \<comment> \<open>Define the half-plane test for edge j:
             h(x,y) = (x-vxw j)*(vyw(Suc j mod nw)-vyw j) - (y-vyw j)*(vxw(Suc j mod nw)-vxw j).
             For interior points: h < 0 (from C11). On edge j: h = 0.\<close>
          define dxj where "dxj = vxw(Suc j mod ?nw) - vxw j"
          define dyj where "dyj = vyw(Suc j mod ?nw) - vyw j"
          define hf where "hf x y = (x - vxw j) * dyj - (y - vyw j) * dxj" for x y
          \<comment> \<open>h is linear: h((1-t)*p1 + t*p2) = (1-t)*h(p1) + t*h(p2).\<close>
          have hlinear: "\<forall>x1 y1 x2 y2 r. hf ((1-r)*x1 + r*x2) ((1-r)*y1 + r*y2) =
            (1-r)*hf x1 y1 + r*hf x2 y2"
            unfolding hf_def by (by100 algebra)
          \<comment> \<open>h(centroid) < 0: centroid is strictly on the interior side of edge j.\<close>
          have hf_centroid_neg: "hf ?cxw ?cyw < 0"
          proof -
            \<comment> \<open>If h(c\\_w) = 0, then centroid is on edge j line. Apply C10 argument.\<close>
            from hC10_w[rule_format, OF hj]
            have hcr: "(vxw j - ?cxw) * (vyw(Suc j mod ?nw) - ?cyw) -
                       (vyw j - ?cyw) * (vxw(Suc j mod ?nw) - ?cxw) > 0"
              by (by100 simp)
            \<comment> \<open>Expand: hcr = -(hf ?cxw ?cyw) + ?cxw*dyj - ?cyw*dxj - vxw j*dyj + vyw j*dxj
               Actually: (vxw j - ?cxw)*(vyw(Suc j)-?cyw) - (vyw j-?cyw)*(vxw(Suc j)-?cxw)
               = vxw j * vyw(Suc j) - vxw j * ?cyw - ?cxw * vyw(Suc j) + ?cxw*?cyw
                 - vyw j * vxw(Suc j) + vyw j * ?cxw + ?cyw * vxw(Suc j) - ?cyw*?cxw
               = [vxw j * dyj - vyw j * dxj] + [?cyw * dxj - ?cxw * dyj] + [vxw j * (-?cyw) + ?cxw * ?cyw + vyw j * ?cxw - ?cyw * ?cxw]...
               This is getting messy. Let me use a different approach.\<close>
            \<comment> \<open>Direct: assume hf(?cxw, ?cyw) \\<ge> 0 and derive contradiction.\<close>
            show ?thesis
            proof (rule ccontr)
              assume "\<not> (hf ?cxw ?cyw < 0)"
              hence hf_ge: "hf ?cxw ?cyw \<ge> 0" by (by100 simp)
              \<comment> \<open>hf(v\\_k) < 0 for k \\<noteq> j, k \\<noteq> Suc j (by C11).
                 hf(v\\_j) = 0, hf(v\\_{Suc j}) = 0.
                 hf(?cxw, ?cyw) = (1/nw) * \\<Sum> hf(v\\_k)
                 = (1/nw) * [0 + 0 + \\<Sum>\\_{k\\<noteq>j,Suc j} hf(v\\_k)] < 0.
                 Contradiction with hf \\<ge> 0.\<close>
              have hf_vj: "hf (vxw j) (vyw j) = 0" unfolding hf_def by (by100 algebra)
              have hf_vsj: "hf (vxw(Suc j mod ?nw)) (vyw(Suc j mod ?nw)) = 0"
                unfolding hf_def dxj_def dyj_def by (by100 algebra)
              have hf_sum: "hf ?cxw ?cyw = (1/real ?nw) * (\<Sum>k<?nw. hf (vxw k) (vyw k))"
              proof -
                \<comment> \<open>Expand hf at centroid.\<close>
                have "hf ?cxw ?cyw = (?cxw - vxw j) * dyj - (?cyw - vyw j) * dxj"
                  unfolding hf_def by (by100 simp)
                \<comment> \<open>centroid - v\\_j = (1/nw) * \\<Sum>(v\\_k - v\\_j).\<close>
                have hcx_diff: "?cxw - vxw j = (1/real ?nw) * (\<Sum>k<?nw. vxw k - vxw j)"
                proof -
                  have hnwr: "real ?nw > 0" using hnw_pos by (by100 simp)
                  have hnwcx: "real ?nw * ?cxw = (\<Sum>k<?nw. vxw k)" using hnwr by (by100 simp)
                  have "real ?nw * (?cxw - vxw j) = real ?nw * ?cxw - real ?nw * vxw j"
                    by (by100 algebra)
                  hence "real ?nw * (?cxw - vxw j) = (\<Sum>k<?nw. vxw k) - real ?nw * vxw j"
                    using hnwcx by (by100 linarith)
                  also have "\<dots> = (\<Sum>k<?nw. vxw k - vxw j)"
                    using sum_subtractf[of vxw "\<lambda>_. vxw j" "{..<?nw}"] by (by100 simp)
                  finally have hmul: "real ?nw * (?cxw - vxw j) = (\<Sum>k<?nw. vxw k - vxw j)" .
                  have "(?cxw - vxw j) * real ?nw = real ?nw * (?cxw - vxw j)"
                    by (by100 algebra)
                  also from hmul have "\<dots> = (\<Sum>k<?nw. vxw k - vxw j)" .
                  finally have "(?cxw - vxw j) * real ?nw = (\<Sum>k<?nw. vxw k - vxw j)" .
                  hence hdiv: "(?cxw - vxw j) = (\<Sum>k<?nw. vxw k - vxw j) / real ?nw"
                  proof -
                    assume hmul2: "(?cxw - vxw j) * real ?nw = (\<Sum>k<?nw. vxw k - vxw j)"
                    have "real ?nw \<noteq> (0::real)" using hnwr by (by100 linarith)
                    hence "(?cxw - vxw j) = (?cxw - vxw j) * real ?nw / real ?nw"
                      by (by100 simp)
                    also have "\<dots> = (\<Sum>k<?nw. vxw k - vxw j) / real ?nw"
                      using hmul2 by (by100 simp)
                    finally show ?thesis .
                  qed
                  thus ?thesis by (by100 simp)
                qed
                have hcy_diff: "?cyw - vyw j = (1/real ?nw) * (\<Sum>k<?nw. vyw k - vyw j)"
                proof -
                  have hnwr: "real ?nw > 0" using hnw_pos by (by100 simp)
                  have hnwcy: "real ?nw * ?cyw = (\<Sum>k<?nw. vyw k)" using hnwr by (by100 simp)
                  have "real ?nw * (?cyw - vyw j) = real ?nw * ?cyw - real ?nw * vyw j"
                    by (by100 algebra)
                  hence "real ?nw * (?cyw - vyw j) = (\<Sum>k<?nw. vyw k) - real ?nw * vyw j"
                    using hnwcy by (by100 linarith)
                  also have "\<dots> = (\<Sum>k<?nw. vyw k - vyw j)"
                    using sum_subtractf[of vyw "\<lambda>_. vyw j" "{..<?nw}"] by (by100 simp)
                  finally have hmulY: "real ?nw * (?cyw - vyw j) = (\<Sum>k<?nw. vyw k - vyw j)" .
                  have "(?cyw - vyw j) * real ?nw = real ?nw * (?cyw - vyw j)"
                    by (by100 algebra)
                  also from hmulY have "\<dots> = (\<Sum>k<?nw. vyw k - vyw j)" .
                  finally have "(?cyw - vyw j) * real ?nw = (\<Sum>k<?nw. vyw k - vyw j)" .
                  hence hdivY: "(?cyw - vyw j) = (\<Sum>k<?nw. vyw k - vyw j) / real ?nw"
                  proof -
                    assume hmul2Y: "(?cyw - vyw j) * real ?nw = (\<Sum>k<?nw. vyw k - vyw j)"
                    have "real ?nw \<noteq> (0::real)" using hnwr by (by100 linarith)
                    hence "(?cyw - vyw j) = (?cyw - vyw j) * real ?nw / real ?nw"
                      by (by100 simp)
                    also have "\<dots> = (\<Sum>k<?nw. vyw k - vyw j) / real ?nw"
                      using hmul2Y by (by100 simp)
                    finally show ?thesis .
                  qed
                  thus ?thesis using hdivY by (by100 simp)
                qed
                \<comment> \<open>Substitute and distribute.\<close>
                have "hf ?cxw ?cyw =
                  ((1/real ?nw) * (\<Sum>k<?nw. vxw k - vxw j)) * dyj -
                  ((1/real ?nw) * (\<Sum>k<?nw. vyw k - vyw j)) * dxj"
                  unfolding hf_def using hcx_diff hcy_diff by (by100 simp)
                also have "\<dots> = (1/real ?nw) * ((\<Sum>k<?nw. vxw k - vxw j) * dyj -
                  (\<Sum>k<?nw. vyw k - vyw j) * dxj)"
                  by (by100 algebra)
                also have "(\<Sum>k<?nw. vxw k - vxw j) * dyj - (\<Sum>k<?nw. vyw k - vyw j) * dxj
                  = (\<Sum>k<?nw. (vxw k - vxw j) * dyj - (vyw k - vyw j) * dxj)"
                proof -
                  have "(\<Sum>k<?nw. vxw k - vxw j) * dyj = (\<Sum>k<?nw. (vxw k - vxw j) * dyj)"
                    using sum_distrib_right[of "\<lambda>k. vxw k - vxw j" "{..<?nw}" dyj] by (by100 simp)
                  moreover have "(\<Sum>k<?nw. vyw k - vyw j) * dxj = (\<Sum>k<?nw. (vyw k - vyw j) * dxj)"
                    using sum_distrib_right[of "\<lambda>k. vyw k - vyw j" "{..<?nw}" dxj] by (by100 simp)
                  ultimately show ?thesis
                    using sum_subtractf[of "\<lambda>k. (vxw k - vxw j) * dyj" "\<lambda>k. (vyw k - vyw j) * dxj" "{..<?nw}"]
                    by (by100 simp)
                qed
                also have "\<dots> = (\<Sum>k<?nw. hf (vxw k) (vyw k))"
                  unfolding hf_def by (by100 simp)
                finally show ?thesis .
              qed
              have "\<exists>k<?nw. k \<noteq> j \<and> k \<noteq> Suc j mod ?nw"
              proof -
                have hnw3: "?nw \<ge> 3" using hlen by (by100 simp)
                have hsj_lt: "Suc j mod ?nw < ?nw" using hnw_pos by (by100 simp)
                have hj_sj: "j \<noteq> Suc j mod ?nw"
                proof (cases "Suc j < ?nw")
                  case True thus ?thesis by (by100 simp)
                next
                  case False hence "Suc j = ?nw" using hj by (by100 linarith)
                  hence "Suc j mod ?nw = 0" by (by100 simp)
                  moreover have "j > 0" using \<open>Suc j = ?nw\<close> hnw3 by (by100 linarith)
                  ultimately show ?thesis by (by100 simp)
                qed
                \<comment> \<open>j and Suc j mod nw are two distinct elements of {0,..,nw-1}.
                   Since nw \\<ge> 3, there's a third.\<close>
                have "card ({..<?nw} - {j, Suc j mod ?nw}) \<ge> ?nw - 2"
                proof -
                  have hsub: "{j, Suc j mod ?nw} \<subseteq> {..<?nw}" using hj hsj_lt by (by100 blast)
                  have "card ({..<?nw} - {j, Suc j mod ?nw}) = ?nw - card {j, Suc j mod ?nw}"
                    using card_Diff_subset[OF _ hsub] by (by100 simp)
                  also have "card {j, Suc j mod ?nw} = 2" using hj_sj by (by100 simp)
                  finally show ?thesis by (by100 linarith)
                qed
                hence "card ({..<?nw} - {j, Suc j mod ?nw}) \<ge> 1" using hnw3 by (by100 linarith)
                hence "{..<?nw} - {j, Suc j mod ?nw} \<noteq> {}" by (by100 fastforce)
                then obtain k where "k \<in> {..<?nw} - {j, Suc j mod ?nw}" by (by100 blast)
                thus ?thesis by (by100 blast)
              qed
              then obtain k0 where hk0: "k0 < ?nw" "k0 \<noteq> j" "k0 \<noteq> Suc j mod ?nw" by (by100 blast)
              from hC11_w[rule_format, OF hj hk0(1) hk0(2) hk0(3)]
              have "hf (vxw k0) (vyw k0) < 0" unfolding hf_def dxj_def dyj_def by (by100 simp)
              \<comment> \<open>All terms in the sum are \\<le> 0, at least one is < 0, so sum < 0.\<close>
              have hall_le: "\<forall>k<?nw. hf (vxw k) (vyw k) \<le> 0"
              proof (intro allI impI)
                fix k assume "k < ?nw"
                show "hf (vxw k) (vyw k) \<le> 0"
                proof (cases "k = j")
                  case True thus ?thesis using hf_vj by (by100 simp)
                next
                  case False
                  show ?thesis
                  proof (cases "k = Suc j mod ?nw")
                    case True thus ?thesis using hf_vsj by (by100 simp)
                  next
                    case False2: False
                    from hC11_w[rule_format, OF hj \<open>k < ?nw\<close> False False2]
                    show ?thesis unfolding hf_def dxj_def dyj_def by (by100 linarith)
                  qed
                qed
              qed
              have "(\<Sum>k<?nw. hf (vxw k) (vyw k)) < 0"
              proof -
                have "(\<Sum>k<?nw. hf (vxw k) (vyw k)) \<le> 0"
                  using hall_le by (intro sum_nonpos) (by100 simp)
                moreover have "hf (vxw k0) (vyw k0) < 0"
                  using hC11_w[rule_format, OF hj hk0(1) hk0(2) hk0(3)]
                  unfolding hf_def dxj_def dyj_def by (by100 linarith)
                \<comment> \<open>Sum = hf(k0) + rest. rest \\<le> 0 (all terms \\<le> 0). hf(k0) < 0. So sum < 0.\<close>
                have "(\<Sum>k<?nw. hf (vxw k) (vyw k)) = hf (vxw k0) (vyw k0)
                  + (\<Sum>k \<in> {..<?nw} - {k0}. hf (vxw k) (vyw k))"
                proof -
                  have "k0 \<in> {..<?nw}" using hk0(1) by (by100 simp)
                  have "(\<Sum>k<?nw. hf (vxw k) (vyw k))
                    = hf (vxw k0) (vyw k0) + (\<Sum>k \<in> {..<?nw} - {k0}. hf (vxw k) (vyw k))"
                    using sum.remove[of "{..<?nw}" k0 "\<lambda>k. hf (vxw k) (vyw k)"] \<open>k0 \<in> {..<?nw}\<close>
                    by (by100 simp)
                  thus ?thesis .
                qed
                moreover have "(\<Sum>k \<in> {..<?nw} - {k0}. hf (vxw k) (vyw k)) \<le> 0"
                proof (intro sum_nonpos)
                  fix k assume "k \<in> {..<?nw} - {k0}"
                  hence "k < ?nw" by (by100 simp)
                  thus "hf (vxw k) (vyw k) \<le> 0" using hall_le by (by100 blast)
                qed
                ultimately have "(\<Sum>k<?nw. hf (vxw k) (vyw k)) = hf (vxw k0) (vyw k0) + (\<Sum>k \<in> {..<?nw} - {k0}. hf (vxw k) (vyw k))"
                  and "(\<Sum>k \<in> {..<?nw} - {k0}. hf (vxw k) (vyw k)) \<le> 0" by (by100 simp)+
                hence "(\<Sum>k<?nw. hf (vxw k) (vyw k)) \<le> hf (vxw k0) (vyw k0)"
                  by (by100 linarith)
                thus ?thesis using \<open>hf (vxw k0) (vyw k0) < 0\<close> by (by100 linarith)
              qed
              hence "hf ?cxw ?cyw < 0"
              proof -
                from \<open>(\<Sum>k<?nw. hf (vxw k) (vyw k)) < 0\<close>
                have "(1/real ?nw) * (\<Sum>k<?nw. hf (vxw k) (vyw k)) < 0"
                proof -
                  have "real ?nw > 0" using hnw_pos by (by100 simp)
                  hence "1/real ?nw > 0" by (by100 simp)
                  thus ?thesis using \<open>(\<Sum>k<?nw. hf (vxw k) (vyw k)) < 0\<close>
                    by (rule mult_pos_neg)
                qed
                thus ?thesis using hf_sum by (by100 linarith)
              qed
              thus False using hf_ge by (by100 linarith)
            qed
          qed
          \<comment> \<open>h(u\\_0) \\<le> 0: vertex v\\_0 is in the polygon, so satisfies all half-plane conditions.\<close>
          have hf_u0_le: "hf (vxw 0) (vyw 0) \<le> 0"
          proof (cases "j = 0 \<or> Suc j mod ?nw = 0")
            case True \<comment> \<open>v\\_0 is an endpoint of edge j.\<close>
            hence "hf (vxw 0) (vyw 0) = 0"
            proof (elim disjE)
              assume hj0: "j = 0"
              show ?thesis unfolding hf_def dxj_def dyj_def hj0 by (by100 algebra)
            next
              assume hsj0: "Suc j mod ?nw = 0"
              have "dxj = vxw 0 - vxw j" unfolding dxj_def using hsj0 by (by100 simp)
              moreover have "dyj = vyw 0 - vyw j" unfolding dyj_def using hsj0 by (by100 simp)
              ultimately show ?thesis unfolding hf_def by (by100 algebra)
            qed
            thus ?thesis by (by100 simp)
          next
            case False
            hence "0 \<noteq> j" and "0 \<noteq> Suc j mod ?nw" by (by100 simp)+
            hence "(0::nat) < ?nw" using hnw_pos by (by100 simp)
            from hC11_w[rule_format, OF hj this \<open>0 \<noteq> j\<close> \<open>0 \<noteq> Suc j mod ?nw\<close>]
            have "hf (vxw 0) (vyw 0) < 0" unfolding hf_def dxj_def dyj_def by (by100 simp)
            thus ?thesis by (by100 simp)
          qed
          \<comment> \<open>h(edge point on edge j) = 0.\<close>
          have hf_edge_zero: "hf (fst (edge_pt_w j s)) (snd (edge_pt_w j s)) = 0"
          proof -
            have "fst (edge_pt_w j s) = (1-s)*vxw j + s*vxw(Suc j mod ?nw)"
              unfolding edge_pt_w_def by (by100 simp)
            moreover have "snd (edge_pt_w j s) = (1-s)*vyw j + s*vyw(Suc j mod ?nw)"
              unfolding edge_pt_w_def by (by100 simp)
            ultimately show ?thesis unfolding hf_def dxj_def dyj_def by (by100 algebra)
          qed
          \<comment> \<open>h(arc point) = (1-t)*h(u\\_0) + t*h(c\\_w) < 0.\<close>
          have hf_arc_neg: "hf ((1-t)*vxw 0 + t*?cxw) ((1-t)*vyw 0 + t*?cyw) < 0"
          proof -
            have "hf ((1-t)*vxw 0 + t*?cxw) ((1-t)*vyw 0 + t*?cyw) =
              (1-t)*hf (vxw 0) (vyw 0) + t*hf ?cxw ?cyw"
              unfolding hf_def dxj_def dyj_def by (by100 algebra)
            also have "\<dots> \<le> 0 + t*hf ?cxw ?cyw"
            proof -
              have h1t: "(1-t) \<ge> 0" using ht unfolding top1_unit_interval_def by (by100 auto)
              have "(1-t)*hf (vxw 0) (vyw 0) \<le> 0"
                using h1t hf_u0_le by (rule mult_nonneg_nonpos)
              thus ?thesis by (by100 linarith)
            qed
            also have "\<dots> < 0"
            proof -
              have "t * hf ?cxw ?cyw < 0"
                using ht_pos hf_centroid_neg by (rule mult_pos_neg)
              thus ?thesis by (by100 linarith)
            qed
            finally show ?thesis .
          qed
          \<comment> \<open>If arc = edge, then h(arc) = h(edge) = 0. But h(arc) < 0. Contradiction.\<close>
          show ?thesis
          proof
            assume heq2: "((1-t)*vxw 0 + t*?cxw, (1-t)*vyw 0 + t*?cyw) = edge_pt_w j s"
            hence "fst ((1-t)*vxw 0 + t*?cxw, (1-t)*vyw 0 + t*?cyw) = fst(edge_pt_w j s)
              \<and> snd ((1-t)*vxw 0 + t*?cxw, (1-t)*vyw 0 + t*?cyw) = snd(edge_pt_w j s)"
              by (by100 simp)
            hence "hf ((1-t)*vxw 0 + t*?cxw) ((1-t)*vyw 0 + t*?cyw) =
              hf (fst(edge_pt_w j s)) (snd(edge_pt_w j s))" unfolding hf_def by (by100 simp)
            hence "hf ((1-t)*vxw 0 + t*?cxw) ((1-t)*vyw 0 + t*?cyw) = 0"
              using hf_edge_zero by (by100 simp)
            thus False using hf_arc_neg by (by100 linarith)
          qed
        qed
        show "phi_fn (edge_pt_e 0 t) \<noteq> edge_pt_w j s"
          using harc_not_edge hval by (by100 simp)
      qed
      have prop7: "\<forall>j<?nw. \<forall>s\<in>I_set. phi_fn (edge_pt_e 0 1) \<noteq> edge_pt_w j s"
      proof (intro allI ballI impI)
        fix j :: nat and s :: real
        assume hj: "j < ?nw" and hs: "s \<in> I_set"
        have "1 \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        hence "phi_fn (edge_pt_e 0 1) = ((1-1)*vxw 0 + 1*?cxw, (1-1)*vyw 0 + 1*?cyw)"
          using hphi_on_spur0 by (by100 blast)
        hence hval: "phi_fn (edge_pt_e 0 1) = (?cxw, ?cyw)" by (by100 simp)
        have "(?cxw, ?cyw) \<noteq> edge_pt_w j s" using hcw_not_edge hj hs by (by100 blast)
        thus "phi_fn (edge_pt_e 0 1) \<noteq> edge_pt_w j s" using hval by (by100 simp)
      qed
      have prop8: "\<forall>t\<in>I_set. \<forall>s\<in>I_set. phi_fn (edge_pt_e 0 t) = phi_fn (edge_pt_e 0 s) \<longrightarrow> t = s"
      proof (intro ballI impI)
        fix t s :: real assume ht: "t \<in> I_set" and hs: "s \<in> I_set"
          and heq: "phi_fn (edge_pt_e 0 t) = phi_fn (edge_pt_e 0 s)"
        have h1: "phi_fn (edge_pt_e 0 t) = ((1-t)*vxw 0 + t*?cxw, (1-t)*vyw 0 + t*?cyw)"
          using hphi_on_spur0 ht by (by100 blast)
        have h2: "phi_fn (edge_pt_e 0 s) = ((1-s)*vxw 0 + s*?cxw, (1-s)*vyw 0 + s*?cyw)"
          using hphi_on_spur0 hs by (by100 blast)
        from heq h1 h2 have hpair_eq: "((1-t)*vxw 0 + t*?cxw, (1-t)*vyw 0 + t*?cyw) =
          ((1-s)*vxw 0 + s*?cxw, (1-s)*vyw 0 + s*?cyw)" by (by100 simp)
        hence hx_eq: "(1-t)*vxw 0 + t*?cxw = (1-s)*vxw 0 + s*?cxw" by (by100 simp)
        hence "(t-s)*?cxw = (t-s)*vxw 0" by (by100 algebra)
        hence hx_diff: "(t-s)*(?cxw - vxw 0) = 0" by (by100 algebra)
        from hpair_eq have hy_eq: "(1-t)*vyw 0 + t*?cyw = (1-s)*vyw 0 + s*?cyw" by (by100 simp)
        hence "(t-s)*?cyw = (t-s)*vyw 0" by (by100 algebra)
        hence hy_diff: "(t-s)*(?cyw - vyw 0) = 0" by (by100 algebra)
        have "(t-s) = 0"
        proof (rule ccontr)
          assume "t - s \<noteq> 0"
          from hx_diff this have "?cxw - vxw 0 = 0" by (by100 algebra)
          hence "?cxw = vxw 0" by (by100 simp)
          from hy_diff \<open>t - s \<noteq> 0\<close> have "?cyw - vyw 0 = 0" by (by100 algebra)
          hence "?cyw = vyw 0" by (by100 simp)
          hence "(?cxw, ?cyw) = (vxw 0, vyw 0)" using \<open>?cxw = vxw 0\<close> by (by100 simp)
          thus False using hcw_neq_u0 by (by100 simp)
        qed
        thus "t = s" by (by100 simp)
      qed
      have prop9: "\<forall>k<?nw. \<forall>t\<in>I_set. phi_fn (edge_pt_e (k+2) t) = edge_pt_w k t"
        using hphi_on_nonspur by (by100 blast)
      \<comment> \<open>NOTE: hinterior\\_strict removed. Direct sector arguments used in prop10-12 instead.
         The key insight: for interior p, the centroid weight (1-s-t) > 0 because
         s+t=1 would put p on edge jp+2 of P\\_e, contradicting interior.\<close>
      have prop10: "\<forall>p\<in>P_e. \<forall>p'\<in>P_e.
          (\<forall>i<?ne. \<forall>t\<in>I_set. p \<noteq> edge_pt_e i t) \<longrightarrow>
          (\<forall>i<?ne. \<forall>t\<in>I_set. p' \<noteq> edge_pt_e i t) \<longrightarrow>
          phi_fn p = phi_fn p' \<longrightarrow> p = p'"
      proof (intro ballI impI)
        fix p p' assume hp: "p \<in> P_e" and hp': "p' \<in> P_e"
            and hint_p: "\<forall>i<?ne. \<forall>t\<in>I_set. p \<noteq> edge_pt_e i t"
            and hint_p': "\<forall>i<?ne. \<forall>t\<in>I_set. p' \<noteq> edge_pt_e i t"
            and heq: "phi_fn p = phi_fn p'"
        \<comment> \<open>p is in strict sector j, p' is in strict sector j'.
           If j = j': phi\\_fn is affine injective on sector j (det > 0).
           If j \\<noteq> j': phi\\_fn(p) is in strict interior of target sector j,
           phi\\_fn(p') is in strict interior of target sector j', and these are disjoint.\<close>
        \<comment> \<open>p is not v\\_1 (v\\_1 = edge\\_pt\\_e 1 0), so p is in some sector.\<close>
        have h1_lt_ne: "1 < ?ne" using hlen_ext by linarith
        have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        have hedge1: "edge_pt_e 1 0 = (vxe 1, vye 1)" unfolding edge_pt_e_def by (by100 simp)
        have hp_ne_v1: "p \<noteq> (vxe 1, vye 1)"
        proof
          assume "p = (vxe 1, vye 1)"
          hence "p = edge_pt_e 1 0" using hedge1 by simp
          with hint_p[rule_format, OF h1_lt_ne h0_I] show False by simp
        qed
        from hfan_cover[rule_format, OF hp] hp_ne_v1
        obtain jp where hjp: "jp < ?nw" and hin_p: "in_sector jp p" by blast
        have hp'_ne_v1: "p' \<noteq> (vxe 1, vye 1)"
        proof
          assume "p' = (vxe 1, vye 1)"
          hence "p' = edge_pt_e 1 0" using hedge1 by simp
          with hint_p'[rule_format, OF h1_lt_ne h0_I] show False by simp
        qed
        from hfan_cover[rule_format, OF hp'] hp'_ne_v1
        obtain jp' where hjp': "jp' < ?nw" and hin_p': "in_sector jp' p'" by blast
        \<comment> \<open>DIRECT PROOF (bypassing fan\\_affine\\_interior\\_injective):
           Same sector: Cramer uniqueness. Different sector: centroid-cone disjointness.\<close>
        \<comment> \<open>Extract Cramer coords for p in sector jp (at outer scope to avoid define issues).\<close>
        define sp_v where "sp_v = (let fy = vye(Suc(jp+2) mod ?ne)-vye 1; fx = vxe(Suc(jp+2) mod ?ne)-vxe 1;
            det = (vxe(jp+2)-vxe 1)*fy-(vye(jp+2)-vye 1)*fx; dx = fst p-vxe 1; dy = snd p-vye 1
        in (fy*dx-fx*dy)/det)"
        define tp_v where "tp_v = (let ex = vxe(jp+2)-vxe 1; ey = vye(jp+2)-vye 1;
            fx = vxe(Suc(jp+2) mod ?ne)-vxe 1; fy = vye(Suc(jp+2) mod ?ne)-vye 1;
            det = ex*fy-ey*fx; dx = fst p-vxe 1; dy = snd p-vye 1
        in (ex*dy-ey*dx)/det)"
        have hdet_v_pos: "(vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-
            (vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1) > 0"
          using hdet_pos[rule_format, OF hjp] by (by100 simp)
        have hphi_x_v: "fst (phi_fn p) = (1-sp_v-tp_v)*?cxw + sp_v*vxw jp + tp_v*vxw(Suc jp mod ?nw)"
        proof -
          from hphi_affine_on_sector[rule_format, OF hjp hp hin_p]
          show ?thesis unfolding Let_def sp_v_def tp_v_def by (by100 simp)
        qed
        have hphi_y_v: "snd (phi_fn p) = (1-sp_v-tp_v)*?cyw + sp_v*vyw jp + tp_v*vyw(Suc jp mod ?nw)"
        proof -
          from hphi_affine_on_sector[rule_format, OF hjp hp hin_p]
          show ?thesis unfolding Let_def sp_v_def tp_v_def by (by100 simp)
        qed
        have hsp_v_ge: "sp_v \<ge> 0"
        proof -
          from hin_p have "cross_v1 (Suc(jp+2) mod ?ne) p \<le> 0" unfolding in_sector_def by (by100 auto)
          have "sp_v * ((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1))
            = (vye(Suc(jp+2) mod ?ne)-vye 1)*(fst p-vxe 1)-(vxe(Suc(jp+2) mod ?ne)-vxe 1)*(snd p-vye 1)"
            unfolding sp_v_def Let_def using hdet_v_pos by (by100 simp)
          also have "\<dots> = -(cross_v1 (Suc(jp+2) mod ?ne) p)"
            unfolding cross_v1_def by (by100 algebra)
          finally have "sp_v * ((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1)) \<ge> 0"
            using \<open>cross_v1 _ p \<le> 0\<close> by linarith
          thus ?thesis using hdet_v_pos by (metis linorder_not_le mult_neg_pos)
        qed
        have htp_v_ge: "tp_v \<ge> 0"
        proof -
          from hin_p have "cross_v1 (jp+2) p \<ge> 0" unfolding in_sector_def by (by100 auto)
          have "tp_v * ((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1))
            = (vxe(jp+2)-vxe 1)*(snd p-vye 1)-(vye(jp+2)-vye 1)*(fst p-vxe 1)"
            unfolding tp_v_def Let_def using hdet_v_pos by (by100 simp)
          also have "\<dots> = cross_v1 (jp+2) p"
            unfolding cross_v1_def by (by100 simp)
          finally have "tp_v * ((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1)) \<ge> 0"
            using \<open>cross_v1 _ p \<ge> 0\<close> by linarith
          thus ?thesis using hdet_v_pos by (metis linorder_not_le mult_neg_pos)
        qed
        have habg_v: "(1-sp_v-tp_v) + sp_v + tp_v = 1" by linarith
        have hC10_jp_v: "(vxw jp-?cxw)*(vyw(Suc jp mod ?nw)-?cyw)-(vyw jp-?cyw)*(vxw(Suc jp mod ?nw)-?cxw) > 0"
        proof -
          from hC10_w[rule_format, OF hjp] show ?thesis by (by100 simp)
        qed
        from centroid_cone_cross_nonneg[OF hsp_v_ge htp_v_ge habg_v hphi_x_v hphi_y_v hC10_jp_v]
        have hcross_jp_ge: "(vxw jp-?cxw)*(snd (phi_fn p)-?cyw)-(vyw jp-?cyw)*(fst (phi_fn p)-?cxw) \<ge> 0"
          and hcross_jp1_ge: "(fst (phi_fn p)-?cxw)*(vyw(Suc jp mod ?nw)-?cyw)-(snd (phi_fn p)-?cyw)*(vxw(Suc jp mod ?nw)-?cxw) \<ge> 0"
          by auto
        \<comment> \<open>For jp=jp': same sector Cramer uniqueness. For jp\\<noteq>jp': cross product mismatch.\<close>
        show "p = p'"
        proof (cases "jp = jp'")
          case True
          \<comment> \<open>Same sector: from phi(p)=phi(p') with same affine map, det>0 gives p=p'.\<close>
          \<comment> \<open>Same sector: from hphi\\_affine + jp=jp', the target-side coords match.
             Then triangle\\_coords\\_injective + cramer\\_injective give p=p'.\<close>
          have hC10_ne: "(vxw jp-?cxw)*(vyw(Suc jp mod ?nw)-?cyw)-(vyw jp-?cyw)*(vxw(Suc jp mod ?nw)-?cxw) \<noteq> 0"
            using hC10_jp_v by linarith
          have hdet_ne: "(vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-
              (vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1) \<noteq> 0"
            using hdet_v_pos by linarith
          \<comment> \<open>phi(p') also in sector jp (since jp=jp').\<close>
          from hphi_affine_on_sector[rule_format, OF hjp' hp' hin_p']
          have hphi_p': "phi_fn (fst p', snd p') = (let ex = vxe(jp'+2)-vxe 1; ey = vye(jp'+2)-vye 1;
              fx = vxe(Suc(jp'+2) mod ?ne)-vxe 1; fy = vye(Suc(jp'+2) mod ?ne)-vye 1;
              det = ex*fy-ey*fx; dx = fst p'-vxe 1; dy = snd p'-vye 1;
              s' = (fy*dx-fx*dy)/det; t' = (ex*dy-ey*dx)/det
          in ((1-s'-t')*?cxw + s'*vxw jp' + t'*vxw(Suc jp' mod ?nw),
              (1-s'-t')*?cyw + s'*vyw jp' + t'*vyw(Suc jp' mod ?nw)))" .
          \<comment> \<open>With jp=jp': both phi formulas use the same sector.\<close>
          define sp_v' where "sp_v' = (let fy = vye(Suc(jp+2) mod ?ne)-vye 1; fx = vxe(Suc(jp+2) mod ?ne)-vxe 1;
              det = (vxe(jp+2)-vxe 1)*fy-(vye(jp+2)-vye 1)*fx; dx = fst p'-vxe 1; dy = snd p'-vye 1
          in (fy*dx-fx*dy)/det)"
          define tp_v' where "tp_v' = (let ex = vxe(jp+2)-vxe 1; ey = vye(jp+2)-vye 1;
              fx = vxe(Suc(jp+2) mod ?ne)-vxe 1; fy = vye(Suc(jp+2) mod ?ne)-vye 1;
              det = ex*fy-ey*fx; dx = fst p'-vxe 1; dy = snd p'-vye 1
          in (ex*dy-ey*dx)/det)"
          have hphi_x_v': "fst (phi_fn p') = (1-sp_v'-tp_v')*?cxw + sp_v'*vxw jp + tp_v'*vxw(Suc jp mod ?nw)"
            using hphi_p' True unfolding Let_def sp_v'_def tp_v'_def by (by100 simp)
          have hphi_y_v': "snd (phi_fn p') = (1-sp_v'-tp_v')*?cyw + sp_v'*vyw jp + tp_v'*vyw(Suc jp mod ?nw)"
            using hphi_p' True unfolding Let_def sp_v'_def tp_v'_def by (by100 simp)
          \<comment> \<open>phi(p)=phi(p'): target coords match.\<close>
          from heq have "fst (phi_fn p) = fst (phi_fn p')" "snd (phi_fn p) = snd (phi_fn p')" by auto
          hence hx_eq: "(1-sp_v-tp_v)*?cxw + sp_v*vxw jp + tp_v*vxw(Suc jp mod ?nw) =
              (1-sp_v'-tp_v')*?cxw + sp_v'*vxw jp + tp_v'*vxw(Suc jp mod ?nw)"
            and hy_eq: "(1-sp_v-tp_v)*?cyw + sp_v*vyw jp + tp_v*vyw(Suc jp mod ?nw) =
              (1-sp_v'-tp_v')*?cyw + sp_v'*vyw jp + tp_v'*vyw(Suc jp mod ?nw)"
            using hphi_x_v hphi_y_v hphi_x_v' hphi_y_v' by auto
          \<comment> \<open>triangle\\_coords\\_injective: det(target) \\<noteq> 0 implies sp=sp' and tp=tp'.\<close>
          from triangle_coords_injective[OF hC10_ne hx_eq hy_eq]
          have "sp_v = sp_v'" "tp_v = tp_v'" by auto
          \<comment> \<open>cramer\\_injective: det(source) \\<noteq> 0 and sp=sp', tp=tp' implies dx=dx', dy=dy'.\<close>
          \<comment> \<open>From sp=sp' and tp=tp': the source Cramer systems match.\<close>
          \<comment> \<open>From sp=sp' and tp=tp': unfold Let and apply cramer\\_injective.\<close>
          define ex_s where "ex_s = vxe(jp+2)-vxe 1"
          define ey_s where "ey_s = vye(jp+2)-vye 1"
          define fx_s where "fx_s = vxe(Suc(jp+2) mod ?ne)-vxe 1"
          define fy_s where "fy_s = vye(Suc(jp+2) mod ?ne)-vye 1"
          have hdet_s_ne: "ex_s*fy_s - ey_s*fx_s \<noteq> 0"
            using hdet_v_pos unfolding ex_s_def ey_s_def fx_s_def fy_s_def by linarith
          have hsp_cramer: "(fy_s*(fst p-vxe 1)-fx_s*(snd p-vye 1))/(ex_s*fy_s-ey_s*fx_s) =
              (fy_s*(fst p'-vxe 1)-fx_s*(snd p'-vye 1))/(ex_s*fy_s-ey_s*fx_s)"
            using \<open>sp_v = sp_v'\<close> unfolding sp_v_def sp_v'_def Let_def
              ex_s_def ey_s_def fx_s_def fy_s_def by (by100 simp)
          have htp_cramer: "(ex_s*(snd p-vye 1)-ey_s*(fst p-vxe 1))/(ex_s*fy_s-ey_s*fx_s) =
              (ex_s*(snd p'-vye 1)-ey_s*(fst p'-vxe 1))/(ex_s*fy_s-ey_s*fx_s)"
            using \<open>tp_v = tp_v'\<close> unfolding tp_v_def tp_v'_def Let_def
              ex_s_def ey_s_def fx_s_def fy_s_def by (by100 simp)
          from cramer_injective[OF hdet_s_ne hsp_cramer htp_cramer]
          have "fst p - vxe 1 = fst p' - vxe 1 \<and> snd p - vye 1 = snd p' - vye 1" .
          hence "fst p = fst p'" "snd p = snd p'" by auto
          thus ?thesis by (cases p, cases p') (by100 simp)
        next
          case False
          \<comment> \<open>Different sector: centroid-cone cross products from sector jp hold for phi(p).
             Since phi(p)=phi(p'), they also hold for phi(p'). But from sector jp',
             the cross products should have OPPOSITE signs for non-adjacent sectors.\<close>
          \<comment> \<open>Key: cross(u\\_{jp+1}-cw, phi(p)-cw) = -sp\\_v*C10(jp) \\<le> 0 from sector jp.
             For jp' \\<noteq> jp: if jp' uses the same direction u\\_{jp+1}, we get incompatibility.\<close>
          \<comment> \<open>Adjacent case (jp' = Suc jp mod nw or jp' = (jp-1) mod nw): boundary analysis.\<close>
          \<comment> \<open>Non-adjacent: cross product of u\\_{jp'} with phi(p) from C11 perspective.\<close>
          \<comment> \<open>Step 1: Compute cross(u\\_{jp+1}-cw, phi(p)-cw) = -sp\\_v * C10(jp) \\<le> 0.\<close>
          have hcross_neg1: "(vxw(Suc jp mod ?nw)-?cxw)*(snd (phi_fn p)-?cyw)-
              (vyw(Suc jp mod ?nw)-?cyw)*(fst (phi_fn p)-?cxw) =
              -(sp_v * ((vxw jp-?cxw)*(vyw(Suc jp mod ?nw)-?cyw)-(vyw jp-?cyw)*(vxw(Suc jp mod ?nw)-?cxw)))"
          proof -
            have "fst (phi_fn p) - ?cxw = sp_v*(vxw jp-?cxw) + tp_v*(vxw(Suc jp mod ?nw)-?cxw)"
              using hphi_x_v habg_v by (by100 algebra)
            have "snd (phi_fn p) - ?cyw = sp_v*(vyw jp-?cyw) + tp_v*(vyw(Suc jp mod ?nw)-?cyw)"
              using hphi_y_v habg_v by (by100 algebra)
            show ?thesis using \<open>fst _ - _ = _\<close> \<open>snd _ - _ = _\<close> by (by100 algebra)
          qed
          hence hcross_jp1_le: "(vxw(Suc jp mod ?nw)-?cxw)*(snd (phi_fn p)-?cyw)-
              (vyw(Suc jp mod ?nw)-?cyw)*(fst (phi_fn p)-?cxw) \<le> 0"
            using hsp_v_ge hC10_jp_v by (by100 auto)
          \<comment> \<open>Similarly: cross(phi(p)-cw, u\\_jp-cw) = -tp\\_v * C10(jp) \\<le> 0.\<close>
          have hcross_neg2: "(fst (phi_fn p)-?cxw)*(vyw jp-?cyw)-
              (snd (phi_fn p)-?cyw)*(vxw jp-?cxw) =
              -(tp_v * ((vxw jp-?cxw)*(vyw(Suc jp mod ?nw)-?cyw)-(vyw jp-?cyw)*(vxw(Suc jp mod ?nw)-?cxw)))"
          proof -
            have "fst (phi_fn p) - ?cxw = sp_v*(vxw jp-?cxw) + tp_v*(vxw(Suc jp mod ?nw)-?cxw)"
              using hphi_x_v habg_v by (by100 algebra)
            have "snd (phi_fn p) - ?cyw = sp_v*(vyw jp-?cyw) + tp_v*(vyw(Suc jp mod ?nw)-?cyw)"
              using hphi_y_v habg_v by (by100 algebra)
            show ?thesis using \<open>fst _ - _ = _\<close> \<open>snd _ - _ = _\<close> by (by100 algebra)
          qed
          hence hcross_jp_le: "(fst (phi_fn p)-?cxw)*(vyw jp-?cyw)-
              (snd (phi_fn p)-?cyw)*(vxw jp-?cxw) \<le> 0"
            using htp_v_ge hC10_jp_v by (by100 auto)
          \<comment> \<open>Now: phi(p) = phi(p'). Similar Cramer analysis for p' in sector jp'.
             Extract cross products from sector jp' perspective.\<close>
          \<comment> \<open>For the contradiction: phi(p)=phi(p') must be in BOTH cones jp and jp'.
             From cone jp: cross(u\\_{jp+1}-cw, q-cw) \\<le> 0.
             From cone jp': cross(u\\_{jp'}-cw, q-cw) \\<ge> 0.
             For jp' = Suc jp mod nw: u\\_{jp'} = u\\_{jp+1}. Then cross(u\\_{jp+1}-cw,q-cw) both \\<le>0 and \\<ge>0.
             So = 0, which means sp\\_v = 0. Then diagonal injectivity gives p = p'.
             For non-adjacent jp': use C11 to show incompatibility.\<close>
          \<comment> \<open>Extract Cramer coords for p' in sector jp'.\<close>
          define sp_v' where "sp_v' = (let fy = vye(Suc(jp'+2) mod ?ne)-vye 1; fx = vxe(Suc(jp'+2) mod ?ne)-vxe 1;
              det = (vxe(jp'+2)-vxe 1)*fy-(vye(jp'+2)-vye 1)*fx; dx = fst p'-vxe 1; dy = snd p'-vye 1
          in (fy*dx-fx*dy)/det)"
          define tp_v' where "tp_v' = (let ex = vxe(jp'+2)-vxe 1; ey = vye(jp'+2)-vye 1;
              fx = vxe(Suc(jp'+2) mod ?ne)-vxe 1; fy = vye(Suc(jp'+2) mod ?ne)-vye 1;
              det = ex*fy-ey*fx; dx = fst p'-vxe 1; dy = snd p'-vye 1
          in (ex*dy-ey*dx)/det)"
          have hdet_v'_pos: "(vxe(jp'+2)-vxe 1)*(vye(Suc(jp'+2) mod ?ne)-vye 1)-
              (vye(jp'+2)-vye 1)*(vxe(Suc(jp'+2) mod ?ne)-vxe 1) > 0"
            using hdet_pos[rule_format, OF hjp'] by (by100 simp)
          have hphi_x_v': "fst (phi_fn p') = (1-sp_v'-tp_v')*?cxw + sp_v'*vxw jp' + tp_v'*vxw(Suc jp' mod ?nw)"
            using hphi_affine_on_sector[rule_format, OF hjp' hp' hin_p']
            unfolding Let_def sp_v'_def tp_v'_def by (by100 simp)
          have hphi_y_v': "snd (phi_fn p') = (1-sp_v'-tp_v')*?cyw + sp_v'*vyw jp' + tp_v'*vyw(Suc jp' mod ?nw)"
            using hphi_affine_on_sector[rule_format, OF hjp' hp' hin_p']
            unfolding Let_def sp_v'_def tp_v'_def by (by100 simp)
          have hsp_v'_ge: "sp_v' \<ge> 0"
          proof -
            from hin_p' have "cross_v1 (Suc(jp'+2) mod ?ne) p' \<le> 0" unfolding in_sector_def by (by100 auto)
            have "sp_v' * ((vxe(jp'+2)-vxe 1)*(vye(Suc(jp'+2) mod ?ne)-vye 1)-(vye(jp'+2)-vye 1)*(vxe(Suc(jp'+2) mod ?ne)-vxe 1))
              = (vye(Suc(jp'+2) mod ?ne)-vye 1)*(fst p'-vxe 1)-(vxe(Suc(jp'+2) mod ?ne)-vxe 1)*(snd p'-vye 1)"
              unfolding sp_v'_def Let_def using hdet_v'_pos by (by100 simp)
            also have "\<dots> = -(cross_v1 (Suc(jp'+2) mod ?ne) p')"
              unfolding cross_v1_def by (by100 algebra)
            finally have "sp_v' * ((vxe(jp'+2)-vxe 1)*(vye(Suc(jp'+2) mod ?ne)-vye 1)-(vye(jp'+2)-vye 1)*(vxe(Suc(jp'+2) mod ?ne)-vxe 1)) \<ge> 0"
              using \<open>cross_v1 _ p' \<le> 0\<close> by linarith
            thus ?thesis using hdet_v'_pos by (metis linorder_not_le mult_neg_pos)
          qed
          have htp_v'_ge: "tp_v' \<ge> 0"
          proof -
            from hin_p' have "cross_v1 (jp'+2) p' \<ge> 0" unfolding in_sector_def by (by100 auto)
            have "tp_v' * ((vxe(jp'+2)-vxe 1)*(vye(Suc(jp'+2) mod ?ne)-vye 1)-(vye(jp'+2)-vye 1)*(vxe(Suc(jp'+2) mod ?ne)-vxe 1))
              = (vxe(jp'+2)-vxe 1)*(snd p'-vye 1)-(vye(jp'+2)-vye 1)*(fst p'-vxe 1)"
              unfolding tp_v'_def Let_def using hdet_v'_pos by (by100 simp)
            also have "\<dots> = cross_v1 (jp'+2) p'"
              unfolding cross_v1_def by (by100 simp)
            finally have "tp_v' * ((vxe(jp'+2)-vxe 1)*(vye(Suc(jp'+2) mod ?ne)-vye 1)-(vye(jp'+2)-vye 1)*(vxe(Suc(jp'+2) mod ?ne)-vxe 1)) \<ge> 0"
              using \<open>cross_v1 _ p' \<ge> 0\<close> by linarith
            thus ?thesis using hdet_v'_pos by (metis linorder_not_le mult_neg_pos)
          qed
          have habg_v': "(1-sp_v'-tp_v') + sp_v' + tp_v' = 1" by linarith
          have hC10_jp'_v: "(vxw jp'-?cxw)*(vyw(Suc jp' mod ?nw)-?cyw)-(vyw jp'-?cyw)*(vxw(Suc jp' mod ?nw)-?cxw) > 0"
          proof -
            from hC10_w[rule_format, OF hjp'] show ?thesis by (by100 simp)
          qed
          \<comment> \<open>Cross products from cone jp' (using phi(p')=phi(p)).\<close>
          from centroid_cone_cross_nonneg[OF hsp_v'_ge htp_v'_ge habg_v' hphi_x_v' hphi_y_v' hC10_jp'_v]
          have hcross_jp'_ge: "(vxw jp'-?cxw)*(snd (phi_fn p')-?cyw)-(vyw jp'-?cyw)*(fst (phi_fn p')-?cxw) \<ge> 0"
            and hcross_jp'1_ge: "(fst (phi_fn p')-?cxw)*(vyw(Suc jp' mod ?nw)-?cyw)-(snd (phi_fn p')-?cyw)*(vxw(Suc jp' mod ?nw)-?cxw) \<ge> 0"
            by auto
          \<comment> \<open>Since phi(p)=phi(p'): the cross products apply to the SAME point.\<close>
          from heq have hfst_eq: "fst (phi_fn p) = fst (phi_fn p')" and hsnd_eq: "snd (phi_fn p) = snd (phi_fn p')"
            by auto
          hence hcross_jp'_from_p: "(vxw jp'-?cxw)*(snd (phi_fn p)-?cyw)-(vyw jp'-?cyw)*(fst (phi_fn p)-?cxw) \<ge> 0"
            using hcross_jp'_ge by (by100 simp)
          hence hcross_jp'1_from_p: "(fst (phi_fn p)-?cxw)*(vyw(Suc jp' mod ?nw)-?cyw)-(snd (phi_fn p)-?cyw)*(vxw(Suc jp' mod ?nw)-?cxw) \<ge> 0"
            using hcross_jp'1_ge hfst_eq hsnd_eq by (by100 simp)
          \<comment> \<open>Now combine: from cone jp we have cross(u\\_{jp+1}-cw, q-cw) \\<le> 0 and cross(q-cw, u\\_jp-cw) \\<le> 0.
             From cone jp' we have cross(u\\_{jp'}-cw, q-cw) \\<ge> 0 and cross(q-cw, u\\_{jp'+1}-cw) \\<ge> 0.
             For jp' = Suc jp mod nw: u\\_{jp'} = u\\_{jp+1}. cross(u\\_{jp+1}-cw,q-cw) \\<le> 0 AND \\<ge> 0. So = 0.
             This means sp\\_v = 0. Then q is on the shared diagonal.
             Similarly if jp' = (jp + nw - 1) mod nw (i.e., jp = Suc jp' mod nw): tp\\_v = 0.\<close>
          \<comment> \<open>HELPER: diagonal injectivity via Cramer + centroid-cone matching.\<close>
          \<comment> \<open>If sp\\_v = 0 and jp' = Suc jp: p and p' are on the shared diagonal, same parameter.\<close>
          have hadj_fwd: "jp' = Suc jp mod ?nw \<longrightarrow> p = p'"
          proof (intro impI)
            assume hTrue: "jp' = Suc jp mod ?nw"
            \<comment> \<open>sp\\_v = 0 from cross product analysis.\<close>
            from hTrue hcross_jp'_from_p
            have "(vxw(Suc jp mod ?nw)-?cxw)*(snd (phi_fn p)-?cyw)-
                (vyw(Suc jp mod ?nw)-?cyw)*(fst (phi_fn p)-?cxw) \<ge> 0" by (by100 simp)
            with hcross_jp1_le have "(vxw(Suc jp mod ?nw)-?cxw)*(snd (phi_fn p)-?cyw)-
                (vyw(Suc jp mod ?nw)-?cyw)*(fst (phi_fn p)-?cxw) = 0" by linarith
            hence "sp_v * ((vxw jp-?cxw)*(vyw(Suc jp mod ?nw)-?cyw)-(vyw jp-?cyw)*(vxw(Suc jp mod ?nw)-?cxw)) = 0"
              using hcross_neg1 by linarith
            hence hsp0: "sp_v = 0" using hC10_jp_v by (by100 simp)
            \<comment> \<open>Cramer: (dx,dy) = tp\\_v * (diagonal direction).\<close>
            have hsp_zero_eq: "(vye(Suc(jp+2) mod ?ne)-vye 1)*(fst p-vxe 1)-
                (vxe(Suc(jp+2) mod ?ne)-vxe 1)*(snd p-vye 1) = 0"
            proof -
              have "sp_v * ((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1))
                = (vye(Suc(jp+2) mod ?ne)-vye 1)*(fst p-vxe 1)-(vxe(Suc(jp+2) mod ?ne)-vxe 1)*(snd p-vye 1)"
                unfolding sp_v_def Let_def using hdet_v_pos by (by100 simp)
              with hsp0 show ?thesis by (by100 simp)
            qed
            have htp_v_det: "tp_v * ((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1))
                = (vxe(jp+2)-vxe 1)*(snd p-vye 1)-(vye(jp+2)-vye 1)*(fst p-vxe 1)"
              unfolding tp_v_def Let_def using hdet_v_pos by (by100 simp)
            \<comment> \<open>Solve 2x2 system: dx = tp\\_v * fx, dy = tp\\_v * fy.\<close>
            have hdx_p: "fst p - vxe 1 = tp_v * (vxe(Suc(jp+2) mod ?ne)-vxe 1)"
            proof -
              have "((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1)) * (fst p-vxe 1) =
                  (vxe(jp+2)-vxe 1)*((vye(Suc(jp+2) mod ?ne)-vye 1)*(fst p-vxe 1)) -
                  (vye(jp+2)-vye 1)*((vxe(Suc(jp+2) mod ?ne)-vxe 1)*(fst p-vxe 1))"
                by (by100 algebra)
              also have "\<dots> = (vxe(jp+2)-vxe 1)*((vxe(Suc(jp+2) mod ?ne)-vxe 1)*(snd p-vye 1)) -
                  (vye(jp+2)-vye 1)*((vxe(Suc(jp+2) mod ?ne)-vxe 1)*(fst p-vxe 1))"
                using hsp_zero_eq by (by100 algebra)
              also have "\<dots> = (vxe(Suc(jp+2) mod ?ne)-vxe 1)*((vxe(jp+2)-vxe 1)*(snd p-vye 1)-(vye(jp+2)-vye 1)*(fst p-vxe 1))"
                by (by100 algebra)
              also have "\<dots> = (vxe(Suc(jp+2) mod ?ne)-vxe 1)*tp_v*((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1))"
                using htp_v_det by (by100 algebra)
              finally show ?thesis using hdet_v_pos by (by100 simp)
            qed
            have hdy_p: "snd p - vye 1 = tp_v * (vye(Suc(jp+2) mod ?ne)-vye 1)"
            proof -
              have "((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1)) * (snd p-vye 1) =
                  (vye(Suc(jp+2) mod ?ne)-vye 1)*((vxe(jp+2)-vxe 1)*(snd p-vye 1)-(vye(jp+2)-vye 1)*(fst p-vxe 1)) +
                  (vye(jp+2)-vye 1)*((vye(Suc(jp+2) mod ?ne)-vye 1)*(fst p-vxe 1)-(vxe(Suc(jp+2) mod ?ne)-vxe 1)*(snd p-vye 1))"
                by (by100 algebra)
              also have "\<dots> = (vye(Suc(jp+2) mod ?ne)-vye 1)*tp_v*((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1)) + (vye(jp+2)-vye 1)*0"
                using htp_v_det hsp_zero_eq by (by100 algebra)
              finally show ?thesis using hdet_v_pos by (by100 simp)
            qed
            \<comment> \<open>Similarly for p': tp\\_v' = 0 and sp\\_v' = tp\\_v (from centroid-cone matching).\<close>
            \<comment> \<open>Then dx' = sp\\_v' * ex\\_s' = tp\\_v * fx (since ex\\_s' = fx for shared diagonal).\<close>
            \<comment> \<open>Case split: wrapping (jp=nw-1, jp'=0) vs non-wrapping.\<close>
            \<comment> \<open>Case split: wrapping (jp=nw-1) vs non-wrapping.\<close>
            show "p = p'"
            proof (cases "jp = ?nw - 1")
              case True
              \<comment> \<open>Wrapping: sp\\_v=0 puts p on edge 0 (v\\_0-v\\_1 diagonal). Impossible for interior p.\<close>
              have "Suc(jp+2) mod ?ne = 0"
              proof -
                have "jp + 2 = ?nw + 1" using True hlen by (by100 linarith)
                hence "Suc(jp+2) = ?nw + 2" by (by100 arith)
                also have "?nw + 2 = ?ne" using hne_eq by (by100 simp)
                finally have "Suc(jp+2) = ?ne" .
                thus ?thesis using hlen by (by100 simp)
              qed
              \<comment> \<open>From dx = tp\\_v * (vxe 0 - vxe 1): p on line v\\_1 to v\\_0 = edge 0.\<close>
              have hdx0: "fst p - vxe 1 = tp_v * (vxe 0 - vxe 1)"
                using hdx_p \<open>Suc(jp+2) mod ?ne = 0\<close> by (by100 simp)
              have hdy0: "snd p - vye 1 = tp_v * (vye 0 - vye 1)"
                using hdy_p \<open>Suc(jp+2) mod ?ne = 0\<close> by (by100 simp)
              have hfp: "fst p = (1-tp_v)*vxe 1 + tp_v*vxe 0"
                using hdx0 by (by100 algebra)
              have hsp_v2: "snd p = (1-tp_v)*vye 1 + tp_v*vye 0"
                using hdy0 by (by100 algebra)
              \<comment> \<open>p = edge\\_pt\\_e 0 (1-tp\\_v).\<close>
              have h0_lt: "(0::nat) < ?ne" using hlen hne_eq by (by100 linarith)
              have hSuc0: "Suc 0 mod ?ne = 1" using hlen hne_eq by (by100 simp)
              have hp_edge0: "p = edge_pt_e 0 (1-tp_v)"
              proof -
                have "edge_pt_e 0 (1-tp_v) = ((1-(1-tp_v))*vxe 0+(1-tp_v)*vxe(Suc 0 mod ?ne),
                    (1-(1-tp_v))*vye 0+(1-tp_v)*vye(Suc 0 mod ?ne))"
                  unfolding edge_pt_e_def by (by100 simp)
                also have "\<dots> = (tp_v*vxe 0+(1-tp_v)*vxe 1, tp_v*vye 0+(1-tp_v)*vye 1)"
                  using hSuc0 by (by100 simp)
                also have "\<dots> = ((1-tp_v)*vxe 1+tp_v*vxe 0, (1-tp_v)*vye 1+tp_v*vye 0)"
                  by (by100 auto)
                also have "\<dots> = p" using hfp hsp_v2 by (cases p) (by100 auto)
                finally show ?thesis by (by100 simp)
              qed
              have "tp_v \<noteq> 1"
              proof
                assume "tp_v = 1"
                \<comment> \<open>tp\\_v=1 with sp\\_v=0: p = v\\_1 + 1*(v\\_0-v\\_1) = v\\_0 = vertex 0.\<close>
                from hdx0 \<open>tp_v = 1\<close> have "fst p - vxe 1 = vxe 0 - vxe 1" by (by100 simp)
                hence "fst p = vxe 0" by linarith
                from hdy0 \<open>tp_v = 1\<close> have "snd p - vye 1 = vye 0 - vye 1" by (by100 simp)
                hence "snd p = vye 0" by linarith
                \<comment> \<open>p = vertex 0 = edge\\_pt\\_e(?ne-1, 1).\<close>
                have hne_pos: "?ne > 0" using hlen hne_eq by (by100 linarith)
                have hne1_lt: "?ne - 1 < ?ne" using hne_pos by (by100 linarith)
                have "Suc (?ne-1) mod ?ne = 0" using hne_pos by (by100 simp)
                have "edge_pt_e (?ne-1) 1 = (1*vxe 0 + (1-1)*vxe(Suc(?ne-1) mod ?ne),
                    1*vye 0 + (1-1)*vye(Suc(?ne-1) mod ?ne))"
                  unfolding edge_pt_e_def using \<open>Suc(?ne-1) mod ?ne = 0\<close> by (by100 simp)
                hence "edge_pt_e (?ne-1) 1 = (vxe 0, vye 0)" by (by100 simp)
                hence "p = edge_pt_e (?ne-1) 1" using \<open>fst p = vxe 0\<close> \<open>snd p = vye 0\<close>
                  by (cases p) (by100 simp)
                have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                from hint_p[rule_format, OF hne1_lt this] \<open>p = edge_pt_e (?ne-1) 1\<close> show False by (by100 simp)
              qed
              have "tp_v \<le> 1"
              proof (rule ccontr)
                assume "\<not> tp_v \<le> 1"
                hence "tp_v > 1" by linarith
                \<comment> \<open>tp\\_v > 1 with sp\\_v=0: p is outside the polygon (past vertex 0).\<close>
                \<comment> \<open>phi(p) = (1-tp\\_v)*cxw + tp\\_v*u\\_{jp+1}. With tp\\_v > 1: centroid weight < 0.
                   By centroid\\_weight\\_not\\_on\\_edge: phi(p) \\<ne> any target edge.
                   But with negative centroid weight: the proof breaks down.
                   Alternative: p \\<in> P\\_e = convex hull. On the line from v\\_1 to v\\_0,
                   points in P\\_e have parameter in [0,1]. tp\\_v > 1 means outside.\<close>
                \<comment> \<open>phi(p) = tp\\_v * u\\_{jp+1} (centroid=0, sp\\_v=0). With tp\\_v>1:
                   phi(p) is past u\\_{jp+1} on the ray from origin.
                   The edge cross at edge Suc jp mod nw for phi(p) < 0, so phi(p) \\<notin> P\\_w.\<close>
                have "phi_fn p \<in> P_w" using prop1 hp by (by100 blast)
                \<comment> \<open>phi(p) = tp\\_v * u\\_{jp+1}.\<close>
                have hcxw0: "?cxw = 0" using hcxw_0 unfolding cxw_def by (by100 simp)
                have hcyw0: "?cyw = 0" using hcyw_0 unfolding cyw_def by (by100 simp)
                have hphi_fst: "fst (phi_fn p) = tp_v*vxw(Suc jp mod ?nw)"
                  using hphi_x_v hsp0 hcxw0 by (by100 algebra)
                have hphi_snd: "snd (phi_fn p) = tp_v*vyw(Suc jp mod ?nw)"
                  using hphi_y_v hsp0 hcyw0 by (by100 algebra)
                \<comment> \<open>By centroid\\_weight\\_not\\_on\\_edge with alpha = 1-tp\\_v < 0 and sp=0, tp=tp\\_v:
                   actually, we use a DIFFERENT argument.
                   phi(p) = tp\\_v * u, |u|=1. phi(p) \\<in> P\\_w \\<subseteq> unit disk.
                   |phi(p)| = tp\\_v > 1. But all convex hull points have |q| \\<le> 1.\<close>
                \<comment> \<open>Norm argument: |phi(p)|^2 = tp\\_v^2 > 1 since tp\\_v > 1.\<close>
                have hnw_pos: "?nw > 0" using hlen by (by100 linarith)
                have hSjp_lt: "Suc jp mod ?nw < ?nw" using hnw_pos by (by100 simp)
                have hunit: "vxw(Suc jp mod ?nw)^2 + vyw(Suc jp mod ?nw)^2 = 1"
                  using hunit_circle_w[rule_format, OF hSjp_lt] .
                have hnorm_sq: "(fst (phi_fn p))^2 + (snd (phi_fn p))^2 = tp_v^2"
                  using hphi_fst hphi_snd hunit by (by100 algebra)
                have "tp_v^2 > 1" using \<open>tp_v > 1\<close> by (by100 auto)
                hence hnorm_gt1: "(fst (phi_fn p))^2 + (snd (phi_fn p))^2 > 1"
                  using hnorm_sq by linarith
                \<comment> \<open>All convex hull points have |q|^2 \\<le> 1 (Jensen).\<close>
                \<comment> \<open>phi(p) \\<in> P\\_w, so |phi(p)|^2 \\<le> 1. Contradiction.\<close>
                from \<open>phi_fn p \<in> P_w\<close>
                have "\<exists>coeffs. (\<forall>i<?nw. coeffs i \<ge> 0) \<and> (\<Sum>i<?nw. coeffs i) = 1 \<and>
                    fst (phi_fn p) = (\<Sum>i<?nw. coeffs i * vxw i) \<and>
                    snd (phi_fn p) = (\<Sum>i<?nw. coeffs i * vyw i)"
                  using hC5_w by (by100 auto)
                then obtain cfs where hcfs: "(\<forall>i<?nw. cfs i \<ge> 0)" "(\<Sum>i<?nw. cfs i) = 1"
                    "fst (phi_fn p) = (\<Sum>i<?nw. cfs i * vxw i)"
                    "snd (phi_fn p) = (\<Sum>i<?nw. cfs i * vyw i)"
                  by (by100 blast)
                \<comment> \<open>|phi(p)|^2 = (\\<Sum> c\\_i*vxw\\_i)^2 + (\\<Sum> c\\_i*vyw\\_i)^2 \\<le> \\<Sum> c\\_i*(vxw\\_i^2+vyw\\_i^2) = 1.\<close>
                have "(fst (phi_fn p))^2 + (snd (phi_fn p))^2 \<le> 1"
                  using convex_hull_unit_circle_norm_le[OF hcfs(1) hcfs(2) hunit_circle_w]
                    hcfs(3) hcfs(4) by (by100 simp)
                with hnorm_gt1 show False by linarith
              qed
              have "(1-tp_v) \<in> I_set" using htp_v_ge \<open>tp_v \<le> 1\<close> unfolding top1_unit_interval_def
                by (by100 auto)
              from hint_p[rule_format, OF h0_lt this] hp_edge0 show ?thesis by (by100 simp)
            next
              case False
              \<comment> \<open>Non-wrapping: apply adjacent\\_cone\\_diagonal\\_injective.\<close>
              \<comment> \<open>Non-wrapping: jp \\<noteq> nw-1, jp' = Suc jp mod nw.
                 Apply adjacent\\_cone\\_diagonal\\_injective with proper instantiation.\<close>
              \<comment> \<open>Step 1: phi(p)=phi(p') with centroid=0 gives the matching equations.\<close>
              have hcxw0_loc: "?cxw = 0" using hcxw_0 unfolding cxw_def by (by100 simp)
              have hcyw0_loc: "?cyw = 0" using hcyw_0 unfolding cyw_def by (by100 simp)
              \<comment> \<open>Step 2: From phi(p)=phi(p'), sp\\_v=0, centroid=0:\<close>
              have hphi_match_x: "tp_v * vxw(Suc jp mod ?nw) = sp_v' * vxw(Suc jp mod ?nw) + tp_v' * vxw(Suc jp' mod ?nw)"
              proof -
                from heq have "fst (phi_fn p) = fst (phi_fn p')" by (by100 simp)
                thus ?thesis using hphi_x_v hphi_x_v' hsp0 hcxw0_loc hTrue by (by100 simp)
              qed
              have hphi_match_y: "tp_v * vyw(Suc jp mod ?nw) = sp_v' * vyw(Suc jp mod ?nw) + tp_v' * vyw(Suc jp' mod ?nw)"
              proof -
                from heq have "snd (phi_fn p) = snd (phi_fn p')" by (by100 simp)
                thus ?thesis using hphi_y_v hphi_y_v' hsp0 hcyw0_loc hTrue by (by100 simp)
              qed
              \<comment> \<open>Step 3: C10 at Suc jp mod nw gives nonzero cross product.\<close>
              have hC10_ne_loc: "vxw(Suc jp mod ?nw)*vyw(Suc jp' mod ?nw) - vyw(Suc jp mod ?nw)*vxw(Suc jp' mod ?nw) \<noteq> 0"
              proof -
                have hnw_pos: "?nw > 0" using hlen by (by100 linarith)
                have hjp1_lt: "Suc jp mod ?nw < ?nw" using hnw_pos by (by100 simp)
                from hC10_w[rule_format, OF hjp1_lt]
                have "(vxw(Suc jp mod ?nw)-?cxw)*(vyw(Suc(Suc jp mod ?nw) mod ?nw)-?cyw) -
                    (vyw(Suc jp mod ?nw)-?cyw)*(vxw(Suc(Suc jp mod ?nw) mod ?nw)-?cxw) > 0"
                  by (by100 simp)
                moreover have "Suc(Suc jp mod ?nw) mod ?nw = Suc jp' mod ?nw"
                  using hTrue by (by100 simp)
                ultimately have "vxw(Suc jp mod ?nw)*vyw(Suc jp' mod ?nw) - vyw(Suc jp mod ?nw)*vxw(Suc jp' mod ?nw) > 0"
                  using hcxw0_loc hcyw0_loc by (by100 simp)
                thus ?thesis by linarith
              qed
              \<comment> \<open>Step 4: Shared diagonal direction: ex\\_s' = fx\\_s for non-wrapping.\<close>
              have hjp3_lt: "jp + 3 < ?ne" using False hjp hne_eq hlen by (by100 linarith)
              have hjp3_mod: "Suc(jp+2) mod ?ne = jp+3" using hjp3_lt by (by100 simp)
              have hjp'2_eq: "jp'+2 = Suc(jp+2) mod ?ne"
              proof -
                have "Suc jp < ?nw" using False hjp by (by100 linarith)
                hence "jp' = Suc jp" using hTrue by (by100 simp)
                hence "jp'+2 = Suc jp + 2" by (by100 arith)
                also have "\<dots> = jp + 3" by (by100 arith)
                also have "\<dots> = Suc(jp+2) mod ?ne" using hjp3_mod by (by100 simp)
                finally show ?thesis .
              qed
              have hex'_eq: "vxe(jp'+2)-vxe 1 = vxe(Suc(jp+2) mod ?ne)-vxe 1"
                using hjp'2_eq by (by100 simp)
              have hey'_eq: "vye(jp'+2)-vye 1 = vye(Suc(jp+2) mod ?ne)-vye 1"
                using hjp'2_eq by (by100 simp)
              \<comment> \<open>Step 5: p' Cramer determinant > 0.\<close>
              have hdet_v'_pos_loc: "(vxe(jp'+2)-vxe 1)*(vye(Suc(jp'+2) mod ?ne)-vye 1)-
                  (vye(jp'+2)-vye 1)*(vxe(Suc(jp'+2) mod ?ne)-vxe 1) > 0"
                using hdet_pos[rule_format, OF hjp'] by (by100 simp)
              \<comment> \<open>Step 6: p' Cramer formulas.\<close>
              have hsp_v'_mul_loc: "sp_v' * ((vxe(jp'+2)-vxe 1)*(vye(Suc(jp'+2) mod ?ne)-vye 1)-(vye(jp'+2)-vye 1)*(vxe(Suc(jp'+2) mod ?ne)-vxe 1))
                = (vye(Suc(jp'+2) mod ?ne)-vye 1)*(fst p'-vxe 1)-(vxe(Suc(jp'+2) mod ?ne)-vxe 1)*(snd p'-vye 1)"
                unfolding sp_v'_def Let_def using hdet_v'_pos_loc by (by100 simp)
              have htp_v'_mul_loc: "tp_v' * ((vxe(jp'+2)-vxe 1)*(vye(Suc(jp'+2) mod ?ne)-vye 1)-(vye(jp'+2)-vye 1)*(vxe(Suc(jp'+2) mod ?ne)-vxe 1))
                = (vxe(jp'+2)-vxe 1)*(snd p'-vye 1)-(vye(jp'+2)-vye 1)*(fst p'-vxe 1)"
                unfolding tp_v'_def Let_def using hdet_v'_pos_loc by (by100 simp)
              \<comment> \<open>Step 7: Apply adjacent\\_cone\\_diagonal\\_injective.\<close>
              from adjacent_cone_diagonal_injective[OF hsp0 htp_v_ge hdet_v_pos htp_v_det hsp_zero_eq
                  hphi_match_x hphi_match_y hC10_ne_loc hex'_eq hey'_eq hdet_v'_pos_loc
                  hsp_v'_mul_loc htp_v'_mul_loc]
              have "fst p - vxe 1 = fst p' - vxe 1 \<and> snd p - vye 1 = snd p' - vye 1" .
              hence "fst p = fst p'" "snd p = snd p'" by auto
              show ?thesis by (cases p, cases p') (use \<open>fst p = fst p'\<close> \<open>snd p = snd p'\<close> in \<open>by100 auto\<close>)
            qed
          qed
          have hadj_bwd: "jp = Suc jp' mod ?nw \<longrightarrow> p = p'"
          proof (intro impI)
            assume hBwd: "jp = Suc jp' mod ?nw"
            \<comment> \<open>From hcross\\_jp\\_le and cone jp': cross(phi-cw, u\\_jp-cw) = 0. So tp\\_v = 0.\<close>
            from hcross_jp'1_from_p have "(fst (phi_fn p)-?cxw)*(vyw(Suc jp' mod ?nw)-?cyw)-
                (snd (phi_fn p)-?cyw)*(vxw(Suc jp' mod ?nw)-?cxw) \<ge> 0" .
            hence "(fst (phi_fn p)-?cxw)*(vyw jp-?cyw)-(snd (phi_fn p)-?cyw)*(vxw jp-?cxw) \<ge> 0"
              using hBwd by (by100 simp)
            with hcross_jp_le have "(fst (phi_fn p)-?cxw)*(vyw jp-?cyw)-(snd (phi_fn p)-?cyw)*(vxw jp-?cxw) = 0"
              by linarith
            hence "tp_v * ((vxw jp-?cxw)*(vyw(Suc jp mod ?nw)-?cyw)-(vyw jp-?cyw)*(vxw(Suc jp mod ?nw)-?cxw)) = 0"
              using hcross_neg2 by linarith
            hence htp0: "tp_v = 0" using hC10_jp_v by (by100 simp)
            \<comment> \<open>With tp\\_v=0: p on LEFT diagonal of sector jp (from v\\_1 to v\\_{jp+2}).\<close>
            \<comment> \<open>Symmetric diagonal injectivity argument.\<close>
            \<comment> \<open>Cramer with tp\\_v=0: ex*dy-ey*dx=0.\<close>
            have htp_zero_eq: "(vxe(jp+2)-vxe 1)*(snd p-vye 1)-(vye(jp+2)-vye 1)*(fst p-vxe 1) = 0"
            proof -
              have "tp_v * ((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1))
                = (vxe(jp+2)-vxe 1)*(snd p-vye 1)-(vye(jp+2)-vye 1)*(fst p-vxe 1)"
                unfolding tp_v_def Let_def using hdet_v_pos by (by100 simp)
              with htp0 show ?thesis by (by100 simp)
            qed
            have hsp_v_det_loc: "sp_v * ((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1))
              = (vye(Suc(jp+2) mod ?ne)-vye 1)*(fst p-vxe 1)-(vxe(Suc(jp+2) mod ?ne)-vxe 1)*(snd p-vye 1)"
              unfolding sp_v_def Let_def using hdet_v_pos by (by100 simp)
            \<comment> \<open>dx = sp\\_v*ex, dy = sp\\_v*ey.\<close>
            have hdx_bwd: "fst p - vxe 1 = sp_v * (vxe(jp+2)-vxe 1)"
            proof -
              have "((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1)) * (fst p-vxe 1) =
                  (vxe(jp+2)-vxe 1)*((vye(Suc(jp+2) mod ?ne)-vye 1)*(fst p-vxe 1)-(vxe(Suc(jp+2) mod ?ne)-vxe 1)*(snd p-vye 1)) +
                  (vxe(Suc(jp+2) mod ?ne)-vxe 1)*((vxe(jp+2)-vxe 1)*(snd p-vye 1)-(vye(jp+2)-vye 1)*(fst p-vxe 1))"
                by (by100 algebra)
              also have "\<dots> = (vxe(jp+2)-vxe 1)*(sp_v*((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1))) + (vxe(Suc(jp+2) mod ?ne)-vxe 1)*0"
                using hsp_v_det_loc htp_zero_eq by (by100 algebra)
              finally show ?thesis using hdet_v_pos by (by100 simp)
            qed
            have hdy_bwd: "snd p - vye 1 = sp_v * (vye(jp+2)-vye 1)"
            proof -
              have "((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1)) * (snd p-vye 1) =
                  (vye(jp+2)-vye 1)*((vye(Suc(jp+2) mod ?ne)-vye 1)*(fst p-vxe 1)-(vxe(Suc(jp+2) mod ?ne)-vxe 1)*(snd p-vye 1)) +
                  (vye(Suc(jp+2) mod ?ne)-vye 1)*((vxe(jp+2)-vxe 1)*(snd p-vye 1)-(vye(jp+2)-vye 1)*(fst p-vxe 1))"
                by (by100 algebra)
              also have "\<dots> = (vye(jp+2)-vye 1)*(sp_v*((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1))) + (vye(Suc(jp+2) mod ?ne)-vye 1)*0"
                using hsp_v_det_loc htp_zero_eq by (by100 algebra)
              finally show ?thesis using hdet_v_pos by (by100 simp)
            qed
            \<comment> \<open>Case split: wrapping (jp=0) vs non-wrapping.\<close>
            show "p = p'"
            proof (cases "jp = 0")
              case True
              \<comment> \<open>jp=0: LEFT diagonal = edge 1 (v\\_1 to v\\_2). p on edge 1 \\<to> contradiction.\<close>
              \<comment> \<open>p = v\\_1 + sp\\_v*(v\\_2-v\\_1) = (1-sp\\_v)*v\\_1 + sp\\_v*v\\_2 = edge\\_pt\\_e 1 sp\\_v.\<close>
              have h1_lt: "(1::nat) < ?ne" using hlen hne_eq by (by100 linarith)
              have hne_gt2: "?ne > 2" using hlen hne_eq by (by100 linarith)
              have hSuc1: "Suc 1 mod ?ne = 2"
              proof -
                have "(2::nat) < ?ne" using hne_gt2 by linarith
                thus ?thesis by (by100 simp)
              qed
              have hp_edge1: "p = edge_pt_e 1 sp_v"
              proof -
                have "edge_pt_e 1 sp_v = ((1-sp_v)*vxe 1+sp_v*vxe(Suc 1 mod ?ne),
                    (1-sp_v)*vye 1+sp_v*vye(Suc 1 mod ?ne))"
                  unfolding edge_pt_e_def by (by100 simp)
                also have "\<dots> = ((1-sp_v)*vxe 1+sp_v*vxe 2, (1-sp_v)*vye 1+sp_v*vye 2)"
                  using hSuc1 by (by100 simp)
                finally have hedge_form: "edge_pt_e 1 sp_v = ((1-sp_v)*vxe 1+sp_v*vxe 2, (1-sp_v)*vye 1+sp_v*vye 2)" .
                \<comment> \<open>p = (vxe 1 + sp\\_v*(vxe(jp+2)-vxe 1), ...) with jp=0: jp+2=2.\<close>
                have "jp + 2 = Suc(Suc 0)" using True by (by100 arith)
                from hdx_bwd have "fst p - vxe 1 = sp_v*(vxe(jp+2) - vxe 1)" .
                have hjp2_is_2: "jp + 2 = (2::nat)" using True by (by100 arith)
                have hvxe_jp2: "vxe(jp+2) = vxe 2" using hjp2_is_2 by (by100 metis)
                have hvye_jp2: "vye(jp+2) = vye 2" using hjp2_is_2 by (by100 metis)
                from hdx_bwd hvxe_jp2
                have "fst p - vxe 1 = sp_v*(vxe 2 - vxe 1)" by (by100 simp)
                hence hfp: "fst p = (1-sp_v)*vxe 1 + sp_v*vxe 2" by (by100 algebra)
                from hdy_bwd hvye_jp2
                have "snd p - vye 1 = sp_v*(vye 2 - vye 1)" by (by100 simp)
                hence hgp: "snd p = (1-sp_v)*vye 1 + sp_v*vye 2" by (by100 algebra)
                from hedge_form hfp hgp show ?thesis by (cases p) (by100 auto)
              qed
              \<comment> \<open>sp\\_v \\<in> I\\_set from norm bound.\<close>
              have "sp_v \<le> 1"
              proof (rule ccontr)
                assume "\<not> sp_v \<le> 1"
                hence "sp_v > 1" by linarith
                \<comment> \<open>|phi(p)|^2 = sp\\_v^2 > 1 (from tp\\_v=0, centroid=0).\<close>
                have hcxw0: "?cxw = 0" using hcxw_0 unfolding cxw_def by (by100 simp)
                have hcyw0: "?cyw = 0" using hcyw_0 unfolding cyw_def by (by100 simp)
                have hphi_fst_sp: "fst (phi_fn p) = sp_v*vxw jp"
                  using hphi_x_v htp0 hcxw0 by (by100 algebra)
                have hphi_snd_sp: "snd (phi_fn p) = sp_v*vyw jp"
                  using hphi_y_v htp0 hcyw0 by (by100 algebra)
                have hunit_jp: "vxw jp^2 + vyw jp^2 = 1"
                  using hunit_circle_w hjp by (by100 blast)
                have "(fst (phi_fn p))^2 + (snd (phi_fn p))^2 = sp_v^2"
                  using hphi_fst_sp hphi_snd_sp hunit_jp by (by100 algebra)
                moreover have "sp_v^2 > 1" using \<open>sp_v > 1\<close> by (by100 auto)
                ultimately have "(fst (phi_fn p))^2 + (snd (phi_fn p))^2 > 1" by linarith
                have "phi_fn p \<in> P_w" using prop1 hp by (by100 blast)
                hence "\<exists>cfs. (\<forall>i<?nw. cfs i \<ge> 0) \<and> (\<Sum>i<?nw. cfs i) = 1 \<and>
                    fst (phi_fn p) = (\<Sum>i<?nw. cfs i * vxw i) \<and>
                    snd (phi_fn p) = (\<Sum>i<?nw. cfs i * vyw i)"
                  using hC5_w by (by100 auto)
                then obtain cfs where hcfs: "(\<forall>i<?nw. cfs i \<ge> 0)" "(\<Sum>i<?nw. cfs i) = 1"
                    "fst (phi_fn p) = (\<Sum>i<?nw. cfs i * vxw i)"
                    "snd (phi_fn p) = (\<Sum>i<?nw. cfs i * vyw i)"
                  by (by100 blast)
                have "(fst (phi_fn p))^2 + (snd (phi_fn p))^2 \<le> 1"
                  using convex_hull_unit_circle_norm_le[OF hcfs(1) hcfs(2) hunit_circle_w]
                    hcfs(3) hcfs(4) by (by100 simp)
                with \<open>(fst (phi_fn p))^2 + (snd (phi_fn p))^2 > 1\<close> show False by linarith
              qed
              have "sp_v \<in> I_set" using hsp_v_ge \<open>sp_v \<le> 1\<close> unfolding top1_unit_interval_def
                by (by100 auto)
              from hint_p[rule_format, OF h1_lt this] hp_edge1 show ?thesis by (by100 simp)
            next
              case False
              \<comment> \<open>Non-wrapping backward: apply adjacent\\_cone\\_diagonal\\_injective\\_tp.\<close>
              \<comment> \<open>Non-wrapping backward: jp \\<noteq> 0, jp = Suc jp' mod nw, tp\\_v = 0.\<close>
              \<comment> \<open>Shared diagonal: from v\\_1 to v\\_{jp+2}. Direction = (ex\\_s, ey\\_s).\<close>
              \<comment> \<open>For sector jp': RIGHT boundary goes to v\\_{Suc(jp'+2) mod ne}.\<close>
              \<comment> \<open>With jp = Suc jp' (non-wrapping, jp'\\<noteq>nw-1): Suc(jp'+2) = jp+2. Same direction.\<close>
              have hcxw0: "?cxw = 0" using hcxw_0 unfolding cxw_def by (by100 simp)
              have hcyw0: "?cyw = 0" using hcyw_0 unfolding cyw_def by (by100 simp)
              \<comment> \<open>phi matching with centroid=0 and tp\\_v=0.\<close>
              have hphi_match_x_bwd: "sp_v * vxw jp = tp_v' * vxw jp + sp_v' * vxw jp'"
              proof -
                from heq have "fst (phi_fn p) = fst (phi_fn p')" by (by100 simp)
                thus ?thesis using hphi_x_v hphi_x_v' htp0 hcxw0 hBwd by (by100 simp)
              qed
              have hphi_match_y_bwd: "sp_v * vyw jp = tp_v' * vyw jp + sp_v' * vyw jp'"
              proof -
                from heq have "snd (phi_fn p) = snd (phi_fn p')" by (by100 simp)
                thus ?thesis using hphi_y_v hphi_y_v' htp0 hcyw0 hBwd by (by100 simp)
              qed
              \<comment> \<open>C10 ne for u\\_{jp'} and u\\_jp.\<close>
              have hC10_ne_bwd: "vxw jp'*vyw jp - vyw jp'*vxw jp \<noteq> 0"
              proof -
                from hC10_w[rule_format, OF hjp'] have "(vxw jp'-?cxw)*(vyw(Suc jp' mod ?nw)-?cyw) -
                    (vyw jp'-?cyw)*(vxw(Suc jp' mod ?nw)-?cxw) > 0" by (by100 simp)
                hence "vxw jp'*vyw(Suc jp' mod ?nw) - vyw jp'*vxw(Suc jp' mod ?nw) > 0"
                  using hcxw0 hcyw0 by (by100 simp)
                moreover have "Suc jp' mod ?nw = jp" using hBwd by (by100 auto)
                ultimately have "vxw jp'*vyw jp - vyw jp'*vxw jp > 0" by (by100 simp)
                thus ?thesis by linarith
              qed
              \<comment> \<open>Shared diagonal direction: fx\\_s'=ex\\_s for sector jp'.\<close>
              have hjp'2_eq_bwd: "Suc(jp'+2) mod ?ne = jp+2"
              proof -
                have "Suc jp' < ?nw"
                proof (rule ccontr)
                  assume "\<not> Suc jp' < ?nw"
                  hence "Suc jp' \<ge> ?nw" by linarith
                  with hjp' have "Suc jp' = ?nw" by (by100 linarith)
                  hence "Suc jp' mod ?nw = 0" by (by100 simp)
                  hence "jp = 0" using hBwd by (by100 simp)
                  with False show False by (by100 simp)
                qed
                hence hjp'1: "jp' + 1 = jp" using hBwd by (by100 simp)
                hence hSjp'2: "Suc(jp'+2) = jp + 2" by (by100 arith)
                have "jp + 2 < ?ne" using hjp hne_eq by (by100 linarith)
                hence "Suc(jp'+2) mod ?ne = jp + 2" using hSjp'2 by (by100 simp)
                thus ?thesis using hSjp'2 by (by100 simp)
              qed
              have hfx'_eq_bwd: "vxe(Suc(jp'+2) mod ?ne)-vxe 1 = vxe(jp+2)-vxe 1"
                using hjp'2_eq_bwd by (by100 simp)
              have hfy'_eq_bwd: "vye(Suc(jp'+2) mod ?ne)-vye 1 = vye(jp+2)-vye 1"
                using hjp'2_eq_bwd by (by100 simp)
              \<comment> \<open>p' Cramer determinant and formulas.\<close>
              have hdet_v'_pos_bwd: "(vxe(jp'+2)-vxe 1)*(vye(Suc(jp'+2) mod ?ne)-vye 1)-
                  (vye(jp'+2)-vye 1)*(vxe(Suc(jp'+2) mod ?ne)-vxe 1) > 0"
                using hdet_pos[rule_format, OF hjp'] by (by100 simp)
              have hsp_v'_mul_bwd: "sp_v' * ((vxe(jp'+2)-vxe 1)*(vye(Suc(jp'+2) mod ?ne)-vye 1)-(vye(jp'+2)-vye 1)*(vxe(Suc(jp'+2) mod ?ne)-vxe 1))
                = (vye(Suc(jp'+2) mod ?ne)-vye 1)*(fst p'-vxe 1)-(vxe(Suc(jp'+2) mod ?ne)-vxe 1)*(snd p'-vye 1)"
                unfolding sp_v'_def Let_def using hdet_v'_pos_bwd by (by100 simp)
              have htp_v'_mul_bwd: "tp_v' * ((vxe(jp'+2)-vxe 1)*(vye(Suc(jp'+2) mod ?ne)-vye 1)-(vye(jp'+2)-vye 1)*(vxe(Suc(jp'+2) mod ?ne)-vxe 1))
                = (vxe(jp'+2)-vxe 1)*(snd p'-vye 1)-(vye(jp'+2)-vye 1)*(fst p'-vxe 1)"
                unfolding tp_v'_def Let_def using hdet_v'_pos_bwd by (by100 simp)
              \<comment> \<open>Apply adjacent\\_cone\\_diagonal\\_injective\\_tp.\<close>
              from adjacent_cone_diagonal_injective_tp[OF htp0 hsp_v_ge hdet_v_pos hsp_v_det_loc htp_zero_eq
                  hphi_match_x_bwd hphi_match_y_bwd hC10_ne_bwd hfx'_eq_bwd hfy'_eq_bwd
                  hdet_v'_pos_bwd hsp_v'_mul_bwd htp_v'_mul_bwd]
              have "fst p - vxe 1 = fst p' - vxe 1 \<and> snd p - vye 1 = snd p' - vye 1" .
              hence "fst p = fst p'" "snd p = snd p'" by auto
              show ?thesis using \<open>fst p = fst p'\<close> \<open>snd p = snd p'\<close>
                by (cases p, cases p') (by100 auto)
            qed
          qed
          show ?thesis
          proof (cases "jp' = Suc jp mod ?nw")
            case True from hadj_fwd True show ?thesis by (by100 simp)
          next
            case False
            show ?thesis
            proof (cases "jp = Suc jp' mod ?nw")
              case True from hadj_bwd True show ?thesis by (by100 simp)
            next
              case False
              \<comment> \<open>Non-adjacent sector disjointness.\<close>
              \<comment> \<open>Non-adjacent: jp \\<noteq> jp', jp' \\<noteq> Suc jp, jp \\<noteq> Suc jp'. Sectors \\<ge> 2 apart.
                 phi(p) satisfies: cross(u\\_{jp+1}-cw, phi-cw) \\<le> 0 AND cross(phi-cw, u\\_jp-cw) \\<le> 0.
                 For non-adjacent jp': at least one cone condition from jp' fails.\<close>
              \<comment> \<open>For nw = 3: non-adjacent case is VACUOUS (all pairs adjacent).\<close>
              \<comment> \<open>For nw \\<ge> 4: use cross product from C11 to show angular incompatibility.\<close>
              \<comment> \<open>Apply non\\_adjacent\\_cone\\_disjoint.\<close>
              have hcxw0: "?cxw = 0" using hcxw_0 unfolding cxw_def by (by100 simp)
              have hcyw0: "?cyw = 0" using hcyw_0 unfolding cyw_def by (by100 simp)
              have hC10_0: "\<forall>i<?nw. vxw i * vyw(Suc i mod ?nw) - vyw i * vxw(Suc i mod ?nw) > 0"
              proof (intro allI impI)
                fix i assume "i < ?nw"
                from hC10_w[rule_format, OF this] show "vxw i * vyw(Suc i mod ?nw) - vyw i * vxw(Suc i mod ?nw) > 0"
                  using hcxw0 hcyw0 by (by100 simp)
              qed
              \<comment> \<open>sp\\_v + tp\\_v > 0 (since p \\<noteq> vertex 1: dx or dy nonzero, hence sp or tp > 0).\<close>
              have hst_pos: "sp_v + tp_v > 0"
              proof (rule ccontr)
                assume "\<not> sp_v + tp_v > 0"
                hence "sp_v = 0 \<and> tp_v = 0" using hsp_v_ge htp_v_ge by linarith
                hence "fst p = vxe 1 \<and> snd p = vye 1"
                proof -
                  have "sp_v * ((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1))
                    = (vye(Suc(jp+2) mod ?ne)-vye 1)*(fst p-vxe 1)-(vxe(Suc(jp+2) mod ?ne)-vxe 1)*(snd p-vye 1)"
                    unfolding sp_v_def Let_def using hdet_v_pos by (by100 simp)
                  have "tp_v * ((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1))
                    = (vxe(jp+2)-vxe 1)*(snd p-vye 1)-(vye(jp+2)-vye 1)*(fst p-vxe 1)"
                    unfolding tp_v_def Let_def using hdet_v_pos by (by100 simp)
                  have hsp_mul: "sp_v * ((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1))
                    = (vye(Suc(jp+2) mod ?ne)-vye 1)*(fst p-vxe 1)-(vxe(Suc(jp+2) mod ?ne)-vxe 1)*(snd p-vye 1)"
                    unfolding sp_v_def Let_def using hdet_v_pos by (by100 simp)
                  have htp_mul: "tp_v * ((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1))
                    = (vxe(jp+2)-vxe 1)*(snd p-vye 1)-(vye(jp+2)-vye 1)*(fst p-vxe 1)"
                    unfolding tp_v_def Let_def using hdet_v_pos by (by100 simp)
                  from hsp_mul \<open>sp_v = 0 \<and> tp_v = 0\<close>
                  have hfy_eq: "(vye(Suc(jp+2) mod ?ne)-vye 1)*(fst p-vxe 1)-(vxe(Suc(jp+2) mod ?ne)-vxe 1)*(snd p-vye 1) = 0"
                    by (by100 simp)
                  from htp_mul \<open>sp_v = 0 \<and> tp_v = 0\<close>
                  have hex_eq: "(vxe(jp+2)-vxe 1)*(snd p-vye 1)-(vye(jp+2)-vye 1)*(fst p-vxe 1) = 0"
                    by (by100 simp)
                  \<comment> \<open>2x2 system with det > 0: dx = dy = 0.\<close>
                  have "(vxe(jp+2)-vxe 1)*((vye(Suc(jp+2) mod ?ne)-vye 1)*(fst p-vxe 1)-(vxe(Suc(jp+2) mod ?ne)-vxe 1)*(snd p-vye 1)) +
                    (vxe(Suc(jp+2) mod ?ne)-vxe 1)*((vxe(jp+2)-vxe 1)*(snd p-vye 1)-(vye(jp+2)-vye 1)*(fst p-vxe 1)) =
                    ((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1))*(fst p-vxe 1)"
                    by (by100 algebra)
                  hence "((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1))*(fst p-vxe 1) = 0"
                    using hfy_eq hex_eq by (by100 simp)
                  hence "fst p = vxe 1" using hdet_v_pos by (by100 simp)
                  have "(vye(jp+2)-vye 1)*((vye(Suc(jp+2) mod ?ne)-vye 1)*(fst p-vxe 1)-(vxe(Suc(jp+2) mod ?ne)-vxe 1)*(snd p-vye 1)) +
                    (vye(Suc(jp+2) mod ?ne)-vye 1)*((vxe(jp+2)-vxe 1)*(snd p-vye 1)-(vye(jp+2)-vye 1)*(fst p-vxe 1)) =
                    ((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1))*(snd p-vye 1)"
                    by (by100 algebra)
                  hence "((vxe(jp+2)-vxe 1)*(vye(Suc(jp+2) mod ?ne)-vye 1)-(vye(jp+2)-vye 1)*(vxe(Suc(jp+2) mod ?ne)-vxe 1))*(snd p-vye 1) = 0"
                    using hfy_eq hex_eq by (by100 simp)
                  hence "snd p = vye 1" using hdet_v_pos by (by100 simp)
                  with \<open>fst p = vxe 1\<close> show ?thesis by (by100 simp)
                qed
                hence "p = (vxe 1, vye 1)" by (cases p) (by100 auto)
                with hp_ne_v1 show False by (by100 simp)
              qed
              \<comment> \<open>Cone conditions from phi(p)=phi(p').\<close>
              have hcone1_inst: "vxw jp' * (sp_v*vyw jp + tp_v*vyw(Suc jp mod ?nw)) -
                  vyw jp' * (sp_v*vxw jp + tp_v*vxw(Suc jp mod ?nw)) \<ge> 0"
              proof -
                from hcross_jp'_from_p hcxw0 hcyw0
                have "(vxw jp'-0)*(snd (phi_fn p)-0)-(vyw jp'-0)*(fst (phi_fn p)-0) \<ge> 0"
                  by (by100 simp)
                hence "vxw jp'*snd (phi_fn p) - vyw jp'*fst (phi_fn p) \<ge> 0" by (by100 simp)
                thus ?thesis using hphi_x_v hphi_y_v hcxw0 hcyw0 by (by100 simp)
              qed
              have hcone2_inst: "(sp_v*vxw jp + tp_v*vxw(Suc jp mod ?nw)) * vyw(Suc jp' mod ?nw) -
                  (sp_v*vyw jp + tp_v*vyw(Suc jp mod ?nw)) * vxw(Suc jp' mod ?nw) \<ge> 0"
              proof -
                from hcross_jp'1_from_p hcxw0 hcyw0
                have "(fst (phi_fn p)-0)*vyw(Suc jp' mod ?nw) - (snd (phi_fn p)-0)*vxw(Suc jp' mod ?nw) \<ge> 0"
                  by (by100 simp)
                hence "fst (phi_fn p)*vyw(Suc jp' mod ?nw) - snd (phi_fn p)*vxw(Suc jp' mod ?nw) \<ge> 0" by (by100 simp)
                thus ?thesis using hphi_x_v hphi_y_v hcxw0 hcyw0 by (by100 simp)
              qed
              from non_adjacent_cone_disjoint[OF hlen hC10_0 hC11_w hunit_circle_w
                  hsum_vxw_0 hsum_vyw_0 hjp hjp' \<open>jp \<noteq> jp'\<close> \<open>jp' \<noteq> Suc jp mod ?nw\<close> False
                  hsp_v_ge htp_v_ge hst_pos hcone1_inst hcone2_inst]
              show ?thesis by (by100 simp)
            qed
          qed
        qed
      qed
      have prop11: "\<forall>p\<in>P_e.
          (\<forall>i<?ne. \<forall>t\<in>I_set. p \<noteq> edge_pt_e i t) \<longrightarrow>
          (\<forall>j<?nw. \<forall>s\<in>I_set. phi_fn p \<noteq> edge_pt_w j s)"
      proof (intro ballI impI allI)
        fix p j s assume hp: "p \<in> P_e" and hint_p: "\<forall>i<?ne. \<forall>t\<in>I_set. p \<noteq> edge_pt_e i t"
            and hj: "j < ?nw" and hs: "s \<in> I_set"
        have h1_lt: "1 < ?ne" using hlen_ext by linarith
        have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        have hp_ne_v1: "p \<noteq> (vxe 1, vye 1)"
        proof
          assume "p = (vxe 1, vye 1)"
          hence "p = edge_pt_e 1 0" unfolding edge_pt_e_def by (by100 simp)
          with hint_p[rule_format, OF h1_lt h0_I] show False by simp
        qed
        from hfan_cover[rule_format, OF hp] hp_ne_v1
        obtain jp where hjp: "jp < ?nw" and hin_sec: "in_sector jp p" by blast
        have hjp2_lt: "jp + 2 < ?ne" using hjp hne_eq by linarith
        \<comment> \<open>s\\_p + t\\_p < 1 (since = 1 would put p on edge jp+2, contradicting interior).
           Therefore the centroid weight in phi\\_fn(p) is strictly positive.
           phi\\_fn(p) is then strictly on the interior side of every edge of P\\_w.
           Hence phi\\_fn(p) \\<noteq> any edge point.\<close>
        \<comment> \<open>The edge cross product at edge jp+2 for point p is > 0 (strictly).
           This means the centroid weight in phi\\_fn(p) is strictly positive.
           A point with positive centroid weight in the target fan is strictly interior
           to P\\_w, hence not on any boundary edge.\<close>
        let ?si_jp = "Suc(jp+2) mod ?ne"
        have hedge_pos: "(vxe ?si_jp - vxe(jp+2))*(snd p - vye(jp+2)) -
            (vye ?si_jp - vye(jp+2))*(fst p - vxe(jp+2)) > 0"
        proof -
          from hp obtain coeffs_p where hcp: "(\<forall>i<?ne. coeffs_p i \<ge> 0)"
            "(\<Sum>i<?ne. coeffs_p i) = 1" "fst p = (\<Sum>i<?ne. coeffs_p i * vxe i)"
            "snd p = (\<Sum>i<?ne. coeffs_p i * vye i)"
            using hC5_e by (by100 auto)
          \<comment> \<open>C11 at edge jp+2: for k \\<noteq> jp+2, k \\<noteq> si, cross product > 0.\<close>
          have hC11_inst: "\<forall>k<?ne. k \<noteq> jp+2 \<longrightarrow> k \<noteq> ?si_jp \<longrightarrow>
              (vxe ?si_jp-vxe(jp+2))*(vye k-vye(jp+2))-(vye ?si_jp-vye(jp+2))*(vxe k-vxe(jp+2)) > 0"
          proof (intro allI impI)
            fix k assume hk: "k < ?ne" and hk1: "k \<noteq> jp+2" and hk2: "k \<noteq> ?si_jp"
            from hC11_e[rule_format, OF hjp2_lt hk hk1 hk2]
            have "(vxe k-vxe(jp+2))*(vye ?si_jp-vye(jp+2))-(vye k-vye(jp+2))*(vxe ?si_jp-vxe(jp+2)) < 0" .
            \<comment> \<open>Negate: det(B-A, C-A) = -det(C-A, B-A).\<close>
            let ?ax = "vxe(jp+2)" and ?ay = "vye(jp+2)"
            let ?bx = "vxe ?si_jp" and ?by' = "vye ?si_jp"
            let ?kx = "vxe k" and ?ky = "vye k"
            have "(?bx-?ax)*(?ky-?ay)-(?by'-?ay)*(?kx-?ax) =
                -((?kx-?ax)*(?by'-?ay)-(?ky-?ay)*(?bx-?ax))" by (by100 algebra)
            thus "(vxe ?si_jp-vxe(jp+2))*(vye k-vye(jp+2))-(vye ?si_jp-vye(jp+2))*(vxe k-vxe(jp+2)) > 0"
              using \<open>(vxe k-vxe(jp+2))*(vye ?si_jp-vye(jp+2))-(vye k-vye(jp+2))*(vxe ?si_jp-vxe(jp+2)) < 0\<close>
              by linarith
          qed
          \<comment> \<open>Strictness: \\<exists> k with k \\<noteq> jp+2, k \\<noteq> si, coeffs\\_p k > 0 (p not on edge jp+2).\<close>
          have hstrict_k: "\<exists>k<?ne. k \<noteq> jp+2 \<and> k \<noteq> ?si_jp \<and> coeffs_p k > 0"
          proof (rule ccontr)
            assume "\<not>(\<exists>k<?ne. k \<noteq> jp+2 \<and> k \<noteq> ?si_jp \<and> coeffs_p k > 0)"
            hence hall_zero: "\<forall>k<?ne. k \<noteq> jp+2 \<longrightarrow> k \<noteq> ?si_jp \<longrightarrow> coeffs_p k = 0"
              using hcp(1) by (by100 fastforce)
            \<comment> \<open>p = coeffs(jp+2)*v\\_{jp+2} + coeffs(si)*v\\_{si}.\<close>
            have hsi_lt: "?si_jp < ?ne" using hjp2_lt by simp
            have hsi_ne: "?si_jp \<noteq> jp+2"
            proof (cases "Suc(jp+2) < ?ne")
              case True thus ?thesis by simp
            next
              case False
              hence "Suc(jp+2) \<ge> ?ne" by simp
              moreover have "Suc(jp+2) \<le> ?ne" using hjp2_lt by simp
              ultimately have "Suc(jp+2) = ?ne" by simp
              hence "?si_jp = 0" by simp
              moreover have "jp+2 \<ge> 2" by simp
              ultimately show ?thesis by simp
            qed
            have hcoeffs_sum2: "coeffs_p (jp+2) + coeffs_p ?si_jp = 1"
            proof -
              have "(\<Sum>k<?ne. coeffs_p k) = coeffs_p (jp+2) + coeffs_p ?si_jp +
                  (\<Sum>k \<in> {..<?ne} - {jp+2, ?si_jp}. coeffs_p k)"
              proof -
                have s1: "(\<Sum>k<?ne. coeffs_p k) = coeffs_p (jp+2) + (\<Sum>k \<in> {..<?ne} - {jp+2}. coeffs_p k)"
                  using sum.remove[of "{..<?ne}" "jp+2" coeffs_p] hjp2_lt by simp
                have s2: "(\<Sum>k \<in> {..<?ne} - {jp+2}. coeffs_p k) = coeffs_p ?si_jp + (\<Sum>k \<in> {..<?ne} - {jp+2} - {?si_jp}. coeffs_p k)"
                  using sum.remove[of "{..<?ne} - {jp+2}" ?si_jp coeffs_p] hsi_lt hsi_ne by simp
                have "({..<?ne} - {jp+2} - {?si_jp}) = ({..<?ne} - {jp+2, ?si_jp})" by auto
                from s1 s2 this show ?thesis by simp
              qed
              moreover have "(\<Sum>k \<in> {..<?ne} - {jp+2, ?si_jp}. coeffs_p k) = 0"
                by (rule sum.neutral) (use hall_zero in auto)
              ultimately show ?thesis using hcp(2) by simp
            qed
            \<comment> \<open>p = coeffs(jp+2)*v\\_{jp+2} + coeffs(si)*v\\_{si} = edge\\_pt\\_e(jp+2, coeffs(si)).\<close>
            have hpx: "fst p = coeffs_p (jp+2) * vxe(jp+2) + coeffs_p ?si_jp * vxe ?si_jp"
            proof -
              have "fst p = (\<Sum>k<?ne. coeffs_p k * vxe k)" using hcp(3) .
              also have "\<dots> = coeffs_p (jp+2) * vxe(jp+2) + coeffs_p ?si_jp * vxe ?si_jp +
                  (\<Sum>k \<in> {..<?ne} - {jp+2, ?si_jp}. coeffs_p k * vxe k)"
              proof -
                have s1: "(\<Sum>k<?ne. coeffs_p k * vxe k) = coeffs_p (jp+2) * vxe(jp+2) + (\<Sum>k \<in> {..<?ne} - {jp+2}. coeffs_p k * vxe k)"
                  using sum.remove[of "{..<?ne}" "jp+2" "\<lambda>k. coeffs_p k * vxe k"] hjp2_lt by simp
                have s2: "(\<Sum>k \<in> {..<?ne} - {jp+2}. coeffs_p k * vxe k) = coeffs_p ?si_jp * vxe ?si_jp + (\<Sum>k \<in> {..<?ne} - {jp+2} - {?si_jp}. coeffs_p k * vxe k)"
                  using sum.remove[of "{..<?ne} - {jp+2}" ?si_jp "\<lambda>k. coeffs_p k * vxe k"] hsi_lt hsi_ne by simp
                have "({..<?ne} - {jp+2} - {?si_jp}) = ({..<?ne} - {jp+2, ?si_jp})" by auto
                from s1 s2 this show ?thesis by simp
              qed
              also have "(\<Sum>k \<in> {..<?ne} - {jp+2, ?si_jp}. coeffs_p k * vxe k) = 0"
                by (rule sum.neutral) (use hall_zero in auto)
              finally show ?thesis by simp
            qed
            have hpy: "snd p = coeffs_p (jp+2) * vye(jp+2) + coeffs_p ?si_jp * vye ?si_jp"
            proof -
              have "snd p = (\<Sum>k<?ne. coeffs_p k * vye k)" using hcp(4) .
              also have "\<dots> = coeffs_p (jp+2) * vye(jp+2) + coeffs_p ?si_jp * vye ?si_jp +
                  (\<Sum>k \<in> {..<?ne} - {jp+2, ?si_jp}. coeffs_p k * vye k)"
              proof -
                have s1: "(\<Sum>k<?ne. coeffs_p k * vye k) = coeffs_p (jp+2) * vye(jp+2) + (\<Sum>k \<in> {..<?ne} - {jp+2}. coeffs_p k * vye k)"
                  using sum.remove[of "{..<?ne}" "jp+2" "\<lambda>k. coeffs_p k * vye k"] hjp2_lt by simp
                have s2: "(\<Sum>k \<in> {..<?ne} - {jp+2}. coeffs_p k * vye k) = coeffs_p ?si_jp * vye ?si_jp + (\<Sum>k \<in> {..<?ne} - {jp+2} - {?si_jp}. coeffs_p k * vye k)"
                  using sum.remove[of "{..<?ne} - {jp+2}" ?si_jp "\<lambda>k. coeffs_p k * vye k"] hsi_lt hsi_ne by simp
                have "({..<?ne} - {jp+2} - {?si_jp}) = ({..<?ne} - {jp+2, ?si_jp})" by auto
                from s1 s2 this show ?thesis by simp
              qed
              also have "(\<Sum>k \<in> {..<?ne} - {jp+2, ?si_jp}. coeffs_p k * vye k) = 0"
                by (rule sum.neutral) (use hall_zero in auto)
              finally show ?thesis by simp
            qed
            \<comment> \<open>p = (1-t')*v\\_{jp+2} + t'*v\\_{si} where t' = coeffs(si). This is edge\\_pt\\_e(jp+2, t').\<close>
            let ?t' = "coeffs_p ?si_jp"
            have "p = edge_pt_e (jp+2) ?t'"
            proof -
              have "edge_pt_e (jp+2) ?t' = ((1-?t')*vxe(jp+2)+?t'*vxe ?si_jp,
                  (1-?t')*vye(jp+2)+?t'*vye ?si_jp)" unfolding edge_pt_e_def by simp
              also have "(1-?t') = coeffs_p (jp+2)" using hcoeffs_sum2 by linarith
              finally have "edge_pt_e (jp+2) ?t' = (coeffs_p(jp+2)*vxe(jp+2)+?t'*vxe ?si_jp,
                  coeffs_p(jp+2)*vye(jp+2)+?t'*vye ?si_jp)" by simp
              thus ?thesis using hpx hpy by (cases p) simp
            qed
            moreover have "?t' \<in> I_set" using hcp(1)[rule_format, OF hsi_lt] hcoeffs_sum2
              hcp(1)[rule_format, OF hjp2_lt] unfolding top1_unit_interval_def by (by100 auto)
            ultimately show False using hint_p[rule_format, OF hjp2_lt \<open>?t' \<in> I_set\<close>] by simp
          qed
          from convex_combo_edge_cross_strict[OF _ hjp2_lt hcp(1) hcp(2) hC11_inst hstrict_k]
          have "(vxe ?si_jp-vxe(jp+2))*((\<Sum>k<?ne. coeffs_p k * vye k)-vye(jp+2))-
              (vye ?si_jp-vye(jp+2))*((\<Sum>k<?ne. coeffs_p k * vxe k)-vxe(jp+2)) > 0"
            using hlen_ext by linarith
          thus ?thesis using hcp(3) hcp(4) by simp
        qed
        \<comment> \<open>From hedge\\_pos > 0: the centroid weight (1-s\\_p-t\\_p) > 0 in phi\\_fn's formula.
           This means phi\\_fn(p) has a strict centroid contribution.
           The edge cross product of phi\\_fn(p) at any edge of P\\_w is then > 0
           (since centroid is strictly interior), but edge points have edge cross = 0.\<close>
        \<comment> \<open>Get Cramer coordinates for p in sector jp.\<close>
        let ?si_jp2 = "Suc(jp+2) mod ?ne"
        let ?det_jp = "(vxe(jp+2)-vxe 1)*(vye ?si_jp2-vye 1)-(vye(jp+2)-vye 1)*(vxe ?si_jp2-vxe 1)"
        have hdet_jp_pos: "?det_jp > 0" using hdet_pos[rule_format, OF hjp] by simp
        \<comment> \<open>From hedge\\_pos: 1-s-t > 0 via algebraic identity (1-s-t)*det = hedge\\_pos.\<close>
        \<comment> \<open>The centroid weight \\<alpha> = 1-s-t > 0, and phi\\_fn(p) = \\<alpha>*cw + s*u\\_{jp} + t*u\\_{jp+1}.\<close>
        \<comment> \<open>Apply centroid\\_weight\\_not\\_on\\_edge.\<close>
        \<comment> \<open>The full chain: hedge\\_pos > 0 \\<Rightarrow> centroid weight > 0 \\<Rightarrow> not on edge.
           For now: sorry the connection (needs algebraic identity for centroid weight
           + instantiation of centroid\\_weight\\_not\\_on\\_edge).\<close>
        \<comment> \<open>Step 1: phi\\_fn(p) has a known affine form in sector jp.\<close>
        from hphi_affine_on_sector[rule_format, OF hjp hp hin_sec]
        have hphi_form: "phi_fn (fst p, snd p) = (let ex = vxe(jp+2)-vxe 1; ey = vye(jp+2)-vye 1;
            fx = vxe ?si_jp2-vxe 1; fy = vye ?si_jp2-vye 1;
            det = ex*fy-ey*fx; dx = fst p-vxe 1; dy = snd p-vye 1;
            s' = (fy*dx-fx*dy)/det; t' = (ex*dy-ey*dx)/det
        in ((1-s'-t')*?cxw + s'*vxw jp + t'*vxw(Suc jp mod ?nw),
            (1-s'-t')*?cyw + s'*vyw jp + t'*vyw(Suc jp mod ?nw)))" .
        \<comment> \<open>Step 2: compute Cramer coordinates and show centroid weight > 0.\<close>
        define ex_p where "ex_p = vxe(jp+2)-vxe 1"
        define ey_p where "ey_p = vye(jp+2)-vye 1"
        define fx_p where "fx_p = vxe ?si_jp2-vxe 1"
        define fy_p where "fy_p = vye ?si_jp2-vye 1"
        define dx_p where "dx_p = fst p-vxe 1"
        define dy_p where "dy_p = snd p-vye 1"
        define det_p where "det_p = ex_p*fy_p-ey_p*fx_p"
        define s_p where "s_p = (fy_p*dx_p-fx_p*dy_p)/det_p"
        define t_p where "t_p = (ex_p*dy_p-ey_p*dx_p)/det_p"
        have hdet_p_pos: "det_p > 0" using hdet_jp_pos
          unfolding det_p_def ex_p_def ey_p_def fx_p_def fy_p_def by simp
        have hdet_p_ne: "det_p \<noteq> 0" using hdet_p_pos by linarith
        \<comment> \<open>hedge\\_pos = (1-s\\_p-t\\_p)*det\\_p (algebraic identity, proved for target fan in hec\\_eq).\<close>
        \<comment> \<open>s\\_p*det\\_p = fy\\_p*dx\\_p-fx\\_p*dy\\_p, t\\_p*det\\_p = ex\\_p*dy\\_p-ey\\_p*dx\\_p.\<close>
        have hs_p_mul: "s_p*det_p = fy_p*dx_p-fx_p*dy_p"
          unfolding s_p_def using hdet_p_ne by simp
        have ht_p_mul: "t_p*det_p = ex_p*dy_p-ey_p*dx_p"
          unfolding t_p_def using hdet_p_ne by simp
        have hweight_identity: "(1-s_p-t_p)*det_p = (fx_p-ex_p)*(dy_p-ey_p) - (fy_p-ey_p)*(dx_p-ex_p)"
        proof -
          have h1: "(1-s_p-t_p)*det_p = det_p - s_p*det_p - t_p*det_p" by (by100 algebra)
          have h2: "det_p - (fy_p*dx_p-fx_p*dy_p) - (ex_p*dy_p-ey_p*dx_p)
              = (fx_p-ex_p)*(dy_p-ey_p) - (fy_p-ey_p)*(dx_p-ex_p)"
            unfolding det_p_def by (by100 algebra)
          from h1 hs_p_mul ht_p_mul h2 show ?thesis by linarith
        qed
        \<comment> \<open>RHS = hedge\\_pos (change of basis).\<close>
        have hRHS_eq: "(fx_p-ex_p)*(dy_p-ey_p) - (fy_p-ey_p)*(dx_p-ex_p)
            = (vxe ?si_jp2 - vxe(jp+2))*(snd p - vye(jp+2)) - (vye ?si_jp2 - vye(jp+2))*(fst p - vxe(jp+2))"
          unfolding fx_p_def ex_p_def fy_p_def ey_p_def dx_p_def dy_p_def by (by100 algebra)
        have halpha_pos: "1-s_p-t_p > 0"
        proof -
          from hweight_identity hRHS_eq hedge_pos
          have hprod_pos: "(1-s_p-t_p)*det_p > 0" by linarith
          show ?thesis
          proof (rule ccontr)
            assume "\<not> 1 - s_p - t_p > 0"
            hence "1 - s_p - t_p \<le> 0" by linarith
            hence "(1-s_p-t_p)*det_p \<le> 0"
              using hdet_p_pos mult_nonpos_nonneg[of "1-s_p-t_p" det_p] by linarith
            with hprod_pos show False by linarith
          qed
        qed
        \<comment> \<open>Step 3: phi\\_fn(p) = (1-s\\_p-t\\_p)*cw + s\\_p*u\\_{jp} + t\\_p*u\\_{jp+1}.\<close>
        have hphi_x: "fst (phi_fn p) = (1-s_p-t_p)*?cxw + s_p*vxw jp + t_p*vxw(Suc jp mod ?nw)"
          using hphi_form unfolding Let_def s_p_def t_p_def det_p_def
            ex_p_def ey_p_def fx_p_def fy_p_def dx_p_def dy_p_def by simp
        have hphi_y: "snd (phi_fn p) = (1-s_p-t_p)*?cyw + s_p*vyw jp + t_p*vyw(Suc jp mod ?nw)"
          using hphi_form unfolding Let_def s_p_def t_p_def det_p_def
            ex_p_def ey_p_def fx_p_def fy_p_def dx_p_def dy_p_def by simp
        \<comment> \<open>Step 4: s\\_p \\<ge> 0 and t\\_p \\<ge> 0 (from in\\_sector + Cramer).\<close>
        \<comment> \<open>s\\_p \\<ge> 0 from cross\\_v1(si, p) \\<le> 0: s\\_p*det = -(cross\\_v1(si,p)) \\<ge> 0.\<close>
        have hs_p_ge: "s_p \<ge> 0"
        proof -
          from hin_sec have "cross_v1 ?si_jp2 p \<le> 0" unfolding in_sector_def by auto
          have "fy_p*dx_p - fx_p*dy_p = -(cross_v1 ?si_jp2 p)"
            unfolding cross_v1_def fx_p_def fy_p_def dx_p_def dy_p_def by (by100 algebra)
          hence hsp_det: "s_p*det_p \<ge> 0" using hs_p_mul \<open>cross_v1 ?si_jp2 p \<le> 0\<close> by linarith
          show ?thesis
          proof (rule ccontr)
            assume "\<not> s_p \<ge> 0"
            hence "s_p < 0" by linarith
            hence "s_p*det_p < 0" using hdet_p_pos mult_neg_pos by (by100 blast)
            with hsp_det show False by linarith
          qed
        qed
        have ht_p_ge: "t_p \<ge> 0"
        proof -
          from hin_sec have "cross_v1 (jp+2) p \<ge> 0" unfolding in_sector_def by auto
          have "ex_p*dy_p - ey_p*dx_p = cross_v1 (jp+2) p"
            unfolding cross_v1_def ex_p_def ey_p_def dx_p_def dy_p_def by (by100 simp)
          hence htp_det: "t_p*det_p \<ge> 0" using ht_p_mul \<open>cross_v1 (jp+2) p \<ge> 0\<close> by linarith
          show ?thesis
          proof (rule ccontr)
            assume "\<not> t_p \<ge> 0"
            hence "t_p < 0" by linarith
            hence "t_p*det_p < 0" using hdet_p_pos mult_neg_pos by (by100 blast)
            with htp_det show False by linarith
          qed
        qed
        have habg: "(1-s_p-t_p) + s_p + t_p = 1" by linarith
        \<comment> \<open>Step 5: edge point has specific form.\<close>
        have hedge_x: "fst (edge_pt_w j s) = (1-s)*vxw j + s*vxw(Suc j mod ?nw)"
          unfolding edge_pt_w_def by simp
        have hedge_y: "snd (edge_pt_w j s) = (1-s)*vyw j + s*vyw(Suc j mod ?nw)"
          unfolding edge_pt_w_def by simp
        \<comment> \<open>Step 6: expand hC10\\_w and hC11\\_w to match centroid\\_weight\\_not\\_on\\_edge format.\<close>
        have hC10_expanded: "\<forall>i<?nw. (vxw i - ?cxw) * (vyw(Suc i mod ?nw) - ?cyw) -
            (vyw i - ?cyw) * (vxw(Suc i mod ?nw) - ?cxw) > 0"
          using hC10_w by (by100 simp)
        from centroid_weight_not_on_edge[OF hlen hC10_expanded hC11_w hjp halpha_pos hs_p_ge ht_p_ge habg
            hphi_x hphi_y hj hedge_x hedge_y]
        show "phi_fn p \<noteq> edge_pt_w j s" .
      qed
      have prop12: "\<forall>t\<in>I_set. \<forall>p\<in>P_e.
          (\<forall>i<?ne. \<forall>s\<in>I_set. p \<noteq> edge_pt_e i s) \<longrightarrow>
          phi_fn (edge_pt_e 0 t) \<noteq> phi_fn p"
      proof (intro ballI impI)
        fix t p assume ht: "t \<in> I_set" and hp: "p \<in> P_e"
            and hint_p: "\<forall>i<?ne. \<forall>s\<in>I_set. p \<noteq> edge_pt_e i s"
        have h1_lt: "1 < ?ne" using hlen_ext by linarith
        have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        have hp_ne_v1: "p \<noteq> (vxe 1, vye 1)"
        proof
          assume "p = (vxe 1, vye 1)"
          hence "p = edge_pt_e 1 0" unfolding edge_pt_e_def by (by100 simp)
          with hint_p[rule_format, OF h1_lt h0_I] show False by simp
        qed
        from hfan_cover[rule_format, OF hp] hp_ne_v1
        obtain jp where hjp: "jp < ?nw" and hin_sec: "in_sector jp p" by blast
        \<comment> \<open>PROOF via target fan sector analysis:
           1. For jp \\<notin> {0, nw-1}: spur\\_arc\\_target\\_sector shows spur arc NOT in sector jp.
              phi\\_fn(p) IS in sector jp (affine map). So \\<noteq>.
           2. For jp = 0: spur\\_arc\\_match\\_forces\\_edge j=0 case: t\\_p=0 \\<to> p on edge \\<to> contradiction.
           3. For jp = nw-1: j+1=0 case: s\\_p=0 \\<to> p on edge \\<to> contradiction.\<close>
        \<comment> \<open>Expand hC10\\_w for use with spur\\_arc\\_target\\_sector.\<close>
        have hC10_expanded: "\<forall>i<?nw. (vxw i - ?cxw) * (vyw(Suc i mod ?nw) - ?cyw) -
            (vyw i - ?cyw) * (vxw(Suc i mod ?nw) - ?cxw) > 0"
          using hC10_w by (by100 simp)
        show "phi_fn (edge_pt_e 0 t) \<noteq> phi_fn p"
        proof
          assume heq: "phi_fn (edge_pt_e 0 t) = phi_fn p"
          \<comment> \<open>STRUCTURED PROOF: case jp = 0 or nw-1: affine independence from C10 forces
             Cramer coordinate zero, making p an edge point (contradiction with hint\\_p).
             Case jp \\<notin> {0, nw-1}: spur\\_arc\\_target\\_sector gives cross product contradiction.\<close>
          show False
          proof (cases "jp = 0")
            case True
            \<comment> \<open>Use prop11 infrastructure: centroid\\_weight\\_not\\_on\\_edge already established that
               phi\\_fn(p) = (1-s-t)*cw + s*u\\_jp + t*u\\_{jp+1} with the Cramer coords.
               For jp=0: matching with spur forces t=0 via affine independence.\<close>
            \<comment> \<open>We use the prop11-style analysis already done for centroid weight.\<close>
            let ?si_jp2 = "Suc(jp+2) mod ?ne"
            from hphi_affine_on_sector[rule_format, OF hjp hp hin_sec]
            have hphi_form12: "phi_fn (fst p, snd p) = (let ex = vxe(jp+2)-vxe 1; ey = vye(jp+2)-vye 1;
                fx = vxe ?si_jp2-vxe 1; fy = vye ?si_jp2-vye 1;
                det = ex*fy-ey*fx; dx = fst p-vxe 1; dy = snd p-vye 1;
                s' = (fy*dx-fx*dy)/det; t' = (ex*dy-ey*dx)/det
            in ((1-s'-t')*?cxw + s'*vxw jp + t'*vxw(Suc jp mod ?nw),
                (1-s'-t')*?cyw + s'*vyw jp + t'*vyw(Suc jp mod ?nw)))" .
            define ex_p where "ex_p = vxe(jp+2)-vxe 1"
            define ey_p where "ey_p = vye(jp+2)-vye 1"
            define fx_p where "fx_p = vxe ?si_jp2-vxe 1"
            define fy_p where "fy_p = vye ?si_jp2-vye 1"
            define dx_p where "dx_p = fst p-vxe 1"
            define dy_p where "dy_p = snd p-vye 1"
            define det_p where "det_p = ex_p*fy_p-ey_p*fx_p"
            define sp12 where "sp12 = (fy_p*dx_p-fx_p*dy_p)/det_p"
            define tp12 where "tp12 = (ex_p*dy_p-ey_p*dx_p)/det_p"
            have hphi_x12: "fst (phi_fn p) = (1-sp12-tp12)*?cxw + sp12*vxw jp + tp12*vxw(Suc jp mod ?nw)"
              using hphi_form12 unfolding Let_def sp12_def tp12_def det_p_def
                ex_p_def ey_p_def fx_p_def fy_p_def dx_p_def dy_p_def by simp
            have hphi_y12: "snd (phi_fn p) = (1-sp12-tp12)*?cyw + sp12*vyw jp + tp12*vyw(Suc jp mod ?nw)"
              using hphi_form12 unfolding Let_def sp12_def tp12_def det_p_def
                ex_p_def ey_p_def fx_p_def fy_p_def dx_p_def dy_p_def by simp
            have h0_lt: "(0::nat) < ?nw" using hnw_pos by linarith
            have hspur12: "phi_fn (edge_pt_e 0 t) = ((1-t)*vxw 0 + t*?cxw, (1-t)*vyw 0 + t*?cyw)"
              using hphi_on_spur0[rule_format, OF ht] .
            have hphi_eq_spur: "phi_fn p = ((1-t)*vxw 0 + t*?cxw, (1-t)*vyw 0 + t*?cyw)"
              using heq hspur12 by simp
            have hmx0: "(1-sp12-tp12)*?cxw + sp12*vxw 0 + tp12*vxw(Suc 0 mod ?nw) = (1-t)*vxw 0 + t*?cxw"
            proof -
              have "fst (phi_fn p) = (1-t)*vxw 0 + t*?cxw" using hphi_eq_spur by simp
              thus ?thesis using hphi_x12 True by simp
            qed
            have hmy0: "(1-sp12-tp12)*?cyw + sp12*vyw 0 + tp12*vyw(Suc 0 mod ?nw) = (1-t)*vyw 0 + t*?cyw"
            proof -
              have "snd (phi_fn p) = (1-t)*vyw 0 + t*?cyw" using hphi_eq_spur by simp
              thus ?thesis using hphi_y12 True by simp
            qed
            from spur_match_sector0_forces_t_zero[OF hlen hC10_expanded[rule_format, OF h0_lt] hmx0 hmy0]
            have htp0: "tp12 = 0" .
            \<comment> \<open>Cramer inverse + edge derivation + I\\_set membership.\<close>
            have hdet_p_ne: "det_p \<noteq> 0"
              using hdet_pos[rule_format, OF hjp] unfolding det_p_def ex_p_def ey_p_def fx_p_def fy_p_def
                Let_def by linarith
            have hsp_mul: "sp12*det_p = fy_p*dx_p - fx_p*dy_p" unfolding sp12_def using hdet_p_ne by simp
            have htp_mul: "tp12*det_p = ex_p*dy_p - ey_p*dx_p" unfolding tp12_def using hdet_p_ne by simp
            have hdet_eq: "det_p = ex_p*fy_p - ey_p*fx_p" unfolding det_p_def by simp
            from cramer_inverse_tp_zero[OF hsp_mul htp_mul htp0 hdet_p_ne hdet_eq]
            have hdx: "dx_p = sp12*ex_p" and hdy: "dy_p = sp12*ey_p" by auto
            \<comment> \<open>Derive p = edge\\_pt\\_e(1, sp12): need ex\\_p = vxe(Suc 1 mod ne)-vxe 1.\<close>
            have hne_gt: "?ne > 2" using hlen hne_eq by (by100 linarith)
            have hsuc1_jp2: "Suc 1 mod ?ne = jp + 2"
            proof -
              have "jp + 2 < ?ne" using hjp hne_eq by (by100 linarith)
              moreover have "Suc 1 = jp + 2" using True by (by100 arith)
              ultimately show ?thesis by (by100 simp)
            qed
            hence hex_match: "ex_p = vxe(Suc 1 mod ?ne) - vxe 1"
              unfolding ex_p_def by simp
            have hey_match: "ey_p = vye(Suc 1 mod ?ne) - vye 1"
              using hsuc1_jp2 unfolding ey_p_def by simp
            \<comment> \<open>p = (vxe 1 + sp12*ex\\_p, vye 1 + sp12*ey\\_p) from hdx, hdy.\<close>
            have h_px: "fst p = vxe 1 + sp12*ex_p" using hdx unfolding dx_p_def by linarith
            have h_py: "snd p = vye 1 + sp12*ey_p" using hdy unfolding dy_p_def by linarith
            \<comment> \<open>edge\\_pt\\_e 1 sp12 = ((1-sp12)*vxe 1 + sp12*vxe(Suc 1 mod ne), ...).\<close>
            have hedge: "edge_pt_e 1 sp12 = ((1-sp12)*vxe 1 + sp12*vxe(Suc 1 mod ?ne),
                (1-sp12)*vye 1 + sp12*vye(Suc 1 mod ?ne))"
              unfolding edge_pt_e_def by (by100 simp)
            \<comment> \<open>Show fst(edge) = fst p and snd(edge) = snd p.\<close>
            have hp_edge: "p = edge_pt_e 1 sp12"
            proof -
              \<comment> \<open>Need: (1-sp12)*vxe 1 + sp12*vxe(Suc 1 mod ne) = vxe 1 + sp12*ex\\_p.
                 From hex\\_match: vxe(Suc 1 mod ne) = vxe 1 + ex\\_p.
                 (1-sp12)*vxe 1 + sp12*(vxe 1+ex\\_p) = vxe 1 + sp12*ex\\_p. Ring algebra.\<close>
              define vx2 where "vx2 = vxe(Suc 1 mod ?ne)"
              define vy2 where "vy2 = vye(Suc 1 mod ?ne)"
              have "vx2 = vxe 1 + ex_p" unfolding vx2_def using hex_match by linarith
              have "vy2 = vye 1 + ey_p" unfolding vy2_def using hey_match by linarith
              \<comment> \<open>fst edge = (1-sp12)*vxe 1 + sp12*vx2 = vxe 1-sp12*vxe 1+sp12*(vxe 1+ex\\_p)
                 = vxe 1 + sp12*ex\\_p.\<close>
              define sp_v1 where "sp_v1 = sp12*vxe 1"
              define sp_vx2 where "sp_vx2 = sp12*vx2"
              have "sp_vx2 = sp_v1 + sp12*ex_p"
                unfolding sp_vx2_def sp_v1_def \<open>vx2 = vxe 1 + ex_p\<close> by (by100 algebra)
              have hfst_e: "fst (edge_pt_e 1 sp12) = (1-sp12)*vxe 1 + sp12*vx2"
                using hedge unfolding vx2_def by simp
              define omsv1 where "omsv1 = (1-sp12)*vxe 1"
              have "omsv1 = vxe 1 - sp_v1" unfolding omsv1_def sp_v1_def by (by100 algebra)
              have "fst (edge_pt_e 1 sp12) = omsv1 + sp_vx2"
                using hfst_e unfolding omsv1_def sp_vx2_def vx2_def by simp
              hence "fst (edge_pt_e 1 sp12) = vxe 1 - sp_v1 + sp_vx2"
                using \<open>omsv1 = vxe 1 - sp_v1\<close> by linarith
              hence hfst_eq: "fst (edge_pt_e 1 sp12) = vxe 1 + sp12*ex_p"
                using \<open>sp_vx2 = sp_v1 + sp12*ex_p\<close> unfolding sp_v1_def by linarith
              define sp_v1y where "sp_v1y = sp12*vye 1"
              define sp_vy2 where "sp_vy2 = sp12*vy2"
              have "sp_vy2 = sp_v1y + sp12*ey_p"
                unfolding sp_vy2_def sp_v1y_def \<open>vy2 = vye 1 + ey_p\<close> by (by100 algebra)
              have hsnd_e: "snd (edge_pt_e 1 sp12) = (1-sp12)*vye 1 + sp12*vy2"
                using hedge unfolding vy2_def by simp
              define omsv1y where "omsv1y = (1-sp12)*vye 1"
              have "omsv1y = vye 1 - sp_v1y" unfolding omsv1y_def sp_v1y_def by (by100 algebra)
              have "snd (edge_pt_e 1 sp12) = omsv1y + sp_vy2"
                using hsnd_e unfolding omsv1y_def sp_vy2_def vy2_def by simp
              hence "snd (edge_pt_e 1 sp12) = vye 1 - sp_v1y + sp_vy2"
                using \<open>omsv1y = vye 1 - sp_v1y\<close> by linarith
              hence hsnd_eq: "snd (edge_pt_e 1 sp12) = vye 1 + sp12*ey_p"
                using \<open>sp_vy2 = sp_v1y + sp12*ey_p\<close> unfolding sp_v1y_def by linarith
              from hfst_eq hsnd_eq h_px h_py show ?thesis
                by (cases "edge_pt_e 1 sp12", cases p) simp
            qed
            \<comment> \<open>sp12 \\<in> I\\_set: derive sp12 = 1-t from matching.\<close>
            have hsp_eq: "sp12 = 1 - t"
            proof -
              from hmx0 htp0 have hmx_s: "(1-sp12)*?cxw + sp12*vxw 0 = (1-t)*vxw 0 + t*?cxw" by simp
              from hmy0 htp0 have hmy_s: "(1-sp12)*?cyw + sp12*vyw 0 = (1-t)*vyw 0 + t*?cyw" by simp
              \<comment> \<open>Ring distribute: (1-sp12)*cxw = cxw - sp12*cxw, etc.\<close>
              define sp_cx where "sp_cx = sp12*?cxw"
              define t_cx where "t_cx = t*?cxw"
              define sp_vx where "sp_vx = sp12*vxw 0"
              define t_vx where "t_vx = t*vxw 0"
              define oms_cx where "oms_cx = (1-sp12)*?cxw"
              define omt_vx where "omt_vx = (1-t)*vxw 0"
              have "oms_cx = ?cxw - sp_cx" unfolding oms_cx_def sp_cx_def by (by100 algebra)
              have "omt_vx = vxw 0 - t_vx" unfolding omt_vx_def t_vx_def by (by100 algebra)
              from hmx_s have "oms_cx + sp_vx = omt_vx + t_cx"
                unfolding oms_cx_def sp_vx_def omt_vx_def t_cx_def by simp
              hence "?cxw - sp_cx + sp_vx = vxw 0 - t_vx + t_cx"
                using \<open>oms_cx = ?cxw - sp_cx\<close> \<open>omt_vx = vxw 0 - t_vx\<close> by linarith
              hence hx_lin: "sp_vx - sp_cx = (vxw 0 - ?cxw) + (t_cx - t_vx)" by linarith
              \<comment> \<open>sp\\_vx - sp\\_cx = sp12*(vxw 0-cxw), t\\_cx-t\\_vx = t*(cxw-vxw 0) = -(t*(vxw 0-cxw)).\<close>
              define wx where "wx = vxw 0 - ?cxw"
              have "sp_vx - sp_cx = sp12*wx" unfolding sp_vx_def sp_cx_def wx_def by (by100 algebra)
              have "t_cx - t_vx = -(t*wx)" unfolding t_cx_def t_vx_def wx_def by (by100 algebra)
              have hwx_eq: "vxw 0 - ?cxw = wx" unfolding wx_def by simp
              from hx_lin have "sp12*wx = wx - t*wx"
                using \<open>sp_vx - sp_cx = sp12*wx\<close> \<open>t_cx - t_vx = -(t*wx)\<close> hwx_eq by linarith
              hence hsp_wx: "sp12*wx = (1-t)*wx" by (by100 algebra)
              \<comment> \<open>Similarly for y.\<close>
              define wy where "wy = vyw 0 - ?cyw"
              have hsp_wy: "sp12*wy = (1-t)*wy"
              proof -
                define sp_cy where "sp_cy = sp12*?cyw"
                define t_cy where "t_cy = t*?cyw"
                define sp_vy where "sp_vy = sp12*vyw 0"
                define t_vy where "t_vy = t*vyw 0"
                define oms_cy where "oms_cy = (1-sp12)*?cyw"
                define omt_vy where "omt_vy = (1-t)*vyw 0"
                have "oms_cy = ?cyw - sp_cy" unfolding oms_cy_def sp_cy_def by (by100 algebra)
                have "omt_vy = vyw 0 - t_vy" unfolding omt_vy_def t_vy_def by (by100 algebra)
                from hmy_s have "oms_cy + sp_vy = omt_vy + t_cy"
                  unfolding oms_cy_def sp_vy_def omt_vy_def t_cy_def by simp
                hence "?cyw - sp_cy + sp_vy = vyw 0 - t_vy + t_cy"
                  using \<open>oms_cy = ?cyw - sp_cy\<close> \<open>omt_vy = vyw 0 - t_vy\<close> by linarith
                hence hy_lin: "sp_vy - sp_cy = (vyw 0 - ?cyw) + (t_cy - t_vy)" by linarith
                have "sp_vy - sp_cy = sp12*wy" unfolding sp_vy_def sp_cy_def wy_def by (by100 algebra)
                have "t_cy - t_vy = -(t*wy)" unfolding t_cy_def t_vy_def wy_def by (by100 algebra)
                have hwy_eq: "vyw 0 - ?cyw = wy" unfolding wy_def by simp
                from hy_lin have "sp12*wy = wy - t*wy"
                  using \<open>sp_vy - sp_cy = sp12*wy\<close> \<open>t_cy - t_vy = -(t*wy)\<close> hwy_eq by linarith
                thus ?thesis by (by100 algebra)
              qed
              \<comment> \<open>From sp12*wx = (1-t)*wx: if wx \\<noteq> 0 then sp12=1-t. Else use wy. C10 ensures one \\<noteq> 0.\<close>
              show ?thesis
              proof (cases "wx \<noteq> 0")
                case True from hsp_wx True show ?thesis by simp
              next
                case False hence "wx = 0" by simp
                show ?thesis
                proof (cases "wy \<noteq> 0")
                  case True from hsp_wy True show ?thesis by simp
                next
                  case False hence "wy = 0" by simp
                  \<comment> \<open>wx=wy=0 means vxw 0=cxw and vyw 0=cyw. C10(0) gives contradiction.\<close>
                  have "vxw 0 = ?cxw" using \<open>wx = 0\<close> unfolding wx_def by simp
                  have "vyw 0 = ?cyw" using \<open>wy = 0\<close> unfolding wy_def by simp
                  have h0_lt: "(0::nat) < ?nw" using hnw_pos by linarith
                  from hC10_expanded[rule_format, OF h0_lt]
                  have "(vxw 0-?cxw)*(vyw(Suc 0 mod ?nw)-?cyw)-(vyw 0-?cyw)*(vxw(Suc 0 mod ?nw)-?cxw) > 0" .
                  with \<open>vxw 0 = ?cxw\<close> \<open>vyw 0 = ?cyw\<close> show ?thesis by simp
                qed
              qed
            qed
            have "sp12 \<in> I_set" using hsp_eq ht
              unfolding top1_unit_interval_def by (by100 auto)
            have "1 < ?ne" using hlen_ext by (by100 linarith)
            from hint_p[rule_format, OF this \<open>sp12 \<in> I_set\<close>] hp_edge show False by (by100 simp)
          next
            case False note hjp_ne0 = this
            show False
            proof (cases "Suc jp mod ?nw = 0")
              case True
              \<comment> \<open>jp=nw-1 (Suc jp mod nw = 0): symmetric to jp=0 with sp12=0.\<close>
              \<comment> \<open>Reuse the Cramer decomposition from prop12 context.\<close>
              have hphi_eq_spur: "phi_fn p = ((1-t)*vxw 0 + t*?cxw, (1-t)*vyw 0 + t*?cyw)"
                using heq hphi_on_spur0[rule_format, OF ht] by simp
              \<comment> \<open>Need matching equations for sector jp with Suc jp mod nw = 0.\<close>
              let ?si_jp2' = "Suc(jp+2) mod ?ne"
              from hphi_affine_on_sector[rule_format, OF hjp hp hin_sec]
              have hphi_form': "phi_fn (fst p, snd p) = (let ex = vxe(jp+2)-vxe 1; ey = vye(jp+2)-vye 1;
                  fx = vxe ?si_jp2'-vxe 1; fy = vye ?si_jp2'-vye 1;
                  det = ex*fy-ey*fx; dx = fst p-vxe 1; dy = snd p-vye 1;
                  s' = (fy*dx-fx*dy)/det; t' = (ex*dy-ey*dx)/det
              in ((1-s'-t')*?cxw + s'*vxw jp + t'*vxw(Suc jp mod ?nw),
                  (1-s'-t')*?cyw + s'*vyw jp + t'*vyw(Suc jp mod ?nw)))" .
              define ex_p' where "ex_p' = vxe(jp+2)-vxe 1"
              define ey_p' where "ey_p' = vye(jp+2)-vye 1"
              define fx_p' where "fx_p' = vxe ?si_jp2'-vxe 1"
              define fy_p' where "fy_p' = vye ?si_jp2'-vye 1"
              define dx_p' where "dx_p' = fst p-vxe 1"
              define dy_p' where "dy_p' = snd p-vye 1"
              define det_p' where "det_p' = ex_p'*fy_p'-ey_p'*fx_p'"
              define sp12' where "sp12' = (fy_p'*dx_p'-fx_p'*dy_p')/det_p'"
              define tp12' where "tp12' = (ex_p'*dy_p'-ey_p'*dx_p')/det_p'"
              have hphi_x': "fst (phi_fn p) = (1-sp12'-tp12')*?cxw + sp12'*vxw jp + tp12'*vxw(Suc jp mod ?nw)"
                using hphi_form' unfolding Let_def sp12'_def tp12'_def det_p'_def
                  ex_p'_def ey_p'_def fx_p'_def fy_p'_def dx_p'_def dy_p'_def by simp
              have hphi_y': "snd (phi_fn p) = (1-sp12'-tp12')*?cyw + sp12'*vyw jp + tp12'*vyw(Suc jp mod ?nw)"
                using hphi_form' unfolding Let_def sp12'_def tp12'_def det_p'_def
                  ex_p'_def ey_p'_def fx_p'_def fy_p'_def dx_p'_def dy_p'_def by simp
              \<comment> \<open>Matching equations in un-substituted form (Suc jp mod nw, not 0).\<close>
              have hmx': "(1-sp12'-tp12')*?cxw + sp12'*vxw jp + tp12'*vxw(Suc jp mod ?nw) = (1-t)*vxw 0 + t*?cxw"
              proof -
                have "fst (phi_fn p) = (1-t)*vxw 0 + t*?cxw" using hphi_eq_spur by simp
                thus ?thesis using hphi_x' by (cases p) simp
              qed
              have hmy': "(1-sp12'-tp12')*?cyw + sp12'*vyw jp + tp12'*vyw(Suc jp mod ?nw) = (1-t)*vyw 0 + t*?cyw"
              proof -
                have "snd (phi_fn p) = (1-t)*vyw 0 + t*?cyw" using hphi_eq_spur by simp
                thus ?thesis using hphi_y' by (cases p) simp
              qed
              \<comment> \<open>Apply spur\\_match\\_sector\\_last\\_forces\\_s\\_zero: sp12' = 0.\<close>
              from spur_match_sector_last_forces_s_zero[OF hlen hjp True hC10_expanded[rule_format, OF hjp]
                  hmx' hmy']
              have hsp0: "sp12' = 0" .
              \<comment> \<open>sp12'=0: Cramer inverse gives dx=tp12'*fx, dy=tp12'*fy.\<close>
              have hdet_p_ne': "det_p' \<noteq> 0"
                using hdet_pos[rule_format, OF hjp] unfolding det_p'_def ex_p'_def ey_p'_def fx_p'_def fy_p'_def
                  Let_def by linarith
              have hsp_mul': "sp12'*det_p' = fy_p'*dx_p' - fx_p'*dy_p'" unfolding sp12'_def using hdet_p_ne' by simp
              have htp_mul': "tp12'*det_p' = ex_p'*dy_p' - ey_p'*dx_p'" unfolding tp12'_def using hdet_p_ne' by simp
              have hdet_eq': "det_p' = ex_p'*fy_p' - ey_p'*fx_p'" unfolding det_p'_def by simp
              from cramer_inverse_sp_zero[OF hsp_mul' htp_mul' hsp0 hdet_p_ne' hdet_eq']
              have hdx': "dx_p' = tp12'*fx_p'" and hdy': "dy_p' = tp12'*fy_p'" by auto
              \<comment> \<open>For jp=nw-1: si\\_jp2' = Suc(jp+2) mod ne = 0. So fx\\_p' = vxe 0-vxe 1.\<close>
              have hsi_zero: "?si_jp2' = 0"
              proof -
                from True hjp have "jp = ?nw - 1"
                proof -
                  from True have "Suc jp mod ?nw = 0" .
                  hence "?nw dvd Suc jp" by (metis dvd_eq_mod_eq_0)
                  with hjp have "Suc jp = ?nw"
                  proof -
                    from hjp have "Suc jp \<le> ?nw" by (by100 simp)
                    from \<open>?nw dvd Suc jp\<close> have "Suc jp \<ge> 1" by (by100 simp)
                    from \<open>?nw dvd Suc jp\<close> \<open>Suc jp \<le> ?nw\<close> show ?thesis
                      using dvd_imp_le[of ?nw "Suc jp"] by (by100 linarith)
                  qed
                  thus "jp = ?nw - 1" by (by100 arith)
                qed
                hence "jp + 2 = ?nw + 1" using hnw_pos by (by100 arith)
                hence "Suc(jp + 2) = ?nw + 2" by (by100 arith)
                also have "?nw + 2 = ?ne" using hne_eq by (by100 simp)
                finally have "Suc(jp+2) = ?ne" .
                thus ?thesis by (by100 simp)
              qed
              hence hfx_eq: "fx_p' = vxe 0 - vxe 1" "fy_p' = vye 0 - vye 1"
                unfolding fx_p'_def fy_p'_def by auto
              have h_px': "fst p = vxe 1 + tp12'*fx_p'" using hdx' unfolding dx_p'_def by linarith
              have h_py': "snd p = vye 1 + tp12'*fy_p'" using hdy' unfolding dy_p'_def by linarith
              \<comment> \<open>edge\\_pt\\_e 0 (1-tp12') = ((1-(1-tp12'))*vxe 0 + (1-tp12')*vxe 1, ...) = p.\<close>
              have hsuc0: "Suc 0 mod ?ne = 1" using hlen hne_eq by (by100 simp)
              have hedge0: "edge_pt_e 0 (1-tp12') = (tp12'*vxe 0 + (1-tp12')*vxe 1,
                  tp12'*vye 0 + (1-tp12')*vye 1)"
                unfolding edge_pt_e_def using hsuc0 by (by100 simp)
              have hp_edge': "p = edge_pt_e 0 (1-tp12')"
              proof -
                \<comment> \<open>fst p = vxe 1 + tp12'*(vxe 0-vxe 1) = (1-tp12')*vxe 1 + tp12'*vxe 0.\<close>
                define tp_fx where "tp_fx = tp12'*fx_p'"
                define tp_vx0 where "tp_vx0 = tp12'*vxe 0"
                define tp_vx1 where "tp_vx1 = tp12'*vxe 1"
                have "tp_fx = tp_vx0 - tp_vx1" unfolding tp_fx_def tp_vx0_def tp_vx1_def
                  hfx_eq by (by100 algebra)
                have "fst p = vxe 1 + tp_fx" using h_px' unfolding tp_fx_def by simp
                hence "fst p = vxe 1 + tp_vx0 - tp_vx1"
                  using \<open>tp_fx = tp_vx0 - tp_vx1\<close> by linarith
                define omt_v1 where "omt_v1 = (1-tp12')*vxe 1"
                have "omt_v1 = vxe 1 - tp_vx1" unfolding omt_v1_def tp_vx1_def by (by100 algebra)
                hence hfst': "fst p = tp_vx0 + omt_v1"
                  using \<open>fst p = vxe 1 + tp_vx0 - tp_vx1\<close> by linarith
                define tp_fy where "tp_fy = tp12'*fy_p'"
                define tp_vy0 where "tp_vy0 = tp12'*vye 0"
                define tp_vy1 where "tp_vy1 = tp12'*vye 1"
                have "tp_fy = tp_vy0 - tp_vy1" unfolding tp_fy_def tp_vy0_def tp_vy1_def
                  using hfx_eq by (by100 algebra)
                have "snd p = vye 1 + tp_fy" using h_py' unfolding tp_fy_def by simp
                hence "snd p = vye 1 + tp_vy0 - tp_vy1"
                  using \<open>tp_fy = tp_vy0 - tp_vy1\<close> by linarith
                define omt_v1y where "omt_v1y = (1-tp12')*vye 1"
                have "omt_v1y = vye 1 - tp_vy1" unfolding omt_v1y_def tp_vy1_def by (by100 algebra)
                hence hsnd': "snd p = tp_vy0 + omt_v1y"
                  using \<open>snd p = vye 1 + tp_vy0 - tp_vy1\<close> by linarith
                from hfst' hsnd' hedge0 show ?thesis
                  unfolding tp_vx0_def tp_vy0_def omt_v1_def omt_v1y_def
                  by (cases "edge_pt_e 0 (1-tp12')", cases p) simp
              qed
              \<comment> \<open>(1-tp12') \\<in> I\\_set: derive tp12' = 1-t.\<close>
              have htp_eq': "tp12' = 1 - t"
              proof -
                \<comment> \<open>From hmx' with sp12'=0 and Suc jp mod nw = 0: (1-tp12')*cxw + tp12'*vxw 0 = (1-t)*vxw 0+t*cxw.\<close>
                from hmx' hsp0 True have "(1-tp12')*?cxw + tp12'*vxw 0 = (1-t)*vxw 0 + t*?cxw" by simp
                from hmy' hsp0 True have "(1-tp12')*?cyw + tp12'*vyw 0 = (1-t)*vyw 0 + t*?cyw" by simp
                \<comment> \<open>Same ring algebra as jp=0 case but with tp12' and vxw 0.\<close>
                define tp_cx where "tp_cx = tp12'*?cxw"
                define t_cx' where "t_cx' = t*?cxw"
                define tp_vx where "tp_vx = tp12'*vxw 0"
                define t_vx' where "t_vx' = t*vxw 0"
                define oms_cx' where "oms_cx' = (1-tp12')*?cxw"
                define omt_vx' where "omt_vx' = (1-t)*vxw 0"
                have "oms_cx' = ?cxw - tp_cx" unfolding oms_cx'_def tp_cx_def by (by100 algebra)
                have "omt_vx' = vxw 0 - t_vx'" unfolding omt_vx'_def t_vx'_def by (by100 algebra)
                from \<open>(1-tp12')*?cxw + tp12'*vxw 0 = (1-t)*vxw 0 + t*?cxw\<close>
                have "oms_cx' + tp_vx = omt_vx' + t_cx'"
                  unfolding oms_cx'_def tp_vx_def omt_vx'_def t_cx'_def by simp
                hence "?cxw - tp_cx + tp_vx = vxw 0 - t_vx' + t_cx'"
                  using \<open>oms_cx' = ?cxw - tp_cx\<close> \<open>omt_vx' = vxw 0 - t_vx'\<close> by linarith
                hence hx_lin': "tp_vx - tp_cx = (vxw 0 - ?cxw) + (t_cx' - t_vx')" by linarith
                define wx' where "wx' = vxw 0 - ?cxw"
                have "tp_vx - tp_cx = tp12'*wx'" unfolding tp_vx_def tp_cx_def wx'_def by (by100 algebra)
                have "t_cx' - t_vx' = -(t*wx')" unfolding t_cx'_def t_vx'_def wx'_def by (by100 algebra)
                have hwx'_eq: "vxw 0 - ?cxw = wx'" unfolding wx'_def by simp
                from hx_lin' have "tp12'*wx' = wx' - t*wx'"
                  using \<open>tp_vx - tp_cx = tp12'*wx'\<close> \<open>t_cx' - t_vx' = -(t*wx')\<close> hwx'_eq by linarith
                hence htp_wx: "tp12'*wx' = (1-t)*wx'" by (by100 algebra)
                define wy' where "wy' = vyw 0 - ?cyw"
                have htp_wy: "tp12'*wy' = (1-t)*wy'"
                proof -
                  define tp_cy where "tp_cy = tp12'*?cyw"
                  define t_cy' where "t_cy' = t*?cyw"
                  define tp_vy where "tp_vy = tp12'*vyw 0"
                  define t_vy' where "t_vy' = t*vyw 0"
                  define oms_cy' where "oms_cy' = (1-tp12')*?cyw"
                  define omt_vy' where "omt_vy' = (1-t)*vyw 0"
                  have "oms_cy' = ?cyw - tp_cy" unfolding oms_cy'_def tp_cy_def by (by100 algebra)
                  have "omt_vy' = vyw 0 - t_vy'" unfolding omt_vy'_def t_vy'_def by (by100 algebra)
                  from \<open>(1-tp12')*?cyw + tp12'*vyw 0 = (1-t)*vyw 0 + t*?cyw\<close>
                  have "oms_cy' + tp_vy = omt_vy' + t_cy'"
                    unfolding oms_cy'_def tp_vy_def omt_vy'_def t_cy'_def by simp
                  hence "?cyw - tp_cy + tp_vy = vyw 0 - t_vy' + t_cy'"
                    using \<open>oms_cy' = ?cyw - tp_cy\<close> \<open>omt_vy' = vyw 0 - t_vy'\<close> by linarith
                  hence hy_lin': "tp_vy - tp_cy = (vyw 0 - ?cyw) + (t_cy' - t_vy')" by linarith
                  have "tp_vy - tp_cy = tp12'*wy'" unfolding tp_vy_def tp_cy_def wy'_def by (by100 algebra)
                  have "t_cy' - t_vy' = -(t*wy')" unfolding t_cy'_def t_vy'_def wy'_def by (by100 algebra)
                  have hwy'_eq: "vyw 0 - ?cyw = wy'" unfolding wy'_def by simp
                  from hy_lin' have "tp12'*wy' = wy' - t*wy'"
                    using \<open>tp_vy - tp_cy = tp12'*wy'\<close> \<open>t_cy' - t_vy' = -(t*wy')\<close> hwy'_eq by linarith
                  thus ?thesis by (by100 algebra)
                qed
                show ?thesis
                proof (cases "wx' \<noteq> 0")
                  case True from htp_wx True show ?thesis by simp
                next
                  case False hence "wx' = 0" by simp
                  show ?thesis
                  proof (cases "wy' \<noteq> 0")
                    case True from htp_wy True show ?thesis by simp
                  next
                    case False hence "wy' = 0" by simp
                    have "vxw 0 = ?cxw" using \<open>wx' = 0\<close> unfolding wx'_def by simp
                    have "vyw 0 = ?cyw" using \<open>wy' = 0\<close> unfolding wy'_def by simp
                    have h0_lt: "(0::nat) < ?nw" using hnw_pos by linarith
                    from hC10_expanded[rule_format, OF h0_lt]
                    have "(vxw 0-?cxw)*(vyw(Suc 0 mod ?nw)-?cyw)-(vyw 0-?cyw)*(vxw(Suc 0 mod ?nw)-?cxw) > 0" .
                    with \<open>vxw 0 = ?cxw\<close> \<open>vyw 0 = ?cyw\<close> show ?thesis by simp
                  qed
                qed
              qed
              have "(1-tp12') \<in> I_set" using htp_eq' ht
                unfolding top1_unit_interval_def by (by100 auto)
              have "0 < ?ne" using hlen hne_eq by (by100 linarith)
              from hint_p[rule_format, OF this \<open>(1-tp12') \<in> I_set\<close>] hp_edge' show False by (by100 simp)
            next
              case False note hjp_ne_last = this
              \<comment> \<open>Apply spur\\_arc\\_target\\_sector with full arguments.\<close>
              have hC5_cxw: "cxw = (\<Sum>j<?nw. vxw j) / real ?nw" unfolding cxw_def ..
              have hC5_cyw: "cyw = (\<Sum>j<?nw. vyw j) / real ?nw" unfolding cyw_def ..
              have hC10_cxw: "\<forall>i<?nw. (vxw i - cxw) * (vyw(Suc i mod ?nw) - cyw) -
                  (vyw i - cyw) * (vxw(Suc i mod ?nw) - cxw) > 0"
                using hC10_expanded unfolding cxw_def cyw_def by (by100 simp)
              have hC11_cxw: "\<forall>i<?nw. \<forall>k<?nw. k\<noteq>i \<longrightarrow> k\<noteq>Suc i mod ?nw \<longrightarrow>
                  (vxw k-vxw i)*(vyw(Suc i mod ?nw)-vyw i)-(vyw k-vyw i)*(vxw(Suc i mod ?nw)-vxw i) < 0"
                using hC11_w .
              have hcc_disj: "(vxw jp-cxw)*(vyw 0-cyw)-(vyw jp-cyw)*(vxw 0-cxw) < 0
                \<or> (vxw(Suc jp mod ?nw)-cxw)*(vyw 0-cyw)-(vyw(Suc jp mod ?nw)-cyw)*(vxw 0-cxw) > 0"
                by (rule spur_arc_target_sector[OF hlen hC10_cxw hC11_cxw hC5_cxw hC5_cyw
                    hfan_det_w hregular_w hjp hjp_ne0 hjp_ne_last])
              \<comment> \<open>Cramer extraction (same as prop11 but at higher scope to avoid define issues).\<close>
              from hphi_affine_on_sector[rule_format, OF hjp hp hin_sec]
              have hphi_form12: "phi_fn (fst p, snd p) = (let ex = vxe(jp+2)-vxe 1; ey = vye(jp+2)-vye 1;
                  fx = vxe(Suc(jp+2) mod ?ne)-vxe 1; fy = vye(Suc(jp+2) mod ?ne)-vye 1;
                  det = ex*fy-ey*fx; dx = fst p-vxe 1; dy = snd p-vye 1;
                  s' = (fy*dx-fx*dy)/det; t' = (ex*dy-ey*dx)/det
              in ((1-s'-t')*?cxw + s'*vxw jp + t'*vxw(Suc jp mod ?nw),
                  (1-s'-t')*?cyw + s'*vyw jp + t'*vyw(Suc jp mod ?nw)))" .
              define ex_p12 where "ex_p12 = vxe(jp+2)-vxe 1"
              define ey_p12 where "ey_p12 = vye(jp+2)-vye 1"
              define fx_p12 where "fx_p12 = vxe(Suc(jp+2) mod ?ne)-vxe 1"
              define fy_p12 where "fy_p12 = vye(Suc(jp+2) mod ?ne)-vye 1"
              define dx_p12 where "dx_p12 = fst p-vxe 1"
              define dy_p12 where "dy_p12 = snd p-vye 1"
              define det_p12 where "det_p12 = ex_p12*fy_p12-ey_p12*fx_p12"
              define sp12 where "sp12 = (fy_p12*dx_p12-fx_p12*dy_p12)/det_p12"
              define tp12 where "tp12 = (ex_p12*dy_p12-ey_p12*dx_p12)/det_p12"
              have hdet_p12_pos: "det_p12 > 0"
                using hdet_pos[rule_format, OF hjp]
                unfolding det_p12_def ex_p12_def ey_p12_def fx_p12_def fy_p12_def by (by100 simp)
              have hdet_p12_ne: "det_p12 \<noteq> 0" using hdet_p12_pos by linarith
              have hphi_x12: "fst (phi_fn p) = (1-sp12-tp12)*?cxw + sp12*vxw jp + tp12*vxw(Suc jp mod ?nw)"
                using hphi_form12 unfolding Let_def sp12_def tp12_def det_p12_def
                  ex_p12_def ey_p12_def fx_p12_def fy_p12_def dx_p12_def dy_p12_def by (by100 simp)
              have hphi_y12: "snd (phi_fn p) = (1-sp12-tp12)*?cyw + sp12*vyw jp + tp12*vyw(Suc jp mod ?nw)"
                using hphi_form12 unfolding Let_def sp12_def tp12_def det_p12_def
                  ex_p12_def ey_p12_def fx_p12_def fy_p12_def dx_p12_def dy_p12_def by (by100 simp)
              have hsp12_ge: "sp12 \<ge> 0"
              proof -
                from hin_sec have "cross_v1 (Suc(jp+2) mod ?ne) p \<le> 0" unfolding in_sector_def by (by100 auto)
                have "fy_p12*dx_p12 - fx_p12*dy_p12 = -(cross_v1 (Suc(jp+2) mod ?ne) p)"
                  unfolding cross_v1_def fx_p12_def fy_p12_def dx_p12_def dy_p12_def by (by100 algebra)
                hence "sp12*det_p12 \<ge> 0"
                  unfolding sp12_def using hdet_p12_ne \<open>cross_v1 _ p \<le> 0\<close> by (by100 simp)
                thus ?thesis using hdet_p12_pos
                  by (metis linorder_not_le mult_neg_pos)
              qed
              have htp12_ge: "tp12 \<ge> 0"
              proof -
                from hin_sec have "cross_v1 (jp+2) p \<ge> 0" unfolding in_sector_def by (by100 auto)
                have "ex_p12*dy_p12 - ey_p12*dx_p12 = cross_v1 (jp+2) p"
                  unfolding cross_v1_def ex_p12_def ey_p12_def dx_p12_def dy_p12_def by (by100 simp)
                hence "tp12*det_p12 \<ge> 0"
                  unfolding tp12_def using hdet_p12_ne \<open>cross_v1 _ p \<ge> 0\<close> by (by100 simp)
                thus ?thesis using hdet_p12_pos
                  by (metis linorder_not_le mult_neg_pos)
              qed
              have habg12: "(1-sp12-tp12) + sp12 + tp12 = 1" by linarith
              have hC10_jp: "(vxw jp-?cxw)*(vyw(Suc jp mod ?nw)-?cyw)-(vyw jp-?cyw)*(vxw(Suc jp mod ?nw)-?cxw) > 0"
                using hC10_expanded hjp by (by100 blast)
              \<comment> \<open>Centroid-cone cross products \\<ge> 0.\<close>
              from centroid_cone_cross_nonneg[OF hsp12_ge htp12_ge habg12 hphi_x12 hphi_y12 hC10_jp]
              have hcross_phi_ge1: "(vxw jp-?cxw)*(snd (phi_fn p)-?cyw)-(vyw jp-?cyw)*(fst (phi_fn p)-?cxw) \<ge> 0"
                and hcross_phi_ge2: "(fst (phi_fn p)-?cxw)*(vyw(Suc jp mod ?nw)-?cyw)-(snd (phi_fn p)-?cyw)*(vxw(Suc jp mod ?nw)-?cxw) \<ge> 0"
                by auto
              show False
              proof (cases "t = 1")
                case True
                \<comment> \<open>t=1: spur point = centroid. phi(p)=cw forces p=vertex1.\<close>
                have "phi_fn (edge_pt_e 0 t) = (?cxw, ?cyw)"
                  using hphi_on_spur0[rule_format, OF ht] True by (by100 simp)
                hence "phi_fn p = (?cxw, ?cyw)" using heq by (by100 simp)
                \<comment> \<open>From affine form: phi(p)=cw means sp=tp=0, hence p=vertex1.\<close>
                from hphi_affine_on_sector[rule_format, OF hjp hp hin_sec]
                have hphi_form: "phi_fn (fst p, snd p) = (let ex = vxe(jp+2)-vxe 1; ey = vye(jp+2)-vye 1;
                    fx = vxe(Suc(jp+2) mod ?ne)-vxe 1; fy = vye(Suc(jp+2) mod ?ne)-vye 1;
                    det = ex*fy-ey*fx; dx = fst p-vxe 1; dy = snd p-vye 1;
                    s' = (fy*dx-fx*dy)/det; t' = (ex*dy-ey*dx)/det
                in ((1-s'-t')*?cxw + s'*vxw jp + t'*vxw(Suc jp mod ?nw),
                    (1-s'-t')*?cyw + s'*vyw jp + t'*vyw(Suc jp mod ?nw)))" .
                \<comment> \<open>From phi(p)=cw and hcxw\\_0/hcyw\\_0: phi\\_x = 0, phi\\_y = 0.\<close>
                \<comment> \<open>Cramer coords: sp*vxw(jp) + tp*vxw(jp+1) = 0 (with alpha*cxw = 0).\<close>
                \<comment> \<open>Since vxw,vyw linearly independent (C10), sp=tp=0, hence dx=dy=0, p=v1.\<close>
                \<comment> \<open>phi(p)=cw=(0,0). From hphi\\_x12: 0 = sp12*vxw(jp)+tp12*vxw(jp+1) (cxw=0).\<close>
                have "?cxw = 0" using hcxw_0 unfolding cxw_def by (by100 simp)
                have "?cyw = 0" using hcyw_0 unfolding cyw_def by (by100 simp)
                have hfst_eq: "sp12*vxw jp + tp12*vxw(Suc jp mod ?nw) = 0"
                proof -
                  from \<open>phi_fn p = (?cxw, ?cyw)\<close> have "fst (phi_fn p) = ?cxw" by (by100 simp)
                  with hphi_x12 have "(1-sp12-tp12)*?cxw + sp12*vxw jp + tp12*vxw(Suc jp mod ?nw) = ?cxw"
                    by (by100 simp)
                  with \<open>?cxw = 0\<close> show ?thesis by (by100 algebra)
                qed
                have hsnd_eq: "sp12*vyw jp + tp12*vyw(Suc jp mod ?nw) = 0"
                proof -
                  from \<open>phi_fn p = (?cxw, ?cyw)\<close> have "snd (phi_fn p) = ?cyw" by (by100 simp)
                  with hphi_y12 have "(1-sp12-tp12)*?cyw + sp12*vyw jp + tp12*vyw(Suc jp mod ?nw) = ?cyw"
                    by (by100 simp)
                  with \<open>?cyw = 0\<close> show ?thesis by (by100 algebra)
                qed
                \<comment> \<open>C10(jp) \\<noteq> 0, so the 2x2 system has only solution sp12=tp12=0.\<close>
                have "sp12 = 0 \<and> tp12 = 0"
                proof -
                  \<comment> \<open>cross(u\\_jp, u\\_{jp+1}) = vxw(jp)*vyw(jp+1)-vyw(jp)*vxw(jp+1) \\<noteq> 0.\<close>
                  \<comment> \<open>Cramer: sp12 = (0*vyw(jp+1)-0*vxw(jp+1))/cross = 0, tp12 = (vxw(jp)*0-vyw(jp)*0)/cross = 0.\<close>
                  have hcross_ne: "vxw jp*vyw(Suc jp mod ?nw)-vyw jp*vxw(Suc jp mod ?nw) \<noteq> 0"
                  proof -
                    from hC10_jp \<open>?cxw = 0\<close> \<open>?cyw = 0\<close>
                    have "vxw jp*vyw(Suc jp mod ?nw)-vyw jp*vxw(Suc jp mod ?nw) > 0" by (by100 simp)
                    thus ?thesis by linarith
                  qed
                  \<comment> \<open>From the 2x2 system: sp12*(det) = 0 and tp12*(det) = 0.\<close>
                  have "sp12*(vxw jp*vyw(Suc jp mod ?nw)-vyw jp*vxw(Suc jp mod ?nw)) = 0"
                    using hfst_eq hsnd_eq by (by100 algebra)
                  hence "sp12 = 0" using hcross_ne by (by100 simp)
                  have "tp12*(vxw jp*vyw(Suc jp mod ?nw)-vyw jp*vxw(Suc jp mod ?nw)) = 0"
                    using hfst_eq hsnd_eq by (by100 algebra)
                  hence "tp12 = 0" using hcross_ne by (by100 simp)
                  with \<open>sp12 = 0\<close> show ?thesis by (by100 simp)
                qed
                \<comment> \<open>sp12=tp12=0 implies dx\\_p12=dy\\_p12=0 (Cramer with nonzero det).\<close>
                have hsp_mul12: "sp12*det_p12 = fy_p12*dx_p12-fx_p12*dy_p12"
                  unfolding sp12_def using hdet_p12_ne by (by100 simp)
                have htp_mul12: "tp12*det_p12 = ex_p12*dy_p12-ey_p12*dx_p12"
                  unfolding tp12_def using hdet_p12_ne by (by100 simp)
                have "fy_p12*dx_p12 - fx_p12*dy_p12 = 0"
                  using \<open>sp12 = 0 \<and> tp12 = 0\<close> hsp_mul12 by (by100 simp)
                have "ex_p12*dy_p12 - ey_p12*dx_p12 = 0"
                  using \<open>sp12 = 0 \<and> tp12 = 0\<close> htp_mul12 by (by100 simp)
                have "dx_p12 = 0 \<and> dy_p12 = 0"
                proof -
                  have "ex_p12*(fy_p12*dx_p12-fx_p12*dy_p12)+fx_p12*(ex_p12*dy_p12-ey_p12*dx_p12) = det_p12*dx_p12"
                    unfolding det_p12_def by (by100 algebra)
                  have "ex_p12*0 + fx_p12*0 = det_p12*dx_p12"
                    using \<open>fy_p12*dx_p12-fx_p12*dy_p12 = 0\<close> \<open>ex_p12*dy_p12-ey_p12*dx_p12 = 0\<close>
                    \<open>ex_p12*(fy_p12*dx_p12-fx_p12*dy_p12)+fx_p12*(ex_p12*dy_p12-ey_p12*dx_p12) = det_p12*dx_p12\<close>
                    by (by100 simp)
                  hence "det_p12*dx_p12 = 0" by (by100 simp)
                  hence "dx_p12 = 0" using hdet_p12_ne by (by100 simp)
                  have "ey_p12*(fy_p12*dx_p12-fx_p12*dy_p12)+fy_p12*(ex_p12*dy_p12-ey_p12*dx_p12) = det_p12*dy_p12"
                    unfolding det_p12_def by (by100 algebra)
                  have "ey_p12*0 + fy_p12*0 = det_p12*dy_p12"
                    using \<open>fy_p12*dx_p12-fx_p12*dy_p12 = 0\<close> \<open>ex_p12*dy_p12-ey_p12*dx_p12 = 0\<close>
                    \<open>ey_p12*(fy_p12*dx_p12-fx_p12*dy_p12)+fy_p12*(ex_p12*dy_p12-ey_p12*dx_p12) = det_p12*dy_p12\<close>
                    by (by100 simp)
                  hence "det_p12*dy_p12 = 0" by (by100 simp)
                  hence "dy_p12 = 0" using hdet_p12_ne by (by100 simp)
                  with \<open>dx_p12 = 0\<close> show ?thesis by (by100 simp)
                qed
                hence "fst p = vxe 1" "snd p = vye 1"
                  unfolding dx_p12_def dy_p12_def by auto
                hence "p = (vxe 1, vye 1)" by (cases p) (by100 simp)
                with hp_ne_v1 show False by (by100 simp)
              next
                case False
                hence ht_lt1: "t < 1" using ht unfolding top1_unit_interval_def by (by100 auto)
                hence h1mt_pos: "1 - t > 0" by linarith
                \<comment> \<open>Spur point: q = (1-t)*u\\_0 + t*cw.\<close>
                \<comment> \<open>Cross product of (q-cw) with (u\\_jp-cw) = (1-t)*cc(jp).
                   Cross product of (u\\_{jp+1}-cw) with (q-cw) = (1-t)*cc(jp+1).\<close>
                \<comment> \<open>For the spur to be in centroid-cone jp: need (1-t)*cc(jp) \\<ge> 0 AND -(1-t)*cc(jp+1) \\<ge> 0.
                   i.e., cc(jp) \\<ge> 0 AND cc(jp+1) \\<le> 0. But hcc\\_disj says the opposite.\<close>
                \<comment> \<open>phi\\_fn(p) IS in centroid-cone jp (from affine map + hin\\_sec).\<close>
                \<comment> \<open>Formally: show centroid-cone cross products agree for phi\\_fn(p) but not for spur.\<close>
                \<comment> \<open>phi\\_fn(p) = spur. Compute cross(u\\_jp-cw, point-cw) two ways.\<close>
                have hspur_eq: "phi_fn p = ((1-t)*vxw 0 + t*?cxw, (1-t)*vyw 0 + t*?cyw)"
                  using heq hphi_on_spur0[rule_format, OF ht] by (by100 simp)
                \<comment> \<open>phi\\_fn(p) - cw = (1-t)*(u\\_0 - cw) (direction from centroid to vertex 0).\<close>
                have hfst_diff: "fst (phi_fn p) - ?cxw = (1-t)*(vxw 0 - ?cxw)"
                proof -
                  have "fst (phi_fn p) = (1-t)*vxw 0 + t*?cxw" using hspur_eq by (by100 simp)
                  thus ?thesis by (by100 algebra)
                qed
                have hsnd_diff: "snd (phi_fn p) - ?cyw = (1-t)*(vyw 0 - ?cyw)"
                proof -
                  have "snd (phi_fn p) = (1-t)*vyw 0 + t*?cyw" using hspur_eq by (by100 simp)
                  thus ?thesis by (by100 algebra)
                qed
                \<comment> \<open>Cross(u\\_jp-cw, phi(p)-cw) = (1-t)*cc(jp).\<close>
                have hcross_spur: "(vxw jp - ?cxw)*(snd (phi_fn p) - ?cyw) - (vyw jp - ?cyw)*(fst (phi_fn p) - ?cxw) =
                  (1-t)*((vxw jp - ?cxw)*(vyw 0 - ?cyw) - (vyw jp - ?cyw)*(vxw 0 - ?cxw))"
                  using hfst_diff hsnd_diff by (by100 algebra)
                \<comment> \<open>But phi\\_fn(p) is in sector jp, so Cross(u\\_jp-cw, phi(p)-cw) = tp*C10(jp) \\<ge> 0.\<close>
                \<comment> \<open>We use: from the affine form, the cross product with u\\_jp-cw must have correct sign.\<close>
                from hcc_disj show False
                proof
                  assume hcc_neg: "(vxw jp-cxw)*(vyw 0-cyw)-(vyw jp-cyw)*(vxw 0-cxw) < 0"
                  \<comment> \<open>cc(jp) < 0. Cross(u\\_jp-cw, spur-cw) = (1-t)*cc(jp) < 0.\<close>
                  have "((vxw jp-?cxw)*(vyw 0-?cyw)-(vyw jp-?cyw)*(vxw 0-?cxw)) < 0"
                    using hcc_neg unfolding cxw_def cyw_def by (by100 simp)
                  hence hcross_neg: "(vxw jp - ?cxw)*(snd (phi_fn p) - ?cyw) - (vyw jp - ?cyw)*(fst (phi_fn p) - ?cxw) < 0"
                    using hcross_spur h1mt_pos
                    by (metis mult_pos_neg)
                  \<comment> \<open>But from centroid\\_weight\\_not\\_on\\_edge infrastructure: phi(p) has \\<alpha>>0, so
                     the cross with u\\_jp-cw direction via C10 is \\<ge> 0. Contradiction.\<close>
                  \<comment> \<open>Actually: direct computation. phi(p) = \\<alpha>*cw + sp*u\\_jp + tp*u\\_{jp+1}.
                     cross(u\\_jp-cw, phi(p)-cw) = sp*cross(u\\_jp-cw, u\\_jp-cw) + tp*cross(u\\_jp-cw, u\\_{jp+1}-cw)
                       = tp * C10(jp). Since tp \\<ge> 0 and C10(jp) > 0: cross \\<ge> 0.\<close>
                  with hcross_phi_ge1 show False by linarith
                next
                  assume hcc_pos: "(vxw(Suc jp mod ?nw)-cxw)*(vyw 0-cyw)-(vyw(Suc jp mod ?nw)-cyw)*(vxw 0-cxw) > 0"
                  \<comment> \<open>cc(jp+1) > 0. Cross(phi(p)-cw, u\\_{jp+1}-cw) = -(1-t)*cc(jp+1) < 0.
                     But from sector form: sp*C10(jp) \\<ge> 0. Contradiction.\<close>
                  have "((vxw(Suc jp mod ?nw)-?cxw)*(vyw 0-?cyw)-(vyw(Suc jp mod ?nw)-?cyw)*(vxw 0-?cxw)) > 0"
                    using hcc_pos unfolding cxw_def cyw_def by (by100 simp)
                  \<comment> \<open>Cross(phi(p)-cw, u\\_{jp+1}-cw) = (1-t)*cross(u\\_0-cw, u\\_{jp+1}-cw) = -(1-t)*cc(jp+1).\<close>
                  have hcross_spur2: "(fst (phi_fn p) - ?cxw)*(vyw(Suc jp mod ?nw) - ?cyw) -
                    (snd (phi_fn p) - ?cyw)*(vxw(Suc jp mod ?nw) - ?cxw) =
                    -(1-t)*((vxw(Suc jp mod ?nw) - ?cxw)*(vyw 0 - ?cyw) - (vyw(Suc jp mod ?nw) - ?cyw)*(vxw 0 - ?cxw))"
                    using hfst_diff hsnd_diff by (by100 algebra)
                  hence hcross_neg2: "(fst (phi_fn p) - ?cxw)*(vyw(Suc jp mod ?nw) - ?cyw) -
                    (snd (phi_fn p) - ?cyw)*(vxw(Suc jp mod ?nw) - ?cxw) < 0"
                  proof -
                    have "-(1-t) < 0" using h1mt_pos by linarith
                    thus ?thesis using hcross_spur2
                      \<open>((vxw(Suc jp mod ?nw)-?cxw)*(vyw 0-?cyw)-(vyw(Suc jp mod ?nw)-?cyw)*(vxw 0-?cxw)) > 0\<close>
                      by (metis mult_neg_pos)
                  qed
                  with hcross_phi_ge2 show False by linarith
                qed
              qed
            qed
          qed
        qed
      qed
      show ?thesis
        by (rule that[of phi_fn])
           (use prop1 prop2 prop3 prop4 prop5 prop6 prop7 prop8 prop9
                prop10 prop11 prop12 in blast)+
    qed
    \<comment> \<open>Define g = q\\_w o phi: P\\_e -> Y\\_w.\<close>
    let ?g = "\<lambda>p. q_w (phi p)"
    \<comment> \<open>Property 1: range. q\\_w maps P\\_w to Y\\_w.\<close>
    have hg_range: "\<forall>p \<in> P_e. ?g p \<in> Y_w"
    proof (intro ballI)
      fix p assume "p \<in> P_e"
      have "phi p \<in> P_w" using hphi_range \<open>p \<in> P_e\<close> by (by100 blast)
      have "q_w (phi p) \<in> Y_w"
        using hC2_w \<open>phi p \<in> P_w\<close>
        unfolding top1_quotient_map_on_def top1_continuous_map_on_def by (by100 blast)
      thus "?g p \<in> Y_w" by (by100 simp)
    qed
    \<comment> \<open>Property 2: continuity. Composition of continuous maps.\<close>
    have hg_cont: "top1_continuous_map_on P_e
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_e)
        Y_w TY_w ?g"
    proof -
      \<comment> \<open>q\\_w: P\\_w -> Y\\_w is continuous (from quotient map).\<close>
      have hqw_cont: "top1_continuous_map_on P_w
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_w)
          Y_w TY_w q_w"
        using hC2_w unfolding top1_quotient_map_on_def by (by100 blast)
      \<comment> \<open>g = q\\_w o phi is composition of continuous phi and continuous q\\_w.\<close>
      have "top1_continuous_map_on P_e
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_e)
          Y_w TY_w (q_w \<circ> phi)"
        by (rule top1_continuous_map_on_comp[OF hphi_cont hqw_cont])
      thus ?thesis unfolding comp_def .
    qed
    \<comment> \<open>Property 3: surjectivity. phi surjective + q\\_w surjective.\<close>
    have hg_surj: "?g ` P_e = Y_w"
    proof -
      have hq_surj: "q_w ` P_w = Y_w"
        using hC2_w unfolding top1_quotient_map_on_def top1_continuous_map_on_def by (by100 blast)
      have "?g ` P_e = q_w ` (phi ` P_e)" by (by100 auto)
      also have "phi ` P_e = P_w" using hphi_surj .
      also have "q_w ` P_w = Y_w" using hq_surj .
      finally show ?thesis .
    qed
    \<comment> \<open>Property 4: forward fibres. q\\_e(x) = q\\_e(y) implies g(x) = g(y).
       Cases:
       - Both interior: q\\_e injective (C8) -> x=y -> g(x)=g(y). CHECK.
       - Both spur: phi maps spur to u\\_0, so g constant on spur. CHECK.
       - Matched non-spur edges: C7 of q\\_e at (i+2,j+2) corresponds to
         C7 of q\\_w at (i,j) via label correspondence -> g values match. CHECK.
       - Spur to vertex v\\_2: q\\_e(v\\_0)=q\\_e(v\\_2), phi(v\\_0)=u\\_0, phi(v\\_2)=u\\_0. CHECK.
       - Cross-type: impossible by C8/C12.\<close>
    have hg_fwd: "\<forall>x\<in>P_e. \<forall>y\<in>P_e. q_e x = q_e y \<longrightarrow> ?g x = ?g y"
    proof (intro ballI impI)
      fix x y assume hx: "x \<in> P_e" and hy: "y \<in> P_e" and heq: "q_e x = q_e y"
      \<comment> \<open>Goal: q\\_w(phi(x)) = q\\_w(phi(y)).
         The identification q\\_e(x)=q\\_e(y) means x and y are in the same fibre.
         By the structure of q\\_e (3-branch): either x=y (interior injectivity),
         or both are on matching edges identified by C7, or vertex identification.
         In each case, phi maps them to q\\_w-identified points.\<close>
      \<comment> \<open>Case split: x interior or boundary.\<close>
      consider (x_int) "\<forall>i<?ne. \<forall>t\<in>I_set. x \<noteq> edge_pt_e i t"
        | (x_bdy) "\<exists>i<?ne. \<exists>t\<in>I_set. x = edge_pt_e i t"
        by (by100 blast)
      thus "?g x = ?g y"
      proof cases
        case x_int
        \<comment> \<open>x interior: C8\\_e says x=y.\<close>
        have hx_int': "\<forall>i<?ne. \<forall>t\<in>I_set.
            x \<noteq> ((1-t)*vxe i+t*vxe(Suc i mod ?ne),(1-t)*vye i+t*vye(Suc i mod ?ne))"
          using x_int unfolding edge_pt_e_def by (by100 simp)
        from hC8_e[rule_format, OF hx] hx_int'
        have "\<forall>p'\<in>P_e. q_e x = q_e p' \<longrightarrow> x = p'" by (by100 blast)
        hence "x = y" using hy heq by (by100 blast)
        thus ?thesis by (by100 simp)
      next
        case x_bdy
        from x_bdy obtain ix tx where hix: "ix < ?ne" and htx: "tx \<in> I_set"
            and hx_eq: "x = edge_pt_e ix tx" by (by100 blast)
        \<comment> \<open>y must also be on boundary (from C8\\_e + C12\\_e).\<close>
        \<comment> \<open>Sub-case: is y interior or boundary?\<close>
        consider (y_int) "\<forall>i<?ne. \<forall>t\<in>I_set. y \<noteq> edge_pt_e i t"
          | (y_bdy) "\<exists>i<?ne. \<exists>t\<in>I_set. y = edge_pt_e i t"
          by (by100 blast)
        thus ?thesis
        proof cases
          case y_int
          \<comment> \<open>x boundary, y interior: C8\\_e at y gives y unique -> x=y impossible
             since x is boundary and y interior? Not quite: C8\\_e says y has unique preimage
             under q\\_e. Since q\\_e(x) = q\\_e(y) and y is interior (unique), x = y.
             But x is boundary and y is interior -> x != y? That depends on whether
             boundary and interior are disjoint. They ARE for convex polygons.\<close>
          have hy_int': "\<forall>i<?ne. \<forall>t\<in>I_set.
              y \<noteq> ((1-t)*vxe i+t*vxe(Suc i mod ?ne),(1-t)*vye i+t*vye(Suc i mod ?ne))"
            using y_int unfolding edge_pt_e_def by (by100 simp)
          from hC8_e[rule_format, OF hy] hy_int'
          have "\<forall>p'\<in>P_e. q_e y = q_e p' \<longrightarrow> y = p'" by (by100 blast)
          hence "y = x" using hx heq[symmetric] by (by100 blast)
          thus ?thesis by (by100 simp)
        next
          case y_bdy
          from y_bdy obtain iy ty where hiy: "iy < ?ne" and hty: "ty \<in> I_set"
              and hy_eq: "y = edge_pt_e iy ty" by (by100 blast)
          \<comment> \<open>Both boundary. Forward matching by cases on spur/non-spur.
             q\\_e(x) = q\\_e(y): from C9\\_e + C7\\_e, this gives the edge matching.
             Then phi maps the matched edges to q\\_w-matched edges.\<close>
          \<comment> \<open>Both boundary. Split on edge-interior vs vertex.\<close>
          show ?thesis
          proof (cases "0 < tx \<and> tx < 1 \<and> 0 < ty \<and> ty < 1")
            case True
            hence htx_int: "tx \<in> {0<..<(1::real)}" and hty_int: "ty \<in> {0<..<(1::real)}" by (by100 auto)+
            \<comment> \<open>C9\\_e: q\\_e(edge(ix,tx))=q\\_e(edge(iy,ty)) with both interior gives
               (ix=iy and tx=ty) or (label match + direction).\<close>
            have hq_inst: "q_e ((1-tx)*vxe ix+tx*vxe(Suc ix mod ?ne),
                (1-tx)*vye ix+tx*vye(Suc ix mod ?ne))
              = q_e ((1-ty)*vxe iy+ty*vxe(Suc iy mod ?ne),
                (1-ty)*vye iy+ty*vye(Suc iy mod ?ne))"
              using heq hx_eq hy_eq unfolding edge_pt_e_def by (by100 simp)
            from hC9_e[rule_format, OF hix hiy htx_int hty_int] hq_inst
            have hC9_result: "(ix=iy \<and> tx=ty) \<or> (fst(?ext!ix)=fst(?ext!iy) \<and>
                (if snd(?ext!ix)=snd(?ext!iy) then ty=tx else ty=1-tx))"
              by (by100 blast)
            from hC9_result show ?thesis
            proof (elim disjE conjE)
              assume "ix=iy" "tx=ty" thus ?thesis using hx_eq hy_eq by (by100 simp)
            next
              assume hlbl_e: "fst(?ext!ix) = fst(?ext!iy)"
                and hdir_e: "if snd(?ext!ix)=snd(?ext!iy) then ty=tx else ty=1-tx"
              \<comment> \<open>phi maps edge(ix,tx) and edge(iy,ty) to phi-images.
                 Need: q\\_w(phi(x)) = q\\_w(phi(y)).
                 This follows from: phi maps matched ext-edges to q\\_w-matched w-edges
                 (when non-spur) or to spur arc points (when spur).\<close>
              \<comment> \<open>Case analysis on spur/non-spur.\<close>
              show ?thesis
              proof (cases "ix < 2")
                case True
                \<comment> \<open>ix spur. Since fst(ext!ix) = fst(ext!iy) and ext!ix has label a,
                   iy must also be spur (label a is fresh in w).\<close>
                have "iy < 2"
                proof (rule ccontr)
                  assume "\<not>(iy < 2)" hence "iy \<ge> 2" by (by100 simp)
                  hence "iy - 2 < ?nw" using hiy hne_eq by (by100 linarith)
                  have hiy_eq2: "(iy-2)+2 = iy" using \<open>iy \<ge> 2\<close> by (by100 linarith)
                  from hlabel_corr[rule_format, OF \<open>iy-2 < ?nw\<close>]
                  have h_: "([a, top1_inverse_edge a] @ w) ! ((iy-2)+2) = w!(iy-2)" .
                  have "([a, top1_inverse_edge a] @ w) ! iy = ([a, top1_inverse_edge a] @ w) ! ((iy-2)+2)"
                    using hiy_eq2 by (by100 simp)
                  hence "([a, top1_inverse_edge a] @ w) ! iy = w!(iy-2)" using h_ by (by100 simp)
                  hence "fst(?ext!iy) = fst(w!(iy-2))" by (by100 simp)
                  moreover have "fst(?ext!ix) = fst a"
                  proof (cases "ix = 0")
                    case True thus ?thesis using hspur0 by (by100 simp)
                  next
                    case False hence "ix = 1" using \<open>ix < 2\<close> by (by100 simp)
                    thus ?thesis using hspur1 unfolding top1_inverse_edge_def by (by100 simp)
                  qed
                  ultimately have "fst a = fst(w!(iy-2))" using hlbl_e by (by100 simp)
                  moreover have "w!(iy-2) \<in> set w" using \<open>iy-2 < ?nw\<close> by (by100 simp)
                  hence "fst(w!(iy-2)) \<in> fst ` set w" by (by100 blast)
                  ultimately have "fst a \<in> fst ` set w" by (by100 simp)
                  thus False using hfresh by (by100 blast)
                qed
                \<comment> \<open>Both spur: phi maps both to spur arc. By spur\\_match, the images agree.\<close>
                show ?thesis
                proof (cases "snd(?ext!ix) = snd(?ext!iy)")
                  case True
                  \<comment> \<open>Same direction: ty = tx. Both on same spur edge or same param.\<close>
                  hence "ty = tx" using hdir_e by (by100 simp)
                  hence "phi (edge_pt_e ix tx) = phi (edge_pt_e iy ty)"
                  proof -
                    \<comment> \<open>ix,iy in {0,1} with same snd -> ix=iy (since snd(ext!0)!=snd(ext!1)).\<close>
                    have "snd(?ext!0) \<noteq> snd(?ext!1)"
                      using hspur0 hspur1 unfolding top1_inverse_edge_def by (by100 simp)
                    have "ix = 0 \<or> ix = 1" using \<open>ix < 2\<close> by (by100 linarith)
                    moreover have "iy = 0 \<or> iy = 1" using \<open>iy < 2\<close> by (by100 linarith)
                    ultimately have "ix = iy"
                      using True \<open>snd(?ext!0) \<noteq> snd(?ext!1)\<close> by (by100 auto)
                    thus ?thesis using \<open>ty = tx\<close> by (by100 simp)
                  qed
                  thus ?thesis using hx_eq hy_eq by (by100 simp)
                next
                  case False
                  \<comment> \<open>Opposite direction: ty = 1-tx. C7 pairs edge(0,t) with edge(1,1-t).\<close>
                  hence hty_rel: "ty = 1-tx" using hdir_e by (by100 simp)
                  \<comment> \<open>ix!=iy (different snd). So ix=0,iy=1 or ix=1,iy=0.\<close>
                  have "ix = 0 \<or> ix = 1" using \<open>ix < 2\<close> by (by100 linarith)
                  moreover have "iy = 0 \<or> iy = 1" using \<open>iy < 2\<close> by (by100 linarith)
                  moreover have "snd(?ext!0) \<noteq> snd(?ext!1)"
                    using hspur0 hspur1 unfolding top1_inverse_edge_def by (by100 simp)
                  ultimately consider (a01) "ix=0 \<and> iy=1" | (a10) "ix=1 \<and> iy=0"
                    using False by (by100 auto)
                  thus ?thesis
                  proof cases
                    case a01
                    \<comment> \<open>phi(edge(0,tx)) = phi(edge(1,1-tx)) = phi(edge(1,ty)) by spur\\_match.\<close>
                    from hphi_spur_match[rule_format, OF htx]
                    have "phi (edge_pt_e 0 tx) = phi (edge_pt_e 1 (1-tx))" .
                    hence "phi (edge_pt_e ix tx) = phi (edge_pt_e iy ty)"
                      using a01 hty_rel by (by100 simp)
                    thus ?thesis using hx_eq hy_eq by (by100 simp)
                  next
                    case a10
                    from hphi_spur_match[rule_format, OF hty]
                    have "phi (edge_pt_e 0 ty) = phi (edge_pt_e 1 (1-ty))" .
                    hence "phi (edge_pt_e iy ty) = phi (edge_pt_e ix tx)"
                      using a10 hty_rel by (by100 simp)
                    thus ?thesis using hx_eq hy_eq by (by100 simp)
                  qed
                qed
              next
                case False hence "ix \<ge> 2" by (by100 simp)
                \<comment> \<open>ix non-spur. iy must also be non-spur (freshness eliminates spur).\<close>
                have "iy \<ge> 2"
                proof (rule ccontr)
                  assume "\<not>(iy \<ge> 2)" hence "iy < 2" by (by100 simp)
                  have "ix - 2 < ?nw" using hix hne_eq \<open>ix \<ge> 2\<close> by (by100 linarith)
                  have hix_eq2: "(ix-2)+2 = ix" using \<open>ix \<ge> 2\<close> by (by100 linarith)
                  from hlabel_corr[rule_format, OF \<open>ix-2 < ?nw\<close>]
                  have h_2: "([a, top1_inverse_edge a] @ w) ! ((ix-2)+2) = w!(ix-2)" .
                  have "([a, top1_inverse_edge a] @ w) ! ix = ([a, top1_inverse_edge a] @ w) ! ((ix-2)+2)"
                    using hix_eq2 by (by100 simp)
                  hence "([a, top1_inverse_edge a] @ w) ! ix = w!(ix-2)" using h_2 by (by100 simp)
                  hence "fst(?ext!ix) = fst(w!(ix-2))" by (by100 simp)
                  moreover have "fst(?ext!iy) = fst a"
                  proof (cases "iy = 0")
                    case True thus ?thesis using hspur0 by (by100 simp)
                  next
                    case False hence "iy = 1" using \<open>iy < 2\<close> by (by100 simp)
                    thus ?thesis using hspur1 unfolding top1_inverse_edge_def by (by100 simp)
                  qed
                  ultimately have "fst a = fst(w!(ix-2))" using hlbl_e by (by100 simp)
                  moreover have "w!(ix-2) \<in> set w" using \<open>ix-2 < ?nw\<close> by (by100 simp)
                  hence "fst(w!(ix-2)) \<in> fst ` set w" by (by100 blast)
                  ultimately have "fst a \<in> fst ` set w" by (by100 simp)
                  thus False using hfresh by (by100 blast)
                qed
                \<comment> \<open>Both non-spur. phi maps to edge\\_pt\\_w. C7\\_w gives identification.\<close>
                have hix_k: "ix - 2 < ?nw" using hix hne_eq \<open>ix \<ge> 2\<close> by (by100 linarith)
                have hiy_k: "iy - 2 < ?nw" using hiy hne_eq \<open>iy \<ge> 2\<close> by (by100 linarith)
                have hix_eq2: "(ix-2)+2 = ix" using \<open>ix \<ge> 2\<close> by (by100 linarith)
                have hiy_eq2: "(iy-2)+2 = iy" using \<open>iy \<ge> 2\<close> by (by100 linarith)
                have hext_ix: "?ext!ix = w!(ix-2)"
                proof -
                  from hlabel_corr[rule_format, OF hix_k]
                  have "([a, top1_inverse_edge a] @ w) ! ((ix-2)+2) = w!(ix-2)" .
                  have "([a, top1_inverse_edge a] @ w) ! ix = ([a, top1_inverse_edge a] @ w) ! ((ix-2)+2)"
                    using hix_eq2 by (by100 simp)
                  hence "([a, top1_inverse_edge a] @ w) ! ix = w!(ix-2)" using \<open>_ ! ((ix-2)+2) = _\<close> by (by100 simp)
                  thus ?thesis by (by100 simp)
                qed
                have hext_iy: "?ext!iy = w!(iy-2)"
                proof -
                  from hlabel_corr[rule_format, OF hiy_k]
                  have "([a, top1_inverse_edge a] @ w) ! ((iy-2)+2) = w!(iy-2)" .
                  have "([a, top1_inverse_edge a] @ w) ! iy = ([a, top1_inverse_edge a] @ w) ! ((iy-2)+2)"
                    using hiy_eq2 by (by100 simp)
                  hence "([a, top1_inverse_edge a] @ w) ! iy = w!(iy-2)" using \<open>_ ! ((iy-2)+2) = _\<close> by (by100 simp)
                  thus ?thesis by (by100 simp)
                qed
                have hw_lbl: "fst(w!(ix-2)) = fst(w!(iy-2))" using hext_ix hext_iy hlbl_e by (by100 simp)
                have hw_dir: "snd(w!(ix-2)) = snd(w!(iy-2)) \<longleftrightarrow> snd(?ext!ix) = snd(?ext!iy)"
                  using hext_ix hext_iy by (by100 simp)
                \<comment> \<open>phi maps: edge(ix,tx) -> edge\\_w(ix-2,tx), edge(iy,ty) -> edge\\_w(iy-2,ty).\<close>
                have hphi_x: "phi x = edge_pt_w (ix-2) tx"
                proof -
                  have "phi (edge_pt_e ((ix-2)+2) tx) = edge_pt_w (ix-2) tx"
                    using hphi_nonspur[rule_format, OF hix_k htx] by (by100 simp)
                  thus ?thesis using hix_eq2 hx_eq by (by100 simp)
                qed
                have hphi_y: "phi y = edge_pt_w (iy-2) ty"
                proof -
                  have "phi (edge_pt_e ((iy-2)+2) ty) = edge_pt_w (iy-2) ty"
                    using hphi_nonspur[rule_format, OF hiy_k hty] by (by100 simp)
                  thus ?thesis using hiy_eq2 hy_eq by (by100 simp)
                qed
                \<comment> \<open>C7\\_w: q\\_w(edge\\_w(ix-2,tx)) = q\\_w(edge\\_w(iy-2,ty')).\<close>
                show ?thesis
                proof (cases "snd(?ext!ix) = snd(?ext!iy)")
                  case True
                  hence "ty = tx" using hdir_e by (by100 simp)
                  from hC7_w[rule_format, OF hix_k hiy_k hw_lbl htx]
                  have "q_w ((1-tx)*vxw(ix-2)+tx*vxw(Suc(ix-2) mod ?nw),
                      (1-tx)*vyw(ix-2)+tx*vyw(Suc(ix-2) mod ?nw)) =
                    (if snd(w!(ix-2))=snd(w!(iy-2)) then q_w ((1-tx)*vxw(iy-2)+tx*vxw(Suc(iy-2) mod ?nw),
                        (1-tx)*vyw(iy-2)+tx*vyw(Suc(iy-2) mod ?nw))
                     else q_w (tx*vxw(iy-2)+(1-tx)*vxw(Suc(iy-2) mod ?nw),
                        tx*vyw(iy-2)+(1-tx)*vyw(Suc(iy-2) mod ?nw)))" by (by100 blast)
                  hence "q_w (edge_pt_w (ix-2) tx) = q_w (edge_pt_w (iy-2) tx)"
                    using hw_dir True unfolding edge_pt_w_def by (by100 simp)
                  thus ?thesis using hphi_x hphi_y \<open>ty=tx\<close> by (by100 simp)
                next
                  case False
                  hence "ty = 1-tx" using hdir_e by (by100 simp)
                  from hC7_w[rule_format, OF hix_k hiy_k hw_lbl htx]
                  have "q_w ((1-tx)*vxw(ix-2)+tx*vxw(Suc(ix-2) mod ?nw),
                      (1-tx)*vyw(ix-2)+tx*vyw(Suc(ix-2) mod ?nw)) =
                    (if snd(w!(ix-2))=snd(w!(iy-2)) then q_w ((1-tx)*vxw(iy-2)+tx*vxw(Suc(iy-2) mod ?nw),
                        (1-tx)*vyw(iy-2)+tx*vyw(Suc(iy-2) mod ?nw))
                     else q_w (tx*vxw(iy-2)+(1-tx)*vxw(Suc(iy-2) mod ?nw),
                        tx*vyw(iy-2)+(1-tx)*vyw(Suc(iy-2) mod ?nw)))" by (by100 blast)
                  hence "q_w (edge_pt_w (ix-2) tx) = q_w (tx*vxw(iy-2)+(1-tx)*vxw(Suc(iy-2) mod ?nw),
                      tx*vyw(iy-2)+(1-tx)*vyw(Suc(iy-2) mod ?nw))"
                    using hw_dir False unfolding edge_pt_w_def by (by100 simp)
                  moreover have "edge_pt_w (iy-2) (1-tx) = (tx*vxw(iy-2)+(1-tx)*vxw(Suc(iy-2) mod ?nw),
                      tx*vyw(iy-2)+(1-tx)*vyw(Suc(iy-2) mod ?nw))"
                    unfolding edge_pt_w_def by (by100 simp)
                  ultimately have "q_w (edge_pt_w (ix-2) tx) = q_w (edge_pt_w (iy-2) (1-tx))" by (by100 simp)
                  thus ?thesis using hphi_x hphi_y \<open>ty=1-tx\<close> by (by100 simp)
                qed
              qed
            qed
          next
            case False
            \<comment> \<open>At least one of tx, ty is at 0 or 1 (vertex endpoint).
               The key idea: q\\_e at vertices is determined by vtgt\\_e.
               phi maps vertices to corresponding w-vertices (spur -> u\\_0, non-spur -> u\\_k).
               The vtgt chain transfers: if vtgt\\_e(k) = vtgt\\_e(l), then the corresponding
               w-vertices also have vtgt\\_w(k') = vtgt\\_w(l').
               This requires the vtgt chain correspondence between ext and w schemes.
               For now: sorry pending vtgt chain transfer formalization.\<close>
            \<comment> \<open>At least one of tx,ty is 0 or 1. First: show the other must also be 0 or 1
               (i.e., both are vertices). If one is vertex and one is edge-interior,
               C12\\_e gives a contradiction with q\\_e(x) = q\\_e(y).\<close>
            have hboth_vtx: "(tx = 0 \<or> tx = 1) \<and> (ty = 0 \<or> ty = 1)"
            proof -
              from False have "\<not>(0 < tx \<and> tx < 1) \<or> \<not>(0 < ty \<and> ty < 1)" by (by100 blast)
              thus ?thesis
              proof
                assume hnotx: "\<not>(0 < tx \<and> tx < 1)"
                hence htx_vtx: "tx = 0 \<or> tx = 1" using htx unfolding top1_unit_interval_def by (by100 auto)
                show ?thesis
                proof (cases "0 < ty \<and> ty < 1")
                  case False
                  hence "ty = 0 \<or> ty = 1" using hty unfolding top1_unit_interval_def by (by100 auto)
                  thus ?thesis using htx_vtx by (by100 blast)
                next
                  case True
                  hence hty_int: "ty \<in> {0<..<(1::real)}" by (by100 simp)
                  \<comment> \<open>tx is vertex, ty is edge-interior. C12\\_e: contradiction.\<close>
                  have hx_vtx: "\<exists>kx<?ne. x = (vxe kx, vye kx)"
                  proof -
                    from htx_vtx show ?thesis
                    proof
                      assume "tx = 0"
                      hence "x = (vxe ix, vye ix)" using hx_eq unfolding edge_pt_e_def by (by100 simp)
                      thus ?thesis using hix by (by100 blast)
                    next
                      assume "tx = 1"
                      hence "x = (vxe (Suc ix mod ?ne), vye (Suc ix mod ?ne))"
                        using hx_eq unfolding edge_pt_e_def by (by100 simp)
                      moreover have "Suc ix mod ?ne < ?ne" using hlen hne_eq by (by100 simp)
                      ultimately show ?thesis by (by100 blast)
                    qed
                  qed
                  then obtain kx where hkx: "kx < ?ne" and hx_vtx_eq: "x = (vxe kx, vye kx)"
                    by (by100 blast)
                  \<comment> \<open>C12\\_e: q\\_e(vertex kx) != q\\_e(edge-interior (iy, ty)).\<close>
                  from hC12_e[rule_format, OF hkx hiy hty_int]
                  have "q_e (vxe kx, vye kx) \<noteq> q_e ((1-ty)*vxe iy+ty*vxe(Suc iy mod ?ne),
                      (1-ty)*vye iy+ty*vye(Suc iy mod ?ne))" .
                  hence "q_e x \<noteq> q_e y" using hx_vtx_eq hy_eq unfolding edge_pt_e_def by (by100 simp)
                  hence False using heq by (by100 simp)
                  thus ?thesis by (by100 simp)
                qed
              next
                assume hnoty: "\<not>(0 < ty \<and> ty < 1)"
                hence hty_vtx: "ty = 0 \<or> ty = 1" using hty unfolding top1_unit_interval_def by (by100 auto)
                show ?thesis
                proof (cases "0 < tx \<and> tx < 1")
                  case False
                  hence "tx = 0 \<or> tx = 1" using htx unfolding top1_unit_interval_def by (by100 auto)
                  thus ?thesis using hty_vtx by (by100 blast)
                next
                  case True
                  hence htx_int: "tx \<in> {0<..<(1::real)}" by (by100 simp)
                  \<comment> \<open>ty is vertex, tx is edge-interior. C12\\_e: symmetric contradiction.\<close>
                  have hy_vtx: "\<exists>ky<?ne. y = (vxe ky, vye ky)"
                  proof -
                    from hty_vtx show ?thesis
                    proof
                      assume "ty = 0"
                      hence "y = (vxe iy, vye iy)" using hy_eq unfolding edge_pt_e_def by (by100 simp)
                      thus ?thesis using hiy by (by100 blast)
                    next
                      assume "ty = 1"
                      hence "y = (vxe (Suc iy mod ?ne), vye (Suc iy mod ?ne))"
                        using hy_eq unfolding edge_pt_e_def by (by100 simp)
                      moreover have "Suc iy mod ?ne < ?ne" using hlen hne_eq by (by100 simp)
                      ultimately show ?thesis by (by100 blast)
                    qed
                  qed
                  then obtain ky where hky: "ky < ?ne" and hy_vtx_eq: "y = (vxe ky, vye ky)"
                    by (by100 blast)
                  from hC12_e[rule_format, OF hky hix htx_int]
                  have "q_e (vxe ky, vye ky) \<noteq> q_e ((1-tx)*vxe ix+tx*vxe(Suc ix mod ?ne),
                      (1-tx)*vye ix+tx*vye(Suc ix mod ?ne))" .
                  hence "q_e y \<noteq> q_e x" using hy_vtx_eq hx_eq unfolding edge_pt_e_def by (by100 simp)
                  hence False using heq by (by100 simp)
                  thus ?thesis by (by100 simp)
                qed
              qed
            qed
            \<comment> \<open>Both are at vertices. The vtgt chain transfer gives the result.\<close>
            \<comment> \<open>Express x and y as specific P\\_e vertices.\<close>
            obtain kx where hkx: "kx < ?ne" and hx_vtx: "x = (vxe kx, vye kx)"
            proof -
              from hboth_vtx have "tx = 0 \<or> tx = 1" by (by100 blast)
              thus ?thesis
              proof
                assume "tx = 0"
                hence "x = (vxe ix, vye ix)" using hx_eq unfolding edge_pt_e_def by (by100 simp)
                thus ?thesis using hix that by (by100 blast)
              next
                assume "tx = 1"
                hence "x = (vxe (Suc ix mod ?ne), vye (Suc ix mod ?ne))"
                  using hx_eq unfolding edge_pt_e_def by (by100 simp)
                moreover have "Suc ix mod ?ne < ?ne" using hlen hne_eq by (by100 simp)
                ultimately show ?thesis using that by (by100 blast)
              qed
            qed
            obtain ky where hky: "ky < ?ne" and hy_vtx: "y = (vxe ky, vye ky)"
            proof -
              from hboth_vtx have "ty = 0 \<or> ty = 1" by (by100 blast)
              thus ?thesis
              proof
                assume "ty = 0"
                hence "y = (vxe iy, vye iy)" using hy_eq unfolding edge_pt_e_def by (by100 simp)
                thus ?thesis using hiy that by (by100 blast)
              next
                assume "ty = 1"
                hence "y = (vxe (Suc iy mod ?ne), vye (Suc iy mod ?ne))"
                  using hy_eq unfolding edge_pt_e_def by (by100 simp)
                moreover have "Suc iy mod ?ne < ?ne" using hlen hne_eq by (by100 simp)
                ultimately show ?thesis using that by (by100 blast)
              qed
            qed
            \<comment> \<open>q\\_e(v\\_kx) = q\\_e(v\\_ky). Need: q\\_w(phi(v\\_kx)) = q\\_w(phi(v\\_ky)).
               The vertex identification in q\\_e transfers to q\\_w via the label correspondence.
               This requires the vtgt chain transfer (induction on rtrancl of C7 generators).
               For now: sorry the general chain transfer. The math is:
               each C7 step in ext for non-spur edges (i,j >= 2) corresponds to a C7 step
               in w at (i-2, j-2). Spur C7 step (0,1) gives phi(v\\_0)=phi(v\\_2)=u\\_0.
               Chain doesn't pass through spur edges (freshness of a).\<close>
            \<comment> \<open>Case: kx = ky -> trivial.\<close>
            show ?thesis
            proof (cases "kx = ky")
              case True thus ?thesis using hx_vtx hy_vtx by (by100 simp)
            next
              case False note hkx_ne_ky = this
              \<comment> \<open>Distinct vertices. phi maps to specific P\\_w points.
                 For kx in {0,2}: phi -> u\\_0. For kx >= 3: phi -> u\\_{kx-2}.
                 The q\\_e identification transfers to q\\_w via C7 chain correspondence.
                 Formal chain transfer: sorry (needs induction on rtrancl).\<close>
              \<comment> \<open>Step 1: From q\\_e equality, derive vtgt\\_e(kx) = vtgt\\_e(ky).\<close>
              have hqe_kx: "q_e (vxe kx, vye kx) = (vxe (vtgt_e kx), vye (vtgt_e kx))"
                using hvtgt_e hkx by (by100 blast)
              have hqe_ky: "q_e (vxe ky, vye ky) = (vxe (vtgt_e ky), vye (vtgt_e ky))"
                using hvtgt_e hky by (by100 blast)
              have hvtgt_eq: "vtgt_e kx = vtgt_e ky"
              proof -
                from heq hx_vtx hy_vtx hqe_kx hqe_ky
                have "(vxe (vtgt_e kx), vye (vtgt_e kx)) = (vxe (vtgt_e ky), vye (vtgt_e ky))"
                  by (by100 simp)
                \<comment> \<open>By vertex distinctness C3\\_e: same coordinates -> same index.\<close>
                have hvkx_lt: "vtgt_e kx < ?ne" using hvtgt_e_bound hkx by (by100 blast)
                have hvky_lt: "vtgt_e ky < ?ne" using hvtgt_e_bound hky by (by100 blast)
                show ?thesis
                proof (rule ccontr)
                  assume "vtgt_e kx \<noteq> vtgt_e ky"
                  from hC3_e[rule_format, OF hvkx_lt hvky_lt this]
                  have "(vxe (vtgt_e kx), vye (vtgt_e kx)) \<noteq> (vxe (vtgt_e ky), vye (vtgt_e ky))" .
                  moreover from heq hx_vtx hy_vtx hqe_kx hqe_ky
                  have "(vxe (vtgt_e kx), vye (vtgt_e kx)) = (vxe (vtgt_e ky), vye (vtgt_e ky))"
                    by (by100 simp)
                  ultimately show False by (by100 simp)
                qed
              qed
              \<comment> \<open>Step 2: From hvtgt\\_e\\_chain: (kx, ky) in rtrancl of C7 generators.\<close>
              from hvtgt_e_chain[rule_format, OF hkx hky hvtgt_eq]
              have hchain: "(kx, ky) \<in> {(a, b). \<exists>i<?ne. \<exists>j<?ne. i \<noteq> j
                  \<and> fst (?ext ! i) = fst (?ext ! j)
                  \<and> ((snd (?ext ! i) = snd (?ext ! j) \<and> a = i \<and> b = j)
                   \<or> (snd (?ext ! i) = snd (?ext ! j) \<and> a = Suc i mod ?ne \<and> b = Suc j mod ?ne)
                   \<or> (snd (?ext ! i) \<noteq> snd (?ext ! j) \<and> a = i \<and> b = Suc j mod ?ne)
                   \<or> (snd (?ext ! i) \<noteq> snd (?ext ! j) \<and> a = Suc i mod ?ne \<and> b = j))}\<^sup>*"
                by (by100 blast)
              \<comment> \<open>Step 3: Induction on rtrancl. Each step: phi preserves q\\_w identification.\<close>
              \<comment> \<open>The generator set pairs (a,b) where a,b are vertex endpoints of matching edges.
                 For each such step: show q\\_w(phi(v\\_a)) = q\\_w(phi(v\\_b)).
                 - Spur pair (i=0,j=1 or i=1,j=0): the step pairs v\\_0 with v\\_2
                   (or v\\_1 with v\\_1). phi(v\\_0) = u\\_0 = phi(v\\_2). q\\_w equal. CHECK.
                 - Non-spur pair (i,j >= 2): transfers to w-scheme C7 pair.
                   phi(v\\_a) = u\\_{a-2}, phi(v\\_b) = u\\_{b-2}. C7\\_w gives q\\_w equal. CHECK.
                 - Mixed spur+non-spur: impossible by freshness (proved earlier).
                 By induction: the full chain transfers.\<close>
              \<comment> \<open>Induction on rtrancl chain. For each generator step (a,b): show
                 q\\_w(phi(v\\_a)) = q\\_w(phi(v\\_b)) via C7\\_w or spur equality.\<close>
              let ?R = "{(a, b). \<exists>i<?ne. \<exists>j<?ne. i \<noteq> j
                  \<and> fst (?ext ! i) = fst (?ext ! j)
                  \<and> ((snd (?ext ! i) = snd (?ext ! j) \<and> a = i \<and> b = j)
                   \<or> (snd (?ext ! i) = snd (?ext ! j) \<and> a = Suc i mod ?ne \<and> b = Suc j mod ?ne)
                   \<or> (snd (?ext ! i) \<noteq> snd (?ext ! j) \<and> a = i \<and> b = Suc j mod ?ne)
                   \<or> (snd (?ext ! i) \<noteq> snd (?ext ! j) \<and> a = Suc i mod ?ne \<and> b = j))}"
              \<comment> \<open>Single-step lemma: for (a,b) in ?R, phi identifies in q\\_w.\<close>
              have hstep: "\<forall>va vb. (va, vb) \<in> ?R \<longrightarrow> q_w (phi (vxe va, vye va)) = q_w (phi (vxe vb, vye vb))"
              proof (intro allI impI)
                fix va vb assume hab: "(va, vb) \<in> ?R"
                then obtain i j where hi: "i < ?ne" and hj: "j < ?ne" and hij: "i \<noteq> j"
                    and hlbl: "fst (?ext ! i) = fst (?ext ! j)"
                    and hcases: "(snd (?ext ! i) = snd (?ext ! j) \<and> va = i \<and> vb = j)
                       \<or> (snd (?ext ! i) = snd (?ext ! j) \<and> va = Suc i mod ?ne \<and> vb = Suc j mod ?ne)
                       \<or> (snd (?ext ! i) \<noteq> snd (?ext ! j) \<and> va = i \<and> vb = Suc j mod ?ne)
                       \<or> (snd (?ext ! i) \<noteq> snd (?ext ! j) \<and> va = Suc i mod ?ne \<and> vb = j)"
                  by (by5000 blast)
                \<comment> \<open>The edge pair (i,j) either involves spur or non-spur edges.
                   Spur+non-spur: impossible (freshness). So both spur or both non-spur.\<close>
                \<comment> \<open>Classify: both spur (i,j < 2) or both non-spur (i,j >= 2).
                   Mixed is impossible by freshness of label a.\<close>
                have hboth_spur_or_nonspur: "(i < 2 \<and> j < 2) \<or> (i \<ge> 2 \<and> j \<ge> 2)"
                proof (rule ccontr)
                  assume "\<not>((i < 2 \<and> j < 2) \<or> (i \<ge> 2 \<and> j \<ge> 2))"
                  hence hmixed: "(i < 2 \<and> j \<ge> 2) \<or> (i \<ge> 2 \<and> j < 2)" by (by100 linarith)
                  \<comment> \<open>One spur, one non-spur. fst(ext!spur) = fst(a), fst(ext!non-spur) = fst(w!k).
                     Freshness: fst(a) not in fst ` set w -> contradiction.\<close>
                  from hmixed show False
                  proof
                    assume "i < 2 \<and> j \<ge> 2"
                    hence hi2: "i < 2" and hj2: "j \<ge> 2" by (by100 auto)+
                    have "fst (?ext ! i) = fst a"
                    proof (cases "i = 0")
                      case True thus ?thesis using hspur0 by (by100 simp)
                    next
                      case False hence "i = 1" using hi2 by (by100 linarith)
                      thus ?thesis using hspur1 unfolding top1_inverse_edge_def by (by100 simp)
                    qed
                    have "j - 2 < ?nw" using hj hne_eq hj2 by (by100 linarith)
                    from hlabel_corr[rule_format, OF this]
                    have "([a, top1_inverse_edge a] @ w) ! ((j-2)+2) = w!(j-2)" .
                    have "(j-2)+2 = j" using hj2 by (by100 linarith)
                    hence "fst(?ext ! j) = fst(w!(j-2))"
                      using \<open>([a, top1_inverse_edge a] @ w) ! ((j-2)+2) = w!(j-2)\<close> by (by100 simp)
                    hence "fst a = fst(w!(j-2))" using hlbl \<open>fst(?ext!i) = fst a\<close> by (by100 simp)
                    moreover have "w!(j-2) \<in> set w" using \<open>j-2 < ?nw\<close> by (by100 simp)
                    hence "fst(w!(j-2)) \<in> fst ` set w" by (by100 blast)
                    ultimately show False using hfresh by (by100 simp)
                  next
                    assume "i \<ge> 2 \<and> j < 2"
                    hence hi2: "i \<ge> 2" and hj2: "j < 2" by (by100 auto)+
                    have "fst (?ext ! j) = fst a"
                    proof (cases "j = 0")
                      case True thus ?thesis using hspur0 by (by100 simp)
                    next
                      case False hence "j = 1" using hj2 by (by100 linarith)
                      thus ?thesis using hspur1 unfolding top1_inverse_edge_def by (by100 simp)
                    qed
                    have "i - 2 < ?nw" using hi hne_eq hi2 by (by100 linarith)
                    from hlabel_corr[rule_format, OF this]
                    have "([a, top1_inverse_edge a] @ w) ! ((i-2)+2) = w!(i-2)" .
                    have "(i-2)+2 = i" using hi2 by (by100 linarith)
                    hence "fst(?ext ! i) = fst(w!(i-2))"
                      using \<open>([a, top1_inverse_edge a] @ w) ! ((i-2)+2) = w!(i-2)\<close> by (by100 simp)
                    hence "fst a = fst(w!(i-2))" using hlbl \<open>fst(?ext!j) = fst a\<close> by (by100 simp)
                    moreover have "w!(i-2) \<in> set w" using \<open>i-2 < ?nw\<close> by (by100 simp)
                    hence "fst(w!(i-2)) \<in> fst ` set w" by (by100 blast)
                    ultimately show False using hfresh by (by100 simp)
                  qed
                qed
                show "q_w (phi (vxe va, vye va)) = q_w (phi (vxe vb, vye vb))"
                  using hboth_spur_or_nonspur
                proof
                  assume hboth_spur: "i < 2 \<and> j < 2"
                  \<comment> \<open>Both spur. The 4 vertex patterns from the a-pair:
                     same-dir: (a=0,b=1) or (a=1,b=2). But snd(ext!0) != snd(ext!1) (opposite dir).
                     So only opposite-dir patterns: (a=0,b=2) or (a=1,b=1).
                     phi(v\\_0) = u\\_0, phi(v\\_2) = u\\_0, phi(v\\_1) = spur tip.
                     For (a=0,b=2): phi equal (both u\\_0). For (a=1,b=1): trivial.\<close>
                  \<comment> \<open>snd(ext!0) != snd(ext!1): only opposite-dir patterns apply.\<close>
                  have hopp: "snd(?ext!0) \<noteq> snd(?ext!1)"
                    using hspur0 hspur1 unfolding top1_inverse_edge_def by (by100 simp)
                  \<comment> \<open>From hcases + same-dir impossible: va and vb are opp-dir endpoints.\<close>
                  have "i = 0 \<or> i = 1" using hboth_spur by (by100 linarith)
                  moreover have "j = 0 \<or> j = 1" using hboth_spur by (by100 linarith)
                  ultimately have hpair: "(i = 0 \<and> j = 1) \<or> (i = 1 \<and> j = 0)" using hij by (by100 auto)
                  \<comment> \<open>In all cases: va,vb in {0,1,2} and phi maps to u\\_0 or spur tip.\<close>
                  have hne_ge5: "?ne \<ge> 5" using hlen hne_eq by (by100 linarith)
                  hence hmod0: "Suc 0 mod ?ne = 1" by (by100 simp)
                  have hmod1: "Suc 1 mod ?ne = 2"
                  proof -
                    have "Suc 1 = (2::nat)" by (by100 simp)
                    moreover have "(2::nat) < ?ne" using hne_ge5 by (by100 linarith)
                    ultimately show ?thesis by (by100 simp)
                  qed
                  \<comment> \<open>From hcases + hopp: only opp-dir patterns. From hpair: i,j in {0,1}.
                     The 4 possible (va,vb) values: (0,2), (1,1), (2,0), (1,1).\<close>
                  from hcases hopp hpair hmod0 hmod1 have
                    hvavb: "va = vb \<or> (va = 0 \<and> vb = 2) \<or> (va = 2 \<and> vb = 0)"
                    by (by5000 auto)
                  from hvavb show ?thesis
                  proof (elim disjE conjE)
                    assume "va = vb" thus ?thesis by (by100 simp)
                  next
                    assume "va = 0" "vb = 2"
                    \<comment> \<open>phi(v\\_0) = u\\_0 (spur endpoint). phi(v\\_2) = edge\\_pt\\_w(0,0) = u\\_0.\<close>
                    have "phi (vxe 0, vye 0) = (vxw 0, vyw 0)"
                      using hphi_spur_endpoints unfolding edge_pt_e_def by (by100 simp)
                    moreover have hphi_v2: "phi (vxe 2, vye 2) = (vxw 0, vyw 0)"
                    proof -
                      have "0 < ?nw" using hlen by (by100 linarith)
                      have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      from hphi_nonspur[rule_format, OF \<open>0 < ?nw\<close> this]
                      have hphi_02: "phi (edge_pt_e (0+2) 0) = edge_pt_w 0 0" by (by100 simp)
                      have "edge_pt_w 0 0 = (vxw 0, vyw 0)" unfolding edge_pt_w_def by (by100 simp)
                      have "edge_pt_e (0+2) 0 = (vxe 2, vye 2)"
                        unfolding edge_pt_e_def by (simp add: numeral_2_eq_2)
                      thus ?thesis using hphi_02 \<open>edge_pt_w 0 0 = (vxw 0, vyw 0)\<close> by (by100 simp)
                    qed
                    ultimately have "phi (vxe 0, vye 0) = phi (vxe 2, vye 2)" by (by100 simp)
                    thus ?thesis using \<open>va = 0\<close> \<open>vb = 2\<close> by (by100 simp)
                  next
                    assume "va = 2" "vb = 0"
                    have hphi_v0: "phi (vxe 0, vye 0) = (vxw 0, vyw 0)"
                      using hphi_spur_endpoints unfolding edge_pt_e_def by (by100 simp)
                    have hphi_v2: "phi (vxe 2, vye 2) = (vxw 0, vyw 0)"
                    proof -
                      have "0 < ?nw" using hlen by (by100 linarith)
                      have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      from hphi_nonspur[rule_format, OF \<open>0 < ?nw\<close> this]
                      have hphi_02: "phi (edge_pt_e (0+2) 0) = edge_pt_w 0 0" by (by100 simp)
                      have "edge_pt_w 0 0 = (vxw 0, vyw 0)" unfolding edge_pt_w_def by (by100 simp)
                      have "edge_pt_e (0+2) 0 = (vxe 2, vye 2)"
                        unfolding edge_pt_e_def by (simp add: numeral_2_eq_2)
                      thus ?thesis using hphi_02 \<open>edge_pt_w 0 0 = (vxw 0, vyw 0)\<close> by (by100 simp)
                    qed
                    thus ?thesis using \<open>va = 2\<close> \<open>vb = 0\<close> hphi_v0 hphi_v2 by (by100 simp)
                  qed
                next
                  assume hboth_nonspur: "i \<ge> 2 \<and> j \<ge> 2"
                  \<comment> \<open>Both non-spur. C7\\_w at t=0 or t=1 gives q\\_w identification.
                     phi maps v\\_a to u\\_{a-2} or u\\_{Suc(a-2) mod nw}.\<close>
                  \<comment> \<open>Both non-spur. Transfer to w-scheme via label correspondence.\<close>
                  have hi2: "i \<ge> 2" and hj2: "j \<ge> 2" using hboth_nonspur by (by100 auto)+
                  have hik: "i - 2 < ?nw" using hi hne_eq hi2 by (by100 linarith)
                  have hjk: "j - 2 < ?nw" using hj hne_eq hj2 by (by100 linarith)
                  \<comment> \<open>Label correspondence: fst(w!(i-2)) = fst(w!(j-2)).\<close>
                  have hext_i: "?ext!i = w!(i-2)"
                  proof -
                    from hlabel_corr[rule_format, OF hik]
                    have "([a, top1_inverse_edge a] @ w) ! ((i-2)+2) = w!(i-2)" .
                    have "(i-2)+2 = i" using hi2 by (by100 linarith)
                    hence "([a, top1_inverse_edge a] @ w) ! i = w!(i-2)"
                      using \<open>([a, top1_inverse_edge a] @ w) ! ((i-2)+2) = w!(i-2)\<close> by (by100 simp)
                    thus ?thesis by (by100 simp)
                  qed
                  have hext_j: "?ext!j = w!(j-2)"
                  proof -
                    from hlabel_corr[rule_format, OF hjk]
                    have "([a, top1_inverse_edge a] @ w) ! ((j-2)+2) = w!(j-2)" .
                    have "(j-2)+2 = j" using hj2 by (by100 linarith)
                    hence "([a, top1_inverse_edge a] @ w) ! j = w!(j-2)"
                      using \<open>([a, top1_inverse_edge a] @ w) ! ((j-2)+2) = w!(j-2)\<close> by (by100 simp)
                    thus ?thesis by (by100 simp)
                  qed
                  have hw_lbl: "fst(w!(i-2)) = fst(w!(j-2))" using hlbl hext_i hext_j by (by100 simp)
                  have hw_dir: "snd(w!(i-2)) = snd(w!(j-2)) \<longleftrightarrow> snd(?ext!i) = snd(?ext!j)"
                    using hext_i hext_j by (by100 simp)
                  \<comment> \<open>phi maps non-spur vertices: v\\_k -> edge\\_pt\\_w(k-2, 0) or edge\\_pt\\_w(k-3, 1).\<close>
                  \<comment> \<open>For va = i: phi(v\\_i) = edge\\_pt\\_w(i-2, 0) = u\\_{i-2}.\<close>
                  \<comment> \<open>For va = Suc i mod ne: phi(v\\_{Suc i mod ne}) = edge\\_pt\\_w(i-2, 1) or edge\\_pt\\_w(Suc i mod ne - 2, 0).\<close>
                  \<comment> \<open>Use C7\\_w at t=0 for same-dir start, t=1 for same-dir end,
                     or the mixed endpoints for opp-dir.\<close>
                  from hcases show ?thesis
                  proof (elim disjE conjE)
                    \<comment> \<open>Case 1: same-dir, va=i, vb=j. phi(v\\_i) = u\\_{i-2}, phi(v\\_j) = u\\_{j-2}.
                       C7\\_w at t=0: q\\_w(u\\_{i-2}) = q\\_w(u\\_{j-2}) (same-dir start vertices).\<close>
                    assume hsame: "snd(?ext!i) = snd(?ext!j)" and "va = i" "vb = j"
                    have "phi (vxe i, vye i) = edge_pt_w (i-2) 0"
                    proof -
                      have h_eq: "(i-2)+2 = i" using hi2 by (by100 linarith)
                      have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      from hphi_nonspur[rule_format, OF hik this]
                      have "phi (edge_pt_e ((i-2)+2) 0) = edge_pt_w (i-2) 0" by (by100 simp)
                      moreover have "edge_pt_e ((i-2)+2) 0 = (vxe i, vye i)"
                        unfolding edge_pt_e_def using h_eq by (by100 simp)
                      ultimately show ?thesis by (by100 simp)
                    qed
                    hence hphi_va: "phi (vxe va, vye va) = ((1-0)*vxw(i-2)+0*vxw(Suc(i-2) mod ?nw),
                        (1-0)*vyw(i-2)+0*vyw(Suc(i-2) mod ?nw))"
                      using \<open>va = i\<close> unfolding edge_pt_w_def by (by100 simp)
                    have "phi (vxe j, vye j) = edge_pt_w (j-2) 0"
                    proof -
                      have h_eq: "(j-2)+2 = j" using hj2 by (by100 linarith)
                      have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      from hphi_nonspur[rule_format, OF hjk this]
                      have "phi (edge_pt_e ((j-2)+2) 0) = edge_pt_w (j-2) 0" by (by100 simp)
                      moreover have "edge_pt_e ((j-2)+2) 0 = (vxe j, vye j)"
                        unfolding edge_pt_e_def using h_eq by (by100 simp)
                      ultimately show ?thesis by (by100 simp)
                    qed
                    hence hphi_vb: "phi (vxe vb, vye vb) = ((1-0)*vxw(j-2)+0*vxw(Suc(j-2) mod ?nw),
                        (1-0)*vyw(j-2)+0*vyw(Suc(j-2) mod ?nw))"
                      using \<open>vb = j\<close> unfolding edge_pt_w_def by (by100 simp)
                    have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                    from hC7_w[rule_format, OF hik hjk hw_lbl h0_I]
                    have "q_w ((1-0)*vxw(i-2)+0*vxw(Suc(i-2) mod ?nw),
                        (1-0)*vyw(i-2)+0*vyw(Suc(i-2) mod ?nw)) =
                      (if snd(w!(i-2))=snd(w!(j-2)) then q_w ((1-0)*vxw(j-2)+0*vxw(Suc(j-2) mod ?nw),
                          (1-0)*vyw(j-2)+0*vyw(Suc(j-2) mod ?nw))
                       else q_w (0*vxw(j-2)+(1-0)*vxw(Suc(j-2) mod ?nw),
                          0*vyw(j-2)+(1-0)*vyw(Suc(j-2) mod ?nw)))" by (by100 blast)
                    hence "q_w (phi (vxe va, vye va)) = q_w ((1-0)*vxw(j-2)+0*vxw(Suc(j-2) mod ?nw),
                        (1-0)*vyw(j-2)+0*vyw(Suc(j-2) mod ?nw))"
                      using hphi_va hw_dir hsame by (by100 simp)
                    thus ?thesis using hphi_vb by (by100 simp)
                  next
                    \<comment> \<open>Case 2: same-dir, va=Suc i mod ne, vb=Suc j mod ne. Use C7\\_w at t=1.\<close>
                    assume hsame: "snd(?ext!i) = snd(?ext!j)" and hva: "va = Suc i mod ?ne" and hvb: "vb = Suc j mod ?ne"
                    \<comment> \<open>phi(v\\_{Suc i mod ne}) = edge\\_pt\\_w(i-2, 1) (end of edge i-2 in P\\_w).\<close>
                    have hphi_va2: "phi (vxe va, vye va) = edge_pt_w (i-2) 1"
                    proof -
                      have h_eq: "(i-2)+2 = i" using hi2 by (by100 linarith)
                      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      from hphi_nonspur[rule_format, OF hik this]
                      have "phi (edge_pt_e ((i-2)+2) 1) = edge_pt_w (i-2) 1" by (by100 simp)
                      moreover have "edge_pt_e ((i-2)+2) 1 = edge_pt_e i 1"
                        using h_eq by (by100 simp)
                      moreover have "edge_pt_e i 1 = (vxe (Suc i mod ?ne), vye (Suc i mod ?ne))"
                        unfolding edge_pt_e_def by (by100 simp)
                      ultimately show ?thesis using hva by (by100 simp)
                    qed
                    have hphi_vb2: "phi (vxe vb, vye vb) = edge_pt_w (j-2) 1"
                    proof -
                      have h_eq: "(j-2)+2 = j" using hj2 by (by100 linarith)
                      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      from hphi_nonspur[rule_format, OF hjk this]
                      have "phi (edge_pt_e ((j-2)+2) 1) = edge_pt_w (j-2) 1" by (by100 simp)
                      moreover have "edge_pt_e ((j-2)+2) 1 = edge_pt_e j 1"
                        using h_eq by (by100 simp)
                      moreover have "edge_pt_e j 1 = (vxe (Suc j mod ?ne), vye (Suc j mod ?ne))"
                        unfolding edge_pt_e_def by (by100 simp)
                      ultimately show ?thesis using hvb by (by100 simp)
                    qed
                    have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                    from hC7_w[rule_format, OF hik hjk hw_lbl h1_I]
                    have hC7_inst: "q_w ((1-1)*vxw(i-2)+1*vxw(Suc(i-2) mod ?nw),
                        (1-1)*vyw(i-2)+1*vyw(Suc(i-2) mod ?nw)) =
                      (if snd(w!(i-2))=snd(w!(j-2)) then q_w ((1-1)*vxw(j-2)+1*vxw(Suc(j-2) mod ?nw),
                          (1-1)*vyw(j-2)+1*vyw(Suc(j-2) mod ?nw))
                       else q_w (1*vxw(j-2)+(1-1)*vxw(Suc(j-2) mod ?nw),
                          1*vyw(j-2)+(1-1)*vyw(Suc(j-2) mod ?nw)))" by (by100 blast)
                    have "q_w (edge_pt_w (i-2) 1) = q_w (edge_pt_w (j-2) 1)"
                      using hC7_inst hw_dir hsame unfolding edge_pt_w_def by (by100 simp)
                    thus ?thesis using hphi_va2 hphi_vb2 by (by100 simp)
                  next
                    \<comment> \<open>Case 3: opp-dir, va=i, vb=Suc j mod ne. C7\\_w at t=0 gives opp-dir match.\<close>
                    assume hopp: "snd(?ext!i) \<noteq> snd(?ext!j)" and hva: "va = i" and hvb: "vb = Suc j mod ?ne"
                    have hphi_va3: "phi (vxe va, vye va) = edge_pt_w (i-2) 0"
                    proof -
                      have h_eq: "(i-2)+2 = i" using hi2 by (by100 linarith)
                      have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      from hphi_nonspur[rule_format, OF hik this]
                      have "phi (edge_pt_e ((i-2)+2) 0) = edge_pt_w (i-2) 0" by (by100 simp)
                      moreover have "edge_pt_e ((i-2)+2) 0 = (vxe i, vye i)"
                        unfolding edge_pt_e_def using h_eq by (by100 simp)
                      ultimately show ?thesis using hva by (by100 simp)
                    qed
                    have hphi_vb3: "phi (vxe vb, vye vb) = edge_pt_w (j-2) 1"
                    proof -
                      have h_eq: "(j-2)+2 = j" using hj2 by (by100 linarith)
                      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      from hphi_nonspur[rule_format, OF hjk this]
                      have "phi (edge_pt_e ((j-2)+2) 1) = edge_pt_w (j-2) 1" by (by100 simp)
                      moreover have "edge_pt_e ((j-2)+2) 1 = (vxe (Suc j mod ?ne), vye (Suc j mod ?ne))"
                        unfolding edge_pt_e_def using h_eq by (by100 simp)
                      ultimately show ?thesis using hvb by (by100 simp)
                    qed
                    have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                    from hC7_w[rule_format, OF hik hjk hw_lbl h0_I]
                    have hC7_inst: "q_w ((1-0)*vxw(i-2)+0*vxw(Suc(i-2) mod ?nw),
                        (1-0)*vyw(i-2)+0*vyw(Suc(i-2) mod ?nw)) =
                      (if snd(w!(i-2))=snd(w!(j-2)) then q_w ((1-0)*vxw(j-2)+0*vxw(Suc(j-2) mod ?nw),
                          (1-0)*vyw(j-2)+0*vyw(Suc(j-2) mod ?nw))
                       else q_w (0*vxw(j-2)+(1-0)*vxw(Suc(j-2) mod ?nw),
                          0*vyw(j-2)+(1-0)*vyw(Suc(j-2) mod ?nw)))" by (by100 blast)
                    \<comment> \<open>Opposite direction: use else branch.\<close>
                    have "\<not>(snd(w!(i-2)) = snd(w!(j-2)))" using hw_dir hopp by (by100 simp)
                    hence "q_w (edge_pt_w (i-2) 0) = q_w (0*vxw(j-2)+(1-0)*vxw(Suc(j-2) mod ?nw),
                        0*vyw(j-2)+(1-0)*vyw(Suc(j-2) mod ?nw))"
                      using hC7_inst unfolding edge_pt_w_def by (by100 simp)
                    moreover have "(0*vxw(j-2)+(1-0)*vxw(Suc(j-2) mod ?nw),
                        0*vyw(j-2)+(1-0)*vyw(Suc(j-2) mod ?nw)) = edge_pt_w (j-2) 1"
                      unfolding edge_pt_w_def by (by100 simp)
                    ultimately have "q_w (edge_pt_w (i-2) 0) = q_w (edge_pt_w (j-2) 1)" by (by100 simp)
                    thus ?thesis using hphi_va3 hphi_vb3 by (by100 simp)
                  next
                    \<comment> \<open>Case 4: opp-dir, va=Suc i mod ne, vb=j. C7\\_w at t=1 gives opp-dir match.\<close>
                    assume hopp: "snd(?ext!i) \<noteq> snd(?ext!j)" and hva: "va = Suc i mod ?ne" and hvb: "vb = j"
                    have hphi_va4: "phi (vxe va, vye va) = edge_pt_w (i-2) 1"
                    proof -
                      have h_eq: "(i-2)+2 = i" using hi2 by (by100 linarith)
                      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      from hphi_nonspur[rule_format, OF hik this]
                      have "phi (edge_pt_e ((i-2)+2) 1) = edge_pt_w (i-2) 1" by (by100 simp)
                      moreover have "edge_pt_e ((i-2)+2) 1 = (vxe (Suc i mod ?ne), vye (Suc i mod ?ne))"
                        unfolding edge_pt_e_def using h_eq by (by100 simp)
                      ultimately show ?thesis using hva by (by100 simp)
                    qed
                    have hphi_vb4: "phi (vxe vb, vye vb) = edge_pt_w (j-2) 0"
                    proof -
                      have h_eq: "(j-2)+2 = j" using hj2 by (by100 linarith)
                      have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      from hphi_nonspur[rule_format, OF hjk this]
                      have "phi (edge_pt_e ((j-2)+2) 0) = edge_pt_w (j-2) 0" by (by100 simp)
                      moreover have "edge_pt_e ((j-2)+2) 0 = (vxe j, vye j)"
                        unfolding edge_pt_e_def using h_eq by (by100 simp)
                      ultimately show ?thesis using hvb by (by100 simp)
                    qed
                    have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                    from hC7_w[rule_format, OF hik hjk hw_lbl h1_I]
                    have hC7_inst: "q_w ((1-1)*vxw(i-2)+1*vxw(Suc(i-2) mod ?nw),
                        (1-1)*vyw(i-2)+1*vyw(Suc(i-2) mod ?nw)) =
                      (if snd(w!(i-2))=snd(w!(j-2)) then q_w ((1-1)*vxw(j-2)+1*vxw(Suc(j-2) mod ?nw),
                          (1-1)*vyw(j-2)+1*vyw(Suc(j-2) mod ?nw))
                       else q_w (1*vxw(j-2)+(1-1)*vxw(Suc(j-2) mod ?nw),
                          1*vyw(j-2)+(1-1)*vyw(Suc(j-2) mod ?nw)))" by (by100 blast)
                    have "\<not>(snd(w!(i-2)) = snd(w!(j-2)))" using hw_dir hopp by (by100 simp)
                    hence "q_w (edge_pt_w (i-2) 1) = q_w (1*vxw(j-2)+(1-1)*vxw(Suc(j-2) mod ?nw),
                        1*vyw(j-2)+(1-1)*vyw(Suc(j-2) mod ?nw))"
                      using hC7_inst unfolding edge_pt_w_def by (by100 simp)
                    moreover have "(1*vxw(j-2)+(1-1)*vxw(Suc(j-2) mod ?nw),
                        1*vyw(j-2)+(1-1)*vyw(Suc(j-2) mod ?nw)) = edge_pt_w (j-2) 0"
                      unfolding edge_pt_w_def by (by100 simp)
                    ultimately have "q_w (edge_pt_w (i-2) 1) = q_w (edge_pt_w (j-2) 0)" by (by100 simp)
                    thus ?thesis using hphi_va4 hphi_vb4 by (by100 simp)
                  qed
                qed
              qed
              \<comment> \<open>Induction on rtrancl.\<close>
              have "q_w (phi (vxe kx, vye kx)) = q_w (phi (vxe ky, vye ky))"
              proof -
                from hchain have "(kx, ky) \<in> ?R\<^sup>*" .
                thus ?thesis
                proof (induction rule: rtrancl_induct)
                  case base thus ?case by (by100 simp)
                next
                  case (step y z)
                  have "(y, z) \<in> ?R" using step.hyps(2) .
                  from hstep[rule_format, of y z]
                  have "q_w (phi (vxe y, vye y)) = q_w (phi (vxe z, vye z))"
                    using \<open>(y, z) \<in> ?R\<close> by (by100 simp)
                  thus ?case using step.IH by (by100 simp)
                qed
              qed
              thus ?thesis using hx_vtx hy_vtx by (by100 simp)
            qed
          qed
        qed
      qed
    qed
    \<comment> \<open>Property 5: backward fibres. g(x) = g(y) implies q\\_e(x) = q\\_e(y).
       Cases:
       - Both interior: q\\_w injective (C8\\_w) + phi injective on interior -> x=y. CHECK.
       - Both spur: q\\_e identifies all spur points. CHECK.
       - Matched non-spur edges: C9\\_w -> label match -> C7\\_e gives identification. CHECK.
       - One spur, one non-spur edge: g(spur)=q\\_w(u\\_0)=vertex, g(edge)=q\\_w(edge\\_interior).
         C12\\_w: vertex != edge\\_interior -> contradiction. CHECK.
       - One spur, one interior: g(spur)=q\\_w(u\\_0)=boundary image,
         g(interior)=q\\_w(interior)=interior image. Boundary != interior. CHECK.
       - Edge to interior: similar to above.\<close>
    have hg_bwd: "\<forall>x\<in>P_e. \<forall>y\<in>P_e. ?g x = ?g y \<longrightarrow> q_e x = q_e y"
    proof (intro ballI impI)
      fix x y assume hx: "x \<in> P_e" and hy: "y \<in> P_e" and hgeq: "q_w (phi x) = q_w (phi y)"
      \<comment> \<open>Key fact: phi(x), phi(y) are in P\\_w.\<close>
      have hpx: "phi x \<in> P_w" using hphi_range hx by (by100 blast)
      have hpy: "phi y \<in> P_w" using hphi_range hy by (by100 blast)
      \<comment> \<open>Case analysis: is x on the boundary or interior of P\\_e?\<close>
      consider
        (x_int) "\<forall>i<?ne. \<forall>t\<in>I_set. x \<noteq> edge_pt_e i t"
        | (x_bdy) "\<exists>i<?ne. \<exists>t\<in>I_set. x = edge_pt_e i t"
        by (by100 blast)
      thus "q_e x = q_e y"
      proof cases
        case x_int
        \<comment> \<open>x is interior. phi(x) is interior to P\\_w (by hphi\\_int\\_to\\_int).\<close>
        have hpx_int: "\<forall>j<?nw. \<forall>s\<in>I_set. phi x \<noteq> edge_pt_w j s"
          using hphi_int_to_int hx x_int by (by100 blast)
        \<comment> \<open>Sub-case: is y interior or boundary?\<close>
        consider
          (y_int) "\<forall>i<?ne. \<forall>t\<in>I_set. y \<noteq> edge_pt_e i t"
          | (y_bdy) "\<exists>i<?ne. \<exists>t\<in>I_set. y = edge_pt_e i t"
          by (by100 blast)
        thus ?thesis
        proof cases
          case y_int
          \<comment> \<open>Both interior: phi injectivity gives x = y.\<close>
          have hpy_int: "\<forall>j<?nw. \<forall>s\<in>I_set. phi y \<noteq> edge_pt_w j s"
            using hphi_int_to_int hy y_int by (by100 blast)
          \<comment> \<open>q\\_w injective on interior: phi(x) = phi(y).\<close>
          have hpx_int': "\<forall>j<?nw. \<forall>s\<in>I_set.
              phi x \<noteq> ((1-s)*vxw j+s*vxw(Suc j mod ?nw),
                        (1-s)*vyw j+s*vyw(Suc j mod ?nw))"
            using hpx_int unfolding edge_pt_w_def by (by100 simp)
          from hC8_w[rule_format, OF hpx] hpx_int'
          have "\<forall>p'\<in>P_w. q_w (phi x) = q_w p' \<longrightarrow> phi x = p'" by (by100 blast)
          hence "phi x = phi y" using hpy hgeq by (by100 blast)
          \<comment> \<open>phi injective on interior: x = y.\<close>
          hence "x = y"
            using hphi_int_inj hx hy x_int y_int by (by100 blast)
          thus ?thesis by (by100 simp)
        next
          case y_bdy
          \<comment> \<open>x interior, y boundary: use phi separation properties.
             phi(x) != phi(y) because: interior maps don't equal spur arc or edge maps.\<close>
          from y_bdy obtain i t where hi: "i < ?ne" and ht: "t \<in> I_set"
              and hy_eq: "y = edge_pt_e i t" by (by100 blast)
          \<comment> \<open>C8\\_w: phi(x) is interior (hphi\\_int\\_to\\_int), so q\\_w injective at phi(x).\<close>
          have hpx_int': "\<forall>j<?nw. \<forall>s\<in>I_set.
              phi x \<noteq> ((1-s)*vxw j+s*vxw(Suc j mod ?nw),
                        (1-s)*vyw j+s*vyw(Suc j mod ?nw))"
            using hpx_int unfolding edge_pt_w_def by (by100 simp)
          from hC8_w[rule_format, OF hpx] hpx_int'
          have hC8_inst: "\<forall>p'\<in>P_w. q_w (phi x) = q_w p' \<longrightarrow> phi x = p'" by (by100 blast)
          hence hphi_eq: "phi x = phi y" using hpy hgeq by (by100 blast)
          \<comment> \<open>phi(x) is interior image. phi(y) is either spur arc or edge image.
             In both cases: phi(x) != phi(y) by separation properties.\<close>
          show ?thesis
          proof (cases "i < 2")
            case True
            \<comment> \<open>y on spur: phi(y) is spur arc point. phi(x) is interior. Separated.\<close>
            have hy_spur_edge: "y = edge_pt_e i t" using hy_eq .
            \<comment> \<open>phi(edge(0, t)) for the spur. First reduce to edge 0.\<close>
            have "\<exists>t0\<in>I_set. phi y = phi (edge_pt_e 0 t0)"
            proof (cases "i = 0")
              case True thus ?thesis using hy_eq ht by (by100 blast)
            next
              case False hence "i = 1" using \<open>i < 2\<close> by (by100 simp)
              \<comment> \<open>phi(edge(1, t)) = phi(edge(0, 1-t)) by hphi\\_spur\\_match.\<close>
              have "1-t \<in> I_set" using ht unfolding top1_unit_interval_def by (by100 auto)
              from hphi_spur_match[rule_format, OF \<open>1-t \<in> I_set\<close>]
              have "phi (edge_pt_e 0 (1-t)) = phi (edge_pt_e 1 (1-(1-t)))" .
              hence "phi (edge_pt_e 0 (1-t)) = phi (edge_pt_e 1 t)" by (by100 simp)
              hence "phi y = phi (edge_pt_e 0 (1-t))" using hy_eq \<open>i=1\<close> by (by100 simp)
              thus ?thesis using \<open>1-t \<in> I_set\<close> by (by100 blast)
            qed
            then obtain t0 where ht0: "t0 \<in> I_set" and hphi_y_eq: "phi y = phi (edge_pt_e 0 t0)"
              by (by100 blast)
            \<comment> \<open>phi(spur) != phi(interior) by hphi\\_spur\\_not\\_int.\<close>
            have "phi (edge_pt_e 0 t0) \<noteq> phi x"
              using hphi_spur_not_int[rule_format, OF ht0 hx] x_int by (by100 blast)
            hence "phi y \<noteq> phi x" using hphi_y_eq by (by100 simp)
            thus ?thesis using hphi_eq by (by100 simp)
          next
            case False hence "i \<ge> 2" by (by100 simp)
            \<comment> \<open>y on non-spur edge: phi(y) = edge\\_pt\\_w(i-2, t) = boundary of P\\_w.
               phi(x) is interior (not on any edge). Contradiction.\<close>
            hence hk: "i - 2 < ?nw" using hi hne_eq by (by100 linarith)
            have hi_eq: "(i - 2) + 2 = i" using \<open>i \<ge> 2\<close> by (by100 linarith)
            have "phi (edge_pt_e ((i-2)+2) t) = edge_pt_w (i-2) t"
              using hphi_nonspur[rule_format, OF hk ht] by (by100 simp)
            hence "phi y = edge_pt_w (i-2) t" using hi_eq hy_eq by (by100 simp)
            hence "phi x = edge_pt_w (i-2) t" using hphi_eq by (by100 simp)
            hence False using hpx_int hk ht by (by100 blast)
            thus ?thesis by (by100 simp)
          qed
        qed
      next
        case x_bdy
        \<comment> \<open>x is on some boundary edge. Sub-case on y.\<close>
        consider
          (y_int) "\<forall>i<?ne. \<forall>t\<in>I_set. y \<noteq> edge_pt_e i t"
          | (y_bdy) "\<exists>i<?ne. \<exists>t\<in>I_set. y = edge_pt_e i t"
          by (by100 blast)
        thus ?thesis
        proof cases
          case y_int
          \<comment> \<open>y interior, x boundary: symmetric to x\\_int/y\\_bdy case above.\<close>
          from x_bdy obtain ix tx where hix: "ix < ?ne" and htx: "tx \<in> I_set"
              and hx_eq: "x = edge_pt_e ix tx" by (by100 blast)
          \<comment> \<open>C8\\_w on phi(y): interior, so q\\_w injective.\<close>
          have hpy_int: "\<forall>j<?nw. \<forall>s\<in>I_set. phi y \<noteq> edge_pt_w j s"
            using hphi_int_to_int hy y_int by (by100 blast)
          have hpy_int': "\<forall>j<?nw. \<forall>s\<in>I_set.
              phi y \<noteq> ((1-s)*vxw j+s*vxw(Suc j mod ?nw),
                        (1-s)*vyw j+s*vyw(Suc j mod ?nw))"
            using hpy_int unfolding edge_pt_w_def by (by100 simp)
          from hC8_w[rule_format, OF hpy] hpy_int'
          have hC8_inst: "\<forall>p'\<in>P_w. q_w (phi y) = q_w p' \<longrightarrow> phi y = p'" by (by100 blast)
          hence hphi_eq: "phi y = phi x" using hpx hgeq[symmetric] by (by100 blast)
          show ?thesis
          proof (cases "ix < 2")
            case True
            \<comment> \<open>x on spur: phi(x) = spur arc point. phi(y) = interior. Separated.\<close>
            have "\<exists>t0\<in>I_set. phi x = phi (edge_pt_e 0 t0)"
            proof (cases "ix = 0")
              case True thus ?thesis using hx_eq htx by (by100 blast)
            next
              case False hence "ix = 1" using \<open>ix < 2\<close> by (by100 simp)
              have "1-tx \<in> I_set" using htx unfolding top1_unit_interval_def by (by100 auto)
              from hphi_spur_match[rule_format, OF \<open>1-tx \<in> I_set\<close>]
              have "phi (edge_pt_e 0 (1-tx)) = phi (edge_pt_e 1 (1-(1-tx)))" .
              hence "phi (edge_pt_e 0 (1-tx)) = phi (edge_pt_e 1 tx)" by (by100 simp)
              hence "phi x = phi (edge_pt_e 0 (1-tx))" using hx_eq \<open>ix=1\<close> by (by100 simp)
              thus ?thesis using \<open>1-tx \<in> I_set\<close> by (by100 blast)
            qed
            then obtain t0 where ht0: "t0 \<in> I_set" and hphi_x_eq: "phi x = phi (edge_pt_e 0 t0)"
              by (by100 blast)
            have "phi (edge_pt_e 0 t0) \<noteq> phi y"
              using hphi_spur_not_int[rule_format, OF ht0 hy] y_int by (by100 blast)
            hence "phi x \<noteq> phi y" using hphi_x_eq by (by100 simp)
            thus ?thesis using hphi_eq by (by100 simp)
          next
            case False hence "ix \<ge> 2" by (by100 simp)
            hence hkx: "ix - 2 < ?nw" using hix hne_eq by (by100 linarith)
            have hix_eq: "(ix - 2) + 2 = ix" using \<open>ix \<ge> 2\<close> by (by100 linarith)
            have "phi (edge_pt_e ((ix-2)+2) tx) = edge_pt_w (ix-2) tx"
              using hphi_nonspur[rule_format, OF hkx htx] by (by100 simp)
            hence "phi x = edge_pt_w (ix-2) tx" using hix_eq hx_eq by (by100 simp)
            hence "phi y = edge_pt_w (ix-2) tx" using hphi_eq by (by100 simp)
            hence False using hpy_int hkx htx by (by100 blast)
            thus ?thesis by (by100 simp)
          qed
        next
          case y_bdy
          \<comment> \<open>Both x and y on boundary of P\\_e.
             Sub-case on which edges they're on.\<close>
          from x_bdy obtain ix tx where hix: "ix < ?ne" and htx: "tx \<in> I_set"
              and hx_eq: "x = edge_pt_e ix tx" by (by100 blast)
          from y_bdy obtain iy ty where hiy: "iy < ?ne" and hty: "ty \<in> I_set"
              and hy_eq: "y = edge_pt_e iy ty" by (by100 blast)
          \<comment> \<open>Sub-case: are both tx, ty in (0,1) (edge-interior), or at 0/1 (vertex)?\<close>
          show ?thesis
          proof (cases "0 < tx \<and> tx < 1 \<and> 0 < ty \<and> ty < 1")
            case True
            \<comment> \<open>Both edge-interior. Sub-case on spur/non-spur.\<close>
            hence htx_int: "tx \<in> {0<..<(1::real)}" and hty_int: "ty \<in> {0<..<(1::real)}" by (by100 auto)+
            show ?thesis
            proof (cases "ix < 2")
              case True note hix_spur = this
              \<comment> \<open>x on spur edge-interior.\<close>
              show ?thesis
              proof (cases "iy < 2")
                case True note hiy_spur = this
                \<comment> \<open>Both spur edge-interior: q\\_e identifies via the a-pair (C7\\_e).\<close>
                \<comment> \<open>ext[0] and ext[1] have the same label (a). C7\\_e at the appropriate params.\<close>
                have "fst (?ext ! 0) = fst (?ext ! 1)"
                  using hspur0 hspur1 unfolding top1_inverse_edge_def by (by100 simp)
                \<comment> \<open>C7 for the a-pair gives q\\_e identification.\<close>
                \<comment> \<open>Both on spur. Reduce to edge 0 params via hphi\\_spur\\_match.\<close>
                \<comment> \<open>Get phi(x) and phi(y) as spur arc points on edge 0.\<close>
                have "\<exists>tx0\<in>I_set. phi x = phi (edge_pt_e 0 tx0) \<and>
                    (ix = 0 \<and> tx0 = tx \<or> ix = 1 \<and> tx0 = 1-tx)"
                proof (cases "ix = 0")
                  case True thus ?thesis using hx_eq htx unfolding top1_unit_interval_def by (by100 auto)
                next
                  case False hence "ix = 1" using hix_spur by (by100 simp)
                  have h1mtx: "1-tx \<in> I_set" using htx unfolding top1_unit_interval_def by (by100 auto)
                  from hphi_spur_match[rule_format, OF h1mtx]
                  have "phi (edge_pt_e 0 (1-tx)) = phi (edge_pt_e 1 (1-(1-tx)))" .
                  hence "phi (edge_pt_e 0 (1-tx)) = phi (edge_pt_e 1 tx)" by (by100 simp)
                  hence "phi x = phi (edge_pt_e 0 (1-tx))" using hx_eq \<open>ix=1\<close> by (by100 simp)
                  thus ?thesis using h1mtx \<open>ix=1\<close> by (by100 blast)
                qed
                then obtain tx0 where htx0: "tx0 \<in> I_set" and hphi_x0: "phi x = phi (edge_pt_e 0 tx0)"
                    and htx0_case: "ix = 0 \<and> tx0 = tx \<or> ix = 1 \<and> tx0 = 1-tx" by (by100 blast)
                have "\<exists>ty0\<in>I_set. phi y = phi (edge_pt_e 0 ty0) \<and>
                    (iy = 0 \<and> ty0 = ty \<or> iy = 1 \<and> ty0 = 1-ty)"
                proof (cases "iy = 0")
                  case True thus ?thesis using hy_eq hty unfolding top1_unit_interval_def by (by100 auto)
                next
                  case False hence "iy = 1" using hiy_spur by (by100 simp)
                  have h1mty: "1-ty \<in> I_set" using hty unfolding top1_unit_interval_def by (by100 auto)
                  from hphi_spur_match[rule_format, OF h1mty]
                  have "phi (edge_pt_e 0 (1-ty)) = phi (edge_pt_e 1 ty)" by (by100 simp)
                  hence "phi y = phi (edge_pt_e 0 (1-ty))" using hy_eq \<open>iy=1\<close> by (by100 simp)
                  thus ?thesis using h1mty \<open>iy=1\<close> by (by100 blast)
                qed
                then obtain ty0 where hty0: "ty0 \<in> I_set" and hphi_y0: "phi y = phi (edge_pt_e 0 ty0)"
                    and hty0_case: "iy = 0 \<and> ty0 = ty \<or> iy = 1 \<and> ty0 = 1-ty" by (by100 blast)
                \<comment> \<open>phi(x) on spur arc is interior (not on any edge).\<close>
                have htx0_int: "tx0 \<in> {0<..<(1::real)}"
                  using htx0_case htx_int by (by100 auto)
                have hphi_x_not_edge: "\<forall>j<?nw. \<forall>s\<in>I_set.
                    phi x \<noteq> ((1-s)*vxw j+s*vxw(Suc j mod ?nw),(1-s)*vyw j+s*vyw(Suc j mod ?nw))"
                  using hphi_spur_int[rule_format, OF htx0_int] hphi_x0 unfolding edge_pt_w_def by (by100 simp)
                \<comment> \<open>C8\\_w: phi(x) = phi(y).\<close>
                from hC8_w[rule_format, OF hpx] hphi_x_not_edge
                have "\<forall>p'\<in>P_w. q_w (phi x) = q_w p' \<longrightarrow> phi x = p'" by (by100 blast)
                hence "phi x = phi y" using hpy hgeq by (by100 blast)
                \<comment> \<open>phi(edge(0,tx0)) = phi(edge(0,ty0)) -> tx0 = ty0 (hphi\\_spur\\_inj).\<close>
                have "phi (edge_pt_e 0 tx0) = phi (edge_pt_e 0 ty0)"
                  using hphi_x0 hphi_y0 \<open>phi x = phi y\<close> by (by100 simp)
                hence "tx0 = ty0" using hphi_spur_inj[rule_format, OF htx0 hty0] by (by100 blast)
                \<comment> \<open>Now derive q\\_e(x) = q\\_e(y) from the param equality + C7\\_e for a-pair.\<close>
                \<comment> \<open>From tx0=ty0 and the case analysis: derive ix,tx,iy,ty relationship.\<close>
                show ?thesis
                proof -
                  have hparam_rel: "(ix=0 \<and> iy=0 \<and> tx=ty) \<or> (ix=0 \<and> iy=1 \<and> tx=1-ty)
                      \<or> (ix=1 \<and> iy=0 \<and> 1-tx=ty) \<or> (ix=1 \<and> iy=1 \<and> tx=ty)"
                  proof -
                    have "ix = 0 \<or> ix = 1" using hix_spur by (by100 linarith)
                    moreover have "iy = 0 \<or> iy = 1" using hiy_spur by (by100 linarith)
                    ultimately show ?thesis using htx0_case hty0_case \<open>tx0 = ty0\<close>
                      by (by5000 auto)
                  qed
                  from hparam_rel
                  consider (both0) "ix=0 \<and> iy=0 \<and> tx=ty" | (x0y1) "ix=0 \<and> iy=1 \<and> tx=1-ty"
                      | (x1y0) "ix=1 \<and> iy=0 \<and> 1-tx=ty" | (both1) "ix=1 \<and> iy=1 \<and> tx=ty"
                    by (by100 blast)
                  thus ?thesis
                  proof cases
                    case both0 thus ?thesis using hx_eq hy_eq by (by100 simp)
                  next
                    case x0y1
                    \<comment> \<open>ix=0, iy=1, tx=1-ty. C7\\_e: q\\_e(edge(0,tx))=q\\_e(edge(1,1-tx))=q\\_e(edge(1,ty)).\<close>
                    have hix0: "ix = 0" and hiy1: "iy = 1" using x0y1 by (by100 auto)+
                    have hext_lbl: "fst (?ext ! ix) = fst (?ext ! iy)"
                      using \<open>fst(?ext!0)=fst(?ext!1)\<close> hix0 hiy1 by (by100 simp)
                    from hC7_e[rule_format, OF hix hiy hext_lbl htx]
                    have hC7: "q_e ((1-tx)*vxe ix+tx*vxe(Suc ix mod ?ne),
                        (1-tx)*vye ix+tx*vye(Suc ix mod ?ne)) =
                      (if snd(?ext!ix)=snd(?ext!iy) then q_e ((1-tx)*vxe iy+tx*vxe(Suc iy mod ?ne),
                          (1-tx)*vye iy+tx*vye(Suc iy mod ?ne))
                       else q_e (tx*vxe iy+(1-tx)*vxe(Suc iy mod ?ne),
                          tx*vye iy+(1-tx)*vye(Suc iy mod ?ne)))" by (by100 blast)
                    \<comment> \<open>snd(ext!0)=True, snd(ext!1)=False -> opposite direction.\<close>
                    have "snd(?ext!0) \<noteq> snd(?ext!1)"
                      using hspur0 hspur1 unfolding top1_inverse_edge_def by (by100 simp)
                    hence "\<not>(snd(?ext!ix)=snd(?ext!iy))" using x0y1 by (by100 simp)
                    hence "q_e (edge_pt_e ix tx) =
                        q_e (tx*vxe iy+(1-tx)*vxe(Suc iy mod ?ne),
                             tx*vye iy+(1-tx)*vye(Suc iy mod ?ne))"
                      using hC7 unfolding edge_pt_e_def by (by100 simp)
                    moreover have "edge_pt_e iy ty = (tx*vxe iy+(1-tx)*vxe(Suc iy mod ?ne),
                        tx*vye iy+(1-tx)*vye(Suc iy mod ?ne))"
                      unfolding edge_pt_e_def using x0y1 by (by100 simp)
                    ultimately have "q_e (edge_pt_e ix tx) = q_e (edge_pt_e iy ty)" by (by100 simp)
                    thus ?thesis using hx_eq hy_eq by (by100 simp)
                  next
                    case x1y0
                    \<comment> \<open>ix=1, iy=0, 1-tx=ty. Use C7\\_e with iy,ix (swapped) to get
                       q\\_e(edge(0,ty)) = q\\_e(edge(1,1-ty)) = q\\_e(edge(1,tx)).\<close>
                    have hiy0: "iy = 0" and hix1: "ix = 1" using x1y0 by (by100 auto)+
                    have hty_eq: "ty = 1 - tx" using x1y0 by (by100 linarith)
                    have hext_lbl2: "fst (?ext ! iy) = fst (?ext ! ix)"
                      using \<open>fst(?ext!0)=fst(?ext!1)\<close> hiy0 hix1 by (by100 simp)
                    from hC7_e[rule_format, OF hiy hix hext_lbl2 hty]
                    have hC7: "q_e ((1-ty)*vxe iy+ty*vxe(Suc iy mod ?ne),
                        (1-ty)*vye iy+ty*vye(Suc iy mod ?ne)) =
                      (if snd(?ext!iy)=snd(?ext!ix) then q_e ((1-ty)*vxe ix+ty*vxe(Suc ix mod ?ne),
                          (1-ty)*vye ix+ty*vye(Suc ix mod ?ne))
                       else q_e (ty*vxe ix+(1-ty)*vxe(Suc ix mod ?ne),
                          ty*vye ix+(1-ty)*vye(Suc ix mod ?ne)))" by (by100 blast)
                    have "snd(?ext!0) \<noteq> snd(?ext!1)"
                      using hspur0 hspur1 unfolding top1_inverse_edge_def by (by100 simp)
                    hence "\<not>(snd(?ext!iy)=snd(?ext!ix))" using hiy0 hix1 by (by100 simp)
                    hence "q_e (edge_pt_e iy ty) = q_e (ty*vxe ix+(1-ty)*vxe(Suc ix mod ?ne),
                        ty*vye ix+(1-ty)*vye(Suc ix mod ?ne))"
                      using hC7 unfolding edge_pt_e_def by (by100 simp)
                    moreover have "edge_pt_e ix tx = (ty*vxe ix+(1-ty)*vxe(Suc ix mod ?ne),
                        ty*vye ix+(1-ty)*vye(Suc ix mod ?ne))"
                      unfolding edge_pt_e_def using hty_eq by (by100 simp)
                    ultimately have "q_e (edge_pt_e iy ty) = q_e (edge_pt_e ix tx)" by (by100 simp)
                    thus ?thesis using hx_eq hy_eq by (by100 simp)
                  next
                    case both1 thus ?thesis using hx_eq hy_eq by (by100 simp)
                  qed
                qed
              next
                case False note hiy_nonspur = this
                hence "iy \<ge> 2" by (by100 simp)
                \<comment> \<open>x spur edge-interior, y non-spur edge-interior.
                   phi(x) = spur arc interior point (NOT on any w-edge, by hphi\\_spur\\_int).
                   phi(y) = edge\\_pt\\_w(iy-2, ty) (ON a w-edge).
                   C8\\_w: q\\_w injective at phi(x) -> phi(x) = phi(y) -> contradiction.\<close>
                \<comment> \<open>phi(x) is NOT on any w-edge (spur arc interior point).\<close>
                have "\<exists>t0\<in>{0<..<(1::real)}. phi x = phi (edge_pt_e 0 t0)"
                proof (cases "ix = 0")
                  case True thus ?thesis using hx_eq htx_int by (by100 blast)
                next
                  case False hence "ix = 1" using hix_spur by (by100 simp)
                  have "1-tx \<in> I_set" using htx unfolding top1_unit_interval_def by (by100 auto)
                  have "1-tx \<in> {0<..<(1::real)}" using htx_int by (by100 auto)
                  from hphi_spur_match[rule_format, OF \<open>1-tx \<in> I_set\<close>]
                  have "phi (edge_pt_e 0 (1-tx)) = phi (edge_pt_e 1 (1-(1-tx)))" .
                  hence "phi (edge_pt_e 0 (1-tx)) = phi (edge_pt_e 1 tx)" by (by100 simp)
                  hence "phi x = phi (edge_pt_e 0 (1-tx))" using hx_eq \<open>ix=1\<close> by (by100 simp)
                  thus ?thesis using \<open>1-tx \<in> {0<..<(1::real)}\<close> by (by100 blast)
                qed
                then obtain t0 where ht0_int: "t0 \<in> {0<..<(1::real)}"
                    and hphi_x_eq: "phi x = phi (edge_pt_e 0 t0)" by (by100 blast)
                have hphi_x_not_edge: "\<forall>j<?nw. \<forall>s\<in>I_set. phi x \<noteq> edge_pt_w j s"
                  using hphi_spur_int[rule_format, OF ht0_int] hphi_x_eq by (by100 simp)
                have hphi_x_not_edge': "\<forall>j<?nw. \<forall>s\<in>I_set.
                    phi x \<noteq> ((1-s)*vxw j+s*vxw(Suc j mod ?nw),
                              (1-s)*vyw j+s*vyw(Suc j mod ?nw))"
                  using hphi_x_not_edge unfolding edge_pt_w_def by (by100 simp)
                from hC8_w[rule_format, OF hpx] hphi_x_not_edge'
                have "\<forall>p'\<in>P_w. q_w (phi x) = q_w p' \<longrightarrow> phi x = p'" by (by100 blast)
                hence "phi x = phi y" using hpy hgeq by (by100 blast)
                \<comment> \<open>phi(y) is on non-spur edge of P\\_w.\<close>
                have hiy_k: "iy - 2 < ?nw" using hiy hne_eq \<open>iy \<ge> 2\<close> by (by100 linarith)
                have hiy_eq2: "(iy - 2) + 2 = iy" using \<open>iy \<ge> 2\<close> by (by100 linarith)
                have "phi (edge_pt_e ((iy-2)+2) ty) = edge_pt_w (iy-2) ty"
                  using hphi_nonspur[rule_format, OF hiy_k hty] by (by100 simp)
                hence "phi y = edge_pt_w (iy-2) ty" using hiy_eq2 hy_eq by (by100 simp)
                \<comment> \<open>phi(x) = phi(y) but phi(x) not on any edge and phi(y) on edge. Contradiction.\<close>
                hence "phi x = edge_pt_w (iy-2) ty" using \<open>phi x = phi y\<close> by (by100 simp)
                hence False using hphi_x_not_edge hiy_k hty by (by100 blast)
                thus ?thesis by (by100 simp)
              qed
            next
              case False note hix_nonspur = this
              hence "ix \<ge> 2" by (by100 simp)
              show ?thesis
              proof (cases "iy < 2")
                case True note hiy_spur = this
                \<comment> \<open>y spur, x non-spur edge-interior: symmetric to spur+nonspur above.\<close>
                have "\<exists>t0\<in>{0<..<(1::real)}. phi y = phi (edge_pt_e 0 t0)"
                proof (cases "iy = 0")
                  case True thus ?thesis using hy_eq hty_int by (by100 blast)
                next
                  case False hence "iy = 1" using hiy_spur by (by100 simp)
                  have "1-ty \<in> I_set" using hty unfolding top1_unit_interval_def by (by100 auto)
                  have "1-ty \<in> {0<..<(1::real)}" using hty_int by (by100 auto)
                  from hphi_spur_match[rule_format, OF \<open>1-ty \<in> I_set\<close>]
                  have "phi (edge_pt_e 0 (1-ty)) = phi (edge_pt_e 1 (1-(1-ty)))" .
                  hence "phi (edge_pt_e 0 (1-ty)) = phi (edge_pt_e 1 ty)" by (by100 simp)
                  hence "phi y = phi (edge_pt_e 0 (1-ty))" using hy_eq \<open>iy=1\<close> by (by100 simp)
                  thus ?thesis using \<open>1-ty \<in> {0<..<(1::real)}\<close> by (by100 blast)
                qed
                then obtain t0 where ht0_int: "t0 \<in> {0<..<(1::real)}"
                    and hphi_y_eq: "phi y = phi (edge_pt_e 0 t0)" by (by100 blast)
                have hphi_y_not_edge: "\<forall>j<?nw. \<forall>s\<in>I_set. phi y \<noteq> edge_pt_w j s"
                  using hphi_spur_int[rule_format, OF ht0_int] hphi_y_eq by (by100 simp)
                have hphi_y_not_edge': "\<forall>j<?nw. \<forall>s\<in>I_set.
                    phi y \<noteq> ((1-s)*vxw j+s*vxw(Suc j mod ?nw),
                              (1-s)*vyw j+s*vyw(Suc j mod ?nw))"
                  using hphi_y_not_edge unfolding edge_pt_w_def by (by100 simp)
                from hC8_w[rule_format, OF hpy] hphi_y_not_edge'
                have "\<forall>p'\<in>P_w. q_w (phi y) = q_w p' \<longrightarrow> phi y = p'" by (by100 blast)
                hence "phi y = phi x" using hpx hgeq[symmetric] by (by100 blast)
                have hix_k: "ix - 2 < ?nw" using hix hne_eq \<open>ix \<ge> 2\<close> by (by100 linarith)
                have hix_eq2: "(ix - 2) + 2 = ix" using \<open>ix \<ge> 2\<close> by (by100 linarith)
                have "phi (edge_pt_e ((ix-2)+2) tx) = edge_pt_w (ix-2) tx"
                  using hphi_nonspur[rule_format, OF hix_k htx] by (by100 simp)
                hence "phi x = edge_pt_w (ix-2) tx" using hix_eq2 hx_eq by (by100 simp)
                hence "phi y = edge_pt_w (ix-2) tx" using \<open>phi y = phi x\<close> by (by100 simp)
                hence False using hphi_y_not_edge hix_k htx by (by100 blast)
                thus ?thesis by (by100 simp)
              next
                case False note hiy_nonspur = this
                hence "iy \<ge> 2" by (by100 simp)
                \<comment> \<open>Both non-spur edge-interior. C9\\_w + label correspondence -> C7\\_e.\<close>
                have hix_k: "ix - 2 < ?nw" using hix hne_eq \<open>ix \<ge> 2\<close> by (by100 linarith)
                have hiy_k: "iy - 2 < ?nw" using hiy hne_eq \<open>iy \<ge> 2\<close> by (by100 linarith)
                have hix_eq2: "(ix - 2) + 2 = ix" using \<open>ix \<ge> 2\<close> by (by100 linarith)
                have hiy_eq2: "(iy - 2) + 2 = iy" using \<open>iy \<ge> 2\<close> by (by100 linarith)
                have hphi_x3: "phi x = edge_pt_w (ix-2) tx"
                proof -
                  have "phi (edge_pt_e ((ix-2)+2) tx) = edge_pt_w (ix-2) tx"
                    using hphi_nonspur[rule_format, OF hix_k htx] by (by100 simp)
                  thus ?thesis using hix_eq2 hx_eq by (by100 simp)
                qed
                have hphi_y3: "phi y = edge_pt_w (iy-2) ty"
                proof -
                  have "phi (edge_pt_e ((iy-2)+2) ty) = edge_pt_w (iy-2) ty"
                    using hphi_nonspur[rule_format, OF hiy_k hty] by (by100 simp)
                  thus ?thesis using hiy_eq2 hy_eq by (by100 simp)
                qed
                \<comment> \<open>C9\\_w: q\\_w(edge\\_w(ix-2, tx)) = q\\_w(edge\\_w(iy-2, ty)) with both in (0,1)
                   implies: (ix-2 = iy-2 and tx = ty) or (label match + direction).\<close>
                \<comment> \<open>Apply C9\\_w to the equality q\\_w(phi(x)) = q\\_w(phi(y)).\<close>
                have hgeq_w: "q_w ((1-tx)*vxw(ix-2)+tx*vxw(Suc(ix-2) mod ?nw),
                    (1-tx)*vyw(ix-2)+tx*vyw(Suc(ix-2) mod ?nw))
                  = q_w ((1-ty)*vxw(iy-2)+ty*vxw(Suc(iy-2) mod ?nw),
                    (1-ty)*vyw(iy-2)+ty*vyw(Suc(iy-2) mod ?nw))"
                  using hgeq hphi_x3 hphi_y3 unfolding edge_pt_w_def by (by100 simp)
                from hC9_w[rule_format, OF hix_k hiy_k htx_int hty_int] hgeq_w
                have hC9_result: "(ix-2 = iy-2 \<and> tx = ty) \<or> (fst(w!(ix-2)) = fst(w!(iy-2)) \<and>
                    (if snd(w!(ix-2))=snd(w!(iy-2)) then ty=tx else ty=1-tx))"
                  by (by100 blast)
                from hC9_result show ?thesis
                proof (elim disjE conjE)
                  assume hieq: "ix-2 = iy-2" and hteq: "tx = ty"
                  have "ix = iy" using hieq \<open>ix \<ge> 2\<close> \<open>iy \<ge> 2\<close> by (by100 linarith)
                  hence "x = y" using hx_eq hy_eq hteq by (by100 simp)
                  thus ?thesis by (by100 simp)
                next
                  assume hlbl: "fst(w!(ix-2)) = fst(w!(iy-2))"
                    and hdir: "if snd(w!(ix-2))=snd(w!(iy-2)) then ty=tx else ty=1-tx"
                  \<comment> \<open>Transfer label match from w to ext via hlabel\\_corr.\<close>
                  have hext_ix: "?ext!ix = w!(ix-2)"
                  proof -
                    from hlabel_corr[rule_format, OF hix_k]
                    have h_: "([a, top1_inverse_edge a] @ w) ! ((ix-2)+2) = w!(ix-2)" .
                    have "(ix-2)+2 = ix" using hix_eq2 .
                    hence "([a, top1_inverse_edge a] @ w) ! ix = w!(ix-2)" using h_ by (by100 simp)
                    thus ?thesis by (by100 simp)
                  qed
                  have hext_iy: "?ext!iy = w!(iy-2)"
                  proof -
                    from hlabel_corr[rule_format, OF hiy_k]
                    have h_: "([a, top1_inverse_edge a] @ w) ! ((iy-2)+2) = w!(iy-2)" .
                    have "(iy-2)+2 = iy" using hiy_eq2 .
                    hence "([a, top1_inverse_edge a] @ w) ! iy = w!(iy-2)" using h_ by (by100 simp)
                    thus ?thesis by (by100 simp)
                  qed
                  have hext_lbl: "fst(?ext!ix) = fst(?ext!iy)"
                    using hext_ix hext_iy hlbl by (by100 simp)
                  have hext_dir: "snd(?ext!ix) = snd(?ext!iy) \<longleftrightarrow> snd(w!(ix-2)) = snd(w!(iy-2))"
                    using hext_ix hext_iy by (by100 simp)
                  \<comment> \<open>Apply C7\\_e to get q\\_e(x) = q\\_e(y).\<close>
                  from hC7_e[rule_format, OF hix hiy hext_lbl htx]
                  have hC7_raw: "q_e ((1-tx)*vxe ix+tx*vxe(Suc ix mod ?ne),
                      (1-tx)*vye ix+tx*vye(Suc ix mod ?ne))
                    = (if snd(?ext!ix) = snd(?ext!iy)
                       then q_e ((1-tx)*vxe iy+tx*vxe(Suc iy mod ?ne),
                                 (1-tx)*vye iy+tx*vye(Suc iy mod ?ne))
                       else q_e (tx*vxe iy+(1-tx)*vxe(Suc iy mod ?ne),
                                 tx*vye iy+(1-tx)*vye(Suc iy mod ?ne)))"
                    using hC7_e[rule_format, OF hix hiy hext_lbl htx] by (by100 blast)
                  have hC7_inst: "q_e (edge_pt_e ix tx) =
                      (if snd(?ext!ix) = snd(?ext!iy)
                       then q_e (edge_pt_e iy tx)
                       else q_e (tx*vxe iy+(1-tx)*vxe(Suc iy mod ?ne),
                                 tx*vye iy+(1-tx)*vye(Suc iy mod ?ne)))"
                    using hC7_raw unfolding edge_pt_e_def by (by100 simp)
                  show ?thesis
                  proof (cases "snd(?ext!ix) = snd(?ext!iy)")
                    case True
                    hence "ty = tx" using hdir hext_dir by (by100 simp)
                    hence "q_e (edge_pt_e ix tx) = q_e (edge_pt_e iy ty)"
                      using hC7_inst True by (by100 simp)
                    thus ?thesis using hx_eq hy_eq by (by100 simp)
                  next
                    case False
                    hence hty_eq: "ty = 1 - tx" using hdir hext_dir by (by100 simp)
                    \<comment> \<open>q\\_e(edge\\_e(ix,tx)) = q\\_e(tx*vxe iy + ...). And edge\\_e(iy, 1-tx) = (1-(1-tx))*... = tx*...\<close>
                    have "q_e (edge_pt_e ix tx) = q_e (tx*vxe iy+(1-tx)*vxe(Suc iy mod ?ne),
                        tx*vye iy+(1-tx)*vye(Suc iy mod ?ne))"
                      using hC7_inst False by (by100 simp)
                    moreover have "edge_pt_e iy (1-tx) = (tx*vxe iy+(1-tx)*vxe(Suc iy mod ?ne),
                        tx*vye iy+(1-tx)*vye(Suc iy mod ?ne))"
                      unfolding edge_pt_e_def by (by100 simp)
                    ultimately have "q_e (edge_pt_e ix tx) = q_e (edge_pt_e iy (1-tx))" by (by100 simp)
                    hence "q_e (edge_pt_e ix tx) = q_e (edge_pt_e iy ty)" using hty_eq by (by100 simp)
                    thus ?thesis using hx_eq hy_eq by (by100 simp)
                  qed
                qed
              qed
            qed
          next
            case False
            \<comment> \<open>At least one of tx, ty is 0 or 1 (vertex case).\<close>
            \<comment> \<open>Backward vertex case. Same structure as forward vertex:
               1. Show vertex + edge-interior is impossible (contradiction).
               2. Handle both-vertex via vtgt chain reverse transfer.\<close>
            \<comment> \<open>Step 1: show both must be vertices. If one vertex, one edge-interior:
               phi maps vertex to P\\_w vertex/spur-endpoint and edge-interior to P\\_w edge/spur-arc.
               C8\\_w or C12\\_w separates them -> g values differ -> contradiction.\<close>
            \<comment> \<open>Step 2: both vertices -> vtgt chain reverse transfer.
               q\\_w(phi(v\\_a)) = q\\_w(phi(v\\_b)) -> phi images are q\\_w-identified ->
               vtgt\\_w chain -> ext scheme has corresponding chain -> q\\_e identified.\<close>
            \<comment> \<open>This is the reverse of the forward argument. For the forward: each ext C7 step
               gives a w C7 step. For the backward: each w C7 step (among the non-spur edges,
               shifted by 2) gives an ext C7 step. The chain transfer works in both directions
               because the label correspondence is an exact bijection between non-spur ext edges
               and w edges.\<close>
            \<comment> \<open>Backward vertex case. Mirrors forward:
               1. vertex + edge-interior -> contradiction
               2. both vertices -> vtgt reverse transfer\<close>
            \<comment> \<open>The backward vertex proof is symmetric to the forward. The key difference:
               forward uses ext-to-w C7 transfer (each ext step gives w step).
               backward uses w-to-ext C7 transfer (each w step gives ext step, shifted by 2).
               Both directions work because the label correspondence is a bijection
               between non-spur ext edges and w edges.\<close>
            \<comment> \<open>Step 1: show both are vertices (vertex + edge-interior impossible).\<close>
            have hboth_vtx_bwd: "(tx = 0 \<or> tx = 1) \<and> (ty = 0 \<or> ty = 1)"
            proof -
              from False have "\<not>(0 < tx \<and> tx < 1) \<or> \<not>(0 < ty \<and> ty < 1)" by (by100 blast)
              thus ?thesis
              proof
                assume "\<not>(0 < tx \<and> tx < 1)"
                hence htx_vtx: "tx = 0 \<or> tx = 1" using htx unfolding top1_unit_interval_def by (by100 auto)
                show ?thesis
                proof (cases "0 < ty \<and> ty < 1")
                  case False2: False
                  hence "ty = 0 \<or> ty = 1" using hty unfolding top1_unit_interval_def by (by100 auto)
                  thus ?thesis using htx_vtx by (by100 blast)
                next
                  case True
                  \<comment> \<open>tx vertex, ty edge-interior -> contradiction via phi separation.\<close>
                  \<comment> \<open>x is a vertex, y is edge-interior. phi(x) is P\\_w vertex or spur endpoint.
                     phi(y) is P\\_w edge or spur arc interior. g(x) != g(y) -> contradiction.\<close>
                  \<comment> \<open>Reuse the same C8/C12 separation as in the forward vertex-edge case.\<close>
                  \<comment> \<open>tx vertex, ty edge-interior. Show g(x) != g(y) -> contradiction with hgeq.
                     x = vertex v\\_kx. phi(x) is a specific P\\_w point.
                     y = edge-interior. phi(y) is P\\_w edge or spur arc interior.
                     Separation by type gives phi(x) != phi(y) via C8\\_w.\<close>
                  have hty_int_01: "ty \<in> {0<..<(1::real)}" using True by (by100 simp)
                  \<comment> \<open>Express x as vertex, determine phi(x) type.\<close>
                  obtain kx_v where hkx_v: "kx_v < ?ne" and hx_vtx_v: "x = (vxe kx_v, vye kx_v)"
                  proof -
                    from \<open>tx = 0 \<or> tx = 1\<close> show ?thesis
                    proof
                      assume "tx = 0" thus ?thesis using hx_eq hix that unfolding edge_pt_e_def by (by100 simp)
                    next
                      assume "tx = 1"
                      hence "x = (vxe (Suc ix mod ?ne), vye (Suc ix mod ?ne))"
                        using hx_eq unfolding edge_pt_e_def by (by100 simp)
                      moreover have "Suc ix mod ?ne < ?ne" using hlen hne_eq by (by100 simp)
                      ultimately show ?thesis using that by (by100 blast)
                    qed
                  qed
                  \<comment> \<open>phi(y) is in P\\_w. phi(x) is in P\\_w. Both are specific types.
                     Key: phi(y) for edge-interior is either spur arc (not on edge)
                     or non-spur edge point. phi(x) for vertex is boundary vertex or spur tip.
                     In all cases: C8\\_w or C12\\_w prevents q\\_w equality.\<close>
                  \<comment> \<open>Use the forward vertex-edge argument via C12\\_e on the q\\_e side:
                     q\\_e(vertex) != q\\_e(edge-interior). So q\\_e(x) != q\\_e(y).
                     But the GOAL is q\\_e(x) = q\\_e(y). If this is false, it's still OK
                     because the proof obligation "q\\_e(x) = q\\_e(y)" under the assumption
                     hgeq: g(x) = g(y) just needs to hold. If we can show the assumption
                     is CONTRADICTORY, we're done.\<close>
                  \<comment> \<open>Actually: the simplest approach is to show hgeq leads to contradiction.
                     For this: show q\\_w(phi(x)) != q\\_w(phi(y)).\<close>
                  \<comment> \<open>Approach: the edge-interior backward matching cases (both tx,ty in (0,1))
                     already handle all edge-interior pairs. Here tx is 0 or 1 (vertex).
                     We need to show g(x)=g(y) is impossible, or directly show q\\_e(x)=q\\_e(y).

                     Simplest: show g(x) != g(y) -> contradiction with hgeq -> False -> anything.
                     g(x) = q\\_w(phi(vertex)), g(y) = q\\_w(phi(edge-interior)).
                     phi(vertex) and phi(edge-interior) map to different types in P\\_w.
                     C8\\_w/C12\\_w separates them.\<close>
                  \<comment> \<open>phi(y): y is edge-interior at (iy, ty) with ty in (0,1).\<close>
                  show ?thesis
                  proof (cases "iy < 2")
                    case True
                    \<comment> \<open>y on spur edge-interior: phi(y) = spur arc interior (not on any w-edge).\<close>
                    have "\<exists>t0\<in>{0<..<(1::real)}. phi y = phi (edge_pt_e 0 t0)"
                    proof (cases "iy = 0")
                      case True thus ?thesis using hy_eq hty_int_01 by (by100 blast)
                    next
                      case False hence "iy = 1" using \<open>iy < 2\<close> by (by100 simp)
                      have h1mty: "1-ty \<in> I_set" using hty unfolding top1_unit_interval_def by (by100 auto)
                      have "1-ty \<in> {0<..<(1::real)}" using hty_int_01 by (by100 auto)
                      from hphi_spur_match[rule_format, OF h1mty]
                      have "phi (edge_pt_e 0 (1-ty)) = phi (edge_pt_e 1 (1-(1-ty)))" .
                      hence "phi (edge_pt_e 0 (1-ty)) = phi (edge_pt_e 1 ty)" by (by100 simp)
                      hence "phi y = phi (edge_pt_e 0 (1-ty))" using hy_eq \<open>iy=1\<close> by (by100 simp)
                      thus ?thesis using \<open>1-ty \<in> {0<..<(1::real)}\<close> by (by100 blast)
                    qed
                    then obtain t0 where ht0: "t0 \<in> {0<..<(1::real)}" and hphi_y_eq: "phi y = phi (edge_pt_e 0 t0)"
                      by (by100 blast)
                    \<comment> \<open>phi(y) not on any w-edge.\<close>
                    have hphi_y_not_edge: "\<forall>j<?nw. \<forall>s\<in>I_set. phi y \<noteq> edge_pt_w j s"
                      using hphi_spur_int[rule_format, OF ht0] hphi_y_eq by (by100 simp)
                    have hphi_y_not_edge': "\<forall>j<?nw. \<forall>s\<in>I_set.
                        phi y \<noteq> ((1-s)*vxw j+s*vxw(Suc j mod ?nw),(1-s)*vyw j+s*vyw(Suc j mod ?nw))"
                      using hphi_y_not_edge unfolding edge_pt_w_def by (by100 simp)
                    \<comment> \<open>C8\\_w at phi(y): unique preimage. q\\_w(phi(y)) = q\\_w(phi(x)) -> phi(y) = phi(x).\<close>
                    from hC8_w[rule_format, OF hpy] hphi_y_not_edge'
                    have "\<forall>p'\<in>P_w. q_w (phi y) = q_w p' \<longrightarrow> phi y = p'" by (by100 blast)
                    hence "phi y = phi x" using hpx hgeq[symmetric] by (by100 blast)
                    \<comment> \<open>phi(x) is a vertex: show it's NOT a spur arc interior point.\<close>
                    \<comment> \<open>phi(y) = spur arc interior. phi(x) = phi(vertex). Spur arc != vertex image.\<close>
                    \<comment> \<open>phi(y) = phi(x), but phi(y) is spur arc at t0 in (0,1),
                       and phi(x) is phi(vertex). Derive contradiction by cases on kx\\_v.\<close>
                    show ?thesis
                    proof (cases "kx_v = 1")
                      case True
                      \<comment> \<open>kx\\_v = 1: phi(x) = phi(v\\_1) = phi(edge(0,1)). phi(y) = phi(edge(0,t0)).
                         By spur\\_inj: 1 = t0. But t0 in (0,1). Contradiction.\<close>
                      have "phi x = phi (edge_pt_e 0 1)"
                      proof -
                        have "edge_pt_e 0 1 = (vxe 1, vye 1)" unfolding edge_pt_e_def by (by100 simp)
                        thus ?thesis using hx_vtx_v True by (by100 simp)
                      qed
                      hence "phi (edge_pt_e 0 t0) = phi (edge_pt_e 0 1)"
                        using \<open>phi y = phi x\<close> hphi_y_eq by (by100 simp)
                      have ht0_I: "t0 \<in> I_set" using ht0 unfolding top1_unit_interval_def by (by100 auto)
                      have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      from hphi_spur_inj[rule_format, OF ht0_I h1_I]
                      have "t0 = 1" using \<open>phi (edge_pt_e 0 t0) = phi (edge_pt_e 0 1)\<close> by (by100 blast)
                      hence False using ht0 by (by100 auto)
                      thus ?thesis by (by100 simp)
                    next
                      case False
                      \<comment> \<open>kx\\_v != 1: phi(x) is on a w-edge (boundary vertex).
                         phi(y) NOT on any w-edge. phi(y) = phi(x) -> contradiction.\<close>
                      have "\<exists>je<?nw. \<exists>se\<in>I_set. phi x = edge_pt_w je se"
                      proof (cases "kx_v = 0")
                        case True
                        have "phi (vxe 0, vye 0) = (vxw 0, vyw 0)"
                          using hphi_spur_endpoints unfolding edge_pt_e_def by (by100 simp)
                        moreover have "edge_pt_w 0 0 = (vxw 0, vyw 0)" unfolding edge_pt_w_def by (by100 simp)
                        moreover have "(0::nat) < ?nw" using hlen by (by100 linarith)
                        moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                        ultimately show ?thesis using True hx_vtx_v by (by100 force)
                      next
                        case False2: False hence "kx_v \<ge> 2" using False by (by100 linarith)
                        have hkx_k: "kx_v - 2 < ?nw" using hkx_v hne_eq \<open>kx_v \<ge> 2\<close> by (by100 linarith)
                        have h_eq: "(kx_v-2)+2 = kx_v" using \<open>kx_v \<ge> 2\<close> by (by100 linarith)
                        have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                        from hphi_nonspur[rule_format, OF hkx_k this]
                        have "phi (edge_pt_e ((kx_v-2)+2) 0) = edge_pt_w (kx_v-2) 0" by (by100 simp)
                        moreover have "edge_pt_e ((kx_v-2)+2) 0 = (vxe kx_v, vye kx_v)"
                          unfolding edge_pt_e_def using h_eq by (by100 simp)
                        ultimately have "phi (vxe kx_v, vye kx_v) = edge_pt_w (kx_v-2) 0" by (by100 simp)
                        thus ?thesis using hx_vtx_v hkx_k \<open>(0::real) \<in> I_set\<close> by (by100 force)
                      qed
                      then obtain je se where hje: "je < ?nw" and hse: "se \<in> I_set"
                          and hphi_x_edge: "phi x = edge_pt_w je se" by (by100 blast)
                      have "phi y = edge_pt_w je se" using \<open>phi y = phi x\<close> hphi_x_edge by (by100 simp)
                      hence False using hphi_y_not_edge hje hse by (by100 blast)
                      thus ?thesis by (by100 simp)
                    qed
                  next
                    case False hence "iy \<ge> 2" by (by100 simp)
                    \<comment> \<open>y on non-spur edge-interior: phi(y) = edge\\_pt\\_w(iy-2, ty) on a w-edge.\<close>
                    have hiy_k: "iy - 2 < ?nw" using hiy hne_eq \<open>iy \<ge> 2\<close> by (by100 linarith)
                    have hiy_eq: "(iy-2)+2 = iy" using \<open>iy \<ge> 2\<close> by (by100 linarith)
                    have hphi_y: "phi y = edge_pt_w (iy-2) ty"
                    proof -
                      from hphi_nonspur[rule_format, OF hiy_k hty]
                      have "phi (edge_pt_e ((iy-2)+2) ty) = edge_pt_w (iy-2) ty" by (by100 simp)
                      moreover have "edge_pt_e ((iy-2)+2) ty = edge_pt_e iy ty"
                        using hiy_eq by (by100 simp)
                      ultimately show ?thesis using hy_eq by (by100 simp)
                    qed
                    \<comment> \<open>phi(x) is a P\\_w vertex. C12\\_w: vertex != edge-interior on P\\_w.\<close>
                    \<comment> \<open>Need: phi(x) is a P\\_w vertex, i.e., phi(x) = (vxw m, vyw m) for some m.\<close>
                    show ?thesis
                    proof (cases "kx_v = 1")
                      case True
                      \<comment> \<open>kx\\_v = 1 (spur tip). phi(v\\_1) not on any w-edge.
                         phi(y) IS on a w-edge. C8\\_w contradiction.\<close>
                      have hphi_x_not_edge: "\<forall>j<?nw. \<forall>s\<in>I_set. phi x \<noteq> edge_pt_w j s"
                        using hphi_spur_tip_int hx_vtx_v True
                        unfolding edge_pt_e_def by (by100 simp)
                      have hphi_x_not_edge': "\<forall>j<?nw. \<forall>s\<in>I_set.
                          phi x \<noteq> ((1-s)*vxw j+s*vxw(Suc j mod ?nw),(1-s)*vyw j+s*vyw(Suc j mod ?nw))"
                        using hphi_x_not_edge unfolding edge_pt_w_def by (by100 simp)
                      from hC8_w[rule_format, OF hpx] hphi_x_not_edge'
                      have "\<forall>p'\<in>P_w. q_w (phi x) = q_w p' \<longrightarrow> phi x = p'" by (by100 blast)
                      hence "phi x = phi y" using hpy hgeq by (by100 blast)
                      hence "phi x = edge_pt_w (iy-2) ty" using hphi_y by (by100 simp)
                      hence False using hphi_x_not_edge hiy_k hty by (by100 blast)
                      thus ?thesis by (by100 simp)
                    next
                      case False
                      \<comment> \<open>kx\\_v != 1. phi(x) = (vxw mx, vyw mx) = boundary vertex of P\\_w.
                         C12\\_w: vertex != edge-interior at (iy-2, ty).\<close>
                      define mx_v where "mx_v = (if kx_v = 0 then 0 else kx_v - 2)"
                      have hmx_v_lt: "mx_v < ?nw"
                      proof (cases "kx_v = 0")
                        case True hence "mx_v = 0" unfolding mx_v_def by (by100 simp)
                        thus ?thesis using hlen by (by100 linarith)
                      next
                        case False2: False hence "kx_v \<ge> 2" using False by (by100 linarith)
                        hence "mx_v = kx_v - 2" unfolding mx_v_def by (by100 simp)
                        thus ?thesis using hkx_v hne_eq \<open>kx_v \<ge> 2\<close> by (by100 linarith)
                      qed
                      have hphi_x_vtx: "phi x = (vxw mx_v, vyw mx_v)"
                      proof (cases "kx_v = 0")
                        case True thus ?thesis using hphi_spur_endpoints hx_vtx_v
                          unfolding mx_v_def edge_pt_e_def by (by100 simp)
                      next
                        case False2: False hence "kx_v \<ge> 2" using False by (by100 linarith)
                        hence hmx_eq: "mx_v = kx_v - 2" unfolding mx_v_def by (by100 simp)
                        have h_eq: "(kx_v-2)+2 = kx_v" using \<open>kx_v \<ge> 2\<close> by (by100 linarith)
                        have hkx_k: "kx_v - 2 < ?nw" using hkx_v hne_eq \<open>kx_v \<ge> 2\<close> by (by100 linarith)
                        have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                        from hphi_nonspur[rule_format, OF hkx_k this]
                        have "phi (edge_pt_e ((kx_v-2)+2) 0) = edge_pt_w (kx_v-2) 0" by (by100 simp)
                        hence "phi (vxe kx_v, vye kx_v) = edge_pt_w (kx_v-2) 0"
                          unfolding edge_pt_e_def using h_eq by (by100 simp)
                        thus ?thesis using hx_vtx_v hmx_eq unfolding edge_pt_w_def by (by100 simp)
                      qed
                      \<comment> \<open>C12\\_w: q\\_w(vertex mx\\_v) != q\\_w(edge-interior (iy-2, ty)).\<close>
                      have "q_w (vxw mx_v, vyw mx_v) \<noteq> q_w ((1-ty)*vxw(iy-2)+ty*vxw(Suc(iy-2) mod ?nw),
                          (1-ty)*vyw(iy-2)+ty*vyw(Suc(iy-2) mod ?nw))"
                        using hC12_w[rule_format, OF hmx_v_lt hiy_k hty_int_01] by (by100 blast)
                      hence "q_w (phi x) \<noteq> q_w (phi y)"
                        using hphi_x_vtx hphi_y unfolding edge_pt_w_def by (by100 simp)
                      hence False using hgeq by (by100 simp)
                      thus ?thesis by (by100 simp)
                    qed
                  qed
                qed
              next
                assume "\<not>(0 < ty \<and> ty < 1)"
                hence hty_vtx: "ty = 0 \<or> ty = 1" using hty unfolding top1_unit_interval_def by (by100 auto)
                show ?thesis
                proof (cases "0 < tx \<and> tx < 1")
                  case False2: False
                  hence "tx = 0 \<or> tx = 1" using htx unfolding top1_unit_interval_def by (by100 auto)
                  thus ?thesis using hty_vtx by (by100 blast)
                next
                  case True
                  \<comment> \<open>Symmetric: tx edge-interior, ty vertex. Same argument with x,y swapped.\<close>
                  have htx_int_01: "tx \<in> {0<..<(1::real)}" using True by (by100 simp)
                  obtain ky_v where hky_v: "ky_v < ?ne" and hy_vtx_v: "y = (vxe ky_v, vye ky_v)"
                  proof -
                    from hty_vtx show ?thesis
                    proof
                      assume "ty = 0" thus ?thesis using hy_eq hiy that unfolding edge_pt_e_def by (by100 simp)
                    next
                      assume "ty = 1"
                      hence "y = (vxe (Suc iy mod ?ne), vye (Suc iy mod ?ne))"
                        using hy_eq unfolding edge_pt_e_def by (by100 simp)
                      moreover have "Suc iy mod ?ne < ?ne" using hlen hne_eq by (by100 simp)
                      ultimately show ?thesis using that by (by100 blast)
                    qed
                  qed
                  \<comment> \<open>Same case analysis as case 1 but with x,y roles swapped.\<close>
                  show ?thesis
                  proof (cases "ix < 2")
                    case True
                    \<comment> \<open>x on spur edge-interior.\<close>
                    have "\<exists>t0\<in>{0<..<(1::real)}. phi x = phi (edge_pt_e 0 t0)"
                    proof (cases "ix = 0")
                      case True thus ?thesis using hx_eq htx_int_01 by (by100 blast)
                    next
                      case False hence "ix = 1" using \<open>ix < 2\<close> by (by100 simp)
                      have h1mtx: "1-tx \<in> I_set" using htx unfolding top1_unit_interval_def by (by100 auto)
                      have "1-tx \<in> {0<..<(1::real)}" using htx_int_01 by (by100 auto)
                      from hphi_spur_match[rule_format, OF h1mtx]
                      have "phi (edge_pt_e 0 (1-tx)) = phi (edge_pt_e 1 (1-(1-tx)))" .
                      hence "phi (edge_pt_e 0 (1-tx)) = phi (edge_pt_e 1 tx)" by (by100 simp)
                      hence "phi x = phi (edge_pt_e 0 (1-tx))" using hx_eq \<open>ix=1\<close> by (by100 simp)
                      thus ?thesis using \<open>1-tx \<in> {0<..<(1::real)}\<close> by (by100 blast)
                    qed
                    then obtain t0 where ht0: "t0 \<in> {0<..<(1::real)}" and hphi_x_eq: "phi x = phi (edge_pt_e 0 t0)"
                      by (by100 blast)
                    have hphi_x_not_edge: "\<forall>j<?nw. \<forall>s\<in>I_set. phi x \<noteq> edge_pt_w j s"
                      using hphi_spur_int[rule_format, OF ht0] hphi_x_eq by (by100 simp)
                    have hphi_x_not_edge': "\<forall>j<?nw. \<forall>s\<in>I_set.
                        phi x \<noteq> ((1-s)*vxw j+s*vxw(Suc j mod ?nw),(1-s)*vyw j+s*vyw(Suc j mod ?nw))"
                      using hphi_x_not_edge unfolding edge_pt_w_def by (by100 simp)
                    from hC8_w[rule_format, OF hpx] hphi_x_not_edge'
                    have "\<forall>p'\<in>P_w. q_w (phi x) = q_w p' \<longrightarrow> phi x = p'" by (by100 blast)
                    hence hphi_eq: "phi x = phi y" using hpy hgeq by (by100 blast)
                    show ?thesis
                    proof (cases "ky_v = 1")
                      case True
                      have "phi y = phi (edge_pt_e 0 1)"
                      proof -
                        have "edge_pt_e 0 1 = (vxe 1, vye 1)" unfolding edge_pt_e_def by (by100 simp)
                        thus ?thesis using hy_vtx_v True by (by100 simp)
                      qed
                      hence "phi (edge_pt_e 0 t0) = phi (edge_pt_e 0 1)" using hphi_eq hphi_x_eq by (by100 simp)
                      have ht0_I: "t0 \<in> I_set" using ht0 unfolding top1_unit_interval_def by (by100 auto)
                      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      from hphi_spur_inj[rule_format, OF ht0_I this]
                      have "t0 = 1" using \<open>phi (edge_pt_e 0 t0) = phi (edge_pt_e 0 1)\<close> by (by100 blast)
                      hence False using ht0 by (by100 auto)
                      thus ?thesis by (by100 simp)
                    next
                      case False
                      have "\<exists>je<?nw. \<exists>se\<in>I_set. phi y = edge_pt_w je se"
                      proof (cases "ky_v = 0")
                        case True
                        have "phi (vxe 0, vye 0) = (vxw 0, vyw 0)"
                          using hphi_spur_endpoints unfolding edge_pt_e_def by (by100 simp)
                        moreover have "edge_pt_w 0 0 = (vxw 0, vyw 0)" unfolding edge_pt_w_def by (by100 simp)
                        moreover have "(0::nat) < ?nw" using hlen by (by100 linarith)
                        moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                        ultimately show ?thesis using True hy_vtx_v by (by100 force)
                      next
                        case False2: False hence "ky_v \<ge> 2" using False by (by100 linarith)
                        have hky_k: "ky_v - 2 < ?nw" using hky_v hne_eq \<open>ky_v \<ge> 2\<close> by (by100 linarith)
                        have h_eq: "(ky_v-2)+2 = ky_v" using \<open>ky_v \<ge> 2\<close> by (by100 linarith)
                        have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                        from hphi_nonspur[rule_format, OF hky_k this]
                        have "phi (edge_pt_e ((ky_v-2)+2) 0) = edge_pt_w (ky_v-2) 0" by (by100 simp)
                        moreover have "edge_pt_e ((ky_v-2)+2) 0 = (vxe ky_v, vye ky_v)"
                          unfolding edge_pt_e_def using h_eq by (by100 simp)
                        ultimately have "phi (vxe ky_v, vye ky_v) = edge_pt_w (ky_v-2) 0" by (by100 simp)
                        thus ?thesis using hy_vtx_v hky_k \<open>(0::real) \<in> I_set\<close> by (by100 force)
                      qed
                      then obtain je se where hje: "je < ?nw" and hse: "se \<in> I_set"
                          and hphi_y_edge: "phi y = edge_pt_w je se" by (by100 blast)
                      have "phi x = edge_pt_w je se" using hphi_eq hphi_y_edge by (by100 simp)
                      hence False using hphi_x_not_edge hje hse by (by100 blast)
                      thus ?thesis by (by100 simp)
                    qed
                  next
                    case False hence "ix \<ge> 2" by (by100 simp)
                    \<comment> \<open>x on non-spur edge-interior.\<close>
                    have hix_k: "ix - 2 < ?nw" using hix hne_eq \<open>ix \<ge> 2\<close> by (by100 linarith)
                    have hix_eq: "(ix-2)+2 = ix" using \<open>ix \<ge> 2\<close> by (by100 linarith)
                    have hphi_x: "phi x = edge_pt_w (ix-2) tx"
                    proof -
                      from hphi_nonspur[rule_format, OF hix_k htx]
                      have "phi (edge_pt_e ((ix-2)+2) tx) = edge_pt_w (ix-2) tx" by (by100 simp)
                      moreover have "edge_pt_e ((ix-2)+2) tx = edge_pt_e ix tx"
                        using hix_eq by (by100 simp)
                      ultimately show ?thesis using hx_eq by (by100 simp)
                    qed
                    show ?thesis
                    proof (cases "ky_v = 1")
                      case True
                      have hphi_y_not_edge: "\<forall>j<?nw. \<forall>s\<in>I_set. phi y \<noteq> edge_pt_w j s"
                        using hphi_spur_tip_int hy_vtx_v True unfolding edge_pt_e_def by (by100 simp)
                      have hphi_y_not_edge': "\<forall>j<?nw. \<forall>s\<in>I_set.
                          phi y \<noteq> ((1-s)*vxw j+s*vxw(Suc j mod ?nw),(1-s)*vyw j+s*vyw(Suc j mod ?nw))"
                        using hphi_y_not_edge unfolding edge_pt_w_def by (by100 simp)
                      from hC8_w[rule_format, OF hpy] hphi_y_not_edge'
                      have "\<forall>p'\<in>P_w. q_w (phi y) = q_w p' \<longrightarrow> phi y = p'" by (by100 blast)
                      hence "phi y = phi x" using hpx hgeq[symmetric] by (by100 blast)
                      hence "phi y = edge_pt_w (ix-2) tx" using hphi_x by (by100 simp)
                      hence False using hphi_y_not_edge hix_k htx by (by100 blast)
                      thus ?thesis by (by100 simp)
                    next
                      case False
                      define my_v where "my_v = (if ky_v = 0 then 0 else ky_v - 2)"
                      have hmy_v_lt: "my_v < ?nw"
                      proof (cases "ky_v = 0")
                        case True hence "my_v = 0" unfolding my_v_def by (by100 simp)
                        thus ?thesis using hlen by (by100 linarith)
                      next
                        case False2: False hence "ky_v \<ge> 2" using False by (by100 linarith)
                        hence "my_v = ky_v - 2" unfolding my_v_def by (by100 simp)
                        thus ?thesis using hky_v hne_eq \<open>ky_v \<ge> 2\<close> by (by100 linarith)
                      qed
                      have hphi_y_vtx: "phi y = (vxw my_v, vyw my_v)"
                      proof (cases "ky_v = 0")
                        case True thus ?thesis using hphi_spur_endpoints hy_vtx_v
                          unfolding my_v_def edge_pt_e_def by (by100 simp)
                      next
                        case False2: False hence "ky_v \<ge> 2" using False by (by100 linarith)
                        hence hmv_eq: "my_v = ky_v - 2" unfolding my_v_def by (by100 simp)
                        have h_eq: "(ky_v-2)+2 = ky_v" using \<open>ky_v \<ge> 2\<close> by (by100 linarith)
                        have hky_k: "ky_v - 2 < ?nw" using hky_v hne_eq \<open>ky_v \<ge> 2\<close> by (by100 linarith)
                        have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                        from hphi_nonspur[rule_format, OF hky_k this]
                        have "phi (edge_pt_e ((ky_v-2)+2) 0) = edge_pt_w (ky_v-2) 0" by (by100 simp)
                        hence "phi (vxe ky_v, vye ky_v) = edge_pt_w (ky_v-2) 0"
                          unfolding edge_pt_e_def using h_eq by (by100 simp)
                        thus ?thesis using hy_vtx_v hmv_eq unfolding edge_pt_w_def by (by100 simp)
                      qed
                      have "q_w (vxw my_v, vyw my_v) \<noteq> q_w ((1-tx)*vxw(ix-2)+tx*vxw(Suc(ix-2) mod ?nw),
                          (1-tx)*vyw(ix-2)+tx*vyw(Suc(ix-2) mod ?nw))"
                        using hC12_w[rule_format, OF hmy_v_lt hix_k htx_int_01] by (by100 blast)
                      hence "q_w (phi y) \<noteq> q_w (phi x)"
                        using hphi_y_vtx hphi_x unfolding edge_pt_w_def by (by100 simp)
                      hence False using hgeq by (by100 simp)
                      thus ?thesis by (by100 simp)
                    qed
                  qed
                qed
              qed
            qed
            \<comment> \<open>Step 2: express x,y as vertices.\<close>
            obtain kx where hkx_bwd: "kx < ?ne" and hx_vtx_bwd: "x = (vxe kx, vye kx)"
            proof -
              from hboth_vtx_bwd have "tx = 0 \<or> tx = 1" by (by100 blast)
              thus ?thesis
              proof
                assume "tx = 0"
                hence "x = (vxe ix, vye ix)" using hx_eq unfolding edge_pt_e_def by (by100 simp)
                thus ?thesis using hix that by (by100 blast)
              next
                assume "tx = 1"
                hence "x = (vxe (Suc ix mod ?ne), vye (Suc ix mod ?ne))"
                  using hx_eq unfolding edge_pt_e_def by (by100 simp)
                moreover have "Suc ix mod ?ne < ?ne" using hlen hne_eq by (by100 simp)
                ultimately show ?thesis using that by (by100 blast)
              qed
            qed
            obtain ky where hky_bwd: "ky < ?ne" and hy_vtx_bwd: "y = (vxe ky, vye ky)"
            proof -
              from hboth_vtx_bwd have "ty = 0 \<or> ty = 1" by (by100 blast)
              thus ?thesis
              proof
                assume "ty = 0"
                hence "y = (vxe iy, vye iy)" using hy_eq unfolding edge_pt_e_def by (by100 simp)
                thus ?thesis using hiy that by (by100 blast)
              next
                assume "ty = 1"
                hence "y = (vxe (Suc iy mod ?ne), vye (Suc iy mod ?ne))"
                  using hy_eq unfolding edge_pt_e_def by (by100 simp)
                moreover have "Suc iy mod ?ne < ?ne" using hlen hne_eq by (by100 simp)
                ultimately show ?thesis using that by (by100 blast)
              qed
            qed
            \<comment> \<open>Step 3: from g(x)=g(y), derive q\\_e(x)=q\\_e(y) via vtgt reverse transfer.\<close>
            show ?thesis
            proof (cases "kx = ky")
              case True thus ?thesis using hx_vtx_bwd hy_vtx_bwd by (by100 simp)
            next
              case False
              \<comment> \<open>Distinct vertices. phi maps to P\\_w vertices/spur arc.
                 q\\_w equality of phi images -> vtgt\\_w chain -> ext chain -> q\\_e.\<close>
              \<comment> \<open>Step 3a: kx=1 or ky=1 is impossible (spur tip has unique q\\_w image).\<close>
              have hkx_ne1: "kx \<noteq> 1"
              proof
                assume "kx = 1"
                \<comment> \<open>phi(v\\_1) is on spur arc interior. phi(v\\_ky) for ky!=1 is boundary vertex.
                   C8\\_w: q\\_w(interior) is unique -> can only equal q\\_w(boundary) if same point.
                   But interior != boundary -> contradiction.\<close>
                have hky_ne_kx: "ky \<noteq> kx" using False by (by100 blast)
                hence "ky \<noteq> 1" using \<open>kx = 1\<close> by (by100 blast)
                \<comment> \<open>phi(v\\_1) = phi(edge\\_pt\\_e(0, 1)): on spur arc. NOT on any w-edge.\<close>
                have hv1_eq: "edge_pt_e 0 1 = (vxe 1, vye 1)"
                  unfolding edge_pt_e_def by (by100 simp)
                have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                \<comment> \<open>phi(v\\_1) not on any w-edge (from spur\\_int at boundary or spur\\_not\\_int).\<close>
                \<comment> \<open>phi(v\\_ky) for ky in {0,2,...}: is (vxw my, vyw my) = on boundary of P\\_w.\<close>
                \<comment> \<open>phi(v\\_1) is on spur arc (interior, NOT on any w-edge).
                   phi(v\\_ky) for ky!=1 is boundary vertex of P\\_w.
                   C8\\_w: q\\_w(interior) has unique preimage -> phi(v\\_1) = phi(v\\_ky).
                   But spur arc != boundary vertex -> contradiction.\<close>
                \<comment> \<open>phi(v\\_1) = phi(edge\\_pt\\_e(0, 1)), which is on the spur arc.\<close>
                \<comment> \<open>phi(v\\_1) = phi(edge(0,1)): spur arc tip. NOT on any w-edge (hphi\\_spur\\_tip\\_int).
                   phi(v\\_ky) for ky!=1: is a boundary vertex u\\_{my} of P\\_w, which IS on w-edges.
                   So phi(v\\_1) != phi(v\\_ky). Then C8\\_w at phi(v\\_1) gives
                   q\\_w(phi(v\\_1)) != q\\_w(phi(v\\_ky)), contradicting hgeq.\<close>
                have hv1_spur: "phi (vxe 1, vye 1) = phi (edge_pt_e 0 1)"
                  using hv1_eq by (by100 simp)
                \<comment> \<open>phi(v\\_1) NOT on any w-edge.\<close>
                have hv1_not_edge: "\<forall>j<?nw. \<forall>s\<in>I_set. phi (vxe 1, vye 1) \<noteq> edge_pt_w j s"
                  using hphi_spur_tip_int hv1_spur by (by100 simp)
                have hv1_not_edge': "\<forall>j<?nw. \<forall>s\<in>I_set.
                    phi (vxe 1, vye 1) \<noteq> ((1-s)*vxw j+s*vxw(Suc j mod ?nw),
                              (1-s)*vyw j+s*vyw(Suc j mod ?nw))"
                  using hv1_not_edge unfolding edge_pt_w_def by (by100 simp)
                \<comment> \<open>phi(v\\_ky) IS on a w-edge (boundary vertex).\<close>
                have "\<exists>j<?nw. \<exists>s\<in>I_set. phi (vxe ky, vye ky) = edge_pt_w j s"
                proof (cases "ky = 0")
                  case True
                  have "phi (vxe 0, vye 0) = (vxw 0, vyw 0)"
                    using hphi_spur_endpoints unfolding edge_pt_e_def by (by100 simp)
                  moreover have "edge_pt_w 0 0 = (vxw 0, vyw 0)" unfolding edge_pt_w_def by (by100 simp)
                  moreover have "(0::nat) < ?nw" using hlen by (by100 linarith)
                  moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                  ultimately show ?thesis using True by (by100 force)
                next
                  case False hence "ky \<ge> 2" using \<open>ky \<noteq> 1\<close> by (by100 linarith)
                  have hky_k: "ky - 2 < ?nw" using hky_bwd hne_eq \<open>ky \<ge> 2\<close> by (by100 linarith)
                  have h_eq: "(ky-2)+2 = ky" using \<open>ky \<ge> 2\<close> by (by100 linarith)
                  have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                  from hphi_nonspur[rule_format, OF hky_k this]
                  have "phi (edge_pt_e ((ky-2)+2) 0) = edge_pt_w (ky-2) 0" by (by100 simp)
                  moreover have "edge_pt_e ((ky-2)+2) 0 = (vxe ky, vye ky)"
                    unfolding edge_pt_e_def using h_eq by (by100 simp)
                  ultimately have "phi (vxe ky, vye ky) = edge_pt_w (ky-2) 0" by (by100 simp)
                  thus ?thesis using hky_k \<open>(0::real) \<in> I_set\<close> by (by100 force)
                qed
                then obtain jky sky where hjky: "jky < ?nw" and hsky: "sky \<in> I_set"
                    and hphi_ky_edge: "phi (vxe ky, vye ky) = edge_pt_w jky sky" by (by100 blast)
                \<comment> \<open>C8\\_w at phi(v\\_1) (not on any edge): q\\_w unique preimage.\<close>
                have hv1_P: "(vxe 1, vye 1) \<in> P_e"
                proof -
                  have "1 < ?ne" using hlen hne_eq by (by100 linarith)
                  have "edge_pt_e 1 0 = (vxe 1, vye 1)" unfolding edge_pt_e_def by (by100 simp)
                  have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                  \<comment> \<open>edge\\_pt\\_e(1,0) is in P\\_e (boundary point).\<close>
                  show ?thesis using hx hx_vtx_bwd \<open>kx = 1\<close> by (by100 simp)
                qed
                have hphi_v1_P: "phi (vxe 1, vye 1) \<in> P_w" using hphi_range hv1_P by (by100 blast)
                from hC8_w[rule_format, OF hphi_v1_P] hv1_not_edge'
                have "\<forall>p'\<in>P_w. q_w (phi (vxe 1, vye 1)) = q_w p' \<longrightarrow> phi (vxe 1, vye 1) = p'"
                  by (by100 blast)
                hence "phi (vxe 1, vye 1) = phi (vxe ky, vye ky)"
                  using hphi_range hy_vtx_bwd hpy hgeq hx_vtx_bwd \<open>kx = 1\<close> by (by100 simp)
                \<comment> \<open>phi(v\\_1) NOT on edge jky, but phi(v\\_ky) IS -> contradiction.\<close>
                hence hphi_v1_eq: "phi (vxe 1, vye 1) = edge_pt_w jky sky" using hphi_ky_edge by (by100 simp)
                have "phi (vxe 1, vye 1) \<noteq> edge_pt_w jky sky" using hv1_not_edge hjky hsky by (by100 blast)
                thus False using hphi_v1_eq by (by100 simp)
              qed
              have hky_ne1: "ky \<noteq> 1"
              proof
                assume "ky = 1"
                have "kx \<noteq> 1" using False \<open>ky = 1\<close> by (by100 blast)
                \<comment> \<open>Symmetric to kx=1: phi(v\\_1) spur arc tip, phi(v\\_kx) boundary vertex.\<close>
                have hv1_eq: "edge_pt_e 0 1 = (vxe 1, vye 1)"
                  unfolding edge_pt_e_def by (by100 simp)
                have hv1_not_edge: "\<forall>j<?nw. \<forall>s\<in>I_set. phi (vxe 1, vye 1) \<noteq> edge_pt_w j s"
                  using hphi_spur_tip_int hv1_eq by (by100 simp)
                have "\<exists>jkx<?nw. \<exists>skx\<in>I_set. phi (vxe kx, vye kx) = edge_pt_w jkx skx"
                proof (cases "kx = 0")
                  case True
                  have "phi (vxe 0, vye 0) = (vxw 0, vyw 0)"
                    using hphi_spur_endpoints unfolding edge_pt_e_def by (by100 simp)
                  moreover have "edge_pt_w 0 0 = (vxw 0, vyw 0)" unfolding edge_pt_w_def by (by100 simp)
                  moreover have "(0::nat) < ?nw" using hlen by (by100 linarith)
                  moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                  ultimately show ?thesis using True by (by100 force)
                next
                  case False2: False hence "kx \<ge> 2" using \<open>kx \<noteq> 1\<close> by (by100 linarith)
                  have hkx_k: "kx - 2 < ?nw" using hkx_bwd hne_eq \<open>kx \<ge> 2\<close> by (by100 linarith)
                  have h_eq: "(kx-2)+2 = kx" using \<open>kx \<ge> 2\<close> by (by100 linarith)
                  have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                  from hphi_nonspur[rule_format, OF hkx_k this]
                  have "phi (edge_pt_e ((kx-2)+2) 0) = edge_pt_w (kx-2) 0" by (by100 simp)
                  moreover have "edge_pt_e ((kx-2)+2) 0 = (vxe kx, vye kx)"
                    unfolding edge_pt_e_def using h_eq by (by100 simp)
                  ultimately have "phi (vxe kx, vye kx) = edge_pt_w (kx-2) 0" by (by100 simp)
                  thus ?thesis using hkx_k \<open>(0::real) \<in> I_set\<close> by (by100 force)
                qed
                then obtain jkx skx where hjkx: "jkx < ?nw" and hskx: "skx \<in> I_set"
                    and hphi_kx_edge: "phi (vxe kx, vye kx) = edge_pt_w jkx skx" by (by100 blast)
                have hv1_P_ky: "(vxe 1, vye 1) \<in> P_e" using hy hy_vtx_bwd \<open>ky = 1\<close> by (by100 simp)
                have hphi_v1_P: "phi (vxe 1, vye 1) \<in> P_w" using hphi_range hv1_P_ky by (by100 blast)
                have hv1_not_edge': "\<forall>j<?nw. \<forall>s\<in>I_set.
                    phi (vxe 1, vye 1) \<noteq> ((1-s)*vxw j+s*vxw(Suc j mod ?nw),
                              (1-s)*vyw j+s*vyw(Suc j mod ?nw))"
                  using hv1_not_edge unfolding edge_pt_w_def by (by100 simp)
                from hC8_w[rule_format, OF hphi_v1_P] hv1_not_edge'
                have "\<forall>p'\<in>P_w. q_w (phi (vxe 1, vye 1)) = q_w p' \<longrightarrow> phi (vxe 1, vye 1) = p'"
                  by (by100 blast)
                hence "phi (vxe 1, vye 1) = phi (vxe kx, vye kx)"
                  using hphi_range hx_vtx_bwd hpx hgeq[symmetric] hy_vtx_bwd \<open>ky = 1\<close> by (by100 simp)
                hence hphi_v1_eq: "phi (vxe 1, vye 1) = edge_pt_w jkx skx" using hphi_kx_edge by (by100 simp)
                have "phi (vxe 1, vye 1) \<noteq> edge_pt_w jkx skx" using hv1_not_edge hjkx hskx by (by100 blast)
                thus False using hphi_v1_eq by (by100 simp)
              qed
              \<comment> \<open>Step 3b: compute the w-vertex indices for phi images.\<close>
              define mx where "mx = (if kx = 0 then 0 else kx - 2)"
              define my where "my = (if ky = 0 then 0 else ky - 2)"
              have hmx_lt: "mx < ?nw"
              proof (cases "kx = 0")
                case True hence "mx = 0" unfolding mx_def by (by100 simp)
                thus ?thesis using hlen by (by100 linarith)
              next
                case False hence "kx \<ge> 2" using hkx_ne1 by (by100 linarith)
                hence hmx_eq: "mx = kx - 2" unfolding mx_def by (by100 simp)
                have "kx - 2 < ?nw" using hkx_bwd hne_eq \<open>kx \<ge> 2\<close> by (by100 linarith)
                thus ?thesis using hmx_eq by (by100 linarith)
              qed
              have hmy_lt: "my < ?nw"
              proof (cases "ky = 0")
                case True hence "my = 0" unfolding my_def by (by100 simp)
                thus ?thesis using hlen by (by100 linarith)
              next
                case False hence "ky \<ge> 2" using hky_ne1 by (by100 linarith)
                hence hmy_eq: "my = ky - 2" unfolding my_def by (by100 simp)
                have "ky - 2 < ?nw" using hky_bwd hne_eq \<open>ky \<ge> 2\<close> by (by100 linarith)
                thus ?thesis using hmy_eq by (by100 linarith)
              qed
              \<comment> \<open>phi(v\\_kx) = u\\_{mx}, phi(v\\_ky) = u\\_{my}.\<close>
              have hphi_kx: "phi (vxe kx, vye kx) = (vxw mx, vyw mx)"
              proof (cases "kx = 0")
                case True
                hence "mx = 0" unfolding mx_def by (by100 simp)
                moreover have "phi (vxe 0, vye 0) = (vxw 0, vyw 0)"
                  using hphi_spur_endpoints unfolding edge_pt_e_def by (by100 simp)
                ultimately show ?thesis using True by (by100 simp)
              next
                case False hence "kx \<ge> 2" using hkx_ne1 by (by100 linarith)
                hence hmx_eq: "mx = kx - 2" unfolding mx_def by (by100 simp)
                have h_eq: "(kx-2)+2 = kx" using \<open>kx \<ge> 2\<close> by (by100 linarith)
                have hkx_k: "kx - 2 < ?nw" using hkx_bwd hne_eq \<open>kx \<ge> 2\<close> by (by100 linarith)
                have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                from hphi_nonspur[rule_format, OF hkx_k this]
                have "phi (edge_pt_e ((kx-2)+2) 0) = edge_pt_w (kx-2) 0" by (by100 simp)
                hence "phi (vxe kx, vye kx) = edge_pt_w (kx-2) 0"
                  unfolding edge_pt_e_def using h_eq by (by100 simp)
                hence "phi (vxe kx, vye kx) = (vxw (kx-2), vyw (kx-2))"
                  unfolding edge_pt_w_def by (by100 simp)
                thus ?thesis using hmx_eq by (by100 simp)
              qed
              have hphi_ky: "phi (vxe ky, vye ky) = (vxw my, vyw my)"
              proof (cases "ky = 0")
                case True
                hence "my = 0" unfolding my_def by (by100 simp)
                moreover have "phi (vxe 0, vye 0) = (vxw 0, vyw 0)"
                  using hphi_spur_endpoints unfolding edge_pt_e_def by (by100 simp)
                ultimately show ?thesis using True by (by100 simp)
              next
                case False hence "ky \<ge> 2" using hky_ne1 by (by100 linarith)
                hence hmy_eq: "my = ky - 2" unfolding my_def by (by100 simp)
                have h_eq: "(ky-2)+2 = ky" using \<open>ky \<ge> 2\<close> by (by100 linarith)
                have hky_k: "ky - 2 < ?nw" using hky_bwd hne_eq \<open>ky \<ge> 2\<close> by (by100 linarith)
                have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                from hphi_nonspur[rule_format, OF hky_k this]
                have "phi (edge_pt_e ((ky-2)+2) 0) = edge_pt_w (ky-2) 0" by (by100 simp)
                hence "phi (vxe ky, vye ky) = edge_pt_w (ky-2) 0"
                  unfolding edge_pt_e_def using h_eq by (by100 simp)
                hence "phi (vxe ky, vye ky) = (vxw (ky-2), vyw (ky-2))"
                  unfolding edge_pt_w_def by (by100 simp)
                thus ?thesis using hmy_eq by (by100 simp)
              qed
              \<comment> \<open>Step 3c: q\\_w(u\\_{mx}) = q\\_w(u\\_{my}) from hgeq.\<close>
              have hqw_eq: "q_w (vxw mx, vyw mx) = q_w (vxw my, vyw my)"
                using hgeq hx_vtx_bwd hy_vtx_bwd hphi_kx hphi_ky by (by100 simp)
              \<comment> \<open>Step 3d: vtgt\\_w(mx) = vtgt\\_w(my) from q\\_w equality + C3\\_w.\<close>
              have hvtgt_w_eq: "vtgt_w mx = vtgt_w my"
              proof -
                have hqw_mx: "q_w (vxw mx, vyw mx) = (vxw (vtgt_w mx), vyw (vtgt_w mx))"
                  using hvtgt_w hmx_lt by (by100 blast)
                have hqw_my: "q_w (vxw my, vyw my) = (vxw (vtgt_w my), vyw (vtgt_w my))"
                  using hvtgt_w hmy_lt by (by100 blast)
                show ?thesis
                proof (rule ccontr)
                  assume "vtgt_w mx \<noteq> vtgt_w my"
                  have hvmx: "vtgt_w mx < ?nw" using hvtgt_w_bound hmx_lt by (by100 blast)
                  have hvmy: "vtgt_w my < ?nw" using hvtgt_w_bound hmy_lt by (by100 blast)
                  from hC3_w[rule_format, OF hvmx hvmy \<open>vtgt_w mx \<noteq> vtgt_w my\<close>]
                  have "(vxw (vtgt_w mx), vyw (vtgt_w mx)) \<noteq> (vxw (vtgt_w my), vyw (vtgt_w my))" .
                  moreover from hqw_eq hqw_mx hqw_my
                  have "(vxw (vtgt_w mx), vyw (vtgt_w mx)) = (vxw (vtgt_w my), vyw (vtgt_w my))"
                    by (by100 simp)
                  ultimately show False by (by100 simp)
                qed
              qed
              \<comment> \<open>Step 3e: vtgt\\_w chain -> ext chain -> q\\_e identification.\<close>
              from hvtgt_w_chain[rule_format, OF hmx_lt hmy_lt hvtgt_w_eq]
              have hchain_w: "(mx, my) \<in> {(a, b). \<exists>i<?nw. \<exists>j<?nw. i \<noteq> j
                  \<and> fst (w ! i) = fst (w ! j)
                  \<and> ((snd (w ! i) = snd (w ! j) \<and> a = i \<and> b = j)
                   \<or> (snd (w ! i) = snd (w ! j) \<and> a = Suc i mod ?nw \<and> b = Suc j mod ?nw)
                   \<or> (snd (w ! i) \<noteq> snd (w ! j) \<and> a = i \<and> b = Suc j mod ?nw)
                   \<or> (snd (w ! i) \<noteq> snd (w ! j) \<and> a = Suc i mod ?nw \<and> b = j))}\<^sup>*"
                by (by100 blast)
              \<comment> \<open>Each w C7 step gives an ext C7 step (shifted by 2).
                 Then rtrancl gives q\\_e identification.\<close>
              \<comment> \<open>The w-to-ext transfer: for w edge pair (i,j), ext has pair (i+2, j+2)
                 with the SAME label and direction. The vertex patterns shift:
                 w: (a,b) -> ext: (a+2, b+2).
                 So (mx, my) in w-rtrancl -> (mx+2, my+2) in ext-rtrancl.
                 Then q\\_e(v\\_{mx+2}) = q\\_e(v\\_{my+2}).
                 And kx maps to mx (so v\\_kx is identified with v\\_{mx+2} or v\\_{mx+2}=v\\_kx).
                 Need: v\\_kx = v\\_{mx+2} (or at least q\\_e-identified).\<close>
              \<comment> \<open>From mx def: if kx=0 then mx=0, mx+2=2. v\\_0 ~ v\\_2 (a-pair). CHECK.
                 If kx>=2 (and kx!=1): mx=kx-2, mx+2=kx. v\\_kx = v\\_{mx+2}. CHECK.\<close>
              \<comment> \<open>W-to-ext chain transfer: each w C7 step (i,j) -> ext step (i+2,j+2).\<close>
              let ?Rw = "{(a, b). \<exists>i<?nw. \<exists>j<?nw. i \<noteq> j
                  \<and> fst (w ! i) = fst (w ! j)
                  \<and> ((snd (w ! i) = snd (w ! j) \<and> a = i \<and> b = j)
                   \<or> (snd (w ! i) = snd (w ! j) \<and> a = Suc i mod ?nw \<and> b = Suc j mod ?nw)
                   \<or> (snd (w ! i) \<noteq> snd (w ! j) \<and> a = i \<and> b = Suc j mod ?nw)
                   \<or> (snd (w ! i) \<noteq> snd (w ! j) \<and> a = Suc i mod ?nw \<and> b = j))}"
              \<comment> \<open>Step A: from w-chain, derive q\\_e(v\\_{mx+2}) = q\\_e(v\\_{my+2}) via induction.\<close>
              have hqe_mx_my: "q_e (vxe (mx+2), vye (mx+2)) = q_e (vxe (my+2), vye (my+2))"
              proof -
                \<comment> \<open>Single-step helper: each w C7 step -> q\\_e identification at shifted vertices.\<close>
                have hstep_bwd: "\<forall>va vb. (va, vb) \<in> ?Rw \<longrightarrow>
                    q_e (vxe (va+2), vye (va+2)) = q_e (vxe (vb+2), vye (vb+2))"
                proof (intro allI impI)
                  fix va vb assume hvab: "(va, vb) \<in> ?Rw"
                  then obtain i j where hi_w: "i < ?nw" and hj_w: "j < ?nw" and hij_w: "i \<noteq> j"
                      and hlbl_w: "fst (w ! i) = fst (w ! j)"
                      and hcases_w: "(snd (w ! i) = snd (w ! j) \<and> va = i \<and> vb = j)
                         \<or> (snd (w ! i) = snd (w ! j) \<and> va = Suc i mod ?nw \<and> vb = Suc j mod ?nw)
                         \<or> (snd (w ! i) \<noteq> snd (w ! j) \<and> va = i \<and> vb = Suc j mod ?nw)
                         \<or> (snd (w ! i) \<noteq> snd (w ! j) \<and> va = Suc i mod ?nw \<and> vb = j)"
                    by (by100 blast)
                  \<comment> \<open>Transfer to ext: ext!(i+2) = w!i, ext!(j+2) = w!j.\<close>
                  have hi_e: "i + 2 < ?ne" using hi_w hne_eq by (by100 linarith)
                  have hj_e: "j + 2 < ?ne" using hj_w hne_eq by (by100 linarith)
                  have hij_e: "i + 2 \<noteq> j + 2" using hij_w by (by100 linarith)
                  have hext_i: "?ext ! (i+2) = w ! i"
                    using hlabel_corr[rule_format, OF hi_w] by (by100 simp)
                  have hext_j: "?ext ! (j+2) = w ! j"
                    using hlabel_corr[rule_format, OF hj_w] by (by100 simp)
                  have hlbl_e: "fst (?ext ! (i+2)) = fst (?ext ! (j+2))"
                    using hext_i hext_j hlbl_w by (by100 simp)
                  have hdir_e: "snd (?ext ! (i+2)) = snd (?ext ! (j+2)) \<longleftrightarrow> snd (w ! i) = snd (w ! j)"
                    using hext_i hext_j by (by100 simp)
                  \<comment> \<open>C7\\_e at (i+2, j+2): gives vertex identifications at ext edges.\<close>
                  \<comment> \<open>Helper: q\\_e identification from C7\\_e at t=0 (start vertices).\<close>
                  have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                  have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                  \<comment> \<open>C7\\_e at t=0: q\\_e(v\\_{i+2}) relates to q\\_e(v\\_{j+2}) or q\\_e(v\\_{Suc(j+2) mod ne}).\<close>
                  have hC7e_t0: "q_e ((1-0)*vxe(i+2)+0*vxe(Suc(i+2) mod ?ne),
                      (1-0)*vye(i+2)+0*vye(Suc(i+2) mod ?ne)) =
                    (if snd(?ext!(i+2))=snd(?ext!(j+2)) then q_e ((1-0)*vxe(j+2)+0*vxe(Suc(j+2) mod ?ne),
                        (1-0)*vye(j+2)+0*vye(Suc(j+2) mod ?ne))
                     else q_e (0*vxe(j+2)+(1-0)*vxe(Suc(j+2) mod ?ne),
                        0*vye(j+2)+(1-0)*vye(Suc(j+2) mod ?ne)))"
                    using hC7_e[rule_format, OF hi_e hj_e hlbl_e h0_I] by (by100 blast)
                  hence hC7e_start: "q_e (vxe(i+2), vye(i+2)) =
                    (if snd(w!i)=snd(w!j) then q_e (vxe(j+2), vye(j+2))
                     else q_e (vxe(Suc(j+2) mod ?ne), vye(Suc(j+2) mod ?ne)))"
                    using hdir_e by (by100 simp)
                  \<comment> \<open>C7\\_e at t=1: q\\_e(v\\_{Suc(i+2) mod ne}) relates similarly.\<close>
                  have hC7e_t1: "q_e ((1-1)*vxe(i+2)+1*vxe(Suc(i+2) mod ?ne),
                      (1-1)*vye(i+2)+1*vye(Suc(i+2) mod ?ne)) =
                    (if snd(?ext!(i+2))=snd(?ext!(j+2)) then q_e ((1-1)*vxe(j+2)+1*vxe(Suc(j+2) mod ?ne),
                        (1-1)*vye(j+2)+1*vye(Suc(j+2) mod ?ne))
                     else q_e (1*vxe(j+2)+(1-1)*vxe(Suc(j+2) mod ?ne),
                        1*vye(j+2)+(1-1)*vye(Suc(j+2) mod ?ne)))"
                    using hC7_e[rule_format, OF hi_e hj_e hlbl_e h1_I] by (by100 blast)
                  hence hC7e_end: "q_e (vxe(Suc(i+2) mod ?ne), vye(Suc(i+2) mod ?ne)) =
                    (if snd(w!i)=snd(w!j) then q_e (vxe(Suc(j+2) mod ?ne), vye(Suc(j+2) mod ?ne))
                     else q_e (vxe(j+2), vye(j+2)))"
                    using hdir_e by (by100 simp)
                  \<comment> \<open>Helper: (Suc k mod nw) + 2 is q\\_e-identified with Suc(k+2) mod ne.
                     For k < nw-1: they're equal. For k = nw-1: v\\_0 ~ v\\_2 from a-pair.\<close>
                  have hvert_shift: "\<And>k. k < ?nw \<Longrightarrow>
                      q_e (vxe((Suc k mod ?nw)+2), vye((Suc k mod ?nw)+2)) =
                      q_e (vxe(Suc(k+2) mod ?ne), vye(Suc(k+2) mod ?ne))"
                  proof -
                    fix k assume hk: "k < ?nw"
                    show "q_e (vxe((Suc k mod ?nw)+2), vye((Suc k mod ?nw)+2)) =
                        q_e (vxe(Suc(k+2) mod ?ne), vye(Suc(k+2) mod ?ne))"
                    proof (cases "Suc k < ?nw")
                      case True
                      hence "Suc k mod ?nw = Suc k" by (by100 simp)
                      moreover have "Suc(k+2) < ?ne" using True hne_eq by (by100 linarith)
                      hence "Suc(k+2) mod ?ne = Suc(k+2)" by (by100 simp)
                      moreover have "(Suc k) + 2 = Suc(k+2)" by (by100 simp)
                      ultimately show ?thesis by (by100 simp)
                    next
                      case False
                      hence "k = ?nw - 1" using hk by (by100 linarith)
                      hence "Suc k = ?nw" using hk by (by100 linarith)
                      hence "Suc k mod ?nw = 0" by (by100 simp)
                      hence hvl: "(Suc k mod ?nw) + 2 = 2" by (by100 simp)
                      have "Suc(k+2) = ?nw + 2" using \<open>k = ?nw - 1\<close> hlen by (by100 linarith)
                      hence "Suc(k+2) mod ?ne = 0" using hne_eq by (by100 simp)
                      hence hvr: "Suc(k+2) mod ?ne = 0" .
                      \<comment> \<open>Need: q\\_e(v\\_2) = q\\_e(v\\_0). From a-pair C7.\<close>
                      have "q_e (vxe 0, vye 0) = q_e (vxe 2, vye 2)"
                      proof -
                        have "fst (?ext ! 0) = fst (?ext ! 1)"
                          using hspur0 hspur1 unfolding top1_inverse_edge_def by (by100 simp)
                        have "snd (?ext ! 0) \<noteq> snd (?ext ! 1)"
                          using hspur0 hspur1 unfolding top1_inverse_edge_def by (by100 simp)
                        have "0 < ?ne" using hlen hne_eq by (by100 linarith)
                        have "1 < ?ne" using hlen hne_eq by (by100 linarith)
                        from hC7_e[rule_format, OF \<open>0 < ?ne\<close> \<open>1 < ?ne\<close> \<open>fst(?ext!0) = fst(?ext!1)\<close> h0_I]
                        have "q_e (vxe 0, vye 0) = q_e (vxe(Suc 1 mod ?ne), vye(Suc 1 mod ?ne))"
                          using \<open>snd(?ext!0) \<noteq> snd(?ext!1)\<close> by (by100 simp)
                        moreover have "Suc 1 mod ?ne = 2"
                        proof -
                          have "?ne \<ge> 5" using hlen hne_eq by (by100 linarith)
                          hence "(2::nat) < ?ne" by (by100 linarith)
                          thus ?thesis by (by100 simp)
                        qed
                        ultimately show ?thesis by (simp add: numeral_2_eq_2)
                      qed
                      thus ?thesis using hvl hvr by (simp add: numeral_2_eq_2)
                    qed
                  qed
                  \<comment> \<open>Now handle the 4 vertex patterns.\<close>
                  from hcases_w show "q_e (vxe (va+2), vye (va+2)) = q_e (vxe (vb+2), vye (vb+2))"
                  proof (elim disjE conjE)
                    \<comment> \<open>Case 1: same-dir start: va=i, vb=j.\<close>
                    assume "snd(w!i) = snd(w!j)" "va = i" "vb = j"
                    thus ?thesis using hC7e_start by (by100 simp)
                  next
                    \<comment> \<open>Case 2: same-dir end: va=Suc i mod nw, vb=Suc j mod nw.\<close>
                    assume hsame: "snd(w!i) = snd(w!j)" and hva: "va = Suc i mod ?nw" and hvb: "vb = Suc j mod ?nw"
                    from hC7e_end hsame have "q_e (vxe(Suc(i+2) mod ?ne), vye(Suc(i+2) mod ?ne)) =
                        q_e (vxe(Suc(j+2) mod ?ne), vye(Suc(j+2) mod ?ne))" by (by100 simp)
                    moreover from hvert_shift[OF hi_w] have "q_e (vxe(va+2), vye(va+2)) =
                        q_e (vxe(Suc(i+2) mod ?ne), vye(Suc(i+2) mod ?ne))" using hva by (by100 simp)
                    moreover from hvert_shift[OF hj_w] have "q_e (vxe(vb+2), vye(vb+2)) =
                        q_e (vxe(Suc(j+2) mod ?ne), vye(Suc(j+2) mod ?ne))" using hvb by (by100 simp)
                    ultimately show ?thesis by (by100 simp)
                  next
                    \<comment> \<open>Case 3: opp-dir start-end: va=i, vb=Suc j mod nw.\<close>
                    assume hopp: "snd(w!i) \<noteq> snd(w!j)" and hva: "va = i" and hvb: "vb = Suc j mod ?nw"
                    from hC7e_start hopp have "q_e (vxe(i+2), vye(i+2)) =
                        q_e (vxe(Suc(j+2) mod ?ne), vye(Suc(j+2) mod ?ne))" by (by100 simp)
                    moreover from hvert_shift[OF hj_w] have "q_e (vxe(vb+2), vye(vb+2)) =
                        q_e (vxe(Suc(j+2) mod ?ne), vye(Suc(j+2) mod ?ne))" using hvb by (by100 simp)
                    ultimately show ?thesis using hva by (by100 simp)
                  next
                    \<comment> \<open>Case 4: opp-dir end-start: va=Suc i mod nw, vb=j.\<close>
                    assume hopp: "snd(w!i) \<noteq> snd(w!j)" and hva: "va = Suc i mod ?nw" and hvb: "vb = j"
                    from hC7e_end hopp have "q_e (vxe(Suc(i+2) mod ?ne), vye(Suc(i+2) mod ?ne)) =
                        q_e (vxe(j+2), vye(j+2))" by (by100 simp)
                    moreover from hvert_shift[OF hi_w] have "q_e (vxe(va+2), vye(va+2)) =
                        q_e (vxe(Suc(i+2) mod ?ne), vye(Suc(i+2) mod ?ne))" using hva by (by100 simp)
                    ultimately show ?thesis using hvb by (by100 simp)
                  qed
                qed
                from hchain_w have "(mx, my) \<in> ?Rw\<^sup>*" .
                thus ?thesis
                proof (induction rule: rtrancl_induct)
                  case base thus ?case by (by100 simp)
                next
                  case (step y z)
                  have "(y, z) \<in> ?Rw" using step.hyps(2) .
                  from hstep_bwd[rule_format, of y z]
                  have "q_e (vxe (y+2), vye (y+2)) = q_e (vxe (z+2), vye (z+2))"
                    using \<open>(y, z) \<in> ?Rw\<close> by (by100 simp)
                  thus ?case using step.IH by (by100 simp)
                qed
              qed
              \<comment> \<open>Step B: relate kx to mx+2 and ky to my+2 via q\\_e.\<close>
              have hqe_kx_mx: "q_e (vxe kx, vye kx) = q_e (vxe (mx+2), vye (mx+2))"
              proof (cases "kx = 0")
                case True hence "mx + 2 = 2" unfolding mx_def by (by100 simp)
                \<comment> \<open>kx=0, mx+2=2. Need q\\_e(v\\_0) = q\\_e(v\\_2). From a-pair C7 at t=0.\<close>
                have "fst (?ext ! 0) = fst (?ext ! 1)"
                  using hspur0 hspur1 unfolding top1_inverse_edge_def by (by100 simp)
                have "snd (?ext ! 0) \<noteq> snd (?ext ! 1)"
                  using hspur0 hspur1 unfolding top1_inverse_edge_def by (by100 simp)
                have "0 < ?ne" using hlen hne_eq by (by100 linarith)
                have "1 < ?ne" using hlen hne_eq by (by100 linarith)
                have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                from hC7_e[rule_format, OF \<open>0 < ?ne\<close> \<open>1 < ?ne\<close> \<open>fst(?ext!0) = fst(?ext!1)\<close> this]
                have "q_e ((1-0)*vxe 0+0*vxe(Suc 0 mod ?ne),(1-0)*vye 0+0*vye(Suc 0 mod ?ne)) =
                  (if snd(?ext!0) = snd(?ext!1) then q_e ((1-0)*vxe 1+0*vxe(Suc 1 mod ?ne),
                      (1-0)*vye 1+0*vye(Suc 1 mod ?ne))
                   else q_e (0*vxe 1+(1-0)*vxe(Suc 1 mod ?ne),
                      0*vye 1+(1-0)*vye(Suc 1 mod ?ne)))" by (by100 blast)
                hence "q_e (vxe 0, vye 0) = q_e (vxe (Suc 1 mod ?ne), vye (Suc 1 mod ?ne))"
                  using \<open>snd(?ext!0) \<noteq> snd(?ext!1)\<close> by (by100 simp)
                moreover have "Suc 1 mod ?ne = 2"
                proof -
                  have "?ne \<ge> 5" using hlen hne_eq by (by100 linarith)
                  hence "(2::nat) < ?ne" by (by100 linarith)
                  thus ?thesis by (by100 simp)
                qed
                ultimately have "q_e (vxe 0, vye 0) = q_e (vxe 2, vye 2)" by (by100 simp)
                thus ?thesis using True \<open>mx+2 = 2\<close> by (simp add: numeral_2_eq_2)
              next
                case False hence "kx \<ge> 2" using hkx_ne1 by (by100 linarith)
                hence "mx = kx - 2" unfolding mx_def by (by100 simp)
                hence "mx + 2 = kx" using \<open>kx \<ge> 2\<close> by (by100 linarith)
                thus ?thesis by (by100 simp)
              qed
              have hqe_ky_my: "q_e (vxe ky, vye ky) = q_e (vxe (my+2), vye (my+2))"
              proof (cases "ky = 0")
                case True hence "my + 2 = 2" unfolding my_def by (by100 simp)
                have "fst (?ext ! 0) = fst (?ext ! 1)"
                  using hspur0 hspur1 unfolding top1_inverse_edge_def by (by100 simp)
                have "snd (?ext ! 0) \<noteq> snd (?ext ! 1)"
                  using hspur0 hspur1 unfolding top1_inverse_edge_def by (by100 simp)
                have "0 < ?ne" using hlen hne_eq by (by100 linarith)
                have "1 < ?ne" using hlen hne_eq by (by100 linarith)
                have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                from hC7_e[rule_format, OF \<open>0 < ?ne\<close> \<open>1 < ?ne\<close> \<open>fst(?ext!0) = fst(?ext!1)\<close> this]
                have "q_e ((1-0)*vxe 0+0*vxe(Suc 0 mod ?ne),(1-0)*vye 0+0*vye(Suc 0 mod ?ne)) =
                  (if snd(?ext!0) = snd(?ext!1) then q_e ((1-0)*vxe 1+0*vxe(Suc 1 mod ?ne),
                      (1-0)*vye 1+0*vye(Suc 1 mod ?ne))
                   else q_e (0*vxe 1+(1-0)*vxe(Suc 1 mod ?ne),
                      0*vye 1+(1-0)*vye(Suc 1 mod ?ne)))" by (by100 blast)
                hence "q_e (vxe 0, vye 0) = q_e (vxe (Suc 1 mod ?ne), vye (Suc 1 mod ?ne))"
                  using \<open>snd(?ext!0) \<noteq> snd(?ext!1)\<close> by (by100 simp)
                moreover have "Suc 1 mod ?ne = 2"
                proof -
                  have "?ne \<ge> 5" using hlen hne_eq by (by100 linarith)
                  hence "(2::nat) < ?ne" by (by100 linarith)
                  thus ?thesis by (by100 simp)
                qed
                ultimately have "q_e (vxe 0, vye 0) = q_e (vxe 2, vye 2)" by (by100 simp)
                thus ?thesis using True \<open>my+2 = 2\<close> by (simp add: numeral_2_eq_2)
              next
                case False hence "ky \<ge> 2" using hky_ne1 by (by100 linarith)
                hence "my = ky - 2" unfolding my_def by (by100 simp)
                hence "my + 2 = ky" using \<open>ky \<ge> 2\<close> by (by100 linarith)
                thus ?thesis by (by100 simp)
              qed
              \<comment> \<open>Step C: compose: q\\_e(v\\_kx) = q\\_e(v\\_{mx+2}) = q\\_e(v\\_{my+2}) = q\\_e(v\\_ky).\<close>
              have "q_e (vxe kx, vye kx) = q_e (vxe ky, vye ky)"
                using hqe_kx_mx hqe_mx_my hqe_ky_my by (by100 simp)
              thus ?thesis using hx_vtx_bwd hy_vtx_bwd by (by100 simp)
            qed
          qed
        qed
      qed
    qed
    show ?thesis
      apply (rule exI[of _ ?g])
      using hg_range hg_cont hg_surj hg_fwd hg_bwd by (by100 blast)
  qed
  then obtain g where hg_range: "\<forall>p \<in> P_e. g p \<in> Y_w"
    and hg_cont: "top1_continuous_map_on P_e
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_e)
        Y_w TY_w g"
    and hg_surj: "g ` P_e = Y_w"
    and hg_fwd: "\<forall>x\<in>P_e. \<forall>y\<in>P_e. q_e x = q_e y \<longrightarrow> g x = g y"
    and hg_bwd: "\<forall>x\<in>P_e. \<forall>y\<in>P_e. g x = g y \<longrightarrow> q_e x = q_e y"
    by (elim exE conjE) (rule that, assumption+)
  \<comment> \<open>Step C: Factor g through q\\_e to get f: Y\\_e -> Y\\_w (Theorem 22.2).\<close>
  from Theorem_22_2[OF hC2_e hg_range hg_fwd]
  obtain f where hf_range: "\<forall>y\<in>Y_e. f y \<in> Y_w"
    and hf_comp: "\<forall>x\<in>P_e. f (q_e x) = g x"
    and hf_cont_iff: "top1_continuous_map_on Y_e TY_e Y_w TY_w f
        \<longleftrightarrow> top1_continuous_map_on P_e
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_e)
            Y_w TY_w g"
    by (by100 blast)
  have hf_cont: "top1_continuous_map_on Y_e TY_e Y_w TY_w f"
    using hf_cont_iff hg_cont by (by100 simp)
  \<comment> \<open>Step D: f is bijective.\<close>
  have hf_bij: "bij_betw f Y_e Y_w"
  proof -
    \<comment> \<open>Surjectivity: Y\\_w = g(P\\_e) = f(q\\_e(P\\_e)) = f(Y\\_e).\<close>
    have hq_surj: "q_e ` P_e = Y_e"
      using hC2_e unfolding top1_quotient_map_on_def top1_continuous_map_on_def by (by100 blast)
    have hf_surj: "f ` Y_e = Y_w"
    proof -
      have "f ` Y_e = f ` (q_e ` P_e)" using hq_surj by (by100 simp)
      also have "\<dots> = (f \<circ> q_e) ` P_e" by (by100 auto)
      also have "\<dots> = g ` P_e"
      proof -
        have "\<forall>x\<in>P_e. (f \<circ> q_e) x = g x" using hf_comp by (by100 simp)
        thus ?thesis by (by100 force)
      qed
      also have "\<dots> = Y_w" using hg_surj .
      finally show ?thesis .
    qed
    \<comment> \<open>Injectivity: f(y1) = f(y2) implies y1 = y2.\<close>
    have hf_inj: "inj_on f Y_e"
    proof (rule inj_onI)
      fix y1 y2 assume hy1: "y1 \<in> Y_e" and hy2: "y2 \<in> Y_e" and heq: "f y1 = f y2"
      \<comment> \<open>y1 = q\\_e(x1) and y2 = q\\_e(x2) for some x1, x2 in P\\_e.\<close>
      from hy1 obtain x1 where hx1: "x1 \<in> P_e" "q_e x1 = y1"
        using hq_surj by (by100 blast)
      from hy2 obtain x2 where hx2: "x2 \<in> P_e" "q_e x2 = y2"
        using hq_surj by (by100 blast)
      have "g x1 = f (q_e x1)" using hf_comp[rule_format, OF hx1(1)] by (by100 simp)
      also have "\<dots> = f y1" using hx1(2) by (by100 simp)
      also have "\<dots> = f y2" using heq .
      also have "\<dots> = f (q_e x2)" using hx2(2) by (by100 simp)
      also have "\<dots> = g x2" using hf_comp[rule_format, OF hx2(1)] by (by100 simp)
      finally have "g x1 = g x2" .
      hence "q_e x1 = q_e x2"
        using hg_bwd hx1(1) hx2(1) by (by100 blast)
      thus "y1 = y2" using hx1(2) hx2(2) by (by100 simp)
    qed
    show ?thesis unfolding bij_betw_def using hf_inj hf_surj by (by100 blast)
  qed
  \<comment> \<open>Step E: Apply Theorem 26.6: continuous bijection compact -> Hausdorff = homeomorphism.\<close>
  have htopo_e_on: "is_topology_on Y_e TY_e"
    using htopo_e by (rule is_topology_on_strict_imp)
  have htopo_w_on: "is_topology_on Y_w TY_w"
    using htopo_w by (rule is_topology_on_strict_imp)
  from Theorem_26_6[OF htopo_e_on htopo_w_on hcompact_e hhaus_w hf_cont hf_bij]
  have hY_e_w: "\<exists>h. top1_homeomorphism_on Y_e TY_e Y_w TY_w h"
    by (by100 blast)
  from hY_e_w obtain h2 where hh2: "top1_homeomorphism_on Y_e TY_e Y_w TY_w h2"
    by (by100 blast)
  from scheme_quotient_uniqueness[OF htopo_w htopo_wf hY_w hY_wf]
  obtain h3 where hh3: "top1_homeomorphism_on Y_w TY_w Y_wf TY_wf h3"
    by (by100 blast)
  from homeomorphism_comp[OF hh1 hh2]
  have "top1_homeomorphism_on Y_ef TY_ef Y_w TY_w (h2 \<circ> h1)" .
  from homeomorphism_comp[OF this hh3]
  show ?thesis by (by100 blast)
qed

\<comment> \<open>Direct front-cancel for proper+fresh schemes.
   DOES NOT use quotient\\_of\\_scheme\\_uncancel (breaks circular dependency).
   Uses scheme\\_quotient\\_exists(2) for BOTH extended and base schemes,
   then proves the cancel homeomorphism by direct fibre matching.
   The spur (edges 0,1 of extended scheme) maps to a single vertex in the quotient.
   Key: C12 from scheme\\_quotient\\_exists(2) rules out vertex-edge crossings.\<close>
lemma front_cancel_proper_direct:
  fixes Y :: "'a set" and TY :: "'a set set"
    and a :: "nat \<times> bool" and w :: "(nat \<times> bool) list"
  assumes hY: "top1_quotient_of_scheme_on Y TY ([a, top1_inverse_edge a] @ w)"
      and hlen: "length w \<ge> 3"
      and hproper: "\<forall>label. card {i. i < length w \<and> fst (w ! i) = label} \<in> {0, 2}"
      and hfresh: "fst a \<notin> fst ` set w"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' w \<and>
    top1_homeomorphism_on Y TY Y' TY' h"
proof -
  let ?ext = "[a, top1_inverse_edge a] @ w"
  have htopo_Y: "is_topology_on_strict Y TY"
    using hY unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  have hlen_ext: "length ?ext \<ge> 3" using hlen by (by100 simp)
  have hproper_ext: "\<forall>label. card {i. i < length ?ext \<and> fst (?ext ! i) = label} \<in> {0, 2}"
    by (rule cancel_pair_prepend_proper[OF hproper hfresh])
  \<comment> \<open>Step 1: Get canonical quotient of w.\<close>
  from scheme_quotient_exists(1)[OF hlen hproper]
  obtain Y_w :: "(real \<times> real) set" and TY_w :: "(real \<times> real) set set"
    where hY_w: "top1_quotient_of_scheme_on Y_w TY_w w" by (by100 blast)
  have htopo_w: "is_topology_on_strict Y_w TY_w"
    using hY_w unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  \<comment> \<open>Step 2: Get canonical quotient of extended scheme with C12.\<close>
  \<comment> \<open>Step 2: Get canonical quotient of extended scheme.\<close>
  from scheme_quotient_exists(1)[OF hlen_ext hproper_ext]
  obtain Y_ext :: "(real \<times> real) set" and TY_ext :: "(real \<times> real) set set"
    where hY_ext: "top1_quotient_of_scheme_on Y_ext TY_ext ?ext" by (by100 blast)
  have htopo_ext: "is_topology_on_strict Y_ext TY_ext"
    using hY_ext unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  \<comment> \<open>Step 3: Direct fibre-matching homeomorphism Y\\_ext to Y\\_w.
     The spur pair (edges 0,1 of P\\_ext) collapses to vertex q\\_ext(v\\_ext\\_0) = q\\_ext(v\\_ext\\_2).
     The main edges (2,...,n+1 of P\\_ext) correspond to edges (0,...,n-1 of P\\_w).
     Define f: P\\_ext to Y\\_w by:
       f(spur\\_pt) = q\\_w(v\\_w\\_0)  [vertex image]
       f(main\\_edge(k+2,t)) = q\\_w(edge\\_w(k,t))  [corresponding edge]
       f(interior) = q\\_w(spur\\_collapse(interior))
     f has the same fibres as q\\_ext because:
       - The spur fibre: all spur points and v\\_ext\\_0, v\\_ext\\_2 map to the same point.
         In q\\_ext: the a-pair identifies edges 0,1 (C7). At vertices: v\\_0 ~ v\\_2 (from C7 at t=0).
         So the spur fibre = {all spur pts, v\\_ext\\_0, v\\_ext\\_1, v\\_ext\\_2} modulo.
       - The main fibres: same as q\\_w fibres shifted by 2 positions.
     Apply quotient\\_same\\_fibres\\_homeomorphic to get Y\\_ext ~ Y\\_w.\<close>
  \<comment> \<open>Step 3a: Get full C1-C12 from scheme\\_quotient\\_exists(2) for BOTH schemes.\<close>
  from scheme_quotient_exists(2)[OF hlen hproper]
  obtain P_wf :: "(real \<times> real) set" and q_wf :: "real \<times> real \<Rightarrow> real \<times> real"
    and vxw vyw :: "nat \<Rightarrow> real"
    and Y_wf :: "(real \<times> real) set" and TY_wf :: "(real \<times> real) set set"
    where hY_wf: "top1_quotient_of_scheme_on Y_wf TY_wf w"
    and hC2_wf: "top1_quotient_map_on P_wf
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_wf)
        Y_wf TY_wf q_wf"
    and hC12_wf: "\<forall>k<length w. \<forall>j<length w. \<forall>s'\<in>{0<..<(1::real)}.
        q_wf (vxw k, vyw k) \<noteq> q_wf ((1-s')*vxw j + s'*vxw(Suc j mod length w),
                               (1-s')*vyw j + s'*vyw(Suc j mod length w))"
    by (elim exE conjE) (rule that, assumption+)
  have htopo_wf: "is_topology_on_strict Y_wf TY_wf"
    using hY_wf unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  from scheme_quotient_exists(2)[OF hlen_ext hproper_ext]
  obtain P_ef :: "(real \<times> real) set" and q_ef :: "real \<times> real \<Rightarrow> real \<times> real"
    and vxe vye :: "nat \<Rightarrow> real"
    and Y_ef :: "(real \<times> real) set" and TY_ef :: "(real \<times> real) set set"
    where hY_ef: "top1_quotient_of_scheme_on Y_ef TY_ef ?ext"
    and hC2_ef: "top1_quotient_map_on P_ef
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_ef)
        Y_ef TY_ef q_ef"
    and hC7_ef: "\<forall>i<length ?ext. \<forall>j<length ?ext. fst (?ext!i) = fst (?ext!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q_ef ((1-t)*vxe i+t*vxe(Suc i mod length ?ext),
            (1-t)*vye i+t*vye(Suc i mod length ?ext))
         = (if snd (?ext!i) = snd (?ext!j)
            then q_ef ((1-t)*vxe j+t*vxe(Suc j mod length ?ext),
                    (1-t)*vye j+t*vye(Suc j mod length ?ext))
            else q_ef (t*vxe j+(1-t)*vxe(Suc j mod length ?ext),
                    t*vye j+(1-t)*vye(Suc j mod length ?ext))))"
    and hC8_ef: "\<forall>p\<in>P_ef. (\<forall>i<length ?ext. \<forall>t\<in>I_set.
          p \<noteq> ((1-t)*vxe i+t*vxe(Suc i mod length ?ext),
                (1-t)*vye i+t*vye(Suc i mod length ?ext)))
       \<longrightarrow> (\<forall>p'\<in>P_ef. q_ef p = q_ef p' \<longrightarrow> p = p')"
    and hC12_ef: "\<forall>k<length ?ext. \<forall>j<length ?ext. \<forall>s'\<in>{0<..<(1::real)}.
        q_ef (vxe k, vye k) \<noteq> q_ef ((1-s')*vxe j + s'*vxe(Suc j mod length ?ext),
                               (1-s')*vye j + s'*vye(Suc j mod length ?ext))"
    by (elim exE conjE) (rule that, assumption+)
  have htopo_ef: "is_topology_on_strict Y_ef TY_ef"
    using hY_ef unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  \<comment> \<open>Step 3b: The fibre-matching cancel homeomorphism Y\\_ef ~ Y\\_wf.
     Define p2: P\\_ef -> Y\\_wf by collapsing the spur (edges 0,1) to vertex 0.
     p2 = q\\_wf o collapse, where collapse: P\\_ef -> P\\_wf merges the spur.
     Then: q\\_ef and p2 have the same fibres (by C7/C8/C9/C12 analysis).
     quotient\\_same\\_fibres\\_homeomorphic gives Y\\_ef ~ Y\\_wf.\<close>
  have hY_ef_wf_homeo: "\<exists>h. top1_homeomorphism_on Y_ef TY_ef Y_wf TY_wf h"
  proof -
    \<comment> \<open>Construction: define p2: P\\_ef -> Y\\_wf that collapses the a-spur.
       The extended scheme [a, a^{-1}] @ w has n+2 edges where edges 0,1 are the a-spur.
       The base scheme w has n edges.
       The map p2 collapses edges 0,1 of P\\_ef to vertex 0 of P\\_wf,
       and maps edges 2,...,n+1 of P\\_ef to edges 0,...,n-1 of P\\_wf.\<close>
    \<comment> \<open>Step A: p2 is a quotient map from P\\_ef to Y\\_wf.
       p2 = q\\_wf o collapse where collapse: P\\_ef -> P\\_wf.
       Since P\\_ef is compact, Y\\_wf is Hausdorff, and p2 is continuous surjection,
       p2 is automatically a quotient map.\<close>
    \<comment> \<open>Use spur\\_collapse\\_cancel\\_homeo to get Y\\_ef ~ Y\\_wf directly.\<close>
    from spur_collapse_cancel_homeo[OF hlen hproper hfresh hY_ef hY_wf]
    show ?thesis .
  qed
  \<comment> \<open>Step 3c: Bridge all quotients via uniqueness.\<close>
  from scheme_quotient_uniqueness[OF htopo_ext htopo_ef hY_ext hY_ef]
  obtain h_be where hbe: "top1_homeomorphism_on Y_ext TY_ext Y_ef TY_ef h_be"
    by (by100 blast)
  from hY_ef_wf_homeo obtain h_ew where hew: "top1_homeomorphism_on Y_ef TY_ef Y_wf TY_wf h_ew"
    by (by100 blast)
  from homeomorphism_comp[OF hbe hew]
  have h_ew2: "top1_homeomorphism_on Y_ext TY_ext Y_wf TY_wf (h_ew \<circ> h_be)" .
  from scheme_quotient_uniqueness[OF htopo_wf htopo_w hY_wf hY_w]
  obtain h_ww where hww: "top1_homeomorphism_on Y_wf TY_wf Y_w TY_w h_ww"
    by (by100 blast)
  from homeomorphism_comp[OF h_ew2 hww]
  have hY_ext_w_homeo: "\<exists>h. top1_homeomorphism_on Y_ext TY_ext Y_w TY_w h"
    by (by100 blast)
  \<comment> \<open>Step 4: Bridge Y to Y\\_ext using uniqueness (both quotients of extended scheme).\<close>
  from scheme_quotient_uniqueness[OF htopo_Y htopo_ext hY hY_ext]
  obtain h_bridge where hbridge: "top1_homeomorphism_on Y TY Y_ext TY_ext h_bridge"
    by (by100 blast)
  \<comment> \<open>Step 5: Compose homeomorphisms: Y to Y\\_ext to Y\\_w.\<close>
  from hY_ext_w_homeo obtain h_cancel where
    hcancel: "top1_homeomorphism_on Y_ext TY_ext Y_w TY_w h_cancel"
    by (by100 blast)
  from homeomorphism_comp[OF hbridge hcancel]
  have hcomp: "top1_homeomorphism_on Y TY Y_w TY_w (h_cancel \<circ> h_bridge)" .
  \<comment> \<open>Step 6: Transfer quotient of w from Y\\_w to Y via inverse homeomorphism.\<close>
  from homeomorphism_inverse[OF hcomp]
  have hinv: "top1_homeomorphism_on Y_w TY_w Y TY (inv_into Y (h_cancel \<circ> h_bridge))" .
  from scheme_quotient_transfer_along_homeomorphism[OF hY_w hinv htopo_Y]
  have "top1_quotient_of_scheme_on Y TY w" .
  thus ?thesis by (rule same_space_implies_homeo_realization)
qed

\<comment> \<open>§76 Polygon diagonal cut-reglue homeomorphism (per expert audit 30 §6).
   Given two proper schemes s1, s2 of the same length where s2 is a cut-paste
   rearrangement of s1 (i.e., s2 is obtained from s1 by moving a block of edges
   past an identified pair), the canonical quotients Y1, Y2 are homeomorphic.

   Construction (per Munkres §76 + audit 30):
   1. Both canonical quotients use the SAME regular n-gon P (from scheme\\_quotient\\_exists)
   2. Cut P along a diagonal d into sub-polygons Q1, Q2
   3. On Q1: define a PL homeomorphism that rearranges boundary arcs (fixing the diagonal)
   4. On Q2: identity
   5. The combined map \\<phi>: P \\<to> P is a homeomorphism (continuous at diagonal)
   6. \\<phi> maps old-identification fibres to new-identification fibres
   7. quotient\\_same\\_fibres\\_homeomorphic gives Y\\_old \\<cong> Y\\_new

   The sub-polygon rearrangement is the key geometric step. It's a PL homeomorphism
   of a convex polygon that cyclically shifts some boundary arcs while fixing others.
   Extension from boundary to interior by cone from centroid.\<close>

\<comment> \<open>Helper: convex polygon sub-region (intersection of P with a half-plane).
   Given a convex polygon P and a diagonal from vertex v\\_a to v\\_b,
   the sub-polygon on one side is still convex and its boundary consists of
   the edges between v\\_a and v\\_b plus the diagonal segment.\<close>

\<comment> \<open>Helper: PL homeomorphism of convex polygon that permutes boundary arcs.
   Given a convex polygon Q with boundary arcs A1,...,Ak,D (where D is fixed),
   a cyclic permutation \\<sigma> of A1,...,Ak induces a PL boundary homeomorphism
   extended to the interior by cone from centroid.

   Construction: for each boundary arc Ai (angular interval [\\<alpha>i, \\<alpha>i+1]),
   map it linearly to the arc A\\<sigma>(i) (angular interval [\\<alpha>'\\<sigma>(i), \\<alpha>'\\<sigma>(i)+1]).
   Since all maps are linear on arcs and agree at arc endpoints (consecutive arcs
   share endpoints in the permuted order), the boundary map is continuous.
   Extend to interior by: for a point at distance r from centroid in direction \\<theta>,
   map to distance r in direction \\<sigma>(\\<theta>).

   This construction works for ANY convex polygon, not just regular ones.
   The key property: D (the fixed arc) maps to itself, ensuring compatibility
   with the identity on the other sub-polygon.\<close>

\<comment> \<open>Core lemma: PL homeomorphism of the closed unit disk B2 that rearranges
   boundary arcs. Given n arcs dividing S1 into equal parts (each of width 2\\<pi>/n)
   and a permutation \\<sigma> of {0,..n-1}, construct a PL homeomorphism \\<phi>: B2 \\<to> B2
   that maps the k-th arc linearly to the \\<sigma>(k)-th arc.

   The construction: for each boundary point at angle \\<theta> in the k-th arc
   [2\\<pi>k/n, 2\\<pi>(k+1)/n], map to the corresponding angle in the \\<sigma>(k)-th arc.
   Extend radially: \\<phi>(r*p) = r*\\<phi>(p/|p|) for p \\<noteq> 0, \\<phi>(0) = 0.

   CAVEAT (from session 1520): This is NOT continuous at arc boundaries unless
   the permutation preserves adjacency. For cut-paste operations, we need a
   DIFFERENT construction: cut the polygon along a diagonal, rearrange one
   sub-polygon while fixing the diagonal, then reassemble.
   The sub-polygon rearrangement IS a cyclic rotation of edges on one side
   of the diagonal, which DOES preserve adjacency within that side.
   The diagonal arc is fixed, ensuring continuity at the cut boundary.\<close>

\<comment> \<open>Diagonal cut rearrangement: the key geometric lemma for §76 operations.
   Given a regular n-gon P inscribed in the unit circle, a diagonal d from
   vertex v\\_a to v\\_b divides P into sub-polygons Q1 (vertices a,...,b) and
   Q2 (vertices b,...,a). A cyclic rotation of the edges within Q1
   (fixing the diagonal) gives a homeomorphism of P that rearranges edges.

   This is formalized as: there exists a homeomorphism \\<phi> of B2 that maps
   the old edge arcs to the new (rearranged) edge arcs on S1, where the
   rearrangement is a cyclic shift of edges within one sub-polygon.\<close>
\<comment> \<open>IMPORTANT: a self-homeomorphism \\<phi>: P \\<to> P that shifts Q1 edges while fixing Q2
   is IMPOSSIBLE for shift > 0. At diagonal vertex v\\_{cut\\_a}: Q2-identity gives
   \\<phi>(v\\_{cut\\_a}) = v\\_{cut\\_a}, but Q1-shift gives \\<phi>(v\\_{cut\\_a}) = v\\_{cut\\_a+shift}.
   These contradict for shift > 0.

   The correct approach (per expert audit §6): construct homeomorphism DIRECTLY
   between quotient spaces Y\\_old \\<to> Y\\_new, not at polygon level.
   In quotient spaces, diagonal vertex conflict is absorbed by identification.

   The \\<sigma> properties below (range, injectivity, fix, in\\_Q1) remain useful for
   the quotient-level fibre matching.\<close>

\<comment> \<open>NOTE: polygon\\_sub\\_rearrange\\_homeo as a SELF-MAP P\\<to>P is impossible for shift>0.
   The lemma below retains the \\<sigma> property proofs which are used by the quotient-level
   homeomorphism construction in cut\\_paste\\_opp\\_proper.

   The correct statement would be at the QUOTIENT level:
   \\<exists>h. top1\\_homeomorphism\\_on Y\\_old TY\\_old Y\\_new TY\\_new h
   where Y\\_old, Y\\_new are quotients of the old/new schemes.
   This is the sorry at line ~1382 in cut\\_paste\\_opp\\_proper.\<close>
lemma polygon_sub_rearrange_sigma_props:
  fixes n :: nat and cut_a cut_b :: nat and shift :: nat
  assumes hn: "n \<ge> 3"
      and hcut_a: "cut_a < n" and hcut_b: "cut_b < n"
      and hcut_lt: "cut_a < cut_b"
      and hm: "cut_b - cut_a \<ge> 2"
      and hshift: "shift > 0" "shift < cut_b - cut_a"
  shows "\<exists>\<sigma> :: nat \<Rightarrow> nat.
    (\<forall>k<n. \<sigma> k < n) \<and>
    inj_on \<sigma> {..<n} \<and>
    (\<forall>k<n. \<not>(cut_a \<le> k \<and> k < cut_b) \<longrightarrow> \<sigma> k = k) \<and>
    (\<forall>k. cut_a \<le> k \<and> k < cut_b \<longrightarrow> cut_a \<le> \<sigma> k \<and> \<sigma> k < cut_b)"
proof -
  let ?m = "cut_b - cut_a"
  define \<sigma> :: "nat \<Rightarrow> nat" where
    "\<sigma> k = (if cut_a \<le> k \<and> k < cut_b
            then cut_a + ((k - cut_a + shift) mod ?m)
            else k)" for k
  \<comment> \<open>Sub-lemma 1: \\<sigma> is a permutation of {0,...,n-1}.\<close>
  have hmpos: "?m > 0" using hm by (by100 linarith)
  have h\<sigma>_range: "\<forall>k<n. \<sigma> k < n"
  proof (intro allI impI)
    fix k assume hk: "k < n"
    show "\<sigma> k < n" unfolding \<sigma>_def
    proof (cases "cut_a \<le> k \<and> k < cut_b")
      case True
      have "(k - cut_a + shift) mod ?m < ?m" using hmpos by simp
      hence "cut_a + ((k - cut_a + shift) mod ?m) < cut_b" by (by100 linarith)
      thus "(if cut_a \<le> k \<and> k < cut_b then cut_a + (k - cut_a + shift) mod ?m else k) < n"
        using True hcut_b by simp
    next
      case False thus "(if cut_a \<le> k \<and> k < cut_b then cut_a + (k - cut_a + shift) mod ?m else k) < n"
        using hk by (simp add: if_not_P)
    qed
  qed
  have h\<sigma>_in_Q1: "\<forall>k. cut_a \<le> k \<and> k < cut_b \<longrightarrow> cut_a \<le> \<sigma> k \<and> \<sigma> k < cut_b"
  proof (intro allI impI)
    fix k assume hk: "cut_a \<le> k \<and> k < cut_b"
    have "\<sigma> k = cut_a + ((k - cut_a + shift) mod ?m)" unfolding \<sigma>_def using hk by simp
    moreover have "((k - cut_a + shift) mod ?m) < ?m" using hmpos by simp
    ultimately show "cut_a \<le> \<sigma> k \<and> \<sigma> k < cut_b" by (by100 linarith)
  qed
  have h\<sigma>_inj: "inj_on \<sigma> {..<n}"
  proof (rule inj_onI)
    fix x y assume hx: "x \<in> {..<n}" and hy: "y \<in> {..<n}" and heq: "\<sigma> x = \<sigma> y"
    show "x = y"
    proof (cases "cut_a \<le> x \<and> x < cut_b")
      case True note hx_in = this
      show ?thesis
      proof (cases "cut_a \<le> y \<and> y < cut_b")
        case True note hy_in = this
        from heq have "cut_a + ((x - cut_a + shift) mod ?m) =
            cut_a + ((y - cut_a + shift) mod ?m)"
          unfolding \<sigma>_def using hx_in hy_in by simp
        hence hmod_eq: "(x - cut_a + shift) mod ?m = (y - cut_a + shift) mod ?m"
          by (by100 linarith)
        have hxm: "x - cut_a < ?m" using hx_in by (by100 linarith)
        have hym: "y - cut_a < ?m" using hy_in by (by100 linarith)
        \<comment> \<open>From (a+s)mod m = (b+s)mod m with a,b < m: derive a = b.
           Use mod\\_eq\\_dvd\\_iff\\_nat + dvd\\_imp\\_le.\<close>
        have "x - cut_a = y - cut_a"
        proof (rule ccontr)
          assume hne: "x - cut_a \<noteq> y - cut_a"
          consider (lt) "x - cut_a < y - cut_a" | (gt) "x - cut_a > y - cut_a"
            using hne by (by100 linarith)
          thus False
          proof cases
            case lt
            hence hle: "x - cut_a + shift \<le> y - cut_a + shift" by (by100 linarith)
            from hle have "(y - cut_a + shift) mod ?m = (x - cut_a + shift) mod ?m \<longleftrightarrow>
                ?m dvd ((y - cut_a + shift) - (x - cut_a + shift))"
              by (rule mod_eq_dvd_iff_nat)
            hence "?m dvd ((y - cut_a) - (x - cut_a))"
              using hmod_eq by (by100 simp)
            moreover have "0 < (y - cut_a) - (x - cut_a)" using lt by (by100 linarith)
            moreover have hlt_m: "(y - cut_a) - (x - cut_a) < ?m" using hxm hym by (by100 linarith)
            moreover have hpos: "0 < (y - cut_a) - (x - cut_a)" using lt by (by100 linarith)
            ultimately show False
              using dvd_imp_le[of ?m "(y - cut_a) - (x - cut_a)"] by (by100 linarith)
          next
            case gt
            hence hle: "y - cut_a + shift \<le> x - cut_a + shift" by (by100 linarith)
            from hle have "(x - cut_a + shift) mod ?m = (y - cut_a + shift) mod ?m \<longleftrightarrow>
                ?m dvd ((x - cut_a + shift) - (y - cut_a + shift))"
              by (rule mod_eq_dvd_iff_nat)
            hence "?m dvd ((x - cut_a) - (y - cut_a))"
              using hmod_eq by (by100 simp)
            moreover have "0 < (x - cut_a) - (y - cut_a)" using gt by (by100 linarith)
            moreover have hlt_m: "(x - cut_a) - (y - cut_a) < ?m" using hxm hym by (by100 linarith)
            moreover have hpos: "0 < (x - cut_a) - (y - cut_a)" using gt by (by100 linarith)
            ultimately show False
              using dvd_imp_le[of ?m "(x - cut_a) - (y - cut_a)"] by (by100 linarith)
          qed
        qed
        thus "x = y" using hx_in hy_in by (by100 linarith)
      next
        case False
        from h\<sigma>_in_Q1[rule_format, OF hx_in] have "cut_a \<le> \<sigma> x \<and> \<sigma> x < cut_b" .
        moreover have "\<sigma> y = y" unfolding \<sigma>_def using False by (simp add: if_not_P)
        ultimately show "x = y" using heq False by (by100 linarith)
      qed
    next
      case False note hx_out = this
      show ?thesis
      proof (cases "cut_a \<le> y \<and> y < cut_b")
        case True
        from h\<sigma>_in_Q1[rule_format, OF True] have "cut_a \<le> \<sigma> y \<and> \<sigma> y < cut_b" .
        moreover have "\<sigma> x = x" unfolding \<sigma>_def using hx_out by (simp add: if_not_P)
        ultimately show "x = y" using heq hx_out by (by100 linarith)
      next
        case False
        have hsx: "\<sigma> x = x" unfolding \<sigma>_def using hx_out by (simp add: if_not_P)
        have hsy: "\<sigma> y = y" unfolding \<sigma>_def using False by (simp add: if_not_P)
        from heq hsx hsy show "x = y" by (by100 simp)
      qed
    qed
  qed
  \<comment> \<open>Sub-lemma 2: \\<sigma> preserves labels.
     old\\_scheme[k] = new\\_scheme[\\<sigma>(k)] where new\\_scheme is the target scheme.\<close>
  \<comment> \<open>Sub-lemma 3: \\<sigma> fixes edges outside Q1.
     For k not in Q1 range: \\<sigma>(k) = k.\<close>
  have h\<sigma>_fix: "\<forall>k<n. \<not>(cut_a \<le> k \<and> k < cut_b) \<longrightarrow> \<sigma> k = k"
    unfolding \<sigma>_def by (by100 simp)
  \<comment> \<open>All four \\<sigma> properties proved. Package them.\<close>
  show ?thesis
    apply (rule exI[of _ \<sigma>])
    using h\<sigma>_range h\<sigma>_inj h\<sigma>_fix h\<sigma>_in_Q1 by (by100 blast)
qed

\<comment> \<open>DELETED: edge\\_merge\\_quotient\\_homeo (COMBINE step, ~100 lines, ~12 sorrys).
   No longer needed: front\\_cancel\\_proper now uses the simpler
   uncancel + uniqueness proof that avoids the 3-step CUT-COMBINE-PASTE argument.
   The COMBINE step may still be useful for cut-paste operations in the future.\<close>

\<comment> \<open>Cancel at front for PROPER schemes -- per expert audit 23 step 5.
   Uses scheme\\_quotient\\_exists for w to get a canonical quotient Y\\_w,
   then shows Y (quotient of [a,inv a]@w) \\<cong> Y\\_w via spur collapse.
   Properness needed for scheme\\_quotient\\_exists.
   Placed after scheme\\_quotient\\_uniqueness so it can use it.\<close>


\<comment> \<open>Cut-paste-opp/same-direction for proper nat-typed schemes:
   quotient\\_of\\_scheme\\_cut\\_paste\\_opp\\_proper and quotient\\_of\\_scheme\\_cut\\_paste\\_proper
   DELETED (were dead code, not called by anything). Both used the FALSE
   quotient\\_rearrangement\\_homeomorphism lemma (also deleted).
   The conclusions ARE true but the proof route was wrong.
   The correct approach uses theorem\\_76\\_1\\_paste\\_chain.\<close>


\<comment> \<open>front\\_cancel\\_proper: delegates to front\\_cancel\\_proper\\_direct.
   The spur-collapse argument (spur\\_collapse\\_cancel\\_homeo) is the only sorry
   in the dependency chain. No dependency on uncancel or the old tau-map.\<close>
lemma front_cancel_proper:
  fixes Y :: "'a set" and TY :: "'a set set"
    and a :: "nat \<times> bool" and w :: "(nat \<times> bool) list"
  assumes "top1_quotient_of_scheme_on Y TY ([a, top1_inverse_edge a] @ w)"
      and "length w \<ge> 3"
      and hproper: "\<forall>label. card {i. i < length w \<and> fst (w ! i) = label} \<in> {0, 2}"
      and hfresh: "fst a \<notin> fst ` set w"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' w \<and>
    top1_homeomorphism_on Y TY Y' TY' h"
  \<comment> \<open>Delegates to front\\_cancel\\_proper\\_direct (which does NOT depend on uncancel).
     This breaks the circular dependency chain.\<close>
  using front_cancel_proper_direct[OF assms(1) assms(2) hproper hfresh] .


\<comment> \<open>front\\_cancel\\_proper now delegates to front\\_cancel\\_proper\\_direct (defined earlier).
   The entire cancel chain depends only on spur\\_collapse\\_cancel\\_homeo (1 sorry).
   No dependency on uncancel or the old tau-map approach.\<close>

\<comment> \<open>Cancel at front — homeomorphic-realization form for proper+fresh schemes.
   Uses front\\_cancel\\_proper directly. No general cancel sorry dependency.
   Can be used in v\\_cancel case when properness is available.\<close>
lemma front_cancel_realization_homeo_proper:
  fixes Y :: "'a set" and TY :: "'a set set"
    and a :: "nat \<times> bool" and w :: "(nat \<times> bool) list"
  assumes "top1_quotient_of_scheme_on Y TY ([a, top1_inverse_edge a] @ w)"
      and "length w \<ge> 3"
      and "\<forall>label. card {i. i < length w \<and> fst (w ! i) = label} \<in> {0, 2}"
      and "fst a \<notin> fst ` set w"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' w \<and>
    top1_homeomorphism_on Y TY Y' TY' h"
  using front_cancel_proper[OF assms(1) assms(2) assms(3) assms(4)] .

\<comment> \<open>Uncancel for proper schemes: derived from front\\_cancel\\_proper\\_direct + existence + uniqueness + transfer.
   Uses front\\_cancel\\_proper\\_direct (which does NOT depend on uncancel) to break circularity.
   Only depends on spur\\_collapse\\_cancel\\_homeo (through front\\_cancel\\_proper\\_direct).\<close>
lemma quotient_of_scheme_uncancel_front_proper:
  fixes a :: "nat \<times> bool" and w :: "(nat \<times> bool) list"
  assumes "top1_quotient_of_scheme_on Y TY w"
      and "length w \<ge> 3"
      and hproper: "\<forall>label. card {i. i < length w \<and> fst (w ! i) = label} \<in> {0, 2}"
      and hfresh: "fst a \<notin> fst ` set w"
  shows "top1_quotient_of_scheme_on Y TY ([a, top1_inverse_edge a] @ w)"
proof -
  let ?ext = "[a, top1_inverse_edge a] @ w"
  have htopo_Y: "is_topology_on_strict Y TY"
    using assms(1) unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  \<comment> \<open>Step 1: scheme\\_quotient\\_exists for the extended scheme.\<close>
  have hlen_ext: "length ?ext \<ge> 3" using assms(2) by (by100 simp)
  have hproper_ext: "\<forall>label. card {i. i < length ?ext \<and> fst (?ext ! i) = label} \<in> {0, 2}"
    by (rule cancel_pair_prepend_proper[OF hproper hfresh])
  from scheme_quotient_exists(1)[OF hlen_ext hproper_ext]
  obtain Y_ext :: "(real \<times> real) set" and TY_ext :: "(real \<times> real) set set" where
      hY_ext: "top1_quotient_of_scheme_on Y_ext TY_ext ?ext" by (by100 blast)
  have htopo_ext: "is_topology_on_strict Y_ext TY_ext"
    using hY_ext unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  \<comment> \<open>Step 2: front\\_cancel\\_proper\\_direct gives Y\\_ext homeomorphic to some quotient of w.
     Uses front\\_cancel\\_proper\\_direct (NOT front\\_cancel\\_proper) to avoid uncancel dependency.\<close>
  from front_cancel_proper_direct[OF hY_ext assms(2) hproper hfresh]
  obtain Y_w :: "(real \<times> real) set" and TY_w :: "(real \<times> real) set set" and h1 where
      hY_w: "top1_quotient_of_scheme_on Y_w TY_w w"
    and hh1: "top1_homeomorphism_on Y_ext TY_ext Y_w TY_w h1" by (by100 blast)
  have htopo_w: "is_topology_on_strict Y_w TY_w"
    using hY_w unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  \<comment> \<open>Step 3: uniqueness gives Y\\_w homeomorphic to Y (both quotients of w).\<close>
  from scheme_quotient_uniqueness[OF htopo_w htopo_Y hY_w assms(1)]
  obtain h2 where hh2: "top1_homeomorphism_on Y_w TY_w Y TY h2" by (by100 blast)
  \<comment> \<open>Step 4: Compose: Y\\_ext to Y\\_w to Y.\<close>
  from homeomorphism_comp[OF hh1 hh2]
  have hcomp: "top1_homeomorphism_on Y_ext TY_ext Y TY (h2 \<circ> h1)" .
  \<comment> \<open>Step 5: Transfer quotient of ?ext from Y\\_ext to Y.\<close>
  from scheme_quotient_transfer_along_homeomorphism[OF hY_ext hcomp htopo_Y]
  show ?thesis .
qed

\<comment> \<open>Homeomorphism-preservation for valid scheme operations (per expert audit step 8).
   This is the correct semantic theorem for the classification chain.\<close>
lemma valid_operation_preserves_quotient_homeo:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "top1_quotient_of_scheme_on X TX s"
      and "top1_valid_scheme_operation s t"
  shows "\<exists>(Y :: 'a set) (TY :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y TY t \<and>
    top1_homeomorphism_on X TX Y TY h"
  using assms(2,1)
proof (induction rule: top1_valid_scheme_operation.induct)
  case (v_rotate u v)
  have hq: "top1_quotient_of_scheme_on X TX (v @ u)"
    by (rule quotient_of_scheme_rotate[OF v_rotate.prems])
  have htopo: "is_topology_on X TX"
    using hq unfolding top1_quotient_of_scheme_on_def is_topology_on_strict_def by (by100 blast)
  show ?case by (rule homeo_realization_flat_introI[OF hq homeomorphism_id[OF htopo]])
next
  case (v_cancel u a v)
  \<comment> \<open>Cancel: §76(vi). The (n+2)-gon folds along cancelled edge pair to give n-gon.
     Step 1: Extract polygon P, quotient map q, vertices from the old quotient.
     Step 2: Define new polygon P' by skipping vertex at position |u|+1.
     Step 3: Show P' is a valid polygonal region for scheme u@v.
     Step 4: Use quotient\\_transport\\_by\\_homeomorphism.\<close>
  \<comment> \<open>Use homeo-realization: rotate to front, apply cancel, rotate back.\<close>
  show ?case
  proof (cases "length (u @ v) \<ge> 3")
    case True
    have h1: "top1_quotient_of_scheme_on X TX ([a, top1_inverse_edge a] @ v @ u)"
      using quotient_of_scheme_rotate[OF v_cancel.prems] by simp
    have hlen: "length (v @ u) \<ge> 3" using True by simp
    from front_cancel_realization_homeo[OF h1 hlen]
    obtain Y' :: "'a set" and TY' :: "'a set set" and h1' :: "'a \<Rightarrow> 'a" where
        hY': "top1_quotient_of_scheme_on Y' TY' (v @ u)"
        and hh1': "top1_homeomorphism_on X TX Y' TY' h1'"
      by (by100 blast)
    have "top1_quotient_of_scheme_on Y' TY' (u @ v)"
      using quotient_of_scheme_rotate[OF hY'] by simp
    thus ?thesis using hh1' by (rule homeo_realization_flat_introI)
  next
    case False
    \<comment> \<open>Short scheme: length(u@v) < 3.\<close>
    have hlen_src: "length (u @ [a, top1_inverse_edge a] @ v) \<ge> 3"
      using quotient_scheme_length_ge3[OF v_cancel.prems] .
    hence hlen_uv: "length (u @ v) \<ge> 1" by (by100 simp)
    show ?thesis
    proof (cases "length (u @ v) = 0")
      case True
      \<comment> \<open>length(u@v) = 0: source has length 2 < 3, so premise is false.\<close>
      hence "length (u @ [a, top1_inverse_edge a] @ v) = 2" by (by100 simp)
      hence False using hlen_src by (by100 linarith)
      thus ?thesis by (by100 simp)
    next
      case False2: False
      \<comment> \<open>length(u@v) \\<in> {1, 2}: genuinely false for length(u@v) = 2.
         For proper schemes: length(u@v) is even (from even source length - 2).
         So length(u@v) = 2 is the only remaining case (length 1 = odd, can't be proper).
         Target has length 2 < 3, so quotient\\_on is impossible.
         Never arises in the classification chain (even proper schemes only).\<close>
      show ?thesis sorry \<comment> \<open>Genuinely false for length(u@v)=2. Needs precondition.\<close>
    qed
  qed
next
  case (v_uncancel a u v)
  \<comment> \<open>Uncancel: §76(vii). Use front\\_uncancel\\_realization\\_homeo via rotation.\<close>
  have h1: "top1_quotient_of_scheme_on X TX (v @ u)"
    using quotient_of_scheme_rotate[OF v_uncancel.prems] by simp
  have hlen_vu: "length (v @ u) \<ge> 3"
    using quotient_scheme_length_ge3[OF h1] .
  from front_uncancel_realization_homeo[OF h1 hlen_vu, of a]
  obtain Y' :: "'a set" and TY' :: "'a set set" and h1' :: "'a \<Rightarrow> 'a" where
      hY': "top1_quotient_of_scheme_on Y' TY' ([a, top1_inverse_edge a] @ v @ u)"
      and hh1': "top1_homeomorphism_on X TX Y' TY' h1'"
    by (by100 blast)
  have "top1_quotient_of_scheme_on Y' TY' ((v @ u) @ [a, top1_inverse_edge a])"
    using quotient_of_scheme_rotate[OF hY'] by simp
  hence "top1_quotient_of_scheme_on Y' TY' (v @ (u @ [a, top1_inverse_edge a]))"
    by simp
  hence "top1_quotient_of_scheme_on Y' TY' ((u @ [a, top1_inverse_edge a]) @ v)"
    using quotient_of_scheme_rotate by (by100 fastforce)
  hence "top1_quotient_of_scheme_on Y' TY' (u @ [a, top1_inverse_edge a] @ v)"
    by simp
  thus ?case using hh1' by (rule homeo_realization_flat_introI)
next
  case v_cancel_reverse
  \<comment> \<open>v\\_cancel\\_reverse: u@v -> u@[a,inv a]@v. Same as uncancel.\<close>
  from quotient_of_scheme_uncancel_proved[OF v_cancel_reverse.prems]
  show ?case by (rule same_space_implies_homeo_realization)
next
  case (v_cut_paste_reverse u1_r a_r u2_r u3_r)
  \<comment> \<open>Reverse of cut-paste: needs reverse direction of the rearrangement.
     For proper schemes: use scheme\\_quotient\\_exists + forward cut\\_paste + uniqueness.
     For general: sorry pending proper chain restructuring.\<close>
  have "top1_quotient_of_scheme_on X TX (u1_r @ [(a_r, True)] @ u2_r @ [(a_r, True)] @ u3_r)"
    sorry \<comment> \<open>Same-space: quotient\\_scheme\\_edge\\_permutation with \\<sigma>\\<inverse>.\<close>
  thus ?case by (rule same_space_implies_homeo_realization_early)
next
  case (v_cut_paste2_reverse b_r u2_r u1_r u0_r a_r)
  \<comment> \<open>Reverse of cut-paste2: same geometric argument in reverse direction.\<close>
  have "top1_quotient_of_scheme_on X TX (u0_r @ [(a_r, True)] @ u1_r @ [(a_r, True)] @ u2_r)"
    sorry \<comment> \<open>Same-space: quotient\\_scheme\\_edge\\_permutation with \\<sigma>\\<inverse>.\<close>
  thus ?case by (rule same_space_implies_homeo_realization_early)
next
  case (v_invert w)
  have hq: "top1_quotient_of_scheme_on X TX (rev (map top1_inverse_edge w))"
    by (rule quotient_of_scheme_invert[OF v_invert.prems])
  have htopo: "is_topology_on X TX"
    using hq unfolding top1_quotient_of_scheme_on_def is_topology_on_strict_def by (by100 blast)
  show ?case by (rule homeo_realization_flat_introI[OF hq homeomorphism_id[OF htopo]])
next
  case (v_relabel new old w)
  from quotient_of_scheme_relabel_fresh[OF v_relabel.prems v_relabel(1) v_relabel(2)]
  show ?case by (rule same_space_implies_homeo_realization)
next
  case (v_flip_label w a)
  have hq: "top1_quotient_of_scheme_on X TX (map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) w)"
    by (rule quotient_scheme_flip_label[OF v_flip_label.prems])
  have htopo: "is_topology_on X TX"
    using hq unfolding top1_quotient_of_scheme_on_def is_topology_on_strict_def by (by100 blast)
  show ?case by (rule homeo_realization_flat_introI[OF hq homeomorphism_id[OF htopo]])
next
  case (v_cut_paste u1 a u2 u3)
  \<comment> \<open>Cut-paste: §76(iv). Homeomorphic realization via polygon cut-reglue.\<close>
  from quotient_of_scheme_cut_paste[OF v_cut_paste.prems] show ?case .
next
  case (v_cut_paste2 b u0 a u1 u2)
  \<comment> \<open>Cut-paste2: §76(v) variant.\<close>
  from quotient_of_scheme_cut_paste2[OF v_cut_paste2.prems] show ?case .
next
  case (v_cut_paste2_nonfresh u0 a u1 u2 b)
  \<comment> \<open>Cut-paste2 without freshness. Same underlying lemma.\<close>
  from quotient_of_scheme_cut_paste2[OF v_cut_paste2_nonfresh.prems] show ?case .
next
  case (v_cut_paste_opp u0 u1 a u2 u3)
  \<comment> \<open>Cut-paste-opp: §76(ix). Homeomorphic realization.\<close>
  from quotient_of_scheme_cut_paste_opp[OF v_cut_paste_opp.prems] show ?case .
next
  case (v_context_left y z prefix)
  \<comment> \<open>Context-left: valid operation y \\<to> z lifts to prefix@y \\<to> prefix@z.
     Per audit 22 option 2: nested case analysis on inner operation y \\<to> z.
     For v\\_relabel (fresh): relabeling the suffix is the same as relabeling
     the full scheme when the label only appears in the suffix (from properness).
     Other cases: admitted (not exercised in the normal form chain for proper schemes).\<close>
  from v_context_left.hyps
  show ?case
  proof (cases rule: top1_valid_scheme_operation.cases)
    case (v_relabel new old)
    \<comment> \<open>Inner operation is fresh relabeling: rename old \\<to> new in suffix y.
       If old \\<notin> labels(prefix) and new \\<notin> labels(prefix), this is a full-scheme relabel.\<close>
    have hfresh: "new \<notin> fst ` set y" and hne: "new \<noteq> old"
      and hz_eq: "z = map (\<lambda>(l, b). (if l = old then new else l, b)) y"
      using v_relabel by (by100 auto)+
    \<comment> \<open>If old does not appear in prefix, the context-left relabel = full-scheme relabel.\<close>
    show ?thesis
    proof (cases "old \<notin> fst ` set prefix \<and> new \<notin> fst ` set prefix")
      case True
      hence hold_fresh: "old \<notin> fst ` set prefix" and hnew_fresh: "new \<notin> fst ` set prefix"
        by (by100 auto)+
      \<comment> \<open>prefix@y \\<to> prefix@z is the same as map(rename) applied to prefix@y.
         Since old \\<notin> prefix: map(rename) doesn't change the prefix.
         Since new \\<notin> prefix: the full rename is fresh in prefix@y.\<close>
      have hfull_map: "prefix @ z = map (\<lambda>(l, b). (if l = old then new else l, b)) (prefix @ y)"
      proof -
        have "map (\<lambda>(l, b). (if l = old then new else l, b)) prefix = prefix"
          using hold_fresh by (induction prefix) (by100 auto)+
        thus ?thesis using hz_eq by (by100 simp)
      qed
      have hfull_fresh: "new \<notin> fst ` set (prefix @ y)"
        using hfresh hnew_fresh by (by100 auto)
      from quotient_of_scheme_relabel_fresh[OF v_context_left.prems hfull_fresh hne]
      have "top1_quotient_of_scheme_on X TX (prefix @ z)" using hfull_map by (by100 simp)
      thus ?thesis by (rule same_space_implies_homeo_realization)
    next
      case False
      \<comment> \<open>old or new appears in prefix: non-trivial case.
         For PROPER schemes this can't happen (label appears exactly 2 times,
         all in the suffix). For the classification chain, all schemes are proper.\<close>
      \<comment> \<open>Sub-case: if old \\<notin> y, the relabel is a no-op (z = y).\<close>
      show ?thesis
      proof (cases "old \<in> fst ` set y")
        case False2: False
        hence "z = y"
          unfolding hz_eq by (induction y) (by100 auto)+
        hence "prefix @ z = prefix @ y" by simp
        hence "top1_quotient_of_scheme_on X TX (prefix @ z)"
          using v_context_left.prems by simp
        thus ?thesis by (rule same_space_implies_homeo_realization)
      next
        case True2: True
        \<comment> \<open>old \\<in> y AND (old \\<in> prefix OR new \\<in> prefix): genuine cross-prefix relabel.
           For proper schemes: old appears exactly 2 times in prefix@y.
           If old \\<in> y: at least 1 in y. If old \\<in> prefix: at least 1 in prefix.
           Total \\<ge> 2. For proper: exactly 2. So old has 1 in prefix and 1 in y.
           The relabel changes the y-occurrence to new, creating new in y.
           Since new might also be in prefix: creates cross-prefix new-identification.
           This is genuinely non-trivial for non-proper schemes.\<close>
        show ?thesis sorry \<comment> \<open>Cross-prefix relabel with old in both prefix and suffix.
           Needs properness or multi-polygon argument.\<close>
      qed
    qed
  next
    \<comment> \<open>Other inner operations: not exercised by the normal form chain.
       The classification proof (scheme\\_normal\\_form\\_valid in AlgTopCached14)
       only uses v\\_context\\_left with inner operation = v\\_relabel (fresh).
       For proper schemes, the fresh-prefix case (proved above) always holds.
       These remaining sub-cases are structural completeness requirements.\<close>
    case (v_rotate u_r v_r)
    \<comment> \<open>Inner rotate: y = u\\_r@v\\_r \\<to> z = v\\_r@u\\_r.\<close>
    have hy_rot: "y = u_r @ v_r" and hz_rot: "z = v_r @ u_r"
      using v_rotate by (by100 auto)+
    show ?thesis
    proof (cases "u_r = [] \<or> v_r = []")
      case True
      hence "prefix @ z = prefix @ y" using hy_rot hz_rot by (by100 auto)
      hence "top1_quotient_of_scheme_on X TX (prefix @ z)"
        using v_context_left.prems by simp
      thus ?thesis by (rule same_space_implies_homeo_realization)
    next
      case False
      \<comment> \<open>Both u\\_r and v\\_r non-empty: genuine sub-sequence rotation.
         Cannot express as full-scheme rotation (prefix stays fixed).
         Needs multi-polygon paste infrastructure.\<close>
      show ?thesis sorry \<comment> \<open>Sub-sequence rotation with non-empty parts.\<close>
    qed
  next case (v_cancel u_c a_c v_c)
    \<comment> \<open>Inner cancel: y = u\\_c@[a\\_c,inv a\\_c]@v\\_c \\<to> z = u\\_c@v\\_c.
       Full scheme: (prefix@u\\_c)@[a\\_c,inv a\\_c]@v\\_c \\<to> (prefix@u\\_c)@v\\_c.
       This is a v\\_cancel on the full scheme with u' = prefix@u\\_c.\<close>
    have hy: "y = u_c @ [a_c, top1_inverse_edge a_c] @ v_c"
      and hz: "z = u_c @ v_c" using v_cancel by (by100 auto)+
    show ?thesis
    proof (cases "length ((prefix @ u_c) @ v_c) \<ge> 3")
      case True
      have hprems_eq: "prefix @ y = (prefix @ u_c) @ [a_c, top1_inverse_edge a_c] @ v_c"
        using hy by (by100 simp)
      have h1: "top1_quotient_of_scheme_on X TX
          ([a_c, top1_inverse_edge a_c] @ v_c @ prefix @ u_c)"
      proof -
        have "top1_quotient_of_scheme_on X TX ((prefix @ u_c) @ ([a_c, top1_inverse_edge a_c] @ v_c))"
          using v_context_left.prems hprems_eq by (by100 simp)
        from quotient_of_scheme_rotate[OF this]
        show ?thesis by (by100 simp)
      qed
      have hlen: "length (v_c @ prefix @ u_c) \<ge> 3" using True by (by100 simp)
      from front_cancel_realization_homeo[OF h1 hlen]
      obtain Y'c :: "'a set" and TY'c :: "'a set set" and h'c :: "'a \<Rightarrow> 'a" where
          hY'c: "top1_quotient_of_scheme_on Y'c TY'c (v_c @ prefix @ u_c)"
          and hh'c: "top1_homeomorphism_on X TX Y'c TY'c h'c"
        by (by100 blast)
      have "top1_quotient_of_scheme_on Y'c TY'c ((prefix @ u_c) @ v_c)"
        using quotient_of_scheme_rotate[OF hY'c] by (by100 simp)
      hence "top1_quotient_of_scheme_on Y'c TY'c (prefix @ u_c @ v_c)"
        by (by100 simp)
      hence "top1_quotient_of_scheme_on Y'c TY'c (prefix @ z)" using hz by (by100 simp)
      thus ?thesis using hh'c by (rule homeo_realization_flat_introI)
    next
      case False
      \<comment> \<open>Short case: length((prefix@u\\_c)@v\\_c) < 3. Genuinely false for length = 2.
         For proper schemes, never arises (even length sources).\<close>
      have "length ((prefix @ u_c) @ [a_c, top1_inverse_edge a_c] @ v_c) \<ge> 3"
        using quotient_scheme_length_ge3[OF v_context_left.prems] hy by (by100 simp)
      hence "length ((prefix @ u_c) @ v_c) \<ge> 1" by (by100 simp)
      show ?thesis sorry \<comment> \<open>Genuinely false for length((prefix@u\\_c)@v\\_c)=2.\<close>
    qed
  next case (v_uncancel a_u u_u v_u)
    \<comment> \<open>Inner uncancel: y = u\\_u@v\\_u \\<to> z = u\\_u@[a\\_u,inv a\\_u]@v\\_u.
       Full scheme: prefix@u\\_u@v\\_u \\<to> prefix@u\\_u@[a\\_u,inv a\\_u]@v\\_u.
       This is a v\\_cancel\\_reverse on the full scheme.\<close>
    have hy: "y = u_u @ v_u" and hz: "z = u_u @ [a_u, top1_inverse_edge a_u] @ v_u"
      using v_uncancel by (by100 auto)+
    have "top1_quotient_of_scheme_on X TX ((prefix @ u_u) @ v_u)"
      using v_context_left.prems hy by (by100 simp)
    from quotient_of_scheme_uncancel_proved[OF this, of a_u]
    have "top1_quotient_of_scheme_on X TX ((prefix @ u_u) @ [a_u, top1_inverse_edge a_u] @ v_u)" .
    hence "top1_quotient_of_scheme_on X TX (prefix @ z)" using hz by (by100 simp)
    thus ?thesis by (rule same_space_implies_homeo_realization)
  next case (v_cancel_reverse u_cr v_cr a_cr)
    \<comment> \<open>Same as v\\_uncancel above but via v\\_cancel\\_reverse.\<close>
    have hy: "y = u_cr @ v_cr" and hz: "z = u_cr @ [a_cr, top1_inverse_edge a_cr] @ v_cr"
      using v_cancel_reverse by (by100 auto)+
    have "top1_quotient_of_scheme_on X TX ((prefix @ u_cr) @ v_cr)"
      using v_context_left.prems hy by (by100 simp)
    from quotient_of_scheme_uncancel_proved[OF this, of a_cr]
    have "top1_quotient_of_scheme_on X TX ((prefix @ u_cr) @ [a_cr, top1_inverse_edge a_cr] @ v_cr)" .
    hence "top1_quotient_of_scheme_on X TX (prefix @ z)" using hz by (by100 simp)
    thus ?thesis by (rule same_space_implies_homeo_realization)
  next case (v_cut_paste_reverse u1_cpr a_cpr u2_cpr u3_cpr)
    \<comment> \<open>Inner cut-paste-reverse in suffix = full-scheme v\\_cut\\_paste\\_reverse with u1' = prefix@u1.\<close>
    have hy_r: "y = u1_cpr @ [(a_cpr, True), (a_cpr, True)] @ rev (map top1_inverse_edge u2_cpr) @ u3_cpr"
      and hz_r: "z = u1_cpr @ [(a_cpr, True)] @ u2_cpr @ [(a_cpr, True)] @ u3_cpr"
      using v_cut_paste_reverse by (by100 auto)+
    have "top1_quotient_of_scheme_on X TX
        ((prefix @ u1_cpr) @ [(a_cpr, True), (a_cpr, True)] @ rev (map top1_inverse_edge u2_cpr) @ u3_cpr)"
      using v_context_left.prems hy_r by (by100 simp)
    hence "top1_quotient_of_scheme_on X TX
        ((prefix @ u1_cpr) @ [(a_cpr, True)] @ u2_cpr @ [(a_cpr, True)] @ u3_cpr)"
      sorry \<comment> \<open>Same-space: reverse edge permutation (same sorry as v\\_cut\\_paste\\_reverse outer case).\<close>
    hence "top1_quotient_of_scheme_on X TX (prefix @ z)" using hz_r by (by100 simp)
    thus ?thesis by (rule same_space_implies_homeo_realization)
  next case (v_cut_paste2_reverse b_cpr u2_cpr u1_cpr u0_cpr a_cpr)
    \<comment> \<open>Inner cut-paste2-reverse: similar pattern.\<close>
    have hy_r: "y = [(b_cpr, True)] @ u2_cpr @ [(b_cpr, True)] @ u1_cpr @ rev (map top1_inverse_edge u0_cpr)"
      and hz_r: "z = u0_cpr @ [(a_cpr, True)] @ u1_cpr @ [(a_cpr, True)] @ u2_cpr"
      using v_cut_paste2_reverse by (by100 auto)+
    show ?thesis sorry \<comment> \<open>Full-scheme cut-paste2-reverse: prefix splitting differs.\<close>
  next case v_invert
    \<comment> \<open>Inner invert: y = w \\<to> z = rev(inv w).
       Cannot express as full-scheme invert (prefix is not inverted).
       For no-shared-labels case: ROTATE + INVERT + multi-flip restores prefix.
       But multi-flip needs induction over prefix labels.
       For shared-labels case: needs multi-polygon infrastructure.\<close>
    show ?thesis sorry
  next case (v_flip_label a_fl)
    \<comment> \<open>Inner operation flips direction of label a\\_fl in suffix y.
       If a\\_fl \\<notin> labels(prefix): equivalent to full-scheme flip.\<close>
    have hz_fl: "z = map (\<lambda>(l,b). (l, if l = a_fl then \<not>b else b)) y" using v_flip_label by (by100 auto)
    show ?thesis
    proof (cases "a_fl \<notin> fst ` set prefix")
      case True
      have "prefix @ z = map (\<lambda>(l,b). (l, if l = a_fl then \<not>b else b)) (prefix @ y)"
      proof -
        have "map (\<lambda>(l,b). (l, if l = a_fl then \<not>b else b)) prefix = prefix"
          using True by (induction prefix) (by100 auto)+
        thus ?thesis using hz_fl by (by100 simp)
      qed
      from quotient_scheme_flip_label[OF v_context_left.prems]
      have "top1_quotient_of_scheme_on X TX (map (\<lambda>(l,b). (l, if l = a_fl then \<not>b else b)) (prefix @ y))" .
      hence "top1_quotient_of_scheme_on X TX (prefix @ z)"
        using \<open>prefix @ z = _\<close> by (by100 simp)
      thus ?thesis by (rule same_space_implies_homeo_realization)
    next
      case False
      show ?thesis
      proof (cases "a_fl \<in> fst ` set y")
        case False2: False
        hence "z = y" unfolding hz_fl by (induction y) (by100 auto)+
        hence "top1_quotient_of_scheme_on X TX (prefix @ z)"
          using v_context_left.prems by simp
        thus ?thesis by (rule same_space_implies_homeo_realization)
      next
        case True2: True
        show ?thesis sorry \<comment> \<open>a\\_fl in both prefix and suffix: genuine cross-prefix flip.\<close>
      qed
    qed
  next case (v_cut_paste u1_cp a_cp u2_cp u3_cp)
    \<comment> \<open>Inner cut-paste in suffix = full-scheme cut-paste with u1' = prefix@u1.\<close>
    have hy: "y = u1_cp @ [(a_cp, True)] @ u2_cp @ [(a_cp, True)] @ u3_cp"
      and hz: "z = u1_cp @ [(a_cp, True), (a_cp, True)] @ rev (map top1_inverse_edge u2_cp) @ u3_cp"
      using v_cut_paste by (by100 auto)+
    have "top1_quotient_of_scheme_on X TX
        ((prefix @ u1_cp) @ [(a_cp, True)] @ u2_cp @ [(a_cp, True)] @ u3_cp)"
      using v_context_left.prems hy by (by100 simp)
    from quotient_of_scheme_cut_paste[OF this]
    obtain Y'cp :: "'a set" and TY'cp :: "'a set set" and h'cp :: "'a \<Rightarrow> 'a" where
        hY'cp: "top1_quotient_of_scheme_on Y'cp TY'cp
          ((prefix @ u1_cp) @ [(a_cp, True), (a_cp, True)] @ rev (map top1_inverse_edge u2_cp) @ u3_cp)"
        and hh'cp: "top1_homeomorphism_on X TX Y'cp TY'cp h'cp"
      by (by100 blast)
    have "top1_quotient_of_scheme_on Y'cp TY'cp (prefix @ z)" using hY'cp hz by (by100 simp)
    thus ?thesis using hh'cp by (rule homeo_realization_flat_introI)
  next case (v_cut_paste2 b_cp u0_cp a_cp2 u1_cp2 u2_cp)
    \<comment> \<open>Inner cut-paste2 in suffix = full-scheme cut-paste2 with u0' = prefix@u0.\<close>
    have hy: "y = u0_cp @ [(a_cp2, True)] @ u1_cp2 @ [(a_cp2, True)] @ u2_cp"
      and hz: "z = [(b_cp, True)] @ u2_cp @ [(b_cp, True)] @ u1_cp2 @ rev (map top1_inverse_edge u0_cp)"
      using v_cut_paste2 by (by100 auto)+
    show ?thesis sorry \<comment> \<open>Full-scheme cut-paste2 with different prefix splitting.\<close>
  next case (v_cut_paste2_nonfresh u0_nf a_nf u1_nf u2_nf b_nf)
    show ?thesis sorry \<comment> \<open>Same as v\\_cut\\_paste2.\<close>
  next case (v_cut_paste_opp u0_opp u1_opp a_opp u2_opp u3_opp)
    \<comment> \<open>Inner cut-paste-opp in suffix = full-scheme cut-paste-opp with u0' = prefix@u0.\<close>
    have hy: "y = u0_opp @ u1_opp @ [(a_opp, True)] @ u2_opp @ [(a_opp, False)] @ u3_opp"
      and hz: "z = u0_opp @ [(a_opp, True)] @ u2_opp @ [(a_opp, False)] @ u1_opp @ u3_opp"
      using v_cut_paste_opp by (by100 auto)+
    have "top1_quotient_of_scheme_on X TX
        ((prefix @ u0_opp) @ u1_opp @ [(a_opp, True)] @ u2_opp @ [(a_opp, False)] @ u3_opp)"
      using v_context_left.prems hy by (by100 simp)
    from quotient_of_scheme_cut_paste_opp[OF this]
    obtain Y'opp :: "'a set" and TY'opp :: "'a set set" and h'opp :: "'a \<Rightarrow> 'a" where
        hY'opp: "top1_quotient_of_scheme_on Y'opp TY'opp
          ((prefix @ u0_opp) @ [(a_opp, True)] @ u2_opp @ [(a_opp, False)] @ u1_opp @ u3_opp)"
        and hh'opp: "top1_homeomorphism_on X TX Y'opp TY'opp h'opp"
      by (by100 blast)
    have "top1_quotient_of_scheme_on Y'opp TY'opp (prefix @ z)" using hY'opp hz by (by100 simp)
    thus ?thesis using hh'opp by (rule homeo_realization_flat_introI)
  next case v_context_left
    \<comment> \<open>Nested context-left: inner is v\\_context\\_left(prefix2, y2, z2).
       The full operation: (prefix@prefix2)@y2 \\<to> (prefix@prefix2)@z2.
       This is a v\\_context\\_left with combined prefix, handled by the lemma itself.\<close>
    show ?thesis sorry \<comment> \<open>Nested context-left: needs recursion on nesting depth.\<close>
  qed
qed

\<comment> \<open>Chain: valid equivalence preserves quotient homeomorphism type.\<close>
lemma valid_equiv_preserves_quotient_homeo:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "top1_quotient_of_scheme_on X TX s"
      and "top1_valid_scheme_equiv s t"
  shows "\<exists>(Y :: 'a set) (TY :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y TY t \<and>
    top1_homeomorphism_on X TX Y TY h"
  using assms(2,1) unfolding top1_valid_scheme_equiv_def
proof (induction rule: rtranclp.induct)
  case rtrancl_refl
  then show ?case by (rule same_space_implies_homeo_realization)
next
  case (rtrancl_into_rtrancl a b c)
  \<comment> \<open>Step: IH gives \\<exists>Y TY h for 'a'; valid\\_op gives \\<exists>Z TZ g for 'b\\<to>c'; compose.\<close>
  from rtrancl_into_rtrancl.IH[OF rtrancl_into_rtrancl.prems]
  have hIH: "\<exists>(Y :: 'a set) (TY :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y TY b \<and> top1_homeomorphism_on X TX Y TY h" .
  then obtain Y :: "'a set" and TY :: "'a set set" and hy :: "'a \<Rightarrow> 'a" where
      qY: "top1_quotient_of_scheme_on Y TY b"
    and hXY: "top1_homeomorphism_on X TX Y TY hy"
    by (by100 blast)
  from valid_operation_preserves_quotient_homeo[OF qY rtrancl_into_rtrancl.hyps(2)]
  obtain Z :: "'a set" and TZ :: "'a set set" and gz :: "'a \<Rightarrow> 'a" where
      qZ: "top1_quotient_of_scheme_on Z TZ c"
    and hYZ: "top1_homeomorphism_on Y TY Z TZ gz"
    by (by100 blast)
  have hXZ: "top1_homeomorphism_on X TX Z TZ (gz \<circ> hy)"
    using homeomorphism_comp[OF hXY hYZ] .
  show ?case using qZ hXZ by (rule homeo_realization_flat_introI)
qed

\<comment> \<open>Proper version: valid operations preserve quotient homeomorphism type for proper schemes.
   Uses front\\_cancel\\_proper (which depends only on spur\\_collapse\\_cancel\\_homeo)
   and quotient\\_of\\_scheme\\_cut\\_paste\\_opp\\_proper + quotient\\_of\\_scheme\\_cut\\_paste\\_proper
   for the cut-paste operations. Avoids the FALSE same-space sorrys.\<close>
\<comment> \<open>TODO: The proper version currently delegates to the general chain which has
   unnecessary sorrys (non-fresh prefix, short-scheme, etc.) that are eliminable with
   properness. Future: implement proper-specific single-step lemma and chain it here.
   Impact: would eliminate ~5 structural sorrys from the effective sorry count.\<close>
lemma valid_equiv_preserves_quotient_homeo_proper:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "top1_quotient_of_scheme_on X TX s"
      and "top1_valid_scheme_equiv s t"
      and hproper: "\<forall>label. card {i. i < length s \<and> fst (s ! i) = label} \<in> {0, 2}"
  shows "\<exists>(Y :: 'a set) (TY :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y TY t \<and>
    top1_homeomorphism_on X TX Y TY h"
  \<comment> \<open>PROPER CHAIN: uses proper-specific proofs for each step.
     All forward operations are proved except cut\\_paste/cut\\_paste2/cut\\_paste\\_opp.
     For the classification chain: all operations are forward, scheme stays proper.\<close>
  using valid_equiv_preserves_quotient_homeo[OF assms(1) assms(2)] .

\<comment> \<open>Bridge moved to before valid\\_operation\\_preserves.\<close>


\<comment> \<open>Old bridge lemmas (scheme\\_equiv\\_homeomorphic, scheme\\_rotate/cancel/invert\\_homeomorphic):
   DELETED per expert audit 21. Superseded by valid\\_equiv\\_preserves\\_quotient\\_homeo.\<close>

\<comment> \<open>§76 book theorem (old formulation, kept per policy). Valid version: valid\\_equiv\\_preserves\\_quotient\\_homeo.\<close>
theorem Theorem_76_elementary_operations:
  fixes scheme1 scheme2 :: "('a \<times> bool) list"
    and X1 X2 :: "'x set" and TX1 TX2 :: "'x set set"
  assumes "is_topology_on_strict X1 TX1" and "is_topology_on_strict X2 TX2"
      and "top1_elementary_scheme_operation scheme1 scheme2"
      and "top1_quotient_of_scheme_on X1 TX1 scheme1
         \<and> top1_quotient_of_scheme_on X2 TX2 scheme2"
  shows "\<exists>h. top1_homeomorphism_on X1 TX1 X2 TX2 h"
proof -
  \<comment> \<open>Step 1: elementary \\<to> valid operation (mostly direct correspondence).\<close>
  \<comment> \<open>Proof strategy: convert elementary to valid operation, apply preservation + uniqueness.\<close>
  from assms(4) have hX1: "top1_quotient_of_scheme_on X1 TX1 scheme1" by (by100 blast)
  from assms(4) have hX2: "top1_quotient_of_scheme_on X2 TX2 scheme2" by (by100 blast)
  \<comment> \<open>Elementary \\<to> valid (by cases; most are identical).\<close>
  from assms(3) have hvalid: "top1_valid_scheme_operation scheme1 scheme2"
  proof (induction rule: top1_elementary_scheme_operation.induct)
    case rotate show ?case by (rule top1_valid_scheme_operation.v_rotate)
  next
    case cancel show ?case by (rule top1_valid_scheme_operation.v_cancel)
  next
    case uncancel show ?case by (rule top1_valid_scheme_operation.v_cancel_reverse)
  next
    case invert show ?case by (rule top1_valid_scheme_operation.v_invert)
  next
    case (relabel w old new)
    show ?case
    proof (cases "new \<in> fst ` set w")
      case False
      \<comment> \<open>new \\<notin> labels(w): v\\_relabel applies directly.\<close>
      show ?thesis
      proof (cases "new = old")
        case True
        \<comment> \<open>new = old: the relabel is a no-op.\<close>
        have "map (\<lambda>(l,b). (if l = old then new else l, b)) w = w"
          using True by (induction w) (by100 auto)+
        thus ?thesis by (simp add: top1_valid_scheme_operation.v_rotate[of w "[]", simplified])
      next
        case False2: False
        from top1_valid_scheme_operation.v_relabel[OF \<open>new \<notin> fst ` set w\<close> False2]
        show ?thesis .
      qed
    next
      case True
      \<comment> \<open>new \\<in> labels(w): can't use v\\_relabel (freshness fails).\<close>
      show ?thesis
      proof (cases "old \<in> fst ` set w")
        case False
        \<comment> \<open>old \\<notin> labels(w): relabel is a no-op.\<close>
        have "map (\<lambda>(l,b). (if l = old then new else l, b)) w = w"
          using False by (induction w) (by100 auto)+
        thus ?thesis by (simp add: top1_valid_scheme_operation.v_rotate[of w "[]", simplified])
      next
        case True2: True
        \<comment> \<open>Both old and new in w: genuine non-fresh relabel.\<close>
        show ?thesis sorry \<comment> \<open>Non-fresh relabel: old,new both in scheme.\<close>
      qed
    qed
  next
    case flip_label show ?case by (rule top1_valid_scheme_operation.v_flip_label)
  next
    case cut_paste show ?case by (rule top1_valid_scheme_operation.v_cut_paste)
  next
    case cut_paste2 show ?case by (rule top1_valid_scheme_operation.v_cut_paste2_nonfresh)
  next
    case cut_paste_opp show ?case by (rule top1_valid_scheme_operation.v_cut_paste_opp)
  next
    case (context_left y z prefix)
    from context_left.IH
    show ?case by (rule top1_valid_scheme_operation.v_context_left)
  qed
  \<comment> \<open>Valid op preservation + uniqueness.\<close>
  from valid_operation_preserves_quotient_homeo[OF hX1 hvalid]
  obtain Y :: "'x set" and TY :: "'x set set" and g :: "'x \<Rightarrow> 'x" where
      hY: "top1_quotient_of_scheme_on Y TY scheme2"
    and hg: "top1_homeomorphism_on X1 TX1 Y TY g"
    by (by100 blast)
  have htopo_Y: "is_topology_on_strict Y TY"
    using hY unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  from scheme_quotient_uniqueness[OF htopo_Y assms(2) hY hX2]
  obtain h2 where hh2: "top1_homeomorphism_on Y TY X2 TX2 h2" by (by100 blast)
  from homeomorphism_comp[OF hg hh2]
  show ?thesis by (by100 blast)
qed

section \<open>*\<S>78 Constructing Compact Surfaces\<close>


\<comment> \<open>standard\_simplex moved to AlgTopCached8.\<close>


\<comment> \<open>Theorem\\_78\\_1\\_triangulable\\_surface moved to AlgTopCached18.\<close>

(** from \<S>78 Theorem 78.2: connected compact triangulable surfaces are
    quotients of a single polygonal region. **)
theorem Theorem_78_2_connected_polygonal_quotient:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "top1_is_surface_on X TX"
      and "top1_connected_on X TX"
      and "top1_is_triangulable_on X TX"
  shows "\<exists>(P :: (real \<times> real) set) n q.
           top1_is_polygonal_region_on P n
         \<and> top1_quotient_map_on P
             (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P)
             X TX q"
proof -
  \<comment> \<open>Munkres 78.2: By Theorem 78.1, X is a quotient of triangles.
     Since X is connected, the triangles can be assembled into a single
     polygonal region by iteratively pasting triangles along shared edges.
     Start with one triangle. At each step, an adjacent triangle shares
     exactly one edge with the current polygon; paste it along that edge
     to get a polygon with 2 more sides (minus the shared edge = net +0 or +1).
     Repeat until all triangles are incorporated.\<close>
  \<comment> \<open>Step 1: By Theorem 78.1, X = quotient of finitely many triangles.\<close>
  \<comment> \<open>Step 2: Since X is connected, the dual graph of the triangulation is connected.
     Choose a spanning tree. Walk the tree, merging triangles along shared edges.
     Each merge: paste two polygons along a common edge to get a larger polygon.\<close>
  \<comment> \<open>Step 3: After merging all triangles, we have a single polygon P with
     boundary identifications reproducing X.\<close>
  \<comment> \<open>Step 1: By Theorem 78.1, X is a quotient of finitely many triangular regions.\<close>
  from Theorem_78_1_triangulable_surface[OF assms(1) assms(3)]
  obtain \<T> q_tri where h\<T>: "finite \<T>" "\<T> \<noteq> {}"
      "\<forall>T \<in> \<T>. top1_is_polygonal_region_on T 3"
      "\<forall>T \<in> \<T>. top1_continuous_map_on T
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) X TX q_tri"
      "(\<Union>T\<in>\<T>. q_tri ` T) = X"
      "\<forall>U. U \<subseteq> X \<longrightarrow>
          (U \<in> TX \<longleftrightarrow> (\<forall>T\<in>\<T>. {p\<in>T. q_tri p \<in> U} \<in>
              subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T))"
    by (by100 auto)
  \<comment> \<open>Step 2: Iteratively paste triangles along shared edges using Theorem 76.1 (\\<S>76).
     Book proof: "As long as two regions have edges bearing the same label, we can
     paste them together. Eventually either one has a single polygon (theorem proved)
     or several polygons with no shared labels. The latter gives a disconnected space,
     contradicting X connected."
     Formally: induction on card(\\<T>). If card = 1: done. If card > 1: find two regions
     sharing a label, paste them (§76.1), reducing card by 1. Apply IH.\<close>
  \<comment> \<open>Base case: if card(\\<T>) = 1, the single triangle is already a polygon.\<close>
  have hbase: "card \<T> = 1 \<Longrightarrow> ?thesis"
  proof -
    assume "card \<T> = 1"
    then obtain T0 where hT0: "\<T> = {T0}" using card_1_singletonE by (by100 blast)
    have hpoly: "top1_is_polygonal_region_on T0 3" using h\<T>(3) hT0 by (by100 blast)
    \<comment> \<open>q\\_tri restricted to T0 is a quotient map from T0 to X.
       Coverage: q\\_tri ` T0 = X (since \\<Union>\\<T> = X and \\<T> = {T0}).
       Quotient topology: U \\<in> TX \\<longleftrightarrow> preimage in T0 is open (from h\\<T>(6)).\<close>
    have hcov: "q_tri ` T0 = X" using h\<T>(5) hT0 by (by100 auto)
    have hcont: "top1_continuous_map_on T0
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T0) X TX q_tri"
      using h\<T>(4) hT0 by (by100 blast)
    let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T0"
    have hquot_cond: "\<And>U. U \<subseteq> X \<Longrightarrow> U \<in> TX \<longleftrightarrow> {p\<in>T0. q_tri p \<in> U} \<in> ?TP"
    proof -
      fix U assume "U \<subseteq> X"
      from h\<T>(6)[rule_format, OF this]
      have "U \<in> TX \<longleftrightarrow> (\<forall>T\<in>\<T>. {p\<in>T. q_tri p \<in> U} \<in>
          subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T)" .
      also have "\<dots> = ({p\<in>T0. q_tri p \<in> U} \<in> ?TP)"
        using hT0 by simp
      finally show "U \<in> TX \<longleftrightarrow> {p\<in>T0. q_tri p \<in> U} \<in> ?TP" .
    qed
    have hquot: "top1_quotient_map_on T0 ?TP X TX q_tri"
      unfolding top1_quotient_map_on_def
    proof (intro conjI allI impI)
      show "is_topology_on T0 ?TP"
        using subspace_topology_is_topology_on[OF product_topology_on_is_topology_on[OF
          top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV]] by simp
      show "is_topology_on X TX"
        using assms(1) unfolding top1_is_surface_on_def top1_connected_on_def by (by100 blast)
      show "top1_continuous_map_on T0 ?TP X TX q_tri" by (rule hcont)
      show "q_tri ` T0 = X" by (rule hcov)
      fix V assume "V \<subseteq> X" "{p \<in> T0. q_tri p \<in> V} \<in> ?TP"
      thus "V \<in> TX" using hquot_cond[OF \<open>V \<subseteq> X\<close>] by simp
    qed
    show ?thesis
      apply (rule exI[of _ T0], rule exI[of _ 3], rule exI[of _ q_tri])
      using hpoly hquot by (by100 blast)
  qed
  \<comment> \<open>Inductive step: if card > 1, find two adjacent triangles, paste them.\<close>
  show ?thesis
  proof (cases "card \<T> = 1")
    case True thus ?thesis by (rule hbase)
  next
    case False
    \<comment> \<open>card(\\<T>) > 1. By connectedness of X, two triangles share an edge.
       Paste them (\\<S>76 Theorem 76.1) to get a larger polygon. Repeat.\<close>
    have "card \<T> \<noteq> 0" using h\<T>(2) h\<T>(1) by (by100 auto)
    hence "card \<T> > 1" using False \<open>card \<T> \<noteq> 0\<close> by (by100 linarith)
    show ?thesis sorry \<comment> \<open>Induction on card(\\<T>) > 1. At each step, paste two adjacent
       regions sharing a label. When card = 1: done (base case above).\<close>
  qed
qed

\<comment> \<open>Sphere realization: the quotient of the sphere scheme [(a,T),(a,F),(b,T),(b,F)]
   is homeomorphic to S2 (the unit sphere in R3).
   This is a specific geometric fact about the 4-gon quotient with two adjacent cancel pairs.
   The identification collapses all boundary edges to two points (poles), leaving S2.\<close>
lemma sphere_scheme_realizes_S2:
  fixes a b :: "'b"
  assumes hab: "a \<noteq> b"
      and hY: "top1_quotient_of_scheme_on Y TY [(a, True), (a, False), (b, True), (b, False)]"
  shows "\<exists>g. top1_homeomorphism_on Y TY top1_S2 top1_S2_topology g"
  sorry \<comment> \<open>SPHERE REALIZATION.
     Proof: extract 4-gon P with q: P -> Y. Define f: P -> S2 via
     f(x,y) = (sin(pi*t2)*cos(2*pi*t1), sin(pi*t2)*sin(2*pi*t1), cos(pi*t2))
     where (t1,t2) maps P to [0,1]x[0,1]. f is continuous, surjective, and
     constant on q-fibres. Induced map: continuous bijection, compact to Hausdorff -> homeo.
     Independent of paste-chain infrastructure. Estimated: ~200 lines.\<close>

theorem Theorem_77_5_classification:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "top1_is_surface_on X TX"
      and "top1_is_triangulable_on X TX"
  shows "(\<exists>h. top1_homeomorphism_on X TX top1_S2 top1_S2_topology h)
       \<or> (\<exists>n > 0. \<exists>(T_n::'a set) TT h.
             top1_is_n_fold_torus_on T_n TT n
           \<and> top1_homeomorphism_on X TX T_n TT h)
       \<or> (\<exists>m > 0. \<exists>(P_m::'a set) TP h.
             top1_is_m_fold_projective_on P_m TP m
           \<and> top1_homeomorphism_on X TX P_m TP h)"
proof -
  \<comment> \<open>Munkres 77.5: By Theorem 78.2, X is a quotient of a single polygonal region by
     an edge scheme w. Apply elementary operations (Theorem 76) to reduce w to one of:
     (i) the empty scheme (giving S^2),
     (ii) a_1 b_1 a_1\<inverse> b_1\<inverse> \<cdots> a_n b_n a_n\<inverse> b_n\<inverse> (giving the n-fold torus T_n), or
     (iii) a_1 a_1 \<cdots> a_m a_m (giving the m-fold projective plane P_m).
     The reduction proceeds in steps:
     Step 1: bring all vertices to one equivalence class;
     Step 2: collect all pairs aa into adjacent positions;
     Step 3: pair off remaining letters into commutator blocks aba\<inverse>b\<inverse>.\<close>
  have hconn: "top1_connected_on X TX"
    using assms(1) unfolding top1_is_surface_on_def by (by100 blast)
  obtain P n q where hP: "top1_is_polygonal_region_on P n"
      and hq: "top1_quotient_map_on P
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q"
    using Theorem_78_2_connected_polygonal_quotient[OF assms(1) hconn assms(2)] by (by100 blast)
  \<comment> \<open>Step 1: From the polygonal quotient, extract the edge labeling scheme.\<close>
  \<comment> \<open>Step 1: Extract edge scheme from the polygonal quotient.
     The polygon P has n edges. The quotient map q identifies boundary edges in pairs.
     For each pair of identified edges: assign a shared label. The direction (same or opposite)
     determines the exponent (True/False). This gives the edge scheme.
     The scheme satisfies quotient\\_of\\_scheme\\_on by construction.\<close>
  obtain scheme :: "(nat \<times> bool) list" where
      hsch: "top1_quotient_of_scheme_on X TX scheme"
      and hproper: "\<forall>label. card {i. i < length scheme \<and> fst (scheme!i) = label} \<in> {0, 2}"
    sorry \<comment> \<open>Extract proper scheme from polygonal quotient.
       Construction: P has n edges. q identifies edges in pairs (from surface = no boundary).
       Each pair gets a shared label. Properness: each label appears exactly 0 or 2 times
       (from the pairing structure of edge identifications on a closed surface).\<close>
  have hlen_ge4: "length scheme \<ge> 4"
  proof -
    from hsch obtain P0 q0 where "top1_is_polygonal_region_on P0 (length scheme)"
      by (rule quotient_of_scheme_extract)
    hence "length scheme \<ge> 3" unfolding top1_is_polygonal_region_on_def by (by100 blast)
    moreover have "even (length scheme)" using proper_scheme_even_length[OF hproper] .
    ultimately show ?thesis by (by100 presburger)
  qed
  \<comment> \<open>Apply scheme\_normal\_form: sphere, torus, or projective.\<close>
  \<comment> \<open>Use valid normal form (avoids old §76 chain).\<close>
  from scheme_normal_form_valid[OF hlen_ge4 hproper]
  have hNF_valid: "(\<exists>a b. a \<noteq> b \<and> top1_valid_scheme_equiv scheme [(a, True), (a, False), (b, True), (b, False)])
       \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_valid_scheme_equiv scheme w)
       \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_valid_scheme_equiv scheme w)" .
  \<comment> \<open>Theorem 77.5 now routes through valid chain directly (no old scheme\\_equiv needed).\<close>
  \<comment> \<open>Step 3: Each normal form corresponds to the standard surface.
     - Empty/sphere: cancellation gives S² (a@a⁻¹@b@b⁻¹ with cancellation).
     - Torus scheme: the standard n-torus IS the quotient of this scheme
       (by definition top1\\_is\\_n\\_fold\\_torus\\_on). scheme\\_quotient\\_uniqueness gives homeo.
     - Projective scheme: similarly, top1\\_is\\_m\\_fold\\_projective\\_on.
     Plus: Theorem 76 preserves quotient homeomorphism type, so scheme\\_equiv gives homeo.\<close>
  show ?thesis
  proof -
    \<comment> \<open>Use valid chain: valid\\_equiv\\_preserves\\_quotient\\_homeo gives Y \\<cong> X directly.\<close>
    from hNF_valid show ?thesis
    proof (elim disjE exE conjE)
      \<comment> \<open>Case 0: sphere case. scheme ~ [(a,T),(a,F),(b,T),(b,F)].\<close>
      fix a_s b_s assume hab_s: "a_s \<noteq> b_s"
          and hequiv_s: "top1_valid_scheme_equiv scheme [(a_s, True), (a_s, False), (b_s, True), (b_s, False)]"
      \<comment> \<open>Step 1: X is homeomorphic to some quotient Y of the sphere scheme.\<close>
      \<comment> \<open>Use proper version (avoids FALSE same-space sorrys in general chain).\<close>
      from valid_equiv_preserves_quotient_homeo_proper[OF hsch hequiv_s hproper]
      obtain Y :: "'a set" and TY :: "'a set set" and h :: "'a \<Rightarrow> 'a" where
        hY: "top1_quotient_of_scheme_on Y TY [(a_s, True), (a_s, False), (b_s, True), (b_s, False)]"
        and hXY: "top1_homeomorphism_on X TX Y TY h"
        by (by100 blast)
      \<comment> \<open>Step 2: Y (quotient of sphere scheme) \\<cong> S2.
         Needs sphere\\_scheme\\_realizes\\_sphere lemma (geometric construction).\<close>
      \<comment> \<open>Sphere scheme realizes S2: quotient of [(a,T),(a,F),(b,T),(b,F)] \\<cong> S2.
         The scheme has two adjacent cancel pairs. Both pairs cancel, collapsing
         the 4-gon boundary to a topological sphere.

         Proof approach: the quotient map sends the square to S2 via:
         1. Map the interior of the square homeomorphically to S2 minus two points
         2. The boundary collapses to two points (north and south poles)
         3. The combined map is a continuous bijection from quotient to S2
         4. By Theorem 26.6 (compact \\<to> Hausdorff): it's a homeomorphism.

         Alternative: use the double-cancel approach:
         1. First cancel the a-pair: quotient([(a,T),(a,F),(b,T),(b,F)]) \\<cong> quotient([(b,T),(b,F)])
            But [(b,T),(b,F)] has only 2 edges (too short for polygon quotient!)
         2. Instead: the quotient of [(a,T),(a,F),(b,T),(b,F)]) is a closed surface
            with Euler characteristic 2 = sphere.\<close>
      have "\<exists>g. top1_homeomorphism_on Y TY top1_S2 top1_S2_topology g"
        by (rule sphere_scheme_realizes_S2[OF hab_s hY])
      then obtain g where hYS: "top1_homeomorphism_on Y TY top1_S2 top1_S2_topology g" by (by100 blast)
      \<comment> \<open>Step 3: X \\<cong> Y \\<cong> S2 by composition.\<close>
      from homeomorphism_comp[OF hXY hYS]
      have "top1_homeomorphism_on X TX top1_S2 top1_S2_topology (g \<circ> h)" .
      thus ?thesis by (by100 blast)
    next
      \<comment> \<open>Case 1: scheme \\<sim> torus normal form.\<close>
      fix n w assume hn: "n > 0" and htor: "top1_is_torus_scheme w n"
          and hequiv: "top1_valid_scheme_equiv scheme w"
      \<comment> \<open>valid chain: \\<exists>Y TY h. quotient Y TY w \\<and> homeo X TX Y TY h.\<close>
      from valid_equiv_preserves_quotient_homeo_proper[OF hsch hequiv hproper]
      obtain Y :: "'a set" and TY :: "'a set set" and h_t :: "'a \<Rightarrow> 'a" where
        hY_t: "top1_quotient_of_scheme_on Y TY w" and hXY_t: "top1_homeomorphism_on X TX Y TY h_t"
        by (by100 blast)
      have "top1_quotient_of_scheme_on Y TY (top1_n_torus_scheme n)"
        using hY_t htor unfolding top1_is_torus_scheme_def by (by100 simp)
      hence "top1_is_n_fold_torus_on Y TY n" using hn unfolding top1_is_n_fold_torus_on_def by (by100 simp)
      show ?thesis using hn \<open>top1_is_n_fold_torus_on Y TY n\<close> hXY_t by (by100 blast)
    next
      \<comment> \<open>Case 3: scheme \\<sim> projective normal form.\<close>
      fix m w assume hm: "m > 0" and hproj: "top1_is_projective_scheme w m"
          and hequiv: "top1_valid_scheme_equiv scheme w"
      from valid_equiv_preserves_quotient_homeo_proper[OF hsch hequiv hproper]
      obtain Y :: "'a set" and TY :: "'a set set" and h_p :: "'a \<Rightarrow> 'a" where
        hY_p: "top1_quotient_of_scheme_on Y TY w" and hXY_p: "top1_homeomorphism_on X TX Y TY h_p"
        by (by100 blast)
      have "top1_quotient_of_scheme_on Y TY (top1_m_projective_scheme m)"
        using hY_p hproj unfolding top1_is_projective_scheme_def by (by100 simp)
      show ?thesis
      proof (cases "m \<ge> 2")
        case True
        hence "top1_is_m_fold_projective_on Y TY m"
          unfolding top1_is_m_fold_projective_on_def
          using \<open>top1_quotient_of_scheme_on Y TY (top1_m_projective_scheme m)\<close> by (by100 simp)
        thus ?thesis using hm hXY_p by (by100 blast)
      next
        case False hence hm1: "m = 1" using hm by (by100 linarith)
        have hlen2: "length (top1_m_projective_scheme 1) = 2"
          unfolding top1_m_projective_scheme_def by (by100 simp)
        from \<open>top1_quotient_of_scheme_on Y TY (top1_m_projective_scheme m)\<close>
        have hqs1: "top1_quotient_of_scheme_on Y TY (top1_m_projective_scheme 1)"
          using hm1 by (by100 simp)
        from hqs1 obtain P0 q0 where "top1_is_polygonal_region_on P0 (length (top1_m_projective_scheme 1))"
          by (rule quotient_of_scheme_extract)
        hence "top1_is_polygonal_region_on P0 2" using hlen2 by simp
        hence "2 \<ge> (3::nat)" unfolding top1_is_polygonal_region_on_def by (by100 blast)
        hence False by simp
        thus ?thesis by simp
      qed
    qed
  qed
qed


end
















 





































 

































