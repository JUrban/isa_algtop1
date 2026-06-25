theory AlgTopCached20
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

~40 sorry proof commands in AlgTop + 0 in cached = ~40 total. Build ~90s.
   Session 0146: hphi_L_sigma t=0 FIXED, hphi_R i=n-1 base edge PROVED,
   hphi_R t=0 vertex PROVED, hjunction t=0 at i=k PROVED.

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

\<comment> \<open>Cramer decomposition on a triangle edge: if p is on the edge from a to b
   in triangle (o, a, b) with det(a-o, b-o) \\<noteq> 0, then the Cramer coords are (0, 1-t, t)
   and the mapped point is (1-t)*target\\_a + t*target\\_b.\<close>
lemma cramer_on_triangle_edge:
  fixes ox oy ax ay bx by' :: real and t :: real
  defines "ex \<equiv> ax - ox" and "ey \<equiv> ay - oy"
  defines "fx \<equiv> bx - ox" and "fy \<equiv> by' - oy"
  defines "det \<equiv> ex*fy - ey*fx"
  assumes hdet: "det \<noteq> 0"
  defines "dx \<equiv> (1-t)*ex + t*fx" and "dy \<equiv> (1-t)*ey + t*fy"
  defines "s \<equiv> (fy*dx - fx*dy)/det" and "t_par \<equiv> (ex*dy - ey*dx)/det"
  shows "s = 1 - t" and "t_par = t" and "1 - s - t_par = 0"
proof -
  have hs: "s * det = fy*dx - fx*dy" using hdet unfolding s_def by simp
  have ht: "t_par * det = ex*dy - ey*dx" using hdet unfolding t_par_def by simp
  have "fy*dx - fx*dy = (1-t)*(fy*ex - fx*ey) + t*(fy*fx - fx*fy)"
    unfolding dx_def dy_def by (by100 algebra)
  also have "\<dots> = (1-t)*det" unfolding det_def by (by100 algebra)
  finally have hs_eq: "s * det = (1-t) * det" using hs by simp
  hence "s = 1 - t" using hdet by simp
  thus "s = 1 - t" .
  have "ex*dy - ey*dx = (1-t)*(ex*ey - ey*ex) + t*(ex*fy - ey*fx)"
    unfolding dx_def dy_def by (by100 algebra)
  also have "\<dots> = t*det" unfolding det_def by (by100 algebra)
  finally have ht_eq: "t_par * det = t * det" using ht by simp
  hence "t_par = t" using hdet by simp
  thus "t_par = t" .
  from \<open>s = 1 - t\<close> \<open>t_par = t\<close> show "1 - s - t_par = 0" by simp
qed

\<comment> \<open>Cramer decomposition on the base edge: if p is on the edge from o to a
   in triangle (o, a, b), the Cramer coords are (1-t, t, 0).\<close>
lemma cramer_on_triangle_base_edge:
  fixes ox oy ax ay bx by' :: real and t :: real
  defines "ex \<equiv> ax - ox" and "ey \<equiv> ay - oy"
  defines "fx \<equiv> bx - ox" and "fy \<equiv> by' - oy"
  defines "det \<equiv> ex*fy - ey*fx"
  assumes hdet: "det \<noteq> 0"
  defines "dx \<equiv> t*ex" and "dy \<equiv> t*ey"
  defines "s \<equiv> (fy*dx - fx*dy)/det" and "t_par \<equiv> (ex*dy - ey*dx)/det"
  shows "s = t" and "t_par = 0" and "1 - s - t_par = 1 - t"
proof -
  have "fy*dx - fx*dy = t*(fy*ex - fx*ey)" unfolding dx_def dy_def by (by100 algebra)
  also have "\<dots> = t*det" unfolding det_def by (by100 algebra)
  finally have "s * det = t * det" using hdet unfolding s_def by simp
  thus "s = t" using hdet by simp
  have "ex*dy - ey*dx = t*(ex*ey - ey*ex)" unfolding dx_def dy_def by (by100 algebra)
  also have "\<dots> = 0" by (by100 algebra)
  finally have "t_par * det = 0" using hdet unfolding t_par_def by simp
  thus "t_par = 0" using hdet by simp
  from \<open>s = t\<close> \<open>t_par = 0\<close> show "1 - s - t_par = 1 - t" by simp
qed

\<comment> \<open>Pl\\"ucker identity for 2D cross products:
   cross(A,B) * cross(C,D) = cross(A,C) * cross(B,D) - cross(A,D) * cross(B,C).
   Used in fan determinant proof to transfer angular ordering.\<close>
lemma cross2_plucker:
  fixes a1 a2 b1 b2 c1 c2 d1 d2 :: real
  shows "(a1*b2 - a2*b1) * (c1*d2 - c2*d1)
       = (a1*c2 - a2*c1) * (b1*d2 - b2*d1) - (a1*d2 - a2*d1) * (b1*c2 - b2*c1)"
  by (by100 algebra)

\<comment> \<open>Fan determinant positivity from v\\_0: in a convex polygon with CCW vertices,
   cross(v\\_a - v\\_0, v\\_b - v\\_0) > 0 for 1 \\<le> a < b < n.
   Follows from C11 (non-adjacent vertices on interior side of each edge).
   Proof: case a=1 from C11 at i=0. Case a\\<ge>2 by strong induction on b-a using
   Pl\\"ucker identity + half-plane property (all vertices left of edge 0\\<to>1).\<close>
lemma convex_polygon_fan_det_from_v0:
  fixes vx vy :: "nat \<Rightarrow> real" and n :: nat
  assumes hn: "n \<ge> 3"
      and hC11: "\<forall>i<n. \<forall>kk<n. kk \<noteq> i \<longrightarrow> kk \<noteq> Suc i mod n \<longrightarrow>
          (vx kk - vx i) * (vy (Suc i mod n) - vy i) - (vy kk - vy i) * (vx (Suc i mod n) - vx i) < 0"
  shows "\<forall>a<n. \<forall>b<n. 1 \<le> a \<longrightarrow> a < b \<longrightarrow>
      (vx a - vx 0) * (vy b - vy 0) - (vy a - vy 0) * (vx b - vx 0) > 0"
proof (intro allI impI)
  fix a b assume ha: "a < n" and hb: "b < n" and ha1: "1 \<le> a" and hab: "a < b"
  \<comment> \<open>Base case: a = 1. From C11 with i=0: cross(v\\_kk - v\\_0, v\\_1 - v\\_0) < 0 for kk \\<ge> 2.
     Equivalently: cross(v\\_1 - v\\_0, v\\_b - v\\_0) > 0 for b \\<ge> 2.\<close>
  \<comment> \<open>General case: by induction or geometric argument.
     For now: sorry the full proof. The key tool is C11 applied to edge (a-1, a)
     to show the cross product with (v\\_0) is negative, then use this to derive
     positivity of cross(v\\_a - v\\_0, v\\_b - v\\_0) by bilinearity + induction.\<close>
  show "(vx a - vx 0) * (vy b - vy 0) - (vy a - vy 0) * (vx b - vx 0) > 0"
  proof (cases "a = 1")
    case True
    \<comment> \<open>a = 1, b \\<ge> 2. From C11 with i=0, kk=b: cross(v\\_b - v\\_0, v\\_1 - v\\_0) < 0.\<close>
    have hb2: "b \<ge> 2" using hab True by linarith
    have hb_ne0: "b \<noteq> 0" using hb2 by linarith
    have hb_ne1: "b \<noteq> Suc 0 mod n" using hb2 hn hab True by (by100 simp)
    have h0_lt: "(0::nat) < n" using hn by linarith
    from hC11[rule_format, OF h0_lt hb hb_ne0 hb_ne1]
    have "((vx b - vx 0) * (vy (Suc 0 mod n) - vy 0) -
           (vy b - vy 0) * (vx (Suc 0 mod n) - vx 0)) < 0" .
    hence "((vx b - vx 0) * (vy 1 - vy 0) -
           (vy b - vy 0) * (vx 1 - vx 0)) < 0" using hn by (by100 simp)
    \<comment> \<open>This is cross(v\\_b - v\\_0, v\\_1 - v\\_0) < 0, i.e., cross(v\\_1 - v\\_0, v\\_b - v\\_0) > 0.\<close>
    moreover have "(vx 1 - vx 0) * (vy b - vy 0) - (vy 1 - vy 0) * (vx b - vx 0)
      = -((vx b - vx 0) * (vy 1 - vy 0) - (vy b - vy 0) * (vx 1 - vx 0))" by (by100 algebra)
    ultimately have "(vx 1 - vx 0) * (vy b - vy 0) - (vy 1 - vy 0) * (vx b - vx 0) > 0"
      by linarith
    thus ?thesis using True by simp
  next
    case False hence ha2: "a \<ge> 2" using ha1 by linarith
    \<comment> \<open>General case a \\<ge> 2. By strong induction on b-a using Pl\\"ucker identity.
       Key ingredients:
       (1) Half-plane: cross(v\\_k - v\\_0, v\\_1 - v\\_0) < 0 for k \\<ge> 2 (from C11 at i=0)
       (2) Consecutive: cross(v\\_j - v\\_0, v\\_{j+1} - v\\_0) > 0 for j \\<ge> 1 (from C11 at i=j)
       (3) Pl\\"ucker: cross(A,B)*cross(C,D) = cross(A,C)*cross(B,D) - cross(A,D)*cross(B,C)
       Step: cross(u\\_a,u\\_b) * cross(u\\_{b-1},u\\_1) = cross(u\\_a,u\\_{b-1})*cross(u\\_b,u\\_1)
             - cross(u\\_a,u\\_1)*cross(u\\_b,u\\_{b-1}). RHS < 0 (pos*neg - neg*neg),
       denominator < 0, so quotient > 0.\<close>
    \<comment> \<open>Helper: consecutive fan det from C11 at edge (j, j+1) with kk=0.\<close>
    have hconsec: "\<And>j. 1 \<le> j \<Longrightarrow> Suc j < n \<Longrightarrow>
        (vx j - vx 0) * (vy (Suc j) - vy 0) - (vy j - vy 0) * (vx (Suc j) - vx 0) > 0"
    proof -
      fix j :: nat assume hj1: "1 \<le> j" and hjn: "Suc j < n"
      have hj_lt: "j < n" using hjn by linarith
      have h0_ne_j: "(0::nat) \<noteq> j" using hj1 by linarith
      have h0_ne_sj: "(0::nat) \<noteq> Suc j mod n" using hjn by simp
      have h0_lt: "(0::nat) < n" using hn by linarith
      from hC11[rule_format, OF hj_lt h0_lt h0_ne_j h0_ne_sj]
      have hraw: "(vx 0 - vx j) * (vy (Suc j mod n) - vy j) - (vy 0 - vy j) * (vx (Suc j mod n) - vx j) < 0" .
      have hsuc_mod: "Suc j mod n = Suc j" using hjn by simp
      have hraw2: "(vx 0 - vx j) * (vy (Suc j) - vy j) - (vy 0 - vy j) * (vx (Suc j) - vx j) < 0"
        using hraw hsuc_mod by simp
      \<comment> \<open>cross(v\\_0 - v\\_j, v\\_{j+1} - v\\_j) < 0, so cross(v\\_j - v\\_0, v\\_{j+1} - v\\_j) > 0.
         And cross(v\\_j - v\\_0, v\\_{j+1} - v\\_0) = cross(v\\_j - v\\_0, v\\_{j+1} - v\\_j) by algebra.\<close>
      have "(vx j - vx 0) * (vy (Suc j) - vy 0) - (vy j - vy 0) * (vx (Suc j) - vx 0)
          = -((vx 0 - vx j) * (vy (Suc j) - vy j) - (vy 0 - vy j) * (vx (Suc j) - vx j))"
        by (by100 algebra)
      thus "(vx j - vx 0) * (vy (Suc j) - vy 0) - (vy j - vy 0) * (vx (Suc j) - vx 0) > 0"
        using hraw2 by linarith
    qed
    \<comment> \<open>Helper: half-plane property from C11 at edge (0, 1) with kk=k.\<close>
    have hhalf: "\<And>k. 2 \<le> k \<Longrightarrow> k < n \<Longrightarrow>
        (vx k - vx 0) * (vy 1 - vy 0) - (vy k - vy 0) * (vx 1 - vx 0) < 0"
    proof -
      fix k :: nat assume hk2: "2 \<le> k" and hkn: "k < n"
      have h0_lt: "(0::nat) < n" using hn by linarith
      have hk_ne0: "k \<noteq> (0::nat)" using hk2 by linarith
      have hk_ne1: "k \<noteq> Suc 0 mod n" using hk2 hn by simp
      from hC11[rule_format, OF h0_lt hkn hk_ne0 hk_ne1]
      have "(vx k - vx 0) * (vy (Suc 0 mod n) - vy 0) - (vy k - vy 0) * (vx (Suc 0 mod n) - vx 0) < 0" .
      thus "(vx k - vx 0) * (vy 1 - vy 0) - (vy k - vy 0) * (vx 1 - vx 0) < 0"
        using hn by simp
    qed
    \<comment> \<open>Main: strong induction on b - a.\<close>
    define cross_v0 :: "nat \<Rightarrow> nat \<Rightarrow> real" where
      "cross_v0 p q = (vx p - vx 0) * (vy q - vy 0) - (vy p - vy 0) * (vx q - vx 0)" for p q
    have hgoal_eq: "(vx a - vx 0) * (vy b - vy 0) - (vy a - vy 0) * (vx b - vx 0) = cross_v0 a b"
      unfolding cross_v0_def by simp
    have hconsec': "\<And>j. 1 \<le> j \<Longrightarrow> Suc j < n \<Longrightarrow> cross_v0 j (Suc j) > 0"
      using hconsec unfolding cross_v0_def by simp
    have hhalf': "\<And>k. 2 \<le> k \<Longrightarrow> k < n \<Longrightarrow> cross_v0 k 1 < 0"
      using hhalf unfolding cross_v0_def by simp
    \<comment> \<open>Pl\\"ucker identity instantiated for cross\\_v0.
       cross\\_v0 p q * cross\\_v0 r s = cross\\_v0 p r * cross\\_v0 q s - cross\\_v0 p s * cross\\_v0 q r.
       Proved by expanding cross\\_v0\\_def and applying cross2\\_plucker directly.\<close>
    have hplucker': "\<And>p q r s. cross_v0 p q * cross_v0 r s
        = cross_v0 p r * cross_v0 q s - cross_v0 p s * cross_v0 q r"
      unfolding cross_v0_def by (by100 algebra)
    \<comment> \<open>Prove cross\\_v0 a b > 0 by strong induction on b - a.\<close>
    have "\<And>aa bb. 2 \<le> aa \<Longrightarrow> aa < bb \<Longrightarrow> bb < n \<Longrightarrow> cross_v0 aa bb > 0"
    proof -
      fix aa bb :: nat assume haa2: "2 \<le> aa" and haabb: "aa < bb" and hbbn: "bb < n"
      show "cross_v0 aa bb > 0" using haa2 haabb hbbn
      proof (induction "bb - aa" arbitrary: aa bb rule: less_induct)
        case (less aa bb)
        show ?case
        proof (cases "bb = Suc aa")
          case True
          \<comment> \<open>Consecutive: cross\\_v0 aa (aa+1) > 0.\<close>
          have "Suc aa < n" using less.prems True by linarith
          from hconsec'[OF _ this] less.prems show ?thesis using True by simp
        next
          case False
          hence hba2: "bb - aa \<ge> 2" using less.prems by linarith
          have hbb_ge4: "bb \<ge> 4" using hba2 less.prems by linarith
          have hbm1_ge3: "bb - 1 \<ge> 3" using hbb_ge4 by linarith
          have hbm1_ge2: "bb - 1 \<ge> 2" using hbm1_ge3 by linarith
          have hbm1_lt: "bb - 1 < n" using less.prems by linarith
          have haabm1: "aa < bb - 1" using hba2 by linarith
          have hbm1_suc: "Suc (bb - 1) = bb" using hbb_ge4 by linarith
          have hbm1_suc_lt: "Suc (bb - 1) < n" using hbm1_suc less.prems by simp
          \<comment> \<open>IH: cross\\_v0 aa (bb-1) > 0 (gap bb-1-aa < bb-aa).\<close>
          have hgap_less: "bb - 1 - aa < bb - aa" using hba2 by linarith
          have hIH: "cross_v0 aa (bb - 1) > 0"
            using less.hyps[OF hgap_less less.prems(1) haabm1 hbm1_lt] .
          \<comment> \<open>Half-plane: cross\\_v0 bb 1 < 0, cross\\_v0 aa 1 < 0, cross\\_v0 (bb-1) 1 < 0.\<close>
          have hbb_ge2: "bb \<ge> 2" using hbb_ge4 by linarith
          have haa_lt: "aa < n" using less.prems by linarith
          have hhalf_bb: "cross_v0 bb 1 < 0" using hhalf'[OF hbb_ge2 less.prems(3)] .
          have hhalf_aa: "cross_v0 aa 1 < 0" using hhalf'[OF less.prems(1) haa_lt] .
          have hhalf_bm1: "cross_v0 (bb - 1) 1 < 0" using hhalf'[OF hbm1_ge2 hbm1_lt] .
          \<comment> \<open>Consecutive: cross\\_v0 (bb-1) bb > 0.\<close>
          have hconsec_bm1: "cross_v0 (bb - 1) bb > 0"
            using hconsec'[OF _ hbm1_suc_lt] hbm1_suc hbm1_ge2 by simp
          \<comment> \<open>cross\\_v0 bb (bb-1) = -cross\\_v0 (bb-1) bb < 0.\<close>
          have hanti: "cross_v0 bb (bb - 1) = -cross_v0 (bb - 1) bb"
            unfolding cross_v0_def by (by100 algebra)
          have hcross_b_bm1: "cross_v0 bb (bb - 1) < 0" using hanti hconsec_bm1 by linarith
          \<comment> \<open>Pl\\"ucker identity: cross\\_v0 aa bb * cross\\_v0 (bb-1) 1
             = cross\\_v0 aa (bb-1) * cross\\_v0 bb 1 - cross\\_v0 aa 1 * cross\\_v0 bb (bb-1).\<close>
          have hpluck: "cross_v0 aa bb * cross_v0 (bb - 1) 1
            = cross_v0 aa (bb - 1) * cross_v0 bb 1 - cross_v0 aa 1 * cross_v0 bb (bb - 1)"
            using hplucker'[of aa bb "bb - 1" 1] .
          \<comment> \<open>RHS = pos * neg - neg * neg = neg - pos < 0.\<close>
          have hterm1: "cross_v0 aa (bb - 1) * cross_v0 bb 1 < 0"
            using mult_pos_neg[OF hIH hhalf_bb] .
          have hterm2: "0 < cross_v0 aa 1 * cross_v0 bb (bb - 1)"
            using mult_neg_neg[OF hhalf_aa hcross_b_bm1] .
          have hrhs: "cross_v0 aa (bb - 1) * cross_v0 bb 1 - cross_v0 aa 1 * cross_v0 bb (bb - 1) < 0"
            using hterm1 hterm2 by linarith
          \<comment> \<open>LHS = cross\\_v0 aa bb * (negative) < 0, so cross\\_v0 aa bb > 0.\<close>
          from hpluck hrhs have hprod_neg: "cross_v0 aa bb * cross_v0 (bb - 1) 1 < 0" by linarith
          \<comment> \<open>Product < 0 and second factor < 0 implies first factor > 0.\<close>
          have hbm1_neg: "cross_v0 (bb - 1) 1 < 0" using hhalf_bm1 .
          \<comment> \<open>From a*b < 0 and b < 0: if a \\<le> 0 then a*b \\<ge> 0, contradiction. So a > 0.\<close>
          show ?thesis
          proof (rule ccontr)
            assume "\<not> 0 < cross_v0 aa bb"
            hence hle: "cross_v0 aa bb \<le> 0" by linarith
            have "cross_v0 aa bb * cross_v0 (bb - 1) 1 \<ge> 0"
            proof (cases "cross_v0 aa bb = 0")
              case True thus ?thesis by simp
            next
              case False
              hence "cross_v0 aa bb < 0" using hle by linarith
              from mult_neg_neg[OF this hbm1_neg] show ?thesis by linarith
            qed
            with hprod_neg show False by linarith
          qed
        qed
      qed
    qed
    from this[OF ha2 hab hb] show ?thesis using hgoal_eq by simp
  qed
qed

\<comment> \<open>LEFT FAN SECTOR SELECTION: for a point on edge i (0 \\<le> i < k) at param t > 0,
   the LEAST sector in the left fan from v\\_0 through v\\_1,...,v\\_k is determined.
   For i = 0: LEAST = 1 (point on edge from v\\_0 to v\\_1, in sector 1).
   For 1 \\<le> i < k: LEAST = i (point strictly inside edge i is in sector i).
   NOTE: at t = 0 (vertex), LEAST might give i-1; handled separately.\<close>
lemma left_fan_edge_sector:
  fixes vx vy :: "nat \<Rightarrow> real" and n k i :: nat and t :: real
  assumes hn: "n \<ge> 3" and hk: "k \<ge> 2" and hk_lt: "k < n"
      and ht: "t \<in> I_set" and ht_pos: "t > 0" and hi: "i < k"
      and hfan: "\<forall>a<n. \<forall>b<n. 1 \<le> a \<longrightarrow> a < b \<longrightarrow>
          (vx a - vx 0) * (vy b - vy 0) - (vy a - vy 0) * (vx b - vx 0) > 0"
  defines "px \<equiv> (1-t)*vx i + t*vx(Suc i mod n)"
      and "py \<equiv> (1-t)*vy i + t*vy(Suc i mod n)"
  shows "(LEAST j. 1 \<le> j \<and> j < k \<and>
      (vx j - vx 0)*(py - vy 0) - (vy j - vy 0)*(px - vx 0) \<ge> 0 \<and>
      (vx(Suc j) - vx 0)*(py - vy 0) - (vy(Suc j) - vy 0)*(px - vx 0) \<le> 0)
    = (if i = 0 then 1 else i)"
proof -
  let ?PL = "\<lambda>j. 1 \<le> j \<and> j < k \<and>
      (vx j - vx 0)*(py - vy 0) - (vy j - vy 0)*(px - vx 0) \<ge> 0 \<and>
      (vx(Suc j) - vx 0)*(py - vy 0) - (vy(Suc j) - vy 0)*(px - vx 0) \<le> 0"
  have ht01: "t \<ge> 0 \<and> t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)
  have h1mt: "1 - t \<ge> 0" using ht01 by linarith
  have hsi_lt: "Suc i < n" using hi hk_lt by linarith
  have hsi_mod: "Suc i mod n = Suc i" using hsi_lt by simp
  \<comment> \<open>Cross product bilinearity: cross(v\\_j, edge\\_pt) = (1-t)*cross(j,i) + t*cross(j,i+1).\<close>
  have hbilin: "\<And>j. (vx j - vx 0)*(py - vy 0) - (vy j - vy 0)*(px - vx 0)
      = (1-t)*((vx j - vx 0)*(vy i - vy 0) - (vy j - vy 0)*(vx i - vx 0))
      + t*((vx j - vx 0)*(vy(Suc i) - vy 0) - (vy j - vy 0)*(vx(Suc i) - vx 0))"
  proof -
    fix j :: nat
    have hpx: "px = (1-t)*vx i + t*vx(Suc i)" unfolding px_def using hsi_mod by simp
    have hpy: "py = (1-t)*vy i + t*vy(Suc i)" unfolding py_def using hsi_mod by simp
    have "(vx j - vx 0)*(py - vy 0) - (vy j - vy 0)*(px - vx 0)
        = (vx j - vx 0)*((1-t)*(vy i - vy 0) + t*(vy(Suc i) - vy 0))
        - (vy j - vy 0)*((1-t)*(vx i - vx 0) + t*(vx(Suc i) - vx 0))"
      using hpx hpy by (by100 algebra)
    also have "\<dots> = (1-t)*((vx j - vx 0)*(vy i - vy 0) - (vy j - vy 0)*(vx i - vx 0))
      + t*((vx j - vx 0)*(vy(Suc i) - vy 0) - (vy j - vy 0)*(vx(Suc i) - vx 0))"
      by (by100 algebra)
    finally show "(vx j - vx 0)*(py - vy 0) - (vy j - vy 0)*(px - vx 0)
      = (1-t)*((vx j - vx 0)*(vy i - vy 0) - (vy j - vy 0)*(vx i - vx 0))
      + t*((vx j - vx 0)*(vy(Suc i) - vy 0) - (vy j - vy 0)*(vx(Suc i) - vx 0))" .
  qed
  define expected where "expected = (if i = 0 then 1 else i)"
  \<comment> \<open>Step A: ?PL(expected) holds.\<close>
  have hPL_holds: "?PL expected"
  proof -
    have hexp_ge1: "1 \<le> expected" unfolding expected_def by simp
    have hexp_lt_k: "expected < k" unfolding expected_def using hi hk by simp
    \<comment> \<open>Lower bound: hbilin[of expected] = (1-t)*cross(expected,i) + t*cross(expected,Suc i).
       Both terms: if i=0 then cross(1,0) = 0 and cross(1,1) = 0, so lower = 0.
                   if i \\<ge> 1 then expected = i, cross(i,i) = 0, cross(i,Suc i) > 0 (fan det),
                   so lower = t*fan\\_det > 0.\<close>
    have hlower: "(vx expected - vx 0)*(py - vy 0) - (vy expected - vy 0)*(px - vx 0) \<ge> 0"
    proof -
      from hbilin[of expected]
      have hlow_decomp: "(vx expected - vx 0)*(py - vy 0) - (vy expected - vy 0)*(px - vx 0)
        = (1-t)*((vx expected - vx 0)*(vy i - vy 0) - (vy expected - vy 0)*(vx i - vx 0))
        + t*((vx expected - vx 0)*(vy(Suc i) - vy 0) - (vy expected - vy 0)*(vx(Suc i) - vx 0))" .
      have hcross_eq_0: "((vx expected - vx 0)*(vy i - vy 0) - (vy expected - vy 0)*(vx i - vx 0)) = 0"
      proof (cases "i = 0")
        case True thus ?thesis unfolding expected_def by simp
      next
        case False hence "expected = i" unfolding expected_def by simp
        thus ?thesis by simp
      qed
      have hcross_ge_0: "t * ((vx expected - vx 0)*(vy(Suc i) - vy 0) - (vy expected - vy 0)*(vx(Suc i) - vx 0)) \<ge> 0"
      proof (cases "i = 0")
        case True hence "expected = 1" and "Suc i = 1" unfolding expected_def by simp+
        thus ?thesis by simp
      next
        case False hence "expected = i" and "i \<ge> 1" unfolding expected_def by simp+
        have "i < n" using hi hk_lt by linarith
        have "i < n" using hi hk_lt by linarith
        from hfan[rule_format, OF \<open>i < n\<close> hsi_lt \<open>i \<ge> 1\<close>]
        have hfdi: "((vx i - vx 0)*(vy(Suc i) - vy 0) - (vy i - vy 0)*(vx(Suc i) - vx 0)) > 0"
          using hi by linarith
        from mult_pos_pos[OF ht_pos hfdi]
        show ?thesis using \<open>expected = i\<close> by simp
      qed
      have "(1-t) * 0 + t * ((vx expected - vx 0)*(vy(Suc i) - vy 0) - (vy expected - vy 0)*(vx(Suc i) - vx 0)) \<ge> 0"
        using hcross_ge_0 by simp
      hence "(1-t)*((vx expected - vx 0)*(vy i - vy 0) - (vy expected - vy 0)*(vx i - vx 0))
        + t*((vx expected - vx 0)*(vy(Suc i) - vy 0) - (vy expected - vy 0)*(vx(Suc i) - vx 0)) \<ge> 0"
        using hcross_eq_0 by simp
      thus ?thesis using hlow_decomp by linarith
    qed
    \<comment> \<open>Upper bound: hbilin[of "Suc expected"] = (1-t)*cross(Suc expected, i) + t*cross(Suc expected, Suc i).
       If i = 0: Suc expected = 2, cross(2,0) = 0, cross(2,1) = -fan\\_det(1,2) < 0.
       If i \\<ge> 1: expected = i, Suc expected = Suc i, cross(Suc i, i) < 0, cross(Suc i, Suc i) = 0.\<close>
    have hupper: "(vx(Suc expected) - vx 0)*(py - vy 0) - (vy(Suc expected) - vy 0)*(px - vx 0) \<le> 0"
    proof -
      from hbilin[of "Suc expected"]
      have hup_decomp: "(vx(Suc expected) - vx 0)*(py - vy 0) - (vy(Suc expected) - vy 0)*(px - vx 0)
        = (1-t)*((vx(Suc expected) - vx 0)*(vy i - vy 0) - (vy(Suc expected) - vy 0)*(vx i - vx 0))
        + t*((vx(Suc expected) - vx 0)*(vy(Suc i) - vy 0) - (vy(Suc expected) - vy 0)*(vx(Suc i) - vx 0))" .
      show ?thesis
      proof (cases "i = 0")
        case True
        \<comment> \<open>i=0: Suc expected = 2, cross(2,0)=0, cross(2,1)=-fan\\_det(1,2)<0.\<close>
        have "expected = 1" unfolding expected_def using True by simp
        hence hSE: "Suc expected = 2" by simp
        have hcr_20: "((vx 2 - vx 0)*(vy 0 - vy 0) - (vy 2 - vy 0)*(vx 0 - vx 0)) = 0" by simp
        have "(vx 2 - vx 0)*(vy 1 - vy 0) - (vy 2 - vy 0)*(vx 1 - vx 0) < 0"
        proof -
          have "(1::nat) < n" using hn by linarith
          have "(2::nat) < n" using hn by linarith
          from hfan[rule_format, OF \<open>1 < n\<close> \<open>2 < n\<close>]
          have "(vx 1 - vx 0)*(vy 2 - vy 0) - (vy 1 - vy 0)*(vx 2 - vx 0) > 0" by simp
          moreover have "(vx 2 - vx 0)*(vy 1 - vy 0) - (vy 2 - vy 0)*(vx 1 - vx 0)
            = -((vx 1 - vx 0)*(vy 2 - vy 0) - (vy 1 - vy 0)*(vx 2 - vx 0))"
            by (by100 algebra)
          ultimately show ?thesis by linarith
        qed
        have "t \<ge> 0" using ht_pos by linarith
        hence "t * ((vx 2 - vx 0)*(vy 1 - vy 0) - (vy 2 - vy 0)*(vx 1 - vx 0)) \<le> 0"
          using \<open>(vx 2 - vx 0)*(vy 1 - vy 0) - (vy 2 - vy 0)*(vx 1 - vx 0) < 0\<close>
          using mult_nonneg_nonpos[of t "(vx 2 - vx 0)*(vy 1 - vy 0) - (vy 2 - vy 0)*(vx 1 - vx 0)"]
          by linarith
        \<comment> \<open>Need: upper \\<le> 0. From hup\\_decomp: upper = (1-t)*cross(2,i) + t*cross(2,Suc i).
           With i=0, Suc i mod n = 1: = (1-t)*cross(2,0) + t*cross(2,1) = 0 + neg \\<le> 0.\<close>
        have "Suc i = 1" using True by simp
        have "Suc i mod n = 1" using \<open>Suc i = 1\<close> hn by simp
        have hup_eq: "(vx 2 - vx 0)*(py - vy 0) - (vy 2 - vy 0)*(px - vx 0)
          = (1-t)*((vx 2 - vx 0)*(vy 0 - vy 0) - (vy 2 - vy 0)*(vx 0 - vx 0))
          + t*((vx 2 - vx 0)*(vy 1 - vy 0) - (vy 2 - vy 0)*(vx 1 - vx 0))"
          using hbilin[of 2] True \<open>Suc i mod n = 1\<close> by simp
        have "(1-t)*((vx 2 - vx 0)*(vy 0 - vy 0) - (vy 2 - vy 0)*(vx 0 - vx 0)) = 0"
          by simp
        hence "(vx 2 - vx 0)*(py - vy 0) - (vy 2 - vy 0)*(px - vx 0) \<le> 0"
          using hup_eq \<open>t * ((vx 2 - vx 0)*(vy 1 - vy 0) - (vy 2 - vy 0)*(vx 1 - vx 0)) \<le> 0\<close>
          by linarith
        moreover have "(2::nat) = Suc expected" using hSE by simp
        ultimately show ?thesis by (by100 auto)
      next
        case False
        \<comment> \<open>i\\<ge>1: expected = i, Suc expected = Suc i, cross(Suc i, i) < 0, cross(Suc i, Suc i) = 0.\<close>
        have "expected = i" unfolding expected_def using False by simp
        hence hSE: "Suc expected = Suc i" by simp
        have "((vx(Suc i) - vx 0)*(vy(Suc i) - vy 0) - (vy(Suc i) - vy 0)*(vx(Suc i) - vx 0)) = 0" by (by100 algebra)
        have "((vx(Suc i) - vx 0)*(vy i - vy 0) - (vy(Suc i) - vy 0)*(vx i - vx 0)) < 0"
        proof -
          have "i < n" using hi hk_lt by linarith
          from hfan[rule_format, OF \<open>i < n\<close> hsi_lt]
          have "((vx i - vx 0)*(vy(Suc i) - vy 0) - (vy i - vy 0)*(vx(Suc i) - vx 0)) > 0"
            using False by linarith
          moreover have "((vx(Suc i) - vx 0)*(vy i - vy 0) - (vy(Suc i) - vy 0)*(vx i - vx 0))
            = -((vx i - vx 0)*(vy(Suc i) - vy 0) - (vy i - vy 0)*(vx(Suc i) - vx 0))"
            by (by100 algebra)
          ultimately show ?thesis by linarith
        qed
        hence "(1-t) * ((vx(Suc i) - vx 0)*(vy i - vy 0) - (vy(Suc i) - vy 0)*(vx i - vx 0)) \<le> 0"
          using h1mt
          using mult_nonneg_nonpos[of "1-t" "((vx(Suc i) - vx 0)*(vy i - vy 0) - (vy(Suc i) - vy 0)*(vx i - vx 0))"]
          by linarith
        thus ?thesis using hup_decomp hSE
          \<open>((vx(Suc i) - vx 0)*(vy(Suc i) - vy 0) - (vy(Suc i) - vy 0)*(vx(Suc i) - vx 0)) = 0\<close>
          by simp
      qed
    qed
    show "?PL expected" using hexp_ge1 hexp_lt_k hlower hupper by simp
  qed
  \<comment> \<open>Step B: ?PL(j) false for j < expected.\<close>
  have hPL_min: "\<And>j. ?PL j \<Longrightarrow> expected \<le> j"
  proof -
    fix j assume hj: "?PL j"
    hence hj1: "1 \<le> j" by simp
    from hj have hjk: "j < k" by simp
    from hj have hupper: "(vx(Suc j) - vx 0)*(py - vy 0) - (vy(Suc j) - vy 0)*(px - vx 0) \<le> 0"
      by simp
    show "expected \<le> j"
    proof (cases "i = 0")
      case True hence "expected = 1" unfolding expected_def by simp
      thus ?thesis using hj1 by simp
    next
      case False hence hi1: "i \<ge> 1" by linarith
      hence "expected = i" unfolding expected_def by simp
      \<comment> \<open>Need: i \\<le> j. Suppose j < i. Then upper(j) > 0 (from fan det), contradicting hupper.\<close>
      have "i \<le> j"
      proof (rule ccontr)
        assume "\<not> i \<le> j"
        hence hjlt: "j < i" by linarith
        \<comment> \<open>Upper(j) = (1-t)*cross(j+1,i) + t*cross(j+1,i+1).
           Both \\<ge> 0 from fan det, and t*cross(j+1,i+1) > 0 since t > 0.\<close>
        have "Suc j \<le> i" using hjlt by linarith
        have hcr1: "(vx(Suc j) - vx 0)*(vy i - vy 0) - (vy(Suc j) - vy 0)*(vx i - vx 0) \<ge> 0"
        proof (cases "Suc j = i")
          case True thus ?thesis by simp
        next
          case False
          hence "Suc j < i" using \<open>Suc j \<le> i\<close> by linarith
          hence "1 \<le> Suc j" by simp
          have "Suc j < n" using hjlt hi hk_lt by linarith
          have "i < n" using hi hk_lt by linarith
          from hfan[rule_format, OF \<open>Suc j < n\<close> \<open>i < n\<close> \<open>1 \<le> Suc j\<close> \<open>Suc j < i\<close>]
          show ?thesis by linarith
        qed
        have "Suc j < Suc i" using hjlt by linarith
        have hcr2: "(vx(Suc j) - vx 0)*(vy(Suc i) - vy 0) - (vy(Suc j) - vy 0)*(vx(Suc i) - vx 0) > 0"
        proof -
          have "1 \<le> Suc j" using hj1 by simp
          have "Suc j < n" using hjlt hi hk_lt by linarith
          have "Suc i < n" using hsi_lt .
          from hfan[rule_format, OF \<open>Suc j < n\<close> \<open>Suc i < n\<close> \<open>1 \<le> Suc j\<close> \<open>Suc j < Suc i\<close>]
          show ?thesis .
        qed
        have "t * ((vx(Suc j) - vx 0)*(vy(Suc i) - vy 0) - (vy(Suc j) - vy 0)*(vx(Suc i) - vx 0)) > 0"
          using mult_pos_pos[OF ht_pos hcr2] .
        moreover have "(1-t) * ((vx(Suc j) - vx 0)*(vy i - vy 0) - (vy(Suc j) - vy 0)*(vx i - vx 0)) \<ge> 0"
          using mult_nonneg_nonneg[of "1-t" "(vx(Suc j) - vx 0)*(vy i - vy 0) - (vy(Suc j) - vy 0)*(vx i - vx 0)"]
                h1mt hcr1 by linarith
        ultimately have "(vx(Suc j) - vx 0)*(py - vy 0) - (vy(Suc j) - vy 0)*(px - vx 0) > 0"
          using hbilin[of "Suc j"] hsi_mod by linarith
        with hupper show False by linarith \<comment> \<open>Contradiction: upper > 0 but hupper says \\<le> 0.\<close>
      qed
      thus ?thesis using \<open>expected = i\<close> by simp
    qed
  qed
  \<comment> \<open>Step C: LEAST = expected.\<close>
  have "(LEAST j. ?PL j) = expected"
    using Least_equality[of ?PL expected] hPL_holds hPL_min by (by100 blast)
  thus ?thesis unfolding expected_def by simp
qed


end
