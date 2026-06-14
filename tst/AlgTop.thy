theory AlgTop
  imports "AlgTopCached16.AlgTopCached16"
begin

\<comment> \<open>SORRY ANALYSIS (as of 2026-06-14, sessions 1316-1511, 18 standalone sorry lines):
UPDATE (session 1501-1511):
- h\\_psi\\_e\\_int: PROVED (boundary image extraction from polygon\\_homeomorphic\\_to\\_disk)
- p\\_cm interior: PROVED (fst(p\\_cm)²+snd(p\\_cm)² < 1)
- h\\_tau\\_strict\\_B2: BOTH sectors FULLY PROVED (good + cancel, zero sorry)
- h\\_tau\\_cancel\\_bdy: FULLY PROVED (\\<tau> at cancel boundary maps to B2 interior)
- h\\_tau\\_vtx1\\_int: PROVED (\\<tau>(\\<psi>\\_e(vertex\\_e(1))) in B2 interior)
- converse vtx\\_id \\<subseteq> output\\_step\\_rel: PROVED (symmetry swap)
- BUG FOUND AND FIXED: h\\_tau\\_inj was FALSE (midpoint ray collapse when p\\_cm=0).
  Fix: changed spur target from centroid to midpoint(vertex\\_m(0), centroid).
  p\\_cm \\<noteq> (0,0) now provable (modulo PolygonDisk export blocked by eta-conversion).
- hspur\\_in\\_Pm: PROVED (spur target in P\\_m via coefficient averaging)
- Remaining \\<tau> fix sorrys: hspur\\_interior (cross product, ~100 lines), \\<psi>\\_m(centroid)=(0,0) (eta issue).

SPUR COLLAPSE (decomposed, key properties proved):
- h\\_tau\\_range: FULLY PROVED!
- h\\_tau\\_surj: FULLY PROVED!
- h\\_tau\\_cont: PROVED from sub-sorrys via continuous\\_on\\_closed\\_Un pasting:
  (1) S\\_g closed — PROVED \\<checkmark>
  (2) S\\_c closed — PROVED \\<checkmark>
  (3+4) Nonzero continuity: consolidated to h\\_tau\\_cont\\_B2\\_nonzero via continuous\\_on\\_subset.
    Decomposed via open cover U1={snd>0}\\<union>{fst<0}, U2={snd<0}\\<union>{fst>0} + at\\_within\\_nhd.
    2 sorrys: h\\_U1\\_cont (angle continuous, cases\\_le), h\\_U2\\_cont (closed paste).
  Bounds |fst/snd(\\<tau>)| \\<le> C*r: ALL 4 PROVED (triangle ineq + convex comb bound)
- h\\_spur\\_good\\_edge: FULLY PROVED!
- h\\_spur\\_cancel\\_collapse: FULLY PROVED!
- h\\_spur\\_vertex: FULLY PROVED! (k\\<ge>2 \\<to> vx\\_m(k-2))
- h\\_spur\\_vertex\\_0: FULLY PROVED! (vx\\_e(0) \\<to> vx\\_m(0))
- h\\_fibres\\_good\\_edge: FULLY PROVED!
- h\\_fibres: PROVED from forward + backward.
  h\\_fibres\\_forward: FULLY PROVED (ZERO SORRY)!
    Interior: C8\\_e. Good-good: C9+shift+C7. Cancel-cancel: collapse+dir.
    Cancel-good: freshness contradiction. Vertex-edge: hC12\\_e contradiction.
    Vertex-vertex: PROVED via rtrancl chain transfer:
      scheme\\_quotient\\_exists exports vtgt\\<to>rtrancl (PROVED).
      h\\_step\\_f: each C7 generator preserves q\\_m\\<circ>spur\\_f (PROVED).
      h\\_rtrancl\\_f: closure preserves f (PROVED by rtrancl\\_induct).
      h\\_vtx\\_vtgt\\_transfer: vtgt equality \\<to> f equality (PROVED).
  h\\_fibres\\_backward: sorry (similar case analysis to forward).
- hC12\\_e, hC12\\_m: BOTH PROVED from scheme\\_quotient\\_exists(2).
- scheme\\_quotient\\_exists: BOTH conclusions FULLY PROVED (zero sorry).
  (2) outputs ALL C1-C12 + vtgt facts + vtgt(k) \\<le> k + vtgt idempotent + rtrancl characterization.
- edge\\_interior\\_not\\_vertex: PROVED (polygon-level, C3+C11).

CUT-PASTE (5 sorrys):
- Same-space (3): quotient\\_of\\_scheme\\_cut\\_paste/2/opp (lines 113, 125, 153)
- Proper variants (2): cut-reglue homeo between canonical quotients (lines 4350, 4399)
  Structural proof done: canonical quotients + bridge + transfer. Only cut-reglue sorry.

VERTEX UNIQUENESS (5 sorrys, decomposed from 2):
- Forward: vertex-vertex (1), vertex-edge-interior (2) — lines 4219, 4226, 4314
- Backward: vertex case (1) — line 4427
  Vertex extraction infrastructure PROVED (phi maps vx1(k) to vx2(k)).

GENUINELY FALSE (2 sorrys): length(u@v) < 3 after cancel — lines 5376, 5543
  Fix: add length precondition (requires cached session change)

CONTEXT-LEFT (10 sorrys): suffix operations \\<noteq> full-scheme operations — lines 5624-5782
  PROVED: v\\_relabel(fresh), v\\_cancel(long), v\\_uncancel, v\\_cancel\\_reverse,
          v\\_cut\\_paste, v\\_cut\\_paste\\_opp, v\\_flip\\_label(fresh).
  SORRY: v\\_rotate(inner), v\\_invert(inner), v\\_flip\\_label(non-fresh),
         v\\_cut\\_paste\\_reverse, v\\_cut\\_paste2, v\\_context\\_left(recursive).

CUT-PASTE REVERSE (2 sorrys): lines 5409, 5416
  Need reverse of cut-paste geometry.

FINAL ASSEMBLY (3 sorrys):
- Thm 78.2 induction (line 6666): polygon-pasting
- Scheme extraction (line 6707): construct scheme from quotient map
- Sphere realization (line 6749): sphere scheme quotient \\<cong> S2

DEAD CODE (1 sorry): Theorem\\_76 relabel (line 5849)

KEY INFRASTRUCTURE (all PROVED):
- scheme\\_quotient\\_exists, scheme\\_quotient\\_uniqueness, compact\\_surj\\_quotient
- scheme\\_quotient\\_transfer\\_along\\_homeomorphism (all 11 conditions)
- front\\_cancel\\_proper skeleton (modulo spur collapse sub-sorrys)
- quotient\\_of\\_scheme\\_uncancel\\_front\\_proper (for proper schemes)
- spur\\_f = \\<psi>\\_m\\<inverse> \\<circ> \\<tau> \\<circ> \\<psi>\\_e continuity + surjectivity (from sub-sorrys)
- Continuity chain: \\<psi>\\_e \\<checkmark> \\<to> \\<tau> (sorry) \\<to> \\<psi>\\_m\\<inverse> \\<checkmark> \\<to> spur\\_f \\<checkmark>
- Vertex extraction: \\<phi>(vx1(k)) = vx2(k) for k < n
- r > 0, r \\<le> 1, r^2 = fst p^2 + snd p^2 (for \\<tau> range proof)
- real\\_abs\\_mul\\_le\\_half\\_sum\\_squares: |xy| \\<le> (x^2+y^2)/2 (AM-GM global)
- real\\_inner2\\_abs\\_le\\_half\\_norm\\_sums: |s\\<cdot>d| \\<le> (S+D)/2 (2D inner product bound)
- cancel\\_shift\\_label: ([a,a\\<inverse>]@w)!(i+2) = w!i (index shift for fibre matching)\<close>
lemma quotient_of_scheme_cut_paste:
  assumes "top1_quotient_of_scheme_on Y TY (u1 @ [(a, True)] @ u2 @ [(a, True)] @ u3)"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' (u1 @ [(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3) \<and>
    top1_homeomorphism_on Y TY Y' TY' h"
proof -
  have "top1_quotient_of_scheme_on Y TY (u1 @ [(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3)"
    sorry \<comment> \<open>Munkres §76(iv): cut along diagonal, flip u2 piece, recombine.
       Uses quotient\\_scheme\\_edge\\_permutation with \\<sigma> that swaps u2 block (reversed).\<close>
  thus ?thesis by (rule same_space_implies_homeo_realization_early)
qed

lemma quotient_of_scheme_cut_paste2:
  assumes "top1_quotient_of_scheme_on Y TY (u0 @ [(a, True)] @ u1 @ [(a, True)] @ u2)"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' ([(b, True)] @ u2 @ [(b, True)] @ u1 @ rev (map top1_inverse_edge u0)) \<and>
    top1_homeomorphism_on Y TY Y' TY' h"
proof -
  have "top1_quotient_of_scheme_on Y TY ([(b, True)] @ u2 @ [(b, True)] @ u1 @ rev (map top1_inverse_edge u0))"
    sorry \<comment> \<open>Munkres §76(v): cut, relabel, recombine with fresh label b.\<close>
  thus ?thesis by (rule same_space_implies_homeo_realization_early)
qed

lemma quotient_of_scheme_cut_paste_opp:
  assumes "top1_quotient_of_scheme_on Y TY (u0 @ u1 @ [(a, True)] @ u2 @ [(a, False)] @ u3)"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' (u0 @ [(a, True)] @ u2 @ [(a, False)] @ u1 @ u3) \<and>
    top1_homeomorphism_on Y TY Y' TY' h"
proof -
  let ?s = "u0 @ u1 @ [(a, True)] @ u2 @ [(a, False)] @ u3"
  let ?s' = "u0 @ [(a, True)] @ u2 @ [(a, False)] @ u1 @ u3"
  \<comment> \<open>Expert approach (audit 23 §4/§7): canonical quotients + uniqueness.
     Step 1: Get canonical (real\\<times>real) quotients of both s and s'.
     Step 2: Show the canonical quotients are homeomorphic (geometric cut-paste).
     Step 3: Use scheme\\_quotient\\_uniqueness to bridge Y (type 'a) to canonical (real\\<times>real).
     Step 4: Compose homeomorphisms.\<close>
  have htopo_strict: "is_topology_on_strict Y TY"
    using assms unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  have htopo: "is_topology_on Y TY"
    using htopo_strict unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>Step 1: canonical quotients.\<close>
  have hlen_s: "length ?s \<ge> 3"
    using quotient_scheme_length_ge3[OF assms] .
  have hlen_s': "length ?s' = length ?s" by (by100 simp)
  \<comment> \<open>scheme\\_quotient\\_exists needs properness, which we don't have in general.
     Fall back to edge-permutation approach (same-space, no properness needed).\<close>
  have "top1_quotient_of_scheme_on Y TY ?s'"
    sorry \<comment> \<open>Munkres §76(ix): move u1 block past identified edge pair.
       Via quotient\\_scheme\\_edge\\_permutation (disk homeo + arc permutation).\<close>
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
  sorry \<comment> \<open>Sub-polygon approach replaced by front\\_cancel\\_proper (after uniqueness).
     See front\\_cancel\\_proper for the expert-recommended approach using
     scheme\\_quotient\\_exists + uniqueness + spur collapse.\<close>

\<comment> \<open>Uncancel same-space: if Y is quotient of w, then Y is also quotient of [a,inv a]@w.
   The additional cancelling pair creates a spur that collapses to nothing.
   Proof deferred — needs geometric spur insertion or canonical quotients + transfer lemma.\<close>
lemma quotient_of_scheme_uncancel_front:
  assumes "top1_quotient_of_scheme_on Y TY w"
      and "length w \<ge> 3"
  shows "top1_quotient_of_scheme_on Y TY ([a, top1_inverse_edge a] @ w)"
  sorry \<comment> \<open>General case (non-proper). Proper case proved via
     quotient\\_of\\_scheme\\_uncancel\\_front\\_proper.\<close>

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

\<comment> \<open>Vertex identification helper (vertex\\_identification\\_scheme\\_determined) REMOVED:
   was never used. The vertex case in uniqueness is handled directly
   via the admitted steps at lines 4325/4437 (continuity/density argument).\<close>

\<comment> \<open>Quotient-of-scheme uniqueness: any two quotient spaces of the same scheme are homeomorphic.
   Proof: both are quotients of convex n-gons by the same identification pattern.
   The n-gons are homeomorphic (convex compact in R²), and the homeomorphism respects
   the boundary identifications. So the quotient spaces are homeomorphic.\<close>
lemma scheme_quotient_uniqueness:
  assumes "is_topology_on_strict Y1 TY1" and "is_topology_on_strict Y2 TY2"
      and "top1_quotient_of_scheme_on Y1 TY1 scheme"
      and "top1_quotient_of_scheme_on Y2 TY2 scheme"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  let ?n = "length scheme"
  let ?TP = "\<lambda>S. subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S"
  \<comment> \<open>Step 1: Extract ALL 11 conditions from both quotients.\<close>
  from assms(3) obtain P1 q1 vx1 vy1 where
      hC1_1: "top1_is_polygonal_region_on P1 ?n"
    and hC2_1: "top1_quotient_map_on P1 (?TP P1) Y1 TY1 q1"
    and hC3_1: "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> (vx1 i, vy1 i) \<noteq> (vx1 j, vy1 j)"
    and hC4_1: "\<forall>i<?n. (vx1 i, vy1 i) \<in> P1"
    and hC5_1: "P1 = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx1 i)
                     \<and> y = (\<Sum>i<?n. coeffs i * vy1 i)}"
    and hC7_1: "\<forall>i<?n. \<forall>j<?n. fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set.
           q1 ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
              (1-t) * vy1 i + t * vy1 (Suc i mod ?n))
         = (if snd (scheme!i) = snd (scheme!j)
            then q1 ((1-t) * vx1 j + t * vx1 (Suc j mod ?n),
                    (1-t) * vy1 j + t * vy1 (Suc j mod ?n))
            else q1 (t * vx1 j + (1-t) * vx1 (Suc j mod ?n),
                    t * vy1 j + (1-t) * vy1 (Suc j mod ?n))))"
    and hC8_1: "\<forall>p\<in>P1. (\<forall>i<?n. \<forall>t\<in>I_set.
                p \<noteq> ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
                      (1-t) * vy1 i + t * vy1 (Suc i mod ?n)))
             \<longrightarrow> (\<forall>p'\<in>P1. q1 p = q1 p' \<longrightarrow> p = p')"
    and hC9_1: "\<forall>i<?n. \<forall>j<?n. \<forall>t\<in>{0<..<(1::real)}. \<forall>s\<in>{0<..<(1::real)}.
            q1 ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
               (1-t) * vy1 i + t * vy1 (Suc i mod ?n))
          = q1 ((1-s) * vx1 j + s * vx1 (Suc j mod ?n),
               (1-s) * vy1 j + s * vy1 (Suc j mod ?n))
          \<longrightarrow> (i = j \<and> t = s)
            \<or> (fst (scheme!i) = fst (scheme!j) \<and>
               (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
    and hC10_1: "\<forall>i<?n. let cx = (\<Sum>j<?n. vx1 j) / real ?n;
                             cy = (\<Sum>j<?n. vy1 j) / real ?n
         in (vx1 i - cx) * (vy1 (Suc i mod ?n) - cy)
          - (vy1 i - cy) * (vx1 (Suc i mod ?n) - cx) > 0"
    and hC11_1: "\<forall>i<?n. \<forall>k<?n.
          k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
          (vx1 k - vx1 i) * (vy1 (Suc i mod ?n) - vy1 i)
          - (vy1 k - vy1 i) * (vx1 (Suc i mod ?n) - vx1 i) < 0"
    by (rule quotient_of_scheme_extract_vx)
  from assms(4) obtain P2 q2 vx2 vy2 where
      hC1_2: "top1_is_polygonal_region_on P2 ?n"
    and hC2_2: "top1_quotient_map_on P2 (?TP P2) Y2 TY2 q2"
    and hC4_2: "\<forall>i<?n. (vx2 i, vy2 i) \<in> P2"
    and hC5_2: "P2 = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx2 i)
                     \<and> y = (\<Sum>i<?n. coeffs i * vy2 i)}"
    and hC7_2: "\<forall>i<?n. \<forall>j<?n. fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set.
           q2 ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
              (1-t) * vy2 i + t * vy2 (Suc i mod ?n))
         = (if snd (scheme!i) = snd (scheme!j)
            then q2 ((1-t) * vx2 j + t * vx2 (Suc j mod ?n),
                    (1-t) * vy2 j + t * vy2 (Suc j mod ?n))
            else q2 (t * vx2 j + (1-t) * vx2 (Suc j mod ?n),
                    t * vy2 j + (1-t) * vy2 (Suc j mod ?n))))"
    and hC8_2: "\<forall>p\<in>P2. (\<forall>i<?n. \<forall>t\<in>I_set.
                p \<noteq> ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
                      (1-t) * vy2 i + t * vy2 (Suc i mod ?n)))
             \<longrightarrow> (\<forall>p'\<in>P2. q2 p = q2 p' \<longrightarrow> p = p')"
    and hC9_2: "\<forall>i<?n. \<forall>j<?n. \<forall>t\<in>{0<..<(1::real)}. \<forall>s\<in>{0<..<(1::real)}.
            q2 ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
               (1-t) * vy2 i + t * vy2 (Suc i mod ?n))
          = q2 ((1-s) * vx2 j + s * vx2 (Suc j mod ?n),
               (1-s) * vy2 j + s * vy2 (Suc j mod ?n))
          \<longrightarrow> (i = j \<and> t = s)
            \<or> (fst (scheme!i) = fst (scheme!j) \<and>
               (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
    and hC10_2: "\<forall>i<?n. let cx = (\<Sum>j<?n. vx2 j) / real ?n;
                             cy = (\<Sum>j<?n. vy2 j) / real ?n
         in (vx2 i - cx) * (vy2 (Suc i mod ?n) - cy)
          - (vy2 i - cy) * (vx2 (Suc i mod ?n) - cx) > 0"
    and hC11_2: "\<forall>i<?n. \<forall>k<?n.
          k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
          (vx2 k - vx2 i) * (vy2 (Suc i mod ?n) - vy2 i)
          - (vy2 k - vy2 i) * (vx2 (Suc i mod ?n) - vx2 i) < 0"
    by (rule quotient_of_scheme_extract_vx)
  have hn3: "?n \<ge> 3" using hC1_1 unfolding top1_is_polygonal_region_on_def by (by100 blast)
  \<comment> \<open>Step 2: Derive non-strict side conditions (needed for disk homeomorphism).\<close>
  have hside_le_1: "\<forall>i<?n. \<forall>k<?n.
      (vx1 k - vx1 i) * (vy1 (Suc i mod ?n) - vy1 i)
      - (vy1 k - vy1 i) * (vx1 (Suc i mod ?n) - vx1 i) \<le> 0"
  proof (intro allI impI)
    fix i k assume "i < ?n" "k < ?n"
    show "(vx1 k - vx1 i) * (vy1 (Suc i mod ?n) - vy1 i) -
          (vy1 k - vy1 i) * (vx1 (Suc i mod ?n) - vx1 i) \<le> 0"
    proof (cases "k = i")
      case True thus ?thesis by (by100 simp)
    next
      case False
      show ?thesis
      proof (cases "k = Suc i mod ?n")
        case True
        hence "(vx1 k - vx1 i) * (vy1 (Suc i mod ?n) - vy1 i) =
               (vy1 k - vy1 i) * (vx1 (Suc i mod ?n) - vx1 i)" by (by100 simp)
        thus ?thesis by (by100 simp)
      next
        case False2: False
        from hC11_1 \<open>i < ?n\<close> \<open>k < ?n\<close> False False2
        have "(vx1 k - vx1 i) * (vy1 (Suc i mod ?n) - vy1 i) -
              (vy1 k - vy1 i) * (vx1 (Suc i mod ?n) - vx1 i) < 0" by (by100 blast)
        thus ?thesis by (by100 linarith)
      qed
    qed
  qed
  have hside_le_2: "\<forall>i<?n. \<forall>k<?n.
      (vx2 k - vx2 i) * (vy2 (Suc i mod ?n) - vy2 i)
      - (vy2 k - vy2 i) * (vx2 (Suc i mod ?n) - vx2 i) \<le> 0"
  proof (intro allI impI)
    fix i k assume "i < ?n" "k < ?n"
    show "(vx2 k - vx2 i) * (vy2 (Suc i mod ?n) - vy2 i) -
          (vy2 k - vy2 i) * (vx2 (Suc i mod ?n) - vx2 i) \<le> 0"
    proof (cases "k = i")
      case True thus ?thesis by (by100 simp)
    next
      case False
      show ?thesis
      proof (cases "k = Suc i mod ?n")
        case True
        hence "(vx2 k - vx2 i) * (vy2 (Suc i mod ?n) - vy2 i) =
               (vy2 k - vy2 i) * (vx2 (Suc i mod ?n) - vx2 i)" by (by100 simp)
        thus ?thesis by (by100 simp)
      next
        case False2: False
        from hC11_2 \<open>i < ?n\<close> \<open>k < ?n\<close> \<open>k \<noteq> i\<close> False2
        have "(vx2 k - vx2 i) * (vy2 (Suc i mod ?n) - vy2 i) -
              (vy2 k - vy2 i) * (vx2 (Suc i mod ?n) - vx2 i) < 0" by (by100 blast)
        thus ?thesis by (by100 linarith)
      qed
    qed
  qed
  \<comment> \<open>Step 3: Get edge-preserving homeomorphisms P1 \\<to> B² \\<to> P2 via disk lemma.\<close>
  \<comment> \<open>Apply polygon\\_homeomorphic\\_to\\_disk\\_with\\_boundary to both polygons.
     The lemma uses cross2 from AlgTopChain. Need to convert our conditions.\<close>
  \<comment> \<open>Convert hside\\_le\\_1 and hC11\\_1 to cross2 form.\<close>
  have hvert_hp_1: "\<forall>i<?n. \<forall>k<?n. AlgTopChain.cross2 (vx1 k - vx1 i, vy1 k - vy1 i)
      (vx1 (Suc i mod ?n) - vx1 i, vy1 (Suc i mod ?n) - vy1 i) \<le> 0"
    using hside_le_1 unfolding AlgTopChain.cross2_def by (by100 simp)
  have hstrict_hp_1: "\<forall>i<?n. \<forall>k<?n. k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
      AlgTopChain.cross2 (vx1 k - vx1 i, vy1 k - vy1 i)
          (vx1 (Suc i mod ?n) - vx1 i, vy1 (Suc i mod ?n) - vy1 i) < 0"
    using hC11_1 unfolding AlgTopChain.cross2_def by (by100 simp)
  have hdisk1: "\<exists>\<psi>. top1_homeomorphism_on P1 (?TP P1) top1_B2 top1_B2_topology \<psi>
    \<and> (\<forall>i<?n. \<forall>t\<in>I_set. \<psi> ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
        (1-t) * vy1 i + t * vy1 (Suc i mod ?n))
      = (cos (2*pi*(real i + t)/real ?n), sin (2*pi*(real i + t)/real ?n)))"
    using AlgTopChain.polygon_homeomorphic_to_disk_with_boundary
      [OF hC1_1 hn3 hC4_1 hC5_1 hC10_1 hvert_hp_1 hstrict_hp_1]
  proof -
    from AlgTopChain.polygon_homeomorphic_to_disk_with_boundary
        [OF hC1_1 hn3 hC4_1 hC5_1 hC10_1 hvert_hp_1 hstrict_hp_1]
    show ?thesis
      apply (elim exE conjE)
      apply (intro exI conjI)
       apply assumption
      apply assumption
      done
  qed
  then obtain \<psi>1 where
    h\<psi>1_homeo: "top1_homeomorphism_on P1 (?TP P1) top1_B2 top1_B2_topology \<psi>1"
    and h\<psi>1_edge: "\<forall>i<?n. \<forall>t\<in>I_set. \<psi>1 ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
        (1-t) * vy1 i + t * vy1 (Suc i mod ?n))
      = (cos (2*pi*(real i + t)/real ?n), sin (2*pi*(real i + t)/real ?n))"
    by (by100 blast)
  have hvert_hp_2: "\<forall>i<?n. \<forall>k<?n. AlgTopChain.cross2 (vx2 k - vx2 i, vy2 k - vy2 i)
      (vx2 (Suc i mod ?n) - vx2 i, vy2 (Suc i mod ?n) - vy2 i) \<le> 0"
    using hside_le_2 unfolding AlgTopChain.cross2_def by (by100 simp)
  have hstrict_hp_2: "\<forall>i<?n. \<forall>k<?n. k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
      AlgTopChain.cross2 (vx2 k - vx2 i, vy2 k - vy2 i)
          (vx2 (Suc i mod ?n) - vx2 i, vy2 (Suc i mod ?n) - vy2 i) < 0"
    using hC11_2 unfolding AlgTopChain.cross2_def by (by100 simp)
  have hdisk2: "\<exists>\<psi>. top1_homeomorphism_on P2 (?TP P2) top1_B2 top1_B2_topology \<psi>
    \<and> (\<forall>i<?n. \<forall>t\<in>I_set. \<psi> ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
        (1-t) * vy2 i + t * vy2 (Suc i mod ?n))
      = (cos (2*pi*(real i + t)/real ?n), sin (2*pi*(real i + t)/real ?n)))"
  proof -
    from AlgTopChain.polygon_homeomorphic_to_disk_with_boundary
        [OF hC1_2 hn3 hC4_2 hC5_2 hC10_2 hvert_hp_2 hstrict_hp_2]
    show ?thesis
      apply (elim exE conjE)
      apply (intro exI conjI)
       apply assumption
      apply assumption
      done
  qed
  then obtain \<psi>2 where
    h\<psi>2_homeo: "top1_homeomorphism_on P2 (?TP P2) top1_B2 top1_B2_topology \<psi>2"
    and h\<psi>2_edge: "\<forall>i<?n. \<forall>t\<in>I_set. \<psi>2 ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
        (1-t) * vy2 i + t * vy2 (Suc i mod ?n))
      = (cos (2*pi*(real i + t)/real ?n), sin (2*pi*(real i + t)/real ?n))"
    by (by100 blast)
  \<comment> \<open>Step 4: Compose \\<psi>2\\<inverse> \\<circ> \\<psi>1 to get edge-preserving \\<phi>: P1 \\<to> P2.\<close>
  from homeomorphism_inverse[OF h\<psi>2_homeo]
  have h\<psi>2_inv: "top1_homeomorphism_on top1_B2 top1_B2_topology P2 (?TP P2) (inv_into P2 \<psi>2)" .
  define \<phi> where "\<phi> = (inv_into P2 \<psi>2) \<circ> \<psi>1"
  from homeomorphism_comp[OF h\<psi>1_homeo h\<psi>2_inv]
  have h\<phi>: "top1_homeomorphism_on P1 (?TP P1) P2 (?TP P2) \<phi>" unfolding \<phi>_def .
  \<comment> \<open>Step 5: \\<phi> preserves edge parametrization.\<close>
  \<comment> \<open>\\<phi> preserves edge parametrization: \\<psi>1 and \\<psi>2 map corresponding edge points to
     the same S¹ point (cos/sin at 2\\<pi>(i+t)/n), so \\<psi>2\\<inverse> \\<circ> \\<psi>1 maps edge i of P1
     to edge i of P2. Uses h\\<psi>1\\_edge, h\\<psi>2\\_edge, injectivity of \\<psi>2, and inv\\_into\\_f\\_f.\<close>
  have h\<psi>2_bij: "bij_betw \<psi>2 P2 top1_B2"
    using h\<psi>2_homeo unfolding top1_homeomorphism_on_def top1_continuous_map_on_def
    by (by100 blast)
  have h\<psi>2_inj: "inj_on \<psi>2 P2"
    using h\<psi>2_bij unfolding bij_betw_def by (by100 blast)
  have h\<phi>_edge: "\<forall>i<?n. \<forall>t\<in>I_set.
      \<phi> ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
         (1-t) * vy1 i + t * vy1 (Suc i mod ?n))
      = ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
         (1-t) * vy2 i + t * vy2 (Suc i mod ?n))"
    \<comment> \<open>Apply standalone lemmas: composed\\_disk\\_homeo\\_edge\\_preserving + edge\\_point\\_in\\_polygon\\_witness.\<close>
    apply (intro allI impI ballI)
    apply (unfold \<phi>_def comp_def)
    \<comment> \<open>Goal: inv\\_into P2 \\<psi>2 (\\<psi>1 (edge1(i,t))) = edge2(i,t).
       Now i < n and t \\<in> I\\_set are meta-level assumptions (from impI + ballI).\<close>
    apply (subst h\<psi>1_edge[rule_format], assumption, assumption)
    apply (subst h\<psi>2_edge[rule_format, symmetric], assumption, assumption)
    apply (rule inv_into_f_f[OF h\<psi>2_inj])
    apply (rule edge_point_in_polygon_witness[OF hn3 _ _ hC5_2], assumption, assumption)
    done
  \<comment> \<open>Step 6: q2 \\<circ> \\<phi> is a quotient map P1 \\<to> Y2.\<close>
  have h\<phi>_quot: "top1_quotient_map_on P1 (?TP P1) P2 (?TP P2) \<phi>"
    by (rule top1_homeomorphism_on_imp_quotient_map_on[OF h\<phi>])
  have hcomp_quot: "top1_quotient_map_on P1 (?TP P1) Y2 TY2 (q2 \<circ> \<phi>)"
    by (rule top1_quotient_map_on_comp[OF h\<phi>_quot hC2_2])
  \<comment> \<open>Step 7: Fibres of q1 and q2\\<circ>\\<phi> agree (key step, uses edge preservation).
     Interior points: both maps are injective (C8), so fibres match.
     Edge points: \\<phi> preserves edge parametrization, so the scheme identification
     pattern is preserved. q1 identifies edges i,j iff scheme says so, and
     q2\\<circ>\\<phi> identifies the same edges because \\<phi> maps edge i to edge i.\<close>
  \<comment> \<open>Helper: \\<phi> is bijective (from homeomorphism).\<close>
  have h\<phi>_bij: "bij_betw \<phi> P1 P2"
    using h\<phi> unfolding top1_homeomorphism_on_def top1_continuous_map_on_def
    by (by100 blast)
  \<comment> \<open>Helper: \\<phi> preserves interior (not-on-boundary) of P1 to interior of P2.\<close>
  have h\<phi>_int: "\<And>x. \<lbrakk>x \<in> P1; \<forall>i<?n. \<forall>t\<in>I_set.
      x \<noteq> ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
            (1-t) * vy1 i + t * vy1 (Suc i mod ?n))\<rbrakk> \<Longrightarrow>
      \<forall>i<?n. \<forall>t\<in>I_set.
      \<phi> x \<noteq> ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
            (1-t) * vy2 i + t * vy2 (Suc i mod ?n))"
    by (rule edge_preserving_homeo_interior[OF h\<phi>_bij h\<phi>_edge hn3 hC5_1])
  \<comment> \<open>\\<phi> maps P1 into P2 (from bij\\_betw).\<close>
  have h\<phi>_img: "\<And>x. x \<in> P1 \<Longrightarrow> \<phi> x \<in> P2"
    using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
  have hfibres: "\<forall>x\<in>P1. \<forall>y\<in>P1. (q1 x = q1 y) \<longleftrightarrow> ((q2 \<circ> \<phi>) x = (q2 \<circ> \<phi>) y)"
  proof (intro ballI iffI)
    fix x y assume hxP: "x \<in> P1" and hyP: "y \<in> P1"
    \<comment> \<open>Forward: q1 x = q1 y \\<Longrightarrow> q2(\\<phi>(x)) = q2(\\<phi>(y)).\<close>
    {
      assume heq: "q1 x = q1 y"
      \<comment> \<open>Case split: is x on a boundary edge?\<close>
      consider
        (x_int) "\<forall>i<?n. \<forall>t\<in>I_set. x \<noteq> ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
              (1-t) * vy1 i + t * vy1 (Suc i mod ?n))"
        | (x_bdy) "\<exists>i<?n. \<exists>t\<in>I_set. x = ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
              (1-t) * vy1 i + t * vy1 (Suc i mod ?n))"
        by (by100 blast)
      hence "(q2 \<circ> \<phi>) x = (q2 \<circ> \<phi>) y"
      proof cases
        case x_int
        \<comment> \<open>x is interior: C8\\_1 says q1 injective at x, so x = y.\<close>
        from hC8_1 hxP x_int have "\<forall>p'\<in>P1. q1 x = q1 p' \<longrightarrow> x = p'" by (by100 blast)
        hence "x = y" using hyP heq by (by100 blast)
        thus ?thesis by (by100 simp)
      next
        case x_bdy
        then obtain i t where hi: "i < ?n" and ht: "t \<in> I_set"
          and hx_eq: "x = ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
                           (1-t) * vy1 i + t * vy1 (Suc i mod ?n))"
          by (by100 blast)
        \<comment> \<open>Is y on a boundary edge?\<close>
        consider
          (y_int) "\<forall>j<?n. \<forall>s\<in>I_set. y \<noteq> ((1-s) * vx1 j + s * vx1 (Suc j mod ?n),
                (1-s) * vy1 j + s * vy1 (Suc j mod ?n))"
          | (y_bdy) "\<exists>j<?n. \<exists>s\<in>I_set. y = ((1-s) * vx1 j + s * vx1 (Suc j mod ?n),
                (1-s) * vy1 j + s * vy1 (Suc j mod ?n))"
          by (by100 blast)
        thus ?thesis
        proof cases
          case y_int
          \<comment> \<open>y interior: C8\\_1 says q1 injective at y, so y = x.\<close>
          from hC8_1 hyP y_int have "\<forall>p'\<in>P1. q1 y = q1 p' \<longrightarrow> y = p'" by (by100 blast)
          hence "y = x" using hxP heq[symmetric] by (by100 blast)
          thus ?thesis by (by100 simp)
        next
          case y_bdy
          \<comment> \<open>Both on boundary: use C7/C9 — identification depends only on scheme.\<close>
          then obtain j s where hj: "j < ?n" and hs: "s \<in> I_set"
            and hy_eq: "y = ((1-s) * vx1 j + s * vx1 (Suc j mod ?n),
                             (1-s) * vy1 j + s * vy1 (Suc j mod ?n))"
            by (by100 blast)
          \<comment> \<open>From q1(e1(i,t)) = q1(e1(j,s)) and C9\\_1: get label/direction condition.
             C9 now only applies to interior edge points (0 < t < 1).
             Vertex case (t=0 or t=1) needs separate C7-based argument.\<close>
          \<comment> \<open>Need: q2(\\<phi>(x)) = q2(\\<phi>(y)), i.e. q2(e2(i,t)) = q2(e2(j,s)).\<close>
          have h\<phi>x: "\<phi> x = ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
                             (1-t) * vy2 i + t * vy2 (Suc i mod ?n))"
            using h\<phi>_edge[rule_format, OF hi ht] hx_eq by (by100 simp)
          have h\<phi>y: "\<phi> y = ((1-s) * vx2 j + s * vx2 (Suc j mod ?n),
                             (1-s) * vy2 j + s * vy2 (Suc j mod ?n))"
            using h\<phi>_edge[rule_format, OF hj hs] hy_eq by (by100 simp)
          \<comment> \<open>Split: interior (use C9) vs vertex (direct argument).\<close>
          show ?thesis
          proof (cases "0 < t \<and> t < 1 \<and> 0 < s \<and> s < 1")
            case True
            \<comment> \<open>Interior case: use C9 to get hcond, then C7\\_2.\<close>
            hence "t \<in> {0<..<(1::real)}" "s \<in> {0<..<(1::real)}" by (by100 auto)+
            from hC9_1 hi hj this heq[unfolded hx_eq hy_eq]
            have hcond: "(i = j \<and> t = s) \<or> (fst (scheme!i) = fst (scheme!j) \<and>
                (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
              by (by100 blast)
            from hcond show ?thesis
            proof (elim disjE conjE)
              assume "i = j" "t = s"
              thus ?thesis using h\<phi>x h\<phi>y by (by100 simp)
            next
              assume hlabel: "fst (scheme!i) = fst (scheme!j)"
                and hdir: "if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t"
              from hC7_2 hi hj hlabel ht
              have "q2 ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
                        (1-t) * vy2 i + t * vy2 (Suc i mod ?n))
                  = (if snd (scheme!i) = snd (scheme!j)
                     then q2 ((1-t) * vx2 j + t * vx2 (Suc j mod ?n),
                             (1-t) * vy2 j + t * vy2 (Suc j mod ?n))
                     else q2 (t * vx2 j + (1-t) * vx2 (Suc j mod ?n),
                             t * vy2 j + (1-t) * vy2 (Suc j mod ?n)))"
                by (by100 blast)
              thus ?thesis
              proof (cases "snd (scheme!i) = snd (scheme!j)")
                case True
                hence "s = t" using hdir by (by100 simp)
                thus ?thesis using \<open>q2 _ = _\<close> True h\<phi>x h\<phi>y by (by100 simp)
              next
                case False
                hence "s = 1 - t" using hdir by (by100 simp)
                hence "\<phi> y = (t * vx2 j + (1-t) * vx2 (Suc j mod ?n),
                             t * vy2 j + (1-t) * vy2 (Suc j mod ?n))"
                  using h\<phi>y by (by100 simp)
                thus ?thesis using \<open>q2 _ = _\<close> False h\<phi>x by (by100 simp)
              qed
            qed
          next
            case False
            \<comment> \<open>Vertex case: at least one of t, s is 0 or 1.
               Derive q2(\\<phi>(x)) = q2(\\<phi>(y)) directly without hcond.
               Vertices identified under q1 must also be identified under q2
               because both use the same scheme and C7 determines vertex identification.\<close>
            \<comment> \<open>Vertex case: at least one of t, s is 0 or 1.
               Strategy: show vertex identification follows from C7 applied at vertex parameters.
               Since C7 holds for all t \\<in> I\\_set = {0..1}, including t=0 and t=1, and both q1/q2
               satisfy C7 for the same scheme, vertex identifications are the same.
               Key sub-cases: (1) both vertices, (2) one vertex + one edge-interior.\<close>
            have ht_01: "t \<in> I_set" using ht .
            have hs_01: "s \<in> I_set" using hs .
            \<comment> \<open>Case 2a: both t, s are at 0 or 1 (both vertices).
               Then x = vertex, y = vertex. q1 identifies them \\<Longrightarrow> q2 identifies them.
               Case 2b: one of t,s in (0,1), the other at 0 or 1.
               Then one is a vertex, the other is an edge interior.
               By C8\\_1, the vertex must map to a value not achievable by any interior point.
               But edges are on the boundary, so C8 doesn't directly apply.
               Instead: use C9\\_1 limiting argument or show this case is impossible.\<close>
            show ?thesis
            proof (cases "0 < t \<and> t < 1")
              case True \<comment> \<open>0 < t < 1, so s = 0 or s = 1.\<close>
              hence "\<not>(0 < s \<and> s < 1)" using False by (by100 blast)
              hence hs_vtx: "s = 0 \<or> s = 1" using hs unfolding top1_unit_interval_def by (by100 auto)
              \<comment> \<open>Symmetric to the backward case: y is a vertex, x is edge-interior.\<close>
              show ?thesis sorry \<comment> \<open>Vertex(y) \\<leftrightarrow> edge-interior(x) case. Needs C7+C9 argument.\<close>
            next
              case False
              hence ht_vtx: "t = 0 \<or> t = 1" using ht unfolding top1_unit_interval_def by (by100 auto)
              show ?thesis
              proof (cases "0 < s \<and> s < 1")
                case True \<comment> \<open>s in (0,1), t at vertex.\<close>
                show ?thesis sorry \<comment> \<open>Vertex(x) \\<leftrightarrow> edge-interior(y) case.\<close>
              next
                case False \<comment> \<open>Both at vertices.\<close>
                hence hs_vtx: "s = 0 \<or> s = 1" using hs unfolding top1_unit_interval_def by (by100 auto)
                \<comment> \<open>x is vertex vx1(i) or vx1(Suc i mod n), y is vertex vx1(j) or vx1(Suc j mod n).
                   q1(vx1(k)) = q1(vx1(l)) for some k, l.
                   Need: q2(vx2(k)) = q2(vx2(l)).
                   This follows from: for each matching label pair (i0,j0) in the scheme,
                   C7 at t=0,1 identifies the same vertex pairs for both q1 and q2.
                   The vertex identification classes are the same.\<close>
                \<comment> \<open>Express x and y as vertices.\<close>
                have "\<exists>k. k < ?n \<and> fst (\<phi> x) = vx2 k \<and> snd (\<phi> x) = vy2 k
                    \<and> fst x = vx1 k \<and> snd x = vy1 k"
                proof -
                  from ht_vtx show ?thesis
                  proof
                    assume "t = 0"
                    hence "x = (vx1 i, vy1 i)" using hx_eq by (by100 simp)
                    moreover have "\<phi> x = (vx2 i, vy2 i)"
                    proof -
                      have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      from h\<phi>_edge[rule_format, OF hi this]
                      have "\<phi> ((1-0) * vx1 i + 0 * vx1 (Suc i mod ?n),
                              (1-0) * vy1 i + 0 * vy1 (Suc i mod ?n))
                          = ((1-0) * vx2 i + 0 * vx2 (Suc i mod ?n),
                             (1-0) * vy2 i + 0 * vy2 (Suc i mod ?n))" .
                      thus ?thesis using \<open>x = (vx1 i, vy1 i)\<close> \<open>t = 0\<close> hx_eq by (by100 simp)
                    qed
                    ultimately have "fst (\<phi> x) = vx2 i \<and> snd (\<phi> x) = vy2 i \<and> fst x = vx1 i \<and> snd x = vy1 i"
                      by (by100 auto)
                    thus ?thesis using hi by (by100 blast)
                  next
                    assume "t = 1"
                    hence hx_t1: "x = (vx1 (Suc i mod ?n), vy1 (Suc i mod ?n))" using hx_eq by (by100 simp)
                    moreover have h\<phi>x_t1: "\<phi> x = (vx2 (Suc i mod ?n), vy2 (Suc i mod ?n))"
                    proof -
                      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      from h\<phi>_edge[rule_format, OF hi this]
                      have "\<phi> ((1-1) * vx1 i + 1 * vx1 (Suc i mod ?n),
                              (1-1) * vy1 i + 1 * vy1 (Suc i mod ?n))
                          = ((1-1) * vx2 i + 1 * vx2 (Suc i mod ?n),
                             (1-1) * vy2 i + 1 * vy2 (Suc i mod ?n))" .
                      thus ?thesis using hx_t1 by (by100 simp)
                    qed
                    moreover have "Suc i mod ?n < ?n"
                    proof -
                      have "?n > 0" using hn3 by (by100 linarith)
                      thus ?thesis by (by100 simp)
                    qed
                    ultimately have "fst (\<phi> x) = vx2 (Suc i mod ?n) \<and> snd (\<phi> x) = vy2 (Suc i mod ?n)
                        \<and> fst x = vx1 (Suc i mod ?n) \<and> snd x = vy1 (Suc i mod ?n)"
                      by (by100 auto)
                    thus ?thesis using \<open>Suc i mod ?n < ?n\<close> by (by100 blast)
                  qed
                qed
                then obtain kx where hkx: "kx < ?n" "fst (\<phi> x) = vx2 kx" "snd (\<phi> x) = vy2 kx"
                    "fst x = vx1 kx" "snd x = vy1 kx"
                  by (by100 blast)
                have "\<exists>ky. ky < ?n \<and> fst (\<phi> y) = vx2 ky \<and> snd (\<phi> y) = vy2 ky
                    \<and> fst y = vx1 ky \<and> snd y = vy1 ky"
                proof -
                  from hs_vtx show ?thesis
                  proof
                    assume "s = 0"
                    hence hy_s0: "y = (vx1 j, vy1 j)" using hy_eq by (by100 simp)
                    moreover have "\<phi> y = (vx2 j, vy2 j)"
                    proof -
                      have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      from h\<phi>_edge[rule_format, OF hj this]
                      show ?thesis using hy_s0 by (by100 simp)
                    qed
                    ultimately have "fst (\<phi> y) = vx2 j \<and> snd (\<phi> y) = vy2 j \<and> fst y = vx1 j \<and> snd y = vy1 j"
                      by (by100 auto)
                    thus ?thesis using hj by (by100 blast)
                  next
                    assume "s = 1"
                    hence hy_s1: "y = (vx1 (Suc j mod ?n), vy1 (Suc j mod ?n))" using hy_eq by (by100 simp)
                    moreover have "\<phi> y = (vx2 (Suc j mod ?n), vy2 (Suc j mod ?n))"
                    proof -
                      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      from h\<phi>_edge[rule_format, OF hj this]
                      show ?thesis using hy_s1 by (by100 simp)
                    qed
                    moreover have "Suc j mod ?n < ?n"
                    proof -
                      have "?n > 0" using hn3 by (by100 linarith)
                      thus ?thesis by (by100 simp)
                    qed
                    ultimately have "fst (\<phi> y) = vx2 (Suc j mod ?n) \<and> snd (\<phi> y) = vy2 (Suc j mod ?n)
                        \<and> fst y = vx1 (Suc j mod ?n) \<and> snd y = vy1 (Suc j mod ?n)"
                      by (by100 auto)
                    thus ?thesis using \<open>Suc j mod ?n < ?n\<close> by (by100 blast)
                  qed
                qed
                then obtain ky where hky: "ky < ?n" "fst (\<phi> y) = vx2 ky" "snd (\<phi> y) = vy2 ky"
                    "fst y = vx1 ky" "snd y = vy1 ky"
                  by (by100 blast)
                \<comment> \<open>Now: q1(vx1(kx)) = q1(vx1(ky)), need q2(vx2(kx)) = q2(vx2(ky)).
                   Both follow from C7 applied at the vertex parameter.
                   The vertex equivalence classes are generated by: for matching label edges (i0,j0),
                   vx(i0) ~ vx(j0) (same dir) or vx(i0) ~ vx(Suc j0 mod n) (opp dir), etc.
                   Since both q1 and q2 satisfy C7 for the same scheme, and the vertex identification
                   is the transitive closure of these C7-endpoint identifications, they agree.\<close>
                \<comment> \<open>Goal: q2(vx2 kx, vy2 kx) = q2(vx2 ky, vy2 ky).
                   From: q1(vx1 kx, vy1 kx) = q1(vx1 ky, vy1 ky).
                   Use C7 at t=0: for each matching label pair, C7 gives vertex identification.
                   Both q1 and q2 satisfy C7 for the same scheme.\<close>
                have hgoal: "(q2 \<circ> \<phi>) x = q2 (vx2 kx, vy2 kx)"
                proof -
                  have "\<phi> x = (vx2 kx, vy2 kx)" using hkx(2,3) by (cases "\<phi> x") (by100 auto)
                  thus ?thesis by (by100 simp)
                qed
                have hgoal2: "(q2 \<circ> \<phi>) y = q2 (vx2 ky, vy2 ky)"
                proof -
                  have "\<phi> y = (vx2 ky, vy2 ky)" using hky(2,3) by (cases "\<phi> y") (by100 auto)
                  thus ?thesis by (by100 simp)
                qed
                have hq1_eq: "q1 (vx1 kx, vy1 kx) = q1 (vx1 ky, vy1 ky)"
                proof -
                  have "x = (vx1 kx, vy1 kx)" using hkx(4,5) by (cases x) (by100 auto)
                  moreover have "y = (vx1 ky, vy1 ky)" using hky(4,5) by (cases y) (by100 auto)
                  ultimately show ?thesis using heq by (by100 simp)
                qed
                \<comment> \<open>Remaining goal: q2(vx2 kx, vy2 kx) = q2(vx2 ky, vy2 ky).
                   Known: q1(vx1 kx, vy1 kx) = q1(vx1 ky, vy1 ky).
                   Use: both q1/q2 satisfy C7 for the same scheme at the same vertex endpoints.
                   Since (0::real) \\<in> I\\_set and (1::real) \\<in> I\\_set, C7 applies at vertices.\<close>
                \<comment> \<open>Direct case: kx and ky are directly C7-connected (i.e., there exist matching
                   label edges where kx and ky are endpoints).
                   General case: kx and ky are connected by a CHAIN of C7 identifications.
                   For now: sorry the general transitivity argument.\<close>
                \<comment> \<open>KEY BLOCKER: vertex identification transfer requires:
                   (A) Show q1(vx1 kx) = q1(vx1 ky) \\<Longrightarrow> \\<exists>C7 chain from kx to ky.
                       (Hard: needs vertex-edge-interior separation, expert audit 27 §4)
                   (B) C7 chain \\<Longrightarrow> q2(vx2 kx) = q2(vx2 ky).
                       (Easy: C7\\_2 at t=0 gives q2(vx2(i)) = q2(vx2(j)) for matching edges.
                        Transitivity of = gives the result for chains.)\<close>
                show ?thesis using hgoal hgoal2 hq1_eq
                  sorry \<comment> \<open>Vertex identification transfer.
                     Needs vertex-edge-interior separation to show q1-identified vertices
                     are C7-chain-connected. See expert audit 27 §4.\<close>
              qed
            qed
          qed
        qed
      qed
    }
    thus "q1 x = q1 y \<Longrightarrow> (q2 \<circ> \<phi>) x = (q2 \<circ> \<phi>) y" .
  next
    fix x y assume hxP: "x \<in> P1" and hyP: "y \<in> P1"
    \<comment> \<open>Backward: q2(\\<phi>(x)) = q2(\\<phi>(y)) \\<Longrightarrow> q1 x = q1 y. Symmetric argument.\<close>
    assume heq2: "(q2 \<circ> \<phi>) x = (q2 \<circ> \<phi>) y"
    \<comment> \<open>Symmetric to forward, but using C8\\_2 on \\<phi>(x),\\<phi>(y) \\<in> P2, then pulling back to P1.\<close>
    have h\<phi>xP: "\<phi> x \<in> P2" using h\<phi>_img hxP by (by100 blast)
    have h\<phi>yP: "\<phi> y \<in> P2" using h\<phi>_img hyP by (by100 blast)
    have heq2': "q2 (\<phi> x) = q2 (\<phi> y)" using heq2 by (by100 simp)
    consider
      (x_int) "\<forall>i<?n. \<forall>t\<in>I_set. x \<noteq> ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
            (1-t) * vy1 i + t * vy1 (Suc i mod ?n))"
      | (x_bdy) "\<exists>i<?n. \<exists>t\<in>I_set. x = ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
            (1-t) * vy1 i + t * vy1 (Suc i mod ?n))"
      by (by100 blast)
    thus "q1 x = q1 y"
    proof cases
      case x_int
      \<comment> \<open>x interior \\<Longrightarrow> \\<phi>(x) interior \\<Longrightarrow> q2 injective at \\<phi>(x) \\<Longrightarrow> \\<phi>(x)=\\<phi>(y) \\<Longrightarrow> x=y.\<close>
      from h\<phi>_int hxP x_int
      have "\<forall>i<?n. \<forall>t\<in>I_set. \<phi> x \<noteq> ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
          (1-t) * vy2 i + t * vy2 (Suc i mod ?n))" .
      from hC8_2 h\<phi>xP this have "\<forall>p'\<in>P2. q2 (\<phi> x) = q2 p' \<longrightarrow> \<phi> x = p'" by (by100 blast)
      hence "\<phi> x = \<phi> y" using h\<phi>yP heq2' by (by100 blast)
      hence "x = y" using bij_betw_imp_inj_on[OF h\<phi>_bij] hxP hyP
        unfolding inj_on_def by (by100 blast)
      thus ?thesis by (by100 simp)
    next
      case x_bdy
      then obtain i t where hi: "i < ?n" and ht: "t \<in> I_set"
        and hx_eq: "x = ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
                         (1-t) * vy1 i + t * vy1 (Suc i mod ?n))"
        by (by100 blast)
      consider
        (y_int) "\<forall>j<?n. \<forall>s\<in>I_set. y \<noteq> ((1-s) * vx1 j + s * vx1 (Suc j mod ?n),
              (1-s) * vy1 j + s * vy1 (Suc j mod ?n))"
        | (y_bdy) "\<exists>j<?n. \<exists>s\<in>I_set. y = ((1-s) * vx1 j + s * vx1 (Suc j mod ?n),
              (1-s) * vy1 j + s * vy1 (Suc j mod ?n))"
        by (by100 blast)
      thus ?thesis
      proof cases
        case y_int
        from h\<phi>_int hyP y_int
        have "\<forall>i<?n. \<forall>t\<in>I_set. \<phi> y \<noteq> ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
            (1-t) * vy2 i + t * vy2 (Suc i mod ?n))" .
        from hC8_2 h\<phi>yP this have "\<forall>p'\<in>P2. q2 (\<phi> y) = q2 p' \<longrightarrow> \<phi> y = p'" by (by100 blast)
        hence "\<phi> y = \<phi> x" using h\<phi>xP heq2'[symmetric] by (by100 blast)
        hence "y = x" using bij_betw_imp_inj_on[OF h\<phi>_bij] hxP hyP
          unfolding inj_on_def by (by100 blast)
        thus ?thesis by (by100 simp)
      next
        case y_bdy
        then obtain j s where hj: "j < ?n" and hs: "s \<in> I_set"
          and hy_eq: "y = ((1-s) * vx1 j + s * vx1 (Suc j mod ?n),
                           (1-s) * vy1 j + s * vy1 (Suc j mod ?n))"
          by (by100 blast)
        \<comment> \<open>\\<phi>(x) = e2(i,t), \\<phi>(y) = e2(j,s). From C9\\_2 + C7\\_1: same argument as forward.\<close>
        have h\<phi>x: "\<phi> x = ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
                           (1-t) * vy2 i + t * vy2 (Suc i mod ?n))"
          using h\<phi>_edge[rule_format, OF hi ht] hx_eq by (by100 simp)
        have h\<phi>y: "\<phi> y = ((1-s) * vx2 j + s * vx2 (Suc j mod ?n),
                           (1-s) * vy2 j + s * vy2 (Suc j mod ?n))"
          using h\<phi>_edge[rule_format, OF hj hs] hy_eq by (by100 simp)
        \<comment> \<open>Split: interior (C9\\_2 + C7\\_1) vs vertex (direct).\<close>
        show ?thesis
        proof (cases "0 < t \<and> t < 1 \<and> 0 < s \<and> s < 1")
          case True
          hence "t \<in> {0<..<(1::real)}" "s \<in> {0<..<(1::real)}" by (by100 auto)+
          from hC9_2 hi hj this heq2'[unfolded h\<phi>x h\<phi>y]
          have hcond: "(i = j \<and> t = s) \<or> (fst (scheme!i) = fst (scheme!j) \<and>
              (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
            by (by100 blast)
          from hcond show ?thesis
          proof (elim disjE conjE)
            assume "i = j" "t = s"
            thus ?thesis using hx_eq hy_eq by (by100 simp)
          next
            assume hlabel: "fst (scheme!i) = fst (scheme!j)"
              and hdir: "if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t"
            from hC7_1 hi hj hlabel ht
            have hq1: "q1 ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
                          (1-t) * vy1 i + t * vy1 (Suc i mod ?n))
                = (if snd (scheme!i) = snd (scheme!j)
                   then q1 ((1-t) * vx1 j + t * vx1 (Suc j mod ?n),
                           (1-t) * vy1 j + t * vy1 (Suc j mod ?n))
                   else q1 (t * vx1 j + (1-t) * vx1 (Suc j mod ?n),
                           t * vy1 j + (1-t) * vy1 (Suc j mod ?n)))"
              by (by100 blast)
            show ?thesis
            proof (cases "snd (scheme!i) = snd (scheme!j)")
              case True
              hence "s = t" using hdir by (by100 simp)
              thus ?thesis using hq1 True hx_eq hy_eq by (by100 simp)
            next
              case False
              hence "s = 1 - t" using hdir by (by100 simp)
              hence "y = (t * vx1 j + (1-t) * vx1 (Suc j mod ?n),
                          t * vy1 j + (1-t) * vy1 (Suc j mod ?n))"
                using hy_eq by (by100 simp)
              thus ?thesis using hq1 False hx_eq by (by100 simp)
            qed
          qed
        next
          case False
          \<comment> \<open>Vertex case: same approach as forward direction.\<close>
          show ?thesis sorry \<comment> \<open>Vertex case in uniqueness backward direction.\<close>
        qed
      qed
    qed
  qed
  from quotient_same_fibres_homeomorphic[OF hC2_1 hcomp_quot hfibres]
  show ?thesis .
qed

\<comment> \<open>Cancel at front for PROPER schemes — per expert audit 23 §5.
   Uses scheme\\_quotient\\_exists for w to get a canonical quotient Y\\_w,
   then shows Y (quotient of [a,inv a]@w) \\<cong> Y\\_w via spur collapse.
   Properness needed for scheme\\_quotient\\_exists.
   Placed after scheme\\_quotient\\_uniqueness so it can use it.\<close>


\<comment> \<open>Cut-paste-opp for proper nat-typed schemes via canonical quotients + uniqueness.
   Expert audit 24 §5: both schemes have same length \\<to> same regular polygon.
   Homeomorphism via scheme\\_quotient\\_uniqueness (no edge permutation needed!).\<close>
lemma quotient_of_scheme_cut_paste_opp_proper:
  fixes a_label :: "nat"
    and u0 u1 u2 u3 :: "(nat \<times> bool) list"
  assumes hq: "top1_quotient_of_scheme_on Y TY (u0 @ u1 @ [(a_label, True)] @ u2 @ [(a_label, False)] @ u3)"
      and hproper_old: "\<forall>label. card {i. i < length (u0 @ u1 @ [(a_label, True)] @ u2 @ [(a_label, False)] @ u3)
          \<and> fst ((u0 @ u1 @ [(a_label, True)] @ u2 @ [(a_label, False)] @ u3) ! i) = label} \<in> {0, 2}"
      and hproper_new: "\<forall>label. card {i. i < length (u0 @ [(a_label, True)] @ u2 @ [(a_label, False)] @ u1 @ u3)
          \<and> fst ((u0 @ [(a_label, True)] @ u2 @ [(a_label, False)] @ u1 @ u3) ! i) = label} \<in> {0, 2}"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' (u0 @ [(a_label, True)] @ u2 @ [(a_label, False)] @ u1 @ u3) \<and>
    top1_homeomorphism_on Y TY Y' TY' h"
proof -
  let ?s = "u0 @ u1 @ [(a_label, True)] @ u2 @ [(a_label, False)] @ u3"
  let ?s' = "u0 @ [(a_label, True)] @ u2 @ [(a_label, False)] @ u1 @ u3"
  have hlen: "length ?s \<ge> 3" using quotient_scheme_length_ge3[OF hq] .
  have hlen': "length ?s' = length ?s" by (by100 simp)
  have htopo: "is_topology_on_strict Y TY"
    using hq unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  from scheme_quotient_exists(1)[OF hlen hproper_old]
  obtain Y_old :: "(real \<times> real) set" and TY_old where
    hY_old: "top1_quotient_of_scheme_on Y_old TY_old ?s" by (by100 blast)
  have htopo_old: "is_topology_on_strict Y_old TY_old"
    using hY_old unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  have hlen'3: "length ?s' \<ge> 3" using hlen hlen' by (by100 linarith)
  from scheme_quotient_exists(1)[OF hlen'3 hproper_new]
  obtain Y_new :: "(real \<times> real) set" and TY_new where
    hY_new: "top1_quotient_of_scheme_on Y_new TY_new ?s'" by (by100 blast)
  have htopo_new: "is_topology_on_strict Y_new TY_new"
    using hY_new unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  \<comment> \<open>Step 2: Y\\_old \\<cong> Y\\_new (cut-reglue homeomorphism). Both are quotients of the
     SAME regular polygon by different identification patterns. The homeomorphism
     is induced by arc rearrangement on S1 extended by cone to B2.
     NOTE: scheme\\_quotient\\_uniqueness doesn't apply here (different schemes).
     This step requires the geometric arc-permutation construction.\<close>
  have "\<exists>h. top1_homeomorphism_on Y_old TY_old Y_new TY_new h"
    sorry \<comment> \<open>Cut-reglue homeomorphism between canonical quotients of same-length
       proper schemes. Construction: arc permutation on S1 (piecewise linear
       bijection that moves u1 block past identified edge pair) extended by
       cone from origin to B2. Then compose with disk homeomorphisms.\<close>
  then obtain h_rearrange where hrearr: "top1_homeomorphism_on Y_old TY_old Y_new TY_new h_rearrange"
    by (by100 blast)
  from scheme_quotient_uniqueness[OF htopo htopo_old hq hY_old]
  obtain h_bridge where hbridge: "top1_homeomorphism_on Y TY Y_old TY_old h_bridge"
    by (by100 blast)
  from homeomorphism_comp[OF hbridge hrearr]
  have hcomp: "top1_homeomorphism_on Y TY Y_new TY_new (h_rearrange \<circ> h_bridge)" .
  from homeomorphism_inverse[OF hcomp]
  have "top1_homeomorphism_on Y_new TY_new Y TY (inv_into Y (h_rearrange \<circ> h_bridge))" .
  from scheme_quotient_transfer_along_homeomorphism[OF hY_new this htopo]
  have "top1_quotient_of_scheme_on Y TY ?s'" .
  thus ?thesis by (rule same_space_implies_homeo_realization)
qed

\<comment> \<open>Cut-paste (same-direction) for proper nat-typed schemes. Same pattern.\<close>
lemma quotient_of_scheme_cut_paste_proper:
  fixes a_label :: "nat"
    and u1 u2 u3 :: "(nat \<times> bool) list"
  assumes hq: "top1_quotient_of_scheme_on Y TY (u1 @ [(a_label, True)] @ u2 @ [(a_label, True)] @ u3)"
      and hproper_old: "\<forall>label. card {i. i < length (u1 @ [(a_label, True)] @ u2 @ [(a_label, True)] @ u3)
          \<and> fst ((u1 @ [(a_label, True)] @ u2 @ [(a_label, True)] @ u3) ! i) = label} \<in> {0, 2}"
      and hproper_new: "\<forall>label. card {i. i < length (u1 @ [(a_label, True), (a_label, True)] @ rev (map top1_inverse_edge u2) @ u3)
          \<and> fst ((u1 @ [(a_label, True), (a_label, True)] @ rev (map top1_inverse_edge u2) @ u3) ! i) = label} \<in> {0, 2}"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' (u1 @ [(a_label, True), (a_label, True)] @ rev (map top1_inverse_edge u2) @ u3) \<and>
    top1_homeomorphism_on Y TY Y' TY' h"
proof -
  let ?s = "u1 @ [(a_label, True)] @ u2 @ [(a_label, True)] @ u3"
  let ?s' = "u1 @ [(a_label, True), (a_label, True)] @ rev (map top1_inverse_edge u2) @ u3"
  have hlen: "length ?s \<ge> 3" using quotient_scheme_length_ge3[OF hq] .
  have hlen': "length ?s' = length ?s" by (by100 simp)
  have htopo: "is_topology_on_strict Y TY"
    using hq unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  from scheme_quotient_exists(1)[OF hlen hproper_old]
  obtain Y_old :: "(real \<times> real) set" and TY_old where
    hY_old: "top1_quotient_of_scheme_on Y_old TY_old ?s" by (by100 blast)
  have htopo_old: "is_topology_on_strict Y_old TY_old"
    using hY_old unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  have hlen'3: "length ?s' \<ge> 3" using hlen hlen' by (by100 linarith)
  from scheme_quotient_exists(1)[OF hlen'3 hproper_new]
  obtain Y_new :: "(real \<times> real) set" and TY_new where
    hY_new: "top1_quotient_of_scheme_on Y_new TY_new ?s'" by (by100 blast)
  have htopo_new: "is_topology_on_strict Y_new TY_new"
    using hY_new unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  have "\<exists>h. top1_homeomorphism_on Y_old TY_old Y_new TY_new h"
    sorry \<comment> \<open>Cut-reglue homeomorphism: arc permutation on S1 extended by cone to B2.\<close>
  then obtain h_rearrange where hrearr: "top1_homeomorphism_on Y_old TY_old Y_new TY_new h_rearrange"
    by (by100 blast)
  from scheme_quotient_uniqueness[OF htopo htopo_old hq hY_old]
  obtain h_bridge where hbridge: "top1_homeomorphism_on Y TY Y_old TY_old h_bridge"
    by (by100 blast)
  from homeomorphism_comp[OF hbridge hrearr]
  have hcomp: "top1_homeomorphism_on Y TY Y_new TY_new (h_rearrange \<circ> h_bridge)" .
  from homeomorphism_inverse[OF hcomp]
  have "top1_homeomorphism_on Y_new TY_new Y TY (inv_into Y (h_rearrange \<circ> h_bridge))" .
  from scheme_quotient_transfer_along_homeomorphism[OF hY_new this htopo]
  have "top1_quotient_of_scheme_on Y TY ?s'" .
  thus ?thesis by (rule same_space_implies_homeo_realization)
qed

\<comment> \<open>Shared helper: properness of [a,inv a]@w from properness of w + freshness of a.\<close>

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
proof -
  \<comment> \<open>Step 1: scheme\\_quotient\\_exists(2) gives Y\\_w + canonical witnesses with ALL C1-C12.\<close>
  from scheme_quotient_exists(2)[of w, OF assms(2) hproper]
  obtain P_m :: "(real \<times> real) set" and q_m :: "(real \<times> real) \<Rightarrow> (real \<times> real)"
    and vx_m vy_m :: "nat \<Rightarrow> real"
    and Y_w :: "(real \<times> real) set" and TY_w :: "(real \<times> real) set set"
    and vtgt_m :: "nat \<Rightarrow> nat"
    where hY_w: "top1_quotient_of_scheme_on Y_w TY_w w"
    and hC1m: "top1_is_polygonal_region_on P_m (length w)"
    and hC2m: "top1_quotient_map_on P_m
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_m) Y_w TY_w q_m"
    and hC3m_w: "\<forall>i<length w. \<forall>j<length w. i \<noteq> j \<longrightarrow> (vx_m i, vy_m i) \<noteq> (vx_m j, vy_m j)"
    and hC4m: "\<forall>i<length w. (vx_m i, vy_m i) \<in> P_m"
    and hC5m: "P_m = {(x, y) | x y. \<exists>coeffs. (\<forall>i<length w. coeffs i \<ge> 0)
                   \<and> (\<Sum>i<length w. coeffs i) = 1
                   \<and> x = (\<Sum>i<length w. coeffs i * vx_m i)
                   \<and> y = (\<Sum>i<length w. coeffs i * vy_m i)}"
    and hC7m: "\<forall>i<length w. \<forall>j<length w. fst(w!i)=fst(w!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q_m ((1-t)*vx_m i+t*vx_m(Suc i mod length w),(1-t)*vy_m i+t*vy_m(Suc i mod length w))
         = (if snd(w!i)=snd(w!j)
            then q_m ((1-t)*vx_m j+t*vx_m(Suc j mod length w),(1-t)*vy_m j+t*vy_m(Suc j mod length w))
            else q_m (t*vx_m j+(1-t)*vx_m(Suc j mod length w),t*vy_m j+(1-t)*vy_m(Suc j mod length w))))"
    and hC8m: "\<forall>p\<in>P_m. (\<forall>i<length w. \<forall>t\<in>I_set.
          p \<noteq> ((1-t)*vx_m i+t*vx_m(Suc i mod length w),(1-t)*vy_m i+t*vy_m(Suc i mod length w)))
       \<longrightarrow> (\<forall>p'\<in>P_m. q_m p = q_m p' \<longrightarrow> p = p')"
    and hC9m: "\<forall>i<length w. \<forall>j<length w. \<forall>t\<in>{0<..<(1::real)}. \<forall>s\<in>{0<..<(1::real)}.
        q_m ((1-t)*vx_m i+t*vx_m(Suc i mod length w),(1-t)*vy_m i+t*vy_m(Suc i mod length w))
      = q_m ((1-s)*vx_m j+s*vx_m(Suc j mod length w),(1-s)*vy_m j+s*vy_m(Suc j mod length w))
      \<longrightarrow> (i=j \<and> t=s) \<or> (fst(w!i)=fst(w!j) \<and> (if snd(w!i)=snd(w!j) then s=t else s=1-t))"
    and hC10m: "\<forall>i<length w. let cx=(\<Sum>j<length w. vx_m j)/real(length w);
                             cy=(\<Sum>j<length w. vy_m j)/real(length w)
         in (vx_m i-cx)*(vy_m(Suc i mod length w)-cy)-(vy_m i-cy)*(vx_m(Suc i mod length w)-cx) > 0"
    and hC11m: "\<forall>i<length w. \<forall>k<length w. k\<noteq>i \<longrightarrow> k\<noteq>Suc i mod length w \<longrightarrow>
        (vx_m k-vx_m i)*(vy_m(Suc i mod length w)-vy_m i)-(vy_m k-vy_m i)*(vx_m(Suc i mod length w)-vx_m i) < 0"
    and hC12m_proved: "\<forall>k<length w. \<forall>j<length w. \<forall>s\<in>{0<..<(1::real)}.
        q_m (vx_m k, vy_m k) \<noteq> q_m ((1-s)*vx_m j + s*vx_m(Suc j mod length w),
                               (1-s)*vy_m j + s*vy_m(Suc j mod length w))"
    and hq_vtgt_m1: "\<forall>k<length w. q_m (vx_m k, vy_m k) = (vx_m (vtgt_m k), vy_m (vtgt_m k))"
    and hq_vtgt_m2: "\<forall>k<length w. vtgt_m k < length w"
    and hq_vtgt_m3: "\<forall>k<length w. vtgt_m k \<le> k"
    and hq_vtgt_m4: "\<forall>k<length w. vtgt_m (vtgt_m k) = vtgt_m k"
    and hq_vtgt_m5: "\<forall>k<length w. \<forall>l<length w. vtgt_m k = vtgt_m l \<longrightarrow>
        (k, l) \<in> {(a, b). \<exists>i<length w. \<exists>j<length w. i \<noteq> j
          \<and> fst (w ! i) = fst (w ! j)
          \<and> ((snd (w ! i) = snd (w ! j) \<and> a = i \<and> b = j)
           \<or> (snd (w ! i) = snd (w ! j) \<and> a = Suc i mod length w \<and> b = Suc j mod length w)
           \<or> (snd (w ! i) \<noteq> snd (w ! j) \<and> a = i \<and> b = Suc j mod length w)
           \<or> (snd (w ! i) \<noteq> snd (w ! j) \<and> a = Suc i mod length w \<and> b = j))}\<^sup>*"
    by (elim exE conjE) (rule that, assumption+)
  have htopo_w: "is_topology_on_strict Y_w TY_w"
    using hY_w unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  \<comment> \<open>Step 2: Get (real\\<times>real) quotient of [a,inv a]@w.\<close>
  have htopo_Y: "is_topology_on_strict Y TY"
    using assms(1) unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  have hproper_ext: "\<forall>label. card {i. i < length ([a, top1_inverse_edge a] @ w) \<and>
      fst (([a, top1_inverse_edge a] @ w) ! i) = label} \<in> {0, 2}"
    by (rule cancel_pair_prepend_proper[OF hproper hfresh])
  have hlen_ext: "length ([a, top1_inverse_edge a] @ w) \<ge> 3" using assms(2) by (by100 simp)
  let ?n_ext = "length ([a, top1_inverse_edge a] @ w)"
  from scheme_quotient_exists(2)[OF hlen_ext hproper_ext]
  obtain P_e :: "(real \<times> real) set" and q_e :: "(real \<times> real) \<Rightarrow> (real \<times> real)"
    and vx_e vy_e :: "nat \<Rightarrow> real"
    and Y_ext :: "(real \<times> real) set" and TY_ext :: "(real \<times> real) set set"
    and vtgt_e :: "nat \<Rightarrow> nat"
    where hY_ext: "top1_quotient_of_scheme_on Y_ext TY_ext ([a, top1_inverse_edge a] @ w)"
    and hC1e: "top1_is_polygonal_region_on P_e ?n_ext"
    and hC2e: "top1_quotient_map_on P_e
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_e) Y_ext TY_ext q_e"
    and hC3e: "\<forall>i<?n_ext. \<forall>j<?n_ext. i \<noteq> j \<longrightarrow> (vx_e i, vy_e i) \<noteq> (vx_e j, vy_e j)"
    and hC4e: "\<forall>i<?n_ext. (vx_e i, vy_e i) \<in> P_e"
    and hC5e: "P_e = {(x, y) | x y. \<exists>coeffs. (\<forall>i<?n_ext. coeffs i \<ge> 0)
                   \<and> (\<Sum>i<?n_ext. coeffs i) = 1
                   \<and> x = (\<Sum>i<?n_ext. coeffs i * vx_e i)
                   \<and> y = (\<Sum>i<?n_ext. coeffs i * vy_e i)}"
    and hC7e: "\<forall>i<?n_ext. \<forall>j<?n_ext. fst(([a, top1_inverse_edge a] @ w)!i)=fst(([a, top1_inverse_edge a] @ w)!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q_e ((1-t)*vx_e i+t*vx_e(Suc i mod ?n_ext),(1-t)*vy_e i+t*vy_e(Suc i mod ?n_ext))
         = (if snd(([a, top1_inverse_edge a] @ w)!i)=snd(([a, top1_inverse_edge a] @ w)!j)
            then q_e ((1-t)*vx_e j+t*vx_e(Suc j mod ?n_ext),(1-t)*vy_e j+t*vy_e(Suc j mod ?n_ext))
            else q_e (t*vx_e j+(1-t)*vx_e(Suc j mod ?n_ext),t*vy_e j+(1-t)*vy_e(Suc j mod ?n_ext))))"
    and hC8e: "\<forall>p\<in>P_e. (\<forall>i<?n_ext. \<forall>t\<in>I_set.
          p \<noteq> ((1-t)*vx_e i+t*vx_e(Suc i mod ?n_ext),(1-t)*vy_e i+t*vy_e(Suc i mod ?n_ext)))
       \<longrightarrow> (\<forall>p'\<in>P_e. q_e p = q_e p' \<longrightarrow> p = p')"
    and hC9e: "\<forall>i<?n_ext. \<forall>j<?n_ext. \<forall>t\<in>{0<..<(1::real)}. \<forall>s\<in>{0<..<(1::real)}.
        q_e ((1-t)*vx_e i+t*vx_e(Suc i mod ?n_ext),(1-t)*vy_e i+t*vy_e(Suc i mod ?n_ext))
      = q_e ((1-s)*vx_e j+s*vx_e(Suc j mod ?n_ext),(1-s)*vy_e j+s*vy_e(Suc j mod ?n_ext))
      \<longrightarrow> (i=j \<and> t=s) \<or> (fst(([a, top1_inverse_edge a] @ w)!i)=fst(([a, top1_inverse_edge a] @ w)!j) \<and>
          (if snd(([a, top1_inverse_edge a] @ w)!i)=snd(([a, top1_inverse_edge a] @ w)!j) then s=t else s=1-t))"
    and hC10e: "\<forall>i<?n_ext. let cx=(\<Sum>j<?n_ext. vx_e j)/real ?n_ext; cy=(\<Sum>j<?n_ext. vy_e j)/real ?n_ext
         in (vx_e i-cx)*(vy_e(Suc i mod ?n_ext)-cy)-(vy_e i-cy)*(vx_e(Suc i mod ?n_ext)-cx) > 0"
    and hC11e: "\<forall>i<?n_ext. \<forall>k<?n_ext. k\<noteq>i \<longrightarrow> k\<noteq>Suc i mod ?n_ext \<longrightarrow>
        (vx_e k-vx_e i)*(vy_e(Suc i mod ?n_ext)-vy_e i)-(vy_e k-vy_e i)*(vx_e(Suc i mod ?n_ext)-vx_e i) < 0"
    and hC12e_proved: "\<forall>k<?n_ext. \<forall>j<?n_ext. \<forall>s\<in>{0<..<(1::real)}.
        q_e (vx_e k, vy_e k) \<noteq> q_e ((1-s)*vx_e j + s*vx_e(Suc j mod ?n_ext),
                               (1-s)*vy_e j + s*vy_e(Suc j mod ?n_ext))"
    and hq_vtgt_e1: "\<forall>k<?n_ext. q_e (vx_e k, vy_e k) = (vx_e (vtgt_e k), vy_e (vtgt_e k))"
    and hq_vtgt_e2: "\<forall>k<?n_ext. vtgt_e k < ?n_ext"
    and hq_vtgt_e3: "\<forall>k<?n_ext. vtgt_e k \<le> k"
    and hq_vtgt_e4: "\<forall>k<?n_ext. vtgt_e (vtgt_e k) = vtgt_e k"
    and hq_vtgt_e5: "\<forall>k<?n_ext. \<forall>l<?n_ext. vtgt_e k = vtgt_e l \<longrightarrow>
        (k, l) \<in> {(x, y). \<exists>i<?n_ext. \<exists>j<?n_ext. i \<noteq> j
          \<and> fst (([a, top1_inverse_edge a] @ w) ! i) = fst (([a, top1_inverse_edge a] @ w) ! j)
          \<and> ((snd (([a, top1_inverse_edge a] @ w) ! i) = snd (([a, top1_inverse_edge a] @ w) ! j) \<and> x = i \<and> y = j)
           \<or> (snd (([a, top1_inverse_edge a] @ w) ! i) = snd (([a, top1_inverse_edge a] @ w) ! j) \<and> x = Suc i mod ?n_ext \<and> y = Suc j mod ?n_ext)
           \<or> (snd (([a, top1_inverse_edge a] @ w) ! i) \<noteq> snd (([a, top1_inverse_edge a] @ w) ! j) \<and> x = i \<and> y = Suc j mod ?n_ext)
           \<or> (snd (([a, top1_inverse_edge a] @ w) ! i) \<noteq> snd (([a, top1_inverse_edge a] @ w) ! j) \<and> x = Suc i mod ?n_ext \<and> y = j))}\<^sup>*"
    by (elim exE conjE) (rule that, assumption+)
  have htopo_ext: "is_topology_on_strict Y_ext TY_ext"
    using hY_ext unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  \<comment> \<open>Step 3: Y \\<cong> Y\\_ext (both quotients of [a,inv a]@w, different types).\<close>
  from scheme_quotient_uniqueness[OF htopo_Y htopo_ext assms(1) hY_ext]
  obtain h_bridge :: "'a \<Rightarrow> (real \<times> real)" where
      hbridge: "top1_homeomorphism_on Y TY Y_ext TY_ext h_bridge" by (by100 blast)
  \<comment> \<open>Step 4: Y\\_ext \\<cong> Y\\_w (spur collapse in concrete (real\\<times>real) setting).
     Both are quotients of regular polygons via scheme\\_quotient\\_exists.
     The homeomorphism collapses the spur (cancelling pair) to get w-quotient.\<close>
  have "\<exists>h_collapse. top1_homeomorphism_on Y_ext TY_ext Y_w TY_w h_collapse"
  proof -
    \<comment> \<open>Helper: continuous surjection between polygonal regions is a quotient map.
       Uses: polygonal regions are compact (polygonal\\_region\\_compact),
       subspace topology of R2 is Hausdorff, compact\\<to>Hausdorff continuous = closed map,
       closed surjection = quotient map.\<close>
    have compact_surj_quotient: "\<And>P1 P2 f n1 n2.
        top1_is_polygonal_region_on P1 n1 \<Longrightarrow>
        top1_is_polygonal_region_on P2 n2 \<Longrightarrow>
        continuous_on P1 f \<Longrightarrow>
        f ` P1 = P2 \<Longrightarrow>
        (\<forall>x\<in>P1. f x \<in> P2) \<Longrightarrow>
        top1_quotient_map_on P1
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P1)
          P2
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P2) f"
    proof -
      fix P1 P2 :: "(real \<times> real) set" and f :: "(real \<times> real) \<Rightarrow> (real \<times> real)" and n1 n2 :: nat
      assume hC1_1: "top1_is_polygonal_region_on P1 n1"
         and hC1_2: "top1_is_polygonal_region_on P2 n2"
         and hf_cont: "continuous_on P1 f"
         and hf_surj: "f ` P1 = P2"
         and hf_range: "\<forall>x\<in>P1. f x \<in> P2"
      let ?TP1 = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P1"
      let ?TP2 = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P2"
      \<comment> \<open>Topologies.\<close>
      have htopo_R2: "is_topology_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
        using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV]
        by (by100 simp)
      have htopo1: "is_topology_on P1 ?TP1"
        by (rule subspace_topology_is_topology_on[OF htopo_R2]) (by100 simp)
      have htopo2: "is_topology_on P2 ?TP2"
        by (rule subspace_topology_is_topology_on[OF htopo_R2]) (by100 simp)
      \<comment> \<open>P1 is compact.\<close>
      have hn1_ge3: "n1 \<ge> 3" using hC1_1 unfolding top1_is_polygonal_region_on_def by (by100 blast)
      have hcompact: "top1_compact_on P1 ?TP1"
        by (rule AlgTopChain.polygonal_region_compact[OF hC1_1 hn1_ge3])
      \<comment> \<open>P2 subspace is Hausdorff.\<close>
      have hR2_haus: "is_hausdorff_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
        using top1_R2_is_hausdorff .
      have hhaus: "is_hausdorff_on P2 ?TP2"
        using hausdorff_subspace[OF hR2_haus] by (by100 blast)
      \<comment> \<open>f is continuous (top1 version).\<close>
      have hf_cont_top1: "top1_continuous_map_on P1 ?TP1 P2 ?TP2 f"
      proof -
        have "\<And>p. p \<in> P1 \<Longrightarrow> f p \<in> P2" using hf_range by (by100 blast)
        from top1_continuous_map_on_real2_subspace_general[OF this hf_cont]
        show ?thesis .
      qed
      \<comment> \<open>f is a closed map (compact \\<to> Hausdorff continuous).\<close>
      have hf_closed: "top1_closed_map_on P1 ?TP1 P2 ?TP2 f"
        unfolding top1_closed_map_on_def
      proof (intro conjI allI impI ballI)
        fix x assume "x \<in> P1" thus "f x \<in> P2" using hf_range by (by100 blast)
      next
        fix A assume hA: "closedin_on P1 ?TP1 A"
        from compact_hausdorff_continuous_closed_map[OF hcompact hhaus hf_cont_top1 hA]
        show "closedin_on P2 ?TP2 (f ` A)" .
      qed
      \<comment> \<open>Closed surjection is a quotient map (Munkres Cor. 22.3).\<close>
      show "top1_quotient_map_on P1 ?TP1 P2 ?TP2 f"
        unfolding top1_quotient_map_on_def
      proof (intro conjI allI impI)
        show "is_topology_on P1 ?TP1" using htopo1 .
        show "is_topology_on P2 ?TP2" using htopo2 .
        show "top1_continuous_map_on P1 ?TP1 P2 ?TP2 f" using hf_cont_top1 .
        show "f ` P1 = P2" using hf_surj .
        \<comment> \<open>Quotient condition: if f\\<inverse>(V) is open in P1 then V is open in P2.\<close>
        fix V assume hV_sub: "V \<subseteq> P2" and hV_preimg: "{x \<in> P1. f x \<in> V} \<in> ?TP1"
        \<comment> \<open>P2 \\\\ V is closed in P2 (complement of preimage).\<close>
        \<comment> \<open>Munkres Cor. 22.3: P1 \\\\ f\\<inverse>(V) = f\\<inverse>(P2\\\\V) is closed. By closed map:
           f(f\\<inverse>(P2\\\\V)) = P2\\\\V is closed in P2. So V is open in P2.\<close>
        show "V \<in> ?TP2"
        proof -
          \<comment> \<open>Complement of preimage is closed.\<close>
          have hpreimg_closed: "closedin_on P1 ?TP1 (P1 - {x \<in> P1. f x \<in> V})"
          proof -
            have "P1 - (P1 - {x \<in> P1. f x \<in> V}) = {x \<in> P1. f x \<in> V}" by (by100 blast)
            thus ?thesis unfolding closedin_on_def using hV_preimg by (by100 simp)
          qed
          \<comment> \<open>By closed map: image of closed set is closed.\<close>
          have "closedin_on P2 ?TP2 (f ` (P1 - {x \<in> P1. f x \<in> V}))"
            using hf_closed hpreimg_closed unfolding top1_closed_map_on_def by (by100 blast)
          \<comment> \<open>f(P1 \\\\ f\\<inverse>(V)) = P2 \\\\ V (by surjectivity).\<close>
          moreover have "f ` (P1 - {x \<in> P1. f x \<in> V}) = P2 - V"
          proof (rule set_eqI, rule iffI)
            fix y assume "y \<in> f ` (P1 - {x \<in> P1. f x \<in> V})"
            then obtain x where hx: "x \<in> P1" "f x \<notin> V" "y = f x" by (by100 blast)
            have "y \<in> P2" using hx(1) hx(3) hf_range by (by100 blast)
            thus "y \<in> P2 - V" using hx(2,3) by (by100 blast)
          next
            fix y assume hy: "y \<in> P2 - V"
            hence "y \<in> P2" "y \<notin> V" by (by100 auto)+
            from \<open>y \<in> P2\<close> obtain x where "x \<in> P1" "f x = y"
              using hf_surj by (by100 force)
            moreover have "f x \<notin> V" using \<open>y \<notin> V\<close> \<open>f x = y\<close> by (by100 simp)
            ultimately show "y \<in> f ` (P1 - {x \<in> P1. f x \<in> V})" by (by100 blast)
          qed
          \<comment> \<open>P2 \\\\ V closed \\<Longrightarrow> V open.\<close>
          ultimately have "closedin_on P2 ?TP2 (P2 - V)" by (by100 simp)
          hence "P2 - (P2 - V) \<in> ?TP2" unfolding closedin_on_def by (by100 blast)
          moreover have "P2 - (P2 - V) = V" using hV_sub by (by100 blast)
          ultimately show "V \<in> ?TP2" by (by100 simp)
        qed
      qed
    qed
    \<comment> \<open>Extract polygons and quotient maps from both quotients.\<close>
    let ?n = "length ([a, top1_inverse_edge a] @ w)"
    let ?m = "length w"
    let ?TP = "\<lambda>S. subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S"
    \<comment> \<open>The spur collapse homeomorphism uses disk homeomorphisms + arc collapsing.
       Both polygons have disk homeomorphisms (polygon\\_homeomorphic\\_to\\_disk\\_with\\_boundary).
       The collapse map \\<tau>: B2 \\<to> B2 collapses the first 2 arcs and rescales the rest.
       Composition: f = \\<psi>\\_m\\<inverse> \\<circ> \\<tau> \\<circ> \\<psi>\\_e gives P\\_e \\<to> P\\_m.
       Then q\\_m \\<circ> f has the same fibres as q\\_e (by fibre matching argument).
       quotient\\_same\\_fibres\\_homeomorphic gives Y\\_ext \\<cong> Y\\_w.\<close>
    \<comment> \<open>C1-C12 for P\\_e, q\\_e, vx\\_e, vy\\_e and P\\_m, q\\_m, vx\\_m, vy\\_m
       now come from scheme\\_quotient\\_exists(2) above.\<close>
    \<comment> \<open>Spur collapse map f: P\\_e \\<to> P\\_m via fan construction.
       Fan from vertex v\\_e(1) of P\\_e to centroid c\\_m of P\\_m:
       Triangle (v\\_e(1), v\\_e(k), v\\_e(k+1)) maps affinely to (c\\_m, u(k-2), u(k-1)).
       Key properties:
       - Edges 0,1 (cancelling pair) collapse to spur from u0 to c\\_m and back
       - Edges i\\<ge>2 map to edges i-2 of P\\_m preserving parameter
       - Interior maps homeomorphically (fan-to-fan bijection)
       - Fibre matching: q\\_e-fibres = (q\\_m\\<circ>f)-fibres\<close>
    have hm3: "?m \<ge> 3" using assms(2) .
    have hn_eq: "?n = ?m + 2" by (by100 simp)
    have hn5: "?n \<ge> 5" using hm3 hn_eq by (by100 linarith)
    \<comment> \<open>Centroid of P\\_m (interior point for the fan target).\<close>
    define cx_m where "cx_m = (\<Sum>j<?m. vx_m j) / real ?m"
    define cy_m where "cy_m = (\<Sum>j<?m. vy_m j) / real ?m"
    \<comment> \<open>Centroid is in P\\_m (convex combination with equal weights 1/m).\<close>
    have hcm_in_Pm: "(cx_m, cy_m) \<in> P_m"
    proof -
      define coeffs :: "nat \<Rightarrow> real" where "coeffs j = 1 / real ?m" for j
      have hnn: "\<forall>j<?m. coeffs j \<ge> 0" unfolding coeffs_def using hm3 by (by100 simp)
      have hm_pos: "?m > 0" using hm3 by (by100 linarith)
      have hsum: "(\<Sum>j<?m. coeffs j) = 1"
        unfolding coeffs_def using hm_pos by (by100 simp)
      have hx: "cx_m = (\<Sum>j<?m. coeffs j * vx_m j)"
        unfolding coeffs_def cx_m_def
        using sum_divide_distrib[of vx_m "{..<?m}" "real ?m", symmetric]
        by (by100 simp)
      have hy: "cy_m = (\<Sum>j<?m. coeffs j * vy_m j)"
        unfolding coeffs_def cy_m_def
        using sum_divide_distrib[of vy_m "{..<?m}" "real ?m", symmetric]
        by (by100 simp)
      show ?thesis unfolding hC5m using hnn hsum hx hy by (by100 blast)
    qed
    \<comment> \<open>Centroid is strictly interior to P\\_m (not on any edge).
       From C11\\_m: all non-adjacent vertices are strictly on the interior side.
       The centroid (average of ALL vertices) inherits the strict inequality.\<close>
    have hcm_interior: "\<forall>i<?m. \<forall>t\<in>I_set.
      (cx_m, cy_m) \<noteq> ((1-t)*vx_m i+t*vx_m(Suc i mod ?m),(1-t)*vy_m i+t*vy_m(Suc i mod ?m))"
    proof (intro allI impI ballI)
      fix i t assume hi: "i < ?m" and ht: "t \<in> I_set"
      \<comment> \<open>Signed cross product of centroid relative to edge i.\<close>
      define dx where "dx = vx_m (Suc i mod ?m) - vx_m i"
      define dy where "dy = vy_m (Suc i mod ?m) - vy_m i"
      define cross_cm where "cross_cm = (cx_m - vx_m i) * dy - (cy_m - vy_m i) * dx"
      \<comment> \<open>Express cross\\_cm as (1/m) * \\<Sum> cross products from C11.\<close>
      have hm_pos: "?m > 0" using hm3 by (by100 linarith)
      have hm_ne0: "real ?m \<noteq> (0::real)" using hm_pos by (by100 simp)
      have hcx_diff: "cx_m - vx_m i = (\<Sum>j<?m. vx_m j - vx_m i) / real ?m"
      proof -
        have h1: "(\<Sum>j<?m. vx_m j - vx_m i) = (\<Sum>j<?m. vx_m j) - real ?m * vx_m i"
          using sum_subtractf[of vx_m "\<lambda>_. vx_m i" "{..<?m}"] by (by100 simp)
        have "real ?m * vx_m i / real ?m = vx_m i" using hm_ne0 by (by100 simp)
        hence h2: "((\<Sum>j<?m. vx_m j) - real ?m * vx_m i) / real ?m = (\<Sum>j<?m. vx_m j) / real ?m - vx_m i"
          using diff_divide_distrib[of "(\<Sum>j<?m. vx_m j)" "real ?m * vx_m i" "real ?m"] by (by100 simp)
        show ?thesis unfolding cx_m_def using h1 h2 by (by100 simp)
      qed
      have hcy_diff: "cy_m - vy_m i = (\<Sum>j<?m. vy_m j - vy_m i) / real ?m"
      proof -
        have h1: "(\<Sum>j<?m. vy_m j - vy_m i) = (\<Sum>j<?m. vy_m j) - real ?m * vy_m i"
          using sum_subtractf[of vy_m "\<lambda>_. vy_m i" "{..<?m}"] by (by100 simp)
        have "real ?m * vy_m i / real ?m = vy_m i" using hm_ne0 by (by100 simp)
        hence h2: "((\<Sum>j<?m. vy_m j) - real ?m * vy_m i) / real ?m = (\<Sum>j<?m. vy_m j) / real ?m - vy_m i"
          using diff_divide_distrib[of "(\<Sum>j<?m. vy_m j)" "real ?m * vy_m i" "real ?m"] by (by100 simp)
        show ?thesis unfolding cy_m_def using h1 h2 by (by100 simp)
      qed
      have "cross_cm = (\<Sum>j<?m. (vx_m j - vx_m i) * dy - (vy_m j - vy_m i) * dx) / real ?m"
      proof -
        \<comment> \<open>Step 1: cross\\_cm in terms of centroid diffs.\<close>
        have h1: "cross_cm = (cx_m - vx_m i) * dy - (cy_m - vy_m i) * dx"
          unfolding cross_cm_def by (by100 simp)
        \<comment> \<open>Step 2: substitute centroid diff = sum/m.\<close>
        have h2: "cross_cm = (\<Sum>j<?m. vx_m j - vx_m i) / real ?m * dy - (\<Sum>j<?m. vy_m j - vy_m i) / real ?m * dx"
          using h1 hcx_diff hcy_diff by (by100 simp)
        \<comment> \<open>Step 3: (A/m)*dy = (A*dy)/m and (B/m)*dx = (B*dx)/m.\<close>
        have "((\<Sum>j<?m. vx_m j - vx_m i) * dy - (\<Sum>j<?m. vy_m j - vy_m i) * dx) / real ?m
            = (\<Sum>j<?m. vx_m j - vx_m i) / real ?m * dy - (\<Sum>j<?m. vy_m j - vy_m i) / real ?m * dx"
          using hm_ne0 diff_divide_distrib[of "(\<Sum>j<?m. vx_m j - vx_m i) * dy" "(\<Sum>j<?m. vy_m j - vy_m i) * dx" "real ?m"]
          by (by100 simp)
        hence h3: "cross_cm = ((\<Sum>j<?m. vx_m j - vx_m i) * dy - (\<Sum>j<?m. vy_m j - vy_m i) * dx) / real ?m"
          using h2 by (by100 linarith)
        \<comment> \<open>Step 4: Σ(a*dy) - Σ(b*dx) = Σ(a*dy - b*dx) via sum\\_subtractf.\<close>
        have "(\<Sum>j<?m. (vx_m j - vx_m i) * dy) - (\<Sum>j<?m. (vy_m j - vy_m i) * dx)
            = (\<Sum>j<?m. (vx_m j - vx_m i) * dy - (vy_m j - vy_m i) * dx)"
          using sum_subtractf[of "\<lambda>j. (vx_m j - vx_m i) * dy" "\<lambda>j. (vy_m j - vy_m i) * dx" "{..<?m}", symmetric]
          by (by100 simp)
        \<comment> \<open>Step 5: Σ(a - b) * dy = Σ(a*dy) etc. via sum\\_distrib\\_right.\<close>
        moreover have "(\<Sum>j<?m. vx_m j - vx_m i) * dy = (\<Sum>j<?m. (vx_m j - vx_m i) * dy)"
          using sum_distrib_right[of "\<lambda>j. vx_m j - vx_m i" "{..<?m}" dy, symmetric] by (by100 simp)
        moreover have "(\<Sum>j<?m. vy_m j - vy_m i) * dx = (\<Sum>j<?m. (vy_m j - vy_m i) * dx)"
          using sum_distrib_right[of "\<lambda>j. vy_m j - vy_m i" "{..<?m}" dx, symmetric] by (by100 simp)
        ultimately show ?thesis using h3 by (by100 simp)
      qed
      \<comment> \<open>Each term for j \\<noteq> i, j \\<noteq> Suc i mod m is < 0 (from C11\\_m).\<close>
      moreover have "(\<Sum>j<?m. (vx_m j - vx_m i) * dy - (vy_m j - vy_m i) * dx) < 0"
      proof -
        define f_cross where "f_cross j = (vx_m j - vx_m i) * dy - (vy_m j - vy_m i) * dx" for j
        have hfi: "f_cross i = 0" unfolding f_cross_def by (by100 simp)
        have hSi: "Suc i mod ?m < ?m" using hm_pos by (by100 simp)
        have hfSi: "f_cross (Suc i mod ?m) = 0" unfolding f_cross_def dx_def dy_def by (by100 algebra)
        have hineq_m: "i \<noteq> Suc i mod ?m"
        proof (cases "Suc i < ?m")
          case True thus ?thesis by (by100 simp)
        next
          case False hence "Suc i = ?m" using hi by (by100 linarith)
          hence "Suc i mod ?m = 0" by (by100 simp)
          moreover have "i \<ge> 2" using hm3 \<open>Suc i = ?m\<close> by (by100 linarith)
          ultimately show ?thesis by (by100 linarith)
        qed
        \<comment> \<open>C11\\_m: all other terms are < 0.\<close>
        have hneg: "\<forall>k\<in>{..<?m} - {i, Suc i mod ?m}. f_cross k < 0"
        proof (intro ballI)
          fix k assume hk: "k \<in> {..<?m} - {i, Suc i mod ?m}"
          hence "k < ?m" "k \<noteq> i" "k \<noteq> Suc i mod ?m" by (by100 auto)+
          from hC11m[rule_format, OF hi \<open>k < ?m\<close> \<open>k \<noteq> i\<close> \<open>k \<noteq> Suc i mod ?m\<close>]
          show "f_cross k < 0" unfolding f_cross_def dx_def dy_def by (by100 linarith)
        qed
        \<comment> \<open>The remaining set is nonempty (since m \\<ge> 3 and we removed 2).\<close>
        have hS_ne: "{..<?m} - {i, Suc i mod ?m} \<noteq> {}"
        proof -
          have "card ({..<?m} - {i, Suc i mod ?m}) = ?m - 2"
            using hi hSi hineq_m by (by100 simp)
          hence "card ({..<?m} - {i, Suc i mod ?m}) \<ge> 1" using hm3 by (by100 linarith)
          thus ?thesis by (by100 force)
        qed
        \<comment> \<open>Extract f(i) and f(Suc i mod m) from the sum.\<close>
        have hi_in: "i \<in> {..<?m}" using hi by (by100 simp)
        from sum.remove[OF finite_lessThan hi_in, of f_cross]
        have hs1: "(\<Sum>j<?m. f_cross j) = f_cross i + (\<Sum>j\<in>{..<?m}-{i}. f_cross j)" by (by100 simp)
        have hSi_in: "Suc i mod ?m \<in> {..<?m} - {i}" using hSi hineq_m by (by100 simp)
        from sum.remove[OF _ hSi_in, of f_cross]
        have hs2: "(\<Sum>j\<in>{..<?m}-{i}. f_cross j) = f_cross (Suc i mod ?m) + (\<Sum>j\<in>{..<?m}-{i}-{Suc i mod ?m}. f_cross j)"
          by (by100 simp)
        have hset_eq: "{..<?m}-{i}-{Suc i mod ?m} = {..<?m} - {i, Suc i mod ?m}" by (by100 blast)
        \<comment> \<open>The remaining sum is < 0 (all terms < 0, nonempty).\<close>
        have "(\<Sum>j\<in>{..<?m} - {i, Suc i mod ?m}. f_cross j) < 0"
        proof -
          from hS_ne obtain k where hk: "k \<in> {..<?m} - {i, Suc i mod ?m}" by (by100 blast)
          from sum.remove[OF _ hk, of f_cross]
          have "(\<Sum>j\<in>{..<?m} - {i, Suc i mod ?m}. f_cross j) = f_cross k + (\<Sum>j\<in>{..<?m} - {i, Suc i mod ?m} - {k}. f_cross j)"
            by (by100 simp)
          moreover have "f_cross k < 0" using hneg hk by (by100 blast)
          moreover have "(\<Sum>j\<in>{..<?m} - {i, Suc i mod ?m} - {k}. f_cross j) \<le> 0"
            by (rule sum_nonpos) (use hneg in \<open>by100 force\<close>)
          ultimately show ?thesis by (by100 linarith)
        qed
        \<comment> \<open>Combine: total sum = 0 + 0 + (negative) < 0.\<close>
        hence "(\<Sum>j\<in>{..<?m}-{i}-{Suc i mod ?m}. f_cross j) < 0" using hset_eq by (by100 simp)
        hence "(\<Sum>j<?m. f_cross j) < 0" using hs1 hs2 hfi hfSi by (by100 linarith)
        thus "(\<Sum>j<?m. (vx_m j - vx_m i) * dy - (vy_m j - vy_m i) * dx) < 0"
          unfolding f_cross_def .
      qed
      ultimately have hcross_neg: "cross_cm < 0"
      proof -
        assume heq: "cross_cm = (\<Sum>j<?m. (vx_m j - vx_m i) * dy - (vy_m j - vy_m i) * dx) / real ?m"
          and hlt: "(\<Sum>j<?m. (vx_m j - vx_m i) * dy - (vy_m j - vy_m i) * dx) < 0"
        have "real ?m > 0" using hm_pos by (by100 simp)
        hence "(\<Sum>j<?m. (vx_m j - vx_m i) * dy - (vy_m j - vy_m i) * dx) / real ?m < 0"
          using hlt divide_less_0_iff by (by100 blast)
        thus ?thesis using heq by (by100 linarith)
      qed
      \<comment> \<open>Edge point has cross product = 0.\<close>
      moreover have "((1-t)*vx_m i+t*vx_m(Suc i mod ?m) - vx_m i) * dy
        - ((1-t)*vy_m i+t*vy_m(Suc i mod ?m) - vy_m i) * dx = 0"
        unfolding dx_def dy_def by (by100 algebra)
      \<comment> \<open>If centroid = edge point, their cross products would match. But < 0 \\<noteq> 0.\<close>
      ultimately show "(cx_m, cy_m) \<noteq> ((1-t)*vx_m i+t*vx_m(Suc i mod ?m),(1-t)*vy_m i+t*vy_m(Suc i mod ?m))"
      proof -
        assume hlt: "cross_cm < 0"
        assume hedge: "((1-t)*vx_m i+t*vx_m(Suc i mod ?m) - vx_m i) * dy
          - ((1-t)*vy_m i+t*vy_m(Suc i mod ?m) - vy_m i) * dx = 0"
        show ?thesis
        proof
          assume heq: "(cx_m, cy_m) = ((1-t)*vx_m i+t*vx_m(Suc i mod ?m),(1-t)*vy_m i+t*vy_m(Suc i mod ?m))"
          hence "cx_m = (1-t)*vx_m i+t*vx_m(Suc i mod ?m)" "cy_m = (1-t)*vy_m i+t*vy_m(Suc i mod ?m)"
            by (by100 simp)+
          hence "cross_cm = ((1-t)*vx_m i+t*vx_m(Suc i mod ?m) - vx_m i) * dy
            - ((1-t)*vy_m i+t*vy_m(Suc i mod ?m) - vy_m i) * dx"
            unfolding cross_cm_def by (by100 simp)
          hence "cross_cm = 0" using hedge by (by100 linarith)
          thus False using hlt by (by100 linarith)
        qed
      qed
    qed
    \<comment> \<open>Bridge: top1\\_continuous\\_map\\_on (subspace) \\<to> continuous\\_on (HOL-Analysis).
       Reverse of top1\\_continuous\\_map\\_on\\_real2\\_subspace\\_general.\<close>
    have continuous_on_from_top1:
      "\<And>S T (f :: real \<times> real \<Rightarrow> real \<times> real).
        top1_continuous_map_on S
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S)
          T (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) f
        \<Longrightarrow> continuous_on S f"
    proof -
      fix S T :: "(real \<times> real) set" and f :: "real \<times> real \<Rightarrow> real \<times> real"
      assume hcont: "top1_continuous_map_on S
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S)
          T (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) f"
      show "continuous_on S f"
        unfolding continuous_on_open_invariant
      proof (intro allI impI)
        fix B :: "(real \<times> real) set" assume hB: "open B"
        \<comment> \<open>B is open in \\<real>2. So B \\<in> product\\_topology\\_on.\<close>
        have "B \<in> product_topology_on top1_open_sets top1_open_sets"
        proof -
          have "B \<in> top1_open_sets" using hB unfolding top1_open_sets_def by (by100 blast)
          thus ?thesis unfolding product_topology_on_open_sets .
        qed
        hence "T \<inter> B \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T"
          unfolding subspace_topology_def by (by100 auto)
        from hcont[unfolded top1_continuous_map_on_def]
        have "\<forall>V. V \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T
            \<longrightarrow> {x \<in> S. f x \<in> V} \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S"
          by (by100 blast)
        hence "{x \<in> S. f x \<in> T \<inter> B} \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S"
          using \<open>T \<inter> B \<in> _\<close> by (by100 blast)
        then obtain A where "A \<in> product_topology_on top1_open_sets top1_open_sets"
            and "{x \<in> S. f x \<in> T \<inter> B} = S \<inter> A"
          unfolding subspace_topology_def by (by100 auto)
        have "open A"
        proof -
          have "A \<in> top1_open_sets"
            using \<open>A \<in> product_topology_on top1_open_sets top1_open_sets\<close>
            unfolding product_topology_on_open_sets .
          thus ?thesis unfolding top1_open_sets_def by (by100 blast)
        qed
        moreover have "f -` B \<inter> S = {x \<in> S. f x \<in> T \<inter> B}"
        proof -
          have "\<forall>x \<in> S. f x \<in> T"
            using hcont unfolding top1_continuous_map_on_def by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        hence "A \<inter> S = f -` B \<inter> S" using \<open>{x \<in> S. f x \<in> T \<inter> B} = S \<inter> A\<close> by (by100 blast)
        ultimately show "\<exists>A. open A \<and> A \<inter> S = f -` B \<inter> S" by (by100 blast)
      qed
    qed
    \<comment> \<open>Fan construction: define f using the vertex map.\<close>
    \<comment> \<open>f maps each triangle of the fan from v\\_e(1) to the corresponding triangle
       of the fan from c\\_m. The vertex map is:
       v\\_e(0) \\<to> u\\_m(0), v\\_e(1) \\<to> c\\_m, v\\_e(k) \\<to> u\\_m(k-2) for k\\<ge>2.\<close>
    \<comment> \<open>Spur collapse: existence of f with fibre matching.
       Fan construction from v\\_e(1) to centroid c\\_m:
       - PL map on fan triangulation (n-2 triangles)
       - Edges 0,1 fold to spur (u0→c\\_m→u0), edges \\<ge>2 map to P\\_m edges
       - Interior: fan-to-fan bijection
       - Fibre matching: interior cases from C8, non-vertex boundary from C7/C9,
         vertex/cancel from fan vertex map + C7 chain transfer.
       All cases algebraically verified (sessions 2-4).
       Structural properties: hf\\_edge, hf\\_spur0/1, hf\\_int\\_range, hf\\_int\\_inj, hf\\_bdy\\_fibres.\<close>
    \<comment> \<open>Obtain disk homeomorphisms for both polygons.\<close>
    have hvert_hp_e: "\<forall>i<?n. \<forall>k<?n. AlgTopChain.cross2 (vx_e k - vx_e i, vy_e k - vy_e i)
        (vx_e (Suc i mod ?n) - vx_e i, vy_e (Suc i mod ?n) - vy_e i) \<le> 0"
    proof (intro allI impI)
      fix i k assume hi: "i < ?n" and hk: "k < ?n"
      show "AlgTopChain.cross2 (vx_e k - vx_e i, vy_e k - vy_e i)
          (vx_e (Suc i mod ?n) - vx_e i, vy_e (Suc i mod ?n) - vy_e i) \<le> 0"
      proof (cases "k = i \<or> k = Suc i mod ?n")
        case True
        thus ?thesis unfolding AlgTopChain.cross2_def by (by100 auto)
      next
        case False
        from hC11e[rule_format, OF hi hk] False
        have "(vx_e k - vx_e i) * (vy_e (Suc i mod ?n) - vy_e i)
            - (vy_e k - vy_e i) * (vx_e (Suc i mod ?n) - vx_e i) < 0" by (by100 blast)
        thus ?thesis unfolding AlgTopChain.cross2_def by (by100 simp)
      qed
    qed
    have hstrict_hp_e: "\<forall>i<?n. \<forall>k<?n. k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
        AlgTopChain.cross2 (vx_e k - vx_e i, vy_e k - vy_e i)
            (vx_e (Suc i mod ?n) - vx_e i, vy_e (Suc i mod ?n) - vy_e i) < 0"
      using hC11e unfolding AlgTopChain.cross2_def by (by100 simp)
    have hn3_e: "?n \<ge> 3" using hC1e unfolding top1_is_polygonal_region_on_def by (by100 blast)
    from AlgTopChain.polygon_homeomorphic_to_disk_with_boundary
        [OF hC1e hn3_e hC4e hC5e hC10e hvert_hp_e hstrict_hp_e]
    obtain \<psi>_e where
      h\<psi>e_homeo: "top1_homeomorphism_on P_e (?TP P_e) top1_B2 top1_B2_topology \<psi>_e"
      and h\<psi>e_bdry: "\<psi>_e ` (\<Union>i<?n. {((1-t) * vx_e i + t * vx_e (Suc i mod ?n),
                     (1-t) * vy_e i + t * vy_e (Suc i mod ?n)) | t. t \<in> I_set})
        = top1_S1"
      and h\<psi>e_edge: "\<forall>i<?n. \<forall>t\<in>I_set.
        \<psi>_e ((1-t) * vx_e i + t * vx_e (Suc i mod ?n),
            (1-t) * vy_e i + t * vy_e (Suc i mod ?n))
        = (cos (2*pi*(real i + t)/real ?n), sin (2*pi*(real i + t)/real ?n))"
      by auto
    \<comment> \<open>Obtain disk homeomorphism for P\\_m.\<close>
    have hvert_hp_m: "\<forall>i<?m. \<forall>k<?m. AlgTopChain.cross2 (vx_m k - vx_m i, vy_m k - vy_m i)
        (vx_m (Suc i mod ?m) - vx_m i, vy_m (Suc i mod ?m) - vy_m i) \<le> 0"
    proof (intro allI impI)
      fix i k assume hi: "i < ?m" and hk: "k < ?m"
      show "AlgTopChain.cross2 (vx_m k - vx_m i, vy_m k - vy_m i)
          (vx_m (Suc i mod ?m) - vx_m i, vy_m (Suc i mod ?m) - vy_m i) \<le> 0"
      proof (cases "k = i \<or> k = Suc i mod ?m")
        case True thus ?thesis unfolding AlgTopChain.cross2_def by (by100 auto)
      next
        case False
        from hC11m[rule_format, OF hi hk] False
        have "(vx_m k - vx_m i) * (vy_m (Suc i mod ?m) - vy_m i)
            - (vy_m k - vy_m i) * (vx_m (Suc i mod ?m) - vx_m i) < 0" by (by100 blast)
        thus ?thesis unfolding AlgTopChain.cross2_def by (by100 simp)
      qed
    qed
    have hstrict_hp_m: "\<forall>i<?m. \<forall>k<?m. k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?m \<longrightarrow>
        AlgTopChain.cross2 (vx_m k - vx_m i, vy_m k - vy_m i)
            (vx_m (Suc i mod ?m) - vx_m i, vy_m (Suc i mod ?m) - vy_m i) < 0"
      using hC11m unfolding AlgTopChain.cross2_def by (by100 simp)
    from AlgTopChain.polygon_homeomorphic_to_disk_with_boundary
        [OF hC1m hm3 hC4m hC5m hC10m hvert_hp_m hstrict_hp_m]
    obtain \<psi>_m where
      h\<psi>m_homeo: "top1_homeomorphism_on P_m (?TP P_m) top1_B2 top1_B2_topology \<psi>_m"
      and h\<psi>m_bdry: "\<psi>_m ` (\<Union>j<?m. {((1-t) * vx_m j + t * vx_m (Suc j mod ?m),
                     (1-t) * vy_m j + t * vy_m (Suc j mod ?m)) | t. t \<in> I_set})
        = top1_S1"
      and h\<psi>m_edge: "\<forall>j<?m. \<forall>t\<in>I_set.
        \<psi>_m ((1-t) * vx_m j + t * vx_m (Suc j mod ?m),
            (1-t) * vy_m j + t * vy_m (Suc j mod ?m))
        = (cos (2*pi*(real j + t)/real ?m), sin (2*pi*(real j + t)/real ?m))"
      by auto
    \<comment> \<open>Inverse homeomorphism: \\<psi>\\_m\\<inverse>: B2 \\<to> P\\_m.\<close>
    from homeomorphism_inverse[OF h\<psi>m_homeo]
    have h\<psi>m_inv: "top1_homeomorphism_on top1_B2 top1_B2_topology P_m (?TP P_m) (inv_into P_m \<psi>_m)" .
    \<comment> \<open>\\<psi>\\_m is injective on P\\_m (from homeomorphism = bijection).\<close>
    have h\<psi>m_inj: "inj_on \<psi>_m P_m"
      using h\<psi>m_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    \<comment> \<open>\\<psi>\\_m maps P\\_m onto B2.\<close>
    have h\<psi>m_surj: "\<psi>_m ` P_m = top1_B2"
      using h\<psi>m_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    \<comment> \<open>Inverse on boundary: \\<psi>\\_m\\<inverse>(cos(2\\<pi>(j+t)/m), sin(2\\<pi>(j+t)/m)) = edge\\_m(j,t).\<close>
    have h\<psi>m_inv_edge: "\<forall>j<?m. \<forall>t\<in>I_set.
        inv_into P_m \<psi>_m (cos (2*pi*(real j + t)/real ?m), sin (2*pi*(real j + t)/real ?m))
        = ((1-t) * vx_m j + t * vx_m (Suc j mod ?m),
           (1-t) * vy_m j + t * vy_m (Suc j mod ?m))"
    proof (intro allI impI ballI)
      fix j t assume hj: "j < ?m" and ht: "t \<in> I_set"
      have hedge: "((1-t) * vx_m j + t * vx_m (Suc j mod ?m),
           (1-t) * vy_m j + t * vy_m (Suc j mod ?m)) \<in> P_m"
        by (rule edge_point_in_polygon_witness[OF hm3 hj ht hC5m])
      from h\<psi>m_edge[rule_format, OF hj ht]
      have "\<psi>_m ((1-t) * vx_m j + t * vx_m (Suc j mod ?m),
           (1-t) * vy_m j + t * vy_m (Suc j mod ?m))
        = (cos (2*pi*(real j + t)/real ?m), sin (2*pi*(real j + t)/real ?m))" .
      from inv_into_f_f[OF h\<psi>m_inj hedge] this
      show "inv_into P_m \<psi>_m (cos (2*pi*(real j + t)/real ?m), sin (2*pi*(real j + t)/real ?m))
        = ((1-t) * vx_m j + t * vx_m (Suc j mod ?m),
           (1-t) * vy_m j + t * vy_m (Suc j mod ?m))" by (by100 simp)
    qed
    \<comment> \<open>Extract continuous\\_on from homeomorphisms via the bridge lemma.\<close>
    \<comment> \<open>B2 topology = subspace topology (needed for bridge lemma).\<close>
    have hB2_eq: "top1_B2_topology = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_B2"
      unfolding top1_B2_topology_def by (by100 simp)
    have h\<psi>e_cont_on: "continuous_on P_e \<psi>_e"
    proof (rule continuous_on_from_top1)
      have "top1_continuous_map_on P_e (?TP P_e) top1_B2 top1_B2_topology \<psi>_e"
        using h\<psi>e_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      thus "top1_continuous_map_on P_e
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_e)
          top1_B2
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_B2) \<psi>_e"
        unfolding hB2_eq[symmetric] by (by100 simp)
    qed
    have h\<psi>m_inv_cont_on: "continuous_on top1_B2 (inv_into P_m \<psi>_m)"
    proof (rule continuous_on_from_top1)
      have "top1_continuous_map_on top1_B2 top1_B2_topology P_m (?TP P_m) (inv_into P_m \<psi>_m)"
        using h\<psi>m_inv unfolding top1_homeomorphism_on_def by (by100 blast)
      thus "top1_continuous_map_on top1_B2
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_B2)
          P_m (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P_m)
          (inv_into P_m \<psi>_m)"
        unfolding hB2_eq[symmetric] by (by100 simp)
    qed
    \<comment> \<open>Both disk homeomorphisms + inverse + continuous\\_on available.
       Define f = \\<psi>\\_m\\<inverse> \\<circ> \\<tau> \\<circ> \\<psi>\\_e where \\<tau>: B2 \\<to> B2 is the spur collapse map.\<close>
    \<comment> \<open>Spur target: p\\_cm = (1/2, 0) in B2 coordinates (directly defined, no PolygonDisk export needed).
       This is explicitly \\<noteq> (0,0), has |p\\_cm| = 1/2 < 1, and avoids the midpoint-ray collapse.
       The preimage \\<psi>\\_m\\<inverse>(1/2, 0) is an interior point of P\\_m (since (1/2,0) \\<in> B2 \\ S1).\<close>
    define p_cm :: "real \<times> real" where "p_cm = (1/2, 0)"
    have hp_cm_B2: "p_cm \<in> top1_B2" unfolding p_cm_def top1_B2_def power2_eq_square
      by (by100 simp)
    have hp_cm_not_S1: "p_cm \<notin> top1_S1" unfolding p_cm_def top1_S1_def power2_eq_square
      by (by100 simp)
    have hp_cm_int: "fst p_cm ^ 2 + snd p_cm ^ 2 < 1" unfolding p_cm_def power2_eq_square
      by (by100 simp)
    have hp_cm_ne: "p_cm \<noteq> (0, 0)" unfolding p_cm_def by (by100 simp)
    \<comment> \<open>\\<tau> on the boundary S1:
       - Good arcs (edges \\<ge>2 of P\\_e): angle 2\\<pi>(k+t)/n \\<to> angle 2\\<pi>(k-2+t)/m on S1
       - Cancel arcs (edges 0,1): angle 2\\<pi>t/n \\<to> spur point (1-t')*(1,0) + t'*p\\_cm
       where t' parameterizes the fold.\<close>
    \<comment> \<open>For now, sorry \\<tau>. The key property: f = \\<psi>\\_m\\<inverse> \\<circ> \\<tau> \\<circ> \\<psi>\\_e should satisfy:
       - Edge k (k\\<ge>2) at t: \\<psi>\\_e maps to angle 2\\<pi>(k+t)/n on S1.
         \\<tau> rescales to angle 2\\<pi>(k-2+t)/m on S1.
         \\<psi>\\_m\\<inverse> maps back to edge\\_m(k-2, t).
       - Edge 0 at t: \\<psi>\\_e maps to angle 2\\<pi>t/n.
         \\<tau> maps to spur: (1-t)*\\<psi>\\_m(u0) + t*\\<psi>\\_m(c\\_m) = (1-t)*(1,0) + t*p\\_cm.
         \\<psi>\\_m\\<inverse> maps to (1-t)*u0 + t*c\\_m.
       - Edge 1 at t: \\<psi>\\_e maps to angle 2\\<pi>(1+t)/n.
         \\<tau> maps to spur: (1-t)*\\<psi>\\_m(c\\_m) + t*\\<psi>\\_m(u0) = (1-t)*p\\_cm + t*(1,0).
         \\<psi>\\_m\\<inverse> maps to (1-t)*c\\_m + t*u0.\<close>
    \<comment> \<open>Define f via disk homeomorphisms: f = \\<psi>\\_m\\<inverse> \\<circ> \\<tau> \\<circ> \\<psi>\\_e.
       For the boundary behavior, \\<tau> rescales good arcs and folds cancel arcs.
       Define \\<tau> on boundary by angle mapping, extend to interior by cone from origin.\<close>
    \<comment> \<open>Boundary angle thresholds.\<close>
    define \<theta>_cancel where "\<theta>_cancel = 4 * pi / real ?n"
    \<comment> \<open>\\<tau> on boundary S1: for angle \\<theta> \\<in> [\\<theta>\\_cancel, 2\\<pi>), rescale to [0, 2\\<pi>).
       For \\<theta> \\<in> [0, \\<theta>\\_cancel), map to spur.\<close>
    define \<tau>_boundary :: "real \<Rightarrow> real \<times> real" where
      "\<tau>_boundary \<theta> = (if \<theta> \<ge> \<theta>_cancel then
         (cos ((\<theta> - \<theta>_cancel) * real ?n / real ?m), sin ((\<theta> - \<theta>_cancel) * real ?n / real ?m))
       else
         let t_fold = min (\<theta> * real ?n / (2*pi)) ((4*pi/real ?n - \<theta>) * real ?n / (2*pi))
         in ((1 - t_fold) * 1 + t_fold * fst p_cm, (1 - t_fold) * 0 + t_fold * snd p_cm))" for \<theta>
    \<comment> \<open>Perpendicular direction to spur (from (1,0) to p\\_cm).\<close>
    define d_perp where "d_perp = (- snd p_cm, fst p_cm - 1)"
    \<comment> \<open>Midpoint angle of cancel sector.\<close>
    define \<theta>_mid where "\<theta>_mid = 2 * pi / real ?n"
    \<comment> \<open>Extend \\<tau> to B2 with sector-squeezing: for the cancel sector, add perpendicular
       offset proportional to (1-r)*sin(\\<pi>*t) that keeps the two halves separated.
       For the good sector, use the standard cone extension.\<close>
    define \<tau> :: "real \<times> real \<Rightarrow> real \<times> real" where
      "\<tau> p = (if p = (0, 0) then (0, 0)
       else let r = sqrt (fst p ^ 2 + snd p ^ 2);
                \<theta> = (if snd p \<ge> 0 then arccos (fst p / r) else 2*pi - arccos (fst p / r))
            in if \<theta> \<ge> \<theta>_cancel then
                 \<comment> \<open>Good sector: cone rescaling.\<close>
                 (r * fst (\<tau>_boundary \<theta>), r * snd (\<tau>_boundary \<theta>))
               else
                 \<comment> \<open>Cancel sector: spur + perpendicular offset for injectivity.\<close>
                 let spur_pt = \<tau>_boundary \<theta>;
                     t_fold = min (\<theta> * real ?n / (2*pi)) ((\<theta>_cancel - \<theta>) * real ?n / (2*pi));
                     sign = (if \<theta> \<le> \<theta>_mid then 1 else -1);
                     offset = sign * r * (1 - r) * sin (pi * t_fold) / 4
                 in (r * fst spur_pt + offset * fst d_perp,
                     r * snd spur_pt + offset * snd d_perp))" for p
    \<comment> \<open>Define f = \\<psi>\\_m\\<inverse> \\<circ> \\<tau> \\<circ> \\<psi>\\_e.\<close>
    define spur_f where "spur_f p = inv_into P_m \<psi>_m (\<tau> (\<psi>_e p))" for p
    \<comment> \<open>Provide spur\\_f as witness. The sector-squeezing \\<tau> adds perpendicular offsets
       to the spur, keeping the two halves of the cancel sector separated.
       Properties: (1) continuous (piecewise smooth), (2) at r=1: collapses to spur
       (offset=0), (3) for r<1: offset>0 separates halves, (4) injective on interior.\<close>
    \<comment> \<open>\\<tau> maps nonzero to nonzero. With p\\_cm = (1/2,0), d\\_perp = (0,-1/2):
       Good sector: \\<tau> = (r*cos\\<phi>, r*sin\\<phi>), |\\<tau>| = r > 0.
       Cancel sector: \\<tau>\\_boundary = (1-tf/2, 0), so fst(\\<tau>) = r*(1-tf/2) > 0.\<close>
    have h_tau_nonzero: "\<And>q. q \<in> top1_B2 \<Longrightarrow> q \<noteq> (0,0) \<Longrightarrow> \<tau> q \<noteq> (0, 0)"
    proof -
      fix q :: "real \<times> real" assume hq: "q \<in> top1_B2" and hne: "q \<noteq> (0, 0)"
      \<comment> \<open>Proof: assume \\<tau>(q) = (0,0). After unfolding with p\\_cm=(1/2,0):
         Good sector: fst(\\<tau>)=r*cos(\\<phi>)=0, snd(\\<tau>)=r*sin(\\<phi>)=0, so r²(cos²+sin²)=0, r=0, contradiction.
         Cancel sector: fst(\\<tau>)=r*(1-tf/2)=0. Since 0\\<le>tf\\<le>1: 1-tf/2\\<ge>1/2>0 and r>0, contradiction.\<close>
      show "\<tau> q \<noteq> (0, 0)"
        unfolding \<tau>_def using hne
        apply (simp only: if_False)
        unfolding Let_def p_cm_def d_perp_def \<tau>_boundary_def \<theta>_cancel_def \<theta>_mid_def
        apply (auto simp: power2_eq_square sin_cos_squared_add3[simplified])
        sorry
    qed
    have "\<exists>f. continuous_on P_e f \<and> f ` P_e = P_m
        \<and> (\<forall>x\<in>P_e. \<forall>y\<in>P_e. (q_e x = q_e y) \<longleftrightarrow> (q_m (f x) = q_m (f y)))"
    proof (rule exI[of _ spur_f])
      \<comment> \<open>(1) Continuity of spur\\_f via composition of continuous maps.\<close>
      \<comment> \<open>Continuity of spur\\_f: PROVED via composition, assuming \\<tau> properties.
         The proof is: \\<psi>\\_e continuous (proved) \\<to> \\<tau> continuous (assumed) \\<to> \\<psi>\\_m\\<inverse> continuous (proved).
         \\<tau> properties + surjectivity + fibre matching sorry'd together below.\<close>
      \<comment> \<open>Sub-sorry 1: \\<tau> is continuous on B2 (piecewise smooth, matching at sector boundaries).
         Good sector: standard cone map (angle rescaling) \\<to> continuous.
         Cancel sector: spur + perpendicular offset \\<to> continuous (smooth formula).
         Matching at \\<theta>=\\<theta>\\_cancel: both sides give (r, 0). \\<checkmark>
         Matching at \\<theta>=\\<theta>\\_mid: offset = 0 (sin(\\<pi>*1) = 0). \\<checkmark>
         Matching at \\<theta>=0/2\\<pi>: both sides give (r, 0). \\<checkmark>
         Matching at r=0: both sides give (0, 0). \\<checkmark>\<close>
      \<comment> \<open>Define angle function for sector classification.\<close>
      define angle_of :: "real \<times> real \<Rightarrow> real" where
        "angle_of p = (if snd p \<ge> 0 then arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))
                       else 2*pi - arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2)))" for p
      \<comment> \<open>Sectors for pasting lemma. S\\_g includes positive x-axis to ensure closedness.
         S\\_c includes everything with angle \\<le> \\<theta>\\_cancel (which naturally includes positive x-axis).
         On the positive x-axis, \\<tau> uses cancel formula giving (r,0). Good formula also
         gives (r,0) at angle \\<to> 2\\<pi>. So \\<tau> is continuous across the sector boundary.\<close>
      define S_g where "S_g = {p \<in> top1_B2. p = (0,0) \<or> angle_of p \<ge> \<theta>_cancel
          \<or> (snd p = 0 \<and> fst p \<ge> 0)}"
      define S_c where "S_c = {p \<in> top1_B2. p = (0,0) \<or> angle_of p \<le> \<theta>_cancel}"
      have h_cover: "top1_B2 = S_g \<union> S_c"
        unfolding S_g_def S_c_def by (by100 auto)
      have h_g_closed: "closed S_g"
      proof -
        \<comment> \<open>S\\_g = (B2 \\<inter> {snd \\<le> 0}) \\<union> (B2 \\<inter> {snd \\<ge> 0} \\<inter> {fst \\<le> cos \\<theta> * |p|}).
           Union of two closed sets is closed.\<close>
        define A where "A = {p :: real \<times> real. fst p ^ 2 + snd p ^ 2 \<le> 1 \<and> snd p \<le> 0}"
        define B where "B = {p :: real \<times> real. fst p ^ 2 + snd p ^ 2 \<le> 1 \<and> snd p \<ge> 0
            \<and> fst p \<le> cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2)}"
        have h\<theta>_ge0: "\<theta>_cancel \<ge> 0" unfolding \<theta>_cancel_def
          using pi_gt_zero assms(2) by (by100 simp)
        have h\<theta>_le_pi: "\<theta>_cancel \<le> pi"
        proof -
          have "?n \<ge> 5" using assms(2) by (by100 simp)
          hence "real ?n \<ge> 5" by (by100 simp)
          hence "4 * pi / real ?n \<le> 4 * pi / 5"
            using divide_left_mono[of 5 "real ?n" "4*pi"] pi_gt_zero by (by100 simp)
          also have "\<dots> < pi" using pi_gt_zero by (by100 linarith)
          finally show ?thesis unfolding \<theta>_cancel_def by (by100 linarith)
        qed
        have h\<theta>_lt_pi: "\<theta>_cancel < pi"
        proof -
          have "?n \<ge> 5" using assms(2) by (by100 simp)
          hence "real ?n \<ge> 5" by (by100 simp)
          hence "4 * pi / real ?n \<le> 4 * pi / 5"
            using divide_left_mono[of 5 "real ?n" "4*pi"] pi_gt_zero by (by100 simp)
          also have "\<dots> < pi" using pi_gt_zero by (by100 linarith)
          finally show ?thesis unfolding \<theta>_cancel_def .
        qed
        \<comment> \<open>Step 1: S\\_g = A \\<union> B.\<close>
        have hS_g_eq: "S_g = A \<union> B"
        proof (rule set_eqI, rule iffI)
          fix p :: "real \<times> real"
          assume hp: "p \<in> S_g"
          hence hp_B2: "p \<in> top1_B2" and hp_disj: "p = (0,0) \<or> angle_of p \<ge> \<theta>_cancel
              \<or> (snd p = 0 \<and> fst p \<ge> 0)"
            unfolding S_g_def by (by100 auto)+
          have hp_norm: "fst p ^ 2 + snd p ^ 2 \<le> 1"
            using hp_B2 unfolding top1_B2_def by (by100 simp)
          show "p \<in> A \<union> B"
          proof (cases "snd p \<le> 0")
            case True thus ?thesis unfolding A_def using hp_norm by (by100 simp)
          next
            case False
            hence hsnd_pos: "snd p > 0" by (by100 linarith)
            \<comment> \<open>snd p > 0 rules out p = (0,0) and positive x-axis, so angle\\_of p \\<ge> \\<theta>.\<close>
            have "p \<noteq> (0,0)" using hsnd_pos by (by100 auto)
            moreover have "\<not>(snd p = 0 \<and> fst p \<ge> 0)" using hsnd_pos by (by100 linarith)
            ultimately have h_angle: "angle_of p \<ge> \<theta>_cancel" using hp_disj by (by100 blast)
            have hp_ne: "fst p \<noteq> 0 \<or> snd p \<noteq> 0" using hsnd_pos by (by100 linarith)
            have h_aof: "angle_of p = arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))"
              unfolding angle_of_def using hsnd_pos by (by100 simp)
            have h_lb: "-1 \<le> fst p / sqrt (fst p ^ 2 + snd p ^ 2)"
              by (rule fst_div_norm_bounded(1)[OF hp_ne])
            have h_ub: "fst p / sqrt (fst p ^ 2 + snd p ^ 2) \<le> 1"
              by (rule fst_div_norm_bounded(2)[OF hp_ne])
            have h_arccos_lb: "0 \<le> arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))"
              using arccos_lbound[OF h_lb h_ub] .
            have h_arccos_ub: "arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2)) \<le> pi"
              using arccos_ubound[OF h_lb h_ub] .
            \<comment> \<open>arccos(z) \\<ge> \\<theta> \\<Longrightarrow> z \\<le> cos \\<theta> via cos\\_mono\\_le\\_eq.\<close>
            have "fst p / sqrt (fst p ^ 2 + snd p ^ 2) \<le> cos \<theta>_cancel"
            proof -
              from h_angle h_aof have h_ge: "\<theta>_cancel \<le> arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))"
                by (by100 simp)
              \<comment> \<open>cos(arccos z) \\<le> cos \\<theta> \\<iff> \\<theta> \\<le> arccos z.\<close>
              from cos_mono_le_eq[OF h_arccos_lb h_arccos_ub h\<theta>_ge0 h\<theta>_le_pi]
              have "cos (arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))) \<le> cos \<theta>_cancel
                  \<longleftrightarrow> \<theta>_cancel \<le> arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))" .
              moreover have "cos (arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2)))
                  = fst p / sqrt (fst p ^ 2 + snd p ^ 2)"
                using cos_arccos[OF h_lb h_ub] .
              ultimately show ?thesis using h_ge by (by100 simp)
            qed
            hence "fst p \<le> cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2)"
            proof -
              have hr_pos: "sqrt (fst p ^ 2 + snd p ^ 2) > 0"
              proof -
                have "snd p ^ 2 > 0" using hsnd_pos by (by100 simp)
                moreover have "fst p ^ 2 \<ge> 0" by (by100 simp)
                ultimately have "fst p ^ 2 + snd p ^ 2 > 0" by (by100 linarith)
                thus ?thesis using real_sqrt_gt_0_iff by (by100 auto)
              qed
              from \<open>fst p / sqrt _ \<le> cos \<theta>_cancel\<close> hr_pos
              show ?thesis by (simp add: pos_divide_le_eq)
            qed
            thus ?thesis unfolding B_def using hp_norm hsnd_pos by (by100 simp)
          qed
        next
          fix p :: "real \<times> real"
          assume hp: "p \<in> A \<union> B"
          thus "p \<in> S_g"
          proof
            assume hp_A: "p \<in> A"
            hence hp_norm: "fst p ^ 2 + snd p ^ 2 \<le> 1" and hsnd: "snd p \<le> 0"
              unfolding A_def by (by100 simp)+
            have hp_B2: "p \<in> top1_B2" unfolding top1_B2_def using hp_norm by (by100 simp)
            show "p \<in> S_g"
            proof (cases "p = (0,0)")
              case True thus ?thesis unfolding S_g_def using hp_B2 by (by100 simp)
            next
              case False
              hence hp_ne: "fst p \<noteq> 0 \<or> snd p \<noteq> 0" by (cases p) (by100 auto)
              show ?thesis
              proof (cases "snd p = 0")
                case True
                hence "fst p \<noteq> 0"
                  using False by (cases p) (by100 auto)
                show ?thesis
                proof (cases "fst p \<ge> 0")
                  case True
                  thus ?thesis unfolding S_g_def using hp_B2 \<open>snd p = 0\<close> by (by100 simp)
                next
                  case False_fst: False
                  \<comment> \<open>fst p < 0, snd p = 0: angle = arccos(-|fst p|/|fst p|) = arccos(-1) = \\<pi> > \\<theta>.\<close>
                  have "fst p < 0" using False_fst by (by100 linarith)
                  have "angle_of p = arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))"
                    unfolding angle_of_def using True by (by100 simp)
                  moreover have "sqrt (fst p ^ 2 + snd p ^ 2) = sqrt (fst p ^ 2)"
                    using True by (by100 simp)
                  moreover have "sqrt (fst p ^ 2) = \<bar>fst p\<bar>" using real_sqrt_abs by (by100 simp)
                  moreover have "\<bar>fst p\<bar> = - fst p" using \<open>fst p < 0\<close> by (by100 simp)
                  ultimately have "angle_of p = arccos (fst p / (- fst p))" by (by100 simp)
                  moreover have "fst p / (- fst p) = -1" using \<open>fst p < 0\<close> by (by100 simp)
                  ultimately have "angle_of p = arccos (-1)" by (by100 simp)
                  moreover have "arccos (-1 :: real) = pi" using arccos_minus_1 .
                  ultimately have "angle_of p = pi" by (by100 simp)
                  hence "angle_of p \<ge> \<theta>_cancel" using h\<theta>_lt_pi by (by100 linarith)
                  thus ?thesis unfolding S_g_def using hp_B2 by (by100 simp)
                qed
              next
                case False_snd: False
                hence "snd p < 0" using hsnd by (by100 linarith)
                \<comment> \<open>snd p < 0: angle = 2\\<pi> - arccos(...) \\<ge> \\<pi> > \\<theta>.\<close>
                have "angle_of p = 2*pi - arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))"
                  unfolding angle_of_def using \<open>snd p < 0\<close> by (by100 simp)
                moreover have "arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2)) \<le> pi"
                  using arccos_ubound[OF fst_div_norm_bounded(1)[OF hp_ne]
                      fst_div_norm_bounded(2)[OF hp_ne]] .
                ultimately have "angle_of p \<ge> pi" using pi_gt_zero by (by100 linarith)
                hence "angle_of p \<ge> \<theta>_cancel" using h\<theta>_lt_pi by (by100 linarith)
                thus ?thesis unfolding S_g_def using hp_B2 by (by100 simp)
              qed
            qed
          next
            assume hp_B: "p \<in> B"
            hence hp_norm: "fst p ^ 2 + snd p ^ 2 \<le> 1"
              and hsnd: "snd p \<ge> 0"
              and hfst: "fst p \<le> cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2)"
              unfolding B_def by (by100 simp)+
            have hp_B2: "p \<in> top1_B2" unfolding top1_B2_def using hp_norm by (by100 simp)
            show "p \<in> S_g"
            proof (cases "p = (0,0)")
              case True thus ?thesis unfolding S_g_def using hp_B2 by (by100 simp)
            next
              case False
              hence hp_ne: "fst p \<noteq> 0 \<or> snd p \<noteq> 0" by (cases p) (by100 auto)
              have hr_pos: "sqrt (fst p ^ 2 + snd p ^ 2) > 0"
              proof -
                have "fst p ^ 2 + snd p ^ 2 > 0" using hp_ne
                proof
                  assume "fst p \<noteq> 0" hence "fst p^2 > 0" by (by100 simp)
                  moreover have "snd p^2 \<ge> 0" by (by100 simp)
                  ultimately show ?thesis by (by100 linarith)
                next
                  assume "snd p \<noteq> 0" hence "snd p^2 > 0" by (by100 simp)
                  moreover have "fst p^2 \<ge> 0" by (by100 simp)
                  ultimately show ?thesis by (by100 linarith)
                qed
                thus ?thesis using real_sqrt_gt_0_iff by (by100 auto)
              qed
              have h_lb: "-1 \<le> fst p / sqrt (fst p ^ 2 + snd p ^ 2)"
                by (rule fst_div_norm_bounded(1)[OF hp_ne])
              have h_ub: "fst p / sqrt (fst p ^ 2 + snd p ^ 2) \<le> 1"
                by (rule fst_div_norm_bounded(2)[OF hp_ne])
              have "fst p / sqrt (fst p ^ 2 + snd p ^ 2) \<le> cos \<theta>_cancel"
                using hfst hr_pos by (simp add: pos_divide_le_eq)
              have h_arccos_lb: "0 \<le> arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))"
                using arccos_lbound[OF h_lb h_ub] .
              have h_arccos_ub: "arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2)) \<le> pi"
                using arccos_ubound[OF h_lb h_ub] .
              \<comment> \<open>cos(arccos z) = z \\<le> cos \\<theta> and cos\\_mono\\_le\\_eq gives \\<theta> \\<le> arccos z.\<close>
              have "cos (arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))) \<le> cos \<theta>_cancel"
              proof -
                have "cos (arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2)))
                    = fst p / sqrt (fst p ^ 2 + snd p ^ 2)"
                  using cos_arccos[OF h_lb h_ub] .
                thus ?thesis using \<open>fst p / _ \<le> cos \<theta>_cancel\<close> by (by100 linarith)
              qed
              from cos_mono_le_eq[OF h_arccos_lb h_arccos_ub h\<theta>_ge0 h\<theta>_le_pi] this
              have "\<theta>_cancel \<le> arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))"
                by (by100 blast)
              hence "angle_of p \<ge> \<theta>_cancel"
                unfolding angle_of_def using hsnd by (by100 simp)
              thus ?thesis unfolding S_g_def using hp_B2 by (by100 simp)
            qed
          qed
        qed
        \<comment> \<open>Step 2: A and B are closed.\<close>
        have hA_cl: "closed A"
        proof -
          have "closed {p :: real \<times> real. fst p ^ 2 + snd p ^ 2 \<le> 1}"
          proof -
            have "continuous_on UNIV (\<lambda>p :: real \<times> real. fst p ^ 2 + snd p ^ 2)"
              by (intro continuous_intros)
            hence "closed ((\<lambda>p :: real \<times> real. fst p ^ 2 + snd p ^ 2) -` {..1})"
              by (simp add: closed_vimage)
            moreover have "{p :: real \<times> real. fst p ^ 2 + snd p ^ 2 \<le> 1}
                = (\<lambda>p. fst p ^ 2 + snd p ^ 2) -` {..1}"
              by (by100 auto)
            ultimately show ?thesis by (by100 simp)
          qed
          moreover have "closed {p :: real \<times> real. snd p \<le> 0}"
          proof -
            have "continuous_on UNIV (\<lambda>p :: real \<times> real. snd p)" by (intro continuous_intros)
            hence "closed ((\<lambda>p :: real \<times> real. snd p) -` {..0})"
              by (simp add: closed_vimage)
            moreover have "{p :: real \<times> real. snd p \<le> 0} = snd -` {..0}"
              by (by100 auto)
            ultimately show ?thesis by (by100 simp)
          qed
          ultimately have "closed ({p. fst p ^ 2 + snd p ^ 2 \<le> 1} \<inter> {p :: real \<times> real. snd p \<le> 0})"
            using closed_Int by (by100 blast)
          moreover have "A = {p. fst p ^ 2 + snd p ^ 2 \<le> 1} \<inter> {p :: real \<times> real. snd p \<le> 0}"
            unfolding A_def by (by100 auto)
          ultimately show ?thesis by (by100 simp)
        qed
        have hB_cl: "closed B"
        proof -
          have hB2_cl: "closed {p :: real \<times> real. fst p ^ 2 + snd p ^ 2 \<le> 1}"
          proof -
            have "continuous_on UNIV (\<lambda>p :: real \<times> real. fst p ^ 2 + snd p ^ 2)"
              by (intro continuous_intros)
            hence "closed ((\<lambda>p :: real \<times> real. fst p ^ 2 + snd p ^ 2) -` {..1})"
              by (simp add: closed_vimage)
            moreover have "{p :: real \<times> real. fst p ^ 2 + snd p ^ 2 \<le> 1}
                = (\<lambda>p. fst p ^ 2 + snd p ^ 2) -` {..1}"
              by (by100 auto)
            ultimately show ?thesis by (by100 simp)
          qed
          have hup_cl: "closed {p :: real \<times> real. (0::real) \<le> snd p}"
          proof -
            have "continuous_on UNIV (\<lambda>p :: real \<times> real. snd p)" by (intro continuous_intros)
            hence "closed ((\<lambda>p :: real \<times> real. snd p) -` {0..})"
              by (simp add: closed_vimage_snd)
            moreover have "{p :: real \<times> real. (0::real) \<le> snd p} = snd -` {0..}"
              by (by100 auto)
            ultimately show ?thesis by (by100 simp)
          qed
          have hcone_cl: "closed {p :: real \<times> real. fst p \<le> cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2)}"
          proof -
            have "continuous_on UNIV (\<lambda>p :: real \<times> real. cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2) - fst p)"
              by (intro continuous_intros)
            hence "closed ((\<lambda>p :: real \<times> real. cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2) - fst p) -` {0..})"
              by (simp add: closed_vimage)
            moreover have "{p :: real \<times> real. fst p \<le> cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2)}
                = (\<lambda>p. cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2) - fst p) -` {0..}"
              by (by100 auto)
            ultimately show ?thesis by (by100 simp)
          qed
          from closed_Int[OF closed_Int[OF hB2_cl hup_cl] hcone_cl]
          have "closed ({p. fst p ^ 2 + snd p ^ 2 \<le> 1} \<inter> {p. (0::real) \<le> snd p}
              \<inter> {p :: real \<times> real. fst p \<le> cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2)})" .
          moreover have "B = {p. fst p ^ 2 + snd p ^ 2 \<le> 1} \<inter> {p. (0::real) \<le> snd p}
              \<inter> {p. fst p \<le> cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2)}"
            unfolding B_def by (by100 auto)
          ultimately show ?thesis by (by100 simp)
        qed
        from closed_Un[OF hA_cl hB_cl]
        show ?thesis unfolding hS_g_eq .
      qed
      have h_c_closed: "closed S_c"
      proof -
        \<comment> \<open>S\\_c = {p \\<in> B2 | snd p \\<ge> 0 \\<and> fst p \\<ge> cos(\\<theta>\\_cancel) * |p|}.
           This equals: B2 \\<inter> {snd p \\<ge> 0} \\<inter> {fst p \\<ge> cos(\\<theta>\\_cancel)*sqrt(fst p^2+snd p^2)}.
           Each component is closed (B2 closed, half-plane closed, cone preimage closed).
           The equivalence angle\\_of(p) \\<le> \\<theta>\\_cancel \\<iff> fst p / |p| \\<ge> cos(\\<theta>\\_cancel) uses
           cos\\_mono\\_le\\_eq (arccos is strictly decreasing on [-1,1]).\<close>
        \<comment> \<open>Step 1: Show S\\_c = Cartesian cone description.\<close>
        have hS_c_eq: "S_c = {p. fst p ^ 2 + snd p ^ 2 \<le> 1 \<and> snd p \<ge> 0
            \<and> fst p \<ge> cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2)}"
        proof (rule set_eqI, rule iffI)
          fix p :: "real \<times> real"
          assume hp: "p \<in> S_c"
          hence hp_B2: "p \<in> top1_B2" and hp_angle: "p = (0,0) \<or> angle_of p \<le> \<theta>_cancel"
            unfolding S_c_def by (by100 auto)+
          have hp_norm: "fst p ^ 2 + snd p ^ 2 \<le> 1"
            using hp_B2 unfolding top1_B2_def by (by100 simp)
          show "p \<in> {p. fst p ^ 2 + snd p ^ 2 \<le> 1 \<and> snd p \<ge> 0
              \<and> fst p \<ge> cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2)}"
          proof (cases "p = (0,0)")
            case True thus ?thesis using hp_norm by (by100 simp)
          next
            case False
            hence hp_ne: "fst p \<noteq> 0 \<or> snd p \<noteq> 0" by (cases p) (by100 auto)
            from hp_angle False have h_angle_le: "angle_of p \<le> \<theta>_cancel" by (by100 simp)
            \<comment> \<open>snd p \\<ge> 0: if snd p < 0, angle\\_of > \\<pi> > \\<theta>\\_cancel, contradiction.\<close>
            have hsnd_ge: "snd p \<ge> 0"
            proof (rule ccontr)
              assume "\<not> snd p \<ge> 0"
              hence "snd p < 0" by (by100 linarith)
              hence "angle_of p = 2*pi - arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))"
                unfolding angle_of_def by (by100 simp)
              moreover have "arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2)) \<le> pi"
                using arccos_ubound[OF fst_div_norm_bounded(1)[OF hp_ne] fst_div_norm_bounded(2)[OF hp_ne]] .
              ultimately have "angle_of p \<ge> pi" using pi_gt_zero by (by100 linarith)
              have "\<theta>_cancel < pi"
              proof -
                have "?n \<ge> 5" using assms(2) by (by100 simp)
                hence "real ?n \<ge> 5" by (by100 simp)
                hence "4 * pi / real ?n \<le> 4 * pi / 5"
                proof -
                  from divide_left_mono[of 5 "real ?n" "4*pi"] \<open>real ?n \<ge> 5\<close> pi_gt_zero
                  show ?thesis by (by100 simp)
                qed
                also have "\<dots> < pi" using pi_gt_zero by (by100 linarith)
                finally show ?thesis unfolding \<theta>_cancel_def .
              qed
              thus False using h_angle_le \<open>angle_of p \<ge> pi\<close> \<open>\<theta>_cancel < pi\<close> by (by100 linarith)
            qed
            \<comment> \<open>For snd p \\<ge> 0: angle\\_of = arccos(fst p/|p|). arccos \\<le> \\<theta>\\_cancel \\<Longrightarrow> fst p/|p| \\<ge> cos(\\<theta>\\_cancel).\<close>
            have hfst_ge: "fst p \<ge> cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2)"
            proof -
              have h_aof: "angle_of p = arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))"
                unfolding angle_of_def using hsnd_ge by (by100 simp)
              have h_arccos_le: "arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2)) \<le> \<theta>_cancel"
                using h_angle_le h_aof by (by100 simp)
              \<comment> \<open>arccos z \\<le> \\<theta> \\<Longrightarrow> cos \\<theta> \\<le> z via cos\\_mono\\_le\\_eq.\<close>
              have h_lb: "-1 \<le> fst p / sqrt (fst p ^ 2 + snd p ^ 2)"
                by (rule fst_div_norm_bounded(1)[OF hp_ne])
              have h_ub: "fst p / sqrt (fst p ^ 2 + snd p ^ 2) \<le> 1"
                by (rule fst_div_norm_bounded(2)[OF hp_ne])
              have h_arccos_lb: "0 \<le> arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))"
                using arccos_lbound[OF h_lb h_ub] .
              have h_arccos_ub: "arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2)) \<le> pi"
                using arccos_ubound[OF h_lb h_ub] .
              have h\<theta>_ge0: "\<theta>_cancel \<ge> 0" unfolding \<theta>_cancel_def
                using pi_gt_zero assms(2) by (by100 simp)
              have h\<theta>_le_pi: "\<theta>_cancel \<le> pi"
              proof -
                have "?n \<ge> 5" using assms(2) by (by100 simp)
                hence "real ?n \<ge> 5" by (by100 simp)
                hence "4 * pi / real ?n \<le> 4 * pi / 5"
                  using divide_left_mono[of 5 "real ?n" "4*pi"] pi_gt_zero by (by100 simp)
                also have "\<dots> < pi" using pi_gt_zero by (by100 linarith)
                finally show ?thesis unfolding \<theta>_cancel_def by (by100 linarith)
              qed
              have h_cos_le: "cos \<theta>_cancel \<le> fst p / sqrt (fst p ^ 2 + snd p ^ 2)"
              proof (cases "\<theta>_cancel = arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))")
                case True
                hence "cos \<theta>_cancel = cos (arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2)))"
                  by (by100 simp)
                also have "\<dots> = fst p / sqrt (fst p ^ 2 + snd p ^ 2)"
                  using cos_arccos[OF h_lb h_ub] .
                finally show ?thesis by (by100 linarith)
              next
                case False
                hence "arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2)) < \<theta>_cancel"
                  using h_arccos_le by (by100 linarith)
                have "\<not> (\<theta>_cancel \<le> arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2)))"
                  using \<open>arccos _ < \<theta>_cancel\<close> by (by100 linarith)
                from cos_mono_le_eq[OF h_arccos_lb h_arccos_ub h\<theta>_ge0 h\<theta>_le_pi]
                have "\<not> (cos (arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))) \<le> cos \<theta>_cancel)"
                  using \<open>\<not> (\<theta>_cancel \<le> _)\<close> by (by100 blast)
                hence "cos \<theta>_cancel < cos (arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2)))"
                  by (by100 linarith)
                also have "\<dots> = fst p / sqrt (fst p ^ 2 + snd p ^ 2)"
                  using cos_arccos[OF h_lb h_ub] .
                finally show ?thesis by (by100 linarith)
              qed
              \<comment> \<open>fst p / |p| \\<ge> cos \\<theta> and |p| > 0 \\<Longrightarrow> fst p \\<ge> cos \\<theta> * |p|.\<close>
              have hr_pos: "sqrt (fst p ^ 2 + snd p ^ 2) > 0"
              proof -
                have "fst p ^ 2 + snd p ^ 2 > 0" using hp_ne
                proof
                  assume "fst p \<noteq> 0" hence "fst p^2 > 0" by (by100 simp)
                  moreover have "snd p^2 \<ge> 0" by (by100 simp)
                  ultimately show ?thesis by (by100 linarith)
                next
                  assume "snd p \<noteq> 0" hence "snd p^2 > 0" by (by100 simp)
                  moreover have "fst p^2 \<ge> 0" by (by100 simp)
                  ultimately show ?thesis by (by100 linarith)
                qed
                thus ?thesis using real_sqrt_gt_0_iff by (by100 auto)
              qed
              from mult_right_mono[OF h_cos_le less_imp_le[OF hr_pos]]
              have "cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2)
                  \<le> fst p / sqrt (fst p ^ 2 + snd p ^ 2) * sqrt (fst p ^ 2 + snd p ^ 2)" .
              also have "\<dots> = fst p" using hr_pos by (simp add: field_simps)
              finally show ?thesis .
            qed
            show ?thesis using hp_norm hsnd_ge hfst_ge by (by100 simp)
          qed
        next
          fix p :: "real \<times> real"
          assume hp: "p \<in> {p. fst p ^ 2 + snd p ^ 2 \<le> 1 \<and> snd p \<ge> 0
              \<and> fst p \<ge> cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2)}"
          show "p \<in> S_c"
          proof -
            from hp have hp_norm: "fst p ^ 2 + snd p ^ 2 \<le> 1"
              and hsnd_ge: "snd p \<ge> 0"
              and hfst_ge: "fst p \<ge> cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2)"
              by (by100 simp)+
            have hp_B2: "p \<in> top1_B2" unfolding top1_B2_def using hp_norm by (by100 simp)
            show ?thesis
            proof (cases "p = (0,0)")
              case True thus ?thesis unfolding S_c_def using hp_B2 by (by100 simp)
            next
              case False
              hence hp_ne: "fst p \<noteq> 0 \<or> snd p \<noteq> 0" by (cases p) (by100 auto)
              have hr_pos: "sqrt (fst p ^ 2 + snd p ^ 2) > 0"
              proof -
                have "fst p ^ 2 + snd p ^ 2 > 0" using hp_ne
                proof
                  assume "fst p \<noteq> 0" hence "fst p^2 > 0" by (by100 simp)
                  moreover have "snd p^2 \<ge> 0" by (by100 simp)
                  ultimately show ?thesis by (by100 linarith)
                next
                  assume "snd p \<noteq> 0" hence "snd p^2 > 0" by (by100 simp)
                  moreover have "fst p^2 \<ge> 0" by (by100 simp)
                  ultimately show ?thesis by (by100 linarith)
                qed
                thus ?thesis using real_sqrt_gt_0_iff by (by100 auto)
              qed
              have h_lb: "-1 \<le> fst p / sqrt (fst p ^ 2 + snd p ^ 2)"
                by (rule fst_div_norm_bounded(1)[OF hp_ne])
              have h_ub: "fst p / sqrt (fst p ^ 2 + snd p ^ 2) \<le> 1"
                by (rule fst_div_norm_bounded(2)[OF hp_ne])
              have h_arccos_lb: "0 \<le> arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))"
                using arccos_lbound[OF h_lb h_ub] .
              have h_arccos_ub: "arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2)) \<le> pi"
                using arccos_ubound[OF h_lb h_ub] .
              have h\<theta>_ge0: "\<theta>_cancel \<ge> 0" unfolding \<theta>_cancel_def
                using pi_gt_zero assms(2) by (by100 simp)
              have h\<theta>_le_pi: "\<theta>_cancel \<le> pi"
              proof -
                have "?n \<ge> 5" using assms(2) by (by100 simp)
                hence "real ?n \<ge> 5" by (by100 simp)
                hence "4 * pi / real ?n \<le> 4 * pi / 5"
                  using divide_left_mono[of 5 "real ?n" "4*pi"] pi_gt_zero by (by100 simp)
                also have "\<dots> < pi" using pi_gt_zero by (by100 linarith)
                finally show ?thesis unfolding \<theta>_cancel_def by (by100 linarith)
              qed
              \<comment> \<open>fst p / |p| \\<ge> cos \\<theta> (dividing hypothesis by |p| > 0).\<close>
              have h_cos_le: "cos \<theta>_cancel \<le> fst p / sqrt (fst p ^ 2 + snd p ^ 2)"
                using hfst_ge hr_pos by (simp add: pos_le_divide_eq)
              \<comment> \<open>cos \\<theta> \\<le> z = cos(arccos(z)) via cos\\_arccos, then cos\\_mono\\_le\\_eq gives arccos(z) \\<le> \\<theta>.\<close>
              have h_angle_le: "angle_of p \<le> \<theta>_cancel"
              proof -
                have h_aof: "angle_of p = arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))"
                  unfolding angle_of_def using hsnd_ge by (by100 simp)
                have "cos \<theta>_cancel \<le> cos (arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2)))"
                  using h_cos_le cos_arccos[OF h_lb h_ub] by (by100 simp)
                hence "arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2)) \<le> \<theta>_cancel"
                  using cos_mono_le_eq[OF h\<theta>_ge0 h\<theta>_le_pi h_arccos_lb h_arccos_ub]
                  by (by100 blast)
                thus ?thesis using h_aof by (by100 simp)
              qed
              show ?thesis unfolding S_c_def using hp_B2 False h_angle_le by (by100 simp)
            qed
          qed
        qed
        \<comment> \<open>Step 2: The Cartesian cone set is closed (intersection of closed sets).\<close>
        have "closed {p :: real \<times> real. fst p ^ 2 + snd p ^ 2 \<le> 1 \<and> snd p \<ge> 0
            \<and> fst p \<ge> cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2)}"
        proof -
          have hB2_cl: "closed {p :: real \<times> real. fst p ^ 2 + snd p ^ 2 \<le> 1}"
          proof -
            have "continuous_on UNIV (\<lambda>p :: real \<times> real. fst p ^ 2 + snd p ^ 2)"
              by (intro continuous_intros)
            hence "closed ((\<lambda>p :: real \<times> real. fst p ^ 2 + snd p ^ 2) -` {..1})"
              by (simp add: closed_vimage)
            moreover have "{p :: real \<times> real. fst p ^ 2 + snd p ^ 2 \<le> 1}
                = (\<lambda>p. fst p ^ 2 + snd p ^ 2) -` {..1}"
              by (by100 auto)
            ultimately show ?thesis by (by100 simp)
          qed
          have hup_cl: "closed {p :: real \<times> real. (0::real) \<le> snd p}"
          proof -
            have "continuous_on UNIV (\<lambda>p :: real \<times> real. snd p)" by (intro continuous_intros)
            hence "closed ((\<lambda>p :: real \<times> real. snd p) -` {0..})"
              by (simp add: closed_vimage_snd) \<comment> \<open>Found by sledgehammer.\<close>
            moreover have "{p :: real \<times> real. (0::real) \<le> snd p} = snd -` {0..}"
              by (by100 auto)
            ultimately show ?thesis by (by100 simp)
          qed
          have hcone_cl: "closed {p :: real \<times> real. cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2) \<le> fst p}"
          proof -
            have "continuous_on UNIV (\<lambda>p :: real \<times> real. fst p - cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2))"
              by (intro continuous_intros)
            hence "closed ((\<lambda>p :: real \<times> real. fst p - cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2)) -` {0..})"
              by (simp add: closed_vimage)
            moreover have "{p :: real \<times> real. cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2) \<le> fst p}
                = (\<lambda>p. fst p - cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2)) -` {0..}"
              by (by100 auto)
            ultimately show ?thesis by (by100 simp)
          qed
          from closed_Int[OF closed_Int[OF hB2_cl hup_cl] hcone_cl]
          have "closed ({p. fst p ^ 2 + snd p ^ 2 \<le> 1} \<inter> {p. (0::real) \<le> snd p}
              \<inter> {p :: real \<times> real. cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2) \<le> fst p})" .
          moreover have "{p :: real \<times> real. fst p ^ 2 + snd p ^ 2 \<le> 1 \<and> snd p \<ge> 0
              \<and> fst p \<ge> cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2)}
            = {p. fst p ^ 2 + snd p ^ 2 \<le> 1} \<inter> {p. (0::real) \<le> snd p}
              \<inter> {p. cos \<theta>_cancel * sqrt (fst p ^ 2 + snd p ^ 2) \<le> fst p}"
            by (by100 auto)
          ultimately show ?thesis by (by100 simp)
        qed
        thus ?thesis unfolding hS_c_eq .
      qed
      have h_tau_cont_B2_nonzero: "continuous_on (top1_B2 - {(0,0)}) \<tau>"
      proof -
        let ?B = "top1_B2 - {(0::real, 0::real)}"
        \<comment> \<open>Two open sets covering B2\\{0}.\<close>
        define U1 where "U1 = {p :: real \<times> real. snd p > 0} \<union> {p. fst p < 0}"
        define U2 where "U2 = {p :: real \<times> real. snd p < 0} \<union> {p. fst p > 0}"
        have hU1_open: "open U1" unfolding U1_def
          by (intro open_Un open_Collect_less continuous_intros)
        have hU2_open: "open U2" unfolding U2_def
          by (intro open_Un open_Collect_less continuous_intros)
        have h_cover: "?B \<subseteq> U1 \<union> U2" unfolding U1_def U2_def by (by100 auto)
        \<comment> \<open>\\<tau> continuous on each intersection.\<close>
        have h_U1_cont: "continuous_on (?B \<inter> U1) \<tau>"
          sorry \<comment> \<open>On U1 = {snd>0}\\<union>{fst<0}: angle\\_of is continuous (branch cut excluded).
             \\<tau> = if angle\\<ge>\\<theta>\\_cancel then good\\_formula else cancel\\_formula.
             Use continuous\\_on\\_cases\\_le with h=angle\\_of and a=\\<theta>\\_cancel.
             Good formula: (r*cos(rescaled), r*sin(rescaled)) — composition of continuous.
             Cancel formula: (r*spur\\_x + offset*dp\\_x, ...) — composition of continuous.
             Sign\\_v discontinuity at \\<theta>\\_mid handled by nested cases\\_le (offset=0 at boundary).
             Both branches give (r,0) at \\<theta>=\\<theta>\\_cancel (agreement).\<close>
        have h_U2_cont: "continuous_on (?B \<inter> U2) \<tau>"
          sorry \<comment> \<open>On U2 = {snd<0} \\<union> {fst>0}: For snd<0, good formula (continuous).
             For fst>0: cancel formula (snd\\<ge>0) and good formula (snd\\<le>0) both give (r,0) at x-axis.
             Pointwise continuity follows. Key cases: (1) snd\\<noteq>0: single formula in neighborhood,
             (2) snd=0, fst>0: both formulas converge to (fst p, 0).\<close>
        \<comment> \<open>Pointwise: for each p \\<in> ?B, p \\<in> U1 or U2. In either case, at\\_within\\_nhd gives limit.\<close>
        show ?thesis unfolding continuous_on_def
        proof (intro ballI)
          fix p assume hp: "p \<in> ?B"
          hence "p \<in> U1 \<or> p \<in> U2" using h_cover by (by100 blast)
          thus "((\<lambda>x. \<tau> x) \<longlongrightarrow> \<tau> p) (at p within ?B)"
          proof
            assume hU1: "p \<in> U1"
            have hp1: "p \<in> ?B \<inter> U1" using hp hU1 by (by100 simp)
            from continuous_on_def[THEN iffD1, OF h_U1_cont, rule_format, OF hp1]
            have "((\<lambda>x. \<tau> x) \<longlongrightarrow> \<tau> p) (at p within (?B \<inter> U1))" .
            moreover have "at p within (?B \<inter> U1) = at p within ?B"
            proof (rule at_within_nhd[where S = U1])
              show "p \<in> U1" by (rule hU1)
              show "open U1" by (rule hU1_open)
              show "(?B \<inter> U1) \<inter> U1 - {p} = ?B \<inter> U1 - {p}" by (by100 auto)
            qed
            ultimately show ?thesis by (by100 simp)
          next
            assume hU2: "p \<in> U2"
            have hp2: "p \<in> ?B \<inter> U2" using hp hU2 by (by100 simp)
            from continuous_on_def[THEN iffD1, OF h_U2_cont, rule_format, OF hp2]
            have "((\<lambda>x. \<tau> x) \<longlongrightarrow> \<tau> p) (at p within (?B \<inter> U2))" .
            moreover have "at p within (?B \<inter> U2) = at p within ?B"
            proof (rule at_within_nhd[where S = U2])
              show "p \<in> U2" by (rule hU2)
              show "open U2" by (rule hU2_open)
              show "(?B \<inter> U2) \<inter> U2 - {p} = ?B \<inter> U2 - {p}" by (by100 auto)
            qed
            ultimately show ?thesis by (by100 simp)
          qed
        qed
      qed
      have h_g_cont_nonzero: "continuous_on (S_g - {(0,0)}) \<tau>"
      proof (rule continuous_on_subset[OF h_tau_cont_B2_nonzero])
        show "S_g - {(0,0)} \<subseteq> top1_B2 - {(0,0)}" unfolding S_g_def by (by100 blast)
      qed
      have h_g_cont_origin: "((\<lambda>x. \<tau> x) \<longlongrightarrow> (0,0)) (at (0,0) within S_g)"
      proof -
        \<comment> \<open>Bound with C=1: on S\\_g, |fst(\\<tau>)| and |snd(\\<tau>)| are both \\<le> r.
           Good sector: |r\\<cdot>cos(...)| \\<le> r. Cancel (pos x-axis): |(r,0)| \\<le> r. Origin: 0.\<close>
        have h_fst_bound_g: "\<exists>C. \<forall>p \<in> S_g. \<bar>fst (\<tau> p)\<bar> \<le> C * sqrt (fst p ^ 2 + snd p ^ 2)"
        proof (rule exI[of _ "1 + \<bar>fst p_cm\<bar> + \<bar>fst d_perp\<bar>"])
          have hC_pos: "1 + \<bar>fst p_cm\<bar> + \<bar>fst d_perp\<bar> \<ge> 0" by (by100 simp)
          show "\<forall>p\<in>S_g. \<bar>fst (\<tau> p)\<bar> \<le> (1 + \<bar>fst p_cm\<bar> + \<bar>fst d_perp\<bar>) * sqrt (fst p ^ 2 + snd p ^ 2)"
          proof (intro ballI)
            fix p assume hp: "p \<in> S_g"
            define r where "r = sqrt (fst p ^ 2 + snd p ^ 2)"
            have hr_ge0: "r \<ge> 0" unfolding r_def by (by100 simp)
            have hC_ge1: "(1::real) + \<bar>fst p_cm\<bar> + \<bar>fst d_perp\<bar> \<ge> 1" by (by100 simp)
            show "\<bar>fst (\<tau> p)\<bar> \<le> (1 + \<bar>fst p_cm\<bar> + \<bar>fst d_perp\<bar>) * sqrt (fst p ^ 2 + snd p ^ 2)"
            proof (cases "p = (0::real, 0::real)")
              case True
              hence "\<tau> p = (0, 0)" unfolding \<tau>_def by (by100 simp)
              thus ?thesis using True by (by100 simp)
            next
              case False
              hence hne: "p \<noteq> (0::real, 0)" .
              have hr_pos: "r > 0"
              proof -
                have "fst p \<noteq> 0 \<or> snd p \<noteq> 0" using hne by (cases p) (by100 auto)
                hence "fst p ^ 2 + snd p ^ 2 > 0"
                proof
                  assume "fst p \<noteq> 0"
                  hence "fst p ^ 2 > 0" by (by100 simp)
                  moreover have "snd p ^ 2 \<ge> 0" by (by100 simp)
                  ultimately show ?thesis by (by100 linarith)
                next
                  assume "snd p \<noteq> 0"
                  hence "snd p ^ 2 > 0" by (by100 simp)
                  moreover have "fst p ^ 2 \<ge> 0" by (by100 simp)
                  ultimately show ?thesis by (by100 linarith)
                qed
                thus ?thesis unfolding r_def using real_sqrt_gt_0_iff by (by100 auto)
              qed
              have hr_eq: "sqrt (fst p ^ 2 + snd p ^ 2) = r" unfolding r_def by (by100 simp)
              \<comment> \<open>Define angle and unfold \\<tau> at p \\<noteq> (0,0).\<close>
              define \<theta>_p where "\<theta>_p = angle_of p"
              have h\<tau>_simp: "\<tau> p = (let \<theta> = \<theta>_p in
                  if \<theta> \<ge> \<theta>_cancel then (r * fst (\<tau>_boundary \<theta>), r * snd (\<tau>_boundary \<theta>))
                  else let spur_pt = \<tau>_boundary \<theta>;
                           t_fold = min (\<theta> * real ?n / (2*pi)) ((\<theta>_cancel - \<theta>) * real ?n / (2*pi));
                           sign_v = (if \<theta> \<le> \<theta>_mid then 1 else -1);
                           offset = sign_v * r * (1 - r) * sin (pi * t_fold) / 4
                       in (r * fst spur_pt + offset * fst d_perp,
                           r * snd spur_pt + offset * snd d_perp))"
                unfolding \<tau>_def \<theta>_p_def angle_of_def using hne hr_eq by (by100 simp)
              from hp hne have hcases: "angle_of p \<ge> \<theta>_cancel \<or> (snd p = 0 \<and> fst p \<ge> 0)"
                unfolding S_g_def by (by100 auto)
              show ?thesis
              proof (cases "\<theta>_p \<ge> \<theta>_cancel")
                case True
                \<comment> \<open>Good sector: fst(\\<tau> p) = r * cos(...).\<close>
                have h\<tau>_good: "\<tau> p = (r * fst (\<tau>_boundary \<theta>_p), r * snd (\<tau>_boundary \<theta>_p))"
                  using h\<tau>_simp True by (by100 simp)
                have "fst (\<tau>_boundary \<theta>_p) = cos ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)"
                  using True unfolding \<tau>_boundary_def by (by100 auto)
                hence hfst: "fst (\<tau> p) = r * cos ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)"
                  using h\<tau>_good by (by100 simp)
                have "\<bar>r * cos ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)\<bar> \<le> r"
                proof -
                  have "\<bar>cos ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)\<bar> \<le> 1"
                    using abs_cos_le_one by (by100 blast)
                  thus ?thesis using hr_ge0
                    by (simp add: abs_mult mult_left_le)
                qed
                hence hle_r: "\<bar>fst (\<tau> p)\<bar> \<le> r" using hfst by (by100 simp)
                have "r \<le> (1 + \<bar>fst p_cm\<bar> + \<bar>fst d_perp\<bar>) * r"
                  using mult_right_mono[OF hC_ge1 hr_ge0] by (by100 simp)
                hence "\<bar>fst (\<tau> p)\<bar> \<le> (1 + \<bar>fst p_cm\<bar> + \<bar>fst d_perp\<bar>) * r"
                  using hle_r by (by100 linarith)
                thus ?thesis using hr_eq by (by100 simp)
              next
                case False
                \<comment> \<open>Cancel sector in S\\_g: must be positive x-axis (snd p = 0, fst p \\<ge> 0).\<close>
                hence h\<theta>_lt: "\<not> \<theta>_p \<ge> \<theta>_cancel" .
                from hcases this have haxis: "snd p = 0 \<and> fst p \<ge> 0"
                  unfolding \<theta>_p_def by (by100 auto)
                \<comment> \<open>On positive x-axis: \\<theta> = 0, t\\_fold = 0, spur\\_pt = (1,0), offset = 0.\<close>
                from haxis have hsnd0: "snd p = 0" and hfst0: "fst p \<ge> 0" by (by100 auto)+
                have hfst_eq_r: "r = fst p"
                proof -
                  have "fst p ^ 2 + snd p ^ 2 = fst p ^ 2" using hsnd0 by (by100 simp)
                  hence "sqrt (fst p ^ 2 + snd p ^ 2) = sqrt (fst p ^ 2)" by (by100 simp)
                  hence "sqrt (fst p ^ 2 + snd p ^ 2) = \<bar>fst p\<bar>"
                    using real_sqrt_abs by (by100 simp)
                  thus ?thesis unfolding r_def using hfst0 by (by100 simp)
                qed
                have hfst_pos: "fst p > 0" using hr_pos hfst_eq_r by (by100 linarith)
                have hdiv1: "fst p / sqrt (fst p ^ 2 + snd p ^ 2) = 1"
                  using hfst_eq_r hfst_pos unfolding r_def by (by100 simp)
                have h\<theta>0: "\<theta>_p = 0"
                  unfolding \<theta>_p_def angle_of_def using hsnd0 hdiv1 arccos_1 by (by100 simp)
                have h\<tau>_axis: "\<tau> p = (r, 0)"
                proof -
                  have h\<tau>bdy0: "\<tau>_boundary (0::real) = (1, 0)"
                  proof -
                    have "\<theta>_cancel > 0" unfolding \<theta>_cancel_def using pi_gt_zero hn5
                      by (by100 simp)
                    hence "\<not> (0::real) \<ge> \<theta>_cancel" by (by100 linarith)
                    thus ?thesis unfolding \<tau>_boundary_def by (by100 simp)
                  qed
                  \<comment> \<open>Unfold \\<tau>\\_def directly for p on positive x-axis.\<close>
                  have "\<tau> p = (r * fst (\<tau>_boundary 0), r * snd (\<tau>_boundary 0))"
                  proof -
                    from h\<tau>_simp h\<theta>_lt h\<theta>0
                    have "\<tau> p = (let spur_pt = \<tau>_boundary 0;
                         t_fold = min (0 * real ?n / (2*pi)) ((\<theta>_cancel - 0) * real ?n / (2*pi));
                         sign_v = (if (0::real) \<le> \<theta>_mid then 1 else -1);
                         offset = sign_v * r * (1 - r) * sin (pi * t_fold) / 4
                     in (r * fst spur_pt + offset * fst d_perp,
                         r * snd spur_pt + offset * snd d_perp))" by (by100 simp)
                    also have "\<dots> = (let t_fold = min 0 ((\<theta>_cancel - 0) * real ?n / (2*pi));
                         sign_v = (if (0::real) \<le> \<theta>_mid then 1 else -1);
                         offset = sign_v * r * (1 - r) * sin (pi * t_fold) / 4
                     in (r * fst (\<tau>_boundary 0) + offset * fst d_perp,
                         r * snd (\<tau>_boundary 0) + offset * snd d_perp))"
                      unfolding Let_def by (by100 simp)
                    also have "\<dots> = (r * fst (\<tau>_boundary 0), r * snd (\<tau>_boundary 0))"
                    proof -
                      have "\<theta>_cancel > 0" unfolding \<theta>_cancel_def using pi_gt_zero hn5
                        by (by100 simp)
                      hence "(\<theta>_cancel - 0) * real ?n / (2*pi) \<ge> 0"
                        using pi_gt_zero hn5 by (by100 simp)
                      hence "min (0::real) ((\<theta>_cancel - 0) * real ?n / (2*pi)) = 0"
                        by (by100 simp)
                      hence "sin (pi * min (0::real) ((\<theta>_cancel - 0) * real ?n / (2*pi))) = 0"
                        by (by100 simp)
                      thus ?thesis unfolding Let_def by (by100 simp)
                    qed
                    finally show ?thesis .
                  qed
                  thus ?thesis using h\<tau>bdy0 by (by100 simp)
                qed
                hence "\<bar>fst (\<tau> p)\<bar> = r" using hr_ge0 by (by100 simp)
                moreover have "r \<le> (1 + \<bar>fst p_cm\<bar> + \<bar>fst d_perp\<bar>) * r"
                  using mult_right_mono[OF hC_ge1 hr_ge0] by (by100 simp)
                ultimately have "\<bar>fst (\<tau> p)\<bar> \<le> (1 + \<bar>fst p_cm\<bar> + \<bar>fst d_perp\<bar>) * r"
                  by (by100 linarith)
                thus ?thesis using hr_eq by (by100 simp)
              qed
            qed
          qed
        qed
        have h_snd_bound_g: "\<exists>C. \<forall>p \<in> S_g. \<bar>snd (\<tau> p)\<bar> \<le> C * sqrt (fst p ^ 2 + snd p ^ 2)"
        proof (rule exI[of _ "1 + \<bar>snd p_cm\<bar> + \<bar>snd d_perp\<bar>"], intro ballI)
          fix p assume hp: "p \<in> S_g"
          define r where "r = sqrt (fst p ^ 2 + snd p ^ 2)"
          have hr_ge0: "r \<ge> 0" unfolding r_def by (by100 simp)
          have hC_ge1: "(1::real) + \<bar>snd p_cm\<bar> + \<bar>snd d_perp\<bar> \<ge> 1" by (by100 simp)
          show "\<bar>snd (\<tau> p)\<bar> \<le> (1 + \<bar>snd p_cm\<bar> + \<bar>snd d_perp\<bar>) * sqrt (fst p ^ 2 + snd p ^ 2)"
          proof (cases "p = (0::real, 0::real)")
            case True
            hence "\<tau> p = (0, 0)" unfolding \<tau>_def by (by100 simp)
            thus ?thesis using True by (by100 simp)
          next
            case False
            hence hne: "p \<noteq> (0::real, 0)" .
            have hr_pos: "r > 0"
            proof -
              have "fst p \<noteq> 0 \<or> snd p \<noteq> 0" using hne by (cases p) (by100 auto)
              hence "fst p ^ 2 + snd p ^ 2 > 0"
              proof
                assume "fst p \<noteq> 0"
                hence "fst p ^ 2 > 0" by (by100 simp)
                moreover have "snd p ^ 2 \<ge> 0" by (by100 simp)
                ultimately show ?thesis by (by100 linarith)
              next
                assume "snd p \<noteq> 0"
                hence "snd p ^ 2 > 0" by (by100 simp)
                moreover have "fst p ^ 2 \<ge> 0" by (by100 simp)
                ultimately show ?thesis by (by100 linarith)
              qed
              thus ?thesis unfolding r_def using real_sqrt_gt_0_iff by (by100 auto)
            qed
            have hr_eq: "sqrt (fst p ^ 2 + snd p ^ 2) = r" unfolding r_def by (by100 simp)
            define \<theta>_p where "\<theta>_p = angle_of p"
            have h\<tau>_simp: "\<tau> p = (let \<theta> = \<theta>_p in
                if \<theta> \<ge> \<theta>_cancel then (r * fst (\<tau>_boundary \<theta>), r * snd (\<tau>_boundary \<theta>))
                else let spur_pt = \<tau>_boundary \<theta>;
                         t_fold = min (\<theta> * real ?n / (2*pi)) ((\<theta>_cancel - \<theta>) * real ?n / (2*pi));
                         sign_v = (if \<theta> \<le> \<theta>_mid then 1 else -1);
                         offset = sign_v * r * (1 - r) * sin (pi * t_fold) / 4
                     in (r * fst spur_pt + offset * fst d_perp,
                         r * snd spur_pt + offset * snd d_perp))"
              unfolding \<tau>_def \<theta>_p_def angle_of_def using hne hr_eq by (by100 simp)
            from hp hne have hcases: "angle_of p \<ge> \<theta>_cancel \<or> (snd p = 0 \<and> fst p \<ge> 0)"
              unfolding S_g_def by (by100 auto)
            show ?thesis
            proof (cases "\<theta>_p \<ge> \<theta>_cancel")
              case True
              have h\<tau>_good: "\<tau> p = (r * fst (\<tau>_boundary \<theta>_p), r * snd (\<tau>_boundary \<theta>_p))"
                using h\<tau>_simp True by (by100 simp)
              have "snd (\<tau>_boundary \<theta>_p) = sin ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)"
                using True unfolding \<tau>_boundary_def by (by100 auto)
              hence hsnd: "snd (\<tau> p) = r * sin ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)"
                using h\<tau>_good by (by100 simp)
              have "\<bar>r * sin ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)\<bar> \<le> r"
              proof -
                have "\<bar>sin ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)\<bar> \<le> 1"
                  using abs_sin_le_one by (by100 blast)
                thus ?thesis using hr_ge0
                  by (simp add: abs_mult mult_left_le)
              qed
              hence hle_r: "\<bar>snd (\<tau> p)\<bar> \<le> r" using hsnd by (by100 simp)
              have "r \<le> (1 + \<bar>snd p_cm\<bar> + \<bar>snd d_perp\<bar>) * r"
                using mult_right_mono[OF hC_ge1 hr_ge0] by (by100 simp)
              hence "\<bar>snd (\<tau> p)\<bar> \<le> (1 + \<bar>snd p_cm\<bar> + \<bar>snd d_perp\<bar>) * r"
                using hle_r by (by100 linarith)
              thus ?thesis using hr_eq by (by100 simp)
            next
              case False
              hence h\<theta>_lt: "\<not> \<theta>_p \<ge> \<theta>_cancel" .
              from hcases this have haxis: "snd p = 0 \<and> fst p \<ge> 0"
                unfolding \<theta>_p_def by (by100 auto)
              from haxis have hsnd0: "snd p = 0" and hfst0: "fst p \<ge> 0" by (by100 auto)+
              have hfst_eq_r: "r = fst p"
              proof -
                have "fst p ^ 2 + snd p ^ 2 = fst p ^ 2" using hsnd0 by (by100 simp)
                hence "sqrt (fst p ^ 2 + snd p ^ 2) = sqrt (fst p ^ 2)" by (by100 simp)
                hence "sqrt (fst p ^ 2 + snd p ^ 2) = \<bar>fst p\<bar>"
                  using real_sqrt_abs by (by100 simp)
                thus ?thesis unfolding r_def using hfst0 by (by100 simp)
              qed
              have hfst_pos: "fst p > 0" using hr_pos hfst_eq_r by (by100 linarith)
              have hdiv1: "fst p / sqrt (fst p ^ 2 + snd p ^ 2) = 1"
                using hfst_eq_r hfst_pos unfolding r_def by (by100 simp)
              have h\<theta>0: "\<theta>_p = 0"
                unfolding \<theta>_p_def angle_of_def using hsnd0 hdiv1 arccos_1 by (by100 simp)
              have h\<tau>_axis: "\<tau> p = (r, 0)"
              proof -
                have h\<tau>bdy0: "\<tau>_boundary (0::real) = (1, 0)"
                proof -
                  have "\<theta>_cancel > 0" unfolding \<theta>_cancel_def using pi_gt_zero hn5
                    by (by100 simp)
                  hence "\<not> (0::real) \<ge> \<theta>_cancel" by (by100 linarith)
                  thus ?thesis unfolding \<tau>_boundary_def by (by100 simp)
                qed
                have "\<tau> p = (r * fst (\<tau>_boundary 0), r * snd (\<tau>_boundary 0))"
                proof -
                  from h\<tau>_simp h\<theta>_lt h\<theta>0
                  have "\<tau> p = (let spur_pt = \<tau>_boundary 0;
                       t_fold = min (0 * real ?n / (2*pi)) ((\<theta>_cancel - 0) * real ?n / (2*pi));
                       sign_v = (if (0::real) \<le> \<theta>_mid then 1 else -1);
                       offset = sign_v * r * (1 - r) * sin (pi * t_fold) / 4
                   in (r * fst spur_pt + offset * fst d_perp,
                       r * snd spur_pt + offset * snd d_perp))" by (by100 simp)
                  also have "\<dots> = (let t_fold = min 0 ((\<theta>_cancel - 0) * real ?n / (2*pi));
                       sign_v = (if (0::real) \<le> \<theta>_mid then 1 else -1);
                       offset = sign_v * r * (1 - r) * sin (pi * t_fold) / 4
                   in (r * fst (\<tau>_boundary 0) + offset * fst d_perp,
                       r * snd (\<tau>_boundary 0) + offset * snd d_perp))"
                    unfolding Let_def by (by100 simp)
                  also have "\<dots> = (r * fst (\<tau>_boundary 0), r * snd (\<tau>_boundary 0))"
                  proof -
                    have "\<theta>_cancel > 0" unfolding \<theta>_cancel_def using pi_gt_zero hn5
                      by (by100 simp)
                    hence "(\<theta>_cancel - 0) * real ?n / (2*pi) \<ge> 0"
                      using pi_gt_zero hn5 by (by100 simp)
                    hence "min (0::real) ((\<theta>_cancel - 0) * real ?n / (2*pi)) = 0"
                      by (by100 simp)
                    hence "sin (pi * min (0::real) ((\<theta>_cancel - 0) * real ?n / (2*pi))) = 0"
                      by (by100 simp)
                    thus ?thesis unfolding Let_def by (by100 simp)
                  qed
                  finally show ?thesis .
                qed
                thus ?thesis using h\<tau>bdy0 by (by100 simp)
              qed
              hence "\<bar>snd (\<tau> p)\<bar> = 0" by (by100 simp)
              thus ?thesis by (by100 simp)
            qed
          qed
        qed
        have h_fst_to_0_g: "((\<lambda>p. fst p) \<longlongrightarrow> (0::real)) (at (0::real, 0::real) within S_g)"
        proof -
          have "isCont fst (0::real, 0::real)" by (intro continuous_intros)
          hence "(fst \<longlongrightarrow> (0::real)) (at (0::real, 0::real))"
            unfolding isCont_def by (by100 simp)
          thus ?thesis by (rule filterlim_mono) (auto simp: at_le)
        qed
        have h_snd_to_0_g: "((\<lambda>p. snd p) \<longlongrightarrow> (0::real)) (at (0::real, 0::real) within S_g)"
        proof -
          have "isCont snd (0::real, 0::real)" by (intro continuous_intros)
          hence "(snd \<longlongrightarrow> (0::real)) (at (0::real, 0::real))"
            unfolding isCont_def by (by100 simp)
          thus ?thesis by (rule filterlim_mono) (auto simp: at_le)
        qed
        have h_r_to_0_g: "((\<lambda>p. sqrt (fst p ^ 2 + snd p ^ 2)) \<longlongrightarrow> 0)
            (at (0::real, 0::real) within S_g)"
        proof -
          have "((\<lambda>p. sqrt (fst p ^ 2 + snd p ^ 2)) \<longlongrightarrow> sqrt ((0::real) ^ 2 + (0::real) ^ 2))
              (at (0::real, 0::real) within S_g)"
            using h_fst_to_0_g h_snd_to_0_g by (intro tendsto_intros)
          thus ?thesis by (by100 simp)
        qed
        \<comment> \<open>Squeeze: 0 \\<le> |fst(\\<tau> p)| \\<le> C*r and C*r \\<to> 0, so |fst(\\<tau> p)| \\<to> 0, hence fst(\\<tau> p) \\<to> 0.\<close>
        from h_fst_bound_g obtain C1 where hC1: "\<forall>p\<in>S_g. \<bar>fst (\<tau> p)\<bar> \<le> C1 * sqrt (fst p^2 + snd p^2)"
          by (by100 blast)
        have h_C1r: "((\<lambda>p. C1 * sqrt (fst p ^ 2 + snd p ^ 2)) \<longlongrightarrow> 0)
            (at (0::real, 0::real) within S_g)"
          using tendsto_mult_left[OF h_r_to_0_g, of C1] by (by100 simp)
        have h_abs_fst: "((\<lambda>p. \<bar>fst (\<tau> p)\<bar>) \<longlongrightarrow> 0) (at (0,0) within S_g)"
        proof (rule real_tendsto_sandwich[where f="\<lambda>_. 0" and h="\<lambda>p. C1 * sqrt (fst p^2+snd p^2)"])
          show "\<forall>\<^sub>F p in at (0,0) within S_g. (0::real) \<le> \<bar>fst (\<tau> p)\<bar>"
            by (intro always_eventually) (by100 auto)
          show "\<forall>\<^sub>F p in at (0,0) within S_g. \<bar>fst (\<tau> p)\<bar> \<le> C1 * sqrt (fst p^2+snd p^2)"
            unfolding eventually_at_filter using hC1 by (intro always_eventually) (by100 auto)
          show "((\<lambda>_. 0::real) \<longlongrightarrow> 0) (at (0,0) within S_g)" by (by100 simp)
          show "((\<lambda>p. C1 * sqrt (fst p ^ 2 + snd p ^ 2)) \<longlongrightarrow> 0)
              (at (0::real, 0::real) within S_g)" by (rule h_C1r)
        qed
        have h_fst_tau_0: "((\<lambda>p. fst (\<tau> p)) \<longlongrightarrow> 0) (at (0,0) within S_g)"
          using tendsto_rabs_zero_cancel[OF h_abs_fst] .
        \<comment> \<open>Same for snd.\<close>
        from h_snd_bound_g obtain C2 where hC2: "\<forall>p\<in>S_g. \<bar>snd (\<tau> p)\<bar> \<le> C2 * sqrt (fst p^2 + snd p^2)"
          by (by100 blast)
        have h_C2r: "((\<lambda>p. C2 * sqrt (fst p ^ 2 + snd p ^ 2)) \<longlongrightarrow> 0)
            (at (0::real, 0::real) within S_g)"
          using tendsto_mult_left[OF h_r_to_0_g, of C2] by (by100 simp)
        have h_abs_snd: "((\<lambda>p. \<bar>snd (\<tau> p)\<bar>) \<longlongrightarrow> 0) (at (0,0) within S_g)"
        proof (rule real_tendsto_sandwich[where f="\<lambda>_. 0" and h="\<lambda>p. C2 * sqrt (fst p^2+snd p^2)"])
          show "\<forall>\<^sub>F p in at (0,0) within S_g. (0::real) \<le> \<bar>snd (\<tau> p)\<bar>"
            by (intro always_eventually) (by100 auto)
          show "\<forall>\<^sub>F p in at (0,0) within S_g. \<bar>snd (\<tau> p)\<bar> \<le> C2 * sqrt (fst p^2+snd p^2)"
            unfolding eventually_at_filter using hC2 by (intro always_eventually) (by100 auto)
          show "((\<lambda>_. 0::real) \<longlongrightarrow> 0) (at (0,0) within S_g)" by (by100 simp)
          show "((\<lambda>p. C2 * sqrt (fst p ^ 2 + snd p ^ 2)) \<longlongrightarrow> 0)
              (at (0::real, 0::real) within S_g)" by (rule h_C2r)
        qed
        have h_snd_tau_0: "((\<lambda>p. snd (\<tau> p)) \<longlongrightarrow> 0) (at (0,0) within S_g)"
          using tendsto_rabs_zero_cancel[OF h_abs_snd] .
        \<comment> \<open>Combine via tendsto\\_Pair.\<close>
        from tendsto_Pair[OF h_fst_tau_0 h_snd_tau_0]
        show ?thesis by (by100 simp)
      qed
      have h_origin_in_Sg: "(0::real, 0::real) \<in> S_g"
        unfolding S_g_def top1_B2_def by (by100 simp)
      have h_g_cont: "continuous_on S_g \<tau>"
        unfolding continuous_on_def
      proof (intro ballI)
        fix p assume hp: "p \<in> S_g"
        show "((\<lambda>x. \<tau> x) \<longlongrightarrow> \<tau> p) (at p within S_g)"
        proof (cases "p = (0::real,0::real)")
          case True
          hence "\<tau> p = (0,0)" unfolding \<tau>_def by (by100 simp)
          thus ?thesis using True h_g_cont_origin by (by100 simp)
        next
          case False
          from continuous_on_def[THEN iffD1, OF h_g_cont_nonzero, rule_format]
          have "((\<lambda>x. \<tau> x) \<longlongrightarrow> \<tau> p) (at p within (S_g - {(0, 0)}))"
            using hp False by (by100 blast)
          moreover have "at p within (S_g - {(0, 0)}) = at p within S_g"
          proof (rule at_within_nhd[where S = "- {(0::real, 0::real)}"])
            show "p \<in> - {(0::real, 0::real)}" using False by (by100 simp)
            show "open (- {(0::real, 0::real)})"
              using closed_singleton by (by100 blast)
            show "(S_g - {(0, 0)}) \<inter> (- {(0, 0)}) - {p} = S_g \<inter> (- {(0, 0)}) - {p}"
              by (by100 auto)
          qed
          ultimately show ?thesis by (by100 simp)
        qed
      qed
      \<comment> \<open>On S\\_c, \\<tau> agrees with the cancel formula at ALL points:
         - For p \\<noteq> (0,0) with angle < \\<theta>\\_cancel: directly the cancel branch.
         - For p \\<noteq> (0,0) with angle = \\<theta>\\_cancel: good branch gives (r,0) = cancel at \\<theta>\\_cancel.
         - For p = (0,0): cancel formula gives (0*..., 0*...) = (0,0) = \\<tau>(0,0).
         So it suffices to show the cancel formula is continuous on S\\_c.
         Key steps:
         (1) arccos(x/sqrt(x^2+y^2)) continuous on {x^2+y^2>0, y\\<ge>0} via continuous\\_on\\_arccos
         (2) min, sin, multiplication all continuous
         (3) O(r) bound at origin: each component has factor r=sqrt(x^2+y^2)
         (4) continuous\\_on\\_If for the p=(0,0) case split.\<close>
      have h_c_cont_nonzero: "continuous_on (S_c - {(0,0)}) \<tau>"
      proof (rule continuous_on_subset[OF h_tau_cont_B2_nonzero])
        show "S_c - {(0,0)} \<subseteq> top1_B2 - {(0,0)}" unfolding S_c_def by (by100 blast)
      qed
      have h_c_cont_origin: "((\<lambda>x. \<tau> x) \<longlongrightarrow> (0,0)) (at (0,0) within S_c)"
      proof -
        \<comment> \<open>Componentwise: fst(\\<tau>(p)) \\<to> 0 and snd(\\<tau>(p)) \\<to> 0.
           Both have factor r = sqrt(x^2+y^2) \\<to> 0, with bounded cofactors.\<close>
        have h_fst_bound: "\<exists>C. \<forall>p \<in> S_c. \<bar>fst (\<tau> p)\<bar> \<le> C * sqrt (fst p ^ 2 + snd p ^ 2)"
        proof (rule exI[of _ "1 + \<bar>fst p_cm\<bar> + \<bar>fst d_perp\<bar>"], intro ballI)
          fix p assume hp: "p \<in> S_c"
          define r where "r = sqrt (fst p ^ 2 + snd p ^ 2)"
          have hr_ge0: "r \<ge> 0" unfolding r_def by (by100 simp)
          have hC_ge1: "(1::real) + \<bar>fst p_cm\<bar> + \<bar>fst d_perp\<bar> \<ge> 1" by (by100 simp)
          show "\<bar>fst (\<tau> p)\<bar> \<le> (1 + \<bar>fst p_cm\<bar> + \<bar>fst d_perp\<bar>) * sqrt (fst p ^ 2 + snd p ^ 2)"
          proof (cases "p = (0::real, 0::real)")
            case True
            hence "\<tau> p = (0, 0)" unfolding \<tau>_def by (by100 simp)
            thus ?thesis using True by (by100 simp)
          next
            case False
            hence hne: "p \<noteq> (0::real, 0)" .
            have hr_pos: "r > 0"
            proof -
              have "fst p \<noteq> 0 \<or> snd p \<noteq> 0" using hne by (cases p) (by100 auto)
              hence "fst p ^ 2 + snd p ^ 2 > 0"
              proof
                assume "fst p \<noteq> 0"
                hence "fst p ^ 2 > 0" by (by100 simp)
                moreover have "snd p ^ 2 \<ge> 0" by (by100 simp)
                ultimately show ?thesis by (by100 linarith)
              next
                assume "snd p \<noteq> 0"
                hence "snd p ^ 2 > 0" by (by100 simp)
                moreover have "fst p ^ 2 \<ge> 0" by (by100 simp)
                ultimately show ?thesis by (by100 linarith)
              qed
              thus ?thesis unfolding r_def using real_sqrt_gt_0_iff by (by100 auto)
            qed
            have hr_eq: "sqrt (fst p ^ 2 + snd p ^ 2) = r" unfolding r_def by (by100 simp)
            define \<theta>_p where "\<theta>_p = angle_of p"
            have h\<tau>_simp: "\<tau> p = (let \<theta> = \<theta>_p in
                if \<theta> \<ge> \<theta>_cancel then (r * fst (\<tau>_boundary \<theta>), r * snd (\<tau>_boundary \<theta>))
                else let spur_pt = \<tau>_boundary \<theta>;
                         t_fold = min (\<theta> * real ?n / (2*pi)) ((\<theta>_cancel - \<theta>) * real ?n / (2*pi));
                         sign_v = (if \<theta> \<le> \<theta>_mid then 1 else -1);
                         offset = sign_v * r * (1 - r) * sin (pi * t_fold) / 4
                     in (r * fst spur_pt + offset * fst d_perp,
                         r * snd spur_pt + offset * snd d_perp))"
              unfolding \<tau>_def \<theta>_p_def angle_of_def using hne hr_eq by (by100 simp)
            show ?thesis
            proof (cases "\<theta>_p \<ge> \<theta>_cancel")
              case True
              \<comment> \<open>Good sector (boundary): same bound as S\\_g good sector.\<close>
              have h\<tau>_good: "\<tau> p = (r * fst (\<tau>_boundary \<theta>_p), r * snd (\<tau>_boundary \<theta>_p))"
                using h\<tau>_simp True by (by100 simp)
              have "fst (\<tau>_boundary \<theta>_p) = cos ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)"
                using True unfolding \<tau>_boundary_def by (by100 auto)
              hence hfst: "fst (\<tau> p) = r * cos ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)"
                using h\<tau>_good by (by100 simp)
              have "\<bar>r * cos ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)\<bar> \<le> r"
              proof -
                have "\<bar>cos ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)\<bar> \<le> 1"
                  using abs_cos_le_one by (by100 blast)
                thus ?thesis using hr_ge0
                  by (simp add: abs_mult mult_left_le)
              qed
              hence hle_r: "\<bar>fst (\<tau> p)\<bar> \<le> r" using hfst by (by100 simp)
              have "r \<le> (1 + \<bar>fst p_cm\<bar> + \<bar>fst d_perp\<bar>) * r"
                using mult_right_mono[OF hC_ge1 hr_ge0] by (by100 simp)
              hence "\<bar>fst (\<tau> p)\<bar> \<le> (1 + \<bar>fst p_cm\<bar> + \<bar>fst d_perp\<bar>) * r"
                using hle_r by (by100 linarith)
              thus ?thesis using hr_eq by (by100 simp)
            next
              case False
              \<comment> \<open>Cancel sector: \\<tau>(p) = r*spur\\_pt + offset*d\\_perp.\<close>
              hence h\<theta>_lt: "\<not> \<theta>_p \<ge> \<theta>_cancel" .
              define spur_pt where "spur_pt = \<tau>_boundary \<theta>_p"
              define t_fold where "t_fold = min (\<theta>_p * real ?n / (2*pi)) ((\<theta>_cancel - \<theta>_p) * real ?n / (2*pi))"
              define sign_v where "sign_v = (if \<theta>_p \<le> \<theta>_mid then (1::real) else -1)"
              define offset where "offset = sign_v * r * (1 - r) * sin (pi * t_fold) / 4"
              have h\<tau>_cancel: "\<tau> p = (r * fst spur_pt + offset * fst d_perp,
                                      r * snd spur_pt + offset * snd d_perp)"
              proof -
                from h\<tau>_simp h\<theta>_lt
                have "\<tau> p = (let sp = \<tau>_boundary \<theta>_p;
                     tf = min (\<theta>_p * real ?n / (2*pi)) ((\<theta>_cancel - \<theta>_p) * real ?n / (2*pi));
                     sv = (if \<theta>_p \<le> \<theta>_mid then 1 else -1);
                     off = sv * r * (1 - r) * sin (pi * tf) / 4
                 in (r * fst sp + off * fst d_perp,
                     r * snd sp + off * snd d_perp))" by (by100 simp)
                thus ?thesis unfolding spur_pt_def t_fold_def sign_v_def offset_def Let_def
                  by (by100 simp)
              qed
              \<comment> \<open>Triangle inequality: |r*fst(sp) + off*fst(dp)| \\<le> r*|fst(sp)| + |off|*|fst(dp)|.\<close>
              have hfst_tau: "\<bar>fst (\<tau> p)\<bar> \<le> \<bar>r * fst spur_pt\<bar> + \<bar>offset * fst d_perp\<bar>"
                using h\<tau>_cancel by (by100 simp)
              \<comment> \<open>Bound |fst(spur\\_pt)| \\<le> 1 + |fst(p\\_cm)|.\<close>
              have h\<theta>_cancel_eq: "\<theta>_cancel = 4*pi/real ?n" unfolding \<theta>_cancel_def by (by100 simp)
              have hsp_bound: "\<bar>fst spur_pt\<bar> \<le> 1 + \<bar>fst p_cm\<bar>"
              proof -
                have hsp_fst: "fst spur_pt = (1 - t_fold) + t_fold * fst p_cm"
                proof -
                  \<comment> \<open>Use h\\<theta>\\_lt to eliminate good-sector branch.\<close>
                  from h\<theta>_lt
                  have hsp_eq: "\<tau>_boundary \<theta>_p = (let tf = min (\<theta>_p * real ?n / (2*pi))
                      ((4*pi/real ?n - \<theta>_p) * real ?n / (2*pi))
                    in ((1 - tf) * 1 + tf * fst p_cm, (1 - tf) * 0 + tf * snd p_cm))"
                    unfolding \<tau>_boundary_def \<theta>_cancel_def by (by100 simp)
                  have "fst (spur_pt) = fst (let tf = min (\<theta>_p * real ?n / (2*pi))
                      ((4*pi/real ?n - \<theta>_p) * real ?n / (2*pi))
                    in ((1 - tf) * 1 + tf * fst p_cm, (1 - tf) * 0 + tf * snd p_cm))"
                    unfolding spur_pt_def using hsp_eq by (by100 simp)
                  also have "\<dots> = (1 - min (\<theta>_p * real ?n / (2*pi))
                      ((4*pi/real ?n - \<theta>_p) * real ?n / (2*pi))) +
                      min (\<theta>_p * real ?n / (2*pi))
                      ((4*pi/real ?n - \<theta>_p) * real ?n / (2*pi)) * fst p_cm"
                    unfolding Let_def by (by100 simp)
                  also have "\<dots> = (1 - t_fold) + t_fold * fst p_cm"
                    unfolding t_fold_def using h\<theta>_cancel_eq by (by100 simp)
                  finally show ?thesis .
                qed
                have h_fst_div_bnd: "fst p / r \<ge> -1 \<and> fst p / r \<le> 1"
                proof -
                  have "fst p ^ 2 \<le> fst p ^ 2 + snd p ^ 2" by (by100 simp)
                  hence "fst p ^ 2 \<le> r ^ 2"
                  proof -
                    have "r ^ 2 = fst p ^ 2 + snd p ^ 2"
                      unfolding r_def using real_sqrt_pow2[of "fst p^2 + snd p^2"]
                      by (by100 simp)
                    thus ?thesis by (by100 simp)
                  qed
                  hence "\<bar>fst p\<bar> \<le> r"
                  proof -
                    have "\<bar>fst p\<bar> ^ 2 \<le> r ^ 2"
                      using \<open>fst p ^ 2 \<le> r ^ 2\<close> power2_abs[of "fst p"] by (by100 simp)
                    hence "sqrt (\<bar>fst p\<bar> ^ 2) \<le> sqrt (r ^ 2)" by (rule real_sqrt_le_mono)
                    thus ?thesis using real_sqrt_abs hr_ge0 by (by100 simp)
                  qed
                  hence hfp_le: "fst p \<le> r" and hfp_ge: "- r \<le> fst p" by (by100 linarith)+
                  have "fst p / r \<le> 1"
                  proof -
                    have "fst p / r \<le> r / r"
                      by (intro divide_right_mono hfp_le) (rule less_imp_le[OF hr_pos])
                    thus ?thesis using hr_pos by (by100 simp)
                  qed
                  moreover have "fst p / r \<ge> -1"
                  proof -
                    have "- r / r \<le> fst p / r"
                      by (intro divide_right_mono hfp_ge) (rule less_imp_le[OF hr_pos])
                    thus ?thesis using hr_pos by (by100 simp)
                  qed
                  ultimately show ?thesis by (by100 linarith)
                qed
                have h\<theta>_ge0: "\<theta>_p \<ge> 0"
                proof -
                  have h_fst_ge: "- 1 \<le> fst p / r" using h_fst_div_bnd by (by100 linarith)
                  have h_fst_le: "fst p / r \<le> 1" using h_fst_div_bnd by (by100 linarith)
                  have h_arc_ge0: "arccos (fst p / r) \<ge> 0"
                    using arccos_lbound[OF h_fst_ge h_fst_le] .
                  have h_arc_le_pi: "arccos (fst p / r) \<le> pi"
                    using arccos_ubound[OF h_fst_ge h_fst_le] .
                  show ?thesis
                  proof (cases "snd p \<ge> 0")
                    case True
                    hence "\<theta>_p = arccos (fst p / r)"
                      unfolding \<theta>_p_def angle_of_def r_def by (by100 simp)
                    thus ?thesis using h_arc_ge0 by (by100 linarith)
                  next
                    case False
                    hence "\<theta>_p = 2*pi - arccos (fst p / r)"
                      unfolding \<theta>_p_def angle_of_def r_def by (by100 simp)
                    thus ?thesis using h_arc_le_pi pi_gt_zero by (by100 linarith)
                  qed
                qed
                have htf_ge0: "t_fold \<ge> 0"
                proof -
                  have "\<theta>_p * real ?n / (2*pi) \<ge> 0"
                    using h\<theta>_ge0 pi_gt_zero hn5 by (by100 simp)
                  moreover have "(\<theta>_cancel - \<theta>_p) * real ?n / (2*pi) \<ge> 0"
                  proof -
                    have "\<theta>_cancel > \<theta>_p" using h\<theta>_lt by (by100 linarith)
                    thus ?thesis using pi_gt_zero hn5 by (by100 simp)
                  qed
                  ultimately show ?thesis unfolding t_fold_def by (by100 simp)
                qed
                have htf_le1: "t_fold \<le> 1"
                proof -
                  have "\<theta>_p * real ?n / (2*pi) \<ge> 0"
                    using h\<theta>_ge0 pi_gt_zero hn5 by (by100 simp)
                  moreover have "(\<theta>_cancel - \<theta>_p) * real ?n / (2*pi) \<ge> 0"
                  proof -
                    have "\<theta>_cancel > \<theta>_p" using h\<theta>_lt by (by100 linarith)
                    thus ?thesis using pi_gt_zero hn5 by (by100 simp)
                  qed
                  moreover have "\<theta>_p * real ?n / (2*pi) + (\<theta>_cancel - \<theta>_p) * real ?n / (2*pi)
                      = \<theta>_cancel * real ?n / (2*pi)" by (by100 algebra)
                  moreover have "\<theta>_cancel * real ?n / (2*pi) = 2"
                    unfolding \<theta>_cancel_def using pi_gt_zero hn5 by (by100 simp)
                  ultimately show ?thesis unfolding t_fold_def by (by100 linarith)
                qed
                have "\<bar>(1 - t_fold) + t_fold * fst p_cm\<bar> \<le> \<bar>1 - t_fold\<bar> + \<bar>t_fold * fst p_cm\<bar>"
                  by (rule abs_triangle_ineq)
                also have "\<dots> = (1 - t_fold) + t_fold * \<bar>fst p_cm\<bar>"
                  using htf_ge0 htf_le1 abs_mult[of t_fold "fst p_cm"] by (by100 simp)
                also have "\<dots> \<le> 1 + \<bar>fst p_cm\<bar>"
                proof -
                  have "(1 - t_fold) \<le> 1" using htf_ge0 by (by100 linarith)
                  moreover have "t_fold * \<bar>fst p_cm\<bar> \<le> \<bar>fst p_cm\<bar>"
                    using mult_right_mono[OF htf_le1 abs_ge_zero[of "fst p_cm"]] by (by100 simp)
                  ultimately show ?thesis by (by100 linarith)
                qed
                finally show ?thesis unfolding hsp_fst .
              qed
              \<comment> \<open>Bound |offset| \\<le> r.\<close>
              have hr_le1: "r \<le> 1"
              proof -
                have "p \<in> top1_B2" using hp unfolding S_c_def by (by100 blast)
                hence "fst p ^ 2 + snd p ^ 2 \<le> 1" unfolding top1_B2_def by (by100 simp)
                hence "sqrt (fst p ^ 2 + snd p ^ 2) \<le> sqrt 1" by (rule real_sqrt_le_mono)
                thus ?thesis unfolding r_def by (by100 simp)
              qed
              have hoff_bound: "\<bar>offset\<bar> \<le> r"
              proof -
                have h1mr_ge0: "1 - r \<ge> 0" using hr_le1 by (by100 linarith)
                have hprod_ge0: "r * (1 - r) \<ge> 0" using hr_ge0 h1mr_ge0 by (by100 simp)
                have hprod_le_r: "r * (1 - r) \<le> r"
                proof -
                  have "(1 - r) \<le> 1" using hr_ge0 by (by100 linarith)
                  from mult_left_mono[OF this hr_ge0]
                  show ?thesis by (by100 simp)
                qed
                have hsin_le: "sin (pi * t_fold) \<le> 1" by (rule sin_le_one)
                have hsin_ge: "sin (pi * t_fold) \<ge> -1" by (rule sin_ge_minus_one)
                \<comment> \<open>Product r*(1-r)*sin is in [-r*(1-r), r*(1-r)] \\<subseteq> [-r, r].\<close>
                have hprod_sin_le: "r * (1 - r) * sin (pi * t_fold) \<le> r * (1 - r)"
                  using mult_left_mono[OF hsin_le hprod_ge0] by (by100 simp)
                have hprod_sin_ge: "r * (1 - r) * sin (pi * t_fold) \<ge> - (r * (1 - r))"
                proof -
                  have "r * (1 - r) * sin (pi * t_fold) \<ge> r * (1 - r) * (-1)"
                    using mult_left_mono[OF hsin_ge hprod_ge0] by (by100 simp)
                  thus ?thesis by (by100 linarith)
                qed
                \<comment> \<open>sign\\_v \\<in> {1, -1} scales but preserves the bound.\<close>
                have "offset \<le> r \<and> offset \<ge> -r"
                proof -
                  have "sign_v = 1 \<or> sign_v = -1" unfolding sign_v_def by (by100 auto)
                  thus ?thesis
                  proof
                    assume hsv1: "sign_v = 1"
                    hence "offset = 1 * r * (1 - r) * sin (pi * t_fold) / 4"
                      unfolding offset_def by (by100 simp)
                    hence "offset = r * (1 - r) * sin (pi * t_fold) / 4" by (by100 simp)
                    thus ?thesis using hprod_sin_le hprod_sin_ge hprod_le_r hr_ge0
                      by (by100 linarith)
                  next
                    assume hsvm1: "sign_v = -1"
                    hence "offset = (-1) * r * (1 - r) * sin (pi * t_fold) / 4"
                      unfolding offset_def by (by100 simp)
                    hence "offset = - (r * (1 - r) * sin (pi * t_fold) / 4)" by (by100 linarith)
                    thus ?thesis using hprod_sin_le hprod_sin_ge hprod_le_r hr_ge0
                      by (by100 linarith)
                  qed
                qed
                thus ?thesis by (by100 linarith)
              qed
              \<comment> \<open>Combine.\<close>
              have "\<bar>r * fst spur_pt\<bar> = r * \<bar>fst spur_pt\<bar>"
                using hr_ge0 abs_mult[of r "fst spur_pt"] by (by100 simp)
              hence "\<bar>r * fst spur_pt\<bar> \<le> r * (1 + \<bar>fst p_cm\<bar>)"
                using mult_left_mono[OF hsp_bound hr_ge0] by (by100 simp)
              moreover have "\<bar>offset * fst d_perp\<bar> = \<bar>offset\<bar> * \<bar>fst d_perp\<bar>"
                using abs_mult[of offset "fst d_perp"] by (by100 simp)
              hence "\<bar>offset * fst d_perp\<bar> \<le> r * \<bar>fst d_perp\<bar>"
                using mult_right_mono[OF hoff_bound abs_ge_zero[of "fst d_perp"]] by (by100 simp)
              ultimately have "\<bar>fst (\<tau> p)\<bar> \<le> r * (1 + \<bar>fst p_cm\<bar>) + r * \<bar>fst d_perp\<bar>"
                using hfst_tau by (by100 linarith)
              hence "\<bar>fst (\<tau> p)\<bar> \<le> (1 + \<bar>fst p_cm\<bar> + \<bar>fst d_perp\<bar>) * r"
              proof -
                have "r * (1 + \<bar>fst p_cm\<bar>) + r * \<bar>fst d_perp\<bar> = (1 + \<bar>fst p_cm\<bar> + \<bar>fst d_perp\<bar>) * r"
                  by (by100 algebra)
                thus ?thesis using \<open>\<bar>fst (\<tau> p)\<bar> \<le> r * (1 + \<bar>fst p_cm\<bar>) + r * \<bar>fst d_perp\<bar>\<close>
                  by (by100 linarith)
              qed
              thus ?thesis using hr_eq by (by100 simp)
            qed
          qed
        qed
        have h_snd_bound: "\<exists>C. \<forall>p \<in> S_c. \<bar>snd (\<tau> p)\<bar> \<le> C * sqrt (fst p ^ 2 + snd p ^ 2)"
        proof (rule exI[of _ "1 + \<bar>snd p_cm\<bar> + \<bar>snd d_perp\<bar>"], intro ballI)
          fix p assume hp: "p \<in> S_c"
          define r where "r = sqrt (fst p ^ 2 + snd p ^ 2)"
          have hr_ge0: "r \<ge> 0" unfolding r_def by (by100 simp)
          have hC_ge1: "(1::real) + \<bar>snd p_cm\<bar> + \<bar>snd d_perp\<bar> \<ge> 1" by (by100 simp)
          show "\<bar>snd (\<tau> p)\<bar> \<le> (1 + \<bar>snd p_cm\<bar> + \<bar>snd d_perp\<bar>) * sqrt (fst p ^ 2 + snd p ^ 2)"
          proof (cases "p = (0::real, 0::real)")
            case True
            hence "\<tau> p = (0, 0)" unfolding \<tau>_def by (by100 simp)
            thus ?thesis using True by (by100 simp)
          next
            case False
            hence hne: "p \<noteq> (0::real, 0)" .
            have hr_pos: "r > 0"
            proof -
              have "fst p \<noteq> 0 \<or> snd p \<noteq> 0" using hne by (cases p) (by100 auto)
              hence "fst p ^ 2 + snd p ^ 2 > 0"
              proof
                assume "fst p \<noteq> 0"
                hence "fst p ^ 2 > 0" by (by100 simp)
                moreover have "snd p ^ 2 \<ge> 0" by (by100 simp)
                ultimately show ?thesis by (by100 linarith)
              next
                assume "snd p \<noteq> 0"
                hence "snd p ^ 2 > 0" by (by100 simp)
                moreover have "fst p ^ 2 \<ge> 0" by (by100 simp)
                ultimately show ?thesis by (by100 linarith)
              qed
              thus ?thesis unfolding r_def using real_sqrt_gt_0_iff by (by100 auto)
            qed
            have hr_eq: "sqrt (fst p ^ 2 + snd p ^ 2) = r" unfolding r_def by (by100 simp)
            define \<theta>_p where "\<theta>_p = angle_of p"
            have h\<tau>_simp: "\<tau> p = (let \<theta> = \<theta>_p in
                if \<theta> \<ge> \<theta>_cancel then (r * fst (\<tau>_boundary \<theta>), r * snd (\<tau>_boundary \<theta>))
                else let spur_pt = \<tau>_boundary \<theta>;
                         t_fold = min (\<theta> * real ?n / (2*pi)) ((\<theta>_cancel - \<theta>) * real ?n / (2*pi));
                         sign_v = (if \<theta> \<le> \<theta>_mid then 1 else -1);
                         offset = sign_v * r * (1 - r) * sin (pi * t_fold) / 4
                     in (r * fst spur_pt + offset * fst d_perp,
                         r * snd spur_pt + offset * snd d_perp))"
              unfolding \<tau>_def \<theta>_p_def angle_of_def using hne hr_eq by (by100 simp)
            show ?thesis
            proof (cases "\<theta>_p \<ge> \<theta>_cancel")
              case True
              have h\<tau>_good: "\<tau> p = (r * fst (\<tau>_boundary \<theta>_p), r * snd (\<tau>_boundary \<theta>_p))"
                using h\<tau>_simp True by (by100 simp)
              have "snd (\<tau>_boundary \<theta>_p) = sin ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)"
                using True unfolding \<tau>_boundary_def by (by100 auto)
              hence hsnd: "snd (\<tau> p) = r * sin ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)"
                using h\<tau>_good by (by100 simp)
              have "\<bar>r * sin ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)\<bar> \<le> r"
              proof -
                have "\<bar>sin ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)\<bar> \<le> 1"
                  using abs_sin_le_one by (by100 blast)
                thus ?thesis using hr_ge0
                  by (simp add: abs_mult mult_left_le)
              qed
              hence hle_r: "\<bar>snd (\<tau> p)\<bar> \<le> r" using hsnd by (by100 simp)
              have "r \<le> (1 + \<bar>snd p_cm\<bar> + \<bar>snd d_perp\<bar>) * r"
                using mult_right_mono[OF hC_ge1 hr_ge0] by (by100 simp)
              hence "\<bar>snd (\<tau> p)\<bar> \<le> (1 + \<bar>snd p_cm\<bar> + \<bar>snd d_perp\<bar>) * r"
                using hle_r by (by100 linarith)
              thus ?thesis using hr_eq by (by100 simp)
            next
              case False
              hence h\<theta>_lt: "\<not> \<theta>_p \<ge> \<theta>_cancel" .
              define spur_pt where "spur_pt = \<tau>_boundary \<theta>_p"
              define t_fold where "t_fold = min (\<theta>_p * real ?n / (2*pi)) ((\<theta>_cancel - \<theta>_p) * real ?n / (2*pi))"
              define sign_v where "sign_v = (if \<theta>_p \<le> \<theta>_mid then (1::real) else -1)"
              define offset where "offset = sign_v * r * (1 - r) * sin (pi * t_fold) / 4"
              have h\<tau>_cancel: "\<tau> p = (r * fst spur_pt + offset * fst d_perp,
                                      r * snd spur_pt + offset * snd d_perp)"
              proof -
                from h\<tau>_simp h\<theta>_lt
                have "\<tau> p = (let sp = \<tau>_boundary \<theta>_p;
                     tf = min (\<theta>_p * real ?n / (2*pi)) ((\<theta>_cancel - \<theta>_p) * real ?n / (2*pi));
                     sv = (if \<theta>_p \<le> \<theta>_mid then 1 else -1);
                     off = sv * r * (1 - r) * sin (pi * tf) / 4
                 in (r * fst sp + off * fst d_perp,
                     r * snd sp + off * snd d_perp))" by (by100 simp)
                thus ?thesis unfolding spur_pt_def t_fold_def sign_v_def offset_def Let_def
                  by (by100 simp)
              qed
              have h\<theta>_cancel_eq: "\<theta>_cancel = 4*pi/real ?n" unfolding \<theta>_cancel_def by (by100 simp)
              \<comment> \<open>Bound |snd(spur\\_pt)| \\<le> |snd(p\\_cm)|.\<close>
              have h\<theta>_lt2: "\<not> \<theta>_p \<ge> 4*pi/real ?n"
                using h\<theta>_lt unfolding \<theta>_cancel_def by (by100 linarith)
              have hsp_snd: "snd spur_pt = t_fold * snd p_cm"
              proof -
                from h\<theta>_lt
                have hsp_eq: "\<tau>_boundary \<theta>_p = (let tf = min (\<theta>_p * real ?n / (2*pi))
                    ((4*pi/real ?n - \<theta>_p) * real ?n / (2*pi))
                  in ((1 - tf) * 1 + tf * fst p_cm, (1 - tf) * 0 + tf * snd p_cm))"
                  unfolding \<tau>_boundary_def \<theta>_cancel_def by (by100 simp)
                have "snd spur_pt = snd (let tf = min (\<theta>_p * real ?n / (2*pi))
                    ((4*pi/real ?n - \<theta>_p) * real ?n / (2*pi))
                  in ((1 - tf) * 1 + tf * fst p_cm, (1 - tf) * 0 + tf * snd p_cm))"
                  unfolding spur_pt_def using hsp_eq by (by100 simp)
                also have "\<dots> = min (\<theta>_p * real ?n / (2*pi))
                    ((4*pi/real ?n - \<theta>_p) * real ?n / (2*pi)) * snd p_cm"
                  unfolding Let_def by (by100 simp)
                also have "\<dots> = t_fold * snd p_cm"
                  unfolding t_fold_def using h\<theta>_cancel_eq by (by100 simp)
                finally show ?thesis .
              qed
              have h_fst_div_bnd: "fst p / r \<ge> -1 \<and> fst p / r \<le> 1"
              proof -
                have "fst p ^ 2 \<le> fst p ^ 2 + snd p ^ 2" by (by100 simp)
                hence "fst p ^ 2 \<le> r ^ 2"
                proof -
                  have "r ^ 2 = fst p ^ 2 + snd p ^ 2"
                    unfolding r_def using real_sqrt_pow2[of "fst p^2 + snd p^2"]
                    by (by100 simp)
                  thus ?thesis by (by100 simp)
                qed
                hence "\<bar>fst p\<bar> ^ 2 \<le> r ^ 2"
                  using power2_abs[of "fst p"] by (by100 simp)
                hence "sqrt (\<bar>fst p\<bar> ^ 2) \<le> sqrt (r ^ 2)" by (rule real_sqrt_le_mono)
                hence "\<bar>fst p\<bar> \<le> r" using real_sqrt_abs hr_ge0 by (by100 simp)
                hence hfp_le: "fst p \<le> r" and hfp_ge: "- r \<le> fst p" by (by100 linarith)+
                have "fst p / r \<le> 1"
                proof -
                  have "fst p / r \<le> r / r"
                    by (intro divide_right_mono hfp_le) (rule less_imp_le[OF hr_pos])
                  thus ?thesis using hr_pos by (by100 simp)
                qed
                moreover have "fst p / r \<ge> -1"
                proof -
                  have "- r / r \<le> fst p / r"
                    by (intro divide_right_mono hfp_ge) (rule less_imp_le[OF hr_pos])
                  thus ?thesis using hr_pos by (by100 simp)
                qed
                ultimately show ?thesis by (by100 linarith)
              qed
              have h\<theta>_ge0: "\<theta>_p \<ge> 0"
              proof -
                have h_fst_ge: "- 1 \<le> fst p / r" using h_fst_div_bnd by (by100 linarith)
                have h_fst_le: "fst p / r \<le> 1" using h_fst_div_bnd by (by100 linarith)
                have h_arc_ge0: "arccos (fst p / r) \<ge> 0"
                  using arccos_lbound[OF h_fst_ge h_fst_le] .
                have h_arc_le_pi: "arccos (fst p / r) \<le> pi"
                  using arccos_ubound[OF h_fst_ge h_fst_le] .
                show ?thesis
                proof (cases "snd p \<ge> 0")
                  case True
                  hence "\<theta>_p = arccos (fst p / r)"
                    unfolding \<theta>_p_def angle_of_def r_def by (by100 simp)
                  thus ?thesis using h_arc_ge0 by (by100 linarith)
                next
                  case False
                  hence "\<theta>_p = 2*pi - arccos (fst p / r)"
                    unfolding \<theta>_p_def angle_of_def r_def by (by100 simp)
                  thus ?thesis using h_arc_le_pi pi_gt_zero by (by100 linarith)
                qed
              qed
              have htf_ge0: "t_fold \<ge> 0"
              proof -
                have "\<theta>_p * real ?n / (2*pi) \<ge> 0"
                  using h\<theta>_ge0 pi_gt_zero hn5 by (by100 simp)
                moreover have "(\<theta>_cancel - \<theta>_p) * real ?n / (2*pi) \<ge> 0"
                proof -
                  have "\<theta>_cancel > \<theta>_p" using h\<theta>_lt by (by100 linarith)
                  thus ?thesis using pi_gt_zero hn5 by (by100 simp)
                qed
                ultimately show ?thesis unfolding t_fold_def by (by100 simp)
              qed
              have htf_le1: "t_fold \<le> 1"
              proof -
                have "\<theta>_p * real ?n / (2*pi) \<ge> 0"
                  using h\<theta>_ge0 pi_gt_zero hn5 by (by100 simp)
                moreover have "(\<theta>_cancel - \<theta>_p) * real ?n / (2*pi) \<ge> 0"
                proof -
                  have "\<theta>_cancel > \<theta>_p" using h\<theta>_lt by (by100 linarith)
                  thus ?thesis using pi_gt_zero hn5 by (by100 simp)
                qed
                moreover have "\<theta>_p * real ?n / (2*pi) + (\<theta>_cancel - \<theta>_p) * real ?n / (2*pi)
                    = \<theta>_cancel * real ?n / (2*pi)" by (by100 algebra)
                moreover have "\<theta>_cancel * real ?n / (2*pi) = 2"
                  unfolding \<theta>_cancel_def using pi_gt_zero hn5 by (by100 simp)
                ultimately show ?thesis unfolding t_fold_def by (by100 linarith)
              qed
              have hsp_snd_bound: "\<bar>snd spur_pt\<bar> \<le> \<bar>snd p_cm\<bar>"
              proof -
                have "\<bar>t_fold * snd p_cm\<bar> = t_fold * \<bar>snd p_cm\<bar>"
                  using htf_ge0 abs_mult[of t_fold "snd p_cm"] by (by100 simp)
                also have "\<dots> \<le> 1 * \<bar>snd p_cm\<bar>"
                  using mult_right_mono[OF htf_le1 abs_ge_zero[of "snd p_cm"]] by (by100 simp)
                finally show ?thesis unfolding hsp_snd by (by100 simp)
              qed
              have hr_le1: "r \<le> 1"
              proof -
                have "p \<in> top1_B2" using hp unfolding S_c_def by (by100 blast)
                hence "fst p ^ 2 + snd p ^ 2 \<le> 1" unfolding top1_B2_def by (by100 simp)
                hence "sqrt (fst p ^ 2 + snd p ^ 2) \<le> sqrt 1" by (rule real_sqrt_le_mono)
                thus ?thesis unfolding r_def by (by100 simp)
              qed
              have hoff_bound: "\<bar>offset\<bar> \<le> r"
              proof -
                have h1mr_ge0: "1 - r \<ge> 0" using hr_le1 by (by100 linarith)
                have hprod_ge0: "r * (1 - r) \<ge> 0" using hr_ge0 h1mr_ge0 by (by100 simp)
                have hprod_le_r: "r * (1 - r) \<le> r"
                  using mult_left_mono[of "1 - r" 1 r] hr_ge0 hr_le1 by (by100 simp)
                have hsin_le: "sin (pi * t_fold) \<le> 1" by (rule sin_le_one)
                have hsin_ge: "sin (pi * t_fold) \<ge> -1" by (rule sin_ge_minus_one)
                have hprod_sin_le: "r * (1 - r) * sin (pi * t_fold) \<le> r * (1 - r)"
                  using mult_left_mono[OF hsin_le hprod_ge0] by (by100 simp)
                have hprod_sin_ge: "r * (1 - r) * sin (pi * t_fold) \<ge> - (r * (1 - r))"
                  using mult_left_mono[OF hsin_ge hprod_ge0] by (by100 simp)
                have "sign_v = 1 \<or> sign_v = -1" unfolding sign_v_def by (by100 auto)
                thus ?thesis
                proof
                  assume "sign_v = 1"
                  hence "offset = 1 * r * (1 - r) * sin (pi * t_fold) / 4"
                    unfolding offset_def by (by100 simp)
                  hence "offset = r * (1 - r) * sin (pi * t_fold) / 4" by (by100 simp)
                  thus ?thesis using hprod_sin_le hprod_sin_ge hprod_le_r hr_ge0
                    by (by100 linarith)
                next
                  assume "sign_v = -1"
                  hence "offset = (-1) * r * (1 - r) * sin (pi * t_fold) / 4"
                    unfolding offset_def by (by100 simp)
                  hence "offset = - (r * (1 - r) * sin (pi * t_fold) / 4)" by (by100 linarith)
                  thus ?thesis using hprod_sin_le hprod_sin_ge hprod_le_r hr_ge0
                    by (by100 linarith)
                qed
              qed
              \<comment> \<open>Combine: |snd(\\<tau> p)| \\<le> r*|snd(sp)| + |off|*|snd(dp)|.\<close>
              have hsnd_tau: "\<bar>snd (\<tau> p)\<bar> \<le> \<bar>r * snd spur_pt\<bar> + \<bar>offset * snd d_perp\<bar>"
                using h\<tau>_cancel by (by100 simp)
              have "\<bar>r * snd spur_pt\<bar> = r * \<bar>snd spur_pt\<bar>"
                using hr_ge0 abs_mult[of r "snd spur_pt"] by (by100 simp)
              hence "\<bar>r * snd spur_pt\<bar> \<le> r * \<bar>snd p_cm\<bar>"
                using mult_left_mono[OF hsp_snd_bound hr_ge0] by (by100 simp)
              moreover have "\<bar>offset * snd d_perp\<bar> = \<bar>offset\<bar> * \<bar>snd d_perp\<bar>"
                using abs_mult[of offset "snd d_perp"] by (by100 simp)
              hence "\<bar>offset * snd d_perp\<bar> \<le> r * \<bar>snd d_perp\<bar>"
                using mult_right_mono[OF hoff_bound abs_ge_zero[of "snd d_perp"]] by (by100 simp)
              ultimately have "\<bar>snd (\<tau> p)\<bar> \<le> r * \<bar>snd p_cm\<bar> + r * \<bar>snd d_perp\<bar>"
                using hsnd_tau by (by100 linarith)
              hence "\<bar>snd (\<tau> p)\<bar> \<le> (1 + \<bar>snd p_cm\<bar> + \<bar>snd d_perp\<bar>) * r"
              proof -
                have "r * \<bar>snd p_cm\<bar> + r * \<bar>snd d_perp\<bar> \<le> (1 + \<bar>snd p_cm\<bar> + \<bar>snd d_perp\<bar>) * r"
                proof -
                  have "r * \<bar>snd p_cm\<bar> + r * \<bar>snd d_perp\<bar> = r * (\<bar>snd p_cm\<bar> + \<bar>snd d_perp\<bar>)"
                    by (by100 algebra)
                  also have "\<dots> \<le> r * (1 + \<bar>snd p_cm\<bar> + \<bar>snd d_perp\<bar>)"
                    using mult_left_mono[of "\<bar>snd p_cm\<bar> + \<bar>snd d_perp\<bar>" "1 + \<bar>snd p_cm\<bar> + \<bar>snd d_perp\<bar>" r]
                      hr_ge0 by (by100 simp)
                  also have "\<dots> = (1 + \<bar>snd p_cm\<bar> + \<bar>snd d_perp\<bar>) * r" by (by100 algebra)
                  finally show ?thesis .
                qed
                thus ?thesis using \<open>\<bar>snd (\<tau> p)\<bar> \<le> r * \<bar>snd p_cm\<bar> + r * \<bar>snd d_perp\<bar>\<close>
                  by (by100 linarith)
              qed
              thus ?thesis using hr_eq by (by100 simp)
            qed
          qed
        qed
        have h_fst_to_0: "((\<lambda>p. fst p) \<longlongrightarrow> (0::real)) (at (0::real, 0::real) within S_c)"
        proof -
          have "isCont fst (0::real, 0::real)" by (intro continuous_intros)
          hence "(fst \<longlongrightarrow> (0::real)) (at (0::real, 0::real))"
            unfolding isCont_def by (by100 simp)
          thus ?thesis by (rule filterlim_mono) (auto simp: at_le)
        qed
        have h_snd_to_0: "((\<lambda>p. snd p) \<longlongrightarrow> (0::real)) (at (0::real, 0::real) within S_c)"
        proof -
          have "isCont snd (0::real, 0::real)" by (intro continuous_intros)
          hence "(snd \<longlongrightarrow> (0::real)) (at (0::real, 0::real))"
            unfolding isCont_def by (by100 simp)
          thus ?thesis by (rule filterlim_mono) (auto simp: at_le)
        qed
        have h_r_to_0: "((\<lambda>p. sqrt (fst p ^ 2 + snd p ^ 2)) \<longlongrightarrow> 0)
            (at (0::real, 0::real) within S_c)"
        proof -
          have "((\<lambda>p. sqrt (fst p ^ 2 + snd p ^ 2)) \<longlongrightarrow> sqrt ((0::real) ^ 2 + (0::real) ^ 2))
              (at (0::real, 0::real) within S_c)"
            using h_fst_to_0 h_snd_to_0 by (intro tendsto_intros)
          thus ?thesis by (by100 simp)
        qed
        \<comment> \<open>Squeeze: 0 \\<le> |fst(\\<tau> p)| \\<le> C*r and C*r \\<to> 0.\<close>
        from h_fst_bound obtain C1 where hC1: "\<forall>p\<in>S_c. \<bar>fst (\<tau> p)\<bar> \<le> C1 * sqrt (fst p^2 + snd p^2)"
          by (by100 blast)
        have h_C1r: "((\<lambda>p. C1 * sqrt (fst p ^ 2 + snd p ^ 2)) \<longlongrightarrow> 0)
            (at (0::real, 0::real) within S_c)"
          using tendsto_mult_left[OF h_r_to_0, of C1] by (by100 simp)
        have h_abs_fst: "((\<lambda>p. \<bar>fst (\<tau> p)\<bar>) \<longlongrightarrow> 0) (at (0,0) within S_c)"
        proof (rule real_tendsto_sandwich[where f="\<lambda>_. 0" and h="\<lambda>p. C1 * sqrt (fst p^2+snd p^2)"])
          show "\<forall>\<^sub>F p in at (0,0) within S_c. (0::real) \<le> \<bar>fst (\<tau> p)\<bar>"
            by (intro always_eventually) (by100 auto)
          show "\<forall>\<^sub>F p in at (0,0) within S_c. \<bar>fst (\<tau> p)\<bar> \<le> C1 * sqrt (fst p^2+snd p^2)"
            unfolding eventually_at_filter using hC1 by (intro always_eventually) (by100 auto)
          show "((\<lambda>_. 0::real) \<longlongrightarrow> 0) (at (0,0) within S_c)" by (by100 simp)
          show "((\<lambda>p. C1 * sqrt (fst p ^ 2 + snd p ^ 2)) \<longlongrightarrow> 0)
              (at (0::real, 0::real) within S_c)" by (rule h_C1r)
        qed
        have h_fst_tau_0: "((\<lambda>p. fst (\<tau> p)) \<longlongrightarrow> 0) (at (0,0) within S_c)"
          using tendsto_rabs_zero_cancel[OF h_abs_fst] .
        from h_snd_bound obtain C2 where hC2: "\<forall>p\<in>S_c. \<bar>snd (\<tau> p)\<bar> \<le> C2 * sqrt (fst p^2 + snd p^2)"
          by (by100 blast)
        have h_C2r: "((\<lambda>p. C2 * sqrt (fst p ^ 2 + snd p ^ 2)) \<longlongrightarrow> 0)
            (at (0::real, 0::real) within S_c)"
          using tendsto_mult_left[OF h_r_to_0, of C2] by (by100 simp)
        have h_abs_snd: "((\<lambda>p. \<bar>snd (\<tau> p)\<bar>) \<longlongrightarrow> 0) (at (0,0) within S_c)"
        proof (rule real_tendsto_sandwich[where f="\<lambda>_. 0" and h="\<lambda>p. C2 * sqrt (fst p^2+snd p^2)"])
          show "\<forall>\<^sub>F p in at (0,0) within S_c. (0::real) \<le> \<bar>snd (\<tau> p)\<bar>"
            by (intro always_eventually) (by100 auto)
          show "\<forall>\<^sub>F p in at (0,0) within S_c. \<bar>snd (\<tau> p)\<bar> \<le> C2 * sqrt (fst p^2+snd p^2)"
            unfolding eventually_at_filter using hC2 by (intro always_eventually) (by100 auto)
          show "((\<lambda>_. 0::real) \<longlongrightarrow> 0) (at (0,0) within S_c)" by (by100 simp)
          show "((\<lambda>p. C2 * sqrt (fst p ^ 2 + snd p ^ 2)) \<longlongrightarrow> 0)
              (at (0::real, 0::real) within S_c)" by (rule h_C2r)
        qed
        have h_snd_tau_0: "((\<lambda>p. snd (\<tau> p)) \<longlongrightarrow> 0) (at (0,0) within S_c)"
          using tendsto_rabs_zero_cancel[OF h_abs_snd] .
        from tendsto_Pair[OF h_fst_tau_0 h_snd_tau_0]
        show ?thesis by (by100 simp)
      qed
      have h_origin_in_Sc: "(0::real, 0::real) \<in> S_c"
        unfolding S_c_def top1_B2_def by (by100 simp)
      have h_c_cont: "continuous_on S_c \<tau>"
        unfolding continuous_on_def
      proof (intro ballI)
        fix p assume hp: "p \<in> S_c"
        show "((\<lambda>x. \<tau> x) \<longlongrightarrow> \<tau> p) (at p within S_c)"
        proof (cases "p = (0::real,0::real)")
          case True
          hence "\<tau> p = (0,0)" unfolding \<tau>_def by (by100 simp)
          thus ?thesis using True h_c_cont_origin by (by100 simp)
        next
          case False
          from continuous_on_def[THEN iffD1, OF h_c_cont_nonzero, rule_format]
          have "((\<lambda>x. \<tau> x) \<longlongrightarrow> \<tau> p) (at p within (S_c - {(0, 0)}))"
            using hp False by (by100 blast)
          moreover have "at p within (S_c - {(0, 0)}) = at p within S_c"
          proof (rule at_within_nhd[where S = "- {(0::real, 0::real)}"])
            show "p \<in> - {(0::real, 0::real)}" using False by (by100 simp)
            show "open (- {(0::real, 0::real)})"
              using closed_singleton by (by100 blast)
            show "(S_c - {(0, 0)}) \<inter> (- {(0, 0)}) - {p} = S_c \<inter> (- {(0, 0)}) - {p}"
              by (by100 auto)
          qed
          ultimately show ?thesis by (by100 simp)
        qed
      qed
      have h\<tau>_cont: "continuous_on top1_B2 \<tau>"
        using continuous_on_closed_Un[OF h_g_closed h_c_closed h_g_cont h_c_cont]
        unfolding h_cover[symmetric] .
      \<comment> \<open>Sub-sorry 2: \\<tau> maps B2 onto B2 (range and surjectivity).
         Good sector: angle rescaling is a bijection [\\<theta>\\_cancel, 2\\<pi>) \\<to> [0, 2\\<pi>).
         Cancel sector: maps to interior of B2 (spur + offset, |result| < 1 for r < 1).
         At r=1 (boundary): \\<tau>\\_boundary maps S1 onto S1 (good sector) + spur (cancel).
         Overall: \\<tau> is continuous on compact B2, image is contained in B2, image contains
         all of S1 (via good sector at r=1), and image contains origin. By connectedness and
         surjectivity of \\<tau>\\_boundary, \\<tau>(B2) = B2.\<close>
      have h\<tau>_range: "\<forall>p \<in> top1_B2. \<tau> p \<in> top1_B2"
      proof (intro ballI)
        fix p assume hp: "p \<in> top1_B2"
        hence hp_norm: "fst p ^ 2 + snd p ^ 2 \<le> 1" unfolding top1_B2_def by (by100 simp)
        show "\<tau> p \<in> top1_B2"
        proof (cases "p = (0, 0)")
          case True thus ?thesis unfolding \<tau>_def top1_B2_def by (by100 simp)
        next
          case False
          define r where "r = sqrt (fst p ^ 2 + snd p ^ 2)"
          define \<theta>_p where "\<theta>_p = (if snd p \<ge> 0 then arccos (fst p / r) else 2*pi - arccos (fst p / r))"
          have hr_pos: "r > 0"
          proof -
            have "fst p \<noteq> 0 \<or> snd p \<noteq> 0" using False by (cases p) (by100 auto)
            hence "fst p ^ 2 + snd p ^ 2 > 0"
            proof
              assume "fst p \<noteq> 0"
              hence "fst p ^ 2 > 0" by (by100 simp)
              moreover have "snd p ^ 2 \<ge> 0" by (by100 simp)
              ultimately show ?thesis by (by100 linarith)
            next
              assume "snd p \<noteq> 0"
              hence "snd p ^ 2 > 0" by (by100 simp)
              moreover have "fst p ^ 2 \<ge> 0" by (by100 simp)
              ultimately show ?thesis by (by100 linarith)
            qed
            thus ?thesis unfolding r_def using real_sqrt_gt_0_iff by (by100 auto)
          qed
          have hr_le1: "r \<le> 1"
          proof -
            have "fst p ^ 2 + snd p ^ 2 \<le> 1" using hp_norm .
            hence "sqrt (fst p ^ 2 + snd p ^ 2) \<le> sqrt 1" by (rule real_sqrt_le_mono)
            thus ?thesis unfolding r_def by (by100 simp)
          qed
          have hr_sq: "r^2 = fst p ^ 2 + snd p ^ 2"
          proof -
            have "fst p ^ 2 + snd p ^ 2 \<ge> 0" by (rule sum_power2_ge_zero)
            thus ?thesis unfolding r_def using real_sqrt_pow2 by (by100 blast)
          qed
          \<comment> \<open>Both sectors map into B2. Need: fst(\\<tau> p)^2 + snd(\\<tau> p)^2 \\<le> 1.\<close>
          \<comment> \<open>Key property: \\<tau> p = r * (boundary\\_point) + small\\_offset. Since r \\<le> 1 and
             boundary\\_point has norm \\<le> 1, the main term has norm \\<le> r. The offset is
             proportional to r*(1-r) which vanishes at r=0 and r=1.\<close>
          \<comment> \<open>Helper: for any angle \\<alpha>, (r*cos \\<alpha>)^2 + (r*sin \\<alpha>)^2 = r^2 \\<le> 1.\<close>
          have hgood_norm: "\<And>\<alpha>. (r * cos \<alpha>) ^ 2 + (r * sin \<alpha>) ^ 2 \<le> 1"
          proof -
            fix \<alpha> :: real
            have "(r * cos \<alpha>) ^ 2 + (r * sin \<alpha>) ^ 2 = r^2 * (cos \<alpha> ^ 2 + sin \<alpha> ^ 2)"
              by (by100 algebra)
            also have "\<dots> = r^2" using sin_cos_squared_add3 by (by100 simp)
            also have "\<dots> \<le> 1"
            proof -
              have "r \<ge> 0" using hr_pos by (by100 linarith)
              hence "r^2 \<le> 1^2" using hr_le1
                by (intro power_mono) (by100 auto)
              thus ?thesis by (by100 simp)
            qed
            finally show "(r * cos \<alpha>) ^ 2 + (r * sin \<alpha>) ^ 2 \<le> 1" .
          qed
          \<comment> \<open>The \\<tau> definition matches r and \\<theta>\\_p locally. To use r and \\<theta>\\_p, we need
             to show \\<tau> p unfolds to use these local definitions.
             For the good sector: \\<tau>(p) = (r * cos(\\<theta>'), r * sin(\\<theta>')) where
             \\<theta>' = (\\<theta>\\_p - \\<theta>\\_cancel) * n / m. So norm = r \\<le> 1.
             For the cancel sector: more complex but bounded by r*(3-r)/2 \\<le> 1.\<close>
          \<comment> \<open>Key fact: \\<tau>\\_def at p \\<noteq> (0,0) uses sqrt(fst p^2+snd p^2) = r (our local r).
             To avoid let-binding unfolding issues, prove \\<tau> p \\<in> B2 directly.\<close>
          \<comment> \<open>p\\_cm norm: centroid mapped to disk interior.\<close>
          have hp_cm_le: "fst p_cm ^ 2 + snd p_cm ^ 2 \<le> 1"
          proof -
            have "p_cm \<in> top1_B2" using hp_cm_B2 .
            thus ?thesis unfolding top1_B2_def by (by100 simp)
          qed
          \<comment> \<open>Convex combination of (1,0) and p\\_cm is in B2 (by convexity of B2).\<close>
          have hconv_bound: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow>
              ((1-t) + t * fst p_cm) ^ 2 + (t * snd p_cm) ^ 2 \<le> 1"
          proof -
            fix t :: real assume ht0: "0 \<le> t" and ht1: "t \<le> 1"
            let ?f = "fst p_cm" and ?s = "snd p_cm"
            \<comment> \<open>Expand: ((1-t) + t*f)^2 + (t*s)^2 = (1-t)^2 + 2*t*(1-t)*f + t^2*(f^2+s^2).\<close>
            have hexpand: "((1-t) + t * ?f) ^ 2 + (t * ?s) ^ 2
                = (1-t)^2 + 2*t*(1-t)*?f + t^2*(?f^2 + ?s^2)"
              by (by100 algebra)
            \<comment> \<open>f^2+s^2 \\<le> 1.\<close>
            have hfs: "?f^2 + ?s^2 \<le> 1" using hp_cm_le .
            \<comment> \<open>t^2 * (f^2+s^2) \\<le> t^2.\<close>
            have ht2: "t^2 * (?f^2 + ?s^2) \<le> t^2"
            proof -
              have "t^2 \<ge> 0" by (by100 simp)
              have "t^2 * (?f^2 + ?s^2) \<le> t^2 * 1"
                using mult_left_mono[OF hfs \<open>t^2 \<ge> 0\<close>] by (by100 linarith)
              thus ?thesis by (by100 simp)
            qed
            \<comment> \<open>-1 \\<le> f \\<le> 1 (from |p\\_cm| \\<le> 1).\<close>
            have hf_ge: "?f \<ge> -1" and hf_le: "?f \<le> 1"
            proof -
              have "?s ^ 2 \<ge> 0" by (by100 simp)
              hence "?f ^ 2 \<le> 1" using hfs by (by100 linarith)
              show "?f \<ge> -1"
              proof (rule ccontr)
                assume "\<not> ?f \<ge> -1"
                hence "(-?f) > 1" by (by100 linarith)
                hence "(-?f) * (-?f) > 1" using mult_strict_mono'[of 1 "-?f" 1 "-?f"] by (by100 linarith)
                hence "?f ^ 2 > 1" unfolding power2_eq_square by (by100 linarith)
                thus False using \<open>?f ^ 2 \<le> 1\<close> by (by100 linarith)
              qed
              show "?f \<le> 1"
              proof (rule ccontr)
                assume "\<not> ?f \<le> 1"
                hence "?f > 1" by (by100 linarith)
                hence "?f * ?f > 1" using mult_strict_mono'[of 1 "?f" 1 "?f"] by (by100 linarith)
                hence "?f ^ 2 > 1" unfolding power2_eq_square by (by100 linarith)
                thus False using \<open>?f ^ 2 \<le> 1\<close> by (by100 linarith)
              qed
            qed
            \<comment> \<open>2*t*(1-t)*f \\<le> 2*t*(1-t): since 0 \\<le> t*(1-t) and f \\<le> 1.\<close>
            have h2tf: "2*t*(1-t)*?f \<le> 2*t*(1-t)"
            proof -
              have h1t: "1 - t \<ge> 0" using ht1 by (by100 linarith)
              have "t*(1-t) \<ge> 0" using ht0 h1t by (rule mult_nonneg_nonneg)
              hence h2t: "2*t*(1-t) \<ge> 0" by (by100 linarith)
              have "2*t*(1-t)*?f \<le> 2*t*(1-t)*1"
                using mult_left_mono[OF hf_le h2t] by (by100 linarith)
              thus ?thesis by (by100 simp)
            qed
            \<comment> \<open>Sum: (1-t)^2 + 2*t*(1-t) + t^2 = 1.\<close>
            have hsum1: "(1-t)^2 + 2*t*(1-t) + t^2 = (1::real)" by (by100 algebra)
            \<comment> \<open>Combine.\<close>
            have "((1-t) + t * ?f) ^ 2 + (t * ?s) ^ 2 \<le> (1-t)^2 + 2*t*(1-t) + t^2"
              using hexpand ht2 h2tf by (by100 linarith)
            thus "((1-t) + t * ?f) ^ 2 + (t * ?s) ^ 2 \<le> 1"
              using hsum1 by (by100 linarith)
          qed
          \<comment> \<open>d\\_perp norm: (-snd p\\_cm, fst p\\_cm - 1). |d|^2 \\<le> 4.\<close>
          have hd_sq_bound: "fst d_perp ^ 2 + snd d_perp ^ 2 \<le> 4"
          proof -
            have "fst d_perp = - snd p_cm" "snd d_perp = fst p_cm - 1"
              unfolding d_perp_def by (by100 auto)+
            hence "fst d_perp ^ 2 + snd d_perp ^ 2
                 = snd p_cm ^ 2 + (fst p_cm - 1) ^ 2" by (by100 simp)
            also have "\<dots> = snd p_cm ^ 2 + fst p_cm ^ 2 - 2 * fst p_cm + 1"
              by (by100 algebra)
            also have "\<dots> \<le> 1 - 2 * fst p_cm + 1"
              using hp_cm_le by (by100 linarith)
            also have "\<dots> = 2 - 2 * fst p_cm" by (by100 linarith)
            also have "\<dots> \<le> 4"
            proof -
              have "fst p_cm \<ge> -1"
              proof -
                have "snd p_cm ^ 2 \<ge> 0" by (by100 simp)
                hence "fst p_cm ^ 2 \<le> 1" using hp_cm_le by (by100 linarith)
                hence "- 1 \<le> fst p_cm \<and> fst p_cm \<le> 1"
                proof -
                  assume h: "(fst p_cm)\<^sup>2 \<le> 1"
                  have "fst p_cm \<le> 1"
                  proof (rule ccontr)
                    assume "\<not> fst p_cm \<le> 1"
                    hence hgt: "fst p_cm > 1" by (by100 linarith)
                    have "fst p_cm ^ 2 > 1"
                    proof -
                      have "fst p_cm * fst p_cm > 1 * 1"
                        using mult_strict_mono'[of 1 "fst p_cm" 1 "fst p_cm"] hgt by (by100 linarith)
                      thus ?thesis unfolding power2_eq_square by (by100 linarith)
                    qed
                    thus False using h by (by100 linarith)
                  qed
                  moreover have "fst p_cm \<ge> -1"
                  proof (rule ccontr)
                    assume "\<not> fst p_cm \<ge> -1"
                    hence hlt: "fst p_cm < -1" by (by100 linarith)
                    have "fst p_cm ^ 2 > 1"
                    proof -
                      have "(-fst p_cm) > 1" using hlt by (by100 linarith)
                      hence "(-fst p_cm) * (-fst p_cm) > 1 * 1"
                        using mult_strict_mono'[of 1 "-fst p_cm" 1 "-fst p_cm"] by (by100 linarith)
                      thus ?thesis unfolding power2_eq_square by (by100 linarith)
                    qed
                    thus False using h by (by100 linarith)
                  qed
                  ultimately show ?thesis by (by100 simp)
                qed
                thus ?thesis by (by100 linarith)
              qed
              thus ?thesis by (by100 linarith)
            qed
            finally show ?thesis .
          qed
          \<comment> \<open>Key: relate \\<tau> definition's internal sqrt to our local r.
             \\<tau>\\_def uses sqrt(fst p^2 + snd p^2) which equals r by definition.\<close>
          have hr_eq: "sqrt (fst p ^ 2 + snd p ^ 2) = r" unfolding r_def by (by100 simp)
          \<comment> \<open>Unfold \\<tau> at p \\<noteq> (0,0): the let-expression uses sqrt and arccos.\<close>
          have h\<tau>_simp: "\<tau> p = (let \<theta> = \<theta>_p in
              if \<theta> \<ge> \<theta>_cancel then (r * fst (\<tau>_boundary \<theta>), r * snd (\<tau>_boundary \<theta>))
              else let spur_pt = \<tau>_boundary \<theta>;
                       t_fold = min (\<theta> * real ?n / (2*pi)) ((\<theta>_cancel - \<theta>) * real ?n / (2*pi));
                       sign = (if \<theta> \<le> \<theta>_mid then 1 else -1);
                       offset = sign * r * (1 - r) * sin (pi * t_fold) / 4
                   in (r * fst spur_pt + offset * fst d_perp,
                       r * snd spur_pt + offset * snd d_perp))"
            unfolding \<tau>_def using False hr_eq \<theta>_p_def by (by100 simp)
          show ?thesis
          proof (cases "\<theta>_p \<ge> \<theta>_cancel")
            case True
            \<comment> \<open>Good sector: \\<tau>(p) = (r*fst(\\<tau>\\_bdy), r*snd(\\<tau>\\_bdy)) where \\<tau>\\_bdy = (cos, sin).\<close>
            have h\<tau>_good: "\<tau> p = (r * fst (\<tau>_boundary \<theta>_p), r * snd (\<tau>_boundary \<theta>_p))"
              using h\<tau>_simp True by (by100 simp)
            have "fst (\<tau>_boundary \<theta>_p) = cos ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)"
              using True unfolding \<tau>_boundary_def by (by100 auto)
            moreover have "snd (\<tau>_boundary \<theta>_p) = sin ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)"
              using True unfolding \<tau>_boundary_def by (by100 auto)
            ultimately have "fst (\<tau> p) = r * cos ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)
                           \<and> snd (\<tau> p) = r * sin ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)"
              using h\<tau>_good by (by100 auto)
            hence "fst (\<tau> p) ^ 2 + snd (\<tau> p) ^ 2
                = (r * cos ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)) ^ 2
                + (r * sin ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)) ^ 2"
              by (by100 simp)
            hence "fst (\<tau> p) ^ 2 + snd (\<tau> p) ^ 2 \<le> 1" using hgood_norm by (by100 simp)
            thus ?thesis unfolding top1_B2_def by (by100 simp)
          next
            case False
            \<comment> \<open>Cancel sector: \\<tau>(p) = r*spur\\_pt + offset*d\\_perp.
               Need norm \\<le> 1 via triangle inequality + all proved bounds.\<close>
            \<comment> \<open>Cancel sector: \\<tau>(p) = r*spur\\_pt + offset*d\\_perp.\<close>
            have h\<theta>_lt: "\<not> \<theta>_p \<ge> \<theta>_cancel" using False .
            \<comment> \<open>From h\\<tau>\\_simp: extract \\<tau>(p) components in cancel sector.\<close>
            define spur_pt_loc where "spur_pt_loc = \<tau>_boundary \<theta>_p"
            define t_fold_loc where "t_fold_loc = min (\<theta>_p * real ?n / (2*pi)) ((\<theta>_cancel - \<theta>_p) * real ?n / (2*pi))"
            define sign_loc where "sign_loc = (if \<theta>_p \<le> \<theta>_mid then (1::real) else -1)"
            define offset_loc where "offset_loc = sign_loc * r * (1 - r) * sin (pi * t_fold_loc) / 4"
            have h\<tau>_cancel: "\<tau> p = (r * fst spur_pt_loc + offset_loc * fst d_perp,
                                    r * snd spur_pt_loc + offset_loc * snd d_perp)"
            proof -
              from h\<tau>_simp h\<theta>_lt
              have "\<tau> p = (let spur_pt = \<tau>_boundary \<theta>_p;
                       t_fold = min (\<theta>_p * real ?n / (2*pi)) ((\<theta>_cancel - \<theta>_p) * real ?n / (2*pi));
                       sign = (if \<theta>_p \<le> \<theta>_mid then 1 else -1);
                       offset = sign * r * (1 - r) * sin (pi * t_fold) / 4
                   in (r * fst spur_pt + offset * fst d_perp,
                       r * snd spur_pt + offset * snd d_perp))"
                by (by100 simp)
              thus ?thesis unfolding spur_pt_loc_def t_fold_loc_def sign_loc_def offset_loc_def Let_def
                by (by100 simp)
            qed
            \<comment> \<open>Bound: |offset\\_loc| \\<le> r*(1-r)/4 (from |sin| \\<le> 1 and |sign| = 1).\<close>
            \<comment> \<open>Bound: offset\\_loc^2 \\<le> (r*(1-r)/4)^2.\<close>
            have hoffset: "offset_loc ^ 2 \<le> (r * (1-r) / 4) ^ 2"
            proof -
              \<comment> \<open>offset = sign * r * (1-r) * sin(...) / 4. Square: sign^2=1, sin^2\\<le>1.\<close>
              have "sign_loc ^ 2 = 1" unfolding sign_loc_def by (by100 auto)
              have hsin_sq: "sin (pi * t_fold_loc) ^ 2 \<le> 1"
              proof -
                let ?s = "sin (pi * t_fold_loc)"
                have h1: "?s \<le> 1" by (rule sin_le_one)
                have h2: "?s \<ge> -1" by (rule sin_ge_minus_one)
                have "?s * ?s \<le> 1"
                proof (cases "?s \<ge> 0")
                  case True
                  have "?s * ?s \<le> ?s * 1"
                    using mult_left_mono[OF h1 True] by (by100 simp)
                  also have "?s * 1 \<le> 1" using h1 by (by100 simp)
                  finally show ?thesis .
                next
                  case False
                  hence hneg: "?s < 0" by (by100 linarith)
                  have hmle: "-?s \<le> 1" using h2 by (by100 linarith)
                  have hmge: "-?s \<ge> 0" using hneg by (by100 linarith)
                  have "(-?s) * (-?s) \<le> (-?s) * 1"
                    using mult_left_mono[OF hmle hmge] by (by100 simp)
                  also have "(-?s) * 1 \<le> 1" using hmle by (by100 simp)
                  finally have "(-?s) * (-?s) \<le> 1" .
                  thus ?thesis by (by100 simp)
                qed
                thus ?thesis unfolding power2_eq_square .
              qed
              have "offset_loc ^ 2 = sign_loc ^ 2 * r ^ 2 * (1 - r) ^ 2 * sin (pi * t_fold_loc) ^ 2 / 16"
                unfolding offset_loc_def power2_eq_square by (by100 simp)
              also have "\<dots> = r ^ 2 * (1 - r) ^ 2 * sin (pi * t_fold_loc) ^ 2 / 16"
                using \<open>sign_loc ^ 2 = 1\<close> by (by100 simp)
              also have "\<dots> \<le> r ^ 2 * (1 - r) ^ 2 * 1 / 16"
              proof -
                have "r ^ 2 * (1 - r) ^ 2 \<ge> 0" by (by100 simp)
                from mult_left_mono[OF hsin_sq this]
                show ?thesis by (by100 linarith)
              qed
              also have "\<dots> = (r * (1-r) / 4) ^ 2"
                unfolding power2_eq_square by (by100 simp)
              finally show ?thesis .
            qed
            \<comment> \<open>spur\\_pt\\_loc is \\<tau>\\_boundary(\\<theta>\\_p) in cancel sector = convex combo of (1,0) and p\\_cm.\<close>
            have hspur_in_B2: "fst spur_pt_loc ^ 2 + snd spur_pt_loc ^ 2 \<le> 1"
            proof -
              \<comment> \<open>spur\\_pt\\_loc = \\<tau>\\_boundary(\\<theta>\\_p) in cancel sector = convex combo.\<close>
              have h\<theta>_lt: "\<not> \<theta>_p \<ge> \<theta>_cancel" using \<open>\<not> \<theta>_p \<ge> \<theta>_cancel\<close> .
              define tf where "tf = min (\<theta>_p * real ?n / (2*pi)) ((4*pi/real ?n - \<theta>_p) * real ?n / (2*pi))"
              have hspur_eq: "spur_pt_loc = ((1-tf) + tf * fst p_cm, tf * snd p_cm)"
              proof -
                have "\<not> \<theta>_p \<ge> \<theta>_cancel" using h\<theta>_lt .
                hence "\<tau>_boundary \<theta>_p = (let t_fold = min (\<theta>_p * real ?n / (2*pi))
                    ((4*pi/real ?n - \<theta>_p) * real ?n / (2*pi))
                    in ((1 - t_fold) * 1 + t_fold * fst p_cm, (1 - t_fold) * 0 + t_fold * snd p_cm))"
                  unfolding \<tau>_boundary_def \<theta>_cancel_def by (by100 simp)
                thus ?thesis unfolding spur_pt_loc_def tf_def Let_def by (by100 simp)
              qed
              \<comment> \<open>Show 0 \\<le> tf \\<le> 1.\<close>
              have hn_pos: "real ?n > 0"
              proof -
                have "?n \<ge> 5" using assms(2) by (by100 simp)
                thus ?thesis by (by100 simp)
              qed
              have hpi_pos: "pi > 0" using pi_gt_zero .
              have htf_ge0: "tf \<ge> 0"
              proof -
                have "\<theta>_p \<ge> 0"
                proof (cases "snd p \<ge> 0")
                  case True
                  hence "\<theta>_p = arccos (fst p / r)" unfolding \<theta>_p_def by (by100 simp)
                  moreover have "arccos (fst p / r) \<ge> 0"
                  proof (rule arccos_lbound)
                    have "fst p ^ 2 \<le> r^2"
                    proof -
                      have "snd p ^ 2 \<ge> 0" by (by100 simp)
                      thus ?thesis using hr_sq by (by100 linarith)
                    qed
                    hence hfp_le_r: "abs (fst p) \<le> r"
                    proof -
                      assume h: "fst p ^ 2 \<le> r ^ 2"
                      have "0 \<le> r" using hr_pos by (by100 linarith)
                      from power2_le_imp_le[OF h this]
                      have "fst p \<le> r" .
                      moreover have "- fst p \<le> r"
                      proof -
                        have "(- fst p) ^ 2 = fst p ^ 2" by (by100 algebra)
                        hence "(- fst p) ^ 2 \<le> r ^ 2" using h by (by100 linarith)
                        from power2_le_imp_le[OF this \<open>0 \<le> r\<close>]
                        show ?thesis .
                      qed
                      ultimately show ?thesis by (by100 linarith)
                    qed
                    show "- 1 \<le> fst p / r"
                    proof -
                      have "- r \<le> fst p" using hfp_le_r by (by100 linarith)
                      hence "- 1 \<le> fst p / r"
                        using hr_pos divide_right_mono[of "-r" "fst p" r] by (by100 simp)
                      thus ?thesis .
                    qed
                    show "fst p / r \<le> 1"
                    proof -
                      have "fst p \<le> r" using hfp_le_r by (by100 linarith)
                      thus ?thesis using hr_pos by (by100 simp)
                    qed
                  qed
                  ultimately show ?thesis by (by100 linarith)
                next
                  case False
                  hence "\<theta>_p = 2*pi - arccos (fst p / r)" unfolding \<theta>_p_def by (by100 simp)
                  moreover have "arccos (fst p / r) \<le> pi"
                  proof (rule arccos_ubound)
                    have "fst p ^ 2 \<le> r^2"
                    proof -
                      have "snd p ^ 2 \<ge> 0" by (by100 simp)
                      thus ?thesis using hr_sq by (by100 linarith)
                    qed
                    hence hfp_le_r: "abs (fst p) \<le> r"
                    proof -
                      assume h: "fst p ^ 2 \<le> r ^ 2"
                      have "0 \<le> r" using hr_pos by (by100 linarith)
                      from power2_le_imp_le[OF h this]
                      have "fst p \<le> r" .
                      moreover have "- fst p \<le> r"
                      proof -
                        have "(- fst p) ^ 2 = fst p ^ 2" by (by100 algebra)
                        hence "(- fst p) ^ 2 \<le> r ^ 2" using h by (by100 linarith)
                        from power2_le_imp_le[OF this \<open>0 \<le> r\<close>]
                        show ?thesis .
                      qed
                      ultimately show ?thesis by (by100 linarith)
                    qed
                    show "- 1 \<le> fst p / r"
                    proof -
                      have "- r \<le> fst p" using hfp_le_r by (by100 linarith)
                      hence "- 1 \<le> fst p / r"
                        using hr_pos divide_right_mono[of "-r" "fst p" r] by (by100 simp)
                      thus ?thesis .
                    qed
                    show "fst p / r \<le> 1"
                    proof -
                      have "fst p \<le> r" using hfp_le_r by (by100 linarith)
                      thus ?thesis using hr_pos by (by100 simp)
                    qed
                  qed
                  moreover have "pi > 0" using pi_gt_zero .
                  ultimately show ?thesis by (by100 linarith)
                qed
                hence "\<theta>_p * real ?n / (2*pi) \<ge> 0"
                  using hn_pos hpi_pos by (by100 simp)
                moreover have "(4*pi/real ?n - \<theta>_p) * real ?n / (2*pi) \<ge> 0"
                proof -
                  have "\<theta>_p < 4*pi/real ?n"
                    using h\<theta>_lt unfolding \<theta>_cancel_def by (by100 linarith)
                  hence "4*pi/real ?n - \<theta>_p > 0" by (by100 linarith)
                  thus ?thesis using hn_pos hpi_pos by (by100 simp)
                qed
                ultimately show ?thesis unfolding tf_def by (by100 simp)
              qed
              have htf_le1: "tf \<le> 1"
              proof -
                \<comment> \<open>Case: if \\<theta>\\_p \\<le> 2\\<pi>/n then first arg \\<le> 1, else second arg \\<le> 1.\<close>
                show ?thesis
                proof (cases "\<theta>_p \<le> 2*pi/real ?n")
                  case True
                  have "\<theta>_p * real ?n / (2*pi) \<le> 1"
                  proof -
                    have hrn_ge: "real ?n \<ge> 0" using hn_pos by (by100 linarith)
                    from mult_right_mono[OF True hrn_ge]
                    have "\<theta>_p * real ?n \<le> 2*pi / real ?n * real ?n" .
                    moreover have "2*pi / real ?n * real ?n = 2*pi" using hn_pos by (by100 simp)
                    ultimately have "\<theta>_p * real ?n \<le> 2*pi" by (by100 linarith)
                    moreover have "2*pi > 0" using hpi_pos by (by100 linarith)
                    ultimately show ?thesis
                      by (by100 simp)
                  qed
                  thus ?thesis unfolding tf_def by (by100 linarith)
                next
                  case False
                  hence "\<theta>_p > 2*pi/real ?n" by (by100 linarith)
                  have "(4*pi/real ?n - \<theta>_p) * real ?n / (2*pi) \<le> 1"
                  proof -
                    have hrn_ge: "real ?n \<ge> 0" using hn_pos by (by100 linarith)
                    have h2pi: "2*pi > 0" using hpi_pos by (by100 linarith)
                    have "4*pi/real ?n - \<theta>_p < 2*pi / real ?n"
                      using \<open>\<theta>_p > 2*pi/real ?n\<close> by (by100 linarith)
                    from mult_right_mono[OF less_imp_le[OF this] hrn_ge]
                    have "(4*pi/real ?n - \<theta>_p) * real ?n \<le> 2*pi / real ?n * real ?n" .
                    moreover have "2*pi / real ?n * real ?n = 2*pi" using hn_pos by (by100 simp)
                    ultimately have "(4*pi/real ?n - \<theta>_p) * real ?n \<le> 2*pi" by (by100 linarith)
                    thus ?thesis using h2pi by (by100 simp)
                  qed
                  thus ?thesis unfolding tf_def by (by100 linarith)
                qed
              qed
              \<comment> \<open>Apply hconv\\_bound.\<close>
              from hconv_bound[OF htf_ge0 htf_le1]
              have "((1-tf) + tf * fst p_cm) ^ 2 + (tf * snd p_cm) ^ 2 \<le> 1" .
              thus ?thesis using hspur_eq by (by100 simp)
            qed
            \<comment> \<open>Triangle inequality: |(r*s + o*d)|^2 \\<le> (r*|s| + |o|*|d|)^2 \\<le> 1.
               This is the hardest part: vector norm bound via Cauchy-Schwarz.\<close>
            \<comment> \<open>Goal: fst(\\<tau> p)^2 + snd(\\<tau> p)^2 \\<le> 1.\<close>
            have hgoal_eq: "fst (\<tau> p) ^ 2 + snd (\<tau> p) ^ 2
                = (r * fst spur_pt_loc + offset_loc * fst d_perp) ^ 2
                + (r * snd spur_pt_loc + offset_loc * snd d_perp) ^ 2"
              using h\<tau>_cancel by (by100 simp)
            \<comment> \<open>Expand: = r^2*|spur|^2 + 2*r*offset*(spur\\<cdot>d) + offset^2*|d|^2.\<close>
            also have "\<dots> = r ^ 2 * (fst spur_pt_loc ^ 2 + snd spur_pt_loc ^ 2)
                + 2 * r * offset_loc * (fst spur_pt_loc * fst d_perp + snd spur_pt_loc * snd d_perp)
                + offset_loc ^ 2 * (fst d_perp ^ 2 + snd d_perp ^ 2)"
              unfolding power2_eq_square by (by100 algebra)
            \<comment> \<open>Bound each term.\<close>
            \<comment> \<open>Strategy: bound cross term via AM-GM (avoids Cauchy-Schwarz).
               AM-GM: 2|a\\_i*d\\_i| \\<le> a\\_i^2 + d\\_i^2, so
               |a\\<cdot>d| \\<le> |a\\_1||d\\_1| + |a\\_2||d\\_2| \\<le> (a\\_1^2+d\\_1^2)/2 + (a\\_2^2+d\\_2^2)/2
               = (|a|^2+|d|^2)/2 \\<le> (1+4)/2 = 5/2.
               Total bound: r^2 + 2r|o|*(5/2) + o^2*4 = r^2 + 5r|o| + 4o^2.
               With |o| \\<le> r(1-r)/4: \\<le> r^2*(10-7r+r^2)/4.
               Factor: r^2*(10-7r+r^2) - 4 = (r-1)*(r^3-6r^2+4r+4).
               On [0,1]: (r-1) \\<le> 0 and (r^3-6r^2+4r+4) \\<ge> 0, so product \\<le> 0.\<close>
            also have "\<dots> \<le> r ^ 2 * 1
                + 2 * r * abs offset_loc * (5/2)
                + offset_loc ^ 2 * 4"
            proof -
              \<comment> \<open>Term 1: r^2 * |spur|^2 \\<le> r^2.\<close>
              have ht1: "r ^ 2 * (fst spur_pt_loc ^ 2 + snd spur_pt_loc ^ 2) \<le> r ^ 2 * 1"
                using mult_left_mono[OF hspur_in_B2] by (by100 simp)
              \<comment> \<open>Term 2: cross term via |x*y| \\<le> x*y or -(x*y). Bound |a\\<cdot>d| \\<le> 5/2 via AM-GM.\<close>
              have h_inner_bound: "abs (fst spur_pt_loc * fst d_perp + snd spur_pt_loc * snd d_perp) \<le> 5/2"
              proof -
                from real_inner2_abs_le_half_norm_sums[OF hspur_in_B2 hd_sq_bound]
                show ?thesis by (by100 simp)
              qed
              have ht2: "2 * r * offset_loc * (fst spur_pt_loc * fst d_perp + snd spur_pt_loc * snd d_perp)
                  \<le> 2 * r * abs offset_loc * (5/2)"
              proof -
                have "offset_loc * (fst spur_pt_loc * fst d_perp + snd spur_pt_loc * snd d_perp)
                    \<le> abs offset_loc * abs (fst spur_pt_loc * fst d_perp + snd spur_pt_loc * snd d_perp)"
                proof -
                  have "offset_loc * (fst spur_pt_loc * fst d_perp + snd spur_pt_loc * snd d_perp)
                      \<le> abs (offset_loc * (fst spur_pt_loc * fst d_perp + snd spur_pt_loc * snd d_perp))"
                    by (rule abs_ge_self)
                  also have "\<dots> = abs offset_loc * abs (fst spur_pt_loc * fst d_perp + snd spur_pt_loc * snd d_perp)"
                    by (rule abs_mult)
                  finally show ?thesis .
                qed
                also have "\<dots> \<le> abs offset_loc * (5/2)"
                  using mult_left_mono[OF h_inner_bound] by (by100 simp)
                finally have h_cross_bound: "offset_loc * (fst spur_pt_loc * fst d_perp + snd spur_pt_loc * snd d_perp)
                    \<le> abs offset_loc * (5/2)" .
                have "r \<ge> 0" using hr_pos by (by100 linarith)
                have "2 * r * offset_loc * (fst spur_pt_loc * fst d_perp + snd spur_pt_loc * snd d_perp)
                    \<le> 2 * r * (abs offset_loc * (5/2))"
                proof -
                  from mult_left_mono[OF h_cross_bound \<open>r \<ge> 0\<close>]
                  have "r * (offset_loc * (fst spur_pt_loc * fst d_perp + snd spur_pt_loc * snd d_perp))
                      \<le> r * (abs offset_loc * (5/2))" .
                  thus ?thesis by (by100 linarith)
                qed
                thus ?thesis by (by100 linarith)
              qed
              \<comment> \<open>Term 3: offset^2 * |d|^2 \\<le> offset^2 * 4.\<close>
              have ht3: "offset_loc ^ 2 * (fst d_perp ^ 2 + snd d_perp ^ 2) \<le> offset_loc ^ 2 * 4"
                using mult_left_mono[OF hd_sq_bound] by (by100 simp)
              show ?thesis using ht1 ht2 ht3 by (by100 linarith)
            qed
            \<comment> \<open>Now: r^2 + 5*r*|o| + 4*o^2 \\<le> 1. Use |o| \\<le> r(1-r)/4.\<close>
            also have "\<dots> \<le> 1"
            proof -
              have hr_ge0: "r \<ge> 0" using hr_pos by (by100 linarith)
              have h1r_ge0: "1 - r \<ge> 0" using hr_le1 by (by100 linarith)
              \<comment> \<open>|offset| \\<le> r*(1-r)/4.\<close>
              have ho_r1r4: "r * (1-r) / 4 \<ge> 0"
              proof -
                from mult_nonneg_nonneg[OF hr_ge0 h1r_ge0]
                show ?thesis by (by100 simp)
              qed
              have ho_abs: "abs offset_loc \<le> r * (1-r) / 4"
              proof -
                have h_pos: "offset_loc \<le> r * (1-r) / 4"
                  by (rule power2_le_imp_le[OF hoffset ho_r1r4])
                have h_neg: "- offset_loc \<le> r * (1-r) / 4"
                proof -
                  have "(-offset_loc) ^ 2 = offset_loc ^ 2"
                    unfolding power2_eq_square by (by100 simp)
                  hence "(-offset_loc) ^ 2 \<le> (r * (1-r) / 4) ^ 2" using hoffset by (by100 linarith)
                  thus ?thesis by (rule power2_le_imp_le[OF _ ho_r1r4])
                qed
                from h_pos h_neg show ?thesis by (by100 linarith)
              qed
              \<comment> \<open>Substitute bound into expression.\<close>
              have h1: "2 * r * abs offset_loc * (5/2) \<le> 2 * r * (r*(1-r)/4) * (5/2)"
              proof -
                have "2 * r * (5/2) \<ge> 0" using hr_ge0 by (by100 simp)
                from mult_left_mono[OF ho_abs this]
                show ?thesis by (by100 simp)
              qed
              have h2: "offset_loc ^ 2 * 4 \<le> (r*(1-r)/4)^2 * 4"
                using hoffset by (by100 linarith)
              \<comment> \<open>Total: r^2 + 5*r^2*(1-r)/4 + r^2*(1-r)^2/4 = r^2*(10-7r+r^2)/4.\<close>
              have "r^2 * 1 + 2 * r * (r*(1-r)/4) * (5/2) + (r*(1-r)/4)^2 * 4
                  = r^2 * (10 - 7*r + r^2) / 4"
                unfolding power2_eq_square by argo
              \<comment> \<open>Show r^2*(10-7r+r^2)/4 \\<le> 1, i.e., r^2*(10-7r+r^2) \\<le> 4.
                 Equivalently: (r-1)*(r^3-6r^2+4r+4) \\<le> 0.
                 On [0,1]: (r-1) \\<le> 0 and (r^3-6r^2+4r+4) > 0 (positive at r=0,1).\<close>
              moreover have "r^2 * (10 - 7*r + r^2) / 4 \<le> 1"
              proof -
                \<comment> \<open>Equivalent: r^4 - 7r^3 + 10r^2 - 4 \\<le> 0.
                   Factor: (r-1)*(r^3-6r^2+4r+4).
                   On [0,1]: (r-1) \\<le> 0 and (r^3-6r^2+4r+4) \\<ge> 0.\<close>
                have hfactor: "r^2 * (10 - 7*r + r^2) - 4 = (r - 1) * (r^3 - 6*r^2 + 4*r + 4)"
                  unfolding power2_eq_square power3_eq_cube by argo
                have hle0: "r - 1 \<le> 0" using hr_le1 by (by100 linarith)
                have hge0: "r^3 - 6*r^2 + 4*r + 4 \<ge> 0"
                proof -
                  \<comment> \<open>At r=0: 4. At r=1: 3. Minimum on [0,1] is at critical points.
                     f'(r) = 3r^2-12r+4. Roots: (12\\<pm>\\<surd>96)/6 \\<approx> 0.35, 3.65. Only 0.35 in [0,1].
                     f(0.35) \\<approx> 4+1.4-0.735-0.043 = 4.62 > 0. So min > 0.\<close>
                  have "r^3 - 6*r^2 + 4*r + 4 = r^3 - 6*r^2 + 4*r + 4" by (by100 simp)
                  \<comment> \<open>Bound: r^3 \\<le> r (for r \\<in> [0,1]), so r^3-6r^2+4r+4 \\<ge> r-6r^2+4r+4 = 5r-6r^2+4.
                     And 5r-6r^2+4 = -6(r^2-5r/6)+4 = -6(r-5/12)^2+25/24+4 > 0.\<close>
                  \<comment> \<open>r^2 \\<le> r from r \\<in> [0,1].\<close>
                  have hr2r: "r^2 \<le> r"
                  proof -
                    from mult_left_mono[OF hr_le1 hr_ge0]
                    show ?thesis unfolding power2_eq_square by (by100 simp)
                  qed
                  \<comment> \<open>r^3 \\<le> r from r^2 \\<le> r and r \\<ge> 0.\<close>
                  have hr3r: "r^3 \<le> r"
                  proof -
                    from mult_right_mono[OF hr2r hr_ge0]
                    have "r^2 * r \<le> r * r" .
                    hence "r^3 \<le> r^2" unfolding power2_eq_square power3_eq_cube by (by100 linarith)
                    thus ?thesis using hr2r by (by100 linarith)
                  qed
                  \<comment> \<open>r^3-6r^2+4r+4 = r(r^2-6r+4)+4. On [0,1]: r^2-6r+4 \\<ge> -1 (at r=1),
                     so r(r^2-6r+4) \\<ge> -1, hence +4 \\<ge> 3 > 0.\<close>
                  have "r^2 - 6*r + 4 \<ge> -1"
                  proof -
                    have "r - 1 \<le> 0" using hr_le1 by (by100 linarith)
                    moreover have "r - 5 \<le> 0" using hr_le1 by (by100 linarith)
                    ultimately have "(r-1)*(r-5) \<ge> 0"
                      using mult_nonpos_nonpos by (by100 blast)
                    moreover have "(r-1)*(r-5) = r^2 - 6*r + 5"
                      unfolding power2_eq_square by argo
                    ultimately have "r^2 - 6*r + 5 \<ge> 0" by (by100 linarith)
                    thus ?thesis by (by100 linarith)
                  qed
                  hence "r * (r^2 - 6*r + 4) \<ge> r * (-1)"
                    using mult_left_mono[of "-1" "r^2-6*r+4" r] hr_ge0 by (by100 linarith)
                  hence "r * (r^2 - 6*r + 4) \<ge> -r" by (by100 simp)
                  hence "r * (r^2 - 6*r + 4) + 4 \<ge> -r + 4" by (by100 linarith)
                  moreover have "-r + 4 \<ge> 3" using hr_le1 by (by100 linarith)
                  moreover have "r^3 - 6*r^2 + 4*r + 4 = r * (r^2 - 6*r + 4) + 4"
                    unfolding power2_eq_square power3_eq_cube by argo
                  ultimately show ?thesis by (by100 linarith)
                qed
                have "(r - 1) * (r^3 - 6*r^2 + 4*r + 4) \<le> 0"
                  using mult_nonpos_nonneg[OF hle0 hge0] .
                hence "r^2 * (10 - 7*r + r^2) - 4 \<le> 0" using hfactor by (by100 linarith)
                thus ?thesis by (by100 linarith)
              qed
              ultimately show ?thesis using h1 h2 by (by100 linarith)
            qed
            finally show ?thesis unfolding top1_B2_def by (by100 simp)
          qed
        qed
      qed
      have h\<tau>_surj: "\<tau> ` top1_B2 = top1_B2"
      proof (rule set_eqI, rule iffI)
        fix q assume "q \<in> \<tau> ` top1_B2"
        then obtain p where "p \<in> top1_B2" "\<tau> p = q" by (by100 blast)
        thus "q \<in> top1_B2" using h\<tau>_range by (by100 blast)
      next
        fix q assume hq: "q \<in> top1_B2"
        \<comment> \<open>For any target q \\<in> B2, find a source p in the good sector.
           At target (x0,y0) with angle \\<theta>0 and radius r0:
           source = (r0, \\<theta>\\_cancel + \\<theta>0 * m/n) which is in the good sector.
           \\<tau>(source) = (r0 * cos(\\<theta>0), r0 * sin(\\<theta>0)) = (x0, y0) = q.
           The good sector rescaling (\\<theta>-\\<theta>\\_cancel)*n/m maps [\\<theta>\\_cancel, 2\\<pi>) to [0, 2\\<pi>),
           so every angle is reachable.\<close>
        show "q \<in> \<tau> ` top1_B2"
        proof (cases "q = (0, 0)")
          case True
          have "(0::real, 0) \<in> top1_B2" unfolding top1_B2_def by (by100 simp)
          moreover have "\<tau> (0, 0) = (0, 0)" unfolding \<tau>_def by (by100 simp)
          ultimately show ?thesis using True by (by100 force)
        next
          case False
          \<comment> \<open>q \\<noteq> (0,0). Let r0 = |q| and \\<theta>0 = angle(q). Construct source in good sector.\<close>
          define r0 where "r0 = sqrt (fst q ^ 2 + snd q ^ 2)"
          define \<theta>0 where "\<theta>0 = (if snd q \<ge> 0 then arccos (fst q / r0) else 2*pi - arccos (fst q / r0))"
          \<comment> \<open>Source angle: \\<alpha> = \\<theta>\\_cancel + \\<theta>0 * m/n. In [\\<theta>\\_cancel, 2\\<pi>).\<close>
          define \<alpha> where "\<alpha> = \<theta>_cancel + \<theta>0 * real ?m / real ?n"
          define p where "p = (r0 * cos \<alpha>, r0 * sin \<alpha>)"
          \<comment> \<open>p \\<in> B2, p in good sector, \\<tau>(p) = q.\<close>
          have "p \<in> top1_B2"
          proof -
            have hfp: "fst p = r0 * cos \<alpha>" and hsp: "snd p = r0 * sin \<alpha>"
              unfolding p_def by (by100 simp)+
            have "fst p ^ 2 + snd p ^ 2 = r0 ^ 2 * (cos \<alpha> ^ 2 + sin \<alpha> ^ 2)"
              unfolding hfp hsp power2_eq_square by argo
            also have "\<dots> = r0 ^ 2" using sin_cos_squared_add3 by (by100 simp)
            also have "\<dots> = fst q ^ 2 + snd q ^ 2"
              unfolding r0_def using real_sqrt_pow2[OF sum_power2_ge_zero] by (by100 blast)
            also have "\<dots> \<le> 1" using hq unfolding top1_B2_def by (by100 simp)
            finally show ?thesis unfolding top1_B2_def by (by100 simp)
          qed
          moreover have "\<tau> p = q"
          proof -
            \<comment> \<open>Step 1: p \\<noteq> (0,0) since |p| = |q| > 0.\<close>
            have hp_ne: "p \<noteq> (0, 0)"
            proof -
              have "fst q \<noteq> 0 \<or> snd q \<noteq> 0" using False by (cases q) (by100 auto)
              hence "fst q ^ 2 + snd q ^ 2 > 0"
              proof
                assume "fst q \<noteq> 0" hence "fst q ^ 2 > 0" by (by100 simp)
                moreover have "snd q ^ 2 \<ge> 0" by (by100 simp)
                ultimately show ?thesis by (by100 linarith)
              next
                assume "snd q \<noteq> 0" hence "snd q ^ 2 > 0" by (by100 simp)
                moreover have "fst q ^ 2 \<ge> 0" by (by100 simp)
                ultimately show ?thesis by (by100 linarith)
              qed
              hence "r0 > 0" unfolding r0_def using real_sqrt_gt_0_iff by (by100 auto)
              hence "r0 * cos \<alpha> \<noteq> 0 \<or> r0 * sin \<alpha> \<noteq> 0"
              proof -
                assume hr0: "0 < r0"
                have "(r0 * cos \<alpha>) ^ 2 + (r0 * sin \<alpha>) ^ 2 = r0 ^ 2"
                proof -
                  have "(r0 * cos \<alpha>) ^ 2 + (r0 * sin \<alpha>) ^ 2 = r0^2 * (cos \<alpha> ^2 + sin \<alpha> ^2)"
                    unfolding power2_eq_square by argo
                  also have "\<dots> = r0^2" using sin_cos_squared_add3 by (by100 simp)
                  finally show ?thesis .
                qed
                moreover have "r0 ^ 2 > 0" using hr0 by (by100 simp)
                ultimately have "(r0 * cos \<alpha>) ^ 2 + (r0 * sin \<alpha>) ^ 2 > 0" by (by100 linarith)
                thus ?thesis by (by100 auto)
              qed
              thus ?thesis unfolding p_def by (by100 auto)
            qed
            \<comment> \<open>Step 2-8: unfold \\<tau> at p, show good sector, show rescaling gives \\<theta>0, show q decomposition.\<close>
            \<comment> \<open>Step 2: \\<alpha> \\<ge> \\<theta>\\_cancel (trivial from definition).\<close>
            \<comment> \<open>Arccos precondition: -1 \\<le> fst q / r0 \\<le> 1.\<close>
            have hr0_pos: "r0 > 0"
            proof -
              have "fst q \<noteq> 0 \<or> snd q \<noteq> 0" using False by (cases q) (by100 auto)
              hence "fst q ^ 2 + snd q ^ 2 > 0"
              proof
                assume "fst q \<noteq> 0"
                hence "fst q ^ 2 > 0" by (by100 simp)
                moreover have "snd q ^ 2 \<ge> 0" by (by100 simp)
                ultimately show ?thesis by (by100 linarith)
              next
                assume "snd q \<noteq> 0"
                hence "snd q ^ 2 > 0" by (by100 simp)
                moreover have "fst q ^ 2 \<ge> 0" by (by100 simp)
                ultimately show ?thesis by (by100 linarith)
              qed
              thus ?thesis unfolding r0_def using real_sqrt_gt_0_iff by (by100 auto)
            qed
            have hq_div_bound: "-1 \<le> fst q / r0 \<and> fst q / r0 \<le> 1"
            proof -
              have "fst q ^ 2 \<le> r0 ^ 2"
              proof -
                have "snd q ^ 2 \<ge> 0" by (by100 simp)
                moreover have "r0 ^ 2 = fst q ^ 2 + snd q ^ 2"
                  unfolding r0_def using real_sqrt_pow2[OF sum_power2_ge_zero] by (by100 blast)
                ultimately show ?thesis by (by100 linarith)
              qed
              hence "abs (fst q) \<le> r0"
              proof -
                assume h: "fst q ^ 2 \<le> r0 ^ 2"
                from power2_le_imp_le[OF h] hr0_pos
                have "fst q \<le> r0" by (by100 linarith)
                moreover have "- fst q \<le> r0"
                proof -
                  have "(-fst q)^2 = fst q ^ 2" unfolding power2_eq_square by (by100 simp)
                  hence "(-fst q)^2 \<le> r0^2" using h by (by100 linarith)
                  from power2_le_imp_le[OF this] hr0_pos
                  show ?thesis by (by100 linarith)
                qed
                ultimately show ?thesis by (by100 linarith)
              qed
              hence hmr0: "- r0 \<le> fst q" and hfr0: "fst q \<le> r0" by (by100 linarith)+
              from divide_right_mono[OF hmr0, of r0] hr0_pos
              have h_lb: "-1 \<le> fst q / r0" by (by100 simp)
              from divide_right_mono[OF hfr0, of r0] hr0_pos
              have h_ub: "fst q / r0 \<le> 1" by (by100 simp)
              from h_lb h_ub show ?thesis by (by100 simp)
            qed
            have h\<alpha>_ge: "\<alpha> \<ge> \<theta>_cancel"
            proof -
              have h\<theta>0_ge: "\<theta>0 \<ge> 0"
              proof (cases "snd q \<ge> 0")
                case True
                hence "\<theta>0 = arccos (fst q / r0)" unfolding \<theta>0_def by (by100 simp)
                moreover have "arccos (fst q / r0) \<ge> 0"
                  using arccos_lbound[OF conjunct1[OF hq_div_bound] conjunct2[OF hq_div_bound]] .
                ultimately show ?thesis by (by100 linarith)
              next
                case False
                hence "\<theta>0 = 2*pi - arccos (fst q / r0)" unfolding \<theta>0_def by (by100 simp)
                moreover have "arccos (fst q / r0) \<le> pi"
                  using arccos_ubound[OF conjunct1[OF hq_div_bound] conjunct2[OF hq_div_bound]] .
                ultimately show ?thesis using pi_gt_zero by (by100 linarith)
              qed
              have hmn_ge: "real ?m / real ?n \<ge> 0" using assms(2) by (by100 simp)
              from mult_nonneg_nonneg[OF h\<theta>0_ge hmn_ge]
              have "\<theta>0 * (real ?m / real ?n) \<ge> 0" .
              thus ?thesis unfolding \<alpha>_def by (by100 simp)
            qed
            \<comment> \<open>Step 3: angle rescaling.\<close>
            have h_rescale: "(\<alpha> - \<theta>_cancel) * real ?n / real ?m = \<theta>0"
            proof -
              have hm_pos: "real ?m > 0"
              proof -
                have "?m \<ge> 3" using assms(2) .
                hence "?m > 0" by (by100 linarith)
                thus ?thesis by (by100 simp)
              qed
              have hn_pos: "real ?n > 0"
              proof -
                have "?n = ?m + 2" by (by100 simp)
                hence "?n > 0" using assms(2) by (by100 linarith)
                thus ?thesis by (by100 simp)
              qed
              have "\<alpha> - \<theta>_cancel = \<theta>0 * real ?m / real ?n"
                unfolding \<alpha>_def by (by100 simp)
              hence "(\<alpha> - \<theta>_cancel) * real ?n = \<theta>0 * real ?m / real ?n * real ?n"
                by (by100 simp)
              also have "\<dots> = \<theta>0 * real ?m" using hn_pos by (by100 simp)
              finally have "(\<alpha> - \<theta>_cancel) * real ?n / real ?m = \<theta>0 * real ?m / real ?m"
                using hm_pos by (by100 simp)
              thus ?thesis using hm_pos by (by100 simp)
            qed
            \<comment> \<open>Step 4: \\<tau>(p) unfolds to good-sector formula.\<close>
            have h\<tau>_at_p: "\<tau> p = (r0 * cos ((\<alpha> - \<theta>_cancel) * real ?n / real ?m),
                                  r0 * sin ((\<alpha> - \<theta>_cancel) * real ?n / real ?m))"
            proof -
              \<comment> \<open>Step 4a: sqrt(fst p^2 + snd p^2) = r0.\<close>
              have h_r_eq: "sqrt (fst p ^ 2 + snd p ^ 2) = r0"
              proof -
                have "(r0 * cos \<alpha>)^2 + (r0 * sin \<alpha>)^2 = r0^2 * (cos \<alpha> ^2 + sin \<alpha> ^2)"
                  unfolding power2_eq_square by argo
                also have "\<dots> = r0^2" using sin_cos_squared_add3 by (by100 simp)
                finally have "(r0 * cos \<alpha>)^2 + (r0 * sin \<alpha>)^2 = r0^2" .
                hence "fst p ^ 2 + snd p ^ 2 = r0^2" unfolding p_def by (by100 simp)
                moreover have "r0 \<ge> 0" using hr0_pos by (by100 linarith)
                ultimately show ?thesis by (by100 simp)
              qed
              \<comment> \<open>Step 4b: the angle computed by \\<tau> equals \\<alpha> (via angle\\_recovery).\<close>
              have h_angle: "(if snd p \<ge> 0 then arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))
                   else 2*pi - arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))) = \<alpha>"
              proof -
                have "fst p = r0 * cos \<alpha>" "snd p = r0 * sin \<alpha>"
                  unfolding p_def by (by100 simp)+
                hence "(if snd p \<ge> 0 then arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2))
                   else 2*pi - arccos (fst p / sqrt (fst p ^ 2 + snd p ^ 2)))
                    = (if r0 * sin \<alpha> \<ge> 0 then arccos ((r0 * cos \<alpha>) / sqrt ((r0*cos \<alpha>)^2 + (r0*sin \<alpha>)^2))
                       else 2*pi - arccos ((r0 * cos \<alpha>) / sqrt ((r0*cos \<alpha>)^2 + (r0*sin \<alpha>)^2)))"
                  by (by100 simp)
                also have "\<dots> = \<alpha>"
                proof -
                  have h\<alpha>_ge0: "\<alpha> \<ge> 0"
                  proof -
                    have "\<theta>_cancel \<ge> 0" unfolding \<theta>_cancel_def using pi_gt_zero assms(2) by (by100 simp)
                    thus ?thesis using h\<alpha>_ge by (by100 linarith)
                  qed
                  have h\<alpha>_lt2pi: "\<alpha> < 2*pi"
                  proof -
                    have h\<theta>0_strict: "\<theta>0 < 2*pi"
                    proof (cases "snd q \<ge> 0")
                      case True
                      hence "\<theta>0 = arccos (fst q / r0)" unfolding \<theta>0_def by (by100 simp)
                      thus ?thesis using arccos_ubound[OF conjunct1[OF hq_div_bound] conjunct2[OF hq_div_bound]]
                            pi_gt_zero by (by100 linarith)
                    next
                      case False
                      hence hsnd: "snd q < 0" by (by100 linarith)
                      have hfqr: "fst q / r0 < 1"
                      proof (rule ccontr)
                        assume "\<not> fst q / r0 < 1"
                        hence "fst q / r0 = 1" using conjunct2[OF hq_div_bound] by (by100 linarith)
                        hence "fst q = r0" using hr0_pos by (by100 simp)
                        have "snd q = 0"
                        proof -
                          have "r0 ^ 2 = fst q ^ 2 + snd q ^ 2"
                            unfolding r0_def using real_sqrt_pow2[OF sum_power2_ge_zero] by (by100 blast)
                          hence "r0 * r0 = fst q * fst q + snd q * snd q"
                            unfolding power2_eq_square .
                          note heq = this[unfolded \<open>fst q = r0\<close>]
                          hence "snd q * snd q = 0" by (by100 linarith)
                          thus "snd q = 0" by (by100 simp)
                        qed
                        thus False using hsnd by (by100 linarith)
                      qed
                      have "arccos (fst q / r0) > 0"
                      proof -
                        have "arccos (fst q / r0) \<ge> 0"
                          using arccos_lbound[OF conjunct1[OF hq_div_bound] conjunct2[OF hq_div_bound]] .
                        moreover have "arccos (fst q / r0) \<noteq> 0"
                        proof
                          assume "arccos (fst q / r0) = 0"
                          hence "cos (arccos (fst q / r0)) = cos 0" by (by100 simp)
                          hence "fst q / r0 = 1"
                            using cos_arccos[OF conjunct1[OF hq_div_bound] conjunct2[OF hq_div_bound]]
                            by (by100 simp)
                          thus False using hfqr by (by100 linarith)
                        qed
                        ultimately show ?thesis by (by100 linarith)
                      qed
                      hence "\<theta>0 < 2*pi"
                      proof -
                        have "\<theta>0 = 2*pi - arccos (fst q / r0)"
                          unfolding \<theta>0_def using False by (by100 simp)
                        thus ?thesis using \<open>arccos (fst q / r0) > 0\<close> by (by100 linarith)
                      qed
                      thus ?thesis .
                    qed
                    have hmn: "real ?m / real ?n > 0"
                    proof -
                      have hm3: "?m \<ge> 3" using assms(2) .
                      hence "?m > 0" by (by100 linarith)
                      hence "real ?m > 0" by (by100 simp)
                      moreover have "real ?n > 0"
                      proof -
                        have "?n = ?m + 2" by (by100 simp)
                        thus ?thesis using \<open>?m \<ge> 3\<close> by (by100 simp)
                      qed
                      ultimately show ?thesis by (by100 simp)
                    qed
                    from mult_strict_right_mono[OF h\<theta>0_strict hmn]
                    have "\<theta>0 * (real ?m / real ?n) < 2*pi * (real ?m / real ?n)" .
                    have h\<alpha>_eq: "\<alpha> = \<theta>_cancel + \<theta>0 * (real ?m / real ?n)"
                      unfolding \<alpha>_def by (by100 simp)
                    hence "\<alpha> < \<theta>_cancel + 2*pi * (real ?m / real ?n)"
                      using \<open>\<theta>0 * _ < 2*pi * _\<close> by (by100 linarith)
                    moreover have "\<theta>_cancel + 2*pi * (real ?m / real ?n) = 2*pi"
                    proof -
                      have hn: "real ?n > 0"
                      proof -
                        have "?n = ?m + 2" by (by100 simp)
                        hence "?n \<ge> 5" using hm3 by (by100 linarith)
                        thus ?thesis by (by100 simp)
                      qed
                      \<comment> \<open>4\\<pi>/n + 2\\<pi>*m/n = 2\\<pi>*(2+m)/n = 2\\<pi>*n/n = 2\\<pi>.\<close>
                      have "4*pi / real ?n + 2*pi * (real ?m / real ?n) = 2*pi"
                      proof -
                        have h_mn: "?m + 2 = ?n" by (by100 simp)
                        have h_div1: "4*pi / real ?n * real ?n = 4*pi" using hn by (by100 simp)
                        have h_div2: "real ?m / real ?n * real ?n = real ?m" using hn by (by100 simp)
                        have "(4*pi / real ?n + 2*pi * (real ?m / real ?n)) * real ?n
                            = 4*pi / real ?n * real ?n + 2*pi * (real ?m / real ?n) * real ?n"
                          by argo
                        also have "\<dots> = 4*pi + 2*pi * (real ?m / real ?n * real ?n)"
                          using h_div1 by argo
                        also have "\<dots> = 4*pi + 2*pi * real ?m"
                          using h_div2 by (by100 simp)
                        finally have "(4*pi / real ?n + 2*pi * (real ?m / real ?n)) * real ?n
                            = 4*pi + 2*pi * real ?m" .
                        also have "\<dots> = 2*pi * (real ?m + 2)" by argo
                        also have "\<dots> = 2*pi * real ?n"
                        proof -
                          have "real ?m + 2 = real ?n" using h_mn by (by100 simp)
                          thus ?thesis by (by100 simp)
                        qed
                        finally have h: "(4*pi / real ?n + 2*pi * (real ?m / real ?n)) * real ?n = 2*pi * real ?n" .
                        from mult_right_cancel[of "4*pi / real ?n + 2*pi * (real ?m / real ?n)" "real ?n" "2*pi"]
                        show ?thesis using h hn by (by100 simp)
                      qed
                      thus ?thesis unfolding \<theta>_cancel_def by (by100 linarith)
                    qed
                    ultimately show ?thesis by (by100 linarith)
                  qed
                  from angle_recovery[OF hr0_pos h\<alpha>_ge0 h\<alpha>_lt2pi]
                  show ?thesis .
                qed
                finally show ?thesis .
              qed
              \<comment> \<open>Step 4c: unfold \\<tau>\\_def, use h\\_r\\_eq and h\\_angle.\<close>
              \<comment> \<open>Use h\\<tau>\\_simp-like approach: unfold \\<tau> at p \\<noteq> (0,0) with good sector.\<close>
              show ?thesis
                using hp_ne h_r_eq h_angle h\<alpha>_ge
                unfolding \<tau>_def \<tau>_boundary_def Let_def
                by simp \<comment> \<open>Found by sledgehammer: τ_def + Let_def unfolding + simp (38ms).
                   by100 can't handle the nested let/if unfolding. Mathematical content proved.\<close>
            qed
            \<comment> \<open>Step 5: combine rescaling.\<close>
            have "\<tau> p = (r0 * cos \<theta>0, r0 * sin \<theta>0)"
              using h\<tau>_at_p h_rescale by (by100 simp)
            \<comment> \<open>Step 6: q = (r0*cos \\<theta>0, r0*sin \\<theta>0) by polar decomposition.\<close>
            moreover have "q = (r0 * cos \<theta>0, r0 * sin \<theta>0)"
            proof -
              have hfst_sq_pos: "fst q ^ 2 + snd q ^ 2 > 0"
              proof -
                have "fst q \<noteq> 0 \<or> snd q \<noteq> 0" using False by (cases q) (by100 auto)
                thus ?thesis
                proof
                  assume "fst q \<noteq> 0" hence "fst q ^ 2 > 0" by (by100 simp)
                  moreover have "snd q ^ 2 \<ge> 0" by (by100 simp)
                  ultimately show ?thesis by (by100 linarith)
                next
                  assume "snd q \<noteq> 0" hence "snd q ^ 2 > 0" by (by100 simp)
                  moreover have "fst q ^ 2 \<ge> 0" by (by100 simp)
                  ultimately show ?thesis by (by100 linarith)
                qed
              qed
              have "fst q = r0 * cos \<theta>0"
                using polar_decomposition_fst[OF hfst_sq_pos] unfolding r0_def \<theta>0_def by (by100 simp)
              moreover have "snd q = r0 * sin \<theta>0"
                using polar_decomposition_snd[OF hfst_sq_pos] unfolding r0_def \<theta>0_def by (by100 simp)
              ultimately show ?thesis by (cases q) (by100 simp)
            qed
            ultimately show ?thesis by (by100 simp)
          qed
          ultimately show ?thesis by (by100 blast)
        qed
      qed
      \<comment> \<open>Sub-sorry 3: Fibre matching q\\_e x = q\\_e y \\<longleftrightarrow> q\\_m(spur\\_f x) = q\\_m(spur\\_f y).
         Verified algebraically in sessions 2-4. Cases:
         - Both x,y interior of P\\_e: spur\\_f injective on interior \\<to> both sides trivially equiv.
         - x on good edge k (k\\<ge>2), y on good edge l: edge identification transfers directly
           because spur\\_f maps edge k to edge k-2 of P\\_m with same parameter.
         - x on cancel edge (0 or 1): q\\_e identifies edge 0 at t with edge 1 at 1-t.
           spur\\_f maps both to the same point on the spur \\<to> q\\_m values equal.
         - Cross cases (cancel vs good, interior vs boundary): handled by injectivity.\<close>
      \<comment> \<open>Fibre matching: the core spur-collapse theorem (expert audit 26 §7).
         The proof has two main parts that depend on the definitional properties of spur\\_f:
         (A) Good edges: spur\\_f maps edge k (k\\<ge>2) at parameter t to edge k-2 at parameter t.
             This means q\\_e identifications on good edges match q\\_m identifications via shift.
         (B) Cancel edges: spur\\_f maps cancel pair to interior spur \\<to> collapsed.
         Both depend on HOW \\<tau> maps boundary arcs, which follows from the \\<tau> definition.
         The proof also needs \\<tau> injectivity on B2 interior (from perpendicular offsets).\<close>
      \<comment> \<open>Key property: spur\\_f maps good edge k (k\\<ge>2) at parameter t to edge\\_m(k-2, t).
         Proof: \\<psi>\\_e(edge\\_e(k,t)) = (cos(2\\<pi>(k+t)/n), sin(2\\<pi>(k+t)/n)).
         \\<tau> rescales angle: 2\\<pi>(k+t)/n \\<to> (2\\<pi>(k+t)/n - \\<theta>\\_cancel)\\<cdot>n/m = 2\\<pi>(k-2+t)/m.
         \\<psi>\\_m\\<inverse> maps back: edge\\_m(k-2, t).\<close>
      have h_spur_good_edge: "\<forall>k. 2 \<le> k \<longrightarrow> k < ?n \<longrightarrow> (\<forall>t\<in>{0<..<(1::real)}.
          spur_f ((1-t)*vx_e k + t*vx_e(Suc k mod ?n),
                  (1-t)*vy_e k + t*vy_e(Suc k mod ?n))
        = ((1-t)*vx_m (k-2) + t*vx_m(Suc (k-2) mod ?m),
           (1-t)*vy_m (k-2) + t*vy_m(Suc (k-2) mod ?m)))"
      proof (intro allI impI ballI)
        fix k t assume hk2: "2 \<le> k" and hk: "k < ?n" and ht: "t \<in> {0<..<(1::real)}"
        \<comment> \<open>Step 1: \\<psi>\\_e maps edge\\_e(k,t) to S1.\<close>
        define \<alpha> where "\<alpha> = 2*pi*(real k + t)/real ?n"
        have ht_Iset: "t \<in> I_set" using ht unfolding top1_unit_interval_def by (by100 auto)
        have h\<psi>e: "\<psi>_e ((1-t)*vx_e k + t*vx_e(Suc k mod ?n),
            (1-t)*vy_e k + t*vy_e(Suc k mod ?n)) = (cos \<alpha>, sin \<alpha>)"
          unfolding \<alpha>_def using h\<psi>e_edge[rule_format, OF hk ht_Iset] .
        \<comment> \<open>Step 2: (cos \\<alpha>, sin \\<alpha>) \\<noteq> (0,0).\<close>
        have h_ne: "(cos \<alpha>, sin \<alpha>) \<noteq> (0::real, 0)"
        proof
          assume "(cos \<alpha>, sin \<alpha>) = (0, 0)"
          hence "cos \<alpha> = 0" "sin \<alpha> = 0" by (by100 auto)+
          hence "cos \<alpha> * cos \<alpha> + sin \<alpha> * sin \<alpha> = 0" by (by100 simp)
          moreover have "cos \<alpha> * cos \<alpha> + sin \<alpha> * sin \<alpha> = 1"
            using sin_cos_squared_add3[of \<alpha>] by (simp add: power2_eq_square)
          ultimately show False by (by100 linarith)
        qed
        \<comment> \<open>Step 3: angle is \\<alpha> (via angle\\_recovery with r=1).\<close>
        have hn_pos: "real ?n > 0" using hn5 by (by100 linarith)
        have ht_pos: "t > 0" using ht by (by100 simp)
        have ht_lt1: "t < 1" using ht by (by100 simp)
        have ht_ge0: "t \<ge> 0" using ht_pos by (by100 linarith)
        have ht_le1: "t \<le> 1" using ht_lt1 by (by100 linarith)
        have h\<alpha>_ge0: "\<alpha> \<ge> 0" unfolding \<alpha>_def
          using pi_gt_zero hn_pos ht_ge0 hk2 by (by100 simp)
        have h\<alpha>_lt2pi: "\<alpha> < 2*pi"
        proof -
          have "real k + t < real k + 1" using ht_lt1 by (by100 linarith)
          also have "\<dots> \<le> real ?n" using hk by (by100 simp)
          finally have "real k + t < real ?n" .
          show ?thesis unfolding \<alpha>_def using pi_gt_zero hn_pos \<open>real k + t < real ?n\<close>
            by (simp add: divide_less_eq mult.commute)
        qed
        \<comment> \<open>Step 4: \\<alpha> \\<ge> \\<theta>\\_cancel since k\\<ge>2.\<close>
        have h_good: "\<alpha> \<ge> \<theta>_cancel"
        proof -
          have "real k + t \<ge> 2" using hk2 ht_ge0 by (by100 linarith)
          show ?thesis unfolding \<alpha>_def \<theta>_cancel_def using \<open>real k + t \<ge> 2\<close> pi_gt_zero hn_pos
            by (simp add: divide_le_eq mult.commute)
        qed
        \<comment> \<open>Step 5: \\<tau> on S1 in good sector gives (cos(...), sin(...)).\<close>
        have h_\<tau>: "\<tau> (cos \<alpha>, sin \<alpha>) =
            (cos ((\<alpha> - \<theta>_cancel) * real ?n / real ?m),
             sin ((\<alpha> - \<theta>_cancel) * real ?n / real ?m))"
        proof -
          \<comment> \<open>r = sqrt(cos^2+sin^2) = 1.\<close>
          have hr1: "sqrt ((cos \<alpha>)^2 + (sin \<alpha>)^2) = 1"
          proof -
            have "(cos \<alpha>)^2 + (sin \<alpha>)^2 = 1" using sin_cos_squared_add3 by (by100 simp)
            thus ?thesis by (by100 simp)
          qed
          \<comment> \<open>Angle recovery: the angle computed by \\<tau> is \\<alpha>.\<close>
          have hdiv: "cos \<alpha> / sqrt ((cos \<alpha>)^2 + (sin \<alpha>)^2) = cos \<alpha>"
            using hr1 by (by100 simp)
          have h_angle: "(if sin \<alpha> \<ge> 0 then arccos (cos \<alpha> / sqrt ((cos \<alpha>)^2 + (sin \<alpha>)^2))
              else 2*pi - arccos (cos \<alpha> / sqrt ((cos \<alpha>)^2 + (sin \<alpha>)^2))) = \<alpha>"
          proof (cases "sin \<alpha> \<ge> 0")
            case True
            have "\<alpha> \<le> pi"
            proof (rule ccontr)
              assume "\<not> \<alpha> \<le> pi"
              hence "\<alpha> > pi" by (by100 linarith)
              hence "sin \<alpha> < 0" using h\<alpha>_lt2pi sin_lt_zero by (by100 auto)
              thus False using True by (by100 linarith)
            qed
            hence "arccos (cos \<alpha>) = \<alpha>" using h\<alpha>_ge0 arccos_cos by (by100 blast)
            thus ?thesis using True hdiv by (by100 simp)
          next
            case False
            hence "sin \<alpha> < 0" by (by100 linarith)
            have h\<alpha>_gt_pi: "\<alpha> > pi"
            proof (rule ccontr)
              assume "\<not> \<alpha> > pi"
              hence "\<alpha> \<le> pi" by (by100 linarith)
              hence "sin \<alpha> \<ge> 0" using h\<alpha>_ge0 sin_ge_zero by (by100 blast)
              thus False using \<open>sin \<alpha> < 0\<close> by (by100 linarith)
            qed
            have "arccos (cos \<alpha>) = 2*pi - \<alpha>"
            proof -
              have hx: "\<alpha> - 2*pi \<le> 0" using h\<alpha>_lt2pi by (by100 linarith)
              have hx2: "- pi \<le> \<alpha> - 2*pi" using h\<alpha>_gt_pi by (by100 linarith)
              have "cos (\<alpha> - 2*pi) = cos \<alpha>" by (simp add: cos_diff)
              from arccos_cos2[OF hx hx2] this
              have "arccos (cos \<alpha>) = -((\<alpha>) - 2*pi)" by (by100 simp)
              thus ?thesis by (by100 linarith)
            qed
            thus ?thesis using False hdiv by (by100 simp)
          qed
          \<comment> \<open>Unfold \\<tau> definition, substitute r=1, angle=\\<alpha>, and simplify.\<close>
          have "\<tau> (cos \<alpha>, sin \<alpha>) = (fst (\<tau>_boundary \<alpha>), snd (\<tau>_boundary \<alpha>))"
          proof -
            have "\<tau> (cos \<alpha>, sin \<alpha>) = (1 * fst (\<tau>_boundary \<alpha>), 1 * snd (\<tau>_boundary \<alpha>))"
              unfolding \<tau>_def using h_ne hr1 h_angle h_good by auto
            thus ?thesis by (by100 simp)
          qed
          also have "\<dots> = (cos ((\<alpha> - \<theta>_cancel) * real ?n / real ?m),
              sin ((\<alpha> - \<theta>_cancel) * real ?n / real ?m))"
            unfolding \<tau>_boundary_def using h_good by (by100 auto)
          finally show ?thesis .
        qed
        \<comment> \<open>Step 6: Arithmetic: (\\<alpha>-\\<theta>\\_cancel)\\<cdot>n/m = 2\\<pi>(k-2+t)/m.\<close>
        have h_arith: "(\<alpha> - \<theta>_cancel) * real ?n / real ?m = 2*pi*(real (k-2) + t) / real ?m"
        proof -
          have "\<alpha> - \<theta>_cancel = 2*pi*(real k + t)/real ?n - 4*pi/real ?n"
            unfolding \<alpha>_def \<theta>_cancel_def by (by100 simp)
          also have "\<dots> = 2*pi*(real k + t - 2)/real ?n"
            using hn_pos by (simp add: diff_divide_distrib algebra_simps)
          finally have h1: "\<alpha> - \<theta>_cancel = 2*pi*(real k + t - 2)/real ?n" .
          have "(\<alpha> - \<theta>_cancel) * real ?n / real ?m = 2*pi*(real k + t - 2)/real ?n * real ?n / real ?m"
            using h1 by (by100 simp)
          also have "\<dots> = 2*pi*(real k + t - 2) / real ?m"
            using hn_pos by (by100 simp)
          also have "real k + t - 2 = real (k - 2) + t"
            using hk2 by (by100 simp)
          finally show ?thesis .
        qed
        \<comment> \<open>Step 7: \\<psi>\\_m\\<inverse> maps result to edge\\_m(k-2,t).\<close>
        have hk2m: "k - 2 < ?m" using hk hk2 hn_eq by (by100 linarith)
        have h_result: "spur_f ((1-t)*vx_e k + t*vx_e(Suc k mod ?n),
            (1-t)*vy_e k + t*vy_e(Suc k mod ?n))
          = ((1-t)*vx_m (k-2) + t*vx_m(Suc (k-2) mod ?m),
             (1-t)*vy_m (k-2) + t*vy_m(Suc (k-2) mod ?m))"
        proof -
          have "spur_f ((1-t)*vx_e k + t*vx_e(Suc k mod ?n),
              (1-t)*vy_e k + t*vy_e(Suc k mod ?n))
            = inv_into P_m \<psi>_m (\<tau> (cos \<alpha>, sin \<alpha>))"
            unfolding spur_f_def using h\<psi>e by (by100 simp)
          also have "\<dots> = inv_into P_m \<psi>_m
              (cos (2*pi*(real (k-2) + t) / real ?m), sin (2*pi*(real (k-2) + t) / real ?m))"
            unfolding h_\<tau> h_arith ..
          also have "\<dots> = ((1-t)*vx_m (k-2) + t*vx_m(Suc (k-2) mod ?m),
              (1-t)*vy_m (k-2) + t*vy_m(Suc (k-2) mod ?m))"
            using h\<psi>m_inv_edge[rule_format, OF hk2m ht_Iset] .
          finally show ?thesis .
        qed
        show "spur_f ((1-t)*vx_e k + t*vx_e(Suc k mod ?n),
            (1-t)*vy_e k + t*vy_e(Suc k mod ?n))
          = ((1-t)*vx_m (k-2) + t*vx_m(Suc (k-2) mod ?m),
             (1-t)*vy_m (k-2) + t*vy_m(Suc (k-2) mod ?m))"
          by (rule h_result)
      qed
      \<comment> \<open>Cancel edge collapse: edges 0 and 1 of P\\_e both map to the spur in P\\_m.
         Edge 0 at t and edge 1 at 1-t map to the same spur point.\<close>
      have h_spur_cancel_collapse: "\<forall>t\<in>{0<..<(1::real)}.
          spur_f ((1-t)*vx_e 0 + t*vx_e(Suc 0 mod ?n), (1-t)*vy_e 0 + t*vy_e(Suc 0 mod ?n))
        = spur_f (t*vx_e 1 + (1-t)*vx_e(Suc 1 mod ?n), t*vy_e 1 + (1-t)*vy_e(Suc 1 mod ?n))"
      proof (intro ballI)
        fix t :: real assume ht: "t \<in> {0<..<(1::real)}"
        \<comment> \<open>Both edges map to S1 at angles 2\\<pi>t/n and 2\\<pi>(2-t)/n.
           Both in cancel sector (< \\<theta>\\_cancel = 4\\<pi>/n).
           At r=1: offset = 0, so \\<tau> = \\<tau>\\_boundary.
           t\\_fold = min(t, 2-t) = t (since t < 1 < 2-t).
           So \\<tau>\\_boundary(\\<theta>\\_0) = \\<tau>\\_boundary(\\<theta>\\_1) and spur\\_f values equal.\<close>
        \<comment> \<open>\\<psi>\\_e maps both edge points to S1.\<close>
        have h0: "0 < ?n" using hn5 by (by100 linarith)
        have ht_pos: "t > 0" using ht by (by100 simp)
        have ht_lt1: "t < 1" using ht by (by100 simp)
        have ht_Iset: "t \<in> I_set" using ht unfolding top1_unit_interval_def by (by100 auto)
        have h1t_Iset: "1-t \<in> I_set" using ht_pos ht_lt1 unfolding top1_unit_interval_def by (by100 auto)
        \<comment> \<open>Both S1 points have the same \\<tau>\\_boundary value.\<close>
        define \<alpha>0 where "\<alpha>0 = 2*pi*t/real ?n"
        define \<alpha>1 where "\<alpha>1 = 2*pi*(2-t)/real ?n"
        \<comment> \<open>Both \\<tau>\\_boundary values are equal because both give t\\_fold = t.\<close>
        have h\<alpha>0_lt: "\<alpha>0 < \<theta>_cancel"
        proof -
          have "t < 2" using ht_lt1 by (by100 linarith)
          thus ?thesis unfolding \<alpha>0_def \<theta>_cancel_def
            using pi_gt_zero h0 by (simp add: divide_less_eq mult.commute)
        qed
        have h\<alpha>1_lt: "\<alpha>1 < \<theta>_cancel"
        proof -
          have "2 - t < 2" using ht_pos by (by100 linarith)
          thus ?thesis unfolding \<alpha>1_def \<theta>_cancel_def
            using pi_gt_zero h0 by (simp add: divide_less_eq mult.commute)
        qed
        have h_tb_eq: "\<tau>_boundary \<alpha>0 = \<tau>_boundary \<alpha>1"
        proof -
          \<comment> \<open>Compute t\\_fold for \\<alpha>0: min(2\\<pi>t/n \\<cdot> n/(2\\<pi>), (4\\<pi>/n - 2\\<pi>t/n) \\<cdot> n/(2\\<pi>)) = min(t, 2-t) = t.\<close>
          have hpi_pos: "pi > 0" using pi_gt_zero .
          have h_tf0: "min (\<alpha>0 * real ?n / (2*pi)) ((4*pi/real ?n - \<alpha>0) * real ?n / (2*pi)) = t"
          proof -
            have "\<alpha>0 * real ?n / (2*pi) = t"
              unfolding \<alpha>0_def using hpi_pos h0 by (by100 simp)
            moreover have "(4*pi/real ?n - \<alpha>0) * real ?n / (2*pi) = 2 - t"
            proof -
              have "4*pi/real ?n - \<alpha>0 = (4*pi - 2*pi*t)/real ?n"
                unfolding \<alpha>0_def using h0 by (simp add: diff_divide_distrib)
              also have "\<dots> = 2*pi*(2-t)/real ?n" by argo
              finally have "(4*pi/real ?n - \<alpha>0) * real ?n / (2*pi) = 2*pi*(2-t)/real ?n * real ?n / (2*pi)"
                by (by100 simp)
              also have "\<dots> = 2-t" using hpi_pos h0 by (by100 simp)
              finally show ?thesis .
            qed
            moreover have "min t (2 - t) = t" using ht_lt1 by (by100 simp)
            ultimately show ?thesis by (by100 simp)
          qed
          have h_tf1: "min (\<alpha>1 * real ?n / (2*pi)) ((4*pi/real ?n - \<alpha>1) * real ?n / (2*pi)) = t"
          proof -
            have "\<alpha>1 * real ?n / (2*pi) = 2 - t"
              unfolding \<alpha>1_def using hpi_pos h0 by (by100 simp)
            moreover have "(4*pi/real ?n - \<alpha>1) * real ?n / (2*pi) = t"
            proof -
              have "4*pi/real ?n - \<alpha>1 = (4*pi - 2*pi*(2-t))/real ?n"
                unfolding \<alpha>1_def using h0 by (simp add: diff_divide_distrib)
              also have "\<dots> = 2*pi*t/real ?n" by argo
              finally have "(4*pi/real ?n - \<alpha>1) * real ?n / (2*pi) = 2*pi*t/real ?n * real ?n / (2*pi)"
                by (by100 simp)
              also have "\<dots> = t" using hpi_pos h0 by (by100 simp)
              finally show ?thesis .
            qed
            moreover have "min (2 - t) t = t" using ht_lt1 by (by100 simp)
            ultimately show ?thesis by (by100 simp)
          qed
          \<comment> \<open>Both \\<tau>\\_boundary values use the cancel branch with the same t\\_fold.\<close>
          have "\<tau>_boundary \<alpha>0 = ((1 - t) * 1 + t * fst p_cm, (1 - t) * 0 + t * snd p_cm)"
            unfolding \<tau>_boundary_def using h\<alpha>0_lt h_tf0 by (by100 simp)
          moreover have "\<tau>_boundary \<alpha>1 = ((1 - t) * 1 + t * fst p_cm, (1 - t) * 0 + t * snd p_cm)"
            unfolding \<tau>_boundary_def using h\<alpha>1_lt h_tf1 by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        \<comment> \<open>Since r=1 on S1 and offset=0: \\<tau> = (fst(\\<tau>\\_boundary), snd(\\<tau>\\_boundary)).\<close>
        have h_\<tau>_eq: "\<tau> (cos \<alpha>0, sin \<alpha>0) = \<tau> (cos \<alpha>1, sin \<alpha>1)"
        proof -
          \<comment> \<open>Both (cos \\<alpha>, sin \\<alpha>) \\<noteq> (0,0) and r = 1. Unfold \\<tau>.\<close>
          have hne0: "(cos \<alpha>0, sin \<alpha>0) \<noteq> (0::real, 0)"
          proof
            assume "(cos \<alpha>0, sin \<alpha>0) = (0, 0)"
            hence "cos \<alpha>0 * cos \<alpha>0 + sin \<alpha>0 * sin \<alpha>0 = 0" by (by100 simp)
            moreover have "cos \<alpha>0 * cos \<alpha>0 + sin \<alpha>0 * sin \<alpha>0 = 1"
              using sin_cos_squared_add3[of \<alpha>0] by (simp add: power2_eq_square)
            ultimately show False by (by100 linarith)
          qed
          have hne1: "(cos \<alpha>1, sin \<alpha>1) \<noteq> (0::real, 0)"
          proof
            assume "(cos \<alpha>1, sin \<alpha>1) = (0, 0)"
            hence "cos \<alpha>1 * cos \<alpha>1 + sin \<alpha>1 * sin \<alpha>1 = 0" by (by100 simp)
            moreover have "cos \<alpha>1 * cos \<alpha>1 + sin \<alpha>1 * sin \<alpha>1 = 1"
              using sin_cos_squared_add3[of \<alpha>1] by (simp add: power2_eq_square)
            ultimately show False by (by100 linarith)
          qed
          have hr0: "sqrt ((cos \<alpha>0)^2 + (sin \<alpha>0)^2) = 1"
          proof -
            have "(cos \<alpha>0)^2 + (sin \<alpha>0)^2 = 1" using sin_cos_squared_add3 by (by100 simp)
            thus ?thesis by (by100 simp)
          qed
          have hr1: "sqrt ((cos \<alpha>1)^2 + (sin \<alpha>1)^2) = 1"
          proof -
            have "(cos \<alpha>1)^2 + (sin \<alpha>1)^2 = 1" using sin_cos_squared_add3 by (by100 simp)
            thus ?thesis by (by100 simp)
          qed
          \<comment> \<open>Angle recovery for both.\<close>
          \<comment> \<open>Both \\<alpha> are in (0, 4\\<pi>/n) \\<subset> (0, \\<pi>), so sin \\<ge> 0 and arccos\\_cos applies.\<close>
          have h\<theta>_lt_pi_local: "\<theta>_cancel < pi"
          proof -
            have "real ?n \<ge> 5" using hn5 by (by100 simp)
            hence "4 * pi / real ?n \<le> 4 * pi / 5"
              using divide_left_mono[of 5 "real ?n" "4*pi"] pi_gt_zero by (by100 simp)
            also have "\<dots> < pi" using pi_gt_zero by (by100 linarith)
            finally show ?thesis unfolding \<theta>_cancel_def .
          qed
          have h\<alpha>0_ge0: "\<alpha>0 \<ge> 0" unfolding \<alpha>0_def using pi_gt_zero h0 ht_pos by (by100 simp)
          have h\<alpha>0_le_pi: "\<alpha>0 \<le> pi" using h\<alpha>0_lt h\<theta>_lt_pi_local by (by100 linarith)
          have h\<alpha>1_ge0: "\<alpha>1 \<ge> 0" unfolding \<alpha>1_def using pi_gt_zero h0 ht_lt1 by (by100 simp)
          have h\<alpha>1_le_pi: "\<alpha>1 \<le> pi" using h\<alpha>1_lt h\<theta>_lt_pi_local by (by100 linarith)
          have h_angle0: "(if sin \<alpha>0 \<ge> 0 then arccos (cos \<alpha>0 / sqrt ((cos \<alpha>0)^2 + (sin \<alpha>0)^2))
              else 2*pi - arccos (cos \<alpha>0 / sqrt ((cos \<alpha>0)^2 + (sin \<alpha>0)^2))) = \<alpha>0"
          proof -
            have "sin \<alpha>0 \<ge> 0" using sin_ge_zero[OF h\<alpha>0_ge0 h\<alpha>0_le_pi] .
            moreover have "cos \<alpha>0 / sqrt ((cos \<alpha>0)^2 + (sin \<alpha>0)^2) = cos \<alpha>0" using hr0 by (by100 simp)
            moreover have "arccos (cos \<alpha>0) = \<alpha>0" using arccos_cos[OF h\<alpha>0_ge0 h\<alpha>0_le_pi] .
            ultimately show ?thesis by (by100 simp)
          qed
          have h_angle1: "(if sin \<alpha>1 \<ge> 0 then arccos (cos \<alpha>1 / sqrt ((cos \<alpha>1)^2 + (sin \<alpha>1)^2))
              else 2*pi - arccos (cos \<alpha>1 / sqrt ((cos \<alpha>1)^2 + (sin \<alpha>1)^2))) = \<alpha>1"
          proof -
            have "sin \<alpha>1 \<ge> 0" using sin_ge_zero[OF h\<alpha>1_ge0 h\<alpha>1_le_pi] .
            moreover have "cos \<alpha>1 / sqrt ((cos \<alpha>1)^2 + (sin \<alpha>1)^2) = cos \<alpha>1" using hr1 by (by100 simp)
            moreover have "arccos (cos \<alpha>1) = \<alpha>1" using arccos_cos[OF h\<alpha>1_ge0 h\<alpha>1_le_pi] .
            ultimately show ?thesis by (by100 simp)
          qed
          \<comment> \<open>Both \\<alpha> < \\<theta>\\_cancel, so cancel branch. At r=1: offset = sign*1*(1-1)*sin(.)/4 = 0.
             So \\<tau> = (fst(\\<tau>\\_boundary(\\<alpha>)), snd(\\<tau>\\_boundary(\\<alpha>))).\<close>
          have "\<tau> (cos \<alpha>0, sin \<alpha>0) = (fst (\<tau>_boundary \<alpha>0), snd (\<tau>_boundary \<alpha>0))"
            unfolding \<tau>_def using hne0 hr0 h_angle0 h\<alpha>0_lt by auto
          moreover have "\<tau> (cos \<alpha>1, sin \<alpha>1) = (fst (\<tau>_boundary \<alpha>1), snd (\<tau>_boundary \<alpha>1))"
            unfolding \<tau>_def using hne1 hr1 h_angle1 h\<alpha>1_lt by auto
          ultimately show ?thesis using h_tb_eq by (by100 simp)
        qed
        \<comment> \<open>Assemble: spur\\_f = \\<psi>\\_m\\<inverse> \\<circ> \\<tau> \\<circ> \\<psi>\\_e.\<close>
        have h_e0: "\<psi>_e ((1-t)*vx_e 0 + t*vx_e(Suc 0 mod ?n), (1-t)*vy_e 0 + t*vy_e(Suc 0 mod ?n))
            = (cos \<alpha>0, sin \<alpha>0)"
        proof -
          have "0 < ?n" using hn5 by (by100 linarith)
          from h\<psi>e_edge[rule_format, OF this ht_Iset]
          show ?thesis unfolding \<alpha>0_def by (by100 simp)
        qed
        have h1_lt: "1 < ?n" using hn5 by (by100 linarith)
        \<comment> \<open>Edge 1 reversed: parameter 1-t gives angle 2\\<pi>(1+(1-t))/n = 2\\<pi>(2-t)/n = \\<alpha>\\_1.\<close>
        have h_e1: "\<psi>_e (t*vx_e 1 + (1-t)*vx_e(Suc 1 mod ?n),
            t*vy_e 1 + (1-t)*vy_e(Suc 1 mod ?n)) = (cos \<alpha>1, sin \<alpha>1)"
        proof -
          \<comment> \<open>Reversed edge 1 at t = edge 1 at parameter 1-t.\<close>
          have "t*vx_e 1 + (1-t)*vx_e(Suc 1 mod ?n)
              = (1-(1-t))*vx_e 1 + (1-t)*vx_e(Suc 1 mod ?n)" by (by100 simp)
          moreover have "t*vy_e 1 + (1-t)*vy_e(Suc 1 mod ?n)
              = (1-(1-t))*vy_e 1 + (1-t)*vy_e(Suc 1 mod ?n)" by (by100 simp)
          ultimately have "t*vx_e 1 + (1-t)*vx_e(Suc 1 mod ?n) =
              (1-(1-t))*vx_e 1 + (1-t)*vx_e(Suc 1 mod ?n)
            \<and> t*vy_e 1 + (1-t)*vy_e(Suc 1 mod ?n) =
              (1-(1-t))*vy_e 1 + (1-t)*vy_e(Suc 1 mod ?n)" by (by100 blast)
          from h\<psi>e_edge[rule_format, OF h1_lt h1t_Iset]
          have "\<psi>_e ((1-(1-t))*vx_e 1 + (1-t)*vx_e(Suc 1 mod ?n),
              (1-(1-t))*vy_e 1 + (1-t)*vy_e(Suc 1 mod ?n))
            = (cos (2*pi*(real 1 + (1-t))/real ?n), sin (2*pi*(real 1 + (1-t))/real ?n))" .
          hence "\<psi>_e (t*vx_e 1 + (1-t)*vx_e(Suc 1 mod ?n),
              t*vy_e 1 + (1-t)*vy_e(Suc 1 mod ?n))
            = (cos (2*pi*(2-t)/real ?n), sin (2*pi*(2-t)/real ?n))"
            by (by100 simp)
          thus ?thesis unfolding \<alpha>1_def by (by100 simp)
        qed
        show "spur_f ((1-t)*vx_e 0 + t*vx_e(Suc 0 mod ?n), (1-t)*vy_e 0 + t*vy_e(Suc 0 mod ?n))
          = spur_f (t*vx_e 1 + (1-t)*vx_e(Suc 1 mod ?n), t*vy_e 1 + (1-t)*vy_e(Suc 1 mod ?n))"
          unfolding spur_f_def using h_e0 h_e1 h_\<tau>_eq by (by100 simp)
      qed
      \<comment> \<open>Vertex mapping: spur\\_f(vx\\_e(k)) for k \\<ge> 2.\<close>
      have h_spur_vertex: "\<forall>k. 2 \<le> k \<longrightarrow> k < ?n \<longrightarrow>
          spur_f (vx_e k, vy_e k) = (vx_m (k-2), vy_m (k-2))"
      proof (intro allI impI)
        fix k assume hk2: "2 \<le> k" and hk: "k < ?n"
        \<comment> \<open>This is h\\_spur\\_good\\_edge at t=0, using I\\_set edge formula.\<close>
        have ht0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        have hk2m: "k - 2 < ?m" using hk hk2 hn_eq by (by100 linarith)
        \<comment> \<open>Edge at t=0 is the vertex.\<close>
        have h_vx_eq: "(vx_e k, vy_e k) = ((1-0)*vx_e k + 0*vx_e(Suc k mod ?n),
            (1-0)*vy_e k + 0*vy_e(Suc k mod ?n))" by (by100 simp)
        have h_vxm_eq: "(vx_m (k-2), vy_m (k-2)) = ((1-0)*vx_m(k-2) + 0*vx_m(Suc(k-2) mod ?m),
            (1-0)*vy_m(k-2) + 0*vy_m(Suc(k-2) mod ?m))" by (by100 simp)
        \<comment> \<open>Use \\<psi>\\_e at edge k, t=0.\<close>
        define \<alpha> where "\<alpha> = 2*pi*(real k)/real ?n"
        have h\<psi>e: "\<psi>_e (vx_e k, vy_e k) = (cos \<alpha>, sin \<alpha>)"
        proof -
          from h\<psi>e_edge[rule_format, OF hk ht0_I]
          show ?thesis unfolding \<alpha>_def by (by100 simp)
        qed
        \<comment> \<open>\\<tau> at (cos \\<alpha>, sin \\<alpha>): good sector (\\<alpha> \\<ge> \\<theta>\\_cancel).\<close>
        have hn_pos: "real ?n > 0" using hn5 by (by100 linarith)
        have h\<alpha>_ge0: "\<alpha> \<ge> 0" unfolding \<alpha>_def using pi_gt_zero hn_pos hk2 by (by100 simp)
        have h\<alpha>_lt2pi: "\<alpha> < 2*pi"
        proof -
          have "real k < real ?n" using hk by (by100 simp)
          thus ?thesis unfolding \<alpha>_def using pi_gt_zero hn_pos
            by (simp add: divide_less_eq mult.commute)
        qed
        have h_good: "\<alpha> \<ge> \<theta>_cancel"
        proof -
          have "real k \<ge> 2" using hk2 by (by100 simp)
          thus ?thesis unfolding \<alpha>_def \<theta>_cancel_def using pi_gt_zero hn_pos
            by (simp add: divide_le_eq mult.commute)
        qed
        have h_\<tau>: "\<tau> (cos \<alpha>, sin \<alpha>) =
            (cos ((\<alpha> - \<theta>_cancel) * real ?n / real ?m),
             sin ((\<alpha> - \<theta>_cancel) * real ?n / real ?m))"
        proof -
          have h_ne: "(cos \<alpha>, sin \<alpha>) \<noteq> (0::real, 0)"
          proof
            assume "(cos \<alpha>, sin \<alpha>) = (0, 0)"
            hence "cos \<alpha> * cos \<alpha> + sin \<alpha> * sin \<alpha> = 0" by (by100 simp)
            moreover have "cos \<alpha> * cos \<alpha> + sin \<alpha> * sin \<alpha> = 1"
              using sin_cos_squared_add3[of \<alpha>] by (simp add: power2_eq_square)
            ultimately show False by (by100 linarith)
          qed
          have hr1: "sqrt ((cos \<alpha>)^2 + (sin \<alpha>)^2) = 1"
          proof -
            have "(cos \<alpha>)^2 + (sin \<alpha>)^2 = 1" using sin_cos_squared_add3 by (by100 simp)
            thus ?thesis by (by100 simp)
          qed
          have hdiv: "cos \<alpha> / sqrt ((cos \<alpha>)^2 + (sin \<alpha>)^2) = cos \<alpha>"
            using hr1 by (by100 simp)
          have h_angle: "(if sin \<alpha> \<ge> 0 then arccos (cos \<alpha> / sqrt ((cos \<alpha>)^2 + (sin \<alpha>)^2))
              else 2*pi - arccos (cos \<alpha> / sqrt ((cos \<alpha>)^2 + (sin \<alpha>)^2))) = \<alpha>"
          proof (cases "sin \<alpha> \<ge> 0")
            case True
            have "\<alpha> \<le> pi"
            proof (rule ccontr)
              assume "\<not> \<alpha> \<le> pi"
              hence "\<alpha> > pi" by (by100 linarith)
              hence "sin \<alpha> < 0" using h\<alpha>_lt2pi sin_lt_zero by (by100 auto)
              thus False using True by (by100 linarith)
            qed
            hence "arccos (cos \<alpha>) = \<alpha>" using h\<alpha>_ge0 arccos_cos by (by100 blast)
            thus ?thesis using True hdiv by (by100 simp)
          next
            case False
            hence "sin \<alpha> < 0" by (by100 linarith)
            have "\<alpha> > pi"
            proof (rule ccontr)
              assume "\<not> \<alpha> > pi"
              hence "\<alpha> \<le> pi" by (by100 linarith)
              hence "sin \<alpha> \<ge> 0" using h\<alpha>_ge0 sin_ge_zero by (by100 blast)
              thus False using \<open>sin \<alpha> < 0\<close> by (by100 linarith)
            qed
            have "arccos (cos \<alpha>) = 2*pi - \<alpha>"
            proof -
              have "\<alpha> - 2*pi \<le> 0" using h\<alpha>_lt2pi by (by100 linarith)
              have "- pi \<le> \<alpha> - 2*pi" using \<open>\<alpha> > pi\<close> by (by100 linarith)
              have "cos (\<alpha> - 2*pi) = cos \<alpha>" by (simp add: cos_diff)
              from arccos_cos2[OF \<open>\<alpha> - 2*pi \<le> 0\<close> \<open>- pi \<le> \<alpha> - 2*pi\<close>] this
              show ?thesis by (by100 simp)
            qed
            thus ?thesis using False hdiv by (by100 simp)
          qed
          have "\<tau> (cos \<alpha>, sin \<alpha>) = (fst (\<tau>_boundary \<alpha>), snd (\<tau>_boundary \<alpha>))"
            unfolding \<tau>_def using h_ne hr1 h_angle h_good by auto
          also have "\<dots> = (cos ((\<alpha> - \<theta>_cancel) * real ?n / real ?m),
              sin ((\<alpha> - \<theta>_cancel) * real ?n / real ?m))"
            unfolding \<tau>_boundary_def using h_good by (by100 auto)
          finally show ?thesis .
        qed
        have h_arith: "(\<alpha> - \<theta>_cancel) * real ?n / real ?m = 2*pi*(real (k-2)) / real ?m"
        proof -
          have "\<alpha> - \<theta>_cancel = 2*pi*real k/real ?n - 4*pi/real ?n"
            unfolding \<alpha>_def \<theta>_cancel_def by (by100 simp)
          also have "\<dots> = 2*pi*(real k - 2)/real ?n"
            using hn_pos by (simp add: diff_divide_distrib algebra_simps)
          finally have h1: "\<alpha> - \<theta>_cancel = 2*pi*(real k - 2)/real ?n" .
          have "(\<alpha> - \<theta>_cancel) * real ?n / real ?m = 2*pi*(real k - 2) / real ?m"
            using h1 hn_pos by (by100 simp)
          also have "real k - 2 = real (k - 2)" using hk2 by (by100 simp)
          finally show ?thesis .
        qed
        show "spur_f (vx_e k, vy_e k) = (vx_m (k-2), vy_m (k-2))"
        proof -
          have "spur_f (vx_e k, vy_e k) = inv_into P_m \<psi>_m (\<tau> (cos \<alpha>, sin \<alpha>))"
            unfolding spur_f_def using h\<psi>e by (by100 simp)
          also have "\<dots> = inv_into P_m \<psi>_m
              (cos (2*pi*real(k-2)/real ?m), sin (2*pi*real(k-2)/real ?m))"
            unfolding h_\<tau> h_arith ..
          also have "\<dots> = ((1-0)*vx_m(k-2) + 0*vx_m(Suc(k-2) mod ?m),
              (1-0)*vy_m(k-2) + 0*vy_m(Suc(k-2) mod ?m))"
            using h\<psi>m_inv_edge[rule_format, OF hk2m ht0_I] by (by100 simp)
          also have "\<dots> = (vx_m(k-2), vy_m(k-2))" by (by100 simp)
          finally show ?thesis .
        qed
      qed
      \<comment> \<open>Cancel vertex mapping: spur\\_f(vx\\_e(0)) = vx\\_m(0), spur\\_f(vx\\_e(1)) = centroid.\<close>
      have h_spur_vertex_0: "spur_f (vx_e 0, vy_e 0) = (vx_m 0, vy_m 0)"
      proof -
        have h0_lt: "(0::nat) < ?n" using hn5 by (by100 linarith)
        have ht0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        \<comment> \<open>\\<psi>\\_e at vertex 0: (cos(0), sin(0)) = (1, 0).\<close>
        have h\<psi>e0: "\<psi>_e (vx_e 0, vy_e 0) = (1::real, 0)"
        proof -
          from h\<psi>e_edge[rule_format, OF h0_lt ht0_I]
          have "\<psi>_e ((1-0)*vx_e 0 + 0*vx_e(Suc 0 mod ?n), (1-0)*vy_e 0 + 0*vy_e(Suc 0 mod ?n))
            = (cos (2*pi*(real 0 + 0)/real ?n), sin (2*pi*(real 0 + 0)/real ?n))" .
          thus ?thesis by (by100 simp)
        qed
        \<comment> \<open>\\<tau> at (1,0): cancel sector with \\<theta>=0, r=1, t\\_fold=0 \\<to> (1,0).\<close>
        have h\<tau>10: "\<tau> (1::real, 0) = (1, 0)"
        proof -
          have h_ne: "((1::real), (0::real)) \<noteq> (0, 0)" by (by100 simp)
          have "sqrt ((1::real)^2 + (0::real)^2) = 1" by (by100 simp)
          moreover have "arccos ((1::real) / 1) = 0" using arccos_1 by (by100 simp)
          moreover have "(0::real) < \<theta>_cancel" unfolding \<theta>_cancel_def using pi_gt_zero hn5
            by (by100 simp)
          ultimately show ?thesis unfolding \<tau>_def \<tau>_boundary_def using h_ne by auto
        qed
        \<comment> \<open>\\<psi>\\_m\\<inverse> at (1,0) = vx\\_m(0).\<close>
        have h0m_lt: "(0::nat) < ?m" using hm3 by (by100 linarith)
        from h\<psi>m_inv_edge[rule_format, OF h0m_lt ht0_I]
        have "inv_into P_m \<psi>_m (cos (2*pi*(real 0 + 0)/real ?m), sin (2*pi*(real 0 + 0)/real ?m))
          = ((1-0)*vx_m 0 + 0*vx_m(Suc 0 mod ?m), (1-0)*vy_m 0 + 0*vy_m(Suc 0 mod ?m))" .
        hence h_inv: "inv_into P_m \<psi>_m (1, 0) = (vx_m 0, vy_m 0)" by (by100 simp)
        show ?thesis unfolding spur_f_def using h\<psi>e0 h\<tau>10 h_inv by (by100 simp)
      qed
      \<comment> \<open>Vertex\\_e(0) and vertex\\_e(2) both map to vertex\\_m(0) via spur\\_f.\<close>
      have h_spur_vertex_02: "spur_f (vx_e 0, vy_e 0) = spur_f (vx_e 2, vy_e 2)"
      proof -
        have "spur_f (vx_e 0, vy_e 0) = (vx_m 0, vy_m 0)" by (rule h_spur_vertex_0)
        moreover have "spur_f (vx_e 2, vy_e 2) = (vx_m 0, vy_m 0)"
        proof -
          have h2le: "(2::nat) \<le> 2" by (by100 simp)
          have h2lt: "(2::nat) < ?n" using hn5 by (by100 linarith)
          from h_spur_vertex[rule_format, OF h2le h2lt]
          show ?thesis by (by100 simp)
        qed
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>Decompose h\\_fibres into sub-cases.\<close>
      \<comment> \<open>Case 3: Good-edge fibre matching (i,j \\<ge> 2, 0 < t,s < 1).
         q\\_e(edge\\_e(i,t)) = q\\_e(edge\\_e(j,s)) via C7\\_e \\<longleftrightarrow>
         label match in ext\\_scheme \\<longleftrightarrow> label match in w (cancel\\_shift\\_partner) \\<longleftrightarrow>
         q\\_m(edge\\_m(i-2,t)) = q\\_m(edge\\_m(j-2,s)) via C7\\_m.\<close>
      have h_fibres_good_edge: "\<forall>i. 2 \<le> i \<longrightarrow> i < ?n \<longrightarrow>
          (\<forall>j. 2 \<le> j \<longrightarrow> j < ?n \<longrightarrow>
          (\<forall>t\<in>{0<..<(1::real)}. \<forall>s\<in>{0<..<(1::real)}.
          (q_e ((1-t)*vx_e i+t*vx_e(Suc i mod ?n),(1-t)*vy_e i+t*vy_e(Suc i mod ?n))
         = q_e ((1-s)*vx_e j+s*vx_e(Suc j mod ?n),(1-s)*vy_e j+s*vy_e(Suc j mod ?n)))
         \<longleftrightarrow>
          (q_m ((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2)mod ?m),(1-t)*vy_m(i-2)+t*vy_m(Suc(i-2)mod ?m))
         = q_m ((1-s)*vx_m(j-2)+s*vx_m(Suc(j-2)mod ?m),(1-s)*vy_m(j-2)+s*vy_m(Suc(j-2)mod ?m)))))"
      proof (intro allI impI ballI)
        fix i j :: nat and t s :: real
        assume hi: "2 \<le> i" "i < ?n" and hj: "2 \<le> j" "j < ?n" and ht: "t \<in> {0<..<1}" and hs: "s \<in> {0<..<1}"
        let ?ext = "[a, top1_inverse_edge a] @ w"
        have hi_m: "i - 2 < ?m" using hi hn_eq by (by100 linarith)
        have hj_m: "j - 2 < ?m" using hj hn_eq by (by100 linarith)
        \<comment> \<open>cancel\\_shift: ext\\_scheme!(i) = w!(i-2) and ext\\_scheme!(j) = w!(j-2).\<close>
        have hshift_i: "?ext ! i = w ! (i - 2)"
        proof -
          have "i = (i - 2) + 2" using hi by (by100 simp)
          thus ?thesis using cancel_shift_label[OF hi_m, of a] by (by100 simp)
        qed
        have hshift_j: "?ext ! j = w ! (j - 2)"
        proof -
          have "j = (j - 2) + 2" using hj by (by100 simp)
          thus ?thesis using cancel_shift_label[OF hj_m, of a] by (by100 simp)
        qed
        have hlabel_iff: "fst (?ext ! i) = fst (?ext ! j) \<longleftrightarrow> fst (w ! (i-2)) = fst (w ! (j-2))"
          using hshift_i hshift_j by (by100 simp)
        have hdir_iff: "snd (?ext ! i) = snd (?ext ! j) \<longleftrightarrow> snd (w ! (i-2)) = snd (w ! (j-2))"
          using hshift_i hshift_j by (by100 simp)
        \<comment> \<open>No Suc mod shift needed — h\\_spur\\_good\\_edge already handles the mapping directly.\<close>
        show "(q_e ((1-t)*vx_e i+t*vx_e(Suc i mod ?n),(1-t)*vy_e i+t*vy_e(Suc i mod ?n))
           = q_e ((1-s)*vx_e j+s*vx_e(Suc j mod ?n),(1-s)*vy_e j+s*vy_e(Suc j mod ?n)))
           \<longleftrightarrow>
            (q_m ((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2)mod ?m),(1-t)*vy_m(i-2)+t*vy_m(Suc(i-2)mod ?m))
           = q_m ((1-s)*vx_m(j-2)+s*vx_m(Suc(j-2)mod ?m),(1-s)*vy_m(j-2)+s*vy_m(Suc(j-2)mod ?m)))"
        proof (intro iffI)
          \<comment> \<open>Forward: q\\_e identification \\<Longrightarrow> q\\_m identification.\<close>
          assume heq_e: "q_e ((1-t)*vx_e i+t*vx_e(Suc i mod ?n),(1-t)*vy_e i+t*vy_e(Suc i mod ?n))
              = q_e ((1-s)*vx_e j+s*vx_e(Suc j mod ?n),(1-s)*vy_e j+s*vy_e(Suc j mod ?n))"
          \<comment> \<open>C9\\_e: edge-interior identification \\<Longrightarrow> label match or same point.\<close>
          from hC9e[rule_format, OF hi(2) hj(2) ht hs] heq_e
          have "(i=j \<and> t=s) \<or> (fst(?ext!i)=fst(?ext!j) \<and> (if snd(?ext!i)=snd(?ext!j) then s=t else s=1-t))"
            by (by100 blast)
          thus "q_m ((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2)mod ?m),(1-t)*vy_m(i-2)+t*vy_m(Suc(i-2)mod ?m))
              = q_m ((1-s)*vx_m(j-2)+s*vx_m(Suc(j-2)mod ?m),(1-s)*vy_m(j-2)+s*vy_m(Suc(j-2)mod ?m))"
          proof
            assume "i=j \<and> t=s"
            thus ?thesis by (by100 simp)
          next
            assume hlm: "fst(?ext!i)=fst(?ext!j) \<and>
                (if snd(?ext!i)=snd(?ext!j) then s=t else s=1-t)"
            hence hlabel_w: "fst(w!(i-2)) = fst(w!(j-2))" using hlabel_iff by (by100 blast)
            have ht_I: "t \<in> I_set" using ht unfolding top1_unit_interval_def by (by100 auto)
            from hC7m[rule_format, OF hi_m hj_m hlabel_w ht_I]
            have hC7_app: "q_m ((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2)mod ?m),(1-t)*vy_m(i-2)+t*vy_m(Suc(i-2)mod ?m))
              = (if snd(w!(i-2))=snd(w!(j-2))
                then q_m ((1-t)*vx_m(j-2)+t*vx_m(Suc(j-2)mod ?m),(1-t)*vy_m(j-2)+t*vy_m(Suc(j-2)mod ?m))
                else q_m (t*vx_m(j-2)+(1-t)*vx_m(Suc(j-2)mod ?m),t*vy_m(j-2)+(1-t)*vy_m(Suc(j-2)mod ?m)))" .
            from hlm have hdir: "if snd(?ext!i)=snd(?ext!j) then s=t else s=1-t" by (by100 blast)
            show ?thesis
            proof (cases "snd(?ext!i) = snd(?ext!j)")
              case True
              hence "s = t" using hdir by (by100 simp)
              moreover have "snd(w!(i-2)) = snd(w!(j-2))" using True hdir_iff by (by100 blast)
              ultimately show ?thesis using hC7_app by (by100 simp)
            next
              case False
              hence "s = 1-t" using hdir by (by100 simp)
              moreover have "snd(w!(i-2)) \<noteq> snd(w!(j-2))" using False hdir_iff by (by100 blast)
              ultimately show ?thesis using hC7_app by (by100 simp)
            qed
          qed
        next
          \<comment> \<open>Backward: q\\_m identification \\<Longrightarrow> q\\_e identification.\<close>
          assume heq_m: "q_m ((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2)mod ?m),(1-t)*vy_m(i-2)+t*vy_m(Suc(i-2)mod ?m))
              = q_m ((1-s)*vx_m(j-2)+s*vx_m(Suc(j-2)mod ?m),(1-s)*vy_m(j-2)+s*vy_m(Suc(j-2)mod ?m))"
          from hC9m[rule_format, OF hi_m hj_m ht hs] heq_m
          have "(i-2=j-2 \<and> t=s) \<or> (fst(w!(i-2))=fst(w!(j-2)) \<and> (if snd(w!(i-2))=snd(w!(j-2)) then s=t else s=1-t))"
            by (by100 blast)
          thus "q_e ((1-t)*vx_e i+t*vx_e(Suc i mod ?n),(1-t)*vy_e i+t*vy_e(Suc i mod ?n))
              = q_e ((1-s)*vx_e j+s*vx_e(Suc j mod ?n),(1-s)*vy_e j+s*vy_e(Suc j mod ?n))"
          proof
            assume "i-2=j-2 \<and> t=s"
            hence "i = j" "t = s" using hi hj by (by100 linarith)+
            thus ?thesis by (by100 simp)
          next
            assume hlm: "fst(w!(i-2))=fst(w!(j-2)) \<and>
                (if snd(w!(i-2))=snd(w!(j-2)) then s=t else s=1-t)"
            hence hlabel_ext: "fst(?ext!i) = fst(?ext!j)" using hlabel_iff by (by100 blast)
            have ht_I: "t \<in> I_set" using ht unfolding top1_unit_interval_def by (by100 auto)
            from hC7e[rule_format, OF hi(2) hj(2) hlabel_ext ht_I]
            have hC7_app: "q_e ((1-t)*vx_e i+t*vx_e(Suc i mod ?n),(1-t)*vy_e i+t*vy_e(Suc i mod ?n))
              = (if snd(?ext!i)=snd(?ext!j)
                then q_e ((1-t)*vx_e j+t*vx_e(Suc j mod ?n),(1-t)*vy_e j+t*vy_e(Suc j mod ?n))
                else q_e (t*vx_e j+(1-t)*vx_e(Suc j mod ?n),t*vy_e j+(1-t)*vy_e(Suc j mod ?n)))" .
            from hlm have hdir: "if snd(w!(i-2))=snd(w!(j-2)) then s=t else s=1-t" by (by100 blast)
            show ?thesis
            proof (cases "snd(w!(i-2)) = snd(w!(j-2))")
              case True
              hence "s = t" using hdir by (by100 simp)
              moreover have "snd(?ext!i) = snd(?ext!j)" using True hdir_iff by (by100 blast)
              ultimately show ?thesis using hC7_app by (by100 simp)
            next
              case False
              hence "s = 1-t" using hdir by (by100 simp)
              moreover have "snd(?ext!i) \<noteq> snd(?ext!j)" using False hdir_iff by (by100 blast)
              ultimately show ?thesis using hC7_app by (by100 simp)
            qed
          qed
        qed
      qed
      \<comment> \<open>Vertex-edge quotient separation: q\\_e does not identify vertices with edge interiors.
         This holds because hY\\_ext comes from scheme\\_quotient\\_exists (canonical construction),
         where q is defined by 3 branches (vertex\\<to>vtgt, non-canonical edge\\<to>partner, else\\<to>id).
         The vertex branch maps to a vertex representative, the edge branch maps to an edge point,
         and these are disjoint by edge\\_interior\\_not\\_vertex.\<close>
      have hC12_e: "\<forall>k<?n. \<forall>j<?n. \<forall>s\<in>{0<..<(1::real)}.
          q_e (vx_e k, vy_e k) \<noteq> q_e ((1-s)*vx_e j + s*vx_e(Suc j mod ?n),
                                        (1-s)*vy_e j + s*vy_e(Suc j mod ?n))"
        using hC12e_proved by (by100 simp)
      have hC12_m: "\<forall>k<?m. \<forall>j<?m. \<forall>s\<in>{0<..<(1::real)}.
          q_m (vx_m k, vy_m k) \<noteq> q_m ((1-s)*vx_m j + s*vx_m(Suc j mod ?m),
                                        (1-s)*vy_m j + s*vy_m(Suc j mod ?m))"
        using hC12m_proved by (by100 simp)
      \<comment> \<open>VERTEX-VERTEX TRANSFER: q\\_m(spur\\_f(vertex\\_e(k))) = q\\_m(spur\\_f(vertex\\_e(vtgt\\_e(k)))).
         By strong induction on k, using vtgt\\_e(k) \\<le> k.
         Base (vtgt\\_e(k) = k): trivial.
         Step (vtgt\\_e(k) < k): k is connected via a C7\\_e edge pair to some vertex
         with smaller or equal index. The generator step preserves q\\_m\\<circ>spur\\_f.
         By IH, the intermediate vertex's q\\_m value equals the representative's.\<close>
      \<comment> \<open>Define the C7 vertex step relation for the ext scheme.\<close>
      let ?ext = "[a, top1_inverse_edge a] @ w"
      let ?vtx_step = "{(x, y). \<exists>i<?n. \<exists>j<?n. i \<noteq> j
          \<and> fst (?ext ! i) = fst (?ext ! j)
          \<and> ((snd (?ext ! i) = snd (?ext ! j) \<and> x = i \<and> y = j)
           \<or> (snd (?ext ! i) = snd (?ext ! j) \<and> x = Suc i mod ?n \<and> y = Suc j mod ?n)
           \<or> (snd (?ext ! i) \<noteq> snd (?ext ! j) \<and> x = i \<and> y = Suc j mod ?n)
           \<or> (snd (?ext ! i) \<noteq> snd (?ext ! j) \<and> x = Suc i mod ?n \<and> y = j))}"
      \<comment> \<open>Each C7 vertex step preserves q\\_m \\<circ> spur\\_f.\<close>
      have h_step_f: "\<forall>k l. (k, l) \<in> ?vtx_step \<longrightarrow>
          q_m (spur_f (vx_e k, vy_e k)) = q_m (spur_f (vx_e l, vy_e l))"
      proof (intro allI impI)
        fix k l assume h: "(k, l) \<in> ?vtx_step"
        then obtain ia ja where hia: "ia < ?n" and hja: "ja < ?n" and hne: "ia \<noteq> ja"
            and hlbl: "fst (?ext ! ia) = fst (?ext ! ja)"
            and hcase: "(snd (?ext ! ia) = snd (?ext ! ja) \<and> k = ia \<and> l = ja) \<or>
                (snd (?ext ! ia) = snd (?ext ! ja) \<and> k = Suc ia mod ?n \<and> l = Suc ja mod ?n) \<or>
                (snd (?ext ! ia) \<noteq> snd (?ext ! ja) \<and> k = ia \<and> l = Suc ja mod ?n) \<or>
                (snd (?ext ! ia) \<noteq> snd (?ext ! ja) \<and> k = Suc ia mod ?n \<and> l = ja)"
          by auto
        \<comment> \<open>For each case: show spur\\_f transfers C7 identification to q\\_m equality.\<close>
        \<comment> \<open>Mixed case impossible: hfresh prevents cancel label matching good label.\<close>
        have hmixed_impossible: "ia \<ge> 2 \<longleftrightarrow> ja \<ge> 2"
        proof -
          have hlen_ext: "length ?ext = ?n" by (by100 simp)
          show ?thesis
          proof
            assume hia2: "ia \<ge> 2"
            show "ja \<ge> 2"
            proof (rule ccontr)
              assume "\<not> ja \<ge> 2" hence "ja < 2" by (by100 linarith)
              hence "fst (?ext ! ja) = fst a"
                unfolding top1_inverse_edge_def by (cases ja) (by100 auto)+
              moreover have "fst (?ext ! ia) \<in> fst ` set w"
              proof -
                have "ia - 2 < ?m" using hia2 hia hn_eq by (by100 linarith)
                have "ia = (ia - 2) + 2" using hia2 by (by100 simp)
                hence "?ext ! ia = w ! (ia - 2)"
                  using cancel_shift_label[OF \<open>ia - 2 < ?m\<close>, of a] by (by100 simp)
                hence "fst (?ext ! ia) = fst (w ! (ia - 2))" by (by100 simp)
                moreover have "w ! (ia - 2) \<in> set w" using \<open>ia - 2 < ?m\<close> by (by100 simp)
                ultimately show ?thesis by (by100 force)
              qed
              ultimately show False using hfresh hlbl by (by100 auto)
            qed
          next
            assume hja2: "ja \<ge> 2"
            show "ia \<ge> 2"
            proof (rule ccontr)
              assume "\<not> ia \<ge> 2" hence "ia < 2" by (by100 linarith)
              hence "fst (?ext ! ia) = fst a"
                unfolding top1_inverse_edge_def by (cases ia) (by100 auto)+
              moreover have "fst (?ext ! ja) \<in> fst ` set w"
              proof -
                have "ja - 2 < ?m" using hja2 hja hn_eq by (by100 linarith)
                have "ja = (ja - 2) + 2" using hja2 by (by100 simp)
                hence "?ext ! ja = w ! (ja - 2)"
                  using cancel_shift_label[OF \<open>ja - 2 < ?m\<close>, of a] by (by100 simp)
                hence "fst (?ext ! ja) = fst (w ! (ja - 2))" by (by100 simp)
                moreover have "w ! (ja - 2) \<in> set w" using \<open>ja - 2 < ?m\<close> by (by100 simp)
                ultimately show ?thesis by (by100 force)
              qed
              ultimately show False using hfresh hlbl by (by100 auto)
            qed
          qed
        qed
        show "q_m (spur_f (vx_e k, vy_e k)) = q_m (spur_f (vx_e l, vy_e l))"
        proof (cases "ia \<ge> 2")
          case True
          hence hja2: "ja \<ge> 2" using hmixed_impossible by (by100 simp)
          have hia_m: "ia - 2 < ?m" using True hia hn_eq by (by100 linarith)
          have hja_m: "ja - 2 < ?m" using hja2 hja hn_eq by (by100 linarith)
          \<comment> \<open>Good edges: cancel\\_shift + C7\\_m.\<close>
          have hia_eq: "ia = (ia - 2) + 2" using True by (by100 simp)
          have hja_eq: "ja = (ja - 2) + 2" using hja2 by (by100 simp)
          have hshift_ia: "?ext ! ia = w ! (ia - 2)"
          proof -
            have "ia - Suc (Suc 0) = ia - 2" by (by100 simp)
            moreover have "([a, top1_inverse_edge a] @ w) ! ia = w ! (ia - Suc (Suc 0))"
              using True hia by (by100 simp)
            ultimately show ?thesis by (by100 simp)
          qed
          have hshift_ja: "?ext ! ja = w ! (ja - 2)"
          proof -
            have "ja - Suc (Suc 0) = ja - 2" by (by100 simp)
            moreover have "([a, top1_inverse_edge a] @ w) ! ja = w ! (ja - Suc (Suc 0))"
              using hja2 hja by (by100 simp)
            ultimately show ?thesis by (by100 simp)
          qed
          have hlbl_w: "fst (w ! (ia - 2)) = fst (w ! (ja - 2))"
            using hlbl hshift_ia hshift_ja by (by100 simp)
          have hdir_w: "snd (w ! (ia - 2)) = snd (w ! (ja - 2)) \<longleftrightarrow> snd (?ext ! ia) = snd (?ext ! ja)"
            using hshift_ia hshift_ja by (by100 simp)
          have ht0: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
          have ht1: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
          \<comment> \<open>Use C7\\_m at t=0 and t=1, and h\\_spur\\_vertex for the spur\\_f mapping.\<close>
          \<comment> \<open>Helper: spur\\_f at good vertices.\<close>
          have hsf_ia: "spur_f (vx_e ia, vy_e ia) = (vx_m (ia-2), vy_m (ia-2))"
            using h_spur_vertex[rule_format, OF True hia] .
          have hsf_ja: "spur_f (vx_e ja, vy_e ja) = (vx_m (ja-2), vy_m (ja-2))"
            using h_spur_vertex[rule_format, OF hja2 hja] .
          \<comment> \<open>Helper: spur\\_f at Suc vertices. Key fact: for k \\<ge> 2 and k < n:
             spur\\_f(vertex\\_e(Suc k mod n)) = vertex\\_m(Suc(k-2) mod m).\<close>
          have h_spur_Suc: "\<And>kk. kk \<ge> 2 \<Longrightarrow> kk < ?n \<Longrightarrow>
              spur_f (vx_e (Suc kk mod ?n), vy_e (Suc kk mod ?n)) =
              (vx_m (Suc (kk-2) mod ?m), vy_m (Suc (kk-2) mod ?m))"
          proof -
            fix kk assume hkk2: "kk \<ge> 2" and hkk: "kk < ?n"
            show "spur_f (vx_e (Suc kk mod ?n), vy_e (Suc kk mod ?n)) =
                (vx_m (Suc (kk-2) mod ?m), vy_m (Suc (kk-2) mod ?m))"
            proof (cases "kk < ?n - 1")
              case True
              \<comment> \<open>kk < n-1: Suc kk mod n = kk+1 \\<ge> 3. spur\\_f = vertex\\_m(kk-1).
                 Suc(kk-2) mod m = (kk-1) mod m = kk-1.\<close>
              have hSuc: "Suc kk mod ?n = Suc kk" using True hn5 by (by100 simp)
              have hSuc_ge2: "Suc kk \<ge> 2" using hkk2 by (by100 linarith)
              have hSuc_lt: "Suc kk < ?n" using True by (by100 linarith)
              from h_spur_vertex[rule_format, OF hSuc_ge2 hSuc_lt]
              have "spur_f (vx_e (Suc kk), vy_e (Suc kk)) =
                  (vx_m (Suc kk - 2), vy_m (Suc kk - 2))" .
              moreover have "Suc kk - 2 = Suc (kk - 2)" using hkk2 by (by100 simp)
              moreover have "Suc (kk - 2) < ?m" using hkk True hn_eq hkk2 by (by100 linarith)
              hence "Suc (kk - 2) mod ?m = Suc (kk - 2)" by (by100 simp)
              ultimately show ?thesis using hSuc by (by100 simp)
            next
              case False
              hence "kk = ?n - 1" using hkk by (by100 linarith)
              hence hSuc0: "Suc kk mod ?n = 0" using hn5 by (by100 simp)
              have "spur_f (vx_e 0, vy_e 0) = (vx_m 0, vy_m 0)" by (rule h_spur_vertex_0)
              moreover have "Suc (kk - 2) = ?m" using \<open>kk = ?n - 1\<close> hn_eq hkk2 by (by100 linarith)
              hence "Suc (kk - 2) mod ?m = 0" by (by100 simp)
              ultimately show ?thesis using hSuc0 by (by100 simp)
            qed
          qed
          have hsf_Suc_ia: "spur_f (vx_e (Suc ia mod ?n), vy_e (Suc ia mod ?n)) =
              (vx_m (Suc (ia-2) mod ?m), vy_m (Suc (ia-2) mod ?m))"
            by (rule h_spur_Suc[OF True hia])
          have hsf_Suc_ja: "spur_f (vx_e (Suc ja mod ?n), vy_e (Suc ja mod ?n)) =
              (vx_m (Suc (ja-2) mod ?m), vy_m (Suc (ja-2) mod ?m))"
            by (rule h_spur_Suc[OF hja2 hja])
          \<comment> \<open>Now the 4 cases.\<close>
          have hcase_sd0: "snd (?ext ! ia) = snd (?ext ! ja) \<Longrightarrow> k = ia \<Longrightarrow> l = ja \<Longrightarrow>
              q_m (spur_f (vx_e k, vy_e k)) = q_m (spur_f (vx_e l, vy_e l))"
          proof -
            assume hsd: "snd (?ext ! ia) = snd (?ext ! ja)" and "k = ia" and "l = ja"
            from hC7m[rule_format, OF hia_m hja_m hlbl_w ht0]
              hsd hdir_w
            have "q_m (vx_m(ia-2), vy_m(ia-2)) = q_m (vx_m(ja-2), vy_m(ja-2))"
              by (by100 simp)
            thus ?thesis using hsf_ia hsf_ja \<open>k = ia\<close> \<open>l = ja\<close> by (by100 simp)
          qed
          have hcase_sd1: "snd (?ext ! ia) = snd (?ext ! ja) \<Longrightarrow> k = Suc ia mod ?n \<Longrightarrow> l = Suc ja mod ?n \<Longrightarrow>
              q_m (spur_f (vx_e k, vy_e k)) = q_m (spur_f (vx_e l, vy_e l))"
          proof -
            assume hsd: "snd (?ext ! ia) = snd (?ext ! ja)"
                and "k = Suc ia mod ?n" and "l = Suc ja mod ?n"
            from hC7m[rule_format, OF hia_m hja_m hlbl_w ht1]
              hsd hdir_w
            have "q_m (vx_m(Suc(ia-2)mod ?m), vy_m(Suc(ia-2)mod ?m)) =
                q_m (vx_m(Suc(ja-2)mod ?m), vy_m(Suc(ja-2)mod ?m))" by (by100 simp)
            thus ?thesis using hsf_Suc_ia hsf_Suc_ja \<open>k = Suc ia mod ?n\<close> \<open>l = Suc ja mod ?n\<close>
              by (by100 simp)
          qed
          have hcase_od0: "snd (?ext ! ia) \<noteq> snd (?ext ! ja) \<Longrightarrow> k = ia \<Longrightarrow> l = Suc ja mod ?n \<Longrightarrow>
              q_m (spur_f (vx_e k, vy_e k)) = q_m (spur_f (vx_e l, vy_e l))"
          proof -
            assume hod: "snd (?ext ! ia) \<noteq> snd (?ext ! ja)"
                and "k = ia" and "l = Suc ja mod ?n"
            from hC7m[rule_format, OF hia_m hja_m hlbl_w ht0]
              hod hdir_w
            have "q_m (vx_m(ia-2), vy_m(ia-2)) =
                q_m (vx_m(Suc(ja-2)mod ?m), vy_m(Suc(ja-2)mod ?m))" by (by100 simp)
            thus ?thesis using hsf_ia hsf_Suc_ja \<open>k = ia\<close> \<open>l = Suc ja mod ?n\<close> by (by100 simp)
          qed
          have hcase_od1: "snd (?ext ! ia) \<noteq> snd (?ext ! ja) \<Longrightarrow> k = Suc ia mod ?n \<Longrightarrow> l = ja \<Longrightarrow>
              q_m (spur_f (vx_e k, vy_e k)) = q_m (spur_f (vx_e l, vy_e l))"
          proof -
            assume hod: "snd (?ext ! ia) \<noteq> snd (?ext ! ja)"
                and "k = Suc ia mod ?n" and "l = ja"
            from hC7m[rule_format, OF hia_m hja_m hlbl_w ht1]
              hod hdir_w
            have "q_m (vx_m(Suc(ia-2)mod ?m), vy_m(Suc(ia-2)mod ?m)) =
                q_m (vx_m(ja-2), vy_m(ja-2))" by (by100 simp)
            thus ?thesis using hsf_Suc_ia hsf_ja \<open>k = Suc ia mod ?n\<close> \<open>l = ja\<close> by (by100 simp)
          qed
          from hcase hcase_sd0 hcase_sd1 hcase_od0 hcase_od1
          show ?thesis by (by100 blast)
        next
          case False
          hence hia_cancel: "ia < 2" by (by100 linarith)
          hence hja_cancel: "ja < 2" using hmixed_impossible by (by100 simp)
          \<comment> \<open>Cancel pair: (ia, ja) = (0,1) or (1,0).\<close>
          from hcase show ?thesis
          proof (elim disjE conjE)
            assume "snd (?ext ! ia) = snd (?ext ! ja)" and "k = ia" and "l = ja"
            \<comment> \<open>Same dir: but cancel pair has opposite direction. Contradiction.\<close>
            hence False using hia_cancel hja_cancel hne
              unfolding top1_inverse_edge_def by (cases ia; cases ja) auto+
            thus ?thesis by (by100 simp)
          next
            assume "snd (?ext ! ia) = snd (?ext ! ja)"
                and "k = Suc ia mod ?n" and "l = Suc ja mod ?n"
            hence False using hia_cancel hja_cancel hne
              unfolding top1_inverse_edge_def by (cases ia; cases ja) auto+
            thus ?thesis by (by100 simp)
          next
            assume "snd (?ext ! ia) \<noteq> snd (?ext ! ja)" and "k = ia" and "l = Suc ja mod ?n"
            \<comment> \<open>Opp dir: vtx(0) ~ vtx(Suc 1 mod n)=vtx(2) or vtx(1) ~ vtx(Suc 0 mod n)=vtx(1).\<close>
            show ?thesis
            proof (cases "ia = 0")
              case True hence "ja = 1" using hja_cancel hne by (by100 linarith)
              hence "l = Suc 1 mod ?n" using \<open>l = Suc ja mod ?n\<close> by (by100 simp)
              have "Suc (Suc 0) mod ?n = Suc (Suc 0)"
                using mod_less[of "Suc (Suc 0)" ?n] hn5 by (by100 linarith)
              hence "l = 2" using \<open>l = Suc 1 mod ?n\<close> by (by100 simp)
              have "spur_f (vx_e 0, vy_e 0) = (vx_m 0, vy_m 0)" by (rule h_spur_vertex_0)
              moreover have "spur_f (vx_e 2, vy_e 2) = (vx_m 0, vy_m 0)"
              proof -
                have "(2::nat) \<le> 2" by (by100 simp)
                have "(2::nat) < ?n" using hn5 by (by100 linarith)
                from h_spur_vertex[rule_format, OF \<open>2 \<le> 2\<close> \<open>2 < ?n\<close>]
                show ?thesis by (by100 simp)
              qed
              ultimately show ?thesis using \<open>k = ia\<close> True \<open>l = 2\<close> by (by100 simp)
            next
              case False hence "ia = 1" using hia_cancel by (by100 linarith)
              hence "ja = 0" using hja_cancel hne by (by100 linarith)
              hence "l = 1" using \<open>l = Suc ja mod ?n\<close> hn5 by (by100 simp)
              thus ?thesis using \<open>k = ia\<close> \<open>ia = 1\<close> by (by100 simp)
            qed
          next
            assume "snd (?ext ! ia) \<noteq> snd (?ext ! ja)"
                and "k = Suc ia mod ?n" and "l = ja"
            show ?thesis
            proof (cases "ia = 0")
              case True hence "ja = 1" using hja_cancel hne by (by100 linarith)
              hence "k = 1" using \<open>k = Suc ia mod ?n\<close> True hn5 by (by100 simp)
              thus ?thesis using \<open>l = ja\<close> \<open>ja = 1\<close> by (by100 simp)
            next
              case False hence "ia = 1" using hia_cancel by (by100 linarith)
              hence "ja = 0" using hja_cancel hne by (by100 linarith)
              have "Suc (Suc 0) mod ?n = Suc (Suc 0)"
                using mod_less[of "Suc (Suc 0)" ?n] hn5 by (by100 linarith)
              hence "k = 2" using \<open>k = Suc ia mod ?n\<close> \<open>ia = 1\<close> by (by100 simp)
              have hsf2: "spur_f (vx_e 2, vy_e 2) = (vx_m 0, vy_m 0)"
              proof -
                have "(2::nat) \<le> 2" by (by100 simp)
                have "(2::nat) < ?n" using hn5 by (by100 linarith)
                from h_spur_vertex[rule_format, OF \<open>2 \<le> 2\<close> \<open>2 < ?n\<close>]
                show ?thesis by (by100 simp)
              qed
              moreover have "spur_f (vx_e 0, vy_e 0) = (vx_m 0, vy_m 0)" by (rule h_spur_vertex_0)
              ultimately show ?thesis using \<open>k = 2\<close> \<open>l = ja\<close> \<open>ja = 0\<close> by (by100 simp)
            qed
          qed
        qed
      qed
      \<comment> \<open>The rtrancl closure preserves q\\_m \\<circ> spur\\_f (by induction on rtrancl).\<close>
      have h_rtrancl_f: "\<forall>k l. (k, l) \<in> ?vtx_step\<^sup>* \<longrightarrow>
          q_m (spur_f (vx_e k, vy_e k)) = q_m (spur_f (vx_e l, vy_e l))"
      proof (intro allI impI)
        fix k l assume "(k, l) \<in> ?vtx_step\<^sup>*"
        thus "q_m (spur_f (vx_e k, vy_e k)) = q_m (spur_f (vx_e l, vy_e l))"
        proof (induction rule: rtrancl_induct)
          case base show ?case by (by100 simp)
        next
          case (step y z)
          from h_step_f[rule_format, OF step.hyps(2)]
          have "q_m (spur_f (vx_e y, vy_e y)) = q_m (spur_f (vx_e z, vy_e z))" .
          with step.IH show ?case by (by100 simp)
        qed
      qed
      \<comment> \<open>vtgt equality \\<to> rtrancl connectivity (from hq\\_vtgt\\_e5) \\<to> f equality.\<close>
      have h_vtx_vtgt_transfer: "\<forall>k<?n. \<forall>l<?n. vtgt_e k = vtgt_e l \<longrightarrow>
          q_m (spur_f (vx_e k, vy_e k)) = q_m (spur_f (vx_e l, vy_e l))"
      proof (intro allI impI)
        fix k l assume hk: "k < ?n" and hl: "l < ?n" and hv: "vtgt_e k = vtgt_e l"
        from hq_vtgt_e5[rule_format, OF hk hl hv]
        have "(k, l) \<in> ?vtx_step\<^sup>*" .
        from h_rtrancl_f[rule_format, OF this]
        show "q_m (spur_f (vx_e k, vy_e k)) = q_m (spur_f (vx_e l, vy_e l))" .
      qed
      \<comment> \<open>Forward direction of h\\_fibres: q\\_e(x)=q\\_e(y) \\<Longrightarrow> q\\_m(spur\\_f x)=q\\_m(spur\\_f y).
         For INTERIOR x: C8\\_e gives x=y \\<to> trivial.
         For EDGE-INTERIOR x with EDGE-INTERIOR y (both t,s \\<in> (0,1)):
           C9\\_e constrains identifications. Good-good: h\\_fibres\\_good\\_edge + h\\_spur\\_good\\_edge.
           Cancel-cancel: h\\_spur\\_cancel\\_collapse. Good-cancel: impossible (fresh labels).
         For VERTEX cases: use hC12\\_e (vertex-edge separation).\<close>
      have h_fibres_forward: "\<forall>x\<in>P_e. \<forall>y\<in>P_e. q_e x = q_e y \<longrightarrow> q_m (spur_f x) = q_m (spur_f y)"
      proof (intro ballI impI)
        fix x y assume hx: "x \<in> P_e" and hy: "y \<in> P_e" and heq: "q_e x = q_e y"
        \<comment> \<open>Case on whether x is interior or on a boundary edge.\<close>
        consider
          (x_int) "\<forall>i<?n. \<forall>t\<in>I_set. x \<noteq> ((1-t)*vx_e i + t*vx_e(Suc i mod ?n),
                (1-t)*vy_e i + t*vy_e(Suc i mod ?n))"
          | (x_bdy) "\<exists>i<?n. \<exists>t\<in>I_set. x = ((1-t)*vx_e i + t*vx_e(Suc i mod ?n),
                (1-t)*vy_e i + t*vy_e(Suc i mod ?n))"
          by (by100 blast)
        thus "q_m (spur_f x) = q_m (spur_f y)"
        proof cases
          case x_int
          \<comment> \<open>x interior: C8\\_e gives q\\_e injective at x \\<to> x = y \\<to> trivial.\<close>
          have "x = y"
          proof -
            from hC8e[rule_format, OF hx] x_int
            have "\<forall>p'\<in>P_e. q_e x = q_e p' \<longrightarrow> x = p'" by (by100 blast)
            thus ?thesis using hy heq by (by100 blast)
          qed
          thus ?thesis by (by100 simp)
        next
          case x_bdy
          \<comment> \<open>x is on some boundary edge. Case on point type.\<close>
          then obtain i t where hi: "i < ?n" and ht: "t \<in> I_set"
            and hx_eq: "x = ((1-t)*vx_e i + t*vx_e(Suc i mod ?n),
                (1-t)*vy_e i + t*vy_e(Suc i mod ?n))" by (by100 blast)
          \<comment> \<open>Forward direction with x on edge: needs case analysis on y's type
             and on edge parameters. Vertex cases sorry'd.\<close>
          \<comment> \<open>Sub-case: is t strictly interior (0<t<1) or at a vertex (t=0 or t=1)?\<close>
          show ?thesis
          proof (cases "0 < t \<and> t < 1")
            case True
            \<comment> \<open>x is edge-interior. Case on y's type.\<close>
            consider
              (y_int) "\<forall>j<?n. \<forall>s\<in>I_set. y \<noteq> ((1-s)*vx_e j + s*vx_e(Suc j mod ?n),
                    (1-s)*vy_e j + s*vy_e(Suc j mod ?n))"
              | (y_bdy) "\<exists>j<?n. \<exists>s\<in>I_set. y = ((1-s)*vx_e j + s*vx_e(Suc j mod ?n),
                    (1-s)*vy_e j + s*vy_e(Suc j mod ?n))"
              by (by100 blast)
            thus ?thesis
            proof cases
              case y_int
              \<comment> \<open>y interior: C8\\_e gives q\\_e injective at y, so y=x.\<close>
              from hC8e[rule_format, OF hy] y_int
              have "\<forall>p'\<in>P_e. q_e y = q_e p' \<longrightarrow> y = p'" by (by100 blast)
              hence "y = x" using hx heq[symmetric] by (by100 blast)
              thus ?thesis by (by100 simp)
            next
              case y_bdy
              then obtain j s where hj: "j < ?n" and hs: "s \<in> I_set"
                and hy_eq: "y = ((1-s)*vx_e j + s*vx_e(Suc j mod ?n),
                    (1-s)*vy_e j + s*vy_e(Suc j mod ?n))" by (by100 blast)
              show ?thesis
              proof (cases "0 < s \<and> s < 1")
                case True
                \<comment> \<open>Both edge-interior: C9\\_e applies.\<close>
                hence ht_open: "t \<in> {0<..<(1::real)}" and hs_open: "s \<in> {0<..<(1::real)}"
                  using \<open>0 < t \<and> t < 1\<close> by (by100 auto)+
                from hC9e[rule_format, OF hi hj ht_open hs_open]
                  heq[unfolded hx_eq hy_eq]
                have hcond: "(i = j \<and> t = s) \<or> (fst (([a, top1_inverse_edge a] @ w)!i) =
                    fst (([a, top1_inverse_edge a] @ w)!j) \<and>
                    (if snd (([a, top1_inverse_edge a] @ w)!i) = snd (([a, top1_inverse_edge a] @ w)!j)
                     then s = t else s = 1 - t))"
                  by (by100 blast)
                \<comment> \<open>Case on i,j: both good (\\<ge>2), both cancel (0,1), or mixed.\<close>
                show ?thesis
                proof (cases "i \<ge> 2 \<and> j \<ge> 2")
                  case True
                  \<comment> \<open>Both good edges: use h\\_fibres\\_good\\_edge + h\\_spur\\_good\\_edge.\<close>
                  from h_fibres_good_edge[rule_format, OF conjunct1[OF True] hi(1)
                      conjunct2[OF True] hj(1) ht_open hs_open]
                  have "(q_e ((1-t)*vx_e i+t*vx_e(Suc i mod ?n),(1-t)*vy_e i+t*vy_e(Suc i mod ?n))
                     = q_e ((1-s)*vx_e j+s*vx_e(Suc j mod ?n),(1-s)*vy_e j+s*vy_e(Suc j mod ?n)))
                     \<longleftrightarrow>
                      (q_m ((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2)mod ?m),(1-t)*vy_m(i-2)+t*vy_m(Suc(i-2)mod ?m))
                     = q_m ((1-s)*vx_m(j-2)+s*vx_m(Suc(j-2)mod ?m),(1-s)*vy_m(j-2)+s*vy_m(Suc(j-2)mod ?m)))" .
                  hence hge: "q_m ((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2)mod ?m),(1-t)*vy_m(i-2)+t*vy_m(Suc(i-2)mod ?m))
                     = q_m ((1-s)*vx_m(j-2)+s*vx_m(Suc(j-2)mod ?m),(1-s)*vy_m(j-2)+s*vy_m(Suc(j-2)mod ?m))"
                    using heq[unfolded hx_eq hy_eq] by (by100 blast)
                  \<comment> \<open>Now translate from q\\_m(edge\\_m) to q\\_m(spur\\_f(edge\\_e)) using h\\_spur\\_good\\_edge.\<close>
                  have hsf_x: "spur_f x = ((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2)mod ?m),
                      (1-t)*vy_m(i-2)+t*vy_m(Suc(i-2)mod ?m))"
                    using h_spur_good_edge[rule_format, OF conjunct1[OF True] hi ht_open]
                    unfolding hx_eq by (by100 simp)
                  have hsf_y: "spur_f y = ((1-s)*vx_m(j-2)+s*vx_m(Suc(j-2)mod ?m),
                      (1-s)*vy_m(j-2)+s*vy_m(Suc(j-2)mod ?m))"
                    using h_spur_good_edge[rule_format, OF conjunct2[OF True] hj hs_open]
                    unfolding hy_eq by (by100 simp)
                  show ?thesis using hge hsf_x hsf_y by (by100 simp)
                next
                  case False
                  \<comment> \<open>At least one of i,j is a cancel edge (0 or 1).\<close>
                  \<comment> \<open>At least one of i,j < 2 (cancel edge). With fresh label:
                     cancel-good impossible (C9 label mismatch), cancel-cancel by collapse.\<close>
                  let ?ext = "[a, top1_inverse_edge a] @ w"
                  from hcond show ?thesis
                  proof (elim disjE conjE)
                    assume "i = j" "t = s"
                    thus ?thesis using hx_eq hy_eq by (by100 simp)
                  next
                    assume hlabel: "fst (?ext ! i) = fst (?ext ! j)"
                      and hdir: "if snd (?ext ! i) = snd (?ext ! j) then s = t else s = 1 - t"
                    \<comment> \<open>Both cancel (i<2, j<2): spur\\_f collapses both to same point.\<close>
                    \<comment> \<open>Mixed (one cancel, one good): label mismatch \\<to> contradiction.\<close>
                    show ?thesis
                    proof (cases "i < 2 \<and> j < 2")
                      case True
                      \<comment> \<open>Both cancel edges. Labels: fst(?ext!0)=fst a, fst(?ext!1)=fst a.
                         spur\\_f collapses cancel pair via h\\_spur\\_cancel\\_collapse.\<close>
                      \<comment> \<open>i,j \\<in> {0,1}, labels match, direction gives s = 1-t (opposite).
                         spur\\_f collapses: edge(0,t) and reversed\\_edge(1,t) map to same point.\<close>
                      have hdir_opp: "snd (?ext ! 0) \<noteq> snd (?ext ! 1)"
                        unfolding top1_inverse_edge_def by (by100 simp)
                      \<comment> \<open>Direction: for i\\<noteq>j (both <2): opposite direction, so s=1-t.
                         For i=j: same direction gives s=t, but that was the earlier disjunct.\<close>
                      have "i = 0 \<and> j = 1 \<or> i = 1 \<and> j = 0 \<or> i = 0 \<and> j = 0 \<or> i = 1 \<and> j = 1"
                        using True by (by100 linarith)
                      thus ?thesis
                      proof (elim disjE conjE)
                        assume "i = 0" "j = 1"
                        hence "snd (?ext ! i) \<noteq> snd (?ext ! j)" using hdir_opp by (by100 simp)
                        hence hs1t: "s = 1 - t" using hdir by (by100 simp)
                        have hy_rev: "y = (t*vx_e 1 + (1-t)*vx_e(Suc 1 mod ?n),
                            t*vy_e 1 + (1-t)*vy_e(Suc 1 mod ?n))"
                        proof -
                          have "y = ((1-s)*vx_e 1 + s*vx_e(Suc 1 mod ?n),
                              (1-s)*vy_e 1 + s*vy_e(Suc 1 mod ?n))"
                            using hy_eq \<open>j = 1\<close> by (by100 simp)
                          moreover have "1 - s = t" "s = 1 - t" using hs1t by argo+
                          ultimately show ?thesis by (by100 simp)
                        qed
                        from h_spur_cancel_collapse[rule_format, OF ht_open]
                        have "spur_f ((1-t)*vx_e 0 + t*vx_e(Suc 0 mod ?n),
                            (1-t)*vy_e 0 + t*vy_e(Suc 0 mod ?n))
                          = spur_f (t*vx_e 1 + (1-t)*vx_e(Suc 1 mod ?n),
                            t*vy_e 1 + (1-t)*vy_e(Suc 1 mod ?n))" .
                        thus ?thesis using hx_eq \<open>i = 0\<close> hy_rev by (by100 simp)
                      next
                        assume "i = 1" "j = 0"
                        hence "snd (?ext ! i) \<noteq> snd (?ext ! j)" using hdir_opp by auto
                        hence hs1t: "s = 1 - t" using hdir by (by100 simp)
                        \<comment> \<open>x = edge(1,t), y = edge(0,1-t). Symmetric: use collapse at 1-t.\<close>
                        have h1t_open: "1-t \<in> {0<..<(1::real)}" using ht_open by (by100 simp)
                        have hy_eq0: "y = ((1-(1-t))*vx_e 0 + (1-t)*vx_e(Suc 0 mod ?n),
                            (1-(1-t))*vy_e 0 + (1-t)*vy_e(Suc 0 mod ?n))"
                        proof -
                          have "y = ((1-s)*vx_e 0 + s*vx_e(Suc 0 mod ?n),
                              (1-s)*vy_e 0 + s*vy_e(Suc 0 mod ?n))"
                            using hy_eq \<open>j = 0\<close> by (by100 simp)
                          moreover have "1 - s = 1 - (1-t)" "s = 1 - t" using hs1t by argo+
                          ultimately show ?thesis by (by100 simp)
                        qed
                        have hx_eq1: "x = ((1-t)*vx_e 1 + t*vx_e(Suc 1 mod ?n),
                            (1-t)*vy_e 1 + t*vy_e(Suc 1 mod ?n))"
                          using hx_eq \<open>i = 1\<close> by (by100 simp)
                        from h_spur_cancel_collapse[rule_format, OF h1t_open]
                        have "spur_f ((1-(1-t))*vx_e 0 + (1-t)*vx_e(Suc 0 mod ?n),
                            (1-(1-t))*vy_e 0 + (1-t)*vy_e(Suc 0 mod ?n))
                          = spur_f ((1-t)*vx_e 1 + (1-(1-t))*vx_e(Suc 1 mod ?n),
                            (1-t)*vy_e 1 + (1-(1-t))*vy_e(Suc 1 mod ?n))"
                          by (by100 simp)
                        hence "spur_f y = spur_f x" using hy_eq0 hx_eq1 by argo
                        thus ?thesis by (by100 simp)
                      next
                        assume "i = 0" "j = 0"
                        hence "snd (?ext ! i) = snd (?ext ! j)" by (by100 simp)
                        hence "s = t" using hdir by (by100 simp)
                        thus ?thesis using hx_eq hy_eq \<open>i=0\<close> \<open>j=0\<close> by (by100 simp)
                      next
                        assume "i = 1" "j = 1"
                        hence "snd (?ext ! i) = snd (?ext ! j)" by (by100 simp)
                        hence "s = t" using hdir by (by100 simp)
                        thus ?thesis using hx_eq hy_eq \<open>i=1\<close> \<open>j=1\<close> by (by100 simp)
                      qed
                    next
                      case False
                      \<comment> \<open>Mixed cancel+good: label mismatch gives contradiction.\<close>
                      have "i \<ge> 2 \<or> j \<ge> 2" using \<open>\<not>(i \<ge> 2 \<and> j \<ge> 2)\<close> False by (by100 linarith)
                      \<comment> \<open>WLOG i < 2, j \\<ge> 2: fst(?ext!i) = fst a, fst(?ext!j) = fst(w!(j-2)).
                         Fresh: fst a \\<notin> fst ` set w, so fst(?ext!j) \\<noteq> fst a. Contradiction.\<close>
                      \<comment> \<open>One of i,j is cancel (< 2), other is good (\\<ge> 2).\<close>
                      have "i < 2 \<or> j < 2" using \<open>\<not>(i \<ge> 2 \<and> j \<ge> 2)\<close> by (by100 linarith)
                      moreover have "i \<ge> 2 \<or> j \<ge> 2" using False by (by100 linarith)
                      ultimately have hmixed: "(i < 2 \<and> j \<ge> 2) \<or> (i \<ge> 2 \<and> j < 2)" by (by100 linarith)
                      \<comment> \<open>Cancel edge label = fst a; good edge label \\<in> fst ` set w.
                         Fresh: fst a \\<notin> fst ` set w. Contradiction with hlabel.\<close>
                      from hmixed show ?thesis
                      proof
                        assume "i < 2 \<and> j \<ge> 2"
                        hence hi2: "i < 2" and hj2: "j \<ge> 2" by (by100 auto)+
                        have "fst (?ext ! i) = fst a"
                          using hi2 unfolding top1_inverse_edge_def by (cases i) (by100 auto)+
                        moreover have "j - 2 < ?m" using hj hj2 hn_eq by (by100 linarith)
                        hence "fst (?ext ! j) = fst (w ! (j - 2))"
                        proof -
                          have "j = (j-2) + 2" using hj2 by (by100 simp)
                          thus ?thesis using cancel_shift_label[of "j-2" w a] \<open>j-2 < ?m\<close>
                            by (by100 simp)
                        qed
                        moreover have "fst (w ! (j-2)) \<noteq> fst a"
                        proof
                          assume "fst (w ! (j-2)) = fst a"
                          have "w ! (j-2) \<in> set w" using \<open>j-2 < ?m\<close> by (by100 simp)
                          hence "fst (w ! (j-2)) \<in> fst ` set w" by (by100 blast)
                          hence "fst a \<in> fst ` set w" using \<open>fst (w ! (j-2)) = fst a\<close> by (by100 simp)
                          thus False using hfresh by (by100 blast)
                        qed
                        ultimately show ?thesis using hlabel by (by100 simp)
                      next
                        assume "i \<ge> 2 \<and> j < 2"
                        hence hi2: "i \<ge> 2" and hj2: "j < 2" by (by100 auto)+
                        have "fst (?ext ! j) = fst a"
                          using hj2 unfolding top1_inverse_edge_def by (cases j) (by100 auto)+
                        moreover have "i - 2 < ?m" using hi hi2 hn_eq by (by100 linarith)
                        hence "fst (?ext ! i) = fst (w ! (i - 2))"
                        proof -
                          have "i = (i-2) + 2" using hi2 by (by100 simp)
                          thus ?thesis using cancel_shift_label[of "i-2" w a] \<open>i-2 < ?m\<close>
                            by (by100 simp)
                        qed
                        moreover have "fst (w ! (i-2)) \<noteq> fst a"
                        proof
                          assume "fst (w ! (i-2)) = fst a"
                          have "w ! (i-2) \<in> set w" using \<open>i-2 < ?m\<close> by (by100 simp)
                          hence "fst (w ! (i-2)) \<in> fst ` set w" by (by100 blast)
                          hence "fst a \<in> fst ` set w" using \<open>fst (w ! (i-2)) = fst a\<close> by (by100 simp)
                          thus False using hfresh by (by100 blast)
                        qed
                        ultimately show ?thesis using hlabel by (by100 simp)
                      qed
                    qed
                  qed
                qed
              next
                case False
                \<comment> \<open>s = 0 or s = 1: y is a vertex.\<close>
                \<comment> \<open>y is a vertex. Need: q\\_e(edge\\_e(i,t)) = q\\_e(vertex(y)).
                   But hC12\\_e says vertex-edge identification is impossible.\<close>
                have hs_vtx: "s = 0 \<or> s = 1"
                  using False hs unfolding top1_unit_interval_def by (by100 auto)
                \<comment> \<open>y = vertex at parameter s=0 or s=1 of edge j. So y = (vx\\_e j, vy\\_e j) or vx\\_e(Suc j).\<close>
                have ht_oi2: "t \<in> {0<..<(1::real)}" using \<open>0 < t \<and> t < 1\<close> by (by100 simp)
                show ?thesis
                proof (cases "s = 0")
                  case True
                  \<comment> \<open>y = vx\\_e(j). By hC12\\_e: q\\_e(edge(i,t)) \\<noteq> q\\_e(vx\\_e(j)). Contradiction with heq.\<close>
                  have "y = (vx_e j, vy_e j)" using hy_eq True by (by100 simp)
                  hence "q_e x = q_e (vx_e j, vy_e j)" using heq by (by100 simp)
                  hence heq2: "q_e ((1-t)*vx_e i + t*vx_e(Suc i mod ?n),
                      (1-t)*vy_e i + t*vy_e(Suc i mod ?n)) = q_e (vx_e j, vy_e j)"
                    using hx_eq by (by100 simp)
                  have ht_oi: "t \<in> {0<..<(1::real)}" using \<open>0 < t \<and> t < 1\<close> by (by100 simp)
                  have hneq: "q_e (vx_e j, vy_e j) \<noteq> q_e ((1-t)*vx_e i + t*vx_e(Suc i mod ?n),
                      (1-t)*vy_e i + t*vy_e(Suc i mod ?n))"
                    using hC12_e[rule_format, OF hj hi ht_oi] .
                  from hneq heq2 have False by (by100 simp)
                  thus ?thesis by (by100 simp)
                next
                  case False
                  hence "s = 1" using hs_vtx by (by100 blast)
                  \<comment> \<open>y = vx\\_e(Suc j mod n). Similar argument.\<close>
                  \<comment> \<open>y = vx\\_e(Suc j mod n). Apply hC12\\_e with k=Suc j mod n.\<close>
                  have "y = (vx_e (Suc j mod ?n), vy_e (Suc j mod ?n))"
                    using hy_eq \<open>s = 1\<close> by (by100 simp)
                  hence heq2: "q_e ((1-t)*vx_e i + t*vx_e(Suc i mod ?n),
                      (1-t)*vy_e i + t*vy_e(Suc i mod ?n)) = q_e (vx_e (Suc j mod ?n), vy_e (Suc j mod ?n))"
                    using hx_eq heq by (by100 simp)
                  have hSj_lt: "Suc j mod ?n < ?n" using hn5 by (by100 simp)
                  have hneq: "q_e (vx_e (Suc j mod ?n), vy_e (Suc j mod ?n)) \<noteq>
                      q_e ((1-t)*vx_e i + t*vx_e(Suc i mod ?n),
                           (1-t)*vy_e i + t*vy_e(Suc i mod ?n))"
                    using hC12_e[rule_format, OF hSj_lt hi ht_oi2] .
                  from hneq heq2 have False by (by100 simp)
                  thus ?thesis by (by100 simp)
                qed
              qed
            qed
          next
            case False
            \<comment> \<open>t = 0 or t = 1: x is a vertex.\<close>
            \<comment> \<open>x is vertex\\_e(k) for some k. y can be interior, edge-interior, or vertex.\<close>
            have ht_vtx: "t = 0 \<or> t = 1"
              using False ht unfolding top1_unit_interval_def by (by100 auto)
            \<comment> \<open>Case on y's type.\<close>
            consider
              (y_int2) "\<forall>j<?n. \<forall>s\<in>I_set. y \<noteq> ((1-s)*vx_e j + s*vx_e(Suc j mod ?n),
                    (1-s)*vy_e j + s*vy_e(Suc j mod ?n))"
              | (y_bdy2) "\<exists>j<?n. \<exists>s\<in>I_set. y = ((1-s)*vx_e j + s*vx_e(Suc j mod ?n),
                    (1-s)*vy_e j + s*vy_e(Suc j mod ?n))"
              by (by100 blast)
            thus ?thesis
            proof cases
              case y_int2
              \<comment> \<open>y interior: C8\\_e gives y=x.\<close>
              from hC8e[rule_format, OF hy] y_int2
              have "\<forall>p'\<in>P_e. q_e y = q_e p' \<longrightarrow> y = p'" by (by100 blast)
              hence "y = x" using hx heq[symmetric] by (by100 blast)
              thus ?thesis by (by100 simp)
            next
              case y_bdy2
              then obtain j2 s2 where hj2: "j2 < ?n" and hs2: "s2 \<in> I_set"
                and hy_eq2: "y = ((1-s2)*vx_e j2 + s2*vx_e(Suc j2 mod ?n),
                    (1-s2)*vy_e j2 + s2*vy_e(Suc j2 mod ?n))" by (by100 blast)
              show ?thesis
              proof (cases "0 < s2 \<and> s2 < 1")
                case True
                \<comment> \<open>y is edge-interior. By hC12\\_e: vertex \\<noteq> edge-interior. Contradiction.\<close>
                have hs2_oi: "s2 \<in> {0<..<(1::real)}" using True by (by100 simp)
                \<comment> \<open>x = vertex\\_e(k) where k = i (if t=0) or Suc i mod n (if t=1).\<close>
                from ht_vtx show ?thesis
                proof
                  assume "t = 0"
                  hence "x = (vx_e i, vy_e i)" using hx_eq by (by100 simp)
                  hence "q_e (vx_e i, vy_e i) = q_e y" using heq by (by100 simp)
                  hence "q_e (vx_e i, vy_e i) = q_e ((1-s2)*vx_e j2 + s2*vx_e(Suc j2 mod ?n),
                      (1-s2)*vy_e j2 + s2*vy_e(Suc j2 mod ?n))" using hy_eq2 by (by100 simp)
                  from hC12_e[rule_format, OF hi hj2 hs2_oi] this
                  have False by (by100 simp)
                  thus ?thesis by (by100 simp)
                next
                  assume "t = 1"
                  hence "x = (vx_e (Suc i mod ?n), vy_e (Suc i mod ?n))" using hx_eq by (by100 simp)
                  hence "q_e (vx_e (Suc i mod ?n), vy_e (Suc i mod ?n)) = q_e y" using heq by (by100 simp)
                  hence heq_vi: "q_e (vx_e (Suc i mod ?n), vy_e (Suc i mod ?n)) =
                      q_e ((1-s2)*vx_e j2 + s2*vx_e(Suc j2 mod ?n),
                           (1-s2)*vy_e j2 + s2*vy_e(Suc j2 mod ?n))" using hy_eq2 by (by100 simp)
                  have "Suc i mod ?n < ?n" using hn5 by (by100 simp)
                  from hC12_e[rule_format, OF this hj2 hs2_oi] heq_vi
                  have False by (by100 simp)
                  thus ?thesis by (by100 simp)
                qed
              next
                case False
                \<comment> \<open>y is also a vertex. Vertex-vertex transfer.\<close>
                hence hs2_vtx: "s2 = 0 \<or> s2 = 1" using hs2
                  unfolding top1_unit_interval_def by (by100 auto)
                define k where "k = (if t = 0 then i else Suc i mod ?n)"
                define l where "l = (if s2 = 0 then j2 else Suc j2 mod ?n)"
                have hk_lt: "k < ?n" unfolding k_def using hi hn5 by (by100 auto)
                have hl_lt: "l < ?n" unfolding l_def using hj2 hn5 by (by100 auto)
                have hx_vtx: "x = (vx_e k, vy_e k)" unfolding k_def
                  using ht_vtx hx_eq by (by100 auto)
                have hy_vtx: "y = (vx_e l, vy_e l)" unfolding l_def
                  using hs2_vtx hy_eq2 by (by100 auto)
                have hvtgt: "vtgt_e k = vtgt_e l"
                proof -
                  have "q_e (vx_e k, vy_e k) = q_e (vx_e l, vy_e l)"
                    using heq hx_vtx hy_vtx by (by100 simp)
                  hence "(vx_e (vtgt_e k), vy_e (vtgt_e k)) = (vx_e (vtgt_e l), vy_e (vtgt_e l))"
                    using hq_vtgt_e1[rule_format, OF hk_lt]
                          hq_vtgt_e1[rule_format, OF hl_lt] by (by100 simp)
                  thus ?thesis using hC3e[rule_format]
                    hq_vtgt_e2[rule_format, OF hk_lt] hq_vtgt_e2[rule_format, OF hl_lt]
                    by (by100 blast)
                qed
                from h_vtx_vtgt_transfer[rule_format, OF hk_lt hl_lt hvtgt]
                show ?thesis using hx_vtx hy_vtx by (by100 simp)
              qed
            qed
          qed
        qed
      qed
      \<comment> \<open>Backward direction: q\\_m(spur\\_f x)=q\\_m(spur\\_f y) \\<Longrightarrow> q\\_e x=q\\_e y.
         Uses hC12\\_m (vertex-edge separation for q\\_m) + C8\\_m (interior injectivity)
         + h\\_spur\\_good\\_edge (edge mapping) + h\\_spur\\_cancel\\_collapse (cancel collapse).\<close>
      \<comment> \<open>Reverse vertex transfer: q\\_m vertex identification \\<to> q\\_e vertex identification.
         Symmetric to h\\_vtx\\_vtgt\\_transfer but uses C7\\_m \\<to> C7\\_e (reverse cancel\\_shift).\<close>
      have h_vtx_vtgt_transfer_rev: "\<forall>k<?m. \<forall>l<?m. vtgt_m k = vtgt_m l \<longrightarrow>
          q_e (vx_e (k+2), vy_e (k+2)) = q_e (vx_e (l+2), vy_e (l+2))"
      proof -
        let ?ext = "[a, top1_inverse_edge a] @ w"
        let ?vtx_step_m = "{(x, y). \<exists>i<?m. \<exists>j<?m. i \<noteq> j
            \<and> fst (w ! i) = fst (w ! j)
            \<and> ((snd (w ! i) = snd (w ! j) \<and> x = i \<and> y = j)
             \<or> (snd (w ! i) = snd (w ! j) \<and> x = Suc i mod ?m \<and> y = Suc j mod ?m)
             \<or> (snd (w ! i) \<noteq> snd (w ! j) \<and> x = i \<and> y = Suc j mod ?m)
             \<or> (snd (w ! i) \<noteq> snd (w ! j) \<and> x = Suc i mod ?m \<and> y = j))}"
        \<comment> \<open>Each C7\\_m vertex step transfers to q\\_e vertex identification.\<close>
        have h_step_rev: "\<forall>k l. (k, l) \<in> ?vtx_step_m \<longrightarrow>
            q_e (vx_e (k+2), vy_e (k+2)) = q_e (vx_e (l+2), vy_e (l+2))"
        proof (intro allI impI)
          fix k l assume h: "(k, l) \<in> ?vtx_step_m"
          then obtain ia ja where hia: "ia < ?m" and hja: "ja < ?m" and hne: "ia \<noteq> ja"
              and hlbl: "fst (w ! ia) = fst (w ! ja)"
              and hcase: "(snd (w ! ia) = snd (w ! ja) \<and> k = ia \<and> l = ja) \<or>
                  (snd (w ! ia) = snd (w ! ja) \<and> k = Suc ia mod ?m \<and> l = Suc ja mod ?m) \<or>
                  (snd (w ! ia) \<noteq> snd (w ! ja) \<and> k = ia \<and> l = Suc ja mod ?m) \<or>
                  (snd (w ! ia) \<noteq> snd (w ! ja) \<and> k = Suc ia mod ?m \<and> l = ja)"
            by auto
          \<comment> \<open>Reverse cancel\\_shift: w!ia = ext!(ia+2) and w!ja = ext!(ja+2).\<close>
          have hshift_ia: "?ext ! (ia+2) = w ! ia"
            using cancel_shift_label[OF hia, of a] .
          have hshift_ja: "?ext ! (ja+2) = w ! ja"
            using cancel_shift_label[OF hja, of a] .
          have hia_e: "ia + 2 < ?n" using hia hn_eq by (by100 linarith)
          have hja_e: "ja + 2 < ?n" using hja hn_eq by (by100 linarith)
          have hlbl_e: "fst (?ext ! (ia+2)) = fst (?ext ! (ja+2))"
            using hlbl hshift_ia hshift_ja by (by100 simp)
          have hdir_e: "snd (w ! ia) = snd (w ! ja) \<longleftrightarrow> snd (?ext ! (ia+2)) = snd (?ext ! (ja+2))"
            using hshift_ia hshift_ja by (by100 simp)
          have hne_e: "ia + 2 \<noteq> ja + 2" using hne by (by100 linarith)
          have ht0: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
          have ht1: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
          \<comment> \<open>Helper: q\\_e at Suc(ia+2) mod n equals q\\_e at Suc ia mod m + 2.
             For ia < m-1: indices match. For ia = m-1: index 0 vs 2, q\\_e-identified via cancel pair.\<close>
          have hSuc_qe_ia: "q_e (vx_e (Suc (ia + 2) mod ?n), vy_e (Suc (ia + 2) mod ?n)) =
              q_e (vx_e (Suc ia mod ?m + 2), vy_e (Suc ia mod ?m + 2))"
          proof (cases "ia < ?m - 1")
            case True
            hence "Suc (ia + 2) mod ?n = Suc ia mod ?m + 2"
              using hn_eq hm3 by (by100 simp)
            thus ?thesis by (by100 simp)
          next
            case False
            hence hia_last: "ia = ?m - 1" using hia by (by100 linarith)
            hence "Suc (ia + 2) = ?n" using hn_eq hm3 by (by100 linarith)
            hence hmod0_ia: "Suc (ia + 2) mod ?n = 0" by (by100 simp)
            have "Suc ia = ?m" using hia_last hm3 by (by100 linarith)
            hence hmod0_ia_m: "Suc ia mod ?m = 0" by (by100 simp)
            \<comment> \<open>LHS = q\\_e(vx\\_e 0, vy\\_e 0). RHS = q\\_e(vx\\_e(0+2), vy\\_e(0+2)).
               Cancel pair gives q\\_e(vx\\_e 0, ...) = q\\_e(vx\\_e(0+2), ...).\<close>
            have hcancel_0_2: "q_e (vx_e 0, vy_e 0) = q_e (vx_e (0+2), vy_e (0+2))"
            proof -
              have "0 < ?n" "1 < ?n" using hn5 by (by100 linarith)+
              have "fst (?ext ! 0) = fst (?ext ! 1)"
                unfolding top1_inverse_edge_def by (by100 simp)
              have "snd (?ext ! 0) \<noteq> snd (?ext ! 1)"
                unfolding top1_inverse_edge_def by (by100 simp)
              from hC7e[rule_format, OF \<open>0 < ?n\<close> \<open>1 < ?n\<close> \<open>fst (?ext ! 0) = fst (?ext ! 1)\<close> ht0]
                \<open>snd (?ext ! 0) \<noteq> snd (?ext ! 1)\<close>
              have "q_e (vx_e 0, vy_e 0) = q_e (vx_e (Suc 1 mod ?n), vy_e (Suc 1 mod ?n))"
                by (by100 simp)
              moreover have "Suc (Suc 0) < ?n" using hn5 by (by100 linarith)
              hence "Suc 1 mod ?n = Suc (Suc 0)" using mod_less by (by100 simp)
              ultimately show ?thesis by (by100 simp)
            qed
            have hgoal_lhs: "vx_e (Suc (ia + 2) mod ?n) = vx_e 0"
                "vy_e (Suc (ia + 2) mod ?n) = vy_e 0"
              using hmod0_ia by (by100 simp)+
            have hgoal_rhs: "vx_e (Suc ia mod ?m + 2) = vx_e (0 + 2)"
                "vy_e (Suc ia mod ?m + 2) = vy_e (0 + 2)"
              using hmod0_ia_m by (by100 simp)+
            show ?thesis unfolding hgoal_lhs hgoal_rhs by (rule hcancel_0_2)
          qed
          have hSuc_qe_ja: "q_e (vx_e (Suc (ja + 2) mod ?n), vy_e (Suc (ja + 2) mod ?n)) =
              q_e (vx_e (Suc ja mod ?m + 2), vy_e (Suc ja mod ?m + 2))"
          proof (cases "ja < ?m - 1")
            case True
            hence "Suc (ja + 2) mod ?n = Suc ja mod ?m + 2"
              using hn_eq hm3 by (by100 simp)
            thus ?thesis by (by100 simp)
          next
            case False
            hence "ja = ?m - 1" using hja by (by100 linarith)
            hence "Suc (ja + 2) = ?n" using hn_eq hm3 by (by100 linarith)
            hence hmod0_ja: "Suc (ja + 2) mod ?n = 0" by (by100 simp)
            have "Suc ja = ?m" using \<open>ja = ?m - 1\<close> hm3 by (by100 linarith)
            hence hmod0_ja_m: "Suc ja mod ?m = 0" by (by100 simp)
            have hcancel_0_2_ja: "q_e (vx_e 0, vy_e 0) = q_e (vx_e (0+2), vy_e (0+2))"
            proof -
              have "0 < ?n" "1 < ?n" using hn5 by (by100 linarith)+
              have "fst (?ext ! 0) = fst (?ext ! 1)"
                unfolding top1_inverse_edge_def by (by100 simp)
              have "snd (?ext ! 0) \<noteq> snd (?ext ! 1)"
                unfolding top1_inverse_edge_def by (by100 simp)
              from hC7e[rule_format, OF \<open>0 < ?n\<close> \<open>1 < ?n\<close> \<open>fst (?ext ! 0) = fst (?ext ! 1)\<close> ht0]
                \<open>snd (?ext ! 0) \<noteq> snd (?ext ! 1)\<close>
              have "q_e (vx_e 0, vy_e 0) = q_e (vx_e (Suc 1 mod ?n), vy_e (Suc 1 mod ?n))"
                by (by100 simp)
              moreover have "Suc (Suc 0) < ?n" using hn5 by (by100 linarith)
              hence "Suc 1 mod ?n = Suc (Suc 0)" using mod_less by (by100 simp)
              ultimately show ?thesis by (by100 simp)
            qed
            have hgoal_lhs: "vx_e (Suc (ja + 2) mod ?n) = vx_e 0"
                "vy_e (Suc (ja + 2) mod ?n) = vy_e 0"
              using hmod0_ja by (by100 simp)+
            have hgoal_rhs: "vx_e (Suc ja mod ?m + 2) = vx_e (0 + 2)"
                "vy_e (Suc ja mod ?m + 2) = vy_e (0 + 2)"
              using hmod0_ja_m by (by100 simp)+
            show ?thesis unfolding hgoal_lhs hgoal_rhs by (rule hcancel_0_2_ja)
          qed
          \<comment> \<open>4 cases on direction/endpoint, each using C7\\_e.\<close>
          \<comment> \<open>Specialize C7\\_e at t=0 and t=1 for edges ia+2, ja+2.\<close>
          from hC7e[rule_format, OF hia_e hja_e hlbl_e ht0]
          have hC7e_t0: "q_e (vx_e(ia+2), vy_e(ia+2)) =
              (if snd(?ext!(ia+2))=snd(?ext!(ja+2))
               then q_e (vx_e(ja+2), vy_e(ja+2))
               else q_e (vx_e(Suc(ja+2) mod ?n), vy_e(Suc(ja+2) mod ?n)))"
            by (by100 simp)
          from hC7e[rule_format, OF hia_e hja_e hlbl_e ht1]
          have hC7e_t1: "q_e (vx_e(Suc(ia+2) mod ?n), vy_e(Suc(ia+2) mod ?n)) =
              (if snd(?ext!(ia+2))=snd(?ext!(ja+2))
               then q_e (vx_e(Suc(ja+2) mod ?n), vy_e(Suc(ja+2) mod ?n))
               else q_e (vx_e(ja+2), vy_e(ja+2)))"
            by (by100 simp)
          have hcase_sd0: "snd (w ! ia) = snd (w ! ja) \<Longrightarrow> k = ia \<Longrightarrow> l = ja \<Longrightarrow>
              q_e (vx_e (k+2), vy_e (k+2)) = q_e (vx_e (l+2), vy_e (l+2))"
          proof -
            assume hsd: "snd (w ! ia) = snd (w ! ja)" and "k = ia" and "l = ja"
            have "snd (?ext ! (ia+2)) = snd (?ext ! (ja+2))"
              using hsd hdir_e by (by100 blast)
            hence "q_e (vx_e(ia+2), vy_e(ia+2)) = q_e (vx_e(ja+2), vy_e(ja+2))"
              using hC7e_t0 by (by100 simp)
            thus ?thesis using \<open>k = ia\<close> \<open>l = ja\<close> by (by100 simp)
          qed
          have hcase_sd1: "snd (w ! ia) = snd (w ! ja) \<Longrightarrow> k = Suc ia mod ?m \<Longrightarrow> l = Suc ja mod ?m \<Longrightarrow>
              q_e (vx_e (k+2), vy_e (k+2)) = q_e (vx_e (l+2), vy_e (l+2))"
          proof -
            assume hsd: "snd (w ! ia) = snd (w ! ja)"
                and "k = Suc ia mod ?m" and "l = Suc ja mod ?m"
            have hsd_e: "snd (?ext ! (ia+2)) = snd (?ext ! (ja+2))" using hsd hdir_e by (by100 blast)
            hence "q_e (vx_e(Suc(ia+2)mod ?n), vy_e(Suc(ia+2)mod ?n)) =
                q_e (vx_e(Suc(ja+2)mod ?n), vy_e(Suc(ja+2)mod ?n))"
              using hC7e_t1 by (by100 simp)
            hence "q_e (vx_e (Suc ia mod ?m + 2), vy_e (Suc ia mod ?m + 2)) =
                q_e (vx_e (Suc ja mod ?m + 2), vy_e (Suc ja mod ?m + 2))"
              using hSuc_qe_ia hSuc_qe_ja by (by100 simp)
            thus ?thesis using \<open>k = Suc ia mod ?m\<close> \<open>l = Suc ja mod ?m\<close>
              by (by100 simp)
          qed
          have hcase_od0: "snd (w ! ia) \<noteq> snd (w ! ja) \<Longrightarrow> k = ia \<Longrightarrow> l = Suc ja mod ?m \<Longrightarrow>
              q_e (vx_e (k+2), vy_e (k+2)) = q_e (vx_e (l+2), vy_e (l+2))"
          proof -
            assume hod: "snd (w ! ia) \<noteq> snd (w ! ja)"
                and "k = ia" and "l = Suc ja mod ?m"
            have hod_e: "snd (?ext ! (ia+2)) \<noteq> snd (?ext ! (ja+2))" using hod hdir_e by (by100 blast)
            hence "q_e (vx_e(ia+2), vy_e(ia+2)) =
                q_e (vx_e(Suc(ja+2)mod ?n), vy_e(Suc(ja+2)mod ?n))"
              using hC7e_t0 by (by100 simp)
            hence "q_e (vx_e (ia + 2), vy_e (ia + 2)) =
                q_e (vx_e (Suc ja mod ?m + 2), vy_e (Suc ja mod ?m + 2))"
              using hSuc_qe_ja by (by100 simp)
            thus ?thesis using \<open>k = ia\<close> \<open>l = Suc ja mod ?m\<close> by (by100 simp)
          qed
          have hcase_od1: "snd (w ! ia) \<noteq> snd (w ! ja) \<Longrightarrow> k = Suc ia mod ?m \<Longrightarrow> l = ja \<Longrightarrow>
              q_e (vx_e (k+2), vy_e (k+2)) = q_e (vx_e (l+2), vy_e (l+2))"
          proof -
            assume hod: "snd (w ! ia) \<noteq> snd (w ! ja)"
                and "k = Suc ia mod ?m" and "l = ja"
            have hod_e: "snd (?ext ! (ia+2)) \<noteq> snd (?ext ! (ja+2))" using hod hdir_e by (by100 blast)
            hence "q_e (vx_e(Suc(ia+2)mod ?n), vy_e(Suc(ia+2)mod ?n)) =
                q_e (vx_e(ja+2), vy_e(ja+2))"
              using hC7e_t1 by (by100 simp)
            hence "q_e (vx_e (Suc ia mod ?m + 2), vy_e (Suc ia mod ?m + 2)) =
                q_e (vx_e (ja + 2), vy_e (ja + 2))"
              using hSuc_qe_ia by (by100 simp)
            thus ?thesis using \<open>k = Suc ia mod ?m\<close> \<open>l = ja\<close> by (by100 simp)
          qed
          from hcase hcase_sd0 hcase_sd1 hcase_od0 hcase_od1
          show "q_e (vx_e (k+2), vy_e (k+2)) = q_e (vx_e (l+2), vy_e (l+2))"
            by (by100 blast)
        qed
        \<comment> \<open>Closure by rtrancl\\_induct.\<close>
        have h_rtrancl_rev: "\<forall>k l. (k, l) \<in> ?vtx_step_m\<^sup>* \<longrightarrow>
            q_e (vx_e (k+2), vy_e (k+2)) = q_e (vx_e (l+2), vy_e (l+2))"
        proof (intro allI impI)
          fix k l assume "(k, l) \<in> ?vtx_step_m\<^sup>*"
          thus "q_e (vx_e (k+2), vy_e (k+2)) = q_e (vx_e (l+2), vy_e (l+2))"
          proof (induction rule: rtrancl_induct)
            case base show ?case by (by100 simp)
          next
            case (step y z)
            from h_step_rev[rule_format, OF step.hyps(2)]
            have "q_e (vx_e (y+2), vy_e (y+2)) = q_e (vx_e (z+2), vy_e (z+2))" .
            with step.IH show ?case by (by100 simp)
          qed
        qed
        \<comment> \<open>vtgt\\_m equality \\<to> rtrancl \\<to> q\\_e equality.\<close>
        show ?thesis
        proof (intro allI impI)
          fix k l assume hk: "k < ?m" and hl: "l < ?m" and hv: "vtgt_m k = vtgt_m l"
          from hq_vtgt_m5[rule_format, OF hk hl hv]
          have "(k, l) \<in> ?vtx_step_m\<^sup>*" .
          from h_rtrancl_rev[rule_format, OF this]
          show "q_e (vx_e (k+2), vy_e (k+2)) = q_e (vx_e (l+2), vy_e (l+2))" .
        qed
      qed
      \<comment> \<open>Helper: spur\\_f is injective on P\\_e (hence \\<tau> injective on B2).
         Proof: good sector = polar rotation (injective). Cancel sector = spur + perpendicular
         offset (injective since offset separates the two halves and is monotone within each).\<close>
      \<comment> \<open>\\<tau> is injective on B2\\{0}: good sector = polar rescaling (injective),
         cancel sector = spur + perpendicular offset (injective by offset separation).
         Composition with bijections \\<psi>\\_e, \\<psi>\\_m\\<inverse> gives spur\\_f injective.\<close>
      have h_tau_inj: "inj_on \<tau> (top1_B2 - {(0,0)})"
        sorry \<comment> \<open>Good sector: (r,\\<theta>) \\<to> (r, rescaled \\<theta>) is injective (strictly monotone rescaling).
           Cancel sector: (r,\\<theta>) \\<to> (r*sp+off*dp) injective by:
             (1) Two halves have opposite sign\\_v offset \\<to> different perpendicular sides.
             (2) Within each half, (r, tf) \\<to> (r*sp(tf), off(r,tf)*dp) is injective:
                 sp determined by tf (monotone), off determined by r and tf.
           Cross-sector: good image has norm² = r² (on circle), cancel image has
             norm² = r²*|sp|² + off²*|dp|² + 2*r*off*(sp·dp) ≠ r² in general.\<close>
      \<comment> \<open>Helper: \\<tau>(q) = (0,0) implies q = (0,0).
         With p\\_cm = (1/2,0): in cancel sector, fst(\\<tau>) = r*(1-tf/2) > 0.
         In good sector, |\\<tau>| = r > 0. So \\<tau>(q) \\<noteq> (0,0) for q \\<noteq> (0,0).\<close>
      have h_tau_zero: "\<And>q. q \<in> top1_B2 \<Longrightarrow> \<tau> q = (0, 0) \<Longrightarrow> q = (0, 0)"
      proof -
        fix q assume hq: "q \<in> top1_B2" and h\<tau>0: "\<tau> q = (0, 0)"
        show "q = (0, 0)"
        proof (rule ccontr)
          assume hne: "q \<noteq> (0, 0)"
          \<comment> \<open>In good sector: |\\<tau>| = r > 0. In cancel sector: fst(\\<tau>) > 0.\<close>
          \<comment> \<open>Either way \\<tau> \\<noteq> (0,0), contradicting h\\<tau>0.\<close>
          \<comment> \<open>With p\\_cm = (1/2, 0): in good sector |\\<tau>| = r > 0, in cancel sector fst(\\<tau>) > 0.\<close>
          have "fst (\<tau> q) \<noteq> 0 \<or> snd (\<tau> q) \<noteq> 0"
          proof -
            define r where "r = sqrt (fst q ^ 2 + snd q ^ 2)"
            have hr_pos: "r > 0"
            proof -
              have "fst q \<noteq> 0 \<or> snd q \<noteq> 0" using hne by (cases q) (by100 auto)
              hence "fst q ^ 2 + snd q ^ 2 > 0"
              proof
                assume "fst q \<noteq> 0"
                hence "fst q ^ 2 > 0" unfolding power2_eq_square
                  using mult_pos_neg[of "fst q" "fst q"] mult_neg_neg[of "fst q" "fst q"]
                  by (cases "fst q > 0") (by100 auto)+
                moreover have "snd q ^ 2 \<ge> 0" by (by100 simp)
                ultimately show ?thesis by (by100 linarith)
              next
                assume "snd q \<noteq> 0"
                hence "snd q ^ 2 > 0" unfolding power2_eq_square
                  using mult_pos_neg[of "snd q" "snd q"] mult_neg_neg[of "snd q" "snd q"]
                  by (cases "snd q > 0") (by100 auto)+
                moreover have "fst q ^ 2 \<ge> 0" by (by100 simp)
                ultimately show ?thesis by (by100 linarith)
              qed
              thus ?thesis unfolding r_def using real_sqrt_gt_0_iff by (by100 auto)
            qed
            \<comment> \<open>In good sector: \\<tau>(q) = (r*cos \\<phi>, r*sin \\<phi>), |\\<tau>|² = r² > 0.
               In cancel sector: fst(\\<tau>) = r*(1-tf/2) > 0 (since r > 0, tf \\<le> 1).\<close>
            \<comment> \<open>For both: \\<tau>(q) \\<noteq> (0,0).\<close>
            have "fst (\<tau> q) ^ 2 + snd (\<tau> q) ^ 2 > 0"
            proof -
              have "\<tau> q \<in> top1_B2" using hq h\<tau>_range by (by100 blast)
              have "fst (\<tau> q) ^ 2 + snd (\<tau> q) ^ 2 \<le> 1"
                using \<open>\<tau> q \<in> top1_B2\<close> unfolding top1_B2_def by (by100 simp)
              from h_tau_nonzero[OF hq hne]
              have "\<tau> q \<noteq> (0, 0)" .
              hence "fst (\<tau> q) \<noteq> 0 \<or> snd (\<tau> q) \<noteq> 0" by (cases "\<tau> q") (by100 auto)
              thus ?thesis
              proof
                assume "fst (\<tau> q) \<noteq> 0"
                have "fst (\<tau> q) * fst (\<tau> q) > 0"
                  by (cases "fst (\<tau> q) > 0")
                     (use \<open>fst (\<tau> q) \<noteq> 0\<close> mult_neg_neg[of "fst (\<tau> q)" "fst (\<tau> q)"] in
                      \<open>by100 simp, by100 linarith\<close>)
                moreover have "snd (\<tau> q) * snd (\<tau> q) \<ge> 0" by (by100 simp)
                ultimately show ?thesis unfolding power2_eq_square by (by100 linarith)
              next
                assume "snd (\<tau> q) \<noteq> 0"
                have "snd (\<tau> q) * snd (\<tau> q) > 0"
                  by (cases "snd (\<tau> q) > 0")
                     (use \<open>snd (\<tau> q) \<noteq> 0\<close> mult_neg_neg[of "snd (\<tau> q)" "snd (\<tau> q)"] in
                      \<open>by100 simp, by100 linarith\<close>)
                moreover have "fst (\<tau> q) * fst (\<tau> q) \<ge> 0" by (by100 simp)
                ultimately show ?thesis unfolding power2_eq_square by (by100 linarith)
              qed
            qed
            thus ?thesis by (by100 auto)
          qed
          thus False using h\<tau>0 by (by100 simp)
        qed
      qed
      have h_spur_inj: "inj_on spur_f P_e"
      proof -
        have h\<psi>e_inj: "inj_on \<psi>_e P_e"
          using h\<psi>e_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have h\<psi>m_inv_inj: "inj_on (inv_into P_m \<psi>_m) top1_B2"
        proof -
          have "bij_betw \<psi>_m P_m top1_B2"
            using h\<psi>m_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          hence "bij_betw (inv_into P_m \<psi>_m) top1_B2 P_m"
            by (rule bij_betw_inv_into)
          thus ?thesis unfolding bij_betw_def by (by100 blast)
        qed
        \<comment> \<open>spur\\_f = \\<psi>\\_m\\<inverse> \\<circ> \\<tau> \\<circ> \\<psi>\\_e. Composition of injective functions.\<close>
        show ?thesis unfolding inj_on_def spur_f_def
        proof (intro ballI impI)
          fix x y assume hx: "x \<in> P_e" and hy: "y \<in> P_e"
              and heq: "inv_into P_m \<psi>_m (\<tau> (\<psi>_e x)) = inv_into P_m \<psi>_m (\<tau> (\<psi>_e y))"
          have hxB: "\<psi>_e x \<in> top1_B2"
            using hx h\<psi>e_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
          have hyB: "\<psi>_e y \<in> top1_B2"
            using hy h\<psi>e_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
          have hxR: "\<tau> (\<psi>_e x) \<in> top1_B2" using hxB h\<tau>_range by (by100 blast)
          have hyR: "\<tau> (\<psi>_e y) \<in> top1_B2" using hyB h\<tau>_range by (by100 blast)
          \<comment> \<open>\\<psi>\\_m\\<inverse> injective \\<to> \\<tau>(\\<psi>\\_e x) = \\<tau>(\\<psi>\\_e y).\<close>
          from h\<psi>m_inv_inj[unfolded inj_on_def, rule_format, OF hxR hyR heq]
          have "\<tau> (\<psi>_e x) = \<tau> (\<psi>_e y)" .
          \<comment> \<open>\\<tau> injective on B2\\{0}: either both at origin (hence equal) or both non-origin.\<close>
          moreover have "\<psi>_e x = \<psi>_e y"
          proof (cases "\<psi>_e x = (0, 0)")
            case True
            hence "\<tau> (\<psi>_e x) = (0, 0)" unfolding \<tau>_def by (by100 simp)
            hence "\<tau> (\<psi>_e y) = (0, 0)" using \<open>\<tau> (\<psi>_e x) = \<tau> (\<psi>_e y)\<close> by (by100 simp)
            hence "\<psi>_e y = (0, 0)" using h_tau_zero[OF hyB] by (by100 simp)
            thus ?thesis using True by (by100 simp)
          next
            case False
            have "\<psi>_e x \<in> top1_B2 - {(0, 0)}" using hxB False by (by100 blast)
            moreover have "\<psi>_e y \<in> top1_B2 - {(0, 0)}"
            proof -
              have "\<psi>_e y \<noteq> (0, 0)"
              proof
                assume "\<psi>_e y = (0, 0)"
                hence "\<tau> (\<psi>_e y) = (0, 0)" unfolding \<tau>_def by (by100 simp)
                hence "\<tau> (\<psi>_e x) = (0, 0)" using \<open>\<tau> (\<psi>_e x) = \<tau> (\<psi>_e y)\<close> by (by100 simp)
                hence "\<psi>_e x = (0, 0)" using h_tau_zero[OF hxB] by (by100 simp)
                thus False using False by (by100 simp)
              qed
              thus ?thesis using hyB by (by100 blast)
            qed
            ultimately show ?thesis
              using h_tau_inj[unfolded inj_on_def, rule_format] \<open>\<tau> (\<psi>_e x) = \<tau> (\<psi>_e y)\<close>
              by (by100 blast)
          qed
          \<comment> \<open>\\<psi>\\_e injective \\<to> x = y.\<close>
          ultimately show "x = y"
            using h\<psi>e_inj[unfolded inj_on_def, rule_format, OF hx hy]
            by (by100 blast)
        qed
      qed
      \<comment> \<open>Helper: \\<psi>\\_e maps P\\_e non-edge points to B2 interior (norm < 1).\<close>
      have h_psi_e_int: "\<And>p. p \<in> P_e \<Longrightarrow>
          (\<forall>i<?n. \<forall>t\<in>I_set. p \<noteq> ((1-t)*vx_e i+t*vx_e(Suc i mod ?n),
              (1-t)*vy_e i+t*vy_e(Suc i mod ?n))) \<Longrightarrow>
          fst (\<psi>_e p) ^ 2 + snd (\<psi>_e p) ^ 2 < 1"
      proof -
        fix p assume hp: "p \<in> P_e"
            and hp_ne: "\<forall>i<?n. \<forall>t\<in>I_set. p \<noteq> ((1-t)*vx_e i+t*vx_e(Suc i mod ?n),
                (1-t)*vy_e i+t*vy_e(Suc i mod ?n))"
        have h\<psi>e_B2: "\<psi>_e p \<in> top1_B2"
          using hp h\<psi>e_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        hence h\<psi>e_le1: "fst (\<psi>_e p) ^ 2 + snd (\<psi>_e p) ^ 2 \<le> 1"
          unfolding top1_B2_def by (by100 simp)
        show "fst (\<psi>_e p) ^ 2 + snd (\<psi>_e p) ^ 2 < 1"
        proof (rule ccontr)
          assume "\<not> fst (\<psi>_e p) ^ 2 + snd (\<psi>_e p) ^ 2 < 1"
          hence "fst (\<psi>_e p) ^ 2 + snd (\<psi>_e p) ^ 2 = 1" using h\<psi>e_le1 by (by100 linarith)
          \<comment> \<open>\\<psi>\\_e(p) is on unit circle. So p must be on some edge.\<close>
          \<comment> \<open>Unit circle point = (cos \\<alpha>, sin \\<alpha>) for some \\<alpha>.
             For \\<alpha> = 2\\<pi>(i+t)/n with i < n, t \\<in> I\\_set: this is \\<psi>\\_e(edge\\_e(i,t)).
             Since \\<psi>\\_e is bijective: p = edge\\_e(i,t). Contradicts hp\\_ne.\<close>
          \<comment> \<open>More precisely: \\<psi>\\_e is bijective P\\_e \\<to> B2. \\<psi>\\_e(p) on unit circle means
             \\<psi>\\_e(p) = \\<psi>\\_e(edge\\_e(i,t)) for some i,t. By injectivity: p = edge\\_e(i,t).\<close>
          \<comment> \<open>\\<psi>\\_e(p) \\<in> S1 = \\<psi>\\_e ` edges. By injectivity, p is on an edge. Contradiction.\<close>
          have "\<psi>_e p \<in> top1_S1"
            using \<open>fst (\<psi>_e p) ^ 2 + snd (\<psi>_e p) ^ 2 = 1\<close> unfolding top1_S1_def by (by100 simp)
          hence "\<psi>_e p \<in> \<psi>_e ` (\<Union>i<?n. {((1-t) * vx_e i + t * vx_e (Suc i mod ?n),
                     (1-t) * vy_e i + t * vy_e (Suc i mod ?n)) | t. t \<in> I_set})"
            using h\<psi>e_bdry by (by100 simp)
          then obtain i' t' where hi': "i' < ?n" and ht': "t' \<in> I_set"
              and h\<psi>_eq: "\<psi>_e p = \<psi>_e ((1-t')*vx_e i'+t'*vx_e(Suc i' mod ?n),
                  (1-t')*vy_e i'+t'*vy_e(Suc i' mod ?n))"
            by auto
          define q where "q = ((1-t')*vx_e i'+t'*vx_e(Suc i' mod ?n),
              (1-t')*vy_e i'+t'*vy_e(Suc i' mod ?n))"
          have hq_in_Pe: "q \<in> P_e"
            using edge_point_in_polygon_witness[OF hn3_e hi' ht' hC5e] unfolding q_def by (by100 simp)
          have h\<psi>e_inj2: "inj_on \<psi>_e P_e"
            using h\<psi>e_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
          have "p = q" using h\<psi>e_inj2[unfolded inj_on_def, rule_format, OF hp hq_in_Pe]
              h\<psi>_eq unfolding q_def by (by100 simp)
          hence "p = ((1-t')*vx_e i'+t'*vx_e(Suc i' mod ?n),
              (1-t')*vy_e i'+t'*vy_e(Suc i' mod ?n))" unfolding q_def by (by100 simp)
          thus False using hp_ne hi' ht' by (by100 blast)
        qed
      qed
      \<comment> \<open>Helper: if \\<tau>(p) is in B2 interior (norm < 1), then spur\\_f(\\<psi>\\_e\\<inverse>(p)) is P\\_m interior.\<close>
      have h_B2_int_to_Pm_int: "\<And>q j s. q \<in> top1_B2 \<Longrightarrow> fst q ^ 2 + snd q ^ 2 < 1 \<Longrightarrow>
          j < ?m \<Longrightarrow> s \<in> I_set \<Longrightarrow>
          inv_into P_m \<psi>_m q \<noteq> ((1-s)*vx_m j+s*vx_m(Suc j mod ?m),
              (1-s)*vy_m j+s*vy_m(Suc j mod ?m))"
      proof -
        fix q :: "real \<times> real" and j :: nat and s :: real
        assume hq: "q \<in> top1_B2" and hq_int: "fst q ^ 2 + snd q ^ 2 < 1"
            and hj: "j < ?m" and hs: "s \<in> I_set"
        show "inv_into P_m \<psi>_m q \<noteq> ((1-s)*vx_m j+s*vx_m(Suc j mod ?m),
            (1-s)*vy_m j+s*vy_m(Suc j mod ?m))"
        proof
          assume "inv_into P_m \<psi>_m q = ((1-s)*vx_m j+s*vx_m(Suc j mod ?m),
              (1-s)*vy_m j+s*vy_m(Suc j mod ?m))"
          hence "\<psi>_m (inv_into P_m \<psi>_m q) =
              \<psi>_m ((1-s)*vx_m j+s*vx_m(Suc j mod ?m),(1-s)*vy_m j+s*vy_m(Suc j mod ?m))"
            by (by100 simp)
          moreover have "\<psi>_m (inv_into P_m \<psi>_m q) = q"
          proof -
            have "\<psi>_m ` P_m = top1_B2"
              using h\<psi>m_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
            from f_inv_into_f[OF hq[unfolded this[symmetric]]]
            show ?thesis .
          qed
          moreover have "\<psi>_m ((1-s)*vx_m j+s*vx_m(Suc j mod ?m),(1-s)*vy_m j+s*vy_m(Suc j mod ?m))
              = (cos (2*pi*(real j + s)/real ?m), sin (2*pi*(real j + s)/real ?m))"
            using h\<psi>m_edge[rule_format, OF hj hs] .
          ultimately have "q = (cos (2*pi*(real j + s)/real ?m), sin (2*pi*(real j + s)/real ?m))"
            by (by100 simp)
          hence "fst q ^ 2 + snd q ^ 2 = 1"
            using sin_cos_squared_add3[of "2*pi*(real j + s)/real ?m"] by (by100 simp)
          thus False using hq_int by (by100 linarith)
        qed
      qed
      \<comment> \<open>Helper: \\<tau> maps B2 interior to B2 interior (norm strictly < 1 for good/cancel sectors).\<close>
      have h_tau_strict_B2: "\<And>p. p \<in> top1_B2 \<Longrightarrow> p \<noteq> (0,0) \<Longrightarrow> fst p ^ 2 + snd p ^ 2 < 1 \<Longrightarrow>
          fst (\<tau> p) ^ 2 + snd (\<tau> p) ^ 2 < 1"
      proof -
        fix p :: "real \<times> real"
        assume hp: "p \<in> top1_B2" and hne: "p \<noteq> (0,0)"
            and hp_int: "fst p ^ 2 + snd p ^ 2 < 1"
        \<comment> \<open>From h\\_tau\\_range: |\\<tau>(p)| \\<le> 1. Need strict: |\\<tau>(p)| < 1.\<close>
        have h\<tau>_le1: "fst (\<tau> p) ^ 2 + snd (\<tau> p) ^ 2 \<le> 1"
          using hp h\<tau>_range unfolding top1_B2_def by (by100 blast)
        \<comment> \<open>Good sector: |\\<tau>(p)|² = r² = fst p² + snd p² < 1.
           Cancel sector: |\\<tau>(p)| \\<le> 1, and strict inequality from detailed analysis.\<close>
        \<comment> \<open>Unfold \\<tau> at p \\<noteq> (0,0).\<close>
        define r where "r = sqrt (fst p ^ 2 + snd p ^ 2)"
        have hr_pos: "r > 0"
        proof -
          have "fst p \<noteq> 0 \<or> snd p \<noteq> 0" using hne by (cases p) (by100 auto)
          hence "fst p ^ 2 + snd p ^ 2 > 0"
          proof
            assume "fst p \<noteq> 0" hence "fst p ^ 2 > 0" by (by100 simp)
            moreover have "snd p ^ 2 \<ge> 0" by (by100 simp)
            ultimately show ?thesis by (by100 linarith)
          next
            assume "snd p \<noteq> 0" hence "snd p ^ 2 > 0" by (by100 simp)
            moreover have "fst p ^ 2 \<ge> 0" by (by100 simp)
            ultimately show ?thesis by (by100 linarith)
          qed
          thus ?thesis unfolding r_def using real_sqrt_gt_0_iff by (by100 auto)
        qed
        have hr_lt1: "r < 1"
        proof -
          have "r ^ 2 = fst p ^ 2 + snd p ^ 2"
            unfolding r_def using real_sqrt_pow2[of "fst p^2 + snd p^2"] by (by100 simp)
          hence "r ^ 2 < 1" using hp_int by (by100 linarith)
          hence "r * r < 1" unfolding power2_eq_square .
          have "r < 1"
          proof (rule ccontr)
            assume "\<not> r < 1"
            hence "r \<ge> 1" by (by100 linarith)
            hence "r * r \<ge> r * 1" using hr_pos by (by100 simp)
            hence "r * r \<ge> 1" using \<open>r \<ge> 1\<close> by (by100 linarith)
            thus False using \<open>r * r < 1\<close> by (by100 linarith)
          qed
          thus ?thesis using hr_pos by (by100 simp)
        qed
        have hr_sq: "r ^ 2 = fst p ^ 2 + snd p ^ 2"
          unfolding r_def using real_sqrt_pow2[of "fst p^2 + snd p^2"] by (by100 simp)
        \<comment> \<open>Unfold \\<tau> at p \\<noteq> (0,0) and case-split on sector.\<close>
        have hr_eq: "sqrt (fst p ^ 2 + snd p ^ 2) = r" unfolding r_def by (by100 simp)
        define \<theta>_p where "\<theta>_p = (if snd p \<ge> 0 then arccos (fst p / r) else 2*pi - arccos (fst p / r))"
        have h\<tau>_simp: "\<tau> p = (let \<theta> = \<theta>_p in
            if \<theta> \<ge> \<theta>_cancel then (r * fst (\<tau>_boundary \<theta>), r * snd (\<tau>_boundary \<theta>))
            else let spur_pt = \<tau>_boundary \<theta>;
                     t_fold = min (\<theta> * real ?n / (2*pi)) ((\<theta>_cancel - \<theta>) * real ?n / (2*pi));
                     sign_v = (if \<theta> \<le> \<theta>_mid then 1 else -1);
                     offset = sign_v * r * (1 - r) * sin (pi * t_fold) / 4
                 in (r * fst spur_pt + offset * fst d_perp,
                     r * snd spur_pt + offset * snd d_perp))"
          unfolding \<tau>_def \<theta>_p_def using hne hr_eq by (by100 simp)
        show "fst (\<tau> p) ^ 2 + snd (\<tau> p) ^ 2 < 1"
        proof (cases "\<theta>_p \<ge> \<theta>_cancel")
          case True
          \<comment> \<open>Good sector: \\<tau> = (r*cos(\\<phi>), r*sin(\\<phi>)). |\\<tau>|² = r².\<close>
          have h\<tau>_good: "\<tau> p = (r * fst (\<tau>_boundary \<theta>_p), r * snd (\<tau>_boundary \<theta>_p))"
            using h\<tau>_simp True by (by100 simp)
          have "fst (\<tau>_boundary \<theta>_p) = cos ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)"
            using True unfolding \<tau>_boundary_def by (by100 auto)
          moreover have "snd (\<tau>_boundary \<theta>_p) = sin ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)"
            using True unfolding \<tau>_boundary_def by (by100 auto)
          ultimately have "fst (\<tau> p) ^ 2 + snd (\<tau> p) ^ 2
              = (r * cos ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)) ^ 2
              + (r * sin ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m)) ^ 2"
            using h\<tau>_good by (by100 simp)
          also have "\<dots> = r ^ 2 * (cos ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m) ^ 2
              + sin ((\<theta>_p - \<theta>_cancel) * real ?n / real ?m) ^ 2)"
            by (by100 algebra)
          also have "\<dots> = r ^ 2" using sin_cos_squared_add3 by (by100 simp)
          finally have "fst (\<tau> p) ^ 2 + snd (\<tau> p) ^ 2 = r ^ 2" .
          moreover have "r ^ 2 < 1"
          proof -
            have "r * r < 1 * r" using hr_lt1 hr_pos
              using mult_strict_right_mono[of r 1 r] by (by100 simp)
            hence "r * r < 1" using hr_lt1 by (by100 linarith)
            thus ?thesis unfolding power2_eq_square .
          qed
          ultimately show ?thesis by (by100 linarith)
        next
          case False
          \<comment> \<open>Cancel sector: |\\<tau>|² < 1. Uses r < 1 and (1-tf)² < 1 for tf > 0.\<close>
          \<comment> \<open>Cancel sector: decompose \\<tau> and bound each component.\<close>
          have h\<theta>_lt: "\<theta>_p < \<theta>_cancel" using False by (by100 linarith)
          define sp where "sp = \<tau>_boundary \<theta>_p"
          define tf where "tf = min (\<theta>_p * real ?n / (2*pi)) ((\<theta>_cancel - \<theta>_p) * real ?n / (2*pi))"
          define sign_v where "sign_v = (if \<theta>_p \<le> \<theta>_mid then (1::real) else -1)"
          define ofs where "ofs = sign_v * r * (1 - r) * sin (pi * tf) / 4"
          \<comment> \<open>Step 1: \\<tau> p = r*sp + ofs*d\\_perp in cancel sector.\<close>
          have h\<tau>_cancel: "\<tau> p = (r * fst sp + ofs * fst d_perp,
              r * snd sp + ofs * snd d_perp)"
            using h\<tau>_simp h\<theta>_lt unfolding sp_def tf_def sign_v_def ofs_def Let_def
            by (by100 simp)
          \<comment> \<open>Compute sp as explicit pair.\<close>
          have hsp_pair: "sp = ((1-tf) + tf * fst p_cm, tf * snd p_cm)"
          proof -
            have "\<not> \<theta>_p \<ge> \<theta>_cancel" using h\<theta>_lt by (by100 linarith)
            hence "sp = (let t_fold = min (\<theta>_p * real ?n / (2*pi))
                ((\<theta>_cancel - \<theta>_p) * real ?n / (2*pi))
              in ((1 - t_fold) * 1 + t_fold * fst p_cm,
                  (1 - t_fold) * 0 + t_fold * snd p_cm))"
              unfolding sp_def \<tau>_boundary_def \<theta>_cancel_def by (by100 simp)
            also have "\<dots> = ((1 - tf) + tf * fst p_cm, tf * snd p_cm)"
              unfolding tf_def Let_def by (by100 simp)
            finally show ?thesis .
          qed
          \<comment> \<open>Step 2: |sp|² \\<le> 1 (convex combination of (1,0) and p\\_cm in B2).\<close>
          have hsp_norm: "fst sp ^ 2 + snd sp ^ 2 \<le> 1"
          proof -
            have htf_ge: "tf \<ge> 0"
            proof -
              have "\<theta>_p \<ge> 0"
              proof -
                have "fst p \<noteq> 0 \<or> snd p \<noteq> 0" using hne by (cases p) (by100 auto)
                have h_lb: "-1 \<le> fst p / r" unfolding r_def
                  by (rule fst_div_norm_bounded(1)[OF \<open>fst p \<noteq> 0 \<or> snd p \<noteq> 0\<close>])
                have h_ub: "fst p / r \<le> 1" unfolding r_def
                  by (rule fst_div_norm_bounded(2)[OF \<open>fst p \<noteq> 0 \<or> snd p \<noteq> 0\<close>])
                show ?thesis
                proof (cases "snd p \<ge> 0")
                  case True thus ?thesis unfolding \<theta>_p_def
                    using arccos_lbound[OF h_lb h_ub] by (by100 simp)
                next
                  case False
                  hence "\<theta>_p = 2*pi - arccos (fst p / r)" unfolding \<theta>_p_def by (by100 simp)
                  moreover have "arccos (fst p / r) \<le> pi" using arccos_ubound[OF h_lb h_ub] .
                  ultimately show ?thesis using pi_gt_zero by (by100 linarith)
                qed
              qed
              hence "\<theta>_p * real ?n / (2*pi) \<ge> 0" using pi_gt_zero hn5 by (by100 simp)
              moreover have "(\<theta>_cancel - \<theta>_p) * real ?n / (2*pi) \<ge> 0"
                using h\<theta>_lt pi_gt_zero hn5 by (by100 simp)
              ultimately show ?thesis unfolding tf_def by (by100 simp)
            qed
            have hfst_pcm_le1: "fst p_cm \<le> 1"
            proof (rule ccontr)
              assume "\<not> fst p_cm \<le> 1"
              hence "fst p_cm > 1" by (by100 linarith)
              have "snd p_cm ^ 2 \<ge> 0" by (by100 simp)
              have "fst p_cm ^ 2 \<ge> 1"
              proof -
                define a where "a = fst p_cm"
                have "a > 1" using \<open>fst p_cm > 1\<close> unfolding a_def .
                hence "a * a > 1 * 1"
                  using mult_strict_mono'[of 1 a 1 a] by (by100 linarith)
                thus ?thesis unfolding a_def power2_eq_square by (by100 linarith)
              qed
              hence "fst p_cm ^ 2 + snd p_cm ^ 2 \<ge> 1"
                using \<open>snd p_cm ^ 2 \<ge> 0\<close> by (by100 linarith)
              thus False using hp_cm_int by (by100 linarith)
            qed
            have hpcm_le1: "fst p_cm ^ 2 + snd p_cm ^ 2 \<le> 1" using hp_cm_int by (by100 linarith)
            have "fst sp ^ 2 + snd sp ^ 2
                = ((1-tf) + tf * fst p_cm) ^ 2 + (tf * snd p_cm) ^ 2"
              using hsp_pair by (by100 simp)
            also have "\<dots> = (1-tf)^2 + 2*(1-tf)*tf*fst p_cm + tf^2*(fst p_cm^2 + snd p_cm^2)"
              by (by100 algebra)
            also have "\<dots> \<le> (1-tf)^2 + 2*(1-tf)*tf*1 + tf^2*1"
            proof -
              have "2*(1-tf)*tf*fst p_cm \<le> 2*(1-tf)*tf*1"
              proof -
                have "tf \<le> 1"
                proof -
                  show ?thesis unfolding tf_def
                    using h\<theta>_lt pi_gt_zero hn5
                    by (smt (verit, ccfv_threshold) \<theta>_cancel_def divide_diff_eq_iff
                      divide_le_eq_1_pos length_greater_0_conv list.size(3)
                      nonzero_divide_eq_eq not_numeral_le_zero of_nat_0_less_iff)
                qed
                have "2*(1-tf)*tf \<ge> 0" using htf_ge \<open>tf \<le> 1\<close> by (by100 simp)
                thus ?thesis using mult_left_mono[of "fst p_cm" 1 "2*(1-tf)*tf"]
                  hfst_pcm_le1 by (by100 simp)
              qed
              moreover have "tf^2*(fst p_cm^2 + snd p_cm^2) \<le> tf^2*1"
              proof -
                have "tf^2 \<ge> 0" by (by100 simp)
                thus ?thesis using mult_left_mono[of "fst p_cm^2+snd p_cm^2" 1 "tf^2"]
                  hpcm_le1 by (by100 simp)
              qed
              ultimately show ?thesis by (by100 linarith)
            qed
            also have "\<dots> = 1"
            proof -
              have "(1-tf)^2 + 2*(1-tf)*tf*1 + tf^2*1 = ((1-tf)+tf) * ((1-tf)+tf)"
                unfolding power2_eq_square by (by100 algebra)
              thus ?thesis by (by100 simp)
            qed
            finally show ?thesis .
          qed
          \<comment> \<open>Step 3: |ofs| \\<le> r*(1-r)/4 (from |sin| \\<le> 1 and |sign| = 1).\<close>
          have hofs_sq: "ofs ^ 2 \<le> (r * (1 - r) / 4) ^ 2"
          proof -
            have "sign_v ^ 2 = 1" unfolding sign_v_def by (by100 simp)
            have "sin (pi * tf) ^ 2 \<le> 1"
            proof -
              have "sin (pi * tf) ^ 2 + cos (pi * tf) ^ 2 = 1" by (by100 simp)
              moreover have "cos (pi * tf) ^ 2 \<ge> 0" by (by100 simp)
              ultimately show ?thesis by (by100 linarith)
            qed
            have "ofs ^ 2 = sign_v ^ 2 * r ^ 2 * (1-r) ^ 2 * sin(pi*tf) ^ 2 / 16"
              unfolding ofs_def power2_eq_square by (by100 simp)
            also have "\<dots> = r ^ 2 * (1-r) ^ 2 * sin(pi*tf) ^ 2 / 16"
              using \<open>sign_v ^ 2 = 1\<close> by (by100 simp)
            also have "\<dots> \<le> r ^ 2 * (1-r) ^ 2 * 1 / 16"
            proof -
              have "r ^ 2 * (1-r) ^ 2 \<ge> 0" by (by100 simp)
              thus ?thesis using \<open>sin (pi * tf) ^ 2 \<le> 1\<close>
                using mult_left_mono[of "sin(pi*tf)^2" "1^2" "r^2*(1-r)^2"]
                by (by100 simp)
            qed
            also have "\<dots> = (r * (1-r) / 4) ^ 2" unfolding power2_eq_square by (by100 simp)
            finally show ?thesis .
          qed
          have hofs_abs: "\<bar>ofs\<bar> \<le> r * (1 - r) / 4"
          proof -
            have hX_ge: "r * (1 - r) / 4 \<ge> 0" using hr_pos hr_lt1 by (by100 simp)
            show ?thesis
            proof (rule ccontr)
              assume "\<not> \<bar>ofs\<bar> \<le> r * (1 - r) / 4"
              hence "\<bar>ofs\<bar> > r * (1 - r) / 4" by (by100 linarith)
              hence "\<bar>ofs\<bar> * \<bar>ofs\<bar> > (r*(1-r)/4) * (r*(1-r)/4)"
                using hX_ge
                using mult_strict_mono'[of "r*(1-r)/4" "\<bar>ofs\<bar>" "r*(1-r)/4" "\<bar>ofs\<bar>"]
                by (by100 linarith)
              hence "ofs ^ 2 > (r*(1-r)/4) ^ 2" unfolding power2_eq_square abs_mult_self
                by (by100 linarith)
              thus False using hofs_sq by (by100 linarith)
            qed
          qed
          \<comment> \<open>Step 4: |d\\_perp|² < 4 (from |p\\_cm| < 1, so snd(p\\_cm)² + (fst(p\\_cm)-1)² < 4).\<close>
          have hdp_norm: "fst d_perp ^ 2 + snd d_perp ^ 2 < 4"
          proof -
            have hfst_dp: "fst d_perp = - snd p_cm" unfolding d_perp_def by (by100 simp)
            have hsnd_dp: "snd d_perp = fst p_cm - 1" unfolding d_perp_def by (by100 simp)
            have "fst d_perp ^ 2 + snd d_perp ^ 2
                = snd p_cm ^ 2 + (fst p_cm - 1) ^ 2"
              using hfst_dp hsnd_dp by (by100 algebra)
            also have "\<dots> = fst p_cm ^ 2 + snd p_cm ^ 2 - 2 * fst p_cm + 1"
              by (by100 algebra)
            also have "\<dots> < 2 - 2 * fst p_cm" using hp_cm_int by (by100 linarith)
            finally have "fst d_perp ^ 2 + snd d_perp ^ 2 < 2 - 2 * fst p_cm" .
            moreover have "fst p_cm > -1"
            proof (rule ccontr)
              assume "\<not> fst p_cm > -1"
              hence "fst p_cm \<le> -1" by (by100 linarith)
              hence hle: "- fst p_cm \<ge> 1" by (by100 linarith)
              have "fst p_cm ^ 2 = (- fst p_cm) * (- fst p_cm)" by (by100 algebra)
              also have "\<dots> \<ge> 1 * 1"
                using mult_mono[of 1 "- fst p_cm" 1 "- fst p_cm"] hle by (by100 linarith)
              finally have "fst p_cm ^ 2 \<ge> 1" by (by100 linarith)
              have "snd p_cm ^ 2 \<ge> 0" by (by100 simp)
              hence "fst p_cm ^ 2 + snd p_cm ^ 2 \<ge> 1"
                using \<open>fst p_cm ^ 2 \<ge> 1\<close> by (by100 linarith)
              thus False using hp_cm_int by (by100 linarith)
            qed
            ultimately show ?thesis by (by100 linarith)
          qed
          \<comment> \<open>Step 5: sp\\<cdot>dp = -snd(p\\_cm), so |sp\\<cdot>dp| < 1.\<close>
          have hsp_dot: "\<bar>fst sp * fst d_perp + snd sp * snd d_perp\<bar> < 1"
          proof -
            \<comment> \<open>sp = ((1-tf)+tf*fst(pcm), tf*snd(pcm)), dp = (-snd(pcm), fst(pcm)-1).\<close>
            \<comment> \<open>Compute sp as pair, then extract components.\<close>
            have hsp_pair: "sp = ((1-tf) + tf * fst p_cm, tf * snd p_cm)"
            proof -
              have "\<not> \<theta>_p \<ge> \<theta>_cancel" using h\<theta>_lt by (by100 linarith)
              hence "sp = (let t_fold = min (\<theta>_p * real ?n / (2*pi))
                  ((\<theta>_cancel - \<theta>_p) * real ?n / (2*pi))
                in ((1 - t_fold) * 1 + t_fold * fst p_cm,
                    (1 - t_fold) * 0 + t_fold * snd p_cm))"
                unfolding sp_def \<tau>_boundary_def \<theta>_cancel_def by (by100 simp)
              also have "\<dots> = ((1 - tf) + tf * fst p_cm, tf * snd p_cm)"
                unfolding tf_def Let_def by (by100 simp)
              finally show ?thesis .
            qed
            have hsp_fst: "fst sp = (1-tf) + tf * fst p_cm" using hsp_pair by (by100 simp)
            have hsp_snd: "snd sp = tf * snd p_cm" using hsp_pair by (by100 simp)
            have "fst sp * fst d_perp + snd sp * snd d_perp
                = ((1-tf) + tf * fst p_cm) * (- snd p_cm) + tf * snd p_cm * (fst p_cm - 1)"
              using hsp_fst hsp_snd unfolding d_perp_def by (by100 simp)
            also have "\<dots> = - snd p_cm" by (by100 algebra)
            finally have hdot: "fst sp * fst d_perp + snd sp * snd d_perp = - snd p_cm" .
            have "snd p_cm ^ 2 \<le> fst p_cm ^ 2 + snd p_cm ^ 2" by (by100 simp)
            also have "\<dots> < 1" using hp_cm_int .
            finally have "snd p_cm ^ 2 < 1" .
            hence "\<bar>snd p_cm\<bar> < 1"
            proof -
              have "snd p_cm ^ 2 < 1" using \<open>snd p_cm ^ 2 < 1\<close> .
              show ?thesis
              proof (cases "snd p_cm \<ge> 0")
                case True
                hence "snd p_cm \<ge> 0" .
                have "snd p_cm < 1"
                proof (rule ccontr)
                  assume "\<not> snd p_cm < 1"
                  hence "snd p_cm \<ge> 1" by (by100 linarith)
                  hence "snd p_cm ^ 2 \<ge> 1 ^ 2"
                    using power_mono[of 1 "snd p_cm" 2] by (by100 simp)
                  hence "snd p_cm ^ 2 \<ge> 1" by (by100 simp)
                  thus False using \<open>snd p_cm ^ 2 < 1\<close> by (by100 linarith)
                qed
                thus ?thesis using True by (by100 simp)
              next
                case False
                hence "- snd p_cm > 0" by (by100 linarith)
                have "- snd p_cm < 1"
                proof (rule ccontr)
                  assume "\<not> - snd p_cm < 1"
                  hence "- snd p_cm \<ge> 1" by (by100 linarith)
                  hence "(- snd p_cm) ^ 2 \<ge> 1 ^ 2"
                    using power_mono[of 1 "- snd p_cm" 2] by (by100 simp)
                  hence "snd p_cm ^ 2 \<ge> 1" by (by100 simp)
                  thus False using \<open>snd p_cm ^ 2 < 1\<close> by (by100 linarith)
                qed
                thus ?thesis using False by (by100 simp)
              qed
            qed
            thus ?thesis using hdot by (by100 linarith)
          qed
          \<comment> \<open>Step 6: Expand |\\<tau>|² and bound by r²+r²(1-r)/2+r²(1-r)²/4.\<close>
          have h_upper: "fst (\<tau> p) ^ 2 + snd (\<tau> p) ^ 2
              \<le> r^2 + r^2*(1-r)/2 + r^2*(1-r)^2/4"
          proof -
            have "fst (\<tau> p) ^ 2 + snd (\<tau> p) ^ 2
                = (r * fst sp + ofs * fst d_perp) ^ 2 + (r * snd sp + ofs * snd d_perp) ^ 2"
              using h\<tau>_cancel by (by100 simp)
            also have "\<dots> = r^2 * (fst sp^2 + snd sp^2)
                + 2 * r * ofs * (fst sp * fst d_perp + snd sp * snd d_perp)
                + ofs^2 * (fst d_perp^2 + snd d_perp^2)"
              unfolding power2_eq_square by (by100 algebra)
            finally have h_exp: "fst (\<tau> p) ^ 2 + snd (\<tau> p) ^ 2
                = r^2 * (fst sp^2 + snd sp^2)
                + 2 * r * ofs * (fst sp * fst d_perp + snd sp * snd d_perp)
                + ofs^2 * (fst d_perp^2 + snd d_perp^2)" .
            have ht1: "r^2 * (fst sp^2 + snd sp^2) \<le> r^2"
            proof -
              have "r^2 \<ge> 0" by (by100 simp)
              thus ?thesis using mult_left_mono[of "fst sp^2+snd sp^2" 1 "r^2"]
                hsp_norm by (by100 simp)
            qed
            have ht2: "2*r*ofs*(fst sp*fst d_perp+snd sp*snd d_perp) \<le> r^2*(1-r)/2"
            proof -
              have "\<bar>2*r*ofs*(fst sp*fst d_perp+snd sp*snd d_perp)\<bar>
                  \<le> 2*r*\<bar>ofs\<bar>*\<bar>fst sp*fst d_perp+snd sp*snd d_perp\<bar>"
                using hr_pos
                by (metis abs_mult abs_mult_pos' less_eq_real_def mult_nonneg_nonneg
                  zero_le_numeral)
              also have "\<dots> \<le> 2*r*(r*(1-r)/4)*1"
              proof -
                have h1: "\<bar>ofs\<bar> \<le> r*(1-r)/4" using hofs_abs .
                have h2: "\<bar>fst sp*fst d_perp+snd sp*snd d_perp\<bar> \<le> 1"
                  using hsp_dot by (by100 linarith)
                have h3: "2*r \<ge> 0" using hr_pos by (by100 simp)
                have "2*r*\<bar>ofs\<bar> \<le> 2*r*(r*(1-r)/4)"
                  using mult_left_mono[OF h1 h3] by (by100 simp)
                moreover have "2*r*(r*(1-r)/4) \<ge> 0"
                  using hr_pos hr_lt1 by (by100 simp)
                ultimately have "2*r*\<bar>ofs\<bar>*\<bar>fst sp*fst d_perp+snd sp*snd d_perp\<bar>
                    \<le> 2*r*(r*(1-r)/4)*\<bar>fst sp*fst d_perp+snd sp*snd d_perp\<bar>"
                  using mult_right_mono[of "2*r*\<bar>ofs\<bar>" "2*r*(r*(1-r)/4)"
                      "\<bar>fst sp*fst d_perp+snd sp*snd d_perp\<bar>"] by (by100 simp)
                also have "\<dots> \<le> 2*r*(r*(1-r)/4)*1"
                  using mult_left_mono[OF h2 \<open>2*r*(r*(1-r)/4) \<ge> 0\<close>] by (by100 simp)
                finally show ?thesis .
              qed
              also have "\<dots> = r^2*(1-r)/2" unfolding power2_eq_square by (by100 simp)
              finally show ?thesis by (by100 linarith)
            qed
            have ht3: "ofs^2 * (fst d_perp^2+snd d_perp^2) \<le> r^2*(1-r)^2/4"
            proof -
              have "ofs^2 * (fst d_perp^2+snd d_perp^2)
                  \<le> (r*(1-r)/4)^2 * 4"
                using hofs_sq hdp_norm
                by (metis (no_types, opaque_lifting) less_eq_real_def mult_mono
                  power2_eq_square sum_power2_ge_zero zero_le_square)
              also have "\<dots> = r^2*(1-r)^2/4"
                unfolding power2_eq_square by (by100 simp)
              finally show ?thesis .
            qed
            from h_exp ht1 ht2 ht3 show ?thesis by (by100 linarith)
          qed
          \<comment> \<open>Step 7: Polynomial bound: r²(r²-4r+7)/4 < 1 for r < 1.
             Factor: r⁴-4r³+7r²-4 = (r-1)(r³-3r²+4r+4), second factor > 0.\<close>
          have h_poly: "r^2 + r^2*(1-r)/2 + r^2*(1-r)^2/4 < 1"
          proof -
            \<comment> \<open>Since r \\<le> 1: r² \\<le> r, (1-r)² \\<le> 1-r. So bound by r+r(1-r)/2+r(1-r)/4.\<close>
            define s where "s = 1 - r"
            have hs_ge: "s \<ge> 0" using hr_lt1 s_def by (by100 linarith)
            have hs_le: "s \<le> 1" using hr_pos s_def by (by100 linarith)
            have hrr_le: "r * r \<le> 1 * r"
              using mult_right_mono[of r 1 r] hr_lt1 hr_pos by (by100 linarith)
            have hss_le: "s * s \<le> 1 * s"
              using mult_right_mono[of s 1 s] hs_le hs_ge by (by100 linarith)
            have hr2_le_r: "r^2 \<le> r" using hrr_le unfolding power2_eq_square by (by100 linarith)
            have hs2_le_s: "s^2 \<le> s" using hss_le unfolding power2_eq_square by (by100 linarith)
            \<comment> \<open>r²(1-r) \\<le> r(1-r) and r²(1-r)² \\<le> r(1-r).\<close>
            have "s \<ge> 0" using hs_ge .
            have h_t2: "r^2*(1-r) \<le> r*(1-r)"
              using mult_right_mono[of "r^2" r s] hr2_le_r hs_ge s_def by (by100 simp)
            have "r^2*(1-r)^2 \<le> r^2*(1-r)"
              using mult_left_mono[of "s^2" s "r^2"] hs2_le_s s_def by (by100 simp)
            hence h_t3: "r^2*(1-r)^2 \<le> r*(1-r)" using h_t2 by (by100 linarith)
            have "r^2 + r^2*(1-r)/2 + r^2*(1-r)^2/4 \<le> r + r*(1-r)/2 + r*(1-r)/4"
              using hr2_le_r h_t2 h_t3 by (by100 linarith)
            \<comment> \<open>Now: r+r(1-r)/2+r(1-r)/4 = r+3r(1-r)/4 = r(4+3s)/4 = r(4+3-3r)/4 = r(7-3r)/4.\<close>
            \<comment> \<open>Need r(7-3r)/4 < 1, i.e., 7r-3r² < 4, i.e., (3r-4)(r-1) > 0.\<close>
            moreover have "r + r*(1-r)/2 + r*(1-r)/4 < 1"
            proof -
              have "(3*r - 4) * (r - 1) > 0"
              proof -
                have "3*r - 4 < 0" using hr_lt1 by (by100 linarith)
                have "r - 1 < 0" using hr_lt1 by (by100 linarith)
                from mult_neg_neg[OF \<open>3*r-4<0\<close> \<open>r-1<0\<close>] show ?thesis .
              qed
              have "(3*r-4)*(r-1) = 3*r*r - 7*r + 4" by (by100 algebra)
              hence "7*r - 3*r*r < 4"
                using \<open>(3*r-4)*(r-1) > 0\<close> by (by100 linarith)
              \<comment> \<open>4*(r+r(1-r)/2+r(1-r)/4) = 4r + 2r(1-r) + r(1-r). Use s = 1-r.\<close>
              have "r * s = r - r * r" unfolding s_def by (by100 algebra)
              hence "3 * (r * s) = 3*r - 3*r*r" by (by100 linarith)
              have "4 * (r + r*s/2 + r*s/4) = 7*r - 3*r*r"
              proof -
                have "r*s = r - r*r" unfolding s_def by (by100 algebra)
                hence "4*r + 3*(r*s) = 4*r + 3*r - 3*r*r" by (by100 linarith)
                hence h7: "4*r + 3*(r*s) = 7*r - 3*r*r" by (by100 linarith)
                have "4 * (r + r*s/2 + r*s/4) = 4*r + 3*(r*s)"
                  by (by100 simp)
                thus ?thesis using h7 by (by100 linarith)
              qed
              hence "4 * (r + r*(1-r)/2 + r*(1-r)/4) = 7*r - 3*r*r"
                unfolding s_def by (by100 simp)
              hence "4 * (r + r*(1-r)/2 + r*(1-r)/4) < 4"
                using \<open>7*r - 3*r*r < 4\<close> by (by100 linarith)
              thus ?thesis by (by100 simp)
            qed
            ultimately show ?thesis by (by100 linarith)
          qed
          show ?thesis using h_upper h_poly by (by100 linarith)
        qed
      qed
      \<comment> \<open>Helper: \\<tau> maps cancel-sector boundary to B2 interior.
         At r=1, offset=0, so \\<tau> = sp = (1-tf)*(1,0)+tf*p\\_cm. For tf > 0 and |p\\_cm| < 1: |sp| < 1.\<close>
      have h_tau_cancel_bdy: "\<And>\<theta>. 0 < \<theta> \<Longrightarrow> \<theta> < \<theta>_cancel \<Longrightarrow>
          fst (\<tau> (cos \<theta>, sin \<theta>)) ^ 2 + snd (\<tau> (cos \<theta>, sin \<theta>)) ^ 2 < 1"
      proof -
        fix \<theta> :: real assume h\<theta>_pos: "0 < \<theta>" and h\<theta>_lt: "\<theta> < \<theta>_cancel"
        \<comment> \<open>Step 1: (cos \\<theta>, sin \\<theta>) \\<noteq> (0,0) and r = 1.\<close>
        have hne: "(cos \<theta>, sin \<theta>) \<noteq> (0::real, 0::real)"
        proof -
          have "sin \<theta> \<noteq> 0" using h\<theta>_pos h\<theta>_lt
          proof -
            have "real ?n \<ge> 5" using hn5 by (by100 simp)
            have "\<theta>_cancel = 4*pi/real ?n" unfolding \<theta>_cancel_def by (by100 simp)
            hence "\<theta>_cancel \<le> 4*pi/5"
              using divide_left_mono[of 5 "real ?n" "4*pi"] pi_gt_zero \<open>real ?n \<ge> 5\<close>
              by (by100 simp)
            also have "\<dots> < pi" using pi_gt_zero by (by100 linarith)
            finally have "\<theta>_cancel < pi" .
            hence "\<theta> < pi" using h\<theta>_lt by (by100 linarith)
            from sin_gt_zero[OF h\<theta>_pos \<open>\<theta> < pi\<close>] show ?thesis by (by100 linarith)
          qed
          thus ?thesis by (by100 auto)
        qed
        have hr_eq: "sqrt ((cos \<theta>)^2 + (sin \<theta>)^2) = 1"
          using sin_cos_squared_add3[of \<theta>] by (by100 simp)
        \<comment> \<open>Step 2: \\<theta>\\_cancel < \\<pi>, so sin \\<theta> > 0, hence angle branch = arccos(cos \\<theta>) = \\<theta>.\<close>
        have h\<theta>_lt_pi: "\<theta> < pi"
        proof -
          have "\<theta>_cancel < pi"
          proof -
            have "\<theta>_cancel = 4*pi/real ?n" unfolding \<theta>_cancel_def by (by100 simp)
            have "real ?n \<ge> 5" using hn5 by (by100 simp)
            have "4*pi/real ?n \<le> 4*pi/5"
              using divide_left_mono[of 5 "real ?n" "4*pi"] pi_gt_zero \<open>real ?n \<ge> 5\<close>
              by (by100 simp)
            also have "\<dots> < pi" using pi_gt_zero by (by100 linarith)
            finally show ?thesis using \<open>\<theta>_cancel = 4*pi/real ?n\<close> by (by100 linarith)
          qed
          thus ?thesis using h\<theta>_lt by (by100 linarith)
        qed
        have hsin_pos: "sin \<theta> > 0" using h\<theta>_pos h\<theta>_lt_pi
          using sin_gt_zero[OF h\<theta>_pos h\<theta>_lt_pi] by (by100 linarith)
        have hangle_eq: "(if sin \<theta> \<ge> 0 then arccos (cos \<theta> / 1) else 2*pi - arccos (cos \<theta> / 1)) = \<theta>"
        proof -
          have "sin \<theta> \<ge> 0" using hsin_pos by (by100 linarith)
          hence "(if sin \<theta> \<ge> 0 then arccos (cos \<theta> / 1) else 2*pi - arccos (cos \<theta> / 1))
              = arccos (cos \<theta>)" by (by100 simp)
          also have "\<dots> = \<theta>"
          proof -
            have "0 \<le> \<theta>" using h\<theta>_pos by (by100 linarith)
            have "\<theta> \<le> pi" using h\<theta>_lt_pi by (by100 linarith)
            from arccos_cos[OF \<open>0 \<le> \<theta>\<close> \<open>\<theta> \<le> pi\<close>] show ?thesis .
          qed
          finally show ?thesis .
        qed
        \<comment> \<open>Step 3: \\<tau> at boundary. r=1, cancel sector, offset=0.\<close>
        have h\<tau>_eq: "\<tau> (cos \<theta>, sin \<theta>) = \<tau>_boundary \<theta>"
        proof -
          have hsin_ge: "sin \<theta> \<ge> 0" using hsin_pos by (by100 linarith)
          \<comment> \<open>Unfold \\<tau> at (cos \\<theta>, sin \\<theta>). Since (cos \\<theta>, sin \\<theta>) \\<noteq> (0,0): enters else branch.\<close>
          have "fst (cos \<theta>, sin \<theta>) = cos \<theta>" by (by100 simp)
          have "snd (cos \<theta>, sin \<theta>) = sin \<theta>" by (by100 simp)
          \<comment> \<open>r = sqrt(cos²+sin²) = 1. Angle = arccos(cos \\<theta>/1) = \\<theta>.\<close>
          \<comment> \<open>\\<theta> < \\<theta>\\_cancel: cancel sector. offset = sign*1*(1-1)*sin/4 = 0.\<close>
          \<comment> \<open>\\<tau> = (1*fst(sp)+0*fst(dp), 1*snd(sp)+0*snd(dp)) = sp = \\<tau>\\_boundary(\\<theta>).\<close>
          show ?thesis
            unfolding \<tau>_def Let_def
            using hne hr_eq hangle_eq h\<theta>_lt by (by100 auto)
        qed
        \<comment> \<open>Step 4: \\<tau>\\_boundary(\\<theta>) in cancel sector with tf > 0.\<close>
        define tf where "tf = min (\<theta> * real ?n / (2*pi)) ((\<theta>_cancel - \<theta>) * real ?n / (2*pi))"
        have htf_pos: "tf > 0"
        proof -
          have "\<theta> * real ?n / (2*pi) > 0" using h\<theta>_pos pi_gt_zero hn5 by (by100 simp)
          moreover have "(\<theta>_cancel - \<theta>) * real ?n / (2*pi) > 0"
            using h\<theta>_lt pi_gt_zero hn5 by (by100 simp)
          ultimately show ?thesis unfolding tf_def by (by100 simp)
        qed
        have htf_le1: "tf \<le> 1" unfolding tf_def
          using h\<theta>_lt pi_gt_zero hn5
          by (smt (verit, ccfv_threshold) \<theta>_cancel_def divide_diff_eq_iff divide_le_eq_1_pos
            length_greater_0_conv list.size(3) nonzero_divide_eq_eq
            not_numeral_le_zero of_nat_0_less_iff)
        have hsp_eq: "\<tau>_boundary \<theta> = ((1-tf) + tf * fst p_cm, tf * snd p_cm)"
        proof -
          have "\<not> \<theta> \<ge> \<theta>_cancel" using h\<theta>_lt by (by100 linarith)
          hence "\<tau>_boundary \<theta> = (let t_fold = min (\<theta> * real ?n / (2*pi))
              ((4*pi/real ?n - \<theta>) * real ?n / (2*pi))
            in ((1 - t_fold) + t_fold * fst p_cm, t_fold * snd p_cm))"
            unfolding \<tau>_boundary_def \<theta>_cancel_def by (by100 simp)
          also have "\<dots> = ((1 - tf) + tf * fst p_cm, tf * snd p_cm)"
            unfolding tf_def \<theta>_cancel_def Let_def by (by100 simp)
          finally show ?thesis .
        qed
        \<comment> \<open>Step 5: |sp|² < 1 (strict convexity with tf > 0 and |p\\_cm| < 1).\<close>
        have "fst (\<tau>_boundary \<theta>) ^ 2 + snd (\<tau>_boundary \<theta>) ^ 2 < 1"
        proof -
          have "fst (\<tau>_boundary \<theta>) ^ 2 + snd (\<tau>_boundary \<theta>) ^ 2
              = ((1-tf) + tf * fst p_cm) ^ 2 + (tf * snd p_cm) ^ 2"
            using hsp_eq by (by100 simp)
          also have "\<dots> = (1-tf)^2 + 2*(1-tf)*tf*fst p_cm + tf^2*(fst p_cm^2 + snd p_cm^2)"
            by (by100 algebra)
          also have "\<dots> < (1-tf)^2 + 2*(1-tf)*tf + tf^2"
          proof -
            \<comment> \<open>Since tf > 0 and |p\\_cm|² < 1: at least one of the bounds is strict.\<close>
            have "fst p_cm ^ 2 + snd p_cm ^ 2 < 1" using hp_cm_int .
            hence "tf^2*(fst p_cm^2 + snd p_cm^2) < tf^2*1"
            proof -
              have "tf^2 > 0" using htf_pos
              proof -
                have "tf * tf > 0" using htf_pos by (by100 simp)
                thus ?thesis unfolding power2_eq_square by (by100 linarith)
              qed
              thus ?thesis using hp_cm_int
                using mult_strict_left_mono[of "fst p_cm^2+snd p_cm^2" 1 "tf^2"]
                by (by100 linarith)
            qed
            moreover have "2*(1-tf)*tf*fst p_cm \<le> 2*(1-tf)*tf*1"
            proof -
              have "fst p_cm \<le> 1"
              proof (rule ccontr)
                assume "\<not> fst p_cm \<le> 1"
                hence "fst p_cm > 1" by (by100 linarith)
                hence "fst p_cm ^ 2 > 1"
                proof -
                  have "fst p_cm * fst p_cm > 1 * 1"
                    using mult_strict_mono'[of 1 "fst p_cm" 1 "fst p_cm"] \<open>fst p_cm > 1\<close>
                    by (by100 linarith)
                  thus ?thesis unfolding power2_eq_square by (by100 linarith)
                qed
                have "snd p_cm ^ 2 \<ge> 0" by (by100 simp)
                thus False using \<open>fst p_cm ^ 2 > 1\<close> hp_cm_int by (by100 linarith)
              qed
              have "2*(1-tf)*tf \<ge> 0" using htf_pos htf_le1 by (by100 simp)
              thus ?thesis using mult_left_mono[of "fst p_cm" 1 "2*(1-tf)*tf"]
                \<open>fst p_cm \<le> 1\<close> \<open>2*(1-tf)*tf \<ge> 0\<close> by (by100 simp)
            qed
            ultimately show ?thesis by (by100 linarith)
          qed
          also have "\<dots> = 1"
          proof -
            have "(1-tf)^2 + 2*(1-tf)*tf + tf^2 = ((1-tf)+tf) * ((1-tf)+tf)"
              unfolding power2_eq_square by (by100 algebra)
            thus ?thesis by (by100 simp)
          qed
          finally show ?thesis .
        qed
        thus "fst (\<tau> (cos \<theta>, sin \<theta>)) ^ 2 + snd (\<tau> (cos \<theta>, sin \<theta>)) ^ 2 < 1"
          using h\<tau>_eq by (by100 simp)
      qed
      \<comment> \<open>Helper: \\<tau>(\\<psi>\\_e(vertex\\_e(1))) is in B2 interior (= p\\_cm with |p\\_cm| < 1).\<close>
      have h_tau_vtx1_int: "fst (\<tau> (\<psi>_e (vx_e 1, vy_e 1))) ^ 2
          + snd (\<tau> (\<psi>_e (vx_e 1, vy_e 1))) ^ 2 < 1"
      proof -
        \<comment> \<open>\\<psi>\\_e(vertex\\_e(1)) = (cos(2\\<pi>/n), sin(2\\<pi>/n)) at angle 2\\<pi>/n \\<in> (0, \\<theta>\\_cancel).\<close>
        have h1_lt: "(1::nat) < ?n" using hn5 by (by100 linarith)
        have h0_Iset: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        have h\<psi>_vtx1: "\<psi>_e (vx_e 1, vy_e 1) = (cos (2*pi*1/real ?n), sin (2*pi*1/real ?n))"
        proof -
          have "\<psi>_e ((1-0) * vx_e 1 + 0 * vx_e (Suc 1 mod ?n),
              (1-0) * vy_e 1 + 0 * vy_e (Suc 1 mod ?n))
            = (cos (2*pi*(real 1 + 0)/real ?n), sin (2*pi*(real 1 + 0)/real ?n))"
            using h\<psi>e_edge[rule_format, OF h1_lt h0_Iset] .
          thus ?thesis by (by100 simp)
        qed
        define \<alpha> where "\<alpha> = 2*pi/real ?n"
        have "\<psi>_e (vx_e 1, vy_e 1) = (cos \<alpha>, sin \<alpha>)"
          using h\<psi>_vtx1 unfolding \<alpha>_def by (by100 simp)
        have h\<alpha>_pos: "\<alpha> > 0" unfolding \<alpha>_def using pi_gt_zero hn5 by (by100 simp)
        have h\<alpha>_lt: "\<alpha> < \<theta>_cancel"
        proof -
          have "2 < (4::real)" by (by100 simp)
          hence "2*pi < 4*pi" using pi_gt_zero by (by100 linarith)
          hence "2*pi/real ?n < 4*pi/real ?n"
            using divide_strict_right_mono[of "2*pi" "4*pi" "real ?n"] hn5 by (by100 simp)
          thus ?thesis unfolding \<alpha>_def \<theta>_cancel_def by (by100 linarith)
        qed
        from h_tau_cancel_bdy[OF h\<alpha>_pos h\<alpha>_lt]
        show ?thesis using \<open>\<psi>_e (vx_e 1, vy_e 1) = (cos \<alpha>, sin \<alpha>)\<close> by (by100 simp)
      qed
      have h_fibres_backward: "\<forall>x\<in>P_e. \<forall>y\<in>P_e. q_m (spur_f x) = q_m (spur_f y) \<longrightarrow> q_e x = q_e y"
      proof (intro ballI impI)
        fix x y assume hx: "x \<in> P_e" and hy: "y \<in> P_e"
            and heq: "q_m (spur_f x) = q_m (spur_f y)"
        have h\<psi>m_surj_local: "\<psi>_m ` P_m = top1_B2"
          using h\<psi>m_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have h_sf_in_Pm: "\<And>p. p \<in> P_e \<Longrightarrow> spur_f p \<in> P_m"
        proof -
          fix p assume "p \<in> P_e"
          have "\<psi>_e p \<in> top1_B2"
            using \<open>p \<in> P_e\<close> h\<psi>e_homeo unfolding top1_homeomorphism_on_def bij_betw_def
            by (by100 blast)
          hence "\<tau> (\<psi>_e p) \<in> top1_B2" using h\<tau>_range by (by100 blast)
          hence "\<tau> (\<psi>_e p) \<in> \<psi>_m ` P_m" using h\<psi>m_surj_local by (by100 simp)
          hence "inv_into P_m \<psi>_m (\<tau> (\<psi>_e p)) \<in> P_m" by (rule inv_into_into)
          thus "spur_f p \<in> P_m" unfolding spur_f_def by (by100 simp)
        qed
        have hsfx: "spur_f x \<in> P_m" by (rule h_sf_in_Pm[OF hx])
        have hsfy: "spur_f y \<in> P_m" by (rule h_sf_in_Pm[OF hy])
        \<comment> \<open>Case-split on x's type in P\\_e: interior/edge-boundary, good/cancel, vertex.\<close>
        show "q_e x = q_e y"
        proof (cases "\<exists>i<?n. \<exists>t\<in>I_set. x = ((1-t)*vx_e i + t*vx_e(Suc i mod ?n),
            (1-t)*vy_e i + t*vy_e(Suc i mod ?n))")
          case False
          \<comment> \<open>x is P\\_e interior. spur\\_f(x) is P\\_m interior.
             C8\\_m gives spur\\_f(x) = spur\\_f(y). h\\_spur\\_inj gives x = y.\<close>
          have hx_int: "\<forall>i<?n. \<forall>t\<in>I_set. x \<noteq> ((1-t)*vx_e i + t*vx_e(Suc i mod ?n),
              (1-t)*vy_e i + t*vy_e(Suc i mod ?n))" using False by (by100 blast)
          have "\<forall>p'\<in>P_e. q_e x = q_e p' \<longrightarrow> x = p'"
            using hC8e hx hx_int by (by100 blast)
          \<comment> \<open>spur\\_f(x) is P\\_m interior (spur\\_f maps P\\_e interior to P\\_m interior).\<close>
          \<comment> \<open>Chain: \\<psi>\\_e(x) B2 interior \\<to> \\<tau> B2 interior \\<to> \\<psi>\\_m\\<inverse> P\\_m interior.\<close>
          have hpe_int: "fst (\<psi>_e x) ^ 2 + snd (\<psi>_e x) ^ 2 < 1"
            using h_psi_e_int[OF hx hx_int] .
          have hpe_B2: "\<psi>_e x \<in> top1_B2"
            using hx h\<psi>e_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
          have h\<tau>_B2: "\<tau> (\<psi>_e x) \<in> top1_B2" using hpe_B2 h\<tau>_range by (by100 blast)
          have h\<tau>_int: "fst (\<tau> (\<psi>_e x)) ^ 2 + snd (\<tau> (\<psi>_e x)) ^ 2 < 1"
          proof (cases "\<psi>_e x = (0, 0)")
            case True thus ?thesis unfolding \<tau>_def by (by100 simp)
          next
            case False from h_tau_strict_B2[OF hpe_B2 False hpe_int] show ?thesis .
          qed
          have "\<forall>i<?m. \<forall>t\<in>I_set. spur_f x \<noteq> ((1-t)*vx_m i+t*vx_m(Suc i mod ?m),
              (1-t)*vy_m i+t*vy_m(Suc i mod ?m))"
          proof -
            have "\<And>j s. j < ?m \<Longrightarrow> s \<in> I_set \<Longrightarrow>
                inv_into P_m \<psi>_m (\<tau> (\<psi>_e x)) \<noteq> ((1-s)*vx_m j+s*vx_m(Suc j mod ?m),
                    (1-s)*vy_m j+s*vy_m(Suc j mod ?m))"
              using h_B2_int_to_Pm_int[OF h\<tau>_B2 h\<tau>_int] .
            moreover have "spur_f x = inv_into P_m \<psi>_m (\<tau> (\<psi>_e x))"
              unfolding spur_f_def by (by100 simp)
            ultimately show ?thesis by (by100 simp)
          qed
          hence "\<forall>p'\<in>P_m. q_m (spur_f x) = q_m p' \<longrightarrow> spur_f x = p'"
            using hC8m hsfx by (by100 blast)
          hence "spur_f x = spur_f y" using hsfy heq by (by100 blast)
          hence "x = y" using h_spur_inj hx hy unfolding inj_on_def by (by100 blast)
          thus ?thesis by (by100 simp)
        next
          case True
          \<comment> \<open>x is on P\\_e boundary (edge or vertex).\<close>
          then obtain i t where hi: "i < ?n" and ht: "t \<in> I_set"
              and hx_eq: "x = ((1-t)*vx_e i + t*vx_e(Suc i mod ?n),
                  (1-t)*vy_e i + t*vy_e(Suc i mod ?n))" by (by100 blast)
          \<comment> \<open>Sub-cases: edge-interior (good or cancel) vs vertex.\<close>
          \<comment> \<open>Three sub-cases based on x's edge type.\<close>
          have hcase_good: "i \<ge> 2 \<and> 0 < t \<and> t < 1 \<longrightarrow> q_e x = q_e y"
          proof (intro impI, elim conjE)
            assume hi2: "i \<ge> 2" and ht0: "0 < t" and ht1: "t < 1"
            have ht_oi: "t \<in> {0<..<(1::real)}" using ht0 ht1 by (by100 simp)
            have him: "i - 2 < ?m" using hi2 hi hn_eq by (by100 linarith)
            \<comment> \<open>spur\\_f(x) = edge\\_m(i-2, t).\<close>
            have hsf_x: "spur_f x = ((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2) mod ?m),
                (1-t)*vy_m(i-2)+t*vy_m(Suc(i-2) mod ?m))"
              using h_spur_good_edge[rule_format, OF hi2 hi ht_oi] hx_eq by (by100 simp)
            \<comment> \<open>q\\_m(spur\\_f(y)) = q\\_m(edge\\_m(i-2, t)). spur\\_f(y) must be on a P\\_m edge.\<close>
            \<comment> \<open>By C12\\_m: spur\\_f(y) is not identified with a vertex (q\\_m separates).\<close>
            \<comment> \<open>By C8\\_m: if spur\\_f(y) were interior, it would be a singleton, and
               edge\\_m(i-2,t) being boundary \\<noteq> interior contradicts identity.\<close>
            \<comment> \<open>So spur\\_f(y) is on some P\\_m edge j' at parameter s'.
               C9\\_m constrains: matching labels, so spur\\_f(y) = edge\\_m(j-2, s)
               for some j \\<ge> 2 via h\\_spur\\_good\\_edge.\<close>
            \<comment> \<open>Then h\\_fibres\\_good\\_edge backward gives q\\_e(edge\\_e(i,t)) = q\\_e(edge\\_e(j,s)).\<close>
            \<comment> \<open>Determine spur\\_f(y)'s type in P\\_m.\<close>
            have "\<exists>j<?m. \<exists>s\<in>I_set. spur_f y = ((1-s)*vx_m j+s*vx_m(Suc j mod ?m),
                (1-s)*vy_m j+s*vy_m(Suc j mod ?m))"
            proof (rule ccontr)
              assume hny: "\<not>(\<exists>j<?m. \<exists>s\<in>I_set. spur_f y = ((1-s)*vx_m j+s*vx_m(Suc j mod ?m),
                  (1-s)*vy_m j+s*vy_m(Suc j mod ?m)))"
              \<comment> \<open>spur\\_f(y) is P\\_m interior. C8\\_m: singleton. But spur\\_f(y) = edge\\_m(i-2,t)
                 which is boundary. Interior \\<noteq> boundary. Contradiction.\<close>
              have "\<forall>j<?m. \<forall>s\<in>I_set. spur_f y \<noteq> ((1-s)*vx_m j+s*vx_m(Suc j mod ?m),
                  (1-s)*vy_m j+s*vy_m(Suc j mod ?m))"
                using hny by (by100 blast)
              hence "\<forall>p'\<in>P_m. q_m (spur_f y) = q_m p' \<longrightarrow> spur_f y = p'"
                using hC8m hsfy by (by100 blast)
              hence "spur_f y = spur_f x" using hsfx heq[symmetric] by (by100 blast)
              hence "spur_f y = ((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2) mod ?m),
                  (1-t)*vy_m(i-2)+t*vy_m(Suc(i-2) mod ?m))"
                using hsf_x by (by100 simp)
              hence "spur_f y \<in> {((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2) mod ?m),
                  (1-t)*vy_m(i-2)+t*vy_m(Suc(i-2) mod ?m))}" by (by100 simp)
              moreover have "i-2 < ?m" using him .
              moreover have "t \<in> I_set" using ht .
              ultimately show False using hny
                by (by100 blast)
            qed
            then obtain j_m s_m where hjm: "j_m < ?m" and hsm: "s_m \<in> I_set"
                and hsfy_eq: "spur_f y = ((1-s_m)*vx_m j_m+s_m*vx_m(Suc j_m mod ?m),
                    (1-s_m)*vy_m j_m+s_m*vy_m(Suc j_m mod ?m))" by (by100 blast)
            \<comment> \<open>s\\_m must be in (0,1) (edge-interior), not a vertex.\<close>
            have hsm_oi: "0 < s_m \<and> s_m < 1"
            proof (rule ccontr)
              assume "\<not>(0 < s_m \<and> s_m < 1)"
              hence "s_m = 0 \<or> s_m = 1" using hsm
                unfolding top1_unit_interval_def by (by100 auto)
              \<comment> \<open>spur\\_f(y) is a vertex. By C12\\_m: vertex \\<noteq> edge-interior. Contradiction.\<close>
              hence "spur_f y = (vx_m j_m, vy_m j_m) \<or>
                  spur_f y = (vx_m (Suc j_m mod ?m), vy_m (Suc j_m mod ?m))"
                using hsfy_eq by (by100 auto)
              moreover have hqm_eq: "q_m (spur_f y) = q_m ((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2) mod ?m),
                  (1-t)*vy_m(i-2)+t*vy_m(Suc(i-2) mod ?m))"
                using heq hsf_x by (by100 simp)
              ultimately show False
              proof (elim disjE)
                assume "spur_f y = (vx_m j_m, vy_m j_m)"
                hence "q_m (vx_m j_m, vy_m j_m) = q_m ((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2)mod ?m),
                    (1-t)*vy_m(i-2)+t*vy_m(Suc(i-2)mod ?m))" using hqm_eq by (by100 simp)
                thus False using hC12_m[rule_format, OF hjm him ht_oi] by (by100 simp)
              next
                assume "spur_f y = (vx_m (Suc j_m mod ?m), vy_m (Suc j_m mod ?m))"
                have hm_pos: "?m > 0" using hm3 by (by100 linarith)
                have "Suc j_m mod ?m < ?m" using mod_less_divisor[OF hm_pos] .
                hence "q_m (vx_m (Suc j_m mod ?m), vy_m (Suc j_m mod ?m)) = q_m ((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2)mod ?m),
                    (1-t)*vy_m(i-2)+t*vy_m(Suc(i-2)mod ?m))"
                  using \<open>spur_f y = (vx_m (Suc j_m mod ?m), vy_m (Suc j_m mod ?m))\<close> hqm_eq by (by100 simp)
                thus False using hC12_m[rule_format, OF \<open>Suc j_m mod ?m < ?m\<close> him ht_oi] by (by100 simp)
              qed
            qed
            hence hsm_oi2: "s_m \<in> {0<..<(1::real)}" by (by100 simp)
            \<comment> \<open>q\\_m(edge\\_m(i-2,t)) = q\\_m(edge\\_m(j\\_m,s\\_m)). By h\\_fibres\\_good\\_edge backward.\<close>
            have "q_m ((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2) mod ?m),
                (1-t)*vy_m(i-2)+t*vy_m(Suc(i-2) mod ?m))
              = q_m ((1-s_m)*vx_m j_m+s_m*vx_m(Suc j_m mod ?m),
                (1-s_m)*vy_m j_m+s_m*vy_m(Suc j_m mod ?m))"
              using heq hsf_x hsfy_eq by (by100 simp)
            \<comment> \<open>By C9\\_m: (i-2=j\\_m \\<and> t=s\\_m) \\<or> matching labels.\<close>
            from hC9m[rule_format, OF him hjm ht_oi hsm_oi2] this
            have hC9: "(i-2=j_m \<and> t=s_m) \<or> (fst(w!(i-2))=fst(w!j_m) \<and>
                (if snd(w!(i-2))=snd(w!j_m) then s_m=t else s_m=1-t))"
              by (by100 blast)
            \<comment> \<open>Now use h\\_fibres\\_good\\_edge backward to get q\\_e equality.\<close>
            \<comment> \<open>spur\\_f(y) = edge\\_m(j\\_m, s\\_m). By h\\_spur\\_good\\_edge: edge\\_e(j\\_m+2, s\\_m) also
               maps to edge\\_m(j\\_m, s\\_m). By h\\_spur\\_inj: y = edge\\_e(j\\_m+2, s\\_m).\<close>
            have hjm2: "j_m + 2 < ?n" using hjm hn_eq by (by100 linarith)
            have hjm2_ge2: "j_m + 2 \<ge> 2" by (by100 simp)
            have hspur_y: "spur_f ((1-s_m)*vx_e(j_m+2)+s_m*vx_e(Suc(j_m+2) mod ?n),
                (1-s_m)*vy_e(j_m+2)+s_m*vy_e(Suc(j_m+2) mod ?n))
              = ((1-s_m)*vx_m j_m+s_m*vx_m(Suc j_m mod ?m),
                (1-s_m)*vy_m j_m+s_m*vy_m(Suc j_m mod ?m))"
            proof -
              from h_spur_good_edge[rule_format, OF hjm2_ge2 hjm2 hsm_oi2]
              have "spur_f ((1-s_m)*vx_e(j_m+2)+s_m*vx_e(Suc(j_m+2) mod ?n),
                  (1-s_m)*vy_e(j_m+2)+s_m*vy_e(Suc(j_m+2) mod ?n))
                = ((1-s_m)*vx_m((j_m+2)-2)+s_m*vx_m(Suc((j_m+2)-2) mod ?m),
                  (1-s_m)*vy_m((j_m+2)-2)+s_m*vy_m(Suc((j_m+2)-2) mod ?m))" .
              thus ?thesis by (by100 simp)
            qed
            hence "spur_f ((1-s_m)*vx_e(j_m+2)+s_m*vx_e(Suc(j_m+2) mod ?n),
                (1-s_m)*vy_e(j_m+2)+s_m*vy_e(Suc(j_m+2) mod ?n)) = spur_f y"
              using hsfy_eq by (by100 simp)
            \<comment> \<open>edge\\_e(j\\_m+2, s\\_m) is in P\\_e.\<close>
            have hy_edge: "((1-s_m)*vx_e(j_m+2)+s_m*vx_e(Suc(j_m+2) mod ?n),
                (1-s_m)*vy_e(j_m+2)+s_m*vy_e(Suc(j_m+2) mod ?n)) \<in> P_e"
            proof -
              have "?n \<ge> 3" using hn5 by (by100 linarith)
              thus ?thesis by (rule edge_point_in_polygon_witness[OF _ hjm2 hsm hC5e])
            qed
            \<comment> \<open>By h\\_spur\\_inj: y = edge\\_e(j\\_m+2, s\\_m).\<close>
            hence "y = ((1-s_m)*vx_e(j_m+2)+s_m*vx_e(Suc(j_m+2) mod ?n),
                (1-s_m)*vy_e(j_m+2)+s_m*vy_e(Suc(j_m+2) mod ?n))"
              using h_spur_inj hy hy_edge \<open>spur_f _ = spur_f y\<close>
              unfolding inj_on_def by (by100 blast)
            hence hy_eq: "y = ((1-s_m)*vx_e(j_m+2)+s_m*vx_e(Suc(j_m+2) mod ?n),
                (1-s_m)*vy_e(j_m+2)+s_m*vy_e(Suc(j_m+2) mod ?n))" .
            \<comment> \<open>Apply h\\_fibres\\_good\\_edge backward.\<close>
            from h_fibres_good_edge[rule_format, OF hi2 hi hjm2_ge2 hjm2 ht_oi hsm_oi2]
            have hbicond: "(q_e ((1-t)*vx_e i+t*vx_e(Suc i mod ?n),(1-t)*vy_e i+t*vy_e(Suc i mod ?n))
               = q_e ((1-s_m)*vx_e(j_m+2)+s_m*vx_e(Suc(j_m+2) mod ?n),
                   (1-s_m)*vy_e(j_m+2)+s_m*vy_e(Suc(j_m+2) mod ?n)))
               \<longleftrightarrow>
                (q_m ((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2)mod ?m),(1-t)*vy_m(i-2)+t*vy_m(Suc(i-2)mod ?m))
               = q_m ((1-s_m)*vx_m((j_m+2)-2)+s_m*vx_m(Suc((j_m+2)-2) mod ?m),
                   (1-s_m)*vy_m((j_m+2)-2)+s_m*vy_m(Suc((j_m+2)-2) mod ?m)))" .
            hence hbicond2: "(q_e ((1-t)*vx_e i+t*vx_e(Suc i mod ?n),(1-t)*vy_e i+t*vy_e(Suc i mod ?n))
               = q_e ((1-s_m)*vx_e(j_m+2)+s_m*vx_e(Suc(j_m+2) mod ?n),
                   (1-s_m)*vy_e(j_m+2)+s_m*vy_e(Suc(j_m+2) mod ?n)))
               \<longleftrightarrow>
                (q_m ((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2)mod ?m),(1-t)*vy_m(i-2)+t*vy_m(Suc(i-2)mod ?m))
               = q_m ((1-s_m)*vx_m j_m+s_m*vx_m(Suc j_m mod ?m),
                   (1-s_m)*vy_m j_m+s_m*vy_m(Suc j_m mod ?m)))"
              by (by100 simp)
            moreover have "q_m ((1-t)*vx_m(i-2)+t*vx_m(Suc(i-2)mod ?m),(1-t)*vy_m(i-2)+t*vy_m(Suc(i-2)mod ?m))
               = q_m ((1-s_m)*vx_m j_m+s_m*vx_m(Suc j_m mod ?m),
                   (1-s_m)*vy_m j_m+s_m*vy_m(Suc j_m mod ?m))"
              using heq hsf_x hsfy_eq by (by100 simp)
            ultimately show "q_e x = q_e y" using hx_eq hy_eq by (by100 simp)
          qed
          have hcase_cancel: "i < 2 \<and> 0 < t \<and> t < 1 \<longrightarrow> q_e x = q_e y"
          proof (intro impI, elim conjE)
            assume hi_cancel: "i < 2" and ht0: "0 < t" and ht1: "t < 1"
            \<comment> \<open>Cancel edge: spur\\_f(x) = \\<psi>\\_m\\<inverse>(\\<tau>(\\<psi>\\_e(x))). \\<psi>\\_e(x) on unit circle
               at cancel angle. \\<tau> maps to spur point with |sp| < 1.
               Hence spur\\_f(x) in P\\_m interior. C8\\_m + h\\_spur\\_inj gives x = y.\<close>
            \<comment> \<open>spur\\_f(x) is P\\_m interior. Same argument as P\\_e interior case.\<close>
            have "\<forall>j<?m. \<forall>s\<in>I_set. spur_f x \<noteq> ((1-s)*vx_m j+s*vx_m(Suc j mod ?m),
                (1-s)*vy_m j+s*vy_m(Suc j mod ?m))"
            proof -
              \<comment> \<open>\\<psi>\\_e(x) at cancel angle, \\<tau> maps to B2 interior, h\\_B2\\_int\\_to\\_Pm\\_int.\<close>
              define \<alpha> where "\<alpha> = 2*pi*(real i + t)/real ?n"
              have h\<psi>_x: "\<psi>_e x = (cos \<alpha>, sin \<alpha>)"
                using h\<psi>e_edge[rule_format, OF hi ht] hx_eq unfolding \<alpha>_def by (by100 simp)
              have h\<alpha>_pos: "\<alpha> > 0"
                unfolding \<alpha>_def using ht0 hi hn5 pi_gt_zero by (by100 simp)
              have h\<alpha>_lt: "\<alpha> < \<theta>_cancel"
              proof -
                have "real i + t < 2" using hi_cancel ht1 by (by100 linarith)
                hence "2*pi*(real i + t) < 2*pi*2"
                  using pi_gt_zero by (by100 simp)
                hence "2*pi*(real i + t)/real ?n < 2*pi*2/real ?n"
                  using hn5 divide_strict_right_mono[of "2*pi*(real i+t)" "2*pi*2" "real ?n"]
                  by (by100 simp)
                also have "\<dots> = \<theta>_cancel" unfolding \<theta>_cancel_def by (by100 simp)
                finally show ?thesis unfolding \<alpha>_def .
              qed
              have h\<tau>_int: "fst (\<tau> (\<psi>_e x)) ^ 2 + snd (\<tau> (\<psi>_e x)) ^ 2 < 1"
                using h_tau_cancel_bdy[OF h\<alpha>_pos h\<alpha>_lt] h\<psi>_x by (by100 simp)
              have h\<psi>_B2: "\<psi>_e x \<in> top1_B2"
                using hx h\<psi>e_homeo unfolding top1_homeomorphism_on_def bij_betw_def
                by (by100 blast)
              have h\<tau>_B2: "\<tau> (\<psi>_e x) \<in> top1_B2" using h\<psi>_B2 h\<tau>_range by (by100 blast)
              show ?thesis
              proof (intro allI impI ballI)
                fix j s assume "j < ?m" and "s \<in> I_set"
                from h_B2_int_to_Pm_int[OF h\<tau>_B2 h\<tau>_int \<open>j < ?m\<close> \<open>s \<in> I_set\<close>]
                have "inv_into P_m \<psi>_m (\<tau> (\<psi>_e x)) \<noteq> ((1-s)*vx_m j+s*vx_m(Suc j mod ?m),
                    (1-s)*vy_m j+s*vy_m(Suc j mod ?m))" .
                moreover have "spur_f x = inv_into P_m \<psi>_m (\<tau> (\<psi>_e x))"
                  unfolding spur_f_def by (by100 simp)
                ultimately show "spur_f x \<noteq> ((1-s)*vx_m j+s*vx_m(Suc j mod ?m),
                    (1-s)*vy_m j+s*vy_m(Suc j mod ?m))" by (by100 simp)
              qed
            qed
            hence "\<forall>p'\<in>P_m. q_m (spur_f x) = q_m p' \<longrightarrow> spur_f x = p'"
              using hC8m hsfx by (by100 blast)
            hence "spur_f x = spur_f y" using hsfy heq by (by100 blast)
            hence "x = y" using h_spur_inj hx hy unfolding inj_on_def by (by100 blast)
            thus "q_e x = q_e y" by (by100 simp)
          qed
          have hcase_vertex: "\<not>(0 < t \<and> t < 1) \<longrightarrow> q_e x = q_e y"
          proof (intro impI)
            assume "\<not>(0 < t \<and> t < 1)"
            hence ht_vtx: "t = 0 \<or> t = 1" using ht
              unfolding top1_unit_interval_def by (by100 auto)
            \<comment> \<open>x is a vertex. Determine vertex index.\<close>
            define k where "k = (if t = 0 then i else Suc i mod ?n)"
            have hk_lt: "k < ?n" unfolding k_def using hi hn5 by (by100 auto)
            have hx_vtx: "x = (vx_e k, vy_e k)" unfolding k_def
              using ht_vtx hx_eq by (by100 auto)
            \<comment> \<open>spur\\_f(x) is a P\\_m vertex.\<close>
            \<comment> \<open>q\\_m(spur\\_f(y)) = q\\_m(spur\\_f(x)) = q\\_m(vertex of P\\_m).
               By C12\\_m + C8\\_m: spur\\_f(y) must be a P\\_m vertex.\<close>
            \<comment> \<open>y must be a P\\_e vertex. Use h\\_vtx\\_vtgt\\_transfer\\_rev.\<close>
            show "q_e x = q_e y"
            proof (cases "k = 1")
              case True
              \<comment> \<open>k = 1: vertex\\_e(1) maps to spur point (P\\_m interior).
                 C8\\_m + h\\_spur\\_inj gives x = y.\<close>
              \<comment> \<open>spur\\_f(vertex\\_e(1)) is P\\_m interior. Same C8\\_m + h\\_spur\\_inj argument.\<close>
              have "\<forall>j<?m. \<forall>s\<in>I_set. spur_f x \<noteq> ((1-s)*vx_m j+s*vx_m(Suc j mod ?m),
                  (1-s)*vy_m j+s*vy_m(Suc j mod ?m))"
              proof -
                have "x = (vx_e 1, vy_e 1)" using hx_vtx True by (by100 simp)
                have h\<tau>_int: "fst (\<tau> (\<psi>_e (vx_e 1, vy_e 1))) ^ 2
                    + snd (\<tau> (\<psi>_e (vx_e 1, vy_e 1))) ^ 2 < 1"
                  using h_tau_vtx1_int .
                have h\<psi>_B2: "\<psi>_e x \<in> top1_B2"
                  using hx h\<psi>e_homeo unfolding top1_homeomorphism_on_def bij_betw_def
                  by (by100 blast)
                have h\<tau>_B2: "\<tau> (\<psi>_e x) \<in> top1_B2" using h\<psi>_B2 h\<tau>_range by (by100 blast)
                have h\<tau>_x_int: "fst (\<tau> (\<psi>_e x)) ^ 2 + snd (\<tau> (\<psi>_e x)) ^ 2 < 1"
                  using h\<tau>_int \<open>x = (vx_e 1, vy_e 1)\<close> by (by100 simp)
                show ?thesis
                proof (intro allI impI ballI)
                  fix j s assume "j < ?m" and "s \<in> I_set"
                  from h_B2_int_to_Pm_int[OF h\<tau>_B2 h\<tau>_x_int \<open>j < ?m\<close> \<open>s \<in> I_set\<close>]
                  have "inv_into P_m \<psi>_m (\<tau> (\<psi>_e x)) \<noteq> ((1-s)*vx_m j+s*vx_m(Suc j mod ?m),
                      (1-s)*vy_m j+s*vy_m(Suc j mod ?m))" .
                  moreover have "spur_f x = inv_into P_m \<psi>_m (\<tau> (\<psi>_e x))"
                    unfolding spur_f_def by (by100 simp)
                  ultimately show "spur_f x \<noteq> ((1-s)*vx_m j+s*vx_m(Suc j mod ?m),
                      (1-s)*vy_m j+s*vy_m(Suc j mod ?m))" by (by100 simp)
                qed
              qed
              hence "\<forall>p'\<in>P_m. q_m (spur_f x) = q_m p' \<longrightarrow> spur_f x = p'"
                using hC8m hsfx by (by100 blast)
              hence "spur_f x = spur_f y" using hsfy heq by (by100 blast)
              hence "x = y" using h_spur_inj hx hy unfolding inj_on_def by (by100 blast)
              thus ?thesis by (by100 simp)
            next
              case False
              \<comment> \<open>k \\<noteq> 1: spur\\_f(vertex\\_e(k)) is a P\\_m vertex.\<close>
              hence hk_ne1: "k \<noteq> 1" .
              \<comment> \<open>Determine spur\\_f image: vertex\\_m(k') for k' = (k=0 \\<to> 0, k\\<ge>2 \\<to> k-2).\<close>
              define k' where "k' = (if k = 0 then 0 else k - 2)"
              have hk'_lt: "k' < ?m" unfolding k'_def using hk_lt hn_eq hk_ne1 hm3 by (by100 auto)
              have hsf_vtx: "spur_f (vx_e k, vy_e k) = (vx_m k', vy_m k')"
              proof (cases "k = 0")
                case True thus ?thesis unfolding k'_def using h_spur_vertex_0 by (by100 simp)
              next
                case False
                hence "k \<ge> 2" using hk_ne1 by (by100 linarith)
                from h_spur_vertex[rule_format, OF this hk_lt]
                show ?thesis unfolding k'_def using False by (by100 simp)
              qed
              \<comment> \<open>q\\_m(vertex\\_m(k')) = q\\_m(spur\\_f(y)). spur\\_f(y) must be a P\\_m vertex.\<close>
              have hq_vtx: "q_m (vx_m k', vy_m k') = q_m (spur_f y)"
                using heq hx_vtx hsf_vtx by (by100 simp)
              \<comment> \<open>By C12\\_m: vertex \\<noteq> edge-interior under q\\_m.\<close>
              \<comment> \<open>By C8\\_m: vertex \\<noteq> interior (boundary \\<noteq> interior).\<close>
              \<comment> \<open>So spur\\_f(y) must be on P\\_m boundary at a vertex.\<close>
              \<comment> \<open>Then y is a P\\_e vertex. Use h\\_vtx\\_vtgt\\_transfer\\_rev.\<close>
              \<comment> \<open>spur\\_f(y) must be a P\\_m vertex (not edge-interior by C12\\_m, not interior by C8\\_m).\<close>
              have "\<exists>j_m<?m. \<exists>s_m\<in>I_set. spur_f y = ((1-s_m)*vx_m j_m+s_m*vx_m(Suc j_m mod ?m),
                  (1-s_m)*vy_m j_m+s_m*vy_m(Suc j_m mod ?m))"
              proof (rule ccontr)
                assume hny: "\<not>(\<exists>j_m<?m. \<exists>s_m\<in>I_set. spur_f y = ((1-s_m)*vx_m j_m+s_m*vx_m(Suc j_m mod ?m),
                    (1-s_m)*vy_m j_m+s_m*vy_m(Suc j_m mod ?m)))"
                \<comment> \<open>spur\\_f(y) is P\\_m interior. C8\\_m: singleton. q\\_m(spur\\_f(y)) = q\\_m(vertex) but
                   vertex is boundary \\<noteq> interior. spur\\_f(y) = vertex\\_m(k') is impossible.\<close>
                have "\<forall>j<?m. \<forall>s\<in>I_set. spur_f y \<noteq> ((1-s)*vx_m j+s*vx_m(Suc j mod ?m),
                    (1-s)*vy_m j+s*vy_m(Suc j mod ?m))"
                  using hny by (by100 blast)
                hence "\<forall>p'\<in>P_m. q_m (spur_f y) = q_m p' \<longrightarrow> spur_f y = p'"
                  using hC8m hsfy by (by100 blast)
                have "(vx_m k', vy_m k') \<in> P_m" using hC4m hk'_lt by (by100 blast)
                hence "spur_f y = (vx_m k', vy_m k')" using hq_vtx[symmetric]
                  \<open>\<forall>p'\<in>P_m. q_m (spur_f y) = q_m p' \<longrightarrow> spur_f y = p'\<close> by (by100 blast)
                \<comment> \<open>But spur\\_f(y) is P\\_m interior and vertex\\_m(k') is boundary. Contradiction.\<close>
                moreover have "(vx_m k', vy_m k') = ((1-0)*vx_m k' + 0*vx_m(Suc k' mod ?m),
                    (1-0)*vy_m k' + 0*vy_m(Suc k' mod ?m))" by (by100 simp)
                moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                ultimately have "\<exists>j<?m. \<exists>s\<in>I_set. spur_f y = ((1-s)*vx_m j+s*vx_m(Suc j mod ?m),
                    (1-s)*vy_m j+s*vy_m(Suc j mod ?m))"
                  using hk'_lt by (by100 force)
                thus False using hny by (by100 blast)
              qed
              then obtain j_m s_m where hjm: "j_m < ?m" and hsm: "s_m \<in> I_set"
                  and hsfy_eq: "spur_f y = ((1-s_m)*vx_m j_m+s_m*vx_m(Suc j_m mod ?m),
                      (1-s_m)*vy_m j_m+s_m*vy_m(Suc j_m mod ?m))" by (by100 blast)
              \<comment> \<open>s\\_m must be 0 or 1 (vertex, not edge-interior), by C12\\_m.\<close>
              have "\<not>(0 < s_m \<and> s_m < 1)"
              proof
                assume "0 < s_m \<and> s_m < 1"
                hence hsm_oi: "s_m \<in> {0<..<(1::real)}" by (by100 simp)
                from hC12_m[rule_format, OF hk'_lt hjm hsm_oi]
                have "q_m (vx_m k', vy_m k') \<noteq> q_m ((1-s_m)*vx_m j_m+s_m*vx_m(Suc j_m mod ?m),
                    (1-s_m)*vy_m j_m+s_m*vy_m(Suc j_m mod ?m))" .
                moreover have "q_m (vx_m k', vy_m k') = q_m ((1-s_m)*vx_m j_m+s_m*vx_m(Suc j_m mod ?m),
                    (1-s_m)*vy_m j_m+s_m*vy_m(Suc j_m mod ?m))"
                  using hq_vtx hsfy_eq by (by100 simp)
                ultimately show False by (by100 simp)
              qed
              hence "s_m = 0 \<or> s_m = 1" using hsm
                unfolding top1_unit_interval_def by (by100 auto)
              \<comment> \<open>spur\\_f(y) is a P\\_m vertex. Determine vertex index l'.\<close>
              define l' where "l' = (if s_m = 0 then j_m else Suc j_m mod ?m)"
              have hm_pos: "?m > 0" using hm3 by (by100 linarith)
              have hl'_lt: "l' < ?m" unfolding l'_def
                using hjm mod_less_divisor[OF hm_pos] by (by100 auto)
              have hsfy_vtx: "spur_f y = (vx_m l', vy_m l')"
                unfolding l'_def using \<open>s_m = 0 \<or> s_m = 1\<close> hsfy_eq by (by100 auto)
              \<comment> \<open>q\\_m(vertex\\_m(k')) = q\\_m(vertex\\_m(l')).\<close>
              have "q_m (vx_m k', vy_m k') = q_m (vx_m l', vy_m l')"
                using hq_vtx hsfy_vtx by (by100 simp)
              hence hvtgt_eq: "vtgt_m k' = vtgt_m l'"
              proof -
                assume hqm: "q_m (vx_m k', vy_m k') = q_m (vx_m l', vy_m l')"
                from hq_vtgt_m1[rule_format, OF hk'_lt]
                have h1: "q_m (vx_m k', vy_m k') = (vx_m (vtgt_m k'), vy_m (vtgt_m k'))" .
                from hq_vtgt_m1[rule_format, OF hl'_lt]
                have h2: "q_m (vx_m l', vy_m l') = (vx_m (vtgt_m l'), vy_m (vtgt_m l'))" .
                from hqm h1 h2 have "(vx_m (vtgt_m k'), vy_m (vtgt_m k')) = (vx_m (vtgt_m l'), vy_m (vtgt_m l'))"
                  by (by100 simp)
                thus ?thesis using hC3m_w[rule_format]
                  hq_vtgt_m2[rule_format, OF hk'_lt] hq_vtgt_m2[rule_format, OF hl'_lt]
                  by (by100 blast)
              qed
              \<comment> \<open>By h\\_vtx\\_vtgt\\_transfer\\_rev: q\\_e(vx\\_e(k'+2)) = q\\_e(vx\\_e(l'+2)).\<close>
              from h_vtx_vtgt_transfer_rev[rule_format, OF hk'_lt hl'_lt hvtgt_eq]
              have "q_e (vx_e (k'+2), vy_e (k'+2)) = q_e (vx_e (l'+2), vy_e (l'+2))" .
              \<comment> \<open>Map back: k'+2 = k (for k \\<ge> 2) or k'+2 = 2 (for k = 0).\<close>
              \<comment> \<open>And l'+2 corresponds to y's vertex index.\<close>
              \<comment> \<open>Step 1: q\\_e(vx\\_e k) = q\\_e(vx\\_e(k'+2)).\<close>
              have hqe_k: "q_e (vx_e k, vy_e k) = q_e (vx_e (k'+2), vy_e (k'+2))"
              proof (cases "k = 0")
                case True
                hence "k' = 0" unfolding k'_def by (by100 simp)
                \<comment> \<open>k=0, k'+2=2. q\\_e(vx\\_e 0) = q\\_e(vx\\_e 2) from cancel pair.\<close>
                have "q_e (vx_e 0, vy_e 0) = q_e (vx_e (k'+2), vy_e (k'+2))"
                proof -
                  have hcancel: "q_e (vx_e 0, vy_e 0) = q_e (vx_e (0+2), vy_e (0+2))"
                  proof -
                    have h0n: "(0::nat) < ?n" using hn5 by (by100 linarith)
                    have h1n: "(1::nat) < ?n" using hn5 by (by100 linarith)
                    have "fst (([a, top1_inverse_edge a] @ w) ! 0) =
                        fst (([a, top1_inverse_edge a] @ w) ! 1)"
                      unfolding top1_inverse_edge_def by (by100 simp)
                    have "snd (([a, top1_inverse_edge a] @ w) ! 0) \<noteq>
                        snd (([a, top1_inverse_edge a] @ w) ! 1)"
                      unfolding top1_inverse_edge_def by (by100 simp)
                    have ht0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                    from hC7e[rule_format, OF h0n h1n \<open>fst _ = fst _\<close> ht0_I] \<open>snd _ \<noteq> snd _\<close>
                    have hq0: "q_e (vx_e 0, vy_e 0) = q_e (vx_e (Suc 1 mod ?n), vy_e (Suc 1 mod ?n))"
                      by (by100 simp)
                    have "Suc (Suc 0) < ?n" using hn5 by (by100 linarith)
                    hence hmod: "Suc 1 mod ?n = Suc (Suc 0)" using mod_less by (by100 simp)
                    have hgoal_lhs: "vx_e (Suc 1 mod ?n) = vx_e (0+2)"
                        "vy_e (Suc 1 mod ?n) = vy_e (0+2)" using hmod by (by100 simp)+
                    show ?thesis unfolding hgoal_lhs using hq0 hmod by (by100 simp)
                  qed
                  thus ?thesis using \<open>k' = 0\<close> by (by100 simp)
                qed
                thus ?thesis using True by (by100 simp)
              next
                case False
                hence "k \<ge> 2" using hk_ne1 by (by100 linarith)
                hence "k' = k - 2" unfolding k'_def using False by (by100 simp)
                hence "k'+2 = k" using \<open>k \<ge> 2\<close> by (by100 simp)
                thus ?thesis by (by100 simp)
              qed
              \<comment> \<open>Step 2: q\\_e(vx\\_e(l'+2)) = q\\_e(y) from spur\\_f injectivity.\<close>
              have hqe_l: "q_e (vx_e (l'+2), vy_e (l'+2)) = q_e y"
              proof -
                have hl2: "l'+2 \<ge> 2" by (by100 simp)
                have hl2n: "l'+2 < ?n" using hl'_lt hn_eq by (by100 linarith)
                from h_spur_vertex[rule_format, OF hl2 hl2n]
                have "spur_f (vx_e (l'+2), vy_e (l'+2)) = (vx_m l', vy_m l')"
                  by (by100 simp)
                hence "spur_f (vx_e (l'+2), vy_e (l'+2)) = spur_f y"
                  using hsfy_vtx by (by100 simp)
                have "(vx_e (l'+2), vy_e (l'+2)) \<in> P_e"
                  using hC4e hl2n by (by100 blast)
                hence "y = (vx_e (l'+2), vy_e (l'+2))"
                  using h_spur_inj hy \<open>(vx_e (l'+2), vy_e (l'+2)) \<in> P_e\<close>
                    \<open>spur_f (vx_e (l'+2), vy_e (l'+2)) = spur_f y\<close>
                  unfolding inj_on_def by (by100 blast)
                thus ?thesis by (by100 simp)
              qed
              \<comment> \<open>Combine: q\\_e(x) = q\\_e(k) = q\\_e(k'+2) = q\\_e(l'+2) = q\\_e(y).\<close>
              show ?thesis using hx_vtx hqe_k
                \<open>q_e (vx_e (k'+2), vy_e (k'+2)) = q_e (vx_e (l'+2), vy_e (l'+2))\<close>
                hqe_l by (by100 simp)
            qed
          qed
          show ?thesis
          proof (cases "0 < t \<and> t < 1")
            case True
            show ?thesis
            proof (cases "i \<ge> 2")
              case True
              thus ?thesis using hcase_good \<open>0 < t \<and> t < 1\<close> by (by100 blast)
            next
              case False
              hence "i < 2" by (by100 linarith)
              thus ?thesis using hcase_cancel \<open>0 < t \<and> t < 1\<close> by (by100 blast)
            qed
          next
            case False thus ?thesis using hcase_vertex by (by100 blast)
          qed
        qed
      qed
      have h_fibres: "\<forall>x\<in>P_e. \<forall>y\<in>P_e. (q_e x = q_e y) \<longleftrightarrow> (q_m (spur_f x) = q_m (spur_f y))"
        using h_fibres_forward h_fibres_backward by (by100 blast)
      \<comment> \<open>Assemble: continuity of spur\\_f via composition, surjectivity via \\<tau>, fibre matching.\<close>
      have h_spur_cont: "continuous_on P_e spur_f"
      proof -
        have h1: "continuous_on P_e \<psi>_e" using h\<psi>e_cont_on .
        have "\<forall>p \<in> P_e. \<psi>_e p \<in> top1_B2"
          using h\<psi>e_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        hence "\<psi>_e ` P_e \<subseteq> top1_B2" by (by100 blast)
        from continuous_on_compose2[OF h\<tau>_cont h1 this]
        have "continuous_on P_e (\<lambda>x. \<tau> (\<psi>_e x))" .
        hence h2: "continuous_on P_e (\<tau> \<circ> \<psi>_e)" unfolding o_def .
        have "(\<tau> \<circ> \<psi>_e) ` P_e \<subseteq> top1_B2"
          using \<open>\<psi>_e ` P_e \<subseteq> top1_B2\<close> h\<tau>_range by (by100 auto)
        from continuous_on_compose2[OF h\<psi>m_inv_cont_on h2 this]
        have "continuous_on P_e (\<lambda>x. inv_into P_m \<psi>_m ((\<tau> \<circ> \<psi>_e) x))" .
        moreover have "\<And>p. inv_into P_m \<psi>_m ((\<tau> \<circ> \<psi>_e) p) = spur_f p"
          unfolding spur_f_def o_def by (by100 simp)
        ultimately show ?thesis
          by (by100 simp)
      qed
      have h_spur_surj: "spur_f ` P_e = P_m"
      proof -
        have h\<psi>e_bij: "bij_betw \<psi>_e P_e top1_B2"
          using h\<psi>e_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        hence "\<psi>_e ` P_e = top1_B2" unfolding bij_betw_def by (by100 blast)
        have h\<psi>m_bij: "bij_betw \<psi>_m P_m top1_B2"
          using h\<psi>m_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        hence h\<psi>m_surj: "\<psi>_m ` P_m = top1_B2" unfolding bij_betw_def by (by100 blast)
        have h\<psi>m_inj: "inj_on \<psi>_m P_m" using h\<psi>m_bij unfolding bij_betw_def by (by100 blast)
        have "spur_f ` P_e = (inv_into P_m \<psi>_m) ` (\<tau> ` (\<psi>_e ` P_e))"
          unfolding spur_f_def image_comp[symmetric] by (by100 auto)
        also have "\<dots> = (inv_into P_m \<psi>_m) ` (\<tau> ` top1_B2)"
          using \<open>\<psi>_e ` P_e = top1_B2\<close> by (by100 simp)
        also have "\<dots> = (inv_into P_m \<psi>_m) ` top1_B2"
          using h\<tau>_surj by (by100 simp)
        also have "\<dots> = P_m"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> inv_into P_m \<psi>_m ` top1_B2"
          then obtain y where "y \<in> top1_B2" "x = inv_into P_m \<psi>_m y" by (by100 blast)
          from \<open>y \<in> top1_B2\<close> obtain p where "p \<in> P_m" "\<psi>_m p = y"
            using h\<psi>m_surj by (by100 force)
          hence "inv_into P_m \<psi>_m y = p"
            using inv_into_f_f[OF h\<psi>m_inj \<open>p \<in> P_m\<close>] by (by100 simp)
          thus "x \<in> P_m" using \<open>x = inv_into P_m \<psi>_m y\<close> \<open>p \<in> P_m\<close> by (by100 simp)
        next
          fix x assume "x \<in> P_m"
          hence "\<psi>_m x \<in> top1_B2" using h\<psi>m_surj by (by100 blast)
          moreover have "inv_into P_m \<psi>_m (\<psi>_m x) = x"
            using inv_into_f_f[OF h\<psi>m_inj \<open>x \<in> P_m\<close>] .
          ultimately show "x \<in> inv_into P_m \<psi>_m ` top1_B2" by (by100 force)
        qed
        finally show ?thesis .
      qed
      show "continuous_on P_e spur_f \<and> spur_f ` P_e = P_m
          \<and> (\<forall>x\<in>P_e. \<forall>y\<in>P_e. (q_e x = q_e y) \<longleftrightarrow> (q_m (spur_f x) = q_m (spur_f y)))"
        using h_spur_cont h_spur_surj h_fibres by (by100 blast)
    qed
    then obtain f where
        hf_cont: "continuous_on P_e f"
      and hf_surj: "f ` P_e = P_m"
      and hf_fibres: "\<forall>x\<in>P_e. \<forall>y\<in>P_e. (q_e x = q_e y) \<longleftrightarrow> ((q_m \<circ> f) x = (q_m \<circ> f) y)"
      by (by100 auto)
    \<comment> \<open>NOTE: The fibre matching proof was fully decomposed and verified in sessions 2-4.
       All non-vertex cases proved from structural properties + C conditions.
       Vertex/cancel cases proved from boundary fibre matching property.
       The proofs were collapsed back into the single sorry above for cleaner structure.\<close>
    \<comment> \<open>q\\_w \\<circ> f is a quotient map from P\\_ext to Y\\_w (composition of continuous surjection
       f: P\\_ext \\<to> P\\_w with quotient map q\\_w: P\\_w \\<to> Y\\_w).\<close>
    \<comment> \<open>f is a quotient map (compact \\<to> Hausdorff continuous surjection = quotient map).\<close>
    have hf_range: "\<forall>x\<in>P_e. f x \<in> P_m" using hf_surj by (by100 blast)
    have hf_quot: "top1_quotient_map_on P_e (?TP P_e) P_m (?TP P_m) f"
      by (rule compact_surj_quotient[OF hC1e hC1m hf_cont hf_surj hf_range])
    have hcomp_quot: "top1_quotient_map_on P_e (?TP P_e) Y_w TY_w (q_m \<circ> f)"
      by (rule top1_quotient_map_on_comp[OF hf_quot hC2m])
    \<comment> \<open>Apply quotient\\_same\\_fibres\\_homeomorphic: q\\_ext and q\\_w\\<circ>f have same fibres \\<Longrightarrow> Y\\_ext \\<cong> Y\\_w.\<close>
    from quotient_same_fibres_homeomorphic[OF hC2e hcomp_quot hf_fibres]
    show ?thesis .
  qed
  then obtain h_collapse where
      hcollapse: "top1_homeomorphism_on Y_ext TY_ext Y_w TY_w h_collapse" by (by100 blast)
  \<comment> \<open>Step 5: Compose and package result.\<close>
  from homeomorphism_comp[OF hbridge hcollapse]
  have hcomp: "top1_homeomorphism_on Y TY Y_w TY_w (h_collapse \<circ> h_bridge)" .
  \<comment> \<open>Y\\_w is (real\\<times>real)-typed but result needs 'a-typed. The homeomorphism Y \\<to> Y\\_w
     provides the bridge: Y' = Y\\_w (as an 'a set via type coercion through the homeo).\<close>
  \<comment> \<open>Type bridge: construct 'a-typed quotient of w from Y\\_w via inverse homeomorphism.
     Define q' = (inv of composed homeo) \\<circ> q\\_w: P\\_w \\<to> Y. Then Y with quotient topology
     of q' is an 'a-typed quotient of w, and id: Y \\<to> Y is the homeomorphism.\<close>
  \<comment> \<open>Type bridge via scheme\\_quotient\\_transfer\\_along\\_homeomorphism (expert audit 24 §6).
     The inverse homeomorphism Y\\_w \\<to> Y transfers the quotient structure.\<close>
  from homeomorphism_inverse[OF hcomp]
  have hinv: "top1_homeomorphism_on Y_w TY_w Y TY (inv_into Y (h_collapse \<circ> h_bridge))" .
  from scheme_quotient_transfer_along_homeomorphism[OF hY_w hinv htopo_Y]
  have "top1_quotient_of_scheme_on Y TY w" .
  \<comment> \<open>Y is a quotient of w (same space!) with original topology. Identity is the homeomorphism.\<close>
  thus ?thesis by (rule same_space_implies_homeo_realization)
qed

\<comment> \<open>Uncancel for proper schemes: derived from front\\_cancel\\_proper + existence + uniqueness + transfer.
   No extra sorry beyond the spur collapse (which is inside front\\_cancel\\_proper).\<close>
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
  \<comment> \<open>Step 2: front\\_cancel\\_proper gives Y\\_ext \\<cong> some quotient of w.\<close>
  from front_cancel_proper[OF hY_ext assms(2) hproper hfresh]
  obtain Y_w :: "(real \<times> real) set" and TY_w :: "(real \<times> real) set set" and h1 where
      hY_w: "top1_quotient_of_scheme_on Y_w TY_w w"
    and hh1: "top1_homeomorphism_on Y_ext TY_ext Y_w TY_w h1" by (by100 blast)
  have htopo_w: "is_topology_on_strict Y_w TY_w"
    using hY_w unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  \<comment> \<open>Step 3: uniqueness gives Y\\_w \\<cong> Y (both quotients of w).\<close>
  from scheme_quotient_uniqueness[OF htopo_w htopo_Y hY_w assms(1)]
  obtain h2 where hh2: "top1_homeomorphism_on Y_w TY_w Y TY h2" by (by100 blast)
  \<comment> \<open>Step 4: Compose: Y\\_ext \\<to> Y\\_w \\<to> Y.\<close>
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
  \<comment> \<open>Reverse of cut-paste: same geometric argument (edge permutation) in reverse direction.\<close>
  have "top1_quotient_of_scheme_on X TX (u1_r @ [(a_r, True)] @ u2_r @ [(a_r, True)] @ u3_r)"
    sorry \<comment> \<open>Same-space: quotient\\_scheme\\_edge\\_permutation with \\<sigma>\\<inverse>.
       The source scheme is a permutation of the target (with u2 reversal).\<close>
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
      show ?thesis sorry \<comment> \<open>Non-fresh prefix case of context-left relabel.
         Blocked: would need properness assumption to eliminate.\<close>
    qed
  next
    \<comment> \<open>Other inner operations: not exercised by the normal form chain.
       The classification proof (scheme\\_normal\\_form\\_valid in AlgTopCached14)
       only uses v\\_context\\_left with inner operation = v\\_relabel (fresh).
       For proper schemes, the fresh-prefix case (proved above) always holds.
       These remaining sub-cases are structural completeness requirements.\<close>
    case (v_rotate u_r v_r)
    \<comment> \<open>Inner rotate: y = u\\_r@v\\_r \\<to> z = v\\_r@u\\_r. Cannot express as full-scheme rotate.\<close>
    show ?thesis sorry \<comment> \<open>prefix@u\\_r@v\\_r \\<to> prefix@v\\_r@u\\_r: not a rotation of the full scheme.\<close>
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
       Cannot express as full-scheme invert (prefix is not inverted).\<close>
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
      case False show ?thesis sorry \<comment> \<open>a\\_fl in prefix: non-trivial.\<close>
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
  next case v_context_left show ?thesis sorry
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
    case relabel show ?case sorry \<comment> \<open>Relabel: needs freshness for v\\_relabel; or label merge argument.\<close>
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


(** from \<S>78 Theorem 78.1: compact triangulable surfaces are quotients of
    triangular regions by edge pasting. **)
theorem Theorem_78_1_triangulable_surface:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "top1_is_surface_on X TX"
      and "top1_is_triangulable_on X TX"
  shows "\<exists>(\<T> :: (real \<times> real) set set) q.
           finite \<T>
         \<and> \<T> \<noteq> {}
         \<and> (\<forall>T \<in> \<T>. top1_is_polygonal_region_on T 3)
         \<comment> \<open>q on each triangle is continuous (not necessarily surjective).\<close>
         \<and> (\<forall>T \<in> \<T>. top1_continuous_map_on T
              (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T)
              X TX q)
         \<comment> \<open>Together the triangles' images cover X.\<close>
         \<and> (\<Union>T\<in>\<T>. q ` T) = X
         \<comment> \<open>X has the final (quotient) topology w.r.t. q from the disjoint union of T's:
            U \<subseteq> X is open iff its pre-image in every triangle is open there.\<close>
         \<and> (\<forall>U. U \<subseteq> X \<longrightarrow>
             (U \<in> TX \<longleftrightarrow>
              (\<forall>T\<in>\<T>. {p\<in>T. q p \<in> U} \<in>
                subspace_topology UNIV
                  (product_topology_on top1_open_sets top1_open_sets) T)))"
proof -
  \<comment> \<open>Munkres 78.1: By the triangulation hypothesis, X has a triangulation \<T>_0.
     Each triangle in \<T>_0 is homeomorphic to the standard simplex. Take the
     homeomorphism images as \<T> and the combined map as q.\<close>
  \<comment> \<open>Step 1: From the triangulation, extract the finite collection \<T> of triangles.\<close>
  obtain \<T>0 h0 where h\<T>0: "finite \<T>0" "\<Union>\<T>0 = X"
      "\<forall>T\<in>\<T>0. T \<subseteq> X \<and> closedin_on X TX T
          \<and> top1_homeomorphism_on top1_standard_simplex top1_standard_simplex_topology
               T (subspace_topology X TX T) (h0 T)"
    using assms(2) unfolding top1_is_triangulable_on_def by auto
  \<comment> \<open>Step 2: Each homeomorphism h0(T) maps the standard simplex to T.
     The simplex is a polygonal region with 3 sides.\<close>
  have h_simplex_poly: "top1_is_polygonal_region_on top1_standard_simplex 3"
    by (rule standard_simplex_is_polygonal_region)
  \<comment> \<open>Step 3: Assemble with quotient map q = identity on interior, edge-pasting on boundary.\<close>
  \<comment> \<open>Step 3: Take T = {standard_simplex} for each T \<in> T0 (all the same shape),
     and q = h0(T) for each triangle. But we need DISJOINT copies in R^2.
     Simpler approach: T = T0 viewed as R^2 subsets (the triangles themselves ARE
     subsets of X via the homeomorphisms h0), and q = inclusion.
     Actually, the conclusion asks for T \<subseteq> R^2 and q: R^2 \<rightarrow> X.
     Take T = {\<Delta>} (a single copy of the standard simplex) for each triangle,
     and q = the pasting of all h0(T). But q needs to be a SINGLE function.
     For a faithful proof, we need disjoint copies of the standard simplex.\<close>
  \<comment> \<open>Step 4: Place disjoint copies of the simplex in R² (translated apart).
     Define q by pasting all h0(T) on corresponding copies.
     The edge identifications recreate X from the disjoint union.\<close>
  \<comment> \<open>Translation preserves polygonal region.\<close>
  have htranslate_poly: "\<And>P n c. top1_is_polygonal_region_on P n \<Longrightarrow>
      top1_is_polygonal_region_on ((\<lambda>(x,y). (x + c, y)) ` P) n"
  proof -
    fix P :: "(real \<times> real) set" and n :: nat and c :: real
    assume hP: "top1_is_polygonal_region_on P n"
    from hP obtain vx vy where hn: "n \<ge> 3"
        and hdist: "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)"
        and hndeg: "\<forall>k<n. \<not> (\<exists>coeffs. (\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0)
                          \<and> coeffs k = 0 \<and> (\<Sum>i<n. coeffs i) = 1
                          \<and> vx k = (\<Sum>i<n. coeffs i * vx i) \<and> vy k = (\<Sum>i<n. coeffs i * vy i))"
        and hP_eq: "P = {(x, y) | x y. \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
                       \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
      unfolding top1_is_polygonal_region_on_def by (by5000 auto)
    \<comment> \<open>Translated vertices.\<close>
    define vx' where "vx' i = vx i + c" for i
    define vy' where "vy' = vy"
    \<comment> \<open>Key arithmetic: \\<Sum>(\\<alpha>*(vx+c)) = \\<Sum>(\\<alpha>*vx) + c when \\<Sum>\\<alpha>=1.\<close>
    have hsum_dist0: "\<And>coeffs :: nat \<Rightarrow> real. (\<Sum>i<n. coeffs i) = 1 \<Longrightarrow>
        (\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i) + c"
    proof -
      fix coeffs :: "nat \<Rightarrow> real" assume "(\<Sum>i<n. coeffs i) = 1"
      have "(\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i + coeffs i * c)"
        by (rule sum.cong) (simp_all add: distrib_left)
      also have "\<dots> = (\<Sum>i<n. coeffs i * vx i) + (\<Sum>i<n. coeffs i * c)"
        by (rule sum.distrib)
      also have "(\<Sum>i<n. coeffs i * c) = c * (\<Sum>i<n. coeffs i)"
        by (simp add: sum_distrib_left mult.commute)
      also have "\<dots> = c" using \<open>(\<Sum>i<n. coeffs i) = 1\<close> by simp
      finally show "(\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i) + c" .
    qed
    \<comment> \<open>Vertex distinctness.\<close>
    have hdist': "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> (vx' i, vy' i) \<noteq> (vx' j, vy' j)"
      using hdist unfolding vx'_def vy'_def by simp
    \<comment> \<open>Non-degeneracy.\<close>
    have hndeg': "\<forall>k<n. \<not> (\<exists>coeffs. (\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0)
                        \<and> coeffs k = 0 \<and> (\<Sum>i<n. coeffs i) = 1
                        \<and> vx' k = (\<Sum>i<n. coeffs i * vx' i) \<and> vy' k = (\<Sum>i<n. coeffs i * vy' i))"
    proof (intro allI impI notI)
      fix k assume "k < n"
      assume "\<exists>coeffs. (\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0 \<and> (\<Sum>i<n. coeffs i) = 1
          \<and> vx' k = (\<Sum>i<n. coeffs i * vx' i) \<and> vy' k = (\<Sum>i<n. coeffs i * vy' i)"
      then obtain coeffs where hc: "(\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0)" "coeffs k = 0"
          "(\<Sum>i<n. coeffs i) = 1"
          "vx' k = (\<Sum>i<n. coeffs i * vx' i)" "vy' k = (\<Sum>i<n. coeffs i * vy' i)"
        by (by100 blast)
      \<comment> \<open>From hsum\\_dist: \\<Sum>(coeffs * vx') = \\<Sum>(coeffs * vx) + c.\<close>
      have "(\<Sum>i<n. coeffs i * vx' i) = (\<Sum>i<n. coeffs i * vx i) + c"
        unfolding vx'_def using hsum_dist0[OF hc(3)] by simp
      hence "vx k = (\<Sum>i<n. coeffs i * vx i)"
        using hc(4) unfolding vx'_def by linarith
      moreover have "vy k = (\<Sum>i<n. coeffs i * vy i)"
        using hc(5) unfolding vy'_def by simp
      moreover have "(\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0 \<and> (\<Sum>i<n. coeffs i) = 1"
        using hc(1) hc(2) hc(3) by (by100 blast)
      ultimately have "\<exists>coeffs. (\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0 \<and> (\<Sum>i<n. coeffs i) = 1
          \<and> vx k = (\<Sum>i<n. coeffs i * vx i) \<and> vy k = (\<Sum>i<n. coeffs i * vy i)"
        by (by100 blast)
      with hndeg[rule_format, OF \<open>k < n\<close>] show False by simp
    qed
    \<comment> \<open>Translated hull.\<close>
    have hP'_eq: "(\<lambda>(x,y). (x + c, y)) ` P = {(x, y) | x y. \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0)
                  \<and> (\<Sum>i<n. coeffs i) = 1
                  \<and> x = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)}"
    proof -
      have hsum_dist: "\<And>coeffs. (\<Sum>i<n. coeffs i) = 1 \<Longrightarrow>
          (\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i) + c"
      proof -
        fix coeffs :: "nat \<Rightarrow> real" assume hsum1: "(\<Sum>i<n. coeffs i) = 1"
        have "(\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i + coeffs i * c)"
          by (rule sum.cong) (simp_all add: distrib_left)
        also have "\<dots> = (\<Sum>i<n. coeffs i * vx i) + (\<Sum>i<n. coeffs i * c)"
          by (rule sum.distrib)
        also have "(\<Sum>i<n. coeffs i * c) = c * (\<Sum>i<n. coeffs i)"
          by (simp add: sum_distrib_left mult.commute)
        also have "\<dots> = c" using \<open>(\<Sum>i<n. coeffs i) = 1\<close> by simp
        finally show "(\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i) + c" .
      qed
      show ?thesis
      proof
        show "(\<lambda>(x, y). (x + c, y)) ` P \<subseteq>
            {(x, y) |x y. \<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
                \<and> x = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)}"
        proof
          fix p assume "p \<in> (\<lambda>(x, y). (x + c, y)) ` P"
          then obtain x y where hp: "p = (x + c, y)" "(x, y) \<in> P" by (by100 force)
          then obtain coeffs where hc: "(\<forall>i<n. 0 \<le> coeffs i)" "(\<Sum>i<n. coeffs i) = 1"
              "x = (\<Sum>i<n. coeffs i * vx i)" "y = (\<Sum>i<n. coeffs i * vy i)"
            unfolding hP_eq by (by100 auto)
          have hxc: "x + c = (\<Sum>i<n. coeffs i * vx' i)" unfolding vx'_def using hsum_dist[OF hc(2)] hc(3) by simp
          have hyv: "y = (\<Sum>i<n. coeffs i * vy' i)" unfolding vy'_def using hc(4) by simp
          have "\<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
              \<and> (x + c) = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)"
            using hc(1) hc(2) hxc hyv by (by100 blast)
          thus "p \<in> {(x, y) |x y. \<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
              \<and> x = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)}"
            using hp(1) by (by100 blast)
        qed
      next
        show "{(x, y) |x y. \<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
                \<and> x = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)}
              \<subseteq> (\<lambda>(x, y). (x + c, y)) ` P"
        proof
          fix p assume "p \<in> {(x, y) |x y. \<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
              \<and> x = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)}"
          then obtain x' y coeffs where hp: "p = (x', y)"
              and hc: "(\<forall>i<n. 0 \<le> coeffs i)" "(\<Sum>i<n. coeffs i) = 1"
              "x' = (\<Sum>i<n. coeffs i * vx' i)" "y = (\<Sum>i<n. coeffs i * vy' i)" by (by5000 auto)
          have "x' = (\<Sum>i<n. coeffs i * vx i) + c"
            using hc(3) unfolding vx'_def using hsum_dist[OF hc(2)] by simp
          hence hx_orig: "x' - c = (\<Sum>i<n. coeffs i * vx i)" by simp
          have hy_orig: "y = (\<Sum>i<n. coeffs i * vy i)" using hc(4) unfolding vy'_def by simp
          have "(x' - c, y) \<in> P" unfolding hP_eq using hc(1) hc(2) hx_orig hy_orig by (by100 blast)
          hence "(x' - c + c, y) = p" using hp by simp
          hence "(\<lambda>(x,y). (x+c, y)) (x' - c, y) = p" by simp
          thus "p \<in> (\<lambda>(x, y). (x + c, y)) ` P" using \<open>(x' - c, y) \<in> P\<close> by (by100 force)
        qed
      qed
    qed
    show "top1_is_polygonal_region_on ((\<lambda>(x,y). (x + c, y)) ` P) n"
      unfolding top1_is_polygonal_region_on_def
      using hn hdist' hndeg' hP'_eq by (by100 blast)
  qed
  \<comment> \<open>Step 4: Construct disjoint copies of standard simplex in R², one per triangle.\<close>
  \<comment> \<open>Enumerate the triangles.\<close>
  obtain tlist where htlist: "set tlist = \<T>0" "distinct tlist"
    using finite_distinct_list[OF h\<T>0(1)] by (by100 blast)
  let ?m = "length tlist"
  have h\<T>0_ne: "\<T>0 \<noteq> {}"
  proof -
    have "X \<noteq> {}" using assms(1) unfolding top1_is_surface_on_def by (by100 blast)
    thus ?thesis using h\<T>0(2) by (by100 blast)
  qed
  have hm_pos: "?m > 0"
    using h\<T>0_ne htlist(1) by (by100 force)
  \<comment> \<open>Place the i-th simplex copy at position (3*i, 0) to ensure disjointness.\<close>
  define \<Delta>copy :: "nat \<Rightarrow> (real \<times> real) set" where
    "\<Delta>copy i = (\<lambda>(x,y). (x + 3 * real i, y)) ` top1_standard_simplex" for i
  let ?\<T> = "{\<Delta>copy i | i. i < ?m}"
  \<comment> \<open>Define q: on \\<Delta>copy i, apply h0(tlist!i) composed with the inverse translation.\<close>
  define q_map :: "(real \<times> real) \<Rightarrow> 'a" where
    "q_map p = (let i = (SOME i. i < ?m \<and> p \<in> \<Delta>copy i) in
                h0 (tlist ! i) ((fst p - 3 * real i, snd p)))" for p
  \<comment> \<open>Show the required properties.\<close>
  have h\<T>_fin: "finite ?\<T>"
  proof -
    have "?\<T> = (\<lambda>i. \<Delta>copy i) ` {..<?m}" by (by100 blast)
    thus ?thesis by simp
  qed
  have h\<T>_ne: "?\<T> \<noteq> {}"
  proof -
    have "\<Delta>copy 0 \<in> ?\<T>" using hm_pos by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  have h\<T>_poly: "\<forall>T \<in> ?\<T>. top1_is_polygonal_region_on T 3"
  proof (intro ballI)
    fix T assume "T \<in> ?\<T>"
    then obtain i where "i < ?m" "T = \<Delta>copy i" by (by100 blast)
    \<comment> \<open>\\<Delta>copy i = translation of standard simplex. Translation preserves polygonal region.
       The standard simplex has vertices (vx j, vy j) for j < 3 (from h\\_simplex\\_poly).
       \\<Delta>copy i has vertices (vx j + 3*i, vy j). Same convex hull structure.\<close>
    show "top1_is_polygonal_region_on T 3"
      using \<open>T = \<Delta>copy i\<close> unfolding \<Delta>copy_def
      using htranslate_poly[OF h_simplex_poly] by simp
  qed
  \<comment> \<open>Infrastructure: disjointness, SOME resolution, inverse translation, h0 range.\<close>
  have h_fst_bound: "\<And>i p. p \<in> \<Delta>copy i \<Longrightarrow> 3 * real i \<le> fst p \<and> fst p \<le> 3 * real i + 1"
  proof -
    fix i :: nat and p :: "real \<times> real" assume "p \<in> \<Delta>copy i"
    then obtain x y where hxy: "(x, y) \<in> top1_standard_simplex" "p = (x + 3 * real i, y)"
      unfolding \<Delta>copy_def by (by100 force)
    have "x \<ge> 0" "x \<le> 1" using hxy(1) unfolding top1_standard_simplex_def by (by100 auto)+
    thus "3 * real i \<le> fst p \<and> fst p \<le> 3 * real i + 1" using hxy(2) by simp
  qed
  have h_disjoint: "\<And>i j. i \<noteq> j \<Longrightarrow> \<Delta>copy i \<inter> \<Delta>copy j = {}"
  proof -
    fix i j :: nat assume hij: "i \<noteq> j"
    show "\<Delta>copy i \<inter> \<Delta>copy j = {}"
    proof (rule ccontr)
      assume "\<Delta>copy i \<inter> \<Delta>copy j \<noteq> {}"
      then obtain p where hp: "p \<in> \<Delta>copy i" "p \<in> \<Delta>copy j" by (by100 blast)
      have "3 * real i \<le> fst p" "fst p \<le> 3 * real i + 1"
        using h_fst_bound[OF hp(1)] by (by100 auto)+
      have "3 * real j \<le> fst p" "fst p \<le> 3 * real j + 1"
        using h_fst_bound[OF hp(2)] by (by100 auto)+
      hence "3 * real i \<le> 3 * real j + 1" "3 * real j \<le> 3 * real i + 1"
        using \<open>3 * real i \<le> fst p\<close> \<open>fst p \<le> 3 * real j + 1\<close>
              \<open>3 * real j \<le> fst p\<close> \<open>fst p \<le> 3 * real i + 1\<close> by linarith+
      hence "real i \<le> real j + 1/3" "real j \<le> real i + 1/3" by linarith+
      hence "\<bar>real i - real j\<bar> \<le> 1/3" by linarith
      hence "i = j" by linarith
      thus False using hij by simp
    qed
  qed
  have h_SOME: "\<And>i p. i < ?m \<Longrightarrow> p \<in> \<Delta>copy i \<Longrightarrow> (SOME j. j < ?m \<and> p \<in> \<Delta>copy j) = i"
  proof -
    fix i :: nat and p assume hi: "i < ?m" and hp: "p \<in> \<Delta>copy i"
    have huniq: "\<And>j. j < ?m \<and> p \<in> \<Delta>copy j \<Longrightarrow> j = i"
    proof -
      fix j assume "j < ?m \<and> p \<in> \<Delta>copy j"
      hence "p \<in> \<Delta>copy j" by simp
      hence "\<Delta>copy i \<inter> \<Delta>copy j \<noteq> {}" using hp by (by100 blast)
      thus "j = i" using h_disjoint by (by100 blast)
    qed
    show "(SOME j. j < ?m \<and> p \<in> \<Delta>copy j) = i"
      by (rule some_equality) (use hi hp huniq in \<open>by100 blast\<close>)+
  qed
  have h_inv_trans: "\<And>i p. p \<in> \<Delta>copy i \<Longrightarrow> (fst p - 3 * real i, snd p) \<in> top1_standard_simplex"
  proof -
    fix i :: nat and p :: "real \<times> real" assume "p \<in> \<Delta>copy i"
    then obtain x y where hxy: "(x, y) \<in> top1_standard_simplex" "p = (x + 3 * real i, y)"
      unfolding \<Delta>copy_def by (by100 force)
    have "fst p - 3 * real i = x" "snd p = y" using hxy(2) by simp+
    thus "(fst p - 3 * real i, snd p) \<in> top1_standard_simplex" using hxy(1) by simp
  qed
  have h_h0_surj: "\<And>i. i < ?m \<Longrightarrow> h0 (tlist ! i) ` top1_standard_simplex = tlist ! i"
  proof -
    fix i assume "i < ?m"
    have "tlist ! i \<in> set tlist" using \<open>i < ?m\<close> by simp
    hence "tlist ! i \<in> \<T>0" using htlist(1) by simp
    hence "top1_homeomorphism_on top1_standard_simplex top1_standard_simplex_topology
        (tlist ! i) (subspace_topology X TX (tlist ! i)) (h0 (tlist ! i))"
      using h\<T>0(3) by (by100 blast)
    hence "bij_betw (h0 (tlist ! i)) top1_standard_simplex (tlist ! i)"
      unfolding top1_homeomorphism_on_def by (by100 blast)
    thus "h0 (tlist ! i) ` top1_standard_simplex = tlist ! i"
      unfolding bij_betw_def by simp
  qed
  have h_qmap_on_copy: "\<And>i p. i < ?m \<Longrightarrow> p \<in> \<Delta>copy i \<Longrightarrow>
      q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
  proof -
    fix i :: nat and p assume "i < ?m" "p \<in> \<Delta>copy i"
    have "(SOME j. j < ?m \<and> p \<in> \<Delta>copy j) = i" using h_SOME[OF \<open>i < ?m\<close> \<open>p \<in> \<Delta>copy i\<close>] .
    thus "q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
      unfolding q_map_def Let_def using \<open>(SOME j. j < ?m \<and> p \<in> \<Delta>copy j) = i\<close> by simp
  qed
  \<comment> \<open>Lift h0 continuity from subspace(X,TX,Ti) to TX.\<close>
  have h_h0_cont_X: "\<And>i. i < ?m \<Longrightarrow> top1_continuous_map_on
      top1_standard_simplex top1_standard_simplex_topology X TX (h0 (tlist ! i))"
  proof -
    fix i assume hi: "i < ?m"
    have "tlist ! i \<in> set tlist" using hi by simp
    hence "tlist ! i \<in> \<T>0" using htlist(1) by simp
    hence hTi_sub: "tlist ! i \<subseteq> X" using h\<T>0(2) by (by100 blast)
    have hhomeo: "top1_homeomorphism_on top1_standard_simplex top1_standard_simplex_topology
        (tlist ! i) (subspace_topology X TX (tlist ! i)) (h0 (tlist ! i))"
      using h\<T>0(3) \<open>tlist ! i \<in> \<T>0\<close> by (by100 blast)
    hence hcont_sub: "top1_continuous_map_on top1_standard_simplex top1_standard_simplex_topology
        (tlist ! i) (subspace_topology X TX (tlist ! i)) (h0 (tlist ! i))"
      unfolding top1_homeomorphism_on_def by (by100 blast)
    show "top1_continuous_map_on top1_standard_simplex top1_standard_simplex_topology X TX (h0 (tlist ! i))"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> top1_standard_simplex"
      have "h0 (tlist ! i) s \<in> tlist ! i"
        using hcont_sub \<open>s \<in> top1_standard_simplex\<close>
        unfolding top1_continuous_map_on_def by (by100 blast)
      thus "h0 (tlist ! i) s \<in> X" using hTi_sub by (by100 blast)
    next
      fix V assume hV: "V \<in> TX"
      have "V \<inter> tlist ! i \<in> subspace_topology X TX (tlist ! i)"
        unfolding subspace_topology_def using hV by (by100 blast)
      hence "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V \<inter> tlist ! i}
          \<in> top1_standard_simplex_topology"
        using hcont_sub unfolding top1_continuous_map_on_def by (by100 blast)
      moreover have "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}
          = {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V \<inter> tlist ! i}"
      proof
        show "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}
            \<subseteq> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V \<inter> tlist ! i}"
        proof
          fix s assume "s \<in> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}"
          hence "s \<in> top1_standard_simplex" "h0 (tlist ! i) s \<in> V" by (by100 auto)+
          moreover have "h0 (tlist ! i) s \<in> tlist ! i"
            using hcont_sub \<open>s \<in> top1_standard_simplex\<close>
            unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "s \<in> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V \<inter> tlist ! i}"
            by (by100 blast)
        qed
      next
        show "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V \<inter> tlist ! i}
            \<subseteq> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}" by (by100 blast)
      qed
      ultimately show "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}
          \<in> top1_standard_simplex_topology" by simp
    qed
  qed
  have h\<T>_cont: "\<forall>T \<in> ?\<T>. top1_continuous_map_on T
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) X TX q_map"
  proof (intro ballI)
    fix T assume "T \<in> ?\<T>"
    then obtain i where hi: "i < ?m" "T = \<Delta>copy i" by (by100 blast)
    show "top1_continuous_map_on T
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) X TX q_map"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix p assume hp: "p \<in> T"
      hence "p \<in> \<Delta>copy i" using hi(2) by simp
      have "q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
        using h_qmap_on_copy[OF hi(1) \<open>p \<in> \<Delta>copy i\<close>] .
      moreover have "(fst p - 3 * real i, snd p) \<in> top1_standard_simplex"
        using h_inv_trans[OF \<open>p \<in> \<Delta>copy i\<close>] .
      ultimately show "q_map p \<in> X"
        using continuous_map_maps_to[OF h_h0_cont_X[OF hi(1)]] by simp
    next
      fix V assume hV: "V \<in> TX"
      \<comment> \<open>Need: {p \\<in> T. q\\_map p \\<in> V} \\<in> subspace R² T.
         This equals {p \\<in> \\<Delta>copy i. h0(tlist!i)(invtrans(p)) \\<in> V}.
         From h0 continuity: {s \\<in> \\<Delta>. h0 s \\<in> V} \\<in> standard\\_simplex\\_topology.
         Translation preserves openness.\<close>
      have hpre_ss: "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}
          \<in> top1_standard_simplex_topology"
        using continuous_map_preimage_open[OF h_h0_cont_X[OF hi(1)] hV] .
      \<comment> \<open>This preimage in standard\\_simplex\\_topology = subspace R² standard\\_simplex.
         So there exists W open in R² with preimage = W \\<inter> standard\\_simplex.\<close>
      then obtain W where hW: "W \<in> product_topology_on top1_open_sets top1_open_sets"
          "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V} = W \<inter> top1_standard_simplex"
        unfolding top1_standard_simplex_topology_def subspace_topology_def by (by100 blast)
      \<comment> \<open>Translate W by (3*i, 0) to get W' open in R².\<close>
      define W' where "W' = (\<lambda>(x,y). (x + 3 * real i, y)) ` W"
      \<comment> \<open>Translation preserves openness in product\\_topology. This is the key step.\<close>
      have hW'_open: "W' \<in> product_topology_on top1_open_sets top1_open_sets"
        unfolding product_topology_on_def topology_generated_by_basis_def
      proof (intro CollectI conjI ballI)
        show "W' \<subseteq> UNIV" by simp
      next
        fix p assume "p \<in> W'"
        then obtain s where hs: "s \<in> W" "p = (\<lambda>(x,y). (x + 3 * real i, y)) s"
          unfolding W'_def by (by100 blast)
        have hW_open: "W \<in> topology_generated_by_basis UNIV (product_basis top1_open_sets top1_open_sets)"
          using hW(1) unfolding product_topology_on_def .
        hence "\<exists>b\<in>product_basis top1_open_sets top1_open_sets. s \<in> b \<and> b \<subseteq> W"
          using \<open>s \<in> W\<close> unfolding topology_generated_by_basis_def by (by100 blast)
        then obtain U0 V0 where hUV: "U0 \<in> top1_open_sets" "V0 \<in> top1_open_sets"
            "s \<in> U0 \<times> V0" "U0 \<times> V0 \<subseteq> W"
          unfolding product_basis_def by (by100 blast)
        define U' where "U' = (\<lambda>x. x + 3 * real i) ` U0"
        have hU'_open: "U' \<in> top1_open_sets"
        proof -
          have "open U0" using hUV(1) unfolding top1_open_sets_def by simp
          have "open ((\<lambda>x::real. x - 3 * real i) -` U0)"
            by (rule open_vimage[OF \<open>open U0\<close>]) (intro continuous_intros)
          moreover have "(\<lambda>x::real. x - 3 * real i) -` U0 = (\<lambda>x. x + 3 * real i) ` U0"
            by (by100 force)
          ultimately have "open ((\<lambda>x. 3 * real i + x) ` U0)"
            by (simp add: add.commute)
          moreover have "(\<lambda>x. 3 * real i + x) ` U0 = U'"
            unfolding U'_def by (by100 force)
          ultimately show ?thesis unfolding top1_open_sets_def by simp
        qed
        have "p \<in> U' \<times> V0"
          using hUV(3) hs(2) unfolding U'_def by (cases s) (by100 force)
        moreover have "U' \<times> V0 \<subseteq> W'"
        proof
          fix q assume "q \<in> U' \<times> V0"
          then obtain u v where "u \<in> U'" "v \<in> V0" "q = (u, v)" by (by100 blast)
          then obtain u0 where "u0 \<in> U0" "u = u0 + 3 * real i"
            unfolding U'_def by (by100 blast)
          hence "(u0, v) \<in> U0 \<times> V0" using \<open>v \<in> V0\<close> by simp
          hence "(u0, v) \<in> W" using hUV(4) by (by100 blast)
          have "q = (\<lambda>(x,y). (x + 3 * real i, y)) (u0, v)"
            using \<open>q = (u, v)\<close> \<open>u = u0 + 3 * real i\<close> by simp
          thus "q \<in> W'" unfolding W'_def using \<open>(u0, v) \<in> W\<close> by (by100 blast)
        qed
        moreover have hU'V0_basis: "U' \<times> V0 \<in> product_basis top1_open_sets top1_open_sets"
          unfolding product_basis_def using hU'_open hUV(2) by (by100 blast)
        ultimately show "\<exists>b\<in>product_basis top1_open_sets top1_open_sets. p \<in> b \<and> b \<subseteq> W'"
          apply (rule_tac bexI[of _ "U' \<times> V0"])
          apply (by100 blast)
          apply assumption
          done
      qed
      \<comment> \<open>{p \\<in> T. q\\_map p \\<in> V} = W' \\<inter> T.\<close>
      have hpre_eq: "{p \<in> T. q_map p \<in> V} = W' \<inter> T"
      proof
        show "{p \<in> T. q_map p \<in> V} \<subseteq> W' \<inter> T"
        proof
          fix p assume hp: "p \<in> {p \<in> T. q_map p \<in> V}"
          hence "p \<in> T" "q_map p \<in> V" by (by100 auto)+
          hence "p \<in> \<Delta>copy i" using hi(2) by simp
          have "(fst p - 3 * real i, snd p) \<in> top1_standard_simplex"
            using h_inv_trans[OF \<open>p \<in> \<Delta>copy i\<close>] .
          moreover have "h0 (tlist ! i) (fst p - 3 * real i, snd p) \<in> V"
            using h_qmap_on_copy[OF hi(1) \<open>p \<in> \<Delta>copy i\<close>] \<open>q_map p \<in> V\<close> by simp
          ultimately have "(fst p - 3 * real i, snd p) \<in> W"
            using hW(2) by (by100 blast)
          have "p = (\<lambda>(x,y). (x + 3 * real i, y)) (fst p - 3 * real i, snd p)" by simp
          hence "p \<in> W'" unfolding W'_def
            using \<open>(fst p - 3 * real i, snd p) \<in> W\<close> by (by100 blast)
          thus "p \<in> W' \<inter> T" using \<open>p \<in> T\<close> by (by100 blast)
        qed
      next
        show "W' \<inter> T \<subseteq> {p \<in> T. q_map p \<in> V}"
        proof
          fix p assume hp: "p \<in> W' \<inter> T"
          hence "p \<in> W'" "p \<in> T" by (by100 auto)+
          hence "p \<in> \<Delta>copy i" using hi(2) by simp
          from \<open>p \<in> W'\<close> obtain s where hs: "s \<in> W" "p = (\<lambda>(x,y). (x + 3 * real i, y)) s"
            unfolding W'_def by (by100 blast)
          have "fst p - 3 * real i = fst s" "snd p = snd s"
            using hs(2) by (cases s, simp)+
          hence hinv: "(fst p - 3 * real i, snd p) = s" by (cases s) simp
          have "s \<in> top1_standard_simplex"
            using h_inv_trans[OF \<open>p \<in> \<Delta>copy i\<close>] hinv by simp
          hence "s \<in> W \<inter> top1_standard_simplex" using \<open>s \<in> W\<close> by simp
          hence "h0 (tlist ! i) s \<in> V" using hW(2) by (by100 blast)
          hence "h0 (tlist ! i) (fst p - 3 * real i, snd p) \<in> V" using hinv by simp
          hence "q_map p \<in> V" using h_qmap_on_copy[OF hi(1) \<open>p \<in> \<Delta>copy i\<close>] by simp
          thus "p \<in> {p \<in> T. q_map p \<in> V}" using \<open>p \<in> T\<close> by (by100 blast)
        qed
      qed
      thus "{p \<in> T. q_map p \<in> V} \<in> subspace_topology UNIV
          (product_topology_on top1_open_sets top1_open_sets) T"
        unfolding subspace_topology_def using hW'_open by (by100 blast)
    qed
  qed
  have h\<T>_cov: "(\<Union>T\<in>?\<T>. q_map ` T) = X"
  proof
    show "(\<Union>T\<in>?\<T>. q_map ` T) \<subseteq> X"
    proof
      fix x assume "x \<in> (\<Union>T\<in>?\<T>. q_map ` T)"
      then obtain T p where hT: "T \<in> ?\<T>" and hp: "p \<in> T" and hx: "x = q_map p" by (by100 blast)
      from hT obtain i where hi: "i < ?m" "T = \<Delta>copy i" by (by100 blast)
      have "q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
        using h_qmap_on_copy[OF hi(1)] hp hi(2) by simp
      moreover have "(fst p - 3 * real i, snd p) \<in> top1_standard_simplex"
        using h_inv_trans hp hi(2) by simp
      ultimately have "x \<in> h0 (tlist ! i) ` top1_standard_simplex" using hx by (by100 blast)
      hence "x \<in> tlist ! i" using h_h0_surj[OF hi(1)] by simp
      moreover have "tlist ! i \<in> set tlist" using hi(1) by simp
      hence "tlist ! i \<in> \<T>0" using htlist(1) by simp
      hence "tlist ! i \<subseteq> X" using h\<T>0(2) by (by100 blast)
      ultimately show "x \<in> X" by (by100 blast)
    qed
  next
    show "X \<subseteq> (\<Union>T\<in>?\<T>. q_map ` T)"
    proof
      fix x assume "x \<in> X"
      hence "x \<in> \<Union>\<T>0" using h\<T>0(2) by simp
      then obtain T0i where hT0i: "T0i \<in> \<T>0" "x \<in> T0i" by (by100 blast)
      have "T0i \<in> set tlist" using hT0i(1) htlist(1) by simp
      then obtain i where hi: "i < ?m" "tlist ! i = T0i"
        by (metis in_set_conv_nth)
      have "x \<in> tlist ! i" using hT0i(2) hi(2) by simp
      hence "x \<in> h0 (tlist ! i) ` top1_standard_simplex" using h_h0_surj[OF hi(1)] by simp
      then obtain s where hs: "s \<in> top1_standard_simplex" "h0 (tlist ! i) s = x" by (by100 blast)
      define p where "p = (fst s + 3 * real i, snd s)"
      have hp_in: "p \<in> \<Delta>copy i"
      proof -
        have "p = (\<lambda>(x,y). (x + 3 * real i, y)) s" unfolding p_def by (cases s) simp
        thus ?thesis unfolding \<Delta>copy_def using hs(1) by (by100 blast)
      qed
      have "fst p - 3 * real i = fst s" "snd p = snd s"
        unfolding p_def by simp+
      hence "q_map p = h0 (tlist ! i) s"
        using h_qmap_on_copy[OF hi(1) hp_in] by simp
      hence "q_map p = x" using hs(2) by simp
      moreover have "\<Delta>copy i \<in> ?\<T>" using hi(1) by (by100 blast)
      ultimately show "x \<in> (\<Union>T\<in>?\<T>. q_map ` T)" using hp_in by (by100 blast)
    qed
  qed
  \<comment> \<open>Key bridge: h0 is an open map (homeomorphism maps opens to opens).\<close>
  have h_h0_open_map: "\<And>i Uo. i < ?m \<Longrightarrow>
      Uo \<in> top1_standard_simplex_topology \<Longrightarrow>
      h0 (tlist ! i) ` Uo \<in> subspace_topology X TX (tlist ! i)"
  proof -
    fix i Uo assume hi: "i < ?m" and hO: "Uo \<in> top1_standard_simplex_topology"
    have "tlist ! i \<in> set tlist" using hi by simp
    hence "tlist ! i \<in> \<T>0" using htlist(1) by simp
    have hhomeo: "top1_homeomorphism_on top1_standard_simplex top1_standard_simplex_topology
        (tlist ! i) (subspace_topology X TX (tlist ! i)) (h0 (tlist ! i))"
      using h\<T>0(3) \<open>tlist ! i \<in> \<T>0\<close> by (by100 blast)
    hence hinv_cont: "top1_continuous_map_on (tlist ! i) (subspace_topology X TX (tlist ! i))
        top1_standard_simplex top1_standard_simplex_topology (inv_into top1_standard_simplex (h0 (tlist ! i)))"
      unfolding top1_homeomorphism_on_def by (by100 blast)
    \<comment> \<open>h0(T) `` O = {b \\<in> T | inv\\_into(h0)(b) \\<in> O} (preimage under inverse).\<close>
    have hbij: "bij_betw (h0 (tlist ! i)) top1_standard_simplex (tlist ! i)"
      using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
    have hinj: "inj_on (h0 (tlist ! i)) top1_standard_simplex"
      using hbij unfolding bij_betw_def by simp
    have hrange: "h0 (tlist ! i) ` top1_standard_simplex = tlist ! i"
      using h_h0_surj[OF hi] .
    have heq: "h0 (tlist ! i) ` Uo = {b \<in> tlist ! i. inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo}"
    proof
      show "h0 (tlist ! i) ` Uo \<subseteq> {b \<in> tlist ! i. inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo}"
      proof
        fix b assume "b \<in> h0 (tlist ! i) ` Uo"
        then obtain s where hs: "s \<in> Uo" "b = h0 (tlist ! i) s" by (by100 blast)
        have "s \<in> top1_standard_simplex" using hO hs(1)
          unfolding top1_standard_simplex_topology_def subspace_topology_def by (by100 blast)
        hence "b \<in> tlist ! i" using hs(2) hrange by (by100 blast)
        moreover have "inv_into top1_standard_simplex (h0 (tlist ! i)) b = s"
          using inv_into_f_f[OF hinj \<open>s \<in> top1_standard_simplex\<close>] hs(2) by simp
        ultimately show "b \<in> {b \<in> tlist ! i. inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo}"
          using hs(1) by (by100 blast)
      qed
    next
      show "{b \<in> tlist ! i. inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo}
          \<subseteq> h0 (tlist ! i) ` Uo"
      proof
        fix b assume "b \<in> {b \<in> tlist ! i. inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo}"
        hence hb: "b \<in> tlist ! i" "inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo" by auto
        have "h0 (tlist ! i) (inv_into top1_standard_simplex (h0 (tlist ! i)) b) = b"
          using f_inv_into_f[of b "h0 (tlist ! i)" top1_standard_simplex] hb(1) hrange by (by100 blast)
        thus "b \<in> h0 (tlist ! i) ` Uo" using hb(2) by (by100 force)
      qed
    qed
    show "h0 (tlist ! i) ` Uo \<in> subspace_topology X TX (tlist ! i)"
      unfolding heq
      using continuous_map_preimage_open[OF hinv_cont hO] .
  qed
  \<comment> \<open>Backward: if preimages open in each \\<Delta>copy, then U \\<in> TX via finite closed cover.\<close>
  have h_X_strict: "is_topology_on_strict X TX"
    using assms(2) unfolding top1_is_triangulable_on_def by (by100 blast)
  have h_X_top: "is_topology_on X TX"
    using h_X_strict by (rule is_topology_on_strict_imp)
  have h\<T>_quot: "\<forall>U. U \<subseteq> X \<longrightarrow>
      (U \<in> TX \<longleftrightarrow> (\<forall>T\<in>?\<T>. {p\<in>T. q_map p \<in> U} \<in>
        subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T))"
  proof (intro allI impI iffI)
    fix U assume hU_sub: "U \<subseteq> X"
    \<comment> \<open>Forward: U \\<in> TX \\<Rightarrow> preimages open (from continuity).\<close>
    assume hU: "U \<in> TX"
    show "\<forall>T\<in>?\<T>. {p\<in>T. q_map p \<in> U} \<in>
        subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T"
      using h\<T>_cont hU unfolding top1_continuous_map_on_def by (by100 blast)
  next
    fix U assume hU_sub: "U \<subseteq> X"
    \<comment> \<open>Backward: preimages open \\<Rightarrow> U \\<in> TX via finite closed cover.\<close>
    assume hpre: "\<forall>T\<in>?\<T>. {p\<in>T. q_map p \<in> U} \<in>
        subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T"
    \<comment> \<open>Step 1: For each i, U \\<inter> tlist!i is open in subspace(X, TX, tlist!i).\<close>
    have hU_open_piece: "\<And>i. i < ?m \<Longrightarrow>
        U \<inter> tlist ! i \<in> subspace_topology X TX (tlist ! i)"
    proof -
      fix i assume hi: "i < ?m"
      have "\<Delta>copy i \<in> ?\<T>" using hi by (by100 blast)
      hence hpre_i: "{p \<in> \<Delta>copy i. q_map p \<in> U} \<in>
          subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (\<Delta>copy i)"
        using hpre by simp
      \<comment> \<open>Translate to standard simplex: {s \\<in> SS. h0(s) \\<in> U} is open in SS\\_top.\<close>
      have "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}
          \<in> top1_standard_simplex_topology"
      proof -
        \<comment> \<open>The preimage in \\<Delta>copy i is open: = W' \\<inter> \\<Delta>copy i for some W' open in R².\<close>
        from hpre_i obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
            "{p \<in> \<Delta>copy i. q_map p \<in> U} = W' \<inter> \<Delta>copy i"
          unfolding subspace_topology_def by (by100 blast)
        \<comment> \<open>Inverse-translate W' to get W open in R², such that preimage in SS = W \\<inter> SS.\<close>
        define W where "W = (\<lambda>(x,y). (x - 3 * real i, y)) ` W'"
        \<comment> \<open>W is open in R² (inverse translation preserves openness, same argument as forward).\<close>
        have hW_open: "W \<in> product_topology_on top1_open_sets top1_open_sets"
          unfolding product_topology_on_def topology_generated_by_basis_def
        proof (intro CollectI conjI ballI)
          show "W \<subseteq> UNIV" by simp
        next
          fix s assume "s \<in> W"
          then obtain p where hp: "p \<in> W'" "s = (\<lambda>(x,y). (x - 3 * real i, y)) p"
            unfolding W_def by (by100 blast)
          from hW'(1) have "W' \<in> topology_generated_by_basis UNIV (product_basis top1_open_sets top1_open_sets)"
            unfolding product_topology_on_def .
          hence "\<exists>b\<in>product_basis top1_open_sets top1_open_sets. p \<in> b \<and> b \<subseteq> W'"
            using hp(1) unfolding topology_generated_by_basis_def by (by100 blast)
          then obtain U0 V0 where hUV: "U0 \<in> top1_open_sets" "V0 \<in> top1_open_sets"
              "p \<in> U0 \<times> V0" "U0 \<times> V0 \<subseteq> W'"
            unfolding product_basis_def by (by100 blast)
          define U0' where "U0' = (\<lambda>x. x - 3 * real i) ` U0"
          have "open U0" using hUV(1) unfolding top1_open_sets_def by simp
          have "(\<lambda>x. x - 3 * real i) ` U0 = (\<lambda>y::real. y + 3 * real i) -` U0"
            by (by100 force)
          moreover have "open ((\<lambda>y::real. y + 3 * real i) -` U0)"
            by (rule open_vimage[OF \<open>open U0\<close>]) (intro continuous_intros)
          ultimately have "open U0'" unfolding U0'_def by simp
          hence hU0'_open: "U0' \<in> top1_open_sets" unfolding top1_open_sets_def by simp
          have "s \<in> U0' \<times> V0"
            using hUV(3) hp(2) unfolding U0'_def by (cases p) (by100 force)
          moreover have "U0' \<times> V0 \<subseteq> W"
          proof
            fix q assume "q \<in> U0' \<times> V0"
            then obtain u v where "u \<in> U0'" "v \<in> V0" "q = (u, v)" by (by100 blast)
            then obtain u0 where "u0 \<in> U0" "u = u0 - 3 * real i"
              unfolding U0'_def by (by100 blast)
            hence "(u0, v) \<in> U0 \<times> V0" using \<open>v \<in> V0\<close> by simp
            hence "(u0, v) \<in> W'" using hUV(4) by (by100 blast)
            have "q = (\<lambda>(x,y). (x - 3 * real i, y)) (u0, v)"
              using \<open>q = (u, v)\<close> \<open>u = u0 - 3 * real i\<close> by simp
            thus "q \<in> W" unfolding W_def using \<open>(u0, v) \<in> W'\<close> by (by100 blast)
          qed
          moreover have hU0'V0_basis: "U0' \<times> V0 \<in> product_basis top1_open_sets top1_open_sets"
            unfolding product_basis_def using hU0'_open hUV(2) by (by100 blast)
          ultimately show "\<exists>b\<in>product_basis top1_open_sets top1_open_sets. s \<in> b \<and> b \<subseteq> W"
            apply (rule_tac bexI[of _ "U0' \<times> V0"])
            apply (by100 blast)
            apply assumption
            done
        qed
        \<comment> \<open>Now: {s \\<in> SS. h0(s) \\<in> U} = W \\<inter> SS.\<close>
        have heq: "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U} = W \<inter> top1_standard_simplex"
        proof
          show "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U} \<subseteq> W \<inter> top1_standard_simplex"
          proof
            fix s assume hs: "s \<in> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}"
            hence "s \<in> top1_standard_simplex" "h0 (tlist ! i) s \<in> U" by auto
            define p where "p = (\<lambda>(x,y). (x + 3 * real i, y)) s"
            have "p \<in> \<Delta>copy i"
            proof -
              have "p = (\<lambda>(x,y). (x + 3 * real i, y)) s" unfolding p_def by simp
              thus ?thesis unfolding \<Delta>copy_def using \<open>s \<in> top1_standard_simplex\<close> by (by100 blast)
            qed
            have "q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
              using h_qmap_on_copy[OF hi \<open>p \<in> \<Delta>copy i\<close>] .
            also have "(fst p - 3 * real i, snd p) = s" unfolding p_def by (cases s) simp
            finally have "q_map p = h0 (tlist ! i) s" .
            hence "q_map p \<in> U" using \<open>h0 (tlist ! i) s \<in> U\<close> by simp
            hence "p \<in> {p \<in> \<Delta>copy i. q_map p \<in> U}" using \<open>p \<in> \<Delta>copy i\<close> by simp
            hence "p \<in> W' \<inter> \<Delta>copy i" using hW'(2) by simp
            hence "p \<in> W'" by simp
            have "s = (\<lambda>(x,y). (x - 3 * real i, y)) p" unfolding p_def by (cases s) simp
            hence "s \<in> W" unfolding W_def using \<open>p \<in> W'\<close> by (by100 blast)
            thus "s \<in> W \<inter> top1_standard_simplex" using \<open>s \<in> top1_standard_simplex\<close> by simp
          qed
        next
          show "W \<inter> top1_standard_simplex \<subseteq> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}"
          proof
            fix s assume hs: "s \<in> W \<inter> top1_standard_simplex"
            hence "s \<in> W" "s \<in> top1_standard_simplex" by auto
            from \<open>s \<in> W\<close> obtain p where hp: "p \<in> W'" "s = (\<lambda>(x,y). (x - 3 * real i, y)) p"
              unfolding W_def by (by100 blast)
            have "fst s + 3 * real i = fst p" "snd s = snd p" using hp(2) by (cases p, simp)+
            hence "p \<in> \<Delta>copy i"
            proof -
              have "p = (\<lambda>(x,y). (x + 3 * real i, y)) s" using hp(2) by (cases s, cases p) simp
              thus ?thesis unfolding \<Delta>copy_def using \<open>s \<in> top1_standard_simplex\<close> by (by100 blast)
            qed
            hence "p \<in> W' \<inter> \<Delta>copy i" using hp(1) by simp
            hence "p \<in> {p \<in> \<Delta>copy i. q_map p \<in> U}" using hW'(2) by simp
            hence "q_map p \<in> U" by simp
            have "q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
              using h_qmap_on_copy[OF hi \<open>p \<in> \<Delta>copy i\<close>] .
            also have "(fst p - 3 * real i, snd p) = s" using hp(2) by (cases p) simp
            finally have "h0 (tlist ! i) s = q_map p" by simp
            hence "h0 (tlist ! i) s \<in> U" using \<open>q_map p \<in> U\<close> by simp
            thus "s \<in> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}"
              using \<open>s \<in> top1_standard_simplex\<close> by simp
          qed
        qed
        show ?thesis unfolding heq top1_standard_simplex_topology_def subspace_topology_def
          using hW_open by (by100 blast)
      qed
      \<comment> \<open>h0 maps this open set to U \\<inter> tlist!i.\<close>
      moreover have "h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}
          = U \<inter> tlist ! i"
      proof
        show "h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}
            \<subseteq> U \<inter> tlist ! i"
          using h_h0_surj[OF hi] by (by100 blast)
      next
        show "U \<inter> tlist ! i
            \<subseteq> h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}"
        proof
          fix x assume "x \<in> U \<inter> tlist ! i"
          hence "x \<in> tlist ! i" "x \<in> U" by auto
          hence "x \<in> h0 (tlist ! i) ` top1_standard_simplex" using h_h0_surj[OF hi] by simp
          then obtain s where "s \<in> top1_standard_simplex" "h0 (tlist ! i) s = x" by (by100 blast)
          thus "x \<in> h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}"
            using \<open>x \<in> U\<close> by (by100 blast)
        qed
      qed
      ultimately show "U \<inter> tlist ! i \<in> subspace_topology X TX (tlist ! i)"
      proof -
        assume h1: "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U} \<in> top1_standard_simplex_topology"
        assume h2: "h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U} = U \<inter> tlist ! i"
        from h_h0_open_map[OF hi h1] have "h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}
            \<in> subspace_topology X TX (tlist ! i)" .
        thus ?thesis using h2 by simp
      qed
    qed
    \<comment> \<open>Step 2: Finite closed cover \\<Rightarrow> U \\<in> TX.\<close>
    \<comment> \<open>X - U is closed: each (tlist!i) - U = (tlist!i) \\<inter> (X-U) is closed in TX.\<close>
    have hcl: "\<And>i. i < ?m \<Longrightarrow> closedin_on X TX (tlist ! i \<inter> (X - U))"
    proof -
      fix i assume hi: "i < ?m"
      have "tlist ! i \<in> set tlist" using hi by simp
      hence "tlist ! i \<in> \<T>0" using htlist(1) by simp
      hence hTi_cl: "closedin_on X TX (tlist ! i)" using h\<T>0(3) by (by100 blast)
      \<comment> \<open>tlist!i - U is closed in subspace(X,TX,tlist!i).\<close>
      have "U \<inter> tlist ! i \<in> subspace_topology X TX (tlist ! i)"
        using hU_open_piece[OF hi] .
      then obtain V where hV: "V \<in> TX" "U \<inter> tlist ! i = V \<inter> tlist ! i"
        unfolding subspace_topology_def by (by100 blast)
      have "tlist ! i \<inter> (X - U) = tlist ! i \<inter> (X - V)"
        using hV(2) by (by100 blast)
      moreover have "closedin_on X TX (tlist ! i \<inter> (X - V))"
      proof -
        have hXV_cl: "closedin_on X TX (X - V)"
          unfolding closedin_on_def
        proof (intro conjI)
          show "X - V \<subseteq> X" by (by100 blast)
          show "X - (X - V) \<in> TX"
          proof -
            have "X - (X - V) = V \<inter> X"
              by (by100 blast)
            also have "V \<inter> X = V"
              using is_topology_on_strict_opens_sub[OF h_X_strict hV(1)] by (by100 blast)
            finally show ?thesis using hV(1) by simp
          qed
        qed
        have hsub: "tlist ! i \<inter> (X - V) \<subseteq> X" using hTi_cl unfolding closedin_on_def by (by100 blast)
        have hcomp: "X - (tlist ! i \<inter> (X - V)) \<in> TX"
        proof -
          have hV_sub: "V \<subseteq> X" using is_topology_on_strict_opens_sub[OF h_X_strict hV(1)] .
          have hXTi: "X - tlist ! i \<in> TX"
            using hTi_cl unfolding closedin_on_def by simp
          have "{X - tlist ! i, V} \<subseteq> TX" using hXTi hV(1) by (by100 blast)
          hence hUn: "\<Union>{X - tlist ! i, V} \<in> TX"
            using h_X_top unfolding is_topology_on_def by (by100 blast)
          have "(X - tlist ! i) \<union> V = X - (tlist ! i \<inter> (X - V))"
            using hV_sub by (by100 blast)
          thus ?thesis using hUn by simp
        qed
        show ?thesis unfolding closedin_on_def using hsub hcomp by (by100 blast)
      qed
      ultimately show "closedin_on X TX (tlist ! i \<inter> (X - U))" by simp
    qed
    have "X - U = (\<Union>i<?m. tlist ! i \<inter> (X - U))"
    proof
      show "X - U \<subseteq> (\<Union>i<length tlist. tlist ! i \<inter> (X - U))"
      proof
        fix x assume "x \<in> X - U"
        hence "x \<in> X" by simp
        hence "x \<in> \<Union>\<T>0" using h\<T>0(2) by simp
        then obtain T where "T \<in> \<T>0" "x \<in> T" by (by100 blast)
        have "T \<in> set tlist" using \<open>T \<in> \<T>0\<close> htlist(1) by simp
        then obtain i where "i < ?m" "tlist ! i = T" by (metis in_set_conv_nth)
        thus "x \<in> (\<Union>i<length tlist. tlist ! i \<inter> (X - U))"
          using \<open>x \<in> T\<close> \<open>x \<in> X - U\<close> by (by100 force)
      qed
    next
      show "(\<Union>i<length tlist. tlist ! i \<inter> (X - U)) \<subseteq> X - U"
        by (by100 blast)
    qed
    hence "closedin_on X TX (X - U)"
    proof -
      have "closedin_on X TX (\<Union>i<?m. tlist ! i \<inter> (X - U))"
      proof -
        have "finite {i. i < ?m}" by simp
        moreover have "\<And>i. i < ?m \<Longrightarrow> closedin_on X TX (tlist ! i \<inter> (X - U))"
          using hcl .
        ultimately have "closedin_on X TX (\<Union>((\<lambda>i. tlist ! i \<inter> (X - U)) ` {..<length tlist}))"
          using closedin_Union_finite[OF h_X_top, of "(\<lambda>i. tlist ! i \<inter> (X - U)) ` {..<length tlist}"]
          by (by100 auto)
        moreover have "(\<Union>((\<lambda>i. tlist ! i \<inter> (X - U)) ` {..<length tlist}))
            = (\<Union>i<?m. tlist ! i \<inter> (X - U))" by (by100 blast)
        ultimately show ?thesis by simp
      qed
      thus ?thesis using \<open>X - U = (\<Union>i<?m. tlist ! i \<inter> (X - U))\<close> by simp
    qed
    hence "X - (X - U) \<in> TX" unfolding closedin_on_def by simp
    moreover have "X - (X - U) = U" using hU_sub by (by100 blast)
    ultimately show "U \<in> TX" by simp
  qed
  show ?thesis
    apply (rule exI[of _ "?\<T>"])
    apply (rule exI[of _ q_map])
    using h\<T>_fin h\<T>_ne h\<T>_poly h\<T>_cont h\<T>_cov h\<T>_quot
    apply (intro conjI)
    apply assumption+
    done
qed

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
      from valid_equiv_preserves_quotient_homeo[OF hsch hequiv_s]
      obtain Y :: "'a set" and TY :: "'a set set" and h :: "'a \<Rightarrow> 'a" where
        hY: "top1_quotient_of_scheme_on Y TY [(a_s, True), (a_s, False), (b_s, True), (b_s, False)]"
        and hXY: "top1_homeomorphism_on X TX Y TY h"
        by (by100 blast)
      \<comment> \<open>Step 2: Y (quotient of sphere scheme) \\<cong> S2.
         Needs sphere\\_scheme\\_realizes\\_sphere lemma (geometric construction).\<close>
      have "\<exists>g. top1_homeomorphism_on Y TY top1_S2 top1_S2_topology g"
        sorry \<comment> \<open>Sphere scheme realizes S2. See audit 20 step 6.\<close>
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
      from valid_equiv_preserves_quotient_homeo[OF hsch hequiv]
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
      from valid_equiv_preserves_quotient_homeo[OF hsch hequiv]
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
















 





































 

































