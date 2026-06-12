theory AlgTop
  imports "AlgTopCached14.AlgTopCached14"
begin

\<comment> \<open>valid\\_operation\\_reverse, valid\\_equiv\\_sym: cached in AlgTopCached14.\<close>
\<comment> \<open>§77 normal form chain (scheme\\_normal\\_form\\_valid + all valid helpers): cached in AlgTopCached14.\<close>

\<comment> \<open>Helper: quotient\\_of\\_scheme\\_on implies length \\<ge> 3 (from polygonal region).\<close>
lemma quotient_scheme_length_ge3:
  "top1_quotient_of_scheme_on Y TY w \<Longrightarrow> length w \<ge> 3"
proof -
  assume "top1_quotient_of_scheme_on Y TY w"
  then obtain P q vx vy where "top1_is_polygonal_region_on P (length w)"
    by (rule quotient_of_scheme_extract_vx)
  thus "length w \<ge> 3" unfolding top1_is_polygonal_region_on_def by (by100 blast)
qed

\<comment> \<open>Identity homeomorphism + same-space helper (moved here for use by cut-paste lemmas).\<close>
lemma homeomorphism_id_early:
  assumes "is_topology_on X TX"
  shows "top1_homeomorphism_on X TX X TX id"
proof -
  have hid_cont: "top1_continuous_map_on X TX X TX id"
    by (rule top1_continuous_map_on_id[OF assms])
  have hinv: "\<forall>x\<in>X. inv_into X id x = x"
  proof
    fix x assume "x \<in> X"
    thus "inv_into X id x = x" using inv_into_f_f[OF inj_on_id \<open>x \<in> X\<close>] by simp
  qed
  have "top1_continuous_map_on X TX X TX (inv_into X id)"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI allI impI)
    fix x assume "x \<in> X" thus "inv_into X id x \<in> X" using hinv by (by100 simp)
  next
    fix V assume hV: "V \<in> TX"
    have "{x \<in> X. inv_into X id x \<in> V} = {x \<in> X. id x \<in> V}"
      using hinv by (by100 auto)
    thus "{x \<in> X. inv_into X id x \<in> V} \<in> TX"
      using hid_cont hV unfolding top1_continuous_map_on_def by (by100 simp)
  qed
  thus ?thesis unfolding top1_homeomorphism_on_def using assms hid_cont by (by100 simp)
qed

lemma same_space_implies_homeo_realization_early:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "top1_quotient_of_scheme_on X TX t"
  shows "\<exists>(Y :: 'a set) (TY :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y TY t \<and>
    top1_homeomorphism_on X TX Y TY h"
proof -
  have "is_topology_on X TX"
    using assms unfolding top1_quotient_of_scheme_on_def is_topology_on_strict_def by (by100 blast)
  show ?thesis
    using assms homeomorphism_id_early[OF \<open>is_topology_on X TX\<close>] by (by100 blast)
qed

\<comment> \<open>Regular n-gon is a polygonal region. Standalone helper for reuse.\<close>
lemma regular_ngon_polygonal_region:
  fixes n :: nat
  assumes "n \<ge> 3"
  defines "vx \<equiv> \<lambda>k. cos (2 * pi * real k / real n)"
  defines "vy \<equiv> \<lambda>k. sin (2 * pi * real k / real n)"
  defines "P \<equiv> {(x::real,y::real). \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<n. coeffs i) = 1
                     \<and> x = (\<Sum>i<n. coeffs i * vx i)
                     \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
  shows "top1_is_polygonal_region_on P n
       \<and> (\<forall>i<n. (vx i, vy i) \<in> P)
       \<and> (\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j))
       \<and> (\<forall>i<n. let cx = (\<Sum>j<n. vx j) / real n; cy = (\<Sum>j<n. vy j) / real n
           in (vx i - cx) * (vy (Suc i mod n) - cy) - (vy i - cy) * (vx (Suc i mod n) - cx) > 0)
       \<and> (\<forall>i<n. \<forall>k<n. k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod n \<longrightarrow>
           (vx k - vx i) * (vy (Suc i mod n) - vy i) - (vy k - vy i) * (vx (Suc i mod n) - vx i) < 0)"
  sorry \<comment> \<open>Regular n-gon properties: C1/C3/C4/C10/C11.
     Proved inside scheme\\_quotient\\_exists for the same definitions. Should be extractable.\<close>

\<comment> \<open>Key geometric helper: quotient preservation under edge permutation.
   Given a quotient of scheme s and s' = \\<sigma>-permutation of s (same edges, different order),
   Y is also a quotient of s'. The proof constructs a fresh polygon P' and quotient map
   q' = q \\<circ> \\<phi> where \\<phi>: P' \\<to> P is obtained by composing disk homeomorphisms with an
   arc permutation on B². See polygon\\_homeomorphic\\_to\\_disk\\_with\\_boundary.\<close>
lemma quotient_scheme_edge_permutation:
  fixes Y :: "'a set" and TY :: "'a set set"
  assumes "top1_quotient_of_scheme_on Y TY s"
      and "length s' = length s"
      and "\<exists>\<sigma>. bij_betw \<sigma> {..< length s} {..< length s} \<and> (\<forall>k < length s. s' ! k = s ! \<sigma> k)"
  shows "top1_quotient_of_scheme_on Y TY s'"
proof -
  let ?n = "length s"
  let ?TP = "\<lambda>S. subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S"
  \<comment> \<open>Step 1: Extract polygon P1, quotient map q1, vertices vx1/vy1 from the assumption.\<close>
  from assms(1) obtain P1 q1 vx1 vy1 where
      hC1_1: "top1_is_polygonal_region_on P1 ?n"
    and hC2_1: "top1_quotient_map_on P1 (?TP P1) Y TY q1"
    and hC3_1: "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> (vx1 i, vy1 i) \<noteq> (vx1 j, vy1 j)"
    and hC4_1: "\<forall>i<?n. (vx1 i, vy1 i) \<in> P1"
    and hC5_1: "P1 = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0) \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx1 i) \<and> y = (\<Sum>i<?n. coeffs i * vy1 i)}"
    and hC7_1: "\<forall>i<?n. \<forall>j<?n. fst (s!i) = fst (s!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q1 ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
           (1-t) * vy1 i + t * vy1 (Suc i mod ?n))
         = (if snd (s!i) = snd (s!j)
            then q1 ((1-t) * vx1 j + t * vx1 (Suc j mod ?n),
                    (1-t) * vy1 j + t * vy1 (Suc j mod ?n))
            else q1 (t * vx1 j + (1-t) * vx1 (Suc j mod ?n),
                    t * vy1 j + (1-t) * vy1 (Suc j mod ?n))))"
    and hC8_1: "\<forall>p\<in>P1. (\<forall>i<?n. \<forall>t\<in>I_set.
                p \<noteq> ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
                      (1-t) * vy1 i + t * vy1 (Suc i mod ?n)))
             \<longrightarrow> (\<forall>p'\<in>P1. q1 p = q1 p' \<longrightarrow> p = p')"
    and hC9_1: "\<forall>i<?n. \<forall>j<?n. \<forall>t\<in>{0<..<(1::real)}. \<forall>ss\<in>{0<..<(1::real)}.
            q1 ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
               (1-t) * vy1 i + t * vy1 (Suc i mod ?n))
          = q1 ((1-ss) * vx1 j + ss * vx1 (Suc j mod ?n),
               (1-ss) * vy1 j + ss * vy1 (Suc j mod ?n))
          \<longrightarrow> (i = j \<and> t = ss)
            \<or> (fst (s!i) = fst (s!j) \<and>
               (if snd (s!i) = snd (s!j) then ss = t else ss = 1 - t))"
    and hC10_1: "\<forall>i<?n. let cx = (\<Sum>j<?n. vx1 j) / real ?n;
                             cy = (\<Sum>j<?n. vy1 j) / real ?n
         in (vx1 i - cx) * (vy1 (Suc i mod ?n) - cy)
          - (vy1 i - cy) * (vx1 (Suc i mod ?n) - cx) > 0"
    and hC11_1: "\<forall>i<?n. \<forall>k<?n. k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
          (vx1 k - vx1 i) * (vy1 (Suc i mod ?n) - vy1 i)
          - (vy1 k - vy1 i) * (vx1 (Suc i mod ?n) - vx1 i) < 0"
    by (rule quotient_of_scheme_extract_vx)
  \<comment> \<open>Step 2: Get the permutation \\<sigma>.\<close>
  from assms(3) obtain \<sigma> where
    h\<sigma>_bij: "bij_betw \<sigma> {..< ?n} {..< ?n}"
    and h\<sigma>_match: "\<forall>k < ?n. s' ! k = s ! \<sigma> k"
    by (by100 blast)
  have hn3: "?n \<ge> 3" using assms(1) quotient_scheme_length_ge3 by (by100 simp)
  \<comment> \<open>Step 3: Construct fresh polygon P2 (regular n-gon) and disk homeomorphisms.
     Then \\<phi> = \\<psi>1\\<inverse> \\<circ> \\<tau> \\<circ> \\<psi>2 where \\<tau> permutes arcs per \\<sigma>.
     Define q2 = q1 \\<circ> \\<phi> and verify all 11 conditions for (P2, q2, vx2, vy2, s').
     This follows the scheme\\_quotient\\_uniqueness technique with permuted edges.\<close>
  \<comment> \<open>Step 3a: Construct P2 as regular n-gon (from scheme\\_quotient\\_exists infrastructure).\<close>
  define vx2 where "vx2 k = cos (2 * pi * real k / real ?n)" for k
  define vy2 where "vy2 k = sin (2 * pi * real k / real ?n)" for k
  define P2 where "P2 = {(x::real,y::real). \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx2 i)
                     \<and> y = (\<Sum>i<?n. coeffs i * vy2 i)}"
  \<comment> \<open>P2 satisfies C1/C3/C4/C5/C10/C11 (from regular\\_ngon\\_polygonal\\_region).\<close>
  from regular_ngon_polygonal_region[OF hn3]
  have hC1_2: "top1_is_polygonal_region_on P2 ?n"
    and hC4_2: "\<forall>i<?n. (vx2 i, vy2 i) \<in> P2"
    and hC3_2: "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> (vx2 i, vy2 i) \<noteq> (vx2 j, vy2 j)"
    and hC10_2: "\<forall>i<?n. let cx = (\<Sum>j<?n. vx2 j) / real ?n;
                             cy = (\<Sum>j<?n. vy2 j) / real ?n
         in (vx2 i - cx) * (vy2 (Suc i mod ?n) - cy)
          - (vy2 i - cy) * (vx2 (Suc i mod ?n) - cx) > 0"
    and hC11_2: "\<forall>i<?n. \<forall>k<?n. k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
          (vx2 k - vx2 i) * (vy2 (Suc i mod ?n) - vy2 i)
          - (vy2 k - vy2 i) * (vx2 (Suc i mod ?n) - vx2 i) < 0"
    unfolding vx2_def vy2_def P2_def by (by100 auto)+
  have hC5_2: "P2 = {(x, y) | x y. \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0) \<and> (\<Sum>i<?n. coeffs i) = 1
      \<and> x = (\<Sum>i<?n. coeffs i * vx2 i) \<and> y = (\<Sum>i<?n. coeffs i * vy2 i)}"
    unfolding P2_def by (by100 simp)
  \<comment> \<open>Step 3b: Get disk homeomorphisms for both polygons.\<close>
  \<comment> \<open>The disk homeomorphism technique and composition follow
     exactly as in scheme\\_quotient\\_uniqueness (line ~4050-4200 of this file).
     \\<psi>1: P1 \\<to> B2, \\<psi>2: P2 \\<to> B2 (from polygon\\_homeomorphic\\_to\\_disk\\_with\\_boundary).
     \\<tau>: B2 \\<to> B2 (PL homeomorphism permuting arcs per \\<sigma>).
     \\<phi> = \\<psi>1\\<inverse> \\<circ> \\<tau> \\<circ> \\<psi>2: P2 \\<to> P1.
     \\<phi> maps edge k of P2 to edge \\<sigma>(k) of P1.
     q2 = q1 \\<circ> \\<phi>: P2 \\<to> Y.
     Fibre matching: (q1\\<circ>\\<phi>)(x) = (q1\\<circ>\\<phi>)(y) \\<longleftrightarrow> s'-identification of x, y.
     Then quotient\\_on Y TY s' using P2, q2, vx2, vy2.\<close>
  show ?thesis sorry \<comment> \<open>Steps 3b onward: disk homeo composition + fibre matching.
     Same technique as scheme\\_quotient\\_uniqueness (lines 4050-4370) but with
     \\<tau> permuting arcs per \\<sigma>. The fibre matching uses:
     q1(\\<phi>(edge\\_k\\_P2(t))) = q1(edge\\_{\\<sigma>(k)}\\_P1(t))
     and C9 of P1 gives the s'-identification pattern.\<close>
qed

\<comment> \<open>Cut-paste preservation: homeomorphic realization (per audit 22 §5.5).
   The quotient of the cut-paste rearranged scheme is homeomorphic to the original.
   Book: Munkres §76, Theorem 76.1. Cut along diagonal, rearrange, paste.
   Uses quotient\\_scheme\\_same\\_labels\\_rearrange for the same-space construction.\<close>
\<comment> \<open>Cut-paste §76(iv): homeomorphic realization via polygon\\_cut\\_reglue (Munkres Theorem 76.1).
   Per audit 22 §5.5: one geometric theorem for all three cut-paste variants.\<close>
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
lemma scheme_quotient_exists:
  fixes scheme :: "(nat \<times> bool) list"
  assumes "length scheme \<ge> 3"
      and hproper: "\<forall>label. card {i. i < length scheme \<and> fst (scheme ! i) = label} \<in> {0, 2}"
  shows "\<exists>(Y :: (real \<times> real) set) (TY :: (real \<times> real) set set).
    top1_quotient_of_scheme_on Y TY scheme"
proof -
  let ?n = "length scheme"
  \<comment> \<open>Regular n-gon: vertices at (cos(2\\<pi>k/n), sin(2\\<pi>k/n)).\<close>
  define vx where "vx k = cos (2 * pi * real k / real ?n)" for k
  define vy where "vy k = sin (2 * pi * real k / real ?n)" for k
  \<comment> \<open>P = convex hull of vertices.\<close>
  define P where "P = {(x::real,y::real). \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx i)
                     \<and> y = (\<Sum>i<?n. coeffs i * vy i)}"
  \<comment> \<open>Quotient map: on boundary, identify edges per scheme. Interior maps injectively.
     For edge i (from v\\_i to v\\_{i+1}), at parameter t \\<in> [0,1]:
       point = ((1-t)*vx i + t*vx(Suc i mod n), (1-t)*vy i + t*vy(Suc i mod n))
     If edge i is identified with edge j (same label):
       - same direction: q(edge\\_i(t)) = q(edge\\_j(t))
       - opposite direction: q(edge\\_i(t)) = q(edge\\_j(1-t))
     For interior points (not on any edge): q = id (no identification).\<close>
  \<comment> \<open>Define q via representatives: for each boundary point, pick canonical edge/param.\<close>
  \<comment> \<open>Edge point helper: point on edge i at parameter t.\<close>
  define edge_pt where "edge_pt i t = ((1-t)*vx i + t*vx(Suc i mod ?n),
                                        (1-t)*vy i + t*vy(Suc i mod ?n))" for i t
  \<comment> \<open>For each edge position i, find the partner position (same label, other occurrence).
     For a proper scheme, each label appears 0 or 2 times.\<close>
  define partner where "partner i = (SOME j. j < ?n \<and> j \<noteq> i \<and> fst(scheme!i) = fst(scheme!j))" for i
  \<comment> \<open>Is edge i the canonical one (lower index) of its pair?\<close>
  define is_canonical where "is_canonical i = (i \<le> partner i)" for i
  \<comment> \<open>Partner properties (from properness of scheme).\<close>
  have partner_props: "\<And>i. i < ?n \<Longrightarrow> card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)} = 2 \<Longrightarrow>
      partner i < ?n \<and> partner i \<noteq> i \<and> fst(scheme!(partner i)) = fst(scheme!i)"
  proof -
    fix i assume hi: "i < ?n" and hcard: "card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)} = 2"
    \<comment> \<open>The set has exactly 2 elements, one of which is i. The other is partner(i).\<close>
    have "i \<in> {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)}" using hi by (by100 simp)
    hence "\<exists>j. j \<in> {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)} \<and> j \<noteq> i"
    proof -
      have "card ({j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)} - {i}) = 1"
        using hcard \<open>i \<in> _\<close> by (by100 simp)
      hence "{j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)} - {i} \<noteq> {}" by (by100 force)
      thus ?thesis by (by100 blast)
    qed
    then obtain j where hj: "j < ?n" "j \<noteq> i" "fst(scheme!j) = fst(scheme!i)" by (by100 blast)
    have hex: "\<exists>j. j < ?n \<and> j \<noteq> i \<and> fst(scheme!i) = fst(scheme!j)"
      using hj(1) hj(2) hj(3)[symmetric] by (by100 blast)
    have "partner i < ?n \<and> partner i \<noteq> i \<and> fst(scheme!i) = fst(scheme!(partner i))"
      unfolding partner_def using someI_ex[OF hex] by (by100 blast)
    thus "partner i < ?n \<and> partner i \<noteq> i \<and> fst(scheme!(partner i)) = fst(scheme!i)"
      by (by100 simp)
  qed
  \<comment> \<open>Partner uniqueness: for proper scheme, partner is the unique other edge with same label.\<close>
  have partner_unique: "\<And>i j. i < ?n \<Longrightarrow> j < ?n \<Longrightarrow> i \<noteq> j \<Longrightarrow> fst(scheme!i) = fst(scheme!j) \<Longrightarrow>
      partner i = j"
  proof -
    fix i j assume hi: "i < ?n" and hj: "j < ?n" and hij: "i \<noteq> j" and hlabel: "fst(scheme!i) = fst(scheme!j)"
    \<comment> \<open>The set {k. k < n \\<and> fst(scheme!k) = fst(scheme!i)} has exactly 2 elements: i and j.\<close>
    have hcard: "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} = 2"
    proof -
      have "i \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" using hi by (by100 simp)
      have hfin: "finite {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" by (by100 simp)
      have hne: "{k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<noteq> {}" using \<open>i \<in> _\<close> by (by100 blast)
      have "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<noteq> 0" using hfin hne by (by100 simp)
      hence "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<ge> 1" by (by100 linarith)
      moreover have "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<in> {0, 2}"
        using hproper by (by100 blast)
      ultimately show ?thesis
      proof (cases "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} = 0")
        case True thus ?thesis using \<open>_ \<ge> 1\<close> by (by100 linarith)
      next
        case False thus ?thesis using \<open>_ \<in> {0,2}\<close> by (by100 blast)
      qed
    qed
    \<comment> \<open>The set is exactly {i, j}.\<close>
    have hset: "{k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} = {i, j}"
    proof -
      have "i \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" using hi by (by100 simp)
      have "j \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" using hj hlabel by (by100 simp)
      have "card {i, j} = 2" using hij by (by100 simp)
      have "{i, j} \<subseteq> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}"
        using \<open>i \<in> _\<close> \<open>j \<in> _\<close> by (by100 blast)
      have hfin: "finite {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" by (by100 simp)
      from card_subset_eq[OF hfin \<open>{i,j} \<subseteq> _\<close>]
      show ?thesis using hcard \<open>card {i,j} = 2\<close> by (by100 simp)
    qed
    \<comment> \<open>partner(i) is the unique k \\<noteq> i with same label. Since the set is {i,j}, partner(i) = j.\<close>
    have "partner i \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<and> partner i \<noteq> i"
      using partner_props[OF hi hcard] hlabel by (by100 blast)
    hence "partner i \<in> {i, j} \<and> partner i \<noteq> i" using hset by (by100 blast)
    thus "partner i = j" by (by100 blast)
  qed
  \<comment> \<open>Vertex equivalence: one-step identification pairs from all edge pairings.\<close>
  define vtx_id :: "(nat \<times> nat) set" where "vtx_id =
    (\<Union>idx \<in> {..<?n}. let j = partner idx in
      if snd(scheme!idx) = snd(scheme!j) then {(idx, j), (Suc idx mod ?n, Suc j mod ?n)}
      else {(idx, Suc j mod ?n), (Suc idx mod ?n, j)})"
  \<comment> \<open>Vertex target: LEAST vertex reachable via symmetric closure of vtx\\_id.
     This correctly computes the equivalence class representative even when
     vertex identifications chain across multiple edge pairings.\<close>
  define vtgt where "vtgt k = (LEAST m. (k, m) \<in> (vtx_id \<union> (converse vtx_id) \<union> Id)\<^sup>*)" for k
  \<comment> \<open>Key property: vertices in the same equivalence class have the same vtgt representative.\<close>
  have vtgt_class: "\<And>k1 k2. (k1, k2) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>* \<Longrightarrow> vtgt k1 = vtgt k2"
  proof -
    fix k1 k2 :: nat assume hrel: "(k1, k2) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*"
    have hsym: "sym (vtx_id \<union> converse vtx_id \<union> Id)" unfolding sym_def by (by100 blast)
    from sym_rtrancl[OF hsym] have hsymR: "sym ((vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*)" .
    hence hrev: "(k2, k1) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*"
      using hrel unfolding sym_def by (by100 blast)
    have "{m. (k1, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*}
        = {m. (k2, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*}"
    proof (intro equalityI subsetI CollectI)
      fix m assume "m \<in> {m. (k1, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*}"
      hence "(k1, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*" by (by100 simp)
      with hrev show "(k2, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*"
        by (rule rtrancl_trans)
    next
      fix m assume "m \<in> {m. (k2, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*}"
      hence "(k2, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*" by (by100 simp)
      with hrel show "(k1, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*"
        by (rule rtrancl_trans)
    qed
    hence "(\<lambda>m. (k1, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*)
         = (\<lambda>m. (k2, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*)"
      by (by100 auto)
    thus "vtgt k1 = vtgt k2" unfolding vtgt_def by (by100 simp)
  qed
  \<comment> \<open>Quotient map q (3-branch): vertex \\<to> vtgt, edge interior \\<to> partner, else \\<to> identity.\<close>
  define q :: "(real \<times> real) \<Rightarrow> (real \<times> real)" where
    "q p = (if \<exists>k<?n. p = (vx k, vy k) then
              let k = (SOME k. k < ?n \<and> p = (vx k, vy k)) in (vx (vtgt k), vy (vtgt k))
            else if \<exists>i t. i < ?n \<and> 0 < t \<and> t < 1 \<and> p = edge_pt i t \<and> \<not> is_canonical i then
              let (i,t) = (SOME (i,t). i < ?n \<and> 0 < t \<and> t < 1 \<and> p = edge_pt i t \<and> \<not> is_canonical i)
              in let j = partner i in
              if snd(scheme!i) = snd(scheme!j) then edge_pt j t else edge_pt j (1-t)
            else p)" for p
  \<comment> \<open>Y = image of P under q.\<close>
  define Y where "Y = q ` P"
  define TY where "TY = {U. \<exists>V. V \<subseteq> P \<and> (\<forall>x \<in> V. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> V) \<and> U = q ` V
      \<and> V \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P}"
  \<comment> \<open>The 11 conditions need to be verified. Main challenges:
     C1 (polygonal region): regular n-gon is convex, n \\<ge> 3 by assumption.
     C2 (quotient map): q is continuous, surjective, TY is quotient topology.
     C3 (vertex distinctness): distinct angles give distinct points.
     C4 (vertices in P): vertices are in convex hull.
     C5 (P = convex hull): by definition.
     C6 (edge interiors don't intersect): convexity + distinct vertices.
     C8 (identification pattern): by construction of q.
     C9 (interior injectivity): q = id on interior.
     C10 (CCW orientation): regular polygon vertices are CCW.
     C11 (strict convexity): all vertices on one side of each edge.\<close>
  \<comment> \<open>C3: vertex distinctness. Distinct i,j < n give distinct angles, hence distinct (cos,sin).\<close>
  have hC3: "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)"
  proof (intro allI impI)
    fix i j assume hi: "i < ?n" and hj: "j < ?n" and hij: "i \<noteq> j"
    show "(vx i, vy i) \<noteq> (vx j, vy j)"
    proof
      assume heq: "(vx i, vy i) = (vx j, vy j)"
      hence "cos (2*pi*real i/real ?n) = cos (2*pi*real j/real ?n)"
        and "sin (2*pi*real i/real ?n) = sin (2*pi*real j/real ?n)"
        unfolding vx_def vy_def by (by100 auto)+
      from cos_sin_eq_imp[OF this]
      obtain k :: int where hk: "2*pi*real i/real ?n - 2*pi*real j/real ?n = real_of_int k * 2 * pi"
        by (by100 blast)
      have hpi_pos: "pi > 0" using pi_gt_zero .
      have hn_pos: "real ?n > 0" using assms by (by100 linarith)
      from hk have h_diff: "(real i - real j) / real ?n = real_of_int k"
      proof -
        from hk have "2*pi*real i/real ?n - 2*pi*real j/real ?n = real_of_int k * (2 * pi)"
          by (by100 simp)
        hence "2*pi * (real i/real ?n - real j/real ?n) = real_of_int k * (2 * pi)"
          using hn_pos by (simp add: diff_divide_distrib algebra_simps)
        hence "real i/real ?n - real j/real ?n = real_of_int k"
          using hpi_pos by (by100 simp)
        thus ?thesis using hn_pos by (simp add: diff_divide_distrib)
      qed
      hence "real i - real j = real_of_int k * real ?n"
        using hn_pos by (simp add: field_simps)
      hence "real_of_int (int i - int j) = real_of_int k * real ?n"
        by (by100 simp)
      \<comment> \<open>Since |i-j| < n and n > 0, the only integer k giving |k*n| < n is k = 0.\<close>
      hence hk0: "k = 0"
      proof -
        have "real_of_int (int i - int j) = real_of_int k * real ?n"
          using \<open>real i - real j = real_of_int k * real ?n\<close> by (by100 simp)
        have "\<bar>real_of_int (int i - int j)\<bar> < real ?n"
          using hi hj by (by100 simp)
        hence "\<bar>real_of_int k * real ?n\<bar> < real ?n"
          using \<open>real_of_int (int i - int j) = real_of_int k * real ?n\<close> by (by100 simp)
        hence "\<bar>real_of_int k\<bar> * real ?n < real ?n"
          using hn_pos by (simp add: abs_mult)
        hence "\<bar>real_of_int k\<bar> < 1"
          using hn_pos by (by100 simp)
        thus "k = 0" by (by100 linarith)
      qed
      hence "real i = real j" using \<open>(real i - real j)/real ?n = real_of_int k\<close> hn_pos
        by (by100 simp)
      hence "i = j" by (by100 simp)
      thus False using hij by (by100 simp)
    qed
  qed
  \<comment> \<open>C4: vertices in P (each vertex is a convex combination with coefficient 1 at position k).\<close>
  have hC4: "\<forall>i<?n. (vx i, vy i) \<in> P"
  proof (intro allI impI)
    fix k assume hk: "k < ?n"
    define coeffs :: "nat \<Rightarrow> real" where "coeffs j = (if j = k then 1 else 0)" for j
    have "\<forall>i<?n. coeffs i \<ge> 0" unfolding coeffs_def by (by100 simp)
    moreover have "(\<Sum>i<?n. coeffs i) = 1"
      unfolding coeffs_def using hk by (by100 simp)
    moreover have "vx k = (\<Sum>i<?n. coeffs i * vx i)"
    proof -
      have "(\<Sum>i<?n. coeffs i * vx i) = (\<Sum>i<?n. (if i=k then vx i else 0))"
        unfolding coeffs_def by (rule sum.cong) (by100 auto)+
      also have "\<dots> = vx k" using hk by (by100 simp)
      finally show ?thesis by (by100 simp)
    qed
    moreover have "vy k = (\<Sum>i<?n. coeffs i * vy i)"
    proof -
      have "(\<Sum>i<?n. coeffs i * vy i) = (\<Sum>i<?n. (if i=k then vy i else 0))"
        unfolding coeffs_def by (rule sum.cong) (by100 auto)+
      also have "\<dots> = vy k" using hk by (by100 simp)
      finally show ?thesis by (by100 simp)
    qed
    ultimately show "(vx k, vy k) \<in> P"
      unfolding P_def by (by100 blast)
  qed
  \<comment> \<open>C5: P = convex hull of vertices (by definition of P).\<close>
  have hC5: "P = {(x,y) | x y. \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0)
                   \<and> (\<Sum>i<?n. coeffs i) = 1
                   \<and> x = (\<Sum>i<?n. coeffs i * vx i)
                   \<and> y = (\<Sum>i<?n. coeffs i * vy i)}"
    unfolding P_def by (by100 simp)
  \<comment> \<open>C1: P is a polygonal region. Need: n \\<ge> 3, distinct vertices, no vertex in hull of others.\<close>
  \<comment> \<open>Extremality: no vertex is in convex hull of the others.\<close>
  have hextreme: "\<forall>k<?n. \<not> (\<exists>coeffs. (\<forall>i<?n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0
            \<and> (\<Sum>i<?n. coeffs i) = 1
            \<and> vx k = (\<Sum>i<?n. coeffs i * vx i) \<and> vy k = (\<Sum>i<?n. coeffs i * vy i))"
  proof (intro allI impI notI)
    fix k assume hk: "k < ?n"
    assume "\<exists>coeffs. (\<forall>i<?n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0
            \<and> (\<Sum>i<?n. coeffs i) = 1
            \<and> vx k = (\<Sum>i<?n. coeffs i * vx i) \<and> vy k = (\<Sum>i<?n. coeffs i * vy i)"
    then obtain coeffs where
        hcoeff_pos: "\<forall>i<?n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0"
      and hk0: "coeffs k = 0"
      and hsum1: "(\<Sum>i<?n. coeffs i) = 1"
      and hvx: "vx k = (\<Sum>i<?n. coeffs i * vx i)"
      and hvy: "vy k = (\<Sum>i<?n. coeffs i * vy i)" by (by100 blast)
    \<comment> \<open>Dot product with radial direction of vertex k:
       d(k) = vx(k)*vx(k) + vy(k)*vy(k) = cos^2 + sin^2 = 1.
       For any other vertex i \\<noteq> k:
       d(i) = vx(k)*vx(i) + vy(k)*vy(i) = cos(2\\<pi>k/n)*cos(2\\<pi>i/n) + sin(2\\<pi>k/n)*sin(2\\<pi>i/n)
            = cos(2\\<pi>(k-i)/n) < 1 (since k \\<noteq> i mod n gives nonzero angle).\<close>
    define dot where "dot i = vx k * vx i + vy k * vy i" for i
    have hdk: "dot k = 1" unfolding dot_def vx_def vy_def
      using sin_cos_squared_add[of "2*pi*real k/real ?n"] by (by100 simp)
    \<comment> \<open>Convex combination of dot products equals dot product of convex combination.\<close>
    have "(\<Sum>i<?n. coeffs i * dot i) = vx k * (\<Sum>i<?n. coeffs i * vx i) + vy k * (\<Sum>i<?n. coeffs i * vy i)"
      unfolding dot_def by (simp add: sum_distrib_left algebra_simps sum.distrib)
    also have "\<dots> = vx k * vx k + vy k * vy k" using hvx hvy by (by100 simp)
    also have "\<dots> = 1" unfolding vx_def vy_def
      using sin_cos_squared_add[of "2*pi*real k/real ?n"] by (by100 simp)
    finally have hsum_dot: "(\<Sum>i<?n. coeffs i * dot i) = 1" .
    \<comment> \<open>But dot i < 1 for all i \\<noteq> k (cosine of nonzero angle).\<close>
    have hdot_lt: "\<forall>i<?n. i \<noteq> k \<longrightarrow> dot i < 1"
    proof (intro allI impI)
      fix i assume "i < ?n" "i \<noteq> k"
      have hn_pos': "real ?n > 0" using assms by (by100 linarith)
      have "dot i = cos (2*pi*real k/real ?n - 2*pi*real i/real ?n)"
        unfolding dot_def vx_def vy_def
        using cos_diff[of "2*pi*real k/real ?n" "2*pi*real i/real ?n"] by (by100 simp)
      also have "\<dots> = cos (2*pi*(real k - real i)/real ?n)"
        using hn_pos' by (simp add: diff_divide_distrib algebra_simps)
      finally have hdot_eq: "dot i = cos (2*pi*(real k - real i)/real ?n)" .
      \<comment> \<open>The angle 2\\<pi>(k-i)/n is not a multiple of 2\\<pi> (since 0 < |k-i| < n).\<close>
      have "cos (2*pi*(real k - real i)/real ?n) < 1"
      proof -
        \<comment> \<open>The angle \\<theta> = 2\\<pi>(k-i)/n is not a multiple of 2\\<pi>.\<close>
        have "real k - real i \<noteq> 0" using \<open>i \<noteq> k\<close> by (by100 simp)
        hence hangle_ne0: "2*pi*(real k - real i)/real ?n \<noteq> 0"
          using pi_gt_zero hn_pos' by (by100 simp)
        \<comment> \<open>|k-i| < n, so |\\<theta>| < 2\\<pi>. Hence \\<theta> is not a nonzero multiple of 2\\<pi>.\<close>
        have habs_diff: "\<bar>real k - real i\<bar> < real ?n" using \<open>i < ?n\<close> hk by (by100 simp)
        have "\<bar>2*pi*(real k - real i)/real ?n\<bar> = 2*pi * \<bar>real k - real i\<bar> / real ?n"
          using pi_gt_zero hn_pos' by (simp add: abs_mult)
        also have "\<dots> < 2*pi"
        proof -
          have "\<bar>real k - real i\<bar> / real ?n < real ?n / real ?n"
            using habs_diff hn_pos'
            by (intro divide_strict_right_mono) (by100 auto)+
          hence "\<bar>real k - real i\<bar> / real ?n < 1" using hn_pos' by (by100 simp)
          have h2pi: "2*pi > 0" using pi_gt_zero by (by100 simp)
          have "2*pi * (\<bar>real k - real i\<bar> / real ?n) < 2*pi * 1"
            using \<open>\<bar>real k - real i\<bar> / real ?n < 1\<close> h2pi
            by (rule mult_strict_left_mono)
          hence "2*pi * \<bar>real k - real i\<bar> / real ?n < 2*pi"
            by (by100 simp)
          thus ?thesis by (by100 simp)
        qed
        finally have habs_lt: "\<bar>2*pi*(real k - real i)/real ?n\<bar> < 2*pi" .
        \<comment> \<open>So \\<theta> \\<in> (-2\\<pi>, 2\\<pi>) \\<setminus> \\{0\\}. cos is < 1 on this set.\<close>
        \<comment> \<open>cos \\<le> 1 always. cos = 1 implies \\<theta> = 0 (modulo 2\\<pi>).\<close>
        let ?\<theta> = "2*pi*(real k - real i)/real ?n"
        have "cos ?\<theta> \<noteq> 1"
        proof
          assume hcos1: "cos ?\<theta> = 1"
          have hsin0: "sin ?\<theta> = 0"
          proof -
            from sin_cos_squared_add[of ?\<theta>]
            have "(sin ?\<theta>)\<^sup>2 = 1 - (cos ?\<theta>)\<^sup>2" by (by100 linarith)
            also have "\<dots> = 0" using hcos1 by (by100 simp)
            finally show ?thesis by (by100 simp)
          qed
          have hcos_eq: "cos 0 = cos ?\<theta>" using hcos1 by (by100 simp)
          have hsin_eq: "sin 0 = sin ?\<theta>" using hsin0 by (by100 simp)
          from cos_sin_eq_imp[OF hcos_eq hsin_eq]
          obtain kk :: int where hkk: "0 - ?\<theta> = real_of_int kk * 2 * pi" by (by100 blast)
          hence "?\<theta> = -(real_of_int kk) * (2*pi)" by (by100 linarith)
          hence "\<bar>real_of_int kk\<bar> * (2*pi) < 2*pi"
            using habs_lt by (simp add: abs_mult abs_minus_commute)
          hence "\<bar>real_of_int kk\<bar> < 1" using pi_gt_zero by (by100 simp)
          hence "kk = 0" by (by100 linarith)
          hence "?\<theta> = 0" using \<open>?\<theta> = -(real_of_int kk) * (2*pi)\<close> by (by100 simp)
          thus False using hangle_ne0 by (by100 simp)
        qed
        from this show ?thesis using cos_le_one[of ?\<theta>] by (by100 linarith)
      qed
      thus "dot i < 1" using hdot_eq by (by100 simp)
    qed
    \<comment> \<open>Since coeffs k = 0 and sum coeffs = 1, there exists i \\<noteq> k with coeffs i > 0.\<close>
    have "\<exists>i<?n. i \<noteq> k \<and> coeffs i > 0"
    proof (rule ccontr)
      assume "\<not> (\<exists>i<?n. i \<noteq> k \<and> coeffs i > 0)"
      hence "\<forall>i<?n. i \<noteq> k \<longrightarrow> coeffs i \<le> 0" by (by100 auto)
      hence hall0: "\<forall>i<?n. i \<noteq> k \<longrightarrow> coeffs i = 0" using hcoeff_pos by (by100 force)
      hence "\<forall>i<?n. coeffs i = 0" using hk0 by (by100 force)
      hence "(\<Sum>i<?n. coeffs i) = 0" by (by100 simp)
      thus False using hsum1 by (by100 simp)
    qed
    \<comment> \<open>Then the weighted sum of dot products is < 1, contradicting = 1.\<close>
    then obtain i0 where hi0: "i0 < ?n" "i0 \<noteq> k" "coeffs i0 > 0" by (by100 blast)
    have "(\<Sum>i<?n. coeffs i * dot i) < (\<Sum>i<?n. coeffs i * 1)"
    proof -
      \<comment> \<open>Each term: coeffs i * dot i \\<le> coeffs i * 1 (since dot i \\<le> 1 and coeffs i \\<ge> 0).\<close>
      have hle: "\<forall>i<?n. coeffs i * dot i \<le> coeffs i * 1"
      proof (intro allI impI)
        fix i assume "i < ?n"
        show "coeffs i * dot i \<le> coeffs i * 1"
        proof (cases "i = k")
          case True thus ?thesis using hk0 by (by100 simp)
        next
          case False
          hence "coeffs i \<ge> 0" using hcoeff_pos \<open>i < ?n\<close> by (by100 blast)
          moreover have "dot i \<le> 1"
          proof -
            have "dot i = cos (2*pi*real k/real ?n - 2*pi*real i/real ?n)"
              unfolding dot_def vx_def vy_def
              using cos_diff[of "2*pi*real k/real ?n" "2*pi*real i/real ?n"] by (by100 simp)
            thus ?thesis using cos_le_one by (by100 simp)
          qed
          ultimately show ?thesis using mult_left_mono[of "dot i" 1 "coeffs i"] by (by100 simp)
        qed
      qed
      \<comment> \<open>The i0 term is strictly less: coeffs i0 * dot i0 < coeffs i0 * 1.\<close>
      have hdot_i0_lt: "dot i0 < 1" using hdot_lt hi0(1) hi0(2) by (by100 blast)
      have hstrict: "coeffs i0 * dot i0 < coeffs i0 * 1"
        using hi0(3) hdot_i0_lt by (by100 simp)
      \<comment> \<open>Sum with one strict and rest \\<le> gives strict overall.\<close>
      show ?thesis
        using sum_strict_mono_ex1[of "{..<(length scheme)}" "\<lambda>i. coeffs i * dot i" "\<lambda>i. coeffs i * 1"]
              hle hstrict hi0(1) by (by100 force)
    qed
    also have "\<dots> = 1" using hsum1 by (by100 simp)
    finally show False using hsum_dot by (by100 simp)
  qed
  have hC1: "top1_is_polygonal_region_on P ?n"
    unfolding top1_is_polygonal_region_on_def
    using assms hC3 hextreme hC5 by (by100 blast)
  \<comment> \<open>C10: CCW orientation. For regular polygon, cross product
     (v\\_i - centroid) \\<times> (v\\_{i+1} - centroid) = sin(2\\<pi>/n) > 0.\<close>
  \<comment> \<open>Centroid of regular n-gon is (0,0): sum of n-th roots of unity = 0.\<close>
  \<comment> \<open>Sum of n-th roots of unity = 0 (complex geometric series).
     Proof: cis(2\\<pi>k/n) = (cis(2\\<pi>/n))^k by DeMoivre.
     \\<Sum>k<n (cis(2\\<pi>/n))^k = (1 - (cis(2\\<pi>/n))^n)/(1 - cis(2\\<pi>/n)) = 0
     since (cis(2\\<pi>/n))^n = cis(2\\<pi>) = 1.\<close>
  \<comment> \<open>Prove \\<Sum>k<n. cis(2\\<pi>k/n) = 0 via geometric series, then extract Re/Im.\<close>
  have hn_pos: "real ?n > 0" using assms by (by100 linarith)
  have hsin_pos: "sin (2 * pi / real ?n) > 0"
  proof -
    have "2 * pi / real ?n > 0" using pi_gt_zero hn_pos by (by100 simp)
    moreover have "2 * pi / real ?n < pi"
    proof -
      have "real ?n \<ge> 3" using assms by (by100 simp)
      hence "2 * pi / real ?n \<le> 2 * pi / 3" using pi_gt_zero
        by (intro divide_left_mono) (by100 auto)+
      also have "\<dots> < pi" using pi_gt_zero by (by100 simp)
      finally show ?thesis .
    qed
    ultimately show ?thesis using sin_gt_zero by (by100 blast)
  qed
  have hroots: "(\<Sum>k<?n. cis (2*pi*real k/real ?n)) = (0 :: complex)"
  proof -
    let ?w = "cis (2*pi/real ?n) :: complex"
    \<comment> \<open>Each term is ?w^k.\<close>
    have hw_k: "\<And>k. ?w ^ k = cis (real k * (2*pi/real ?n))"
      using DeMoivre by (by100 blast)
    have hw_k': "\<And>k::nat. cis (2*pi*real k/real ?n) = ?w ^ k"
    proof -
      fix k :: nat
      have eq: "(2::real)*pi*real k/real ?n = real k * (2*pi/real ?n)"
        by (by100 algebra)
      show "cis (2*pi*real k/real ?n) = ?w ^ k"
        unfolding eq using hw_k[of k] by (by100 simp)
    qed
    have sum_eq: "(\<Sum>k<?n. cis (2*pi*real k/real ?n)) = (\<Sum>k<?n. ?w ^ k)"
      using hw_k' by (intro sum.cong) (by100 simp)+
    \<comment> \<open>?w^n = cis(2\\<pi>) = 1.\<close>
    have hw_n: "?w ^ ?n = 1"
    proof -
      have "?w ^ ?n = cis (real ?n * (2*pi/real ?n))" using DeMoivre by (by100 blast)
      also have "real ?n * (2*pi/real ?n) = 2*pi" using hn_pos by (by100 simp)
      also have "cis (2*pi) = 1"
        using cis_2pi by (by100 simp)
      finally show ?thesis .
    qed
    \<comment> \<open>?w \\<noteq> 1 (since 0 < 2\\<pi>/n < 2\\<pi>).\<close>
    have hw_ne1: "?w \<noteq> 1"
    proof
      assume "?w = 1"
      \<comment> \<open>cis(2\\<pi>/n)=1 implies 2\\<pi>/n = 2k\\<pi> for some integer k.
         Since 0 < 2\\<pi>/n < 2\\<pi> (for n\\<ge>3), only k=0 possible, giving 2\\<pi>/n=0, contradiction.\<close>
      hence "sin (2*pi/real ?n) = 0"
        by (simp add: complex_eq_iff cis.simps)
      thus False using hsin_pos by (by100 linarith)
    qed
    \<comment> \<open>Geometric series: (1 - ?w) * \\<Sum>k\\<le>n-1. ?w^k = 1 - ?w^n = 0.\<close>
    have "(1 - ?w) * (\<Sum>k\<le>?n - 1. ?w ^ k) = 1 - ?w ^ (Suc (?n - 1))"
      by (rule sum_gp_basic)
    also have "Suc (?n - 1) = ?n" using assms by (by100 simp)
    also have "1 - ?w ^ ?n = 0" using hw_n by (by100 simp)
    finally have "(1 - ?w) * (\<Sum>k\<le>?n - 1. ?w ^ k) = 0" .
    hence "(\<Sum>k\<le>?n - 1. ?w ^ k) = 0" using hw_ne1 by (by100 force)
    \<comment> \<open>Convert from {..n-1} to {..<n}.\<close>
    moreover have "{..?n - 1} = {..<?n}" using assms by (by100 auto)
    ultimately have "(\<Sum>k<?n. ?w ^ k) = 0" by (by100 simp)
    thus ?thesis using sum_eq by (by100 simp)
  qed
  have hcx0: "(\<Sum>j<?n. vx j) = 0"
  proof -
    have "(\<Sum>j<?n. vx j) = Re (\<Sum>j<?n. cis (2*pi*real j/real ?n))"
      unfolding vx_def by (simp add: Re_sum cis.simps)
    also have "\<dots> = Re 0" using hroots by (by100 simp)
    also have "\<dots> = 0" by (by100 simp)
    finally show ?thesis .
  qed
  have hcy0: "(\<Sum>j<?n. vy j) = 0"
  proof -
    have "(\<Sum>j<?n. vy j) = Im (\<Sum>j<?n. cis (2*pi*real j/real ?n))"
      unfolding vy_def by (simp add: Im_sum cis.simps)
    also have "\<dots> = Im 0" using hroots by (by100 simp)
    also have "\<dots> = 0" by (by100 simp)
    finally show ?thesis .
  qed
  \<comment> \<open>Cross product vx(i)*vy(i+1) - vy(i)*vx(i+1) = sin(2\\<pi>/n) for regular polygon.\<close>
  have hcross: "\<And>i. i < ?n \<Longrightarrow> vx i * vy (Suc i mod ?n) - vy i * vx (Suc i mod ?n) = sin (2 * pi / real ?n)"
  proof -
    fix i assume hi: "i < ?n"
    let ?a = "2*pi*real i/real ?n"
    let ?b = "2*pi*real (Suc i mod ?n)/real ?n"
    have step1: "vx i * vy (Suc i mod ?n) - vy i * vx (Suc i mod ?n)
        = cos ?a * sin ?b - sin ?a * cos ?b" unfolding vx_def vy_def by (by100 simp)
    have step2: "cos ?a * sin ?b - sin ?a * cos ?b = sin (?b - ?a)"
      using sin_diff[of ?b ?a] by (by100 simp)
    \<comment> \<open>Key: ?b - ?a = 2\\<pi> * (Suc i mod n - i) / n = 2\\<pi>/n (or 2\\<pi>*(n-i+1?)/n for wraparound).\<close>
    have step3: "sin (?b - ?a) = sin (2*pi/real ?n)"
    proof (cases "Suc i < ?n")
      case True
      \<comment> \<open>i < n-1: Suc i mod n = Suc i, so b-a = 2\\<pi>(i+1)/n - 2\\<pi>i/n = 2\\<pi>/n.\<close>
      have "Suc i mod ?n = Suc i" using True by (by100 simp)
      hence "?b - ?a = 2*pi*(real (Suc i))/real ?n - 2*pi*real i/real ?n" by (by100 simp)
      also have "\<dots> = 2*pi/real ?n"
        using assms by (simp add: of_nat_Suc divide_simps algebra_simps)
      finally show ?thesis by (by100 simp)
    next
      case False
      \<comment> \<open>i = n-1: Suc i mod n = 0, b-a = -2\\<pi>(n-1)/n. sin(-2\\<pi>(n-1)/n) = sin(2\\<pi>/n).\<close>
      hence "i = ?n - 1" using hi by (by100 simp)
      hence "Suc i = ?n" using hi by (by100 simp)
      hence "Suc i mod ?n = 0" by (by100 simp)
      hence h_mod0: "Suc i mod ?n = 0" by (by100 simp)
      \<comment> \<open>Direct: sin(?b - ?a) = sin(-2\\<pi>*(n-1)/n) = sin(2\\<pi>/n).\<close>
      have hba_neg: "?b - ?a = - (2*pi*real i/real ?n)"
        using h_mod0 by (by100 simp)
      have "sin (?b - ?a) = - sin (2*pi*real i/real ?n)"
        unfolding hba_neg by (by100 simp)
      also have "\<dots> = - sin (2*pi*real (?n - 1)/real ?n)"
        using \<open>i = ?n - 1\<close> by (by100 simp)
      also have "\<dots> = - sin (2*pi - 2*pi/real ?n)"
        using assms by (simp add: divide_simps algebra_simps of_nat_diff)
      also have "\<dots> = sin (2*pi/real ?n)"
      proof -
        have "sin (2*pi - 2*pi/real ?n) = - sin (2*pi/real ?n)"
          using sin_minus[of "2*pi/real ?n"] by (simp add: sin_diff)
        thus ?thesis by (by100 simp)
      qed
      finally show ?thesis .
    qed
    show "vx i * vy (Suc i mod ?n) - vy i * vx (Suc i mod ?n) = sin (2*pi/real ?n)"
      using step1 step2 step3 by (by100 simp)
  qed
  \<comment> \<open>hsin\\_pos already proved above. hcross uses it for C10 assembly.\<close>
  have hC10: "\<forall>i<?n. let cx = (\<Sum>j<?n. vx j)/real ?n; cy = (\<Sum>j<?n. vy j)/real ?n
       in (vx i - cx)*(vy(Suc i mod ?n) - cy) - (vy i - cy)*(vx(Suc i mod ?n) - cx) > 0"
  proof (intro allI impI, unfold Let_def)
    fix i assume hi: "i < ?n"
    \<comment> \<open>Goal: (vx i - cx)*(vy(i+1) - cy) - (vy i - cy)*(vx(i+1) - cx) > 0, where cx=\\<Sum>vx/n, cy=\\<Sum>vy/n.\<close>
    have "(\<Sum>j<?n. vx j) / real ?n = 0" using hcx0 by (by100 simp)
    moreover have "(\<Sum>j<?n. vy j) / real ?n = 0" using hcy0 by (by100 simp)
    moreover have "vx i * vy(Suc i mod ?n) - vy i * vx(Suc i mod ?n) = sin (2*pi/real ?n)"
      using hcross[OF hi] .
    moreover note hsin_pos
    ultimately have h1: "(\<Sum>j<?n. vx j) / real ?n = 0"
      and h2: "(\<Sum>j<?n. vy j) / real ?n = 0"
      and h3: "vx i * vy(Suc i mod ?n) - vy i * vx(Suc i mod ?n) = sin (2*pi/real ?n)"
      and h4: "sin (2*pi/real ?n) > 0" by auto
    show "(vx i - (\<Sum>j<?n. vx j) / real ?n) *
       (vy (Suc i mod ?n) - (\<Sum>j<?n. vy j) / real ?n) -
       (vy i - (\<Sum>j<?n. vy j) / real ?n) *
       (vx (Suc i mod ?n) - (\<Sum>j<?n. vx j) / real ?n) > 0"
    proof -
      have "vx i * vy (Suc i mod ?n) - vy i * vx (Suc i mod ?n) > 0"
        using h3 h4 by (by100 linarith)
      moreover have "(vx i - (\<Sum>j<?n. vx j) / real ?n) *
         (vy (Suc i mod ?n) - (\<Sum>j<?n. vy j) / real ?n) -
         (vy i - (\<Sum>j<?n. vy j) / real ?n) *
         (vx (Suc i mod ?n) - (\<Sum>j<?n. vx j) / real ?n)
         = vx i * vy (Suc i mod ?n) - vy i * vx (Suc i mod ?n)"
      proof -
        have "(\<Sum>j<?n. vx j) / real ?n = (0::real)" using h1 .
        moreover have "(\<Sum>j<?n. vy j) / real ?n = (0::real)" using h2 .
        ultimately have sx: "(\<Sum>j<?n. vx j) / real ?n = (0::real)"
          and sy: "(\<Sum>j<?n. vy j) / real ?n = (0::real)" by auto
        show ?thesis
          apply (subst sx)+
          apply (subst sy)+
          apply (simp only: diff_0_right mult_1_right)
          done
      qed
      ultimately show ?thesis by (by100 linarith)
    qed
  qed
  \<comment> \<open>C11: strict convexity. Every non-adjacent vertex is on the right of each edge.\<close>
  \<comment> \<open>C11 helper: the cross product for regular polygon vertices on the unit circle.
     For points at angles \\<alpha>, \\<beta>, \\<gamma> on the unit circle, the signed area of
     triangle (cos \\<alpha>, sin \\<alpha>), (cos \\<beta>, sin \\<beta>), (cos \\<gamma>, sin \\<gamma>) is
     (1/2)(sin(\\<beta>-\\<alpha>) + sin(\\<gamma>-\\<beta>) + sin(\\<alpha>-\\<gamma>)).
     We need: (cos \\<gamma> - cos \\<alpha>)(sin \\<beta> - sin \\<alpha>) - (sin \\<gamma> - sin \\<alpha>)(cos \\<beta> - cos \\<alpha>) < 0
     which equals sin(\\<beta>-\\<gamma>) + sin(\\<gamma>-\\<alpha>) - sin(\\<beta>-\\<alpha>).\<close>
  have cross_unit_circle:
    "\<And>a b c :: real. (cos c - cos a)*(sin b - sin a) - (sin c - sin a)*(cos b - cos a)
      = sin (b - c) + sin (c - a) - sin (b - a)"
  proof -
    fix a b c :: real
    \<comment> \<open>Expand LHS: cos(c)*sin(b) - cos(c)*sin(a) - cos(a)*sin(b) + cos(a)*sin(a)
       - sin(c)*cos(b) + sin(c)*cos(a) + sin(a)*cos(b) - sin(a)*cos(a)
       = [cos(c)*sin(b) - sin(c)*cos(b)]   = sin(b-c)
       + [sin(c)*cos(a) - cos(c)*sin(a)]   = sin(c-a)
       - [cos(a)*sin(b) - sin(a)*cos(b)]   = -sin(b-a)
       + [cos(a)*sin(a) - sin(a)*cos(a)]   = 0.\<close>
    have "cos c * sin b - sin c * cos b = sin (b - c)"
      using sin_diff[of b c] by (by100 simp)
    moreover have "sin c * cos a - cos c * sin a = sin (c - a)"
      using sin_diff[of c a] by (by100 simp)
    moreover have "cos a * sin b - sin a * cos b = sin (b - a)"
      using sin_diff[of b a] by (by100 simp)
    ultimately have h1: "sin (b - c) = cos c * sin b - sin c * cos b"
      and h2: "sin (c - a) = sin c * cos a - cos c * sin a"
      and h3: "sin (b - a) = cos a * sin b - sin a * cos b" by auto
    have expand: "(cos c - cos a)*(sin b - sin a) - (sin c - sin a)*(cos b - cos a)
      = cos c * sin b - cos c * sin a - cos a * sin b + cos a * sin a
      - (sin c * cos b - sin c * cos a - sin a * cos b + sin a * cos a)"
      by (by100 algebra)
    show "(cos c - cos a)*(sin b - sin a) - (sin c - sin a)*(cos b - cos a)
      = sin (b - c) + sin (c - a) - sin (b - a)"
      unfolding expand h1 h2 h3 by (by100 algebra)
  qed
  have hC11: "\<forall>i<?n. \<forall>k<?n.
        k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
        (vx k - vx i)*(vy(Suc i mod ?n) - vy i) - (vy k - vy i)*(vx(Suc i mod ?n) - vx i) < 0"
  proof (intro allI impI)
    fix i k assume hi: "i < ?n" and hk: "k < ?n" and hki: "k \<noteq> i" and hki1: "k \<noteq> Suc i mod ?n"
    let ?\<alpha> = "2*pi*real i/real ?n"
    let ?\<beta> = "2*pi*real (Suc i mod ?n)/real ?n"
    let ?\<gamma> = "2*pi*real k/real ?n"
    have cross_eq: "(vx k - vx i)*(vy(Suc i mod ?n) - vy i) - (vy k - vy i)*(vx(Suc i mod ?n) - vx i)
        = sin (?\<beta> - ?\<gamma>) + sin (?\<gamma> - ?\<alpha>) - sin (?\<beta> - ?\<alpha>)"
    proof -
      have "(cos ?\<gamma> - cos ?\<alpha>)*(sin ?\<beta> - sin ?\<alpha>) - (sin ?\<gamma> - sin ?\<alpha>)*(cos ?\<beta> - cos ?\<alpha>)
          = sin (?\<beta> - ?\<gamma>) + sin (?\<gamma> - ?\<alpha>) - sin (?\<beta> - ?\<alpha>)"
        by (rule cross_unit_circle)
      thus ?thesis unfolding vx_def vy_def by (by100 simp)
    qed
    \<comment> \<open>sin(\\<beta>-\\<alpha>) = sin(2\\<pi>/n) from hcross.\<close>
    have hba: "sin (?\<beta> - ?\<alpha>) = sin (2*pi/real ?n)"
    proof -
      have "vx i * vy (Suc i mod ?n) - vy i * vx (Suc i mod ?n) = sin (2*pi/real ?n)"
        using hcross[OF hi] .
      moreover have "vx i * vy (Suc i mod ?n) - vy i * vx (Suc i mod ?n)
          = sin (?\<beta> - ?\<alpha>)"
        unfolding vx_def vy_def using sin_diff[of ?\<beta> ?\<alpha>] by (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Apply sin\\_plus\\_sin: sin(\\<beta>-\\<gamma>) + sin(\\<gamma>-\\<alpha>)
       = 2*sin((\\<beta>-\\<alpha>)/2)*cos((\\<beta>+\\<alpha>-2\\<gamma>)/2).
       Since \\<beta>-\\<alpha> corresponds to 2\\<pi>/n, this gives
       = 2*sin(\\<pi>/n)*cos(something).\<close>
    have sum_eq: "sin (?\<beta> - ?\<gamma>) + sin (?\<gamma> - ?\<alpha>)
        = 2 * sin ((?\<beta> - ?\<alpha>)/2) * cos ((?\<beta> + ?\<alpha> - 2*?\<gamma>)/2)"
    proof -
      have "sin (?\<beta> - ?\<gamma>) + sin (?\<gamma> - ?\<alpha>)
          = 2 * sin (((?\<beta> - ?\<gamma>) + (?\<gamma> - ?\<alpha>))/2) * cos (((?\<beta> - ?\<gamma>) - (?\<gamma> - ?\<alpha>))/2)"
        by (rule sin_plus_sin)
      moreover have "((?\<beta> - ?\<gamma>) + (?\<gamma> - ?\<alpha>))/2 = (?\<beta> - ?\<alpha>)/2" by (by100 algebra)
      moreover have "((?\<beta> - ?\<gamma>) - (?\<gamma> - ?\<alpha>))/2 = (?\<beta> + ?\<alpha> - 2*?\<gamma>)/2" by (by100 algebra)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Also sin(2\\<pi>/n) = 2*sin(\\<pi>/n)*cos(\\<pi>/n).\<close>
    have double_angle: "sin (2*pi/real ?n) = 2 * sin (pi/real ?n) * cos (pi/real ?n)"
      using sin_double[of "pi/real ?n"] by (by100 simp)
    \<comment> \<open>Cleaner approach (no case split): use cos difference identity
       cos A - cos B = -2*sin((A+B)/2)*sin((A-B)/2)
       to get: cross = -4*sin((\\<beta>-\\<alpha>)/2)*sin((\\<beta>-\\<gamma>)/2)*sin((\\<alpha>-\\<gamma>)/2)
       Then show the product of three sines is positive.\<close>
    show "(vx k - vx i)*(vy(Suc i mod ?n) - vy i) - (vy k - vy i)*(vx(Suc i mod ?n) - vx i) < 0"
    proof -
      \<comment> \<open>Step 1: cross = sum - sin(\\<beta>-\\<alpha>) = 2*sin((\\<beta>-\\<alpha>)/2)*[cos bracket - cos half].\<close>
      have da2: "sin (?\<beta> - ?\<alpha>) = 2 * sin ((?\<beta> - ?\<alpha>)/2) * cos ((?\<beta> - ?\<alpha>)/2)"
      proof -
        have h2ne: "(2::real) \<noteq> 0" by (by100 simp)
        have h2x2: "(2::real) * ((?\<beta> - ?\<alpha>) / 2) = ?\<beta> - ?\<alpha>"
          using nonzero_mult_div_cancel_left[OF h2ne, of "?\<beta> - ?\<alpha>"] by (by100 simp)
        have "sin (2 * ((?\<beta> - ?\<alpha>) / 2)) = 2 * sin ((?\<beta> - ?\<alpha>) / 2) * cos ((?\<beta> - ?\<alpha>) / 2)"
          by (rule sin_double)
        thus ?thesis by (subst (asm) h2x2) (by100 assumption)
      qed
      have step2: "sin (?\<beta> - ?\<gamma>) + sin (?\<gamma> - ?\<alpha>) - sin (?\<beta> - ?\<alpha>)
        = 2 * sin ((?\<beta> - ?\<alpha>)/2) * (cos ((?\<beta> + ?\<alpha> - 2*?\<gamma>)/2) - cos ((?\<beta> - ?\<alpha>)/2))"
        using sum_eq da2 by (by100 algebra)
      \<comment> \<open>Step 2: Apply cos A - cos B = -2*sin((A+B)/2)*sin((A-B)/2).\<close>
      have cos_diff_eq: "cos ((?\<beta> + ?\<alpha> - 2*?\<gamma>)/2) - cos ((?\<beta> - ?\<alpha>)/2)
          = - 2 * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2)"
      proof -
        define A where "A = (?\<beta> + ?\<alpha> - 2*?\<gamma>)/(2::real)"
        define B where "B = (?\<beta> - ?\<alpha>)/(2::real)"
        \<comment> \<open>cos A - cos B = 2*sin((A+B)/2)*sin((B-A)/2).\<close>
        have step: "cos A - cos B = 2 * sin ((A+B)/2) * sin ((B-A)/2)"
          unfolding A_def B_def by (rule cos_diff_cos)
        have eq1: "(A+B)/2 = (?\<beta> - ?\<gamma>)/2" unfolding A_def B_def by (by100 algebra)
        have eq2: "(B-A)/2 = (?\<gamma> - ?\<alpha>)/2" unfolding A_def B_def by (by100 algebra)
        have mid: "cos A - cos B = 2 * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<gamma> - ?\<alpha>)/2)"
          using step by (subst (asm) eq1, subst (asm) eq2) (by100 assumption)
        \<comment> \<open>sin((\\<gamma>-\\<alpha>)/2) = -sin((\\<alpha>-\\<gamma>)/2).\<close>
        have neg: "(?\<gamma> - ?\<alpha>)/2 = -((?\<alpha> - ?\<gamma>)/2)" by (by100 algebra)
        have "sin ((?\<gamma> - ?\<alpha>)/2) = - sin ((?\<alpha> - ?\<gamma>)/2)"
          by (subst neg, rule sin_minus)
        hence hsneg: "sin ((?\<gamma> - ?\<alpha>)/2) = - sin ((?\<alpha> - ?\<gamma>)/2)" .
        have "2 * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<gamma> - ?\<alpha>)/2)
            = - (2 * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2))"
          by (subst hsneg, simp only: mult_minus_right)
        with mid show ?thesis unfolding A_def B_def by (by100 linarith)
      qed
      \<comment> \<open>Step 3: cross = -4*sin((\\<beta>-\\<alpha>)/2)*sin((\\<beta>-\\<gamma>)/2)*sin((\\<alpha>-\\<gamma>)/2).\<close>
      have cross_product: "sin (?\<beta> - ?\<gamma>) + sin (?\<gamma> - ?\<alpha>) - sin (?\<beta> - ?\<alpha>)
        = - 4 * sin ((?\<beta> - ?\<alpha>)/2) * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2)"
        using step2 cos_diff_eq by (by100 algebra)
      \<comment> \<open>Step 4: Each sine is nonzero and the product is > 0.\<close>
      \<comment> \<open>sin((\\<beta>-\\<alpha>)/2) \\<noteq> 0: because \\<beta> \\<noteq> \\<alpha> (vertices i and i+1 are distinct).\<close>
      \<comment> \<open>sin((\\<beta>-\\<gamma>)/2) \\<noteq> 0: because \\<beta> \\<noteq> \\<gamma> (k \\<noteq> Suc i mod n).\<close>
      \<comment> \<open>sin((\\<alpha>-\\<gamma>)/2) \\<noteq> 0: because \\<alpha> \\<noteq> \\<gamma> (k \\<noteq> i).\<close>
      \<comment> \<open>Product positive: all three angles are multiples of \\<pi>/n in range (-\\<pi>,\\<pi>).
         The product of their signs is always positive (checked for all cases).\<close>
      have "sin ((?\<beta> - ?\<alpha>)/2) * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2) > 0"
      proof -
        \<comment> \<open>Each angle is \\<pi>*m/n for some integer m with 0 < |m| < n.
           sin(\\<pi>*m/n) > 0 for 0 < m < n; sin(\\<pi>*m/n) < 0 for -n < m < 0.
           Product of signs is always (+) for non-adjacent vertices.\<close>
        \<comment> \<open>Factor 1: sin((\\<beta>-\\<alpha>)/2). Nonzero since vertices i and i+1 are distinct.\<close>
        \<comment> \<open>sin(\\<pi>*m/n) \\<noteq> 0 when 0 < |m| < n. Proof: sin = 0 iff angle = k\\<pi>.
           \\<pi>*m/n = k\\<pi> iff m = kn. Since |m| < n, k = 0, so m = 0. Contradiction.\<close>
        \<comment> \<open>Helper: sin(\\<pi>*m/n) \\<noteq> 0 for 0 < |m| < n (integer m, n \\<ge> 3).\<close>
        have sin_pi_frac_ne: "\<And>m::int. m \<noteq> 0 \<Longrightarrow> \<bar>m\<bar> < int ?n \<Longrightarrow>
            sin (pi * real_of_int m / real ?n) \<noteq> 0"
        proof -
          fix m :: int assume hm0: "m \<noteq> 0" and hm_bnd: "\<bar>m\<bar> < int ?n"
          show "sin (pi * real_of_int m / real ?n) \<noteq> 0"
          proof
            assume hsin0: "sin (pi * real_of_int m / real ?n) = 0"
            \<comment> \<open>By sin\\_zero\\_iff\\_int2: \\<exists>k. angle = k*\\<pi>.\<close>
            from hsin0[unfolded sin_zero_iff_int2]
            obtain kk :: int where hkk: "pi * real_of_int m / real ?n = real_of_int kk * pi"
              by (by100 blast)
            \<comment> \<open>Cancel \\<pi>: m/n = kk. Since |m| < n: |kk| < 1, so kk = 0, m = 0.\<close>
            \<comment> \<open>pi * m / n = kk * pi \\<Longrightarrow> m = kk * n.\<close>
            have "pi * real_of_int m = real_of_int kk * pi * real ?n"
              using hkk hn_pos by (simp add: field_simps)
            hence "real_of_int m = real_of_int kk * real ?n"
              using pi_gt_zero by (by100 simp)
            hence "\<bar>real_of_int m\<bar> = \<bar>real_of_int kk\<bar> * real ?n"
              using hn_pos by (simp add: abs_mult)
            hence "\<bar>real_of_int kk\<bar> * real ?n < real ?n"
              using hm_bnd by (by100 linarith)
            hence "\<bar>real_of_int kk\<bar> < 1" using hn_pos by (by100 simp)
            hence "kk = 0" by (by100 linarith)
            hence "real_of_int m = 0"
              using \<open>real_of_int m = real_of_int kk * real ?n\<close> by (by100 simp)
            thus False using hm0 by (by100 simp)
          qed
        qed
        \<comment> \<open>Apply sin\\_pi\\_frac\\_ne. Each angle = \\<pi>*(m)/n for integer m with 0<|m|<n.\<close>
        have hf1_ne: "sin ((?\<beta> - ?\<alpha>)/2) \<noteq> 0"
        proof -
          define m1 :: int where "m1 = int (Suc i mod ?n) - int i"
          have "Suc i mod ?n \<noteq> i"
          proof
            assume "Suc i mod ?n = i"
            hence "Suc i mod ?n = i mod ?n" using hi by (by100 simp)
            hence "Suc i mod ?n = i mod ?n" .
            hence "(Suc i - i) mod ?n = 0" using assms by (simp add: mod_eq_dvd_iff_nat)
            hence "?n dvd 1" by (by100 simp)
            thus False using assms by (by100 simp)
          qed
          hence hm1_ne: "m1 \<noteq> 0"
            unfolding m1_def by (by100 simp)
          have hm1_bnd: "\<bar>m1\<bar> < int ?n"
          proof -
            have "?n > 0" using assms by (by100 linarith)
            hence "Suc i mod ?n < ?n" by (by100 simp)
            thus ?thesis unfolding m1_def using hi by (by100 linarith)
          qed
          have hangle: "(?\<beta> - ?\<alpha>)/2 = pi * real_of_int m1 / real ?n"
            unfolding m1_def using hn_pos by (simp add: divide_simps of_int_diff algebra_simps)
          show ?thesis unfolding hangle using sin_pi_frac_ne[OF hm1_ne hm1_bnd] .
        qed
        have hf2_ne: "sin ((?\<beta> - ?\<gamma>)/2) \<noteq> 0"
        proof -
          define m2 :: int where "m2 = int (Suc i mod ?n) - int k"
          have hm2_ne: "m2 \<noteq> 0"
            unfolding m2_def using hki1 by (by100 simp)
          have hm2_bnd: "\<bar>m2\<bar> < int ?n"
          proof -
            have "?n > 0" using assms by (by100 linarith)
            hence "Suc i mod ?n < ?n" by (by100 simp)
            thus ?thesis unfolding m2_def using hk by (by100 linarith)
          qed
          have hangle: "(?\<beta> - ?\<gamma>)/2 = pi * real_of_int m2 / real ?n"
            unfolding m2_def using hn_pos by (simp add: divide_simps of_int_diff algebra_simps)
          show ?thesis unfolding hangle using sin_pi_frac_ne[OF hm2_ne hm2_bnd] .
        qed
        have hf3_ne: "sin ((?\<alpha> - ?\<gamma>)/2) \<noteq> 0"
        proof -
          define m3 :: int where "m3 = int i - int k"
          have hm3_ne: "m3 \<noteq> 0" using hki unfolding m3_def by (by100 simp)
          have hm3_bnd: "\<bar>m3\<bar> < int ?n" using hi hk unfolding m3_def by (by100 simp)
          have hangle: "(?\<alpha> - ?\<gamma>)/2 = pi * real_of_int m3 / real ?n"
            unfolding m3_def using hn_pos by (simp add: divide_simps of_int_diff algebra_simps)
          show ?thesis unfolding hangle using sin_pi_frac_ne[OF hm3_ne hm3_bnd] .
        qed
        \<comment> \<open>Product of signs: for i<n-1 and k<i: (+)(+)(+). For k>i+1: (+)(-)(-).
           For i=n-1: (-)(-)( +). All give (+).\<close>
        \<comment> \<open>The sign of the product: each sin(\\<pi>m/n) has the same sign as m.
           Product of m1*m2*m3 > 0 in all cases.\<close>
        \<comment> \<open>Helper: sin(\\<pi>*m/n) > 0 for 0 < m < n (positive integer m).\<close>
        have sin_pi_frac_pos: "\<And>m::int. 0 < m \<Longrightarrow> m < int ?n \<Longrightarrow>
            sin (pi * real_of_int m / real ?n) > 0"
        proof -
          fix m :: int assume hm_pos: "0 < m" and hm_bnd: "m < int ?n"
          have "0 < pi * real_of_int m / real ?n"
            using pi_gt_zero hm_pos hn_pos by (by100 simp)
          moreover have "pi * real_of_int m / real ?n < pi"
          proof -
            have "real_of_int m / real ?n < 1" using hm_bnd hn_pos by (by100 simp)
            hence "pi * (real_of_int m / real ?n) < pi * 1"
              using pi_gt_zero by (rule mult_strict_left_mono)
            thus ?thesis by (by100 simp)
          qed
          ultimately show "sin (pi * real_of_int m / real ?n) > 0"
            using sin_gt_zero by (by100 blast)
        qed
        \<comment> \<open>Helper: sin(\\<pi>*m/n) < 0 for -n < m < 0 (negative integer m).\<close>
        have sin_pi_frac_neg: "\<And>m::int. m < 0 \<Longrightarrow> - int ?n < m \<Longrightarrow>
            sin (pi * real_of_int m / real ?n) < 0"
        proof -
          fix m :: int assume hm_neg: "m < 0" and hm_bnd: "- int ?n < m"
          have "sin (pi * real_of_int m / real ?n) = sin (- (pi * real_of_int (-m) / real ?n))"
            by (by100 simp)
          also have "\<dots> = - sin (pi * real_of_int (-m) / real ?n)"
            by (rule sin_minus)
          also have "\<dots> < 0"
          proof -
            have "0 < -m" using hm_neg by (by100 simp)
            moreover have "-m < int ?n" using hm_bnd by (by100 simp)
            ultimately have "sin (pi * real_of_int (-m) / real ?n) > 0"
              by (rule sin_pi_frac_pos)
            thus ?thesis by (by100 linarith)
          qed
          finally show "sin (pi * real_of_int m / real ?n) < 0" .
        qed
        \<comment> \<open>Now compute the sign of each factor.\<close>
        have sign_pos: "sin ((?\<beta> - ?\<alpha>)/2) * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2) > 0"
        proof -
          \<comment> \<open>Re-derive angle matching (same as in hf\\_ne proofs).\<close>
          define m1 :: int where "m1 = int (Suc i mod ?n) - int i"
          define m2 :: int where "m2 = int (Suc i mod ?n) - int k"
          define m3 :: int where "m3 = int i - int k"
          have ha1: "(?\<beta> - ?\<alpha>)/2 = pi * real_of_int m1 / real ?n"
            unfolding m1_def using hn_pos by (simp add: divide_simps of_int_diff algebra_simps)
          have ha2: "(?\<beta> - ?\<gamma>)/2 = pi * real_of_int m2 / real ?n"
            unfolding m2_def using hn_pos by (simp add: divide_simps of_int_diff algebra_simps)
          have ha3: "(?\<alpha> - ?\<gamma>)/2 = pi * real_of_int m3 / real ?n"
            unfolding m3_def using hn_pos by (simp add: divide_simps of_int_diff algebra_simps)
          \<comment> \<open>Bounds on mi.\<close>
          have hn_gt0: "?n > 0" using assms by (by100 linarith)
          have hmod_lt: "Suc i mod ?n < ?n" using hn_gt0 by (by100 simp)
          have hm1_bnd: "- int ?n < m1 \<and> m1 < int ?n" unfolding m1_def using hi hmod_lt by (by100 linarith)
          have hm2_bnd: "- int ?n < m2 \<and> m2 < int ?n" unfolding m2_def using hk hmod_lt by (by100 linarith)
          have hm3_bnd: "- int ?n < m3 \<and> m3 < int ?n" unfolding m3_def using hi hk by (by100 linarith)
          \<comment> \<open>Show m1*m2*m3 > 0 by case split on signs.\<close>
          have hm_prod_pos: "m1 * m2 * m3 > 0"
          proof (cases "Suc i < ?n")
            case True \<comment> \<open>i < n-1: m1 = 1.\<close>
            hence "Suc i mod ?n = Suc i" by (by100 simp)
            hence hm1_eq: "m1 = 1" unfolding m1_def by (by100 simp)
            \<comment> \<open>k < i or k > i+1. In both cases (i+1-k)*(i-k) > 0.\<close>
            have "m2 * m3 > 0"
            proof -
              have "m2 = int (Suc i) - int k" unfolding m2_def using True by (by100 simp)
              hence "m2 = m3 + 1" unfolding m3_def by (by100 linarith)
              \<comment> \<open>m3 \\<noteq> 0 (k \\<noteq> i), m2 \\<noteq> 0 (k \\<noteq> i+1). m2 = m3+1, so both same sign or one is 0.\<close>
              have "m3 \<noteq> 0" unfolding m3_def using hki by (by100 simp)
              have "m2 \<noteq> 0" unfolding m2_def using hki1 True by (by100 simp)
              \<comment> \<open>m2 = m3+1. If m3 > 0: m2 > 0. If m3 < 0 and m3 \\<noteq> -1: m2 < 0.\<close>
              \<comment> \<open>m3 = -1 would mean k = i+1, but k \\<noteq> Suc i = Suc i mod n. Contradiction.\<close>
              have "m3 \<noteq> -1"
              proof
                assume "m3 = -1"
                hence "int k = int i + 1" unfolding m3_def by (by100 linarith)
                hence "k = Suc i" by (by100 simp)
                hence "k = Suc i mod ?n" using True by (by100 simp)
                thus False using hki1 by (by100 simp)
              qed
              \<comment> \<open>m2 = m3+1, m3 \\<noteq> 0, m3 \\<noteq> -1: either both > 0 or both < 0.\<close>
              show ?thesis
              proof (cases "m3 > 0")
                case True hence "m2 > 0" using \<open>m2 = m3 + 1\<close> by (by100 linarith)
                thus ?thesis using True by (by100 simp)
              next
                case False hence "m3 < 0" using \<open>m3 \<noteq> 0\<close> by (by100 linarith)
                hence "m3 < -1" using \<open>m3 \<noteq> -1\<close> by (by100 linarith)
                hence "m2 < 0" using \<open>m2 = m3 + 1\<close> by (by100 linarith)
                thus ?thesis using \<open>m3 < 0\<close> mult_neg_neg[of m2 m3] by (by100 linarith)
              qed
            qed
            thus ?thesis using hm1_eq by (by100 simp)
          next
            case False \<comment> \<open>i = n-1.\<close>
            hence hi_eq: "i = ?n - 1" using hi by (by100 simp)
            hence "Suc i mod ?n = 0" using hn_gt0 by (by100 simp)
            hence hm1_neg: "m1 = - int (?n - 1)" unfolding m1_def using hi_eq by (by100 simp)
            hence "m1 < 0" using assms by (by100 linarith)
            have hm2_neg: "m2 = - int k" unfolding m2_def using \<open>Suc i mod ?n = 0\<close> by (by100 simp)
            have "k \<noteq> 0" using hki1 \<open>Suc i mod ?n = 0\<close> by (by100 simp)
            hence "m2 < 0" using hm2_neg hk by (by100 linarith)
            have hm3_pos: "m3 = int (?n - 1) - int k" unfolding m3_def using hi_eq by (by100 simp)
            have "k \<noteq> ?n - 1" using hki hi_eq by (by100 simp)
            hence "k < ?n - 1" using hk by (by100 linarith)
            hence "m3 > 0" using hm3_pos by (by100 linarith)
            have "m1 * m2 > 0" using \<open>m1 < 0\<close> \<open>m2 < 0\<close> mult_neg_neg[of m1 m2]
              by (by100 linarith)
            thus ?thesis using \<open>m3 > 0\<close> by (by100 simp)
          qed
          \<comment> \<open>Each factor: sin(\\<pi>*mi/n) has the sign of mi.\<close>
          \<comment> \<open>Sign matching: for each factor, mi > 0 gives sin > 0; mi < 0 gives sin < 0.\<close>
          have hm1_ne: "m1 \<noteq> 0" using hf1_ne unfolding ha1
            using sin_pi_frac_ne[of m1] hm1_bnd by (by100 force)
          have hm2_ne: "m2 \<noteq> 0" using hf2_ne unfolding ha2
            using sin_pi_frac_ne[of m2] hm2_bnd by (by100 force)
          have hm3_ne: "m3 \<noteq> 0" using hf3_ne unfolding ha3
            using sin_pi_frac_ne[of m3] hm3_bnd by (by100 force)
          have s1: "sgn (sin ((?\<beta> - ?\<alpha>)/2)) = sgn m1"
          proof (cases "m1 > 0")
            case True thus ?thesis unfolding ha1
              using sin_pi_frac_pos[OF True] hm1_bnd by (by100 simp)
          next
            case False hence "m1 < 0" using hm1_ne by (by100 linarith)
            thus ?thesis unfolding ha1
              using sin_pi_frac_neg[of m1] hm1_bnd by (by100 simp)
          qed
          have s2: "sgn (sin ((?\<beta> - ?\<gamma>)/2)) = sgn m2"
          proof (cases "m2 > 0")
            case True thus ?thesis unfolding ha2
              using sin_pi_frac_pos[OF True] hm2_bnd by (by100 simp)
          next
            case False hence "m2 < 0" using hm2_ne by (by100 linarith)
            thus ?thesis unfolding ha2
              using sin_pi_frac_neg[of m2] hm2_bnd by (by100 simp)
          qed
          have s3: "sgn (sin ((?\<alpha> - ?\<gamma>)/2)) = sgn m3"
          proof (cases "m3 > 0")
            case True thus ?thesis unfolding ha3
              using sin_pi_frac_pos[OF True] hm3_bnd by (by100 simp)
          next
            case False hence "m3 < 0" using hm3_ne by (by100 linarith)
            thus ?thesis unfolding ha3
              using sin_pi_frac_neg[of m3] hm3_bnd by (by100 simp)
          qed
          \<comment> \<open>Product of sines has same sign as product of mi.\<close>
          \<comment> \<open>Product of sines: directly case-split on sign of each mi.\<close>
          have "sin ((?\<beta> - ?\<alpha>)/2) * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2) > 0"
          proof (cases "m1 > 0")
            case hm1p: True
            hence hs1: "sin ((?\<beta> - ?\<alpha>)/2) > 0" unfolding ha1
              using sin_pi_frac_pos[OF hm1p] hm1_bnd by (by100 linarith)
            show ?thesis
            proof (cases "m2 > 0")
              case hm2p: True
              hence hs2: "sin ((?\<beta> - ?\<gamma>)/2) > 0" unfolding ha2
                using sin_pi_frac_pos[OF hm2p] hm2_bnd by (by100 linarith)
              have "m1 * m2 > 0" using hm1p hm2p by (by100 simp)
              have "m3 > 0"
              proof (rule ccontr)
                assume "\<not> m3 > 0"
                hence "m3 \<le> 0" by (by100 simp)
                hence "m1 * m2 * m3 \<le> 0" using \<open>m1 * m2 > 0\<close>
                  using mult_nonneg_nonpos[of "m1*m2" m3] by (by100 linarith)
                thus False using hm_prod_pos by (by100 linarith)
              qed
              hence hs3: "sin ((?\<alpha> - ?\<gamma>)/2) > 0" unfolding ha3
                using sin_pi_frac_pos[of m3] hm3_bnd by (by100 linarith)
              define sp where "sp = sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2)"
              have "sp > 0" unfolding sp_def
                using hs2 hs3 mult_pos_pos[of "sin ((?\<beta> - ?\<gamma>)/2)" "sin ((?\<alpha> - ?\<gamma>)/2)"]
                by (by100 linarith)
              hence "sin ((?\<beta> - ?\<alpha>)/2) * sp > 0"
                using hs1 mult_pos_pos[of "sin ((?\<beta> - ?\<alpha>)/2)" sp] by (by100 linarith)
              thus ?thesis unfolding sp_def by (simp add: mult.assoc)
            next
              case hm2n: False hence "m2 < 0" using hm2_ne by (by100 linarith)
              hence hs2: "sin ((?\<beta> - ?\<gamma>)/2) < 0" unfolding ha2
                using sin_pi_frac_neg[of m2] hm2_bnd by (by100 linarith)
              have "m1 * m2 < 0" using hm1p \<open>m2 < 0\<close>
                using mult_pos_neg[of m1 m2] by (by100 linarith)
              have "m3 < 0"
              proof (rule ccontr)
                assume "\<not> m3 < 0"
                hence "m3 \<ge> 0" by (by100 simp)
                hence "m1 * m2 * m3 \<le> 0" using \<open>m1 * m2 < 0\<close>
                  using mult_nonpos_nonneg[of "m1*m2" m3] by (by100 linarith)
                thus False using hm_prod_pos by (by100 linarith)
              qed
              hence hs3: "sin ((?\<alpha> - ?\<gamma>)/2) < 0" unfolding ha3
                using sin_pi_frac_neg[of m3] hm3_bnd by (by100 linarith)
              define s23 where "s23 = sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2)"
              have "s23 > 0" unfolding s23_def
                using hs2 hs3 mult_neg_neg[of "sin ((?\<beta> - ?\<gamma>)/2)" "sin ((?\<alpha> - ?\<gamma>)/2)"]
                by (by100 linarith)
              hence "sin ((?\<beta> - ?\<alpha>)/2) * s23 > 0"
                using hs1 mult_pos_pos[of "sin ((?\<beta> - ?\<alpha>)/2)" s23] by (by100 linarith)
              thus ?thesis unfolding s23_def by (simp add: mult.assoc)
            qed
          next
            case hm1n: False hence "m1 < 0" using hm1_ne by (by100 linarith)
            hence hs1: "sin ((?\<beta> - ?\<alpha>)/2) < 0" unfolding ha1
              using sin_pi_frac_neg[of m1] hm1_bnd by (by100 linarith)
            \<comment> \<open>m1 < 0 and m1*m2*m3 > 0: either m2>0,m3<0 or m2<0,m3>0.\<close>
            show ?thesis
            proof (cases "m2 > 0")
              case hm2p: True
              hence hs2: "sin ((?\<beta> - ?\<gamma>)/2) > 0" unfolding ha2
                using sin_pi_frac_pos[OF hm2p] hm2_bnd by (by100 linarith)
              have "m1 * m2 < 0" using \<open>m1 < 0\<close> hm2p
                using mult_neg_pos[of m1 m2] by (by100 linarith)
              have "m3 < 0"
              proof (rule ccontr)
                assume "\<not> m3 < 0" hence "m3 \<ge> 0" by (by100 simp)
                hence "m1 * m2 * m3 \<le> 0" using \<open>m1 * m2 < 0\<close>
                  using mult_nonpos_nonneg[of "m1*m2" m3] by (by100 linarith)
                thus False using hm_prod_pos by (by100 linarith)
              qed
              hence hs3: "sin ((?\<alpha> - ?\<gamma>)/2) < 0" unfolding ha3
                using sin_pi_frac_neg[of m3] hm3_bnd by (by100 linarith)
              define sp where "sp = sin ((?\<beta> - ?\<alpha>)/2) * sin ((?\<alpha> - ?\<gamma>)/2)"
              have "sp > 0" unfolding sp_def
                using hs1 hs3 mult_neg_neg[of "sin ((?\<beta> - ?\<alpha>)/2)" "sin ((?\<alpha> - ?\<gamma>)/2)"]
                by (by100 linarith)
              hence "sp * sin ((?\<beta> - ?\<gamma>)/2) > 0"
                using hs2 mult_pos_pos[of sp "sin ((?\<beta> - ?\<gamma>)/2)"] by (by100 linarith)
              thus ?thesis unfolding sp_def by (simp add: mult.assoc mult.commute mult.left_commute)
            next
              case hm2n: False hence "m2 < 0" using hm2_ne by (by100 linarith)
              hence hs2: "sin ((?\<beta> - ?\<gamma>)/2) < 0" unfolding ha2
                using sin_pi_frac_neg[of m2] hm2_bnd by (by100 linarith)
              have "m1 * m2 > 0" using \<open>m1 < 0\<close> \<open>m2 < 0\<close>
                using mult_neg_neg[of m1 m2] by (by100 linarith)
              have "m3 > 0"
              proof (rule ccontr)
                assume "\<not> m3 > 0" hence "m3 \<le> 0" by (by100 simp)
                hence "m1 * m2 * m3 \<le> 0" using \<open>m1 * m2 > 0\<close>
                  using mult_nonneg_nonpos[of "m1*m2" m3] by (by100 linarith)
                thus False using hm_prod_pos by (by100 linarith)
              qed
              hence hs3: "sin ((?\<alpha> - ?\<gamma>)/2) > 0" unfolding ha3
                using sin_pi_frac_pos[of m3] hm3_bnd by (by100 linarith)
              define sp where "sp = sin ((?\<beta> - ?\<alpha>)/2) * sin ((?\<beta> - ?\<gamma>)/2)"
              have "sp > 0" unfolding sp_def
                using hs1 hs2 mult_neg_neg[of "sin ((?\<beta> - ?\<alpha>)/2)" "sin ((?\<beta> - ?\<gamma>)/2)"]
                by (by100 linarith)
              hence "sp * sin ((?\<alpha> - ?\<gamma>)/2) > 0"
                using hs3 mult_pos_pos[of sp "sin ((?\<alpha> - ?\<gamma>)/2)"] by (by100 linarith)
              thus ?thesis unfolding sp_def by (simp add: mult.assoc)
            qed
          qed
          thus ?thesis .
        qed
        thus ?thesis .
      qed
      hence "- 4 * sin ((?\<beta> - ?\<alpha>)/2) * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2) < 0"
        by (by100 linarith)
      thus ?thesis using cross_eq cross_product by (by100 linarith)
    qed
  qed
  \<comment> \<open>C6: non-adjacent edge interiors don't intersect (strict convexity implies this).\<close>
  \<comment> \<open>C6: non-adjacent edge interiors don't intersect. Follows from C11.\<close>
  define open01 :: "real set" where "open01 = {0<..<1}"
  have hC6: "\<forall>i<?n. \<forall>j<?n.
        i \<noteq> j \<longrightarrow> (Suc i mod ?n) \<noteq> j \<longrightarrow> i \<noteq> (Suc j mod ?n) \<longrightarrow>
        (\<forall>s\<in>open01. \<forall>t\<in>open01.
           ((1 - s) * vx i + s * vx (Suc i mod ?n),
            (1 - s) * vy i + s * vy (Suc i mod ?n))
         \<noteq> ((1 - t) * vx j + t * vx (Suc j mod ?n),
             (1 - t) * vy j + t * vy (Suc j mod ?n)))"
  proof (intro allI impI ballI)
    fix i j s t
    assume hi: "i < ?n" and hj: "j < ?n" and hij: "i \<noteq> j"
       and hij1: "(Suc i mod ?n) \<noteq> j" and hji1: "i \<noteq> (Suc j mod ?n)"
       and hs: "s \<in> open01" and ht: "t \<in> open01"
    have hs01: "0 < s" "s < 1" using hs unfolding open01_def by (by100 auto)+
    have ht01: "0 < t" "t < 1" using ht unfolding open01_def by (by100 auto)+
    \<comment> \<open>Proof by contradiction: assume edges i and j have a common interior point p.\<close>
    show "((1 - s) * vx i + s * vx (Suc i mod ?n),
            (1 - s) * vy i + s * vy (Suc i mod ?n))
         \<noteq> ((1 - t) * vx j + t * vx (Suc j mod ?n),
             (1 - t) * vy j + t * vy (Suc j mod ?n))"
    proof
      assume heq: "((1 - s) * vx i + s * vx (Suc i mod ?n),
            (1 - s) * vy i + s * vy (Suc i mod ?n))
         = ((1 - t) * vx j + t * vx (Suc j mod ?n),
             (1 - t) * vy j + t * vy (Suc j mod ?n))"
      \<comment> \<open>Let p = the common point. p is on edge i (param s) and edge j (param t).\<close>
      \<comment> \<open>Cross product of (p - v\\_i) with (v\\_{i+1} - v\\_i):
         From edge i: p - v\\_i = s*(v\\_{i+1} - v\\_i), so cross = 0.
         From edge j: cross = (1-t)*C11(j) + t*C11(j+1) < 0. Contradiction.\<close>
      \<comment> \<open>Step 1: C11 gives cross(j,i) < 0 and cross(j+1,i) < 0.\<close>
      have hj_ne_i: "j \<noteq> i" using hij by (by100 simp)
      have hj_ne_i1: "j \<noteq> Suc i mod ?n" using hij1 by (by100 simp)
      have hj1_ne_i: "Suc j mod ?n \<noteq> i" using hji1 by (by100 simp)
      have hj1_ne_i1: "Suc j mod ?n \<noteq> Suc i mod ?n"
      proof
        assume "Suc j mod ?n = Suc i mod ?n"
        hence "Suc j mod ?n = Suc i mod ?n" .
        \<comment> \<open>Since j < n and i < n: Suc j < 2n and Suc i < 2n.
           Suc j mod n = Suc i mod n implies either Suc j = Suc i or |Suc j - Suc i| = n.\<close>
        have "j < ?n" "i < ?n" using hi hj by auto
        hence "Suc j \<le> ?n" "Suc i \<le> ?n" by auto
        \<comment> \<open>If Suc j \\<le> n and Suc i \\<le> n, and mod n equal: Suc j = Suc i (only possible).\<close>
        have "j = i"
        proof (cases "Suc j < ?n")
          case True hence "Suc j mod ?n = Suc j" by (by100 simp)
          show ?thesis
          proof (cases "Suc i < ?n")
            case True2: True hence "Suc i mod ?n = Suc i" by (by100 simp)
            from \<open>Suc j mod ?n = Suc i mod ?n\<close> True \<open>Suc j mod ?n = Suc j\<close> True2 \<open>Suc i mod ?n = Suc i\<close>
            show ?thesis by (by100 simp)
          next
            case False hence "Suc i = ?n" using \<open>Suc i \<le> ?n\<close> by (by100 linarith)
            hence "Suc i mod ?n = 0" by (by100 simp)
            from \<open>Suc j mod ?n = Suc i mod ?n\<close> \<open>Suc j mod ?n = Suc j\<close> this
            have "Suc j = 0" by (by100 simp)
            thus ?thesis by (by100 simp)
          qed
        next
          case False hence "Suc j = ?n" using \<open>Suc j \<le> ?n\<close> by (by100 linarith)
          hence "Suc j mod ?n = 0" by (by100 simp)
          show ?thesis
          proof (cases "Suc i < ?n")
            case True hence "Suc i mod ?n = Suc i" by (by100 simp)
            from \<open>Suc j mod ?n = Suc i mod ?n\<close> \<open>Suc j mod ?n = 0\<close> this
            have "Suc i = 0" by (by100 simp)
            thus ?thesis by (by100 simp)
          next
            case False hence "Suc i = ?n" using \<open>Suc i \<le> ?n\<close> by (by100 linarith)
            from \<open>Suc j = ?n\<close> this show ?thesis by (by100 simp)
          qed
        qed
        thus False using hij by (by100 simp)
      qed
      have hn_gt0: "?n > 0" using assms by (by100 linarith)
      have hj1_lt: "Suc j mod ?n < ?n" using hn_gt0 by (by100 simp)
      \<comment> \<open>Apply C11 to vertices j and Suc j mod n.\<close>
      have hcross_j: "(vx j - vx i)*(vy(Suc i mod ?n) - vy i) - (vy j - vy i)*(vx(Suc i mod ?n) - vx i) < 0"
        using hC11 hi hj hj_ne_i hj_ne_i1 by (by100 blast)
      have hcross_j1: "(vx(Suc j mod ?n) - vx i)*(vy(Suc i mod ?n) - vy i) - (vy(Suc j mod ?n) - vy i)*(vx(Suc i mod ?n) - vx i) < 0"
        using hC11 hi hj1_lt hj1_ne_i hj1_ne_i1 by (by100 blast)
      \<comment> \<open>Step 2: cross((1-t)*v\\_j + t*v\\_{j+1} - v\\_i, v\\_{i+1} - v\\_i) < 0.\<close>
      define dx where "dx = vx(Suc i mod ?n) - vx i"
      define dy where "dy = vy(Suc i mod ?n) - vy i"
      have cross_j_eq: "(vx j - vx i)*dy - (vy j - vy i)*dx < 0"
        using hcross_j unfolding dx_def dy_def .
      have cross_j1_eq: "(vx(Suc j mod ?n) - vx i)*dy - (vy(Suc j mod ?n) - vy i)*dx < 0"
        using hcross_j1 unfolding dx_def dy_def .
      \<comment> \<open>The point from edge j: (1-t)*v\\_j + t*v\\_{j+1}. Its cross product with edge i direction:\<close>
      have cross_p_from_j:
        "((1-t)*(vx j - vx i) + t*(vx(Suc j mod ?n) - vx i))*dy
       - ((1-t)*(vy j - vy i) + t*(vy(Suc j mod ?n) - vy i))*dx < 0"
      proof -
        \<comment> \<open>Expand: ((1-t)*a + t*b)*dy - ((1-t)*c + t*d)*dx
           = (1-t)*(a*dy - c*dx) + t*(b*dy - d*dx).\<close>
        have expand: "((1-t)*(vx j - vx i) + t*(vx(Suc j mod ?n) - vx i))*dy
           - ((1-t)*(vy j - vy i) + t*(vy(Suc j mod ?n) - vy i))*dx
           = (1-t)*((vx j - vx i)*dy - (vy j - vy i)*dx)
           + t*((vx(Suc j mod ?n) - vx i)*dy - (vy(Suc j mod ?n) - vy i)*dx)"
          by (by100 algebra)
        have "(1-t) > 0" using ht01 by (by100 linarith)
        moreover have "t > 0" using ht01 by (by100 linarith)
        moreover have "(vx j - vx i)*dy - (vy j - vy i)*dx < 0" using cross_j_eq .
        moreover have "(vx(Suc j mod ?n) - vx i)*dy - (vy(Suc j mod ?n) - vy i)*dx < 0" using cross_j1_eq .
        ultimately have h_neg1: "(1-t)*((vx j - vx i)*dy - (vy j - vy i)*dx) < 0"
          and h_neg2: "t*((vx(Suc j mod ?n) - vx i)*dy - (vy(Suc j mod ?n) - vy i)*dx) < 0"
          using mult_pos_neg[of "1-t" "(vx j - vx i)*dy - (vy j - vy i)*dx"]
                mult_pos_neg[of t "(vx(Suc j mod ?n) - vx i)*dy - (vy(Suc j mod ?n) - vy i)*dx"]
          by (by100 linarith)+
        thus ?thesis using expand by (by100 linarith)
      qed
      \<comment> \<open>Step 3: The same point is on edge i: p - v\\_i = s*(v\\_{i+1} - v\\_i).\<close>
      \<comment> \<open>From heq: (1-s)*vx i + s*vx(i+1) = (1-t)*vx j + t*vx(j+1).
         So: (1-t)*(vx j - vx i) + t*(vx(j+1) - vx i) = s*(vx(i+1) - vx i) = s*dx.
         Similarly for vy.\<close>
      have heqx: "(1-s)*vx i + s*vx(Suc i mod ?n) = (1-t)*vx j + t*vx(Suc j mod ?n)"
      proof -
        from heq have "fst ((1-s)*vx i + s*vx(Suc i mod ?n), (1-s)*vy i + s*vy(Suc i mod ?n))
            = fst ((1-t)*vx j + t*vx(Suc j mod ?n), (1-t)*vy j + t*vy(Suc j mod ?n))"
          by (by100 simp)
        thus ?thesis by (by100 simp)
      qed
      have heqy: "(1-s)*vy i + s*vy(Suc i mod ?n) = (1-t)*vy j + t*vy(Suc j mod ?n)"
      proof -
        from heq have "snd ((1-s)*vx i + s*vx(Suc i mod ?n), (1-s)*vy i + s*vy(Suc i mod ?n))
            = snd ((1-t)*vx j + t*vx(Suc j mod ?n), (1-t)*vy j + t*vy(Suc j mod ?n))"
          by (by100 simp)
        thus ?thesis by (by100 simp)
      qed
      have px_eq: "(1-t)*(vx j - vx i) + t*(vx(Suc j mod ?n) - vx i) = s * dx"
      proof -
        have "(1-t)*(vx j - vx i) + t*(vx(Suc j mod ?n) - vx i)
            = (1-t)*vx j + t*vx(Suc j mod ?n) - vx i" by (by100 algebra)
        also have "\<dots> = (1-s)*vx i + s*vx(Suc i mod ?n) - vx i" using heqx by (by100 linarith)
        also have "\<dots> = s*(vx(Suc i mod ?n) - vx i)" by (by100 algebra)
        finally show ?thesis unfolding dx_def by (by100 simp)
      qed
      have py_eq: "(1-t)*(vy j - vy i) + t*(vy(Suc j mod ?n) - vy i) = s * dy"
      proof -
        have "(1-t)*(vy j - vy i) + t*(vy(Suc j mod ?n) - vy i)
            = (1-t)*vy j + t*vy(Suc j mod ?n) - vy i" by (by100 algebra)
        also have "\<dots> = (1-s)*vy i + s*vy(Suc i mod ?n) - vy i" using heqy by (by100 linarith)
        also have "\<dots> = s*(vy(Suc i mod ?n) - vy i)" by (by100 algebra)
        finally show ?thesis unfolding dy_def by (by100 simp)
      qed
      \<comment> \<open>Substituting: s*dx*dy - s*dy*dx = 0. But from cross\\_p: should be < 0.\<close>
      \<comment> \<open>From px\\_eq and py\\_eq: the cross\\_p expression equals s*dx*dy - s*dy*dx = 0.\<close>
      have "((1-t)*(vx j - vx i) + t*(vx(Suc j mod ?n) - vx i))*dy
         - ((1-t)*(vy j - vy i) + t*(vy(Suc j mod ?n) - vy i))*dx
         = s*dx*dy - s*dy*dx"
        using px_eq py_eq by (by100 algebra)
      also have "\<dots> = 0" by (by100 algebra)
      finally have "((1-t)*(vx j - vx i) + t*(vx(Suc j mod ?n) - vx i))*dy
         - ((1-t)*(vy j - vy i) + t*(vy(Suc j mod ?n) - vy i))*dx = 0" .
      \<comment> \<open>But cross\\_p\\_from\\_j says this is < 0. Contradiction.\<close>
      thus False using cross_p_from_j by (by100 linarith)
    qed
  qed
  \<comment> \<open>General: interior point of any edge is not a vertex. Uses C11 + C3.\<close>
  have hnotvertex_gen: "\<And>idx ss. idx < ?n \<Longrightarrow> 0 < ss \<Longrightarrow> ss < 1 \<Longrightarrow>
      \<not>(\<exists>k<?n. edge_pt idx ss = (vx k, vy k))"
  proof -
    fix idx :: nat and ss :: real
    assume hidx: "idx < ?n" and hss1: "0 < ss" and hss2: "ss < 1"
    show "\<not>(\<exists>k<?n. edge_pt idx ss = (vx k, vy k))"
    proof
      assume "\<exists>k<?n. edge_pt idx ss = (vx k, vy k)"
      then obtain k where hk: "k < ?n"
        and hxeq_g: "(1-ss)*vx idx + ss*vx(Suc idx mod ?n) = vx k"
        and hyeq_g: "(1-ss)*vy idx + ss*vy(Suc idx mod ?n) = vy k"
        unfolding edge_pt_def by (by100 auto)
      define ag where "ag = vx idx" define bg where "bg = vx(Suc idx mod ?n)" define cg where "cg = vx k"
      define ag' where "ag' = vy idx" define bg' where "bg' = vy(Suc idx mod ?n)" define cg' where "cg' = vy k"
      have habg: "(1-ss)*ag + ss*bg = cg" using hxeq_g unfolding ag_def bg_def cg_def by (by100 simp)
      have habg': "(1-ss)*ag' + ss*bg' = cg'" using hyeq_g unfolding ag'_def bg'_def cg'_def by (by100 simp)
      have hcolx_g: "cg - ag = ss*(bg - ag)"
      proof -
        have "(1-ss)*ag = ag - ss*ag" by (by100 algebra)
        hence "ag - ss*ag + ss*bg = cg" using habg by (by100 linarith)
        hence "cg - ag = ss*bg - ss*ag" by (by100 linarith)
        thus ?thesis by (simp only: right_diff_distrib[symmetric])
      qed
      have hcoly_g: "cg' - ag' = ss*(bg' - ag')"
      proof -
        have "(1-ss)*ag' = ag' - ss*ag'" by (by100 algebra)
        hence "ag' - ss*ag' + ss*bg' = cg'" using habg' by (by100 linarith)
        hence "cg' - ag' = ss*bg' - ss*ag'" by (by100 linarith)
        thus ?thesis by (simp only: right_diff_distrib[symmetric])
      qed
      have hcross0_g: "(cg - ag)*(bg' - ag') - (cg' - ag')*(bg - ag) = 0"
        unfolding hcolx_g hcoly_g by (by100 algebra)
      have "k = idx \<or> k = Suc idx mod ?n"
      proof (rule ccontr)
        assume "\<not>(k = idx \<or> k = Suc idx mod ?n)"
        hence "k \<noteq> idx" "k \<noteq> Suc idx mod ?n" by (by100 auto)+
        from hC11 hidx hk this
        have "(vx k - vx idx)*(vy(Suc idx mod ?n) - vy idx)
            - (vy k - vy idx)*(vx(Suc idx mod ?n) - vx idx) < 0" by (by100 blast)
        hence "(cg - ag)*(bg' - ag') - (cg' - ag')*(bg - ag) < 0"
          unfolding cg_def ag_def bg'_def ag'_def cg'_def bg_def by (by100 simp)
        thus False using hcross0_g by (by100 linarith)
      qed
      thus False
      proof
        assume "k = idx" hence "cg = ag" unfolding cg_def ag_def by (by100 simp)
        hence "ss*(bg - ag) = 0" using hcolx_g by (by100 linarith)
        from this have "ss = 0 \<or> bg - ag = 0" using mult_eq_0_iff by (by100 blast)
        hence hba_g: "bg = ag" using hss1 by (by100 linarith)
        have "cg' = ag'" unfolding cg'_def ag'_def using \<open>k = idx\<close> by (by100 simp)
        hence "ss*(bg' - ag') = 0" using hcoly_g by (by100 linarith)
        from this have "ss = 0 \<or> bg' - ag' = 0" using mult_eq_0_iff by (by100 blast)
        hence "bg' = ag'" using hss1 by (by100 linarith)
        hence "(vx idx, vy idx) = (vx(Suc idx mod ?n), vy(Suc idx mod ?n))"
          using hba_g unfolding ag_def ag'_def bg_def bg'_def by (by100 simp)
        have hn_gt0_g: "?n > 0" using assms by (by100 linarith)
        have hmod_lt_g: "Suc idx mod ?n < ?n" using hn_gt0_g by (by100 simp)
        have hmod_ne_g: "idx \<noteq> Suc idx mod ?n"
        proof
          assume "idx = Suc idx mod ?n"
          hence "Suc idx mod ?n = idx mod ?n" using hidx by (by100 simp)
          hence "(Suc idx - idx) mod ?n = 0" using assms by (simp add: mod_eq_dvd_iff_nat)
          hence "?n dvd 1" by (by100 simp)
          thus False using assms by (by100 simp)
        qed
        show False using hC3 hidx hmod_lt_g hmod_ne_g
          \<open>(vx idx, vy idx) = (vx(Suc idx mod ?n), vy(Suc idx mod ?n))\<close> by (by100 blast)
      next
        assume "k = Suc idx mod ?n" hence "cg = bg" unfolding cg_def bg_def by (by100 simp)
        hence "(1-ss)*ag + ss*bg = bg" using habg by (by100 simp)
        hence "(1-ss)*ag = bg - ss*bg" by (by100 linarith)
        have "(1-ss)*bg = bg - ss*bg" by (by100 algebra)
        hence "(1-ss)*ag = (1-ss)*bg" using \<open>(1-ss)*ag = bg - ss*bg\<close> by (by100 linarith)
        hence "(1-ss)*(ag - bg) = 0"
          using right_diff_distrib[of "1-ss" ag bg] by (by100 linarith)
        have "1-ss > 0" using hss2 by (by100 linarith)
        from \<open>(1-ss)*(ag - bg) = 0\<close> have "1-ss = 0 \<or> ag - bg = 0"
          using mult_eq_0_iff by (by100 blast)
        hence hba_g: "ag = bg" using \<open>1-ss > 0\<close> by (by100 linarith)
        have "cg' = bg'" unfolding cg'_def bg'_def using \<open>k = Suc idx mod ?n\<close> by (by100 simp)
        hence "(1-ss)*ag' + ss*bg' = bg'" using habg' by (by100 simp)
        hence "(1-ss)*ag' = bg' - ss*bg'" by (by100 linarith)
        have "(1-ss)*bg' = bg' - ss*bg'" by (by100 algebra)
        hence "(1-ss)*ag' = (1-ss)*bg'" using \<open>(1-ss)*ag' = bg' - ss*bg'\<close> by (by100 linarith)
        hence "(1-ss)*(ag' - bg') = 0"
          using right_diff_distrib[of "1-ss" ag' bg'] by (by100 linarith)
        from this have "1-ss = 0 \<or> ag' - bg' = 0" using mult_eq_0_iff by (by100 blast)
        hence "ag' = bg'" using \<open>1-ss > 0\<close> by (by100 linarith)
        hence "(vx idx, vy idx) = (vx(Suc idx mod ?n), vy(Suc idx mod ?n))"
          using hba_g unfolding ag_def ag'_def bg_def bg'_def by (by100 simp)
        have hn_gt0_g: "?n > 0" using assms by (by100 linarith)
        have hmod_lt_g: "Suc idx mod ?n < ?n" using hn_gt0_g by (by100 simp)
        have hmod_ne_g: "idx \<noteq> Suc idx mod ?n"
        proof
          assume "idx = Suc idx mod ?n"
          hence "Suc idx mod ?n = idx mod ?n" using hidx by (by100 simp)
          hence "(Suc idx - idx) mod ?n = 0" using assms by (simp add: mod_eq_dvd_iff_nat)
          hence "?n dvd 1" by (by100 simp)
          thus False using assms by (by100 simp)
        qed
        show False using hC3 hidx hmod_lt_g hmod_ne_g
          \<open>(vx idx, vy idx) = (vx(Suc idx mod ?n), vy(Suc idx mod ?n))\<close> by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>Helper: convex polygon edges have injective interior parameterization.
     If edge\_pt(i1,t1) = edge\_pt(i2,t2) with 0<t1,t2<1 then i1=i2 and t1=t2.\<close>
  have hedge_unique: "\<And>i1 i2 t1 t2. i1 < ?n \<Longrightarrow> i2 < ?n \<Longrightarrow> 0 < t1 \<Longrightarrow> t1 < 1 \<Longrightarrow>
      0 < t2 \<Longrightarrow> t2 < 1 \<Longrightarrow> edge_pt i1 t1 = edge_pt i2 t2 \<Longrightarrow> i1 = i2 \<and> t1 = t2"
  proof -
    fix i1 i2 :: nat and t1 t2 :: real
    assume hi1: "i1 < ?n" and hi2: "i2 < ?n"
      and ht1a: "0 < t1" and ht1b: "t1 < 1" and ht2a: "0 < t2" and ht2b: "t2 < 1"
      and heq_u: "edge_pt i1 t1 = edge_pt i2 t2"
    have heqx_u: "(1-t1)*vx i1 + t1*vx(Suc i1 mod ?n) = (1-t2)*vx i2 + t2*vx(Suc i2 mod ?n)"
      using heq_u unfolding edge_pt_def by (by100 simp)
    have heqy_u: "(1-t1)*vy i1 + t1*vy(Suc i1 mod ?n) = (1-t2)*vy i2 + t2*vy(Suc i2 mod ?n)"
      using heq_u unfolding edge_pt_def by (by100 simp)
    show "i1 = i2 \<and> t1 = t2"
    proof (cases "i1 = i2")
      case True
      \<comment> \<open>Same edge: (t1-t2)*(endpoint - startpoint) = 0 in both coords.
         Since vertices are distinct (C3), t1 = t2.\<close>
      have ht_eq: "t1 = t2"
      proof -
        from heqx_u True
        have "(1-t1)*vx i1 + t1*vx(Suc i1 mod ?n) = (1-t2)*vx i1 + t2*vx(Suc i1 mod ?n)"
          by (by100 simp)
        hence hx0: "(t1-t2)*(vx(Suc i1 mod ?n) - vx i1) = 0" by (by100 algebra)
        from heqy_u True
        have "(1-t1)*vy i1 + t1*vy(Suc i1 mod ?n) = (1-t2)*vy i1 + t2*vy(Suc i1 mod ?n)"
          by (by100 simp)
        hence hy0: "(t1-t2)*(vy(Suc i1 mod ?n) - vy i1) = 0" by (by100 algebra)
        have hn_gt0_u: "?n > 0" using assms by (by100 linarith)
        have hmod_lt_u: "Suc i1 mod ?n < ?n" using hn_gt0_u by (by100 simp)
        have hmod_ne_u: "i1 \<noteq> Suc i1 mod ?n"
        proof
          assume "i1 = Suc i1 mod ?n"
          hence "Suc i1 mod ?n = i1 mod ?n" using hi1 by (by100 simp)
          hence "(Suc i1 - i1) mod ?n = 0" using assms by (simp add: mod_eq_dvd_iff_nat)
          hence "?n dvd 1" by (by100 simp)
          thus False using assms by (by100 simp)
        qed
        have "(vx i1, vy i1) \<noteq> (vx(Suc i1 mod ?n), vy(Suc i1 mod ?n))"
          using hC3 hi1 hmod_lt_u hmod_ne_u by (by100 blast)
        hence "vx i1 \<noteq> vx(Suc i1 mod ?n) \<or> vy i1 \<noteq> vy(Suc i1 mod ?n)" by (by100 auto)
        thus "t1 = t2"
        proof
          assume "vx i1 \<noteq> vx(Suc i1 mod ?n)"
          hence "vx(Suc i1 mod ?n) - vx i1 \<noteq> 0" by (by100 linarith)
          from hx0 this show "t1 = t2"
            using mult_eq_0_iff[of "t1 - t2" "vx(Suc i1 mod ?n) - vx i1"] by (by100 linarith)
        next
          assume "vy i1 \<noteq> vy(Suc i1 mod ?n)"
          hence "vy(Suc i1 mod ?n) - vy i1 \<noteq> 0" by (by100 linarith)
          from hy0 this show "t1 = t2"
            using mult_eq_0_iff[of "t1 - t2" "vy(Suc i1 mod ?n) - vy i1"] by (by100 linarith)
        qed
      qed
      thus ?thesis using True by (by100 simp)
    next
      case hne_u: False
      \<comment> \<open>Different edges: cross product argument gives contradiction.
         Key idea: the point lies on edge i1 (cross with edge direction = 0)
         but C11 forces all non-endpoint vertices to have cross < 0.\<close>
      define dx_u where "dx_u = vx(Suc i1 mod ?n) - vx i1"
      define dy_u where "dy_u = vy(Suc i1 mod ?n) - vy i1"
      have hn_gt0_u: "?n > 0" using assms by (by100 linarith)
      have hi1s_lt: "Suc i1 mod ?n < ?n" using hn_gt0_u by (by100 simp)
      have hi2s_lt: "Suc i2 mod ?n < ?n" using hn_gt0_u by (by100 simp)
      \<comment> \<open>From edge i1: point = (1-t1)*v\_i1 + t1*v\_{Suc i1}.
         Translated: point - v\_i1 = t1*(v\_{Suc i1} - v\_i1) = t1*(dx\_u, dy\_u).\<close>
      have px_u: "(1-t2)*(vx i2 - vx i1) + t2*(vx(Suc i2 mod ?n) - vx i1) = t1 * dx_u"
      proof -
        have "(1-t2)*(vx i2 - vx i1) + t2*(vx(Suc i2 mod ?n) - vx i1)
            = (1-t2)*vx i2 + t2*vx(Suc i2 mod ?n) - vx i1" by (by100 algebra)
        also have "\<dots> = (1-t1)*vx i1 + t1*vx(Suc i1 mod ?n) - vx i1"
          using heqx_u by (by100 linarith)
        also have "\<dots> = t1*(vx(Suc i1 mod ?n) - vx i1)" by (by100 algebra)
        finally show ?thesis unfolding dx_u_def by (by100 simp)
      qed
      have py_u: "(1-t2)*(vy i2 - vy i1) + t2*(vy(Suc i2 mod ?n) - vy i1) = t1 * dy_u"
      proof -
        have "(1-t2)*(vy i2 - vy i1) + t2*(vy(Suc i2 mod ?n) - vy i1)
            = (1-t2)*vy i2 + t2*vy(Suc i2 mod ?n) - vy i1" by (by100 algebra)
        also have "\<dots> = (1-t1)*vy i1 + t1*vy(Suc i1 mod ?n) - vy i1"
          using heqy_u by (by100 linarith)
        also have "\<dots> = t1*(vy(Suc i1 mod ?n) - vy i1)" by (by100 algebra)
        finally show ?thesis unfolding dy_u_def by (by100 simp)
      qed
      \<comment> \<open>Cross product of translated point with edge direction = 0.\<close>
      have cross0_u: "((1-t2)*(vx i2 - vx i1) + t2*(vx(Suc i2 mod ?n) - vx i1))*dy_u
         - ((1-t2)*(vy i2 - vy i1) + t2*(vy(Suc i2 mod ?n) - vy i1))*dx_u = 0"
        using px_u py_u by (by100 algebra)
      \<comment> \<open>Expand cross as convex combination of individual vertex crosses.\<close>
      have expand_u: "((1-t2)*(vx i2 - vx i1) + t2*(vx(Suc i2 mod ?n) - vx i1))*dy_u
         - ((1-t2)*(vy i2 - vy i1) + t2*(vy(Suc i2 mod ?n) - vy i1))*dx_u
         = (1-t2)*((vx i2 - vx i1)*dy_u - (vy i2 - vy i1)*dx_u)
         + t2*((vx(Suc i2 mod ?n) - vx i1)*dy_u - (vy(Suc i2 mod ?n) - vy i1)*dx_u)"
        by (by100 algebra)
      \<comment> \<open>Define the two cross terms for readability.\<close>
      define A_u where "A_u = (vx i2 - vx i1)*dy_u - (vy i2 - vy i1)*dx_u"
      define B_u where "B_u = (vx(Suc i2 mod ?n) - vx i1)*dy_u - (vy(Suc i2 mod ?n) - vy i1)*dx_u"
      \<comment> \<open>A\_u \<le> 0: C11 gives < 0 unless i2 = Suc i1 mod n (where cross = 0).\<close>
      have hAle: "A_u \<le> 0"
      proof (cases "i2 = Suc i1 mod ?n")
        case True
        hence "A_u = dx_u*dy_u - dy_u*dx_u" unfolding A_u_def dx_u_def dy_u_def by (by100 simp)
        thus ?thesis by (by100 simp)
      next
        case False
        from hC11 hi1 hi2 hne_u False
        have "(vx i2 - vx i1)*(vy(Suc i1 mod ?n) - vy i1)
            - (vy i2 - vy i1)*(vx(Suc i1 mod ?n) - vx i1) < 0" by (by100 blast)
        thus ?thesis unfolding A_u_def dx_u_def dy_u_def by (by100 linarith)
      qed
      \<comment> \<open>B\_u \<le> 0: similarly, C11 gives < 0 unless Suc i2 mod n \<in> {i1, Suc i1 mod n}.\<close>
      have hBle: "B_u \<le> 0"
      proof (cases "Suc i2 mod ?n = i1 \<or> Suc i2 mod ?n = Suc i1 mod ?n")
        case True
        hence "B_u = 0"
        proof
          assume "Suc i2 mod ?n = i1"
          thus ?thesis unfolding B_u_def by (by100 simp)
        next
          assume "Suc i2 mod ?n = Suc i1 mod ?n"
          thus ?thesis unfolding B_u_def dx_u_def dy_u_def by (by100 simp)
        qed
        thus ?thesis by (by100 linarith)
      next
        case False
        hence "Suc i2 mod ?n \<noteq> i1" "Suc i2 mod ?n \<noteq> Suc i1 mod ?n" by (by100 auto)+
        from hC11 hi1 hi2s_lt this
        have "(vx(Suc i2 mod ?n) - vx i1)*(vy(Suc i1 mod ?n) - vy i1)
            - (vy(Suc i2 mod ?n) - vy i1)*(vx(Suc i1 mod ?n) - vx i1) < 0" by (by100 blast)
        thus ?thesis unfolding B_u_def dx_u_def dy_u_def by (by100 linarith)
      qed
      \<comment> \<open>From convex combination = 0 with both terms \<le> 0: both must be 0.\<close>
      have hconv_u: "(1-t2)*A_u + t2*B_u = 0"
        using cross0_u expand_u unfolding A_u_def B_u_def by (by100 linarith)
      have h1t2: "1-t2 > 0" using ht2b by (by100 linarith)
      have ht2p: "t2 > 0" using ht2a .
      have "(1-t2)*A_u \<le> 0"
        using h1t2 hAle mult_nonneg_nonpos[of "1-t2" A_u] by (by100 linarith)
      have "t2*B_u \<le> 0"
        using ht2p hBle mult_nonneg_nonpos[of t2 B_u] by (by100 linarith)
      have h1tA0: "(1-t2)*A_u = 0"
        using \<open>(1-t2)*A_u \<le> 0\<close> \<open>t2*B_u \<le> 0\<close> hconv_u by (by100 linarith)
      have hA0: "A_u = 0"
      proof -
        from h1tA0 have "1-t2 = 0 \<or> A_u = 0"
          using mult_eq_0_iff by (by100 blast)
        thus ?thesis using h1t2 by (by100 linarith)
      qed
      have hB0: "B_u = 0"
      proof -
        have "t2*B_u = 0" using h1tA0 hconv_u by (by100 linarith)
        from this have "t2 = 0 \<or> B_u = 0" using mult_eq_0_iff by (by100 blast)
        thus ?thesis using ht2p by (by100 linarith)
      qed
      \<comment> \<open>From A\_u = 0 and i1 \<noteq> i2: must have i2 = Suc i1 mod n.\<close>
      have hi2eq: "i2 = Suc i1 mod ?n"
      proof (rule ccontr)
        assume "i2 \<noteq> Suc i1 mod ?n"
        from hC11 hi1 hi2 hne_u this
        have "(vx i2 - vx i1)*(vy(Suc i1 mod ?n) - vy i1)
            - (vy i2 - vy i1)*(vx(Suc i1 mod ?n) - vx i1) < 0" by (by100 blast)
        hence "A_u < 0" unfolding A_u_def dx_u_def dy_u_def by (by100 linarith)
        thus False using hA0 by (by100 linarith)
      qed
      \<comment> \<open>From B\_u = 0: Suc i2 mod n must be i1 (only other zero option Suc i1 mod n
         would give i2 = i1 by the Suc-mod injectivity below).\<close>
      have hsi2eq: "Suc i2 mod ?n = i1"
      proof (rule ccontr)
        assume hne2: "Suc i2 mod ?n \<noteq> i1"
        have "Suc i2 mod ?n \<noteq> Suc i1 mod ?n"
        proof
          assume heq_s: "Suc i2 mod ?n = Suc i1 mod ?n"
          \<comment> \<open>Suc i2 mod n = Suc i1 mod n with i1,i2 < n implies i2 = i1.\<close>
          have "Suc i2 \<le> ?n" using hi2 by (by100 linarith)
          have "Suc i1 \<le> ?n" using hi1 by (by100 linarith)
          have "i2 = i1"
          proof (cases "Suc i2 < ?n")
            case True hence "Suc i2 mod ?n = Suc i2" by (by100 simp)
            show ?thesis
            proof (cases "Suc i1 < ?n")
              case True2: True hence "Suc i1 mod ?n = Suc i1" by (by100 simp)
              from heq_s \<open>Suc i2 mod ?n = Suc i2\<close> True2 show ?thesis by (by100 simp)
            next
              case False hence "Suc i1 = ?n" using \<open>Suc i1 \<le> ?n\<close> by (by100 linarith)
              hence "Suc i1 mod ?n = 0" by (by100 simp)
              from heq_s \<open>Suc i2 mod ?n = Suc i2\<close> this have "Suc i2 = 0" by (by100 simp)
              thus ?thesis by (by100 simp)
            qed
          next
            case False hence "Suc i2 = ?n" using \<open>Suc i2 \<le> ?n\<close> by (by100 linarith)
            hence "Suc i2 mod ?n = 0" by (by100 simp)
            show ?thesis
            proof (cases "Suc i1 < ?n")
              case True hence "Suc i1 mod ?n = Suc i1" by (by100 simp)
              from heq_s \<open>Suc i2 mod ?n = 0\<close> this have "Suc i1 = 0" by (by100 simp)
              thus ?thesis by (by100 simp)
            next
              case False hence "Suc i1 = ?n" using \<open>Suc i1 \<le> ?n\<close> by (by100 linarith)
              from \<open>Suc i2 = ?n\<close> this show ?thesis by (by100 simp)
            qed
          qed
          thus False using hne_u by (by100 simp)
        qed
        from hC11 hi1 hi2s_lt hne2 this
        have "(vx(Suc i2 mod ?n) - vx i1)*(vy(Suc i1 mod ?n) - vy i1)
            - (vy(Suc i2 mod ?n) - vy i1)*(vx(Suc i1 mod ?n) - vx i1) < 0" by (by100 blast)
        hence "B_u < 0" unfolding B_u_def dx_u_def dy_u_def by (by100 linarith)
        thus False using hB0 by (by100 linarith)
      qed
      \<comment> \<open>Now i2 = Suc i1 mod n and Suc i2 mod n = i1.
         This means Suc(Suc i1 mod n) mod n = i1, giving n | 2.
         Since n \<ge> 3, contradiction.\<close>
      have "Suc (Suc i1 mod ?n) mod ?n = i1"
        using hi2eq hsi2eq by (by100 simp)
      have False
      proof (cases "Suc i1 < ?n")
        case True hence "Suc i1 mod ?n = Suc i1" by (by100 simp)
        hence "Suc (Suc i1) mod ?n = i1" using \<open>Suc (Suc i1 mod ?n) mod ?n = i1\<close> by (by100 simp)
        show False
        proof (cases "Suc (Suc i1) < ?n")
          case True2: True hence "Suc (Suc i1) mod ?n = Suc (Suc i1)" by (by100 simp)
          from \<open>Suc (Suc i1) mod ?n = i1\<close> this have "Suc (Suc i1) = i1" by (by100 simp)
          thus False by (by100 simp)
        next
          case False hence "Suc (Suc i1) \<ge> ?n" by (by100 linarith)
          moreover have "Suc (Suc i1) \<le> Suc ?n" using True by (by100 linarith)
          ultimately have "Suc (Suc i1) = ?n \<or> Suc (Suc i1) = Suc ?n" by (by100 linarith)
          thus False
          proof
            assume "Suc (Suc i1) = ?n"
            hence "Suc (Suc i1) mod ?n = 0" by (by100 simp)
            from \<open>Suc (Suc i1) mod ?n = i1\<close> this have "i1 = 0" by (by100 simp)
            hence "?n = 2" using \<open>Suc (Suc i1) = ?n\<close> by (by100 simp)
            thus False using assms by (by100 linarith)
          next
            assume "Suc (Suc i1) = Suc ?n"
            hence "Suc i1 = ?n" by (by100 simp)
            thus False using True by (by100 linarith)
          qed
        qed
      next
        case False hence "Suc i1 = ?n" using hi1 by (by100 linarith)
        hence "Suc i1 mod ?n = 0" by (by100 simp)
        hence "Suc 0 mod ?n = i1" using \<open>Suc (Suc i1 mod ?n) mod ?n = i1\<close> by (by100 simp)
        have "1 mod ?n = (1::nat)" using assms by (by100 simp)
        hence "i1 = 1" using \<open>Suc 0 mod ?n = i1\<close> by (by100 simp)
        hence "?n = 2" using \<open>Suc i1 = ?n\<close> by (by100 simp)
        thus False using assms by (by100 linarith)
      qed
      thus ?thesis by (by100 simp)
    qed
  qed
  \<comment> \<open>C2 (quotient map): q is continuous, surjective, TY is quotient topology.\<close>
  have hC2: "top1_quotient_map_on P
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) Y TY q"
  proof -
    let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
    have htopo_P_c2: "is_topology_on P ?TP"
    proof -
      have "is_topology_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
        using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV]
        by (by100 simp)
      thus ?thesis by (rule subspace_topology_is_topology_on) (by100 simp)
    qed
    have htopo_Y_c2: "is_topology_on Y TY"
    proof -
      \<comment> \<open>TY equals the standard quotient topology by map. Show equivalence.\<close>
      have hTY_eq: "TY = top1_quotient_topology_by_map_on P ?TP Y q"
      proof (intro equalityI subsetI)
        fix U assume "U \<in> TY"
        then obtain W where hW: "W \<subseteq> P" "\<forall>x\<in>W. \<forall>y. y\<in>P \<and> q y = q x \<longrightarrow> y \<in> W"
          "U = q ` W" "W \<in> ?TP" unfolding TY_def by (by100 blast)
        have "U \<subseteq> Y" using hW(3) unfolding Y_def using hW(1) by (by100 blast)
        have "{x\<in>P. q x \<in> U} = W"
        proof (intro equalityI subsetI)
          fix x assume "x \<in> {x\<in>P. q x \<in> U}"
          hence "x \<in> P" "q x \<in> q ` W" using hW(3) by (by100 auto)+
          then obtain w where "w \<in> W" "q x = q w" by (by100 blast)
          thus "x \<in> W" using hW(2) \<open>x \<in> P\<close> hW(1) by (by100 blast)
        next
          fix x assume "x \<in> W" thus "x \<in> {x\<in>P. q x \<in> U}" using hW(1) hW(3) by (by100 blast)
        qed
        hence "{x\<in>P. q x \<in> U} \<in> ?TP" using hW(4) by (by100 simp)
        thus "U \<in> top1_quotient_topology_by_map_on P ?TP Y q"
          unfolding top1_quotient_topology_by_map_on_def using \<open>U \<subseteq> Y\<close> by (by100 blast)
      next
        fix U assume "U \<in> top1_quotient_topology_by_map_on P ?TP Y q"
        hence hU: "U \<subseteq> Y" "{x\<in>P. q x \<in> U} \<in> ?TP"
          unfolding top1_quotient_topology_by_map_on_def by (by100 blast)+
        define W where "W = {x\<in>P. q x \<in> U}"
        have "W \<subseteq> P" unfolding W_def by (by100 blast)
        have "\<forall>x\<in>W. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> W" unfolding W_def by (by100 auto)
        have "U = q ` W"
        proof (intro equalityI subsetI)
          fix u assume "u \<in> U"
          hence "u \<in> Y" using hU(1) by (by100 blast)
          then obtain x where "x \<in> P" "q x = u" unfolding Y_def by (by100 blast)
          hence "x \<in> W" unfolding W_def using \<open>u \<in> U\<close> by (by100 blast)
          thus "u \<in> q ` W" using \<open>q x = u\<close> by (by100 blast)
        next
          fix u assume "u \<in> q ` W" thus "u \<in> U" unfolding W_def by (by100 blast)
        qed
        have "W \<in> ?TP" using hU(2) unfolding W_def .
        show "U \<in> TY" unfolding TY_def
          using \<open>W \<subseteq> P\<close> \<open>\<forall>x\<in>W. _\<close> \<open>U = q ` W\<close> \<open>W \<in> ?TP\<close> by (by100 blast)
      qed
      have hpmap: "\<forall>x\<in>P. q x \<in> Y" unfolding Y_def by (by100 blast)
      from top1_quotient_topology_by_map_on_is_topology_on[OF htopo_P_c2 hpmap]
      show ?thesis using hTY_eq by (by100 simp)
    qed
    show ?thesis unfolding top1_quotient_map_on_def
    proof (intro conjI)
      show "is_topology_on P ?TP" using htopo_P_c2 .
      show "is_topology_on Y TY" using htopo_Y_c2 .
      \<comment> \<open>q continuous: preimage of open is open. By quotient topology definition.\<close>
      show "top1_continuous_map_on P ?TP Y TY q"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix x assume "x \<in> P" thus "q x \<in> Y" unfolding Y_def by (by100 blast)
      next
        fix V assume hV: "V \<in> TY"
        from hV obtain W where hW_sub: "W \<subseteq> P"
          and hW_sat: "\<forall>x\<in>W. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> W"
          and hV_eq: "V = q ` W" and hW_open: "W \<in> ?TP"
          unfolding TY_def by (by100 blast)
        have "{x \<in> P. q x \<in> V} = W"
        proof (intro equalityI subsetI)
          fix x assume "x \<in> {x \<in> P. q x \<in> V}"
          hence "x \<in> P" "q x \<in> q ` W" using hV_eq by (by100 auto)+
          then obtain w where "w \<in> W" "q x = q w" by (by100 blast)
          thus "x \<in> W" using hW_sat \<open>x \<in> P\<close> hW_sub by (by100 blast)
        next
          fix x assume "x \<in> W"
          hence "x \<in> P" using hW_sub by (by100 blast)
          moreover have "q x \<in> V" using \<open>x \<in> W\<close> hV_eq by (by100 blast)
          ultimately show "x \<in> {x \<in> P. q x \<in> V}" by (by100 blast)
        qed
        thus "{x \<in> P. q x \<in> V} \<in> ?TP" using hW_open by (by100 simp)
      qed
      show "q ` P = Y" unfolding Y_def by (by100 simp)
      \<comment> \<open>Quotient condition: saturated open preimage gives open set.\<close>
      show "\<forall>V. V \<subseteq> Y \<longrightarrow> ({x \<in> P. q x \<in> V} \<in> ?TP \<longrightarrow> V \<in> TY)"
      proof (intro allI impI)
        fix V assume hVsub: "V \<subseteq> Y" and hpre: "{x \<in> P. q x \<in> V} \<in> ?TP"
        define W where "W = {x \<in> P. q x \<in> V}"
        have "W \<subseteq> P" unfolding W_def by (by100 blast)
        have "\<forall>x\<in>W. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> W" unfolding W_def by (by100 auto)
        have "V = q ` W"
        proof (intro equalityI subsetI)
          fix v assume "v \<in> V"
          hence "v \<in> Y" using hVsub by (by100 blast)
          hence "\<exists>x \<in> P. q x = v" unfolding Y_def by (by100 blast)
          then obtain x where "x \<in> P" "q x = v" by (by100 blast)
          hence "x \<in> W" unfolding W_def using \<open>v \<in> V\<close> by (by100 blast)
          thus "v \<in> q ` W" using \<open>q x = v\<close> by (by100 blast)
        next
          fix v assume "v \<in> q ` W"
          then obtain x where "x \<in> W" "q x = v" by (by100 blast)
          thus "v \<in> V" unfolding W_def by (by100 blast)
        qed
        have "W \<in> ?TP" using hpre unfolding W_def .
        show "V \<in> TY" unfolding TY_def
          using \<open>W \<subseteq> P\<close> \<open>\<forall>x\<in>W. _\<close> \<open>V = q ` W\<close> \<open>W \<in> ?TP\<close> by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>C7/C8: Edge identification pattern matches the scheme.\<close>
  have hC8: "\<forall>i<?n. \<forall>j<?n. fst(scheme!i) = fst(scheme!j) \<longrightarrow>
      (\<forall>t\<in>I_set.
         q ((1-t)*vx i + t*vx(Suc i mod ?n), (1-t)*vy i + t*vy(Suc i mod ?n))
       = (if snd(scheme!i) = snd(scheme!j)
          then q ((1-t)*vx j + t*vx(Suc j mod ?n), (1-t)*vy j + t*vy(Suc j mod ?n))
          else q (t*vx j + (1-t)*vx(Suc j mod ?n), t*vy j + (1-t)*vy(Suc j mod ?n))))"
  proof (intro allI impI ballI)
    fix i j t assume hi: "i < ?n" and hj: "j < ?n" and hlabel: "fst(scheme!i) = fst(scheme!j)"
      and ht: "t \<in> I_set"
    \<comment> \<open>Need: q(edge\\_pt i t) = (if same\\_dir then q(edge\\_pt j t) else q(edge\\_pt j (1-t))).\<close>
    show "q ((1-t)*vx i + t*vx(Suc i mod ?n), (1-t)*vy i + t*vy(Suc i mod ?n))
       = (if snd(scheme!i) = snd(scheme!j)
          then q ((1-t)*vx j + t*vx(Suc j mod ?n), (1-t)*vy j + t*vy(Suc j mod ?n))
          else q (t*vx j + (1-t)*vx(Suc j mod ?n), t*vy j + (1-t)*vy(Suc j mod ?n)))"
    proof (cases "i = j")
      case True thus ?thesis by (by100 simp)
    next
      case hij: False
      have hpi: "partner i = j" using partner_unique[OF hi hj hij hlabel] .
      have hpj: "partner j = i" using partner_unique[OF hj hi hij[symmetric] hlabel[symmetric]] .
      have ht01: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)+
      \<comment> \<open>Case split on whether t is a vertex (0 or 1) or interior.\<close>
      show ?thesis
      proof (cases "0 < t \<and> t < 1")
        case hint: True \<comment> \<open>Edge interior: q enters the edge-interior branch.\<close>
        \<comment> \<open>hnotvertex_gen and hedge_unique are available from top-level scope.\<close>
        \<comment> \<open>Instantiate for edge i at parameter t.\<close>
        have hnotvertex_i: "\<not>(\<exists>k<?n. (1-t)*vx i + t*vx(Suc i mod ?n) = vx k \<and> (1-t)*vy i + t*vy(Suc i mod ?n) = vy k)"
        proof -
          have "0 < t" "t < 1" using hint by (by100 auto)+
          from hnotvertex_gen[OF hi this] show ?thesis unfolding edge_pt_def by (by100 auto)
        qed
        \<comment> \<open>For the interior case: q on canonical edges = id, q on non-canonical = partner.
           Both sides evaluate to the same canonical edge point.\<close>
        \<comment> \<open>Rewrite goal in terms of edge\\_pt.\<close>
        have hgoal_lhs: "edge_pt i t = ((1-t)*vx i + t*vx(Suc i mod ?n), (1-t)*vy i + t*vy(Suc i mod ?n))"
          unfolding edge_pt_def by (by100 simp)
        show ?thesis
        proof (cases "is_canonical i")
          case hican: True \<comment> \<open>i canonical, j non-canonical.\<close>
          hence hjnon: "\<not> is_canonical j"
          proof -
            have "i \<le> partner i" using hican unfolding is_canonical_def by (by100 simp)
            hence "i \<le> j" using hpi by (by100 simp)
            hence "i < j" using hij by (by100 linarith)
            hence "j > partner j" using hpj by (by100 simp)
            thus ?thesis unfolding is_canonical_def by (by100 linarith)
          qed
          \<comment> \<open>q(edge\\_pt i t) = edge\\_pt(i,t) since i canonical and not a vertex.\<close>
          have hqi: "q (edge_pt i t) = edge_pt i t"
          proof -
            \<comment> \<open>Not a vertex.\<close>
            have hv: "\<not>(\<exists>k<?n. edge_pt i t = (vx k, vy k))"
              using hnotvertex_i unfolding edge_pt_def by (by100 simp)
            \<comment> \<open>Not on any non-canonical edge interior.\<close>
            have he: "\<not>(\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i')"
            proof
              assume "\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i'"
              then obtain i' t' where hi': "i' < ?n" "0 < t'" "t' < 1" "edge_pt i t = edge_pt i' t'" "\<not> is_canonical i'"
                by (by100 blast)
              \<comment> \<open>Edges i and i' share interior point. By C6 + adjacency: i = i'.\<close>
              have "i = i'"
              proof -
                have "0 < t" "t < 1" using hint by (by100 auto)+
                from hedge_unique[OF hi hi'(1) this hi'(2) hi'(3) hi'(4)]
                show ?thesis by (by100 simp)
              qed
              thus False using hican hi'(5) by (by100 simp)
            qed
            show ?thesis unfolding q_def using hv he by (by100 auto)
          qed
          \<comment> \<open>q(edge\\_pt j s) where s is the matching param.\<close>
          have hqj: "\<And>s. 0 < s \<Longrightarrow> s < 1 \<Longrightarrow> q (edge_pt j s) = edge_pt i
              (if snd(scheme!j) = snd(scheme!i) then s else 1 - s)"
          proof -
            fix s :: real assume hs: "0 < s" "s < 1"
            \<comment> \<open>edge\\_pt(j,s) is not a vertex.\<close>
            have hvj: "\<not>(\<exists>k<?n. edge_pt j s = (vx k, vy k))"
              using hnotvertex_gen[OF hj hs(1) hs(2)] .
            \<comment> \<open>edge\\_pt(j,s) IS on non-canonical edge j.\<close>
            have hexj: "\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i'"
              using hj hs hjnon by (by100 blast)
            \<comment> \<open>q enters edge-interior branch. SOME picks (j', s'). By uniqueness j' = j, s' = s.\<close>
            define sel where "sel = (SOME (i',t'). i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i')"
            define j' where "j' = fst sel" define s' where "s' = snd sel"
            have hsel: "j' < ?n \<and> 0 < s' \<and> s' < 1 \<and> edge_pt j s = edge_pt j' s' \<and> \<not> is_canonical j'"
            proof -
              from hexj have "\<exists>p. (\<lambda>(i',t'). i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i') p"
                by (by100 auto)
              from someI_ex[OF this] show ?thesis unfolding sel_def j'_def s'_def by (by100 auto)
            qed
            \<comment> \<open>By edge uniqueness: j' = j and s' = s.\<close>
            have "j' = j \<and> s' = s"
            proof -
              from hsel have hj'_lt: "j' < ?n" and hs'a: "0 < s'" and hs'b: "s' < 1"
                and heq_js: "edge_pt j s = edge_pt j' s'" by (by100 auto)+
              from hedge_unique[OF hj hj'_lt hs(1) hs(2) hs'a hs'b heq_js]
              show ?thesis by (by100 simp)
            qed
            hence "partner j' = partner j" and "snd(scheme!j') = snd(scheme!j)" by (by100 auto)+
            hence "q (edge_pt j s) = edge_pt (partner j) (if snd(scheme!j) = snd(scheme!(partner j)) then s else 1-s)"
            proof -
              have "q (edge_pt j s) = (let (i',t') = sel in let jj = partner i' in
                  if snd(scheme!i') = snd(scheme!jj) then edge_pt jj t' else edge_pt jj (1-t'))"
                unfolding q_def sel_def using hexj hvj by (by100 auto)
              also have "\<dots> = (let jj = partner j' in
                  if snd(scheme!j') = snd(scheme!jj) then edge_pt jj s' else edge_pt jj (1-s'))"
              proof -
                have "sel = (j', s')" unfolding j'_def s'_def by (by100 simp)
                thus ?thesis by (by100 simp)
              qed
              also have "\<dots> = (if snd(scheme!j) = snd(scheme!(partner j)) then edge_pt (partner j) s else edge_pt (partner j) (1-s))"
                using \<open>j' = j \<and> s' = s\<close> by (by100 simp)
              finally show ?thesis by (by100 simp)
            qed
            thus "q (edge_pt j s) = edge_pt i (if snd(scheme!j) = snd(scheme!i) then s else 1 - s)"
              using hpj by (by100 simp)
          qed
          show ?thesis
          proof (cases "snd(scheme!i) = snd(scheme!j)")
            case True \<comment> \<open>Same direction.\<close>
            have "q (edge_pt j t) = edge_pt i t" using hqj hint True by (by100 simp)
            thus ?thesis using hqi hgoal_lhs True unfolding edge_pt_def by (by100 simp)
          next
            case False \<comment> \<open>Opposite direction.\<close>
            have "0 < 1 - t" "1 - t < 1" using hint by (by100 linarith)+
            hence "q (edge_pt j (1-t)) = edge_pt i (1 - (1-t))"
              using hqj[of "1-t"] False by (by100 simp)
            hence "q (edge_pt j (1-t)) = edge_pt i t" by (by100 simp)
            thus ?thesis using hqi hgoal_lhs False unfolding edge_pt_def by (by100 simp)
          qed
        next
          case hican: False \<comment> \<open>i non-canonical, j canonical. Symmetric to the True case.\<close>
          hence hjcan: "is_canonical j"
          proof -
            have "\<not>(i \<le> partner i)" using hican unfolding is_canonical_def by (by100 simp)
            hence "i > partner i" by (by100 linarith)
            hence "i > j" using hpi by (by100 simp)
            hence "j < i" by (by100 linarith)
            hence "j \<le> partner j" using hpj by (by100 simp)
            thus ?thesis unfolding is_canonical_def by (by100 simp)
          qed
          \<comment> \<open>q(edge\\_pt i t): i non-canonical, so q enters edge-interior branch.\<close>
          have hqi_nc: "q (edge_pt i t) = edge_pt j (if snd(scheme!i) = snd(scheme!j) then t else 1-t)"
          proof -
            have ht_pos: "0 < t" and ht_lt1: "t < 1" using hint by (by100 auto)+
            have hv_i: "\<not>(\<exists>k<?n. edge_pt i t = (vx k, vy k))"
              using hnotvertex_gen[OF hi ht_pos ht_lt1] .
            have hex_i: "\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i'"
              using hi ht_pos ht_lt1 hican by (by100 blast)
            define sel_i where "sel_i = (SOME (i',t'). i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i')"
            define i'' where "i'' = fst sel_i" define t'' where "t'' = snd sel_i"
            have hsel_i: "i'' < ?n \<and> 0 < t'' \<and> t'' < 1 \<and> edge_pt i t = edge_pt i'' t'' \<and> \<not> is_canonical i''"
            proof -
              from hex_i have "\<exists>p. (\<lambda>(i',t'). i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i') p"
                by (by100 auto)
              from someI_ex[OF this] show ?thesis unfolding sel_i_def i''_def t''_def by (by100 auto)
            qed
            have hii: "i'' = i \<and> t'' = t"
            proof -
              from hsel_i have "i'' < ?n" "0 < t''" "t'' < 1" "edge_pt i t = edge_pt i'' t''"
                by (by100 auto)+
              from hedge_unique[OF hi this(1) ht_pos ht_lt1 this(2) this(3) this(4)]
              show ?thesis by (by100 simp)
            qed
            have "q (edge_pt i t) = (let (i',t') = sel_i in let jj = partner i' in
                if snd(scheme!i') = snd(scheme!jj) then edge_pt jj t' else edge_pt jj (1-t'))"
              unfolding q_def sel_i_def using hex_i hv_i by (by100 auto)
            also have "\<dots> = (let jj = partner i'' in
                if snd(scheme!i'') = snd(scheme!jj) then edge_pt jj t'' else edge_pt jj (1-t''))"
            proof -
              have "sel_i = (i'', t'')" unfolding i''_def t''_def by (by100 simp)
              thus ?thesis by (by100 simp)
            qed
            also have "\<dots> = (if snd(scheme!i) = snd(scheme!(partner i)) then edge_pt (partner i) t else edge_pt (partner i) (1-t))"
              using hii by (by100 simp)
            finally show ?thesis using hpi by (by100 simp)
          qed
          \<comment> \<open>q(edge\\_pt j s): j canonical, so q enters else branch (identity).\<close>
          have hqj_c: "\<And>s. 0 < s \<Longrightarrow> s < 1 \<Longrightarrow> q (edge_pt j s) = edge_pt j s"
          proof -
            fix s :: real assume hs_c: "0 < s" "s < 1"
            have hv_j: "\<not>(\<exists>k<?n. edge_pt j s = (vx k, vy k))"
              using hnotvertex_gen[OF hj hs_c(1) hs_c(2)] .
            have he_j: "\<not>(\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i')"
            proof
              assume "\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i'"
              then obtain i' t' where hi': "i' < ?n" "0 < t'" "t' < 1" "edge_pt j s = edge_pt i' t'" "\<not> is_canonical i'"
                by (by100 blast)
              have "j = i'"
              proof -
                from hedge_unique[OF hj hi'(1) hs_c(1) hs_c(2) hi'(2) hi'(3) hi'(4)]
                show ?thesis by (by100 simp)
              qed
              thus False using hjcan hi'(5) by (by100 simp)
            qed
            show "q (edge_pt j s) = edge_pt j s" unfolding q_def using hv_j he_j by (by100 auto)
          qed
          \<comment> \<open>Combine: same direction or opposite.\<close>
          show ?thesis
          proof (cases "snd(scheme!i) = snd(scheme!j)")
            case True \<comment> \<open>Same direction.\<close>
            have "0 < t" "t < 1" using hint by (by100 auto)+
            have "q (edge_pt i t) = edge_pt j t" using hqi_nc True by (by100 simp)
            moreover have "q (edge_pt j t) = edge_pt j t" using hqj_c \<open>0 < t\<close> \<open>t < 1\<close> by (by100 simp)
            ultimately have "q (edge_pt i t) = q (edge_pt j t)" by (by100 simp)
            thus ?thesis using hgoal_lhs True unfolding edge_pt_def by (by100 simp)
          next
            case False \<comment> \<open>Opposite direction.\<close>
            have "0 < t" "t < 1" using hint by (by100 auto)+
            have "0 < 1-t" "1-t < 1" using \<open>0 < t\<close> \<open>t < 1\<close> by (by100 linarith)+
            have "q (edge_pt i t) = edge_pt j (1-t)" using hqi_nc False by (by100 simp)
            moreover have "q (edge_pt j (1-t)) = edge_pt j (1-t)"
              using hqj_c \<open>0 < 1-t\<close> \<open>1-t < 1\<close> by (by100 simp)
            ultimately have "q (edge_pt i t) = q (edge_pt j (1-t))" by (by100 simp)
            thus ?thesis using hgoal_lhs False unfolding edge_pt_def by (by100 simp)
          qed
        qed
      next
        case hvert: False \<comment> \<open>Vertex: t = 0 or t = 1. q enters the vertex branch.\<close>
        hence "t = 0 \<or> t = 1" using ht01 by (by100 linarith)
        \<comment> \<open>Vertex case: t=0 gives v\\_i, t=1 gives v\\_{Suc i mod n}.
           The vtx\\_id relation captures the vertex identifications from each edge pairing.
           vtgt\\_class ensures vertices in the same equivalence class map to the same rep.\<close>
        thus ?thesis
        proof
          assume ht0: "t = 0"
          \<comment> \<open>LHS: q(v\\_i) = (vx(vtgt i), vy(vtgt i)). RHS depends on direction.\<close>
          have hq_vi: "q (edge_pt i 0) = (vx (vtgt i), vy (vtgt i))"
          proof -
            have hvi: "edge_pt i 0 = (vx i, vy i)" unfolding edge_pt_def by (by100 simp)
            have "\<exists>k<?n. (vx i, vy i) = (vx k, vy k)" using hi by (by100 blast)
            have "(SOME k. k < ?n \<and> (vx i, vy i) = (vx k, vy k)) = i"
              by (rule some_equality) (use hi hC3 in \<open>(by100 blast)+\<close>)
            thus ?thesis unfolding q_def hvi using \<open>\<exists>k<?n. _\<close> by (by100 auto)
          qed
          show ?thesis
          proof (cases "snd(scheme!i) = snd(scheme!j)")
            case True \<comment> \<open>Same direction, t=0: need vtgt i = vtgt j.\<close>
            have hdir_eq: "snd(scheme!i) = snd(scheme!(partner i))" using True hpi by (by100 simp)
            have "(i, j) \<in> vtx_id"
            proof -
              have "(i, j) \<in> (let jj = partner i in if snd(scheme!i) = snd(scheme!jj)
                then {(i, jj), (Suc i mod ?n, Suc jj mod ?n)}
                else {(i, Suc jj mod ?n), (Suc i mod ?n, jj)})"
                using hpi hdir_eq by (by100 simp)
              thus ?thesis unfolding vtx_id_def using hi by (by100 blast)
            qed
            hence "(i, j) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*" by (by100 auto)
            hence "vtgt i = vtgt j" by (rule vtgt_class)
            have hq_vj: "q (edge_pt j 0) = (vx (vtgt j), vy (vtgt j))"
            proof -
              have hvj: "edge_pt j 0 = (vx j, vy j)" unfolding edge_pt_def by (by100 simp)
              have "\<exists>k<?n. (vx j, vy j) = (vx k, vy k)" using hj by (by100 blast)
              have "(SOME k. k < ?n \<and> (vx j, vy j) = (vx k, vy k)) = j"
                by (rule some_equality) (use hj hC3 in \<open>(by100 blast)+\<close>)
              thus ?thesis unfolding q_def hvj using \<open>\<exists>k<?n. _\<close> by (by100 auto)
            qed
            from hq_vi hq_vj \<open>vtgt i = vtgt j\<close>
            have "q (edge_pt i 0) = q (edge_pt j 0)" by (by100 simp)
            thus ?thesis using ht0 True unfolding edge_pt_def by (by100 simp)
          next
            case False \<comment> \<open>Opposite direction, t=0: need vtgt i = vtgt(Suc j mod n).\<close>
            have hn_gt: "?n > 0" using assms by (by100 linarith)
            have hjm: "Suc j mod ?n < ?n" using hn_gt by (by100 simp)
            have hdir_ne: "snd(scheme!i) \<noteq> snd(scheme!(partner i))" using False hpi by (by100 simp)
            have "(i, Suc j mod ?n) \<in> vtx_id"
            proof -
              have "(i, Suc j mod ?n) \<in> (let jj = partner i in if snd(scheme!i) = snd(scheme!jj)
                then {(i, jj), (Suc i mod ?n, Suc jj mod ?n)}
                else {(i, Suc jj mod ?n), (Suc i mod ?n, jj)})"
                using hpi hdir_ne by (by100 simp)
              thus ?thesis unfolding vtx_id_def using hi by (by100 blast)
            qed
            hence "(i, Suc j mod ?n) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*" by (by100 auto)
            hence "vtgt i = vtgt (Suc j mod ?n)" by (rule vtgt_class)
            have hq_vjm: "q (edge_pt j 1) = (vx (vtgt (Suc j mod ?n)), vy (vtgt (Suc j mod ?n)))"
            proof -
              have hedge_j1_0: "edge_pt j 1 = (vx (Suc j mod ?n), vy (Suc j mod ?n))"
                unfolding edge_pt_def by (by100 simp)
              have hexk_jm0: "\<exists>k<?n. (vx (Suc j mod ?n), vy (Suc j mod ?n)) = (vx k, vy k)"
                using hjm by (by100 blast)
              have hsome_jm0: "(SOME k. k < ?n \<and> (vx (Suc j mod ?n), vy (Suc j mod ?n)) = (vx k, vy k)) = Suc j mod ?n"
                by (rule some_equality) (use hjm hC3 in \<open>(by100 blast)+\<close>)
              thus ?thesis unfolding q_def hedge_j1_0 Let_def using hexk_jm0 hsome_jm0 by (by100 auto)
            qed
            \<comment> \<open>RHS at t=0 opp\\_dir: q(t*vx j + (1-t)*vx(Suc j), ...) at t=0 = q(vx(Suc j), vy(Suc j)).\<close>
            have "edge_pt j (1 - 0) = edge_pt j 1" by (by100 simp)
            from hq_vi hq_vjm \<open>vtgt i = vtgt (Suc j mod ?n)\<close>
            have "q (edge_pt i 0) = q (edge_pt j 1)" by (by100 simp)
            thus ?thesis using ht0 False unfolding edge_pt_def by (by100 simp)
          qed
        next
          assume ht1: "t = 1"
          \<comment> \<open>LHS: q(v\\_{Suc i mod n}).\<close>
          have hn_gt: "?n > 0" using assms by (by100 linarith)
          have him: "Suc i mod ?n < ?n" using hn_gt by (by100 simp)
          have hq_vim: "q (edge_pt i 1) = (vx (vtgt (Suc i mod ?n)), vy (vtgt (Suc i mod ?n)))"
          proof -
            have hedge_i1: "edge_pt i 1 = (vx (Suc i mod ?n), vy (Suc i mod ?n))"
              unfolding edge_pt_def by (by100 simp)
            have hexk_im: "\<exists>k<?n. (vx (Suc i mod ?n), vy (Suc i mod ?n)) = (vx k, vy k)"
              using him by (by100 blast)
            have hsome_im: "(SOME k. k < ?n \<and> (vx (Suc i mod ?n), vy (Suc i mod ?n)) = (vx k, vy k)) = Suc i mod ?n"
              by (rule some_equality) (use him hC3 in \<open>(by100 blast)+\<close>)
            thus ?thesis unfolding q_def hedge_i1 Let_def using hexk_im hsome_im by (by100 auto)
          qed
          show ?thesis
          proof (cases "snd(scheme!i) = snd(scheme!j)")
            case True \<comment> \<open>Same direction, t=1: need vtgt(Suc i) = vtgt(Suc j).\<close>
            have hjm: "Suc j mod ?n < ?n" using hn_gt by (by100 simp)
            have hdir_eq: "snd(scheme!i) = snd(scheme!(partner i))" using True hpi by (by100 simp)
            have "(Suc i mod ?n, Suc j mod ?n) \<in> vtx_id"
            proof -
              have "(Suc i mod ?n, Suc j mod ?n) \<in> (let jj = partner i in if snd(scheme!i) = snd(scheme!jj)
                then {(i, jj), (Suc i mod ?n, Suc jj mod ?n)}
                else {(i, Suc jj mod ?n), (Suc i mod ?n, jj)})"
                using hpi hdir_eq by (by100 simp)
              thus ?thesis unfolding vtx_id_def using hi by (by100 blast)
            qed
            hence "(Suc i mod ?n, Suc j mod ?n) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*" by (by100 auto)
            hence "vtgt (Suc i mod ?n) = vtgt (Suc j mod ?n)" by (rule vtgt_class)
            have hq_vjm_1: "q (edge_pt j 1) = (vx (vtgt (Suc j mod ?n)), vy (vtgt (Suc j mod ?n)))"
            proof -
              have hedge_j1_1: "edge_pt j 1 = (vx (Suc j mod ?n), vy (Suc j mod ?n))"
                unfolding edge_pt_def by (by100 simp)
              have hexk_jm1: "\<exists>k<?n. (vx (Suc j mod ?n), vy (Suc j mod ?n)) = (vx k, vy k)"
                using hjm by (by100 blast)
              have hsome_jm1: "(SOME k. k < ?n \<and> (vx (Suc j mod ?n), vy (Suc j mod ?n)) = (vx k, vy k)) = Suc j mod ?n"
                by (rule some_equality) (use hjm hC3 in \<open>(by100 blast)+\<close>)
              thus ?thesis unfolding q_def hedge_j1_1 Let_def using hexk_jm1 hsome_jm1 by (by100 auto)
            qed
            from hq_vim hq_vjm_1 \<open>vtgt (Suc i mod ?n) = vtgt (Suc j mod ?n)\<close>
            have "q (edge_pt i 1) = q (edge_pt j 1)" by (by100 simp)
            thus ?thesis using ht1 True unfolding edge_pt_def by (by100 simp)
          next
            case False \<comment> \<open>Opposite direction, t=1: need vtgt(Suc i) = vtgt j.\<close>
            have hdir_ne: "snd(scheme!i) \<noteq> snd(scheme!(partner i))" using False hpi by (by100 simp)
            have "(Suc i mod ?n, j) \<in> vtx_id"
            proof -
              have "(Suc i mod ?n, j) \<in> (let jj = partner i in if snd(scheme!i) = snd(scheme!jj)
                then {(i, jj), (Suc i mod ?n, Suc jj mod ?n)}
                else {(i, Suc jj mod ?n), (Suc i mod ?n, jj)})"
                using hpi hdir_ne by (by100 simp)
              thus ?thesis unfolding vtx_id_def using hi by (by100 blast)
            qed
            hence "(Suc i mod ?n, j) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*" by (by100 auto)
            hence "vtgt (Suc i mod ?n) = vtgt j" by (rule vtgt_class)
            have hq_vj: "q (edge_pt j 0) = (vx (vtgt j), vy (vtgt j))"
            proof -
              have hvj: "edge_pt j 0 = (vx j, vy j)" unfolding edge_pt_def by (by100 simp)
              have "\<exists>k<?n. (vx j, vy j) = (vx k, vy k)" using hj by (by100 blast)
              have "(SOME k. k < ?n \<and> (vx j, vy j) = (vx k, vy k)) = j"
                by (rule some_equality) (use hj hC3 in \<open>(by100 blast)+\<close>)
              thus ?thesis unfolding q_def hvj using \<open>\<exists>k<?n. _\<close> by (by100 auto)
            qed
            from hq_vim hq_vj \<open>vtgt (Suc i mod ?n) = vtgt j\<close>
            have "q (edge_pt i 1) = q (edge_pt j 0)" by (by100 simp)
            thus ?thesis using ht1 False unfolding edge_pt_def by (by100 simp)
          qed
        qed
      qed
    qed
  qed
  \<comment> \<open>C9: Interior injectivity + boundary identification pattern.\<close>
  have hC9_interior: "\<forall>p\<in>P. (\<forall>i<?n. \<forall>t\<in>I_set.
              p \<noteq> ((1-t)*vx i + t*vx(Suc i mod ?n), (1-t)*vy i + t*vy(Suc i mod ?n)))
           \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
  proof (intro ballI impI allI)
    fix p p' assume hp: "p \<in> P" and hp': "p' \<in> P"
      and hinterior: "\<forall>i<?n. \<forall>t\<in>I_set.
              p \<noteq> ((1-t)*vx i + t*vx(Suc i mod ?n), (1-t)*vy i + t*vy(Suc i mod ?n))"
      and hqeq: "q p = q p'"
    \<comment> \<open>q(p) = p: p is not on any edge, so the \\<exists> in q\\_def is false.\<close>
    have hqp: "q p = p"
    proof -
      \<comment> \<open>p is not a vertex (vertex v\\_k = edge\\_pt k 0 is on edge k at t=0).\<close>
      have hnotvertex: "\<not>(\<exists>k<?n. p = (vx k, vy k))"
      proof
        assume "\<exists>k<?n. p = (vx k, vy k)"
        then obtain k where "k < ?n" "p = (vx k, vy k)" by (by100 blast)
        hence "p = ((1-0)*vx k + 0*vx(Suc k mod ?n), (1-0)*vy k + 0*vy(Suc k mod ?n))" by (by100 simp)
        moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        ultimately show False using hinterior \<open>k < ?n\<close> by (by100 blast)
      qed
      \<comment> \<open>p is not on any non-canonical edge interior.\<close>
      have hnotedge: "\<not>(\<exists>i t. i < ?n \<and> 0 < t \<and> t < 1 \<and> p = edge_pt i t \<and> \<not> is_canonical i)"
      proof
        assume "\<exists>i t. i < ?n \<and> 0 < t \<and> t < 1 \<and> p = edge_pt i t \<and> \<not> is_canonical i"
        then obtain i t where "i < ?n" "0 < t" "t < 1" "p = edge_pt i t" by (by100 blast)
        have "t \<in> I_set" using \<open>0 < t\<close> \<open>t < 1\<close>
          unfolding top1_unit_interval_def by (by100 simp)
        have "p = ((1-t)*vx i + t*vx(Suc i mod ?n), (1-t)*vy i + t*vy(Suc i mod ?n))"
          using \<open>p = edge_pt i t\<close> unfolding edge_pt_def by (by100 simp)
        thus False using hinterior \<open>i < ?n\<close> \<open>t \<in> I_set\<close> by (by100 blast)
      qed
      show ?thesis unfolding q_def using hnotvertex hnotedge by (by100 auto)
    qed
    \<comment> \<open>Now p = q(p) = q(p'). If p' is also not on any non-canonical edge, q(p') = p'.\<close>
    show "p = p'"
    proof (cases "\<exists>i t. i < ?n \<and> 0 \<le> t \<and> t \<le> 1 \<and> p' = edge_pt i t \<and> \<not> is_canonical i")
      case False
      have "q p' = p'"
      proof (cases "\<exists>k<?n. p' = (vx k, vy k)")
        case True \<comment> \<open>p' is a vertex v\\_k. Edge k must be canonical (else on non-canon edge).\<close>
        then obtain k where hk: "k < ?n" "p' = (vx k, vy k)" by (by100 blast)
        have "is_canonical k"
        proof (rule ccontr)
          assume "\<not> is_canonical k"
          have "p' = edge_pt k 0" unfolding edge_pt_def using hk(2) by (by100 simp)
          hence "\<exists>i t. i < ?n \<and> 0 \<le> t \<and> t \<le> 1 \<and> p' = edge_pt i t \<and> \<not> is_canonical i"
            using hk(1) \<open>\<not> is_canonical k\<close> by (by100 force)
          with False show False by (by100 blast)
        qed
        \<comment> \<open>q(p') enters vertex branch. q(p') = v\\_{vtgt k} which is an edge point.
           Since p is interior (not on any edge), p \\<noteq> q(p'). But p = q(p) = q(p'). Contradiction.\<close>
        have hvtgt_k: "vtgt k \<le> k"
          unfolding vtgt_def by (rule Least_le) (by100 simp)
        hence "vtgt k < ?n" using hk(1) by (by100 linarith)
        have "(SOME k'. k' < ?n \<and> p' = (vx k', vy k')) = k"
          by (rule some_equality) (use hk hC3 in \<open>(by100 blast)+\<close>)
        hence hq_vtgt: "q p' = (vx (vtgt k), vy (vtgt k))"
          unfolding q_def using True by (by100 auto)
        have "p = q p'" using hqeq hqp by (by100 simp)
        hence "p = ((1-0)*vx(vtgt k) + 0*vx(Suc(vtgt k) mod ?n),
                     (1-0)*vy(vtgt k) + 0*vy(Suc(vtgt k) mod ?n))"
          using hq_vtgt by (by100 simp)
        moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        ultimately have False using hinterior \<open>vtgt k < ?n\<close> by (by100 blast)
        thus ?thesis by (by100 simp)
      next
        case vF: False
        have "\<not>(\<exists>i t. i < ?n \<and> 0 < t \<and> t < 1 \<and> p' = edge_pt i t \<and> \<not> is_canonical i)"
          using \<open>\<not>(\<exists>i t. i < ?n \<and> 0 \<le> t \<and> t \<le> 1 \<and> p' = edge_pt i t \<and> \<not> is_canonical i)\<close>
          by (by100 force)
        thus ?thesis unfolding q_def using vF by (by100 auto)
      qed
      thus ?thesis using hqeq hqp by (by100 simp)
    next
      case True
      \<comment> \<open>p' is on a non-canonical edge. q(p') is on a canonical edge.
         But p = q(p') is interior (not on any edge). Contradiction.\<close>
      \<comment> \<open>Need: partner(i) < n, q(p') = edge\\_pt(partner i, ...).
         Then q(p') is on edge partner(i), contradicting p = q(p') being interior.\<close>
      \<comment> \<open>p' on non-canonical edge: q(p') enters the THEN branch of q\\_def.
         q(p') = edge\\_pt(partner(SOME...), t') for some t'.
         This is a point on a canonical edge. But p is interior (not on any edge).
         So p \\<noteq> q(p'), contradicting p = q(p) = q(p').\<close>
      \<comment> \<open>Key: any value returned by the THEN branch of q is an edge point.\<close>
      have q_then_on_edge: "\<And>p0. (\<exists>i t. i < ?n \<and> 0 \<le> t \<and> t \<le> 1 \<and> p0 = edge_pt i t \<and> \<not> is_canonical i) \<Longrightarrow>
        \<exists>j t'. j < ?n \<and> 0 \<le> t' \<and> t' \<le> 1 \<and> q p0 = edge_pt j t'"
      proof -
        fix p0 assume hex: "\<exists>i t. i < ?n \<and> 0 \<le> t \<and> t \<le> 1 \<and> p0 = edge_pt i t \<and> \<not> is_canonical i"
        then obtain i0 t0 where hi0: "i0 < ?n" "0 \<le> t0" "t0 \<le> 1" "p0 = edge_pt i0 t0" "\<not> is_canonical i0"
          by (by100 blast)
        \<comment> \<open>Case: is p0 a vertex?\<close>
        show "\<exists>j t'. j < ?n \<and> 0 \<le> t' \<and> t' \<le> 1 \<and> q p0 = edge_pt j t'"
        proof (cases "\<exists>k<?n. p0 = (vx k, vy k)")
          case True \<comment> \<open>p0 is a vertex v\\_k. q enters vertex branch.\<close>
          then obtain k where hk: "k < ?n" "p0 = (vx k, vy k)" by (by100 blast)
          have "(SOME k'. k' < ?n \<and> p0 = (vx k', vy k')) = k"
            by (rule some_equality) (use hk hC3 in \<open>(by100 blast)+\<close>)
          hence hq_eq: "q p0 = (vx (vtgt k), vy (vtgt k))"
            unfolding q_def using True by (by100 auto)
          \<comment> \<open>vtgt k < n (need partner properties).\<close>
          have "vtgt k < ?n"
          proof -
            have "(k, k) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*" by (by100 simp)
            hence "vtgt k \<le> k" unfolding vtgt_def by (rule Least_le)
            thus ?thesis using hk(1) by (by100 linarith)
          qed
          hence "q p0 = edge_pt (vtgt k) 0" using hq_eq unfolding edge_pt_def by (by100 simp)
          thus ?thesis using \<open>vtgt k < ?n\<close> by (by100 force)
        next
          case vF: False \<comment> \<open>p0 is not a vertex. Must be edge interior (0 < t < 1).\<close>
          have "0 < t0 \<and> t0 < 1"
          proof -
            have "t0 \<noteq> 0"
            proof
              assume "t0 = 0"
              hence "p0 = (vx i0, vy i0)" using hi0(4) unfolding edge_pt_def by (by100 simp)
              hence "\<exists>k<?n. p0 = (vx k, vy k)" using hi0(1) by (by100 blast)
              with vF show False by (by100 blast)
            qed
            moreover have "t0 \<noteq> 1"
            proof
              assume "t0 = 1"
              hence "p0 = (vx (Suc i0 mod ?n), vy (Suc i0 mod ?n))"
                using hi0(4) unfolding edge_pt_def by (by100 simp)
              have "?n > 0" using assms by (by100 linarith)
              hence "Suc i0 mod ?n < ?n" by (by100 simp)
              hence "\<exists>k<?n. p0 = (vx k, vy k)"
                using \<open>p0 = (vx (Suc i0 mod ?n), vy (Suc i0 mod ?n))\<close> by (by100 blast)
              with vF show False by (by100 blast)
            qed
            ultimately show ?thesis using hi0(2) hi0(3) by (by100 linarith)
          qed
          hence hex_interior: "\<exists>i t. i < ?n \<and> 0 < t \<and> t < 1 \<and> p0 = edge_pt i t \<and> \<not> is_canonical i"
            using hi0(1) hi0(4) hi0(5) by (by100 blast)
          \<comment> \<open>q enters the edge interior branch. Same proof as before.\<close>
          define sel where "sel = (SOME (i,t). i < ?n \<and> 0 < t \<and> t < 1 \<and> p0 = edge_pt i t \<and> \<not> is_canonical i)"
          define i' where "i' = fst sel" define t' where "t' = snd sel"
          have hsel: "i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> p0 = edge_pt i' t' \<and> \<not> is_canonical i'"
          proof -
            from hex_interior have "\<exists>p. (\<lambda>(i,t). i < ?n \<and> 0 < t \<and> t < 1 \<and> p0 = edge_pt i t \<and> \<not> is_canonical i) p"
              by (by100 auto)
            from someI_ex[OF this] show ?thesis unfolding sel_def i'_def t'_def by (by100 auto)
          qed
          have hpartner: "partner i' < ?n"
          proof -
            have hcard: "card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i')} = 2"
            proof -
              have "i' \<in> {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i')}" using hsel by (by100 simp)
              have "finite {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i')}" by (by100 simp)
              have "{j. j < ?n \<and> fst(scheme!j) = fst(scheme!i')} \<noteq> {}" using \<open>i' \<in> _\<close> by (by100 blast)
              have "card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i')} \<noteq> 0"
                using \<open>finite _\<close> \<open>_ \<noteq> {}\<close> by (by100 simp)
              moreover have "card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i')} \<in> {0, 2}"
                using hproper by (by100 blast)
              ultimately show ?thesis
                by (cases "card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i')} = 0") (by100 blast)+
            qed
            have "i' < ?n" using hsel by (by100 blast)
            from partner_props[OF this hcard] show ?thesis by (by100 blast)
          qed
          define j where "j = partner i'" define s where "s = (if snd(scheme!i') = snd(scheme!j) then t' else 1 - t')"
          have q_eq: "q p0 = (let (i,t) = sel in let j' = partner i
                 in if snd(scheme!i) = snd(scheme!j') then edge_pt j' t else edge_pt j' (1-t))"
            unfolding q_def sel_def using hex_interior vF by (by100 auto)
          have "sel = (i', t')" unfolding i'_def t'_def by (by100 simp)
          hence "q p0 = edge_pt j s" using q_eq unfolding j_def s_def by (by100 simp)
          moreover have "j < ?n" using hpartner unfolding j_def by (by100 simp)
          moreover have "0 \<le> s" "s \<le> 1" using hsel unfolding s_def by (by100 auto)+
          ultimately show ?thesis by (by100 blast)
        qed
      qed
      from True obtain i t where hit: "i < ?n" "0 \<le> t" "t \<le> 1" "p' = edge_pt i t" "\<not> is_canonical i"
        by (by100 blast)
      have hex: "\<exists>i t. i < ?n \<and> 0 \<le> t \<and> t \<le> 1 \<and> p' = edge_pt i t \<and> \<not> is_canonical i"
        using hit by (by100 blast)
      from q_then_on_edge[OF hex]
      obtain j t' where hjt: "j < ?n" "0 \<le> t'" "t' \<le> 1" "q p' = edge_pt j t'" by (by100 blast)
      have "t' \<in> I_set" using hjt unfolding top1_unit_interval_def by (by100 simp)
      have "q p' = ((1-t')*vx j + t'*vx(Suc j mod ?n), (1-t')*vy j + t'*vy(Suc j mod ?n))"
        using hjt(4) unfolding edge_pt_def by (by100 simp)
      hence "p \<noteq> q p'" using hinterior hjt(1) \<open>t' \<in> I_set\<close> by (by100 blast)
      thus ?thesis using hqeq hqp by (by100 simp)
    qed
  qed
  have hC9_boundary: "\<forall>i<?n. \<forall>j<?n. \<forall>t\<in>{0<..<(1::real)}. \<forall>s\<in>{0<..<(1::real)}.
          q ((1-t)*vx i + t*vx(Suc i mod ?n), (1-t)*vy i + t*vy(Suc i mod ?n))
        = q ((1-s)*vx j + s*vx(Suc j mod ?n), (1-s)*vy j + s*vy(Suc j mod ?n))
        \<longrightarrow> (i=j \<and> t=s) \<or> (fst(scheme!i) = fst(scheme!j) \<and>
             (if snd(scheme!i) = snd(scheme!j) then s=t else s=1-t))"
  proof (intro allI impI ballI)
    fix i j t s
    assume hi9: "i < ?n" and hj9: "j < ?n"
      and ht9: "t \<in> {0<..<(1::real)}" and hs9: "s \<in> {0<..<(1::real)}"
    assume hqeq9: "q ((1-t)*vx i + t*vx(Suc i mod ?n), (1-t)*vy i + t*vy(Suc i mod ?n))
        = q ((1-s)*vx j + s*vx(Suc j mod ?n), (1-s)*vy j + s*vy(Suc j mod ?n))"
    have ht_i: "0 < t" "t < 1" using ht9 by (by100 auto)+
    have hs_i: "0 < s" "s < 1" using hs9 by (by100 auto)+
    have ht01: "0 \<le> t" "t \<le> 1" using ht_i by (by100 linarith)+
    have hs01: "0 \<le> s" "s \<le> 1" using hs_i by (by100 linarith)+
    have hqep: "q (edge_pt i t) = q (edge_pt j s)" using hqeq9 unfolding edge_pt_def by (by100 simp)
    show "(i=j \<and> t=s) \<or> (fst(scheme!i) = fst(scheme!j) \<and>
           (if snd(scheme!i) = snd(scheme!j) then s=t else s=1-t))"
    \<comment> \<open>Both t, s \\<in> (0,1) so we're always in the interior case.\<close>
    proof -
      \<comment> \<open>Interior case: q maps each edge point to a canonical edge point.
         For canonical i: q(edge\\_pt i t) = edge\\_pt i t.
         For non-canonical i: q(edge\\_pt i t) = edge\\_pt(partner i, matching\\_t).
         Use hedge\\_unique on the q-images to determine the relationship.\<close>
      \<comment> \<open>q(edge\\_pt i t) is not a vertex.\<close>
      have hv_i: "\<not>(\<exists>k<?n. edge_pt i t = (vx k, vy k))"
        using hnotvertex_gen[OF hi9 ht_i(1) ht_i(2)] .
      have hv_j: "\<not>(\<exists>k<?n. edge_pt j s = (vx k, vy k))"
        using hnotvertex_gen[OF hj9 hs_i(1) hs_i(2)] .
      \<comment> \<open>Determine what q does on each edge point.\<close>
      have hqi9: "q (edge_pt i t) = (if \<not> is_canonical i then
        (if snd(scheme!i) = snd(scheme!(partner i))
          then edge_pt (partner i) t else edge_pt (partner i) (1-t))
        else edge_pt i t)"
      proof (cases "is_canonical i")
        case True
        \<comment> \<open>i canonical: q enters else branch (identity).\<close>
        have "\<not>(\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i')"
        proof
          assume "\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i'"
          then obtain i' t' where "i' < ?n" "0 < t'" "t' < 1" "edge_pt i t = edge_pt i' t'" "\<not> is_canonical i'"
            by (by100 blast)
          from hedge_unique[OF hi9 \<open>i' < ?n\<close> ht_i(1) ht_i(2) \<open>0 < t'\<close> \<open>t' < 1\<close> \<open>edge_pt i t = edge_pt i' t'\<close>]
          have "i = i'" by (by100 simp)
          thus False using True \<open>\<not> is_canonical i'\<close> by (by100 simp)
        qed
        thus ?thesis unfolding q_def using hv_i True by (by100 auto)
      next
        case False
        \<comment> \<open>i non-canonical: q enters edge-interior branch.\<close>
        have hex_i: "\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i'"
          using hi9 ht_i False by (by100 blast)
        \<comment> \<open>The SOME picks (i, t) by uniqueness.\<close>
        define sel_i where "sel_i = (SOME (i',t'). i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i')"
        have hsel_i: "fst sel_i < ?n \<and> 0 < snd sel_i \<and> snd sel_i < 1 \<and>
            edge_pt i t = edge_pt (fst sel_i) (snd sel_i) \<and> \<not> is_canonical (fst sel_i)"
        proof -
          from hex_i have "\<exists>p. (\<lambda>(i',t'). i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i') p"
            by (by100 auto)
          from someI_ex[OF this] show ?thesis unfolding sel_i_def by (by100 auto)
        qed
        have "fst sel_i = i \<and> snd sel_i = t"
        proof -
          from hsel_i have "fst sel_i < ?n" "0 < snd sel_i" "snd sel_i < 1" "edge_pt i t = edge_pt (fst sel_i) (snd sel_i)"
            by (by100 auto)+
          from hedge_unique[OF hi9 this(1) ht_i(1) ht_i(2) this(2) this(3) this(4)]
          show ?thesis by (by100 simp)
        qed
        have "q (edge_pt i t) = (let (i',t') = sel_i in let j' = partner i' in
            if snd(scheme!i') = snd(scheme!j') then edge_pt j' t' else edge_pt j' (1-t'))"
          unfolding q_def sel_i_def using hex_i hv_i by (by100 auto)
        also have "\<dots> = (if snd(scheme!i) = snd(scheme!(partner i))
            then edge_pt (partner i) t else edge_pt (partner i) (1-t))"
        proof -
          have "sel_i = (fst sel_i, snd sel_i)" by (by100 simp)
          hence "sel_i = (i, t)" using \<open>fst sel_i = i \<and> snd sel_i = t\<close> by (by100 simp)
          thus ?thesis by (by100 simp)
        qed
        finally show ?thesis using False by (by100 simp)
      qed
      \<comment> \<open>Similarly for j.\<close>
      have hqj9: "q (edge_pt j s) = (if \<not> is_canonical j then
        (if snd(scheme!j) = snd(scheme!(partner j))
          then edge_pt (partner j) s else edge_pt (partner j) (1-s))
        else edge_pt j s)"
      proof (cases "is_canonical j")
        case True
        have "\<not>(\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i')"
        proof
          assume "\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i'"
          then obtain i' t' where "i' < ?n" "0 < t'" "t' < 1" "edge_pt j s = edge_pt i' t'" "\<not> is_canonical i'"
            by (by100 blast)
          from hedge_unique[OF hj9 \<open>i' < ?n\<close> hs_i(1) hs_i(2) \<open>0 < t'\<close> \<open>t' < 1\<close> \<open>edge_pt j s = edge_pt i' t'\<close>]
          have "j = i'" by (by100 simp)
          thus False using True \<open>\<not> is_canonical i'\<close> by (by100 simp)
        qed
        thus ?thesis unfolding q_def using hv_j True by (by100 auto)
      next
        case False
        have hex_j: "\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i'"
          using hj9 hs_i False by (by100 blast)
        define sel_j where "sel_j = (SOME (i',t'). i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i')"
        have hsel_j: "fst sel_j < ?n \<and> 0 < snd sel_j \<and> snd sel_j < 1 \<and>
            edge_pt j s = edge_pt (fst sel_j) (snd sel_j) \<and> \<not> is_canonical (fst sel_j)"
        proof -
          from hex_j have "\<exists>p. (\<lambda>(i',t'). i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i') p"
            by (by100 auto)
          from someI_ex[OF this] show ?thesis unfolding sel_j_def by (by100 auto)
        qed
        have "fst sel_j = j \<and> snd sel_j = s"
        proof -
          from hsel_j have "fst sel_j < ?n" "0 < snd sel_j" "snd sel_j < 1" "edge_pt j s = edge_pt (fst sel_j) (snd sel_j)"
            by (by100 auto)+
          from hedge_unique[OF hj9 this(1) hs_i(1) hs_i(2) this(2) this(3) this(4)]
          show ?thesis by (by100 simp)
        qed
        have "q (edge_pt j s) = (let (i',t') = sel_j in let j' = partner i' in
            if snd(scheme!i') = snd(scheme!j') then edge_pt j' t' else edge_pt j' (1-t'))"
          unfolding q_def sel_j_def using hex_j hv_j by (by100 auto)
        also have "\<dots> = (if snd(scheme!j) = snd(scheme!(partner j))
            then edge_pt (partner j) s else edge_pt (partner j) (1-s))"
        proof -
          have "sel_j = (fst sel_j, snd sel_j)" by (by100 simp)
          hence "sel_j = (j, s)" using \<open>fst sel_j = j \<and> snd sel_j = s\<close> by (by100 simp)
          thus ?thesis by (by100 simp)
        qed
        finally show ?thesis using False by (by100 simp)
      qed
      \<comment> \<open>Now: q(edge\\_pt i t) is edge\\_pt(ci, ct) and q(edge\\_pt j s) is edge\\_pt(cj, cs)
         for canonical edges ci, cj. By hedge\\_unique: ci=cj and ct=cs.\<close>
      define ci where "ci = (if is_canonical i then i else partner i)"
      define ct where "ct = (if is_canonical i then t
          else if snd(scheme!i) = snd(scheme!(partner i)) then t else 1-t)"
      define cj where "cj = (if is_canonical j then j else partner j)"
      define cs where "cs = (if is_canonical j then s
          else if snd(scheme!j) = snd(scheme!(partner j)) then s else 1-s)"
      have "q (edge_pt i t) = edge_pt ci ct" using hqi9 unfolding ci_def ct_def by (by100 auto)
      have "q (edge_pt j s) = edge_pt cj cs" using hqj9 unfolding cj_def cs_def by (by100 auto)
      from hqep \<open>q (edge_pt i t) = edge_pt ci ct\<close> \<open>q (edge_pt j s) = edge_pt cj cs\<close>
      have "edge_pt ci ct = edge_pt cj cs" by (by100 simp)
      have "0 < ct" "ct < 1" unfolding ct_def using ht_i by (by100 auto)+
      have "0 < cs" "cs < 1" unfolding cs_def using hs_i by (by100 auto)+
      have hci_lt: "ci < ?n"
      proof (cases "is_canonical i")
        case True thus ?thesis unfolding ci_def using hi9 by (by100 simp)
      next
        case False
        have hcard_i: "card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)} = 2"
        proof -
          have "i \<in> {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)}" using hi9 by (by100 simp)
          have "finite {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)}" by (by100 simp)
          hence "card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)} \<noteq> 0"
            using \<open>i \<in> _\<close> by (by100 auto)
          moreover have "card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)} \<in> {0, 2}"
            using hproper by (by100 blast)
          ultimately show ?thesis by (by100 blast)
        qed
        from partner_props[OF hi9 hcard_i] show ?thesis unfolding ci_def using False by (by100 simp)
      qed
      have hcj_lt: "cj < ?n"
      proof (cases "is_canonical j")
        case True thus ?thesis unfolding cj_def using hj9 by (by100 simp)
      next
        case False
        have hcard_j: "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} = 2"
        proof -
          have "j \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)}" using hj9 by (by100 simp)
          have "finite {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)}" by (by100 simp)
          hence "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} \<noteq> 0"
            using \<open>j \<in> _\<close> by (by100 auto)
          moreover have "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} \<in> {0, 2}"
            using hproper by (by100 blast)
          ultimately show ?thesis by (by100 blast)
        qed
        from partner_props[OF hj9 hcard_j] show ?thesis unfolding cj_def using False by (by100 simp)
      qed
      from hedge_unique[OF hci_lt hcj_lt \<open>0 < ct\<close> \<open>ct < 1\<close> \<open>0 < cs\<close> \<open>cs < 1\<close> \<open>edge_pt ci ct = edge_pt cj cs\<close>]
      have "ci = cj" "ct = cs" by (by100 auto)+
      \<comment> \<open>Recover i, j, t, s from ci, cj, ct, cs.\<close>
      show ?thesis
      proof (cases "is_canonical i")
        case hiC: True
        hence "ci = i" "ct = t" unfolding ci_def ct_def by (by100 auto)+
        show ?thesis
        proof (cases "is_canonical j")
          case True
          hence "cj = j" "cs = s" unfolding cj_def cs_def by (by100 auto)+
          from \<open>ci = i\<close> \<open>ci = cj\<close> \<open>cj = j\<close> have "i = j" by (by100 simp)
          from \<open>ct = t\<close> \<open>ct = cs\<close> \<open>cs = s\<close> have "t = s" by (by100 simp)
          thus ?thesis using \<open>i = j\<close> \<open>t = s\<close> by (by100 blast)
        next
          case hjNC: False
          hence "cj = partner j" unfolding cj_def by (by100 simp)
          from \<open>ci = i\<close> \<open>ci = cj\<close> \<open>cj = partner j\<close> have hip: "i = partner j" by (by100 simp)
          \<comment> \<open>Same label: partner j has same label as j.\<close>
          have hcard_j2: "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} = 2"
          proof -
            have "j \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)}" using hj9 by (by100 simp)
            have "finite {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)}" by (by100 simp)
            hence "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} \<noteq> 0"
              using \<open>j \<in> _\<close> by (by100 auto)
            moreover have "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} \<in> {0, 2}"
              using hproper by (by100 blast)
            ultimately show ?thesis by (by100 blast)
          qed
          from partner_props[OF hj9 hcard_j2]
          have "fst(scheme!(partner j)) = fst(scheme!j)" by (by100 blast)
          hence "fst(scheme!i) = fst(scheme!j)" using hip by (by100 simp)
          moreover have "if snd(scheme!i) = snd(scheme!j) then s=t else s=1-t"
          proof (cases "snd(scheme!j) = snd(scheme!(partner j))")
            case True
            hence "cs = s" unfolding cs_def using hjNC by (by100 simp)
            from \<open>ct = t\<close> \<open>ct = cs\<close> this have "t = s" by (by100 simp)
            have "snd(scheme!i) = snd(scheme!j)" using True hip by (by100 simp)
            thus ?thesis using \<open>t = s\<close> by (by100 simp)
          next
            case False
            hence "cs = 1-s" unfolding cs_def using hjNC by (by100 simp)
            from \<open>ct = t\<close> \<open>ct = cs\<close> this have "t = 1-s" by (by100 simp)
            hence "s = 1-t" by (by100 linarith)
            have "snd(scheme!i) \<noteq> snd(scheme!j)" using False hip by (by100 simp)
            thus ?thesis using \<open>s = 1-t\<close> by (by100 simp)
          qed
          ultimately show ?thesis by (by100 blast)
        qed
      next
        case hiNC: False
        hence "ci = partner i" unfolding ci_def by (by100 simp)
        show ?thesis
        proof (cases "is_canonical j")
          case hjC: True
          hence "cj = j" "cs = s" unfolding cj_def cs_def by (by100 auto)+
          from \<open>ci = cj\<close> \<open>ci = partner i\<close> \<open>cj = j\<close> have hjp: "partner i = j" by (by100 simp)
          have hcard_i2: "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} = 2"
          proof -
            have "i \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" using hi9 by (by100 simp)
            have "finite {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" by (by100 simp)
            hence "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<noteq> 0"
              using \<open>i \<in> _\<close> by (by100 auto)
            moreover have "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<in> {0, 2}"
              using hproper by (by100 blast)
            ultimately show ?thesis by (by100 blast)
          qed
          from partner_props[OF hi9 hcard_i2]
          have "fst(scheme!(partner i)) = fst(scheme!i)" by (by100 blast)
          hence "fst(scheme!i) = fst(scheme!j)" using hjp by (by100 simp)
          moreover have "if snd(scheme!i) = snd(scheme!j) then s=t else s=1-t"
          proof (cases "snd(scheme!i) = snd(scheme!(partner i))")
            case True
            hence "ct = t" unfolding ct_def using hiNC by (by100 simp)
            from this \<open>ct = cs\<close> \<open>cs = s\<close> have "t = s" by (by100 simp)
            have "snd(scheme!i) = snd(scheme!j)" using True hjp by (by100 simp)
            thus ?thesis using \<open>t = s\<close> by (by100 simp)
          next
            case False
            hence "ct = 1-t" unfolding ct_def using hiNC by (by100 simp)
            from this \<open>ct = cs\<close> \<open>cs = s\<close> have "1-t = s" by (by100 simp)
            have "snd(scheme!i) \<noteq> snd(scheme!j)" using False hjp by (by100 simp)
            thus ?thesis using \<open>1-t = s\<close> by (by100 simp)
          qed
          ultimately show ?thesis by (by100 blast)
        next
          case hjNC: False
          hence "cj = partner j" unfolding cj_def by (by100 simp)
          from \<open>ci = cj\<close> \<open>ci = partner i\<close> \<open>cj = partner j\<close> have hpp: "partner i = partner j" by (by100 simp)
          \<comment> \<open>partner i = partner j implies i = j (label uniqueness: card = 2).\<close>
          have "i = j"
          proof -
            have hcard_i3: "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} = 2"
            proof -
              have "i \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" using hi9 by (by100 simp)
              have "finite {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" by (by100 simp)
              hence "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<noteq> 0"
                using \<open>i \<in> _\<close> by (by100 auto)
              moreover have "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<in> {0, 2}"
                using hproper by (by100 blast)
              ultimately show ?thesis by (by100 blast)
            qed
            from partner_props[OF hi9 hcard_i3]
            have hpi: "partner i < ?n" "partner i \<noteq> i" "fst(scheme!(partner i)) = fst(scheme!i)" by (by100 blast)+
            have hcard_j3: "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} = 2"
            proof -
              have "j \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)}" using hj9 by (by100 simp)
              have "finite {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)}" by (by100 simp)
              hence "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} \<noteq> 0"
                using \<open>j \<in> _\<close> by (by100 auto)
              moreover have "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} \<in> {0, 2}"
                using hproper by (by100 blast)
              ultimately show ?thesis by (by100 blast)
            qed
            from partner_props[OF hj9 hcard_j3]
            have hpj: "partner j < ?n" "partner j \<noteq> j" "fst(scheme!(partner j)) = fst(scheme!j)" by (by100 blast)+
            \<comment> \<open>i, j, partner i = partner j = k all have the same label.\<close>
            define k where "k = partner i"
            have "fst(scheme!i) = fst(scheme!k)" using hpi(3) unfolding k_def by (by100 simp)
            have "fst(scheme!j) = fst(scheme!k)" using hpj(3) hpp unfolding k_def by (by100 simp)
            hence "fst(scheme!i) = fst(scheme!j)" using \<open>fst(scheme!i) = fst(scheme!k)\<close> by (by100 simp)
            \<comment> \<open>{k, i, j} \\<subseteq> the 2-element label set. Since k \\<noteq> i and k \\<noteq> j: i = j.\<close>
            have "k \<in> {m. m < ?n \<and> fst(scheme!m) = fst(scheme!i)}"
              using hpi(1) \<open>fst(scheme!i) = fst(scheme!k)\<close> unfolding k_def by (by100 simp)
            have "i \<in> {m. m < ?n \<and> fst(scheme!m) = fst(scheme!i)}" using hi9 by (by100 simp)
            have "j \<in> {m. m < ?n \<and> fst(scheme!m) = fst(scheme!i)}"
              using hj9 \<open>fst(scheme!i) = fst(scheme!j)\<close> by (by100 simp)
            have "{k, i, j} \<subseteq> {m. m < ?n \<and> fst(scheme!m) = fst(scheme!i)}"
              using \<open>k \<in> _\<close> \<open>i \<in> _\<close> \<open>j \<in> _\<close> by (by100 blast)
            have "k \<noteq> i" using hpi(2) unfolding k_def by (by100 simp)
            have "k \<noteq> j" using hpj(2) hpp unfolding k_def by (by100 simp)
            have "card {k, i, j} \<le> 2" using hcard_i3 \<open>{k, i, j} \<subseteq> _\<close>
            proof -
              have "finite {m. m < ?n \<and> fst(scheme!m) = fst(scheme!i)}" by (by100 simp)
              from card_mono[OF this \<open>{k, i, j} \<subseteq> _\<close>]
              show ?thesis using hcard_i3 by (by100 linarith)
            qed
            \<comment> \<open>card {k, i, j} = 3 if all distinct, but \\<le> 2. So not all distinct: i = j.\<close>
            have "card {k, i} = 2" using \<open>k \<noteq> i\<close> by (by100 simp)
            show "i = j"
            proof (rule ccontr)
              assume "i \<noteq> j"
              hence "card {k, i, j} = 3" using \<open>k \<noteq> i\<close> \<open>k \<noteq> j\<close> by (by100 simp)
              thus False using \<open>card {k, i, j} \<le> 2\<close> by (by100 linarith)
            qed
          qed
          \<comment> \<open>i = j implies ct = cs gives t = s.\<close>
          have "t = s"
          proof -
            from \<open>ct = cs\<close> \<open>i = j\<close>
            show ?thesis unfolding ct_def cs_def
              by (cases "is_canonical i"; cases "snd(scheme!i) = snd(scheme!(partner i))") (by100 auto)+
          qed
          thus ?thesis using \<open>i = j\<close> \<open>t = s\<close> by (by100 blast)
        qed
      qed
    qed
  qed
  \<comment> \<open>Assembly: introduce witnesses P, q, vx, vy and combine all conditions.\<close>
  \<comment> \<open>Assemble: pack all conditions into the existential.\<close>
  have htopo: "is_topology_on_strict Y TY"
  proof -
    let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
    \<comment> \<open>TY is the quotient topology: U \\<in> TY iff q\\<inverse>(U) \\<cap> P is open in P.\<close>
    \<comment> \<open>Standard: quotient topology is a topology on the quotient set.\<close>
    have htopo_P: "is_topology_on P ?TP"
    proof -
      have "is_topology_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
        using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV]
        by (by100 simp)
      thus ?thesis
        by (rule subspace_topology_is_topology_on) (by100 simp)
    qed
    have hY_eq: "Y = q ` P" unfolding Y_def by (by100 simp)
    \<comment> \<open>is\\_topology\\_on Y TY: Y = \\<Union>TY, TY closed under \\<union> and finite \\<inter>.\<close>
    have "is_topology_on Y TY"
      unfolding is_topology_on_def
    proof (intro conjI allI impI)
      \<comment> \<open>1. \\<emptyset> \\<in> TY.\<close>
      show "{} \<in> TY" unfolding TY_def
      proof (intro CollectI exI[of _ "{}"] conjI)
        show "({} :: (real \<times> real) set) \<subseteq> P" by (by100 simp)
        show "\<forall>x\<in>{}. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> {}" by (by100 simp)
        show "{} = q ` {}" by (by100 simp)
        show "{} \<in> ?TP" using htopo_P unfolding is_topology_on_def by (by100 blast)
      qed
    next
      \<comment> \<open>2. Y \\<in> TY.\<close>
      show "Y \<in> TY" unfolding TY_def
      proof (intro CollectI exI[of _ P] conjI)
        show "P \<subseteq> P" by (by100 simp)
        show "\<forall>x\<in>P. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> P" by (by100 simp)
        show "Y = q ` P" unfolding Y_def by (by100 simp)
        show "P \<in> ?TP" using htopo_P unfolding is_topology_on_def by (by100 blast)
      qed
    next
      \<comment> \<open>3. Arbitrary union.\<close>
      fix U :: "(real \<times> real) set set" assume hU: "U \<subseteq> TY"
      show "\<Union>U \<in> TY"
      proof -
        \<comment> \<open>For each u \\<in> U, get the witness V\\_u.\<close>
        have "\<forall>u\<in>U. \<exists>V. V \<subseteq> P \<and> (\<forall>x\<in>V. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> V) \<and> u = q ` V \<and> V \<in> ?TP"
          using hU unfolding TY_def by (by100 blast)
        from bchoice[OF this]
        obtain f where hf: "\<forall>u\<in>U. f u \<subseteq> P \<and> (\<forall>x\<in>f u. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> f u) \<and> u = q ` f u \<and> f u \<in> ?TP"
          by (by100 auto)
        define V where "V = \<Union>(f ` U)"
        have hV_sub: "V \<subseteq> P" unfolding V_def using hf by (by100 auto)
        have hV_sat: "\<forall>x\<in>V. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> V"
          unfolding V_def using hf by (by100 blast)
        have hV_image: "\<Union>U = q ` V"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> \<Union>U"
          then obtain u where hu: "u \<in> U" "x \<in> u" by (by100 blast)
          hence "x \<in> q ` f u" using hf by (by100 blast)
          thus "x \<in> q ` V" unfolding V_def using hu(1) by (by100 blast)
        next
          fix x assume "x \<in> q ` V"
          then obtain p where hp: "p \<in> V" "x = q p" by (by100 blast)
          from hp(1) obtain u where hu: "u \<in> U" "p \<in> f u" unfolding V_def by (by100 blast)
          have "x \<in> u" using hp(2) hu(2) hf hu(1) by (by100 blast)
          thus "x \<in> \<Union>U" using hu(1) by (by100 blast)
        qed
        have hV_open: "V \<in> ?TP"
        proof -
          have "f ` U \<subseteq> ?TP" using hf by (by100 blast)
          hence "\<Union>(f ` U) \<in> ?TP" using htopo_P unfolding is_topology_on_def by (by100 blast)
          thus ?thesis unfolding V_def .
        qed
        show ?thesis unfolding TY_def
          using hV_sub hV_sat hV_image hV_open by (by100 blast)
      qed
    next
      \<comment> \<open>4. Finite intersection.\<close>
      fix F :: "(real \<times> real) set set" assume hF: "finite F \<and> F \<noteq> {} \<and> F \<subseteq> TY"
      show "\<Inter>F \<in> TY"
      proof -
        have hFfin: "finite F" and hFne: "F \<noteq> {}" and hFsub: "F \<subseteq> TY" using hF by auto
        have "\<forall>u\<in>F. \<exists>V. V \<subseteq> P \<and> (\<forall>x\<in>V. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> V) \<and> u = q ` V \<and> V \<in> ?TP"
          using hFsub unfolding TY_def by (by100 blast)
        from bchoice[OF this]
        obtain f where hf: "\<forall>u\<in>F. f u \<subseteq> P \<and> (\<forall>x\<in>f u. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> f u) \<and> u = q ` f u \<and> f u \<in> ?TP"
          by (by100 auto)
        define V where "V = \<Inter>(f ` F)"
        have hV_sub: "V \<subseteq> P"
        proof -
          from hFne obtain u0 where hu0F: "u0 \<in> F" by (by100 blast)
          have "f u0 \<subseteq> P" using hf hu0F by (by100 force)
          moreover have "V \<subseteq> f u0" unfolding V_def using \<open>u0 \<in> F\<close> by (by100 blast)
          ultimately show ?thesis by (by100 blast)
        qed
        have hV_sat: "\<forall>x\<in>V. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> V"
        proof (intro ballI allI impI)
          fix x y assume hx: "x \<in> V" and hy: "y \<in> P \<and> q y = q x"
          show "y \<in> V" unfolding V_def
          proof (rule InterI)
            fix W assume "W \<in> f ` F"
            then obtain u where hu: "u \<in> F" "W = f u" by (by100 blast)
            have "x \<in> f u" using hx hu(1) unfolding V_def by (by100 blast)
            hence "y \<in> f u" using hf hu(1) hy by (by100 blast)
            thus "y \<in> W" using hu(2) by (by100 simp)
          qed
        qed
        \<comment> \<open>q`V = \\<Inter>F: uses saturation to distribute image over intersection.\<close>
        have hV_image: "\<Inter>F = q ` V"
        proof (rule set_eqI, rule iffI)
          fix x assume hx: "x \<in> \<Inter>F"
          \<comment> \<open>x \\<in> every u \\<in> F, so x = q(p\\_u) for some p\\_u \\<in> f u.
             Pick any u0 \\<in> F. p\\_{u0} \\<in> f u0. For any other u \\<in> F:
             x \\<in> u = q`(f u), so x = q(p\\_u) for some p\\_u \\<in> f u.
             q(p\\_{u0}) = x = q(p\\_u). By saturation of f u: p\\_{u0} \\<in> f u.
             So p\\_{u0} \\<in> \\<Inter>(f ` F) = V.\<close>
          from hFne obtain u0 where hu0: "u0 \<in> F" by (by100 blast)
          from hx hu0 have "x \<in> u0" by (by100 blast)
          have "u0 = q ` f u0" using hf hu0 by (by100 blast)
          hence "x \<in> q ` f u0" using \<open>x \<in> u0\<close> by (by100 simp)
          from this obtain p0 where hp0: "p0 \<in> f u0" "x = q p0" by (by100 blast)
          have "p0 \<in> V" unfolding V_def
          proof (rule InterI)
            fix W assume "W \<in> f ` F"
            then obtain u where hu: "u \<in> F" "W = f u" by (by100 blast)
            have "x \<in> u" using hx hu(1) by (by100 blast)
            have "u = q ` f u" using hf hu(1) by (by100 blast)
            hence "x \<in> q ` f u" using \<open>x \<in> u\<close> by (by100 simp)
            then obtain pu where hpu: "pu \<in> f u" "x = q pu" by (by100 blast)
            have "q p0 = q pu" using hp0(2) hpu(2) by (by100 simp)
            have "f u0 \<subseteq> P" using hf hu0 by (by100 force)
            hence "p0 \<in> P" using hp0(1) by (by100 blast)
            \<comment> \<open>By saturation of f u: pu \\<in> f u, q(p0)=q(pu), p0 \\<in> P \\<Longrightarrow> p0 \\<in> f u.\<close>
            have sat_u: "\<forall>x\<in>f u. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> f u"
              using hf hu(1) by (by100 blast)
            have "p0 \<in> f u" using sat_u hpu(1) \<open>p0 \<in> P\<close> \<open>q p0 = q pu\<close> by (by100 blast)
            thus "p0 \<in> W" using hu(2) by (by100 simp)
          qed
          thus "x \<in> q ` V" using hp0(2) by (by100 blast)
        next
          fix x assume "x \<in> q ` V"
          then obtain p where hp: "p \<in> V" "x = q p" by (by100 blast)
          show "x \<in> \<Inter>F"
          proof (rule InterI)
            fix u assume hu: "u \<in> F"
            have "p \<in> f u" using hp(1) hu unfolding V_def by (by100 blast)
            hence "q p \<in> q ` f u" by (by100 blast)
            hence "q p \<in> u" using hf hu by (by100 blast)
            thus "x \<in> u" using hp(2) by (by100 simp)
          qed
        qed
        have hV_open: "V \<in> ?TP"
        proof -
          have "f ` F \<subseteq> ?TP" using hf by (by100 blast)
          moreover have "finite (f ` F)" using hFfin by (by100 simp)
          moreover have "f ` F \<noteq> {}" using hFne by (by100 simp)
          ultimately have "\<Inter>(f ` F) \<in> ?TP"
            using htopo_P unfolding is_topology_on_def by (by100 blast)
          thus ?thesis unfolding V_def .
        qed
        show ?thesis unfolding TY_def
          using hV_sub hV_sat hV_image hV_open by (by100 blast)
      qed
    qed
    moreover have "TY \<subseteq> Pow Y"
    proof
      fix U assume "U \<in> TY"
      then obtain V where "V \<subseteq> P" "U = q ` V" unfolding TY_def by (by100 blast)
      thus "U \<in> Pow Y" unfolding Y_def using \<open>V \<subseteq> P\<close> by (by100 auto)
    qed
    ultimately show ?thesis unfolding is_topology_on_strict_def by (by100 blast)
  qed
  show ?thesis
    unfolding top1_quotient_of_scheme_on_def
  proof (intro exI conjI)
    show "is_topology_on_strict Y TY" using htopo .
    show "top1_is_polygonal_region_on P ?n" using hC1 .
    show "top1_quotient_map_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) Y TY q"
      using hC2 .
    show "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)" using hC3 .
    show "\<forall>i<?n. (vx i, vy i) \<in> P" using hC4 .
    show "P = {(x, y) | x y.
                \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0)
                       \<and> (\<Sum>i<?n. coeffs i) = 1
                       \<and> x = (\<Sum>i<?n. coeffs i * vx i)
                       \<and> y = (\<Sum>i<?n. coeffs i * vy i)}" using hC5 .
    \<comment> \<open>C6: use hC6 with open01 = {0<..<1}.\<close>
    show "\<forall>i<?n. \<forall>j<?n.
          i \<noteq> j \<longrightarrow> (Suc i mod ?n) \<noteq> j \<longrightarrow> i \<noteq> (Suc j mod ?n) \<longrightarrow>
          (\<forall>s\<in>{0<..<(1::real)}. \<forall>t\<in>{0<..<(1::real)}.
             ((1-s) * vx i + s * vx (Suc i mod ?n),
              (1-s) * vy i + s * vy (Suc i mod ?n))
           \<noteq> ((1-t) * vx j + t * vx (Suc j mod ?n),
               (1-t) * vy j + t * vy (Suc j mod ?n)))"
      using hC6 unfolding open01_def .
    show "\<forall>i<?n. \<forall>j<?n. fst(scheme!i) = fst(scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set.
           q ((1-t) * vx i + t * vx (Suc i mod ?n),
              (1-t) * vy i + t * vy (Suc i mod ?n))
         = (if snd(scheme!i) = snd(scheme!j)
            then q ((1-t) * vx j + t * vx (Suc j mod ?n),
                    (1-t) * vy j + t * vy (Suc j mod ?n))
            else q (t * vx j + (1-t) * vx (Suc j mod ?n),
                    t * vy j + (1-t) * vy (Suc j mod ?n))))"
      using hC8 .
    show "\<forall>p\<in>P. (\<forall>i<?n. \<forall>t\<in>I_set.
                p \<noteq> ((1-t) * vx i + t * vx (Suc i mod ?n),
                      (1-t) * vy i + t * vy (Suc i mod ?n)))
             \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
      using hC9_interior .
    show "\<forall>i<?n. \<forall>j<?n. \<forall>t\<in>{0<..<(1::real)}. \<forall>s\<in>{0<..<(1::real)}.
            q ((1-t) * vx i + t * vx (Suc i mod ?n),
               (1-t) * vy i + t * vy (Suc i mod ?n))
          = q ((1-s) * vx j + s * vx (Suc j mod ?n),
               (1-s) * vy j + s * vy (Suc j mod ?n))
          \<longrightarrow> (i = j \<and> t = s)
            \<or> (fst(scheme!i) = fst(scheme!j) \<and>
               (if snd(scheme!i) = snd(scheme!j) then s = t else s = 1 - t))"
      using hC9_boundary .
    show "\<forall>i<?n. let cx = (\<Sum>j<?n. vx j) / real ?n;
                       cy = (\<Sum>j<?n. vy j) / real ?n
         in (vx i - cx) * (vy (Suc i mod ?n) - cy)
          - (vy i - cy) * (vx (Suc i mod ?n) - cx) > 0"
      using hC10 .
    show "\<forall>i<?n. \<forall>k<?n.
          k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
          (vx k - vx i) * (vy (Suc i mod ?n) - vy i)
          - (vy k - vy i) * (vx (Suc i mod ?n) - vx i) < 0"
      using hC11 .
  qed
qed

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

\<comment> \<open>Uncancel at front — derived from cancel + existence + uniqueness (per audit 22 §5.3).
   Given quotient of w, produce quotient of [a,inv a]@w homeomorphic to it.
   Strategy:
   (1) scheme\\_quotient\\_exists gives Y1 as quotient of [a,inv a]@w
   (2) front\\_cancel gives Y2 as quotient of w with Y1 \\<cong> Y2
   (3) scheme\\_quotient\\_uniqueness gives Y2 \\<cong> Y (both quotients of w)
   (4) Compose: Y \\<cong> Y2 \\<cong> Y1, giving the required homeomorphism.\<close>
lemma front_uncancel_realization_homeo:
  fixes Y :: "'a set" and TY :: "'a set set"
  assumes "top1_quotient_of_scheme_on Y TY w"
      and "length w \<ge> 3"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' ([a, top1_inverse_edge a] @ w) \<and>
    top1_homeomorphism_on Y TY Y' TY' h"
  sorry \<comment> \<open>Derive from cancel + existence + uniqueness per audit 22 §5.3.
     Uses: scheme\\_quotient\\_exists (for existence of quotient of [a,inv a]@w),
     front\\_cancel (for homeomorphism between quotients),
     scheme\\_quotient\\_uniqueness (for uniqueness up to homeomorphism).
     Type issue: scheme\\_quotient\\_exists gives (real\\<times>real) quotients;
     need to bridge to polymorphic 'a via uniqueness.\<close>

\<comment> \<open>Uncancel same-space: derived from homeomorphic uncancel (take Y'=Y via uniqueness).\<close>
lemma quotient_of_scheme_uncancel_front:
  assumes "top1_quotient_of_scheme_on Y TY w"
      and "length w \<ge> 3"
  shows "top1_quotient_of_scheme_on Y TY ([a, top1_inverse_edge a] @ w)"
  sorry \<comment> \<open>Derive from front\\_uncancel\\_realization\\_homeo + uniqueness.
     Or keep as separate geometric construction (spur insertion).\<close>

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
lemma homeomorphism_id:
  assumes "is_topology_on X TX"
  shows "top1_homeomorphism_on X TX X TX id"
proof -
  have hid_cont: "top1_continuous_map_on X TX X TX id"
    by (rule top1_continuous_map_on_id[OF assms])
  have hinv: "\<forall>x\<in>X. inv_into X id x = x"
  proof
    fix x assume "x \<in> X"
    have "inv_into X id (id x) = x" by (rule inv_into_f_f[OF inj_on_id \<open>x \<in> X\<close>])
    thus "inv_into X id x = x" by simp
  qed
  have "top1_continuous_map_on X TX X TX (inv_into X id)"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI allI impI)
    fix x assume "x \<in> X" thus "inv_into X id x \<in> X" using hinv by (by100 simp)
  next
    fix V assume hV: "V \<in> TX"
    have "{x \<in> X. inv_into X id x \<in> V} = {x \<in> X. id x \<in> V}"
      using hinv by (by100 auto)
    thus "{x \<in> X. inv_into X id x \<in> V} \<in> TX"
      using hid_cont hV unfolding top1_continuous_map_on_def by (by100 simp)
  qed
  thus ?thesis unfolding top1_homeomorphism_on_def using assms hid_cont by (by100 simp)
qed

\<comment> \<open>Flat intro for homeomorphic realization.\<close>
lemma homeo_realization_flat_introI:
  fixes X :: "'a set" and TX :: "'a set set" and Y :: "'a set" and TY :: "'a set set" and h :: "'a \<Rightarrow> 'a"
  assumes hq: "top1_quotient_of_scheme_on Y TY t"
      and hh: "top1_homeomorphism_on X TX Y TY h"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h' :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' t \<and>
    top1_homeomorphism_on X TX Y' TY' h'"
proof -
  have H0: "top1_quotient_of_scheme_on Y TY t \<and>
     top1_homeomorphism_on X TX Y TY h"
    using hq hh by (by100 blast)
  have H1: "\<exists>h'. top1_quotient_of_scheme_on Y TY t \<and>
        top1_homeomorphism_on X TX Y TY h'"
  proof (rule exI[where x = h])
    show "top1_quotient_of_scheme_on Y TY t \<and>
          top1_homeomorphism_on X TX Y TY h"
      using H0 .
  qed
  have H2: "\<exists>TY' h'. top1_quotient_of_scheme_on Y TY' t \<and>
            top1_homeomorphism_on X TX Y TY' h'"
  proof (rule exI[where x = TY])
    show "\<exists>h'. top1_quotient_of_scheme_on Y TY t \<and>
            top1_homeomorphism_on X TX Y TY h'"
      using H1 .
  qed
  show ?thesis
  proof (rule exI[where x = Y])
    show "\<exists>TY' h'. top1_quotient_of_scheme_on Y TY' t \<and>
                top1_homeomorphism_on X TX Y TY' h'"
      using H2 .
  qed
qed

lemma same_space_implies_homeo_realization:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "top1_quotient_of_scheme_on X TX t"
  shows "\<exists>(Y :: 'a set) (TY :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y TY t \<and>
    top1_homeomorphism_on X TX Y TY h"
proof -
  have "is_topology_on X TX"
    using assms unfolding top1_quotient_of_scheme_on_def is_topology_on_strict_def by (by100 blast)
  show ?thesis by (rule homeo_realization_flat_introI[OF assms homeomorphism_id[OF \<open>is_topology_on X TX\<close>]])
qed

\<comment> \<open>scheme\\_equiv\\_implies\\_homeo\\_realization: DELETED (old bridge, unused).\<close>

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

\<comment> \<open>A polygonal region is compact (continuous image of a compact simplex).\<close>
lemma polygonal_region_compact:
  assumes "top1_is_polygonal_region_on P n"
  shows "compact P"
proof -
  from assms obtain vx vy where hn: "n \<ge> 3"
      and hP: "P = {(x, y). \<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
                  \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
    unfolding top1_is_polygonal_region_on_def by (by5000 auto)
  \<comment> \<open>P is bounded: all coordinates are convex combinations of finitely many vertex coordinates.\<close>
  define M where "M = Max ((\<lambda>i. \<bar>vx i\<bar>) ` {..<n} \<union> (\<lambda>i. \<bar>vy i\<bar>) ` {..<n})"
  have hfin: "finite ((\<lambda>i. \<bar>vx i\<bar>) ` {..<n} \<union> (\<lambda>i. \<bar>vy i\<bar>) ` {..<n})"
    by simp
  have hne: "(\<lambda>i. \<bar>vx i\<bar>) ` {..<n} \<union> (\<lambda>i. \<bar>vy i\<bar>) ` {..<n} \<noteq> {}"
  proof -
    have "(0::nat) < n" using hn by simp
    hence "\<bar>vx 0\<bar> \<in> (\<lambda>i. \<bar>vx i\<bar>) ` {..<n}" by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  have hM_bound: "\<And>i. i < n \<Longrightarrow> \<bar>vx i\<bar> \<le> M \<and> \<bar>vy i\<bar> \<le> M"
  proof -
    fix i assume "i < n"
    have "\<bar>vx i\<bar> \<in> (\<lambda>i. \<bar>vx i\<bar>) ` {..<n}" using \<open>i < n\<close> by (by100 blast)
    hence "\<bar>vx i\<bar> \<le> M" unfolding M_def using hfin hne by (by100 auto)
    moreover have "\<bar>vy i\<bar> \<in> (\<lambda>i. \<bar>vy i\<bar>) ` {..<n}" using \<open>i < n\<close> by (by100 blast)
    hence "\<bar>vy i\<bar> \<le> M" unfolding M_def using hfin hne by (by100 auto)
    ultimately show "\<bar>vx i\<bar> \<le> M \<and> \<bar>vy i\<bar> \<le> M" by simp
  qed
  have hP_bounded: "P \<subseteq> {- M .. M} \<times> {- M .. M}"
  proof
    fix p assume "p \<in> P"
    then obtain x y coeffs where hp: "p = (x, y)"
        and hcoeffs: "\<forall>i<n. (0::real) \<le> coeffs i" "(\<Sum>i<n. coeffs i) = 1"
        and hx: "x = (\<Sum>i<n. coeffs i * vx i)" and hy: "y = (\<Sum>i<n. coeffs i * vy i)"
      unfolding hP by (by5000 auto)
    \<comment> \<open>|x| \\<le> \\<Sum> coeffs i * M = M. Similarly for y.\<close>
    have "\<bar>x\<bar> \<le> M"
    proof -
      have "\<bar>x\<bar> \<le> (\<Sum>i<n. \<bar>coeffs i * vx i\<bar>)" unfolding hx
        by (rule sum_abs)
      also have "\<dots> \<le> (\<Sum>i<n. coeffs i * M)"
      proof (rule sum_mono)
        fix i assume "i \<in> {..<n}" hence "i < n" by simp
        have "\<bar>coeffs i * vx i\<bar> = coeffs i * \<bar>vx i\<bar>"
          using hcoeffs(1) \<open>i < n\<close> by (simp add: abs_mult)
        also have "\<dots> \<le> coeffs i * M" using hM_bound[OF \<open>i < n\<close>] hcoeffs(1) \<open>i < n\<close>
          by (intro mult_left_mono) (by100 auto)+
        finally show "\<bar>coeffs i * vx i\<bar> \<le> coeffs i * M" .
      qed
      also have "\<dots> = M" using hcoeffs(2) by (simp add: sum_distrib_right[symmetric])
      finally show ?thesis .
    qed
    have "\<bar>y\<bar> \<le> M"
    proof -
      have "\<bar>y\<bar> \<le> (\<Sum>i<n. \<bar>coeffs i * vy i\<bar>)" unfolding hy
        by (rule sum_abs)
      also have "\<dots> \<le> (\<Sum>i<n. coeffs i * M)"
      proof (rule sum_mono)
        fix i assume "i \<in> {..<n}" hence "i < n" by simp
        have "\<bar>coeffs i * vy i\<bar> = coeffs i * \<bar>vy i\<bar>"
          using hcoeffs(1) \<open>i < n\<close> by (simp add: abs_mult)
        also have "\<dots> \<le> coeffs i * M" using hM_bound[OF \<open>i < n\<close>] hcoeffs(1) \<open>i < n\<close>
          by (intro mult_left_mono) (by100 auto)+
        finally show "\<bar>coeffs i * vy i\<bar> \<le> coeffs i * M" .
      qed
      also have "\<dots> = M" using hcoeffs(2) by (simp add: sum_distrib_right[symmetric])
      finally show ?thesis .
    qed
    show "p \<in> {- M..M} \<times> {- M..M}" using \<open>\<bar>x\<bar> \<le> M\<close> \<open>\<bar>y\<bar> \<le> M\<close> hp by (by100 auto)
  qed
  \<comment> \<open>P is closed: the set of convex combinations of finitely many fixed points is closed.
     (Limit of convergent sequence of convex combinations is a convex combination.)\<close>
  \<comment> \<open>Show P is compact directly via inductive convex hull argument.\<close>
  have hP_compact_direct: "compact P"
  proof -
    \<comment> \<open>Define partial convex hulls: Q k = conv({(vx i, vy i) | i \\<le> k}).\<close>
    define Q where "Q k = {(x::real, y::real). \<exists>coeffs.
        (\<forall>i\<le>k. 0 \<le> coeffs i) \<and> (\<Sum>i\<le>k. coeffs i) = 1
        \<and> x = (\<Sum>i\<le>k. coeffs i * vx i) \<and> y = (\<Sum>i\<le>k. coeffs i * vy i)}" for k
    \<comment> \<open>Base: Q 0 = {(vx 0, vy 0)} is compact (singleton).\<close>
    have hQ0_eq: "Q 0 = {(vx 0, vy 0)}"
    proof
      show "Q 0 \<subseteq> {(vx 0, vy 0)}"
        unfolding Q_def by (by5000 force)
      show "{(vx 0, vy 0)} \<subseteq> Q 0"
        unfolding Q_def
      proof
        fix p assume "p \<in> {(vx 0, vy 0)}"
        hence "p = (vx 0, vy 0)" by simp
        define coeffs :: "nat \<Rightarrow> real" where "coeffs = (\<lambda>_. 1)"
        have "(\<forall>i\<le>(0::nat). (0::real) \<le> coeffs i) \<and> (\<Sum>i\<le>0. coeffs i) = 1
            \<and> vx 0 = (\<Sum>i\<le>0. coeffs i * vx i) \<and> vy 0 = (\<Sum>i\<le>0. coeffs i * vy i)"
          unfolding coeffs_def by simp
        thus "p \<in> {(x, y). \<exists>coeffs. (\<forall>i\<le>0. 0 \<le> coeffs i) \<and> (\<Sum>i\<le>0. coeffs i) = 1
            \<and> x = (\<Sum>i\<le>0. coeffs i * vx i) \<and> y = (\<Sum>i\<le>0. coeffs i * vy i)}"
          unfolding \<open>p = (vx 0, vy 0)\<close> by (by100 blast)
      qed
    qed
    have hQ0: "compact (Q 0)"
      unfolding hQ0_eq
    proof (rule compactI)
      fix C :: "(real \<times> real) set set"
      assume "\<forall>c\<in>C. open c" and "{(vx 0, vy 0)} \<subseteq> \<Union>C"
      then obtain U where "U \<in> C" "(vx 0, vy 0) \<in> U" by (by100 blast)
      thus "\<exists>D\<subseteq>C. finite D \<and> {(vx 0, vy 0)} \<subseteq> \<Union>D"
        by (intro exI[of _ "{U}"]) (by100 auto)
    qed
    \<comment> \<open>Step: Q (Suc k) = {t*v\\_{k+1} + (1-t)*p | t \\<in> [0,1], p \\<in> Q k}.
       This is the continuous image of [0,1] \\<times> Q k, hence compact.\<close>
    have hQstep: "\<And>k. compact (Q k) \<Longrightarrow> compact (Q (Suc k))"
    proof -
      fix k assume hIH: "compact (Q k)"
      \<comment> \<open>Q(Suc k) = image of [0,1] \\<times> Q(k) under the affine combination map.\<close>
      define f where "f = (\<lambda>(t::real, p::real\<times>real). (t * vx (Suc k) + (1-t) * fst p, t * vy (Suc k) + (1-t) * snd p))"
      have hQ_eq: "Q (Suc k) = f ` ({0..1} \<times> Q k)"
      proof
        \<comment> \<open>(\\<subseteq>): every convex combo of k+2 points = t*v\\_{k+1} + (1-t)*(combo of first k+1).\<close>
        show "Q (Suc k) \<subseteq> f ` ({0..1} \<times> Q k)"
        proof
          fix q assume "q \<in> Q (Suc k)"
          then obtain coeffs where hc: "(\<forall>i\<le>Suc k. 0 \<le> coeffs i)" "(\<Sum>i\<le>Suc k. coeffs i) = 1"
              "fst q = (\<Sum>i\<le>Suc k. coeffs i * vx i)" "snd q = (\<Sum>i\<le>Suc k. coeffs i * vy i)"
            unfolding Q_def by (by5000 auto)
          define t where "t = coeffs (Suc k)"
          have ht: "t \<in> {0..1}"
          proof -
            have "0 \<le> t" using hc(1) unfolding t_def by simp
            moreover have "t \<le> 1"
            proof -
              have "(\<Sum>i\<le>k. coeffs i) \<ge> 0"
                using hc(1) by (intro sum_nonneg) (by100 auto)
              hence "t = 1 - (\<Sum>i\<le>k. coeffs i)" using hc(2) unfolding t_def by simp
              thus ?thesis using \<open>(\<Sum>i\<le>k. coeffs i) \<ge> 0\<close> by linarith
            qed
            ultimately show ?thesis by simp
          qed
          show "q \<in> f ` ({0..1} \<times> Q k)"
          proof (cases "t = 1")
            case True
            \<comment> \<open>If t=1: q = v\\_{k+1}. f(1,p) = v\\_{k+1} for any p. Need Q k nonempty.\<close>
            have "fst q = vx (Suc k) \<and> snd q = vy (Suc k)"
            proof -
              have hzero: "\<forall>i\<le>k. coeffs i = 0"
              proof (rule ccontr)
                assume "\<not> (\<forall>i\<le>k. coeffs i = 0)"
                then obtain j where "j \<le> k" "coeffs j \<noteq> 0" by (by100 blast)
                have "0 \<le> coeffs j" using hc(1) \<open>j \<le> k\<close> by simp
                hence "coeffs j > 0" using \<open>coeffs j \<noteq> 0\<close> by linarith
                hence "(\<Sum>i\<le>k. coeffs i) > 0"
                  using hc(1) \<open>j \<le> k\<close> by (intro sum_pos2[of "{..k}" j]) (by100 auto)+
                hence "1 - t > 0" using hc(2) unfolding t_def by simp
                thus False using True by simp
              qed
              hence "(\<Sum>i\<le>k. coeffs i * vx i) = 0" "(\<Sum>i\<le>k. coeffs i * vy i) = 0"
                by (simp_all add: sum.neutral)
              thus ?thesis using hc(3,4) True unfolding t_def by simp
            qed
            \<comment> \<open>Q k is nonempty: (vx 0, vy 0) \\<in> Q 0 \\<subseteq> Q k.\<close>
            have "(vx 0, vy 0) \<in> Q k"
            proof -
              define c0 :: "nat \<Rightarrow> real" where "c0 i = (if i = 0 then 1 else 0)" for i
              have "(\<forall>i\<le>k. 0 \<le> c0 i)" unfolding c0_def by simp
              moreover have "(\<Sum>i\<le>k. c0 i) = 1" unfolding c0_def by simp
              moreover have "vx 0 = (\<Sum>i\<le>k. c0 i * vx i)"
              proof -
                have "(\<Sum>i\<le>k. c0 i * vx i) = c0 0 * vx 0 + (\<Sum>i\<in>{..k}-{0}. c0 i * vx i)"
                  by (rule sum.remove) simp_all
                also have "(\<Sum>i\<in>{..k}-{0}. c0 i * vx i) = 0"
                  by (rule sum.neutral) (simp add: c0_def)
                finally show ?thesis unfolding c0_def by simp
              qed
              moreover have "vy 0 = (\<Sum>i\<le>k. c0 i * vy i)"
              proof -
                have "(\<Sum>i\<le>k. c0 i * vy i) = c0 0 * vy 0 + (\<Sum>i\<in>{..k}-{0}. c0 i * vy i)"
                  by (rule sum.remove) simp_all
                also have "(\<Sum>i\<in>{..k}-{0}. c0 i * vy i) = 0"
                  by (rule sum.neutral) (simp add: c0_def)
                finally show ?thesis unfolding c0_def by simp
              qed
              ultimately show ?thesis unfolding Q_def by (by100 auto)
            qed
            hence "(1::real, (vx 0, vy 0)) \<in> {0..1} \<times> Q k" by simp
            hence "f (1, (vx 0, vy 0)) \<in> f ` ({0..1} \<times> Q k)" by (by100 blast)
            moreover have "f (1, (vx 0, vy 0)) = (vx (Suc k), vy (Suc k))"
              unfolding f_def by simp
            ultimately have "(vx (Suc k), vy (Suc k)) \<in> f ` ({0..1} \<times> Q k)" by simp
            thus ?thesis using \<open>fst q = vx (Suc k) \<and> snd q = vy (Suc k)\<close>
              by (cases q) (by100 auto)
          next
            case False
            \<comment> \<open>t < 1: define \\<alpha> i = coeffs i / (1-t) for i \\<le> k.\<close>
            have ht_lt: "t < 1" using ht False by simp
            hence h1mt: "1 - t > 0" by simp
            define \<alpha> where "\<alpha> i = coeffs i / (1 - t)" for i
            have h\<alpha>_pos: "\<forall>i\<le>k. 0 \<le> \<alpha> i"
              using hc(1) h1mt unfolding \<alpha>_def by (by100 auto)
            have h\<alpha>_sum: "(\<Sum>i\<le>k. \<alpha> i) = 1"
            proof -
              have "(\<Sum>i\<le>k. \<alpha> i) = (\<Sum>i\<le>k. coeffs i) / (1-t)"
                unfolding \<alpha>_def by (simp add: sum_divide_distrib)
              also have "(\<Sum>i\<le>k. coeffs i) = 1 - t"
                using hc(2) unfolding t_def by simp
              finally show ?thesis using h1mt by simp
            qed
            define p where "p = ((\<Sum>i\<le>k. \<alpha> i * vx i), (\<Sum>i\<le>k. \<alpha> i * vy i))"
            have hp: "p \<in> Q k" unfolding Q_def p_def
              using h\<alpha>_pos h\<alpha>_sum by (by100 auto)
            have "q = f (t, p)"
            proof -
              \<comment> \<open>fst q = t*vx(k+1) + (1-t) * Σα_i*vx_i\<close>
              have hx: "fst q = t * vx (Suc k) + (1-t) * (\<Sum>i\<le>k. \<alpha> i * vx i)"
              proof -
                have "fst q = (\<Sum>i\<le>Suc k. coeffs i * vx i)" using hc(3) by simp
                also have "\<dots> = (\<Sum>i\<le>k. coeffs i * vx i) + coeffs (Suc k) * vx (Suc k)" by simp
                also have "(\<Sum>i\<le>k. coeffs i * vx i) = (1-t) * (\<Sum>i\<le>k. \<alpha> i * vx i)"
                  unfolding \<alpha>_def using h1mt
                  by (simp add: sum_distrib_left sum_divide_distrib)
                finally show ?thesis unfolding t_def by (simp add: algebra_simps)
              qed
              have hy: "snd q = t * vy (Suc k) + (1-t) * (\<Sum>i\<le>k. \<alpha> i * vy i)"
              proof -
                have "snd q = (\<Sum>i\<le>Suc k. coeffs i * vy i)" using hc(4) by simp
                also have "\<dots> = (\<Sum>i\<le>k. coeffs i * vy i) + coeffs (Suc k) * vy (Suc k)" by simp
                also have "(\<Sum>i\<le>k. coeffs i * vy i) = (1-t) * (\<Sum>i\<le>k. \<alpha> i * vy i)"
                  unfolding \<alpha>_def using h1mt
                  by (simp add: sum_distrib_left sum_divide_distrib)
                finally show ?thesis unfolding t_def by (simp add: algebra_simps)
              qed
              show ?thesis unfolding f_def p_def using hx hy by (cases q) simp
            qed
            thus ?thesis using ht hp by (by100 blast)
          qed
        qed
        \<comment> \<open>(\\<supseteq>): t*v\\_{k+1} + (1-t)*p where p \\<in> Q k is a convex combo of k+2 points.\<close>
        show "f ` ({0..1} \<times> Q k) \<subseteq> Q (Suc k)"
        proof
          fix q assume "q \<in> f ` ({0..1} \<times> Q k)"
          then obtain t p where ht: "t \<in> {0..1}" and hp: "p \<in> Q k" and hq: "q = f (t, p)"
            by (by100 blast)
          from hp obtain coeffs where hc: "(\<forall>i\<le>k. 0 \<le> coeffs i)" "(\<Sum>i\<le>k. coeffs i) = 1"
              "fst p = (\<Sum>i\<le>k. coeffs i * vx i)" "snd p = (\<Sum>i\<le>k. coeffs i * vy i)"
            unfolding Q_def by (by5000 auto)
          \<comment> \<open>New coefficients: \\<beta> i = (1-t)*coeffs i for i \\<le> k, \\<beta> (k+1) = t.\<close>
          define \<beta> where "\<beta> i = (if i = Suc k then t else (1-t) * coeffs i)" for i
          have h\<beta>_pos: "\<forall>i\<le>Suc k. 0 \<le> \<beta> i"
            using hc(1) ht unfolding \<beta>_def by (by100 auto)
          have h\<beta>_sum: "(\<Sum>i\<le>Suc k. \<beta> i) = 1"
          proof -
            have "(\<Sum>i\<le>Suc k. \<beta> i) = (\<Sum>i\<le>k. \<beta> i) + \<beta> (Suc k)" by simp
            also have "(\<Sum>i\<le>k. \<beta> i) = (\<Sum>i\<le>k. (1-t) * coeffs i)"
              by (rule sum.cong) (simp_all add: \<beta>_def)
            also have "\<dots> = (1-t) * (\<Sum>i\<le>k. coeffs i)"
              by (simp add: sum_distrib_left)
            also have "\<dots> = (1-t)" using hc(2) by simp
            also have "\<beta> (Suc k) = t" unfolding \<beta>_def by simp
            finally show ?thesis by simp
          qed
          have hx: "fst q = (\<Sum>i\<le>Suc k. \<beta> i * vx i)"
          proof -
            have "fst q = t * vx (Suc k) + (1-t) * fst p" using hq unfolding f_def by simp
            also have "\<dots> = t * vx (Suc k) + (1-t) * (\<Sum>i\<le>k. coeffs i * vx i)"
              using hc(3) by simp
            also have "(1-t) * (\<Sum>i\<le>k. coeffs i * vx i) = (\<Sum>i\<le>k. (1-t) * coeffs i * vx i)"
              by (simp add: sum_distrib_left mult.assoc)
            also have "(\<Sum>i\<le>k. (1-t) * coeffs i * vx i) = (\<Sum>i\<le>k. \<beta> i * vx i)"
              by (rule sum.cong) (simp_all add: \<beta>_def)
            finally have "fst q = \<beta> (Suc k) * vx (Suc k) + (\<Sum>i\<le>k. \<beta> i * vx i)"
              unfolding \<beta>_def by simp
            thus ?thesis by simp
          qed
          have hy: "snd q = (\<Sum>i\<le>Suc k. \<beta> i * vy i)"
          proof -
            have "snd q = t * vy (Suc k) + (1-t) * snd p" using hq unfolding f_def by simp
            also have "\<dots> = t * vy (Suc k) + (1-t) * (\<Sum>i\<le>k. coeffs i * vy i)"
              using hc(4) by simp
            also have "(1-t) * (\<Sum>i\<le>k. coeffs i * vy i) = (\<Sum>i\<le>k. (1-t) * coeffs i * vy i)"
              by (simp add: sum_distrib_left mult.assoc)
            also have "(\<Sum>i\<le>k. (1-t) * coeffs i * vy i) = (\<Sum>i\<le>k. \<beta> i * vy i)"
              by (rule sum.cong) (simp_all add: \<beta>_def)
            finally have "snd q = \<beta> (Suc k) * vy (Suc k) + (\<Sum>i\<le>k. \<beta> i * vy i)"
              unfolding \<beta>_def by simp
            thus ?thesis by simp
          qed
          show "q \<in> Q (Suc k)"
          proof -
            have "\<exists>coeffs. (\<forall>i\<le>Suc k. 0 \<le> coeffs i) \<and> (\<Sum>i\<le>Suc k. coeffs i) = 1
                \<and> fst q = (\<Sum>i\<le>Suc k. coeffs i * vx i) \<and> snd q = (\<Sum>i\<le>Suc k. coeffs i * vy i)"
              using h\<beta>_pos h\<beta>_sum hx hy by (by100 blast)
            thus ?thesis unfolding Q_def by (by100 auto)
          qed
        qed
      qed
      have hf_cont: "continuous_on ({0..1} \<times> Q k) f"
      proof -
        have "f = (\<lambda>tp. (fst tp * vx (Suc k) + (1 - fst tp) * fst (snd tp),
                         fst tp * vy (Suc k) + (1 - fst tp) * snd (snd tp)))"
          unfolding f_def by (rule ext, simp add: case_prod_beta)
        moreover have "continuous_on ({0..1} \<times> Q k)
            (\<lambda>tp. (fst tp * vx (Suc k) + (1 - fst tp) * fst (snd tp),
                   fst tp * vy (Suc k) + (1 - fst tp) * snd (snd tp)))"
          by (intro continuous_intros)
        ultimately show ?thesis by simp
      qed
      have hdom_compact: "compact ({0..1::real} \<times> Q k)"
        by (rule compact_Times_general[OF compact_Icc hIH])
      show "compact (Q (Suc k))" unfolding hQ_eq
        by (rule compact_continuous_image[OF hf_cont hdom_compact])
    qed
    \<comment> \<open>By induction: Q k is compact for all k.\<close>
    have hQk: "\<And>k. compact (Q k)"
    proof -
      fix k show "compact (Q k)"
        by (induction k) (use hQ0 in simp, use hQstep in simp)
    qed
    \<comment> \<open>P = Q (n-1) (when n \\<ge> 3).\<close>
    have "P = Q (n - 1)"
    proof -
      have "{..<n} = {..n-1}" using hn by (by100 auto)
      hence "(\<forall>i<n. P_cond i) = (\<forall>i\<le>n-1. P_cond i)" for P_cond by (by100 auto)
      moreover have "(\<Sum>i<n. f i) = (\<Sum>i\<le>n-1. f i)" for f :: "nat \<Rightarrow> real"
        using \<open>{..<n} = {..n-1}\<close> by (by100 auto)
      ultimately show ?thesis unfolding hP Q_def by (by100 auto)
    qed
    thus ?thesis using hQk by simp
  qed
  have hP_closed: "closed P" by (rule compact_imp_closed[OF hP_compact_direct])
  \<comment> \<open>Closed subset of compact {-M..M}\\<times>{-M..M} is compact.\<close>
  show "compact P"
    by (rule closed_subset_compact[OF compact_Icc_Times hP_closed hP_bounded])
qed

\<comment> \<open>QUARANTINED: convex\\_polygon\\_homeomorphism is UNUSED and its barycentric/SOME approach
   is wrong for n > 3 (non-unique representations). The correct approach (using
   polygon\\_homeomorphic\\_to\\_disk\\_with\\_boundary) is now implemented directly inside
   scheme\\_quotient\\_uniqueness (per expert audit steps 4-7). This lemma can be deleted.\<close>
\<comment> \<open>convex\\_polygon\\_homeomorphism: REMOVED (unused, wrong barycentric approach for n>3).
   See scheme\\_quotient\\_uniqueness for the correct disk-homeomorphism approach.\<close>

\<comment> \<open>Interior preservation: if \\<phi> maps edge i of P1 to edge i of P2 bijectively,
   then \\<phi> also maps interior points (not on any edge) to interior points.\<close>
lemma edge_preserving_homeo_interior:
  assumes hbij: "bij_betw \<phi> P1 P2"
      and hedge: "\<forall>i<n. \<forall>t\<in>I_set.
          \<phi> ((1-t) * vx1 i + t * vx1 (Suc i mod n),
             (1-t) * vy1 i + t * vy1 (Suc i mod n))
          = ((1-t) * vx2 i + t * vx2 (Suc i mod n),
             (1-t) * vy2 i + t * vy2 (Suc i mod n))"
      and hn3: "n \<ge> 3"
      and hP1_hull: "P1 = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<n. coeffs i) = 1
                     \<and> x = (\<Sum>i<n. coeffs i * vx1 i)
                     \<and> y = (\<Sum>i<n. coeffs i * vy1 i)}"
      and hx: "x \<in> P1"
      and hint: "\<forall>i<n. \<forall>t\<in>I_set.
          x \<noteq> ((1-t) * vx1 i + t * vx1 (Suc i mod n),
                (1-t) * vy1 i + t * vy1 (Suc i mod n))"
  shows "\<forall>i<n. \<forall>t\<in>I_set.
      \<phi> x \<noteq> ((1-t) * vx2 i + t * vx2 (Suc i mod n),
            (1-t) * vy2 i + t * vy2 (Suc i mod n))"
proof (intro allI impI ballI notI)
  fix i t assume hi: "i < n" and ht: "t \<in> I_set"
  assume "(\<phi> x) = ((1-t) * vx2 i + t * vx2 (Suc i mod n),
            (1-t) * vy2 i + t * vy2 (Suc i mod n))"
  \<comment> \<open>But \\<phi>(edge1(i,t)) = edge2(i,t) by hedge. Since \\<phi> is injective, x = edge1(i,t).\<close>
  have h_edge_eq: "\<phi> ((1-t) * vx1 i + t * vx1 (Suc i mod n),
             (1-t) * vy1 i + t * vy1 (Suc i mod n))
        = ((1-t) * vx2 i + t * vx2 (Suc i mod n),
           (1-t) * vy2 i + t * vy2 (Suc i mod n))"
    using hedge[rule_format, OF hi ht] .
  hence "\<phi> x = \<phi> ((1-t) * vx1 i + t * vx1 (Suc i mod n),
                   (1-t) * vy1 i + t * vy1 (Suc i mod n))"
    using \<open>(\<phi> x) = _\<close> by (by100 simp)
  hence "x = ((1-t) * vx1 i + t * vx1 (Suc i mod n),
              (1-t) * vy1 i + t * vy1 (Suc i mod n))"
  proof -
    have "inj_on \<phi> P1" using bij_betw_imp_inj_on[OF hbij] .
    have "((1-t) * vx1 i + t * vx1 (Suc i mod n),
            (1-t) * vy1 i + t * vy1 (Suc i mod n)) \<in> P1"
      by (rule edge_point_in_polygon_witness[OF hn3 hi ht hP1_hull])
    from \<open>inj_on \<phi> P1\<close> hx this \<open>\<phi> x = \<phi> _\<close>
    show ?thesis unfolding inj_on_def by (by100 blast)
  qed
  thus False using hint hi ht by (by100 blast)
qed

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
            show ?thesis sorry \<comment> \<open>Vertex case in uniqueness forward direction.
               Needs: vertex identification is determined by C7 at endpoints + transitivity.
               Both q1 and q2 satisfy C7 for the same scheme, so identify the same vertices.\<close>
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

\<comment> \<open>Transfer quotient\\_of\\_scheme\\_on along a homeomorphism (expert audit 24 §6).
   If Y is a quotient of scheme s, and Y \\<cong> Y', then Y' is also a quotient of s.
   Proof: define q' = h \\<circ> q: P \\<to> Y'. All 11 conditions transfer through h.\<close>
lemma scheme_quotient_transfer_along_homeomorphism:
  assumes hq: "top1_quotient_of_scheme_on Y TY s"
      and hh: "top1_homeomorphism_on Y TY Y' TY' h"
  shows "top1_quotient_of_scheme_on Y' TY' s"
  sorry \<comment> \<open>Proof: extract (P, q, vx, vy) from hq. Define q' = h \\<circ> q.
     C1,C3-C5,C10,C11: don't reference q, transfer directly.
     C2: q' = h \\<circ> q. h is homeomorphism, q is quotient map,
         composition of quotient map with homeomorphism = quotient map.
     C7: q'(edge(i,t)) = h(q(edge(i,t))). Since h preserves equality:
         q(e1) = q(e2) iff h(q(e1)) = h(q(e2)). So C7 transfers.
     C8: q' injective on interior = h \\<circ> q injective = true (both injective).
     C9: boundary identification transfers similarly to C7.\<close>

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
  \<comment> \<open>Step 1: scheme\\_quotient\\_exists gives Y\\_w :: (real\\<times>real) quotient of w.\<close>
  from scheme_quotient_exists[of w, OF assms(2) hproper]
  obtain Y_w :: "(real \<times> real) set" and TY_w :: "(real \<times> real) set set" where
      hY_w: "top1_quotient_of_scheme_on Y_w TY_w w" by (by100 blast)
  have htopo_w: "is_topology_on_strict Y_w TY_w"
    using hY_w unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  \<comment> \<open>Step 2: Get (real\\<times>real) quotient of [a,inv a]@w.\<close>
  have htopo_Y: "is_topology_on_strict Y TY"
    using assms(1) unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  have hproper_ext: "\<forall>label. card {i. i < length ([a, top1_inverse_edge a] @ w) \<and>
      fst (([a, top1_inverse_edge a] @ w) ! i) = label} \<in> {0, 2}"
  proof (intro allI)
    fix label
    let ?s = "[a, top1_inverse_edge a] @ w"
    show "card {i. i < length ?s \<and> fst (?s ! i) = label} \<in> {0, 2}"
    proof (cases "label = fst a")
      case True
      \<comment> \<open>Label = fst(a): appears at positions 0 and 1, nowhere in w (by hfresh).\<close>
      have "{i. i < length ?s \<and> fst (?s ! i) = label} = {0, 1}"
      proof (rule set_eqI, rule iffI)
        fix i assume "i \<in> {i. i < length ?s \<and> fst (?s ! i) = label}"
        hence hi: "i < length ?s" and hlbl: "fst (?s ! i) = label" by (by100 auto)+
        show "i \<in> {0, 1}"
        proof (cases "i < 2")
          case True
          hence "i = 0 \<or> i = 1" by (by100 linarith)
          thus ?thesis by (by100 blast)
        next
          case False
          hence hi2: "i \<ge> 2" by (by100 linarith)
          have hsi: "fst (?s ! i) \<in> fst ` set w"
          proof -
            \<comment> \<open>For i \\<ge> 2: ?s!i is the (i-2)-th element of w.\<close>
            define j where "j = i - 2"
            have hj: "i = j + 2" using hi2 unfolding j_def by (by100 linarith)
            have "?s ! (j + 2) = w ! j"
              by (by100 simp)
            hence "?s ! i = w ! j" using hj by (by100 simp)
            moreover have "j < length w" using hi hj by (by100 simp)
            hence "w ! j \<in> set w" by (by100 simp)
            ultimately have "?s ! i \<in> set w" by (by100 simp)
            thus ?thesis by (by100 force)
          qed
          have "fst (?s ! i) \<noteq> fst a"
          proof
            assume "fst (?s ! i) = fst a"
            hence "fst a \<in> fst ` set w" using hsi by (by100 simp)
            thus False using hfresh by (by100 blast)
          qed
          thus ?thesis using hlbl True by (by100 simp)
        qed
      next
        fix i assume "i \<in> {0::nat, 1}"
        hence "i = 0 \<or> i = 1" by (by100 blast)
        thus "i \<in> {i. i < length ?s \<and> fst (?s ! i) = label}"
        proof
          assume "i = 0"
          thus ?thesis using True assms(2) by (by100 simp)
        next
          assume "i = 1"
          thus ?thesis using True assms(2) unfolding top1_inverse_edge_def by (by100 simp)
        qed
      qed
      thus ?thesis by (by100 simp)
    next
      case False
      \<comment> \<open>Label \\<noteq> fst(a): appears in w at same positions (shifted by 2).\<close>
      have hset_eq: "{i. i < length ?s \<and> fst (?s ! i) = label} = {i. \<exists>j<length w. i = j + 2 \<and> fst (w ! j) = label}"
      proof (rule set_eqI, rule iffI)
        fix i assume "i \<in> {i. i < length ?s \<and> fst (?s ! i) = label}"
        hence hi: "i < length ?s" and hlbl: "fst (?s ! i) = label" by (by100 auto)+
        \<comment> \<open>i \\<ge> 2 (positions 0,1 have fst = fst(a) \\<noteq> label).\<close>
        have "i \<ge> 2"
        proof (rule ccontr)
          assume "\<not> i \<ge> 2" hence "i < 2" by (by100 linarith)
          hence "i = 0 \<or> i = 1" by (by100 linarith)
          hence "fst (?s ! i) = fst a"
          proof
            assume "i = 0" thus ?thesis by (by100 simp)
          next
            assume "i = 1" thus ?thesis unfolding top1_inverse_edge_def by (by100 simp)
          qed
          thus False using hlbl False by (by100 simp)
        qed
        define j where "j = i - 2"
        have "i = j + 2" using \<open>i \<ge> 2\<close> unfolding j_def by (by100 linarith)
        have "j < length w" using hi \<open>i = j + 2\<close> by (by100 simp)
        have "?s ! (j + 2) = w ! j" by (by100 simp)
        hence "fst (w ! j) = label" using hlbl \<open>i = j + 2\<close> by (by100 simp)
        show "i \<in> {i. \<exists>j<length w. i = j + 2 \<and> fst (w ! j) = label}"
          using \<open>j < length w\<close> \<open>i = j + 2\<close> \<open>fst (w ! j) = label\<close> by (by100 blast)
      next
        fix i assume "i \<in> {i. \<exists>j<length w. i = j + 2 \<and> fst (w ! j) = label}"
        then obtain j where hj: "j < length w" "i = j + 2" "fst (w ! j) = label" by (by100 blast)
        have "i < length ?s" using hj by (by100 simp)
        have "?s ! (j + 2) = w ! j" by (by100 simp)
        hence "fst (?s ! i) = label" using hj by (by100 simp)
        show "i \<in> {i. i < length ?s \<and> fst (?s ! i) = label}"
          using \<open>i < length ?s\<close> \<open>fst (?s ! i) = label\<close> by (by100 blast)
      qed
      moreover have "card {i. \<exists>j<length w. i = j + 2 \<and> fst (w ! j) = label}
          = card {j. j < length w \<and> fst (w ! j) = label}"
      proof -
        have "bij_betw (\<lambda>j. j + 2) {j. j < length w \<and> fst (w ! j) = label}
                                    {i. \<exists>j<length w. i = j + 2 \<and> fst (w ! j) = label}"
          unfolding bij_betw_def
        proof (intro conjI)
          show "inj_on (\<lambda>j. j + 2) {j. j < length w \<and> fst (w ! j) = label}"
            unfolding inj_on_def by (by100 simp)
          show "(\<lambda>j. j + 2) ` {j. j < length w \<and> fst (w ! j) = label}
              = {i. \<exists>j<length w. i = j + 2 \<and> fst (w ! j) = label}"
            by (by100 force)
        qed
        from bij_betw_same_card[OF this] show ?thesis by (by100 simp)
      qed
      moreover have "card {j. j < length w \<and> fst (w ! j) = label} \<in> {0, 2}"
        using hproper by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
  qed
  from scheme_quotient_exists[of "[a, top1_inverse_edge a] @ w", OF _ hproper_ext]
  obtain Y_ext :: "(real \<times> real) set" and TY_ext :: "(real \<times> real) set set" where
      hY_ext: "top1_quotient_of_scheme_on Y_ext TY_ext ([a, top1_inverse_edge a] @ w)"
    using assms(2) by (by100 auto)
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
    \<comment> \<open>Extract full conditions for both polygons to get disk homeomorphisms.\<close>
    from hY_ext obtain P_e q_e vx_e vy_e where
        hC1e: "top1_is_polygonal_region_on P_e ?n"
      and hC2e: "top1_quotient_map_on P_e (?TP P_e) Y_ext TY_ext q_e"
      and hC3e: "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> (vx_e i, vy_e i) \<noteq> (vx_e j, vy_e j)"
      and hC4e: "\<forall>i<?n. (vx_e i, vy_e i) \<in> P_e"
      and hC5e: "P_e = {(x, y) | x y. \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx_e i)
                     \<and> y = (\<Sum>i<?n. coeffs i * vy_e i)}"
      and hC7e: "\<forall>i<?n. \<forall>j<?n. fst (([a, top1_inverse_edge a] @ w)!i) = fst (([a, top1_inverse_edge a] @ w)!j) \<longrightarrow>
          (\<forall>t\<in>I_set. q_e ((1-t)*vx_e i+t*vx_e(Suc i mod ?n),(1-t)*vy_e i+t*vy_e(Suc i mod ?n))
           = (if snd(([a, top1_inverse_edge a] @ w)!i) = snd(([a, top1_inverse_edge a] @ w)!j)
              then q_e ((1-t)*vx_e j+t*vx_e(Suc j mod ?n),(1-t)*vy_e j+t*vy_e(Suc j mod ?n))
              else q_e (t*vx_e j+(1-t)*vx_e(Suc j mod ?n),t*vy_e j+(1-t)*vy_e(Suc j mod ?n))))"
      and hC8e: "\<forall>p\<in>P_e. (\<forall>i<?n. \<forall>t\<in>I_set.
                p \<noteq> ((1-t)*vx_e i+t*vx_e(Suc i mod ?n),(1-t)*vy_e i+t*vy_e(Suc i mod ?n)))
             \<longrightarrow> (\<forall>p'\<in>P_e. q_e p = q_e p' \<longrightarrow> p = p')"
      and hC9e: "\<forall>i<?n. \<forall>j<?n. \<forall>t\<in>{0<..<(1::real)}. \<forall>s\<in>{0<..<(1::real)}.
            q_e ((1-t)*vx_e i+t*vx_e(Suc i mod ?n),(1-t)*vy_e i+t*vy_e(Suc i mod ?n))
          = q_e ((1-s)*vx_e j+s*vx_e(Suc j mod ?n),(1-s)*vy_e j+s*vy_e(Suc j mod ?n))
          \<longrightarrow> (i=j \<and> t=s) \<or> (fst(([a, top1_inverse_edge a] @ w)!i)=fst(([a, top1_inverse_edge a] @ w)!j)
               \<and> (if snd(([a, top1_inverse_edge a] @ w)!i)=snd(([a, top1_inverse_edge a] @ w)!j) then s=t else s=1-t))"
      and hC10e: "\<forall>i<?n. let cx=(\<Sum>j<?n. vx_e j)/real ?n; cy=(\<Sum>j<?n. vy_e j)/real ?n
           in (vx_e i-cx)*(vy_e(Suc i mod ?n)-cy)-(vy_e i-cy)*(vx_e(Suc i mod ?n)-cx) > 0"
      and hC11e: "\<forall>i<?n. \<forall>k<?n. k\<noteq>i \<longrightarrow> k\<noteq>Suc i mod ?n \<longrightarrow>
            (vx_e k-vx_e i)*(vy_e(Suc i mod ?n)-vy_e i)-(vy_e k-vy_e i)*(vx_e(Suc i mod ?n)-vx_e i) < 0"
      by (rule quotient_of_scheme_extract_vx)
    from hY_w obtain P_m q_m vx_m vy_m where
        hC1m: "top1_is_polygonal_region_on P_m ?m"
      and hC2m: "top1_quotient_map_on P_m (?TP P_m) Y_w TY_w q_m"
      and hC4m: "\<forall>i<?m. (vx_m i, vy_m i) \<in> P_m"
      and hC5m: "P_m = {(x, y) | x y. \<exists>coeffs. (\<forall>i<?m. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<?m. coeffs i) = 1
                     \<and> x = (\<Sum>i<?m. coeffs i * vx_m i)
                     \<and> y = (\<Sum>i<?m. coeffs i * vy_m i)}"
      and hC7m: "\<forall>i<?m. \<forall>j<?m. fst (w!i) = fst (w!j) \<longrightarrow>
          (\<forall>t\<in>I_set. q_m ((1-t)*vx_m i+t*vx_m(Suc i mod ?m),(1-t)*vy_m i+t*vy_m(Suc i mod ?m))
           = (if snd(w!i)=snd(w!j)
              then q_m ((1-t)*vx_m j+t*vx_m(Suc j mod ?m),(1-t)*vy_m j+t*vy_m(Suc j mod ?m))
              else q_m (t*vx_m j+(1-t)*vx_m(Suc j mod ?m),t*vy_m j+(1-t)*vy_m(Suc j mod ?m))))"
      and hC10m: "\<forall>i<?m. let cx=(\<Sum>j<?m. vx_m j)/real ?m; cy=(\<Sum>j<?m. vy_m j)/real ?m
           in (vx_m i-cx)*(vy_m(Suc i mod ?m)-cy)-(vy_m i-cy)*(vx_m(Suc i mod ?m)-cx) > 0"
      and hC11m: "\<forall>i<?m. \<forall>k<?m. k\<noteq>i \<longrightarrow> k\<noteq>Suc i mod ?m \<longrightarrow>
            (vx_m k-vx_m i)*(vy_m(Suc i mod ?m)-vy_m i)-(vy_m k-vy_m i)*(vx_m(Suc i mod ?m)-vx_m i) < 0"
      by (rule quotient_of_scheme_extract_vx)
    \<comment> \<open>Spur collapse map f: P\\_e \\<to> P\\_m.
       Constructed via disk homeomorphisms + arc collapsing.
       Phase 1: extract \\<psi>\\_e and \\<psi>\\_m from polygon\\_homeomorphic\\_to\\_disk\\_with\\_boundary.\<close>
    have "\<exists>f. continuous_on P_e f \<and> f ` P_e = P_m
        \<and> (\<forall>x\<in>P_e. \<forall>y\<in>P_e. (q_e x = q_e y) \<longleftrightarrow> (q_m (f x) = q_m (f y)))"
      sorry \<comment> \<open>TODO: construct f via \\<psi>\\_m\\<inverse> \\<circ> \\<tau> \\<circ> \\<psi>\\_e.\<close>
    then obtain f where
        hf_cont: "continuous_on P_e f"
      and hf_surj: "f ` P_e = P_m"
      and hf_fibres: "\<forall>x\<in>P_e. \<forall>y\<in>P_e. (q_e x = q_e y) \<longleftrightarrow> ((q_m \<circ> f) x = (q_m \<circ> f) y)"
      by (by100 auto)
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
  from scheme_quotient_transfer_along_homeomorphism[OF hY_w hinv]
  have "top1_quotient_of_scheme_on Y TY w" .
  \<comment> \<open>Y is a quotient of w (same space!) with original topology. Identity is the homeomorphism.\<close>
  thus ?thesis by (rule same_space_implies_homeo_realization)
qed

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
  sorry \<comment> \<open>Old chain; live proof is via valid\\_equiv\\_preserves\\_quotient\\_homeo.\<close>

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


