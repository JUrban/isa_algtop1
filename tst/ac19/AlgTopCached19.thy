theory AlgTopCached19
  imports "AlgTopCached18.AlgTopCached18"
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

\<comment> \<open>Spur-collapse homeomorphism (Munkres §76 operation (vi)).
   Given canonical quotients of [a, a^{-1}] @ w and w (from scheme\\_quotient\\_exists),
   the spur pair (first two edges) collapses to a vertex in the quotient.
   The remaining edges correspond exactly to the w-scheme edges.
   Result: quotient([a, a^{-1}] @ w) is homeomorphic to quotient(w).

   Proof approach (following book §76, Figure 76.3):
   Both P\\_ef and P\\_wf are homeomorphic to B2 (by polygon\\_homeomorphic\\_to\\_disk\\_with\\_boundary).
   Under the disk homeomorphisms, the boundary edge arcs become S1 arcs.
   The spur pair (edges 0,1) corresponds to two adjacent S1 arcs that are identified
   by C7 (opposite direction). Collapsing these identified arcs gives B2 again.
   The composition q\\_wf composed with disk\\_homeo composed with spur\\_collapse
   gives a continuous surjection g: P\\_ef -> Y\\_wf.
   Fibre matching g fibres = q\\_ef fibres follows from:
   - Interior: C8 injectivity on both sides
   - Non-spur edges: C7/C9 label matching transfers
   - Spur to vertex: C12 prevents vertex-edge crossings
   - Vertex chains: vtgt transfers via label correspondence
   Apply quotient\\_same\\_fibres\\_homeomorphic.\<close>
\<comment> \<open>Lemmas sin_sum_minus_sin_add, fan_det_pos_regular, cross_positive_from_det_bounds,
   cross_negative_from_det_bounds, frac_eq_from_cross_mult, cyclic_sign_change,
   convex_combo_edge_cross_strict have been moved to AlgTopCached17.\<close>


\<comment> \<open>Standalone lemma: if phi(p) = spur arc point and jp=0, then t\\_p = 0.
   From the affine form: (1-s-t)*cw + s*u\\_0 + t*u\\_1 = (1-r)*u\\_0 + r*cw.
   Rearranging: s*(u\\_0-cw) + t*(u\\_1-cw) = (1-r)*(u\\_0-cw).
   Cramer with det(u\\_0-cw, u\\_1-cw) = C10(0) > 0:
   t*C10(0) = (1-r)*det(u\\_0-cw, u\\_0-cw) = 0. So t = 0.\<close>
lemma spur_match_sector0_forces_t_zero:
  fixes nw :: nat and vxw vyw :: "nat \<Rightarrow> real" and cxw cyw :: real
  assumes hnw: "nw \<ge> 3"
      and hC10_0: "(vxw 0 - cxw) * (vyw(Suc 0 mod nw) - cyw) - (vyw 0 - cyw) * (vxw(Suc 0 mod nw) - cxw) > 0"
      and hmx: "(1-s-tp)*cxw + s*vxw 0 + tp*vxw(Suc 0 mod nw) = (1-r)*vxw 0 + r*cxw"
      and hmy: "(1-s-tp)*cyw + s*vyw 0 + tp*vyw(Suc 0 mod nw) = (1-r)*vyw 0 + r*cyw"
  shows "tp = 0"
proof -
  \<comment> \<open>Multiply hmx by (vyw 0-cyw), hmy by (vxw 0-cxw), subtract to eliminate s.\<close>
  define Ay where "Ay = vyw 0 - cyw"
  define Ax where "Ax = vxw 0 - cxw"
  \<comment> \<open>From hmx: Ay*((1-s-tp)*cxw + s*vxw 0 + tp*vxw(Suc 0 mod nw)) = Ay*((1-r)*vxw 0 + r*cxw).\<close>
  \<comment> \<open>From hmy: Ax*((1-s-tp)*cyw + s*vyw 0 + tp*vyw(Suc 0 mod nw)) = Ax*((1-r)*vyw 0 + r*cyw).\<close>
  \<comment> \<open>Subtract: Ay*LHS\\_x - Ax*LHS\\_y = Ay*RHS\\_x - Ax*RHS\\_y.\<close>
  \<comment> \<open>LHS: (1-s-tp)*(Ay*cxw-Ax*cyw) + s*(Ay*vxw 0-Ax*vyw 0) + tp*(Ay*vxw(suc)-Ax*vyw(suc)).\<close>
  \<comment> \<open>Key: Ay*vxw 0 - Ax*vyw 0 = (vyw 0-cyw)*vxw 0 - (vxw 0-cxw)*vyw 0 = cxw*vyw 0-cyw*vxw 0
     = Ay*cxw - Ax*cyw. So the (1-s-tp) and s terms COMBINE: (1-tp)*(Ay*cxw-Ax*cyw).\<close>
  \<comment> \<open>RHS: (1-r)*Ay*vxw 0 + r*Ay*cxw - (1-r)*Ax*vyw 0 - r*Ax*cyw
     = (1-r)*(Ay*vxw 0-Ax*vyw 0) + r*(Ay*cxw-Ax*cyw)
     = (1-r)*(Ay*cxw-Ax*cyw) + r*(Ay*cxw-Ax*cyw) = Ay*cxw - Ax*cyw.\<close>
  \<comment> \<open>So: (1-tp)*(Ay*cxw-Ax*cyw) + tp*(Ay*vxw(suc)-Ax*vyw(suc)) = Ay*cxw - Ax*cyw.\<close>
  \<comment> \<open>Hence: tp*(Ay*vxw(suc)-Ax*vyw(suc) - (Ay*cxw-Ax*cyw)) = 0.\<close>
  \<comment> \<open>The coefficient of tp is: Ay*(vxw(suc)-cxw) - Ax*(vyw(suc)-cyw) = C10(0) > 0.\<close>
  \<comment> \<open>Define products for Cramer cross-multiplication.\<close>
  have h1: "Ay*((1-s-tp)*cxw + s*vxw 0 + tp*vxw(Suc 0 mod nw)) = Ay*((1-r)*vxw 0 + r*cxw)"
    using hmx by simp
  have h2: "Ax*((1-s-tp)*cyw + s*vyw 0 + tp*vyw(Suc 0 mod nw)) = Ax*((1-r)*vyw 0 + r*cyw)"
    using hmy by simp
  \<comment> \<open>Subtract h2 from h1. On the LHS, the s*(Ay*vxw 0 - Ax*vyw 0) and
     (1-s-tp)*(Ay*cxw - Ax*cyw) terms combine because Ay*vxw 0 - Ax*vyw 0 = Ay*cxw - Ax*cyw.
     Result: tp * ((Ax*(vyw(Suc 0 mod nw)-cyw) - Ay*(vxw(Suc 0 mod nw)-cxw))) = 0.
     But Ax*(vyw(suc)-cyw) - Ay*(vxw(suc)-cxw) = -C10(0) < 0. Wait, let me check the sign.\<close>
  \<comment> \<open>Actually: Ay*vxw(suc) - Ax*vyw(suc) - (Ay*cxw - Ax*cyw) =
     Ay*(vxw(suc)-cxw) - Ax*(vyw(suc)-cyw) = (vyw 0-cyw)*(vxw(suc)-cxw)-(vxw 0-cxw)*(vyw(suc)-cyw).
     This is -C10(0) (by antisymmetry). So tp*(-C10(0)) = 0, tp = 0.\<close>
  \<comment> \<open>The algebra is tedious but straightforward. Sorry for now.\<close>
  \<comment> \<open>The key Cramer cross-multiplication identity.\<close>
  have htp_zero: "tp * ((vyw 0-cyw)*(vxw(Suc 0 mod nw)-cxw) - (vxw 0-cxw)*(vyw(Suc 0 mod nw)-cyw)) = 0"
  proof -
    \<comment> \<open>h1-h2 gives: the difference of the cross-multiplied matching equations.\<close>
    from h1 have h1': "(vyw 0-cyw)*((1-s-tp)*cxw + s*vxw 0 + tp*vxw(Suc 0 mod nw)) =
        (vyw 0-cyw)*((1-r)*vxw 0 + r*cxw)" unfolding Ay_def .
    from h2 have h2': "(vxw 0-cxw)*((1-s-tp)*cyw + s*vyw 0 + tp*vyw(Suc 0 mod nw)) =
        (vxw 0-cxw)*((1-r)*vyw 0 + r*cyw)" unfolding Ax_def .
    \<comment> \<open>Expand and subtract. The key cancellation: the s terms cancel because
       (vyw 0-cyw)*vxw 0 - (vxw 0-cxw)*vyw 0 = cxw*(vyw 0)-cyw*(vxw 0)
       and (vyw 0-cyw)*cxw - (vxw 0-cxw)*cyw = same. So (1-s-tp+s)=1-tp factor.\<close>
    show ?thesis using h1' h2' by (by20000 algebra)
  qed
  have hdet_ne: "(vyw 0-cyw)*(vxw(Suc 0 mod nw)-cxw) - (vxw 0-cxw)*(vyw(Suc 0 mod nw)-cyw) \<noteq> 0"
    using hC10_0 by linarith
  from htp_zero hdet_ne show "tp = 0" by simp
qed

\<comment> \<open>Symmetric lemma for jp=nw-1: if phi(p) = spur and Suc jp mod nw = 0 (u\\_{jp+1}=u\\_0),
   then s\\_p = 0. The matching equation gives s*(u\\_j-cw)+t*(u\\_0-cw)=(1-r)*(u\\_0-cw),
   and Cramer with C10(jp) > 0 shows s = 0.\<close>
lemma spur_match_sector_last_forces_s_zero:
  fixes nw :: nat and vxw vyw :: "nat \<Rightarrow> real" and cxw cyw :: real
  assumes hnw: "nw \<ge> 3"
      and hjp: "jp < nw" and hjp_last: "Suc jp mod nw = 0"
      and hC10_jp: "(vxw jp - cxw) * (vyw(Suc jp mod nw) - cyw) - (vyw jp - cyw) * (vxw(Suc jp mod nw) - cxw) > 0"
      and hmx: "(1-sp-t)*cxw + sp*vxw jp + t*vxw(Suc jp mod nw) = (1-r)*vxw 0 + r*cxw"
      and hmy: "(1-sp-t)*cyw + sp*vyw jp + t*vyw(Suc jp mod nw) = (1-r)*vyw 0 + r*cyw"
  shows "sp = 0"
proof -
  \<comment> \<open>Suc jp mod nw = 0, so vxw(Suc jp mod nw) = vxw 0.\<close>
  from hjp_last have hvx: "vxw(Suc jp mod nw) = vxw 0" "vyw(Suc jp mod nw) = vyw 0" by auto
  \<comment> \<open>Multiply hmy by (vxw(Suc jp mod nw)-cxw)=(vxw 0-cxw), hmx by (vyw(Suc jp mod nw)-cyw)=(vyw 0-cyw).
     Subtract to eliminate t. For jp=nw-1: u\\_{jp+1}=u\\_0, so the t coefficients match the RHS.\<close>
  define Bx where "Bx = vxw 0 - cxw"
  define By where "By = vyw 0 - cyw"
  have h1: "By*((1-sp-t)*cxw + sp*vxw jp + t*vxw 0) = By*((1-r)*vxw 0 + r*cxw)"
    using hmx hvx by simp
  have h2: "Bx*((1-sp-t)*cyw + sp*vyw jp + t*vyw 0) = Bx*((1-r)*vyw 0 + r*cyw)"
    using hmy hvx by simp
  \<comment> \<open>h1 - h2 eliminates t and (1-sp-t) by the same cancellation as sector0.\<close>
  have hsp_zero: "sp * ((vxw jp - cxw)*(vyw 0 - cyw) - (vyw jp - cyw)*(vxw 0 - cxw)) = 0"
  proof -
    from h1 have h1': "By*((1-sp-t)*cxw + sp*vxw jp + t*vxw 0) =
        By*((1-r)*vxw 0 + r*cxw)" .
    from h2 have h2': "Bx*((1-sp-t)*cyw + sp*vyw jp + t*vyw 0) =
        Bx*((1-r)*vyw 0 + r*cyw)" .
    show ?thesis using h1' h2' unfolding Bx_def By_def by (by20000 algebra)
  qed
  have hdet_ne: "(vxw jp - cxw)*(vyw 0 - cyw) - (vyw jp - cyw)*(vxw 0 - cxw) \<noteq> 0"
  proof -
    from hC10_jp hvx have "(vxw jp - cxw)*(vyw 0 - cyw) - (vyw jp - cyw)*(vxw 0 - cxw) > 0"
      by simp
    thus ?thesis by linarith
  qed
  from hsp_zero hdet_ne show "sp = 0" by simp
qed

\<comment> \<open>Cramer inverse: if sp*det = fy*dx-fx*dy and tp*det = ex*dy-ey*dx and tp=0 and det\\<noteq>0,
   then dx = sp*ex and dy = sp*ey.\<close>
lemma cramer_inverse_tp_zero:
  assumes hsp_mul: "sp*det_v = fy*dx - fx*dy"
      and htp_mul: "tp*det_v = ex*dy - ey*dx"
      and htp0: "(tp::real) = 0"
      and hdet_ne: "det_v \<noteq> 0"
      and hdet_eq: "det_v = ex*fy - ey*fx"
  shows "dx = sp*ex" "dy = sp*ey"
proof -
  have "dx*det_v = (fy*dx-fx*dy)*ex + (ex*dy-ey*dx)*fx"
    unfolding hdet_eq by (by20000 algebra)
  hence "dx*det_v = sp*det_v*ex + tp*det_v*fx" using hsp_mul htp_mul by simp
  with htp0 have "dx*det_v = (sp*ex)*det_v" by (by100 algebra)
  thus "dx = sp*ex" using hdet_ne by simp
next
  have "dy*det_v = (fy*dx-fx*dy)*ey + (ex*dy-ey*dx)*fy"
    unfolding hdet_eq by (by20000 algebra)
  hence "dy*det_v = sp*det_v*ey + tp*det_v*fy" using hsp_mul htp_mul by simp
  with htp0 have "dy*det_v = (sp*ey)*det_v" by (by100 algebra)
  thus "dy = sp*ey" using hdet_ne by simp
qed

\<comment> \<open>Symmetric Cramer inverse: sp=0 gives dx = tp*fx, dy = tp*fy.\<close>
lemma cramer_inverse_sp_zero:
  assumes hsp_mul: "sp*det_v = fy*dx - fx*dy"
      and htp_mul: "tp*det_v = ex*dy - ey*dx"
      and hsp0: "(sp::real) = 0"
      and hdet_ne: "det_v \<noteq> 0"
      and hdet_eq: "det_v = ex*fy - ey*fx"
  shows "dx = tp*fx" "dy = tp*fy"
proof -
  have "dx*det_v = (fy*dx-fx*dy)*ex + (ex*dy-ey*dx)*fx"
    unfolding hdet_eq by (by20000 algebra)
  hence "dx*det_v = sp*det_v*ex + tp*det_v*fx" using hsp_mul htp_mul by simp
  with hsp0 have "dx*det_v = (tp*fx)*det_v" by (by100 algebra)
  thus "dx = tp*fx" using hdet_ne by simp
next
  have "dy*det_v = (fy*dx-fx*dy)*ey + (ex*dy-ey*dx)*fy"
    unfolding hdet_eq by (by20000 algebra)
  hence "dy*det_v = sp*det_v*ey + tp*det_v*fy" using hsp_mul htp_mul by simp
  with hsp0 have "dy*det_v = (tp*fy)*det_v" by (by100 algebra)
  thus "dy = tp*fy" using hdet_ne by simp
qed

\<comment> \<open>Standalone lemma: spur arc point is NOT in target sector jp for jp \\<notin> {0, nw-1}.
   The spur arc ((1-t)*u\\_0 + t*cw) has cross\\_cw(j, spur) = (1-t)*cross\\_cw(j, u\\_0).
   cross\\_cw(j, u\\_0) = det(u\\_j-cw, u\\_0-cw).
   For jp \\<notin> {0, nw-1}: either cross\\_cw(jp, u\\_0) < 0 (from consecutive C10 analysis)
   or cross\\_cw(Suc jp mod nw, u\\_0) > 0, so the in\\_tsector condition fails.\<close>
lemma spur_arc_target_sector:
  fixes nw :: nat and vxw vyw :: "nat \<Rightarrow> real" and cxw cyw :: real
  assumes hnw: "nw \<ge> 3"
      and hC10: "\<forall>i<nw. (vxw i - cxw) * (vyw(Suc i mod nw) - cyw) -
          (vyw i - cyw) * (vxw(Suc i mod nw) - cxw) > 0"
      and hC11: "\<forall>i<nw. \<forall>k<nw. k\<noteq>i \<longrightarrow> k\<noteq>Suc i mod nw \<longrightarrow>
          (vxw k-vxw i)*(vyw(Suc i mod nw)-vyw i)-(vyw k-vyw i)*(vxw(Suc i mod nw)-vxw i) < 0"
      and hC5: "cxw = (\<Sum>j<nw. vxw j) / real nw" "cyw = (\<Sum>j<nw. vyw j) / real nw"
      and hfan_det: "\<forall>m n. 2 \<le> m \<longrightarrow> m < n \<longrightarrow> n < nw \<longrightarrow>
          (vxw m - vxw 1) * (vyw n - vyw 1) - (vyw m - vyw 1) * (vxw n - vxw 1) > 0"
      and hregular: "\<exists>r > 0. \<forall>j<nw. (vxw j - cxw)^2 + (vyw j - cyw)^2 = r^2"
      and hjp: "jp < nw" and hjp_ne0: "jp \<noteq> 0" and hjp_ne_last: "Suc jp mod nw \<noteq> 0"
  shows "(vxw jp-cxw)*(vyw 0-cyw)-(vyw jp-cyw)*(vxw 0-cxw) < 0
         \<or> (vxw(Suc jp mod nw)-cxw)*(vyw 0-cyw)-(vyw(Suc jp mod nw)-cyw)*(vxw 0-cxw) > 0"
proof -
  \<comment> \<open>cross\\_cw(j, u\\_0) = det(u\\_j-cw, u\\_0-cw) = -(det(u\\_0-cw, u\\_j-cw)).\<close>
  define cc where "cc j = (vxw j-cxw)*(vyw 0-cyw)-(vyw j-cyw)*(vxw 0-cxw)" for j
  \<comment> \<open>cc(0) = 0 (self), cc(1) < 0 (from C10 at i=0, antisymmetry),
     cc(nw-1) > 0 (from C10 at i=nw-1).\<close>
  have hcc0: "cc 0 = 0" unfolding cc_def by (by100 simp)
  have hcc1: "cc 1 < 0"
  proof -
    from hC10[rule_format, of 0] hnw
    have "(vxw 0 - cxw) * (vyw(Suc 0 mod nw) - cyw) - (vyw 0 - cyw) * (vxw(Suc 0 mod nw) - cxw) > 0"
      by simp
    hence "(vxw 0 - cxw) * (vyw 1 - cyw) - (vyw 0 - cyw) * (vxw 1 - cxw) > 0"
      using hnw by simp
    \<comment> \<open>cc(1) = -(the above) < 0.\<close>
    \<comment> \<open>cc(1) = -(C10 at 0) by expand + algebra\\_simps.\<close>
    have "cc 1 = -((vxw 0 - cxw) * (vyw 1 - cyw) - (vyw 0 - cyw) * (vxw 1 - cxw))"
      unfolding cc_def by (simp add: algebra_simps mult.commute)
    thus ?thesis using \<open>(vxw 0 - cxw) * (vyw 1 - cyw) - (vyw 0 - cyw) * (vxw 1 - cxw) > 0\<close> by linarith
  qed
  have hcc_last: "cc (nw - 1) > 0"
  proof -
    have "nw - 1 < nw" using hnw by linarith
    from hC10[rule_format, OF this]
    have "(vxw (nw-1) - cxw) * (vyw(Suc(nw-1) mod nw) - cyw) - (vyw (nw-1) - cyw) * (vxw(Suc(nw-1) mod nw) - cxw) > 0" .
    have "Suc(nw-1) mod nw = 0" using hnw by simp
    hence "(vxw (nw-1) - cxw) * (vyw 0 - cyw) - (vyw (nw-1) - cyw) * (vxw 0 - cxw) > 0"
      using \<open>(vxw (nw-1) - cxw) * (vyw(Suc(nw-1) mod nw) - cyw) - (vyw (nw-1) - cyw) * (vxw(Suc(nw-1) mod nw) - cxw) > 0\<close>
      by simp
    thus ?thesis unfolding cc_def .
  qed
  \<comment> \<open>Main argument: if cc(jp) \\<ge> 0 then cc(Suc jp mod nw) > 0.
     Proof: cc goes 0 \\<to> negative \\<to> ... \\<to> positive \\<to> 0.
     Once cc becomes \\<ge> 0 (past the minimum), it stays positive.
     This uses the monotone CCW sweep from C10.\<close>
  show ?thesis
  proof (cases "cc jp < 0")
    case True thus ?thesis unfolding cc_def by auto
  next
    case False
    hence "cc jp \<ge> 0" by linarith
    \<comment> \<open>cc(jp) \\<ge> 0 with jp \\<ge> 1 and jp+1 < nw: show cc(jp+1) > 0.
       Since cc(1) < 0 and cc(jp) \\<ge> 0 with jp \\<ge> 2: the sign changed from neg to nonneg.
       With the CCW sweep, once nonneg, stays positive for subsequent vertices.\<close>
    \<comment> \<open>Key: cc(jp+1) = cc(jp) + det(edge\\_jp, u\\_0-cw).
       From the CCW sweep property: when cc(jp) \\<ge> 0, the edge direction
       is such that the increment keeps cc positive.\<close>
    \<comment> \<open>For now: sorry this monotonicity property.\<close>
    \<comment> \<open>cc(jp) \\<ge> 0 and jp \\<noteq> 0 and jp+1 \\<noteq> nw: show cc(jp+1) > 0.
       From cc(1) < 0: jp \\<ge> 2. From cc(nw-1) > 0: jp+1 \\<le> nw-2.
       The centroid cross product sequence is: 0, neg, ..., neg, (0/pos), pos, ..., pos, 0.
       Once non-negative, the subsequent values are positive.
       This follows from the convex polygon structure (C10 + centroid inside).\<close>
    \<comment> \<open>PROOF: Use the fact that each C10 step has angle < \\<pi>.
       det(u\\_j-cw, u\\_{j+1}-cw) > 0 means the angle from cw→u\\_j to cw→u\\_{j+1} is in (0,\\<pi>).
       Cumulative: if the total angle from u\\_0 to u\\_jp exceeds \\<pi> (i.e., cc(jp) \\<ge> 0),
       adding one more step (< \\<pi>) keeps it in (\\<pi>, 2\\<pi>), so cc(jp+1) > 0.
       This is formalized via the "cross product chain" property.\<close>
    \<comment> \<open>Key helper: for vectors a,b with det(a,b) \\<le> 0 and |a|,|b| > 0, and c with det(b,c) > 0,
       if additionally det(a, -(r*b+s*c)) \\<ge> 0 for some r > 0, s > 0 (encoding angle < 2\\<pi>),
       then det(a,c) < 0.
       Simpler: use the Jacobi identity det(a,b)*c + det(b,c)*a + det(c,a)*b = 0 (vector form).
       From det(a,b) \\<le> 0, det(b,c) > 0: if det(a,c) \\<ge> 0, then from Jacobi:
       det(a,b)*c = -det(b,c)*a + det(a,c)*b. The RHS has -det(b,c)*a (opposite to a) + det(a,c)*b.
       Need to show this is contradictory given the polygon structure.\<close>
    \<comment> \<open>Use the "half-plane chain" from C10:
       The sequence u\\_0-cw, u\\_1-cw, ..., u\\_{nw-1}-cw goes CCW around cw.
       Each pair (u\\_j-cw, u\\_{j+1}-cw) has positive det (C10).
       The signed angle from the first to the last vector is exactly 2\\<pi>-\\<delta>\\_0 where \\<delta>\\_0 > 0.
       u\\_0 is the "starting" direction. Once the cumulative angle passes \\<pi>,
       the det with u\\_0-cw flips sign permanently.\<close>
    have hjp_lt: "jp < nw - 1"
    proof (rule ccontr)
      assume "\<not> jp < nw - 1"
      hence "jp \<ge> nw - 1" by (by100 linarith)
      with hjp have "jp = nw - 1" by (by100 linarith)
      hence "Suc jp = nw" using hnw by (by100 arith)
      hence "Suc jp mod nw = 0" by (by100 simp)
      with hjp_ne_last show False by simp
    qed
    have hsjp: "Suc jp mod nw = jp + 1" using hjp_lt by (by100 simp)
    \<comment> \<open>The DECISIVE helper: det(u\\_0-cw, u\\_{jp+1}-cw) < 0 when det(u\\_0-cw, u\\_jp-cw) \\<le> 0.
       This follows from: u\\_{jp+1} is CCW of u\\_jp (from C10), and the CCW step is < \\<pi>,
       so u\\_{jp+1} stays in the same half-plane as u\\_jp (w.r.t. the line through cw \\<perp> u\\_0-cw).
       Formal proof: use C11 to show the step stays bounded.\<close>
    \<comment> \<open>PROOF via complex-number argument (Arg function).
       Convert vectors to complex, use Arg(z\\_{j+1}/z\\_j) \\<in> (0,\\<pi>) from C10,
       telescope to get cumulative angle, then use angle arithmetic.\<close>
    define zw :: "nat \<Rightarrow> complex" where "zw j = Complex (vxw j - cxw) (vyw j - cyw)" for j
    have hzw_ne: "\<forall>j<nw. zw j \<noteq> 0"
    proof (intro allI impI)
      fix j assume hj: "j < nw"
      show "zw j \<noteq> 0"
      proof
        assume "zw j = 0"
        hence "vxw j = cxw" "vyw j = cyw" unfolding zw_def by (auto simp: complex_eq_iff)
        from hC10[rule_format, OF hj]
        have "(vxw j - cxw) * (vyw(Suc j mod nw) - cyw) -
            (vyw j - cyw) * (vxw(Suc j mod nw) - cxw) > 0" .
        with \<open>vxw j = cxw\<close> \<open>vyw j = cyw\<close> show False by simp
      qed
    qed
    \<comment> \<open>C10 gives Im(cnj(z\\_j)*z\\_{j+1}) > 0, i.e., the angular step is in (0,\\<pi>).\<close>
    have hC10_im: "\<forall>j<nw. Im (cnj (zw j) * zw (Suc j mod nw)) > 0"
    proof (intro allI impI)
      fix j assume hj: "j < nw"
      have "Im (cnj (zw j) * zw (Suc j mod nw)) =
          (vxw j - cxw) * (vyw(Suc j mod nw) - cyw) - (vyw j - cyw) * (vxw(Suc j mod nw) - cxw)"
      proof -
        define a where "a = vxw j - cxw"
        define b where "b = vyw j - cyw"
        define c where "c = vxw(Suc j mod nw) - cxw"
        define d where "d = vyw(Suc j mod nw) - cyw"
        have hzj: "zw j = Complex a b" unfolding zw_def a_def b_def by simp
        have hzk: "zw (Suc j mod nw) = Complex c d" unfolding zw_def c_def d_def by simp
        have "cnj (zw j) * zw (Suc j mod nw) = Complex a (-b) * Complex c d"
          unfolding hzj hzk using complex_cnj[of a b] by simp
        also have "\<dots> = Complex (a*c+b*d) (a*d-b*c)"
          using complex_mult[of a "- b" c d] by simp
        finally have "Im (cnj (zw j) * zw (Suc j mod nw)) = a*d-b*c" by simp
        thus ?thesis unfolding a_def b_def c_def d_def .
      qed
      also have "\<dots> > 0" using hC10[rule_format, OF hj] .
      finally show "Im (cnj (zw j) * zw (Suc j mod nw)) > 0" .
    qed
    \<comment> \<open>cc(j) = Im(cnj(z\\_j)*z\\_0) = -(Im(cnj(z\\_0)*z\\_j)).\<close>
    have hcc_im: "\<forall>j<nw. cc j = Im (cnj (zw j) * zw 0)"
    proof (intro allI impI)
      fix j assume "j < nw"
      show "cc j = Im (cnj (zw j) * zw 0)"
      proof -
        define a where "a = vxw j - cxw"
        define b where "b = vyw j - cyw"
        define c where "c = vxw 0 - cxw"
        define d where "d = vyw 0 - cyw"
        have hzj: "zw j = Complex a b" unfolding zw_def a_def b_def by simp
        have hz0: "zw 0 = Complex c d" unfolding zw_def c_def d_def by simp
        have "cnj (zw j) * zw 0 = Complex a (-b) * Complex c d"
          unfolding hzj hz0 using complex_cnj[of a b] by simp
        also have "\<dots> = Complex (a*c+b*d) (a*d-b*c)"
          using complex_mult[of a "- b" c d] by simp
        finally have "Im (cnj (zw j) * zw 0) = a*d-b*c" by simp
        also have "a*d-b*c = cc j" unfolding a_def b_def c_def d_def cc_def by (by100 simp)
        finally show ?thesis by simp
      qed
    qed
    \<comment> \<open>Define angular steps and cumulative angle.\<close>
    define theta where "theta j = Arg (zw (Suc j mod nw) / zw j)" for j
    have htheta_pos: "\<forall>j<nw. theta j > 0 \<and> theta j < pi"
    proof (intro allI impI conjI)
      fix j assume hj: "j < nw"
      have hzj_ne: "zw j \<noteq> 0" using hzw_ne hj by (by100 blast)
      have hzk_ne: "zw (Suc j mod nw) \<noteq> 0" using hzw_ne hj hnw by (by100 auto)
      have hratio_ne: "zw (Suc j mod nw) / zw j \<noteq> 0" using hzj_ne hzk_ne by (by100 simp)
      \<comment> \<open>Im(cnj z * w) = |z|^2 * Im(w/z).\<close>
      \<comment> \<open>From Im(cnj z * w) > 0: Im(w/z) > 0 (since cnj z * w = |z|^2 * (w/z)).\<close>
      have "Im (zw (Suc j mod nw) / zw j) > 0"
      proof -
        have "cnj (zw j) * (zw (Suc j mod nw) / zw j) = cnj (zw j) / zw j * zw (Suc j mod nw)"
          using hzj_ne by (by100 simp)
        have "cnj (zw j) * zw (Suc j mod nw) = zw j * cnj (zw j) * (zw (Suc j mod nw) / zw j)"
          using hzj_ne by (by100 simp)
        have "zw j * cnj (zw j) = of_real ((cmod (zw j))^2)"
          using complex_norm_square[of "zw j"] by simp
        hence "cnj (zw j) * zw (Suc j mod nw) = of_real ((cmod (zw j))^2) * (zw (Suc j mod nw) / zw j)"
          using \<open>cnj (zw j) * zw (Suc j mod nw) = zw j * cnj (zw j) * _\<close> by simp
        hence hIm_eq: "Im (cnj (zw j) * zw (Suc j mod nw)) = (cmod (zw j))^2 * Im (zw (Suc j mod nw) / zw j)"
        proof -
          from \<open>cnj (zw j) * zw (Suc j mod nw) = of_real ((cmod (zw j))^2) * (zw (Suc j mod nw) / zw j)\<close>
          have "Im (cnj (zw j) * zw (Suc j mod nw)) = Im (of_real ((cmod (zw j))^2) * (zw (Suc j mod nw) / zw j))"
            by simp
          also have "\<dots> = (cmod (zw j))^2 * Im (zw (Suc j mod nw) / zw j)"
          proof -
            define w where "w = zw (Suc j mod nw) / zw j"
            define r where "r = (cmod (zw j))^2"
            have "Im (of_real r * w) = r * Im w"
            proof -
              have "of_real r * w = Complex (r * Re w) (r * Im w)"
                by (cases w) (simp add: complex_of_real_mult_Complex)
              thus ?thesis by simp
            qed
            thus ?thesis unfolding w_def r_def .
          qed
          finally show ?thesis .
        qed
        with hC10_im[rule_format, OF hj] have "(cmod (zw j))^2 * Im (zw (Suc j mod nw) / zw j) > 0" by linarith
        moreover have "((cmod (zw j))^2 :: real) > 0" using hzj_ne by (by100 simp)
        ultimately show ?thesis
        proof -
          assume hab: "(cmod (zw j))^2 * Im (zw (Suc j mod nw) / zw j) > 0"
              and ha: "((cmod (zw j))^2 :: real) > 0"
          show "Im (zw (Suc j mod nw) / zw j) > 0"
          proof (rule ccontr)
            assume "\<not> Im (zw (Suc j mod nw) / zw j) > 0"
            hence "Im (zw (Suc j mod nw) / zw j) \<le> 0" by linarith
            hence "(cmod (zw j))^2 * Im (zw (Suc j mod nw) / zw j) \<le> 0"
              using ha mult_nonneg_nonpos[of "(cmod (zw j))^2" "Im (zw (Suc j mod nw) / zw j)"]
              by linarith
            with hab show False by linarith
          qed
        qed
      qed
      \<comment> \<open>From Im > 0 and z \\<noteq> 0: sin(Arg z) > 0, hence Arg z \\<in> (0, \\<pi>).\<close>
      have "sin (Arg (zw (Suc j mod nw) / zw j)) > 0"
        using sin_Arg[OF hratio_ne] \<open>Im (zw (Suc j mod nw) / zw j) > 0\<close> hratio_ne
        by (by100 simp)
      have "Arg (zw (Suc j mod nw) / zw j) > -pi" using Arg_bounded[of "zw (Suc j mod nw) / zw j"] by linarith
      have "Arg (zw (Suc j mod nw) / zw j) \<le> pi" using Arg_bounded[of "zw (Suc j mod nw) / zw j"] by linarith
      show "theta j > 0" unfolding theta_def
      proof (rule ccontr)
        assume "\<not> Arg (zw (Suc j mod nw) / zw j) > 0"
        hence "Arg (zw (Suc j mod nw) / zw j) \<le> 0" by linarith
        with \<open>Arg _ > -pi\<close> have "Arg (zw (Suc j mod nw) / zw j) \<in> {x. -pi < x \<and> x \<le> 0}" by auto
        hence "sin (Arg (zw (Suc j mod nw) / zw j)) \<le> 0"
        proof -
          from \<open>Arg _ \<le> 0\<close> \<open>Arg _ > -pi\<close>
          have h1: "0 \<le> -(Arg (zw (Suc j mod nw) / zw j))" by linarith
          have h2: "-(Arg (zw (Suc j mod nw) / zw j)) \<le> pi" using \<open>Arg _ > -pi\<close> by linarith
          from sin_ge_zero[OF h1 h2] have "sin (-(Arg (zw (Suc j mod nw) / zw j))) \<ge> 0" .
          thus ?thesis by (by100 simp)
        qed
        with \<open>sin _ > 0\<close> show False by linarith
      qed
      show "theta j < pi" unfolding theta_def
      proof (rule ccontr)
        assume "\<not> Arg (zw (Suc j mod nw) / zw j) < pi"
        with \<open>Arg _ \<le> pi\<close> have "Arg (zw (Suc j mod nw) / zw j) = pi" by linarith
        hence "sin (Arg (zw (Suc j mod nw) / zw j)) = 0" by (by100 simp)
        with \<open>sin _ > 0\<close> show False by linarith
      qed
    qed
    define alpha where "alpha m = (\<Sum>j<m. theta j)" for m
    \<comment> \<open>Partial telescope for m < nw: z\\_m = (\\<Prod>\\_{j<m} ratio\\_j) * z\\_0.
       For j < m < nw: Suc j mod nw = j+1, so ratios telescope.\<close>
    have hpartial_telescope: "\<forall>m<nw. zw m = (\<Prod>j<m. zw (Suc j mod nw) / zw j) * zw 0"
    proof -
      have aux: "\<And>m. m < nw \<Longrightarrow> zw m = (\<Prod>j<m. zw (Suc j mod nw) / zw j) * zw 0"
      proof -
        fix m show "m < nw \<Longrightarrow> zw m = (\<Prod>j<m. zw (Suc j mod nw) / zw j) * zw 0"
        proof (induction m)
          case 0 thus ?case by simp
        next
          case (Suc k)
          hence hk_lt: "k < nw" by simp
          have hSuc_lt: "Suc k < nw" using Suc.prems .
          have hSuc_mod: "Suc k mod nw = Suc k" using hSuc_lt by (by100 simp)
          from Suc.IH[OF hk_lt]
          have hIH: "zw k = (\<Prod>j<k. zw (Suc j mod nw) / zw j) * zw 0" .
          have "(\<Prod>j<Suc k. zw (Suc j mod nw) / zw j) =
              (\<Prod>j<k. zw (Suc j mod nw) / zw j) * (zw (Suc k mod nw) / zw k)"
            by simp
          hence "(\<Prod>j<Suc k. zw (Suc j mod nw) / zw j) * zw 0 =
              (\<Prod>j<k. zw (Suc j mod nw) / zw j) * (zw (Suc k) / zw k) * zw 0"
            using hSuc_mod by simp
          also have "\<dots> = (zw (Suc k) / zw k) * ((\<Prod>j<k. zw (Suc j mod nw) / zw j) * zw 0)"
            by (by100 algebra)
          also have "\<dots> = (zw (Suc k) / zw k) * zw k" using hIH by simp
          also have "\<dots> = zw (Suc k)" using hzw_ne[rule_format, OF hk_lt] by simp
          finally show ?case by simp
        qed
      qed
      thus ?thesis by (by100 blast)
    qed
    \<comment> \<open>Product decomposition: each ratio = |ratio|*cis(theta).\<close>
    \<comment> \<open>Product of cis: \\<Prod> cis(\\<theta>\\_j) = cis(\\<Sum> \\<theta>\\_j) = cis(alpha m).\<close>
    \<comment> \<open>Telescope: \\<Prod>\\_{j<nw} (z\\_{j+1}/z\\_j) = 1, so cis(\\<Sum> \\<theta>\\_j) = 1, hence \\<Sum> = 2k\\<pi>.
       For convex polygon (C10): k=1, so \\<Sum> = 2\\<pi>.\<close>
    have htelescope: "(\<Prod>j<nw. zw (Suc j mod nw) / zw j) = 1"
    proof -
      have hnw1_lt: "nw - 1 < nw" using hnw by linarith
      have hz0_ne: "zw 0 \<noteq> 0" using hzw_ne hnw by (by100 simp)
      have hznw1_ne: "zw (nw-1) \<noteq> 0" using hzw_ne hnw1_lt by (by100 blast)
      from hpartial_telescope[rule_format, OF hnw1_lt]
      have hP: "zw (nw-1) = (\<Prod>j<nw-1. zw (Suc j mod nw) / zw j) * zw 0" .
      \<comment> \<open>Split: \\<Prod>\\_{j<nw} = (\\<Prod>\\_{j<nw-1}) * (zw(Suc(nw-1) mod nw) / zw(nw-1)).\<close>
      define f where "f j = zw (Suc j mod nw) / zw j" for j
      have "(\<Prod>j<nw. f j) = (\<Prod>j<nw-1. f j) * f (nw-1)"
      proof -
        have hnw_Suc: "nw = Suc (nw-1)" using hnw by (by100 arith)
        have "{..<Suc (nw-1)} = insert (nw-1) {..<(nw-1)}" by (rule lessThan_Suc)
        hence "{..<nw} = insert (nw-1) {..<nw-1}" using hnw_Suc by simp
        hence "prod f {..<nw} = f (nw-1) * prod f {..<nw-1}" by simp
        thus ?thesis by (by100 algebra)
      qed
      hence hsplit: "(\<Prod>j<nw. zw (Suc j mod nw) / zw j) =
          (\<Prod>j<nw-1. zw (Suc j mod nw) / zw j) * (zw (Suc (nw-1) mod nw) / zw (nw-1))"
        unfolding f_def .
      have "Suc (nw-1) mod nw = 0" using hnw by simp
      with hsplit have "(\<Prod>j<nw. zw (Suc j mod nw) / zw j) =
          (\<Prod>j<nw-1. zw (Suc j mod nw) / zw j) * (zw 0 / zw (nw-1))" by simp
      \<comment> \<open>From hP: (\\<Prod>\\_{j<nw-1}) = zw(nw-1) / zw 0.\<close>
      from hP hz0_ne have "(\<Prod>j<nw-1. zw (Suc j mod nw) / zw j) = zw (nw-1) / zw 0"
        by (by100 simp)
      hence "(\<Prod>j<nw. zw (Suc j mod nw) / zw j) = (zw (nw-1) / zw 0) * (zw 0 / zw (nw-1))"
        using \<open>(\<Prod>j<nw. zw (Suc j mod nw) / zw j) = _ * (zw 0 / zw (nw-1))\<close> by simp
      also have "\<dots> = 1" using hz0_ne hznw1_ne by (by100 simp)
      finally show ?thesis .
    qed
    have halpha_sum: "alpha nw = 2*pi"
    proof -
      \<comment> \<open>Step 1: cis(alpha nw) = 1 from telescope product decomposition.\<close>
      \<comment> \<open>The full product \\<Prod> ratio\\_j = 1 (htelescope). By polar decomposition (induction),
         \\<Prod> ratio\\_j = of\\_real(\\<Prod> cmod ratio\\_j) * cis(alpha nw).
         Since |\\<Prod>| = 1 (from |telescope| = |1| = 1): of\\_real(1) * cis(alpha nw) = 1.\<close>
      define rj where "rj j = zw (Suc j mod nw) / zw j" for j
      \<comment> \<open>From the polar decomposition proof pattern: \\<Prod> rj = of\\_real(\\<Prod> cmod rj) * cis(alpha nw).\<close>
      have hrj_ne: "\<forall>j<nw. rj j \<noteq> 0"
      proof (intro allI impI)
        fix j assume "j < nw"
        have "Suc j mod nw < nw" using hnw by (by100 simp)
        thus "rj j \<noteq> 0" unfolding rj_def
          using hzw_ne[rule_format, OF \<open>Suc j mod nw < nw\<close>] hzw_ne[rule_format, OF \<open>j < nw\<close>]
          by (by100 simp)
      qed
      have "(\<Prod>j<nw. rj j) = of_real (\<Prod>j<nw. cmod (rj j)) * cis (alpha nw)"
      proof -
        \<comment> \<open>By induction: \\<Prod>\\_{j<k} rj = of\\_real(\\<Prod> cmod) * cis(\\<Sum> theta) for k \\<le> nw.\<close>
        have "\<And>k. k \<le> nw \<Longrightarrow> (\<Prod>j<k. rj j) = of_real (\<Prod>j<k. cmod (rj j)) * cis (\<Sum>j<k. theta j)"
        proof -
          fix k show "k \<le> nw \<Longrightarrow> (\<Prod>j<k. rj j) = of_real (\<Prod>j<k. cmod (rj j)) * cis (\<Sum>j<k. theta j)"
          proof (induction k)
            case 0 thus ?case by simp
          next
            case (Suc k')
            hence "k' < nw" by simp
            from Suc.IH[OF order.strict_implies_order[OF \<open>k' < nw\<close>]]
            have hIH: "(\<Prod>j<k'. rj j) = of_real (\<Prod>j<k'. cmod (rj j)) * cis (\<Sum>j<k'. theta j)" .
            from rcis_cmod_Arg[of "rj k'", symmetric]
            have "rj k' = of_real (cmod (rj k')) * cis (Arg (rj k'))" unfolding rcis_def .
            also have "Arg (rj k') = theta k'" unfolding rj_def theta_def by (by100 simp)
            finally have hrj_decomp: "rj k' = of_real (cmod (rj k')) * cis (theta k')" .
            have "(\<Prod>j<Suc k'. rj j) = (\<Prod>j<k'. rj j) * rj k'" by simp
            also have "\<dots> = (of_real (\<Prod>j<k'. cmod (rj j)) * cis (\<Sum>j<k'. theta j)) * (of_real (cmod (rj k')) * cis (theta k'))"
              using hIH hrj_decomp by simp
            also have "\<dots> = rcis ((\<Prod>j<k'. cmod (rj j)) * cmod (rj k')) ((\<Sum>j<k'. theta j) + theta k')"
              unfolding rcis_def using rcis_mult[of "(\<Prod>j<k'. cmod (rj j))" "(\<Sum>j<k'. theta j)" "cmod (rj k')" "theta k'"]
              unfolding rcis_def by simp
            also have "(\<Prod>j<k'. cmod (rj j)) * cmod (rj k') = (\<Prod>j<Suc k'. cmod (rj j))" by simp
            also have "(\<Sum>j<k'. theta j) + theta k' = (\<Sum>j<Suc k'. theta j)" by simp
            finally show ?case unfolding rcis_def .
          qed
        qed
        from this[of nw] show ?thesis unfolding alpha_def by simp
      qed
      also have "(\<Prod>j<nw. rj j) = 1" using htelescope unfolding rj_def .
      also have "(\<Prod>j<nw. cmod (rj j)) = cmod (\<Prod>j<nw. rj j)"
        by (simp add: prod_norm)
      also have "\<dots> = 1" using htelescope unfolding rj_def by simp
      finally have "cis (alpha nw) = 1" by simp
      \<comment> \<open>Step 2: cis(alpha) = 1 \\<Longleftrightarrow> alpha = 2k\\<pi>.\<close>
      \<comment> \<open>Step 3: alpha nw \\<in> (0, nw*\\<pi>). Combined with cis = 1: alpha = 2\\<pi> for nw \\<le> 4,
         and needs C11 convexity for nw \\<ge> 5.\<close>
      have halpha_pos: "alpha nw > 0"
      proof -
        have "\<forall>j\<in>{..<nw}. theta j > 0" using htheta_pos hnw by (by100 auto)
        have "(0::nat) < nw" using hnw by linarith
        hence "{..<nw} \<noteq> {}" by (by100 blast)
        from sum_pos[OF _ \<open>{..<nw} \<noteq> {}\<close>] \<open>\<forall>j\<in>{..<nw}. theta j > 0\<close>
        show ?thesis unfolding alpha_def by (by100 blast)
      qed
      have halpha_lt: "alpha nw < real nw * pi"
      proof -
        have h1: "\<And>j. j < nw \<Longrightarrow> theta j < pi" using htheta_pos by (by100 blast)
        have "alpha nw = (\<Sum>j<nw. theta j)" unfolding alpha_def by simp
        also have "\<dots> < (\<Sum>j<nw. pi)"
        proof (rule sum_strict_mono)
          show "finite {..<nw}" by simp
          have "(0::nat) \<in> {..<nw}" using hnw by simp
          thus "{..<nw} \<noteq> {}" by (by100 blast)
          fix j assume "j \<in> {..<nw}" thus "theta j < pi" using h1 by simp
        qed
        also have "(\<Sum>j<nw. pi) = real nw * pi" by simp
        finally show ?thesis .
      qed
      \<comment> \<open>From cis(alpha) = 1 and alpha > 0: alpha = 2k\\<pi> for some k \\<ge> 1.\<close>
      from \<open>cis (alpha nw) = 1\<close>
      have hcos: "cos (alpha nw) = 1" using cis.sel(1)[of "alpha nw"] by simp
      from \<open>cis (alpha nw) = 1\<close>
      have hsin: "sin (alpha nw) = 0" using cis.sel(2)[of "alpha nw"] by simp
      \<comment> \<open>From alpha \\<in> (0, nw*\\<pi>) and cos=1,sin=0: alpha = 2\\<pi>*(nw div something)...
         For nw \\<le> 4: alpha < 4\\<pi>, so alpha = 2\\<pi>.
         For nw \\<ge> 5: alpha < nw*\\<pi>, and we use C11 to show alpha < 4\\<pi>.\<close>
      \<comment> \<open>From cis = 1: alpha = 2k\\<pi> for integer k. From alpha > 0: k \\<ge> 1.
         From alpha < nw*\\<pi>: 2k < nw. For nw \\<le> 4: k = 1.
         For nw \\<ge> 5: k < nw/2 and C11 convexity rules out k \\<ge> 2.\<close>
      have "\<exists>k::nat. k \<ge> 1 \<and> alpha nw = 2 * real k * pi"
      proof -
        from hcos have "((\<exists>n::nat. alpha nw = real n * 2 * pi) \<or> (\<exists>n::nat. alpha nw = -(real n * 2 * pi)))"
          using cos_one_2pi by (by100 blast)
        hence "\<exists>n::nat. alpha nw = real n * 2 * pi"
        proof (elim disjE exE)
          fix n :: nat assume "alpha nw = real n * 2 * pi" thus ?thesis by (by100 blast)
        next
          fix n :: nat assume "alpha nw = -(real n * 2 * pi)"
          hence "alpha nw \<le> 0" using pi_gt_zero by (by100 simp)
          with halpha_pos show ?thesis by linarith
        qed
        then obtain n :: nat where hn: "alpha nw = real n * 2 * pi" by (by100 blast)
        have "n \<ge> 1"
        proof (rule ccontr)
          assume "\<not> n \<ge> 1" hence "n = 0" by (by100 simp)
          with hn have "alpha nw = 0" by simp
          with halpha_pos show False by linarith
        qed
        from hn have "alpha nw = 2 * real n * pi" by (by100 algebra)
        with \<open>n \<ge> 1\<close> show ?thesis by (by100 blast)
      qed
      then obtain k :: nat where hk: "k \<ge> 1" "alpha nw = 2 * real k * pi" by (by100 blast)
      from hk(2) halpha_lt have "2 * real k * pi < real nw * pi" by simp
      hence "2 * real k < real nw" using pi_gt_zero by (by100 simp)
      hence h2k_lt: "2 * k < nw" by linarith
      \<comment> \<open>For nw \\<le> 4: 2k < nw \\<le> 4, so k < 2, hence k = 1.\<close>
      \<comment> \<open>For nw \\<ge> 5: need C11 to show k < 2.\<close>
      have "k = 1"
      proof (rule ccontr)
        assume "k \<noteq> 1"
        with hk(1) have "k \<ge> 2" by linarith
        hence "2 * k \<ge> 4" by linarith
        \<comment> \<open>For k \\<ge> 2: alpha = 2k\\<pi> \\<ge> 4\\<pi>. But need alpha < nw*\\<pi> with nw \\<ge> 3.
           For nw = 3,4: 4\\<pi> > nw*\\<pi> is false (4\\<pi> > 3\\<pi> = true, 4\\<pi> > 4\\<pi> = false but strict).
           Actually: alpha < nw*pi STRICT. For k=2: alpha = 4\\<pi>. Need 4\\<pi> < nw*\\<pi>, i.e., nw > 4.
           For nw \\<le> 4: 4\\<pi> \\<ge> nw*\\<pi> (4\\<pi> \\<ge> 4\\<pi>), contradicting alpha < nw*\\<pi>.
           For nw = 3: 4\\<pi> > 3\\<pi>. Contradiction. For nw = 4: 4\\<pi> = 4\\<pi>, not strict. But alpha < 4\\<pi> = nw*\\<pi>.
           4\\<pi> < 4\\<pi> is false. So alpha = 4\\<pi> \\<ge> 4\\<pi> = nw*\\<pi>. Contradiction with strict <.
           For nw \\<ge> 5: 4\\<pi> < 5\\<pi> \\<le> nw*\\<pi>. No contradiction from alpha < nw*\\<pi> alone.\<close>
        \<comment> \<open>Use C11 to show this is impossible for nw \\<ge> 5.
           If alpha = 2k\\<pi> \\<ge> 4\\<pi>: the polygon wraps twice around cw.
           C11 (convexity) prevents this: for a convex polygon, winding number = 1.\<close>
        \<comment> \<open>From k \\<ge> 2 and 2k < nw: nw \\<ge> 5.\<close>
        have "nw \<ge> 5" using \<open>2 * k \<ge> 4\<close> h2k_lt by linarith
        \<comment> \<open>PROOF: hregular gives all |z\\_j| = r. For k \\<ge> 2: alpha\\_nw = 2k\\<pi>.
           Since all moduli = r: z\\_m/z\\_0 = cis(alpha\\_m). For the sub-product
           from 0 to some index p: cis(alpha\\_p) = 1 (i.e., z\\_p = z\\_0) when alpha\\_p = 2\\<pi>.
           By discrete IVT: \\<exists>p with alpha\\_p near 2\\<pi>.
           More directly: with all moduli equal and cis(alpha\\_nw) = cis(2k\\<pi>) = 1:
           the product is periodic. There exist j1 < j2 with z\\_{j2} = z\\_{j1}.
           C11 at edge (j1, j1+1), vertex j2: det(z\\_{j2}-z\\_{j1}, z\\_{j1+1}-z\\_{j1}) = det(0, ..) = 0.
           But C11 requires strict < 0. Contradiction.\<close>
        \<comment> \<open>From hregular: all |z\\_j| = r.\<close>
        from hregular obtain r where hr_pos: "r > 0"
            and hr_eq: "\<forall>j<nw. (vxw j - cxw)^2 + (vyw j - cyw)^2 = r^2" by (by100 blast)
        \<comment> \<open>All cmod(zw j) = r.\<close>
        have hmod_eq: "\<forall>j<nw. cmod (zw j) = r"
        proof (intro allI impI)
          fix j assume "j < nw"
          from hr_eq[rule_format, OF this]
          have "(vxw j - cxw)^2 + (vyw j - cyw)^2 = r^2" .
          hence hsum_sq: "(vxw j - cxw)^2 + (vyw j - cyw)^2 = r^2" .
          have "cmod (zw j) = sqrt ((vxw j - cxw)^2 + (vyw j - cyw)^2)"
            unfolding zw_def cmod_def by simp
          also have "\<dots> = sqrt (r^2)" using hsum_sq by simp
          also have "\<dots> = r" using hr_pos by simp
          finally show "cmod (zw j) = r" .
        qed
        \<comment> \<open>With equal moduli: z\\_m/z\\_0 = cis(alpha\\_m) (from polar decomp with r\\_j = 1).\<close>
        \<comment> \<open>There exist j1 < j2 < nw with alpha\\_{j2} - alpha\\_{j1} = 2\\<pi>.
           Then z\\_{j2}/z\\_0 = cis(alpha\\_{j2}) = cis(alpha\\_{j1}+2\\<pi>) = cis(alpha\\_{j1}) = z\\_{j1}/z\\_0.
           So z\\_{j2} = z\\_{j1}, i.e., u\\_{j2} = u\\_{j1}.\<close>
        \<comment> \<open>C11 at edge (j1, Suc j1 mod nw), vertex j2: det = 0. Contradiction.\<close>
        \<comment> \<open>Find the 2\\<pi> crossing index: m0 is the largest with alpha\\_{m0} < 2\\<pi>.\<close>
        \<comment> \<open>With k \\<ge> 2: alpha\\_nw \\<ge> 4\\<pi>. So some index crosses 2\\<pi>.\<close>
        \<comment> \<open>Use C11 at edge (0,1), vertex m0+1 to get contradiction.\<close>
        \<comment> \<open>The cis-difference formula gives the det as a product of three sines,
           which has sign (-)*(+)*(-) = (+), contradicting C11 < 0.\<close>
        \<comment> \<open>Key computation (for circle polygon with equal moduli):
           det(u\\_{m0+1}-u\\_0, u\\_1-u\\_0) = r^2 * 4*sin(alpha\\_{m0+1}/2)*sin(theta\\_0/2)*sin((theta\\_0-alpha\\_{m0+1})/2)
           With alpha\\_{m0+1} \\<in> [2\\<pi>, 3\\<pi>): sin(alpha\\_{m0+1}/2) < 0 and sin((theta\\_0-alpha\\_{m0+1})/2) < 0.
           Product of three sines > 0, but C11 requires < 0. Contradiction.\<close>
        \<comment> \<open>Step 1: find crossing index m0 with alpha\\_{m0} < 2\\<pi> \\<le> alpha\\_{m0+1}.\<close>
        \<comment> \<open>alpha\\_1 = theta\\_0 < \\<pi> < 2\\<pi>. And alpha\\_nw \\<ge> 4\\<pi> > 2\\<pi>. So crossing exists.\<close>
        define m0 where "m0 = (GREATEST m. m < nw \<and> alpha m < 2*pi)"
        \<comment> \<open>For now: sorry the existence and properties of m0.
           Key properties: m0 \\<ge> 2, m0+1 < nw, alpha\\_{m0+1} \\<ge> 2\\<pi>, alpha\\_{m0+1} < 3\\<pi>.\<close>
        \<comment> \<open>Existence: alpha\\_1 = theta\\_0 < \\<pi> < 2\\<pi>. And alpha\\_{nw-1} = 2k\\<pi>-theta\\_{nw-1} > 3\\<pi> (for k \\<ge> 2).
           So there's a crossing of 2\\<pi> between indices 1 and nw-1.\<close>
        have halpha_1_lt: "alpha 1 < 2*pi"
        proof -
          have "alpha 1 = theta 0" unfolding alpha_def by simp
          have h0_lt: "0 < nw" using hnw by linarith
          from htheta_pos[rule_format, OF h0_lt] have "theta 0 < pi" by simp
          hence "theta 0 < 2*pi" using pi_gt_zero by linarith
          thus ?thesis using \<open>alpha 1 = theta 0\<close> by simp
        qed
        have halpha_nw1_ge: "alpha (nw-1) > 2*pi"
        proof -
          have "alpha nw = 2 * real k * pi" using hk(2) .
          have hnw_Suc: "nw = Suc (nw-1)" using hnw by (by100 arith)
          have "alpha nw = alpha (nw-1) + theta (nw-1)" unfolding alpha_def
          proof -
            have "{..<Suc (nw-1)} = insert (nw-1) {..<(nw-1)}" by (rule lessThan_Suc)
            hence "(\<Sum>j<nw. theta j) = theta (nw-1) + (\<Sum>j<nw-1. theta j)"
              using hnw_Suc by simp
            thus "(\<Sum>j<nw. theta j) = (\<Sum>j<nw-1. theta j) + theta (nw-1)"
              by (by100 algebra)
          qed
          hence "alpha (nw-1) = alpha nw - theta (nw-1)" by linarith
          also have "\<dots> = 2*real k*pi - theta (nw-1)" using hk(2) by simp
          finally have h: "alpha (nw-1) = 2*real k*pi - theta (nw-1)" .
          have "theta (nw-1) < pi" using htheta_pos hnw by (by100 auto)
          from \<open>k \<ge> 2\<close> have "2*real k*pi \<ge> 4*pi" using pi_gt_zero by (by100 simp)
          from h have "alpha (nw-1) = 2*real k*pi - theta (nw-1)" .
          with \<open>4*pi \<le> 2*real k*pi\<close> \<open>theta (nw-1) < pi\<close> pi_gt_zero
          show ?thesis by linarith
        qed
        \<comment> \<open>By discrete IVT: \\<exists>m0 with alpha(m0) < 2\\<pi> and alpha(m0+1) \\<ge> 2\\<pi>.\<close>
        \<comment> \<open>Discrete IVT: define m0 via GREATEST, show properties.\<close>
        \<comment> \<open>Actually, just find ANY suitable index, no need for GREATEST.\<close>
        \<comment> \<open>alpha\\_2 = theta\\_0+theta\\_1 < 2\\<pi>. alpha\\_{nw-1} > 2\\<pi>. So \\<exists>m with alpha\\_m < 2\\<pi> \\<le> alpha\\_{m+1}.\<close>
        have hm0_props: "\<exists>m0. m0 \<ge> 2 \<and> m0 + 1 < nw \<and> alpha (m0+1) \<ge> 2*pi \<and> alpha (m0+1) < 3*pi \<and> alpha m0 < 2*pi"
        proof -
          \<comment> \<open>alpha\\_2 < 2\\<pi>: alpha\\_2 = theta\\_0+theta\\_1 < \\<pi>+\\<pi> = 2\\<pi>.\<close>
          have "alpha 2 < 2*pi"
          proof -
            have h0: "0 < nw" using hnw by linarith
            have h1: "1 < nw" using hnw by linarith
            have "alpha 2 = theta 0 + theta 1" unfolding alpha_def
              by (simp add: lessThan_Suc numeral_2_eq_2)
            also have "\<dots> < pi + pi"
              using htheta_pos[rule_format, OF h0] htheta_pos[rule_format, OF h1] by linarith
            finally show ?thesis by simp
          qed
          \<comment> \<open>alpha\\_{nw-1} > 2\\<pi> (proved above as halpha\\_nw1\\_ge).\<close>
          \<comment> \<open>By well-ordering: let m0 = Max {m. m \\<le> nw-2 \\<and> alpha m < 2\\<pi>}.\<close>
          define S where "S = {m. 2 \<le> m \<and> m \<le> nw-2 \<and> alpha m < 2*pi}"
          have "2 \<in> S" using \<open>alpha 2 < 2*pi\<close> \<open>nw \<ge> 5\<close> unfolding S_def by (by100 auto)
          hence "S \<noteq> {}" by (by100 blast)
          have "finite S" unfolding S_def by (by100 auto)
          define m0_val where "m0_val = Max S"
          have hm0_in: "m0_val \<in> S" using Max_in[OF \<open>finite S\<close> \<open>S \<noteq> {}\<close>] unfolding m0_val_def .
          hence hm0_ge: "m0_val \<ge> 2" and hm0_le: "m0_val \<le> nw-2" and hm0_alpha: "alpha m0_val < 2*pi"
            unfolding S_def by (by100 auto)+
          have hm0_max: "\<forall>m \<in> S. m \<le> m0_val" using Max_ge[OF \<open>finite S\<close>] unfolding m0_val_def by (by100 auto)
          \<comment> \<open>alpha(m0\\_val+1) \\<ge> 2\\<pi>: otherwise m0\\_val+1 \\<in> S, contradicting maximality.\<close>
          have "alpha (m0_val+1) \<ge> 2*pi"
          proof (rule ccontr)
            assume "\<not> alpha (m0_val+1) \<ge> 2*pi"
            hence "alpha (m0_val+1) < 2*pi" by linarith
            have "m0_val+1 \<le> nw-2"
            proof (rule ccontr)
              assume "\<not> m0_val+1 \<le> nw-2"
              hence "m0_val+1 > nw-2" by linarith
              hence "m0_val \<ge> nw-2" by linarith
              with hm0_le have "m0_val = nw-2" by linarith
              hence "m0_val+1 = nw-1" using \<open>nw \<ge> 5\<close> by (by100 arith)
              from \<open>alpha (m0_val+1) < 2*pi\<close> have "alpha (nw-1) < 2*pi"
                using \<open>m0_val+1 = nw-1\<close> by simp
              with halpha_nw1_ge show False by linarith
            qed
            have "m0_val+1 \<in> S" using \<open>alpha (m0_val+1) < 2*pi\<close> hm0_ge \<open>m0_val+1 \<le> nw-2\<close>
              unfolding S_def by (by100 auto)
            from hm0_max[rule_format, OF this] show False by linarith
          qed
          \<comment> \<open>alpha(m0\\_val+1) < 3\\<pi>: each step < \\<pi>.\<close>
          have "alpha (m0_val+1) < 3*pi"
          proof -
            have "alpha (m0_val+1) = alpha m0_val + theta m0_val" unfolding alpha_def by simp
            also have "\<dots> < 2*pi + pi"
            proof -
              have "m0_val < nw" using hm0_le \<open>nw \<ge> 5\<close> by linarith
              from htheta_pos[rule_format, OF this] have "theta m0_val < pi" by simp
              with hm0_alpha show ?thesis by linarith
            qed
            also have "\<dots> = 3*pi" by simp
            finally show ?thesis .
          qed
          \<comment> \<open>m0\\_val+1 < nw.\<close>
          have "m0_val+1 < nw" using hm0_le \<open>nw \<ge> 5\<close> by linarith
          \<comment> \<open>Provide all 5 properties as separate conjuncts for the obtain.\<close>
          show ?thesis
            apply (rule exI[of _ m0_val])
            using hm0_ge \<open>alpha (m0_val+1) \<ge> 2*pi\<close> \<open>alpha (m0_val+1) < 3*pi\<close>
              \<open>m0_val+1 < nw\<close> hm0_alpha
            by (by100 auto)
        qed
        then obtain m0_real where hm0_ge2: "m0_real \<ge> 2" and hm0_lt: "m0_real + 1 < nw"
            and halpha_m0_ge: "alpha (m0_real+1) \<ge> 2*pi" and halpha_m0_lt: "alpha (m0_real+1) < 3*pi"
            and halpha_m0_below: "alpha m0_real < 2*pi"
          by (by5000 auto)
        \<comment> \<open>Step 2: C11 at edge (0, 1), vertex m0\\_real+1.\<close>
        have hm0_ne0: "m0_real+1 \<noteq> 0" using hm0_ge2 by (by100 arith)
        have "Suc 0 mod nw = 1" using hnw by (by100 simp)
        have hm0_ne1: "m0_real+1 \<noteq> Suc 0 mod nw" using hm0_ge2 \<open>Suc 0 mod nw = 1\<close> by (by100 arith)
        have h0_lt: "(0::nat) < nw" using hnw by linarith
        have h_C11_inst: "(vxw (m0_real+1)-vxw 0)*(vyw(Suc 0 mod nw)-vyw 0)-(vyw (m0_real+1)-vyw 0)*(vxw(Suc 0 mod nw)-vxw 0) < 0"
          using hC11[rule_format, OF h0_lt hm0_lt hm0_ne0 hm0_ne1] .
        \<comment> \<open>Step 3: Compute det(u\\_{m0+1}-u\\_0, u\\_1-u\\_0) using the equal-modulus property.
           All u\\_j = cw + r*cis(phi\\_j) where phi\\_j = Arg(z\\_0)+alpha\\_j.
           det = r^2 * 4*sin(alpha\\_{m0+1}/2)*sin(theta\\_0/2)*sin((theta\\_0-alpha\\_{m0+1})/2).\<close>
        \<comment> \<open>For alpha\\_{m0+1} \\<in> [2\\<pi>, 3\\<pi>):
           sin(alpha\\_{m0+1}/2) \\<in> sin([\\<pi>, 3\\<pi>/2)): \\<le> 0 (actually < 0 for > \\<pi>).
           sin(theta\\_0/2) > 0.
           sin((theta\\_0-alpha\\_{m0+1})/2): (theta\\_0-alpha\\_{m0+1})/2 \\<in> ((-3\\<pi>+theta\\_0)/2, (theta\\_0-2\\<pi>)/2).
             = ((-3\\<pi>+theta\\_0)/2, (theta\\_0-2\\<pi>)/2) \\<subset> (-3\\<pi>/2, 0).
             For the range (-\\<pi>, 0): sin < 0.
           Product: (\\<le>0)*(>0)*(\\<le>0) \\<ge> 0. But C11 requires < 0. Contradiction.\<close>
        \<comment> \<open>Formal computation using the cis-difference formula.\<close>
        \<comment> \<open>TWO-CASE proof using crossing index m0\\_real.\<close>
        \<comment> \<open>Case 1: alpha(m0+1) > 2\\<pi>+theta\\_0: hfan\\_det with m0,m0+1 gives contradiction.
           Case 2: alpha(m0+1) \\<le> 2\\<pi>+theta\\_0: C11 at edge (0,1) for vertex m0+1 gives det \\<ge> 0.
           Both lead to contradiction.\<close>
        \<comment> \<open>For now: sorry the two-case sign computation. The math is verified;
           formalization needs the cis-difference formula for circle polygons.
           Case 1: the three-sine product from hfan\\_det has signs (+)(-)(+) < 0.
           Case 2: det = r^2*2*sin(theta\\_0/2)*(cos((theta\\_0-2*delta)/2)-cos(theta\\_0/2)) \\<ge> 0.\<close>
        \<comment> \<open>The C11 det in centroid coords:\<close>
        define alpha_cross where "alpha_cross = alpha (m0_real + 1)"
        define delta where "delta = alpha_cross - 2*pi"
        have hdelta_ge: "delta \<ge> 0" using halpha_m0_ge unfolding delta_def alpha_cross_def by linarith
        have hdelta_lt: "delta < pi" using halpha_m0_lt unfolding delta_def alpha_cross_def by linarith
        define theta0 where "theta0 = theta 0"
        have htheta0_pos: "theta0 > 0" and htheta0_lt: "theta0 < pi"
          using htheta_pos hnw unfolding theta0_def by (by100 auto)+
        \<comment> \<open>The C11 det = (cross product formula involving vxw, vyw).
           With equal moduli: det = r^2 * (sin(theta0-delta) + sin(delta) - sin(theta0)).
           (Using periodicity: sin(alpha\\_cross) = sin(delta), sin(theta0-alpha\\_cross) = sin(theta0-delta).)
           This expression \\<ge> 0 when delta \\<le> theta0, contradicting C11 < 0.\<close>
        \<comment> \<open>For now: sorry the det computation. Needs expressing det in terms of
           sin(alpha\\_cross), sin(theta0), etc. using the equal-modulus formula.\<close>
        \<comment> \<open>Key identity: the C11 det equals r^2*(sin(theta0-delta)+sin(delta)-sin(theta0)).
           Proof: u\\_j = cw + r*cis(Arg(z\\_0)+alpha\\_j). Differences factor out cis(Arg(z\\_0)).
           Then conj(cis(alpha\\_cross)-1)*(cis(theta0)-1) gives the formula via cis periodicity.\<close>
        have hSuc0: "Suc 0 mod nw = 1" using hnw by (by100 simp)
        \<comment> \<open>Circle polygon infrastructure: zw j = cis(alpha j) * zw 0 for j < nw.\<close>
        have hz0_ne: "zw 0 \<noteq> 0" using hzw_ne hnw by (by100 simp)
        \<comment> \<open>Each ratio zw(j+1)/zw(j) = cis(theta j) since equal moduli.\<close>
        have hratio_cis: "\<forall>k. k < nw \<longrightarrow> zw (Suc k mod nw) / zw k = cis (theta k)"
        proof (intro allI impI)
          fix k assume hk: "k < nw"
          have hk_ne: "zw k \<noteq> 0" using hzw_ne hk by (by100 auto)
          have hSk: "Suc k mod nw < nw" using hnw by (by100 simp)
          have "cmod (zw (Suc k mod nw) / zw k) = 1"
          proof -
            have "cmod (zw (Suc k mod nw)) = r" using hmod_eq[rule_format, OF hSk] .
            moreover have "cmod (zw k) = r" using hmod_eq[rule_format, OF hk] .
            ultimately show ?thesis using hk_ne hr_pos norm_divide[of "zw (Suc k mod nw)" "zw k"]
              by (by100 simp)
          qed
          moreover have "Arg (zw (Suc k mod nw) / zw k) = theta k"
            unfolding theta_def by (by100 simp)
          moreover have "zw (Suc k mod nw) / zw k \<noteq> 0" using hk_ne hzw_ne hSk
            by (by100 auto)
          ultimately show "zw (Suc k mod nw) / zw k = cis (theta k)"
            using rcis_cmod_Arg[of "zw (Suc k mod nw) / zw k"]
            unfolding rcis_def by (by100 simp)
        qed
        \<comment> \<open>Product of cis = cis of sum: \\<Prod>k<j. cis(theta k) = cis(alpha j).\<close>
        have hprod_cis: "\<forall>j. (\<Prod>k<j. cis (theta k)) = cis (alpha j)"
        proof
          fix j show "(\<Prod>k<j. cis (theta k)) = cis (alpha j)"
          proof (induct j)
            case 0 show ?case unfolding alpha_def by (by100 simp)
          next
            case (Suc j)
            have "{..<Suc j} = insert j {..<j}" by (rule lessThan_Suc)
            hence "(\<Prod>k<Suc j. cis (theta k)) = cis (theta j) * (\<Prod>k<j. cis (theta k))"
              by (by100 simp)
            also have "\<dots> = cis (theta j) * cis (alpha j)" using Suc by (by100 simp)
            also have "\<dots> = cis (theta j + alpha j)" using cis_mult[of "theta j" "alpha j"] by (by100 simp)
            also have "\<dots> = cis (alpha (Suc j))"
            proof -
              have "alpha (Suc j) = (\<Sum>k<Suc j. theta k)" unfolding alpha_def by (by100 simp)
              also have "\<dots> = theta j + (\<Sum>k<j. theta k)"
                using lessThan_Suc by (by100 simp)
              also have "\<dots> = theta j + alpha j" unfolding alpha_def by (by100 simp)
              finally show ?thesis by (by100 simp)
            qed
            finally show ?case .
          qed
        qed
        \<comment> \<open>Combine: zw j = cis(alpha j) * zw 0.\<close>
        have hzw_cis: "\<forall>j. j < nw \<longrightarrow> zw j = cis (alpha j) * zw 0"
        proof (intro allI impI)
          fix j assume hj: "j < nw"
          from hpartial_telescope[rule_format, OF hj]
          have "zw j = (\<Prod>k<j. zw (Suc k mod nw) / zw k) * zw 0" .
          also have "(\<Prod>k<j. zw (Suc k mod nw) / zw k) = (\<Prod>k<j. cis (theta k))"
          proof (rule prod.cong, simp)
            fix k assume "k \<in> {..<j}"
            hence "k < nw" using hj by (by100 auto)
            from hratio_cis[rule_format, OF this] show "zw (Suc k mod nw) / zw k = cis (theta k)" .
          qed
          also have "\<dots> = cis (alpha j)" using hprod_cis by (by100 simp)
          finally show "zw j = cis (alpha j) * zw 0" .
        qed
        \<comment> \<open>The C11 det in terms of cc values.\<close>
        have hdet_formula: "(vxw (m0_real+1)-vxw 0)*(vyw 1-vyw 0)-(vyw (m0_real+1)-vyw 0)*(vxw 1-vxw 0) =
            r^2 * (sin(theta0-delta) + sin delta - sin theta0)"
        proof -
          \<comment> \<open>Step A: det = Im(cnj(zw(m0+1)-zw 0)*(zw 1-zw 0)).\<close>
          have hdet_Im: "(vxw (m0_real+1)-vxw 0)*(vyw 1-vyw 0)-(vyw (m0_real+1)-vyw 0)*(vxw 1-vxw 0) =
            Im (cnj (zw (m0_real+1) - zw 0) * (zw 1 - zw 0))"
          proof -
            \<comment> \<open>Re/Im of differences = coordinate differences.\<close>
            have hRe_diff_m: "Re (zw (m0_real+1) - zw 0) = vxw (m0_real+1) - vxw 0"
              unfolding zw_def by (by100 simp)
            have hIm_diff_m: "Im (zw (m0_real+1) - zw 0) = vyw (m0_real+1) - vyw 0"
              unfolding zw_def by (by100 simp)
            have hRe_diff_1: "Re (zw 1 - zw 0) = vxw 1 - vxw 0"
              unfolding zw_def by (by100 simp)
            have hIm_diff_1: "Im (zw 1 - zw 0) = vyw 1 - vyw 0"
              unfolding zw_def by (by100 simp)
            \<comment> \<open>Im(cnj(z)*w) = Re(z)*Im(w) - Im(z)*Re(w).\<close>
            define z1 where "z1 = zw (m0_real+1) - zw 0"
            define w1 where "w1 = zw 1 - zw 0"
            have "Im (cnj z1 * w1) = Re (cnj z1) * Im w1 + Im (cnj z1) * Re w1"
              by (by100 simp)
            also have "\<dots> = Re z1 * Im w1 - Im z1 * Re w1"
              by (by100 simp)
            finally have "Im (cnj z1 * w1) = Re z1 * Im w1 - Im z1 * Re w1" .
            thus ?thesis unfolding z1_def w1_def
              using hRe_diff_m hIm_diff_m hRe_diff_1 hIm_diff_1 by (by100 algebra)
          qed
          \<comment> \<open>Step B: Substitute zw j = cis(alpha j)*zw 0.\<close>
          have hm01_lt: "m0_real+1 < nw" using hm0_lt .
          have h1_lt: "(1::nat) < nw" using hnw by linarith
          have hzw_m: "zw (m0_real+1) = cis alpha_cross * zw 0"
            using hzw_cis[rule_format, OF hm01_lt] unfolding alpha_cross_def by (by100 simp)
          have halpha1: "alpha 1 = theta 0"
            unfolding alpha_def by (by100 simp)
          have hzw_1: "zw 1 = cis theta0 * zw 0"
            using hzw_cis[rule_format, OF h1_lt] halpha1 unfolding theta0_def by (by100 simp)
          \<comment> \<open>Differences.\<close>
          have hdiff_m: "zw (m0_real+1) - zw 0 = (cis alpha_cross - 1) * zw 0"
            using hzw_m by (by100 algebra)
          have hdiff_1: "zw 1 - zw 0 = (cis theta0 - 1) * zw 0"
            using hzw_1 by (by100 algebra)
          \<comment> \<open>Step C: cnj(d1)*d2 = r^2*(cis(-alpha\\_cross)-1)*(cis(theta0)-1).\<close>
          have hprod_val: "cnj (zw (m0_real+1) - zw 0) * (zw 1 - zw 0) =
            of_real (r^2) * ((cis (-alpha_cross) - 1) * (cis theta0 - 1))"
          proof -
            \<comment> \<open>Substitute differences.\<close>
            have s1: "cnj (zw (m0_real+1) - zw 0) * (zw 1 - zw 0) =
              cnj ((cis alpha_cross - 1) * zw 0) * ((cis theta0 - 1) * zw 0)"
              using hdiff_m hdiff_1 by (by100 simp)
            \<comment> \<open>Distribute cnj.\<close>
            have s2: "cnj ((cis alpha_cross - 1) * zw 0) = (cis (-alpha_cross) - 1) * cnj (zw 0)"
              using cis_cnj[of alpha_cross] by (by100 simp)
            \<comment> \<open>Reorder to separate cnj(z0)*z0.\<close>
            have s3: "(cis (-alpha_cross) - 1) * cnj (zw 0) * ((cis theta0 - 1) * zw 0) =
              (cis (-alpha_cross) - 1) * (cis theta0 - 1) * (cnj (zw 0) * zw 0)"
              by (by100 algebra)
            \<comment> \<open>cnj(z0)*z0 = |z0|^2 = r^2.\<close>
            have "cmod (zw 0) = r" using hmod_eq hnw by (by100 auto)
            hence hmod_sq: "(cmod (zw 0))^2 = r^2" by (by100 simp)
            have s4: "cnj (zw 0) * zw 0 = of_real (r^2)"
            proof -
              have "cnj (zw 0) * zw 0 = zw 0 * cnj (zw 0)" by (by100 algebra)
              also have "\<dots> = of_real ((cmod (zw 0))^2)"
                using complex_norm_square[of "zw 0"] by (by100 simp)
              also have "\<dots> = of_real (r^2)" using hmod_sq by (by100 simp)
              finally show ?thesis .
            qed
            \<comment> \<open>Combine.\<close>
            from s1 s2 have "cnj (zw (m0_real+1) - zw 0) * (zw 1 - zw 0) =
              (cis (-alpha_cross) - 1) * cnj (zw 0) * ((cis theta0 - 1) * zw 0)"
              by (by100 simp)
            also from s3 have "\<dots> = (cis (-alpha_cross) - 1) * (cis theta0 - 1) * (cnj (zw 0) * zw 0)"
              by (by100 simp)
            also from s4 have "\<dots> = (cis (-alpha_cross) - 1) * (cis theta0 - 1) * of_real (r^2)"
              by (by100 simp)
            also have "\<dots> = of_real (r^2) * ((cis (-alpha_cross) - 1) * (cis theta0 - 1))"
              by (by100 algebra)
            finally show ?thesis .
          qed
          \<comment> \<open>Step D: Im of the product.\<close>
          have hIm_expand: "Im ((cis (-alpha_cross) - 1) * (cis theta0 - 1)) =
            sin (theta0 - alpha_cross) + sin alpha_cross - sin theta0"
          proof -
            have hexpand: "(cis (-alpha_cross) - 1) * (cis theta0 - 1) =
              cis (theta0 - alpha_cross) - cis (-alpha_cross) - cis theta0 + 1"
            proof -
              have heq_arg: "-alpha_cross + theta0 = theta0 - alpha_cross" by (by100 linarith)
              have hcis_prod: "cis (-alpha_cross) * cis theta0 = cis (theta0 - alpha_cross)"
                using cis_mult[of "-alpha_cross" theta0] heq_arg by (by100 simp)
              \<comment> \<open>Expand: (a-1)*(b-1) = a*b - a - b + 1.\<close>
              have "(cis (-alpha_cross) - 1) * (cis theta0 - 1) =
                cis (-alpha_cross) * cis theta0 - cis (-alpha_cross) - cis theta0 + 1"
                by (by100 algebra)
              thus ?thesis using hcis_prod by (by100 simp)
            qed
            have "Im ((cis (-alpha_cross) - 1) * (cis theta0 - 1)) =
              Im (cis (theta0 - alpha_cross) - cis (-alpha_cross) - cis theta0 + 1)"
              using hexpand by (by100 simp)
            also have "\<dots> = sin (theta0 - alpha_cross) - sin (-alpha_cross) - sin theta0"
              by (by100 simp)
            also have "\<dots> = sin (theta0 - alpha_cross) + sin alpha_cross - sin theta0"
              by (by100 simp)
            finally show ?thesis .
          qed
          \<comment> \<open>Step E: Sin periodicity: alpha\\_cross = 2\\<pi>+\\<delta>.\<close>
          have hsin_period1: "sin (theta0 - alpha_cross) = sin (theta0 - delta)"
          proof -
            have "alpha_cross = delta + 2*pi" unfolding delta_def by (by100 algebra)
            hence "theta0 - alpha_cross = (theta0 - delta) + (-(2*pi))" by (by100 linarith)
            hence h1: "sin(theta0 - alpha_cross) = sin((theta0-delta) + (-(2*pi)))" by (by100 metis)
            have h2: "sin((theta0-delta) + (-(2*pi))) = sin(theta0-delta)"
              using sin_periodic[of "(theta0-delta) - 2*pi"] by (by100 simp)
            from h1 h2 show ?thesis by (by100 simp)
          qed
          have hsin_period2: "sin alpha_cross = sin delta"
          proof -
            have "alpha_cross = delta + 2*pi" unfolding delta_def by (by100 algebra)
            thus ?thesis using sin_periodic[of delta] by (by100 simp)
          qed
          \<comment> \<open>Combine.\<close>
          have "Im (cnj (zw (m0_real+1) - zw 0) * (zw 1 - zw 0)) =
            r^2 * (sin (theta0 - delta) + sin delta - sin theta0)"
          proof -
            from hprod_val have "Im (cnj (zw (m0_real+1) - zw 0) * (zw 1 - zw 0)) =
              r^2 * Im ((cis (-alpha_cross) - 1) * (cis theta0 - 1))"
              by (by100 simp)
            also have "\<dots> = r^2 * (sin (theta0 - alpha_cross) + sin alpha_cross - sin theta0)"
              using hIm_expand by (by100 simp)
            also have "\<dots> = r^2 * (sin (theta0 - delta) + sin delta - sin theta0)"
              using hsin_period1 hsin_period2 by (by100 simp)
            finally show ?thesis .
          qed
          with hdet_Im show ?thesis by (by100 simp)
        qed
        \<comment> \<open>From h\\_C11\\_inst: the LHS < 0.\<close>
        from h_C11_inst hSuc0
        have hdet_neg: "r^2 * (sin(theta0-delta) + sin delta - sin theta0) < 0"
          using hdet_formula by simp
        \<comment> \<open>Case analysis on delta vs theta0.\<close>
        show False
        proof (cases "delta \<le> theta0")
          case True
          \<comment> \<open>CASE 1: delta \\<le> theta0. Show sin(theta0-delta)+sin(delta)-sin(theta0) \\<ge> 0.\<close>
          have "sin(theta0-delta) + sin delta - sin theta0 \<ge> 0"
          proof -
            \<comment> \<open>sin(A-B)+sin(B) = 2*sin(A/2)*cos((A-2B)/2). So:
               sin(theta0-delta)+sin(delta) = 2*sin(theta0/2)*cos((theta0-2*delta)/2).
               And sin(theta0) = 2*sin(theta0/2)*cos(theta0/2).
               Difference = 2*sin(theta0/2)*(cos((theta0-2*delta)/2)-cos(theta0/2)).
               For delta \\<in> [0, theta0]: |(theta0-2*delta)/2| \\<le> theta0/2.
               cos is even and decreasing on [0,\\<pi>]: cos(|(theta0-2*delta)/2|) \\<ge> cos(theta0/2).\<close>
            \<comment> \<open>Identity: sin(A-B)+sin(B)-sin(A) = 4*sin(A/2)*sin(B/2)*sin((A-B)/2).
               Proof via half-angle substitutions.\<close>
            have h_expand: "sin(theta0-delta) + sin delta - sin theta0 =
              sin theta0 * (cos delta - 1) + sin delta * (1 - cos theta0)"
              using sin_diff[of theta0 delta] by (by100 algebra)
            have hcos_half_t: "1 - cos theta0 = 2 * (sin(theta0/2))^2"
            proof -
              from cos_double_sin[of "theta0/2"] have "cos(2*(theta0/2)) = 1 - 2*(sin(theta0/2))^2" .
              hence "cos theta0 = 1 - 2*(sin(theta0/2))^2" by (by100 simp)
              thus ?thesis by linarith
            qed
            have hcos_half_d: "cos delta - 1 = -(2 * (sin(delta/2))^2)"
            proof -
              from cos_double_sin[of "delta/2"] have "cos(2*(delta/2)) = 1 - 2*(sin(delta/2))^2" .
              hence "cos delta = 1 - 2*(sin(delta/2))^2" by (by100 simp)
              thus ?thesis by linarith
            qed
            have h2: "sin(theta0-delta) + sin delta - sin theta0 =
              2 * (sin delta * (sin(theta0/2))^2 - sin theta0 * (sin(delta/2))^2)"
              using h_expand hcos_half_t hcos_half_d by (by100 algebra)
            have hsin_half_t: "sin theta0 = 2 * sin(theta0/2) * cos(theta0/2)"
            proof -
              from sin_double[of "theta0/2"] have "sin(2*(theta0/2)) = 2 * sin(theta0/2) * cos(theta0/2)" .
              thus ?thesis by (by100 simp)
            qed
            have hsin_half_d: "sin delta = 2 * sin(delta/2) * cos(delta/2)"
            proof -
              from sin_double[of "delta/2"] have "sin(2*(delta/2)) = 2 * sin(delta/2) * cos(delta/2)" .
              thus ?thesis by (by100 simp)
            qed
            have h3: "sin(theta0-delta) + sin delta - sin theta0 =
              4 * sin(theta0/2) * sin(delta/2) * (cos(delta/2) * sin(theta0/2) - cos(theta0/2) * sin(delta/2))"
              using h2 hsin_half_t hsin_half_d by (by100 algebra)
            have h_sin_diff: "cos(delta/2) * sin(theta0/2) - cos(theta0/2) * sin(delta/2) = sin((theta0 - delta) / 2)"
            proof -
              have heq: "theta0/2 - delta/2 = (theta0 - delta) / 2" by (by100 simp)
              have "sin((theta0 - delta)/2) = sin(theta0/2) * cos(delta/2) - cos(theta0/2) * sin(delta/2)"
                using sin_diff[of "theta0/2" "delta/2"] heq by (by100 simp)
              also have "\<dots> = cos(delta/2) * sin(theta0/2) - cos(theta0/2) * sin(delta/2)"
                by (by100 algebra)
              finally show ?thesis by (by100 simp)
            qed
            from h3 h_sin_diff
            have h_product: "sin(theta0-delta) + sin delta - sin theta0 =
              4 * sin(theta0/2) * sin(delta/2) * sin((theta0 - delta) / 2)"
              by (by100 algebra)
            \<comment> \<open>All three sine factors are non-negative.\<close>
            have "sin(theta0/2) > 0"
              using sin_gt_zero[of "theta0/2"] htheta0_pos htheta0_lt by (by100 auto)
            have "sin(delta/2) \<ge> 0"
              using sin_ge_zero[of "delta/2"] hdelta_ge hdelta_lt by (by100 auto)
            have "sin((theta0 - delta) / 2) \<ge> 0"
            proof (rule sin_ge_zero)
              from True show "0 \<le> (theta0 - delta) / 2" by simp
              have "theta0 - delta \<le> 2 * pi" using htheta0_lt hdelta_ge pi_gt_zero by linarith
              thus "(theta0 - delta) / 2 \<le> pi" by simp
            qed
            have "sin(theta0/2) * sin(delta/2) \<ge> 0"
              using \<open>sin(theta0/2) > 0\<close> \<open>sin(delta/2) \<ge> 0\<close> by (by100 auto)
            hence "sin(theta0/2) * sin(delta/2) * sin((theta0 - delta) / 2) \<ge> 0"
              using \<open>sin((theta0 - delta) / 2) \<ge> 0\<close> by (by100 auto)
            hence "4 * sin(theta0/2) * sin(delta/2) * sin((theta0 - delta) / 2) \<ge> 0"
              by (by100 linarith)
            with h_product show ?thesis by linarith
          qed
          hence "r^2 * (sin(theta0-delta) + sin delta - sin theta0) \<ge> 0"
            using hr_pos by (by100 simp)
          with hdet_neg show False by linarith
        next
          case False
          hence "delta > theta0" by linarith
          \<comment> \<open>CASE 2: delta > theta0. Use hfan\\_det at m=m0\\_real, n=m0\\_real+1.\<close>
          \<comment> \<open>The hfan\\_det product = r^2*4*sin(A)*sin(B)*sin(C) where:
             A = (alpha\\_m0 - theta0)/2 > 0 (first loop, sin > 0)
             B = (alpha\\_cross - theta0)/2 > \\<pi> (second loop, sin < 0)
             C = theta\\_{m0}/2 > 0 (sin > 0)
             Product < 0, contradicting hfan\\_det > 0.\<close>
          have hm0_ge2_nat: "2 \<le> m0_real" using hm0_ge2 .
          have hm0_lt_nat: "m0_real < m0_real + 1" by (by100 arith)
          have hm01_lt: "m0_real + 1 < nw" using hm0_lt .
          from hfan_det[rule_format, OF hm0_ge2_nat hm0_lt_nat hm01_lt]
          have hfan_pos: "(vxw m0_real - vxw 1) * (vyw (m0_real+1) - vyw 1) -
              (vyw m0_real - vyw 1) * (vxw (m0_real+1) - vxw 1) > 0" .
          \<comment> \<open>This equals r^2*4*sin((alpha\\_m0-theta0)/2)*sin((alpha\\_cross-theta0)/2)*sin(theta\\_{m0}/2).\<close>
          have hfan_formula: "(vxw m0_real - vxw 1) * (vyw (m0_real+1) - vyw 1) -
              (vyw m0_real - vyw 1) * (vxw (m0_real+1) - vxw 1) =
              r^2 * 4 * sin((alpha m0_real - theta0)/2) * sin((alpha_cross - theta0)/2) * sin(theta (m0_real) / 2)"
          proof -
            \<comment> \<open>Step A: det = Im(cnj(zw m0-zw 1)*(zw(m0+1)-zw 1)).\<close>
            define z1_m where "z1_m = zw m0_real - zw 1"
            define z1_c where "z1_c = zw (m0_real+1) - zw 1"
            have hdet_Im2: "(vxw m0_real - vxw 1) * (vyw (m0_real+1) - vyw 1) -
                (vyw m0_real - vyw 1) * (vxw (m0_real+1) - vxw 1) = Im (cnj z1_m * z1_c)"
            proof -
              have "Re z1_m = vxw m0_real - vxw 1" unfolding z1_m_def zw_def by (by100 simp)
              have "Im z1_m = vyw m0_real - vyw 1" unfolding z1_m_def zw_def by (by100 simp)
              have "Re z1_c = vxw (m0_real+1) - vxw 1" unfolding z1_c_def zw_def by (by100 simp)
              have "Im z1_c = vyw (m0_real+1) - vyw 1" unfolding z1_c_def zw_def by (by100 simp)
              have "Im (cnj z1_m * z1_c) = Re z1_m * Im z1_c - Im z1_m * Re z1_c"
                by (by100 simp)
              thus ?thesis using \<open>Re z1_m = _\<close> \<open>Im z1_m = _\<close> \<open>Re z1_c = _\<close> \<open>Im z1_c = _\<close>
                by (by100 algebra)
            qed
            \<comment> \<open>Step B: Substitute zw j = cis(alpha j)*zw 0.\<close>
            have hm0_lt_nw: "m0_real < nw" using hm0_lt by linarith
            have hzw_m0: "zw m0_real = cis (alpha m0_real) * zw 0"
              using hzw_cis[rule_format, OF hm0_lt_nw] .
            have hzw_m01: "zw (m0_real+1) = cis alpha_cross * zw 0"
              using hzw_cis[rule_format, OF hm01_lt] unfolding alpha_cross_def by (by100 simp)
            have h1_lt: "(1::nat) < nw" using hnw by linarith
            have halpha1_eq: "alpha 1 = theta 0" unfolding alpha_def by (by100 simp)
            have hzw_1: "zw 1 = cis theta0 * zw 0"
              using hzw_cis[rule_format, OF h1_lt] halpha1_eq unfolding theta0_def by (by100 simp)
            \<comment> \<open>Differences from vertex 1.\<close>
            have hdm: "z1_m = (cis (alpha m0_real) - cis theta0) * zw 0"
              unfolding z1_m_def using hzw_m0 hzw_1 by (by100 algebra)
            have hdc: "z1_c = (cis alpha_cross - cis theta0) * zw 0"
              unfolding z1_c_def using hzw_m01 hzw_1 by (by100 algebra)
            \<comment> \<open>Step C: Factor out |zw 0|^2 = r^2.\<close>
            have "cmod (zw 0) = r" using hmod_eq hnw by (by100 auto)
            hence hmod_sq2: "(cmod (zw 0))^2 = r^2" by (by100 simp)
            have s4_2: "cnj (zw 0) * zw 0 = of_real (r^2)"
            proof -
              have "cnj (zw 0) * zw 0 = zw 0 * cnj (zw 0)" by (by100 algebra)
              also have "\<dots> = of_real ((cmod (zw 0))^2)"
                using complex_norm_square[of "zw 0"] by (by100 simp)
              also have "\<dots> = of_real (r^2)" using hmod_sq2 by (by100 simp)
              finally show ?thesis .
            qed
            define A where "A = alpha m0_real"
            define B where "B = alpha_cross"
            define T where "T = theta0"
            have "cnj z1_m * z1_c = cnj ((cis A - cis T) * zw 0) * ((cis B - cis T) * zw 0)"
              using hdm hdc unfolding A_def B_def T_def by (by100 simp)
            also have "\<dots> = (cnj (cis A - cis T) * cnj (zw 0)) * ((cis B - cis T) * zw 0)"
              by (by100 simp)
            also have "\<dots> = (cnj (cis A - cis T) * (cis B - cis T)) * (cnj (zw 0) * zw 0)"
              by (by100 algebra)
            also have "\<dots> = (cnj (cis A - cis T) * (cis B - cis T)) * of_real (r^2)"
              using s4_2 by (by100 simp)
            also have "\<dots> = of_real (r^2) * (cnj (cis A - cis T) * (cis B - cis T))"
              by (by100 algebra)
            finally have hprod2: "cnj z1_m * z1_c = of_real (r^2) * (cnj (cis A - cis T) * (cis B - cis T))" .
            \<comment> \<open>Step D: cnj(cis A - cis T)*(cis B - cis T) expanded.\<close>
            have "cnj (cis A - cis T) = cis (-A) - cis (-T)"
              using cis_cnj[of A] cis_cnj[of T] by (by100 simp)
            hence hprod_expand: "cnj (cis A - cis T) * (cis B - cis T) =
              (cis (-A) - cis (-T)) * (cis B - cis T)"
              by (by100 simp)
            have hcis1: "cis (-A) * cis B = cis (B - A)"
            proof -
              have "-A + B = B - A" by (by100 linarith)
              thus ?thesis using cis_mult[of "-A" B] by (by100 simp)
            qed
            have hcis2: "cis (-A) * cis T = cis (T - A)"
            proof -
              have "-A + T = T - A" by (by100 linarith)
              thus ?thesis using cis_mult[of "-A" T] by (by100 simp)
            qed
            have hcis3: "cis (-T) * cis B = cis (B - T)"
            proof -
              have "-T + B = B - T" by (by100 linarith)
              thus ?thesis using cis_mult[of "-T" B] by (by100 simp)
            qed
            have hcis4: "cis (-T) * cis T = cis 0"
            proof -
              have "-T + T = (0::real)" by (by100 linarith)
              thus ?thesis using cis_mult[of "-T" T] by (by100 simp)
            qed
            have hprod_cis2: "(cis (-A) - cis (-T)) * (cis B - cis T) =
              cis (B-A) - cis (T-A) - cis (B-T) + cis 0"
            proof -
              have "(cis (-A) - cis (-T)) * (cis B - cis T) =
                cis (-A)*cis B - cis (-A)*cis T - cis (-T)*cis B + cis (-T)*cis T"
                by (by100 algebra)
              thus ?thesis using hcis1 hcis2 hcis3 hcis4 by (by100 simp)
            qed
            \<comment> \<open>Step E: Take Im.\<close>
            have "Im (cis (B-A) - cis (T-A) - cis (B-T) + cis 0) =
              sin(B-A) - sin(T-A) - sin(B-T)"
              by (by100 simp)
            \<comment> \<open>Step F: B-A = theta(m0), T-A = theta0-alpha(m0), B-T = alpha\\_cross-theta0.\<close>
            have hBA: "B - A = theta (m0_real)"
            proof -
              have "B - A = alpha_cross - alpha m0_real" unfolding B_def A_def by (by100 simp)
              also have "\<dots> = alpha (m0_real+1) - alpha m0_real" unfolding alpha_cross_def by (by100 simp)
              also have "\<dots> = theta m0_real" unfolding alpha_def by (by100 simp)
              finally show ?thesis .
            qed
            have hTA: "T - A = theta0 - alpha m0_real" unfolding T_def A_def by (by100 simp)
            have hBT: "B - T = alpha_cross - theta0" unfolding B_def T_def by (by100 simp)
            \<comment> \<open>So Im = sin(theta m0) + sin(alpha m0 - theta0) - sin(alpha\\_cross-theta0).\<close>
            \<comment> \<open>= sin(A'-B')+sin(B')-sin(A') with A'=alpha\\_cross-theta0, B'=alpha m0-theta0.\<close>
            \<comment> \<open>= 4*sin(A'/2)*sin(B'/2)*sin((A'-B')/2) by the identity.\<close>
            have hsin_neg: "sin(theta0 - alpha m0_real) = -sin(alpha m0_real - theta0)"
              using sin_minus[of "alpha m0_real - theta0"] by (by100 simp)
            have hIm_val: "sin(B-A) - sin(T-A) - sin(B-T) =
              sin(theta m0_real) + sin(alpha m0_real - theta0) - sin(alpha_cross - theta0)"
              using hBA hTA hBT hsin_neg by (by100 simp)
            \<comment> \<open>Apply the 4*sin*sin*sin identity: sin(X-Y)+sin(Y)-sin(X) = 4*sin(X/2)*sin(Y/2)*sin((X-Y)/2).\<close>
            define X where "X = alpha_cross - theta0"
            define Y where "Y = alpha m0_real - theta0"
            have hXY: "X - Y = theta (m0_real)" using hBA unfolding X_def Y_def B_def A_def T_def
              by (by100 simp)
            have h_identity: "sin(X-Y) + sin Y - sin X =
              4 * sin(X/2) * sin(Y/2) * sin((X-Y)/2)"
            proof -
              \<comment> \<open>Same half-angle identity as before.\<close>
              have h_ex: "sin(X-Y) + sin Y - sin X =
                sin X * (cos Y - 1) + sin Y * (1 - cos X)"
                using sin_diff[of X Y] by (by100 algebra)
              have hc1: "cos X = 1 - 2 * (sin(X/2))^2"
              proof -
                from cos_double_sin[of "X/2"] have "cos(2*(X/2)) = 1 - 2*(sin(X/2))^2" .
                thus ?thesis by (by100 simp)
              qed
              have hc2: "cos Y = 1 - 2 * (sin(Y/2))^2"
              proof -
                from cos_double_sin[of "Y/2"] have "cos(2*(Y/2)) = 1 - 2*(sin(Y/2))^2" .
                thus ?thesis by (by100 simp)
              qed
              have hs1: "sin X = 2 * sin(X/2) * cos(X/2)"
              proof -
                from sin_double[of "X/2"] have "sin(2*(X/2)) = 2*sin(X/2)*cos(X/2)" .
                thus ?thesis by (by100 simp)
              qed
              have hs2: "sin Y = 2 * sin(Y/2) * cos(Y/2)"
              proof -
                from sin_double[of "Y/2"] have "sin(2*(Y/2)) = 2*sin(Y/2)*cos(Y/2)" .
                thus ?thesis by (by100 simp)
              qed
              have h_expand2: "sin(X-Y) + sin Y - sin X =
                4 * sin(X/2) * sin(Y/2) * (cos(Y/2) * sin(X/2) - cos(X/2) * sin(Y/2))"
                using h_ex hc1 hc2 hs1 hs2 by (by100 algebra)
              have h_sin_XY: "cos(Y/2) * sin(X/2) - cos(X/2) * sin(Y/2) = sin((X-Y)/2)"
              proof -
                have heq2: "X/2 - Y/2 = (X-Y)/2" by (by100 simp)
                have "sin((X-Y)/2) = sin(X/2)*cos(Y/2) - cos(X/2)*sin(Y/2)"
                  using sin_diff[of "X/2" "Y/2"] heq2 by (by100 simp)
                also have "\<dots> = cos(Y/2)*sin(X/2) - cos(X/2)*sin(Y/2)"
                  by (by100 algebra)
                finally show ?thesis by (by100 simp)
              qed
              from h_expand2 h_sin_XY show ?thesis by (by100 algebra)
            qed
            have "sin(theta m0_real) + sin(alpha m0_real - theta0) - sin(alpha_cross - theta0) =
              sin(X-Y) + sin Y - sin X"
            proof -
              have "X = alpha_cross - theta0" unfolding X_def by (by100 simp)
              have "Y = alpha m0_real - theta0" unfolding Y_def by (by100 simp)
              have "X - Y = theta m0_real" using hXY .
              thus ?thesis using \<open>X = _\<close> \<open>Y = _\<close> by (by100 simp)
            qed
            also have "\<dots> = 4 * sin(X/2) * sin(Y/2) * sin((X-Y)/2)"
              using h_identity .
            also have "\<dots> = 4 * sin((alpha_cross-theta0)/2) * sin((alpha m0_real-theta0)/2) * sin(theta m0_real/2)"
            proof -
              have "sin(X/2) = sin((alpha_cross-theta0)/2)" unfolding X_def ..
              moreover have "sin(Y/2) = sin((alpha m0_real-theta0)/2)" unfolding Y_def ..
              moreover have "sin((X-Y)/2) = sin(theta m0_real/2)"
              proof -
                have "X - Y = theta m0_real" using hXY .
                thus ?thesis by (by100 simp)
              qed
              ultimately show ?thesis by (by100 simp)
            qed
            finally have hIm_product: "sin(theta m0_real) + sin(alpha m0_real - theta0) - sin(alpha_cross - theta0) =
              4 * sin((alpha_cross-theta0)/2) * sin((alpha m0_real-theta0)/2) * sin(theta m0_real/2)" .
            \<comment> \<open>Combine all: det = r^2 * (above expression).\<close>
            have "Im (cnj z1_m * z1_c) = r^2 * (sin(theta m0_real) + sin(alpha m0_real - theta0) - sin(alpha_cross - theta0))"
            proof -
              from hprod2 have "Im (cnj z1_m * z1_c) = r^2 * Im (cnj (cis A - cis T) * (cis B - cis T))"
                by (by100 simp)
              also have "\<dots> = r^2 * (sin(B-A) - sin(T-A) - sin(B-T))"
                using hprod_expand hprod_cis2 by (by100 simp)
              also have "\<dots> = r^2 * (sin(theta m0_real) + sin(alpha m0_real - theta0) - sin(alpha_cross - theta0))"
                using hIm_val by (by100 simp)
              finally show ?thesis .
            qed
            with hIm_product hdet_Im2 show ?thesis by (by100 algebra)
          qed
          from hfan_pos hfan_formula
          have hprod_pos: "sin((alpha m0_real - theta0)/2) * sin((alpha_cross - theta0)/2) * sin(theta (m0_real) / 2) > 0"
          proof -
            have "r^2 * 4 > 0" using hr_pos by (by100 simp)
            from hfan_pos hfan_formula have "r^2 * 4 * (sin((alpha m0_real - theta0)/2) * sin((alpha_cross - theta0)/2) * sin(theta (m0_real) / 2)) > 0"
              by (by100 linarith)
            with \<open>r^2 * 4 > 0\<close> show ?thesis
              by (simp add: zero_less_mult_iff)
          qed
          \<comment> \<open>But: sin((alpha\\_cross-theta0)/2) < 0 since alpha\\_cross-theta0 = 2\\<pi>+delta-theta0 > 2\\<pi>.
             So (alpha\\_cross-theta0)/2 > \\<pi>. sin < 0.\<close>
          have "alpha_cross - theta0 > 2*pi"
            using \<open>delta > theta0\<close> unfolding delta_def alpha_cross_def by linarith
          hence "sin((alpha_cross - theta0)/2) < 0"
          proof -
            have hpi_lt: "pi < (alpha_cross - theta0)/2"
              using \<open>alpha_cross - theta0 > 2*pi\<close> by simp
            from halpha_m0_lt have "alpha_cross < 3*pi" unfolding alpha_cross_def .
            hence "(alpha_cross - theta0)/2 < 3*pi/2" using htheta0_pos by simp
            hence h2pi_lt: "(alpha_cross - theta0)/2 < 2*pi" using pi_gt_zero by linarith
            from sin_lt_zero[OF hpi_lt h2pi_lt] show ?thesis .
          qed
          \<comment> \<open>And the other two sines > 0.\<close>
          have "sin(theta (m0_real) / 2) > 0"
          proof -
            have "m0_real < nw" using hm0_lt by linarith
            from htheta_pos[rule_format, OF this] have "theta m0_real > 0" "theta m0_real < pi" by auto
            thus ?thesis using sin_gt_zero by (by100 auto)
          qed
          have "sin((alpha m0_real - theta0)/2) > 0"
          proof -
            have "alpha m0_real > theta0"
            proof -
              have "alpha m0_real \<ge> alpha 2"
              proof -
                have "alpha m0_real = alpha 2 + (\<Sum>j=2..<m0_real. theta j)" unfolding alpha_def
                  using sum.atLeastLessThan_concat[of 0 2 m0_real theta] hm0_ge2
                  by (simp add: atLeast0LessThan)
                moreover have "(\<Sum>j=2..<m0_real. theta j) \<ge> 0"
                proof (rule sum_nonneg)
                  fix j assume "j \<in> {2..<m0_real}"
                  hence "j < nw" using hm0_lt by (by100 auto)
                  from htheta_pos[rule_format, OF this] show "0 \<le> theta j" by linarith
                qed
                ultimately show ?thesis by linarith
              qed
              moreover have "alpha 2 > theta0"
              proof -
                have "alpha 2 = theta 0 + theta 1" unfolding alpha_def
                  by (simp add: lessThan_Suc numeral_2_eq_2)
                moreover have "theta 1 > 0" using htheta_pos hnw by (by100 auto)
                ultimately show ?thesis unfolding theta0_def by linarith
              qed
              ultimately show ?thesis by linarith
            qed
            moreover have "alpha m0_real < 2*pi"
              using halpha_m0_below .
            ultimately have h1: "(alpha m0_real - theta0)/2 > 0" by simp
            have h2: "(alpha m0_real - theta0)/2 < pi" using \<open>alpha m0_real < 2*pi\<close> htheta0_pos by simp
            from sin_gt_zero[OF h1 h2] show ?thesis .
          qed
          \<comment> \<open>Product: (+)*(-)*)(+) < 0. But we showed > 0. Contradiction.\<close>
          from \<open>sin((alpha m0_real - theta0)/2) * sin((alpha_cross - theta0)/2) * sin(theta (m0_real) / 2) > 0\<close>
            \<open>sin((alpha m0_real - theta0)/2) > 0\<close> \<open>sin(theta (m0_real) / 2) > 0\<close>
            \<open>sin((alpha_cross - theta0)/2) < 0\<close>
          show False
          proof -
            have "sin((alpha m0_real - theta0)/2) * sin((alpha_cross - theta0)/2) < 0"
              using \<open>sin((alpha m0_real - theta0)/2) > 0\<close> \<open>sin((alpha_cross - theta0)/2) < 0\<close>
              using mult_pos_neg[of "sin((alpha m0_real - theta0)/2)" "sin((alpha_cross - theta0)/2)"]
              by linarith
            hence "sin((alpha m0_real - theta0)/2) * sin((alpha_cross - theta0)/2) * sin(theta (m0_real) / 2) < 0"
              using \<open>sin(theta (m0_real) / 2) > 0\<close>
              mult_neg_pos[of "sin((alpha m0_real - theta0)/2) * sin((alpha_cross - theta0)/2)" "sin(theta (m0_real) / 2)"]
              by linarith
            with \<open>sin((alpha m0_real - theta0)/2) * sin((alpha_cross - theta0)/2) * sin(theta (m0_real) / 2) > 0\<close>
            show False by linarith
          qed
        qed
      qed
      with hk(2) show "alpha nw = 2*pi" by simp
    qed
    \<comment> \<open>Key: cc(m) = -|z\\_0|*|z\\_m|*sin(alpha m) for m \\<in> {1,...,nw-1}.\<close>
    have hcc_sin: "\<forall>m. 0 < m \<longrightarrow> m < nw \<longrightarrow>
        cc m = -(cmod (zw 0) * cmod (zw m) * sin (alpha m))"
    proof (intro allI impI)
      fix m assume hm_pos: "0 < m" and hm_lt: "m < nw"
      \<comment> \<open>z\\_m/z\\_0 = \\<Prod>\\_{j<m} ratio\\_j. Each ratio = |r|*cis(\\<theta>).
         Product = (\\<Prod> |r|)*cis(\\<Sum> \\<theta>) = (|z\\_m|/|z\\_0|)*cis(alpha m).\<close>
      \<comment> \<open>cc(m) = Im(cnj(z\\_m)*z\\_0) = -|z\\_0|*|z\\_m|*sin(alpha m).\<close>
      \<comment> \<open>Step 1: z\\_m/z\\_0 = (|z\\_m|/|z\\_0|)*cis(alpha m).\<close>
      have hzm_decomp: "zw m / zw 0 = of_real (cmod (zw m) / cmod (zw 0)) * cis (alpha m)"
      proof -
        \<comment> \<open>From partial telescope: zw m / zw 0 = \\<Prod>\\_{j<m} ratio\\_j.
           Each ratio\\_j = cmod(ratio\\_j) * cis(Arg(ratio\\_j)) = cmod(ratio\\_j) * cis(theta j).
           Product of cis: cis(\\<Sum> theta) = cis(alpha m).
           Product of mods: \\<Prod> cmod(ratio\\_j) = cmod(\\<Prod> ratio\\_j) = cmod(zw m / zw 0).\<close>
        from hpartial_telescope[rule_format, OF hm_lt]
        have "zw m = (\<Prod>j<m. zw (Suc j mod nw) / zw j) * zw 0" .
        have hz0_ne_loc: "zw 0 \<noteq> 0" using hzw_ne hnw by (by100 simp)
        hence "zw m / zw 0 = (\<Prod>j<m. zw (Suc j mod nw) / zw j)"
          using \<open>zw m = _ * zw 0\<close> by (by100 simp)
        \<comment> \<open>Each ratio decomposed: ratio\\_j = of\\_real(cmod ratio\\_j)*cis(Arg ratio\\_j).\<close>
        \<comment> \<open>Arg(ratio\\_j) = theta j by definition.\<close>
        \<comment> \<open>Product: \\<Prod> (of\\_real r\\_j * cis t\\_j) = of\\_real(\\<Prod> r\\_j) * cis(\\<Sum> t\\_j).\<close>
        \<comment> \<open>And \\<Prod> r\\_j = cmod(\\<Prod> ratio\\_j) = cmod(zw m/zw 0) = cmod(zw m)/cmod(zw 0).\<close>
        \<comment> \<open>Helper: \\<Prod>\\_{j<m} r\\_j = of\\_real(\\<Prod> cmod r\\_j) * cis(\\<Sum> Arg r\\_j) when each r\\_j \\<noteq> 0.\<close>
        define rj where "rj j = zw (Suc j mod nw) / zw j" for j
        have hrj_ne: "\<forall>j<m. rj j \<noteq> 0"
        proof (intro allI impI)
          fix j assume "j < m"
          hence "j < nw" using hm_lt by linarith
          have "Suc j mod nw < nw" using hnw by (by100 simp)
          thus "rj j \<noteq> 0" unfolding rj_def
            using hzw_ne[rule_format, OF \<open>Suc j mod nw < nw\<close>] hzw_ne[rule_format, OF \<open>j < nw\<close>]
            by (by100 simp)
        qed
        \<comment> \<open>Each r\\_j = of\\_real(cmod r\\_j) * cis(Arg r\\_j) = of\\_real(cmod r\\_j) * cis(theta j).\<close>
        have hrj_decomp: "\<forall>j<m. rj j = of_real (cmod (rj j)) * cis (theta j)"
        proof (intro allI impI)
          fix j assume "j < m"
          from rcis_cmod_Arg[of "rj j", symmetric] have "rj j = of_real (cmod (rj j)) * cis (Arg (rj j))"
            unfolding rcis_def .
          also have "Arg (rj j) = theta j" unfolding rj_def theta_def by (by100 simp)
          finally show "rj j = of_real (cmod (rj j)) * cis (theta j)" .
        qed
        \<comment> \<open>Product induction: \\<Prod> r\\_j = of\\_real(\\<Prod> cmod r\\_j) * cis(\\<Sum> theta j).\<close>
        have hprod_polar: "(\<Prod>j<m. rj j) = of_real (\<Prod>j<m. cmod (rj j)) * cis (alpha m)"
        proof -
          have "\<And>k. k \<le> m \<Longrightarrow> (\<Prod>j<k. rj j) = of_real (\<Prod>j<k. cmod (rj j)) * cis (\<Sum>j<k. theta j)"
          proof -
            fix k show "k \<le> m \<Longrightarrow> (\<Prod>j<k. rj j) = of_real (\<Prod>j<k. cmod (rj j)) * cis (\<Sum>j<k. theta j)"
            proof (induction k)
              case 0 thus ?case by simp
            next
              case (Suc k')
              hence "k' < m" by simp
              from Suc.IH[OF order.strict_implies_order[OF \<open>k' < m\<close>]]
              have hIH: "(\<Prod>j<k'. rj j) = of_real (\<Prod>j<k'. cmod (rj j)) * cis (\<Sum>j<k'. theta j)" .
              have "(\<Prod>j<Suc k'. rj j) = (\<Prod>j<k'. rj j) * rj k'" by simp
              also have "\<dots> = of_real (\<Prod>j<k'. cmod (rj j)) * cis (\<Sum>j<k'. theta j) * rj k'"
                using hIH by simp
              also from hrj_decomp[rule_format, OF \<open>k' < m\<close>]
              have "\<dots> = of_real (\<Prod>j<k'. cmod (rj j)) * cis (\<Sum>j<k'. theta j) *
                  (of_real (cmod (rj k')) * cis (theta k'))" by simp
              also have "\<dots> = of_real ((\<Prod>j<k'. cmod (rj j)) * cmod (rj k')) *
                  (cis (\<Sum>j<k'. theta j) * cis (theta k'))"
              proof -
                have "of_real (\<Prod>j<k'. cmod (rj j)) * cis (\<Sum>j<k'. theta j) *
                    (of_real (cmod (rj k')) * cis (theta k'))
                    = rcis (\<Prod>j<k'. cmod (rj j)) (\<Sum>j<k'. theta j) *
                      rcis (cmod (rj k')) (theta k')"
                  unfolding rcis_def by simp
                also have "\<dots> = rcis ((\<Prod>j<k'. cmod (rj j)) * cmod (rj k'))
                    ((\<Sum>j<k'. theta j) + theta k')"
                  by (rule rcis_mult)
                also have "\<dots> = of_real ((\<Prod>j<k'. cmod (rj j)) * cmod (rj k')) *
                    cis ((\<Sum>j<k'. theta j) + theta k')"
                  unfolding rcis_def ..
                also have "cis ((\<Sum>j<k'. theta j) + theta k') = cis (\<Sum>j<k'. theta j) * cis (theta k')"
                  using cis_mult[symmetric] .
                finally show ?thesis .
              qed
              also have "cis (\<Sum>j<k'. theta j) * cis (theta k') = cis ((\<Sum>j<k'. theta j) + theta k')"
                by (rule cis_mult)
              also have "(\<Sum>j<k'. theta j) + theta k' = (\<Sum>j<Suc k'. theta j)" by simp
              also have "(\<Prod>j<k'. cmod (rj j)) * cmod (rj k') = (\<Prod>j<Suc k'. cmod (rj j))" by simp
              finally show ?case .
            qed
          qed
          from this[of m] show ?thesis unfolding alpha_def by simp
        qed
        \<comment> \<open>\\<Prod> cmod r\\_j = cmod(\\<Prod> r\\_j) = cmod(zw m/zw 0) = cmod(zw m)/cmod(zw 0).\<close>
        have "(\<Prod>j<m. cmod (rj j)) = cmod (\<Prod>j<m. rj j)"
          by (simp add: prod_norm)
        also have "\<dots> = cmod (zw m / zw 0)"
          using \<open>zw m / zw 0 = (\<Prod>j<m. zw (Suc j mod nw) / zw j)\<close> unfolding rj_def by simp
        also have "\<dots> = cmod (zw m) / cmod (zw 0)" by (rule norm_divide)
        finally have hmod_eq: "(\<Prod>j<m. cmod (rj j)) = cmod (zw m) / cmod (zw 0)" .
        from hprod_polar hmod_eq
        show ?thesis unfolding rj_def using \<open>zw m / zw 0 = _\<close> by simp
      qed
      \<comment> \<open>Step 2: cc(m) = Im(cnj(z\\_m)*z\\_0) = -|z\\_0|*|z\\_m|*sin(alpha m).\<close>
      have hz0_ne: "zw 0 \<noteq> 0" using hzw_ne hnw by (by100 simp)
      have hzm_ne: "zw m \<noteq> 0" using hzw_ne hm_lt by (by100 blast)
      \<comment> \<open>From decomposition: cnj(z\\_m)*z\\_0 = of\\_real(|z\\_0|*|z\\_m|)*cis(-alpha m).\<close>
      have hcnj_eq: "cnj (zw m) * zw 0 = of_real (cmod (zw 0) * cmod (zw m)) * cis (-(alpha m))"
      proof -
        \<comment> \<open>Use rcis decomposition: zw m/zw 0 = rcis(|zm|/|z0|, alpha m).
           cnj(rcis(r,t)) = rcis(r,-t). Then cnj(zm)*z0 = cnj(zm/z0)*|z0|^2 = rcis(|zm|/|z0|,-alpha)*|z0|^2.\<close>
        define r_ratio where "r_ratio = cmod (zw m) / cmod (zw 0)"
        from hzm_decomp have hrat: "zw m / zw 0 = rcis r_ratio (alpha m)"
          unfolding rcis_def r_ratio_def .
        \<comment> \<open>cnj(zw m/zw 0) = rcis(r\\_ratio, -alpha m).\<close>
        have "cnj (zw m / zw 0) = cnj (rcis r_ratio (alpha m))" using hrat by simp
        also have "cnj (rcis r_ratio (alpha m)) = rcis r_ratio (-(alpha m))"
          unfolding rcis_def by (simp add: cis_cnj)
        finally have hcnj_rat: "cnj (zw m / zw 0) = rcis r_ratio (-(alpha m))" .
        \<comment> \<open>cnj(zm)*z0 = cnj(zm/z0) * |z0|^2.\<close>
        have hnorm_sq: "cnj (zw 0) * zw 0 = of_real ((cmod (zw 0))^2)"
          using complex_norm_square by simp
        have hcnj_prod: "cnj (zw m / zw 0) * cnj (zw 0) = cnj (zw m)" using hz0_ne by simp
        have "cnj (zw m) * zw 0 = (cnj (zw m / zw 0) * cnj (zw 0)) * zw 0" using hcnj_prod by simp
        also have "\<dots> = cnj (zw m / zw 0) * (cnj (zw 0) * zw 0)" by (by100 algebra)
        also have "\<dots> = cnj (zw m / zw 0) * of_real ((cmod (zw 0))^2)" using hnorm_sq by simp
        also have "\<dots> = rcis r_ratio (-(alpha m)) * of_real ((cmod (zw 0))^2)" using hcnj_rat by simp
        also have "\<dots> = rcis (r_ratio * (cmod (zw 0))^2) (-(alpha m))"
          using rcis_mult[of r_ratio "-(alpha m)" "(cmod (zw 0))^2" 0] by (by100 simp)
        also have "r_ratio * (cmod (zw 0))^2 = cmod (zw 0) * cmod (zw m)"
        proof -
          have "cmod (zw 0) > 0" using hz0_ne by (by100 simp)
          hence "cmod (zw 0) \<noteq> 0" by linarith
          hence "cmod (zw m) / cmod (zw 0) * (cmod (zw 0))^2 = cmod (zw m) * cmod (zw 0)"
            by (simp add: power2_eq_square)
          thus ?thesis unfolding r_ratio_def by (by100 algebra)
        qed
        finally show ?thesis unfolding rcis_def by simp
      qed
      hence "Im (cnj (zw m) * zw 0) = cmod (zw 0) * cmod (zw m) * sin (-(alpha m))"
      proof -
        have "Im (of_real (cmod (zw 0) * cmod (zw m)) * cis (-(alpha m))) =
            cmod (zw 0) * cmod (zw m) * Im (cis (-(alpha m)))"
          by (cases "cis (-(alpha m))") (simp add: complex_of_real_mult_Complex)
        also have "Im (cis (-(alpha m))) = sin (-(alpha m))" by (by100 simp)
        finally show ?thesis using hcnj_eq by simp
      qed
      hence "Im (cnj (zw m) * zw 0) = -(cmod (zw 0) * cmod (zw m) * sin (alpha m))"
        by (by100 simp)
      from hcc_im[rule_format, OF hm_lt] this
      show "cc m = -(cmod (zw 0) * cmod (zw m) * sin (alpha m))" by linarith
    qed
    \<comment> \<open>From cc(jp) \\<ge> 0: sin(alpha jp) \\<le> 0, so alpha\\_jp \\<in> [\\<pi>, 2\\<pi>).\<close>
    have hjp_pos: "jp > 0" using hjp_ne0 by (by100 linarith)
    have hjp1_lt: "jp + 1 < nw" using hjp_lt by (by100 linarith)
    from hcc_sin[rule_format, OF hjp_pos hjp] \<open>cc jp \<ge> 0\<close>
    have "sin (alpha jp) \<le> 0"
    proof -
      have "cmod (zw 0) > 0" using hzw_ne hnw by (by100 simp)
      have "cmod (zw jp) > 0" using hzw_ne hjp by (by100 simp)
      from hcc_sin[rule_format, OF hjp_pos hjp]
      have "cc jp = -(cmod (zw 0) * cmod (zw jp) * sin (alpha jp))" .
      with \<open>cc jp \<ge> 0\<close> have "cmod (zw 0) * cmod (zw jp) * sin (alpha jp) \<le> 0" by linarith
      have "cmod (zw 0) * cmod (zw jp) > 0"
        using \<open>cmod (zw 0) > 0\<close> \<open>cmod (zw jp) > 0\<close> by (by100 simp)
      show ?thesis
      proof (rule ccontr)
        assume "\<not> sin (alpha jp) \<le> 0"
        hence "sin (alpha jp) > 0" by linarith
        hence "cmod (zw 0) * cmod (zw jp) * sin (alpha jp) > 0"
          using \<open>cmod (zw 0) * cmod (zw jp) > 0\<close> by (by100 simp)
        with \<open>cmod (zw 0) * cmod (zw jp) * sin (alpha jp) \<le> 0\<close> show False by linarith
      qed
    qed
    \<comment> \<open>alpha\\_jp \\<in> (0, 2\\<pi>) and sin \\<le> 0: alpha\\_jp \\<in> [\\<pi>, 2\\<pi>).\<close>
    have halpha_jp_range: "alpha jp \<ge> pi \<and> alpha jp < 2*pi"
    proof -
      \<comment> \<open>alpha jp > 0 (each theta > 0 and jp > 0).\<close>
      have halpha_pos: "alpha jp > 0"
      proof -
        have "alpha jp = (\<Sum>j<jp. theta j)" unfolding alpha_def by simp
        have "\<forall>j\<in>{..<jp}. theta j > 0" using htheta_pos hjp by (by100 auto)
        have "{..<jp} \<noteq> {}" using hjp_ne0 by (by100 auto)
        from sum_pos[OF _ \<open>{..<jp} \<noteq> {}\<close>] \<open>\<forall>j\<in>{..<jp}. theta j > 0\<close>
        have "(\<Sum>j<jp. theta j) > 0" by (by100 blast)
        thus ?thesis unfolding alpha_def by simp
      qed
      \<comment> \<open>alpha jp < 2*pi (remaining sum > 0).\<close>
      have halpha_lt: "alpha jp < 2*pi"
      proof -
        have "alpha jp + (\<Sum>j=jp..<nw. theta j) = alpha nw" unfolding alpha_def
        proof -
          have "(\<Sum>j<jp. theta j) + (\<Sum>j=jp..<nw. theta j) = (\<Sum>j<nw. theta j)"
            using sum.atLeastLessThan_concat[of 0 jp nw theta] hjp
            by (simp add: atLeast0LessThan)
          thus "(\<Sum>j<jp. theta j) + (\<Sum>j=jp..<nw. theta j) = (\<Sum>j<nw. theta j)" .
        qed
        moreover have "(\<Sum>j=jp..<nw. theta j) > 0"
        proof -
          have "\<forall>j\<in>{jp..<nw}. theta j > 0" using htheta_pos hjp by (by100 auto)
          have "{jp..<nw} \<noteq> {}" using hjp by (by100 auto)
          have "finite {jp..<nw}" by (by100 simp)
          from sum_pos[OF \<open>finite {jp..<nw}\<close> \<open>{jp..<nw} \<noteq> {}\<close>] \<open>\<forall>j\<in>{jp..<nw}. theta j > 0\<close>
          show ?thesis by (by100 blast)
        qed
        ultimately show ?thesis using halpha_sum by linarith
      qed
      \<comment> \<open>sin(alpha jp) \\<le> 0 and 0 < alpha jp: alpha jp \\<ge> pi.\<close>
      have "alpha jp \<ge> pi"
      proof (rule ccontr)
        assume "\<not> alpha jp \<ge> pi"
        hence "alpha jp < pi" by linarith
        with halpha_pos have "sin (alpha jp) > 0" by (rule sin_gt_zero)
        with \<open>sin (alpha jp) \<le> 0\<close> show False by linarith
      qed
      with halpha_lt show ?thesis by (by100 auto)
    qed
    \<comment> \<open>alpha(jp+1) = alpha(jp) + theta(jp) \\<in> (\\<pi>, 2\\<pi>+\\<pi>) \\<cap> (0, 2\\<pi>) = (\\<pi>, 2\\<pi>).\<close>
    have halpha_jp1_range: "alpha (jp+1) > pi \<and> alpha (jp+1) < 2*pi"
    proof -
      have "alpha (jp+1) = alpha jp + theta jp" unfolding alpha_def by simp
      moreover from htheta_pos hjp have "theta jp > 0" by (by100 blast)
      moreover from halpha_jp_range have "alpha jp \<ge> pi" by (by100 blast)
      moreover have "alpha (jp+1) < 2*pi"
      proof -
        have "alpha nw = 2*pi" using halpha_sum .
        have "alpha (jp+1) + (\<Sum>j=jp+1..<nw. theta j) = alpha nw" unfolding alpha_def
        proof -
          have "(\<Sum>j<jp+1. theta j) + (\<Sum>j=jp+1..<nw. theta j) = (\<Sum>j<nw. theta j)"
            using sum.atLeastLessThan_concat[of 0 "jp+1" nw theta] hjp1_lt
            by (simp add: atLeast0LessThan)
          thus "(\<Sum>j<jp+1. theta j) + (\<Sum>j=jp+1..<nw. theta j) = (\<Sum>j<nw. theta j)" .
        qed
        moreover have "(\<Sum>j=jp+1..<nw. theta j) > 0"
        proof -
          have "\<forall>j\<in>{jp+1..<nw}. theta j > 0" using htheta_pos hjp1_lt by (by100 auto)
          have "{jp+1..<nw} \<noteq> {}" using hjp1_lt by (by100 auto)
          have "finite {jp+1..<nw}" by (by100 simp)
          from sum_pos[OF \<open>finite {jp+1..<nw}\<close> \<open>{jp+1..<nw} \<noteq> {}\<close>] \<open>\<forall>j\<in>{jp+1..<nw}. theta j > 0\<close>
          show ?thesis by (by100 blast)
        qed
        ultimately show ?thesis using halpha_sum by linarith
      qed
      ultimately show ?thesis by linarith
    qed
    \<comment> \<open>sin(alpha(jp+1)) < 0 since alpha(jp+1) \\<in> (\\<pi>, 2\\<pi>).\<close>
    have "sin (alpha (jp+1)) < 0"
      using halpha_jp1_range sin_lt_zero by (by100 blast)
    \<comment> \<open>Therefore cc(jp+1) > 0.\<close>
    have "cc (jp + 1) > 0"
    proof -
      have "cmod (zw 0) > 0" using hzw_ne hnw by (by100 simp)
      have "cmod (zw (jp+1)) > 0" using hzw_ne hjp1_lt by (by100 simp)
      from hcc_sin[rule_format, OF _ hjp1_lt] hjp_pos
      have hcc_jp1_eq: "cc (jp+1) = -(cmod (zw 0) * cmod (zw (jp+1)) * sin (alpha (jp+1)))"
        by (by100 linarith)
      with \<open>sin (alpha (jp+1)) < 0\<close> \<open>cmod (zw 0) > 0\<close> \<open>cmod (zw (jp+1)) > 0\<close>
      show ?thesis
      proof -
        have "cmod (zw 0) * cmod (zw (jp+1)) > 0"
          using \<open>cmod (zw 0) > 0\<close> \<open>cmod (zw (jp+1)) > 0\<close> by (by100 simp)
        hence "cmod (zw 0) * cmod (zw (jp+1)) * sin (alpha (jp+1)) < 0"
          using \<open>sin (alpha (jp+1)) < 0\<close> mult_pos_neg by (by100 blast)
        thus ?thesis using hcc_jp1_eq by linarith
      qed
    qed
    hence "cc (Suc jp mod nw) > 0" using hsjp by simp
    thus ?thesis unfolding cc_def by auto
  qed
qed

\<comment> \<open>Standalone lemma: fan triangle interiors from a centroid are disjoint.
   If q = \\<alpha>*cw + s*u\\_j + t*u\\_{j+1} with \\<alpha>,s,t > 0
   and q = \\<alpha>'*cw + s'*u\\_{j'} + t'*u\\_{j'+1} with \\<alpha>',s',t' > 0
   and C10 holds (centroid strictly interior), and j \\<noteq> j', then contradiction.\<close>
\<comment> \<open>Actually: we show the cross product cross\\_cw at the shared boundary forces j = j'.
   Specifically: cross\\_cw(j+1, q) = s'*det(u\\_{j+1}-cw, u\\_{j'}-cw) + ... and these
   must be both < 0 (from being in sector j) and \\<ge> 0 (from sector j' if j+1 = j').
   The full proof is complex; for now sorry this for progress.\<close>

\<comment> \<open>Standalone lemma for prop12: if s*(u\\_j - u\\_0) + t*(u\\_{j+1} - u\\_0) = 0 with s,t \\<ge> 0
   and the vertices are not at u\\_0 (i.e., j \\<noteq> 0 and j+1 \\<noteq> 0), then s = t = 0.
   This forces p = v\\_1 in the spur arc collision argument.\<close>
lemma nonneg_combo_independent_zero:
  fixes ax ay bx by' :: real
  assumes hs: "s_v \<ge> 0" and ht: "t_v \<ge> 0"
      and hx: "s_v*ax + t_v*bx = 0"
      and hy: "s_v*ay + t_v*by' = 0"
      and hdet: "ax*by' - ay*bx \<noteq> 0"
  shows "s_v = 0 \<and> t_v = 0"
proof -
  \<comment> \<open>Cramer: s\\_v*(ax*by'-ay*bx) = by'*(s\\_v*ax) - bx*(s\\_v*ay)
     = by'*(-(t\\_v*bx)) - bx*(-(t\\_v*by')) = 0.\<close>
  have "s_v*(ax*by'-ay*bx) = (s_v*ax)*by' - (s_v*ay)*bx" by (by100 algebra)
  also have "(s_v*ax) = -(t_v*bx)" using hx by linarith
  also have "(s_v*ay) = -(t_v*by')" using hy by linarith
  finally have "s_v*(ax*by'-ay*bx) = -(t_v*bx)*by' - (-(t_v*by'))*bx" by simp
  hence "s_v*(ax*by'-ay*bx) = 0" by (by100 algebra)
  hence "s_v = 0" using hdet by simp
  moreover from hx \<open>s_v = 0\<close> have "t_v*bx = 0" by simp
  from hy \<open>s_v = 0\<close> have "t_v*by' = 0" by simp
  have "t_v = 0"
  proof (rule ccontr)
    assume "t_v \<noteq> 0"
    from \<open>t_v*bx = 0\<close> \<open>t_v \<noteq> 0\<close> have "bx = 0" by simp
    from \<open>t_v*by' = 0\<close> \<open>t_v \<noteq> 0\<close> have "by' = 0" by simp
    hence "ax*by' - ay*bx = 0" using \<open>bx = 0\<close> by simp
    with hdet show False by simp
  qed
  ultimately show ?thesis by auto
qed

lemma weighted_sum_square_le:
  assumes "\<forall>i\<in>S. (c i :: real) \<ge> 0" and "(\<Sum>i\<in>S. c i) = 1" and "finite S"
  shows "(\<Sum>i\<in>S. c i * f i)^2 \<le> (\<Sum>i\<in>S. c i * (f i)^2)"
  using assms(3,1,2)
proof (induction arbitrary: c rule: finite_induct)
  case empty thus ?case by simp
next
  case (insert x F)
  show ?case
  proof (cases "c x = 1")
    case True
    hence "\<forall>i\<in>F. c i = 0"
    proof -
      from insert(5) True have "(\<Sum>i\<in>F. c i) = 0" using insert(1,2) by simp
      with insert(4) show ?thesis
        using sum_nonneg_eq_0_iff[OF insert(1)] by (by100 auto)
    qed
    hence "(\<Sum>i\<in>insert x F. c i * f i) = c x * f x"
      using insert(1,2) using sum.insert_if by (by100 simp)
    also have "\<dots> = f x" using True by simp
    finally have lhs: "(\<Sum>i\<in>insert x F. c i * f i)^2 = (f x)^2" by simp
    have "(\<Sum>i\<in>insert x F. c i * (f i)^2) = c x * (f x)^2"
      using \<open>\<forall>i\<in>F. c i = 0\<close> insert(1,2) using sum.insert_if by (by100 simp)
    hence rhs: "(\<Sum>i\<in>insert x F. c i * (f i)^2) = (f x)^2" using True by simp
    from lhs rhs show ?thesis by simp
  next
    case False
    hence hcx_lt: "c x < 1"
      using insert(4,5) insert(1,2) sum_nonneg[of F c]
      using sum.insert_if by (by100 simp)
    hence hrest_pos: "(\<Sum>i\<in>F. c i) > 0"
      using insert(5) insert(1,2) using sum.insert_if by (by100 simp)
    define r where "r = (\<Sum>i\<in>F. c i)"
    have hr: "r > 0" using hrest_pos unfolding r_def .
    have hcxr: "c x + r = 1" using insert(5) insert(1,2) unfolding r_def
      using sum.insert_if by (by100 simp)
    define c' where "c' i = c i / r" for i
    have hc'_nn: "\<forall>i\<in>F. c' i \<ge> 0" using insert(4) hr unfolding c'_def by (by100 auto)
    have hc'_sum: "(\<Sum>i\<in>F. c' i) = 1"
    proof -
      have "(\<Sum>i\<in>F. c' i) = (\<Sum>i\<in>F. c i / r)" unfolding c'_def by (by100 simp)
      also have "\<dots> = (\<Sum>i\<in>F. c i) / r" using sum_divide_distrib[of c F r] by (by100 simp)
      also have "\<dots> = r / r" unfolding r_def by (by100 simp)
      also have "\<dots> = 1" using hr by (by100 simp)
      finally show ?thesis .
    qed
    define \<mu> where "\<mu> = (\<Sum>i\<in>F. c' i * f i)"
    \<comment> \<open>IH: \\<mu>^2 \\<le> \\<Sum>c'\\_i*f\\_i^2.\<close>
    from insert(3)[OF hc'_nn hc'_sum]
    have hIH: "\<mu>^2 \<le> (\<Sum>i\<in>F. c' i * (f i)^2)" unfolding \<mu>_def .
    \<comment> \<open>Express the full sum in terms of c(x)*f(x) + r*\\<mu>.\<close>
    have hsum_f: "(\<Sum>i\<in>insert x F. c i * f i) = c x * f x + r * \<mu>"
    proof -
      have "(\<Sum>i\<in>insert x F. c i * f i) = c x * f x + (\<Sum>i\<in>F. c i * f i)"
        using insert(1,2) using sum.insert_if by (by100 simp)
      also have "(\<Sum>i\<in>F. c i * f i) = r * \<mu>"
        unfolding \<mu>_def c'_def using hr by (simp add: sum_distrib_left)
      finally show ?thesis .
    qed
    have hsum_f2: "(\<Sum>i\<in>insert x F. c i * (f i)^2) = c x * (f x)^2 + r * (\<Sum>i\<in>F. c' i * (f i)^2)"
    proof -
      have "(\<Sum>i\<in>insert x F. c i * (f i)^2) = c x * (f x)^2 + (\<Sum>i\<in>F. c i * (f i)^2)"
        using insert(1,2) using sum.insert_if by (by100 simp)
      also have "(\<Sum>i\<in>F. c i * (f i)^2) = r * (\<Sum>i\<in>F. c' i * (f i)^2)"
        unfolding c'_def using hr by (simp add: sum_distrib_left)
      finally show ?thesis .
    qed
    \<comment> \<open>Two-point inequality: (c\\_x*a + r*b)^2 \\<le> c\\_x*a^2 + r*b^2 when c\\_x+r=1.\<close>
    have htwo: "(c x * f x + r * \<mu>)^2 \<le> c x * (f x)^2 + r * \<mu>^2"
    proof -
      have "c x * (f x)^2 + r * \<mu>^2 - (c x * f x + r * \<mu>)^2 = c x * r * (f x - \<mu>)^2"
        using hcxr by (by100 algebra)
      moreover have "c x * r * (f x - \<mu>)^2 \<ge> 0"
        using insert(4) hr by (by100 auto)
      ultimately show ?thesis by linarith
    qed
    \<comment> \<open>Combine: (\\<Sum>c\\_i*f\\_i)^2 = (c\\_x*f\\_x+r*\\<mu>)^2 \\<le> c\\_x*f\\_x^2+r*\\<mu>^2 \\<le> c\\_x*f\\_x^2+r*(\\<Sum>c'\\_i*f\\_i^2).\<close>
    have "(\<Sum>i\<in>insert x F. c i * f i)^2 = (c x * f x + r * \<mu>)^2"
      using hsum_f by simp
    also have "\<dots> \<le> c x * (f x)^2 + r * \<mu>^2" using htwo .
    also have "\<dots> \<le> c x * (f x)^2 + r * (\<Sum>i\<in>F. c' i * (f i)^2)"
      using hIH hr by (by100 auto)
    also have "\<dots> = (\<Sum>i\<in>insert x F. c i * (f i)^2)"
      using hsum_f2 by simp
    finally show ?thesis .
  qed
qed

\<comment> \<open>Corollary: convex hull of unit circle vertices is inside unit disk.\<close>
lemma convex_hull_unit_circle_norm_le:
  assumes "\<forall>i<(n::nat). (c i :: real) \<ge> 0" "(\<Sum>i<n. c i) = 1"
      "\<forall>i<n. (vx i)^2 + (vy i)^2 = 1"
  shows "(\<Sum>i<n. c i * vx i)^2 + (\<Sum>i<n. c i * vy i)^2 \<le> 1"
proof -
  have "(\<Sum>i<n. c i * vx i)^2 \<le> (\<Sum>i<n. c i * (vx i)^2)"
    using weighted_sum_square_le[of "{..<n}" c vx] assms(1,2) by (by100 auto)
  moreover have "(\<Sum>i<n. c i * vy i)^2 \<le> (\<Sum>i<n. c i * (vy i)^2)"
    using weighted_sum_square_le[of "{..<n}" c vy] assms(1,2) by (by100 auto)
  ultimately have "(\<Sum>i<n. c i * vx i)^2 + (\<Sum>i<n. c i * vy i)^2 \<le>
      (\<Sum>i<n. c i * (vx i)^2) + (\<Sum>i<n. c i * (vy i)^2)" by linarith
  also have "\<dots> = (\<Sum>i<n. c i * ((vx i)^2 + (vy i)^2))"
    by (simp add: sum.distrib[symmetric] algebra_simps)
  also have "\<dots> = (\<Sum>i<n. c i)"
    by (rule sum.cong) (use assms(3) in auto)
  also have "\<dots> = 1" using assms(2) .
  finally show ?thesis .
qed

\<comment> \<open>Cross product of centroid-cone point with sector direction is non-negative.
   If q = \\<alpha>*cw + sp*u\\_j + tp*u\\_{j+1} with sp,tp \\<ge> 0,
   then cross(u\\_j-cw, q-cw) = tp*C10(j) \\<ge> 0 and cross(q-cw, u\\_{j+1}-cw) = sp*C10(j) \\<ge> 0.\<close>
lemma centroid_cone_cross_nonneg:
  fixes cxw cyw vjx vjy vjpx vjpy :: real
  assumes hsp: "sp \<ge> 0" and htp: "tp \<ge> 0"
      and habg: "alpha + sp + tp = 1"
      and hqx: "qx = alpha*cxw + sp*vjx + tp*vjpx"
      and hqy: "qy = alpha*cyw + sp*vjy + tp*vjpy"
      and hC10: "(vjx-cxw)*(vjpy-cyw)-(vjy-cyw)*(vjpx-cxw) > 0"
  shows "(vjx-cxw)*(qy-cyw)-(vjy-cyw)*(qx-cxw) \<ge> 0"
    and "(qx-cxw)*(vjpy-cyw)-(qy-cyw)*(vjpx-cxw) \<ge> 0"
proof -
  have "qx - cxw = sp*(vjx-cxw) + tp*(vjpx-cxw)"
    using hqx habg by (by100 algebra)
  have "qy - cyw = sp*(vjy-cyw) + tp*(vjpy-cyw)"
    using hqy habg by (by100 algebra)
  have h1: "(vjx-cxw)*(qy-cyw)-(vjy-cyw)*(qx-cxw) =
    tp * ((vjx-cxw)*(vjpy-cyw)-(vjy-cyw)*(vjpx-cxw))"
    using \<open>qx - cxw = _\<close> \<open>qy - cyw = _\<close> by (by100 algebra)
  have h2: "(qx-cxw)*(vjpy-cyw)-(qy-cyw)*(vjpx-cxw) =
    sp * ((vjx-cxw)*(vjpy-cyw)-(vjy-cyw)*(vjpx-cxw))"
    using \<open>qx - cxw = _\<close> \<open>qy - cyw = _\<close> by (by100 algebra)
  from h1 htp hC10 show "(vjx-cxw)*(qy-cyw)-(vjy-cyw)*(qx-cxw) \<ge> 0" by (by100 auto)
  from h2 hsp hC10 show "(qx-cxw)*(vjpy-cyw)-(qy-cyw)*(vjpx-cxw) \<ge> 0" by (by100 auto)
qed

\<comment> \<open>Cross product of affine-mapped point with sector directions is non-negative.
   Given the standard Cramer affine map from sector to centroid cone,
   if cross\\_v1(jp+2, p) \\<ge> 0 and cross\\_v1(si, p) \\<le> 0 (from in\\_sector),
   det(sector) > 0, and C10(jp) > 0, then the centroid-cone cross products are \\<ge> 0.\<close>
lemma phi_sector_cross_nonneg:
  fixes ex ey fx fy dx dy det_v cxw cyw vjx vjy vjpx vjpy :: real
  assumes hex: "ex = vxe2 - vxe1" and hey: "ey = vye2 - vye1"
      and hfx: "fx = vxf2 - vxe1" and hfy: "fy = vyf2 - vye1"
      and hdx: "dx = px - vxe1" and hdy: "dy = py - vye1"
      and hdet_def: "det_v = ex*fy - ey*fx"
      and hdet_pos: "det_v > 0"
      and hqx: "qx = (1 - (fy*dx-fx*dy)/det_v - (ex*dy-ey*dx)/det_v)*cxw + (fy*dx-fx*dy)/det_v*vjx + (ex*dy-ey*dx)/det_v*vjpx"
      and hqy: "qy = (1 - (fy*dx-fx*dy)/det_v - (ex*dy-ey*dx)/det_v)*cyw + (fy*dx-fx*dy)/det_v*vjy + (ex*dy-ey*dx)/det_v*vjpy"
      and hcross_pos: "ex*dy - ey*dx \<ge> 0" \<comment> \<open>cross\\_v1(jp+2, p) \\<ge> 0\<close>
      and hcross_neg: "fy*dx - fx*dy \<ge> 0" \<comment> \<open>-(cross\\_v1(si, p)) \\<ge> 0\<close>
      and hC10: "(vjx-cxw)*(vjpy-cyw)-(vjy-cyw)*(vjpx-cxw) > 0"
  shows "(vjx-cxw)*(qy-cyw)-(vjy-cyw)*(qx-cxw) \<ge> 0"
    and "(qx-cxw)*(vjpy-cyw)-(qy-cyw)*(vjpx-cxw) \<ge> 0"
proof -
  define sp where "sp = (fy*dx-fx*dy)/det_v"
  define tp where "tp = (ex*dy-ey*dx)/det_v"
  have hsp_ge: "sp \<ge> 0"
    using hcross_neg hdet_pos unfolding sp_def by (by100 simp)
  have htp_ge: "tp \<ge> 0"
    using hcross_pos hdet_pos unfolding tp_def by (by100 simp)
  have habg: "(1-sp-tp) + sp + tp = 1" by linarith
  have hqx': "qx = (1-sp-tp)*cxw + sp*vjx + tp*vjpx"
    using hqx unfolding sp_def tp_def .
  have hqy': "qy = (1-sp-tp)*cyw + sp*vjy + tp*vjpy"
    using hqy unfolding sp_def tp_def .
  from centroid_cone_cross_nonneg[OF hsp_ge htp_ge habg hqx' hqy' hC10]
  show "(vjx-cxw)*(qy-cyw)-(vjy-cyw)*(qx-cxw) \<ge> 0"
   and "(qx-cxw)*(vjpy-cyw)-(qy-cyw)*(vjpx-cxw) \<ge> 0" by auto
qed

\<comment> \<open>Sine interval characterization: sin(x) \\<ge> 0 and sin(y-x) \\<ge> 0 with y \\<in> (0,\\<pi>) implies x \\<in> [0,y].\<close>
lemma sin_interval_nonneg:
  assumes "sin x \<ge> 0" and "sin (y - x) \<ge> 0" and "0 < y" and "y < pi"
      and "x > -pi" and "x < 2*pi"
  shows "0 \<le> x \<and> x \<le> y"
proof -
  \<comment> \<open>From sin(x) \\<ge> 0: x \\<in> [2k\\<pi>, (2k+1)\\<pi>] for some k. With x \\<in> (-2\\<pi>, 2\\<pi>): x \\<in> [-2\\<pi>,-\\<pi>] \\<union> [0,\\<pi>].
     From sin(y-x) \\<ge> 0: y-x \\<in> [2k\\<pi>, (2k+1)\\<pi>]. So x \\<in> [y-(2k+1)\\<pi>, y-2k\\<pi>].
     Combining: x \\<in> [0, y].\<close>
  have hx_lower: "x \<ge> 0"
  proof (rule ccontr)
    assume "\<not> x \<ge> 0"
    hence "x < 0" by linarith
    \<comment> \<open>sin(x) \\<ge> 0 with x < 0: x \\<in> [-2\\<pi>, -\\<pi>] (for x > -2\\<pi>).
       Then y-x > y > 0 and y-x > \\<pi> (since x < -\\<pi>+y < \\<pi>... need x \\<le> -\\<pi>).\<close>
    show False
    proof (cases "x \<ge> -pi")
      case True
      \<comment> \<open>x \\<in> [-\\<pi>, 0). If x = -\\<pi>: sin(y-x) = sin(y+\\<pi>) = -sin(y) < 0. Contradiction.\<close>
      show False
      proof (cases "x = -pi")
        case True
        hence "sin(y - x) = sin(y + pi)" by (by100 simp)
        also have "\<dots> = -sin y" using sin_periodic_pi by (by100 metis)
        finally have "sin(y-x) < 0" using sin_gt_zero[of y] assms(3) assms(4) by linarith
        with assms(2) show False by linarith
      next
        case False
        hence "x > -pi" using True by linarith
        hence "x + pi > 0" by linarith
        moreover have "x + pi < pi" using \<open>x < 0\<close> by linarith
        ultimately have "sin(x + pi) > 0" using sin_gt_zero[of "x+pi"] by linarith
        hence "-(sin x) > 0" using sin_periodic_pi[of x] by (by100 metis)
        hence "sin x < 0" by linarith
        with assms(1) show False by linarith
      qed
    next
      case False
      hence "x < -pi" by linarith
      with assms(5) show False by linarith
    qed
  qed
  have hx_upper: "x \<le> y"
  proof (rule ccontr)
    assume "\<not> x \<le> y"
    hence "x > y" by linarith
    \<comment> \<open>First show x \\<le> \\<pi>: from sin(x) \\<ge> 0 and x \\<ge> 0, if x > \\<pi> then sin < 0.\<close>
    have hx_le_pi: "x \<le> pi"
    proof (rule ccontr)
      assume "\<not> x \<le> pi" hence "x > pi" by linarith
      \<comment> \<open>x \\<in> (\\<pi>, 2\\<pi>) from x > \\<pi> and assms(6). sin\\_lt\\_zero gives sin(x) < 0.\<close>
      hence "sin x < 0" using sin_lt_zero[of x] assms(6) by linarith
      with assms(1) show False by linarith
    qed
    \<comment> \<open>x \\<in> [0, \\<pi>] and x > y, so y - x \\<in> (-\\<pi>, 0). sin negative on (-\\<pi>, 0).\<close>
    have "y - x > -pi" using hx_le_pi assms(3) by linarith
    have "y - x < 0" using \<open>x > y\<close> by linarith
    \<comment> \<open>sin(y-x) < 0 for y-x \\<in> (-\\<pi>, 0): use sin(-(y-x)) > 0 since -(y-x) \\<in> (0, \\<pi>).\<close>
    have "sin(-(y-x)) > 0" using sin_gt_zero[of "-(y-x)"] \<open>y-x > -pi\<close> \<open>y-x < 0\<close> by linarith
    hence "sin(y-x) < 0" using sin_minus[of "y-x"] by linarith
    with assms(2) show False by linarith
  qed
  from hx_lower hx_upper show ?thesis by (by100 auto)
qed

\<comment> \<open>Cross product of unit circle polygon vertices = sin(cumulative angle difference).
   cnj(uw i)*uw j = cis(alpha\\_j - alpha\\_i) where alpha is the cumulative angle from Arg steps.\<close>


\<comment> \<open>Cross product of unit circle polygon vertices = sin(cumulative angle difference).
   cnj(uw i)*uw j = cis(alpha\\_j - alpha\\_i) where alpha is the cumulative angle from Arg steps.\<close>
lemma unit_circle_cross_cis:
  fixes nw :: nat and vxw vyw :: "nat \<Rightarrow> real"
  assumes hnw: "nw \<ge> 3"
      and hC10: "\<forall>i<nw. vxw i * vyw(Suc i mod nw) - vyw i * vxw(Suc i mod nw) > 0"
      and hC11: "\<forall>i<nw. \<forall>k<nw. k\<noteq>i \<longrightarrow> k\<noteq>Suc i mod nw \<longrightarrow>
          (vxw k-vxw i)*(vyw(Suc i mod nw)-vyw i)-(vyw k-vyw i)*(vxw(Suc i mod nw)-vxw i) < 0"
      and hunit: "\<forall>j<nw. (vxw j)^2 + (vyw j)^2 = 1"
      and hi: "i < nw" and hj: "j < nw"
  shows "\<exists>alpha. (\<forall>j<nw. \<forall>j'<nw. cnj (Complex (vxw j) (vyw j)) * Complex (vxw j') (vyw j') =
      cis (alpha j' - alpha j)) \<and>
    (\<forall>j<nw. alpha j < alpha (Suc j)) \<and> alpha 0 = 0 \<and> alpha nw = 2*pi"
  proof -
    define uw where "uw j = Complex (vxw j) (vyw j)" for j
    define theta where "theta j = Arg (uw (Suc j mod nw) / uw j)" for j
    define alpha where "alpha m = (\<Sum>j<m. theta j)" for m
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
    have hC10_im: "\<forall>j<nw. Im (cnj (uw j) * uw (Suc j mod nw)) > 0"
    proof (intro allI impI)
      fix j assume hj: "j < nw"
      have "Im (cnj (uw j) * uw (Suc j mod nw)) =
          vxw j * vyw(Suc j mod nw) - vyw j * vxw(Suc j mod nw)"
        unfolding uw_def by (by100 simp)
      with hC10[rule_format, OF hj] show "Im (cnj (uw j) * uw (Suc j mod nw)) > 0" by linarith
    qed
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
    have halpha_strict: "\<forall>j<nw. alpha j < alpha (Suc j)"
    proof (intro allI impI)
      fix j assume "j < nw"
      have "alpha (Suc j) = alpha j + theta j" unfolding alpha_def
        using lessThan_Suc by (by100 simp)
      with htheta_pos[rule_format, OF \<open>j < nw\<close>] show "alpha j < alpha (Suc j)" by linarith
    qed
    have halpha_0: "alpha 0 = 0" unfolding alpha_def by (by100 simp)
    \<comment> \<open>Key: uw(Suc k mod nw)/uw k = cis(theta k) for k < nw.\<close>
    have hratio_cis: "\<forall>k<nw. uw (Suc k mod nw) / uw k = cis (theta k)"
    proof (intro allI impI)
      fix k assume "k < nw"
      have "uw k \<noteq> 0" using huw_ne \<open>k < nw\<close> by (by100 auto)
      have "Suc k mod nw < nw" using hnw by (by100 simp)
      have hmod_k: "cmod (uw (Suc k mod nw) / uw k) = 1"
      proof -
        have "cmod (uw (Suc k mod nw) / uw k) = cmod (uw (Suc k mod nw)) / cmod (uw k)"
          using norm_divide[of "uw (Suc k mod nw)" "uw k"] by (by100 simp)
        also have "\<dots> = 1 / 1"
          using hmod_eq[rule_format, OF \<open>Suc k mod nw < nw\<close>] hmod_eq[rule_format, OF \<open>k < nw\<close>]
          by (by100 simp)
        finally show ?thesis by (by100 simp)
      qed
      have hne: "uw (Suc k mod nw) / uw k \<noteq> 0"
        using huw_ne[rule_format, OF \<open>Suc k mod nw < nw\<close>] \<open>uw k \<noteq> 0\<close> by (by100 auto)
      have "uw (Suc k mod nw) / uw k = cis(Arg(uw (Suc k mod nw) / uw k))"
      proof -
        from rcis_cmod_Arg[of "uw (Suc k mod nw) / uw k"]
        have "rcis (cmod(uw (Suc k mod nw) / uw k)) (Arg(uw (Suc k mod nw) / uw k)) =
              uw (Suc k mod nw) / uw k" .
        hence "of_real(cmod(uw (Suc k mod nw) / uw k)) * cis(Arg(uw (Suc k mod nw) / uw k)) =
              uw (Suc k mod nw) / uw k" unfolding rcis_def by (by100 simp)
        with hmod_k show ?thesis by (by100 simp)
      qed
      thus "uw (Suc k mod nw) / uw k = cis (theta k)" unfolding theta_def by (by100 simp)
    qed
    have hcnj_self: "\<forall>j<nw. cnj (uw j) * uw j = 1"
    proof (intro allI impI)
      fix j assume "j < nw"
      have "cnj (uw j) * uw j = of_real ((cmod (uw j))^2)"
        using complex_norm_square by (by100 simp)
      with hmod_eq[rule_format, OF \<open>j < nw\<close>] show "cnj (uw j) * uw j = 1" by (by100 simp)
    qed
    \<comment> \<open>Telescoping: uw j'/uw j = cis(alpha j' - alpha j) for j \\<le> j' < nw.\<close>
    have htelescope: "\<And>ja jb. ja \<le> jb \<Longrightarrow> jb < nw \<Longrightarrow> uw jb / uw ja = cis (alpha jb - alpha ja)"
    proof -
      fix ja jb :: nat assume "ja \<le> jb" "jb < nw"
      thus "uw jb / uw ja = cis (alpha jb - alpha ja)"
      proof (induct "jb - ja" arbitrary: jb)
        case 0 hence "jb = ja" by linarith
        have "uw ja / uw ja = 1" using huw_ne[rule_format] 0 by (by100 auto)
        with \<open>jb = ja\<close> show ?case unfolding alpha_def by (by100 simp)
      next
        case (Suc n)
        have hjb1: "jb - 1 < nw" using Suc by linarith
        have hjb1_suc: "Suc (jb - 1) = jb" using Suc by linarith
        have "Suc (jb - 1) mod nw = jb mod nw" using hjb1_suc by (by100 simp)
        also have "jb mod nw = jb" using Suc by (by100 simp)
        finally have hSmod: "Suc (jb - 1) mod nw = jb" .
        have hIH: "uw (jb - 1) / uw ja = cis (alpha (jb - 1) - alpha ja)"
          using Suc(1)[of "jb-1"] Suc(2-4) by linarith
        have hratio: "uw jb / uw (jb - 1) = cis(theta (jb - 1))"
          using hratio_cis[rule_format, OF hjb1] hSmod by (by100 simp)
        have "uw jb / uw ja = (uw jb / uw (jb - 1)) * (uw (jb - 1) / uw ja)"
          using huw_ne[rule_format, OF hjb1] by (by100 simp)
        also have "\<dots> = cis(theta(jb-1)) * cis(alpha(jb-1) - alpha ja)"
          using hratio hIH by (by100 simp)
        also have "\<dots> = cis(theta(jb-1) + (alpha(jb-1) - alpha ja))"
          using cis_mult[of "theta(jb-1)" "alpha(jb-1) - alpha ja"] by (by100 simp)
        also have "\<dots> = cis(alpha jb - alpha ja)"
        proof -
          have "alpha (Suc(jb-1)) = alpha (jb - 1) + theta (jb - 1)" unfolding alpha_def
            using lessThan_Suc by (by100 simp)
          hence "alpha jb = alpha (jb - 1) + theta (jb - 1)" using hjb1_suc by (by100 simp)
          hence "theta(jb-1) + (alpha(jb-1) - alpha ja) = alpha jb - alpha ja" by linarith
          thus ?thesis by (by100 metis)
        qed
        finally show ?case .
      qed
    qed
    have halpha_cis: "\<forall>j<nw. \<forall>j'<nw. cnj (uw j) * uw j' = cis (alpha j' - alpha j)"
    proof (intro allI impI)
      fix ja jb :: nat assume hja: "ja < nw" and hjb: "jb < nw"
      have hne_ja: "uw ja \<noteq> 0" using huw_ne hja by (by100 auto)
      have "cnj (uw ja) * uw jb = uw jb / uw ja"
      proof -
        have "cnj (uw ja) * uw jb = (cnj (uw ja) * uw ja) * (uw jb / uw ja)"
          using hne_ja by (by100 simp)
        with hcnj_self[rule_format, OF hja] show ?thesis by (by100 simp)
      qed
      also have "\<dots> = cis (alpha jb - alpha ja)"
      proof (cases "ja \<le> jb")
        case True from htelescope[OF True hjb] show ?thesis .
      next
        case False hence "jb \<le> ja" by linarith
        from htelescope[OF this hja] have h: "uw ja / uw jb = cis (alpha ja - alpha jb)" .
        have hne_jb: "uw jb \<noteq> 0" using huw_ne hjb by (by100 auto)
        have "uw jb / uw ja = inverse (uw ja / uw jb)" using hne_ja hne_jb by (by100 simp)
        also have "\<dots> = inverse (cis (alpha ja - alpha jb))" using h by (by100 simp)
        also have "\<dots> = cis (-(alpha ja - alpha jb))" by (by100 simp)
        finally show ?thesis by (by100 simp)
      qed
      finally show "cnj (uw ja) * uw jb = cis (alpha jb - alpha ja)" .
    qed
    have halpha_nw: "alpha nw = 2*pi"
    proof -
      \<comment> \<open>Product of ratios telescopes to 1.\<close>
      have hprod_cis: "(\<Prod>j<nw. uw (Suc j mod nw) / uw j) = cis (alpha nw)"
      proof -
        have "(\<Prod>j<nw. uw (Suc j mod nw) / uw j) = (\<Prod>j<nw. cis (theta j))"
        proof (rule prod.cong)
          fix j assume "j \<in> {..<nw}"
          hence "j < nw" by (by100 simp)
          from hratio_cis[rule_format, OF this] show "uw (Suc j mod nw) / uw j = cis (theta j)" .
        qed (by100 simp)
        also have "\<dots> = cis (\<Sum>j<nw. theta j)"
        proof -
          have "\<And>n. (\<Prod>j<n. cis (theta j)) = cis (\<Sum>j<n. theta j)"
          proof -
            fix n show "(\<Prod>j<n. cis (theta j)) = cis (\<Sum>j<n. theta j)"
            proof (induct n)
              case 0 thus ?case by (by100 simp)
            next
              case (Suc m)
              have "(\<Prod>j<Suc m. cis (theta j)) = (\<Prod>j<m. cis (theta j)) * cis (theta m)"
                by (by100 simp)
              also have "\<dots> = cis (\<Sum>j<m. theta j) * cis (theta m)" using Suc by (by100 simp)
              also have "\<dots> = cis ((\<Sum>j<m. theta j) + theta m)"
                using cis_mult by (by100 metis)
              also have "(\<Sum>j<m. theta j) + theta m = (\<Sum>j<Suc m. theta j)" by (by100 simp)
              finally show ?case by (by100 metis)
            qed
          qed
          thus ?thesis by (by100 simp)
        qed
        finally show ?thesis unfolding alpha_def by (by100 simp)
      qed
      have hprod_one: "(\<Prod>j<nw. uw (Suc j mod nw) / uw j) = 1"
      proof -
        \<comment> \<open>Step 1: split last factor.\<close>
        have hnw_suc: "nw = Suc(nw-1)" using hnw by linarith
        have hprod_split: "(\<Prod>j<nw. uw (Suc j mod nw) / uw j) =
            (\<Prod>j<nw-1. uw (Suc j mod nw) / uw j) * (uw 0 / uw (nw-1))"
        proof -
          have h0: "Suc(nw-1) mod nw = 0" using hnw by (by100 auto)
          have "{..<nw} = insert (nw-1) {..<nw-1}" using hnw_suc by (by100 auto)
          hence "(\<Prod>j<nw. uw (Suc j mod nw) / uw j) =
              (uw (Suc(nw-1) mod nw) / uw(nw-1)) * (\<Prod>j<nw-1. uw (Suc j mod nw) / uw j)"
            by (by100 simp)
          with h0 show ?thesis using mult.commute[of "uw 0 / uw(nw-1)"] by (by100 simp)
        qed
        \<comment> \<open>Step 2: non-wrapping terms: Suc j mod nw = Suc j for j < nw-1.\<close>
        have hprod_nomod: "(\<Prod>j<nw-1. uw (Suc j mod nw) / uw j) = (\<Prod>j<nw-1. uw (Suc j) / uw j)"
        proof (rule prod.cong)
          fix j assume "j \<in> {..<nw-1}"
          hence "j < nw-1" by (by100 auto)
          hence "Suc j < nw" by linarith
          hence "Suc j mod nw = Suc j" using hnw by (by100 auto)
          thus "uw (Suc j mod nw) / uw j = uw (Suc j) / uw j" by (by100 simp)
        qed (by100 simp)
        \<comment> \<open>Step 3: telescope \\<Prod>j<m. uw(Suc j)/uw j = uw m / uw 0.\<close>
        have "\<And>m. m \<le> nw-1 \<Longrightarrow> (\<Prod>j<m. uw (Suc j) / uw j) = uw m / uw 0"
        proof -
          fix m :: nat assume "m \<le> nw-1"
          thus "(\<Prod>j<m. uw (Suc j) / uw j) = uw m / uw 0"
          proof (induct m)
            case 0 show ?case using huw_ne hnw by (by100 auto)
          next
            case (Suc k)
            hence "k < nw" by linarith
            have "(\<Prod>j<Suc k. uw (Suc j) / uw j) = (\<Prod>j<k. uw (Suc j) / uw j) * (uw (Suc k) / uw k)"
              by (by100 simp)
            also have "(\<Prod>j<k. uw (Suc j) / uw j) = uw k / uw 0"
              using Suc by linarith
            also have "(uw k / uw 0) * (uw (Suc k) / uw k) = uw (Suc k) / uw 0"
              using huw_ne[rule_format, of k] \<open>k < nw\<close> by (by100 simp)
            finally show ?case .
          qed
        qed
        hence "(\<Prod>j<nw-1. uw (Suc j) / uw j) = uw (nw-1) / uw 0" by (by100 simp)
        \<comment> \<open>Step 4: combine.\<close>
        with hprod_split hprod_nomod
        have "(\<Prod>j<nw. uw (Suc j mod nw) / uw j) = (uw(nw-1) / uw 0) * (uw 0 / uw(nw-1))"
          by (by100 simp)
        also have "\<dots> = 1" using huw_ne[rule_format, of 0] huw_ne[rule_format, of "nw-1"] hnw
          by (by100 simp)
        finally show ?thesis .
      qed
      have hcis_eq: "cis (alpha nw) = 1" using hprod_cis hprod_one by (by100 simp)
      \<comment> \<open>alpha nw > 0 and alpha nw < nw*pi (each theta \\<in> (0, pi)).\<close>
      have halpha_pos: "alpha nw > 0"
      proof -
        have "0 < alpha (Suc 0)" using halpha_strict[rule_format, of 0] hnw halpha_0 by linarith
        moreover have "alpha (Suc 0) \<le> alpha nw"
        proof (cases "Suc 0 < nw")
          case True
          have "\<And>m n. m < n \<Longrightarrow> n \<le> nw \<Longrightarrow> alpha m < alpha n"
          proof -
            fix m n :: nat assume "m < n" "n \<le> nw"
            thus "alpha m < alpha n"
            proof (induct "n - Suc m" arbitrary: n)
              case 0 hence "n = Suc m" by linarith
              with 0 halpha_strict show ?case by (by100 simp)
            next
              case (Suc k)
              have "alpha(n-1) < alpha n"
                using halpha_strict[rule_format, of "n-1"] Suc by (by100 simp)
              moreover have "alpha m < alpha(n-1)"
                using Suc(1)[of "n-1"] Suc(2-4) by linarith
              ultimately show ?case by linarith
            qed
          qed
          from this[of "Suc 0" nw] True show ?thesis by linarith
        next
          case False hence "Suc 0 = nw" using hnw by linarith
          thus ?thesis by (by100 simp)
        qed
        ultimately show ?thesis by linarith
      qed
      have halpha_bound: "alpha nw < real nw * pi"
      proof -
        have "(\<Sum>j<nw. theta j) < (\<Sum>j<nw. pi)"
        proof (rule sum_strict_mono)
          show "finite {..<nw}" by (by100 simp)
          have "(0::nat) < nw" using hnw by linarith
          thus "{..<nw} \<noteq> ({}::nat set)" by (by100 auto)
          fix j assume "j \<in> {..<nw}"
          hence "j < nw" by (by100 simp)
          with htheta_pos show "theta j < pi" by (by100 auto)
        qed
        also have "\<dots> = real nw * pi" by (by100 simp)
        finally show ?thesis unfolding alpha_def by linarith
      qed
      \<comment> \<open>cis(alpha nw) = 1 and alpha nw \\<in> (0, nw*pi): alpha nw = 2*pi.\<close>
      \<comment> \<open>cis x = 1 iff x = 2*k*pi. With x \\<in> (0, nw*pi) and nw \\<ge> 3: only k=1 works.\<close>
      show ?thesis
      proof -
        \<comment> \<open>cis(alpha nw) = 1 means cos = 1 and sin = 0.\<close>
        from hcis_eq have hcos: "cos (alpha nw) = 1"
        proof -
          have "Re (cis (alpha nw)) = cos (alpha nw)" by (by100 simp)
          with hcis_eq show ?thesis by (by100 simp)
        qed
        \<comment> \<open>cos x = 1 with x > 0 and x < nw*pi: x = 2*pi (for nw \\<ge> 3).\<close>
        \<comment> \<open>cos x = 1 iff x = 2k*pi. With x \\<in> (0, nw*pi) and nw \\<ge> 3: k = 1.\<close>
        from cos_one_2pi_int[of "alpha nw"] hcos
        obtain k :: int where hk: "alpha nw = real_of_int k * 2 * pi" by (by100 auto)
        have "k > 0"
        proof (rule ccontr)
          assume "\<not> k > 0" hence "k \<le> 0" by linarith
          hence "real_of_int k \<le> 0" by linarith
          hence "real_of_int k * 2 \<le> 0" by linarith
          hence "real_of_int k * 2 * pi \<le> 0" using pi_ge_zero
            using mult_nonpos_nonneg[of "real_of_int k * 2" pi] by linarith
          with halpha_pos hk show False by linarith
        qed
        \<comment> \<open>Prove k = 1 using vertex distinctness from C11.\<close>
        \<comment> \<open>Step 1: All vertices are distinct (from C10 for adjacent, C11 for non-adjacent).\<close>
        have hdistinct: "\<forall>j<nw. \<forall>j'<nw. j \<noteq> j' \<longrightarrow> uw j \<noteq> uw j'"
        proof (intro allI impI)
          fix ja jb :: nat assume hja: "ja < nw" and hjb: "jb < nw" and hne: "ja \<noteq> jb"
          show "uw ja \<noteq> uw jb"
          proof
            assume heq: "uw ja = uw jb"
            \<comment> \<open>From C10 or C11, cross(uw ja, uw(ja+1)) involves uw ja. If uw ja = uw jb,
               the C11 cross product for edge ja and vertex jb would be 0, contradicting < 0.\<close>
            show False
            proof (cases "jb = Suc ja mod nw")
              case True
              \<comment> \<open>Adjacent: uw ja = uw(ja+1). C10 gives cross > 0, but cross(uw ja, uw ja) = 0.\<close>
              from hC10_im[rule_format, OF hja]
              have "Im (cnj (uw ja) * uw (Suc ja mod nw)) > 0" .
              with True heq have "Im (cnj (uw ja) * uw ja) > 0" by (by100 simp)
              moreover have "Im (cnj (uw ja) * uw ja) = 0"
              proof -
                have "cnj (uw ja) * uw ja = of_real ((cmod (uw ja))^2)"
                  using complex_norm_square by (by100 simp)
                thus ?thesis by (by100 simp)
              qed
              ultimately show False by linarith
            next
              case hadj1: False
              show False
              proof (cases "ja = Suc jb mod nw")
                case True
                \<comment> \<open>Adjacent the other way: uw jb = uw(jb+1) effectively.\<close>
                from hC10_im[rule_format, OF hjb]
                have "Im (cnj (uw jb) * uw (Suc jb mod nw)) > 0" .
                with True heq have "Im (cnj (uw jb) * uw jb) > 0" by (by100 simp)
                moreover have "Im (cnj (uw jb) * uw jb) = 0"
                proof -
                  have "cnj (uw jb) * uw jb = of_real ((cmod (uw jb))^2)"
                    using complex_norm_square by (by100 simp)
                  thus ?thesis by (by100 simp)
                qed
                ultimately show False by linarith
              next
                case hadj2: False
                \<comment> \<open>Non-adjacent: C11 gives cross < 0 but uw ja = uw jb makes cross = 0.\<close>
                have "jb \<noteq> ja" using hne by (by100 auto)
                from hC11[rule_format, OF hja hjb this hadj1]
                have "(vxw jb-vxw ja)*(vyw(Suc ja mod nw)-vyw ja)-(vyw jb-vyw ja)*(vxw(Suc ja mod nw)-vxw ja) < 0" .
                moreover from heq have "vxw jb = vxw ja \<and> vyw jb = vyw ja"
                  unfolding uw_def by (by100 auto)
                hence "(vxw jb-vxw ja)*(vyw(Suc ja mod nw)-vyw ja)-(vyw jb-vyw ja)*(vxw(Suc ja mod nw)-vxw ja) = 0"
                  by (by100 simp)
                ultimately show False by linarith
              qed
            qed
          qed
        qed
        \<comment> \<open>Step 2: Distinct vertices \\<to> distinct positions on circle \\<to> alpha differences \\<noteq> 2m\\<pi>.\<close>
        \<comment> \<open>Not needed directly; use hdistinct + halpha\\_cis instead.\<close>
        \<comment> \<open>Step 3: k = 1. Proof: show alpha(nw-1) < 2\\<pi> by contradiction using C11.\<close>
        have halphanm1_lt: "alpha (nw - 1) < 2*pi"
        proof (rule ccontr)
          assume "\<not> alpha (nw - 1) < 2*pi"
          hence halarge: "alpha (nw - 1) \<ge> 2*pi" by linarith
          \<comment> \<open>Find the crossing index: j1 with alpha(j1-1) < 2\\<pi> \\<le> alpha(j1).
             Then find j0 with alpha(j0) \\<le> alpha(j1)-2\\<pi> < alpha(j0+1).
             C11[i=j0, k=j1] gives cross < 0, but angular bracketing gives cross > 0.\<close>
          \<comment> \<open>Existence of crossing: alpha 1 < 2\\<pi> (since alpha 1 = theta 0 < \\<pi>)
             and alpha(nw-1) \\<ge> 2\\<pi>. By discrete IVT: \\<exists> j1 with alpha(j1-1) < 2\\<pi> \\<le> alpha(j1).\<close>
          have halpha1_lt: "alpha 1 < 2*pi"
            using htheta_pos[rule_format, of 0] hnw unfolding alpha_def by (by100 simp)
          \<comment> \<open>The full angular argument is complex to formalize. Use a simpler approach:
             If alpha(nw-1) \\<ge> 2\\<pi>: since alpha nw = 2k\\<pi> and alpha(nw-1) < alpha nw:
             alpha(nw-1) < 2k\\<pi>. And alpha(nw-1) \\<ge> 2\\<pi>. Each step < \\<pi>.
             For the C11 argument: use vertex j1 (first to cross 2\\<pi>) and j0 = 0.
             Since j1 \\<ge> 2 (alpha 1 < 2\\<pi> \\<le> alpha(j1)): j1 \\<noteq> 0 and j1 \\<noteq> 1.
             C11[i=0, k=j1]: cross(uw(j1)-uw 0, uw 1-uw 0) < 0.
             In sin form: sin(alpha 1 - alpha j1) + sin(alpha j1) - sin(alpha 1).
             Using 2\\<pi>-periodicity: sin(alpha j1) = sin(alpha j1 - 2\\<pi>), cos(alpha j1) = cos(alpha j1-2\\<pi>).
             Let beta = alpha j1 - 2\\<pi> \\<in> [0, \\<pi>).
             C11 value = sin(alpha 1 - beta - 2\\<pi>) + sin(beta + 2\\<pi>) - sin(alpha 1)
                       = sin(alpha 1 - beta) + sin(beta) - sin(alpha 1)
                       = sin(alpha 1)(cos beta - 1) + sin(beta)(1 - cos(alpha 1))
             Since alpha 1 \\<in> (0, \\<pi>): sin(alpha 1) > 0, 1-cos(alpha 1) > 0.
             beta \\<in> [0, \\<pi>): cos beta \\<le> 1 (so cos beta - 1 \\<le> 0), sin beta \\<ge> 0.
             If beta = 0: value = 0. But beta = 0 means alpha j1 = 2\\<pi>, so uw j1 = uw 0. Contradicts hdistinct.
             If beta > 0: sin beta > 0 and 1-cos(alpha 1) > 0, so sin(beta)(1-cos(alpha 1)) > 0.
             And |sin(alpha 1)(cos beta - 1)| = sin(alpha 1)(1-cos beta).
             Value = -sin(alpha 1)(1-cos beta) + sin(beta)(1-cos(alpha 1)).
             Using half-angle: 1-cos x = 2 sin^2(x/2), sin x = 2 sin(x/2)cos(x/2).
             Value = -2 sin(alpha 1) sin^2(beta/2) + 2 sin(beta/2)cos(beta/2) * 2 sin^2(alpha 1/2)
             Hmm too complex. Instead: for 0 < beta < alpha 1 < \\<pi>:
             value > 0 (standard inequality). For alpha 1 \\<le> beta < \\<pi>: also > 0.
             So C11 value > 0, contradicting < 0.\<close>
          \<comment> \<open>Crossing argument: alpha(nw-1) \\<ge> 2\\<pi>. Let beta = alpha(nw-1) - 2\\<pi> \\<ge> 0.
             Iterate C11 to show beta \\<ge> alpha(nw-2), hence theta(nw-2) \\<ge> 2\\<pi>. Contradiction.\<close>
          \<comment> \<open>Key lemma: for any m < nw-1 with m+1 < nw-1: if beta \\<ge> alpha m and
             C11[i=m, k=nw-1] applies (nw-1 \\<noteq> m, nw-1 \\<noteq> m+1): then beta \\<ge> alpha(m+1).
             Proof: C11 gives cross < 0. In sin form (after 2\\<pi>-reduction):
             sin(beta-alpha m) + sin(alpha(m+1)-beta) - sin(theta m) \\<ge> 0 when beta \\<in> (alpha m, alpha(m+1)).
             So beta \\<notin> (alpha m, alpha(m+1)), and with beta \\<ge> alpha m: beta \\<ge> alpha(m+1)
             (or beta = alpha m, excluded by hdistinct).\<close>
          define beta where "beta = alpha (nw - 1) - 2*pi"
          have hbeta_ge: "beta \<ge> 0" using halarge unfolding beta_def by linarith
          \<comment> \<open>Iterate: beta \\<ge> alpha m for all m < nw-1.\<close>
          have hbeta_chain: "\<forall>m. m < nw - 1 \<longrightarrow> beta \<ge> alpha m"
          proof (intro allI impI)
            fix m assume "m < nw - 1"
            thus "beta \<ge> alpha m"
            proof (induct m)
              case 0 show ?case using hbeta_ge halpha_0 by linarith
            next
              case (Suc m')
              hence hm': "m' < nw - 1" by linarith
              have hIH: "beta \<ge> alpha m'" using Suc(1)[OF hm'] .
              \<comment> \<open>Show beta \\<ge> alpha(Suc m') using C11[i=m', k=nw-1].\<close>
              \<comment> \<open>Need: m' < nw, nw-1 < nw, nw-1 \\<noteq> m', nw-1 \\<noteq> Suc m' mod nw.\<close>
              have hm'_lt: "m' < nw" using hm' by linarith
              have hnm1_lt: "nw - 1 < nw" using hnw by linarith
              have hne1: "(nw-1::nat) \<noteq> m'" using Suc by linarith
              have hne2: "(nw-1::nat) \<noteq> Suc m' mod nw"
              proof -
                have "Suc m' < nw" using Suc by linarith
                hence "Suc m' mod nw = Suc m'" using hnw by (by100 auto)
                with Suc show ?thesis by linarith
              qed
              from hC11[rule_format, OF hm'_lt hnm1_lt hne1 hne2]
              have hC11_m: "(vxw(nw-1)-vxw m')*(vyw(Suc m' mod nw)-vyw m') -
                  (vyw(nw-1)-vyw m')*(vxw(Suc m' mod nw)-vxw m') < 0" by (by100 auto)
              \<comment> \<open>Convert to sin form: cross(uw(nw-1)-uw m', uw(m'+1)-uw m')
                 = sin(alpha(m'+1) - alpha(nw-1)) + sin(alpha(nw-1) - alpha m') - sin(theta m')
                 After 2\\<pi>-reduction on alpha(nw-1) = beta + 2\\<pi>:
                 = sin(alpha(m'+1) - beta) + sin(beta - alpha m') - sin(theta m')
                 = sin(b) + sin(a) - sin(a+b) where a = beta-alpha m', b = alpha(m'+1)-beta, a+b = theta m'.
                 For a \\<in> (0, theta m'): this is > 0. C11 < 0 \\<to> a \\<notin> (0, theta m').
                 With a = beta - alpha m' \\<ge> 0 (from IH): a \\<ge> theta m', i.e., beta \\<ge> alpha(m'+1).\<close>
              \<comment> \<open>Proof: beta \\<notin> (alpha m', alpha(Suc m')). With beta \\<ge> alpha m' (IH): beta \\<ge> alpha(Suc m').
                 Case beta = alpha m': uw(nw-1) = uw m' (contradicts hdistinct).
                 Case beta \\<in> (alpha m', alpha(Suc m')): C11 value > 0, contradicts < 0.
                 Case beta \\<ge> alpha(Suc m'): done.\<close>
              show "beta \<ge> alpha (Suc m')"
              proof (rule ccontr)
                assume "\<not> beta \<ge> alpha (Suc m')"
                hence hbeta_lt: "beta < alpha (Suc m')" by linarith
                \<comment> \<open>So beta \\<in> [alpha m', alpha(Suc m')). Case beta = alpha m': contradiction from hdistinct.\<close>
                have "beta \<noteq> alpha m'"
                proof
                  assume "beta = alpha m'"
                  hence "alpha (nw-1) - alpha m' = 2*pi" unfolding beta_def by linarith
                  \<comment> \<open>cis(alpha(nw-1)-alpha m') = cis(2\\<pi>) = 1 \\<to> uw(nw-1) = uw m'.\<close>
                  hence "cnj (uw m') * uw (nw-1) = cis (2*pi)"
                    using halpha_cis[rule_format, OF hm'_lt hnm1_lt] by (by100 simp)
                  hence "cnj (uw m') * uw (nw-1) = 1" by (by100 simp)
                  moreover have "cnj (uw m') * uw m' = 1"
                    using hcnj_self[rule_format, OF hm'_lt] .
                  ultimately have "cnj (uw m') * uw (nw-1) = cnj (uw m') * uw m'" by (by100 simp)
                  hence "uw (nw-1) = uw m'"
                    using huw_ne[rule_format, OF hm'_lt] by (by100 simp)
                  with hdistinct[rule_format, OF hm'_lt hnm1_lt] hne1
                  show False by (by100 auto)
                qed
                with hIH have hbeta_strict: "beta > alpha m'" by linarith
                \<comment> \<open>beta \\<in> (alpha m', alpha(Suc m')). C11 value in sin form should be > 0.\<close>
                \<comment> \<open>C11 = cross(uw(nw-1)-uw m', uw(m'+1)-uw m') in coordinates.
                   In sin form (using halpha\\_cis + 2\\<pi> periodicity):
                   = sin(alpha(Suc m') - beta) + sin(beta - alpha m') - sin(theta m')
                   where theta m' = alpha(Suc m') - alpha m'.
                   Let a = beta - alpha m' \\<in> (0, theta m') and b = alpha(Suc m') - beta = theta m' - a.
                   sin(b) + sin(a) - sin(a+b) = 2*sin(theta m'/2)*(cos(a-theta m'/2) - cos(theta m'/2)) > 0
                   when a \\<in> (0, theta m').\<close>
                define a_val where "a_val = beta - alpha m'"
                define b_val where "b_val = alpha (Suc m') - beta"
                have ha_pos: "a_val > 0" using hbeta_strict unfolding a_val_def by linarith
                have hb_pos: "b_val > 0" using hbeta_lt unfolding b_val_def by linarith
                have hab: "a_val + b_val = alpha (Suc m') - alpha m'"
                  unfolding a_val_def b_val_def by linarith
                have htheta_m: "alpha (Suc m') - alpha m' > 0"
                  using halpha_strict[rule_format] hm' by (by100 auto)
                have htheta_m_lt_pi: "alpha (Suc m') - alpha m' < pi"
                proof -
                  have "alpha (Suc m') = alpha m' + theta m'" unfolding alpha_def
                    using lessThan_Suc by (by100 simp)
                  moreover have "theta m' < pi" using htheta_pos[rule_format, of m'] hm' by linarith
                  ultimately show ?thesis by linarith
                qed
                \<comment> \<open>The C11 coordinate value equals sin(b\\_val) + sin(a\\_val) - sin(a\\_val+b\\_val) (via cis).\<close>
                have hC11_sin_form: "(vxw(nw-1)-vxw m')*(vyw(Suc m' mod nw)-vyw m') -
                    (vyw(nw-1)-vyw m')*(vxw(Suc m' mod nw)-vxw m')
                    = sin(b_val) + sin(a_val) - sin(a_val + b_val)"
                proof -
                  have hSm'_lt: "Suc m' < nw" using Suc by linarith
                  have hSm'_mod: "Suc m' mod nw = Suc m'" using hSm'_lt hnw by (by100 auto)
                  \<comment> \<open>Step 1: Extract three Im terms via halpha\\_cis + uw\\_def.\<close>
                  have hIm_nm1_Sm: "Im(cnj(uw(nw-1)) * uw(Suc m')) = sin(alpha(Suc m') - alpha(nw-1))"
                  proof -
                    from halpha_cis[rule_format, OF hnm1_lt hSm'_lt]
                    have "cnj(uw(nw-1)) * uw(Suc m') = cis(alpha(Suc m') - alpha(nw-1))" unfolding uw_def .
                    thus ?thesis by (by100 simp)
                  qed
                  have hIm_nm1_m: "Im(cnj(uw(nw-1)) * uw m') = sin(alpha m' - alpha(nw-1))"
                  proof -
                    from halpha_cis[rule_format, OF hnm1_lt hm'_lt]
                    have "cnj(uw(nw-1)) * uw m' = cis(alpha m' - alpha(nw-1))" unfolding uw_def .
                    thus ?thesis by (by100 simp)
                  qed
                  have hIm_m_Sm: "Im(cnj(uw m') * uw(Suc m')) = sin(alpha(Suc m') - alpha m')"
                  proof -
                    from halpha_cis[rule_format, OF hm'_lt hSm'_lt]
                    have "cnj(uw m') * uw(Suc m') = cis(alpha(Suc m') - alpha m')" unfolding uw_def .
                    thus ?thesis by (by100 simp)
                  qed
                  \<comment> \<open>Step 2: Convert Im terms to coordinate cross products.\<close>
                  have hcross1: "vxw(nw-1)*vyw(Suc m') - vyw(nw-1)*vxw(Suc m') = Im(cnj(uw(nw-1))*uw(Suc m'))"
                    unfolding uw_def by (by100 simp)
                  have hcross2: "vxw(nw-1)*vyw m' - vyw(nw-1)*vxw m' = Im(cnj(uw(nw-1))*uw m')"
                    unfolding uw_def by (by100 simp)
                  have hcross3: "vxw m'*vyw(Suc m') - vyw m'*vxw(Suc m') = Im(cnj(uw m')*uw(Suc m'))"
                    unfolding uw_def by (by100 simp)
                  have hSm'_lt: "Suc m' < nw" using Suc by linarith
                  have hSm'_mod: "Suc m' mod nw = Suc m'" using hSm'_lt hnw by (by100 auto)
                  \<comment> \<open>Step 4: Substitute Im = sin and reduce 2\\<pi>-periodicity.\<close>
                  \<comment> \<open>Combine: LHS = Im1 - Im2 - Im3 = sin1 - sin2 - sin3.\<close>
                  have hLHS: "(vxw(nw-1)-vxw m')*(vyw(Suc m' mod nw)-vyw m') -
                      (vyw(nw-1)-vyw m')*(vxw(Suc m' mod nw)-vxw m')
                    = sin(alpha(Suc m') - alpha(nw-1))
                    - sin(alpha m' - alpha(nw-1))
                    - sin(alpha(Suc m') - alpha m')"
                  proof -
                    have h1: "vxw(nw-1)*vyw(Suc m') - vyw(nw-1)*vxw(Suc m') = sin(alpha(Suc m') - alpha(nw-1))"
                      using hcross1 hIm_nm1_Sm by linarith
                    have h2: "vxw(nw-1)*vyw m' - vyw(nw-1)*vxw m' = sin(alpha m' - alpha(nw-1))"
                      using hcross2 hIm_nm1_m by linarith
                    have h3: "vxw m'*vyw(Suc m') - vyw m'*vxw(Suc m') = sin(alpha(Suc m') - alpha m')"
                      using hcross3 hIm_m_Sm by linarith
                    \<comment> \<open>Bilinear expansion with Suc m' mod nw = Suc m'.\<close>
                    have "(vxw(nw-1)-vxw m')*(vyw(Suc m' mod nw)-vyw m') -
                        (vyw(nw-1)-vyw m')*(vxw(Suc m' mod nw)-vxw m')
                      = (vxw(nw-1)-vxw m')*(vyw(Suc m')-vyw m') -
                        (vyw(nw-1)-vyw m')*(vxw(Suc m')-vxw m')"
                      using hSm'_mod by (by100 simp)
                    also have "\<dots> = (vxw(nw-1)*vyw(Suc m') - vyw(nw-1)*vxw(Suc m'))
                      - (vxw(nw-1)*vyw m' - vyw(nw-1)*vxw m')
                      - (vxw m'*vyw(Suc m') - vyw m'*vxw(Suc m'))"
                      by (by100 algebra)
                    finally show ?thesis using h1 h2 h3 by linarith
                  qed
                  \<comment> \<open>Step 5: Use 2\\<pi>-periodicity. alpha(nw-1) = beta + 2\\<pi>.
                     sin(alpha(Suc m') - (beta+2\\<pi>)) = sin(alpha(Suc m') - beta) = sin(b\\_val).
                     sin(alpha m' - (beta+2\\<pi>)) = sin(alpha m' - beta) = -sin(a\\_val).\<close>
                  have hperiod1: "sin(alpha(Suc m') - alpha(nw-1)) = sin(alpha(Suc m') - beta)"
                  proof -
                    have heq: "alpha(Suc m') - beta = (alpha(Suc m') - alpha(nw-1)) + 2*pi"
                      unfolding beta_def by linarith
                    from sin_periodic[of "alpha(Suc m') - alpha(nw-1)"]
                    have "sin((alpha(Suc m') - alpha(nw-1)) + 2*pi) = sin(alpha(Suc m') - alpha(nw-1))" .
                    with heq show ?thesis by (by100 metis)
                  qed
                  have hperiod2: "sin(alpha m' - alpha(nw-1)) = sin(alpha m' - beta)"
                  proof -
                    have heq: "alpha m' - beta = (alpha m' - alpha(nw-1)) + 2*pi"
                      unfolding beta_def by linarith
                    from sin_periodic[of "alpha m' - alpha(nw-1)"]
                    have "sin((alpha m' - alpha(nw-1)) + 2*pi) = sin(alpha m' - alpha(nw-1))" .
                    with heq show ?thesis by (by100 metis)
                  qed
                  have "sin(alpha(Suc m') - beta) = sin(b_val)" unfolding b_val_def by (by100 simp)
                  moreover have "sin(alpha m' - beta) = - sin(a_val)"
                  proof -
                    have "- sin(a_val) = sin(- a_val)" using sin_minus[of a_val] by linarith
                    also have "- a_val = alpha m' - beta" unfolding a_val_def by linarith
                    finally show ?thesis by (by100 simp)
                  qed
                  moreover have "sin(alpha(Suc m') - alpha m') = sin(a_val + b_val)"
                    using hab by (by100 metis)
                  ultimately have "sin(alpha(Suc m') - alpha(nw-1)) - sin(alpha m' - alpha(nw-1)) - sin(alpha(Suc m') - alpha m')
                      = sin(b_val) - (-sin(a_val)) - sin(a_val + b_val)"
                    using hperiod1 hperiod2 by linarith
                  hence "sin(alpha(Suc m') - alpha(nw-1)) - sin(alpha m' - alpha(nw-1)) - sin(alpha(Suc m') - alpha m')
                      = sin(b_val) + sin(a_val) - sin(a_val + b_val)" by linarith
                  with hLHS show ?thesis by linarith
                qed
                \<comment> \<open>sin(b) + sin(a) - sin(a+b) > 0 for a, b > 0 and a + b < \\<pi>.\<close>
                have "sin(b_val) + sin(a_val) - sin(a_val + b_val) > 0"
                proof -
                  have "sin(a_val + b_val) = sin(a_val)*cos(b_val) + cos(a_val)*sin(b_val)"
                    using sin_add[of a_val b_val] by (by100 simp)
                  hence "sin(b_val) + sin(a_val) - sin(a_val + b_val) =
                    sin(a_val)*(1-cos(b_val)) + sin(b_val)*(1-cos(a_val))" by (by100 algebra)
                  moreover have "a_val < pi" using hab htheta_m_lt_pi hb_pos by linarith
                  moreover have "sin(a_val) > 0"
                    using sin_gt_zero[of a_val] ha_pos \<open>a_val < pi\<close> by linarith
                  moreover have "b_val < pi" using hab htheta_m_lt_pi ha_pos by linarith
                  moreover have "1 - cos(b_val) > 0"
                  proof -
                    have "b_val / 2 < 2" using \<open>b_val < pi\<close> pi_less_4 by linarith
                    have "cos(2*(b_val/2)) < 1"
                      using cos_double_less_one[of "b_val/2"] hb_pos \<open>b_val/2 < 2\<close>
                      by linarith
                    thus ?thesis by (by100 simp)
                  qed
                  moreover have "sin(b_val) > 0"
                    using sin_gt_zero[of b_val] hb_pos \<open>b_val < pi\<close> by linarith
                  moreover have "1 - cos(a_val) > 0"
                  proof -
                    have "a_val / 2 < 2" using \<open>a_val < pi\<close> pi_less_4 by linarith
                    have "cos(2*(a_val/2)) < 1"
                      using cos_double_less_one[of "a_val/2"] ha_pos \<open>a_val/2 < 2\<close>
                      by linarith
                    thus ?thesis by (by100 simp)
                  qed
                  ultimately show ?thesis
                  proof -
                    assume h1: "sin(b_val) + sin(a_val) - sin(a_val + b_val) =
                      sin(a_val)*(1-cos(b_val)) + sin(b_val)*(1-cos(a_val))"
                    assume h2: "a_val < pi" and h3: "sin(a_val) > 0"
                    assume h4: "b_val < pi" and h5: "1 - cos(b_val) > 0"
                    assume h6: "sin(b_val) > 0" and h7: "1 - cos(a_val) > 0"
                    have "sin(a_val)*(1-cos(b_val)) > 0"
                      using mult_pos_pos[OF h3 h5] .
                    moreover have "sin(b_val)*(1-cos(a_val)) > 0"
                      using mult_pos_pos[OF h6 h7] .
                    ultimately show ?thesis using h1 by linarith
                  qed
                qed
                \<comment> \<open>So C11 coordinate value > 0. But hC11\\_m says < 0. Contradiction.\<close>
                with hC11_sin_form hC11_m show False by linarith
              qed
            qed
          qed
          \<comment> \<open>In particular: beta \\<ge> alpha(nw-2).\<close>
          have "beta \<ge> alpha (nw - 2)"
          proof -
            have "nw - 2 < nw - 1" using hnw by linarith
            from hbeta_chain[rule_format, OF this] show ?thesis .
          qed
          \<comment> \<open>But beta = alpha(nw-1) - 2\\<pi> = alpha(nw-2) + theta(nw-2) - 2\\<pi>.\<close>
          have "beta = alpha (nw - 2) + theta (nw - 2) - 2*pi"
          proof -
            have "Suc (nw - 2) = nw - 1" using hnw by linarith
            have "alpha (Suc (nw-2)) = alpha (nw-2) + theta (nw-2)" unfolding alpha_def
              using lessThan_Suc by (by100 simp)
            hence "alpha (nw - 1) = alpha (nw - 2) + theta (nw - 2)"
              using \<open>Suc (nw-2) = nw-1\<close> by (by100 simp)
            thus ?thesis unfolding beta_def by linarith
          qed
          \<comment> \<open>So alpha(nw-2) + theta(nw-2) - 2\\<pi> \\<ge> alpha(nw-2), i.e., theta(nw-2) \\<ge> 2\\<pi>.\<close>
          hence "theta (nw - 2) \<ge> 2*pi" using \<open>beta \<ge> alpha (nw - 2)\<close> by linarith
          \<comment> \<open>But theta(nw-2) < \\<pi>. Contradiction.\<close>
          moreover have "theta (nw - 2) < pi" using htheta_pos hnw by (by100 auto)
          ultimately show False using pi_gt_zero by linarith
        qed
        have "2 * real_of_int k * pi = alpha nw" using hk by linarith
        also have "\<dots> = alpha (nw - 1) + theta (nw - 1)"
        proof -
          have "alpha (Suc (nw-1)) = alpha (nw-1) + theta (nw-1)" unfolding alpha_def
            using lessThan_Suc by (by100 simp)
          moreover have "Suc (nw - 1) = nw" using hnw by linarith
          ultimately show ?thesis by (by100 simp)
        qed
        also have "\<dots> < 2*pi + pi" using halphanm1_lt htheta_pos[rule_format, of "nw-1"] hnw by linarith
        finally have "2 * real_of_int k * pi < 2*pi + pi" .
        hence "real_of_int k * 2 * pi < 3*pi" by linarith
        hence "real_of_int k * 2 < 3" using pi_gt_zero by (by100 simp)
        with \<open>k > 0\<close> have "k = 1" by linarith
        with hk show ?thesis by (by100 auto)
      qed
    qed
    show ?thesis
    proof (rule exI[of _ alpha])
      show "(\<forall>j<nw. \<forall>j'<nw. cnj (Complex (vxw j) (vyw j)) * Complex (vxw j') (vyw j') =
          cis (alpha j' - alpha j)) \<and>
        (\<forall>j<nw. alpha j < alpha (Suc j)) \<and> alpha 0 = 0 \<and> alpha nw = 2 * pi"
        using halpha_cis halpha_strict halpha_0 halpha_nw unfolding uw_def by (by100 auto)
    qed
  qed

end
