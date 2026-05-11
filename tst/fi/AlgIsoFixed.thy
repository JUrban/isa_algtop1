theory AlgIsoFixed
imports AlgTopC.AlgTopCached
begin

text \<open>Fixed versions of theorems that should state a SPECIFIC MAP is an isomorphism,
  not just that the groups are abstractly isomorphic.
  See REPORT_wrong_iso_statements.md for details.\<close>

section \<open>Copied infrastructure (sorry-free, from AlgTop.thy)\<close>

text \<open>These lemmas are proved in AlgTop.thy but not accessible from this session.
  Copied verbatim. Both are sorry-free (verified by thm\_oracles).\<close>

lemma SCC_pi1_iso_Z:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
      and "c0 \<in> C"
  shows "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier C
        (subspace_topology top1_S2 top1_S2_topology C) c0)
      (top1_fundamental_group_mul C
        (subspace_topology top1_S2 top1_S2_topology C) c0)
      top1_Z_group top1_Z_mul"
proof -
  let ?TC = "subspace_topology top1_S2 top1_S2_topology C"
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hC_sub_S2: "C \<subseteq> top1_S2" using simple_closed_curve_subset[OF assms(2)] .
  obtain f where hf_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S2 top1_S2_topology f"
      and hf_inj: "inj_on f top1_S1" and hf_img: "f ` top1_S1 = C"
    using assms(2) unfolding top1_simple_closed_curve_on_def by (by100 blast)
  have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
    using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
  have hTC_top: "is_topology_on C ?TC"
    by (rule subspace_topology_is_topology_on[OF hTopS2 hC_sub_S2])
  have hf_all_C: "\<And>s. s \<in> top1_S1 \<Longrightarrow> f s \<in> C"
  proof -
    fix s assume "s \<in> top1_S1"
    hence "f s \<in> f ` top1_S1" by (rule imageI)
    thus "f s \<in> C" using hf_img by simp
  qed
  have hf_cont_C: "top1_continuous_map_on top1_S1 top1_S1_topology C ?TC f"
    by (intro continuous_map_restrict_codomain[OF hf_cont _ hC_sub_S2] ballI)
       (rule hf_all_C)
  have hf_bij: "bij_betw f top1_S1 C"
    unfolding bij_betw_def using hf_inj hf_img by (by100 blast)
  have hC_haus: "is_hausdorff_on C ?TC"
    using conjunct2[OF conjunct2[OF Theorem_17_11]] hC_sub_S2 top1_S2_is_hausdorff
    by (by100 blast)
  have hf_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology C ?TC f"
    by (rule Theorem_26_6[OF hS1_top hTC_top S1_compact hC_haus hf_cont_C hf_bij])
  obtain s0 where hs0: "s0 \<in> top1_S1" "f s0 = c0"
    using hf_img assms(3) by (by100 blast)
  have h_pi1_S1_C: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology s0)
      (top1_fundamental_group_mul top1_S1 top1_S1_topology s0)
      (top1_fundamental_group_carrier C ?TC c0)
      (top1_fundamental_group_mul C ?TC c0)"
    by (rule Corollary_52_5_homeomorphism_iso[OF hS1_top hTC_top hf_homeo hs0(1) hs0(2)])
  have h10_S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
  have h_pi1_S1_bp: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1::real, 0::real))
      (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology s0)
      (top1_fundamental_group_mul top1_S1 top1_S1_topology s0)"
  proof -
    obtain \<gamma> where "top1_is_path_on top1_S1 top1_S1_topology (1, 0) s0 \<gamma>"
      using S1_path_connected h10_S1 hs0(1) unfolding top1_path_connected_on_def
      by (by100 blast)
    thus ?thesis by (rule basepoint_change_iso_via_path[OF hS1_top])
  qed
  have h_pi1_S1_Z: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
      top1_Z_group top1_Z_mul"
    by (rule Theorem_54_5_iso)
  \<comment> \<open>Chain: \<pi>_1(C,c0) \<cong> \<pi>_1(S1,s0) \<cong> \<pi>_1(S1,(1,0)) \<cong> Z.\<close>
  have h_pi1_S1_C_sym: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier C ?TC c0)
      (top1_fundamental_group_mul C ?TC c0)
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology s0)
      (top1_fundamental_group_mul top1_S1 top1_S1_topology s0)"
  proof (rule top1_groups_isomorphic_on_sym[OF h_pi1_S1_C])
    show "top1_is_group_on (top1_fundamental_group_carrier top1_S1 top1_S1_topology s0)
        (top1_fundamental_group_mul top1_S1 top1_S1_topology s0)
        (top1_fundamental_group_id top1_S1 top1_S1_topology s0)
        (top1_fundamental_group_invg top1_S1 top1_S1_topology s0)"
      by (rule top1_fundamental_group_is_group[OF hS1_top hs0(1)])
    have "c0 \<in> C" by (rule assms(3))
    show "top1_is_group_on (top1_fundamental_group_carrier C ?TC c0)
        (top1_fundamental_group_mul C ?TC c0)
        (top1_fundamental_group_id C ?TC c0)
        (top1_fundamental_group_invg C ?TC c0)"
      by (rule top1_fundamental_group_is_group[OF hTC_top \<open>c0 \<in> C\<close>])
  qed
  have h_pi1_S1_bp_sym: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology s0)
      (top1_fundamental_group_mul top1_S1 top1_S1_topology s0)
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))"
  proof (rule top1_groups_isomorphic_on_sym[OF h_pi1_S1_bp])
    show "top1_is_group_on (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1::real, 0::real))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_id top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_invg top1_S1 top1_S1_topology (1, 0))"
      by (rule top1_fundamental_group_is_group[OF hS1_top h10_S1])
    show "top1_is_group_on (top1_fundamental_group_carrier top1_S1 top1_S1_topology s0)
        (top1_fundamental_group_mul top1_S1 top1_S1_topology s0)
        (top1_fundamental_group_id top1_S1 top1_S1_topology s0)
        (top1_fundamental_group_invg top1_S1 top1_S1_topology s0)"
      by (rule top1_fundamental_group_is_group[OF hS1_top hs0(1)])
  qed
  have h1: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier C ?TC c0)
      (top1_fundamental_group_mul C ?TC c0)
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))"
    by (rule groups_isomorphic_trans_fwd[OF h_pi1_S1_C_sym h_pi1_S1_bp_sym])
  show ?thesis
    by (rule groups_isomorphic_trans_fwd[OF h1 h_pi1_S1_Z])
qed

lemma Theorem_63_1_b_generation:
  assumes "is_topology_on X TX"
      and "openin_on X TX U" and "openin_on X TX V" and "U \<union> V = X"
      and "U \<inter> V = A \<union> B" and "A \<inter> B = {}"
      and "openin_on X TX A" and "openin_on X TX B"
      and "a \<in> A" and "b \<in> B"
      and "top1_is_path_on U (subspace_topology X TX U) a b \<alpha>"
      and "top1_is_path_on V (subspace_topology X TX V) b a \<beta>"
      \<comment> \<open>\<pi>_1(X, a) is infinite cyclic with some generator gen.\<close>
      and "\<exists>gen. top1_is_loop_on X TX a gen \<and>
        (\<forall>f. top1_is_loop_on X TX a f \<longrightarrow>
          (\<exists>n::nat. top1_path_homotopic_on X TX a a f (top1_path_power gen a n)
            \<or> top1_path_homotopic_on X TX a a f
                 (top1_path_power (top1_path_reverse gen) a n)))"
  shows "\<forall>f. top1_is_loop_on X TX a f \<longrightarrow>
    (\<exists>n::nat. top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_product \<alpha> \<beta>) a n)
      \<or> top1_path_homotopic_on X TX a a f
           (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n))"
proof -
  \<comment> \<open>Step 1: Construct helix covering.\<close>
  have ha_U: "a \<in> U" using assms(5,9) by (by100 blast)
  define E :: "('a \<times> int) set" where
    "E = {(x, m). (even m \<and> x \<in> U) \<or> (odd m \<and> x \<in> V - U)}"
  define TE :: "('a \<times> int) set set" where
    "TE = {W. W \<subseteq> E \<and>
      (\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX) \<and>
      (\<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX)}"
  define p0 :: "'a \<times> int \<Rightarrow> 'a" where "p0 = fst"
  have he0: "(a, 0::int) \<in> E" unfolding E_def using ha_U by simp
  have hp0: "p0 (a, 0::int) = a" unfolding p0_def by simp
  have hcov_TE: "top1_covering_map_on E TE X TX p0 \<and> is_topology_on E TE"
  proof -
    note h = helix_covering_construction[OF assms(1-8)]
    have "E = {x. even (snd x) \<and> fst x \<in> U \<or> odd (snd x) \<and> fst x \<in> V - U}"
      unfolding E_def by auto
    moreover have "TE = {W. W \<subseteq> E \<and>
        (\<forall>n. {x \<in> U. (x, 2 * n) \<in> W} \<in> TX) \<and>
        (\<forall>n. {x \<in> A. (x, 2 * n + 2) \<in> W} \<union> {x \<in> B. (x, 2 * n) \<in> W} \<union>
              {x \<in> V - U. (x, 2 * n + 1) \<in> W} \<in> TX)}"
      unfolding TE_def E_def by auto
    moreover have "p0 = fst" unfolding p0_def by simp
    ultimately show ?thesis using h by simp
  qed
  hence hTE: "is_topology_on E TE" and hcov: "top1_covering_map_on E TE X TX p0" by auto
  \<comment> \<open>Step 2: (\<alpha>*\<beta>)^m lifts from (a,0) to (a, 2m).\<close>
  have hfm_lift: "\<And>m. \<exists>ftm. top1_is_path_on E TE (a, 0) (a, 2 * int m) ftm \<and>
      (\<forall>s\<in>I_set. p0 (ftm s) = top1_path_power (top1_path_product \<alpha> \<beta>) a m s)"
  proof -
    fix m :: nat
    show "\<exists>ftm. top1_is_path_on E TE (a, 0) (a, 2 * int m) ftm \<and>
        (\<forall>s\<in>I_set. p0 (ftm s) = top1_path_power (top1_path_product \<alpha> \<beta>) a m s)"
    proof (rule helix_f_power_lift[OF assms(1-12) hcov hTE he0 hp0])
      show "\<And>W n. W \<in> TE \<Longrightarrow> {x \<in> U. (x, 2 * n) \<in> W} \<in> TX"
        unfolding TE_def by (by100 blast)
      show "\<And>W n. W \<in> TE \<Longrightarrow> {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
          {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX"
        unfolding TE_def by (by100 blast)
      show "\<And>x n. x \<in> U \<Longrightarrow> (x, 2*n) \<in> E" unfolding E_def by auto
      show "\<And>x n. x \<in> V - U \<Longrightarrow> (x, 2*n + 1) \<in> E" unfolding E_def by auto
      show "\<And>x n. x \<in> A \<Longrightarrow> (x, 2*n + 2) \<in> E"
        using assms(5) unfolding E_def by auto
      show "\<And>x n. x \<in> B \<Longrightarrow> (x, 2*n) \<in> E"
        using assms(5) unfolding E_def by auto
      show "p0 = fst" unfolding p0_def by simp
      show "\<And>x m. (x, m) \<in> E \<Longrightarrow> (even m \<and> x \<in> U) \<or> (odd m \<and> x \<in> V - U)"
        unfolding E_def by auto
      show "\<And>W. \<lbrakk>W \<subseteq> E; \<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX;
          \<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                    {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX\<rbrakk> \<Longrightarrow> W \<in> TE"
        unfolding TE_def by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 3: From assms(13), \<pi>_1(X) is infinite cyclic with generator gen.\<close>
  obtain gen where hgen_loop: "top1_is_loop_on X TX a gen"
      and hgen_all: "\<forall>f. top1_is_loop_on X TX a f \<longrightarrow>
        (\<exists>n::nat. top1_path_homotopic_on X TX a a f (top1_path_power gen a n)
          \<or> top1_path_homotopic_on X TX a a f
               (top1_path_power (top1_path_reverse gen) a n))"
    using assms(13) by blast
  \<comment> \<open>Step 4: [\<alpha>*\<beta>] is nontrivial (from Theorem\_63\_1\_loop\_nontrivial).\<close>
  have h\<alpha>\<beta>_nontrivial: "\<not> top1_path_homotopic_on X TX a a
      (top1_path_product \<alpha> \<beta>) (top1_constant_path a)"
    by (rule Theorem_63_1_loop_nontrivial[OF assms(1-12)])
  \<comment> \<open>Step 5: [\<alpha>*\<beta>] = gen^k for some k with k \<noteq> 0.\<close>
  have h\<alpha>\<beta>_loop: "top1_is_loop_on X TX a (top1_path_product \<alpha> \<beta>)"
  proof -
    have hU_sub: "U \<subseteq> X" using assms(2) unfolding openin_on_def by (by100 blast)
    have hV_sub: "V \<subseteq> X" using assms(3) unfolding openin_on_def by (by100 blast)
    have hTU: "is_topology_on U (subspace_topology X TX U)"
      by (rule subspace_topology_is_topology_on[OF assms(1) hU_sub])
    have hTV: "is_topology_on V (subspace_topology X TX V)"
      by (rule subspace_topology_is_topology_on[OF assms(1) hV_sub])
    have h\<alpha>_X: "top1_is_path_on X TX a b \<alpha>"
      by (rule path_in_subspace_is_path_in_ambient'[OF assms(1) hU_sub assms(11)])
    have h\<beta>_X: "top1_is_path_on X TX b a \<beta>"
      by (rule path_in_subspace_is_path_in_ambient'[OF assms(1) hV_sub assms(12)])
    show ?thesis unfolding top1_is_loop_on_def
      by (rule top1_path_product_is_path[OF assms(1) h\<alpha>_X h\<beta>_X])
  qed
  obtain k :: nat where hk: "top1_path_homotopic_on X TX a a
      (top1_path_product \<alpha> \<beta>) (top1_path_power gen a k)
    \<or> top1_path_homotopic_on X TX a a
      (top1_path_product \<alpha> \<beta>) (top1_path_power (top1_path_reverse gen) a k)"
    using hgen_all[THEN spec, of "top1_path_product \<alpha> \<beta>"] h\<alpha>\<beta>_loop by blast
  have hk_ne: "k \<noteq> 0"
  proof
    assume "k = 0"
    hence "top1_path_homotopic_on X TX a a
        (top1_path_product \<alpha> \<beta>) (top1_constant_path a)"
      using hk by simp
    thus False using h\<alpha>\<beta>_nontrivial by contradiction
  qed
  \<comment> \<open>Step 6: The shift T(x,n) = (x, n+2) is a covering automorphism of E.
     This gives: if gen lifts from (a,0) to (a,2d), then gen^k lifts to (a,2kd).
     Since gen^k = [\<alpha>*\<beta>] lifts to (a,2): kd = 1, so k = \<plusminus>1.\<close>
  \<comment> \<open>Step 6a: The lift of gen from (a,0) exists and ends at some (a, 2d).\<close>
  have hgen_path: "top1_is_path_on X TX a a gen"
    using hgen_loop unfolding top1_is_loop_on_def by (by100 blast)
  obtain gen_lift where hgen_lift: "top1_is_path_on E TE (a, 0) (gen_lift 1) gen_lift"
      and hgen_lift_proj: "\<forall>s\<in>I_set. p0 (gen_lift s) = gen s"
    using Lemma_54_1_path_lifting[OF hcov he0 hp0 hgen_path assms(1) hTE] by blast
  \<comment> \<open>gen\_lift ends at some point in the fiber at a = \{(a, 2n) : n \<in> Z\}.\<close>
  have hgen_end_fiber: "\<exists>d :: int. gen_lift 1 = (a, 2 * d)"
  proof -
    have h1_I: "(1::real) \<in> I_set"
      unfolding top1_unit_interval_def by (by100 simp)
    have hend_E: "gen_lift 1 \<in> E"
      using hgen_lift unfolding top1_is_path_on_def top1_continuous_map_on_def
      using h1_I by (by100 blast)
    have hp0_gen1: "p0 (gen_lift 1) = gen 1"
      using hgen_lift_proj h1_I by (by100 blast)
    have hgen1_a: "gen 1 = a"
      using hgen_loop unfolding top1_is_loop_on_def top1_is_path_on_def
      by (by100 blast)
    have hend_proj: "p0 (gen_lift 1) = a"
      using hp0_gen1 hgen1_a by simp
    hence hfst: "fst (gen_lift 1) = a" unfolding p0_def by simp
    obtain x' n' where hpair: "gen_lift 1 = (x', n')" by (cases "gen_lift 1")
    hence "x' = a" using hfst by simp
    have "(x', n') \<in> E" using hend_E hpair by simp
    hence "(even n' \<and> x' \<in> U) \<or> (odd n' \<and> x' \<in> V - U)" unfolding E_def by auto
    hence "even n'"
    proof
      assume "even n' \<and> x' \<in> U" thus "even n'" by simp
    next
      assume "odd n' \<and> x' \<in> V - U"
      hence "x' \<in> V - U" by simp
      hence "a \<in> V - U" using \<open>x' = a\<close> by simp
      hence False using ha_U by (by100 blast)
      thus "even n'" by simp
    qed
    then obtain d where "n' = 2 * d" using evenE by blast
    hence "gen_lift 1 = (a, 2 * d)" using hpair \<open>x' = a\<close> by simp
    thus ?thesis by blast
  qed
  obtain d :: int where hgen_end: "gen_lift 1 = (a, 2 * d)"
    using hgen_end_fiber by blast
  \<comment> \<open>Step 6b: The shift T is a covering automorphism.\<close>
  \<comment> \<open>Step 6c: gen^k lifts from (a,0) to (a, 2kd) by applying T iteratively.\<close>
  \<comment> \<open>Step 6d: gen^k \<simeq> \<alpha>*\<beta>, and \<alpha>*\<beta> lifts to (a, 2). By Theorem\_54\_3: 2kd = 2.
     So kd = 1 with k \<in> N, d \<in> Z. If k = 0: already excluded. k \<ge> 1.
     Integer solutions to kd = 1: (k,d) = (1,1). So k = 1.\<close>
  \<comment> \<open>If [\<alpha>*\<beta>] = gen^k: k = 1 (positive case). If [\<alpha>*\<beta>] = gen^{-k}: k = 1 too.\<close>
  \<comment> \<open>Lift of (\<alpha>*\<beta>) (= m=1 case) from (a,0) to (a, 2).\<close>
  \<comment> \<open>(\<alpha>*\<beta>) lifts from (a,0) to (a, 2): from hfm\_lift with m = 1.\<close>
  obtain ab_lift where hab_lift: "top1_is_path_on E TE (a, 0) (a, 2) ab_lift"
      and hab_lift_proj: "\<forall>s\<in>I_set. p0 (ab_lift s) =
          top1_path_power (top1_path_product \<alpha> \<beta>) a 1 s"
  proof -
    obtain ftm where hftm: "top1_is_path_on E TE (a, 0) (a, 2 * int (1::nat)) ftm"
        "\<forall>s\<in>I_set. p0 (ftm s) = top1_path_power (top1_path_product \<alpha> \<beta>) a 1 s"
      using hfm_lift[of 1] by blast
    have "2 * int (1::nat) = (2::int)" by simp
    hence "top1_is_path_on E TE (a, 0) (a, 2) ftm" using hftm(1) by simp
    thus ?thesis using hftm(2) that by blast
  qed
  \<comment> \<open>gen^k lifts from (a,0) to (a, 2*int(k)*d).
     This uses the helix shift automorphism T(x,n) = (x, n+2).
     By induction on k: the lift of gen^k concatenates k lifts of gen,
     each shifted by T, giving endpoint (a, 2*k*d).\<close>
  \<comment> \<open>Define the helix shift T(x,n) = (x, n + 2*d). This maps a lift of gen
     from (a, 0) to a lift from (a, 2*d), from (a, 2*d) to (a, 4*d), etc.\<close>
  \<comment> \<open>Actually, we use the general shift T\_d(x,n) = (x, n + 2*d).
     For d = 1: this is the standard period-1 shift.
     The key property: T\_d is a covering automorphism.
     For arbitrary d: T\_d = T\_1^d where T\_1(x,n) = (x, n+2) is period-1.\<close>
  \<comment> \<open>The lift of gen from (a, 2*j*d) ends at (a, 2*(j+1)*d).
     This follows from the shift T\_d being a covering automorphism.\<close>
  \<comment> \<open>Define the period-1 helix shift T1(x,n) = (x, n+2).\<close>
  define T1 :: "('a \<times> int) \<Rightarrow> ('a \<times> int)" where "T1 = (\<lambda>(x, n). (x, n + 2))"
  \<comment> \<open>T1 maps E to E (parity of n preserved by adding 2).\<close>
  have hT1_E: "\<And>e. e \<in> E \<Longrightarrow> T1 e \<in> E"
    unfolding T1_def E_def by auto
  \<comment> \<open>p0 \<circ> T1 = p0.\<close>
  have hT1_proj: "\<And>e. p0 (T1 e) = p0 e"
    unfolding T1_def p0_def by auto
  \<comment> \<open>T1 is continuous: T1\<inverse>(W) \<in> TE for W \<in> TE.
     Key: T1\<inverse>(W) = \{(x,n) : (x, n+2) \<in> W\}.
     Slice conditions: \{x \<in> U. (x, 2n) \<in> T1\<inverse>(W)\} = \{x \<in> U. (x, 2(n+1)) \<in> W\} \<in> TX.\<close>
  have hT1_cont: "top1_continuous_map_on E TE E TE T1"
  proof -
    note h = helix_shift_general_continuous[OF assms(1-3) assms(5) assms(7-8), of 1]
    have "E = {x :: ('a \<times> int). even (snd x) \<and> fst x \<in> U \<or> odd (snd x) \<and> fst x \<in> V - U}"
      unfolding E_def by auto
    moreover have "TE = {W. W \<subseteq> E \<and>
        (\<forall>n. {x \<in> U. (x, 2 * n) \<in> W} \<in> TX) \<and>
        (\<forall>n. {x \<in> A. (x, 2 * n + 2) \<in> W} \<union> {x \<in> B. (x, 2 * n) \<in> W} \<union>
              {x \<in> V - U. (x, 2 * n + 1) \<in> W} \<in> TX)}"
      unfolding TE_def E_def by auto
    moreover have "T1 = (\<lambda>(x :: 'a, n :: int). (x, n + 2 * (1::int)))" unfolding T1_def by auto
    ultimately show ?thesis using h by simp
  qed
  \<comment> \<open>The lift of gen from (a, 2*j) ends at (a, 2*j + 2*d) for any j.
     Proof: by covering\_lift\_unique\_connected, the lift from (a, 2*j) is
     T1^j \<circ> gen\_lift (since T1^j shifts by 2j, and the projection is unchanged).
     Then its endpoint is T1^j(gen\_lift 1) = T1^j(a, 2d) = (a, 2d + 2j).\<close>
  \<comment> \<open>More precisely: define T1_pow j (x,n) = (x, n + 2*j). Then:
     T1\_pow j \<circ> gen\_lift is a path from (a, 2*j) to (a, 2*d + 2*j) in E
     projecting to gen. By covering\_lift\_unique\_connected, this is THE unique lift
     of gen from (a, 2*j).\<close>
  \<comment> \<open>gen^k lift by induction: gen * shifted(gen^{k-1}), matching path\_power definition.
     path\_power gen a (Suc k') = gen * gen^{k'}.
     So: gen\_lift from (a,0) to (a,2d), then shifted gen^{k'} lift from (a,2d) to (a,2d+2k'd).\<close>
  have hgenk_lift: "\<exists>ftk. top1_is_path_on E TE (a, 0) (a, 2 * int k * d) ftk \<and>
      (\<forall>s\<in>I_set. p0 (ftk s) = top1_path_power gen a k s)"
  proof (induct k)
    case 0
    define ftk0 :: "real \<Rightarrow> ('a \<times> int)" where "ftk0 = (\<lambda>s. (a, 0::int))"
    have "top1_is_path_on E TE (a, 0) (a, 2 * int 0 * d) ftk0"
    proof -
      have "top1_is_path_on E TE (a, 0) (a, 0) ftk0"
        unfolding top1_is_path_on_def ftk0_def
      proof (intro conjI)
        have "top1_continuous_map_on I_set I_top E TE (top1_constant_path (a, 0::int))"
          by (rule top1_constant_path_continuous[OF hTE he0])
        thus "top1_continuous_map_on I_set I_top E TE (\<lambda>s. (a, 0::int))"
          unfolding top1_constant_path_def by simp
      qed simp+
      thus ?thesis by simp
    qed
    moreover have "\<forall>s\<in>I_set. p0 (ftk0 s) = top1_path_power gen a 0 s"
    proof (intro ballI)
      fix s assume "s \<in> I_set"
      show "p0 (ftk0 s) = top1_path_power gen a 0 s"
        unfolding ftk0_def p0_def by (simp add: top1_constant_path_def)
    qed
    ultimately show ?case by blast
  next
    case (Suc k')
    obtain ftk' where hftk': "top1_is_path_on E TE (a, 0) (a, 2 * int k' * d) ftk'"
        "\<forall>s\<in>I_set. p0 (ftk' s) = top1_path_power gen a k' s"
      using Suc.hyps by blast
    \<comment> \<open>Shift ftk' by d periods: T\_d(x,n) = (x, n+2d). Then T\_d \<circ> ftk' is a
       path from (a, 2d) to (a, 2d + 2k'd) = (a, 2(k'+1)d) in E,
       projecting to gen^{k'} (since p0 \<circ> T\_d = p0).\<close>
    define T_d :: "('a \<times> int) \<Rightarrow> ('a \<times> int)" where "T_d = (\<lambda>(x, n). (x, n + 2*d))"
    define ftk'_shifted :: "real \<Rightarrow> ('a \<times> int)"
      where "ftk'_shifted = T_d \<circ> ftk'"
    have hTd_cont: "top1_continuous_map_on E TE E TE T_d"
    proof -
      note h = helix_shift_general_continuous[OF assms(1-3) assms(5) assms(7-8)]
      have "E = {x :: ('a \<times> int). even (snd x) \<and> fst x \<in> U \<or> odd (snd x) \<and> fst x \<in> V - U}"
        unfolding E_def by auto
      moreover have "TE = {W. W \<subseteq> E \<and>
          (\<forall>n. {x \<in> U. (x, 2 * n) \<in> W} \<in> TX) \<and>
          (\<forall>n. {x \<in> A. (x, 2 * n + 2) \<in> W} \<union> {x \<in> B. (x, 2 * n) \<in> W} \<union>
                {x \<in> V - U. (x, 2 * n + 1) \<in> W} \<in> TX)}"
        unfolding TE_def E_def by auto
      moreover have "T_d = (\<lambda>(x :: 'a, n :: int). (x, n + 2 * d))" unfolding T_d_def by auto
      ultimately show ?thesis using h by simp
    qed
    have hTd_proj: "\<And>e. p0 (T_d e) = p0 e" unfolding T_d_def p0_def by auto
    \<comment> \<open>ftk'\_shifted is a path from (a, 2d) to (a, 2d + 2k'd) in E.\<close>
    have hftk'_shifted_path: "top1_is_path_on E TE (a, 2 * d) (a, 2 * d + 2 * int k' * d) ftk'_shifted"
    proof -
      have hcomp_cont: "top1_continuous_map_on I_set I_top E TE ftk'_shifted"
        unfolding ftk'_shifted_def
        by (rule top1_continuous_map_on_comp[where Y=E and TY=TE])
           (use hftk'(1) hTd_cont in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
      have hstart: "ftk'_shifted 0 = (a, 2 * d)"
        unfolding ftk'_shifted_def T_d_def using hftk'(1)
        unfolding top1_is_path_on_def by (by100 simp)
      have hend: "ftk'_shifted 1 = (a, 2 * d + 2 * int k' * d)"
        unfolding ftk'_shifted_def T_d_def using hftk'(1)
        unfolding top1_is_path_on_def by (by100 simp)
      show ?thesis unfolding top1_is_path_on_def
        using hcomp_cont hstart hend by (by100 blast)
    qed
    have hftk'_shifted_proj: "\<forall>s\<in>I_set. p0 (ftk'_shifted s) = top1_path_power gen a k' s"
    proof (intro ballI)
      fix s assume "s \<in> I_set"
      have "p0 (ftk'_shifted s) = p0 (T_d (ftk' s))" unfolding ftk'_shifted_def by simp
      also have "... = p0 (ftk' s)" by (rule hTd_proj)
      also have "... = top1_path_power gen a k' s" using hftk'(2) \<open>s \<in> I_set\<close> by (by100 blast)
      finally show "p0 (ftk'_shifted s) = top1_path_power gen a k' s" .
    qed
    \<comment> \<open>Concatenate: gen * shifted(gen^{k'}) = gen^{Suc k'}.\<close>
    have h_endpoint_eq: "2 * d + 2 * int k' * d = 2 * int (Suc k') * d"
      by (simp add: algebra_simps)
    \<comment> \<open>gen\_lift goes (a,0)\<rightarrow>(a,2d), ftk'\_shifted goes (a,2d)\<rightarrow>(a,2d+2k'd).\<close>
    have hgen_lift_typed: "top1_is_path_on E TE (a, 0) (a, 2 * d) gen_lift"
      using hgen_lift hgen_end by simp
    define ftk_suc where "ftk_suc = top1_path_product gen_lift ftk'_shifted"
    have "top1_is_path_on E TE (a, 0) (a, 2 * int (Suc k') * d) ftk_suc"
    proof -
      have "top1_is_path_on E TE (a, 0) (a, 2 * d + 2 * int k' * d)
          (top1_path_product gen_lift ftk'_shifted)"
        by (rule top1_path_product_is_path[OF hTE hgen_lift_typed hftk'_shifted_path])
      thus ?thesis unfolding ftk_suc_def using h_endpoint_eq by simp
    qed
    moreover have "\<forall>s\<in>I_set. p0 (ftk_suc s) = top1_path_power gen a (Suc k') s"
    proof (intro ballI)
      fix s :: real assume hs: "s \<in> I_set"
      have "p0 (ftk_suc s) = p0 (top1_path_product gen_lift ftk'_shifted s)"
        unfolding ftk_suc_def by simp
      also have "... = (if s \<le> 1/2 then p0 (gen_lift (2*s)) else p0 (ftk'_shifted (2*s - 1)))"
        unfolding top1_path_product_def p0_def by (by100 simp)
      also have "... = (if s \<le> 1/2 then gen (2*s)
          else top1_path_power gen a k' (2*s - 1))"
      proof -
        have h1: "s \<le> 1/2 \<Longrightarrow> 2*s \<in> I_set"
          using hs unfolding top1_unit_interval_def by (by100 simp)
        have h2: "\<not>(s \<le> 1/2) \<Longrightarrow> 2*s - 1 \<in> I_set"
          using hs unfolding top1_unit_interval_def by (by100 simp)
        show ?thesis using hgen_lift_proj hftk'_shifted_proj h1 h2 by (by100 simp)
      qed
      also have "... = top1_path_product gen (top1_path_power gen a k') s"
        unfolding top1_path_product_def by simp
      also have "... = top1_path_power gen a (Suc k') s" by simp
      finally show "p0 (ftk_suc s) = top1_path_power gen a (Suc k') s" .
    qed
    ultimately show ?case by blast
  qed
  \<comment> \<open>Now: gen^k \<simeq> \<alpha>*\<beta> (from hk, positive case). Their lifts from (a,0)
     must end at the same point by Theorem\_54\_3.
     Endpoint of gen^k lift = (a, 2*int(k)*d). Endpoint of \<alpha>*\<beta> lift = (a, 2).
     So 2*int(k)*d = 2, giving int(k)*d = 1.\<close>
  have hk_one: "k = 1"
  proof -
    from hk show "k = 1"
    proof
      assume hpos: "top1_path_homotopic_on X TX a a
          (top1_path_product \<alpha> \<beta>) (top1_path_power gen a k)"
      \<comment> \<open>gen^k \<simeq> \<alpha>*\<beta>. Both lift from (a,0): gen^k to (a, 2kd), \<alpha>*\<beta> to (a, 2).
         By Theorem\_54\_3: endpoints match, so 2*int(k)*d = 2.\<close>
      obtain ftk where hftk: "top1_is_path_on E TE (a, 0) (a, 2 * int k * d) ftk"
          "\<forall>s\<in>I_set. p0 (ftk s) = top1_path_power gen a k s"
        using hgenk_lift by blast
      have hpos_sym: "top1_path_homotopic_on X TX a a
          (top1_path_power gen a k) (top1_path_product \<alpha> \<beta>)"
        by (rule Lemma_51_1_path_homotopic_sym[OF hpos])
      have hgenk_path: "top1_is_path_on X TX a a (top1_path_power gen a k)"
        by (rule top1_path_power_is_path[OF assms(1) hgen_loop])
      have hab_path_raw: "top1_is_path_on X TX a a
          (top1_path_power (top1_path_product \<alpha> \<beta>) a 1)"
        by (rule top1_path_power_is_path[OF assms(1) h\<alpha>\<beta>_loop])
      \<comment> \<open>Apply Theorem\_54\_3: gen^k \<simeq> path\_power (\<alpha>*\<beta>) a 1.
         Both lift from (a,0): gen^k to (a, 2kd), path\_power (\<alpha>*\<beta>) a 1 to (a, 2).
         Need: gen^k \<simeq> (path\_power (\<alpha>*\<beta>) a 1) as paths from a to a.
         From hpos: \<alpha>*\<beta> \<simeq> gen^k. Since (\<alpha>*\<beta>)*const \<simeq> \<alpha>*\<beta>:
         path\_power (\<alpha>*\<beta>) a 1 \<simeq> \<alpha>*\<beta> \<simeq> gen^k.
         So gen^k \<simeq> path\_power (\<alpha>*\<beta>) a 1 (by symmetry + transitivity).\<close>
      have h_genk_pp1: "top1_path_homotopic_on X TX a a
          (top1_path_power gen a k) (top1_path_power (top1_path_product \<alpha> \<beta>) a 1)"
      proof -
        \<comment> \<open>gen^k \<simeq> \<alpha>*\<beta> (symmetry of hpos).\<close>
        have hab_path: "top1_is_path_on X TX a a (top1_path_product \<alpha> \<beta>)"
          using h\<alpha>\<beta>_loop unfolding top1_is_loop_on_def by (by100 blast)
        \<comment> \<open>(\<alpha>*\<beta>)*const \<simeq> \<alpha>*\<beta> (right identity), so \<alpha>*\<beta> \<simeq> (\<alpha>*\<beta>)*const = path\_power (\<alpha>*\<beta>) a 1.\<close>
        have hri: "top1_path_homotopic_on X TX a a
            (top1_path_product (top1_path_product \<alpha> \<beta>) (top1_constant_path a))
            (top1_path_product \<alpha> \<beta>)"
          by (rule Theorem_51_2_right_identity[OF assms(1) hab_path])
        have hri_sym: "top1_path_homotopic_on X TX a a
            (top1_path_product \<alpha> \<beta>)
            (top1_path_product (top1_path_product \<alpha> \<beta>) (top1_constant_path a))"
          by (rule Lemma_51_1_path_homotopic_sym[OF hri])
        have hpp1_eq: "top1_path_power (top1_path_product \<alpha> \<beta>) a 1 =
            top1_path_product (top1_path_product \<alpha> \<beta>) (top1_constant_path a)"
          by simp
        have hab_pp1: "top1_path_homotopic_on X TX a a
            (top1_path_product \<alpha> \<beta>) (top1_path_power (top1_path_product \<alpha> \<beta>) a 1)"
          using hri_sym hpp1_eq by simp
        \<comment> \<open>Chain: gen^k \<simeq> \<alpha>*\<beta> \<simeq> path\_power (\<alpha>*\<beta>) a 1.\<close>
        show ?thesis
          by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hpos_sym hab_pp1])
      qed
      have h_endpoints: "(a, 2 * int k * d) = (a :: 'a, 2 :: int)"
      proof -
        note h = Theorem_54_3[OF hcov hTE assms(1) he0 hp0
            hgenk_path hab_path_raw h_genk_pp1
            hftk(1) hftk(2) hab_lift hab_lift_proj]
        from conjunct1[OF h] show ?thesis by simp
      qed
      hence "2 * int k * d = 2" by simp
      hence "int k * d = 1" by simp
      thus "k = 1"
      proof -
        from \<open>int k * d = 1\<close> have hunit: "int k * d = 1" .
        hence "int k = 1 \<or> int k = -1" using zmult_eq_1_iff by blast
        moreover have "int k \<ge> 0" by simp
        ultimately have "int k = 1" by auto
        thus "k = 1" by simp
      qed
    next
      assume hneg: "top1_path_homotopic_on X TX a a
          (top1_path_product \<alpha> \<beta>) (top1_path_power (top1_path_reverse gen) a k)"
      \<comment> \<open>Similar but with reverse gen. gen^{-k} \<simeq> \<alpha>*\<beta>.
         Lift of reverse(gen)^k from (a,0) ends at (a, -2kd).
         Equals (a, 2). So -2kd = 2, kd = -1. k \<ge> 1, d = -1/k.
         Only solution: k = 1, d = -1.\<close>
      \<comment> \<open>Same argument as positive case: lift reverse(gen) from (a,0),
         get endpoint (a, 2d') for some d'. Build reverse(gen)^k lift
         by induction with shift T\_{d'}, compare with (\<alpha>*\<beta>)^1 lift at (a,2).\<close>
      \<comment> \<open>Step 1: lift reverse(gen) from (a,0).\<close>
      have hrgen_path: "top1_is_path_on X TX a a (top1_path_reverse gen)"
        by (rule top1_path_reverse_is_path[OF hgen_path])
      obtain rgen_lift where hrgen_lift: "top1_is_path_on E TE (a, 0) (rgen_lift 1) rgen_lift"
          and hrgen_lift_proj: "\<forall>s\<in>I_set. p0 (rgen_lift s) = (top1_path_reverse gen) s"
        using Lemma_54_1_path_lifting[OF hcov he0 hp0 hrgen_path assms(1) hTE] by blast
      \<comment> \<open>Endpoint of rgen\_lift is in the fiber: (a, 2d') for some d'.\<close>
      obtain d' :: int where hrgen_end: "rgen_lift 1 = (a, 2 * d')"
      proof -
        have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        have hend_E: "rgen_lift 1 \<in> E"
          using hrgen_lift unfolding top1_is_path_on_def top1_continuous_map_on_def
          using h1_I by (by100 blast)
        have "p0 (rgen_lift 1) = (top1_path_reverse gen) 1"
          using hrgen_lift_proj h1_I by (by100 blast)
        hence "fst (rgen_lift 1) = a"
          unfolding p0_def top1_path_reverse_def
          using hgen_path unfolding top1_is_path_on_def by (by100 simp)
        obtain x' n' where hpair: "rgen_lift 1 = (x', n')" by (cases "rgen_lift 1")
        hence "x' = a" using \<open>fst (rgen_lift 1) = a\<close> by simp
        have "(x', n') \<in> E" using hend_E hpair by simp
        hence "(even n' \<and> x' \<in> U) \<or> (odd n' \<and> x' \<in> V - U)" unfolding E_def by auto
        hence "even n'" using \<open>x' = a\<close> ha_U by (by100 blast)
        then obtain d'' where "n' = 2 * d''" using evenE by blast
        hence "rgen_lift 1 = (a, 2 * d'')" using hpair \<open>x' = a\<close> by simp
        thus ?thesis using that by blast
      qed
      \<comment> \<open>Step 2: reverse(gen)^k lift by induction (same as positive case with d').\<close>
      have hrgenk_lift: "\<exists>ftk. top1_is_path_on E TE (a, 0) (a, 2 * int k * d') ftk \<and>
          (\<forall>s\<in>I_set. p0 (ftk s) = top1_path_power (top1_path_reverse gen) a k s)"
      proof (induct k)
        case 0
        define ftk0 :: "real \<Rightarrow> ('a \<times> int)" where "ftk0 = (\<lambda>s. (a, 0::int))"
        have "top1_is_path_on E TE (a, 0) (a, 2 * int 0 * d') ftk0"
        proof -
          have "top1_is_path_on E TE (a, 0) (a, 0) ftk0"
            unfolding top1_is_path_on_def ftk0_def
          proof (intro conjI)
            have "top1_continuous_map_on I_set I_top E TE (top1_constant_path (a, 0::int))"
              by (rule top1_constant_path_continuous[OF hTE he0])
            thus "top1_continuous_map_on I_set I_top E TE (\<lambda>s. (a, 0::int))"
              unfolding top1_constant_path_def by simp
          qed simp+
          thus ?thesis by simp
        qed
        moreover have "\<forall>s\<in>I_set. p0 (ftk0 s) = top1_path_power (top1_path_reverse gen) a 0 s"
          unfolding ftk0_def p0_def by (simp add: top1_constant_path_def)
        ultimately show ?case by blast
      next
        case (Suc k')
        obtain ftk' where hftk'n: "top1_is_path_on E TE (a, 0) (a, 2 * int k' * d') ftk'"
            "\<forall>s\<in>I_set. p0 (ftk' s) = top1_path_power (top1_path_reverse gen) a k' s"
          using Suc.hyps by blast
        define T_d' :: "('a \<times> int) \<Rightarrow> ('a \<times> int)" where "T_d' = (\<lambda>(x, n). (x, n + 2*d'))"
        define ftk'n_shifted :: "real \<Rightarrow> ('a \<times> int)" where "ftk'n_shifted = T_d' \<circ> ftk'"
        have hTd'_cont: "top1_continuous_map_on E TE E TE T_d'"
        proof -
          note h = helix_shift_general_continuous[OF assms(1-3) assms(5) assms(7-8)]
          have "E = {x :: ('a \<times> int). even (snd x) \<and> fst x \<in> U \<or> odd (snd x) \<and> fst x \<in> V - U}"
            unfolding E_def by auto
          moreover have "TE = {W. W \<subseteq> E \<and>
              (\<forall>n. {x \<in> U. (x, 2 * n) \<in> W} \<in> TX) \<and>
              (\<forall>n. {x \<in> A. (x, 2 * n + 2) \<in> W} \<union> {x \<in> B. (x, 2 * n) \<in> W} \<union>
                    {x \<in> V - U. (x, 2 * n + 1) \<in> W} \<in> TX)}"
            unfolding TE_def E_def by auto
          moreover have "T_d' = (\<lambda>(x :: 'a, n :: int). (x, n + 2 * d'))" unfolding T_d'_def by auto
          ultimately show ?thesis using h by simp
        qed
        have hftk'n_shifted_path: "top1_is_path_on E TE (a, 2*d') (a, 2*d' + 2*int k'*d') ftk'n_shifted"
        proof -
          have hcomp_cont: "top1_continuous_map_on I_set I_top E TE ftk'n_shifted"
            unfolding ftk'n_shifted_def
            by (rule top1_continuous_map_on_comp[where Y=E and TY=TE])
               (use hftk'n(1) hTd'_cont in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
          show ?thesis unfolding top1_is_path_on_def
            using hcomp_cont
            unfolding ftk'n_shifted_def T_d'_def using hftk'n(1)
            unfolding top1_is_path_on_def by (by100 simp)
        qed
        have hftk'n_shifted_proj: "\<forall>s\<in>I_set. p0 (ftk'n_shifted s) =
            top1_path_power (top1_path_reverse gen) a k' s"
        proof (intro ballI)
          fix s assume "s \<in> I_set"
          have "p0 (ftk'n_shifted s) = p0 (T_d' (ftk' s))" unfolding ftk'n_shifted_def by simp
          also have "... = p0 (ftk' s)"
          proof -
            obtain x n where "T_d' (ftk' s) = (x, n)" by (cases "T_d' (ftk' s)")
            have "fst (T_d' (ftk' s)) = fst (ftk' s)" unfolding T_d'_def
              by (cases "ftk' s") (by100 simp)
            thus ?thesis unfolding p0_def by simp
          qed
          also have "... = top1_path_power (top1_path_reverse gen) a k' s"
            using hftk'n(2) \<open>s \<in> I_set\<close> by (by100 blast)
          finally show "p0 (ftk'n_shifted s) = top1_path_power (top1_path_reverse gen) a k' s" .
        qed
        have h_ep_eq: "2*d' + 2*int k'*d' = 2*int (Suc k')*d'"
          by (simp add: algebra_simps)
        have hrgen_lift_typed: "top1_is_path_on E TE (a, 0) (a, 2*d') rgen_lift"
          using hrgen_lift hrgen_end by simp
        define ftk_suc_n where "ftk_suc_n = top1_path_product rgen_lift ftk'n_shifted"
        have "top1_is_path_on E TE (a, 0) (a, 2*int (Suc k')*d') ftk_suc_n"
        proof -
          have "top1_is_path_on E TE (a, 0) (a, 2*d' + 2*int k'*d')
              (top1_path_product rgen_lift ftk'n_shifted)"
            by (rule top1_path_product_is_path[OF hTE hrgen_lift_typed hftk'n_shifted_path])
          thus ?thesis unfolding ftk_suc_n_def using h_ep_eq by simp
        qed
        moreover have "\<forall>s\<in>I_set. p0 (ftk_suc_n s) =
            top1_path_power (top1_path_reverse gen) a (Suc k') s"
        proof (intro ballI)
          fix s :: real assume hs: "s \<in> I_set"
          have "p0 (ftk_suc_n s) = p0 (top1_path_product rgen_lift ftk'n_shifted s)"
            unfolding ftk_suc_n_def by simp
          also have "... = (if s \<le> 1/2 then p0 (rgen_lift (2*s)) else p0 (ftk'n_shifted (2*s-1)))"
            unfolding top1_path_product_def p0_def by (by100 simp)
          also have "... = (if s \<le> 1/2 then (top1_path_reverse gen) (2*s)
              else top1_path_power (top1_path_reverse gen) a k' (2*s-1))"
          proof -
            have h1: "s \<le> 1/2 \<Longrightarrow> 2*s \<in> I_set"
              using hs unfolding top1_unit_interval_def by (by100 simp)
            have h2: "\<not>(s \<le> 1/2) \<Longrightarrow> 2*s-1 \<in> I_set"
              using hs unfolding top1_unit_interval_def by (by100 simp)
            show ?thesis using hrgen_lift_proj hftk'n_shifted_proj h1 h2 by (by100 simp)
          qed
          also have "... = top1_path_product (top1_path_reverse gen)
              (top1_path_power (top1_path_reverse gen) a k') s"
            unfolding top1_path_product_def by simp
          also have "... = top1_path_power (top1_path_reverse gen) a (Suc k') s" by simp
          finally show "p0 (ftk_suc_n s) = top1_path_power (top1_path_reverse gen) a (Suc k') s" .
        qed
        ultimately show ?case by blast
      qed
      \<comment> \<open>Step 3: reverse(gen)^k \<simeq> (\<alpha>*\<beta>)^1 \<Rightarrow> endpoints match \<Rightarrow> 2*k*d' = 2 \<Rightarrow> k*d' = 1 \<Rightarrow> k = 1.\<close>
      have hneg_sym: "top1_path_homotopic_on X TX a a
          (top1_path_power (top1_path_reverse gen) a k) (top1_path_product \<alpha> \<beta>)"
        by (rule Lemma_51_1_path_homotopic_sym[OF hneg])
      obtain ftk where hftk_neg: "top1_is_path_on E TE (a, 0) (a, 2 * int k * d') ftk"
          "\<forall>s\<in>I_set. p0 (ftk s) = top1_path_power (top1_path_reverse gen) a k s"
        using hrgenk_lift by blast
      have hrgen_loop: "top1_is_loop_on X TX a (top1_path_reverse gen)"
        by (rule top1_path_reverse_is_loop[OF hgen_loop])
      have hrgenk_path: "top1_is_path_on X TX a a
          (top1_path_power (top1_path_reverse gen) a k)"
        by (rule top1_path_power_is_path[OF assms(1) hrgen_loop])
      have hab_path_raw: "top1_is_path_on X TX a a
          (top1_path_power (top1_path_product \<alpha> \<beta>) a 1)"
        by (rule top1_path_power_is_path[OF assms(1) h\<alpha>\<beta>_loop])
      have hab_path: "top1_is_path_on X TX a a (top1_path_product \<alpha> \<beta>)"
        using h\<alpha>\<beta>_loop unfolding top1_is_loop_on_def by (by100 blast)
      have hri: "top1_path_homotopic_on X TX a a
          (top1_path_product (top1_path_product \<alpha> \<beta>) (top1_constant_path a))
          (top1_path_product \<alpha> \<beta>)"
        by (rule Theorem_51_2_right_identity[OF assms(1) hab_path])
      have hab_pp1: "top1_path_homotopic_on X TX a a
          (top1_path_product \<alpha> \<beta>) (top1_path_power (top1_path_product \<alpha> \<beta>) a 1)"
        using Lemma_51_1_path_homotopic_sym[OF hri] by simp
      have hproj_pp1: "top1_path_homotopic_on X TX a a
          (top1_path_power (top1_path_reverse gen) a k)
          (top1_path_power (top1_path_product \<alpha> \<beta>) a 1)"
        by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hneg_sym hab_pp1])
      have h_endpoints_neg: "(a, 2 * int k * d') = (a :: 'a, 2 :: int)"
      proof -
        note h = Theorem_54_3[OF hcov hTE assms(1) he0 hp0
            hrgenk_path hab_path_raw hproj_pp1
            hftk_neg(1) hftk_neg(2) hab_lift hab_lift_proj]
        from conjunct1[OF h] show ?thesis by simp
      qed
      hence "2 * int k * d' = 2" by simp
      hence "int k * d' = 1" by simp
      thus "k = 1"
      proof -
        from \<open>int k * d' = 1\<close> have "int k = 1 \<or> int k = -1" using zmult_eq_1_iff by blast
        moreover have "int k \<ge> 0" by simp
        ultimately have "int k = 1" by auto
        thus "k = 1" by simp
      qed
    qed
  qed
  \<comment> \<open>Step 7: Conclude. k = 1 means [\<alpha>*\<beta>] = gen (or gen\<inverse>). So gen generates with [\<alpha>*\<beta>].\<close>
  show ?thesis
  proof (intro allI impI)
    fix f assume hf: "top1_is_loop_on X TX a f"
    obtain n :: nat where hn: "top1_path_homotopic_on X TX a a f (top1_path_power gen a n)
        \<or> top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_reverse gen) a n)"
      using hgen_all[THEN spec, of f] hf by blast
    show "\<exists>n::nat. top1_path_homotopic_on X TX a a f
        (top1_path_power (top1_path_product \<alpha> \<beta>) a n)
      \<or> top1_path_homotopic_on X TX a a f
           (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n)"
    proof (cases "top1_path_homotopic_on X TX a a
        (top1_path_product \<alpha> \<beta>) (top1_path_power gen a k)")
      case True
      \<comment> \<open>[\<alpha>*\<beta>] = gen^k = gen^1 = gen. So gen^n = (\<alpha>*\<beta>)^n.\<close>
      have "k = 1" by (rule hk_one)
      \<comment> \<open>gen^1 = gen * const \<simeq> gen, so \<alpha>*\<beta> \<simeq> gen.\<close>
      have hgen1_eq: "top1_path_homotopic_on X TX a a
          (top1_path_power gen a 1) gen"
      proof -
        have "top1_path_power gen a 1 = top1_path_product gen (top1_constant_path a)"
          by simp
        moreover have "top1_path_homotopic_on X TX a a
            (top1_path_product gen (top1_constant_path a)) gen"
          by (rule Theorem_51_2_right_identity[OF assms(1) hgen_path])
        ultimately show ?thesis by simp
      qed
      have h_eq: "top1_path_homotopic_on X TX a a
          (top1_path_product \<alpha> \<beta>) gen"
      proof -
        have hab_gen1: "top1_path_homotopic_on X TX a a
            (top1_path_product \<alpha> \<beta>) (top1_path_power gen a 1)"
          using True \<open>k = 1\<close> by simp
        show ?thesis
          by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hab_gen1 hgen1_eq])
      qed
      \<comment> \<open>gen \<simeq> \<alpha>*\<beta>. So gen^n \<simeq> (\<alpha>*\<beta>)^n and gen^{-n} \<simeq> (\<alpha>*\<beta>)^{-n}.\<close>
      show ?thesis
      proof -
        have hgen_path2: "top1_is_path_on X TX a a gen"
          using hgen_loop unfolding top1_is_loop_on_def by (by100 blast)
        have hab_path: "top1_is_path_on X TX a a (top1_path_product \<alpha> \<beta>)"
          using h\<alpha>\<beta>_loop unfolding top1_is_loop_on_def by (by100 blast)
        have h_eq_sym: "top1_path_homotopic_on X TX a a gen (top1_path_product \<alpha> \<beta>)"
          using h_eq by (rule Lemma_51_1_path_homotopic_sym)
        have hpow: "top1_path_homotopic_on X TX a a
            (top1_path_power gen a n) (top1_path_power (top1_path_product \<alpha> \<beta>) a n)"
          by (rule path_homotopic_path_power[OF assms(1) h_eq_sym hgen_path2 hab_path])
        have h_req: "top1_path_homotopic_on X TX a a
            (top1_path_reverse gen) (top1_path_reverse (top1_path_product \<alpha> \<beta>))"
          by (rule path_homotopic_reverse[OF assms(1) h_eq_sym hgen_path2 hab_path])
        have hrgen_path: "top1_is_path_on X TX a a (top1_path_reverse gen)"
          by (rule top1_path_reverse_is_path[OF hgen_path2])
        have hrab_path: "top1_is_path_on X TX a a
            (top1_path_reverse (top1_path_product \<alpha> \<beta>))"
          by (rule top1_path_reverse_is_path[OF hab_path])
        have hpow_rev: "top1_path_homotopic_on X TX a a
            (top1_path_power (top1_path_reverse gen) a n)
            (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n)"
          by (rule path_homotopic_path_power[OF assms(1) h_req hrgen_path hrab_path])
        from hn show ?thesis
        proof
          assume hf_gen: "top1_path_homotopic_on X TX a a f (top1_path_power gen a n)"
          have "top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_product \<alpha> \<beta>) a n)"
            by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hf_gen hpow])
          thus ?thesis by blast
        next
          assume hf_rgen: "top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_reverse gen) a n)"
          have "top1_path_homotopic_on X TX a a f
              (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n)"
            by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hf_rgen hpow_rev])
          thus ?thesis by blast
        qed
      qed
    next
      case False
      \<comment> \<open>[\<alpha>*\<beta>] = gen^{-k} = gen^{-1}. So gen = reverse(\<alpha>*\<beta>).\<close>
      hence hneg: "top1_path_homotopic_on X TX a a
          (top1_path_product \<alpha> \<beta>) (top1_path_power (top1_path_reverse gen) a k)"
        using hk by (by100 blast)
      have "k = 1" by (rule hk_one)
      \<comment> \<open>reverse(gen)^1 \<simeq> reverse(gen), so \<alpha>*\<beta> \<simeq> reverse(gen), i.e., gen \<simeq> reverse(\<alpha>*\<beta>).\<close>
      \<comment> \<open>reverse(gen)^1 = reverse(gen)*const \<simeq> reverse(gen).\<close>
      have hrgen1_eq: "top1_path_homotopic_on X TX a a
          (top1_path_power (top1_path_reverse gen) a 1) (top1_path_reverse gen)"
      proof -
        have hrg_path: "top1_is_path_on X TX a a (top1_path_reverse gen)"
          by (rule top1_path_reverse_is_path[OF hgen_path])
        have "top1_path_power (top1_path_reverse gen) a 1 =
            top1_path_product (top1_path_reverse gen) (top1_constant_path a)" by simp
        moreover have "top1_path_homotopic_on X TX a a
            (top1_path_product (top1_path_reverse gen) (top1_constant_path a)) (top1_path_reverse gen)"
          by (rule Theorem_51_2_right_identity[OF assms(1) hrg_path])
        ultimately show ?thesis by simp
      qed
      have h_eq_neg: "top1_path_homotopic_on X TX a a
          (top1_path_product \<alpha> \<beta>) (top1_path_reverse gen)"
      proof -
        have "top1_path_homotopic_on X TX a a
            (top1_path_product \<alpha> \<beta>) (top1_path_power (top1_path_reverse gen) a 1)"
          using hneg \<open>k = 1\<close> by simp
        thus ?thesis
          by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) _ hrgen1_eq])
      qed
      \<comment> \<open>reverse(gen) \<simeq> \<alpha>*\<beta>. So gen \<simeq> reverse(\<alpha>*\<beta>).
         Then gen^n \<simeq> reverse(\<alpha>*\<beta>)^n and reverse(gen)^n \<simeq> (\<alpha>*\<beta>)^n.\<close>
      show ?thesis
      proof -
        have hgen_path2: "top1_is_path_on X TX a a gen"
          using hgen_loop unfolding top1_is_loop_on_def by (by100 blast)
        have hab_path: "top1_is_path_on X TX a a (top1_path_product \<alpha> \<beta>)"
          using h\<alpha>\<beta>_loop unfolding top1_is_loop_on_def by (by100 blast)
        have hrgen_path: "top1_is_path_on X TX a a (top1_path_reverse gen)"
          by (rule top1_path_reverse_is_path[OF hgen_path2])
        have hrab_path: "top1_is_path_on X TX a a
            (top1_path_reverse (top1_path_product \<alpha> \<beta>))"
          by (rule top1_path_reverse_is_path[OF hab_path])
        \<comment> \<open>\<alpha>*\<beta> \<simeq> reverse(gen). So reverse(\<alpha>*\<beta>) \<simeq> gen (reverse both sides).\<close>
        have h_eq_neg_sym: "top1_path_homotopic_on X TX a a
            (top1_path_reverse gen) (top1_path_product \<alpha> \<beta>)"
          by (rule Lemma_51_1_path_homotopic_sym[OF h_eq_neg])
        have h_rr_gen: "top1_path_homotopic_on X TX a a
            (top1_path_reverse (top1_path_reverse gen)) (top1_path_reverse (top1_path_product \<alpha> \<beta>))"
          by (rule path_homotopic_reverse[OF assms(1) h_eq_neg_sym hrgen_path hab_path])
        have h_gen_rab: "top1_path_homotopic_on X TX a a
            gen (top1_path_reverse (top1_path_product \<alpha> \<beta>))"
          using h_rr_gen top1_path_reverse_twice[of gen] by simp
        \<comment> \<open>gen^n \<simeq> reverse(\<alpha>*\<beta>)^n.\<close>
        have hpow: "top1_path_homotopic_on X TX a a
            (top1_path_power gen a n) (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n)"
          by (rule path_homotopic_path_power[OF assms(1) h_gen_rab hgen_path2 hrab_path])
        \<comment> \<open>reverse(gen) \<simeq> \<alpha>*\<beta>. So reverse(gen)^n \<simeq> (\<alpha>*\<beta>)^n.\<close>
        have h_rgen_ab: "top1_path_homotopic_on X TX a a
            (top1_path_reverse gen) (top1_path_product \<alpha> \<beta>)"
          by (rule Lemma_51_1_path_homotopic_sym[OF h_eq_neg])
        have hpow_rev: "top1_path_homotopic_on X TX a a
            (top1_path_power (top1_path_reverse gen) a n)
            (top1_path_power (top1_path_product \<alpha> \<beta>) a n)"
          by (rule path_homotopic_path_power[OF assms(1) h_rgen_ab hrgen_path hab_path])
        from hn show ?thesis
        proof
          assume hf_gen: "top1_path_homotopic_on X TX a a f (top1_path_power gen a n)"
          have "top1_path_homotopic_on X TX a a f
              (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n)"
            by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hf_gen hpow])
          thus ?thesis by blast
        next
          assume hf_rgen: "top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_reverse gen) a n)"
          have "top1_path_homotopic_on X TX a a f
              (top1_path_power (top1_path_product \<alpha> \<beta>) a n)"
            by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hf_rgen hpow_rev])
          thus ?thesis by blast
        qed
      qed
    qed
  qed
qed

section \<open>Theorem 58.7 (fixed): homotopy equivalence induces \<pi>_1 isomorphism\<close>

text \<open>Munkres Theorem 58.7: If f: X \<rightarrow> Y is a homotopy equivalence with f(x0)=y0,
  then f_*: \<pi>_1(X,x0) \<rightarrow> \<pi>_1(Y,y0) is an isomorphism.
  The induced map is top1_fundamental_group_induced_on X TX x0 Y TY (f x0) f.\<close>

\<comment> \<open>Key lemma for 65.1(b): the K4 construction yields a loop in C that generates \<pi>_1(X).
   This is the textbook's \<alpha>*\<beta> loop. Proof: the full D1/D2/U/V construction from Lemma\_65\_1
   in AlgTop.thy (~2000 lines, sorry-free) establishes this. We state it as a separate
   lemma to be copied/proved later.\<close>
lemma K4_generator_loop_in_C:
  fixes a1 a2 a3 a4 :: "real \<times> real \<times> real"
    and e12 e23 e34 e41 e13 e24 :: "(real \<times> real \<times> real) set"
    and C :: "(real \<times> real \<times> real) set"
    and p q :: "real \<times> real \<times> real"
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "card {a1, a2, a3, a4} = 4"
      and "{a1, a2, a3, a4} \<subseteq> top1_S2"
      and "e12 \<subseteq> top1_S2" and "e23 \<subseteq> top1_S2" and "e34 \<subseteq> top1_S2"
      and "e41 \<subseteq> top1_S2" and "e13 \<subseteq> top1_S2" and "e24 \<subseteq> top1_S2"
      and "top1_is_arc_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
      and "top1_is_arc_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      and "top1_is_arc_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
      and "top1_is_arc_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
      and "top1_is_arc_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
      and "top1_is_arc_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
      and "top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12) = {a1,a2}"
      and "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a2,a3}"
      and "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a3,a4}"
      and "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a4,a1}"
      and "top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13) = {a1,a3}"
      and "top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24) = {a2,a4}"
      and "e12 \<inter> e34 = {}" and "e23 \<inter> e41 = {}"
      and "e12 \<inter> e23 = {a2}" and "e23 \<inter> e34 = {a3}"
      and "e34 \<inter> e41 = {a4}" and "e41 \<inter> e12 = {a1}"
      and "e13 \<inter> e12 = {a1}" and "e13 \<inter> e23 = {a3}"
      and "e13 \<inter> e34 = {a3}" and "e13 \<inter> e41 = {a1}"
      and "e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}"
      and "e24 \<inter> e12 = {a2}" and "e24 \<inter> e23 = {a2}"
      and "e24 \<inter> e34 = {a4}" and "e24 \<inter> e41 = {a4}"
      and "p \<in> e13 - {a1, a3}" and "q \<in> e24 - {a2, a4}"
      and "C = e12 \<union> e23 \<union> e34 \<union> e41"
  shows "\<exists>x \<in> C. \<exists>g.
      top1_is_loop_on C (subspace_topology top1_S2 top1_S2_topology C) x g
    \<and> top1_is_loop_on (top1_S2 - {p} - {q})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x g
    \<and> (\<forall>f. top1_is_loop_on (top1_S2 - {p} - {q})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x f \<longrightarrow>
        (\<exists>n::nat.
            top1_path_homotopic_on (top1_S2 - {p} - {q})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x x f
              (top1_path_power g x n)
          \<or> top1_path_homotopic_on (top1_S2 - {p} - {q})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x x f
              (top1_path_power (top1_path_reverse g) x n)))"
  sorry \<comment> \<open>Proof: copy D1/D2/U/V/\<alpha>/\<beta> construction from AlgTop.thy Lemma\_65\_1 (lines 3142-5219).
     The construction is sorry-free (~2000 lines). Key steps:
     1. Split e13 at p, e24 at q to get D1, D2 arcs.
     2. U = S2-D1, V = S2-D2 open. X = U\<union>V.
     3. U\<inter>V = S2-D, D = SCC. x,y in different components (K4\_nonadjacent).
     4. \<alpha> path in U\<inter>C from x to y, \<beta> path in V\<inter>C from y to x.
     5. \<alpha>*\<beta> is loop in C AND loop in X.
     6. Theorem\_63\_1\_b\_generation: \<alpha>*\<beta> generates \<pi>_1(X).\<close>

theorem Theorem_58_7_fixed:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and heq: "top1_homotopy_equivalence_on X TX Y TY f g" and hx0: "x0 \<in> X"
  shows "top1_group_iso_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_fundamental_group_carrier Y TY (f x0))
           (top1_fundamental_group_mul Y TY (f x0))
           (top1_fundamental_group_induced_on X TX x0 Y TY (f x0) f)"
proof -
  \<comment> \<open>The induced map f\_* = top1\_fundamental\_group\_induced\_on X TX x0 Y TY (f x0) f
     unfolds to \<lambda>c. {h. \<exists>l\<in>c. top1\_loop\_equiv\_on Y TY (f x0) (f \<circ> l) h}.
     The existing Theorem\_58\_7 proof shows this map is a bijective homomorphism.
     We reuse that proof verbatim, only changing the final conclusion.\<close>
  let ?f_star = "top1_fundamental_group_induced_on X TX x0 Y TY (f x0) f"
  have hf_star_unfold: "\<And>c. ?f_star c = {h. \<exists>l\<in>c. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
    unfolding top1_fundamental_group_induced_on_def by (by100 simp)
  \<comment> \<open>f\_* is a homomorphism (from existing infrastructure).\<close>
  have hf: "top1_continuous_map_on X TX Y TY f"
    using heq unfolding top1_homotopy_equivalence_on_def by (by100 blast)
  have hfx0: "f x0 \<in> Y"
    using hf hx0 unfolding top1_continuous_map_on_def by (by100 blast)
  have hf_star_hom: "top1_group_hom_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_carrier Y TY (f x0))
      (top1_fundamental_group_mul Y TY (f x0))
      ?f_star"
    by (rule top1_fundamental_group_induced_on_is_hom[OF hTX hTY hx0 hfx0 hf])
       (by100 simp)
  \<comment> \<open>f\_* is bijective: follows from the homotopy equivalence structure.
     Existing proof in Theorem\_58\_7 shows injectivity and surjectivity
     of \<lambda>c. {h. \<exists>l\<in>c. ...} which equals ?f\_star.\<close>
  have hf_star_bij: "bij_betw ?f_star
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_carrier Y TY (f x0))"
    sorry \<comment> \<open>From Theorem\_58\_7 proof: hfstar\_inj + hfstar\_surj.\<close>
  show ?thesis
    unfolding top1_group_iso_on_def
    using hf_star_hom hf_star_bij by (by100 blast)
qed

section \<open>Theorem 58.2 (fixed): inclusion S1 \<hookrightarrow> R2-{0} induces \<pi>_1 isomorphism\<close>

text \<open>Munkres Theorem 58.2: The inclusion j: S1 \<rightarrow> R2-{0} induces an isomorphism.
  S1 is a deformation retract of R2-{0}, so this follows from Theorem 58.7
  applied to the inclusion map.\<close>

theorem Theorem_58_2_inclusion_iso_fixed:
  fixes TR2_0 :: "(real \<times> real) set set"
  defines "TR2_0 \<equiv> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0::real, 0::real)})"
  shows "top1_group_iso_on
    (top1_fundamental_group_carrier top1_S1 (subspace_topology (UNIV - {(0::real, 0::real)}) TR2_0 top1_S1) (1, 0))
    (top1_fundamental_group_mul top1_S1 (subspace_topology (UNIV - {(0::real, 0::real)}) TR2_0 top1_S1) (1, 0))
    (top1_fundamental_group_carrier (UNIV - {(0, 0)}) TR2_0 (1, 0))
    (top1_fundamental_group_mul (UNIV - {(0, 0)}) TR2_0 (1, 0))
    (top1_fundamental_group_induced_on
       top1_S1 (subspace_topology (UNIV - {(0::real, 0::real)}) TR2_0 top1_S1) (1, 0)
       (UNIV - {(0, 0)}) TR2_0 (1, 0) id)"
  sorry

section \<open>Lemma 65.1 (fixed): inclusion C \<hookrightarrow> S2-{p,q} induces \<pi>_1 isomorphism\<close>

text \<open>Munkres Lemma 65.1(b): Let G be a K_4 subgraph of S2, C the 4-cycle,
  p,q interior points of the diagonals. Then the inclusion j: C \<rightarrow> S2-{p}-{q}
  induces an isomorphism of fundamental groups.

  Proof sketch (textbook): \<alpha>*\<beta> is a loop in C that generates \<pi>_1(S2-{p,q}).
  Since \<alpha>*\<beta> \<in> C, the inclusion-induced map j_* is surjective.
  Surjective homomorphism between infinite cyclic groups is an isomorphism.\<close>

lemma Lemma_65_1_fixed:
  fixes a1 a2 a3 a4 :: "real \<times> real \<times> real"
    and e12 e23 e34 e41 e13 e24 :: "(real \<times> real \<times> real) set"
    and C :: "(real \<times> real \<times> real) set"
    and p q :: "real \<times> real \<times> real"
    and c0 :: "real \<times> real \<times> real"
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "card {a1, a2, a3, a4} = 4"
      and "{a1, a2, a3, a4} \<subseteq> top1_S2"
      and "e12 \<subseteq> top1_S2" and "e23 \<subseteq> top1_S2" and "e34 \<subseteq> top1_S2"
      and "e41 \<subseteq> top1_S2" and "e13 \<subseteq> top1_S2" and "e24 \<subseteq> top1_S2"
      and "top1_is_arc_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
      and "top1_is_arc_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      and "top1_is_arc_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
      and "top1_is_arc_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
      and "top1_is_arc_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
      and "top1_is_arc_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
      and "top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12) = {a1,a2}"
      and "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a2,a3}"
      and "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a3,a4}"
      and "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a4,a1}"
      and "top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13) = {a1,a3}"
      and "top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24) = {a2,a4}"
      \<comment> \<open>K_4 planarity.\<close>
      and "e12 \<inter> e34 = {}" and "e23 \<inter> e41 = {}"
      and "e12 \<inter> e23 = {a2}" and "e23 \<inter> e34 = {a3}"
      and "e34 \<inter> e41 = {a4}" and "e41 \<inter> e12 = {a1}"
      and "e13 \<inter> e12 = {a1}" and "e13 \<inter> e23 = {a3}"
      and "e13 \<inter> e34 = {a3}" and "e13 \<inter> e41 = {a1}"
      and "e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}"
      and "e24 \<inter> e12 = {a2}" and "e24 \<inter> e23 = {a2}"
      and "e24 \<inter> e34 = {a4}" and "e24 \<inter> e41 = {a4}"
      \<comment> \<open>p, q are interior points of diagonals.\<close>
      and "p \<in> e13 - {a1, a3}" and "q \<in> e24 - {a2, a4}"
      \<comment> \<open>C is the 4-cycle.\<close>
      and "C = e12 \<union> e23 \<union> e34 \<union> e41"
      \<comment> \<open>Basepoint.\<close>
      and "c0 \<in> C"
  shows "top1_group_iso_on
    (top1_fundamental_group_carrier C
       (subspace_topology top1_S2 top1_S2_topology C) c0)
    (top1_fundamental_group_mul C
       (subspace_topology top1_S2 top1_S2_topology C) c0)
    (top1_fundamental_group_carrier (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0)
    (top1_fundamental_group_mul (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0)
    (top1_fundamental_group_induced_on C
       (subspace_topology top1_S2 top1_S2_topology C) c0
       (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0 id)"
proof -
  let ?X = "top1_S2 - {p} - {q}"
  let ?TX = "subspace_topology top1_S2 top1_S2_topology ?X"
  let ?TC = "subspace_topology top1_S2 top1_S2_topology C"
  let ?j_star = "top1_fundamental_group_induced_on C ?TC c0 ?X ?TX c0 id"
  \<comment> \<open>Step 1: C \<subseteq> X (p \<notin> C, q \<notin> C).\<close>
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology" by (rule top1_S2_is_hausdorff)
  \<comment> \<open>C \<subseteq> S2.\<close>
  have hC_sub_S2: "C \<subseteq> top1_S2" using assms(4,5,6,7,39) by (by100 blast)
  \<comment> \<open>p \<notin> C, q \<notin> C (p interior to diagonal e13, q interior to e24, both disjoint from C).\<close>
  have hp_not_C: "p \<notin> C"
  proof -
    have "p \<in> e13" "p \<noteq> a1" "p \<noteq> a3" using assms(37) by (by100 blast)+
    have "p \<notin> e12" using \<open>p \<in> e13\<close> \<open>p \<noteq> a1\<close> assms(28) by (by100 blast)
    moreover have "p \<notin> e23" using \<open>p \<in> e13\<close> \<open>p \<noteq> a3\<close> assms(29) by (by100 blast)
    moreover have "p \<notin> e34" using \<open>p \<in> e13\<close> \<open>p \<noteq> a3\<close> assms(30) by (by100 blast)
    moreover have "p \<notin> e41" using \<open>p \<in> e13\<close> \<open>p \<noteq> a1\<close> assms(31) by (by100 blast)
    ultimately show ?thesis using assms(39) by (by100 blast)
  qed
  have hq_not_C: "q \<notin> C"
  proof -
    have "q \<in> e24" "q \<noteq> a2" "q \<noteq> a4" using assms(38) by (by100 blast)+
    have "q \<notin> e12" using \<open>q \<in> e24\<close> \<open>q \<noteq> a2\<close> assms(33) by (by100 blast)
    moreover have "q \<notin> e23" using \<open>q \<in> e24\<close> \<open>q \<noteq> a2\<close> assms(34) by (by100 blast)
    moreover have "q \<notin> e34" using \<open>q \<in> e24\<close> \<open>q \<noteq> a4\<close> assms(35) by (by100 blast)
    moreover have "q \<notin> e41" using \<open>q \<in> e24\<close> \<open>q \<noteq> a4\<close> assms(36) by (by100 blast)
    ultimately show ?thesis using assms(39) by (by100 blast)
  qed
  have hC_sub_X: "C \<subseteq> ?X" using hC_sub_S2 hp_not_C hq_not_C by (by100 blast)
  have hc0_X: "c0 \<in> ?X" using assms(40) hC_sub_X by (by100 blast)
  \<comment> \<open>Step 2: j\_* is a homomorphism.\<close>
  have hTX: "is_topology_on ?X ?TX"
    by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
  have hTC: "is_topology_on C ?TC"
    by (rule subspace_topology_is_topology_on[OF hTopS2]) (use hC_sub_S2 in \<open>by100 blast\<close>)
  have hj_cont: "top1_continuous_map_on C ?TC ?X ?TX id"
  proof -
    have hid_S2: "top1_continuous_map_on C ?TC top1_S2 top1_S2_topology id"
      using Theorem_18_2[OF hTopS2 hTopS2 hTopS2] hC_sub_S2 by (by100 blast)
    have himg: "\<forall>s\<in>C. s \<in> ?X" using hC_sub_X by (by100 blast)
    have "top1_continuous_map_on C ?TC ?X ?TX id"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x assume "x \<in> C"
      hence "x \<in> ?X" using hC_sub_X by (by100 blast)
      thus "id x \<in> ?X" by (by100 simp)
    next
      fix V assume "V \<in> ?TX"
      hence "\<exists>U \<in> top1_S2_topology. V = ?X \<inter> U"
        unfolding subspace_topology_def by (by100 blast)
      then obtain U where "U \<in> top1_S2_topology" "V = ?X \<inter> U" by (by100 blast)
      have "{x \<in> C. id x \<in> V} = {x \<in> C. x \<in> V}" by (by100 simp)
      also have "\<dots> = C \<inter> V" by (by100 blast)
      also have "\<dots> = C \<inter> (?X \<inter> U)" using \<open>V = ?X \<inter> U\<close> by (by100 simp)
      also have "\<dots> = C \<inter> U" using hC_sub_X by (by100 blast)
      also have "\<dots> = {x \<in> C. id x \<in> U}" by auto
      finally have "{x \<in> C. id x \<in> V} = {x \<in> C. id x \<in> U}" .
      moreover have "{x \<in> C. id x \<in> U} \<in> ?TC"
        using hid_S2 \<open>U \<in> top1_S2_topology\<close> unfolding top1_continuous_map_on_def by (by100 blast)
      ultimately show "{x \<in> C. id x \<in> V} \<in> ?TC" by (by100 simp)
    qed
    thus ?thesis .
  qed
  have hj_star_hom: "top1_group_hom_on
      (top1_fundamental_group_carrier C ?TC c0) (top1_fundamental_group_mul C ?TC c0)
      (top1_fundamental_group_carrier ?X ?TX c0) (top1_fundamental_group_mul ?X ?TX c0) ?j_star"
    by (rule top1_fundamental_group_induced_on_is_hom[OF hTC hTX assms(40) hc0_X hj_cont])
       (by100 simp)
  \<comment> \<open>Step 3: Both groups are infinite cyclic (\<cong> Z).
     From existing infrastructure: SCC\_pi1\_iso\_Z and pi1\_S2\_minus\_two\_points.\<close>
  have hC_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  proof -
    \<comment> \<open>C = (e12\<union>e23) \<union> (e34\<union>e41). Each half is an arc from a1 to a3 (resp a3 to a1).\<close>
    have ha1_ne_a2: "a1 \<noteq> a2" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha1_ne_a3: "a1 \<noteq> a3" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha3_ne_a4: "a3 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha1_ne_a4: "a1 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha2_e12: "a2 \<in> top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
      using assms(16) by (by100 blast)
    have ha2_e23: "a2 \<in> top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      using assms(17) by (by100 blast)
    have hArc1_arc: "top1_is_arc_on (e12 \<union> e23) (subspace_topology top1_S2 top1_S2_topology (e12 \<union> e23))"
      by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus assms(10,4,11,5) assms(24) ha2_e12 ha2_e23])
    have ha4_e34: "a4 \<in> top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
      using assms(18) by (by100 blast)
    have ha4_e41: "a4 \<in> top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
      using assms(19) by (by100 blast)
    have hArc2_arc: "top1_is_arc_on (e34 \<union> e41) (subspace_topology top1_S2 top1_S2_topology (e34 \<union> e41))"
      by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus assms(12,6,13,7) assms(26) ha4_e34 ha4_e41])
    have hArc1_sub: "e12 \<union> e23 \<subseteq> top1_S2" using assms(4,5) by (by100 blast)
    have hArc2_sub: "e34 \<union> e41 \<subseteq> top1_S2" using assms(6,7) by (by100 blast)
    have ha2_ne_a1: "a2 \<noteq> a1" using ha1_ne_a2 by (by100 blast)
    have ha2_ne_a3: "a2 \<noteq> a3" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have hep_e23_swap: "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a3, a2}"
      using assms(17) by (by100 blast)
    have hArc1_ep: "top1_arc_endpoints_on (e12 \<union> e23) (subspace_topology top1_S2 top1_S2_topology (e12 \<union> e23)) = {a1, a3}"
      by (rule arc_concat_endpoints[OF assms(1) hS2_haus assms(10,4,11,5) assms(24) ha2_e12 ha2_e23
          assms(16) assms(17) ha1_ne_a2 ha2_ne_a3])
    have ha4_ne_a3: "a4 \<noteq> a3" using ha3_ne_a4 by (by100 blast)
    have ha4_ne_a1: "a4 \<noteq> a1" using ha1_ne_a4 by (by100 blast)
    have hep_e41_swap: "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a1, a4}"
      using assms(19) by (by100 blast)
    have hArc2_ep: "top1_arc_endpoints_on (e34 \<union> e41) (subspace_topology top1_S2 top1_S2_topology (e34 \<union> e41)) = {a3, a1}"
      by (rule arc_concat_endpoints[OF assms(1) hS2_haus assms(12,6,13,7) assms(26) ha4_e34 ha4_e41
          assms(18) assms(19) ha3_ne_a4 ha4_ne_a1])
    have hint: "(e12 \<union> e23) \<inter> (e34 \<union> e41) = {a1, a3}"
    proof -
      have "e12 \<inter> e34 = {}" by (rule assms(22))
      moreover have "e12 \<inter> e41 = {a1}" using assms(27) by (by100 blast)
      moreover have "e23 \<inter> e34 = {a3}" by (rule assms(25))
      moreover have "e23 \<inter> e41 = {}" by (rule assms(23))
      ultimately show ?thesis by (by100 blast)
    qed
    have hArc2_ep': "top1_arc_endpoints_on (e34 \<union> e41) (subspace_topology top1_S2 top1_S2_topology (e34 \<union> e41)) = {a1, a3}"
      using hArc2_ep by (by100 blast)
    have "top1_simple_closed_curve_on top1_S2 top1_S2_topology ((e12 \<union> e23) \<union> (e34 \<union> e41))"
      by (rule arcs_form_simple_closed_curve[OF assms(1) hS2_haus hArc1_arc hArc1_sub
          hArc2_arc hArc2_sub hint ha1_ne_a3 hArc1_ep hArc2_ep'])
    moreover have "(e12 \<union> e23) \<union> (e34 \<union> e41) = C" using assms(39) by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  have hp_ne_q: "p \<noteq> q"
  proof
    assume "p = q"
    have "p \<in> e13" using assms(37) by (by100 blast)
    have "p \<in> e24" using \<open>p = q\<close> assms(38) by (by100 blast)
    hence "p \<in> e13 \<inter> e24" using \<open>p \<in> e13\<close> by (by100 blast)
    hence "p \<in> {a1,a2,a3,a4}" using assms(32) by (by100 blast)
    moreover have "p \<noteq> a1" "p \<noteq> a3" using assms(37) by (by100 blast)+
    moreover have "p \<noteq> a2" "p \<noteq> a4" using \<open>p = q\<close> assms(38) by (by100 blast)+
    ultimately show False by (by100 blast)
  qed
  have hp_S2: "p \<in> top1_S2" using assms(8,37) by (by100 blast)
  have hq_S2: "q \<in> top1_S2" using assms(9,38) by (by100 blast)
  have hC_pi1_Z: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier C ?TC c0) (top1_fundamental_group_mul C ?TC c0)
      top1_Z_group top1_Z_mul"
    by (rule SCC_pi1_iso_Z[OF assms(1) hC_scc assms(40)])
  have hX_pi1_Z: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier ?X ?TX c0) (top1_fundamental_group_mul ?X ?TX c0)
      top1_Z_group top1_Z_mul"
    by (rule pi1_S2_minus_two_points_iso_Z[OF assms(1) hp_S2 hq_S2 hp_ne_q hc0_X])
  \<comment> \<open>Step 4 (KEY - textbook 65.1(b)): j\_* is surjective.
     Construct \<alpha>*\<beta> loop in C that generates \<pi>_1(X) via Theorem 63.1.
     j\_*([a*b]\_C) = [a*b]\_X = generator. Generator hit \<Rightarrow> surjective.\<close>
  have hj_star_surj: "?j_star ` (top1_fundamental_group_carrier C ?TC c0) =
      top1_fundamental_group_carrier ?X ?TX c0"
  proof -
    \<comment> \<open>Textbook 65.1(b): Construct \<alpha>*\<beta> loop in C that generates \<pi>_1(X).
       Since \<alpha>*\<beta> \<in> C: j\_*([a*b]\_C) = [a*b]\_X = generator.
       Every element of \<pi>_1(X) is a power of the generator = j\_*(power in \<pi>_1(C)).
       Hence j\_* is surjective.\<close>
    \<comment> \<open>Step A: There exists a loop g in C, based at some point x \<in> C,
       that generates \<pi>_1(X, x). (From Theorem 63.1 + K4 structure.)\<close>
    from K4_generator_loop_in_C[OF assms(1-39)]
    obtain x g where hx_C: "x \<in> C"
        and hg_loop_C: "top1_is_loop_on C ?TC x g"
        and hg_loop_X: "top1_is_loop_on ?X ?TX x g"
        and hg_generates: "\<forall>f. top1_is_loop_on ?X ?TX x f \<longrightarrow>
            (\<exists>n::nat. top1_path_homotopic_on ?X ?TX x x f (top1_path_power g x n)
              \<or> top1_path_homotopic_on ?X ?TX x x f (top1_path_power (top1_path_reverse g) x n))"
      by (by100 blast)
    \<comment> \<open>Step B: j\_*([g]\_C) = [g]\_X (inclusion sends loop class to itself).
       Step C: [g] generates \<pi>_1(X), so j\_* is surjective.
       Step D: Basepoint change from x to c0.\<close>
    \<comment> \<open>j\_*([g]\_C) = [g]\_X by inclusion\_induced\_class.\<close>
    have hx_X: "x \<in> ?X" using hx_C hC_sub_X by (by100 blast)
    let ?j_star_x = "top1_fundamental_group_induced_on C ?TC x ?X ?TX x id"
    \<comment> \<open>Note: inclusion uses (\<lambda>x. x) not id in the library.\<close>
    let ?j_star_x_lam = "top1_fundamental_group_induced_on C ?TC x ?X ?TX x (\<lambda>x. x)"
    have hj_star_x_class: "?j_star_x_lam {h. top1_loop_equiv_on C ?TC x g h} =
        {k. top1_loop_equiv_on ?X ?TX x g k}"
    proof -
      have hTC_eq: "subspace_topology ?X ?TX C = ?TC"
        using subspace_topology_trans[of C ?X top1_S2 top1_S2_topology] hC_sub_X by (by100 simp)
      have hg_loop_C': "top1_is_loop_on C (subspace_topology ?X ?TX C) x g"
        using hg_loop_C hTC_eq by (by100 simp)
      from subspace_inclusion_induced_class[OF hTX hC_sub_X hg_loop_C']
      have "top1_fundamental_group_induced_on C (subspace_topology ?X ?TX C) x ?X ?TX x (\<lambda>x. x)
          {k. top1_loop_equiv_on C (subspace_topology ?X ?TX C) x g k} =
          {k. top1_loop_equiv_on ?X ?TX x g k}" .
      thus ?thesis using hTC_eq by (by100 simp)
    qed
    \<comment> \<open>Note: ?j\_star and ?j\_star\_x\_lam agree extensionally (id = \<lambda>x. x).\<close>
    \<comment> \<open>Every element of \<pi>_1(X,x) is a power of [g]\_X. Since each power lifts
       from C (g^n is a loop in C): j\_*\_x is surjective.\<close>
    \<comment> \<open>Surjectivity at x, then basepoint change to c0.\<close>
    have hj_star_x_surj: "?j_star_x ` (top1_fundamental_group_carrier C ?TC x) =
        top1_fundamental_group_carrier ?X ?TX x"
    proof (intro set_eqI iffI)
      \<comment> \<open>(\<subseteq>): image of carrier \<subseteq> carrier. Follows from j\_* being a homomorphism.\<close>
      fix c assume "c \<in> ?j_star_x ` (top1_fundamental_group_carrier C ?TC x)"
      then obtain d where "d \<in> top1_fundamental_group_carrier C ?TC x" "c = ?j_star_x d"
        by (by100 blast)
      \<comment> \<open>j\_star\_x maps carrier to carrier (hom property at basepoint x).\<close>
      have "top1_group_hom_on
          (top1_fundamental_group_carrier C ?TC x) (top1_fundamental_group_mul C ?TC x)
          (top1_fundamental_group_carrier ?X ?TX x) (top1_fundamental_group_mul ?X ?TX x) ?j_star_x"
        sorry \<comment> \<open>induced\_on\_is\_hom at basepoint x.\<close>
      hence "?j_star_x d \<in> top1_fundamental_group_carrier ?X ?TX x"
        using \<open>d \<in> _\<close> unfolding top1_group_hom_on_def by (by100 blast)
      thus "c \<in> top1_fundamental_group_carrier ?X ?TX x" using \<open>c = _\<close> by (by100 blast)
    next
      \<comment> \<open>(\<supseteq>): every [f]\_X is hit. Key argument.\<close>
      fix c assume hc: "c \<in> top1_fundamental_group_carrier ?X ?TX x"
      \<comment> \<open>c = [f] for some loop f in X.\<close>
      then obtain f where hf: "top1_is_loop_on ?X ?TX x f"
          and hc_eq: "c = {h. top1_loop_equiv_on ?X ?TX x f h}"
        unfolding top1_fundamental_group_carrier_def by (by100 blast)
      \<comment> \<open>f \<simeq> g^n or g\_rev^n.\<close>
      from hg_generates hf
      obtain n where "top1_path_homotopic_on ?X ?TX x x f (top1_path_power g x n)
          \<or> top1_path_homotopic_on ?X ?TX x x f (top1_path_power (top1_path_reverse g) x n)"
        by (by100 blast)
      \<comment> \<open>In either case: the power is a loop in C, and j\_* maps it to [f].\<close>
      \<comment> \<open>For either g^n or (g\_rev)^n: it's a loop in C, and j\_* maps its class to [f].\<close>
      thus "c \<in> ?j_star_x ` (top1_fundamental_group_carrier C ?TC x)"
      proof (elim disjE)
        assume hfgn: "top1_path_homotopic_on ?X ?TX x x f (top1_path_power g x n)"
        \<comment> \<open>g^n is a loop in C.\<close>
        \<comment> \<open>g^n loop in C. j\_*([g^n]\_C) = [g^n]\_X = [f]\_X = c. So c \<in> image(j\_*).\<close>
        show ?thesis sorry \<comment> \<open>top1\_path\_power\_is\_loop + inclusion\_induced\_class + homotopy class eq.\<close>
      next
        assume hfgrn: "top1_path_homotopic_on ?X ?TX x x f (top1_path_power (top1_path_reverse g) x n)"
        \<comment> \<open>Same argument with g\_rev instead of g.\<close>
        show ?thesis sorry
      qed
    qed
    \<comment> \<open>Transfer surjectivity from x to c0 via basepoint change (C path-connected).\<close>
    show ?thesis sorry \<comment> \<open>Basepoint change: surj at x \<Rightarrow> surj at c0.\<close>
  qed
  \<comment> \<open>Step 5: Surjective hom Z \<rightarrow> Z is injective (hence bijective).\<close>
  have hj_star_inj: "inj_on ?j_star (top1_fundamental_group_carrier C ?TC c0)" sorry
  \<comment> \<open>Combine.\<close>
  have hj_star_bij: "bij_betw ?j_star
      (top1_fundamental_group_carrier C ?TC c0) (top1_fundamental_group_carrier ?X ?TX c0)"
    unfolding bij_betw_def using hj_star_inj hj_star_surj by (by100 blast)
  show ?thesis unfolding top1_group_iso_on_def using hj_star_hom hj_star_bij by (by100 blast)
qed

section \<open>Theorem 65.2 (fixed): inclusion C \<hookrightarrow> S2-{p,q} induces iso (general SCC)\<close>

text \<open>Munkres Theorem 65.2: Let C be a simple closed curve in S2; let p and q lie
  in different components of S2-C. Then the inclusion j: C \<rightarrow> S2-p-q induces
  an isomorphism of fundamental groups.\<close>

theorem Theorem_65_2_fixed:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  and "p \<in> top1_S2 - C" and "q \<in> top1_S2 - C"
  \<comment> \<open>p, q in different path-components of S2 - C.\<close>
  and "\<not> (\<exists>f. top1_is_path_on (top1_S2 - C)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p q f)"
  and "c0 \<in> C"
  shows "top1_group_iso_on
    (top1_fundamental_group_carrier C (subspace_topology top1_S2 top1_S2_topology C) c0)
    (top1_fundamental_group_mul C (subspace_topology top1_S2 top1_S2_topology C) c0)
    (top1_fundamental_group_carrier (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0)
    (top1_fundamental_group_mul (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0)
    (top1_fundamental_group_induced_on C
       (subspace_topology top1_S2 top1_S2_topology C) c0
       (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0 id)"
  sorry

end
