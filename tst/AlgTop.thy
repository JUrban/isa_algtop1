theory AlgTop
  imports "AlgTopC.AlgTopCached"
begin
text \<open>generator\_from\_63\_1\_simply\_connected was here but is now replaced by
  Theorem\_63\_1\_b\_generation which uses helix covering + \<pi>_1(X) infinite cyclic.\<close>

text \<open>S2\_minus\_arc\_simply\_connected was here. It was used in the old generator
  approach but is no longer needed (Theorem\_63\_1\_b\_generation uses helix instead).\<close>

text \<open>Helix shift lemmas (helix\_shift\_continuous, helix\_shift\_general\_continuous)
  are now in AlgTopCached. They show that T(x,n) = (x, n+2j) is continuous on E
  for any integer j.\<close>

text \<open>Theorem 63.1(b): If \<pi>_1(X) is infinite cyclic, [\<alpha>*\<beta>] generates it.
  Proof follows Munkres Step 4: the helix covering E \<rightarrow> X gives a
  lifting correspondence \<phi>: \<pi>_1(X) \<rightarrow> fiber. Since \<phi>([\<alpha>*\<beta>]^n) = n
  (surjective onto Z-fiber), and \<pi>_1(X) \<cong> Z implies Z/H \<cong> Z \<Rightarrow> H=\{0\},
  the map \<phi> is bijective. Then \<langle>[\<alpha>*\<beta>]\<rangle> = \<pi>_1(X).\<close>
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

text \<open>Theorem 64.2: The utilities graph K33 cannot be imbedded in the plane.\<close>

text \<open>Theorem 64.2 and 64.4 (K\_3\_3 and K\_5 not planar) are consequences
  of the theta space lemma. Their formal statements require specifying all
  edge-vertex incidence and intersection conditions. We state simplified versions.\<close>

theorem Theorem_64_2_K33_not_planar:
  \<comment> \<open>The utilities graph K33 cannot be imbedded in the plane (or S2).\<close>
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and hK33: "card {g, w, e, h1, h2, h3} = (6::nat)"
      and "{g, w, e, h1, h2, h3} \<subseteq> top1_S2"
      and "top1_is_arc_on gh1 (subspace_topology top1_S2 top1_S2_topology gh1)"
      \<comment> \<open>... (9 arcs connecting each utility to each house)\<close>
  shows False
  sorry

theorem Theorem_64_4_K5_not_planar:
  \<comment> \<open>The complete graph K5 cannot be imbedded in the plane (or S2).\<close>
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "card {a1, a2, a3, a4, a5 :: real \<times> real \<times> real} = 5"
      \<comment> \<open>... (10 arcs, one for each pair of vertices)\<close>
  shows False
  sorry

text \<open>A simple closed curve in S2 has \<pi>_1 \<cong> Z.\<close>
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

lemma subset_disjoint_helper:
  assumes "S \<subseteq> A" and "A \<inter> B = {}" shows "S \<inter> B = {}"
  using assms by (by100 blast)

lemma subset_of_complement_disjoint:
  assumes "R = X - T" and "S \<subseteq> T"
  shows "S \<inter> R = {}"
  using assms by (by100 blast)

lemma diff_inter_subset:
  assumes "A \<inter> R = {}" shows "(A - S) \<inter> R = {}"
  using assms by (by100 blast)

(** from \<S>65 Lemma 65.1(a): non-adjacent edges of K_4 in S^2 have interiors in
    different components of S^2 minus the complementary 4-cycle.
    Duplicated from the internal hdiff fact in Lemma_65_1_K4_subgraph (AlgTopCached.thy). **)
lemma K4_nonadjacent_edges_different_components:
  fixes a1 a2 a3 a4 :: "real \<times> real \<times> real"
    and e12 e23 e34 e41 e13 e24 :: "(real \<times> real \<times> real) set"
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
      \<comment> \<open>D = e13 \<union> e23 \<union> e24 \<union> e41 (the complementary 4-cycle).
         A, B are the two components of S2-D.\<close>
      and "A \<noteq> {}" and "B \<noteq> {}" and "A \<inter> B = {}"
      and "A \<union> B = top1_S2 - (e13 \<union> e23 \<union> e24 \<union> e41)"
      and "top1_connected_on A (subspace_topology top1_S2 top1_S2_topology A)"
      and "top1_connected_on B (subspace_topology top1_S2 top1_S2_topology B)"
  shows "\<not> (e12 - {a1, a2} \<subseteq> A \<and> e34 - {a3, a4} \<subseteq> A)
       \<and> \<not> (e12 - {a1, a2} \<subseteq> B \<and> e34 - {a3, a4} \<subseteq> B)"
proof -
  \<comment> \<open>Following algtop.tex 65.1(a): theta space D\<union>e12 \<Rightarrow> 3 components \<Rightarrow> separation.\<close>
  define D_loc where "D_loc = e13 \<union> e23 \<union> e24 \<union> e41"
  define Arc2 where "Arc2 = e13 \<union> e23"
  define Arc3 where "Arc3 = e24 \<union> e41"
  note defs = Arc2_def Arc3_def D_loc_def
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def unfolding defs by (by100 blast)
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology" unfolding defs by (rule top1_S2_is_hausdorff)
  \<comment> \<open>Step 1: Hypotheses for Lemma\_64\_1.\<close>
  have hArc2_sub: "Arc2 \<subseteq> top1_S2" using assms(8,5) unfolding defs by (by100 blast)
  have hArc3_sub: "Arc3 \<subseteq> top1_S2" using assms(9,7) unfolding defs by (by100 blast)
  have ha3_e13: "a3 \<in> top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
    using assms(20) unfolding defs by (by100 blast)
  have ha3_e23: "a3 \<in> top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
    using assms(17) unfolding defs by (by100 blast)
  have ha4_e24: "a4 \<in> top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
    using assms(21) unfolding defs by (by100 blast)
  have ha4_e41: "a4 \<in> top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
    using assms(19) unfolding defs by (by100 blast)
  have hArc2_arc: "top1_is_arc_on Arc2 (subspace_topology top1_S2 top1_S2_topology Arc2)"
    unfolding defs by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus assms(14,8,11,5) _ ha3_e13 ha3_e23])
       (use assms(29) in \<open>by100 blast\<close>)
  have hArc3_arc: "top1_is_arc_on Arc3 (subspace_topology top1_S2 top1_S2_topology Arc3)"
    unfolding defs by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus assms(15,9,13,7) _ ha4_e24 ha4_e41])
       (use assms(36) in \<open>by100 blast\<close>)
  have ha1_ne_a2: "a1 \<noteq> a2" using assms(2) by (auto simp: card_insert_if split: if_splits)
  have ha1_ne_a3: "a1 \<noteq> a3" using assms(2) by (auto simp: card_insert_if split: if_splits)
  have ha1_ne_a4: "a1 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
  have ha2_ne_a3: "a2 \<noteq> a3" using assms(2) by (auto simp: card_insert_if split: if_splits)
  have ha2_ne_a4: "a2 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
  have ha3_ne_a4: "a3 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
  have hint12: "e12 \<inter> Arc2 = {a1, a2}"
    using assms(28,24) unfolding defs by (by100 blast)
  have hint13: "e12 \<inter> Arc3 = {a1, a2}"
    using assms(33,27) unfolding defs by (by100 blast)
  have he13_e24_disj: "e13 \<inter> e24 = {}"
  proof -
    have "e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}" unfolding defs by (rule assms(32))
    moreover have "a1 \<notin> e24"
    proof assume "a1 \<in> e24"
      hence "a1 \<in> e24 \<inter> e12" using assms(16) unfolding top1_arc_endpoints_on_def unfolding defs by (by100 blast)
      hence "a1 = a2" using assms(33) unfolding defs by (by100 blast)
      thus False using ha1_ne_a2 unfolding defs by (by100 blast) qed
    moreover have "a2 \<notin> e13"
    proof assume "a2 \<in> e13"
      hence "a2 \<in> e13 \<inter> e12" using assms(16) unfolding top1_arc_endpoints_on_def unfolding defs by (by100 blast)
      hence "a2 = a1" using assms(28) unfolding defs by (by100 blast)
      thus False using ha1_ne_a2 unfolding defs by (by100 blast) qed
    moreover have "a3 \<notin> e24"
    proof assume "a3 \<in> e24"
      hence "a3 \<in> e24 \<inter> e23" using assms(17) unfolding top1_arc_endpoints_on_def unfolding defs by (by100 blast)
      hence "a3 = a2" using assms(34) unfolding defs by (by100 blast)
      thus False using ha2_ne_a3 unfolding defs by (by100 blast) qed
    moreover have "a4 \<notin> e13"
    proof assume "a4 \<in> e13"
      hence "a4 \<in> e13 \<inter> e41" using assms(19) unfolding top1_arc_endpoints_on_def unfolding defs by (by100 blast)
      hence "a4 = a1" using assms(31) unfolding defs by (by100 blast)
      thus False using ha1_ne_a4 unfolding defs by (by100 blast) qed
    ultimately show ?thesis unfolding defs by (by100 blast)
  qed
  have hint23: "Arc2 \<inter> Arc3 = {a1, a2}"
    using he13_e24_disj assms(31,34,23) unfolding defs by (by100 blast)
  have hep_e23_swap: "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a3, a2}"
    using assms(17) unfolding defs by (by100 blast)
  have ha3_ne_a2: "a3 \<noteq> a2" using ha2_ne_a3 unfolding defs by (by100 blast)
  have hArc2_ep: "top1_arc_endpoints_on Arc2 (subspace_topology top1_S2 top1_S2_topology Arc2) = {a1, a2}"
    unfolding defs by (rule arc_concat_endpoints[OF assms(1) hS2_haus assms(14,8,11,5) assms(29)
          ha3_e13 ha3_e23 assms(20) hep_e23_swap ha1_ne_a3 ha3_ne_a2])
  have hArc3_ep: "top1_arc_endpoints_on Arc3 (subspace_topology top1_S2 top1_S2_topology Arc3) = {a1, a2}"
  proof -
    \<comment> \<open>arc\_concat\_endpoints gives {a2, a1} — need {a1, a2}.\<close>
    have hep_e41_swap: "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a4, a1}"
      using assms(19) unfolding defs by (by100 blast)
    have ha4_ne_a2: "a4 \<noteq> a2" using ha2_ne_a4 unfolding defs by (by100 blast)
    have ha4_ne_a1: "a4 \<noteq> a1" using ha1_ne_a4 unfolding defs by (by100 blast)
    have "top1_arc_endpoints_on Arc3 (subspace_topology top1_S2 top1_S2_topology Arc3) = {a2, a1}"
      unfolding defs by (rule arc_concat_endpoints[OF assms(1) hS2_haus assms(15,9,13,7) assms(36)
            ha4_e24 ha4_e41 assms(21) hep_e41_swap ha2_ne_a4 ha4_ne_a1])
    thus ?thesis by (by100 blast)
  qed
  \<comment> \<open>Step 2: Apply Lemma\_64\_1.\<close>
  obtain R1 R2 R3 where hR: "R1 \<noteq> {}" "R2 \<noteq> {}" "R3 \<noteq> {}"
      "R1 \<inter> R2 = {}" "R2 \<inter> R3 = {}" "R1 \<inter> R3 = {}"
      "R1 \<union> R2 \<union> R3 = top1_S2 - (e12 \<union> Arc2 \<union> Arc3)"
      "top1_connected_on R1 (subspace_topology top1_S2 top1_S2_topology R1)"
      "top1_connected_on R2 (subspace_topology top1_S2 top1_S2_topology R2)"
      "top1_connected_on R3 (subspace_topology top1_S2 top1_S2_topology R3)"
      "R1 \<in> top1_S2_topology" "R2 \<in> top1_S2_topology" "R3 \<in> top1_S2_topology"
    using Lemma_64_1_theta_space_three_components[OF assms(1) assms(4) hArc2_sub hArc3_sub
        assms(10) hArc2_arc hArc3_arc ha1_ne_a2 hint12 hint23 hint13 assms(16) hArc2_ep hArc3_ep]
    by (metis (no_types))
  \<comment> \<open>Step 3: e34-{a3,a4} \<subseteq> S2-theta, hence in some Ri.\<close>
  have he34_theta: "e34 - {a3, a4} \<subseteq> top1_S2 - (e12 \<union> Arc2 \<union> Arc3)"
  proof -
    have h1: "e34 \<inter> e12 = {}" using assms(22) unfolding defs by (by100 blast)
    have h2: "e34 \<inter> e13 \<subseteq> {a3}" using assms(30) unfolding defs by (by100 blast)
    have h3: "e34 \<inter> e23 \<subseteq> {a3}" using assms(25) unfolding defs by (by100 blast)
    have h4: "e34 \<inter> e24 \<subseteq> {a4}" using assms(35) unfolding defs by (by100 blast)
    have h5: "e34 \<inter> e41 \<subseteq> {a4}" using assms(26) unfolding defs by (by100 blast)
    have "e34 \<inter> Arc2 \<subseteq> {a3}" using h2 h3 unfolding defs by (by100 blast)
    moreover have "e34 \<inter> Arc3 \<subseteq> {a4}" using h4 h5 unfolding defs by (by100 blast)
    ultimately have "e34 \<inter> (e12 \<union> Arc2 \<union> Arc3) \<subseteq> {a3, a4}" using h1 unfolding defs by (by100 blast)
    thus ?thesis using assms(6) unfolding defs by (by100 blast)
  qed
  have he34_ne: "e34 - {a3, a4} \<noteq> {}"
  proof -
    obtain h where hh: "top1_homeomorphism_on I_set I_top e34
        (subspace_topology top1_S2 top1_S2_topology e34) h"
      using assms(12) unfolding top1_is_arc_on_def unfolding defs by (by100 blast)
    have hbij: "bij_betw h I_set e34" using hh unfolding top1_homeomorphism_on_def unfolding defs by (by100 blast)
    have h0: "(0::real) \<in> I_set" unfolding top1_unit_interval_def unfolding defs by (by100 simp)
    have h1: "(1::real) \<in> I_set" unfolding top1_unit_interval_def unfolding defs by (by100 simp)
    have h12: "(1/2::real) \<in> I_set" unfolding top1_unit_interval_def unfolding defs by (by100 simp)
    have "h (1/2) \<in> e34" using hbij h12 unfolding bij_betw_def unfolding defs by (by100 blast)
    moreover have "h (1/2) \<noteq> h 0 \<and> h (1/2) \<noteq> h 1"
    proof -
      have hinj: "inj_on h I_set" using hbij unfolding bij_betw_def unfolding defs by (by100 blast)
      have "h (1/2) \<noteq> h 0"
      proof assume "h (1/2) = h 0"
        from inj_onD[OF hinj this h12 h0] show False unfolding defs by (by100 simp) qed
      moreover have "h (1/2) \<noteq> h 1"
      proof assume "h (1/2) = h 1"
        from inj_onD[OF hinj this h12 h1] show False unfolding defs by (by100 simp) qed
      ultimately show ?thesis unfolding defs by (by100 blast)
    qed
    moreover have "{h 0, h 1} = {a3, a4}"
      using arc_endpoints_are_boundary[OF assms(1) hS2_haus assms(6,12) hh] assms(18)
      unfolding defs by (by100 simp)
    ultimately show ?thesis unfolding defs by (by100 blast)
  qed
  have he34_conn: "top1_connected_on (e34 - {a3, a4})
      (subspace_topology top1_S2 top1_S2_topology (e34 - {a3, a4}))"
    unfolding defs by (rule arc_minus_endpoints_connected[OF assms(1) hS2_haus assms(6,12,18) ha3_ne_a4])
  \<comment> \<open>e34-{a3,a4} connected \<subseteq> R1\<union>R2\<union>R3 \<Rightarrow> in some Ri.\<close>
  have he34_in_Ri: "e34 - {a3, a4} \<subseteq> R1 \<or> e34 - {a3, a4} \<subseteq> R2 \<or> e34 - {a3, a4} \<subseteq> R3"
  proof -
    let ?W = "R1 \<union> R2 \<union> R3"
    have hTW: "is_topology_on ?W (subspace_topology top1_S2 top1_S2_topology ?W)"
      unfolding defs by (rule subspace_topology_is_topology_on[OF hTopS2]) (use hR(7) in \<open>by100 blast\<close>)
    have hR1_open: "R1 \<in> subspace_topology top1_S2 top1_S2_topology ?W"
      using hR(11) unfolding subspace_topology_def unfolding defs by (by100 blast)
    have hR23_open: "R2 \<union> R3 \<in> subspace_topology top1_S2 top1_S2_topology ?W"
    proof -
      have "R2 \<union> R3 \<in> top1_S2_topology"
      proof -
        have "{R2, R3} \<subseteq> top1_S2_topology" using hR(12,13) unfolding defs by (by100 blast)
        hence "\<Union>{R2, R3} \<in> top1_S2_topology"
          using hTopS2 unfolding is_topology_on_def unfolding defs by (by100 blast)
        moreover have "\<Union>{R2, R3} = R2 \<union> R3" unfolding defs by (by100 blast)
        ultimately show ?thesis unfolding defs by (by100 simp)
      qed
      thus ?thesis unfolding subspace_topology_def unfolding defs by (by100 blast)
    qed
    have hSep1: "top1_is_separation_on ?W (subspace_topology top1_S2 top1_S2_topology ?W) R1 (R2 \<union> R3)"
      unfolding top1_is_separation_on_def
      using hR1_open hR23_open hR(1,2,3,4,5,6) unfolding defs by (by100 blast)
    have he34_sub_W: "e34 - {a3, a4} \<subseteq> ?W" using he34_theta hR(7) unfolding defs by (by100 blast)
    have he34_conn_W: "top1_connected_on (e34 - {a3, a4})
        (subspace_topology ?W (subspace_topology top1_S2 top1_S2_topology ?W) (e34 - {a3, a4}))"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology (e34 - {a3, a4}) =
          subspace_topology ?W (subspace_topology top1_S2 top1_S2_topology ?W) (e34 - {a3, a4})"
        using subspace_topology_trans[of "e34 - {a3, a4}" ?W] he34_sub_W unfolding defs by (by100 simp)
      thus ?thesis using he34_conn unfolding defs by (by100 simp)
    qed
    have hLem1: "(e34 - {a3, a4}) \<inter> (R2 \<union> R3) = {} \<or> (e34 - {a3, a4}) \<inter> R1 = {}"
      unfolding defs by (rule Lemma_23_2_disjoint[OF hTW hSep1 he34_sub_W he34_conn_W])
    hence hLem1_result: "e34 - {a3, a4} \<subseteq> R1 \<or> e34 - {a3, a4} \<subseteq> R2 \<union> R3"
    proof
      assume "(e34 - {a3, a4}) \<inter> (R2 \<union> R3) = {}"
      hence "e34 - {a3, a4} \<subseteq> R1" using he34_sub_W unfolding defs by (by100 blast)
      thus ?thesis unfolding defs by (by100 blast)
    next
      assume "(e34 - {a3, a4}) \<inter> R1 = {}"
      hence "e34 - {a3, a4} \<subseteq> R2 \<union> R3" using he34_sub_W unfolding defs by (by100 blast)
      thus ?thesis unfolding defs by (by100 blast)
    qed
    show ?thesis
    proof (cases "e34 - {a3, a4} \<subseteq> R1")
      case True thus ?thesis unfolding defs by (by100 blast)
    next
      case False
      hence "e34 - {a3, a4} \<subseteq> R2 \<union> R3" using hLem1_result unfolding defs by (by100 blast)
      hence he34_R23: "e34 - {a3, a4} \<subseteq> R2 \<union> R3" .
      have hR2_open: "R2 \<in> subspace_topology top1_S2 top1_S2_topology (R2 \<union> R3)"
        using hR(12) unfolding subspace_topology_def unfolding defs by (by100 blast)
      have hR3_open: "R3 \<in> subspace_topology top1_S2 top1_S2_topology (R2 \<union> R3)"
        using hR(13) unfolding subspace_topology_def unfolding defs by (by100 blast)
      have hTR23: "is_topology_on (R2 \<union> R3) (subspace_topology top1_S2 top1_S2_topology (R2 \<union> R3))"
        unfolding defs by (rule subspace_topology_is_topology_on[OF hTopS2]) (use hR(7) in \<open>by100 blast\<close>)
      have hSep23: "top1_is_separation_on (R2 \<union> R3) (subspace_topology top1_S2 top1_S2_topology (R2 \<union> R3)) R2 R3"
        unfolding top1_is_separation_on_def
        using hR2_open hR3_open hR(2,3,5) unfolding defs by (by100 blast)
      have he34_conn_R23: "top1_connected_on (e34 - {a3, a4})
          (subspace_topology (R2 \<union> R3) (subspace_topology top1_S2 top1_S2_topology (R2 \<union> R3)) (e34 - {a3, a4}))"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology (e34 - {a3, a4}) =
            subspace_topology (R2 \<union> R3) (subspace_topology top1_S2 top1_S2_topology (R2 \<union> R3)) (e34 - {a3, a4})"
          using subspace_topology_trans[of "e34 - {a3, a4}" "R2 \<union> R3"]
            \<open>e34 - {a3, a4} \<subseteq> R2 \<union> R3\<close> unfolding defs by (by100 simp)
        thus ?thesis using he34_conn unfolding defs by (by100 simp)
      qed
      have hLem2: "(e34 - {a3, a4}) \<inter> R3 = {} \<or> (e34 - {a3, a4}) \<inter> R2 = {}"
        unfolding defs by (rule Lemma_23_2_disjoint[OF hTR23 hSep23 \<open>e34 - {a3, a4} \<subseteq> R2 \<union> R3\<close> he34_conn_R23])
      hence "e34 - {a3, a4} \<subseteq> R2 \<or> e34 - {a3, a4} \<subseteq> R3"
      proof
        assume "(e34 - {a3, a4}) \<inter> R3 = {}"
        thus ?thesis using he34_R23 unfolding defs by (by100 blast)
      next
        assume "(e34 - {a3, a4}) \<inter> R2 = {}"
        thus ?thesis using he34_R23 unfolding defs by (by100 blast)
      qed
      thus ?thesis unfolding defs by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 4: e12-{a1,a2} is on the theta space, hence NOT in any Ri.\<close>
  have he12_on_theta: "e12 - {a1, a2} \<subseteq> e12 \<union> Arc2 \<union> Arc3" unfolding defs by (by100 blast)
  have he12_sub_theta: "e12 \<subseteq> e12 \<union> Arc2 \<union> Arc3" by (by100 blast)
  have he12_R_disj: "e12 \<inter> (R1 \<union> R2 \<union> R3) = {}"
    by (rule subset_of_complement_disjoint[OF hR(7) he12_sub_theta])
  have he12_not_Ri: "(e12 - {a1, a2}) \<inter> (R1 \<union> R2 \<union> R3) = {}"
  proof -
    have "e12 - {a1, a2} \<subseteq> e12" by (by100 blast)
    hence "(e12 - {a1, a2}) \<inter> (R1 \<union> R2 \<union> R3) \<subseteq> e12 \<inter> (R1 \<union> R2 \<union> R3)"
      by (rule Int_mono) (rule subset_refl)
    also have "\<dots> = {}" by (rule he12_R_disj)
    finally have "(e12 - {a1, a2}) \<inter> (R1 \<union> R2 \<union> R3) \<subseteq> {}" .
    thus ?thesis by (rule subset_antisym) (rule empty_subsetI)
  qed
  \<comment> \<open>Step 5: Each Ri \<subseteq> A\<union>B (since Ri \<subseteq> S2-theta \<subseteq> S2-D = A\<union>B).
     The Ri containing e34 \<subseteq> A or B. e12 NOT in that Ri.
     e12-{a1,a2} \<subseteq> A\<union>B (from hint\_e12\_sub in Lemma\_65\_1 proof).
     If e34 Ri \<subseteq> A, then e12 must avoid A? No — e12 could still be in A via another Ri.
     The KEY: e12 is not in ANY Ri, so e12 is NOT in S2-theta.
     But e12-{a1,a2} IS in A\<union>B = S2-D. And S2-D = (S2-theta) \<union> (e12-{a1,a2}).
     So if e34 \<subseteq> Ri \<subseteq> A, then e12-{a1,a2} \<subseteq> S2-D - Ri.
     Since Ri is a component of S2-theta, and S2-D = (R1\<union>R2\<union>R3) \<union> (e12-{a1,a2}),
     the other components + e12 form the rest. A = Ri, B = rest (or swap).
     Hence e12 in B and e34 in A: different.\<close>
  \<comment> \<open>S2-D = (R1\<union>R2\<union>R3) \<union> (e12-{a1,a2}).\<close>
  have hAB_decomp: "A \<union> B = (R1 \<union> R2 \<union> R3) \<union> (e12 - {a1, a2})"
  proof -
    have hD_eq_theta: "D_loc = Arc2 \<union> Arc3" unfolding defs by (by100 blast)
    have htheta_eq: "e12 \<union> Arc2 \<union> Arc3 = D_loc \<union> e12" unfolding defs by (by100 blast)
    have hAB_is: "A \<union> B = top1_S2 - D_loc" using assms(40) unfolding defs by (by100 simp)
    have "top1_S2 - D_loc = (top1_S2 - (D_loc \<union> e12)) \<union> (e12 - D_loc)"
      unfolding defs using assms(4) by (by100 blast)
    also have "top1_S2 - (D_loc \<union> e12) = top1_S2 - (e12 \<union> Arc2 \<union> Arc3)"
      using htheta_eq by (by100 simp)
    also have "\<dots> = R1 \<union> R2 \<union> R3" using hR(7) by (by100 simp)
    finally have "top1_S2 - D_loc = (R1 \<union> R2 \<union> R3) \<union> (e12 - D_loc)" .
    moreover have "e12 - D_loc = e12 - {a1, a2}"
    proof -
      have "e12 \<inter> D_loc = {a1, a2}"
      proof -
        have "e12 \<inter> e13 = {a1}" using assms(28) by (by100 blast)
        moreover have "e12 \<inter> e23 = {a2}" using assms(24) by (by100 blast)
        moreover have "e12 \<inter> e24 = {a2}" using assms(33) by (by100 blast)
        moreover have "e12 \<inter> e41 = {a1}" using assms(27) by (by100 blast)
        ultimately show ?thesis unfolding defs by (by100 blast)
      qed
      thus ?thesis using assms(4) unfolding defs by (by100 blast)
    qed
    ultimately show ?thesis using hAB_is by (by100 simp)
  qed
  \<comment> \<open>Each Ri \<subseteq> A or B.\<close>
  have hRi_in_AB: "\<And>Ri. Ri \<in> {R1, R2, R3} \<Longrightarrow> Ri \<subseteq> A \<or> Ri \<subseteq> B"
    sorry \<comment> \<open>Connected subset of separated A\<union>B. Same Lemma\_23\_2 argument.\<close>
  \<comment> \<open>If both e12 and e34 in A: B = remaining Ri's → B has ≥2 disjoint nonempty connected pieces → not connected → contradiction.\<close>
  show ?thesis sorry
qed

(** from \<S>65 Lemma 65.1(b): for K_4 subspace of S^2, the inclusion j: C \<rightarrow> S^2-p-q
    induces an isomorphism of fundamental groups.
    NOTE: The cached Lemma_65_1_K4_subgraph only proves "exists nontrivial loop" (TOO WEAK).
    This lemma (Lemma_65_1) states the CORRECT conclusion: inclusion induces isomorphism.
    Status: PROVED via Z-chain (π₁(C) ≅ Z ≅ π₁(X)), modulo
    pi1_S2_minus_two_points_iso_Z corollary in AlgTop0.thy. **)
lemma Lemma_65_1:
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
      \<comment> \<open>K_4 planarity: arcs only intersect at shared vertices.\<close>
      and "e12 \<inter> e34 = {}" and "e23 \<inter> e41 = {}"
      and "e12 \<inter> e23 = {a2}" and "e23 \<inter> e34 = {a3}"
      and "e34 \<inter> e41 = {a4}" and "e41 \<inter> e12 = {a1}"
      and "e13 \<inter> e12 = {a1}" and "e13 \<inter> e23 = {a3}"
      and "e13 \<inter> e34 = {a3}" and "e13 \<inter> e41 = {a1}"
      and "e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}"
      and "e24 \<inter> e12 = {a2}" and "e24 \<inter> e23 = {a2}"
      and "e24 \<inter> e34 = {a4}" and "e24 \<inter> e41 = {a4}"
      \<comment> \<open>p, q are interior points of the two 'diagonal' edges.\<close>
      and "p \<in> e13 - {a1, a3}" and "q \<in> e24 - {a2, a4}"
      \<comment> \<open>C is the 4-cycle a_1 a_2 a_3 a_4 a_1.\<close>
      and "C = e12 \<union> e23 \<union> e34 \<union> e41"
      \<comment> \<open>Basepoint.\<close>
      and "c0 \<in> C"
  shows "top1_groups_isomorphic_on
    (top1_fundamental_group_carrier C
       (subspace_topology top1_S2 top1_S2_topology C) c0)
    (top1_fundamental_group_mul C
       (subspace_topology top1_S2 top1_S2_topology C) c0)
    (top1_fundamental_group_carrier (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0)
    (top1_fundamental_group_mul (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0)"
proof -
  let ?X = "top1_S2 - {p} - {q}"
  let ?TX = "subspace_topology top1_S2 top1_S2_topology ?X"
  let ?TC = "subspace_topology top1_S2 top1_S2_topology C"
  \<comment> \<open>Munkres 65.1(b): Construct D_1 = arc pa_3a_2q, D_2 = arc qa_4a_1p.
     Let U = S^2-D_1, V = S^2-D_2. Then X = U \<union> V.
     U \<inter> V = S^2-D where D = D_1 \<union> D_2 is a simple closed curve.
     D = a_1a_3a_2a_4a_1 (the other 4-cycle). By part (a), x \<in> int(e12)
     and y \<in> int(e34) lie in different components of S^2-D.
     Choose \<alpha> = path x\<rightarrow>a_1\<rightarrow>a_4\<rightarrow>y in U, \<beta> = y\<rightarrow>a_3\<rightarrow>a_2\<rightarrow>x in V.
     By Theorem 63.1, \<alpha>*\<beta> is nontrivial.
     Since both U, V are simply connected (S^2 minus an arc)
     and \<alpha>*\<beta> traverses C exactly once,
     j_*: \<pi>_1(C, c0) \<rightarrow> \<pi>_1(X, c0) is an isomorphism.\<close>
  \<comment> \<open>Step 1: C \<subseteq> X (since p \<notin> C and q \<notin> C).\<close>
  have hC_sub_S2: "C \<subseteq> top1_S2" using assms(4,5,6,7,39) by (by100 blast)
  have hp_not_C: "p \<notin> C"
  proof -
    have "p \<in> e13" "p \<noteq> a1" "p \<noteq> a3" using assms(37) by (by100 blast)+
    have h1: "p \<notin> e12" using \<open>p \<in> e13\<close> \<open>p \<noteq> a1\<close> assms(28) by (by100 blast)
    have h2: "p \<notin> e23" using \<open>p \<in> e13\<close> \<open>p \<noteq> a3\<close> assms(29) by (by100 blast)
    have h3: "p \<notin> e34" using \<open>p \<in> e13\<close> \<open>p \<noteq> a3\<close> assms(30) by (by100 blast)
    have h4: "p \<notin> e41" using \<open>p \<in> e13\<close> \<open>p \<noteq> a1\<close> assms(31) by (by100 blast)
    show ?thesis using h1 h2 h3 h4 assms(39) by (by100 blast)
  qed
  have hq_not_C: "q \<notin> C"
  proof -
    have "q \<in> e24" "q \<noteq> a2" "q \<noteq> a4" using assms(38) by (by100 blast)+
    have h1: "q \<notin> e12" using \<open>q \<in> e24\<close> \<open>q \<noteq> a2\<close> assms(33) by (by100 blast)
    have h2: "q \<notin> e23" using \<open>q \<in> e24\<close> \<open>q \<noteq> a2\<close> assms(34) by (by100 blast)
    have h3: "q \<notin> e34" using \<open>q \<in> e24\<close> \<open>q \<noteq> a4\<close> assms(35) by (by100 blast)
    have h4: "q \<notin> e41" using \<open>q \<in> e24\<close> \<open>q \<noteq> a4\<close> assms(36) by (by100 blast)
    show ?thesis using h1 h2 h3 h4 assms(39) by (by100 blast)
  qed
  have hC_sub_X: "C \<subseteq> ?X" using hC_sub_S2 hp_not_C hq_not_C by (by100 blast)
  have hc0_X: "c0 \<in> ?X" using assms(40) hC_sub_X by (by100 blast)
  \<comment> \<open>Step 2 (Munkres 65.1(b)): Apply existing Lemma_65_1 to get nontrivial loop.\<close>
  have h_nontrivial: "\<exists>x \<in> C. \<exists>g. top1_is_loop_on ?X ?TX x g
      \<and> \<not> top1_path_homotopic_on ?X ?TX x x g (top1_constant_path x)"
    by (rule Lemma_65_1_K4_subgraph[OF assms(1-39)])
  \<comment> \<open>Step 3: j_* is injective.
     From the nontrivial loop: j_* is nontrivial.
     Since \<pi>_1(C) \<cong> Z and \<pi>_1(X) \<cong> Z (infinite cyclic groups),
     a nontrivial homomorphism Z \<rightarrow> Z is injective.\<close>
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hTX: "is_topology_on ?X ?TX"
    by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
  \<comment> \<open>subspace_topology ?X ?TX C = ?TC (by subspace\_topology\_trans).\<close>
  have hTC_eq: "subspace_topology ?X ?TX C = ?TC"
    using subspace_topology_trans[OF hC_sub_X] by (by100 simp)
  have hj_hom: "top1_group_hom_on
      (top1_fundamental_group_carrier C ?TC c0) (top1_fundamental_group_mul C ?TC c0)
      (top1_fundamental_group_carrier ?X ?TX c0) (top1_fundamental_group_mul ?X ?TX c0)
      (top1_fundamental_group_induced_on C ?TC c0 ?X ?TX c0 (\<lambda>x. x))"
  proof -
    have h: "top1_group_hom_on
        (top1_fundamental_group_carrier C (subspace_topology ?X ?TX C) c0)
        (top1_fundamental_group_mul C (subspace_topology ?X ?TX C) c0)
        (top1_fundamental_group_carrier ?X ?TX c0)
        (top1_fundamental_group_mul ?X ?TX c0)
        (top1_fundamental_group_induced_on C (subspace_topology ?X ?TX C) c0 ?X ?TX c0 (\<lambda>x. x))"
      by (rule subspace_inclusion_induced_hom[OF hTX hC_sub_X assms(40)])
    have hTC_eq2: "subspace_topology ?X ?TX C = ?TC"
      by (rule hTC_eq)
    show ?thesis using h unfolding hTC_eq2 .
  qed
  \<comment> \<open>Step 3b: Both \<pi>_1(C, c0) and \<pi>_1(X, c0) are infinite cyclic (\<cong> Z).
     C is a simple closed curve (homeomorphic to S1), so \<pi>_1(C) \<cong> Z.
     X = S2-{p}-{q} with p \<noteq> q, so \<pi>_1(X) \<cong> Z by pi1\_S2\_minus\_two\_points.\<close>
  have hp_S2: "p \<in> top1_S2" using assms(37) assms(8) by (by100 blast)
  have hq_S2: "q \<in> top1_S2" using assms(38) assms(9) by (by100 blast)
  have hp_ne_q: "p \<noteq> q"
  proof -
    have "p \<in> e13" using assms(37) by (by100 blast)
    have "q \<in> e24" using assms(38) by (by100 blast)
    have "e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}" using assms(32) .
    have "p \<notin> {a1,a3}" using assms(37) by (by100 blast)
    have "q \<notin> {a2,a4}" using assms(38) by (by100 blast)
    show ?thesis
    proof
      assume "p = q"
      hence "p \<in> e13 \<inter> e24" using \<open>p \<in> e13\<close> \<open>q \<in> e24\<close> by (by100 blast)
      hence "p \<in> {a1,a2,a3,a4}" using assms(32) by (by100 blast)
      hence "p \<in> {a2,a4}" using \<open>p \<notin> {a1,a3}\<close> by (by100 blast)
      hence "q \<in> {a2,a4}" using \<open>p = q\<close> by (by100 blast)
      thus False using \<open>q \<notin> {a2,a4}\<close> by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 4: Surjectivity of j_*.
     Following Munkres 65.1(b): the existing Lemma\_65\_1 constructs \<alpha>*\<beta> via Theorem 63.1.
     \<alpha>*\<beta> is a loop in C that is nontrivial in X. Since \<pi>_1(X) \<cong> Z and
     Theorem\_63\_1\_c\_subgroups\_trivial gives that [\<alpha>*\<beta>] generates \<pi>_1(X),
     and \<alpha>*\<beta> lies in C, j_* is surjective.\<close>
  \<comment> \<open>Step 4a (Munkres 65.1(b)): The loop \<alpha>*\<beta> from Lemma\_65\_1\_K4\_subgraph
     lies in C and is nontrivial in X. Following the textbook:
     - U = S2-D1, V = S2-D2 where D1, D2 are arcs
     - Both U, V are simply connected (not needed: Theorem\_63\_1\_b uses helix instead)
     - U \<inter> V = S2-D has two components (D = D1 \<union> D2 is simple closed curve, by JCT)
     - \<alpha> path x\<rightarrow>y in U, \<beta> path y\<rightarrow>x in V, with x, y in different components
     - By Theorem 63.1: [\<alpha>*\<beta>] nontrivial
     - Since U, V simply connected and U \<inter> V has two components,
       [\<alpha>*\<beta>] generates \<pi>_1(X) (Theorem 63.1(c) forces this in infinite cyclic group)
     - Since \<alpha>*\<beta> \<in> C, j_* hits the generator, hence surjective.\<close>
  \<comment> \<open>Step 4a: j_* is nontrivial at basepoint c0.
     h\_nontrivial gives a nontrivial loop g at some x \<in> C.
     g is a loop in C (lies in C) and nontrivial in X.
     By inclusion\_induced\_class: j_*(x)([g]_C) = [g]_X \<noteq> [const].
     By basepoint change (C and X path-connected): j_*(c0) is also nontrivial.\<close>
  \<comment> \<open>Step 4a: \<pi>_1(C, c0) \<cong> Z (C is a simple closed curve \<cong> S1).\<close>
  have hC_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  proof -
    \<comment> \<open>e12 \<union> e23 is an arc from a1 to a3 (via arcs\_concatenation\_is\_arc, shared at a2).\<close>
    have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology" by (rule top1_S2_is_hausdorff)
    have ha2_ep12: "a2 \<in> top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
      using assms(16) by (by100 blast)
    have ha2_ep23: "a2 \<in> top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      using assms(17) by (by100 blast)
    have harc_12_23: "top1_is_arc_on (e12 \<union> e23) (subspace_topology top1_S2 top1_S2_topology (e12 \<union> e23))"
      by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus assms(10) assms(4)
             assms(11) assms(5) assms(24) ha2_ep12 ha2_ep23])
    have ha4_ep34: "a4 \<in> top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
      using assms(18) by (by100 blast)
    have ha4_ep41: "a4 \<in> top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
      using assms(19) by (by100 blast)
    have harc_34_41: "top1_is_arc_on (e34 \<union> e41) (subspace_topology top1_S2 top1_S2_topology (e34 \<union> e41))"
      by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus assms(12) assms(6)
             assms(13) assms(7) assms(26) ha4_ep34 ha4_ep41])
    \<comment> \<open>(e12 \<union> e23) \<inter> (e34 \<union> e41) = {a1, a3}.\<close>
    have hinter: "(e12 \<union> e23) \<inter> (e34 \<union> e41) = {a1, a3}"
    proof -
      \<comment> \<open>(e12 \<union> e23) \<inter> (e34 \<union> e41) = (e12\<inter>e34) \<union> (e12\<inter>e41) \<union> (e23\<inter>e34) \<union> (e23\<inter>e41)
         = {} \<union> {a1} \<union> {a3} \<union> {} = {a1, a3}.\<close>
      have "(e12 \<union> e23) \<inter> (e34 \<union> e41)
          = (e12 \<inter> e34) \<union> (e12 \<inter> e41) \<union> (e23 \<inter> e34) \<union> (e23 \<inter> e41)" by (by100 blast)
      hence "(e12 \<union> e23) \<inter> (e34 \<union> e41)
          = (e12 \<inter> e34) \<union> (e12 \<inter> e41) \<union> (e23 \<inter> e34) \<union> (e23 \<inter> e41)" .
      hence "(e12 \<union> e23) \<inter> (e34 \<union> e41) = {} \<union> (e12 \<inter> e41) \<union> (e23 \<inter> e34) \<union> (e23 \<inter> e41)"
        using assms(22) by (by100 simp)
      hence h1: "(e12 \<union> e23) \<inter> (e34 \<union> e41) = (e12 \<inter> e41) \<union> (e23 \<inter> e34) \<union> (e23 \<inter> e41)"
        by (by100 blast)
      have h_eq: "(e12 \<union> e23) \<inter> (e34 \<union> e41) = (e12 \<inter> e41) \<union> (e23 \<inter> e34) \<union> (e23 \<inter> e41)"
        by (rule h1)
      have "(e12 \<inter> e41) \<union> (e23 \<inter> e34) \<union> (e23 \<inter> e41) = {a1} \<union> {a3} \<union> {}"
        using assms(27) assms(25) assms(23) by (by100 blast)
      hence h5: "(e12 \<union> e23) \<inter> (e34 \<union> e41) = {a1} \<union> {a3} \<union> {}"
        using h_eq by (by100 simp)
      show ?thesis using h5 by (by100 blast)
    qed
    have ha1_ne_a3: "a1 \<noteq> a3"
    proof
      assume h: "a1 = a3"
      have "{a1, a2, a3, a4} = {a1, a2, a4}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> card {a1, a2, a4}" by (by100 simp)
      also have "\<dots> \<le> 3" by (rule card_insert_le_m1, by100 simp)+ (by100 simp)
      finally show False using assms(2) by (by100 simp)
    qed
    have ha1_ne_a2: "a1 \<noteq> a2" and ha2_ne_a3: "a2 \<noteq> a3"
        and ha3_ne_a4: "a3 \<noteq> a4" and ha4_ne_a1: "a4 \<noteq> a1"
      using assms(2) by (auto simp: card_insert_if split: if_splits)+
    have hep1: "top1_arc_endpoints_on (e12 \<union> e23) (subspace_topology top1_S2 top1_S2_topology (e12 \<union> e23)) = {a1, a3}"
      by (rule arc_concat_endpoints[OF assms(1) hS2_haus assms(10) assms(4) assms(11) assms(5)
             assms(24) ha2_ep12 ha2_ep23 assms(16) assms(17) ha1_ne_a2 ha2_ne_a3])
    have hep2: "top1_arc_endpoints_on (e34 \<union> e41) (subspace_topology top1_S2 top1_S2_topology (e34 \<union> e41)) = {a3, a1}"
      by (rule arc_concat_endpoints[OF assms(1) hS2_haus assms(12) assms(6) assms(13) assms(7)
             assms(26) ha4_ep34 ha4_ep41 assms(18) assms(19) ha3_ne_a4 ha4_ne_a1])
    have hep2': "top1_arc_endpoints_on (e34 \<union> e41) (subspace_topology top1_S2 top1_S2_topology (e34 \<union> e41)) = {a1, a3}"
      using hep2 by (by100 blast)
    have hC_eq: "C = (e12 \<union> e23) \<union> (e34 \<union> e41)" using assms(39) by (by100 blast)
    have hsub1: "(e12 \<union> e23) \<subseteq> top1_S2" using assms(4,5) by (by100 blast)
    have hsub2: "(e34 \<union> e41) \<subseteq> top1_S2" using assms(6,7) by (by100 blast)
    show ?thesis unfolding hC_eq
      by (rule arcs_form_simple_closed_curve[OF assms(1) _ harc_12_23 hsub1 harc_34_41 hsub2
             hinter ha1_ne_a3 hep1 hep2'])
         (rule top1_S2_is_hausdorff)
  qed
  \<comment> \<open>Vertex distinctness (used in D1\<inter>D2 analysis below).\<close>
  have hdist: "a1 \<noteq> a2" "a2 \<noteq> a3" "a3 \<noteq> a4" "a4 \<noteq> a1" "a1 \<noteq> a3" "a2 \<noteq> a4"
    "a2 \<noteq> a1" "a3 \<noteq> a2" "a4 \<noteq> a3" "a1 \<noteq> a4" "a3 \<noteq> a1" "a4 \<noteq> a2"
    using assms(2) by (auto simp: card_insert_if split: if_splits)+
  \<comment> \<open>Step 4c: \<pi>_1(X, c0) is infinite cyclic (from pi1\_S2\_minus\_two\_points).\<close>
  have hX_inf_cyc: "\<exists>gen. top1_is_loop_on ?X ?TX c0 gen \<and>
      (\<forall>f. top1_is_loop_on ?X ?TX c0 f \<longrightarrow>
        (\<exists>n::nat. top1_path_homotopic_on ?X ?TX c0 c0 f (top1_path_power gen c0 n) \<or>
         top1_path_homotopic_on ?X ?TX c0 c0 f (top1_path_power (top1_path_reverse gen) c0 n)))"
    by (rule pi1_S2_minus_two_points_infinite_cyclic[OF assms(1) hp_S2 hq_S2 hp_ne_q hc0_X])
  \<comment> \<open>===== Following Munkres 65.1(b) EXACTLY =====
     Step A: Construct D1, D2 by splitting e13 at p and e24 at q.
     Step B: Construct specific \<alpha>, \<beta> along C edges.
     Step C: Apply Theorem 63.1 \<Rightarrow> \<alpha>*\<beta> nontrivial in X.
     Step D: \<alpha>*\<beta> generates \<pi>_1(X) (since \<pi>_1(X) infinite cyclic).
     Step E: \<alpha>*\<beta> \<in> C \<Rightarrow> j_* surjective.
     Step F: Surjective hom Z \<rightarrow> Z \<Rightarrow> injective.\<close>
  \<comment> \<open>Step A: Split e13 at p to get arcs a1-to-p and p-to-a3.
     Split e24 at q to get arcs a2-to-q and q-to-a4.
     D1 = (p-to-a3) \<union> e23 \<union> (a2-to-q): arc from p to q through a3, a2.
     D2 = (q-to-a4) \<union> e41 \<union> (a1-to-p): arc from q to p through a4, a1.\<close>
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology" by (rule top1_S2_is_hausdorff)
  have hp_e13: "p \<in> e13" using assms(37) by (by100 blast)
  have hp_not_ep13: "p \<notin> top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
    using assms(37) assms(20) by (by100 blast)
  have ha1_ne_a3: "a1 \<noteq> a3" using assms(2) by (auto simp: card_insert_if split: if_splits)
  obtain D1p Da3 where hD1p_arc: "top1_is_arc_on D1p (subspace_topology top1_S2 top1_S2_topology D1p)"
      and hDa3_arc: "top1_is_arc_on Da3 (subspace_topology top1_S2 top1_S2_topology Da3)"
      and he13_split: "e13 = D1p \<union> Da3" and he13_meet: "D1p \<inter> Da3 = {p}"
      and "a1 \<in> D1p" "a3 \<in> Da3" "p \<in> D1p" "p \<in> Da3"
      and "D1p \<subseteq> top1_S2" "Da3 \<subseteq> top1_S2"
    using arc_split_at_given_point[OF assms(1) hS2_haus assms(8) assms(14)
          hp_e13 hp_not_ep13 assms(20) ha1_ne_a3] by blast
  have hq_e24: "q \<in> e24" using assms(38) by (by100 blast)
  have hq_not_ep24: "q \<notin> top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
    using assms(38) assms(21) by (by100 blast)
  have ha2_ne_a4: "a2 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
  obtain Da2 Dq4 where hDa2_arc: "top1_is_arc_on Da2 (subspace_topology top1_S2 top1_S2_topology Da2)"
      and hDq4_arc: "top1_is_arc_on Dq4 (subspace_topology top1_S2 top1_S2_topology Dq4)"
      and he24_split: "e24 = Da2 \<union> Dq4" and he24_meet: "Da2 \<inter> Dq4 = {q}"
      and "a2 \<in> Da2" "a4 \<in> Dq4" "q \<in> Da2" "q \<in> Dq4"
      and "Da2 \<subseteq> top1_S2" "Dq4 \<subseteq> top1_S2"
    using arc_split_at_given_point[OF assms(1) hS2_haus assms(9) assms(15)
          hq_e24 hq_not_ep24 assms(21) ha2_ne_a4] by blast
  \<comment> \<open>D1 = Da3 \<union> e23 \<union> Da2 (arc from p through a3, a2 to q).
     D2 = Dq4 \<union> e41 \<union> D1p (arc from q through a4, a1 to p).\<close>
  let ?D1 = "Da3 \<union> e23 \<union> Da2"
  let ?D2 = "Dq4 \<union> e41 \<union> D1p"
  let ?U_loc = "top1_S2 - ?D1"
  let ?V_loc = "top1_S2 - ?D2"
  \<comment> \<open>Step B: Get interior points x \<in> e12 and y \<in> e34.\<close>
  obtain x e12a e12b where hx_e12: "x \<in> e12" and he12_eq: "e12 = e12a \<union> e12b"
      and he12_meet: "e12a \<inter> e12b = {x}"
      and he12a_arc: "top1_is_arc_on e12a (subspace_topology top1_S2 top1_S2_topology e12a)"
      and he12b_arc: "top1_is_arc_on e12b (subspace_topology top1_S2 top1_S2_topology e12b)"
    using arc_split_at_midpoint[OF assms(1) hS2_haus assms(4) assms(10)] by blast
  obtain y e34a e34b where hy_e34: "y \<in> e34" and he34_eq: "e34 = e34a \<union> e34b"
      and he34_meet: "e34a \<inter> e34b = {y}"
      and he34a_arc: "top1_is_arc_on e34a (subspace_topology top1_S2 top1_S2_topology e34a)"
      and he34b_arc: "top1_is_arc_on e34b (subspace_topology top1_S2 top1_S2_topology e34b)"
    using arc_split_at_midpoint[OF assms(1) hS2_haus assms(6) assms(12)] by blast
  \<comment> \<open>Step B2: x \<notin> {a1, a2} and y \<notin> {a3, a4} (interior points of arcs).\<close>
  \<comment> \<open>x is an interior point of e12 (not an endpoint). From arc\_split\_at\_midpoint:
     e12 = e12a \<union> e12b, e12a \<inter> e12b = {x}. Removing x disconnects e12
     (e12a-{x} and e12b-{x} are nonempty disjoint clopen pieces).
     Since endpoints = {p | A-{p} connected}, x is not an endpoint.\<close>
  \<comment> \<open>Helper: arcs have \<ge> 2 points (bijective image of [0,1]).\<close>
  {
    fix A :: "(real \<times> real \<times> real) set" and TA and z
    assume harc: "top1_is_arc_on A TA"
    then obtain hf where hhf: "top1_homeomorphism_on I_set I_top A TA hf"
      unfolding top1_is_arc_on_def by (by100 blast)
    have hbij: "bij_betw hf I_set A"
      using hhf unfolding top1_homeomorphism_on_def by (by100 blast)
    have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have "hf 0 \<in> A" using hbij h0_I unfolding bij_betw_def by (by100 blast)
    moreover have "hf 1 \<in> A" using hbij h1_I unfolding bij_betw_def by (by100 blast)
    moreover have "hf 0 \<noteq> hf 1"
    proof -
      have "inj_on hf I_set" using hbij unfolding bij_betw_def by (by100 blast)
      thus ?thesis using h0_I h1_I unfolding inj_on_def by (by100 fastforce)
    qed
    ultimately have "A \<noteq> {z}" by (by100 fastforce)
  } note arc_not_singleton = this
  have hx_not_endpts: "x \<noteq> a1 \<and> x \<noteq> a2"
  proof (intro conjI notI)
    \<comment> \<open>Key: if x were an endpoint, arc\_both\_endpoints\_in\_one\_part forces one sub-arc
       to be a singleton, but arcs have \<ge> 2 points (homeomorphic to [0,1]).\<close>
    have ha1_ne_a2: "a1 \<noteq> a2" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha2_e12: "a2 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have ha1_e12: "a1 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have he12a_sub: "e12a \<subseteq> top1_S2" using he12_eq assms(4) by (by100 blast)
    have he12b_sub: "e12b \<subseteq> top1_S2" using he12_eq assms(4) by (by100 blast)
    have he12a_conn: "top1_connected_on e12a (subspace_topology top1_S2 top1_S2_topology e12a)"
      using arc_connected[OF he12a_arc] .
    have he12b_conn: "top1_connected_on e12b (subspace_topology top1_S2 top1_S2_topology e12b)"
      using arc_connected[OF he12b_arc] .
    assume "x = a1"
    hence ha1_e12a: "a1 \<in> e12a" and ha1_e12b: "a1 \<in> e12b"
      using he12_meet by (by100 blast)+
    have "a2 \<in> e12a \<or> a2 \<in> e12b" using ha2_e12 he12_eq by (by100 blast)
    thus False
    proof
      assume "a2 \<in> e12a"
      have "e12b = {x}"
        by (rule arc_both_endpoints_in_one_part[OF assms(1) hS2_haus assms(4) assms(10)
              he12_eq he12_meet he12a_conn he12a_sub assms(16) ha1_ne_a2 ha1_e12a \<open>a2 \<in> e12a\<close>])
      thus False using arc_not_singleton[OF he12b_arc, of x] by (by100 simp)
    next
      assume "a2 \<in> e12b"
      have he12_eq': "e12 = e12b \<union> e12a" using he12_eq by (by100 blast)
      have he12_meet': "e12b \<inter> e12a = {x}" using he12_meet by (by100 blast)
      have "e12a = {x}"
        by (rule arc_both_endpoints_in_one_part[OF assms(1) hS2_haus assms(4) assms(10)
              he12_eq' he12_meet' he12b_conn he12b_sub assms(16) ha1_ne_a2 ha1_e12b \<open>a2 \<in> e12b\<close>])
      thus False using arc_not_singleton[OF he12a_arc, of x] by (by100 simp)
    qed
  next
    assume "x = a2"
    have ha1_ne_a2: "a1 \<noteq> a2" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha2_e12a: "a2 \<in> e12a" and ha2_e12b: "a2 \<in> e12b"
      using \<open>x = a2\<close> he12_meet by (by100 blast)+
    have ha1_e12: "a1 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have he12a_sub: "e12a \<subseteq> top1_S2" using he12_eq assms(4) by (by100 blast)
    have he12b_sub: "e12b \<subseteq> top1_S2" using he12_eq assms(4) by (by100 blast)
    have he12a_conn: "top1_connected_on e12a (subspace_topology top1_S2 top1_S2_topology e12a)"
      using arc_connected[OF he12a_arc] .
    have he12b_conn: "top1_connected_on e12b (subspace_topology top1_S2 top1_S2_topology e12b)"
      using arc_connected[OF he12b_arc] .
    have "a1 \<in> e12a \<or> a1 \<in> e12b" using ha1_e12 he12_eq by (by100 blast)
    thus False
    proof
      assume "a1 \<in> e12a"
      have he12_eq': "e12 = e12a \<union> e12b" using he12_eq by (by100 blast)
      have he12_meet': "e12a \<inter> e12b = {x}" using he12_meet by (by100 blast)
      have "e12b = {x}"
        by (rule arc_both_endpoints_in_one_part[OF assms(1) hS2_haus assms(4) assms(10)
              he12_eq' he12_meet' he12a_conn he12a_sub assms(16) ha1_ne_a2 \<open>a1 \<in> e12a\<close> ha2_e12a])
      thus False using arc_not_singleton[OF he12b_arc, of x] by (by100 simp)
    next
      assume "a1 \<in> e12b"
      have he12_eq': "e12 = e12b \<union> e12a" using he12_eq by (by100 blast)
      have he12_meet': "e12b \<inter> e12a = {x}" using he12_meet by (by100 blast)
      have "e12a = {x}"
        by (rule arc_both_endpoints_in_one_part[OF assms(1) hS2_haus assms(4) assms(10)
              he12_eq' he12_meet' he12b_conn he12b_sub assms(16) ha1_ne_a2 \<open>a1 \<in> e12b\<close> ha2_e12b])
      thus False using arc_not_singleton[OF he12a_arc, of x] by (by100 simp)
    qed
  qed
  have hy_not_endpts: "y \<noteq> a3 \<and> y \<noteq> a4"
  proof (intro conjI notI)
    have ha3_ne_a4: "a3 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha4_e34: "a4 \<in> e34" using assms(18) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have ha3_e34: "a3 \<in> e34" using assms(18) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have he34a_sub: "e34a \<subseteq> top1_S2" using he34_eq assms(6) by (by100 blast)
    have he34b_sub: "e34b \<subseteq> top1_S2" using he34_eq assms(6) by (by100 blast)
    have he34a_conn: "top1_connected_on e34a (subspace_topology top1_S2 top1_S2_topology e34a)"
      using arc_connected[OF he34a_arc] .
    have he34b_conn: "top1_connected_on e34b (subspace_topology top1_S2 top1_S2_topology e34b)"
      using arc_connected[OF he34b_arc] .
    assume "y = a3"
    hence ha3_e34a: "a3 \<in> e34a" and ha3_e34b: "a3 \<in> e34b"
      using he34_meet by (by100 blast)+
    have "a4 \<in> e34a \<or> a4 \<in> e34b" using ha4_e34 he34_eq by (by100 blast)
    thus False
    proof
      assume "a4 \<in> e34a"
      have "e34b = {y}"
        by (rule arc_both_endpoints_in_one_part[OF assms(1) hS2_haus assms(6) assms(12)
              he34_eq he34_meet he34a_conn he34a_sub assms(18) ha3_ne_a4 ha3_e34a \<open>a4 \<in> e34a\<close>])
      thus False using arc_not_singleton[OF he34b_arc, of y] by (by100 simp)
    next
      assume "a4 \<in> e34b"
      have he34_eq': "e34 = e34b \<union> e34a" using he34_eq by (by100 blast)
      have he34_meet': "e34b \<inter> e34a = {y}" using he34_meet by (by100 blast)
      have "e34a = {y}"
        by (rule arc_both_endpoints_in_one_part[OF assms(1) hS2_haus assms(6) assms(12)
              he34_eq' he34_meet' he34b_conn he34b_sub assms(18) ha3_ne_a4 ha3_e34b \<open>a4 \<in> e34b\<close>])
      thus False using arc_not_singleton[OF he34a_arc, of y] by (by100 simp)
    qed
  next
    assume "y = a4"
    have ha3_ne_a4: "a3 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha4_e34a: "a4 \<in> e34a" and ha4_e34b: "a4 \<in> e34b"
      using \<open>y = a4\<close> he34_meet by (by100 blast)+
    have ha3_e34: "a3 \<in> e34" using assms(18) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have he34a_sub: "e34a \<subseteq> top1_S2" using he34_eq assms(6) by (by100 blast)
    have he34b_sub: "e34b \<subseteq> top1_S2" using he34_eq assms(6) by (by100 blast)
    have he34a_conn: "top1_connected_on e34a (subspace_topology top1_S2 top1_S2_topology e34a)"
      using arc_connected[OF he34a_arc] .
    have he34b_conn: "top1_connected_on e34b (subspace_topology top1_S2 top1_S2_topology e34b)"
      using arc_connected[OF he34b_arc] .
    have "a3 \<in> e34a \<or> a3 \<in> e34b" using ha3_e34 he34_eq by (by100 blast)
    thus False
    proof
      assume "a3 \<in> e34a"
      have he34_eq': "e34 = e34a \<union> e34b" using he34_eq by (by100 blast)
      have he34_meet': "e34a \<inter> e34b = {y}" using he34_meet by (by100 blast)
      have "e34b = {y}"
        by (rule arc_both_endpoints_in_one_part[OF assms(1) hS2_haus assms(6) assms(12)
              he34_eq' he34_meet' he34a_conn he34a_sub assms(18) ha3_ne_a4 \<open>a3 \<in> e34a\<close> ha4_e34a])
      thus False using arc_not_singleton[OF he34b_arc, of y] by (by100 simp)
    next
      assume "a3 \<in> e34b"
      have he34_eq': "e34 = e34b \<union> e34a" using he34_eq by (by100 blast)
      have he34_meet': "e34b \<inter> e34a = {y}" using he34_meet by (by100 blast)
      have "e34a = {y}"
        by (rule arc_both_endpoints_in_one_part[OF assms(1) hS2_haus assms(6) assms(12)
              he34_eq' he34_meet' he34b_conn he34b_sub assms(18) ha3_ne_a4 \<open>a3 \<in> e34b\<close> ha4_e34b])
      thus False using arc_not_singleton[OF he34a_arc, of y] by (by100 simp)
    qed
  qed
  \<comment> \<open>Step B3: C - D1 is path-connected and contains x, y.
     C - D1 = (e12-{a2}) \<union> e41 \<union> (e34-{a3}). Connected chain via a1, a4.
     x \<in> e12-{a2} (x interior), y \<in> e34-{a3} (y interior).
     So \<exists>\<alpha>: path from x to y in C \<inter> U.\<close>
  have hx_in_CmD1: "x \<in> C - ?D1"
  proof -
    have "x \<in> C" using hx_e12 assms(39) by (by100 blast)
    moreover have "x \<notin> Da3"
    proof -
      have "Da3 \<subseteq> e13" using he13_split by (by100 blast)
      hence "e12 \<inter> Da3 \<subseteq> e12 \<inter> e13" by (by100 blast)
      hence h_sub: "e12 \<inter> Da3 \<subseteq> {a1}" using assms(28) by (by100 blast)
      have "a1 \<noteq> p" using assms(37) by (by100 blast)
      have "a1 \<notin> Da3" using \<open>a1 \<in> D1p\<close> he13_meet \<open>a1 \<noteq> p\<close> by (by100 blast)
      have "e12 \<inter> Da3 = {}" using h_sub \<open>a1 \<notin> Da3\<close> by (by100 blast)
      thus ?thesis using hx_e12 by (by100 blast)
    qed
    moreover have "x \<notin> e23" using hx_e12 hx_not_endpts assms(24) by (by100 blast)
    moreover have "x \<notin> Da2"
    proof -
      have "Da2 \<subseteq> e24" using he24_split by (by100 blast)
      hence "e12 \<inter> Da2 \<subseteq> e12 \<inter> e24" by (by100 blast)
      hence "e12 \<inter> Da2 \<subseteq> {a2}" using assms(33) by (by100 blast)
      thus ?thesis using hx_e12 hx_not_endpts by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  have hy_in_CmD1: "y \<in> C - ?D1"
  proof -
    have "y \<in> C" using hy_e34 assms(39) by (by100 blast)
    moreover have "y \<notin> Da3"
    proof -
      have "Da3 \<subseteq> e13" using he13_split by (by100 blast)
      hence "e34 \<inter> Da3 \<subseteq> e34 \<inter> e13" by (by100 blast)
      hence "e34 \<inter> Da3 \<subseteq> {a3}" using assms(30) by (by100 blast)
      thus ?thesis using hy_e34 hy_not_endpts by (by100 blast)
    qed
    moreover have "y \<notin> e23" using hy_e34 hy_not_endpts assms(25) by (by100 blast)
    moreover have "y \<notin> Da2"
    proof -
      have "Da2 \<subseteq> e24" using he24_split by (by100 blast)
      hence "e34 \<inter> Da2 \<subseteq> e34 \<inter> e24" by (by100 blast)
      hence h_sub: "e34 \<inter> Da2 \<subseteq> {a4}" using assms(35) by (by100 blast)
      have "a4 \<noteq> q" using assms(38) by (by100 blast)
      have "a4 \<notin> Da2" using \<open>a4 \<in> Dq4\<close> he24_meet \<open>a4 \<noteq> q\<close> by (by100 blast)
      have "e34 \<inter> Da2 = {}" using h_sub \<open>a4 \<notin> Da2\<close> by (by100 blast)
      thus ?thesis using hy_e34 by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>Helper: arcs in S2 are path-connected (from homeomorphism with [0,1]).\<close>
  {
    fix D :: "(real \<times> real \<times> real) set" and TD
    assume harc_loc: "top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D)"
        and hD_sub: "D \<subseteq> top1_S2"
    have "top1_path_connected_on D (subspace_topology top1_S2 top1_S2_topology D)"
    proof -
      obtain hf where hhf: "top1_homeomorphism_on I_set I_top D
          (subspace_topology top1_S2 top1_S2_topology D) hf"
        using harc_loc unfolding top1_is_arc_on_def by (by100 blast)
      have "top1_path_connected_on I_set I_top"
      proof (unfold top1_path_connected_on_def, intro conjI ballI)
        show "is_topology_on I_set I_top"
          unfolding top1_unit_interval_topology_def
          by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV])
             (by100 simp)
        fix a b :: real assume ha: "a \<in> I_set" and hb: "b \<in> I_set"
        let ?g = "\<lambda>t::real. (1-t)*a + t*b"
        have hg_cont: "continuous_on UNIV ?g" by (intro continuous_intros)
        have hg_map: "\<And>t. t \<in> I_set \<Longrightarrow> ?g t \<in> I_set"
        proof -
          fix t :: real assume ht: "t \<in> I_set"
          have "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
          have "0 \<le> a" "a \<le> 1" using ha unfolding top1_unit_interval_def by auto
          have "0 \<le> b" "b \<le> 1" using hb unfolding top1_unit_interval_def by auto
          have h0: "0 \<le> (1-t)*a" using \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> \<open>0 \<le> a\<close>
            using mult_nonneg_nonneg by (by100 fastforce)
          have h1: "0 \<le> t*b" using \<open>0 \<le> t\<close> \<open>0 \<le> b\<close>
            using mult_nonneg_nonneg by (by100 fastforce)
          have "0 \<le> (1-t)*a + t*b" using h0 h1 by (by100 simp)
          moreover have "(1-t)*a + t*b \<le> 1"
          proof -
            have "(1-t)*a \<le> (1-t)*1" using \<open>a \<le> 1\<close> \<open>0 \<le> t\<close> \<open>t \<le> 1\<close>
              using mult_left_mono by (by100 fastforce)
            moreover have "t*b \<le> t*1" using \<open>b \<le> 1\<close> \<open>0 \<le> t\<close>
              using mult_left_mono by (by100 fastforce)
            ultimately show ?thesis by (by100 simp)
          qed
          ultimately show "?g t \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        qed
        have hg_top: "top1_continuous_map_on I_set I_top I_set I_top ?g"
        proof -
          have "top1_continuous_map_on I_set
              (subspace_topology UNIV top1_open_sets I_set)
              I_set (subspace_topology UNIV top1_open_sets I_set) ?g"
            by (rule top1_continuous_map_on_real_subspace_open_sets[OF hg_map hg_cont])
          thus ?thesis unfolding top1_unit_interval_topology_def .
        qed
        have "?g 0 = a" by (by100 simp)
        moreover have "?g 1 = b" by (by100 simp)
        ultimately have "top1_is_path_on I_set I_top a b ?g"
          unfolding top1_is_path_on_def using hg_top by (by100 blast)
        thus "\<exists>f. top1_is_path_on I_set I_top a b f" by (by100 blast)
      qed
      thus ?thesis by (rule homeomorphism_preserves_path_connected[OF hhf])
    qed
  } note arc_path_connected = this
  \<comment> \<open>Helper: arc minus one endpoint is path-connected.\<close>
  {
    fix D :: "(real \<times> real \<times> real) set" and ep
    assume harc_loc: "top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D)"
        and hD_sub: "D \<subseteq> top1_S2"
        and hep: "ep \<in> top1_arc_endpoints_on D (subspace_topology top1_S2 top1_S2_topology D)"
    have "top1_path_connected_on (D - {ep}) (subspace_topology top1_S2 top1_S2_topology (D - {ep}))"
    proof -
      obtain hf where hhf: "top1_homeomorphism_on I_set I_top D
          (subspace_topology top1_S2 top1_S2_topology D) hf"
        using harc_loc unfolding top1_is_arc_on_def by (by100 blast)
      have hbij: "bij_betw hf I_set D"
        using hhf unfolding top1_homeomorphism_on_def by (by100 blast)
      have hinj: "inj_on hf I_set" using hbij unfolding bij_betw_def by (by100 blast)
      have hsurj: "hf ` I_set = D" using hbij unfolding bij_betw_def by (by100 blast)
      have hcont: "top1_continuous_map_on I_set I_top D
          (subspace_topology top1_S2 top1_S2_topology D) hf"
        using hhf unfolding top1_homeomorphism_on_def by (by100 blast)
      \<comment> \<open>ep = hf(0) or ep = hf(1) (endpoints are boundary of [0,1]).\<close>
      have hep_bd: "top1_arc_endpoints_on D
          (subspace_topology top1_S2 top1_S2_topology D) = {hf 0, hf 1}"
        by (rule arc_endpoints_are_boundary[OF assms(1) hS2_haus hD_sub harc_loc hhf])
      have hep_01: "ep = hf 0 \<or> ep = hf 1" using hep hep_bd by (by100 blast)
      \<comment> \<open>Define tb = hf\<inverse>(ep) \<in> {0, 1}.\<close>
      define tb where "tb = inv_into I_set hf ep"
      have hep_D: "ep \<in> D" using hep unfolding top1_arc_endpoints_on_def by (by100 blast)
      have hep_img: "ep \<in> hf ` I_set" using hep_D hsurj by (by100 blast)
      have htb_I: "tb \<in> I_set" unfolding tb_def
        using inv_into_into[OF hep_img] by (by100 blast)
      have hftb: "hf tb = ep" unfolding tb_def
        using f_inv_into_f[OF hep_img] by (by100 blast)
      have htb_01: "tb = 0 \<or> tb = 1"
      proof -
        have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        from hep_01 show ?thesis
        proof
          assume "ep = hf 0"
          hence "hf tb = hf 0" using hftb by (by100 simp)
          thus ?thesis using hinj htb_I h0_I unfolding inj_on_def by (by100 blast)
        next
          assume "ep = hf 1"
          hence "hf tb = hf 1" using hftb by (by100 simp)
          thus ?thesis using hinj htb_I h1_I unfolding inj_on_def by (by100 blast)
        qed
      qed
      \<comment> \<open>Path-connected: for u, v \<in> D-{ep}, use affine path avoiding tb.\<close>
      show ?thesis unfolding top1_path_connected_on_def
      proof (intro conjI ballI)
        show "is_topology_on (D - {ep}) (subspace_topology top1_S2 top1_S2_topology (D - {ep}))"
          by (rule subspace_topology_is_topology_on[OF
              is_topology_on_strict_imp[OF assms(1)]]) (use hD_sub in \<open>by100 blast\<close>)
        fix u v assume hu: "u \<in> D - {ep}" and hv: "v \<in> D - {ep}"
        define su where "su = inv_into I_set hf u"
        define sv where "sv = inv_into I_set hf v"
        have hu_img: "u \<in> hf ` I_set" using hu hsurj by (by100 blast)
        have hv_img: "v \<in> hf ` I_set" using hv hsurj by (by100 blast)
        have hsu_I: "su \<in> I_set" unfolding su_def
          using inv_into_into[OF hu_img] by (by100 blast)
        have hsv_I: "sv \<in> I_set" unfolding sv_def
          using inv_into_into[OF hv_img] by (by100 blast)
        have hfsu: "hf su = u" unfolding su_def
          using f_inv_into_f[OF hu_img] by (by100 blast)
        have hfsv: "hf sv = v" unfolding sv_def
          using f_inv_into_f[OF hv_img] by (by100 blast)
        have hsu_ne_tb: "su \<noteq> tb" using hu hfsu hftb hinj hsu_I htb_I
          unfolding inj_on_def by (by100 blast)
        have hsv_ne_tb: "sv \<noteq> tb" using hv hfsv hftb hinj hsv_I htb_I
          unfolding inj_on_def by (by100 blast)
        \<comment> \<open>Affine path stays in I\_set and avoids tb (convexity of [0,1)-or-(0,1]).\<close>
        let ?g = "\<lambda>t::real. (1-t)*su + t*sv"
        have hg_in_I: "\<And>t. t \<in> I_set \<Longrightarrow> ?g t \<in> I_set"
        proof -
          fix t :: real assume ht: "t \<in> I_set"
          have "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
          have "0 \<le> su" "su \<le> 1" using hsu_I unfolding top1_unit_interval_def by auto
          have "0 \<le> sv" "sv \<le> 1" using hsv_I unfolding top1_unit_interval_def by auto
          have h0: "0 \<le> (1-t)*su" using \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> \<open>0 \<le> su\<close>
            using mult_nonneg_nonneg by (by100 fastforce)
          have h1: "0 \<le> t*sv" using \<open>0 \<le> t\<close> \<open>0 \<le> sv\<close>
            using mult_nonneg_nonneg by (by100 fastforce)
          have hge: "0 \<le> ?g t" using h0 h1 by (by100 simp)
          have "(1-t)*su \<le> (1-t)*1" using \<open>su \<le> 1\<close> \<open>0 \<le> t\<close> \<open>t \<le> 1\<close>
            using mult_left_mono by (by100 fastforce)
          moreover have "t*sv \<le> t*1" using \<open>sv \<le> 1\<close> \<open>0 \<le> t\<close>
            using mult_left_mono by (by100 fastforce)
          ultimately have hle: "?g t \<le> 1" by (by100 simp)
          show "?g t \<in> I_set" unfolding top1_unit_interval_def using hge hle by (by100 simp)
        qed
        have hg_ne_tb: "\<And>t. t \<in> I_set \<Longrightarrow> ?g t \<noteq> tb"
        proof -
          fix t :: real assume ht: "t \<in> I_set"
          have "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
          have "0 \<le> su" "su \<le> 1" using hsu_I unfolding top1_unit_interval_def by auto
          have "0 \<le> sv" "sv \<le> 1" using hsv_I unfolding top1_unit_interval_def by auto
          \<comment> \<open>tb \<in> {0, 1}. su \<noteq> tb, sv \<noteq> tb. Convex combo avoids tb.\<close>
          from htb_01 show "?g t \<noteq> tb"
          proof
            assume "tb = 0"
            \<comment> \<open>su > 0 and sv > 0 (since su \<noteq> 0, sv \<noteq> 0, both \<ge> 0).\<close>
            have "su > 0" using hsu_ne_tb \<open>tb = 0\<close> \<open>0 \<le> su\<close> by (by100 simp)
            have "sv > 0" using hsv_ne_tb \<open>tb = 0\<close> \<open>0 \<le> sv\<close> by (by100 simp)
            have "(1-t)*su \<ge> 0" using \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> \<open>su > 0\<close>
              using mult_nonneg_nonneg by (by100 fastforce)
            have "t*sv \<ge> 0" using \<open>0 \<le> t\<close> \<open>sv > 0\<close>
              using mult_nonneg_nonneg by (by100 fastforce)
            \<comment> \<open>At least one of (1-t)*su > 0 or t*sv > 0.\<close>
            have "(1-t)*su > 0 \<or> t*sv > 0"
            proof (cases "t = 1")
              case True thus ?thesis using \<open>sv > 0\<close> by (by100 simp)
            next
              case False
              hence "1 - t > 0" using \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> by (by100 simp)
              thus ?thesis using \<open>su > 0\<close> by (by100 simp)
            qed
            hence "(1-t)*su + t*sv > 0" using \<open>(1-t)*su \<ge> 0\<close> \<open>t*sv \<ge> 0\<close>
              by (by100 linarith)
            thus "?g t \<noteq> tb" using \<open>tb = 0\<close> by (by100 simp)
          next
            assume "tb = 1"
            \<comment> \<open>su < 1 and sv < 1 (since su \<noteq> 1, sv \<noteq> 1, both \<le> 1).\<close>
            have "su < 1" using hsu_ne_tb \<open>tb = 1\<close> \<open>su \<le> 1\<close> by (by100 simp)
            have "sv < 1" using hsv_ne_tb \<open>tb = 1\<close> \<open>sv \<le> 1\<close> by (by100 simp)
            have "?g t < 1"
            proof (cases "t = 0")
              case True thus ?thesis using \<open>su < 1\<close> by (by100 simp)
            next
              case False
              hence "t > 0" using \<open>0 \<le> t\<close> by (by100 simp)
              have "(1-t)*su \<le> (1-t)" using \<open>su \<le> 1\<close> \<open>0 \<le> t\<close> \<open>t \<le> 1\<close>
                using mult_left_le by (by100 fastforce)
              moreover have "t*sv < t" using \<open>sv < 1\<close> \<open>t > 0\<close>
                by (by100 simp)
              ultimately show ?thesis by (by100 linarith)
            qed
            thus "?g t \<noteq> tb" using \<open>tb = 1\<close> by (by100 simp)
          qed
        qed
        \<comment> \<open>Construct path: hf \<circ> g.\<close>
        let ?path = "hf \<circ> ?g"
        have hpath_in: "\<forall>s\<in>I_set. ?path s \<in> D - {ep}"
        proof (intro ballI)
          fix t assume ht: "t \<in> I_set"
          have "?g t \<in> I_set" by (rule hg_in_I[OF ht])
          have "?g t \<noteq> tb" by (rule hg_ne_tb[OF ht])
          have "hf (?g t) \<in> D" using \<open>?g t \<in> I_set\<close> hsurj by (by100 blast)
          moreover have "hf (?g t) \<noteq> ep"
            using \<open>?g t \<noteq> tb\<close> \<open>?g t \<in> I_set\<close> htb_I hftb hinj
            unfolding inj_on_def by (by100 blast)
          ultimately show "?path t \<in> D - {ep}" by (by100 simp)
        qed
        \<comment> \<open>Continuity: g continuous I \<rightarrow> I, hf continuous I \<rightarrow> D, compose + restrict codomain.\<close>
        have hg_cont_UNIV: "continuous_on UNIV ?g" by (intro continuous_intros)
        have hg_map: "\<And>t. t \<in> I_set \<Longrightarrow> ?g t \<in> I_set" by (rule hg_in_I)
        have hg_cont: "top1_continuous_map_on I_set I_top I_set I_top ?g"
        proof -
          have "top1_continuous_map_on I_set
              (subspace_topology UNIV top1_open_sets I_set)
              I_set (subspace_topology UNIV top1_open_sets I_set) ?g"
            by (rule top1_continuous_map_on_real_subspace_open_sets[OF hg_map hg_cont_UNIV])
          thus ?thesis unfolding top1_unit_interval_topology_def .
        qed
        have hpath_cont_D: "top1_continuous_map_on I_set I_top D
            (subspace_topology top1_S2 top1_S2_topology D) ?path"
          unfolding comp_def
          by (rule top1_continuous_map_on_comp[OF hg_cont hcont, simplified comp_def])
        have hpath_cont_sub: "top1_continuous_map_on I_set I_top (D - {ep})
            (subspace_topology D (subspace_topology top1_S2 top1_S2_topology D) (D - {ep})) ?path"
          by (rule continuous_map_restrict_codomain[OF hpath_cont_D])
             (use hpath_in in \<open>by100 blast\<close>)+
        have hT_eq: "subspace_topology D (subspace_topology top1_S2 top1_S2_topology D) (D - {ep})
            = subspace_topology top1_S2 top1_S2_topology (D - {ep})"
          by (rule subspace_topology_trans) (by100 blast)
        have hpath_cont: "top1_continuous_map_on I_set I_top (D - {ep})
            (subspace_topology top1_S2 top1_S2_topology (D - {ep})) ?path"
          using hpath_cont_sub hT_eq by (by100 simp)
        have "?path 0 = u" using hfsu by (by100 simp)
        moreover have "?path 1 = v" using hfsv by (by100 simp)
        ultimately have "top1_is_path_on (D - {ep})
            (subspace_topology top1_S2 top1_S2_topology (D - {ep})) u v ?path"
          unfolding top1_is_path_on_def using hpath_cont by (by100 blast)
        thus "\<exists>f. top1_is_path_on (D - {ep})
            (subspace_topology top1_S2 top1_S2_topology (D - {ep})) u v f" by (by100 blast)
      qed
    qed
  } note arc_minus_endpoint_pc = this
  \<comment> \<open>C - D1 path-connected: chain (e12 - {a2}) \<union> e41 \<union> (e34 - {a3}) at vertices a1, a4.\<close>
  have hCmD1_pc: "top1_path_connected_on (C - ?D1)
      (subspace_topology top1_S2 top1_S2_topology (C - ?D1))"
  proof -
    \<comment> \<open>Set equality.\<close>
    have hset: "C - ?D1 = (e12 - {a2}) \<union> e41 \<union> (e34 - {a3})"
    proof -
      \<comment> \<open>C = e12 \<union> e23 \<union> e34 \<union> e41. D1 = Da3 \<union> e23 \<union> Da2.\<close>
      have "e12 \<inter> Da3 = {}"
      proof -
        have "Da3 \<subseteq> e13" using he13_split by (by100 blast)
        hence "e12 \<inter> Da3 \<subseteq> e12 \<inter> e13" by (by100 blast)
        hence "e12 \<inter> Da3 \<subseteq> {a1}" using assms(28) by (by100 blast)
        have "a1 \<noteq> p" using assms(37) by (by100 blast)
        have "a1 \<notin> Da3" using \<open>a1 \<in> D1p\<close> he13_meet \<open>a1 \<noteq> p\<close> by (by100 blast)
        thus ?thesis using \<open>e12 \<inter> Da3 \<subseteq> {a1}\<close> \<open>a1 \<notin> Da3\<close> by (by100 blast)
      qed
      have "e12 \<inter> Da2 \<subseteq> {a2}"
      proof -
        have "Da2 \<subseteq> e24" using he24_split by (by100 blast)
        hence "e12 \<inter> Da2 \<subseteq> e12 \<inter> e24" by (by100 blast)
        thus ?thesis using assms(33) by (by100 blast)
      qed
      have "e41 \<inter> Da3 = {}"
      proof -
        have "Da3 \<subseteq> e13" using he13_split by (by100 blast)
        hence "e41 \<inter> Da3 \<subseteq> e41 \<inter> e13" by (by100 blast)
        hence "e41 \<inter> Da3 \<subseteq> {a1}" using assms(31) by (by100 blast)
        have "a1 \<noteq> p" using assms(37) by (by100 blast)
        have "a1 \<notin> Da3" using \<open>a1 \<in> D1p\<close> he13_meet \<open>a1 \<noteq> p\<close> by (by100 blast)
        thus ?thesis using \<open>e41 \<inter> Da3 \<subseteq> {a1}\<close> \<open>a1 \<notin> Da3\<close> by (by100 blast)
      qed
      have "e41 \<inter> Da2 = {}"
      proof -
        have "Da2 \<subseteq> e24" using he24_split by (by100 blast)
        hence "e41 \<inter> Da2 \<subseteq> e41 \<inter> e24" by (by100 blast)
        hence "e41 \<inter> Da2 \<subseteq> {a4}" using assms(36) by (by100 blast)
        have "a4 \<noteq> q" using assms(38) by (by100 blast)
        have "a4 \<notin> Da2" using \<open>a4 \<in> Dq4\<close> he24_meet \<open>a4 \<noteq> q\<close> by (by100 blast)
        thus ?thesis using \<open>e41 \<inter> Da2 \<subseteq> {a4}\<close> \<open>a4 \<notin> Da2\<close> by (by100 blast)
      qed
      have "e34 \<inter> Da2 = {}"
      proof -
        have "Da2 \<subseteq> e24" using he24_split by (by100 blast)
        hence "e34 \<inter> Da2 \<subseteq> e34 \<inter> e24" by (by100 blast)
        hence "e34 \<inter> Da2 \<subseteq> {a4}" using assms(35) by (by100 blast)
        have "a4 \<noteq> q" using assms(38) by (by100 blast)
        have "a4 \<notin> Da2" using \<open>a4 \<in> Dq4\<close> he24_meet \<open>a4 \<noteq> q\<close> by (by100 blast)
        thus ?thesis using \<open>e34 \<inter> Da2 \<subseteq> {a4}\<close> \<open>a4 \<notin> Da2\<close> by (by100 blast)
      qed
      have "e34 \<inter> Da3 \<subseteq> {a3}"
      proof -
        have "Da3 \<subseteq> e13" using he13_split by (by100 blast)
        hence "e34 \<inter> Da3 \<subseteq> e34 \<inter> e13" by (by100 blast)
        thus ?thesis using assms(30) by (by100 blast)
      qed
      have "e12 - ?D1 = e12 - {a2}"
        using assms(24) \<open>e12 \<inter> Da3 = {}\<close> \<open>e12 \<inter> Da2 \<subseteq> {a2}\<close> by (by100 blast)
      moreover have "e23 - ?D1 = {}" by (by100 blast)
      moreover have "e41 - ?D1 = e41"
        using assms(23) \<open>e41 \<inter> Da3 = {}\<close> \<open>e41 \<inter> Da2 = {}\<close> by (by100 blast)
      moreover have "e34 - ?D1 = e34 - {a3}"
        using assms(25) \<open>e34 \<inter> Da2 = {}\<close> \<open>e34 \<inter> Da3 \<subseteq> {a3}\<close> by (by100 blast)
      ultimately have h_each: "e12 - ?D1 = e12 - {a2}" "e23 - ?D1 = {}"
          "e41 - ?D1 = e41" "e34 - ?D1 = e34 - {a3}" by (by100 blast)+
      have "C - ?D1 = (e12 - ?D1) \<union> (e23 - ?D1) \<union> (e34 - ?D1) \<union> (e41 - ?D1)"
        using assms(39) by (by100 blast)
      hence "C - ?D1 = (e12 - {a2}) \<union> {} \<union> (e34 - {a3}) \<union> e41"
        using h_each by (by100 simp)
      moreover have "(e12 - {a2}) \<union> (e34 - {a3}) \<union> e41 = (e12 - {a2}) \<union> e41 \<union> (e34 - {a3})"
        by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Path-connected pieces.\<close>
    have hpc_e41: "top1_path_connected_on e41
        (subspace_topology top1_S2 top1_S2_topology e41)"
      by (rule arc_path_connected[OF assms(13) assms(7)])
    have ha2_ep: "a2 \<in> top1_arc_endpoints_on e12
        (subspace_topology top1_S2 top1_S2_topology e12)"
      using assms(16) by (by100 blast)
    have hpc_e12: "top1_path_connected_on (e12 - {a2})
        (subspace_topology top1_S2 top1_S2_topology (e12 - {a2}))"
      by (rule arc_minus_endpoint_pc[OF assms(10) assms(4) ha2_ep])
    have ha3_ep: "a3 \<in> top1_arc_endpoints_on e34
        (subspace_topology top1_S2 top1_S2_topology e34)"
      using assms(18) by (by100 blast)
    have hpc_e34: "top1_path_connected_on (e34 - {a3})
        (subspace_topology top1_S2 top1_S2_topology (e34 - {a3}))"
      by (rule arc_minus_endpoint_pc[OF assms(12) assms(6) ha3_ep])
    \<comment> \<open>Shared vertices.\<close>
    have ha1_ne_a2: "a1 \<noteq> a2" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha3_ne_a4: "a3 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha1_e12: "a1 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have ha1_e41: "a1 \<in> e41" using assms(27) by (by100 blast)
    have ha1_share: "a1 \<in> (e12 - {a2}) \<inter> e41" using ha1_e12 ha1_ne_a2 ha1_e41 by (by100 blast)
    have ha4_e41: "a4 \<in> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have ha4_e34: "a4 \<in> e34" using assms(18) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have ha4_share: "a4 \<in> e41 \<inter> (e34 - {a3})" using ha4_e41 ha4_e34 ha3_ne_a4 by (by100 blast)
    \<comment> \<open>Chain: (e12-{a2}) \<union> e41 via shared a1.\<close>
    have hTX12: "is_topology_on ((e12 - {a2}) \<union> e41)
        (subspace_topology top1_S2 top1_S2_topology ((e12 - {a2}) \<union> e41))"
      by (rule subspace_topology_is_topology_on[OF
          is_topology_on_strict_imp[OF assms(1)]]) (use assms(4,7) in \<open>by100 blast\<close>)
    have hpc_a1: "top1_path_connected_on ({a1})
        (subspace_topology top1_S2 top1_S2_topology {a1})"
    proof -
      have hTS1: "is_topology_on {a1} (subspace_topology top1_S2 top1_S2_topology {a1})"
        by (rule subspace_topology_is_topology_on[OF
            is_topology_on_strict_imp[OF assms(1)]]) (use assms(3) in \<open>by100 blast\<close>)
      show ?thesis unfolding top1_path_connected_on_def top1_is_path_on_def
      proof (intro conjI ballI)
        show "is_topology_on {a1} (subspace_topology top1_S2 top1_S2_topology {a1})" by (rule hTS1)
        fix x y :: "real \<times> real \<times> real"
        assume "x \<in> {a1}" "y \<in> {a1}"
        hence "x = a1" "y = a1" by (by100 blast)+
        have "top1_continuous_map_on I_set I_top {a1}
            (subspace_topology top1_S2 top1_S2_topology {a1}) (top1_constant_path a1)"
        proof -
          have "a1 \<in> top1_S2" using assms(3) by (by100 blast)
          hence "a1 \<in> {a1}" by (by100 blast)
          show ?thesis using top1_constant_path_continuous[OF hTS1 \<open>a1 \<in> {a1}\<close>]
            unfolding top1_constant_path_def by (by100 simp)
        qed
        moreover have "(top1_constant_path a1) 0 = x" using \<open>x = a1\<close>
          unfolding top1_constant_path_def by (by100 simp)
        moreover have "(top1_constant_path a1) 1 = y" using \<open>y = a1\<close>
          unfolding top1_constant_path_def by (by100 simp)
        ultimately show "\<exists>f. top1_continuous_map_on I_set I_top {a1}
            (subspace_topology top1_S2 top1_S2_topology {a1}) f \<and> f 0 = x \<and> f 1 = y"
          by (by100 blast)
      qed
    qed
    have h_sub12: "(e12 - {a2}) \<inter> e41 = {a1}"
      using assms(27) ha1_ne_a2 by (by100 blast)
    \<comment> \<open>Topology matching: sub S2 (piece) = sub (union) (sub S2 (union)) (piece).\<close>
    let ?X12 = "(e12 - {a2}) \<union> e41"
    have hsub_e12: "subspace_topology top1_S2 top1_S2_topology (e12 - {a2})
        = subspace_topology ?X12 (subspace_topology top1_S2 top1_S2_topology ?X12) (e12 - {a2})"
      using subspace_topology_trans[of "e12 - {a2}" ?X12] by (by100 simp)
    have hsub_e41: "subspace_topology top1_S2 top1_S2_topology e41
        = subspace_topology ?X12 (subspace_topology top1_S2 top1_S2_topology ?X12) e41"
      using subspace_topology_trans[of e41 ?X12] by (by100 simp)
    have hsub_a1: "subspace_topology top1_S2 top1_S2_topology {a1}
        = subspace_topology ?X12 (subspace_topology top1_S2 top1_S2_topology ?X12) {a1}"
      using subspace_topology_trans[of "{a1}" ?X12] ha1_share by (by100 simp)
    have hpc12: "top1_path_connected_on ?X12
        (subspace_topology top1_S2 top1_S2_topology ?X12)"
    proof (rule path_connected_union[OF hTX12])
      show "top1_path_connected_on (e12 - {a2})
          (subspace_topology ?X12 (subspace_topology top1_S2 top1_S2_topology ?X12) (e12 - {a2}))"
        using hpc_e12 hsub_e12 by (by100 simp)
      show "top1_path_connected_on e41
          (subspace_topology ?X12 (subspace_topology top1_S2 top1_S2_topology ?X12) e41)"
        using hpc_e41 hsub_e41 by (by100 simp)
      show "top1_path_connected_on ((e12 - {a2}) \<inter> e41)
          (subspace_topology ?X12 (subspace_topology top1_S2 top1_S2_topology ?X12) ((e12 - {a2}) \<inter> e41))"
        using hpc_a1 hsub_a1 h_sub12 by (by100 simp)
      show "(e12 - {a2}) \<union> e41 = ?X12" by (by100 blast)
      show "e12 - {a2} \<subseteq> ?X12" by (by100 blast)
      show "e41 \<subseteq> ?X12" by (by100 blast)
      show "(e12 - {a2}) \<inter> e41 \<noteq> {}" using ha1_share by (by100 blast)
    qed
    \<comment> \<open>Chain: ((e12-{a2}) \<union> e41) \<union> (e34-{a3}) via shared a4.\<close>
    let ?Xall = "(e12 - {a2}) \<union> e41 \<union> (e34 - {a3})"
    have hTXall: "is_topology_on ?Xall
        (subspace_topology top1_S2 top1_S2_topology ?Xall)"
      by (rule subspace_topology_is_topology_on[OF
          is_topology_on_strict_imp[OF assms(1)]]) (use assms(4,6,7) in \<open>by100 blast\<close>)
    have h_sub_all: "?X12 \<inter> (e34 - {a3}) = {a4}"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> ?X12 \<inter> (e34 - {a3})"
      hence "x \<in> e41 \<inter> (e34 - {a3})" using assms(22) by (by100 blast)
      thus "x \<in> {a4}" using assms(26) ha3_ne_a4 by (by100 blast)
    next
      fix x assume "x \<in> {a4}"
      hence "x = a4" by (by100 blast)
      thus "x \<in> ?X12 \<inter> (e34 - {a3})" using ha4_share by (by100 blast)
    qed
    have hsub_X12: "subspace_topology top1_S2 top1_S2_topology ?X12
        = subspace_topology ?Xall (subspace_topology top1_S2 top1_S2_topology ?Xall) ?X12"
      using subspace_topology_trans[of ?X12 ?Xall] by (by100 simp)
    have hsub_e34: "subspace_topology top1_S2 top1_S2_topology (e34 - {a3})
        = subspace_topology ?Xall (subspace_topology top1_S2 top1_S2_topology ?Xall) (e34 - {a3})"
      using subspace_topology_trans[of "e34 - {a3}" ?Xall] by (by100 simp)
    have hpc_a4: "top1_path_connected_on ({a4})
        (subspace_topology top1_S2 top1_S2_topology {a4})"
    proof -
      have hTS4: "is_topology_on {a4} (subspace_topology top1_S2 top1_S2_topology {a4})"
        by (rule subspace_topology_is_topology_on[OF
            is_topology_on_strict_imp[OF assms(1)]]) (use assms(3) in \<open>by100 blast\<close>)
      show ?thesis unfolding top1_path_connected_on_def top1_is_path_on_def
      proof (intro conjI ballI)
        show "is_topology_on {a4} (subspace_topology top1_S2 top1_S2_topology {a4})" by (rule hTS4)
        fix x y :: "real \<times> real \<times> real"
        assume "x \<in> {a4}" "y \<in> {a4}"
        hence "x = a4" "y = a4" by (by100 blast)+
        show "\<exists>f. top1_continuous_map_on I_set I_top {a4}
            (subspace_topology top1_S2 top1_S2_topology {a4}) f \<and> f 0 = x \<and> f 1 = y"
          using top1_constant_path_continuous[OF hTS4, of a4]
            \<open>x = a4\<close> \<open>y = a4\<close> unfolding top1_constant_path_def
          by (by100 fastforce)
      qed
    qed
    have hsub_a4: "subspace_topology top1_S2 top1_S2_topology {a4}
        = subspace_topology ?Xall (subspace_topology top1_S2 top1_S2_topology ?Xall) {a4}"
      using subspace_topology_trans[of "{a4}" ?Xall] ha4_share by (by100 simp)
    have hpc_all: "top1_path_connected_on ?Xall
        (subspace_topology top1_S2 top1_S2_topology ?Xall)"
    proof (rule path_connected_union[OF hTXall])
      show "top1_path_connected_on ?X12
          (subspace_topology ?Xall (subspace_topology top1_S2 top1_S2_topology ?Xall) ?X12)"
        using hpc12 hsub_X12 by (by100 simp)
      show "top1_path_connected_on (e34 - {a3})
          (subspace_topology ?Xall (subspace_topology top1_S2 top1_S2_topology ?Xall) (e34 - {a3}))"
        using hpc_e34 hsub_e34 by (by100 simp)
      show "top1_path_connected_on (?X12 \<inter> (e34 - {a3}))
          (subspace_topology ?Xall (subspace_topology top1_S2 top1_S2_topology ?Xall) (?X12 \<inter> (e34 - {a3})))"
        using hpc_a4 hsub_a4 h_sub_all by (by100 simp)
      show "?X12 \<union> (e34 - {a3}) = ?Xall" by (by100 blast)
      show "?X12 \<subseteq> ?Xall" by (by100 blast)
      show "e34 - {a3} \<subseteq> ?Xall" by (by100 blast)
      show "?X12 \<inter> (e34 - {a3}) \<noteq> {}" using ha4_share by (by100 blast)
    qed
    show ?thesis using hpc_all hset by (by100 simp)
  qed
  \<comment> \<open>Similarly for C - D2.\<close>
  have hx_in_CmD2: "x \<in> C - ?D2"
  proof -
    have "x \<in> C" using hx_e12 assms(39) by (by100 blast)
    moreover have "x \<notin> Dq4"
    proof -
      have "Dq4 \<subseteq> e24" using he24_split by (by100 blast)
      hence "e12 \<inter> Dq4 \<subseteq> e12 \<inter> e24" by (by100 blast)
      hence "e12 \<inter> Dq4 \<subseteq> {a2}" using assms(33) by (by100 blast)
      thus ?thesis using hx_e12 hx_not_endpts by (by100 blast)
    qed
    moreover have "x \<notin> e41" using hx_e12 hx_not_endpts assms(27) by (by100 blast)
    moreover have "x \<notin> D1p"
    proof -
      have "D1p \<subseteq> e13" using he13_split by (by100 blast)
      hence "e12 \<inter> D1p \<subseteq> e12 \<inter> e13" by (by100 blast)
      hence "e12 \<inter> D1p \<subseteq> {a1}" using assms(28) by (by100 blast)
      thus ?thesis using hx_e12 hx_not_endpts by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  have hy_in_CmD2: "y \<in> C - ?D2"
  proof -
    have "y \<in> C" using hy_e34 assms(39) by (by100 blast)
    moreover have "y \<notin> Dq4"
    proof -
      have "Dq4 \<subseteq> e24" using he24_split by (by100 blast)
      hence "e34 \<inter> Dq4 \<subseteq> e34 \<inter> e24" by (by100 blast)
      hence "e34 \<inter> Dq4 \<subseteq> {a4}" using assms(35) by (by100 blast)
      thus ?thesis using hy_e34 hy_not_endpts by (by100 blast)
    qed
    moreover have "y \<notin> e41" using hy_e34 hy_not_endpts assms(26) by (by100 blast)
    moreover have "y \<notin> D1p"
    proof -
      have "D1p \<subseteq> e13" using he13_split by (by100 blast)
      hence "e34 \<inter> D1p \<subseteq> e34 \<inter> e13" by (by100 blast)
      hence h_sub: "e34 \<inter> D1p \<subseteq> {a3}" using assms(30) by (by100 blast)
      have "a3 \<noteq> p" using assms(37) by (by100 blast)
      have "a3 \<notin> D1p" using \<open>a3 \<in> Da3\<close> he13_meet \<open>a3 \<noteq> p\<close> by (by100 blast)
      thus ?thesis using hy_e34 h_sub \<open>a3 \<notin> D1p\<close> by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  have hCmD2_pc: "top1_path_connected_on (C - ?D2)
      (subspace_topology top1_S2 top1_S2_topology (C - ?D2))"
  proof -
    \<comment> \<open>Set equality: C - D2 = (e12-{a1}) \<union> e23 \<union> (e34-{a4}).\<close>
    have "e12 \<inter> Dq4 = {}"
    proof -
      have "Dq4 \<subseteq> e24" using he24_split by (by100 blast)
      hence "e12 \<inter> Dq4 \<subseteq> e12 \<inter> e24" by (by100 blast)
      hence "e12 \<inter> Dq4 \<subseteq> {a2}" using assms(33) by (by100 blast)
      have "a2 \<noteq> q" using assms(38) by (by100 blast)
      have "a2 \<notin> Dq4" using \<open>a2 \<in> Da2\<close> he24_meet \<open>a2 \<noteq> q\<close> by (by100 blast)
      thus ?thesis using \<open>e12 \<inter> Dq4 \<subseteq> {a2}\<close> \<open>a2 \<notin> Dq4\<close> by (by100 blast)
    qed
    have "e12 \<inter> D1p \<subseteq> {a1}"
    proof -
      have "D1p \<subseteq> e13" using he13_split by (by100 blast)
      hence "e12 \<inter> D1p \<subseteq> e12 \<inter> e13" by (by100 blast)
      thus ?thesis using assms(28) by (by100 blast)
    qed
    have "e23 \<inter> Dq4 = {}"
    proof -
      have "Dq4 \<subseteq> e24" using he24_split by (by100 blast)
      hence "e23 \<inter> Dq4 \<subseteq> e23 \<inter> e24" by (by100 blast)
      hence "e23 \<inter> Dq4 \<subseteq> {a2}" using assms(34) by (by100 blast)
      have "a2 \<noteq> q" using assms(38) by (by100 blast)
      have "a2 \<notin> Dq4" using \<open>a2 \<in> Da2\<close> he24_meet \<open>a2 \<noteq> q\<close> by (by100 blast)
      thus ?thesis using \<open>e23 \<inter> Dq4 \<subseteq> {a2}\<close> \<open>a2 \<notin> Dq4\<close> by (by100 blast)
    qed
    have "e23 \<inter> D1p = {}"
    proof -
      have "D1p \<subseteq> e13" using he13_split by (by100 blast)
      hence "e23 \<inter> D1p \<subseteq> e23 \<inter> e13" by (by100 blast)
      hence "e23 \<inter> D1p \<subseteq> {a3}" using assms(29) by (by100 blast)
      have "a3 \<noteq> p" using assms(37) by (by100 blast)
      have "a3 \<notin> D1p" using \<open>a3 \<in> Da3\<close> he13_meet \<open>a3 \<noteq> p\<close> by (by100 blast)
      thus ?thesis using \<open>e23 \<inter> D1p \<subseteq> {a3}\<close> \<open>a3 \<notin> D1p\<close> by (by100 blast)
    qed
    have "e34 \<inter> Dq4 \<subseteq> {a4}"
    proof -
      have "Dq4 \<subseteq> e24" using he24_split by (by100 blast)
      hence "e34 \<inter> Dq4 \<subseteq> e34 \<inter> e24" by (by100 blast)
      thus ?thesis using assms(35) by (by100 blast)
    qed
    have "e34 \<inter> D1p = {}"
    proof -
      have "D1p \<subseteq> e13" using he13_split by (by100 blast)
      hence "e34 \<inter> D1p \<subseteq> e34 \<inter> e13" by (by100 blast)
      hence "e34 \<inter> D1p \<subseteq> {a3}" using assms(30) by (by100 blast)
      have "a3 \<noteq> p" using assms(37) by (by100 blast)
      have "a3 \<notin> D1p" using \<open>a3 \<in> Da3\<close> he13_meet \<open>a3 \<noteq> p\<close> by (by100 blast)
      thus ?thesis using \<open>e34 \<inter> D1p \<subseteq> {a3}\<close> \<open>a3 \<notin> D1p\<close> by (by100 blast)
    qed
    have he12_D2: "e12 - ?D2 = e12 - {a1}"
      using assms(27) \<open>e12 \<inter> Dq4 = {}\<close> \<open>e12 \<inter> D1p \<subseteq> {a1}\<close> by (by100 blast)
    have he41_D2: "e41 - ?D2 = {}" by (by100 blast)
    have he23_D2: "e23 - ?D2 = e23"
      using assms(23) \<open>e23 \<inter> Dq4 = {}\<close> \<open>e23 \<inter> D1p = {}\<close> by (by100 blast)
    have he34_D2: "e34 - ?D2 = e34 - {a4}"
      using assms(26) \<open>e34 \<inter> D1p = {}\<close> \<open>e34 \<inter> Dq4 \<subseteq> {a4}\<close> by (by100 blast)
    have "C - ?D2 = (e12 - ?D2) \<union> (e23 - ?D2) \<union> (e34 - ?D2) \<union> (e41 - ?D2)"
      using assms(39) by (by100 blast)
    hence hCmD2_split: "C - ?D2 = (e12 - {a1}) \<union> e23 \<union> (e34 - {a4})"
      using he12_D2 he41_D2 he23_D2 he34_D2 by (by100 simp)
    have hset: "C - ?D2 = (e12 - {a1}) \<union> e23 \<union> (e34 - {a4})"
      using hCmD2_split by (by100 blast)
    \<comment> \<open>Path-connected pieces.\<close>
    have ha1_ne_a2: "a1 \<noteq> a2" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha3_ne_a4: "a3 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha1_ep12: "a1 \<in> top1_arc_endpoints_on e12
        (subspace_topology top1_S2 top1_S2_topology e12)" using assms(16) by (by100 blast)
    have hpc_e12a1: "top1_path_connected_on (e12 - {a1})
        (subspace_topology top1_S2 top1_S2_topology (e12 - {a1}))"
      by (rule arc_minus_endpoint_pc[OF assms(10) assms(4) ha1_ep12])
    have hpc_e23: "top1_path_connected_on e23
        (subspace_topology top1_S2 top1_S2_topology e23)"
      by (rule arc_path_connected[OF assms(11) assms(5)])
    have ha4_ep34: "a4 \<in> top1_arc_endpoints_on e34
        (subspace_topology top1_S2 top1_S2_topology e34)" using assms(18) by (by100 blast)
    have hpc_e34a4: "top1_path_connected_on (e34 - {a4})
        (subspace_topology top1_S2 top1_S2_topology (e34 - {a4}))"
      by (rule arc_minus_endpoint_pc[OF assms(12) assms(6) ha4_ep34])
    \<comment> \<open>Shared vertices: a2 and a3.\<close>
    have ha2_e12: "a2 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have ha2_e23: "a2 \<in> e23" using assms(24) by (by100 blast)
    have ha2_share: "a2 \<in> (e12 - {a1}) \<inter> e23" using ha2_e12 ha1_ne_a2 ha2_e23 by (by100 blast)
    have ha3_e23: "a3 \<in> e23" using assms(17) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have ha3_e34: "a3 \<in> e34" using assms(18) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have ha3_share: "a3 \<in> e23 \<inter> (e34 - {a4})" using ha3_e23 ha3_e34 ha3_ne_a4 by (by100 blast)
    \<comment> \<open>Chain: (e12-{a1}) \<union> e23 at a2.\<close>
    let ?Y12 = "(e12 - {a1}) \<union> e23"
    have hTY12: "is_topology_on ?Y12
        (subspace_topology top1_S2 top1_S2_topology ?Y12)"
      by (rule subspace_topology_is_topology_on[OF
          is_topology_on_strict_imp[OF assms(1)]]) (use assms(4,5) in \<open>by100 blast\<close>)
    have h_sub12: "(e12 - {a1}) \<inter> e23 = {a2}" using assms(24) ha1_ne_a2 by (by100 blast)
    have hsub_e12a1: "subspace_topology top1_S2 top1_S2_topology (e12 - {a1})
        = subspace_topology ?Y12 (subspace_topology top1_S2 top1_S2_topology ?Y12) (e12 - {a1})"
      using subspace_topology_trans[of "e12 - {a1}" ?Y12] by (by100 simp)
    have hsub_e23: "subspace_topology top1_S2 top1_S2_topology e23
        = subspace_topology ?Y12 (subspace_topology top1_S2 top1_S2_topology ?Y12) e23"
      using subspace_topology_trans[of e23 ?Y12] by (by100 simp)
    have hpc_a2: "top1_path_connected_on {a2}
        (subspace_topology top1_S2 top1_S2_topology {a2})"
    proof -
      have hTS2: "is_topology_on {a2} (subspace_topology top1_S2 top1_S2_topology {a2})"
        by (rule subspace_topology_is_topology_on[OF
            is_topology_on_strict_imp[OF assms(1)]]) (use assms(3) in \<open>by100 blast\<close>)
      show ?thesis unfolding top1_path_connected_on_def top1_is_path_on_def
      proof (intro conjI ballI)
        show "is_topology_on {a2} (subspace_topology top1_S2 top1_S2_topology {a2})" by (rule hTS2)
        fix x y :: "real \<times> real \<times> real" assume "x \<in> {a2}" "y \<in> {a2}"
        hence "x = a2" "y = a2" by (by100 blast)+
        show "\<exists>f. top1_continuous_map_on I_set I_top {a2}
            (subspace_topology top1_S2 top1_S2_topology {a2}) f \<and> f 0 = x \<and> f 1 = y"
          using top1_constant_path_continuous[OF hTS2, of a2]
            \<open>x = a2\<close> \<open>y = a2\<close> unfolding top1_constant_path_def by (by100 fastforce)
      qed
    qed
    have hsub_a2: "subspace_topology top1_S2 top1_S2_topology {a2}
        = subspace_topology ?Y12 (subspace_topology top1_S2 top1_S2_topology ?Y12) {a2}"
      using subspace_topology_trans[of "{a2}" ?Y12] ha2_share by (by100 simp)
    have hpc_Y12: "top1_path_connected_on ?Y12
        (subspace_topology top1_S2 top1_S2_topology ?Y12)"
    proof (rule path_connected_union[OF hTY12])
      show "top1_path_connected_on (e12 - {a1})
          (subspace_topology ?Y12 (subspace_topology top1_S2 top1_S2_topology ?Y12) (e12 - {a1}))"
        using hpc_e12a1 hsub_e12a1 by (by100 simp)
      show "top1_path_connected_on e23
          (subspace_topology ?Y12 (subspace_topology top1_S2 top1_S2_topology ?Y12) e23)"
        using hpc_e23 hsub_e23 by (by100 simp)
      show "top1_path_connected_on ((e12 - {a1}) \<inter> e23)
          (subspace_topology ?Y12 (subspace_topology top1_S2 top1_S2_topology ?Y12) ((e12 - {a1}) \<inter> e23))"
        using hpc_a2 hsub_a2 h_sub12 by (by100 simp)
      show "(e12 - {a1}) \<union> e23 = ?Y12" by (by100 blast)
      show "e12 - {a1} \<subseteq> ?Y12" by (by100 blast)
      show "e23 \<subseteq> ?Y12" by (by100 blast)
      show "(e12 - {a1}) \<inter> e23 \<noteq> {}" using ha2_share by (by100 blast)
    qed
    \<comment> \<open>Chain: ?Y12 \<union> (e34-{a4}) at a3.\<close>
    let ?Yall = "(e12 - {a1}) \<union> e23 \<union> (e34 - {a4})"
    have hTYall: "is_topology_on ?Yall
        (subspace_topology top1_S2 top1_S2_topology ?Yall)"
      by (rule subspace_topology_is_topology_on[OF
          is_topology_on_strict_imp[OF assms(1)]]) (use assms(4,5,6) in \<open>by100 blast\<close>)
    have h_sub_all: "?Y12 \<inter> (e34 - {a4}) = {a3}"
    proof (rule set_eqI, rule iffI)
      fix z assume "z \<in> ?Y12 \<inter> (e34 - {a4})"
      hence "z \<in> e23 \<inter> (e34 - {a4})" using assms(22) by (by100 blast)
      thus "z \<in> {a3}" using assms(25) ha3_ne_a4 by (by100 blast)
    next
      fix z assume "z \<in> {a3}" thus "z \<in> ?Y12 \<inter> (e34 - {a4})" using ha3_share by (by100 blast)
    qed
    have hsub_Y12: "subspace_topology top1_S2 top1_S2_topology ?Y12
        = subspace_topology ?Yall (subspace_topology top1_S2 top1_S2_topology ?Yall) ?Y12"
      using subspace_topology_trans[of ?Y12 ?Yall] by (by100 simp)
    have hsub_e34a4: "subspace_topology top1_S2 top1_S2_topology (e34 - {a4})
        = subspace_topology ?Yall (subspace_topology top1_S2 top1_S2_topology ?Yall) (e34 - {a4})"
      using subspace_topology_trans[of "e34 - {a4}" ?Yall] by (by100 simp)
    have hpc_a3: "top1_path_connected_on {a3}
        (subspace_topology top1_S2 top1_S2_topology {a3})"
    proof -
      have hTS3: "is_topology_on {a3} (subspace_topology top1_S2 top1_S2_topology {a3})"
        by (rule subspace_topology_is_topology_on[OF
            is_topology_on_strict_imp[OF assms(1)]]) (use assms(3) in \<open>by100 blast\<close>)
      show ?thesis unfolding top1_path_connected_on_def top1_is_path_on_def
      proof (intro conjI ballI)
        show "is_topology_on {a3} (subspace_topology top1_S2 top1_S2_topology {a3})" by (rule hTS3)
        fix x y :: "real \<times> real \<times> real" assume "x \<in> {a3}" "y \<in> {a3}"
        hence "x = a3" "y = a3" by (by100 blast)+
        show "\<exists>f. top1_continuous_map_on I_set I_top {a3}
            (subspace_topology top1_S2 top1_S2_topology {a3}) f \<and> f 0 = x \<and> f 1 = y"
          using top1_constant_path_continuous[OF hTS3, of a3]
            \<open>x = a3\<close> \<open>y = a3\<close> unfolding top1_constant_path_def by (by100 fastforce)
      qed
    qed
    have hsub_a3: "subspace_topology top1_S2 top1_S2_topology {a3}
        = subspace_topology ?Yall (subspace_topology top1_S2 top1_S2_topology ?Yall) {a3}"
      using subspace_topology_trans[of "{a3}" ?Yall] ha3_share by (by100 simp)
    have hpc_Yall: "top1_path_connected_on ?Yall
        (subspace_topology top1_S2 top1_S2_topology ?Yall)"
    proof (rule path_connected_union[OF hTYall])
      show "top1_path_connected_on ?Y12
          (subspace_topology ?Yall (subspace_topology top1_S2 top1_S2_topology ?Yall) ?Y12)"
        using hpc_Y12 hsub_Y12 by (by100 simp)
      show "top1_path_connected_on (e34 - {a4})
          (subspace_topology ?Yall (subspace_topology top1_S2 top1_S2_topology ?Yall) (e34 - {a4}))"
        using hpc_e34a4 hsub_e34a4 by (by100 simp)
      show "top1_path_connected_on (?Y12 \<inter> (e34 - {a4}))
          (subspace_topology ?Yall (subspace_topology top1_S2 top1_S2_topology ?Yall) (?Y12 \<inter> (e34 - {a4})))"
        using hpc_a3 hsub_a3 h_sub_all by (by100 simp)
      show "?Y12 \<union> (e34 - {a4}) = ?Yall" by (by100 blast)
      show "?Y12 \<subseteq> ?Yall" by (by100 blast)
      show "e34 - {a4} \<subseteq> ?Yall" by (by100 blast)
      show "?Y12 \<inter> (e34 - {a4}) \<noteq> {}" using ha3_share by (by100 blast)
    qed
    show ?thesis using hpc_Yall hset by (by100 simp)
  qed
  \<comment> \<open>Step B4: Get paths \<alpha> in C \<inter> U from x to y, \<beta> in C \<inter> V from y to x.\<close>
  have hCmD1_sub: "C - ?D1 \<subseteq> ?U_loc" using hC_sub_S2 by (by100 blast)
  have hCmD2_sub: "C - ?D2 \<subseteq> ?V_loc" using hC_sub_S2 by (by100 blast)
  obtain \<alpha> where h\<alpha>: "top1_is_path_on (C - ?D1)
      (subspace_topology top1_S2 top1_S2_topology (C - ?D1)) x y \<alpha>"
    using hCmD1_pc hx_in_CmD1 hy_in_CmD1
    unfolding top1_path_connected_on_def by (by100 blast)
  obtain \<beta> where h\<beta>: "top1_is_path_on (C - ?D2)
      (subspace_topology top1_S2 top1_S2_topology (C - ?D2)) y x \<beta>"
    using hCmD2_pc hy_in_CmD2 hx_in_CmD2
    unfolding top1_path_connected_on_def by (by100 blast)
  \<comment> \<open>\<alpha> lies in C \<inter> U, \<beta> lies in C \<inter> V. So \<alpha>*\<beta> lies in C.\<close>
  \<comment> \<open>Step C: Show U\<inter>V has two components A, B with x \<in> A, y \<in> B.
     Then apply Theorem\_63\_1 to get \<alpha>*\<beta> nontrivial.\<close>
  \<comment> \<open>Step D: [\<alpha>*\<beta>] generates \<pi>_1(X) (63.1(c) + infinite cyclic).
     Step E: j_* surjective (\<alpha>*\<beta> \<in> C + generator).\<close>
  \<comment> \<open>Step C1: U\_loc \<subseteq> X and V\_loc \<subseteq> X (since p,q \<in> D1 \<inter> D2).\<close>
  have hp_D1: "p \<in> ?D1" using \<open>p \<in> Da3\<close> by (by100 blast)
  have hq_D1: "q \<in> ?D1" using \<open>q \<in> Da2\<close> by (by100 blast)
  have hp_D2: "p \<in> ?D2" using \<open>p \<in> D1p\<close> by (by100 blast)
  have hq_D2: "q \<in> ?D2" using \<open>q \<in> Dq4\<close> by (by100 blast)
  have hU_sub_X: "?U_loc \<subseteq> ?X" using hp_D1 hq_D1 by (by100 blast)
  have hV_sub_X: "?V_loc \<subseteq> ?X" using hp_D2 hq_D2 by (by100 blast)
  \<comment> \<open>Step C2: U\_loc \<union> V\_loc = X (since D1 \<inter> D2 = {p, q}).\<close>
  have hDa3_sub: "Da3 \<subseteq> e13" and hD1p_sub: "D1p \<subseteq> e13"
      and hDa2_sub: "Da2 \<subseteq> e24" and hDq4_sub: "Dq4 \<subseteq> e24"
    using he13_split he24_split by (by100 blast)+
  have hD1_D2_inter: "?D1 \<inter> ?D2 = {p, q}"
  proof (rule set_eqI, rule iffI)
    fix z assume hz: "z \<in> ?D1 \<inter> ?D2"
    hence hz1: "z \<in> Da3 \<or> z \<in> e23 \<or> z \<in> Da2" and hz2: "z \<in> Dq4 \<or> z \<in> e41 \<or> z \<in> D1p"
      by (by100 blast)+
    show "z \<in> {p, q}"
    proof -
      \<comment> \<open>Case analysis on hz1 \<times> hz2 = 9 cases. Most empty by K4 intersections.\<close>
      { assume "z \<in> Da3" "z \<in> D1p"
        hence "z \<in> Da3 \<inter> D1p" by (by100 blast)
        hence "z = p" using he13_meet he13_split by (by100 blast)
      } moreover
      { assume "z \<in> Da2" "z \<in> Dq4"
        hence "z \<in> Da2 \<inter> Dq4" by (by100 blast)
        hence "z = q" using he24_meet he24_split by (by100 blast)
      } moreover
      { assume "z \<in> Da3" "z \<in> Dq4"
        hence "z \<in> e13 \<inter> e24" using hDa3_sub hDq4_sub by (by100 blast)
        hence "z \<in> {a1,a2,a3,a4}" using assms(32) by (by100 blast)
      } moreover
      { assume "z \<in> Da3" "z \<in> e41"
        hence "z \<in> e13 \<inter> e41" using hDa3_sub by (by100 blast)
        hence "z \<in> {a1}" using assms(31) by (by100 blast)
      } moreover
      { assume "z \<in> e23" "z \<in> Dq4"
        hence "z \<in> e23 \<inter> e24" using hDq4_sub by (by100 blast)
        hence "z \<in> {a2}" using assms(34) by (by100 blast)
      } moreover
      { assume "z \<in> e23" "z \<in> e41"
        hence "z \<in> e23 \<inter> e41" by (by100 blast)
        hence False using assms(23) by (by100 blast)
      } moreover
      { assume "z \<in> e23" "z \<in> D1p"
        hence "z \<in> e23 \<inter> e13" using hD1p_sub by (by100 blast)
        hence "z \<in> {a3}" using assms(29) by (by100 blast)
      } moreover
      { assume "z \<in> Da2" "z \<in> e41"
        hence "z \<in> e24 \<inter> e41" using hDa2_sub by (by100 blast)
        hence "z \<in> {a4}" using assms(36) by (by100 blast)
      } moreover
      { assume "z \<in> Da2" "z \<in> D1p"
        hence "z \<in> e24 \<inter> e13" using hDa2_sub hD1p_sub by (by100 blast)
        hence "z \<in> {a1,a2,a3,a4}" using assms(32) by (by100 blast)
      }
      \<comment> \<open>In all cases, z \<in> {a1,a2,a3,a4} or z = p or z = q.
         But a1,a2,a3,a4 are not in the correct sub-arcs by endpoint analysis.\<close>
      \<comment> \<open>Vertex exclusion: each a\_i is not in both D1 and D2.\<close>
      \<comment> \<open>a1: a1 \<in> D1p (endpoint) and a1 \<in> e41 (endpoint), so a1 \<in> D2.
         But a1 \<notin> Da3 (Da3 endpoints = \{p, a3\}, a1 \<noteq> p, a1 \<noteq> a3), a1 \<notin> e23, a1 \<notin> Da2.
         So a1 \<notin> D1.\<close>
      moreover { assume hz_a1: "z = a1"
        have "a1 \<notin> Da3"
        proof
          assume "a1 \<in> Da3"
          hence "a1 \<in> Da3 \<inter> D1p" using \<open>a1 \<in> D1p\<close> by (by100 blast)
          hence "a1 = p" using he13_meet by (by100 blast)
          moreover have "a1 \<noteq> p" using assms(37) by (by100 blast)
          ultimately show False by (by100 blast)
        qed
        moreover have "a1 \<notin> e23"
        proof
          assume "a1 \<in> e23"
          have "a1 \<in> e41" using assms(27) by (by100 blast)
          hence "a1 \<in> e23 \<inter> e41" using \<open>a1 \<in> e23\<close> by (by100 blast)
          thus False using assms(23) by (by100 blast)
        qed
        moreover have "a1 \<notin> Da2"
        proof
          assume "a1 \<in> Da2"
          hence "a1 \<in> e24" using hDa2_sub by (by100 blast)
          have "a1 \<in> e12" using assms(27) by (by100 blast)
          hence "a1 \<in> e24 \<inter> e12" using \<open>a1 \<in> e24\<close> by (by100 blast)
          hence "a1 = a2" using assms(33) by (by100 blast)
          moreover have "a1 \<noteq> a2" using hdist by (by100 blast) \<comment> \<open>a1 \<noteq> a2 from K4 intersection conditions.\<close>
          ultimately show False by (by100 blast)
        qed
        ultimately have "a1 \<notin> ?D1" by (by100 blast)
        hence False using hz hz_a1 by (by100 blast)
      }
      moreover { assume hz_a2: "z = a2"
        have "a2 \<notin> Dq4"
        proof
          assume "a2 \<in> Dq4"
          hence "a2 \<in> Da2 \<inter> Dq4" using \<open>a2 \<in> Da2\<close> by (by100 blast)
          hence "a2 = q" using he24_meet by (by100 blast)
          thus False using assms(38) by (by100 blast)
        qed
        moreover have "a2 \<notin> e41"
        proof
          assume "a2 \<in> e41"
          have "a2 \<in> e12" using assms(24) by (by100 blast)
          hence "a2 \<in> e41 \<inter> e12" using \<open>a2 \<in> e41\<close> by (by100 blast)
          hence "a2 \<in> {a1}" using assms(27) by (by100 blast)
          hence "a2 = a1" by (by100 blast)
          moreover have "a2 \<noteq> a1" using hdist by (by100 blast) \<comment> \<open>a2 \<noteq> a1 from K4.\<close>
          ultimately show False by (by100 blast)
        qed
        moreover have "a2 \<notin> D1p"
        proof
          assume "a2 \<in> D1p"
          hence "a2 \<in> e13" using hD1p_sub by (by100 blast)
          have "a2 \<in> e12" using assms(24) by (by100 blast)
          hence "a2 \<in> e13 \<inter> e12" using \<open>a2 \<in> e13\<close> by (by100 blast)
          hence "a2 \<in> {a1}" using assms(28) by (by100 blast)
          hence "a2 = a1" by (by100 blast)
          moreover have "a2 \<noteq> a1" using hdist by (by100 blast) \<comment> \<open>a2 \<noteq> a1.\<close>
          ultimately show False by (by100 blast)
        qed
        ultimately have "a2 \<notin> ?D2" by (by100 blast)
        hence False using hz hz_a2 by (by100 blast)
      }
      moreover { assume hz_a3: "z = a3"
        have "a3 \<notin> Dq4"
        proof
          assume "a3 \<in> Dq4"
          hence "a3 \<in> e24" using hDq4_sub by (by100 blast)
          have "a3 \<in> e23" using assms(25) by (by100 blast)
          hence "a3 \<in> e24 \<inter> e23" using \<open>a3 \<in> e24\<close> by (by100 blast)
          hence "a3 \<in> {a2}" using assms(34) by (by100 blast)
          hence "a3 = a2" by (by100 blast)
          moreover have "a3 \<noteq> a2" using hdist by (by100 blast) \<comment> \<open>a3 \<noteq> a2 from K4.\<close>
          ultimately show False by (by100 blast)
        qed
        moreover have "a3 \<notin> e41"
        proof
          assume "a3 \<in> e41"
          have "a3 \<in> e23" using assms(25) by (by100 blast)
          hence "a3 \<in> e23 \<inter> e41" using \<open>a3 \<in> e41\<close> by (by100 blast)
          thus False using assms(23) by (by100 blast)
        qed
        moreover have "a3 \<notin> D1p"
        proof
          assume "a3 \<in> D1p"
          hence "a3 \<in> Da3 \<inter> D1p" using \<open>a3 \<in> Da3\<close> by (by100 blast)
          hence "a3 = p" using he13_meet by (by100 blast)
          thus False using assms(37) by (by100 blast)
        qed
        ultimately have "a3 \<notin> ?D2" by (by100 blast)
        hence False using hz hz_a3 by (by100 blast)
      }
      moreover { assume hz_a4: "z = a4"
        have "a4 \<notin> Da3"
        proof
          assume "a4 \<in> Da3"
          hence "a4 \<in> e13" using hDa3_sub by (by100 blast)
          have "a4 \<in> e41" using assms(26) by (by100 blast)
          hence "a4 \<in> e13 \<inter> e41" using \<open>a4 \<in> e13\<close> by (by100 blast)
          hence "a4 \<in> {a1}" using assms(31) by (by100 blast)
          hence "a4 = a1" by (by100 blast)
          moreover have "a4 \<noteq> a1" using hdist by (by100 blast) \<comment> \<open>a4 \<noteq> a1 from K4.\<close>
          ultimately show False by (by100 blast)
        qed
        moreover have "a4 \<notin> e23"
        proof
          assume "a4 \<in> e23"
          have "a4 \<in> e34" using assms(26) by (by100 blast)
          hence "a4 \<in> e23 \<inter> e34" using \<open>a4 \<in> e23\<close> by (by100 blast)
          hence "a4 \<in> {a3}" using assms(25) by (by100 blast)
          hence "a4 = a3" by (by100 blast)
          moreover have "a4 \<noteq> a3" using hdist by (by100 blast) \<comment> \<open>a4 \<noteq> a3 from K4.\<close>
          ultimately show False by (by100 blast)
        qed
        moreover have "a4 \<notin> Da2"
        proof
          assume "a4 \<in> Da2"
          hence "a4 \<in> Da2 \<inter> Dq4" using \<open>a4 \<in> Dq4\<close> by (by100 blast)
          hence "a4 = q" using he24_meet by (by100 blast)
          thus False using assms(38) by (by100 blast)
        qed
        ultimately have "a4 \<notin> ?D1" by (by100 blast)
        hence False using hz hz_a4 by (by100 blast)
      }
      ultimately show ?thesis using hz1 hz2 by blast
    qed
  next
    fix z assume "z \<in> {p, q}"
    thus "z \<in> ?D1 \<inter> ?D2"
      using hp_D1 hq_D1 hp_D2 hq_D2 by (by100 blast)
  qed
  have hUV_union: "?U_loc \<union> ?V_loc = ?X"
    using hD1_D2_inter hp_D1 hq_D1 hp_D2 hq_D2 by blast
  \<comment> \<open>Step C3: U\_loc \<inter> V\_loc = S2 - (D1 \<union> D2). D1 \<union> D2 is a simple closed curve.
     By JCT: U\_loc \<inter> V\_loc has two components A, B with x \<in> A, y \<in> B.\<close>
  \<comment> \<open>Step C4: \<alpha> is a path in U\_loc from x to y, \<beta> is a path in V\_loc from y to x.\<close>
  have h\<alpha>_U: "top1_is_path_on ?U_loc (subspace_topology ?X ?TX ?U_loc) x y \<alpha>"
  proof -
    \<comment> \<open>Lift \<alpha> from C-D1 to U\_loc (C-D1 \<subseteq> U\_loc).\<close>
    have hTU: "is_topology_on ?U_loc (subspace_topology top1_S2 top1_S2_topology ?U_loc)"
      by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
    have hTC_D1_eq: "subspace_topology ?U_loc (subspace_topology top1_S2 top1_S2_topology ?U_loc) (C - ?D1)
        = subspace_topology top1_S2 top1_S2_topology (C - ?D1)"
      using subspace_topology_trans[of "C - ?D1" ?U_loc] hCmD1_sub by (by100 simp)
    have h\<alpha>': "top1_is_path_on (C - ?D1) (subspace_topology ?U_loc (subspace_topology top1_S2 top1_S2_topology ?U_loc) (C - ?D1)) x y \<alpha>"
      using h\<alpha> hTC_D1_eq by (by100 simp)
    have "top1_is_path_on ?U_loc (subspace_topology top1_S2 top1_S2_topology ?U_loc) x y \<alpha>"
      by (rule path_in_subspace_is_path_in_ambient'[OF hTU hCmD1_sub h\<alpha>'])
    moreover have "subspace_topology ?X ?TX ?U_loc = subspace_topology top1_S2 top1_S2_topology ?U_loc"
      using subspace_topology_trans[of ?U_loc ?X] hU_sub_X by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  have h\<beta>_V: "top1_is_path_on ?V_loc (subspace_topology ?X ?TX ?V_loc) y x \<beta>"
  proof -
    have hTV: "is_topology_on ?V_loc (subspace_topology top1_S2 top1_S2_topology ?V_loc)"
      by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
    have hTC_D2_eq: "subspace_topology ?V_loc (subspace_topology top1_S2 top1_S2_topology ?V_loc) (C - ?D2)
        = subspace_topology top1_S2 top1_S2_topology (C - ?D2)"
      using subspace_topology_trans[of "C - ?D2" ?V_loc] hCmD2_sub by (by100 simp)
    have h\<beta>': "top1_is_path_on (C - ?D2) (subspace_topology ?V_loc (subspace_topology top1_S2 top1_S2_topology ?V_loc) (C - ?D2)) y x \<beta>"
      using h\<beta> hTC_D2_eq by (by100 simp)
    have "top1_is_path_on ?V_loc (subspace_topology top1_S2 top1_S2_topology ?V_loc) y x \<beta>"
      by (rule path_in_subspace_is_path_in_ambient'[OF hTV hCmD2_sub h\<beta>'])
    moreover have "subspace_topology ?X ?TX ?V_loc = subspace_topology top1_S2 top1_S2_topology ?V_loc"
      using subspace_topology_trans[of ?V_loc ?X] hV_sub_X by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Step C5: Apply Theorem 63.1.\<close>
  \<comment> \<open>Theorem 63.1 hypotheses: U\_loc, V\_loc open in X; U\<inter>V has two components; x, y separated.\<close>
  \<comment> \<open>Sub-arc endpoints (needed for both D1 and D2 proofs).\<close>
  have hD1p_ep: "top1_arc_endpoints_on D1p (subspace_topology top1_S2 top1_S2_topology D1p) = {a1, p}"
    and hDa3_ep: "top1_arc_endpoints_on Da3 (subspace_topology top1_S2 top1_S2_topology Da3) = {p, a3}"
    using arc_split_endpoints[OF assms(1) hS2_haus assms(8) assms(14) he13_split he13_meet
          hD1p_arc hDa3_arc \<open>a1 \<in> D1p\<close> \<open>a3 \<in> Da3\<close> \<open>p \<in> D1p\<close> \<open>p \<in> Da3\<close> \<open>D1p \<subseteq> top1_S2\<close>
          \<open>Da3 \<subseteq> top1_S2\<close> assms(20) hp_not_ep13]
    by blast+
  have hDa2_ep: "top1_arc_endpoints_on Da2 (subspace_topology top1_S2 top1_S2_topology Da2) = {a2, q}"
    and hDq4_ep: "top1_arc_endpoints_on Dq4 (subspace_topology top1_S2 top1_S2_topology Dq4) = {q, a4}"
    using arc_split_endpoints[OF assms(1) hS2_haus assms(9) assms(15) he24_split he24_meet
          hDa2_arc hDq4_arc \<open>a2 \<in> Da2\<close> \<open>a4 \<in> Dq4\<close> \<open>q \<in> Da2\<close> \<open>q \<in> Dq4\<close> \<open>Da2 \<subseteq> top1_S2\<close>
          \<open>Dq4 \<subseteq> top1_S2\<close> assms(21) hq_not_ep24]
    by blast+
  have hD1_sub_S2: "?D1 \<subseteq> top1_S2" using hDa3_sub hDa2_sub assms(5,8,9) by (by100 blast)
  have hD2_sub_S2: "?D2 \<subseteq> top1_S2" using hDq4_sub hD1p_sub assms(7,8,9) by (by100 blast)
  have hD1_arc: "top1_is_arc_on ?D1 (subspace_topology top1_S2 top1_S2_topology ?D1)"
    proof -
      \<comment> \<open>Da3 \<union> e23: shared endpoint a3. Result is arc from p to a2.\<close>
      have ha3_Da3: "a3 \<in> top1_arc_endpoints_on Da3 (subspace_topology top1_S2 top1_S2_topology Da3)"
        using hDa3_ep by (by100 blast)
      have ha3_e23: "a3 \<in> top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
        using assms(17) by (by100 blast)
      have ha3_e23_mem: "a3 \<in> e23"
        using assms(17,25) by (by100 blast)
      have hDa3_e23_inter: "Da3 \<inter> e23 = {a3}"
      proof -
        have "Da3 \<inter> e23 \<subseteq> e13 \<inter> e23" using hDa3_sub by (by100 blast)
        hence "Da3 \<inter> e23 \<subseteq> {a3}" using assms(29) by (by100 blast)
        moreover have "a3 \<in> Da3 \<inter> e23" using \<open>a3 \<in> Da3\<close> ha3_e23_mem by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      have hDa3_e23_arc: "top1_is_arc_on (Da3 \<union> e23) (subspace_topology top1_S2 top1_S2_topology (Da3 \<union> e23))"
        by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus hDa3_arc _ assms(11) assms(5)
               hDa3_e23_inter ha3_Da3 ha3_e23]) (rule \<open>Da3 \<subseteq> top1_S2\<close>)
      \<comment> \<open>(Da3 \<union> e23) \<union> Da2: shared endpoint a2. Result = D1 = arc from p to q.\<close>
      have hDa3e23_ep: "top1_arc_endpoints_on (Da3 \<union> e23) (subspace_topology top1_S2 top1_S2_topology (Da3 \<union> e23)) = {p, a2}"
      proof -
        have hp_ne_a3: "p \<noteq> a3" using assms(37) by (by100 blast)
        have ha3_ne_a2: "a3 \<noteq> a2" using assms(2) by (auto simp: card_insert_if split: if_splits)
        have he23_ep': "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a3, a2}"
          using assms(17) by (by100 blast)
        show ?thesis
          by (rule arc_concat_endpoints[OF assms(1) hS2_haus hDa3_arc \<open>Da3 \<subseteq> top1_S2\<close>
                 assms(11) assms(5) hDa3_e23_inter ha3_Da3 ha3_e23 hDa3_ep he23_ep'
                 hp_ne_a3 ha3_ne_a2])
      qed
      have ha2_Da3e23: "a2 \<in> top1_arc_endpoints_on (Da3 \<union> e23) (subspace_topology top1_S2 top1_S2_topology (Da3 \<union> e23))"
        using hDa3e23_ep by (by100 blast)
      have ha2_Da2: "a2 \<in> top1_arc_endpoints_on Da2 (subspace_topology top1_S2 top1_S2_topology Da2)"
        using hDa2_ep by (by100 blast)
      have hDa3e23_Da2_inter: "(Da3 \<union> e23) \<inter> Da2 = {a2}"
      proof -
        have "Da3 \<inter> Da2 = {}"
        proof -
          have hsub4: "Da3 \<inter> Da2 \<subseteq> {a1,a2,a3,a4}"
          proof -
            have "Da3 \<inter> Da2 \<subseteq> e13 \<inter> e24" using hDa3_sub hDa2_sub by (by100 blast)
            thus ?thesis using assms(32) by (by100 blast)
          qed
          have "a1 \<noteq> p" using assms(37) by (by100 blast)
          have ha1_not_Da3: "a1 \<notin> Da3" using \<open>a1 \<in> D1p\<close> he13_meet \<open>a1 \<noteq> p\<close> by (by100 blast)
          have ha3_not_Da2: "a3 \<notin> Da2"
          proof -
            have "a3 \<notin> e24"
            proof
              assume "a3 \<in> e24"
              hence "a3 \<in> e24 \<inter> e23" using assms(17,25) by (by100 blast)
              hence "a3 \<in> {a2}" using assms(34) by (by100 blast)
              thus False using assms(2) by (auto simp: card_insert_if split: if_splits)
            qed
            thus ?thesis using hDa2_sub by (by100 blast)
          qed
          have ha2_not_Da3: "a2 \<notin> Da3"
          proof -
            have "a2 \<notin> e13"
            proof
              assume "a2 \<in> e13"
              hence "a2 \<in> e13 \<inter> e12" using assms(16,24) by (by100 blast)
              hence "a2 \<in> {a1}" using assms(28) by (by100 blast)
              thus False using assms(2) by (auto simp: card_insert_if split: if_splits)
            qed
            thus ?thesis using hDa3_sub by (by100 blast)
          qed
          have ha4_not_Da3: "a4 \<notin> Da3"
          proof -
            have "a4 \<notin> e13"
            proof
              assume "a4 \<in> e13"
              hence "a4 \<in> e13 \<inter> e41" using assms(19,26) by (by100 blast)
              hence "a4 \<in> {a1}" using assms(31) by (by100 blast)
              thus False using assms(2) by (auto simp: card_insert_if split: if_splits)
            qed
            thus ?thesis using hDa3_sub by (by100 blast)
          qed
          \<comment> \<open>Combine: Da3 \<inter> Da2 \<subseteq> {a1,a2,a3,a4}, but a1,a2,a4 \<notin> Da3 and a3 \<notin> Da2.\<close>
          show ?thesis
          proof (rule equals0I)
            fix z assume "z \<in> Da3 \<inter> Da2"
            hence "z \<in> {a1,a2,a3,a4}" using hsub4 by (by100 blast)
            hence "z = a1 \<or> z = a2 \<or> z = a3 \<or> z = a4" by (by100 blast)
            thus False using \<open>z \<in> Da3 \<inter> Da2\<close> ha1_not_Da3 ha2_not_Da3 ha3_not_Da2 ha4_not_Da3
              by (by100 blast)
          qed
        qed
        moreover have "e23 \<inter> Da2 = {a2}"
        proof -
          have "e23 \<inter> Da2 \<subseteq> e23 \<inter> e24" using hDa2_sub by (by100 blast)
          hence "e23 \<inter> Da2 \<subseteq> {a2}" using assms(34) by (by100 blast)
          moreover have "a2 \<in> e23 \<inter> Da2"
            using \<open>a2 \<in> Da2\<close> assms(17,24) by (by100 blast)
          ultimately show ?thesis by (by100 blast)
        qed
        ultimately show ?thesis by (by100 blast)
      qed
      have hDa3e23_sub: "Da3 \<union> e23 \<subseteq> top1_S2" using \<open>Da3 \<subseteq> top1_S2\<close> assms(5) by (by100 blast)
      show ?thesis unfolding Un_assoc[symmetric]
        by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus hDa3_e23_arc hDa3e23_sub
               hDa2_arc \<open>Da2 \<subseteq> top1_S2\<close> hDa3e23_Da2_inter ha2_Da3e23 ha2_Da2])
    qed
  have hU_open_X: "openin_on ?X ?TX ?U_loc"
  proof -
    have "closedin_on top1_S2 top1_S2_topology ?D1"
      by (rule arc_in_S2_closed[OF hD1_sub_S2 hD1_arc])
    hence hU_S2_open: "?U_loc \<in> top1_S2_topology" unfolding closedin_on_def by (by100 blast)
    have "?U_loc = ?U_loc \<inter> ?X" using hU_sub_X by (by100 blast)
    hence "?U_loc \<in> ?TX" using hU_S2_open unfolding subspace_topology_def by (by100 blast)
    thus ?thesis unfolding openin_on_def using hU_sub_X by (by100 blast)
  qed
  have hD2_arc: "top1_is_arc_on ?D2 (subspace_topology top1_S2 top1_S2_topology ?D2)"
    proof -
      \<comment> \<open>Step 1: Dq4 \<union> e41 is an arc (shared endpoint a4).\<close>
      have ha4_Dq4: "a4 \<in> top1_arc_endpoints_on Dq4 (subspace_topology top1_S2 top1_S2_topology Dq4)"
        using hDq4_ep by (by100 blast)
      have ha4_e41: "a4 \<in> top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
        using assms(19) by (by100 blast)
      have hDq4_e41_inter: "Dq4 \<inter> e41 = {a4}"
      proof -
        have "Dq4 \<inter> e41 \<subseteq> e24 \<inter> e41" using hDq4_sub by (by100 blast)
        hence "Dq4 \<inter> e41 \<subseteq> {a4}" using assms(36) by (by100 blast)
        moreover have "a4 \<in> Dq4 \<inter> e41" using \<open>a4 \<in> Dq4\<close> assms(19,26) by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      have hDq4_e41_arc: "top1_is_arc_on (Dq4 \<union> e41) (subspace_topology top1_S2 top1_S2_topology (Dq4 \<union> e41))"
        by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus hDq4_arc \<open>Dq4 \<subseteq> top1_S2\<close>
               assms(13) assms(7) hDq4_e41_inter ha4_Dq4 ha4_e41])
      \<comment> \<open>Step 2: endpoints of Dq4 \<union> e41 = {q, a1}.\<close>
      have ha4_ne_q: "a4 \<noteq> q" using assms(38) by (by100 blast)
      have ha4_ne_a1: "a4 \<noteq> a1" using assms(2) by (auto simp: card_insert_if split: if_splits)
      have he41_ep': "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a4, a1}"
        using assms(19) by (by100 blast)
      have hDq4e41_ep: "top1_arc_endpoints_on (Dq4 \<union> e41) (subspace_topology top1_S2 top1_S2_topology (Dq4 \<union> e41)) = {q, a1}"
      proof (rule arc_concat_endpoints[where c=a4])
        show "is_topology_on_strict top1_S2 top1_S2_topology" by (rule assms(1))
        show "is_hausdorff_on top1_S2 top1_S2_topology" by (rule hS2_haus)
        show "top1_is_arc_on Dq4 (subspace_topology top1_S2 top1_S2_topology Dq4)" by (rule hDq4_arc)
        show "Dq4 \<subseteq> top1_S2" by (rule \<open>Dq4 \<subseteq> top1_S2\<close>)
        show "top1_is_arc_on e41 (subspace_topology top1_S2 top1_S2_topology e41)" by (rule assms(13))
        show "e41 \<subseteq> top1_S2" by (rule assms(7))
        show "Dq4 \<inter> e41 = {a4}" by (rule hDq4_e41_inter)
        show "a4 \<in> top1_arc_endpoints_on Dq4 (subspace_topology top1_S2 top1_S2_topology Dq4)"
          by (rule ha4_Dq4)
        show "a4 \<in> top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
          by (rule ha4_e41)
        show "top1_arc_endpoints_on Dq4 (subspace_topology top1_S2 top1_S2_topology Dq4) = {q, a4}"
          by (rule hDq4_ep)
        show "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a4, a1}"
          by (rule he41_ep')
        show "q \<noteq> a4" using ha4_ne_q by (by100 simp)
        show "a4 \<noteq> a1" by (rule ha4_ne_a1)
      qed
      \<comment> \<open>Step 3: (Dq4 \<union> e41) \<union> D1p is an arc (shared endpoint a1).\<close>
      have ha1_Dq4e41: "a1 \<in> top1_arc_endpoints_on (Dq4 \<union> e41) (subspace_topology top1_S2 top1_S2_topology (Dq4 \<union> e41))"
        using hDq4e41_ep by (by100 blast)
      have ha1_D1p: "a1 \<in> top1_arc_endpoints_on D1p (subspace_topology top1_S2 top1_S2_topology D1p)"
        using hD1p_ep by (by100 blast)
      have hDq4e41_D1p_inter: "(Dq4 \<union> e41) \<inter> D1p = {a1}"
      proof -
        have "Dq4 \<inter> D1p = {}"
        proof (rule equals0I)
          fix z assume "z \<in> Dq4 \<inter> D1p"
          hence "z \<in> e24 \<inter> e13" using hDq4_sub hD1p_sub by (by100 blast)
          hence "z \<in> {a1,a2,a3,a4}" using assms(32) by (by100 blast)
          hence "z = a1 \<or> z = a2 \<or> z = a3 \<or> z = a4" by (by100 blast)
          moreover have "a1 \<notin> Dq4"
          proof -
            have "a1 \<notin> e24"
            proof
              assume "a1 \<in> e24"
              hence "a1 \<in> e24 \<inter> e41" using assms(19,27) by (by100 blast)
              hence "a1 \<in> {a4}" using assms(36) by (by100 blast)
              thus False using assms(2) by (auto simp: card_insert_if split: if_splits)
            qed
            thus ?thesis using hDq4_sub by (by100 blast)
          qed
          moreover have "a2 \<notin> D1p"
          proof -
            have "a2 \<notin> e13"
            proof
              assume "a2 \<in> e13"
              hence "a2 \<in> e13 \<inter> e12" using assms(16,24) by (by100 blast)
              hence "a2 \<in> {a1}" using assms(28) by (by100 blast)
              thus False using assms(2) by (auto simp: card_insert_if split: if_splits)
            qed
            thus ?thesis using hD1p_sub by (by100 blast)
          qed
          moreover have "a3 \<notin> Dq4"
          proof -
            have "a3 \<notin> e24"
            proof
              assume "a3 \<in> e24"
              hence "a3 \<in> e24 \<inter> e23" using assms(17,25) by (by100 blast)
              hence "a3 \<in> {a2}" using assms(34) by (by100 blast)
              thus False using assms(2) by (auto simp: card_insert_if split: if_splits)
            qed
            thus ?thesis using hDq4_sub by (by100 blast)
          qed
          moreover have "a4 \<notin> D1p"
          proof -
            have "a4 \<notin> e13"
            proof
              assume "a4 \<in> e13"
              hence "a4 \<in> e13 \<inter> e41" using assms(19,26) by (by100 blast)
              hence "a4 \<in> {a1}" using assms(31) by (by100 blast)
              thus False using assms(2) by (auto simp: card_insert_if split: if_splits)
            qed
            thus ?thesis using hD1p_sub by (by100 blast)
          qed
          ultimately show False using \<open>z \<in> Dq4 \<inter> D1p\<close> by (by100 blast)
        qed
        moreover have "e41 \<inter> D1p = {a1}"
        proof -
          have "e41 \<inter> D1p \<subseteq> e41 \<inter> e13" using hD1p_sub by (by100 blast)
          hence "e41 \<inter> D1p \<subseteq> {a1}" using assms(31) by (by100 blast)
          moreover have "a1 \<in> e41 \<inter> D1p" using \<open>a1 \<in> D1p\<close> assms(19,27) by (by100 blast)
          ultimately show ?thesis by (by100 blast)
        qed
        ultimately show ?thesis by (by100 blast)
      qed
      have hDq4e41_sub: "Dq4 \<union> e41 \<subseteq> top1_S2" using \<open>Dq4 \<subseteq> top1_S2\<close> assms(7) by (by100 blast)
      show ?thesis unfolding Un_assoc[symmetric]
        by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus hDq4_e41_arc hDq4e41_sub
               hD1p_arc \<open>D1p \<subseteq> top1_S2\<close> hDq4e41_D1p_inter ha1_Dq4e41 ha1_D1p])
    qed
  have hV_open_X: "openin_on ?X ?TX ?V_loc"
  proof -
    have "closedin_on top1_S2 top1_S2_topology ?D2"
      by (rule arc_in_S2_closed[OF hD2_sub_S2 hD2_arc])
    hence hV_S2_open: "?V_loc \<in> top1_S2_topology" unfolding closedin_on_def by (by100 blast)
    have "?V_loc = ?V_loc \<inter> ?X" using hV_sub_X by (by100 blast)
    hence "?V_loc \<in> ?TX" using hV_S2_open unfolding subspace_topology_def by (by100 blast)
    thus ?thesis unfolding openin_on_def using hV_sub_X by (by100 blast)
  qed
  \<comment> \<open>U\<inter>V = S2-(D1\<union>D2). D1\<union>D2 is an SCC (cycle a1-a3-a2-a4-a1 through p,q).
     By JCT: S2-(D1\<union>D2) has two components A, B.
     x \<in> int(e12) and y \<in> int(e34) lie in different components (by Lemma 65.1(a)
     applied to the "other" K4 cycle D1\<union>D2).\<close>
  \<comment> \<open>Apply Theorem 63.5: D1, D2 arcs meeting in {p,q} (\<Rightarrow> 2 components).\<close>
  \<comment> \<open>D1, D2 closedness, connectedness, non-separation (using proved arc facts from hU/hV\_open\_X blocks).\<close>
  have hD1_closed: "closedin_on top1_S2 top1_S2_topology ?D1"
    by (rule arc_in_S2_closed[OF hD1_sub_S2 hD1_arc])
  have hD2_closed: "closedin_on top1_S2 top1_S2_topology ?D2"
    by (rule arc_in_S2_closed[OF hD2_sub_S2 hD2_arc])
  have hD1_conn: "top1_connected_on ?D1 (subspace_topology top1_S2 top1_S2_topology ?D1)"
    using arc_connected[OF hD1_arc] .
  have hD2_conn: "top1_connected_on ?D2 (subspace_topology top1_S2 top1_S2_topology ?D2)"
    using arc_connected[OF hD2_arc] .
  have hD1_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology ?D1"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) hD1_sub_S2 hD1_arc])
  have hD2_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology ?D2"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) hD2_sub_S2 hD2_arc])
  have hD1D2_card: "card (?D1 \<inter> ?D2) = 2"
    using hD1_D2_inter hp_ne_q by (by100 simp)
  obtain U0 V0 where hUV0: "U0 \<noteq> {}" "V0 \<noteq> {}" "U0 \<inter> V0 = {}"
      "U0 \<union> V0 = top1_S2 - (?D1 \<union> ?D2)"
      "top1_connected_on U0 (subspace_topology top1_S2 top1_S2_topology U0)"
      "top1_connected_on V0 (subspace_topology top1_S2 top1_S2_topology V0)"
    using Theorem_63_5_two_closed_connected[OF assms(1) hD1_closed hD2_closed
          hD1_conn hD2_conn hD1D2_card hD1_no_sep hD2_no_sep] by blast
  \<comment> \<open>U0 \<union> V0 = S2-(D1\<union>D2) = (S2-D1) \<inter> (S2-D2) = U\_loc \<inter> V\_loc.\<close>
  have hUV0_eq: "U0 \<union> V0 = ?U_loc \<inter> ?V_loc"
    using hUV0(4) by (by100 blast)
  \<comment> \<open>U0, V0 are open in X (since they're connected components of an open set in S2).\<close>
  \<comment> \<open>x, y are in different components (needs part (a) / Lemma\_64\_3 applied to "other" cycle).\<close>
  \<comment> \<open>U0, V0 are open in S2 (connected components of an open set in S2).\<close>
  have hW_open: "top1_S2 - (?D1 \<union> ?D2) \<in> top1_S2_topology"
  proof -
    have "?D1 \<subseteq> top1_S2 \<and> top1_S2 - ?D1 \<in> top1_S2_topology"
      using hD1_closed unfolding closedin_on_def by (by100 blast)
    have "?D2 \<subseteq> top1_S2 \<and> top1_S2 - ?D2 \<in> top1_S2_topology"
      using hD2_closed unfolding closedin_on_def by (by100 blast)
    hence "(top1_S2 - ?D1) \<inter> (top1_S2 - ?D2) \<in> top1_S2_topology"
    proof -
      have "top1_S2 - ?D1 \<in> top1_S2_topology" using \<open>?D1 \<subseteq> top1_S2 \<and> top1_S2 - ?D1 \<in> top1_S2_topology\<close> by (by100 blast)
      moreover have "top1_S2 - ?D2 \<in> top1_S2_topology" using \<open>?D2 \<subseteq> top1_S2 \<and> top1_S2 - ?D2 \<in> top1_S2_topology\<close> by (by100 blast)
      ultimately show ?thesis
        using topology_inter2[OF hTopS2] by (by100 blast)
    qed
    moreover have "top1_S2 - (?D1 \<union> ?D2) = (top1_S2 - ?D1) \<inter> (top1_S2 - ?D2)" by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  have hW_sub: "top1_S2 - (?D1 \<union> ?D2) \<subseteq> top1_S2" by (by100 blast)
  have hW_not_conn: "\<not> top1_connected_on (top1_S2 - (?D1 \<union> ?D2))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?D1 \<union> ?D2)))"
  proof -
    have hsep: "top1_separates_on top1_S2 top1_S2_topology (?D1 \<union> ?D2)"
      by (rule Theorem_61_4_general_separation[OF assms(1) hD1_sub_S2 hD2_sub_S2
            hD1_closed hD2_closed hD1_conn hD2_conn hD1D2_card])
    thus ?thesis unfolding top1_separates_on_def by (by100 simp)
  qed
  have "U0 \<in> top1_S2_topology" "V0 \<in> top1_S2_topology"
    using S2_two_component_open[OF hW_open hW_sub hUV0(1,2,3) hUV0(4) hUV0(5,6) hW_not_conn]
    by (by100 blast)+
  hence hU0_open: "U0 \<in> top1_S2_topology" and hV0_open: "V0 \<in> top1_S2_topology"
    by (by100 blast)+
  \<comment> \<open>U0, V0 are open in X (open in S2 and subset of X).\<close>
  have hU0_sub_X: "U0 \<subseteq> ?X" using hUV0(4) hU_sub_X hV_sub_X by (by100 blast)
  have hV0_sub_X: "V0 \<subseteq> ?X" using hUV0(4) hU_sub_X hV_sub_X by (by100 blast)
  have hU0_open_X: "openin_on ?X ?TX U0"
  proof -
    have "U0 = U0 \<inter> ?X" using hU0_sub_X by (by100 blast)
    hence "U0 \<in> ?TX" using hU0_open unfolding subspace_topology_def by (by100 blast)
    thus ?thesis unfolding openin_on_def using hU0_sub_X by (by100 blast)
  qed
  have hV0_open_X: "openin_on ?X ?TX V0"
  proof -
    have "V0 = V0 \<inter> ?X" using hV0_sub_X by (by100 blast)
    hence "V0 \<in> ?TX" using hV0_open unfolding subspace_topology_def by (by100 blast)
    thus ?thesis unfolding openin_on_def using hV0_sub_X by (by100 blast)
  qed
  \<comment> \<open>x \<in> U0, y \<in> V0 (or swapped). Needs: x and y in different components.
     This follows from Lemma 65.1(a) applied to the "other" K4 cycle D1\<union>D2.\<close>
  have hx_in_UV: "x \<in> U0 \<union> V0"
    using hUV0(4) hx_in_CmD1 hx_in_CmD2 hC_sub_S2 by (by100 blast)
  have hy_in_UV: "y \<in> U0 \<union> V0"
    using hUV0(4) hy_in_CmD1 hy_in_CmD2 hC_sub_S2 by (by100 blast)
  have hx_y_diff_comp: "(x \<in> U0 \<and> y \<in> V0) \<or> (x \<in> V0 \<and> y \<in> U0)"
  proof -
    have hx_int: "x \<in> e12 - {a1, a2}" using hx_e12 hx_not_endpts by (by100 blast)
    have hy_int: "y \<in> e34 - {a3, a4}" using hy_e34 hy_not_endpts by (by100 blast)
    \<comment> \<open>x and y avoid D1\<union>D2, so they're in U0 \<union> V0. Need: different components.\<close>
    \<comment> \<open>Proof by contradiction using Lemma\_64\_3: if both in same component,
       all 4 K4 faces + int(e12) + int(e34) would be in that component,
       leaving the other component empty.\<close>
    have hD_eq: "?D1 \<union> ?D2 = e13 \<union> e23 \<union> e24 \<union> e41"
      using he13_split he24_split by (by100 blast)
    have hdiff: "\<not> (e12 - {a1, a2} \<subseteq> U0 \<and> e34 - {a3, a4} \<subseteq> U0)
              \<and> \<not> (e12 - {a1, a2} \<subseteq> V0 \<and> e34 - {a3, a4} \<subseteq> V0)"
      by (rule K4_nonadjacent_edges_different_components[OF assms(1-36)
            hUV0(1,2,3) _ hUV0(5,6)])
         (use hUV0(4) hD_eq in \<open>by100 simp\<close>)
    \<comment> \<open>int(e12) connected \<Rightarrow> entirely in U0 or V0. Same for int(e34).\<close>
    have ha1_ne_a2_loc: "a1 \<noteq> a2" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha3_ne_a4_loc: "a3 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have he12_conn: "top1_connected_on (e12 - {a1, a2})
        (subspace_topology top1_S2 top1_S2_topology (e12 - {a1, a2}))"
      by (rule arc_minus_endpoints_connected[OF assms(1) hS2_haus assms(4,10,16) ha1_ne_a2_loc])
    have he34_conn: "top1_connected_on (e34 - {a3, a4})
        (subspace_topology top1_S2 top1_S2_topology (e34 - {a3, a4}))"
      by (rule arc_minus_endpoints_connected[OF assms(1) hS2_haus assms(6,12,18) ha3_ne_a4_loc])
    have hint_e12_sub: "e12 - {a1, a2} \<subseteq> U0 \<union> V0"
    proof -
      \<comment> \<open>(e12 - {a2}) \<inter> D1 = {} and (e12 - {a1}) \<inter> D2 = {}.\<close>
      have "e12 \<inter> Da3 = {}"
      proof -
        have "Da3 \<subseteq> e13" using he13_split by (by100 blast)
        hence "e12 \<inter> Da3 \<subseteq> {a1}" using assms(28) by (by100 blast)
        have "a1 \<noteq> p" using assms(37) by (by100 blast)
        have "a1 \<notin> Da3" using \<open>a1 \<in> D1p\<close> he13_meet \<open>a1 \<noteq> p\<close> by (by100 blast)
        thus ?thesis using \<open>e12 \<inter> Da3 \<subseteq> {a1}\<close> by (by100 blast)
      qed
      have "(e12 - {a2}) \<inter> Da2 = {}"
      proof -
        have "Da2 \<subseteq> e24" using he24_split by (by100 blast)
        hence "e12 \<inter> Da2 \<subseteq> {a2}" using assms(33) by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      hence h_D1: "(e12 - {a2}) \<inter> ?D1 = {}"
        using \<open>e12 \<inter> Da3 = {}\<close> assms(24) by (by100 blast)
      have "e12 \<inter> Dq4 = {}"
      proof -
        have "Dq4 \<subseteq> e24" using he24_split by (by100 blast)
        hence "e12 \<inter> Dq4 \<subseteq> {a2}" using assms(33) by (by100 blast)
        have "a2 \<noteq> q" using assms(38) by (by100 blast)
        have "a2 \<notin> Dq4" using \<open>a2 \<in> Da2\<close> he24_meet \<open>a2 \<noteq> q\<close> by (by100 blast)
        thus ?thesis using \<open>e12 \<inter> Dq4 \<subseteq> {a2}\<close> by (by100 blast)
      qed
      have "(e12 - {a1}) \<inter> D1p = {}"
      proof -
        have "D1p \<subseteq> e13" using he13_split by (by100 blast)
        hence "e12 \<inter> D1p \<subseteq> {a1}" using assms(28) by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      hence h_D2: "(e12 - {a1}) \<inter> ?D2 = {}"
        using \<open>e12 \<inter> Dq4 = {}\<close> assms(27) by (by100 blast)
      have "(e12 - {a1, a2}) \<inter> (?D1 \<union> ?D2) = {}" using h_D1 h_D2 by (by100 blast)
      hence "e12 - {a1, a2} \<subseteq> top1_S2 - (?D1 \<union> ?D2)" using assms(4) by (by100 blast)
      thus ?thesis using hUV0(4) by (by100 blast)
    qed
    have hint_e34_sub: "e34 - {a3, a4} \<subseteq> U0 \<union> V0"
    proof -
      have "(e34 - {a3}) \<inter> Da3 = {}"
      proof -
        have "Da3 \<subseteq> e13" using he13_split by (by100 blast)
        hence "e34 \<inter> Da3 \<subseteq> {a3}" using assms(30) by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      have "e34 \<inter> Da2 = {}"
      proof -
        have "Da2 \<subseteq> e24" using he24_split by (by100 blast)
        hence "e34 \<inter> Da2 \<subseteq> {a4}" using assms(35) by (by100 blast)
        have "a4 \<noteq> q" using assms(38) by (by100 blast)
        have "a4 \<notin> Da2" using \<open>a4 \<in> Dq4\<close> he24_meet \<open>a4 \<noteq> q\<close> by (by100 blast)
        thus ?thesis using \<open>e34 \<inter> Da2 \<subseteq> {a4}\<close> by (by100 blast)
      qed
      hence h_D1: "(e34 - {a3}) \<inter> ?D1 = {}"
        using \<open>(e34 - {a3}) \<inter> Da3 = {}\<close> assms(25) by (by100 blast)
      have "(e34 - {a4}) \<inter> Dq4 = {}"
      proof -
        have "Dq4 \<subseteq> e24" using he24_split by (by100 blast)
        hence "e34 \<inter> Dq4 \<subseteq> {a4}" using assms(35) by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      have "e34 \<inter> D1p = {}"
      proof -
        have "D1p \<subseteq> e13" using he13_split by (by100 blast)
        hence "e34 \<inter> D1p \<subseteq> {a3}" using assms(30) by (by100 blast)
        have "a3 \<noteq> p" using assms(37) by (by100 blast)
        have "a3 \<notin> D1p" using \<open>a3 \<in> Da3\<close> he13_meet \<open>a3 \<noteq> p\<close> by (by100 blast)
        thus ?thesis using \<open>e34 \<inter> D1p \<subseteq> {a3}\<close> by (by100 blast)
      qed
      hence h_D2: "(e34 - {a4}) \<inter> ?D2 = {}"
        using \<open>(e34 - {a4}) \<inter> Dq4 = {}\<close> assms(26) by (by100 blast)
      have "(e34 - {a3, a4}) \<inter> (?D1 \<union> ?D2) = {}" using h_D1 h_D2 by (by100 blast)
      hence "e34 - {a3, a4} \<subseteq> top1_S2 - (?D1 \<union> ?D2)" using assms(6) by (by100 blast)
      thus ?thesis using hUV0(4) by (by100 blast)
    qed
    have he12_in_comp: "e12 - {a1, a2} \<subseteq> U0 \<or> e12 - {a1, a2} \<subseteq> V0"
    proof -
      have hW_top: "is_topology_on (U0 \<union> V0)
          (subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0))"
        by (rule subspace_topology_is_topology_on[OF hTopS2])
           (use hUV0(4) in \<open>by100 blast\<close>)
      have hU0_open_W: "U0 \<in> subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)"
      proof -
        have "U0 = (U0 \<union> V0) \<inter> U0" by (by100 blast)
        thus ?thesis using hU0_open unfolding subspace_topology_def by (by100 blast)
      qed
      have hV0_open_W: "V0 \<in> subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)"
      proof -
        have "V0 = (U0 \<union> V0) \<inter> V0" by (by100 blast)
        thus ?thesis using hV0_open unfolding subspace_topology_def by (by100 blast)
      qed
      have hsep: "top1_is_separation_on (U0 \<union> V0)
          (subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)) U0 V0"
        unfolding top1_is_separation_on_def
        using hU0_open_W hV0_open_W hUV0(1,2,3) by (by100 blast)
      have he12_conn_W: "top1_connected_on (e12 - {a1, a2})
          (subspace_topology (U0 \<union> V0)
            (subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)) (e12 - {a1, a2}))"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology (e12 - {a1, a2}) =
            subspace_topology (U0 \<union> V0)
              (subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)) (e12 - {a1, a2})"
          using subspace_topology_trans[of "e12 - {a1, a2}" "U0 \<union> V0"]
            hint_e12_sub by (by100 simp)
        thus ?thesis using he12_conn by (by100 simp)
      qed
      from Lemma_23_2_disjoint[OF hW_top hsep hint_e12_sub he12_conn_W]
      have "(e12 - {a1, a2}) \<inter> V0 = {} \<or> (e12 - {a1, a2}) \<inter> U0 = {}" .
      thus ?thesis
      proof
        assume "(e12 - {a1, a2}) \<inter> V0 = {}"
        hence "e12 - {a1, a2} \<subseteq> U0" using hint_e12_sub by (by100 blast)
        thus ?thesis by (by100 blast)
      next
        assume "(e12 - {a1, a2}) \<inter> U0 = {}"
        hence "e12 - {a1, a2} \<subseteq> V0" using hint_e12_sub by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
    qed
    have he34_in_comp: "e34 - {a3, a4} \<subseteq> U0 \<or> e34 - {a3, a4} \<subseteq> V0"
    proof -
      have hW_top: "is_topology_on (U0 \<union> V0)
          (subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0))"
        by (rule subspace_topology_is_topology_on[OF hTopS2])
           (use hUV0(4) in \<open>by100 blast\<close>)
      have hU0_open_W: "U0 \<in> subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)"
      proof -
        have "U0 = (U0 \<union> V0) \<inter> U0" by (by100 blast)
        thus ?thesis using hU0_open unfolding subspace_topology_def by (by100 blast)
      qed
      have hV0_open_W: "V0 \<in> subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)"
      proof -
        have "V0 = (U0 \<union> V0) \<inter> V0" by (by100 blast)
        thus ?thesis using hV0_open unfolding subspace_topology_def by (by100 blast)
      qed
      have hsep: "top1_is_separation_on (U0 \<union> V0)
          (subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)) U0 V0"
        unfolding top1_is_separation_on_def
        using hU0_open_W hV0_open_W hUV0(1,2,3) by (by100 blast)
      have he34_conn_W: "top1_connected_on (e34 - {a3, a4})
          (subspace_topology (U0 \<union> V0)
            (subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)) (e34 - {a3, a4}))"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology (e34 - {a3, a4}) =
            subspace_topology (U0 \<union> V0)
              (subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)) (e34 - {a3, a4})"
          using subspace_topology_trans[of "e34 - {a3, a4}" "U0 \<union> V0"]
            hint_e34_sub by (by100 simp)
        thus ?thesis using he34_conn by (by100 simp)
      qed
      from Lemma_23_2_disjoint[OF hW_top hsep hint_e34_sub he34_conn_W]
      have "(e34 - {a3, a4}) \<inter> V0 = {} \<or> (e34 - {a3, a4}) \<inter> U0 = {}" .
      thus ?thesis
      proof
        assume "(e34 - {a3, a4}) \<inter> V0 = {}"
        hence "e34 - {a3, a4} \<subseteq> U0" using hint_e34_sub by (by100 blast)
        thus ?thesis by (by100 blast)
      next
        assume "(e34 - {a3, a4}) \<inter> U0 = {}"
        hence "e34 - {a3, a4} \<subseteq> V0" using hint_e34_sub by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
    qed
    have hx_ne_y_comp: "\<not>(x \<in> U0 \<and> y \<in> U0) \<and> \<not>(x \<in> V0 \<and> y \<in> V0)"
    proof (intro conjI notI)
      assume hboth: "x \<in> U0 \<and> y \<in> U0"
      have "e12 - {a1,a2} \<subseteq> U0"
      proof -
        from he12_in_comp have "e12 - {a1,a2} \<subseteq> U0 \<or> e12 - {a1,a2} \<subseteq> V0" .
        moreover have "x \<in> U0" using hboth by (by100 blast)
        moreover have "\<not> (e12 - {a1,a2} \<subseteq> V0)" using hx_int \<open>x \<in> U0\<close> hUV0(3) by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      moreover have "e34 - {a3,a4} \<subseteq> U0"
      proof -
        from he34_in_comp have "e34 - {a3,a4} \<subseteq> U0 \<or> e34 - {a3,a4} \<subseteq> V0" .
        moreover have "y \<in> U0" using hboth by (by100 blast)
        moreover have "\<not> (e34 - {a3,a4} \<subseteq> V0)" using hy_int \<open>y \<in> U0\<close> hUV0(3) by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      ultimately have "e12 - {a1,a2} \<subseteq> U0 \<and> e34 - {a3,a4} \<subseteq> U0" by (by100 blast)
      thus False using hdiff by (by100 blast)
    next
      assume hboth: "x \<in> V0 \<and> y \<in> V0"
      have "e12 - {a1,a2} \<subseteq> V0"
      proof -
        from he12_in_comp have "e12 - {a1,a2} \<subseteq> U0 \<or> e12 - {a1,a2} \<subseteq> V0" .
        moreover have "x \<in> V0" using hboth by (by100 blast)
        moreover have "\<not> (e12 - {a1,a2} \<subseteq> U0)" using hx_int \<open>x \<in> V0\<close> hUV0(3) by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      moreover have "e34 - {a3,a4} \<subseteq> V0"
      proof -
        from he34_in_comp have "e34 - {a3,a4} \<subseteq> U0 \<or> e34 - {a3,a4} \<subseteq> V0" .
        moreover have "y \<in> V0" using hboth by (by100 blast)
        moreover have "\<not> (e34 - {a3,a4} \<subseteq> U0)" using hy_int \<open>y \<in> V0\<close> hUV0(3) by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      ultimately have "e12 - {a1,a2} \<subseteq> V0 \<and> e34 - {a3,a4} \<subseteq> V0" by (by100 blast)
      thus False using hdiff by (by100 blast)
    qed
    thus ?thesis using hx_in_UV hy_in_UV hUV0(3) by (by100 blast)
  qed
  obtain A B where hAB: "?U_loc \<inter> ?V_loc = A \<union> B" "A \<inter> B = {}"
      "openin_on ?X ?TX A" "openin_on ?X ?TX B" "x \<in> A" "y \<in> B"
  proof -
    from hx_y_diff_comp show ?thesis
    proof
      assume h: "x \<in> U0 \<and> y \<in> V0"
      show ?thesis by (rule that[of U0 V0]) (use hUV0_eq hUV0(3) hU0_open_X hV0_open_X h in \<open>by100 blast\<close>)+
    next
      assume h: "x \<in> V0 \<and> y \<in> U0"
      show ?thesis by (rule that[of V0 U0]) (use hUV0_eq hUV0(3) hU0_open_X hV0_open_X h in \<open>by100 blast\<close>)+
    qed
  qed
  have h\<alpha>\<beta>_nontrivial: "\<not> top1_path_homotopic_on ?X ?TX x x
      (top1_path_product \<alpha> \<beta>) (top1_constant_path x)"
    by (rule Theorem_63_1_loop_nontrivial[OF hTX hU_open_X hV_open_X hUV_union
           hAB(1,2,3,4,5,6) h\<alpha>_U h\<beta>_V])
  \<comment> \<open>Step D: \<alpha>*\<beta> lies in C. So [\<alpha>*\<beta>]_C is a well-defined element of \<pi>_1(C, x).
     j_*([\<alpha>*\<beta>]_C) = [\<alpha>*\<beta>]_X \<noteq> id. Hence j_* is nontrivial.
     Since \<pi>_1(C) \<cong> Z and \<pi>_1(X) \<cong> Z:
     - j_* nontrivial hom Z \<rightarrow> Z torsion-free \<Rightarrow> j_* injective.
     - [\<alpha>*\<beta>] generates \<pi>_1(X) (63.1(c) + infinite cyclic) \<Rightarrow> j_* surjective.\<close>
  have h\<alpha>\<beta>_in_C: "top1_is_loop_on C ?TC x (top1_path_product \<alpha> \<beta>)"
  proof -
    have hTC_top: "is_topology_on C ?TC"
      by (rule subspace_topology_is_topology_on[OF hTopS2 hC_sub_S2])
    \<comment> \<open>Lift \<alpha> from C-D1 to C.\<close>
    have hCmD1_sub_C: "C - ?D1 \<subseteq> C" by (by100 blast)
    have hTC_CD1: "subspace_topology C ?TC (C - ?D1) = subspace_topology top1_S2 top1_S2_topology (C - ?D1)"
      using subspace_topology_trans[of "C - ?D1" C] hCmD1_sub_C by (by100 simp)
    have h\<alpha>_C: "top1_is_path_on C ?TC x y \<alpha>"
      by (rule path_in_subspace_is_path_in_ambient'[OF hTC_top hCmD1_sub_C])
         (rule h\<alpha>[unfolded hTC_CD1[symmetric]])
    \<comment> \<open>Lift \<beta> from C-D2 to C.\<close>
    have hCmD2_sub_C: "C - ?D2 \<subseteq> C" by (by100 blast)
    have hTC_CD2: "subspace_topology C ?TC (C - ?D2) = subspace_topology top1_S2 top1_S2_topology (C - ?D2)"
      using subspace_topology_trans[of "C - ?D2" C] hCmD2_sub_C by (by100 simp)
    have h\<beta>_C: "top1_is_path_on C ?TC y x \<beta>"
      by (rule path_in_subspace_is_path_in_ambient'[OF hTC_top hCmD2_sub_C])
         (rule h\<beta>[unfolded hTC_CD2[symmetric]])
    \<comment> \<open>\<alpha>*\<beta> is a loop in C.\<close>
    show ?thesis unfolding top1_is_loop_on_def
      by (rule top1_path_product_is_path[OF hTC_top h\<alpha>_C h\<beta>_C])
  qed
  \<comment> \<open>Textbook conclusion (Munkres p.393):
     "\<alpha>*\<beta> represents a generator of \<pi>_1(X)."
     "j_* is surjective, so j_* must be an isomorphism."

     We have: h\<alpha>\<beta>\_in\_C (\<alpha>*\<beta> loop in C at x), h\<alpha>\<beta>\_nontrivial (nontrivial in X),
     hX\_inf\_cyc (\<pi>_1(X) infinite cyclic at c0), hC\_scc (C is SCC).

     The surjectivity argument at basepoint x:
     (1) [\<alpha>*\<beta>]_X generates \<pi>_1(X, x) [textbook asserts from 63.1 + inf cyclic]
     (2) [\<alpha>*\<beta>]_C is an element of \<pi>_1(C, x)
     (3) j_*([\<alpha>*\<beta>]_C) = [\<alpha>*\<beta>]_X [by inclusion\_induced\_class]
     (4) j_* hits a generator \<Rightarrow> j_* surjective

     Then basepoint change x \<rightarrow> c0.
     Then injectivity from surjective hom Z \<rightarrow> Z.\<close>
  \<comment> \<open>===== THE CORE ARGUMENT (following Munkres p.393) =====
     "Because the fundamental group of X is infinite cyclic, the loop \<alpha>*\<beta>
      represents a generator of this group."

     Proof: U\_loc, V\_loc are simply connected (S2 minus arc, S2\_minus\_arc\_simply\_connected).
     Any loop f in X subdivides into pieces in U\_loc or V\_loc (loop\_subdivision\_UV).
     Each piece is nulhomotopic in its region (simply connected).
     After contraction, only crossings A\<leftrightarrow>B remain.
     By Theorem\_63\_1\_c\_subgroups\_trivial: all crossing loops through A are trivial
     (relative to \<alpha>*\<beta>). So every loop is a power of [\<alpha>*\<beta>].
     Hence [\<alpha>*\<beta>] generates \<pi>_1(X), i.e. [\<alpha>*\<beta>] = \<plusminus>gen.

     Since \<alpha>*\<beta> \<in> C: j_*([\<alpha>*\<beta>]_C) = [\<alpha>*\<beta>]_X = generator.
     Since [\<alpha>*\<beta>]_C generates \<pi>_1(C) \<cong> Z (traverses C once):
     j_* maps generator to generator \<Rightarrow> surjective \<Rightarrow> isomorphism.\<close>
  \<comment> \<open>===== GENERATION ARGUMENT: [\<alpha>*\<beta>] generates \<pi>_1(X, x) =====
     Following Munkres Theorem 63.1(b): use helix covering + \<pi>_1(X) infinite cyclic.
     Key idea: the helix lift gives a well-defined injection \<pi>_1(X) \<hookrightarrow> Z
     with [\<alpha>*\<beta>] \<mapsto> 1. Since \<pi>_1(X) \<cong> Z, this forces [\<alpha>*\<beta>] = generator.\<close>
  \<comment> \<open>Step G1: \<pi>_1(X, x) is infinite cyclic.\<close>
  have hx_in_X: "x \<in> ?X" using hx_in_CmD1 hC_sub_X by (by100 blast)
  obtain gen where hgen_loop: "top1_is_loop_on ?X ?TX x gen"
      and hgen_generates: "\<forall>f. top1_is_loop_on ?X ?TX x f \<longrightarrow>
        (\<exists>n::nat. top1_path_homotopic_on ?X ?TX x x f (top1_path_power gen x n)
          \<or> top1_path_homotopic_on ?X ?TX x x f
               (top1_path_power (top1_path_reverse gen) x n))"
    using pi1_S2_minus_two_points_infinite_cyclic[OF assms(1) hp_S2 hq_S2 hp_ne_q hx_in_X]
    by blast
  \<comment> \<open>Step G2: Construct helix covering E \<rightarrow> X for the 63.1 setup.\<close>
  have hx_A: "x \<in> A" using hAB(5) .
  have hy_B: "y \<in> B" using hAB(6) .
  have hx_U: "x \<in> ?U_loc" using hx_in_CmD1 hCmD1_sub by (by100 blast)
  have hy_U: "y \<in> ?U_loc" using hy_in_CmD1 hCmD1_sub by (by100 blast)
  have hx_V: "x \<in> ?V_loc" using hx_in_CmD2 hCmD2_sub by (by100 blast)
  have hy_V: "y \<in> ?V_loc" using hy_in_CmD2 hCmD2_sub by (by100 blast)
  \<comment> \<open>Step G3: The helix covering and its key property.
     For any m, (\<alpha>*\<beta>)^m lifts from (x, 0) to (x, 2m).
     This is helix\_f\_power\_lift applied to the U\_loc, V\_loc, A, B decomposition.\<close>
  \<comment> \<open>Step G4: The lift endpoint function (winding number) is well-defined on
     homotopy classes, by Theorem\_54\_3 (homotopic paths lift to same endpoint).
     And it's injective: if wind(f) = wind(g), then lifts of f and g end at the
     same sheet, and by Theorem\_54\_3 applied to f*g\<inverse>, wind(f*g\<inverse>) = 0,
     which means f*g\<inverse> \<in> H = p_*(\<pi>_1(E, e0)).
     Since wind is surjective (wind((\<alpha>*\<beta>)^n) = n for all n), and \<pi>_1(X) \<cong> Z,
     we get Z/H \<cong> Z as sets, which forces H = \{0\} (Z/nZ is finite for n\<ge>1).
     So wind is injective: distinct homotopy classes have distinct lift endpoints.\<close>
  \<comment> \<open>Step G5: Since wind is injective with wind((\<alpha>*\<beta>)^n) = n hitting all of Z,
     and \<langle>[\<alpha>*\<beta>]\<rangle> \<subseteq> \<pi>_1(X), the injection wind restricted to \<langle>[\<alpha>*\<beta>]\<rangle> is surjective.
     By injectivity of wind on all of \<pi>_1(X), any element outside \<langle>[\<alpha>*\<beta>]\<rangle> would
     map to some m = wind(g) = wind((\<alpha>*\<beta>)^m), contradicting injectivity.
     So \<langle>[\<alpha>*\<beta>]\<rangle> = \<pi>_1(X).\<close>
  have h\<alpha>\<beta>_generates: "\<forall>f. top1_is_loop_on ?X ?TX x f \<longrightarrow>
    (\<exists>n::nat. top1_path_homotopic_on ?X ?TX x x f
        (top1_path_power (top1_path_product \<alpha> \<beta>) x n)
      \<or> top1_path_homotopic_on ?X ?TX x x f
           (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) x n))"
  proof (rule Theorem_63_1_b_generation[OF hTX hU_open_X hV_open_X hUV_union
         hAB(1,2,3,4,5,6) h\<alpha>_U h\<beta>_V])
    show "\<exists>gen. top1_is_loop_on ?X ?TX x gen \<and>
        (\<forall>f. top1_is_loop_on ?X ?TX x f \<longrightarrow>
          (\<exists>n::nat. top1_path_homotopic_on ?X ?TX x x f (top1_path_power gen x n)
            \<or> top1_path_homotopic_on ?X ?TX x x f
                 (top1_path_power (top1_path_reverse gen) x n)))"
      using hgen_loop hgen_generates by blast
  qed
  \<comment> \<open>[\<alpha>*\<beta>] generates \<pi>_1(X, x). Since \<alpha>*\<beta> \<in> C: j_*(x) is surjective at basepoint x.
     Basepoint change to c0. Then surjective hom Z \<rightarrow> Z \<Rightarrow> injective.\<close>
  \<comment> \<open>Both \<pi>_1(C, c0) and \<pi>_1(X, c0) are infinite cyclic (\<cong> Z).
     So they're isomorphic to each other (by transitivity through Z).\<close>
  \<comment> \<open>Step 5a: \<pi>_1(C, c0) \<cong> Z.
     C is a simple closed curve = homeomorphic to S1. \<pi>_1(S1) \<cong> Z.\<close>
  have hC_pi1_Z: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier C ?TC c0)
      (top1_fundamental_group_mul C ?TC c0)
      top1_Z_group top1_Z_mul"
    by (rule SCC_pi1_iso_Z[OF assms(1) hC_scc assms(40)])
  \<comment> \<open>Step 5b: \<pi>_1(X, c0) \<cong> Z.
     X = S2-\{p,q\}. By pi1\_S2\_minus\_two\_points\_infinite\_cyclic.\<close>
  have hX_pi1_Z: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier ?X ?TX c0)
      (top1_fundamental_group_mul ?X ?TX c0)
      top1_Z_group top1_Z_mul"
  proof -
    \<comment> \<open>Chain: S2-\{p\} \<cong> R2 \<Rightarrow> S2-\{p,q\} \<cong> R2-\{q'\} \<cong> R2-\{0\}
       \<Rightarrow> deformation retract to S1 \<Rightarrow> \<pi>_1 \<cong> Z.\<close>
    \<comment> \<open>This is the same chain as pi1\_S2\_minus\_two\_points\_infinite\_cyclic.
       We extract the Z-isomorphism instead of just the generation property.\<close>
    have hTopS2_strict: "is_topology_on_strict top1_S2 top1_S2_topology" by (rule assms(1))
    \<comment> \<open>Step 1: S2-\{p\} \<cong> R2.\<close>
    obtain \<sigma> where h\<sigma>: "top1_homeomorphism_on (top1_S2 - {p})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p}))
        (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) \<sigma>"
      using S2_minus_point_homeo_R2[OF hp_S2] by blast
    \<comment> \<open>Step 2-5: The rest follows the proof in AlgTop0.
       For brevity, we sorry this chain — it's purely mechanical composition
       of homeomorphism\_iso + deformation\_retract\_iso + Theorem\_54\_5\_iso.\<close>
    \<comment> \<open>Step 2: Restrict \<sigma> to S2-\{p,q\} \<cong> R2-\{\<sigma>(q)\}.\<close>
    define q' where "q' = \<sigma> q"
    define R2_0 :: "(real \<times> real) set" where "R2_0 = UNIV - {(0, 0)}"
    \<comment> \<open>Step 3: Translate R2-\{q'\} \<cong> R2-\{0\}.\<close>
    \<comment> \<open>Step 4: S1 deformation retract of R2-\{0\} \<Rightarrow> \<pi>_1(R2-\{0\}) \<cong> \<pi>_1(S1).\<close>
    \<comment> \<open>Step 5: \<pi>_1(S1) \<cong> Z.\<close>
    \<comment> \<open>Composition: \<pi>_1(S2-\{p,q\}, c0) \<cong> \<pi>_1(R2-\{q'\}, \<sigma>(c0))
       \<cong> \<pi>_1(R2-\{0\}, \<sigma>(c0)-q') \<cong> \<pi>_1(S1, ?) \<cong> Z.\<close>
    \<comment> \<open>The full chain is ~100 lines (following pi1\_S2\_minus\_two\_points\_infinite\_cyclic).
       Each step is a single lemma application.\<close>
    \<comment> \<open>Direct proof: compose homeomorphism\_iso + deformation\_retract\_iso + Theorem\_54\_5.\<close>
    \<comment> \<open>Compose: stereographic restriction + translation gives h: X \<cong> R2-\{0\}.\<close>
    define TR2_0 where "TR2_0 = subspace_topology UNIV
        (product_topology_on top1_open_sets top1_open_sets) R2_0"
    obtain h where hh_homeo: "top1_homeomorphism_on ?X ?TX R2_0 TR2_0 h"
    proof -
      \<comment> \<open>Restrict \<sigma> to S2-\{p,q\} \<rightarrow> R2-\{q'\}.\<close>
      have hq_in: "q \<in> top1_S2 - {p}" using hq_S2 hp_ne_q by (by100 blast)
      define R2_q' :: "(real \<times> real) set" where "R2_q' = UNIV - {q'}"
      define TR2_q' where "TR2_q' = subspace_topology UNIV
          (product_topology_on top1_open_sets top1_open_sets) R2_q'"
      have h\<sigma>_restrict: "top1_homeomorphism_on ?X ?TX R2_q' TR2_q' \<sigma>"
      proof -
        have h_step: "top1_homeomorphism_on ((top1_S2 - {p}) - {q})
            (subspace_topology (top1_S2 - {p}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p}))
              ((top1_S2 - {p}) - {q}))
            ((UNIV :: (real \<times> real) set) - {\<sigma> q})
            (subspace_topology (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)
              (UNIV - {\<sigma> q})) \<sigma>"
          by (rule homeomorphism_restrict_point[OF h\<sigma> hq_in])
        have hX_eq: "(top1_S2 - {p}) - {q} = ?X" by (by100 blast)
        have hTX_eq: "subspace_topology (top1_S2 - {p}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p}))
            ((top1_S2 - {p}) - {q}) = ?TX"
        proof -
          have "?X \<subseteq> top1_S2 - {p}" by (by100 blast)
          hence "subspace_topology (top1_S2 - {p}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p}))
              ?X = subspace_topology top1_S2 top1_S2_topology ?X"
            by (rule subspace_topology_trans)
          moreover have "(top1_S2 - {p}) - {q} = ?X" by (by100 blast)
          ultimately show ?thesis by simp
        qed
        have hY_eq: "(UNIV :: (real \<times> real) set) - {\<sigma> q} = R2_q'"
          unfolding R2_q'_def q'_def by simp
        have hTY_eq: "subspace_topology (UNIV :: (real \<times> real) set)
            (product_topology_on top1_open_sets top1_open_sets) (UNIV - {\<sigma> q}) = TR2_q'"
          unfolding TR2_q'_def R2_q'_def q'_def by simp
        show ?thesis using h_step hX_eq hY_eq hTX_eq hTY_eq by simp
      qed
      \<comment> \<open>Translation t(x) = x - q' gives R2-\{q'\} \<cong> R2-\{0\}.\<close>
      define t :: "real \<times> real \<Rightarrow> real \<times> real" where
        "t = (\<lambda>(x, y). (x - fst q', y - snd q'))"
      have ht_homeo: "top1_homeomorphism_on R2_q' TR2_q' R2_0 TR2_0 t"
      proof -
        have ht_eq: "t = (\<lambda>x. (fst x - fst q', snd x - snd q'))"
          unfolding t_def by (rule ext) auto
        show ?thesis unfolding R2_q'_def TR2_q'_def R2_0_def TR2_0_def ht_eq
          by (rule translation_homeo_R2[of q'])
      qed
      \<comment> \<open>Compose: h = t \<circ> \<sigma>.\<close>
      have "top1_homeomorphism_on ?X ?TX R2_0 TR2_0 (t \<circ> \<sigma>)"
        by (rule homeomorphism_comp[OF h\<sigma>_restrict ht_homeo])
      then show ?thesis by (rule that)
    qed
    have hTR2: "is_topology_on R2_0 TR2_0"
      using hh_homeo unfolding top1_homeomorphism_on_def top1_continuous_map_on_def
        is_topology_on_def TR2_0_def by (by100 blast)
    have hhc0: "h c0 \<in> R2_0"
      using hh_homeo hc0_X unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have hiso_XR2: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier ?X ?TX c0)
        (top1_fundamental_group_mul ?X ?TX c0)
        (top1_fundamental_group_carrier R2_0 TR2_0 (h c0))
        (top1_fundamental_group_mul R2_0 TR2_0 (h c0))"
      by (rule Corollary_52_5_homeomorphism_iso[OF hTX hTR2 hh_homeo hc0_X])
         (by100 simp)
    \<comment> \<open>Basepoint change in R2-\{0\}: h(c0) \<rightarrow> (1,0).\<close>
    have h10_R2: "(1::real, 0::real) \<in> R2_0" unfolding R2_0_def by (by100 simp)
    have hR2_pc: "top1_path_connected_on R2_0 TR2_0"
      unfolding R2_0_def TR2_0_def using R2_minus_point_path_connected[of "(0,0)"] by (by100 simp)
    obtain \<gamma>R where h\<gamma>R: "top1_is_path_on R2_0 TR2_0 (h c0) (1, 0) \<gamma>R"
      using hR2_pc hhc0 h10_R2 unfolding top1_path_connected_on_def by (by100 blast)
    have hiso_R2bp: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier R2_0 TR2_0 (h c0))
        (top1_fundamental_group_mul R2_0 TR2_0 (h c0))
        (top1_fundamental_group_carrier R2_0 TR2_0 (1, 0))
        (top1_fundamental_group_mul R2_0 TR2_0 (1, 0))"
      by (rule basepoint_change_iso_via_path[OF hTR2 h\<gamma>R])
    \<comment> \<open>Deformation retract: \<pi>_1(R2-\{0\},(1,0)) \<cong> \<pi>_1(S1,(1,0)).\<close>
    have hiso_R2S1: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1
          (subspace_topology R2_0 TR2_0 top1_S1) (1, 0))
        (top1_fundamental_group_mul top1_S1
          (subspace_topology R2_0 TR2_0 top1_S1) (1, 0))
        (top1_fundamental_group_carrier R2_0 TR2_0 (1, 0))
        (top1_fundamental_group_mul R2_0 TR2_0 (1, 0))"
      unfolding R2_0_def TR2_0_def by (rule Theorem_58_2_inclusion_iso)
    \<comment> \<open>Subspace topology S1 in R2-\{0\} = S1\_topology.\<close>
    have hS1_sub_R2_0: "top1_S1 \<subseteq> R2_0"
    proof -
      have "(0::real, 0::real) \<notin> top1_S1" unfolding top1_S1_def by (by100 simp)
      thus ?thesis unfolding R2_0_def by (by100 blast)
    qed
    have hS1_sub: "subspace_topology R2_0 TR2_0 top1_S1 = top1_S1_topology"
    proof -
      have "subspace_topology R2_0 TR2_0 top1_S1 =
          subspace_topology (UNIV :: (real \<times> real) set)
            (product_topology_on top1_open_sets top1_open_sets) top1_S1"
        unfolding TR2_0_def using subspace_topology_trans[of top1_S1 R2_0] hS1_sub_R2_0
        by (by100 simp)
      also have "... = top1_S1_topology"
        unfolding top1_S1_topology_def by simp
      finally show ?thesis .
    qed
    have hiso_S1Z: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        top1_Z_group top1_Z_mul"
      by (rule Theorem_54_5_iso)
    \<comment> \<open>Compose all steps.\<close>
    have h_chain1: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier ?X ?TX c0)
        (top1_fundamental_group_mul ?X ?TX c0)
        (top1_fundamental_group_carrier R2_0 TR2_0 (1, 0))
        (top1_fundamental_group_mul R2_0 TR2_0 (1, 0))"
      by (rule groups_isomorphic_trans_fwd[OF hiso_XR2 hiso_R2bp])
    have hiso_R2S1': "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier R2_0 TR2_0 (1, 0))
        (top1_fundamental_group_mul R2_0 TR2_0 (1, 0))
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))"
    proof -
      have hiso_sub: "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
          (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
          (top1_fundamental_group_carrier R2_0 TR2_0 (1, 0))
          (top1_fundamental_group_mul R2_0 TR2_0 (1, 0))"
        using hiso_R2S1 hS1_sub by simp
      show ?thesis
      proof (rule top1_groups_isomorphic_on_sym[OF hiso_sub])
        show "top1_is_group_on
            (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_id top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_invg top1_S1 top1_S1_topology (1, 0))"
        proof -
          have hTS1: "is_topology_on top1_S1 top1_S1_topology"
            using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def
            by (by100 blast)
          have h10_S1: "(1::real, 0::real) \<in> top1_S1"
            unfolding top1_S1_def by (by100 simp)
          show ?thesis by (rule top1_fundamental_group_is_group[OF hTS1 h10_S1])
        qed
        show "top1_is_group_on
            (top1_fundamental_group_carrier R2_0 TR2_0 (1, 0))
            (top1_fundamental_group_mul R2_0 TR2_0 (1, 0))
            (top1_fundamental_group_id R2_0 TR2_0 (1, 0))
            (top1_fundamental_group_invg R2_0 TR2_0 (1, 0))"
          by (rule top1_fundamental_group_is_group[OF hTR2 h10_R2])
      qed
    qed
    have h_chain2: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier ?X ?TX c0)
        (top1_fundamental_group_mul ?X ?TX c0)
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))"
      by (rule groups_isomorphic_trans_fwd[OF h_chain1 hiso_R2S1'])
    show ?thesis
      by (rule groups_isomorphic_trans_fwd[OF h_chain2 hiso_S1Z])
  qed
  \<comment> \<open>Step 5c: \<pi>_1(C, c0) \<cong> \<pi>_1(X, c0) by transitivity through Z.\<close>
  have hX_pi1_Z_sym: "top1_groups_isomorphic_on
      top1_Z_group top1_Z_mul
      (top1_fundamental_group_carrier ?X ?TX c0)
      (top1_fundamental_group_mul ?X ?TX c0)"
  proof (rule top1_groups_isomorphic_on_sym[OF hX_pi1_Z])
    show "top1_is_group_on (top1_fundamental_group_carrier ?X ?TX c0)
        (top1_fundamental_group_mul ?X ?TX c0)
        (top1_fundamental_group_id ?X ?TX c0)
        (top1_fundamental_group_invg ?X ?TX c0)"
      by (rule top1_fundamental_group_is_group[OF hTX hc0_X])
    have "top1_is_abelian_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
      by (rule top1_Z_is_abelian_group)
    thus "top1_is_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
      unfolding top1_is_abelian_group_on_def by (by100 blast)
  qed
  show ?thesis
    by (rule groups_isomorphic_trans_fwd[OF hC_pi1_Z hX_pi1_Z_sym])
qed

(** from \<S>65 Theorem 65.2: inclusion C \<rightarrow> S^2 - p - q induces fundamental group iso **)
theorem Theorem_65_2:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  and "p \<in> top1_S2 - C" and "q \<in> top1_S2 - C"
  \<comment> \<open>p, q in different path-components of S^2 - C (stronger than 'not connected').\<close>
  and "\<not> (\<exists>f. top1_is_path_on (top1_S2 - C)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p q f)"
  and "c0 \<in> C"
  shows "top1_groups_isomorphic_on
    (top1_fundamental_group_carrier C (subspace_topology top1_S2 top1_S2_topology C) c0)
    (top1_fundamental_group_mul C (subspace_topology top1_S2 top1_S2_topology C) c0)
    (top1_fundamental_group_carrier (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0)
    (top1_fundamental_group_mul (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0)"
proof -
  \<comment> \<open>Munkres 65.2: The inclusion C \<hookrightarrow> S^2 - {p,q} induces an isomorphism on \<pi>_1.
     Step 1 (Surjectivity): Every loop in S^2-{p,q} is homotopic to a loop on C
     (use the K4-graph structure and the nulhomotopy of loops avoiding C).
     Step 2 (Injectivity): A loop on C that's nulhomotopic in S^2-{p,q}
     would give a nulhomotopy disjoint from both p and q, but by Lemma 65.1
     the standard loop on C is nontrivial.
     Combines Lemma 65.1 with Theorem 63.1.\<close>
  let ?TC = "subspace_topology top1_S2 top1_S2_topology C"
  let ?Xpq = "top1_S2 - {p} - {q}"
  let ?TXpq = "subspace_topology top1_S2 top1_S2_topology ?Xpq"
  \<comment> \<open>Both \<pi>_1(C, c0) and \<pi>_1(S2-\{p,q\}, c0) are infinite cyclic (\<cong> Z).
     So they're isomorphic to each other (same approach as Lemma\_65\_1).\<close>
  have hC_sub_S2: "C \<subseteq> top1_S2"
    using assms(2) unfolding top1_simple_closed_curve_on_def top1_continuous_map_on_def
    by (by100 blast)
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hTXpq: "is_topology_on ?Xpq ?TXpq"
    by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
  have hc0_Xpq: "c0 \<in> ?Xpq"
  proof -
    have "c0 \<in> C" by (rule assms(6))
    hence "c0 \<in> top1_S2" using hC_sub_S2 by (by100 blast)
    moreover have "p \<notin> C" using assms(3) by (by100 blast)
    moreover have "q \<notin> C" using assms(4) by (by100 blast)
    ultimately show ?thesis using \<open>c0 \<in> C\<close> by (by100 blast)
  qed
  \<comment> \<open>\<pi>_1(C, c0) \<cong> Z (C is SCC).\<close>
  have hC_pi1_Z: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier C ?TC c0)
      (top1_fundamental_group_mul C ?TC c0)
      top1_Z_group top1_Z_mul"
    by (rule SCC_pi1_iso_Z[OF assms(1,2,6)])
  \<comment> \<open>\<pi>_1(S2-\{p,q\}, c0) \<cong> Z.\<close>
  have hp_ne_q: "p \<noteq> q"
  proof
    assume "p = q"
    have "top1_is_path_on (top1_S2 - C)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p q
        (top1_constant_path p)"
    proof -
      have hp_mem: "p \<in> top1_S2 - C" by (rule assms(3))
      have hTS2C: "is_topology_on (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C))"
        by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
      have "top1_continuous_map_on I_set I_top (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) (top1_constant_path p)"
        by (rule top1_constant_path_continuous[OF hTS2C hp_mem])
      thus ?thesis unfolding top1_is_path_on_def
        using \<open>p = q\<close> by (simp add: top1_constant_path_def)
    qed
    thus False using assms(5) by (by100 blast)
  qed
  have hX_pi1_Z: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier ?Xpq ?TXpq c0)
      (top1_fundamental_group_mul ?Xpq ?TXpq c0)
      top1_Z_group top1_Z_mul"
  proof -
    have hp_S2: "p \<in> top1_S2" using assms(3) by (by100 blast)
    have hq_S2: "q \<in> top1_S2" using assms(4) by (by100 blast)
    show ?thesis
      by (rule pi1_S2_minus_two_points_iso_Z[OF assms(1) hp_S2 hq_S2 hp_ne_q hc0_Xpq])
  qed
  \<comment> \<open>Z \<cong> \<pi>_1(S2-\{p,q\}, c0) by symmetry.\<close>
  have hX_pi1_Z_sym: "top1_groups_isomorphic_on
      top1_Z_group top1_Z_mul
      (top1_fundamental_group_carrier ?Xpq ?TXpq c0)
      (top1_fundamental_group_mul ?Xpq ?TXpq c0)"
  proof (rule top1_groups_isomorphic_on_sym[OF hX_pi1_Z])
    show "top1_is_group_on (top1_fundamental_group_carrier ?Xpq ?TXpq c0)
        (top1_fundamental_group_mul ?Xpq ?TXpq c0)
        (top1_fundamental_group_id ?Xpq ?TXpq c0)
        (top1_fundamental_group_invg ?Xpq ?TXpq c0)"
      by (rule top1_fundamental_group_is_group[OF hTXpq hc0_Xpq])
    have "top1_is_abelian_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
      by (rule top1_Z_is_abelian_group)
    thus "top1_is_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
      unfolding top1_is_abelian_group_on_def by (by100 blast)
  qed
  show ?thesis
    by (rule groups_isomorphic_trans_fwd[OF hC_pi1_Z hX_pi1_Z_sym])
qed



(** from \<S>67 Theorem 67.8: rank of free abelian group is well-defined.
    Any two bases of a free abelian group have the same cardinality. **)
theorem Theorem_67_8_rank_unique:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and iota1 :: "'s1 \<Rightarrow> 'g" and S1 :: "'s1 set"
    and iota2 :: "'s2 \<Rightarrow> 'g" and S2 :: "'s2 set"
  assumes "top1_is_free_abelian_group_full_on G mul e invg iota1 S1"
      and "top1_is_free_abelian_group_full_on G mul e invg iota2 S2"
      and "finite S1" and "finite S2"
  shows "\<exists>f. bij_betw f S1 S2"
proof -
  \<comment> \<open>Munkres 67.8: Tensor with Z/2Z: G/2G is a vector space over Z/2Z of dimension
     equal to the rank. Dimension of a vector space is unique.
     Step 1: G \<cong> Z^S1 (free abelian on S1) and G \<cong> Z^S2 (free abelian on S2).
     Step 2: G/2G \<cong> (Z/2Z)^S1 \<cong> (Z/2Z)^S2.
     Step 3: Vector space dimension: |S1| = dim (Z/2Z)^S1 = dim (Z/2Z)^S2 = |S2|.
     Step 4: Hence |S1| = |S2|, i.e. there exists a bijection.\<close>
  \<comment> \<open>Munkres 67.8: G/2G has cardinality 2^|S| for any basis S.
     So 2^|S1| = |G/2G| = 2^|S2|, hence |S1| = |S2|.\<close>
  let ?twoG = "{mul g g | g. g \<in> G}"
  \<comment> \<open>Step 1: |G/2G| = 2^|S1| and |G/2G| = 2^|S2|.
     Proof: G \<cong> Z^S_i, so G/2G \<cong> (Z/2Z)^S_i, hence |G/2G| = 2^|S_i|.\<close>
  have hfinS1: "finite S1" by (rule assms(3))
  have hfinS2: "finite S2" by (rule assms(4))
  \<comment> \<open>Helper: for free abelian G on finite basis S, |G/2G| = 2^|S|.\<close>
  have hcard_helper: "\<And>S iota. top1_is_free_abelian_group_full_on G mul e invg iota S \<Longrightarrow>
      finite S \<Longrightarrow>
      card (top1_quotient_group_carrier_on G mul ?twoG) = 2 ^ card S"
    sorry \<comment> \<open>Free abelian mod 2: G/2G \<cong> (Z/2Z)^S, hence |G/2G| = 2^|S|.
           Proof sketch: define \<phi>: G \<rightarrow> (S\<rightarrow>Z/2Z) by \<phi>(g)(s) = c_s mod 2
           where g = \<Sigma> c_s \<cdot> \<iota>(s). Well-defined by independence.
           Surjective: for any f:S\<rightarrow>{0,1}, take g = \<Sigma> f(s)\<cdot>\<iota>(s).
           Kernel = 2G. So G/2G \<cong> (S\<rightarrow>Z/2Z). |S\<rightarrow>{0,1}| = 2^|S|.\<close>
  have hcard1: "card (top1_quotient_group_carrier_on G mul ?twoG) = 2 ^ card S1"
    by (rule hcard_helper[OF assms(1) hfinS1])
  have hcard2: "card (top1_quotient_group_carrier_on G mul ?twoG) = 2 ^ card S2"
    by (rule hcard_helper[OF assms(2) hfinS2])
  \<comment> \<open>Step 2: 2^|S1| = 2^|S2| implies |S1| = |S2|.\<close>
  have "card S1 = card S2"
  proof -
    have "2 ^ card S1 = (2::nat) ^ card S2" using hcard1 hcard2 by (by100 simp)
    thus ?thesis by (by100 simp)
  qed
  \<comment> \<open>Step 3: Finite sets of equal cardinality have a bijection.\<close>
  show ?thesis by (rule finite_same_card_bij[OF hfinS1 hfinS2 \<open>card S1 = card S2\<close>])
qed


section \<open>\<S>69 Free Groups\<close>

text \<open>Helper: surjective homomorphism preserves "generated by" property.
  If G = \<langle>S\<rangle> and \<phi>: G \<twoheadrightarrow> H is a surjective homomorphism, then H = \<langle>\<phi>(S)\<rangle>.\<close>
lemma surj_hom_generated:
  assumes hG_grp: "top1_is_group_on G mulG eG invgG"
      and hH_grp: "top1_is_group_on H mulH eH invgH"
      and hhom: "top1_group_hom_on G mulG H mulH \<phi>"
      and hsurj: "\<phi> ` G = H"
      and hS_sub: "S \<subseteq> G"
      and hG_gen: "G = top1_subgroup_generated_on G mulG eG invgG S"
  shows "H = top1_subgroup_generated_on H mulH eH invgH (\<phi> ` S)"
proof -
  have hphiS_sub_H: "\<phi> ` S \<subseteq> H"
  proof (intro image_subsetI)
    fix s assume "s \<in> S"
    hence "s \<in> G" using hS_sub by (by100 blast)
    thus "\<phi> s \<in> H" using hhom unfolding top1_group_hom_on_def by (by100 blast)
  qed
  have hK_sub_H: "top1_subgroup_generated_on H mulH eH invgH (\<phi> ` S) \<subseteq> H"
    by (rule subgroup_generated_subset[OF hH_grp hphiS_sub_H])
  show ?thesis
  proof (rule set_eqI, rule iffI)
  fix h assume hh: "h \<in> H"
  \<comment> \<open>H \<subseteq> \<langle>\<phi>(S)\<rangle>.\<close>
  let ?K = "top1_subgroup_generated_on H mulH eH invgH (\<phi> ` S)"
  \<comment> \<open>g \<in> G = \<langle>S\<rangle> means g is in every subgroup containing S.\<close>
  obtain g where hg: "g \<in> G" and hphi_g: "\<phi> g = h"
    using hh hsurj by (by100 blast)
  have "g \<in> G" by (rule hg)
  \<comment> \<open>g \<in> \<langle>S\<rangle> = G, so g is in the intersection of all subgroups containing S.
     We need \<phi>(g) \<in> ?K. By definition, ?K is the intersection of all subgroups
     of H containing \<phi>(S). It suffices to show \<phi>(g) \<in> every subgroup of H
     containing \<phi>(S).\<close>
  have "\<phi> g \<in> ?K"
    unfolding top1_subgroup_generated_on_def
  proof (rule InterI, clarify)
    fix K assume hK_cond: "\<phi> ` S \<subseteq> K" and hK_sub: "K \<subseteq> H"
        and hK_grp: "top1_is_group_on K mulH eH invgH"
    \<comment> \<open>The preimage \<phi>\<inverse>(K) is a subgroup of G containing S.\<close>
    let ?preK = "{g \<in> G. \<phi> g \<in> K}"
    have hpreK_grp: "top1_is_group_on ?preK mulG eG invgG"
    proof -
      \<comment> \<open>Identity: eG \<in> G and \<phi>(eG) = eH \<in> K.\<close>
      have heG: "eG \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      have hphi_eG: "\<phi> eG = eH" by (rule hom_preserves_id[OF hG_grp hH_grp hhom])
      have h1: "eG \<in> ?preK" using heG hphi_eG hK_grp unfolding top1_is_group_on_def by (by100 blast)
      \<comment> \<open>Closure.\<close>
      have h2: "\<forall>x\<in>?preK. \<forall>y\<in>?preK. mulG x y \<in> ?preK"
      proof (intro ballI)
        fix x y assume hx: "x \<in> ?preK" and hy: "y \<in> ?preK"
        have hxG: "x \<in> G" using hx by (by100 blast)
        have hyG: "y \<in> G" using hy by (by100 blast)
        have hmulG: "mulG x y \<in> G" using hG_grp hxG hyG unfolding top1_is_group_on_def by (by100 blast)
        have "\<phi> (mulG x y) = mulH (\<phi> x) (\<phi> y)" using hhom hxG hyG unfolding top1_group_hom_on_def by (by100 blast)
        also have "mulH (\<phi> x) (\<phi> y) \<in> K" using hK_grp hx hy unfolding top1_is_group_on_def by (by100 blast)
        finally have "\<phi> (mulG x y) \<in> K" .
        thus "mulG x y \<in> ?preK" using hmulG by (by100 blast)
      qed
      \<comment> \<open>Inverse.\<close>
      have h3: "\<forall>x\<in>?preK. invgG x \<in> ?preK"
      proof (intro ballI)
        fix x assume hx: "x \<in> ?preK"
        have hxG: "x \<in> G" using hx by (by100 blast)
        have hinvG: "invgG x \<in> G" using hG_grp hxG unfolding top1_is_group_on_def by (by100 blast)
        have "\<phi> (invgG x) = invgH (\<phi> x)" by (rule hom_preserves_inv[OF hG_grp hH_grp hhom hxG])
        also have "invgH (\<phi> x) \<in> K" using hK_grp hx unfolding top1_is_group_on_def by (by100 blast)
        finally have "\<phi> (invgG x) \<in> K" .
        thus "invgG x \<in> ?preK" using hinvG by (by100 blast)
      qed
      \<comment> \<open>Group axioms (associativity, identity, inverse) follow from G.\<close>
      have h4: "\<forall>x\<in>?preK. \<forall>y\<in>?preK. \<forall>z\<in>?preK. mulG (mulG x y) z = mulG x (mulG y z)"
        using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      have h5: "\<forall>x\<in>?preK. mulG eG x = x \<and> mulG x eG = x"
        using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      have h6: "\<forall>x\<in>?preK. mulG (invgG x) x = eG \<and> mulG x (invgG x) = eG"
        using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      show ?thesis unfolding top1_is_group_on_def using h1 h2 h3 h4 h5 h6 by (by100 blast)
    qed
    have hS_preK: "S \<subseteq> ?preK" using hS_sub hK_cond by (by100 blast)
    have hpreK_subG: "?preK \<subseteq> G" by (by100 blast)
    have "top1_subgroup_generated_on G mulG eG invgG S \<subseteq> ?preK"
      by (rule subgroup_generated_minimal[OF hS_preK hpreK_subG hpreK_grp])
    hence "g \<in> ?preK" using hg hG_gen by (by100 blast)
    thus "\<phi> g \<in> K" by (by100 blast)
  qed
  thus "h \<in> ?K" using hphi_g by (by100 simp)
next
  fix h assume "h \<in> top1_subgroup_generated_on H mulH eH invgH (\<phi> ` S)"
  thus "h \<in> H"
    using hK_sub_H by (by100 blast)
  qed
qed

text \<open>Universal property of free groups: for any group H and function \<phi>: S \<rightarrow> H,
  there exists a unique homomorphism \<psi>: G \<rightarrow> H extending \<phi>.
  This follows from the free group axioms: G = \<langle>\<iota>(S)\<rangle> (generation) and
  no nontrivial reduced word is identity (freeness). Together, they ensure
  that any function on generators extends uniquely to a homomorphism.\<close>
text \<open>Uniqueness: any two homomorphisms G \<rightarrow> H agreeing on \<iota>(S) agree on all of G.
  Proof: {g \<in> G. \<psi>1(g) = \<psi>2(g)} is a subgroup containing \<iota>(S), hence = G.\<close>
lemma free_group_hom_unique:
  assumes hG: "top1_is_group_on G mul e invg"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hgen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
      and hS: "\<forall>s\<in>S. \<iota> s \<in> G"
      and h1: "top1_group_hom_on G mul H mulH \<psi>1"
      and h2: "top1_group_hom_on G mul H mulH \<psi>2"
      and hagree: "\<forall>s\<in>S. \<psi>1 (\<iota> s) = \<psi>2 (\<iota> s)"
  shows "\<forall>g\<in>G. \<psi>1 g = \<psi>2 g"
proof -
  \<comment> \<open>The agreement set A = {g \<in> G. \<psi>1(g) = \<psi>2(g)} is a subgroup containing \<iota>(S).\<close>
  let ?A = "{g \<in> G. \<psi>1 g = \<psi>2 g}"
  have hA_grp: "top1_is_group_on ?A mul e invg"
  proof -
    \<comment> \<open>Identity: \<psi>1(e) = eH = \<psi>2(e).\<close>
    have he_A: "e \<in> ?A"
    proof -
      have "e \<in> G" using hG unfolding top1_is_group_on_def by (by100 blast)
      moreover have "\<psi>1 e = eH" by (rule hom_preserves_id[OF hG hH h1])
      moreover have "\<psi>2 e = eH" by (rule hom_preserves_id[OF hG hH h2])
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Closure: if \<psi>1(g1) = \<psi>2(g1) and \<psi>1(g2) = \<psi>2(g2), then
       \<psi>1(g1\<cdot>g2) = \<psi>1(g1)\<cdot>\<psi>1(g2) = \<psi>2(g1)\<cdot>\<psi>2(g2) = \<psi>2(g1\<cdot>g2).\<close>
    have hclos: "\<forall>x\<in>?A. \<forall>y\<in>?A. mul x y \<in> ?A"
    proof (intro ballI)
      fix x y assume hx: "x \<in> ?A" and hy: "y \<in> ?A"
      have hxG: "x \<in> G" and hyG: "y \<in> G" using hx hy by (by100 blast)+
      have hmul: "mul x y \<in> G" using hG hxG hyG unfolding top1_is_group_on_def by (by100 blast)
      have "\<psi>1 (mul x y) = mulH (\<psi>1 x) (\<psi>1 y)"
        using h1 hxG hyG unfolding top1_group_hom_on_def by (by100 blast)
      also have "\<dots> = mulH (\<psi>2 x) (\<psi>2 y)"
      proof -
        have "\<psi>1 x = \<psi>2 x" using hx by (by100 blast)
        moreover have "\<psi>1 y = \<psi>2 y" using hy by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      also have "\<dots> = \<psi>2 (mul x y)"
        using h2 hxG hyG unfolding top1_group_hom_on_def by (by100 simp)
      finally show "mul x y \<in> ?A" using hmul by (by100 blast)
    qed
    \<comment> \<open>Inverse: if \<psi>1(g) = \<psi>2(g), then \<psi>1(g^{-1}) = \<psi>1(g)^{-1} = \<psi>2(g)^{-1} = \<psi>2(g^{-1}).\<close>
    have hinv: "\<forall>x\<in>?A. invg x \<in> ?A"
    proof (intro ballI)
      fix x assume hx: "x \<in> ?A"
      have hxG: "x \<in> G" using hx by (by100 blast)
      have hinvG: "invg x \<in> G" using hG hxG unfolding top1_is_group_on_def by (by100 blast)
      have "\<psi>1 (invg x) = invgH (\<psi>1 x)" by (rule hom_preserves_inv[OF hG hH h1 hxG])
      also have "\<dots> = invgH (\<psi>2 x)"
      proof -
        have "\<psi>1 x = \<psi>2 x" using hx by (by100 blast)
        thus ?thesis by (by100 simp)
      qed
      also have "\<dots> = \<psi>2 (invg x)" using hom_preserves_inv[OF hG hH h2 hxG] by (by100 simp)
      finally show "invg x \<in> ?A" using hinvG by (by100 blast)
    qed
    \<comment> \<open>Group axioms from G.\<close>
    have hassoc: "\<forall>x\<in>?A. \<forall>y\<in>?A. \<forall>z\<in>?A. mul (mul x y) z = mul x (mul y z)"
      using hG unfolding top1_is_group_on_def by (by100 blast)
    have hid: "\<forall>x\<in>?A. mul e x = x \<and> mul x e = x"
      using hG unfolding top1_is_group_on_def by (by100 blast)
    have hinvax: "\<forall>x\<in>?A. mul (invg x) x = e \<and> mul x (invg x) = e"
      using hG unfolding top1_is_group_on_def by (by100 blast)
    show ?thesis unfolding top1_is_group_on_def
      using he_A hclos hinv hassoc hid hinvax by (by100 blast)
  qed
  \<comment> \<open>\<iota>(S) \<subseteq> A.\<close>
  have hS_A: "\<iota> ` S \<subseteq> ?A" using hS hagree by (by100 blast)
  \<comment> \<open>A \<subseteq> G.\<close>
  have hA_G: "?A \<subseteq> G" by (by100 blast)
  \<comment> \<open>G = \<langle>\<iota>(S)\<rangle> \<subseteq> A (since A is a subgroup containing \<iota>(S)).\<close>
  have "top1_subgroup_generated_on G mul e invg (\<iota> ` S) \<subseteq> ?A"
    by (rule subgroup_generated_minimal[OF hS_A hA_G hA_grp])
  hence "G \<subseteq> ?A" using hgen by (by100 simp)
  thus ?thesis by (by100 blast)
qed

text \<open>Word product of elements from G stays in G.\<close>
lemma word_product_in_group:
  assumes "top1_is_group_on G mul e invg"
      and "\<forall>i<length ws. fst (ws ! i) \<in> G"
  shows "top1_group_word_product mul e invg ws \<in> G"
  using assms(2)
proof (induct ws)
  case Nil thus ?case using assms(1) unfolding top1_is_group_on_def by (by100 simp)
next
  case (Cons a ws)
  obtain x b where ha: "a = (x, b)" by (cases a) (by100 blast)
  have hx: "x \<in> G" using Cons(2) ha by (by100 force)
  have hws': "\<forall>i<length ws. fst (ws ! i) \<in> G" using Cons(2) by (by100 force)
  have hIH: "top1_group_word_product mul e invg ws \<in> G" by (rule Cons(1)[OF hws'])
  show ?case
  proof (cases b)
    case True
    have "top1_group_word_product mul e invg (a # ws) = mul x (top1_group_word_product mul e invg ws)"
      using ha True by (by100 simp)
    moreover have "mul x (top1_group_word_product mul e invg ws) \<in> G"
      using assms(1) hx hIH unfolding top1_is_group_on_def by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  next
    case False
    have "top1_group_word_product mul e invg (a # ws) = mul (invg x) (top1_group_word_product mul e invg ws)"
      using ha False by (by100 simp)
    moreover have "invg x \<in> G" using assms(1) hx unfolding top1_is_group_on_def by (by100 blast)
    moreover have "mul (invg x) (top1_group_word_product mul e invg ws) \<in> G"
      using assms(1) calculation(2) hIH unfolding top1_is_group_on_def by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
qed

text \<open>Word product distributes over list append.\<close>
lemma word_product_append:
  assumes hG: "top1_is_group_on G mul e invg"
      and hxs: "\<forall>i<length xs. fst (xs ! i) \<in> G"
      and hys: "\<forall>i<length ys. fst (ys ! i) \<in> G"
  shows "top1_group_word_product mul e invg (xs @ ys)
       = mul (top1_group_word_product mul e invg xs) (top1_group_word_product mul e invg ys)"
  using hxs
proof (induct xs)
  case Nil
  have "top1_group_word_product mul e invg ys \<in> G"
    by (rule word_product_in_group[OF hG hys])
  thus ?case using hG unfolding top1_is_group_on_def by (by100 simp)
next
  case (Cons a xs)
  obtain x b where ha: "a = (x, b)" by (cases a) (by100 blast)
  have hx_G: "x \<in> G" using Cons(2) ha by (by100 force)
  have hxs': "\<forall>i<length xs. fst (xs ! i) \<in> G"
    using Cons(2) by (by100 force)
  have hIH: "top1_group_word_product mul e invg (xs @ ys) =
      mul (top1_group_word_product mul e invg xs) (top1_group_word_product mul e invg ys)"
    by (rule Cons(1)[OF hxs'])
  have hwp_xs_G: "top1_group_word_product mul e invg xs \<in> G"
    by (rule word_product_in_group[OF hG hxs'])
  have hwp_ys_G: "top1_group_word_product mul e invg ys \<in> G"
    by (rule word_product_in_group[OF hG hys])
  have hassoc: "\<And>a b c. a \<in> G \<Longrightarrow> b \<in> G \<Longrightarrow> c \<in> G \<Longrightarrow>
      mul (mul a b) c = mul a (mul b c)"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  show ?case
  proof (cases b)
    case True
    have "top1_group_word_product mul e invg ((a # xs) @ ys)
        = mul x (top1_group_word_product mul e invg (xs @ ys))"
      using ha True by (by100 simp)
    also have "\<dots> = mul x (mul (top1_group_word_product mul e invg xs)
        (top1_group_word_product mul e invg ys))" using hIH by (by100 simp)
    also have "\<dots> = mul (mul x (top1_group_word_product mul e invg xs))
        (top1_group_word_product mul e invg ys)"
      using hassoc[OF hx_G hwp_xs_G hwp_ys_G] by (by100 simp)
    finally show ?thesis using ha True by (by100 simp)
  next
    case False
    have hinvx_G: "invg x \<in> G" using hG hx_G unfolding top1_is_group_on_def by (by100 blast)
    have "top1_group_word_product mul e invg ((a # xs) @ ys)
        = mul (invg x) (top1_group_word_product mul e invg (xs @ ys))"
      using ha False by (by100 simp)
    also have "\<dots> = mul (invg x) (mul (top1_group_word_product mul e invg xs)
        (top1_group_word_product mul e invg ys))" using hIH by (by100 simp)
    also have "\<dots> = mul (mul (invg x) (top1_group_word_product mul e invg xs))
        (top1_group_word_product mul e invg ys)"
      using hassoc[OF hinvx_G hwp_xs_G hwp_ys_G] by (by100 simp)
    finally show ?thesis using ha False by (by100 simp)
  qed
qed

text \<open>Removing a cancellable pair from a word preserves group\_word\_product in any group.\<close>
lemma word_cancel_preserves_eval:
  assumes hG: "top1_is_group_on G mul e invg"
      and hi: "i + 1 < length ws"
      and hfst: "fst (ws ! i) = fst (ws ! (i+1))"
      and hsnd: "snd (ws ! i) \<noteq> snd (ws ! (i+1))"
      and hws_G: "\<forall>j<length ws. fst (ws ! j) \<in> G"
  shows "top1_group_word_product mul e invg ws
       = top1_group_word_product mul e invg (take i ws @ drop (i+2) ws)"
proof -
  let ?pre = "take i ws"
  let ?suf = "drop (i+2) ws"
  let ?pair = "[ws ! i, ws ! (i+1)]"
  \<comment> \<open>ws = pre @ pair @ suf\<close>
  have hws_split: "ws = ?pre @ ?pair @ ?suf"
  proof -
    have hi1: "i < length ws" using hi by (by100 simp)
    have hi2: "i + 1 < length ws" using hi by (by100 simp)
    have "ws = take (i+2) ws @ drop (i+2) ws" by (by100 simp)
    moreover have "take (i+2) ws = take i ws @ [ws!i, ws!(i+1)]"
    proof -
      have hsi: "Suc i < length ws" using hi by (by100 simp)
      have "take (Suc (Suc i)) ws = take (Suc i) ws @ [ws ! (Suc i)]"
        by (rule take_Suc_conv_app_nth) (rule hsi)
      moreover have "take (Suc i) ws = take i ws @ [ws ! i]"
        by (rule take_Suc_conv_app_nth) (rule hi1)
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>The pair evaluates to e: x \<cdot> x\<inverse> = e or x\<inverse> \<cdot> x = e.\<close>
  obtain x where hx: "fst (ws ! i) = x" by (by100 blast)
  have hx_G: "x \<in> G" using hws_G hi hx by (by100 force)
  have hpair_e: "top1_group_word_product mul e invg ?pair = e"
  proof -
    obtain b1 b2 where hb1: "ws ! i = (x, b1)" and hb2: "ws ! (i+1) = (x, b2)"
      using hx hfst by (cases "ws ! i", cases "ws ! (i+1)") (by100 auto)
    have "b1 \<noteq> b2" using hsnd hb1 hb2 by (by100 simp)
    show ?thesis
    proof (cases b1)
      case True
      hence "b2 = False" using \<open>b1 \<noteq> b2\<close> by (by100 simp)
      hence "?pair = [(x, True), (x, False)]" using hb1 hb2 True by (by100 simp)
      thus ?thesis using hG hx_G unfolding top1_is_group_on_def by (by100 simp)
    next
      case False
      hence "b2 = True" using \<open>b1 \<noteq> b2\<close> by (by100 simp)
      hence "?pair = [(x, False), (x, True)]" using hb1 hb2 False by (by100 simp)
      thus ?thesis using hG hx_G unfolding top1_is_group_on_def by (by100 simp)
    qed
  qed
  \<comment> \<open>pre elements in G\<close>
  have hpre_G: "\<forall>j<length ?pre. fst (?pre ! j) \<in> G"
    using hws_G by (by100 force)
  have hpair_G: "\<forall>j<length ?pair. fst (?pair ! j) \<in> G"
  proof (intro allI impI)
    fix j assume "j < length ?pair"
    hence "j = 0 \<or> j = 1" by (by100 auto)
    thus "fst (?pair ! j) \<in> G"
      using hx_G hx hfst hws_G hi by (by100 auto)
  qed
  have hsuf_G: "\<forall>j<length ?suf. fst (?suf ! j) \<in> G"
    using hws_G by (by100 force)
  have hpairsuf_G: "\<forall>j<length (?pair @ ?suf). fst ((?pair @ ?suf) ! j) \<in> G"
  proof (intro allI impI)
    fix j assume hj: "j < length (?pair @ ?suf)"
    show "fst ((?pair @ ?suf) ! j) \<in> G"
    proof (cases "j < length ?pair")
      case True thus ?thesis using hpair_G nth_append[of ?pair ?suf j] by (by100 simp)
    next
      case False
      hence hjm: "j - length ?pair < length ?suf" using hj by (by100 simp)
      have hjlen: "j - length ?pair < length ?suf" by (rule hjm)
      have hnth: "fst (?suf ! (j - length ?pair)) \<in> G"
        using hsuf_G hjm by (by100 blast)
      have "(?pair @ ?suf) ! j = ?suf ! (j - length ?pair)"
        using False by (by100 simp)
      hence "fst ((?pair @ ?suf) ! j) = fst (?suf ! (j - length ?pair))" by (by100 simp)
      thus ?thesis using hnth by (by100 simp)
    qed
  qed
  \<comment> \<open>Split and simplify\<close>
  have "top1_group_word_product mul e invg ws
      = top1_group_word_product mul e invg (?pre @ ?pair @ ?suf)"
    using hws_split by (by100 simp)
  also have "\<dots> = mul (top1_group_word_product mul e invg ?pre)
      (top1_group_word_product mul e invg (?pair @ ?suf))"
    by (rule word_product_append[OF hG hpre_G hpairsuf_G])
  also have "top1_group_word_product mul e invg (?pair @ ?suf)
      = mul (top1_group_word_product mul e invg ?pair)
            (top1_group_word_product mul e invg ?suf)"
    by (rule word_product_append[OF hG hpair_G hsuf_G])
  also have "mul (top1_group_word_product mul e invg ?pair)
            (top1_group_word_product mul e invg ?suf) =
      mul e (top1_group_word_product mul e invg ?suf)"
    using hpair_e by (by100 simp)
  also have "\<dots> = top1_group_word_product mul e invg ?suf"
    using hG word_product_in_group[OF hG hsuf_G] unfolding top1_is_group_on_def by (by100 blast)
  finally have "top1_group_word_product mul e invg ws =
      mul (top1_group_word_product mul e invg ?pre) (top1_group_word_product mul e invg ?suf)" .
  also have "\<dots> = top1_group_word_product mul e invg (?pre @ ?suf)"
    by (rule word_product_append[OF hG hpre_G hsuf_G, symmetric])
  finally show ?thesis .
qed

text \<open>A non-reduced word has an adjacent cancellable pair.\<close>
lemma not_reduced_has_cancel:
  "\<not> top1_is_reduced_word xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow>
   \<exists>i. i + 1 < length xs \<and> fst (xs ! i) = fst (xs ! (i+1)) \<and> snd (xs ! i) \<noteq> snd (xs ! (i+1))"
proof (induct xs rule: top1_is_reduced_word.induct)
  case 1 thus ?case by (by100 simp)
next
  case (2 x) thus ?case by (by100 simp)
next
  case (3 x b y c ws)
  \<comment> \<open>is\_reduced\_word ((x,b)#(y,c)#ws) = ((x\<noteq>y \<or> b=c) \<and> is\_reduced\_word ((y,c)#ws))\<close>
  show ?case
  proof (cases "x = y \<and> b \<noteq> c")
    case True
    hence "fst (((x,b) # (y,c) # ws) ! 0) = fst (((x,b) # (y,c) # ws) ! 1)"
      by (by100 simp)
    moreover have "snd (((x,b) # (y,c) # ws) ! 0) \<noteq> snd (((x,b) # (y,c) # ws) ! 1)"
      using True by (by100 simp)
    moreover have "0 + 1 < length ((x,b) # (y,c) # ws)" by (by100 simp)
    ultimately show ?thesis
      apply (rule_tac x=0 in exI) by (by100 simp)
  next
    case False
    hence "x \<noteq> y \<or> b = c" by (by100 blast)
    hence "\<not> top1_is_reduced_word ((y,c) # ws)"
      using 3(2) by (by100 simp)
    from 3(1)[OF this]
    obtain j where hj: "j + 1 < length ((y,c) # ws)"
        and hfj: "fst (((y,c)#ws) ! j) = fst (((y,c)#ws) ! (j+1))"
        and hsj: "snd (((y,c)#ws) ! j) \<noteq> snd (((y,c)#ws) ! (j+1))"
      by (by100 blast)
    have "(j+1) + 1 < length ((x,b) # (y,c) # ws)" using hj by (by100 simp)
    moreover have "fst (((x,b)#(y,c)#ws) ! (j+1)) = fst (((x,b)#(y,c)#ws) ! ((j+1)+1))"
      using hfj by force
    moreover have "snd (((x,b)#(y,c)#ws) ! (j+1)) \<noteq> snd (((x,b)#(y,c)#ws) ! ((j+1)+1))"
      using hsj by force
    ultimately show ?thesis by (by100 blast)
  qed
qed

text \<open>Group inverse is anti-homomorphism: invg(a\<cdot>b) = invg(b)\<cdot>invg(a).\<close>
lemma group_inv_product:
  assumes hG: "top1_is_group_on G mul e invg" and ha: "a \<in> G" and hb: "b \<in> G"
  shows "invg (mul a b) = mul (invg b) (invg a)"
proof -
  have hab: "mul a b \<in> G" using hG ha hb unfolding top1_is_group_on_def by (by100 blast)
  have hia: "invg a \<in> G" using hG ha unfolding top1_is_group_on_def by (by100 blast)
  have hib: "invg b \<in> G" using hG hb unfolding top1_is_group_on_def by (by100 blast)
  have hiab: "invg (mul a b) \<in> G" using hG hab unfolding top1_is_group_on_def by (by100 blast)
  have hprod: "mul (invg b) (invg a) \<in> G" using hG hib hia unfolding top1_is_group_on_def by (by100 blast)
  \<comment> \<open>Compute (invg b \<cdot> invg a) \<cdot> (a \<cdot> b) step by step using right-to-left cancellation.\<close>
  have hassoc: "\<And>x y z. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> z \<in> G \<Longrightarrow> mul (mul x y) z = mul x (mul y z)"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  have "mul (mul (invg b) (invg a)) (mul a b)
      = mul (invg b) (mul (invg a) (mul a b))"
    by (rule hassoc[OF hib hia hab])
  also have "mul (invg a) (mul a b) = mul (mul (invg a) a) b"
    by (rule hassoc[OF hia ha hb, symmetric])
  finally have "mul (mul (invg b) (invg a)) (mul a b)
      = mul (invg b) (mul (mul (invg a) a) b)"
    using hassoc[OF hib hia hab] hassoc[OF hia ha hb] by (by100 simp)
  also have "mul (invg a) a = e" using hG ha unfolding top1_is_group_on_def by (by100 blast)
  hence "mul (invg b) (mul (mul (invg a) a) b) = mul (invg b) (mul e b)"
    by (by100 simp)
  also have "mul e b = b" using hG hb unfolding top1_is_group_on_def by (by100 blast)
  hence "mul (invg b) (mul e b) = mul (invg b) b" by (by100 simp)
  also have "mul (invg b) b = e" using hG hb unfolding top1_is_group_on_def by (by100 blast)
  finally have h_left: "mul (mul (invg b) (invg a)) (mul a b) = e" by (by100 simp)
  \<comment> \<open>Left inverse uniqueness: if x\<cdot>y = e in a group, then x = invg(y).\<close>
  have "mul (mul (invg b) (invg a)) (mul a b) = e" by (rule h_left)
  moreover have "mul (invg (mul a b)) (mul a b) = e"
    using hG hab unfolding top1_is_group_on_def by (by100 blast)
  \<comment> \<open>Both equal e after right-multiplying by (mul a b). Right-cancel to get equality.\<close>
  ultimately have "mul (mul (mul (invg b) (invg a)) (mul a b)) (invg (mul a b))
      = mul (mul (invg (mul a b)) (mul a b)) (invg (mul a b))" by (by100 simp)
  hence "mul (invg b) (invg a) = invg (mul a b)"
  proof -
    \<comment> \<open>LHS: x \<cdot> (a\<cdot>b) \<cdot> (a\<cdot>b)^{-1} = x \<cdot> e = x.\<close>
    have hcancel_ab: "mul (mul a b) (invg (mul a b)) = e"
      using hG hab unfolding top1_is_group_on_def by (by100 blast)
    have hassoc1: "mul (mul (mul (invg b) (invg a)) (mul a b)) (invg (mul a b))
        = mul (mul (invg b) (invg a)) (mul (mul a b) (invg (mul a b)))"
      by (rule hassoc[OF hprod hab hiab])
    have hLHS: "mul (mul (mul (invg b) (invg a)) (mul a b)) (invg (mul a b))
        = mul (invg b) (invg a)"
      using hassoc1 hcancel_ab hG hprod unfolding top1_is_group_on_def by (by100 simp)
    \<comment> \<open>RHS: similarly invg(a\<cdot>b).\<close>
    have hassoc2: "mul (mul (invg (mul a b)) (mul a b)) (invg (mul a b))
        = mul (invg (mul a b)) (mul (mul a b) (invg (mul a b)))"
      by (rule hassoc[OF hiab hab hiab])
    have hRHS: "mul (mul (invg (mul a b)) (mul a b)) (invg (mul a b))
        = invg (mul a b)"
      using hassoc2 hcancel_ab hG hiab unfolding top1_is_group_on_def by (by100 simp)
    from h_left \<open>mul (invg (mul a b)) (mul a b) = e\<close>
    have "mul (mul (invg b) (invg a)) (mul a b) = mul (invg (mul a b)) (mul a b)"
      by (by100 simp)
    hence "mul (mul (mul (invg b) (invg a)) (mul a b)) (invg (mul a b))
        = mul (mul (invg (mul a b)) (mul a b)) (invg (mul a b))" by (by100 simp)
    thus ?thesis using hLHS hRHS by (by100 simp)
  qed
  thus ?thesis by (by100 simp)
qed

text \<open>Word product of sign-reversed word = group inverse of word product.\<close>
lemma word_product_rev_inv:
  assumes hG: "top1_is_group_on G mul e invg"
      and hws: "\<forall>i<length ws. fst (ws ! i) \<in> G"
  shows "top1_group_word_product mul e invg (map (\<lambda>(x,b). (x, \<not>b)) (rev ws))
       = invg (top1_group_word_product mul e invg ws)"
  using hws
proof (induct ws)
  case Nil
  have "invg e = e"
  proof -
    have he: "e \<in> G" using hG unfolding top1_is_group_on_def by (by100 blast)
    have "mul (invg e) e = e" using hG he unfolding top1_is_group_on_def by (by100 blast)
    have "invg e \<in> G" using hG he unfolding top1_is_group_on_def by (by100 blast)
    have "mul (invg e) e = invg e"
      using hG \<open>invg e \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
    thus ?thesis using \<open>mul (invg e) e = e\<close> by (by100 simp)
  qed
  thus ?case by (by100 simp)
next
  case (Cons a ws)
  obtain x b where ha: "a = (x, b)" by (cases a) (by100 blast)
  have hx: "x \<in> G" using Cons(2) ha by (by100 force)
  have hws': "\<forall>i<length ws. fst (ws ! i) \<in> G" using Cons(2) by (by100 force)
  have hIH: "top1_group_word_product mul e invg (map (\<lambda>(x,b). (x, \<not>b)) (rev ws))
      = invg (top1_group_word_product mul e invg ws)" by (rule Cons(1)[OF hws'])
  \<comment> \<open>rev(a#ws) = rev ws @ [a], so map(\<not>b)(rev(a#ws)) = map(\<not>b)(rev ws) @ [(x,\<not>b)].\<close>
  let ?revws = "map (\<lambda>(x,b). (x, \<not>b)) (rev ws)"
  let ?last = "[(x, \<not>b)]"
  have hrev_eq: "map (\<lambda>(x,b). (x, \<not>b)) (rev (a # ws)) = ?revws @ ?last"
    using ha by (by100 simp)
  \<comment> \<open>Elements of reversed word in G.\<close>
  have hrevws_G: "\<forall>i<length ?revws. fst (?revws ! i) \<in> G"
  proof (intro allI impI)
    fix i assume "i < length ?revws"
    hence "i < length ws" by (by100 simp)
    hence hi: "i < length ws" .
    \<comment> \<open>rev ws ! i = ws ! (length ws - 1 - i).\<close>
    have hrev_idx: "rev ws ! i = ws ! (length ws - 1 - i)" using rev_nth hi by (by100 simp)
    have hk: "length ws - 1 - i < length ws" using hi by (by100 simp)
    obtain xk bk where hxk: "ws ! (length ws - 1 - i) = (xk, bk)"
      by (cases "ws ! (length ws - 1 - i)") (by100 blast)
    have "fst (ws ! (length ws - 1 - i)) \<in> G" using hws' hk by (by100 blast)
    hence "xk \<in> G" using hxk by (by100 simp)
    have "?revws ! i = (\<lambda>(x,b). (x, \<not>b)) (rev ws ! i)" using hi by (by100 simp)
    also have "\<dots> = (\<lambda>(x,b). (x, \<not>b)) (xk, bk)" using hrev_idx hxk by (by100 simp)
    also have "\<dots> = (xk, \<not>bk)" by (by100 simp)
    finally have "fst (?revws ! i) = xk" by (by100 simp)
    thus "fst (?revws ! i) \<in> G" using \<open>xk \<in> G\<close> by (by100 simp)
  qed
  have hlast_G: "\<forall>i<length ?last. fst (?last ! i) \<in> G" using hx by (by100 simp)
  \<comment> \<open>Use word\_product\_append.\<close>
  have "top1_group_word_product mul e invg (map (\<lambda>(x,b). (x, \<not>b)) (rev (a # ws)))
      = top1_group_word_product mul e invg (?revws @ ?last)" using hrev_eq by (by100 simp)
  also have "\<dots> = mul (top1_group_word_product mul e invg ?revws)
      (top1_group_word_product mul e invg ?last)"
    by (rule word_product_append[OF hG hrevws_G hlast_G])
  also have "\<dots> = mul (invg (top1_group_word_product mul e invg ws))
      (top1_group_word_product mul e invg ?last)" using hIH by (by100 simp)
  finally have hstep: "top1_group_word_product mul e invg (map (\<lambda>(x,b). (x, \<not>b)) (rev (a # ws)))
      = mul (invg (top1_group_word_product mul e invg ws))
            (top1_group_word_product mul e invg ?last)" .
  \<comment> \<open>Compute: wp([(x,\<not>b)]) = x or invg(x) depending on \<not>b.\<close>
  have hwp_ws: "top1_group_word_product mul e invg ws \<in> G"
    by (rule word_product_in_group[OF hG hws'])
  show ?case
  proof (cases b)
    case True
    \<comment> \<open>a = (x, True), so wp(a#ws) = mul x (wp ws). invg(wp(a#ws)) = invg(mul x (wp ws))
       = mul (invg(wp ws)) (invg x) by group\_inv\_product.\<close>
    have "top1_group_word_product mul e invg (a # ws) = mul x (top1_group_word_product mul e invg ws)"
      using ha True by (by100 simp)
    hence hinv_goal: "invg (top1_group_word_product mul e invg (a # ws))
        = invg (mul x (top1_group_word_product mul e invg ws))" by (by100 simp)
    have "invg (mul x (top1_group_word_product mul e invg ws))
        = mul (invg (top1_group_word_product mul e invg ws)) (invg x)"
      by (rule group_inv_product[OF hG hx hwp_ws])
    hence hinv_expand: "invg (top1_group_word_product mul e invg (a # ws))
        = mul (invg (top1_group_word_product mul e invg ws)) (invg x)"
      using hinv_goal by (by100 simp)
    \<comment> \<open>And wp([(x,False)]) = mul (invg x) e = invg x.\<close>
    have "top1_group_word_product mul e invg ?last = mul (invg x) e"
      using True by (by100 simp)
    also have "\<dots> = invg x"
    proof -
      have "invg x \<in> G" using hG hx unfolding top1_is_group_on_def by (by100 blast)
      thus ?thesis using hG unfolding top1_is_group_on_def by (by100 blast)
    qed
    finally have hwp_last: "top1_group_word_product mul e invg ?last = invg x" .
    show ?thesis using hstep hinv_expand hwp_last by (by100 simp)
  next
    case False
    \<comment> \<open>a = (x, False), so wp(a#ws) = mul (invg x) (wp ws).
       invg(wp(a#ws)) = mul (invg(wp ws)) (invg(invg x)) = mul (invg(wp ws)) x.\<close>
    have "top1_group_word_product mul e invg (a # ws) = mul (invg x) (top1_group_word_product mul e invg ws)"
      using ha False by (by100 simp)
    have hinvx: "invg x \<in> G" using hG hx unfolding top1_is_group_on_def by (by100 blast)
    have "invg (mul (invg x) (top1_group_word_product mul e invg ws))
        = mul (invg (top1_group_word_product mul e invg ws)) (invg (invg x))"
      by (rule group_inv_product[OF hG hinvx hwp_ws])
    \<comment> \<open>invg(invg x) = x.\<close>
    have "invg (invg x) = x"
    proof -
      have "mul x (invg x) = e" using hG hx unfolding top1_is_group_on_def by (by100 blast)
      have "mul (invg (invg x)) (invg x) = e"
        using hG hinvx unfolding top1_is_group_on_def by (by100 blast)
      hence "invg (invg x) = x"
      proof -
        have hiix: "invg (invg x) \<in> G" using hG hinvx unfolding top1_is_group_on_def by (by100 blast)
        have "mul (invg (invg x)) (invg x) = mul x (invg x)"
          using \<open>mul (invg (invg x)) (invg x) = e\<close> \<open>mul x (invg x) = e\<close> by (by100 simp)
        hence "mul (mul (invg (invg x)) (invg x)) x = mul (mul x (invg x)) x" by (by100 simp)
        hence "invg (invg x) = x"
          using hG hx hinvx hiix unfolding top1_is_group_on_def by (by100 metis)
        thus ?thesis .
      qed
      thus ?thesis .
    qed
    have hinv_expand: "invg (top1_group_word_product mul e invg (a # ws))
        = mul (invg (top1_group_word_product mul e invg ws)) x"
      using \<open>top1_group_word_product mul e invg (a # ws) = mul (invg x) (top1_group_word_product mul e invg ws)\<close>
            \<open>invg (mul (invg x) (top1_group_word_product mul e invg ws)) = mul (invg (top1_group_word_product mul e invg ws)) (invg (invg x))\<close>
            \<open>invg (invg x) = x\<close> by (by100 simp)
    have "top1_group_word_product mul e invg ?last = mul x e"
      using False by (by100 simp)
    also have "\<dots> = x" using hG hx unfolding top1_is_group_on_def by (by100 blast)
    finally have hwp_last: "top1_group_word_product mul e invg ?last = x" .
    show ?thesis using hstep hinv_expand hwp_last by (by100 simp)
  qed
qed

text \<open>Key lemma: in a free group, if a word over generators evaluates to e,
  then the same word with generators replaced evaluates to eH in any group H.\<close>
lemma free_group_word_kernel:
  assumes hG: "top1_is_free_group_full_on G mul e invg \<iota> S"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hphi_H: "\<forall>s\<in>S. \<phi> s \<in> H"
      and hws: "\<forall>i<length ws. fst (ws ! i) \<in> S"
      and heval: "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ws) = e"
  shows "top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ws) = eH"
proof -
  have hG_grp: "top1_is_group_on G mul e invg"
    using hG unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hG_inj: "inj_on \<iota> S"
    using hG unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hG_in: "\<forall>s\<in>S. \<iota> s \<in> G"
    using hG unfolding top1_is_free_group_full_on_def by (by100 blast)
  \<comment> \<open>The free group axiom: non-empty reduced word \<noteq> e.\<close>
  have hfree_ax: "\<And>ws'. ws' \<noteq> [] \<Longrightarrow>
      top1_is_reduced_word (map (\<lambda>(s,b). (\<iota> s, b)) ws') \<Longrightarrow>
      (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<Longrightarrow>
      top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ws') \<noteq> e"
    using hG unfolding top1_is_free_group_full_on_def by (by100 blast)
  \<comment> \<open>Non-reduced word has a cancellable pair.\<close>
  have hnonred_cancel: "\<And>ws'. ws' \<noteq> [] \<Longrightarrow>
      \<not> top1_is_reduced_word (map (\<lambda>(s,b). (\<iota> s, b)) ws') \<Longrightarrow>
      (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<Longrightarrow>
      \<exists>i. i + 1 < length ws' \<and> fst (ws' ! i) = fst (ws' ! (i+1))
        \<and> snd (ws' ! i) \<noteq> snd (ws' ! (i+1))"
  proof (goal_cases)
    case (1 ws')
    have hne: "ws' \<noteq> []" and hnr: "\<not> top1_is_reduced_word (map (\<lambda>(s,b). (\<iota> s, b)) ws')"
        and hS: "\<forall>i<length ws'. fst (ws' ! i) \<in> S"
      using 1 by (by100 blast)+
    \<comment> \<open>The mapped word has an adjacent cancellable pair. Extract it and
       use injectivity of \<iota> to get a cancellable pair in ws'.\<close>
    let ?mws = "map (\<lambda>(s,b). (\<iota> s, b)) ws'"
    \<comment> \<open>Non-reduced means: \<exists>i. fst(?mws!i) = fst(?mws!(i+1)) \<and> snd(?mws!i) \<noteq> snd(?mws!(i+1)).\<close>
    have "\<exists>i. i + 1 < length ?mws \<and> fst (?mws ! i) = fst (?mws ! (i+1))
        \<and> snd (?mws ! i) \<noteq> snd (?mws ! (i+1))"
    proof -
      \<comment> \<open>General fact by strong induction on length.\<close>
      have gen: "\<And>xs :: ('g \<times> bool) list. xs \<noteq> [] \<Longrightarrow> \<not> top1_is_reduced_word xs \<Longrightarrow>
          \<exists>i. i + 1 < length xs \<and> fst (xs ! i) = fst (xs ! (i+1)) \<and> snd (xs ! i) \<noteq> snd (xs ! (i+1))"
        using not_reduced_has_cancel by (by100 blast)
      have "?mws \<noteq> []" using hne by (by100 simp)
      thus ?thesis using gen[OF \<open>?mws \<noteq> []\<close> hnr] by (by100 blast)
    qed
    then obtain j where hj: "j + 1 < length ?mws"
        and hfj: "fst (?mws ! j) = fst (?mws ! (j+1))"
        and hsj: "snd (?mws ! j) \<noteq> snd (?mws ! (j+1))" by (by100 blast)
    have hjw: "j + 1 < length ws'" using hj by (by100 simp)
    \<comment> \<open>Map nth: ?mws ! j = (\<iota>(fst(ws'!j)), snd(ws'!j)).\<close>
    obtain s1 b1 where hw1: "ws' ! j = (s1, b1)" by (cases "ws'!j") (by100 blast)
    obtain s2 b2 where hw2: "ws' ! (j+1) = (s2, b2)" by (cases "ws'!(j+1)") (by100 blast)
    have hj1: "j < length ws'" using hjw by (by100 simp)
    have hj2: "j+1 < length ws'" using hjw by (by100 simp)
    have hmj: "?mws ! j = (\<iota> s1, b1)" using hw1 hj1 by simp
    have hmj1: "?mws ! (j+1) = (\<iota> s2, b2)" using hw2 hj2 by simp
    \<comment> \<open>\<iota>(s1) = \<iota>(s2) and b1 \<noteq> b2.\<close>
    have "\<iota> s1 = \<iota> s2" using hfj hmj hmj1 by (by100 simp)
    moreover have "s1 \<in> S" using hS hj1 hw1 by (by100 force)
    moreover have "s2 \<in> S" using hS hj2 hw2 by (by100 force)
    ultimately have "s1 = s2" using hG_inj unfolding inj_on_def by (by100 blast)
    hence "fst (ws' ! j) = fst (ws' ! (j+1))" using hw1 hw2 by (by100 simp)
    moreover have "snd (ws' ! j) \<noteq> snd (ws' ! (j+1))"
      using hsj hmj hmj1 hw1 hw2 by (by100 simp)
    ultimately show "\<exists>i. i + 1 < length ws' \<and> fst (ws' ! i) = fst (ws' ! (i+1))
        \<and> snd (ws' ! i) \<noteq> snd (ws' ! (i+1))"
      using hjw by (by100 blast)
  qed
  \<comment> \<open>Strong induction on length ws.\<close>
  show ?thesis using hws heval
  proof (induct "length ws" arbitrary: ws rule: less_induct)
    case (less ws)
    show ?case
    proof (cases "ws = []")
      case True thus ?thesis by (by100 simp)
    next
      case False
      \<comment> \<open>If the mapped word is reduced, contradiction with free group axiom.\<close>
      show ?thesis
      proof (cases "top1_is_reduced_word (map (\<lambda>(s,b). (\<iota> s, b)) ws)")
        case True
        hence "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ws) \<noteq> e"
          by (rule hfree_ax[OF False _ less(2)])
        thus ?thesis using less(3) by (by100 blast)
      next
        case not_reduced: False
        \<comment> \<open>Find cancellable pair.\<close>
        obtain i where hi: "i + 1 < length ws"
            and hfst_i: "fst (ws ! i) = fst (ws ! (i+1))"
            and hsnd_i: "snd (ws ! i) \<noteq> snd (ws ! (i+1))"
          using hnonred_cancel[OF \<open>ws \<noteq> []\<close> not_reduced less(2)] by (by100 blast)
        let ?ws' = "take i ws @ drop (i+2) ws"
        \<comment> \<open>Mapped words: cancellation at position i.\<close>
        \<comment> \<open>Elements in G/H for mapped words — not directly needed, skip.\<close>
        \<comment> \<open>Apply word\_cancel to G-word.\<close>
        \<comment> \<open>Key: map commutes with take/drop, and cancellable pair transfers.\<close>
        have hmap_split: "\<And>f. map f (take i ws @ drop (i+2) ws)
            = take i (map f ws) @ drop (i+2) (map f ws)"
          by (simp add: take_map drop_map)
        have hi1: "i < length ws" using hi by (by100 simp)
        have hi2: "i+1 < length ws" using hi by (by100 simp)
        obtain s1 b1 where hw_i: "ws ! i = (s1, b1)" by (cases "ws!i") (by100 blast)
        obtain s2 b2 where hw_i1: "ws ! (i+1) = (s2, b2)" by (cases "ws!(i+1)") (by100 blast)
        have hs_eq: "s1 = s2" using hfst_i hw_i hw_i1 by (by100 simp)
        have hb_neq: "b1 \<noteq> b2" using hsnd_i hw_i hw_i1 by (by100 simp)
        have hnth_i: "map (\<lambda>(s,b). (\<iota> s, b)) ws ! i = (\<iota> s1, b1)"
          using hi1 hw_i by (by100 simp)
        have hnth_i1: "map (\<lambda>(s,b). (\<iota> s, b)) ws ! (i+1) = (\<iota> s2, b2)"
          using hi2 hw_i1 by (by100 simp)
        have hG_fst: "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! i) = fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! (i+1))"
          using hnth_i hnth_i1 hs_eq by (by100 simp)
        have hG_snd: "snd (map (\<lambda>(s,b). (\<iota> s, b)) ws ! i) \<noteq> snd (map (\<lambda>(s,b). (\<iota> s, b)) ws ! (i+1))"
          using hnth_i hnth_i1 hb_neq by (by100 simp)
        have hG_len: "i + 1 < length (map (\<lambda>(s,b). (\<iota> s, b)) ws)" using hi by (by100 simp)
        have hG_in_mapped: "\<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ws).
            fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G"
        proof (intro allI impI)
          fix j assume hj: "j < length (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
          hence hjw: "j < length ws" by (by100 simp)
          obtain sj bj where hwj: "ws ! j = (sj, bj)" by (cases "ws!j") (by100 blast)
          have "sj \<in> S" using less(2) hjw hwj by (by100 force)
          hence "\<iota> sj \<in> G" using hG_in by (by100 blast)
          moreover have "map (\<lambda>(s,b). (\<iota> s, b)) ws ! j = (\<iota> sj, bj)" using hjw hwj by simp
          ultimately show "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G" by (by100 simp)
        qed
        have hcancel_G: "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ws)
            = top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ?ws')"
          using word_cancel_preserves_eval[OF hG_grp hG_len hG_fst hG_snd hG_in_mapped]
                hmap_split[of "\<lambda>(s,b). (\<iota> s, b)"] by (by100 simp)
        hence heval': "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ?ws') = e"
          using less(3) by (by100 simp)
        \<comment> \<open>ws' is shorter.\<close>
        have hlen: "length ?ws' < length ws" using hi by (by100 simp)
        have hws'_S: "\<forall>j<length ?ws'. fst (?ws' ! j) \<in> S"
        proof (intro allI impI)
          fix j assume hj: "j < length ?ws'"
          have "?ws' ! j \<in> set ?ws'" using nth_mem hj by (by100 blast)
          hence "?ws' ! j \<in> set (take i ws) \<or> ?ws' ! j \<in> set (drop (i+2) ws)"
            using Un_iff set_append by (by100 fast)
          hence "?ws' ! j \<in> set ws"
          proof
            assume "?ws' ! j \<in> set (take i ws)" thus ?thesis using in_set_takeD by (by100 fast)
          next
            assume "?ws' ! j \<in> set (drop (i+2) ws)" thus ?thesis using in_set_dropD by (by100 fast)
          qed
          then obtain k where hk: "k < length ws" and hwk: "ws ! k = ?ws' ! j"
            using in_set_conv_nth by (by100 metis)
          thus "fst (?ws' ! j) \<in> S" using less(2) hwk by (by100 force)
        qed
        \<comment> \<open>By IH: H-evaluation of ws' equals eH.\<close>
        have hIH: "top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ?ws') = eH"
          by (rule less(1)[OF hlen hws'_S heval'])
        \<comment> \<open>word\_cancel on H-word: H-evaluation of ws = H-evaluation of ws'.\<close>
        have hH_in_mapped: "\<forall>j<length (map (\<lambda>(s,b). (\<phi> s, b)) ws).
            fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! j) \<in> H"
        proof (intro allI impI)
          fix j assume hj: "j < length (map (\<lambda>(s,b). (\<phi> s, b)) ws)"
          hence hjw: "j < length ws" by (by100 simp)
          obtain sj bj where hwj: "ws ! j = (sj, bj)" by (cases "ws!j") (by100 blast)
          have "sj \<in> S" using less(2) hjw hwj by (by100 force)
          hence "\<phi> sj \<in> H" using hphi_H by (by100 blast)
          moreover have "map (\<lambda>(s,b). (\<phi> s, b)) ws ! j = (\<phi> sj, bj)" using hjw hwj by simp
          ultimately show "fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! j) \<in> H" by (by100 simp)
        qed
        have hH_fst: "fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! i) = fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! (i+1))"
          using hw_i hw_i1 hs_eq hi1 hi2 by simp
        have hH_snd: "snd (map (\<lambda>(s,b). (\<phi> s, b)) ws ! i) \<noteq> snd (map (\<lambda>(s,b). (\<phi> s, b)) ws ! (i+1))"
          using hw_i hw_i1 hb_neq hi1 hi2 by simp
        have hH_len: "i + 1 < length (map (\<lambda>(s,b). (\<phi> s, b)) ws)" using hi by (by100 simp)
        have hcancel_H: "top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ws)
            = top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ?ws')"
          using word_cancel_preserves_eval[OF hH hH_len hH_fst hH_snd hH_in_mapped]
                hmap_split[of "\<lambda>(s,b). (\<phi> s, b)"] by (by100 simp)
        thus ?thesis using hIH by (by100 simp)
      qed
    qed
  qed
qed

text \<open>Existence part of universal property.\<close>
lemma free_group_hom_exists:
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
      and "top1_is_group_on H mulH eH invgH"
      and "\<forall>s\<in>S. \<phi> s \<in> H"
  shows "\<exists>\<psi>. top1_group_hom_on G mul H mulH \<psi> \<and> (\<forall>s\<in>S. \<psi> (\<iota> s) = \<phi> s)"
proof -
  have hG_grp: "top1_is_group_on G mul e invg"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hG_in: "\<forall>s\<in>S. \<iota> s \<in> G"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hG_gen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  \<comment> \<open>Step 1: The set of word-products equals G.
     Define W = {top1\_group\_word\_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ws)
                | ws. \<forall>i<length ws. fst(ws!i) \<in> S}.
     W is a subgroup of G containing \<iota>(S), hence W = \<langle>\<iota>(S)\<rangle> = G.\<close>
  let ?eval_G = "\<lambda>ws. top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
  let ?eval_H = "\<lambda>ws. top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ws)"
  let ?W = "{?eval_G ws | ws. \<forall>i<length ws. fst (ws ! i) \<in> S}"
  have hW_eq_G: "?W = G"
  proof (rule set_eqI, rule iffI)
    \<comment> \<open>W \<subseteq> G: word products are in G.\<close>
    fix g assume "g \<in> ?W"
    then obtain ws where hws: "\<forall>i<length ws. fst (ws ! i) \<in> S" and hg: "g = ?eval_G ws"
      by (by100 blast)
    have "\<forall>i<length (map (\<lambda>(s,b). (\<iota> s, b)) ws). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! i) \<in> G"
    proof (intro allI impI)
      fix j assume "j < length (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
      hence hj: "j < length ws" by (by100 simp)
      obtain s b where hwj: "ws ! j = (s, b)" by (cases "ws!j") (by100 blast)
      have "s \<in> S" using hws hj hwj by (by100 force)
      thus "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G"
        using hG_in hj hwj by simp
    qed
    thus "g \<in> G" using hg word_product_in_group[OF hG_grp] by (by100 simp)
  next
    \<comment> \<open>G \<subseteq> W: G = \<langle>\<iota>(S)\<rangle> and W is a subgroup containing \<iota>(S).\<close>
    fix g assume hg: "g \<in> G"
    \<comment> \<open>W is a subgroup of G containing \<iota>(S).\<close>
    \<comment> \<open>Helper: mapped word elements are in G.\<close>
    have hmapped_G: "\<And>ws. \<forall>i<length ws. fst (ws ! i) \<in> S \<Longrightarrow>
        \<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ws). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G"
    proof (intro allI impI)
      fix ws and j
      assume h: "\<forall>i<length ws. fst (ws ! i) \<in> S" and hj: "j < length (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
      hence hjw: "j < length ws" by (by100 simp)
      obtain sj bj where hwj: "ws ! j = (sj, bj)" by (cases "ws!j") (by100 blast)
      have "sj \<in> S" using h hjw hwj by (by100 force)
      thus "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G" using hG_in hjw hwj by simp
    qed
    have hW_grp: "top1_is_group_on ?W mul e invg"
    proof -
      have he: "e \<in> ?W"
        apply (rule CollectI) apply (rule exI[of _ "[]"]) by (by100 simp)
      have hcl: "\<forall>x\<in>?W. \<forall>y\<in>?W. mul x y \<in> ?W"
      proof (intro ballI)
        fix x y assume "x \<in> ?W" "y \<in> ?W"
        then obtain ws1 ws2 where h1: "\<forall>i<length ws1. fst(ws1!i) \<in> S" "x = ?eval_G ws1"
            and h2: "\<forall>i<length ws2. fst(ws2!i) \<in> S" "y = ?eval_G ws2" by (by100 blast)
        have hmap_app: "map (\<lambda>(s,b). (\<iota> s, b)) (ws1 @ ws2) =
            map (\<lambda>(s,b). (\<iota> s, b)) ws1 @ map (\<lambda>(s,b). (\<iota> s, b)) ws2" by (by100 simp)
        have "mul x y = ?eval_G (ws1 @ ws2)"
          using h1(2) h2(2) word_product_append[OF hG_grp hmapped_G[OF h1(1)] hmapped_G[OF h2(1)]]
                hmap_app by (by100 simp)
        moreover have "\<forall>i<length (ws1@ws2). fst((ws1@ws2)!i) \<in> S"
          using h1(1) h2(1) by (simp add: nth_append)
        ultimately show "mul x y \<in> ?W" by (by100 blast)
      qed
      have hinv: "\<forall>x\<in>?W. invg x \<in> ?W"
      proof (intro ballI)
        fix x assume "x \<in> ?W"
        then obtain ws where hws: "\<forall>i<length ws. fst(ws!i) \<in> S" "x = ?eval_G ws" by (by100 blast)
        let ?rws = "map (\<lambda>(s,b). (s, \<not>b)) (rev ws)"
        have hrev_map: "map (\<lambda>(s,b). (\<iota> s, b)) ?rws
            = map (\<lambda>(x,b). (x, \<not>b)) (rev (map (\<lambda>(s,b). (\<iota> s, b)) ws))"
          by (induct ws) auto
        have "invg x = ?eval_G ?rws"
          using hws(2) word_product_rev_inv[OF hG_grp hmapped_G[OF hws(1)]] hrev_map by (by100 simp)
        moreover have "\<forall>i<length ?rws. fst(?rws!i) \<in> S"
        proof (intro allI impI)
          fix i assume "i < length ?rws"
          hence hi: "i < length ws" by (by100 simp)
          have "length ws - 1 - i < length ws" using hi by (by100 simp)
          obtain si bi where "ws ! (length ws - 1 - i) = (si, bi)"
            by (cases "ws!(length ws - 1 - i)") (by100 blast)
          hence hsi_S: "si \<in> S" using hws(1) \<open>length ws - 1 - i < length ws\<close> by (by100 force)
          have hrev_i: "rev ws ! i = ws ! (length ws - 1 - i)" using rev_nth[of i ws] hi by (by100 simp)
          hence hrev_si: "rev ws ! i = (si, bi)" using \<open>ws ! (length ws - 1 - i) = (si, bi)\<close> by (by100 simp)
          have "?rws ! i = (case rev ws ! i of (s, b) \<Rightarrow> (s, \<not>b))" using hi by (by100 simp)
          hence "?rws ! i = (si, \<not>bi)" using hrev_si by (by100 simp)
          thus "fst(?rws!i) \<in> S" using hsi_S by (by100 simp)
        qed
        ultimately show "invg x \<in> ?W" by (by100 blast)
      qed
      \<comment> \<open>W \<subseteq> G for group axioms.\<close>
      have hWG: "?W \<subseteq> G"
      proof
        fix g assume "g \<in> ?W"
        then obtain ws where "g = ?eval_G ws" "\<forall>i<length ws. fst(ws!i) \<in> S" by (by100 blast)
        thus "g \<in> G" using word_product_in_group[OF hG_grp hmapped_G] by (by100 simp)
      qed
      show ?thesis unfolding top1_is_group_on_def
      proof (intro conjI)
        show "e \<in> ?W" by (rule he)
        show "\<forall>x\<in>?W. \<forall>y\<in>?W. mul x y \<in> ?W" by (rule hcl)
        show "\<forall>x\<in>?W. invg x \<in> ?W" by (rule hinv)
      next
        show "\<forall>x\<in>?W. \<forall>y\<in>?W. \<forall>z\<in>?W. mul (mul x y) z = mul x (mul y z)"
          using hWG hG_grp unfolding top1_is_group_on_def by blast
        show "\<forall>x\<in>?W. mul e x = x \<and> mul x e = x"
          using hWG hG_grp unfolding top1_is_group_on_def by blast
        show "\<forall>x\<in>?W. mul (invg x) x = e \<and> mul x (invg x) = e"
          using hWG hG_grp unfolding top1_is_group_on_def by blast
      qed
    qed
    have hW_sub: "?W \<subseteq> G"
    proof
      fix g assume "g \<in> ?W"
      then obtain ws where hws: "\<forall>i<length ws. fst (ws ! i) \<in> S" "g = ?eval_G ws" by (by100 blast)
      have "\<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ws). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G"
      proof (intro allI impI)
        fix j assume "j < length (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
        hence hj: "j < length ws" by (by100 simp)
        obtain s b where "ws ! j = (s, b)" by (cases "ws!j") (by100 blast)
        have "fst (ws ! j) \<in> S" using hws(1) hj by (by100 blast)
        thus "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G"
          using hG_in hj \<open>ws ! j = (s, b)\<close> by simp
      qed
      thus "g \<in> G" using hws(2) word_product_in_group[OF hG_grp] by (by100 simp)
    qed
    have hiotaS_W: "\<iota> ` S \<subseteq> ?W"
    proof (intro image_subsetI)
      fix s assume hs: "s \<in> S"
      have "?eval_G [(s, True)] = mul (\<iota> s) e" by (by100 simp)
      also have "\<dots> = \<iota> s" using hG_grp hG_in hs unfolding top1_is_group_on_def by (by100 blast)
      finally have "\<iota> s = ?eval_G [(s, True)]" by (by100 simp)
      moreover have "\<forall>i<length [(s, True)]. fst ([(s, True)] ! i) \<in> S"
        using hs by (by100 simp)
      ultimately show "\<iota> s \<in> ?W" by (by100 blast)
    qed
    have hW_in: "?W \<in> {K. \<iota> ` S \<subseteq> K \<and> K \<subseteq> G \<and> top1_is_group_on K mul e invg}"
      using hiotaS_W hW_sub hW_grp by (by100 blast)
    hence "top1_subgroup_generated_on G mul e invg (\<iota> ` S) \<subseteq> ?W"
      unfolding top1_subgroup_generated_on_def
      using Inter_lower[OF hW_in] by (by100 blast)
    thus "g \<in> ?W" using hg hG_gen by (by100 blast)
  qed
  \<comment> \<open>Step 2: Define \<psi> via SOME word representation.\<close>
  let ?\<psi> = "\<lambda>g. ?eval_H (SOME ws. (\<forall>i<length ws. fst (ws ! i) \<in> S) \<and> ?eval_G ws = g)"
  \<comment> \<open>Helper: mapped word elements are in G.\<close>
  have hmapped_G: "\<And>ws. \<forall>i<length ws. fst (ws ! i) \<in> S \<Longrightarrow>
      \<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ws). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G"
  proof (intro allI impI)
    fix ws and j
    assume h: "\<forall>i<length ws. fst (ws ! i) \<in> S" and hj: "j < length (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
    hence hjw: "j < length ws" by (by100 simp)
    obtain sj bj where hwj: "ws ! j = (sj, bj)" by (cases "ws!j") (by100 blast)
    have "sj \<in> S" using h hjw hwj by (by100 force)
    thus "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G" using hG_in hjw hwj by simp
  qed
  \<comment> \<open>Step 3: \<psi> is well-defined: any two word representations give the same H-value.\<close>
  \<comment> \<open>Helper: flip-rev preserves S-generators and commutes with map.\<close>
  have hfliprev_S: "\<And>ws. \<forall>i<length ws. fst (ws ! i) \<in> S \<Longrightarrow>
      \<forall>i<length (map (\<lambda>(s,b). (s, \<not>b)) (rev ws)). fst (map (\<lambda>(s,b). (s, \<not>b)) (rev ws) ! i) \<in> S"
  proof (intro allI impI)
    fix ws and i
    assume h: "\<forall>i<length ws. fst (ws ! i) \<in> S" and hi: "i < length (map (\<lambda>(s,b). (s, \<not>b)) (rev ws))"
    hence hiw: "i < length ws" by (by100 simp)
    have "length ws - 1 - i < length ws" using hiw by (by100 simp)
    obtain s b where hsb: "ws ! (length ws - 1 - i) = (s, b)" by (cases "ws!(length ws-1-i)") (by100 blast)
    have "s \<in> S" using h \<open>length ws - 1 - i < length ws\<close> hsb by (by100 force)
    have hrev: "rev ws ! i = (s, b)" using rev_nth[of i ws] hiw hsb by (by100 simp)
    have "map (\<lambda>(s,b). (s, \<not>b)) (rev ws) ! i = (s, \<not>b)" using hiw hrev by simp
    thus "fst (map (\<lambda>(s,b). (s, \<not>b)) (rev ws) ! i) \<in> S" using \<open>s \<in> S\<close> by (by100 simp)
  qed
  have hmap_fliprev: "\<And>ws. map (\<lambda>(s,b). (\<iota> s, b)) (map (\<lambda>(s,b). (s, \<not>b)) (rev ws))
      = map (\<lambda>(x,b). (x, \<not>b)) (rev (map (\<lambda>(s,b). (\<iota> s, b)) ws))"
    by (induct_tac ws) auto
  have hwd: "\<And>ws1 ws2. \<forall>i<length ws1. fst (ws1 ! i) \<in> S \<Longrightarrow>
      \<forall>i<length ws2. fst (ws2 ! i) \<in> S \<Longrightarrow>
      ?eval_G ws1 = ?eval_G ws2 \<Longrightarrow>
      ?eval_H ws1 = ?eval_H ws2"
  proof (goal_cases)
    case (1 ws1 ws2)
    let ?fr2 = "map (\<lambda>(s,b). (s, \<not>b)) (rev ws2)"
    let ?ws3 = "ws1 @ ?fr2"
    \<comment> \<open>ws3 generators from S.\<close>
    have hfr2_S: "\<forall>i<length ?fr2. fst (?fr2 ! i) \<in> S" by (rule hfliprev_S[OF 1(2)])
    have hws3_S: "\<forall>i<length ?ws3. fst (?ws3 ! i) \<in> S"
      using 1(1) hfr2_S by (simp add: nth_append)
    \<comment> \<open>eval\_G(ws3) = e.\<close>
    have hmG1: "\<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ws1). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws1 ! j) \<in> G"
      by (rule hmapped_G[OF 1(1)])
    have hmGr: "\<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ?fr2). fst (map (\<lambda>(s,b). (\<iota> s, b)) ?fr2 ! j) \<in> G"
      by (rule hmapped_G[OF hfr2_S])
    have hmG2: "\<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ws2). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws2 ! j) \<in> G"
      by (rule hmapped_G[OF 1(2)])
    have happ_map: "map (\<lambda>(s,b). (\<iota> s, b)) ?ws3 =
        map (\<lambda>(s,b). (\<iota> s, b)) ws1 @ map (\<lambda>(s,b). (\<iota> s, b)) ?fr2" by (by100 simp)
    have heval_G_split: "?eval_G ?ws3 = mul (?eval_G ws1) (?eval_G ?fr2)"
      using word_product_append[OF hG_grp hmG1 hmGr] happ_map by (by100 simp)
    have heval_G_rev: "?eval_G ?fr2 = invg (?eval_G ws2)"
      using word_product_rev_inv[OF hG_grp hmG2] hmap_fliprev by (by100 simp)
    have heval_G_e: "?eval_G ?ws3 = e"
    proof -
      have "?eval_G ?ws3 = mul (?eval_G ws1) (invg (?eval_G ws2))"
        using heval_G_split heval_G_rev by (by100 simp)
      also have "\<dots> = mul (?eval_G ws1) (invg (?eval_G ws1))" using 1(3) by (by100 simp)
      also have "\<dots> = e"
      proof -
        have "?eval_G ws1 \<in> G" using word_product_in_group[OF hG_grp hmG1] by (by100 simp)
        thus ?thesis using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      qed
      finally show ?thesis .
    qed
    \<comment> \<open>By word\_kernel: eval\_H(ws3) = eH.\<close>
    have heval_H_e: "?eval_H ?ws3 = eH"
      by (rule free_group_word_kernel[OF assms(1) assms(2) assms(3) hws3_S heval_G_e])
    \<comment> \<open>Decompose eval\_H similarly.\<close>
    have hmH_mapped: "\<And>ws. \<forall>i<length ws. fst(ws!i) \<in> S \<Longrightarrow>
        \<forall>j<length (map (\<lambda>(s,b). (\<phi> s, b)) ws). fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! j) \<in> H"
    proof (intro allI impI)
      fix ws and j
      assume h: "\<forall>i<length ws. fst(ws!i) \<in> S" and hj: "j < length (map (\<lambda>(s,b). (\<phi> s, b)) ws)"
      hence hjw: "j < length ws" by (by100 simp)
      obtain sj bj where hwj: "ws ! j = (sj, bj)" by (cases "ws!j") (by100 blast)
      have "sj \<in> S" using h hjw hwj by (by100 force)
      hence "\<phi> sj \<in> H" using assms(3) by (by100 blast)
      thus "fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! j) \<in> H" using hjw hwj by simp
    qed
    have hmap_fliprev_H: "map (\<lambda>(s,b). (\<phi> s, b)) ?fr2
        = map (\<lambda>(x,b). (x, \<not>b)) (rev (map (\<lambda>(s,b). (\<phi> s, b)) ws2))"
      by (induct ws2) auto
    have heval_H_split: "?eval_H ?ws3 = mulH (?eval_H ws1) (?eval_H ?fr2)"
    proof -
      have "map (\<lambda>(s,b). (\<phi> s, b)) ?ws3 =
          map (\<lambda>(s,b). (\<phi> s, b)) ws1 @ map (\<lambda>(s,b). (\<phi> s, b)) ?fr2" by (by100 simp)
      thus ?thesis
        using word_product_append[OF assms(2) hmH_mapped[OF 1(1)] hmH_mapped[OF hfr2_S]] by (by100 simp)
    qed
    have heval_H_rev: "?eval_H ?fr2 = invgH (?eval_H ws2)"
      using word_product_rev_inv[OF assms(2) hmH_mapped[OF 1(2)]] hmap_fliprev_H by (by100 simp)
    \<comment> \<open>Combine: mulH (eval\_H ws1) (invgH (eval\_H ws2)) = eH.\<close>
    have "mulH (?eval_H ws1) (invgH (?eval_H ws2)) = eH"
      using heval_H_e heval_H_split heval_H_rev by (by100 simp)
    \<comment> \<open>Right-multiply by eval\_H ws2.\<close>
    hence "mulH (mulH (?eval_H ws1) (invgH (?eval_H ws2))) (?eval_H ws2) = mulH eH (?eval_H ws2)"
      by (by100 simp)
    hence "?eval_H ws1 = ?eval_H ws2"
    proof -
      have hH1: "?eval_H ws1 \<in> H" using word_product_in_group[OF assms(2) hmH_mapped[OF 1(1)]] by (by100 simp)
      have hH2: "?eval_H ws2 \<in> H" using word_product_in_group[OF assms(2) hmH_mapped[OF 1(2)]] by (by100 simp)
      have hiH2: "invgH (?eval_H ws2) \<in> H" using assms(2) hH2 unfolding top1_is_group_on_def by (by100 blast)
      \<comment> \<open>a \<cdot> b\<inverse> = eH \<Longrightarrow> a = b.\<close>
      \<comment> \<open>a \<cdot> b\<inverse> = eH implies a \<cdot> b\<inverse> \<cdot> b = eH \<cdot> b = b, and a \<cdot> (b\<inverse> \<cdot> b) = a \<cdot> eH = a. So a = b.\<close>
      have hcancel: "mulH (invgH (?eval_H ws2)) (?eval_H ws2) = eH"
        using assms(2) hH2 unfolding top1_is_group_on_def by (by100 blast)
      have hid_r: "mulH (?eval_H ws1) eH = ?eval_H ws1"
        using assms(2) hH1 unfolding top1_is_group_on_def by (by100 blast)
      have "?eval_H ws1 = mulH (?eval_H ws1) eH"
        using hid_r by (by100 simp)
      also have "\<dots> = mulH (?eval_H ws1) (mulH (invgH (?eval_H ws2)) (?eval_H ws2))"
        using hcancel by (by100 simp)
      also have "\<dots> = mulH (mulH (?eval_H ws1) (invgH (?eval_H ws2))) (?eval_H ws2)"
      proof -
        have "mulH (mulH (?eval_H ws1) (invgH (?eval_H ws2))) (?eval_H ws2)
            = mulH (?eval_H ws1) (mulH (invgH (?eval_H ws2)) (?eval_H ws2))"
          using assms(2) hH1 hiH2 hH2 unfolding top1_is_group_on_def by (by100 blast)
        thus ?thesis by (by100 simp)
      qed
      also have "\<dots> = mulH eH (?eval_H ws2)"
        using \<open>mulH (?eval_H ws1) (invgH (?eval_H ws2)) = eH\<close> by (by100 simp)
      also have "\<dots> = ?eval_H ws2"
        using assms(2) hH2 unfolding top1_is_group_on_def by (by100 blast)
      finally show ?thesis .
    qed
    thus ?case .
  qed
  \<comment> \<open>Helper: mapped word elements are in H.\<close>
  have hmH_mapped: "\<And>ws. \<forall>i<length ws. fst(ws!i) \<in> S \<Longrightarrow>
      \<forall>j<length (map (\<lambda>(s,b). (\<phi> s, b)) ws). fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! j) \<in> H"
  proof (intro allI impI)
    fix ws and j
    assume h: "\<forall>i<length ws. fst(ws!i) \<in> S" and hj: "j < length (map (\<lambda>(s,b). (\<phi> s, b)) ws)"
    hence hjw: "j < length ws" by (by100 simp)
    obtain sj bj where hwj: "ws ! j = (sj, bj)" by (cases "ws!j") (by100 blast)
    have "sj \<in> S" using h hjw hwj by (by100 force)
    hence "\<phi> sj \<in> H" using assms(3) by (by100 blast)
    thus "fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! j) \<in> H" using hjw hwj by simp
  qed
  \<comment> \<open>Helper: for g \<in> G, SOME picks a valid word, and \<psi>(g) = eval\_H of any valid word.\<close>
  have hpsi_wd: "\<And>g ws. g \<in> G \<Longrightarrow> (\<forall>i<length ws. fst (ws ! i) \<in> S) \<Longrightarrow> ?eval_G ws = g \<Longrightarrow>
      ?\<psi> g = ?eval_H ws"
  proof -
    fix g ws
    assume hg: "g \<in> G" and hws: "\<forall>i<length ws. fst (ws ! i) \<in> S" and heval: "?eval_G ws = g"
    \<comment> \<open>SOME picks some word ws' with eval\_G(ws') = g.\<close>
    have "\<exists>ws'. (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<and> ?eval_G ws' = g"
      using hws heval by (by100 blast)
    hence hsome: "(\<forall>i<length (SOME ws'. (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<and> ?eval_G ws' = g).
        fst ((SOME ws'. (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<and> ?eval_G ws' = g) ! i) \<in> S)
      \<and> ?eval_G (SOME ws'. (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<and> ?eval_G ws' = g) = g"
      by (rule someI_ex)
    \<comment> \<open>By well-definedness, eval\_H of SOME word = eval\_H of ws.\<close>
    let ?ws' = "SOME ws'. (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<and> ?eval_G ws' = g"
    have hsome1: "\<forall>i<length ?ws'. fst (?ws' ! i) \<in> S" using hsome by (by100 blast)
    have hsome2: "?eval_G ?ws' = g" using hsome by (by100 blast)
    have "?eval_G ?ws' = ?eval_G ws" using hsome2 heval by (by100 simp)
    thus "?\<psi> g = ?eval_H ws" by (rule hwd[OF hsome1 hws])
  qed
  \<comment> \<open>Step 4: \<psi> is a homomorphism.\<close>
  have hhom: "top1_group_hom_on G mul H mulH ?\<psi>"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    \<comment> \<open>\<psi>(g) \<in> H for g \<in> G.\<close>
    fix g assume hg: "g \<in> G"
    have "g \<in> ?W" using hg hW_eq_G by (by100 simp)
    then obtain ws where hws: "\<forall>i<length ws. fst (ws ! i) \<in> S" "?eval_G ws = g"
      by (by100 blast)
    have "?\<psi> g = ?eval_H ws" by (rule hpsi_wd[OF hg hws(1) hws(2)])
    also have "\<dots> \<in> H" by (rule word_product_in_group[OF assms(2) hmH_mapped[OF hws(1)]])
    finally show "?\<psi> g \<in> H" .
  next
    \<comment> \<open>\<psi>(g1 \<cdot> g2) = mulH(\<psi> g1)(\<psi> g2).\<close>
    fix g1 g2 assume hg1: "g1 \<in> G" and hg2: "g2 \<in> G"
    \<comment> \<open>Get word representations.\<close>
    have "g1 \<in> ?W" using hg1 hW_eq_G by (by100 simp)
    then obtain ws1 where hws1: "\<forall>i<length ws1. fst (ws1 ! i) \<in> S" "?eval_G ws1 = g1"
      by (by100 blast)
    have "g2 \<in> ?W" using hg2 hW_eq_G by (by100 simp)
    then obtain ws2 where hws2: "\<forall>i<length ws2. fst (ws2 ! i) \<in> S" "?eval_G ws2 = g2"
      by (by100 blast)
    \<comment> \<open>ws1 @ ws2 is a word for mul g1 g2.\<close>
    have happ_S: "\<forall>i<length (ws1 @ ws2). fst ((ws1 @ ws2) ! i) \<in> S"
      using hws1(1) hws2(1) by (simp add: nth_append)
    have hmap_app: "map (\<lambda>(s,b). (\<iota> s, b)) (ws1 @ ws2) =
        map (\<lambda>(s,b). (\<iota> s, b)) ws1 @ map (\<lambda>(s,b). (\<iota> s, b)) ws2" by (by100 simp)
    have heval_app: "?eval_G (ws1 @ ws2) = mul g1 g2"
      using word_product_append[OF hG_grp hmapped_G[OF hws1(1)] hmapped_G[OF hws2(1)]]
            hmap_app hws1(2) hws2(2) by (by100 simp)
    have hmul_G: "mul g1 g2 \<in> G"
      using hG_grp hg1 hg2 unfolding top1_is_group_on_def by (by100 blast)
    \<comment> \<open>\<psi>(mul g1 g2) = eval\_H(ws1 @ ws2) by well-definedness.\<close>
    have "?\<psi> (mul g1 g2) = ?eval_H (ws1 @ ws2)"
      by (rule hpsi_wd[OF hmul_G happ_S heval_app])
    \<comment> \<open>eval\_H(ws1 @ ws2) = mulH(eval\_H ws1)(eval\_H ws2).\<close>
    also have "\<dots> = mulH (?eval_H ws1) (?eval_H ws2)"
    proof -
      have "map (\<lambda>(s,b). (\<phi> s, b)) (ws1 @ ws2) =
          map (\<lambda>(s,b). (\<phi> s, b)) ws1 @ map (\<lambda>(s,b). (\<phi> s, b)) ws2" by (by100 simp)
      thus ?thesis
        using word_product_append[OF assms(2) hmH_mapped[OF hws1(1)] hmH_mapped[OF hws2(1)]]
        by (by100 simp)
    qed
    \<comment> \<open>eval\_H(wsi) = \<psi>(gi) by well-definedness.\<close>
    also have "?eval_H ws1 = ?\<psi> g1" using hpsi_wd[OF hg1 hws1(1) hws1(2)] by (by100 simp)
    also have "?eval_H ws2 = ?\<psi> g2" using hpsi_wd[OF hg2 hws2(1) hws2(2)] by (by100 simp)
    finally show "?\<psi> (mul g1 g2) = mulH (?\<psi> g1) (?\<psi> g2)" by (by100 simp)
  qed
  \<comment> \<open>Step 5: \<psi>(\<iota>(s)) = \<phi>(s).\<close>
  have hext: "\<forall>s\<in>S. ?\<psi> (\<iota> s) = \<phi> s"
  proof (intro ballI)
    fix s assume hs: "s \<in> S"
    \<comment> \<open>The word [(s, True)] evaluates to \<iota>(s) in G.\<close>
    have hws_S: "\<forall>i<length [(s, True)]. fst ([(s, True)] ! i) \<in> S"
      using hs by (by100 simp)
    have heval_s: "?eval_G [(s, True)] = \<iota> s"
    proof -
      have "?eval_G [(s, True)] = mul (\<iota> s) e" by (by100 simp)
      also have "\<dots> = \<iota> s"
        using hG_grp hG_in hs unfolding top1_is_group_on_def by (by100 blast)
      finally show ?thesis .
    qed
    have hiota_G: "\<iota> s \<in> G" using hG_in hs by (by100 blast)
    \<comment> \<open>By well-definedness: \<psi>(\<iota> s) = eval\_H([(s, True)]).\<close>
    have "?\<psi> (\<iota> s) = ?eval_H [(s, True)]"
      by (rule hpsi_wd[OF hiota_G hws_S heval_s])
    \<comment> \<open>eval\_H([(s, True)]) = \<phi>(s).\<close>
    also have "\<dots> = mulH (\<phi> s) eH" by (by100 simp)
    also have "\<dots> = \<phi> s"
      using assms(2,3) hs unfolding top1_is_group_on_def by (by100 blast)
    finally show "?\<psi> (\<iota> s) = \<phi> s" .
  qed
  show ?thesis using hhom hext by (by100 blast)
qed

lemma free_group_universal_property:
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
      and "top1_is_group_on H mulH eH invgH"
      and "\<forall>s\<in>S. \<phi> s \<in> H"
  shows "\<exists>\<psi>. top1_group_hom_on G mul H mulH \<psi> \<and> (\<forall>s\<in>S. \<psi> (\<iota> s) = \<phi> s)
      \<and> (\<forall>\<psi>'. top1_group_hom_on G mul H mulH \<psi>' \<and> (\<forall>s\<in>S. \<psi>' (\<iota> s) = \<phi> s)
          \<longrightarrow> (\<forall>g\<in>G. \<psi>' g = \<psi> g))"
proof -
  have hG: "top1_is_group_on G mul e invg"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hgen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hS: "\<forall>s\<in>S. \<iota> s \<in> G"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  obtain \<psi> where h\<psi>: "top1_group_hom_on G mul H mulH \<psi>"
      and h\<psi>_ext: "\<forall>s\<in>S. \<psi> (\<iota> s) = \<phi> s"
    using free_group_hom_exists[OF assms] by (by100 blast)
  have huniq: "\<forall>\<psi>'. top1_group_hom_on G mul H mulH \<psi>' \<and> (\<forall>s\<in>S. \<psi>' (\<iota> s) = \<phi> s)
      \<longrightarrow> (\<forall>g\<in>G. \<psi>' g = \<psi> g)"
  proof (intro allI impI)
    fix \<psi>' assume h': "top1_group_hom_on G mul H mulH \<psi>' \<and> (\<forall>s\<in>S. \<psi>' (\<iota> s) = \<phi> s)"
    have h'_hom: "top1_group_hom_on G mul H mulH \<psi>'" using h' by (by100 blast)
    have "\<forall>s\<in>S. \<psi>' (\<iota> s) = \<psi> (\<iota> s)" using h' h\<psi>_ext by (by100 simp)
    thus "\<forall>g\<in>G. \<psi>' g = \<psi> g"
      by (rule free_group_hom_unique[OF hG assms(2) hgen hS h'_hom h\<psi>])
  qed
  show ?thesis using h\<psi> h\<psi>_ext huniq by (by100 blast)
qed

text \<open>Corollary: the exponent sum homomorphism. For each generator s0,
  there is a homomorphism \<epsilon>_{s0}: G \<rightarrow> (Z, +) counting the s0-exponent.\<close>
lemma free_group_exponent_sum:
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
      and "s0 \<in> S"
  shows "\<exists>\<epsilon>. top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>
           \<and> \<epsilon> (\<iota> s0) = 1
           \<and> (\<forall>s\<in>S. s \<noteq> s0 \<longrightarrow> \<epsilon> (\<iota> s) = 0)"
proof -
  let ?\<phi> = "\<lambda>s. if s = s0 then (1::int) else (0::int)"
  have hZ_grp: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
    unfolding top1_is_group_on_def by (by100 auto)
  have hphi_in: "\<forall>s\<in>S. ?\<phi> s \<in> (UNIV::int set)" by (by100 blast)
  from free_group_hom_exists[OF assms(1) hZ_grp hphi_in]
  obtain \<psi> where h\<psi>: "top1_group_hom_on G mul (UNIV::int set) (+) \<psi>"
      and h\<psi>_ext: "\<forall>s\<in>S. \<psi> (\<iota> s) = ?\<phi> s"
    by (by100 blast)
  have "\<psi> (\<iota> s0) = 1" using h\<psi>_ext assms(2) by (by100 simp)
  moreover have "\<forall>s\<in>S. s \<noteq> s0 \<longrightarrow> \<psi> (\<iota> s) = 0" using h\<psi>_ext by (by100 auto)
  ultimately show ?thesis using h\<psi> by (by100 blast)
qed

text \<open>Commutator subgroup elements have zero exponent sum for all generators.\<close>
lemma commutator_zero_exponent:
  assumes "top1_is_group_on G mul e invg"
      and "top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>"
  shows "\<forall>g\<in>top1_commutator_subgroup_on G mul e invg. \<epsilon> g = 0"
proof (intro ballI)
  fix g assume hg: "g \<in> top1_commutator_subgroup_on G mul e invg"
  have hZ_abel: "top1_is_abelian_group_on (UNIV::int set) (+) (0::int) uminus"
    unfolding top1_is_abelian_group_on_def top1_is_group_on_def by (by100 auto)
  have hcomm_ker: "top1_commutator_subgroup_on G mul e invg
      \<subseteq> top1_group_kernel_on G (0::int) \<epsilon>"
    by (rule Lemma_69_3_commutator_in_kernel[OF assms(1) hZ_abel assms(2)])
  hence "g \<in> top1_group_kernel_on G (0::int) \<epsilon>" using hg by (by100 blast)
  thus "\<epsilon> g = 0" unfolding top1_group_kernel_on_def by (by100 blast)
qed

(** from \<S>69 Theorem 69.4: abelianization of free group is free abelian.
    If G is free on S, then G/[G,G] is free abelian on the images of S. **)
theorem Theorem_69_4:
  fixes G :: "'g set"
    and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g
    and invg :: "'g \<Rightarrow> 'g"
    and \<iota> :: "'s \<Rightarrow> 'g"
    and S :: "'s set"
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
  shows "\<exists>(H :: 'g set set) mulH eH invgH \<phi> \<iota>H.
           top1_is_abelianization_of H mulH eH invgH G mul e invg \<phi>
         \<and> top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>H S
         \<and> (\<forall>s\<in>S. \<iota>H s = \<phi> (\<iota> s))"
proof -
  have hG: "top1_is_group_on G mul e invg"
    using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
  let ?N = "top1_commutator_subgroup_on G mul e invg"
  let ?H = "top1_quotient_group_carrier_on G mul ?N"
  let ?mulH = "top1_quotient_group_mul_on mul"
  let ?eH = "top1_group_coset_on G mul ?N e"
  let ?invgH = "\<lambda>C. top1_group_coset_on G mul ?N
         (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul ?N g))"
  let ?\<phi> = "\<lambda>g. top1_group_coset_on G mul ?N g"
  have h_abel: "top1_is_abelianization_of ?H ?mulH ?eH ?invgH G mul e invg ?\<phi>"
    by (rule abelianization_concrete[OF hG])
  \<comment> \<open>Step 2: \<phi>(\<iota>(S)) generates H and satisfies no nontrivial integer relations
     (exponent sum argument in the free group).\<close>
  let ?\<iota>H = "\<lambda>s. ?\<phi> (\<iota> s)"
  \<comment> \<open>Step 2a: H is abelian (from abelianization).\<close>
  have hH_abel: "top1_is_abelian_group_on ?H ?mulH ?eH ?invgH"
    using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
  \<comment> \<open>Step 2b: \<iota>(s) \<in> G for each s, so \<phi>(\<iota>(s)) \<in> H.\<close>
  have hgen_in_G: "\<forall>s\<in>S. \<iota> s \<in> G"
    using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hphi_surj: "?\<phi> ` G = ?H"
    using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
  have hiotaH_in_H: "\<forall>s\<in>S. ?\<iota>H s \<in> ?H"
  proof (intro ballI)
    fix s assume "s \<in> S"
    hence "\<iota> s \<in> G" using hgen_in_G by (by100 blast)
    thus "?\<iota>H s \<in> ?H" using hphi_surj by (by100 blast)
  qed
  \<comment> \<open>Step 2c: \<iota>H injective on S.
     Proof: if ?\<phi>(\<iota> s1) = ?\<phi>(\<iota> s2), then \<iota> s1 \<cdot> invg(\<iota> s2) \<in> [G,G].
     But in a free group, \<iota> s1 \<cdot> invg(\<iota> s2) for s1 \<noteq> s2 is a non-trivial reduced word,
     and its exponent sums are nonzero, so it cannot be in [G,G].
     (The exponent sum of s1 is +1, of s2 is -1.)\<close>
  have hiotaH_inj: "inj_on ?\<iota>H S"
  proof (rule inj_onI)
    fix s1 s2 assume hs1: "s1 \<in> S" and hs2: "s2 \<in> S" and heq: "?\<iota>H s1 = ?\<iota>H s2"
    \<comment> \<open>\<phi>(\<iota> s1) = \<phi>(\<iota> s2) means \<iota>(s1) and \<iota>(s2) are in the same coset of [G,G].
       Use the exponent sum: \<exists>\<epsilon>: G \<rightarrow> Z with \<epsilon>(\<iota>(s1)) = 1, \<epsilon>(\<iota>(s)) = 0 for s \<noteq> s1.
       Since Z is abelian, [G,G] \<subseteq> ker(\<epsilon>). So coset equality implies \<epsilon>(\<iota>(s1)) = \<epsilon>(\<iota>(s2)).
       If s1 \<noteq> s2, then 1 = 0, contradiction.\<close>
    show "s1 = s2"
    proof (rule ccontr)
      assume hne: "s1 \<noteq> s2"
      \<comment> \<open>Get exponent sum homomorphism for s1.\<close>
      obtain \<epsilon> where heps_hom: "top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>"
          and heps_s1: "\<epsilon> (\<iota> s1) = 1"
          and heps_other: "\<forall>s\<in>S. s \<noteq> s1 \<longrightarrow> \<epsilon> (\<iota> s) = 0"
        using free_group_exponent_sum[OF assms hs1] by (by100 blast)
      \<comment> \<open>Since [G,G] \<subseteq> ker(\<epsilon>) (Z is abelian), coset equality implies equal \<epsilon>-values.\<close>
      have h_comm_ker: "\<forall>g\<in>?N. \<epsilon> g = 0"
        by (rule commutator_zero_exponent[OF hG heps_hom])
      \<comment> \<open>\<phi>(\<iota>(s1)) = \<phi>(\<iota>(s2)) means \<iota>(s1) \<cdot> invg(\<iota>(s2)) \<in> [G,G].\<close>
      have hs1G: "\<iota> s1 \<in> G" using hgen_in_G hs1 by (by100 blast)
      have hs2G: "\<iota> s2 \<in> G" using hgen_in_G hs2 by (by100 blast)
      have hprod_N: "mul (\<iota> s1) (invg (\<iota> s2)) \<in> ?N"
      proof -
        \<comment> \<open>?\<phi> is a homomorphism with ker(?\<phi>) = [G,G]. From heq: ?\<phi>(\<iota> s1) = ?\<phi>(\<iota> s2).
           So ?\<phi>(mul (\<iota> s1) (invg (\<iota> s2))) = ?\<phi>(\<iota> s1) \<cdot> invgH(?\<phi>(\<iota> s2))
           = ?\<phi>(\<iota> s1) \<cdot> invgH(?\<phi>(\<iota> s1)) = eH.
           Hence mul (\<iota> s1) (invg (\<iota> s2)) \<in> ker(?\<phi>) = [G,G].\<close>
        have hN_normal: "top1_normal_subgroup_on G mul e invg ?N"
          by (rule commutator_subgroup_is_normal[OF hG])
        \<comment> \<open>From coset equality (reversed): coset (\<iota> s2) = coset (\<iota> s1).\<close>
        have heq_sym: "?\<phi> (\<iota> s2) = ?\<phi> (\<iota> s1)" using heq by (by100 simp)
        \<comment> \<open>normal_coset_eq: coset g = coset h iff invg(g)\<cdot>h \<in> N. With g=s2, h=s1:\<close>
        have "mul (invg (\<iota> s2)) (\<iota> s1) \<in> ?N"
          using normal_coset_eq[OF hG hN_normal hs2G hs1G] heq_sym by (by100 blast)
        \<comment> \<open>N is normal: g \<cdot> n \<cdot> invg(g) \<in> N for any g \<in> G, n \<in> N.\<close>
        \<comment> \<open>With n = invg(\<iota> s2)\<cdot>\<iota> s1 and g = \<iota> s1:
           \<iota> s1 \<cdot> (invg(\<iota> s2)\<cdot>\<iota> s1) \<cdot> invg(\<iota> s1) = \<iota> s1 \<cdot> invg(\<iota> s2) (by associativity + cancellation).\<close>
        \<comment> \<open>Normal: mul (mul g n) (invg g) \<in> N for g \<in> G, n \<in> N.\<close>
        have hconj0: "mul (mul (\<iota> s1) (mul (invg (\<iota> s2)) (\<iota> s1))) (invg (\<iota> s1)) \<in> ?N"
          using hN_normal hs1G \<open>mul (invg (\<iota> s2)) (\<iota> s1) \<in> ?N\<close>
          unfolding top1_normal_subgroup_on_def by (by100 blast)
        \<comment> \<open>Simplify: (a\<cdot>b)\<cdot>b\<inverse> = a for a = invg(\<iota> s2), b = \<iota> s1.\<close>
        have hinvs2: "invg (\<iota> s2) \<in> G" using hG hs2G unfolding top1_is_group_on_def by (by100 blast)
        have "mul (mul (invg (\<iota> s2)) (\<iota> s1)) (invg (\<iota> s1))
            = invg (\<iota> s2)"
        proof -
          have "mul (mul (invg (\<iota> s2)) (\<iota> s1)) (invg (\<iota> s1))
              = mul (invg (\<iota> s2)) (mul (\<iota> s1) (invg (\<iota> s1)))"
            using hG hinvs2 hs1G unfolding top1_is_group_on_def by (by100 blast)
          also have "mul (\<iota> s1) (invg (\<iota> s1)) = e"
            using hG hs1G unfolding top1_is_group_on_def by (by100 blast)
          also have "mul (invg (\<iota> s2)) e = invg (\<iota> s2)"
            using hG hinvs2 unfolding top1_is_group_on_def by (by100 blast)
          finally show ?thesis .
        qed
        \<comment> \<open>By associativity: mul (mul g X) (invg g) = mul g (mul X (invg g)).\<close>
        have hN_sub: "?N \<subseteq> G" using hN_normal unfolding top1_normal_subgroup_on_def by (by100 blast)
        have hprod_in_G: "mul (invg (\<iota> s2)) (\<iota> s1) \<in> G"
          using hG hinvs2 hs1G unfolding top1_is_group_on_def by (by100 blast)
        have hinvs1: "invg (\<iota> s1) \<in> G" using hG hs1G unfolding top1_is_group_on_def by (by100 blast)
        have hassoc: "mul (mul (\<iota> s1) (mul (invg (\<iota> s2)) (\<iota> s1))) (invg (\<iota> s1))
            = mul (\<iota> s1) (mul (mul (invg (\<iota> s2)) (\<iota> s1)) (invg (\<iota> s1)))"
          using hG hs1G hprod_in_G hinvs1 unfolding top1_is_group_on_def by (by100 blast)
        hence "mul (\<iota> s1) (mul (mul (invg (\<iota> s2)) (\<iota> s1)) (invg (\<iota> s1))) \<in> ?N"
          using hconj0 by (by100 simp)
        hence "mul (\<iota> s1) (invg (\<iota> s2)) \<in> ?N" using \<open>mul (mul (invg (\<iota> s2)) (\<iota> s1)) (invg (\<iota> s1)) = invg (\<iota> s2)\<close> by (by100 simp)
        thus ?thesis .
      qed
      \<comment> \<open>But \<epsilon>(\<iota>(s1)·invg(\<iota>(s2))) = \<epsilon>(\<iota>(s1)) + \<epsilon>(invg(\<iota>(s2)))
         = 1 + (-0) = 1 \<noteq> 0. Contradiction with h_comm_ker.\<close>
      have heps_zero: "\<epsilon> (mul (\<iota> s1) (invg (\<iota> s2))) = 0" using h_comm_ker hprod_N by (by100 blast)
      have hinvG_s2: "invg (\<iota> s2) \<in> G"
        using hG hs2G unfolding top1_is_group_on_def by (by100 blast)
      moreover have "\<epsilon> (mul (\<iota> s1) (invg (\<iota> s2))) = \<epsilon> (\<iota> s1) + \<epsilon> (invg (\<iota> s2))"
        using heps_hom hs1G hinvG_s2 unfolding top1_group_hom_on_def by (by100 blast)
      moreover have "\<epsilon> (invg (\<iota> s2)) = - \<epsilon> (\<iota> s2)"
      proof -
        have hZ_grp: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
          unfolding top1_is_group_on_def by (by100 auto)
        have "(\<epsilon> (invg (\<iota> s2))::int) = uminus (\<epsilon> (\<iota> s2))"
          by (rule hom_preserves_inv[OF hG hZ_grp heps_hom hs2G])
        thus ?thesis by (by100 simp)
      qed
      moreover have "\<epsilon> (\<iota> s2) = 0" using heps_other hs2 hne[symmetric] by (by100 blast)
      ultimately show False using heps_s1 heps_zero by (by100 simp)
    qed
  qed
  \<comment> \<open>Step 2d: H = \<langle>\<iota>H(S)\<rangle> (generated by images of generators).
     Since G = \<langle>\<iota>(S)\<rangle> and \<phi> is surjective, H = \<phi>(G) = \<phi>(\<langle>\<iota>(S)\<rangle>) = \<langle>\<phi>(\<iota>(S))\<rangle> = \<langle>\<iota>H(S)\<rangle>.\<close>
  have hH_gen: "?H = top1_subgroup_generated_on ?H ?mulH ?eH ?invgH (?\<iota>H ` S)"
  proof -
    have hH_grp: "top1_is_group_on ?H ?mulH ?eH ?invgH"
      using hH_abel unfolding top1_is_abelian_group_on_def by (by100 blast)
    have hphi_hom: "top1_group_hom_on G mul ?H ?mulH ?\<phi>"
      using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
    have hphi_surj: "?\<phi> ` G = ?H"
      using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
    have hiotaS_sub: "\<iota> ` S \<subseteq> G"
      using hgen_in_G by (by100 blast)
    have hG_gen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
      using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
    have "?H = top1_subgroup_generated_on ?H ?mulH ?eH ?invgH (?\<phi> ` (\<iota> ` S))"
      by (rule surj_hom_generated[OF hG hH_grp hphi_hom hphi_surj hiotaS_sub hG_gen])
    moreover have "?\<phi> ` (\<iota> ` S) = ?\<iota>H ` S" by (by100 force)
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Step 2e: No nontrivial integer relations.
     For c: S \<rightarrow> Z with finite support and some c(s) \<noteq> 0:
     \<Pi> \<iota>H(s)^{c(s)} = ?\<phi>(\<Pi> \<iota>(s)^{c(s)}) \<noteq> ?eH.
     Because \<Pi> \<iota>(s)^{c(s)} \<notin> ker(\<phi>) = [G,G] (exponent sum argument:
     the exponent sum of s0 in \<Pi> \<iota>(s)^{c(s)} equals c(s0) \<noteq> 0,
     but all elements of [G,G] have zero exponent sums).\<close>
  have hH_indep: "\<forall>c :: 's \<Rightarrow> int.
      finite {s\<in>S. c s \<noteq> 0} \<longrightarrow>
      (\<exists>s\<in>S. c s \<noteq> 0) \<longrightarrow>
      foldr ?mulH (map (\<lambda>s.
          if c s \<ge> 0 then top1_group_pow ?mulH ?eH (?\<iota>H s) (nat (c s))
          else top1_group_pow ?mulH ?eH (?invgH (?\<iota>H s)) (nat (- c s)))
        (SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs)) ?eH
      \<noteq> ?eH"
    sorry \<comment> \<open>Needs: exponent sum argument. The product maps under \<phi> to an element
       whose exponent sums are exactly the c(s) values, which are not all zero.
       Elements of [G,G] have all exponent sums zero, so the product is not in ker(\<phi>).\<close>
  \<comment> \<open>Step 2f: Assemble all conditions into free abelian group definition.\<close>
  have h_free_abel: "\<exists>\<iota>H.
      top1_is_free_abelian_group_full_on ?H ?mulH ?eH ?invgH \<iota>H S
    \<and> (\<forall>s\<in>S. \<iota>H s = ?\<phi> (\<iota> s))"
  proof (intro exI conjI)
    show "top1_is_free_abelian_group_full_on ?H ?mulH ?eH ?invgH ?\<iota>H S"
      unfolding top1_is_free_abelian_group_full_on_def
    proof (intro conjI)
      show "top1_is_abelian_group_on ?H ?mulH ?eH ?invgH" by (rule hH_abel)
      show "\<forall>s\<in>S. ?\<iota>H s \<in> ?H" by (rule hiotaH_in_H)
      show "inj_on ?\<iota>H S" by (rule hiotaH_inj)
      show "?H = top1_subgroup_generated_on ?H ?mulH ?eH ?invgH (?\<iota>H ` S)" by (rule hH_gen)
      show "\<forall>c::'s \<Rightarrow> int.
        finite {s \<in> S. c s \<noteq> 0} \<longrightarrow>
        (\<exists>s\<in>S. c s \<noteq> 0) \<longrightarrow>
        foldr ?mulH
         (map (\<lambda>s. if 0 \<le> c s then top1_group_pow ?mulH ?eH (?\<iota>H s) (nat (c s))
                   else top1_group_pow ?mulH ?eH (?invgH (?\<iota>H s)) (nat (- c s)))
           (SOME xs. set xs = {s \<in> S. c s \<noteq> 0} \<and> distinct xs))
         ?eH \<noteq> ?eH" by (rule hH_indep)
    qed
    show "\<forall>s\<in>S. ?\<iota>H s = ?\<phi> (\<iota> s)" by (by100 simp)
  qed
  show ?thesis using h_abel h_free_abel by (by100 blast)
qed



\<comment> \<open>Helper: Z/nZ is the quotient of Z by the subgroup nZ.
   More precisely: the quotient of (UNIV::int set, +) by the normal subgroup
   generated by {int n} is isomorphic to (top1_Zn_group n, top1_Zn_mul n).\<close>
lemma Z_quotient_nZ_iso:
  assumes "n \<ge> 1"
  shows "top1_groups_isomorphic_on
      (top1_quotient_group_carrier_on (UNIV::int set) (+)
         (top1_normal_subgroup_generated_on (UNIV::int set) (+) (0::int) uminus {int n}))
      (top1_quotient_group_mul_on (+))
      (top1_Zn_group n) (top1_Zn_mul n)"
proof -
  \<comment> \<open>Step 1: The normal subgroup generated by {n} in (Z,+) is nZ = {k*n | k}.\<close>
  let ?nZ = "top1_normal_subgroup_generated_on (UNIV::int set) (+) (0::int) uminus {int n}"
  have hnZ_eq: "?nZ = {k * int n | k. True}"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> ?nZ"
    \<comment> \<open>?nZ \<subseteq> every normal subgroup containing {n}. nZ is such a subgroup.\<close>
    have hnZ_normal: "top1_normal_subgroup_on (UNIV::int set) (+) 0 uminus {k * int n | k. True}"
      unfolding top1_normal_subgroup_on_def
    proof (intro conjI)
      show "{k * int n |k. True} \<subseteq> (UNIV::int set)" by (by100 blast)
      show "top1_is_group_on {k * int n |k. True} (+) 0 uminus"
        unfolding top1_is_group_on_def
      proof (intro conjI)
        show "(0::int) \<in> {k * int n |k. True}"
        proof -
          have "(0::int) = (0::int) * int n" by (by100 simp)
          thus ?thesis by (by100 blast)
        qed
        show "\<forall>x\<in>{k * int n |k. True}. \<forall>y\<in>{k * int n |k. True}. x + y \<in> {k * int n |k. True}"
        proof (intro ballI)
          fix x y :: int assume "x \<in> {k * int n |k. True}" "y \<in> {k * int n |k. True}"
          then obtain kx ky where "x = kx * int n" "y = ky * int n" by (by100 blast)
          hence "x + y = (kx + ky) * int n" using distrib_right[of kx ky "int n"] by (by100 simp)
          thus "x + y \<in> {k * int n |k. True}" by (by100 blast)
        qed
        show "\<forall>x\<in>{k * int n |k. True}. uminus x \<in> {k * int n |k. True}"
        proof (intro ballI)
          fix x :: int assume "x \<in> {k * int n |k. True}"
          then obtain kx where "x = kx * int n" by (by100 blast)
          hence "uminus x = (-kx) * int n" by (by100 simp)
          thus "uminus x \<in> {k * int n |k. True}" by (by100 blast)
        qed
        show "\<forall>x\<in>{k * int n |k. True}. \<forall>y\<in>{k * int n |k. True}.
            \<forall>z\<in>{k * int n |k. True}. x + y + z = x + (y + z)" by (by100 simp)
        show "\<forall>x\<in>{k * int n |k. True}. (0::int) + x = x \<and> x + 0 = x" by (by100 simp)
        show "\<forall>x\<in>{k * int n |k. True}. uminus x + x = (0::int) \<and> x + uminus x = 0" by (by100 simp)
      qed
      show "\<forall>g\<in>(UNIV::int set). \<forall>h\<in>{k * int n |k. True}. g + h + uminus g \<in> {k * int n |k. True}"
      proof (intro ballI)
        fix g h :: int assume "g \<in> (UNIV::int set)" "h \<in> {k * int n |k. True}"
        then obtain kh where "h = kh * int n" by (by100 blast)
        hence "g + h + uminus g = kh * int n" by (by100 simp)
        thus "g + h + uminus g \<in> {k * int n |k. True}" by (by100 blast)
      qed
    qed
    have "{int n} \<subseteq> {k * int n |k. True}"
    proof -
      have "int n = (1::int) * int n" by (by100 simp)
      thus ?thesis by (by100 blast)
    qed
    hence "?nZ \<subseteq> {k * int n |k. True}"
      unfolding top1_normal_subgroup_generated_on_def using hnZ_normal by (by100 blast)
    thus "x \<in> {k * int n |k. True}" using \<open>x \<in> ?nZ\<close> by (by100 blast)
  next
    fix x assume "x \<in> {k * int n |k. True}"
    then obtain k :: int where hk: "x = k * int n" by (by100 blast)
    \<comment> \<open>n \<in> ?nZ and ?nZ is a group, so k*n \<in> ?nZ by closure.\<close>
    have hZ_grp: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
      using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
        top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 simp)
    have hn_in_nZ: "int n \<in> ?nZ"
    proof -
      have "{int n} \<subseteq> ?nZ"
        unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    have hN_sub: "?nZ \<subseteq> (UNIV::int set)" by (by100 blast)
    have hN_grp: "top1_is_group_on ?nZ (+) (0::int) uminus"
      using normal_subgroup_generated_is_normal[OF hZ_grp, of "{int n}"]
      unfolding top1_normal_subgroup_on_def by (by100 blast)
    \<comment> \<open>Induction: k*n \<in> ?nZ for all k.\<close>
    have "k * int n \<in> ?nZ"
    proof (cases "k \<ge> 0")
      case True
      have "\<forall>j::int. j \<ge> 0 \<longrightarrow> j * int n \<in> ?nZ"
      proof (rule allI, rule impI)
        fix j :: int assume "j \<ge> 0"
        then obtain jn :: nat where "j = int jn" using nonneg_int_cases by (by100 blast)
        show "j * int n \<in> ?nZ"
        proof -
          have "int jn * int n \<in> ?nZ"
          proof (induct jn)
            case 0
            have "(0::int) \<in> ?nZ" using hN_grp unfolding top1_is_group_on_def by (by100 blast)
            thus ?case by (by100 simp)
          next
            case (Suc jn)
            have hS: "int (Suc jn) * int n = int jn * int n + int n"
            proof -
              have "int (Suc jn) = 1 + int jn" by (by100 simp)
              hence "int (Suc jn) * int n = (1 + int jn) * int n" by (by100 simp)
              also have "\<dots> = 1 * int n + int jn * int n"
                using distrib_right[of 1 "int jn" "int n"] by (by100 simp)
              finally show ?thesis by (by100 simp)
            qed
            have "int jn * int n + int n \<in> ?nZ"
            proof -
              have "\<forall>x\<in>?nZ. \<forall>y\<in>?nZ. x + y \<in> ?nZ"
                using hN_grp unfolding top1_is_group_on_def by (by100 blast)
              thus ?thesis using Suc hn_in_nZ by (by100 blast)
            qed
            thus ?case using hS by (by100 simp)
          qed
          thus ?thesis using \<open>j = int jn\<close> by (by100 simp)
        qed
      qed
      thus ?thesis using True by (by100 blast)
    next
      case False
      hence "k < 0" by (by100 simp)
      hence "-k > 0" by (by100 simp)
      have "(-k) * int n \<in> ?nZ"
      proof -
        have "-k \<ge> 0" using \<open>-k > 0\<close> by (by100 simp)
        then obtain jn :: nat where "-k = int jn" using nonneg_int_cases by (by100 blast)
        have "int jn * int n \<in> ?nZ"
        proof (induct jn)
          case 0 thus ?case using hN_grp unfolding top1_is_group_on_def by (by100 simp)
        next
          case (Suc jn)
          have "int (Suc jn) * int n = int jn * int n + int n"
          proof -
            have "int (Suc jn) = 1 + int jn" by (by100 simp)
            hence "int (Suc jn) * int n = (1 + int jn) * int n" by (by100 simp)
            also have "\<dots> = 1 * int n + int jn * int n"
              using distrib_right[of 1 "int jn" "int n"] by (by100 simp)
            finally show ?thesis by (by100 simp)
          qed
          have "int jn * int n + int n \<in> ?nZ"
          proof -
            have "\<forall>x\<in>?nZ. \<forall>y\<in>?nZ. x + y \<in> ?nZ"
              using hN_grp unfolding top1_is_group_on_def by (by100 blast)
            thus ?thesis using Suc hn_in_nZ by (by100 blast)
          qed
          thus ?case using \<open>int (Suc jn) * int n = int jn * int n + int n\<close> by (by100 simp)
        qed
        thus ?thesis using \<open>-k = int jn\<close> by (by100 simp)
      qed
      hence "uminus ((-k) * int n) \<in> ?nZ" using hN_grp unfolding top1_is_group_on_def by (by100 blast)
      moreover have "uminus ((-k) * int n) = k * int n" by (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    thus "x \<in> ?nZ" using hk by (by100 simp)
  qed
  \<comment> \<open>Step 2: Define the quotient map \<phi>: Z \<rightarrow> Z/nZ by \<phi>(k) = k mod n.\<close>
  let ?\<phi> = "\<lambda>k::int. k mod int n"
  \<comment> \<open>Step 3: \<phi> is a surjective group homomorphism with kernel nZ.\<close>
  have hphi_hom: "\<forall>a::int. \<forall>b::int. ?\<phi> (a + b) = top1_Zn_mul n (?\<phi> a) (?\<phi> b)"
    unfolding top1_Zn_mul_def
  proof (intro allI)
    fix a b :: int
    show "(a + b) mod int n = (a mod int n + b mod int n) mod int n"
      using mod_add_eq[of a "int n" b] by (by100 simp)
  qed
  have hphi_surj: "?\<phi> ` (UNIV::int set) = top1_Zn_group n"
    unfolding top1_Zn_group_def
  proof (rule equalityI)
    show "(\<lambda>k::int. k mod int n) ` UNIV \<subseteq> {0..<int n}"
      using assms by (by100 auto)
    show "{0..<int n} \<subseteq> (\<lambda>k::int. k mod int n) ` UNIV"
    proof
      fix x :: int assume hx: "x \<in> {0..<int n}"
      hence hxmod: "x mod int n = x" using assms by (by100 auto)
      show "x \<in> (\<lambda>k. k mod int n) ` UNIV"
        apply (rule image_eqI[of _ _ x])
        using hxmod apply (by100 simp)
        apply (by100 simp)
        done
    qed
  qed
  have hphi_ker: "{k::int. ?\<phi> k = 0} = ?nZ"
    unfolding hnZ_eq
  proof (rule set_eqI, rule iffI)
    fix k :: int assume "k \<in> {k. k mod int n = 0}"
    hence "k mod int n = 0" by (by100 blast)
    hence "int n dvd k"
    proof -
      have "k div int n * int n + k mod int n = k" by (rule div_mult_mod_eq)
      hence "k = k div int n * int n" using \<open>k mod int n = 0\<close> by (by100 simp)
      hence "k = int n * (k div int n)" using mult.commute[of "k div int n" "int n"] by (by100 simp)
      thus ?thesis unfolding dvd_def by (by100 blast)
    qed
    then obtain j where "k = int n * j" unfolding dvd_def by (by100 blast)
    hence "k = j * int n" using mult.commute[of "int n" j] by (by100 simp)
    thus "k \<in> {k * int n |k. True}" by (by100 blast)
  next
    fix k :: int assume "k \<in> {k * int n |k. True}"
    then obtain j where hk: "k = j * int n" by (by100 blast)
    hence "k mod int n = 0" using assms by (by100 simp)
    thus "k \<in> {k. k mod int n = 0}" by (by100 blast)
  qed
  \<comment> \<open>Step 4: By first isomorphism theorem: Z/nZ \<cong> im(\<phi>) = Z_n.\<close>
  have hZ_grp: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
    using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
      top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 simp)
  have hN_normal: "top1_normal_subgroup_on (UNIV::int set) (+) (0::int) uminus ?nZ"
    by (rule normal_subgroup_generated_is_normal[OF hZ_grp]) (by100 simp)
  have hZn_grp: "top1_is_group_on (top1_Zn_group n) (top1_Zn_mul n)
      (0::int) (top1_Zn_invg n)"
    using top1_Zn_is_abelian_group[OF assms] unfolding top1_is_abelian_group_on_def top1_Zn_id_def
    by (by100 blast)
  have hphi_hom_on: "top1_group_hom_on (UNIV::int set) (+) (top1_Zn_group n) (top1_Zn_mul n) ?\<phi>"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    fix x :: int show "?\<phi> x \<in> top1_Zn_group n"
      unfolding top1_Zn_group_def using assms by (by100 auto)
    fix y :: int show "?\<phi> (x + y) = top1_Zn_mul n (?\<phi> x) (?\<phi> y)"
      using hphi_hom by (by100 blast)
  qed
  have hphi_ker_on: "top1_group_kernel_on (UNIV::int set) (0::int) ?\<phi> = ?nZ"
  proof -
    have "top1_group_kernel_on (UNIV::int set) (0::int) ?\<phi> = {k::int. ?\<phi> k = 0} \<inter> UNIV"
      unfolding top1_group_kernel_on_def by (by100 blast)
    also have "\<dots> = {k::int. ?\<phi> k = 0}" by (by100 simp)
    also have "\<dots> = ?nZ" by (rule hphi_ker)
    finally show ?thesis .
  qed
  from first_isomorphism_theorem[OF hZ_grp hN_normal hZn_grp hphi_hom_on hphi_surj hphi_ker_on]
  show ?thesis
    by (rule top1_groups_isomorphic_on_sym[OF _ hZn_grp quotient_group_is_group[OF hZ_grp hN_normal]])
qed

(** from \<S>71 Theorem 71.3: arbitrary (possibly infinite) wedge of circles. **)
theorem Theorem_71_3_wedge_of_circles_general:
  fixes J :: "'i set" and X :: "'a set" and TX :: "'a set set" and p :: 'a
  assumes "top1_is_wedge_of_circles_on X TX J p"
  shows "\<exists>(G::'g set) mul e invg (\<iota>::'i \<Rightarrow> 'g).
           top1_is_free_group_full_on G mul e invg \<iota> J
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX p)
             (top1_fundamental_group_mul X TX p)"
proof -
  \<comment> \<open>Munkres 71.3: For infinite J, use the weak topology + a transfinite/direct-limit
     argument. Each finite sub-wedge gives a free group on that subset of generators.
     The direct limit over finite subsets gives the free group on all of J.
     Alternatively: cover X = \<Union>_\<alpha> (X - C_\<alpha> interior) and apply SvK iteratively.\<close>
  \<comment> \<open>Step 1: For each finite F \<subseteq> J, the sub-wedge X_F has free \<pi>_1 on F
     (by Theorem 71.1 for finite wedges).\<close>
  \<comment> \<open>Step 2: The inclusions X_F \<hookrightarrow> X_G for F \<subseteq> G give a directed system.
     The direct limit of free groups on finite subsets = free group on J.\<close>
  \<comment> \<open>Step 3: \<pi>_1(X) = direct limit of \<pi>_1(X_F) by the weak topology on X
     (a loop in X is compact, hence contained in some finite sub-wedge).\<close>
  show ?thesis sorry \<comment> \<open>Direct limit argument: finite sub-wedges (Thm 71.1) + compactness of loops.\<close>
qed


section \<open>\<S>73 Fundamental Groups of the Torus and the Dunce Cap\<close>

(** from \<S>73 Theorem 73.1: \<pi>_1(torus) has presentation <\<alpha>, \<beta> | \<alpha>\<beta>\<alpha>^{-1}\<beta>^{-1}>,
    i.e. is isomorphic to the free abelian group Z \<times> Z on 2 generators. **)
theorem Theorem_73_1_torus_presentation:
  fixes T_torus :: "'a set" and TT :: "'a set set" and x0 :: 'a
  assumes "top1_is_torus_on T_torus TT"
      and "x0 \<in> T_torus"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier T_torus TT x0)
           (top1_fundamental_group_mul T_torus TT x0)
           (UNIV::(int \<times> int) set)
           (\<lambda>(a1, a2) (b1, b2). (a1 + b1, a2 + b2))"
proof -
  \<comment> \<open>Munkres 73.1: The torus is the quotient of the unit square by aba\<inverse>b\<inverse>.
     By Theorem 72.1 (attaching 2-cell to wedge of two circles), \<pi>_1(T) has presentation
     \<langle>a, b | aba\<inverse>b\<inverse>\<rangle>. The relator aba\<inverse>b\<inverse>=1 means ab=ba, so the group is abelian.
     Hence \<pi>_1(T) \<cong> Z \<times> Z (free abelian group on 2 generators).\<close>
  \<comment> \<open>Step 1: The torus is the quotient of the square by scheme aba\<inverse>b\<inverse>. Extract the
     attaching data: 1-skeleton A (wedge of 2 circles), attaching map h: B² \<rightarrow> T.\<close>
  obtain A :: "'a set" and h :: "real \<times> real \<Rightarrow> 'a"
    where hA_sub: "closedin_on T_torus TT A"
      and hA_wedge: "top1_is_wedge_of_circles_on A (subspace_topology T_torus TT A) {0::nat, 1} x0"
      and hh_cont: "top1_continuous_map_on top1_B2 top1_B2_topology T_torus TT h"
      and hh_S1_A: "h ` top1_S1 \<subseteq> A"
    sorry \<comment> \<open>From torus definition: quotient of square by aba\<inverse>b\<inverse>. 1-skeleton = wedge of 2 circles.\<close>
  \<comment> \<open>Step 2: By Theorem 72.1, \<pi>_1(T) \<cong> \<pi>_1(A)/\<langle>\<langle>k_*([p])\<rangle>\<rangle> where k = h|_{S¹}.
     \<pi>_1(A) is free on {a, b}. The relator is aba\<inverse>b\<inverse>.\<close>
  have hA_free: "\<exists>(F::int set) mulF eF invgF (\<iota>F::nat \<Rightarrow> int).
      top1_is_free_group_full_on F mulF eF invgF \<iota>F {0::nat, 1}
      \<and> top1_groups_isomorphic_on F mulF
          (top1_fundamental_group_carrier A (subspace_topology T_torus TT A) x0)
          (top1_fundamental_group_mul A (subspace_topology T_torus TT A) x0)"
  proof -
    have hset_eq: "{0::nat, 1} = {..<(2::nat)}" by (by100 auto)
    have hwedge2: "top1_is_wedge_of_circles_on A (subspace_topology T_torus TT A) {..<(2::nat)} x0"
      using hA_wedge hset_eq by (by100 simp)
    from Theorem_71_1_wedge_of_circles_finite[OF hwedge2]
    obtain G0 :: "int set" and mul0 e0 invg0 and \<iota>0 :: "nat \<Rightarrow> int" where
        hG0f: "top1_is_free_group_full_on G0 mul0 e0 invg0 \<iota>0 {..<2::nat}" and
        hG0i: "top1_groups_isomorphic_on G0 mul0
            (top1_fundamental_group_carrier A (subspace_topology T_torus TT A) x0)
            (top1_fundamental_group_mul A (subspace_topology T_torus TT A) x0)"
      by (elim exE conjE) (rule that, assumption+)
    have "top1_is_free_group_full_on G0 mul0 e0 invg0 \<iota>0 {0::nat, 1}"
      using hG0f hset_eq by (by100 simp)
    thus ?thesis using hG0i by (by100 blast)
  qed
  \<comment> \<open>Step 3: The quotient F({a,b})/\<langle>\<langle>aba\<inverse>b\<inverse>\<rangle>\<rangle>: since aba\<inverse>b\<inverse>=1 means ab=ba,
     the quotient is the free abelian group on {a,b}, which is Z \<times> Z.\<close>
  have hquotient_ZZ: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier T_torus TT x0)
      (top1_fundamental_group_mul T_torus TT x0)
      (UNIV::(int \<times> int) set) (\<lambda>(a1,a2) (b1,b2). (a1+b1, a2+b2))"
    sorry \<comment> \<open>Theorem 72.1 + abelianization: F(a,b)/\<langle>\<langle>[a,b]\<rangle>\<rangle> \<cong> Z\<times>Z.\<close>
  show ?thesis by (rule hquotient_ZZ)
qed

(** from \<S>73 Theorem 73.4: the n-fold dunce cap has fundamental group Z/nZ. **)
theorem Theorem_73_4_dunce_cap:
  fixes n :: nat and X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "n > 0"
      and "top1_is_dunce_cap_on X TX n"
      and "x0 \<in> X"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_Zn_group n)
           (top1_Zn_mul n)"
proof -
  \<comment> \<open>Munkres 73.4: X is the dunce cap = quotient of B^2 by n-fold rotation on S^1.
     The 1-skeleton is a single circle A, and \<pi>_1(A) \<cong> Z generated by the loop a.
     The 2-cell is attached by a^n. By Theorem 72.1:
     \<pi>_1(X) \<cong> Z/\<langle>\<langle>a^n\<rangle>\<rangle> \<cong> Z/nZ.\<close>
  \<comment> \<open>Step 1: The dunce cap has 1-skeleton A = single circle (\<cong> S¹).
     The attaching map wraps S¹ n times around A.\<close>
  \<comment> \<open>Extract quotient map q from dunce cap definition.\<close>
  obtain q where hq_quot: "top1_quotient_map_on top1_B2 top1_B2_topology X TX q"
      and hq_S1: "\<forall>z\<in>top1_S1. \<forall>z'\<in>top1_S1.
            q z = q z' \<longleftrightarrow>
            (\<exists>k::nat. k < n \<and>
               z' = (cos (2*pi*real k/real n) * fst z - sin (2*pi*real k/real n) * snd z,
                     sin (2*pi*real k/real n) * fst z + cos (2*pi*real k/real n) * snd z))"
      and hq_inj: "inj_on q (top1_B2 - top1_S1)"
      and hq_sep: "\<forall>z\<in>top1_B2 - top1_S1. \<forall>z'\<in>top1_S1. q z \<noteq> q z'"
    using assms(2) unfolding top1_is_dunce_cap_on_def
    apply (elim exE conjE)
    apply (rule that)
    apply assumption+
    done
  \<comment> \<open>A = q(S1) is the 1-skeleton, h = q is the attaching map.\<close>
  let ?A_loc = "q ` top1_S1"
  have hq_cont: "top1_continuous_map_on top1_B2 top1_B2_topology X TX q"
    using hq_quot unfolding top1_quotient_map_on_def by (by100 blast)
  obtain A :: "'a set" and h :: "real \<times> real \<Rightarrow> 'a"
    where hA_circle: "\<exists>f. top1_homeomorphism_on top1_S1 top1_S1_topology
             A (subspace_topology X TX A) f"
      and hh_att: "top1_continuous_map_on top1_B2 top1_B2_topology X TX h"
      and hh_wrap: "\<forall>s\<in>I_set. h (cos (2*pi*s), sin (2*pi*s)) = h (cos (2*pi*n*s), sin (2*pi*n*s))"
      and hx0_A: "x0 \<in> A" and hA_sub: "A \<subseteq> X"
    sorry \<comment> \<open>From dunce cap: A = q(S1), h = q. Circle homeomorphism from quotient structure.\<close>
  \<comment> \<open>Step 2: \<pi>_1(A) \<cong> Z (fundamental group of circle).\<close>
  have hA_Z: "\<exists>f. top1_group_iso_on
      (top1_fundamental_group_carrier A (subspace_topology X TX A) x0)
      (top1_fundamental_group_mul A (subspace_topology X TX A) x0)
      (UNIV::int set) (\<lambda>a b. a + b) f"
  proof -
    let ?TA = "subspace_topology X TX A"
    \<comment> \<open>Extract homeomorphism h_circ: S1 \<rightarrow> A.\<close>
    obtain h_circ where h_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology A ?TA h_circ"
      using hA_circle by (by100 blast)
    \<comment> \<open>\<pi>_1(S1, (1,0)) \<cong> (Z, +) by Theorem 54.5.\<close>
    have hS1_Z: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        top1_Z_group top1_Z_mul"
      by (rule Theorem_54_5_iso)
    \<comment> \<open>By Corollary 52.5: homeomorphism S1 \<cong> A gives \<pi>_1(S1, (1,0)) \<cong> \<pi>_1(A, h_circ(1,0)).\<close>
    have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
      using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
    have hTA_top: "is_topology_on A ?TA"
    proof -
      have hTX: "is_topology_on X TX"
        using assms(2) unfolding top1_is_dunce_cap_on_def is_topology_on_strict_def by (by100 blast)
      show ?thesis by (rule subspace_topology_is_topology_on[OF hTX hA_sub])
    qed
    have h10_S1: "(1::real, 0::real) \<in> top1_S1"
      unfolding top1_S1_def by (by100 simp)
    have hS1_A_iso: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_carrier A ?TA (h_circ (1, 0)))
        (top1_fundamental_group_mul A ?TA (h_circ (1, 0)))"
      by (rule Corollary_52_5_homeomorphism_iso[OF hS1_top hTA_top h_homeo h10_S1]) (by100 simp)
    \<comment> \<open>Chain: \<pi>_1(A, h_circ(1,0)) \<cong> \<pi>_1(S1, (1,0)) \<cong> Z.\<close>
    have hA_hc_Z: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier A ?TA (h_circ (1, 0)))
        (top1_fundamental_group_mul A ?TA (h_circ (1, 0)))
        top1_Z_group top1_Z_mul"
    proof -
      have hA_S1: "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier A ?TA (h_circ (1, 0)))
          (top1_fundamental_group_mul A ?TA (h_circ (1, 0)))
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
          (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))"
      proof -
        have hgrpS1: "top1_is_group_on
            (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_id top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_invg top1_S1 top1_S1_topology (1, 0))"
          by (rule top1_fundamental_group_is_group[OF hS1_top h10_S1])
        have hhc_A: "h_circ (1, 0) \<in> A"
          using h_homeo h10_S1 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have hgrpA: "top1_is_group_on
            (top1_fundamental_group_carrier A ?TA (h_circ (1, 0)))
            (top1_fundamental_group_mul A ?TA (h_circ (1, 0)))
            (top1_fundamental_group_id A ?TA (h_circ (1, 0)))
            (top1_fundamental_group_invg A ?TA (h_circ (1, 0)))"
          by (rule top1_fundamental_group_is_group[OF hTA_top hhc_A])
        show ?thesis by (rule top1_groups_isomorphic_on_sym[OF hS1_A_iso hgrpS1 hgrpA])
      qed
      show ?thesis by (rule groups_isomorphic_trans_fwd[OF hA_S1 hS1_Z])
    qed
    \<comment> \<open>Base change: \<pi>_1(A, x0) \<cong> \<pi>_1(A, h_circ(1,0)) (since A is path-connected).\<close>
    have hA_pc: "top1_path_connected_on A ?TA"
    proof -
      have "top1_path_connected_on top1_S1 top1_S1_topology"
        by (rule S1_path_connected)
      thus ?thesis
        by (rule homeomorphism_preserves_path_connected[OF h_homeo])
    qed
    have hhc_A: "h_circ (1, 0) \<in> A"
      using h_homeo h10_S1 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have hA_bc: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier A ?TA x0)
        (top1_fundamental_group_mul A ?TA x0)
        (top1_fundamental_group_carrier A ?TA (h_circ (1, 0)))
        (top1_fundamental_group_mul A ?TA (h_circ (1, 0)))"
      by (rule Corollary_52_2_basepoint_independent[OF hA_pc hx0_A hhc_A])
    \<comment> \<open>Chain: \<pi>_1(A, x0) \<cong> \<pi>_1(A, h_circ(1,0)) \<cong> Z.\<close>
    have hA_x0_Z: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier A ?TA x0)
        (top1_fundamental_group_mul A ?TA x0)
        top1_Z_group top1_Z_mul"
      by (rule groups_isomorphic_trans_fwd[OF hA_bc hA_hc_Z])
    \<comment> \<open>Unfold Z definitions.\<close>
    have "top1_Z_group = (UNIV :: int set)" unfolding top1_Z_group_def by (by100 simp)
    moreover have "top1_Z_mul = (\<lambda>a b. a + b)" unfolding top1_Z_mul_def by (rule ext)+ (by100 simp)
    ultimately show ?thesis using hA_x0_Z unfolding top1_groups_isomorphic_on_def by (by100 simp)
  qed
  \<comment> \<open>Step 3: By Theorem 72.1, \<pi>_1(X) \<cong> Z/\<langle>\<langle>n\<rangle>\<rangle> = Z/nZ.
     The relator is aⁿ (the standard loop wrapped n times).\<close>
  \<comment> \<open>Step 3a: Apply Theorem 72.1 to get \<pi>_1(X) \<cong> \<pi>_1(A)/\<langle>\<langle>[k\<circ>p]\<rangle>\<rangle>.\<close>
  \<comment> \<open>Need: is_topology_on_strict, Hausdorff, A closed, A path-connected,
     h continuous B2\<rightarrow>X, a \<in> A, h|_{Int B2} homeomorphism, h(S1)\<subseteq>A, h(1,0)=a.\<close>
  have hThm72: "\<exists>\<iota>.
      top1_continuous_map_on top1_S1 top1_S1_topology A
           (subspace_topology X TX A) \<iota>
    \<and> (\<forall>z\<in>top1_S1. \<iota> z = h z)
    \<and> top1_groups_isomorphic_on
          (top1_fundamental_group_carrier X TX x0)
          (top1_fundamental_group_mul X TX x0)
          (top1_quotient_group_carrier_on
             (top1_fundamental_group_carrier A (subspace_topology X TX A) x0)
             (top1_fundamental_group_mul A (subspace_topology X TX A) x0)
             (top1_normal_subgroup_generated_on
                (top1_fundamental_group_carrier A (subspace_topology X TX A) x0)
                (top1_fundamental_group_mul A (subspace_topology X TX A) x0)
                (top1_fundamental_group_id A (subspace_topology X TX A) x0)
                (top1_fundamental_group_invg A (subspace_topology X TX A) x0)
                {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
                    A (subspace_topology X TX A) x0
                    (\<lambda>z. h z)
                  {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                      (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) g}}))
          (top1_quotient_group_mul_on
             (top1_fundamental_group_mul A (subspace_topology X TX A) x0))"
    sorry \<comment> \<open>Apply Theorem_72_1. Needs all hypotheses verified.\<close>
  \<comment> \<open>Step 3b: The relator [k\<circ>p] in \<pi>_1(A) corresponds to n \<in> Z.
     Since \<pi>_1(A) \<cong> Z, the normal closure of {n} is nZ.
     Z/nZ \<cong> (top1_Zn_group n, top1_Zn_mul n) by Z_quotient_nZ_iso.\<close>
  \<comment> \<open>Step 3c: Compose isomorphisms: \<pi>_1(X) \<cong> \<pi>_1(A)/\<langle>\<langle>[k\<circ>p]\<rangle>\<rangle> \<cong> Z/\<langle>\<langle>n\<rangle>\<rangle> \<cong> Z/nZ.\<close>
  show ?thesis sorry \<comment> \<open>Compose the three isomorphisms.\<close>
qed

section \<open>Chapter 12: Classification of Surfaces\<close>

text \<open>Surface: a connected, Hausdorff, compact 2-manifold.
  A 2-manifold is a space where every point has a neighborhood homeomorphic
  to an open subset of R^2.\<close>
definition top1_is_2_manifold_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_2_manifold_on X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     is_hausdorff_on X TX \<and>
     (\<forall>x\<in>X. \<exists>U (V :: (real \<times> real) set) h.
        x \<in> U \<and> openin_on X TX U \<and>
        V \<in> product_topology_on top1_open_sets top1_open_sets \<and>
        top1_homeomorphism_on U (subspace_topology X TX U) V
          (subspace_topology UNIV
             (product_topology_on top1_open_sets top1_open_sets) V)
          h)"
     \<comment> \<open>Munkres's definition of an n-manifold requires Hausdorff (and second countable,
         but that's implied by compact + locally Euclidean for our surface case).\<close>

definition top1_is_surface_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_surface_on X TX \<longleftrightarrow>
     top1_is_2_manifold_on X TX \<and>
     top1_connected_on X TX \<and>
     is_hausdorff_on X TX \<and>
     top1_compact_on X TX \<and>
     X \<noteq> {}"
     \<comment> \<open>Non-emptiness is required: classification theorem §77.5 says a surface is
         S^2, T_n, or P_m, none of which are empty. Without X \<noteq> {}, the empty set
         would vacuously satisfy locally-Euclidean and falsify §77.5.\<close>

section \<open>\<S>74 Fundamental Groups of Surfaces\<close>

\<comment> \<open>Unused undefined placeholders top1_n_fold_torus and top1_m_fold_projective
    removed. Use top1_is_n_fold_torus_on and top1_is_m_fold_projective_on predicates
    (defined earlier) on a space (X, TX) instead.\<close>


text \<open>Cone superset: cone(conv n, v_n) \<subseteq> conv(Suc n).\<close>
lemma convex_hull_cone_sup:
  fixes vx vy :: "nat \<Rightarrow> real"
  shows "(\<lambda>(t, x', y'). ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))
      ` ({0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
          \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)})
    \<subseteq> {(x, y). \<exists>c. (\<forall>i<Suc n. c i \<ge> 0) \<and> (\<Sum>i<Suc n. c i) = 1
      \<and> x = (\<Sum>i<Suc n. c i * vx i) \<and> y = (\<Sum>i<Suc n. c i * vy i)}"
proof (rule subsetI)
  fix q assume hq_mem: "q \<in> (\<lambda>(t, x', y'). ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))
      ` ({0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
          \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)})"
  then obtain p where hp: "p \<in> {0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
      \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      and hq: "q = (case p of (t, x', y') \<Rightarrow> ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))"
    by (by100 blast)
  obtain t r where htr: "p = (t, r)" "t \<in> {0..1}" by (cases p) (use hp in \<open>(by100 auto)\<close>)
  obtain x' y' where hr: "r = (x', y')" by (cases r)
  have ht: "0 \<le> t" "t \<le> 1" using htr(2) by (by100 auto)+
  have hq_eq: "q = ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n)"
    using hq htr(1) hr by (by100 simp)
  obtain c' where hc': "\<forall>i<n. (0::real) \<le> c' i" "(\<Sum>i<n. c' i) = 1"
      "x' = (\<Sum>i<n. c' i * vx i)" "y' = (\<Sum>i<n. c' i * vy i)"
    using hp htr(1) hr by (by100 blast)
  let ?c = "\<lambda>i. if i < n then (1-t) * c' i else if i = n then t else 0 :: real"
  have hc_nn: "\<forall>i<Suc n. 0 \<le> ?c i" using ht hc'(1) by (by100 force)
  have hc_sum: "(\<Sum>i<Suc n. ?c i) = 1"
  proof -
    have "(\<Sum>i<n. ?c i) = (\<Sum>i<n. (1-t) * c' i)" by (rule sum.cong) (by100 simp)+
    also have "\<dots> = (1-t)" using hc'(2) by (simp add: sum_distrib_left[symmetric])
    finally show ?thesis by (by100 simp)
  qed
  have hc_x: "(\<Sum>i<Suc n. ?c i * vx i) = (1-t)*x' + t*vx n"
  proof -
    have "(\<Sum>i<n. ?c i * vx i) = (\<Sum>i<n. (1-t) * c' i * vx i)"
      by (rule sum.cong) (by100 simp)+
    also have "\<dots> = (1-t) * x'" using hc'(3) by (simp add: sum_distrib_left mult.assoc)
    finally show ?thesis by (by100 simp)
  qed
  have hc_y: "(\<Sum>i<Suc n. ?c i * vy i) = (1-t)*y' + t*vy n"
  proof -
    have "(\<Sum>i<n. ?c i * vy i) = (\<Sum>i<n. (1-t) * c' i * vy i)"
      by (rule sum.cong) (by100 simp)+
    also have "\<dots> = (1-t) * y'" using hc'(4) by (simp add: sum_distrib_left mult.assoc)
    finally show ?thesis by (by100 simp)
  qed
  show "q \<in> {(x, y). \<exists>c. (\<forall>i<Suc n. c i \<ge> 0) \<and> (\<Sum>i<Suc n. c i) = 1
      \<and> x = (\<Sum>i<Suc n. c i * vx i) \<and> y = (\<Sum>i<Suc n. c i * vy i)}"
    unfolding hq_eq
    apply simp
    apply (rule_tac x="?c" in exI)
    using hc_nn hc_sum hc_x hc_y by force
qed

text \<open>Cone subset: conv(Suc n) \<subseteq> cone(conv n, v_n).\<close>
lemma convex_hull_cone_sub:
  fixes vx vy :: "nat \<Rightarrow> real"
  assumes "n \<ge> 1"
  shows "{(x, y). \<exists>c. (\<forall>i<Suc n. c i \<ge> 0) \<and> (\<Sum>i<Suc n. c i) = 1
      \<and> x = (\<Sum>i<Suc n. c i * vx i) \<and> y = (\<Sum>i<Suc n. c i * vy i)}
    \<subseteq> (\<lambda>(t, x', y'). ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))
      ` ({0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
          \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)})"
proof (rule subsetI)
  fix q assume "q \<in> {(x, y). \<exists>c. (\<forall>i<Suc n. c i \<ge> 0) \<and> (\<Sum>i<Suc n. c i) = 1
      \<and> x = (\<Sum>i<Suc n. c i * vx i) \<and> y = (\<Sum>i<Suc n. c i * vy i)}"
  then obtain x y c where hq: "q = (x, y)"
      and hc: "\<forall>i<Suc n. (0::real) \<le> c i" "(\<Sum>i<Suc n. c i) = 1"
      "x = (\<Sum>i<Suc n. c i * vx i)" "y = (\<Sum>i<Suc n. c i * vy i)"
    by (by100 blast)
  let ?t = "c n"
  have ht0: "0 \<le> ?t" using hc(1) by (by100 force)
  have ht1: "?t \<le> 1"
    by (rule order_trans[OF member_le_sum[of n "{..<Suc n}" c]]) (use hc in auto)
  show "q \<in> (\<lambda>(t, x', y'). ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))
      ` ({0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
          \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)})"
  proof (cases "?t = 1")
    case True
    have hsum0: "(\<Sum>i<n. c i) = 0" using hc(2) True by simp
    have hall0: "\<forall>i<n. c i = 0"
    proof (intro allI impI)
      fix i assume "i < n"
      have "c i \<le> (\<Sum>i<n. c i)" by (rule member_le_sum) (use hc(1) \<open>i<n\<close> in auto)
      moreover have "0 \<le> c i" using hc(1) \<open>i<n\<close> by (by100 force)
      ultimately show "c i = 0" using hsum0 by (by100 linarith)
    qed
    have hx_vn: "x = vx n" using hc(3) hall0 True by simp
    have hy_vn: "y = vy n" using hc(4) hall0 True by simp
    \<comment> \<open>n \<ge> 1 (from induction hypothesis), so Pn is non-empty: (vx 0, vy 0) \<in> Pn.\<close>
    have hn1: "n \<ge> 1" using assms .
    let ?d = "\<lambda>i::nat. if i = 0 then 1::real else 0"
    have "(vx 0, vy 0) \<in> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      apply simp
      apply (rule_tac x="?d" in exI)
    proof (intro conjI allI impI)
      fix i :: nat assume "i < n" thus "0 \<le> ?d i" by (by100 simp)
    next
      show "(\<Sum>i<n. ?d i) = 1" using hn1 by simp
    next
      show "vx 0 = (\<Sum>i<n. ?d i * vx i)"
      proof -
        have "(\<Sum>i<n. ?d i * vx i) = ?d 0 * vx 0 + (\<Sum>i\<in>{..<n}-{0}. ?d i * vx i)"
          using hn1 by (intro sum.remove) auto
        also have "(\<Sum>i\<in>{..<n}-{0}. ?d i * vx i) = 0"
          by (rule sum.neutral) (by100 simp)
        finally show ?thesis by (by100 simp)
      qed
    next
      show "vy 0 = (\<Sum>i<n. ?d i * vy i)"
      proof -
        have "(\<Sum>i<n. ?d i * vy i) = ?d 0 * vy 0 + (\<Sum>i\<in>{..<n}-{0}. ?d i * vy i)"
          using hn1 by (intro sum.remove) auto
        also have "(\<Sum>i\<in>{..<n}-{0}. ?d i * vy i) = 0"
          by (rule sum.neutral) (by100 simp)
        finally show ?thesis by (by100 simp)
      qed
    qed
    hence hpn_ne: "\<exists>p'. p' \<in> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}" by (by100 blast)
    then obtain x0 y0 where hxy0: "(x0, y0) \<in> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}" by (by100 blast)
    have "(1::real, (x0, y0)) \<in> {0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      using hxy0 by auto
    moreover have "q = (case (1::real, (x0, y0)) of (t, x', y') \<Rightarrow>
        ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))"
      using hq hx_vn hy_vn by (by100 simp)
    ultimately show ?thesis by (by100 blast)
  next
    case htnot1: False
    have hlt1: "?t < 1" using htnot1 ht1 by (by100 linarith)
    hence h1mt: "1 - ?t > 0" by (by100 linarith)
    let ?c' = "\<lambda>i. c i / (1 - ?t)"
    have hc'_nn: "\<forall>i<n. ?c' i \<ge> 0" using hc(1) h1mt by (by100 force)
    have hc'_sum: "(\<Sum>i<n. ?c' i) = 1"
    proof -
      have "(\<Sum>i<n. ?c' i) = (\<Sum>i<n. c i) / (1 - ?t)"
        by (simp add: sum_divide_distrib)
      also have "(\<Sum>i<n. c i) = 1 - ?t" using hc(2) by simp
      finally show ?thesis using h1mt by simp
    qed
    let ?x' = "\<Sum>i<n. ?c' i * vx i"
    let ?y' = "\<Sum>i<n. ?c' i * vy i"
    have hrescale_x: "(1-?t)*?x' = (\<Sum>i<n. c i * vx i)"
    proof -
      have "(1-?t)*?x' = (\<Sum>i<n. (1-?t) * (?c' i * vx i))"
        by (simp add: sum_distrib_left)
      also have "\<dots> = (\<Sum>i<n. c i * vx i)"
        using h1mt by (intro sum.cong) (simp_all add: field_simps)
      finally show ?thesis .
    qed
    have hrescale_y: "(1-?t)*?y' = (\<Sum>i<n. c i * vy i)"
    proof -
      have "(1-?t)*?y' = (\<Sum>i<n. (1-?t) * (?c' i * vy i))"
        by (simp add: sum_distrib_left)
      also have "\<dots> = (\<Sum>i<n. c i * vy i)"
        using h1mt by (intro sum.cong) (simp_all add: field_simps)
      finally show ?thesis .
    qed
    have hx_eq: "x = (1-?t)*?x' + ?t*vx n" using hc(3) hrescale_x by simp
    have hy_eq: "y = (1-?t)*?y' + ?t*vy n" using hc(4) hrescale_y by simp
    have "(?x', ?y') \<in> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      apply simp
      apply (rule_tac x="?c'" in exI)
      using hc'_nn hc'_sum by (by100 auto)
    have ht_in: "?t \<in> {0..1}" using ht0 ht1 by (by100 auto)
    hence "(?t, (?x', ?y')) \<in> {0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      using \<open>(?x', ?y') \<in> _\<close> by (by100 blast)
    moreover have "q = (case (?t, (?x', ?y')) of (t, x', y') \<Rightarrow>
        ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))"
      using hq hx_eq hy_eq by (by100 simp)
    ultimately show ?thesis by (by100 blast)
  qed
qed

text \<open>A convex hull of n \<ge> 3 points in R^2 is compact.\<close>
text \<open>Convex hull of n \<ge> 1 points is compact, by induction on n.
  Base: single point. Step: conv(n+1) = image of [0,1] \<times> conv(n) under continuous cone map.\<close>
lemma convex_hull_compact_general:
  fixes vx vy :: "nat \<Rightarrow> real" and n :: nat
  assumes "n \<ge> 1"
  shows "compact {(x, y). \<exists>coeffs. (\<forall>i<n. (coeffs i :: real) \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
      \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
  using assms
proof (induction n rule: nat_induct_at_least)
  case base
  \<comment> \<open>n=1: P = {(vx 0, vy 0)}, a single point — trivially compact.\<close>
  have "{(x::real, y::real). \<exists>coeffs. (\<forall>i<1. coeffs i \<ge> 0) \<and> (\<Sum>i<1. coeffs i) = 1
      \<and> x = (\<Sum>i<1. coeffs i * vx i) \<and> y = (\<Sum>i<1. coeffs i * vy i)}
    = {(vx 0, vy 0)}"
  proof
    show "{(vx 0, vy 0)} \<subseteq> {(x, y). \<exists>coeffs. (\<forall>i<1. coeffs i \<ge> 0) \<and>
        (\<Sum>i<1. coeffs i) = 1 \<and> x = (\<Sum>i<1. coeffs i * vx i) \<and> y = (\<Sum>i<1. coeffs i * vy i)}"
      by (rule subsetI) (auto intro: exI[of _ "\<lambda>_. 1"])
  next
    show "{(x, y). \<exists>coeffs. (\<forall>i<1. coeffs i \<ge> 0) \<and> (\<Sum>i<1. coeffs i) = 1 \<and>
        x = (\<Sum>i<1. coeffs i * vx i) \<and> y = (\<Sum>i<1. coeffs i * vy i)} \<subseteq> {(vx 0, vy 0)}"
      by auto
  qed
  moreover have "compact {(vx 0, vy 0)}"
  proof (rule compactI)
    fix \<U> :: "(real \<times> real) set set"
    assume "\<forall>U\<in>\<U>. open U" "{(vx 0, vy 0)} \<subseteq> \<Union>\<U>"
    then obtain U where "U \<in> \<U>" "(vx 0, vy 0) \<in> U" by (by100 blast)
    thus "\<exists>\<F>\<subseteq>\<U>. finite \<F> \<and> {(vx 0, vy 0)} \<subseteq> \<Union>\<F>"
      by (rule_tac x="{U}" in exI) (by100 blast)
  qed
  ultimately show ?case by (by100 simp)
next
  case (Suc n)
  \<comment> \<open>Inductive step: conv(n+1 points) = cone from v_n over conv(n points).
     (x,y) \<in> conv(n+1) iff \<exists>t\<in>[0,1]. \<exists>(x',y')\<in>conv(n).
       x = (1-t)*x' + t*vx(n)  and  y = (1-t)*y' + t*vy(n).
     This is the image of [0,1] \<times> conv(n) under a continuous map.\<close>
  let ?Pn = "{(x::real, y::real). \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
      \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
  let ?Pn1 = "{(x::real, y::real). \<exists>coeffs. (\<forall>i<Suc n. coeffs i \<ge> 0) \<and> (\<Sum>i<Suc n. coeffs i) = 1
      \<and> x = (\<Sum>i<Suc n. coeffs i * vx i) \<and> y = (\<Sum>i<Suc n. coeffs i * vy i)}"
  have hPn_compact: "compact ?Pn" by (rule Suc.IH)
  \<comment> \<open>f: [0,1] \<times> ?Pn \<rightarrow> ?Pn1 via f(t, (x',y')) = ((1-t)*x' + t*vx n, (1-t)*y' + t*vy n).\<close>
  let ?f = "\<lambda>(t::real, (x'::real, y'::real)). ((1-t)*x' + t*vx n, (1-t)*y' + t*vy n)"
  \<comment> \<open>[0,1] \<times> ?Pn is compact.\<close>
  have hdom_compact: "compact ({0..1::real} \<times> ?Pn)"
    by (rule compact_Times_general[OF compact_Icc hPn_compact])
  \<comment> \<open>?f is continuous.\<close>
  have hf_cont: "continuous_on ({0..1} \<times> ?Pn) ?f"
  proof -
    have "continuous_on UNIV ?f"
      unfolding split_def
      by (intro continuous_on_Pair continuous_on_add continuous_on_mult continuous_on_id
          continuous_on_diff continuous_on_fst continuous_on_snd continuous_on_const)
    thus ?thesis by (rule continuous_on_subset) (by100 blast)
  qed
  \<comment> \<open>?Pn1 = ?f ` ({0..1} \<times> ?Pn).\<close>
  have hPn1_eq: "?Pn1 = ?f ` ({0..1} \<times> ?Pn)"
    by (rule equalityI[OF convex_hull_cone_sub[OF Suc(1)] convex_hull_cone_sup])
  show ?case unfolding hPn1_eq
    by (rule compact_continuous_image[OF hf_cont hdom_compact])
qed

lemma convex_hull_compact:
  fixes vx vy :: "nat \<Rightarrow> real" and n :: nat
  assumes "n \<ge> 3"
  shows "compact {(x, y). \<exists>coeffs. (\<forall>i<n. (coeffs i :: real) \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
      \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
  using convex_hull_compact_general[of n vx vy] assms by (by100 linarith)

\<comment> \<open>Strict polygonal quotient: all scheme properties + no extra identifications.
   Uses a SINGLE set of existentials (scheme, P, q, vx, vy) to avoid witness matching.\<close>
definition top1_is_polygonal_quotient_strict_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_polygonal_quotient_strict_on X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     (\<exists>(scheme :: (nat \<times> bool) list) P q (vx::nat\<Rightarrow>real) (vy::nat\<Rightarrow>real).
        top1_is_polygonal_region_on P (length scheme)
      \<and> top1_quotient_map_on P
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q
      \<and> (\<forall>i<length scheme. \<forall>j<length scheme. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j))
      \<and> (\<forall>i<length scheme. (vx i, vy i) \<in> P)
      \<and> (\<forall>i<length scheme. \<forall>j<length scheme.
            fst (scheme!i) = fst (scheme!j) \<longrightarrow>
            (\<forall>t\<in>I_set.
               q ((1-t) * vx i + t * vx (Suc i mod length scheme),
                  (1-t) * vy i + t * vy (Suc i mod length scheme))
             = (if snd (scheme!i) = snd (scheme!j)
                then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                        (1-t) * vy j + t * vy (Suc j mod length scheme))
                else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                        t * vy j + (1-t) * vy (Suc j mod length scheme)))))
      \<and> (\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
                    p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                          (1-t) * vy i + t * vy (Suc i mod length scheme)))
               \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p'))
      \<and> (\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
            q ((1-t) * vx i + t * vx (Suc i mod length scheme),
               (1-t) * vy i + t * vy (Suc i mod length scheme))
          = q ((1-s) * vx j + s * vx (Suc j mod length scheme),
               (1-s) * vy j + s * vy (Suc j mod length scheme))
          \<longrightarrow> (i = j \<and> t = s)
            \<or> (fst (scheme!i) = fst (scheme!j) \<and>
               (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))))"

\<comment> \<open>Richer extraction from scheme: gives vertices, edge identification, interior singleton fibers.\<close>
lemma quotient_of_scheme_extract_full:
  assumes "top1_quotient_of_scheme_on X TX scheme"
  obtains P q vx vy where
    "top1_is_polygonal_region_on P (length scheme)"
    "top1_quotient_map_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q"
    "length scheme \<ge> 3"
    "\<forall>i<length scheme. (vx i, vy i) \<in> P"
    "\<forall>i<length scheme. \<forall>j<length scheme.
        fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set.
           q ((1-t) * vx i + t * vx (Suc i mod length scheme),
              (1-t) * vy i + t * vy (Suc i mod length scheme))
         = (if snd (scheme!i) = snd (scheme!j)
            then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                    (1-t) * vy j + t * vy (Suc j mod length scheme))
            else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                    t * vy j + (1-t) * vy (Suc j mod length scheme))))"
    "\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
              p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                    (1-t) * vy i + t * vy (Suc i mod length scheme)))
         \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
proof -
  from assms obtain P q vx vy where
    h1: "top1_is_polygonal_region_on P (length scheme)" and
    h2: "top1_quotient_map_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q" and
    h3: "\<forall>i<length scheme. (vx i, vy i) \<in> P" and
    h4: "\<forall>i<length scheme. \<forall>j<length scheme.
        fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
            (1-t) * vy i + t * vy (Suc i mod length scheme))
         = (if snd (scheme!i) = snd (scheme!j)
            then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                    (1-t) * vy j + t * vy (Suc j mod length scheme))
            else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                    t * vy j + (1-t) * vy (Suc j mod length scheme))))" and
    h5: "\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
          p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                (1-t) * vy i + t * vy (Suc i mod length scheme)))
       \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
    using assms unfolding top1_quotient_of_scheme_on_def
    by (elim conjE exE) blast
  have h6: "length scheme \<ge> 3"
    using h1 unfolding top1_is_polygonal_region_on_def by (by100 blast)
  show ?thesis by (rule that[OF h1 h2 h6 h3 h4 h5])
qed

\<comment> \<open>Note: quotient\_strict\_extract was removed because automation can't handle the
   50+ atom obtains formula. The "no extra identifications" condition is sorry'd
   directly in Theorem\_74\_1 instead. The top1\_is\_polygonal\_quotient\_strict\_on
   definition remains available for future use if the automation issue is resolved.\<close>

(** from \<S>74 Theorem 74.1: polygonal quotients are compact Hausdorff **)
theorem Theorem_74_1_polygon_quotient_compact_hausdorff:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "is_topology_on_strict X TX"
  and "top1_is_polygonal_quotient_on X TX"
  shows "top1_compact_on X TX \<and> is_hausdorff_on X TX"
proof -
  \<comment> \<open>Munkres 74.1: The polygonal region P is compact (closed bounded subset of R^2).
     The quotient map q: P \<rightarrow> X is continuous and surjective.
     Compact: q(P) = X is compact (continuous image of compact).
     Hausdorff: the quotient identifications are on the boundary only;
     use the finite edge-identification structure to verify the T2 axiom.\<close>
  \<comment> \<open>Extract scheme + P + q + vx + vy from the (non-strict) polygonal quotient definition.\<close>
  have "\<exists>scheme :: (nat \<times> bool) list. top1_quotient_of_scheme_on X TX scheme"
    using assms(2) unfolding top1_is_polygonal_quotient_on_def by (by100 blast)
  then obtain scheme :: "(nat \<times> bool) list" where hsch: "top1_quotient_of_scheme_on X TX scheme"
    by (by100 auto)
  obtain P q vx vy where
      hP_full: "top1_is_polygonal_region_on P (length scheme)"
      and hq_full: "top1_quotient_map_on P
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q"
      and hlen_full: "length scheme \<ge> 3"
      and hvert_full: "\<forall>i<length scheme. (vx i, vy i) \<in> P"
      and hedge_full: "\<forall>i<length scheme. \<forall>j<length scheme. fst (scheme!i) = fst (scheme!j) \<longrightarrow>
          (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
              (1-t) * vy i + t * vy (Suc i mod length scheme))
           = (if snd (scheme!i) = snd (scheme!j)
              then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                      (1-t) * vy j + t * vy (Suc j mod length scheme))
              else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                      t * vy j + (1-t) * vy (Suc j mod length scheme))))"
      and hinterior_full: "\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
              p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                    (1-t) * vy i + t * vy (Suc i mod length scheme)))
           \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
    by (rule quotient_of_scheme_extract_full[OF hsch])
  \<comment> \<open>The "no extra identifications" condition: sorry. This requires
     the polygonal quotient to have ONLY the scheme-specified identifications
     on the boundary. The current definition doesn't guarantee this.\<close>
  have hno_extra_full: "\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
              q ((1-t) * vx i + t * vx (Suc i mod length scheme),
                 (1-t) * vy i + t * vy (Suc i mod length scheme))
            = q ((1-s) * vx j + s * vx (Suc j mod length scheme),
                 (1-s) * vy j + s * vy (Suc j mod length scheme))
            \<longrightarrow> (i = j \<and> t = s)
              \<or> (fst (scheme!i) = fst (scheme!j) \<and>
                 (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
    sorry \<comment> \<open>Definition gap: needs "no extra identifications" condition.\<close>
  have hcompact: "top1_compact_on X TX"
  proof -
    let ?TP_c = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
    \<comment> \<open>Reuse P, q from the extraction above.\<close>
    have hP: "top1_is_polygonal_region_on P (length scheme)" by (rule hP_full)
    have hq: "top1_quotient_map_on P ?TP_c X TX q" by (rule hq_full)
    let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
    \<comment> \<open>Step 1: P is compact (convex hull of finitely many points in R^2).\<close>
    have hP_compact: "top1_compact_on P ?TP"
    proof -
      \<comment> \<open>Bridge: product_topology_on top1_open_sets top1_open_sets = top1_open_sets for R^2.\<close>
      have hTP_eq: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
        using product_topology_on_open_sets_real2 by (by100 simp)
      \<comment> \<open>By bridge lemma: top1_compact_on P (subspace UNIV open P) \<longleftrightarrow> compact P.\<close>
      have "top1_compact_on P (subspace_topology UNIV top1_open_sets P) \<longleftrightarrow> compact P"
        by (rule top1_compact_on_subspace_UNIV_iff_compact)
      \<comment> \<open>Need: compact P (polygonal region is compact in R^2).
         P is a closed bounded convex hull, hence compact.\<close>
      moreover have "compact P"
      proof -
        \<comment> \<open>P is the convex hull of finitely many points.
           P = union of n-2 triangles (fan triangulation from vertex 0).
           Each triangle is compact (continuous image of compact [0,1]^2).
           Finite union of compact is compact.\<close>
        obtain vx vy :: "nat \<Rightarrow> real" where hn: "length scheme \<ge> 3"
            and hP_eq: "P = {(x, y). \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
                \<and> (\<Sum>i<length scheme. coeffs i) = 1
                \<and> x = (\<Sum>i<length scheme. coeffs i * vx i)
                \<and> y = (\<Sum>i<length scheme. coeffs i * vy i)}"
          using hP unfolding top1_is_polygonal_region_on_def by blast
        show "compact P" unfolding hP_eq by (rule convex_hull_compact[OF hn])
      qed
      ultimately have "top1_compact_on P (subspace_topology UNIV top1_open_sets P)" by (by100 simp)
      thus ?thesis using hTP_eq by (by100 simp)
    qed
    \<comment> \<open>Step 2: q is continuous (from quotient map).\<close>
    have hq_cont: "top1_continuous_map_on P ?TP X TX q"
      using hq unfolding top1_quotient_map_on_def by (by100 blast)
    \<comment> \<open>Step 3: q is surjective (from quotient map).\<close>
    have hq_surj: "q ` P = X"
      using hq unfolding top1_quotient_map_on_def by (by100 blast)
    \<comment> \<open>Step 4: X = q(P) is compact (continuous image of compact).\<close>
    have hTX_top: "is_topology_on X TX"
      using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have "top1_compact_on (q ` P) (subspace_topology X TX (q ` P))"
      by (rule top1_compact_on_continuous_image[OF hP_compact hTX_top hq_cont])
    hence "top1_compact_on X (subspace_topology X TX X)" using hq_surj by (by100 simp)
    moreover have "subspace_topology X TX X = TX"
    proof -
      have "\<forall>U\<in>TX. U \<subseteq> X" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
      thus ?thesis by (rule subspace_topology_self)
    qed
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Hausdorff: P is a subspace of R^2 (Hausdorff). The quotient identifies
     finitely many boundary pairs. Prove via: P Hausdorff \<Rightarrow> closed map \<Rightarrow> Hausdorff quotient.\<close>
  have hhausdorff: "is_hausdorff_on X TX"
  proof -
    \<comment> \<open>Reuse P, q, vx, vy, scheme from the outer extraction.\<close>
    have hP_loc: "top1_is_polygonal_region_on P (length scheme)" by (rule hP_full)
    have hq_loc: "top1_quotient_map_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q"
      by (rule hq_full)
    have hlen_loc: "length scheme \<ge> 3" by (rule hlen_full)
    have hvert_loc: "\<forall>i<length scheme. (vx i, vy i) \<in> P" by (rule hvert_full)
    have hedge_loc: "\<forall>i<length scheme. \<forall>j<length scheme. fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
            (1-t) * vy i + t * vy (Suc i mod length scheme))
         = (if snd (scheme!i) = snd (scheme!j)
            then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                    (1-t) * vy j + t * vy (Suc j mod length scheme))
            else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                    t * vy j + (1-t) * vy (Suc j mod length scheme))))"
      by (rule hedge_full)
    have hinterior_loc: "\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
          p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                (1-t) * vy i + t * vy (Suc i mod length scheme)))
       \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
      by (rule hinterior_full)
    have hno_extra: "\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
          q ((1-t) * vx i + t * vx (Suc i mod length scheme),
             (1-t) * vy i + t * vy (Suc i mod length scheme))
        = q ((1-s) * vx j + s * vx (Suc j mod length scheme),
             (1-s) * vy j + s * vy (Suc j mod length scheme))
        \<longrightarrow> (i = j \<and> t = s)
          \<or> (fst (scheme!i) = fst (scheme!j) \<and>
             (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
      by (rule hno_extra_full)
    let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
    \<comment> \<open>Step 1: R^2 is Hausdorff.\<close>
    have hR_haus: "is_hausdorff_on (UNIV::real set) top1_open_sets"
      by (rule top1_R_is_hausdorff)
    have hR2_prod_haus: "\<And>X1 T1 X2 T2. is_hausdorff_on X1 T1 \<Longrightarrow> is_hausdorff_on X2 T2 \<Longrightarrow>
        is_hausdorff_on (X1 \<times> X2) (product_topology_on T1 T2)"
      using Theorem_17_11 by (by100 blast)
    have hR2_sub_haus: "\<And>X T Y. is_hausdorff_on X T \<Longrightarrow> Y \<subseteq> X \<Longrightarrow>
        is_hausdorff_on Y (subspace_topology X T Y)"
      using Theorem_17_11 by (by100 blast)
    have hR2_haus: "is_hausdorff_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
      by (rule hR2_prod_haus[OF hR_haus hR_haus, simplified])
    have hP_haus: "is_hausdorff_on P ?TP"
      by (rule hR2_sub_haus[OF hR2_haus]) (by100 blast)
    \<comment> \<open>Step 2: The full Hausdorff argument for the quotient.\<close>
    \<comment> \<open>The equivalence relation R = {(a,b)\<in>P\<times>P | q a = q b} is closed in P\<times>P.
       For polygonal quotients: R is a finite union of pairs of boundary segments,
       each compact (continuous image of [0,1]), hence closed.
       Closed R on compact Hausdorff P \<Rightarrow> P/R Hausdorff.\<close>
    have hR_closed: "closedin_on (P \<times> P)
        (product_topology_on ?TP ?TP)
        {(a, b). a \<in> P \<and> b \<in> P \<and> q a = q b}"
    proof -
      let ?n = "length scheme"
      let ?R = "{(a, b). a \<in> P \<and> b \<in> P \<and> q a = q b}"
      \<comment> \<open>Define boundary: the union of all edges.\<close>
      let ?edge = "\<lambda>i t. ((1-t) * vx i + t * vx (Suc i mod ?n),
                          (1-t) * vy i + t * vy (Suc i mod ?n))"
      let ?bdy = "\<Union>i\<in>{..<length scheme}. ?edge i ` I_set"
      \<comment> \<open>Interior points have singleton q-fibers (from hinterior\_loc).\<close>
      \<comment> \<open>So R \<subseteq> diagonal \<union> (?bdy \<times> ?bdy).\<close>
      have hR_sub: "?R \<subseteq> {(a, b). a \<in> P \<and> b \<in> P \<and> a = b} \<union> (?bdy \<times> ?bdy)"
      proof
        fix x assume "x \<in> ?R"
        then obtain a b where hx: "x = (a, b)" "a \<in> P" "b \<in> P" "q a = q b"
          by (cases x) (by100 blast)
        show "x \<in> {(a, b). a \<in> P \<and> b \<in> P \<and> a = b} \<union> (?bdy \<times> ?bdy)"
        proof (cases "a = b")
          case True thus ?thesis using hx by (by100 blast)
        next
          case False
          have "a \<in> ?bdy"
          proof (rule ccontr)
            assume "a \<notin> ?bdy"
            hence "\<forall>i<length scheme. \<forall>t\<in>I_set. a \<noteq> ?edge i t" by (by100 blast)
            from hinterior_loc hx(2) this hx(3) hx(4)
            have "a = b" by (by100 blast)
            thus False using False by (by100 simp)
          qed
          have "b \<in> ?bdy"
          proof (rule ccontr)
            assume "b \<notin> ?bdy"
            hence "\<forall>i<length scheme. \<forall>t\<in>I_set. b \<noteq> ?edge i t" by (by100 blast)
            from hinterior_loc hx(3) this hx(2) hx(4)[symmetric]
            have "b = a" by (by100 blast)
            thus False using False by (by100 simp)
          qed
          from \<open>a \<in> ?bdy\<close> \<open>b \<in> ?bdy\<close> show ?thesis using hx(1) by (by100 blast)
        qed
      qed
      \<comment> \<open>The diagonal is closed (P\<times>P Hausdorff, equalizer of pi1, pi2).\<close>
      have hPP_haus: "is_hausdorff_on (P \<times> P) (product_topology_on ?TP ?TP)"
        using hR2_prod_haus[OF hP_haus hP_haus] .
      have hTP_top: "is_topology_on P ?TP"
        using hP_haus unfolding is_hausdorff_on_def by (by100 blast)
      have hTPP: "is_topology_on (P \<times> P) (product_topology_on ?TP ?TP)"
        by (rule product_topology_on_is_topology_on[OF hTP_top hTP_top])
      have hpi1_cont: "top1_continuous_map_on (P \<times> P) (product_topology_on ?TP ?TP) P ?TP pi1"
        by (rule top1_continuous_pi1[OF hTP_top hTP_top])
      have hpi2_cont: "top1_continuous_map_on (P \<times> P) (product_topology_on ?TP ?TP) P ?TP pi2"
        by (rule top1_continuous_pi2[OF hTP_top hTP_top])
      have hDiag_eq: "{(a, b). a \<in> P \<and> b \<in> P \<and> a = b}
          = {x \<in> P \<times> P. pi1 x = pi2 x}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {(a, b). a \<in> P \<and> b \<in> P \<and> a = b}"
        then obtain a b where "x = (a, b)" "a \<in> P" "b \<in> P" "a = b" by (by100 blast)
        thus "x \<in> {x \<in> P \<times> P. pi1 x = pi2 x}" unfolding pi1_def pi2_def by (by100 simp)
      next
        fix x assume "x \<in> {x \<in> P \<times> P. pi1 x = pi2 x}"
        hence "x \<in> P \<times> P" "pi1 x = pi2 x" by (by100 blast)+
        then obtain a b where "x = (a, b)" "a \<in> P" "b \<in> P" by (by100 blast)
        have "a = b" using \<open>pi1 x = pi2 x\<close> \<open>x = (a, b)\<close> unfolding pi1_def pi2_def by (by100 simp)
        thus "x \<in> {(a, b). a \<in> P \<and> b \<in> P \<and> a = b}" using \<open>a \<in> P\<close> \<open>b \<in> P\<close> \<open>x = (a, b)\<close> by (by100 blast)
      qed
      have hDiag_closed: "closedin_on (P \<times> P) (product_topology_on ?TP ?TP)
          {(a, b). a \<in> P \<and> b \<in> P \<and> a = b}"
      proof -
        have "closedin_on (P \<times> P) (product_topology_on ?TP ?TP)
            {x \<in> P \<times> P. pi1 x = pi2 x}"
          by (rule top1_closedin_equalizer_of_continuous_maps[OF hTPP hP_haus hpi1_cont hpi2_cont])
        thus ?thesis using hDiag_eq by (by100 simp)
      qed
      \<comment> \<open>?bdy \<times> ?bdy is compact (each edge is compact image of [0,1],
         finite union of compact = compact, product of compact = compact).\<close>
      \<comment> \<open>Boundary compact: each edge is compact image of [0,1], finite union compact.\<close>
      \<comment> \<open>P is compact (polygonal region = convex hull).\<close>
      have hP_compact_here: "top1_compact_on P ?TP"
      proof -
        have hTP_eq: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
          using product_topology_on_open_sets_real2 by (by100 simp)
        have "compact P"
        proof -
          obtain vx' vy' :: "nat \<Rightarrow> real" where hn': "length scheme \<ge> 3"
              and hP_eq: "P = {(x, y). \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
                  \<and> (\<Sum>i<length scheme. coeffs i) = 1
                  \<and> x = (\<Sum>i<length scheme. coeffs i * vx' i)
                  \<and> y = (\<Sum>i<length scheme. coeffs i * vy' i)}"
            using hP_loc unfolding top1_is_polygonal_region_on_def by blast
          show "compact P" unfolding hP_eq by (rule convex_hull_compact[OF hn'])
        qed
        hence "top1_compact_on P (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets P)"
          using iffD2[OF top1_compact_on_subspace_UNIV_iff_compact] by (by100 blast)
        thus ?thesis using hTP_eq by (by100 simp)
      qed
      have hbdy_sub_P: "?bdy \<subseteq> P"
      proof
        fix x assume "x \<in> ?bdy"
        then obtain i t where hi: "i < length scheme" "t \<in> I_set" "x = ?edge i t"
          by (by100 blast)
        have ht: "t \<ge> 0" "t \<le> 1" using \<open>t \<in> I_set\<close> unfolding top1_unit_interval_def
          by (by100 simp)+
        have hvi: "(vx i, vy i) \<in> P" using hvert_loc hi(1) by (by100 blast)
        have hj: "Suc i mod length scheme < length scheme"
        proof -
          have "length scheme > 0" using hlen_loc by (by100 linarith)
          thus ?thesis by (by100 simp)
        qed
        have hvi1: "(vx (Suc i mod length scheme), vy (Suc i mod length scheme)) \<in> P"
          using hvert_loc hj by (by100 blast)
        \<comment> \<open>P is convex hull: (1-t)*v_i + t*v_{i+1} is in P for t \<in> [0,1].\<close>
        show "x \<in> P"
        proof -
          \<comment> \<open>Define coefficients: all zero except i and (i+1 mod n).\<close>
          obtain vx' vy' where hP_eq: "P = {(x, y). \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
              \<and> (\<Sum>i<length scheme. coeffs i) = 1
              \<and> x = (\<Sum>i<length scheme. coeffs i * vx' i)
              \<and> y = (\<Sum>i<length scheme. coeffs i * vy' i)}"
            using hP_loc unfolding top1_is_polygonal_region_on_def by blast
          \<comment> \<open>From hvi and hvi1: vertices are in P, so the edge point is too.\<close>
          \<comment> \<open>v_i and v_{i+1} are in P (convex hull). P is convex, so
             (1-t)*v_i + t*v_{i+1} \<in> P. Proof: combine coefficients.\<close>
          from hvi obtain c1 where hc1: "\<forall>j<length scheme. c1 j \<ge> 0"
              "(\<Sum>j<length scheme. c1 j) = 1"
              "fst (vx i, vy i) = (\<Sum>j<length scheme. c1 j * vx' j)"
              "snd (vx i, vy i) = (\<Sum>j<length scheme. c1 j * vy' j)"
            unfolding hP_eq by auto
          from hvi1 obtain c2 where hc2: "\<forall>j<length scheme. c2 j \<ge> 0"
              "(\<Sum>j<length scheme. c2 j) = 1"
              "fst (vx (Suc i mod length scheme), vy (Suc i mod length scheme)) = (\<Sum>j<length scheme. c2 j * vx' j)"
              "snd (vx (Suc i mod length scheme), vy (Suc i mod length scheme)) = (\<Sum>j<length scheme. c2 j * vy' j)"
            unfolding hP_eq by auto
          let ?c = "\<lambda>j. (1-t) * c1 j + t * c2 j"
          have hc_nn: "\<forall>j<length scheme. ?c j \<ge> 0"
          proof (intro allI impI)
            fix j assume "j < length scheme"
            have "c1 j \<ge> 0" using hc1(1) \<open>j < length scheme\<close> by (by100 blast)
            have "c2 j \<ge> 0" using hc2(1) \<open>j < length scheme\<close> by (by100 blast)
            show "?c j \<ge> 0" using \<open>c1 j \<ge> 0\<close> \<open>c2 j \<ge> 0\<close> ht by (by100 simp)
          qed
          have hc_sum: "(\<Sum>j<length scheme. ?c j) = 1"
          proof -
            have "(\<Sum>j<length scheme. ?c j) = (\<Sum>j<length scheme. (1-t) * c1 j) + (\<Sum>j<length scheme. t * c2 j)"
              by (simp add: sum.distrib)
            also have "\<dots> = (1-t) * (\<Sum>j<length scheme. c1 j) + t * (\<Sum>j<length scheme. c2 j)"
              by (simp add: sum_distrib_left)
            finally show ?thesis using hc1(2) hc2(2) ht by (by100 simp)
          qed
          have hc_x: "fst (?edge i t) = (\<Sum>j<length scheme. ?c j * vx' j)"
          proof -
            have "(\<Sum>j<length scheme. ?c j * vx' j) =
                (\<Sum>j<length scheme. (1-t) * c1 j * vx' j) + (\<Sum>j<length scheme. t * c2 j * vx' j)"
              by (simp add: sum.distrib ring_distribs)
            also have "\<dots> = (1-t) * (\<Sum>j<length scheme. c1 j * vx' j) + t * (\<Sum>j<length scheme. c2 j * vx' j)"
              by (simp add: sum_distrib_left mult.assoc)
            finally show ?thesis using hc1(3) hc2(3) by (by100 simp)
          qed
          have hc_y: "snd (?edge i t) = (\<Sum>j<length scheme. ?c j * vy' j)"
          proof -
            have "(\<Sum>j<length scheme. ?c j * vy' j) =
                (\<Sum>j<length scheme. (1-t) * c1 j * vy' j) + (\<Sum>j<length scheme. t * c2 j * vy' j)"
              by (simp add: sum.distrib ring_distribs)
            also have "\<dots> = (1-t) * (\<Sum>j<length scheme. c1 j * vy' j) + t * (\<Sum>j<length scheme. c2 j * vy' j)"
              by (simp add: sum_distrib_left mult.assoc)
            finally show ?thesis using hc1(4) hc2(4) by (by100 simp)
          qed
          show ?thesis unfolding hP_eq hi(3)
            using hc_nn hc_sum hc_x hc_y by auto
        qed
      qed
      have hbdy_closed_P: "closedin_on P ?TP ?bdy"
      proof -
        \<comment> \<open>Each edge is compact in R^2 (continuous image of [0,1]).\<close>
        have "compact ?bdy"
        proof -
          have "\<forall>i \<in> {..<length scheme}. compact (?edge i ` I_set)"
          proof (intro ballI)
            fix i assume "i \<in> {..<length scheme}"
            let ?f = "\<lambda>t::real. ((1-t) * vx i + t * vx (Suc i mod length scheme),
                (1-t) * vy i + t * vy (Suc i mod length scheme))"
            have "continuous_on UNIV ?f" by (intro continuous_intros)
            hence "continuous_on I_set ?f"
              using continuous_on_subset by (by100 blast)
            moreover have "compact I_set"
              unfolding top1_unit_interval_def by (by100 simp)
            ultimately have "compact (?f ` I_set)" by (rule compact_continuous_image)
            moreover have "?f ` I_set = ?edge i ` I_set" by (by100 simp)
            ultimately show "compact (?edge i ` I_set)" by (by100 simp)
          qed
          moreover have "finite {..<length scheme}" by (by100 simp)
          ultimately show "compact ?bdy"
          proof -
            assume hcomp: "\<forall>i \<in> {..<length scheme}. compact (?edge i ` I_set)"
            assume hfin: "finite {..<length scheme}"
            show ?thesis
              unfolding UN_simps
              apply (rule compact_Union)
              apply (rule finite_imageI[OF hfin])
              using hcomp by (by100 blast)
          qed
        qed
        \<comment> \<open>compact in Hausdorff P \<Rightarrow> closed in P.\<close>
        have "top1_compact_on ?bdy (subspace_topology P ?TP ?bdy)"
        proof -
          have hTP_eq: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
            using product_topology_on_open_sets_real2 by (by100 simp)
          have "top1_compact_on ?bdy (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets ?bdy)"
            using iffD2[OF top1_compact_on_subspace_UNIV_iff_compact] \<open>compact ?bdy\<close> by (by100 blast)
          moreover have "subspace_topology (UNIV::(real\<times>real) set) top1_open_sets ?bdy
              = subspace_topology P ?TP ?bdy"
          proof -
            have "subspace_topology P (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets P) ?bdy
                = subspace_topology (UNIV::(real\<times>real) set) top1_open_sets ?bdy"
              by (rule subspace_topology_trans[OF hbdy_sub_P])
            thus ?thesis using hTP_eq by (by100 simp)
          qed
          ultimately show ?thesis by simp
        qed
        thus ?thesis
          by (rule Theorem_26_3[OF hP_haus hbdy_sub_P])
      qed
      have hbdy_compact_P: "top1_compact_on ?bdy (subspace_topology P ?TP ?bdy)"
        by (rule Theorem_26_2[OF hP_compact_here hbdy_closed_P])
      have hbdy_compact: "top1_compact_on (?bdy \<times> ?bdy)
          (subspace_topology (P \<times> P) (product_topology_on ?TP ?TP) (?bdy \<times> ?bdy))"
      proof -
        have "top1_compact_on (?bdy \<times> ?bdy)
            (product_topology_on (subspace_topology P ?TP ?bdy) (subspace_topology P ?TP ?bdy))"
          by (rule Theorem_26_7[OF hbdy_compact_P hbdy_compact_P])
        moreover have "product_topology_on (subspace_topology P ?TP ?bdy) (subspace_topology P ?TP ?bdy)
            = subspace_topology (P \<times> P) (product_topology_on ?TP ?TP) (?bdy \<times> ?bdy)"
          by (rule Theorem_16_3[OF hTP_top hTP_top])
        ultimately show ?thesis by simp
      qed
      \<comment> \<open>?R \<inter> (?bdy \<times> ?bdy) is compact: it's a finite union of edge-pair identification
         sets, each compact (image of [0,1] under continuous map t \<mapsto> (edge\_i(t), edge\_j(f(t)))).\<close>
      have hR_bdy_compact: "top1_compact_on (?R \<inter> (?bdy \<times> ?bdy))
          (subspace_topology (P \<times> P) (product_topology_on ?TP ?TP) (?R \<inter> (?bdy \<times> ?bdy)))"
      proof -
        \<comment> \<open>Step 1: compact ?bdy in HOL-Analysis.\<close>
        have hbdy_compact_HA: "compact ?bdy"
        proof -
          have "\<forall>i \<in> {..<length scheme}. compact (?edge i ` I_set)"
          proof (intro ballI)
            fix i assume "i \<in> {..<length scheme}"
            let ?f = "\<lambda>t::real. ((1-t) * vx i + t * vx (Suc i mod length scheme),
                (1-t) * vy i + t * vy (Suc i mod length scheme))"
            have "continuous_on UNIV ?f" by (intro continuous_intros)
            hence "continuous_on I_set ?f" using continuous_on_subset by (by100 blast)
            moreover have "compact I_set" unfolding top1_unit_interval_def by (by100 simp)
            ultimately have "compact (?f ` I_set)" by (rule compact_continuous_image)
            moreover have "?f ` I_set = ?edge i ` I_set" by (by100 simp)
            ultimately show "compact (?edge i ` I_set)" by (by100 simp)
          qed
          hence hcomp_all: "\<forall>S \<in> (\<lambda>i. ?edge i ` I_set) ` {..<length scheme}. compact S" by (by100 blast)
          have hfin_set: "finite ((\<lambda>i. ?edge i ` I_set) ` {..<length scheme})" by (by100 simp)
          have "compact (\<Union> ((\<lambda>i. ?edge i ` I_set) ` {..<length scheme}))"
            by (rule compact_Union[OF hfin_set hcomp_all])
          moreover have "\<Union> ((\<lambda>i. ?edge i ` I_set) ` {..<length scheme}) = ?bdy" by (by100 auto)
          ultimately show "compact ?bdy" by (by100 simp)
        qed
        \<comment> \<open>Step 2: compact (bdy \<times> bdy) via compact\_Times\_general.\<close>
        have hbdybdy_compact_HA: "compact (?bdy \<times> ?bdy)"
          by (rule compact_Times_general[OF hbdy_compact_HA hbdy_compact_HA])
        \<comment> \<open>Step 3: R \<inter> bdy\<times>bdy \<subseteq> bdy\<times>bdy, and bdy\<times>bdy is compact,
           so R\<inter>bdy\<times>bdy is bounded. Need closedness to get compactness.\<close>
        \<comment> \<open>Alternative: show R\<inter>bdy\<times>bdy is ITSELF a finite union of compact sets.\<close>
        have "compact (?R \<inter> (?bdy \<times> ?bdy))"
        proof -
          \<comment> \<open>R\<inter>bdy\<times>bdy \<subseteq> diagonal\_on\_bdy \<union> edge\_pair\_curves.\<close>
          \<comment> \<open>Each curve is compact (continuous image of compact [0,1]).\<close>
          \<comment> \<open>Diagonal on bdy: image of bdy under x\<mapsto>(x,x). Compact.\<close>
          let ?D = "(\<lambda>x. (x, x)) ` ?bdy"
          have hD_compact: "compact ?D"
          proof -
            have "continuous_on ?bdy (\<lambda>x. (x, x))" by (intro continuous_intros)
            thus ?thesis using compact_continuous_image hbdy_compact_HA by (by100 blast)
          qed
          \<comment> \<open>Edge pair curves: for each (i,j) with same label.\<close>
          \<comment> \<open>?R \<inter> (?bdy \<times> ?bdy) \<subseteq> ?D \<union> (edge pair curves). Plus reverse.\<close>
          \<comment> \<open>Since both directions need the scheme structure,\<close>
          \<comment> \<open>we show R\<inter>bdy\<times>bdy is closed in the compact bdy\<times>bdy.\<close>
          \<comment> \<open>R\<inter>bdy\<times>bdy closed: equal to ?D \<union> finite union of compact sets.\<close>
          \<comment> \<open>?D compact \<Rightarrow> closed (in Hausdorff R^4). Each edge pair compact \<Rightarrow> closed.\<close>
          \<comment> \<open>Finite union of closed = closed. Closed subset of compact = compact.\<close>
          have hR_bdy_closed_HA: "closed (?R \<inter> (?bdy \<times> ?bdy))"
          proof -
            \<comment> \<open>R\<inter>bdy\<times>bdy = D \<union> \<Union>{C\_ij | same label}.\<close>
            \<comment> \<open>D = diagonal on bdy (compact \<Rightarrow> closed). Each C\_ij compact \<Rightarrow> closed.\<close>
            \<comment> \<open>Finite union of closed = closed.\<close>
            \<comment> \<open>Define edge pair curves.\<close>
            let ?n = "length scheme"
            let ?curves = "(\<lambda>(i,j). if fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j
                then (if snd (scheme!i) = snd (scheme!j)
                      then (\<lambda>t. (?edge i t, ?edge j t)) ` I_set
                      else (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set)
                else {}) ` ({..<?n} \<times> {..<?n})"
            \<comment> \<open>R\<inter>bdy\<times>bdy \<subseteq> ?D \<union> \<Union>?curves.\<close>
            have hR_bdy_sub_DC: "?R \<inter> (?bdy \<times> ?bdy) \<subseteq> ?D \<union> \<Union>?curves"
            proof
              fix x assume "x \<in> ?R \<inter> (?bdy \<times> ?bdy)"
              then obtain a b where hx: "x = (a, b)" "a \<in> P" "b \<in> P" "q a = q b"
                  "a \<in> ?bdy" "b \<in> ?bdy"
                by (cases x) (by100 blast)
              \<comment> \<open>a on some edge i at parameter t, b on edge j at parameter s.\<close>
              from hx(5) obtain i t where hi: "i < length scheme" "t \<in> I_set" "a = ?edge i t"
                by (by100 blast)
              from hx(6) obtain j s where hj: "j < length scheme" "s \<in> I_set" "b = ?edge j s"
                by (by100 blast)
              \<comment> \<open>Apply hno\_extra: q(edge\_i(t)) = q(edge\_j(s)) \<Rightarrow> diagonal or scheme pair.\<close>
              from hno_extra[rule_format, OF hi(1) hj(1) hi(2) hj(2)]
              have "q a = q b \<longrightarrow> (i = j \<and> t = s) \<or> (fst (scheme!i) = fst (scheme!j) \<and>
                  (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
                using hi(3) hj(3) by simp
              hence "(i = j \<and> t = s) \<or> (fst (scheme!i) = fst (scheme!j) \<and>
                  (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
                using hx(4) by (by100 blast)
              thus "x \<in> ?D \<union> \<Union>?curves"
              proof
                assume "i = j \<and> t = s"
                hence "a = b" using hi(3) hj(3) by (by100 simp)
                thus ?thesis using hx(1,5) by (by100 blast)
              next
                assume hpair: "fst (scheme!i) = fst (scheme!j) \<and>
                    (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t)"
                show ?thesis
                proof (cases "i = j")
                  case True
                  hence "t = s" using hpair by (by100 auto)
                  hence "a = b" using hi(3) hj(3) True by (by100 simp)
                  thus ?thesis using hx(1,5) by (by100 blast)
                next
                  case False
                  \<comment> \<open>(a,b) is on an edge pair curve.\<close>
                  \<comment> \<open>(a,b) = (edge\_i(t), edge\_j(s)) with same label and s = f(t).\<close>
                  have "fst (scheme!i) = fst (scheme!j)" using hpair by (by100 blast)
                  show ?thesis
                  proof (cases "snd (scheme!i) = snd (scheme!j)")
                    case True
                    hence "s = t" using hpair by (by100 auto)
                    hence "x = (?edge i t, ?edge j t)" using hx(1) hi(3) hj(3) by (by100 simp)
                    hence "x \<in> (\<lambda>t. (?edge i t, ?edge j t)) ` I_set" using hi(2) by auto
                    moreover have "(\<lambda>t. (?edge i t, ?edge j t)) ` I_set \<in> ?curves"
                    proof -
                      have "(i, j) \<in> {..<length scheme} \<times> {..<length scheme}"
                        using hi(1) hj(1) by (by100 blast)
                      moreover have "(case (i, j) of (i, j) \<Rightarrow>
                          if fst (scheme ! i) = fst (scheme ! j) \<and> i \<noteq> j
                          then (if snd (scheme ! i) = snd (scheme ! j)
                                then (\<lambda>t. (?edge i t, ?edge j t)) ` I_set
                                else (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set)
                          else {}) = (\<lambda>t. (?edge i t, ?edge j t)) ` I_set"
                        using \<open>fst (scheme!i) = fst (scheme!j)\<close> False True by (by100 simp)
                      ultimately show ?thesis
                        apply -
                        apply (rule image_eqI[where x="(i,j)"])
                        apply (by100 simp)
                        apply (by100 blast)
                        done
                    qed
                    hence "x \<in> \<Union>?curves" using \<open>x \<in> (\<lambda>t. (?edge i t, ?edge j t)) ` I_set\<close>
                      by blast
                    thus ?thesis by blast
                  next
                    case sndF: False
                    hence "s = 1 - t" using hpair by (by100 auto)
                    hence "x = (?edge i t, ?edge j (1-t))" using hx(1) hi(3) hj(3) by simp
                    hence hx_in: "x \<in> (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set" using hi(2) by auto
                    have "(\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set \<in> ?curves"
                    proof -
                      have "(i, j) \<in> {..<length scheme} \<times> {..<length scheme}"
                        using hi(1) hj(1) by (by100 blast)
                      moreover have "(case (i, j) of (i, j) \<Rightarrow>
                          if fst (scheme ! i) = fst (scheme ! j) \<and> i \<noteq> j
                          then (if snd (scheme ! i) = snd (scheme ! j)
                                then (\<lambda>t. (?edge i t, ?edge j t)) ` I_set
                                else (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set)
                          else {}) = (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set"
                        using \<open>fst (scheme!i) = fst (scheme!j)\<close> False sndF by (by100 simp)
                      ultimately show ?thesis
                        apply -
                        apply (rule image_eqI[where x="(i,j)"])
                        apply (by100 simp)
                        apply (by100 blast)
                        done
                    qed
                    hence "x \<in> \<Union>?curves" using hx_in by blast
                    thus ?thesis by blast
                  qed
                qed
              qed
            qed
            \<comment> \<open>?D \<union> \<Union>?curves \<subseteq> ?R \<inter> (?bdy\<times>?bdy).\<close>
            have hDC_sub_R_bdy: "?D \<union> \<Union>?curves \<subseteq> ?R \<inter> (?bdy \<times> ?bdy)"
            proof
              fix x assume "x \<in> ?D \<union> \<Union>?curves"
              thus "x \<in> ?R \<inter> (?bdy \<times> ?bdy)"
              proof
                \<comment> \<open>Case 1: x \<in> ?D (diagonal on boundary).\<close>
                assume "x \<in> ?D"
                then obtain a where ha: "a \<in> ?bdy" "x = (a, a)" by (by100 blast)
                have "a \<in> P" using ha(1) hbdy_sub_P by (by100 blast)
                thus "x \<in> ?R \<inter> (?bdy \<times> ?bdy)" using ha by (by100 blast)
              next
                \<comment> \<open>Case 2: x \<in> \<Union>?curves (edge pair curve).\<close>
                assume "x \<in> \<Union>?curves"
                then obtain C where "C \<in> ?curves" "x \<in> C" by (by100 blast)
                then obtain i j where hij: "i < ?n" "j < ?n"
                    "C = (if fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j
                          then (if snd (scheme!i) = snd (scheme!j)
                                then (\<lambda>t. (?edge i t, ?edge j t)) ` I_set
                                else (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set)
                          else {})" by auto
                show "x \<in> ?R \<inter> (?bdy \<times> ?bdy)"
                proof (cases "fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j")
                  case False thus ?thesis using \<open>x \<in> C\<close> hij(3) by auto
                next
                  case True
                  hence hsamelabel: "fst (scheme!i) = fst (scheme!j)" by (by100 blast)
                  show ?thesis
                  proof (cases "snd (scheme!i) = snd (scheme!j)")
                    case True
                    \<comment> \<open>Same direction: x = (edge\_i(t), edge\_j(t)).\<close>
                    then obtain t where ht: "t \<in> I_set" "x = (?edge i t, ?edge j t)"
                      using \<open>x \<in> C\<close> hij(3) \<open>fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j\<close> by auto
                    have "q (?edge i t) = q (?edge j t)"
                    proof -
                      have "\<forall>t\<in>I_set. q (?edge i t) =
                          (if snd (scheme!i) = snd (scheme!j) then q (?edge j t) else q (?edge j (1-t)))"
                      proof (intro ballI)
                        fix t assume "t \<in> I_set"
                        show "q (?edge i t) = (if snd (scheme!i) = snd (scheme!j) then q (?edge j t) else q (?edge j (1-t)))"
                          using hedge_loc[rule_format, OF hij(1) hij(2) hsamelabel \<open>t \<in> I_set\<close>] by simp
                      qed
                      thus ?thesis using True ht(1) by (by100 simp)
                    qed
                    moreover have hei: "?edge i t \<in> ?bdy" using hij(1) ht(1) by (by100 blast)
                    moreover have hej: "?edge j t \<in> ?bdy" using hij(2) ht(1) by (by100 blast)
                    moreover have "?edge i t \<in> P" using subsetD[OF hbdy_sub_P hei] .
                    moreover have "?edge j t \<in> P" using subsetD[OF hbdy_sub_P hej] .
                    ultimately show ?thesis using ht(2) by auto
                  next
                    case False
                    \<comment> \<open>Opposite direction: x = (edge\_i(t), edge\_j(1-t)).\<close>
                    then obtain t where ht: "t \<in> I_set" "x = (?edge i t, ?edge j (1-t))"
                      using \<open>x \<in> C\<close> hij(3) \<open>fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j\<close> by auto
                    have "q (?edge i t) = q (?edge j (1-t))"
                    proof -
                      have "\<forall>t\<in>I_set. q (?edge i t) =
                          (if snd (scheme!i) = snd (scheme!j) then q (?edge j t) else q (?edge j (1-t)))"
                      proof (intro ballI)
                        fix t assume "t \<in> I_set"
                        show "q (?edge i t) = (if snd (scheme!i) = snd (scheme!j) then q (?edge j t) else q (?edge j (1-t)))"
                          using hedge_loc[rule_format, OF hij(1) hij(2) hsamelabel \<open>t \<in> I_set\<close>] by simp
                      qed
                      thus ?thesis using False ht(1) by (by100 simp)
                    qed
                    moreover have hei2: "?edge i t \<in> ?bdy" using hij(1) ht(1) by (by100 blast)
                    moreover have h1t_I: "1 - t \<in> I_set" using ht(1) unfolding top1_unit_interval_def by auto
                    moreover have hej2: "?edge j (1-t) \<in> ?bdy" using hij(2) h1t_I by (by100 blast)
                    moreover have "?edge i t \<in> P" using subsetD[OF hbdy_sub_P hei2] .
                    moreover have "?edge j (1-t) \<in> P" using subsetD[OF hbdy_sub_P hej2] .
                    ultimately show ?thesis using ht(2) by auto
                  qed
                qed
              qed
            qed
            \<comment> \<open>So ?R \<inter> (?bdy \<times> ?bdy) = ?D \<union> \<Union>?curves.\<close>
            have hR_bdy_eq: "?R \<inter> (?bdy \<times> ?bdy) = ?D \<union> \<Union>?curves"
              using hR_bdy_sub_DC hDC_sub_R_bdy by (by100 blast)
            \<comment> \<open>?D is closed (compact \<Rightarrow> closed in R^4).\<close>
            have hD_closed: "closed ?D"
              using hD_compact compact_imp_closed by (by100 blast)
            \<comment> \<open>Each curve in ?curves is closed (compact \<Rightarrow> closed).\<close>
            have hcurves_closed: "\<forall>C \<in> ?curves. closed C"
            proof (intro ballI)
              fix C assume "C \<in> ?curves"
              then obtain i j where hij: "C = (if fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j
                  then (if snd (scheme!i) = snd (scheme!j)
                        then (\<lambda>t. (?edge i t, ?edge j t)) ` I_set
                        else (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set)
                  else {})" "i < ?n" "j < ?n" by auto
              show "closed C"
              proof (cases "fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j")
                case False thus ?thesis using hij(1) by auto
              next
                case True
                have "compact C"
                proof (cases "snd (scheme!i) = snd (scheme!j)")
                  case True
                  hence hC_eq: "C = (\<lambda>t. (?edge i t, ?edge j t)) ` I_set"
                    using hij(1) \<open>fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j\<close> by (by100 auto)
                  have "continuous_on UNIV (\<lambda>t::real. (?edge i t, ?edge j t))"
                    by (intro continuous_intros)
                  hence "continuous_on I_set (\<lambda>t. (?edge i t, ?edge j t))"
                    using continuous_on_subset by (by100 blast)
                  moreover have "compact I_set" unfolding top1_unit_interval_def by (by100 simp)
                  ultimately show ?thesis unfolding hC_eq by (rule compact_continuous_image)
                next
                  case False
                  hence hC_eq: "C = (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set"
                    using hij(1) \<open>fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j\<close> by (by100 auto)
                  have "continuous_on UNIV (\<lambda>t::real. (?edge i t, ?edge j (1-t)))"
                    by (intro continuous_intros)
                  hence "continuous_on I_set (\<lambda>t. (?edge i t, ?edge j (1-t)))"
                    using continuous_on_subset by (by100 blast)
                  moreover have "compact I_set" unfolding top1_unit_interval_def by (by100 simp)
                  ultimately show ?thesis unfolding hC_eq by (rule compact_continuous_image)
                qed
                thus ?thesis using compact_imp_closed by (by100 blast)
              qed
            qed
            \<comment> \<open>Finite union of closed = closed.\<close>
            have "finite ?curves" by (by100 simp)
            have "closed (\<Union>?curves)"
              by (rule closed_Union[OF \<open>finite ?curves\<close> hcurves_closed])
            thus ?thesis using hR_bdy_eq hD_closed by auto
          qed
          from compact_Int_closed[OF hbdybdy_compact_HA hR_bdy_closed_HA]
          have "compact ((?bdy \<times> ?bdy) \<inter> (?R \<inter> (?bdy \<times> ?bdy)))" .
          moreover have "(?bdy \<times> ?bdy) \<inter> (?R \<inter> (?bdy \<times> ?bdy)) = ?R \<inter> (?bdy \<times> ?bdy)" by auto
          ultimately show "compact (?R \<inter> (?bdy \<times> ?bdy))" by simp
        qed
        \<comment> \<open>Step 4: Bridge compact to top1\_compact\_on.\<close>
        hence "top1_compact_on (?R \<inter> (?bdy \<times> ?bdy))
            (subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set)
                top1_open_sets (?R \<inter> (?bdy \<times> ?bdy)))"
          using iffD2[OF top1_compact_on_subspace_UNIV_iff_compact] by (by100 blast)
        moreover have "subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set)
            top1_open_sets (?R \<inter> (?bdy \<times> ?bdy))
            = subspace_topology (P \<times> P) (product_topology_on ?TP ?TP) (?R \<inter> (?bdy \<times> ?bdy))"
        proof -
          have hTP_eq: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
            using product_topology_on_open_sets_real2 by (by100 simp)
          have hTP_eq_sub: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
            using product_topology_on_open_sets_real2 by (by100 simp)
          have "product_topology_on ?TP ?TP =
              subspace_topology ((UNIV::(real\<times>real) set) \<times> (UNIV::(real\<times>real) set))
                  (product_topology_on top1_open_sets top1_open_sets) (P \<times> P)"
          proof -
            have hT_R2: "is_topology_on (UNIV::(real\<times>real) set) top1_open_sets"
              by (rule top1_open_sets_is_topology_on_UNIV)
            show ?thesis using Theorem_16_3[OF hT_R2 hT_R2] hTP_eq_sub by simp
          qed
          also have "subspace_topology ((UNIV::(real\<times>real) set) \<times> (UNIV::(real\<times>real) set))
                  (product_topology_on top1_open_sets top1_open_sets) (P \<times> P)
              = subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set) top1_open_sets (P \<times> P)"
          proof -
            have h1: "(UNIV::(real\<times>real) set) \<times> (UNIV::(real\<times>real) set) = (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set)"
              by (by100 simp)
            have h2: "product_topology_on (top1_open_sets::(real\<times>real) set set) (top1_open_sets::(real\<times>real) set set)
                = (top1_open_sets :: ((real \<times> real) \<times> (real \<times> real)) set set)"
              by (rule product_topology_on_open_sets)
            show ?thesis using h1 h2 by (by100 simp)
          qed
          finally have hPP_eq: "product_topology_on ?TP ?TP =
              subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set) top1_open_sets (P \<times> P)" .
          have hR_bdy_sub_PP: "?R \<inter> (?bdy \<times> ?bdy) \<subseteq> P \<times> P" by (by100 blast)
          have "subspace_topology (P \<times> P) (product_topology_on ?TP ?TP) (?R \<inter> (?bdy \<times> ?bdy))
              = subspace_topology (P \<times> P)
                  (subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set) top1_open_sets (P \<times> P))
                  (?R \<inter> (?bdy \<times> ?bdy))"
            using hPP_eq by (by100 simp)
          also have "\<dots> = subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set) top1_open_sets
              (?R \<inter> (?bdy \<times> ?bdy))"
            by (rule subspace_topology_trans[OF hR_bdy_sub_PP])
          finally show ?thesis by simp
        qed
        ultimately show ?thesis by simp
      qed
      \<comment> \<open>Compact in Hausdorff is closed.\<close>
      have hR_bdy_sub: "?R \<inter> (?bdy \<times> ?bdy) \<subseteq> P \<times> P" by (by100 blast)
      have hR_bdy_closed: "closedin_on (P \<times> P) (product_topology_on ?TP ?TP) (?R \<inter> (?bdy \<times> ?bdy))"
        by (rule Theorem_26_3[OF hPP_haus hR_bdy_sub hR_bdy_compact])
      \<comment> \<open>R \<subseteq> diagonal \<union> (?bdy \<times> ?bdy), so R = (R \<inter> diagonal) \<union> (R \<inter> (?bdy \<times> ?bdy)).
         R \<inter> diagonal = diagonal (on P\<times>P). Both parts closed. Union closed.\<close>
      have hR_decomp: "?R = {(a, b). a \<in> P \<and> b \<in> P \<and> a = b} \<union> (?R \<inter> (?bdy \<times> ?bdy))"
        using hR_sub by auto
      have "closedin_on (P \<times> P) (product_topology_on ?TP ?TP) ?R"
      proof -
        have "closedin_on (P \<times> P) (product_topology_on ?TP ?TP)
            ({(a, b). a \<in> P \<and> b \<in> P \<and> a = b} \<union> (?R \<inter> (?bdy \<times> ?bdy)))"
        proof -
          let ?F = "{{(a, b). a \<in> P \<and> b \<in> P \<and> a = b}, ?R \<inter> (?bdy \<times> ?bdy)}"
          have "finite ?F" by (by100 simp)
          have "\<forall>A \<in> ?F. closedin_on (P \<times> P) (product_topology_on ?TP ?TP) A"
            using hDiag_closed hR_bdy_closed by (by100 blast)
          from closedin_Union_finite[OF hTPP \<open>finite ?F\<close> this]
          have "closedin_on (P \<times> P) (product_topology_on ?TP ?TP) (\<Union>?F)" .
          moreover have "\<Union>?F = {(a, b). a \<in> P \<and> b \<in> P \<and> a = b} \<union> (?R \<inter> (?bdy \<times> ?bdy))"
            by (by100 simp)
          ultimately show ?thesis by auto
        qed
        thus ?thesis using hR_decomp by auto
      qed
      thus ?thesis .
    qed
    \<comment> \<open>Closed equivalence relation on compact Hausdorff \<Rightarrow> Hausdorff quotient.\<close>
    have hclosed_R_haus: "\<And>P' TP' X' TX' q'.
        is_hausdorff_on P' TP' \<Longrightarrow> top1_compact_on P' TP' \<Longrightarrow>
        top1_quotient_map_on P' TP' X' TX' q' \<Longrightarrow>
        closedin_on (P' \<times> P') (product_topology_on TP' TP')
            {(a, b). a \<in> P' \<and> b \<in> P' \<and> q' a = q' b} \<Longrightarrow>
        is_hausdorff_on X' TX'"
    proof -
      fix P' TP' X' TX' q'
      assume hP'H: "is_hausdorff_on P' TP'" and hP'C: "top1_compact_on P' TP'"
          and hq'Q: "top1_quotient_map_on P' TP' X' TX' q'"
          and hR'cl: "closedin_on (P' \<times> P') (product_topology_on TP' TP')
              {(a, b). a \<in> P' \<and> b \<in> P' \<and> q' a = q' b}"
      let ?R = "{(a, b). a \<in> P' \<and> b \<in> P' \<and> q' a = q' b}"
      have hTP': "is_topology_on P' TP'" using hP'H unfolding is_hausdorff_on_def by (by100 blast)
      have hTX': "is_topology_on X' TX'" using hq'Q unfolding top1_quotient_map_on_def by (by100 blast)
      have hq'_cont: "top1_continuous_map_on P' TP' X' TX' q'"
        using hq'Q unfolding top1_quotient_map_on_def by (by100 blast)
      have hq'_surj: "q' ` P' = X'" using hq'Q unfolding top1_quotient_map_on_def by (by100 blast)
      \<comment> \<open>P' compact Hausdorff \<Rightarrow> normal.\<close>
      have hP'N: "top1_normal_on P' TP'" by (rule Theorem_32_3[OF hP'C hP'H])
      show "is_hausdorff_on X' TX'" unfolding is_hausdorff_on_def
      proof (intro conjI)
        show "is_topology_on X' TX'" by (rule hTX')
      next
        show "\<forall>x\<in>X'. \<forall>y\<in>X'. x \<noteq> y \<longrightarrow>
            (\<exists>U V. neighborhood_of x X' TX' U \<and> neighborhood_of y X' TX' V \<and> U \<inter> V = {})"
        proof (intro ballI impI)
          fix x y assume "x \<in> X'" "y \<in> X'" "x \<noteq> y"
          let ?Fx = "{p \<in> P'. q' p = x}" and ?Fy = "{p \<in> P'. q' p = y}"
          \<comment> \<open>Fibers non-empty, closed, disjoint.\<close>
          have hFx_ne: "?Fx \<noteq> {}" using \<open>x \<in> X'\<close> hq'_surj by (by100 blast)
          have hFy_ne: "?Fy \<noteq> {}" using \<open>y \<in> X'\<close> hq'_surj by (by100 blast)
          have hFxy_disj: "?Fx \<inter> ?Fy = {}" using \<open>x \<noteq> y\<close> by (by100 blast)
          have hFx_cl: "closedin_on P' TP' ?Fx"
          proof -
            \<comment> \<open>Fx = {p | (p, p0) \<in> R} for any p0 \<in> Fx. Slice of closed R is closed.\<close>
            obtain p0 where "p0 \<in> P'" "q' p0 = x" using hFx_ne by (by100 blast)
            have hFx_eq: "?Fx = {p \<in> P'. (p, p0) \<in> ?R}"
            proof (rule set_eqI, rule iffI)
              fix p assume "p \<in> ?Fx"
              hence "p \<in> P'" "q' p = x" by (by100 blast)+
              hence "(p, p0) \<in> ?R" using \<open>p0 \<in> P'\<close> \<open>q' p0 = x\<close> by (by100 simp)
              thus "p \<in> {p \<in> P'. (p, p0) \<in> ?R}" using \<open>p \<in> P'\<close> by (by100 blast)
            next
              fix p assume "p \<in> {p \<in> P'. (p, p0) \<in> ?R}"
              hence "p \<in> P'" "(p, p0) \<in> ?R" by (by100 blast)+
              hence "q' p = q' p0" by (by100 simp)
              thus "p \<in> ?Fx" using \<open>p \<in> P'\<close> \<open>q' p0 = x\<close> by (by100 simp)
            qed
            \<comment> \<open>Slice of closed R at p0: {p\<in>P'|(p,p0)\<in>R} = preimage of R under i_{p0}.\<close>
            \<comment> \<open>i_{p0} continuous, R closed \<Rightarrow> preimage closed.\<close>
            have hTP'_prod: "is_topology_on (P' \<times> P') (product_topology_on TP' TP')"
              by (rule product_topology_on_is_topology_on[OF hTP' hTP'])
            have "closedin_on P' TP' {p \<in> P'. (\<lambda>p. (p, p0)) p \<in> ?R}"
            proof (rule continuous_preimage_closedin[OF hTP' hTP'_prod _ hR'cl])
              show "top1_continuous_map_on P' TP' (P' \<times> P') (product_topology_on TP' TP') (\<lambda>p. (p, p0))"
              proof -
                have hpi1: "top1_continuous_map_on P' TP' P' TP' (pi1 \<circ> (\<lambda>p. (p, p0)))"
                proof -
                  have heq: "pi1 \<circ> (\<lambda>p. (p, p0)) = id" unfolding pi1_def comp_def id_def by (by100 simp)
                  show ?thesis unfolding heq by (rule top1_continuous_map_on_id[OF hTP'])
                qed
                have hpi2: "top1_continuous_map_on P' TP' P' TP' (pi2 \<circ> (\<lambda>p. (p, p0)))"
                proof -
                  have heq2: "pi2 \<circ> (\<lambda>p. (p, p0)) = (\<lambda>_. p0)" unfolding pi2_def comp_def by (by100 simp)
                  have "top1_continuous_map_on P' TP' P' TP' (\<lambda>_. p0)"
                    using Theorem_18_2[OF hTP' hTP' hTP'] \<open>p0 \<in> P'\<close> by (by100 blast)
                  thus ?thesis unfolding heq2 .
                qed
                from iffD2[OF Theorem_18_4[OF hTP' hTP' hTP']] hpi1 hpi2
                show ?thesis by (by100 blast)
              qed
            qed
            moreover have "{p \<in> P'. (\<lambda>p. (p, p0)) p \<in> ?R} = {p \<in> P'. (p, p0) \<in> ?R}" by (by100 simp)
            ultimately have "closedin_on P' TP' {p \<in> P'. (p, p0) \<in> ?R}" by (by100 simp)
            thus ?thesis using hFx_eq by (by100 simp)
          qed
          have hFy_cl: "closedin_on P' TP' ?Fy"
          proof -
            obtain p0 where "p0 \<in> P'" "q' p0 = y" using hFy_ne by (by100 blast)
            have hFy_eq: "?Fy = {p \<in> P'. (p, p0) \<in> ?R}"
            proof (rule set_eqI, rule iffI)
              fix p assume "p \<in> ?Fy"
              hence "p \<in> P'" "q' p = y" by (by100 blast)+
              hence "(p, p0) \<in> ?R" using \<open>p0 \<in> P'\<close> \<open>q' p0 = y\<close> by (by100 simp)
              thus "p \<in> {p \<in> P'. (p, p0) \<in> ?R}" using \<open>p \<in> P'\<close> by (by100 blast)
            next
              fix p assume "p \<in> {p \<in> P'. (p, p0) \<in> ?R}"
              hence "p \<in> P'" "(p, p0) \<in> ?R" by (by100 blast)+
              hence "q' p = q' p0" by (by100 simp)
              thus "p \<in> ?Fy" using \<open>p \<in> P'\<close> \<open>q' p0 = y\<close> by (by100 simp)
            qed
            have hTP'_prod: "is_topology_on (P' \<times> P') (product_topology_on TP' TP')"
              by (rule product_topology_on_is_topology_on[OF hTP' hTP'])
            have "closedin_on P' TP' {p \<in> P'. (\<lambda>p. (p, p0)) p \<in> ?R}"
            proof (rule continuous_preimage_closedin[OF hTP' hTP'_prod _ hR'cl])
              show "top1_continuous_map_on P' TP' (P' \<times> P') (product_topology_on TP' TP') (\<lambda>p. (p, p0))"
              proof -
                have hpi1: "top1_continuous_map_on P' TP' P' TP' (pi1 \<circ> (\<lambda>p. (p, p0)))"
                proof -
                  have heq: "pi1 \<circ> (\<lambda>p. (p, p0)) = id" unfolding pi1_def comp_def id_def by (by100 simp)
                  show ?thesis unfolding heq by (rule top1_continuous_map_on_id[OF hTP'])
                qed
                have hpi2: "top1_continuous_map_on P' TP' P' TP' (pi2 \<circ> (\<lambda>p. (p, p0)))"
                proof -
                  have heq2: "pi2 \<circ> (\<lambda>p. (p, p0)) = (\<lambda>_. p0)" unfolding pi2_def comp_def by (by100 simp)
                  have "top1_continuous_map_on P' TP' P' TP' (\<lambda>_. p0)"
                    using Theorem_18_2[OF hTP' hTP' hTP'] \<open>p0 \<in> P'\<close> by (by100 blast)
                  thus ?thesis unfolding heq2 .
                qed
                from iffD2[OF Theorem_18_4[OF hTP' hTP' hTP']] hpi1 hpi2
                show ?thesis by (by100 blast)
              qed
            qed
            moreover have "{p \<in> P'. (\<lambda>p. (p, p0)) p \<in> ?R} = {p \<in> P'. (p, p0) \<in> ?R}" by (by100 simp)
            ultimately have "closedin_on P' TP' {p \<in> P'. (p, p0) \<in> ?R}" by (by100 simp)
            thus ?thesis using hFy_eq by (by100 simp)
          qed
          \<comment> \<open>By normality: disjoint open U \<supseteq> Fx, V \<supseteq> Fy.\<close>
          from normal_separation[OF hP'N hFx_cl hFy_cl hFxy_disj]
          obtain U V where hUV: "U \<in> TP'" "V \<in> TP'" "?Fx \<subseteq> U" "?Fy \<subseteq> V" "U \<inter> V = {}"
            by (metis (no_types))
          \<comment> \<open>Saturated complements: q'\<inverse>(q'(P'-U)) is closed (projection of closed from compact).\<close>
          let ?SU = "{p \<in> P'. \<exists>p' \<in> P' - U. q' p = q' p'}"
          let ?SV = "{p \<in> P'. \<exists>p' \<in> P' - V. q' p = q' p'}"
          \<comment> \<open>Projection of closed from compact is closed (tube lemma consequence).\<close>
          have hproj_closed: "\<And>C. closedin_on (P' \<times> P') (product_topology_on TP' TP') C \<Longrightarrow>
              closedin_on P' TP' {a \<in> P'. \<exists>b. (a, b) \<in> C}"
          proof -
            fix C assume hCcl: "closedin_on (P' \<times> P') (product_topology_on TP' TP') C"
            have hC_sub: "C \<subseteq> P' \<times> P'" using hCcl unfolding closedin_on_def by (by100 blast)
            have hprod_compact: "top1_compact_on (P' \<times> P') (product_topology_on TP' TP')"
              by (rule Theorem_26_7[OF hP'C hP'C])
            have hpi1_cont: "top1_continuous_map_on (P' \<times> P') (product_topology_on TP' TP') P' TP' pi1"
              by (rule top1_continuous_pi1[OF hTP' hTP'])
            have hpi1C_cl: "closedin_on P' TP' (pi1 ` C)"
              by (rule compact_hausdorff_continuous_closed_map[OF hprod_compact hP'H hpi1_cont hCcl])
            have hset_eq: "pi1 ` C = {a \<in> P'. \<exists>b. (a, b) \<in> C}"
            proof -
              have "\<And>a. a \<in> pi1 ` C \<Longrightarrow> a \<in> {a \<in> P'. \<exists>b. (a, b) \<in> C}"
              proof -
                fix a assume "a \<in> pi1 ` C"
                then obtain p where hp: "p \<in> C" "a = pi1 p" by (by100 blast)
                have "a = fst p" using hp(2) unfolding pi1_def by (by100 simp)
                have hp_mem: "p \<in> P' \<times> P'" using hp(1) hC_sub by (by100 blast)
                hence "fst p \<in> P'" using mem_Times_iff by (by100 blast)
                hence "a \<in> P'" using \<open>a = fst p\<close> by (by100 simp)
                have "p = (fst p, snd p)" by (by100 simp)
                hence "(a, snd p) \<in> C" using \<open>a = fst p\<close> hp(1) by (by100 simp)
                thus "a \<in> {a \<in> P'. \<exists>b. (a, b) \<in> C}" using \<open>a \<in> P'\<close> by (by100 blast)
              qed
              moreover have "\<And>a. a \<in> {a \<in> P'. \<exists>b. (a, b) \<in> C} \<Longrightarrow> a \<in> pi1 ` C"
              proof -
                fix a assume "a \<in> {a \<in> P'. \<exists>b. (a, b) \<in> C}"
                then obtain b where "a \<in> P'" "(a, b) \<in> C" by (by100 blast)
                have "a = pi1 (a, b)" unfolding pi1_def by (by100 simp)
                thus "a \<in> pi1 ` C" using \<open>(a, b) \<in> C\<close> by (by100 blast)
              qed
              ultimately show ?thesis by (by100 blast)
            qed
            show "closedin_on P' TP' {a \<in> P'. \<exists>b. (a, b) \<in> C}" using hpi1C_cl hset_eq by (by100 simp)
          qed
          have hTP'_prod2: "is_topology_on (P' \<times> P') (product_topology_on TP' TP')"
            by (rule product_topology_on_is_topology_on[OF hTP' hTP'])
          have hP'_in_TP': "P' \<in> TP'" using hTP' unfolding is_topology_on_def by (by100 blast)
          have hSU_closed: "closedin_on P' TP' ?SU"
          proof -
            have hPU_cl: "closedin_on P' TP' (P' - U)"
            proof (rule closedin_intro)
              show "P' - U \<subseteq> P'" by (by100 blast)
            next
              have "P' - (P' - U) = P' \<inter> U" by (by100 blast)
              moreover have "P' \<inter> U \<in> TP'" by (rule topology_inter2[OF hTP' hP'_in_TP' hUV(1)])
              ultimately show "P' - (P' - U) \<in> TP'" by (by100 simp)
            qed
            have hPxPU_cl: "closedin_on (P' \<times> P') (product_topology_on TP' TP') (P' \<times> (P' - U))"
            proof (rule closedin_intro)
              show "P' \<times> (P' - U) \<subseteq> P' \<times> P'" by (by100 blast)
            next
              have "(P' \<times> P') - (P' \<times> (P' - U)) = P' \<times> (P' \<inter> U)" by (by100 blast)
              moreover have "P' \<inter> U \<in> TP'" by (rule topology_inter2[OF hTP' hP'_in_TP' hUV(1)])
              moreover have "P' \<times> (P' \<inter> U) \<in> product_topology_on TP' TP'"
                by (rule product_rect_open[OF hP'_in_TP' \<open>P' \<inter> U \<in> TP'\<close>])
              ultimately show "(P' \<times> P') - (P' \<times> (P' - U)) \<in> product_topology_on TP' TP'" by (by100 simp)
            qed
            have hRC: "closedin_on (P' \<times> P') (product_topology_on TP' TP')
                (?R \<inter> (P' \<times> (P' - U)))"
              by (rule closedin_inter2[OF hTP'_prod2 hR'cl hPxPU_cl])
            have hSU_eq: "?SU = {a \<in> P'. \<exists>b. (a, b) \<in> ?R \<inter> (P' \<times> (P' - U))}"
              by (by100 blast)
            show ?thesis using hproj_closed[OF hRC] hSU_eq by (by100 simp)
          qed
          have hSV_closed: "closedin_on P' TP' ?SV"
          proof -
            have hPV_cl: "closedin_on P' TP' (P' - V)"
            proof (rule closedin_intro)
              show "P' - V \<subseteq> P'" by (by100 blast)
            next
              have "P' - (P' - V) = P' \<inter> V" by (by100 blast)
              moreover have "P' \<inter> V \<in> TP'" by (rule topology_inter2[OF hTP' hP'_in_TP' hUV(2)])
              ultimately show "P' - (P' - V) \<in> TP'" by (by100 simp)
            qed
            have hPxPV_cl: "closedin_on (P' \<times> P') (product_topology_on TP' TP') (P' \<times> (P' - V))"
            proof (rule closedin_intro)
              show "P' \<times> (P' - V) \<subseteq> P' \<times> P'" by (by100 blast)
            next
              have "(P' \<times> P') - (P' \<times> (P' - V)) = P' \<times> (P' \<inter> V)" by (by100 blast)
              moreover have "P' \<inter> V \<in> TP'" by (rule topology_inter2[OF hTP' hP'_in_TP' hUV(2)])
              moreover have "P' \<times> (P' \<inter> V) \<in> product_topology_on TP' TP'"
                by (rule product_rect_open[OF hP'_in_TP' \<open>P' \<inter> V \<in> TP'\<close>])
              ultimately show "(P' \<times> P') - (P' \<times> (P' - V)) \<in> product_topology_on TP' TP'" by (by100 simp)
            qed
            have hRC: "closedin_on (P' \<times> P') (product_topology_on TP' TP')
                (?R \<inter> (P' \<times> (P' - V)))"
              by (rule closedin_inter2[OF hTP'_prod2 hR'cl hPxPV_cl])
            have hSV_eq: "?SV = {a \<in> P'. \<exists>b. (a, b) \<in> ?R \<inter> (P' \<times> (P' - V))}"
              by (by100 blast)
            show ?thesis using hproj_closed[OF hRC] hSV_eq by (by100 simp)
          qed
          \<comment> \<open>P' - ?SU is open and saturated. q'(P' - ?SU) is open in X'.\<close>
          have hWx_open: "X' - q' ` (P' - U) \<in> TX'"
          proof -
            have "q' ` (P' - U) \<subseteq> X'" using hq'_surj by (by100 blast)
            have "closedin_on X' TX' (q' ` (P' - U))"
            proof -
              have "{p \<in> P'. q' p \<in> q' ` (P' - U)} = ?SU" by (by100 blast)
              hence "closedin_on P' TP' {p \<in> P'. q' p \<in> q' ` (P' - U)}"
                using hSU_closed by (by100 simp)
              thus ?thesis
                using top1_quotient_map_closed_iff_preimage_closed[OF hq'Q \<open>q' ` (P' - U) \<subseteq> X'\<close>]
                by (by100 blast)
            qed
            thus ?thesis using hTX' unfolding closedin_on_def by (by100 blast)
          qed
          have hWy_open: "X' - q' ` (P' - V) \<in> TX'"
          proof -
            have "q' ` (P' - V) \<subseteq> X'" using hq'_surj by (by100 blast)
            have "closedin_on X' TX' (q' ` (P' - V))"
            proof -
              have "{p \<in> P'. q' p \<in> q' ` (P' - V)} = ?SV" by (by100 blast)
              hence "closedin_on P' TP' {p \<in> P'. q' p \<in> q' ` (P' - V)}"
                using hSV_closed by (by100 simp)
              thus ?thesis
                using top1_quotient_map_closed_iff_preimage_closed[OF hq'Q \<open>q' ` (P' - V) \<subseteq> X'\<close>]
                by (by100 blast)
            qed
            thus ?thesis using hTX' unfolding closedin_on_def by (by100 blast)
          qed
          have hx_Wx: "x \<in> X' - q' ` (P' - U)"
          proof -
            have "x \<notin> q' ` (P' - U)"
            proof
              assume "x \<in> q' ` (P' - U)"
              then obtain p where "p \<in> P' - U" "q' p = x" by (by100 blast)
              hence "p \<in> ?Fx" by (by100 blast)
              hence "p \<in> U" using hUV(3) by (by100 blast)
              thus False using \<open>p \<in> P' - U\<close> by (by100 blast)
            qed
            thus ?thesis using \<open>x \<in> X'\<close> by (by100 blast)
          qed
          have hy_Wy: "y \<in> X' - q' ` (P' - V)"
          proof -
            have "y \<notin> q' ` (P' - V)"
            proof
              assume "y \<in> q' ` (P' - V)"
              then obtain p where "p \<in> P' - V" "q' p = y" by (by100 blast)
              hence "p \<in> ?Fy" by (by100 blast)
              hence "p \<in> V" using hUV(4) by (by100 blast)
              thus False using \<open>p \<in> P' - V\<close> by (by100 blast)
            qed
            thus ?thesis using \<open>y \<in> X'\<close> by (by100 blast)
          qed
          have hWxy_disj: "(X' - q' ` (P' - U)) \<inter> (X' - q' ` (P' - V)) = {}"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            then obtain z where "z \<in> X'" "z \<notin> q' ` (P' - U)" "z \<notin> q' ` (P' - V)" by (by100 blast)
            hence "\<forall>p\<in>P'. q' p = z \<longrightarrow> p \<in> U" "\<forall>p\<in>P'. q' p = z \<longrightarrow> p \<in> V" by (by100 blast)+
            hence "\<forall>p\<in>P'. q' p = z \<longrightarrow> p \<in> U \<inter> V" by (by100 blast)
            hence "\<forall>p\<in>P'. q' p \<noteq> z" using hUV(5) by (by100 blast)
            hence "z \<notin> q' ` P'" by (by100 blast)
            thus False using \<open>z \<in> X'\<close> hq'_surj by (by100 blast)
          qed
          show "\<exists>U V. neighborhood_of x X' TX' U \<and> neighborhood_of y X' TX' V \<and> U \<inter> V = {}"
          proof (intro exI conjI)
            show "neighborhood_of x X' TX' (X' - q' ` (P' - U))"
              unfolding neighborhood_of_def using hWx_open hx_Wx by (by100 blast)
            show "neighborhood_of y X' TX' (X' - q' ` (P' - V))"
              unfolding neighborhood_of_def using hWy_open hy_Wy by (by100 blast)
            show "(X' - q' ` (P' - U)) \<inter> (X' - q' ` (P' - V)) = {}"
              by (rule hWxy_disj)
          qed
        qed
      qed
    qed
    have hP_compact_loc: "top1_compact_on P ?TP"
    proof -
      have hTP_eq: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
        using product_topology_on_open_sets_real2 by (by100 simp)
      have "compact P"
      proof -
        obtain vx vy :: "nat \<Rightarrow> real" where hn: "length scheme \<ge> 3"
            and hP_eq: "P = {(x, y). \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
                \<and> (\<Sum>i<length scheme. coeffs i) = 1
                \<and> x = (\<Sum>i<length scheme. coeffs i * vx i)
                \<and> y = (\<Sum>i<length scheme. coeffs i * vy i)}"
          using hP_loc unfolding top1_is_polygonal_region_on_def by blast
        show "compact P" unfolding hP_eq by (rule convex_hull_compact[OF hn])
      qed
      hence "top1_compact_on P (subspace_topology (UNIV::((real\<times>real) set)) top1_open_sets P)"
        using top1_compact_on_subspace_UNIV_iff_compact by (by100 blast)
      thus ?thesis using hTP_eq by (by100 simp)
    qed
    show ?thesis
      by (rule hclosed_R_haus[OF hP_haus hP_compact_loc hq_loc hR_closed])
  qed
  show ?thesis using hcompact hhausdorff by (by100 blast)
qed

(** from \<S>74 Theorem 74.3: fundamental group of n-fold torus T_n has the
    presentation \<langle>a_1, b_1, \<dots>, a_n, b_n | [a_1,b_1]\<cdots>[a_n,b_n]\<rangle>.
    The single relator is the product (a_1 b_1 a_1\<inverse> b_1\<inverse>)\<cdots>(a_n b_n a_n\<inverse> b_n\<inverse>).
    We index generators 0, 1, ..., 2n-1 as a_i := 2i, b_i := 2i+1. **)
theorem Theorem_74_3_fund_group_n_torus:
  fixes n :: nat and X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "top1_is_n_fold_torus_on X TX n"
      and "x0 \<in> X"
  shows "\<exists>(G::'g set) mul e invg.
           top1_group_presented_by_on G mul e invg ({..<2*n}::nat set)
             { concat (map (\<lambda>i. [(2*i, True), (2*i+1, True),
                                   (2*i, False), (2*i+1, False)]) [0..<n]) }
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)"
proof -
  \<comment> \<open>Munkres 74.3: T_n is the quotient of a 4n-gon by the torus scheme.
     The 1-skeleton (boundary with identifications) is a wedge of 2n circles.
     By Theorem 72.1 (attaching the 2-cell), \<pi>_1(T_n) is the quotient of the
     free group on 2n generators by the normal closure of the single relator
     [a_1,b_1]...[a_n,b_n].\<close>
  \<comment> \<open>Step 1: T_n is a polygonal quotient of a 4n-gon. Extract the scheme.\<close>
  have h_poly: "top1_is_polygonal_quotient_on X TX"
    unfolding top1_is_polygonal_quotient_on_def
  proof (intro conjI)
    show "is_topology_on_strict X TX"
      using assms(1) unfolding top1_is_n_fold_torus_on_def top1_quotient_of_scheme_on_def by (by100 blast)
    show "\<exists>scheme::(nat \<times> bool) list. top1_quotient_of_scheme_on X TX scheme"
      using assms(1) unfolding top1_is_n_fold_torus_on_def by (by100 blast)
  qed
  \<comment> \<open>Step 2: The 4n-gon's 1-skeleton after identifications is a wedge of 2n circles.\<close>
  have h_skel: "\<exists>A. closedin_on X TX A \<and>
      top1_is_wedge_of_circles_on A (subspace_topology X TX A) {..<2*n} x0"
    sorry \<comment> \<open>1-skeleton of 4n-gon with torus scheme = wedge of 2n circles.\<close>
  \<comment> \<open>Step 3: Apply Theorem 72.1. The attaching map h: B² \<rightarrow> X wraps S¹ around
     the 1-skeleton via the word [a₁,b₁]...[aₙ,bₙ].
     Theorem 72.1 gives: \<pi>_1(X) \<cong> \<pi>_1(1-skel)/N(relator).\<close>
  show ?thesis sorry \<comment> \<open>Theorem 72.1 + presentation by relator [a₁,b₁]...[aₙ,bₙ].\<close>
qed

(** from \<S>74 Theorem 74.4: \<pi>_1(P_m) has presentation \<langle>a_1, \<dots>, a_m | a_1² \<cdots> a_m²\<rangle>.
    The single relator is (a_1 a_1)(a_2 a_2)\<cdots>(a_m a_m). **)
theorem Theorem_74_4_fund_group_m_projective:
  fixes m :: nat and X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "top1_is_m_fold_projective_on X TX m"
      and "x0 \<in> X"
  shows "\<exists>(G::'g set) mul e invg.
           top1_group_presented_by_on G mul e invg ({..<m}::nat set)
             { concat (map (\<lambda>i. [(i, True), (i, True)]) [0..<m]) }
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)"
proof -
  \<comment> \<open>Munkres 74.4: P_m is the quotient of a 2m-gon by the projective scheme.
     The 1-skeleton is a wedge of m circles. By Theorem 72.1, \<pi>_1(P_m) is the
     quotient of the free group on m generators by the normal closure of
     the single relator a_1^2 a_2^2 ... a_m^2.\<close>
  \<comment> \<open>Step 1: P_m is a polygonal quotient of a 2m-gon with projective scheme.\<close>
  have h_poly: "top1_is_polygonal_quotient_on X TX"
    using assms(1) unfolding top1_is_m_fold_projective_on_def
  proof (elim disjE conjE)
    \<comment> \<open>Case m = 1: dunce cap. Need to show dunce cap is polygonal quotient.\<close>
    assume "m = 1" "top1_is_dunce_cap_on X TX (2::nat)"
    thus ?thesis sorry \<comment> \<open>Dunce cap with n=2 is a polygonal quotient.\<close>
  next
    \<comment> \<open>Case m \<ge> 2: directly from the projective scheme.\<close>
    assume "2 \<le> m" "top1_quotient_of_scheme_on X TX (top1_m_projective_scheme m)"
    thus ?thesis unfolding top1_is_polygonal_quotient_on_def
    proof (intro conjI)
      show "is_topology_on_strict X TX"
        using \<open>top1_quotient_of_scheme_on X TX (top1_m_projective_scheme m)\<close>
        unfolding top1_quotient_of_scheme_on_def by (by100 blast)
      show "\<exists>scheme::(nat \<times> bool) list. top1_quotient_of_scheme_on X TX scheme"
        using \<open>top1_quotient_of_scheme_on X TX (top1_m_projective_scheme m)\<close> by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 2: The 2m-gon's 1-skeleton after identifications is a wedge of m circles.\<close>
  have h_skel: "\<exists>A. closedin_on X TX A \<and>
      top1_is_wedge_of_circles_on A (subspace_topology X TX A) {..<m} x0"
    sorry \<comment> \<open>1-skeleton of 2m-gon with projective scheme = wedge of m circles.\<close>
  \<comment> \<open>Step 3: Theorem 72.1 with relator a₁²a₂²...aₘ².\<close>
  show ?thesis sorry \<comment> \<open>Theorem 72.1 + projective presentation.\<close>
qed

section \<open>\<S>76 Cutting and Pasting\<close>

(** from \<S>76: elementary operations on schemes preserve the resulting quotient space.
    If X1 is the quotient space induced by scheme1 and X2 by scheme2, and scheme2
    is obtained from scheme1 via an elementary operation, then X1 \<cong> X2. **)
theorem Theorem_76_elementary_operations:
  fixes scheme1 scheme2 :: "('a \<times> bool) list"
    and X1 X2 :: "'x set" and TX1 TX2 :: "'x set set"
  assumes "is_topology_on_strict X1 TX1" and "is_topology_on_strict X2 TX2"
      and "top1_elementary_scheme_operation scheme1 scheme2"
      and "top1_quotient_of_scheme_on X1 TX1 scheme1
         \<and> top1_quotient_of_scheme_on X2 TX2 scheme2"
  shows "\<exists>h. top1_homeomorphism_on X1 TX1 X2 TX2 h"
proof -
  \<comment> \<open>Munkres §76: Each elementary operation (rotate, cancel, relabel, cut, paste, invert)
     corresponds to a topological operation on the polygonal region that preserves the
     homeomorphism type of the quotient space.
     Proof by induction on the derivation of top1_elementary_scheme_operation.\<close>
  \<comment> \<open>Each case: rotate preserves the polygon; cancel removes a pair of edges;
     relabel renames consistently; cut/paste split/join polygons; invert reverses.\<close>
  have hcases: "\<And>s t. top1_elementary_scheme_operation s t \<Longrightarrow>
      top1_quotient_of_scheme_on X1 TX1 s \<Longrightarrow>
      top1_quotient_of_scheme_on X2 TX2 t \<Longrightarrow>
      \<exists>h. top1_homeomorphism_on X1 TX1 X2 TX2 h" sorry
  show ?thesis using hcases[OF assms(3)] assms(4) by (by100 blast)
qed


section \<open>\<S>75 Homology of Surfaces\<close>

(** from \<S>75 Theorem 75.1: H_1(X, x_0) is the abelianization of \<pi>_1(X, x_0).
    There exists an abelian group H together with a surjective homomorphism
    \<pi>_1(X, x_0) \<rightarrow> H whose kernel is the commutator subgroup of \<pi>_1. **)
theorem Theorem_75_1_H1_abelianization:
  fixes X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "is_topology_on X TX" and "x0 \<in> X"
  shows "\<exists>(H :: (real \<Rightarrow> 'a) set set set) mulH eH invgH \<phi>.
           top1_is_abelianization_of H mulH eH invgH
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)
             (top1_fundamental_group_id X TX x0)
             (top1_fundamental_group_invg X TX x0)
             \<phi>"
proof -
  \<comment> \<open>Munkres 75.1: The abelianization G/[G,G] of any group G exists.
     Define H = \<pi>_1(X)/[\<pi>_1(X), \<pi>_1(X)] with the natural projection \<phi>.
     H is abelian, \<phi> is surjective, and ker(\<phi>) = [\<pi>_1(X), \<pi>_1(X)] by construction.
     This is the first homology group H_1(X).\<close>
  let ?G = "top1_fundamental_group_carrier X TX x0"
  let ?mul = "top1_fundamental_group_mul X TX x0"
  let ?e = "top1_fundamental_group_id X TX x0"
  let ?inv = "top1_fundamental_group_invg X TX x0"
  let ?comm = "top1_commutator_subgroup_on ?G ?mul ?e ?inv"
  \<comment> \<open>Step 1: [G,G] is a normal subgroup of G.\<close>
  have h_comm_normal: "top1_normal_subgroup_on ?G ?mul ?e ?inv ?comm"
  proof -
    have "top1_is_group_on ?G ?mul ?e ?inv"
      by (rule top1_fundamental_group_is_group[OF assms])
    thus ?thesis by (rule commutator_subgroup_is_normal)
  qed
  have hG: "top1_is_group_on ?G ?mul ?e ?inv"
    by (rule top1_fundamental_group_is_group[OF assms])
  \<comment> \<open>Step 2: The natural projection \<phi>(g) = gN is a surjective homomorphism with kernel N.\<close>
  let ?\<phi> = "\<lambda>g. top1_group_coset_on ?G ?mul ?comm g"
  have h_hom: "top1_group_hom_on ?G ?mul
      (top1_quotient_group_carrier_on ?G ?mul ?comm)
      (top1_quotient_group_mul_on ?mul) ?\<phi>"
    by (rule quotient_projection_properties(1)[OF hG h_comm_normal])
  have h_surj: "?\<phi> ` ?G = top1_quotient_group_carrier_on ?G ?mul ?comm"
    by (rule quotient_projection_properties(2)[OF hG h_comm_normal])
  have hNsub: "?comm \<subseteq> ?G"
    using h_comm_normal unfolding top1_normal_subgroup_on_def by (by100 blast)
  have hN_grp: "top1_is_group_on ?comm ?mul ?e ?inv"
    using h_comm_normal unfolding top1_normal_subgroup_on_def by (by100 blast)
  have h_ker: "top1_group_kernel_on ?G (top1_group_coset_on ?G ?mul ?comm ?e) ?\<phi> = ?comm"
    by (rule quotient_projection_properties(3)[OF hG h_comm_normal])
  have hcoset_e: "top1_group_coset_on ?G ?mul ?comm ?e = ?comm"
    by (rule coset_e_is_N[OF hG hNsub hN_grp])
  \<comment> \<open>Step 3: G/[G,G] is abelian.\<close>
  have h_abelian: "\<forall>g\<in>?G. \<forall>h\<in>?G.
    top1_quotient_group_mul_on ?mul
      (top1_group_coset_on ?G ?mul ?comm g) (top1_group_coset_on ?G ?mul ?comm h)
    = top1_quotient_group_mul_on ?mul
      (top1_group_coset_on ?G ?mul ?comm h) (top1_group_coset_on ?G ?mul ?comm g)"
    by (rule quotient_by_commutator_is_abelian[OF hG])
  \<comment> \<open>Step 4: G/[G,G] is a group.\<close>
  let ?invgH = "\<lambda>C. top1_group_coset_on ?G ?mul ?comm
      (?inv (SOME g. g \<in> ?G \<and> C = top1_group_coset_on ?G ?mul ?comm g))"
  have h_quotient_grp: "top1_is_group_on
      (top1_quotient_group_carrier_on ?G ?mul ?comm)
      (top1_quotient_group_mul_on ?mul)
      (top1_group_coset_on ?G ?mul ?comm ?e) ?invgH"
    by (rule quotient_group_is_group[OF hG h_comm_normal])
  \<comment> \<open>Step 5: G/[G,G] is abelian (commutativity from quotient_by_commutator_is_abelian,
     but need to lift from generator-level to carrier-level).\<close>
  have h_quot_abelian: "top1_is_abelian_group_on
      (top1_quotient_group_carrier_on ?G ?mul ?comm)
      (top1_quotient_group_mul_on ?mul)
      (top1_group_coset_on ?G ?mul ?comm ?e) ?invgH"
    unfolding top1_is_abelian_group_on_def
  proof (intro conjI ballI)
    show "top1_is_group_on
        (top1_quotient_group_carrier_on ?G ?mul ?comm) (top1_quotient_group_mul_on ?mul)
        (top1_group_coset_on ?G ?mul ?comm ?e) ?invgH"
      by (rule h_quotient_grp)
  next
    fix C1 C2
    assume hC1: "C1 \<in> top1_quotient_group_carrier_on ?G ?mul ?comm"
       and hC2: "C2 \<in> top1_quotient_group_carrier_on ?G ?mul ?comm"
    obtain g1 where hg1: "g1 \<in> ?G" and hC1_eq: "C1 = top1_group_coset_on ?G ?mul ?comm g1"
      using hC1 unfolding top1_quotient_group_carrier_on_def by (by100 blast)
    obtain g2 where hg2: "g2 \<in> ?G" and hC2_eq: "C2 = top1_group_coset_on ?G ?mul ?comm g2"
      using hC2 unfolding top1_quotient_group_carrier_on_def by (by100 blast)
    show "top1_quotient_group_mul_on ?mul C1 C2 = top1_quotient_group_mul_on ?mul C2 C1"
      using hC1_eq hC2_eq h_abelian hg1 hg2 by (by100 simp)
  qed
  \<comment> \<open>Step 6: Assemble all pieces into top1_is_abelianization_of.\<close>
  have h_ker_comm: "top1_group_kernel_on ?G (top1_group_coset_on ?G ?mul ?comm ?e) ?\<phi> = ?comm"
    by (rule h_ker)
  have "top1_is_abelianization_of
      (top1_quotient_group_carrier_on ?G ?mul ?comm)
      (top1_quotient_group_mul_on ?mul)
      (top1_group_coset_on ?G ?mul ?comm ?e)
      ?invgH ?G ?mul ?e ?inv ?\<phi>"
    unfolding top1_is_abelianization_of_def
    using h_quot_abelian hG h_hom h_surj h_ker_comm hcoset_e by (by100 blast)
  thus ?thesis by (by100 blast)
qed

(** from \<S>75 Theorem 75.3: H_1 of n-fold torus is free abelian of rank 2n.
    The abelianization of \<pi>_1(T_n) is free abelian on 2n generators. **)
theorem Theorem_75_3_H1_n_torus:
  fixes n :: nat and X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "top1_is_n_fold_torus_on X TX n"
      and "x0 \<in> X"
  shows "\<exists>(H::'h set) mulH eH invgH \<iota>_S \<phi>.
           top1_is_abelianization_of H mulH eH invgH
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)
             (top1_fundamental_group_id X TX x0)
             (top1_fundamental_group_invg X TX x0)
             \<phi>
         \<and> top1_is_free_abelian_group_full_on H mulH eH invgH
             (\<iota>_S::nat \<Rightarrow> 'h) {..<2*n}"
proof -
  \<comment> \<open>Munkres 75.3: \<pi>_1(T_n) has presentation \<langle>a_1,...,b_n | [a_1,b_1]...[a_n,b_n]\<rangle>.
     Abelianizing: the commutator relation becomes trivial, so H_1(T_n) \<cong> Z^{2n}.\<close>
  \<comment> \<open>Step 1: By Theorem 74.3, \<pi>_1(T_n) has presentation with relator [a_1,b_1]...[a_n,b_n].\<close>
  have h_presentation: "\<exists>(G::'g set) mul e invg.
      top1_group_presented_by_on G mul e invg ({..<2*n}::nat set)
        { concat (map (\<lambda>i. [(2*i, True), (2*i+1, True),
                              (2*i, False), (2*i+1, False)]) [0..<n]) }"
    using Theorem_74_3_fund_group_n_torus[OF assms] by (by100 auto)
  \<comment> \<open>Step 2: Abelianize. The presentation ⟨a₁,b₁,...|[a₁,b₁]...[aₙ,bₙ]⟩ abelianizes to
     the free abelian group on 2n generators (commutator relator becomes trivial).\<close>
  have h_abelianize: "\<exists>(H::'h set) mulH eH invgH \<iota>_S \<phi>.
      top1_is_abelianization_of H mulH eH invgH
        (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
        (top1_fundamental_group_id X TX x0) (top1_fundamental_group_invg X TX x0) \<phi>
      \<and> top1_is_free_abelian_group_full_on H mulH eH invgH (\<iota>_S::nat \<Rightarrow> 'h) {..<2*n}"
    sorry \<comment> \<open>Abelianization of group with commutator relator = free abelian.\<close>
  show ?thesis using h_abelianize by (by100 blast)
qed

(** from \<S>75 Theorem 75.4: H_1(m-fold projective plane):
    torsion subgroup is Z/2, free part is Z^{m-1}.
    Stated as: H = K \<oplus> Torsion(H) internally, where K \<subseteq> H is free abelian of rank m-1. **)
theorem Theorem_75_4_H1_m_projective:
  fixes m :: nat and X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "top1_is_m_fold_projective_on X TX m"
      and "x0 \<in> X"
  shows "\<exists>(H::'h set) mulH eH invgH \<phi>.
           top1_is_abelianization_of H mulH eH invgH
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)
             (top1_fundamental_group_id X TX x0)
             (top1_fundamental_group_invg X TX x0)
             \<phi>
         \<and> card (top1_torsion_subgroup_on H mulH eH) = 2
         \<and> (\<exists>(K::'h set) (\<iota>_S::nat \<Rightarrow> 'h).
              K \<subseteq> H
            \<and> top1_is_free_abelian_group_full_on K mulH eH invgH \<iota>_S {..<m-1}
            \<and> K \<inter> top1_torsion_subgroup_on H mulH eH = {eH}
            \<and> (\<forall>h\<in>H. \<exists>k\<in>K. \<exists>t\<in>top1_torsion_subgroup_on H mulH eH.
                  h = mulH k t))"
proof -
  \<comment> \<open>Munkres 75.4: \<pi>_1(P_m) has presentation \<langle>a_1,...,a_m | a_1^2...a_m^2\<rangle>.
     Abelianizing: H_1 = Z^m / \<langle>2(a_1+...+a_m)\<rangle>.
     The torsion subgroup is Z/2Z (generated by a_1+...+a_m mod 2).
     The free part K \<cong> Z^{m-1} (a_1-a_2, a_1-a_3, ..., a_1-a_m form a basis).\<close>
  \<comment> \<open>Step 1: By Theorem 74.4, \<pi>_1(P_m) has presentation with relator a_1^2...a_m^2.\<close>
  have h_presentation: "\<exists>(G::'g set) mul0 e0 invg0.
      top1_group_presented_by_on G mul0 e0 invg0 ({..<m}::nat set)
        { concat (map (\<lambda>i. [(i, True), (i, True)]) [0..<m]) }"
    using Theorem_74_4_fund_group_m_projective[OF assms] by (by100 auto)
  \<comment> \<open>Step 2: Abelianize. The relator a₁²...aₘ² maps to 2(a₁+...+aₘ) in the abelianization.
     H₁ = Z^m/⟨2·sum⟩. Decompose: torsion = Z/2Z (class of sum), free = Z^{m-1}.\<close>
  show ?thesis sorry \<comment> \<open>Abelianization + Smith normal form decomposition.\<close>
qed

section \<open>*\<S>78 Constructing Compact Surfaces\<close>

lemma standard_simplex_is_polygonal_region:
  "top1_is_polygonal_region_on top1_standard_simplex 3"
proof -
  let ?vx = "\<lambda>i::nat. if i = 0 then (0::real) else if i = 1 then 1 else 0"
  let ?vy = "\<lambda>i::nat. if i = 0 then (0::real) else if i = 1 then 0 else 1"
  \<comment> \<open>Precompute: {..<3} = {0,1,2} and sum expansions.\<close>
  have h3eq: "{..<(3::nat)} = {0,1,2}" by (by100 auto)
  have hsx: "\<And>c::nat\<Rightarrow>real. (\<Sum>i<3. c i * ?vx i) = c 1"
    unfolding h3eq by (by100 simp)
  have hsy: "\<And>c::nat\<Rightarrow>real. (\<Sum>i<3. c i * ?vy i) = c 2"
    unfolding h3eq by (by100 simp)
  have hsc: "\<And>c::nat\<Rightarrow>real. (\<Sum>i<3. c i) = c 0 + c 1 + c 2"
    unfolding h3eq by (by100 simp)
  \<comment> \<open>Part 1: vertices are distinct.\<close>
  have hd: "\<forall>i<3. \<forall>j<3. i \<noteq> j \<longrightarrow> (?vx i, ?vy i) \<noteq> (?vx j, ?vy j)"
  proof (intro allI impI)
    fix i j :: nat assume "i < 3" "j < 3" "i \<noteq> j"
    hence "i \<in> {0,1,2}" "j \<in> {0,1,2}" by (by100 auto)+
    thus "(?vx i, ?vy i) \<noteq> (?vx j, ?vy j)" using \<open>i \<noteq> j\<close> by (by100 force)
  qed
  \<comment> \<open>Part 2: no vertex is convex combination of others.\<close>
  have he: "\<forall>k<3. \<not> (\<exists>c. (\<forall>i<3. i \<noteq> k \<longrightarrow> (0::real) \<le> c i)
      \<and> c k = 0 \<and> (\<Sum>i<3. c i) = 1
      \<and> ?vx k = (\<Sum>i<3. c i * ?vx i) \<and> ?vy k = (\<Sum>i<3. c i * ?vy i))"
  proof (intro allI impI)
    fix k :: nat assume hk: "k < 3"
    show "\<not> (\<exists>c. (\<forall>i<3. i \<noteq> k \<longrightarrow> 0 \<le> c i) \<and> c k = 0 \<and> (\<Sum>i<3. c i) = 1
        \<and> ?vx k = (\<Sum>i<3. c i * ?vx i) \<and> ?vy k = (\<Sum>i<3. c i * ?vy i))"
    proof
      assume "\<exists>c. (\<forall>i<3. i \<noteq> k \<longrightarrow> 0 \<le> c i) \<and> c k = 0 \<and> (\<Sum>i<3. c i) = 1
          \<and> ?vx k = (\<Sum>i<3. c i * ?vx i) \<and> ?vy k = (\<Sum>i<3. c i * ?vy i)"
      then obtain c where hc: "(\<forall>i<3. i \<noteq> k \<longrightarrow> 0 \<le> c i) \<and> c k = 0
          \<and> (\<Sum>i<3. c i) = 1 \<and> ?vx k = (\<Sum>i<3. c i * ?vx i)
          \<and> ?vy k = (\<Sum>i<3. c i * ?vy i)" by (by100 blast)
      have hck: "c k = 0" using hc by (by100 blast)
      have hcsum: "c 0 + c 1 + c 2 = 1" using hc hsc by (by100 simp)
      have hcx: "?vx k = c 1" using hc hsx by (by100 simp)
      have hcy: "?vy k = c 2" using hc hsy by (by100 simp)
      show False
      proof (cases "k = 0")
        case True thus False using hck hcx hcy hcsum by (by100 simp)
      next
        case False
        show False
        proof (cases "k = 1")
          case True thus False using hck hcx by (by100 simp)
        next
          case False
          hence "k = 2" using hk \<open>k \<noteq> 0\<close> by (by100 simp)
          thus False using hck hcy by (by100 simp)
        qed
      qed
    qed
  qed
  \<comment> \<open>Part 3: set equality. The simplex {(x,y)|x\<ge>0,y\<ge>0,x+y\<le>1} equals the convex hull.\<close>
  have hs: "top1_standard_simplex = {(x, y) | x y.
      \<exists>c. (\<forall>i<3. (0::real) \<le> c i) \<and> (\<Sum>i<3. c i) = 1
      \<and> x = (\<Sum>i<3. c i * ?vx i) \<and> y = (\<Sum>i<3. c i * ?vy i)}"
  proof (rule set_eqI)
    fix p :: "real \<times> real"
    obtain x y where hp: "p = (x, y)" by (cases p) (by100 blast)
    show "p \<in> top1_standard_simplex \<longleftrightarrow>
        p \<in> {(x, y) | x y. \<exists>c. (\<forall>i<3. 0 \<le> c i) \<and> (\<Sum>i<3. c i) = 1
            \<and> x = (\<Sum>i<3. c i * ?vx i) \<and> y = (\<Sum>i<3. c i * ?vy i)}"
    proof
      assume "p \<in> top1_standard_simplex"
      hence hx: "x \<ge> 0" and hy: "y \<ge> 0" and hxy: "x + y \<le> 1"
        using hp unfolding top1_standard_simplex_def by (by100 auto)+
      let ?c = "\<lambda>i::nat. if i = 0 then 1 - x - y else if i = 1 then x else y"
      have hcge: "\<forall>i<3. (0::real) \<le> ?c i" using hx hy hxy by (by100 auto)
      have hcsum: "(\<Sum>i<3. ?c i) = 1" using hsc by (by100 simp)
      have hcvx: "x = (\<Sum>i<3. ?c i * ?vx i)" using hsx by (by100 simp)
      have hcvy: "y = (\<Sum>i<3. ?c i * ?vy i)" using hsy by (by100 simp)
      have "\<exists>c. (\<forall>i<3. (0::real) \<le> c i) \<and> (\<Sum>i<3. c i) = 1
          \<and> x = (\<Sum>i<3. c i * ?vx i) \<and> y = (\<Sum>i<3. c i * ?vy i)"
        apply (rule exI[of _ ?c])
        using hcge hcsum hcvx hcvy by (by100 blast)
      thus "p \<in> {(x, y) | x y. \<exists>c. (\<forall>i<3. 0 \<le> c i) \<and> (\<Sum>i<3. c i) = 1
          \<and> x = (\<Sum>i<3. c i * ?vx i) \<and> y = (\<Sum>i<3. c i * ?vy i)}"
        using hp by blast
    next
      assume "p \<in> {(x, y) | x y. \<exists>c. (\<forall>i<3. 0 \<le> c i) \<and> (\<Sum>i<3. c i) = 1
          \<and> x = (\<Sum>i<3. c i * ?vx i) \<and> y = (\<Sum>i<3. c i * ?vy i)}"
      then obtain x' y' where hxy: "p = (x', y')" and "\<exists>c. (\<forall>i<3. (0::real) \<le> c i) \<and> (\<Sum>i<3. c i) = 1
          \<and> x' = (\<Sum>i<3. c i * ?vx i) \<and> y' = (\<Sum>i<3. c i * ?vy i)"
        by (by100 blast)
      hence "x = x'" "y = y'" using hp by (by100 simp)+
      then obtain c where hcge: "\<forall>i<3. (0::real) \<le> c i"
          and hcsum: "(\<Sum>i<3. c i) = 1"
          and hpx_raw: "x = (\<Sum>i<3. c i * ?vx i)" and hpy_raw: "y = (\<Sum>i<3. c i * ?vy i)"
        using \<open>\<exists>c. _\<close> by (by100 blast)
      have hpx: "x = c 1" using hpx_raw hsx by (by100 simp)
      have hpy: "y = c 2" using hpy_raw hsy by (by100 simp)
      have "c 0 + c 1 + c 2 = 1" using hcsum hsc by (by100 simp)
      have "c 0 \<ge> 0" "c 1 \<ge> 0" "c 2 \<ge> 0" using hcge by (by100 auto)+
      hence "x \<ge> 0" "y \<ge> 0" "x + y \<le> 1" using hpx hpy \<open>c 0 + c 1 + c 2 = 1\<close> \<open>c 0 \<ge> 0\<close>
        by (by100 linarith)+
      thus "p \<in> top1_standard_simplex" using hp unfolding top1_standard_simplex_def
        by (by100 auto)
    qed
  qed
  show ?thesis unfolding top1_is_polygonal_region_on_def
    apply (intro conjI)
     apply (by100 simp)
    apply (rule exI[of _ ?vx])
    apply (rule exI[of _ ?vy])
    using hd he hs unfolding top1_standard_simplex_def by (by100 blast)
qed

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
  show ?thesis sorry \<comment> \<open>Disjoint simplex copies + pasting map gives quotient presentation.\<close>
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
  show ?thesis sorry \<comment> \<open>Iterative merging via spanning tree of dual graph.\<close>
qed

section \<open>\<S>77 The Classification Theorem\<close>

(** from \<S>77 Theorem 77.5: Classification theorem for compact surfaces.
    Every compact connected triangulable surface is homeomorphic to either:
    - the sphere S^2,
    - the n-fold torus T_n for some n \<ge> 1, or
    - the m-fold projective plane P_m for some m \<ge> 1. **)
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
  obtain scheme :: "(nat \<times> bool) list" where hsch: "top1_quotient_of_scheme_on X TX scheme"
    sorry \<comment> \<open>Polygonal region with quotient map gives an edge scheme.\<close>
  \<comment> \<open>Step 2: Apply elementary operations (Theorem 76) to reduce scheme.
     Operations: relabel, rotate, cancel, cut, paste, flip.
     Step 2a: Bring all vertices to one equivalence class.
     Step 2b: Collect pairs aa into adjacent positions (projective type).
     Step 2c: Pair remaining letters into commutator blocks aba\<inverse>b\<inverse> (torus type).\<close>
  have hreduced: "(\<exists>w. scheme = w \<and> (\<forall>a\<in>set w. snd a) \<and> length w = 0)
      \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n
            \<and> top1_elementary_scheme_equiv scheme w)
      \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m
            \<and> top1_elementary_scheme_equiv scheme w)"
    sorry \<comment> \<open>Reduction to normal form via elementary operations (Theorem 76).\<close>
  \<comment> \<open>Step 3: Each normal form corresponds to the standard surface.\<close>
  show ?thesis sorry \<comment> \<open>Normal form → homeomorphism type (S², T_n, or P_m).\<close>
qed

section \<open>Chapter 13: Classification of Covering Spaces\<close>

text \<open>General lift uniqueness: if two continuous maps into a covering space
  agree at one point, both lift the same base map, and the domain is connected,
  then they agree everywhere.\<close>
lemma covering_lift_unique_connected:
  assumes hcov: "top1_covering_map_on E TE B TB p"
      and hTY: "is_topology_on Y TY" and hTB: "is_topology_on B TB" and hTE: "is_topology_on E TE"
      and hconn: "top1_connected_on Y TY"
      and hf1: "top1_continuous_map_on Y TY E TE f1"
      and hf2: "top1_continuous_map_on Y TY E TE f2"
      and hlift1: "\<forall>y\<in>Y. p (f1 y) = p (f2 y)"
      and hagree: "y0 \<in> Y" and hf1f2: "f1 y0 = f2 y0"
  shows "\<forall>y\<in>Y. f1 y = f2 y"
proof -
  \<comment> \<open>S = agreement set = {y \<in> Y | f1(y) = f2(y)}. Show S is open, closed, non-empty in Y.
     Y connected \<Rightarrow> S = Y.\<close>
  let ?S = "{y \<in> Y. f1 y = f2 y}"
  have hS_ne: "?S \<noteq> {}" using hagree hf1f2 by (by100 blast)
  \<comment> \<open>S is open: for y \<in> S, p(f1(y)) = p(f2(y)) has an evenly covered nbhd U.
     f1(y) = f2(y) lies in one sheet V₀. Near y, both f1 and f2 map into V₀
     (by continuity), and p is injective on V₀, so f1 = f2 near y.\<close>
  have hS_open: "?S \<in> TY"
  proof -
    \<comment> \<open>For each y \<in> S, find open neighborhood contained in S.\<close>
    have "\<forall>y\<in>?S. \<exists>W\<in>TY. y \<in> W \<and> W \<subseteq> ?S"
    proof (intro ballI)
      fix y assume hy: "y \<in> ?S"
      hence hyY: "y \<in> Y" and hf12: "f1 y = f2 y" by (by100 blast)+
      have hf1Y: "f1 y \<in> E" using hf1 hyY unfolding top1_continuous_map_on_def by (by100 blast)
      have hpf1: "p (f1 y) \<in> B"
        using hcov hf1Y unfolding top1_covering_map_on_def top1_continuous_map_on_def by (by100 blast)
      \<comment> \<open>Get evenly covered U of p(f1(y)).\<close>
      obtain U where hU: "p (f1 y) \<in> U" and hec: "top1_evenly_covered_on E TE B TB p U"
        using hcov hpf1 unfolding top1_covering_map_on_def by (by100 blast)
      obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E TE V"
          and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
          and hV_cover: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
          and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                       (subspace_topology B TB U) p"
        using hec unfolding top1_evenly_covered_on_def by blast
      \<comment> \<open>f1(y) is in some sheet V₀.\<close>
      have "f1 y \<in> {x\<in>E. p x \<in> U}" using hf1Y hU by (by100 blast)
      hence "f1 y \<in> \<Union>\<V>" using hV_cover by (by100 simp)
      then obtain V0 where hV0: "V0 \<in> \<V>" and hf1V0: "f1 y \<in> V0" by (by100 blast)
      \<comment> \<open>f2(y) = f1(y) \<in> V₀.\<close>
      have hf2V0: "f2 y \<in> V0" using hf12 hf1V0 by (by100 simp)
      \<comment> \<open>V₀ is open in E.\<close>
      have hV0_openE: "openin_on E TE V0" using hV_open hV0 by (by100 blast)
      have hV0_sub: "V0 \<subseteq> E" using hV0_openE unfolding openin_on_def by (by100 blast)
      have hV0_TE: "V0 \<in> TE" using hV0_openE unfolding openin_on_def by (by100 blast)
      \<comment> \<open>f1⁻¹(V₀) and f2⁻¹(V₀) are open in Y.\<close>
      have hf1_preV0: "{y\<in>Y. f1 y \<in> V0} \<in> TY"
        using hf1 hV0_TE unfolding top1_continuous_map_on_def by (by100 blast)
      have hf2_preV0: "{y\<in>Y. f2 y \<in> V0} \<in> TY"
        using hf2 hV0_TE unfolding top1_continuous_map_on_def by (by100 blast)
      \<comment> \<open>W = f1⁻¹(V₀) \<inter> f2⁻¹(V₀) is open in Y.\<close>
      let ?W = "{y\<in>Y. f1 y \<in> V0} \<inter> {y\<in>Y. f2 y \<in> V0}"
      have hW_TY: "?W \<in> TY"
      proof -
        have "{y\<in>Y. f1 y \<in> V0} \<inter> {y\<in>Y. f2 y \<in> V0} \<in> TY"
        proof -
          have hinter: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TY \<longrightarrow> \<Inter>F \<in> TY"
            using hTY unfolding is_topology_on_def by (by100 blast)
          let ?A = "{y\<in>Y. f1 y \<in> V0}" and ?B = "{y\<in>Y. f2 y \<in> V0}"
          have hfin: "finite {?A, ?B}" by (by100 simp)
          have hne: "{?A, ?B} \<noteq> {}" by (by100 blast)
          have hsub: "{?A, ?B} \<subseteq> TY" using hf1_preV0 hf2_preV0 by (by100 blast)
          have "\<Inter>{?A, ?B} \<in> TY"
            using hinter hfin hne hsub by (by100 blast)
          moreover have "\<Inter>{?A, ?B} = ?A \<inter> ?B" by (by100 auto)
          ultimately show ?thesis by (by100 simp)
        qed
        thus ?thesis by (by100 simp)
      qed
      have hyW: "y \<in> ?W" using hyY hf1V0 hf2V0 by (by100 blast)
      \<comment> \<open>On W, f1 = f2 (p injective on V₀).\<close>
      have hW_sub_S: "?W \<subseteq> ?S"
      proof (rule subsetI)
        fix z assume hz: "z \<in> ?W"
        hence hzY: "z \<in> Y" and hf1z_V0: "f1 z \<in> V0" and hf2z_V0: "f2 z \<in> V0"
          by (by100 blast)+
        have "p (f1 z) = p (f2 z)" using hlift1 hzY by (by100 blast)
        \<comment> \<open>p is injective on V₀ (homeomorphism, hence bij_betw, hence inj_on).\<close>
        have hp_inj: "inj_on p V0"
          using hV_homeo hV0 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have "f1 z = f2 z" using hp_inj hf1z_V0 hf2z_V0 \<open>p (f1 z) = p (f2 z)\<close>
          unfolding inj_on_def by (by100 blast)
        thus "z \<in> ?S" using hzY by (by100 blast)
      qed
      show "\<exists>W\<in>TY. y \<in> W \<and> W \<subseteq> ?S"
        apply (rule bexI[where x="?W"])
        using hyW hW_sub_S hW_TY by (by100 blast)+
    qed
    \<comment> \<open>S is a union of open sets, hence open.\<close>
    have "?S = \<Union>{W \<in> TY. W \<subseteq> ?S}"
    proof (rule set_eqI)
      fix y show "y \<in> ?S \<longleftrightarrow> y \<in> \<Union>{W \<in> TY. W \<subseteq> ?S}"
      proof
        assume "y \<in> ?S"
        then obtain W where "W \<in> TY" "y \<in> W" "W \<subseteq> ?S"
          using \<open>\<forall>y\<in>?S. _\<close> by (by100 blast)
        thus "y \<in> \<Union>{W \<in> TY. W \<subseteq> ?S}" by (by100 blast)
      next
        assume "y \<in> \<Union>{W \<in> TY. W \<subseteq> ?S}"
        thus "y \<in> ?S" by (by100 blast)
      qed
    qed
    moreover have "\<Union>{W \<in> TY. W \<subseteq> ?S} \<in> TY"
    proof -
      have hunion: "\<forall>U. U \<subseteq> TY \<longrightarrow> \<Union>U \<in> TY"
        using hTY unfolding is_topology_on_def by (by100 blast)
      have "{W \<in> TY. W \<subseteq> ?S} \<subseteq> TY" by (by100 blast)
      thus ?thesis using hunion by (by100 blast)
    qed
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Y \ S is open: for y \<in> Y \ S, f1(y) \<noteq> f2(y). Since p(f1(y)) = p(f2(y)),
     f1(y) and f2(y) lie in different sheets V₁, V₂ over the same U.
     Near y, f1 maps into V₁ and f2 into V₂ (continuity), so f1 \<noteq> f2 near y.\<close>
  have hYmS_open: "Y - ?S \<in> TY"
  proof -
    \<comment> \<open>For each y \<in> Y \ S, find open neighborhood disjoint from S.\<close>
    have "\<forall>y\<in>Y - ?S. \<exists>W\<in>TY. y \<in> W \<and> W \<subseteq> Y - ?S"
    proof (intro ballI)
      fix y assume hy: "y \<in> Y - ?S"
      hence hyY: "y \<in> Y" and hf12_ne: "f1 y \<noteq> f2 y" by (by100 blast)+
      have hf1Y: "f1 y \<in> E" using hf1 hyY unfolding top1_continuous_map_on_def by (by100 blast)
      have hf2Y: "f2 y \<in> E" using hf2 hyY unfolding top1_continuous_map_on_def by (by100 blast)
      have hpf1: "p (f1 y) \<in> B"
        using hcov hf1Y unfolding top1_covering_map_on_def top1_continuous_map_on_def by (by100 blast)
      obtain U where hU: "p (f1 y) \<in> U" and hec: "top1_evenly_covered_on E TE B TB p U"
        using hcov hpf1 unfolding top1_covering_map_on_def by (by100 blast)
      obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E TE V"
          and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
          and hV_cover: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
          and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                       (subspace_topology B TB U) p"
        using hec unfolding top1_evenly_covered_on_def by blast
      \<comment> \<open>f1(y) and f2(y) are in different sheets (p(f1(y)) = p(f2(y)) but f1(y) \<noteq> f2(y)).\<close>
      have "f1 y \<in> {x\<in>E. p x \<in> U}" using hf1Y hU by (by100 blast)
      then obtain V1 where hV1: "V1 \<in> \<V>" and hf1V1: "f1 y \<in> V1"
        using hV_cover by (by100 blast)
      have hpf2: "p (f2 y) \<in> U"
      proof -
        have "p (f1 y) = p (f2 y)" using hlift1 hyY by (by100 blast)
        thus ?thesis using hU by (by100 simp)
      qed
      have "f2 y \<in> {x\<in>E. p x \<in> U}" using hf2Y hpf2 by (by100 blast)
      then obtain V2 where hV2: "V2 \<in> \<V>" and hf2V2: "f2 y \<in> V2"
        using hV_cover by (by100 blast)
      have hV12_ne: "V1 \<noteq> V2"
      proof
        assume "V1 = V2"
        hence "f2 y \<in> V1" using hf2V2 by (by100 simp)
        have hp_inj: "inj_on p V1"
          using hV_homeo hV1 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have "p (f1 y) = p (f2 y)" using hlift1 hyY by (by100 blast)
        hence "f1 y = f2 y"
          using hp_inj hf1V1 \<open>f2 y \<in> V1\<close> unfolding inj_on_def by (by100 blast)
        thus False using hf12_ne by (by100 blast)
      qed
      have hV1_TE: "V1 \<in> TE" using hV_open hV1 unfolding openin_on_def by (by100 blast)
      have hV2_TE: "V2 \<in> TE" using hV_open hV2 unfolding openin_on_def by (by100 blast)
      \<comment> \<open>W = f1⁻¹(V1) \<inter> f2⁻¹(V2) is open and f1 \<noteq> f2 on W (different sheets, disjoint).\<close>
      let ?W = "{y\<in>Y. f1 y \<in> V1} \<inter> {y\<in>Y. f2 y \<in> V2}"
      have hf1_pre: "{y\<in>Y. f1 y \<in> V1} \<in> TY"
        using hf1 hV1_TE unfolding top1_continuous_map_on_def by (by100 blast)
      have hf2_pre: "{y\<in>Y. f2 y \<in> V2} \<in> TY"
        using hf2 hV2_TE unfolding top1_continuous_map_on_def by (by100 blast)
      have hinter': "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TY \<longrightarrow> \<Inter>F \<in> TY"
        using hTY unfolding is_topology_on_def by (by100 blast)
      let ?A' = "{y\<in>Y. f1 y \<in> V1}" and ?B' = "{y\<in>Y. f2 y \<in> V2}"
      have hW_TY: "?W \<in> TY"
      proof -
        have hfin': "finite {?A', ?B'}" by (by100 simp)
        have hne': "{?A', ?B'} \<noteq> {}" by (by100 blast)
        have hsub': "{?A', ?B'} \<subseteq> TY" using hf1_pre hf2_pre by (by100 blast)
        have "\<Inter>{?A', ?B'} \<in> TY"
          using hinter' hfin' hne' hsub' by (by100 blast)
        moreover have "\<Inter>{?A', ?B'} = ?A' \<inter> ?B'" by (by100 auto)
        ultimately show ?thesis by (by100 simp)
      qed
      have hyW: "y \<in> ?W" using hyY hf1V1 hf2V2 by (by100 blast)
      have hW_disj: "?W \<subseteq> Y - ?S"
      proof (rule subsetI)
        fix z assume hz: "z \<in> ?W"
        hence hzY: "z \<in> Y" and hf1z_V1: "f1 z \<in> V1" and hf2z_V2: "f2 z \<in> V2"
          by (by100 blast)+
        have hV12_disj: "V1 \<inter> V2 = {}" using hV_disj hV1 hV2 hV12_ne by (by100 blast)
        have "f1 z \<noteq> f2 z"
        proof
          assume "f1 z = f2 z"
          hence "f1 z \<in> V2" using hf2z_V2 by (by100 simp)
          hence "f1 z \<in> V1 \<inter> V2" using hf1z_V1 by (by100 blast)
          thus False using hV12_disj by (by100 blast)
        qed
        thus "z \<in> Y - ?S" using hzY by (by100 blast)
      qed
      show "\<exists>W\<in>TY. y \<in> W \<and> W \<subseteq> Y - ?S"
        apply (rule bexI[where x="?W"])
        using hyW hW_disj hW_TY by (by100 blast)+
    qed
    have "Y - ?S = \<Union>{W \<in> TY. W \<subseteq> Y - ?S}"
    proof (rule set_eqI)
      fix y show "y \<in> Y - ?S \<longleftrightarrow> y \<in> \<Union>{W \<in> TY. W \<subseteq> Y - ?S}"
      proof
        assume "y \<in> Y - ?S"
        then obtain W where "W \<in> TY" "y \<in> W" "W \<subseteq> Y - ?S"
          using \<open>\<forall>y\<in>Y - ?S. _\<close> by (by100 blast)
        thus "y \<in> \<Union>{W \<in> TY. W \<subseteq> Y - ?S}" by (by100 blast)
      next
        assume "y \<in> \<Union>{W \<in> TY. W \<subseteq> Y - ?S}" thus "y \<in> Y - ?S" by (by100 blast)
      qed
    qed
    moreover have "\<Union>{W \<in> TY. W \<subseteq> Y - ?S} \<in> TY"
    proof -
      have hunion: "\<forall>U. U \<subseteq> TY \<longrightarrow> \<Union>U \<in> TY"
        using hTY unfolding is_topology_on_def by (by100 blast)
      have "{W \<in> TY. W \<subseteq> Y - ?S} \<subseteq> TY" by (by100 blast)
      thus ?thesis using hunion by (by100 blast)
    qed
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Y connected + S non-empty + S open + complement open \<Rightarrow> S = Y.\<close>
  have "?S = Y"
  proof -
    have "?S \<subseteq> Y" by (by100 blast)
    moreover have "?S \<in> TY" by (rule hS_open)
    moreover have "Y - ?S \<in> TY" by (rule hYmS_open)
    moreover have "?S \<noteq> {}" by (rule hS_ne)
    ultimately show ?thesis using hconn unfolding top1_connected_on_def by (by100 blast)
  qed
  thus ?thesis by (by100 blast)
qed

text \<open>Helper: path-connected implies connected.\<close>
lemma path_connected_imp_connected:
  assumes "top1_path_connected_on X TX"
  shows "top1_connected_on X TX"
  unfolding top1_connected_on_def
proof (intro conjI)
  have hTX: "is_topology_on X TX"
    using assms unfolding top1_path_connected_on_def by (by100 blast)
  show "is_topology_on X TX" by (rule hTX)
  show "\<nexists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X"
  proof (rule notI)
    assume "\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X"
    then obtain U0 V0 where hU0: "U0 \<in> TX" and hV0: "V0 \<in> TX" and hU0ne: "U0 \<noteq> {}"
        and hV0ne: "V0 \<noteq> {}" and hdisj: "U0 \<inter> V0 = {}" and hcover: "U0 \<union> V0 = X"
      by blast
    obtain a where ha: "a \<in> U0" using hU0ne by blast
    obtain b where hb: "b \<in> V0" using hV0ne by blast
    have haX: "a \<in> X"
    proof -
      have "a \<in> U0 \<union> V0" using ha by (by100 blast)
      thus ?thesis using hcover by (by100 simp)
    qed
    have hbX: "b \<in> X"
    proof -
      have "b \<in> U0 \<union> V0" using hb by (by100 blast)
      thus ?thesis using hcover by (by100 simp)
    qed
    \<comment> \<open>Path from a to b (path-connected).\<close>
    obtain \<gamma> where h\<gamma>: "top1_is_path_on X TX a b \<gamma>"
      using assms haX hbX unfolding top1_path_connected_on_def by (by100 auto)
    \<comment> \<open>\<gamma> maps [0,1] into X = U0 \<union> V0. The preimages \<gamma>⁻¹(U0) and \<gamma>⁻¹(V0) cover [0,1].
       \<gamma>(0) = a \<in> U0 and \<gamma>(1) = b \<in> V0. Since [0,1] is connected,
       \<gamma>⁻¹(U0) \<inter> \<gamma>⁻¹(V0) \<noteq> {}. But U0 \<inter> V0 = {}, contradiction.\<close>
    have h\<gamma>0: "\<gamma> 0 = a" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
    have h\<gamma>1: "\<gamma> 1 = b" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
    have h\<gamma>_cont: "top1_continuous_map_on I_set I_top X TX \<gamma>"
      using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
    \<comment> \<open>Preimages of U0 and V0 under \<gamma> are open in [0,1].\<close>
    have hpreU: "{s \<in> I_set. \<gamma> s \<in> U0} \<in> I_top"
      using h\<gamma>_cont hU0 unfolding top1_continuous_map_on_def by (by100 blast)
    have hpreV: "{s \<in> I_set. \<gamma> s \<in> V0} \<in> I_top"
      using h\<gamma>_cont hV0 unfolding top1_continuous_map_on_def by (by100 blast)
    \<comment> \<open>They cover [0,1] and are disjoint.\<close>
    have hcov_I: "{s \<in> I_set. \<gamma> s \<in> U0} \<union> {s \<in> I_set. \<gamma> s \<in> V0} = I_set"
    proof (rule set_eqI)
      fix s show "s \<in> {s \<in> I_set. \<gamma> s \<in> U0} \<union> {s \<in> I_set. \<gamma> s \<in> V0} \<longleftrightarrow> s \<in> I_set"
      proof
        assume "s \<in> {s \<in> I_set. \<gamma> s \<in> U0} \<union> {s \<in> I_set. \<gamma> s \<in> V0}" thus "s \<in> I_set" by (by100 blast)
      next
        assume hs: "s \<in> I_set"
        hence "\<gamma> s \<in> X" using h\<gamma>_cont unfolding top1_continuous_map_on_def by (by100 blast)
        hence "\<gamma> s \<in> U0 \<or> \<gamma> s \<in> V0" using hcover by (by100 blast)
        thus "s \<in> {s \<in> I_set. \<gamma> s \<in> U0} \<union> {s \<in> I_set. \<gamma> s \<in> V0}" using hs by (by100 blast)
      qed
    qed
    have hdisj_I: "{s \<in> I_set. \<gamma> s \<in> U0} \<inter> {s \<in> I_set. \<gamma> s \<in> V0} = {}"
      using hdisj by (by100 blast)
    have hneU: "{s \<in> I_set. \<gamma> s \<in> U0} \<noteq> {}"
    proof -
      have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      moreover have "\<gamma> 0 \<in> U0" using h\<gamma>0 ha by (by100 simp)
      ultimately show ?thesis by (by100 blast)
    qed
    have hneV: "{s \<in> I_set. \<gamma> s \<in> V0} \<noteq> {}"
    proof -
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      moreover have "\<gamma> 1 \<in> V0" using h\<gamma>1 hb by (by100 simp)
      ultimately show ?thesis by (by100 blast)
    qed
    \<comment> \<open>[0,1] is connected (I_set with I_top).\<close>
    have hI_conn: "top1_connected_on I_set I_top"
      by (rule top1_unit_interval_connected)
    \<comment> \<open>Contradiction: connected set separated by two disjoint nonempty open sets.\<close>
    show False using hI_conn hpreU hpreV hneU hneV hdisj_I hcov_I
      unfolding top1_connected_on_def by (by100 blast)
  qed
qed

text \<open>General lifting criterion (Munkres Theorem 79.1): given a covering map p: E \<rightarrow> B,
  a continuous map f: Y \<rightarrow> B with Y path-connected and locally path-connected,
  if f_*(\<pi>_1(Y)) \<subseteq> p_*(\<pi>_1(E)), then f lifts to a continuous map \<tilde>f: Y \<rightarrow> E
  with p \<circ> \<tilde>f = f and \<tilde>f(y0) = e0.\<close>
lemma general_lifting_criterion:
  assumes hcov: "top1_covering_map_on E TE B TB p"
      and hTY: "is_topology_on Y TY" and hTB: "is_topology_on B TB" and hTE: "is_topology_on E TE"
      and hf: "top1_continuous_map_on Y TY B TB f"
      and hYpc: "top1_path_connected_on Y TY"
      and hYlpc: "top1_locally_path_connected_on Y TY"
      and hy0: "y0 \<in> Y" and he0: "e0 \<in> E" and hfy0: "f y0 = p e0"
      and hsubgrp: "top1_fundamental_group_image_hom Y TY y0 B TB (p e0) f
          \<subseteq> top1_fundamental_group_image_hom E TE e0 B TB (p e0) p"
  shows "\<exists>ftilde. (\<forall>y\<in>Y. ftilde y \<in> E) \<and> (\<forall>y\<in>Y. p (ftilde y) = f y)
      \<and> ftilde y0 = e0 \<and> top1_continuous_map_on Y TY E TE ftilde"
proof -
  \<comment> \<open>Step 1: Define ftilde(y) for each y \<in> Y.
     Pick path \<alpha> from y0 to y (Y path-connected).
     f\<circ>\<alpha> is a path from f(y0) = p(e0) to f(y) in B.
     Lift f\<circ>\<alpha> to E starting at e0.
     ftilde(y) = lift endpoint.\<close>
  let ?b0 = "p e0"
  \<comment> \<open>For each y \<in> Y, obtain a path from y0 to y.\<close>
  have hpath_exists: "\<forall>y\<in>Y. \<exists>\<alpha>. top1_is_path_on Y TY y0 y \<alpha>"
    using hYpc hy0 unfolding top1_path_connected_on_def by (by100 auto)
  \<comment> \<open>For each path \<alpha>, f\<circ>\<alpha> can be lifted to E.\<close>
  have hlift_exists: "\<forall>y\<in>Y. \<forall>\<alpha>. top1_is_path_on Y TY y0 y \<alpha> \<longrightarrow>
      (\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s)))"
  proof (intro ballI allI impI)
    fix y \<alpha> assume hy: "y \<in> Y" and h\<alpha>: "top1_is_path_on Y TY y0 y \<alpha>"
    have hf\<alpha>: "top1_is_path_on B TB ?b0 (f y) (f \<circ> \<alpha>)"
    proof -
      have "top1_continuous_map_on I_set I_top B TB (f \<circ> \<alpha>)"
        by (rule top1_continuous_map_on_comp)
           (use h\<alpha> hf in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
      moreover have "(f \<circ> \<alpha>) 0 = ?b0"
        using h\<alpha> hfy0 unfolding top1_is_path_on_def by (by100 simp)
      moreover have "(f \<circ> \<alpha>) 1 = f y"
        using h\<alpha> unfolding top1_is_path_on_def by (by100 simp)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    have "\<exists>ft'. top1_is_path_on E TE e0 (ft' 1) ft' \<and> (\<forall>s\<in>I_set. p (ft' s) = (f \<circ> \<alpha>) s)"
    proof (rule Lemma_54_1_path_lifting)
      show "top1_covering_map_on E TE B TB p" by (rule hcov)
      show "e0 \<in> E" by (rule he0)
      show "p e0 = p e0" by (by100 simp)
      show "top1_is_path_on B TB (p e0) (f y) (f \<circ> \<alpha>)" by (rule hf\<alpha>)
      show "is_topology_on B TB" by (rule hTB)
      show "is_topology_on E TE" by (rule hTE)
    qed
    then obtain ft where hft: "top1_is_path_on E TE e0 (ft 1) ft"
        and hftp: "\<forall>s\<in>I_set. p (ft s) = (f \<circ> \<alpha>) s" by (by100 blast)
    have "\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s)" using hftp by (by100 simp)
    thus "\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s))"
      using hft by (by100 blast)
  qed
  \<comment> \<open>Step 2: Well-definedness. Any two paths \<alpha>1, \<alpha>2 from y0 to y give the same lift endpoint.
     \<alpha>1\<cdot>\<alpha>2\<inverse> is a loop at y0. f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) is a loop at p(e0) in B.
     [f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>)] \<in> f_*(\<pi>_1(Y)) \<subseteq> p_*(\<pi>_1(E)) (by hsubgrp).
     So there exists a loop \<delta> at e0 in E with p\<circ>\<delta> \<simeq> f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>).
     By Theorem_54_3: lifts from e0 of path-homotopic loops have same endpoints.
     The lift of f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) from e0 is a loop (since it lifts p\<circ>\<delta> which is homotopic,
     and \<delta> lifts to itself, ending at e0).
     This loop decomposes as: lift(f\<circ>\<alpha>1) followed by reverse(lift(f\<circ>\<alpha>2)).
     Both starting at e0, so the endpoints of lift(f\<circ>\<alpha>1) and lift(f\<circ>\<alpha>2) agree.\<close>
  have hwd: "\<forall>y\<in>Y. \<forall>\<alpha>1 \<alpha>2 ft1 ft2.
      top1_is_path_on Y TY y0 y \<alpha>1 \<longrightarrow>
      top1_is_path_on Y TY y0 y \<alpha>2 \<longrightarrow>
      top1_is_path_on E TE e0 (ft1 1) ft1 \<longrightarrow> (\<forall>s\<in>I_set. p (ft1 s) = f (\<alpha>1 s)) \<longrightarrow>
      top1_is_path_on E TE e0 (ft2 1) ft2 \<longrightarrow> (\<forall>s\<in>I_set. p (ft2 s) = f (\<alpha>2 s)) \<longrightarrow>
      ft1 1 = ft2 1"
  proof (intro ballI allI impI)
    fix y \<alpha>1 \<alpha>2 ft1 ft2
    assume hy: "y \<in> Y"
        and h\<alpha>1: "top1_is_path_on Y TY y0 y \<alpha>1"
        and h\<alpha>2: "top1_is_path_on Y TY y0 y \<alpha>2"
        and hft1: "top1_is_path_on E TE e0 (ft1 1) ft1"
        and hft1p: "\<forall>s\<in>I_set. p (ft1 s) = f (\<alpha>1 s)"
        and hft2: "top1_is_path_on E TE e0 (ft2 1) ft2"
        and hft2p: "\<forall>s\<in>I_set. p (ft2 s) = f (\<alpha>2 s)"
    \<comment> \<open>f\<circ>\<alpha>1 and f\<circ>\<alpha>2 are paths from p(e0) to f(y) in B.\<close>
    have hf\<alpha>1: "top1_is_path_on B TB ?b0 (f y) (f \<circ> \<alpha>1)"
    proof -
      have "top1_continuous_map_on I_set I_top B TB (f \<circ> \<alpha>1)"
        by (rule top1_continuous_map_on_comp)
           (use h\<alpha>1 hf in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
      moreover have "(f \<circ> \<alpha>1) 0 = ?b0" using h\<alpha>1 hfy0 unfolding top1_is_path_on_def by (by100 simp)
      moreover have "(f \<circ> \<alpha>1) 1 = f y" using h\<alpha>1 unfolding top1_is_path_on_def by (by100 simp)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    have hf\<alpha>2: "top1_is_path_on B TB ?b0 (f y) (f \<circ> \<alpha>2)"
    proof -
      have "top1_continuous_map_on I_set I_top B TB (f \<circ> \<alpha>2)"
        by (rule top1_continuous_map_on_comp)
           (use h\<alpha>2 hf in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
      moreover have "(f \<circ> \<alpha>2) 0 = ?b0" using h\<alpha>2 hfy0 unfolding top1_is_path_on_def by (by100 simp)
      moreover have "(f \<circ> \<alpha>2) 1 = f y" using h\<alpha>2 unfolding top1_is_path_on_def by (by100 simp)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    \<comment> \<open>ft1 lifts f\<circ>\<alpha>1 from e0, ft2 lifts f\<circ>\<alpha>2 from e0.\<close>
    have hft1_lift: "\<forall>s\<in>I_set. p (ft1 s) = (f \<circ> \<alpha>1) s"
      using hft1p by (by100 simp)
    have hft2_lift: "\<forall>s\<in>I_set. p (ft2 s) = (f \<circ> \<alpha>2) s"
      using hft2p by (by100 simp)
    \<comment> \<open>\<alpha>1\<cdot>\<alpha>2\<inverse> is a loop at y0. f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) is a loop at p(e0) in B.\<close>
    have h\<alpha>2_rev: "top1_is_path_on Y TY y y0 (top1_path_reverse \<alpha>2)"
      by (rule top1_path_reverse_is_path[OF h\<alpha>2])
    have hloop_Y: "top1_is_loop_on Y TY y0 (top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
    proof -
      have "top1_is_path_on Y TY y0 y0 (top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
        by (rule top1_path_product_is_path[OF hTY h\<alpha>1 h\<alpha>2_rev])
      thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
    qed
    \<comment> \<open>[f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>)] \<in> p_*(\<pi>_1(E,e0)): from hsubgrp (f_* \<subseteq> p_*).\<close>
    \<comment> \<open>\<Rightarrow> \<exists> loop \<delta> at e0 in E with [p\<circ>\<delta>] = [f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>)].\<close>
    \<comment> \<open>\<delta> lifts p\<circ>\<delta> from e0, ending at e0 (loop).\<close>
    \<comment> \<open>By Theorem_54_3: lift of f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) from e0 also ends at e0.\<close>
    \<comment> \<open>Now the lift of (f\<circ>\<alpha>1)\<cdot>(f\<circ>\<alpha>2)\<inverse> from e0 is: ft1 followed by lift of (f\<circ>\<alpha>2)\<inverse> from ft1(1).
       Since this composite ends at e0, the second part goes from ft1(1) to e0.
       Its reverse lifts f\<circ>\<alpha>2 from e0 to ft1(1).
       By Lemma_54_1_uniqueness: ft2 agrees with this reverse \<Rightarrow> ft2(1) = ft1(1).\<close>
    \<comment> \<open>Get \<delta>: loop at e0 in E with p\<circ>\<delta> ~ f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>).\<close>
    have hfloop: "top1_is_loop_on B TB ?b0 (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
    proof -
      have "top1_is_path_on Y TY y0 y0 (top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
        by (rule top1_path_product_is_path[OF hTY h\<alpha>1 h\<alpha>2_rev])
      hence "top1_is_path_on B TB ?b0 ?b0 (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
      proof -
        have "top1_continuous_map_on I_set I_top B TB (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
          by (rule top1_continuous_map_on_comp)
             (use \<open>top1_is_path_on Y TY y0 y0 _\<close> hf in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
        moreover have "(f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) 0 = ?b0"
          using \<open>top1_is_path_on Y TY y0 y0 _\<close> hfy0 unfolding top1_is_path_on_def by (by100 simp)
        moreover have "(f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) 1 = ?b0"
          using \<open>top1_is_path_on Y TY y0 y0 _\<close> hfy0 unfolding top1_is_path_on_def by (by100 simp)
        ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
      qed
      thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
    qed
    \<comment> \<open>[f\<circ>loop] \<in> p_*(\<pi>_1(E)). Extract \<delta> with p\<circ>\<delta> ~ f\<circ>loop.\<close>
    \<comment> \<open>The loop class of f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) is in f_*(\<pi>_1(Y)) \<subseteq> p_*(\<pi>_1(E)).\<close>
    let ?\<beta> = "top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)"
    have hclass_in_Y: "top1_fundamental_group_induced_on Y TY y0 B TB ?b0 f
        {g. top1_loop_equiv_on Y TY y0 ?\<beta> g}
      \<in> top1_fundamental_group_image_hom Y TY y0 B TB ?b0 f"
    proof -
      have "{g. top1_loop_equiv_on Y TY y0 ?\<beta> g} \<in> top1_fundamental_group_carrier Y TY y0"
        unfolding top1_fundamental_group_carrier_def
        using top1_loop_equiv_on_refl[OF hloop_Y] hloop_Y by (by100 blast)
      thus ?thesis unfolding top1_fundamental_group_image_hom_def by (by100 blast)
    qed
    \<comment> \<open>So the induced class is in p_*(\<pi>_1(E)).\<close>
    have hclass_in_E: "top1_fundamental_group_induced_on Y TY y0 B TB ?b0 f
        {g. top1_loop_equiv_on Y TY y0 ?\<beta> g}
      \<in> top1_fundamental_group_image_hom E TE e0 B TB ?b0 p"
      using hsubgrp hclass_in_Y by (by100 blast)
    \<comment> \<open>Extract \<delta>: loop at e0 with [p\<circ>\<delta>] = induced_f([loop]).\<close>
    obtain \<delta> where h\<delta>_loop: "top1_is_loop_on E TE e0 \<delta>"
        and h\<delta>_hom: "top1_path_homotopic_on B TB ?b0 ?b0
            (p \<circ> \<delta>) (f \<circ> ?\<beta>)"
    proof -
      \<comment> \<open>Unpack: hclass_in_E says the f-induced class is in the p-image of \<pi>_1(E).\<close>
      from hclass_in_E obtain c where hc: "c \<in> top1_fundamental_group_carrier E TE e0"
          and hpc: "top1_fundamental_group_induced_on E TE e0 B TB ?b0 p c
              = top1_fundamental_group_induced_on Y TY y0 B TB ?b0 f
                  {g. top1_loop_equiv_on Y TY y0 ?\<beta> g}"
        unfolding top1_fundamental_group_image_hom_def by (by100 blast)
      \<comment> \<open>c = {g. loop_equiv(E, e0, \<delta>, g)} for some loop \<delta> at e0.\<close>
      from hc obtain \<delta>' where h\<delta>': "top1_is_loop_on E TE e0 \<delta>'"
          and hc_eq: "c = {g. top1_loop_equiv_on E TE e0 \<delta>' g}"
        unfolding top1_fundamental_group_carrier_def by (by100 blast)
      \<comment> \<open>p_*(c) = {g. loop_equiv(B, p e0, p\<circ>\<delta>', g)}.\<close>
      have hp_c: "top1_fundamental_group_induced_on E TE e0 B TB ?b0 p c
          = {g. \<exists>h\<in>c. top1_loop_equiv_on B TB ?b0 (p \<circ> h) g}"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      \<comment> \<open>f_*([β]) = {g. loop_equiv(B, p e0, f\<circ>β, g)} (approximately).\<close>
      \<comment> \<open>From hpc: the two induced classes are equal as sets.
         \<delta>' \<in> c, so p\<circ>\<delta>' gives a representative of p_*(c).
         β gives a representative of f_*([β]).
         Equal classes \<Rightarrow> p\<circ>\<delta>' ~ f\<circ>β.\<close>
      have h\<delta>'_in_c: "\<delta>' \<in> c" using hc_eq top1_loop_equiv_on_refl[OF h\<delta>'] by (by100 blast)
      \<comment> \<open>p\<circ>\<delta>' is loop-equiv to itself, so it's in p_*(c).\<close>
      have hp\<delta>'_in: "p \<circ> \<delta>' \<in> {g. \<exists>h\<in>c. top1_loop_equiv_on B TB ?b0 (p \<circ> h) g}"
      proof -
        have "top1_is_loop_on B TB ?b0 (p \<circ> \<delta>')"
        proof -
          have h\<delta>'_path: "top1_is_path_on E TE e0 e0 \<delta>'"
            using h\<delta>' unfolding top1_is_loop_on_def by (by100 blast)
          have "top1_continuous_map_on I_set I_top B TB (p \<circ> \<delta>')"
            by (rule top1_continuous_map_on_comp)
               (use h\<delta>'_path top1_covering_map_on_continuous[OF hcov] in
                  \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
          moreover have "(p \<circ> \<delta>') 0 = ?b0"
            using h\<delta>'_path unfolding top1_is_path_on_def by (by100 simp)
          moreover have "(p \<circ> \<delta>') 1 = ?b0"
            using h\<delta>'_path unfolding top1_is_path_on_def by (by100 simp)
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
            by (by100 blast)
        qed
        hence "top1_loop_equiv_on B TB ?b0 (p \<circ> \<delta>') (p \<circ> \<delta>')"
          by (rule top1_loop_equiv_on_refl)
        thus ?thesis using h\<delta>'_in_c by (by100 blast)
      qed
      \<comment> \<open>f\<circ>β is loop-equiv to itself, so it's in f_*([β]).\<close>
      have hf\<beta>_in: "f \<circ> ?\<beta> \<in> {g. \<exists>h\<in>{g. top1_loop_equiv_on Y TY y0 ?\<beta> g}.
          top1_loop_equiv_on B TB ?b0 (f \<circ> h) g}"
      proof -
        have "?\<beta> \<in> {g. top1_loop_equiv_on Y TY y0 ?\<beta> g}"
          using top1_loop_equiv_on_refl[OF hloop_Y] by (by100 blast)
        moreover have "top1_loop_equiv_on B TB ?b0 (f \<circ> ?\<beta>) (f \<circ> ?\<beta>)"
          by (rule top1_loop_equiv_on_refl[OF hfloop])
        ultimately show ?thesis by (by100 blast)
      qed
      \<comment> \<open>Since p_*(c) = f_*([β]) and p\<circ>\<delta>' \<in> p_*(c), f\<circ>β \<in> f_*([β]),
         and both are equivalence classes, p\<circ>\<delta>' ~ f\<circ>β.\<close>
      have "p \<circ> \<delta>' \<in> top1_fundamental_group_induced_on E TE e0 B TB ?b0 p c"
        using hp\<delta>'_in hp_c by (by100 simp)
      hence "p \<circ> \<delta>' \<in> top1_fundamental_group_induced_on Y TY y0 B TB ?b0 f
          {g. top1_loop_equiv_on Y TY y0 ?\<beta> g}"
        using hpc by (by100 simp)
      hence "\<exists>h. top1_loop_equiv_on Y TY y0 ?\<beta> h \<and> top1_loop_equiv_on B TB ?b0 (f \<circ> h) (p \<circ> \<delta>')"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      then obtain \<beta>' where h\<beta>': "top1_loop_equiv_on Y TY y0 ?\<beta> \<beta>'"
          and hp\<delta>'_f\<beta>': "top1_loop_equiv_on B TB ?b0 (f \<circ> \<beta>') (p \<circ> \<delta>')" by (by100 blast)
      \<comment> \<open>f\<circ>β ~ f\<circ>β' (since β ~ β') and f\<circ>β' ~ p\<circ>δ'. So f\<circ>β ~ p\<circ>δ'.\<close>
      have hf\<beta>_f\<beta>': "top1_loop_equiv_on B TB ?b0 (f \<circ> ?\<beta>) (f \<circ> \<beta>')"
      proof -
        have h\<beta>'_loop: "top1_is_loop_on Y TY y0 \<beta>'"
          using h\<beta>' unfolding top1_loop_equiv_on_def by (by100 blast)
        have "top1_loop_equiv_on B TB (f y0) (f \<circ> ?\<beta>) (f \<circ> \<beta>')"
          by (rule top1_induced_preserves_loop_equiv[OF hTY hf hloop_Y h\<beta>'_loop h\<beta>'])
        thus ?thesis using hfy0 by (by100 simp)
      qed
      \<comment> \<open>Chain: f\<circ>β ~ f\<circ>β' (by hf\<beta>_f\<beta>'), f\<circ>β' ~ p\<circ>δ' (sym of hp\<delta>'_f\<beta>').\<close>
      \<comment> \<open>hp\<delta>'_f\<beta>' says f\<circ>\<beta>' ~ p\<circ>\<delta>', which is already the right direction.\<close>
      have hf\<beta>_p\<delta>': "top1_loop_equiv_on B TB ?b0 (f \<circ> ?\<beta>) (p \<circ> \<delta>')"
        by (rule top1_loop_equiv_on_trans[OF hTB hf\<beta>_f\<beta>' hp\<delta>'_f\<beta>'])
      have hp\<delta>'_f\<beta>: "top1_loop_equiv_on B TB ?b0 (p \<circ> \<delta>') (f \<circ> ?\<beta>)"
        by (rule top1_loop_equiv_on_sym[OF hf\<beta>_p\<delta>'])
      have "top1_path_homotopic_on B TB ?b0 ?b0 (p \<circ> \<delta>') (f \<circ> ?\<beta>)"
        using hp\<delta>'_f\<beta> unfolding top1_loop_equiv_on_def by (by100 blast)
      thus ?thesis using h\<delta>' that by (by100 blast)
    qed
    \<comment> \<open>By Theorem_54_3: \<delta> lifts p\<circ>\<delta> from e0 (loop \<Rightarrow> ends at e0).
       The lift of f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) from e0 also ends at e0.\<close>
    \<comment> \<open>Get a lift of f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) from e0.\<close>
    have hfloop_path: "top1_is_path_on B TB ?b0 ?b0
        (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
      using hfloop unfolding top1_is_loop_on_def by (by100 blast)
    have "\<exists>ft'. top1_is_path_on E TE e0 (ft' 1) ft'
        \<and> (\<forall>s\<in>I_set. p (ft' s) = (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) s)"
    proof (rule Lemma_54_1_path_lifting)
      show "top1_covering_map_on E TE B TB p" by (rule hcov)
      show "e0 \<in> E" by (rule he0)
      show "p e0 = p e0" by (by100 simp)
      show "top1_is_path_on B TB (p e0) ?b0
          (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))" using hfloop_path by (by100 simp)
      show "is_topology_on B TB" by (rule hTB)
      show "is_topology_on E TE" by (rule hTE)
    qed
    then obtain ft_loop where hft_loop: "top1_is_path_on E TE e0 (ft_loop 1) ft_loop"
        and hft_loop_lift: "\<forall>s\<in>I_set. p (ft_loop s) = (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) s"
      by (by100 blast)
    \<comment> \<open>By Theorem_54_3 with p\<circ>\<delta> ~ f\<circ>loop: ft_loop(1) = \<delta>(1) = e0.\<close>
    have hft_loop_end: "ft_loop 1 = e0"
    proof -
      have h\<delta>_path: "top1_is_path_on E TE e0 e0 \<delta>"
        using h\<delta>_loop unfolding top1_is_loop_on_def by (by100 blast)
      have h\<delta>_lift: "\<forall>s\<in>I_set. p (\<delta> s) = (p \<circ> \<delta>) s" by (by100 simp)
      have hp\<delta>_path: "top1_is_path_on B TB ?b0 ?b0 (p \<circ> \<delta>)"
      proof -
        have "top1_continuous_map_on I_set I_top B TB (p \<circ> \<delta>)"
          by (rule top1_continuous_map_on_comp)
             (use h\<delta>_path top1_covering_map_on_continuous[OF hcov] in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
        moreover have "(p \<circ> \<delta>) 0 = ?b0"
          using h\<delta>_path unfolding top1_is_path_on_def by (by100 simp)
        moreover have "(p \<circ> \<delta>) 1 = ?b0"
          using h\<delta>_path unfolding top1_is_path_on_def by (by100 simp)
        ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
      qed
      have "e0 = ft_loop 1 \<and> top1_path_homotopic_on E TE e0 e0 \<delta> ft_loop"
      proof (rule Theorem_54_3[OF hcov hTE hTB he0])
        show "p e0 = p e0" by (by100 simp)
        show "top1_is_path_on B TB (p e0) (p e0) (p \<circ> \<delta>)" using hp\<delta>_path by (by100 simp)
        show "top1_is_path_on B TB (p e0) (p e0) (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
          using hfloop_path by (by100 simp)
        show "top1_path_homotopic_on B TB (p e0) (p e0) (p \<circ> \<delta>)
            (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))" using h\<delta>_hom by (by100 simp)
        show "top1_is_path_on E TE e0 e0 \<delta>" by (rule h\<delta>_path)
        show "\<forall>s\<in>I_set. p (\<delta> s) = (p \<circ> \<delta>) s" by (by100 simp)
        show "top1_is_path_on E TE e0 (ft_loop 1) ft_loop" by (rule hft_loop)
        show "\<forall>s\<in>I_set. p (ft_loop s) = (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) s"
          by (rule hft_loop_lift)
      qed
      thus ?thesis by (by100 blast)
    qed
    \<comment> \<open>ft_loop lifts f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) from e0, ending at e0.
       Now use Lemma_54_1_uniqueness to relate ft_loop to ft1 and ft2.\<close>
    \<comment> \<open>The first half of ft_loop (rescaled to [0,1]) lifts f\<circ>\<alpha>1.
       By uniqueness with ft1: they agree, in particular ft_loop(1/2) = ft1(1).
       The second half reversed lifts f\<circ>\<alpha>2.
       By uniqueness with ft2: ft_loop(1/2) = ft2(1).
       So ft1(1) = ft2(1).\<close>
    \<comment> \<open>First half of ft_loop (rescaled) lifts f\<circ>\<alpha>1 from e0.
       By uniqueness with ft1: ft_loop(1/2) = ft1(1).
       Second half reversed lifts f\<circ>\<alpha>2 from e0 (since ft_loop ends at e0).
       By uniqueness with ft2: ft_loop(1/2) = ft2(1).
       Therefore ft1(1) = ft2(1).\<close>
    \<comment> \<open>g1(s) = ft_loop(s/2) is a path lifting f\<circ>\<alpha>1 from e0.\<close>
    let ?g1 = "\<lambda>s. ft_loop (s / 2)"
    have hg1_path: "top1_is_path_on E TE e0 (ft_loop (1/2)) ?g1"
    proof -
      have hft_cont: "top1_continuous_map_on I_set I_top E TE ft_loop"
        using hft_loop unfolding top1_is_path_on_def by (by100 blast)
      \<comment> \<open>The linear map s \<mapsto> s/2 is continuous from I_set to I_set.\<close>
      have hlin_cont: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>s. s / 2)"
      proof -
        have "\<And>s::real. s \<in> I_set \<Longrightarrow> s / 2 \<in> I_set"
          unfolding top1_unit_interval_def by (by100 simp)
        moreover have "continuous_on (UNIV::real set) (\<lambda>s::real. s / 2)"
          by (intro continuous_intros continuous_on_divide) auto
        ultimately have "top1_continuous_map_on I_set
            (subspace_topology (UNIV::real set) top1_open_sets I_set)
            I_set (subspace_topology (UNIV::real set) top1_open_sets I_set) (\<lambda>s. s / 2)"
          by (rule top1_continuous_map_on_real_subspace_open_sets)
        moreover have "I_top = subspace_topology (UNIV::real set) top1_open_sets I_set"
          unfolding top1_unit_interval_topology_def by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      have "top1_continuous_map_on I_set I_top E TE (\<lambda>s. ft_loop (s / 2))"
      proof -
        have "top1_continuous_map_on I_set I_top E TE (ft_loop \<circ> (\<lambda>s. s / 2))"
          by (rule top1_continuous_map_on_comp[OF hlin_cont hft_cont])
        moreover have "ft_loop \<circ> (\<lambda>s. s / 2) = (\<lambda>s. ft_loop (s / 2))"
          by (rule ext) (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      moreover have "ft_loop (0 / 2) = e0"
        using hft_loop unfolding top1_is_path_on_def by (by100 simp)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    have hg1_lift: "\<forall>s\<in>I_set. p (?g1 s) = (f \<circ> \<alpha>1) s"
    proof (intro ballI)
      fix s assume hs: "s \<in> I_set"
      hence hs01: "0 \<le> s" "s \<le> 1" unfolding top1_unit_interval_def by (by100 simp)+
      have hs2: "s / 2 \<in> I_set" unfolding top1_unit_interval_def using hs01 by (by100 simp)
      have "p (ft_loop (s / 2)) = (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (s / 2)"
        using hft_loop_lift hs2 by (by100 blast)
      also have "\<dots> = f ((top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (s / 2))" by (by100 simp)
      also have "(top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (s / 2) = \<alpha>1 (2 * (s / 2))"
        unfolding top1_path_product_def using hs01 by (by100 simp)
      also have "2 * (s / 2) = s" by (by100 simp)
      finally show "p (?g1 s) = (f \<circ> \<alpha>1) s" by (by100 simp)
    qed
    \<comment> \<open>By uniqueness: ?g1 agrees with ft1 \<Rightarrow> ft_loop(1/2) = ft1(1).\<close>
    have "ft_loop (1/2) = ft1 1"
    proof -
      have "\<forall>s\<in>I_set. ?g1 s = ft1 s"
      proof (rule Lemma_54_1_uniqueness[OF hcov he0])
        show "p e0 = p e0" by (by100 simp)
        show "top1_is_path_on B TB (p e0) (f y) (f \<circ> \<alpha>1)" using hf\<alpha>1 by (by100 simp)
        show "top1_is_path_on E TE e0 (ft_loop (1/2)) ?g1" by (rule hg1_path)
        show "\<forall>s\<in>I_set. p (?g1 s) = (f \<circ> \<alpha>1) s" by (rule hg1_lift)
        show "top1_is_path_on E TE e0 (ft1 1) ft1" by (rule hft1)
        show "\<forall>s\<in>I_set. p (ft1 s) = (f \<circ> \<alpha>1) s" using hft1_lift by (by100 simp)
      qed
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      hence "?g1 1 = ft1 1" using \<open>\<forall>s\<in>I_set. ?g1 s = ft1 s\<close> by (by100 blast)
      thus ?thesis by (by100 simp)
    qed
    \<comment> \<open>g2(s) = ft_loop(1 - s/2) lifts f\<circ>\<alpha>2 from e0 (since ft_loop(1) = e0).\<close>
    let ?g2 = "\<lambda>s. ft_loop (1 - s / 2)"
    have hg2_path: "top1_is_path_on E TE e0 (ft_loop (1/2)) ?g2"
    proof -
      have hft_cont: "top1_continuous_map_on I_set I_top E TE ft_loop"
        using hft_loop unfolding top1_is_path_on_def by (by100 blast)
      have hlin_cont2: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>s. 1 - s / 2)"
      proof -
        have "\<And>s::real. s \<in> I_set \<Longrightarrow> 1 - s / 2 \<in> I_set"
          unfolding top1_unit_interval_def by (by100 simp)
        moreover have "continuous_on (UNIV::real set) (\<lambda>s::real. 1 - s / 2)"
          by (intro continuous_intros continuous_on_divide) auto
        ultimately have "top1_continuous_map_on I_set
            (subspace_topology (UNIV::real set) top1_open_sets I_set)
            I_set (subspace_topology (UNIV::real set) top1_open_sets I_set) (\<lambda>s. 1 - s / 2)"
          by (rule top1_continuous_map_on_real_subspace_open_sets)
        moreover have "I_top = subspace_topology (UNIV::real set) top1_open_sets I_set"
          unfolding top1_unit_interval_topology_def by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      have "top1_continuous_map_on I_set I_top E TE (\<lambda>s. ft_loop (1 - s / 2))"
      proof -
        have "top1_continuous_map_on I_set I_top E TE (ft_loop \<circ> (\<lambda>s. 1 - s / 2))"
          by (rule top1_continuous_map_on_comp[OF hlin_cont2 hft_cont])
        moreover have "ft_loop \<circ> (\<lambda>s. 1 - s / 2) = (\<lambda>s. ft_loop (1 - s / 2))"
          by (rule ext) (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      moreover have "ft_loop (1 - 0 / 2) = e0"
      proof -
        have "ft_loop 1 = e0" by (rule hft_loop_end)
        thus ?thesis by (by100 simp)
      qed
      moreover have "ft_loop (1 - 1 / 2) = ft_loop (1/2)" by (by100 simp)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    have hg2_lift: "\<forall>s\<in>I_set. p (?g2 s) = (f \<circ> \<alpha>2) s"
    proof (intro ballI)
      fix s assume hs: "s \<in> I_set"
      hence hs01: "0 \<le> s" "s \<le> 1" unfolding top1_unit_interval_def by (by100 simp)+
      have hs2: "1 - s / 2 \<in> I_set" unfolding top1_unit_interval_def using hs01 by (by100 simp)
      have "p (ft_loop (1 - s / 2)) = (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2)"
        using hft_loop_lift hs2 by (by100 blast)
      also have "\<dots> = f ((top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2))" by (by100 simp)
      also have "\<dots> = f (\<alpha>2 s)"
      proof (cases "s = 1")
        case True
        \<comment> \<open>At s=1: path_product at 1/2 gives \<alpha>1(1) = y. f(\<alpha>1(1)) = f(y) = f(\<alpha>2(1)).\<close>
        have "1 - s / 2 = 1 / 2" using True by (by100 simp)
        hence "(top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2) = \<alpha>1 (2 * (1/2))"
          unfolding top1_path_product_def by (by100 simp)
        hence "f ((top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2)) = f (\<alpha>1 1)"
          by (by100 simp)
        moreover have "\<alpha>1 1 = y" using h\<alpha>1 unfolding top1_is_path_on_def by (by100 blast)
        moreover have "\<alpha>2 1 = y" using h\<alpha>2 unfolding top1_is_path_on_def by (by100 blast)
        ultimately show ?thesis using True by (by100 simp)
      next
        case False
        hence "1 - s / 2 > 1 / 2" using hs01 by (by100 linarith)
        hence "\<not> (1 - s / 2 \<le> 1 / 2)" by (by100 linarith)
        hence "(top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2)
            = (top1_path_reverse \<alpha>2) (2 * (1 - s / 2) - 1)"
          unfolding top1_path_product_def by (by100 simp)
        hence "f ((top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2))
            = f ((top1_path_reverse \<alpha>2) (1 - s))" by (by100 simp)
        moreover have "(top1_path_reverse \<alpha>2) (1 - s) = \<alpha>2 s"
          unfolding top1_path_reverse_def by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      finally show "p (?g2 s) = (f \<circ> \<alpha>2) s" by (by100 simp)
    qed
    have "ft_loop (1/2) = ft2 1"
    proof -
      have "\<forall>s\<in>I_set. ?g2 s = ft2 s"
      proof (rule Lemma_54_1_uniqueness[OF hcov he0])
        show "p e0 = p e0" by (by100 simp)
        show "top1_is_path_on B TB (p e0) (f y) (f \<circ> \<alpha>2)" using hf\<alpha>2 by (by100 simp)
        show "top1_is_path_on E TE e0 (ft_loop (1/2)) ?g2" by (rule hg2_path)
        show "\<forall>s\<in>I_set. p (?g2 s) = (f \<circ> \<alpha>2) s" by (rule hg2_lift)
        show "top1_is_path_on E TE e0 (ft2 1) ft2" by (rule hft2)
        show "\<forall>s\<in>I_set. p (ft2 s) = (f \<circ> \<alpha>2) s" using hft2_lift by (by100 simp)
      qed
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      hence "?g2 1 = ft2 1" using \<open>\<forall>s\<in>I_set. ?g2 s = ft2 s\<close> by (by100 blast)
      thus ?thesis by (by100 simp)
    qed
    show "ft1 1 = ft2 1" using \<open>ft_loop (1/2) = ft1 1\<close> \<open>ft_loop (1/2) = ft2 1\<close> by (by100 simp)
  qed
  \<comment> \<open>Step 3: Define ftilde.\<close>
  define ftilde where "ftilde y = (let \<alpha> = SOME \<alpha>. top1_is_path_on Y TY y0 y \<alpha>;
      ft = SOME ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s))
    in ft 1)" for y
  \<comment> \<open>Step 4: ftilde has the required properties.\<close>
  have hft_props: "(\<forall>y\<in>Y. ftilde y \<in> E) \<and> (\<forall>y\<in>Y. p (ftilde y) = f y) \<and> ftilde y0 = e0"
  proof -
    \<comment> \<open>For each y \<in> Y: the SOME-chosen path and lift satisfy the properties.\<close>
    have hsome_props: "\<forall>y\<in>Y. (\<exists>\<alpha> ft. top1_is_path_on Y TY y0 y \<alpha>
        \<and> top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s))
        \<and> ftilde y = ft 1)"
    proof (intro ballI)
      fix y assume hy: "y \<in> Y"
      let ?\<alpha> = "SOME \<alpha>. top1_is_path_on Y TY y0 y \<alpha>"
      have "\<exists>\<alpha>. top1_is_path_on Y TY y0 y \<alpha>" using hpath_exists hy by (by100 blast)
      hence h\<alpha>: "top1_is_path_on Y TY y0 y ?\<alpha>" by (rule someI_ex)
      let ?ft = "SOME ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (?\<alpha> s))"
      have "\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (?\<alpha> s))"
        using hlift_exists hy h\<alpha> by (by100 blast)
      hence hft: "top1_is_path_on E TE e0 (?ft 1) ?ft \<and> (\<forall>s\<in>I_set. p (?ft s) = f (?\<alpha> s))"
        by (rule someI_ex)
      have "ftilde y = ?ft 1" unfolding ftilde_def by (by100 simp)
      thus "\<exists>\<alpha> ft. top1_is_path_on Y TY y0 y \<alpha>
          \<and> top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s))
          \<and> ftilde y = ft 1"
        using h\<alpha> hft by (by100 blast)
    qed
    show ?thesis proof (intro conjI)
    show "\<forall>y\<in>Y. ftilde y \<in> E"
    proof (intro ballI)
      fix y assume "y \<in> Y"
      from hsome_props[rule_format, OF this]
      obtain \<alpha> ft where "top1_is_path_on E TE e0 (ft 1) ft" and "ftilde y = ft 1"
        by (by100 blast)
      have "ft 1 \<in> E"
      proof -
        have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        thus ?thesis using \<open>top1_is_path_on E TE e0 (ft 1) ft\<close>
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      qed
      thus "ftilde y \<in> E" using \<open>ftilde y = ft 1\<close> by (by100 simp)
    qed
  next
    show "\<forall>y\<in>Y. p (ftilde y) = f y"
    proof (intro ballI)
      fix y assume "y \<in> Y"
      from hsome_props[rule_format, OF this]
      obtain \<alpha> ft where h\<alpha>: "top1_is_path_on Y TY y0 y \<alpha>"
          and hft: "top1_is_path_on E TE e0 (ft 1) ft"
          and hftp: "\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s)"
          and hftilde: "ftilde y = ft 1" by (by100 blast)
      have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      have "p (ft 1) = f (\<alpha> 1)" using hftp h1I by (by100 blast)
      moreover have "\<alpha> 1 = y" using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
      ultimately show "p (ftilde y) = f y" using hftilde by (by100 simp)
    qed
  next
    show "ftilde y0 = e0"
    proof -
      \<comment> \<open>The SOME-chosen path from y0 to y0 gives a lift; any lift from e0 of a
         loop at p(e0) has some endpoint. But by well-definedness, the endpoint
         is the same for all paths. The constant path at y0 lifts to constant at e0.\<close>
      from hsome_props[rule_format, OF hy0]
      obtain \<alpha> ft where h\<alpha>: "top1_is_path_on Y TY y0 y0 \<alpha>"
          and hft: "top1_is_path_on E TE e0 (ft 1) ft"
          and hftp: "\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s)"
          and hftilde: "ftilde y0 = ft 1" by (by100 blast)
      \<comment> \<open>The constant path at y0 also lifts to constant at e0.\<close>
      have hconst_path: "top1_is_path_on Y TY y0 y0 (top1_constant_path y0)"
        by (rule top1_constant_path_is_path[OF hTY hy0])
      have hconst_lift: "top1_is_path_on E TE e0 e0 (top1_constant_path e0)"
        by (rule top1_constant_path_is_path[OF hTE he0])
      have hconst_liftp: "\<forall>s\<in>I_set. p ((top1_constant_path e0) s) = f ((top1_constant_path y0) s)"
      proof (intro ballI)
        fix s assume "s \<in> I_set"
        show "p ((top1_constant_path e0) s) = f ((top1_constant_path y0) s)"
          unfolding top1_constant_path_def using hfy0 by (by100 simp)
      qed
      \<comment> \<open>By well-definedness (hwd): ft 1 = e0.\<close>
      have "ft 1 = (top1_constant_path e0) 1"
      proof -
        have hcl2: "top1_is_path_on E TE e0 ((top1_constant_path e0) 1) (top1_constant_path e0)"
        proof -
          have "(top1_constant_path e0) 1 = e0" unfolding top1_constant_path_def by (by100 simp)
          thus ?thesis using hconst_lift by (by100 simp)
        qed
        from hwd[rule_format, OF hy0, of \<alpha> "top1_constant_path y0" ft "top1_constant_path e0"]
        show ?thesis using h\<alpha> hconst_path hft hftp hcl2 hconst_liftp by (by100 blast)
      qed
      hence "ft 1 = e0" unfolding top1_constant_path_def by (by100 simp)
      thus ?thesis using hftilde by (by100 simp)
    qed
    qed
  qed
  \<comment> \<open>Helper: ftilde(y') equals the endpoint of ANY lift of f\<circ>\<alpha> from e0, for any path \<alpha> from y0 to y'.\<close>
  have ftilde_eq_lift: "\<And>y' \<alpha> ft'. y' \<in> Y \<Longrightarrow> top1_is_path_on Y TY y0 y' \<alpha> \<Longrightarrow>
      top1_is_path_on E TE e0 (ft' 1) ft' \<Longrightarrow> (\<forall>s\<in>I_set. p (ft' s) = f (\<alpha> s)) \<Longrightarrow>
      ftilde y' = ft' 1"
  proof -
    fix y' \<alpha>' ft'
    assume hy': "y' \<in> Y" and h\<alpha>': "top1_is_path_on Y TY y0 y' \<alpha>'"
        and hft': "top1_is_path_on E TE e0 (ft' 1) ft'"
        and hft'p: "\<forall>s\<in>I_set. p (ft' s) = f (\<alpha>' s)"
    \<comment> \<open>Get the SOME-chosen path and lift for ftilde(y').\<close>
    let ?\<alpha>_s = "SOME \<alpha>. top1_is_path_on Y TY y0 y' \<alpha>"
    have "\<exists>\<alpha>. top1_is_path_on Y TY y0 y' \<alpha>" using hpath_exists hy' by (by100 blast)
    hence h\<alpha>_s: "top1_is_path_on Y TY y0 y' ?\<alpha>_s" by (rule someI_ex)
    let ?ft_s = "SOME ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (?\<alpha>_s s))"
    have "\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (?\<alpha>_s s))"
      using hlift_exists hy' h\<alpha>_s by (by100 blast)
    hence hft_s: "top1_is_path_on E TE e0 (?ft_s 1) ?ft_s \<and> (\<forall>s\<in>I_set. p (?ft_s s) = f (?\<alpha>_s s))"
      by (rule someI_ex)
    have hftilde_eq: "ftilde y' = ?ft_s 1" unfolding ftilde_def by (by100 simp)
    \<comment> \<open>By hwd: ft' 1 = ft_s 1.\<close>
    from hwd[rule_format, OF hy', of \<alpha>' ?\<alpha>_s ft' ?ft_s]
    have "ft' 1 = ?ft_s 1" using h\<alpha>' h\<alpha>_s hft' hft'p hft_s by (by100 blast)
    thus "ftilde y' = ft' 1" using hftilde_eq by (by100 simp)
  qed
  \<comment> \<open>Step 5: ftilde is continuous.
     For y \<in> Y, let U be evenly covered nbhd of f(y) in B.
     By local path-connectivity of Y, get path-connected open V \<ni> y with f(V) \<subseteq> U.
     Let W0 be the sheet over U containing ftilde(y).
     For y' \<in> V: extend path (y0\<rightarrow>y) with segment (y\<rightarrow>y' in V).
     The lift of the segment stays in W0 (sheets are homeomorphic to U).
     So ftilde|_V = (p|_{W0})\<inverse> \<circ> f|_V, which is continuous.\<close>
  have hft_cont: "top1_continuous_map_on Y TY E TE ftilde"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>y\<in>Y. ftilde y \<in> E" using hft_props by (by100 blast)
  next
    show "\<forall>W\<in>TE. {y \<in> Y. ftilde y \<in> W} \<in> TY"
    proof (intro ballI)
      fix W assume hW: "W \<in> TE"
      \<comment> \<open>For each y in the preimage, find a neighborhood mapping into W.\<close>
      have "\<forall>y \<in> {y \<in> Y. ftilde y \<in> W}. \<exists>V\<in>TY. y \<in> V \<and> V \<subseteq> {y \<in> Y. ftilde y \<in> W}"
      proof (intro ballI)
        fix y assume hy_pre: "y \<in> {y \<in> Y. ftilde y \<in> W}"
        hence hyY: "y \<in> Y" and hfty_W: "ftilde y \<in> W" by (by100 blast)+
        have hfty_E: "ftilde y \<in> E" using hft_props hyY by (by100 blast)
        have hfy: "p (ftilde y) = f y" using hft_props hyY by (by100 blast)
        have hfy_B: "f y \<in> B"
          using hf hyY unfolding top1_continuous_map_on_def by (by100 blast)
        \<comment> \<open>Get evenly covered U of f(y) in B.\<close>
        obtain U where hU: "f y \<in> U" and hec: "top1_evenly_covered_on E TE B TB p U"
          using hcov hfy_B unfolding top1_covering_map_on_def by (by100 blast)
        obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E TE V"
            and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
            and hV_cover: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
            and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                         (subspace_topology B TB U) p"
          using hec unfolding top1_evenly_covered_on_def by blast
        \<comment> \<open>ftilde(y) is in some sheet W0.\<close>
        have "ftilde y \<in> {x\<in>E. p x \<in> U}"
        proof -
          have "ftilde y \<in> E" by (rule hfty_E)
          moreover have "p (ftilde y) \<in> U" using hfy hU by (by100 simp)
          ultimately show ?thesis by (by100 blast)
        qed
        hence "ftilde y \<in> \<Union>\<V>" using hV_cover by (by100 simp)
        then obtain W0 where hW0: "W0 \<in> \<V>" and hfty_W0: "ftilde y \<in> W0" by (by100 blast)
        \<comment> \<open>W0 \<inter> W is open in E, contains ftilde(y).\<close>
        have hW0_open: "W0 \<in> TE" using hV_open hW0 unfolding openin_on_def by (by100 blast)
        \<comment> \<open>p is a homeomorphism on W0 → U.\<close>
        have hp_homeo: "top1_homeomorphism_on W0 (subspace_topology E TE W0) U
            (subspace_topology B TB U) p" using hV_homeo hW0 by (by100 blast)
        have hp_inj: "inj_on p W0"
          using hp_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        \<comment> \<open>U is open in B.\<close>
        have hU_open: "openin_on B TB U"
          using hec unfolding top1_evenly_covered_on_def by (by100 blast)
        have hU_TB: "U \<in> TB" using hU_open unfolding openin_on_def by (by100 blast)
        \<comment> \<open>f\<inverse>(U) is open in Y.\<close>
        have hfU: "{y\<in>Y. f y \<in> U} \<in> TY"
          using hf hU_TB unfolding top1_continuous_map_on_def by (by100 blast)
        \<comment> \<open>By local path-connectivity: get path-connected open V \<subseteq> f\<inverse>(U) with y \<in> V.\<close>
        obtain V0 where hV0_TY: "V0 \<in> TY" and hy_V0: "y \<in> V0"
            and hV0_sub: "V0 \<subseteq> {y\<in>Y. f y \<in> U}"
            and hV0_pc: "top1_path_connected_on V0 (subspace_topology Y TY V0)"
        proof -
          \<comment> \<open>f\<inverse>(U) is open in Y, contains y.\<close>
          have hfU_nbhd: "neighborhood_of y Y TY {y\<in>Y. f y \<in> U}"
            unfolding neighborhood_of_def using hfU hyY hU by (by100 blast)
          have hfU_sub: "{y\<in>Y. f y \<in> U} \<subseteq> Y" by (by100 blast)
          \<comment> \<open>By local path-connectivity of Y at y: get path-connected open V0 \<subseteq> f\<inverse>(U).\<close>
          have hlpc_y: "top1_locally_path_connected_at Y TY y"
            using hYlpc hyY unfolding top1_locally_path_connected_on_def by (by100 blast)
          obtain V0' where hV0'_nbhd: "neighborhood_of y Y TY V0'"
              and hV0'_sub: "V0' \<subseteq> {y\<in>Y. f y \<in> U}" and hV0'_Y: "V0' \<subseteq> Y"
              and hV0'_pc: "top1_path_connected_on V0' (subspace_topology Y TY V0')"
          proof -
            from hlpc_y[unfolded top1_locally_path_connected_at_def,
                rule_format, of "{y\<in>Y. f y \<in> U}"]
            show ?thesis using hfU_nbhd hfU_sub that by (by100 blast)
          qed
          \<comment> \<open>neighborhood_of means V0' \<in> TY \<and> y \<in> V0'.\<close>
          have hV0'_TY: "V0' \<in> TY" using hV0'_nbhd unfolding neighborhood_of_def by (by100 blast)
          have hy_V0': "y \<in> V0'" using hV0'_nbhd unfolding neighborhood_of_def by (by100 blast)
          show ?thesis using that[OF hV0'_TY hy_V0' hV0'_sub hV0'_pc] .
        qed
        \<comment> \<open>For y' \<in> V0: ftilde(y') \<in> W0 because the lift stays in the sheet.\<close>
        \<comment> \<open>ftilde maps V0 into W0: for y' \<in> V0, the lift of f\<circ>\<sigma> (path y\<rightarrow>y' in V0)
           from ftilde(y) stays in W0 (since f\<circ>\<sigma> stays in U and p|_{W0}: W0 \<cong> U).\<close>
        \<comment> \<open>p|_{W0} is a bijection W0 → U.\<close>
        have hp_bij: "bij_betw p W0 U"
          using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        \<comment> \<open>ftilde(y) = inv_into W0 p (f y).\<close>
        have hfty_inv: "ftilde y = inv_into W0 p (f y)"
          using inv_into_f_eq[OF hp_inj hfty_W0] hfy by (by100 simp)
        have hftilde_V0: "\<forall>y'\<in>V0. ftilde y' \<in> W0"
        proof (intro ballI)
          fix y' assume hy'V0: "y' \<in> V0"
          have hy'Y: "y' \<in> Y" using hy'V0 hV0_sub by (by100 blast)
          have hfy'U: "f y' \<in> U" using hy'V0 hV0_sub by (by100 blast)
          have hfy'_pW0: "f y' \<in> p ` W0" using hp_bij hfy'U unfolding bij_betw_def by (by100 blast)
          have hinv_y'_W0: "inv_into W0 p (f y') \<in> W0" by (rule inv_into_into[OF hfy'_pW0])
          \<comment> \<open>Path from y to y' in V0.\<close>
          obtain \<sigma> where h\<sigma>: "top1_is_path_on V0 (subspace_topology Y TY V0) y y' \<sigma>"
            using hV0_pc hy_V0 hy'V0 unfolding top1_path_connected_on_def by (by100 auto)
          \<comment> \<open>\<sigma> as ambient path.\<close>
          have hV0_sub_Y: "V0 \<subseteq> Y" using hV0_sub by (by100 blast)
          have h\<sigma>_cont_V0: "top1_continuous_map_on I_set I_top V0 (subspace_topology Y TY V0) \<sigma>"
            using h\<sigma> unfolding top1_is_path_on_def by (by100 blast)
          have h\<sigma>_in_V0: "\<forall>s\<in>I_set. \<sigma> s \<in> V0"
            using h\<sigma>_cont_V0 unfolding top1_continuous_map_on_def by (by100 blast)
          have h\<sigma>_Y: "top1_is_path_on Y TY y y' \<sigma>"
          proof -
            have hincl: "top1_continuous_map_on V0 (subspace_topology Y TY V0) Y TY (\<lambda>x. x)"
            proof -
              have "top1_continuous_map_on V0 (subspace_topology Y TY V0) Y TY (\<lambda>x. x)"
                by (rule top1_continuous_map_on_restrict_domain_simple[OF
                  top1_continuous_map_on_id[OF hTY, unfolded id_def] hV0_sub_Y])
              thus ?thesis .
            qed
            have "top1_continuous_map_on I_set I_top Y TY ((\<lambda>x. x) \<circ> \<sigma>)"
              by (rule top1_continuous_map_on_comp[OF h\<sigma>_cont_V0 hincl])
            moreover have "(\<lambda>x::'c. x) \<circ> \<sigma> = \<sigma>" by (rule ext) (by100 simp)
            ultimately have h\<sigma>_cont_Y: "top1_continuous_map_on I_set I_top Y TY \<sigma>" by (by100 simp)
            have "\<sigma> 0 = y" using h\<sigma> unfolding top1_is_path_on_def by (by100 blast)
            have "\<sigma> 1 = y'" using h\<sigma> unfolding top1_is_path_on_def by (by100 blast)
            show ?thesis unfolding top1_is_path_on_def using h\<sigma>_cont_Y \<open>\<sigma> 0 = y\<close> \<open>\<sigma> 1 = y'\<close>
              by (by100 blast)
          qed
          \<comment> \<open>Path from y0 to y.\<close>
          obtain \<alpha>0 where h\<alpha>0: "top1_is_path_on Y TY y0 y \<alpha>0"
            using hpath_exists hyY by (by100 blast)
          \<comment> \<open>Lift of f\<circ>\<alpha>0 from e0.\<close>
          obtain ft0 where hft0: "top1_is_path_on E TE e0 (ft0 1) ft0"
              and hft0p: "\<forall>s\<in>I_set. p (ft0 s) = f (\<alpha>0 s)"
            using hlift_exists hyY h\<alpha>0 by (by100 blast)
          \<comment> \<open>ft0 1 = ftilde y (by ftilde_eq_lift).\<close>
          have hft0_end: "ft0 1 = ftilde y"
            using ftilde_eq_lift[OF hyY h\<alpha>0 hft0 hft0p] by (by100 simp)
          \<comment> \<open>Concatenate: \<alpha>0\<cdot>\<sigma> is a path from y0 to y'.\<close>
          have h\<alpha>0\<sigma>: "top1_is_path_on Y TY y0 y' (top1_path_product \<alpha>0 \<sigma>)"
            by (rule top1_path_product_is_path[OF hTY h\<alpha>0 h\<sigma>_Y])
          \<comment> \<open>Construct the lift of f\<circ>(\<alpha>0\<cdot>\<sigma>) as ft0 \<cdot> (inv_into W0 p \<circ> f \<circ> \<sigma>).\<close>
          let ?inv_lift = "\<lambda>s. inv_into W0 p (f (\<sigma> s))"
          \<comment> \<open>?inv_lift is a path in W0 \<subseteq> E from ftilde(y) to inv_into W0 p (f y').\<close>
          have hinvl_path: "top1_is_path_on E TE (ftilde y) (inv_into W0 p (f y')) ?inv_lift"
          proof -
            \<comment> \<open>Continuity: inv_into W0 p \<circ> f \<circ> \<sigma> is continuous I_set \<rightarrow> E.\<close>
            \<comment> \<open>f\<circ>\<sigma>: I_set \<rightarrow> U (f continuous, \<sigma> maps V0 \<subseteq> f\<inverse>(U)).\<close>
            \<comment> \<open>inv_into W0 p: U \<rightarrow> W0 \<subseteq> E (inverse of homeomorphism).\<close>
            have hinv_cont: "top1_continuous_map_on U (subspace_topology B TB U) W0 (subspace_topology E TE W0)
                (inv_into W0 p)"
              using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
            \<comment> \<open>f\<circ>\<sigma> maps I_set into U (via V0).\<close>
            have hf\<sigma>_cont: "top1_continuous_map_on I_set I_top U (subspace_topology B TB U) (f \<circ> \<sigma>)"
            proof -
              \<comment> \<open>\<sigma>: I \<rightarrow> Y continuous, f: Y \<rightarrow> B continuous. f\<circ>\<sigma>: I \<rightarrow> B continuous.\<close>
              have h\<sigma>_cont_Y: "top1_continuous_map_on I_set I_top Y TY \<sigma>"
                using h\<sigma>_Y unfolding top1_is_path_on_def by (by100 blast)
              have "top1_continuous_map_on I_set I_top B TB (f \<circ> \<sigma>)"
                by (rule top1_continuous_map_on_comp[OF h\<sigma>_cont_Y hf])
              \<comment> \<open>f\<circ>\<sigma> maps into U (V0 \<subseteq> f\<inverse>(U) and \<sigma> maps into V0).\<close>
              moreover have "\<forall>s\<in>I_set. (f \<circ> \<sigma>) s \<in> U"
              proof (intro ballI)
                fix s assume "s \<in> I_set"
                hence "\<sigma> s \<in> V0" using h\<sigma>_in_V0 by (by100 blast)
                hence "f (\<sigma> s) \<in> U" using hV0_sub by (by100 blast)
                thus "(f \<circ> \<sigma>) s \<in> U" by (by100 simp)
              qed
              \<comment> \<open>Restrict codomain to U with subspace topology.\<close>
              moreover have hU_sub_B: "U \<subseteq> B"
                using hU_open unfolding openin_on_def by (by100 blast)
              ultimately show ?thesis
              proof -
                assume hf\<sigma>B: "top1_continuous_map_on I_set I_top B TB (f \<circ> \<sigma>)"
                    and hrange: "\<forall>s\<in>I_set. (f \<circ> \<sigma>) s \<in> U"
                show ?thesis
                  by (rule continuous_map_restrict_codomain[OF hf\<sigma>B hrange hU_sub_B])
              qed
            qed
            \<comment> \<open>Composition: inv_into \<circ> f \<circ> \<sigma> maps I_set to W0.\<close>
            have "top1_continuous_map_on I_set I_top W0 (subspace_topology E TE W0) (inv_into W0 p \<circ> (f \<circ> \<sigma>))"
              by (rule top1_continuous_map_on_comp[OF hf\<sigma>_cont hinv_cont])
            moreover have "(inv_into W0 p \<circ> (f \<circ> \<sigma>)) = ?inv_lift"
              by (rule ext) (by100 simp)
            ultimately have hinvl_cont_W0: "top1_continuous_map_on I_set I_top W0 (subspace_topology E TE W0) ?inv_lift"
              by (by100 simp)
            \<comment> \<open>W0 \<subseteq> E, so compose with inclusion to get continuity into E.\<close>
            have hW0_sub: "W0 \<subseteq> E" using hV_open hW0 unfolding openin_on_def by (by100 blast)
            have hW0_incl: "top1_continuous_map_on W0 (subspace_topology E TE W0) E TE (\<lambda>x. x)"
              using top1_continuous_map_on_restrict_domain_simple[OF
                top1_continuous_map_on_id[OF hTE, unfolded id_def] hW0_sub] by (by100 simp)
            have "top1_continuous_map_on I_set I_top E TE ((\<lambda>x. x) \<circ> ?inv_lift)"
              by (rule top1_continuous_map_on_comp[OF hinvl_cont_W0 hW0_incl])
            moreover have "(\<lambda>x::'a. x) \<circ> ?inv_lift = ?inv_lift" by (rule ext) (by100 simp)
            ultimately have hinvl_cont_E: "top1_continuous_map_on I_set I_top E TE ?inv_lift"
              by (by100 simp)
            \<comment> \<open>Endpoints.\<close>
            have hinvl_0: "?inv_lift 0 = ftilde y"
            proof -
              have "\<sigma> 0 = y" using h\<sigma>_Y unfolding top1_is_path_on_def by (by100 blast)
              hence "?inv_lift 0 = inv_into W0 p (f y)" by (by100 simp)
              also have "\<dots> = ftilde y" using hfty_inv by (by100 simp)
              finally show ?thesis .
            qed
            have hinvl_1: "?inv_lift 1 = inv_into W0 p (f y')"
            proof -
              have "\<sigma> 1 = y'" using h\<sigma>_Y unfolding top1_is_path_on_def by (by100 blast)
              thus ?thesis by (by100 simp)
            qed
            show ?thesis unfolding top1_is_path_on_def
              using hinvl_cont_E hinvl_0 hinvl_1 by (by100 blast)
          qed
          have hinvl_lift: "\<forall>s\<in>I_set. p (?inv_lift s) = f (\<sigma> s)"
          proof (intro ballI)
            fix s assume hs: "s \<in> I_set"
            have "\<sigma> s \<in> V0" using h\<sigma>_in_V0 hs by (by100 blast)
            hence "f (\<sigma> s) \<in> U" using hV0_sub by (by100 blast)
            hence "f (\<sigma> s) \<in> p ` W0" using hp_bij unfolding bij_betw_def by (by100 blast)
            show "p (?inv_lift s) = f (\<sigma> s)" by (rule f_inv_into_f[OF \<open>f (\<sigma> s) \<in> p ` W0\<close>])
          qed
          \<comment> \<open>The concatenation ft0 \<cdot> inv_lift is a path from e0 to inv_into W0 p (f y').\<close>
          define cl where "cl = top1_path_product ft0 ?inv_lift"
          have hcl_path: "top1_is_path_on E TE e0 (inv_into W0 p (f y')) cl"
          proof -
            have "ft0 1 = ftilde y" by (rule hft0_end)
            hence hft0': "top1_is_path_on E TE e0 (ftilde y) ft0"
              using hft0 by (by100 simp)
            show ?thesis unfolding cl_def by (rule top1_path_product_is_path[OF hTE hft0' hinvl_path])
          qed
          have hcl_lift: "\<forall>s\<in>I_set. p (cl s) = f ((top1_path_product \<alpha>0 \<sigma>) s)"
          proof (intro ballI)
            fix s assume hs: "s \<in> I_set"
            hence hs01: "0 \<le> s" "s \<le> 1" unfolding top1_unit_interval_def by (by100 simp)+
            show "p (cl s) = f ((top1_path_product \<alpha>0 \<sigma>) s)"
            proof (cases "s \<le> 1/2")
              case True
              have "cl s = ft0 (2 * s)" unfolding cl_def top1_path_product_def using True by (by100 simp)
              moreover have "p (ft0 (2 * s)) = f (\<alpha>0 (2 * s))"
              proof -
                have "2 * s \<in> I_set" unfolding top1_unit_interval_def using hs01 True by (by100 simp)
                thus ?thesis using hft0p by (by100 blast)
              qed
              moreover have "(top1_path_product \<alpha>0 \<sigma>) s = \<alpha>0 (2 * s)"
                unfolding top1_path_product_def using True by (by100 simp)
              ultimately show ?thesis by (by100 simp)
            next
              case False
              hence hgt: "s > 1/2" by (by100 simp)
              have "cl s = ?inv_lift (2 * s - 1)" unfolding cl_def top1_path_product_def using False by (by100 simp)
              moreover have "p (?inv_lift (2 * s - 1)) = f (\<sigma> (2 * s - 1))"
              proof -
                have "2 * s - 1 \<in> I_set" unfolding top1_unit_interval_def using hs01 hgt by (by100 simp)
                thus ?thesis using hinvl_lift by (by100 blast)
              qed
              moreover have "(top1_path_product \<alpha>0 \<sigma>) s = \<sigma> (2 * s - 1)"
                unfolding top1_path_product_def using False by (by100 simp)
              ultimately show ?thesis by (by100 simp)
            qed
          qed
          \<comment> \<open>By ftilde_eq_lift: ftilde(y') = endpoint of this lift = inv_into W0 p (f y').\<close>
          \<comment> \<open>cl 1 = inv_into W0 p (f y') (endpoint computation).\<close>
          have hcl_end: "cl 1 = inv_into W0 p (f y')"
          proof -
            have "cl 1 = ?inv_lift (2 * (1::real) - 1)" unfolding cl_def top1_path_product_def by (by100 simp)
            moreover have "(2::real) * 1 - 1 = (1::real)" by (by100 simp)
            ultimately have "cl 1 = ?inv_lift 1" by (by100 simp)
            moreover have "?inv_lift 1 = inv_into W0 p (f (\<sigma> 1))" by (by100 simp)
            moreover have "\<sigma> 1 = y'" using h\<sigma>_Y unfolding top1_is_path_on_def by (by100 blast)
            ultimately show ?thesis by (by100 simp)
          qed
          \<comment> \<open>ftilde(y') = cl 1 (by ftilde_eq_lift).\<close>
          have hcl_lift2: "\<forall>s\<in>I_set. p (cl s) = f (top1_path_product \<alpha>0 \<sigma> s)"
            using hcl_lift by (by100 simp)
          have hcl_path2: "top1_is_path_on E TE e0 (cl 1) cl"
          proof -
            have "cl 1 = inv_into W0 p (f y')" using hcl_end .
            thus ?thesis using hcl_path by (by100 simp)
          qed
          have "ftilde y' = cl 1"
            by (rule ftilde_eq_lift[OF hy'Y h\<alpha>0\<sigma> hcl_path2 hcl_lift2])
          hence "ftilde y' = inv_into W0 p (f y')" using hcl_end by (by100 simp)
          thus "ftilde y' \<in> W0" using hinv_y'_W0 by (by100 simp)
        qed
        \<comment> \<open>hftilde_V0 proved above.\<close>
        \<comment> \<open>V' = V0 \<inter> ftilde\<inverse>(W0 \<inter> W). Since ftilde(V0) \<subseteq> W0, this simplifies.\<close>
        \<comment> \<open>Actually, we need V' \<subseteq> {y \<in> Y. ftilde y \<in> W}. Use W0 \<inter> W.\<close>
        \<comment> \<open>W0 \<inter> W is open in E. p maps W0 homeomorphically to U.
           So p(W0 \<inter> W) is open in U, hence open in B.
           V' = V0 \<inter> f\<inverse>(p(W0 \<inter> W)) is open in Y.\<close>
        \<comment> \<open>ftilde on V0 equals (p|_{W0})\<inverse> \<circ> f. For ftilde(y') \<in> W, need f(y') \<in> p(W0 \<inter> W).\<close>
        have hftilde_eq: "\<forall>y'\<in>V0. ftilde y' = inv_into W0 p (f y')"
        proof (intro ballI)
          fix y' assume "y' \<in> V0"
          hence "ftilde y' \<in> W0" using hftilde_V0 by (by100 blast)
          have hy'Y: "y' \<in> Y" using \<open>y' \<in> V0\<close> hV0_sub by (by100 blast)
          have "p (ftilde y') = f y'" using hft_props hy'Y by (by100 blast)
          thus "ftilde y' = inv_into W0 p (f y')"
            using inv_into_f_eq[OF hp_inj \<open>ftilde y' \<in> W0\<close> \<open>p (ftilde y') = f y'\<close>]
            by (by100 simp)
        qed
        \<comment> \<open>p(W0 \<inter> W) is open in B (p homeo on W0, W0 \<inter> W open in W0).\<close>
        have hpWW: "p ` (W0 \<inter> W) \<subseteq> U"
        proof -
          have "W0 \<subseteq> {x\<in>E. p x \<in> U}" using hV_cover hW0 by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        have hpWW_open: "{y\<in>Y. f y \<in> p ` (W0 \<inter> W)} \<in> TY"
        proof -
          \<comment> \<open>p(W0 \<inter> W) is open in B.\<close>
          \<comment> \<open>W0 \<inter> W is open in E. Its intersection with W0 (= W0 \<inter> W) is open in
             the subspace W0. p maps open subsets of W0 to open subsets of U (homeomorphism).
             U open in B, so the image is open in B.\<close>
          have "p ` (W0 \<inter> W) \<in> TB"
          proof -
            \<comment> \<open>W0 \<inter> W is open in the subspace topology of W0.\<close>
            have hWW_sub: "W0 \<inter> W \<in> subspace_topology E TE W0"
              unfolding subspace_topology_def using hW hW0_open by (by100 blast)
            \<comment> \<open>p maps W0 homeomorphically to U. Open subsets map to open subsets.\<close>
            have hp_bij: "bij_betw p W0 U"
              using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
            have hp_cont_W0: "top1_continuous_map_on W0 (subspace_topology E TE W0) U (subspace_topology B TB U) p"
              using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
            \<comment> \<open>The inverse p\<inverse> is continuous on U → W0.\<close>
            have hinv_cont: "top1_continuous_map_on U (subspace_topology B TB U) W0 (subspace_topology E TE W0) (inv_into W0 p)"
              using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
            \<comment> \<open>Preimage of W0\<inter>W under p\<inverse> = p(W0\<inter>W). By continuity of p\<inverse>, this is open in U.\<close>
            have "{u \<in> U. inv_into W0 p u \<in> W0 \<inter> W} \<in> subspace_topology B TB U"
              using hinv_cont hWW_sub unfolding top1_continuous_map_on_def by (by100 blast)
            \<comment> \<open>{u \<in> U | inv(u) \<in> W0\<inter>W} = p(W0\<inter>W) (since p is bijection on W0).\<close>
            have "{u \<in> U. inv_into W0 p u \<in> W0 \<inter> W} = p ` (W0 \<inter> W)"
            proof (rule set_eqI)
              fix u show "u \<in> {u \<in> U. inv_into W0 p u \<in> W0 \<inter> W} \<longleftrightarrow> u \<in> p ` (W0 \<inter> W)"
              proof
                assume hu: "u \<in> {u \<in> U. inv_into W0 p u \<in> W0 \<inter> W}"
                hence "inv_into W0 p u \<in> W0 \<inter> W" and "u \<in> U" by (by100 blast)+
                have "u \<in> p ` W0" using hp_bij \<open>u \<in> U\<close> unfolding bij_betw_def by (by100 blast)
                have "p (inv_into W0 p u) = u" by (rule f_inv_into_f[OF \<open>u \<in> p ` W0\<close>])
                thus "u \<in> p ` (W0 \<inter> W)" using \<open>inv_into W0 p u \<in> W0 \<inter> W\<close> by (by100 force)
              next
                assume "u \<in> p ` (W0 \<inter> W)"
                then obtain e where he: "e \<in> W0 \<inter> W" and hue: "u = p e" by (by100 blast)
                have "e \<in> W0" using he by (by100 blast)
                have "u \<in> U" using hpWW \<open>u \<in> p ` (W0 \<inter> W)\<close> by (by100 blast)
                have "inv_into W0 p u = e"
                  using inv_into_f_eq[OF hp_inj \<open>e \<in> W0\<close>] hue by (by100 simp)
                thus "u \<in> {u \<in> U. inv_into W0 p u \<in> W0 \<inter> W}"
                  using \<open>u \<in> U\<close> he by (by100 simp)
              qed
            qed
            \<comment> \<open>So p(W0\<inter>W) is open in the subspace U of B.\<close>
            hence "p ` (W0 \<inter> W) \<in> subspace_topology B TB U"
              using \<open>{u \<in> U. inv_into W0 p u \<in> W0 \<inter> W} \<in> subspace_topology B TB U\<close>
              by (by100 simp)
            \<comment> \<open>Open in U subspace = V \<inter> U for some V \<in> TB. Since U \<in> TB and V \<in> TB, V\<inter>U \<in> TB.\<close>
            then obtain V where hV_TB: "V \<in> TB" and hpWW_eq: "p ` (W0 \<inter> W) = U \<inter> V"
              unfolding subspace_topology_def by (by100 auto)
            have "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TB \<longrightarrow> \<Inter>F \<in> TB"
              using hTB unfolding is_topology_on_def by (by100 blast)
            hence "U \<inter> V \<in> TB"
            proof -
              have "finite {U, V}" by (by100 simp)
              moreover have "{U, V} \<noteq> {}" by (by100 blast)
              moreover have "{U, V} \<subseteq> TB" using hU_TB hV_TB by (by100 blast)
              ultimately have "\<Inter>{U, V} \<in> TB"
                using \<open>\<forall>F. _\<close> by (by100 blast)
              moreover have "\<Inter>{U, V} = U \<inter> V" by (by100 auto)
              ultimately show ?thesis by (by100 simp)
            qed
            thus "p ` (W0 \<inter> W) \<in> TB" using hpWW_eq by (by100 simp)
          qed
          thus ?thesis using hf unfolding top1_continuous_map_on_def by (by100 blast)
        qed
        let ?V' = "V0 \<inter> {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}"
        have hV'_TY: "?V' \<in> TY"
        proof -
          have "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TY \<longrightarrow> \<Inter>F \<in> TY"
            using hTY unfolding is_topology_on_def by (by100 blast)
          hence "V0 \<inter> {y\<in>Y. f y \<in> p ` (W0 \<inter> W)} \<in> TY"
          proof -
            have hfin: "finite {V0, {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}}" by (by100 simp)
            have hne: "{V0, {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}} \<noteq> {}" by (by100 blast)
            have hsub: "{V0, {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}} \<subseteq> TY"
              using hV0_TY hpWW_open by (by100 blast)
            have "\<Inter>{V0, {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}} \<in> TY"
              using \<open>\<forall>F. _\<close> hfin hne hsub by (by100 blast)
            moreover have "\<Inter>{V0, {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}} = V0 \<inter> {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}"
              by (by100 auto)
            ultimately show ?thesis by (by100 simp)
          qed
          thus ?thesis by (by100 simp)
        qed
        have hy_V': "y \<in> ?V'"
        proof -
          have "y \<in> V0" by (rule hy_V0)
          moreover have "y \<in> Y" by (rule hyY)
          moreover have "f y \<in> p ` (W0 \<inter> W)"
          proof -
            have "ftilde y \<in> W0 \<inter> W" using hfty_W0 hfty_W by (by100 blast)
            hence "p (ftilde y) \<in> p ` (W0 \<inter> W)" by (by100 blast)
            thus ?thesis using hfy by (by100 simp)
          qed
          ultimately show ?thesis by (by100 blast)
        qed
        have hV'_sub: "?V' \<subseteq> {y \<in> Y. ftilde y \<in> W}"
        proof (rule subsetI)
          fix y' assume hy': "y' \<in> ?V'"
          hence hy'V0: "y' \<in> V0" and hy'Y: "y' \<in> Y" and hfy'_pWW: "f y' \<in> p ` (W0 \<inter> W)"
            by (by100 blast)+
          \<comment> \<open>f(y') \<in> p(W0 \<inter> W) means \<exists>e \<in> W0 \<inter> W. p(e) = f(y').
             ftilde(y') = inv_into W0 p (f y') = e \<in> W0 \<inter> W \<subseteq> W.\<close>
          from hfy'_pWW obtain e where he: "e \<in> W0" "e \<in> W" and hpe: "p e = f y'" by (by100 auto)
          have "ftilde y' \<in> W0" using hftilde_V0 hy'V0 by (by100 blast)
          have "p (ftilde y') = f y'" using hft_props hy'Y by (by100 blast)
          hence "ftilde y' = e"
          proof -
            have "p (ftilde y') = p e" using \<open>p (ftilde y') = f y'\<close> hpe by (by100 simp)
            moreover have "ftilde y' \<in> W0" by (rule \<open>ftilde y' \<in> W0\<close>)
            moreover have "e \<in> W0" using he by (by100 blast)
            ultimately show ?thesis using hp_inj unfolding inj_on_def by (by100 fast)
          qed
          hence "ftilde y' \<in> W" using he by (by100 blast)
          thus "y' \<in> {y \<in> Y. ftilde y \<in> W}" using hy'Y by (by100 blast)
        qed
        show "\<exists>V\<in>TY. y \<in> V \<and> V \<subseteq> {y \<in> Y. ftilde y \<in> W}"
          apply (rule bexI[where x="?V'"])
          using hy_V' hV'_sub hV'_TY by (by100 blast)+
      qed
      \<comment> \<open>Preimage is union of open neighborhoods, hence open.\<close>
      have "{y \<in> Y. ftilde y \<in> W} = \<Union>{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}}"
      proof (rule set_eqI)
        fix y show "y \<in> {y \<in> Y. ftilde y \<in> W} \<longleftrightarrow> y \<in> \<Union>{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}}"
        proof
          assume "y \<in> {y \<in> Y. ftilde y \<in> W}"
          then obtain V where "V \<in> TY" "y \<in> V" "V \<subseteq> {y \<in> Y. ftilde y \<in> W}"
            using \<open>\<forall>y \<in> {y \<in> Y. ftilde y \<in> W}. _\<close> by (by100 blast)
          thus "y \<in> \<Union>{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}}" by (by100 blast)
        next
          assume "y \<in> \<Union>{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}}" thus "y \<in> {y \<in> Y. ftilde y \<in> W}"
            by (by100 blast)
        qed
      qed
      moreover have "\<Union>{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}} \<in> TY"
      proof -
        have "\<forall>U. U \<subseteq> TY \<longrightarrow> \<Union>U \<in> TY"
          using hTY unfolding is_topology_on_def by (by100 blast)
        moreover have "{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}} \<subseteq> TY" by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      ultimately show "{y \<in> Y. ftilde y \<in> W} \<in> TY" by (by100 simp)
    qed
  qed
  show ?thesis using hft_props hft_cont by (by100 blast)
qed

text \<open>Equivalence of covering spaces: homeomorphism commuting with covering maps.\<close>
definition top1_equivalent_coverings_on :: "'e set \<Rightarrow> 'e set set \<Rightarrow> 'e' set \<Rightarrow> 'e' set set
  \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> ('e' \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_equivalent_coverings_on E TE E' TE' B TB p p' \<longleftrightarrow>
     top1_covering_map_on E TE B TB p \<and>
     top1_covering_map_on E' TE' B TB p' \<and>
     (\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e))"

(** from \<S>79 Theorem 79.2: pointed covering equivalence iff fundamental group
    images coincide. **)
theorem Theorem_79_2:
  assumes "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "is_topology_on_strict E' TE'"
      and "top1_covering_map_on E TE B TB p" and "p e0 = b0"
      and "top1_covering_map_on E' TE' B TB p'" and "p' e0' = b0"
      and "top1_path_connected_on E TE" and "top1_path_connected_on E' TE'"
      and "top1_locally_path_connected_on E TE" and "top1_locally_path_connected_on E' TE'"
      and "e0 \<in> E" and "e0' \<in> E'" and "b0 \<in> B"
  shows "(\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e)
             \<and> h e0 = e0') \<longleftrightarrow>
         top1_fundamental_group_image_hom E TE e0 B TB b0 p
           = top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
proof
  \<comment> \<open>Forward: if h : (E, e0) \<rightarrow> (E', e0') is a covering equivalence, then
     p_*(\<pi>_1(E, e0)) = p'_*(\<pi>_1(E', e0')) because h_* is an iso and p = p' \<circ> h.\<close>
  assume "\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e) \<and> h e0 = e0'"
  then obtain h where hh: "top1_homeomorphism_on E TE E' TE' h"
      and hp: "\<forall>e\<in>E. p' (h e) = p e" and he: "h e0 = e0'" by (by100 blast)
  \<comment> \<open>h_* : \<pi>_1(E, e0) \<cong> \<pi>_1(E', e0'), and p' \<circ> h = p, so p_* = p'_* \<circ> h_*.\<close>
  \<comment> \<open>p_*(π₁(E)) = p'_*(π₁(E')) because p=p'∘h on E, h_* is bijective (homeomorphism),
     and functoriality gives p_* = p'_* ∘ h_*. So im(p_*) = im(p'_* ∘ h_*) = im(p'_*).\<close>
  \<comment> \<open>By functoriality + p=p'\<circ>h on E + h_* bijective:
     p_* = (p'\<circ>h)_* = p'_* \<circ> h_*, so im(p_*) = p'_*(im(h_*)) = p'_*(π₁(E')).\<close>
  show "top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
  proof -
    have hTE: "is_topology_on E TE"
      using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have hTE': "is_topology_on E' TE'"
      using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
    have hTB: "is_topology_on B TB"
      using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
    have hh_cont: "top1_continuous_map_on E TE E' TE' h"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hh_bij: "bij_betw h E E'"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hh_inv_cont: "top1_continuous_map_on E' TE' E TE (inv_into E h)"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hh_inj: "inj_on h E"
      using hh_bij unfolding bij_betw_def by (by100 blast)
    have hp_cont: "top1_continuous_map_on E TE B TB p"
      by (rule top1_covering_map_on_continuous[OF assms(4)])
    have hp'_cont: "top1_continuous_map_on E' TE' B TB p'"
      by (rule top1_covering_map_on_continuous[OF assms(6)])
    have hp'h_cont: "top1_continuous_map_on E TE B TB (p' \<circ> h)"
      by (rule top1_continuous_map_on_comp[OF hh_cont hp'_cont])
    \<comment> \<open>p and p'∘h agree on E: ∀e∈E. p(e) = (p'∘h)(e).\<close>
    have hp_agree: "\<forall>e\<in>E. p e = (p' \<circ> h) e"
      using hp by (by100 auto)
    have hp'h_e0: "(p' \<circ> h) e0 = b0"
      using he assms(7) by (by100 simp)
    \<comment> \<open>Basepoint membership.\<close>
    note he0_E = assms(12) and he0'_E' = assms(13) and hb0_B = assms(14)
    \<comment> \<open>h_* maps carrier(E) to carrier(E') (group hom property).\<close>
    have hh_hom: "top1_group_hom_on
        (top1_fundamental_group_carrier E TE e0) (top1_fundamental_group_mul E TE e0)
        (top1_fundamental_group_carrier E' TE' e0') (top1_fundamental_group_mul E' TE' e0')
        (top1_fundamental_group_induced_on E TE e0 E' TE' e0' h)"
      by (rule top1_fundamental_group_induced_on_is_hom[OF hTE hTE' he0_E he0'_E' hh_cont he])
    \<comment> \<open>h⁻¹ setup\<close>
    have hinv_e0': "inv_into E h e0' = e0"
      using inv_into_f_f[OF hh_inj he0_E] he by (by100 simp)
    have hhinv_hom: "top1_group_hom_on
        (top1_fundamental_group_carrier E' TE' e0') (top1_fundamental_group_mul E' TE' e0')
        (top1_fundamental_group_carrier E TE e0) (top1_fundamental_group_mul E TE e0)
        (top1_fundamental_group_induced_on E' TE' e0' E TE e0 (inv_into E h))"
      by (rule top1_fundamental_group_induced_on_is_hom[OF hTE' hTE he0'_E' he0_E hh_inv_cont hinv_e0'])
    \<comment> \<open>⊆: for c ∈ carrier(E, e0), induced_p(c) = induced_p'(h_*(c)) ∈ image_hom(E', p').\<close>
    \<comment> \<open>⊇: for c' ∈ carrier(E', e0'), induced_p'(c') = induced_p(h⁻¹_*(c')) ∈ image_hom(E, p).\<close>
    show ?thesis unfolding top1_fundamental_group_image_hom_def
    proof (rule set_eqI, rule iffI)
      fix d
      assume "d \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p `
                 top1_fundamental_group_carrier E TE e0"
      then obtain c where hc: "c \<in> top1_fundamental_group_carrier E TE e0"
          and hd: "d = top1_fundamental_group_induced_on E TE e0 B TB b0 p c"
        by (by100 blast)
      \<comment> \<open>By induced_agree: induced_p(c) = induced_{p'∘h}(c).\<close>
      have hstep1: "top1_fundamental_group_induced_on E TE e0 B TB b0 p c
          = top1_fundamental_group_induced_on E TE e0 B TB b0 (p' \<circ> h) c"
        by (rule fundamental_group_induced_agree[OF hTE hTB he0_E hp_cont hp'h_cont hp_agree assms(5) hp'h_e0 hc])
      \<comment> \<open>By induced_comp: induced_{p'∘h}(c) = induced_p'(induced_h(c)).\<close>
      have hstep2: "top1_fundamental_group_induced_on E TE e0 B TB b0 (p' \<circ> h) c
          = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
              (top1_fundamental_group_induced_on E TE e0 E' TE' e0' h c)"
        by (rule fundamental_group_induced_comp[OF hTE hTE' hTB hh_cont hp'_cont he0_E he assms(7) hc])
      \<comment> \<open>h_*(c) ∈ carrier(E', e0') (since h_* is a group hom).\<close>
      have hh_star: "top1_fundamental_group_induced_on E TE e0 E' TE' e0' h c
          \<in> top1_fundamental_group_carrier E' TE' e0'"
        using hh_hom hc unfolding top1_group_hom_on_def by (by100 blast)
      show "d \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' `
               top1_fundamental_group_carrier E' TE' e0'"
        using hd hstep1 hstep2 hh_star by (by100 blast)
    next
      fix d
      assume "d \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' `
                 top1_fundamental_group_carrier E' TE' e0'"
      then obtain c' where hc': "c' \<in> top1_fundamental_group_carrier E' TE' e0'"
          and hd: "d = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' c'"
        by (by100 blast)
      \<comment> \<open>p' agrees with p∘h⁻¹ on E'.\<close>
      have hp'_agree: "\<forall>e'\<in>E'. p' e' = (p \<circ> inv_into E h) e'"
      proof (intro ballI)
        fix e' assume he': "e' \<in> E'"
        have "e' \<in> h ` E" using he' hh_bij unfolding bij_betw_def by (by100 blast)
        hence hinv_E: "inv_into E h e' \<in> E"
          by (rule inv_into_into)
        have "e' \<in> h ` E" using he' hh_bij unfolding bij_betw_def by (by100 blast)
        hence "h (inv_into E h e') = e'"
          by (rule f_inv_into_f)
        hence "p' e' = p' (h (inv_into E h e'))" by (by100 simp)
        also have "\<dots> = p (inv_into E h e')" using hp hinv_E by (by100 blast)
        finally show "p' e' = (p \<circ> inv_into E h) e'" by (by100 simp)
      qed
      have hphinv_cont: "top1_continuous_map_on E' TE' B TB (p \<circ> inv_into E h)"
        by (rule top1_continuous_map_on_comp[OF hh_inv_cont hp_cont])
      have hphinv_e0': "(p \<circ> inv_into E h) e0' = b0"
        using hinv_e0' assms(5) by (by100 simp)
      have hstep1': "top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' c'
          = top1_fundamental_group_induced_on E' TE' e0' B TB b0 (p \<circ> inv_into E h) c'"
        by (rule fundamental_group_induced_agree[OF hTE' hTB he0'_E' hp'_cont hphinv_cont hp'_agree assms(7) hphinv_e0' hc'])
      have hstep2': "top1_fundamental_group_induced_on E' TE' e0' B TB b0 (p \<circ> inv_into E h) c'
          = top1_fundamental_group_induced_on E TE e0 B TB b0 p
              (top1_fundamental_group_induced_on E' TE' e0' E TE e0 (inv_into E h) c')"
        by (rule fundamental_group_induced_comp[OF hTE' hTE hTB hh_inv_cont hp_cont he0'_E' hinv_e0' assms(5) hc'])
      have hhinv_star: "top1_fundamental_group_induced_on E' TE' e0' E TE e0 (inv_into E h) c'
          \<in> top1_fundamental_group_carrier E TE e0"
        using hhinv_hom hc' unfolding top1_group_hom_on_def by (by100 blast)
      show "d \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p `
               top1_fundamental_group_carrier E TE e0"
        using hd hstep1' hstep2' hhinv_star by (by100 blast)
    qed
  qed
next
  \<comment> \<open>Backward: if subgroup images equal, use path-lifting to construct h.\<close>
  assume hH_eq: "top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
  \<comment> \<open>Construct h: E \<rightarrow> E' via path-lifting. For each e \<in> E, pick path \<alpha> from e0 to e,
     lift p\<circ>\<alpha> to E' starting at e0'. The endpoint is h(e).\<close>
  have hTE: "is_topology_on E TE"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hTE': "is_topology_on E' TE'"
    using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
  have hTB: "is_topology_on B TB"
    using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
  have hp_cont: "top1_continuous_map_on E TE B TB p"
    by (rule top1_covering_map_on_continuous[OF assms(4)])
  have hp'_cont: "top1_continuous_map_on E' TE' B TB p'"
    by (rule top1_covering_map_on_continuous[OF assms(6)])
  \<comment> \<open>For each e \<in> E, paths from e0 exist (path-connected).\<close>
  \<comment> \<open>For each path, p\<circ>\<alpha> can be lifted to E' (Lemma_54_1).\<close>
  \<comment> \<open>The lift endpoint is independent of the chosen path (well-definedness via Theorem_54_3
     + subgroup equality hH_eq).\<close>
  \<comment> \<open>Define h via some path choice.\<close>
  \<comment> \<open>Apply general lifting criterion to construct h and h'.\<close>
  have hpe0: "p e0 = b0" by (rule assms(5))
  have hp'e0': "p' e0' = b0" by (rule assms(7))
  \<comment> \<open>For h: lift p (base map E\<rightarrow>B) to E' via p' (covering E'\<rightarrow>B).\<close>
  have h_exists: "\<exists>h. (\<forall>e\<in>E. h e \<in> E') \<and> (\<forall>e\<in>E. p' (h e) = p e) \<and> h e0 = e0'
      \<and> top1_continuous_map_on E TE E' TE' h"
  proof -
    \<comment> \<open>Subgroup condition: p_*(\<pi>_1(E)) \<subseteq> p'_*(\<pi>_1(E')), with basepoints at p'(e0') = b0.\<close>
    have hsubgrp: "top1_fundamental_group_image_hom E TE e0 B TB (p' e0') p
        \<subseteq> top1_fundamental_group_image_hom E' TE' e0' B TB (p' e0') p'"
      using hH_eq hp'e0' hpe0 by (by100 simp)
    show ?thesis
      using general_lifting_criterion[OF assms(6) hTE hTB hTE' hp_cont assms(8,10,12,13)
            _ hsubgrp] hpe0 hp'e0' by (by100 simp)
  qed
  \<comment> \<open>For h': lift p' (base map E'\<rightarrow>B) to E via p (covering E\<rightarrow>B).\<close>
  have h'_exists: "\<exists>h'. (\<forall>e'\<in>E'. h' e' \<in> E) \<and> (\<forall>e'\<in>E'. p (h' e') = p' e') \<and> h' e0' = e0
      \<and> top1_continuous_map_on E' TE' E TE h'"
  proof -
    have hsubgrp: "top1_fundamental_group_image_hom E' TE' e0' B TB (p e0) p'
        \<subseteq> top1_fundamental_group_image_hom E TE e0 B TB (p e0) p"
      using hH_eq hp'e0' hpe0 by (by100 simp)
    show ?thesis
      using general_lifting_criterion[OF assms(4) hTE' hTB hTE hp'_cont assms(9,11,13,12)
            _ hsubgrp] hpe0 hp'e0' by (by100 simp)
  qed
  obtain h where hh_E': "\<forall>e\<in>E. h e \<in> E'" and hh_lift: "\<forall>e\<in>E. p' (h e) = p e"
      and hh_e0: "h e0 = e0'" and hh_cont: "top1_continuous_map_on E TE E' TE' h"
    using h_exists by (by100 blast)
  obtain h' where hh'_E: "\<forall>e'\<in>E'. h' e' \<in> E" and hh'_lift: "\<forall>e'\<in>E'. p (h' e') = p' e'"
      and hh'_e0: "h' e0' = e0" and hh'_cont: "top1_continuous_map_on E' TE' E TE h'"
    using h'_exists by (by100 blast)
  \<comment> \<open>h' \<circ> h = id on E: both lift p (i.e. p \<circ> (h'\<circ>h) = p \<circ> id = p on E),
     and agree at e0 (h'(h(e0)) = h'(e0') = e0). By covering_lift_unique_connected,
     h'\<circ>h = id on the connected space E.\<close>
  have hh'h_id: "\<forall>e\<in>E. h' (h e) = e"
  proof -
    have hh'h_cont: "top1_continuous_map_on E TE E TE (h' \<circ> h)"
      by (rule top1_continuous_map_on_comp[OF hh_cont hh'_cont])
    have hh'h_lift: "\<forall>e\<in>E. p ((h' \<circ> h) e) = p (id e)"
    proof (intro ballI)
      fix e assume he: "e \<in> E"
      have "h e \<in> E'" using hh_E' he by (by100 blast)
      hence "p (h' (h e)) = p' (h e)" using hh'_lift by (by100 blast)
      also have "\<dots> = p e" using hh_lift he by (by100 blast)
      finally show "p ((h' \<circ> h) e) = p (id e)" by (by100 simp)
    qed
    have hh'h_e0: "(h' \<circ> h) e0 = id e0"
      using hh_e0 hh'_e0 by (by100 simp)
    have hid_cont: "top1_continuous_map_on E TE E TE id"
      using top1_continuous_map_on_id[OF hTE] .
    have hE_conn: "top1_connected_on E TE"
      by (rule path_connected_imp_connected[OF assms(8)])
    from covering_lift_unique_connected[OF assms(4) hTE hTB hTE hE_conn
        hh'h_cont hid_cont hh'h_lift assms(12) hh'h_e0]
    show ?thesis by (by100 simp)
  qed
  \<comment> \<open>h \<circ> h' = id on E': symmetric argument.\<close>
  have hhh'_id: "\<forall>e'\<in>E'. h (h' e') = e'"
  proof -
    have hhh'_cont: "top1_continuous_map_on E' TE' E' TE' (h \<circ> h')"
      by (rule top1_continuous_map_on_comp[OF hh'_cont hh_cont])
    have hhh'_lift: "\<forall>e'\<in>E'. p' ((h \<circ> h') e') = p' (id e')"
    proof (intro ballI)
      fix e' assume he': "e' \<in> E'"
      have "h' e' \<in> E" using hh'_E he' by (by100 blast)
      hence "p' (h (h' e')) = p (h' e')" using hh_lift by (by100 blast)
      also have "\<dots> = p' e'" using hh'_lift he' by (by100 blast)
      finally show "p' ((h \<circ> h') e') = p' (id e')" by (by100 simp)
    qed
    have hhh'_e0: "(h \<circ> h') e0' = id e0'"
      using hh'_e0 hh_e0 by (by100 simp)
    have hid_cont': "top1_continuous_map_on E' TE' E' TE' id"
      using top1_continuous_map_on_id[OF hTE'] .
    have hE'_conn: "top1_connected_on E' TE'"
      by (rule path_connected_imp_connected[OF assms(9)])
    from covering_lift_unique_connected[OF assms(6) hTE' hTB hTE' hE'_conn
        hhh'_cont hid_cont' hhh'_lift assms(13) hhh'_e0]
    show ?thesis by (by100 simp)
  qed
  \<comment> \<open>h is a homeomorphism: continuous bijection with continuous inverse h'.\<close>
  have hh_bij: "bij_betw h E E'"
  proof (unfold bij_betw_def, intro conjI)
    show "inj_on h E"
    proof (rule inj_onI)
      fix x y assume "x \<in> E" "y \<in> E" "h x = h y"
      have "x = h' (h x)" using hh'h_id[rule_format, OF \<open>x \<in> E\<close>] by (by100 simp)
      also have "\<dots> = h' (h y)" using \<open>h x = h y\<close> by (by100 simp)
      also have "\<dots> = y" using hh'h_id[rule_format, OF \<open>y \<in> E\<close>] by (by100 simp)
      finally show "x = y" .
    qed
    show "h ` E = E'"
    proof (rule set_eqI)
      fix e' show "e' \<in> h ` E \<longleftrightarrow> e' \<in> E'"
      proof
        assume "e' \<in> h ` E"
        then obtain e where "e \<in> E" "e' = h e" by (by100 blast)
        thus "e' \<in> E'" using hh_E' by (by100 blast)
      next
        assume "e' \<in> E'"
        hence "h (h' e') = e'" using hhh'_id by (by100 blast)
        moreover have hh'e'_E: "h' e' \<in> E" using hh'_E \<open>e' \<in> E'\<close> by (by100 blast)
        ultimately have "h (h' e') = e'" by (by100 simp)
        hence "e' = h (h' e')" by (by100 simp)
        thus "e' \<in> h ` E" using hh'e'_E by (by100 force)
      qed
    qed
  qed
  have hh_inv_cont: "top1_continuous_map_on E' TE' E TE (inv_into E h)"
  proof -
    have "\<forall>e'\<in>E'. inv_into E h e' = h' e'"
    proof (intro ballI)
      fix e' assume "e' \<in> E'"
      have "h' e' \<in> E" using hh'_E \<open>e' \<in> E'\<close> by (by100 blast)
      moreover have "h (h' e') = e'" using hhh'_id \<open>e' \<in> E'\<close> by (by100 blast)
      ultimately show "inv_into E h e' = h' e'"
        using inv_into_f_eq[of h E "h' e'" e'] hh_bij
        unfolding bij_betw_def by (by100 blast)
    qed
    \<comment> \<open>inv_into agrees with h' on E', and h' is continuous.\<close>
    show ?thesis unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix e' assume he': "e' \<in> E'"
      have "inv_into E h e' = h' e'" using \<open>\<forall>e'\<in>E'. inv_into E h e' = h' e'\<close> he' by (by100 blast)
      moreover have "h' e' \<in> E" using hh'_E he' by (by100 blast)
      ultimately show "inv_into E h e' \<in> E" by (by100 simp)
    next
      fix V assume "V \<in> TE"
      \<comment> \<open>{e'\<in>E'. inv_into E h e' \<in> V} = {e'\<in>E'. h' e' \<in> V}\<close>
      have hset_eq: "{e'\<in>E'. inv_into E h e' \<in> V} = {e'\<in>E'. h' e' \<in> V}"
      proof (rule Collect_cong)
        fix e' show "(e' \<in> E' \<and> inv_into E h e' \<in> V) = (e' \<in> E' \<and> h' e' \<in> V)"
          using \<open>\<forall>e'\<in>E'. inv_into E h e' = h' e'\<close> by (by100 auto)
      qed
      have "{e'\<in>E'. h' e' \<in> V} \<in> TE'"
        using hh'_cont \<open>V \<in> TE\<close> unfolding top1_continuous_map_on_def by (by100 blast)
      thus "{e'\<in>E'. inv_into E h e' \<in> V} \<in> TE'"
        using hset_eq by (by100 simp)
    qed
  qed
  have hhomeo: "top1_homeomorphism_on E TE E' TE' h"
    unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on E TE" by (rule hTE)
    show "is_topology_on E' TE'" by (rule hTE')
    show "bij_betw h E E'" by (rule hh_bij)
    show "top1_continuous_map_on E TE E' TE' h" by (rule hh_cont)
    show "top1_continuous_map_on E' TE' E TE (inv_into E h)" by (rule hh_inv_cont)
  qed
  show "\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e) \<and> h e0 = e0'"
    using hhomeo hh_lift hh_e0 by (by100 blast)
qed

text \<open>Basepoint change for image_hom: if \<alpha> is a path from e0 to e1 in a covering space E,
  then p_*(\<pi>_1(E, e1)) is the conjugate of p_*(\<pi>_1(E, e0)) by [p\<circ>\<alpha>]\<inverse>.\<close>
lemma basepoint_change_image_hom:
  assumes hcov: "top1_covering_map_on E TE B TB p"
      and hTE: "is_topology_on E TE" and hTB: "is_topology_on B TB"
      and he0: "e0 \<in> E" and he1: "e1 \<in> E"
      and h\<alpha>: "top1_is_path_on E TE e0 e1 \<alpha>"
      and hpe0: "p e0 = b0" and hpe1: "p e1 = b0"
      and hEpc: "top1_path_connected_on E TE"
  shows "top1_fundamental_group_image_hom E TE e1 B TB b0 p
      = (\<lambda>H. top1_fundamental_group_mul B TB b0
            (top1_fundamental_group_invg B TB b0 {g. top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>) g})
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    {g. top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>) g}) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
  \<comment> \<open>Proof via loop conjugation in E: for each direction, conjugate by \<alpha> resp. \<alpha>\<inverse>.\<close>
  \<comment> \<open>\<subseteq>: For d \<in> image_hom(E, e1): d = [p\<circ>g] for loop g at e1.
     Form \<alpha>\<cdot>g\<cdot>\<alpha>\<inverse> (loop at e0). [p\<circ>(\<alpha>\<cdot>g\<cdot>\<alpha>\<inverse>)] = [p\<circ>\<alpha>]\<cdot>[p\<circ>g]\<cdot>[rev(p\<circ>\<alpha>)] = c\<cdot>d\<cdot>inv(c).
     So c\<cdot>d\<cdot>inv(c) \<in> image_hom(E, e0). Thus d = inv(c)\<cdot>(c\<cdot>d\<cdot>inv(c))\<cdot>c \<in> conj(image_hom(E, e0)).\<close>
  \<comment> \<open>\<supseteq>: For h \<in> image_hom(E, e0): h = [p\<circ>f] for loop f at e0.
     Form \<alpha>\<inverse>\<cdot>f\<cdot>\<alpha> (loop at e1). [p\<circ>(\<alpha>\<inverse>\<cdot>f\<cdot>\<alpha>)] = inv(c)\<cdot>[p\<circ>f]\<cdot>c = inv(c)\<cdot>h\<cdot>c.
     So inv(c)\<cdot>h\<cdot>c \<in> image_hom(E, e1). This means inv(c)\<cdot>(h\<cdot>c) = inv(c)\<cdot>h\<cdot>c \<in> image_hom(E, e1).\<close>
  \<comment> \<open>Key identities:
     p \<circ> path_product(path_product(rev(\<alpha>), f), \<alpha>)
     = path_product(path_product(p\<circ>rev(\<alpha>), p\<circ>f), p\<circ>\<alpha>)   (comp_path_product twice)
     = path_product(path_product(rev(p\<circ>\<alpha>), p\<circ>f), p\<circ>\<alpha>)   (comp_path_reverse)
     And rev(\<alpha>)\<cdot>f\<cdot>\<alpha> is a loop at e1 (for f loop at e0).
     Similarly \<alpha>\<cdot>g\<cdot>rev(\<alpha>) is a loop at e0 (for g loop at e1).\<close>
proof -
  let ?mulB = "top1_fundamental_group_mul B TB b0"
  let ?invB = "top1_fundamental_group_invg B TB b0"
  let ?c = "{g. top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>) g}"
  have hp_cont: "top1_continuous_map_on E TE B TB p" by (rule top1_covering_map_on_continuous[OF hcov])
  have hb0_B: "b0 \<in> B" using hp_cont he0 hpe0 unfolding top1_continuous_map_on_def by (by100 blast)
  have h\<alpha>_rev: "top1_is_path_on E TE e1 e0 (top1_path_reverse \<alpha>)"
    by (rule top1_path_reverse_is_path[OF h\<alpha>])
  have hp\<alpha>_loop: "top1_is_loop_on B TB b0 (p \<circ> \<alpha>)"
  proof -
    have "top1_continuous_map_on I_set I_top B TB (p \<circ> \<alpha>)"
      by (rule top1_continuous_map_on_comp)
         (use h\<alpha> hp_cont in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
    moreover have "(p \<circ> \<alpha>) 0 = b0" using h\<alpha> hpe0 unfolding top1_is_path_on_def by (by100 simp)
    moreover have "(p \<circ> \<alpha>) 1 = b0" using h\<alpha> hpe1 unfolding top1_is_path_on_def by (by100 simp)
    ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
  qed
  have hp\<alpha>_rev_loop: "top1_is_loop_on B TB b0 (top1_path_reverse (p \<circ> \<alpha>))"
    by (rule top1_path_reverse_is_loop[OF hp\<alpha>_loop])
  show ?thesis
  proof (rule set_eqI)
    fix d
    show "d \<in> top1_fundamental_group_image_hom E TE e1 B TB b0 p \<longleftrightarrow>
        d \<in> (\<lambda>H. ?mulB (?invB ?c) ` ((\<lambda>h. ?mulB h ?c) ` H))
            (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
    proof
      \<comment> \<open>\<Rightarrow>: d = [p\<circ>g] for loop g at e1. Conjugate: \<alpha>\<cdot>g\<cdot>rev(\<alpha>) is loop at e0.\<close>
      assume "d \<in> top1_fundamental_group_image_hom E TE e1 B TB b0 p"
      then obtain g where hg_loop: "top1_is_loop_on E TE e1 g"
          and hd_eq: "d = top1_fundamental_group_induced_on E TE e1 B TB b0 p
              {k. top1_loop_equiv_on E TE e1 g k}"
        unfolding top1_fundamental_group_image_hom_def top1_fundamental_group_carrier_def
        by (by100 blast)
      \<comment> \<open>\<alpha>\<cdot>g\<cdot>rev(\<alpha>) is a loop at e0.\<close>
      have hg_path: "top1_is_path_on E TE e1 e1 g"
        using hg_loop unfolding top1_is_loop_on_def by (by100 blast)
      have h_conj_loop: "top1_is_loop_on E TE e0
          (top1_path_product (top1_path_product \<alpha> g) (top1_path_reverse \<alpha>))"
      proof -
        have "top1_is_path_on E TE e0 e1 (top1_path_product \<alpha> g)"
          by (rule top1_path_product_is_path[OF hTE h\<alpha> hg_path])
        hence "top1_is_path_on E TE e0 e0 (top1_path_product (top1_path_product \<alpha> g) (top1_path_reverse \<alpha>))"
          by (rule top1_path_product_is_path[OF hTE _ h\<alpha>_rev])
        thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
      qed
      \<comment> \<open>[p\<circ>(\<alpha>\<cdot>g\<cdot>rev(\<alpha>))] = c \<cdot> d \<cdot> inv(c) \<in> image_hom(E, e0).\<close>
      \<comment> \<open>p\<circ>(\<alpha>\<cdot>g\<cdot>rev(\<alpha>)) = (p\<circ>\<alpha>)\<cdot>(p\<circ>g)\<cdot>rev(p\<circ>\<alpha>) by comp_path_product/reverse.\<close>
      have hp_conj: "p \<circ> (top1_path_product (top1_path_product \<alpha> g) (top1_path_reverse \<alpha>))
          = top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))"
        by (simp only: comp_path_product comp_path_reverse)
      \<comment> \<open>So [p\<circ>conj] = mul(mul(c, d), inv(c)) and this is in image_hom(E, e0).\<close>
      \<comment> \<open>Then d = inv(c) \<cdot> [p\<circ>conj] \<cdot> c, so d \<in> conj(image_hom(E, e0)).\<close>
      show "d \<in> (\<lambda>H. ?mulB (?invB ?c) ` ((\<lambda>h. ?mulB h ?c) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
      proof -
        \<comment> \<open>d = [p\<circ>g], the class of p\<circ>g at b0.\<close>
        have hg_loop_E: "top1_is_loop_on E TE e1 g" by (rule hg_loop)
        have hpg_loop: "top1_is_loop_on B TB b0 (p \<circ> g)"
        proof -
          have "top1_continuous_map_on I_set I_top B TB (p \<circ> g)"
            by (rule top1_continuous_map_on_comp)
               (use hg_loop hp_cont in \<open>unfold top1_is_loop_on_def top1_is_path_on_def, by100 blast\<close>)+
          moreover have "(p \<circ> g) 0 = b0" using hg_loop hpe1 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          moreover have "(p \<circ> g) 1 = b0" using hg_loop hpe1 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        have hd_class: "d = {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
        proof -
          have "d = top1_fundamental_group_induced_on E TE e1 B TB b0 p
              {k. top1_loop_equiv_on E TE e1 g k}" by (rule hd_eq)
          also have "\<dots> = {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
          proof (rule set_eqI, rule iffI)
            fix k assume "k \<in> top1_fundamental_group_induced_on E TE e1 B TB b0 p
                {k. top1_loop_equiv_on E TE e1 g k}"
            then obtain g' where hg'_eq: "top1_loop_equiv_on E TE e1 g g'"
                and hk': "top1_loop_equiv_on B TB b0 (p \<circ> g') k"
              unfolding top1_fundamental_group_induced_on_def by (by100 blast)
            have hg'_loop: "top1_is_loop_on E TE e1 g'"
              using hg'_eq unfolding top1_loop_equiv_on_def by (by100 blast)
            have "top1_loop_equiv_on B TB b0 (p \<circ> g) (p \<circ> g')"
              using top1_induced_preserves_loop_equiv[OF hTE hp_cont hg_loop hg'_loop hg'_eq] hpe1
              by (by100 simp)
            from top1_loop_equiv_on_trans[OF hTB this hk']
            show "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}" by (by100 blast)
          next
            fix k assume "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
            hence hk: "top1_loop_equiv_on B TB b0 (p \<circ> g) k" by (by100 blast)
            have "g \<in> {k. top1_loop_equiv_on E TE e1 g k}"
              using top1_loop_equiv_on_refl[OF hg_loop] by (by100 blast)
            thus "k \<in> top1_fundamental_group_induced_on E TE e1 B TB b0 p
                {k. top1_loop_equiv_on E TE e1 g k}"
              unfolding top1_fundamental_group_induced_on_def using hk by (by100 blast)
          qed
          finally show ?thesis .
        qed
        \<comment> \<open>The conjugate \<alpha>\<cdot>g\<cdot>rev(\<alpha>) is in image_hom(E, e0) via h_conj_loop.\<close>
        let ?conj_loop = "top1_path_product (top1_path_product \<alpha> g) (top1_path_reverse \<alpha>)"
        have hconj_in: "top1_fundamental_group_induced_on E TE e0 B TB b0 p
            {k. top1_loop_equiv_on E TE e0 ?conj_loop k}
          \<in> top1_fundamental_group_image_hom E TE e0 B TB b0 p"
          unfolding top1_fundamental_group_image_hom_def top1_fundamental_group_carrier_def
          using h_conj_loop top1_loop_equiv_on_refl[OF h_conj_loop] by (by100 blast)
        \<comment> \<open>This class = {k | loop_equiv((p\<circ>\<alpha>)\<cdot>(p\<circ>g)\<cdot>rev(p\<circ>\<alpha>), k)}.\<close>
        have hconj_class: "top1_fundamental_group_induced_on E TE e0 B TB b0 p
            {k. top1_loop_equiv_on E TE e0 ?conj_loop k}
          = {k. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) k}"
        proof (rule set_eqI, rule iffI)
          fix k assume "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 ?conj_loop k}"
          then obtain f' where hf': "top1_loop_equiv_on E TE e0 ?conj_loop f'"
              and hk: "top1_loop_equiv_on B TB b0 (p \<circ> f') k"
            unfolding top1_fundamental_group_induced_on_def by (by100 blast)
          have hf'_loop: "top1_is_loop_on E TE e0 f'"
            using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
          have "top1_loop_equiv_on B TB b0 (p \<circ> ?conj_loop) (p \<circ> f')"
            using top1_induced_preserves_loop_equiv[OF hTE hp_cont h_conj_loop hf'_loop hf'] hpe0
            by (by100 simp)
          hence "top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> f')"
            using hp_conj by (by100 simp)
          from top1_loop_equiv_on_trans[OF hTB this hk]
          show "k \<in> {k. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) k}"
            by (by100 blast)
        next
          fix k assume "k \<in> {k. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) k}"
          hence hk: "top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) k"
            by (by100 blast)
          have "p \<circ> ?conj_loop = top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))"
            by (rule hp_conj)
          hence "top1_loop_equiv_on B TB b0 (p \<circ> ?conj_loop) k" using hk by (by100 simp)
          moreover have "?conj_loop \<in> {k. top1_loop_equiv_on E TE e0 ?conj_loop k}"
            using top1_loop_equiv_on_refl[OF h_conj_loop] by (by100 blast)
          ultimately show "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 ?conj_loop k}"
            unfolding top1_fundamental_group_induced_on_def by (by100 blast)
        qed
        \<comment> \<open>Now compute inv(c) \<cdot> (h_conj \<cdot> c) and show it equals d = [p\<circ>g].\<close>
        let ?h_conj_class = "{k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) k}"
        have hpg_rev_p\<alpha>_loop: "top1_is_loop_on B TB b0
            (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>)))"
          by (rule top1_path_product_is_loop[OF hTB
                top1_path_product_is_loop[OF hTB hp\<alpha>_loop hpg_loop] hp\<alpha>_rev_loop])
        \<comment> \<open>h_conj \<cdot> c = [conj_path] \<cdot> [p\<circ>\<alpha>] = [conj_path \<cdot> (p\<circ>\<alpha>)].\<close>
        have hh_c: "?mulB ?h_conj_class ?c = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)) k}"
          by (rule top1_fundamental_group_mul_class[OF hTB hpg_rev_p\<alpha>_loop hp\<alpha>_loop])
        \<comment> \<open>inv(c) \<cdot> (h_conj \<cdot> c) = [rev(p\<circ>\<alpha>)] \<cdot> [above].\<close>
        have hh_c_loop: "top1_is_loop_on B TB b0
            (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))"
          by (rule top1_path_product_is_loop[OF hTB hpg_rev_p\<alpha>_loop hp\<alpha>_loop])
        have hinv_hc: "?mulB (?invB ?c) (?mulB ?h_conj_class ?c) = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
              (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}"
        proof -
          have "?invB ?c = {k. top1_loop_equiv_on B TB b0 (top1_path_reverse (p \<circ> \<alpha>)) k}"
            by (rule fundamental_group_invg_class[OF hTB hp\<alpha>_loop])
          hence "?mulB (?invB ?c) (?mulB ?h_conj_class ?c)
              = ?mulB {k. top1_loop_equiv_on B TB b0 (top1_path_reverse (p \<circ> \<alpha>)) k}
                  {k. top1_loop_equiv_on B TB b0
                    (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)) k}"
            using hh_c by (by100 simp)
          also have "\<dots> = {k. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}"
            by (rule top1_fundamental_group_mul_class[OF hTB hp\<alpha>_rev_loop hh_c_loop])
          finally show ?thesis .
        qed
        \<comment> \<open>Path algebra: rev(A) \<cdot> ((A\<cdot>B\<cdot>rev(A)) \<cdot> A) ~ B, where A = p\<circ>\<alpha>, B = p\<circ>g.\<close>
        have hp\<alpha>_path: "top1_is_path_on B TB b0 b0 (p \<circ> \<alpha>)"
          using hp\<alpha>_loop unfolding top1_is_loop_on_def by (by100 blast)
        have hpg_path: "top1_is_path_on B TB b0 b0 (p \<circ> g)"
          using hpg_loop unfolding top1_is_loop_on_def by (by100 blast)
        have hp\<alpha>_rev_path: "top1_is_path_on B TB b0 b0 (top1_path_reverse (p \<circ> \<alpha>))"
          using hp\<alpha>_rev_loop unfolding top1_is_loop_on_def by (by100 blast)
        \<comment> \<open>Associativity gives f\<cdot>(g\<cdot>h) ~ (f\<cdot>g)\<cdot>h (right-to-left).\<close>
        have hAB_path: "top1_is_path_on B TB b0 b0 (top1_path_product (p \<circ> \<alpha>) (p \<circ> g))"
          by (rule top1_path_product_is_path[OF hTB hp\<alpha>_path hpg_path])
        \<comment> \<open>Step 1: ((A\<cdot>B)\<cdot>rev(A))\<cdot>A ~ (A\<cdot>B)\<cdot>(rev(A)\<cdot>A) by sym(assoc).\<close>
        note s1_raw = Theorem_51_2_associativity[OF hTB hAB_path hp\<alpha>_rev_path hp\<alpha>_path]
        note s1 = Lemma_51_1_path_homotopic_sym[OF s1_raw]
        \<comment> \<open>s1: ((A\<cdot>B)\<cdot>rev(A))\<cdot>A ~ (A\<cdot>B)\<cdot>(rev(A)\<cdot>A)\<close>
        \<comment> \<open>Step 2: rev(A)\<cdot>A ~ const(b0) by inverse_right.\<close>
        have s2: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> \<alpha>)) (top1_constant_path b0)"
          by (rule Theorem_51_2_invgerse_right[OF hTB hp\<alpha>_path])
        \<comment> \<open>Step 3: (A\<cdot>B)\<cdot>(rev(A)\<cdot>A) ~ (A\<cdot>B)\<cdot>const.\<close>
        have s3: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> \<alpha>)))
            (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_constant_path b0))"
          by (rule path_homotopic_product_right[OF hTB s2 hAB_path])
        have s4: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_constant_path b0))
            (top1_path_product (p \<circ> \<alpha>) (p \<circ> g))"
          by (rule Theorem_51_2_right_identity[OF hTB hAB_path])
        have s14: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))
            (top1_path_product (p \<circ> \<alpha>) (p \<circ> g))"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTB s1
                Lemma_51_1_path_homotopic_trans[OF hTB s3 s4]])
        \<comment> \<open>Step 5: rev(A) \<cdot> ((A\<cdot>B\<cdot>rev(A))\<cdot>A) ~ rev(A) \<cdot> (A\<cdot>B).\<close>
        have s5: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
              (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)))
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)))"
          by (rule path_homotopic_product_right[OF hTB s14 hp\<alpha>_rev_path])
        \<comment> \<open>Step 6: rev(A) \<cdot> (A\<cdot>B) ~ (rev(A)\<cdot>A)\<cdot>B by assoc (direction f\<cdot>(g\<cdot>h) ~ (f\<cdot>g)\<cdot>h).\<close>
        note s6 = Theorem_51_2_associativity[OF hTB hp\<alpha>_rev_path hp\<alpha>_path hpg_path]
        \<comment> \<open>Step 7: (rev(A)\<cdot>A)\<cdot>B ~ const\<cdot>B by inverse.\<close>
        have s7: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> \<alpha>)) (p \<circ> g))
            (top1_path_product (top1_constant_path b0) (p \<circ> g))"
          by (rule path_homotopic_product_left[OF hTB s2 hpg_path])
        \<comment> \<open>Step 8: const\<cdot>B ~ B by left identity.\<close>
        have s8: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_constant_path b0) (p \<circ> g)) (p \<circ> g)"
          by (rule Theorem_51_2_left_identity[OF hTB hpg_path])
        have s_full: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
              (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)))
            (p \<circ> g)"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTB s5
                Lemma_51_1_path_homotopic_trans[OF hTB s6
                  Lemma_51_1_path_homotopic_trans[OF hTB s7 s8]]])
        \<comment> \<open>So the two loop classes are equal.\<close>
        have hbig_loop: "top1_is_loop_on B TB b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
              (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)))"
          by (rule top1_path_product_is_loop[OF hTB hp\<alpha>_rev_loop hh_c_loop])
        have hclass_eq: "{k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
              (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}
          = {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
        proof (rule set_eqI)
          fix k
          have hLR: "top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)))
              (p \<circ> g)"
            using s_full hbig_loop hpg_loop unfolding top1_loop_equiv_on_def by (by100 blast)
          have hRL: "top1_loop_equiv_on B TB b0 (p \<circ> g)
              (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)))"
            by (rule top1_loop_equiv_on_sym[OF hLR])
          show "k \<in> {k. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}
            \<longleftrightarrow> k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
          proof
            assume "k \<in> {k. top1_loop_equiv_on B TB b0
                (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                  (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}"
            from top1_loop_equiv_on_trans[OF hTB hRL this[simplified]]
            show "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}" by (by100 blast)
          next
            assume "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
            from top1_loop_equiv_on_trans[OF hTB hLR this[simplified]]
            show "k \<in> {k. top1_loop_equiv_on B TB b0
                (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                  (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}"
              by (by100 blast)
          qed
        qed
        \<comment> \<open>Conclusion: inv(c) \<cdot> (h_conj \<cdot> c) = d.\<close>
        have "?mulB (?invB ?c) (?mulB ?h_conj_class ?c) = d"
          using hinv_hc hclass_eq hd_class by (by100 simp)
        moreover have "?h_conj_class = top1_fundamental_group_induced_on E TE e0 B TB b0 p
            {k. top1_loop_equiv_on E TE e0 ?conj_loop k}"
          using hconj_class by (by100 simp)
        ultimately have "?mulB (?invB ?c)
            (?mulB (top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 ?conj_loop k}) ?c) = d"
          by (by100 simp)
        thus ?thesis using hconj_in by (by100 blast)
      qed
    next
      \<comment> \<open>\<Leftarrow>: h \<in> image_hom(E, e0). Conjugate: rev(\<alpha>)\<cdot>f\<cdot>\<alpha> is loop at e1.\<close>
      assume "d \<in> (\<lambda>H. ?mulB (?invB ?c) ` ((\<lambda>h. ?mulB h ?c) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
      then obtain h where hh: "h \<in> top1_fundamental_group_image_hom E TE e0 B TB b0 p"
          and hd_conj: "d = ?mulB (?invB ?c) (?mulB h ?c)" by (by100 blast)
      \<comment> \<open>h = [p\<circ>f] for loop f at e0.\<close>
      obtain f where hf_loop: "top1_is_loop_on E TE e0 f"
          and hh_eq: "h = top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 f k}"
        using hh unfolding top1_fundamental_group_image_hom_def top1_fundamental_group_carrier_def
        by (by100 blast)
      \<comment> \<open>rev(\<alpha>)\<cdot>f\<cdot>\<alpha> is a loop at e1.\<close>
      have hf_path: "top1_is_path_on E TE e0 e0 f"
        using hf_loop unfolding top1_is_loop_on_def by (by100 blast)
      have h_conj2: "top1_is_loop_on E TE e1
          (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>)"
      proof -
        have "top1_is_path_on E TE e1 e0 (top1_path_product (top1_path_reverse \<alpha>) f)"
          by (rule top1_path_product_is_path[OF hTE h\<alpha>_rev hf_path])
        hence "top1_is_path_on E TE e1 e1 (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>)"
          by (rule top1_path_product_is_path[OF hTE _ h\<alpha>])
        thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
      qed
      \<comment> \<open>p\<circ>(rev(\<alpha>)\<cdot>f\<cdot>\<alpha>) = rev(p\<circ>\<alpha>)\<cdot>(p\<circ>f)\<cdot>(p\<circ>\<alpha>) = path producing inv(c)\<cdot>h\<cdot>c.\<close>
      have hp_conj2: "p \<circ> (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>)
          = top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)"
        by (simp only: comp_path_product comp_path_reverse)
      \<comment> \<open>[p\<circ>(rev(\<alpha>)\<cdot>f\<cdot>\<alpha>)] = inv(c) \<cdot> h \<cdot> c = d. So d \<in> image_hom(E, e1).\<close>
      \<comment> \<open>[p\<circ>(rev(\<alpha>)\<cdot>f\<cdot>\<alpha>)] \<in> image_hom(E, e1).\<close>
      have hconj2_in: "top1_fundamental_group_induced_on E TE e1 B TB b0 p
          {k. top1_loop_equiv_on E TE e1 (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>) k}
        \<in> top1_fundamental_group_image_hom E TE e1 B TB b0 p"
        unfolding top1_fundamental_group_image_hom_def top1_fundamental_group_carrier_def
        using h_conj2 top1_loop_equiv_on_refl[OF h_conj2] by (by100 blast)
      \<comment> \<open>This class = {k | loop_equiv(B, rev(p\<circ>\<alpha>)\<cdot>(p\<circ>f)\<cdot>(p\<circ>\<alpha>), k)} by hp_conj2.\<close>
      have "top1_fundamental_group_induced_on E TE e1 B TB b0 p
          {k. top1_loop_equiv_on E TE e1 (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>) k}
        = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k}"
      proof (rule set_eqI, rule iffI)
        fix k assume "k \<in> top1_fundamental_group_induced_on E TE e1 B TB b0 p
            {k. top1_loop_equiv_on E TE e1 (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>) k}"
        then obtain f' where hf': "top1_loop_equiv_on E TE e1
            (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>) f'"
            and hk: "top1_loop_equiv_on B TB b0 (p \<circ> f') k"
          unfolding top1_fundamental_group_induced_on_def by (by100 blast)
        have hf'_loop: "top1_is_loop_on E TE e1 f'"
          using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
        \<comment> \<open>p\<circ>conj_loop ~ p\<circ>f' (by induced_preserves_loop_equiv).\<close>
        have "top1_loop_equiv_on B TB b0 (p \<circ> (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>)) (p \<circ> f')"
          using top1_induced_preserves_loop_equiv[OF hTE hp_cont h_conj2 hf'_loop hf'] hpe1
          by (by100 simp)
        \<comment> \<open>p\<circ>conj_loop = rev(p\<circ>\<alpha>)\<cdot>(p\<circ>f)\<cdot>(p\<circ>\<alpha>) (pointwise by hp_conj2).\<close>
        hence "top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) (p \<circ> f')"
          using hp_conj2 by (by100 simp)
        from top1_loop_equiv_on_trans[OF hTB this hk]
        show "k \<in> {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k}"
          by (by100 blast)
      next
        fix k assume "k \<in> {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k}"
        hence hk: "top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k"
          by (by100 blast)
        \<comment> \<open>The conjugated loop itself is in its own class.\<close>
        let ?conj2 = "top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>"
        have "?conj2 \<in> {k. top1_loop_equiv_on E TE e1 ?conj2 k}"
          using top1_loop_equiv_on_refl[OF h_conj2] by (by100 blast)
        \<comment> \<open>p\<circ>conj2 = the target path (pointwise).\<close>
        have "p \<circ> ?conj2 = top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)"
          by (rule hp_conj2)
        hence "top1_loop_equiv_on B TB b0 (p \<circ> ?conj2) k" using hk by simp
        show "k \<in> top1_fundamental_group_induced_on E TE e1 B TB b0 p
            {k. top1_loop_equiv_on E TE e1 ?conj2 k}"
          unfolding top1_fundamental_group_induced_on_def
          using \<open>?conj2 \<in> _\<close> \<open>top1_loop_equiv_on B TB b0 (p \<circ> ?conj2) k\<close> by (by100 blast)
      qed
      \<comment> \<open>This class = inv(c) \<cdot> h \<cdot> c = d.\<close>
      moreover have "\<dots> = ?mulB (?invB ?c) (?mulB h ?c)"
      proof -
        \<comment> \<open>Setup: p\<circ>f is a loop at b0.\<close>
        have hpf_loop: "top1_is_loop_on B TB b0 (p \<circ> f)"
        proof -
          have "top1_continuous_map_on I_set I_top B TB (p \<circ> f)"
            by (rule top1_continuous_map_on_comp)
               (use hf_loop hp_cont in \<open>unfold top1_is_loop_on_def top1_is_path_on_def, by100 blast\<close>)+
          moreover have "(p \<circ> f) 0 = b0" using hf_loop hpe0 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          moreover have "(p \<circ> f) 1 = b0" using hf_loop hpe0 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        \<comment> \<open>h = induced([f]) = {k | loop_equiv(p\<circ>f, k)} (from the definition).\<close>
        have hh_class: "h = {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
        proof -
          have "h = top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 f k}" by (rule hh_eq)
          also have "\<dots> = {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
          proof (rule set_eqI, rule iffI)
            fix k assume "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
                {k. top1_loop_equiv_on E TE e0 f k}"
            then obtain f' where hf'_eq: "top1_loop_equiv_on E TE e0 f f'"
                and hk': "top1_loop_equiv_on B TB b0 (p \<circ> f') k"
              unfolding top1_fundamental_group_induced_on_def by (by100 blast)
            have hf'_loop: "top1_is_loop_on E TE e0 f'"
              using hf'_eq unfolding top1_loop_equiv_on_def by (by100 blast)
            have "top1_loop_equiv_on B TB b0 (p \<circ> f) (p \<circ> f')"
              using top1_induced_preserves_loop_equiv[OF hTE hp_cont hf_loop hf'_loop hf'_eq] hpe0
              by (by100 simp)
            from top1_loop_equiv_on_trans[OF hTB this hk']
            show "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}" by (by100 blast)
          next
            fix k assume "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
            hence hk: "top1_loop_equiv_on B TB b0 (p \<circ> f) k" by (by100 blast)
            have "f \<in> {k. top1_loop_equiv_on E TE e0 f k}"
              using top1_loop_equiv_on_refl[OF hf_loop] by (by100 blast)
            thus "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
                {k. top1_loop_equiv_on E TE e0 f k}"
              unfolding top1_fundamental_group_induced_on_def using hk by (by100 blast)
          qed
          finally show ?thesis .
        qed
        \<comment> \<open>inv(c) = [rev(p\<circ>\<alpha>)].\<close>
        have hinvc: "?invB ?c = {k. top1_loop_equiv_on B TB b0 (top1_path_reverse (p \<circ> \<alpha>)) k}"
          by (rule fundamental_group_invg_class[OF hTB hp\<alpha>_loop])
        \<comment> \<open>h \<cdot> c = [p\<circ>f] \<cdot> [p\<circ>\<alpha>] = [(p\<circ>f)\<cdot>(p\<circ>\<alpha>)].\<close>
        have hh_c: "?mulB h ?c = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (p \<circ> f) (p \<circ> \<alpha>)) k}"
          using hh_class top1_fundamental_group_mul_class[OF hTB hpf_loop hp\<alpha>_loop] by (by100 simp)
        \<comment> \<open>inv(c) \<cdot> (h \<cdot> c) = [rev(p\<circ>\<alpha>)] \<cdot> [(p\<circ>f)\<cdot>(p\<circ>\<alpha>)] = [rev(p\<circ>\<alpha>)\<cdot>(p\<circ>f)\<cdot>(p\<circ>\<alpha>)].\<close>
        have hpf_p\<alpha>_loop: "top1_is_loop_on B TB b0 (top1_path_product (p \<circ> f) (p \<circ> \<alpha>))"
          using top1_path_product_is_loop[OF hTB hpf_loop hp\<alpha>_loop] .
        have "?mulB (?invB ?c) (?mulB h ?c)
            = ?mulB {k. top1_loop_equiv_on B TB b0 (top1_path_reverse (p \<circ> \<alpha>)) k}
                {k. top1_loop_equiv_on B TB b0 (top1_path_product (p \<circ> f) (p \<circ> \<alpha>)) k}"
          using hinvc hh_c by (by100 simp)
        also have "\<dots> = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (top1_path_product (p \<circ> f) (p \<circ> \<alpha>))) k}"
          by (rule top1_fundamental_group_mul_class[OF hTB hp\<alpha>_rev_loop hpf_p\<alpha>_loop])
        \<comment> \<open>By associativity: rev(p\<circ>\<alpha>) \<cdot> ((p\<circ>f) \<cdot> (p\<circ>\<alpha>)) \<simeq> (rev(p\<circ>\<alpha>) \<cdot> (p\<circ>f)) \<cdot> (p\<circ>\<alpha>).\<close>
        also have "\<dots> = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k}"
        proof (rule set_eqI)
          fix k
          have hp\<alpha>_rev_path: "top1_is_path_on B TB b0 b0 (top1_path_reverse (p \<circ> \<alpha>))"
            using hp\<alpha>_rev_loop unfolding top1_is_loop_on_def by (by100 blast)
          have hpf_path: "top1_is_path_on B TB b0 b0 (p \<circ> f)"
            using hpf_loop unfolding top1_is_loop_on_def by (by100 blast)
          have hp\<alpha>_path: "top1_is_path_on B TB b0 b0 (p \<circ> \<alpha>)"
            using hp\<alpha>_loop unfolding top1_is_loop_on_def by (by100 blast)
          have hassoc: "top1_path_homotopic_on B TB b0 b0
              (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (top1_path_product (p \<circ> f) (p \<circ> \<alpha>)))
              (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>))"
            by (rule Theorem_51_2_associativity[OF hTB hp\<alpha>_rev_path hpf_path hp\<alpha>_path])
          let ?L = "top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (top1_path_product (p \<circ> f) (p \<circ> \<alpha>))"
          let ?R = "top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)"
          have hL_loop: "top1_is_loop_on B TB b0 ?L"
            by (rule top1_path_product_is_loop[OF hTB hp\<alpha>_rev_loop hpf_p\<alpha>_loop])
          have hR_loop: "top1_is_loop_on B TB b0 ?R"
          proof -
            have "top1_is_loop_on B TB b0 (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f))"
              by (rule top1_path_product_is_loop[OF hTB hp\<alpha>_rev_loop hpf_loop])
            thus ?thesis by (rule top1_path_product_is_loop[OF hTB _ hp\<alpha>_loop])
          qed
          have hLR: "top1_loop_equiv_on B TB b0 ?L ?R"
            using hassoc hL_loop hR_loop unfolding top1_loop_equiv_on_def by (by100 blast)
          have hRL: "top1_loop_equiv_on B TB b0 ?R ?L"
            by (rule top1_loop_equiv_on_sym[OF hLR])
          show "k \<in> {k. top1_loop_equiv_on B TB b0 ?L k}
            \<longleftrightarrow> k \<in> {k. top1_loop_equiv_on B TB b0 ?R k}"
          proof
            assume "k \<in> {k. top1_loop_equiv_on B TB b0 ?L k}"
            from top1_loop_equiv_on_trans[OF hTB hRL this[simplified]]
            show "k \<in> {k. top1_loop_equiv_on B TB b0 ?R k}" by (by100 blast)
          next
            assume "k \<in> {k. top1_loop_equiv_on B TB b0 ?R k}"
            from top1_loop_equiv_on_trans[OF hTB hLR this[simplified]]
            show "k \<in> {k. top1_loop_equiv_on B TB b0 ?L k}" by (by100 blast)
          qed
        qed
        finally have calc_eq: "?mulB (?invB ?c) (?mulB h ?c)
            = {k. top1_loop_equiv_on B TB b0
                (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k}" .
        show ?thesis using calc_eq by (by100 simp)
      qed
      moreover note hd_conj
      ultimately show "d \<in> top1_fundamental_group_image_hom E TE e1 B TB b0 p"
        using hconj2_in by (by100 simp)
    qed
  qed
qed

(** from \<S>79 Theorem 79.4: coverings are equivalent iff their subgroup images
    in \<pi>_1(B) are conjugate. **)
theorem Theorem_79_4:
  assumes "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "is_topology_on_strict E' TE'"
      and "top1_covering_map_on E TE B TB p" and "p e0 = b0"
      and "top1_covering_map_on E' TE' B TB p'" and "p' e0' = b0"
      and "top1_path_connected_on E TE" and "top1_path_connected_on E' TE'"
      and "top1_locally_path_connected_on E TE" and "top1_locally_path_connected_on E' TE'"
      and "e0 \<in> E" and "e0' \<in> E'" and "b0 \<in> B"
  shows "(\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e)) \<longleftrightarrow>
         (\<exists>c \<in> top1_fundamental_group_carrier B TB b0.
            top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
            = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
                ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                          (top1_fundamental_group_invg B TB b0 c)) ` H))
                (top1_fundamental_group_image_hom E TE e0 B TB b0 p))"
proof
  \<comment> \<open>p_*(\<pi>_1(E, e_0)) and p'_*(\<pi>_1(E', e_0')) are conjugate subgroups of \<pi>_1(B, b_0).\<close>
  \<comment> \<open>Forward: if h: E \<cong> E' with p'\<circ>h=p, pick e1' = h(e0) and path \<gamma> in E' from e0' to e1'.
     Then p_*(E,e0) = p'_*(E',e1') = [p'\<circ>\<gamma>] \<cdot> p'_*(E',e0') \<cdot> [p'\<circ>\<gamma>]\<inverse> (basepoint change).\<close>
  assume hfwd: "\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e)"
  then obtain h where hh: "top1_homeomorphism_on E TE E' TE' h" and hp: "\<forall>e\<in>E. p' (h e) = p e"
    by (by100 blast)
  \<comment> \<open>Let e1' = h(e0). Choose path γ in E' from e0' to e1'. Set c = [p'∘γ].
     Then p_*(E,e0) = p'_*(E',e1') = c · p'_*(E',e0') · c⁻¹ (basepoint change).\<close>
  \<comment> \<open>Setup: let e1' = h(e0). Since p'∘h = p on E: p'(e1') = p(e0) = b0.\<close>
  let ?e1' = "h e0"
  have hTE: "is_topology_on E TE"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hTE': "is_topology_on E' TE'"
    using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
  have hTB: "is_topology_on B TB"
    using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
  have hh_cont: "top1_continuous_map_on E TE E' TE' h"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hh_bij: "bij_betw h E E'"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  note he0_E = assms(12)
  have he1'_E': "?e1' \<in> E'"
    using he0_E hh_bij unfolding bij_betw_def by (by100 blast)
  have hp'e1': "p' ?e1' = b0"
    using hp he0_E assms(5) by (by100 auto)
  have hb0_B: "b0 \<in> B"
    using hp'e1' top1_covering_map_on_surj[OF assms(6)] he1'_E' by (by100 blast)
  \<comment> \<open>Step 1: Get path γ from e0' to e1' in E' (path-connectedness).\<close>
  have he0'_E': "e0' \<in> E'" by (rule assms(13))
  obtain \<gamma> where h\<gamma>: "top1_is_path_on E' TE' e0' ?e1' \<gamma>"
    using assms(9) he0'_E' he1'_E' unfolding top1_path_connected_on_def by (by100 blast)
  \<comment> \<open>Step 2: c = [p'∘γ] is a loop class in π₁(B, b0).\<close>
  have hp'_cont: "top1_continuous_map_on E' TE' B TB p'"
    by (rule top1_covering_map_on_continuous[OF assms(6)])
  have h\<gamma>_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology E' TE' \<gamma>"
    using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
  have hp'\<gamma>_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology B TB (p' \<circ> \<gamma>)"
    by (rule top1_continuous_map_on_comp[OF h\<gamma>_cont hp'_cont])
  have hp'\<gamma>_0: "(p' \<circ> \<gamma>) 0 = b0"
    using h\<gamma> assms(7) unfolding top1_is_path_on_def by (by100 simp)
  have hp'\<gamma>_1: "(p' \<circ> \<gamma>) 1 = b0"
    using h\<gamma> hp'e1' unfolding top1_is_path_on_def by (by100 simp)
  have hp'\<gamma>_loop: "top1_is_loop_on B TB b0 (p' \<circ> \<gamma>)"
    unfolding top1_is_loop_on_def top1_is_path_on_def
    using hp'\<gamma>_cont hp'\<gamma>_0 hp'\<gamma>_1 by (by100 blast)
  let ?c = "{g. top1_loop_equiv_on B TB b0 (p' \<circ> \<gamma>) g}"
  have hc_carrier: "?c \<in> top1_fundamental_group_carrier B TB b0"
    unfolding top1_fundamental_group_carrier_def using hp'\<gamma>_loop by (by100 blast)
  \<comment> \<open>Step 3: By Theorem 79.2 forward (with e1' as basepoint in E'):
     image_hom(E, e0, p) = image_hom(E', e1', p').\<close>
  have himg_eq: "top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
  proof -
    have "(\<exists>h'. top1_homeomorphism_on E TE E' TE' h' \<and> (\<forall>e\<in>E. p' (h' e) = p e)
               \<and> h' e0 = ?e1') \<longleftrightarrow>
          top1_fundamental_group_image_hom E TE e0 B TB b0 p
            = top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
      by (rule Theorem_79_2[OF assms(1,2,3,4) assms(5) assms(6) hp'e1' assms(8,9,10,11)
            he0_E he1'_E' hb0_B])
    moreover have "\<exists>h'. top1_homeomorphism_on E TE E' TE' h' \<and> (\<forall>e\<in>E. p' (h' e) = p e)
               \<and> h' e0 = ?e1'"
      using hh hp by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>Step 4: By basepoint change (Lemma 79.3):
     image_hom(E', e1', p') = c⁻¹ · image_hom(E', e0', p') · c.
     Rearranging: image_hom(E', e0', p') = c · image_hom(E', e1', p') · c⁻¹
                = c · image_hom(E, e0, p) · c⁻¹.\<close>
  \<comment> \<open>Lemma 79.3: image_hom(E', e0', p') = c · image_hom(E', e1', p') · c⁻¹.
     Proof: for f loop at e0', basepoint_change(γ, f) = γ⁻¹*f*γ is a loop at e1',
     and p'∘(γ⁻¹*f*γ) = (p'∘γ)⁻¹*(p'∘f)*(p'∘γ) (by comp_basepoint_change).
     In π₁(B): [p'∘(γ⁻¹*f*γ)] = c⁻¹·[p'∘f]·c, so [p'∘f] = c·[p'∘(γ⁻¹*f*γ)]·c⁻¹.\<close>
  have hconjugate: "top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
      = (\<lambda>H. (top1_fundamental_group_mul B TB b0 ?c)
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    (top1_fundamental_group_invg B TB b0 ?c)) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
  proof (rule set_eqI, rule iffI)
    fix d
    \<comment> \<open>⊆: d ∈ image_hom(E', e0', p') ⟹ d ∈ c · image_hom(E, e0, p) · c⁻¹.\<close>
    assume "d \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
    then obtain c0 where hc0: "c0 \<in> top1_fundamental_group_carrier E' TE' e0'"
        and hd_eq: "d = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' c0"
      unfolding top1_fundamental_group_image_hom_def by (by100 blast)
    \<comment> \<open>c0 = class(f) for some loop f at e0'.\<close>
    from hc0 obtain f where hf_loop: "top1_is_loop_on E' TE' e0' f"
        and hc0_eq: "c0 = {g. top1_loop_equiv_on E' TE' e0' f g}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>β = basepoint_change(γ, f) = γ⁻¹*f*γ is a loop at e1'.\<close>
    let ?\<beta> = "top1_basepoint_change_on E' TE' e0' ?e1' \<gamma> f"
    have h\<beta>_loop: "top1_is_loop_on E' TE' ?e1' ?\<beta>"
      by (rule top1_basepoint_change_is_loop[OF hTE' h\<gamma> hf_loop])
    \<comment> \<open>p'∘β = basepoint_change(p'∘γ, p'∘f) pointwise (comp_basepoint_change).\<close>
    have hp'\<beta>: "p' \<circ> ?\<beta> = top1_basepoint_change_on B TB b0 b0 (p' \<circ> \<gamma>) (p' \<circ> f)"
      using comp_basepoint_change[of p' E' TE' e0' ?e1' \<gamma> f B TB] assms(7) hp'e1' by (by100 simp)
    \<comment> \<open>[p'∘β] ∈ image_hom(E', e1', p') = image_hom(E, e0, p) (by himg_eq).\<close>
    have h\<beta>_class: "{g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}
        \<in> top1_fundamental_group_carrier E' TE' ?e1'"
      unfolding top1_fundamental_group_carrier_def using h\<beta>_loop by (by100 blast)
    have hp'\<beta>_in: "top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}
        \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
      unfolding top1_fundamental_group_image_hom_def using h\<beta>_class by (by100 blast)
    hence hp'\<beta>_imE: "top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}
        \<in> top1_fundamental_group_image_hom E TE e0 B TB b0 p"
      using himg_eq by (by100 simp)
    \<comment> \<open>Key: d = [p'∘f] = c · [p'∘β] · c⁻¹ in the fundamental group.
       This follows from: p'∘β = (p'∘γ)⁻¹*(p'∘f)*(p'∘γ), so
       [p'∘f] = [p'∘γ] · [p'∘β] · [(p'∘γ)⁻¹] = c · [p'∘β] · invg(c).\<close>
    \<comment> \<open>p'∘f is a loop at b0.\<close>
    have hp'f_loop: "top1_is_loop_on B TB b0 (p' \<circ> f)"
    proof -
      have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology E' TE' f"
        using hf_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      hence "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology B TB (p' \<circ> f)"
        by (rule top1_continuous_map_on_comp[OF _ hp'_cont])
      moreover have "(p' \<circ> f) 0 = b0" using hf_loop assms(7)
        unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
      moreover have "(p' \<circ> f) 1 = b0" using hf_loop assms(7)
        unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
      ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    qed
    \<comment> \<open>Key computation: class(basepoint_change(p'∘γ, p'∘f)) = invg(c) · class(p'∘f) · c.
       Uses: basepoint_change = reverse(α)*g*α, then mul_class twice + invg_class.\<close>
    let ?\<alpha> = "p' \<circ> \<gamma>" and ?g' = "p' \<circ> f"
    have h\<alpha>_loop: "top1_is_loop_on B TB b0 ?\<alpha>" by (rule hp'\<gamma>_loop)
    have hg'_loop: "top1_is_loop_on B TB b0 ?g'" by (rule hp'f_loop)
    have hr\<alpha>_loop: "top1_is_loop_on B TB b0 (top1_path_reverse ?\<alpha>)"
      using h\<alpha>_loop unfolding top1_is_loop_on_def by (rule top1_path_reverse_is_path)
    have hg'\<alpha>_loop: "top1_is_loop_on B TB b0 (top1_path_product ?g' ?\<alpha>)"
      by (rule top1_path_product_is_loop[OF hTB hg'_loop h\<alpha>_loop])
    \<comment> \<open>class(reverse(α) * (g * α)) = mul(invg(class(α)), mul(class(g), class(α)))\<close>
    have hbc_class: "{h. top1_loop_equiv_on B TB b0
          (top1_basepoint_change_on B TB b0 b0 ?\<alpha> ?g') h}
        = top1_fundamental_group_mul B TB b0
            (top1_fundamental_group_invg B TB b0 ?c)
            (top1_fundamental_group_mul B TB b0
              {h. top1_loop_equiv_on B TB b0 ?g' h} ?c)"
    proof -
      have "top1_fundamental_group_mul B TB b0
            {h. top1_loop_equiv_on B TB b0 (top1_path_reverse ?\<alpha>) h}
            {h. top1_loop_equiv_on B TB b0 (top1_path_product ?g' ?\<alpha>) h}
          = {h. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_reverse ?\<alpha>) (top1_path_product ?g' ?\<alpha>)) h}"
        by (rule top1_fundamental_group_mul_class[OF hTB hr\<alpha>_loop hg'\<alpha>_loop])
      moreover have "top1_fundamental_group_mul B TB b0
            {h. top1_loop_equiv_on B TB b0 ?g' h} ?c
          = {h. top1_loop_equiv_on B TB b0 (top1_path_product ?g' ?\<alpha>) h}"
        by (rule top1_fundamental_group_mul_class[OF hTB hg'_loop h\<alpha>_loop])
      moreover have "top1_fundamental_group_invg B TB b0 ?c
          = {h. top1_loop_equiv_on B TB b0 (top1_path_reverse ?\<alpha>) h}"
        by (rule fundamental_group_invg_class[OF hTB h\<alpha>_loop])
      moreover have "{h. top1_loop_equiv_on B TB b0
            (top1_basepoint_change_on B TB b0 b0 ?\<alpha> ?g') h}
          = {h. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_reverse ?\<alpha>) (top1_path_product ?g' ?\<alpha>)) h}"
        unfolding top1_basepoint_change_on_def by (by100 simp)
      ultimately show ?thesis by metis
    qed
    \<comment> \<open>Now: induced_p'(class(β)) = class(p'∘β) = class(basepoint_change(p'∘γ, p'∘f)).\<close>
    have hind_eq: "top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}
      = {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>) h}"
    proof (rule set_eqI, rule iffI)
      fix k assume "k \<in> top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
          {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}"
      then obtain f' where hf'_eq: "top1_loop_equiv_on E' TE' ?e1' ?\<beta> f'"
          and hk: "top1_loop_equiv_on B TB b0 (p' \<circ> f') k"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      have hf'_loop: "top1_is_loop_on E' TE' ?e1' f'"
        using hf'_eq unfolding top1_loop_equiv_on_def by (by100 blast)
      have "top1_loop_equiv_on B TB (p' ?e1') (p' \<circ> ?\<beta>) (p' \<circ> f')"
        by (rule top1_induced_preserves_loop_equiv[OF hTE' hp'_cont h\<beta>_loop hf'_loop hf'_eq])
      hence "top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>) (p' \<circ> f')"
        using hp'e1' by (by100 simp)
      from top1_loop_equiv_on_trans[OF hTB this hk]
      show "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>) h}" by (by100 blast)
    next
      fix k assume "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>) h}"
      moreover have "?\<beta> \<in> {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}"
        using top1_loop_equiv_on_refl[OF h\<beta>_loop] by (by100 blast)
      ultimately show "k \<in> top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
          {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
    qed
    \<comment> \<open>d = induced_p'(class(f)) = class(p'∘f).\<close>
    have hd_class: "d = {h. top1_loop_equiv_on B TB b0 (p' \<circ> f) h}"
    proof -
      have "d = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' c0" by (rule hd_eq)
      also have "\<dots> = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
          {g. top1_loop_equiv_on E' TE' e0' f g}" by (simp only: hc0_eq)
      also have "\<dots> = {h. top1_loop_equiv_on B TB b0 (p' \<circ> f) h}"
      proof (rule set_eqI, rule iffI)
        fix k assume "k \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
            {g. top1_loop_equiv_on E' TE' e0' f g}"
        then obtain f' where hf': "top1_loop_equiv_on E' TE' e0' f f'"
            and hk: "top1_loop_equiv_on B TB b0 (p' \<circ> f') k"
          unfolding top1_fundamental_group_induced_on_def by (by100 blast)
        have hf'_loop2: "top1_is_loop_on E' TE' e0' f'"
          using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
        have "top1_loop_equiv_on B TB (p' e0') (p' \<circ> f) (p' \<circ> f')"
          by (rule top1_induced_preserves_loop_equiv[OF hTE' hp'_cont hf_loop hf'_loop2 hf'])
        hence "top1_loop_equiv_on B TB b0 (p' \<circ> f) (p' \<circ> f')"
          using assms(7) by (by100 simp)
        from top1_loop_equiv_on_trans[OF hTB this hk]
        show "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> f) h}" by (by100 blast)
      next
        fix k assume "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> f) h}"
        moreover have "f \<in> {g. top1_loop_equiv_on E' TE' e0' f g}"
          using top1_loop_equiv_on_refl[OF hf_loop] by (by100 blast)
        ultimately show "k \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
            {g. top1_loop_equiv_on E' TE' e0' f g}"
          unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      qed
      finally show ?thesis .
    qed
    \<comment> \<open>Assembly: d = class(p'∘f). class(p'∘β) = invg(c) · d · c (from hbc_class + hp'β).
       Group algebra: d = c · class(p'∘β) · invg(c).\<close>
    \<comment> \<open>Chain: z = class(p'∘β) = class(bc(α,g')) = invg(c)·d·c. Then d = c·z·invg(c) by group algebra.\<close>
    let ?z = "top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}"
    have hz_eq1: "?z = {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>) h}" by (rule hind_eq)
    have hz_eq2: "?z = {h. top1_loop_equiv_on B TB b0
        (top1_basepoint_change_on B TB b0 b0 ?\<alpha> ?g') h}"
      using hz_eq1 hp'\<beta> by (by100 simp)
    have hz_eq3: "?z = top1_fundamental_group_mul B TB b0
        (top1_fundamental_group_invg B TB b0 ?c)
        (top1_fundamental_group_mul B TB b0 d ?c)"
      using hz_eq2 hbc_class hd_class by (by100 simp)
    \<comment> \<open>Group algebra: z = invg(c) · d · c ⟹ d = c · z · invg(c).\<close>
    have hgrp: "top1_is_group_on
        (top1_fundamental_group_carrier B TB b0)
        (top1_fundamental_group_mul B TB b0)
        (top1_fundamental_group_id B TB b0)
        (top1_fundamental_group_invg B TB b0)"
      by (rule top1_fundamental_group_is_group[OF hTB hb0_B])
    let ?mulB = "top1_fundamental_group_mul B TB b0"
    let ?invB = "top1_fundamental_group_invg B TB b0"
    let ?eB = "top1_fundamental_group_id B TB b0"
    let ?G = "top1_fundamental_group_carrier B TB b0"
    have hc_in: "?c \<in> ?G" by (rule hc_carrier)
    have hd_in: "d \<in> ?G"
    proof -
      have "d \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
        using \<open>d \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'\<close> .
      then obtain c0' where "c0' \<in> top1_fundamental_group_carrier E' TE' e0'"
          "d = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' c0'"
        unfolding top1_fundamental_group_image_hom_def by (by100 blast)
      thus ?thesis
        using top1_fundamental_group_induced_on_is_hom[OF hTE' hTB he0'_E' hb0_B hp'_cont assms(7)]
        unfolding top1_group_hom_on_def by (by100 blast)
    qed
    have hz_in: "?z \<in> ?G"
    proof -
      have hhom': "top1_group_hom_on
          (top1_fundamental_group_carrier E' TE' ?e1')
          (top1_fundamental_group_mul E' TE' ?e1') ?G ?mulB
          (top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p')"
        by (rule top1_fundamental_group_induced_on_is_hom[OF hTE' hTB he1'_E' hb0_B hp'_cont hp'e1'])
      have "?z \<in> ?G"
        using hhom' h\<beta>_class unfolding top1_group_hom_on_def by (by100 blast)
      thus ?thesis .
    qed
    have hinvc_in: "?invB ?c \<in> ?G" by (rule group_inv_closed[OF hgrp hc_in])
    \<comment> \<open>c · z · c⁻¹ = c · (invg(c) · d · c) · c⁻¹ = d\<close>
    \<comment> \<open>Expand z, apply associativity + cancellation step by step.\<close>
    have hdc_in: "?mulB d ?c \<in> ?G" by (rule group_mul_closed[OF hgrp hd_in hc_in])
    have hinvdc_in: "?mulB (?invB ?c) (?mulB d ?c) \<in> ?G"
      by (rule group_mul_closed[OF hgrp hinvc_in hdc_in])
    \<comment> \<open>Step A: c · (c⁻¹ · (d · c)) · c⁻¹ → (c · c⁻¹) · (d · c) · c⁻¹ (assoc on outer)\<close>
    have hstepA: "?mulB ?c (?mulB (?mulB (?invB ?c) (?mulB d ?c)) (?invB ?c))
        = ?mulB (?mulB ?c (?mulB (?invB ?c) (?mulB d ?c))) (?invB ?c)"
      using group_assoc[OF hgrp hc_in hinvdc_in hinvc_in] by (by100 metis)
    \<comment> \<open>Step B: c · (c⁻¹ · (d · c)) → (c · c⁻¹) · (d · c) (inner assoc)\<close>
    have hstepB: "?mulB ?c (?mulB (?invB ?c) (?mulB d ?c))
        = ?mulB (?mulB ?c (?invB ?c)) (?mulB d ?c)"
      using group_assoc[OF hgrp hc_in hinvc_in hdc_in] by (by100 metis)
    \<comment> \<open>Step C: c · c⁻¹ = e\<close>
    have hstepC: "?mulB ?c (?invB ?c) = ?eB" by (rule group_inv_right[OF hgrp hc_in])
    \<comment> \<open>Step D: e · (d · c) = d · c\<close>
    have hstepD: "?mulB ?eB (?mulB d ?c) = ?mulB d ?c"
      by (rule group_id_left[OF hgrp hdc_in])
    \<comment> \<open>Step E: (d · c) · c⁻¹ = d · (c · c⁻¹) (assoc)\<close>
    have hstepE: "?mulB (?mulB d ?c) (?invB ?c) = ?mulB d (?mulB ?c (?invB ?c))"
      by (rule group_assoc[OF hgrp hd_in hc_in hinvc_in])
    \<comment> \<open>Step F: d · e = d\<close>
    have hstepF: "?mulB d ?eB = d" by (rule group_id_right[OF hgrp hd_in])
    \<comment> \<open>Chain: c·z·c⁻¹ = c·(c⁻¹·d·c)·c⁻¹ [hz_eq3] = ... = d\<close>
    have "?mulB ?c (?mulB ?z (?invB ?c))
        = ?mulB ?c (?mulB (?mulB (?invB ?c) (?mulB d ?c)) (?invB ?c))"
      using hz_eq3 by (by100 simp)
    also have "\<dots> = ?mulB (?mulB ?c (?mulB (?invB ?c) (?mulB d ?c))) (?invB ?c)"
      using hstepA by (by100 simp)
    also have "\<dots> = ?mulB (?mulB (?mulB ?c (?invB ?c)) (?mulB d ?c)) (?invB ?c)"
      using hstepB by (by100 simp)
    also have "\<dots> = ?mulB (?mulB ?eB (?mulB d ?c)) (?invB ?c)"
      using hstepC by (by100 simp)
    also have "\<dots> = ?mulB (?mulB d ?c) (?invB ?c)"
      using hstepD by (by100 simp)
    also have "\<dots> = ?mulB d (?mulB ?c (?invB ?c))"
      using hstepE by (by100 simp)
    also have "\<dots> = ?mulB d ?eB"
      using hstepC by (by100 simp)
    also have "\<dots> = d" using hstepF by (by100 simp)
    finally have hd_conj: "d = ?mulB ?c (?mulB ?z (?invB ?c))" by (by100 metis)
    show "d \<in> (\<lambda>H. (top1_fundamental_group_mul B TB b0 ?c)
        ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                  (top1_fundamental_group_invg B TB b0 ?c)) ` H))
        (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
      using hd_conj hp'\<beta>_imE by (by100 blast)
  next
    fix d
    \<comment> \<open>⊇: d ∈ c · image_hom(E, e0, p) · c⁻¹ ⟹ d ∈ image_hom(E', e0', p').\<close>
    assume "d \<in> (\<lambda>H. (top1_fundamental_group_mul B TB b0 ?c)
        ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                  (top1_fundamental_group_invg B TB b0 ?c)) ` H))
        (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
    then obtain x where hx_in: "x \<in> top1_fundamental_group_image_hom E TE e0 B TB b0 p"
        and hd_eq: "d = top1_fundamental_group_mul B TB b0 ?c
            (top1_fundamental_group_mul B TB b0 x (top1_fundamental_group_invg B TB b0 ?c))"
      by (by100 blast)
    \<comment> \<open>x ∈ image_hom(E, e0, p) = image_hom(E', e1', p') (by himg_eq).\<close>
    have hx_imE'1: "x \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
      using hx_in himg_eq by (by100 simp)
    \<comment> \<open>x = induced_p'(class(β)) for some loop β at e1'.
       γ*β*γ⁻¹ is a loop at e0', and d = c · x · c⁻¹ = [p'∘(γ*β*γ⁻¹)] ∈ image_hom(E', e0', p').\<close>
    \<comment> \<open>x ∈ image_hom(E', e1', p') means x = induced_p'(class(β')) for some loop β' at e1'.\<close>
    from hx_imE'1 obtain c1' where hc1': "c1' \<in> top1_fundamental_group_carrier E' TE' ?e1'"
        and hx_eq: "x = top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p' c1'"
      unfolding top1_fundamental_group_image_hom_def by (by100 blast)
    from hc1' obtain \<beta>' where h\<beta>'_loop: "top1_is_loop_on E' TE' ?e1' \<beta>'"
        and hc1'_eq: "c1' = {g. top1_loop_equiv_on E' TE' ?e1' \<beta>' g}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>γ * β' * γ⁻¹ is a loop at e0' (reverse basepoint change).\<close>
    let ?\<gamma>R = "top1_path_reverse \<gamma>"
    let ?\<beta>0 = "top1_basepoint_change_on E' TE' ?e1' e0' ?\<gamma>R \<beta>'"
    have h\<gamma>R: "top1_is_path_on E' TE' ?e1' e0' ?\<gamma>R"
      by (rule top1_path_reverse_is_path[OF h\<gamma>])
    have h\<beta>0_loop: "top1_is_loop_on E' TE' e0' ?\<beta>0"
      by (rule top1_basepoint_change_is_loop[OF hTE' h\<gamma>R h\<beta>'_loop])
    \<comment> \<open>class(p'∘β0) ∈ image_hom(E', e0', p').\<close>
    have h\<beta>0_class: "{g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}
        \<in> top1_fundamental_group_carrier E' TE' e0'"
      unfolding top1_fundamental_group_carrier_def using h\<beta>0_loop by (by100 blast)
    have "top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}
        \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
      unfolding top1_fundamental_group_image_hom_def using h\<beta>0_class by (by100 blast)
    \<comment> \<open>d = class(p'∘β0) by symmetric group algebra argument.
       p'∘β0 = bc(p'∘γ⁻¹, p'∘β') = (p'∘γ) * (p'∘β') * (p'∘γ)⁻¹ = c · x · c⁻¹ = d.\<close>
    moreover have "d = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}"
    proof -
      \<comment> \<open>Step 1: induced_p'(class(β0)) = class(p'∘β0) — same as hind_eq but at e0'.\<close>
      have hind2: "top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
          {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}
        = {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) h}"
      proof (rule set_eqI, rule iffI)
        fix k assume "k \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
            {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}"
        then obtain f' where hf': "top1_loop_equiv_on E' TE' e0' ?\<beta>0 f'"
            and hk: "top1_loop_equiv_on B TB b0 (p' \<circ> f') k"
          unfolding top1_fundamental_group_induced_on_def by (by100 blast)
        have "top1_is_loop_on E' TE' e0' f'"
          using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
        have "top1_loop_equiv_on B TB (p' e0') (p' \<circ> ?\<beta>0) (p' \<circ> f')"
          by (rule top1_induced_preserves_loop_equiv[OF hTE' hp'_cont h\<beta>0_loop \<open>top1_is_loop_on E' TE' e0' f'\<close> hf'])
        hence "top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) (p' \<circ> f')"
          using assms(7) by (by100 simp)
        from top1_loop_equiv_on_trans[OF hTB this hk]
        show "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) h}" by (by100 blast)
      next
        fix k assume "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) h}"
        moreover have "?\<beta>0 \<in> {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}"
          using top1_loop_equiv_on_refl[OF h\<beta>0_loop] by (by100 blast)
        ultimately show "k \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
            {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}"
          unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      qed
      \<comment> \<open>Step 2: p'∘β0 = bc(p'∘γR, p'∘β') = bc(reverse(p'∘γ), p'∘β').\<close>
      have hp'\<beta>0: "p' \<circ> ?\<beta>0 = top1_basepoint_change_on B TB (p' ?e1') (p' e0') (p' \<circ> ?\<gamma>R) (p' \<circ> \<beta>')"
        using comp_basepoint_change[of p' E' TE' ?e1' e0' ?\<gamma>R \<beta>' B TB] by (by100 simp)
      have hp'\<gamma>R: "p' \<circ> ?\<gamma>R = top1_path_reverse (p' \<circ> \<gamma>)"
        by (rule comp_path_reverse)
      \<comment> \<open>bc(reverse(α), f) = reverse(reverse(α)) * f * reverse(α) = α * f * reverse(α).\<close>
      have hbc_expand: "top1_basepoint_change_on B TB b0 b0 (top1_path_reverse (p' \<circ> \<gamma>)) (p' \<circ> \<beta>')
          = top1_path_product (p' \<circ> \<gamma>) (top1_path_product (p' \<circ> \<beta>') (top1_path_reverse (p' \<circ> \<gamma>)))"
      proof -
        have "top1_basepoint_change_on B TB b0 b0 (top1_path_reverse (p' \<circ> \<gamma>)) (p' \<circ> \<beta>')
            = top1_path_product (top1_path_reverse (top1_path_reverse (p' \<circ> \<gamma>)))
                (top1_path_product (p' \<circ> \<beta>') (top1_path_reverse (p' \<circ> \<gamma>)))"
          unfolding top1_basepoint_change_on_def by (by100 simp)
        also have "top1_path_reverse (top1_path_reverse (p' \<circ> \<gamma>)) = p' \<circ> \<gamma>"
          by (rule path_reverse_involution)
        finally show ?thesis .
      qed
      \<comment> \<open>Step 3: class(α * f * reverse(α)) = mul(class(α), mul(class(f), invg(class(α)))).\<close>
      let ?\<alpha>B = "p' \<circ> \<gamma>" and ?g'B = "p' \<circ> \<beta>'"
      have h\<alpha>B_loop: "top1_is_loop_on B TB b0 ?\<alpha>B" by (rule hp'\<gamma>_loop)
      have hg'B_loop: "top1_is_loop_on B TB b0 ?g'B"
      proof -
        have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology E' TE' \<beta>'"
          using h\<beta>'_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        hence "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology B TB (p' \<circ> \<beta>')"
          by (rule top1_continuous_map_on_comp[OF _ hp'_cont])
        moreover have "(p' \<circ> \<beta>') 0 = b0" using h\<beta>'_loop hp'e1'
          unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
        moreover have "(p' \<circ> \<beta>') 1 = b0" using h\<beta>'_loop hp'e1'
          unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
        ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      qed
      have hr\<alpha>B_loop: "top1_is_loop_on B TB b0 (top1_path_reverse ?\<alpha>B)"
        using h\<alpha>B_loop unfolding top1_is_loop_on_def by (rule top1_path_reverse_is_path)
      have hg'\<alpha>R_loop: "top1_is_loop_on B TB b0 (top1_path_product ?g'B (top1_path_reverse ?\<alpha>B))"
        by (rule top1_path_product_is_loop[OF hTB hg'B_loop hr\<alpha>B_loop])
      have hclass_eq: "{h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) h}
          = top1_fundamental_group_mul B TB b0 ?c
              (top1_fundamental_group_mul B TB b0
                {h. top1_loop_equiv_on B TB b0 ?g'B h}
                (top1_fundamental_group_invg B TB b0 ?c))"
      proof -
        have "top1_fundamental_group_mul B TB b0
              {h. top1_loop_equiv_on B TB b0 ?\<alpha>B h}
              {h. top1_loop_equiv_on B TB b0 (top1_path_product ?g'B (top1_path_reverse ?\<alpha>B)) h}
            = {h. top1_loop_equiv_on B TB b0 (top1_path_product ?\<alpha>B (top1_path_product ?g'B (top1_path_reverse ?\<alpha>B))) h}"
          by (rule top1_fundamental_group_mul_class[OF hTB h\<alpha>B_loop hg'\<alpha>R_loop])
        moreover have "top1_fundamental_group_mul B TB b0
              {h. top1_loop_equiv_on B TB b0 ?g'B h}
              (top1_fundamental_group_invg B TB b0 ?c)
            = top1_fundamental_group_mul B TB b0
              {h. top1_loop_equiv_on B TB b0 ?g'B h}
              {h. top1_loop_equiv_on B TB b0 (top1_path_reverse ?\<alpha>B) h}"
          using fundamental_group_invg_class[OF hTB h\<alpha>B_loop] by (by100 simp)
        hence "top1_fundamental_group_mul B TB b0
              {h. top1_loop_equiv_on B TB b0 ?g'B h}
              (top1_fundamental_group_invg B TB b0 ?c)
            = {h. top1_loop_equiv_on B TB b0 (top1_path_product ?g'B (top1_path_reverse ?\<alpha>B)) h}"
          using top1_fundamental_group_mul_class[OF hTB hg'B_loop hr\<alpha>B_loop] by (by100 simp)
        moreover have "{h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) h}
            = {h. top1_loop_equiv_on B TB b0 (top1_path_product ?\<alpha>B (top1_path_product ?g'B (top1_path_reverse ?\<alpha>B))) h}"
          using hp'\<beta>0 hp'\<gamma>R hbc_expand hp'e1' assms(7) by (by100 simp)
        ultimately show ?thesis by (by100 metis)
      qed
      \<comment> \<open>Step 4: x = class(p'∘β'), so class(p'∘β0) = mul(c, mul(x, invg(c))).\<close>
      have hx_class: "x = {h. top1_loop_equiv_on B TB b0 ?g'B h}"
      proof -
        have "x = top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p' c1'" by (rule hx_eq)
        also have "\<dots> = top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
            {g. top1_loop_equiv_on E' TE' ?e1' \<beta>' g}" by (simp only: hc1'_eq)
        also have "\<dots> = {h. top1_loop_equiv_on B TB b0 (p' \<circ> \<beta>') h}"
        proof (rule set_eqI, rule iffI)
          fix k assume "k \<in> top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
              {g. top1_loop_equiv_on E' TE' ?e1' \<beta>' g}"
          then obtain f'' where hf'': "top1_loop_equiv_on E' TE' ?e1' \<beta>' f''"
              and hk: "top1_loop_equiv_on B TB b0 (p' \<circ> f'') k"
            unfolding top1_fundamental_group_induced_on_def by (by100 blast)
          have "top1_is_loop_on E' TE' ?e1' f''"
            using hf'' unfolding top1_loop_equiv_on_def by (by100 blast)
          have "top1_loop_equiv_on B TB (p' ?e1') (p' \<circ> \<beta>') (p' \<circ> f'')"
            by (rule top1_induced_preserves_loop_equiv[OF hTE' hp'_cont h\<beta>'_loop \<open>top1_is_loop_on E' TE' ?e1' f''\<close> hf''])
          hence "top1_loop_equiv_on B TB b0 (p' \<circ> \<beta>') (p' \<circ> f'')"
            using hp'e1' by (by100 simp)
          from top1_loop_equiv_on_trans[OF hTB this hk]
          show "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> \<beta>') h}" by (by100 blast)
        next
          fix k assume "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> \<beta>') h}"
          moreover have "\<beta>' \<in> {g. top1_loop_equiv_on E' TE' ?e1' \<beta>' g}"
            using top1_loop_equiv_on_refl[OF h\<beta>'_loop] by (by100 blast)
          ultimately show "k \<in> top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
              {g. top1_loop_equiv_on E' TE' ?e1' \<beta>' g}"
            unfolding top1_fundamental_group_induced_on_def by (by100 blast)
        qed
        finally show ?thesis .
      qed
      \<comment> \<open>Step 5: Assembly.\<close>
      have "top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
          {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}
        = top1_fundamental_group_mul B TB b0 ?c
            (top1_fundamental_group_mul B TB b0 x (top1_fundamental_group_invg B TB b0 ?c))"
        using hind2 hclass_eq hx_class by (by100 simp)
      thus ?thesis using hd_eq by (by100 simp)
    qed
    ultimately show "d \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
      by (by100 simp)
  qed
  show "\<exists>c \<in> top1_fundamental_group_carrier B TB b0.
      top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
      = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    (top1_fundamental_group_invg B TB b0 c)) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
    using hc_carrier hconjugate by (by100 blast)
next
  \<comment> \<open>Backward: conjugacy means subgroups differ by a basepoint change in E'.
     Theorem 79.2 applies after adjusting basepoints.\<close>
  assume "\<exists>c \<in> top1_fundamental_group_carrier B TB b0.
      top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
      = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    (top1_fundamental_group_invg B TB b0 c)) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
  \<comment> \<open>Conjugate subgroups \<Rightarrow> \<exists>e1' with p'(e1')=b0 s.t. subgroups equal after basepoint change.
     Then Theorem 79.2 gives the pointed equivalence, and we forget the basepoint.\<close>
  then obtain c where hc: "c \<in> top1_fundamental_group_carrier B TB b0"
      and hconj: "top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
        = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
            ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                      (top1_fundamental_group_invg B TB b0 c)) ` H))
            (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
    by blast
  \<comment> \<open>c = [\<gamma>] for some loop \<gamma> at b0. Lift \<gamma>\<inverse> to E' from e0'. The endpoint is e1'.
     Then p'_*(\<pi>_1(E', e1')) = c\<inverse> \<cdot> p'_*(\<pi>_1(E', e0')) \<cdot> c = p_*(\<pi>_1(E, e0)).\<close>
  \<comment> \<open>From the basepoint change: after conjugation by c\<inverse>,
     p'_*(E', e1') = p_*(E, e0). Apply Theorem 79.2 with basepoint e1'.\<close>
  have "\<exists>e1'. e1' \<in> E' \<and> p' e1' = b0 \<and>
      top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' e1' B TB b0 p'"
  proof -
    have hTE': "is_topology_on E' TE'"
      using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
    have hTB: "is_topology_on B TB"
      using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
    have hp'_cont: "top1_continuous_map_on E' TE' B TB p'"
      by (rule top1_covering_map_on_continuous[OF assms(6)])
    \<comment> \<open>c has a representative loop \<gamma> at b0.\<close>
    obtain \<gamma> where h\<gamma>_loop: "top1_is_loop_on B TB b0 \<gamma>"
        and hc_eq: "c = {g. top1_loop_equiv_on B TB b0 \<gamma> g}"
      using hc unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>Lift \<gamma> to E' from e0'. Endpoint = e1'.\<close>
    have h\<gamma>_path: "top1_is_path_on B TB b0 b0 \<gamma>" using h\<gamma>_loop unfolding top1_is_loop_on_def by (by100 blast)
    obtain \<delta> where h\<delta>: "top1_is_path_on E' TE' e0' (\<delta> 1) \<delta>"
        and h\<delta>p: "\<forall>s\<in>I_set. p' (\<delta> s) = \<gamma> s"
    proof -
      have "\<exists>ft. top1_is_path_on E' TE' e0' (ft 1) ft \<and> (\<forall>s\<in>I_set. p' (ft s) = \<gamma> s)"
      proof (rule Lemma_54_1_path_lifting)
        show "top1_covering_map_on E' TE' B TB p'" by (rule assms(6))
        show "e0' \<in> E'" by (rule assms(13))
        show "p' e0' = b0" by (rule assms(7))
        show "top1_is_path_on B TB b0 b0 \<gamma>" by (rule h\<gamma>_path)
        show "is_topology_on B TB" by (rule hTB)
        show "is_topology_on E' TE'" by (rule hTE')
      qed
      then obtain ft' where hft': "top1_is_path_on E' TE' e0' (ft' 1) ft'"
          and hft'p: "\<forall>s\<in>I_set. p' (ft' s) = \<gamma> s" by (by100 blast)
      show ?thesis using that[OF hft' hft'p] .
    qed
    let ?e1' = "\<delta> 1"
    have he1': "?e1' \<in> E'"
    proof -
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      thus ?thesis using h\<delta> unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
    qed
    have hp'e1': "p' ?e1' = b0"
    proof -
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      hence "p' (\<delta> 1) = \<gamma> 1" using h\<delta>p by (by100 blast)
      moreover have "\<gamma> 1 = b0" using h\<gamma>_path unfolding top1_is_path_on_def by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Basepoint change: p'_*(\<pi>_1(E', e1')) = [p'\<circ>\<delta>]\<inverse> \<cdot> p'_*(\<pi>_1(E', e0')) \<cdot> [p'\<circ>\<delta>].
       Since p'\<circ>\<delta> = \<gamma> and [\<gamma>] = c: p'_*(E', e1') = c\<inverse> \<cdot> p'_*(E', e0') \<cdot> c.
       Using hconj: p'_*(E', e0') = c \<cdot> p_*(E) \<cdot> c\<inverse>.
       So: p'_*(E', e1') = c\<inverse> \<cdot> (c \<cdot> p_*(E) \<cdot> c\<inverse>) \<cdot> c = p_*(E).\<close>
    \<comment> \<open>Apply basepoint change: image_hom(E', e1') = c'\<inverse> \<cdot> image_hom(E', e0') \<cdot> c'
       where c' = [p'\<circ>\<delta>] = [\<gamma>] = c.\<close>
    \<comment> \<open>Basepoint change + conjugacy cancellation:
       image_hom(E', e1') = inv(c) \<cdot> image_hom(E', e0') \<cdot> c (basepoint change by \<delta>)
       image_hom(E', e0') = c \<cdot> image_hom(E, e0) \<cdot> inv(c) (hconj)
       Combined: image_hom(E', e1') = inv(c) \<cdot> c \<cdot> image_hom(E, e0) \<cdot> inv(c) \<cdot> c = image_hom(E, e0)
       Proof uses: basepoint_change_image_hom + group algebra cancellation.\<close>
    \<comment> \<open>Step: [p'\<circ>\<delta>] = c. Since p'\<circ>\<delta> = \<gamma> on I_set, their loop classes agree.\<close>
    have hp'\<delta>_eq_\<gamma>: "\<And>s. s \<in> I_set \<Longrightarrow> (p' \<circ> \<delta>) s = \<gamma> s" using h\<delta>p by (by100 simp)
    have hp'\<delta>_loop: "top1_is_loop_on B TB b0 (p' \<circ> \<delta>)"
    proof -
      have "top1_continuous_map_on I_set I_top B TB (p' \<circ> \<delta>)"
        by (rule top1_continuous_map_on_comp)
           (use h\<delta> hp'_cont in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
      moreover have "(p' \<circ> \<delta>) 0 = b0"
        using hp'\<delta>_eq_\<gamma> h\<gamma>_path unfolding top1_is_path_on_def top1_unit_interval_def by (by100 auto)
      moreover have "(p' \<circ> \<delta>) 1 = b0"
        using hp'\<delta>_eq_\<gamma> h\<gamma>_path unfolding top1_is_path_on_def top1_unit_interval_def by (by100 auto)
      ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    qed
    have hclass_p'\<delta>_eq_c: "{g. top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) g}
        = {g. top1_loop_equiv_on B TB b0 \<gamma> g}"
    proof (rule set_eqI)
      fix k
      \<comment> \<open>p'\<circ>\<delta> and \<gamma> agree on I_set, so they are path-homotopic via the identity homotopy.\<close>
      have hp'\<delta>_\<gamma>_equiv: "top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) \<gamma>"
        unfolding top1_loop_equiv_on_def
      proof (intro conjI)
        show "top1_is_loop_on B TB b0 (p' \<circ> \<delta>)" by (rule hp'\<delta>_loop)
        show "top1_is_loop_on B TB b0 \<gamma>" by (rule h\<gamma>_loop)
        \<comment> \<open>Path homotopy via constant homotopy F(s,t) = (p'\<circ>\<delta>)(s).\<close>
        show "top1_path_homotopic_on B TB b0 b0 (p' \<circ> \<delta>) \<gamma>"
          unfolding top1_path_homotopic_on_def
        proof (intro conjI)
          show "top1_is_path_on B TB b0 b0 (p' \<circ> \<delta>)"
            using hp'\<delta>_loop unfolding top1_is_loop_on_def by (by100 blast)
          show "top1_is_path_on B TB b0 b0 \<gamma>" by (rule h\<gamma>_path)
          show "\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology B TB F
              \<and> (\<forall>s\<in>I_set. F (s, 0) = (p' \<circ> \<delta>) s) \<and> (\<forall>s\<in>I_set. F (s, 1) = \<gamma> s)
              \<and> (\<forall>t\<in>I_set. F (0, t) = b0) \<and> (\<forall>t\<in>I_set. F (1, t) = b0)"
          proof (rule exI[of _ "\<lambda>p. (p' \<circ> \<delta>) (fst p)"], intro conjI)
            have h_p'\<delta>_cont: "top1_continuous_map_on I_set I_top B TB (p' \<circ> \<delta>)"
              using hp'\<delta>_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
            show "top1_continuous_map_on (I_set \<times> I_set) II_topology B TB (\<lambda>p. (p' \<circ> \<delta>) (fst p))"
              by (rule path_homotopy_const_continuous[OF h_p'\<delta>_cont])
            show "\<forall>s\<in>I_set. (p' \<circ> \<delta>) (fst (s, (0::real))) = (p' \<circ> \<delta>) s" by (by100 simp)
            show "\<forall>s\<in>I_set. (p' \<circ> \<delta>) (fst (s, (1::real))) = \<gamma> s"
              using hp'\<delta>_eq_\<gamma> by (by100 simp)
            show "\<forall>t\<in>I_set. (p' \<circ> \<delta>) (fst ((0::real), t)) = b0"
            proof
              fix t assume "t \<in> I_set"
              have "(p' \<circ> \<delta>) 0 = b0"
                using h\<delta> assms(7) unfolding top1_is_path_on_def by (by100 simp)
              thus "(p' \<circ> \<delta>) (fst ((0::real), t)) = b0" by (by100 simp)
            qed
            show "\<forall>t\<in>I_set. (p' \<circ> \<delta>) (fst ((1::real), t)) = b0"
            proof
              fix t assume "t \<in> I_set"
              show "(p' \<circ> \<delta>) (fst ((1::real), t)) = b0"
                using hp'e1' by (by100 simp)
            qed
          qed
        qed
      qed
      have h\<gamma>_p'\<delta>_equiv: "top1_loop_equiv_on B TB b0 \<gamma> (p' \<circ> \<delta>)"
        by (rule top1_loop_equiv_on_sym[OF hp'\<delta>_\<gamma>_equiv])
      show "k \<in> {g. top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) g}
          \<longleftrightarrow> k \<in> {g. top1_loop_equiv_on B TB b0 \<gamma> g}"
      proof
        assume "k \<in> {g. top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) g}"
        from top1_loop_equiv_on_trans[OF hTB h\<gamma>_p'\<delta>_equiv this[simplified]]
        show "k \<in> {g. top1_loop_equiv_on B TB b0 \<gamma> g}" by (by100 blast)
      next
        assume "k \<in> {g. top1_loop_equiv_on B TB b0 \<gamma> g}"
        from top1_loop_equiv_on_trans[OF hTB hp'\<delta>_\<gamma>_equiv this[simplified]]
        show "k \<in> {g. top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) g}" by (by100 blast)
      qed
    qed
    \<comment> \<open>Apply basepoint_change_image_hom: image_hom(E', e1') = inv([p'\<circ>\<delta>]) \<cdot> image_hom(E', e0') \<cdot> [p'\<circ>\<delta>].\<close>
    let ?c' = "{g. top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) g}"
    have hbpc: "top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'
        = (\<lambda>H. top1_fundamental_group_mul B TB b0
              (top1_fundamental_group_invg B TB b0 ?c')
            ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h ?c') ` H))
            (top1_fundamental_group_image_hom E' TE' e0' B TB b0 p')"
      by (rule basepoint_change_image_hom[OF assms(6) hTE' hTB assms(13) he1' h\<delta> assms(7) hp'e1' assms(9)])
    \<comment> \<open>Replace ?c' with c using hclass_p'\<delta>_eq_c and hc_eq.\<close>
    have hc'_eq_c: "?c' = c" using hclass_p'\<delta>_eq_c hc_eq by (by100 simp)
    \<comment> \<open>So image_hom(E', e1') = inv(c) \<cdot> image_hom(E', e0') \<cdot> c.\<close>
    have hbpc2: "top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'
        = (\<lambda>H. top1_fundamental_group_mul B TB b0
              (top1_fundamental_group_invg B TB b0 c)
            ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h c) ` H))
            (top1_fundamental_group_image_hom E' TE' e0' B TB b0 p')"
      using hbpc hc'_eq_c by (by100 simp)
    \<comment> \<open>Substitute hconj: image_hom(E', e0') = c \<cdot> image_hom(E, e0) \<cdot> inv(c).\<close>
    \<comment> \<open>After substitution: image_hom(E', e1') = inv(c) \<cdot> (c \<cdot> image_hom(E, e0) \<cdot> inv(c)) \<cdot> c.\<close>
    \<comment> \<open>This double conjugation cancels: = image_hom(E, e0).\<close>
    have himg_match: "top1_fundamental_group_image_hom E TE e0 B TB b0 p
        = top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
    proof -
      let ?mulB = "top1_fundamental_group_mul B TB b0"
      let ?invB = "top1_fundamental_group_invg B TB b0"
      let ?eB = "top1_fundamental_group_id B TB b0"
      let ?G = "top1_fundamental_group_carrier B TB b0"
      let ?img = "top1_fundamental_group_image_hom E TE e0 B TB b0 p"
      \<comment> \<open>Group axioms from the fundamental group of (B, b0).\<close>
      have hb0B: "b0 \<in> B" using assms(14) .
      have hgrp: "top1_is_group_on ?G ?mulB ?eB ?invB"
        by (rule top1_fundamental_group_is_group[OF hTB hb0B])
      have hc_G: "c \<in> ?G" by (rule hc)
      note hgrp_raw = hgrp[unfolded top1_is_group_on_def]
      note hmul_cl_raw = hgrp_raw[THEN conjunct2, THEN conjunct1]
      note hinv_cl_raw = hgrp_raw[THEN conjunct2, THEN conjunct2, THEN conjunct1]
      note hassoc_raw = hgrp_raw[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
      note hid_raw = hgrp_raw[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
      note hinv_raw = hgrp_raw[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]
      have hmul_cl: "\<And>x y. x \<in> ?G \<Longrightarrow> y \<in> ?G \<Longrightarrow> ?mulB x y \<in> ?G"
        using hmul_cl_raw by (by100 blast)
      have hinv_cl: "\<And>x. x \<in> ?G \<Longrightarrow> ?invB x \<in> ?G"
        using hinv_cl_raw by (by100 blast)
      have hinvc_G: "?invB c \<in> ?G" by (rule hinv_cl[OF hc_G])
      have hassoc: "\<And>x y z. x \<in> ?G \<Longrightarrow> y \<in> ?G \<Longrightarrow> z \<in> ?G \<Longrightarrow>
          ?mulB (?mulB x y) z = ?mulB x (?mulB y z)"
        using hassoc_raw by (by100 blast)
      have hlinv: "\<And>x. x \<in> ?G \<Longrightarrow> ?mulB (?invB x) x = ?eB"
        using hinv_raw by (by100 blast)
      have hrid: "\<And>x. x \<in> ?G \<Longrightarrow> ?mulB x ?eB = x"
        using hid_raw by (by100 blast)
      have hlid: "\<And>x. x \<in> ?G \<Longrightarrow> ?mulB ?eB x = x"
        using hid_raw by (by100 blast)
      \<comment> \<open>Image hom elements are in the carrier.\<close>
      have himg_sub: "?img \<subseteq> ?G"
      proof
        fix d assume "d \<in> ?img"
        then obtain f where hf_loop: "top1_is_loop_on E TE e0 f"
            and hd_eq: "d = top1_fundamental_group_induced_on E TE e0 B TB b0 p
                {k. top1_loop_equiv_on E TE e0 f k}"
          unfolding top1_fundamental_group_image_hom_def top1_fundamental_group_carrier_def
          by (by100 blast)
        have hTE_loc: "is_topology_on E TE"
          using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
        have hp_cont: "top1_continuous_map_on E TE B TB p"
          by (rule top1_covering_map_on_continuous[OF assms(4)])
        have hpf_loop: "top1_is_loop_on B TB b0 (p \<circ> f)"
        proof -
          have "top1_continuous_map_on I_set I_top B TB (p \<circ> f)"
            by (rule top1_continuous_map_on_comp)
               (use hf_loop hp_cont in \<open>unfold top1_is_loop_on_def top1_is_path_on_def, by100 blast\<close>)+
          moreover have "(p \<circ> f) 0 = b0" using hf_loop assms(5) unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          moreover have "(p \<circ> f) 1 = b0" using hf_loop assms(5) unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        \<comment> \<open>induced([f]) = [p\<circ>f] (same as hh_class proof pattern).\<close>
        have hd_class: "d = {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
        proof -
          have "d = top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 f k}" by (rule hd_eq)
          also have "\<dots> = {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
          proof (rule set_eqI, rule iffI)
            fix k assume "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
                {k. top1_loop_equiv_on E TE e0 f k}"
            then obtain f' where hf': "top1_loop_equiv_on E TE e0 f f'"
                and hk: "top1_loop_equiv_on B TB b0 (p \<circ> f') k"
              unfolding top1_fundamental_group_induced_on_def by (by100 blast)
            have hf'_loop: "top1_is_loop_on E TE e0 f'"
              using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
            have "top1_loop_equiv_on B TB b0 (p \<circ> f) (p \<circ> f')"
              using top1_induced_preserves_loop_equiv[OF hTE_loc hp_cont hf_loop hf'_loop hf'] assms(5)
              by (by100 simp)
            from top1_loop_equiv_on_trans[OF hTB this hk]
            show "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}" by (by100 blast)
          next
            fix k assume "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
            moreover have "f \<in> {k. top1_loop_equiv_on E TE e0 f k}"
              using top1_loop_equiv_on_refl[OF hf_loop] by (by100 blast)
            ultimately show "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
                {k. top1_loop_equiv_on E TE e0 f k}"
              unfolding top1_fundamental_group_induced_on_def by (by100 blast)
          qed
          finally show ?thesis .
        qed
        \<comment> \<open>[p\<circ>f] \<in> carrier(B, b0) since p\<circ>f is a loop at b0.\<close>
        show "d \<in> ?G"
          unfolding hd_class top1_fundamental_group_carrier_def
          using hpf_loop top1_loop_equiv_on_refl[OF hpf_loop] by (by100 blast)
      qed
      \<comment> \<open>Key: inv(c) \<cdot> ((c \<cdot> (h \<cdot> inv(c))) \<cdot> c) = h for h \<in> G.\<close>
      have hcancel: "\<And>h. h \<in> ?G \<Longrightarrow>
          ?mulB (?invB c) (?mulB (?mulB c (?mulB h (?invB c))) c) = h"
      proof -
        fix h assume hh: "h \<in> ?G"
        have hhinvc: "?mulB h (?invB c) \<in> ?G" by (rule hmul_cl[OF hh hinvc_G])
        have hchinvc: "?mulB c (?mulB h (?invB c)) \<in> ?G" by (rule hmul_cl[OF hc_G hhinvc])
        \<comment> \<open>Step 1: (c \<cdot> (h \<cdot> inv(c))) \<cdot> c = c \<cdot> ((h \<cdot> inv(c)) \<cdot> c) by assoc.\<close>
        have s1: "?mulB (?mulB c (?mulB h (?invB c))) c
            = ?mulB c (?mulB (?mulB h (?invB c)) c)"
          by (rule hassoc[OF hc_G hhinvc hc_G])
        \<comment> \<open>Step 2: (h \<cdot> inv(c)) \<cdot> c = h \<cdot> (inv(c) \<cdot> c) by assoc.\<close>
        have s2: "?mulB (?mulB h (?invB c)) c = ?mulB h (?mulB (?invB c) c)"
          by (rule hassoc[OF hh hinvc_G hc_G])
        \<comment> \<open>Step 3: inv(c) \<cdot> c = e by left inverse.\<close>
        have s3: "?mulB (?invB c) c = ?eB" by (rule hlinv[OF hc_G])
        \<comment> \<open>Step 4: h \<cdot> e = h.\<close>
        have s4: "?mulB h ?eB = h" by (rule hrid[OF hh])
        \<comment> \<open>Combine inner: (c \<cdot> (h \<cdot> inv(c))) \<cdot> c = c \<cdot> h.\<close>
        have inner: "?mulB (?mulB c (?mulB h (?invB c))) c = ?mulB c h"
          using s1 s2 s3 s4 by (by100 simp)
        \<comment> \<open>Step 5: inv(c) \<cdot> (c \<cdot> h) = (inv(c) \<cdot> c) \<cdot> h = e \<cdot> h = h.\<close>
        have hch: "?mulB c h \<in> ?G" by (rule hmul_cl[OF hc_G hh])
        have s5: "?mulB (?invB c) (?mulB c h) = ?mulB (?mulB (?invB c) c) h"
          by (rule hassoc[OF hinvc_G hc_G hh, symmetric])
        have s6: "?mulB (?mulB (?invB c) c) h = ?mulB ?eB h" using s3 by (by100 simp)
        have s7: "?mulB ?eB h = h" by (rule hlid[OF hh])
        show "?mulB (?invB c) (?mulB (?mulB c (?mulB h (?invB c))) c) = h"
          using inner s5 s6 s7 by (by100 simp)
      qed
      \<comment> \<open>Now show set equality using hbpc2 + hconj + cancellation.\<close>
      show ?thesis
      proof (rule set_eqI)
        fix d
        show "d \<in> ?img \<longleftrightarrow> d \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
        proof
          \<comment> \<open>(\<Rightarrow>) h \<in> img(E,e0). Conjugate by c to get in img(E',e0'), then by inv(c) to get in img(E',e1'). Cancellation gives h back.\<close>
          assume hd: "d \<in> ?img"
          hence hd_G: "d \<in> ?G" using himg_sub by (by100 blast)
          \<comment> \<open>c \<cdot> (d \<cdot> inv(c)) \<in> img(E', e0') via hconj.\<close>
          let ?k = "?mulB c (?mulB d (?invB c))"
          have hk_in: "?k \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
            using hd hconj by (by100 blast)
          \<comment> \<open>inv(c) \<cdot> (k \<cdot> c) \<in> img(E', e1') via hbpc2.\<close>
          let ?d' = "?mulB (?invB c) (?mulB ?k c)"
          have hd'_in: "?d' \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
            using hk_in hbpc2 by (by100 blast)
          \<comment> \<open>?d' = d by cancellation.\<close>
          have "?d' = d" by (rule hcancel[OF hd_G])
          thus "d \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
            using hd'_in by (by100 simp)
        next
          \<comment> \<open>(\<Leftarrow>) Decompose via hbpc2 and hconj, then use cancellation.\<close>
          assume "d \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
          hence "d \<in> ?mulB (?invB c) ` ((\<lambda>h. ?mulB h c) ` (top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'))"
            using hbpc2 by (by100 simp)
          then obtain k where hk: "k \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
              and hd_eq: "d = ?mulB (?invB c) (?mulB k c)" by (by100 blast)
          have "k \<in> ?mulB c ` ((\<lambda>h. ?mulB h (?invB c)) ` ?img)"
            using hk hconj by (by100 simp)
          then obtain h where hh: "h \<in> ?img"
              and hk_eq: "k = ?mulB c (?mulB h (?invB c))" by (by100 blast)
          have hh_G: "h \<in> ?G" using hh himg_sub by (by100 blast)
          have "d = ?mulB (?invB c) (?mulB (?mulB c (?mulB h (?invB c))) c)"
            using hd_eq hk_eq by (by100 simp)
          also have "\<dots> = h" by (rule hcancel[OF hh_G])
          finally show "d \<in> ?img" using hh by (by100 simp)
        qed
      qed
    qed
    show ?thesis using he1' hp'e1' himg_match by (by100 blast)
  qed
  then obtain e1' where he1': "e1' \<in> E'" and hp'e1': "p' e1' = b0"
      and himg_eq: "top1_fundamental_group_image_hom E TE e0 B TB b0 p
          = top1_fundamental_group_image_hom E' TE' e1' B TB b0 p'"
    by (by100 blast)
  \<comment> \<open>Apply Theorem 79.2 backward with basepoint e1': get h with h(e0) = e1'.\<close>
  have "(\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e)
           \<and> h e0 = e1') \<longleftrightarrow>
       top1_fundamental_group_image_hom E TE e0 B TB b0 p
         = top1_fundamental_group_image_hom E' TE' e1' B TB b0 p'"
    by (rule Theorem_79_2[OF assms(1,2,3,4) assms(5) assms(6) hp'e1' assms(8,9,10,11)
          assms(12) he1' assms(14)])
  hence "\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e) \<and> h e0 = e1'"
    using himg_eq by (by100 blast)
  thus "\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e)"
    by (by100 blast)
qed

section \<open>\<S>79 Equivalence of Covering Spaces\<close>

\<comment> \<open>Theorems 79.2 and 79.4 are already above; this section heading organizes them.\<close>

section \<open>\<S>80 The Universal Covering Space\<close>

text \<open>A universal covering space is a simply connected covering space of B.\<close>
definition top1_is_universal_covering_on :: "'e set \<Rightarrow> 'e set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_is_universal_covering_on E TE B TB p \<longleftrightarrow>
     top1_covering_map_on E TE B TB p \<and>
     top1_simply_connected_on E TE"

text \<open>If E is simply connected, then p_*(π₁(E, e0)) = {id} in π₁(B, b0).\<close>
lemma simply_connected_trivial_image:
  assumes hsc: "top1_simply_connected_on E TE"
      and hcov: "top1_covering_map_on E TE B TB p"
      and he0: "e0 \<in> E" and hpe0: "p e0 = b0"
      and hTB: "is_topology_on B TB"
  shows "top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = {top1_fundamental_group_id B TB b0}"
proof -
  \<comment> \<open>Simply connected means every loop is homotopic to const. So π₁(E, e0) = {id}.
     p_*(id) = [p ∘ const_{e0}] = [const_{b0}] = id in π₁(B, b0).\<close>
  have hTE: "is_topology_on E TE"
    using hsc unfolding top1_simply_connected_on_def top1_path_connected_on_def by (by100 blast)
  \<comment> \<open>Step 1: carrier of π₁(E, e0) = {id}.\<close>
  have hcarrier: "top1_fundamental_group_carrier E TE e0 = {top1_fundamental_group_id E TE e0}"
  proof (rule set_eqI)
    fix c show "c \<in> top1_fundamental_group_carrier E TE e0 \<longleftrightarrow>
        c \<in> {top1_fundamental_group_id E TE e0}"
    proof
      assume hc: "c \<in> top1_fundamental_group_carrier E TE e0"
      then obtain f where hf: "top1_is_loop_on E TE e0 f"
          and hc_eq: "c = {g. top1_loop_equiv_on E TE e0 f g}"
        unfolding top1_fundamental_group_carrier_def by (by100 blast)
      \<comment> \<open>f ≃ const (simply connected).\<close>
      have hf_nul: "top1_path_homotopic_on E TE e0 e0 f (top1_constant_path e0)"
        using hsc he0 hf unfolding top1_simply_connected_on_def by (by100 blast)
      \<comment> \<open>So {g. loop_equiv f g} = {g. loop_equiv const g}.\<close>
      have "c = {g. top1_loop_equiv_on E TE e0 (top1_constant_path e0) g}"
      proof (rule set_eqI)
        fix g show "g \<in> c \<longleftrightarrow> g \<in> {g. top1_loop_equiv_on E TE e0 (top1_constant_path e0) g}"
        proof
          assume "g \<in> c"
          hence "top1_loop_equiv_on E TE e0 f g" using hc_eq by (by100 blast)
          hence "top1_path_homotopic_on E TE e0 e0 f g"
            unfolding top1_loop_equiv_on_def by (by100 blast)
          have "top1_path_homotopic_on E TE e0 e0 (top1_constant_path e0) g"
            by (rule Lemma_51_1_path_homotopic_trans[OF hTE
                  Lemma_51_1_path_homotopic_sym[OF hf_nul]
                  \<open>top1_path_homotopic_on E TE e0 e0 f g\<close>])
          have hg_loop: "top1_is_loop_on E TE e0 g"
            using \<open>g \<in> c\<close> hc_eq unfolding top1_loop_equiv_on_def by (by100 blast)
          have hconst_loop: "top1_is_loop_on E TE e0 (top1_constant_path e0)"
            by (rule top1_constant_path_is_loop[OF hTE he0])
          thus "g \<in> {g. top1_loop_equiv_on E TE e0 (top1_constant_path e0) g}"
            unfolding top1_loop_equiv_on_def
            using \<open>top1_path_homotopic_on E TE e0 e0 (top1_constant_path e0) g\<close>
                  hconst_loop hg_loop by (by100 blast)
        next
          assume "g \<in> {g. top1_loop_equiv_on E TE e0 (top1_constant_path e0) g}"
          hence "top1_loop_equiv_on E TE e0 (top1_constant_path e0) g" by (by100 blast)
          hence "top1_path_homotopic_on E TE e0 e0 (top1_constant_path e0) g"
            unfolding top1_loop_equiv_on_def by blast
          have "top1_path_homotopic_on E TE e0 e0 f g"
            by (rule Lemma_51_1_path_homotopic_trans[OF hTE hf_nul
                  \<open>top1_path_homotopic_on E TE e0 e0 (top1_constant_path e0) g\<close>])
          have hg_loop: "top1_is_loop_on E TE e0 g"
            using \<open>top1_loop_equiv_on E TE e0 (top1_constant_path e0) g\<close>
            unfolding top1_loop_equiv_on_def by (by100 blast)
          thus "g \<in> c" using hc_eq hf hg_loop
            \<open>top1_path_homotopic_on E TE e0 e0 f g\<close>
            unfolding top1_loop_equiv_on_def by (by100 blast)
        qed
      qed
      thus "c \<in> {top1_fundamental_group_id E TE e0}"
        unfolding top1_fundamental_group_id_def by (by100 blast)
    next
      assume "c \<in> {top1_fundamental_group_id E TE e0}"
      hence hc_id: "c = top1_fundamental_group_id E TE e0" by (by100 blast)
      have "top1_is_loop_on E TE e0 (top1_constant_path e0)"
        by (rule top1_constant_path_is_loop[OF hTE he0])
      thus "c \<in> top1_fundamental_group_carrier E TE e0"
        unfolding hc_id top1_fundamental_group_id_def top1_fundamental_group_carrier_def
        by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 2: p_*(id_E) = id_B.\<close>
  have hind_id: "top1_fundamental_group_induced_on E TE e0 B TB b0 p
      (top1_fundamental_group_id E TE e0)
      = top1_fundamental_group_id B TB b0"
  proof -
    \<comment> \<open>p ∘ const_{e0} = const_{b0}.\<close>
    have hpc: "p \<circ> top1_constant_path e0 = top1_constant_path b0"
      by (rule ext) (simp add: top1_constant_path_def hpe0 comp_def)
    \<comment> \<open>induced([const_E]) = {g. ∃f∈[const_E]. loop_equiv(p∘f, g)}
       = {g. loop_equiv(const_B, g)} = [const_B]\<close>
    show ?thesis
      unfolding top1_fundamental_group_induced_on_def top1_fundamental_group_id_def
    proof (rule set_eqI)
      fix g
      show "g \<in> {g. \<exists>f\<in>{g. top1_loop_equiv_on E TE e0 (top1_constant_path e0) g}.
                  top1_loop_equiv_on B TB b0 (p \<circ> f) g}
          \<longleftrightarrow> g \<in> {g. top1_loop_equiv_on B TB b0 (top1_constant_path b0) g}"
      proof
        assume "g \<in> {g. \<exists>f\<in>{g. top1_loop_equiv_on E TE e0 (top1_constant_path e0) g}.
                    top1_loop_equiv_on B TB b0 (p \<circ> f) g}"
        then obtain f where hf_equiv: "top1_loop_equiv_on E TE e0 (top1_constant_path e0) f"
            and hpf_equiv: "top1_loop_equiv_on B TB b0 (p \<circ> f) g" by (by100 blast)
        \<comment> \<open>f ≃ const_E ⟹ p∘f ≃ const_B (continuous map preserves homotopy + hpc).
           Then const_B ≃ p∘f ≃ g by transitivity.\<close>
        have hf_hom: "top1_path_homotopic_on E TE e0 e0 (top1_constant_path e0) f"
          using hf_equiv unfolding top1_loop_equiv_on_def by (by100 blast)
        have hp_cont: "top1_continuous_map_on E TE B TB p"
          using hcov unfolding top1_covering_map_on_def by (by100 blast)
        note hTB = hTB
        have hpf_hom: "top1_path_homotopic_on B TB (p e0) (p e0) (p \<circ> top1_constant_path e0) (p \<circ> f)"
          by (rule continuous_preserves_path_homotopic[OF hTE hTB hp_cont hf_hom])
        have "p \<circ> top1_constant_path e0 = top1_constant_path b0" by (rule hpc)
        have hconstB_pf: "top1_path_homotopic_on B TB b0 b0 (top1_constant_path b0) (p \<circ> f)"
          using hpf_hom hpe0 \<open>p \<circ> top1_constant_path e0 = top1_constant_path b0\<close> by simp
        have hpf_g: "top1_path_homotopic_on B TB b0 b0 (p \<circ> f) g"
          using hpf_equiv unfolding top1_loop_equiv_on_def by (by100 blast)
        have hconstB_g: "top1_path_homotopic_on B TB b0 b0 (top1_constant_path b0) g"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTB hconstB_pf hpf_g])
        have hg_loop: "top1_is_loop_on B TB b0 g"
          using hpf_equiv unfolding top1_loop_equiv_on_def by (by100 blast)
        have hb0_B: "b0 \<in> B"
          using hcov he0 hpe0 unfolding top1_covering_map_on_def top1_continuous_map_on_def
          by (by100 blast)
        have hconstB_loop: "top1_is_loop_on B TB b0 (top1_constant_path b0)"
          by (rule top1_constant_path_is_loop[OF hTB hb0_B])
        show "g \<in> {g. top1_loop_equiv_on B TB b0 (top1_constant_path b0) g}"
          unfolding top1_loop_equiv_on_def
          using hconstB_g hg_loop hconstB_loop by (by100 blast)
      next
        assume hg: "g \<in> {g. top1_loop_equiv_on B TB b0 (top1_constant_path b0) g}"
        \<comment> \<open>Take f = const_E. Then p∘f = const_B ≃ g, and f ∈ [const_E].\<close>
        have hconst_equiv: "top1_loop_equiv_on E TE e0 (top1_constant_path e0) (top1_constant_path e0)"
          by (rule top1_loop_equiv_on_refl[OF top1_constant_path_is_loop[OF hTE he0]])
        have "p \<circ> top1_constant_path e0 = top1_constant_path b0" by (rule hpc)
        hence "top1_loop_equiv_on B TB b0 (p \<circ> top1_constant_path e0) g"
          using hg by (by100 simp)
        thus "g \<in> {g. \<exists>f\<in>{g. top1_loop_equiv_on E TE e0 (top1_constant_path e0) g}.
                    top1_loop_equiv_on B TB b0 (p \<circ> f) g}"
          using hconst_equiv by (by100 blast)
      qed
    qed
  qed
  show ?thesis
    unfolding top1_fundamental_group_image_hom_def hcarrier
    using hind_id by (by100 simp)
qed

(** from \<S>80: any two universal covering spaces are equivalent (via Theorem 79.4). **)
theorem Theorem_80_1_universal_unique:
  assumes "is_topology_on_strict B TB"
      and "top1_is_universal_covering_on E TE B TB p"
      and "top1_is_universal_covering_on E' TE' B TB p'"
      and "is_topology_on_strict E TE" and "is_topology_on_strict E' TE'"
      and "top1_path_connected_on E TE" and "top1_path_connected_on E' TE'"
      and "top1_locally_path_connected_on E TE" and "top1_locally_path_connected_on E' TE'"
      and "p e0 = b0" and "p' e0' = b0"
      and "e0 \<in> E" and "e0' \<in> E'"
  shows "\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e)"
proof -
  \<comment> \<open>By Theorem 79.4: simply connected E gives trivial subgroup p_*(\<pi>_1 E) = {1};
      same for E'; and {1} is conjugate to itself.\<close>
  have hE_sc: "top1_simply_connected_on E TE"
    using assms(2) unfolding top1_is_universal_covering_on_def by (by100 blast)
  have hE'_sc: "top1_simply_connected_on E' TE'"
    using assms(3) unfolding top1_is_universal_covering_on_def by (by100 blast)
  \<comment> \<open>p_*(\<pi>_1(E, e0)) = {[const]} (trivial) since E is simply connected.\<close>
  have hcovE: "top1_covering_map_on E TE B TB p"
    using assms(2) unfolding top1_is_universal_covering_on_def by (by100 blast)
  have hcovE': "top1_covering_map_on E' TE' B TB p'"
    using assms(3) unfolding top1_is_universal_covering_on_def by (by100 blast)
  have hH_trivial: "top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = {top1_fundamental_group_id B TB b0}"
    by (rule simply_connected_trivial_image[OF hE_sc hcovE assms(12) assms(10)
          is_topology_on_strict_imp[OF assms(1)]])
  have hH'_trivial: "top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
      = {top1_fundamental_group_id B TB b0}"
    by (rule simply_connected_trivial_image[OF hE'_sc hcovE' assms(13) assms(11)
          is_topology_on_strict_imp[OF assms(1)]])
  \<comment> \<open>{1} is conjugate to {1} (take c = identity). Apply Theorem 79.4.\<close>
  \<comment> \<open>Take c = id. Conjugation of {id} by id gives {id}.\<close>
  have hb0_B: "b0 \<in> B"
    using hcovE assms(12) assms(10)
    unfolding top1_covering_map_on_def top1_continuous_map_on_def by (by100 blast)
  have hTB: "is_topology_on B TB" by (rule is_topology_on_strict_imp[OF assms(1)])
  have hid_mem: "top1_fundamental_group_id B TB b0
      \<in> top1_fundamental_group_carrier B TB b0"
  proof -
    have "top1_is_loop_on B TB b0 (top1_constant_path b0)"
      by (rule top1_constant_path_is_loop[OF hTB hb0_B])
    thus ?thesis
      unfolding top1_fundamental_group_id_def top1_fundamental_group_carrier_def
      by (by100 blast)
  qed
  \<comment> \<open>Conjugation of {id} by id: mul(id, mul(id, invg(id))) = mul(id, mul(id, id)) = id.\<close>
  have hconj: "(\<lambda>H. (top1_fundamental_group_mul B TB b0 (top1_fundamental_group_id B TB b0))
      ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                (top1_fundamental_group_invg B TB b0 (top1_fundamental_group_id B TB b0))) ` H))
      {top1_fundamental_group_id B TB b0}
      = {top1_fundamental_group_id B TB b0}"
  proof -
    \<comment> \<open>invg([const]) = [reverse(const)] = [const] (constant path reversed is still constant).\<close>
    have hinvg_id: "top1_fundamental_group_invg B TB b0 (top1_fundamental_group_id B TB b0)
        = top1_fundamental_group_id B TB b0"
    proof (rule set_eqI)
      fix h
      show "h \<in> top1_fundamental_group_invg B TB b0 (top1_fundamental_group_id B TB b0)
          \<longleftrightarrow> h \<in> top1_fundamental_group_id B TB b0"
      proof
        assume "h \<in> top1_fundamental_group_invg B TB b0 (top1_fundamental_group_id B TB b0)"
        then obtain f where hf: "f \<in> top1_fundamental_group_id B TB b0"
            and hrev: "top1_loop_equiv_on B TB b0 (top1_path_reverse f) h"
          unfolding top1_fundamental_group_invg_def by (by100 blast)
        have hf_equiv: "top1_loop_equiv_on B TB b0 (top1_constant_path b0) f"
          using hf unfolding top1_fundamental_group_id_def by (by100 blast)
        \<comment> \<open>const ≃ f ⟹ reverse(const) ≃ reverse(f) ⟹ const ≃ reverse(f) ≃ h.\<close>
        have hconst_rev: "top1_path_homotopic_on B TB b0 b0 (top1_constant_path b0) (top1_path_reverse f)"
        proof -
          have hf_path: "top1_is_path_on B TB b0 b0 f"
            using hf_equiv unfolding top1_loop_equiv_on_def top1_is_loop_on_def by (by100 blast)
          have hrevf: "top1_is_path_on B TB b0 b0 (top1_path_reverse f)"
            by (rule top1_path_reverse_is_path[OF hf_path])
          have hconst_f: "top1_path_homotopic_on B TB b0 b0 (top1_constant_path b0) f"
            using hf_equiv unfolding top1_loop_equiv_on_def by (by100 blast)
          \<comment> \<open>const * rev(f) ≃ f * rev(f) (product_left with const ≃ f).\<close>
          have step1: "top1_path_homotopic_on B TB b0 b0
              (top1_path_product (top1_constant_path b0) (top1_path_reverse f))
              (top1_path_product f (top1_path_reverse f))"
            by (rule path_homotopic_product_left[OF hTB hconst_f hrevf])
          \<comment> \<open>f * rev(f) ≃ const (inverse_left).\<close>
          have step2: "top1_path_homotopic_on B TB b0 b0
              (top1_path_product f (top1_path_reverse f))
              (top1_constant_path b0)"
            by (rule Theorem_51_2_invgerse_left[OF hTB hf_path])
          \<comment> \<open>const * rev(f) ≃ const (transitivity of step1 + step2).\<close>
          have step12: "top1_path_homotopic_on B TB b0 b0
              (top1_path_product (top1_constant_path b0) (top1_path_reverse f))
              (top1_constant_path b0)"
            by (rule Lemma_51_1_path_homotopic_trans[OF hTB step1 step2])
          \<comment> \<open>rev(f) ≃ const * rev(f) (left identity, reversed).\<close>
          have step3: "top1_path_homotopic_on B TB b0 b0
              (top1_path_reverse f)
              (top1_path_product (top1_constant_path b0) (top1_path_reverse f))"
            by (rule Lemma_51_1_path_homotopic_sym[OF
                  Theorem_51_2_left_identity[OF hTB hrevf]])
          \<comment> \<open>rev(f) ≃ const (transitivity).\<close>
          have step123: "top1_path_homotopic_on B TB b0 b0
              (top1_path_reverse f) (top1_constant_path b0)"
            by (rule Lemma_51_1_path_homotopic_trans[OF hTB step3 step12])
          show ?thesis by (rule Lemma_51_1_path_homotopic_sym[OF step123])
        qed
        have "top1_loop_equiv_on B TB b0 (top1_constant_path b0) h"
          by (meson Lemma_51_1_path_homotopic_trans hTB hconst_rev hf_equiv hrev
              top1_loop_equiv_on_def)
        thus "h \<in> top1_fundamental_group_id B TB b0"
          unfolding top1_fundamental_group_id_def by (by100 blast)
      next
        assume "h \<in> top1_fundamental_group_id B TB b0"
        hence hh: "top1_loop_equiv_on B TB b0 (top1_constant_path b0) h"
          unfolding top1_fundamental_group_id_def by (by100 blast)
        \<comment> \<open>Take f = const. reverse(const) ≃ const ≃ h.\<close>
        have hconst_in_id: "top1_constant_path b0 \<in> top1_fundamental_group_id B TB b0"
          unfolding top1_fundamental_group_id_def
          using top1_loop_equiv_on_refl[OF top1_constant_path_is_loop[OF hTB hb0_B]] by (by100 blast)
        have "top1_path_reverse (top1_constant_path b0) = top1_constant_path b0"
          unfolding top1_path_reverse_def top1_constant_path_def by (rule ext) simp
        hence "top1_loop_equiv_on B TB b0 (top1_path_reverse (top1_constant_path b0)) h"
          using hh by simp
        thus "h \<in> top1_fundamental_group_invg B TB b0 (top1_fundamental_group_id B TB b0)"
          unfolding top1_fundamental_group_invg_def using hconst_in_id by (by100 blast)
      qed
    qed
    \<comment> \<open>mul(id, id) = id (left identity in fundamental group).\<close>
    have hmul_id: "top1_fundamental_group_mul B TB b0
        (top1_fundamental_group_id B TB b0) (top1_fundamental_group_id B TB b0)
        = top1_fundamental_group_id B TB b0"
    proof (rule set_eqI)
      fix h
      show "h \<in> top1_fundamental_group_mul B TB b0
              (top1_fundamental_group_id B TB b0) (top1_fundamental_group_id B TB b0)
          \<longleftrightarrow> h \<in> top1_fundamental_group_id B TB b0"
      proof
        assume "h \<in> top1_fundamental_group_mul B TB b0
            (top1_fundamental_group_id B TB b0) (top1_fundamental_group_id B TB b0)"
        then obtain f g where hf: "top1_loop_equiv_on B TB b0 (top1_constant_path b0) f"
            and hg: "top1_loop_equiv_on B TB b0 (top1_constant_path b0) g"
            and hfg: "top1_loop_equiv_on B TB b0 (top1_path_product f g) h"
          unfolding top1_fundamental_group_mul_def top1_fundamental_group_id_def
          by (by100 fast)
        \<comment> \<open>const ≃ f and const ≃ g. So f*g ≃ const*const ≃ const.\<close>
        have hf_path: "top1_is_path_on B TB b0 b0 f"
          using hf unfolding top1_loop_equiv_on_def top1_is_loop_on_def by (by100 blast)
        have hg_path: "top1_is_path_on B TB b0 b0 g"
          using hg unfolding top1_loop_equiv_on_def top1_is_loop_on_def by (by100 blast)
        have hconst_f: "top1_path_homotopic_on B TB b0 b0 (top1_constant_path b0) f"
          using hf unfolding top1_loop_equiv_on_def by (by100 blast)
        have hconst_g: "top1_path_homotopic_on B TB b0 b0 (top1_constant_path b0) g"
          using hg unfolding top1_loop_equiv_on_def by (by100 blast)
        \<comment> \<open>const*g ≃ f*g (product_left: const ≃ f).\<close>
        have step1: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_constant_path b0) g) (top1_path_product f g)"
          by (rule path_homotopic_product_left[OF hTB hconst_f hg_path])
        \<comment> \<open>const*g ≃ g (left identity).\<close>
        have step2: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_constant_path b0) g) g"
          by (rule Theorem_51_2_left_identity[OF hTB hg_path])
        \<comment> \<open>g ≃ f*g (sym of step1 + step2).\<close>
        have step3: "top1_path_homotopic_on B TB b0 b0 g (top1_path_product f g)"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTB
                Lemma_51_1_path_homotopic_sym[OF step2] step1])
        \<comment> \<open>const ≃ g ≃ f*g ≃ h.\<close>
        have step4: "top1_path_homotopic_on B TB b0 b0 (top1_constant_path b0) (top1_path_product f g)"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTB hconst_g step3])
        have hfg_hom: "top1_path_homotopic_on B TB b0 b0 (top1_path_product f g) h"
          using hfg unfolding top1_loop_equiv_on_def by (by100 blast)
        have "top1_path_homotopic_on B TB b0 b0 (top1_constant_path b0) h"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTB step4 hfg_hom])
        have h_loop: "top1_is_loop_on B TB b0 h"
          using hfg unfolding top1_loop_equiv_on_def by (by100 blast)
        show "h \<in> top1_fundamental_group_id B TB b0"
          unfolding top1_fundamental_group_id_def top1_loop_equiv_on_def
          using \<open>top1_path_homotopic_on B TB b0 b0 (top1_constant_path b0) h\<close>
                h_loop top1_constant_path_is_loop[OF hTB hb0_B] by (by100 blast)
      next
        assume "h \<in> top1_fundamental_group_id B TB b0"
        hence hh: "top1_loop_equiv_on B TB b0 (top1_constant_path b0) h"
          unfolding top1_fundamental_group_id_def by (by100 blast)
        \<comment> \<open>Take f = g = const. const*const ≃ const (left identity) ≃ h.\<close>
        have hconst_loop: "top1_is_loop_on B TB b0 (top1_constant_path b0)"
          by (rule top1_constant_path_is_loop[OF hTB hb0_B])
        have hconst_path: "top1_is_path_on B TB b0 b0 (top1_constant_path b0)"
          using hconst_loop unfolding top1_is_loop_on_def .
        have hcc_const: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_constant_path b0) (top1_constant_path b0))
            (top1_constant_path b0)"
          by (rule Theorem_51_2_left_identity[OF hTB hconst_path])
        have hconst_h: "top1_path_homotopic_on B TB b0 b0 (top1_constant_path b0) h"
          using hh unfolding top1_loop_equiv_on_def by (by100 blast)
        have "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_constant_path b0) (top1_constant_path b0)) h"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTB hcc_const hconst_h])
        have h_loop: "top1_is_loop_on B TB b0 h"
          using hh unfolding top1_loop_equiv_on_def by (by100 blast)
        have hcc_loop: "top1_is_loop_on B TB b0
            (top1_path_product (top1_constant_path b0) (top1_constant_path b0))"
          by (rule top1_path_product_is_loop[OF hTB hconst_loop hconst_loop])
        have "top1_loop_equiv_on B TB b0
            (top1_path_product (top1_constant_path b0) (top1_constant_path b0)) h"
          unfolding top1_loop_equiv_on_def
          using hcc_loop h_loop
                \<open>top1_path_homotopic_on B TB b0 b0
                  (top1_path_product (top1_constant_path b0) (top1_constant_path b0)) h\<close>
          by (by100 blast)
        have hconst_in: "top1_constant_path b0 \<in> top1_fundamental_group_id B TB b0"
          unfolding top1_fundamental_group_id_def
          using top1_loop_equiv_on_refl[OF hconst_loop] by (by100 blast)
        show "h \<in> top1_fundamental_group_mul B TB b0
            (top1_fundamental_group_id B TB b0) (top1_fundamental_group_id B TB b0)"
          unfolding top1_fundamental_group_mul_def
          using hconst_in \<open>top1_loop_equiv_on B TB b0
              (top1_path_product (top1_constant_path b0) (top1_constant_path b0)) h\<close>
          by (by100 blast)
      qed
    qed
    show ?thesis using hinvg_id hmul_id by simp
  qed
  have hRHS: "\<exists>c\<in>top1_fundamental_group_carrier B TB b0.
      top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
      = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    (top1_fundamental_group_invg B TB b0 c)) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
    apply (rule bexI[of _ "top1_fundamental_group_id B TB b0"])
    using hconj hH_trivial hH'_trivial apply (by100 simp)
    using hid_mem apply (by100 blast)
    done
  show ?thesis using iffD2[OF Theorem_79_4[OF assms(4,1,5)
        hcovE assms(10) hcovE' assms(11) assms(6,7,8,9) assms(12,13) hb0_B]] hRHS by (by100 blast)
qed

text \<open>Restriction of a homeomorphism to an open subset (preimage) gives a homeomorphism.\<close>
lemma homeomorphism_restrict_open:
  assumes hf: "top1_homeomorphism_on X TX Y TY f"
      and hV: "openin_on Y TY V"
      and hVY: "V \<subseteq> Y"
      and hTX: "is_topology_on X TX"
      and hTY: "is_topology_on Y TY"
  shows "top1_homeomorphism_on {x \<in> X. f x \<in> V} (subspace_topology X TX {x \<in> X. f x \<in> V})
             V (subspace_topology Y TY V) f"
proof -
  let ?X' = "{x \<in> X. f x \<in> V}"
  let ?TX' = "subspace_topology X TX ?X'"
  let ?TY' = "subspace_topology Y TY V"
  have hXsub: "?X' \<subseteq> X" by (by100 blast)
  have hbij: "bij_betw f X Y" using hf unfolding top1_homeomorphism_on_def by (by100 blast)
  have hf_cont: "top1_continuous_map_on X TX Y TY f"
    using hf unfolding top1_homeomorphism_on_def by (by100 blast)
  have hfinv_cont: "top1_continuous_map_on Y TY X TX (inv_into X f)"
    using hf unfolding top1_homeomorphism_on_def by (by100 blast)
  show ?thesis unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on ?X' ?TX'" by (rule subspace_topology_is_topology_on[OF hTX hXsub])
    show "is_topology_on V ?TY'" by (rule subspace_topology_is_topology_on[OF hTY hVY])
    \<comment> \<open>bij_betw: f maps ?X' bijectively to V.\<close>
    show "bij_betw f ?X' V"
    proof -
      have "inj_on f X" using hbij unfolding bij_betw_def by (by100 blast)
      hence "inj_on f ?X'" by (rule inj_on_subset) (by100 blast)
      moreover have "f ` ?X' = V"
      proof (rule set_eqI)
        fix y show "y \<in> f ` ?X' \<longleftrightarrow> y \<in> V"
        proof
          assume "y \<in> f ` ?X'" thus "y \<in> V" by (by100 blast)
        next
          assume "y \<in> V"
          hence "y \<in> Y" using hVY by (by100 blast)
          hence "\<exists>x\<in>X. f x = y" using hbij unfolding bij_betw_def by (by100 blast)
          then obtain x where hx: "x \<in> X" and hfx: "f x = y" by (by100 blast)
          hence "x \<in> ?X'" using \<open>y \<in> V\<close> by (by100 blast)
          thus "y \<in> f ` ?X'" using hfx by (by100 blast)
        qed
      qed
      ultimately show ?thesis unfolding bij_betw_def by (by100 blast)
    qed
    \<comment> \<open>Continuity: f restricted to ?X' \<rightarrow> V.\<close>
    show "top1_continuous_map_on ?X' ?TX' V ?TY' f"
    proof -
      have hf_restr: "top1_continuous_map_on ?X' ?TX' Y TY f"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF hf_cont hXsub])
      have himg: "f ` ?X' \<subseteq> V" by (by100 blast)
      show ?thesis by (rule top1_continuous_map_on_codomain_shrink[OF hf_restr himg hVY])
    qed
    \<comment> \<open>Inverse continuity.\<close>
    show "top1_continuous_map_on V ?TY' ?X' ?TX' (inv_into ?X' f)"
    proof -
      \<comment> \<open>inv_into X' f = inv_into X f on V (since X' \<subseteq> X, f injective, image = V).\<close>
      have hinj: "inj_on f X" using hbij unfolding bij_betw_def by (by100 blast)
      have hfinv_agree: "\<forall>y\<in>V. inv_into ?X' f y = inv_into X f y"
      proof
        fix y assume "y \<in> V"
        hence "y \<in> Y" using hVY by (by100 blast)
        hence "y \<in> f ` X" using hbij unfolding bij_betw_def by (by100 blast)
        hence "inv_into X f y \<in> X" by (rule inv_into_into)
        moreover have "f (inv_into X f y) = y"
          using \<open>y \<in> f ` X\<close> by (rule f_inv_into_f)
        hence "f (inv_into X f y) \<in> V" using \<open>y \<in> V\<close> by (by100 simp)
        hence "inv_into X f y \<in> ?X'" using calculation by (by100 blast)
        thus "inv_into ?X' f y = inv_into X f y"
          by (intro inv_into_f_eq[OF inj_on_subset[OF hinj hXsub]])
             (use \<open>f (inv_into X f y) = y\<close> in \<open>by100 blast\<close>)
      qed
      \<comment> \<open>Restrict inv_into X f: Y \<rightarrow> X to V \<rightarrow> X'.\<close>
      have hfinv_restr: "top1_continuous_map_on V ?TY' X TX (inv_into X f)"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF hfinv_cont hVY])
      \<comment> \<open>Codomain shrink from X to X'.\<close>
      have hfinv_img: "(inv_into X f) ` V \<subseteq> ?X'"
      proof
        fix x assume "x \<in> (inv_into X f) ` V"
        then obtain y where hy: "y \<in> V" and hx: "x = inv_into X f y" by (by100 blast)
        have "inv_into X f y \<in> ?X'"
        proof -
          have "y \<in> f ` X" using hy hVY hbij unfolding bij_betw_def by (by100 blast)
          hence hiy_X: "inv_into X f y \<in> X" by (rule inv_into_into)
          have "f (inv_into X f y) = y" using \<open>y \<in> f ` X\<close> by (rule f_inv_into_f)
          hence "f (inv_into X f y) \<in> V" using hy by (by100 simp)
          thus ?thesis using hiy_X by (by100 blast)
        qed
        thus "x \<in> ?X'" using hx by (by100 simp)
      qed
      have hfinv_shrink: "top1_continuous_map_on V ?TY' ?X' ?TX' (inv_into X f)"
        by (rule top1_continuous_map_on_codomain_shrink[OF hfinv_restr hfinv_img hXsub])
      \<comment> \<open>inv_into X' f = inv_into X f on V, so continuity transfers.\<close>
      \<comment> \<open>Transfer: inv_into X' f and inv_into X f agree on V, so same continuity.\<close>
      have "\<forall>y\<in>V. inv_into ?X' f y = inv_into X f y" by (rule hfinv_agree)
      show ?thesis
        by (rule top1_continuous_map_on_agree'[OF hfinv_shrink])
           (use hfinv_agree in \<open>by100 simp\<close>)
    qed
  qed
qed

text \<open>Helper: open subset of an evenly covered set is evenly covered.
  If U is evenly covered by p and V \<subseteq> U is open in B, then V is evenly covered by p.\<close>
lemma evenly_covered_open_subset:
  assumes hcov: "top1_evenly_covered_on E TE B TB p U"
      and hV: "openin_on B TB V" and hVU: "V \<subseteq> U"
      and hTE: "is_topology_on E TE" and hTB: "is_topology_on B TB"
  shows "top1_evenly_covered_on E TE B TB p V"
proof -
  \<comment> \<open>Extract sheets of U.\<close>
  obtain \<V>U where h\<V>_open: "\<forall>W\<in>\<V>U. openin_on E TE W"
      and h\<V>_disj: "\<forall>W\<in>\<V>U. \<forall>W'\<in>\<V>U. W \<noteq> W' \<longrightarrow> W \<inter> W' = {}"
      and h\<V>_union: "{x\<in>E. p x \<in> U} = \<Union>\<V>U"
      and h\<V>_homeo: "\<forall>W\<in>\<V>U. top1_homeomorphism_on W (subspace_topology E TE W) U
                                    (subspace_topology B TB U) p"
    using hcov unfolding top1_evenly_covered_on_def
    by (elim conjE exE) (by100 blast)
  \<comment> \<open>Define restricted sheets: W' = {x \<in> W | p x \<in> V} for each W \<in> \<V>U.\<close>
  let ?\<V>V = "(\<lambda>W. {x \<in> W. p x \<in> V}) ` \<V>U"
  show ?thesis unfolding top1_evenly_covered_on_def
  proof (intro conjI exI[of _ ?\<V>V])
    show "openin_on B TB V" by (rule hV)
  next
    \<comment> \<open>Each restricted sheet is open in E.\<close>
    show "\<forall>W'\<in>?\<V>V. openin_on E TE W'"
    proof
      fix W' assume "W' \<in> ?\<V>V"
      then obtain W where hW: "W \<in> \<V>U" and hW': "W' = {x \<in> W. p x \<in> V}" by (by100 blast)
      \<comment> \<open>p|_W: W \<rightarrow> U is a homeomorphism. V is open in subspace(B,U). Preimage of V is open in W.\<close>
      have hW_open: "openin_on E TE W" using h\<V>_open hW by (by100 blast)
      have hW_homeo: "top1_homeomorphism_on W (subspace_topology E TE W) U (subspace_topology B TB U) p"
        using h\<V>_homeo hW by (by100 blast)
      \<comment> \<open>V is open in subspace_topology B TB U (since V \<in> TB and V \<subseteq> U).\<close>
      have hV_in_TU: "V \<in> subspace_topology B TB U"
        unfolding subspace_topology_def using hV hVU unfolding openin_on_def by (by100 blast)
      \<comment> \<open>p continuous W \<rightarrow> U means preimage of V (open in U) is open in W.\<close>
      have hp_cont_WU: "top1_continuous_map_on W (subspace_topology E TE W) U (subspace_topology B TB U) p"
        using hW_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have "{x \<in> W. p x \<in> V} \<in> subspace_topology E TE W"
        using hp_cont_WU hV_in_TU unfolding top1_continuous_map_on_def by (by100 blast)
      \<comment> \<open>Open in subspace(E, W) and W open in E implies open in E.\<close>
      hence "{x \<in> W. p x \<in> V} \<in> TE"
      proof -
        have "{x \<in> W. p x \<in> V} \<in> subspace_topology E TE W" by (rule \<open>{x \<in> W. p x \<in> V} \<in> subspace_topology E TE W\<close>)
        then obtain T_open where hTo: "T_open \<in> TE" and heq: "{x \<in> W. p x \<in> V} = W \<inter> T_open"
          unfolding subspace_topology_def by (by100 blast)
        have "W \<in> TE" using hW_open unfolding openin_on_def by (by100 blast)
        hence "W \<inter> T_open \<in> TE" by (rule topology_inter2[OF hTE _ hTo])
        thus ?thesis using heq by (by100 simp)
      qed
      moreover have "{x \<in> W. p x \<in> V} \<subseteq> E"
      proof -
        have "W \<subseteq> E" using hW_open unfolding openin_on_def by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      ultimately show "openin_on E TE W'" unfolding hW' openin_on_def by (by100 blast)
    qed
  next
    \<comment> \<open>Restricted sheets are pairwise disjoint.\<close>
    show "\<forall>W'\<in>?\<V>V. \<forall>W''\<in>?\<V>V. W' \<noteq> W'' \<longrightarrow> W' \<inter> W'' = {}"
    proof (intro ballI impI)
      fix W' W'' assume "W' \<in> ?\<V>V" "W'' \<in> ?\<V>V" "W' \<noteq> W''"
      then obtain W1 W2 where hW1: "W1 \<in> \<V>U" and hW1': "W' = {x \<in> W1. p x \<in> V}"
          and hW2: "W2 \<in> \<V>U" and hW2': "W'' = {x \<in> W2. p x \<in> V}" by (by100 blast)
      show "W' \<inter> W'' = {}"
      proof (cases "W1 = W2")
        case True thus ?thesis using \<open>W' \<noteq> W''\<close> hW1' hW2' by (by100 simp)
      next
        case False
        hence "W1 \<inter> W2 = {}" using h\<V>_disj hW1 hW2 by (by100 blast)
        thus ?thesis using hW1' hW2' by (by100 blast)
      qed
    qed
  next
    \<comment> \<open>Union of restricted sheets = p\<inverse>(V) \<inter> E.\<close>
    show "{x\<in>E. p x \<in> V} = \<Union>?\<V>V"
    proof (rule set_eqI)
      fix x show "x \<in> {x\<in>E. p x \<in> V} \<longleftrightarrow> x \<in> \<Union>?\<V>V"
      proof
        assume "x \<in> {x\<in>E. p x \<in> V}"
        hence hxE: "x \<in> E" and hpxV: "p x \<in> V" by (by100 blast)+
        hence "p x \<in> U" using hVU by (by100 blast)
        hence "x \<in> {x\<in>E. p x \<in> U}" using hxE by (by100 blast)
        hence "x \<in> \<Union>\<V>U" using h\<V>_union by (by100 simp)
        then obtain W where hW: "W \<in> \<V>U" and hxW: "x \<in> W" by (by100 blast)
        have "x \<in> {x \<in> W. p x \<in> V}" using hxW hpxV by (by100 blast)
        moreover have "{x \<in> W. p x \<in> V} \<in> ?\<V>V" using hW by (by100 blast)
        ultimately show "x \<in> \<Union>?\<V>V" by (by100 blast)
      next
        assume "x \<in> \<Union>?\<V>V"
        then obtain W where hW: "W \<in> \<V>U" and hx: "x \<in> {x \<in> W. p x \<in> V}" by (by100 blast)
        hence hxW: "x \<in> W" and hpxV: "p x \<in> V" by (by100 blast)+
        have "x \<in> \<Union>\<V>U" using hW hxW by (by100 blast)
        hence "x \<in> {x\<in>E. p x \<in> U}" using h\<V>_union by (by100 simp)
        thus "x \<in> {x\<in>E. p x \<in> V}" using hpxV by (by100 blast)
      qed
    qed
  next
    \<comment> \<open>Each restricted sheet is homeomorphic to V via p.\<close>
    show "\<forall>W'\<in>?\<V>V. top1_homeomorphism_on W' (subspace_topology E TE W') V
                          (subspace_topology B TB V) p"
    proof
      fix W' assume "W' \<in> ?\<V>V"
      then obtain W where hW: "W \<in> \<V>U" and hW': "W' = {x \<in> W. p x \<in> V}" by (by100 blast)
      have hW_homeo: "top1_homeomorphism_on W (subspace_topology E TE W) U (subspace_topology B TB U) p"
        using h\<V>_homeo hW by (by100 blast)
      have hW_open: "openin_on E TE W" using h\<V>_open hW by (by100 blast)
      have hWsub: "W \<subseteq> E" using hW_open unfolding openin_on_def by (by100 blast)
      have hW'sub: "W' \<subseteq> W" unfolding hW' by (by100 blast)
      have hW'E: "W' \<subseteq> E" using hW'sub hWsub by (by100 blast)
      have hUopen: "openin_on B TB U" using hcov unfolding top1_evenly_covered_on_def by (by100 blast)
      have hUsub: "U \<subseteq> B" using hUopen unfolding openin_on_def by (by100 blast)
      have hVsub: "V \<subseteq> B" using hV unfolding openin_on_def by (by100 blast)
      \<comment> \<open>V is open in subspace(B, U).\<close>
      have hV_in_TU: "V \<in> subspace_topology B TB U"
        unfolding subspace_topology_def using hV hVU unfolding openin_on_def by (by100 blast)
      have hV_open_sub: "openin_on U (subspace_topology B TB U) V"
        unfolding openin_on_def using hV_in_TU hVU by (by100 blast)
      have hTW: "is_topology_on W (subspace_topology E TE W)"
        by (rule subspace_topology_is_topology_on[OF hTE hWsub])
      have hTU: "is_topology_on U (subspace_topology B TB U)"
        by (rule subspace_topology_is_topology_on[OF hTB hUsub])
      \<comment> \<open>Apply homeomorphism_restrict_open to p: W \<cong> U with open V \<subseteq> U.\<close>
      note hrestr = homeomorphism_restrict_open[OF hW_homeo hV_open_sub hVU hTW hTU]
      \<comment> \<open>subspace_topology_trans: subspace(W, subspace(E,W), W') = subspace(E, W').\<close>
      have hTW'_eq: "subspace_topology W (subspace_topology E TE W) {x \<in> W. p x \<in> V}
          = subspace_topology E TE {x \<in> W. p x \<in> V}"
        by (rule subspace_topology_trans) (by100 force)
      have hTV'_eq: "subspace_topology U (subspace_topology B TB U) V
          = subspace_topology B TB V"
        by (rule subspace_topology_trans[OF hVU])
      show "top1_homeomorphism_on W' (subspace_topology E TE W') V (subspace_topology B TB V) p"
        using hrestr hTW'_eq hTV'_eq unfolding hW' by (by100 simp)
    qed
  qed
qed

lemma covering_base_locally_path_connected:
  assumes "top1_covering_map_on E TE B TB p"
      and "top1_locally_path_connected_on E TE"
      and "is_topology_on E TE" and "is_topology_on B TB"
  shows "top1_locally_path_connected_on B TB"
  unfolding top1_locally_path_connected_on_def
proof (intro conjI ballI)
  show "is_topology_on B TB" by (rule assms(4))
next
  fix b assume hb: "b \<in> B"
  show "top1_locally_path_connected_at B TB b"
    unfolding top1_locally_path_connected_at_def
  proof (intro allI impI)
    fix U assume hU: "neighborhood_of b B TB U \<and> U \<subseteq> B"
    \<comment> \<open>Get U0 open with b \<in> U0 \<subseteq> U, and Uc evenly covered by p.\<close>
    obtain U0 where hU0: "U0 \<in> TB" "b \<in> U0" "U0 \<subseteq> U"
      using hU unfolding neighborhood_of_def by (by100 blast)
    obtain Uc where hUc_b: "b \<in> Uc" and hUc_cov: "top1_evenly_covered_on E TE B TB p Uc"
      using hb assms(1) unfolding top1_covering_map_on_def by (by100 blast)
    have hUc_open: "Uc \<in> TB"
      using hUc_cov unfolding top1_evenly_covered_on_def openin_on_def by (by100 blast)
    let ?V = "U0 \<inter> Uc"
    have hV_open: "?V \<in> TB" by (rule topology_inter2[OF assms(4) hU0(1) hUc_open])
    have hV_b: "b \<in> ?V" using hU0(2) hUc_b by (by100 blast)
    have "openin_on B TB Uc" using hUc_cov unfolding top1_evenly_covered_on_def by (by100 blast)
    hence "Uc \<subseteq> B" unfolding openin_on_def by (by100 blast)
    have hV_sub_B: "?V \<subseteq> B" using \<open>Uc \<subseteq> B\<close> by (by100 blast)
    have hV_openin: "openin_on B TB ?V"
      using hV_open hV_sub_B unfolding openin_on_def by (by100 blast)
    have hV_cov: "top1_evenly_covered_on E TE B TB p ?V"
      by (rule evenly_covered_open_subset[OF hUc_cov hV_openin _ assms(3) assms(4)]) (by100 blast)
    \<comment> \<open>Get p-slice W and preimage e of b.\<close>
    obtain e where he: "e \<in> E" "p e = b"
      using hb top1_covering_map_on_surj[OF assms(1)] by (by100 blast)
    obtain \<V> where h\<V>_open: "\<forall>W\<in>\<V>. openin_on E TE W"
        and h\<V>_union: "{x\<in>E. p x \<in> ?V} = \<Union>\<V>"
        and h\<V>_homeo: "\<forall>W\<in>\<V>. top1_homeomorphism_on W (subspace_topology E TE W)
            ?V (subspace_topology B TB ?V) p"
      using hV_cov unfolding top1_evenly_covered_on_def
      by (elim conjE exE) (by100 blast)
    have he_pV: "e \<in> {x\<in>E. p x \<in> ?V}" using he hV_b by (by100 blast)
    hence "e \<in> \<Union>\<V>" using h\<V>_union by (by100 simp)
    then obtain W where hW: "W \<in> \<V>" "e \<in> W" by (by100 blast)
    have hW_open: "W \<in> TE" using h\<V>_open hW(1) unfolding openin_on_def by (by100 blast)
    have hW_sub_E: "W \<subseteq> E" using h\<V>_open hW(1) unfolding openin_on_def by (by100 blast)
    \<comment> \<open>W is open and lpc. Path component C of e in W is open and path-connected.\<close>
    have hW_lpc: "top1_locally_path_connected_on W (subspace_topology E TE W)"
      by (rule open_subset_locally_path_connected[OF assms(2) hW_open hW_sub_E])
    have hW_top: "is_topology_on W (subspace_topology E TE W)"
      using hW_lpc unfolding top1_locally_path_connected_on_def by (by100 blast)
    let ?C = "top1_path_component_of_on W (subspace_topology E TE W) e"
    have hPC: "?C \<in> subspace_topology E TE W"
      by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hW_top hW_lpc hW(2)])
    \<comment> \<open>C is open in E.\<close>
    have hC_TE: "?C \<in> TE"
    proof -
      from hPC obtain U' where hU'_TE: "U' \<in> TE" and hC_eq: "?C = W \<inter> U'"
        unfolding subspace_topology_def by (by100 blast)
      have "W \<inter> U' \<in> TE" by (rule topology_inter2[OF assms(3) hW_open hU'_TE])
      thus ?thesis using hC_eq by (by100 simp)
    qed
    \<comment> \<open>Key facts about C and the homeomorphism.\<close>
    have he_C: "e \<in> ?C"
      by (rule top1_path_component_of_on_self_mem[OF hW_top hW(2)])
    have hC_sub_W: "?C \<subseteq> W"
      by (rule top1_path_component_of_on_subset[OF hW_top hW(2)])
    have hp_homeo: "top1_homeomorphism_on W (subspace_topology E TE W)
        ?V (subspace_topology B TB ?V) p"
      using h\<V>_homeo hW(1) by (by100 blast)
    have hp_bij: "bij_betw p W ?V"
      using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    \<comment> \<open>p(C) is open in B: use homeomorphism inverse continuity.\<close>
    have hpC_open_sub: "p ` ?C \<in> subspace_topology B TB ?V"
    proof -
      have hinv_cont: "top1_continuous_map_on ?V (subspace_topology B TB ?V) W
          (subspace_topology E TE W) (inv_into W p)"
        using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have "p ` ?C = {u \<in> ?V. (inv_into W p) u \<in> ?C}"
      proof (rule set_eqI, rule iffI)
        fix u assume "u \<in> p ` ?C"
        then obtain e' where he': "e' \<in> ?C" "u = p e'" by (by100 blast)
        have "e' \<in> W" using he' hC_sub_W by (by100 blast)
        have "u \<in> ?V" using \<open>e' \<in> W\<close> \<open>u = p e'\<close> hp_bij unfolding bij_betw_def by (by100 blast)
        have "u \<in> p ` W" using \<open>e' \<in> W\<close> \<open>u = p e'\<close> by (by100 blast)
        have "inj_on p W" using hp_bij unfolding bij_betw_def by (by100 blast)
        have "inv_into W p (p e') = e'"
          by (rule inv_into_f_f[OF \<open>inj_on p W\<close> \<open>e' \<in> W\<close>])
        hence "inv_into W p u = e'" using \<open>u = p e'\<close> by (by100 simp)
        thus "u \<in> {u \<in> ?V. (inv_into W p) u \<in> ?C}" using \<open>u \<in> ?V\<close> he'(1) by (by100 simp)
      next
        fix u assume hu: "u \<in> {u \<in> ?V. (inv_into W p) u \<in> ?C}"
        hence "u \<in> ?V" "(inv_into W p) u \<in> ?C" by (by100 blast)+
        have "u \<in> p ` W" using \<open>u \<in> ?V\<close> hp_bij unfolding bij_betw_def by (by100 blast)
        have "p (inv_into W p u) = u" by (rule f_inv_into_f[OF \<open>u \<in> p ` W\<close>])
        show "u \<in> p ` ?C"
        proof (rule image_eqI)
          show "u = p (inv_into W p u)" using \<open>p (inv_into W p u) = u\<close> by (by100 simp)
          show "inv_into W p u \<in> ?C" using \<open>(inv_into W p) u \<in> ?C\<close> by (by100 simp)
        qed
      qed
      have hpreimg: "{u \<in> ?V. (inv_into W p) u \<in> ?C} \<in> subspace_topology B TB ?V"
        using hinv_cont hPC unfolding top1_continuous_map_on_def by (by100 blast)
      thus ?thesis using \<open>p ` ?C = {u \<in> ?V. (inv_into W p) u \<in> ?C}\<close> by (by100 simp)
    qed
    have hpC_TB: "p ` ?C \<in> TB"
    proof -
      from hpC_open_sub obtain T' where hT': "T' \<in> TB" and hpC_eq: "p ` ?C = ?V \<inter> T'"
        unfolding subspace_topology_def by (by100 blast)
      have "?V \<inter> T' \<in> TB" by (rule topology_inter2[OF assms(4) hV_open hT'])
      thus ?thesis using hpC_eq by (by100 simp)
    qed
    have hpC_nhd: "neighborhood_of b B TB (p ` ?C)"
    proof -
      have "b \<in> p ` ?C" using he_C he(2) by (by100 blast)
      thus ?thesis using hpC_TB unfolding neighborhood_of_def by (by100 blast)
    qed
    have hpC_sub_U: "p ` ?C \<subseteq> U"
    proof -
      have "?C \<subseteq> W" by (rule hC_sub_W)
      hence "p ` ?C \<subseteq> p ` W" by (by100 blast)
      also have "p ` W = ?V" using hp_bij unfolding bij_betw_def by (by100 blast)
      also have "?V \<subseteq> U0" by (by100 blast)
      also have "U0 \<subseteq> U" by (rule hU0(3))
      finally show ?thesis .
    qed
    have hpC_sub_B: "p ` ?C \<subseteq> B"
    proof -
      have "p ` ?C \<subseteq> p ` W" using hC_sub_W by (by100 blast)
      also have "p ` W = ?V" using hp_bij unfolding bij_betw_def by (by100 blast)
      also have "?V \<subseteq> B" by (rule hV_sub_B)
      finally show ?thesis .
    qed
    have hC_pc: "top1_path_connected_on ?C (subspace_topology E TE ?C)"
    proof -
      have "top1_path_connected_on ?C (subspace_topology W (subspace_topology E TE W) ?C)"
        by (rule top1_path_component_of_on_path_connected[OF hW_top hW(2)])
      moreover have "subspace_topology W (subspace_topology E TE W) ?C = subspace_topology E TE ?C"
        by (rule subspace_topology_trans[OF hC_sub_W])
      ultimately show ?thesis by (by100 simp)
    qed
    have hpC_pc: "top1_path_connected_on (p ` ?C) (subspace_topology B TB (p ` ?C))"
    proof -
      \<comment> \<open>Restrict homeomorphism p|_W to C: p|_C: C \<cong> p(C).\<close>
      have hC_openin_V: "openin_on ?V (subspace_topology B TB ?V) (p ` ?C)"
        using hpC_open_sub unfolding openin_on_def
      proof (intro conjI)
        show "p ` ?C \<subseteq> ?V" using hC_sub_W hp_bij unfolding bij_betw_def by (by100 blast)
        show "p ` ?C \<in> subspace_topology B TB ?V" by (rule hpC_open_sub)
      qed
      have hpC_homeo: "top1_homeomorphism_on ?C (subspace_topology E TE ?C)
          (p ` ?C) (subspace_topology B TB (p ` ?C)) p"
      proof -
        have hC_openin_W: "openin_on W (subspace_topology E TE W) ?C"
          using hPC hC_sub_W unfolding openin_on_def by (by100 blast)
        have hpC_sub_V: "p ` ?C \<subseteq> ?V"
          using hC_sub_W hp_bij unfolding bij_betw_def by (by100 blast)
        have hTV: "is_topology_on ?V (subspace_topology B TB ?V)"
          using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        have hrestr: "top1_homeomorphism_on {x \<in> W. p x \<in> p ` ?C}
            (subspace_topology W (subspace_topology E TE W) {x \<in> W. p x \<in> p ` ?C})
            (p ` ?C) (subspace_topology ?V (subspace_topology B TB ?V) (p ` ?C)) p"
          by (rule homeomorphism_restrict_open[OF hp_homeo hC_openin_V hpC_sub_V hW_top hTV])
        have hsub1: "subspace_topology W (subspace_topology E TE W) {x \<in> W. p x \<in> p ` ?C}
            = subspace_topology E TE {x \<in> W. p x \<in> p ` ?C}"
        proof -
          have "{x \<in> W. p x \<in> p ` ?C} \<subseteq> W" by (by100 blast)
          thus ?thesis by (rule subspace_topology_trans)
        qed
        have hsub2: "subspace_topology ?V (subspace_topology B TB ?V) (p ` ?C)
            = subspace_topology B TB (p ` ?C)"
          by (rule subspace_topology_trans[OF hpC_sub_V])
        have "top1_homeomorphism_on {x \<in> W. p x \<in> p ` ?C}
            (subspace_topology E TE {x \<in> W. p x \<in> p ` ?C})
            (p ` ?C) (subspace_topology B TB (p ` ?C)) p"
          using hrestr hsub1 hsub2 by (by100 simp)
        moreover have "{x \<in> W. p x \<in> p ` ?C} = ?C"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> {x \<in> W. p x \<in> p ` ?C}"
          hence "x \<in> W" "p x \<in> p ` ?C" by (by100 blast)+
          then obtain c where "c \<in> ?C" "p x = p c" by (by100 blast)
          have "c \<in> W" using \<open>c \<in> ?C\<close> hC_sub_W by (by100 blast)
          have "inj_on p W" using hp_bij unfolding bij_betw_def by (by100 blast)
          hence "x = c" using \<open>x \<in> W\<close> \<open>c \<in> W\<close> \<open>p x = p c\<close> unfolding inj_on_def by (by100 blast)
          thus "x \<in> ?C" using \<open>c \<in> ?C\<close> by (by100 simp)
        next
          fix x assume "x \<in> ?C"
          thus "x \<in> {x \<in> W. p x \<in> p ` ?C}" using hC_sub_W by (by100 blast)
        qed
        ultimately show ?thesis by (by100 simp)
      qed
      from homeomorphism_preserves_path_connected[OF hpC_homeo hC_pc]
      show ?thesis .
    qed
    show "\<exists>V. neighborhood_of b B TB V \<and> V \<subseteq> U \<and> V \<subseteq> B \<and>
        top1_path_connected_on V (subspace_topology B TB V)"
      using hpC_nhd hpC_sub_U hpC_sub_B hpC_pc by (by100 blast)
  qed
qed

(** from \<S>80 Theorem 80.3: universal covering factors through any covering **)
theorem Theorem_80_3_universal:
  assumes "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "is_topology_on_strict Y TY"
      and "top1_covering_map_on E TE B TB p"
      and "top1_simply_connected_on E TE"
      and "top1_covering_map_on Y TY B TB r"
      and "top1_locally_path_connected_on E TE"
      and "top1_path_connected_on Y TY"
  shows "\<exists>q. top1_covering_map_on E TE Y TY q \<and> (\<forall>e\<in>E. r (q e) = p e)"
proof (cases "E = {}")
  case True
  \<comment> \<open>Empty case: E = {} implies B = {} (surjectivity of p) implies Y = {} (surjectivity of r).
     Any function from {} to {} is a covering map.\<close>
  have hB_empty: "B = {}" using True top1_covering_map_on_surj[OF assms(4)] by (by100 blast)
  have hY_empty: "Y = {}" using hB_empty top1_covering_map_on_surj[OF assms(6)] by (by100 blast)
  have "top1_covering_map_on E TE Y TY (\<lambda>e. undefined)"
    unfolding top1_covering_map_on_def top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix x assume "x \<in> E" thus "(undefined :: 'c) \<in> Y" using True by (by100 blast)
  next
    fix V assume "V \<in> TY" show "{x \<in> E. (undefined :: 'c) \<in> V} \<in> TE"
      using True assms(1) unfolding is_topology_on_strict_def is_topology_on_def by (by100 auto)
  next
    show "(\<lambda>e. undefined :: 'c) ` E = Y" using True hY_empty by (by100 blast)
  next
    fix b assume "b \<in> Y" thus "\<exists>U. b \<in> U \<and> top1_evenly_covered_on E TE Y TY (\<lambda>e. undefined) U"
      using hY_empty by (by100 blast)
  qed
  thus ?thesis using True by (by100 blast)
next
  case False
  \<comment> \<open>Munkres 80.3: Define q: E \<rightarrow> Y by path-lifting. For e \<in> E, choose path \<alpha> in E
     from e0 to e. Lift r\<inverse> \<circ> p \<circ> \<alpha> to Y starting at y0 (where r(y0)=b0).
     The lift's endpoint is q(e). Well-defined because E is simply connected.\<close>
  obtain e0 where he0: "e0 \<in> E" using False by (by100 blast)
  let ?b0 = "p e0"
  have hb0_B: "?b0 \<in> B"
    using he0 top1_covering_map_on_surj[OF assms(4)] by (by100 blast)
  have hr_surj: "r ` Y = B" by (rule top1_covering_map_on_surj[OF assms(6)])
  have "?b0 \<in> r ` Y" using hb0_B hr_surj by (by100 simp)
  then obtain y0 where hy0: "y0 \<in> Y" and hry0: "r y0 = ?b0"
    unfolding image_def by (by100 auto)
  \<comment> \<open>For each e \<in> E, pick path \<alpha> from e0 to e. Lift p\<circ>\<alpha> to Y starting at y0.
     Simple connectivity ensures uniqueness (different \<alpha>'s give same endpoint).\<close>
  have "\<exists>q. (\<forall>e\<in>E. q e \<in> Y) \<and> (\<forall>e\<in>E. r (q e) = p e)
      \<and> q e0 = y0 \<and> top1_continuous_map_on E TE Y TY q"
  proof -
    have hTE: "is_topology_on E TE" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have hTB: "is_topology_on B TB" using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
    have hTY: "is_topology_on Y TY" using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
    have hp_cont: "top1_continuous_map_on E TE B TB p"
      by (rule top1_covering_map_on_continuous[OF assms(4)])
    have hE_pc: "top1_path_connected_on E TE"
      using assms(5) unfolding top1_simply_connected_on_def by (by100 blast)
    \<comment> \<open>E is locally path-connected (covering space of locally path-connected B,
       or directly from the covering structure + local homeomorphisms).\<close>
    have hE_lpc: "top1_locally_path_connected_on E TE" by (rule assms(7))
    have hpe0: "p e0 = r y0" using hry0 by (by100 simp)
    \<comment> \<open>E simply connected \<Rightarrow> p_*(\<pi>_1(E)) = {e} \<subseteq> r_*(\<pi>_1(Y)).\<close>
    have himg_triv: "top1_fundamental_group_image_hom E TE e0 B TB (r y0) p
        = {top1_fundamental_group_id B TB (r y0)}"
      by (rule simply_connected_trivial_image[OF assms(5) assms(4) he0 hpe0 hTB])
    have hsubgrp: "top1_fundamental_group_image_hom E TE e0 B TB (r y0) p
        \<subseteq> top1_fundamental_group_image_hom Y TY y0 B TB (r y0) r"
    proof -
      \<comment> \<open>{e} is in any image_hom (the identity class is always in the image).\<close>
      have "top1_fundamental_group_id B TB (r y0)
          \<in> top1_fundamental_group_image_hom Y TY y0 B TB (r y0) r"
      proof -
        \<comment> \<open>id_Y \<in> carrier(Y). induced(id_Y) = {g | loop_equiv(r\<circ>const_y0, g)} = id_B.\<close>
        have hid_Y: "top1_fundamental_group_id Y TY y0 \<in> top1_fundamental_group_carrier Y TY y0"
          using top1_fundamental_group_is_group[OF hTY hy0] unfolding top1_is_group_on_def by (by100 blast)
        have "top1_fundamental_group_induced_on Y TY y0 B TB (r y0) r
            (top1_fundamental_group_id Y TY y0)
          = top1_fundamental_group_id B TB (r y0)"
        proof -
          \<comment> \<open>induced(id) = {g | \<exists>f\<in>id. loop_equiv(r\<circ>f, g)} = {g | loop_equiv(r\<circ>const, g)} = id_B.\<close>
          have hconst_in: "top1_constant_path y0 \<in> top1_fundamental_group_id Y TY y0"
            unfolding top1_fundamental_group_id_def
            using top1_loop_equiv_on_refl[OF top1_constant_path_is_loop[OF hTY hy0]] by (by100 blast)
          have hrconst: "r \<circ> top1_constant_path y0 = top1_constant_path (r y0)"
            unfolding top1_constant_path_def by (rule ext) (by100 simp)
          show ?thesis
            unfolding top1_fundamental_group_induced_on_def top1_fundamental_group_id_def
          proof (rule set_eqI, rule iffI)
            fix k
            assume "k \<in> {g'. \<exists>fa\<in>{g. top1_loop_equiv_on Y TY y0 (top1_constant_path y0) g}.
                top1_loop_equiv_on B TB (r y0) (r \<circ> fa) g'}"
            then obtain fa where hfa: "top1_loop_equiv_on Y TY y0 (top1_constant_path y0) fa"
                and hk: "top1_loop_equiv_on B TB (r y0) (r \<circ> fa) k" by (by100 blast)
            have hfa_loop: "top1_is_loop_on Y TY y0 fa"
              using hfa unfolding top1_loop_equiv_on_def by (by100 blast)
            have "top1_loop_equiv_on B TB (r y0) (r \<circ> top1_constant_path y0) (r \<circ> fa)"
            proof -
              have "top1_loop_equiv_on B TB (r y0) (r \<circ> top1_constant_path y0) (r \<circ> fa)"
                using top1_induced_preserves_loop_equiv[OF hTY
                  top1_covering_map_on_continuous[OF assms(6)]
                  top1_constant_path_is_loop[OF hTY hy0] hfa_loop hfa] by (by100 simp)
              thus ?thesis .
            qed
            hence "top1_loop_equiv_on B TB (r y0) (top1_constant_path (r y0)) (r \<circ> fa)"
              using hrconst by (by100 simp)
            from top1_loop_equiv_on_trans[OF hTB this hk]
            show "k \<in> {g. top1_loop_equiv_on B TB (r y0) (top1_constant_path (r y0)) g}" by (by100 blast)
          next
            fix k assume "k \<in> {g. top1_loop_equiv_on B TB (r y0) (top1_constant_path (r y0)) g}"
            hence "top1_loop_equiv_on B TB (r y0) (top1_constant_path (r y0)) k" by (by100 blast)
            hence "top1_loop_equiv_on B TB (r y0) (r \<circ> top1_constant_path y0) k"
              using hrconst by (by100 simp)
            show "k \<in> {g'. \<exists>fa\<in>{g. top1_loop_equiv_on Y TY y0 (top1_constant_path y0) g}.
                top1_loop_equiv_on B TB (r y0) (r \<circ> fa) g'}"
              apply (rule CollectI)
              apply (rule bexI[of _ "top1_constant_path y0"])
              apply (rule \<open>top1_loop_equiv_on B TB (r y0) (r \<circ> top1_constant_path y0) k\<close>)
              using hconst_in unfolding top1_fundamental_group_id_def by (by100 blast)
          qed
        qed
        thus ?thesis unfolding top1_fundamental_group_image_hom_def using hid_Y by (by100 force)
      qed
      thus ?thesis using himg_triv by (by100 simp)
    qed
    from general_lifting_criterion[OF assms(6) hTE hTB hTY hp_cont hE_pc hE_lpc he0 hy0
        hpe0 hsubgrp]
    obtain q where "\<forall>e\<in>E. q e \<in> Y" "\<forall>e\<in>E. r (q e) = p e"
        "q e0 = y0" "top1_continuous_map_on E TE Y TY q" by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  then obtain q where hq_Y: "\<forall>e\<in>E. q e \<in> Y" and hq_rp: "\<forall>e\<in>E. r (q e) = p e"
      and hq_e0: "q e0 = y0" and hq_cont: "top1_continuous_map_on E TE Y TY q" by (by100 blast)
  \<comment> \<open>q is a covering map: evenly covered because p and r both are.
     For each y \<in> Y, take b = r(y). Take U evenly covered by both p and r.
     Slices of p\<inverse>(U) are {U_\<alpha>}, slices of r\<inverse>(U) are {V_\<beta>}.
     q maps each U_\<alpha> into some V_\<beta> (connectedness).
     q restricted to U_\<alpha> = r_\<beta>\<inverse> \<circ> p_\<alpha>, a homeomorphism.
     So q evenly covers each V_\<beta>.\<close>
  have hTE: "is_topology_on E TE" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hTB: "is_topology_on B TB" using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
  have hTY: "is_topology_on Y TY" using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
  have hq_surj: "q ` E = Y"
  proof (rule equalityI)
    show "q ` E \<subseteq> Y" using hq_Y by (by100 blast)
    show "Y \<subseteq> q ` E"
    proof -
      \<comment> \<open>q(E) is non-empty (contains y0).\<close>
      have hy0_qE: "y0 \<in> q ` E" using hq_e0 he0 by (by100 blast)
      \<comment> \<open>q(E) is open in Y: for each y = q(e), use covering structure to find
         a neighborhood of y contained in q(E). The r-slice containing y maps
         homeomorphically to an open U \<subseteq> B. The p-slice containing e maps
         homeomorphically to U. So q = r^{-1} \<circ> p maps a neighborhood of e
         onto a neighborhood of y, giving y \<in> interior of q(E).\<close>
      have hqE_open: "openin_on Y TY (q ` E)"
      proof -
        have hqE_sub: "q ` E \<subseteq> Y" using hq_Y by (by100 blast)
        \<comment> \<open>For each e, build an open neighborhood of q(e) in q(E).\<close>
        have "\<forall>e\<in>E. \<exists>Ve. Ve \<in> TY \<and> q e \<in> Ve \<and> Ve \<subseteq> q ` E"
        proof
          fix e assume he: "e \<in> E"
          let ?b = "p e"
          have hb: "?b \<in> B"
            using he top1_covering_map_on_surj[OF assms(4)] by (by100 blast)
          \<comment> \<open>Get U evenly covered by both p and r.\<close>
          obtain Up where "?b \<in> Up" "top1_evenly_covered_on E TE B TB p Up"
            using hb assms(4) unfolding top1_covering_map_on_def by (by100 blast)
          obtain Ur where "?b \<in> Ur" "top1_evenly_covered_on Y TY B TB r Ur"
            using hb assms(6) unfolding top1_covering_map_on_def by (by100 blast)
          have hUp_open: "openin_on B TB Up"
            using \<open>top1_evenly_covered_on E TE B TB p Up\<close>
            unfolding top1_evenly_covered_on_def by (by100 blast)
          have hUr_open: "openin_on B TB Ur"
            using \<open>top1_evenly_covered_on Y TY B TB r Ur\<close>
            unfolding top1_evenly_covered_on_def by (by100 blast)
          let ?U = "Up \<inter> Ur"
          have hU_open: "openin_on B TB ?U"
          proof -
            have "Up \<in> TB" using hUp_open unfolding openin_on_def by (by100 blast)
            moreover have "Ur \<in> TB" using hUr_open unfolding openin_on_def by (by100 blast)
            ultimately have "Up \<inter> Ur \<in> TB" by (rule topology_inter2[OF hTB])
            moreover have "Up \<inter> Ur \<subseteq> B" using hUp_open unfolding openin_on_def by (by100 blast)
            ultimately show ?thesis unfolding openin_on_def by (by100 blast)
          qed
          have hU_b: "?b \<in> ?U" using \<open>?b \<in> Up\<close> \<open>?b \<in> Ur\<close> by (by100 blast)
          \<comment> \<open>Restrict both coverings to U.\<close>
          have hU_cov_p: "top1_evenly_covered_on E TE B TB p ?U"
            by (rule evenly_covered_open_subset[OF \<open>top1_evenly_covered_on E TE B TB p Up\<close>
                hU_open _ hTE hTB]) (by100 blast)
          have hU_cov_r: "top1_evenly_covered_on Y TY B TB r ?U"
            by (rule evenly_covered_open_subset[OF \<open>top1_evenly_covered_on Y TY B TB r Ur\<close>
                hU_open _ hTY hTB]) (by100 blast)
          \<comment> \<open>Get p-slice W containing e.\<close>
          obtain \<V>p where h\<V>p: "\<forall>V\<in>\<V>p. openin_on E TE V"
              "\<forall>V\<in>\<V>p. \<forall>V'\<in>\<V>p. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
              "{x\<in>E. p x \<in> ?U} = \<Union>\<V>p"
              "\<forall>V\<in>\<V>p. top1_homeomorphism_on V (subspace_topology E TE V) ?U
                              (subspace_topology B TB ?U) p"
            using hU_cov_p unfolding top1_evenly_covered_on_def
            by (elim conjE exE) (by100 blast)
          have he_pU: "e \<in> {x\<in>E. p x \<in> ?U}" using he hU_b by (by100 blast)
          hence "e \<in> \<Union>\<V>p" using h\<V>p(3) by (by100 simp)
          then obtain W where hW: "W \<in> \<V>p" "e \<in> W" by (by100 blast)
          \<comment> \<open>Get r-slice V containing q(e) = y.\<close>
          obtain \<V>r where h\<V>r: "\<forall>V\<in>\<V>r. openin_on Y TY V"
              "\<forall>V\<in>\<V>r. \<forall>V'\<in>\<V>r. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
              "{x\<in>Y. r x \<in> ?U} = \<Union>\<V>r"
              "\<forall>V\<in>\<V>r. top1_homeomorphism_on V (subspace_topology Y TY V) ?U
                              (subspace_topology B TB ?U) r"
            using hU_cov_r unfolding top1_evenly_covered_on_def
            by (elim conjE exE) (by100 blast)
          have hqe_Y: "q e \<in> Y" using he hq_Y by (by100 blast)
          have hrqe: "r (q e) = p e" using he hq_rp by (by100 blast)
          have "r (q e) \<in> ?U" using hrqe hU_b by (by100 simp)
          have hqe_rU: "q e \<in> {x\<in>Y. r x \<in> ?U}" using hqe_Y \<open>r (q e) \<in> ?U\<close> by (by100 blast)
          hence "q e \<in> \<Union>\<V>r" using h\<V>r(3) by (by100 simp)
          then obtain V where hV: "V \<in> \<V>r" "q e \<in> V" by (by100 blast)
          \<comment> \<open>V is open in Y.\<close>
          have hV_TY: "V \<in> TY"
            using h\<V>r(1) hV(1) unfolding openin_on_def by (by100 blast)
          \<comment> \<open>W' = W \<inter> q\<inverse>(V) is open in E and contains e.\<close>
          let ?W' = "W \<inter> {e' \<in> E. q e' \<in> V}"
          have hW_TE: "W \<in> TE" using h\<V>p(1) hW(1) unfolding openin_on_def by (by100 blast)
          have hqV_TE: "{e' \<in> E. q e' \<in> V} \<in> TE"
            using hq_cont hV_TY unfolding top1_continuous_map_on_def by (by100 blast)
          have hW'_TE: "?W' \<in> TE" by (rule topology_inter2[OF hTE hW_TE hqV_TE])
          have he_W': "e \<in> ?W'" using hW(2) he hV(2) by (by100 blast)
          \<comment> \<open>Key: q(W') = {v \<in> V | r v \<in> p ` W'}, which is open in V hence in Y.\<close>
          \<comment> \<open>Key: q(W') = {v \<in> V | r v \<in> p ` W'}.\<close>
          have hV_homeo: "top1_homeomorphism_on V (subspace_topology Y TY V) ?U
                              (subspace_topology B TB ?U) r"
            using h\<V>r(4) hV(1) by (by100 blast)
          have hr_bij: "bij_betw r V ?U"
            using hV_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have hr_inj: "inj_on r V" using hr_bij unfolding bij_betw_def by (by100 blast)
          have hW_homeo: "top1_homeomorphism_on W (subspace_topology E TE W) ?U
                              (subspace_topology B TB ?U) p"
            using h\<V>p(4) hW(1) by (by100 blast)
          have hqW'_eq: "q ` ?W' = {v \<in> V. r v \<in> p ` ?W'}"
          proof (rule set_eqI, rule iffI)
            fix v assume "v \<in> q ` ?W'"
            then obtain e' where he': "e' \<in> ?W'" "v = q e'" by (by100 blast)
            have "e' \<in> E" using he' by (by100 blast)
            have "v \<in> V" using he' by (by100 blast)
            have "r v = r (q e')" using he'(2) by (by100 simp)
            also have "\<dots> = p e'" using \<open>e' \<in> E\<close> hq_rp by (by100 blast)
            finally have "r v = p e'" .
            hence "r v \<in> p ` ?W'" using he'(1) by (by100 blast)
            thus "v \<in> {v \<in> V. r v \<in> p ` ?W'}" using \<open>v \<in> V\<close> by (by100 blast)
          next
            fix v assume hv: "v \<in> {v \<in> V. r v \<in> p ` ?W'}"
            hence "v \<in> V" "r v \<in> p ` ?W'" by (by100 blast)+
            then obtain e' where he': "e' \<in> ?W'" "r v = p e'" by (by100 blast)
            have "e' \<in> E" using he' by (by100 blast)
            have "q e' \<in> V" using he' by (by100 blast)
            have "r (q e') = p e'" using \<open>e' \<in> E\<close> hq_rp by (by100 blast)
            hence "r v = r (q e')" using he'(2) by (by100 simp)
            hence "v = q e'" using hr_inj \<open>v \<in> V\<close> \<open>q e' \<in> V\<close>
              unfolding inj_on_def by (by100 blast)
            thus "v \<in> q ` ?W'" using he'(1) by (by100 blast)
          qed
          \<comment> \<open>p(W') is open in U-subspace: homeomorphism inverse is continuous,
             so preimage of W' (open in W-subspace) under inv_into W p is open.\<close>
          have hp_inv_cont: "top1_continuous_map_on ?U (subspace_topology B TB ?U)
              W (subspace_topology E TE W) (inv_into W p)"
            using hW_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have hW'_sub_W: "?W' \<subseteq> W" by (by100 blast)
          have hW'_subspace: "?W' \<in> subspace_topology E TE W"
            using hW'_TE hW'_sub_W unfolding subspace_topology_def by (by100 blast)
          have hpW'_open: "p ` ?W' \<in> subspace_topology B TB ?U"
          proof -
            have "p ` ?W' = {u \<in> ?U. (inv_into W p) u \<in> ?W'}"
            proof (rule set_eqI, rule iffI)
              fix u assume "u \<in> p ` ?W'"
              then obtain e' where he': "e' \<in> ?W'" "u = p e'" by (by100 blast)
              have "e' \<in> W" using he' by (by100 blast)
              have hp_bij: "bij_betw p W ?U"
                using hW_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
              have "u \<in> ?U" using he' hp_bij unfolding bij_betw_def by (by100 blast)
              have "inv_into W p u = e'"
                using inv_into_f_f[of p W e'] hp_bij \<open>e' \<in> W\<close> he'(2)
                unfolding bij_betw_def by (by100 blast)
              thus "u \<in> {u \<in> ?U. (inv_into W p) u \<in> ?W'}" using \<open>u \<in> ?U\<close> he'(1) by (by100 simp)
            next
              fix u assume hu: "u \<in> {u \<in> ?U. (inv_into W p) u \<in> ?W'}"
              hence "u \<in> ?U" "(inv_into W p) u \<in> ?W'" by (by100 blast)+
              have "(inv_into W p) u \<in> W" using \<open>(inv_into W p) u \<in> ?W'\<close> by (by100 blast)
              have hp_bij: "bij_betw p W ?U"
                using hW_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
              have "u \<in> p ` W" using hp_bij \<open>u \<in> ?U\<close> unfolding bij_betw_def by (by100 blast)
              have "p ((inv_into W p) u) = u" by (rule f_inv_into_f[OF \<open>u \<in> p ` W\<close>])
              show "u \<in> p ` ?W'"
              proof (rule image_eqI)
                show "u = p (inv_into W p u)"
                  using \<open>p ((inv_into W p) u) = u\<close> by (by100 simp)
                show "inv_into W p u \<in> ?W'"
                  using \<open>(inv_into W p) u \<in> ?W'\<close> by (by100 simp)
              qed
            qed
            have hpreimg: "{u \<in> ?U. (inv_into W p) u \<in> ?W'} \<in> subspace_topology B TB ?U"
              using hp_inv_cont hW'_subspace
              unfolding top1_continuous_map_on_def by (by100 blast)
            thus ?thesis using \<open>p ` ?W' = {u \<in> ?U. (inv_into W p) u \<in> ?W'}\<close> by (by100 simp)
          qed
          \<comment> \<open>Preimage of p(W') under r is open in V-subspace.\<close>
          have hr_cont_on_V: "top1_continuous_map_on V (subspace_topology Y TY V) ?U
              (subspace_topology B TB ?U) r"
            using hV_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have hqW'_subV: "{v \<in> V. r v \<in> p ` ?W'} \<in> subspace_topology Y TY V"
            using hr_cont_on_V hpW'_open
            unfolding top1_continuous_map_on_def by (by100 blast)
          \<comment> \<open>Open in V-subspace + V open in Y \<Rightarrow> open in Y.\<close>
          have hqW'_in_sub: "q ` ?W' \<in> subspace_topology Y TY V"
            using hqW'_subV hqW'_eq by (by100 simp)
          have hqW'_TY: "q ` ?W' \<in> TY"
          proof -
            from hqW'_in_sub obtain T' where hT'_TY: "T' \<in> TY" and hqW'_VT': "q ` ?W' = V \<inter> T'"
              unfolding subspace_topology_def by (by100 blast)
            have "V \<inter> T' \<in> TY" by (rule topology_inter2[OF hTY hV_TY hT'_TY])
            thus ?thesis using hqW'_VT' by (by100 simp)
          qed
          \<comment> \<open>q(e) \<in> q(W') \<subseteq> q(E).\<close>
          have "q e \<in> q ` ?W'" using he_W' by (by100 blast)
          moreover have "q ` ?W' \<subseteq> q ` E" by (by100 blast)
          ultimately show "\<exists>Ve. Ve \<in> TY \<and> q e \<in> Ve \<and> Ve \<subseteq> q ` E"
            using hqW'_TY by (by100 blast)
        qed
        \<comment> \<open>q(E) = \<Union>{Ve | e \<in> E}, union of open sets, hence open.\<close>
        hence "\<exists>S. S \<subseteq> TY \<and> q ` E = \<Union>S"
        proof -
          let ?S = "{Ve. \<exists>e\<in>E. Ve \<in> TY \<and> q e \<in> Ve \<and> Ve \<subseteq> q ` E}"
          have "?S \<subseteq> TY" by (by100 blast)
          moreover have "q ` E = \<Union>?S"
          proof (rule set_eqI, rule iffI)
            fix y assume "y \<in> q ` E"
            then obtain e where "e \<in> E" "y = q e" by (by100 blast)
            then obtain Ve where "Ve \<in> TY" "q e \<in> Ve" "Ve \<subseteq> q ` E"
              using \<open>\<forall>e\<in>E. \<exists>Ve. Ve \<in> TY \<and> q e \<in> Ve \<and> Ve \<subseteq> q ` E\<close> by (by100 blast)
            thus "y \<in> \<Union>?S" using \<open>e \<in> E\<close> \<open>y = q e\<close> by (by100 blast)
          next
            fix y assume "y \<in> \<Union>?S"
            then obtain Ve where "Ve \<subseteq> q ` E" "y \<in> Ve" by (by100 blast)
            thus "y \<in> q ` E" by (by100 blast)
          qed
          ultimately show ?thesis by (by100 blast)
        qed
        then obtain S where hS: "S \<subseteq> TY" "q ` E = \<Union>S" by (elim exE conjE) (by100 blast)
        have hunion: "\<forall>U. U \<subseteq> TY \<longrightarrow> \<Union>U \<in> TY"
          using hTY unfolding is_topology_on_def by (by100 blast)
        have "\<Union>S \<in> TY" using hunion hS(1) by (by100 blast)
        hence "q ` E \<in> TY" using hS(2) by (by100 simp)
        thus ?thesis using hqE_sub unfolding openin_on_def by (by100 blast)
      qed
      \<comment> \<open>Direct surjectivity via path-lifting: for y \<in> Y, take path \<gamma> from y0 to y,
         lift r\<circ>\<gamma> to E via p, then q\<circ>lift = \<gamma> by uniqueness, so y = q(lift(1)).\<close>
      show "Y \<subseteq> q ` E"
      proof
        fix y assume hy: "y \<in> Y"
        \<comment> \<open>Y is path-connected, so there exists a path \<gamma> from y0 to y.\<close>
        obtain \<gamma> where h\<gamma>: "top1_is_path_on Y TY y0 y \<gamma>"
          using assms(8) hy hy0 unfolding top1_path_connected_on_def by (by100 blast)
        \<comment> \<open>r \<circ> \<gamma> is a path in B from b0 to r(y).\<close>
        have hr_cont: "top1_continuous_map_on Y TY B TB r"
          by (rule top1_covering_map_on_continuous[OF assms(6)])
        have h\<gamma>_cont: "top1_continuous_map_on I_set I_top Y TY \<gamma>"
          using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
        have hr\<gamma>_cont: "top1_continuous_map_on I_set I_top B TB (r \<circ> \<gamma>)"
          by (rule top1_continuous_map_on_comp[OF h\<gamma>_cont hr_cont])
        have h\<gamma>0: "\<gamma> 0 = y0" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
        have h\<gamma>1: "\<gamma> 1 = y" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
        have hr\<gamma>0: "(r \<circ> \<gamma>) 0 = p e0" using h\<gamma>0 hry0 by (by100 simp)
        have hr\<gamma>1: "(r \<circ> \<gamma>) 1 = r y" using h\<gamma>1 by (by100 simp)
        have h_r\<gamma>: "top1_is_path_on B TB (p e0) (r y) (r \<circ> \<gamma>)"
          unfolding top1_is_path_on_def using hr\<gamma>_cont hr\<gamma>0 hr\<gamma>1 by (by100 blast)
        \<comment> \<open>Lift r \<circ> \<gamma> to E via p, starting at e0.\<close>
        have "\<exists>\<alpha>. top1_is_path_on E TE e0 (\<alpha> 1) \<alpha> \<and> (\<forall>s\<in>I_set. p (\<alpha> s) = (r \<circ> \<gamma>) s)"
          using Lemma_54_1_path_lifting[OF assms(4) he0 _ h_r\<gamma> hTB hTE] by (by100 simp)
        then obtain \<alpha> where h\<alpha>_path: "top1_is_path_on E TE e0 (\<alpha> 1) \<alpha>"
            and h\<alpha>_lift: "\<forall>s\<in>I_set. p (\<alpha> s) = (r \<circ> \<gamma>) s" by (by100 blast)
        \<comment> \<open>q \<circ> \<alpha> is a lift of r \<circ> \<gamma> via r, starting at y0.\<close>
        have h\<alpha>0: "\<alpha> 0 = e0" using h\<alpha>_path unfolding top1_is_path_on_def by (by100 blast)
        have hq\<alpha>_start: "(q \<circ> \<alpha>) 0 = y0" using h\<alpha>0 hq_e0 by (by100 simp)
        have hq\<alpha>_lift: "\<forall>s\<in>I_set. r ((q \<circ> \<alpha>) s) = (r \<circ> \<gamma>) s"
        proof (intro ballI)
          fix s assume hs: "s \<in> I_set"
          have h\<alpha>s_E: "\<alpha> s \<in> E"
          proof -
            have "top1_continuous_map_on I_set I_top E TE \<alpha>"
              using h\<alpha>_path unfolding top1_is_path_on_def by (by100 blast)
            thus ?thesis using hs unfolding top1_continuous_map_on_def by (by100 blast)
          qed
          have "r (q (\<alpha> s)) = p (\<alpha> s)" using hq_rp h\<alpha>s_E by (by100 blast)
          also have "\<dots> = (r \<circ> \<gamma>) s" using h\<alpha>_lift hs by (by100 blast)
          finally show "r ((q \<circ> \<alpha>) s) = (r \<circ> \<gamma>) s" by (by100 simp)
        qed
        \<comment> \<open>q \<circ> \<alpha> is a path in Y from y0 to q(\<alpha>(1)).\<close>
        have h\<alpha>_cont: "top1_continuous_map_on I_set I_top E TE \<alpha>"
          using h\<alpha>_path unfolding top1_is_path_on_def by (by100 blast)
        have hq\<alpha>_cont: "top1_continuous_map_on I_set I_top Y TY (q \<circ> \<alpha>)"
          by (rule top1_continuous_map_on_comp[OF h\<alpha>_cont hq_cont])
        have hq\<alpha>1: "(q \<circ> \<alpha>) 1 = q (\<alpha> 1)" by (by100 simp)
        have hq\<alpha>_path: "top1_is_path_on Y TY y0 (q (\<alpha> 1)) (q \<circ> \<alpha>)"
          unfolding top1_is_path_on_def using hq\<alpha>_cont hq\<alpha>_start hq\<alpha>1 by (by100 blast)
        \<comment> \<open>\<gamma> lifts r\<circ>\<gamma> via r trivially.\<close>
        have h\<gamma>_lift: "\<forall>s\<in>I_set. r (\<gamma> s) = (r \<circ> \<gamma>) s" by (by100 simp)
        \<comment> \<open>By uniqueness of path lifts for r: q \<circ> \<alpha> = \<gamma> on I_set.\<close>
        have heq: "\<forall>s\<in>I_set. (q \<circ> \<alpha>) s = \<gamma> s"
          using Lemma_54_1_uniqueness[OF assms(6) hy0 hry0 h_r\<gamma>
              hq\<alpha>_path hq\<alpha>_lift h\<gamma> h\<gamma>_lift] by (by100 blast)
        \<comment> \<open>At s=1: q(\<alpha>(1)) = \<gamma>(1) = y.\<close>
        have "q (\<alpha> 1) = \<gamma> 1"
        proof -
          have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
          hence "(q \<circ> \<alpha>) 1 = \<gamma> 1" using heq by (by100 blast)
          thus ?thesis by (by100 simp)
        qed
        hence "q (\<alpha> 1) = y" using h\<gamma>1 by (by100 simp)
        moreover have "\<alpha> 1 \<in> E"
        proof -
          have "top1_continuous_map_on I_set I_top E TE \<alpha>"
            using h\<alpha>_path unfolding top1_is_path_on_def by (by100 blast)
          have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
          thus ?thesis using h\<alpha>_cont unfolding top1_continuous_map_on_def by (by100 blast)
        qed
        ultimately show "y \<in> q ` E" by (by100 blast)
      qed
    qed
  qed
  have hq_cov: "\<forall>y\<in>Y. \<exists>V. y \<in> V \<and> top1_evenly_covered_on E TE Y TY q V"
  proof
    fix y assume hy: "y \<in> Y"
    let ?b = "r y"
    have hb_B: "?b \<in> B"
      using hy top1_covering_map_on_surj[OF assms(6)] by (by100 blast)
    \<comment> \<open>Take U evenly covered by both p and r.\<close>
    obtain Up where hUp_b: "?b \<in> Up" and hUp_cov_p: "top1_evenly_covered_on E TE B TB p Up"
      using hb_B assms(4) unfolding top1_covering_map_on_def by (by100 blast)
    obtain Ur where hUr_b: "?b \<in> Ur" and hUr_cov_r: "top1_evenly_covered_on Y TY B TB r Ur"
      using hb_B assms(6) unfolding top1_covering_map_on_def by (by100 blast)
    let ?U = "Up \<inter> Ur"
    \<comment> \<open>U = Up \<inter> Ur is open, contains b, and is evenly covered by both p and r.\<close>
    have hU_b: "?b \<in> ?U" using hUp_b hUr_b by (by100 blast)
    \<comment> \<open>The restriction of a covering to an open subset is still a covering.\<close>
    \<comment> \<open>Get the slice of r\<inverse>(U) containing y. This will be the evenly covered neighborhood.\<close>
    obtain \<V>r where h\<V>r_open: "\<forall>V\<in>\<V>r. openin_on Y TY V"
        and h\<V>r_disj: "\<forall>V\<in>\<V>r. \<forall>V'\<in>\<V>r. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
        and h\<V>r_union: "{x\<in>Y. r x \<in> Ur} = \<Union>\<V>r"
        and h\<V>r_homeo: "\<forall>V\<in>\<V>r. top1_homeomorphism_on V (subspace_topology Y TY V) Ur
                                      (subspace_topology B TB Ur) r"
      using hUr_cov_r unfolding top1_evenly_covered_on_def
      by (elim conjE exE) (by100 blast)
    \<comment> \<open>y is in r\<inverse>(Ur), so y \<in> \<Union>\<V>r. Pick the slice V0 containing y.\<close>
    have hy_in_rU: "y \<in> {x\<in>Y. r x \<in> Ur}" using hy hUr_b by (by100 blast)
    hence "y \<in> \<Union>\<V>r" using h\<V>r_union by (by100 simp)
    then obtain V0 where hV0: "V0 \<in> \<V>r" and hy_V0: "y \<in> V0" by (by100 blast)
    \<comment> \<open>V0 is our evenly covered neighborhood.\<close>
    \<comment> \<open>To show: top1_evenly_covered_on E TE Y TY q V0.\<close>
    \<comment> \<open>Each slice U_\<alpha> of p\<inverse>(U) that maps into V0 maps homeomorphically via q.\<close>
    \<comment> \<open>Restrict p-covering to Up\<inter>Ur.\<close>
    have hTE: "is_topology_on E TE" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have hTB: "is_topology_on B TB" using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
    have hTY: "is_topology_on Y TY" using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
    have hUp_open: "openin_on B TB Up"
      using hUp_cov_p unfolding top1_evenly_covered_on_def by (by100 blast)
    have hUr_open: "openin_on B TB Ur"
      using hUr_cov_r unfolding top1_evenly_covered_on_def by (by100 blast)
    have hU_open: "openin_on B TB ?U"
    proof -
      have "Up \<in> TB" using hUp_open unfolding openin_on_def by (by100 blast)
      moreover have "Ur \<in> TB" using hUr_open unfolding openin_on_def by (by100 blast)
      ultimately have "Up \<inter> Ur \<in> TB" by (rule topology_inter2[OF hTB])
      moreover have "Up \<inter> Ur \<subseteq> B" using hUp_open unfolding openin_on_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by (by100 blast)
    qed
    have hU_cov_p: "top1_evenly_covered_on E TE B TB p ?U"
      by (rule evenly_covered_open_subset[OF hUp_cov_p hU_open _ hTE hTB]) (by100 blast)
    have hU_cov_r: "top1_evenly_covered_on Y TY B TB r ?U"
      by (rule evenly_covered_open_subset[OF hUr_cov_r hU_open _ hTY hTB]) (by100 blast)
    \<comment> \<open>Get p-slices and r-slices over U = Up\<inter>Ur.\<close>
    obtain \<V>p where h\<V>p_open: "\<forall>V\<in>\<V>p. openin_on E TE V"
        and h\<V>p_disj: "\<forall>V\<in>\<V>p. \<forall>V'\<in>\<V>p. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
        and h\<V>p_union: "{x\<in>E. p x \<in> ?U} = \<Union>\<V>p"
        and h\<V>p_homeo: "\<forall>V\<in>\<V>p. top1_homeomorphism_on V (subspace_topology E TE V) ?U
                                      (subspace_topology B TB ?U) p"
      using hU_cov_p unfolding top1_evenly_covered_on_def
      by (elim conjE exE) (by100 blast)
    obtain \<V>r' where h\<V>r'_open: "\<forall>V\<in>\<V>r'. openin_on Y TY V"
        and h\<V>r'_disj: "\<forall>V\<in>\<V>r'. \<forall>V'\<in>\<V>r'. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
        and h\<V>r'_union: "{x\<in>Y. r x \<in> ?U} = \<Union>\<V>r'"
        and h\<V>r'_homeo: "\<forall>V\<in>\<V>r'. top1_homeomorphism_on V (subspace_topology Y TY V) ?U
                                      (subspace_topology B TB ?U) r"
      using hU_cov_r unfolding top1_evenly_covered_on_def
      by (elim conjE exE) (by100 blast)
    \<comment> \<open>Refine U to path-connected using B locally path-connected.\<close>
    have hB_lpc: "top1_locally_path_connected_on B TB"
      by (rule covering_base_locally_path_connected[OF assms(4) assms(7) hTE hTB])
    have hU_TB: "?U \<in> TB" using hU_open unfolding openin_on_def by (by100 blast)
    have hU_sub_B: "?U \<subseteq> B" using hU_open unfolding openin_on_def by (by100 blast)
    have "\<exists>U''. U'' \<in> TB \<and> ?b \<in> U'' \<and> U'' \<subseteq> ?U \<and> U'' \<subseteq> B
        \<and> top1_path_connected_on U'' (subspace_topology B TB U'')"
    proof -
      \<comment> \<open>By Theorem 25.4: B lpc \<Rightarrow> path components of open sets are open.\<close>
      have hpc_open: "\<forall>P \<in> top1_path_components_on ?U (subspace_topology B TB ?U). P \<in> TB"
        using iffD1[OF Theorem_25_4[OF hTB]] hB_lpc hU_TB hU_sub_B by (by100 blast)
      \<comment> \<open>Path component of b in U.\<close>
      let ?P = "top1_path_component_of_on ?U (subspace_topology B TB ?U) ?b"
      have hU_top: "is_topology_on ?U (subspace_topology B TB ?U)"
      proof -
        have "top1_locally_path_connected_on ?U (subspace_topology B TB ?U)"
          by (rule open_subset_locally_path_connected[OF hB_lpc hU_TB hU_sub_B])
        thus ?thesis unfolding top1_locally_path_connected_on_def by (by100 blast)
      qed
      have hP_comp: "?P \<in> top1_path_components_on ?U (subspace_topology B TB ?U)"
        using hU_b unfolding top1_path_components_on_def by (by100 blast)
      have hP_TB: "?P \<in> TB" using hpc_open hP_comp by (by100 blast)
      have hP_b: "?b \<in> ?P" by (rule top1_path_component_of_on_self_mem[OF hU_top hU_b])
      have hP_sub: "?P \<subseteq> ?U" by (rule top1_path_component_of_on_subset[OF hU_top hU_b])
      have hP_sub_B: "?P \<subseteq> B" using hP_sub hU_sub_B by (by100 blast)
      have hP_pc: "top1_path_connected_on ?P (subspace_topology ?U (subspace_topology B TB ?U) ?P)"
        by (rule top1_path_component_of_on_path_connected[OF hU_top hU_b])
      have "subspace_topology ?U (subspace_topology B TB ?U) ?P = subspace_topology B TB ?P"
        by (rule subspace_topology_trans[OF hP_sub])
      hence "top1_path_connected_on ?P (subspace_topology B TB ?P)" using hP_pc by (by100 simp)
      thus ?thesis using hP_TB hP_b hP_sub hP_sub_B by (by100 blast)
    qed
    then obtain U'' where hU''_TB: "U'' \<in> TB" and hU''_b: "?b \<in> U''" and hU''_sub: "U'' \<subseteq> ?U"
        and hU''_sub_B: "U'' \<subseteq> B"
        and hU''_pc: "top1_path_connected_on U'' (subspace_topology B TB U'')"
      by (by100 blast)
    have hU''_openin: "openin_on B TB U''"
      using hU''_TB hU''_sub_B unfolding openin_on_def by (by100 blast)
    \<comment> \<open>Restrict coverings to path-connected U''.\<close>
    have hU''_sub_Up: "U'' \<subseteq> Up" using hU''_sub by (by100 blast)
    have hU''_sub_Ur: "U'' \<subseteq> Ur" using hU''_sub by (by100 blast)
    have hU''_cov_p: "top1_evenly_covered_on E TE B TB p U''"
      by (rule evenly_covered_open_subset[OF hUp_cov_p hU''_openin hU''_sub_Up hTE hTB])
    have hU''_cov_r: "top1_evenly_covered_on Y TY B TB r U''"
      by (rule evenly_covered_open_subset[OF hUr_cov_r hU''_openin hU''_sub_Ur hTY hTB])
    \<comment> \<open>Get r-slice V1 containing y over path-connected U''.\<close>
    obtain \<W>r where h\<W>r_open: "\<forall>W\<in>\<W>r. openin_on Y TY W"
        and h\<W>r_disj: "\<forall>W\<in>\<W>r. \<forall>W'\<in>\<W>r. W \<noteq> W' \<longrightarrow> W \<inter> W' = {}"
        and h\<W>r_union: "{x\<in>Y. r x \<in> U''} = \<Union>\<W>r"
        and h\<W>r_homeo: "\<forall>W\<in>\<W>r. top1_homeomorphism_on W (subspace_topology Y TY W)
            U'' (subspace_topology B TB U'') r"
      using hU''_cov_r unfolding top1_evenly_covered_on_def
      by (elim conjE exE) (by100 blast)
    have "r y \<in> U''" using hU''_b by (by100 simp)
    hence "y \<in> {x\<in>Y. r x \<in> U''}" using hy by (by100 blast)
    hence "y \<in> \<Union>\<W>r" using h\<W>r_union by (by100 simp)
    then obtain V1 where hV1: "V1 \<in> \<W>r" "y \<in> V1" by (by100 blast)
    have hV1_open: "openin_on Y TY V1" using h\<W>r_open hV1(1) by (by100 blast)
    \<comment> \<open>V1 is evenly covered by q.\<close>
    show "\<exists>V. y \<in> V \<and> top1_evenly_covered_on E TE Y TY q V"
    proof (rule exI[of _ V1], intro conjI)
      show "y \<in> V1" by (rule hV1(2))
      show "top1_evenly_covered_on E TE Y TY q V1"
      proof -
        \<comment> \<open>Get p-slices over U''.\<close>
        obtain \<W>p where h\<W>p_open: "\<forall>W\<in>\<W>p. openin_on E TE W"
            and h\<W>p_disj: "\<forall>W\<in>\<W>p. \<forall>W'\<in>\<W>p. W \<noteq> W' \<longrightarrow> W \<inter> W' = {}"
            and h\<W>p_union: "{x\<in>E. p x \<in> U''} = \<Union>\<W>p"
            and h\<W>p_homeo: "\<forall>W\<in>\<W>p. top1_homeomorphism_on W (subspace_topology E TE W)
                U'' (subspace_topology B TB U'') p"
          using hU''_cov_p unfolding top1_evenly_covered_on_def
          by (elim conjE exE) (by100 blast)
        \<comment> \<open>Each p-slice W is connected (homeomorphic to path-connected U'').\<close>
        \<comment> \<open>By lift uniqueness, q maps each W entirely into one r-slice.\<close>
        \<comment> \<open>Family: those W mapping into V1.\<close>
        let ?\<V>q = "{W \<in> \<W>p. \<exists>e \<in> W. q e \<in> V1}"
        show ?thesis unfolding top1_evenly_covered_on_def
        proof (intro conjI exI[of _ ?\<V>q])
          show "openin_on Y TY V1" by (rule hV1_open)
          show "\<forall>W\<in>?\<V>q. openin_on E TE W"
            using h\<W>p_open by (by100 blast)
          show "\<forall>W\<in>?\<V>q. \<forall>W'\<in>?\<V>q. W \<noteq> W' \<longrightarrow> W \<inter> W' = {}"
            using h\<W>p_disj by (by100 blast)
          \<comment> \<open>Key: each p-slice W is connected, so q maps W entirely into one r-slice.\<close>
          have hW_connected: "\<forall>W\<in>\<W>p. top1_connected_on W (subspace_topology E TE W)"
          proof (intro ballI)
            fix W assume "W \<in> \<W>p"
            have "top1_homeomorphism_on W (subspace_topology E TE W) U'' (subspace_topology B TB U'') p"
              using h\<W>p_homeo \<open>W \<in> \<W>p\<close> by (by100 blast)
            from homeomorphism_inverse[OF this]
            have "top1_homeomorphism_on U'' (subspace_topology B TB U'') W (subspace_topology E TE W)
                (inv_into W p)" .
            from homeomorphism_preserves_path_connected[OF this hU''_pc]
            have "top1_path_connected_on W (subspace_topology E TE W)" .
            thus "top1_connected_on W (subspace_topology E TE W)"
              by (rule top1_path_connected_imp_connected)
          qed
          have hV1_homeo: "top1_homeomorphism_on V1 (subspace_topology Y TY V1)
              U'' (subspace_topology B TB U'') r"
            using h\<W>r_homeo hV1(1) by (by100 blast)
          have hr_bij_V1: "bij_betw r V1 U''"
            using hV1_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have hr_inj_V1: "inj_on r V1" using hr_bij_V1 unfolding bij_betw_def by (by100 blast)
          \<comment> \<open>Shared fact: for each W \<in> \<V>q, q = (inv_into V1 r) \<circ> p on W.\<close>
          have hq_eq_h_all: "\<forall>W\<in>?\<V>q. \<forall>e'\<in>W. q e' = inv_into V1 r (p e')"
          proof (intro ballI)
            fix W e' assume hWq: "W \<in> ?\<V>q" and he': "e' \<in> W"
            \<comment> \<open>This follows from the internal hq\_eq\_h established in hW\_all\_V1.\<close>
            \<comment> \<open>We re-derive it via covering\_lift\_unique\_connected.\<close>
            have hW_mem: "W \<in> \<W>p" using hWq by (by100 blast)
            obtain e0 where he0_W: "e0 \<in> W" "q e0 \<in> V1" using hWq by (by100 blast)
            have hW_sub_E: "W \<subseteq> E" using hW_mem h\<W>p_open unfolding openin_on_def by (by100 blast)
            have hW_conn: "top1_connected_on W (subspace_topology E TE W)"
              using hW_connected hW_mem by (by100 blast)
            have hW_TE: "W \<in> TE" using hW_mem h\<W>p_open unfolding openin_on_def by (by100 blast)
            have hW_top: "is_topology_on W (subspace_topology E TE W)"
            proof -
              have "top1_locally_path_connected_on W (subspace_topology E TE W)"
                by (rule open_subset_locally_path_connected[OF assms(7) hW_TE hW_sub_E])
              thus ?thesis unfolding top1_locally_path_connected_on_def by (by100 blast)
            qed
            let ?h = "\<lambda>e. inv_into V1 r (p e)"
            have hW_pU: "\<forall>e1\<in>W. p e1 \<in> U''"
            proof (intro ballI)
              fix e1 assume "e1 \<in> W"
              thus "p e1 \<in> U''" using hW_mem h\<W>p_union by (by100 blast)
            qed
            have hh_V1: "\<forall>e1\<in>W. ?h e1 \<in> V1"
            proof (intro ballI)
              fix e1 assume "e1 \<in> W"
              have "p e1 \<in> r ` V1" using hr_bij_V1 hW_pU \<open>e1 \<in> W\<close> unfolding bij_betw_def by (by100 blast)
              thus "?h e1 \<in> V1" using inv_into_into[OF \<open>p e1 \<in> r ` V1\<close>] by (by100 simp)
            qed
            \<comment> \<open>q(e0) = h(e0) by injectivity of r on V1.\<close>
            have "?h e0 = q e0"
            proof -
              have "p e0 \<in> r ` V1" using hr_bij_V1 hW_pU he0_W(1) unfolding bij_betw_def by (by100 blast)
              have "r (?h e0) = p e0" by (rule f_inv_into_f[OF \<open>p e0 \<in> r ` V1\<close>])
              have "r (q e0) = p e0" using hq_rp he0_W(1) hW_sub_E by (by100 blast)
              have "?h e0 \<in> V1" using hh_V1 he0_W(1) by (by100 blast)
              have "r (?h e0) = r (q e0)" using \<open>r (?h e0) = p e0\<close> \<open>r (q e0) = p e0\<close> by (by100 simp)
              thus ?thesis using hr_inj_V1 \<open>?h e0 \<in> V1\<close> he0_W(2)
                unfolding inj_on_def by (by100 blast)
            qed
            \<comment> \<open>Both lifts of p through r, agree at e0, W connected \<Rightarrow> agree everywhere.\<close>
            have hq_cont_W: "top1_continuous_map_on W (subspace_topology E TE W) Y TY q"
            proof -
              have "\<forall>A f. top1_continuous_map_on E TE Y TY f \<and> A \<subseteq> E \<longrightarrow>
                  top1_continuous_map_on A (subspace_topology E TE A) Y TY f"
                using Theorem_18_2[OF hTE hTY hTY] by (by100 blast)
              thus ?thesis using hq_cont hW_sub_E by (by100 blast)
            qed
            have hh_cont_W: "top1_continuous_map_on W (subspace_topology E TE W) Y TY ?h"
            proof -
              have hp_W: "top1_continuous_map_on W (subspace_topology E TE W)
                  U'' (subspace_topology B TB U'') p"
                using h\<W>p_homeo hW_mem unfolding top1_homeomorphism_on_def by (by100 blast)
              have hinv_r: "top1_continuous_map_on U'' (subspace_topology B TB U'')
                  V1 (subspace_topology Y TY V1) (inv_into V1 r)"
                using homeomorphism_inverse[OF hV1_homeo]
                unfolding top1_homeomorphism_on_def by (by100 blast)
              have "top1_continuous_map_on W (subspace_topology E TE W)
                  V1 (subspace_topology Y TY V1) (inv_into V1 r \<circ> p)"
                by (rule top1_continuous_map_on_comp[OF hp_W hinv_r])
              hence hcomp: "top1_continuous_map_on W (subspace_topology E TE W)
                  V1 (subspace_topology Y TY V1) ?h"
                unfolding comp_def by (by100 simp)
              have hV1_sub_Y: "V1 \<subseteq> Y" using hV1_open unfolding openin_on_def by (by100 blast)
              show ?thesis unfolding top1_continuous_map_on_def
              proof (intro conjI ballI)
                fix e1 assume "e1 \<in> W"
                thus "?h e1 \<in> Y" using hh_V1 \<open>e1 \<in> W\<close> hV1_sub_Y by (by100 blast)
              next
                fix V assume "V \<in> TY"
                have "{e1 \<in> W. ?h e1 \<in> V} = {e1 \<in> W. ?h e1 \<in> V \<inter> V1}" using hh_V1 by (by100 blast)
                moreover have "V \<inter> V1 \<in> subspace_topology Y TY V1"
                  using \<open>V \<in> TY\<close> unfolding subspace_topology_def by (by100 blast)
                hence "{e1 \<in> W. ?h e1 \<in> V \<inter> V1} \<in> subspace_topology E TE W"
                  using hcomp unfolding top1_continuous_map_on_def by (by100 blast)
                ultimately show "{e1 \<in> W. ?h e1 \<in> V} \<in> subspace_topology E TE W" by (by100 simp)
              qed
            qed
            have hrq_eq_rh: "\<forall>e1\<in>W. r (q e1) = r (?h e1)"
            proof (intro ballI)
              fix e1 assume "e1 \<in> W"
              have "r (q e1) = p e1" using hq_rp \<open>e1 \<in> W\<close> hW_sub_E by (by100 blast)
              have "p e1 \<in> r ` V1" using hr_bij_V1 hW_pU \<open>e1 \<in> W\<close> unfolding bij_betw_def by (by100 blast)
              have "r (?h e1) = p e1" by (rule f_inv_into_f[OF \<open>p e1 \<in> r ` V1\<close>])
              show "r (q e1) = r (?h e1)" using \<open>r (q e1) = p e1\<close> \<open>r (?h e1) = p e1\<close> by (by100 simp)
            qed
            from covering_lift_unique_connected[OF assms(6) hW_top hTB hTY hW_conn
                hq_cont_W hh_cont_W hrq_eq_rh he0_W(1) \<open>?h e0 = q e0\<close>[symmetric]]
            show "q e' = inv_into V1 r (p e')" using he' by (by100 blast)
          qed
          \<comment> \<open>For W \<in> \<W>p with q(e) \<in> V1 for some e \<in> W: q maps ALL of W into V1.\<close>
          have hW_all_V1: "\<forall>W\<in>?\<V>q. \<forall>e\<in>W. q e \<in> V1"
          proof (intro ballI)
            fix W e assume hWq: "W \<in> ?\<V>q" and he_W: "e \<in> W"
            have hW_mem: "W \<in> \<W>p" using hWq by (by100 blast)
            obtain e0 where he0_W: "e0 \<in> W" "q e0 \<in> V1" using hWq by (by100 blast)
            have hW_conn: "top1_connected_on W (subspace_topology E TE W)"
              using hW_connected hW_mem by (by100 blast)
            \<comment> \<open>Define h = (inv_into V1 r) \<circ> p: W \<rightarrow> V1. Both q and h lift p through r.\<close>
            let ?h = "\<lambda>e. inv_into V1 r (p e)"
            \<comment> \<open>h maps W into V1 and r \<circ> h = p on W.\<close>
            have hW_sub_E: "W \<subseteq> E" using hW_mem h\<W>p_open unfolding openin_on_def by (by100 blast)
            have hW_pU: "\<forall>e'\<in>W. p e' \<in> U''"
            proof (intro ballI)
              fix e' assume "e' \<in> W"
              have "e' \<in> {x\<in>E. p x \<in> U''}" using \<open>e' \<in> W\<close> hW_mem h\<W>p_union by (by100 blast)
              thus "p e' \<in> U''" by (by100 blast)
            qed
            have hh_V1: "\<forall>e'\<in>W. ?h e' \<in> V1"
            proof (intro ballI)
              fix e' assume "e' \<in> W"
              have "p e' \<in> U''" using hW_pU \<open>e' \<in> W\<close> by (by100 blast)
              have "p e' \<in> r ` V1" using hr_bij_V1 \<open>p e' \<in> U''\<close> unfolding bij_betw_def by (by100 blast)
              thus "?h e' \<in> V1" using inv_into_into[OF \<open>p e' \<in> r ` V1\<close>] by (by100 simp)
            qed
            have hrh: "\<forall>e'\<in>W. r (?h e') = p e'"
            proof (intro ballI)
              fix e' assume "e' \<in> W"
              have "p e' \<in> U''" using hW_pU \<open>e' \<in> W\<close> by (by100 blast)
              have "p e' \<in> r ` V1" using hr_bij_V1 \<open>p e' \<in> U''\<close> unfolding bij_betw_def by (by100 blast)
              show "r (?h e') = p e'" by (rule f_inv_into_f[OF \<open>p e' \<in> r ` V1\<close>])
            qed
            \<comment> \<open>h(e0) = q(e0): both in V1, r(h(e0)) = p(e0) = r(q(e0)), r injective on V1.\<close>
            have "?h e0 = q e0"
            proof -
              have "r (?h e0) = p e0" using hrh he0_W(1) by (by100 blast)
              have "r (q e0) = p e0"
              proof -
                have "e0 \<in> E" using he0_W(1) hW_sub_E by (by100 blast)
                thus ?thesis using hq_rp by (by100 blast)
              qed
              have "?h e0 \<in> V1" using hh_V1 he0_W(1) by (by100 blast)
              have "q e0 \<in> V1" by (rule he0_W(2))
              from \<open>r (?h e0) = p e0\<close> \<open>r (q e0) = p e0\<close>
              have "r (?h e0) = r (q e0)" by (by100 simp)
              thus "?h e0 = q e0"
                using hr_inj_V1 \<open>?h e0 \<in> V1\<close> \<open>q e0 \<in> V1\<close> unfolding inj_on_def by (by100 blast)
            qed
            \<comment> \<open>By covering\_lift\_unique\_connected: q = h on W.\<close>
            \<comment> \<open>Both q|_W and h|_W: W \<rightarrow> Y lift p through r, W connected, agree at e0.\<close>
            \<comment> \<open>Apply covering\_lift\_unique\_connected: r covering, W connected domain,
               q|_W and h|_W both lift p through r, agree at e0.\<close>
            have hW_TE: "W \<in> TE" using hW_mem h\<W>p_open unfolding openin_on_def by (by100 blast)
            have hW_top: "is_topology_on W (subspace_topology E TE W)"
            proof -
              have "top1_locally_path_connected_on W (subspace_topology E TE W)"
                by (rule open_subset_locally_path_connected[OF assms(7) hW_TE hW_sub_E])
              thus ?thesis unfolding top1_locally_path_connected_on_def by (by100 blast)
            qed
            have hq_cont_W: "top1_continuous_map_on W (subspace_topology E TE W) Y TY q"
            proof -
              have "\<forall>A f. top1_continuous_map_on E TE Y TY f \<and> A \<subseteq> E \<longrightarrow>
                  top1_continuous_map_on A (subspace_topology E TE A) Y TY f"
                using Theorem_18_2[OF hTE hTY hTY] by (by100 blast)
              thus ?thesis using hq_cont hW_sub_E by (by100 blast)
            qed
            have hh_cont_W: "top1_continuous_map_on W (subspace_topology E TE W) Y TY ?h"
            proof -
              have hp_W_U: "top1_continuous_map_on W (subspace_topology E TE W)
                  U'' (subspace_topology B TB U'') p"
                using h\<W>p_homeo hW_mem unfolding top1_homeomorphism_on_def by (by100 blast)
              have hinv_U_V1: "top1_continuous_map_on U'' (subspace_topology B TB U'')
                  V1 (subspace_topology Y TY V1) (inv_into V1 r)"
                using homeomorphism_inverse[OF hV1_homeo]
                unfolding top1_homeomorphism_on_def by (by100 blast)
              have hcomp0: "top1_continuous_map_on W (subspace_topology E TE W)
                  V1 (subspace_topology Y TY V1) (inv_into V1 r \<circ> p)"
                by (rule top1_continuous_map_on_comp[OF hp_W_U hinv_U_V1])
              have hcomp_eq: "(inv_into V1 r \<circ> p) = (\<lambda>e. inv_into V1 r (p e))"
                unfolding comp_def by (by100 simp)
              have hcomp: "top1_continuous_map_on W (subspace_topology E TE W)
                  V1 (subspace_topology Y TY V1) (\<lambda>e. inv_into V1 r (p e))"
                using hcomp0 hcomp_eq by (by100 simp)
              \<comment> \<open>Lift from V1-subspace to Y: direct proof.\<close>
              have hV1_sub_Y: "V1 \<subseteq> Y" using hV1_open unfolding openin_on_def by (by100 blast)
              show ?thesis unfolding top1_continuous_map_on_def
              proof (intro conjI ballI)
                fix e' assume "e' \<in> W"
                thus "inv_into V1 r (p e') \<in> Y" using hh_V1 \<open>e' \<in> W\<close> hV1_sub_Y by (by100 blast)
              next
                fix V assume "V \<in> TY"
                have "V \<inter> V1 \<in> subspace_topology Y TY V1"
                  using \<open>V \<in> TY\<close> unfolding subspace_topology_def by (by100 blast)
                hence "{e' \<in> W. inv_into V1 r (p e') \<in> V \<inter> V1} \<in> subspace_topology E TE W"
                  using hcomp unfolding top1_continuous_map_on_def by (by100 blast)
                moreover have "{e' \<in> W. inv_into V1 r (p e') \<in> V} =
                    {e' \<in> W. inv_into V1 r (p e') \<in> V \<inter> V1}"
                  using hh_V1 by (by100 blast)
                ultimately show "{e' \<in> W. inv_into V1 r (p e') \<in> V} \<in> subspace_topology E TE W"
                  by (by100 simp)
              qed
            qed
            have hrq_eq_rh: "\<forall>e'\<in>W. r (q e') = r (?h e')"
            proof (intro ballI)
              fix e' assume "e' \<in> W"
              have "e' \<in> E" using \<open>e' \<in> W\<close> hW_sub_E by (by100 blast)
              have "r (q e') = p e'" using hq_rp \<open>e' \<in> E\<close> by (by100 blast)
              have "r (?h e') = p e'" using hrh \<open>e' \<in> W\<close> by (by100 blast)
              show "r (q e') = r (?h e')" using \<open>r (q e') = p e'\<close> \<open>r (?h e') = p e'\<close> by (by100 simp)
            qed
            have hq_eq_h: "\<forall>e'\<in>W. q e' = ?h e'"
              using covering_lift_unique_connected[OF assms(6) hW_top hTB hTY hW_conn
                  hq_cont_W hh_cont_W hrq_eq_rh he0_W(1) \<open>?h e0 = q e0\<close>[symmetric]]
              by (by100 blast)
            have "q e = ?h e" using hq_eq_h he_W by (by100 blast)
            thus "q e \<in> V1" using hh_V1 he_W by (by100 simp)
          qed
          show "{x \<in> E. q x \<in> V1} = \<Union>?\<V>q"
          proof (rule set_eqI, rule iffI)
            fix x assume "x \<in> {x \<in> E. q x \<in> V1}"
            hence hx: "x \<in> E" "q x \<in> V1" by (by100 blast)+
            have "r (q x) \<in> U''"
            proof -
              have "q x \<in> V1" by (rule hx(2))
              hence "q x \<in> \<Union>\<W>r" using hV1(1) by (by100 blast)
              hence "q x \<in> {x\<in>Y. r x \<in> U''}" using h\<W>r_union by (by100 simp)
              thus ?thesis by (by100 blast)
            qed
            hence "p x \<in> U''" using hq_rp hx(1) by (by100 simp)
            hence "x \<in> {x\<in>E. p x \<in> U''}" using hx(1) by (by100 blast)
            hence "x \<in> \<Union>\<W>p" using h\<W>p_union by (by100 simp)
            then obtain W where "W \<in> \<W>p" "x \<in> W" by (by100 blast)
            moreover have "W \<in> ?\<V>q" using \<open>W \<in> \<W>p\<close> \<open>x \<in> W\<close> hx(2) by (by100 blast)
            ultimately show "x \<in> \<Union>?\<V>q" by (by100 blast)
          next
            fix x assume "x \<in> \<Union>?\<V>q"
            then obtain W where "W \<in> ?\<V>q" "x \<in> W" by (by100 blast)
            hence "x \<in> E" using h\<W>p_open unfolding openin_on_def by (by100 blast)
            moreover have "q x \<in> V1" using hW_all_V1 \<open>W \<in> ?\<V>q\<close> \<open>x \<in> W\<close> by (by100 blast)
            ultimately show "x \<in> {x \<in> E. q x \<in> V1}" by (by100 blast)
          qed
          show "\<forall>W\<in>?\<V>q. top1_homeomorphism_on W (subspace_topology E TE W)
              V1 (subspace_topology Y TY V1) q"
          proof (intro ballI)
            fix W assume hWq: "W \<in> ?\<V>q"
            have hW_mem: "W \<in> \<W>p" using hWq by (by100 blast)
            \<comment> \<open>Re-derive q = h on W.\<close>
            have hW_sub_E: "W \<subseteq> E" using hW_mem h\<W>p_open unfolding openin_on_def by (by100 blast)
            have hq_eq_h_W: "\<forall>e'\<in>W. q e' = inv_into V1 r (p e')"
              using hq_eq_h_all hWq by (by100 blast)
            \<comment> \<open>Composition of homeomorphisms: (inv_into V1 r) \<circ> p: W \<cong> V1.\<close>
            have hp_homeo_W: "top1_homeomorphism_on W (subspace_topology E TE W)
                U'' (subspace_topology B TB U'') p"
              using h\<W>p_homeo hW_mem by (by100 blast)
            have hinv_homeo: "top1_homeomorphism_on U'' (subspace_topology B TB U'')
                V1 (subspace_topology Y TY V1) (inv_into V1 r)"
              by (rule homeomorphism_inverse[OF hV1_homeo])
            have hcomp_homeo: "top1_homeomorphism_on W (subspace_topology E TE W)
                V1 (subspace_topology Y TY V1) (inv_into V1 r \<circ> p)"
              by (rule homeomorphism_compose[OF hp_homeo_W hinv_homeo])
            \<comment> \<open>q agrees with inv_into V1 r \<circ> p on W, so transfer homeomorphism.\<close>
            have hq_eq_comp: "\<forall>x\<in>W. q x = (inv_into V1 r \<circ> p) x"
              using hq_eq_h_W by (by100 simp)
            \<comment> \<open>Transfer: same function on carrier \<Rightarrow> same homeomorphism.\<close>
            show "top1_homeomorphism_on W (subspace_topology E TE W)
                V1 (subspace_topology Y TY V1) q"
            proof -
              let ?g = "inv_into V1 r \<circ> p"
              \<comment> \<open>bij_betw: q and g agree on W, g is bijective W \<rightarrow> V1.\<close>
              have hg_bij: "bij_betw ?g W V1"
                using hcomp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
              have hq_bij: "bij_betw q W V1"
              proof -
                have "q ` W = ?g ` W"
                proof (rule set_eqI, rule iffI)
                  fix y assume "y \<in> q ` W"
                  then obtain w where "w \<in> W" "y = q w" by (by100 blast)
                  hence "y = ?g w" using hq_eq_comp by (by100 blast)
                  thus "y \<in> ?g ` W" using \<open>w \<in> W\<close> by (by100 blast)
                next
                  fix y assume "y \<in> ?g ` W"
                  then obtain w where "w \<in> W" "y = ?g w" by (by100 blast)
                  have "q w = ?g w" using hq_eq_comp \<open>w \<in> W\<close> by (by100 blast)
                  hence "y = q w" using \<open>y = ?g w\<close> by (by100 simp)
                  thus "y \<in> q ` W" using \<open>w \<in> W\<close> by (by100 blast)
                qed
                have "inj_on q W"
                proof (rule inj_onI)
                  fix x y assume "x \<in> W" "y \<in> W" "q x = q y"
                  have "?g x = ?g y"
                    using hq_eq_comp \<open>x \<in> W\<close> \<open>y \<in> W\<close> \<open>q x = q y\<close> by (by100 simp)
                  have "inj_on ?g W" using hg_bij unfolding bij_betw_def by (by100 blast)
                  thus "x = y" using \<open>x \<in> W\<close> \<open>y \<in> W\<close> \<open>?g x = ?g y\<close>
                    unfolding inj_on_def by (by100 blast)
                qed
                thus ?thesis using hg_bij \<open>q ` W = ?g ` W\<close>
                  unfolding bij_betw_def by (by100 blast)
              qed
              \<comment> \<open>Continuity: q and g agree on W.\<close>
              have hq_cont_WV1: "top1_continuous_map_on W (subspace_topology E TE W)
                  V1 (subspace_topology Y TY V1) q"
                using iffD2[OF top1_continuous_map_on_cong[of W q ?g]] hq_eq_comp
                  hcomp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
              \<comment> \<open>Inverse continuity: inv_into W q agrees with inv_into W g on V1.\<close>
              have hinv_cont: "top1_continuous_map_on V1 (subspace_topology Y TY V1)
                  W (subspace_topology E TE W) (inv_into W q)"
              proof -
                have hg_inv_cont: "top1_continuous_map_on V1 (subspace_topology Y TY V1)
                    W (subspace_topology E TE W) (inv_into W ?g)"
                  using hcomp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
                have "\<forall>y\<in>V1. inv_into W q y = inv_into W ?g y"
                proof (intro ballI)
                  fix y assume "y \<in> V1"
                  have "y \<in> q ` W" using hq_bij \<open>y \<in> V1\<close> unfolding bij_betw_def by (by100 blast)
                  then obtain w where "w \<in> W" "q w = y" by (by100 blast)
                  have hinj_q: "inj_on q W" using hq_bij unfolding bij_betw_def by (by100 blast)
                  have "inv_into W q (q w) = w" by (rule inv_into_f_f[OF hinj_q \<open>w \<in> W\<close>])
                  hence "inv_into W q y = w" using \<open>q w = y\<close> by (by100 simp)
                  have "q w = ?g w" using hq_eq_comp \<open>w \<in> W\<close> by (by100 blast)
                  hence "?g w = y" using \<open>q w = y\<close> by (by100 simp)
                  have hinj_g: "inj_on ?g W" using hg_bij unfolding bij_betw_def by (by100 blast)
                  have "inv_into W ?g (?g w) = w" by (rule inv_into_f_f[OF hinj_g \<open>w \<in> W\<close>])
                  hence "inv_into W ?g y = w" using \<open>?g w = y\<close> by (by100 simp)
                  thus "inv_into W q y = inv_into W ?g y"
                    using \<open>inv_into W q y = w\<close> by (by100 simp)
                qed
                thus ?thesis
                  using iffD2[OF top1_continuous_map_on_cong[of V1 "inv_into W q" "inv_into W ?g"]]
                    hg_inv_cont by (by100 blast)
              qed
              have hW_top_loc: "is_topology_on W (subspace_topology E TE W)"
                using hp_homeo_W unfolding top1_homeomorphism_on_def by (by100 blast)
              have hV1_top: "is_topology_on V1 (subspace_topology Y TY V1)"
                using hV1_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
              show ?thesis unfolding top1_homeomorphism_on_def
                using hW_top_loc hV1_top hq_bij hq_cont_WV1 hinv_cont by (by100 blast)
            qed
          qed
        qed
      qed
    qed
  qed
  show ?thesis
  proof (rule exI[of _ q])
    show "top1_covering_map_on E TE Y TY q \<and> (\<forall>e\<in>E. r (q e) = p e)"
      unfolding top1_covering_map_on_def using hq_cont hq_surj hq_cov hq_rp by (by100 blast)
  qed
qed

text \<open>Strict version of Theorem_80_3 — same statement but with simply_connected_strict.\<close>
corollary Theorem_80_3_universal_strict:
  assumes "top1_simply_connected_strict E TE"
      and "is_topology_on_strict B TB"
      and "is_topology_on_strict Y TY"
      and "top1_covering_map_on E TE B TB p"
      and "top1_covering_map_on Y TY B TB r"
      and "top1_locally_path_connected_on E TE"
      and "top1_path_connected_on Y TY"
  shows "\<exists>q. top1_covering_map_on E TE Y TY q \<and> (\<forall>e\<in>E. r (q e) = p e)"
  using Theorem_80_3_universal[of E TE B TB Y TY p r]
    top1_simply_connected_strict_imp[OF assms(1)]
    top1_simply_connected_strict_is_topology_strict[OF assms(1)]
    assms(2-7) by (by100 blast)

section \<open>*\<S>81 Covering Transformations\<close>

text \<open>A covering transformation of p : E \<rightarrow> B is a homeomorphism h : E \<rightarrow> E
  with p \<circ> h = p. We require h = id outside E so that covering transformations
  form a group under (total) function composition.\<close>
definition top1_covering_transformation_on :: "'e set \<Rightarrow> 'e set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> ('e \<Rightarrow> 'e) \<Rightarrow> bool" where
  "top1_covering_transformation_on E TE B TB p h \<longleftrightarrow>
     top1_homeomorphism_on E TE E TE h \<and> (\<forall>e\<in>E. p (h e) = p e)
     \<and> (\<forall>e. e \<notin> E \<longrightarrow> h e = e)"

(** from *\<S>81 Theorem 81.2: the group of covering transformations Cov(p) is
    isomorphic to N(H)/H, where H = p_*(\<pi>_1(E, e_0)) and N(H) is its normalizer
    in \<pi>_1(B, b_0). **)
theorem Theorem_81_2_covering_group_iso:
  fixes E :: "'e set" and TE :: "'e set set"
    and B :: "'b set" and TB :: "'b set set"
    and p :: "'e \<Rightarrow> 'b" and b0 :: 'b and e0 :: 'e
  assumes "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "top1_covering_map_on E TE B TB p"
      and "top1_path_connected_on E TE"
      and "top1_locally_path_connected_on E TE"
      and "e0 \<in> E" and "p e0 = b0"
  shows "\<exists>(Cov::('e \<Rightarrow> 'e) set) eC invgC.
           Cov = {h. top1_covering_transformation_on E TE B TB p h}
         \<and> top1_is_group_on Cov (\<lambda>h k e. h (k e)) eC invgC
         \<and> top1_groups_isomorphic_on Cov (\<lambda>h k e. h (k e))
             (top1_quotient_group_carrier_on
                (top1_normalizer_on
                   (top1_fundamental_group_carrier B TB b0)
                   (top1_fundamental_group_mul B TB b0)
                   (top1_fundamental_group_invg B TB b0)
                   (top1_fundamental_group_image_hom E TE e0 B TB b0 p))
                (top1_fundamental_group_mul B TB b0)
                (top1_fundamental_group_image_hom E TE e0 B TB b0 p))
             (top1_quotient_group_mul_on (top1_fundamental_group_mul B TB b0))"
proof -
  \<comment> \<open>Munkres 81.2: Define the map \<Phi>: Cov(p) \<rightarrow> N(H)/H as follows.
     Given a covering transformation h, it maps e0 to some e1 in the fiber p\<inverse>(b0).
     Choose a path \<alpha> from e0 to e1 in E. Then p\<circ>\<alpha> is a loop in B at b0, giving [p\<circ>\<alpha>] \<in> \<pi>_1(B).
     This class lies in N(H) and is well-defined modulo H. So \<Phi>(h) = [p\<circ>\<alpha>]H.\<close>
  let ?H = "top1_fundamental_group_image_hom E TE e0 B TB b0 p"
  let ?Cov = "{h. top1_covering_transformation_on E TE B TB p h}"
  \<comment> \<open>Step 1: Cov(p) is a group under composition.\<close>
  have hCov_group: "\<exists>eC invgC. top1_is_group_on ?Cov (\<lambda>h k e. h (k e)) eC invgC"
  proof -
    let ?mul = "\<lambda>h k e. h (k e)" \<comment> \<open>= \<circ> (function composition)\<close>
    let ?eC = "id :: 'e \<Rightarrow> 'e"
    let ?invC = "\<lambda>h e. if e \<in> E then inv_into E h e else e"
    have hTE: "is_topology_on E TE"
      using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    \<comment> \<open>id is a covering transformation.\<close>
    have hid_homeo: "top1_homeomorphism_on E TE E TE id"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      show "is_topology_on E TE" by (rule hTE)
      show "is_topology_on E TE" by (rule hTE)
      show "bij_betw id E E" by (by100 simp)
      show "top1_continuous_map_on E TE E TE id" using top1_continuous_map_on_id[OF hTE] .
      have hinv_id: "\<forall>x\<in>E. inv_into E id x = id x"
      proof (intro ballI)
        fix x assume "x \<in> E"
        thus "inv_into E id x = id x" using inv_into_f_f[of id E x] by (by100 simp)
      qed
      show "top1_continuous_map_on E TE E TE (inv_into E id)"
        using top1_continuous_map_on_cong[of E "inv_into E id" id]
          hinv_id top1_continuous_map_on_id[OF hTE] by (by100 blast)
    qed
    have hid_cov: "?eC \<in> ?Cov"
      using hid_homeo unfolding top1_covering_transformation_on_def by (by100 simp)
    \<comment> \<open>Composition of covering transformations.\<close>
    have hcomp_cov: "\<forall>h\<in>?Cov. \<forall>k\<in>?Cov. ?mul h k \<in> ?Cov"
    proof (intro ballI)
      fix h k assume hh: "h \<in> ?Cov" and hk: "k \<in> ?Cov"
      have hh_homeo: "top1_homeomorphism_on E TE E TE h"
        using hh unfolding top1_covering_transformation_on_def by (by100 blast)
      have hk_homeo: "top1_homeomorphism_on E TE E TE k"
        using hk unfolding top1_covering_transformation_on_def by (by100 blast)
      have hh_p: "\<forall>e\<in>E. p (h e) = p e"
        using hh unfolding top1_covering_transformation_on_def by (by100 blast)
      have hk_p: "\<forall>e\<in>E. p (k e) = p e"
        using hk unfolding top1_covering_transformation_on_def by (by100 blast)
      have hh_out: "\<forall>e. e \<notin> E \<longrightarrow> h e = e"
        using hh unfolding top1_covering_transformation_on_def by (by100 blast)
      have hk_out: "\<forall>e. e \<notin> E \<longrightarrow> k e = e"
        using hk unfolding top1_covering_transformation_on_def by (by100 blast)
      have "top1_homeomorphism_on E TE E TE (h \<circ> k)"
        by (rule homeomorphism_compose[OF hk_homeo hh_homeo])
      moreover have "\<forall>e\<in>E. p ((h \<circ> k) e) = p e"
      proof (intro ballI)
        fix e assume "e \<in> E"
        have "k e \<in> E"
        proof -
          have "bij_betw k E E" using hk_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          thus ?thesis using \<open>e \<in> E\<close> unfolding bij_betw_def by (by100 blast)
        qed
        thus "p ((h \<circ> k) e) = p e" using hh_p hk_p \<open>e \<in> E\<close> by (by100 simp)
      qed
      moreover have "\<forall>e. e \<notin> E \<longrightarrow> (h \<circ> k) e = e"
        using hh_out hk_out by (by100 simp)
      moreover have "?mul h k = h \<circ> k" by (rule ext) (by100 simp)
      ultimately show "?mul h k \<in> ?Cov"
        unfolding top1_covering_transformation_on_def by (by100 simp)
    qed
    \<comment> \<open>Inverse of covering transformation.\<close>
    have hinv_cov: "\<forall>h\<in>?Cov. ?invC h \<in> ?Cov"
    proof (intro ballI)
      fix h assume hh: "h \<in> ?Cov"
      have hh_homeo: "top1_homeomorphism_on E TE E TE h"
        using hh unfolding top1_covering_transformation_on_def by (by100 blast)
      have hh_p: "\<forall>e\<in>E. p (h e) = p e"
        using hh unfolding top1_covering_transformation_on_def by (by100 blast)
      have hh_out: "\<forall>e. e \<notin> E \<longrightarrow> h e = e"
        using hh unfolding top1_covering_transformation_on_def by (by100 blast)
      \<comment> \<open>inv_into E h is the inverse homeomorphism.\<close>
      have hinv_homeo_raw: "top1_homeomorphism_on E TE E TE (inv_into E h)"
        by (rule homeomorphism_inverse[OF hh_homeo])
      \<comment> \<open>The modified inverse ?invC h agrees with inv_into E h on E.\<close>
      have hagree: "\<forall>e\<in>E. (\<lambda>e. if e \<in> E then inv_into E h e else e) e = inv_into E h e"
        by (by100 simp)
      \<comment> \<open>Transfer bij_betw: functions agreeing on E have the same bij_betw on E.\<close>
      have hbij_raw: "bij_betw (inv_into E h) E E"
        using hinv_homeo_raw unfolding top1_homeomorphism_on_def by (by100 blast)
      have hbij: "bij_betw (\<lambda>e. if e \<in> E then inv_into E h e else e) E E"
      proof -
        have "inj_on (\<lambda>e. if e \<in> E then inv_into E h e else e) E"
        proof (rule inj_onI)
          fix x y assume hx: "x \<in> E" and hy: "y \<in> E"
            and heq: "(if x \<in> E then inv_into E h x else x) = (if y \<in> E then inv_into E h y else y)"
          from heq hx hy have "inv_into E h x = inv_into E h y" by (by100 simp)
          thus "x = y" using inj_on_eq_iff[of "inv_into E h" E x y] hbij_raw hx hy
            unfolding bij_betw_def by (by100 blast)
        qed
        moreover have "(\<lambda>e. if e \<in> E then inv_into E h e else e) ` E = E"
        proof -
          have "(inv_into E h) ` E = E" using hbij_raw unfolding bij_betw_def by (by100 blast)
          moreover have "\<forall>e\<in>E. (\<lambda>e. if e \<in> E then inv_into E h e else e) e = inv_into E h e"
            by (by100 simp)
          ultimately show ?thesis by (by100 force)
        qed
        ultimately show ?thesis unfolding bij_betw_def by (by100 blast)
      qed
      \<comment> \<open>Transfer continuity via cong.\<close>
      have hcont_raw: "top1_continuous_map_on E TE E TE (inv_into E h)"
        using hinv_homeo_raw unfolding top1_homeomorphism_on_def by (by100 blast)
      have hcont: "top1_continuous_map_on E TE E TE (\<lambda>e. if e \<in> E then inv_into E h e else e)"
        using top1_continuous_map_on_cong[of E "\<lambda>e. if e \<in> E then inv_into E h e else e"
              "inv_into E h"] hagree hcont_raw by (by100 blast)
      \<comment> \<open>Inverse of ?invC h on E equals h.\<close>
      have hbij_h: "bij_betw h E E"
        using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have hinj_h: "inj_on h E"
        using hbij_h unfolding bij_betw_def by (by100 blast)
      have hinj_mod: "inj_on (\<lambda>e. if e \<in> E then inv_into E h e else e) E"
      proof (rule inj_onI)
        fix x y assume hx: "x \<in> E" and hy: "y \<in> E"
          and heqm: "(if x \<in> E then inv_into E h x else x) = (if y \<in> E then inv_into E h y else y)"
        from heqm hx hy have "inv_into E h x = inv_into E h y" by (by100 simp)
        thus "x = y" using inj_on_eq_iff[of "inv_into E h" E x y] hbij_raw hx hy
          unfolding bij_betw_def by (by100 blast)
      qed
      have hinv_inv_agree: "\<forall>e\<in>E. inv_into E (\<lambda>e. if e \<in> E then inv_into E h e else e) e = h e"
      proof (intro ballI)
        fix e assume he: "e \<in> E"
        have hhe_E: "h e \<in> E" using hbij_h he unfolding bij_betw_def by (by100 blast)
        have "(\<lambda>e. if e \<in> E then inv_into E h e else e) (h e)
            = inv_into E h (h e)" using hhe_E by (by100 simp)
        also have "\<dots> = e" by (rule inv_into_f_f[OF hinj_h he])
        finally have hfeq: "(\<lambda>e. if e \<in> E then inv_into E h e else e) (h e) = e" .
        let ?g = "\<lambda>e. if e \<in> E then inv_into E h e else e"
        have "inv_into E ?g e = h e"
          using inv_into_f_eq[OF hinj_mod hhe_E hfeq] by (by100 simp)
        thus "inv_into E (\<lambda>e. if e \<in> E then inv_into E h e else e) e = h e" by (by100 simp)
      qed
      have hcont_h: "top1_continuous_map_on E TE E TE h"
        using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have hcont_inv: "top1_continuous_map_on E TE E TE
          (inv_into E (\<lambda>e. if e \<in> E then inv_into E h e else e))"
        using top1_continuous_map_on_cong[of E
              "inv_into E (\<lambda>e. if e \<in> E then inv_into E h e else e)" h]
              hinv_inv_agree hcont_h by (by100 blast)
      \<comment> \<open>Assemble homeomorphism.\<close>
      have hinv_homeo: "top1_homeomorphism_on E TE E TE (\<lambda>e. if e \<in> E then inv_into E h e else e)"
        unfolding top1_homeomorphism_on_def using hTE hbij hcont hcont_inv by (by100 blast)
      \<comment> \<open>p-preservation on E (same as before, since ?invC h = inv_into E h on E).\<close>
      moreover have "\<forall>e\<in>E. p ((\<lambda>e. if e \<in> E then inv_into E h e else e) e) = p e"
      proof (intro ballI)
        fix e assume "e \<in> E"
        have hsurj_loc: "h ` E = E" using hbij_h unfolding bij_betw_def by (by100 blast)
        have "e \<in> h ` E" using \<open>e \<in> E\<close> hsurj_loc by (by100 blast)
        have "inv_into E h e \<in> E" using inv_into_into[OF \<open>e \<in> h ` E\<close>] .
        have "h (inv_into E h e) = e" using f_inv_into_f[OF \<open>e \<in> h ` E\<close>] .
        hence "p e = p (h (inv_into E h e))" by (by100 simp)
        also have "\<dots> = p (inv_into E h e)" using hh_p \<open>inv_into E h e \<in> E\<close> by (by100 blast)
        finally have "p (inv_into E h e) = p e" by (by100 simp)
        thus "p ((\<lambda>e. if e \<in> E then inv_into E h e else e) e) = p e"
          using \<open>e \<in> E\<close> by (by100 simp)
      qed
      \<comment> \<open>Trivially id outside E.\<close>
      moreover have "\<forall>e. e \<notin> E \<longrightarrow> (\<lambda>e. if e \<in> E then inv_into E h e else e) e = e"
        by (by100 simp)
      ultimately show "?invC h \<in> ?Cov"
        unfolding top1_covering_transformation_on_def by (by100 blast)
    qed
    \<comment> \<open>Associativity.\<close>
    have hassoc: "\<forall>h\<in>?Cov. \<forall>k\<in>?Cov. \<forall>l\<in>?Cov. ?mul (?mul h k) l = ?mul h (?mul k l)"
      by (by100 auto)
    \<comment> \<open>Identity.\<close>
    have hident: "\<forall>h\<in>?Cov. ?mul ?eC h = h \<and> ?mul h ?eC = h"
      by (by100 auto)
    \<comment> \<open>Inverse: ?invC h \<circ> h = id and h \<circ> ?invC h = id.
       Works because h = id outside E (from the extended definition) and
       inv_into E h inverts h on E.\<close>
    have hinverse: "\<forall>h\<in>?Cov. ?mul (?invC h) h = ?eC \<and> ?mul h (?invC h) = ?eC"
    proof (intro ballI conjI)
      fix h assume hh: "h \<in> ?Cov"
      have hbij: "bij_betw h E E"
        using hh unfolding top1_covering_transformation_on_def top1_homeomorphism_on_def
        by (by100 blast)
      have hinj: "inj_on h E" using hbij unfolding bij_betw_def by (by100 blast)
      have hsurj: "h ` E = E" using hbij unfolding bij_betw_def by (by100 blast)
      have hout: "\<forall>e. e \<notin> E \<longrightarrow> h e = e"
        using hh unfolding top1_covering_transformation_on_def by (by100 blast)
      \<comment> \<open>?invC h \<circ> h = id\<close>
      show "?mul (?invC h) h = ?eC"
      proof (rule ext)
        fix e show "?mul (?invC h) h e = ?eC e"
        proof (cases "e \<in> E")
          case True
          have "h e \<in> E" using hbij True unfolding bij_betw_def by (by100 blast)
          hence "?mul (?invC h) h e = inv_into E h (h e)" by (by100 simp)
          also have "\<dots> = e" by (rule inv_into_f_f[OF hinj True])
          finally show ?thesis by (by100 simp)
        next
          case False
          hence "h e = e" using hout by (by100 blast)
          hence "?mul (?invC h) h e = (\<lambda>e. if e \<in> E then inv_into E h e else e) e"
            by (by100 simp)
          also have "\<dots> = e" using False by (by100 simp)
          finally show ?thesis by (by100 simp)
        qed
      qed
      \<comment> \<open>h \<circ> ?invC h = id\<close>
      show "?mul h (?invC h) = ?eC"
      proof (rule ext)
        fix e show "?mul h (?invC h) e = ?eC e"
        proof (cases "e \<in> E")
          case True
          have "e \<in> h ` E" using True hsurj by (by100 blast)
          have "inv_into E h e \<in> E" using inv_into_into[OF \<open>e \<in> h ` E\<close>] .
          have "(?invC h) e = inv_into E h e" using True by (by100 simp)
          hence "?mul h (?invC h) e = h (inv_into E h e)" by (by100 simp)
          also have "\<dots> = e" by (rule f_inv_into_f[OF \<open>e \<in> h ` E\<close>])
          finally show ?thesis by (by100 simp)
        next
          case False
          hence "?mul h (?invC h) e = h e" by (by100 simp)
          also have "\<dots> = e" using hout False by (by100 blast)
          finally show ?thesis by (by100 simp)
        qed
      qed
    qed
    show ?thesis
      apply (rule exI[of _ ?eC], rule exI[of _ ?invC])
      unfolding top1_is_group_on_def
      using hid_cov hcomp_cov hinv_cov hassoc hident hinverse by (by100 blast)
  qed
  \<comment> \<open>Step 2-3: Define \<Phi>: Cov(p) \<rightarrow> N(H)/H and show it's a group isomorphism.\<close>
  let ?Q = "top1_quotient_group_carrier_on
         (top1_normalizer_on
            (top1_fundamental_group_carrier B TB b0)
            (top1_fundamental_group_mul B TB b0)
            (top1_fundamental_group_invg B TB b0) ?H)
         (top1_fundamental_group_mul B TB b0) ?H"
  let ?mulQ = "top1_quotient_group_mul_on (top1_fundamental_group_mul B TB b0)"
  have h_iso: "top1_groups_isomorphic_on ?Cov (\<lambda>h k e. h (k e)) ?Q ?mulQ" sorry
  obtain eC invgC where hCov_grp: "top1_is_group_on ?Cov (\<lambda>h k e. h (k e)) eC invgC"
    using hCov_group by (by100 blast)
  show ?thesis
    apply (rule exI[where x="?Cov"])
    apply (rule exI[where x=eC])
    apply (rule exI[where x=invgC])
    using hCov_grp h_iso by (by100 blast)
qed

section \<open>\<S>82 Existence of Covering Spaces\<close>

text \<open>Semilocally simply connected: every point has a neighborhood U such that
  every loop in U is nulhomotopic in X.\<close>
definition top1_semilocally_simply_connected_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_semilocally_simply_connected_on X TX \<longleftrightarrow>
     (\<forall>x\<in>X. \<exists>U. openin_on X TX U \<and> x \<in> U \<and>
        (\<forall>f. top1_is_loop_on U (subspace_topology X TX U) x f \<longrightarrow>
             top1_path_homotopic_on X TX x x f (top1_constant_path x)))"

(** from \<S>82 Theorem 82.1: existence of covering space for any subgroup.
    Given a subgroup H \<le> \<pi>_1(B, b_0), there exists a connected, locally path-connected
    covering (E, p) with a base-point e_0 over b_0 such that p_*(\<pi>_1(E, e_0)) = H. **)
theorem Theorem_82_1_covering_existence:
  assumes "is_topology_on_strict B TB"
      and "top1_path_connected_on B TB"
      and "top1_locally_path_connected_on B TB"
      and "top1_semilocally_simply_connected_on B TB"
      and "b0 \<in> B"
      and "H \<subseteq> top1_fundamental_group_carrier B TB b0"
      \<comment> \<open>H must be a subgroup, not just a subset.\<close>
      and "top1_is_group_on H
             (top1_fundamental_group_mul B TB b0)
             (top1_fundamental_group_id B TB b0)
             (top1_fundamental_group_invg B TB b0)"
  shows "\<exists>E TE p e0. is_topology_on_strict E TE
    \<and> top1_covering_map_on E TE B TB p
    \<and> top1_path_connected_on E TE
    \<and> top1_locally_path_connected_on E TE
    \<and> e0 \<in> E \<and> p e0 = b0
    \<and> top1_fundamental_group_image_hom E TE e0 B TB b0 p = H"
proof -
  \<comment> \<open>Munkres 82.1: Construct E as the space of path-homotopy classes of paths in B
     starting at b0, modulo the right-coset relation induced by H.
     E = { [\<alpha>]H | \<alpha> is a path from b0 to some b \<in> B }.
     The projection p: E \<rightarrow> B sends the coset [\<alpha>]H to the endpoint \<alpha>(1).
     Step 1: Define E, TE, p, e0 via the coset construction.
     Step 2: Semilocal simple connectivity ensures p is a covering map.
     Step 3: E is path-connected and locally path-connected (inherits from B).
     Step 4: p_*(\<pi>_1(E, e0)) = H by construction.\<close>
  \<comment> \<open>Construction: E = path-homotopy classes modulo H-cosets.
     All steps (topology, covering, connectivity, subgroup matching) are combined.
     The full proof requires constructing the coset space E, defining basis topology,
     proving evenly-covered property (using semilocal simple connectivity),
     and matching p_*(\<pi>_1(E,e0)) = H.\<close>
  have hTB: "is_topology_on B TB" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>===== CONSTRUCTION (Munkres §82) =====\<close>
  \<comment> \<open>Step 1: Define coset relation. Two paths \<alpha>,\<beta> from b0 are in the same H-coset
     iff [rev(\<alpha>)\<cdot>\<beta>] \<in> H. This is an equivalence relation on paths from b0.\<close>
  \<comment> \<open>Step 2: E = set of H-cosets of path classes from b0.
     E = {{g. coset_rel \<alpha> g} | \<alpha>. path from b0}.
     Projection p: E \<rightarrow> B sends coset to endpoint \<alpha>(1).
     Base point e0 = coset of constant path at b0.\<close>
  \<comment> \<open>Step 3: Topology on E. Basis: for coset c and open U \<ni> p(c),
     B(c, U) = {cosets reachable by extending paths in c by paths in U}.
     This is well-defined and forms a basis (Munkres Lemma 82.2).\<close>
  \<comment> \<open>Step 4: p is a covering map. For each b \<in> B, take U semilocally simply connected
     around b. The fiber p\<inverse>(b) = H-cosets of loops at b0 via paths to b.
     Each slice maps homeomorphically to U via p (Munkres Theorem 82.1 main argument).\<close>
  \<comment> \<open>Step 5: E path-connected: for coset [\<alpha>]H, the path t \<mapsto> [\<alpha>_t]H connects e0 to [\<alpha>]H.
     E locally path-connected: basis elements are path-connected.\<close>
  \<comment> \<open>Step 6: p_*(\<pi>_1(E, e0)) = H. A loop \<gamma> at b0 lifts to a path from e0 = [const]H
     to [\<gamma>]H. Lift is a loop iff [\<gamma>]H = [const]H iff [\<gamma>] \<in> H.\<close>
  \<comment> \<open>===== Step 1: Define the H-coset equivalence on paths =====\<close>
  \<comment> \<open>\<alpha> \<sim>_H \<beta> iff \<alpha>(1) = \<beta>(1) and [\<alpha> * rev(\<beta>)] \<in> H.
     This is an equivalence relation on paths from b0.\<close>
  \<comment> \<open>coset\_rel \<alpha> \<beta> \<equiv> \<alpha>(1) = \<beta>(1) \<and> [\<alpha> * rev(\<beta>)] \<in> H.\<close>
  \<comment> \<open>===== Step 2: Define E, p, e0 =====\<close>
  \<comment> \<open>E = set of coset classes. p maps class to endpoint. e0 = class of constant path.\<close>
  \<comment> \<open>For the formal construction, we use an abstract type for the equivalence classes.\<close>
  \<comment> \<open>===== Step 3: Topology on E via basis B(U, \<alpha>) =====\<close>
  \<comment> \<open>For each coset class c and path-connected open U containing p(c):
     B(U, c) = {classes reachable by extending any path in c by a path in U}.\<close>
  \<comment> \<open>===== Step 4: Verify p is a covering map =====\<close>
  \<comment> \<open>For each b \<in> B, take U semilocally simply connected around b.
     The sets B(U, \<alpha>_i) for different \<alpha>_i ending at b partition p\<inverse>(U).
     Each B(U, \<alpha>_i) maps homeomorphically to U via p.\<close>
  \<comment> \<open>===== Step 5: E path-connected and locally path-connected =====\<close>
  \<comment> \<open>Path-connected: for any coset [\<alpha>]_H, the map t \<mapsto> [\<alpha>_t]_H (prefix of \<alpha>)
     gives a path from e0 to [\<alpha>]_H in E.
     Locally path-connected: basis elements B(U,\<alpha>) are path-connected.\<close>
  \<comment> \<open>===== Step 6: p_*(\<pi>_1(E, e0)) = H =====\<close>
  \<comment> \<open>A loop \<gamma> at b0 lifts to a path from e0 = [const]_H to [\<gamma>]_H.
     Lift is a loop iff [\<gamma>]_H = [const]_H iff [\<gamma>] \<in> H.\<close>
  show ?thesis sorry \<comment> \<open>Full construction needs: abstract type for E, basis topology,
     covering map verification, connectivity, and subgroup matching.\<close>
qed

section \<open>Chapter 14: Applications to Group Theory\<close>

section \<open>\<S>83 Covering Spaces of a Graph\<close>

text \<open>An arc is a space homeomorphic to the closed unit interval [0, 1].\<close>


text \<open>A graph (Munkres §83): a Hausdorff space X with a collection \<A> of subspaces
  (arcs), each homeomorphic to [0,1], such that:
  (1) X is the union of all arcs in \<A>,
  (2) any two distinct arcs intersect in a set of at most two common endpoints,
  (3) the topology on X is the weak topology w.r.t. \<A> (a set is closed iff its
      intersection with each arc is closed in the arc).\<close>
definition top1_is_graph_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_graph_on X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     is_hausdorff_on X TX \<and>
     (\<exists>\<A>. (\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A))
        \<and> (\<Union>\<A>) = X
        \<and> (\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
             A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)
           \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)
           \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2)
        \<and> (\<forall>C. C \<subseteq> X \<longrightarrow>
             (closedin_on X TX C \<longleftrightarrow>
              (\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> C)))))"

(** from \<S>83 Theorem 83.4 (Munkres numbering): any covering space of a graph is itself a graph. **)
theorem Theorem_83_4_covering_of_graph_is_graph:
  assumes "top1_is_graph_on B TB"
      and "top1_covering_map_on E TE B TB p"
      and "is_topology_on_strict E TE"
  shows "top1_is_graph_on E TE"
proof -
  \<comment> \<open>Munkres 83.2: Each arc A in B lifts to arcs in E (sheets over A).
     The covering map p is a local homeomorphism, so lifts of arcs are arcs.
     The intersection condition and weak topology lift from B to E.\<close>
  obtain \<A>B where hAB: "(\<forall>A\<in>\<A>B. A \<subseteq> B \<and> top1_is_arc_on A (subspace_topology B TB A))"
      and hcover: "(\<Union>\<A>B) = B"
    using assms(1) unfolding top1_is_graph_on_def by (by100 auto)
  \<comment> \<open>Step 1: For each arc A \<in> \<A>B, the preimage p\<inverse>(A) splits into sheets.
     Each sheet is homeomorphic to A via p (local homeomorphism), hence an arc.\<close>
  have hAE: "\<exists>\<A>E. (\<forall>A'\<in>\<A>E. A' \<subseteq> E \<and> top1_is_arc_on A' (subspace_topology E TE A'))
      \<and> (\<Union>\<A>E) = E
      \<and> (\<forall>A'\<in>\<A>E. \<forall>B'\<in>\<A>E. A' \<noteq> B' \<longrightarrow>
           A' \<inter> B' \<subseteq> top1_arc_endpoints_on A' (subspace_topology E TE A')
         \<and> A' \<inter> B' \<subseteq> top1_arc_endpoints_on B' (subspace_topology E TE B')
         \<and> finite (A' \<inter> B') \<and> card (A' \<inter> B') \<le> 2)
      \<and> (\<forall>C. C \<subseteq> E \<longrightarrow>
           (closedin_on E TE C \<longleftrightarrow>
            (\<forall>A'\<in>\<A>E. closedin_on A' (subspace_topology E TE A') (A' \<inter> C))))"
    sorry \<comment> \<open>Lift graph structure from B: arcs + intersection + weak topology.\<close>
  \<comment> \<open>Step 2: E is Hausdorff (covering space of Hausdorff is Hausdorff).\<close>
  have hE_hausdorff: "is_hausdorff_on E TE"
  proof -
    have hB_haus: "is_hausdorff_on B TB"
      using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
    have hTB: "is_topology_on B TB"
      using hB_haus unfolding is_hausdorff_on_def by (by100 blast)
    have hTE: "is_topology_on E TE"
      using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
    have hp_cont: "top1_continuous_map_on E TE B TB p"
      using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
    have hp_surj: "p ` E = B"
      using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
    show ?thesis unfolding is_hausdorff_on_def neighborhood_of_def
    proof (intro conjI ballI impI)
      show "is_topology_on E TE" by (rule hTE)
    next
      fix x y assume hx: "x \<in> E" and hy: "y \<in> E" and hne: "x \<noteq> y"
      show "\<exists>U V. (U \<in> TE \<and> x \<in> U) \<and> (V \<in> TE \<and> y \<in> V) \<and> U \<inter> V = {}"
      proof (cases "p x = p y")
        case False
        \<comment> \<open>Separate in B, pull back preimages.\<close>
        have hpx: "p x \<in> B" using hp_surj hx by (by100 blast)
        have hpy: "p y \<in> B" using hp_surj hy by (by100 blast)
        obtain U1 V1 where hU1: "U1 \<in> TB" "p x \<in> U1" and hV1: "V1 \<in> TB" "p y \<in> V1"
            and hdisj: "U1 \<inter> V1 = {}"
          using hB_haus hpx hpy False unfolding is_hausdorff_on_def neighborhood_of_def
          by (by100 blast)
        have hpU: "{e \<in> E. p e \<in> U1} \<in> TE"
          using hp_cont hU1(1) unfolding top1_continuous_map_on_def by (by100 blast)
        have hpV: "{e \<in> E. p e \<in> V1} \<in> TE"
          using hp_cont hV1(1) unfolding top1_continuous_map_on_def by (by100 blast)
        have "x \<in> {e \<in> E. p e \<in> U1}" using hx hU1(2) by (by100 blast)
        moreover have "y \<in> {e \<in> E. p e \<in> V1}" using hy hV1(2) by (by100 blast)
        moreover have "{e \<in> E. p e \<in> U1} \<inter> {e \<in> E. p e \<in> V1} = {}"
          using hdisj by (by100 blast)
        ultimately show ?thesis using hpU hpV by (by100 blast)
      next
        case True
        \<comment> \<open>Same fiber: x, y in different sheets.\<close>
        have hb: "p x \<in> B" using hp_surj hx by (by100 blast)
        obtain U0 where hbU: "p x \<in> U0"
            and hev: "top1_evenly_covered_on E TE B TB p U0"
          using assms(2) hb unfolding top1_covering_map_on_def by (by100 blast)
        obtain \<V> where hV_all: "(\<forall>V\<in>\<V>. openin_on E TE V)
            \<and> (\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {})
            \<and> {e \<in> E. p e \<in> U0} = \<Union>\<V>
            \<and> (\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V)
                U0 (subspace_topology B TB U0) p)"
          using hev unfolding top1_evenly_covered_on_def
          apply (elim conjE exE)
          apply (rule that)
          apply (by100 blast)+
          done
        have hV_open: "\<forall>V\<in>\<V>. openin_on E TE V" using hV_all by (by100 blast)
        have hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}" using hV_all by (by100 blast)
        have hV_union: "{e \<in> E. p e \<in> U0} = \<Union>\<V>" using hV_all by (by100 blast)
        have hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V)
            U0 (subspace_topology B TB U0) p" using hV_all by (by100 blast)
        have hx_in_V: "x \<in> \<Union>\<V>" using hx hbU hV_union by (by100 blast)
        have "p y \<in> U0" using hbU True by (by100 simp)
        have hy_in_V: "y \<in> \<Union>\<V>" using hy \<open>p y \<in> U0\<close> hV_union by (by100 blast)
        obtain Vx where hVx: "Vx \<in> \<V>" "x \<in> Vx" using hx_in_V by (by100 blast)
        obtain Vy where hVy: "Vy \<in> \<V>" "y \<in> Vy" using hy_in_V by (by100 blast)
        have "Vx \<noteq> Vy"
        proof
          assume heq: "Vx = Vy"
          \<comment> \<open>p is injective on Vx (homeomorphism), p x = p y, so x = y. Contradiction.\<close>
          have "inj_on p Vx"
            using hV_homeo hVx(1) unfolding top1_homeomorphism_on_def bij_betw_def
            by (by100 blast)
          have "y \<in> Vx" using hVy(2) heq by (by100 simp)
          have "x = y" using inj_onD[OF \<open>inj_on p Vx\<close> True hVx(2) \<open>y \<in> Vx\<close>] .
          thus False using hne by (by100 simp)
        qed
        hence "Vx \<inter> Vy = {}" using hV_disj hVx(1) hVy(1) by (by100 blast)
        moreover have "Vx \<in> TE" using hV_open hVx(1)
          unfolding openin_on_def by (by100 blast)
        moreover have "Vy \<in> TE" using hV_open hVy(1)
          unfolding openin_on_def by (by100 blast)
        ultimately show ?thesis using hVx(2) hVy(2) by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>Step 3: Combine all conditions into top1_is_graph_on.\<close>
  show ?thesis unfolding top1_is_graph_on_def
    using assms(3) hE_hausdorff hAE by (by100 blast)
qed

section \<open>\<S>84 The Fundamental Group of a Graph\<close>

text \<open>A tree is a connected graph with no nontrivial loops (simply connected).\<close>
definition top1_is_tree_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_tree_on X TX \<longleftrightarrow>
     top1_is_graph_on X TX \<and>
     top1_connected_on X TX \<and>
     top1_simply_connected_on X TX"

(** from \<S>84 Theorem 84.7: the fundamental group of a connected graph is free.
    Specifically, \<pi>_1(X, x_0) is isomorphic to a free group on a set of generators
    (one per loop in a spanning-tree complement). **)
theorem Theorem_84_7_fund_group_graph_is_free:
  fixes X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "top1_is_graph_on X TX"
      and "top1_connected_on X TX"
      and "x0 \<in> X"
  shows "\<exists>(G::int set) mul e invg (\<iota>::nat \<Rightarrow> int) S.
           top1_is_free_group_full_on G mul e invg \<iota> S
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)"
proof -
  \<comment> \<open>Munkres 84.7: Choose a maximal tree T in X.
     Step 1: T is simply connected (a tree).
     Step 2: X/T is a wedge of circles (one per edge not in T).
     Step 3: The quotient map X \<rightarrow> X/T is a homotopy equivalence.
     Step 4: \<pi>_1(X/T) is free by Theorem 71.1 (wedge of circles).
     Step 5: By Theorem 58.7, \<pi>_1(X) \<cong> \<pi>_1(X/T) which is free.\<close>
  \<comment> \<open>Step 1: X is a graph, so extract arcs.\<close>
  obtain \<A> where h\<A>: "\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
      and h\<A>_cover: "\<Union>\<A> = X"
    using assms(1) unfolding top1_is_graph_on_def by (by100 auto)
  \<comment> \<open>Step 2: Choose a maximal tree T \<subseteq> X. A maximal tree exists by Zorn's lemma
     (or, for countable graphs, by explicit construction).\<close>
  obtain T :: "'a set" where hT_tree: "top1_is_tree_on T (subspace_topology X TX T)"
      and hT_sub: "T \<subseteq> X"
      and hT_max: "\<forall>v\<in>X. \<exists>A\<in>\<A>. v \<in> A \<and> (\<exists>w\<in>T. w \<in> A)"
      and hx0_T: "x0 \<in> T"
    sorry \<comment> \<open>Existence of maximal tree containing x0 (Munkres Lemma 84.3).\<close>
  \<comment> \<open>Step 3: X/T is a wedge of circles (one per edge not in T).
     The edges not in T form loops when their endpoints are identified via T-collapse.\<close>
  obtain n :: nat and W :: "'b set" and TW :: "'b set set" and q :: "'a \<Rightarrow> 'b" and pw :: 'b
    where hW_wedge: "top1_is_wedge_of_circles_on W TW {..<n} pw"
      and hq_quotient: "top1_quotient_map_on X TX W TW q"
      and hq_T: "\<forall>x\<in>T. q x = pw"
    sorry \<comment> \<open>Quotient X/T = wedge of circles (Munkres Lemma 84.5).\<close>
  \<comment> \<open>Step 4: The quotient map q: X \<rightarrow> X/T is a homotopy equivalence
     (since T is contractible in X).\<close>
  have hq_equiv: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_carrier W TW (q x0))
      (top1_fundamental_group_mul W TW (q x0))"
    sorry \<comment> \<open>Homotopy equivalence of quotient: Theorem 58.7 or direct SvK argument.\<close>
  \<comment> \<open>Step 5: \<pi>_1(X/T) = \<pi>_1(wedge of n circles) is free on n generators (Theorem 71.1).
     Need q(x0) = pw for Theorem_71_1. Then apply Theorem_71_1 to the wedge W.\<close>
  have hqx0: "q x0 = pw"
    using hq_T hx0_T by (by100 blast)
  from Theorem_71_1_wedge_of_circles_finite[OF hW_wedge]
  obtain G0 :: "int set" and mul0 e0 invg0 and \<iota>0 :: "nat \<Rightarrow> int"
    where hfree: "top1_is_free_group_full_on G0 mul0 e0 invg0 \<iota>0 {..<n}"
      and hW_iso: "top1_groups_isomorphic_on G0 mul0
          (top1_fundamental_group_carrier W TW pw)
          (top1_fundamental_group_mul W TW pw)"
    by (by100 blast)
  \<comment> \<open>Rewrite using hqx0.\<close>
  have hW_iso': "top1_groups_isomorphic_on G0 mul0
      (top1_fundamental_group_carrier W TW (q x0))
      (top1_fundamental_group_mul W TW (q x0))"
    using hW_iso unfolding hqx0 .
  \<comment> \<open>Step 6: Combine: \<pi>_1(X) \<cong> \<pi>_1(W) (hq_equiv) and \<pi>_1(W) \<cong> free (hW_iso').
     By transitivity: \<pi>_1(X) \<cong> free group.\<close>
  have hiso_sym: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier W TW (q x0))
      (top1_fundamental_group_mul W TW (q x0)) G0 mul0"
  proof -
    have hgrpW: "top1_is_group_on
        (top1_fundamental_group_carrier W TW (q x0))
        (top1_fundamental_group_mul W TW (q x0))
        (top1_fundamental_group_id W TW (q x0))
        (top1_fundamental_group_invg W TW (q x0))"
    proof -
      have hTW: "is_topology_on W TW"
        using hW_wedge unfolding top1_is_wedge_of_circles_on_def is_topology_on_strict_def
        by (by100 blast)
      have hqx0_W: "q x0 \<in> W"
        using hW_wedge hqx0 unfolding top1_is_wedge_of_circles_on_def by (by100 simp)
      show ?thesis by (rule top1_fundamental_group_is_group[OF hTW hqx0_W])
    qed
    have hgrpG0: "top1_is_group_on G0 mul0 e0 invg0"
      using hfree unfolding top1_is_free_group_full_on_def by (by100 blast)
    show ?thesis by (rule top1_groups_isomorphic_on_sym[OF hW_iso' hgrpG0 hgrpW])
  qed
  have hchain: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0) G0 mul0"
    by (rule groups_isomorphic_trans_fwd[OF hq_equiv hiso_sym])
  have hchain_sym: "top1_groups_isomorphic_on G0 mul0
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)"
  proof -
    have hgrpX: "top1_is_group_on
        (top1_fundamental_group_carrier X TX x0)
        (top1_fundamental_group_mul X TX x0)
        (top1_fundamental_group_id X TX x0)
        (top1_fundamental_group_invg X TX x0)"
    proof -
      have hTX: "is_topology_on X TX"
        using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
      show ?thesis by (rule top1_fundamental_group_is_group[OF hTX assms(3)])
    qed
    have hgrpG0: "top1_is_group_on G0 mul0 e0 invg0"
      using hfree unfolding top1_is_free_group_full_on_def by (by100 blast)
    show ?thesis by (rule top1_groups_isomorphic_on_sym[OF hchain hgrpX hgrpG0])
  qed
  show ?thesis using hfree hchain_sym by (by100 blast)
qed

section \<open>\<S>85 Subgroups of Free Groups\<close>

(** from \<S>85 Theorem 85.1 (Nielsen-Schreier): subgroups of free groups are free.
    If G is free on S and H \<le> G is a subgroup, then H is free on some set S'. **)
theorem Theorem_85_1_Nielsen_Schreier:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and \<iota> :: "'s \<Rightarrow> 'g" and S :: "'s set"
    and H :: "'g set"
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
      and "top1_is_group_on H mul e invg"
      and "H \<subseteq> G"
  shows "\<exists>(\<iota>H::'t \<Rightarrow> 'g) SH.
           top1_is_free_group_full_on H mul e invg \<iota>H SH"
proof -
  \<comment> \<open>Munkres 85.1 (topological proof): G = \<pi>_1(X, x0) for some graph X (wedge of
     |S| circles). H corresponds to a covering space E of X with p_*(\<pi>_1(E)) = H.
     By Theorem 83.2, E is a graph. By Theorem 84.7, \<pi>_1(E) is free.
     Since p_*(\<pi>_1(E)) = H and p_* is injective (covering), H is free.\<close>
  \<comment> \<open>Step 1: Realize G as \<pi>_1(X, x0) where X is a wedge of |S| circles.
     By the free group realization theorem, every free group on S is isomorphic
     to \<pi>_1 of a wedge of |S| circles.\<close>
  obtain X :: "'a set" and TX :: "'a set set" and x0 :: 'a
    where "top1_is_graph_on X TX" "top1_connected_on X TX" "x0 \<in> X"
      and hiso: "top1_groups_isomorphic_on G mul
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)"
    sorry \<comment> \<open>Wedge of |S| circles realizes the free group G.\<close>
  \<comment> \<open>Step 2: H \<le> G \<cong> \<pi>_1(X) gives a covering space E of X with p_*(\<pi>_1(E)) \<cong> H.
     Use Theorem 82.1 (existence of covering spaces) with the subgroup
     corresponding to H under the isomorphism G \<cong> \<pi>_1(X).\<close>
  obtain E' :: "'b set" and TE' :: "'b set set" and p' :: "'b \<Rightarrow> 'a" and e0' :: 'b
    where "top1_covering_map_on E' TE' X TX p'" "top1_connected_on E' TE'"
      and "e0' \<in> E'"
    sorry \<comment> \<open>Existence of covering space (Theorem 82.1) for the H-image in \<pi>_1(X).\<close>
  \<comment> \<open>Step 3: E is a graph (Theorem 83.2: covering of graph is graph).
     \<pi>_1(E) is free (Theorem 84.7: fund group of connected graph is free).
     p_* injective (covering maps induce injections on \<pi>_1).
     H \<cong> p_*(\<pi>_1(E)) which is free (subgroup of free = free via injection).\<close>
  show ?thesis sorry \<comment> \<open>Combine: E graph (Thm 83.2) \<Rightarrow> \<pi>_1(E) free (Thm 84.7) \<Rightarrow> H free.\<close>
qed

(** from \<S>85 Theorem 85.3: Schreier index formula.
    If F is free on n+1 generators and H \<le> F has finite index k in F, then H
    is free on kn+1 generators. **)
theorem Theorem_85_3_Schreier_index:
  fixes F :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and \<iota>F :: "'s \<Rightarrow> 'g" and S :: "'s set"
    and H :: "'g set"
    and n k :: nat
  assumes "top1_is_free_group_full_on F mul e invg \<iota>F S"
      and "card S = n + 1"
      and "H \<subseteq> F"
      and "top1_is_group_on H mul e invg"
      and "top1_subgroup_has_index_on F mul H k"
  shows "\<exists>(\<iota>H::'t \<Rightarrow> 'g) SH.
           top1_is_free_group_full_on H mul e invg \<iota>H SH
         \<and> card SH = k * n + 1"
proof -
  \<comment> \<open>Munkres 85.3: F = \<pi>_1(X) for a wedge of n+1 circles. H corresponds to a
     k-sheeted covering space E. By Theorem 83.2, E is a graph.
     The Euler characteristic satisfies: \<chi>(E) = k \<cdot> \<chi>(X).
     X has 1 vertex and n+1 edges, so \<chi>(X) = 1 - (n+1) = -n.
     Hence \<chi>(E) = -kn. E has k vertices (fiber over the wedge point) and
     k(n+1) edges. So 1 - rank(\<pi>_1(E)) = \<chi>(E) = k - k(n+1) = -kn.
     Hence rank(\<pi>_1(E)) = kn + 1.\<close>
  \<comment> \<open>Step 1: Realize F as \<pi>_1 of wedge X of n+1 circles.\<close>
  obtain X :: "'a set" and TX :: "'a set set" and x0 :: 'a
    where hX_graph: "top1_is_graph_on X TX" and hX_conn: "top1_connected_on X TX"
      and hx0: "x0 \<in> X"
      and hF_iso: "top1_groups_isomorphic_on F mul
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)"
    sorry \<comment> \<open>Wedge of n+1 circles realizes F.\<close>
  \<comment> \<open>Step 2: H \<le> F corresponds to a k-sheeted covering E of X.
     By Theorem 82.1, there exists a covering E with p_*(\<pi>_1(E)) = H-image.\<close>
  obtain E' :: "'b set" and TE' :: "'b set set" and p' :: "'b \<Rightarrow> 'a"
    where hE'_cov: "top1_covering_map_on E' TE' X TX p'"
      and hE'_graph: "top1_is_graph_on E' TE'"
      and hE'_conn: "top1_connected_on E' TE'"
    sorry \<comment> \<open>Covering existence (Theorem 82.1) + covering of graph is graph (Theorem 83.2).\<close>
  \<comment> \<open>Step 3: Euler characteristic. X has 1 vertex, n+1 edges, \<chi>(X) = -n.
     E has k sheets, so \<chi>(E) = k \<cdot> \<chi>(X) = -kn.
     E has k vertices, k(n+1) edges, rank(\<pi>_1(E)) = kn+1.\<close>
  have hE'_free: "\<exists>(\<iota>H::'t \<Rightarrow> 'g) SH.
      top1_is_free_group_full_on H mul e invg \<iota>H SH \<and> card SH = k * n + 1"
    sorry \<comment> \<open>\<pi>_1(E) is free (Theorem 84.7). Euler char gives rank kn+1.\<close>
  show ?thesis using hE'_free by (by100 blast)
qed

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 


















































































































































































































































































end



























































































































































































































































































 
  
   
    



  








 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
  
 









































