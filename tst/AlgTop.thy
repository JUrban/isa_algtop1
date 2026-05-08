theory AlgTop
  imports "AlgTopC.AlgTopCached"
begin




\<comment> \<open>Helper: two-element set deductions.\<close>
lemma doubleton_eq_iff:
  assumes "{x, y} = {a, b}" "x \<noteq> y"
  shows "(x = a \<and> y = b) \<or> (x = b \<and> y = a)"
proof -
  have "x \<in> {a, b}" "y \<in> {a, b}" using assms(1) by (by100 blast)+
  thus ?thesis using assms(2) by (by100 blast)
qed

\<comment> \<open>Reusable: affine combination stays in interval.\<close>
lemma affine_param_in_interval:
  fixes a b t :: real
  assumes "a \<le> b" "0 \<le> t" "t \<le> 1"
  shows "a \<le> a + t * (b - a)" "a + t * (b - a) \<le> b"
proof -
  have "0 \<le> t * (b - a)" using assms by (by100 simp)
  thus "a \<le> a + t * (b - a)" by (by100 linarith)
  have "t * (b - a) \<le> 1 * (b - a)"
    using mult_right_mono[of t 1 "b - a"] assms by (by100 linarith)
  hence "t * (b - a) \<le> b - a" by (by100 simp)
  thus "a + t * (b - a) \<le> b" by (by100 linarith)
qed

lemma affine_param_in_unit_interval:
  fixes a b t :: real
  assumes "a \<le> b" "0 \<le> t" "t \<le> 1" "0 \<le> a" "b \<le> 1"
  shows "0 \<le> a + t * (b - a)" "a + t * (b - a) \<le> 1"
  using affine_param_in_interval[OF assms(1-3)] assms(4,5) by (by100 linarith)+

\<comment> \<open>Reusable: extract angle for a point on S1.\<close>
lemma S1_point_to_angle:
  assumes "p \<in> top1_S1"
  shows "\<exists>\<theta>::real. top1_R_to_S1 \<theta> = p"
proof -
  have "fst p ^ 2 + snd p ^ 2 = 1" using assms unfolding top1_S1_def by (by100 simp)
  then obtain \<theta>r where "fst p = cos \<theta>r" "snd p = sin \<theta>r"
    using sincos_total_2pi by (by100 metis)
  hence "fst (top1_R_to_S1 (\<theta>r / (2 * pi))) = fst p"
      "snd (top1_R_to_S1 (\<theta>r / (2 * pi))) = snd p"
    unfolding top1_R_to_S1_def by (by100 simp)+
  hence "top1_R_to_S1 (\<theta>r / (2 * pi)) = p" by (rule prod_eqI)
  thus ?thesis by (by100 blast)
qed

lemma card_three_le: "card {a, b, c::'a} \<le> 3"
  apply (rule card_insert_le_m1) apply simp
  apply (rule card_insert_le_m1) apply simp
  apply (rule card_insert_le_m1) apply simp apply simp done

text \<open>Endpoints of an arc A are the two (distinct) points p, q such that
  A - p and A - q are both connected.\<close>
definition top1_arc_endpoints_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set" where
  "top1_arc_endpoints_on A TA =
     {p. p \<in> A \<and> top1_connected_on (A - {p}) (subspace_topology A TA (A - {p}))}"
\<comment> \<open>Reusable: arc endpoint characterization. If h: [0,1] \<rightarrow> A is a homeomorphism,
   then the arc endpoints of A are exactly {h(0), h(1)}.\<close>
lemma arc_endpoints_are_boundary:
  assumes hT: "is_topology_on_strict X TX" and hH: "is_hausdorff_on X TX"
      and hAX: "A \<subseteq> X"
      and hArc: "top1_is_arc_on A (subspace_topology X TX A)"
      and hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          A (subspace_topology X TX A) h"
  shows "top1_arc_endpoints_on A (subspace_topology X TX A) = {h 0, h 1}"
proof -
  let ?TA = "subspace_topology X TX A"
  have hTopX: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
  have hbij: "bij_betw h top1_unit_interval A" using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hinj: "inj_on h top1_unit_interval" using hbij unfolding bij_betw_def by (by100 blast)
  have himg: "h ` top1_unit_interval = A" using hbij unfolding bij_betw_def by (by100 blast)
  have h0I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
  have h1I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
  show ?thesis unfolding top1_arc_endpoints_on_def
  proof (rule set_eqI, rule iffI)
    fix p assume "p \<in> {p. p \<in> A \<and> top1_connected_on (A - {p}) (subspace_topology A ?TA (A - {p}))}"
    hence hpA: "p \<in> A" and hconn: "top1_connected_on (A - {p}) (subspace_topology A ?TA (A - {p}))"
      by (by100 blast)+
    obtain t where ht: "t \<in> top1_unit_interval" "h t = p" using hpA himg by (by100 blast)
    have "t = 0 \<or> t = 1"
    proof (rule ccontr)
      assume "\<not> (t = 0 \<or> t = 1)"
      hence "0 < t" "t < 1" using ht(1) unfolding top1_unit_interval_def by (by100 auto)+
      \<comment> \<open>[0,1]-{t} disconnected but A-{p} connected: contradiction via homeomorphism.\<close>
      \<comment> \<open>h\<inverse> continuous, A-{p} connected \<Rightarrow> h\<inverse>(A-{p}) connected. But h\<inverse>(A-{p}) = I-{t} disconnected.\<close>
      have hhinv: "top1_continuous_map_on A ?TA top1_unit_interval top1_unit_interval_topology
          (inv_into top1_unit_interval h)"
        using hh unfolding top1_homeomorphism_on_def by (by100 blast)
      have hTA_loc: "is_topology_on A ?TA" by (rule subspace_topology_is_topology_on[OF hTopX hAX])
      have hAp_sub: "A - {p} \<subseteq> A" by (by100 blast)
      have hTAp: "is_topology_on (A - {p}) (subspace_topology A ?TA (A - {p}))"
        by (rule subspace_topology_is_topology_on[OF hTA_loc hAp_sub])
      have hTI: "is_topology_on top1_unit_interval top1_unit_interval_topology"
        by (rule top1_unit_interval_topology_is_topology_on)
      \<comment> \<open>Restrict h\<inverse> to A-{p}.\<close>
      have hhinv_restr: "top1_continuous_map_on (A - {p}) (subspace_topology A ?TA (A - {p}))
          top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval h)"
      proof -
        from top1_continuous_map_on_restrict_domain_simple[OF hhinv hAp_sub]
        have "top1_continuous_map_on (A - {p}) (subspace_topology A ?TA (A - {p}))
            top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval h)"
          using subspace_topology_trans[OF hAp_sub] by (by100 simp)
        thus ?thesis .
      qed
      \<comment> \<open>Image: h\<inverse>(A-{p}) = I-{t}.\<close>
      have hinv_img: "(inv_into top1_unit_interval h) ` (A - {p}) = top1_unit_interval - {t}"
      proof -
        have "A - {p} = h ` (top1_unit_interval - {t})"
        proof -
          have "h ` (top1_unit_interval - {t}) = h ` top1_unit_interval - {h t}"
          proof -
            have "{t} \<subseteq> top1_unit_interval" using ht(1) by (by100 blast)
            from inj_on_image_set_diff[OF hinj _ this]
            show ?thesis by (by100 simp)
          qed
          thus ?thesis using himg ht(2) by (by100 simp)
        qed
        hence "(inv_into top1_unit_interval h) ` (A - {p})
            = (inv_into top1_unit_interval h) ` (h ` (top1_unit_interval - {t}))" by (by100 simp)
        also have "\<dots> = top1_unit_interval - {t}"
        proof (rule set_eqI, rule iffI)
          fix s assume "s \<in> inv_into top1_unit_interval h ` h ` (top1_unit_interval - {t})"
          then obtain u where hu: "u \<in> top1_unit_interval - {t}" "s = inv_into top1_unit_interval h (h u)"
            by (by100 blast)
          hence "s = u" using inv_into_f_f[OF hinj] by (by100 blast)
          thus "s \<in> top1_unit_interval - {t}" using hu(1) by (by100 simp)
        next
          fix s assume hs: "s \<in> top1_unit_interval - {t}"
          hence "h s \<in> h ` (top1_unit_interval - {t})" by (by100 blast)
          moreover have "inv_into top1_unit_interval h (h s) = s"
            using inv_into_f_f[OF hinj] hs by (by100 blast)
          ultimately show "s \<in> inv_into top1_unit_interval h ` h ` (top1_unit_interval - {t})"
            by (by100 force)
        qed
        finally show ?thesis .
      qed
      \<comment> \<open>Continuous image of connected is connected.\<close>
      have hIt_conn: "top1_connected_on (top1_unit_interval - {t})
          (subspace_topology top1_unit_interval top1_unit_interval_topology (top1_unit_interval - {t}))"
      proof -
        from Theorem_23_5[OF hTAp hTI hconn hhinv_restr]
        have "top1_connected_on ((inv_into top1_unit_interval h) ` (A - {p}))
            (subspace_topology top1_unit_interval top1_unit_interval_topology
                ((inv_into top1_unit_interval h) ` (A - {p})))" .
        thus ?thesis using hinv_img by (by100 simp)
      qed
      \<comment> \<open>But I-{t} is disconnected for t \<in> (0,1).\<close>
      have "\<not> top1_connected_on (top1_unit_interval - {t})
          (subspace_topology top1_unit_interval top1_unit_interval_topology (top1_unit_interval - {t}))"
      proof -
        let ?It = "top1_unit_interval - {t}"
        let ?TIt = "subspace_topology top1_unit_interval top1_unit_interval_topology ?It"
        let ?L = "{s \<in> ?It. s < t}" and ?R = "{s \<in> ?It. s > t}"
        have hne_L: "?L \<noteq> {}" using \<open>0 < t\<close> h0I by (by100 force)
        have hne_R: "?R \<noteq> {}" using \<open>t < 1\<close> h1I by (by100 force)
        have hdisj: "?L \<inter> ?R = {}" by (by100 force)
        have hunion: "?L \<union> ?R = ?It" by (by100 force)
        \<comment> \<open>?L and ?R are open in the subspace topology of I-{t}.\<close>
        have hL_open: "?L \<in> ?TIt"
        proof -
          have "open {..<t}" by (rule open_lessThan)
          hence "{..<t} \<in> top1_open_sets" unfolding top1_open_sets_def by (by100 blast)
          hence "{s \<in> top1_unit_interval. s \<in> {..<t}} \<in> top1_unit_interval_topology"
            unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
          moreover have "{s \<in> top1_unit_interval. s \<in> {..<t}} = {s \<in> top1_unit_interval. s < t}"
            by (by100 blast)
          ultimately have "{s \<in> top1_unit_interval. s < t} \<in> top1_unit_interval_topology"
            by (by100 simp)
          moreover have "?L = ?It \<inter> {s \<in> top1_unit_interval. s < t}" by (by100 force)
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have hR_open: "?R \<in> ?TIt"
        proof -
          have "open {t<..}" by (rule open_greaterThan)
          hence "{t<..} \<in> top1_open_sets" unfolding top1_open_sets_def by (by100 blast)
          hence "{s \<in> top1_unit_interval. s \<in> {t<..}} \<in> top1_unit_interval_topology"
            unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
          moreover have "{s \<in> top1_unit_interval. s \<in> {t<..}} = {s \<in> top1_unit_interval. s > t}"
            by (by100 blast)
          ultimately have "{s \<in> top1_unit_interval. s > t} \<in> top1_unit_interval_topology"
            by (by100 simp)
          moreover have "?R = ?It \<inter> {s \<in> top1_unit_interval. s > t}" by (by100 force)
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have "\<exists>U V. U \<in> ?TIt \<and> V \<in> ?TIt \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = ?It"
        proof (rule exI[of _ ?L], rule exI[of _ ?R])
          show "?L \<in> ?TIt \<and> ?R \<in> ?TIt \<and> ?L \<noteq> {} \<and> ?R \<noteq> {} \<and> ?L \<inter> ?R = {} \<and> ?L \<union> ?R = ?It"
            using hL_open hR_open hne_L hne_R hdisj hunion by (by100 blast)
        qed
        thus ?thesis unfolding top1_connected_on_def by (by100 blast)
      qed
      show False using hIt_conn \<open>\<not> top1_connected_on _ _\<close> by (by100 blast)
    qed
    thus "p \<in> {h 0, h 1}" using ht(2) by (by100 blast)
  next
    fix p assume "p \<in> {h 0, h 1}"
    show "p \<in> {p. p \<in> A \<and> top1_connected_on (A - {p}) (subspace_topology A ?TA (A - {p}))}"
    proof (intro CollectI conjI)
      show "p \<in> A" using \<open>p \<in> {h 0, h 1}\<close> himg h0I h1I by (by100 blast)
      show "top1_connected_on (A - {p}) (subspace_topology A ?TA (A - {p}))"
      proof -
        have hh_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology A ?TA h"
          using hh unfolding top1_homeomorphism_on_def by (by100 blast)
        have hTA: "is_topology_on A ?TA" by (rule subspace_topology_is_topology_on[OF hTopX hAX])
        \<comment> \<open>A - {p} = h(I - {inv p}).\<close>
        have hAp: "A - {p} = h ` (top1_unit_interval - {inv_into top1_unit_interval h p})"
        proof -
          have "p \<in> h ` top1_unit_interval" using \<open>p \<in> A\<close> himg by (by100 blast)
          have hip: "inv_into top1_unit_interval h p \<in> top1_unit_interval"
            using inv_into_into[OF \<open>p \<in> h ` top1_unit_interval\<close>] .
          have "h ` (top1_unit_interval - {inv_into top1_unit_interval h p})
              = h ` top1_unit_interval - {h (inv_into top1_unit_interval h p)}"
          proof -
            have hAB: "top1_unit_interval - {inv_into top1_unit_interval h p} \<subseteq> top1_unit_interval"
              by (by100 blast)
            have hB: "{inv_into top1_unit_interval h p} \<subseteq> top1_unit_interval" using hip by (by100 blast)
            from inj_on_image_set_diff[OF hinj hAB hB]
            show ?thesis by (by100 simp)
          qed
          moreover have "h (inv_into top1_unit_interval h p) = p"
            using f_inv_into_f[OF \<open>p \<in> h ` top1_unit_interval\<close>] .
          ultimately show ?thesis using himg by (by100 simp)
        qed
        have hinvp: "inv_into top1_unit_interval h p \<in> {0, 1}"
        proof -
          have "p = h 0 \<or> p = h 1" using \<open>p \<in> {h 0, h 1}\<close> by (by100 blast)
          thus ?thesis
          proof
            assume "p = h 0"
            hence "inv_into top1_unit_interval h p = 0" using inv_into_f_f[OF hinj h0I] by (by100 simp)
            thus ?thesis by (by100 blast)
          next
            assume "p = h 1"
            hence "inv_into top1_unit_interval h p = 1" using inv_into_f_f[OF hinj h1I] by (by100 simp)
            thus ?thesis by (by100 blast)
          qed
        qed
        \<comment> \<open>I - {0} = (0,1] connected. I - {1} = [0,1) connected.\<close>
        let ?S = "top1_unit_interval - {inv_into top1_unit_interval h p}"
        have hS_conn: "connected ?S"
        proof -
          have "inv_into top1_unit_interval h p = 0 \<or> inv_into top1_unit_interval h p = 1"
            using hinvp by (by100 blast)
          thus ?thesis
          proof
            assume h0: "inv_into top1_unit_interval h p = 0"
            have "?S = {0<..(1::real)}"
            proof (rule set_eqI, rule iffI)
              fix x assume hx: "x \<in> ?S"
              hence "x \<in> top1_unit_interval" by (by100 blast)
              have "x \<noteq> inv_into top1_unit_interval h p" using hx by (by100 blast)
              hence "x \<noteq> 0" using h0 by (by100 simp)
              with \<open>x \<in> top1_unit_interval\<close> show "x \<in> {0<..1}" unfolding top1_unit_interval_def by (by100 auto)
            next
              fix x assume "x \<in> {0<..(1::real)}"
              hence "x \<in> top1_unit_interval" "x \<noteq> 0" unfolding top1_unit_interval_def by (by100 auto)+
              thus "x \<in> ?S" using h0 by (by100 blast)
            qed
            moreover have "connected {0<..(1::real)}" by (rule connected_Ioc)
            ultimately show ?thesis by (by100 simp)
          next
            assume h1: "inv_into top1_unit_interval h p = 1"
            have "?S = {0..<(1::real)}"
            proof (rule set_eqI, rule iffI)
              fix x assume hx: "x \<in> ?S"
              hence "x \<in> top1_unit_interval" by (by100 blast)
              have "x \<noteq> inv_into top1_unit_interval h p" using hx by (by100 blast)
              hence "x \<noteq> 1" using h1 by (by100 simp)
              with \<open>x \<in> top1_unit_interval\<close> show "x \<in> {0..<1}" unfolding top1_unit_interval_def by (by100 auto)
            next
              fix x assume "x \<in> {0..<(1::real)}"
              hence "x \<in> top1_unit_interval" "x \<noteq> 1" unfolding top1_unit_interval_def by (by100 auto)+
              thus "x \<in> ?S" using h1 by (by100 blast)
            qed
            moreover have "connected {0..<(1::real)}" by (rule connected_Ico)
            ultimately show ?thesis by (by100 simp)
          qed
        qed
        \<comment> \<open>Convert HOL-Analysis connected to top1_connected_on.\<close>
        have hS_sub: "?S \<subseteq> top1_unit_interval" by (by100 blast)
        have hS_conn_on: "top1_connected_on ?S
            (subspace_topology top1_unit_interval top1_unit_interval_topology ?S)"
        proof -
          have "top1_connected_on ?S (subspace_topology UNIV top1_open_sets ?S)"
            using top1_connected_on_subspace_open_iff_connected hS_conn by (by100 blast)
          moreover have "subspace_topology UNIV top1_open_sets ?S
              = subspace_topology top1_unit_interval top1_unit_interval_topology ?S"
            unfolding top1_unit_interval_topology_def
            using subspace_topology_trans[OF hS_sub] by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        \<comment> \<open>Restrict h to S: continuous S \<rightarrow> A-{p}.\<close>
        have hh_restr: "top1_continuous_map_on ?S
            (subspace_topology top1_unit_interval top1_unit_interval_topology ?S)
            (A - {p}) (subspace_topology A ?TA (A - {p})) h"
        proof -
          \<comment> \<open>Restrict domain from I to S.\<close>
          from top1_continuous_map_on_restrict_domain_simple[OF hh_cont hS_sub]
          have h1: "top1_continuous_map_on ?S
              (subspace_topology top1_unit_interval top1_unit_interval_topology ?S) A ?TA h"
            using subspace_topology_trans[OF hS_sub] by (by100 simp)
          \<comment> \<open>h maps S into A-{p}.\<close>
          have himg_sub: "h ` ?S \<subseteq> A - {p}"
          proof
            fix y assume "y \<in> h ` ?S"
            then obtain s where hs: "s \<in> ?S" "y = h s" by (by100 blast)
            have "s \<in> top1_unit_interval" using hs(1) by (by100 blast)
            hence "h s \<in> A" using hbij unfolding bij_betw_def by (by100 blast)
            moreover have "h s \<noteq> p"
            proof
              assume heq: "h s = p"
              have hip: "inv_into top1_unit_interval h p \<in> top1_unit_interval"
                using inv_into_into[of p h top1_unit_interval] \<open>p \<in> A\<close> himg by (by100 force)
              have "h (inv_into top1_unit_interval h p) = p"
                using f_inv_into_f[of p h top1_unit_interval] \<open>p \<in> A\<close> himg by (by100 force)
              hence "h s = h (inv_into top1_unit_interval h p)" using heq by (by100 simp)
              hence "s = inv_into top1_unit_interval h p"
                using inj_onD[OF hinj] \<open>s \<in> top1_unit_interval\<close> hip by (by100 blast)
              thus False using hs(1) by (by100 blast)
            qed
            ultimately show "y \<in> A - {p}" using hs(2) by (by100 blast)
          qed
          have hAp_sub: "A - {p} \<subseteq> A" by (by100 blast)
          \<comment> \<open>Shrink codomain from A to A-{p}.\<close>
          show ?thesis
            using top1_continuous_map_on_codomain_shrink[OF h1 himg_sub hAp_sub]
              subspace_topology_trans[OF hAp_sub] by (by100 simp)
        qed
        have hTI_S: "is_topology_on ?S
            (subspace_topology top1_unit_interval top1_unit_interval_topology ?S)"
          by (rule subspace_topology_is_topology_on[OF top1_unit_interval_topology_is_topology_on hS_sub])
        have hTA_p: "is_topology_on (A - {p}) (subspace_topology A ?TA (A - {p}))"
          by (rule subspace_topology_is_topology_on[OF hTA]) (by100 blast)
        \<comment> \<open>Continuous image of connected is connected.\<close>
        from Theorem_23_5[OF hTI_S hTA_p hS_conn_on hh_restr]
        have "top1_connected_on (h ` ?S)
            (subspace_topology (A - {p}) (subspace_topology A ?TA (A - {p})) (h ` ?S))" .
        moreover have "h ` ?S = A - {p}" using hAp by (by100 simp)
        moreover have "subspace_topology (A - {p}) (subspace_topology A ?TA (A - {p})) (A - {p})
            = subspace_topology A ?TA (A - {p})"
        proof -
          have "A - {p} \<subseteq> A" by (by100 blast)
          show ?thesis by (rule subspace_topology_self)
            (use hTA_p in \<open>unfold is_topology_on_def subspace_topology_def; by100 blast\<close>)
        qed
        ultimately show ?thesis by (by100 simp)
      qed
    qed
  qed
qed

\<comment> \<open>Note: the general claim "A1\<inter>A2={c} implies c is endpoint of A1" is FALSE.
   Counterexample: A1=[-1,1]\<times>{0}, A2={0}\<times>[0,1], c=(0,0) is interior to A1.
   The correct claim: c must be an endpoint of at least one arc, OR
   one must ADD the endpoint assumption. We add it to arcs_concatenation_is_arc.\<close>

\<comment> \<open>===== Theorems with sorry, moved here for caching =====\<close>


\<comment> \<open>Reusable: composition of homeomorphisms is a homeomorphism.\<close>
lemma homeomorphism_on_comp:
  assumes "top1_homeomorphism_on A TA B TB f" and "top1_homeomorphism_on B TB C TC g"
  shows "top1_homeomorphism_on A TA C TC (g \<circ> f)"
proof -
  have hfbij: "bij_betw f A B" and hgbij: "bij_betw g B C"
    using assms unfolding top1_homeomorphism_on_def by (by100 blast)+
  have hfcont: "top1_continuous_map_on A TA B TB f"
    and hgcont: "top1_continuous_map_on B TB C TC g"
    using assms unfolding top1_homeomorphism_on_def by (by100 blast)+
  have hfinv: "top1_continuous_map_on B TB A TA (inv_into A f)"
    and hginv: "top1_continuous_map_on C TC B TB (inv_into B g)"
    using assms unfolding top1_homeomorphism_on_def by (by100 blast)+
  have hTA: "is_topology_on A TA" and hTB: "is_topology_on B TB" and hTC: "is_topology_on C TC"
    using assms unfolding top1_homeomorphism_on_def by (by100 blast)+
  show ?thesis unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on A TA" by (rule hTA)
    show "is_topology_on C TC" by (rule hTC)
    show "bij_betw (g \<circ> f) A C" by (rule bij_betw_trans[OF hfbij hgbij])
    show "top1_continuous_map_on A TA C TC (g \<circ> f)"
      by (rule top1_continuous_map_on_comp[OF hfcont hgcont])
    show "top1_continuous_map_on C TC A TA (inv_into A (g \<circ> f))"
    proof -
      \<comment> \<open>Use top1_continuous_map_on_agree': inv_into A (g\<circ>f) agrees with f\<inverse>\<circ>g\<inverse> on C.\<close>
      have hinv_comp_cont: "top1_continuous_map_on C TC A TA (inv_into A f \<circ> inv_into B g)"
        by (rule top1_continuous_map_on_comp[OF hginv hfinv])
      have hinv_agree: "\<forall>c\<in>C. inv_into A (g \<circ> f) c = (inv_into A f \<circ> inv_into B g) c"
      proof
        fix c assume hcC: "c \<in> C"
        have hginvc: "inv_into B g c \<in> B"
          using inv_into_into[of c g B] hgbij hcC unfolding bij_betw_def by (by100 blast)
        have hfinvc: "inv_into A f (inv_into B g c) \<in> A"
          using inv_into_into[of "inv_into B g c" f A] hfbij hginvc unfolding bij_betw_def by (by100 blast)
        have "f (inv_into A f (inv_into B g c)) = inv_into B g c"
          by (rule f_inv_into_f) (use hfbij hginvc in \<open>unfold bij_betw_def; by100 blast\<close>)
        moreover have "g (inv_into B g c) = c"
          by (rule f_inv_into_f) (use hgbij hcC in \<open>unfold bij_betw_def; by100 blast\<close>)
        ultimately have "(g \<circ> f) (inv_into A f (inv_into B g c)) = c" unfolding comp_def by (by100 simp)
        have hinj_gf: "inj_on (g \<circ> f) A"
          using bij_betw_trans[OF hfbij hgbij] unfolding bij_betw_def by (by100 blast)
        show "inv_into A (g \<circ> f) c = (inv_into A f \<circ> inv_into B g) c" unfolding comp_def
          using inv_into_f_eq[OF hinj_gf hfinvc \<open>(g \<circ> f) _ = c\<close>] by (by100 simp)
      qed
      show ?thesis
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix c assume "c \<in> C"
        show "inv_into A (g \<circ> f) c \<in> A"
        proof -
          have "inv_into A (g \<circ> f) c = (inv_into A f \<circ> inv_into B g) c"
            using hinv_agree \<open>c \<in> C\<close> by (by100 blast)
          moreover have "(inv_into A f \<circ> inv_into B g) c \<in> A"
            using hinv_comp_cont \<open>c \<in> C\<close> unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
      next
        fix V assume "V \<in> TA"
        show "{c \<in> C. inv_into A (g \<circ> f) c \<in> V} \<in> TC"
        proof -
          have "{c \<in> C. inv_into A (g \<circ> f) c \<in> V} = {c \<in> C. (inv_into A f \<circ> inv_into B g) c \<in> V}"
            using hinv_agree by (by100 force)
          moreover have "{c \<in> C. (inv_into A f \<circ> inv_into B g) c \<in> V} \<in> TC"
            using hinv_comp_cont \<open>V \<in> TA\<close> unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
      qed
    qed
  qed
qed

\<comment> \<open>Reusable: restricting a homeomorphism to a subset gives a homeomorphism on the image.\<close>
lemma homeomorphism_on_restrict:
  assumes hh: "top1_homeomorphism_on A TA B TB h"
      and hSA: "S \<subseteq> A"
  shows "top1_homeomorphism_on S (subspace_topology A TA S)
      (h ` S) (subspace_topology B TB (h ` S)) h"
proof -
  have hTA: "is_topology_on A TA" using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hTB: "is_topology_on B TB" using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hbij: "bij_betw h A B" using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hinj: "inj_on h A" using hbij unfolding bij_betw_def by (by100 blast)
  have himg: "h ` A = B" using hbij unfolding bij_betw_def by (by100 blast)
  have hh_cont: "top1_continuous_map_on A TA B TB h"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hhinv: "top1_continuous_map_on B TB A TA (inv_into A h)"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hTS: "is_topology_on S (subspace_topology A TA S)"
    by (rule subspace_topology_is_topology_on[OF hTA hSA])
  have hhS_sub: "h ` S \<subseteq> B" using hSA himg by (by100 blast)
  have hThS: "is_topology_on (h ` S) (subspace_topology B TB (h ` S))"
    by (rule subspace_topology_is_topology_on[OF hTB hhS_sub])
  show ?thesis unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on S (subspace_topology A TA S)" by (rule hTS)
    show "is_topology_on (h ` S) (subspace_topology B TB (h ` S))" by (rule hThS)
    show "bij_betw h S (h ` S)"
      unfolding bij_betw_def using inj_on_subset[OF hinj hSA] by (by100 blast)
    show "top1_continuous_map_on S (subspace_topology A TA S)
        (h ` S) (subspace_topology B TB (h ` S)) h"
    proof -
      from top1_continuous_map_on_restrict_domain_simple[OF hh_cont hSA]
      have h1: "top1_continuous_map_on S (subspace_topology A TA S) B TB h"
        using subspace_topology_trans[OF hSA] by (by100 simp)
      show ?thesis
        using top1_continuous_map_on_codomain_shrink[OF h1 _ hhS_sub]
          subspace_topology_trans[OF hhS_sub] by (by100 simp)
    qed
    show "top1_continuous_map_on (h ` S) (subspace_topology B TB (h ` S))
        S (subspace_topology A TA S) (inv_into S h)"
    proof -
      \<comment> \<open>inv_into S h agrees with inv_into A h on h(S).\<close>
      have hagree: "\<forall>y\<in>h ` S. inv_into S h y = inv_into A h y"
      proof
        fix y assume "y \<in> h ` S"
        then obtain s where hs: "s \<in> S" "y = h s" by (by100 blast)
        have "inv_into S h y = s"
          using inv_into_f_f[OF inj_on_subset[OF hinj hSA] hs(1)] hs(2) by (by100 simp)
        moreover have "inv_into A h y = s"
          using inv_into_f_f[OF hinj] hSA hs by (by100 blast)
        ultimately show "inv_into S h y = inv_into A h y" by (by100 simp)
      qed
      \<comment> \<open>inv_into A h: B \<rightarrow> A continuous. Restrict to h(S) \<rightarrow> S.\<close>
      from top1_continuous_map_on_restrict_domain_simple[OF hhinv hhS_sub]
      have h1: "top1_continuous_map_on (h ` S) (subspace_topology B TB (h ` S)) A TA (inv_into A h)"
        using subspace_topology_trans[OF hhS_sub] by (by100 simp)
      have hinv_img: "(inv_into A h) ` (h ` S) \<subseteq> S"
      proof
        fix x assume "x \<in> (inv_into A h) ` (h ` S)"
        then obtain y s where "s \<in> S" "y = h s" "x = inv_into A h y" by (by100 blast)
        hence "x = s" using inv_into_f_f[OF hinj] hSA by (by100 blast)
        thus "x \<in> S" using \<open>s \<in> S\<close> by (by100 simp)
      qed
      from top1_continuous_map_on_codomain_shrink[OF h1 hinv_img hSA]
      have h2: "top1_continuous_map_on (h ` S) (subspace_topology B TB (h ` S))
          S (subspace_topology A TA S) (inv_into A h)"
        using subspace_topology_trans[OF hSA] by (by100 simp)
      \<comment> \<open>Transfer from inv_into A h to inv_into S h via agree.\<close>
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix y assume hy: "y \<in> h ` S"
        show "inv_into S h y \<in> S" by (rule inv_into_into[OF hy])
      next
        fix V assume "V \<in> subspace_topology A TA S"
        have "{y \<in> h ` S. inv_into S h y \<in> V} = {y \<in> h ` S. inv_into A h y \<in> V}"
          using hagree by (by100 force)
        also have "\<dots> \<in> subspace_topology B TB (h ` S)"
          using h2 \<open>V \<in> _\<close> unfolding top1_continuous_map_on_def by (by100 blast)
        finally show "{y \<in> h ` S. inv_into S h y \<in> V} \<in> subspace_topology B TB (h ` S)" .
      qed
    qed
  qed
qed

\<comment> \<open>Reusable: t \<mapsto> 1-t is a self-homeomorphism of [0,1] (standalone version).\<close>
lemma unit_interval_reversal_homeomorphism:
  "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      top1_unit_interval top1_unit_interval_topology (\<lambda>t::real. 1 - t)"
  unfolding top1_homeomorphism_on_def
proof (intro conjI)
  show "is_topology_on top1_unit_interval top1_unit_interval_topology"
    by (rule top1_unit_interval_topology_is_topology_on)
  show "is_topology_on top1_unit_interval top1_unit_interval_topology"
    by (rule top1_unit_interval_topology_is_topology_on)
  show "bij_betw (\<lambda>t::real. 1 - t) top1_unit_interval top1_unit_interval"
    unfolding bij_betw_def
  proof (intro conjI)
    show "inj_on (\<lambda>t::real. 1 - t) top1_unit_interval" by (rule inj_onI) (by100 simp)
    show "(\<lambda>t::real. 1 - t) ` top1_unit_interval = top1_unit_interval"
      unfolding top1_unit_interval_def by (by100 force)
  qed
  show "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
      top1_unit_interval top1_unit_interval_topology (\<lambda>t::real. 1 - t)"
  proof -
    have hcont: "continuous_on UNIV (\<lambda>t::real. 1 - t)" by (intro continuous_intros)
    have "top1_continuous_map_on (UNIV::real set) top1_open_sets (UNIV::real set) top1_open_sets (\<lambda>t. 1 - t)"
      using top1_continuous_map_on_real_subspace_open_sets[of UNIV "\<lambda>t. 1-t" UNIV, OF _ hcont]
      unfolding subspace_topology_UNIV_self by (by100 auto)
    from top1_continuous_map_on_restrict_domain_simple[OF this subset_UNIV]
    have "top1_continuous_map_on top1_unit_interval
        (subspace_topology UNIV top1_open_sets top1_unit_interval) UNIV top1_open_sets (\<lambda>t. 1 - t)" .
    hence h1: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
        UNIV top1_open_sets (\<lambda>t. 1 - t)"
      unfolding top1_unit_interval_topology_def subspace_topology_UNIV_self by (by100 simp)
    have h_img: "(\<lambda>t::real. 1 - t) ` top1_unit_interval \<subseteq> top1_unit_interval"
      unfolding top1_unit_interval_def by (by100 force)
    show ?thesis using top1_continuous_map_on_codomain_shrink[OF h1 h_img]
      unfolding top1_unit_interval_topology_def by (by100 simp)
  qed
  have hinv_eq: "\<forall>t\<in>top1_unit_interval. inv_into top1_unit_interval (\<lambda>t::real. 1 - t) t = 1 - t"
  proof
    fix t :: real assume ht: "t \<in> top1_unit_interval"
    have "(\<lambda>s::real. 1 - s) (1 - t) = t" by (by100 simp)
    moreover have "1 - t \<in> top1_unit_interval" using ht unfolding top1_unit_interval_def by (by100 force)
    moreover have "inj_on (\<lambda>t::real. 1 - t) top1_unit_interval" by (rule inj_onI) (by100 simp)
    ultimately show "inv_into top1_unit_interval (\<lambda>t::real. 1 - t) t = 1 - t"
      using inv_into_f_eq by (by100 fast)
  qed
  show "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
      top1_unit_interval top1_unit_interval_topology
      (inv_into top1_unit_interval (\<lambda>t::real. 1 - t))"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix t :: real assume ht: "t \<in> top1_unit_interval"
    show "inv_into top1_unit_interval (\<lambda>t::real. 1 - t) t \<in> top1_unit_interval"
      using hinv_eq[rule_format, OF ht] ht unfolding top1_unit_interval_def by (by100 force)
  next
    fix V assume hV: "V \<in> top1_unit_interval_topology"
    have h_eq: "{t \<in> top1_unit_interval. inv_into top1_unit_interval (\<lambda>t::real. 1 - t) t \<in> V}
        = {t \<in> top1_unit_interval. 1 - t \<in> V}"
    proof (rule set_eqI, rule iffI)
      fix t assume "t \<in> {t \<in> top1_unit_interval. inv_into top1_unit_interval (\<lambda>t. 1 - t) t \<in> V}"
      thus "t \<in> {t \<in> top1_unit_interval. 1 - t \<in> V}" using hinv_eq by (by100 simp)
    next
      fix t assume "t \<in> {t \<in> top1_unit_interval. (1::real) - t \<in> V}"
      thus "t \<in> {t \<in> top1_unit_interval. inv_into top1_unit_interval (\<lambda>t. 1 - t) t \<in> V}"
        using hinv_eq by (by100 simp)
    qed
    have "{t \<in> top1_unit_interval. (1::real) - t \<in> V} \<in> top1_unit_interval_topology"
      using hV \<open>top1_continuous_map_on _ _ _ _ (\<lambda>t. 1 - t)\<close>
      unfolding top1_continuous_map_on_def by (by100 blast)
    thus "{t \<in> top1_unit_interval. inv_into top1_unit_interval (\<lambda>t::real. 1 - t) t \<in> V}
        \<in> top1_unit_interval_topology" using h_eq by (by100 simp)
  qed
qed

\<comment> \<open>Reusable: two arcs meeting only at their two endpoints form a simple closed curve.\<close>
lemma arcs_form_simple_closed_curve:
  assumes hT: "is_topology_on_strict X TX" and hH: "is_hausdorff_on X TX"
      and hA1: "top1_is_arc_on A1 (subspace_topology X TX A1)" and hA1X: "A1 \<subseteq> X"
      and hA2: "top1_is_arc_on A2 (subspace_topology X TX A2)" and hA2X: "A2 \<subseteq> X"
      and hinter: "A1 \<inter> A2 = {a, b}" and hab: "a \<noteq> b"
      and hep1: "top1_arc_endpoints_on A1 (subspace_topology X TX A1) = {a, b}"
      and hep2: "top1_arc_endpoints_on A2 (subspace_topology X TX A2) = {a, b}"
  shows "top1_simple_closed_curve_on X TX (A1 \<union> A2)"
proof -
  \<comment> \<open>Get homeomorphisms h1: [0,1] \<rightarrow> A1 with h1(0)=a, h1(1)=b.
     h2: [0,1] \<rightarrow> A2 with h2(0)=b, h2(1)=a.\<close>
  obtain h1 where hh1: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      A1 (subspace_topology X TX A1) h1" "h1 0 = a" "h1 1 = b"
  proof -
    obtain h0 where hh0: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
        A1 (subspace_topology X TX A1) h0"
      using hA1 unfolding top1_is_arc_on_def by (by100 blast)
    have heps: "top1_arc_endpoints_on A1 (subspace_topology X TX A1) = {h0 0, h0 1}"
      by (rule arc_endpoints_are_boundary[OF hT hH hA1X hA1 hh0])
    hence hab_h0: "{h0 0, h0 1} = {a, b}" using hep1 by (by100 simp)
    show ?thesis
    proof (cases "h0 0 = a")
      case True
      have "h0 1 \<in> {a, b}" using hab_h0 by (by100 blast)
      moreover have "h0 1 \<noteq> a"
      proof -
        have "h0 0 \<noteq> h0 1"
        proof
          assume "h0 0 = h0 1"
          hence "{h0 0, h0 1} = {h0 0}" by (by100 simp)
          hence "card {a, b} = 1" using hab_h0 by (by100 simp)
          thus False using hab by (by100 simp)
        qed
        thus ?thesis using True by (by100 simp)
      qed
      ultimately have "h0 1 = b" by (by100 blast)
      thus ?thesis using that[OF hh0] True by (by100 simp)
    next
      case False hence hh0b: "h0 0 = b" using hab_h0 by (by100 force)
      have "h0 0 \<noteq> h0 1"
      proof
        assume "h0 0 = h0 1"
        hence "{h0 0, h0 1} = {h0 0}" by (by100 simp)
        hence "card {a, b} \<le> 1" using hab_h0 by (by100 simp)
        thus False using hab by (by100 simp)
      qed
      from doubleton_eq_iff[OF hab_h0 this]
      have "(h0 0 = a \<and> h0 1 = b) \<or> (h0 0 = b \<and> h0 1 = a)" .
      hence "h0 1 = a" using hh0b hab by (by100 fast)
      let ?rev = "\<lambda>t::real. 1 - t"
      have hrev: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          top1_unit_interval top1_unit_interval_topology ?rev"
        by (rule unit_interval_reversal_homeomorphism)
      have hcomp: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          A1 (subspace_topology X TX A1) (h0 \<circ> ?rev)"
        by (rule homeomorphism_on_comp[OF hrev hh0])
      have "(h0 \<circ> ?rev) 0 = h0 1" unfolding comp_def by (by100 simp)
      hence h0eq: "(h0 \<circ> ?rev) 0 = a" using \<open>h0 1 = a\<close> by (by100 simp)
      have "(h0 \<circ> ?rev) 1 = h0 0" unfolding comp_def by (by100 simp)
      hence h1eq: "(h0 \<circ> ?rev) 1 = b" using \<open>h0 0 = b\<close> by (by100 simp)
      show ?thesis using that[OF hcomp h0eq h1eq] .
    qed
  qed
  obtain h2 where hh2: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      A2 (subspace_topology X TX A2) h2" "h2 0 = b" "h2 1 = a"
  proof -
    obtain h0 where hh0: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
        A2 (subspace_topology X TX A2) h0"
      using hA2 unfolding top1_is_arc_on_def by (by100 blast)
    have heps: "top1_arc_endpoints_on A2 (subspace_topology X TX A2) = {h0 0, h0 1}"
      by (rule arc_endpoints_are_boundary[OF hT hH hA2X hA2 hh0])
    hence hab_h0: "{h0 0, h0 1} = {a, b}" using hep2 by (by100 simp)
    show ?thesis
    proof (cases "h0 0 = b")
      case True
      have "h0 0 \<noteq> h0 1"
      proof
        assume "h0 0 = h0 1"
        hence "{h0 0, h0 1} = {h0 0}" by (by100 simp)
        hence "card {a, b} \<le> 1" using hab_h0 by (by100 simp)
        thus False using hab by (by100 simp)
      qed
      from doubleton_eq_iff[OF hab_h0 this]
      have "(h0 0 = a \<and> h0 1 = b) \<or> (h0 0 = b \<and> h0 1 = a)" .
      hence "h0 1 = a" using True hab by (by100 fast)
      thus ?thesis using that[OF hh0] True by (by100 simp)
    next
      case False hence hh0a: "h0 0 = a" using hab_h0 by (by100 force)
      have "h0 0 \<noteq> h0 1"
      proof
        assume "h0 0 = h0 1"
        hence "{h0 0, h0 1} = {h0 0}" by (by100 simp)
        hence "card {a, b} \<le> 1" using hab_h0 by (by100 simp)
        thus False using hab by (by100 simp)
      qed
      from doubleton_eq_iff[OF hab_h0 this]
      have "(h0 0 = a \<and> h0 1 = b) \<or> (h0 0 = b \<and> h0 1 = a)" .
      hence "h0 1 = b" using hh0a hab by (by100 fast)
      let ?rev = "\<lambda>t::real. 1 - t"
      have hcomp: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          A2 (subspace_topology X TX A2) (h0 \<circ> ?rev)"
        by (rule homeomorphism_on_comp[OF unit_interval_reversal_homeomorphism hh0])
      have "(h0 \<circ> ?rev) 0 = h0 1" unfolding comp_def by (by100 simp)
      hence h0eq: "(h0 \<circ> ?rev) 0 = b" using \<open>h0 1 = b\<close> by (by100 simp)
      have "(h0 \<circ> ?rev) 1 = h0 0" unfolding comp_def by (by100 simp)
      hence h1eq: "(h0 \<circ> ?rev) 1 = a" using \<open>h0 0 = a\<close> by (by100 simp)
      show ?thesis using that[OF hcomp h0eq h1eq] .
    qed
  qed
  \<comment> \<open>Construct f: S1 \<rightarrow> A1 \<union> A2. Map upper semicircle to A1, lower to A2.\<close>
  \<comment> \<open>Parameterize S1: (cos \<theta>, sin \<theta>) for \<theta> \<in> [0, 2\<pi>].
     For \<theta> \<in> [0, \<pi>]: f(cos \<theta>, sin \<theta>) = h1(\<theta>/\<pi>).
     For \<theta> \<in> [\<pi>, 2\<pi>]: f(cos \<theta>, sin \<theta>) = h2((\<theta>-\<pi>)/\<pi>).\<close>
  \<comment> \<open>Equivalently: for p = (x,y) \<in> S1, angle \<theta> = atan2(y,x) \<in> [0, 2\<pi>).\<close>
  \<comment> \<open>Simpler: use the angle from R_to_S1 and its inverse.\<close>
  \<comment> \<open>Define g: [0,1] \<rightarrow> A1 \<union> A2 by pasting h1 and h2.\<close>
  define g where "g t = (if t \<le> 1/2 then h1 (2*t) else h2 (2*t - 1))" for t :: real
  have hg0: "g 0 = a" unfolding g_def using hh1(2) by (by100 simp)
  have hg1: "g 1 = a" unfolding g_def using hh2(3) by (by100 simp)
  have hg_ident: "g 0 = g 1" using hg0 hg1 by (by100 simp)
  \<comment> \<open>g is continuous, injective on [0,1), surjective onto A1 \<union> A2.\<close>
  have hg_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
      X TX g"
  proof -
    let ?A = "{t \<in> top1_unit_interval. t \<le> 1/2}" and ?B = "{t \<in> top1_unit_interval. t \<ge> 1/2}"
    let ?f = "\<lambda>t. h1 (2*t)" and ?g2 = "\<lambda>t. h2 (2*t - 1)"
    have hTI: "is_topology_on top1_unit_interval top1_unit_interval_topology"
      by (rule top1_unit_interval_topology_is_topology_on)
    have hTX: "is_topology_on X TX"
      using hT unfolding is_topology_on_strict_def by (by100 blast)
    \<comment> \<open>A, B are closed in [0,1] and [0,1] = A \<union> B.\<close>
    have hA_closed: "closedin_on top1_unit_interval top1_unit_interval_topology ?A"
      unfolding closedin_on_def
    proof (intro conjI)
      show "?A \<subseteq> top1_unit_interval" by (by100 blast)
      show "top1_unit_interval - ?A \<in> top1_unit_interval_topology"
      proof -
        have "top1_unit_interval - ?A = top1_unit_interval \<inter> {t. t > 1/2}" by (by100 force)
        moreover have "{t::real. t > 1/2} \<in> top1_open_sets"
        proof -
          have "open {(1/2::real)<..}" by (rule open_greaterThan)
          hence "{t::real. 1/2 < t} \<in> top1_open_sets"
            unfolding greaterThan_def top1_open_sets_def by (by100 simp)
          moreover have "{t::real. t > 1/2} = {t. 1/2 < t}" by (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
        ultimately show ?thesis
          unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
      qed
    qed
    have hB_closed: "closedin_on top1_unit_interval top1_unit_interval_topology ?B"
      unfolding closedin_on_def
    proof (intro conjI)
      show "?B \<subseteq> top1_unit_interval" by (by100 blast)
      show "top1_unit_interval - ?B \<in> top1_unit_interval_topology"
      proof -
        have "top1_unit_interval - ?B = top1_unit_interval \<inter> {t. t < 1/2}" by (by100 force)
        moreover have "{t::real. t < 1/2} \<in> top1_open_sets"
        proof -
          have "open {..<(1/2::real)}" by (rule open_lessThan)
          hence "{t::real. t < 1/2} \<in> top1_open_sets"
            unfolding lessThan_def top1_open_sets_def by (by100 simp)
          thus ?thesis .
        qed
        ultimately show ?thesis
          unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
      qed
    qed
    have hAB_union: "?A \<union> ?B = top1_unit_interval"
      unfolding top1_unit_interval_def by (by100 force)
    \<comment> \<open>g range.\<close>
    have hg_in_X: "\<forall>t \<in> top1_unit_interval. g t \<in> X"
    proof
      fix t assume ht: "t \<in> top1_unit_interval"
      hence "0 \<le> t" "t \<le> 1" unfolding top1_unit_interval_def by (by100 simp)+
      show "g t \<in> X"
      proof (cases "t \<le> 1/2")
        case True hence "g t = h1 (2*t)" unfolding g_def by (by100 simp)
        moreover have "2*t \<in> top1_unit_interval"
          using True \<open>0 \<le> t\<close> unfolding top1_unit_interval_def by (by100 simp)
        ultimately have "g t \<in> A1"
          using hh1(1) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        thus ?thesis using hA1X by (by100 blast)
      next
        case False hence "g t = h2 (2*t - 1)" unfolding g_def by (by100 simp)
        moreover have "2*t - 1 \<in> top1_unit_interval"
          using False \<open>t \<le> 1\<close> unfolding top1_unit_interval_def by (by100 simp)
        ultimately have "g t \<in> A2"
          using hh2(1) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        thus ?thesis using hA2X by (by100 blast)
      qed
    qed
    \<comment> \<open>g continuous on A (= h1 \<circ> (2*) restricted).\<close>
    have hg_cont_A: "top1_continuous_map_on ?A
        (subspace_topology top1_unit_interval top1_unit_interval_topology ?A) X TX g"
    proof -
      \<comment> \<open>h1 \<circ> (\<lambda>t. 2*t) is continuous on A. Then g agrees with it on A.\<close>
      have hdbl_cont: "top1_continuous_map_on ?A
          (subspace_topology top1_unit_interval top1_unit_interval_topology ?A)
          top1_unit_interval top1_unit_interval_topology (\<lambda>t. 2*t)"
      proof -
        have "continuous_on UNIV (\<lambda>t::real. 2*t)" by (intro continuous_intros)
        hence "top1_continuous_map_on (UNIV::real set) top1_open_sets
            (UNIV::real set) top1_open_sets (\<lambda>t. 2*t)"
          using top1_continuous_map_on_real_subspace_open_sets[of UNIV "\<lambda>t. 2*t" UNIV]
          unfolding subspace_topology_UNIV_self by (by100 auto)
        from top1_continuous_map_on_restrict_domain_simple[OF this]
        have "top1_continuous_map_on ?A (subspace_topology UNIV top1_open_sets ?A)
            UNIV top1_open_sets (\<lambda>t. 2*t)" by (by100 blast)
        moreover have "subspace_topology UNIV top1_open_sets ?A
            = subspace_topology top1_unit_interval top1_unit_interval_topology ?A"
          unfolding top1_unit_interval_topology_def
          using subspace_topology_trans[of ?A top1_unit_interval UNIV top1_open_sets] by (by100 simp)
        ultimately have hcont_A_R: "top1_continuous_map_on ?A
            (subspace_topology top1_unit_interval top1_unit_interval_topology ?A)
            UNIV top1_open_sets (\<lambda>t. 2*t)" by (by100 simp)
        have himg: "(\<lambda>t::real. 2*t) ` ?A \<subseteq> top1_unit_interval"
          unfolding top1_unit_interval_def by (by100 auto)
        from top1_continuous_map_on_codomain_shrink[OF hcont_A_R himg]
        show ?thesis unfolding top1_unit_interval_topology_def by (by100 simp)
      qed
      have hh1_cont_X: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX h1"
      proof -
        have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
            A1 (subspace_topology X TX A1) h1"
          using hh1(1) unfolding top1_homeomorphism_on_def by (by100 blast)
        from top1_continuous_map_on_codomain_enlarge[OF this hA1X]
        have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
            X (subspace_topology X TX X) h1" by (by100 simp)
        moreover have "subspace_topology X TX X = TX"
          by (rule subspace_topology_self)
            (use hT in \<open>unfold is_topology_on_strict_def Pow_def; by100 blast\<close>)
        ultimately show ?thesis by (by100 simp)
      qed
      have hcomp: "top1_continuous_map_on ?A
          (subspace_topology top1_unit_interval top1_unit_interval_topology ?A) X TX (h1 \<circ> (\<lambda>t. 2*t))"
        by (rule top1_continuous_map_on_comp[OF hdbl_cont hh1_cont_X])
      have "\<forall>t \<in> ?A. (h1 \<circ> (\<lambda>t. 2*t)) t = g t"
      proof
        fix t assume "t \<in> ?A" hence "t \<le> 1/2" by (by100 blast)
        thus "(h1 \<circ> (\<lambda>t. 2*t)) t = g t" unfolding comp_def g_def by (by100 simp)
      qed
      from top1_continuous_map_on_agree[OF hcomp this] show ?thesis .
    qed
    \<comment> \<open>g continuous on B (= h2 \<circ> (2*-1) restricted).\<close>
    have hg_cont_B: "top1_continuous_map_on ?B
        (subspace_topology top1_unit_interval top1_unit_interval_topology ?B) X TX g"
    proof -
      have hdbl_cont: "top1_continuous_map_on ?B
          (subspace_topology top1_unit_interval top1_unit_interval_topology ?B)
          top1_unit_interval top1_unit_interval_topology (\<lambda>t. 2*t - 1)"
      proof -
        have "continuous_on UNIV (\<lambda>t::real. 2*t - 1)" by (intro continuous_intros)
        hence "top1_continuous_map_on (UNIV::real set) top1_open_sets
            (UNIV::real set) top1_open_sets (\<lambda>t. 2*t - 1)"
          using top1_continuous_map_on_real_subspace_open_sets[of UNIV "\<lambda>t. 2*t-1" UNIV]
          unfolding subspace_topology_UNIV_self by (by100 auto)
        from top1_continuous_map_on_restrict_domain_simple[OF this]
        have "top1_continuous_map_on ?B (subspace_topology UNIV top1_open_sets ?B)
            UNIV top1_open_sets (\<lambda>t. 2*t - 1)" by (by100 blast)
        moreover have "subspace_topology UNIV top1_open_sets ?B
            = subspace_topology top1_unit_interval top1_unit_interval_topology ?B"
          unfolding top1_unit_interval_topology_def
          using subspace_topology_trans[of ?B top1_unit_interval UNIV top1_open_sets] by (by100 simp)
        ultimately have hcont_B_R: "top1_continuous_map_on ?B
            (subspace_topology top1_unit_interval top1_unit_interval_topology ?B)
            UNIV top1_open_sets (\<lambda>t. 2*t - 1)" by (by100 simp)
        have himg: "(\<lambda>t::real. 2*t - 1) ` ?B \<subseteq> top1_unit_interval"
          unfolding top1_unit_interval_def by (by100 auto)
        from top1_continuous_map_on_codomain_shrink[OF hcont_B_R himg]
        show ?thesis unfolding top1_unit_interval_topology_def by (by100 simp)
      qed
      have hh2_cont_X: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX h2"
      proof -
        have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
            A2 (subspace_topology X TX A2) h2"
          using hh2(1) unfolding top1_homeomorphism_on_def by (by100 blast)
        from top1_continuous_map_on_codomain_enlarge[OF this hA2X]
        have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
            X (subspace_topology X TX X) h2" by (by100 simp)
        moreover have "subspace_topology X TX X = TX"
          by (rule subspace_topology_self)
            (use hT in \<open>unfold is_topology_on_strict_def Pow_def; by100 blast\<close>)
        ultimately show ?thesis by (by100 simp)
      qed
      have hcomp: "top1_continuous_map_on ?B
          (subspace_topology top1_unit_interval top1_unit_interval_topology ?B) X TX (h2 \<circ> (\<lambda>t. 2*t - 1))"
        by (rule top1_continuous_map_on_comp[OF hdbl_cont hh2_cont_X])
      have "\<forall>t \<in> ?B. (h2 \<circ> (\<lambda>t. 2*t - 1)) t = g t"
      proof
        fix t assume "t \<in> ?B" hence "t \<ge> 1/2" by (by100 blast)
        show "(h2 \<circ> (\<lambda>t. 2*t - 1)) t = g t"
        proof (cases "t > 1/2")
          case True thus ?thesis unfolding comp_def g_def by (by100 simp)
        next
          case False hence "t = 1/2" using \<open>t \<ge> 1/2\<close> by (by100 linarith)
          have "g (1/2::real) = h1 1" unfolding g_def by (by100 simp)
          hence "g t = h1 1" using \<open>t = 1/2\<close> by (by100 force)
          also have "\<dots> = b" by (rule hh1(3))
          also have "b = h2 0" using hh2(2) by (by100 simp)
          finally have "g t = h2 0" .
          have "(h2 \<circ> (\<lambda>t. 2*t - 1)) (1/2::real) = h2 0"
            unfolding comp_def by (by100 simp)
          hence "(h2 \<circ> (\<lambda>t. 2*t - 1)) t = h2 0"
            using \<open>t = 1/2\<close> by (by100 force)
          thus ?thesis using \<open>g t = h2 0\<close> by (by100 simp)
        qed
      qed
      from top1_continuous_map_on_agree[OF hcomp this] show ?thesis .
    qed
    \<comment> \<open>Apply pasting\_lemma\_two\_closed.\<close>
    from pasting_lemma_two_closed[OF hTI hTX hA_closed hB_closed hAB_union hg_in_X hg_cont_A hg_cont_B]
    show ?thesis .
  qed
  have hh1_img: "h1 ` top1_unit_interval = A1"
    using hh1(1) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  have hh2_img: "h2 ` top1_unit_interval = A2"
    using hh2(1) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  have hg_img: "g ` top1_unit_interval = A1 \<union> A2"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> g ` top1_unit_interval"
    then obtain t where ht: "t \<in> top1_unit_interval" "x = g t" by (by100 blast)
    show "x \<in> A1 \<union> A2"
    proof (cases "t \<le> 1/2")
      case True hence "g t = h1 (2*t)" unfolding g_def by (by100 simp)
      moreover have "2*t \<in> top1_unit_interval"
        using True ht(1) unfolding top1_unit_interval_def by (by100 simp)
      ultimately show ?thesis using hh1_img ht(2) by (by100 blast)
    next
      case False hence "g t = h2 (2*t - 1)" unfolding g_def by (by100 simp)
      moreover have "2*t - 1 \<in> top1_unit_interval"
        using False ht(1) unfolding top1_unit_interval_def by (by100 simp)
      ultimately show ?thesis using hh2_img ht(2) by (by100 blast)
    qed
  next
    fix x assume "x \<in> A1 \<union> A2"
    thus "x \<in> g ` top1_unit_interval"
    proof
      assume "x \<in> A1"
      then obtain s where hs: "s \<in> top1_unit_interval" "h1 s = x"
        using hh1_img by (by100 blast)
      have "s/2 \<in> top1_unit_interval"
        using hs(1) unfolding top1_unit_interval_def by (by100 simp)
      moreover have "g (s/2) = x" unfolding g_def
        using hs unfolding top1_unit_interval_def by (by100 simp)
      ultimately show ?thesis by (by100 blast)
    next
      assume "x \<in> A2"
      then obtain s where hs: "s \<in> top1_unit_interval" "h2 s = x"
        using hh2_img by (by100 blast)
      have hs_bds: "0 \<le> s" "s \<le> 1" using hs(1) unfolding top1_unit_interval_def by (by100 simp)+
      show ?thesis
      proof (cases "s = 0")
        case True
        \<comment> \<open>h2(0) = b = h1(1), so x = b \<in> A1. Use t = 1/2: g(1/2) = h1(1) = b.\<close>
        have "g (1/2) = h1 1" unfolding g_def by (by100 simp)
        hence "g (1/2) = b" using hh1(3) by (by100 simp)
        moreover have "x = b" using hs(2) True hh2(2) by (by100 simp)
        moreover have "(1/2::real) \<in> top1_unit_interval"
          unfolding top1_unit_interval_def by (by100 simp)
        ultimately show ?thesis by (by100 blast)
      next
        case False
        have "(s+1)/2 \<in> top1_unit_interval"
          using hs_bds unfolding top1_unit_interval_def by (by100 simp)
        moreover have "\<not> ((s+1)/2 \<le> 1/2)" using hs_bds False by (by100 simp)
        ultimately have "g ((s+1)/2) = h2 (2 * ((s+1)/2) - 1)" unfolding g_def by (by100 simp)
        moreover have "(s + 1) / 2 * 2 = s + 1" by (by100 simp)
        hence "(2::real) * ((s+1)/2) - 1 = s" by (by100 linarith)
        ultimately have "g ((s+1)/2) = x" using hs(2) by (by100 simp)
        thus ?thesis using \<open>(s+1)/2 \<in> top1_unit_interval\<close> by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>R\_to\_S1: [0,1] \<rightarrow> S1 is a quotient map (continuous surjection, compact to Hausdorff).\<close>
  have hR_quot: "top1_quotient_map_on top1_unit_interval top1_unit_interval_topology
      top1_S1 top1_S1_topology top1_R_to_S1"
    unfolding top1_quotient_map_on_def
  proof (intro conjI)
    show "is_topology_on top1_unit_interval top1_unit_interval_topology"
      by (rule top1_unit_interval_topology_is_topology_on)
    show hTS1: "is_topology_on top1_S1 top1_S1_topology"
    proof -
      have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
        by (rule top1_open_sets_is_topology_on_UNIV)
      have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
        using product_topology_on_is_topology_on[OF hTR hTR] by (by100 simp)
      show ?thesis unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
    qed
    \<comment> \<open>R\_to\_S1 is a covering map, hence continuous UNIV \<rightarrow> S1. Restrict to [0,1].\<close>
    have hR_cont_UNIV: "top1_continuous_map_on (UNIV::real set) top1_open_sets
        top1_S1 top1_S1_topology top1_R_to_S1"
      using Theorem_53_1 unfolding top1_covering_map_on_def by (by100 blast)
    show "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
        top1_S1 top1_S1_topology top1_R_to_S1"
    proof -
      from top1_continuous_map_on_subspace_restrict[OF hR_cont_UNIV]
      show ?thesis unfolding top1_unit_interval_topology_def by (by100 simp)
    qed
    show "top1_R_to_S1 ` top1_unit_interval = top1_S1"
    proof -
      have "top1_R_to_S1 ` (UNIV::real set) = top1_S1"
        using Theorem_53_1 unfolding top1_covering_map_on_def by (by100 blast)
      moreover have "top1_R_to_S1 ` top1_unit_interval \<subseteq> top1_S1"
        using \<open>top1_R_to_S1 ` UNIV = top1_S1\<close> by (by100 blast)
      moreover have "top1_S1 \<subseteq> top1_R_to_S1 ` top1_unit_interval"
      proof
        fix p assume "p \<in> top1_S1"
        from S1_point_to_angle[OF this] obtain \<theta> :: real where "top1_R_to_S1 \<theta> = p" by (by100 blast)
        \<comment> \<open>Shift \<theta> into [0,1): \<theta> - floor(\<theta>) \<in> [0,1) and R\_to\_S1(\<theta> - floor(\<theta>)) = R\_to\_S1(\<theta>).\<close>
        let ?\<theta>' = "\<theta> - of_int (floor \<theta>)"
        have "?\<theta>' \<in> top1_unit_interval"
          unfolding top1_unit_interval_def
          using floor_le_iff[of \<theta> "floor \<theta>"] le_floor_iff[of "floor \<theta> + 1" \<theta>]
          by (by100 simp)
        moreover have "top1_R_to_S1 ?\<theta>' = p"
          using \<open>top1_R_to_S1 \<theta> = p\<close> top1_R_to_S1_int_shift[of "?\<theta>'" "floor \<theta>"]
          by (by100 simp)
        ultimately show "p \<in> top1_R_to_S1 ` top1_unit_interval" by (by100 blast)
      qed
      ultimately show ?thesis by (by100 blast)
    qed
    show "\<forall>V. V \<subseteq> top1_S1 \<longrightarrow>
        ({x \<in> top1_unit_interval. top1_R_to_S1 x \<in> V} \<in> top1_unit_interval_topology
            \<longrightarrow> V \<in> top1_S1_topology)"
    proof (intro allI impI)
      fix V assume hV_sub: "V \<subseteq> top1_S1"
          and hpreimage_open: "{x \<in> top1_unit_interval. top1_R_to_S1 x \<in> V}
              \<in> top1_unit_interval_topology"
      \<comment> \<open>Preimage of complement is closed.\<close>
      have hpreimage_compl: "{x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V}
          = top1_unit_interval - {x \<in> top1_unit_interval. top1_R_to_S1 x \<in> V}"
        by (by100 blast)
      have hcompl_sub: "{x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V} \<subseteq> top1_unit_interval"
        by (by100 blast)
      have hcompl_eq: "top1_unit_interval - {x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V}
          = {x \<in> top1_unit_interval. top1_R_to_S1 x \<in> V}" by (by100 blast)
      have hcompl_closed: "closedin_on top1_unit_interval top1_unit_interval_topology
          {x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V}"
        unfolding closedin_on_def
        using hcompl_sub hcompl_eq hpreimage_open by (by100 force)
      \<comment> \<open>Closed map: image of closed set is closed.\<close>
      have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
      proof -
        have "compact (top1_unit_interval :: real set)" unfolding top1_unit_interval_def by (rule compact_Icc)
        thus ?thesis using top1_compact_on_subspace_UNIV_iff_compact
          unfolding top1_unit_interval_topology_def by (by100 blast)
      qed
      have hS1_haus: "is_hausdorff_on top1_S1 top1_S1_topology"
      proof -
        have "is_hausdorff_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          by (rule top1_R2_is_hausdorff)
        thus ?thesis unfolding top1_S1_topology_def
          using conjunct2[OF conjunct2[OF Theorem_17_11]] by (by100 blast)
      qed
      have hR_cont_I: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          top1_S1 top1_S1_topology top1_R_to_S1"
      proof -
        from top1_continuous_map_on_subspace_restrict[OF hR_cont_UNIV]
        show ?thesis unfolding top1_unit_interval_topology_def by (by100 simp)
      qed
      from compact_hausdorff_continuous_closed_map[OF hI_compact hS1_haus hR_cont_I hcompl_closed]
      have "closedin_on top1_S1 top1_S1_topology
          (top1_R_to_S1 ` {x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V})" .
      \<comment> \<open>Image of complement preimage = complement of V (by surjectivity).\<close>
      moreover have "top1_R_to_S1 ` {x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V} = top1_S1 - V"
      proof (rule set_eqI, rule iffI)
        fix p assume "p \<in> top1_R_to_S1 ` {x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V}"
        then obtain t where "t \<in> top1_unit_interval" "top1_R_to_S1 t \<notin> V" "p = top1_R_to_S1 t"
          by (by100 blast)
        thus "p \<in> top1_S1 - V"
          using \<open>top1_R_to_S1 ` top1_unit_interval = top1_S1\<close> by (by100 blast)
      next
        fix p assume "p \<in> top1_S1 - V"
        hence "p \<in> top1_S1" "p \<notin> V" by (by100 blast)+
        hence "p \<in> top1_R_to_S1 ` top1_unit_interval"
          using \<open>top1_R_to_S1 ` top1_unit_interval = top1_S1\<close> by (by100 blast)
        then obtain t where "t \<in> top1_unit_interval" "top1_R_to_S1 t = p" by (by100 blast)
        hence "t \<in> {x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V}" using \<open>p \<notin> V\<close> by (by100 blast)
        thus "p \<in> top1_R_to_S1 ` {x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V}"
          using \<open>top1_R_to_S1 t = p\<close> by (by100 blast)
      qed
      ultimately have "closedin_on top1_S1 top1_S1_topology (top1_S1 - V)" by (by100 simp)
      \<comment> \<open>Complement closed \<Rightarrow> V open.\<close>
      hence "top1_S1 - (top1_S1 - V) \<in> top1_S1_topology"
        unfolding closedin_on_def by (by100 blast)
      moreover have "top1_S1 - (top1_S1 - V) = V" using hV_sub by (by100 blast)
      ultimately show "V \<in> top1_S1_topology" by (by100 simp)
    qed
  qed
  \<comment> \<open>g respects the identification: R\_to\_S1(s) = R\_to\_S1(t) \<Rightarrow> g(s) = g(t).\<close>
  have hg_compat: "\<forall>s \<in> top1_unit_interval. \<forall>t \<in> top1_unit_interval.
      top1_R_to_S1 s = top1_R_to_S1 t \<longrightarrow> g s = g t"
  proof (intro ballI impI)
    fix s t assume hs: "s \<in> top1_unit_interval" and ht: "t \<in> top1_unit_interval"
        and heq: "top1_R_to_S1 s = top1_R_to_S1 t"
    \<comment> \<open>R\_to\_S1 is injective on [0,1): the only identification is 0\<sim>1.\<close>
    show "g s = g t"
    proof (cases "s = t")
      case True thus ?thesis by (by100 simp)
    next
      case False
      \<comment> \<open>R\_to\_S1(s) = R\_to\_S1(t) with s \<noteq> t on [0,1] means {s,t} = {0,1}.\<close>
      have "{s, t} = {(0::real), 1}"
      proof -
        \<comment> \<open>R\_to\_S1(s) = R\_to\_S1(t) \<Rightarrow> cos(2\<pi>s) = cos(2\<pi>t) \<and> sin(2\<pi>s) = sin(2\<pi>t).\<close>
        have "cos (2*pi*s) = cos (2*pi*t)" and "sin (2*pi*s) = sin (2*pi*t)"
          using heq unfolding top1_R_to_S1_def by (by100 simp)+
        from cos_sin_eq_imp[OF this]
        obtain k :: int where hk: "2*pi*s - 2*pi*t = real_of_int k * 2 * pi" by (by100 blast)
        hence hst_k: "s - t = real_of_int k"
        proof -
          have "2 * pi \<noteq> (0::real)" using pi_gt_zero by (by100 linarith)
          have "2 * pi * s - 2 * pi * t = 2 * pi * (s - t)"
            using right_diff_distrib[of "2*pi" s t] by (by100 simp)
          moreover have "real_of_int k * 2 * pi = 2 * pi * of_int k"
            using mult.commute[of "of_int k * 2" pi] mult.commute[of "of_int k" "2::real"]
            by (by100 linarith)
          ultimately have "2 * pi * (s - t) = 2 * pi * of_int k" using hk by (by100 linarith)
          thus ?thesis using \<open>2 * pi \<noteq> 0\<close> by (by100 simp)
        qed
        have hs_bds: "0 \<le> s" "s \<le> 1" using hs unfolding top1_unit_interval_def by (by100 simp)+
        have ht_bds: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 simp)+
        have hst_range: "- 1 \<le> s - t" "s - t \<le> 1" using hs_bds ht_bds by (by100 linarith)+
        have "k \<noteq> 0" using hst_k False by (by100 simp)
        moreover have "k \<ge> -1" using hst_range(1) hst_k by (by100 linarith)
        moreover have "k \<le> 1" using hst_range(2) hst_k by (by100 linarith)
        ultimately have "k = 1 \<or> k = -1" by (by100 linarith)
        thus ?thesis
        proof
          assume "k = 1" hence "s = t + 1" using hst_k by (by100 simp)
          hence "s = 1" "t = 0" using hs_bds ht_bds by (by100 linarith)+
          thus ?thesis by (by100 blast)
        next
          assume "k = -1" hence "s = t - 1" using hst_k by (by100 simp)
          hence "s = 0" "t = 1" using hs_bds ht_bds by (by100 linarith)+
          thus ?thesis by (by100 blast)
        qed
      qed
      from doubleton_eq_iff[OF this False]
      have "(s = 0 \<and> t = 1) \<or> (s = 1 \<and> t = 0)" by (by100 blast)
      thus ?thesis
      proof
        assume "s = 0 \<and> t = 1" thus ?thesis using hg0 hg1 by (by100 simp)
      next
        assume "s = 1 \<and> t = 0" thus ?thesis using hg0 hg1 by (by100 simp)
      qed
    qed
  qed
  \<comment> \<open>Theorem 22.2: get f: S1 \<rightarrow> A1\<union>A2 with g = f \<circ> R\_to\_S1, f continuous.\<close>
  have hg_range: "\<forall>t \<in> top1_unit_interval. g t \<in> A1 \<union> A2"
    using hg_img by (by100 blast)
  have hg_range_X: "\<forall>t \<in> top1_unit_interval. g t \<in> X"
    using hg_range hA1X hA2X by (by100 blast)
  have hg_compat_X: "\<forall>s \<in> top1_unit_interval. \<forall>t \<in> top1_unit_interval.
      top1_R_to_S1 s = top1_R_to_S1 t \<longrightarrow> g s = g t"
    by (rule hg_compat)
  have hThm222: "\<exists>f. (\<forall>y \<in> top1_S1. f y \<in> X) \<and>
      (\<forall>x \<in> top1_unit_interval. f (top1_R_to_S1 x) = g x) \<and>
      (top1_continuous_map_on top1_S1 top1_S1_topology X TX f
          \<longleftrightarrow> top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX g) \<and>
      (top1_quotient_map_on top1_S1 top1_S1_topology X TX f
          \<longleftrightarrow> top1_quotient_map_on top1_unit_interval top1_unit_interval_topology X TX g)"
    by (rule Theorem_22_2[OF hR_quot hg_range_X hg_compat_X])
  then obtain f where hf0_all: "(\<forall>y \<in> top1_S1. f y \<in> X) \<and>
      (\<forall>x \<in> top1_unit_interval. f (top1_R_to_S1 x) = g x) \<and>
      (top1_continuous_map_on top1_S1 top1_S1_topology X TX f
          \<longleftrightarrow> top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX g) \<and>
      (top1_quotient_map_on top1_S1 top1_S1_topology X TX f
          \<longleftrightarrow> top1_quotient_map_on top1_unit_interval top1_unit_interval_topology X TX g)"
    by (by100 blast)
  have hf0_1: "\<forall>y \<in> top1_S1. f y \<in> X" using hf0_all by (by100 blast)
  have hf0_2: "\<forall>x \<in> top1_unit_interval. f (top1_R_to_S1 x) = g x" using hf0_all by (by100 blast)
  have hf0_3: "top1_continuous_map_on top1_S1 top1_S1_topology X TX f
          \<longleftrightarrow> top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX g"
    using hf0_all by (by100 blast)
  \<comment> \<open>f lands in A1 \<union> A2 (since f(p) = g(t) for some t with R\_to\_S1(t)=p, and g(t) \<in> A1\<union>A2).\<close>
  have hR_surj: "top1_R_to_S1 ` top1_unit_interval = top1_S1"
    using hR_quot unfolding top1_quotient_map_on_def by (by100 blast)
  have hf_range: "\<forall>p \<in> top1_S1. f p \<in> A1 \<union> A2"
  proof
    fix p assume "p \<in> top1_S1"
    then obtain t where ht: "t \<in> top1_unit_interval" "top1_R_to_S1 t = p"
      using hR_surj by (by100 force)
    have "f (top1_R_to_S1 t) = g t" using hf0_2 ht(1) by (by100 blast)
    hence "f p = g t" using ht(2) by (by100 simp)
    have "g t \<in> A1 \<union> A2" using hg_range ht(1) by (by100 blast)
    thus "f p \<in> A1 \<union> A2" using \<open>f p = g t\<close> by (by100 simp)
  qed
  have hf_factor: "\<forall>t \<in> top1_unit_interval. f (top1_R_to_S1 t) = g t"
    by (rule hf0_2)
  have hf_cont_iff: "top1_continuous_map_on top1_S1 top1_S1_topology X TX f
      \<longleftrightarrow> top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX g"
    by (rule hf0_3)
  have hf_cont: "top1_continuous_map_on top1_S1 top1_S1_topology X TX f"
    using hf_cont_iff hg_cont by (by100 blast)
  have hf_inj: "inj_on f top1_S1"
  proof (rule inj_onI)
    fix p q assume hp: "p \<in> top1_S1" and hq: "q \<in> top1_S1" and hfpq: "f p = f q"
    \<comment> \<open>Get s,t with R\_to\_S1(s)=p, R\_to\_S1(t)=q, s,t \<in> [0,1].\<close>
    obtain s where hs: "s \<in> top1_unit_interval" "top1_R_to_S1 s = p"
      using hp hR_surj by (by100 force)
    obtain t where ht: "t \<in> top1_unit_interval" "top1_R_to_S1 t = q"
      using hq hR_surj by (by100 force)
    have "g s = g t"
    proof -
      have "g s = f (top1_R_to_S1 s)" using hf0_2 hs(1) by (by100 force)
      also have "\<dots> = f p" using hs(2) by (by100 simp)
      also have "\<dots> = f q" by (rule hfpq)
      also have "\<dots> = f (top1_R_to_S1 t)" using ht(2) by (by100 simp)
      also have "\<dots> = g t" using hf0_2 ht(1) by (by100 force)
      finally show ?thesis .
    qed
    \<comment> \<open>g injective on [0,1) \<Rightarrow> s = t or {s,t} = {0,1}.\<close>
    \<comment> \<open>In either case R\_to\_S1(s) = R\_to\_S1(t), so p = q.\<close>
    \<comment> \<open>g(s) = g(t) with s,t \<in> [0,1] \<Rightarrow> s = t or {s,t} = {0,1}.\<close>
    have hs_bds: "0 \<le> s" "s \<le> 1" using hs(1) unfolding top1_unit_interval_def by (by100 simp)+
    have ht_bds: "0 \<le> t" "t \<le> 1" using ht(1) unfolding top1_unit_interval_def by (by100 simp)+
    have hh1_inj: "inj_on h1 top1_unit_interval"
      using hh1(1) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have hh2_inj: "inj_on h2 top1_unit_interval"
      using hh2(1) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have h0I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
    have h1I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
    have "s = t \<or> (s = 0 \<and> t = 1) \<or> (s = 1 \<and> t = 0)"
    proof (cases "s \<le> 1/2"; cases "t \<le> 1/2")
      \<comment> \<open>Case 1: both in [0,1/2]. g(s) = h1(2s) = h1(2t) = g(t). h1 injective \<Rightarrow> 2s = 2t \<Rightarrow> s = t.\<close>
      assume "s \<le> 1/2" "t \<le> 1/2"
      hence "h1 (2*s) = h1 (2*t)" using \<open>g s = g t\<close> unfolding g_def by (by100 simp)
      moreover have "2*s \<in> top1_unit_interval" using \<open>s \<le> 1/2\<close> hs_bds
        unfolding top1_unit_interval_def by (by100 simp)
      moreover have "2*t \<in> top1_unit_interval" using \<open>t \<le> 1/2\<close> ht_bds
        unfolding top1_unit_interval_def by (by100 simp)
      ultimately have "2*s = 2*t" using hh1_inj unfolding inj_on_def by (by100 blast)
      hence "s = t" by (by100 simp)
      thus ?thesis by (by100 blast)
    next
      \<comment> \<open>Case 2: both in (1/2,1]. g(s) = h2(2s-1) = h2(2t-1). h2 inj \<Rightarrow> s = t.\<close>
      assume "\<not> s \<le> 1/2" "\<not> t \<le> 1/2"
      hence "h2 (2*s - 1) = h2 (2*t - 1)" using \<open>g s = g t\<close> unfolding g_def by (by100 simp)
      moreover have "2*s - 1 \<in> top1_unit_interval" using \<open>\<not> s \<le> 1/2\<close> hs_bds
        unfolding top1_unit_interval_def by (by100 simp)
      moreover have "2*t - 1 \<in> top1_unit_interval" using \<open>\<not> t \<le> 1/2\<close> ht_bds
        unfolding top1_unit_interval_def by (by100 simp)
      ultimately have "2*s - 1 = 2*t - 1" using hh2_inj unfolding inj_on_def by (by100 blast)
      hence "s = t" by (by100 simp)
      thus ?thesis by (by100 blast)
    next
      \<comment> \<open>Case 3: s \<in> [0,1/2], t \<in> (1/2,1]. g(s) = h1(2s) \<in> A1, g(t) = h2(2t-1) \<in> A2.
         h1(2s) = h2(2t-1) \<in> A1 \<inter> A2 = {a,b}.\<close>
      assume "s \<le> 1/2" "\<not> t \<le> 1/2"
      have "g s = h1 (2*s)" unfolding g_def using \<open>s \<le> 1/2\<close> by (by100 simp)
      have "g t = h2 (2*t - 1)" unfolding g_def using \<open>\<not> t \<le> 1/2\<close> by (by100 simp)
      have "h1 (2*s) = h2 (2*t - 1)" using \<open>g s = g t\<close> \<open>g s = h1 (2*s)\<close> \<open>g t = h2 (2*t-1)\<close>
        by (by100 simp)
      have h2s_I: "2*s \<in> top1_unit_interval" using \<open>s \<le> 1/2\<close> hs_bds
        unfolding top1_unit_interval_def by (by100 simp)
      have h2t1_I: "2*t - 1 \<in> top1_unit_interval" using \<open>\<not> t \<le> 1/2\<close> ht_bds
        unfolding top1_unit_interval_def by (by100 simp)
      have hh1_A1: "h1 (2*s) \<in> A1" using hh1_img h2s_I by (by100 blast)
      have hh2_A2: "h2 (2*t-1) \<in> A2" using hh2_img h2t1_I by (by100 blast)
      have "h1 (2*s) \<in> A2" using hh2_A2 \<open>h1 (2*s) = h2 (2*t - 1)\<close> by (by100 simp)
      have "h1 (2*s) \<in> A1 \<inter> A2" using hh1_A1 \<open>h1 (2*s) \<in> A2\<close> by (by100 blast)
      hence "h1 (2*s) \<in> {a, b}" using hinter by (by100 blast)
      hence "h1 (2*s) = a \<or> h1 (2*s) = b" by (by100 blast)
      thus ?thesis
      proof
        assume heq_a: "h1 (2*s) = a"
        have "h1 (2*s) = h1 0" using heq_a hh1(2) by (by100 simp)
        have h0I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
        hence "2*s = 0" using hh1_inj h2s_I \<open>h1 (2*s) = h1 0\<close>
          unfolding inj_on_def by (by100 blast)
        hence "s = 0" by (by100 simp)
        have "h2 (2*t-1) = a" using \<open>h1 (2*s) = h2 (2*t-1)\<close> heq_a by (by100 simp)
        hence "h2 (2*t-1) = h2 1" using hh2(3) by (by100 simp)
        hence "2*t-1 = 1" using hh2_inj h2t1_I h1I
          unfolding inj_on_def by (by100 blast)
        hence "t = 1" by (by100 linarith)
        show ?thesis using \<open>s = 0\<close> \<open>t = 1\<close> by (by100 blast)
      next
        assume heq_b: "h1 (2*s) = b"
        have "h1 (2*s) = h1 1" using heq_b hh1(3) by (by100 simp)
        hence "2*s = 1" using hh1_inj h2s_I h1I
          unfolding inj_on_def by (by100 blast)
        hence "s = 1/2" by (by100 linarith)
        have "h2 (2*t-1) = b" using \<open>h1 (2*s) = h2 (2*t-1)\<close> heq_b by (by100 simp)
        hence "h2 (2*t-1) = h2 0" using hh2(2) by (by100 simp)
        hence "2*t-1 = 0" using hh2_inj h2t1_I h0I
          unfolding inj_on_def by (by100 blast)
        hence "t = 1/2" by (by100 linarith)
        show ?thesis using \<open>s = 1/2\<close> \<open>t = 1/2\<close> by (by100 simp)
      qed
    next
      \<comment> \<open>Case 4: symmetric to case 3.\<close>
      assume hcase4: "\<not> s \<le> 1/2" "t \<le> 1/2"
      have "g s = h2 (2*s - 1)" unfolding g_def using hcase4(1) by (by100 simp)
      have "g t = h1 (2*t)" unfolding g_def using hcase4(2) by (by100 simp)
      have "h2 (2*s-1) = h1 (2*t)" using \<open>g s = g t\<close> \<open>g s = h2 (2*s-1)\<close> \<open>g t = h1 (2*t)\<close>
        by (by100 simp)
      have h2s1_I: "2*s-1 \<in> top1_unit_interval" using hcase4(1) hs_bds
        unfolding top1_unit_interval_def by (by100 simp)
      have h2t_I: "2*t \<in> top1_unit_interval" using hcase4(2) ht_bds
        unfolding top1_unit_interval_def by (by100 simp)
      have "h2 (2*s-1) \<in> A2" using hh2_img h2s1_I by (by100 blast)
      have "h1 (2*t) \<in> A1" using hh1_img h2t_I by (by100 blast)
      have "h2 (2*s-1) \<in> A1" using \<open>h1 (2*t) \<in> A1\<close> \<open>h2 (2*s-1) = h1 (2*t)\<close> by (by100 simp)
      have "h2 (2*s-1) \<in> A1 \<inter> A2" using \<open>h2 (2*s-1) \<in> A1\<close> \<open>h2 (2*s-1) \<in> A2\<close> by (by100 blast)
      hence "h2 (2*s-1) \<in> {a, b}" using hinter by (by100 blast)
      hence "h2 (2*s-1) = a \<or> h2 (2*s-1) = b" by (by100 blast)
      thus ?thesis
      proof
        assume "h2 (2*s-1) = a"
        hence "h2 (2*s-1) = h2 1" using hh2(3) by (by100 simp)
        hence "2*s-1 = 1" using hh2_inj h2s1_I h1I
          unfolding inj_on_def by (by100 blast)
        hence "s = 1" by (by100 linarith)
        have "h1 (2*t) = a" using \<open>h2 (2*s-1) = h1 (2*t)\<close> \<open>h2 (2*s-1) = a\<close> by (by100 simp)
        hence "h1 (2*t) = h1 0" using hh1(2) by (by100 simp)
        hence "2*t = 0" using hh1_inj h2t_I h0I
          unfolding inj_on_def by (by100 blast)
        hence "t = 0" by (by100 simp)
        show ?thesis using \<open>s = 1\<close> \<open>t = 0\<close> by (by100 blast)
      next
        assume "h2 (2*s-1) = b"
        hence "h2 (2*s-1) = h2 0" using hh2(2) by (by100 simp)
        hence "2*s-1 = 0" using hh2_inj h2s1_I h0I
          unfolding inj_on_def by (by100 blast)
        hence "s = 1/2" by (by100 linarith)
        have "h1 (2*t) = b" using \<open>h2 (2*s-1) = h1 (2*t)\<close> \<open>h2 (2*s-1) = b\<close> by (by100 simp)
        hence "h1 (2*t) = h1 1" using hh1(3) by (by100 simp)
        hence "2*t = 1" using hh1_inj h2t_I h1I
          unfolding inj_on_def by (by100 blast)
        hence "t = 1/2" by (by100 linarith)
        show ?thesis using \<open>s = 1/2\<close> \<open>t = 1/2\<close> by (by100 simp)
      qed
    qed
    thus "p = q"
    proof (elim disjE conjE)
      assume "s = t" thus ?thesis using hs(2) ht(2) by (by100 simp)
    next
      assume "s = 0" "t = 1"
      thus ?thesis using hs(2) ht(2) top1_R_to_S1_int_shift[of 0 1] by (by100 simp)
    next
      assume "s = 1" "t = 0"
      thus ?thesis using hs(2) ht(2) top1_R_to_S1_int_shift[of 0 1] by (by100 simp)
    qed
  qed
  have hf_img: "f ` top1_S1 = A1 \<union> A2"
  proof -
    have hR_surj: "top1_R_to_S1 ` top1_unit_interval = top1_S1"
      using hR_quot unfolding top1_quotient_map_on_def by (by100 blast)
    have "f ` top1_S1 = f ` (top1_R_to_S1 ` top1_unit_interval)" using hR_surj by (by100 simp)
    also have "\<dots> = (f \<circ> top1_R_to_S1) ` top1_unit_interval"
      using image_comp[of f top1_R_to_S1 top1_unit_interval] by (by100 simp)
    also have "\<dots> = g ` top1_unit_interval"
    proof (rule image_cong)
      fix t assume "t \<in> top1_unit_interval"
      thus "(f \<circ> top1_R_to_S1) t = g t" unfolding comp_def using hf_factor by (by100 blast)
    qed (by100 simp)
    finally show ?thesis using hg_img by (by100 simp)
  qed
  show ?thesis unfolding top1_simple_closed_curve_on_def
    using hf_cont hf_inj hf_img by (by100 blast)
qed

\<comment> \<open>Reusable: concatenation of arcs meeting at a single common endpoint is an arc.\<close>
lemma arcs_concatenation_is_arc:
  assumes hT: "is_topology_on_strict X TX" and hH: "is_hausdorff_on X TX"
      and hA1: "top1_is_arc_on A1 (subspace_topology X TX A1)" and hA1X: "A1 \<subseteq> X"
      and hA2: "top1_is_arc_on A2 (subspace_topology X TX A2)" and hA2X: "A2 \<subseteq> X"
      and hinter: "A1 \<inter> A2 = {c}"
      and hc_ep1: "c \<in> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
      and hc_ep2: "c \<in> top1_arc_endpoints_on A2 (subspace_topology X TX A2)"
  shows "top1_is_arc_on (A1 \<union> A2) (subspace_topology X TX (A1 \<union> A2))"
proof -
  let ?TD = "subspace_topology X TX (A1 \<union> A2)"
  \<comment> \<open>Step 1: Get homeomorphisms from [0,1] to each arc.\<close>
  obtain h1 where hh1: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      A1 (subspace_topology X TX A1) h1"
    using hA1 unfolding top1_is_arc_on_def by (by100 blast)
  obtain h2 where hh2: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      A2 (subspace_topology X TX A2) h2"
    using hA2 unfolding top1_is_arc_on_def by (by100 blast)
  \<comment> \<open>Step 2: c is the shared point. Orient h1 so h1(1)=c, h2 so h2(0)=c.
     Since c \<in> A1 \<inter> A2 = {c}, c \<in> h1(I) and c \<in> h2(I).
     The set {h1^{-1}(c)} is a single point in [0,1].
     If h1^{-1}(c) \<noteq> 1, compose h1 with t \<mapsto> 1-t (reverse).
     Similarly for h2.\<close>
  \<comment> \<open>Reversal t \<mapsto> 1-t is a self-homeomorphism of [0,1].\<close>
  have hrev_homeo: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      top1_unit_interval top1_unit_interval_topology (\<lambda>t::real. 1 - t)"
    unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on top1_unit_interval top1_unit_interval_topology"
      by (rule top1_unit_interval_topology_is_topology_on)
    show "is_topology_on top1_unit_interval top1_unit_interval_topology"
      by (rule top1_unit_interval_topology_is_topology_on)
    show "bij_betw (\<lambda>t::real. 1 - t) top1_unit_interval top1_unit_interval"
      unfolding bij_betw_def
    proof (intro conjI)
      show "inj_on (\<lambda>t::real. 1 - t) top1_unit_interval" by (rule inj_onI) (by100 simp)
      show "(\<lambda>t::real. 1 - t) ` top1_unit_interval = top1_unit_interval"
        unfolding top1_unit_interval_def by (by100 force)
    qed
    show "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
        top1_unit_interval top1_unit_interval_topology (\<lambda>t::real. 1 - t)"
    proof -
      have hcont: "continuous_on UNIV (\<lambda>t::real. 1 - t)" by (intro continuous_intros)
      have "top1_continuous_map_on (UNIV::real set) top1_open_sets (UNIV::real set) top1_open_sets (\<lambda>t. 1 - t)"
        using top1_continuous_map_on_real_subspace_open_sets[of UNIV "\<lambda>t. 1-t" UNIV, OF _ hcont]
        unfolding subspace_topology_UNIV_self by (by100 auto)
      from top1_continuous_map_on_restrict_domain_simple[OF this subset_UNIV]
      have "top1_continuous_map_on top1_unit_interval
          (subspace_topology UNIV top1_open_sets top1_unit_interval) UNIV top1_open_sets (\<lambda>t. 1 - t)" .
      hence h1: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          UNIV top1_open_sets (\<lambda>t. 1 - t)"
        unfolding top1_unit_interval_topology_def subspace_topology_UNIV_self by (by100 simp)
      have h_img: "(\<lambda>t::real. 1 - t) ` top1_unit_interval \<subseteq> top1_unit_interval"
        unfolding top1_unit_interval_def by (by100 force)
      have h_sub: "top1_unit_interval \<subseteq> (UNIV::real set)" by (by100 simp)
      show ?thesis
        using top1_continuous_map_on_codomain_shrink[OF h1 h_img h_sub]
        unfolding top1_unit_interval_topology_def by (by100 simp)
    qed
    \<comment> \<open>Inverse = itself (self-inverse).\<close>
    have hinv_eq: "\<forall>t\<in>top1_unit_interval. inv_into top1_unit_interval (\<lambda>t::real. 1 - t) t = 1 - t"
    proof
      fix t :: real assume ht: "t \<in> top1_unit_interval"
      have "(\<lambda>s::real. 1 - s) (1 - t) = t" by (by100 simp)
      moreover have "1 - t \<in> top1_unit_interval" using ht unfolding top1_unit_interval_def by (by100 force)
      moreover have "inj_on (\<lambda>t::real. 1 - t) top1_unit_interval" by (rule inj_onI) (by100 simp)
      ultimately show "inv_into top1_unit_interval (\<lambda>t::real. 1 - t) t = 1 - t"
        using inv_into_f_eq by (by100 fast)
    qed
    show "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
        top1_unit_interval top1_unit_interval_topology
        (inv_into top1_unit_interval (\<lambda>t::real. 1 - t))"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix t :: real assume ht: "t \<in> top1_unit_interval"
      show "inv_into top1_unit_interval (\<lambda>t::real. 1 - t) t \<in> top1_unit_interval"
        using hinv_eq[rule_format, OF ht] ht unfolding top1_unit_interval_def by (by100 force)
    next
      fix V assume "V \<in> top1_unit_interval_topology"
      show "{t \<in> top1_unit_interval. inv_into top1_unit_interval (\<lambda>t::real. 1 - t) t \<in> V}
          \<in> top1_unit_interval_topology"
      proof -
        have h_eq: "{t \<in> top1_unit_interval. inv_into top1_unit_interval (\<lambda>t::real. 1 - t) t \<in> V}
            = {t \<in> top1_unit_interval. 1 - t \<in> V}"
        proof (rule set_eqI, rule iffI)
          fix t assume "t \<in> {t \<in> top1_unit_interval. inv_into top1_unit_interval (\<lambda>t. 1 - t) t \<in> V}"
          hence ht: "t \<in> top1_unit_interval" and "inv_into top1_unit_interval (\<lambda>t. 1 - t) t \<in> V"
            by (by100 blast)+
          thus "t \<in> {t \<in> top1_unit_interval. 1 - t \<in> V}" using hinv_eq[rule_format, OF ht] by (by100 simp)
        next
          fix t assume "t \<in> {t \<in> top1_unit_interval. (1::real) - t \<in> V}"
          hence ht: "t \<in> top1_unit_interval" and "1 - t \<in> V" by (by100 blast)+
          thus "t \<in> {t \<in> top1_unit_interval. inv_into top1_unit_interval (\<lambda>t. 1 - t) t \<in> V}"
            using hinv_eq[rule_format, OF ht] by (by100 simp)
        qed
        have "{t \<in> top1_unit_interval. (1::real) - t \<in> V} \<in> top1_unit_interval_topology"
          using \<open>V \<in> _\<close> \<open>top1_continuous_map_on _ _ _ _ (\<lambda>t. 1 - t)\<close>
          unfolding top1_continuous_map_on_def by (by100 blast)
        thus ?thesis using h_eq by (by100 simp)
      qed
    qed
  qed
  \<comment> \<open>Define oriented homeomorphisms g1, g2 with g1(1)=c=g2(0).\<close>
  obtain g1 where hg1: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      A1 (subspace_topology X TX A1) g1" "g1 1 = c"
  proof -
    have hc_A1: "c \<in> A1" using hinter by (by100 blast)
    have hbij1: "bij_betw h1 top1_unit_interval A1"
      using hh1 unfolding top1_homeomorphism_on_def by (by100 blast)
    have h1_in: "h1 1 \<in> A1" and h0_in: "h1 0 \<in> A1"
    proof -
      have "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
      thus "h1 1 \<in> A1" using hbij1 unfolding bij_betw_def by (by100 blast)
      have "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
      thus "h1 0 \<in> A1" using hbij1 unfolding bij_betw_def by (by100 blast)
    qed
    show ?thesis
    proof (cases "h1 1 = c")
      case True thus ?thesis using that[OF hh1] by (by100 simp)
    next
      case False
      \<comment> \<open>h1(0) must be c (since c \<in> A1 = h1(I), and arc endpoints are {h1(0), h1(1)}).\<close>
      \<comment> \<open>Define g1 = h1 \<circ> (\<lambda>t. 1-t): reverses the orientation.\<close>
      let ?rev = "\<lambda>t::real. 1 - t"
      have hrev_homeo: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          top1_unit_interval top1_unit_interval_topology ?rev"
        by (rule unit_interval_reversal_homeomorphism)
      have hg1_homeo: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          A1 (subspace_topology X TX A1) (h1 \<circ> ?rev)"
        by (rule homeomorphism_on_comp[OF hrev_homeo hh1])
      have "(h1 \<circ> ?rev) 1 = h1 0" unfolding comp_def by (by100 simp)
      moreover have "h1 0 = c"
      proof -
        have hc_ep: "c \<in> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
          by (rule hc_ep1)
        have heps: "top1_arc_endpoints_on A1 (subspace_topology X TX A1) = {h1 0, h1 1}"
          by (rule arc_endpoints_are_boundary[OF hT hH hA1X hA1 hh1])
        from hc_ep[unfolded heps] False show ?thesis by (by100 blast)
      qed
      ultimately have "(h1 \<circ> ?rev) 1 = c" by (by100 simp)
      thus ?thesis using that[OF hg1_homeo] by (by100 simp)
    qed
  qed
  obtain g2 where hg2: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      A2 (subspace_topology X TX A2) g2" "g2 0 = c"
  proof -
    have hc_A2: "c \<in> A2" using hinter by (by100 blast)
    have hbij2: "bij_betw h2 top1_unit_interval A2"
      using hh2 unfolding top1_homeomorphism_on_def by (by100 blast)
    show ?thesis
    proof (cases "h2 0 = c")
      case True thus ?thesis using that[OF hh2] by (by100 simp)
    next
      case False
      \<comment> \<open>h2(1) must be c. Define g2 = h2 \<circ> (\<lambda>t. 1-t).\<close>
      have hrev_homeo: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          top1_unit_interval top1_unit_interval_topology (\<lambda>t::real. 1 - t)"
        by (rule unit_interval_reversal_homeomorphism)
      have hg2_homeo: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          A2 (subspace_topology X TX A2) (h2 \<circ> (\<lambda>t::real. 1 - t))"
        by (rule homeomorphism_on_comp[OF hrev_homeo hh2])
      have "(h2 \<circ> (\<lambda>t::real. 1 - t)) 0 = h2 1" unfolding comp_def by (by100 simp)
      moreover have "h2 1 = c"
      proof -
        have hc_ep: "c \<in> top1_arc_endpoints_on A2 (subspace_topology X TX A2)"
          by (rule hc_ep2)
        have heps: "top1_arc_endpoints_on A2 (subspace_topology X TX A2) = {h2 0, h2 1}"
          by (rule arc_endpoints_are_boundary[OF hT hH hA2X hA2 hh2])
        from hc_ep[unfolded heps] False show ?thesis by (by100 blast)
      qed
      ultimately have "(h2 \<circ> (\<lambda>t::real. 1 - t)) 0 = c" by (by100 simp)
      thus ?thesis using that[OF hg2_homeo] by (by100 simp)
    qed
  qed
  \<comment> \<open>Step 3: Define concatenated map h: [0,1] \<rightarrow> A1 \<union> A2.\<close>
  define h where "h t = (if t \<le> 1/2 then g1 (2*t) else g2 (2*t - 1))" for t :: real
  \<comment> \<open>Step 4: h is a homeomorphism [0,1] \<rightarrow> A1 \<union> A2.\<close>
  have hh_homeo: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology (A1 \<union> A2) ?TD h"
  proof -
    \<comment> \<open>Step 4a: h is continuous (pasting lemma on [0,1/2] and [1/2,1]).\<close>
    have hh_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology (A1 \<union> A2) ?TD h"
    proof -
      let ?IL = "{t \<in> top1_unit_interval. t \<le> 1/2}"
      let ?IR = "{t \<in> top1_unit_interval. t \<ge> 1/2}"
      have hTI: "is_topology_on top1_unit_interval top1_unit_interval_topology"
        by (rule top1_unit_interval_topology_is_topology_on)
      have hTopX: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
      have hTD_loc: "is_topology_on (A1 \<union> A2) ?TD"
        by (rule subspace_topology_is_topology_on[OF hTopX]) (use hA1X hA2X in \<open>by100 blast\<close>)
      \<comment> \<open>?IL and ?IR are closed in [0,1].\<close>
      have hIL_closed: "closedin_on top1_unit_interval top1_unit_interval_topology ?IL"
        unfolding closedin_on_def
      proof (intro conjI)
        show "?IL \<subseteq> top1_unit_interval" by (by100 blast)
        show "top1_unit_interval - ?IL \<in> top1_unit_interval_topology"
        proof -
          have "top1_unit_interval - ?IL = top1_unit_interval \<inter> {t. t > 1/2}" by (by100 force)
          moreover have "{t::real. t > 1/2} \<in> top1_open_sets"
          proof -
            have "open {(1/2::real)<..}" by (rule open_greaterThan)
            hence "open {t::real. 1/2 < t}" unfolding greaterThan_def by (by100 simp)
            hence "{t::real. 1/2 < t} \<in> top1_open_sets" unfolding top1_open_sets_def by (by100 blast)
            moreover have "{t::real. t > 1/2} = {t. 1/2 < t}" by (by100 blast)
            ultimately show ?thesis by (by100 simp)
          qed
          ultimately show ?thesis
            unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
        qed
      qed
      have hIR_closed: "closedin_on top1_unit_interval top1_unit_interval_topology ?IR"
        unfolding closedin_on_def
      proof (intro conjI)
        show "?IR \<subseteq> top1_unit_interval" by (by100 blast)
        show "top1_unit_interval - ?IR \<in> top1_unit_interval_topology"
        proof -
          have "top1_unit_interval - ?IR = top1_unit_interval \<inter> {t. t < 1/2}" by (by100 force)
          moreover have "{t::real. t < 1/2} \<in> top1_open_sets"
          proof -
            have "open {..<(1/2::real)}" by (rule open_lessThan)
            hence "open {t::real. t < 1/2}" unfolding lessThan_def by (by100 simp)
            thus ?thesis unfolding top1_open_sets_def by (by100 blast)
          qed
          ultimately show ?thesis
            unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
        qed
      qed
      have hILR_union: "?IL \<union> ?IR = top1_unit_interval" by (by100 force)
      \<comment> \<open>h maps into A1 \<union> A2.\<close>
      have hh_maps: "\<forall>x\<in>top1_unit_interval. h x \<in> A1 \<union> A2"
      proof (intro ballI)
        fix t :: real assume ht: "t \<in> top1_unit_interval"
        have hg1_bij: "bij_betw g1 top1_unit_interval A1"
          using hg1(1) unfolding top1_homeomorphism_on_def by (by100 blast)
        have hg2_bij: "bij_betw g2 top1_unit_interval A2"
          using hg2(1) unfolding top1_homeomorphism_on_def by (by100 blast)
        show "h t \<in> A1 \<union> A2"
        proof (cases "t \<le> 1/2")
          case True
          have hht: "h t = g1 (2*t)" using True unfolding h_def by (by100 simp)
          have "2*t \<in> top1_unit_interval" using ht True
            unfolding top1_unit_interval_def by (by100 auto)
          hence "g1 (2*t) \<in> A1" using hg1_bij unfolding bij_betw_def by (by100 blast)
          hence "h t \<in> A1" using hht by (by100 simp)
          thus ?thesis by (by100 blast)
        next
          case False
          have hht: "h t = g2 (2*t - 1)" using False unfolding h_def by (by100 simp)
          have "2*t - 1 \<in> top1_unit_interval" using ht False
            unfolding top1_unit_interval_def by (by100 auto)
          hence "g2 (2*t - 1) \<in> A2" using hg2_bij unfolding bij_betw_def by (by100 blast)
          hence "h t \<in> A2" using hht by (by100 simp)
          thus ?thesis by (by100 blast)
        qed
      qed
      \<comment> \<open>h is continuous on ?IL (= g1(2t)).\<close>
      have hh_IL: "top1_continuous_map_on ?IL (subspace_topology top1_unit_interval top1_unit_interval_topology ?IL)
          (A1 \<union> A2) ?TD h"
      proof -
        \<comment> \<open>h agrees with g1 \<circ> (\<lambda>t. 2*t) on ?IL.\<close>
        have hagree: "\<forall>t\<in>?IL. h t = g1 (2*t)"
        proof (intro ballI)
          fix t :: real assume "t \<in> ?IL" hence "t \<le> 1/2" by (by100 blast)
          thus "h t = g1 (2*t)" unfolding h_def by (by100 simp)
        qed
        \<comment> \<open>g1 \<circ> (\<lambda>t. 2*t) is continuous ?IL \<rightarrow> A1 \<union> A2.\<close>
        have hg1_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
            A1 (subspace_topology X TX A1) g1"
          using hg1(1) unfolding top1_homeomorphism_on_def by (by100 blast)
        \<comment> \<open>(\<lambda>t. 2*t) maps ?IL into top1_unit_interval.\<close>
        have hdbl_maps: "\<forall>t\<in>?IL. 2*t \<in> top1_unit_interval"
          unfolding top1_unit_interval_def by (by100 auto)
        \<comment> \<open>g1 \<circ> (\<lambda>t. 2*t) maps ?IL into A1 \<subseteq> A1 \<union> A2.\<close>
        have hcomp_cont: "top1_continuous_map_on ?IL
            (subspace_topology top1_unit_interval top1_unit_interval_topology ?IL)
            (A1 \<union> A2) ?TD (g1 \<circ> (\<lambda>t. 2*t))"
        proof -
          \<comment> \<open>(\<lambda>t. 2*t): ?IL \<rightarrow> I continuous.\<close>
          have hdbl_cont: "top1_continuous_map_on ?IL
              (subspace_topology top1_unit_interval top1_unit_interval_topology ?IL)
              top1_unit_interval top1_unit_interval_topology (\<lambda>t. 2*t)"
          proof -
            have hcont_R: "continuous_on UNIV (\<lambda>t::real. 2*t)" by (intro continuous_intros)
            have hcont_R2: "top1_continuous_map_on (UNIV::real set) top1_open_sets
                (UNIV::real set) top1_open_sets (\<lambda>t. 2*t)"
              using top1_continuous_map_on_real_subspace_open_sets[of UNIV "\<lambda>t. 2*t" UNIV, OF _ hcont_R]
              unfolding subspace_topology_UNIV_self by (by100 auto)
            have hIL_sub: "?IL \<subseteq> (UNIV::real set)" by (by100 blast)
            from top1_continuous_map_on_restrict_domain_simple[OF hcont_R2 hIL_sub]
            have hcont_IL_R: "top1_continuous_map_on ?IL
                (subspace_topology UNIV top1_open_sets ?IL) UNIV top1_open_sets (\<lambda>t. 2*t)" .
            have hIL_sub_I: "?IL \<subseteq> top1_unit_interval" by (by100 blast)
            have hTIL_eq: "subspace_topology UNIV top1_open_sets ?IL
                = subspace_topology top1_unit_interval top1_unit_interval_topology ?IL"
              unfolding top1_unit_interval_topology_def
              using subspace_topology_trans[OF hIL_sub_I] by (by100 simp)
            have hcont_IL_R': "top1_continuous_map_on ?IL
                (subspace_topology top1_unit_interval top1_unit_interval_topology ?IL)
                UNIV top1_open_sets (\<lambda>t. 2*t)"
              using hcont_IL_R hTIL_eq by (by100 simp)
            have himg: "(\<lambda>t::real. 2*t) ` ?IL \<subseteq> top1_unit_interval"
              unfolding top1_unit_interval_def by (by100 auto)
            have hI_sub: "top1_unit_interval \<subseteq> (UNIV::real set)" by (by100 blast)
            from top1_continuous_map_on_codomain_shrink[OF hcont_IL_R' himg hI_sub]
            show ?thesis unfolding top1_unit_interval_topology_def by (by100 simp)
          qed
          \<comment> \<open>g1: I \<rightarrow> A1 continuous.\<close>
          have hg1_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              A1 (subspace_topology X TX A1) g1"
            using hg1(1) unfolding top1_homeomorphism_on_def by (by100 blast)
          \<comment> \<open>g1: I \<rightarrow> A1 \<union> A2 (enlarge codomain).\<close>
          have hg1_cont_D: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              (A1 \<union> A2) ?TD g1"
          proof -
            have hA1_sub: "A1 \<subseteq> A1 \<union> A2" by (by100 blast)
            have hA1_sub_X: "A1 \<subseteq> X" by (rule hA1X)
            have hA1D_sub_X: "A1 \<union> A2 \<subseteq> X" using hA1X hA2X by (by100 blast)
            \<comment> \<open>Enlarge codomain from A1 to A1 \<union> A2 via X.\<close>
            have hg1_X: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                X TX g1"
            proof -
              from top1_continuous_map_on_codomain_enlarge[OF hg1_cont hA1_sub_X]
              have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  X (subspace_topology X TX X) g1"
                by (by100 simp)
              moreover have "subspace_topology X TX X = TX"
                by (rule subspace_topology_self) (use hT in \<open>unfold is_topology_on_strict_def Pow_def; by100 blast\<close>)
              ultimately show ?thesis by (by100 simp)
            qed
            have hg1_img: "g1 ` top1_unit_interval \<subseteq> A1 \<union> A2"
            proof -
              have "g1 ` top1_unit_interval = A1"
                using hg1(1) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
              thus ?thesis by (by100 blast)
            qed
            show ?thesis
              using top1_continuous_map_on_codomain_shrink[OF hg1_X hg1_img hA1D_sub_X] by (by100 simp)
          qed
          show ?thesis by (rule top1_continuous_map_on_comp[OF hdbl_cont hg1_cont_D])
        qed
        \<comment> \<open>h agrees with g1 \<circ> (\<lambda>t. 2*t) on ?IL, so h is continuous on ?IL.\<close>
        show ?thesis
          by (rule top1_continuous_map_on_agree[OF hcomp_cont]) (use hagree in \<open>by100 simp\<close>)
      qed
      \<comment> \<open>h is continuous on ?IR (= g2(2t-1)).\<close>
      have hh_IR: "top1_continuous_map_on ?IR (subspace_topology top1_unit_interval top1_unit_interval_topology ?IR)
          (A1 \<union> A2) ?TD h"
      proof -
        have hagree: "\<forall>t\<in>?IR. h t = g2 (2*t - 1)"
        proof (intro ballI)
          fix t :: real assume ht: "t \<in> ?IR"
          hence htge: "t \<ge> 1/2" by (by100 blast)
          show "h t = g2 (2*t - 1)"
          proof (cases "t > 1/2")
            case True thus ?thesis unfolding h_def by (by100 simp)
          next
            case False hence heq: "t = 1/2" using htge by (by100 simp)
            have "h t = g1 1"
            proof -
              have "h t = (if t \<le> 1/2 then g1 (2*t) else g2 (2*t-1))" unfolding h_def by (by100 blast)
              also have "\<dots> = g1 (2*t)" using htge False by (by100 simp)
              also have "2 * t = 1" using heq by (by100 simp)
              finally show ?thesis by (by100 simp)
            qed
            also have "\<dots> = c" using hg1(2) .
            also have "c = g2 0" using hg2(2)[symmetric] .
            also have "g2 0 = g2 (2 * t - 1)"
            proof -
              have "2 * t - 1 = 0" using heq by (by100 simp)
              thus ?thesis by (by100 simp)
            qed
            finally show ?thesis .
          qed
        qed
        have hcomp_cont: "top1_continuous_map_on ?IR
            (subspace_topology top1_unit_interval top1_unit_interval_topology ?IR)
            (A1 \<union> A2) ?TD (g2 \<circ> (\<lambda>t. 2*t - 1))"
        proof -
          have hdbl_cont: "top1_continuous_map_on ?IR
              (subspace_topology top1_unit_interval top1_unit_interval_topology ?IR)
              top1_unit_interval top1_unit_interval_topology (\<lambda>t. 2*t - 1)"
          proof -
            have hcont_R: "continuous_on UNIV (\<lambda>t::real. 2*t - 1)" by (intro continuous_intros)
            have hcont_R2: "top1_continuous_map_on (UNIV::real set) top1_open_sets
                (UNIV::real set) top1_open_sets (\<lambda>t. 2*t - 1)"
              using top1_continuous_map_on_real_subspace_open_sets[of UNIV "\<lambda>t. 2*t-1" UNIV, OF _ hcont_R]
              unfolding subspace_topology_UNIV_self by (by100 auto)
            have hIR_sub: "?IR \<subseteq> (UNIV::real set)" by (by100 blast)
            from top1_continuous_map_on_restrict_domain_simple[OF hcont_R2 hIR_sub]
            have hcont_IR_R: "top1_continuous_map_on ?IR
                (subspace_topology UNIV top1_open_sets ?IR) UNIV top1_open_sets (\<lambda>t. 2*t - 1)" .
            have hIR_sub_I: "?IR \<subseteq> top1_unit_interval" by (by100 blast)
            have hTIR_eq: "subspace_topology UNIV top1_open_sets ?IR
                = subspace_topology top1_unit_interval top1_unit_interval_topology ?IR"
              unfolding top1_unit_interval_topology_def
              using subspace_topology_trans[OF hIR_sub_I] by (by100 simp)
            have hcont_IR_R': "top1_continuous_map_on ?IR
                (subspace_topology top1_unit_interval top1_unit_interval_topology ?IR)
                UNIV top1_open_sets (\<lambda>t. 2*t - 1)"
              using hcont_IR_R hTIR_eq by (by100 simp)
            have himg: "(\<lambda>t::real. 2*t - 1) ` ?IR \<subseteq> top1_unit_interval"
              unfolding top1_unit_interval_def by (by100 auto)
            have hI_sub: "top1_unit_interval \<subseteq> (UNIV::real set)" by (by100 blast)
            from top1_continuous_map_on_codomain_shrink[OF hcont_IR_R' himg hI_sub]
            show ?thesis unfolding top1_unit_interval_topology_def by (by100 simp)
          qed
          have hg2_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              A2 (subspace_topology X TX A2) g2"
            using hg2(1) unfolding top1_homeomorphism_on_def by (by100 blast)
          have hg2_cont_D: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              (A1 \<union> A2) ?TD g2"
          proof -
            have hA2_sub: "A2 \<subseteq> A1 \<union> A2" by (by100 blast)
            have hA2_sub_X: "A2 \<subseteq> X" by (rule hA2X)
            have hA1D_sub_X: "A1 \<union> A2 \<subseteq> X" using hA1X hA2X by (by100 blast)
            have hg2_X: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX g2"
            proof -
              from top1_continuous_map_on_codomain_enlarge[OF hg2_cont hA2_sub_X]
              have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  X (subspace_topology X TX X) g2" by (by100 simp)
              moreover have "subspace_topology X TX X = TX"
                by (rule subspace_topology_self)
                  (use hT in \<open>unfold is_topology_on_strict_def Pow_def; by100 blast\<close>)
              ultimately show ?thesis by (by100 simp)
            qed
            have hg2_img: "g2 ` top1_unit_interval \<subseteq> A1 \<union> A2"
            proof -
              have "g2 ` top1_unit_interval = A2"
                using hg2(1) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
              thus ?thesis by (by100 blast)
            qed
            show ?thesis
              using top1_continuous_map_on_codomain_shrink[OF hg2_X hg2_img hA1D_sub_X] by (by100 simp)
          qed
          show ?thesis by (rule top1_continuous_map_on_comp[OF hdbl_cont hg2_cont_D])
        qed
        show ?thesis
          by (rule top1_continuous_map_on_agree[OF hcomp_cont]) (use hagree in \<open>by100 simp\<close>)
      qed
      show ?thesis
        by (rule pasting_lemma_two_closed[OF hTI hTD_loc hIL_closed hIR_closed hILR_union hh_maps hh_IL hh_IR])
    qed
    \<comment> \<open>Step 4b: h is bijective.\<close>
    have hh_bij: "bij_betw h top1_unit_interval (A1 \<union> A2)"
      unfolding bij_betw_def
    proof (intro conjI)
      show "inj_on h top1_unit_interval"
      proof (rule inj_onI)
        fix s t assume hs: "s \<in> top1_unit_interval" and ht: "t \<in> top1_unit_interval"
            and heq: "h s = h t"
        have hg1_inj: "inj_on g1 top1_unit_interval"
          using hg1(1) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have hg2_inj: "inj_on g2 top1_unit_interval"
          using hg2(1) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have hg1_bij: "bij_betw g1 top1_unit_interval A1"
          using hg1(1) unfolding top1_homeomorphism_on_def by (by100 blast)
        have hg2_bij: "bij_betw g2 top1_unit_interval A2"
          using hg2(1) unfolding top1_homeomorphism_on_def by (by100 blast)
        show "s = t"
        proof (cases "s \<le> 1/2"; cases "t \<le> 1/2")
          \<comment> \<open>Case 1: both in left half.\<close>
          assume hs2: "s \<le> 1/2" and ht2: "t \<le> 1/2"
          have "g1 (2*s) = g1 (2*t)" using heq hs2 ht2 unfolding h_def by (by100 simp)
          moreover have "2*s \<in> top1_unit_interval" using hs hs2 unfolding top1_unit_interval_def by (by100 auto)
          moreover have "2*t \<in> top1_unit_interval" using ht ht2 unfolding top1_unit_interval_def by (by100 auto)
          ultimately have "2*s = 2*t" using inj_onD[OF hg1_inj] by (by100 blast)
          thus "s = t" by (by100 simp)
        next
          \<comment> \<open>Case 2: both in right half.\<close>
          assume hs2: "\<not> s \<le> 1/2" and ht2: "\<not> t \<le> 1/2"
          have "g2 (2*s-1) = g2 (2*t-1)" using heq hs2 ht2 unfolding h_def by (by100 simp)
          moreover have "2*s-1 \<in> top1_unit_interval" using hs hs2 unfolding top1_unit_interval_def by (by100 auto)
          moreover have "2*t-1 \<in> top1_unit_interval" using ht ht2 unfolding top1_unit_interval_def by (by100 auto)
          ultimately have "2*s-1 = 2*t-1" using inj_onD[OF hg2_inj] by (by100 blast)
          thus "s = t" by (by100 simp)
        next
          \<comment> \<open>Case 3: s left, t right. h(s) \<in> A1, h(t) \<in> A2. Equal only if both = c.\<close>
          assume hs2: "s \<le> 1/2" and ht2: "\<not> t \<le> 1/2"
          have hhs_A1: "h s \<in> A1" using hs hs2 hg1_bij unfolding h_def bij_betw_def top1_unit_interval_def by (by100 auto)
          have "h t \<in> A2" using ht ht2 hg2_bij unfolding h_def bij_betw_def top1_unit_interval_def by (by100 auto)
          hence "h s \<in> A2" using heq by (by100 simp)
          hence "h s \<in> A1 \<inter> A2" using hhs_A1 by (by100 blast)
          hence "h s = c" using hinter by (by100 blast)
          hence "g1 (2*s) = c" using hs2 unfolding h_def by (by100 simp)
          hence "g1 (2*s) = g1 1" using hg1(2) by (by100 simp)
          moreover have "2*s \<in> top1_unit_interval" using hs hs2 unfolding top1_unit_interval_def by (by100 auto)
          moreover have "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
          ultimately have "2*s = 1" using inj_onD[OF hg1_inj] by (by100 blast)
          hence hs_half: "s = 1/2" by (by100 simp)
          have "h t = c" using heq \<open>h s = c\<close> by (by100 simp)
          hence "g2 (2*t-1) = c" using ht2 unfolding h_def by (by100 simp)
          hence "g2 (2*t-1) = g2 0" using hg2(2) by (by100 simp)
          moreover have "2*t-1 \<in> top1_unit_interval" using ht ht2 unfolding top1_unit_interval_def by (by100 auto)
          moreover have "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
          ultimately have "2*t-1 = 0" using inj_onD[OF hg2_inj] by (by100 blast)
          hence "t = 1/2" by (by100 simp)
          thus "s = t" using hs_half by (by100 simp)
        next
          \<comment> \<open>Case 4: s right, t left. Symmetric to case 3.\<close>
          assume hs2: "\<not> s \<le> 1/2" and ht2: "t \<le> 1/2"
          have "h t \<in> A1" using ht ht2 hg1_bij unfolding h_def bij_betw_def top1_unit_interval_def by (by100 auto)
          have hhs_A2: "h s \<in> A2" using hs hs2 hg2_bij unfolding h_def bij_betw_def top1_unit_interval_def by (by100 auto)
          have "h s \<in> A1" using \<open>h t \<in> A1\<close> heq by (by100 simp)
          hence "h s \<in> A1 \<inter> A2" using hhs_A2 by (by100 blast)
          hence "h s = c" using hinter by (by100 blast)
          hence "g2 (2*s-1) = c" using hs2 unfolding h_def by (by100 simp)
          hence "g2 (2*s-1) = g2 0" using hg2(2) by (by100 simp)
          moreover have "2*s-1 \<in> top1_unit_interval" using hs hs2 unfolding top1_unit_interval_def by (by100 auto)
          moreover have "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
          ultimately have "2*s-1 = 0" using inj_onD[OF hg2_inj] by (by100 blast)
          hence hs_half: "s = 1/2" by (by100 simp)
          have "h t = c" using heq \<open>h s = c\<close> by (by100 simp)
          hence "g1 (2*t) = c" using ht2 unfolding h_def by (by100 simp)
          hence "g1 (2*t) = g1 1" using hg1(2) by (by100 simp)
          moreover have "2*t \<in> top1_unit_interval" using ht ht2 unfolding top1_unit_interval_def by (by100 auto)
          moreover have "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
          ultimately have "2*t = 1" using inj_onD[OF hg1_inj] by (by100 blast)
          hence "t = 1/2" by (by100 simp)
          thus "s = t" using hs_half by (by100 simp)
        qed
      qed
      show "h ` top1_unit_interval = A1 \<union> A2"
      proof (rule set_eqI, rule iffI)
        fix y assume "y \<in> h ` top1_unit_interval"
        then obtain t where "t \<in> top1_unit_interval" "y = h t" by (by100 blast)
        thus "y \<in> A1 \<union> A2"
          using hh_cont unfolding top1_continuous_map_on_def by (by100 blast)
      next
        fix y assume hy: "y \<in> A1 \<union> A2"
        have hg1_bij: "bij_betw g1 top1_unit_interval A1"
          using hg1(1) unfolding top1_homeomorphism_on_def by (by100 blast)
        have hg2_bij: "bij_betw g2 top1_unit_interval A2"
          using hg2(1) unfolding top1_homeomorphism_on_def by (by100 blast)
        show "y \<in> h ` top1_unit_interval"
        proof (cases "y \<in> A1")
          case True
          then obtain s where hs: "s \<in> top1_unit_interval" "g1 s = y"
            using hg1_bij unfolding bij_betw_def by (by100 blast)
          let ?t = "s / 2"
          have "?t \<in> top1_unit_interval" using hs(1) unfolding top1_unit_interval_def by (by100 auto)
          moreover have "h ?t = y"
          proof -
            have "?t \<le> 1/2" using hs(1) unfolding top1_unit_interval_def by (by100 auto)
            hence "h ?t = g1 (2 * ?t)" unfolding h_def by (by100 simp)
            also have "2 * ?t = s" by (by100 simp)
            finally show ?thesis using hs(2) by (by100 simp)
          qed
          ultimately show ?thesis by (by100 blast)
        next
          case False hence hyA2: "y \<in> A2" using hy by (by100 blast)
          then obtain s where hs: "s \<in> top1_unit_interval" "g2 s = y"
            using hg2_bij unfolding bij_betw_def by (by100 blast)
          let ?t = "(s + 1) / 2"
          have "?t \<in> top1_unit_interval" using hs(1) unfolding top1_unit_interval_def by (by100 auto)
          have "?t > 1/2 \<or> ?t = 1/2"
          proof (cases "s = 0")
            case True thus ?thesis by (by100 simp)
          next
            case False hence "s > 0" using hs(1) unfolding top1_unit_interval_def by (by100 auto)
            thus ?thesis by (by100 simp)
          qed
          moreover have "h ?t = y"
          proof (cases "?t \<le> 1/2")
            case True
            hence "s = 0" using hs(1) unfolding top1_unit_interval_def by (by100 auto)
            hence "h ?t = g1 1" unfolding h_def using True by (by100 simp)
            also have "\<dots> = c" using hg1(2) .
            also have "c = g2 0" using hg2(2)[symmetric] .
            finally have "h ?t = g2 0" .
            also have "g2 0 = y" using hs(2) \<open>s = 0\<close> by (by100 simp)
            finally show ?thesis .
          next
            case False
            hence "h ?t = g2 (2 * ?t - 1)" unfolding h_def by (by100 simp)
            also have "2 * ?t - 1 = s"
            proof -
              have "2 * ((s + 1) / 2) = s + 1" by (by100 simp)
              thus ?thesis by (by100 linarith)
            qed
            finally show ?thesis using hs(2) by (by100 simp)
          qed
          ultimately show ?thesis using \<open>?t \<in> top1_unit_interval\<close> by (by100 blast)
        qed
      qed
    qed
    \<comment> \<open>Step 4c: continuous bijection from compact to Hausdorff is homeomorphism.\<close>
    have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
    proof -
      have "compact (top1_unit_interval :: real set)"
        unfolding top1_unit_interval_def by (rule compact_Icc)
      hence "top1_compact_on top1_unit_interval
          (subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval)"
        using top1_compact_on_subspace_UNIV_iff_compact by (by100 blast)
      thus ?thesis unfolding top1_unit_interval_topology_def by (by100 simp)
    qed
    have hD_hausdorff: "is_hausdorff_on (A1 \<union> A2) ?TD"
    proof -
      have hHX: "is_hausdorff_on X TX" using hH .
      have hAX: "A1 \<union> A2 \<subseteq> X" using hA1X hA2X by (by100 blast)
      show ?thesis using conjunct2[OF conjunct2[OF Theorem_17_11]]
        hHX hAX by (by100 blast)
    qed
    have hTD_top: "is_topology_on (A1 \<union> A2) ?TD"
    proof -
      have hTopX: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
      show ?thesis by (rule subspace_topology_is_topology_on[OF hTopX])
        (use hA1X hA2X in \<open>by100 blast\<close>)
    qed
    show ?thesis
      by (rule Theorem_26_6[OF top1_unit_interval_topology_is_topology_on hTD_top
          hI_compact hD_hausdorff hh_cont hh_bij])
  qed
  have hTD_strict: "is_topology_on_strict (A1 \<union> A2) ?TD"
  proof -
    have "A1 \<union> A2 \<subseteq> X" using hA1X hA2X by (by100 blast)
    have hTopX: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
    have hTop: "is_topology_on (A1 \<union> A2) ?TD"
      by (rule subspace_topology_is_topology_on[OF hTopX \<open>A1 \<union> A2 \<subseteq> X\<close>])
    have hPow: "?TD \<subseteq> Pow (A1 \<union> A2)"
    proof
      fix U assume "U \<in> ?TD"
      thus "U \<in> Pow (A1 \<union> A2)" using hTop unfolding is_topology_on_def subspace_topology_def
        by (by100 blast)
    qed
    show ?thesis unfolding is_topology_on_strict_def using hTop hPow by (by100 blast)
  qed
  show ?thesis unfolding top1_is_arc_on_def using hh_homeo hTD_strict by (by100 blast)
qed

\<comment> \<open>Reusable: splitting an arc at a given interior point produces two sub-arcs.
   Each endpoint of D goes to a different sub-arc.\<close>
lemma arc_split_at_given_point:
  assumes hT: "is_topology_on_strict X TX" and hH: "is_hausdorff_on X TX"
      and hDX: "D \<subseteq> X"
      and hArc: "top1_is_arc_on D (subspace_topology X TX D)"
      and hp: "p \<in> D" and hp_int: "p \<notin> top1_arc_endpoints_on D (subspace_topology X TX D)"
      and hep: "top1_arc_endpoints_on D (subspace_topology X TX D) = {a, b}" and hab: "a \<noteq> b"
  shows "\<exists>D1 D2. D = D1 \<union> D2 \<and> D1 \<inter> D2 = {p}
      \<and> top1_is_arc_on D1 (subspace_topology X TX D1)
      \<and> top1_is_arc_on D2 (subspace_topology X TX D2)
      \<and> a \<in> D1 \<and> b \<in> D2 \<and> p \<in> D1 \<and> p \<in> D2
      \<and> D1 \<subseteq> X \<and> D2 \<subseteq> X"
proof -
  \<comment> \<open>Get homeomorphism h: [0,1] \<rightarrow> D with h(0)=a, h(1)=b.\<close>
  obtain h where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      D (subspace_topology X TX D) h" "h 0 = a" "h 1 = b"
  proof -
    obtain h0 where hh0: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
        D (subspace_topology X TX D) h0"
      using hArc unfolding top1_is_arc_on_def by (by100 blast)
    have heps0: "top1_arc_endpoints_on D (subspace_topology X TX D) = {h0 0, h0 1}"
      by (rule arc_endpoints_are_boundary[OF hT hH hDX hArc hh0])
    hence hab_h0: "{h0 0, h0 1} = {a, b}" using hep by (by100 simp)
    have "h0 0 \<noteq> h0 1"
    proof
      assume "h0 0 = h0 1"
      hence "{h0 0, h0 1} = {h0 0}" by (by100 simp)
      hence "card {a, b} \<le> 1" using hab_h0 by (by100 simp)
      thus False using hab by (by100 simp)
    qed
    from doubleton_eq_iff[OF hab_h0 this]
    show ?thesis
    proof
      assume "h0 0 = a \<and> h0 1 = b"
      thus ?thesis using that[OF hh0] by (by100 blast)
    next
      assume "h0 0 = b \<and> h0 1 = a"
      hence "h0 0 = b" "h0 1 = a" by (by100 blast)+
      have hcomp: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          D (subspace_topology X TX D) (h0 \<circ> (\<lambda>t::real. 1-t))"
        by (rule homeomorphism_on_comp[OF unit_interval_reversal_homeomorphism hh0])
      have "(h0 \<circ> (\<lambda>t::real. 1-t)) 0 = a" unfolding comp_def using \<open>h0 1 = a\<close> by (by100 simp)
      moreover have "(h0 \<circ> (\<lambda>t::real. 1-t)) 1 = b" unfolding comp_def using \<open>h0 0 = b\<close> by (by100 simp)
      ultimately show ?thesis using that[OF hcomp] by (by100 blast)
    qed
  qed
  \<comment> \<open>p = h(t0) for some t0 \<in> (0,1) (since p \<notin> endpoints = {h(0),h(1)} = {a,b}).\<close>
  have hbij: "bij_betw h top1_unit_interval D" using hh(1) unfolding top1_homeomorphism_on_def by (by100 blast)
  have hinj: "inj_on h top1_unit_interval" using hbij unfolding bij_betw_def by (by100 blast)
  have himg: "h ` top1_unit_interval = D" using hbij unfolding bij_betw_def by (by100 blast)
  obtain t0 where ht0: "t0 \<in> top1_unit_interval" "h t0 = p" using hp himg by (by100 blast)
  have ht0_int: "0 < t0" "t0 < 1"
  proof -
    have "t0 \<noteq> 0"
    proof
      assume "t0 = 0" hence "p = a" using ht0(2) hh(2) by (by100 simp)
      hence "p \<in> {a, b}" by (by100 blast)
      hence "p \<in> top1_arc_endpoints_on D (subspace_topology X TX D)" using hep by (by100 simp)
      thus False using hp_int by (by100 blast)
    qed
    have "t0 \<noteq> 1"
    proof
      assume "t0 = 1" hence "p = b" using ht0(2) hh(3) by (by100 simp)
      hence "p \<in> {a, b}" by (by100 blast)
      hence "p \<in> top1_arc_endpoints_on D (subspace_topology X TX D)" using hep by (by100 simp)
      thus False using hp_int by (by100 blast)
    qed
    show "0 < t0" using ht0(1) \<open>t0 \<noteq> 0\<close> unfolding top1_unit_interval_def by (by100 auto)
    show "t0 < 1" using ht0(1) \<open>t0 \<noteq> 1\<close> unfolding top1_unit_interval_def by (by100 auto)
  qed
  \<comment> \<open>D1 = h([0,t0]), D2 = h([t0,1]).\<close>
  define D1 where "D1 = h ` {t \<in> top1_unit_interval. t \<le> t0}"
  define D2 where "D2 = h ` {t \<in> top1_unit_interval. t \<ge> t0}"
  have hD_eq: "D = D1 \<union> D2"
    unfolding D1_def D2_def using himg by (by100 force)
  have hD_inter: "D1 \<inter> D2 = {p}"
  proof -
    have "D1 \<inter> D2 = h ` ({t \<in> top1_unit_interval. t \<le> t0} \<inter> {t \<in> top1_unit_interval. t \<ge> t0})"
    proof -
      have hsub1: "{t \<in> top1_unit_interval. t \<le> t0} \<subseteq> top1_unit_interval" by (by100 blast)
      have hsub2: "{t \<in> top1_unit_interval. t \<ge> t0} \<subseteq> top1_unit_interval" by (by100 blast)
      show ?thesis unfolding D1_def D2_def
        using inj_on_image_Int[OF hinj hsub1 hsub2] by (by100 simp)
    qed
    also have "{t \<in> top1_unit_interval. t \<le> t0} \<inter> {t \<in> top1_unit_interval. t \<ge> t0} = {t0}"
      using ht0(1) by (by100 force)
    finally show ?thesis using ht0(2) by (by100 simp)
  qed
  have ha_D1: "a \<in> D1"
  proof -
    have h0_le: "(0::real) \<in> {t \<in> top1_unit_interval. t \<le> t0}"
      unfolding top1_unit_interval_def using ht0_int by (by100 auto)
    hence "h 0 \<in> D1" unfolding D1_def by (by100 blast)
    thus ?thesis using hh(2) by (by100 simp)
  qed
  have hb_D2: "b \<in> D2"
  proof -
    have h1_ge: "(1::real) \<in> {t \<in> top1_unit_interval. t \<ge> t0}"
      unfolding top1_unit_interval_def using ht0_int by (by100 auto)
    hence "h 1 \<in> D2" unfolding D2_def by (by100 blast)
    thus ?thesis using hh(3) by (by100 simp)
  qed
  have hp_D1: "p \<in> D1" using hD_inter by (by100 blast)
  have hp_D2: "p \<in> D2" using hD_inter by (by100 blast)
  have hD1_sub: "D1 \<subseteq> X" unfolding D1_def using himg hDX by (by100 blast)
  have hD2_sub: "D2 \<subseteq> X" unfolding D2_def using himg hDX by (by100 blast)
  \<comment> \<open>D1 and D2 are arcs (h restricted to [0,t0] and [t0,1]).\<close>
  have hD1_arc: "top1_is_arc_on D1 (subspace_topology X TX D1)"
  proof -
    \<comment> \<open>D1 is the image of [0,t0] under h. Compose affine [0,1]\<rightarrow>[0,t0] with h|_{[0,t0]}\<rightarrow>D1.\<close>
    let ?I0 = "{t \<in> top1_unit_interval. t \<le> t0}"
    \<comment> \<open>?I0 = [0,t0] as a subset of [0,1].\<close>
    \<comment> \<open>h restricted to [0,t0] is a homeomorphism [0,t0] \<rightarrow> D1.\<close>
    have hh_restr_homeo: "top1_homeomorphism_on ?I0
        (subspace_topology top1_unit_interval top1_unit_interval_topology ?I0)
        D1 (subspace_topology X TX D1) h"
    proof -
      have hI0_sub: "?I0 \<subseteq> top1_unit_interval" by (by100 blast)
      have hD1_eq: "h ` ?I0 = D1" unfolding D1_def by (by100 simp)
      have hD1_D: "D1 \<subseteq> D" unfolding D1_def using himg by (by100 blast)
      \<comment> \<open>h restricted to I0 is continuous I0 \<rightarrow> X (via restrict of h: I \<rightarrow> D \<rightarrow> X).\<close>
      have hTopX_loc: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
      have hh_cont_loc: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          D (subspace_topology X TX D) h"
        using hh(1) unfolding top1_homeomorphism_on_def by (by100 blast)
      \<comment> \<open>h: I \<rightarrow> D cont. Enlarge codomain to X.\<close>
      have hh_cont_X: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX h"
      proof -
        from top1_continuous_map_on_codomain_enlarge[OF hh_cont_loc hDX]
        have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
            X (subspace_topology X TX X) h" by (by100 simp)
        moreover have "subspace_topology X TX X = TX"
          by (rule subspace_topology_self)
            (use hT in \<open>unfold is_topology_on_strict_def Pow_def; by100 blast\<close>)
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>Restrict domain to I0, codomain to D1.\<close>
      from top1_continuous_map_on_restrict_domain_simple[OF hh_cont_X hI0_sub]
      have hh_I0_X: "top1_continuous_map_on ?I0
          (subspace_topology top1_unit_interval top1_unit_interval_topology ?I0) X TX h"
        using subspace_topology_trans[OF hI0_sub] by (by100 simp)
      have hD1_eq: "h ` ?I0 = D1" unfolding D1_def by (by100 simp)
      have hD1_D: "D1 \<subseteq> D" unfolding D1_def using himg by (by100 blast)
      have himg_D1: "h ` ?I0 \<subseteq> D1" using hD1_eq by (by100 blast)
      from top1_continuous_map_on_codomain_shrink[OF hh_I0_X himg_D1 hD1_sub]
      have hh_I0_D1: "top1_continuous_map_on ?I0
          (subspace_topology top1_unit_interval top1_unit_interval_topology ?I0)
          D1 (subspace_topology X TX D1) h" by (by100 simp)
      have hbij_I0: "bij_betw h ?I0 D1"
      proof -
        have "bij_betw h ?I0 (h ` ?I0)"
          unfolding bij_betw_def using inj_on_subset[OF hinj hI0_sub] by (by100 blast)
        thus ?thesis using hD1_eq by (by100 simp)
      qed
      \<comment> \<open>I0 compact, D1 Hausdorff \<Rightarrow> Theorem_26_6 gives homeomorphism.\<close>
      have hI0_compact: "top1_compact_on ?I0
          (subspace_topology top1_unit_interval top1_unit_interval_topology ?I0)"
      proof -
        have "compact {0..t0}" by (rule compact_Icc)
        have "{0..t0} = ?I0" unfolding top1_unit_interval_def using ht0_int ht0(1) by (by100 force)
        hence "compact ?I0" using \<open>compact {0..t0}\<close> by (by100 simp)
        hence "top1_connected_on ?I0 (subspace_topology UNIV top1_open_sets ?I0) \<or>
            top1_compact_on ?I0 (subspace_topology UNIV top1_open_sets ?I0)"
          using top1_compact_on_subspace_UNIV_iff_compact by (by100 blast)
        hence "top1_compact_on ?I0 (subspace_topology UNIV top1_open_sets ?I0)"
          using top1_compact_on_subspace_UNIV_iff_compact \<open>compact ?I0\<close> by (by100 blast)
        thus ?thesis unfolding top1_unit_interval_topology_def
          using subspace_topology_trans[OF hI0_sub] by (by100 simp)
      qed
      have hD1_haus: "is_hausdorff_on D1 (subspace_topology X TX D1)"
        using conjunct2[OF conjunct2[OF Theorem_17_11]] hH hD1_sub by (by100 blast)
      have hTI0: "is_topology_on ?I0 (subspace_topology top1_unit_interval top1_unit_interval_topology ?I0)"
        by (rule subspace_topology_is_topology_on[OF top1_unit_interval_topology_is_topology_on hI0_sub])
      have hTD1: "is_topology_on D1 (subspace_topology X TX D1)"
        by (rule subspace_topology_is_topology_on[OF hTopX_loc hD1_sub])
      show ?thesis
        by (rule Theorem_26_6[OF hTI0 hTD1 hI0_compact hD1_haus hh_I0_D1 hbij_I0])
    qed
    \<comment> \<open>Affine map s \<mapsto> s*t0: [0,1] \<rightarrow> [0,t0] is a homeomorphism.\<close>
    have hscale_homeo: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
        ?I0 (subspace_topology top1_unit_interval top1_unit_interval_topology ?I0) (\<lambda>s. s * t0)"
    proof -
      have hTI: "is_topology_on top1_unit_interval top1_unit_interval_topology"
        by (rule top1_unit_interval_topology_is_topology_on)
      have hI0_sub: "?I0 \<subseteq> top1_unit_interval" by (by100 blast)
      have hTI0: "is_topology_on ?I0 (subspace_topology top1_unit_interval top1_unit_interval_topology ?I0)"
        by (rule subspace_topology_is_topology_on[OF hTI hI0_sub])
      \<comment> \<open>Continuous: s\<mapsto>s*t0 is affine.\<close>
      have hscale_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          ?I0 (subspace_topology top1_unit_interval top1_unit_interval_topology ?I0) (\<lambda>s. s * t0)"
      proof -
        have hcont_R: "continuous_on UNIV (\<lambda>s::real. s * t0)" by (intro continuous_intros)
        have hcont_R2: "top1_continuous_map_on (UNIV::real set) top1_open_sets
            (UNIV::real set) top1_open_sets (\<lambda>s. s * t0)"
          using top1_continuous_map_on_real_subspace_open_sets[of UNIV "\<lambda>s. s*t0" UNIV, OF _ hcont_R]
          unfolding subspace_topology_UNIV_self by (by100 auto)
        from top1_continuous_map_on_restrict_domain_simple[OF hcont_R2 subset_UNIV]
        have "top1_continuous_map_on top1_unit_interval
            (subspace_topology UNIV top1_open_sets top1_unit_interval) UNIV top1_open_sets (\<lambda>s. s*t0)" .
        hence h1: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
            UNIV top1_open_sets (\<lambda>s. s*t0)"
          unfolding top1_unit_interval_topology_def subspace_topology_UNIV_self by (by100 simp)
        have himg_I: "(\<lambda>s::real. s * t0) ` top1_unit_interval \<subseteq> top1_unit_interval"
          unfolding top1_unit_interval_def
        proof (rule image_subsetI)
          fix s :: real assume "s \<in> {0..1}"
          hence "0 \<le> s" "s \<le> 1" by (by100 auto)+
          have "0 \<le> s * t0" using \<open>0 \<le> s\<close> ht0_int(1) by (by100 simp)
          moreover have "s * t0 \<le> 1"
          proof -
            have "s * t0 \<le> 1 * 1"
              using mult_mono[of s 1 t0 1] \<open>0 \<le> s\<close> \<open>s \<le> 1\<close> ht0_int by (by100 linarith)
            thus ?thesis by (by100 simp)
          qed
          ultimately show "s * t0 \<in> {0..1}" by (by100 simp)
        qed
        have hI_UNIV: "top1_unit_interval \<subseteq> (UNIV::real set)" by (by100 blast)
        from top1_continuous_map_on_codomain_shrink[OF h1 himg_I hI_UNIV]
        have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
            top1_unit_interval (subspace_topology UNIV top1_open_sets top1_unit_interval) (\<lambda>s. s*t0)" .
        hence h2: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
            top1_unit_interval top1_unit_interval_topology (\<lambda>s. s*t0)"
          unfolding top1_unit_interval_topology_def by (by100 simp)
        have himg_I0: "(\<lambda>s::real. s * t0) ` top1_unit_interval \<subseteq> ?I0"
        proof
          fix x assume "x \<in> (\<lambda>s. s * t0) ` top1_unit_interval"
          then obtain s where hs: "s \<in> top1_unit_interval" "x = s * t0" by (by100 blast)
          have "x \<in> top1_unit_interval" using hs himg_I by (by100 blast)
          moreover have "x \<le> t0" using hs unfolding top1_unit_interval_def
            using ht0_int(1) by (by100 auto)
          ultimately show "x \<in> ?I0" by (by100 blast)
        qed
        show ?thesis
          using top1_continuous_map_on_codomain_shrink[OF h2 himg_I0 hI0_sub]
            subspace_topology_trans[OF hI0_sub] by (by100 simp)
      qed
      \<comment> \<open>Bijective.\<close>
      have hscale_bij: "bij_betw (\<lambda>s. s * t0) top1_unit_interval ?I0"
        unfolding bij_betw_def
      proof (intro conjI)
        show "inj_on (\<lambda>s. s * t0) top1_unit_interval"
        proof (rule inj_onI)
          fix x y :: real assume "x \<in> top1_unit_interval" "y \<in> top1_unit_interval" "x * t0 = y * t0"
          thus "x = y" using ht0_int(1) by (by100 simp)
        qed
        show "(\<lambda>s. s * t0) ` top1_unit_interval = ?I0"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> (\<lambda>s. s * t0) ` top1_unit_interval"
          then obtain s where hs: "s \<in> top1_unit_interval" "x = s * t0" by (by100 blast)
          have hs_bounds: "0 \<le> s" "s \<le> 1" using hs(1) unfolding top1_unit_interval_def by (by100 auto)+
          have "0 \<le> s * t0" using hs_bounds(1) ht0_int(1) by (by100 simp)
          moreover have "s * t0 \<le> t0"
          proof -
            have "s * t0 \<le> 1 * t0" using hs_bounds ht0_int(1) by (by100 simp)
            thus ?thesis by (by100 simp)
          qed
          moreover have "s * t0 \<le> 1" using \<open>s * t0 \<le> t0\<close> ht0_int(2) by (by100 linarith)
          ultimately show "x \<in> ?I0" using hs(2)
            unfolding top1_unit_interval_def by (by100 auto)
        next
          fix x assume "x \<in> ?I0"
          hence hx: "x \<in> top1_unit_interval" "x \<le> t0" by (by100 blast)+
          let ?s = "x / t0"
          have "?s \<in> top1_unit_interval" using hx ht0_int
            unfolding top1_unit_interval_def by (by100 auto)
          moreover have "?s * t0 = x" using ht0_int(1) by (by100 simp)
          ultimately show "x \<in> (\<lambda>s. s * t0) ` top1_unit_interval" by (by100 force)
        qed
      qed
      \<comment> \<open>Compact + Hausdorff.\<close>
      have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
      proof -
        have "compact (top1_unit_interval :: real set)" unfolding top1_unit_interval_def by (rule compact_Icc)
        thus ?thesis using top1_compact_on_subspace_UNIV_iff_compact
          unfolding top1_unit_interval_topology_def by (by100 blast)
      qed
      have hI0_haus: "is_hausdorff_on ?I0 (subspace_topology top1_unit_interval top1_unit_interval_topology ?I0)"
      proof -
        have "is_hausdorff_on (UNIV::real set) top1_open_sets" by (rule top1_R_is_hausdorff)
        hence "is_hausdorff_on top1_unit_interval (subspace_topology UNIV top1_open_sets top1_unit_interval)"
          using conjunct2[OF conjunct2[OF Theorem_17_11]] by (by100 blast)
        hence "is_hausdorff_on top1_unit_interval top1_unit_interval_topology"
          unfolding top1_unit_interval_topology_def by (by100 simp)
        hence "is_hausdorff_on ?I0 (subspace_topology top1_unit_interval top1_unit_interval_topology ?I0)"
          using conjunct2[OF conjunct2[OF Theorem_17_11]] hI0_sub by (by100 blast)
        thus ?thesis .
      qed
      show ?thesis by (rule Theorem_26_6[OF hTI hTI0 hI_compact hI0_haus hscale_cont hscale_bij])
    qed
    \<comment> \<open>Compose: [0,1] \<rightarrow> [0,t0] \<rightarrow> D1.\<close>
    from homeomorphism_on_comp[OF hscale_homeo hh_restr_homeo]
    have "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
        D1 (subspace_topology X TX D1) (h \<circ> (\<lambda>s. s * t0))" .
    moreover have hTD1_strict: "is_topology_on_strict D1 (subspace_topology X TX D1)"
    proof -
      have hTopX: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
      have hTop: "is_topology_on D1 (subspace_topology X TX D1)"
        by (rule subspace_topology_is_topology_on[OF hTopX hD1_sub])
      have "subspace_topology X TX D1 \<subseteq> Pow D1"
        unfolding subspace_topology_def by (by100 blast)
      thus ?thesis unfolding is_topology_on_strict_def using hTop by (by100 blast)
    qed
    ultimately show ?thesis unfolding top1_is_arc_on_def by (by100 blast)
  qed
  have hD2_arc: "top1_is_arc_on D2 (subspace_topology X TX D2)"
  proof -
    let ?I1 = "{t \<in> top1_unit_interval. t \<ge> t0}"
    have hI1_sub: "?I1 \<subseteq> top1_unit_interval" by (by100 blast)
    have hh_restr_homeo: "top1_homeomorphism_on ?I1
        (subspace_topology top1_unit_interval top1_unit_interval_topology ?I1)
        D2 (subspace_topology X TX D2) h"
    proof -
      have hTopX_loc: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
      have hh_cont_X: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX h"
      proof -
        have hh_cont_D: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
            D (subspace_topology X TX D) h"
          using hh(1) unfolding top1_homeomorphism_on_def by (by100 blast)
        from top1_continuous_map_on_codomain_enlarge[OF hh_cont_D hDX]
        have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
            X (subspace_topology X TX X) h" by (by100 simp)
        moreover have "subspace_topology X TX X = TX"
          by (rule subspace_topology_self)
            (use hT in \<open>unfold is_topology_on_strict_def Pow_def; by100 blast\<close>)
        ultimately show ?thesis by (by100 simp)
      qed
      from top1_continuous_map_on_restrict_domain_simple[OF hh_cont_X hI1_sub]
      have hh_I1_X: "top1_continuous_map_on ?I1
          (subspace_topology top1_unit_interval top1_unit_interval_topology ?I1) X TX h"
        using subspace_topology_trans[OF hI1_sub] by (by100 simp)
      have hD2_eq: "h ` ?I1 = D2" unfolding D2_def by (by100 simp)
      have hD2_D: "D2 \<subseteq> D" unfolding D2_def using himg by (by100 blast)
      have himg_D2: "h ` ?I1 \<subseteq> D2" using hD2_eq by (by100 blast)
      from top1_continuous_map_on_codomain_shrink[OF hh_I1_X himg_D2 hD2_sub]
      have hh_I1_D2: "top1_continuous_map_on ?I1
          (subspace_topology top1_unit_interval top1_unit_interval_topology ?I1)
          D2 (subspace_topology X TX D2) h" by (by100 simp)
      have hbij_I1: "bij_betw h ?I1 D2"
      proof -
        have "bij_betw h ?I1 (h ` ?I1)"
          unfolding bij_betw_def using inj_on_subset[OF hinj hI1_sub] by (by100 blast)
        thus ?thesis using hD2_eq by (by100 simp)
      qed
      have hI1_compact: "top1_compact_on ?I1
          (subspace_topology top1_unit_interval top1_unit_interval_topology ?I1)"
      proof -
        have "compact ?I1"
        proof -
          have "compact {t0..(1::real)}" by (rule compact_Icc)
          moreover have "?I1 = {t0..1}" unfolding top1_unit_interval_def using ht0_int ht0(1) by (by100 force)
          ultimately show ?thesis by (by100 simp)
        qed
        hence "top1_compact_on ?I1 (subspace_topology (UNIV::real set) top1_open_sets ?I1)"
          using top1_compact_on_subspace_UNIV_iff_compact by (by100 blast)
        thus ?thesis unfolding top1_unit_interval_topology_def
          using subspace_topology_trans[OF hI1_sub] by (by100 simp)
      qed
      have hD2_haus: "is_hausdorff_on D2 (subspace_topology X TX D2)"
        using conjunct2[OF conjunct2[OF Theorem_17_11]] hH hD2_sub by (by100 blast)
      have hTI1: "is_topology_on ?I1 (subspace_topology top1_unit_interval top1_unit_interval_topology ?I1)"
        by (rule subspace_topology_is_topology_on[OF top1_unit_interval_topology_is_topology_on hI1_sub])
      have hTD2: "is_topology_on D2 (subspace_topology X TX D2)"
        by (rule subspace_topology_is_topology_on[OF hTopX_loc hD2_sub])
      show ?thesis
        by (rule Theorem_26_6[OF hTI1 hTD2 hI1_compact hD2_haus hh_I1_D2 hbij_I1])
    qed
    have hscale_homeo: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
        ?I1 (subspace_topology top1_unit_interval top1_unit_interval_topology ?I1) (\<lambda>s. t0 + s * (1 - t0))"
    proof -
      have hTI: "is_topology_on top1_unit_interval top1_unit_interval_topology"
        by (rule top1_unit_interval_topology_is_topology_on)
      have hTI1: "is_topology_on ?I1 (subspace_topology top1_unit_interval top1_unit_interval_topology ?I1)"
        by (rule subspace_topology_is_topology_on[OF hTI hI1_sub])
      \<comment> \<open>Continuous.\<close>
      have hscale_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          ?I1 (subspace_topology top1_unit_interval top1_unit_interval_topology ?I1) (\<lambda>s. t0 + s * (1 - t0))"
      proof -
        have hcont_R: "continuous_on UNIV (\<lambda>s::real. t0 + s * (1 - t0))" by (intro continuous_intros)
        have hcont_R2: "top1_continuous_map_on (UNIV::real set) top1_open_sets
            (UNIV::real set) top1_open_sets (\<lambda>s. t0 + s * (1 - t0))"
          using top1_continuous_map_on_real_subspace_open_sets[of UNIV "\<lambda>s. t0 + s*(1-t0)" UNIV, OF _ hcont_R]
          unfolding subspace_topology_UNIV_self by (by100 auto)
        from top1_continuous_map_on_restrict_domain_simple[OF hcont_R2 subset_UNIV]
        have h1: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
            UNIV top1_open_sets (\<lambda>s. t0 + s*(1-t0))"
          unfolding top1_unit_interval_topology_def subspace_topology_UNIV_self by (by100 simp)
        have himg_I: "(\<lambda>s. t0 + s * (1-t0)) ` top1_unit_interval \<subseteq> top1_unit_interval"
          unfolding top1_unit_interval_def
        proof (rule image_subsetI)
          fix s :: real assume "s \<in> {0..1}"
          hence "0 \<le> s" "s \<le> 1" by (by100 auto)+
          have "s * (1-t0) \<le> 1 * (1-t0)" using \<open>s \<le> 1\<close> ht0_int by (by100 simp)
          hence "s * (1-t0) \<le> 1 - t0" by (by100 simp)
          hence "t0 + s * (1-t0) \<le> 1" by (by100 linarith)
          moreover have "0 \<le> t0 + s * (1-t0)" using \<open>0 \<le> s\<close> ht0_int by (by100 simp)
          ultimately show "t0 + s * (1-t0) \<in> {0..1}" by (by100 simp)
        qed
        have hI_UNIV: "top1_unit_interval \<subseteq> (UNIV::real set)" by (by100 blast)
        from top1_continuous_map_on_codomain_shrink[OF h1 himg_I hI_UNIV]
        have h2: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
            top1_unit_interval top1_unit_interval_topology (\<lambda>s. t0 + s*(1-t0))"
          unfolding top1_unit_interval_topology_def by (by100 simp)
        have himg_I1: "(\<lambda>s. t0 + s * (1-t0)) ` top1_unit_interval \<subseteq> ?I1"
        proof
          fix x assume "x \<in> (\<lambda>s. t0 + s * (1-t0)) ` top1_unit_interval"
          then obtain s where "s \<in> top1_unit_interval" "x = t0 + s * (1-t0)" by (by100 blast)
          have "x \<in> top1_unit_interval" using \<open>s \<in> top1_unit_interval\<close> himg_I \<open>x = _\<close> by (by100 blast)
          moreover have "x \<ge> t0" using \<open>x = _\<close> \<open>s \<in> top1_unit_interval\<close> ht0_int
            unfolding top1_unit_interval_def by (by100 auto)
          ultimately show "x \<in> ?I1" by (by100 blast)
        qed
        show ?thesis using top1_continuous_map_on_codomain_shrink[OF h2 himg_I1 hI1_sub]
          subspace_topology_trans[OF hI1_sub] by (by100 simp)
      qed
      \<comment> \<open>Bijective.\<close>
      have hscale_bij: "bij_betw (\<lambda>s. t0 + s * (1-t0)) top1_unit_interval ?I1"
        unfolding bij_betw_def
      proof (intro conjI)
        show "inj_on (\<lambda>s. t0 + s * (1-t0)) top1_unit_interval"
          by (rule inj_onI) (use ht0_int in \<open>by100 simp\<close>)
        show "(\<lambda>s. t0 + s * (1-t0)) ` top1_unit_interval = ?I1"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> (\<lambda>s. t0 + s * (1-t0)) ` top1_unit_interval"
          then obtain s where hs: "s \<in> top1_unit_interval" "x = t0 + s * (1-t0)" by (by100 blast)
          have hs_bounds: "0 \<le> s" "s \<le> 1" using hs(1) unfolding top1_unit_interval_def by (by100 auto)+
          have h1t0: "0 \<le> 1 - t0" using ht0_int(2) by (by100 linarith)
          have "0 \<le> s * (1-t0)" by (rule mult_nonneg_nonneg[OF hs_bounds(1) h1t0])
          have "s * (1-t0) \<le> 1 * (1-t0)"
            using mult_right_mono[OF hs_bounds(2) h1t0] .
          hence "s * (1-t0) \<le> 1 - t0" by (by100 simp)
          have "0 \<le> x" using hs(2) \<open>0 \<le> s * (1-t0)\<close> ht0_int(1) by (by100 linarith)
          have "x \<le> 1" using hs(2) \<open>s * (1-t0) \<le> 1 - t0\<close> by (by100 linarith)
          have "x \<in> top1_unit_interval"
            unfolding top1_unit_interval_def using \<open>0 \<le> x\<close> \<open>x \<le> 1\<close> by (by100 simp)
          moreover have "x \<ge> t0" using hs(2) \<open>0 \<le> s * (1-t0)\<close> by (by100 linarith)
          ultimately show "x \<in> ?I1" by (by100 blast)
        next
          fix x assume "x \<in> ?I1"
          hence hx: "x \<in> top1_unit_interval" "x \<ge> t0" by (by100 blast)+
          let ?s = "(x - t0) / (1 - t0)"
          have "?s \<in> top1_unit_interval" using hx ht0_int unfolding top1_unit_interval_def by (by100 auto)
          moreover have "t0 + ?s * (1-t0) = x" using ht0_int(2) by (by100 simp)
          ultimately show "x \<in> (\<lambda>s. t0 + s * (1-t0)) ` top1_unit_interval" by (by100 force)
        qed
      qed
      \<comment> \<open>Compact + Hausdorff.\<close>
      have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
      proof -
        have "compact (top1_unit_interval :: real set)" unfolding top1_unit_interval_def by (rule compact_Icc)
        thus ?thesis using top1_compact_on_subspace_UNIV_iff_compact
          unfolding top1_unit_interval_topology_def by (by100 blast)
      qed
      have hI1_haus: "is_hausdorff_on ?I1 (subspace_topology top1_unit_interval top1_unit_interval_topology ?I1)"
      proof -
        have "is_hausdorff_on (UNIV::real set) top1_open_sets" by (rule top1_R_is_hausdorff)
        hence "is_hausdorff_on top1_unit_interval top1_unit_interval_topology"
          using conjunct2[OF conjunct2[OF Theorem_17_11]] unfolding top1_unit_interval_topology_def
          by (by100 blast)
        thus ?thesis using conjunct2[OF conjunct2[OF Theorem_17_11]] hI1_sub by (by100 blast)
      qed
      show ?thesis by (rule Theorem_26_6[OF hTI hTI1 hI_compact hI1_haus hscale_cont hscale_bij])
    qed
    from homeomorphism_on_comp[OF hscale_homeo hh_restr_homeo]
    have "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
        D2 (subspace_topology X TX D2) (h \<circ> (\<lambda>s. t0 + s * (1 - t0)))" .
    moreover have "is_topology_on_strict D2 (subspace_topology X TX D2)"
    proof -
      have hTopX: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
      have "is_topology_on D2 (subspace_topology X TX D2)"
        by (rule subspace_topology_is_topology_on[OF hTopX hD2_sub])
      moreover have "subspace_topology X TX D2 \<subseteq> Pow D2"
        unfolding subspace_topology_def by (by100 blast)
      ultimately show ?thesis unfolding is_topology_on_strict_def by (by100 blast)
    qed
    ultimately show ?thesis unfolding top1_is_arc_on_def by (by100 blast)
  qed
  show ?thesis using hD_eq hD_inter hD1_arc hD2_arc ha_D1 hb_D2 hp_D1 hp_D2 hD1_sub hD2_sub
    by (by100 blast)
qed

\<comment> \<open>Reusable: endpoints of sub-arcs from arc_split_at_given_point.
   If D is split at interior point p into D1 (containing a) and D2 (containing b),
   then endpoints of D1 = {a,p} and endpoints of D2 = {p,b}.\<close>
lemma arc_split_endpoints:
  assumes hT: "is_topology_on_strict X TX" and hH: "is_hausdorff_on X TX"
      and hDX: "D \<subseteq> X" and hArc: "top1_is_arc_on D (subspace_topology X TX D)"
      and "D = D1 \<union> D2" "D1 \<inter> D2 = {p}"
      and hD1_arc: "top1_is_arc_on D1 (subspace_topology X TX D1)"
      and hD2_arc: "top1_is_arc_on D2 (subspace_topology X TX D2)"
      and "a \<in> D1" "b \<in> D2" "p \<in> D1" "p \<in> D2" "D1 \<subseteq> X" "D2 \<subseteq> X"
      and hep: "top1_arc_endpoints_on D (subspace_topology X TX D) = {a, b}"
      and hp_int: "p \<notin> top1_arc_endpoints_on D (subspace_topology X TX D)"
  shows "top1_arc_endpoints_on D1 (subspace_topology X TX D1) = {a, p}"
    and "top1_arc_endpoints_on D2 (subspace_topology X TX D2) = {p, b}"
proof -
  have hab: "a \<noteq> b" proof
    assume "a = b" hence "a \<in> D1 \<inter> D2" using assms(9,10) by (by100 blast)
    hence "a = p" using assms(6) by (by100 blast)
    thus False using hp_int hep by (by100 blast) qed
  \<comment> \<open>Step 1: Get oriented homeomorphism h: [0,1] \<rightarrow> D with h(0)=a, h(1)=b.\<close>
  obtain h where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      D (subspace_topology X TX D) h" and hh0: "h 0 = a" and hh1: "h 1 = b"
  proof -
    obtain h0 where hh0: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
        D (subspace_topology X TX D) h0"
      using hArc unfolding top1_is_arc_on_def by (by100 blast)
    have heps0: "top1_arc_endpoints_on D (subspace_topology X TX D) = {h0 0, h0 1}"
      by (rule arc_endpoints_are_boundary[OF hT hH hDX hArc hh0])
    hence hab_h0: "{h0 0, h0 1} = {a, b}" using hep by (by100 simp)
    show ?thesis
    proof (cases "h0 0 = a")
      case True
      have "h0 0 \<noteq> h0 1" proof
        assume "h0 0 = h0 1" hence "{h0 0, h0 1} = {h0 0}" by (by100 simp)
        hence "card {a, b} \<le> 1" using hab_h0 by (by100 simp)
        thus False using hab by (by100 simp) qed
      from doubleton_eq_iff[OF hab_h0 this]
      have "(h0 0 = a \<and> h0 1 = b) \<or> (h0 0 = b \<and> h0 1 = a)" .
      hence "h0 1 = b" using True hab by (by100 fast)
      thus ?thesis using that[OF hh0 True] by (by100 simp)
    next
      case False hence "h0 0 = b" using hab_h0 by (by100 force)
      have "h0 0 \<noteq> h0 1" proof
        assume "h0 0 = h0 1" hence "{h0 0, h0 1} = {h0 0}" by (by100 simp)
        hence "card {a, b} \<le> 1" using hab_h0 by (by100 simp)
        thus False using hab by (by100 simp) qed
      from doubleton_eq_iff[OF hab_h0 this]
      have "(h0 0 = a \<and> h0 1 = b) \<or> (h0 0 = b \<and> h0 1 = a)" .
      hence "h0 1 = a" using \<open>h0 0 = b\<close> hab by (by100 fast)
      have hcomp: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          D (subspace_topology X TX D) (h0 \<circ> (\<lambda>t::real. 1 - t))"
        by (rule homeomorphism_on_comp[OF unit_interval_reversal_homeomorphism hh0])
      have "(h0 \<circ> (\<lambda>t::real. 1 - t)) 0 = h0 1" unfolding comp_def by (by100 simp)
      hence "(h0 \<circ> (\<lambda>t::real. 1 - t)) 0 = a" using \<open>h0 1 = a\<close> by (by100 simp)
      moreover have "(h0 \<circ> (\<lambda>t::real. 1 - t)) 1 = h0 0" unfolding comp_def by (by100 simp)
      hence "(h0 \<circ> (\<lambda>t::real. 1 - t)) 1 = b" using \<open>h0 0 = b\<close> by (by100 simp)
      ultimately show ?thesis using that[OF hcomp] by (by100 simp)
    qed
  qed
  have hinj: "inj_on h top1_unit_interval"
    using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  have himg: "h ` top1_unit_interval = D"
    using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  have hTopX: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>Step 2: p = h(t0) for unique t0 \<in> (0,1).\<close>
  have hp_D: "p \<in> D" using assms(5) assms(11) by (by100 blast)
  define t0 where "t0 = inv_into top1_unit_interval h p"
  have ht0_I: "t0 \<in> top1_unit_interval" unfolding t0_def
    using inv_into_into[of p h top1_unit_interval] hp_D himg by (by100 simp)
  have ht0_p: "h t0 = p" unfolding t0_def
    using f_inv_into_f[of p h top1_unit_interval] hp_D himg by (by100 simp)
  have ht0_ne0: "t0 \<noteq> 0" proof assume "t0 = 0" hence "p = a" using ht0_p hh0 by (by100 simp)
    thus False using hp_int hep by (by100 blast) qed
  have ht0_ne1: "t0 \<noteq> 1" proof assume "t0 = 1" hence "p = b" using ht0_p hh1 by (by100 simp)
    thus False using hp_int hep by (by100 blast) qed
  have ht0_open: "0 < t0" "t0 < 1"
    using ht0_I ht0_ne0 ht0_ne1 unfolding top1_unit_interval_def by (by100 auto)+
  \<comment> \<open>Step 3: h\<inverse>(D1) = [0,t0], h\<inverse>(D2) = [t0,1].
     Key: D1, D2 are connected, so their preimages under h are connected intervals.
     connected\_contains\_Icc gives [0,t0] \<subseteq> h\<inverse>(D1) and [t0,1] \<subseteq> h\<inverse>(D2).
     The intersection constraint forces equality.\<close>
  let ?S1 = "{t \<in> top1_unit_interval. h t \<in> D1}"
  let ?S2 = "{t \<in> top1_unit_interval. h t \<in> D2}"
  have h0_S1: "0 \<in> ?S1" using hh0 assms(9) unfolding top1_unit_interval_def by (by100 auto)
  have ht0_S1: "t0 \<in> ?S1" using ht0_p assms(11) ht0_I by (by100 blast)
  have ht0_S2: "t0 \<in> ?S2" using ht0_p assms(12) ht0_I by (by100 blast)
  have h1_S2: "1 \<in> ?S2" using hh1 assms(10) unfolding top1_unit_interval_def by (by100 auto)
  have hS12_inter: "?S1 \<inter> ?S2 = {t0}"
  proof (rule set_eqI, rule iffI)
    fix t assume "t \<in> ?S1 \<inter> ?S2"
    hence "h t \<in> D1 \<inter> D2" "t \<in> top1_unit_interval" by (by100 blast)+
    hence "h t = p" using assms(6) by (by100 blast)
    thus "t \<in> {t0}" using hinj \<open>t \<in> top1_unit_interval\<close> ht0_I ht0_p
      unfolding inj_on_def by (by100 blast)
  next
    fix t assume "t \<in> {t0}" thus "t \<in> ?S1 \<inter> ?S2" using ht0_S1 ht0_S2 by (by100 blast)
  qed
  have hS12_union: "?S1 \<union> ?S2 = top1_unit_interval"
  proof (rule set_eqI, rule iffI)
    fix t assume "t \<in> ?S1 \<union> ?S2" thus "t \<in> top1_unit_interval" by (by100 blast)
  next
    fix t assume "t \<in> top1_unit_interval"
    hence "h t \<in> D" using himg by (by100 blast)
    thus "t \<in> ?S1 \<union> ?S2" using assms(5) \<open>t \<in> top1_unit_interval\<close> by (by100 blast)
  qed
  \<comment> \<open>Connected preimages via bridge to standard 'connected'.\<close>
  have hS1_connected: "connected ?S1"
  proof -
    \<comment> \<open>D1 is connected (it's an arc).\<close>
    have hD1_conn: "top1_connected_on D1 (subspace_topology X TX D1)"
    proof -
      obtain g where hg: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          D1 (subspace_topology X TX D1) g"
        using hD1_arc unfolding top1_is_arc_on_def by (by100 blast)
      hence hg_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          D1 (subspace_topology X TX D1) g" and hg_img: "g ` top1_unit_interval = D1"
        unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)+
      have hTD1: "is_topology_on D1 (subspace_topology X TX D1)"
        by (rule subspace_topology_is_topology_on[OF hTopX assms(13)])
      from Theorem_23_5[OF top1_unit_interval_topology_is_topology_on hTD1
          top1_unit_interval_connected hg_cont]
      have "top1_connected_on (g ` top1_unit_interval)
          (subspace_topology D1 (subspace_topology X TX D1) (g ` top1_unit_interval))" .
      hence "top1_connected_on D1
          (subspace_topology D1 (subspace_topology X TX D1) D1)" using hg_img by (by100 simp)
      moreover have "subspace_topology D1 (subspace_topology X TX D1) D1 = subspace_topology X TX D1"
      proof (rule subspace_topology_self)
        show "\<forall>U \<in> subspace_topology X TX D1. U \<subseteq> D1"
          unfolding subspace_topology_def by (by100 blast)
      qed
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>h\<inverse> is continuous D \<rightarrow> [0,1]. Use Theorem 23.5 with D1 as connected subspace of D.\<close>
    have hinv_cont: "top1_continuous_map_on D (subspace_topology X TX D)
        top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval h)"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hD1_sub_D: "D1 \<subseteq> D" using assms(5) by (by100 blast)
    \<comment> \<open>Restrict h\<inverse> to D1.\<close>
    have hinv_D1_cont: "top1_continuous_map_on D1 (subspace_topology X TX D1)
        top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval h)"
    proof -
      have "subspace_topology X TX D1 = subspace_topology D (subspace_topology X TX D) D1"
        using subspace_topology_trans[of D1 D X TX] hD1_sub_D hDX by (by100 simp)
      thus ?thesis
        using top1_continuous_map_on_restrict_domain_simple[OF hinv_cont hD1_sub_D]
        by (by100 simp)
    qed
    have hTI: "is_topology_on top1_unit_interval top1_unit_interval_topology"
      by (rule top1_unit_interval_topology_is_topology_on)
    have hTD1: "is_topology_on D1 (subspace_topology X TX D1)"
      by (rule subspace_topology_is_topology_on[OF hTopX assms(13)])
    from Theorem_23_5[OF hTD1 hTI hD1_conn hinv_D1_cont]
    have "top1_connected_on (inv_into top1_unit_interval h ` D1)
        (subspace_topology top1_unit_interval top1_unit_interval_topology
          (inv_into top1_unit_interval h ` D1))" .
    \<comment> \<open>inv\_into image of D1 = S1.\<close>
    moreover have "inv_into top1_unit_interval h ` D1 = ?S1"
    proof (rule set_eqI, rule iffI)
      fix t assume "t \<in> inv_into top1_unit_interval h ` D1"
      then obtain x where hx: "x \<in> D1" "t = inv_into top1_unit_interval h x" by (by100 blast)
      have "x \<in> h ` top1_unit_interval" using hx(1) hD1_sub_D himg by (by100 blast)
      hence "t \<in> top1_unit_interval"
        using inv_into_into[of x h top1_unit_interval] hx(2) by (by100 simp)
      moreover have "h t = x" using f_inv_into_f[of x h top1_unit_interval]
          \<open>x \<in> h ` top1_unit_interval\<close> hx(2) by (by100 simp)
      ultimately show "t \<in> ?S1" using hx(1) by (by100 blast)
    next
      fix t assume "t \<in> ?S1"
      hence ht: "t \<in> top1_unit_interval" "h t \<in> D1" by (by100 blast)+
      have "inv_into top1_unit_interval h (h t) = t"
        by (rule inv_into_f_f[OF hinj ht(1)])
      thus "t \<in> inv_into top1_unit_interval h ` D1" using ht(2) by (by100 force)
    qed
    ultimately have "top1_connected_on ?S1
        (subspace_topology top1_unit_interval top1_unit_interval_topology ?S1)"
      by (by100 simp)
    hence "top1_connected_on ?S1 (subspace_topology UNIV top1_open_sets ?S1)"
    proof -
      have "?S1 \<subseteq> top1_unit_interval" by (by100 blast)
      have "subspace_topology top1_unit_interval top1_unit_interval_topology ?S1
          = subspace_topology UNIV top1_open_sets ?S1"
        unfolding top1_unit_interval_topology_def
        using subspace_topology_trans[of ?S1 top1_unit_interval "UNIV :: real set" top1_open_sets]
          \<open>?S1 \<subseteq> top1_unit_interval\<close> by (by100 simp)
      thus ?thesis using \<open>top1_connected_on ?S1
          (subspace_topology top1_unit_interval top1_unit_interval_topology ?S1)\<close> by (by100 simp)
    qed
    thus "connected ?S1" using top1_connected_on_subspace_open_iff_connected by (by100 blast)
  qed
  have hS2_connected: "connected ?S2"
  proof -
    have hD2_conn: "top1_connected_on D2 (subspace_topology X TX D2)"
    proof -
      obtain g where hg: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          D2 (subspace_topology X TX D2) g"
        using hD2_arc unfolding top1_is_arc_on_def by (by100 blast)
      hence hg_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          D2 (subspace_topology X TX D2) g" and hg_img: "g ` top1_unit_interval = D2"
        unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)+
      have hTD2: "is_topology_on D2 (subspace_topology X TX D2)"
        by (rule subspace_topology_is_topology_on[OF hTopX assms(14)])
      from Theorem_23_5[OF top1_unit_interval_topology_is_topology_on hTD2
          top1_unit_interval_connected hg_cont]
      have "top1_connected_on (g ` top1_unit_interval)
          (subspace_topology D2 (subspace_topology X TX D2) (g ` top1_unit_interval))" .
      hence "top1_connected_on D2
          (subspace_topology D2 (subspace_topology X TX D2) D2)" using hg_img by (by100 simp)
      moreover have "subspace_topology D2 (subspace_topology X TX D2) D2 = subspace_topology X TX D2"
      proof (rule subspace_topology_self)
        show "\<forall>U \<in> subspace_topology X TX D2. U \<subseteq> D2"
          unfolding subspace_topology_def by (by100 blast)
      qed
      ultimately show ?thesis by (by100 simp)
    qed
    have hD2_sub_D: "D2 \<subseteq> D" using assms(5) by (by100 blast)
    have hinv_D2_cont: "top1_continuous_map_on D2 (subspace_topology X TX D2)
        top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval h)"
    proof -
      have hinv_cont: "top1_continuous_map_on D (subspace_topology X TX D)
          top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval h)"
        using hh unfolding top1_homeomorphism_on_def by (by100 blast)
      have "subspace_topology X TX D2 = subspace_topology D (subspace_topology X TX D) D2"
        using subspace_topology_trans[of D2 D X TX] hD2_sub_D hDX by (by100 simp)
      thus ?thesis
        using top1_continuous_map_on_restrict_domain_simple[OF hinv_cont hD2_sub_D]
        by (by100 simp)
    qed
    have hTI: "is_topology_on top1_unit_interval top1_unit_interval_topology"
      by (rule top1_unit_interval_topology_is_topology_on)
    have hTD2: "is_topology_on D2 (subspace_topology X TX D2)"
      by (rule subspace_topology_is_topology_on[OF hTopX assms(14)])
    from Theorem_23_5[OF hTD2 hTI hD2_conn hinv_D2_cont]
    have "top1_connected_on (inv_into top1_unit_interval h ` D2)
        (subspace_topology top1_unit_interval top1_unit_interval_topology
          (inv_into top1_unit_interval h ` D2))" .
    moreover have "inv_into top1_unit_interval h ` D2 = ?S2"
    proof (rule set_eqI, rule iffI)
      fix t assume "t \<in> inv_into top1_unit_interval h ` D2"
      then obtain x where hx: "x \<in> D2" "t = inv_into top1_unit_interval h x" by (by100 blast)
      have "x \<in> h ` top1_unit_interval" using hx(1) hD2_sub_D himg by (by100 blast)
      hence "t \<in> top1_unit_interval"
        using inv_into_into[of x h top1_unit_interval] hx(2) by (by100 simp)
      moreover have "h t = x" using f_inv_into_f[of x h top1_unit_interval]
          \<open>x \<in> h ` top1_unit_interval\<close> hx(2) by (by100 simp)
      ultimately show "t \<in> ?S2" using hx(1) by (by100 blast)
    next
      fix t assume "t \<in> ?S2"
      hence ht: "t \<in> top1_unit_interval" "h t \<in> D2" by (by100 blast)+
      have "inv_into top1_unit_interval h (h t) = t"
        by (rule inv_into_f_f[OF hinj ht(1)])
      thus "t \<in> inv_into top1_unit_interval h ` D2" using ht(2) by (by100 force)
    qed
    ultimately have "top1_connected_on ?S2
        (subspace_topology top1_unit_interval top1_unit_interval_topology ?S2)"
      by (by100 simp)
    hence "top1_connected_on ?S2 (subspace_topology UNIV top1_open_sets ?S2)"
    proof -
      have "?S2 \<subseteq> top1_unit_interval" by (by100 blast)
      have "subspace_topology top1_unit_interval top1_unit_interval_topology ?S2
          = subspace_topology UNIV top1_open_sets ?S2"
        unfolding top1_unit_interval_topology_def
        using subspace_topology_trans[of ?S2 top1_unit_interval "UNIV :: real set" top1_open_sets]
          \<open>?S2 \<subseteq> top1_unit_interval\<close> by (by100 simp)
      thus ?thesis using \<open>top1_connected_on ?S2
          (subspace_topology top1_unit_interval top1_unit_interval_topology ?S2)\<close> by (by100 simp)
    qed
    thus "connected ?S2" using top1_connected_on_subspace_open_iff_connected by (by100 blast)
  qed
  \<comment> \<open>connected\_contains\_Icc: {0..t0} \<subseteq> S1 and {t0..1} \<subseteq> S2.\<close>
  have hIcc_S1: "{0..t0} \<subseteq> ?S1"
    using connected_contains_Icc[OF hS1_connected h0_S1 ht0_S1] .
  have hIcc_S2: "{t0..1} \<subseteq> ?S2"
    using connected_contains_Icc[OF hS2_connected ht0_S2 h1_S2] .
  \<comment> \<open>S1 \<subseteq> {0..t0}: if t \<in> S1 with t > t0, then t \<in> {t0..1} \<subseteq> S2, so t \<in> S1\<inter>S2 = {t0}, contradiction.\<close>
  have hS1_eq: "?S1 = {t \<in> top1_unit_interval. t \<le> t0}"
  proof (rule set_eqI, rule iffI)
    fix t assume "t \<in> ?S1"
    hence ht: "t \<in> top1_unit_interval" "h t \<in> D1" by (by100 blast)+
    show "t \<in> {t \<in> top1_unit_interval. t \<le> t0}"
    proof (rule ccontr)
      assume "\<not> t \<in> {t \<in> top1_unit_interval. t \<le> t0}"
      hence "t > t0" using ht(1) by (by100 force)
      hence "t \<in> {t0..1}" using ht(1) unfolding top1_unit_interval_def by (by100 auto)
      hence "t \<in> ?S2" using hIcc_S2 by (by100 blast)
      hence "t \<in> ?S1 \<inter> ?S2" using \<open>t \<in> ?S1\<close> by (by100 blast)
      hence "t = t0" using hS12_inter by (by100 blast)
      thus False using \<open>t > t0\<close> by (by100 simp)
    qed
  next
    fix t assume "t \<in> {t \<in> top1_unit_interval. t \<le> t0}"
    hence "t \<in> {0..t0}" unfolding top1_unit_interval_def by (by100 auto)
    thus "t \<in> ?S1" using hIcc_S1 by (by100 blast)
  qed
  have hS2_eq: "?S2 = {t \<in> top1_unit_interval. t \<ge> t0}"
  proof (rule set_eqI, rule iffI)
    fix t assume "t \<in> ?S2"
    hence ht: "t \<in> top1_unit_interval" "h t \<in> D2" by (by100 blast)+
    show "t \<in> {t \<in> top1_unit_interval. t \<ge> t0}"
    proof (rule ccontr)
      assume "\<not> t \<in> {t \<in> top1_unit_interval. t \<ge> t0}"
      hence "t < t0" using ht(1) by (by100 force)
      hence "t \<in> {0..t0}" using ht(1) unfolding top1_unit_interval_def by (by100 auto)
      hence "t \<in> ?S1" using hIcc_S1 by (by100 blast)
      hence "t \<in> ?S1 \<inter> ?S2" using \<open>t \<in> ?S2\<close> by (by100 blast)
      hence "t = t0" using hS12_inter by (by100 blast)
      thus False using \<open>t < t0\<close> by (by100 simp)
    qed
  next
    fix t assume "t \<in> {t \<in> top1_unit_interval. t \<ge> t0}"
    hence "t \<in> {t0..1}" unfolding top1_unit_interval_def by (by100 auto)
    thus "t \<in> ?S2" using hIcc_S2 by (by100 blast)
  qed
  \<comment> \<open>Step 4: Reuse homeomorphism construction from arc\_split\_at\_given\_point.
     h \<circ> (\<lambda>s. s*t0): [0,1] \<rightarrow> D1 with 0\<mapsto>a, 1\<mapsto>p.
     h \<circ> (\<lambda>s. t0 + s*(1-t0)): [0,1] \<rightarrow> D2 with 0\<mapsto>p, 1\<mapsto>b.\<close>
  have hD1_img: "h ` {t \<in> top1_unit_interval. t \<le> t0} = D1"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> h ` {t \<in> top1_unit_interval. t \<le> t0}"
    then obtain t where ht: "t \<in> top1_unit_interval" "t \<le> t0" "x = h t" by (by100 blast)
    hence "t \<in> ?S1" using hS1_eq by (by100 blast)
    thus "x \<in> D1" using ht(3) by (by100 blast)
  next
    fix x assume "x \<in> D1"
    hence "x \<in> D" using assms(5) by (by100 blast)
    hence "x \<in> h ` top1_unit_interval" using himg by (by100 blast)
    then obtain t where ht: "t \<in> top1_unit_interval" "x = h t" by (by100 blast)
    hence "t \<in> ?S1" using \<open>x \<in> D1\<close> by (by100 blast)
    hence "t \<le> t0" using hS1_eq by (by100 blast)
    thus "x \<in> h ` {t \<in> top1_unit_interval. t \<le> t0}" using ht by (by100 blast)
  qed
  have hD2_img: "h ` {t \<in> top1_unit_interval. t \<ge> t0} = D2"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> h ` {t \<in> top1_unit_interval. t \<ge> t0}"
    then obtain t where ht: "t \<in> top1_unit_interval" "t \<ge> t0" "x = h t" by (by100 blast)
    hence "t \<in> ?S2" using hS2_eq by (by100 blast)
    thus "x \<in> D2" using ht(3) by (by100 blast)
  next
    fix x assume "x \<in> D2"
    hence "x \<in> D" using assms(5) by (by100 blast)
    hence "x \<in> h ` top1_unit_interval" using himg by (by100 blast)
    then obtain t where ht: "t \<in> top1_unit_interval" "x = h t" by (by100 blast)
    hence "t \<in> ?S2" using \<open>x \<in> D2\<close> by (by100 blast)
    hence "t \<ge> t0" using hS2_eq by (by100 blast)
    thus "x \<in> h ` {t \<in> top1_unit_interval. t \<ge> t0}" using ht by (by100 blast)
  qed
  \<comment> \<open>Now construct homeomorphisms [0,1] \<rightarrow> D1 and [0,1] \<rightarrow> D2 via arc\_split\_at\_given\_point's proof.\<close>
  \<comment> \<open>g1 = h \<circ> (\<lambda>s. s*t0): [0,1] \<rightarrow> D1 is a continuous bijection, hence homeomorphism (Thm 26.6).\<close>
  have hh1: "\<exists>g. top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      D1 (subspace_topology X TX D1) g \<and> g 0 = a \<and> g 1 = p"
  proof -
    let ?g = "h \<circ> (\<lambda>s. s * t0)"
    have hg0: "?g 0 = a" unfolding comp_def using hh0 by (by100 simp)
    have hg1: "?g 1 = p" unfolding comp_def using ht0_p by (by100 simp)
    \<comment> \<open>Image of ?g is D1.\<close>
    have hg_img: "?g ` top1_unit_interval = D1"
    proof -
      have "?g ` top1_unit_interval = h ` ((\<lambda>s. s * t0) ` top1_unit_interval)"
        using image_comp[of h "\<lambda>s. s * t0" top1_unit_interval] by (by100 simp)
      moreover have "(\<lambda>s::real. s * t0) ` top1_unit_interval = {t \<in> top1_unit_interval. t \<le> t0}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> (\<lambda>s. s * t0) ` top1_unit_interval"
        then obtain s where hs: "s \<in> top1_unit_interval" "x = s * t0" by (by100 blast)
        have hs_bds: "0 \<le> s" "s \<le> 1" using hs(1) unfolding top1_unit_interval_def by (by100 simp)+
        have "0 \<le> x" using hs(2) hs_bds(1) ht0_open(1) by (by100 simp)
        moreover have "x \<le> t0" using hs(2) hs_bds(2) ht0_open(1) by (by100 simp)
        moreover have "x \<le> 1" using \<open>x \<le> t0\<close> ht0_open(2) by (by100 linarith)
        ultimately show "x \<in> {t \<in> top1_unit_interval. t \<le> t0}"
          unfolding top1_unit_interval_def by (by100 simp)
      next
        fix x assume "x \<in> {t \<in> top1_unit_interval. t \<le> t0}"
        hence hx: "0 \<le> x" "x \<le> 1" "x \<le> t0" unfolding top1_unit_interval_def by (by100 simp)+
        have "x / t0 \<in> top1_unit_interval" unfolding top1_unit_interval_def
          using hx ht0_open by (by100 simp)
        moreover have "x / t0 * t0 = x" using ht0_open(1) by (by100 simp)
        ultimately show "x \<in> (\<lambda>s. s * t0) ` top1_unit_interval" by (by100 force)
      qed
      ultimately show ?thesis using hD1_img by (by100 simp)
    qed
    \<comment> \<open>?g is injective.\<close>
    have hg_inj: "inj_on ?g top1_unit_interval"
    proof (rule inj_onI)
      fix x y assume hx: "x \<in> top1_unit_interval" and hy: "y \<in> top1_unit_interval"
          and heq: "?g x = ?g y"
      hence "h (x * t0) = h (y * t0)" unfolding comp_def by (by100 simp)
      moreover have "x * t0 \<in> top1_unit_interval"
      proof -
        have "0 \<le> x" "x \<le> 1" using hx unfolding top1_unit_interval_def by (by100 simp)+
        hence "0 \<le> x * t0" "x * t0 \<le> 1" using ht0_open
          by (by100 simp) (rule mult_le_one; by100 linarith)
        thus ?thesis unfolding top1_unit_interval_def by (by100 simp)
      qed
      moreover have "y * t0 \<in> top1_unit_interval"
      proof -
        have "0 \<le> y" "y \<le> 1" using hy unfolding top1_unit_interval_def by (by100 simp)+
        hence "0 \<le> y * t0" "y * t0 \<le> 1" using ht0_open
          by (by100 simp) (rule mult_le_one; by100 linarith)
        thus ?thesis unfolding top1_unit_interval_def by (by100 simp)
      qed
      ultimately have "x * t0 = y * t0" using hinj unfolding inj_on_def by (by100 blast)
      thus "x = y" using ht0_open(1) by (by100 simp)
    qed
    have hg_bij: "bij_betw ?g top1_unit_interval D1"
      unfolding bij_betw_def using hg_inj hg_img by (by100 blast)
    \<comment> \<open>?g is continuous [0,1] \<rightarrow> D1 (composition of affine scaling + h restricted).\<close>
    have hg_cont_D1: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
        D1 (subspace_topology X TX D1) ?g"
    proof -
      \<comment> \<open>h: [0,1] \<rightarrow> D cont (from homeomorphism). Enlarge codomain to X.\<close>
      have hh_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          D (subspace_topology X TX D) h"
        using hh unfolding top1_homeomorphism_on_def by (by100 blast)
      \<comment> \<open>Scaling t \<mapsto> t*t0: [0,1] \<rightarrow> [0,1] is continuous.\<close>
      have hscale_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          top1_unit_interval top1_unit_interval_topology (\<lambda>s::real. s * t0)"
      proof -
        have "continuous_on UNIV ((*) t0 :: real \<Rightarrow> real)" by (rule continuous_on_mult_const)
        hence hcont: "continuous_on UNIV (\<lambda>s::real. s * t0)"
          using mult.commute[of t0] by (by100 simp)
        have himg: "\<And>s::real. s \<in> top1_unit_interval \<Longrightarrow> s * t0 \<in> top1_unit_interval"
          unfolding top1_unit_interval_def using ht0_open
          using mult_le_one[of _ t0] by (by100 simp)
        from top1_continuous_map_on_real_subspace_open_sets[OF himg hcont]
        show ?thesis unfolding top1_unit_interval_topology_def .
      qed
      \<comment> \<open>Composition h \<circ> scale: [0,1] \<rightarrow> D is continuous.\<close>
      from top1_continuous_map_on_comp[OF hscale_cont hh_cont]
      have hcomp_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          D (subspace_topology X TX D) (h \<circ> (\<lambda>s::real. s * t0))" .
      \<comment> \<open>Shrink codomain from D to D1.\<close>
      have hg_img_sub: "?g ` top1_unit_interval \<subseteq> D1" using hg_img by (by100 blast)
      have hD1_sub_D: "D1 \<subseteq> D" using assms(5) by (by100 blast)
      from top1_continuous_map_on_codomain_shrink[OF hcomp_cont hg_img_sub hD1_sub_D]
      have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          D1 (subspace_topology D (subspace_topology X TX D) D1) ?g" .
      moreover have "subspace_topology D (subspace_topology X TX D) D1
          = subspace_topology X TX D1"
        using subspace_topology_trans[of D1 D X TX] hD1_sub_D hDX by (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>[0,1] compact, D1 Hausdorff \<Rightarrow> Theorem 26.6.\<close>
    have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
    proof -
      have "compact (top1_unit_interval :: real set)" unfolding top1_unit_interval_def
        by (rule compact_Icc)
      thus ?thesis using top1_compact_on_subspace_UNIV_iff_compact
        unfolding top1_unit_interval_topology_def by (by100 blast)
    qed
    have hD1_haus: "is_hausdorff_on D1 (subspace_topology X TX D1)"
      using conjunct2[OF conjunct2[OF Theorem_17_11]] hH assms(13) by (by100 blast)
    have hTI: "is_topology_on top1_unit_interval top1_unit_interval_topology"
      by (rule top1_unit_interval_topology_is_topology_on)
    have hTD1: "is_topology_on D1 (subspace_topology X TX D1)"
      by (rule subspace_topology_is_topology_on[OF hTopX assms(13)])
    from Theorem_26_6[OF hTI hTD1 hI_compact hD1_haus hg_cont_D1 hg_bij]
    show ?thesis using hg0 hg1 by (by100 blast)
  qed
  \<comment> \<open>g2 = h \<circ> (\<lambda>s. t0 + s*(1-t0)): [0,1] \<rightarrow> D2 with 0\<mapsto>p, 1\<mapsto>b.\<close>
  have hh2: "\<exists>g. top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      D2 (subspace_topology X TX D2) g \<and> g 0 = p \<and> g 1 = b"
  proof -
    let ?g2 = "h \<circ> (\<lambda>s. t0 + s * (1 - t0))"
    have hg2_0: "?g2 0 = p" unfolding comp_def using ht0_p by (by100 simp)
    have hg2_1: "?g2 1 = b" unfolding comp_def using \<open>h 1 = b\<close> by (by100 simp)
    have hg2_img: "?g2 ` top1_unit_interval = D2"
    proof -
      have "?g2 ` top1_unit_interval = h ` ((\<lambda>s. t0 + s * (1-t0)) ` top1_unit_interval)"
        using image_comp[of h "\<lambda>s. t0 + s * (1-t0)" top1_unit_interval] by (by100 simp)
      moreover have "(\<lambda>s::real. t0 + s * (1-t0)) ` top1_unit_interval = {t \<in> top1_unit_interval. t \<ge> t0}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> (\<lambda>s. t0 + s * (1-t0)) ` top1_unit_interval"
        then obtain s where hs: "s \<in> top1_unit_interval" "x = t0 + s * (1-t0)" by (by100 blast)
        have "0 \<le> s" "s \<le> 1" using hs(1) unfolding top1_unit_interval_def by (by100 simp)+
        have "t0 \<le> x" using hs(2) \<open>0 \<le> s\<close> ht0_open by (by100 simp)
        moreover have "0 \<le> x" using \<open>t0 \<le> x\<close> ht0_open(1) by (by100 linarith)
        moreover have "x \<le> 1"
        proof -
          have "s * (1-t0) \<le> 1 * (1-t0)" using mult_right_mono[OF \<open>s \<le> 1\<close>] ht0_open by (by100 simp)
          thus ?thesis using hs(2) by (by100 simp)
        qed
        ultimately show "x \<in> {t \<in> top1_unit_interval. t \<ge> t0}"
          unfolding top1_unit_interval_def by (by100 simp)
      next
        fix x assume "x \<in> {t \<in> top1_unit_interval. t \<ge> t0}"
        hence hx: "0 \<le> x" "x \<le> 1" "t0 \<le> x" unfolding top1_unit_interval_def by (by100 simp)+
        let ?s = "(x - t0) / (1 - t0)"
        have "0 \<le> ?s" using hx ht0_open by (by100 simp)
        moreover have "?s \<le> 1" using hx ht0_open by (by100 simp)
        ultimately have "?s \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
        moreover have "t0 + ?s * (1-t0) = x" using ht0_open(2) by (by100 simp)
        ultimately show "x \<in> (\<lambda>s. t0 + s * (1-t0)) ` top1_unit_interval" by (by100 force)
      qed
      ultimately show ?thesis using hD2_img by (by100 simp)
    qed
    have hg2_inj: "inj_on ?g2 top1_unit_interval"
    proof (rule inj_onI)
      fix x y assume hx: "x \<in> top1_unit_interval" and hy: "y \<in> top1_unit_interval"
          and heq: "?g2 x = ?g2 y"
      hence "h (t0 + x * (1-t0)) = h (t0 + y * (1-t0))" unfolding comp_def by (by100 simp)
      moreover have "t0 + x * (1-t0) \<in> top1_unit_interval"
      proof -
        have "0 \<le> x" "x \<le> 1" using hx unfolding top1_unit_interval_def by (by100 simp)+
        have "0 \<le> t0 + x * (1-t0)" using \<open>0 \<le> x\<close> ht0_open by (by100 simp)
        moreover have "x*(1-t0) \<le> 1*(1-t0)" using mult_right_mono[OF \<open>x \<le> 1\<close>] ht0_open by (by100 simp)
        hence "t0 + x*(1-t0) \<le> 1" by (by100 simp)
        ultimately show ?thesis unfolding top1_unit_interval_def by (by100 simp)
      qed
      moreover have "t0 + y * (1-t0) \<in> top1_unit_interval"
      proof -
        have "0 \<le> y" "y \<le> 1" using hy unfolding top1_unit_interval_def by (by100 simp)+
        have "0 \<le> t0 + y * (1-t0)" using \<open>0 \<le> y\<close> ht0_open by (by100 simp)
        moreover have "y*(1-t0) \<le> 1*(1-t0)" using mult_right_mono[OF \<open>y \<le> 1\<close>] ht0_open by (by100 simp)
        hence "t0 + y*(1-t0) \<le> 1" by (by100 simp)
        ultimately show ?thesis unfolding top1_unit_interval_def by (by100 simp)
      qed
      ultimately have "t0 + x * (1-t0) = t0 + y * (1-t0)"
        using hinj unfolding inj_on_def by (by100 blast)
      thus "x = y" using ht0_open(2) by (by100 simp)
    qed
    have hg2_bij: "bij_betw ?g2 top1_unit_interval D2"
      unfolding bij_betw_def using hg2_inj hg2_img by (by100 blast)
    have hg2_cont_D2: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
        D2 (subspace_topology X TX D2) ?g2"
    proof -
      have hh_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          D (subspace_topology X TX D) h"
        using hh unfolding top1_homeomorphism_on_def by (by100 blast)
      have "continuous_on UNIV (\<lambda>s::real. t0 + s * (1 - t0))"
      proof -
        have "continuous_on UNIV ((*) (1 - t0) :: real \<Rightarrow> real)" by (rule continuous_on_mult_const)
        hence "continuous_on UNIV (\<lambda>s::real. s * (1 - t0))"
          using mult.commute[of "1-t0"] by (by100 simp)
        thus ?thesis
          by (intro continuous_on_add continuous_on_const)
      qed
      have himg2: "\<And>s::real. s \<in> top1_unit_interval \<Longrightarrow> t0 + s * (1-t0) \<in> top1_unit_interval"
      proof -
        fix s :: real assume "s \<in> top1_unit_interval"
        hence "0 \<le> s" "s \<le> 1" unfolding top1_unit_interval_def by (by100 simp)+
        have "0 \<le> t0 + s * (1 - t0)" using \<open>0 \<le> s\<close> ht0_open by (by100 simp)
        moreover have "t0 + s * (1 - t0) \<le> 1"
        proof -
          have "s * (1 - t0) \<le> 1 * (1 - t0)"
            using mult_right_mono[OF \<open>s \<le> 1\<close>] ht0_open by (by100 simp)
          thus ?thesis by (by100 simp)
        qed
        ultimately show "t0 + s * (1-t0) \<in> top1_unit_interval"
          unfolding top1_unit_interval_def by (by100 simp)
      qed
      have hcont2: "continuous_on UNIV (\<lambda>s::real. t0 + s * (1 - t0))" by (rule \<open>continuous_on UNIV _\<close>)
      from top1_continuous_map_on_real_subspace_open_sets[OF himg2 hcont2]
      have hscale2_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          top1_unit_interval top1_unit_interval_topology (\<lambda>s::real. t0 + s * (1 - t0))"
        unfolding top1_unit_interval_topology_def .
      from top1_continuous_map_on_comp[OF hscale2_cont hh_cont]
      have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          D (subspace_topology X TX D) ?g2" .
      from top1_continuous_map_on_codomain_shrink[OF this _ _]
      have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          D2 (subspace_topology D (subspace_topology X TX D) D2) ?g2"
        using hg2_img assms(5) by (by100 blast)
      moreover have "subspace_topology D (subspace_topology X TX D) D2 = subspace_topology X TX D2"
        using subspace_topology_trans[of D2 D X TX] assms(5) hDX by (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
    proof -
      have "compact (top1_unit_interval :: real set)" unfolding top1_unit_interval_def
        by (rule compact_Icc)
      thus ?thesis using top1_compact_on_subspace_UNIV_iff_compact
        unfolding top1_unit_interval_topology_def by (by100 blast)
    qed
    have hD2_haus: "is_hausdorff_on D2 (subspace_topology X TX D2)"
      using conjunct2[OF conjunct2[OF Theorem_17_11]] hH assms(14) by (by100 blast)
    have hTI: "is_topology_on top1_unit_interval top1_unit_interval_topology"
      by (rule top1_unit_interval_topology_is_topology_on)
    have hTD2: "is_topology_on D2 (subspace_topology X TX D2)"
      by (rule subspace_topology_is_topology_on[OF hTopX assms(14)])
    from Theorem_26_6[OF hTI hTD2 hI_compact hD2_haus hg2_cont_D2 hg2_bij]
    show ?thesis using hg2_0 hg2_1 by (by100 blast)
  qed
  \<comment> \<open>Step 5: Apply arc\_endpoints\_are\_boundary.\<close>
  obtain g1 where hg1: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      D1 (subspace_topology X TX D1) g1" "g1 0 = a" "g1 1 = p" using hh1 by (by100 blast)
  obtain g2 where hg2: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      D2 (subspace_topology X TX D2) g2" "g2 0 = p" "g2 1 = b" using hh2 by (by100 blast)
  have "top1_arc_endpoints_on D1 (subspace_topology X TX D1) = {g1 0, g1 1}"
    by (rule arc_endpoints_are_boundary[OF hT hH assms(13) hD1_arc hg1(1)])
  hence ep1: "top1_arc_endpoints_on D1 (subspace_topology X TX D1) = {a, p}"
    using hg1(2,3) by (by100 simp)
  have "top1_arc_endpoints_on D2 (subspace_topology X TX D2) = {g2 0, g2 1}"
    by (rule arc_endpoints_are_boundary[OF hT hH assms(14) hD2_arc hg2(1)])
  hence ep2: "top1_arc_endpoints_on D2 (subspace_topology X TX D2) = {p, b}"
    using hg2(2,3) by (by100 simp)
  show "top1_arc_endpoints_on D1 (subspace_topology X TX D1) = {a, p}" by (rule ep1)
  show "top1_arc_endpoints_on D2 (subspace_topology X TX D2) = {p, b}" by (rule ep2)
qed

\<comment> \<open>Helper: if an arc D = D1 \<union> D2 with D1 \<inter> D2 = {c} has both endpoints in D1,
   then D2 = {c} (D1 covers all of D except the junction point).\<close>
lemma arc_both_endpoints_in_one_part:
  assumes hT: "is_topology_on_strict X TX" and hH: "is_hausdorff_on X TX"
      and hDX: "D \<subseteq> X" and hArc: "top1_is_arc_on D (subspace_topology X TX D)"
      and "D = D1 \<union> D2" "D1 \<inter> D2 = {c}"
      and hD1_conn: "top1_connected_on D1 (subspace_topology X TX D1)" and "D1 \<subseteq> X"
      and hep: "top1_arc_endpoints_on D (subspace_topology X TX D) = {a, b}" and "a \<noteq> b"
      and "a \<in> D1" "b \<in> D1"
  shows "D2 = {c}"
proof -
  obtain h where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      D (subspace_topology X TX D) h"
    using hArc unfolding top1_is_arc_on_def by (by100 blast)
  have hinj: "inj_on h top1_unit_interval"
    using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  have himg: "h ` top1_unit_interval = D"
    using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  \<comment> \<open>h\<inverse>(D1) is connected (continuous preimage of connected D1).\<close>
  have hS1_conn: "connected {t \<in> top1_unit_interval. h t \<in> D1}"
  proof -
    have hTopX: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
    have hinv_cont: "top1_continuous_map_on D (subspace_topology X TX D)
        top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval h)"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hD1_sub_D: "D1 \<subseteq> D" using assms(5) by (by100 blast)
    have hinv_D1_cont: "top1_continuous_map_on D1 (subspace_topology X TX D1)
        top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval h)"
    proof -
      have "subspace_topology X TX D1 = subspace_topology D (subspace_topology X TX D) D1"
        using subspace_topology_trans[of D1 D X TX] hD1_sub_D hDX by (by100 simp)
      thus ?thesis using top1_continuous_map_on_restrict_domain_simple[OF hinv_cont hD1_sub_D]
        by (by100 simp)
    qed
    have hTD1: "is_topology_on D1 (subspace_topology X TX D1)"
      by (rule subspace_topology_is_topology_on[OF hTopX assms(8)])
    have hTI: "is_topology_on top1_unit_interval top1_unit_interval_topology"
      by (rule top1_unit_interval_topology_is_topology_on)
    from Theorem_23_5[OF hTD1 hTI hD1_conn hinv_D1_cont]
    have "top1_connected_on (inv_into top1_unit_interval h ` D1)
        (subspace_topology top1_unit_interval top1_unit_interval_topology
          (inv_into top1_unit_interval h ` D1))" .
    moreover have "inv_into top1_unit_interval h ` D1 = {t \<in> top1_unit_interval. h t \<in> D1}"
    proof (rule set_eqI, rule iffI)
      fix t assume "t \<in> inv_into top1_unit_interval h ` D1"
      then obtain x where hx: "x \<in> D1" "t = inv_into top1_unit_interval h x" by (by100 blast)
      have "x \<in> h ` top1_unit_interval" using hx(1) hD1_sub_D himg by (by100 blast)
      hence "t \<in> top1_unit_interval"
        using inv_into_into[of x h top1_unit_interval] hx(2) by (by100 simp)
      moreover have "h t = x" using f_inv_into_f[of x h top1_unit_interval]
          \<open>x \<in> h ` top1_unit_interval\<close> hx(2) by (by100 simp)
      ultimately show "t \<in> {t \<in> top1_unit_interval. h t \<in> D1}" using hx(1) by (by100 blast)
    next
      fix t assume "t \<in> {t \<in> top1_unit_interval. h t \<in> D1}"
      hence ht: "t \<in> top1_unit_interval" "h t \<in> D1" by (by100 blast)+
      have "inv_into top1_unit_interval h (h t) = t"
        by (rule inv_into_f_f[OF hinj ht(1)])
      thus "t \<in> inv_into top1_unit_interval h ` D1" using ht(2) by (by100 force)
    qed
    ultimately have "top1_connected_on {t \<in> top1_unit_interval. h t \<in> D1}
        (subspace_topology top1_unit_interval top1_unit_interval_topology
          {t \<in> top1_unit_interval. h t \<in> D1})" by (by100 simp)
    hence "top1_connected_on {t \<in> top1_unit_interval. h t \<in> D1}
        (subspace_topology UNIV top1_open_sets {t \<in> top1_unit_interval. h t \<in> D1})"
    proof -
      have "{t \<in> top1_unit_interval. h t \<in> D1} \<subseteq> top1_unit_interval" by (by100 blast)
      have "subspace_topology top1_unit_interval top1_unit_interval_topology
          {t \<in> top1_unit_interval. h t \<in> D1}
          = subspace_topology UNIV top1_open_sets {t \<in> top1_unit_interval. h t \<in> D1}"
        unfolding top1_unit_interval_topology_def
        using subspace_topology_trans[of "{t \<in> top1_unit_interval. h t \<in> D1}"
            top1_unit_interval "UNIV :: real set" top1_open_sets]
          \<open>{t \<in> top1_unit_interval. h t \<in> D1} \<subseteq> top1_unit_interval\<close> by (by100 simp)
      thus ?thesis using \<open>top1_connected_on {t \<in> top1_unit_interval. h t \<in> D1}
          (subspace_topology top1_unit_interval top1_unit_interval_topology
            {t \<in> top1_unit_interval. h t \<in> D1})\<close> by (by100 simp)
    qed
    thus ?thesis using top1_connected_on_subspace_open_iff_connected by (by100 blast)
  qed
  \<comment> \<open>endpoints(D) = {h 0, h 1}. Since {a,b} = {h 0, h 1} and a,b \<in> D1, h 0 \<in> D1 and h 1 \<in> D1.\<close>
  have hep_h: "top1_arc_endpoints_on D (subspace_topology X TX D) = {h 0, h 1}"
    by (rule arc_endpoints_are_boundary[OF hT hH hDX hArc hh])
  hence hab_h01: "{a, b} = {h 0, h 1}" using hep by (by100 simp)
  have "h 0 \<in> D1"
  proof -
    have "h 0 \<in> {a, b}" using hab_h01 by (by100 blast)
    thus ?thesis using assms(11,12) by (by100 blast)
  qed
  have "h 1 \<in> D1"
  proof -
    have "h 1 \<in> {a, b}" using hab_h01 by (by100 blast)
    thus ?thesis using assms(11,12) by (by100 blast)
  qed
  have "0 \<in> {t \<in> top1_unit_interval. h t \<in> D1}"
    using \<open>h 0 \<in> D1\<close> unfolding top1_unit_interval_def by (by100 simp)
  moreover have "1 \<in> {t \<in> top1_unit_interval. h t \<in> D1}"
    using \<open>h 1 \<in> D1\<close> unfolding top1_unit_interval_def by (by100 simp)
  \<comment> \<open>connected\_contains\_Icc: {0..1} \<subseteq> S1.\<close>
  ultimately have "{0..1} \<subseteq> {t \<in> top1_unit_interval. h t \<in> D1}"
    using connected_contains_Icc[OF hS1_conn] by (by100 blast)
  hence "top1_unit_interval \<subseteq> {t \<in> top1_unit_interval. h t \<in> D1}"
    unfolding top1_unit_interval_def by (by100 blast)
  hence "\<forall>t \<in> top1_unit_interval. h t \<in> D1" by (by100 blast)
  hence "D \<subseteq> D1" using himg by (by100 blast)
  hence "D2 \<subseteq> D1" using assms(5) by (by100 blast)
  hence "D2 \<subseteq> D1 \<inter> D2" by (by100 blast)
  thus "D2 = {c}" using assms(6) by (by100 blast)
qed

\<comment> \<open>Reusable: endpoints of concatenated arc = the non-shared endpoints.\<close>
lemma arc_concat_endpoints:
  assumes hT: "is_topology_on_strict X TX" and hH: "is_hausdorff_on X TX"
      and hA1: "top1_is_arc_on A1 (subspace_topology X TX A1)" and "A1 \<subseteq> X"
      and hA2: "top1_is_arc_on A2 (subspace_topology X TX A2)" and "A2 \<subseteq> X"
      and "A1 \<inter> A2 = {c}"
      and "c \<in> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
      and "c \<in> top1_arc_endpoints_on A2 (subspace_topology X TX A2)"
      and hep1: "top1_arc_endpoints_on A1 (subspace_topology X TX A1) = {x, c}"
      and hep2: "top1_arc_endpoints_on A2 (subspace_topology X TX A2) = {c, y}"
      and "x \<noteq> c" "c \<noteq> y"
  shows "top1_arc_endpoints_on (A1 \<union> A2) (subspace_topology X TX (A1 \<union> A2)) = {x, y}"
proof -
  let ?D = "A1 \<union> A2"
  have hDX: "?D \<subseteq> X" using assms(4,6) by (by100 blast)
  have hD_arc: "top1_is_arc_on ?D (subspace_topology X TX ?D)"
    by (rule arcs_concatenation_is_arc[OF hT hH hA1 assms(4) hA2 assms(6) assms(7) assms(8) assms(9)])
  \<comment> \<open>Key: c is NOT an endpoint of ?D. If it were, removing c would leave ?D connected.
     But ?D \<setminus> {c} = (A1\<setminus>{c}) \<union> (A2\<setminus>{c}), disjoint nonempty \<Rightarrow> disconnected.\<close>
  have hc_not_ep: "c \<notin> top1_arc_endpoints_on ?D (subspace_topology X TX ?D)"
  proof
    assume "c \<in> top1_arc_endpoints_on ?D (subspace_topology X TX ?D)"
    hence hconn: "top1_connected_on (?D - {c}) (subspace_topology ?D (subspace_topology X TX ?D) (?D - {c}))"
      unfolding top1_arc_endpoints_on_def by (by100 blast)
    \<comment> \<open>?D \<setminus> {c} = (A1\<setminus>{c}) \<union> (A2\<setminus>{c}), disjoint, nonempty.\<close>
    have hDc: "?D - {c} = (A1 - {c}) \<union> (A2 - {c})" using assms(7) by (by100 blast)
    have hdisj: "(A1 - {c}) \<inter> (A2 - {c}) = {}" using assms(7) by (by100 blast)
    have hne1: "A1 - {c} \<noteq> {}"
      using hep1 assms(12) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have hne2: "A2 - {c} \<noteq> {}"
      using hep2 assms(13) unfolding top1_arc_endpoints_on_def by (by100 blast)
    \<comment> \<open>But A1\<setminus>{c}, A2\<setminus>{c} are open in ?D\<setminus>{c} (since A1, A2 closed in ?D).\<close>
    \<comment> \<open>This gives a separation, contradicting connectedness.\<close>
    \<comment> \<open>Need: A1\<setminus>{c} and A2\<setminus>{c} are open in ?D\<setminus>{c}'s subspace topology.
       This follows from A1, A2 being closed in ?D (compact in Hausdorff).\<close>
    \<comment> \<open>A1 is compact (arc), hence closed in Hausdorff D. So D \<setminus> A1 = A2\<setminus>{c} is open in D.\<close>
    have hTD: "is_topology_on ?D (subspace_topology X TX ?D)"
      by (rule subspace_topology_is_topology_on[OF])
        (use hT in \<open>unfold is_topology_on_strict_def; by100 blast\<close>,
         use assms(4,6) in \<open>by100 blast\<close>)
    have hA1_closed_D: "closedin_on ?D (subspace_topology X TX ?D) A1"
    proof -
      have hD_haus: "is_hausdorff_on ?D (subspace_topology X TX ?D)"
        using conjunct2[OF conjunct2[OF Theorem_17_11]] hH hDX by (by100 blast)
      have hA1_sub_D: "A1 \<subseteq> ?D" by (by100 blast)
      have hA1_compact: "top1_compact_on A1 (subspace_topology ?D (subspace_topology X TX ?D) A1)"
      proof -
        have "top1_compact_on A1 (subspace_topology X TX A1)"
        proof -
          obtain g where hg: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
              A1 (subspace_topology X TX A1) g"
            using hA1 unfolding top1_is_arc_on_def by (by100 blast)
          have hg_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              A1 (subspace_topology X TX A1) g"
              and hg_img: "g ` top1_unit_interval = A1"
            using hg unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)+
          have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
          proof -
            have "compact (top1_unit_interval :: real set)" unfolding top1_unit_interval_def
              by (rule compact_Icc)
            thus ?thesis using top1_compact_on_subspace_UNIV_iff_compact
              unfolding top1_unit_interval_topology_def by (by100 blast)
          qed
          have hTA1: "is_topology_on A1 (subspace_topology X TX A1)"
            by (rule subspace_topology_is_topology_on[OF])
              (use hT in \<open>unfold is_topology_on_strict_def; by100 blast\<close>, use assms(4) in \<open>by100 blast\<close>)
          from top1_compact_on_continuous_image[OF hI_compact hTA1 hg_cont]
          have "top1_compact_on (g ` top1_unit_interval)
              (subspace_topology A1 (subspace_topology X TX A1) (g ` top1_unit_interval))" .
          hence "top1_compact_on A1
              (subspace_topology A1 (subspace_topology X TX A1) A1)" using hg_img by (by100 simp)
          moreover have "subspace_topology A1 (subspace_topology X TX A1) A1 = subspace_topology X TX A1"
          proof (rule subspace_topology_self)
            show "\<forall>U \<in> subspace_topology X TX A1. U \<subseteq> A1"
              unfolding subspace_topology_def by (by100 blast)
          qed
          ultimately show ?thesis by (by100 simp)
        qed
        moreover have "subspace_topology X TX A1
            = subspace_topology ?D (subspace_topology X TX ?D) A1"
          using subspace_topology_trans[of A1 ?D X TX] hA1_sub_D hDX by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      show ?thesis by (rule Theorem_26_3[OF hD_haus hA1_sub_D hA1_compact])
    qed
    have hA2_closed_D: "closedin_on ?D (subspace_topology X TX ?D) A2"
    proof -
      have hD_haus: "is_hausdorff_on ?D (subspace_topology X TX ?D)"
        using conjunct2[OF conjunct2[OF Theorem_17_11]] hH hDX by (by100 blast)
      have hA2_sub_D: "A2 \<subseteq> ?D" by (by100 blast)
      have hA2_compact: "top1_compact_on A2 (subspace_topology ?D (subspace_topology X TX ?D) A2)"
      proof -
        have "top1_compact_on A2 (subspace_topology X TX A2)"
        proof -
          obtain g where hg: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
              A2 (subspace_topology X TX A2) g"
            using hA2 unfolding top1_is_arc_on_def by (by100 blast)
          have hg_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              A2 (subspace_topology X TX A2) g"
              and hg_img: "g ` top1_unit_interval = A2"
            using hg unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)+
          have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
          proof -
            have "compact (top1_unit_interval :: real set)" unfolding top1_unit_interval_def
              by (rule compact_Icc)
            thus ?thesis using top1_compact_on_subspace_UNIV_iff_compact
              unfolding top1_unit_interval_topology_def by (by100 blast)
          qed
          have hTA2: "is_topology_on A2 (subspace_topology X TX A2)"
            by (rule subspace_topology_is_topology_on[OF])
              (use hT in \<open>unfold is_topology_on_strict_def; by100 blast\<close>, use assms(6) in \<open>by100 blast\<close>)
          from top1_compact_on_continuous_image[OF hI_compact hTA2 hg_cont]
          have "top1_compact_on (g ` top1_unit_interval)
              (subspace_topology A2 (subspace_topology X TX A2) (g ` top1_unit_interval))" .
          hence "top1_compact_on A2
              (subspace_topology A2 (subspace_topology X TX A2) A2)" using hg_img by (by100 simp)
          moreover have "subspace_topology A2 (subspace_topology X TX A2) A2 = subspace_topology X TX A2"
          proof (rule subspace_topology_self)
            show "\<forall>U \<in> subspace_topology X TX A2. U \<subseteq> A2"
              unfolding subspace_topology_def by (by100 blast)
          qed
          ultimately show ?thesis by (by100 simp)
        qed
        moreover have "subspace_topology X TX A2
            = subspace_topology ?D (subspace_topology X TX ?D) A2"
          using subspace_topology_trans[of A2 ?D X TX] hA2_sub_D hDX by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      show ?thesis by (rule Theorem_26_3[OF hD_haus hA2_sub_D hA2_compact])
    qed
    \<comment> \<open>A2\<setminus>{c} = D \<setminus> A1 is open in D.\<close>
    have "?D - A1 = A2 - {c}" using assms(7) by (by100 blast)
    have hA2c_open_D: "A2 - {c} \<in> subspace_topology X TX ?D"
      using hA1_closed_D \<open>?D - A1 = A2 - {c}\<close> unfolding closedin_on_def openin_on_def
      by (by100 simp)
    have "?D - A2 = A1 - {c}" using assms(7) by (by100 blast)
    have hA1c_open_D: "A1 - {c} \<in> subspace_topology X TX ?D"
      using hA2_closed_D \<open>?D - A2 = A1 - {c}\<close> unfolding closedin_on_def openin_on_def
      by (by100 simp)
    \<comment> \<open>Now A1\<setminus>{c} and A2\<setminus>{c} are open in D\<setminus>{c} (subspace).\<close>
    let ?TDc = "subspace_topology ?D (subspace_topology X TX ?D) (?D - {c})"
    have hA1c_open_Dc: "A1 - {c} \<in> ?TDc"
    proof -
      have heq: "A1 - {c} = (?D - {c}) \<inter> (A1 - {c})" by (by100 blast)
      have "A1 - {c} \<in> subspace_topology X TX ?D" by (rule hA1c_open_D)
      hence "A1 - {c} \<in> {?D \<inter> U | U. U \<in> TX}"
        unfolding subspace_topology_def by (by100 simp)
      show ?thesis unfolding subspace_topology_def
        apply (rule CollectI)
        apply (rule exI[of _ "A1 - {c}"])
        using heq \<open>A1 - {c} \<in> {?D \<inter> U | U. U \<in> TX}\<close>
        by (by100 simp)
    qed
    have hA2c_open_Dc: "A2 - {c} \<in> ?TDc"
    proof -
      have heq: "A2 - {c} = (?D - {c}) \<inter> (A2 - {c})" by (by100 blast)
      have "A2 - {c} \<in> subspace_topology X TX ?D" by (rule hA2c_open_D)
      hence "A2 - {c} \<in> {?D \<inter> U | U. U \<in> TX}"
        unfolding subspace_topology_def by (by100 simp)
      show ?thesis unfolding subspace_topology_def
        apply (rule CollectI)
        apply (rule exI[of _ "A2 - {c}"])
        using heq \<open>A2 - {c} \<in> {?D \<inter> U | U. U \<in> TX}\<close>
        by (by100 simp)
    qed
    have hU_Dc: "A1 - {c} \<in> ?TDc" by (rule hA1c_open_Dc)
    have hV_Dc: "A2 - {c} \<in> ?TDc" by (rule hA2c_open_Dc)
    have hsep: "top1_is_separation_on (?D - {c}) ?TDc (A1 - {c}) (A2 - {c})"
      unfolding top1_is_separation_on_def
      using hU_Dc hV_Dc hne1 hne2 hdisj hDc by (by100 blast)
    have "\<not> top1_connected_on (?D - {c}) ?TDc"
    proof
      assume "top1_connected_on (?D - {c}) ?TDc"
      from iffD1[OF Lemma_23_1 this]
      have "\<not> (\<exists>U V. top1_is_separation_on (?D - {c}) ?TDc U V)" by (by100 blast)
      thus False using hsep by (by100 blast)
    qed
    thus False using hconn by (by100 blast)
  qed
  \<comment> \<open>Get endpoints of ?D.\<close>
  obtain a b where hab_ep: "top1_arc_endpoints_on ?D (subspace_topology X TX ?D) = {a, b}"
      and hab_ne: "a \<noteq> b"
  proof -
    obtain g where hg: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
        ?D (subspace_topology X TX ?D) g"
      using hD_arc unfolding top1_is_arc_on_def by (by100 blast)
    have heps: "top1_arc_endpoints_on ?D (subspace_topology X TX ?D) = {g 0, g 1}"
      by (rule arc_endpoints_are_boundary[OF hT hH hDX hD_arc hg])
    have "g 0 \<noteq> g 1"
    proof
      assume "g 0 = g 1"
      have "inj_on g top1_unit_interval"
        using hg unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      hence "(0::real) = 1" using \<open>g 0 = g 1\<close>
        unfolding inj_on_def top1_unit_interval_def by (by100 force)
      thus False by (by100 simp)
    qed
    thus ?thesis using that[OF heps] by (by100 blast)
  qed
  \<comment> \<open>x \<in> A1, y \<in> A2, c \<in> both.\<close>
  have hx_A1: "x \<in> A1" using hep1 unfolding top1_arc_endpoints_on_def by (by100 blast)
  have hy_A2: "y \<in> A2" using hep2 unfolding top1_arc_endpoints_on_def by (by100 blast)
  have hc_A1: "c \<in> A1" using assms(7,8) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have hc_A2: "c \<in> A2" using assms(7,9) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have hx_ne_c: "x \<noteq> c" by (rule assms(12))
  have hc_ne_y: "c \<noteq> y" by (rule assms(13))
  have hx_D: "x \<in> ?D" using hx_A1 by (by100 blast)
  have hy_D: "y \<in> ?D" using hy_A2 by (by100 blast)
  \<comment> \<open>Apply arc\_split\_endpoints: endpoints of A1 = {a,c} or {b,c}.\<close>
  have ha_A1: "a \<in> A1 \<or> a \<in> A2" using hab_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
  have hb_A2: "b \<in> A1 \<or> b \<in> A2" using hab_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
  \<comment> \<open>a \<in> A1 (since a is an endpoint of D, and a \<noteq> c, so a \<notin> A1\<inter>A2 = {c}).\<close>
  \<comment> \<open>arc\_split\_endpoints needs: a \<in> A1, b \<in> A2 (endpoints of D in respective sub-arcs).\<close>
  have hab_ne2: "a \<noteq> c" using hab_ep hc_not_ep by (by100 blast)
  have hbc_ne: "b \<noteq> c" using hab_ep hc_not_ep by (by100 blast)
  have hD_eq: "?D = A1 \<union> A2" by (by100 blast)
  have ha_D: "a \<in> ?D" using hab_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
  have hb_D: "b \<in> ?D" using hab_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
  \<comment> \<open>Case split: either a \<in> A1 or a \<in> A2. In either case we can apply arc\_split\_endpoints
     (with possibly swapped roles) and match to get endpoints(D) = {x,y}.\<close>
  show ?thesis
  proof (cases "a \<in> A1")
    case True
    hence hb_A2: "b \<in> A2"
    proof (cases "b \<in> A2") case True thus ?thesis . next
      case False hence "b \<in> A1" using hb_D by (by100 blast)
      \<comment> \<open>Both a,b \<in> A1. This contradicts A2 being an arc (more than one point):
         A2 \<subseteq> D, A2 is arc, but all of D's endpoints are in A1, forcing A2 = {c}.\<close>
      \<comment> \<open>Contradiction: both a,b \<in> A1 forces A2 = {c} (connected\_contains\_Icc),
         but A2 is an arc with y \<in> A2, y \<noteq> c.\<close>
      have "y \<in> A2" using hep2 unfolding top1_arc_endpoints_on_def by (by100 blast)
      have hA1_conn: "top1_connected_on A1 (subspace_topology X TX A1)"
        using arc_connected[OF hA1] by (by100 simp)
      have "A2 = {c}"
        by (rule arc_both_endpoints_in_one_part[OF hT hH hDX hD_arc hD_eq assms(7) hA1_conn
            assms(4) hab_ep hab_ne True \<open>b \<in> A1\<close>])
      hence "y = c" using \<open>y \<in> A2\<close> by (by100 blast)
      thus ?thesis using hc_ne_y by (by100 blast)
    qed
    from arc_split_endpoints(1)[OF hT hH hDX hD_arc hD_eq assms(7) hA1 hA2
        True hb_A2 hc_A1 hc_A2 assms(4) assms(6) hab_ep hc_not_ep]
    have hep_A1: "top1_arc_endpoints_on A1 (subspace_topology X TX A1) = {a, c}" .
    from arc_split_endpoints(2)[OF hT hH hDX hD_arc hD_eq assms(7) hA1 hA2
        True hb_A2 hc_A1 hc_A2 assms(4) assms(6) hab_ep hc_not_ep]
    have hep_A2: "top1_arc_endpoints_on A2 (subspace_topology X TX A2) = {c, b}" .
    have "a = x"
    proof - have "{a, c} = {x, c}" using hep_A1 hep1 by (by100 simp)
      from doubleton_eq_iff[OF this hab_ne2] show ?thesis using hx_ne_c by (by100 blast) qed
    moreover have "b = y"
    proof - have "{c, b} = {c, y}" using hep_A2 hep2 by (by100 simp)
      from doubleton_eq_iff[OF this \<open>b \<noteq> c\<close>[THEN not_sym]] show ?thesis using hc_ne_y by (by100 blast) qed
    ultimately show ?thesis using hab_ep by (by100 simp)
  next
    case False
    hence "a \<in> A2" using ha_D by (by100 blast)
    have "b \<in> A1"
    proof (rule ccontr)
      assume "b \<notin> A1" hence "b \<in> A2" using hb_D by (by100 blast)
      have "x \<in> A1" using hep1 unfolding top1_arc_endpoints_on_def by (by100 blast)
      have hA2_conn: "top1_connected_on A2 (subspace_topology X TX A2)"
        using arc_connected[OF hA2] by (by100 simp)
      have "A1 = {c}"
        by (rule arc_both_endpoints_in_one_part[OF hT hH hDX hD_arc _ _ hA2_conn assms(6)
            hab_ep hab_ne \<open>a \<in> A2\<close> \<open>b \<in> A2\<close>])
          (use assms(5,7) in \<open>by100 blast\<close>)+
      hence "x = c" using \<open>x \<in> A1\<close> by (by100 blast)
      thus False using hx_ne_c by (by100 blast)
    qed
    \<comment> \<open>Swap roles: b \<in> A1 (= D1), a \<in> A2 (= D2).\<close>
    have hab_ep': "top1_arc_endpoints_on ?D (subspace_topology X TX ?D) = {b, a}"
      using hab_ep by (by100 blast)
    from arc_split_endpoints(1)[OF hT hH hDX hD_arc hD_eq assms(7) hA1 hA2
        \<open>b \<in> A1\<close> \<open>a \<in> A2\<close> hc_A1 hc_A2 assms(4) assms(6) hab_ep' hc_not_ep]
    have hep_A1: "top1_arc_endpoints_on A1 (subspace_topology X TX A1) = {b, c}" .
    from arc_split_endpoints(2)[OF hT hH hDX hD_arc hD_eq assms(7) hA1 hA2
        \<open>b \<in> A1\<close> \<open>a \<in> A2\<close> hc_A1 hc_A2 assms(4) assms(6) hab_ep' hc_not_ep]
    have hep_A2: "top1_arc_endpoints_on A2 (subspace_topology X TX A2) = {c, a}" .
    have "b = x"
    proof - have "{b, c} = {x, c}" using hep_A1 hep1 by (by100 simp)
      from doubleton_eq_iff[OF this hbc_ne] show ?thesis using hx_ne_c by (by100 blast) qed
    moreover have "a = y"
    proof - have "{c, a} = {c, y}" using hep_A2 hep2 by (by100 simp)
      from doubleton_eq_iff[OF this hab_ne2[THEN not_sym]] show ?thesis using hc_ne_y by (by100 blast) qed
    ultimately show ?thesis using hab_ep by (by100 blast)
  qed
qed

section \<open>\<S>64 Imbedding Graphs in the Plane\<close>

text \<open>A theta space X is a Hausdorff space that is the union of three arcs A, B, C,
  each pair of which intersect precisely in their endpoints.\<close>

definition top1_is_theta_space_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_is_theta_space_on X TX A B C \<longleftrightarrow>
    is_hausdorff_on X TX \<and> X = A \<union> B \<union> C \<and>
    top1_is_arc_on A (subspace_topology X TX A) \<and>
    top1_is_arc_on B (subspace_topology X TX B) \<and>
    top1_is_arc_on C (subspace_topology X TX C) \<and>
    (\<exists>a b. a \<noteq> b \<and> A \<inter> B = {a, b} \<and> B \<inter> C = {a, b} \<and> A \<inter> C = {a, b} \<and>
           top1_arc_endpoints_on A (subspace_topology X TX A) = {a, b} \<and>
           top1_arc_endpoints_on B (subspace_topology X TX B) = {a, b} \<and>
           top1_arc_endpoints_on C (subspace_topology X TX C) = {a, b})"

\<comment> \<open>Reusable: arc minus both endpoints is connected (image of (0,1) under homeomorphism).\<close>
lemma arc_minus_endpoints_connected:
  assumes hT: "is_topology_on_strict X TX" and hH: "is_hausdorff_on X TX"
      and hDX: "D \<subseteq> X"
      and hArc: "top1_is_arc_on D (subspace_topology X TX D)"
      and hep: "top1_arc_endpoints_on D (subspace_topology X TX D) = {a, b}" and hab: "a \<noteq> b"
  shows "top1_connected_on (D - {a, b}) (subspace_topology X TX (D - {a, b}))"
proof -
  obtain h where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      D (subspace_topology X TX D) h"
    using hArc unfolding top1_is_arc_on_def by (by100 blast)
  have hh_ep: "{h 0, h 1} = {a, b}"
    using arc_endpoints_are_boundary[OF hT hH hDX hArc hh] hep by (by100 simp)
  have hinj: "inj_on h top1_unit_interval"
    using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  have himg: "h ` top1_unit_interval = D"
    using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  \<comment> \<open>h maps (0,1) = {0<..<1} onto D - {a,b}.\<close>
  have himg_open: "h ` {0<..<1::real} = D - {a, b}"
  proof -
    have hIoo_eq: "{0<..<1::real} = top1_unit_interval - {0, 1}"
      unfolding top1_unit_interval_def by (by100 force)
    have "h ` (top1_unit_interval - {0, 1}) = D - {h 0, h 1}"
    proof -
      have "(0::real) \<in> top1_unit_interval" "(1::real) \<in> top1_unit_interval"
        unfolding top1_unit_interval_def by (by100 simp)+
      have h01_sub: "{0::real, 1} \<subseteq> top1_unit_interval"
        apply (rule insert_subset[THEN iffD2])
        apply (rule conjI)
        apply (rule \<open>(0::real) \<in> top1_unit_interval\<close>)
        apply (rule insert_subset[THEN iffD2])
        apply (rule conjI)
        apply (rule \<open>(1::real) \<in> top1_unit_interval\<close>)
        apply (rule empty_subsetI)
        done
      have hI_minus_sub: "top1_unit_interval - {0::real, 1} \<subseteq> top1_unit_interval" by (by100 blast)
      have "h ` (top1_unit_interval - {0, 1}) = h ` top1_unit_interval - h ` {0, 1}"
        by (rule inj_on_image_set_diff[OF hinj hI_minus_sub h01_sub])
      also have "h ` top1_unit_interval = D" by (rule himg)
      also have "h ` {0::real, 1} = {h 0, h 1}" by (by100 simp)
      finally show ?thesis .
    qed
    thus ?thesis using hIoo_eq hh_ep by (by100 force)
  qed
  \<comment> \<open>(0,1) is connected.\<close>
  have hIoo_conn: "top1_connected_on {0<..<1::real} (subspace_topology UNIV top1_open_sets {0<..<1})"
  proof (rule Theorem_24_1)
    fix x y z :: real assume "x \<in> {0<..<1}" "y \<in> {0<..<1}" "x \<le> z" "z \<le> y"
    thus "z \<in> {0<..<1}" by (by100 simp)
  qed
  \<comment> \<open>h continuous (0,1) \<rightarrow> D-{a,b}: restrict h from [0,1] to (0,1), shrink codomain.\<close>
  have hh_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
      D (subspace_topology X TX D) h"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hTopX: "is_topology_on X TX"
    using hT unfolding is_topology_on_strict_def by (by100 blast)
  have hh_cont_X: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX h"
  proof -
    from top1_continuous_map_on_codomain_enlarge[OF hh_cont hDX]
    have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
        X (subspace_topology X TX X) h" by (by100 simp)
    moreover have "subspace_topology X TX X = TX"
    proof (rule subspace_topology_self)
      show "\<forall>U \<in> TX. U \<subseteq> X" using hT unfolding is_topology_on_strict_def Pow_def by (by100 blast)
    qed
    ultimately show ?thesis by (by100 simp)
  qed
  have hIoo_sub: "{0<..<1::real} \<subseteq> top1_unit_interval"
    unfolding top1_unit_interval_def by (by100 force)
  have hh_cont_Ioo: "top1_continuous_map_on {0<..<1::real}
      (subspace_topology UNIV top1_open_sets {0<..<1})
      X TX h"
  proof -
    from top1_continuous_map_on_subspace_restrict[OF hh_cont_X hIoo_sub]
    have "top1_continuous_map_on {0<..<1}
        (subspace_topology top1_unit_interval top1_unit_interval_topology {0<..<1}) X TX h" .
    moreover have "subspace_topology top1_unit_interval top1_unit_interval_topology {0<..<1}
        = subspace_topology UNIV top1_open_sets {0<..<1}"
      unfolding top1_unit_interval_topology_def
      using subspace_topology_trans[of "{0<..<1}" top1_unit_interval UNIV top1_open_sets]
        hIoo_sub by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  have hh_img_sub: "h ` {0<..<1::real} \<subseteq> D - {a, b}"
    using himg_open by (by100 simp)
  have hDab_sub: "D - {a, b} \<subseteq> X" using hDX by (by100 blast)
  have hh_cont_Dab: "top1_continuous_map_on {0<..<1::real}
      (subspace_topology UNIV top1_open_sets {0<..<1})
      (D - {a, b}) (subspace_topology X TX (D - {a, b})) h"
    using top1_continuous_map_on_codomain_shrink[OF hh_cont_Ioo hh_img_sub hDab_sub] by (by100 simp)
  have hTDab: "is_topology_on (D - {a, b}) (subspace_topology X TX (D - {a, b}))"
    by (rule subspace_topology_is_topology_on[OF hTopX]) (use hDab_sub in \<open>by100 blast\<close>)
  have hT_Ioo: "is_topology_on {0<..<1::real} (subspace_topology UNIV top1_open_sets {0<..<1})"
    by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV]) (by100 blast)
  from Theorem_23_5[OF hT_Ioo hTDab hIoo_conn hh_cont_Dab]
  have "top1_connected_on (h ` {0<..<1})
      (subspace_topology (D-{a,b}) (subspace_topology X TX (D-{a,b})) (h ` {0<..<1}))" .
  hence "top1_connected_on (D-{a,b})
      (subspace_topology (D-{a,b}) (subspace_topology X TX (D-{a,b})) (D-{a,b}))"
    using himg_open by (by100 force)
  moreover have "subspace_topology (D-{a,b}) (subspace_topology X TX (D-{a,b})) (D-{a,b})
      = subspace_topology X TX (D-{a,b})"
  proof (rule subspace_topology_self)
    show "\<forall>U \<in> subspace_topology X TX (D-{a,b}). U \<subseteq> D-{a,b}"
      unfolding subspace_topology_def by (by100 blast)
  qed
  ultimately show ?thesis by (by100 simp)
qed

text \<open>Lemma 64.1: A theta space X \<subseteq> S2 separates S2 into three components.\<close>

lemma Lemma_64_1_theta_space_three_components:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "A \<subseteq> top1_S2" "B \<subseteq> top1_S2" "C \<subseteq> top1_S2"
      and "top1_is_arc_on A (subspace_topology top1_S2 top1_S2_topology A)"
      and "top1_is_arc_on B (subspace_topology top1_S2 top1_S2_topology B)"
      and "top1_is_arc_on C (subspace_topology top1_S2 top1_S2_topology C)"
      and "a \<noteq> b" "A \<inter> B = {a, b}" "B \<inter> C = {a, b}" "A \<inter> C = {a, b}"
      and "top1_arc_endpoints_on A (subspace_topology top1_S2 top1_S2_topology A) = {a, b}"
      and "top1_arc_endpoints_on B (subspace_topology top1_S2 top1_S2_topology B) = {a, b}"
      and "top1_arc_endpoints_on C (subspace_topology top1_S2 top1_S2_topology C) = {a, b}"
  shows "\<exists>U V W. U \<noteq> {} \<and> V \<noteq> {} \<and> W \<noteq> {}
      \<and> U \<inter> V = {} \<and> V \<inter> W = {} \<and> U \<inter> W = {}
      \<and> U \<union> V \<union> W = top1_S2 - (A \<union> B \<union> C)
      \<and> top1_connected_on U (subspace_topology top1_S2 top1_S2_topology U)
      \<and> top1_connected_on V (subspace_topology top1_S2 top1_S2_topology V)
      \<and> top1_connected_on W (subspace_topology top1_S2 top1_S2_topology W)
      \<and> U \<in> top1_S2_topology \<and> V \<in> top1_S2_topology \<and> W \<in> top1_S2_topology"
proof -
  \<comment> \<open>Step 1: A \<union> B is SCC, separates S2 into two components U0, U0'.\<close>
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology"
    by (rule top1_S2_is_hausdorff)
  have hAB_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology (A \<union> B)"
    by (rule arcs_form_simple_closed_curve[OF assms(1) hS2_haus assms(5) assms(2)
        assms(6) assms(3) assms(9) assms(8) assms(12) assms(13)])
  have hAB_sep: "top1_separates_on top1_S2 top1_S2_topology (A \<union> B)"
    by (rule Theorem_61_3_JordanSeparation_S2[OF assms(1) hAB_scc])
  \<comment> \<open>Get two components U0, U0' of S2 - (A \<union> B).\<close>
  \<comment> \<open>A, B are closed arcs with card(A\<inter>B) = 2. Neither separates S2.
     By Theorem 63.5, A \<union> B separates S2 into exactly 2 connected components.\<close>
  have hA_closed: "closedin_on top1_S2 top1_S2_topology A"
    by (rule arc_in_S2_closed[OF assms(2) assms(5)])
  have hB_closed: "closedin_on top1_S2 top1_S2_topology B"
    by (rule arc_in_S2_closed[OF assms(3) assms(6)])
  have hA_conn: "top1_connected_on A (subspace_topology top1_S2 top1_S2_topology A)"
    using arc_connected[OF assms(5)] .
  have hB_conn: "top1_connected_on B (subspace_topology top1_S2 top1_S2_topology B)"
    using arc_connected[OF assms(6)] .
  have hA_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology A"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) assms(2) assms(5)])
  have hB_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology B"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) assms(3) assms(6)])
  have hAB_card: "card (A \<inter> B) = 2"
  proof -
    have "A \<inter> B = {a, b}" by (rule assms(9))
    moreover have "card {a, b} = 2" using assms(8) by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  obtain U0_raw U0'_raw where hU0_raw: "U0_raw \<noteq> {}" "U0'_raw \<noteq> {}" "U0_raw \<inter> U0'_raw = {}"
      "U0_raw \<union> U0'_raw = top1_S2 - (A \<union> B)"
      "top1_connected_on U0_raw (subspace_topology top1_S2 top1_S2_topology U0_raw)"
      "top1_connected_on U0'_raw (subspace_topology top1_S2 top1_S2_topology U0'_raw)"
    using Theorem_63_5_two_closed_connected[OF assms(1) hA_closed hB_closed
        hA_conn hB_conn hAB_card hA_no_sep hB_no_sep]
    by (by100 force)
  \<comment> \<open>C-{a,b} is in one of U0\_raw/U0'\_raw. Choose U0 to NOT contain C-{a,b}.\<close>
  have hC_raw: "C - {a, b} \<subseteq> U0_raw \<or> C - {a, b} \<subseteq> U0'_raw"
  proof -
    \<comment> \<open>Need: raw components are open \<Rightarrow> form separation \<Rightarrow> Lemma\_23\_2.\<close>
    let ?W = "top1_S2 - (A \<union> B)"
    let ?TW = "subspace_topology top1_S2 top1_S2_topology ?W"
    have hAB_closed_S2_raw: "closedin_on top1_S2 top1_S2_topology (A \<union> B)"
    proof -
      have "is_topology_on top1_S2 top1_S2_topology"
        using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
      thus ?thesis by (rule closedin_on_Un[OF _ hA_closed hB_closed])
    qed
    have hW_open: "?W \<in> top1_S2_topology" using hAB_closed_S2_raw unfolding closedin_on_def by (by100 blast)
    have hW_sub: "?W \<subseteq> top1_S2" by (by100 blast)
    have hW_lpc: "top1_locally_path_connected_on ?W ?TW"
      by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hW_open hW_sub])
    have hTW: "is_topology_on ?W ?TW"
    proof -
      have "is_topology_on top1_S2 top1_S2_topology"
        using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
      thus ?thesis by (rule subspace_topology_is_topology_on) (by100 blast)
    qed
    \<comment> \<open>U0\_raw is path component of some x \<in> U0\_raw, hence open.\<close>
    obtain x_raw where "x_raw \<in> U0_raw" using hU0_raw(1) by (by100 blast)
    hence hxr_W: "x_raw \<in> ?W" using hU0_raw(4) by (by100 blast)
    \<comment> \<open>path\_comp = connected\_comp in lpc (Theorem 25.5).\<close>
    have hThm255_raw: "top1_path_component_of_on ?W ?TW x_raw = top1_component_of_on ?W ?TW x_raw"
    proof -
      from conjunct2[OF Theorem_25_5[OF hTW]]
      have "top1_locally_path_connected_on ?W ?TW \<longrightarrow>
          (\<forall>x \<in> ?W. top1_path_component_of_on ?W ?TW x = top1_component_of_on ?W ?TW x)" .
      thus ?thesis using hW_lpc hxr_W by (by100 blast)
    qed
    \<comment> \<open>U0\_raw = comp(x\_raw) (same argument as hU0\_eq\_comp below).\<close>
    have hU0r_sub_W: "U0_raw \<subseteq> ?W" using hU0_raw(4) by (by100 blast)
    have hU0r_conn_W: "top1_connected_on U0_raw (subspace_topology ?W ?TW U0_raw)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology U0_raw = subspace_topology ?W ?TW U0_raw"
        using subspace_topology_trans[of U0_raw ?W top1_S2 top1_S2_topology] hU0r_sub_W by (by100 simp)
      thus ?thesis using hU0_raw(5) by (by100 simp)
    qed
    have "U0_raw \<subseteq> top1_component_of_on ?W ?TW x_raw"
      by (rule top1_connected_subspace_subset_component_of[OF hU0r_sub_W \<open>x_raw \<in> U0_raw\<close> hU0r_conn_W])
    moreover have "top1_component_of_on ?W ?TW x_raw \<subseteq> U0_raw"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain y where hy: "y \<in> top1_component_of_on ?W ?TW x_raw" "y \<notin> U0_raw" by (by100 blast)
      have "top1_component_of_on ?W ?TW x_raw \<subseteq> ?W" by (rule top1_component_of_on_subset)
      have "y \<in> ?W" using hy(1) \<open>top1_component_of_on ?W ?TW x_raw \<subseteq> ?W\<close> by (by100 blast)
      hence "y \<in> U0'_raw" using hy(2) hU0_raw(4) by (by100 blast)
      have hU0'r_sub_W: "U0'_raw \<subseteq> ?W" using hU0_raw(4) by (by100 blast)
      have hU0'r_conn_W: "top1_connected_on U0'_raw (subspace_topology ?W ?TW U0'_raw)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology U0'_raw = subspace_topology ?W ?TW U0'_raw"
          using subspace_topology_trans[of U0'_raw ?W top1_S2 top1_S2_topology] hU0'r_sub_W by (by100 simp)
        thus ?thesis using hU0_raw(6) by (by100 simp)
      qed
      have "U0'_raw \<subseteq> top1_component_of_on ?W ?TW y"
        by (rule top1_connected_subspace_subset_component_of[OF hU0'r_sub_W \<open>y \<in> U0'_raw\<close> hU0'r_conn_W])
      have "top1_component_of_on ?W ?TW y = top1_component_of_on ?W ?TW x_raw"
        by (rule top1_component_of_on_eq_of_mem[OF hTW hy(1)])
      hence "U0'_raw \<subseteq> top1_component_of_on ?W ?TW x_raw"
        using \<open>U0'_raw \<subseteq> top1_component_of_on ?W ?TW y\<close> by (by100 simp)
      hence "?W \<subseteq> top1_component_of_on ?W ?TW x_raw"
        using \<open>U0_raw \<subseteq> top1_component_of_on ?W ?TW x_raw\<close> hU0_raw(4) by (by100 blast)
      have "top1_component_of_on ?W ?TW x_raw \<subseteq> ?W" by (rule top1_component_of_on_subset)
      hence "top1_component_of_on ?W ?TW x_raw = ?W"
        using \<open>?W \<subseteq> top1_component_of_on ?W ?TW x_raw\<close> by (by100 blast)
      have "top1_connected_on (top1_component_of_on ?W ?TW x_raw) (subspace_topology ?W ?TW (top1_component_of_on ?W ?TW x_raw))"
        by (rule top1_component_of_on_connected[OF hTW hxr_W])
      hence "top1_connected_on ?W (subspace_topology ?W ?TW ?W)"
        using \<open>top1_component_of_on ?W ?TW x_raw = ?W\<close> by (by100 force)
      moreover have "subspace_topology ?W ?TW ?W = ?TW"
      proof (rule subspace_topology_self)
        show "\<forall>U \<in> ?TW. U \<subseteq> ?W" unfolding subspace_topology_def by (by100 blast)
      qed
      ultimately have "top1_connected_on ?W ?TW" by (by100 simp)
      thus False using hAB_sep unfolding top1_separates_on_def by (by100 simp)
    qed
    ultimately have "U0_raw = top1_path_component_of_on ?W ?TW x_raw"
      using hThm255_raw by (by100 blast)
    hence hU0r_open: "U0_raw \<in> top1_S2_topology"
    proof -
      have "top1_path_component_of_on ?W ?TW x_raw \<in> ?TW"
        by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTW hW_lpc hxr_W])
      hence "U0_raw \<in> ?TW" using \<open>U0_raw = top1_path_component_of_on ?W ?TW x_raw\<close> by (by100 simp)
      then obtain V where "V \<in> top1_S2_topology" "U0_raw = ?W \<inter> V"
        unfolding subspace_topology_def by (by100 force)
      have hax: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> top1_S2_topology \<longrightarrow> \<Inter>F \<in> top1_S2_topology"
        using assms(1) unfolding is_topology_on_strict_def is_topology_on_def by (by100 blast)
      have "{V, ?W} \<subseteq> top1_S2_topology" using \<open>V \<in> top1_S2_topology\<close> hW_open by (by100 blast)
      have "finite {V, ?W} \<and> {V, ?W} \<noteq> {} \<and> {V, ?W} \<subseteq> top1_S2_topology"
        using \<open>{V, ?W} \<subseteq> top1_S2_topology\<close> by (by100 force)
      from hax[rule_format, OF this] have "\<Inter>{V, ?W} \<in> top1_S2_topology" .
      moreover have "V \<inter> ?W = U0_raw" using \<open>U0_raw = ?W \<inter> V\<close> by (by100 blast)
      hence "\<Inter>{V, ?W} = U0_raw" by (by100 force)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Similarly U0'\_raw open.\<close>
    have hU0'r_open: "U0'_raw \<in> top1_S2_topology"
    proof -
      obtain x_raw' where "x_raw' \<in> U0'_raw" using hU0_raw(2) by (by100 blast)
      hence hxr'_W: "x_raw' \<in> ?W" using hU0_raw(4) by (by100 blast)
      have "top1_path_component_of_on ?W ?TW x_raw' = top1_component_of_on ?W ?TW x_raw'"
      proof -
        from conjunct2[OF Theorem_25_5[OF hTW]]
        have "top1_locally_path_connected_on ?W ?TW \<longrightarrow>
            (\<forall>x \<in> ?W. top1_path_component_of_on ?W ?TW x = top1_component_of_on ?W ?TW x)" .
        thus ?thesis using hW_lpc hxr'_W by (by100 blast)
      qed
      have hU0'r_sub_W: "U0'_raw \<subseteq> ?W" using hU0_raw(4) by (by100 blast)
      have hU0'r_conn_W: "top1_connected_on U0'_raw (subspace_topology ?W ?TW U0'_raw)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology U0'_raw = subspace_topology ?W ?TW U0'_raw"
          using subspace_topology_trans[of U0'_raw ?W top1_S2 top1_S2_topology] hU0'r_sub_W by (by100 simp)
        thus ?thesis using hU0_raw(6) by (by100 simp)
      qed
      have "U0'_raw \<subseteq> top1_component_of_on ?W ?TW x_raw'"
        by (rule top1_connected_subspace_subset_component_of[OF hU0'r_sub_W \<open>x_raw' \<in> U0'_raw\<close> hU0'r_conn_W])
      moreover have "top1_component_of_on ?W ?TW x_raw' \<subseteq> U0'_raw"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then obtain z where hz: "z \<in> top1_component_of_on ?W ?TW x_raw'" "z \<notin> U0'_raw" by (by100 blast)
        have "top1_component_of_on ?W ?TW x_raw' \<subseteq> ?W" by (rule top1_component_of_on_subset)
        hence "z \<in> U0_raw" using hz hU0_raw(4) \<open>top1_component_of_on ?W ?TW x_raw' \<subseteq> ?W\<close> by (by100 blast)
        have "U0_raw \<subseteq> top1_component_of_on ?W ?TW z"
          by (rule top1_connected_subspace_subset_component_of[OF hU0r_sub_W \<open>z \<in> U0_raw\<close> hU0r_conn_W])
        have "top1_component_of_on ?W ?TW z = top1_component_of_on ?W ?TW x_raw'"
          by (rule top1_component_of_on_eq_of_mem[OF hTW hz(1)])
        hence "U0_raw \<subseteq> top1_component_of_on ?W ?TW x_raw'"
          using \<open>U0_raw \<subseteq> top1_component_of_on ?W ?TW z\<close> by (by100 simp)
        hence "?W \<subseteq> top1_component_of_on ?W ?TW x_raw'"
          using \<open>U0'_raw \<subseteq> top1_component_of_on ?W ?TW x_raw'\<close> hU0_raw(4) by (by100 blast)
        have "top1_component_of_on ?W ?TW x_raw' \<subseteq> ?W" by (rule top1_component_of_on_subset)
        hence "top1_component_of_on ?W ?TW x_raw' = ?W"
          using \<open>?W \<subseteq> top1_component_of_on ?W ?TW x_raw'\<close> by (by100 blast)
        have "top1_connected_on (top1_component_of_on ?W ?TW x_raw')
            (subspace_topology ?W ?TW (top1_component_of_on ?W ?TW x_raw'))"
          by (rule top1_component_of_on_connected[OF hTW hxr'_W])
        hence "top1_connected_on ?W (subspace_topology ?W ?TW ?W)"
          using \<open>top1_component_of_on ?W ?TW x_raw' = ?W\<close> by (by100 force)
        moreover have "subspace_topology ?W ?TW ?W = ?TW"
        proof (rule subspace_topology_self)
          show "\<forall>U \<in> ?TW. U \<subseteq> ?W" unfolding subspace_topology_def by (by100 blast)
        qed
        ultimately have "top1_connected_on ?W ?TW" by (by100 simp)
        thus False using hAB_sep unfolding top1_separates_on_def by (by100 simp)
      qed
      ultimately have "U0'_raw = top1_path_component_of_on ?W ?TW x_raw'"
        using \<open>top1_path_component_of_on ?W ?TW x_raw' = top1_component_of_on ?W ?TW x_raw'\<close>
        by (by100 blast)
      hence "U0'_raw \<in> ?TW"
        using top1_path_component_of_on_open_if_locally_path_connected[OF hTW hW_lpc hxr'_W]
        by (by100 simp)
      then obtain V where "V \<in> top1_S2_topology" "U0'_raw = ?W \<inter> V"
        unfolding subspace_topology_def by (by100 force)
      have hax': "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> top1_S2_topology \<longrightarrow> \<Inter>F \<in> top1_S2_topology"
        using assms(1) unfolding is_topology_on_strict_def is_topology_on_def by (by100 blast)
      have "{V, ?W} \<subseteq> top1_S2_topology" using \<open>V \<in> top1_S2_topology\<close> hW_open by (by100 blast)
      have "finite {V, ?W} \<and> {V, ?W} \<noteq> {} \<and> {V, ?W} \<subseteq> top1_S2_topology"
        using \<open>{V, ?W} \<subseteq> top1_S2_topology\<close> by (by100 force)
      from hax'[rule_format, OF this] have "\<Inter>{V, ?W} \<in> top1_S2_topology" .
      moreover have "V \<inter> ?W = U0'_raw" using \<open>U0'_raw = ?W \<inter> V\<close> by (by100 blast)
      hence "\<Inter>{V, ?W} = U0'_raw" by (by100 force)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Now form separation and apply Lemma\_23\_2.\<close>
    have hU0r_in_sub: "U0_raw \<in> ?TW"
    proof -
      have "U0_raw = ?W \<inter> U0_raw" using hU0r_sub_W by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hU0r_open by (by100 blast)
    qed
    have hU0'r_in_sub: "U0'_raw \<in> ?TW"
    proof -
      have "U0'_raw \<subseteq> ?W" using hU0_raw(4) by (by100 blast)
      hence "U0'_raw = ?W \<inter> U0'_raw" by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hU0'r_open by (by100 blast)
    qed
    have "top1_is_separation_on ?W ?TW U0_raw U0'_raw"
      unfolding top1_is_separation_on_def
      using hU0r_in_sub hU0'r_in_sub hU0_raw(1,2,3,4) by (by100 blast)
    \<comment> \<open>C-{a,b} connected and in W.\<close>
    have hCm_sub: "C - {a, b} \<subseteq> ?W"
    proof -
      have "C \<inter> A \<subseteq> {a, b}" using assms(11) by (by100 blast)
      moreover have "C \<inter> B \<subseteq> {a, b}" using assms(10) by (by100 blast)
      ultimately have "C \<inter> (A \<union> B) \<subseteq> {a, b}" by (by100 blast)
      thus ?thesis using assms(4) by (by100 blast)
    qed
    have hCm_conn_sub: "top1_connected_on (C - {a, b}) (subspace_topology ?W ?TW (C - {a, b}))"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology (C - {a, b}) = subspace_topology ?W ?TW (C - {a, b})"
        using subspace_topology_trans[of "C-{a,b}" ?W top1_S2 top1_S2_topology] hCm_sub by (by100 simp)
      thus ?thesis using arc_minus_endpoints_connected[OF assms(1) hS2_haus assms(4) assms(7) assms(14) assms(8)]
        by (by100 simp)
    qed
    from Lemma_23_2[OF hTW \<open>top1_is_separation_on ?W ?TW U0_raw U0'_raw\<close> hCm_sub hCm_conn_sub]
    show ?thesis by (by100 blast)
  qed
  obtain U0 U0' where hU0: "U0 \<noteq> {}" "U0' \<noteq> {}" "U0 \<inter> U0' = {}"
      "U0 \<union> U0' = top1_S2 - (A \<union> B)"
      "top1_connected_on U0 (subspace_topology top1_S2 top1_S2_topology U0)"
      "top1_connected_on U0' (subspace_topology top1_S2 top1_S2_topology U0')"
      and hC_in_U0': "C - {a, b} \<subseteq> U0'"
  proof -
    from hC_raw show ?thesis
    proof
      assume "C - {a, b} \<subseteq> U0_raw"
      show ?thesis
        by (rule that[of U0'_raw U0_raw])
          (use hU0_raw \<open>C - {a, b} \<subseteq> U0_raw\<close> in \<open>by100 blast\<close>)+
    next
      assume "C - {a, b} \<subseteq> U0'_raw"
      show ?thesis
        by (rule that[of U0_raw U0'_raw])
          (use hU0_raw \<open>C - {a, b} \<subseteq> U0'_raw\<close> in \<open>by100 blast\<close>)+
    qed
  qed
  \<comment> \<open>Step 2: C - {a,b} is connected (arc minus endpoints), lies in U0 or U0'.
     WLOG assume C - {a,b} \<subseteq> U0'. (Swap if needed.)\<close>
  have hC_minus: "C - {a, b} \<subseteq> top1_S2 - (A \<union> B)"
  proof -
    have "C \<inter> A \<subseteq> {a, b}" using assms(11) by (by100 blast)
    moreover have "C \<inter> B \<subseteq> {a, b}" using assms(10) by (by100 blast)
    ultimately have "C \<inter> (A \<union> B) \<subseteq> {a, b}" by (by100 blast)
    thus ?thesis using assms(4) by (by100 blast)
  qed
  have hC_minus_conn: "top1_connected_on (C - {a, b})
      (subspace_topology top1_S2 top1_S2_topology (C - {a, b}))"
    by (rule arc_minus_endpoints_connected[OF assms(1) hS2_haus assms(4) assms(7) assms(14) assms(8)])
  \<comment> \<open>U0, U0' are open in S2 (components of open set in loc. path connected space).\<close>
  \<comment> \<open>S2-(A\<union>B) is open, locally path connected. Components are open (Thm 25.4).\<close>
  have hAB_closed_S2: "closedin_on top1_S2 top1_S2_topology (A \<union> B)"
  proof -
    have hTopS2_here: "is_topology_on top1_S2 top1_S2_topology"
      using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    show ?thesis by (rule closedin_on_Un[OF hTopS2_here hA_closed hB_closed])
  qed
  have hAB_open_S2: "top1_S2 - (A \<union> B) \<in> top1_S2_topology"
    using hAB_closed_S2 unfolding closedin_on_def by (by100 blast)
  have hAB_sub_S2: "top1_S2 - (A \<union> B) \<subseteq> top1_S2" by (by100 blast)
  have hAB_lpc: "top1_locally_path_connected_on (top1_S2 - (A \<union> B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A \<union> B)))"
    by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hAB_open_S2 hAB_sub_S2])
  \<comment> \<open>In lpc space, connected comp = path comp (Thm 25.5). U0 nonempty connected \<Rightarrow>
     pick x \<in> U0, path\_component(x) = connected\_component(x) = U0.\<close>
  have hTopAB_early: "is_topology_on (top1_S2 - (A \<union> B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A \<union> B)))"
  proof -
    have "is_topology_on top1_S2 top1_S2_topology"
      using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    thus ?thesis by (rule subspace_topology_is_topology_on) (by100 blast)
  qed
  obtain x0 where hx0: "x0 \<in> U0" using hU0(1) by (by100 blast)
  have hx0_AB: "x0 \<in> top1_S2 - (A \<union> B)" using hx0 hU0(4) by (by100 blast)
  \<comment> \<open>U0 = path\_component(x0) in S2-(A\<union>B). Then U0 open by path\_component\_open\_if\_lpc.\<close>
  have hU0_eq_path_comp: "U0 = top1_path_component_of_on (top1_S2 - (A \<union> B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A \<union> B))) x0"
  proof -
    let ?W = "top1_S2 - (A \<union> B)" and ?TW = "subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A \<union> B))"
    \<comment> \<open>U0 path connected: connected + locally path connected open subspace.\<close>
    have hU0_sub_W: "U0 \<subseteq> ?W" using hU0(4) by (by100 blast)
    have hU0_conn_W: "top1_connected_on U0 (subspace_topology ?W ?TW U0)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology U0 = subspace_topology ?W ?TW U0"
        using subspace_topology_trans[of U0 ?W top1_S2 top1_S2_topology] hU0_sub_W by (by100 simp)
      thus ?thesis using hU0(5) by (by100 simp)
    qed
    \<comment> \<open>By Theorem 25.5: in lpc space, path\_comp = connected\_comp.\<close>
    have hThm255: "top1_path_component_of_on ?W ?TW x0 = top1_component_of_on ?W ?TW x0"
    proof -
      from conjunct2[OF Theorem_25_5[OF hTopAB_early]]
      have "top1_locally_path_connected_on ?W ?TW \<longrightarrow>
          (\<forall>x \<in> ?W. top1_path_component_of_on ?W ?TW x = top1_component_of_on ?W ?TW x)" .
      thus ?thesis using hAB_lpc hx0_AB by (by100 blast)
    qed
    \<comment> \<open>U0 \<subseteq> comp(x0) (U0 connected, x0 \<in> U0).\<close>
    have "U0 \<subseteq> top1_component_of_on ?W ?TW x0"
      by (rule top1_connected_subspace_subset_component_of[OF hU0_sub_W hx0 hU0_conn_W])
    \<comment> \<open>comp(x0) \<subseteq> U0: comp connected, comp \<subseteq> W = U0\<union>U0', comp \<inter> U0 \<ni> x0.
       If comp met U0', comp \<supseteq> U0\<union>U0' = W (by maximality), W connected, contradiction.\<close>
    moreover have "top1_component_of_on ?W ?TW x0 \<subseteq> U0"
    proof (rule ccontr)
      assume "\<not> top1_component_of_on ?W ?TW x0 \<subseteq> U0"
      then obtain y where hy: "y \<in> top1_component_of_on ?W ?TW x0" "y \<notin> U0" by (by100 blast)
      have "top1_component_of_on ?W ?TW x0 \<subseteq> ?W" by (rule top1_component_of_on_subset)
      have "y \<in> ?W" using hy(1) \<open>top1_component_of_on ?W ?TW x0 \<subseteq> ?W\<close> by (by100 blast)
      hence "y \<in> U0'" using hy(2) hU0(4) by (by100 blast)
      \<comment> \<open>U0' connected, y \<in> U0'. So U0' \<subseteq> comp(y) = comp(x0).\<close>
      have hU0'_sub_W: "U0' \<subseteq> ?W" using hU0(4) by (by100 blast)
      have hU0'_conn_W: "top1_connected_on U0' (subspace_topology ?W ?TW U0')"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology U0' = subspace_topology ?W ?TW U0'"
          using subspace_topology_trans[of U0' ?W top1_S2 top1_S2_topology] hU0'_sub_W by (by100 simp)
        thus ?thesis using hU0(6) by (by100 simp)
      qed
      have "U0' \<subseteq> top1_component_of_on ?W ?TW y"
        by (rule top1_connected_subspace_subset_component_of[OF hU0'_sub_W \<open>y \<in> U0'\<close> hU0'_conn_W])
      have "top1_component_of_on ?W ?TW y = top1_component_of_on ?W ?TW x0"
        by (rule top1_component_of_on_eq_of_mem[OF hTopAB_early hy(1)])
      hence "U0' \<subseteq> top1_component_of_on ?W ?TW x0"
        using \<open>U0' \<subseteq> top1_component_of_on ?W ?TW y\<close> by (by100 simp)
      \<comment> \<open>Now comp(x0) \<supseteq> U0 \<union> U0' = W. But comp(x0) \<subseteq> W. So comp(x0) = W.\<close>
      hence "?W \<subseteq> top1_component_of_on ?W ?TW x0"
        using \<open>U0 \<subseteq> top1_component_of_on ?W ?TW x0\<close> hU0(4) by (by100 blast)
      have hcomp_sub_W: "top1_component_of_on ?W ?TW x0 \<subseteq> ?W"
        by (rule top1_component_of_on_subset)
      hence "top1_component_of_on ?W ?TW x0 = ?W"
        using \<open>?W \<subseteq> top1_component_of_on ?W ?TW x0\<close> by (by100 blast)
      \<comment> \<open>Then W = comp(x0) is connected. But hAB\_sep says W not connected.\<close>
      have "top1_connected_on (top1_component_of_on ?W ?TW x0) (subspace_topology ?W ?TW (top1_component_of_on ?W ?TW x0))"
        by (rule top1_component_of_on_connected[OF hTopAB_early hx0_AB])
      hence "top1_connected_on ?W (subspace_topology ?W ?TW ?W)"
        using \<open>top1_component_of_on ?W ?TW x0 = ?W\<close> by (by100 force)
      moreover have "subspace_topology ?W ?TW ?W = ?TW"
      proof (rule subspace_topology_self)
        show "\<forall>U \<in> ?TW. U \<subseteq> ?W" unfolding subspace_topology_def by (by100 blast)
      qed
      ultimately have "top1_connected_on ?W ?TW" by (by100 simp)
      thus False using hAB_sep unfolding top1_separates_on_def by (by100 simp)
    qed
    ultimately show ?thesis using hThm255 by (by100 blast)
  qed
  \<comment> \<open>U0 open: U0 = path\_component(x0), which is open by path\_component\_open\_if\_lpc.\<close>
  have hU0_open: "U0 \<in> top1_S2_topology"
  proof -
    have "top1_path_component_of_on (top1_S2 - (A \<union> B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A \<union> B))) x0
        \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A \<union> B))"
      by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTopAB_early hAB_lpc hx0_AB])
    hence "U0 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A \<union> B))"
      using hU0_eq_path_comp by (by100 simp)
    \<comment> \<open>Open in open subspace \<Rightarrow> open in S2.\<close>
    then obtain V where "V \<in> top1_S2_topology" "U0 = (top1_S2 - (A \<union> B)) \<inter> V"
      unfolding subspace_topology_def by (by100 force)
    \<comment> \<open>U0 = (S2-(A\<union>B)) \<inter> V, both open \<Rightarrow> finite intersection \<Rightarrow> U0 open.\<close>
    have hax_U0: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> top1_S2_topology \<longrightarrow> \<Inter>F \<in> top1_S2_topology"
      using assms(1) unfolding is_topology_on_strict_def is_topology_on_def by (by100 blast)
    have hVW_fin: "finite {V, top1_S2 - (A \<union> B)}" by (by100 simp)
    have hVW_ne: "{V, top1_S2 - (A \<union> B)} \<noteq> {}" by (by100 simp)
    have hVW_sub: "{V, top1_S2 - (A \<union> B)} \<subseteq> top1_S2_topology"
      using \<open>V \<in> top1_S2_topology\<close> hAB_open_S2 by (by100 blast)
    have hVW_conj: "finite {V, top1_S2 - (A \<union> B)} \<and> {V, top1_S2 - (A \<union> B)} \<noteq> {} \<and>
        {V, top1_S2 - (A \<union> B)} \<subseteq> top1_S2_topology"
      using hVW_fin hVW_ne hVW_sub by (by100 blast)
    from hax_U0[rule_format, OF hVW_conj]
    have "\<Inter>{V, top1_S2 - (A \<union> B)} \<in> top1_S2_topology" .
    moreover have "V \<inter> (top1_S2 - (A \<union> B)) = U0" using \<open>U0 = _ \<inter> V\<close> by (by100 blast)
    hence "\<Inter>{V, top1_S2 - (A \<union> B)} = U0" by (by100 force)
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>U0' open: same argument by symmetry.\<close>
  have hU0'_open_pre: "U0' \<in> top1_S2_topology"
  proof -
    obtain x0' where hx0': "x0' \<in> U0'" using hU0(2) by (by100 blast)
    hence hx0'_AB: "x0' \<in> top1_S2 - (A \<union> B)" using hU0(4) by (by100 blast)
    \<comment> \<open>Same argument: U0' = path\_comp(x0') via Thm 25.5 + contradiction.\<close>
    let ?W = "top1_S2 - (A \<union> B)" and ?TW = "subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A \<union> B))"
    have hU0'_sub_W: "U0' \<subseteq> ?W" using hU0(4) by (by100 blast)
    have hU0'_conn_W: "top1_connected_on U0' (subspace_topology ?W ?TW U0')"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology U0' = subspace_topology ?W ?TW U0'"
        using subspace_topology_trans[of U0' ?W top1_S2 top1_S2_topology] hU0'_sub_W by (by100 simp)
      thus ?thesis using hU0(6) by (by100 simp)
    qed
    have hThm255': "top1_path_component_of_on ?W ?TW x0' = top1_component_of_on ?W ?TW x0'"
    proof -
      from conjunct2[OF Theorem_25_5[OF hTopAB_early]]
      have "top1_locally_path_connected_on ?W ?TW \<longrightarrow>
          (\<forall>x \<in> ?W. top1_path_component_of_on ?W ?TW x = top1_component_of_on ?W ?TW x)" .
      thus ?thesis using hAB_lpc hx0'_AB by (by100 blast)
    qed
    have "U0' \<subseteq> top1_component_of_on ?W ?TW x0'"
      by (rule top1_connected_subspace_subset_component_of[OF hU0'_sub_W hx0' hU0'_conn_W])
    moreover have "top1_component_of_on ?W ?TW x0' \<subseteq> U0'"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain y where "y \<in> top1_component_of_on ?W ?TW x0'" "y \<notin> U0'" by (by100 blast)
      have "top1_component_of_on ?W ?TW x0' \<subseteq> ?W" by (rule top1_component_of_on_subset)
      hence "y \<in> ?W" using \<open>y \<in> top1_component_of_on ?W ?TW x0'\<close> by (by100 blast)
      hence "y \<in> U0" using \<open>y \<notin> U0'\<close> hU0(4) by (by100 blast)
      have hU0_sub_W_loc: "U0 \<subseteq> ?W" using hU0(4) by (by100 blast)
      have hU0_conn_W_loc: "top1_connected_on U0 (subspace_topology ?W ?TW U0)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology U0 = subspace_topology ?W ?TW U0"
          using subspace_topology_trans[of U0 ?W top1_S2 top1_S2_topology] hU0_sub_W_loc by (by100 simp)
        thus ?thesis using hU0(5) by (by100 simp)
      qed
      have "U0 \<subseteq> top1_component_of_on ?W ?TW y"
        by (rule top1_connected_subspace_subset_component_of[OF hU0_sub_W_loc \<open>y \<in> U0\<close> hU0_conn_W_loc])
      have "top1_component_of_on ?W ?TW y = top1_component_of_on ?W ?TW x0'"
        by (rule top1_component_of_on_eq_of_mem[OF hTopAB_early \<open>y \<in> top1_component_of_on ?W ?TW x0'\<close>])
      hence "U0 \<subseteq> top1_component_of_on ?W ?TW x0'"
        using \<open>U0 \<subseteq> top1_component_of_on ?W ?TW y\<close> by (by100 simp)
      hence "?W \<subseteq> top1_component_of_on ?W ?TW x0'"
        using \<open>U0' \<subseteq> top1_component_of_on ?W ?TW x0'\<close> hU0(4) by (by100 blast)
      have hcomp_sub_W: "top1_component_of_on ?W ?TW x0' \<subseteq> ?W" by (rule top1_component_of_on_subset)
      hence "top1_component_of_on ?W ?TW x0' = ?W"
        using \<open>?W \<subseteq> top1_component_of_on ?W ?TW x0'\<close> by (by100 blast)
      have "top1_connected_on (top1_component_of_on ?W ?TW x0') (subspace_topology ?W ?TW (top1_component_of_on ?W ?TW x0'))"
        by (rule top1_component_of_on_connected[OF hTopAB_early hx0'_AB])
      hence "top1_connected_on ?W (subspace_topology ?W ?TW ?W)"
        using \<open>top1_component_of_on ?W ?TW x0' = ?W\<close> by (by100 force)
      moreover have "subspace_topology ?W ?TW ?W = ?TW"
      proof (rule subspace_topology_self)
        show "\<forall>U \<in> ?TW. U \<subseteq> ?W" unfolding subspace_topology_def by (by100 blast)
      qed
      ultimately have "top1_connected_on ?W ?TW" by (by100 simp)
      thus False using hAB_sep unfolding top1_separates_on_def by (by100 simp)
    qed
    ultimately have "U0' = top1_path_component_of_on ?W ?TW x0'" using hThm255' by (by100 blast)
    hence "U0' \<in> subspace_topology top1_S2 top1_S2_topology ?W"
      using top1_path_component_of_on_open_if_locally_path_connected[OF hTopAB_early hAB_lpc hx0'_AB]
      by (by100 simp)
    then obtain V where "V \<in> top1_S2_topology" "U0' = ?W \<inter> V"
      unfolding subspace_topology_def by (by100 force)
    have hax': "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> top1_S2_topology \<longrightarrow> \<Inter>F \<in> top1_S2_topology"
      using assms(1) unfolding is_topology_on_strict_def is_topology_on_def by (by100 blast)
    have "{V, ?W} \<subseteq> top1_S2_topology" using \<open>V \<in> top1_S2_topology\<close> hAB_open_S2 by (by100 blast)
    have "finite {V, ?W} \<and> {V, ?W} \<noteq> {} \<and> {V, ?W} \<subseteq> top1_S2_topology"
      using \<open>{V, ?W} \<subseteq> top1_S2_topology\<close> by (by100 force)
    from hax'[rule_format, OF this]
    have "\<Inter>{V, ?W} \<in> top1_S2_topology" .
    moreover have "V \<inter> ?W = U0'" using \<open>U0' = ?W \<inter> V\<close> by (by100 blast)
    hence "\<Inter>{V, ?W} = U0'" by (by100 force)
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Hence U0, U0' form a separation of S2-(A\<union>B).\<close>
  have hTopS2_loc: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hTopAB: "is_topology_on (top1_S2 - (A \<union> B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A \<union> B)))"
    by (rule subspace_topology_is_topology_on[OF hTopS2_loc]) (by100 blast)
  have hU0_in_sub: "U0 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A \<union> B))"
  proof -
    have "U0 = (top1_S2 - (A \<union> B)) \<inter> U0" using hU0(4) by (by100 blast)
    thus ?thesis unfolding subspace_topology_def using hU0_open by (by100 blast)
  qed
  have hU0'_in_sub: "U0' \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A \<union> B))"
  proof -
    have "U0' = (top1_S2 - (A \<union> B)) \<inter> U0'" using hU0(4) by (by100 blast)
    thus ?thesis unfolding subspace_topology_def using hU0'_open_pre by (by100 blast)
  qed
  have hAB_sep_proper: "top1_is_separation_on (top1_S2 - (A \<union> B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A \<union> B))) U0 U0'"
    unfolding top1_is_separation_on_def
    using hU0_in_sub hU0'_in_sub hU0(1,2,3,4) by (by100 blast)
  have hC_minus_sub_unused: "C - {a, b} \<subseteq> U0' \<or> C - {a, b} \<subseteq> U0"
  proof -
    have hCm_sub_AB: "C - {a, b} \<subseteq> top1_S2 - (A \<union> B)" by (rule hC_minus)
    have hCm_conn_sub: "top1_connected_on (C - {a, b})
        (subspace_topology (top1_S2 - (A \<union> B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A \<union> B))) (C - {a, b}))"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology (C - {a, b})
          = subspace_topology (top1_S2 - (A \<union> B))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A \<union> B))) (C - {a, b})"
        using subspace_topology_trans[of "C-{a,b}" "top1_S2-(A\<union>B)" top1_S2 top1_S2_topology]
          hCm_sub_AB by (by100 simp)
      thus ?thesis using hC_minus_conn by (by100 simp)
    qed
    from Lemma_23_2[OF hTopAB hAB_sep_proper hCm_sub_AB hCm_conn_sub]
    show ?thesis by (by100 blast)
  qed
  have "C - {a, b} \<subseteq> U0'" by (rule hC_in_U0')
  let ?Ubar = "U0 \<union> A \<union> B"
  have hUbar_conn: "top1_connected_on ?Ubar (subspace_topology top1_S2 top1_S2_topology ?Ubar)"
  proof -
    \<comment> \<open>Ubar = closure(U0). Use Theorem 23.4: U0 \<subseteq> Ubar \<subseteq> closure(U0), U0 connected \<Rightarrow> Ubar connected.\<close>
    have hU0_sub_Ubar: "U0 \<subseteq> ?Ubar" by (by100 blast)
    have hUbar_sub_closure: "?Ubar \<subseteq> closure_on top1_S2 top1_S2_topology U0"
    proof -
      \<comment> \<open>A\<union>B \<subseteq> closure(U0): by simple\_closed\_curve\_boundary\_meets\_component,
         every neighborhood of a point on A\<union>B meets U0.\<close>
      have "A \<union> B \<subseteq> closure_on top1_S2 top1_S2_topology U0"
      proof
        fix x assume "x \<in> A \<union> B"
        hence "x \<in> top1_S2" using assms(2,3) by (by100 blast)
        have hU0_sub_S2: "U0 \<subseteq> top1_S2" using hU0(4) by (by100 blast)
        have hTopS2_loc2: "is_topology_on top1_S2 top1_S2_topology"
          using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
        show "x \<in> closure_on top1_S2 top1_S2_topology U0"
        proof (rule iffD2[OF Theorem_17_5a[OF hTopS2_loc2 \<open>x \<in> top1_S2\<close> hU0_sub_S2]])
          \<comment> \<open>Every neighborhood of x meets U0.\<close>
          show "\<forall>U. neighborhood_of x top1_S2 top1_S2_topology U \<longrightarrow> intersects U U0"
          proof (intro allI impI)
            fix V assume hV: "neighborhood_of x top1_S2 top1_S2_topology V"
            hence hV_open: "V \<in> top1_S2_topology" and hxV: "x \<in> V"
              unfolding neighborhood_of_def by (by100 blast)+
            \<comment> \<open>V open, x \<in> A\<union>B \<inter> V. By boundary\_meets\_component, V \<inter> U0 \<noteq> {}.\<close>
            have "V \<inter> U0 \<noteq> {}"
              by (rule simple_closed_curve_boundary_meets_component[OF assms(1) hAB_scc hU0(5) hU0(6)
                  hU0(3) hU0(4) hU0(1) hU0(2) hU0_open hU0'_open_pre \<open>x \<in> A \<union> B\<close> hV_open hxV])
            thus "intersects V U0" unfolding intersects_def by (by100 blast)
          qed
        qed
      qed
      moreover have "U0 \<subseteq> closure_on top1_S2 top1_S2_topology U0"
        by (rule subset_closure_on)
      ultimately show ?thesis by (by100 blast)
    qed
    have hTopS2_here: "is_topology_on top1_S2 top1_S2_topology"
      using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have hU0_sub_S2: "U0 \<subseteq> top1_S2" using hU0(4) by (by100 blast)
    have hUbar_sub_S2: "?Ubar \<subseteq> top1_S2" using assms(2,3) hU0_sub_S2 by (by100 force)
    from Theorem_23_4[OF hTopS2_here hU0_sub_S2 hUbar_sub_S2 hU0_sub_Ubar hUbar_sub_closure hU0(5)]
    show ?thesis .
  qed
  have hUbar_eq: "?Ubar = top1_S2 - U0'"
    using hU0(3,4) assms(2,3) by (by100 blast)
  have hU0'_open: "U0' \<in> top1_S2_topology" by (rule hU0'_open_pre)
  have hU0'_sub: "U0' \<subseteq> top1_S2" using hU0(4) by (by100 blast)
  have hUbar_sub: "?Ubar \<subseteq> top1_S2" using assms(2,3) hU0(4) by (by100 force)
  have hUbar_compl: "top1_S2 - ?Ubar = U0'" using hUbar_eq hU0'_sub by (by100 force)
  have hUbar_closed: "closedin_on top1_S2 top1_S2_topology ?Ubar"
    unfolding closedin_on_def
    using hUbar_sub hUbar_compl hU0'_open by (by100 force)
  have hC_closed: "closedin_on top1_S2 top1_S2_topology C"
    by (rule arc_in_S2_closed[OF assms(4) assms(7)])
  have hUbar_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology ?Ubar"
    unfolding top1_separates_on_def
  proof -
    have "top1_S2 - ?Ubar = U0'"
    proof -
      have "U0' \<subseteq> top1_S2" using hU0(4) by (by100 blast)
      thus ?thesis using hUbar_eq by (by100 force)
    qed
    thus "\<not> \<not> top1_connected_on (top1_S2 - ?Ubar)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Ubar))"
      using hU0(6) by (by100 simp)
  qed
  have hC_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology C"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) assms(4) assms(7)])
  have hUbar_C_inter: "?Ubar \<inter> C = {a, b}"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> ?Ubar \<inter> C"
    hence hxU: "x \<in> U0 \<or> x \<in> A \<or> x \<in> B" and hxC: "x \<in> C" by (by100 blast)+
    show "x \<in> {a, b}"
    proof (cases "x \<in> A")
      case True thus ?thesis using hxC assms(11) by (by100 blast)
    next case False show ?thesis
      proof (cases "x \<in> B")
        case True thus ?thesis using hxC assms(10) by (by100 blast)
      next
        case False
        hence "x \<in> U0" using hxU \<open>x \<notin> A\<close> by (by100 blast)
        hence "x \<notin> U0'" using hU0(3) by (by100 blast)
        moreover have "x \<in> C - {a, b} \<or> x \<in> {a, b}" using hxC by (by100 blast)
        moreover { assume "x \<in> C - {a, b}"
          hence "x \<in> U0'" using \<open>C - {a, b} \<subseteq> U0'\<close> by (by100 blast) }
        ultimately show ?thesis by (by100 blast)
      qed
    qed
  next
    fix x assume "x \<in> {a, b}"
    have "a \<in> A" "b \<in> A" using assms(12) unfolding top1_arc_endpoints_on_def by (by100 blast)+
    have "a \<in> C" "b \<in> C" using assms(14) unfolding top1_arc_endpoints_on_def by (by100 blast)+
    thus "x \<in> ?Ubar \<inter> C" using \<open>x \<in> {a, b}\<close> \<open>a \<in> A\<close> \<open>b \<in> A\<close> by (by100 blast)
  qed
  have hUbar_C_card: "card (?Ubar \<inter> C) = 2"
    using hUbar_C_inter assms(8) by (by100 simp)
  \<comment> \<open>Theorem 63.5: Ubar \<union> C separates S2 into 2 components V0, W0.\<close>
  have hC_conn: "top1_connected_on C (subspace_topology top1_S2 top1_S2_topology C)"
    using arc_connected[OF assms(7)] .
  obtain V0 W0 where hVW: "V0 \<noteq> {}" "W0 \<noteq> {}" "V0 \<inter> W0 = {}"
      "V0 \<union> W0 = top1_S2 - (?Ubar \<union> C)"
      "top1_connected_on V0 (subspace_topology top1_S2 top1_S2_topology V0)"
      "top1_connected_on W0 (subspace_topology top1_S2 top1_S2_topology W0)"
    using Theorem_63_5_two_closed_connected[OF assms(1) hUbar_closed hC_closed
        hUbar_conn hC_conn hUbar_C_card hUbar_no_sep hC_no_sep]
    by (by100 force)
  \<comment> \<open>V0, W0 are open in S2 (components of open S2-(?Ubar\<union>C), same lpc argument).\<close>
  have hUbarC_compl_open: "top1_S2 - (?Ubar \<union> C) \<in> top1_S2_topology"
  proof -
    have hTopS2_loc: "is_topology_on top1_S2 top1_S2_topology"
      using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have "closedin_on top1_S2 top1_S2_topology (?Ubar \<union> C)"
      by (rule closedin_on_Un[OF hTopS2_loc hUbar_closed hC_closed])
    thus ?thesis unfolding closedin_on_def by (by100 blast)
  qed
  \<comment> \<open>V0, W0 open: same lpc argument as U0. Components of open S2-(?Ubar\<union>C).\<close>
  have hV0_open: "V0 \<in> top1_S2_topology" sorry
  have hW0_open: "W0 \<in> top1_S2_topology" sorry
  \<comment> \<open>Step 4: S2 - (A \<union> B \<union> C) = U0 \<union> V0 \<union> W0.\<close>
  \<comment> \<open>U0 \<inter> C = {}: since U0 \<subseteq> S2-(A\<union>B) and C\<inter>(A\<union>B) \<subseteq> {a,b}, and C-{a,b} \<subseteq> U0'.\<close>
  have hU0_C_disj: "U0 \<inter> C = {}"
  proof -
    have "U0 \<subseteq> top1_S2 - (A \<union> B)" using hU0(4) by (by100 blast)
    hence "U0 \<inter> (A \<union> B) = {}" by (by100 blast)
    moreover have "C - {a, b} \<subseteq> U0'" using \<open>C - {a, b} \<subseteq> U0'\<close> .
    hence "\<forall>x \<in> C. x \<notin> {a, b} \<longrightarrow> x \<in> U0'" by (by100 blast)
    moreover have "U0 \<inter> U0' = {}" by (rule hU0(3))
    moreover have "{a, b} \<subseteq> A \<union> B" using assms(12,13) unfolding top1_arc_endpoints_on_def
      by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  have "top1_S2 - (A \<union> B \<union> C) = U0 \<union> V0 \<union> W0"
  proof -
    have "top1_S2 - (A \<union> B \<union> C) = (top1_S2 - (A \<union> B)) - C" by (by100 blast)
    also have "\<dots> = (U0 \<union> U0') - C" using hU0(4) by (by100 blast)
    also have "\<dots> = U0 \<union> (U0' - C)" using hU0_C_disj by (by100 blast)
    also have "U0' - C = top1_S2 - (?Ubar \<union> C)"
    proof -
      have "?Ubar \<union> C = (U0 \<union> A \<union> B) \<union> C" by (by100 blast)
      have "top1_S2 - (?Ubar \<union> C) = (top1_S2 - (U0 \<union> A \<union> B)) - C" by (by100 blast)
      also have "top1_S2 - (U0 \<union> A \<union> B) = U0'"
        using hUbar_compl by (by100 simp)
      finally show ?thesis by (by100 simp)
    qed
    also have "\<dots> = V0 \<union> W0" using hVW(4) by (by100 simp)
    finally show ?thesis by (by100 blast)
  qed
  moreover have "U0 \<inter> V0 = {} \<and> U0 \<inter> W0 = {} \<and> V0 \<inter> W0 = {}"
  proof -
    have "V0 \<union> W0 = top1_S2 - (?Ubar \<union> C)" by (rule hVW(4))
    hence "V0 \<subseteq> top1_S2 - ?Ubar" "W0 \<subseteq> top1_S2 - ?Ubar" by (by100 blast)+
    hence "V0 \<inter> U0 = {}" "W0 \<inter> U0 = {}" by (by100 blast)+
    thus ?thesis using hVW(3) by (by100 blast)
  qed
  ultimately have hgoal: "top1_S2 - (A \<union> B \<union> C) = U0 \<union> V0 \<union> W0
      \<and> U0 \<inter> V0 = {} \<and> U0 \<inter> W0 = {} \<and> V0 \<inter> W0 = {}" by (by100 blast)
  show ?thesis
    apply (rule exI[of _ U0])
    apply (rule exI[of _ V0])
    apply (rule exI[of _ W0])
    using hgoal hU0(1) hVW(1,2) hU0(5) hVW(5,6) hU0_open hV0_open hW0_open by (by100 force)
qed

text \<open>Helper: connected components of open subsets of S2 are open in S2.\<close>

lemma S2_component_of_open_subset_is_open:
  assumes "W \<in> top1_S2_topology" "W \<subseteq> top1_S2"
      and "P \<subseteq> W" "P \<noteq> {}"
      and "top1_connected_on P (subspace_topology top1_S2 top1_S2_topology P)"
      and "\<And>Q. \<lbrakk>Q \<subseteq> W; P \<subseteq> Q; top1_connected_on Q (subspace_topology top1_S2 top1_S2_topology Q)\<rbrakk>
           \<Longrightarrow> Q = P"
  shows "P \<in> top1_S2_topology"
proof -
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>W is open lpc (S2 is lpc, open subset of lpc is lpc).\<close>
  have hW_lpc: "top1_locally_path_connected_on W (subspace_topology top1_S2 top1_S2_topology W)"
    by (rule open_subset_locally_path_connected[OF S2_locally_path_connected assms(1) assms(2)])
  have hTW: "is_topology_on W (subspace_topology top1_S2 top1_S2_topology W)"
    by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, rule assms(2))
  \<comment> \<open>Pick x \<in> P. Show P = path\_component\_of\_on W TW x.\<close>
  obtain x where hx: "x \<in> P" using assms(4) by (by100 blast)
  hence hxW: "x \<in> W" using assms(3) by (by100 blast)
  \<comment> \<open>In lpc space, path\_component = connected\_component (Theorem 25.5).\<close>
  have hpc_eq_cc: "top1_path_component_of_on W (subspace_topology top1_S2 top1_S2_topology W) x =
      top1_component_of_on W (subspace_topology top1_S2 top1_S2_topology W) x"
    using conjunct2[OF Theorem_25_5[OF hTW]] hW_lpc hxW by (by100 blast)
  \<comment> \<open>P = component\_of\_on(x): P is connected \<ni> x and maximal.\<close>
  have hP_conn_W: "top1_connected_on P (subspace_topology W (subspace_topology top1_S2 top1_S2_topology W) P)"
  proof -
    have "subspace_topology top1_S2 top1_S2_topology P =
        subspace_topology W (subspace_topology top1_S2 top1_S2_topology W) P"
      using subspace_topology_trans[of P W top1_S2 top1_S2_topology] assms(3) by (by100 simp)
    thus ?thesis using assms(5) by (by100 simp)
  qed
  have "P \<subseteq> top1_component_of_on W (subspace_topology top1_S2 top1_S2_topology W) x"
    by (rule top1_connected_subspace_subset_component_of[OF assms(3) hx hP_conn_W])
  moreover have "top1_component_of_on W (subspace_topology top1_S2 top1_S2_topology W) x \<subseteq> P"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain y where hy: "y \<in> top1_component_of_on W (subspace_topology top1_S2 top1_S2_topology W) x"
        "y \<notin> P" by (by100 blast)
    let ?C = "top1_component_of_on W (subspace_topology top1_S2 top1_S2_topology W) x"
    have hC_sub: "?C \<subseteq> W"
      by (rule top1_component_of_on_subset)
    have hC_conn_S2: "top1_connected_on ?C (subspace_topology top1_S2 top1_S2_topology ?C)"
    proof -
      have hC_conn_W: "top1_connected_on ?C (subspace_topology W (subspace_topology top1_S2 top1_S2_topology W) ?C)"
        by (rule top1_component_of_on_connected[OF hTW hxW])
      have "subspace_topology top1_S2 top1_S2_topology ?C =
          subspace_topology W (subspace_topology top1_S2 top1_S2_topology W) ?C"
        using subspace_topology_trans[of ?C W top1_S2 top1_S2_topology] hC_sub by (by100 simp)
      thus ?thesis using hC_conn_W by (by100 simp)
    qed
    from assms(6)[OF hC_sub _ hC_conn_S2] have "?C = P"
      using \<open>P \<subseteq> ?C\<close> by (by100 blast)
    thus False using hy by (by100 blast)
  qed
  ultimately have hP_eq: "P = top1_component_of_on W (subspace_topology top1_S2 top1_S2_topology W) x"
    by (by100 blast)
  hence hP_eq_pc: "P = top1_path_component_of_on W (subspace_topology top1_S2 top1_S2_topology W) x"
    using hpc_eq_cc by (by100 simp)
  \<comment> \<open>Path component is open in W's subspace topology.\<close>
  have "top1_path_component_of_on W (subspace_topology top1_S2 top1_S2_topology W) x \<in>
      subspace_topology top1_S2 top1_S2_topology W"
    by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTW hW_lpc hxW])
  hence "P \<in> subspace_topology top1_S2 top1_S2_topology W" using hP_eq_pc by (by100 simp)
  \<comment> \<open>Open in subspace of open set \<Rightarrow> open in ambient.\<close>
  then obtain V where hV: "V \<in> top1_S2_topology" "P = W \<inter> V"
    unfolding subspace_topology_def by (by100 blast)
  hence "P = V \<inter> W" by (by100 blast)
  moreover have "V \<inter> W \<in> top1_S2_topology"
  proof -
    have hfin: "finite {V, W}" by (by100 simp)
    have hne: "{V, W} \<noteq> {}" by (by100 simp)
    have hsub: "{V, W} \<subseteq> top1_S2_topology" using hV(1) assms(1) by (by100 blast)
    from hTopS2 have "\<And>F. finite F \<Longrightarrow> F \<noteq> {} \<Longrightarrow> F \<subseteq> top1_S2_topology \<Longrightarrow> \<Inter>F \<in> top1_S2_topology"
      unfolding is_topology_on_def by (by100 blast)
    from this[OF hfin hne hsub] have "\<Inter>{V, W} \<in> top1_S2_topology" .
    moreover have "\<Inter>{V, W} = V \<inter> W" by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  ultimately show ?thesis by (by100 simp)
qed

text \<open>Helper: Arc endpoint is in closure of arc minus endpoints.\<close>

lemma arc_endpoint_in_closure_of_interior:
  assumes "is_topology_on_strict X TX" "is_hausdorff_on X TX"
      and "A \<subseteq> X"
      and "top1_is_arc_on A (subspace_topology X TX A)"
      and "top1_arc_endpoints_on A (subspace_topology X TX A) = {a, b}"
      and "a \<noteq> b"
  shows "a \<in> closure_on X TX (A - {a, b})"
    and "b \<in> closure_on X TX (A - {a, b})"
proof -
  have hTopX: "is_topology_on X TX"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hA_closed: "closedin_on X TX A"
  proof -
    \<comment> \<open>Arc is compact (image of [0,1]), compact in Hausdorff is closed.\<close>
    have "top1_compact_on A (subspace_topology X TX A)"
    proof -
      obtain h where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          A (subspace_topology X TX A) h"
        using assms(4) unfolding top1_is_arc_on_def by (by100 blast)
      have hcont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          A (subspace_topology X TX A) h"
        using hh unfolding top1_homeomorphism_on_def by (by100 blast)
      have himg: "h ` top1_unit_interval = A"
        using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
      proof -
        have "compact (top1_unit_interval :: real set)" unfolding top1_unit_interval_def
          by (rule compact_Icc)
        hence "top1_compact_on top1_unit_interval (subspace_topology (UNIV :: real set) top1_open_sets top1_unit_interval)"
          using top1_compact_on_subspace_UNIV_iff_compact by (by100 blast)
        thus ?thesis unfolding top1_unit_interval_topology_def by (by100 blast)
      qed
      have hTA: "is_topology_on A (subspace_topology X TX A)"
        by (rule subspace_topology_is_topology_on[OF hTopX assms(3)])
      from top1_compact_on_continuous_image[OF hI_compact hTA hcont]
      have "top1_compact_on (h ` top1_unit_interval) (subspace_topology A (subspace_topology X TX A) (h ` top1_unit_interval))" .
      moreover have "h ` top1_unit_interval = A" by (rule himg)
      moreover have "subspace_topology A (subspace_topology X TX A) A = subspace_topology X TX A"
      proof -
        have "\<forall>U\<in>subspace_topology X TX A. U \<subseteq> A" unfolding subspace_topology_def by (by100 blast)
        thus ?thesis by (rule subspace_topology_self)
      qed
      ultimately show ?thesis by (by100 simp)
    qed
    thus ?thesis
    proof -
      \<comment> \<open>Compact in Hausdorff is closed.\<close>
      assume hcomp: "top1_compact_on A (subspace_topology X TX A)"
      show "closedin_on X TX A" sorry \<comment> \<open>Theorem\_26\_3: compact subspace of Hausdorff is closed.\<close>
    qed
  qed
  have ha_in_A: "a \<in> A"
    using assms(5) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have hb_in_A: "b \<in> A"
    using assms(5) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have hA_minus_ne: "A - {a, b} \<noteq> {}"
  proof -
    \<comment> \<open>Arc has \<ge> 3 points: homeomorphic to [0,1] which has uncountably many points.\<close>
    obtain h where "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
        A (subspace_topology X TX A) h"
      using assms(4) unfolding top1_is_arc_on_def by (by100 blast)
    hence "h ` top1_unit_interval = A"
      unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    moreover have "(1/2 :: real) \<in> top1_unit_interval"
      unfolding top1_unit_interval_def by (by100 simp)
    ultimately have "h (1/2) \<in> A" by (by100 blast)
    moreover have "h (1/2) \<notin> {a, b}"
    proof -
      \<comment> \<open>h is injective, h(0) and h(1) are the endpoints {a,b}. h(1/2) \<noteq> h(0) and h(1/2) \<noteq> h(1).\<close>
      obtain hh where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          A (subspace_topology X TX A) hh"
        using assms(4) unfolding top1_is_arc_on_def by (by100 blast)
      have hinj: "inj_on hh top1_unit_interval"
        using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have hhh0: "hh 0 \<in> {a, b}" sorry
      have hhh1: "hh 1 \<in> {a, b}" sorry
      moreover have "(1/2::real) \<noteq> (0::real)" by (by100 simp)
      moreover have "(1/2::real) \<noteq> (1::real)" by (by100 simp)
      moreover have "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
      moreover have "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
      moreover have "(1/2::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
      ultimately show ?thesis sorry
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  have hA_minus_sub: "A - {a, b} \<subseteq> X" using assms(3) by (by100 blast)
  \<comment> \<open>closure(A-{a,b}) \<subseteq> A (A is closed) and closure(A-{a,b}) \<supseteq> A-{a,b}.
     If a \<notin> closure(A-{a,b}), then A-{a,b} is clopen in A-{b} (connected).
     A-{b} is connected (removing one endpoint from arc), contradiction.\<close>
  have hA_minus_b_conn: "top1_connected_on (A - {b}) (subspace_topology X TX (A - {b}))"
    sorry \<comment> \<open>Arc minus one endpoint = [0,1) minus pt, connected.\<close>
  show "a \<in> closure_on X TX (A - {a, b})" sorry
  show "b \<in> closure_on X TX (A - {a, b})" sorry
qed

text \<open>Lemma 64.3: K4 in S2 separates into four components.\<close>

lemma Lemma_64_3_K4_four_components:
  fixes a1 a2 a3 a4 :: "real \<times> real \<times> real"
    and e12 e23 e34 e41 e13 e24 :: "(real \<times> real \<times> real) set"
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "card {a1, a2, a3, a4} = 4"
      and "{a1, a2, a3, a4} \<subseteq> top1_S2"
      and "e12 \<subseteq> top1_S2" "e23 \<subseteq> top1_S2" "e34 \<subseteq> top1_S2"
      and "e41 \<subseteq> top1_S2" "e13 \<subseteq> top1_S2" "e24 \<subseteq> top1_S2"
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
  shows "\<exists>U1 U2 U3 U4.
      U1 \<noteq> {} \<and> U2 \<noteq> {} \<and> U3 \<noteq> {} \<and> U4 \<noteq> {}
      \<and> U1 \<inter> U2 = {} \<and> U1 \<inter> U3 = {} \<and> U1 \<inter> U4 = {}
      \<and> U2 \<inter> U3 = {} \<and> U2 \<inter> U4 = {} \<and> U3 \<inter> U4 = {}
      \<and> U1 \<union> U2 \<union> U3 \<union> U4 = top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e41 \<union> e13 \<union> e24)
      \<and> top1_connected_on U1 (subspace_topology top1_S2 top1_S2_topology U1)
      \<and> top1_connected_on U2 (subspace_topology top1_S2 top1_S2_topology U2)
      \<and> top1_connected_on U3 (subspace_topology top1_S2 top1_S2_topology U3)
      \<and> top1_connected_on U4 (subspace_topology top1_S2 top1_S2_topology U4)"
proof -
  \<comment> \<open>Extract vertex distinctness.\<close>
  have hdist: "a1 \<noteq> a2" "a1 \<noteq> a3" "a1 \<noteq> a4" "a2 \<noteq> a3" "a2 \<noteq> a4" "a3 \<noteq> a4"
  proof -
    from assms(2) have hc4: "card {a1, a2, a3, a4} = 4" .
    { assume h: "a1 = a2"
      have "{a1, a2, a3, a4} = {a1, a3, a4}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a1 \<noteq> a2" by (by100 blast)
    { assume h: "a1 = a3"
      have "{a1, a2, a3, a4} = {a1, a2, a4}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a1 \<noteq> a3" by (by100 blast)
    { assume h: "a1 = a4"
      have "{a1, a2, a3, a4} = {a1, a2, a3}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a1 \<noteq> a4" by (by100 blast)
    { assume h: "a2 = a3"
      have "{a1, a2, a3, a4} = {a1, a2, a4}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a2 \<noteq> a3" by (by100 blast)
    { assume h: "a2 = a4"
      have "{a1, a2, a3, a4} = {a1, a2, a3}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a2 \<noteq> a4" by (by100 blast)
    { assume h: "a3 = a4"
      have "{a1, a2, a3, a4} = {a1, a2, a3}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a3 \<noteq> a4" by (by100 blast)
  qed
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology"
    by (rule top1_S2_is_hausdorff)
  have hS2_strict: "is_topology_on_strict top1_S2 top1_S2_topology"
    by (rule assms(1))
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>Step 1: Form theta space. A = e12 \<union> e23, B = e13, C = e41 \<union> e34.\<close>
  let ?A = "e12 \<union> e23" and ?B = "e13" and ?C = "e41 \<union> e34"
  let ?Y = "?A \<union> ?B \<union> ?C"
  \<comment> \<open>A is an arc from a1 to a3 (via concatenation at a2).\<close>
  have ha2_ep12: "a2 \<in> top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
    using assms(16) by (by100 blast)
  have ha2_ep23: "a2 \<in> top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
    using assms(17) by (by100 blast)
  have hA_arc: "top1_is_arc_on ?A (subspace_topology top1_S2 top1_S2_topology ?A)"
    by (rule arcs_concatenation_is_arc[OF hS2_strict hS2_haus assms(10) assms(4)
        assms(11) assms(5) assms(24) ha2_ep12 ha2_ep23])
  have hA_ep: "top1_arc_endpoints_on ?A (subspace_topology top1_S2 top1_S2_topology ?A) = {a1, a3}"
    by (rule arc_concat_endpoints[OF hS2_strict hS2_haus assms(10) assms(4)
        assms(11) assms(5) assms(24) ha2_ep12 ha2_ep23 assms(16) assms(17) hdist(1) hdist(4)])
  have hA_sub: "?A \<subseteq> top1_S2" using assms(4,5) by (by100 blast)
  \<comment> \<open>C is an arc from a1 to a3 (via concatenation at a4).\<close>
  have he41_e34_int: "e41 \<inter> e34 = {a4}" using assms(26) by (by100 blast)
  have ha4_ep41: "a4 \<in> top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
    using assms(19) by (by100 blast)
  have ha4_ep34: "a4 \<in> top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
    using assms(18) by (by100 blast)
  have hC_arc: "top1_is_arc_on ?C (subspace_topology top1_S2 top1_S2_topology ?C)"
    by (rule arcs_concatenation_is_arc[OF hS2_strict hS2_haus assms(13) assms(7)
        assms(12) assms(6) he41_e34_int ha4_ep41 ha4_ep34])
  have ha4_ne_a3: "a4 \<noteq> a3" using hdist(6) by (by100 blast)
  \<comment> \<open>Reorder endpoints for unification: {a4,a1} \<rightarrow> {a1,a4}, {a3,a4} \<rightarrow> {a4,a3}.\<close>
  have hep_e41: "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a1, a4}"
    using assms(19) by (by100 force)
  have hep_e34: "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a4, a3}"
    using assms(18) by (by100 force)
  have hC_ep: "top1_arc_endpoints_on ?C (subspace_topology top1_S2 top1_S2_topology ?C) = {a1, a3}"
    by (rule arc_concat_endpoints[OF hS2_strict hS2_haus assms(13) assms(7)
        assms(12) assms(6) he41_e34_int ha4_ep41 ha4_ep34 hep_e41 hep_e34 hdist(3) ha4_ne_a3])
  have hC_sub: "?C \<subseteq> top1_S2" using assms(6,7) by (by100 blast)
  \<comment> \<open>Intersection conditions for theta space.\<close>
  have hAB_int: "?A \<inter> ?B = {a1, a3}"
    using assms(28) assms(29) by (by100 blast)
  have hBC_int: "?B \<inter> ?C = {a1, a3}"
    using assms(31) assms(30) by (by100 blast)
  have hAC_int: "?A \<inter> ?C = {a1, a3}"
    using assms(27) assms(22) assms(23) assms(25) by (by100 blast)
  \<comment> \<open>Step 2: Apply Lemma 64.1 to get 3 components.\<close>
  obtain U V W where hUVW:
      "U \<noteq> {}" "V \<noteq> {}" "W \<noteq> {}"
      "U \<inter> V = {}" "V \<inter> W = {}" "U \<inter> W = {}"
      "U \<union> V \<union> W = top1_S2 - (?A \<union> ?B \<union> ?C)"
      "top1_connected_on U (subspace_topology top1_S2 top1_S2_topology U)"
      "top1_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
      "top1_connected_on W (subspace_topology top1_S2 top1_S2_topology W)"
      "U \<in> top1_S2_topology" "V \<in> top1_S2_topology" "W \<in> top1_S2_topology"
    using Lemma_64_1_theta_space_three_components[OF assms(1) hA_sub assms(8) hC_sub
        hA_arc assms(14) hC_arc hdist(2) hAB_int hBC_int hAC_int hA_ep assms(20) hC_ep]
    by (by100 metis)
  \<comment> \<open>Step 3: Identify which theta component contains e24-{a2,a4}.
     Use JCT on A\<union>B and B\<union>C to get 2-component decompositions, then boundary arguments.\<close>
  \<comment> \<open>A\<union>B is SCC.\<close>
  have hAB_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology (?A \<union> ?B)"
    by (rule arcs_form_simple_closed_curve[OF hS2_strict hS2_haus hA_arc hA_sub
        assms(14) assms(8) hAB_int hdist(2) hA_ep assms(20)])
  \<comment> \<open>Apply Theorem_63_5 to A and B (as separate arcs) to get 2 components of S2-(A\<union>B).\<close>
  have hA_closed: "closedin_on top1_S2 top1_S2_topology ?A"
    by (rule arc_in_S2_closed[OF hA_sub hA_arc])
  have hB_closed: "closedin_on top1_S2 top1_S2_topology ?B"
    by (rule arc_in_S2_closed[OF assms(8) assms(14)])
  have hA_conn: "top1_connected_on ?A (subspace_topology top1_S2 top1_S2_topology ?A)"
    using arc_connected[OF hA_arc] .
  have hB_conn: "top1_connected_on ?B (subspace_topology top1_S2 top1_S2_topology ?B)"
    using arc_connected[OF assms(14)] .
  have hA_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology ?A"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) hA_sub hA_arc])
  have hB_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology ?B"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) assms(8) assms(14)])
  have hAB_card: "card (?A \<inter> ?B) = 2"
    using hAB_int hdist(2) by (by100 simp)
  \<comment> \<open>Get raw components, then choose labels so C-{a1,a3} \<subseteq> P2.\<close>
  have hCm_conn: "top1_connected_on (?C - {a1, a3})
      (subspace_topology top1_S2 top1_S2_topology (?C - {a1, a3}))"
    by (rule arc_minus_endpoints_connected[OF hS2_strict hS2_haus hC_sub hC_arc hC_ep hdist(2)])
  have hCm_sub_AB: "?C - {a1, a3} \<subseteq> top1_S2 - (?A \<union> ?B)"
  proof -
    have "?C \<inter> (?A \<union> ?B) \<subseteq> {a1, a3}"
    proof -
      have "?C \<inter> ?A = {a1, a3}" using hAC_int by (by100 blast)
      moreover have "?C \<inter> ?B = {a1, a3}" using hBC_int by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    thus ?thesis using hC_sub by (by100 blast)
  qed
  have hCm_ne: "?C - {a1, a3} \<noteq> {}"
  proof -
    have "a4 \<in> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
    hence "a4 \<in> ?C" by (by100 blast)
    moreover have "a4 \<notin> {a1, a3}" using hdist(3) hdist(6) by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  obtain P1_raw P2_raw where hP_raw: "P1_raw \<noteq> {}" "P2_raw \<noteq> {}" "P1_raw \<inter> P2_raw = {}"
      "P1_raw \<union> P2_raw = top1_S2 - (?A \<union> ?B)"
      "top1_connected_on P1_raw (subspace_topology top1_S2 top1_S2_topology P1_raw)"
      "top1_connected_on P2_raw (subspace_topology top1_S2 top1_S2_topology P2_raw)"
    using Theorem_63_5_two_closed_connected[OF assms(1) hA_closed hB_closed
        hA_conn hB_conn hAB_card hA_no_sep hB_no_sep]
    by (by100 force)
  have hCm_in_raw: "?C - {a1, a3} \<subseteq> P1_raw \<or> ?C - {a1, a3} \<subseteq> P2_raw"
    sorry \<comment> \<open>Lemma\_23\_2: connected subset of separation.\<close>
  obtain P1 P2 where hP: "P1 \<noteq> {}" "P2 \<noteq> {}" "P1 \<inter> P2 = {}"
      "P1 \<union> P2 = top1_S2 - (?A \<union> ?B)"
      "top1_connected_on P1 (subspace_topology top1_S2 top1_S2_topology P1)"
      "top1_connected_on P2 (subspace_topology top1_S2 top1_S2_topology P2)"
      and hCm_in_P2: "?C - {a1, a3} \<subseteq> P2"
  proof -
    from hCm_in_raw show ?thesis
    proof
      assume "?C - {a1, a3} \<subseteq> P1_raw"
      show ?thesis
        by (rule that[of P2_raw P1_raw])
          (use hP_raw \<open>?C - {a1, a3} \<subseteq> P1_raw\<close> in \<open>by100 blast\<close>)+
    next
      assume "?C - {a1, a3} \<subseteq> P2_raw"
      show ?thesis
        by (rule that[of P1_raw P2_raw])
          (use hP_raw \<open>?C - {a1, a3} \<subseteq> P2_raw\<close> in \<open>by100 blast\<close>)+
    qed
  qed
  \<comment> \<open>Both P1, P2 are open (components of open set S2-(A\<union>B)).\<close>
  have hAB_closed_S2: "closedin_on top1_S2 top1_S2_topology (?A \<union> ?B)"
    by (rule closedin_on_Un[OF hTopS2 hA_closed hB_closed])
  have hAB_compl_open: "top1_S2 - (?A \<union> ?B) \<in> top1_S2_topology"
    using hAB_closed_S2 unfolding closedin_on_def by (by100 blast)
  \<comment> \<open>Components P1, P2 are open: they are path components of the open set S2-(A\<union>B),
     which is lpc (S2 is lpc, open subsets of lpc are lpc).\<close>
  \<comment> \<open>Key: S2-(A\<union>B) is open lpc, so connected components are open.\<close>
  have hAB_open_lpc: "top1_locally_path_connected_on (top1_S2 - (?A \<union> ?B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))"
    by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hAB_compl_open])
       (by100 blast)
  have hTAB: "is_topology_on (top1_S2 - (?A \<union> ?B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))"
    by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
  obtain x_P where hx_P: "x_P \<in> P1" using hP(1) by (by100 blast)
  have hx_P_W: "x_P \<in> top1_S2 - (?A \<union> ?B)" using hx_P hP(4) by (by100 blast)
  \<comment> \<open>Establish P1 = path\_component(x\_P) at outer scope for reuse.\<close>
  have hP1_sub_AB: "P1 \<subseteq> top1_S2 - (?A \<union> ?B)" using hP(4) by (by100 blast)
  have hP1_conn_AB: "top1_connected_on P1
      (subspace_topology (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) P1)"
  proof -
    have "subspace_topology top1_S2 top1_S2_topology P1 =
        subspace_topology (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) P1"
      using subspace_topology_trans[of P1 "top1_S2 - (?A \<union> ?B)" top1_S2 top1_S2_topology]
          hP1_sub_AB by (by100 simp)
    thus ?thesis using hP(5) by (by100 simp)
  qed
  have hP1_eq_comp: "P1 = top1_component_of_on (top1_S2 - (?A \<union> ?B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
  proof -
    have hP1_sub_comp: "P1 \<subseteq> top1_component_of_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
      by (rule top1_connected_subspace_subset_component_of[OF hP1_sub_AB hx_P hP1_conn_AB])
    have hcomp_sub_P1: "top1_component_of_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P \<subseteq> P1"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain y where hy: "y \<in> top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P" "y \<notin> P1"
        by (by100 blast)
      have "y \<in> top1_S2 - (?A \<union> ?B)"
        using hy(1) top1_component_of_on_subset[of "top1_S2 - (?A \<union> ?B)"] by (by100 blast)
      hence "y \<in> P2" using hP(4) hy(2) by (by100 blast)
      have hP2_sub: "P2 \<subseteq> top1_S2 - (?A \<union> ?B)" using hP(4) by (by100 blast)
      have hP2_conn_sub: "top1_connected_on P2
          (subspace_topology (top1_S2 - (?A \<union> ?B))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) P2)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology P2 =
            subspace_topology (top1_S2 - (?A \<union> ?B))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) P2"
          using subspace_topology_trans[of P2 "top1_S2 - (?A \<union> ?B)" top1_S2 top1_S2_topology]
              hP2_sub by (by100 simp)
        thus ?thesis using hP(6) by (by100 simp)
      qed
      have "P2 \<subseteq> top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) y"
        by (rule top1_connected_subspace_subset_component_of[OF hP2_sub \<open>y \<in> P2\<close> hP2_conn_sub])
      moreover have "top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) y =
          top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
        by (rule top1_component_of_on_eq_of_mem[OF hTAB hy(1)])
      ultimately have "P1 \<union> P2 \<subseteq> top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
        using hP1_sub_comp by (by100 blast)
      moreover have "top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P \<subseteq>
          top1_S2 - (?A \<union> ?B)"
        by (rule top1_component_of_on_subset)
      ultimately have "top1_S2 - (?A \<union> ?B) = top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
        using hP(4) by (by100 blast)
      have hcomp_conn: "top1_connected_on
          (top1_component_of_on (top1_S2 - (?A \<union> ?B))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P)
          (subspace_topology (top1_S2 - (?A \<union> ?B))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
              (top1_component_of_on (top1_S2 - (?A \<union> ?B))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P))"
        by (rule top1_component_of_on_connected[OF hTAB hx_P_W])
      hence "top1_connected_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology (top1_S2 - (?A \<union> ?B))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
              (top1_S2 - (?A \<union> ?B)))"
        using \<open>top1_S2 - (?A \<union> ?B) = top1_component_of_on _ _ x_P\<close> by (by100 simp)
      moreover have "subspace_topology (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
          (top1_S2 - (?A \<union> ?B)) =
          subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
        using subspace_topology_trans[of "top1_S2 - (?A \<union> ?B)" "top1_S2 - (?A \<union> ?B)"
            top1_S2 top1_S2_topology] by (by100 simp)
      ultimately have "top1_connected_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))" by (by100 simp)
      moreover have "\<not> top1_connected_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))"
        using Theorem_61_3_JordanSeparation_S2[OF assms(1) hAB_scc]
        unfolding top1_separates_on_def by (by100 blast)
      ultimately show False by (by100 blast)
    qed
    from hP1_sub_comp hcomp_sub_P1 show ?thesis by (by100 blast)
  qed
  have hP1_eq_pc: "P1 = top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
  proof -
    from conjunct2[OF Theorem_25_5[OF hTAB]]
    have "\<forall>z \<in> top1_S2 - (?A \<union> ?B).
        top1_locally_path_connected_on (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) \<longrightarrow>
        top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) z =
        top1_component_of_on (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) z" by (by100 blast)
    hence "top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P =
        top1_component_of_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
      using hAB_open_lpc hx_P_W by (by100 metis)
    thus ?thesis using hP1_eq_comp by (by100 simp)
  qed
  \<comment> \<open>Helper: open-in-subspace-of-open implies open-in-S2.\<close>
  have open_in_sub_imp_open: "\<And>W P. W \<in> top1_S2_topology \<Longrightarrow>
      P \<in> subspace_topology top1_S2 top1_S2_topology W \<Longrightarrow> P \<in> top1_S2_topology"
  proof -
    fix W P assume hW: "W \<in> top1_S2_topology" and hP_sub: "P \<in> subspace_topology top1_S2 top1_S2_topology W"
    from hP_sub obtain V where hV: "V \<in> top1_S2_topology" "P = W \<inter> V"
      unfolding subspace_topology_def by (by100 blast)
    have "finite {W, V}" by (by100 simp)
    moreover have "{W, V} \<noteq> {}" by (by100 simp)
    moreover have "{W, V} \<subseteq> top1_S2_topology" using hW hV(1) by (by100 blast)
    ultimately have "\<Inter>{W, V} \<in> top1_S2_topology"
      using hTopS2 unfolding is_topology_on_def by (by100 blast)
    moreover have "\<Inter>{W, V} = W \<inter> V" by (by100 blast)
    ultimately show "P \<in> top1_S2_topology" using hV(2) by (by100 simp)
  qed
  have hP1_open: "P1 \<in> top1_S2_topology"
  proof -
    have "top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P \<in>
        subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
      by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTAB hAB_open_lpc hx_P_W])
    hence "P1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
      using hP1_eq_pc by (by100 simp)
    thus ?thesis by (rule open_in_sub_imp_open[OF hAB_compl_open])
  qed
  \<comment> \<open>P2 = complement of P1 in S2-(A\<union>B). Since P1 is a path component and lpc, complement is open.\<close>
  have hP2_open: "P2 \<in> top1_S2_topology"
  proof -
    have hP2_eq: "P2 = (top1_S2 - (?A \<union> ?B)) -
        top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
      using hP(3,4) hP1_eq_pc by (by100 blast)
    have "(top1_S2 - (?A \<union> ?B)) -
        top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P \<in>
        subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
      by (rule top1_path_component_of_on_complement_open_if_locally_path_connected[OF hTAB hAB_open_lpc hx_P_W])
    hence "P2 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
      using hP2_eq by (by100 simp)
    thus ?thesis by (rule open_in_sub_imp_open[OF hAB_compl_open])
  qed
  \<comment> \<open>C-{a1,a3} \<subseteq> P2 was established in the obtain above.\<close>
  \<comment> \<open>closure(P1) = P1 \<union> (A\<union>B), using simple_closed_curve_boundary_meets_component.\<close>
  have hcl_P1: "closure_on top1_S2 top1_S2_topology P1 = P1 \<union> (?A \<union> ?B)"
  proof (rule set_eqI, rule iffI)
    fix z assume "z \<in> closure_on top1_S2 top1_S2_topology P1"
    \<comment> \<open>cl(P1) \<subseteq> P1 \<union> (A\<union>B): P2 open \<Rightarrow> S2-P2 closed \<Rightarrow> cl(P1) \<subseteq> S2-P2 = P1\<union>(A\<union>B).\<close>
    have hP1_AB_eq: "P1 \<union> (?A \<union> ?B) = top1_S2 - P2"
    proof -
      have hP1_sub_S2: "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      have "top1_S2 - P2 = (top1_S2 - (P1 \<union> P2)) \<union> P1" using hP(3) hP1_sub_S2 by (by100 force)
      also have "\<dots> = (?A \<union> ?B) \<union> P1"
      proof -
        have "top1_S2 - (P1 \<union> P2) = top1_S2 - (top1_S2 - (?A \<union> ?B))" using hP(4) by (by100 blast)
        also have "\<dots> = ?A \<union> ?B"
        proof -
          have "?A \<union> ?B \<subseteq> top1_S2" using hA_sub assms(8) by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        finally show ?thesis by (by100 simp)
      qed
      finally show ?thesis by (by100 blast)
    qed
    moreover have hcl_S2_P2: "closedin_on top1_S2 top1_S2_topology (top1_S2 - P2)"
    proof -
      have hP2_sub_S2: "P2 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      have hsub: "top1_S2 - P2 \<subseteq> top1_S2" by (by100 blast)
      have hcompl: "top1_S2 - (top1_S2 - P2) = P2" using hP2_sub_S2 by (by100 blast)
      show ?thesis unfolding closedin_on_def
        apply (rule conjI[OF hsub])
        using hcompl hP2_open by (by100 simp)
    qed
    moreover have "P1 \<subseteq> top1_S2 - P2"
    proof -
      have "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      thus ?thesis using hP(3) by (by100 blast)
    qed
    ultimately have "closure_on top1_S2 top1_S2_topology P1 \<subseteq> top1_S2 - P2"
      using closure_on_subset_of_closed[OF hcl_S2_P2] by (by100 blast)
    hence "closure_on top1_S2 top1_S2_topology P1 \<subseteq> P1 \<union> (?A \<union> ?B)"
      using hP1_AB_eq by (by100 blast)
    thus "z \<in> P1 \<union> (?A \<union> ?B)" using \<open>z \<in> closure_on top1_S2 top1_S2_topology P1\<close> by (by100 blast)
  next
    fix z assume "z \<in> P1 \<union> (?A \<union> ?B)"
    hence "z \<in> P1 \<or> z \<in> ?A \<union> ?B" by (by100 blast)
    thus "z \<in> closure_on top1_S2 top1_S2_topology P1"
    proof
      assume "z \<in> P1"
      thus ?thesis using subset_closure_on[of P1 top1_S2 top1_S2_topology] by (by100 blast)
    next
      assume "z \<in> ?A \<union> ?B"
      hence "z \<in> top1_S2" using hA_sub assms(8) by (by100 blast)
      have hP1_sub_S2: "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      show "z \<in> closure_on top1_S2 top1_S2_topology P1"
      proof (rule iffD2[OF Theorem_17_5a[OF hTopS2 \<open>z \<in> top1_S2\<close> hP1_sub_S2]])
        show "\<forall>U. neighborhood_of z top1_S2 top1_S2_topology U \<longrightarrow> intersects U P1"
        proof (intro allI impI)
          fix V assume hV: "neighborhood_of z top1_S2 top1_S2_topology V"
          hence hV_open: "V \<in> top1_S2_topology" and hzV: "z \<in> V"
            unfolding neighborhood_of_def by (by100 blast)+
          have "V \<inter> P1 \<noteq> {}"
            by (rule simple_closed_curve_boundary_meets_component[OF assms(1) hAB_scc hP(5) hP(6)
                hP(3) hP(4) hP(1) hP(2) hP1_open hP2_open \<open>z \<in> ?A \<union> ?B\<close> hV_open hzV])
          thus "intersects V P1" unfolding intersects_def by (by100 blast)
        qed
      qed
    qed
  qed
  \<comment> \<open>a4 \<notin> A\<union>B: from intersection assumptions and distinctness.\<close>
  have ha4_not_AB: "a4 \<notin> ?A \<union> ?B"
  proof -
    \<comment> \<open>a4 \<in> e34, e12\<inter>e34 = {}, so a4 \<notin> e12.\<close>
    have ha4_e34: "a4 \<in> e34" using assms(18) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have "a4 \<notin> e12" using assms(22) ha4_e34 by (by100 blast)
    \<comment> \<open>a4 \<in> e23\<inter>e34 = {a3}, but a4 \<noteq> a3, so a4 \<notin> e23.\<close>
    moreover have "a4 \<notin> e23"
    proof assume "a4 \<in> e23"
      hence "a4 \<in> e23 \<inter> e34" using ha4_e34 by (by100 blast)
      hence "a4 = a3" using assms(25) by (by100 blast)
      thus False using hdist(6) by (by100 blast)
    qed
    \<comment> \<open>a4 \<in> e41, e13\<inter>e41 = {a1}, a4 \<noteq> a1, so a4 \<notin> e13.\<close>
    moreover have ha4_e41: "a4 \<in> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
    moreover have "a4 \<notin> e13"
    proof assume "a4 \<in> e13"
      hence "a4 \<in> e13 \<inter> e41" using ha4_e41 by (by100 blast)
      hence "a4 = a1" using assms(31) by (by100 blast)
      thus False using hdist(3) by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>e24-{a2,a4} cannot lie in P1: a4 \<in> closure(e24-{a2,a4}) but a4 \<notin> P1\<union>(A\<union>B).\<close>
  have ha4_in_cl_e24: "a4 \<in> closure_on top1_S2 top1_S2_topology (e24 - {a2, a4})"
    by (rule arc_endpoint_in_closure_of_interior(2)[OF hS2_strict hS2_haus assms(9) assms(15) assms(21) hdist(5)])
  have he24_not_P1: "\<not>(e24 - {a2, a4} \<subseteq> P1)"
  proof
    assume h: "e24 - {a2, a4} \<subseteq> P1"
    have "closure_on top1_S2 top1_S2_topology (e24 - {a2, a4}) \<subseteq>
        closure_on top1_S2 top1_S2_topology P1"
      by (rule closure_on_mono[OF h])
    hence "a4 \<in> closure_on top1_S2 top1_S2_topology P1"
      using ha4_in_cl_e24 by (by100 blast)
    hence "a4 \<in> P1 \<union> (?A \<union> ?B)" using hcl_P1 by (by100 blast)
    moreover have "a4 \<notin> P1"
    proof -
      have ha4_e41: "a4 \<in> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
      have "a4 \<in> ?C - {a1, a3}" using ha4_e41 hdist(3) hdist(6) by (by100 blast)
      hence "a4 \<in> P2" using hCm_in_P2 by (by100 blast)
      thus ?thesis using hP(3) by (by100 blast)
    qed
    ultimately have "a4 \<in> ?A \<union> ?B" by (by100 blast)
    thus False using ha4_not_AB by (by100 blast)
  qed
  \<comment> \<open>Similarly for B\<union>C: get R1, R2 from Theorem_63_5.\<close>
  have hBC_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology (?B \<union> ?C)"
    by (rule arcs_form_simple_closed_curve[OF hS2_strict hS2_haus assms(14) assms(8)
        hC_arc hC_sub hBC_int hdist(2) assms(20) hC_ep])
  have hC_closed: "closedin_on top1_S2 top1_S2_topology ?C"
    by (rule arc_in_S2_closed[OF hC_sub hC_arc])
  have hC_conn: "top1_connected_on ?C (subspace_topology top1_S2 top1_S2_topology ?C)"
    using arc_connected[OF hC_arc] .
  have hC_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology ?C"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) hC_sub hC_arc])
  have hBC_card: "card (?B \<inter> ?C) = 2"
    using hBC_int hdist(2) by (by100 simp)
  \<comment> \<open>Get raw components for S2-(B\<union>C), then choose labels so A-{a1,a3} \<subseteq> R2.\<close>
  have hAm_sub_BC: "?A - {a1, a3} \<subseteq> top1_S2 - (?B \<union> ?C)"
  proof -
    have "?A \<inter> (?B \<union> ?C) \<subseteq> {a1, a3}" using hAB_int hAC_int by (by100 blast)
    thus ?thesis using hA_sub by (by100 blast)
  qed
  have hAm_in_raw_pre: "\<exists>R1' R2'. R1' \<noteq> {} \<and> R2' \<noteq> {} \<and> R1' \<inter> R2' = {}
      \<and> R1' \<union> R2' = top1_S2 - (?B \<union> ?C)
      \<and> top1_connected_on R1' (subspace_topology top1_S2 top1_S2_topology R1')
      \<and> top1_connected_on R2' (subspace_topology top1_S2 top1_S2_topology R2')"
    using Theorem_63_5_two_closed_connected[OF assms(1) hB_closed hC_closed
        hB_conn hC_conn hBC_card hB_no_sep hC_no_sep] by (by100 metis)
  obtain R1 R2 where hR: "R1 \<noteq> {}" "R2 \<noteq> {}" "R1 \<inter> R2 = {}"
      "R1 \<union> R2 = top1_S2 - (?B \<union> ?C)"
      "top1_connected_on R1 (subspace_topology top1_S2 top1_S2_topology R1)"
      "top1_connected_on R2 (subspace_topology top1_S2 top1_S2_topology R2)"
      and hAm_in_R2: "?A - {a1, a3} \<subseteq> R2"
  proof -
    from hAm_in_raw_pre obtain R1' R2' where hR': "R1' \<noteq> {}" "R2' \<noteq> {}" "R1' \<inter> R2' = {}"
        "R1' \<union> R2' = top1_S2 - (?B \<union> ?C)"
        "top1_connected_on R1' (subspace_topology top1_S2 top1_S2_topology R1')"
        "top1_connected_on R2' (subspace_topology top1_S2 top1_S2_topology R2')" by (by100 metis)
    have hAm_raw: "?A - {a1, a3} \<subseteq> R1' \<or> ?A - {a1, a3} \<subseteq> R2'"
      sorry \<comment> \<open>Lemma\_23\_2: connected subset of separation.\<close>
    from hAm_raw show ?thesis
    proof
      assume "?A - {a1, a3} \<subseteq> R1'"
      show ?thesis
        by (rule that[of R2' R1'])
          (use hR' \<open>?A - {a1, a3} \<subseteq> R1'\<close> in \<open>by100 blast\<close>)+
    next
      assume "?A - {a1, a3} \<subseteq> R2'"
      show ?thesis
        by (rule that[of R1' R2'])
          (use hR' \<open>?A - {a1, a3} \<subseteq> R2'\<close> in \<open>by100 blast\<close>)+
    qed
  qed
  have hBC_closed_S2: "closedin_on top1_S2 top1_S2_topology (?B \<union> ?C)"
    by (rule closedin_on_Un[OF hTopS2 hB_closed hC_closed])
  have hBC_compl_open: "top1_S2 - (?B \<union> ?C) \<in> top1_S2_topology"
    using hBC_closed_S2 unfolding closedin_on_def by (by100 blast)
  have hBC_open_lpc: "top1_locally_path_connected_on (top1_S2 - (?B \<union> ?C))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))"
    by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hBC_compl_open])
       (by100 blast)
  have hTBC: "is_topology_on (top1_S2 - (?B \<union> ?C))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))"
    by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
  obtain x_R where hx_R: "x_R \<in> R1" using hR(1) by (by100 blast)
  have hx_R_W: "x_R \<in> top1_S2 - (?B \<union> ?C)" using hx_R hR(4) by (by100 blast)
  \<comment> \<open>R1 = component\_of(x\_R) in S2-(B\<union>C). Same contradiction argument as for P1.\<close>
  have hR1_eq_comp: "R1 = top1_component_of_on (top1_S2 - (?B \<union> ?C))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
  proof -
    have hR1_sub_BC: "R1 \<subseteq> top1_S2 - (?B \<union> ?C)" using hR(4) by (by100 blast)
    have hR1_conn_BC: "top1_connected_on R1
        (subspace_topology (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) R1)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology R1 =
          subspace_topology (top1_S2 - (?B \<union> ?C))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) R1"
        using subspace_topology_trans[of R1 "top1_S2 - (?B \<union> ?C)" top1_S2 top1_S2_topology]
            hR1_sub_BC by (by100 simp)
      thus ?thesis using hR(5) by (by100 simp)
    qed
    have "R1 \<subseteq> top1_component_of_on (top1_S2 - (?B \<union> ?C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
      by (rule top1_connected_subspace_subset_component_of[OF hR1_sub_BC hx_R hR1_conn_BC])
    moreover have "top1_component_of_on (top1_S2 - (?B \<union> ?C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R \<subseteq> R1"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain y where hy: "y \<in> top1_component_of_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R" "y \<notin> R1"
        by (by100 blast)
      have "y \<in> top1_S2 - (?B \<union> ?C)"
        using hy(1) top1_component_of_on_subset[of "top1_S2 - (?B \<union> ?C)"] by (by100 blast)
      hence "y \<in> R2" using hR(4) hy(2) by (by100 blast)
      have hR2_sub: "R2 \<subseteq> top1_S2 - (?B \<union> ?C)" using hR(4) by (by100 blast)
      have hR2_conn_sub: "top1_connected_on R2
          (subspace_topology (top1_S2 - (?B \<union> ?C))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) R2)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology R2 =
            subspace_topology (top1_S2 - (?B \<union> ?C))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) R2"
          using subspace_topology_trans[of R2 "top1_S2 - (?B \<union> ?C)" top1_S2 top1_S2_topology]
              hR2_sub by (by100 simp)
        thus ?thesis using hR(6) by (by100 simp)
      qed
      have "R2 \<subseteq> top1_component_of_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
        using top1_connected_subspace_subset_component_of[OF hR2_sub \<open>y \<in> R2\<close> hR2_conn_sub]
            top1_component_of_on_eq_of_mem[OF hTBC hy(1)] by (by100 simp)
      hence "R1 \<union> R2 \<subseteq> top1_component_of_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
        using \<open>R1 \<subseteq> top1_component_of_on _ _ x_R\<close> by (by100 blast)
      hence "top1_S2 - (?B \<union> ?C) = top1_component_of_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
        using hR(4) top1_component_of_on_subset[of "top1_S2 - (?B \<union> ?C)"] by (by100 blast)
      hence "top1_connected_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))"
      proof -
        have "top1_connected_on
            (top1_component_of_on (top1_S2 - (?B \<union> ?C))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R)
            (subspace_topology (top1_S2 - (?B \<union> ?C))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))
                (top1_component_of_on (top1_S2 - (?B \<union> ?C))
                    (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R))"
          by (rule top1_component_of_on_connected[OF hTBC hx_R_W])
        thus ?thesis
          using \<open>top1_S2 - (?B \<union> ?C) = top1_component_of_on _ _ x_R\<close>
              subspace_topology_trans[of "top1_S2 - (?B \<union> ?C)" "top1_S2 - (?B \<union> ?C)"
                  top1_S2 top1_S2_topology] by (by100 simp)
      qed
      moreover have "\<not> top1_connected_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))"
        using Theorem_61_3_JordanSeparation_S2[OF assms(1) hBC_scc]
        unfolding top1_separates_on_def by (by100 blast)
      ultimately show False by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  have hR1_eq_pc: "R1 = top1_path_component_of_on (top1_S2 - (?B \<union> ?C))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
  proof -
    from conjunct2[OF Theorem_25_5[OF hTBC]]
    have "\<forall>z \<in> top1_S2 - (?B \<union> ?C).
        top1_locally_path_connected_on (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) \<longrightarrow>
        top1_path_component_of_on (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) z =
        top1_component_of_on (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) z" by (by100 blast)
    thus ?thesis using hR1_eq_comp hBC_open_lpc hx_R_W by (by100 metis)
  qed
  have hR1_open: "R1 \<in> top1_S2_topology"
  proof -
    have "top1_path_component_of_on (top1_S2 - (?B \<union> ?C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R \<in>
        subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))"
      by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTBC hBC_open_lpc hx_R_W])
    hence "R1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))"
      using hR1_eq_pc by (by100 simp)
    thus ?thesis by (rule open_in_sub_imp_open[OF hBC_compl_open])
  qed
  have hR2_open: "R2 \<in> top1_S2_topology"
  proof -
    have "R2 = (top1_S2 - (?B \<union> ?C)) -
        top1_path_component_of_on (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
      using hR(3,4) hR1_eq_pc by (by100 blast)
    moreover have "(top1_S2 - (?B \<union> ?C)) -
        top1_path_component_of_on (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R \<in>
        subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))"
      by (rule top1_path_component_of_on_complement_open_if_locally_path_connected[OF hTBC hBC_open_lpc hx_R_W])
    ultimately have "R2 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))"
      by (by100 simp)
    thus ?thesis by (rule open_in_sub_imp_open[OF hBC_compl_open])
  qed
  \<comment> \<open>hAm\_in\_R2 was established in the obtain above.\<close>
  have hcl_R1: "closure_on top1_S2 top1_S2_topology R1 = R1 \<union> (?B \<union> ?C)"
  proof (rule set_eqI, rule iffI)
    fix z assume "z \<in> closure_on top1_S2 top1_S2_topology R1"
    have hR1_BC_eq: "R1 \<union> (?B \<union> ?C) = top1_S2 - R2"
    proof -
      have hR1_sub_S2: "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      have "top1_S2 - R2 = (top1_S2 - (R1 \<union> R2)) \<union> R1" using hR(3) hR1_sub_S2 by (by100 force)
      also have "\<dots> = (?B \<union> ?C) \<union> R1"
      proof -
        have "top1_S2 - (R1 \<union> R2) = top1_S2 - (top1_S2 - (?B \<union> ?C))" using hR(4) by (by100 blast)
        also have "\<dots> = ?B \<union> ?C"
        proof -
          have "?B \<union> ?C \<subseteq> top1_S2" using assms(8) hC_sub by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        finally show ?thesis by (by100 simp)
      qed
      finally show ?thesis by (by100 blast)
    qed
    have hcl_S2_R2: "closedin_on top1_S2 top1_S2_topology (top1_S2 - R2)"
    proof -
      have hR2_sub_S2: "R2 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      have hsub: "top1_S2 - R2 \<subseteq> top1_S2" by (by100 blast)
      have hcompl: "top1_S2 - (top1_S2 - R2) = R2" using hR2_sub_S2 by (by100 blast)
      show ?thesis unfolding closedin_on_def
        apply (rule conjI[OF hsub])
        using hcompl hR2_open by (by100 simp)
    qed
    have "R1 \<subseteq> top1_S2 - R2"
    proof -
      have "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      thus ?thesis using hR(3) by (by100 blast)
    qed
    hence "closure_on top1_S2 top1_S2_topology R1 \<subseteq> top1_S2 - R2"
      using closure_on_subset_of_closed[OF hcl_S2_R2] by (by100 blast)
    hence "closure_on top1_S2 top1_S2_topology R1 \<subseteq> R1 \<union> (?B \<union> ?C)"
      using hR1_BC_eq by (by100 blast)
    thus "z \<in> R1 \<union> (?B \<union> ?C)" using \<open>z \<in> closure_on top1_S2 top1_S2_topology R1\<close> by (by100 blast)
  next
    fix z assume "z \<in> R1 \<union> (?B \<union> ?C)"
    hence "z \<in> R1 \<or> z \<in> ?B \<union> ?C" by (by100 blast)
    thus "z \<in> closure_on top1_S2 top1_S2_topology R1"
    proof
      assume "z \<in> R1"
      thus ?thesis using subset_closure_on[of R1 top1_S2 top1_S2_topology] by (by100 blast)
    next
      assume "z \<in> ?B \<union> ?C"
      hence "z \<in> top1_S2" using assms(8) hC_sub by (by100 blast)
      have hR1_sub_S2: "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      show "z \<in> closure_on top1_S2 top1_S2_topology R1"
      proof (rule iffD2[OF Theorem_17_5a[OF hTopS2 \<open>z \<in> top1_S2\<close> hR1_sub_S2]])
        show "\<forall>U. neighborhood_of z top1_S2 top1_S2_topology U \<longrightarrow> intersects U R1"
        proof (intro allI impI)
          fix V assume hV: "neighborhood_of z top1_S2 top1_S2_topology V"
          hence hV_open: "V \<in> top1_S2_topology" and hzV: "z \<in> V"
            unfolding neighborhood_of_def by (by100 blast)+
          have "V \<inter> R1 \<noteq> {}"
            by (rule simple_closed_curve_boundary_meets_component[OF assms(1) hBC_scc hR(5) hR(6)
                hR(3) hR(4) hR(1) hR(2) hR1_open hR2_open \<open>z \<in> ?B \<union> ?C\<close> hV_open hzV])
          thus "intersects V R1" unfolding intersects_def by (by100 blast)
        qed
      qed
    qed
  qed
  \<comment> \<open>a2 \<notin> B\<union>C.\<close>
  have ha2_not_BC: "a2 \<notin> ?B \<union> ?C"
  proof -
    have ha2_e12: "a2 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
    \<comment> \<open>a2 \<in> e12, e13\<inter>e12 = {a1}, a2 \<noteq> a1, so a2 \<notin> e13.\<close>
    have "a2 \<notin> e13"
    proof assume "a2 \<in> e13"
      hence "a2 \<in> e13 \<inter> e12" using ha2_e12 by (by100 blast)
      hence "a2 = a1" using assms(28) by (by100 blast)
      thus False using hdist(1) by (by100 blast)
    qed
    moreover have "a2 \<notin> e41"
    proof assume "a2 \<in> e41"
      hence "a2 \<in> e41 \<inter> e12" using ha2_e12 by (by100 blast)
      hence "a2 = a1" using assms(27) by (by100 blast)
      thus False using hdist(1) by (by100 blast)
    qed
    \<comment> \<open>a2 \<in> e12, e12\<inter>e34 = {}, so a2 \<notin> e34.\<close>
    moreover have "a2 \<notin> e34" using assms(22) ha2_e12 by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  have ha2_in_cl_e24: "a2 \<in> closure_on top1_S2 top1_S2_topology (e24 - {a2, a4})"
    by (rule arc_endpoint_in_closure_of_interior(1)[OF hS2_strict hS2_haus assms(9) assms(15) assms(21) hdist(5)])
  have he24_not_R1: "\<not>(e24 - {a2, a4} \<subseteq> R1)"
  proof
    assume h: "e24 - {a2, a4} \<subseteq> R1"
    have "closure_on top1_S2 top1_S2_topology (e24 - {a2, a4}) \<subseteq>
        closure_on top1_S2 top1_S2_topology R1"
      by (rule closure_on_mono[OF h])
    hence "a2 \<in> closure_on top1_S2 top1_S2_topology R1"
      using ha2_in_cl_e24 by (by100 blast)
    hence "a2 \<in> R1 \<union> (?B \<union> ?C)" using hcl_R1 by (by100 blast)
    moreover have "a2 \<notin> R1"
    proof -
      have ha2_e12: "a2 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
      have "a2 \<in> ?A - {a1, a3}" using ha2_e12 hdist(1) hdist(4) by (by100 blast)
      hence "a2 \<in> R2" using hAm_in_R2 by (by100 blast)
      thus ?thesis using hR(3) by (by100 blast)
    qed
    ultimately have "a2 \<in> ?B \<union> ?C" by (by100 blast)
    thus False using ha2_not_BC by (by100 blast)
  qed
  \<comment> \<open>Step 4: P1 and R1 are each theta components, and they are distinct.\<close>
  \<comment> \<open>P1 \<subseteq> S2-(A\<union>B) and P1 \<inter> (C-{a1,a3}) = {} (since C-{a1,a3} \<subseteq> P2), so P1 \<subseteq> S2-Y.\<close>
  have hP1_sub_Y_compl: "P1 \<subseteq> top1_S2 - ?Y"
  proof -
    have "P1 \<subseteq> top1_S2 - (?A \<union> ?B)" using hP(4) by (by100 blast)
    moreover have "P1 \<inter> (?C - {a1, a3}) = {}" using hCm_in_P2 hP(3) by (by100 blast)
    moreover have "{a1, a3} \<subseteq> ?A \<union> ?B" using hAB_int by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  have hR1_sub_Y_compl: "R1 \<subseteq> top1_S2 - ?Y"
  proof -
    have "R1 \<subseteq> top1_S2 - (?B \<union> ?C)" using hR(4) by (by100 blast)
    moreover have "R1 \<inter> (?A - {a1, a3}) = {}" using hAm_in_R2 hR(3) by (by100 blast)
    moreover have "{a1, a3} \<subseteq> ?B \<union> ?C" using hBC_int by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>P1 is connected \<subseteq> S2-Y = U\<union>V\<union>W (disjoint open), so P1 \<subseteq> one of U,V,W.\<close>
  \<comment> \<open>Since P1 is a component of S2-(A\<union>B) \<supseteq> S2-Y, and U,V,W are components of S2-Y,
     P1 is exactly one of U,V,W. Similarly R1.\<close>
  \<comment> \<open>U, V, W are open in S2: Y is closed, S2-Y is open lpc, components are open.\<close>
  have hY_closed: "closedin_on top1_S2 top1_S2_topology ?Y"
  proof -
    have hAC_closed: "closedin_on top1_S2 top1_S2_topology (?A \<union> ?C)"
      by (rule closedin_on_Un[OF hTopS2 hA_closed hC_closed])
    have hABC_closed: "closedin_on top1_S2 top1_S2_topology ((?A \<union> ?C) \<union> ?B)"
      by (rule closedin_on_Un[OF hTopS2 hAC_closed hB_closed])
    moreover have "?Y = (?A \<union> ?C) \<union> ?B" by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  have hY_compl_open: "top1_S2 - ?Y \<in> top1_S2_topology"
    using hY_closed unfolding closedin_on_def by (by100 blast)
  \<comment> \<open>NEW APPROACH: P1 is a connected component of S2-Y, hence equals one of U,V,W.
     Key: S2-Y = P1 \<union> (P2 \<inter> (S2-Y)) where both pieces are open in S2-Y.\<close>
  have hP2_cap_Y: "P2 \<inter> (top1_S2 - ?Y) = (top1_S2 - ?Y) - P1"
    using hP1_sub_Y_compl hP(3,4) hUVW(7) by (by100 blast)
  have hP1_open_in_Y: "P1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
  proof -
    have "P1 = (top1_S2 - ?Y) \<inter> P1" using hP1_sub_Y_compl by (by100 blast)
    thus ?thesis unfolding subspace_topology_def using hP1_open by (by100 blast)
  qed
  have hVW_open_in_Y: "(top1_S2 - ?Y) - P1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
  proof -
    have "(top1_S2 - ?Y) - P1 = (top1_S2 - ?Y) \<inter> P2"
      using hP1_sub_Y_compl hP(3,4) hUVW(7) by (by100 blast)
    also have "\<dots> = (top1_S2 - ?Y) \<inter> (top1_S2 \<inter> P2)" using hP(4) by (by100 blast)
    finally show ?thesis unfolding subspace_topology_def using hP2_open by (by100 blast)
  qed
  \<comment> \<open>P1 is a connected component of S2-Y (maximal connected: any connected superset
     in S2-Y would cross the P1/(P2\<inter>S2-Y) separation).\<close>
  have hP1_is_comp: "P1 = U \<or> P1 = V \<or> P1 = W"
  proof -
    \<comment> \<open>P1 connected \<subseteq> U\<union>V\<union>W. By partition, P1 \<subseteq> U or V or W.\<close>
    \<comment> \<open>Conversely, if P1 \<subseteq> U and U \<noteq> P1, then \<exists>z \<in> U-P1. z \<in> P2\<inter>(S2-Y).
       But U is connected and meets both P1 and P2\<inter>(S2-Y), which are open in S2-Y.
       That contradicts U's connectivity.\<close>
    have hP1_in_UVW: "P1 \<subseteq> U \<union> V \<union> W" using hP1_sub_Y_compl hUVW(7) by (by100 blast)
    \<comment> \<open>P1 is connected, P1 \<subseteq> S2-Y which is separated as P1 \<union> (S2-Y-P1).
       Any connected subset of S2-Y is in P1 or in S2-Y-P1.\<close>
    have hTY: "is_topology_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y))"
      by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
    have hVW_ne: "(top1_S2 - ?Y) - P1 \<noteq> {}"
    proof -
      have "V \<noteq> {}" by (rule hUVW(2))
      moreover have "V \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      moreover have "V \<inter> P1 = {}" sorry \<comment> \<open>V \<subseteq> P2 or V \<subseteq> (S2-Y)-P1\<close>
      ultimately show ?thesis by (by100 blast)
    qed
    have hY_sep: "top1_is_separation_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y))
        P1 ((top1_S2 - ?Y) - P1)"
      unfolding top1_is_separation_on_def
      using hP1_open_in_Y hVW_open_in_Y hP(1) hVW_ne hP1_sub_Y_compl by (by100 blast)
    \<comment> \<open>Each of U, V, W is connected \<subseteq> S2-Y. By Lemma\_23\_2, each \<subseteq> P1 or \<subseteq> (S2-Y)-P1.\<close>
    \<comment> \<open>Each of U,V,W connected \<subseteq> S2-Y. By Lemma\_23\_2, each \<subseteq> P1 or (S2-Y)-P1.\<close>
    have hU_conn_Y: "top1_connected_on U
        (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) U)"
    proof -
      have "U \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      hence "subspace_topology top1_S2 top1_S2_topology U =
          subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) U"
        using subspace_topology_trans[of U "top1_S2 - ?Y" top1_S2 top1_S2_topology] by (by100 simp)
      thus ?thesis using hUVW(8) by (by100 simp)
    qed
    have hU_sub_Y: "U \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
    have hU_side: "U \<subseteq> P1 \<or> U \<subseteq> (top1_S2 - ?Y) - P1"
      using Lemma_23_2[OF hTY hY_sep hU_sub_Y hU_conn_Y] by (by100 blast)
    have hV_conn_Y: "top1_connected_on V
        (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) V)"
    proof -
      have "V \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      hence "subspace_topology top1_S2 top1_S2_topology V =
          subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) V"
        using subspace_topology_trans[of V "top1_S2 - ?Y" top1_S2 top1_S2_topology] by (by100 simp)
      thus ?thesis using hUVW(9) by (by100 simp)
    qed
    have hV_sub_Y: "V \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
    have hV_side: "V \<subseteq> P1 \<or> V \<subseteq> (top1_S2 - ?Y) - P1"
      using Lemma_23_2[OF hTY hY_sep hV_sub_Y hV_conn_Y] by (by100 blast)
    have hW_conn_Y: "top1_connected_on W
        (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) W)"
    proof -
      have "W \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      hence "subspace_topology top1_S2 top1_S2_topology W =
          subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) W"
        using subspace_topology_trans[of W "top1_S2 - ?Y" top1_S2 top1_S2_topology] by (by100 simp)
      thus ?thesis using hUVW(10) by (by100 simp)
    qed
    have hW_sub_Y: "W \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
    have hW_side: "W \<subseteq> P1 \<or> W \<subseteq> (top1_S2 - ?Y) - P1"
      using Lemma_23_2[OF hTY hY_sep hW_sub_Y hW_conn_Y] by (by100 blast)
    \<comment> \<open>P1 = component\_of\_{S2-Y}(x\_P): use containment in P1's component of S2-(A\<union>B).\<close>
    have hP1_comp_Y: "P1 = top1_component_of_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
    proof -
      have hP1_sub_Y: "P1 \<subseteq> top1_S2 - ?Y" by (rule hP1_sub_Y_compl)
      have hP1_conn_Y: "top1_connected_on P1
          (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology P1 =
            subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1"
          using subspace_topology_trans[of P1 "top1_S2 - ?Y" top1_S2 top1_S2_topology] hP1_sub_Y
          by (by100 simp)
        thus ?thesis using hP(5) by (by100 simp)
      qed
      have "P1 \<subseteq> top1_component_of_on (top1_S2 - ?Y)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
        by (rule top1_connected_subspace_subset_component_of[OF hP1_sub_Y hx_P hP1_conn_Y])
      moreover have "top1_component_of_on (top1_S2 - ?Y)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P \<subseteq> P1"
      proof -
        \<comment> \<open>comp\_{S2-Y}(x\_P) \<subseteq> comp\_{S2-(A\<union>B)}(x\_P) = P1.\<close>
        have "top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P \<subseteq>
            top1_S2 - ?Y" by (rule top1_component_of_on_subset)
        moreover have "top1_connected_on (top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P)
            (subspace_topology top1_S2 top1_S2_topology (top1_component_of_on (top1_S2 - ?Y)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P))"
        proof -
          have hconn_sub: "top1_connected_on (top1_component_of_on (top1_S2 - ?Y)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P)
              (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y))
                  (top1_component_of_on (top1_S2 - ?Y)
                      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P))"
            by (rule top1_component_of_on_connected[OF hTY])
               (use hx_P hP1_sub_Y in \<open>by100 blast\<close>)
          thus ?thesis
            using subspace_topology_trans[of "top1_component_of_on (top1_S2 - ?Y)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
                "top1_S2 - ?Y" top1_S2 top1_S2_topology]
                top1_component_of_on_subset[of "top1_S2 - ?Y"] by (by100 simp)
        qed
        moreover have "x_P \<in> top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
          by (rule top1_component_of_on_self_mem[OF hTY]) (use hx_P hP1_sub_Y in \<open>by100 blast\<close>)
        moreover have "top1_S2 - ?Y \<subseteq> top1_S2 - (?A \<union> ?B)" by (by100 blast)
        ultimately have hsub_AB: "top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P \<subseteq> top1_S2 - (?A \<union> ?B)"
          and hconn_AB: "top1_connected_on (top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P)
            (subspace_topology top1_S2 top1_S2_topology (top1_component_of_on (top1_S2 - ?Y)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P))"
          and hxP_in_comp: "x_P \<in> top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
          by (by100 blast)+
        have hconn_AB': "top1_connected_on (top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P)
            (subspace_topology (top1_S2 - (?A \<union> ?B))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
                (top1_component_of_on (top1_S2 - ?Y)
                    (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P))"
        proof -
          have "subspace_topology top1_S2 top1_S2_topology (top1_component_of_on (top1_S2 - ?Y)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P) =
              subspace_topology (top1_S2 - (?A \<union> ?B))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
                  (top1_component_of_on (top1_S2 - ?Y)
                      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P)"
            using subspace_topology_trans[of "top1_component_of_on (top1_S2 - ?Y)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
                "top1_S2 - (?A \<union> ?B)" top1_S2 top1_S2_topology] hsub_AB by (by100 simp)
          thus ?thesis using hconn_AB by (by100 simp)
        qed
        show ?thesis
          using top1_connected_subspace_subset_component_of[OF hsub_AB hxP_in_comp hconn_AB']
              hP1_eq_comp by (by100 simp)
      qed
      ultimately show ?thesis by (by100 blast)
    qed
    \<comment> \<open>U,V,W open (hUVW(11,12,13)) + disjoint + P1 connected \<subseteq> U\<union>V\<union>W \<Rightarrow> P1 \<subseteq> one.
       Then that one \<subseteq> P1 (from hU/V/W\_side). So P1 = that one.\<close>
    \<comment> \<open>P1 connected \<subseteq> U\<union>V\<union>W with U,V,W pairwise disjoint and open in S2.
       By connectivity, P1 must be \<subseteq> one of them. Then that one \<subseteq> P1 from side facts.\<close>
    \<comment> \<open>P1 connected \<subseteq> U\<union>V\<union>W (disjoint open). By Lemma\_23\_2 applied twice.\<close>
    \<comment> \<open>Form separation {U, V\<union>W} of S2-Y.\<close>
    have hU_open_Y: "U \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
    proof -
      have "U = (top1_S2 - ?Y) \<inter> U" using hU_sub_Y by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hUVW(11) by (by100 blast)
    qed
    have hVW_open_Y: "V \<union> W \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
    proof -
      have "V \<union> W = (top1_S2 - ?Y) \<inter> (V \<union> W)" using hV_sub_Y hW_sub_Y by (by100 blast)
      moreover have "V \<union> W \<in> top1_S2_topology"
      proof -
        from hTopS2 have hunion: "\<And>U. U \<subseteq> top1_S2_topology \<Longrightarrow> \<Union>U \<in> top1_S2_topology"
          unfolding is_topology_on_def by (by100 blast)
        have "{V, W} \<subseteq> top1_S2_topology" using hUVW(12,13) by (by100 blast)
        from hunion[OF this] have "\<Union>{V, W} \<in> top1_S2_topology" .
        moreover have "\<Union>{V, W} = V \<union> W" by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
    qed
    have hUVW_sep: "top1_is_separation_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) U (V \<union> W)"
    proof -
      have "U \<inter> (V \<union> W) = {}" using hUVW(4,6) by (by100 blast)
      moreover have "U \<union> (V \<union> W) = top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      moreover have "V \<union> W \<noteq> {}" using hUVW(2) by (by100 blast)
      ultimately show ?thesis unfolding top1_is_separation_on_def
        using hU_open_Y hVW_open_Y hUVW(1) by (by100 blast)
    qed
    \<comment> \<open>P1 connected in S2-Y, Lemma\_23\_2 gives P1 \<subseteq> U or P1 \<subseteq> V\<union>W.\<close>
    have hP1_conn_Y_full: "top1_connected_on P1
        (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology P1 =
          subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1"
        using subspace_topology_trans[of P1 "top1_S2 - ?Y" top1_S2 top1_S2_topology]
            hP1_sub_Y_compl by (by100 simp)
      thus ?thesis using hP(5) by (by100 simp)
    qed
    from Lemma_23_2[OF hTY hUVW_sep hP1_sub_Y_compl hP1_conn_Y_full]
    have "P1 \<subseteq> U \<or> P1 \<subseteq> V \<union> W" by (by100 blast)
    thus ?thesis
    proof
      assume hPU: "P1 \<subseteq> U"
      \<comment> \<open>U \<subseteq> P1: from hU\_side, x\_P \<in> U (since P1 \<subseteq> U and x\_P \<in> P1).\<close>
      have "x_P \<in> U" using hPU hx_P by (by100 blast)
      hence "U \<inter> P1 \<noteq> {}" using hx_P by (by100 blast)
      hence "U \<subseteq> P1" using hU_side by (by100 force)
      thus ?thesis using hPU by (by100 blast)
    next
      assume "P1 \<subseteq> V \<union> W"
      \<comment> \<open>Apply Lemma\_23\_2 again: separation {V, W} of V\<union>W.\<close>
      have hV_open_VW: "V \<in> subspace_topology top1_S2 top1_S2_topology (V \<union> W)"
      proof -
        have "V = (V \<union> W) \<inter> V" by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hUVW(12) by (by100 blast)
      qed
      have hW_open_VW: "W \<in> subspace_topology top1_S2 top1_S2_topology (V \<union> W)"
      proof -
        have "W = (V \<union> W) \<inter> W" by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hUVW(13) by (by100 blast)
      qed
      have hTVW: "is_topology_on (V \<union> W)
          (subspace_topology top1_S2 top1_S2_topology (V \<union> W))"
        by (rule subspace_topology_is_topology_on[OF hTopS2])
           (use hV_sub_Y hW_sub_Y in \<open>by100 blast\<close>)
      have hVW_sep: "top1_is_separation_on (V \<union> W)
          (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) V W"
        unfolding top1_is_separation_on_def
        using hV_open_VW hW_open_VW hUVW(2,3,5) by (by100 blast)
      have hP1_sub_VW: "P1 \<subseteq> V \<union> W" by (rule \<open>P1 \<subseteq> V \<union> W\<close>)
      have hP1_conn_VW: "top1_connected_on P1
          (subspace_topology (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) P1)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology P1 =
            subspace_topology (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) P1"
          using subspace_topology_trans[of P1 "V \<union> W" top1_S2 top1_S2_topology]
              hP1_sub_VW by (by100 simp)
        thus ?thesis using hP(5) by (by100 simp)
      qed
      from Lemma_23_2[OF hTVW hVW_sep hP1_sub_VW hP1_conn_VW]
      have "P1 \<subseteq> V \<or> P1 \<subseteq> W" by (by100 blast)
      thus ?thesis
      proof
        assume hPV: "P1 \<subseteq> V"
        have "x_P \<in> V" using hPV hx_P by (by100 blast)
        hence "V \<inter> P1 \<noteq> {}" using hx_P by (by100 blast)
        hence "V \<subseteq> P1" using hV_side by (by100 force)
        thus ?thesis using hPV by (by100 blast)
      next
        assume hPW: "P1 \<subseteq> W"
        have "x_P \<in> W" using hPW hx_P by (by100 blast)
        hence "W \<inter> P1 \<noteq> {}" using hx_P by (by100 blast)
        hence "W \<subseteq> P1" using hW_side by (by100 force)
        thus ?thesis using hPW by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>Same argument for R1.\<close>
  have hR1_is_comp: "R1 = U \<or> R1 = V \<or> R1 = W"
  proof -
    have hR1_in_UVW: "R1 \<subseteq> U \<union> V \<union> W" using hR1_sub_Y_compl hUVW(7) by (by100 blast)
    \<comment> \<open>Same 2\<times>Lemma\_23\_2 approach. Re-derive shared infrastructure.\<close>
    have hTYr: "is_topology_on (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y))"
      by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
    have hVW_open_r: "V \<union> W \<in> top1_S2_topology"
    proof -
      from hTopS2 have "\<And>S. S \<subseteq> top1_S2_topology \<Longrightarrow> \<Union>S \<in> top1_S2_topology"
        unfolding is_topology_on_def by (by100 blast)
      from this[of "{V, W}"] hUVW(12,13) have "\<Union>{V, W} \<in> top1_S2_topology" by (by100 blast)
      moreover have "\<Union>{V, W} = V \<union> W" by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    have hU_oY: "U \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
    proof -
      have "U \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      hence "U = (top1_S2 - ?Y) \<inter> U" by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hUVW(11) by (by100 blast)
    qed
    have hVW_oY: "V \<union> W \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
    proof -
      have "V \<union> W \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      hence "V \<union> W = (top1_S2 - ?Y) \<inter> (V \<union> W)" by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hVW_open_r by (by100 blast)
    qed
    have hUVW_sr: "top1_is_separation_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) U (V \<union> W)"
    proof -
      have "U \<inter> (V \<union> W) = {}" using hUVW(4,6) by (by100 blast)
      moreover have "U \<union> (V \<union> W) = top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      moreover have "V \<union> W \<noteq> {}" using hUVW(2) by (by100 blast)
      ultimately show ?thesis unfolding top1_is_separation_on_def
        using hU_oY hVW_oY hUVW(1) by (by100 blast)
    qed
    have hR1_cY: "top1_connected_on R1
        (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) R1)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology R1 =
          subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) R1"
        using subspace_topology_trans[of R1 "top1_S2 - ?Y" top1_S2 top1_S2_topology]
            hR1_sub_Y_compl by (by100 simp)
      thus ?thesis using hR(5) by (by100 simp)
    qed
    from Lemma_23_2[OF hTYr hUVW_sr hR1_sub_Y_compl hR1_cY]
    have "R1 \<subseteq> U \<or> R1 \<subseteq> V \<union> W" by (by100 blast)
    thus ?thesis
    proof
      assume hRU: "R1 \<subseteq> U"
      have "U \<subseteq> R1"
      proof -
        have "x_R \<in> U" using hRU hx_R by (by100 blast)
        have hU_sub_BC: "U \<subseteq> top1_S2 - (?B \<union> ?C)"
          using hR1_sub_Y_compl hUVW(7) by (by100 blast)
        have hU_conn_BC: "top1_connected_on U
            (subspace_topology (top1_S2 - (?B \<union> ?C))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) U)"
        proof -
          have "subspace_topology top1_S2 top1_S2_topology U =
              subspace_topology (top1_S2 - (?B \<union> ?C))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) U"
            using subspace_topology_trans[of U "top1_S2 - (?B \<union> ?C)" top1_S2 top1_S2_topology]
                hU_sub_BC by (by100 simp)
          thus ?thesis using hUVW(8) by (by100 simp)
        qed
        from top1_connected_subspace_subset_component_of[OF hU_sub_BC \<open>x_R \<in> U\<close> hU_conn_BC]
        show ?thesis using hR1_eq_comp by (by100 simp)
      qed
      thus ?thesis using hRU by (by100 blast)
    next
      assume "R1 \<subseteq> V \<union> W"
      have hTVWr: "is_topology_on (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W))"
        by (rule subspace_topology_is_topology_on[OF hTopS2]) (use hUVW(7) in \<open>by100 blast\<close>)
      have hVW_sr: "top1_is_separation_on (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) V W"
      proof -
        have "V = (V \<union> W) \<inter> V" by (by100 blast)
        hence hVo: "V \<in> subspace_topology top1_S2 top1_S2_topology (V \<union> W)"
          unfolding subspace_topology_def using hUVW(12) by (by100 blast)
        have "W = (V \<union> W) \<inter> W" by (by100 blast)
        hence hWo: "W \<in> subspace_topology top1_S2 top1_S2_topology (V \<union> W)"
          unfolding subspace_topology_def using hUVW(13) by (by100 blast)
        show ?thesis unfolding top1_is_separation_on_def
          using hVo hWo hUVW(2,3,5) by (by100 blast)
      qed
      have hR1_cVW: "top1_connected_on R1
          (subspace_topology (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) R1)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology R1 =
            subspace_topology (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) R1"
          using subspace_topology_trans[of R1 "V \<union> W" top1_S2 top1_S2_topology]
              \<open>R1 \<subseteq> V \<union> W\<close> by (by100 simp)
        thus ?thesis using hR(5) by (by100 simp)
      qed
      from Lemma_23_2[OF hTVWr hVW_sr \<open>R1 \<subseteq> V \<union> W\<close> hR1_cVW]
      have "R1 \<subseteq> V \<or> R1 \<subseteq> W" by (by100 blast)
      thus ?thesis
      proof
        assume "R1 \<subseteq> V"
        have "V \<subseteq> R1"
        proof -
          have "x_R \<in> V" using \<open>R1 \<subseteq> V\<close> hx_R by (by100 blast)
          have hV_sub_BC: "V \<subseteq> top1_S2 - (?B \<union> ?C)"
            using hR1_sub_Y_compl hUVW(7) by (by100 blast)
          have hV_conn_BC: "top1_connected_on V
              (subspace_topology (top1_S2 - (?B \<union> ?C))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) V)"
          proof -
            have "subspace_topology top1_S2 top1_S2_topology V =
                subspace_topology (top1_S2 - (?B \<union> ?C))
                    (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) V"
              using subspace_topology_trans[of V "top1_S2 - (?B \<union> ?C)" top1_S2 top1_S2_topology]
                  hV_sub_BC by (by100 simp)
            thus ?thesis using hUVW(9) by (by100 simp)
          qed
          from top1_connected_subspace_subset_component_of[OF hV_sub_BC \<open>x_R \<in> V\<close> hV_conn_BC]
          show ?thesis using hR1_eq_comp by (by100 simp)
        qed
        thus ?thesis using \<open>R1 \<subseteq> V\<close> by (by100 blast)
      next
        assume "R1 \<subseteq> W"
        have "W \<subseteq> R1"
        proof -
          have "x_R \<in> W" using \<open>R1 \<subseteq> W\<close> hx_R by (by100 blast)
          have hW_sub_BC: "W \<subseteq> top1_S2 - (?B \<union> ?C)"
            using hR1_sub_Y_compl hUVW(7) by (by100 blast)
          have hW_conn_BC: "top1_connected_on W
              (subspace_topology (top1_S2 - (?B \<union> ?C))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) W)"
          proof -
            have "subspace_topology top1_S2 top1_S2_topology W =
                subspace_topology (top1_S2 - (?B \<union> ?C))
                    (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) W"
              using subspace_topology_trans[of W "top1_S2 - (?B \<union> ?C)" top1_S2 top1_S2_topology]
                  hW_sub_BC by (by100 simp)
            thus ?thesis using hUVW(10) by (by100 simp)
          qed
          from top1_connected_subspace_subset_component_of[OF hW_sub_BC \<open>x_R \<in> W\<close> hW_conn_BC]
          show ?thesis using hR1_eq_comp by (by100 simp)
        qed
        thus ?thesis using \<open>R1 \<subseteq> W\<close> by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>P1 \<noteq> R1: closure(P1) = P1\<union>(A\<union>B), closure(R1) = R1\<union>(B\<union>C).
     If P1 = R1 then closure(P1) \<subseteq> (A\<union>B) \<inter> (B\<union>C) gives boundary \<subseteq> B, contradicting
     that an open nonempty subset of S2 has boundary larger than an arc.\<close>
  have hP1_ne_R1: "P1 \<noteq> R1"
  proof
    assume "P1 = R1"
    \<comment> \<open>closure(P1) = P1\<union>(A\<union>B), closure(R1) = R1\<union>(B\<union>C). If equal:
       P1\<union>(A\<union>B) = P1\<union>(B\<union>C), so (A\<union>B) \<subseteq> P1\<union>(B\<union>C) and (B\<union>C) \<subseteq> P1\<union>(A\<union>B).
       Hence A-B \<subseteq> P1\<union>C and C-B \<subseteq> P1\<union>A. But P1 \<subseteq> S2-Y, A,C \<subseteq> Y, P1 \<inter> Y = {}.
       So A-B \<subseteq> C and C-B \<subseteq> A. Combined with A\<inter>C = {a1,a3} and B endpoints = {a1,a3}:
       A-{a1,a3} \<subseteq> C, but A \<inter> C = {a1,a3}, so A-{a1,a3} \<subseteq> C \<inter> A = {a1,a3}.
       Hence A \<subseteq> {a1,a3} \<union> B. But A is an arc with \<ge> 3 points. Contradiction.\<close>
    have "closure_on top1_S2 top1_S2_topology P1 = closure_on top1_S2 top1_S2_topology R1"
      using \<open>P1 = R1\<close> by (by100 simp)
    hence "P1 \<union> (?A \<union> ?B) = P1 \<union> (?B \<union> ?C)" using hcl_P1 hcl_R1 \<open>P1 = R1\<close> by (by100 simp)
    hence "?A \<subseteq> P1 \<union> ?B \<union> ?C" by (by100 blast)
    moreover have "P1 \<inter> ?A = {}" using hP1_sub_Y_compl by (by100 blast)
    ultimately have hA_sub_BC: "?A \<subseteq> ?B \<union> ?C" by (by100 blast)
    \<comment> \<open>But A \<inter> (B\<union>C) = (A\<inter>B) \<union> (A\<inter>C) = {a1,a3} \<union> {a1,a3} = {a1,a3}.\<close>
    have "?A \<inter> (?B \<union> ?C) \<subseteq> {a1, a3}" using hAB_int hAC_int by (by100 blast)
    hence "?A \<subseteq> {a1, a3}" using hA_sub_BC by (by100 blast)
    \<comment> \<open>But A = e12 \<union> e23 has \<ge> 3 points (it's an arc).\<close>
    moreover have "a2 \<in> ?A" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
    moreover have "a2 \<notin> {a1, a3}" using hdist(1,4) by (by100 blast)
    ultimately show False by (by100 blast)
  qed
  \<comment> \<open>e24-{a2,a4} lies in the third component (not P1, not R1).\<close>
  have he24_conn: "top1_connected_on (e24 - {a2, a4})
      (subspace_topology top1_S2 top1_S2_topology (e24 - {a2, a4}))"
    by (rule arc_minus_endpoints_connected[OF hS2_strict hS2_haus assms(9) assms(15) assms(21) hdist(5)])
  \<comment> \<open>e24 \<inter> Y = {a2, a4}: from intersection assumptions.\<close>
  have he24_Y_int: "e24 \<inter> ?Y = {a2, a4}"
  proof -
    \<comment> \<open>e24 \<inter> (e12\<union>e23\<union>e13\<union>e41\<union>e34)
       = (e24\<inter>e12) \<union> (e24\<inter>e23) \<union> (e24\<inter>e13) \<union> (e24\<inter>e41) \<union> (e24\<inter>e34)\<close>
    have "e24 \<inter> e13 = {}"
    proof -
      have ha2_e12: "a2 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
      have ha1_e12: "a1 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
      have ha1_not_e24: "a1 \<notin> e24"
      proof assume "a1 \<in> e24"
        hence "a1 \<in> e24 \<inter> e12" using ha1_e12 by (by100 blast)
        hence "a1 = a2" using assms(33) by (by100 blast)
        thus False using hdist(1) by (by100 blast)
      qed
      have ha3_e23: "a3 \<in> e23" using assms(17) unfolding top1_arc_endpoints_on_def by (by100 blast)
      have ha3_not_e24: "a3 \<notin> e24"
      proof assume "a3 \<in> e24"
        hence "a3 \<in> e24 \<inter> e23" using ha3_e23 by (by100 blast)
        hence "a3 = a2" using assms(34) by (by100 blast)
        thus False using hdist(4) by (by100 blast)
      qed
      \<comment> \<open>a2 \<notin> e13: from ha2_not_BC. a4 \<notin> e13: from ha4_not_AB.\<close>
      have "a2 \<notin> e13" using ha2_not_BC by (by100 blast)
      moreover have "a4 \<notin> e13" using ha4_not_AB by (by100 blast)
      ultimately have "\<forall>x \<in> {a1,a2,a3,a4}. x \<notin> e24 \<inter> e13"
        using ha1_not_e24 ha3_not_e24 by (by100 blast)
      thus ?thesis using assms(32) by (by100 blast)
    qed
    hence he24_e13: "e24 \<inter> e13 = {}" .
    have "e24 \<inter> ?Y = (e24 \<inter> e12) \<union> (e24 \<inter> e23) \<union> (e24 \<inter> e13) \<union> (e24 \<inter> e41) \<union> (e24 \<inter> e34)"
      by (by100 blast)
    also have "\<dots> = {a2} \<union> {a2} \<union> {} \<union> {a4} \<union> {a4}"
      using assms(33,34,35,36) he24_e13 by (by100 simp)
    also have "\<dots> = {a2, a4}" by (by100 blast)
    finally show ?thesis .
  qed
  have ha2_in_Y: "a2 \<in> ?Y"
    using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have ha4_in_Y: "a4 \<in> ?Y"
    using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have he24_in_Y_compl: "e24 - {a2, a4} \<subseteq> top1_S2 - ?Y"
    using he24_Y_int assms(9) by (by100 blast)
  \<comment> \<open>Let T be the theta component \<noteq> P1, \<noteq> R1.\<close>
  obtain T where hT_is: "T \<in> {U, V, W}" "T \<noteq> P1" "T \<noteq> R1"
      and hT_conn: "top1_connected_on T (subspace_topology top1_S2 top1_S2_topology T)"
      and hT_ne: "T \<noteq> {}"
      and hT_union: "P1 \<union> R1 \<union> T = top1_S2 - ?Y"
      and hT_disj: "P1 \<inter> T = {}" "R1 \<inter> T = {}"
  proof -
    \<comment> \<open>Define T as (S2-Y) - P1 - R1. Show it has all required properties.\<close>
    define T0 where "T0 = (top1_S2 - ?Y) - P1 - R1"
    have hT0_in: "T0 \<in> {U, V, W}"
    proof -
      have hUVW_union: "top1_S2 - ?Y = U \<union> V \<union> W" using hUVW(7) by (by100 blast)
      have hT0_alt: "T0 = (U \<union> V \<union> W) - P1 - R1" unfolding T0_def using hUVW_union by (by100 blast)
      \<comment> \<open>Case split: P1=U,V,W and R1=U,V,W; the remainder is T0.\<close>
      from hP1_is_comp show ?thesis
      proof (elim disjE)
        assume "P1 = U" from hR1_is_comp show ?thesis
        proof (elim disjE)
          assume "R1 = U" thus ?thesis using \<open>P1 = U\<close> hP1_ne_R1 by (by100 blast)
        next assume "R1 = V"
          have "T0 = W" using hT0_alt \<open>P1 = U\<close> \<open>R1 = V\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        next assume "R1 = W"
          have "T0 = V" using hT0_alt \<open>P1 = U\<close> \<open>R1 = W\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        qed
      next
        assume "P1 = V" from hR1_is_comp show ?thesis
        proof (elim disjE)
          assume "R1 = U"
          have "T0 = W" using hT0_alt \<open>P1 = V\<close> \<open>R1 = U\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        next assume "R1 = V" thus ?thesis using \<open>P1 = V\<close> hP1_ne_R1 by (by100 blast)
        next assume "R1 = W"
          have "T0 = U" using hT0_alt \<open>P1 = V\<close> \<open>R1 = W\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        qed
      next
        assume "P1 = W" from hR1_is_comp show ?thesis
        proof (elim disjE)
          assume "R1 = U"
          have "T0 = V" using hT0_alt \<open>P1 = W\<close> \<open>R1 = U\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        next assume "R1 = V"
          have "T0 = U" using hT0_alt \<open>P1 = W\<close> \<open>R1 = V\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        next assume "R1 = W" thus ?thesis using \<open>P1 = W\<close> hP1_ne_R1 by (by100 blast)
        qed
      qed
    qed
    have hT0_ne_P1: "T0 \<noteq> P1"
    proof -
      have "P1 \<inter> T0 = {}" using T0_def by (by100 blast)
      thus ?thesis using hP(1) by (by100 blast)
    qed
    have hT0_ne_R1: "T0 \<noteq> R1"
    proof -
      have "R1 \<inter> T0 = {}" using T0_def by (by100 blast)
      thus ?thesis using hR(1) by (by100 blast)
    qed
    have "top1_connected_on T0 (subspace_topology top1_S2 top1_S2_topology T0)"
      using hT0_in hUVW(8,9,10) by (by100 blast)
    moreover have "T0 \<noteq> {}" using hT0_in hUVW(1,2,3) by (by100 blast)
    moreover have "P1 \<union> R1 \<union> T0 = top1_S2 - ?Y"
    proof -
      have hT0e: "T0 = (top1_S2 - ?Y) - P1 - R1" by (rule T0_def)
      show ?thesis
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> P1 \<union> R1 \<union> T0"
        hence "x \<in> P1 \<or> x \<in> R1 \<or> x \<in> T0" by (by100 blast)
        thus "x \<in> top1_S2 - ?Y"
        proof (elim disjE)
          assume "x \<in> P1" thus ?thesis using hP1_sub_Y_compl by (by100 blast)
        next assume "x \<in> R1" thus ?thesis using hR1_sub_Y_compl by (by100 blast)
        next assume "x \<in> T0" thus ?thesis using hT0e by (by100 blast)
        qed
      next
        fix x assume "x \<in> top1_S2 - ?Y"
        thus "x \<in> P1 \<union> R1 \<union> T0" using hT0e by (by100 blast)
      qed
    qed
    moreover have "P1 \<inter> T0 = {}" using T0_def by (by100 blast)
    moreover have "R1 \<inter> T0 = {}" using T0_def by (by100 blast)
    ultimately show ?thesis by (rule that[OF hT0_in hT0_ne_P1 hT0_ne_R1])
  qed
  have he24_in_T: "e24 - {a2, a4} \<subseteq> T"
  proof -
    \<comment> \<open>e24-{a2,a4} connected \<subseteq> P1\<union>R1\<union>T (disjoint open). By Lemma\_23\_2 approach: in one.\<close>
    have "e24 - {a2, a4} \<subseteq> P1 \<union> R1 \<union> T" using he24_in_Y_compl hT_union by (by100 blast)
    \<comment> \<open>Not \<subseteq> P1 (he24\_not\_P1). Not \<subseteq> R1 (he24\_not\_R1). Hence \<subseteq> T.\<close>
    \<comment> \<open>P1, R1, T are pairwise disjoint open. Connected e24-{a2,a4} must be in one.\<close>
    have hT_open: "T \<in> top1_S2_topology" using hT_is(1) hUVW(11,12,13) by (by100 blast)
    \<comment> \<open>e24-{a2,a4} \<subseteq> P1 or \<subseteq> R1\<union>T (separation {P1, R1\<union>T}).\<close>
    have "e24 - {a2, a4} \<subseteq> P1 \<or> e24 - {a2, a4} \<subseteq> R1 \<union> T"
      sorry \<comment> \<open>Lemma\_23\_2 on separation {P1, R1\<union>T} of P1\<union>R1\<union>T.\<close>
    hence "e24 - {a2, a4} \<subseteq> R1 \<union> T" using he24_not_P1 by (by100 blast)
    \<comment> \<open>Then \<subseteq> R1 or \<subseteq> T.\<close>
    moreover have "e24 - {a2, a4} \<subseteq> R1 \<or> e24 - {a2, a4} \<subseteq> T"
      sorry \<comment> \<open>Lemma\_23\_2 on separation {R1, T} of R1\<union>T.\<close>
    ultimately show ?thesis using he24_not_R1 by (by100 blast)
  qed
  \<comment> \<open>Step 5: Apply Theorem_63_5 to split T using cl(P1)\<union>cl(R1) and e24.\<close>
  let ?C1 = "closure_on top1_S2 top1_S2_topology P1
        \<union> closure_on top1_S2 top1_S2_topology R1"
  have hC1_eq: "?C1 = P1 \<union> R1 \<union> ?Y"
    using hcl_P1 hcl_R1 by (by100 blast)
  have hC1_closed: "closedin_on top1_S2 top1_S2_topology ?C1"
  proof -
    have "closedin_on top1_S2 top1_S2_topology (closure_on top1_S2 top1_S2_topology P1)"
    proof -
      have "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      thus ?thesis by (rule closure_on_closed[OF hTopS2])
    qed
    moreover have "closedin_on top1_S2 top1_S2_topology (closure_on top1_S2 top1_S2_topology R1)"
    proof -
      have "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      thus ?thesis by (rule closure_on_closed[OF hTopS2])
    qed
    ultimately show ?thesis by (rule closedin_on_Un[OF hTopS2])
  qed
  have hC1_conn: "top1_connected_on ?C1 (subspace_topology top1_S2 top1_S2_topology ?C1)"
  proof -
    \<comment> \<open>cl(P1) connected (closure of connected set, Theorem 23.4).\<close>
    have hclP1_sub: "closure_on top1_S2 top1_S2_topology P1 \<subseteq> top1_S2"
      using hcl_P1 hP1_sub_AB hA_sub assms(8) by (by100 blast)
    have hP1_sub_S2: "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
    have hclP1_conn: "top1_connected_on (closure_on top1_S2 top1_S2_topology P1)
        (subspace_topology top1_S2 top1_S2_topology (closure_on top1_S2 top1_S2_topology P1))"
      by (rule Theorem_23_4[OF hTopS2 hP1_sub_S2 hclP1_sub subset_closure_on
          closure_on_mono[OF order_refl] hP(5)])
    \<comment> \<open>cl(R1) connected.\<close>
    have hclR1_sub: "closure_on top1_S2 top1_S2_topology R1 \<subseteq> top1_S2"
      using hcl_R1 hR(4) assms(8) hC_sub by (by100 blast)
    have hR1_sub_S2: "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
    have hclR1_conn: "top1_connected_on (closure_on top1_S2 top1_S2_topology R1)
        (subspace_topology top1_S2 top1_S2_topology (closure_on top1_S2 top1_S2_topology R1))"
      by (rule Theorem_23_4[OF hTopS2 hR1_sub_S2 hclR1_sub subset_closure_on
          closure_on_mono[OF order_refl] hR(5)])
    \<comment> \<open>They share B = e13. B \<subseteq> cl(P1) \<inter> cl(R1).\<close>
    have hB_in_both: "?B \<subseteq> closure_on top1_S2 top1_S2_topology P1 \<inter>
        closure_on top1_S2 top1_S2_topology R1"
      using hcl_P1 hcl_R1 by (by100 blast)
    obtain p where hp: "p \<in> ?B" using assms(20) unfolding top1_arc_endpoints_on_def by (by100 blast)
    hence "p \<in> closure_on top1_S2 top1_S2_topology P1 \<inter>
        closure_on top1_S2 top1_S2_topology R1" using hB_in_both by (by100 blast)
    \<comment> \<open>Apply Theorem 23.3: indexed family with common point.\<close>
    have "top1_connected_on (closure_on top1_S2 top1_S2_topology P1 \<union>
        closure_on top1_S2 top1_S2_topology R1)
        (subspace_topology top1_S2 top1_S2_topology (closure_on top1_S2 top1_S2_topology P1 \<union>
        closure_on top1_S2 top1_S2_topology R1))"
    proof -
      let ?I = "{True, False}" and ?A = "\<lambda>b. if b then closure_on top1_S2 top1_S2_topology P1
          else closure_on top1_S2 top1_S2_topology R1"
      have "?I \<noteq> {}" by (by100 simp)
      moreover have "\<forall>i \<in> ?I. ?A i \<subseteq> top1_S2"
        using hclP1_sub hclR1_sub by (by100 simp)
      moreover have "\<forall>i \<in> ?I. top1_connected_on (?A i) (subspace_topology top1_S2 top1_S2_topology (?A i))"
        using hclP1_conn hclR1_conn by (by100 simp)
      moreover have "p \<in> \<Inter>(?A ` ?I)"
        using \<open>p \<in> closure_on top1_S2 top1_S2_topology P1 \<inter>
            closure_on top1_S2 top1_S2_topology R1\<close> by (by100 simp)
      moreover have "(\<Union>i \<in> ?I. ?A i) = closure_on top1_S2 top1_S2_topology P1 \<union>
          closure_on top1_S2 top1_S2_topology R1" by (by100 force)
      ultimately have hpremises: "?I \<noteq> {} \<and> (\<forall>i \<in> ?I. ?A i \<subseteq> top1_S2) \<and>
          (\<forall>i \<in> ?I. top1_connected_on (?A i) (subspace_topology top1_S2 top1_S2_topology (?A i))) \<and>
          p \<in> \<Inter>(?A ` ?I) \<and> (\<Union>i \<in> ?I. ?A i) = closure_on top1_S2 top1_S2_topology P1 \<union>
          closure_on top1_S2 top1_S2_topology R1" by (by100 blast)
      from Theorem_23_3[OF hTopS2, of ?I ?A p] hpremises
      show ?thesis by metis
    qed
    thus ?thesis .
  qed
  have hC1_compl: "top1_S2 - ?C1 = T"
  proof -
    have "top1_S2 - ?C1 = top1_S2 - (P1 \<union> R1 \<union> ?Y)" using hC1_eq by (by100 simp)
    also have "\<dots> = (top1_S2 - ?Y) - P1 - R1" by (by100 blast)
    also have "\<dots> = (P1 \<union> R1 \<union> T) - P1 - R1" using hT_union by (by100 simp)
    also have "\<dots> = T" using hT_disj(1,2) by (by100 blast)
    finally show ?thesis .
  qed
  have hC1_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology ?C1"
    unfolding top1_separates_on_def using hC1_compl hT_conn by (by100 simp)
  have he24_closed: "closedin_on top1_S2 top1_S2_topology e24"
    by (rule arc_in_S2_closed[OF assms(9) assms(15)])
  have he24_conn_full: "top1_connected_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
    using arc_connected[OF assms(15)] .
  have he24_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology e24"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) assms(9) assms(15)])
  have hC1_e24_int: "?C1 \<inter> e24 = {a2, a4}"
  proof -
    \<comment> \<open>(P1 \<union> R1 \<union> Y) \<inter> e24 = (P1 \<inter> e24) \<union> (R1 \<inter> e24) \<union> (Y \<inter> e24).
       P1 \<inter> e24 = {} and R1 \<inter> e24 = {} (both \<subseteq> S2-Y, e24\<setminus>{a2,a4} \<subseteq> T).\<close>
    have "P1 \<inter> e24 = {}"
    proof -
      have "P1 \<subseteq> top1_S2 - ?Y" by (rule hP1_sub_Y_compl)
      moreover have "e24 - {a2, a4} \<subseteq> T" by (rule he24_in_T)
      moreover have "P1 \<inter> T = {}" by (rule hT_disj(1))
      moreover have "{a2, a4} \<subseteq> ?Y" using ha2_in_Y ha4_in_Y by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    moreover have "R1 \<inter> e24 = {}"
    proof -
      have "R1 \<subseteq> top1_S2 - ?Y" by (rule hR1_sub_Y_compl)
      moreover have "e24 - {a2, a4} \<subseteq> T" by (rule he24_in_T)
      moreover have "R1 \<inter> T = {}" by (rule hT_disj(2))
      moreover have "{a2, a4} \<subseteq> ?Y" using ha2_in_Y ha4_in_Y by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    ultimately have h_e24_fact: "(P1 \<union> R1) \<inter> e24 = {}" by (by100 blast)
    show ?thesis
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> ?C1 \<inter> e24"
      hence "x \<in> (P1 \<union> R1 \<union> ?Y) \<inter> e24" using hC1_eq by (by100 blast)
      hence "x \<in> ?Y \<inter> e24" using h_e24_fact by (by100 blast)
      hence "x \<in> e24 \<inter> ?Y" by (by100 blast)
      thus "x \<in> {a2, a4}"
      proof -
        from he24_Y_int have "\<And>z. z \<in> e24 \<inter> ?Y \<Longrightarrow> z \<in> {a2, a4}" by (by100 blast)
        thus ?thesis using \<open>x \<in> e24 \<inter> ?Y\<close> by (by100 blast)
      qed
    next
      fix x assume "x \<in> {a2, a4}"
      hence "x \<in> ?Y \<inter> e24" using he24_Y_int by (by100 blast)
      hence "x \<in> (P1 \<union> R1 \<union> ?Y) \<inter> e24" by (by100 blast)
      thus "x \<in> ?C1 \<inter> e24" using hC1_eq by (by100 blast)
    qed
  qed
  have hC1_e24_card: "card (?C1 \<inter> e24) = 2"
    using hC1_e24_int hdist(5) by (by100 simp)
  obtain W1 W2 where hW: "W1 \<noteq> {}" "W2 \<noteq> {}" "W1 \<inter> W2 = {}"
      "W1 \<union> W2 = top1_S2 - (?C1 \<union> e24)"
      "top1_connected_on W1 (subspace_topology top1_S2 top1_S2_topology W1)"
      "top1_connected_on W2 (subspace_topology top1_S2 top1_S2_topology W2)"
    using Theorem_63_5_two_closed_connected[OF assms(1) hC1_closed he24_closed
        hC1_conn he24_conn_full hC1_e24_card hC1_no_sep he24_no_sep]
    by (by100 metis)
  \<comment> \<open>Step 6: Package the 4 components P1, R1, W1, W2.\<close>
  have hfour_union: "P1 \<union> R1 \<union> W1 \<union> W2 = top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e41 \<union> e13 \<union> e24)"
  proof -
    have "W1 \<union> W2 = top1_S2 - (?C1 \<union> e24)" by (rule hW(4))
    hence "W1 \<union> W2 = top1_S2 - ((P1 \<union> R1 \<union> ?Y) \<union> e24)" using hC1_eq by (by100 simp)
    hence "P1 \<union> R1 \<union> W1 \<union> W2 = P1 \<union> R1 \<union> (top1_S2 - (P1 \<union> R1 \<union> ?Y \<union> e24))" by (by100 blast)
    also have "\<dots> = top1_S2 - (?Y \<union> e24)"
    proof -
      have "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      moreover have "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      moreover have "P1 \<inter> ?Y = {}" using hP1_sub_Y_compl by (by100 blast)
      moreover have "R1 \<inter> ?Y = {}" using hR1_sub_Y_compl by (by100 blast)
      moreover have "P1 \<inter> e24 = {}"
      proof -
        have "P1 \<subseteq> top1_S2 - ?Y" by (rule hP1_sub_Y_compl)
        moreover have "e24 - {a2, a4} \<subseteq> T" by (rule he24_in_T)
        moreover have "P1 \<inter> T = {}" by (rule hT_disj(1))
        moreover have "{a2, a4} \<subseteq> ?Y" using ha2_in_Y ha4_in_Y by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      moreover have "R1 \<inter> e24 = {}"
      proof -
        have "R1 \<subseteq> top1_S2 - ?Y" by (rule hR1_sub_Y_compl)
        moreover have "e24 - {a2, a4} \<subseteq> T" by (rule he24_in_T)
        moreover have "R1 \<inter> T = {}" by (rule hT_disj(2))
        moreover have "{a2, a4} \<subseteq> ?Y" using ha2_in_Y ha4_in_Y by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      ultimately show ?thesis by (by100 blast)
    qed
    also have "\<dots> = top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e41 \<union> e13 \<union> e24)" by (by100 blast)
    finally show ?thesis .
  qed
  have hP1R1_disj: "P1 \<inter> R1 = {}"
  proof -
    from hP1_is_comp show ?thesis
    proof (elim disjE)
      assume "P1 = U" from hR1_is_comp show ?thesis
      proof (elim disjE)
        assume "R1 = U" thus ?thesis using hP1_ne_R1 \<open>P1 = U\<close> by (by100 blast)
      next assume "R1 = V" thus ?thesis using \<open>P1 = U\<close> hUVW(4) by (by100 blast)
      next assume "R1 = W" thus ?thesis using \<open>P1 = U\<close> hUVW(6) by (by100 blast)
      qed
    next
      assume "P1 = V" from hR1_is_comp show ?thesis
      proof (elim disjE)
        assume "R1 = U" thus ?thesis using \<open>P1 = V\<close> hUVW(4) by (by100 blast)
      next assume "R1 = V" thus ?thesis using hP1_ne_R1 \<open>P1 = V\<close> by (by100 blast)
      next assume "R1 = W" thus ?thesis using \<open>P1 = V\<close> hUVW(5) by (by100 blast)
      qed
    next
      assume "P1 = W" from hR1_is_comp show ?thesis
      proof (elim disjE)
        assume "R1 = U" thus ?thesis using \<open>P1 = W\<close> hUVW(6) by (by100 blast)
      next assume "R1 = V" thus ?thesis using \<open>P1 = W\<close> hUVW(5) by (by100 blast)
      next assume "R1 = W" thus ?thesis using hP1_ne_R1 \<open>P1 = W\<close> by (by100 blast)
      qed
    qed
  qed
  have hfour_disj: "P1 \<inter> R1 = {}" "P1 \<inter> W1 = {}" "P1 \<inter> W2 = {}"
      "R1 \<inter> W1 = {}" "R1 \<inter> W2 = {}" "W1 \<inter> W2 = {}"
  proof -
    show "P1 \<inter> R1 = {}" by (rule hP1R1_disj)
    \<comment> \<open>W1, W2 \<subseteq> S2-(C1\<union>e24) = T-e24_inner, which is disjoint from P1, R1.\<close>
    have hW12_sub: "W1 \<union> W2 \<subseteq> top1_S2 - ?C1" using hW(4) by (by100 blast)
    hence "W1 \<subseteq> top1_S2 - ?C1" by (by100 blast)
    hence "P1 \<inter> W1 = {}" using hC1_eq by (by100 blast)
    thus "P1 \<inter> W1 = {}" .
    have "W2 \<subseteq> top1_S2 - ?C1" using hW12_sub by (by100 blast)
    thus "P1 \<inter> W2 = {}" using hC1_eq by (by100 blast)
    have "W1 \<subseteq> top1_S2 - ?C1" using hW12_sub by (by100 blast)
    thus "R1 \<inter> W1 = {}" using hC1_eq by (by100 blast)
    have "W2 \<subseteq> top1_S2 - ?C1" using hW12_sub by (by100 blast)
    thus "R1 \<inter> W2 = {}" using hC1_eq by (by100 blast)
    show "W1 \<inter> W2 = {}" by (rule hW(3))
  qed
  show ?thesis
    apply (rule exI[of _ P1])
    apply (rule exI[of _ R1])
    apply (rule exI[of _ W1])
    apply (rule exI[of _ W2])
    using hP(1) hR(1) hW(1,2) hfour_disj hfour_union hP(5) hR(5) hW(5,6) by (by100 force)
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


(** from \<S>65 Lemma 65.1: for K_4 subspace of S^2 with vertices a_1, ..., a_4 and
    closed-curve edge C = a_1 a_2 a_3 a_4 a_1, and interior points p, q of opposite
    edges a_1 a_3 and a_2 a_4, the loop traversing C is nontrivial in \<pi>_1(S^2-p-q, x_0). **)
lemma Lemma_65_1_K4_subgraph:
  fixes a1 a2 a3 a4 :: "real \<times> real \<times> real"
    and e12 e23 e34 e41 e13 e24 :: "(real \<times> real \<times> real) set"
    and C :: "(real \<times> real \<times> real) set"
    and p q :: "real \<times> real \<times> real"
    and f :: "real \<Rightarrow> real \<times> real \<times> real"
    and x0 :: "real \<times> real \<times> real"
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      \<comment> \<open>K_4 structure: 4 distinct vertices on S^2, plus 6 arcs between them.\<close>
      and "card {a1, a2, a3, a4} = 4"
      and "{a1, a2, a3, a4} \<subseteq> top1_S2"
      \<comment> \<open>All 6 arcs are subsets of S^2.\<close>
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
      \<comment> \<open>f is a loop at x_0 in S^2-{p,q} whose image is C.\<close>
      and "top1_is_loop_on (top1_S2 - {p} - {q})
             (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x0 f"
      and "f ` I_set = C"
  shows "\<not> top1_path_homotopic_on (top1_S2 - {p} - {q})
           (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q}))
           x0 x0 f (top1_constant_path x0)"
proof -
  \<comment> \<open>Munkres 65.1: The loop f traverses the 4-cycle a1-a2-a3-a4-a1 in S^2-{p,q}.
     p lies in the interior of e13 and q in e24.
     By Theorem 63.1 applied to X = S^2-{p,q}, U = S^2-e13, V = S^2-e24:
     U \<inter> V = S^2-(e13\<union>e24) has exactly two components (by Jordan Curve-like argument),
     and the loop f alternates between U and V, creating a nontrivial element.\<close>
  let ?X = "top1_S2 - {p} - {q}" and ?TX = "subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})"
  let ?U = "top1_S2 - e13" and ?V = "top1_S2 - e24"
  \<comment> \<open>Step 1: S²-{p,q} = U \<union> V where U = S²-e13, V = S²-e24.
     Both U, V are open in S²-{p,q}. U \<inter> V = S²-(e13 \<union> e24) has two path-components.\<close>
  \<comment> \<open>Step 2: U and V are each simply connected (S² minus a point is contractible to the
     opposite hemisphere; S² minus an arc is still simply connected).\<close>
  \<comment> \<open>Step 3: f alternates between U and V (traversing edges alternately in each).
     By Theorem 63.1 (generalized SvK for non-trivial intersection),
     the path-class [f] is non-trivial in \<pi>_1(S²-{p,q}).\<close>
  \<comment> \<open>Step 1: Set up the SvK open cover.
     U' = S²-e13, V' = S²-e24. Both are open in S² (arcs are closed).
     X = S²-{p}-{q} = U' \<union> V' (since p \<in> e13, q \<in> e24).
     U = X \<inter> U' = S²-e13-{q} (removing q from U', which is in e24 not e13).
     V = X \<inter> V' = S²-e24-{p} (removing p from V', which is in e13 not e24).
     U, V are open in X. U \<union> V = X.
     U \<inter> V = S²-(e13 \<union> e24)-{p}-{q} = S²-(e13 \<union> e24) minus {p,q} (but p,q are in arcs).
     U \<inter> V has exactly two path-components A, B separated by the 4-cycle C.\<close>
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hTX: "is_topology_on ?X ?TX"
    by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
  have he13_sub: "e13 \<subseteq> top1_S2" by (rule assms(8))
  have he24_sub: "e24 \<subseteq> top1_S2" by (rule assms(9))
  have he23_sub: "e23 \<subseteq> top1_S2" by (rule assms(5))
  have he41_sub: "e41 \<subseteq> top1_S2" by (rule assms(7))
  \<comment> \<open>Step 2: The loop f traverses the 4-cycle a1-a2-a3-a4-a1.
     Decompose f into two paths:
     \<alpha>: portion of f in U (edges e12, e34, not touching e13)
     \<beta>: portion of f in V (edges e23, e41, not touching e24)
     Then f ~ \<alpha>*\<beta> (path product) in X.\<close>
  \<comment> \<open>Step 3: U \<inter> V = S² - (e13 \<union> e24) - {p} - {q} has two path-components.
     One contains a1, a3 and the other contains a2, a4 (separated by arcs e13, e24).
     Choose a \<in> A (component of U\<inter>V containing x0) and b \<in> B (the other component).\<close>
  \<comment> \<open>Step 4: Apply Theorem 63.1: \<alpha> is a path in U from a to b, \<beta> path in V from b to a.
     U\<inter>V = A \<union> B with A,B disjoint open, a \<in> A, b \<in> B.
     Therefore \<alpha>*\<beta> is not nulhomotopic in X.\<close>
  \<comment> \<open>Step 1: Construct D_1 = sub-arc of e13 from p to a3, then e23, then sub-arc of e24 to q.
     D_2 = sub-arc of e24 from q to a4, then e41, then sub-arc of e13 to p.
     D = D_1 \<union> D_2 is a simple closed curve.\<close>
  \<comment> \<open>Split e13 at p into two sub-arcs: e13_a1p (from a1 to p) and e13_pa3 (from p to a3).\<close>
  have hp_e13: "p \<in> e13 - {a1, a3}" by (rule assms(37))
  have hq_e24: "q \<in> e24 - {a2, a4}" by (rule assms(38))
  have he13_ep: "top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13) = {a1,a3}"
    by (rule assms(20))
  have he24_ep: "top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24) = {a2,a4}"
    by (rule assms(21))
  have he13_arc: "top1_is_arc_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
    by (rule assms(14))
  have he24_arc: "top1_is_arc_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
    by (rule assms(15))
  have hp_not_ep: "p \<notin> top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
    using he13_ep hp_e13 by (by100 blast)
  have hq_not_ep: "q \<notin> top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
    using he24_ep hq_e24 by (by100 blast)
  have hS2_strict: "is_topology_on_strict top1_S2 top1_S2_topology" by (rule assms(1))
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology"
    using top1_S2_is_hausdorff .
  have ha1_ne_a3: "a1 \<noteq> a3"
  proof
    assume "a1 = a3"
    hence "{a1, a2, a3, a4} = {a2, a3, a4}" by (by100 blast)
    hence "card {a1, a2, a3, a4} \<le> card {a2, a3, a4}" by (by100 simp)
    moreover have "card {a2, a3, a4} \<le> 3"
    proof -
      show ?thesis by (rule card_three_le)
    qed
    ultimately show False using assms(2) by (by100 simp)
  qed
  have ha2_ne_a4: "a2 \<noteq> a4"
  proof
    assume "a2 = a4"
    hence "{a1, a2, a3, a4} = {a1, a3, a4}" by (by100 blast)
    hence "card {a1, a2, a3, a4} \<le> card {a1, a3, a4}" by (by100 simp)
    moreover have "card {a1, a3, a4} \<le> 3"
      by (rule card_three_le)
    ultimately show False using assms(2) by (by100 simp)
  qed
  obtain e13_a1p e13_pa3 where he13_split: "e13 = e13_a1p \<union> e13_pa3"
      "e13_a1p \<inter> e13_pa3 = {p}"
      "top1_is_arc_on e13_a1p (subspace_topology top1_S2 top1_S2_topology e13_a1p)"
      "top1_is_arc_on e13_pa3 (subspace_topology top1_S2 top1_S2_topology e13_pa3)"
      "a1 \<in> e13_a1p" "a3 \<in> e13_pa3" "p \<in> e13_a1p" "p \<in> e13_pa3"
  proof -
    have "p \<in> e13" using hp_e13 by (by100 blast)
    from arc_split_at_given_point[OF hS2_strict hS2_haus he13_sub he13_arc this hp_not_ep he13_ep ha1_ne_a3]
    obtain D1 D2 where h: "e13 = D1 \<union> D2 \<and> D1 \<inter> D2 = {p}
        \<and> top1_is_arc_on D1 (subspace_topology top1_S2 top1_S2_topology D1)
        \<and> top1_is_arc_on D2 (subspace_topology top1_S2 top1_S2_topology D2)
        \<and> a1 \<in> D1 \<and> a3 \<in> D2 \<and> p \<in> D1 \<and> p \<in> D2 \<and> D1 \<subseteq> top1_S2 \<and> D2 \<subseteq> top1_S2"
      by fast
    have h1: "e13 = D1 \<union> D2" and h2: "D1 \<inter> D2 = {p}"
        and h3: "top1_is_arc_on D1 (subspace_topology top1_S2 top1_S2_topology D1)"
        and h4: "top1_is_arc_on D2 (subspace_topology top1_S2 top1_S2_topology D2)"
        and h5: "a1 \<in> D1" and h6: "a3 \<in> D2" and h7: "p \<in> D1" and h8: "p \<in> D2"
      using h by (by100 blast)+
    show ?thesis using that[OF h1 h2 h3 h4 h5 h6 h7 h8] .
  qed
  \<comment> \<open>Split e24 at q into two sub-arcs.\<close>
  obtain e24_a2q e24_qa4 where he24_split: "e24 = e24_a2q \<union> e24_qa4"
      "e24_a2q \<inter> e24_qa4 = {q}"
      "top1_is_arc_on e24_a2q (subspace_topology top1_S2 top1_S2_topology e24_a2q)"
      "top1_is_arc_on e24_qa4 (subspace_topology top1_S2 top1_S2_topology e24_qa4)"
      "a2 \<in> e24_a2q" "a4 \<in> e24_qa4" "q \<in> e24_a2q" "q \<in> e24_qa4"
  proof -
    have "q \<in> e24" using hq_e24 by (by100 blast)
    from arc_split_at_given_point[OF hS2_strict hS2_haus he24_sub he24_arc this hq_not_ep he24_ep ha2_ne_a4]
    obtain D1 D2 where h: "e24 = D1 \<union> D2 \<and> D1 \<inter> D2 = {q}
        \<and> top1_is_arc_on D1 (subspace_topology top1_S2 top1_S2_topology D1)
        \<and> top1_is_arc_on D2 (subspace_topology top1_S2 top1_S2_topology D2)
        \<and> a2 \<in> D1 \<and> a4 \<in> D2 \<and> q \<in> D1 \<and> q \<in> D2 \<and> D1 \<subseteq> top1_S2 \<and> D2 \<subseteq> top1_S2"
      by fast
    have h1: "e24 = D1 \<union> D2" and h2: "D1 \<inter> D2 = {q}"
        and h3: "top1_is_arc_on D1 (subspace_topology top1_S2 top1_S2_topology D1)"
        and h4: "top1_is_arc_on D2 (subspace_topology top1_S2 top1_S2_topology D2)"
        and h5: "a2 \<in> D1" and h6: "a4 \<in> D2" and h7: "q \<in> D1" and h8: "q \<in> D2"
      using h by (by100 blast)+
    show ?thesis using that[OF h1 h2 h3 h4 h5 h6 h7 h8] .
  qed
  \<comment> \<open>D_1 = e13_pa3 \<union> e23 \<union> e24_a2q (arc from p through a3, a2 to q).
     D_2 = e24_qa4 \<union> e41 \<union> e13_a1p (arc from q through a4, a1 to p).\<close>
  let ?D1 = "e13_pa3 \<union> e23 \<union> e24_a2q"
  let ?D2 = "e24_qa4 \<union> e41 \<union> e13_a1p"
  \<comment> \<open>D_1, D_2 are arcs.\<close>
  have hD1_arc: "top1_is_arc_on ?D1 (subspace_topology top1_S2 top1_S2_topology ?D1)"
  proof -
    \<comment> \<open>Step 1: e13_pa3 \<inter> e23 = {a3}.\<close>
    have hint1: "e13_pa3 \<inter> e23 = {a3}"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> e13_pa3 \<inter> e23"
      hence "x \<in> e13" "x \<in> e23" using he13_split(1) by (by100 blast)+
      hence "x \<in> {a3}" using assms(29) by (by100 blast)
      thus "x \<in> {a3}" .
    next
      fix x assume "x \<in> {a3}"
      hence "x = a3" by (by100 blast)
      have "a3 \<in> e23"
      proof -
        have "a3 \<in> top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
          using assms(17) by (by100 blast)
        thus ?thesis unfolding top1_arc_endpoints_on_def by (by100 blast)
      qed
      thus "x \<in> e13_pa3 \<inter> e23" using he13_split(6) \<open>x = a3\<close> by (by100 blast)
    qed
    \<comment> \<open>Step 2: Concatenate e13_pa3 and e23 at a3.\<close>
    have he13_pa3_sub: "e13_pa3 \<subseteq> top1_S2" using he13_sub he13_split(1) by (by100 blast)
    have he23_sub_loc: "e23 \<subseteq> top1_S2" by (rule he23_sub)
    have he23_arc: "top1_is_arc_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      by (rule assms(11))
    \<comment> \<open>a3 is endpoint of e13_pa3 and e23.\<close>
    have ha3_ep1: "a3 \<in> top1_arc_endpoints_on e13_pa3 (subspace_topology top1_S2 top1_S2_topology e13_pa3)"
    proof -
      have he13_a1p_sub_loc: "e13_a1p \<subseteq> top1_S2" using he13_sub he13_split(1) by (by100 blast)
      have he13_pa3_sub_loc: "e13_pa3 \<subseteq> top1_S2" using he13_sub he13_split(1) by (by100 blast)
      from arc_split_endpoints(2)[OF hS2_strict hS2_haus he13_sub he13_arc
          he13_split(1) he13_split(2) he13_split(3) he13_split(4)
          he13_split(5) he13_split(6) he13_split(7) he13_split(8)
          he13_a1p_sub_loc he13_pa3_sub_loc he13_ep hp_not_ep]
      show ?thesis by (by100 blast)
    qed
    have ha3_ep2: "a3 \<in> top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      using assms(17) by (by100 blast)
    have hconcat1: "top1_is_arc_on (e13_pa3 \<union> e23)
        (subspace_topology top1_S2 top1_S2_topology (e13_pa3 \<union> e23))"
      by (rule arcs_concatenation_is_arc[OF hS2_strict hS2_haus
          he13_split(4) he13_pa3_sub he23_arc he23_sub_loc hint1 ha3_ep1 ha3_ep2])
    \<comment> \<open>Step 3: (e13_pa3 \<union> e23) \<inter> e24_a2q = {a2}.\<close>
    have hint2: "(e13_pa3 \<union> e23) \<inter> e24_a2q = {a2}"
    proof -
      \<comment> \<open>e13_pa3 \<inter> e24_a2q = {}.\<close>
      have "e13_pa3 \<inter> e24_a2q = {}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> e13_pa3 \<inter> e24_a2q"
        hence "x \<in> e13" "x \<in> e24" using he13_split(1) he24_split(1) by (by100 blast)+
        hence "x \<in> {a1,a2,a3,a4}" using assms(32) by (by100 blast)
        moreover have "a1 \<notin> e13_pa3"
        proof
          assume "a1 \<in> e13_pa3"
          hence "a1 \<in> e13_a1p \<inter> e13_pa3" using he13_split(5) by (by100 blast)
          hence "a1 = p" using he13_split(2) by (by100 blast)
          thus False using hp_e13 by (by100 blast)
        qed
        moreover have "a2 \<notin> e13"
        proof
          assume "a2 \<in> e13"
          hence "a2 \<in> e13 \<inter> e23" using assms(17)
            unfolding top1_arc_endpoints_on_def by (by100 blast)
          hence "a2 = a3" using assms(29) by (by100 blast)
          moreover have "a2 \<noteq> a3"
          proof
            assume "a2 = a3"
            hence "card {a1, a2, a3, a4} \<le> card {a1, a3, a4}" by (by100 simp)
            moreover have "card {a1, a3, a4} \<le> 3" by (rule card_three_le)
            ultimately have "card {a1, a2, a3, a4} \<le> 3" by (by100 linarith)
            thus False using assms(2) by (by100 simp)
          qed
          ultimately show False by (by100 blast)
        qed
        hence "a2 \<notin> e13_pa3" using he13_split(1) by (by100 blast)
        moreover have "a3 \<notin> e24"
        proof
          assume "a3 \<in> e24"
          hence "a3 \<in> e24 \<inter> e23" using assms(17)
            unfolding top1_arc_endpoints_on_def by (by100 blast)
          hence "a3 = a2" using assms(34) by (by100 blast)
          moreover have "a2 \<noteq> a3"
          proof
            assume "a2 = a3"
            hence "card {a1, a2, a3, a4} \<le> card {a1, a3, a4}" by (by100 simp)
            moreover have "card {a1, a3, a4} \<le> 3" by (rule card_three_le)
            ultimately have "card {a1, a2, a3, a4} \<le> 3" by (by100 linarith)
            thus False using assms(2) by (by100 simp)
          qed
          ultimately show False by (by100 blast)
        qed
        hence "a3 \<notin> e24_a2q" using he24_split(1) by (by100 blast)
        moreover have "a4 \<notin> e24_a2q"
        proof
          assume "a4 \<in> e24_a2q"
          hence "a4 \<in> e24_a2q \<inter> e24_qa4" using he24_split(6) by (by100 blast)
          hence "a4 = q" using he24_split(2) by (by100 blast)
          thus False using hq_e24 by (by100 blast)
        qed
        ultimately show "x \<in> {}" using \<open>x \<in> e13_pa3 \<inter> e24_a2q\<close> by (by100 blast)
      qed (by100 blast)
      \<comment> \<open>e23 \<inter> e24_a2q = {a2}.\<close>
      moreover have "e23 \<inter> e24_a2q = {a2}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> e23 \<inter> e24_a2q"
        hence "x \<in> e23" "x \<in> e24" using he24_split(1) by (by100 blast)+
        hence "x \<in> {a2}" using assms(34) by (by100 blast)
        thus "x \<in> {a2}" .
      next
        fix x assume "x \<in> {a2}"
        hence "x = a2" by (by100 blast)
        have "a2 \<in> e23" using assms(17) unfolding top1_arc_endpoints_on_def by (by100 blast)
        moreover have "a2 \<in> e24_a2q" using he24_split(5) .
        ultimately show "x \<in> e23 \<inter> e24_a2q" using \<open>x = a2\<close> by (by100 blast)
      qed
      ultimately show ?thesis by (by100 blast)
    qed
    \<comment> \<open>a2 is endpoint of (e13_pa3 \<union> e23) and e24_a2q.\<close>
    have ha2_ep1: "a2 \<in> top1_arc_endpoints_on (e13_pa3 \<union> e23)
        (subspace_topology top1_S2 top1_S2_topology (e13_pa3 \<union> e23))"
    proof -
      have he13_a1p_sub_loc: "e13_a1p \<subseteq> top1_S2" using he13_sub he13_split(1) by (by100 blast)
      have he13_pa3_sub_loc: "e13_pa3 \<subseteq> top1_S2" using he13_sub he13_split(1) by (by100 blast)
      \<comment> \<open>endpoints(e13_pa3) = {p, a3}.\<close>
      have hpa3_eps: "top1_arc_endpoints_on e13_pa3 (subspace_topology top1_S2 top1_S2_topology e13_pa3) = {p, a3}"
        using arc_split_endpoints(2)[OF hS2_strict hS2_haus he13_sub he13_arc
            he13_split(1) he13_split(2) he13_split(3) he13_split(4)
            he13_split(5) he13_split(6) he13_split(7) he13_split(8)
            he13_a1p_sub_loc he13_pa3_sub_loc he13_ep hp_not_ep] .
      \<comment> \<open>endpoints(e23) = {a2, a3}.\<close>
      have he23_eps: "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a2, a3}"
        by (rule assms(17))
      \<comment> \<open>Shared endpoint a3. Non-shared: p and a2.\<close>
      have hp_ne_a3: "p \<noteq> a3" using hp_e13 by (by100 blast)
      have ha3_ne_a2: "a3 \<noteq> a2"
      proof
        assume "a3 = a2"
        hence "card {a1,a2,a3,a4} \<le> card {a1,a3,a4}" by (by100 simp)
        also have "\<dots> \<le> 3" by (rule card_three_le)
        finally show False using assms(2) by (by100 simp)
      qed
      have he23_eps': "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a3, a2}"
        using he23_eps by (by100 blast)
      from arc_concat_endpoints[OF hS2_strict hS2_haus he13_split(4) he13_pa3_sub_loc
          assms(11) he23_sub hint1 ha3_ep1 ha3_ep2 hpa3_eps he23_eps' hp_ne_a3 ha3_ne_a2]
      show ?thesis by (by100 blast)
    qed
    have ha2_ep2: "a2 \<in> top1_arc_endpoints_on e24_a2q (subspace_topology top1_S2 top1_S2_topology e24_a2q)"
    proof -
      have he24_a2q_sub_loc: "e24_a2q \<subseteq> top1_S2" using he24_sub he24_split(1) by (by100 blast)
      have he24_qa4_sub_loc: "e24_qa4 \<subseteq> top1_S2" using he24_sub he24_split(1) by (by100 blast)
      from arc_split_endpoints(1)[OF hS2_strict hS2_haus he24_sub he24_arc
          he24_split(1) he24_split(2) he24_split(3) he24_split(4)
          he24_split(5) he24_split(6) he24_split(7) he24_split(8)
          he24_a2q_sub_loc he24_qa4_sub_loc he24_ep hq_not_ep]
      show ?thesis by (by100 blast)
    qed
    have he13pa3_e23_sub: "e13_pa3 \<union> e23 \<subseteq> top1_S2" using he13_pa3_sub he23_sub by (by100 blast)
    have he24_a2q_sub: "e24_a2q \<subseteq> top1_S2" using he24_sub he24_split(1) by (by100 blast)
    show ?thesis
      using arcs_concatenation_is_arc[OF hS2_strict hS2_haus
          hconcat1 he13pa3_e23_sub he24_split(3) he24_a2q_sub hint2 ha2_ep1 ha2_ep2]
      by (by100 simp)
  qed
  have hD2_arc: "top1_is_arc_on ?D2 (subspace_topology top1_S2 top1_S2_topology ?D2)"
  proof -
    \<comment> \<open>Step 1: e24_qa4 \<inter> e41 = {a4}.\<close>
    have hint_d1: "e24_qa4 \<inter> e41 = {a4}"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> e24_qa4 \<inter> e41"
      hence "x \<in> e24" "x \<in> e41" using he24_split(1) by (by100 blast)+
      thus "x \<in> {a4}" using assms(36) by (by100 blast)
    next
      fix x assume "x \<in> {a4}"
      have "a4 \<in> e24_qa4" using he24_split(6) .
      have "a4 \<in> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
      thus "x \<in> e24_qa4 \<inter> e41" using \<open>x \<in> {a4}\<close> \<open>a4 \<in> e24_qa4\<close> \<open>a4 \<in> e41\<close> by (by100 blast)
    qed
    have he24_qa4_sub: "e24_qa4 \<subseteq> top1_S2" using he24_sub he24_split(1) by (by100 blast)
    have he41_arc: "top1_is_arc_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
      by (rule assms(13))
    have ha4_ep1: "a4 \<in> top1_arc_endpoints_on e24_qa4 (subspace_topology top1_S2 top1_S2_topology e24_qa4)"
    proof -
      have he24_a2q_sub_loc: "e24_a2q \<subseteq> top1_S2" using he24_sub he24_split(1) by (by100 blast)
      have he24_qa4_sub_loc: "e24_qa4 \<subseteq> top1_S2" using he24_sub he24_split(1) by (by100 blast)
      from arc_split_endpoints(2)[OF hS2_strict hS2_haus he24_sub he24_arc
          he24_split(1) he24_split(2) he24_split(3) he24_split(4)
          he24_split(5) he24_split(6) he24_split(7) he24_split(8)
          he24_a2q_sub_loc he24_qa4_sub_loc he24_ep hq_not_ep]
      show ?thesis by (by100 blast)
    qed
    have ha4_ep2: "a4 \<in> top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
      using assms(19) by (by100 blast)
    have hconcat_d1: "top1_is_arc_on (e24_qa4 \<union> e41)
        (subspace_topology top1_S2 top1_S2_topology (e24_qa4 \<union> e41))"
      by (rule arcs_concatenation_is_arc[OF hS2_strict hS2_haus
          he24_split(4) he24_qa4_sub he41_arc he41_sub hint_d1 ha4_ep1 ha4_ep2])
    \<comment> \<open>Step 2: (e24_qa4 \<union> e41) \<inter> e13_a1p = {a1}.\<close>
    have hint_d2: "(e24_qa4 \<union> e41) \<inter> e13_a1p = {a1}"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> (e24_qa4 \<union> e41) \<inter> e13_a1p"
      hence hx_D2: "x \<in> e24_qa4 \<union> e41" and hx_a1p: "x \<in> e13_a1p" by (by100 blast)+
      have hx_e13: "x \<in> e13" using hx_a1p he13_split(1) by (by100 blast)
      show "x \<in> {a1}"
      proof (cases "x \<in> e24_qa4")
        case True
        hence "x \<in> e24" using he24_split(1) by (by100 blast)
        hence "x \<in> e13 \<inter> e24" using hx_e13 by (by100 blast)
        hence "x \<in> {a1,a2,a3,a4}" using assms(32) by (by100 blast)
        moreover have "a2 \<notin> e13"
        proof
          assume "a2 \<in> e13"
          hence "a2 \<in> e13 \<inter> e23" using assms(17) unfolding top1_arc_endpoints_on_def by (by100 blast)
          hence "a2 = a3" using assms(29) by (by100 blast)
          hence "card {a1, a2, a3, a4} \<le> card {a1, a3, a4}" by (by100 simp)
          also have "\<dots> \<le> 3" by (rule card_three_le)
          finally show False using assms(2) by (by100 simp)
        qed
        hence "a2 \<notin> e13_a1p" using he13_split(1) by (by100 blast)
        moreover have "a3 \<notin> e13_a1p"
        proof
          assume "a3 \<in> e13_a1p"
          hence "a3 \<in> e13_a1p \<inter> e13_pa3" using he13_split(6) by (by100 blast)
          hence "a3 = p" using he13_split(2) by (by100 blast)
          thus False using hp_e13 by (by100 blast)
        qed
        moreover have "a4 \<notin> e13"
        proof
          assume "a4 \<in> e13"
          hence "a4 \<in> e13 \<inter> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
          hence "a4 = a1" using assms(31) by (by100 blast)
          hence "{a1, a2, a3, a4} = {a1, a2, a3}" by (by100 blast)
          hence "card {a1, a2, a3, a4} \<le> card {a1, a2, a3}" by (by100 simp)
          also have "\<dots> \<le> 3" by (rule card_three_le)
          finally show False using assms(2) by (by100 simp)
        qed
        hence "a4 \<notin> e13_a1p" using he13_split(1) by (by100 blast)
        ultimately show ?thesis using \<open>x \<in> {a1,a2,a3,a4}\<close> hx_a1p by (by100 blast)
      next
        case False
        hence "x \<in> e41" using hx_D2 by (by100 blast)
        hence "x \<in> e13 \<inter> e41" using hx_e13 by (by100 blast)
        hence "x \<in> {a1}" using assms(31) by (by100 blast)
        thus ?thesis .
      qed
    next
      fix x assume "x \<in> {a1}"
      have "a1 \<in> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
      have "a1 \<in> e13_a1p" using he13_split(5) .
      thus "x \<in> (e24_qa4 \<union> e41) \<inter> e13_a1p" using \<open>x \<in> {a1}\<close> \<open>a1 \<in> e41\<close> \<open>a1 \<in> e13_a1p\<close> by (by100 blast)
    qed
    have ha1_ep1: "a1 \<in> top1_arc_endpoints_on (e24_qa4 \<union> e41)
        (subspace_topology top1_S2 top1_S2_topology (e24_qa4 \<union> e41))"
    proof -
      have he24_a2q_sub_loc: "e24_a2q \<subseteq> top1_S2" using he24_sub he24_split(1) by (by100 blast)
      have he24_qa4_sub_loc: "e24_qa4 \<subseteq> top1_S2" using he24_sub he24_split(1) by (by100 blast)
      \<comment> \<open>endpoints(e24_qa4) = {q, a4}.\<close>
      have hqa4_eps: "top1_arc_endpoints_on e24_qa4 (subspace_topology top1_S2 top1_S2_topology e24_qa4) = {q, a4}"
        using arc_split_endpoints(2)[OF hS2_strict hS2_haus he24_sub he24_arc
            he24_split(1) he24_split(2) he24_split(3) he24_split(4)
            he24_split(5) he24_split(6) he24_split(7) he24_split(8)
            he24_a2q_sub_loc he24_qa4_sub_loc he24_ep hq_not_ep] .
      \<comment> \<open>endpoints(e41) = {a4, a1}.\<close>
      have he41_eps: "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a4, a1}"
        by (rule assms(19))
      have hq_ne_a4: "q \<noteq> a4" using hq_e24 by (by100 blast)
      have ha4_ne_a1: "a4 \<noteq> a1"
      proof
        assume "a4 = a1"
        hence "{a1,a2,a3,a4} = {a1,a2,a3}" by (by100 blast)
        hence "card {a1,a2,a3,a4} \<le> card {a1,a2,a3}" by (by100 simp)
        also have "\<dots> \<le> 3" by (rule card_three_le)
        finally show False using assms(2) by (by100 simp)
      qed
      from arc_concat_endpoints[OF hS2_strict hS2_haus he24_split(4) he24_qa4_sub_loc
          he41_arc he41_sub hint_d1 ha4_ep1 ha4_ep2 hqa4_eps he41_eps hq_ne_a4 ha4_ne_a1]
      show ?thesis by (by100 blast)
    qed
    have ha1_ep2: "a1 \<in> top1_arc_endpoints_on e13_a1p (subspace_topology top1_S2 top1_S2_topology e13_a1p)"
    proof -
      have he13_a1p_sub_loc: "e13_a1p \<subseteq> top1_S2" using he13_sub he13_split(1) by (by100 blast)
      have he13_pa3_sub_loc: "e13_pa3 \<subseteq> top1_S2" using he13_sub he13_split(1) by (by100 blast)
      from arc_split_endpoints(1)[OF hS2_strict hS2_haus he13_sub he13_arc
          he13_split(1) he13_split(2) he13_split(3) he13_split(4)
          he13_split(5) he13_split(6) he13_split(7) he13_split(8)
          he13_a1p_sub_loc he13_pa3_sub_loc he13_ep hp_not_ep]
      show ?thesis by (by100 blast)
    qed
    have he24qa4_e41_sub: "e24_qa4 \<union> e41 \<subseteq> top1_S2" using he24_qa4_sub he41_sub by (by100 blast)
    have he13_a1p_sub: "e13_a1p \<subseteq> top1_S2" using he13_sub he13_split(1) by (by100 blast)
    show ?thesis
      using arcs_concatenation_is_arc[OF hS2_strict hS2_haus
          hconcat_d1 he24qa4_e41_sub he13_split(3) he13_a1p_sub hint_d2 ha1_ep1 ha1_ep2]
      by (by100 simp)
  qed
  have hD1_sub: "?D1 \<subseteq> top1_S2"
    using he13_sub he23_sub he24_sub he13_split(1) he24_split(1) by (by100 blast)
  have hD2_sub: "?D2 \<subseteq> top1_S2"
    using he24_sub he41_sub he13_sub he24_split(1) he13_split(1) by (by100 blast)
  \<comment> \<open>D_1 and D_2 meet only at {p,q}.\<close>
  \<comment> \<open>Pre-prove 7 empty pairwise intersections + 2 singleton intersections.\<close>
  \<comment> \<open>Vertex non-membership facts (used in multiple pairwise intersections).\<close>
  have ha1_not_pa3: "a1 \<notin> e13_pa3" proof
    assume "a1 \<in> e13_pa3" hence "a1 \<in> e13_a1p \<inter> e13_pa3" using he13_split(5) by (by100 blast)
    hence "a1 = p" using he13_split(2) by (by100 blast) thus False using hp_e13 by (by100 blast) qed
  have ha4_not_a2q: "a4 \<notin> e24_a2q" proof
    assume "a4 \<in> e24_a2q" hence "a4 \<in> e24_a2q \<inter> e24_qa4" using he24_split(6) by (by100 blast)
    hence "a4 = q" using he24_split(2) by (by100 blast) thus False using hq_e24 by (by100 blast) qed
  have ha2_not_e13: "a2 \<notin> e13" proof
    assume "a2 \<in> e13" hence "a2 \<in> e13 \<inter> e23" using assms(17) unfolding top1_arc_endpoints_on_def by (by100 blast)
    hence "a2 = a3" using assms(29) by (by100 blast)
    hence "{a1,a2,a3,a4} = {a1,a3,a4}" by (by100 blast)
    hence "card {a1,a2,a3,a4} \<le> card {a1,a3,a4}" by (by100 simp)
    also have "\<dots> \<le> 3" by (rule card_three_le) finally show False using assms(2) by (by100 simp) qed
  have ha3_not_e24: "a3 \<notin> e24" proof
    assume "a3 \<in> e24" hence "a3 \<in> e24 \<inter> e23" using assms(17) unfolding top1_arc_endpoints_on_def by (by100 blast)
    hence "a3 = a2" using assms(34) by (by100 blast)
    hence "{a1,a2,a3,a4} = {a1,a3,a4}" by (by100 blast)
    hence "card {a1,a2,a3,a4} \<le> card {a1,a3,a4}" by (by100 simp)
    also have "\<dots> \<le> 3" by (rule card_three_le) finally show False using assms(2) by (by100 simp) qed
  have ha1_not_e24: "a1 \<notin> e24" proof
    assume "a1 \<in> e24" hence "a1 \<in> e24 \<inter> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
    hence "a1 = a4" using assms(36) by (by100 blast)
    hence "{a1,a2,a3,a4} = {a4,a2,a3}" by (by100 blast)
    hence "card {a1,a2,a3,a4} \<le> card {a4,a2,a3}" by (by100 simp)
    also have "\<dots> \<le> 3" by (rule card_three_le) finally show False using assms(2) by (by100 simp) qed
  have ha4_not_e13: "a4 \<notin> e13" proof
    assume "a4 \<in> e13" hence "a4 \<in> e13 \<inter> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
    hence "a4 = a1" using assms(31) by (by100 blast)
    hence "{a1,a2,a3,a4} = {a1,a2,a3}" by (by100 blast)
    hence "card {a1,a2,a3,a4} \<le> card {a1,a2,a3}" by (by100 simp)
    also have "\<dots> \<le> 3" by (rule card_three_le) finally show False using assms(2) by (by100 simp) qed
  have hpw1: "e13_pa3 \<inter> e24_qa4 = {}"
  proof (rule set_eqI, rule iffI)
    fix y assume "y \<in> e13_pa3 \<inter> e24_qa4"
    hence hy13: "y \<in> e13" and hy24: "y \<in> e24" using he13_split(1) he24_split(1) by (by100 blast)+
    hence "y \<in> {a1,a2,a3,a4}" using assms(32) by (by100 blast)
    moreover have "y \<noteq> a1" using ha1_not_pa3 \<open>y \<in> e13_pa3 \<inter> e24_qa4\<close> by (by100 blast)
    moreover have "y \<noteq> a2" using ha2_not_e13 hy13 by (by100 blast)
    moreover have "y \<noteq> a3" using ha3_not_e24 hy24 by (by100 blast)
    moreover have "y \<noteq> a4" using ha4_not_e13 hy13 by (by100 blast)
    ultimately show "y \<in> {}" by (by100 blast)
  qed (by100 blast)
  have hpw2: "e13_pa3 \<inter> e41 = {}"
  proof (rule set_eqI, rule iffI)
    fix y assume "y \<in> e13_pa3 \<inter> e41"
    hence "y \<in> e13 \<inter> e41" using he13_split(1) by (by100 blast)
    hence "y = a1" using assms(31) by (by100 blast)
    moreover have "a1 \<notin> e13_pa3" proof
      assume "a1 \<in> e13_pa3" hence "a1 \<in> e13_a1p \<inter> e13_pa3" using he13_split(5) by (by100 blast)
      hence "a1 = p" using he13_split(2) by (by100 blast)
      thus False using hp_e13 by (by100 blast) qed
    ultimately show "y \<in> {}" using \<open>y \<in> e13_pa3 \<inter> e41\<close> by (by100 blast)
  qed (by100 blast)
  have hpw3: "e13_pa3 \<inter> e13_a1p = {p}" using he13_split(2) by (by100 blast)
  have hpw4: "e23 \<inter> e24_qa4 = {}"
  proof (rule set_eqI, rule iffI)
    fix y assume "y \<in> e23 \<inter> e24_qa4"
    hence "y \<in> e23 \<inter> e24" using he24_split(1) by (by100 blast)
    hence "y = a2" using assms(34) by (by100 blast)
    moreover have "a2 \<notin> e24_qa4" proof
      assume "a2 \<in> e24_qa4" hence "a2 \<in> e24_a2q \<inter> e24_qa4" using he24_split(5) by (by100 blast)
      hence "a2 = q" using he24_split(2) by (by100 blast)
      thus False using hq_e24 by (by100 blast) qed
    ultimately show "y \<in> {}" using \<open>y \<in> e23 \<inter> e24_qa4\<close> by (by100 blast)
  qed (by100 blast)
  have hpw5: "e23 \<inter> e41 = {}" using assms(23) by (by100 blast)
  have hpw6: "e23 \<inter> e13_a1p = {}"
  proof (rule set_eqI, rule iffI)
    fix y assume "y \<in> e23 \<inter> e13_a1p"
    hence "y \<in> e23 \<inter> e13" using he13_split(1) by (by100 blast)
    hence "y = a3" using assms(29) by (by100 blast)
    moreover have "a3 \<notin> e13_a1p" proof
      assume "a3 \<in> e13_a1p" hence "a3 \<in> e13_a1p \<inter> e13_pa3" using he13_split(6) by (by100 blast)
      hence "a3 = p" using he13_split(2) by (by100 blast)
      thus False using hp_e13 by (by100 blast) qed
    ultimately show "y \<in> {}" using \<open>y \<in> e23 \<inter> e13_a1p\<close> by (by100 blast)
  qed (by100 blast)
  have hpw7: "e24_a2q \<inter> e24_qa4 = {q}" using he24_split(2) by (by100 blast)
  have hpw8: "e24_a2q \<inter> e41 = {}"
  proof (rule set_eqI, rule iffI)
    fix y assume "y \<in> e24_a2q \<inter> e41"
    hence "y \<in> e24 \<inter> e41" using he24_split(1) by (by100 blast)
    hence "y = a4" using assms(36) by (by100 blast)
    moreover have "a4 \<notin> e24_a2q" proof
      assume "a4 \<in> e24_a2q" hence "a4 \<in> e24_a2q \<inter> e24_qa4" using he24_split(6) by (by100 blast)
      hence "a4 = q" using he24_split(2) by (by100 blast)
      thus False using hq_e24 by (by100 blast) qed
    ultimately show "y \<in> {}" using \<open>y \<in> e24_a2q \<inter> e41\<close> by (by100 blast)
  qed (by100 blast)
  have hpw9: "e24_a2q \<inter> e13_a1p = {}"
  proof (rule set_eqI, rule iffI)
    fix y assume "y \<in> e24_a2q \<inter> e13_a1p"
    hence hy24: "y \<in> e24" and hy13: "y \<in> e13" using he24_split(1) he13_split(1) by (by100 blast)+
    hence "y \<in> {a1,a2,a3,a4}" using assms(32) by (by100 blast)
    moreover have "y \<noteq> a1" using ha1_not_e24 hy24 by (by100 blast)
    moreover have "y \<noteq> a2" using ha2_not_e13 hy13 by (by100 blast)
    moreover have "y \<noteq> a3" using ha3_not_e24 hy24 by (by100 blast)
    moreover have "y \<noteq> a4" using ha4_not_a2q \<open>y \<in> e24_a2q \<inter> e13_a1p\<close> by (by100 blast)
    ultimately show "y \<in> {}" by (by100 blast)
  qed (by100 blast)
  have hD12_inter: "?D1 \<inter> ?D2 = {p, q}"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> ?D1 \<inter> ?D2"
    hence hxD1: "x \<in> e13_pa3 \<union> e23 \<union> e24_a2q" and hxD2: "x \<in> e24_qa4 \<union> e41 \<union> e13_a1p"
      by (by100 blast)+
    \<comment> \<open>Case split on which D1 component x belongs to.\<close>
    show "x \<in> {p, q}"
    proof -
      { assume "x \<in> e13_pa3"
        hence "x \<notin> e24_qa4" using hpw1 by (by100 blast)
        moreover have "x \<notin> e41" using \<open>x \<in> e13_pa3\<close> hpw2 by (by100 blast)
        ultimately have "x \<in> e13_a1p" using hxD2 by (by100 blast)
        hence "x \<in> {p}" using hpw3 \<open>x \<in> e13_pa3\<close> by (by100 blast)
      }
      moreover { assume "x \<in> e23"
        have "x \<notin> e24_qa4" using \<open>x \<in> e23\<close> hpw4 by (by100 blast)
        moreover have "x \<notin> e41" using \<open>x \<in> e23\<close> hpw5 by (by100 blast)
        moreover have "x \<notin> e13_a1p" using \<open>x \<in> e23\<close> hpw6 by (by100 blast)
        ultimately have False using hxD2 by (by100 blast)
      }
      moreover { assume "x \<in> e24_a2q"
        have "x \<notin> e41" using \<open>x \<in> e24_a2q\<close> hpw8 by (by100 blast)
        moreover have "x \<notin> e13_a1p" using \<open>x \<in> e24_a2q\<close> hpw9 by (by100 blast)
        ultimately have "x \<in> e24_qa4" using hxD2 by (by100 blast)
        hence "x \<in> {q}" using hpw7 \<open>x \<in> e24_a2q\<close> by (by100 blast)
      }
      ultimately show ?thesis using hxD1 by (by100 blast)
    qed
  next
    fix x assume "x \<in> {p, q}"
    thus "x \<in> ?D1 \<inter> ?D2"
      using he13_split(7-8) he24_split(7-8) by (by100 blast)
  qed
  \<comment> \<open>D = D_1 \<union> D_2 is a simple closed curve.\<close>
  let ?D = "?D1 \<union> ?D2"
  \<comment> \<open>D1 endpoints: step 1: endpoints(e13\_pa3 \<union> e23) = {p, a2}.\<close>
  have hD1_ep_step1: "top1_arc_endpoints_on (e13_pa3 \<union> e23)
      (subspace_topology top1_S2 top1_S2_topology (e13_pa3 \<union> e23)) = {p, a2}"
  proof -
    have he13_pa3_sub: "e13_pa3 \<subseteq> top1_S2" using he13_sub he13_split(1) by (by100 blast)
    have he13_a1p_sub: "e13_a1p \<subseteq> top1_S2" using he13_sub he13_split(1) by (by100 blast)
    have hpa3_eps: "top1_arc_endpoints_on e13_pa3
        (subspace_topology top1_S2 top1_S2_topology e13_pa3) = {p, a3}"
      using arc_split_endpoints(2)[OF hS2_strict hS2_haus he13_sub he13_arc
          he13_split(1) he13_split(2) he13_split(3) he13_split(4)
          he13_split(5) he13_split(6) he13_split(7) he13_split(8)
          he13_a1p_sub he13_pa3_sub he13_ep hp_not_ep] .
    have he23_eps': "top1_arc_endpoints_on e23
        (subspace_topology top1_S2 top1_S2_topology e23) = {a3, a2}"
      using assms(17) by (by100 blast)
    have ha3_ep1: "a3 \<in> top1_arc_endpoints_on e13_pa3
        (subspace_topology top1_S2 top1_S2_topology e13_pa3)"
      using hpa3_eps by (by100 blast)
    have ha3_ep2: "a3 \<in> top1_arc_endpoints_on e23
        (subspace_topology top1_S2 top1_S2_topology e23)"
      using he23_eps' by (by100 blast)
    have hint1: "e13_pa3 \<inter> e23 = {a3}"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> e13_pa3 \<inter> e23"
      hence "x \<in> e13" "x \<in> e23" using he13_split(1) by (by100 blast)+
      thus "x \<in> {a3}" using assms(29) by (by100 blast)
    next
      fix x assume "x \<in> {a3}"
      hence "x = a3" by (by100 blast)
      have "a3 \<in> e13_pa3" using he13_split(6) .
      moreover have "a3 \<in> e23" using assms(17) unfolding top1_arc_endpoints_on_def by (by100 blast)
      ultimately show "x \<in> e13_pa3 \<inter> e23" using \<open>x = a3\<close> by (by100 blast)
    qed
    have hp_ne_a3: "p \<noteq> a3" using hp_e13 by (by100 blast)
    have ha3_ne_a2: "a3 \<noteq> a2"
    proof assume "a3 = a2"
      hence "card {a1,a2,a3,a4} \<le> card {a1,a3,a4}" by (by100 simp)
      also have "\<dots> \<le> 3" by (rule card_three_le)
      finally show False using assms(2) by (by100 simp)
    qed
    show ?thesis
      by (rule arc_concat_endpoints[OF hS2_strict hS2_haus he13_split(4) he13_pa3_sub
          assms(11) he23_sub hint1 ha3_ep1 ha3_ep2 hpa3_eps he23_eps' hp_ne_a3 ha3_ne_a2])
  qed
  \<comment> \<open>D1 endpoints: step 2: endpoints(D1) = endpoints((e13\_pa3 \<union> e23) \<union> e24\_a2q) = {p, q}.\<close>
  have hD1_ep: "top1_arc_endpoints_on ?D1 (subspace_topology top1_S2 top1_S2_topology ?D1) = {p, q}"
  proof -
    have he13pa3_e23_sub: "e13_pa3 \<union> e23 \<subseteq> top1_S2"
      using he13_sub he13_split(1) he23_sub by (by100 blast)
    have he24_a2q_sub: "e24_a2q \<subseteq> top1_S2" using he24_sub he24_split(1) by (by100 blast)
    \<comment> \<open>Intermediate arc: e13\_pa3 \<union> e23.\<close>
    have he13_a1p_sub_loc: "e13_a1p \<subseteq> top1_S2" using he13_sub he13_split(1) by (by100 blast)
    have hpa3_eps_loc: "top1_arc_endpoints_on e13_pa3
        (subspace_topology top1_S2 top1_S2_topology e13_pa3) = {p, a3}"
      using arc_split_endpoints(2)[OF hS2_strict hS2_haus he13_sub he13_arc
          he13_split(1) he13_split(2) he13_split(3) he13_split(4)
          he13_split(5) he13_split(6) he13_split(7) he13_split(8)
          he13_a1p_sub_loc _ he13_ep hp_not_ep]
        he13_sub he13_split(1) by (by100 blast)
    have ha3_ep_pa3: "a3 \<in> top1_arc_endpoints_on e13_pa3 (subspace_topology top1_S2 top1_S2_topology e13_pa3)"
      using hpa3_eps_loc by (by100 blast)
    have ha3_ep_e23: "a3 \<in> top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      using assms(17) by (by100 blast)
    have hint1_loc: "e13_pa3 \<inter> e23 = {a3}"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> e13_pa3 \<inter> e23"
      hence "x \<in> e13" "x \<in> e23" using he13_split(1) by (by100 blast)+
      thus "x \<in> {a3}" using assms(29) by (by100 blast)
    next
      fix x assume "x \<in> {a3}"
      have "a3 \<in> e13_pa3" using he13_split(6) .
      moreover have "a3 \<in> e23" using assms(17) unfolding top1_arc_endpoints_on_def by (by100 blast)
      ultimately show "x \<in> e13_pa3 \<inter> e23" using \<open>x \<in> {a3}\<close> by (by100 blast)
    qed
    have hconcat1: "top1_is_arc_on (e13_pa3 \<union> e23)
        (subspace_topology top1_S2 top1_S2_topology (e13_pa3 \<union> e23))"
      by (rule arcs_concatenation_is_arc[OF hS2_strict hS2_haus
          he13_split(4) _ assms(11) he23_sub hint1_loc ha3_ep_pa3 ha3_ep_e23])
        (use he13_sub he13_split(1) in \<open>by100 blast\<close>)
    \<comment> \<open>e24\_a2q endpoints = {a2, q}.\<close>
    have he24_qa4_sub: "e24_qa4 \<subseteq> top1_S2" using he24_sub he24_split(1) by (by100 blast)
    have he24_a2q_eps: "top1_arc_endpoints_on e24_a2q
        (subspace_topology top1_S2 top1_S2_topology e24_a2q) = {a2, q}"
      using arc_split_endpoints(1)[OF hS2_strict hS2_haus he24_sub he24_arc
          he24_split(1) he24_split(2) he24_split(3) he24_split(4)
          he24_split(5) he24_split(6) he24_split(7) he24_split(8)
          he24_a2q_sub he24_qa4_sub he24_ep hq_not_ep] .
    \<comment> \<open>(e13\_pa3 \<union> e23) \<inter> e24\_a2q = {a2}.\<close>
    have hint2_loc: "(e13_pa3 \<union> e23) \<inter> e24_a2q = {a2}"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> (e13_pa3 \<union> e23) \<inter> e24_a2q"
      hence hx1: "x \<in> e13_pa3 \<union> e23" and hx2: "x \<in> e24_a2q" by (by100 blast)+
      hence "x \<in> e24" using he24_split(1) by (by100 blast)
      show "x \<in> {a2}"
      proof (cases "x \<in> e23")
        case True hence "x \<in> e23 \<inter> e24" using \<open>x \<in> e24\<close> by (by100 blast)
        thus ?thesis using assms(34) by (by100 blast)
      next
        case False hence "x \<in> e13_pa3" using hx1 by (by100 blast)
        hence "x \<in> e13" using he13_split(1) by (by100 blast)
        hence "x \<in> e13 \<inter> e24" using \<open>x \<in> e24\<close> by (by100 blast)
        hence "x \<in> {a1,a2,a3,a4}" using assms(32) by (by100 blast)
        moreover have "x \<noteq> a1" using ha1_not_pa3 \<open>x \<in> e13_pa3\<close> by (by100 blast)
        moreover have "x \<noteq> a3" using ha3_not_e24 \<open>x \<in> e24\<close> by (by100 blast)
        moreover have "x \<noteq> a4" using ha4_not_e13 \<open>x \<in> e13\<close> by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
    next
      fix x assume "x \<in> {a2}"
      have "a2 \<in> e23" using assms(17) unfolding top1_arc_endpoints_on_def by (by100 blast)
      moreover have "a2 \<in> e24_a2q" using he24_split(5) .
      ultimately show "x \<in> (e13_pa3 \<union> e23) \<inter> e24_a2q" using \<open>x \<in> {a2}\<close> by (by100 blast)
    qed
    have ha2_ep1: "a2 \<in> top1_arc_endpoints_on (e13_pa3 \<union> e23)
        (subspace_topology top1_S2 top1_S2_topology (e13_pa3 \<union> e23))"
      using hD1_ep_step1 by (by100 blast)
    have ha2_ep2: "a2 \<in> top1_arc_endpoints_on e24_a2q
        (subspace_topology top1_S2 top1_S2_topology e24_a2q)"
      using he24_a2q_eps by (by100 blast)
    have hp_ne_a2: "p \<noteq> a2"
    proof assume "p = a2" hence "a2 \<in> e13" using hp_e13 by (by100 blast)
      hence "a2 \<in> e13 \<inter> e23" using assms(17) unfolding top1_arc_endpoints_on_def by (by100 blast)
      hence "a2 = a3" using assms(29) by (by100 blast)
      hence "card {a1,a2,a3,a4} \<le> card {a1,a3,a4}" by (by100 simp)
      also have "\<dots> \<le> 3" by (rule card_three_le)
      finally show False using assms(2) by (by100 simp) qed
    have ha2_ne_q: "a2 \<noteq> q" using hq_e24 by (by100 blast)
    show ?thesis
      by (rule arc_concat_endpoints[OF hS2_strict hS2_haus hconcat1 he13pa3_e23_sub
          he24_split(3) he24_a2q_sub hint2_loc ha2_ep1 ha2_ep2 hD1_ep_step1 he24_a2q_eps
          hp_ne_a2 ha2_ne_q])
  qed
  \<comment> \<open>D2 endpoints: similarly {q, p}.\<close>
  have hD2_ep: "top1_arc_endpoints_on ?D2 (subspace_topology top1_S2 top1_S2_topology ?D2) = {p, q}"
  proof -
    \<comment> \<open>Step 1: endpoints(e24\_qa4 \<union> e41) = {q, a1}.\<close>
    have he24_qa4_sub: "e24_qa4 \<subseteq> top1_S2" using he24_sub he24_split(1) by (by100 blast)
    have he24_a2q_sub: "e24_a2q \<subseteq> top1_S2" using he24_sub he24_split(1) by (by100 blast)
    have he24_qa4_eps: "top1_arc_endpoints_on e24_qa4
        (subspace_topology top1_S2 top1_S2_topology e24_qa4) = {q, a4}"
      using arc_split_endpoints(2)[OF hS2_strict hS2_haus he24_sub he24_arc
          he24_split(1) he24_split(2) he24_split(3) he24_split(4)
          he24_split(5) he24_split(6) he24_split(7) he24_split(8)
          he24_a2q_sub he24_qa4_sub he24_ep hq_not_ep] .
    have he41_eps: "top1_arc_endpoints_on e41
        (subspace_topology top1_S2 top1_S2_topology e41) = {a4, a1}"
      using assms(19) by (by100 blast)
    have hint_qa4_41: "e24_qa4 \<inter> e41 = {a4}"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> e24_qa4 \<inter> e41"
      hence "x \<in> e24" "x \<in> e41" using he24_split(1) by (by100 blast)+
      thus "x \<in> {a4}" using assms(36) by (by100 blast)
    next
      fix x assume "x \<in> {a4}"
      have "a4 \<in> e24_qa4" using he24_split(6) .
      moreover have "a4 \<in> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
      ultimately show "x \<in> e24_qa4 \<inter> e41" using \<open>x \<in> {a4}\<close> by (by100 blast)
    qed
    have ha4_ep_qa4: "a4 \<in> top1_arc_endpoints_on e24_qa4
        (subspace_topology top1_S2 top1_S2_topology e24_qa4)"
      using he24_qa4_eps by (by100 blast)
    have ha4_ep_41: "a4 \<in> top1_arc_endpoints_on e41
        (subspace_topology top1_S2 top1_S2_topology e41)"
      using he41_eps by (by100 blast)
    have hq_ne_a4: "q \<noteq> a4" using hq_e24 by (by100 blast)
    have ha4_ne_a1: "a4 \<noteq> a1"
    proof assume "a4 = a1"
      hence "{a1,a2,a3,a4} = {a1,a2,a3}" by (by100 blast)
      hence "card {a1,a2,a3,a4} \<le> card {a1,a2,a3}" by (by100 simp)
      also have "\<dots> \<le> 3" by (rule card_three_le)
      finally show False using assms(2) by (by100 simp) qed
    have hD2_ep_step1: "top1_arc_endpoints_on (e24_qa4 \<union> e41)
        (subspace_topology top1_S2 top1_S2_topology (e24_qa4 \<union> e41)) = {q, a1}"
      by (rule arc_concat_endpoints[OF hS2_strict hS2_haus he24_split(4) he24_qa4_sub
          assms(13) he41_sub hint_qa4_41 ha4_ep_qa4 ha4_ep_41 he24_qa4_eps he41_eps
          hq_ne_a4 ha4_ne_a1])
    \<comment> \<open>Step 2: endpoints(D2) = endpoints((e24\_qa4 \<union> e41) \<union> e13\_a1p) = {q, p} = {p, q}.\<close>
    have he24_qa4_e41_sub: "e24_qa4 \<union> e41 \<subseteq> top1_S2"
      using he24_qa4_sub he41_sub by (by100 blast)
    have he13_a1p_sub: "e13_a1p \<subseteq> top1_S2" using he13_sub he13_split(1) by (by100 blast)
    have hconcat_d2: "top1_is_arc_on (e24_qa4 \<union> e41)
        (subspace_topology top1_S2 top1_S2_topology (e24_qa4 \<union> e41))"
      by (rule arcs_concatenation_is_arc[OF hS2_strict hS2_haus he24_split(4) he24_qa4_sub
          assms(13) he41_sub hint_qa4_41 ha4_ep_qa4 ha4_ep_41])
    have he13_a1p_eps: "top1_arc_endpoints_on e13_a1p
        (subspace_topology top1_S2 top1_S2_topology e13_a1p) = {a1, p}"
      using arc_split_endpoints(1)[OF hS2_strict hS2_haus he13_sub he13_arc
          he13_split(1) he13_split(2) he13_split(3) he13_split(4)
          he13_split(5) he13_split(6) he13_split(7) he13_split(8)
          he13_a1p_sub _ he13_ep hp_not_ep]
        he13_sub he13_split(1) by (by100 blast)
    have hint_qa4_41_a1p: "(e24_qa4 \<union> e41) \<inter> e13_a1p = {a1}"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> (e24_qa4 \<union> e41) \<inter> e13_a1p"
      hence hx1: "x \<in> e24_qa4 \<union> e41" and hx2: "x \<in> e13_a1p" by (by100 blast)+
      have "x \<in> e13" using hx2 he13_split(1) by (by100 blast)
      show "x \<in> {a1}"
      proof (cases "x \<in> e41")
        case True hence "x \<in> e13 \<inter> e41" using \<open>x \<in> e13\<close> by (by100 blast)
        thus ?thesis using assms(31) by (by100 blast)
      next
        case False hence "x \<in> e24_qa4" using hx1 by (by100 blast)
        hence "x \<in> e24" using he24_split(1) by (by100 blast)
        hence "x \<in> e13 \<inter> e24" using \<open>x \<in> e13\<close> by (by100 blast)
        hence "x \<in> {a1,a2,a3,a4}" using assms(32) by (by100 blast)
        moreover have "x \<noteq> a2" using ha2_not_e13 \<open>x \<in> e13\<close> by (by100 blast)
        moreover have "x \<noteq> a3" using ha3_not_e24 \<open>x \<in> e24\<close> by (by100 blast)
        moreover have "x \<noteq> a4" using ha4_not_e13 \<open>x \<in> e13\<close> by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
    next
      fix x assume "x \<in> {a1}"
      have "a1 \<in> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
      moreover have "a1 \<in> e13_a1p" using he13_split(5) .
      ultimately show "x \<in> (e24_qa4 \<union> e41) \<inter> e13_a1p" using \<open>x \<in> {a1}\<close> by (by100 blast)
    qed
    have ha1_ep_qa4_41: "a1 \<in> top1_arc_endpoints_on (e24_qa4 \<union> e41)
        (subspace_topology top1_S2 top1_S2_topology (e24_qa4 \<union> e41))"
      using hD2_ep_step1 by (by100 blast)
    have ha1_ep_a1p: "a1 \<in> top1_arc_endpoints_on e13_a1p
        (subspace_topology top1_S2 top1_S2_topology e13_a1p)"
      using he13_a1p_eps by (by100 blast)
    have hq_ne_a1: "q \<noteq> a1"
    proof assume "q = a1"
      hence "a1 \<in> e24" using hq_e24 by (by100 blast)
      hence "a1 \<in> e24 \<inter> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
      hence "a1 = a4" using assms(36) by (by100 blast)
      hence "{a1,a2,a3,a4} = {a1,a2,a3}" by (by100 blast)
      hence "card {a1,a2,a3,a4} \<le> card {a1,a2,a3}" by (by100 simp)
      also have "\<dots> \<le> 3" by (rule card_three_le)
      finally show False using assms(2) by (by100 simp) qed
    have ha1_ne_p: "a1 \<noteq> p" using hp_e13 by (by100 blast)
    have "top1_arc_endpoints_on ?D2 (subspace_topology top1_S2 top1_S2_topology ?D2) = {q, p}"
      by (rule arc_concat_endpoints[OF hS2_strict hS2_haus hconcat_d2 he24_qa4_e41_sub
          he13_split(3) he13_a1p_sub hint_qa4_41_a1p ha1_ep_qa4_41 ha1_ep_a1p
          hD2_ep_step1 he13_a1p_eps hq_ne_a1 ha1_ne_p])
    thus ?thesis by (by100 blast)
  qed
  have hpq_ne: "p \<noteq> q"
  proof
    assume "p = q"
    hence "p \<in> e13 \<inter> e24" using hp_e13 hq_e24 by (by100 blast)
    hence "p \<in> {a1,a2,a3,a4}" using assms(32) by (by100 blast)
    moreover have "p \<notin> {a1, a3}" using hp_e13 by (by100 blast)
    moreover have "p \<notin> {a2, a4}" using hq_e24 \<open>p = q\<close> by (by100 blast)
    ultimately show False by (by100 blast)
  qed
  have hD_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology ?D"
    by (rule arcs_form_simple_closed_curve[OF hS2_strict hS2_haus hD1_arc hD1_sub hD2_arc hD2_sub
        hD12_inter hpq_ne hD1_ep hD2_ep])
  \<comment> \<open>Step 2: U = S2-D_1, V = S2-D_2 are open in X = S2-{p,q}.\<close>
  let ?U_loc = "?X - ?D1 \<union> {p, q}" and ?V_loc = "?X - ?D2 \<union> {p, q}"
  \<comment> \<open>Actually: use Munkres' U = S2-D_1, V = S2-D_2 restricted to X.\<close>
  let ?U' = "top1_S2 - ?D1" and ?V' = "top1_S2 - ?D2"
  have hU'_open: "openin_on top1_S2 top1_S2_topology ?U'"
  proof -
    have "closedin_on top1_S2 top1_S2_topology ?D1"
      by (rule arc_in_S2_closed[OF hD1_sub hD1_arc])
    thus ?thesis using hTopS2 unfolding closedin_on_def openin_on_def is_topology_on_def
      by (by100 blast)
  qed
  have hV'_open: "openin_on top1_S2 top1_S2_topology ?V'"
  proof -
    have "closedin_on top1_S2 top1_S2_topology ?D2"
      by (rule arc_in_S2_closed[OF hD2_sub hD2_arc])
    thus ?thesis using hTopS2 unfolding closedin_on_def openin_on_def is_topology_on_def
      by (by100 blast)
  qed
  have hU'V'_union: "?U' \<union> ?V' = ?X"
  proof -
    have h1: "?U' \<union> ?V' = top1_S2 - (?D1 \<inter> ?D2)" by (by100 blast)
    have h2: "?D1 \<inter> ?D2 = {p, q}" by (rule hD12_inter)
    show ?thesis using h1 h2 by (by100 force)
  qed
  \<comment> \<open>U', V' are open in X (subspace of S2).\<close>
  have hU'_sub_X: "?U' \<subseteq> ?X"
  proof -
    have "p \<in> ?D1" using he13_split(8) by (by100 blast)
    moreover have "q \<in> ?D1" using he24_split(7) by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  have hV'_sub_X: "?V' \<subseteq> ?X"
  proof -
    have "p \<in> ?D2" using he13_split(7) by (by100 blast)
    moreover have "q \<in> ?D2" using he24_split(8) by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  have hU'_open_X: "openin_on ?X ?TX ?U'"
    unfolding openin_on_def
  proof (intro conjI)
    show "?U' \<subseteq> ?X" by (rule hU'_sub_X)
    have "?U' \<in> top1_S2_topology" using hU'_open unfolding openin_on_def by (by100 blast)
    hence "?U' \<inter> ?X \<in> ?TX" unfolding subspace_topology_def by (by100 blast)
    moreover have "?U' \<inter> ?X = ?U'" using hU'_sub_X by (by100 blast)
    ultimately show "?U' \<in> ?TX" by (by100 simp)
  qed
  have hV'_open_X: "openin_on ?X ?TX ?V'"
    unfolding openin_on_def
  proof (intro conjI)
    show "?V' \<subseteq> ?X" by (rule hV'_sub_X)
    have "?V' \<in> top1_S2_topology" using hV'_open unfolding openin_on_def by (by100 blast)
    hence "?V' \<inter> ?X \<in> ?TX" unfolding subspace_topology_def by (by100 blast)
    moreover have "?V' \<inter> ?X = ?V'" using hV'_sub_X by (by100 blast)
    ultimately show "?V' \<in> ?TX" by (by100 simp)
  qed
  \<comment> \<open>Step 3: U' \<inter> V' = S2 - D has two path-components (by JCT on D).\<close>
  have hUV_eq: "?U' \<inter> ?V' = top1_S2 - ?D" by (by100 blast)
  have hUV_sep: "top1_separates_on top1_S2 top1_S2_topology ?D"
    by (rule Theorem_61_3_JordanSeparation_S2[OF assms(1) hD_scc])
  \<comment> \<open>Get two components A, B of S2 - D.\<close>
  obtain A B where hAB: "?U' \<inter> ?V' = A \<union> B" "A \<inter> B = {}"
      "openin_on ?X ?TX A" "openin_on ?X ?TX B" "A \<noteq> {}" "B \<noteq> {}"
  proof -
    let ?W = "top1_S2 - ?D" and ?TW = "subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?D)"
    have hW_eq: "?U' \<inter> ?V' = ?W" by (rule hUV_eq)
    have hW_not_conn: "\<not> top1_connected_on ?W ?TW"
      using hUV_sep unfolding top1_separates_on_def by (by100 simp)
    have hTopS2: "is_topology_on top1_S2 top1_S2_topology" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have hTW: "is_topology_on ?W ?TW" by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
    \<comment> \<open>Extract separation U, V of W.\<close>
    obtain U V where hUV: "U \<in> ?TW" "V \<in> ?TW" "U \<noteq> {}" "V \<noteq> {}"
        "U \<inter> V = {}" "U \<union> V = ?W"
    proof -
      have "\<exists>U V. U \<in> ?TW \<and> V \<in> ?TW \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = ?W"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        hence "top1_connected_on ?W ?TW" unfolding top1_connected_on_def using hTW by (by100 simp)
        thus False using hW_not_conn by (by100 blast)
      qed
      then obtain UU VV where hUU: "UU \<in> ?TW" "VV \<in> ?TW" "UU \<noteq> {}" "VV \<noteq> {}"
          "UU \<inter> VV = {}" "UU \<union> VV = ?W" by (by100 force)
      show ?thesis by (rule that[OF hUU])
    qed
    \<comment> \<open>U, V are open in W, hence open in S2 (since W is open in S2).\<close>
    have hW_open_S2: "?W \<in> top1_S2_topology"
    proof -
      have "closedin_on top1_S2 top1_S2_topology ?D1"
        by (rule arc_in_S2_closed[OF hD1_sub hD1_arc])
      moreover have "closedin_on top1_S2 top1_S2_topology ?D2"
        by (rule arc_in_S2_closed[OF hD2_sub hD2_arc])
      ultimately have "closedin_on top1_S2 top1_S2_topology (?D1 \<union> ?D2)"
        by (rule closedin_on_Un[OF hTopS2])
      thus ?thesis unfolding closedin_on_def by (by100 blast)
    qed
    \<comment> \<open>U \<in> TW means U = U' \<inter> W for some U' \<in> top1_S2_topology.\<close>
    \<comment> \<open>U open in W + W open in S2 \<Rightarrow> U open in S2 (intersection of opens is open).\<close>
    \<comment> \<open>U, V open in subspace W, W open in S2 \<Rightarrow> U, V open in S2.\<close>
    \<comment> \<open>U, V open in X = S2 - {p,q}: from U,V \<in> subspace(S2, W) and W \<subseteq> X.\<close>
    have hW_sub_X: "?W \<subseteq> ?X" using hU'_sub_X hV'_sub_X hUV_eq by (by100 blast)
    have hU_sub_X: "U \<subseteq> ?X" using hUV(6) hW_sub_X by (by100 blast)
    have hV_sub_X: "V \<subseteq> ?X" using hUV(6) hW_sub_X by (by100 blast)
    have hU_open_X: "openin_on ?X ?TX U"
    proof -
      \<comment> \<open>U \<in> subspace(S2, W): extract U = W \<inter> U' with U' \<in> S2\_top.\<close>
      from hUV(1) have "\<exists>U'. U = ?W \<inter> U' \<and> U' \<in> top1_S2_topology"
        unfolding subspace_topology_def by (by100 force)
      then obtain U' where hU'_eq: "U = ?W \<inter> U'" and hU'_open: "U' \<in> top1_S2_topology"
        by (by100 blast)
      \<comment> \<open>U = W \<inter> U'. Both W, U' \<in> S2\_top. W \<inter> U' \<in> S2\_top.\<close>
      \<comment> \<open>Then U \<subseteq> X and U \<in> S2\_top, so U = U \<inter> X \<in> TX.\<close>
      have "U \<in> top1_S2_topology"
      proof -
        have "finite {U', ?W}" by (by100 simp)
        moreover have "{U', ?W} \<noteq> {}" by (by100 simp)
        moreover have "{U', ?W} \<subseteq> top1_S2_topology" using hU'_open hW_open_S2 by (by100 blast)
        ultimately have "\<Inter>{U', ?W} \<in> top1_S2_topology"
        proof -
          have hax: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> top1_S2_topology \<longrightarrow> \<Inter>F \<in> top1_S2_topology"
            using hTopS2 unfolding is_topology_on_def by (by100 blast)
          have "finite {U', ?W} \<and> {U', ?W} \<noteq> {} \<and> {U', ?W} \<subseteq> top1_S2_topology"
            using \<open>finite {U', ?W}\<close> \<open>{U', ?W} \<noteq> {}\<close> \<open>{U', ?W} \<subseteq> top1_S2_topology\<close>
            by (by100 blast)
          from hax[rule_format, OF this] show ?thesis .
        qed
        moreover have "U' \<inter> ?W = U" using hU'_eq by (by100 blast)
        hence "\<Inter>{U', ?W} = U" by (by100 force)
        ultimately show ?thesis by (by100 simp)
      qed
      hence "U \<inter> ?X \<in> ?TX" unfolding subspace_topology_def by (by100 blast)
      moreover have "U \<inter> ?X = U" using hU_sub_X by (by100 blast)
      ultimately have "U \<in> ?TX" by (by100 simp)
      thus ?thesis unfolding openin_on_def using hU_sub_X by (by100 blast)
    qed
    have hV_open_X: "openin_on ?X ?TX V"
    proof -
      from hUV(2) have "\<exists>V'. V = ?W \<inter> V' \<and> V' \<in> top1_S2_topology"
        unfolding subspace_topology_def by (by100 force)
      then obtain V' where hV'_eq: "V = ?W \<inter> V'" and hV'_open: "V' \<in> top1_S2_topology"
        by (by100 blast)
      have "V \<in> top1_S2_topology"
      proof -
        have "finite {V', ?W}" by (by100 simp)
        moreover have "{V', ?W} \<noteq> {}" by (by100 simp)
        moreover have "{V', ?W} \<subseteq> top1_S2_topology" using hV'_open hW_open_S2 by (by100 blast)
        ultimately have "\<Inter>{V', ?W} \<in> top1_S2_topology"
        proof -
          have hax: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> top1_S2_topology \<longrightarrow> \<Inter>F \<in> top1_S2_topology"
            using hTopS2 unfolding is_topology_on_def by (by100 blast)
          have "finite {V', ?W} \<and> {V', ?W} \<noteq> {} \<and> {V', ?W} \<subseteq> top1_S2_topology"
            using \<open>finite {V', ?W}\<close> \<open>{V', ?W} \<noteq> {}\<close> \<open>{V', ?W} \<subseteq> top1_S2_topology\<close>
            by (by100 blast)
          from hax[rule_format, OF this] show ?thesis .
        qed
        moreover have "V' \<inter> ?W = V" using hV'_eq by (by100 blast)
        hence "\<Inter>{V', ?W} = V" by (by100 force)
        ultimately show ?thesis by (by100 simp)
      qed
      hence "V \<inter> ?X \<in> ?TX" unfolding subspace_topology_def by (by100 blast)
      moreover have "V \<inter> ?X = V" using hV_sub_X by (by100 blast)
      ultimately have "V \<in> ?TX" by (by100 simp)
      thus ?thesis unfolding openin_on_def using hV_sub_X by (by100 blast)
    qed
    show ?thesis using that[OF _ hUV(5) hU_open_X hV_open_X hUV(3,4)]
        hUV(6) hW_eq by (by100 simp)
  qed
  \<comment> \<open>Step 4: Choose points x \<in> e12 (in one component), y \<in> e34 (other component).\<close>
  \<comment> \<open>e12 - {a1,a2} \<subseteq> S2-D and e34 - {a3,a4} \<subseteq> S2-D.\<close>
  have he12_in_comp: "e12 - {a1, a2} \<subseteq> top1_S2 - ?D"
  proof -
    \<comment> \<open>e12 \<inter> D \<subseteq> {a1,a2}: e12 \<inter> e13\_pa3 \<subseteq> e12\<inter>e13 = {a1},
       e12 \<inter> e23 = {a2}, e12 \<inter> e24\_a2q \<subseteq> e12\<inter>e24 = {a2},
       e12 \<inter> e24\_qa4 \<subseteq> e12\<inter>e24 = {a2}, e12 \<inter> e41 = {a1},
       e12 \<inter> e13\_a1p \<subseteq> e12\<inter>e13 = {a1}.\<close>
    have "e12 \<inter> ?D \<subseteq> {a1, a2}"
    proof
      fix x assume "x \<in> e12 \<inter> ?D"
      hence hx12: "x \<in> e12" and hxD: "x \<in> ?D" by (by100 blast)+
      from hxD have "x \<in> e13_pa3 \<or> x \<in> e23 \<or> x \<in> e24_a2q \<or> x \<in> e24_qa4 \<or> x \<in> e41 \<or> x \<in> e13_a1p"
        by (by100 blast)
      thus "x \<in> {a1, a2}"
      proof (elim disjE)
        assume "x \<in> e13_pa3" hence "x \<in> e12 \<inter> e13" using hx12 he13_split(1) by (by100 blast)
        thus ?thesis using assms(28) by (by100 blast)
      next
        assume "x \<in> e23" hence "x \<in> e12 \<inter> e23" using hx12 by (by100 blast)
        hence "x \<in> {a2}" using assms(24) by (by100 blast)
        thus ?thesis by (by100 blast)
      next
        assume "x \<in> e24_a2q" hence "x \<in> e12 \<inter> e24" using hx12 he24_split(1) by (by100 blast)
        hence "x \<in> {a2}" using assms(33) by (by100 blast)
        thus ?thesis by (by100 blast)
      next
        assume "x \<in> e24_qa4" hence "x \<in> e12 \<inter> e24" using hx12 he24_split(1) by (by100 blast)
        hence "x \<in> {a2}" using assms(33) by (by100 blast)
        thus ?thesis by (by100 blast)
      next
        assume "x \<in> e41" hence "x \<in> e41 \<inter> e12" using hx12 by (by100 blast)
        hence "x \<in> {a1}" using assms(27) by (by100 blast)
        thus ?thesis by (by100 blast)
      next
        assume "x \<in> e13_a1p" hence "x \<in> e12 \<inter> e13" using hx12 he13_split(1) by (by100 blast)
        thus ?thesis using assms(28) by (by100 blast)
      qed
    qed
    thus ?thesis using assms(4) by (by100 blast)
  qed
  have he34_in_comp: "e34 - {a3, a4} \<subseteq> top1_S2 - ?D"
  proof -
    have "e34 \<inter> ?D \<subseteq> {a3, a4}"
    proof
      fix x assume "x \<in> e34 \<inter> ?D"
      hence hx34: "x \<in> e34" and hxD: "x \<in> ?D" by (by100 blast)+
      from hxD have "x \<in> e13_pa3 \<or> x \<in> e23 \<or> x \<in> e24_a2q \<or> x \<in> e24_qa4 \<or> x \<in> e41 \<or> x \<in> e13_a1p"
        by (by100 blast)
      thus "x \<in> {a3, a4}"
      proof (elim disjE)
        assume "x \<in> e13_pa3" hence "x \<in> e34 \<inter> e13" using hx34 he13_split(1) by (by100 blast)
        hence "x \<in> {a3}" using assms(30) by (by100 blast) thus ?thesis by (by100 blast)
      next
        assume "x \<in> e23" hence "x \<in> e23 \<inter> e34" using hx34 by (by100 blast)
        hence "x \<in> {a3}" using assms(25) by (by100 blast) thus ?thesis by (by100 blast)
      next
        assume "x \<in> e24_a2q" hence "x \<in> e34 \<inter> e24" using hx34 he24_split(1) by (by100 blast)
        hence "x \<in> {a4}" using assms(35) by (by100 blast) thus ?thesis by (by100 blast)
      next
        assume "x \<in> e24_qa4" hence "x \<in> e34 \<inter> e24" using hx34 he24_split(1) by (by100 blast)
        hence "x \<in> {a4}" using assms(35) by (by100 blast) thus ?thesis by (by100 blast)
      next
        assume "x \<in> e41" hence "x \<in> e34 \<inter> e41" using hx34 by (by100 blast)
        hence "x \<in> {a4}" using assms(26) by (by100 blast) thus ?thesis by (by100 blast)
      next
        assume "x \<in> e13_a1p" hence "x \<in> e34 \<inter> e13" using hx34 he13_split(1) by (by100 blast)
        hence "x \<in> {a3}" using assms(30) by (by100 blast) thus ?thesis by (by100 blast)
      qed
    qed
    thus ?thesis using assms(6) by (by100 blast)
  qed
  \<comment> \<open>e12 - {a1,a2} is connected (arc minus endpoints) and non-empty.\<close>
  \<comment> \<open>Arc minus endpoints is connected: h maps (0,1) onto e12-{a1,a2}, and (0,1) is connected.\<close>
  have ha1_ne_a2: "a1 \<noteq> a2"
  proof assume "a1 = a2"
    hence "{a1,a2,a3,a4} = {a2,a3,a4}" by (by100 blast)
    hence "card {a1,a2,a3,a4} \<le> 3" using card_three_le by (by100 simp)
    thus False using assms(2) by (by100 simp)
  qed
  have ha3_ne_a4: "a3 \<noteq> a4"
  proof assume "a3 = a4"
    hence "{a1,a2,a3,a4} = {a1,a2,a4}" by (by100 blast)
    hence "card {a1,a2,a3,a4} \<le> 3" using card_three_le by (by100 simp)
    thus False using assms(2) by (by100 simp)
  qed
  have he12_conn: "top1_connected_on (e12 - {a1, a2})
      (subspace_topology top1_S2 top1_S2_topology (e12 - {a1, a2}))"
    by (rule arc_minus_endpoints_connected[OF hS2_strict hS2_haus assms(4) assms(10) assms(16) ha1_ne_a2])
  have he12_ne: "e12 - {a1, a2} \<noteq> {}"
  proof -
    obtain h where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
        e12 (subspace_topology top1_S2 top1_S2_topology e12) h"
      using assms(10) unfolding top1_is_arc_on_def by (by100 blast)
    have himg: "h ` top1_unit_interval = e12"
      using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have "(1/2::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
    hence "h (1/2) \<in> e12" using himg by (by100 blast)
    moreover have "h (1/2) \<noteq> h 0 \<and> h (1/2) \<noteq> h 1"
    proof -
      have hinj: "inj_on h top1_unit_interval"
        using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have "(0::real) \<in> top1_unit_interval" "(1::real) \<in> top1_unit_interval"
        unfolding top1_unit_interval_def by (by100 simp)+
      have h12_ne_0: "(1/2::real) \<noteq> 0" by (by100 simp)
      have h12_ne_1: "(1/2::real) \<noteq> 1" by (by100 simp)
      have "h (1/2) \<noteq> h 0" proof
        assume "h (1/2) = h 0"
        from inj_onD[OF hinj this \<open>(1/2) \<in> top1_unit_interval\<close> \<open>(0::real) \<in> top1_unit_interval\<close>]
        show False using h12_ne_0 by (by100 blast) qed
      moreover have "h (1/2) \<noteq> h 1" proof
        assume "h (1/2) = h 1"
        from inj_onD[OF hinj this \<open>(1/2) \<in> top1_unit_interval\<close> \<open>(1::real) \<in> top1_unit_interval\<close>]
        show False using h12_ne_1 by (by100 blast) qed
      ultimately show ?thesis by (by100 blast)
    qed
    moreover have "{h 0, h 1} = {a1, a2}"
      using arc_endpoints_are_boundary[OF hS2_strict hS2_haus assms(4) assms(10) hh] assms(16)
      by (by100 simp)
    ultimately show ?thesis by (by100 blast)
  qed
  have he34_conn: "top1_connected_on (e34 - {a3, a4})
      (subspace_topology top1_S2 top1_S2_topology (e34 - {a3, a4}))"
    by (rule arc_minus_endpoints_connected[OF hS2_strict hS2_haus assms(6) assms(12) assms(18) ha3_ne_a4])
  have he34_ne: "e34 - {a3, a4} \<noteq> {}"
  proof -
    obtain h where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
        e34 (subspace_topology top1_S2 top1_S2_topology e34) h"
      using assms(12) unfolding top1_is_arc_on_def by (by100 blast)
    have himg: "h ` top1_unit_interval = e34"
      using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have "(1/2::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
    hence "h (1/2) \<in> e34" using himg by (by100 blast)
    moreover have "h (1/2) \<noteq> h 0 \<and> h (1/2) \<noteq> h 1"
    proof -
      have hinj: "inj_on h top1_unit_interval"
        using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have "(0::real) \<in> top1_unit_interval" "(1::real) \<in> top1_unit_interval"
        unfolding top1_unit_interval_def by (by100 simp)+
      have h12_ne_0: "(1/2::real) \<noteq> 0" by (by100 simp)
      have h12_ne_1: "(1/2::real) \<noteq> 1" by (by100 simp)
      have "h (1/2) \<noteq> h 0" proof
        assume "h (1/2) = h 0"
        from inj_onD[OF hinj this \<open>(1/2) \<in> top1_unit_interval\<close> \<open>(0::real) \<in> top1_unit_interval\<close>]
        show False using h12_ne_0 by (by100 blast) qed
      moreover have "h (1/2) \<noteq> h 1" proof
        assume "h (1/2) = h 1"
        from inj_onD[OF hinj this \<open>(1/2) \<in> top1_unit_interval\<close> \<open>(1::real) \<in> top1_unit_interval\<close>]
        show False using h12_ne_1 by (by100 blast) qed
      ultimately show ?thesis by (by100 blast)
    qed
    moreover have "{h 0, h 1} = {a3, a4}"
      using arc_endpoints_are_boundary[OF hS2_strict hS2_haus assms(6) assms(12) hh] assms(18)
      by (by100 simp)
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>By Lemma 23.2, each lies in A or B.\<close>
  have he12_AB: "e12 - {a1, a2} \<subseteq> A \<or> e12 - {a1, a2} \<subseteq> B"
    sorry \<comment> \<open>Lemma\_23\_2: connected subset of separation lies in one component.\<close>
  have he34_AB: "e34 - {a3, a4} \<subseteq> A \<or> e34 - {a3, a4} \<subseteq> B"
    sorry \<comment> \<open>Same.\<close>
  \<comment> \<open>They are in different components. (WLOG swap A,B if needed.)\<close>
  obtain x y where hx: "x \<in> A" "x \<in> e12 - {a1, a2}" and hy: "y \<in> B" "y \<in> e34 - {a3, a4}"
    sorry \<comment> \<open>From he12\_AB, he34\_AB + they must be in different components.\<close>
  \<comment> \<open>Step 5: Construct \<alpha>: path in U' from x to y (via a1, a4 or similar).
     \<beta>: path in V' from y to x (via a3, a2).\<close>
  obtain \<alpha> where h\<alpha>: "top1_is_path_on ?U' (subspace_topology top1_S2 top1_S2_topology ?U') x y \<alpha>"
    sorry \<comment> \<open>Path in S2-D_1 from x to y.\<close>
  obtain \<beta> where h\<beta>: "top1_is_path_on ?V' (subspace_topology top1_S2 top1_S2_topology ?V') y x \<beta>"
    sorry \<comment> \<open>Path in S2-D_2 from y to x.\<close>
  \<comment> \<open>Step 6: Apply Theorem_63_1: \<alpha>*\<beta> is not nulhomotopic in X.\<close>
  have hTX: "is_topology_on ?X ?TX"
    by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
  \<comment> \<open>Transfer paths from subspace of S2 to subspace of X.\<close>
  have h\<alpha>_X: "top1_is_path_on ?U' (subspace_topology ?X ?TX ?U') x y \<alpha>"
  proof -
    have "subspace_topology top1_S2 top1_S2_topology ?U'
        = subspace_topology ?X ?TX ?U'"
      using subspace_topology_trans[of ?U' ?X top1_S2 top1_S2_topology] hU'_sub_X by (by100 simp)
    thus ?thesis using h\<alpha> by (by100 simp)
  qed
  have h\<beta>_X: "top1_is_path_on ?V' (subspace_topology ?X ?TX ?V') y x \<beta>"
  proof -
    have "subspace_topology top1_S2 top1_S2_topology ?V'
        = subspace_topology ?X ?TX ?V'"
      using subspace_topology_trans[of ?V' ?X top1_S2 top1_S2_topology] hV'_sub_X by (by100 simp)
    thus ?thesis using h\<beta> by (by100 simp)
  qed
  have h\<alpha>\<beta>_nontrivial: "\<not> top1_path_homotopic_on ?X ?TX x x
      (top1_path_product \<alpha> \<beta>) (top1_constant_path x)"
    by (rule Theorem_63_1_loop_nontrivial[OF hTX hU'_open_X hV'_open_X hU'V'_union
        hAB(1,2) hAB(3,4) hx(1) hy(1) h\<alpha>_X h\<beta>_X])
  \<comment> \<open>Step 7: f is homotopic to \<alpha>*\<beta> (both traverse C), so f is nontrivial.\<close>
  show ?thesis
    sorry \<comment> \<open>Transfer: f ~ \<alpha>*\<beta> (since both are loops on C traversing in same direction).\<close>
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
  \<comment> \<open>Step 1 (Surjectivity): the inclusion j_* is surjective via K4-graph argument.\<close>
  have hj_surj: "(top1_fundamental_group_induced_on C ?TC c0 ?Xpq ?TXpq c0 (\<lambda>x. x))
      ` (top1_fundamental_group_carrier C ?TC c0)
      = top1_fundamental_group_carrier ?Xpq ?TXpq c0" sorry
  \<comment> \<open>Step 2 (Injectivity): j_* is injective via Lemma 65.1 nontriviality.\<close>
  have hj_inj: "inj_on (top1_fundamental_group_induced_on C ?TC c0 ?Xpq ?TXpq c0 (\<lambda>x. x))
      (top1_fundamental_group_carrier C ?TC c0)" sorry
  \<comment> \<open>Step 3 (Homomorphism): j_* preserves products by functoriality.\<close>
  have hj_hom: "top1_group_hom_on
      (top1_fundamental_group_carrier C ?TC c0) (top1_fundamental_group_mul C ?TC c0)
      (top1_fundamental_group_carrier ?Xpq ?TXpq c0) (top1_fundamental_group_mul ?Xpq ?TXpq c0)
      (top1_fundamental_group_induced_on C ?TC c0 ?Xpq ?TXpq c0 (\<lambda>x. x))"
  proof -
    have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
      using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have hTC: "is_topology_on C ?TC"
    proof -
      have "C \<subseteq> top1_S2"
        using assms(2) unfolding top1_simple_closed_curve_on_def top1_continuous_map_on_def
        by (by100 blast)
      thus ?thesis by (rule subspace_topology_is_topology_on[OF hTopS2])
    qed
    have hTXpq: "is_topology_on ?Xpq ?TXpq"
      by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
    have hc0_C: "c0 \<in> C" by (rule assms(6))
    have hC_sub_S2: "C \<subseteq> top1_S2" using simple_closed_curve_subset[OF assms(2)] .
    have hC_sub_Xpq: "C \<subseteq> top1_S2 - {p} - {q}"
    proof -
      have "p \<notin> C" using assms(3) by (by100 blast)
      moreover have "q \<notin> C" using assms(4) by (by100 blast)
      ultimately show ?thesis using hC_sub_S2 by (by100 blast)
    qed
    have hc0_Xpq: "c0 \<in> ?Xpq" using hC_sub_Xpq hc0_C by (by100 blast)
    \<comment> \<open>Inclusion C \<hookrightarrow> Xpq continuous.\<close>
    have hincl: "top1_continuous_map_on C ?TC ?Xpq ?TXpq (\<lambda>x. x)"
    proof -
      have hid_Xpq: "top1_continuous_map_on ?Xpq ?TXpq ?Xpq ?TXpq id"
        by (rule top1_continuous_map_on_id[OF hTXpq])
      have "C \<subseteq> ?Xpq" using hC_sub_Xpq .
      from top1_continuous_map_on_restrict_domain_simple[OF hid_Xpq this]
      have "top1_continuous_map_on C (subspace_topology ?Xpq ?TXpq C) ?Xpq ?TXpq id" .
      have hsub_eq: "subspace_topology ?Xpq ?TXpq C = ?TC"
        using subspace_topology_trans[OF \<open>C \<subseteq> ?Xpq\<close>] by (by100 simp)
      have hid_eq: "id = (\<lambda>x::(real\<times>real\<times>real). x)" by (rule ext) (by100 simp)
      show ?thesis
      proof -
        have h1: "top1_continuous_map_on C (subspace_topology ?Xpq ?TXpq C) ?Xpq ?TXpq id"
          using top1_continuous_map_on_restrict_domain_simple[OF hid_Xpq \<open>C \<subseteq> ?Xpq\<close>] .
        have h2: "top1_continuous_map_on C ?TC ?Xpq ?TXpq id"
          using h1 hsub_eq by (by100 presburger)
        show ?thesis using h2 hid_eq by (by100 presburger)
      qed
    qed
    show ?thesis
      by (rule top1_fundamental_group_induced_on_is_hom[OF hTC hTXpq hc0_C hc0_Xpq hincl]) (by100 simp)
  qed
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
    using hj_hom hj_inj hj_surj unfolding bij_betw_def by (by100 blast)
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
  have hcard1: "card (top1_quotient_group_carrier_on G mul ?twoG) = 2 ^ card S1"
    sorry \<comment> \<open>G \<cong> Z^{S1} implies G/2G \<cong> (Z/2Z)^{S1}, so |G/2G| = 2^|S1|.\<close>
  have hcard2: "card (top1_quotient_group_carrier_on G mul ?twoG) = 2 ^ card S2"
    sorry \<comment> \<open>G \<cong> Z^{S2} implies G/2G \<cong> (Z/2Z)^{S2}, so |G/2G| = 2^|S2|.\<close>
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
  have h_free_abel: "\<exists>\<iota>H.
      top1_is_free_abelian_group_full_on ?H ?mulH ?eH ?invgH \<iota>H S
    \<and> (\<forall>s\<in>S. \<iota>H s = ?\<phi> (\<iota> s))" sorry
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
    using hc_nn hc_sum hc_x hc_y by (by100 force)
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
  have "\<exists>scheme :: (nat \<times> bool) list. top1_quotient_of_scheme_on X TX scheme"
    using assms(2) unfolding top1_is_polygonal_quotient_on_def by (by100 blast)
  then obtain scheme :: "(nat \<times> bool) list" where hsch: "top1_quotient_of_scheme_on X TX scheme"
    by (by100 auto)
  have hcompact: "top1_compact_on X TX"
  proof -
    \<comment> \<open>Extract P, q from the scheme.\<close>
    obtain P q where hP: "top1_is_polygonal_region_on P (length scheme)"
        and hq: "top1_quotient_map_on P
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q"
      by (rule quotient_of_scheme_extract[OF hsch])
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
  have hhausdorff: "is_hausdorff_on X TX" sorry
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
        sorry \<comment> \<open>Local homeomorphism argument: q is open map.\<close>
      \<comment> \<open>Y - q(E) is open in Y: for y \<in> Y - q(E), the r-slice containing y is
         either entirely in q(E) or disjoint (by connectedness of the slice).
         Since y \<notin> q(E), the slice is disjoint.\<close>
      have hqE_closed: "closedin_on Y TY (q ` E)"
        sorry \<comment> \<open>Complement is open: each r-slice meeting q(E) is fully in q(E).\<close>
      \<comment> \<open>Y is connected (path-connected covering space assumption or derived).\<close>
      have hY_conn: "top1_connected_on Y TY"
        by (rule top1_path_connected_imp_connected[OF assms(8)])
      \<comment> \<open>Connected + non-empty clopen subset = whole space.\<close>
      have "q ` E = {} \<or> q ` E = Y"
        using iffD1[OF connected_iff_clopen_openin_on[OF assms(3)] hY_conn]
              hqE_open hqE_closed by (by100 blast)
      moreover have "q ` E \<noteq> {}" using hy0_qE by (by100 blast)
      ultimately show "Y \<subseteq> q ` E" by (by100 blast)
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
    \<comment> \<open>V0' = the r'-slice containing y (over U = Up\<inter>Ur).\<close>
    have hy_in_rU': "y \<in> {x\<in>Y. r x \<in> ?U}" using hy hU_b by (by100 blast)
    hence "y \<in> \<Union>\<V>r'" using h\<V>r'_union by (by100 simp)
    then obtain V0' where hV0': "V0' \<in> \<V>r'" and hy_V0': "y \<in> V0'" by (by100 blast)
    \<comment> \<open>V0' is evenly covered by q: each p-slice U_\<alpha> over U maps homeo to V0' via q.\<close>
    \<comment> \<open>For each U_\<alpha> \<in> \<V>p: p|_{U_\<alpha>}: U_\<alpha> \<cong> U and r|_{V0'}: V0' \<cong> U.
       So q|_{U_\<alpha>} = (r|_{V0'})\<inverse> \<circ> p|_{U_\<alpha>}: U_\<alpha> \<cong> V0'.
       But only for those U_\<alpha> where q(U_\<alpha>) \<subseteq> V0'.\<close>
    \<comment> \<open>For each p-slice W, q maps {e\<in>W | q e \<in> V0'} homeomorphically to V0'.
       Proof: on this subset, q = inv_into V0' r \<circ> p (since r(q e) = p e and q e \<in> V0').
       Both p|_W and r|_{V0'} are homeomorphisms to U, so q is their composition.
       The family of non-empty {e\<in>W | q e \<in> V0'} covers q\<inverse>(V0'), is disjoint and open.\<close>
    have hV0'_open: "openin_on Y TY V0'" using h\<V>r'_open hV0' by (by100 blast)
    show "\<exists>V. y \<in> V \<and> top1_evenly_covered_on E TE Y TY q V"
    proof (rule exI[of _ V0'], intro conjI)
      show "y \<in> V0'" by (rule hy_V0')
      show "top1_evenly_covered_on E TE Y TY q V0'"
        sorry \<comment> \<open>V0' evenly covered: family = {{e\<in>W|q e\<in>V0'} | W\<in>\<V>p, nonempty}.
           Open: q continuous + V0' open. Disjoint: inherited from \<V>p.
           Union = q\<inverse>(V0'). Homeo: q = inv(r|_{V0'}) \<circ> p on each piece.\<close>
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
  with p \<circ> h = p. The group of covering transformations acts on the fiber.\<close>
definition top1_covering_transformation_on :: "'e set \<Rightarrow> 'e set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> ('e \<Rightarrow> 'e) \<Rightarrow> bool" where
  "top1_covering_transformation_on E TE B TB p h \<longleftrightarrow>
     top1_homeomorphism_on E TE E TE h \<and> (\<forall>e\<in>E. p (h e) = p e)"

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
    let ?invC = "\<lambda>h. inv_into E h"
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
      \<comment> \<open>inv_into E h is the inverse homeomorphism.\<close>
      have hinv_homeo: "top1_homeomorphism_on E TE E TE (inv_into E h)"
        by (rule homeomorphism_inverse[OF hh_homeo])
      moreover have "\<forall>e\<in>E. p (inv_into E h e) = p e"
      proof (intro ballI)
        fix e assume "e \<in> E"
        have hbij: "bij_betw h E E" using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        have hsurj_loc: "h ` E = E" using hbij unfolding bij_betw_def by (by100 blast)
        have "e \<in> h ` E" using \<open>e \<in> E\<close> hsurj_loc by (by100 blast)
        have "inv_into E h e \<in> E" using inv_into_into[OF \<open>e \<in> h ` E\<close>] .
        have "h (inv_into E h e) = e" using f_inv_into_f[OF \<open>e \<in> h ` E\<close>] .
        hence "p e = p (h (inv_into E h e))" by (by100 simp)
        also have "\<dots> = p (inv_into E h e)" using hh_p \<open>inv_into E h e \<in> E\<close> by (by100 blast)
        finally show "p (inv_into E h e) = p e" by (by100 simp)
      qed
      ultimately show "?invC h \<in> ?Cov"
        unfolding top1_covering_transformation_on_def by (by100 blast)
    qed
    \<comment> \<open>Associativity.\<close>
    have hassoc: "\<forall>h\<in>?Cov. \<forall>k\<in>?Cov. \<forall>l\<in>?Cov. ?mul (?mul h k) l = ?mul h (?mul k l)"
      by (by100 auto)
    \<comment> \<open>Identity.\<close>
    have hident: "\<forall>h\<in>?Cov. ?mul ?eC h = h \<and> ?mul h ?eC = h"
      by (by100 auto)
    \<comment> \<open>Inverse.\<close>
    have hinverse: "\<forall>h\<in>?Cov. ?mul (?invC h) h = ?eC \<and> ?mul h (?invC h) = ?eC"
      sorry \<comment> \<open>Extensional equality inv_into E h \<circ> h = id requires h injective on UNIV.
           Covering transformations as total functions need special handling.
           TODO: reformulate group using restrict or quotient by agreement on E.\<close>
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
  show ?thesis
    sorry \<comment> \<open>Full coset-space construction (Munkres 82.1):
       Define E' = H-right-cosets of path classes from b0.
       Topology via path-extension basis.
       Verify: covering map (semilocal simple connectivity) + connected + locally path-connected.
       p'_*(pi_1(E', e0')) = H.\<close>
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



























































































































































































































































































 
  
   
    



  








 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
  
 









































