theory AlgTop_JCT_Base
  imports "Top0.Top1_Ch9_13" "AlgTopH.AlgTopHelpers"
begin


text \<open>The squaring map q(z) = z^2 on S^1 is a covering map (Munkres §53 exercise, used in §57).
  In real coordinates: q(x,y) = (x^2-y^2, 2xy).
  Cover S^1 by 4 open semicircles (upper/lower/left/right half-planes).
  For each, the preimage under q consists of 2 disjoint arcs, and q maps each
  homeomorphically onto the semicircle.\<close>

lemma squaring_map_covering:
  "top1_covering_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology
    (\<lambda>(x, y). (x\<^sup>2 - y\<^sup>2, 2*x*y))"
proof -
  define q :: "real \<times> real \<Rightarrow> real \<times> real" where "q p = (fst p ^ 2 - snd p ^ 2, 2 * fst p * snd p)" for p
  have hq_alt: "q = (\<lambda>(x, y). (x\<^sup>2 - y\<^sup>2, 2*x*y))" unfolding q_def by (intro ext) auto
  \<comment> \<open>q maps S^1 to S^1: if x^2+y^2=1 then (x^2-y^2)^2+(2xy)^2 = (x^2+y^2)^2 = 1.\<close>
  have hq_S1: "\<And>p. p \<in> top1_S1 \<Longrightarrow> q p \<in> top1_S1"
  proof -
    fix p assume hp: "p \<in> top1_S1"
    obtain x y where hxy: "p = (x, y)" by (cases p) auto
    have hS1: "x\<^sup>2 + y\<^sup>2 = 1" using hp unfolding top1_S1_def hxy by simp
    have "(x\<^sup>2 - y\<^sup>2)\<^sup>2 + (2*x*y)\<^sup>2 = x^4 - 2*x\<^sup>2*y\<^sup>2 + y^4 + 4*x\<^sup>2*y\<^sup>2"
      by (simp add: power2_eq_square power4_eq_xxxx algebra_simps)
    also have "\<dots> = x^4 + 2*x\<^sup>2*y\<^sup>2 + y^4" by simp
    also have "\<dots> = (x\<^sup>2 + y\<^sup>2)\<^sup>2"
      by (simp add: power2_eq_square power4_eq_xxxx algebra_simps)
    also have "\<dots> = 1" using hS1 by simp
    finally show "q p \<in> top1_S1" unfolding top1_S1_def q_def hxy by simp
  qed
  \<comment> \<open>q is surjective on S^1: for any (a,b) \<in> S^1, find (x,y) with q(x,y) = (a,b).\<close>
  have hq_surj: "q ` top1_S1 = top1_S1"
  proof (intro set_eqI iffI)
    fix w assume "w \<in> q ` top1_S1"
    then obtain p where hp: "p \<in> top1_S1" and hw: "w = q p" by (by100 blast)
    show "w \<in> top1_S1" using hq_S1[OF hp] hw by simp
  next
    fix w assume hw: "w \<in> top1_S1"
    obtain a b where hab: "w = (a, b)" by (cases w) auto
    have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" using hw unfolding top1_S1_def hab by simp
    \<comment> \<open>Use complex square root: z = Complex a b has |z|=1, so csqrt z has |csqrt z|=1.\<close>
    define z where "z = Complex a b"
    have hznorm: "cmod z = 1" unfolding z_def cmod_def using hS1w by simp
    define w' where "w' = csqrt z"
    have hw'norm: "cmod w' = 1" unfolding w'_def using hznorm by (simp add: norm_csqrt)
    have hw'sq: "w' * w' = z"
      using power2_csqrt[of z] unfolding w'_def power2_eq_square by simp
    define x where "x = Re w'"
    define y where "y = Im w'"
    have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1"
      using hw'norm unfolding x_def y_def cmod_def
      by (simp add: power2_eq_square real_sqrt_eq_1_iff)
    have "w' * w' = Complex (x\<^sup>2 - y\<^sup>2) (2*x*y)"
      unfolding x_def y_def
      by (intro complex_eqI) (simp_all add: power2_eq_square algebra_simps)
    hence "Complex (x\<^sup>2 - y\<^sup>2) (2*x*y) = z" using hw'sq by simp
    hence hqa: "x\<^sup>2 - y\<^sup>2 = a" and hqb: "2*x*y = b"
      unfolding z_def by (simp_all add: complex_eq_iff)
    have "(x, y) \<in> top1_S1" unfolding top1_S1_def using hxy_S1 by simp
    moreover have "q (x, y) = w" unfolding q_def hab using hqa hqb by simp
    ultimately show "w \<in> q ` top1_S1" by (by100 blast)
  qed
  \<comment> \<open>q is continuous (polynomial).\<close>
  have hq_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q"
  proof -
    \<comment> \<open>q is continuous as a map R^2 \<rightarrow> R^2 (polynomial), then restrict to S^1.\<close>
    have hcont_univ: "continuous_on UNIV (\<lambda>p::real\<times>real. (fst p ^ 2 - snd p ^ 2, 2 * fst p * snd p))"
      by (intro continuous_intros)
    have hcont_S1: "continuous_on top1_S1 (\<lambda>p. (fst p ^ 2 - snd p ^ 2, 2 * fst p * snd p))"
      using continuous_on_subset[OF hcont_univ] by (by100 blast)
    have hq_eq: "\<And>p. p \<in> top1_S1 \<Longrightarrow> q p = (fst p ^ 2 - snd p ^ 2, 2 * fst p * snd p)"
      unfolding q_def by simp
    \<comment> \<open>Bridge from continuous_on to top1_continuous_map_on via subspace topology.\<close>
    show ?thesis unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix p assume "p \<in> top1_S1" thus "q p \<in> top1_S1" by (rule hq_S1)
    next
      fix V assume hV: "V \<in> top1_S1_topology"
      obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
          and hVeq': "V = top1_S1 \<inter> W'"
        using hV unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      have hW'_open: "open W'" using hW'
        by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
      define W where "W = W'"
      have hW: "open W" and hVeq: "V = top1_S1 \<inter> W"
        using hW'_open hVeq' unfolding W_def by auto
      have "{p \<in> top1_S1. q p \<in> V} = {p \<in> top1_S1. q p \<in> W}"
        using hq_S1 hVeq by (by100 blast)
      also have "\<dots> = {p \<in> top1_S1. (fst p^2 - snd p^2, 2*fst p*snd p) \<in> W}"
        using hq_eq by (intro Collect_cong conj_cong refl) auto
      finally have hpre_eq: "{p \<in> top1_S1. q p \<in> V} =
          {p \<in> top1_S1. (fst p^2 - snd p^2, 2*fst p*snd p) \<in> W}" .
      obtain U where hU: "open U" and hfW: "U \<inter> top1_S1 =
          (\<lambda>p. (fst p^2 - snd p^2, 2*fst p*snd p)) -` W \<inter> top1_S1"
        using hcont_S1 hW unfolding continuous_on_open_invariant by blast
      have "{p \<in> top1_S1. (fst p^2 - snd p^2, 2*fst p*snd p) \<in> W} = U \<inter> top1_S1"
        using hfW by (by100 blast)
      hence "{p \<in> top1_S1. q p \<in> V} = U \<inter> top1_S1" using hpre_eq by simp
      moreover have "U \<inter> top1_S1 \<in> top1_S1_topology"
      proof -
        have "U \<in> (top1_open_sets :: (real \<times> real) set set)"
          using hU unfolding top1_open_sets_def by simp
        hence "U \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
          using product_topology_on_open_sets_real2 by (by100 metis)
        thus ?thesis unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      qed
      ultimately show "{p \<in> top1_S1. q p \<in> V} \<in> top1_S1_topology" by simp
    qed
  qed
  \<comment> \<open>Every point of S^1 has an evenly covered neighborhood.
     Use 4 open semicircles: U_top = {(a,b) \<in> S^1 | b > 0}, etc.\<close>
  \<comment> \<open>4 open semicircles covering S^1.\<close>
  define U_top where "U_top = {p \<in> top1_S1. snd p > 0}"
  define U_bot where "U_bot = {p \<in> top1_S1. snd p < 0}"
  define U_right where "U_right = {p \<in> top1_S1. fst p > 0}"
  define U_left where "U_left = {p \<in> top1_S1. fst p < 0}"
  \<comment> \<open>Every point of S^1 is in at least one semicircle.\<close>
  have hcover: "\<And>p. p \<in> top1_S1 \<Longrightarrow> p \<in> U_top \<or> p \<in> U_bot \<or> p \<in> U_right \<or> p \<in> U_left"
  proof -
    fix p assume hp: "p \<in> top1_S1"
    obtain a b where hab: "p = (a, b)" by (cases p) auto
    have hS1: "a\<^sup>2 + b\<^sup>2 = 1" using hp unfolding top1_S1_def hab by simp
    show "p \<in> U_top \<or> p \<in> U_bot \<or> p \<in> U_right \<or> p \<in> U_left"
    proof (cases "b > 0")
      case True thus ?thesis unfolding U_top_def using hp hab by simp
    next
      case False
      show ?thesis
      proof (cases "b < 0")
        case True thus ?thesis unfolding U_bot_def using hp hab by simp
      next
        case False
        hence "b = 0" using \<open>\<not> b > 0\<close> by simp
        hence "a\<^sup>2 = 1" using hS1 by simp
        hence "a = 1 \<or> a = -1" by (metis power2_eq_1_iff)
        thus ?thesis unfolding U_right_def U_left_def using hp hab by auto
      qed
    qed
  qed
  \<comment> \<open>Each semicircle is evenly covered. We prove this for U_top; the others are analogous.\<close>
  have hevenly_top: "top1_evenly_covered_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q U_top"
  proof -
    \<comment> \<open>U_top is open in S^1: intersection with open upper half-plane.\<close>
    have hU_top_open: "openin_on top1_S1 top1_S1_topology U_top"
    proof -
      have "open {p :: real \<times> real. snd p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      hence "{p :: real \<times> real. snd p > 0} \<in> top1_open_sets" unfolding top1_open_sets_def by simp
      hence "{p :: real \<times> real. snd p > 0} \<in> product_topology_on top1_open_sets top1_open_sets"
        using product_topology_on_open_sets_real2 by (by100 metis)
      hence "top1_S1 \<inter> {p. snd p > 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "U_top = top1_S1 \<inter> {p. snd p > 0}" unfolding U_top_def by (by100 blast)
      moreover have "U_top \<subseteq> top1_S1" unfolding U_top_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    \<comment> \<open>V1 = first quadrant, V2 = third quadrant of S^1.\<close>
    define V1 where "V1 = {p \<in> top1_S1. fst p > 0 \<and> snd p > 0}"
    define V2 where "V2 = {p \<in> top1_S1. fst p < 0 \<and> snd p < 0}"
    \<comment> \<open>V1, V2 are open in S^1, disjoint, and q^{-1}(U_top) = V1 \<union> V2.\<close>
    have hV1_open: "openin_on top1_S1 top1_S1_topology V1"
    proof -
      have h1: "open {p :: real \<times> real. fst p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have h2: "open {p :: real \<times> real. snd p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have "open {p :: real \<times> real. fst p > 0 \<and> snd p > 0}"
      proof -
        have "{p :: real \<times> real. fst p > 0 \<and> snd p > 0} = {p. fst p > 0} \<inter> {p. snd p > 0}" by auto
        thus ?thesis using open_Int[OF h1 h2] by simp
      qed
      hence "{p :: real \<times> real. fst p > 0 \<and> snd p > 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p > 0 \<and> snd p > 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p > 0 \<and> snd p > 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p > 0 \<and> snd p > 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "V1 = top1_S1 \<inter> {p. fst p > 0 \<and> snd p > 0}" unfolding V1_def by (by100 blast)
      moreover have "V1 \<subseteq> top1_S1" unfolding V1_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    have hV2_open: "openin_on top1_S1 top1_S1_topology V2"
    proof -
      have h1: "open {p :: real \<times> real. fst p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have h2: "open {p :: real \<times> real. snd p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have "open {p :: real \<times> real. fst p < 0 \<and> snd p < 0}"
      proof -
        have "{p :: real \<times> real. fst p < 0 \<and> snd p < 0} = {p. fst p < 0} \<inter> {p. snd p < 0}" by auto
        thus ?thesis using open_Int[OF h1 h2] by simp
      qed
      hence "{p :: real \<times> real. fst p < 0 \<and> snd p < 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p < 0 \<and> snd p < 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p < 0 \<and> snd p < 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p < 0 \<and> snd p < 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "V2 = top1_S1 \<inter> {p. fst p < 0 \<and> snd p < 0}" unfolding V2_def by (by100 blast)
      moreover have "V2 \<subseteq> top1_S1" unfolding V2_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    have hV_disj: "V1 \<inter> V2 = {}" unfolding V1_def V2_def by auto
    have hpreimage: "{p \<in> top1_S1. q p \<in> U_top} = V1 \<union> V2"
    proof (intro set_eqI iffI)
      fix p assume hp: "p \<in> {p \<in> top1_S1. q p \<in> U_top}"
      hence hpS1: "p \<in> top1_S1" and hqp: "q p \<in> U_top" by auto
      obtain x y where hxy: "p = (x, y)" by (cases p) auto
      have hS1: "x\<^sup>2 + y\<^sup>2 = 1" using hpS1 unfolding top1_S1_def hxy by simp
      have "snd (q p) > 0" using hqp unfolding U_top_def by (by100 blast)
      hence "2*x*y > 0" unfolding q_def hxy by simp
      hence "x*y > 0" by simp
      hence "(x > 0 \<and> y > 0) \<or> (x < 0 \<and> y < 0)" using zero_less_mult_iff by force
      thus "p \<in> V1 \<union> V2" unfolding V1_def V2_def using hpS1 hxy by auto
    next
      fix p assume "p \<in> V1 \<union> V2"
      hence hpS1: "p \<in> top1_S1" and hq: "fst p * snd p > 0"
        unfolding V1_def V2_def by (auto intro: mult_pos_pos mult_neg_neg)
      have "snd (q p) = 2 * fst p * snd p" unfolding q_def by simp
      hence "snd (q p) > 0" using hq by simp
      moreover have "q p \<in> top1_S1" by (rule hq_S1[OF hpS1])
      ultimately show "p \<in> {p \<in> top1_S1. q p \<in> U_top}" unfolding U_top_def using hpS1 by auto
    qed
    \<comment> \<open>q is a homeomorphism from V1 to U_top and from V2 to U_top.\<close>
    \<comment> \<open>q is a homeomorphism V1 \<rightarrow> U_top. Inverse: (a,b) \<mapsto> (sqrt((1+a)/2), sqrt((1-a)/2)).\<close>
    have hhomeo1: "top1_homeomorphism_on V1 (subspace_topology top1_S1 top1_S1_topology V1)
        U_top (subspace_topology top1_S1 top1_S1_topology U_top) q"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      have hTS1: "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      show "is_topology_on V1 (subspace_topology top1_S1 top1_S1_topology V1)"
        by (rule subspace_topology_is_topology_on[OF hTS1]) (use V1_def in blast)
      show "is_topology_on U_top (subspace_topology top1_S1 top1_S1_topology U_top)"
        by (rule subspace_topology_is_topology_on[OF hTS1]) (use U_top_def in blast)
      show "bij_betw q V1 U_top"
      proof (rule bij_betw_imageI)
        \<comment> \<open>Injectivity of q on V1.\<close>
        show "inj_on q V1"
        proof (rule inj_onI)
          fix p1 p2 assume hp1: "p1 \<in> V1" and hp2: "p2 \<in> V1" and heq: "q p1 = q p2"
          obtain x1 y1 where h1: "p1 = (x1, y1)" by (cases p1) auto
          obtain x2 y2 where h2: "p2 = (x2, y2)" by (cases p2) auto
          have hx1: "x1 > 0" "y1 > 0" "x1\<^sup>2 + y1\<^sup>2 = 1"
            using hp1 unfolding V1_def top1_S1_def h1 by auto
          have hx2: "x2 > 0" "y2 > 0" "x2\<^sup>2 + y2\<^sup>2 = 1"
            using hp2 unfolding V1_def top1_S1_def h2 by auto
          have "x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2"
            using heq unfolding q_def h1 h2 by auto
          have "x1\<^sup>2 = (1 + (x1\<^sup>2 - y1\<^sup>2))/2" using hx1(3) by (simp add: field_simps)
          also have "\<dots> = (1 + (x2\<^sup>2 - y2\<^sup>2))/2" using \<open>x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2\<close> by simp
          also have "\<dots> = x2\<^sup>2" using hx2(3) by (simp add: field_simps)
          finally have "x1\<^sup>2 = x2\<^sup>2" .
          hence "x1 = x2" using hx1(1) hx2(1) by (simp add: power2_eq_iff_nonneg)
          moreover have "y1\<^sup>2 = y2\<^sup>2" using \<open>x1\<^sup>2 = x2\<^sup>2\<close> hx1(3) hx2(3) by linarith
          hence "y1 = y2" using hx1(2) hx2(2) by (simp add: power2_eq_iff_nonneg)
          ultimately show "p1 = p2" unfolding h1 h2 by simp
        qed
      next
        \<comment> \<open>q maps V1 onto U_top.\<close>
        show "q ` V1 = U_top"
        proof (intro set_eqI iffI)
          fix w assume "w \<in> q ` V1"
          then obtain p where hp: "p \<in> V1" and hw: "w = q p" by (by100 blast)
          have "p \<in> top1_S1" "fst p > 0" "snd p > 0" using hp unfolding V1_def by auto
          have "q p \<in> top1_S1" by (rule hq_S1[OF \<open>p \<in> top1_S1\<close>])
          moreover have "snd (q p) = 2 * fst p * snd p" unfolding q_def by simp
          hence "snd (q p) > 0" using \<open>fst p > 0\<close> \<open>snd p > 0\<close> by simp
          ultimately show "w \<in> U_top" unfolding U_top_def using hw by simp
        next
          fix w assume hw: "w \<in> U_top"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and hb: "b > 0"
            using hw unfolding U_top_def top1_S1_def hab by auto
          define x where "x = sqrt ((1+a)/2)"
          define y where "y = sqrt ((1-a)/2)"
          have "b\<^sup>2 > 0" using hb by (simp add: power2_eq_square zero_less_mult_iff)
          hence "a\<^sup>2 < 1" using hS1w by linarith
          hence "a < 1 \<and> -1 < a"
          proof -
            have "\<not> (a \<ge> 1)"
            proof
              assume "1 \<le> a"
              hence "1 \<le> a * a" using mult_mono[of 1 a 1 a] by simp
              thus False using \<open>a\<^sup>2 < 1\<close> by (simp add: power2_eq_square)
            qed
            moreover have "\<not> (a \<le> -1)"
            proof
              assume "a \<le> -1"
              hence "(-a) \<ge> 1" by linarith
              hence "1 \<le> (-a) * (-a)" using mult_mono[of 1 "-a" 1 "-a"] by simp
              hence "1 \<le> a * a" by simp
              thus False using \<open>a\<^sup>2 < 1\<close> by (simp add: power2_eq_square)
            qed
            ultimately show ?thesis by linarith
          qed
          hence ha_lt: "a < 1" and ha_gt: "-1 < a" by linarith+
          have ha_le: "a \<le> 1" and ha_ge: "-1 \<le> a" using ha_lt ha_gt by linarith+
          have hx_pos: "x > 0" unfolding x_def using ha_gt by simp
          have hy_nonneg: "y \<ge> 0" unfolding y_def using ha_le by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square
            using ha_ge by (simp add: real_sqrt_mult_self)
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square
            using ha_le by (simp add: real_sqrt_mult_self)
          have hqa: "x\<^sup>2 - y\<^sup>2 = a" using hx2 hy2 by simp
          have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2"
            using hx2 hy2 hS1w sorry \<comment> \<open>Arithmetic: (2xy)^2 = 4*x^2*y^2 = (1+a)(1-a) = 1-a^2 = b^2.\<close>
          have hxy_nonneg: "2*x*y \<ge> 0" using hx_pos hy_nonneg by simp
          have hqb: "2*x*y = b" using h2xy_eq_b2 hxy_nonneg hb by (simp add: power2_eq_iff_nonneg)
          have hy_pos: "y > 0"
          proof -
            have "2*x*y > 0" using hqb hb by simp
            hence "x*y > 0" by simp
            thus "y > 0" using hx_pos by (simp add: zero_less_mult_iff)
          qed
          have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx2 hy2 by simp
          have "(x, y) \<in> V1" unfolding V1_def top1_S1_def using hxy_S1 hx_pos hy_pos by simp
          moreover have "q (x, y) = w" unfolding q_def hab using hqa hqb by simp
          ultimately show "w \<in> q ` V1" by (by100 blast)
        qed
      qed
      show "top1_continuous_map_on V1 (subspace_topology top1_S1 top1_S1_topology V1)
          U_top (subspace_topology top1_S1 top1_S1_topology U_top) q"
        sorry
      show "top1_continuous_map_on U_top (subspace_topology top1_S1 top1_S1_topology U_top)
          V1 (subspace_topology top1_S1 top1_S1_topology V1) (inv_into V1 q)"
        sorry
    qed
    \<comment> \<open>q is a homeomorphism V2 \<rightarrow> U_top. Inverse: (a,b) \<mapsto> (-sqrt((1+a)/2), -sqrt((1-a)/2)).\<close>
    have hhomeo2: "top1_homeomorphism_on V2 (subspace_topology top1_S1 top1_S1_topology V2)
        U_top (subspace_topology top1_S1 top1_S1_topology U_top) q"
      sorry
    show ?thesis unfolding top1_evenly_covered_on_def
    proof (intro conjI exI[of _ "{V1, V2}"])
      show "openin_on top1_S1 top1_S1_topology U_top" by (rule hU_top_open)
      show "\<forall>V\<in>{V1, V2}. openin_on top1_S1 top1_S1_topology V"
        using hV1_open hV2_open by (by100 blast)
      show "\<forall>V\<in>{V1, V2}. \<forall>V'\<in>{V1, V2}. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
        using hV_disj by (by100 blast)
      show "{x \<in> top1_S1. q x \<in> U_top} = \<Union> {V1, V2}" using hpreimage by simp
      show "\<forall>V\<in>{V1, V2}. top1_homeomorphism_on V (subspace_topology top1_S1 top1_S1_topology V)
          U_top (subspace_topology top1_S1 top1_S1_topology U_top) q"
        using hhomeo1 hhomeo2 by (by100 blast)
    qed
  qed
  have hevenly_bot: "top1_evenly_covered_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q U_bot"
    sorry
  have hevenly_right: "top1_evenly_covered_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q U_right"
    sorry
  have hevenly_left: "top1_evenly_covered_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q U_left"
    sorry
  have hq_evenly: "\<And>b. b \<in> top1_S1 \<Longrightarrow>
      \<exists>U. b \<in> U \<and> top1_evenly_covered_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q U"
  proof -
    fix b assume hb: "b \<in> top1_S1"
    from hcover[OF hb] show "\<exists>U. b \<in> U \<and> top1_evenly_covered_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q U"
      using hevenly_top hevenly_bot hevenly_right hevenly_left by (by100 blast)
  qed
  show ?thesis unfolding hq_alt[symmetric] top1_covering_map_on_def
    using hq_cont hq_surj hq_evenly by (by100 blast)
qed

text \<open>Step 1 helper: h(-z) = -h(z) and q(z)=z^2 implies q\<circ>h factors through q.
  Since q is a quotient map (covering \<Rightarrow> quotient) and q(h(-z)) = q(h(z)),
  there exists continuous k with k\<circ>q = q\<circ>h.\<close>

lemma squaring_map_factorization:
  assumes "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h"
      and "top1_antipode_preserving_S1 h"
  obtains k where "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology k"
      and "\<forall>z\<in>top1_S1. k ((\<lambda>(x,y). (x^2-y^2, 2*x*y)) z) = (\<lambda>(x,y). (x^2-y^2, 2*x*y)) (h z)"
  sorry

(** from *\<S>57 Theorem 57.1: antipode-preserving S^1 \<rightarrow> S^1 is NOT nulhomotopic.

    Munkres' proof:
    Step 1: WLOG h(b_0) = b_0 (rotate). Let q: S^1 \<rightarrow> S^1 be q(z) = z^2 (quotient
            map). q is a covering map and its fibers are antipodal pairs {z, -z}.
            Since h(-z) = -h(z), we have q(h(-z)) = q(h(z)), so q\<circ>h factors as
            k\<circ>q for some continuous k: S^1 \<rightarrow> S^1.
    Step 2: k_* is nontrivial. If \<tilde>f is any path in S^1 from b_0 to -b_0, the
            loop f = q\<circ>\<tilde>f represents a nontrivial element of \<pi>_1(S^1). For \<tilde>f is
            a lifting of f, starting at b_0 but not ending at b_0.
            Hence k_*[f] = [k\<circ>(q\<circ>\<tilde>f)] = [q\<circ>(h\<circ>\<tilde>f)] is also nontrivial.
    Step 3: k_* injective; q_* injective (multiplication by 2 in Z). So k_*\<circ>q_*
            is injective. Since q_*\<circ>h_* = k_*\<circ>q_*, h_* is injective, hence
            nontrivial, hence h is not nulhomotopic. **)
theorem Theorem_57_1:
  assumes "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h"
      and "top1_antipode_preserving_S1 h"
  shows "\<not> top1_nulhomotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h"
proof
  assume hnul: "top1_nulhomotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h"
  \<comment> \<open>Step 1: q(z)=z^2 is a covering map. h(-z)=-h(z) \<Rightarrow> q\<circ>h = k\<circ>q for some k.\<close>
  let ?q = "\<lambda>(x, y). (x^2 - y^2, 2*x*y)"
  have hq_cover: "top1_covering_map_on top1_S1 top1_S1_topology
      top1_S1 top1_S1_topology ?q" by (rule squaring_map_covering)
  obtain k where hk_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
      top1_S1 top1_S1_topology k"
      and hk_eq: "\<forall>z\<in>top1_S1. k (?q z) = ?q (h z)"
    by (rule squaring_map_factorization[OF assms])
  \<comment> \<open>Step 2: k_* is nontrivial. A path from b0 to -b0 in S^1 lifts to a nontrivial loop under q,
     and k maps this to another nontrivial element.\<close>
  have hk_nontrivial: "\<not> (\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
      \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
            (k \<circ> f) (top1_constant_path (1, 0)))" sorry
  \<comment> \<open>Step 3: q_* is multiplication by 2, hence injective. k_*\<circ>q_* injective.
     q_*\<circ>h_* = k_*\<circ>q_* \<Rightarrow> h_* injective \<Rightarrow> nontrivial \<Rightarrow> h not nulhomotopic.\<close>
  have hq_star_inj: "\<forall>f g. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
      \<and> top1_is_loop_on top1_S1 top1_S1_topology (1, 0) g
      \<and> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
           (?q \<circ> f) (?q \<circ> g)
      \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) f g"
  proof (intro allI impI, elim conjE)
    fix f g
    assume hf: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f"
    assume hg: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) g"
    assume hqfg: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) (?q \<circ> f) (?q \<circ> g)"
    \<comment> \<open>Bridge: \<psi>(z) = (Re z, Im z), \<psi>^{-1}(a,b) = Complex a b.\<close>
    let ?\<psi> = "\<lambda>z::complex. (Re z, Im z)"
    let ?\<psi>inv = "\<lambda>p::real\<times>real. Complex (fst p) (snd p)"
    \<comment> \<open>Key identity: q(a,b) = \<psi>((Complex a b)^2) for (a,b) \<in> S^1.\<close>
    have hq_psi: "\<And>p. p \<in> top1_S1 \<Longrightarrow> ?q p = ?\<psi> ((?\<psi>inv p)^2)"
    proof -
      fix p assume hp: "p \<in> top1_S1"
      obtain a b where hab: "p = (a, b)" by (cases p) auto
      have "(?\<psi>inv p)^2 = (Complex a b)^2" using hab by simp
      also have "\<dots> = Complex (a^2 - b^2) (2*a*b)"
        by (rule complex_eqI) (simp_all add: power2_eq_square algebra_simps)
      finally have "(?\<psi>inv p)^2 = Complex (a^2 - b^2) (2*a*b)" .
      hence "?\<psi> ((?\<psi>inv p)^2) = (a^2 - b^2, 2*a*b)" by simp
      also have "\<dots> = ?q p" using hab by (simp add: power2_eq_square)
      finally show "?q p = ?\<psi> ((?\<psi>inv p)^2)" by simp
    qed
    \<comment> \<open>Define f' = \<psi>^{-1} \<circ> f, g' = \<psi>^{-1} \<circ> g: loops on S^1_complex at 1.\<close>
    let ?f' = "?\<psi>inv \<circ> f"
    let ?g' = "?\<psi>inv \<circ> g"
    have hTR_: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hTS1: "is_topology_on top1_S1 top1_S1_topology"
    proof -
      have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
        using product_topology_on_is_topology_on[OF hTR_ hTR_] by simp
      thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
    qed
    have hTS1c: "is_topology_on top1_S1_complex top1_S1_complex_topology"
      unfolding top1_S1_complex_topology_def
      by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV]) simp
    have h\<psi>inv_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
        top1_S1_complex top1_S1_complex_topology ?\<psi>inv"
    proof -
      have h\<psi>inv_map: "\<And>p. p \<in> top1_S1 \<Longrightarrow> ?\<psi>inv p \<in> top1_S1_complex"
        unfolding top1_S1_def top1_S1_complex_def by (auto simp: cmod_def)
      have hcont_univ: "continuous_on UNIV (\<lambda>p::real\<times>real. Complex (fst p) (snd p))"
        by (intro continuous_intros)
      show ?thesis unfolding top1_continuous_map_on_def product_topology_on_open_sets
      proof (intro conjI ballI)
        fix p assume "p \<in> top1_S1" thus "?\<psi>inv p \<in> top1_S1_complex" by (rule h\<psi>inv_map)
      next
        fix V assume hV: "V \<in> top1_S1_complex_topology"
        then obtain W where hWo: "W \<in> (top1_open_sets :: complex set set)"
            and hVeq: "V = top1_S1_complex \<inter> W"
          unfolding top1_S1_complex_topology_def subspace_topology_def by (by100 auto)
        have hWopen: "open W" using hWo unfolding top1_open_sets_def by (by100 simp)
        have hpre_open: "open ((\<lambda>p::real\<times>real. Complex (fst p) (snd p)) -` W)"
        proof -
          have "open ((\<lambda>p::real\<times>real. Complex (fst p) (snd p)) -` W \<inter> UNIV)"
            using iffD1[OF continuous_on_open_vimage[OF open_UNIV] hcont_univ] hWopen
            by (by100 blast)
          thus ?thesis by simp
        qed
        have "{p \<in> top1_S1. ?\<psi>inv p \<in> V} =
            top1_S1 \<inter> ((\<lambda>p. Complex (fst p) (snd p)) -` W)"
          unfolding hVeq using h\<psi>inv_map by (by100 auto)
        thus "{p \<in> top1_S1. ?\<psi>inv p \<in> V} \<in> top1_S1_topology"
          unfolding top1_S1_topology_def subspace_topology_def
          using hpre_open product_topology_on_open_sets_real2
          unfolding top1_open_sets_def by (by100 blast)
      qed
    qed
    have h\<psi>_cont: "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
        top1_S1 top1_S1_topology ?\<psi>"
      by (rule psi_continuous_S1)
    have h\<psi>inv_1: "?\<psi>inv (1::real, 0::real) = (1::complex)"
      by (rule complex_eqI) simp_all
    have h\<psi>_1: "?\<psi> (1::complex) = (1::real, 0::real)" by simp
    \<comment> \<open>f' and g' are loops on S^1_complex at 1.\<close>
    have hf'_loop: "top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 ?f'"
      using top1_continuous_map_loop_early[OF h\<psi>inv_cont hf] h\<psi>inv_1 by simp
    have hg'_loop: "top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 ?g'"
      using top1_continuous_map_loop_early[OF h\<psi>inv_cont hg] h\<psi>inv_1 by simp
    \<comment> \<open>q \<circ> f = \<psi> \<circ> (\<lambda>s. (f' s)^2) on I_set.\<close>
    have hqf_eq: "\<forall>s\<in>I_set. (?q \<circ> f) s = (?\<psi> \<circ> (\<lambda>s. (?f' s)^2)) s"
    proof
      fix s assume hs: "s \<in> I_set"
      have hfs: "f s \<in> top1_S1"
        using hf unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def
        using hs by (by100 blast)
      show "(?q \<circ> f) s = (?\<psi> \<circ> (\<lambda>s. (?f' s)^2)) s"
        using hq_psi[OF hfs] by (simp add: comp_def)
    qed
    have hqg_eq: "\<forall>s\<in>I_set. (?q \<circ> g) s = (?\<psi> \<circ> (\<lambda>s. (?g' s)^2)) s"
    proof
      fix s assume hs: "s \<in> I_set"
      have hgs: "g s \<in> top1_S1"
        using hg unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def
        using hs by (by100 blast)
      show "(?q \<circ> g) s = (?\<psi> \<circ> (\<lambda>s. (?g' s)^2)) s"
        using hq_psi[OF hgs] by (simp add: comp_def)
    qed
    \<comment> \<open>Transfer: q\<circ>f ~ q\<circ>g \<Longrightarrow> \<psi>\<circ>(f')^2 ~ \<psi>\<circ>(g')^2 on S^1.\<close>
    \<comment> \<open>Transfer homotopy: q\<circ>f ~ q\<circ>g, but q\<circ>f = \<psi>\<circ>(f')^2 on I_set. Extract H and rebuild.\<close>
    have h\<psi>f2g2: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
        (?\<psi> \<circ> (\<lambda>s. (?f' s)^2)) (?\<psi> \<circ> (\<lambda>s. (?g' s)^2))"
    proof -
      \<comment> \<open>Extract the homotopy H from hqfg. Replace boundary values using hqf_eq, hqg_eq.\<close>
      obtain H where hH_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology top1_S1 top1_S1_topology H"
          and hH0: "\<forall>s\<in>I_set. H (s, 0) = (?q \<circ> f) s"
          and hH1: "\<forall>s\<in>I_set. H (s, 1) = (?q \<circ> g) s"
          and hH_left: "\<forall>t\<in>I_set. H (0, t) = (1, 0)"
          and hH_right: "\<forall>t\<in>I_set. H (1, t) = (1, 0)"
        using hqfg unfolding top1_path_homotopic_on_def by auto
      have hqf_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) (?q \<circ> f)"
        using hqfg unfolding top1_path_homotopic_on_def by (by100 blast)
      have hqg_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) (?q \<circ> g)"
        using hqfg unfolding top1_path_homotopic_on_def by (by100 blast)
      have h\<psi>f2_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) (?\<psi> \<circ> (\<lambda>s. (?f' s)^2))"
      proof -
        \<comment> \<open>Agrees with q\<circ>f on I_set. Use q\<circ>f path properties with value substitution.\<close>
        have hcont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology (?\<psi> \<circ> (\<lambda>s. (?f' s)^2))"
        proof -
          have hqf_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology (?q \<circ> f)"
            using hqf_path unfolding top1_is_path_on_def by (by100 blast)
          show ?thesis unfolding top1_continuous_map_on_def
          proof (intro conjI ballI)
            fix s assume hs: "s \<in> I_set"
            have "(?q \<circ> f) s \<in> top1_S1"
              using hqf_cont hs unfolding top1_continuous_map_on_def by (by100 blast)
            thus "(?\<psi> \<circ> (\<lambda>s. (?f' s)^2)) s \<in> top1_S1" using hqf_eq hs by simp
          next
            fix V assume hV: "V \<in> top1_S1_topology"
            have "\<And>s. s \<in> I_set \<Longrightarrow> ((?\<psi> \<circ> (\<lambda>s. (?f' s)^2)) s \<in> V) = ((?q \<circ> f) s \<in> V)"
              using hqf_eq by simp
            hence "{s \<in> I_set. (?\<psi> \<circ> (\<lambda>s. (?f' s)^2)) s \<in> V} = {s \<in> I_set. (?q \<circ> f) s \<in> V}"
              by (by100 auto)
            also have "\<dots> \<in> I_top" using hqf_cont hV unfolding top1_continuous_map_on_def
              by (by100 blast)
            finally show "{s \<in> I_set. (?\<psi> \<circ> (\<lambda>s. (?f' s)^2)) s \<in> V} \<in> I_top" .
          qed
        qed
        have "(?q \<circ> f) 0 = (1, 0)"
          using hqf_path unfolding top1_is_path_on_def by (by100 blast)
        hence h0: "(?\<psi> \<circ> (\<lambda>s. (?f' s)^2)) 0 = (1, 0)"
          using hqf_eq unfolding top1_unit_interval_def by auto
        have "(?q \<circ> f) 1 = (1, 0)"
          using hqf_path unfolding top1_is_path_on_def by (by100 blast)
        hence h1: "(?\<psi> \<circ> (\<lambda>s. (?f' s)^2)) 1 = (1, 0)"
          using hqf_eq unfolding top1_unit_interval_def by auto
        show ?thesis unfolding top1_is_path_on_def using hcont h0 h1 by (by100 blast)
      qed
      have h\<psi>g2_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) (?\<psi> \<circ> (\<lambda>s. (?g' s)^2))"
      proof -
        have hcont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology (?\<psi> \<circ> (\<lambda>s. (?g' s)^2))"
        proof -
          have hqg_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology (?q \<circ> g)"
            using hqg_path unfolding top1_is_path_on_def by (by100 blast)
          show ?thesis unfolding top1_continuous_map_on_def
          proof (intro conjI ballI)
            fix s assume hs: "s \<in> I_set"
            have "(?q \<circ> g) s \<in> top1_S1"
              using hqg_cont hs unfolding top1_continuous_map_on_def by (by100 blast)
            thus "(?\<psi> \<circ> (\<lambda>s. (?g' s)^2)) s \<in> top1_S1" using hqg_eq hs by simp
          next
            fix V assume hV: "V \<in> top1_S1_topology"
            have "\<And>s. s \<in> I_set \<Longrightarrow> ((?\<psi> \<circ> (\<lambda>s. (?g' s)^2)) s \<in> V) = ((?q \<circ> g) s \<in> V)"
              using hqg_eq by simp
            hence "{s \<in> I_set. (?\<psi> \<circ> (\<lambda>s. (?g' s)^2)) s \<in> V} = {s \<in> I_set. (?q \<circ> g) s \<in> V}"
              by (by100 auto)
            also have "\<dots> \<in> I_top" using hqg_cont hV unfolding top1_continuous_map_on_def
              by (by100 blast)
            finally show "{s \<in> I_set. (?\<psi> \<circ> (\<lambda>s. (?g' s)^2)) s \<in> V} \<in> I_top" .
          qed
        qed
        have "(?q \<circ> g) 0 = (1, 0)"
          using hqg_path unfolding top1_is_path_on_def by (by100 blast)
        hence h0: "(?\<psi> \<circ> (\<lambda>s. (?g' s)^2)) 0 = (1, 0)"
          using hqg_eq unfolding top1_unit_interval_def by auto
        have "(?q \<circ> g) 1 = (1, 0)"
          using hqg_path unfolding top1_is_path_on_def by (by100 blast)
        hence h1: "(?\<psi> \<circ> (\<lambda>s. (?g' s)^2)) 1 = (1, 0)"
          using hqg_eq unfolding top1_unit_interval_def by auto
        show ?thesis unfolding top1_is_path_on_def using hcont h0 h1 by (by100 blast)
      qed
      have "\<forall>s\<in>I_set. H (s, 0) = (?\<psi> \<circ> (\<lambda>s. (?f' s)^2)) s"
        using hH0 hqf_eq by simp
      moreover have "\<forall>s\<in>I_set. H (s, 1) = (?\<psi> \<circ> (\<lambda>s. (?g' s)^2)) s"
        using hH1 hqg_eq by simp
      ultimately show ?thesis unfolding top1_path_homotopic_on_def
        using h\<psi>f2_path h\<psi>g2_path hH_cont hH_left hH_right
        by (intro conjI exI[of _ H]) auto
    qed
    \<comment> \<open>Apply \<psi>^{-1}: (f')^2 ~ (g')^2 on S^1_complex.\<close>
    have hf2g2: "top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1
        (\<lambda>s. (?f' s)^2) (\<lambda>s. (?g' s)^2)"
    proof -
      have h\<psi>inv_\<psi>: "\<And>z::complex. ?\<psi>inv (?\<psi> z) = z"
        by (rule complex_eqI) simp_all
      have hstep: "top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology
          (?\<psi>inv (1, 0)) (?\<psi>inv (1, 0))
          (?\<psi>inv \<circ> (?\<psi> \<circ> (\<lambda>s. (?f' s)^2))) (?\<psi>inv \<circ> (?\<psi> \<circ> (\<lambda>s. (?g' s)^2)))"
        by (rule continuous_preserves_path_homotopic[OF hTS1 hTS1c h\<psi>inv_cont h\<psi>f2g2])
      have h1: "?\<psi>inv (1, 0) = (1::complex)" by (rule complex_eqI) simp_all
      have heqf: "?\<psi>inv \<circ> (?\<psi> \<circ> (\<lambda>s. (?f' s)^2)) = (\<lambda>s. (?f' s)^2)"
        by (rule ext) (simp add: h\<psi>inv_\<psi>)
      have heqg: "?\<psi>inv \<circ> (?\<psi> \<circ> (\<lambda>s. (?g' s)^2)) = (\<lambda>s. (?g' s)^2)"
        by (rule ext) (simp add: h\<psi>inv_\<psi>)
      show ?thesis using hstep h1 heqf heqg by simp
    qed
    \<comment> \<open>By Theorem_56_1_step_1_inj[of 2]: f' ~ g' on S^1_complex.\<close>
    have hf'g': "top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1 ?f' ?g'"
    proof -
      have "\<forall>f g. top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 f
                \<and> top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 g
                \<and> top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1
                     (\<lambda>s. (f s)^2) (\<lambda>s. (g s)^2)
                \<longrightarrow> top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1 f g"
        by (rule Theorem_56_1_step_1_inj[of 2]) simp
      thus ?thesis using hf'_loop hg'_loop hf2g2 by (by100 blast)
    qed
    \<comment> \<open>Apply \<psi>: \<psi> \<circ> f' ~ \<psi> \<circ> g' on S^1. Since \<psi> \<circ> \<psi>^{-1} = id, this gives f ~ g.\<close>
    have h\<psi>f'g': "top1_path_homotopic_on top1_S1 top1_S1_topology
        (?\<psi> 1) (?\<psi> 1) (?\<psi> \<circ> ?f') (?\<psi> \<circ> ?g')"
      by (rule continuous_preserves_path_homotopic[OF hTS1c hTS1 h\<psi>_cont hf'g'])
    have h\<psi>\<psi>inv: "\<And>p::real\<times>real. ?\<psi> (?\<psi>inv p) = p"
      by (rule prod_eqI) simp_all
    have h\<psi>\<psi>inv_f: "?\<psi> \<circ> (?\<psi>inv \<circ> f) = f"
      by (rule ext) (simp add: h\<psi>\<psi>inv)
    have h\<psi>\<psi>inv_g: "?\<psi> \<circ> (?\<psi>inv \<circ> g) = g"
      by (rule ext) (simp add: h\<psi>\<psi>inv)
    show "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) f g"
      using h\<psi>f'g' h\<psi>\<psi>inv_f h\<psi>\<psi>inv_g h\<psi>_1 by simp
  qed
  \<comment> \<open>WLOG: reduce to h(1,0) = (1,0) by rotation. Munkres: let \<rho> rotate h(b0) to b0.\<close>
  \<comment> \<open>Case 1: h(1,0) = (1,0). Then h_* at (1,0) is nontrivial (from covering theory),
     but nulhomotopic \<Rightarrow> h_* trivial. Contradiction.\<close>
  \<comment> \<open>Case 2: h(1,0) \<noteq> (1,0). Rotate to reduce to Case 1.\<close>
  \<comment> \<open>Derive contradiction via case split on h(1,0) = (1,0).\<close>
  have hh_star_nontrivial: "\<not> (\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
      \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
            (h \<circ> f) (top1_constant_path (1, 0)))" sorry
  \<comment> \<open>Helper: for any loop f at (1,0), h\<circ>f \<simeq> const_{h(1,0)} at h(1,0).
     This is proved via homotopy_induced_basepoint_change + path algebra.\<close>
  have hh_trivial_at_h10: "\<And>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f \<Longrightarrow>
      top1_path_homotopic_on top1_S1 top1_S1_topology (h (1, 0)) (h (1, 0))
          (h \<circ> f) (top1_constant_path (h (1, 0)))"
  proof -
    fix f assume hf: "top1_is_loop_on top1_S1 top1_S1_topology (1::real, 0::real) f"
    obtain c where hcS1: "c \<in> top1_S1"
        and hhom: "top1_homotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h (\<lambda>_. c)"
      using hnul unfolding top1_nulhomotopic_on_def by (by100 blast)
    obtain H where hHcont: "top1_continuous_map_on (top1_S1 \<times> I_set)
            (product_topology_on top1_S1_topology I_top) top1_S1 top1_S1_topology H"
        and hH0: "\<forall>x\<in>top1_S1. H (x, 0) = h x"
        and hH1: "\<forall>x\<in>top1_S1. H (x, 1) = c"
      using hhom unfolding top1_homotopic_on_def by (by100 blast)
    have hTS1: "is_topology_on top1_S1 top1_S1_topology"
      unfolding top1_S1_topology_def
      by (rule subspace_topology_is_topology_on[OF
            product_topology_on_is_topology_on[OF
              top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
              simplified]]) simp
    have h10S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
    have hH1': "\<forall>x\<in>top1_S1. H (x, 1) = (\<lambda>_. c) x" using hH1 by (by100 simp)
    note hbc = homotopy_induced_basepoint_change[OF hTS1 hTS1 hHcont hH0 hH1' hf h10S1]
    have hbc': "top1_loop_equiv_on top1_S1 top1_S1_topology (h (1, 0)) (h \<circ> f)
        (top1_basepoint_change_on top1_S1 top1_S1_topology c (h (1, 0))
           (top1_path_reverse (\<lambda>t. H ((1, 0), t))) (top1_constant_path c))"
    proof -
      have "(\<lambda>_. c) \<circ> f = top1_constant_path c"
        by (rule ext) (simp add: top1_constant_path_def comp_def)
      thus ?thesis using hbc by simp
    qed
    have hbc_is_const: "top1_loop_equiv_on top1_S1 top1_S1_topology (h (1, 0))
        (top1_basepoint_change_on top1_S1 top1_S1_topology c (h (1, 0))
           (top1_path_reverse (\<lambda>t. H ((1, 0), t))) (top1_constant_path c))
        (top1_constant_path (h (1, 0)))"
    proof -
      let ?\<alpha> = "\<lambda>t. H ((1::real, 0::real), t)"
      have h\<alpha>_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology ?\<alpha>"
      proof -
        have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
        have hp1: "pi1 \<circ> (\<lambda>t. ((1::real,0::real),t)) = (\<lambda>_. (1::real,0::real))"
          unfolding pi1_def by (rule ext) simp
        have hp2: "pi2 \<circ> (\<lambda>t. ((1::real,0::real),t)) = id"
          unfolding pi2_def by (rule ext) simp
        have hpair: "top1_continuous_map_on I_set I_top (top1_S1 \<times> I_set)
                       (product_topology_on top1_S1_topology I_top) (\<lambda>t. ((1::real, 0::real), t))"
          using iffD2[OF Theorem_18_4[OF hTI hTS1 hTI]]
                top1_continuous_map_on_const[OF hTI hTS1 h10S1, folded hp1]
                top1_continuous_map_on_id[OF hTI, folded hp2]
          by (by100 blast)
        show ?thesis using top1_continuous_map_on_comp[OF hpair hHcont] by (simp add: comp_def)
      qed
      have h\<alpha>_path: "top1_is_path_on top1_S1 top1_S1_topology (h (1, 0)) c ?\<alpha>"
        unfolding top1_is_path_on_def using h\<alpha>_cont
        by (auto simp: hH0[rule_format, OF h10S1] hH1[rule_format, OF h10S1])
      have hra: "top1_is_path_on top1_S1 top1_S1_topology c (h (1, 0)) (top1_path_reverse ?\<alpha>)"
        by (rule top1_path_reverse_is_path[OF h\<alpha>_path])
      have hconst_c: "top1_is_loop_on top1_S1 top1_S1_topology c (top1_constant_path c)"
        by (rule top1_constant_path_is_loop[OF hTS1 hcS1])
      have hbc_def: "top1_basepoint_change_on top1_S1 top1_S1_topology c (h (1, 0))
          (top1_path_reverse ?\<alpha>) (top1_constant_path c)
        = top1_path_product ?\<alpha> (top1_path_product (top1_constant_path c) (top1_path_reverse ?\<alpha>))"
        unfolding top1_basepoint_change_on_def top1_path_reverse_twice by (rule refl)
      have hchain: "top1_path_homotopic_on top1_S1 top1_S1_topology (h (1, 0)) (h (1, 0))
          (top1_basepoint_change_on top1_S1 top1_S1_topology c (h (1, 0))
             (top1_path_reverse ?\<alpha>) (top1_constant_path c))
          (top1_constant_path (h (1, 0)))"
        using Lemma_51_1_path_homotopic_trans[OF hTS1
            path_homotopic_product_right[OF hTS1 Theorem_51_2_left_identity[OF hTS1 hra] h\<alpha>_path,
              unfolded hbc_def[symmetric]]
            Theorem_51_2_invgerse_left[OF hTS1 h\<alpha>_path]] .
      have hh10S1: "h (1, 0) \<in> top1_S1"
        using assms(1) h10S1 unfolding top1_continuous_map_on_def by (by100 blast)
      show ?thesis unfolding top1_loop_equiv_on_def
        using top1_basepoint_change_is_loop[OF hTS1 hra hconst_c]
              top1_constant_path_is_loop[OF hTS1 hh10S1]
              hchain by (by100 blast)
    qed
    have hresult: "top1_loop_equiv_on top1_S1 top1_S1_topology (h (1, 0)) (h \<circ> f)
        (top1_constant_path (h (1, 0)))"
      by (rule top1_loop_equiv_on_trans[OF hTS1 hbc' hbc_is_const])
    show "top1_path_homotopic_on top1_S1 top1_S1_topology (h (1, 0)) (h (1, 0))
        (h \<circ> f) (top1_constant_path (h (1, 0)))"
      using hresult unfolding top1_loop_equiv_on_def by (by100 blast)
  qed
  \<comment> \<open>Case split: h(1,0) = (1,0) gives direct contradiction;
     h(1,0) \<noteq> (1,0) needs WLOG rotation.\<close>
  show False
  proof (cases "h (1, 0) = (1::real, 0::real)")
    case True
    have "\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
        \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
              (h \<circ> f) (top1_constant_path (1, 0))"
      using hh_trivial_at_h10 True by simp
    thus False using hh_star_nontrivial by blast
  next
    case False
    \<comment> \<open>h(1,0) \<noteq> (1,0): WLOG rotation. Let \<rho> rotate h(1,0) to (1,0).\<close>
    \<comment> \<open>h(1,0) \<in> S^1, so h(1,0) = (cos \<theta>, sin \<theta>) for some \<theta>.
       Rotation by -\<theta>: \<rho>(x,y) = (x cos\<theta> + y sin\<theta>, -x sin\<theta> + y cos\<theta>).
       Then \<rho>(h(1,0)) = (cos^2\<theta> + sin^2\<theta>, 0) = (1,0).\<close>
    have h10_S1: "(1::real,0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
    have hh10: "h (1,0) \<in> top1_S1"
      using assms(1) h10_S1 unfolding top1_continuous_map_on_def by (by100 blast)
    let ?a = "fst (h (1, 0))" and ?b = "snd (h (1, 0))"
    have hab_S1: "?a^2 + ?b^2 = 1" using hh10 unfolding top1_S1_def by (by100 auto)
    \<comment> \<open>Define rotation \<rho>(x,y) = (ax+by, -bx+ay).\<close>
    let ?\<rho> = "\<lambda>(x::real,y::real). (?a*x + ?b*y, -?b*x + ?a*y)"
    have hrho_10: "?\<rho> (h (1,0)) = (1, 0)"
      using hab_S1 by (simp add: prod_eq_iff case_prod_beta power2_eq_square algebra_simps)
    \<comment> \<open>\<rho> commutes with negation: \<rho>(-x,-y) = -\<rho>(x,y).\<close>
    have hrho_neg: "\<And>x y. ?\<rho> (-x,-y) = (- fst (?\<rho> (x,y)), - snd (?\<rho> (x,y)))"
      by (by100 simp)
    \<comment> \<open>\<rho>\<circ>h is continuous, antipode-preserving, nulhomotopic.\<close>
    have "?\<rho> \<circ> h = (\<lambda>z. ?\<rho> (h z))" by (rule ext) (by100 simp)
    \<comment> \<open>\<rho> maps S^1 to S^1 and is continuous.\<close>
    have hrho_S1: "\<And>p. p \<in> top1_S1 \<Longrightarrow> ?\<rho> p \<in> top1_S1"
    proof -
      fix p assume hp: "p \<in> top1_S1"
      have hxy: "(fst p)^2 + (snd p)^2 = 1" using hp unfolding top1_S1_def by (by100 auto)
      have "(?a * fst p + ?b * snd p)^2 + (-?b * fst p + ?a * snd p)^2
          = (?a^2 + ?b^2) * ((fst p)^2 + (snd p)^2)"
        by (simp add: power2_eq_square algebra_simps)
      also have "\<dots> = 1" using hab_S1 hxy by (by100 simp)
      finally show "?\<rho> p \<in> top1_S1" unfolding top1_S1_def by (simp add: case_prod_beta)
    qed
    have hrho_cont_univ: "continuous_on UNIV ?\<rho>"
    proof -
      have "continuous_on UNIV (\<lambda>p::real\<times>real. (?a * fst p + ?b * snd p, -?b * fst p + ?a * snd p))"
        by (intro continuous_on_Pair continuous_on_add continuous_on_mult
            continuous_on_minus continuous_on_const continuous_on_fst continuous_on_snd continuous_on_id)
      moreover have "(\<lambda>p::real\<times>real. (?a * fst p + ?b * snd p, -?b * fst p + ?a * snd p)) = ?\<rho>"
        by (rule ext) (simp add: case_prod_beta)
      ultimately show ?thesis by (by100 metis)
    qed
    have hrho_top1: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology ?\<rho>"
    proof -
      have "top1_continuous_map_on top1_S1
          (subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1)
          top1_S1 (subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1) ?\<rho>"
        using top1_continuous_map_on_subspace_open_sets[OF hrho_S1 hrho_cont_univ]
        by (simp add: product_topology_on_open_sets[where ?'a=real and ?'b=real])
      thus ?thesis unfolding top1_S1_topology_def
        by (simp add: product_topology_on_open_sets[where ?'a=real and ?'b=real])
    qed
    have hrh_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (?\<rho> \<circ> h)"
      by (rule top1_continuous_map_on_comp[OF assms(1) hrho_top1])
    have hrh_anti: "top1_antipode_preserving_S1 (?\<rho> \<circ> h)"
      unfolding top1_antipode_preserving_S1_def
    proof (intro allI)
      fix x y
      have "h (-x, -y) = (- fst (h (x,y)), - snd (h (x,y)))"
        using assms(2) unfolding top1_antipode_preserving_S1_def by (by100 blast)
      thus "(?\<rho> \<circ> h) (-x, -y) = (- fst ((?\<rho> \<circ> h) (x, y)), - snd ((?\<rho> \<circ> h) (x, y)))"
        by (simp add: comp_def case_prod_beta algebra_simps)
    qed
    have hrh_nul: "top1_nulhomotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (?\<rho> \<circ> h)"
    proof -
      obtain c where hc: "c \<in> top1_S1"
          and hhom: "top1_homotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h (\<lambda>_. c)"
        using hnul unfolding top1_nulhomotopic_on_def by (by100 blast)
      have hrhc_S1: "?\<rho> c \<in> top1_S1"
        using hrho_S1[OF hc] by (by100 simp)
      have hTS1: "is_topology_on top1_S1 top1_S1_topology"
        unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF
              product_topology_on_is_topology_on[OF
                top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
                simplified]]) simp
      \<comment> \<open>Extract homotopy H from hhom, compose with \<rho>.\<close>
      obtain H where hHcont: "top1_continuous_map_on (top1_S1 \<times> I_set)
            (product_topology_on top1_S1_topology I_top) top1_S1 top1_S1_topology H"
          and hH0: "\<forall>x\<in>top1_S1. H (x, 0) = h x"
          and hH1: "\<forall>x\<in>top1_S1. H (x, 1) = c"
        using hhom unfolding top1_homotopic_on_def by (by100 blast)
      have hrH_cont: "top1_continuous_map_on (top1_S1 \<times> I_set)
          (product_topology_on top1_S1_topology I_top) top1_S1 top1_S1_topology (?\<rho> \<circ> H)"
        by (rule top1_continuous_map_on_comp[OF hHcont hrho_top1])
      have hconst_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (\<lambda>_. ?\<rho> c)"
        by (rule top1_continuous_map_on_const[OF hTS1 hTS1 hrhc_S1])
      have hrhH0: "\<forall>x\<in>top1_S1. (?\<rho> \<circ> H) (x, 0) = (?\<rho> \<circ> h) x"
        using hH0 by (by100 simp)
      have hrhH1: "\<forall>x\<in>top1_S1. (?\<rho> \<circ> H) (x, 1) = ?\<rho> c"
        using hH1 by (by100 simp)
      have "top1_homotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology
          (?\<rho> \<circ> h) (\<lambda>_. ?\<rho> c)"
        unfolding top1_homotopic_on_def
        apply (intro conjI exI[of _ "?\<rho> \<circ> H"])
        apply (rule hrh_cont)
        apply (rule hconst_cont)
        apply (rule hrH_cont)
        using hrhH0 apply (by100 simp)
        using hrhH1 apply (by100 simp)
        done
      thus ?thesis unfolding top1_nulhomotopic_on_def using hrhc_S1 by (by100 blast)
    qed
    have hrh_10: "(?\<rho> \<circ> h) (1, 0) = (1, 0)"
      using hrho_10 by (by100 simp)
    \<comment> \<open>Apply the same argument as the True case to \<rho>\<circ>h.\<close>
    \<comment> \<open>Step 1: (\<rho>\<circ>h)\<circ>f \<simeq> const for all loops f at (1,0) — from nulhomotopy + basepoint change.\<close>
    have hrh_trivial: "\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
        \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
              ((?\<rho> \<circ> h) \<circ> f) (top1_constant_path (1, 0))"
    proof (intro allI impI)
      fix f assume hf: "top1_is_loop_on top1_S1 top1_S1_topology (1::real, 0::real) f"
      show "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
          ((?\<rho> \<circ> h) \<circ> f) (top1_constant_path (1, 0))"
        by (rule nulhomotopic_trivializes_loops[OF hrh_cont hrh_nul hrh_10 hf])
    qed
    \<comment> \<open>Step 2: (\<rho>\<circ>h)_* is nontrivial (covering theory: antipode-preserving \<Rightarrow> induced map \<times>2).\<close>
    have hrh_star_nontrivial: "\<not> (\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
        \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
              ((?\<rho> \<circ> h) \<circ> f) (top1_constant_path (1, 0)))"
      using hrh_cont hrh_anti hrh_10 sorry
    show False using hrh_trivial hrh_star_nontrivial by (by100 blast)
  qed
qed

end
