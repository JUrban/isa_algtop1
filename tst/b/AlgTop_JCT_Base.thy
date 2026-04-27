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
          proof -
            have "2 * x\<^sup>2 = 1 + a" using hx2 by auto
            have "2 * y\<^sup>2 = 1 - a" using hy2 by auto
            have "(2*x*y)\<^sup>2 = 4 * (x\<^sup>2 * y\<^sup>2)"
              by (simp add: power2_eq_square algebra_simps)
            also have "4 * (x\<^sup>2 * y\<^sup>2) = (2 * x\<^sup>2) * (2 * y\<^sup>2)"
              by (simp add: algebra_simps)
            also have "\<dots> = (1+a) * (1-a)" using \<open>2*x\<^sup>2 = 1+a\<close> \<open>2*y\<^sup>2 = 1-a\<close> by simp
            also have "\<dots> = 1 - a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
            also have "\<dots> = b\<^sup>2" using hS1w by linarith
            finally show ?thesis .
          qed
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
      proof -
        have hV1_sub: "V1 \<subseteq> top1_S1" unfolding V1_def by (by100 blast)
        have hU_sub: "U_top \<subseteq> top1_S1" unfolding U_top_def by (by100 blast)
        have hq_V1: "top1_continuous_map_on V1 (subspace_topology top1_S1 top1_S1_topology V1)
            top1_S1 top1_S1_topology q"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hq_cont hV1_sub])
        have hq_img: "q ` V1 \<subseteq> U_top" using \<open>bij_betw q V1 U_top\<close> unfolding bij_betw_def by (by100 blast)
        \<comment> \<open>Restrict range: V \<in> subspace(S^1, U_top) means V = U_top \<inter> W, W \<in> top_S1.
           q^{-1}(V) \<inter> V1 = q^{-1}(W) \<inter> V1 \<in> subspace(S^1, V1).\<close>
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> V1" thus "q p \<in> U_top" using hq_img by (by100 blast)
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology U_top"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = U_top \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          have "{p \<in> V1. q p \<in> V} = {p \<in> V1. q p \<in> W}"
            using hq_img hVeq by (by100 blast)
          moreover have "{p \<in> V1. q p \<in> W} \<in> subspace_topology top1_S1 top1_S1_topology V1"
            using hq_V1 hW unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "{p \<in> V1. q p \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology V1" by simp
        qed
      qed
      show "top1_continuous_map_on U_top (subspace_topology top1_S1 top1_S1_topology U_top)
          V1 (subspace_topology top1_S1 top1_S1_topology V1) (inv_into V1 q)"
      proof -
        \<comment> \<open>The inverse is (a,b) \<mapsto> (sqrt((1+a)/2), sqrt((1-a)/2)).
           This is continuous as a real-valued function on U_top.\<close>
        define qi where "qi = (\<lambda>(a::real, b::real). (sqrt ((1+a)/2), sqrt ((1-a)/2)))"
        \<comment> \<open>qi agrees with inv_into V1 q on U_top.\<close>
        have hqi_eq: "\<And>w. w \<in> U_top \<Longrightarrow> qi w = inv_into V1 q w"
        proof -
          fix w assume hw: "w \<in> U_top"
          \<comment> \<open>qi w \<in> V1 and q(qi w) = w, so inv_into gives qi w.\<close>
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and hb: "b > 0"
            using hw unfolding U_top_def top1_S1_def hab by auto
          have "b\<^sup>2 > 0" using hb by (simp add: power2_eq_square zero_less_mult_iff)
          hence "a\<^sup>2 < 1" using hS1w by linarith
          hence ha_bounds: "a < 1 \<and> -1 < a"
          proof -
            have "\<not> (a \<ge> 1)" proof assume "1 \<le> a"
              hence "1 \<le> a * a" using mult_mono[of 1 a 1 a] by simp
              thus False using \<open>a\<^sup>2 < 1\<close> by (simp add: power2_eq_square) qed
            moreover have "\<not> (a \<le> -1)" proof assume "a \<le> -1"
              hence "(-a) \<ge> 1" by linarith
              hence "1 \<le> (-a)*(-a)" using mult_mono[of 1 "-a" 1 "-a"] by simp
              hence "1 \<le> a*a" by simp
              thus False using \<open>a\<^sup>2 < 1\<close> by (simp add: power2_eq_square) qed
            ultimately show ?thesis by linarith
          qed
          define x where "x = sqrt ((1+a)/2)"
          define y where "y = sqrt ((1-a)/2)"
          have "qi w = (x, y)" unfolding qi_def hab x_def y_def by simp
          moreover have "(x, y) \<in> V1"
          proof -
            have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
            have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
            have "x > 0" unfolding x_def using ha_bounds by simp
            have "y > 0"
            proof -
              have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2"
              proof -
                have "2*x\<^sup>2 = 1+a" using hx2 by auto
                have "2*y\<^sup>2 = 1-a" using hy2 by auto
                have "(2*x*y)\<^sup>2 = 4*(x\<^sup>2*y\<^sup>2)" by (simp add: power2_eq_square algebra_simps)
                also have "\<dots> = (2*x\<^sup>2)*(2*y\<^sup>2)" by (simp add: algebra_simps)
                also have "\<dots> = (1+a)*(1-a)" using \<open>2*x\<^sup>2 = 1+a\<close> \<open>2*y\<^sup>2 = 1-a\<close> by simp
                also have "\<dots> = 1 - a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
                also have "\<dots> = b\<^sup>2" using hS1w by linarith
                finally show ?thesis .
              qed
              have "2*x*y \<ge> 0" using \<open>x > 0\<close> ha_bounds unfolding y_def
                by (intro mult_nonneg_nonneg) auto
              have "2*x*y = b" using h2xy_eq_b2 \<open>2*x*y \<ge> 0\<close> hb by (simp add: power2_eq_iff_nonneg)
              hence "x*y > 0" using hb by simp
              thus "y > 0" using \<open>x > 0\<close> by (simp add: zero_less_mult_iff)
            qed
            have "x\<^sup>2 + y\<^sup>2 = 1" using hx2 hy2 by simp
            show ?thesis unfolding V1_def top1_S1_def using \<open>x > 0\<close> \<open>y > 0\<close> \<open>x\<^sup>2+y\<^sup>2=1\<close> by simp
          qed
          moreover have "q (x, y) = w"
          proof -
            have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
            have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            have hqa: "x\<^sup>2 - y\<^sup>2 = a" using hx2 hy2 by simp
            have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2"
            proof -
              have "(2*x*y)\<^sup>2 = (2*x\<^sup>2)*(2*y\<^sup>2)" by (simp add: power2_eq_square algebra_simps)
              also have "\<dots> = (1+a)*(1-a)" using \<open>2*x\<^sup>2=1+a\<close> \<open>2*y\<^sup>2=1-a\<close> by simp
              also have "\<dots> = 1-a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
              also have "\<dots> = b\<^sup>2" using hS1w by linarith
              finally show ?thesis .
            qed
            have "x > 0" unfolding x_def using ha_bounds by simp
            have "2*x*y \<ge> 0" using \<open>x > 0\<close> ha_bounds unfolding y_def
              by (intro mult_nonneg_nonneg) auto
            have hqb: "2*x*y = b"
              using h2xy_eq_b2 \<open>2*x*y \<ge> 0\<close> hb by (simp add: power2_eq_iff_nonneg)
            show ?thesis unfolding q_def hab using hqa hqb by simp
          qed
          ultimately show "qi w = inv_into V1 q w"
            by (simp add: inv_into_f_eq[OF inj_on_subset[OF bij_betw_imp_inj_on[OF \<open>bij_betw q V1 U_top\<close>]]])
        qed
        \<comment> \<open>qi maps U_top into V1.\<close>
        have hqi_V1: "\<And>w. w \<in> U_top \<Longrightarrow> qi w \<in> V1"
        proof -
          fix w assume hw: "w \<in> U_top"
          have "qi w = inv_into V1 q w" by (rule hqi_eq[OF hw])
          moreover have "inv_into V1 q w \<in> V1"
          proof -
            have "q ` V1 = U_top" using \<open>bij_betw q V1 U_top\<close> unfolding bij_betw_def by (by100 blast)
            hence "w \<in> q ` V1" using hw by simp
            thus ?thesis by (rule inv_into_into)
          qed
          ultimately show "qi w \<in> V1" by simp
        qed
        \<comment> \<open>qi is continuous on U_top (sqrt composed with continuous affine maps).\<close>
        have hqi_cont: "continuous_on U_top qi"
        proof -
          have "continuous_on U_top (\<lambda>(a, b). (sqrt ((1+a)/2), sqrt ((1-a)/2)))"
            unfolding split_def by (intro continuous_intros) auto
          thus ?thesis unfolding qi_def by simp
        qed
        \<comment> \<open>Bridge: since qi = inv_into on U_top, and qi is continuous + maps into V1,
           we get inv_into continuous from U_top to V1.\<close>
        have hU_sub: "U_top \<subseteq> top1_S1" unfolding U_top_def by (by100 blast)
        have hV1_sub: "V1 \<subseteq> top1_S1" unfolding V1_def by (by100 blast)
        \<comment> \<open>U_top \<subseteq> UNIV (as pairs of reals), so continuous_on U_top qi gives
           preimages of open sets are relatively open.\<close>
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix w assume "w \<in> U_top"
          show "inv_into V1 q w \<in> V1" using hqi_eq[OF \<open>w \<in> U_top\<close>] hqi_V1[OF \<open>w \<in> U_top\<close>] by simp
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology V1"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = V1 \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          obtain W'' where hW'': "W'' \<in> product_topology_on top1_open_sets top1_open_sets"
              and hWeq: "W = top1_S1 \<inter> W''"
            using hW unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
          have hW'_open: "open W''" using hW''
            by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
          define W' where "W' = W''"
          have hW': "open W'" and hW'eq: "W = top1_S1 \<inter> W'"
            using hW'_open hWeq unfolding W'_def by auto
          \<comment> \<open>{w \<in> U_top. inv_into w \<in> V} = {w \<in> U_top. qi w \<in> W'} (since qi maps into V1 \<subseteq> S^1).\<close>
          have "{w \<in> U_top. inv_into V1 q w \<in> V} = {w \<in> U_top. qi w \<in> W'}"
          proof (intro Collect_cong conj_cong refl)
            fix w assume hw: "w \<in> U_top"
            have "inv_into V1 q w = qi w" using hqi_eq[OF hw] by simp
            moreover have "qi w \<in> V1" using hqi_V1[OF hw] .
            moreover have "V1 \<subseteq> top1_S1" using hV1_sub .
            ultimately show "(inv_into V1 q w \<in> V) = (qi w \<in> W')"
              using hVeq hW'eq by auto
          qed
          \<comment> \<open>qi^{-1}(W') \<inter> U_top is open in U_top (by continuous_on).\<close>
          moreover have "{w \<in> U_top. qi w \<in> W'} \<in> subspace_topology top1_S1 top1_S1_topology U_top"
          proof -
            obtain U where hU: "open U" and hUeq: "U \<inter> U_top = qi -` W' \<inter> U_top"
              using hqi_cont hW' unfolding continuous_on_open_invariant by blast
            have "{w \<in> U_top. qi w \<in> W'} = U \<inter> U_top" using hUeq by (by100 blast)
            moreover have "U \<inter> U_top \<in> subspace_topology top1_S1 top1_S1_topology U_top"
            proof -
              have "U \<in> top1_open_sets" using hU unfolding top1_open_sets_def by simp
              hence "U \<in> product_topology_on top1_open_sets top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              hence "top1_S1 \<inter> U \<in> top1_S1_topology"
                unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
              moreover have "U \<inter> U_top = U_top \<inter> (top1_S1 \<inter> U)" using hU_sub by blast
              ultimately show ?thesis unfolding subspace_topology_def by blast
            qed
            ultimately show ?thesis by simp
          qed
          ultimately show "{w \<in> U_top. inv_into V1 q w \<in> V}
              \<in> subspace_topology top1_S1 top1_S1_topology U_top" by simp
        qed
      qed
    qed
    \<comment> \<open>q is a homeomorphism V2 \<rightarrow> U_top. Inverse: (a,b) \<mapsto> (-sqrt((1+a)/2), -sqrt((1-a)/2)).\<close>
    have hhomeo2: "top1_homeomorphism_on V2 (subspace_topology top1_S1 top1_S1_topology V2)
        U_top (subspace_topology top1_S1 top1_S1_topology U_top) q"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      have hTS1': "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      show "is_topology_on V2 (subspace_topology top1_S1 top1_S1_topology V2)"
        by (rule subspace_topology_is_topology_on[OF hTS1']) (use V2_def in blast)
      show "is_topology_on U_top (subspace_topology top1_S1 top1_S1_topology U_top)"
        by (rule subspace_topology_is_topology_on[OF hTS1']) (use U_top_def in blast)
      show "bij_betw q V2 U_top"
      proof (rule bij_betw_imageI)
        show "inj_on q V2"
        proof (rule inj_onI)
          fix p1 p2 assume hp1: "p1 \<in> V2" and hp2: "p2 \<in> V2" and heq: "q p1 = q p2"
          obtain x1 y1 where h1: "p1 = (x1, y1)" by (cases p1) auto
          obtain x2 y2 where h2: "p2 = (x2, y2)" by (cases p2) auto
          have hx1: "x1 < 0" "y1 < 0" "x1\<^sup>2 + y1\<^sup>2 = 1"
            using hp1 unfolding V2_def top1_S1_def h1 by auto
          have hx2: "x2 < 0" "y2 < 0" "x2\<^sup>2 + y2\<^sup>2 = 1"
            using hp2 unfolding V2_def top1_S1_def h2 by auto
          have "x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2"
            using heq unfolding q_def h1 h2 by auto
          have "x1\<^sup>2 = (1 + (x1\<^sup>2 - y1\<^sup>2))/2" using hx1(3) by (simp add: field_simps)
          also have "\<dots> = (1 + (x2\<^sup>2 - y2\<^sup>2))/2" using \<open>x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2\<close> by simp
          also have "\<dots> = x2\<^sup>2" using hx2(3) by (simp add: field_simps)
          finally have "x1\<^sup>2 = x2\<^sup>2" .
          hence "x1 = x2 \<or> x1 = -x2" using power2_eq_iff by (by100 blast)
          hence "x1 = x2" using hx1(1) hx2(1) by linarith
          moreover have "y1\<^sup>2 = y2\<^sup>2" using \<open>x1\<^sup>2 = x2\<^sup>2\<close> hx1(3) hx2(3) by linarith
          hence "y1 = y2 \<or> y1 = -y2" using power2_eq_iff by (by100 blast)
          hence "y1 = y2" using hx1(2) hx2(2) by linarith
          ultimately show "p1 = p2" unfolding h1 h2 by simp
        qed
      next
        show "q ` V2 = U_top"
        proof (intro set_eqI iffI)
          fix w assume "w \<in> q ` V2"
          then obtain p where hp: "p \<in> V2" and hw: "w = q p" by (by100 blast)
          have "p \<in> top1_S1" "fst p < 0" "snd p < 0" using hp unfolding V2_def by auto
          have "q p \<in> top1_S1" by (rule hq_S1[OF \<open>p \<in> top1_S1\<close>])
          moreover have "snd (q p) = 2 * fst p * snd p" unfolding q_def by simp
          hence "snd (q p) > 0" using \<open>fst p < 0\<close> \<open>snd p < 0\<close> by (simp add: mult_neg_neg)
          ultimately show "w \<in> U_top" unfolding U_top_def using hw by simp
        next
          fix w assume hw: "w \<in> U_top"
          \<comment> \<open>Inverse: (a,b) \<mapsto> (-sqrt((1+a)/2), -sqrt((1-a)/2)).\<close>
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and hb: "b > 0"
            using hw unfolding U_top_def top1_S1_def hab by auto
          \<comment> \<open>Reuse the V1 inverse but negate.\<close>
          have "b\<^sup>2 > 0" using hb by (simp add: power2_eq_square zero_less_mult_iff)
          hence "a\<^sup>2 < 1" using hS1w by linarith
          hence ha_bounds: "a < 1 \<and> -1 < a"
          proof -
            have "\<not> (a \<ge> 1)" proof assume "1 \<le> a"
              hence "1 \<le> a * a" using mult_mono[of 1 a 1 a] by simp
              thus False using \<open>a\<^sup>2 < 1\<close> by (simp add: power2_eq_square) qed
            moreover have "\<not> (a \<le> -1)" proof assume "a \<le> -1"
              hence "(-a) \<ge> 1" by linarith
              hence "1 \<le> (-a)*(-a)" using mult_mono[of 1 "-a" 1 "-a"] by simp
              hence "1 \<le> a*a" by simp
              thus False using \<open>a\<^sup>2 < 1\<close> by (simp add: power2_eq_square) qed
            ultimately show ?thesis by linarith
          qed
          define x where "x = -sqrt ((1+a)/2)"
          define y where "y = -sqrt ((1-a)/2)"
          have hx_neg: "x < 0" unfolding x_def using ha_bounds by simp
          have hy_neg: "y < 0" proof -
            have "sqrt ((1-a)/2) > 0" using ha_bounds by simp
            thus ?thesis unfolding y_def by simp
          qed
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square
            using ha_bounds by (simp add: real_sqrt_mult_self)
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square
            using ha_bounds by (simp add: real_sqrt_mult_self)
          have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx2 hy2 by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a" using hx2 hy2 by simp
          have "2*x\<^sup>2 = 1+a" using hx2 by auto
          have "2*y\<^sup>2 = 1-a" using hy2 by auto
          have "(2*x*y)\<^sup>2 = 4*(x\<^sup>2*y\<^sup>2)" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (2*x\<^sup>2)*(2*y\<^sup>2)" by (simp add: algebra_simps)
          also have "\<dots> = (1+a)*(1-a)" using \<open>2*x\<^sup>2=1+a\<close> \<open>2*y\<^sup>2=1-a\<close> by simp
          also have "\<dots> = 1 - a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2" using hS1w by linarith
          finally have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2" .
          have "2*x*y \<ge> 0" using hx_neg hy_neg by (simp add: mult_nonpos_nonpos)
          have hqb: "2*x*y = b" using h2xy_eq_b2 \<open>2*x*y \<ge> 0\<close> hb by (simp add: power2_eq_iff_nonneg)
          have "(x, y) \<in> V2" unfolding V2_def top1_S1_def using hxy_S1 hx_neg hy_neg by simp
          moreover have "q (x, y) = w" unfolding q_def hab using hqa hqb by simp
          ultimately show "w \<in> q ` V2" by (by100 blast)
        qed
      qed
      \<comment> \<open>Continuity: same pattern as V1.\<close>
      show "top1_continuous_map_on V2 (subspace_topology top1_S1 top1_S1_topology V2)
          U_top (subspace_topology top1_S1 top1_S1_topology U_top) q"
      proof -
        have hV2_sub: "V2 \<subseteq> top1_S1" unfolding V2_def by (by100 blast)
        have hU_sub: "U_top \<subseteq> top1_S1" unfolding U_top_def by (by100 blast)
        have hq_V2: "top1_continuous_map_on V2 (subspace_topology top1_S1 top1_S1_topology V2)
            top1_S1 top1_S1_topology q"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hq_cont hV2_sub])
        have hq_img: "q ` V2 \<subseteq> U_top"
          using \<open>bij_betw q V2 U_top\<close> unfolding bij_betw_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> V2" thus "q p \<in> U_top" using hq_img by (by100 blast)
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology U_top"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = U_top \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          have "{p \<in> V2. q p \<in> V} = {p \<in> V2. q p \<in> W}"
            using hq_img hVeq by (by100 blast)
          moreover have "{p \<in> V2. q p \<in> W} \<in> subspace_topology top1_S1 top1_S1_topology V2"
            using hq_V2 hW unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "{p \<in> V2. q p \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology V2" by simp
        qed
      qed
      show "top1_continuous_map_on U_top (subspace_topology top1_S1 top1_S1_topology U_top)
          V2 (subspace_topology top1_S1 top1_S1_topology V2) (inv_into V2 q)"
      proof -
        define qi2 where "qi2 = (\<lambda>(a::real, b::real). (-sqrt ((1+a)/2), -sqrt ((1-a)/2)))"
        \<comment> \<open>qi2 maps U_top into V2 and q \<circ> qi2 = id on U_top.\<close>
        have hqi2_props: "\<And>w. w \<in> U_top \<Longrightarrow> qi2 w \<in> V2 \<and> q (qi2 w) = w"
        proof -
          fix w assume hw: "w \<in> U_top"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and hb: "b > 0"
            using hw unfolding U_top_def top1_S1_def hab by auto
          have "b\<^sup>2 > 0" using hb by (simp add: power2_eq_square zero_less_mult_iff)
          hence ha2: "a\<^sup>2 < 1" using hS1w by linarith
          hence ha_bounds: "a < 1 \<and> -1 < a"
          proof -
            have "\<not> (a \<ge> 1)" proof assume "1 \<le> a"
              hence "1 \<le> a * a" using mult_mono[of 1 a 1 a] by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            moreover have "\<not> (a \<le> -1)" proof assume "a \<le> -1"
              hence "1 \<le> (-a)*(-a)" using mult_mono[of 1 "-a" 1 "-a"] by linarith
              thus False using ha2 by (simp add: power2_eq_square) qed
            ultimately show ?thesis by linarith
          qed
          define x where "x = -sqrt ((1+a)/2)"
          define y where "y = -sqrt ((1-a)/2)"
          have hqi2_w: "qi2 w = (x, y)" unfolding qi2_def hab x_def y_def by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hx_neg: "x < 0" unfolding x_def using ha_bounds by simp
          have hy_neg: "y < 0" unfolding y_def using ha_bounds by simp
          have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx2 hy2 by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a" using hx2 hy2 by simp
          have "2*x\<^sup>2 = 1+a" using hx2 by auto
          have "2*y\<^sup>2 = 1-a" using hy2 by auto
          have "(2*x*y)\<^sup>2 = (2*x\<^sup>2)*(2*y\<^sup>2)" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (1+a)*(1-a)" using \<open>2*x\<^sup>2=1+a\<close> \<open>2*y\<^sup>2=1-a\<close> by simp
          also have "\<dots> = 1-a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2" using hS1w by linarith
          finally have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2" .
          have "2*x*y \<ge> 0" using hx_neg hy_neg by (simp add: mult_nonpos_nonpos)
          have hqb: "2*x*y = b" using h2xy_eq_b2 \<open>2*x*y \<ge> 0\<close> hb by (simp add: power2_eq_iff_nonneg)
          have "qi2 w \<in> V2" unfolding hqi2_w V2_def top1_S1_def using hxy_S1 hx_neg hy_neg by simp
          moreover have "q (qi2 w) = w"
          proof -
            have "fst (q (x, y)) = x\<^sup>2 - y\<^sup>2" unfolding q_def by simp
            hence "fst (q (x, y)) = a" using hqa by simp
            moreover have "snd (q (x, y)) = 2*x*y" unfolding q_def by simp
            hence "snd (q (x, y)) = b" using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hqi2_w hab by simp
          qed
          ultimately show "qi2 w \<in> V2 \<and> q (qi2 w) = w" by (by100 blast)
        qed
        have hqi2_eq: "\<And>w. w \<in> U_top \<Longrightarrow> qi2 w = inv_into V2 q w"
        proof -
          fix w assume hw: "w \<in> U_top"
          have "qi2 w \<in> V2" and "q (qi2 w) = w" using hqi2_props[OF hw] by auto
          thus "qi2 w = inv_into V2 q w"
            by (simp add: inv_into_f_eq[OF inj_on_subset[OF bij_betw_imp_inj_on[OF \<open>bij_betw q V2 U_top\<close>]]])
        qed
        have hqi2_V2: "\<And>w. w \<in> U_top \<Longrightarrow> qi2 w \<in> V2"
          using hqi2_props by (by100 blast)
        have hqi2_cont: "continuous_on U_top qi2"
          unfolding qi2_def split_def by (intro continuous_intros) auto
        have hU_sub: "U_top \<subseteq> top1_S1" unfolding U_top_def by (by100 blast)
        have hV2_sub: "V2 \<subseteq> top1_S1" unfolding V2_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix w assume "w \<in> U_top"
          show "inv_into V2 q w \<in> V2" using hqi2_eq[OF \<open>w \<in> U_top\<close>] hqi2_V2[OF \<open>w \<in> U_top\<close>] by simp
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology V2"
          obtain W'' where hW'': "W'' \<in> product_topology_on top1_open_sets top1_open_sets"
              and hWeq: "V = V2 \<inter> (top1_S1 \<inter> W'')"
          proof -
            obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = V2 \<inter> W"
              using hV unfolding subspace_topology_def by (by100 blast)
            obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
                and hWW': "W = top1_S1 \<inter> W'"
              using hW unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
            show ?thesis using that[OF hW'] hVeq hWW' by simp
          qed
          have hW''_open: "open W''"
            using hW'' by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
          have "{w \<in> U_top. inv_into V2 q w \<in> V} = {w \<in> U_top. qi2 w \<in> W''}"
          proof (intro Collect_cong conj_cong refl)
            fix w assume hw: "w \<in> U_top"
            have "inv_into V2 q w = qi2 w" using hqi2_eq[OF hw] by simp
            moreover have "qi2 w \<in> V2" using hqi2_V2[OF hw] .
            moreover have "V2 \<subseteq> top1_S1" using hV2_sub .
            ultimately show "(inv_into V2 q w \<in> V) = (qi2 w \<in> W'')" using hWeq by auto
          qed
          moreover have "{w \<in> U_top. qi2 w \<in> W''} \<in> subspace_topology top1_S1 top1_S1_topology U_top"
          proof -
            obtain U where hU: "open U" and hUeq: "U \<inter> U_top = qi2 -` W'' \<inter> U_top"
              using hqi2_cont hW''_open unfolding continuous_on_open_invariant by blast
            have "{w \<in> U_top. qi2 w \<in> W''} = U \<inter> U_top" using hUeq by (by100 blast)
            moreover have "U \<inter> U_top \<in> subspace_topology top1_S1 top1_S1_topology U_top"
            proof -
              have "U \<in> top1_open_sets" using hU unfolding top1_open_sets_def by simp
              hence "U \<in> product_topology_on top1_open_sets top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              hence "top1_S1 \<inter> U \<in> top1_S1_topology"
                unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
              moreover have "U \<inter> U_top = U_top \<inter> (top1_S1 \<inter> U)" using hU_sub by blast
              ultimately show ?thesis unfolding subspace_topology_def by blast
            qed
            ultimately show ?thesis by simp
          qed
          ultimately show "{w \<in> U_top. inv_into V2 q w \<in> V}
              \<in> subspace_topology top1_S1 top1_S1_topology U_top" by simp
        qed
      qed
    qed
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
  \<comment> \<open>The remaining 3 semicircle cases are analogous to U_top.
     U_bot: preimage splits into Q2 \<union> Q4, inverse uses mixed signs.
     U_right/U_left: preimage splits using fst > 0 / fst < 0 condition.
     Each follows the exact same proof pattern as hevenly_top.\<close>
  have hevenly_bot: "top1_evenly_covered_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q U_bot"
  proof -
    have hU_bot_open: "openin_on top1_S1 top1_S1_topology U_bot"
    proof -
      have "open {p :: real \<times> real. snd p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      hence "{p :: real \<times> real. snd p < 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. snd p < 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. snd p < 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. snd p < 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "U_bot = top1_S1 \<inter> {p. snd p < 0}" unfolding U_bot_def by (by100 blast)
      moreover have "U_bot \<subseteq> top1_S1" unfolding U_bot_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    define V3 where "V3 = {p \<in> top1_S1. fst p < 0 \<and> snd p > 0}"
    define V4 where "V4 = {p \<in> top1_S1. fst p > 0 \<and> snd p < 0}"
    have hV3_open: "openin_on top1_S1 top1_S1_topology V3"
    proof -
      have h1: "open {p :: real \<times> real. fst p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have h2: "open {p :: real \<times> real. snd p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have "open {p :: real \<times> real. fst p < 0 \<and> snd p > 0}"
        using open_Int[OF h1 h2] by (auto simp: Int_def)
      hence "{p :: real \<times> real. fst p < 0 \<and> snd p > 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p < 0 \<and> snd p > 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p < 0 \<and> snd p > 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p < 0 \<and> snd p > 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "V3 = top1_S1 \<inter> {p. fst p < 0 \<and> snd p > 0}" unfolding V3_def by (by100 blast)
      moreover have "V3 \<subseteq> top1_S1" unfolding V3_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    have hV4_open: "openin_on top1_S1 top1_S1_topology V4"
    proof -
      have h1: "open {p :: real \<times> real. fst p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have h2: "open {p :: real \<times> real. snd p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have "open {p :: real \<times> real. fst p > 0 \<and> snd p < 0}"
        using open_Int[OF h1 h2] by (auto simp: Int_def)
      hence "{p :: real \<times> real. fst p > 0 \<and> snd p < 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p > 0 \<and> snd p < 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p > 0 \<and> snd p < 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p > 0 \<and> snd p < 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "V4 = top1_S1 \<inter> {p. fst p > 0 \<and> snd p < 0}" unfolding V4_def by (by100 blast)
      moreover have "V4 \<subseteq> top1_S1" unfolding V4_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    have hV_disj: "V3 \<inter> V4 = {}" unfolding V3_def V4_def by auto
    have hpreimage: "{p \<in> top1_S1. q p \<in> U_bot} = V3 \<union> V4"
    proof (intro set_eqI iffI)
      fix p assume hp: "p \<in> {p \<in> top1_S1. q p \<in> U_bot}"
      hence hpS1: "p \<in> top1_S1" and hqp: "q p \<in> U_bot" by auto
      obtain x y where hxy: "p = (x, y)" by (cases p) auto
      have "snd (q p) < 0" using hqp unfolding U_bot_def by (by100 blast)
      hence "2*x*y < 0" unfolding q_def hxy by simp
      hence "x*y < 0" by simp
      hence "(x < 0 \<and> y > 0) \<or> (x > 0 \<and> y < 0)" using mult_less_0_iff by force
      thus "p \<in> V3 \<union> V4" unfolding V3_def V4_def using hpS1 hxy by auto
    next
      fix p assume "p \<in> V3 \<union> V4"
      hence hpS1: "p \<in> top1_S1" and hq: "fst p * snd p < 0"
        unfolding V3_def V4_def by (auto intro: mult_neg_pos mult_pos_neg)
      have "snd (q p) = 2 * fst p * snd p" unfolding q_def by simp
      hence "snd (q p) < 0" using hq by simp
      moreover have "q p \<in> top1_S1" by (rule hq_S1[OF hpS1])
      ultimately show "p \<in> {p \<in> top1_S1. q p \<in> U_bot}" unfolding U_bot_def using hpS1 by auto
    qed
    \<comment> \<open>Homeomorphisms V3 \<rightarrow> U_bot and V4 \<rightarrow> U_bot: same structure as hhomeo1/hhomeo2.
       V3 inverse: (a,b) \<mapsto> (-sqrt((1+a)/2), sqrt((1-a)/2)) with b < 0.
       V4 inverse: (a,b) \<mapsto> (sqrt((1+a)/2), -sqrt((1-a)/2)) with b < 0.\<close>
    have hhomeo3: "top1_homeomorphism_on V3 (subspace_topology top1_S1 top1_S1_topology V3)
        U_bot (subspace_topology top1_S1 top1_S1_topology U_bot) q"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      have hTS1: "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      show "is_topology_on V3 (subspace_topology top1_S1 top1_S1_topology V3)"
        by (rule subspace_topology_is_topology_on[OF hTS1]) (use V3_def in blast)
      show "is_topology_on U_bot (subspace_topology top1_S1 top1_S1_topology U_bot)"
        by (rule subspace_topology_is_topology_on[OF hTS1]) (use U_bot_def in blast)
      show "bij_betw q V3 U_bot"
      proof (rule bij_betw_imageI)
        show "inj_on q V3"
        proof (rule inj_onI)
          fix p1 p2 assume hp1: "p1 \<in> V3" and hp2: "p2 \<in> V3" and heq: "q p1 = q p2"
          obtain x1 y1 where h1: "p1 = (x1, y1)" by (cases p1) auto
          obtain x2 y2 where h2: "p2 = (x2, y2)" by (cases p2) auto
          have hx1: "x1 < 0" "y1 > 0" "x1\<^sup>2 + y1\<^sup>2 = 1" using hp1 unfolding V3_def top1_S1_def h1 by auto
          have hx2: "x2 < 0" "y2 > 0" "x2\<^sup>2 + y2\<^sup>2 = 1" using hp2 unfolding V3_def top1_S1_def h2 by auto
          have "x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2" using heq unfolding q_def h1 h2 by auto
          have "x1\<^sup>2 = (1 + (x1\<^sup>2 - y1\<^sup>2))/2" using hx1(3) by (simp add: field_simps)
          also have "\<dots> = (1 + (x2\<^sup>2 - y2\<^sup>2))/2" using \<open>x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2\<close> by simp
          also have "\<dots> = x2\<^sup>2" using hx2(3) by (simp add: field_simps)
          finally have "x1\<^sup>2 = x2\<^sup>2" .
          hence "x1 = x2 \<or> x1 = -x2" using power2_eq_iff by (by100 blast)
          hence "x1 = x2" using hx1(1) hx2(1) by linarith
          moreover have "y1\<^sup>2 = y2\<^sup>2" using \<open>x1\<^sup>2 = x2\<^sup>2\<close> hx1(3) hx2(3) by linarith
          hence "y1 = y2 \<or> y1 = -y2" using power2_eq_iff by (by100 blast)
          hence "y1 = y2" using hx1(2) hx2(2) by linarith
          ultimately show "p1 = p2" unfolding h1 h2 by simp
        qed
      next
        show "q ` V3 = U_bot"
        proof (intro set_eqI iffI)
          fix w assume "w \<in> q ` V3"
          then obtain p where hp: "p \<in> V3" and hw: "w = q p" by (by100 blast)
          have "p \<in> top1_S1" "fst p < 0" "snd p > 0" using hp unfolding V3_def by auto
          have "q p \<in> top1_S1" by (rule hq_S1[OF \<open>p \<in> top1_S1\<close>])
          moreover have "snd (q p) = 2 * fst p * snd p" unfolding q_def by simp
          hence "snd (q p) < 0" using \<open>fst p < 0\<close> \<open>snd p > 0\<close> by (simp add: mult_neg_pos)
          ultimately show "w \<in> U_bot" unfolding U_bot_def using hw by simp
        next
          fix w assume hw: "w \<in> U_bot"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and hb: "b < 0" using hw unfolding U_bot_def top1_S1_def hab by auto
          have "b\<^sup>2 > 0" using hb by (simp add: power2_eq_square) (simp add: mult_neg_neg)
          hence ha2: "a\<^sup>2 < 1" using hS1w by linarith
          hence ha_bounds: "a < 1 \<and> -1 < a"
          proof -
            have "\<not> (a \<ge> 1)" proof assume "1 \<le> a"
              hence "1 \<le> a * a" using mult_mono[of 1 a 1 a] by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            moreover have "\<not> (a \<le> -1)" proof assume "a \<le> -1"
              hence "1 \<le> (-a)*(-a)" using mult_mono[of 1 "-a" 1 "-a"] by linarith
              hence "1 \<le> a*a" by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            ultimately show ?thesis by linarith
          qed
          define x where "x = -sqrt ((1+a)/2)"
          define y where "y = sqrt ((1-a)/2)"
          have hx_neg: "x < 0" unfolding x_def using ha_bounds by simp
          have hy_pos: "y > 0" unfolding y_def using ha_bounds by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx2 hy2 by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a" using hx2 hy2 by simp
          have "2*x\<^sup>2 = 1+a" using hx2 by auto
          have "2*y\<^sup>2 = 1-a" using hy2 by auto
          have "(2*x*y)\<^sup>2 = (2*x\<^sup>2)*(2*y\<^sup>2)" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (1+a)*(1-a)" using \<open>2*x\<^sup>2=1+a\<close> \<open>2*y\<^sup>2=1-a\<close> by simp
          also have "\<dots> = 1-a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2" using hS1w by linarith
          finally have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2" .
          have "2*x*y \<le> 0" using hx_neg hy_pos by (simp add: mult_nonpos_nonneg)
          have hqb: "2*x*y = b"
          proof -
            have "2*x*y = b \<or> 2*x*y = -b" using h2xy_eq_b2 power2_eq_iff by (by100 blast)
            thus ?thesis using \<open>2*x*y \<le> 0\<close> hb by linarith
          qed
          have "(x, y) \<in> V3" unfolding V3_def top1_S1_def using hxy_S1 hx_neg hy_pos by simp
          moreover have "q (x, y) = w"
          proof -
            have "fst (q (x, y)) = x\<^sup>2 - y\<^sup>2" unfolding q_def by simp
            hence "fst (q (x, y)) = a" using hqa by simp
            moreover have "snd (q (x, y)) = 2*x*y" unfolding q_def by simp
            hence "snd (q (x, y)) = b" using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hab by simp
          qed
          ultimately show "w \<in> q ` V3" by (by100 blast)
        qed
      qed
      show "top1_continuous_map_on V3 (subspace_topology top1_S1 top1_S1_topology V3)
          U_bot (subspace_topology top1_S1 top1_S1_topology U_bot) q"
      proof -
        have hV3_sub: "V3 \<subseteq> top1_S1" unfolding V3_def by (by100 blast)
        have hU_sub: "U_bot \<subseteq> top1_S1" unfolding U_bot_def by (by100 blast)
        have hq_V3: "top1_continuous_map_on V3 (subspace_topology top1_S1 top1_S1_topology V3)
            top1_S1 top1_S1_topology q"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hq_cont hV3_sub])
        have hq_img: "q ` V3 \<subseteq> U_bot"
          using \<open>bij_betw q V3 U_bot\<close> unfolding bij_betw_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> V3" thus "q p \<in> U_bot" using hq_img by (by100 blast)
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology U_bot"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = U_bot \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          have "{p \<in> V3. q p \<in> V} = {p \<in> V3. q p \<in> W}"
            using hq_img hVeq by (by100 blast)
          moreover have "{p \<in> V3. q p \<in> W} \<in> subspace_topology top1_S1 top1_S1_topology V3"
            using hq_V3 hW unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "{p \<in> V3. q p \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology V3" by simp
        qed
      qed
      show "top1_continuous_map_on U_bot (subspace_topology top1_S1 top1_S1_topology U_bot)
          V3 (subspace_topology top1_S1 top1_S1_topology V3) (inv_into V3 q)"
      proof -
        define qi3 where "qi3 = (\<lambda>(a::real, b::real). (-sqrt ((1+a)/2), sqrt ((1-a)/2)))"
        have hqi3_props: "\<And>w. w \<in> U_bot \<Longrightarrow> qi3 w \<in> V3 \<and> q (qi3 w) = w"
        proof -
          fix w assume hw: "w \<in> U_bot"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and hb: "b < 0" using hw unfolding U_bot_def top1_S1_def hab by auto
          have "b\<^sup>2 > 0" using hb by (simp add: power2_eq_square) (simp add: mult_neg_neg)
          hence ha2: "a\<^sup>2 < 1" using hS1w by linarith
          hence ha_bounds: "a < 1 \<and> -1 < a"
          proof -
            have "\<not> (a \<ge> 1)" proof assume "1 \<le> a"
              hence "1 \<le> a * a" using mult_mono[of 1 a 1 a] by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            moreover have "\<not> (a \<le> -1)" proof assume "a \<le> -1"
              hence "1 \<le> (-a)*(-a)" using mult_mono[of 1 "-a" 1 "-a"] by linarith
              hence "1 \<le> a*a" by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            ultimately show ?thesis by linarith
          qed
          define x where "x = -sqrt ((1+a)/2)" define y where "y = sqrt ((1-a)/2)"
          have hqi3_w: "qi3 w = (x, y)" unfolding qi3_def hab x_def y_def by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hx_neg: "x < 0" unfolding x_def using ha_bounds by simp
          have hy_pos: "y > 0" unfolding y_def using ha_bounds by simp
          have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx2 hy2 by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a" using hx2 hy2 by simp
          have "2*x\<^sup>2 = 1+a" using hx2 by auto
          have "2*y\<^sup>2 = 1-a" using hy2 by auto
          have "(2*x*y)\<^sup>2 = (2*x\<^sup>2)*(2*y\<^sup>2)" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (1+a)*(1-a)" using \<open>2*x\<^sup>2=1+a\<close> \<open>2*y\<^sup>2=1-a\<close> by simp
          also have "\<dots> = 1-a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2" using hS1w by linarith
          finally have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2" .
          have hqb: "2*x*y = b"
          proof -
            have "2*x*y = b \<or> 2*x*y = -b" using h2xy_eq_b2 power2_eq_iff by (by100 blast)
            moreover have "2*x*y \<le> 0" using hx_neg hy_pos by (simp add: mult_nonpos_nonneg)
            ultimately show ?thesis using hb by linarith
          qed
          have "qi3 w \<in> V3" unfolding hqi3_w V3_def top1_S1_def using hxy_S1 hx_neg hy_pos by simp
          moreover have "q (qi3 w) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hqi3_w hab by simp
          qed
          ultimately show "qi3 w \<in> V3 \<and> q (qi3 w) = w" by (by100 blast)
        qed
        have hqi3_eq: "\<And>w. w \<in> U_bot \<Longrightarrow> qi3 w = inv_into V3 q w"
        proof -
          fix w assume hw: "w \<in> U_bot"
          have "qi3 w \<in> V3" and "q (qi3 w) = w" using hqi3_props[OF hw] by auto
          thus "qi3 w = inv_into V3 q w"
            by (simp add: inv_into_f_eq[OF inj_on_subset[OF bij_betw_imp_inj_on[OF \<open>bij_betw q V3 U_bot\<close>]]])
        qed
        have hqi3_V3: "\<And>w. w \<in> U_bot \<Longrightarrow> qi3 w \<in> V3" using hqi3_props by (by100 blast)
        have hqi3_cont: "continuous_on U_bot qi3"
          unfolding qi3_def split_def by (intro continuous_intros) auto
        have hU_sub: "U_bot \<subseteq> top1_S1" unfolding U_bot_def by (by100 blast)
        have hV3_sub: "V3 \<subseteq> top1_S1" unfolding V3_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix w assume "w \<in> U_bot"
          show "inv_into V3 q w \<in> V3" using hqi3_eq[OF \<open>w \<in> U_bot\<close>] hqi3_V3[OF \<open>w \<in> U_bot\<close>] by simp
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology V3"
          obtain W'' where hW'': "W'' \<in> product_topology_on top1_open_sets top1_open_sets"
              and hWeq: "V = V3 \<inter> (top1_S1 \<inter> W'')"
          proof -
            obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = V3 \<inter> W"
              using hV unfolding subspace_topology_def by (by100 blast)
            obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
                and hWW': "W = top1_S1 \<inter> W'"
              using hW unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
            show ?thesis using that[OF hW'] hVeq hWW' by simp
          qed
          have hW''_open: "open W''"
            using hW'' by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
          have "{w \<in> U_bot. inv_into V3 q w \<in> V} = {w \<in> U_bot. qi3 w \<in> W''}"
          proof (intro Collect_cong conj_cong refl)
            fix w assume hw: "w \<in> U_bot"
            have "inv_into V3 q w = qi3 w" using hqi3_eq[OF hw] by simp
            moreover have "qi3 w \<in> V3" using hqi3_V3[OF hw] .
            moreover have "V3 \<subseteq> top1_S1" using hV3_sub .
            ultimately show "(inv_into V3 q w \<in> V) = (qi3 w \<in> W'')" using hWeq by auto
          qed
          moreover have "{w \<in> U_bot. qi3 w \<in> W''} \<in> subspace_topology top1_S1 top1_S1_topology U_bot"
          proof -
            obtain U where hU: "open U" and hUeq: "U \<inter> U_bot = qi3 -` W'' \<inter> U_bot"
              using hqi3_cont hW''_open unfolding continuous_on_open_invariant by blast
            have "{w \<in> U_bot. qi3 w \<in> W''} = U \<inter> U_bot" using hUeq by (by100 blast)
            moreover have "U \<inter> U_bot \<in> subspace_topology top1_S1 top1_S1_topology U_bot"
            proof -
              have "U \<in> top1_open_sets" using hU unfolding top1_open_sets_def by simp
              hence "U \<in> product_topology_on top1_open_sets top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              hence "top1_S1 \<inter> U \<in> top1_S1_topology"
                unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
              moreover have "U \<inter> U_bot = U_bot \<inter> (top1_S1 \<inter> U)" using hU_sub by blast
              ultimately show ?thesis unfolding subspace_topology_def by blast
            qed
            ultimately show ?thesis by simp
          qed
          ultimately show "{w \<in> U_bot. inv_into V3 q w \<in> V}
              \<in> subspace_topology top1_S1 top1_S1_topology U_bot" by simp
        qed
      qed
    qed
    have hhomeo4: "top1_homeomorphism_on V4 (subspace_topology top1_S1 top1_S1_topology V4)
        U_bot (subspace_topology top1_S1 top1_S1_topology U_bot) q"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      have hTS1'': "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      show "is_topology_on V4 (subspace_topology top1_S1 top1_S1_topology V4)"
        by (rule subspace_topology_is_topology_on[OF hTS1'']) (use V4_def in blast)
      show "is_topology_on U_bot (subspace_topology top1_S1 top1_S1_topology U_bot)"
        by (rule subspace_topology_is_topology_on[OF hTS1'']) (use U_bot_def in blast)
      show hbij4: "bij_betw q V4 U_bot"
      proof (rule bij_betw_imageI)
        show "inj_on q V4"
        proof (rule inj_onI)
          fix p1 p2 assume hp1: "p1 \<in> V4" and hp2: "p2 \<in> V4" and heq: "q p1 = q p2"
          obtain x1 y1 where h1: "p1 = (x1, y1)" by (cases p1) auto
          obtain x2 y2 where h2: "p2 = (x2, y2)" by (cases p2) auto
          have hx1: "x1 > 0" "y1 < 0" "x1\<^sup>2 + y1\<^sup>2 = 1" using hp1 unfolding V4_def top1_S1_def h1 by auto
          have hx2: "x2 > 0" "y2 < 0" "x2\<^sup>2 + y2\<^sup>2 = 1" using hp2 unfolding V4_def top1_S1_def h2 by auto
          have "x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2" using heq unfolding q_def h1 h2 by auto
          have "x1\<^sup>2 = x2\<^sup>2"
          proof -
            have "x1\<^sup>2 = (1 + (x1\<^sup>2 - y1\<^sup>2))/2" using hx1(3) by (simp add: field_simps)
            also have "\<dots> = (1 + (x2\<^sup>2 - y2\<^sup>2))/2" using \<open>x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2\<close> by simp
            also have "\<dots> = x2\<^sup>2" using hx2(3) by (simp add: field_simps)
            finally show ?thesis .
          qed
          hence "x1 = x2" using hx1(1) hx2(1) by (simp add: power2_eq_iff_nonneg)
          moreover have "y1\<^sup>2 = y2\<^sup>2" using \<open>x1\<^sup>2 = x2\<^sup>2\<close> hx1(3) hx2(3) by linarith
          hence "y1 = y2 \<or> y1 = -y2" using power2_eq_iff by (by100 blast)
          hence "y1 = y2" using hx1(2) hx2(2) by linarith
          ultimately show "p1 = p2" unfolding h1 h2 by simp
        qed
      next
        show "q ` V4 = U_bot"
        proof (intro set_eqI iffI)
          fix w assume "w \<in> q ` V4"
          then obtain p where hp: "p \<in> V4" and hw: "w = q p" by (by100 blast)
          have "p \<in> top1_S1" "fst p > 0" "snd p < 0" using hp unfolding V4_def by auto
          have "q p \<in> top1_S1" by (rule hq_S1[OF \<open>p \<in> top1_S1\<close>])
          moreover have "snd (q p) = 2 * fst p * snd p" unfolding q_def by simp
          hence "snd (q p) < 0" using \<open>fst p > 0\<close> \<open>snd p < 0\<close> by (simp add: mult_pos_neg)
          ultimately show "w \<in> U_bot" unfolding U_bot_def using hw by simp
        next
          fix w assume hw: "w \<in> U_bot"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and hb: "b < 0" using hw unfolding U_bot_def top1_S1_def hab by auto
          have "b\<^sup>2 > 0" using hb by (simp add: power2_eq_square) (simp add: mult_neg_neg)
          hence ha2: "a\<^sup>2 < 1" using hS1w by linarith
          hence ha_bounds: "a < 1 \<and> -1 < a"
          proof -
            have "\<not> (a \<ge> 1)" proof assume "1 \<le> a"
              hence "1 \<le> a * a" using mult_mono[of 1 a 1 a] by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            moreover have "\<not> (a \<le> -1)" proof assume "a \<le> -1"
              hence "1 \<le> (-a)*(-a)" using mult_mono[of 1 "-a" 1 "-a"] by linarith
              hence "1 \<le> a*a" by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            ultimately show ?thesis by linarith
          qed
          define x where "x = sqrt ((1+a)/2)" define y where "y = -sqrt ((1-a)/2)"
          have hx_pos: "x > 0" unfolding x_def using ha_bounds by simp
          have hy_neg: "y < 0" unfolding y_def using ha_bounds by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx2 hy2 by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a" using hx2 hy2 by simp
          have "2*x\<^sup>2 = 1+a" using hx2 by auto
          have "2*y\<^sup>2 = 1-a" using hy2 by auto
          have "(2*x*y)\<^sup>2 = (2*x\<^sup>2)*(2*y\<^sup>2)" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (1+a)*(1-a)" using \<open>2*x\<^sup>2=1+a\<close> \<open>2*y\<^sup>2=1-a\<close> by simp
          also have "\<dots> = 1-a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2" using hS1w by linarith
          finally have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2" .
          have hqb: "2*x*y = b"
          proof -
            have "2*x*y = b \<or> 2*x*y = -b" using h2xy_eq_b2 power2_eq_iff by (by100 blast)
            moreover have "2*x*y \<le> 0" using hx_pos hy_neg by (simp add: mult_nonneg_nonpos)
            ultimately show ?thesis using hb by linarith
          qed
          have "(x, y) \<in> V4" unfolding V4_def top1_S1_def using hxy_S1 hx_pos hy_neg by simp
          moreover have "q (x, y) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hab by simp
          qed
          ultimately show "w \<in> q ` V4" by (by100 blast)
        qed
      qed
      show "top1_continuous_map_on V4 (subspace_topology top1_S1 top1_S1_topology V4)
          U_bot (subspace_topology top1_S1 top1_S1_topology U_bot) q"
      proof -
        have hV4_sub: "V4 \<subseteq> top1_S1" unfolding V4_def by (by100 blast)
        have hU_sub: "U_bot \<subseteq> top1_S1" unfolding U_bot_def by (by100 blast)
        have hq_V4: "top1_continuous_map_on V4 (subspace_topology top1_S1 top1_S1_topology V4)
            top1_S1 top1_S1_topology q"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hq_cont hV4_sub])
        have hq_img: "q ` V4 \<subseteq> U_bot" using hbij4 unfolding bij_betw_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> V4" thus "q p \<in> U_bot" using hq_img by (by100 blast)
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology U_bot"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = U_bot \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          have "{p \<in> V4. q p \<in> V} = {p \<in> V4. q p \<in> W}" using hq_img hVeq by (by100 blast)
          moreover have "{p \<in> V4. q p \<in> W} \<in> subspace_topology top1_S1 top1_S1_topology V4"
            using hq_V4 hW unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "{p \<in> V4. q p \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology V4" by simp
        qed
      qed
      show "top1_continuous_map_on U_bot (subspace_topology top1_S1 top1_S1_topology U_bot)
          V4 (subspace_topology top1_S1 top1_S1_topology V4) (inv_into V4 q)"
      proof -
        define qi4 where "qi4 = (\<lambda>(a::real, b::real). (sqrt ((1+a)/2), -sqrt ((1-a)/2)))"
        have hqi4_props: "\<And>w. w \<in> U_bot \<Longrightarrow> qi4 w \<in> V4 \<and> q (qi4 w) = w"
        proof -
          fix w assume hw: "w \<in> U_bot"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and hb: "b < 0" using hw unfolding U_bot_def top1_S1_def hab by auto
          have "b\<^sup>2 > 0" using hb by (simp add: power2_eq_square) (simp add: mult_neg_neg)
          hence ha2: "a\<^sup>2 < 1" using hS1w by linarith
          hence ha_bounds: "a < 1 \<and> -1 < a"
          proof -
            have "\<not> (a \<ge> 1)" proof assume "1 \<le> a"
              hence "1 \<le> a * a" using mult_mono[of 1 a 1 a] by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            moreover have "\<not> (a \<le> -1)" proof assume "a \<le> -1"
              hence "1 \<le> (-a)*(-a)" using mult_mono[of 1 "-a" 1 "-a"] by linarith
              hence "1 \<le> a*a" by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            ultimately show ?thesis by linarith
          qed
          define x where "x = sqrt ((1+a)/2)" define y where "y = -sqrt ((1-a)/2)"
          have hqi4_w: "qi4 w = (x, y)" unfolding qi4_def hab x_def y_def by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hx_pos: "x > 0" unfolding x_def using ha_bounds by simp
          have hy_neg: "y < 0" unfolding y_def using ha_bounds by simp
          have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx2 hy2 by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a" using hx2 hy2 by simp
          have "2*x\<^sup>2 = 1+a" using hx2 by auto
          have "2*y\<^sup>2 = 1-a" using hy2 by auto
          have "(2*x*y)\<^sup>2 = (2*x\<^sup>2)*(2*y\<^sup>2)" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (1+a)*(1-a)" using \<open>2*x\<^sup>2=1+a\<close> \<open>2*y\<^sup>2=1-a\<close> by simp
          also have "\<dots> = 1-a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2" using hS1w by linarith
          finally have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2" .
          have hqb: "2*x*y = b"
          proof -
            have "2*x*y = b \<or> 2*x*y = -b" using h2xy_eq_b2 power2_eq_iff by (by100 blast)
            moreover have "2*x*y \<le> 0" using hx_pos hy_neg by (simp add: mult_nonneg_nonpos)
            ultimately show ?thesis using hb by linarith
          qed
          have "qi4 w \<in> V4" unfolding hqi4_w V4_def top1_S1_def using hxy_S1 hx_pos hy_neg by simp
          moreover have "q (qi4 w) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hqi4_w hab by simp
          qed
          ultimately show "qi4 w \<in> V4 \<and> q (qi4 w) = w" by (by100 blast)
        qed
        have hqi4_eq: "\<And>w. w \<in> U_bot \<Longrightarrow> qi4 w = inv_into V4 q w"
        proof -
          fix w assume hw: "w \<in> U_bot"
          have "qi4 w \<in> V4" and "q (qi4 w) = w" using hqi4_props[OF hw] by auto
          thus "qi4 w = inv_into V4 q w"
            by (simp add: inv_into_f_eq[OF inj_on_subset[OF bij_betw_imp_inj_on[OF hbij4]]])
        qed
        have hqi4_V4: "\<And>w. w \<in> U_bot \<Longrightarrow> qi4 w \<in> V4" using hqi4_props by (by100 blast)
        have hqi4_cont: "continuous_on U_bot qi4"
          unfolding qi4_def split_def by (intro continuous_intros) auto
        have hU_sub: "U_bot \<subseteq> top1_S1" unfolding U_bot_def by (by100 blast)
        have hV4_sub: "V4 \<subseteq> top1_S1" unfolding V4_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix w assume "w \<in> U_bot"
          show "inv_into V4 q w \<in> V4" using hqi4_eq[OF \<open>w \<in> U_bot\<close>] hqi4_V4[OF \<open>w \<in> U_bot\<close>] by simp
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology V4"
          obtain W'' where hW'': "W'' \<in> product_topology_on top1_open_sets top1_open_sets"
              and hWeq: "V = V4 \<inter> (top1_S1 \<inter> W'')"
          proof -
            obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = V4 \<inter> W"
              using hV unfolding subspace_topology_def by (by100 blast)
            obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
                and hWW': "W = top1_S1 \<inter> W'"
              using hW unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
            show ?thesis using that[OF hW'] hVeq hWW' by simp
          qed
          have hW''_open: "open W''"
            using hW'' by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
          have "{w \<in> U_bot. inv_into V4 q w \<in> V} = {w \<in> U_bot. qi4 w \<in> W''}"
          proof (intro Collect_cong conj_cong refl)
            fix w assume hw: "w \<in> U_bot"
            have "inv_into V4 q w = qi4 w" using hqi4_eq[OF hw] by simp
            moreover have "qi4 w \<in> V4" using hqi4_V4[OF hw] .
            moreover have "V4 \<subseteq> top1_S1" using hV4_sub .
            ultimately show "(inv_into V4 q w \<in> V) = (qi4 w \<in> W'')" using hWeq by auto
          qed
          moreover have "{w \<in> U_bot. qi4 w \<in> W''} \<in> subspace_topology top1_S1 top1_S1_topology U_bot"
          proof -
            obtain U where hU: "open U" and hUeq: "U \<inter> U_bot = qi4 -` W'' \<inter> U_bot"
              using hqi4_cont hW''_open unfolding continuous_on_open_invariant by blast
            have "{w \<in> U_bot. qi4 w \<in> W''} = U \<inter> U_bot" using hUeq by (by100 blast)
            moreover have "U \<inter> U_bot \<in> subspace_topology top1_S1 top1_S1_topology U_bot"
            proof -
              have "U \<in> top1_open_sets" using hU unfolding top1_open_sets_def by simp
              hence "U \<in> product_topology_on top1_open_sets top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              hence "top1_S1 \<inter> U \<in> top1_S1_topology"
                unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
              moreover have "U \<inter> U_bot = U_bot \<inter> (top1_S1 \<inter> U)" using hU_sub by blast
              ultimately show ?thesis unfolding subspace_topology_def by blast
            qed
            ultimately show ?thesis by simp
          qed
          ultimately show "{w \<in> U_bot. inv_into V4 q w \<in> V}
              \<in> subspace_topology top1_S1 top1_S1_topology U_bot" by simp
        qed
      qed
    qed
    show ?thesis unfolding top1_evenly_covered_on_def
    proof (intro conjI exI[of _ "{V3, V4}"])
      show "openin_on top1_S1 top1_S1_topology U_bot" by (rule hU_bot_open)
      show "\<forall>V\<in>{V3, V4}. openin_on top1_S1 top1_S1_topology V" using hV3_open hV4_open by (by100 blast)
      show "\<forall>V\<in>{V3, V4}. \<forall>V'\<in>{V3, V4}. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}" using hV_disj by (by100 blast)
      show "{x \<in> top1_S1. q x \<in> U_bot} = \<Union> {V3, V4}" using hpreimage by simp
      show "\<forall>V\<in>{V3, V4}. top1_homeomorphism_on V (subspace_topology top1_S1 top1_S1_topology V)
          U_bot (subspace_topology top1_S1 top1_S1_topology U_bot) q"
        using hhomeo3 hhomeo4 by (by100 blast)
    qed
  qed
  have hevenly_right: "top1_evenly_covered_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q U_right"
  proof -
    have hU_right_open: "openin_on top1_S1 top1_S1_topology U_right"
    proof -
      have "open {p :: real \<times> real. fst p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      hence "{p :: real \<times> real. fst p > 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p > 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p > 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p > 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "U_right = top1_S1 \<inter> {p. fst p > 0}" unfolding U_right_def by (by100 blast)
      moreover have "U_right \<subseteq> top1_S1" unfolding U_right_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    \<comment> \<open>V5 = {x+y>0, x-y>0} \<inter> S^1 (arc near (1,0)), V6 = {x+y<0, x-y<0} \<inter> S^1 (arc near (-1,0)).\<close>
    define V5 where "V5 = {p \<in> top1_S1. fst p + snd p > 0 \<and> fst p - snd p > 0}"
    define V6 where "V6 = {p \<in> top1_S1. fst p + snd p < 0 \<and> fst p - snd p < 0}"
    have hV5_open: "openin_on top1_S1 top1_S1_topology V5"
    proof -
      have h1: "open {p :: real \<times> real. fst p + snd p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have h2: "open {p :: real \<times> real. fst p - snd p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have "open {p :: real \<times> real. fst p + snd p > 0 \<and> fst p - snd p > 0}"
        using open_Int[OF h1 h2] by (auto simp: Int_def)
      hence "{p :: real \<times> real. fst p + snd p > 0 \<and> fst p - snd p > 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p + snd p > 0 \<and> fst p - snd p > 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p + snd p > 0 \<and> fst p - snd p > 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p + snd p > 0 \<and> fst p - snd p > 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "V5 = top1_S1 \<inter> {p. fst p + snd p > 0 \<and> fst p - snd p > 0}" unfolding V5_def by (by100 blast)
      moreover have "V5 \<subseteq> top1_S1" unfolding V5_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    have hV6_open: "openin_on top1_S1 top1_S1_topology V6"
    proof -
      have h1: "open {p :: real \<times> real. fst p + snd p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have h2: "open {p :: real \<times> real. fst p - snd p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have "open {p :: real \<times> real. fst p + snd p < 0 \<and> fst p - snd p < 0}"
        using open_Int[OF h1 h2] by (auto simp: Int_def)
      hence "{p :: real \<times> real. fst p + snd p < 0 \<and> fst p - snd p < 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p + snd p < 0 \<and> fst p - snd p < 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p + snd p < 0 \<and> fst p - snd p < 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p + snd p < 0 \<and> fst p - snd p < 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "V6 = top1_S1 \<inter> {p. fst p + snd p < 0 \<and> fst p - snd p < 0}" unfolding V6_def by (by100 blast)
      moreover have "V6 \<subseteq> top1_S1" unfolding V6_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    have hV_disj: "V5 \<inter> V6 = {}" unfolding V5_def V6_def by auto
    have hpreimage: "{p \<in> top1_S1. q p \<in> U_right} = V5 \<union> V6"
    proof (intro set_eqI iffI)
      fix p assume hp: "p \<in> {p \<in> top1_S1. q p \<in> U_right}"
      hence hpS1: "p \<in> top1_S1" and hqp: "q p \<in> U_right" by auto
      obtain x y where hxy: "p = (x, y)" by (cases p) auto
      have hS1: "x\<^sup>2 + y\<^sup>2 = 1" using hpS1 unfolding top1_S1_def hxy by simp
      have "fst (q p) > 0" using hqp unfolding U_right_def by (by100 blast)
      hence "x\<^sup>2 - y\<^sup>2 > 0" unfolding q_def hxy by (simp add: power2_eq_square)
      \<comment> \<open>x^2-y^2 = (x+y)(x-y) > 0 iff both same sign.\<close>
      hence "(x+y)*(x-y) > 0" by (simp add: power2_eq_square algebra_simps)
      hence "(x+y > 0 \<and> x-y > 0) \<or> (x+y < 0 \<and> x-y < 0)" using zero_less_mult_iff by force
      thus "p \<in> V5 \<union> V6" unfolding V5_def V6_def using hpS1 hxy by auto
    next
      fix p assume "p \<in> V5 \<union> V6"
      hence hpS1: "p \<in> top1_S1" and hq: "(fst p + snd p) * (fst p - snd p) > 0"
        unfolding V5_def V6_def by (auto intro: mult_pos_pos mult_neg_neg)
      have "fst (q p) = fst p ^ 2 - snd p ^ 2" unfolding q_def by simp
      also have "\<dots> = (fst p + snd p) * (fst p - snd p)" by (simp add: power2_eq_square algebra_simps)
      finally have "fst (q p) > 0" using hq by simp
      moreover have "q p \<in> top1_S1" by (rule hq_S1[OF hpS1])
      ultimately show "p \<in> {p \<in> top1_S1. q p \<in> U_right}" unfolding U_right_def using hpS1 by auto
    qed
    \<comment> \<open>Homeomorphisms V5 \<rightarrow> U_right and V6 \<rightarrow> U_right.\<close>
    \<comment> \<open>Homeomorphisms: same pattern as previous cases. Inverse for V5: (a,b) \<mapsto> (sqrt((1+a)/2), b/(2*sqrt((1+a)/2))).
       For V6: negate both components.\<close>
    have hhomeo5: "top1_homeomorphism_on V5 (subspace_topology top1_S1 top1_S1_topology V5)
        U_right (subspace_topology top1_S1 top1_S1_topology U_right) q"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      have hTS1r: "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      show "is_topology_on V5 (subspace_topology top1_S1 top1_S1_topology V5)"
        by (rule subspace_topology_is_topology_on[OF hTS1r]) (use V5_def in blast)
      show "is_topology_on U_right (subspace_topology top1_S1 top1_S1_topology U_right)"
        by (rule subspace_topology_is_topology_on[OF hTS1r]) (use U_right_def in blast)
      show hbij5: "bij_betw q V5 U_right"
      proof (rule bij_betw_imageI)
        show "inj_on q V5"
        proof (rule inj_onI)
          fix p1 p2 assume hp1: "p1 \<in> V5" and hp2: "p2 \<in> V5" and heq: "q p1 = q p2"
          obtain x1 y1 where h1: "p1 = (x1, y1)" by (cases p1) auto
          obtain x2 y2 where h2: "p2 = (x2, y2)" by (cases p2) auto
          have hx1: "x1 + y1 > 0" "x1 - y1 > 0" "x1\<^sup>2 + y1\<^sup>2 = 1"
            using hp1 unfolding V5_def top1_S1_def h1 by auto
          have hx2: "x2 + y2 > 0" "x2 - y2 > 0" "x2\<^sup>2 + y2\<^sup>2 = 1"
            using hp2 unfolding V5_def top1_S1_def h2 by auto
          have "x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2" using heq unfolding q_def h1 h2 by auto
          have "x1\<^sup>2 = x2\<^sup>2"
          proof -
            have "x1\<^sup>2 = (1 + (x1\<^sup>2 - y1\<^sup>2))/2" using hx1(3) by (simp add: field_simps)
            also have "\<dots> = (1 + (x2\<^sup>2 - y2\<^sup>2))/2" using \<open>x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2\<close> by simp
            also have "\<dots> = x2\<^sup>2" using hx2(3) by (simp add: field_simps)
            finally show ?thesis .
          qed
          moreover have "2*x1*y1 = 2*x2*y2" using heq unfolding q_def h1 h2 by auto
          hence "x1*y1 = x2*y2" by simp
          \<comment> \<open>x1^2 = x2^2 and x1 > 0 (since x1+y1>0 and x1-y1>0 imply x1>0).\<close>
          moreover have "x1 > 0" using hx1(1) hx1(2) by linarith
          moreover have "x2 > 0" using hx2(1) hx2(2) by linarith
          ultimately have "x1 = x2" by (simp add: power2_eq_iff_nonneg)
          moreover have "y1 = y2"
          proof -
            have "y1\<^sup>2 = y2\<^sup>2" using \<open>x1\<^sup>2 = x2\<^sup>2\<close> hx1(3) hx2(3) by linarith
            moreover have "x1*y1 = x1*y2" using \<open>x1*y1 = x2*y2\<close> \<open>x1 = x2\<close> by simp
            hence "y1 = y2" using \<open>x1 > 0\<close> by simp
            thus ?thesis .
          qed
          ultimately show "p1 = p2" unfolding h1 h2 by simp
        qed
      next
        show "q ` V5 = U_right"
        proof (intro set_eqI iffI)
          fix w assume "w \<in> q ` V5"
          then obtain p where hp: "p \<in> V5" and hw: "w = q p" by (by100 blast)
          have "p \<in> top1_S1" using hp unfolding V5_def by auto
          obtain x y where hxy: "p = (x, y)" by (cases p) auto
          have "x + y > 0" "x - y > 0" using hp unfolding V5_def hxy by auto
          hence "(x+y)*(x-y) > 0" by (simp add: mult_pos_pos)
          hence "x\<^sup>2 - y\<^sup>2 > 0" by (simp add: power2_eq_square algebra_simps)
          hence "fst (q p) > 0" unfolding q_def hxy by (simp add: power2_eq_square)
          moreover have "q p \<in> top1_S1" by (rule hq_S1[OF \<open>p \<in> top1_S1\<close>])
          ultimately show "w \<in> U_right" unfolding U_right_def using hw by simp
        next
          fix w assume hw: "w \<in> U_right"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and ha: "a > 0" using hw unfolding U_right_def top1_S1_def hab by auto
          define x where "x = sqrt ((1+a)/2)" define y where "y = b / (2 * sqrt ((1+a)/2))"
          have hx_pos: "x > 0" unfolding x_def using ha by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha by (simp add: real_sqrt_mult_self)
          \<comment> \<open>y = b/(2x). Then 2xy = b. And x^2+y^2 = (1+a)/2 + b^2/(4*(1+a)/2) = (1+a)/2 + b^2/(2(1+a)).\<close>
          have hx_eq: "2*x = 2*sqrt((1+a)/2)" unfolding x_def by simp
          have h2x_pos: "2*x > 0" using hx_pos by simp
          have hqb: "2*x*y = b"
          proof -
            have "sqrt ((1+a)/2) > 0" using ha by simp
            hence "2 * sqrt ((1+a)/2) \<noteq> 0" by simp
            thus ?thesis unfolding y_def x_def by simp
          qed
          \<comment> \<open>x^2+y^2=1: from (2xy)^2=b^2 and x^2=(1+a)/2.\<close>
          have "4*x\<^sup>2*(x\<^sup>2 + y\<^sup>2) = 4*x\<^sup>2*x\<^sup>2 + (2*x*y)\<^sup>2"
            by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (2*x\<^sup>2)\<^sup>2 + b\<^sup>2" using hqb by (simp add: power2_eq_square algebra_simps)
          also have "2*x\<^sup>2 = 1+a" using hx2 by auto
          also have "(1+a)\<^sup>2 + b\<^sup>2 = 1 + 2*a + a\<^sup>2 + b\<^sup>2" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = 2 + 2*a" using hS1w by linarith
          also have "\<dots> = 2*(1+a)" by simp
          also have "\<dots> = 4*x\<^sup>2" using hx2 by auto
          finally have "4*x\<^sup>2*(x\<^sup>2+y\<^sup>2) = 4*x\<^sup>2" .
          hence hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx_pos by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            hence "x\<^sup>2 - y\<^sup>2 = 2*x\<^sup>2 - 1" using hxy_S1 by linarith
            also have "\<dots> = a" using \<open>2*x\<^sup>2 = 1+a\<close> by linarith
            finally show ?thesis .
          qed
          \<comment> \<open>(x,y) \<in> V5: need x+y > 0 and x-y > 0.\<close>
          have "x + y > 0 \<and> x - y > 0"
          proof -
            have "(x+y)*(x-y) = x\<^sup>2 - y\<^sup>2" by (simp add: power2_eq_square algebra_simps)
            hence "(x+y)*(x-y) = a" using hqa by simp
            hence "(x+y)*(x-y) > 0" using ha by simp
            hence "(x+y > 0 \<and> x-y > 0) \<or> (x+y < 0 \<and> x-y < 0)"
              using zero_less_mult_iff by force
            moreover have "x + y > 0 \<or> x - y > 0" using hx_pos by linarith
            ultimately show ?thesis by linarith
          qed
          hence "(x, y) \<in> V5" unfolding V5_def top1_S1_def using hxy_S1 by simp
          moreover have "q (x, y) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hab by simp
          qed
          ultimately show "w \<in> q ` V5" by (by100 blast)
        qed
      qed
      \<comment> \<open>Forward and inverse continuity: same pattern as previous cases.\<close>
      show "top1_continuous_map_on V5 (subspace_topology top1_S1 top1_S1_topology V5)
          U_right (subspace_topology top1_S1 top1_S1_topology U_right) q"
      proof -
        have hV5_sub: "V5 \<subseteq> top1_S1" unfolding V5_def by (by100 blast)
        have hU_sub: "U_right \<subseteq> top1_S1" unfolding U_right_def by (by100 blast)
        have hq_V5: "top1_continuous_map_on V5 (subspace_topology top1_S1 top1_S1_topology V5)
            top1_S1 top1_S1_topology q"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hq_cont hV5_sub])
        have hq_img: "q ` V5 \<subseteq> U_right" using hbij5 unfolding bij_betw_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> V5" thus "q p \<in> U_right" using hq_img by (by100 blast)
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology U_right"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = U_right \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          have "{p \<in> V5. q p \<in> V} = {p \<in> V5. q p \<in> W}" using hq_img hVeq by (by100 blast)
          moreover have "{p \<in> V5. q p \<in> W} \<in> subspace_topology top1_S1 top1_S1_topology V5"
            using hq_V5 hW unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "{p \<in> V5. q p \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology V5" by simp
        qed
      qed
      show "top1_continuous_map_on U_right (subspace_topology top1_S1 top1_S1_topology U_right)
          V5 (subspace_topology top1_S1 top1_S1_topology V5) (inv_into V5 q)"
      proof -
        define qi5 where "qi5 = (\<lambda>(a::real, b::real). (sqrt ((1+a)/2), b / (2 * sqrt ((1+a)/2))))"
        have hqi5_props: "\<And>w. w \<in> U_right \<Longrightarrow> qi5 w \<in> V5 \<and> q (qi5 w) = w"
        proof -
          fix w assume hw: "w \<in> U_right"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and ha: "a > 0" using hw unfolding U_right_def top1_S1_def hab by auto
          define x where "x = sqrt ((1+a)/2)" define y where "y = b / (2 * sqrt ((1+a)/2))"
          have hqi5_w: "qi5 w = (x, y)" unfolding qi5_def hab x_def y_def by simp
          have hx_pos: "x > 0" unfolding x_def using ha by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha by (simp add: real_sqrt_mult_self)
          have hqb: "2*x*y = b"
          proof -
            have "sqrt ((1+a)/2) > 0" using ha by simp
            hence "2 * sqrt ((1+a)/2) \<noteq> 0" by simp
            thus ?thesis unfolding y_def x_def by simp
          qed
          have "4*x\<^sup>2*(x\<^sup>2 + y\<^sup>2) = (2*x\<^sup>2)\<^sup>2 + (2*x*y)\<^sup>2"
            by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (1+a)\<^sup>2 + b\<^sup>2"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis using hqb by simp
          qed
          also have "\<dots> = 2 + 2*a"
            using hS1w by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = 4*x\<^sup>2"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis by linarith
          qed
          finally have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx_pos by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis using hxy_S1 by linarith
          qed
          have "x + y > 0 \<and> x - y > 0"
          proof -
            have "(x+y)*(x-y) = a" by (simp add: power2_eq_square algebra_simps) (use hqa in \<open>simp add: power2_eq_square algebra_simps\<close>)
            hence "(x+y)*(x-y) > 0" using ha by simp
            hence "(x+y > 0 \<and> x-y > 0) \<or> (x+y < 0 \<and> x-y < 0)"
              using zero_less_mult_iff by force
            moreover have "x + y > 0 \<or> x - y > 0" using hx_pos by linarith
            ultimately show ?thesis by linarith
          qed
          have "qi5 w \<in> V5" unfolding hqi5_w V5_def top1_S1_def using hxy_S1 \<open>x+y>0 \<and> x-y>0\<close> by simp
          moreover have "q (qi5 w) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hqi5_w hab by simp
          qed
          ultimately show "qi5 w \<in> V5 \<and> q (qi5 w) = w" by (by100 blast)
        qed
        have hqi5_eq: "\<And>w. w \<in> U_right \<Longrightarrow> qi5 w = inv_into V5 q w"
        proof -
          fix w assume hw: "w \<in> U_right"
          have "qi5 w \<in> V5" and "q (qi5 w) = w" using hqi5_props[OF hw] by auto
          thus "qi5 w = inv_into V5 q w"
            by (simp add: inv_into_f_eq[OF inj_on_subset[OF bij_betw_imp_inj_on[OF hbij5]]])
        qed
        have hqi5_V5: "\<And>w. w \<in> U_right \<Longrightarrow> qi5 w \<in> V5" using hqi5_props by (by100 blast)
        have hqi5_cont: "continuous_on U_right qi5"
          unfolding qi5_def split_def
          by (intro continuous_intros continuous_on_divide)
             (auto simp: U_right_def top1_S1_def)
        have hU_sub: "U_right \<subseteq> top1_S1" unfolding U_right_def by (by100 blast)
        have hV5_sub: "V5 \<subseteq> top1_S1" unfolding V5_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix w assume "w \<in> U_right"
          show "inv_into V5 q w \<in> V5" using hqi5_eq[OF \<open>w \<in> U_right\<close>] hqi5_V5[OF \<open>w \<in> U_right\<close>] by simp
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology V5"
          obtain W'' where hW'': "W'' \<in> product_topology_on top1_open_sets top1_open_sets"
              and hWeq: "V = V5 \<inter> (top1_S1 \<inter> W'')"
          proof -
            obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = V5 \<inter> W"
              using hV unfolding subspace_topology_def by (by100 blast)
            obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
                and hWW': "W = top1_S1 \<inter> W'"
              using hW unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
            show ?thesis using that[OF hW'] hVeq hWW' by simp
          qed
          have hW''_open: "open W''"
            using hW'' by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
          have "{w \<in> U_right. inv_into V5 q w \<in> V} = {w \<in> U_right. qi5 w \<in> W''}"
          proof (intro Collect_cong conj_cong refl)
            fix w assume hw: "w \<in> U_right"
            have "inv_into V5 q w = qi5 w" using hqi5_eq[OF hw] by simp
            moreover have "qi5 w \<in> V5" using hqi5_V5[OF hw] .
            moreover have "V5 \<subseteq> top1_S1" using hV5_sub .
            ultimately show "(inv_into V5 q w \<in> V) = (qi5 w \<in> W'')" using hWeq by auto
          qed
          moreover have "{w \<in> U_right. qi5 w \<in> W''} \<in> subspace_topology top1_S1 top1_S1_topology U_right"
          proof -
            obtain U where hU: "open U" and hUeq: "U \<inter> U_right = qi5 -` W'' \<inter> U_right"
              using hqi5_cont hW''_open unfolding continuous_on_open_invariant by blast
            have "{w \<in> U_right. qi5 w \<in> W''} = U \<inter> U_right" using hUeq by (by100 blast)
            moreover have "U \<inter> U_right \<in> subspace_topology top1_S1 top1_S1_topology U_right"
            proof -
              have "U \<in> top1_open_sets" using hU unfolding top1_open_sets_def by simp
              hence "U \<in> product_topology_on top1_open_sets top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              hence "top1_S1 \<inter> U \<in> top1_S1_topology"
                unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
              moreover have "U \<inter> U_right = U_right \<inter> (top1_S1 \<inter> U)" using hU_sub by blast
              ultimately show ?thesis unfolding subspace_topology_def by blast
            qed
            ultimately show ?thesis by simp
          qed
          ultimately show "{w \<in> U_right. inv_into V5 q w \<in> V}
              \<in> subspace_topology top1_S1 top1_S1_topology U_right" by simp
        qed
      qed
    qed
    have hhomeo6: "top1_homeomorphism_on V6 (subspace_topology top1_S1 top1_S1_topology V6)
        U_right (subspace_topology top1_S1 top1_S1_topology U_right) q"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      have hTS1rr: "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      show "is_topology_on V6 (subspace_topology top1_S1 top1_S1_topology V6)"
        by (rule subspace_topology_is_topology_on[OF hTS1rr]) (use V6_def in blast)
      show "is_topology_on U_right (subspace_topology top1_S1 top1_S1_topology U_right)"
        by (rule subspace_topology_is_topology_on[OF hTS1rr]) (use U_right_def in blast)
      show hbij6: "bij_betw q V6 U_right"
      proof (rule bij_betw_imageI)
        show "inj_on q V6"
        proof (rule inj_onI)
          fix p1 p2 assume hp1: "p1 \<in> V6" and hp2: "p2 \<in> V6" and heq: "q p1 = q p2"
          obtain x1 y1 where h1: "p1 = (x1, y1)" by (cases p1) auto
          obtain x2 y2 where h2: "p2 = (x2, y2)" by (cases p2) auto
          have hx1: "x1 + y1 < 0" "x1 - y1 < 0" "x1\<^sup>2 + y1\<^sup>2 = 1" using hp1 unfolding V6_def top1_S1_def h1 by auto
          have hx2: "x2 + y2 < 0" "x2 - y2 < 0" "x2\<^sup>2 + y2\<^sup>2 = 1" using hp2 unfolding V6_def top1_S1_def h2 by auto
          have "x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2" using heq unfolding q_def h1 h2 by auto
          have "x1\<^sup>2 = x2\<^sup>2"
          proof -
            have "x1\<^sup>2 = (1 + (x1\<^sup>2 - y1\<^sup>2))/2" using hx1(3) by (simp add: field_simps)
            also have "\<dots> = (1 + (x2\<^sup>2 - y2\<^sup>2))/2" using \<open>x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2\<close> by simp
            also have "\<dots> = x2\<^sup>2" using hx2(3) by (simp add: field_simps)
            finally show ?thesis .
          qed
          have "2*x1*y1 = 2*x2*y2" using heq unfolding q_def h1 h2 by auto
          hence "x1*y1 = x2*y2" by simp
          have "x1 < 0" using hx1(1) hx1(2) by linarith
          have "x2 < 0" using hx2(1) hx2(2) by linarith
          hence "x1 = x2 \<or> x1 = -x2" using \<open>x1\<^sup>2 = x2\<^sup>2\<close> power2_eq_iff by (by100 blast)
          hence "x1 = x2" using \<open>x1 < 0\<close> \<open>x2 < 0\<close> by linarith
          moreover have "y1 = y2" using \<open>x1*y1 = x2*y2\<close> \<open>x1 = x2\<close> \<open>x1 < 0\<close> by simp
          ultimately show "p1 = p2" unfolding h1 h2 by simp
        qed
      next
        show "q ` V6 = U_right"
        proof (intro set_eqI iffI)
          fix w assume "w \<in> q ` V6"
          then obtain p where hp: "p \<in> V6" and hw: "w = q p" by (by100 blast)
          have "p \<in> top1_S1" using hp unfolding V6_def by auto
          obtain x y where hxy: "p = (x, y)" by (cases p) auto
          have "x + y < 0" "x - y < 0" using hp unfolding V6_def hxy by auto
          hence "(x+y)*(x-y) > 0" by (simp add: mult_neg_neg)
          hence "x\<^sup>2 - y\<^sup>2 > 0" by (simp add: power2_eq_square algebra_simps)
          hence "fst (q p) > 0" unfolding q_def hxy by (simp add: power2_eq_square)
          moreover have "q p \<in> top1_S1" by (rule hq_S1[OF \<open>p \<in> top1_S1\<close>])
          ultimately show "w \<in> U_right" unfolding U_right_def using hw by simp
        next
          fix w assume hw: "w \<in> U_right"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and ha: "a > 0" using hw unfolding U_right_def top1_S1_def hab by auto
          define x where "x = -sqrt ((1+a)/2)" define y where "y = -b / (2 * sqrt ((1+a)/2))"
          have hx_neg: "x < 0" unfolding x_def using ha by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha by (simp add: real_sqrt_mult_self)
          have hqb: "2*x*y = b"
          proof -
            have "sqrt ((1+a)/2) > 0" using ha by simp
            hence "2 * sqrt ((1+a)/2) \<noteq> 0" by simp
            thus ?thesis unfolding y_def x_def by (simp add: field_simps)
          qed
          have "4*x\<^sup>2*(x\<^sup>2 + y\<^sup>2) = (2*x\<^sup>2)\<^sup>2 + (2*x*y)\<^sup>2"
            by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (1+a)\<^sup>2 + b\<^sup>2"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis using hqb by simp
          qed
          also have "\<dots> = 2 + 2*a" using hS1w by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = 4*x\<^sup>2"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis by linarith
          qed
          finally have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx_neg by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis using hxy_S1 by linarith
          qed
          have "x + y < 0 \<and> x - y < 0"
          proof -
            have "(x+y)*(x-y) = a" by (simp add: power2_eq_square algebra_simps) (use hqa in \<open>simp add: power2_eq_square algebra_simps\<close>)
            hence "(x+y)*(x-y) > 0" using ha by simp
            hence "(x+y > 0 \<and> x-y > 0) \<or> (x+y < 0 \<and> x-y < 0)" using zero_less_mult_iff by force
            moreover have "x + y < 0 \<or> x - y < 0" using hx_neg by linarith
            ultimately show ?thesis by linarith
          qed
          have "(x, y) \<in> V6" unfolding V6_def top1_S1_def using hxy_S1 \<open>x+y<0 \<and> x-y<0\<close> by simp
          moreover have "q (x, y) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hab by simp
          qed
          ultimately show "w \<in> q ` V6" by (by100 blast)
        qed
      qed
      show "top1_continuous_map_on V6 (subspace_topology top1_S1 top1_S1_topology V6)
          U_right (subspace_topology top1_S1 top1_S1_topology U_right) q"
      proof -
        have hV6_sub: "V6 \<subseteq> top1_S1" unfolding V6_def by (by100 blast)
        have hU_sub: "U_right \<subseteq> top1_S1" unfolding U_right_def by (by100 blast)
        have hq_V6: "top1_continuous_map_on V6 (subspace_topology top1_S1 top1_S1_topology V6)
            top1_S1 top1_S1_topology q"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hq_cont hV6_sub])
        have hq_img: "q ` V6 \<subseteq> U_right" using hbij6 unfolding bij_betw_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> V6" thus "q p \<in> U_right" using hq_img by (by100 blast)
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology U_right"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = U_right \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          have "{p \<in> V6. q p \<in> V} = {p \<in> V6. q p \<in> W}" using hq_img hVeq by (by100 blast)
          moreover have "{p \<in> V6. q p \<in> W} \<in> subspace_topology top1_S1 top1_S1_topology V6"
            using hq_V6 hW unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "{p \<in> V6. q p \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology V6" by simp
        qed
      qed
      show "top1_continuous_map_on U_right (subspace_topology top1_S1 top1_S1_topology U_right)
          V6 (subspace_topology top1_S1 top1_S1_topology V6) (inv_into V6 q)"
      proof -
        define qi6 where "qi6 = (\<lambda>(a::real, b::real). (-sqrt ((1+a)/2), -b / (2 * sqrt ((1+a)/2))))"
        have hqi6_props: "\<And>w. w \<in> U_right \<Longrightarrow> qi6 w \<in> V6 \<and> q (qi6 w) = w"
        proof -
          fix w assume hw: "w \<in> U_right"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and ha: "a > 0" using hw unfolding U_right_def top1_S1_def hab by auto
          define x where "x = -sqrt ((1+a)/2)" define y where "y = -b / (2 * sqrt ((1+a)/2))"
          have hqi6_w: "qi6 w = (x, y)" unfolding qi6_def hab x_def y_def by simp
          have hx_neg: "x < 0" unfolding x_def using ha by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha by (simp add: real_sqrt_mult_self)
          have hqb: "2*x*y = b"
          proof -
            have "sqrt ((1+a)/2) > 0" using ha by simp
            hence "2 * sqrt ((1+a)/2) \<noteq> 0" by simp
            thus ?thesis unfolding y_def x_def by (simp add: field_simps)
          qed
          have "4*x\<^sup>2*(x\<^sup>2 + y\<^sup>2) = (2*x\<^sup>2)\<^sup>2 + (2*x*y)\<^sup>2"
            by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (1+a)\<^sup>2 + b\<^sup>2"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis using hqb by simp
          qed
          also have "\<dots> = 2 + 2*a" using hS1w by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = 4*x\<^sup>2"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis by linarith
          qed
          finally have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx_neg by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis using hxy_S1 by linarith
          qed
          have "x + y < 0 \<and> x - y < 0"
          proof -
            have "(x+y)*(x-y) = a" by (simp add: power2_eq_square algebra_simps)
              (use hqa in \<open>simp add: power2_eq_square algebra_simps\<close>)
            hence "(x+y)*(x-y) > 0" using ha by simp
            hence "(x+y > 0 \<and> x-y > 0) \<or> (x+y < 0 \<and> x-y < 0)" using zero_less_mult_iff by force
            moreover have "x + y < 0 \<or> x - y < 0" using hx_neg by linarith
            ultimately show ?thesis by linarith
          qed
          have "qi6 w \<in> V6" unfolding hqi6_w V6_def top1_S1_def using hxy_S1 \<open>x+y<0 \<and> x-y<0\<close> by simp
          moreover have "q (qi6 w) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hqi6_w hab by simp
          qed
          ultimately show "qi6 w \<in> V6 \<and> q (qi6 w) = w" by (by100 blast)
        qed
        have hqi6_eq: "\<And>w. w \<in> U_right \<Longrightarrow> qi6 w = inv_into V6 q w"
        proof -
          fix w assume hw: "w \<in> U_right"
          have "qi6 w \<in> V6" and "q (qi6 w) = w" using hqi6_props[OF hw] by auto
          thus "qi6 w = inv_into V6 q w"
            by (simp add: inv_into_f_eq[OF inj_on_subset[OF bij_betw_imp_inj_on[OF hbij6]]])
        qed
        have hqi6_V6: "\<And>w. w \<in> U_right \<Longrightarrow> qi6 w \<in> V6" using hqi6_props by (by100 blast)
        have hqi6_cont: "continuous_on U_right qi6"
          unfolding qi6_def split_def
          by (intro continuous_intros continuous_on_divide)
             (auto simp: U_right_def top1_S1_def)
        have hU_sub: "U_right \<subseteq> top1_S1" unfolding U_right_def by (by100 blast)
        have hV6_sub: "V6 \<subseteq> top1_S1" unfolding V6_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix w assume "w \<in> U_right"
          show "inv_into V6 q w \<in> V6" using hqi6_eq[OF \<open>w \<in> U_right\<close>] hqi6_V6[OF \<open>w \<in> U_right\<close>] by simp
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology V6"
          obtain W'' where hW'': "W'' \<in> product_topology_on top1_open_sets top1_open_sets"
              and hWeq: "V = V6 \<inter> (top1_S1 \<inter> W'')"
          proof -
            obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = V6 \<inter> W"
              using hV unfolding subspace_topology_def by (by100 blast)
            obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
                and hWW': "W = top1_S1 \<inter> W'"
              using hW unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
            show ?thesis using that[OF hW'] hVeq hWW' by simp
          qed
          have hW''_open: "open W''"
            using hW'' by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
          have "{w \<in> U_right. inv_into V6 q w \<in> V} = {w \<in> U_right. qi6 w \<in> W''}"
          proof (intro Collect_cong conj_cong refl)
            fix w assume hw: "w \<in> U_right"
            have "inv_into V6 q w = qi6 w" using hqi6_eq[OF hw] by simp
            moreover have "qi6 w \<in> V6" using hqi6_V6[OF hw] .
            moreover have "V6 \<subseteq> top1_S1" using hV6_sub .
            ultimately show "(inv_into V6 q w \<in> V) = (qi6 w \<in> W'')" using hWeq by auto
          qed
          moreover have "{w \<in> U_right. qi6 w \<in> W''} \<in> subspace_topology top1_S1 top1_S1_topology U_right"
          proof -
            obtain U where hU: "open U" and hUeq: "U \<inter> U_right = qi6 -` W'' \<inter> U_right"
              using hqi6_cont hW''_open unfolding continuous_on_open_invariant by blast
            have "{w \<in> U_right. qi6 w \<in> W''} = U \<inter> U_right" using hUeq by (by100 blast)
            moreover have "U \<inter> U_right \<in> subspace_topology top1_S1 top1_S1_topology U_right"
            proof -
              have "U \<in> top1_open_sets" using hU unfolding top1_open_sets_def by simp
              hence "U \<in> product_topology_on top1_open_sets top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              hence "top1_S1 \<inter> U \<in> top1_S1_topology"
                unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
              moreover have "U \<inter> U_right = U_right \<inter> (top1_S1 \<inter> U)" using hU_sub by blast
              ultimately show ?thesis unfolding subspace_topology_def by blast
            qed
            ultimately show ?thesis by simp
          qed
          ultimately show "{w \<in> U_right. inv_into V6 q w \<in> V}
              \<in> subspace_topology top1_S1 top1_S1_topology U_right" by simp
        qed
      qed
    qed
    show ?thesis unfolding top1_evenly_covered_on_def
    proof (intro conjI exI[of _ "{V5, V6}"])
      show "openin_on top1_S1 top1_S1_topology U_right" by (rule hU_right_open)
      show "\<forall>V\<in>{V5, V6}. openin_on top1_S1 top1_S1_topology V" using hV5_open hV6_open by (by100 blast)
      show "\<forall>V\<in>{V5, V6}. \<forall>V'\<in>{V5, V6}. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}" using hV_disj by (by100 blast)
      show "{x \<in> top1_S1. q x \<in> U_right} = \<Union> {V5, V6}" using hpreimage by simp
      show "\<forall>V\<in>{V5, V6}. top1_homeomorphism_on V (subspace_topology top1_S1 top1_S1_topology V)
          U_right (subspace_topology top1_S1 top1_S1_topology U_right) q"
        using hhomeo5 hhomeo6 by (by100 blast)
    qed
  qed
  have hevenly_left: "top1_evenly_covered_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q U_left"
  proof -
    have hU_left_open: "openin_on top1_S1 top1_S1_topology U_left"
    proof -
      have "open {p :: real \<times> real. fst p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      hence "{p :: real \<times> real. fst p < 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p < 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p < 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p < 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "U_left = top1_S1 \<inter> {p. fst p < 0}" unfolding U_left_def by (by100 blast)
      moreover have "U_left \<subseteq> top1_S1" unfolding U_left_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    define V7 where "V7 = {p \<in> top1_S1. fst p + snd p > 0 \<and> fst p - snd p < 0}"
    define V8 where "V8 = {p \<in> top1_S1. fst p + snd p < 0 \<and> fst p - snd p > 0}"
    have hV7_open: "openin_on top1_S1 top1_S1_topology V7"
    proof -
      have h1: "open {p :: real \<times> real. fst p + snd p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have h2: "open {p :: real \<times> real. fst p - snd p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have "open {p :: real \<times> real. fst p + snd p > 0 \<and> fst p - snd p < 0}"
        using open_Int[OF h1 h2] by (auto simp: Int_def)
      hence "{p :: real \<times> real. fst p + snd p > 0 \<and> fst p - snd p < 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p + snd p > 0 \<and> fst p - snd p < 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p + snd p > 0 \<and> fst p - snd p < 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p + snd p > 0 \<and> fst p - snd p < 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "V7 = top1_S1 \<inter> {p. fst p + snd p > 0 \<and> fst p - snd p < 0}" unfolding V7_def by (by100 blast)
      moreover have "V7 \<subseteq> top1_S1" unfolding V7_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    have hV8_open: "openin_on top1_S1 top1_S1_topology V8"
    proof -
      have h1: "open {p :: real \<times> real. fst p + snd p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have h2: "open {p :: real \<times> real. fst p - snd p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have "open {p :: real \<times> real. fst p + snd p < 0 \<and> fst p - snd p > 0}"
        using open_Int[OF h1 h2] by (auto simp: Int_def)
      hence "{p :: real \<times> real. fst p + snd p < 0 \<and> fst p - snd p > 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p + snd p < 0 \<and> fst p - snd p > 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p + snd p < 0 \<and> fst p - snd p > 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p + snd p < 0 \<and> fst p - snd p > 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "V8 = top1_S1 \<inter> {p. fst p + snd p < 0 \<and> fst p - snd p > 0}" unfolding V8_def by (by100 blast)
      moreover have "V8 \<subseteq> top1_S1" unfolding V8_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    have hV_disj: "V7 \<inter> V8 = {}" unfolding V7_def V8_def by auto
    have hpreimage: "{p \<in> top1_S1. q p \<in> U_left} = V7 \<union> V8"
    proof (intro set_eqI iffI)
      fix p assume hp: "p \<in> {p \<in> top1_S1. q p \<in> U_left}"
      hence hpS1: "p \<in> top1_S1" and hqp: "q p \<in> U_left" by auto
      obtain x y where hxy: "p = (x, y)" by (cases p) auto
      have "fst (q p) < 0" using hqp unfolding U_left_def by (by100 blast)
      hence "x\<^sup>2 - y\<^sup>2 < 0" unfolding q_def hxy by (simp add: power2_eq_square)
      hence "(x+y)*(x-y) < 0" by (simp add: power2_eq_square algebra_simps)
      hence "(x+y > 0 \<and> x-y < 0) \<or> (x+y < 0 \<and> x-y > 0)" using mult_less_0_iff by force
      thus "p \<in> V7 \<union> V8" unfolding V7_def V8_def using hpS1 hxy by auto
    next
      fix p assume "p \<in> V7 \<union> V8"
      hence hpS1: "p \<in> top1_S1" and hq: "(fst p + snd p) * (fst p - snd p) < 0"
        unfolding V7_def V8_def by (auto intro: mult_pos_neg mult_neg_pos)
      have "fst (q p) = fst p ^ 2 - snd p ^ 2" unfolding q_def by simp
      also have "\<dots> = (fst p + snd p) * (fst p - snd p)" by (simp add: power2_eq_square algebra_simps)
      finally have "fst (q p) < 0" using hq by simp
      moreover have "q p \<in> top1_S1" by (rule hq_S1[OF hpS1])
      ultimately show "p \<in> {p \<in> top1_S1. q p \<in> U_left}" unfolding U_left_def using hpS1 by auto
    qed
    \<comment> \<open>Homeomorphisms V7 \<rightarrow> U_left and V8 \<rightarrow> U_left. Same pattern.\<close>
    \<comment> \<open>hhomeo7/hhomeo8: same pattern as hhomeo5/hhomeo6 but using b/(2y) inverse.\<close>
    have hhomeo7: "top1_homeomorphism_on V7 (subspace_topology top1_S1 top1_S1_topology V7)
        U_left (subspace_topology top1_S1 top1_S1_topology U_left) q"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      have hTS1l: "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      show "is_topology_on V7 (subspace_topology top1_S1 top1_S1_topology V7)"
        by (rule subspace_topology_is_topology_on[OF hTS1l]) (use V7_def in blast)
      show "is_topology_on U_left (subspace_topology top1_S1 top1_S1_topology U_left)"
        by (rule subspace_topology_is_topology_on[OF hTS1l]) (use U_left_def in blast)
      show hbij7: "bij_betw q V7 U_left"
      proof (rule bij_betw_imageI)
        show "inj_on q V7"
        proof (rule inj_onI)
          fix p1 p2 assume hp1: "p1 \<in> V7" and hp2: "p2 \<in> V7" and heq: "q p1 = q p2"
          obtain x1 y1 where h1: "p1 = (x1, y1)" by (cases p1) auto
          obtain x2 y2 where h2: "p2 = (x2, y2)" by (cases p2) auto
          have hx1: "x1+y1 > 0" "x1-y1 < 0" "x1\<^sup>2+y1\<^sup>2 = 1" using hp1 unfolding V7_def top1_S1_def h1 by auto
          have hx2: "x2+y2 > 0" "x2-y2 < 0" "x2\<^sup>2+y2\<^sup>2 = 1" using hp2 unfolding V7_def top1_S1_def h2 by auto
          have "x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2" using heq unfolding q_def h1 h2 by auto
          have "y1\<^sup>2 = (1 - (x1\<^sup>2 - y1\<^sup>2))/2" using hx1(3) by (simp add: field_simps)
          also have "\<dots> = (1 - (x2\<^sup>2 - y2\<^sup>2))/2" using \<open>x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2\<close> by simp
          also have "\<dots> = y2\<^sup>2" using hx2(3) by (simp add: field_simps)
          finally have "y1\<^sup>2 = y2\<^sup>2" .
          have "2*x1*y1 = 2*x2*y2" using heq unfolding q_def h1 h2 by auto
          hence "x1*y1 = x2*y2" by simp
          have "y1 > 0" using hx1(1) hx1(2) by linarith
          have "y2 > 0" using hx2(1) hx2(2) by linarith
          hence "y1 = y2" using \<open>y1\<^sup>2 = y2\<^sup>2\<close> \<open>y1 > 0\<close> by (simp add: power2_eq_iff_nonneg)
          moreover have "x1 = x2" using \<open>x1*y1 = x2*y2\<close> \<open>y1 = y2\<close> \<open>y1 > 0\<close> by simp
          ultimately show "p1 = p2" unfolding h1 h2 by simp
        qed
      next
        show "q ` V7 = U_left"
        proof (intro set_eqI iffI)
          fix w assume "w \<in> q ` V7"
          then obtain p where hp: "p \<in> V7" and hw: "w = q p" by (by100 blast)
          have "p \<in> top1_S1" using hp unfolding V7_def by auto
          obtain x y where hxy: "p = (x, y)" by (cases p) auto
          have "x + y > 0" "x - y < 0" using hp unfolding V7_def hxy by auto
          hence "(x+y)*(x-y) < 0" by (simp add: mult_pos_neg)
          hence "x\<^sup>2 - y\<^sup>2 < 0" by (simp add: power2_eq_square algebra_simps)
          hence "fst (q p) < 0" unfolding q_def hxy by (simp add: power2_eq_square)
          moreover have "q p \<in> top1_S1" by (rule hq_S1[OF \<open>p \<in> top1_S1\<close>])
          ultimately show "w \<in> U_left" unfolding U_left_def using hw by simp
        next
          fix w assume hw: "w \<in> U_left"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and ha: "a < 0" using hw unfolding U_left_def top1_S1_def hab by auto
          define y where "y = sqrt ((1-a)/2)" define x where "x = b / (2 * sqrt ((1-a)/2))"
          have hy_pos: "y > 0" unfolding y_def using ha by simp
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha by (simp add: real_sqrt_mult_self)
          have hqb: "2*x*y = b"
          proof -
            have "sqrt ((1-a)/2) > 0" using ha by simp
            hence "2 * sqrt ((1-a)/2) \<noteq> 0" by simp
            thus ?thesis unfolding x_def y_def by simp
          qed
          have "4*y\<^sup>2*(x\<^sup>2 + y\<^sup>2) = (2*x*y)\<^sup>2 + (2*y\<^sup>2)\<^sup>2"
            by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2 + (1-a)\<^sup>2"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis using hqb by simp
          qed
          also have "\<dots> = 2 - 2*a" using hS1w by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = 4*y\<^sup>2"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis by linarith
          qed
          finally have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hy_pos by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis using hxy_S1 by linarith
          qed
          have "x + y > 0 \<and> x - y < 0"
          proof -
            have "(x+y)*(x-y) = a" by (simp add: power2_eq_square algebra_simps)
              (use hqa in \<open>simp add: power2_eq_square algebra_simps\<close>)
            hence "(x+y)*(x-y) < 0" using ha by simp
            hence "(x+y > 0 \<and> x-y < 0) \<or> (x+y < 0 \<and> x-y > 0)" using mult_less_0_iff by force
            moreover have "x + y > 0 \<or> x - y < 0" using hy_pos by linarith
            ultimately show ?thesis by linarith
          qed
          have "(x, y) \<in> V7" unfolding V7_def top1_S1_def using hxy_S1 \<open>x+y>0 \<and> x-y<0\<close> by simp
          moreover have "q (x, y) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hab by simp
          qed
          ultimately show "w \<in> q ` V7" by (by100 blast)
        qed
      qed
      show "top1_continuous_map_on V7 (subspace_topology top1_S1 top1_S1_topology V7)
          U_left (subspace_topology top1_S1 top1_S1_topology U_left) q"
      proof -
        have hV7_sub: "V7 \<subseteq> top1_S1" unfolding V7_def by (by100 blast)
        have hU_sub: "U_left \<subseteq> top1_S1" unfolding U_left_def by (by100 blast)
        have hq_V7: "top1_continuous_map_on V7 (subspace_topology top1_S1 top1_S1_topology V7)
            top1_S1 top1_S1_topology q"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hq_cont hV7_sub])
        have hq_img: "q ` V7 \<subseteq> U_left" using hbij7 unfolding bij_betw_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> V7" thus "q p \<in> U_left" using hq_img by (by100 blast)
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology U_left"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = U_left \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          have "{p \<in> V7. q p \<in> V} = {p \<in> V7. q p \<in> W}" using hq_img hVeq by (by100 blast)
          moreover have "{p \<in> V7. q p \<in> W} \<in> subspace_topology top1_S1 top1_S1_topology V7"
            using hq_V7 hW unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "{p \<in> V7. q p \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology V7" by simp
        qed
      qed
      show "top1_continuous_map_on U_left (subspace_topology top1_S1 top1_S1_topology U_left)
          V7 (subspace_topology top1_S1 top1_S1_topology V7) (inv_into V7 q)"
      proof -
        define qi7 where "qi7 = (\<lambda>(a::real, b::real). (b / (2 * sqrt ((1-a)/2)), sqrt ((1-a)/2)))"
        have hqi7_props: "\<And>w. w \<in> U_left \<Longrightarrow> qi7 w \<in> V7 \<and> q (qi7 w) = w"
        proof -
          fix w assume hw: "w \<in> U_left"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and ha: "a < 0" using hw unfolding U_left_def top1_S1_def hab by auto
          define y where "y = sqrt ((1-a)/2)" define x where "x = b / (2 * sqrt ((1-a)/2))"
          have hqi7_w: "qi7 w = (x, y)" unfolding qi7_def hab x_def y_def by simp
          have hy_pos: "y > 0" unfolding y_def using ha by simp
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha by (simp add: real_sqrt_mult_self)
          have hqb: "2*x*y = b"
          proof -
            have "sqrt ((1-a)/2) > 0" using ha by simp
            hence "2 * sqrt ((1-a)/2) \<noteq> 0" by simp
            thus ?thesis unfolding x_def y_def by simp
          qed
          have "4*y\<^sup>2*(x\<^sup>2 + y\<^sup>2) = (2*x*y)\<^sup>2 + (2*y\<^sup>2)\<^sup>2"
            by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2 + (1-a)\<^sup>2"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis using hqb by simp
          qed
          also have "\<dots> = 2 - 2*a" using hS1w by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = 4*y\<^sup>2"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis by linarith
          qed
          finally have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hy_pos by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis using hxy_S1 by linarith
          qed
          have "x + y > 0 \<and> x - y < 0"
          proof -
            have "(x+y)*(x-y) = a" by (simp add: power2_eq_square algebra_simps)
              (use hqa in \<open>simp add: power2_eq_square algebra_simps\<close>)
            hence "(x+y)*(x-y) < 0" using ha by simp
            hence "(x+y > 0 \<and> x-y < 0) \<or> (x+y < 0 \<and> x-y > 0)" using mult_less_0_iff by force
            moreover have "x + y > 0 \<or> x - y < 0" using hy_pos by linarith
            ultimately show ?thesis by linarith
          qed
          have "qi7 w \<in> V7" unfolding hqi7_w V7_def top1_S1_def using hxy_S1 \<open>x+y>0 \<and> x-y<0\<close> by simp
          moreover have "q (qi7 w) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hqi7_w hab by simp
          qed
          ultimately show "qi7 w \<in> V7 \<and> q (qi7 w) = w" by (by100 blast)
        qed
        have hqi7_eq: "\<And>w. w \<in> U_left \<Longrightarrow> qi7 w = inv_into V7 q w"
        proof -
          fix w assume hw: "w \<in> U_left"
          have "qi7 w \<in> V7" and "q (qi7 w) = w" using hqi7_props[OF hw] by auto
          thus "qi7 w = inv_into V7 q w"
            by (simp add: inv_into_f_eq[OF inj_on_subset[OF bij_betw_imp_inj_on[OF hbij7]]])
        qed
        have hqi7_V7: "\<And>w. w \<in> U_left \<Longrightarrow> qi7 w \<in> V7" using hqi7_props by (by100 blast)
        have hqi7_cont: "continuous_on U_left qi7"
          unfolding qi7_def split_def
          by (intro continuous_intros continuous_on_divide)
             (auto simp: U_left_def top1_S1_def)
        have hU_sub: "U_left \<subseteq> top1_S1" unfolding U_left_def by (by100 blast)
        have hV7_sub: "V7 \<subseteq> top1_S1" unfolding V7_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix w assume "w \<in> U_left"
          show "inv_into V7 q w \<in> V7" using hqi7_eq[OF \<open>w \<in> U_left\<close>] hqi7_V7[OF \<open>w \<in> U_left\<close>] by simp
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology V7"
          obtain W'' where hW'': "W'' \<in> product_topology_on top1_open_sets top1_open_sets"
              and hWeq: "V = V7 \<inter> (top1_S1 \<inter> W'')"
          proof -
            obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = V7 \<inter> W"
              using hV unfolding subspace_topology_def by (by100 blast)
            obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
                and hWW': "W = top1_S1 \<inter> W'"
              using hW unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
            show ?thesis using that[OF hW'] hVeq hWW' by simp
          qed
          have hW''_open: "open W''"
            using hW'' by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
          have "{w \<in> U_left. inv_into V7 q w \<in> V} = {w \<in> U_left. qi7 w \<in> W''}"
          proof (intro Collect_cong conj_cong refl)
            fix w assume hw: "w \<in> U_left"
            have "inv_into V7 q w = qi7 w" using hqi7_eq[OF hw] by simp
            moreover have "qi7 w \<in> V7" using hqi7_V7[OF hw] .
            moreover have "V7 \<subseteq> top1_S1" using hV7_sub .
            ultimately show "(inv_into V7 q w \<in> V) = (qi7 w \<in> W'')" using hWeq by auto
          qed
          moreover have "{w \<in> U_left. qi7 w \<in> W''} \<in> subspace_topology top1_S1 top1_S1_topology U_left"
          proof -
            obtain U where hU: "open U" and hUeq: "U \<inter> U_left = qi7 -` W'' \<inter> U_left"
              using hqi7_cont hW''_open unfolding continuous_on_open_invariant by blast
            have "{w \<in> U_left. qi7 w \<in> W''} = U \<inter> U_left" using hUeq by (by100 blast)
            moreover have "U \<inter> U_left \<in> subspace_topology top1_S1 top1_S1_topology U_left"
            proof -
              have "U \<in> top1_open_sets" using hU unfolding top1_open_sets_def by simp
              hence "U \<in> product_topology_on top1_open_sets top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              hence "top1_S1 \<inter> U \<in> top1_S1_topology"
                unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
              moreover have "U \<inter> U_left = U_left \<inter> (top1_S1 \<inter> U)" using hU_sub by blast
              ultimately show ?thesis unfolding subspace_topology_def by blast
            qed
            ultimately show ?thesis by simp
          qed
          ultimately show "{w \<in> U_left. inv_into V7 q w \<in> V}
              \<in> subspace_topology top1_S1 top1_S1_topology U_left" by simp
        qed
      qed
    qed
    have hhomeo8: "top1_homeomorphism_on V8 (subspace_topology top1_S1 top1_S1_topology V8)
        U_left (subspace_topology top1_S1 top1_S1_topology U_left) q"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      have hTS1ll: "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      show "is_topology_on V8 (subspace_topology top1_S1 top1_S1_topology V8)"
        by (rule subspace_topology_is_topology_on[OF hTS1ll]) (use V8_def in blast)
      show "is_topology_on U_left (subspace_topology top1_S1 top1_S1_topology U_left)"
        by (rule subspace_topology_is_topology_on[OF hTS1ll]) (use U_left_def in blast)
      show hbij8: "bij_betw q V8 U_left"
      proof (rule bij_betw_imageI)
        show "inj_on q V8"
        proof (rule inj_onI)
          fix p1 p2 assume hp1: "p1 \<in> V8" and hp2: "p2 \<in> V8" and heq: "q p1 = q p2"
          obtain x1 y1 where h1: "p1 = (x1, y1)" by (cases p1) auto
          obtain x2 y2 where h2: "p2 = (x2, y2)" by (cases p2) auto
          have hx1: "x1+y1 < 0" "x1-y1 > 0" "x1\<^sup>2+y1\<^sup>2 = 1" using hp1 unfolding V8_def top1_S1_def h1 by auto
          have hx2: "x2+y2 < 0" "x2-y2 > 0" "x2\<^sup>2+y2\<^sup>2 = 1" using hp2 unfolding V8_def top1_S1_def h2 by auto
          have "x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2" using heq unfolding q_def h1 h2 by auto
          have "y1\<^sup>2 = y2\<^sup>2"
          proof -
            have "y1\<^sup>2 = (1 - (x1\<^sup>2 - y1\<^sup>2))/2" using hx1(3) by (simp add: field_simps)
            also have "\<dots> = (1 - (x2\<^sup>2 - y2\<^sup>2))/2" using \<open>x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2\<close> by simp
            also have "\<dots> = y2\<^sup>2" using hx2(3) by (simp add: field_simps)
            finally show ?thesis .
          qed
          have "2*x1*y1 = 2*x2*y2" using heq unfolding q_def h1 h2 by auto
          hence "x1*y1 = x2*y2" by simp
          have "y1 < 0" using hx1(1) hx1(2) by linarith
          have "y2 < 0" using hx2(1) hx2(2) by linarith
          hence "y1 = y2 \<or> y1 = -y2" using \<open>y1\<^sup>2 = y2\<^sup>2\<close> power2_eq_iff by (by100 blast)
          hence "y1 = y2" using \<open>y1 < 0\<close> \<open>y2 < 0\<close> by linarith
          moreover have "x1 = x2" using \<open>x1*y1 = x2*y2\<close> \<open>y1 = y2\<close> \<open>y1 < 0\<close> by simp
          ultimately show "p1 = p2" unfolding h1 h2 by simp
        qed
      next
        show "q ` V8 = U_left"
        proof (intro set_eqI iffI)
          fix w assume "w \<in> q ` V8"
          then obtain p where hp: "p \<in> V8" and hw: "w = q p" by (by100 blast)
          have "p \<in> top1_S1" using hp unfolding V8_def by auto
          obtain x y where hxy: "p = (x, y)" by (cases p) auto
          have "x + y < 0" "x - y > 0" using hp unfolding V8_def hxy by auto
          hence "(x+y)*(x-y) < 0" by (simp add: mult_neg_pos)
          hence "x\<^sup>2 - y\<^sup>2 < 0" by (simp add: power2_eq_square algebra_simps)
          hence "fst (q p) < 0" unfolding q_def hxy by (simp add: power2_eq_square)
          moreover have "q p \<in> top1_S1" by (rule hq_S1[OF \<open>p \<in> top1_S1\<close>])
          ultimately show "w \<in> U_left" unfolding U_left_def using hw by simp
        next
          fix w assume hw: "w \<in> U_left"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and ha: "a < 0" using hw unfolding U_left_def top1_S1_def hab by auto
          define y where "y = -sqrt ((1-a)/2)" define x where "x = -b / (2 * sqrt ((1-a)/2))"
          have hy_neg: "y < 0" unfolding y_def using ha by simp
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha by (simp add: real_sqrt_mult_self)
          have hqb: "2*x*y = b"
          proof -
            have "sqrt ((1-a)/2) > 0" using ha by simp
            hence "2 * sqrt ((1-a)/2) \<noteq> 0" by simp
            thus ?thesis unfolding x_def y_def by (simp add: field_simps)
          qed
          have "4*y\<^sup>2*(x\<^sup>2 + y\<^sup>2) = (2*x*y)\<^sup>2 + (2*y\<^sup>2)\<^sup>2"
            by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2 + (1-a)\<^sup>2"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis using hqb by simp
          qed
          also have "\<dots> = 2 - 2*a" using hS1w by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = 4*y\<^sup>2"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis by linarith
          qed
          finally have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hy_neg by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis using hxy_S1 by linarith
          qed
          have "x + y < 0 \<and> x - y > 0"
          proof -
            have "(x+y)*(x-y) = a" by (simp add: power2_eq_square algebra_simps)
              (use hqa in \<open>simp add: power2_eq_square algebra_simps\<close>)
            hence "(x+y)*(x-y) < 0" using ha by simp
            hence "(x+y > 0 \<and> x-y < 0) \<or> (x+y < 0 \<and> x-y > 0)" using mult_less_0_iff by force
            moreover have "x + y < 0 \<or> x - y > 0" using hy_neg by linarith
            ultimately show ?thesis by linarith
          qed
          have "(x, y) \<in> V8" unfolding V8_def top1_S1_def using hxy_S1 \<open>x+y<0 \<and> x-y>0\<close> by simp
          moreover have "q (x, y) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hab by simp
          qed
          ultimately show "w \<in> q ` V8" by (by100 blast)
        qed
      qed
      show "top1_continuous_map_on V8 (subspace_topology top1_S1 top1_S1_topology V8)
          U_left (subspace_topology top1_S1 top1_S1_topology U_left) q"
      proof -
        have hV8_sub: "V8 \<subseteq> top1_S1" unfolding V8_def by (by100 blast)
        have hU_sub: "U_left \<subseteq> top1_S1" unfolding U_left_def by (by100 blast)
        have hq_V8: "top1_continuous_map_on V8 (subspace_topology top1_S1 top1_S1_topology V8)
            top1_S1 top1_S1_topology q"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hq_cont hV8_sub])
        have hq_img: "q ` V8 \<subseteq> U_left" using hbij8 unfolding bij_betw_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> V8" thus "q p \<in> U_left" using hq_img by (by100 blast)
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology U_left"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = U_left \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          have "{p \<in> V8. q p \<in> V} = {p \<in> V8. q p \<in> W}" using hq_img hVeq by (by100 blast)
          moreover have "{p \<in> V8. q p \<in> W} \<in> subspace_topology top1_S1 top1_S1_topology V8"
            using hq_V8 hW unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "{p \<in> V8. q p \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology V8" by simp
        qed
      qed
      show "top1_continuous_map_on U_left (subspace_topology top1_S1 top1_S1_topology U_left)
          V8 (subspace_topology top1_S1 top1_S1_topology V8) (inv_into V8 q)"
      proof -
        define qi8 where "qi8 = (\<lambda>(a::real, b::real). (-b / (2 * sqrt ((1-a)/2)), -sqrt ((1-a)/2)))"
        have hqi8_props: "\<And>w. w \<in> U_left \<Longrightarrow> qi8 w \<in> V8 \<and> q (qi8 w) = w"
        proof -
          fix w assume hw: "w \<in> U_left"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and ha: "a < 0" using hw unfolding U_left_def top1_S1_def hab by auto
          define y where "y = -sqrt ((1-a)/2)" define x where "x = -b / (2 * sqrt ((1-a)/2))"
          have hqi8_w: "qi8 w = (x, y)" unfolding qi8_def hab x_def y_def by simp
          have hy_neg: "y < 0" unfolding y_def using ha by simp
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha by (simp add: real_sqrt_mult_self)
          have hqb: "2*x*y = b"
          proof -
            have "sqrt ((1-a)/2) > 0" using ha by simp
            hence "2 * sqrt ((1-a)/2) \<noteq> 0" by simp
            thus ?thesis unfolding x_def y_def by (simp add: field_simps)
          qed
          have "4*y\<^sup>2*(x\<^sup>2 + y\<^sup>2) = (2*x*y)\<^sup>2 + (2*y\<^sup>2)\<^sup>2"
            by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2 + (1-a)\<^sup>2"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis using hqb by simp
          qed
          also have "\<dots> = 2 - 2*a" using hS1w by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = 4*y\<^sup>2"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis by linarith
          qed
          finally have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hy_neg by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis using hxy_S1 by linarith
          qed
          have "x + y < 0 \<and> x - y > 0"
          proof -
            have "(x+y)*(x-y) = a" by (simp add: power2_eq_square algebra_simps)
              (use hqa in \<open>simp add: power2_eq_square algebra_simps\<close>)
            hence "(x+y)*(x-y) < 0" using ha by simp
            hence "(x+y > 0 \<and> x-y < 0) \<or> (x+y < 0 \<and> x-y > 0)" using mult_less_0_iff by force
            moreover have "x + y < 0 \<or> x - y > 0" using hy_neg by linarith
            ultimately show ?thesis by linarith
          qed
          have "qi8 w \<in> V8" unfolding hqi8_w V8_def top1_S1_def using hxy_S1 \<open>x+y<0 \<and> x-y>0\<close> by simp
          moreover have "q (qi8 w) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hqi8_w hab by simp
          qed
          ultimately show "qi8 w \<in> V8 \<and> q (qi8 w) = w" by (by100 blast)
        qed
        have hqi8_eq: "\<And>w. w \<in> U_left \<Longrightarrow> qi8 w = inv_into V8 q w"
        proof -
          fix w assume hw: "w \<in> U_left"
          have "qi8 w \<in> V8" and "q (qi8 w) = w" using hqi8_props[OF hw] by auto
          thus "qi8 w = inv_into V8 q w"
            by (simp add: inv_into_f_eq[OF inj_on_subset[OF bij_betw_imp_inj_on[OF hbij8]]])
        qed
        have hqi8_V8: "\<And>w. w \<in> U_left \<Longrightarrow> qi8 w \<in> V8" using hqi8_props by (by100 blast)
        have hqi8_cont: "continuous_on U_left qi8"
          unfolding qi8_def split_def
          by (intro continuous_intros continuous_on_divide)
             (auto simp: U_left_def top1_S1_def)
        have hU_sub: "U_left \<subseteq> top1_S1" unfolding U_left_def by (by100 blast)
        have hV8_sub: "V8 \<subseteq> top1_S1" unfolding V8_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix w assume "w \<in> U_left"
          show "inv_into V8 q w \<in> V8" using hqi8_eq[OF \<open>w \<in> U_left\<close>] hqi8_V8[OF \<open>w \<in> U_left\<close>] by simp
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology V8"
          obtain W'' where hW'': "W'' \<in> product_topology_on top1_open_sets top1_open_sets"
              and hWeq: "V = V8 \<inter> (top1_S1 \<inter> W'')"
          proof -
            obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = V8 \<inter> W"
              using hV unfolding subspace_topology_def by (by100 blast)
            obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
                and hWW': "W = top1_S1 \<inter> W'"
              using hW unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
            show ?thesis using that[OF hW'] hVeq hWW' by simp
          qed
          have hW''_open: "open W''"
            using hW'' by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
          have "{w \<in> U_left. inv_into V8 q w \<in> V} = {w \<in> U_left. qi8 w \<in> W''}"
          proof (intro Collect_cong conj_cong refl)
            fix w assume hw: "w \<in> U_left"
            have "inv_into V8 q w = qi8 w" using hqi8_eq[OF hw] by simp
            moreover have "qi8 w \<in> V8" using hqi8_V8[OF hw] .
            moreover have "V8 \<subseteq> top1_S1" using hV8_sub .
            ultimately show "(inv_into V8 q w \<in> V) = (qi8 w \<in> W'')" using hWeq by auto
          qed
          moreover have "{w \<in> U_left. qi8 w \<in> W''} \<in> subspace_topology top1_S1 top1_S1_topology U_left"
          proof -
            obtain U where hU: "open U" and hUeq: "U \<inter> U_left = qi8 -` W'' \<inter> U_left"
              using hqi8_cont hW''_open unfolding continuous_on_open_invariant by blast
            have "{w \<in> U_left. qi8 w \<in> W''} = U \<inter> U_left" using hUeq by (by100 blast)
            moreover have "U \<inter> U_left \<in> subspace_topology top1_S1 top1_S1_topology U_left"
            proof -
              have "U \<in> top1_open_sets" using hU unfolding top1_open_sets_def by simp
              hence "U \<in> product_topology_on top1_open_sets top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              hence "top1_S1 \<inter> U \<in> top1_S1_topology"
                unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
              moreover have "U \<inter> U_left = U_left \<inter> (top1_S1 \<inter> U)" using hU_sub by blast
              ultimately show ?thesis unfolding subspace_topology_def by blast
            qed
            ultimately show ?thesis by simp
          qed
          ultimately show "{w \<in> U_left. inv_into V8 q w \<in> V}
              \<in> subspace_topology top1_S1 top1_S1_topology U_left" by simp
        qed
      qed
    qed
    show ?thesis unfolding top1_evenly_covered_on_def
    proof (intro conjI exI[of _ "{V7, V8}"])
      show "openin_on top1_S1 top1_S1_topology U_left" by (rule hU_left_open)
      show "\<forall>V\<in>{V7, V8}. openin_on top1_S1 top1_S1_topology V" using hV7_open hV8_open by (by100 blast)
      show "\<forall>V\<in>{V7, V8}. \<forall>V'\<in>{V7, V8}. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}" using hV_disj by (by100 blast)
      show "{x \<in> top1_S1. q x \<in> U_left} = \<Union> {V7, V8}" using hpreimage by simp
      show "\<forall>V\<in>{V7, V8}. top1_homeomorphism_on V (subspace_topology top1_S1 top1_S1_topology V)
          U_left (subspace_topology top1_S1 top1_S1_topology U_left) q"
        using hhomeo7 hhomeo8 by (by100 blast)
    qed
  qed
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



lemma squaring_map_factorization:
  assumes hh: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h"
      and hanti: "top1_antipode_preserving_S1 h"
  obtains k where "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology k"
      and "\<forall>z\<in>top1_S1. k ((\<lambda>(x,y). (x^2-y^2, 2*x*y)) z) = (\<lambda>(x,y). (x^2-y^2, 2*x*y)) (h z)"
proof -
  define q :: "real \<times> real \<Rightarrow> real \<times> real" where
    "q p = (fst p ^ 2 - snd p ^ 2, 2 * fst p * snd p)" for p
  have hq_alt: "q = (\<lambda>(x, y). (x^2-y^2, 2*x*y))" unfolding q_def by (intro ext) auto
  \<comment> \<open>q(-z) = q(z) and h(-z) = -h(z) imply q(h(-z)) = q(h(z)).\<close>
  have hq_neg: "\<And>p. q (- fst p, - snd p) = q p"
    unfolding q_def by (simp add: power2_eq_square algebra_simps)
  have hanti': "\<And>x y. h (-x, -y) = (- fst (h (x, y)), - snd (h (x, y)))"
    using hanti unfolding top1_antipode_preserving_S1_def by (by100 blast)
  have hqh_fiber: "\<And>z. z \<in> top1_S1 \<Longrightarrow> q (h (- fst z, - snd z)) = q (h z)"
  proof -
    fix z assume "z \<in> top1_S1"
    obtain x y where hxy: "z = (x, y)" by (cases z) auto
    have "q (h (-x, -y)) = q (- fst (h (x, y)), - snd (h (x, y)))" using hanti' by simp
    also have "\<dots> = q (h (x, y))" using hq_neg[of "h (x, y)"] by simp
    finally show "q (h (- fst z, - snd z)) = q (h z)" using hxy by simp
  qed
  \<comment> \<open>q∘h is constant on fibers {z, -z}, so it factors through q.
     Define k(w) = q(h(z)) where z is any preimage of w under q.\<close>
  \<comment> \<open>Define k: for each w, pick z with q(z)=w (using surjectivity), set k(w) = q(h(z)).\<close>
  have hq_surj: "q ` top1_S1 = top1_S1"
    using squaring_map_covering unfolding top1_covering_map_on_def hq_alt[symmetric] by (by100 blast)
  define k where "k w = q (h (SOME z. z \<in> top1_S1 \<and> q z = w))" for w
  \<comment> \<open>Fibers of q on S^1: q(z')=q(z) iff z'=z or z'=-z.\<close>
  have hq_fiber: "\<And>z z'. z \<in> top1_S1 \<Longrightarrow> z' \<in> top1_S1 \<Longrightarrow> q z' = q z \<Longrightarrow>
      z' = z \<or> z' = (- fst z, - snd z)"
  proof -
    fix z z' assume hz: "z \<in> top1_S1" and hz': "z' \<in> top1_S1" and hqeq: "q z' = q z"
    obtain x y where hxy: "z = (x, y)" by (cases z) auto
    obtain x' y' where hxy': "z' = (x', y')" by (cases z') auto
    have hS1: "x\<^sup>2 + y\<^sup>2 = 1" using hz unfolding top1_S1_def hxy by simp
    have hS1': "x'\<^sup>2 + y'\<^sup>2 = 1" using hz' unfolding top1_S1_def hxy' by simp
    have heq1: "x'\<^sup>2 - y'\<^sup>2 = x\<^sup>2 - y\<^sup>2" using hqeq unfolding q_def hxy hxy' by auto
    have heq2: "x'*y' = x*y" using hqeq unfolding q_def hxy hxy' by auto
    \<comment> \<open>From S^1 equations: x'^2 = x^2 and y'^2 = y^2.\<close>
    have hx2: "x'\<^sup>2 = x\<^sup>2"
    proof -
      have "x'\<^sup>2 = (1 + (x'\<^sup>2 - y'\<^sup>2))/2" using hS1' by (simp add: field_simps)
      also have "\<dots> = (1 + (x\<^sup>2 - y\<^sup>2))/2" using heq1 by simp
      also have "\<dots> = x\<^sup>2" using hS1 by (simp add: field_simps)
      finally show ?thesis .
    qed
    have hy2: "y'\<^sup>2 = y\<^sup>2" using hx2 hS1 hS1' by linarith
    \<comment> \<open>x' = \<pm>x, y' = \<pm>y. Combined with x'y' = xy:\<close>
    have "x' = x \<or> x' = -x" using hx2 power2_eq_iff by (by100 blast)
    moreover have "y' = y \<or> y' = -y" using hy2 power2_eq_iff by (by100 blast)
    ultimately consider "x' = x \<and> y' = y" | "x' = -x \<and> y' = -y"
        | "x' = x \<and> y' = -y" | "x' = -x \<and> y' = y" by blast
    thus "z' = z \<or> z' = (- fst z, - snd z)"
    proof cases
      case 1 thus ?thesis using hxy hxy' by simp
    next
      case 2 thus ?thesis using hxy hxy' by simp
    next
      case 3 \<comment> \<open>x'=x, y'=-y. Then x'y' = -xy = xy, so 2xy=0, x=0 or y=0.\<close>
      hence "x*(-y) = x*y" using heq2 by simp
      hence "x*y = 0" by simp
      hence "x = 0 \<or> y = 0" by simp
      thus ?thesis
      proof
        assume "x = 0" thus ?thesis using 3 hxy hxy' by simp
      next
        assume "y = 0" thus ?thesis using 3 hxy hxy' by simp
      qed
    next
      case 4 \<comment> \<open>x'=-x, y'=y. Then x'y' = -xy = xy, so 2xy=0.\<close>
      hence "(-x)*y = x*y" using heq2 by simp
      hence "x*y = 0" by simp
      hence "x = 0 \<or> y = 0" by simp
      thus ?thesis
      proof
        assume "x = 0" thus ?thesis using 4 hxy hxy' by simp
      next
        assume "y = 0" thus ?thesis using 4 hxy hxy' by simp
      qed
    qed
  qed
  have hk_eq: "\<And>z. z \<in> top1_S1 \<Longrightarrow> k (q z) = q (h z)"
  proof -
    fix z assume hz: "z \<in> top1_S1"
    define z' where "z' = (SOME z'. z' \<in> top1_S1 \<and> q z' = q z)"
    have "z' \<in> top1_S1 \<and> q z' = q z"
      unfolding z'_def by (rule someI[of "\<lambda>z'. z' \<in> top1_S1 \<and> q z' = q z"]) (use hz in auto)
    hence hz'S1: "z' \<in> top1_S1" and hqz': "q z' = q z" by auto
    have "z' = z \<or> z' = (- fst z, - snd z)" by (rule hq_fiber[OF hz hz'S1 hqz'])
    hence "q (h z') = q (h z)"
    proof
      assume "z' = z" thus ?thesis by simp
    next
      assume "z' = (- fst z, - snd z)"
      thus ?thesis using hqh_fiber[OF hz] by simp
    qed
    thus "k (q z) = q (h z)" unfolding k_def z'_def by simp
  qed
  have hk_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology k"
  proof -
    \<comment> \<open>k is continuous because q is a quotient map and k∘q = q∘h is continuous.\<close>
    \<comment> \<open>First: q∘h is continuous S^1 \<rightarrow> S^1.\<close>
    have hq_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q"
      using squaring_map_covering unfolding top1_covering_map_on_def hq_alt[symmetric] by (by100 blast)
    have hqh_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (q \<circ> h)"
      by (rule top1_continuous_map_on_comp[OF hh hq_cont])
    \<comment> \<open>q is a quotient map (covering \<Rightarrow> open surjection \<Rightarrow> preimages of open=open characterize topology).\<close>
    \<comment> \<open>For V open in S^1: q^{-1}(k^{-1}(V)) = (q\<circ>h)^{-1}(V) is open (since q\<circ>h continuous).
       Since q is a quotient map, k^{-1}(V) is open.\<close>
    \<comment> \<open>Instead of proving q is a quotient map in general, we use Theorem_22_2 directly.\<close>
    have hg_const: "\<forall>z\<in>top1_S1. \<forall>z'\<in>top1_S1. q z = q z' \<longrightarrow> (q \<circ> h) z = (q \<circ> h) z'"
    proof (intro ballI impI)
      fix z z' assume hz: "z \<in> top1_S1" and hz': "z' \<in> top1_S1" and hqeq: "q z = q z'"
      have "z' = z \<or> z' = (- fst z, - snd z)" by (rule hq_fiber[OF hz hz' hqeq[symmetric]])
      thus "(q \<circ> h) z = (q \<circ> h) z'"
      proof
        assume "z' = z" thus ?thesis by simp
      next
        assume "z' = (- fst z, - snd z)"
        hence "(q \<circ> h) z' = q (h (- fst z, - snd z))" by simp
        also have "\<dots> = q (h z)" using hqh_fiber[OF hz] by simp
        finally show ?thesis by simp
      qed
    qed
    \<comment> \<open>q is a quotient map. Covering maps are quotient maps.\<close>
    have hq_quotient: "top1_quotient_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q"
    proof -
      have hTS1q: "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      have hq_cover: "top1_covering_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q"
        using squaring_map_covering unfolding hq_alt[symmetric] by simp
      \<comment> \<open>q is an open map: for U open in S^1, q(U) is open in S^1.
         This follows from q being a local homeomorphism (covering map).
         For each w \<in> q(U), pick evenly covered V \<ni> w. On the sheet containing the
         preimage point in U, q restricts to a homeomorphism, so q(sheet \<inter> U) is open.
         Hence q(U) is a union of opens = open.\<close>
      \<comment> \<open>Proving q is an open map is substantial. Instead, we prove the quotient
         condition directly: if q^{-1}(V) is open and V \<subseteq> S^1, then V is open.
         For each w \<in> V, pick evenly covered U \<ni> w. The preimage q^{-1}(U) = \<Union>V_i
         with q|V_i homeomorphisms. V_i \<inter> q^{-1}(V) is open in V_i (since q^{-1}(V) open).
         q(V_i \<inter> q^{-1}(V)) = U \<inter> V is open in S^1 (homeomorphism maps open to open).
         So w has open neighborhood U \<inter> V \<subseteq> V. Hence V is open.\<close>
      have hquot_cond: "\<forall>V. V \<subseteq> top1_S1 \<longrightarrow>
          ({z \<in> top1_S1. q z \<in> V} \<in> top1_S1_topology \<longrightarrow> V \<in> top1_S1_topology)"
      proof (intro allI impI)
        fix V assume hVsub: "V \<subseteq> top1_S1" and hpreopen: "{z \<in> top1_S1. q z \<in> V} \<in> top1_S1_topology"
        have "\<forall>w \<in> V. \<exists>U \<in> top1_S1_topology. w \<in> U \<and> U \<subseteq> V"
        proof
          fix w assume hw: "w \<in> V"
          hence hwS1: "w \<in> top1_S1" using hVsub by (by100 blast)
          obtain W where hwW: "w \<in> W" and hevenly: "top1_evenly_covered_on top1_S1 top1_S1_topology
              top1_S1 top1_S1_topology q W"
            using hq_cover hwS1 unfolding top1_covering_map_on_def by (by100 blast)
          obtain \<V> where hVi_open: "\<forall>Vi\<in>\<V>. openin_on top1_S1 top1_S1_topology Vi"
              and hVi_union: "{x \<in> top1_S1. q x \<in> W} = \<Union>\<V>"
              and hVi_homeo: "\<forall>Vi\<in>\<V>. top1_homeomorphism_on Vi (subspace_topology top1_S1 top1_S1_topology Vi)
                  W (subspace_topology top1_S1 top1_S1_topology W) q"
            using hevenly unfolding top1_evenly_covered_on_def by auto
          have "w \<in> q ` top1_S1" using hq_surj hwS1 by simp
          then obtain z where hz: "z \<in> top1_S1" and hqz: "q z = w" by (by100 auto)
          have "z \<in> \<Union>\<V>" using hVi_union hz hqz hwW by (by100 auto)
          then obtain Vj where hVjV: "Vj \<in> \<V>" and hzVj: "z \<in> Vj" by (by100 blast)
          have hVj_sub: "Vj \<subseteq> top1_S1" using hVi_open hVjV unfolding openin_on_def by (by100 blast)
          \<comment> \<open>q|Vj: Vj \<rightarrow> W is a homeomorphism.\<close>
          have hhomeo: "top1_homeomorphism_on Vj (subspace_topology top1_S1 top1_S1_topology Vj)
              W (subspace_topology top1_S1 top1_S1_topology W) q"
            using hVi_homeo hVjV by (by100 blast)
          \<comment> \<open>q|Vj is bijective, so q(Vj \<inter> q^{-1}(V)) = W \<inter> V.\<close>
          \<comment> \<open>Vj \<inter> q^{-1}(V) is open in Vj. q maps it to an open subset of W.\<close>
          \<comment> \<open>Open in W + W open in S^1 \<Rightarrow> open in S^1.\<close>
          \<comment> \<open>Vj \<inter> q^{-1}(V) is open in Vj (intersection of opens in S^1, intersect with Vj).\<close>
          have hVj_open: "openin_on top1_S1 top1_S1_topology Vj"
            using hVi_open hVjV by (by100 blast)
          have hW_open: "openin_on top1_S1 top1_S1_topology W"
            using hevenly unfolding top1_evenly_covered_on_def by (by100 blast)
          \<comment> \<open>W is open in S^1.\<close>
          have hW_in_T: "W \<in> top1_S1_topology"
            using hW_open unfolding openin_on_def by (by100 blast)
          \<comment> \<open>q^{-1}(V) \<inter> Vj is open in S^1.\<close>
          have hVj_in_T: "Vj \<in> top1_S1_topology"
            using hVj_open unfolding openin_on_def by (by100 blast)
          have hpre_Vj: "Vj \<inter> {z \<in> top1_S1. q z \<in> V} \<in> top1_S1_topology"
          proof -
            have hfin_inter: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> top1_S1_topology \<longrightarrow> \<Inter>F \<in> top1_S1_topology"
              using hTS1q unfolding is_topology_on_def by (by100 blast)
            have "{Vj, {z \<in> top1_S1. q z \<in> V}} \<subseteq> top1_S1_topology"
              using hVj_in_T hpreopen by (by100 auto)
            moreover have "finite {Vj, {z \<in> top1_S1. q z \<in> V}}" by simp
            moreover have "{Vj, {z \<in> top1_S1. q z \<in> V}} \<noteq> {}" by simp
            ultimately have "\<Inter>{Vj, {z \<in> top1_S1. q z \<in> V}} \<in> top1_S1_topology"
              using hfin_inter by (by100 blast)
            moreover have "\<Inter>{Vj, {z \<in> top1_S1. q z \<in> V}} = Vj \<inter> {z \<in> top1_S1. q z \<in> V}" by (by100 auto)
            ultimately show ?thesis by simp
          qed
          \<comment> \<open>This is open in subspace Vj: Vj \<inter> q^{-1}(V) = Vj \<inter> (Vj \<inter> q^{-1}(V)).\<close>
          have hpre_in_Vj: "Vj \<inter> {z \<in> top1_S1. q z \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology Vj"
            unfolding subspace_topology_def using hpre_Vj by (by100 blast)
          \<comment> \<open>q|Vj is a homeomorphism, so it maps open subsets of Vj to open subsets of W.
             The inverse (inv_into Vj q) is continuous W \<rightarrow> Vj, so preimages of open-in-Vj are open-in-W.\<close>
          have hinv_cont: "top1_continuous_map_on W (subspace_topology top1_S1 top1_S1_topology W)
              Vj (subspace_topology top1_S1 top1_S1_topology Vj) (inv_into Vj q)"
            using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have himg_open_W: "{w' \<in> W. inv_into Vj q w' \<in> Vj \<inter> {z \<in> top1_S1. q z \<in> V}}
              \<in> subspace_topology top1_S1 top1_S1_topology W"
            using hinv_cont hpre_in_Vj unfolding top1_continuous_map_on_def by (by100 blast)
          \<comment> \<open>This set = W \<inter> V (since inv_into Vj q w' \<in> q^{-1}(V) iff w' \<in> V, using bijection).\<close>
          have hbij: "bij_betw q Vj W" using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have hset_eq: "{w' \<in> W. inv_into Vj q w' \<in> Vj \<inter> {z \<in> top1_S1. q z \<in> V}} = W \<inter> V"
          proof (intro set_eqI iffI)
            fix w' assume hw': "w' \<in> {w' \<in> W. inv_into Vj q w' \<in> Vj \<inter> {z \<in> top1_S1. q z \<in> V}}"
            hence "w' \<in> W" and "inv_into Vj q w' \<in> Vj" and "q (inv_into Vj q w') \<in> V" by auto
            have "w' \<in> q ` Vj" using \<open>w' \<in> W\<close> hbij unfolding bij_betw_def by (by100 blast)
            hence "q (inv_into Vj q w') = w'" by (simp add: f_inv_into_f)
            thus "w' \<in> W \<inter> V" using \<open>w' \<in> W\<close> \<open>q (inv_into Vj q w') \<in> V\<close> by simp
          next
            fix w' assume hw': "w' \<in> W \<inter> V"
            hence "w' \<in> W" and "w' \<in> V" by auto
            have "w' \<in> q ` Vj" using \<open>w' \<in> W\<close> hbij unfolding bij_betw_def by (by100 blast)
            hence hinv_Vj: "inv_into Vj q w' \<in> Vj" by (rule inv_into_into)
            hence hinv_S1: "inv_into Vj q w' \<in> top1_S1" using hVj_sub by (by100 blast)
            have "q (inv_into Vj q w') = w'" using \<open>w' \<in> q ` Vj\<close> by (simp add: f_inv_into_f)
            hence "q (inv_into Vj q w') \<in> V" using \<open>w' \<in> V\<close> by simp
            thus "w' \<in> {w' \<in> W. inv_into Vj q w' \<in> Vj \<inter> {z \<in> top1_S1. q z \<in> V}}"
              using \<open>w' \<in> W\<close> hinv_Vj hinv_S1 by (by100 auto)
          qed
          \<comment> \<open>W \<inter> V is open in subspace W, and W is open in S^1, so W \<inter> V is open in S^1.\<close>
          have "W \<inter> V \<in> subspace_topology top1_S1 top1_S1_topology W"
            using himg_open_W hset_eq by simp
          then obtain W' where hW': "W' \<in> top1_S1_topology" and hWV_eq: "W \<inter> V = W \<inter> W'"
            unfolding subspace_topology_def by (by100 blast)
          have "W \<inter> V \<in> top1_S1_topology"
          proof -
            have hfin_inter2: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> top1_S1_topology \<longrightarrow> \<Inter>F \<in> top1_S1_topology"
              using hTS1q unfolding is_topology_on_def by (by100 blast)
            have "{W, W'} \<subseteq> top1_S1_topology" using hW_in_T hW' by (by100 auto)
            moreover have "finite {W, W'}" by simp
            moreover have "{W, W'} \<noteq> ({}::(real\<times>real) set set)" by simp
            ultimately have "\<Inter>{W, W'} \<in> top1_S1_topology" using hfin_inter2 by (by100 blast)
            moreover have "\<Inter>{W, W'} = W \<inter> W'" by (by100 auto)
            ultimately show ?thesis using hWV_eq by simp
          qed
          moreover have "w \<in> W \<inter> V" using hwW hw by simp
          moreover have "W \<inter> V \<subseteq> V" by (by100 blast)
          ultimately show "\<exists>U \<in> top1_S1_topology. w \<in> U \<and> U \<subseteq> V"
            by (intro bexI[of _ "W \<inter> V"]) simp_all
        qed
        hence "V = \<Union>{U \<in> top1_S1_topology. U \<subseteq> V}" by (by100 blast)
        moreover have "\<Union>{U \<in> top1_S1_topology. U \<subseteq> V} \<in> top1_S1_topology"
          using hTS1q unfolding is_topology_on_def by (by100 auto)
        ultimately show "V \<in> top1_S1_topology" by simp
      qed
      show ?thesis unfolding top1_quotient_map_on_def
        using hTS1q hq_cont hq_surj hquot_cond by (by100 blast)
    qed
    \<comment> \<open>By Theorem 22.2: g = q∘h constant on fibers, so \<exists>f with f∘q=g and f continuous iff g continuous.\<close>
    have hg_range: "\<forall>z\<in>top1_S1. (q \<circ> h) z \<in> top1_S1"
      using hqh_cont unfolding top1_continuous_map_on_def by (by100 blast)
    obtain f where hf_range: "\<forall>w\<in>top1_S1. f w \<in> top1_S1"
        and hf_eq: "\<forall>z\<in>top1_S1. f (q z) = (q \<circ> h) z"
        and hf_cont_iff: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology f
            \<longleftrightarrow> top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (q \<circ> h)"
      using Theorem_22_2[OF hq_quotient hg_range hg_const] by blast
    have hf_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology f"
      using hf_cont_iff hqh_cont by simp
    \<comment> \<open>f = k on S^1 (both satisfy f(q(z)) = q(h(z))).\<close>
    have hfk_eq: "\<And>w. w \<in> top1_S1 \<Longrightarrow> f w = k w"
    proof -
      fix w assume hw: "w \<in> top1_S1"
      have "w \<in> q ` top1_S1" using hq_surj hw by simp
      then obtain z where hz: "z \<in> top1_S1" and hqz: "q z = w" by (by100 auto)
      have "f w = f (q z)" using hqz by simp
      also have "\<dots> = (q \<circ> h) z" using hf_eq hz by simp
      also have "\<dots> = q (h z)" by simp
      also have "\<dots> = k (q z)" using hk_eq[OF hz] by simp
      also have "\<dots> = k w" using hqz by simp
      finally show "f w = k w" .
    qed
    \<comment> \<open>k is continuous (= f on S^1, and f is continuous).\<close>
    show ?thesis
      using iffD1[OF top1_continuous_map_on_cong[of top1_S1 f k] hf_cont]
      using hfk_eq by (by100 blast)
  qed
  show ?thesis
  proof (rule that[of k])
    show "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology k" by (rule hk_cont)
    show "\<forall>z\<in>top1_S1. k ((\<lambda>(x,y). (x^2-y^2, 2*x*y)) z) = (\<lambda>(x,y). (x^2-y^2, 2*x*y)) (h z)"
      using hk_eq unfolding hq_alt q_def by simp
  qed
qed


text \<open>Helper for Theorem 57.1: if g: S^1 \<rightarrow> S^1 is continuous, antipode-preserving,
  and g(1,0) = (1,0), then g_* is nontrivial (i.e. NOT every loop maps to the trivial class).
  Proof: Steps 2+3 of Munkres' proof of Theorem 57.1.\<close>

lemma antipode_preserving_basepoint_nontrivial:
  assumes hg: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology g"
      and hanti: "top1_antipode_preserving_S1 g"
      and hg10: "g (1, 0) = (1, 0)"
  shows "\<not> (\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
      \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
            (g \<circ> f) (top1_constant_path (1, 0)))"
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
  \<comment> \<open>Step 2 is subsumed by the helper lemma applied to h (or \<rho>\<circ>h below).\<close>
  have hk_nontrivial: "\<not> (\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
      \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
            (k \<circ> f) (top1_constant_path (1, 0)))" sorry
  \<comment> \<open>Step 2 is not directly used; the nontriviality is applied to h (or \<rho>\<circ>h) below.\<close>
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
  \<comment> \<open>Remove hh_star_nontrivial — use antipode_preserving_basepoint_nontrivial directly in case split.\<close>
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
    have hh_triv: "\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
        \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
              (h \<circ> f) (top1_constant_path (1, 0))"
      using hh_trivial_at_h10 True by simp
    have hh_nontriv: "\<not> (\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
        \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
              (h \<circ> f) (top1_constant_path (1, 0)))"
      by (rule antipode_preserving_basepoint_nontrivial[OF assms(1,2) True])
    thus False using hh_triv by (by100 blast)
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
      by (rule antipode_preserving_basepoint_nontrivial[OF hrh_cont hrh_anti hrh_10])
    show False using hrh_trivial hrh_star_nontrivial by (by100 blast)
  qed
qed



end
