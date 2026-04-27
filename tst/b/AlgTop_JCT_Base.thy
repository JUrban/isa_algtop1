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
        U_right (subspace_topology top1_S1 top1_S1_topology U_right) q" sorry
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
    sorry \<comment> \<open>Same pattern: preimage of {a<0} is {x^2-y^2<0} = {|y|>|x|} = upper-left \<union> lower-right arcs.\<close>
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

end
