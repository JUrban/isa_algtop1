theory AlgTop_JCT_Base
  imports "Top0.Top1_Ch9_13" "AlgTopH.AlgTopHelpers"
begin


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
      top1_S1 top1_S1_topology ?q" sorry
  obtain k where hk_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
      top1_S1 top1_S1_topology k"
      and hk_eq: "\<forall>z\<in>top1_S1. k (?q z) = ?q (h z)"
    sorry
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

(** from *\<S>57 Theorem 57.2: no continuous antipode-preserving S^2 \<rightarrow> S^1.
    Munkres' proof: if g: S^2 \<rightarrow> S^1 is antipode-preserving, then h = g|S^1
    (equator) is antipode-preserving S^1 \<rightarrow> S^1, not nulhomotopic by 57.1.
    But g extends h over the upper hemisphere \<cong> B^2, so h IS nulhomotopic.
    Contradiction.

    (Stated as part of Theorem 57.3 below using an inline S^2 set, since
     top1_S2 is defined later in the file.) **)

(** from *\<S>57 Theorem 57.3: Borsuk-Ulam theorem for S^2.
    Munkres' proof: by contradiction. If f(x) \<ne> f(-x) for all x \<in> S^2, then
    g(x) = (f(x) - f(-x))/||f(x) - f(-x)|| is continuous antipode-preserving
    S^2 \<rightarrow> S^1, contradicting Theorem 57.2. **)
theorem Theorem_57_3_BorsukUlam:
  fixes f :: "real \<times> real \<times> real \<Rightarrow> real \<times> real"
  assumes hf: "top1_continuous_map_on {p. fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1}
    (subspace_topology UNIV
      (product_topology_on top1_open_sets
        (product_topology_on top1_open_sets top1_open_sets))
      {p. fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1})
    UNIV (product_topology_on top1_open_sets top1_open_sets) f"
  shows "\<exists>x::real\<times>real\<times>real. fst x ^ 2 + fst (snd x) ^ 2 + snd (snd x) ^ 2 = 1
    \<and> f x = f (- fst x, - fst (snd x), - snd (snd x))"
proof (rule ccontr)
  assume hno: "\<not> (\<exists>x::real\<times>real\<times>real. fst x ^ 2 + fst (snd x) ^ 2 + snd (snd x) ^ 2 = 1
    \<and> f x = f (- fst x, - fst (snd x), - snd (snd x)))"
  \<comment> \<open>By assumption, f(x) \<noteq> f(-x) for all x \<in> S^2.\<close>
  let ?S2 = "{p::real\<times>real\<times>real. fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1}"
  let ?neg = "\<lambda>x::real\<times>real\<times>real. (- fst x, - fst (snd x), - snd (snd x))"
  have hfne: "\<forall>x\<in>?S2. f x \<noteq> f (?neg x)" using hno by blast
  \<comment> \<open>Define g: S^2 \<rightarrow> S^1 by g(x) = (f(x) - f(-x)) / ||f(x) - f(-x)||.\<close>
  let ?diff = "\<lambda>x. (fst (f x) - fst (f (?neg x)), snd (f x) - snd (f (?neg x)))"
  let ?norm = "\<lambda>x. sqrt ((fst (?diff x))^2 + (snd (?diff x))^2)"
  let ?g = "\<lambda>x. (fst (?diff x) / ?norm x, snd (?diff x) / ?norm x)"
  \<comment> \<open>g is continuous (rational functions with nonzero denominator).\<close>
  have hg_cont: "top1_continuous_map_on ?S2
      (subspace_topology UNIV (product_topology_on top1_open_sets
        (product_topology_on top1_open_sets top1_open_sets)) ?S2)
      top1_S1 top1_S1_topology ?g" sorry
  \<comment> \<open>g is antipode-preserving: g(-x) = -g(x).\<close>
  have hg_anti: "\<forall>x\<in>?S2. ?g (?neg x) = (- fst (?g x), - snd (?g x))"
  proof (intro ballI)
    fix x :: "real \<times> real \<times> real" assume hx: "x \<in> ?S2"
    have hnegneg: "?neg (?neg x) = x" by (simp add: prod_eq_iff)
    have h1: "fst (?diff (?neg x)) = - fst (?diff x)" by (simp add: hnegneg)
    have h2: "snd (?diff (?neg x)) = - snd (?diff x)" by (simp add: hnegneg)
    have hpc1: "(fst (f (?neg x)) - fst (f x))\<^sup>2 = (fst (f x) - fst (f (?neg x)))\<^sup>2"
      by (rule power2_commute)
    have hpc2: "(snd (f (?neg x)) - snd (f x))\<^sup>2 = (snd (f x) - snd (f (?neg x)))\<^sup>2"
      by (rule power2_commute)
    have h3: "?norm (?neg x) = ?norm x" by (simp add: hnegneg hpc1 hpc2)
    have hd1: "fst (f (?neg x)) - fst (f x) = - (fst (f x) - fst (f (?neg x)))"
      by (by100 linarith)
    have hd2: "snd (f (?neg x)) - snd (f x) = - (snd (f x) - snd (f (?neg x)))"
      by (by100 linarith)
    show "?g (?neg x) = (- fst (?g x), - snd (?g x))"
      by (simp del: minus_diff_eq add: prod_eq_iff hnegneg h3 hd1 hd2)
  qed
  \<comment> \<open>Restrict g to the equator S^1: h = g|_{S^1}. h is antipode-preserving S^1 \<rightarrow> S^1.\<close>
  \<comment> \<open>By Theorem 57.1, h is not nulhomotopic. But g extends h over the upper hemisphere
     which is homeomorphic to B^2, so h is nulhomotopic. Contradiction.\<close>
  have hg_not_nulhomo: "\<not> top1_nulhomotopic_on ?S2
      (subspace_topology UNIV (product_topology_on top1_open_sets
        (product_topology_on top1_open_sets top1_open_sets)) ?S2)
      top1_S1 top1_S1_topology ?g" sorry
  have hg_nulhomo: "top1_nulhomotopic_on ?S2
      (subspace_topology UNIV (product_topology_on top1_open_sets
        (product_topology_on top1_open_sets top1_open_sets)) ?S2)
      top1_S1 top1_S1_topology ?g" sorry
  show False using hg_not_nulhomo hg_nulhomo by contradiction
qed


section \<open>\<S>58 Deformation Retracts and Homotopy Type\<close>

text \<open>A is a deformation retract of X: the identity map of X is homotopic
  to a map that carries all of X into A, with A fixed during the homotopy.\<close>
definition top1_deformation_retract_of_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_deformation_retract_of_on X TX A \<longleftrightarrow>
     A \<subseteq> X \<and>
     (\<exists>H. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H
          \<and> (\<forall>x\<in>X. H (x, 0) = x) \<and> (\<forall>x\<in>X. H (x, 1) \<in> A)
          \<and> (\<forall>a\<in>A. \<forall>t\<in>I_set. H (a, t) = a))"

text \<open>Homotopy equivalence: f: X\<rightarrow>Y and g: Y\<rightarrow>X with g\<circ>f \<simeq> id_X and f\<circ>g \<simeq> id_Y.\<close>
definition top1_homotopy_equivalence_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "top1_homotopy_equivalence_on X TX Y TY f g \<longleftrightarrow>
     top1_continuous_map_on X TX Y TY f \<and>
     top1_continuous_map_on Y TY X TX g \<and>
     top1_homotopic_on X TX X TX (g \<circ> f) (\<lambda>x. x) \<and>
     top1_homotopic_on Y TY Y TY (f \<circ> g) (\<lambda>y. y)"

text \<open>Spaces have the same homotopy type if there is a homotopy equivalence between them.\<close>
definition top1_same_homotopy_type_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> bool" where
  "top1_same_homotopy_type_on X TX Y TY \<longleftrightarrow>
     (\<exists>f g. top1_homotopy_equivalence_on X TX Y TY f g)"

text \<open>Homotopy equivalence is symmetric (swap f and g).\<close>
lemma top1_homotopy_equivalence_on_sym:
  assumes "top1_homotopy_equivalence_on X TX Y TY f g"
  shows "top1_homotopy_equivalence_on Y TY X TX g f"
  using assms unfolding top1_homotopy_equivalence_on_def by blast

text \<open>Same homotopy type is symmetric.\<close>
lemma top1_same_homotopy_type_on_sym:
  assumes "top1_same_homotopy_type_on X TX Y TY"
  shows "top1_same_homotopy_type_on Y TY X TX"
  using assms top1_homotopy_equivalence_on_sym
  unfolding top1_same_homotopy_type_on_def by blast

(** from \<S>58 Lemma 58.1: if h, k: (X, x_0) \<rightarrow> (Y, y_0) are homotopic with basepoint
    fixed during the homotopy, then h_* = k_* on fundamental groups. **)
lemma Lemma_58_1_basepoint_fixed:
  assumes hTX: "is_topology_on X TX"
      and hh: "top1_continuous_map_on X TX Y TY h"
      and hk: "top1_continuous_map_on X TX Y TY k"
      and hhx0: "h x0 = y0" and hkx0: "k x0 = y0"
      and hH: "\<exists>H. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY H
              \<and> (\<forall>x\<in>X. H (x, 0) = h x) \<and> (\<forall>x\<in>X. H (x, 1) = k x)
              \<and> (\<forall>t\<in>I_set. H (x0, t) = y0)"
      and hf: "top1_is_loop_on X TX x0 f"
  shows "top1_path_homotopic_on Y TY y0 y0
           (top1_induced_homomorphism_on X TX Y TY h f)
           (top1_induced_homomorphism_on X TX Y TY k f)"
proof -
  obtain H where hHcont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY H"
      and hH0: "\<forall>x\<in>X. H (x, 0) = h x" and hH1: "\<forall>x\<in>X. H (x, 1) = k x"
      and hHbase: "\<forall>t\<in>I_set. H (x0, t) = y0"
    using hH by blast
  have hfcont: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by blast
  have hf_vals: "\<forall>s\<in>I_set. f s \<in> X"
    using hfcont unfolding top1_continuous_map_on_def by blast
  have hf0: "f 0 = x0" and hf1: "f 1 = x0"
    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
    by (rule product_topology_on_is_topology_on[OF hTX hTI])
  have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
    unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
  \<comment> \<open>Continuity of (s,t) \<mapsto> (f s, t) : I \<times> I \<rightarrow> X \<times> I via Theorem_18_4.\<close>
  have hid_II': "top1_continuous_map_on (I_set \<times> I_set) II_topology
                  (I_set \<times> I_set) (product_topology_on I_top I_top) id"
    using top1_continuous_map_on_id[OF hTII] unfolding II_topology_def .
  have hpi1_II: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi1"
  proof -
    have "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top (pi1 \<circ> id)"
      using iffD1[OF Theorem_18_4[OF hTII hTI hTI] hid_II'] by blast
    thus ?thesis by (simp add: comp_def)
  qed
  have hpi2_II: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi2"
  proof -
    have "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top (pi2 \<circ> id)"
      using iffD1[OF Theorem_18_4[OF hTII hTI hTI] hid_II'] by blast
    thus ?thesis by (simp add: comp_def)
  qed
  have hfpi1: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (f \<circ> pi1)"
    by (rule top1_continuous_map_on_comp[OF hpi1_II hfcont])
  \<comment> \<open>Build (\<lambda>(s,t). (f s, t)) via Theorem_18_4.\<close>
  have hpi1_pair: "(pi1 \<circ> (\<lambda>p::real\<times>real. (f (fst p), snd p))) = f \<circ> pi1"
    unfolding pi1_def by (rule ext) simp
  have hpi2_pair: "(pi2 \<circ> (\<lambda>p::real\<times>real. (f (fst p), snd p))) = pi2"
    unfolding pi2_def by (rule ext) simp
  have hpi1_pair_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX
                         (pi1 \<circ> (\<lambda>p::real\<times>real. (f (fst p), snd p)))"
    using hfpi1 unfolding hpi1_pair .
  have hpi2_pair_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top
                         (pi2 \<circ> (\<lambda>p::real\<times>real. (f (fst p), snd p)))"
    using hpi2_II unfolding hpi2_pair .
  have hpair: "top1_continuous_map_on (I_set \<times> I_set) II_topology
                 (X \<times> I_set) (product_topology_on TX I_top)
                 (\<lambda>p::real\<times>real. (f (fst p), snd p))"
    using iffD2[OF Theorem_18_4[OF hTII hTX hTI]] hpi1_pair_cont hpi2_pair_cont
    unfolding II_topology_def by blast
  \<comment> \<open>Composition: F(s,t) = H(f s, t).\<close>
  let ?F = "\<lambda>p::real\<times>real. H (f (fst p), snd p)"
  have hFcomp: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY
                 (H \<circ> (\<lambda>p::real\<times>real. (f (fst p), snd p)))"
    by (rule top1_continuous_map_on_comp[OF hpair hHcont])
  have hFcont: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY ?F"
    using hFcomp by (simp add: comp_def)
  \<comment> \<open>Boundary values.\<close>
  have h_hf_path: "top1_is_path_on Y TY y0 y0 (h \<circ> f)"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    show "top1_continuous_map_on I_set I_top Y TY (h \<circ> f)"
      by (rule top1_continuous_map_on_comp[OF hfcont hh])
  next
    show "(h \<circ> f) 0 = y0" using hf0 hhx0 by (simp add: comp_def)
  next
    show "(h \<circ> f) 1 = y0" using hf1 hhx0 by (simp add: comp_def)
  qed
  have h_kf_path: "top1_is_path_on Y TY y0 y0 (k \<circ> f)"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    show "top1_continuous_map_on I_set I_top Y TY (k \<circ> f)"
      by (rule top1_continuous_map_on_comp[OF hfcont hk])
  next
    show "(k \<circ> f) 0 = y0" using hf0 hkx0 by (simp add: comp_def)
  next
    show "(k \<circ> f) 1 = y0" using hf1 hkx0 by (simp add: comp_def)
  qed
  have hFs0: "\<forall>s\<in>I_set. ?F (s, 0) = (h \<circ> f) s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "f s \<in> X" using hf_vals hs by blast
    hence "H (f s, 0) = h (f s)" using hH0 by blast
    thus "?F (s, 0) = (h \<circ> f) s" by (simp add: comp_def)
  qed
  have hFs1: "\<forall>s\<in>I_set. ?F (s, 1) = (k \<circ> f) s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "f s \<in> X" using hf_vals hs by blast
    hence "H (f s, 1) = k (f s)" using hH1 by blast
    thus "?F (s, 1) = (k \<circ> f) s" by (simp add: comp_def)
  qed
  have hF0t: "\<forall>t\<in>I_set. ?F (0, t) = y0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "f 0 = x0" by (rule hf0)
    hence "?F (0, t) = H (x0, t)" by simp
    also have "\<dots> = y0" using hHbase ht by blast
    finally show "?F (0, t) = y0" .
  qed
  have hF1t: "\<forall>t\<in>I_set. ?F (1, t) = y0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "f 1 = x0" by (rule hf1)
    hence "?F (1, t) = H (x0, t)" by simp
    also have "\<dots> = y0" using hHbase ht by blast
    finally show "?F (1, t) = y0" .
  qed
  show ?thesis
    unfolding top1_path_homotopic_on_def top1_induced_homomorphism_on_def
    using h_hf_path h_kf_path hFcont hFs0 hFs1 hF0t hF1t by blast
qed

(** from \<S>58 Lemma 58.5: if A \<subseteq> X, H : X\<times>I \<rightarrow> X is a homotopy from id_X
    to some map k : X \<rightarrow> X with H(a, t) \<in> A for all a \<in> A and t \<in> I,
    and \<alpha>(t) = H(x_0, t) is the "base-tracking" path from x_0 to k(x_0),
    then the basepoint-change \<alpha>\<^sup>\<hat> commutes with the induced map on \<pi>_1. **)
lemma Lemma_58_5_basepoint_change:
  fixes X :: "'a set" and TX :: "'a set set" and A :: "'a set"
    and H :: "'a \<times> real \<Rightarrow> 'a" and k :: "'a \<Rightarrow> 'a" and x0 :: 'a
  assumes hTX: "is_topology_on_strict X TX"
      and hAsub: "A \<subseteq> X"
      and hHcont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H"
      and hH0: "\<forall>x\<in>X. H (x, 0) = x"
      and hH1: "\<forall>x\<in>X. H (x, 1) = k x"
      and hHA: "\<forall>a\<in>A. \<forall>t\<in>I_set. H (a, t) \<in> A"
      and hx0A: "x0 \<in> A"
  shows "top1_is_path_on X TX x0 (k x0) (\<lambda>t. H (x0, t))"
proof -
  have hx0X: "x0 \<in> X" using hx0A hAsub by blast
  have hTX': "is_topology_on X TX" by (rule is_topology_on_strict_imp[OF hTX])
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
    by (rule product_topology_on_is_topology_on[OF hTX' hTI])
  \<comment> \<open>Continuity of t \<mapsto> (x_0, t) : I \<rightarrow> X \<times> I via Theorem_18_4.\<close>
  have hconst_x0: "top1_continuous_map_on I_set I_top X TX (\<lambda>_. x0)"
    by (rule top1_continuous_map_on_const[OF hTI hTX' hx0X])
  have hid_I: "top1_continuous_map_on I_set I_top I_set I_top id"
    by (rule top1_continuous_map_on_id[OF hTI])
  have hpi1_eq: "(pi1 \<circ> (\<lambda>t. (x0, t))) = (\<lambda>_. x0)"
    unfolding pi1_def by (rule ext) simp
  have hpi2_eq: "(pi2 \<circ> (\<lambda>t. (x0, t))) = id"
    unfolding pi2_def by (rule ext) simp
  have hpi1_cont: "top1_continuous_map_on I_set I_top X TX (pi1 \<circ> (\<lambda>t. (x0, t)))"
    using hconst_x0 unfolding hpi1_eq .
  have hpi2_cont: "top1_continuous_map_on I_set I_top I_set I_top (pi2 \<circ> (\<lambda>t. (x0, t)))"
    using hid_I unfolding hpi2_eq .
  have hpair: "top1_continuous_map_on I_set I_top (X \<times> I_set) (product_topology_on TX I_top)
                 (\<lambda>t. (x0, t))"
    using iffD2[OF Theorem_18_4[OF hTI hTX' hTI]] hpi1_cont hpi2_cont by blast
  \<comment> \<open>Composition H \<circ> (\<lambda>t. (x_0, t)) : I \<rightarrow> X is continuous.\<close>
  have hcomp: "top1_continuous_map_on I_set I_top X TX (H \<circ> (\<lambda>t. (x0, t)))"
    by (rule top1_continuous_map_on_comp[OF hpair hHcont])
  have hcont: "top1_continuous_map_on I_set I_top X TX (\<lambda>t. H (x0, t))"
    using hcomp by (simp add: comp_def)
  \<comment> \<open>Endpoints: H(x_0, 0) = x_0 and H(x_0, 1) = k x_0.\<close>
  have hstart: "H (x0, 0) = x0" using hH0 hx0X by blast
  have hend: "H (x0, 1) = k x0" using hH1 hx0X by blast
  show ?thesis
    unfolding top1_is_path_on_def
    using hcont hstart hend by simp
qed

(** from \<S>58 Theorem 58.7: a homotopy equivalence induces an isomorphism of fundamental groups.
    The strict version is trivially related.

    Munkres' proof (sketch):
    Given f and g as homotopy invgerses, Lemma 58.1 gives that (g o f)_* equals id_*
    and (f o g)_* equals id_*, so f_* and g_* are mutual invgerses in a suitable sense.
    Hence f_* is a bijection onto pi_1(Y, f x_0). **)
text \<open>Helper: continuous f: X \<rightarrow> Y preserves path homotopy.\<close>
lemma top1_continuous_preserves_path_homotopy:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_continuous_map_on X TX Y TY f"
      and hl: "top1_is_loop_on X TX x0 l"
      and hl': "top1_is_loop_on X TX x0 l'"
      and hll': "top1_path_homotopic_on X TX x0 x0 l l'"
  shows "top1_path_homotopic_on Y TY (f x0) (f x0) (f \<circ> l) (f \<circ> l')"
proof -
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hFs0: "\<forall>s\<in>I_set. F (s, 0) = l s" and hFs1: "\<forall>s\<in>I_set. F (s, 1) = l' s"
      and hF0: "\<forall>t\<in>I_set. F (0, t) = x0" and hF1: "\<forall>t\<in>I_set. F (1, t) = x0"
    using hll' unfolding top1_path_homotopic_on_def by blast
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
    unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
  let ?G = "f \<circ> F"
  have hGcont: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY ?G"
    by (rule top1_continuous_map_on_comp[OF hF hf])
  have hl0: "l 0 = x0" and hl1: "l 1 = x0"
    using hl unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  have hl'0: "l' 0 = x0" and hl'1: "l' 1 = x0"
    using hl' unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  have hfl_path: "top1_is_path_on Y TY (f x0) (f x0) (f \<circ> l)"
    unfolding top1_is_path_on_def
    using top1_continuous_map_on_comp[OF top1_is_loop_on_continuous[OF hl] hf]
    by (simp add: comp_def hl0 hl1)
  have hfl'_path: "top1_is_path_on Y TY (f x0) (f x0) (f \<circ> l')"
    unfolding top1_is_path_on_def
    using top1_continuous_map_on_comp[OF top1_is_loop_on_continuous[OF hl'] hf]
    by (simp add: comp_def hl'0 hl'1)
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using hfl_path hfl'_path hGcont hFs0 hFs1 hF0 hF1
    by (auto simp: comp_def)
qed

text \<open>Helper: continuous f sends loops to loops.\<close>
lemma top1_continuous_map_loop:
  assumes "top1_continuous_map_on X TX Y TY f"
      and "top1_is_loop_on X TX x0 l"
  shows "top1_is_loop_on Y TY (f x0) (f \<circ> l)"
proof -
  have hl0: "l 0 = x0" and hl1: "l 1 = x0"
    using assms(2) unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  show ?thesis
    unfolding top1_is_loop_on_def top1_is_path_on_def
    using top1_continuous_map_on_comp[OF top1_is_loop_on_continuous[OF assms(2)] assms(1)]
    by (simp add: comp_def hl0 hl1)
qed

text \<open>Helper: f_* sends loops at x0 to loops at f(x0), preserving loop equiv.\<close>
lemma top1_induced_preserves_loop_equiv:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_continuous_map_on X TX Y TY f"
      and hl: "top1_is_loop_on X TX x0 l"
      and hl': "top1_is_loop_on X TX x0 l'"
      and hll': "top1_loop_equiv_on X TX x0 l l'"
  shows "top1_loop_equiv_on Y TY (f x0) (f \<circ> l) (f \<circ> l')"
  unfolding top1_loop_equiv_on_def
  using top1_continuous_map_loop[OF hf hl] top1_continuous_map_loop[OF hf hl']
        top1_continuous_preserves_path_homotopy[OF hTX hf hl hl']
  using hll' unfolding top1_loop_equiv_on_def by blast

theorem Theorem_58_7:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and heq: "top1_homotopy_equivalence_on X TX Y TY f g" and hx0: "x0 \<in> X"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_fundamental_group_carrier Y TY (f x0))
           (top1_fundamental_group_mul Y TY (f x0))"
proof -
  have hf: "top1_continuous_map_on X TX Y TY f"
    using heq unfolding top1_homotopy_equivalence_on_def by blast
  have hg: "top1_continuous_map_on Y TY X TX g"
    using heq unfolding top1_homotopy_equivalence_on_def by blast
  \<comment> \<open>Define f_* on equivalence classes.\<close>
  let ?f_star = "\<lambda>c. {h. \<exists>l\<in>c. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
  \<comment> \<open>f_* maps carrier to carrier (well-definedness).\<close>
  have hfstar_class: "\<And>l. top1_is_loop_on X TX x0 l \<Longrightarrow>
    ?f_star {h. top1_loop_equiv_on X TX x0 l h} =
    {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
  proof (intro set_eqI iffI)
    fix l h assume hl: "top1_is_loop_on X TX x0 l"
    assume "h \<in> ?f_star {h. top1_loop_equiv_on X TX x0 l h}"
    then obtain l' where hl': "top1_loop_equiv_on X TX x0 l l'"
        and hh: "top1_loop_equiv_on Y TY (f x0) (f \<circ> l') h" by blast
    have hl'_loop: "top1_is_loop_on X TX x0 l'" using hl' unfolding top1_loop_equiv_on_def by blast
    have hfl_equiv: "top1_loop_equiv_on Y TY (f x0) (f \<circ> l) (f \<circ> l')"
      by (rule top1_induced_preserves_loop_equiv[OF hTX hf hl hl'_loop hl'])
    show "h \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
      using top1_loop_equiv_on_trans[OF hTY hfl_equiv hh] by simp
  next
    fix l h assume hl: "top1_is_loop_on X TX x0 l"
    assume "h \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
    hence hh: "top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h" by simp
    have "l \<in> {h. top1_loop_equiv_on X TX x0 l h}"
      using top1_loop_equiv_on_refl[OF hl] by simp
    thus "h \<in> ?f_star {h. top1_loop_equiv_on X TX x0 l h}"
      using hh by blast
  qed
  have hfstar_range: "\<forall>c\<in>top1_fundamental_group_carrier X TX x0.
      ?f_star c \<in> top1_fundamental_group_carrier Y TY (f x0)"
  proof
    fix c assume "c \<in> top1_fundamental_group_carrier X TX x0"
    then obtain l where hl: "top1_is_loop_on X TX x0 l"
        and hc: "c = {h. top1_loop_equiv_on X TX x0 l h}"
      unfolding top1_fundamental_group_carrier_def by blast
    have "?f_star c = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
      unfolding hc by (rule hfstar_class[OF hl])
    moreover have "top1_is_loop_on Y TY (f x0) (f \<circ> l)"
      by (rule top1_continuous_map_loop[OF hf hl])
    ultimately show "?f_star c \<in> top1_fundamental_group_carrier Y TY (f x0)"
      unfolding top1_fundamental_group_carrier_def by blast
  qed
  \<comment> \<open>Pointwise: f \<circ> (l1 * l2) = (f \<circ> l1) * (f \<circ> l2).\<close>
  have hf_comp_product: "\<And>l1 l2. f \<circ> top1_path_product l1 l2 = top1_path_product (f \<circ> l1) (f \<circ> l2)"
    unfolding top1_path_product_def comp_def by (rule ext) auto
  \<comment> \<open>f_* is a homomorphism.\<close>
  have hfstar_hom: "\<forall>c1\<in>top1_fundamental_group_carrier X TX x0.
    \<forall>c2\<in>top1_fundamental_group_carrier X TX x0.
    ?f_star (top1_fundamental_group_mul X TX x0 c1 c2) =
    top1_fundamental_group_mul Y TY (f x0) (?f_star c1) (?f_star c2)"
  proof (intro ballI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier X TX x0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier X TX x0"
    obtain l1 where hl1: "top1_is_loop_on X TX x0 l1"
        and hc1_eq: "c1 = {h. top1_loop_equiv_on X TX x0 l1 h}"
      using hc1 unfolding top1_fundamental_group_carrier_def by blast
    obtain l2 where hl2: "top1_is_loop_on X TX x0 l2"
        and hc2_eq: "c2 = {h. top1_loop_equiv_on X TX x0 l2 h}"
      using hc2 unfolding top1_fundamental_group_carrier_def by blast
    have hl12: "top1_is_loop_on X TX x0 (top1_path_product l1 l2)"
      unfolding top1_is_loop_on_def
      by (rule top1_path_product_is_path[OF hTX])
         (use hl1 hl2 in \<open>auto simp: top1_is_loop_on_def\<close>)
    \<comment> \<open>LHS: f_*(mul c1 c2) = f_*(class(l1*l2)) = class(f\<circ>(l1*l2)) = class((f\<circ>l1)*(f\<circ>l2)).\<close>
    have hmul_eq: "top1_fundamental_group_mul X TX x0 c1 c2
        = {h. top1_loop_equiv_on X TX x0 (top1_path_product l1 l2) h}"
      unfolding hc1_eq hc2_eq by (rule top1_fundamental_group_mul_class[OF hTX hl1 hl2])
    have hLHS: "?f_star (top1_fundamental_group_mul X TX x0 c1 c2)
        = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> top1_path_product l1 l2) h}"
      unfolding hmul_eq by (rule hfstar_class[OF hl12])
    have hLHS': "?f_star (top1_fundamental_group_mul X TX x0 c1 c2)
        = {h. top1_loop_equiv_on Y TY (f x0) (top1_path_product (f \<circ> l1) (f \<circ> l2)) h}"
      unfolding hLHS hf_comp_product ..
    \<comment> \<open>RHS: mul(f_*(c1), f_*(c2)) = mul(class(f\<circ>l1), class(f\<circ>l2)) = class((f\<circ>l1)*(f\<circ>l2)).\<close>
    have hfc1: "?f_star c1 = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l1) h}"
      unfolding hc1_eq by (rule hfstar_class[OF hl1])
    have hfc2: "?f_star c2 = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l2) h}"
      unfolding hc2_eq by (rule hfstar_class[OF hl2])
    have hfl1: "top1_is_loop_on Y TY (f x0) (f \<circ> l1)"
      by (rule top1_continuous_map_loop[OF hf hl1])
    have hfl2: "top1_is_loop_on Y TY (f x0) (f \<circ> l2)"
      by (rule top1_continuous_map_loop[OF hf hl2])
    have hRHS: "top1_fundamental_group_mul Y TY (f x0) (?f_star c1) (?f_star c2)
        = {h. top1_loop_equiv_on Y TY (f x0) (top1_path_product (f \<circ> l1) (f \<circ> l2)) h}"
      unfolding hfc1 hfc2 by (rule top1_fundamental_group_mul_class[OF hTY hfl1 hfl2])
    show "?f_star (top1_fundamental_group_mul X TX x0 c1 c2) =
          top1_fundamental_group_mul Y TY (f x0) (?f_star c1) (?f_star c2)"
      unfolding hLHS' hRHS ..
  qed
  \<comment> \<open>f_* is bijective.
     Injectivity: g_* \<circ> f_* is related to basepoint change (iso).
     Surjectivity: f_* \<circ> g_* is related to basepoint change (iso).\<close>
  have hgof: "top1_homotopic_on X TX X TX (g \<circ> f) (\<lambda>x. x)"
    using heq unfolding top1_homotopy_equivalence_on_def id_def[symmetric] by blast
  have hfog: "top1_homotopic_on Y TY Y TY (f \<circ> g) (\<lambda>y. y)"
    using heq unfolding top1_homotopy_equivalence_on_def id_def[symmetric] by blast
  \<comment> \<open>Injectivity of f_*: g_*\<circ>f_* = basepoint change (iso), so f_* injective.\<close>
  obtain H1 where hH1cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H1"
      and hH10: "\<forall>x\<in>X. H1 (x, 0) = (g \<circ> f) x" and hH11: "\<forall>x\<in>X. H1 (x, 1) = x"
    using hgof unfolding top1_homotopic_on_def id_def by blast
  let ?\<alpha>1 = "\<lambda>t. H1 (x0, t)"
  have hfstar_inj: "inj_on ?f_star (top1_fundamental_group_carrier X TX x0)"
  proof (rule inj_onI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier X TX x0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier X TX x0"
       and heq_fs: "?f_star c1 = ?f_star c2"
    obtain l1 where hl1: "top1_is_loop_on X TX x0 l1"
        and hc1_eq: "c1 = {g. top1_loop_equiv_on X TX x0 l1 g}"
      using hc1 unfolding top1_fundamental_group_carrier_def by blast
    obtain l2 where hl2: "top1_is_loop_on X TX x0 l2"
        and hc2_eq: "c2 = {g. top1_loop_equiv_on X TX x0 l2 g}"
      using hc2 unfolding top1_fundamental_group_carrier_def by blast
    \<comment> \<open>f_*(c1)=f_*(c2) \<Rightarrow> f\<circ>l1 \<simeq> f\<circ>l2 at f(x0).\<close>
    have hfl_equiv: "top1_loop_equiv_on Y TY (f x0) (f \<circ> l1) (f \<circ> l2)"
    proof -
      have "{h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l1) h}
          = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l2) h}"
        using heq_fs
        unfolding hc1_eq hc2_eq hfstar_class[OF hl1] hfstar_class[OF hl2] .
      moreover have "f \<circ> l1 \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l1) h}"
        using top1_loop_equiv_on_refl[OF top1_continuous_map_loop[OF hf hl1]] by simp
      ultimately have "f \<circ> l1 \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l2) h}" by simp
      hence "top1_loop_equiv_on Y TY (f x0) (f \<circ> l2) (f \<circ> l1)" by simp
      thus ?thesis by (rule top1_loop_equiv_on_sym)
    qed
    \<comment> \<open>Apply g: g\<circ>f\<circ>l1 \<simeq> g\<circ>f\<circ>l2 at g(f(x0)).\<close>
    have hgfl_equiv: "top1_loop_equiv_on X TX (g (f x0)) (g \<circ> f \<circ> l1) (g \<circ> f \<circ> l2)"
    proof -
      have "top1_loop_equiv_on X TX (g (f x0)) (g \<circ> (f \<circ> l1)) (g \<circ> (f \<circ> l2))"
        by (rule top1_induced_preserves_loop_equiv[OF hTY hg
            top1_continuous_map_loop[OF hf hl1]
            top1_continuous_map_loop[OF hf hl2] hfl_equiv])
      thus ?thesis by (simp add: comp_assoc)
    qed
    \<comment> \<open>By homotopy_induced_basepoint_change: g\<circ>f\<circ>li \<simeq> bc(li) at g(f(x0)).\<close>
    let ?bc = "\<lambda>l. top1_basepoint_change_on X TX x0 ((g \<circ> f) x0)
                     (top1_path_reverse ?\<alpha>1) l"
    have hH11id: "\<forall>x\<in>X. H1 (x, 1) = id x" using hH11 by simp
    note hbc_raw1 = homotopy_induced_basepoint_change[OF hTX hTX hH1cont hH10 hH11id hl1 hx0]
    have hbc1: "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l1) (?bc l1)"
    proof -
      have "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l1)
        (top1_basepoint_change_on X TX (id x0) ((g \<circ> f) x0)
           (top1_path_reverse ?\<alpha>1) (id \<circ> l1))"
        by (rule hbc_raw1)
      thus ?thesis by simp
    qed
    note hbc_raw2 = homotopy_induced_basepoint_change[OF hTX hTX hH1cont hH10 hH11id hl2 hx0]
    have hbc2: "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l2) (?bc l2)"
    proof -
      have "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l2)
        (top1_basepoint_change_on X TX (id x0) ((g \<circ> f) x0)
           (top1_path_reverse ?\<alpha>1) (id \<circ> l2))"
        by (rule hbc_raw2)
      thus ?thesis by simp
    qed
    \<comment> \<open>Chain: bc(l1) \<simeq> g\<circ>f\<circ>l1 \<simeq> g\<circ>f\<circ>l2 \<simeq> bc(l2) at g(f(x0)).\<close>
    have hgfx0: "(g \<circ> f) x0 = g (f x0)" by simp
    have hbc_equiv: "top1_loop_equiv_on X TX ((g \<circ> f) x0) (?bc l1) (?bc l2)"
    proof -
      have hgfl1': "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l1) ((g \<circ> f) \<circ> l2)"
        using hgfl_equiv by (simp add: comp_def)
      show ?thesis by (rule top1_loop_equiv_on_trans[OF hTX
          top1_loop_equiv_on_trans[OF hTX
            top1_loop_equiv_on_sym[OF hbc1] hgfl1'] hbc2])
    qed
    \<comment> \<open>bc is injective by basepoint_change_iso_via_path + roundtrip.\<close>
    have hra1: "top1_is_path_on X TX ((g \<circ> f) x0) x0 ?\<alpha>1"
    proof -
      have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
      have hconst: "top1_continuous_map_on I_set I_top X TX (\<lambda>_. x0)"
        by (rule top1_continuous_map_on_const[OF hTI hTX hx0])
      have hid_I: "top1_continuous_map_on I_set I_top I_set I_top id"
        by (rule top1_continuous_map_on_id[OF hTI])
      have hp1: "(pi1 \<circ> (\<lambda>t. (x0, t))) = (\<lambda>_. x0)" unfolding pi1_def by (rule ext) simp
      have hp2: "(pi2 \<circ> (\<lambda>t. (x0, t))) = id" unfolding pi2_def by (rule ext) simp
      have hpair: "top1_continuous_map_on I_set I_top (X \<times> I_set) (product_topology_on TX I_top)
                     (\<lambda>t. (x0, t))"
        using iffD2[OF Theorem_18_4[OF hTI hTX hTI]]
              hconst[folded hp1] hid_I[folded hp2] by blast
      have hcomp: "top1_continuous_map_on I_set I_top X TX (\<lambda>t. H1 (x0, t))"
        using top1_continuous_map_on_comp[OF hpair hH1cont] by (simp add: comp_def)
      have "?\<alpha>1 0 = (g \<circ> f) x0" using hH10 hx0 by auto
      moreover have "?\<alpha>1 1 = x0" using hH11 hx0 by auto
      ultimately show ?thesis unfolding top1_is_path_on_def using hcomp by auto
    qed
    have hrev_a1: "top1_is_path_on X TX x0 ((g \<circ> f) x0) (top1_path_reverse ?\<alpha>1)"
      by (rule top1_path_reverse_is_path[OF hra1])
    \<comment> \<open>Roundtrip: li \<simeq> inv_bc(bc(li)). So bc(l1)\<simeq>bc(l2) \<Rightarrow> l1\<simeq>l2.\<close>
    have hrt1: "top1_loop_equiv_on X TX x0 l1
        (top1_basepoint_change_on X TX ((g \<circ> f) x0) x0 ?\<alpha>1 (?bc l1))"
      unfolding top1_loop_equiv_on_def
      using hl1 top1_basepoint_change_is_loop[OF hTX hra1
              top1_basepoint_change_is_loop[OF hTX hrev_a1 hl1]]
            top1_basepoint_change_roundtrip[OF hTX hrev_a1 hl1,
              unfolded top1_path_reverse_twice] by blast
    have hrt2: "top1_loop_equiv_on X TX x0 l2
        (top1_basepoint_change_on X TX ((g \<circ> f) x0) x0 ?\<alpha>1 (?bc l2))"
      unfolding top1_loop_equiv_on_def
      using hl2 top1_basepoint_change_is_loop[OF hTX hra1
              top1_basepoint_change_is_loop[OF hTX hrev_a1 hl2]]
            top1_basepoint_change_roundtrip[OF hTX hrev_a1 hl2,
              unfolded top1_path_reverse_twice] by blast
    have hbc_cong: "top1_loop_equiv_on X TX x0
        (top1_basepoint_change_on X TX ((g \<circ> f) x0) x0 ?\<alpha>1 (?bc l1))
        (top1_basepoint_change_on X TX ((g \<circ> f) x0) x0 ?\<alpha>1 (?bc l2))"
      by (rule top1_basepoint_change_loop_equiv[OF hTX hra1
            top1_basepoint_change_is_loop[OF hTX hrev_a1 hl1]
            top1_basepoint_change_is_loop[OF hTX hrev_a1 hl2]
            hbc_equiv])
    have hl1l2: "top1_loop_equiv_on X TX x0 l1 l2"
      by (rule top1_loop_equiv_on_trans[OF hTX
          top1_loop_equiv_on_trans[OF hTX hrt1 hbc_cong]
          top1_loop_equiv_on_sym[OF hrt2]])
    show "c1 = c2"
    proof -
      have "\<And>g. top1_loop_equiv_on X TX x0 l1 g \<longleftrightarrow> top1_loop_equiv_on X TX x0 l2 g"
        using hl1l2 top1_loop_equiv_on_trans[OF hTX]
              top1_loop_equiv_on_trans[OF hTX top1_loop_equiv_on_sym[OF hl1l2]]
        by blast
      thus ?thesis unfolding hc1_eq hc2_eq by auto
    qed
  qed
  \<comment> \<open>Surjectivity: similar argument using f\<circ>g \<simeq> id.\<close>
  have hfstar_surj: "?f_star ` (top1_fundamental_group_carrier X TX x0)
      = top1_fundamental_group_carrier Y TY (f x0)"
  proof (intro set_eqI iffI)
    fix d assume "d \<in> ?f_star ` (top1_fundamental_group_carrier X TX x0)"
    thus "d \<in> top1_fundamental_group_carrier Y TY (f x0)"
      using hfstar_range by (by100 blast)
  next
    fix d assume hd: "d \<in> top1_fundamental_group_carrier Y TY (f x0)"
    \<comment> \<open>d = [m] for some loop m at f(x0) in Y.\<close>
    obtain m where hm: "top1_is_loop_on Y TY (f x0) m"
        and hd_eq: "d = {h. top1_loop_equiv_on Y TY (f x0) m h}"
      using hd unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>g\<circ>m is a loop at g(f(x0)) in X.\<close>
    have hgm: "top1_is_loop_on X TX (g (f x0)) (g \<circ> m)"
      by (rule top1_continuous_map_loop[OF hg hm])
    \<comment> \<open>Basepoint-change to x0: bc(\<alpha>1, g\<circ>m) is a loop at x0.\<close>
    have hra1: "top1_is_path_on X TX (g (f x0)) x0 ?\<alpha>1"
    proof -
      have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
      have hconst: "top1_continuous_map_on I_set I_top X TX (\<lambda>_. x0)"
        by (rule top1_continuous_map_on_const[OF hTI hTX hx0])
      have hid_I: "top1_continuous_map_on I_set I_top I_set I_top id"
        by (rule top1_continuous_map_on_id[OF hTI])
      have hp1: "(pi1 \<circ> (\<lambda>t. (x0, t))) = (\<lambda>_. x0)" unfolding pi1_def by (rule ext) simp
      have hp2: "(pi2 \<circ> (\<lambda>t. (x0, t))) = id" unfolding pi2_def by (rule ext) simp
      have hpair: "top1_continuous_map_on I_set I_top (X \<times> I_set) (product_topology_on TX I_top)
                     (\<lambda>t. (x0, t))"
        using iffD2[OF Theorem_18_4[OF hTI hTX hTI]]
              hconst[folded hp1] hid_I[folded hp2] by (by100 blast)
      have hcomp: "top1_continuous_map_on I_set I_top X TX (\<lambda>t. H1 (x0, t))"
        using top1_continuous_map_on_comp[OF hpair hH1cont] by (simp add: comp_def)
      have "?\<alpha>1 0 = (g \<circ> f) x0" using hH10 hx0 by (by100 auto)
      moreover have "?\<alpha>1 1 = x0" using hH11 hx0 by (by100 auto)
      ultimately show ?thesis unfolding top1_is_path_on_def using hcomp by (by100 auto)
    qed
    let ?bc_gm = "top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> m)"
    have hbc_loop: "top1_is_loop_on X TX x0 ?bc_gm"
      by (rule top1_basepoint_change_is_loop[OF hTX hra1 hgm])
    \<comment> \<open>c = [bc(\<alpha>1, g\<circ>m)] \<in> carrier(X, x0).\<close>
    let ?c = "{h. top1_loop_equiv_on X TX x0 ?bc_gm h}"
    have hc_mem: "?c \<in> top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def using hbc_loop by (by100 blast)
    \<comment> \<open>f_*(c) = d: use f\<circ>g \<simeq> id to relate f\<circ>bc(\<alpha>1, g\<circ>m) to a basepoint change of m.\<close>
    obtain H2 where hH2cont: "top1_continuous_map_on (Y \<times> I_set) (product_topology_on TY I_top) Y TY H2"
        and hH20: "\<forall>y\<in>Y. H2 (y, 0) = (f \<circ> g) y" and hH21: "\<forall>y\<in>Y. H2 (y, 1) = y"
      using hfog unfolding top1_homotopic_on_def id_def by (by100 blast)
    let ?\<alpha>2 = "\<lambda>t. H2 (f x0, t)"
    \<comment> \<open>By homotopy_induced_basepoint_change: (f\<circ>g)\<circ>m \<simeq> bc(rev \<alpha>2, m).\<close>
    have hfx0Y: "f x0 \<in> Y" using hf hx0 unfolding top1_continuous_map_on_def by (by100 blast)
    have hH21': "\<forall>y\<in>Y. H2 (y, 1) = id y" using hH21 by (by100 simp)
    note hbc2 = homotopy_induced_basepoint_change[OF hTY hTY hH2cont hH20 hH21' hm hfx0Y]
    \<comment> \<open>hbc2: loop_equiv ((f\<circ>g)(f x0)) ((f\<circ>g)\<circ>m) (bc(rev \<alpha>2, id\<circ>m)).\<close>
    have hbc2': "top1_loop_equiv_on Y TY (f (g (f x0))) (f \<circ> g \<circ> m)
        (top1_basepoint_change_on Y TY (f x0) (f (g (f x0)))
           (top1_path_reverse ?\<alpha>2) m)"
    proof -
      have "(\<lambda>y. f (g y)) \<circ> m = f \<circ> g \<circ> m" by (simp add: comp_def)
      moreover have "(\<lambda>y. y) \<circ> m = m" by (simp add: comp_def)
      ultimately show ?thesis using hbc2 by simp
    qed
    \<comment> \<open>f preserves path products: f \<circ> (p * q) = (f\<circ>p) * (f\<circ>q).\<close>
    have hf_comp_product: "\<And>p q. f \<circ> top1_path_product p q = top1_path_product (f \<circ> p) (f \<circ> q)"
      unfolding top1_path_product_def comp_def by (rule ext) (by100 auto)
    have hf_comp_rev: "\<And>p. f \<circ> top1_path_reverse p = top1_path_reverse (f \<circ> p)"
      unfolding top1_path_reverse_def comp_def by (rule ext) (by100 auto)
    \<comment> \<open>f \<circ> bc(\<alpha>1, g\<circ>m) = bc(f\<circ>\<alpha>1, f\<circ>g\<circ>m) since f preserves products.\<close>
    have hfbc_eq: "f \<circ> ?bc_gm = top1_basepoint_change_on Y TY (f (g (f x0))) (f x0)
        (f \<circ> ?\<alpha>1) (f \<circ> g \<circ> m)"
      unfolding top1_basepoint_change_on_def hf_comp_product hf_comp_rev
      by (simp add: comp_assoc)
    \<comment> \<open>Define \<gamma> = rev(\<alpha>2) * (f\<circ>\<alpha>1), a loop at f(x0).\<close>
    have hfa1: "top1_is_path_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1)"
    proof -
      have ha1_cont: "top1_continuous_map_on I_set I_top X TX ?\<alpha>1"
        using hra1 unfolding top1_is_path_on_def by (by100 blast)
      have "top1_continuous_map_on I_set I_top Y TY (f \<circ> ?\<alpha>1)"
        using top1_continuous_map_on_comp[OF ha1_cont hf] by (simp add: comp_assoc)
      moreover have "(f \<circ> ?\<alpha>1) 0 = f (g (f x0))" using hH10 hx0 by (by100 auto)
      moreover have "(f \<circ> ?\<alpha>1) 1 = f x0" using hH11 hx0 by (by100 auto)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    have ha2: "top1_is_path_on Y TY (f (g (f x0))) (f x0) ?\<alpha>2"
    proof -
      have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
      have hconst_fx0: "top1_continuous_map_on I_set I_top Y TY (\<lambda>_. f x0)"
        by (rule top1_continuous_map_on_const[OF hTI hTY hfx0Y])
      have hid_I: "top1_continuous_map_on I_set I_top I_set I_top id"
        by (rule top1_continuous_map_on_id[OF hTI])
      have hp1: "(pi1 \<circ> (\<lambda>t. (f x0, t))) = (\<lambda>_. f x0)" unfolding pi1_def by (rule ext) simp
      have hp2: "(pi2 \<circ> (\<lambda>t. (f x0, t))) = id" unfolding pi2_def by (rule ext) simp
      have hpair: "top1_continuous_map_on I_set I_top (Y \<times> I_set) (product_topology_on TY I_top)
                     (\<lambda>t. (f x0, t))"
        using iffD2[OF Theorem_18_4[OF hTI hTY hTI]]
              hconst_fx0[folded hp1] hid_I[folded hp2] by (by100 blast)
      have hcomp: "top1_continuous_map_on I_set I_top Y TY (\<lambda>t. H2 (f x0, t))"
        using top1_continuous_map_on_comp[OF hpair hH2cont] by (simp add: comp_def)
      have "?\<alpha>2 0 = f (g (f x0))" using hH20 hfx0Y by (by100 auto)
      moreover have "?\<alpha>2 1 = f x0" using hH21 hfx0Y by (by100 auto)
      ultimately show ?thesis unfolding top1_is_path_on_def using hcomp by (by100 auto)
    qed
    have hra2: "top1_is_path_on Y TY (f x0) (f (g (f x0))) (top1_path_reverse ?\<alpha>2)"
      by (rule top1_path_reverse_is_path[OF ha2])
    let ?\<gamma> = "top1_path_product (top1_path_reverse ?\<alpha>2) (f \<circ> ?\<alpha>1)"
    have h\<gamma>_path: "top1_is_path_on Y TY (f x0) (f x0) ?\<gamma>"
      by (rule top1_path_product_is_path[OF hTY hra2 hfa1])
    \<comment> \<open>For ANY loop m' at f(x0): f \<circ> bc(\<alpha>1, g\<circ>m') \<simeq> bc(\<gamma>, m').\<close>
    have hcomp_is_bc: "\<And>m'. top1_is_loop_on Y TY (f x0) m' \<Longrightarrow>
        top1_loop_equiv_on Y TY (f x0) (f \<circ> top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> m'))
            (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> m')"
    proof -
      fix m' assume hm': "top1_is_loop_on Y TY (f x0) m'"
      \<comment> \<open>f\<circ>bc(\<alpha>1, g\<circ>m') = bc(f\<circ>\<alpha>1, f\<circ>g\<circ>m') (f preserves products).\<close>
      have hfbc': "f \<circ> top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> m') =
          top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1) (f \<circ> g \<circ> m')"
        unfolding top1_basepoint_change_on_def hf_comp_product hf_comp_rev
        by (simp add: comp_assoc)
      \<comment> \<open>f\<circ>g\<circ>m' \<simeq> bc(rev \<alpha>2, m') by homotopy_induced_basepoint_change.\<close>
      have hbc2_m': "top1_loop_equiv_on Y TY (f (g (f x0))) (f \<circ> g \<circ> m')
          (top1_basepoint_change_on Y TY (f x0) (f (g (f x0)))
             (top1_path_reverse ?\<alpha>2) m')"
      proof -
        note hbc2_raw = homotopy_induced_basepoint_change[OF hTY hTY hH2cont hH20 hH21' hm' hfx0Y]
        have "(\<lambda>y. f (g y)) \<circ> m' = f \<circ> g \<circ> m'" by (simp add: comp_def)
        moreover have "(\<lambda>y. y) \<circ> m' = m'" by (simp add: comp_def)
        ultimately show ?thesis using hbc2_raw by simp
      qed
      \<comment> \<open>bc(f\<circ>\<alpha>1, f\<circ>g\<circ>m') \<simeq> bc(f\<circ>\<alpha>1, bc(rev\<alpha>2, m')) by bc_loop_equiv.\<close>
      have hfgm'_loop: "top1_is_loop_on Y TY (f (g (f x0))) (f \<circ> g \<circ> m')"
        using hbc2_m' unfolding top1_loop_equiv_on_def by (by100 blast)
      have hbc_ra2_m': "top1_is_loop_on Y TY (f (g (f x0)))
          (top1_basepoint_change_on Y TY (f x0) (f (g (f x0))) (top1_path_reverse ?\<alpha>2) m')"
        by (rule top1_basepoint_change_is_loop[OF hTY hra2 hm'])
      have hstep2: "top1_loop_equiv_on Y TY (f x0)
          (top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1) (f \<circ> g \<circ> m'))
          (top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1)
             (top1_basepoint_change_on Y TY (f x0) (f (g (f x0))) (top1_path_reverse ?\<alpha>2) m'))"
        by (rule top1_basepoint_change_loop_equiv[OF hTY hfa1 hfgm'_loop hbc_ra2_m' hbc2_m'])
      \<comment> \<open>bc(f\<circ>\<alpha>1, bc(rev\<alpha>2, m')) \<simeq> bc(\<gamma>, m') by double_bc.\<close>
      have hstep3: "top1_loop_equiv_on Y TY (f x0)
          (top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1)
             (top1_basepoint_change_on Y TY (f x0) (f (g (f x0))) (top1_path_reverse ?\<alpha>2) m'))
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> m')"
        by (rule double_basepoint_change_equiv[OF hTY hfa1 hra2 hm'])
      \<comment> \<open>Chain: f\<circ>bc = bc(f\<circ>\<alpha>1, f\<circ>g\<circ>m') \<simeq> bc(f\<circ>\<alpha>1, bc(rev\<alpha>2, m')) \<simeq> bc(\<gamma>, m').\<close>
      have hchain: "top1_loop_equiv_on Y TY (f x0)
          (top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1) (f \<circ> g \<circ> m'))
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> m')"
        by (rule top1_loop_equiv_on_trans[OF hTY hstep2 hstep3])
      show "top1_loop_equiv_on Y TY (f x0)
          (f \<circ> top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> m'))
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> m')"
        using hchain unfolding hfbc' .
    qed
    \<comment> \<open>Take m' = bc(rev(\<gamma>), m). By roundtrip: m \<simeq> bc(\<gamma>, m').\<close>
    let ?r\<gamma> = "top1_path_reverse ?\<gamma>"
    have hr\<gamma>: "top1_is_path_on Y TY (f x0) (f x0) ?r\<gamma>"
      by (rule top1_path_reverse_is_path[OF h\<gamma>_path])
    let ?m' = "top1_basepoint_change_on Y TY (f x0) (f x0) ?r\<gamma> m"
    have hm'_loop: "top1_is_loop_on Y TY (f x0) ?m'"
      by (rule top1_basepoint_change_is_loop[OF hTY hr\<gamma> hm])
    have hroundtrip: "top1_loop_equiv_on Y TY (f x0) m
        (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
    proof -
      have "top1_path_homotopic_on Y TY (f x0) (f x0) m
          (top1_basepoint_change_on Y TY (f x0) (f x0) (top1_path_reverse ?r\<gamma>)
            (top1_basepoint_change_on Y TY (f x0) (f x0) ?r\<gamma> m))"
        by (rule top1_basepoint_change_roundtrip[OF hTY hr\<gamma> hm])
      hence hrt: "top1_path_homotopic_on Y TY (f x0) (f x0) m
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
        by (simp add: top1_path_reverse_twice)
      have hbc_gm'_loop: "top1_is_loop_on Y TY (f x0)
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
        by (rule top1_basepoint_change_is_loop[OF hTY h\<gamma>_path hm'_loop])
      show ?thesis
        unfolding top1_loop_equiv_on_def
        using hm hbc_gm'_loop hrt by (by100 blast)
    qed
    \<comment> \<open>Construct preimage: c' = [bc(\<alpha>1, g\<circ>m')].\<close>
    have hgm': "top1_is_loop_on X TX (g (f x0)) (g \<circ> ?m')"
      by (rule top1_continuous_map_loop[OF hg hm'_loop])
    let ?c_pre = "top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> ?m')"
    have hcpre_loop: "top1_is_loop_on X TX x0 ?c_pre"
      by (rule top1_basepoint_change_is_loop[OF hTX hra1 hgm'])
    have hcpre_mem: "{h. top1_loop_equiv_on X TX x0 ?c_pre h}
        \<in> top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def using hcpre_loop by (by100 blast)
    \<comment> \<open>f_*([c']) = [f\<circ>c'] = [bc(\<gamma>, m')] by hcomp_is_bc.\<close>
    have hfcpre_equiv: "top1_loop_equiv_on Y TY (f x0)
        (f \<circ> ?c_pre) (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
      by (rule hcomp_is_bc[OF hm'_loop])
    \<comment> \<open>bc(\<gamma>, m') \<simeq> m by roundtrip (sym).\<close>
    have hbc_gm'_loop_Y: "top1_is_loop_on Y TY (f x0)
        (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
      by (rule top1_basepoint_change_is_loop[OF hTY h\<gamma>_path hm'_loop])
    have hrt_ph: "top1_path_homotopic_on Y TY (f x0) (f x0) m
        (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
      using hroundtrip unfolding top1_loop_equiv_on_def by (by100 blast)
    have hbcgm_equiv_m: "top1_loop_equiv_on Y TY (f x0)
        (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m') m"
      unfolding top1_loop_equiv_on_def
      using hbc_gm'_loop_Y hm Lemma_51_1_path_homotopic_sym[OF hrt_ph]
      by (by100 blast)
    \<comment> \<open>f\<circ>c' \<simeq> m.\<close>
    have hfcpre_m: "top1_loop_equiv_on Y TY (f x0) (f \<circ> ?c_pre) m"
      by (rule top1_loop_equiv_on_trans[OF hTY hfcpre_equiv hbcgm_equiv_m])
    \<comment> \<open>f_*([c']) = [m] = d.\<close>
    have hfstar_cpre: "?f_star {h. top1_loop_equiv_on X TX x0 ?c_pre h} = d"
    proof -
      have "?f_star {h. top1_loop_equiv_on X TX x0 ?c_pre h}
          = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> ?c_pre) h}"
        by (rule hfstar_class[OF hcpre_loop])
      also have "\<dots> = {h. top1_loop_equiv_on Y TY (f x0) m h}"
      proof (intro equalityI subsetI)
        fix h assume "h \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> ?c_pre) h}"
        thus "h \<in> {h. top1_loop_equiv_on Y TY (f x0) m h}"
          using top1_loop_equiv_on_trans[OF hTY
                  top1_loop_equiv_on_sym[OF hfcpre_m]] by (by100 simp)
      next
        fix h assume "h \<in> {h. top1_loop_equiv_on Y TY (f x0) m h}"
        thus "h \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> ?c_pre) h}"
          using top1_loop_equiv_on_trans[OF hTY hfcpre_m] by (by100 simp)
      qed
      also have "\<dots> = d" using hd_eq by simp
      finally show ?thesis .
    qed
    thus "d \<in> ?f_star ` (top1_fundamental_group_carrier X TX x0)"
      using hcpre_mem by (by100 blast)
  qed
  have hfstar_bij: "bij_betw ?f_star (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_carrier Y TY (f x0))"
    unfolding bij_betw_def using hfstar_inj hfstar_surj by blast
  have hiso: "top1_group_iso_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_carrier Y TY (f x0))
      (top1_fundamental_group_mul Y TY (f x0)) ?f_star"
    unfolding top1_group_iso_on_def top1_group_hom_on_def bij_betw_def
    using hfstar_range hfstar_hom hfstar_bij unfolding bij_betw_def by blast
  show ?thesis
    unfolding top1_groups_isomorphic_on_def using hiso by blast
qed

(** from \<S>58 Theorem 58.3: deformation retract induces isomorphism of fundamental groups.

    Munkres' proof: if A is a deformation retract of X via H, then the
    inclusion j: A \<hookrightarrow> X and the retraction r: X \<rightarrow> A = H(\<cdot>, 1) are homotopy
    invgerses. By Theorem 58.7, any homotopy equivalence induces an iso on \<pi>_1. **)

text \<open>Helper: the inclusion-induced map takes A-equivalence classes to X-equivalence classes.\<close>
lemma inclusion_induced_class:
  assumes hTX: "is_topology_on X TX" and hTA: "is_topology_on A TA"
      and hAsub: "A \<subseteq> X" and hTA_eq: "TA = subspace_topology X TX A"
      and hj: "top1_continuous_map_on A TA X TX id"
      and hf: "top1_is_loop_on A TA x0 f"
  shows "top1_fundamental_group_induced_on A TA x0 X TX x0 id
      {g. top1_loop_equiv_on A TA x0 f g}
    = {k. top1_loop_equiv_on X TX x0 f k}"
proof (intro set_eqI iffI)
  fix k assume "k \<in> top1_fundamental_group_induced_on A TA x0 X TX x0 id
      {g. top1_loop_equiv_on A TA x0 f g}"
  then obtain g where hfg: "top1_loop_equiv_on A TA x0 f g"
      and hgk: "top1_loop_equiv_on X TX x0 (id \<circ> g) k"
    unfolding top1_fundamental_group_induced_on_def by (by100 blast)
  have hg_loop: "top1_is_loop_on A TA x0 g"
    using hfg unfolding top1_loop_equiv_on_def by (by100 blast)
  have hfg_X: "top1_loop_equiv_on X TX x0 f g"
    using top1_induced_preserves_loop_equiv[OF hTA hj hf hg_loop hfg]
    by (simp add: comp_def)
  have hgk': "top1_loop_equiv_on X TX x0 g k"
    using hgk by (simp add: comp_def)
  show "k \<in> {k. top1_loop_equiv_on X TX x0 f k}"
    using top1_loop_equiv_on_trans[OF hTX hfg_X hgk'] by simp
next
  fix k assume hk: "k \<in> {k. top1_loop_equiv_on X TX x0 f k}"
  hence hfk: "top1_loop_equiv_on X TX x0 f k" by simp
  have hff: "top1_loop_equiv_on A TA x0 f f"
    by (rule top1_loop_equiv_on_refl[OF hf])
  have hfk': "top1_loop_equiv_on X TX x0 (id \<circ> f) k"
    using hfk by (simp add: comp_def)
  show "k \<in> top1_fundamental_group_induced_on A TA x0 X TX x0 id
      {g. top1_loop_equiv_on A TA x0 f g}"
    unfolding top1_fundamental_group_induced_on_def
    apply (rule CollectI)
    apply (rule bexI[of _ f])
    apply (rule hfk')
    apply (rule CollectI)
    apply (rule hff)
    done
qed

text \<open>Helper for Theorem 58.3: the inclusion-induced map on \<pi>_1 classes is
  a group isomorphism when the inclusion has a retraction homotopic to id.\<close>
lemma inclusion_retraction_iso:
  assumes hTX: "is_topology_on X TX" and hTA: "is_topology_on A TA"
      and hAsub: "A \<subseteq> X" and hTA_eq: "TA = subspace_topology X TX A"
      and hj: "top1_continuous_map_on A TA X TX id"
      and hr: "top1_continuous_map_on X TX A TA r"
      and hrj: "\<forall>a\<in>A. r a = a"
      and hjr: "\<And>f. top1_is_loop_on X TX x0 f \<Longrightarrow>
          top1_path_homotopic_on X TX x0 x0 (r \<circ> f) f"
      and hx0: "x0 \<in> A"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier A TA x0)
           (top1_fundamental_group_mul A TA x0)
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)"
proof -
  \<comment> \<open>The inclusion j: A \<hookrightarrow> X induces j_*: \<pi>_1(A) \<rightarrow> \<pi>_1(X).
     Step 1 (Injectivity): If j_*[f] = [const] in \<pi>_1(X), then f \<simeq> const in X.
     Apply r: r\<circ>f \<simeq> r\<circ>const = const in A. But r\<circ>f = f (since f \<subseteq> A and r|A = id).
     So f \<simeq> const in A. Hence j_* is injective.
     Step 2 (Surjectivity): For any loop f in X, hjr gives f \<simeq> r\<circ>f in X.
     r\<circ>f is a loop in A, so [f] = j_*[r\<circ>f]. Hence j_* is surjective.
     Step 3 (Homomorphism): j_* preserves products by functoriality.\<close>
  let ?j_star = "top1_fundamental_group_induced_on A TA x0 X TX x0 id"
  have hj_inj: "inj_on ?j_star (top1_fundamental_group_carrier A TA x0)"
  proof (rule inj_onI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier A TA x0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier A TA x0"
       and heq: "?j_star c1 = ?j_star c2"
    obtain f where hf: "top1_is_loop_on A TA x0 f"
        and hc1_eq: "c1 = {g. top1_loop_equiv_on A TA x0 f g}"
      using hc1 unfolding top1_fundamental_group_carrier_def by (by100 blast)
    obtain g where hg: "top1_is_loop_on A TA x0 g"
        and hc2_eq: "c2 = {h. top1_loop_equiv_on A TA x0 g h}"
      using hc2 unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>j_*(c1) = [f]_X, j_*(c2) = [g]_X.\<close>
    have hjc1: "?j_star c1 = {k. top1_loop_equiv_on X TX x0 f k}"
      unfolding hc1_eq by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hf])
    have hjc2: "?j_star c2 = {k. top1_loop_equiv_on X TX x0 g k}"
      unfolding hc2_eq by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hg])
    \<comment> \<open>[f]_X = [g]_X, so f \<simeq>_X g.\<close>
    have hfg_X: "top1_loop_equiv_on X TX x0 f g"
    proof -
      have hf_X: "top1_is_loop_on X TX x0 f"
        using top1_continuous_map_loop[OF hj hf] by (simp add: comp_def)
      have hclass_eq: "{k. top1_loop_equiv_on X TX x0 f k}
          = {k. top1_loop_equiv_on X TX x0 g k}"
        using heq hjc1 hjc2 by simp
      have "top1_loop_equiv_on X TX x0 f f"
        by (rule top1_loop_equiv_on_refl[OF hf_X])
      hence "f \<in> {k. top1_loop_equiv_on X TX x0 f k}" by simp
      hence "f \<in> {k. top1_loop_equiv_on X TX x0 g k}"
        using hclass_eq by simp
      hence "top1_loop_equiv_on X TX x0 g f" by simp
      thus ?thesis by (rule top1_loop_equiv_on_sym)
    qed
    \<comment> \<open>Apply r: r\<circ>f \<simeq>_A r\<circ>g.\<close>
    have hfg_hom_X: "top1_path_homotopic_on X TX x0 x0 f g"
      using hfg_X unfolding top1_loop_equiv_on_def by (by100 blast)
    have hrf_rg_A: "top1_path_homotopic_on A TA (r x0) (r x0) (r \<circ> f) (r \<circ> g)"
      by (rule continuous_preserves_path_homotopic[OF hTX hTA hr hfg_hom_X])
    have hrx0: "r x0 = x0" using hrj hx0 by (by100 blast)
    have hrf_rg_A': "top1_path_homotopic_on A TA x0 x0 (r \<circ> f) (r \<circ> g)"
      using hrf_rg_A unfolding hrx0 .
    \<comment> \<open>r\<circ>f = f and r\<circ>g = g (since f, g map into A and r|A = id).\<close>
    have hf_mem: "\<forall>s\<in>I_set. f s \<in> A"
      using hf unfolding top1_is_loop_on_def top1_is_path_on_def
        top1_continuous_map_on_def by (by100 blast)
    have hg_mem: "\<forall>s\<in>I_set. g s \<in> A"
      using hg unfolding top1_is_loop_on_def top1_is_path_on_def
        top1_continuous_map_on_def by (by100 blast)
    have hrf_eq_f: "\<forall>s\<in>I_set. (r \<circ> f) s = f s"
    proof (intro ballI)
      fix s assume "s \<in> I_set"
      have "f s \<in> A" using hf_mem \<open>s \<in> I_set\<close> by (by100 blast)
      thus "(r \<circ> f) s = f s" using hrj by (simp add: comp_def)
    qed
    have hrg_eq_g: "\<forall>s\<in>I_set. (r \<circ> g) s = g s"
    proof (intro ballI)
      fix s assume "s \<in> I_set"
      have "g s \<in> A" using hg_mem \<open>s \<in> I_set\<close> by (by100 blast)
      thus "(r \<circ> g) s = g s" using hrj by (simp add: comp_def)
    qed
    \<comment> \<open>Transfer: f \<simeq>_A r\<circ>f and g \<simeq>_A r\<circ>g (by loop_agree_on_I).\<close>
    have hf_rf: "top1_path_homotopic_on A TA x0 x0 f (r \<circ> f)"
      using conjunct2[OF loop_agree_on_I[OF hf hrf_eq_f]] .
    have hg_rg: "top1_path_homotopic_on A TA x0 x0 g (r \<circ> g)"
      using conjunct2[OF loop_agree_on_I[OF hg hrg_eq_g]] .
    \<comment> \<open>Chain: f \<simeq>_A r\<circ>f \<simeq>_A r\<circ>g \<simeq>_A g.\<close>
    have hf_rg: "top1_path_homotopic_on A TA x0 x0 f (r \<circ> g)"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTA hf_rf hrf_rg_A'])
    have hrg_g: "top1_path_homotopic_on A TA x0 x0 (r \<circ> g) g"
      by (rule Lemma_51_1_path_homotopic_sym[OF hg_rg])
    have hfg_A: "top1_path_homotopic_on A TA x0 x0 f g"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTA hf_rg hrg_g])
    have hfg_equiv: "top1_loop_equiv_on A TA x0 f g"
      unfolding top1_loop_equiv_on_def using hf hg hfg_A by (by100 blast)
    show "c1 = c2"
    proof -
      have "\<And>h. top1_loop_equiv_on A TA x0 f h \<longleftrightarrow> top1_loop_equiv_on A TA x0 g h"
        using hfg_equiv top1_loop_equiv_on_trans[OF hTA]
              top1_loop_equiv_on_trans[OF hTA top1_loop_equiv_on_sym[OF hfg_equiv]]
        by (by100 blast)
      thus ?thesis unfolding hc1_eq hc2_eq by auto
    qed
  qed
  have hj_surj: "?j_star ` (top1_fundamental_group_carrier A TA x0)
      = top1_fundamental_group_carrier X TX x0"
  proof (intro set_eqI iffI)
    fix c assume "c \<in> ?j_star ` (top1_fundamental_group_carrier A TA x0)"
    then obtain c_A where hcA: "c_A \<in> top1_fundamental_group_carrier A TA x0"
        and hc_eq: "c = ?j_star c_A" by (by100 blast)
    obtain f where hf: "top1_is_loop_on A TA x0 f"
        and hcA_eq: "c_A = {g. top1_loop_equiv_on A TA x0 f g}"
      using hcA unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hjc: "c = {k. top1_loop_equiv_on X TX x0 f k}"
      unfolding hc_eq hcA_eq
      by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hf])
    have hf_X: "top1_is_loop_on X TX x0 f"
      using top1_continuous_map_loop[OF hj hf] by (simp add: comp_def)
    show "c \<in> top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def hjc
      using hf_X by (by100 blast)
  next
    fix c assume hc: "c \<in> top1_fundamental_group_carrier X TX x0"
    obtain f where hf: "top1_is_loop_on X TX x0 f"
        and hc_eq: "c = {g. top1_loop_equiv_on X TX x0 f g}"
      using hc unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>r\<circ>f is a loop in A.\<close>
    have hrf_loop: "top1_is_loop_on A TA x0 (r \<circ> f)"
    proof -
      have hrf: "top1_is_loop_on A TA (r x0) (r \<circ> f)"
        by (rule top1_continuous_map_loop[OF hr hf])
      have hrx0: "r x0 = x0" using hrj hx0 by (by100 blast)
      show ?thesis using hrf unfolding hrx0 .
    qed
    \<comment> \<open>j_*([r\<circ>f]_A) = [r\<circ>f]_X.\<close>
    let ?c_A = "{g. top1_loop_equiv_on A TA x0 (r \<circ> f) g}"
    have hcA_mem: "?c_A \<in> top1_fundamental_group_carrier A TA x0"
      unfolding top1_fundamental_group_carrier_def using hrf_loop by (by100 blast)
    have hjcA: "?j_star ?c_A = {k. top1_loop_equiv_on X TX x0 (r \<circ> f) k}"
      by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hrf_loop])
    \<comment> \<open>r\<circ>f \<simeq> f in X (by hjr), so [r\<circ>f]_X = [f]_X.\<close>
    have hrf_f: "top1_path_homotopic_on X TX x0 x0 (r \<circ> f) f"
      by (rule hjr[OF hf])
    have hrf_equiv_f: "top1_loop_equiv_on X TX x0 (r \<circ> f) f"
      unfolding top1_loop_equiv_on_def using hrf_f
      using top1_continuous_map_loop[OF hj hrf_loop] hf
      by (simp add: comp_def top1_is_loop_on_def)
    have hclass_eq: "{k. top1_loop_equiv_on X TX x0 (r \<circ> f) k}
        = {k. top1_loop_equiv_on X TX x0 f k}"
    proof (intro set_eqI iffI)
      fix k assume "k \<in> {k. top1_loop_equiv_on X TX x0 (r \<circ> f) k}"
      hence hk: "top1_loop_equiv_on X TX x0 (r \<circ> f) k" by simp
      have "top1_loop_equiv_on X TX x0 f (r \<circ> f)"
        by (rule top1_loop_equiv_on_sym[OF hrf_equiv_f])
      thus "k \<in> {k. top1_loop_equiv_on X TX x0 f k}"
        using top1_loop_equiv_on_trans[OF hTX _ hk] by simp
    next
      fix k assume "k \<in> {k. top1_loop_equiv_on X TX x0 f k}"
      hence hk: "top1_loop_equiv_on X TX x0 f k" by simp
      thus "k \<in> {k. top1_loop_equiv_on X TX x0 (r \<circ> f) k}"
        using top1_loop_equiv_on_trans[OF hTX hrf_equiv_f] by simp
    qed
    show "c \<in> ?j_star ` (top1_fundamental_group_carrier A TA x0)"
      using hcA_mem unfolding hc_eq hjcA[symmetric] hclass_eq[symmetric] by (by100 blast)
  qed
  have hj_hom: "\<forall>c\<in>top1_fundamental_group_carrier A TA x0.
      \<forall>d\<in>top1_fundamental_group_carrier A TA x0.
      ?j_star (top1_fundamental_group_mul A TA x0 c d)
      = top1_fundamental_group_mul X TX x0 (?j_star c) (?j_star d)"
  proof (intro ballI)
    fix c d assume hc: "c \<in> top1_fundamental_group_carrier A TA x0"
        and hd: "d \<in> top1_fundamental_group_carrier A TA x0"
    obtain f where hf: "top1_is_loop_on A TA x0 f"
        and hc_eq: "c = {g. top1_loop_equiv_on A TA x0 f g}"
      using hc unfolding top1_fundamental_group_carrier_def by (by100 blast)
    obtain g where hg: "top1_is_loop_on A TA x0 g"
        and hd_eq: "d = {h. top1_loop_equiv_on A TA x0 g h}"
      using hd unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>c \<cdot> d = [f*g]_A by mul_class.\<close>
    have hcd: "top1_fundamental_group_mul A TA x0 c d
        = {h. top1_loop_equiv_on A TA x0 (top1_path_product f g) h}"
      unfolding hc_eq hd_eq
      by (rule top1_fundamental_group_mul_class[OF hTA hf hg])
    \<comment> \<open>f*g is a loop in A.\<close>
    have hfg_loop: "top1_is_loop_on A TA x0 (top1_path_product f g)"
      by (rule top1_path_product_is_loop[OF hTA hf hg])
    \<comment> \<open>j_*(c\<cdot>d) = j_*([f*g]_A) = [f*g]_X.\<close>
    have hjcd: "?j_star (top1_fundamental_group_mul A TA x0 c d)
        = {k. top1_loop_equiv_on X TX x0 (top1_path_product f g) k}"
      unfolding hcd
      by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hfg_loop])
    \<comment> \<open>j_*(c) = [f]_X, j_*(d) = [g]_X.\<close>
    have hjc: "?j_star c = {k. top1_loop_equiv_on X TX x0 f k}"
      unfolding hc_eq
      by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hf])
    have hjd: "?j_star d = {k. top1_loop_equiv_on X TX x0 g k}"
      unfolding hd_eq
      by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hg])
    \<comment> \<open>f, g are loops in X (since A \<subseteq> X and inclusion is continuous).\<close>
    have hf_X: "top1_is_loop_on X TX x0 f"
      using top1_continuous_map_loop[OF hj hf] by (simp add: comp_def)
    have hg_X: "top1_is_loop_on X TX x0 g"
      using top1_continuous_map_loop[OF hj hg] by (simp add: comp_def)
    \<comment> \<open>[f]_X \<cdot> [g]_X = [f*g]_X by mul_class.\<close>
    have hjcd': "top1_fundamental_group_mul X TX x0 (?j_star c) (?j_star d)
        = {k. top1_loop_equiv_on X TX x0 (top1_path_product f g) k}"
      unfolding hjc hjd
      by (rule top1_fundamental_group_mul_class[OF hTX hf_X hg_X])
    show "?j_star (top1_fundamental_group_mul A TA x0 c d)
        = top1_fundamental_group_mul X TX x0 (?j_star c) (?j_star d)"
      unfolding hjcd hjcd' ..
  qed
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
  proof (intro exI conjI)
    show "top1_group_hom_on (top1_fundamental_group_carrier A TA x0)
        (top1_fundamental_group_mul A TA x0)
        (top1_fundamental_group_carrier X TX x0)
        (top1_fundamental_group_mul X TX x0) ?j_star"
      unfolding top1_group_hom_on_def
    proof (intro conjI ballI)
      fix c assume hc: "c \<in> top1_fundamental_group_carrier A TA x0"
      show "?j_star c \<in> top1_fundamental_group_carrier X TX x0"
        using hj_surj hc by (by100 blast)
    next
      fix c d assume hc: "c \<in> top1_fundamental_group_carrier A TA x0"
          and hd: "d \<in> top1_fundamental_group_carrier A TA x0"
      show "?j_star (top1_fundamental_group_mul A TA x0 c d)
          = top1_fundamental_group_mul X TX x0 (?j_star c) (?j_star d)"
        using hj_hom hc hd by (by100 blast)
    qed
    show "bij_betw ?j_star (top1_fundamental_group_carrier A TA x0)
        (top1_fundamental_group_carrier X TX x0)"
      unfolding bij_betw_def using hj_inj hj_surj by (by100 blast)
  qed
qed

theorem Theorem_58_3:
  assumes hdef: "top1_deformation_retract_of_on X TX A"
      and hTX: "is_topology_on X TX"
      and hx0: "x0 \<in> A"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier A (subspace_topology X TX A) x0)
           (top1_fundamental_group_mul A (subspace_topology X TX A) x0)
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)"
proof -
  obtain H where hAsub: "A \<subseteq> X"
      and hH: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H"
      and hH0: "\<forall>x\<in>X. H (x, 0) = x" and hH1: "\<forall>x\<in>X. H (x, 1) \<in> A"
      and hHA: "\<forall>a\<in>A. \<forall>t\<in>I_set. H (a, t) = a"
    using hdef unfolding top1_deformation_retract_of_on_def by blast
  let ?TA = "subspace_topology X TX A"
  have hTA: "is_topology_on A ?TA"
    by (rule subspace_topology_is_topology_on[OF hTX hAsub])
  \<comment> \<open>j = id (inclusion) and r = H(\<cdot>,1) (retraction) form a homotopy equivalence.
     By Theorem 58.7, this gives the isomorphism.\<close>
  let ?r = "\<lambda>x. H (x, 1::real)"
  \<comment> \<open>1. Inclusion id: A \<rightarrow> X is continuous.\<close>
  have hj_cont: "top1_continuous_map_on A ?TA X TX id"
    by (rule top1_continuous_map_on_subspace_restrict[OF top1_continuous_map_on_id[OF hTX] hAsub])
  \<comment> \<open>2. Retraction r: X \<rightarrow> A is continuous.\<close>
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have hpair1: "top1_continuous_map_on X TX (X \<times> I_set) (product_topology_on TX I_top)
                  (\<lambda>x. (x, 1::real))"
  proof -
    have hc1: "top1_continuous_map_on X TX I_set I_top (\<lambda>_. 1::real)"
      by (rule top1_continuous_map_on_const[OF hTX hTI h1_I])
    have hp1_eq: "pi1 \<circ> (\<lambda>x. (x, 1::real)) = id" unfolding pi1_def by (rule ext) simp
    have hp1: "top1_continuous_map_on X TX X TX (pi1 \<circ> (\<lambda>x. (x, 1::real)))"
      unfolding hp1_eq by (rule top1_continuous_map_on_id[OF hTX])
    have hp2_eq: "pi2 \<circ> (\<lambda>x. (x, 1::real)) = (\<lambda>_. 1::real)" unfolding pi2_def by (rule ext) simp
    have hp2: "top1_continuous_map_on X TX I_set I_top (pi2 \<circ> (\<lambda>x. (x, 1::real)))"
      unfolding hp2_eq by (rule hc1)
    show ?thesis
      using iffD2[OF Theorem_18_4[OF hTX hTX hTI, of "\<lambda>x. (x, 1::real)"]]
      hp1 hp2 by blast
  qed
  have hr_cont_X: "top1_continuous_map_on X TX X TX ?r"
    using top1_continuous_map_on_comp[OF hpair1 hH] by (simp add: comp_def)
  have hr_img: "?r ` X \<subseteq> A" using hH1 by auto
  have hr_cont: "top1_continuous_map_on X TX A ?TA ?r"
    by (rule top1_continuous_map_on_codomain_shrink[OF hr_cont_X hr_img hAsub])
  \<comment> \<open>3. r \<circ> id ≃ id_A: since H(a,1)=a for a\<in>A, r\<circ>id = id on A. Trivial homotopy.\<close>
  have hrj_eq: "\<forall>a\<in>A. ?r (id a) = id a"
    using hHA h1_I by auto
  have hrj_hom: "top1_homotopic_on A ?TA A ?TA (?r \<circ> id) id"
  proof -
    have hrj_fun_eq: "\<And>a. a \<in> A \<Longrightarrow> (?r \<circ> id) a = id a"
      using hrj_eq by simp
    \<comment> \<open>Constant homotopy: F(a,t) = a for all t.\<close>
    have hconst_hom: "top1_continuous_map_on (A \<times> I_set) (product_topology_on ?TA I_top)
                        A ?TA (\<lambda>p. fst p)"
    proof -
      have hTP: "is_topology_on (A \<times> I_set) (product_topology_on ?TA I_top)"
        by (rule product_topology_on_is_topology_on[OF hTA hTI])
      have "top1_continuous_map_on (A \<times> I_set) (product_topology_on ?TA I_top) A ?TA (pi1 \<circ> id)"
      proof -
        have "top1_continuous_map_on (A \<times> I_set) (product_topology_on ?TA I_top) A ?TA pi1"
          by (rule top1_continuous_pi1[OF hTA hTI])
        thus ?thesis by simp
      qed
      thus ?thesis unfolding pi1_def comp_def by simp
    qed
    have hcont_rj: "top1_continuous_map_on A ?TA A ?TA (?r \<circ> id)"
      using top1_continuous_map_on_comp[OF hj_cont hr_cont] by simp
    show ?thesis
      unfolding top1_homotopic_on_def
    proof (intro conjI exI)
      show "top1_continuous_map_on A ?TA A ?TA (?r \<circ> id)" by (rule hcont_rj)
      show "top1_continuous_map_on A ?TA A ?TA id" by (rule top1_continuous_map_on_id[OF hTA])
      show "top1_continuous_map_on (A \<times> I_set) (product_topology_on ?TA I_top) A ?TA (\<lambda>p. fst p)"
        by (rule hconst_hom)
      show "\<forall>x\<in>A. fst (x, 0::real) = (?r \<circ> id) x" using hrj_fun_eq by auto
      show "\<forall>x\<in>A. fst (x, 1::real) = id x" by simp
    qed
  qed
  \<comment> \<open>4. id \<circ> r ≃ id_X: via H(x, 1-t). H(x,0)=x=id(x), H(x,1)=(id\<circ>r)(x).\<close>
  have hjr_hom: "top1_homotopic_on X TX X TX (id \<circ> ?r) id"
  proof -
    \<comment> \<open>Homotopy F(x,t) = H(x, 1-t). F(x,0) = H(x,1) = r(x), F(x,1) = H(x,0) = x.\<close>
    let ?flip = "\<lambda>(x::'a, t::real). (x, 1 - t)"
    \<comment> \<open>flip is continuous X\<times>I \<rightarrow> X\<times>I via Theorem 18.4.\<close>
    have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
      by (rule product_topology_on_is_topology_on[OF hTX hTI])
    have hflip_pi1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
        X TX (pi1 \<circ> ?flip)"
    proof -
      have "(pi1 \<circ> ?flip) = pi1" unfolding pi1_def by (rule ext) auto
      thus ?thesis using top1_continuous_pi1[OF hTX hTI] by simp
    qed
    have hflip_pi2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
        I_set I_top (pi2 \<circ> ?flip)"
    proof -
      have hpi2_flip_eq: "(pi2 \<circ> ?flip) = (\<lambda>p. 1 - pi2 p)"
        unfolding pi2_def by (rule ext) auto
      \<comment> \<open>(\<lambda>t. 1-t) is continuous I \<rightarrow> I.\<close>
      have hrev_map: "\<And>t. t \<in> I_set \<Longrightarrow> 1 - t \<in> I_set"
        unfolding top1_unit_interval_def by auto
      have hrev_cont: "continuous_on UNIV (\<lambda>t::real. 1 - t)" by (intro continuous_intros)
      have hrev_I: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
      proof -
        have "top1_continuous_map_on I_set
          (subspace_topology UNIV top1_open_sets I_set) I_set
          (subspace_topology UNIV top1_open_sets I_set) (\<lambda>t. 1 - t)"
          by (rule top1_continuous_map_on_real_subspace_open_sets[OF hrev_map hrev_cont])
        thus ?thesis unfolding top1_unit_interval_topology_def .
      qed
      have hpi2_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top pi2"
        by (rule top1_continuous_pi2[OF hTX hTI])
      have hcomp: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top
          ((\<lambda>t. 1 - t) \<circ> pi2)"
        by (rule top1_continuous_map_on_comp[OF hpi2_cont hrev_I])
      have hcomp_eq: "((\<lambda>t. 1 - t) \<circ> pi2) = (\<lambda>p. 1 - pi2 p)" by (rule ext) (simp add: comp_def)
      show ?thesis unfolding hpi2_flip_eq hcomp_eq[symmetric] by (rule hcomp)
    qed
    have hflip_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
        (X \<times> I_set) (product_topology_on TX I_top) ?flip"
      using iffD2[OF Theorem_18_4[OF hTP hTX hTI, of ?flip]]
      hflip_pi1 hflip_pi2 by blast
    have hF_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
        X TX (\<lambda>p. H (?flip p))"
      using top1_continuous_map_on_comp[OF hflip_cont hH] by (simp add: comp_def)
    have hF_eq: "\<And>p. ?flip p = (fst p, 1 - snd p)" by auto
    have hF0: "\<forall>x\<in>X. H (x, 1 - (0::real)) = (id \<circ> ?r) x" by simp
    have hF1: "\<forall>x\<in>X. H (x, 1 - (1::real)) = id x"
    proof
      fix x assume "x \<in> X"
      thus "H (x, 1 - 1) = id x" using hH0 by simp
    qed
    show ?thesis
      unfolding top1_homotopic_on_def id_def[symmetric]
    proof (intro conjI exI)
      show "top1_continuous_map_on X TX X TX (id \<circ> ?r)"
      proof -
        have "(id \<circ> ?r) = ?r" by (rule ext) (simp add: id_def)
        thus ?thesis using hr_cont_X by simp
      qed
      show "top1_continuous_map_on X TX X TX id" by (rule top1_continuous_map_on_id[OF hTX])
      show "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX
              (\<lambda>p. H (fst p, 1 - snd p))"
        using hF_cont by (simp add: case_prod_beta)
      show "\<forall>x\<in>X. H (fst (x, 0::real), 1 - snd (x, 0::real)) = (id \<circ> ?r) x"
        using hF0 by simp
      show "\<forall>x\<in>X. H (fst (x, 1::real), 1 - snd (x, 1::real)) = id x"
        using hF1 by simp
    qed
  qed
  \<comment> \<open>Following Munkres' textbook proof: use Lemma 58.1 (basepoint FIXED) directly.
     Key: H fixes x₀ ∈ A, so the basepoint-fixed version applies.\<close>
  have hx0X: "x0 \<in> X" using hx0 hAsub by blast
  \<comment> \<open>Lemma 58.1 applied: j\<circ>r \<simeq> id with x₀ fixed \<Rightarrow> (j\<circ>r)\<circ>f \<simeq> f for any loop f at x₀.\<close>
  have hjr_fixed: "\<And>f. top1_is_loop_on X TX x0 f \<Longrightarrow>
    top1_path_homotopic_on X TX x0 x0 ((\<lambda>x. ?r x) \<circ> f) f"
  proof -
    fix fl assume hfl: "top1_is_loop_on X TX x0 fl"
    \<comment> \<open>Homotopy from j\<circ>r to id that fixes x₀: use H with H(x₀,t) = x₀.\<close>
    have hH_base_fixed: "\<forall>t\<in>I_set. H (x0, t) = x0"
      using hHA hx0 by blast
    have hH_for_58_1: "\<exists>G. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX G
        \<and> (\<forall>x\<in>X. G (x, 0) = (\<lambda>x. ?r x) x) \<and> (\<forall>x\<in>X. G (x, 1) = id x)
        \<and> (\<forall>t\<in>I_set. G (x0, t) = x0)"
    proof (intro exI conjI)
      let ?G = "\<lambda>p. H (fst p, 1 - snd p)"
      show "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX ?G"
      proof -
        let ?flip = "\<lambda>(x::'a, t::real). (x, 1 - t)"
        have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
          by (rule product_topology_on_is_topology_on[OF hTX hTI])
        have hflip_pi1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX (pi1 \<circ> ?flip)"
        proof -
          have "(pi1 \<circ> ?flip) = pi1" unfolding pi1_def by (rule ext) auto
          thus ?thesis using top1_continuous_pi1[OF hTX hTI] by simp
        qed
        have hflip_pi2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top (pi2 \<circ> ?flip)"
        proof -
          have heq: "(pi2 \<circ> ?flip) = (\<lambda>p. 1 - pi2 p)" unfolding pi2_def by (rule ext) auto
          have hrev: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
          proof -
            have "top1_continuous_map_on I_set (subspace_topology UNIV top1_open_sets I_set) I_set
                (subspace_topology UNIV top1_open_sets I_set) (\<lambda>t. 1 - t)"
              by (rule top1_continuous_map_on_real_subspace_open_sets)
                 (auto simp: top1_unit_interval_def intro: continuous_intros)
            thus ?thesis unfolding top1_unit_interval_topology_def .
          qed
          have hcomp: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top ((\<lambda>t. 1 - t) \<circ> pi2)"
            by (rule top1_continuous_map_on_comp[OF top1_continuous_pi2[OF hTX hTI] hrev])
          show ?thesis unfolding heq using hcomp by (simp add: comp_def)
        qed
        have hflip_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
            (X \<times> I_set) (product_topology_on TX I_top) ?flip"
          using iffD2[OF Theorem_18_4[OF hTP hTX hTI, of ?flip]] hflip_pi1 hflip_pi2 by blast
        show ?thesis
          using top1_continuous_map_on_comp[OF hflip_cont hH] by (simp add: comp_def case_prod_beta)
      qed
      show "\<forall>x\<in>X. ?G (x, 0) = ?r x" by simp
      show "\<forall>x\<in>X. ?G (x, 1) = id x" using hH0 by simp
      show "\<forall>t\<in>I_set. ?G (x0, t) = x0"
      proof
        fix t assume "t \<in> I_set"
        hence "1 - t \<in> I_set" unfolding top1_unit_interval_def by auto
        thus "?G (x0, t) = x0" using hH_base_fixed by simp
      qed
    qed
    have hhx0: "(\<lambda>x. ?r x) x0 = x0"
      using hHA hx0 h1_I by auto
    have "top1_path_homotopic_on X TX x0 x0
        (top1_induced_homomorphism_on X TX X TX (\<lambda>x. ?r x) fl)
        (top1_induced_homomorphism_on X TX X TX id fl)"
      by (rule Lemma_58_1_basepoint_fixed[OF hTX
            hr_cont_X top1_continuous_map_on_id[OF hTX]
            hhx0 _ hH_for_58_1 hfl]) simp
    hence "top1_path_homotopic_on X TX x0 x0 ((\<lambda>x. ?r x) \<circ> fl) ((\<lambda>x. x) \<circ> fl)"
      unfolding top1_induced_homomorphism_on_def id_def by simp
    thus "top1_path_homotopic_on X TX x0 x0 ((\<lambda>x. ?r x) \<circ> fl) fl"
      by (simp add: comp_def)
  qed
  \<comment> \<open>Now: r_*\<circ>j_* = id on \<pi>_1(A) because r\<circ>j = id_A pointwise.
     And j_*\<circ>r_* = id on \<pi>_1(X) because j\<circ>r \<simeq> id with basepoint fixed (Lemma 58.1).
     So j_* is bijective (with inverse r_*), hence a group isomorphism.\<close>
  \<comment> \<open>Apply the inclusion-retraction lemma with j=id, r=H(\<cdot>,1).\<close>
  have hrj_pointwise: "\<forall>a\<in>A. ?r a = a" using hHA h1_I by auto
  show ?thesis
    by (rule inclusion_retraction_iso[OF hTX hTA hAsub refl hj_cont hr_cont hrj_pointwise hjr_fixed hx0])
qed

(** from \<S>58 Theorem 58.2: inclusion S^1 \<rightarrow> R^2-0 induces isomorphism of fundamental groups.

    Munkres' proof: S^1 is a deformation retract of R^2 - 0 via
    H(x, t) = (1-t)x + t(x/||x||). By Theorem 58.3, the inclusion induces
    an isomorphism of fundamental groups. **)
theorem Theorem_58_2_inclusion_iso:
  fixes TR2_0 :: "(real \<times> real) set set"
  defines "TR2_0 \<equiv> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0::real, 0::real)})"
  shows "top1_groups_isomorphic_on
    (top1_fundamental_group_carrier top1_S1 (subspace_topology (UNIV - {(0::real, 0::real)}) TR2_0 top1_S1) (1, 0))
    (top1_fundamental_group_mul top1_S1 (subspace_topology (UNIV - {(0::real, 0::real)}) TR2_0 top1_S1) (1, 0))
    (top1_fundamental_group_carrier (UNIV - {(0, 0)}) TR2_0 (1, 0))
    (top1_fundamental_group_mul (UNIV - {(0, 0)}) TR2_0 (1, 0))"
proof -
  \<comment> \<open>S^1 is a deformation retract of R^2 - {0} via H(x,t) = (1-t)x + t(x/|x|).\<close>
  have hdef: "top1_deformation_retract_of_on
    (UNIV - {(0::real, 0::real)})
    (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
       (UNIV - {(0::real, 0::real)}))
    top1_S1"
  proof -
    let ?R2_0 = "UNIV - {(0::real, 0::real)}"
    let ?TR = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?R2_0"
    let ?norm = "\<lambda>x::real\<times>real. sqrt (fst x ^ 2 + snd x ^ 2)"
    let ?H = "\<lambda>(x::real\<times>real, t::real). ((1-t)*fst x + t*fst x/?norm x, (1-t)*snd x + t*snd x/?norm x)"
    have hS1sub: "top1_S1 \<subseteq> ?R2_0" unfolding top1_S1_def by auto
    have hH0: "\<forall>x\<in>?R2_0. ?H (x, 0) = x" by simp
    have hH1: "\<forall>x\<in>?R2_0. ?H (x, 1) \<in> top1_S1"
    proof
      fix x :: "real \<times> real" assume hx: "x \<in> ?R2_0"
      hence hne: "x \<noteq> (0, 0)" by simp
      hence hnorm_pos: "?norm x > 0"
      proof -
        have "fst x \<noteq> 0 \<or> snd x \<noteq> 0" using hne by (auto simp: prod_eq_iff)
        hence "fst x ^ 2 + snd x ^ 2 > 0" by (auto simp: sum_power2_gt_zero_iff)
        thus ?thesis by simp
      qed
      have "?H (x, 1) = (fst x / ?norm x, snd x / ?norm x)" by simp
      moreover have "(fst x / ?norm x) ^ 2 + (snd x / ?norm x) ^ 2 = 1"
      proof -
        have hns: "?norm x ^ 2 = fst x ^ 2 + snd x ^ 2"
          using hnorm_pos by (simp add: real_sqrt_pow2)
        have h1: "(fst x / ?norm x) ^ 2 = fst x ^ 2 / (fst x ^ 2 + snd x ^ 2)"
          unfolding power_divide hns ..
        have h2: "(snd x / ?norm x) ^ 2 = snd x ^ 2 / (fst x ^ 2 + snd x ^ 2)"
          unfolding power_divide hns ..
        have hdn: "fst x ^ 2 + snd x ^ 2 \<noteq> 0"
        proof -
          have "fst x \<noteq> 0 \<or> snd x \<noteq> 0" using hne by (auto simp: prod_eq_iff)
          hence "fst x ^ 2 + snd x ^ 2 > 0" by (auto simp: sum_power2_gt_zero_iff)
          thus ?thesis by linarith
        qed
        let ?d = "fst x ^ 2 + snd x ^ 2"
        have "fst x ^ 2 / ?d + snd x ^ 2 / ?d = ?d / ?d"
          by (metis add_divide_distrib)
        also have "?d / ?d = 1" using hdn by simp
        finally show ?thesis unfolding h1 h2 .
      qed
      ultimately show "?H (x, 1) \<in> top1_S1" unfolding top1_S1_def by simp
    qed
    have hHA: "\<forall>a\<in>top1_S1. \<forall>t\<in>I_set. ?H (a, t) = a"
    proof (intro ballI)
      fix a :: "real \<times> real" and t :: real
      assume ha: "a \<in> top1_S1" and ht: "t \<in> I_set"
      have heq: "fst a ^ 2 + snd a ^ 2 = 1" using ha unfolding top1_S1_def by simp
      hence hnorm: "?norm a = 1" by (simp add: real_sqrt_eq_1_iff)
      show "?H (a, t) = a" using hnorm by (simp add: prod_eq_iff algebra_simps)
    qed
    have hHcont: "top1_continuous_map_on (?R2_0 \<times> I_set) (product_topology_on ?TR I_top) ?R2_0 ?TR ?H"
    proof -
      \<comment> \<open>Step 1: continuous_on (R²-{0})×I H.\<close>
      have hH_std: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
          ((1 - snd p) * fst (fst p) + snd p * fst (fst p) / ?norm (fst p),
           (1 - snd p) * snd (fst p) + snd p * snd (fst p) / ?norm (fst p)))"
      proof -
        \<comment> \<open>Norm and division continuous on R²-{0}.\<close>
        have hnorm_cont: "continuous_on ?R2_0 ?norm"
          by (intro continuous_on_compose2[OF continuous_on_real_sqrt]
              continuous_on_add continuous_on_power continuous_intros) auto
        have hnorm_nz: "\<forall>x\<in>?R2_0. ?norm x \<noteq> 0"
        proof (intro ballI)
          fix x :: "real \<times> real" assume "x \<in> ?R2_0"
          hence "fst x ^ 2 + snd x ^ 2 > 0"
            by (cases x) (auto simp: sum_power2_gt_zero_iff)
          thus "?norm x \<noteq> 0" by (metis less_imp_neq not_sym real_sqrt_gt_zero)
        qed
        have hfst_div: "continuous_on ?R2_0 (\<lambda>x. fst x / ?norm x)"
          by (rule continuous_on_divide) (intro continuous_intros, rule hnorm_cont, rule hnorm_nz)
        have hsnd_div: "continuous_on ?R2_0 (\<lambda>x. snd x / ?norm x)"
          by (rule continuous_on_divide) (intro continuous_intros, rule hnorm_cont, rule hnorm_nz)
        \<comment> \<open>Lift to (R²-{0})×I via composition with fst.\<close>
        have hfst_R2: "continuous_on (?R2_0 \<times> I_set) (fst::(real\<times>real)\<times>real \<Rightarrow> real\<times>real)"
          by (intro continuous_intros)
        have hfst_img: "fst ` (?R2_0 \<times> I_set) \<subseteq> ?R2_0" by (by100 auto)
        have hfdiv': "continuous_on (?R2_0 \<times> I_set) (\<lambda>p. fst (fst p) / ?norm (fst p))"
          using continuous_on_compose[OF hfst_R2 continuous_on_subset[OF hfst_div hfst_img]]
          by (simp add: comp_def)
        have hsdiv': "continuous_on (?R2_0 \<times> I_set) (\<lambda>p. snd (fst p) / ?norm (fst p))"
          using continuous_on_compose[OF hfst_R2 continuous_on_subset[OF hsnd_div hfst_img]]
          by (simp add: comp_def)
        have hid: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. p)"
          by (rule continuous_on_id)
        have h1mt: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. 1 - snd p)"
          by (intro continuous_on_diff continuous_on_const continuous_on_snd[OF hid])
        have hff: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. fst (fst p))"
          by (intro continuous_on_fst[OF continuous_on_fst[OF hid]])
        have hsf: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. snd (fst p))"
          by (intro continuous_on_snd[OF continuous_on_fst[OF hid]])
        have ht: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. snd p)"
          by (intro continuous_on_snd[OF hid])
        have htfd: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
            snd p * (fst (fst p) / ?norm (fst p)))"
          by (rule continuous_on_mult[OF ht hfdiv'])
        have htsd: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
            snd p * (snd (fst p) / ?norm (fst p)))"
          by (rule continuous_on_mult[OF ht hsdiv'])
        have hcomp1: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
            (1 - snd p) * fst (fst p) + snd p * (fst (fst p) / ?norm (fst p)))"
          by (intro continuous_on_add continuous_on_mult h1mt hff ht hfdiv')
        have hcomp2: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
            (1 - snd p) * snd (fst p) + snd p * (snd (fst p) / ?norm (fst p)))"
          by (intro continuous_on_add continuous_on_mult h1mt hsf ht hsdiv')
        show ?thesis
          using continuous_on_Pair[OF hcomp1 hcomp2] by simp
      qed
      have hH_eq: "(\<lambda>p::(real\<times>real)\<times>real.
          ((1 - snd p) * fst (fst p) + snd p * fst (fst p) / ?norm (fst p),
           (1 - snd p) * snd (fst p) + snd p * snd (fst p) / ?norm (fst p)))
        = (\<lambda>p. ?H (fst p, snd p))"
        by (rule ext) (simp add: case_prod_beta)
      have hH_std': "continuous_on (?R2_0 \<times> I_set) (\<lambda>p. ?H (fst p, snd p))"
        using hH_std unfolding hH_eq .
      \<comment> \<open>Step 2: H maps into R²-{0}.\<close>
      have hH_range: "\<And>p. p \<in> ?R2_0 \<times> I_set \<Longrightarrow> (\<lambda>p. ?H (fst p, snd p)) p \<in> ?R2_0"
      proof -
        fix p :: "(real \<times> real) \<times> real"
        assume hp: "p \<in> ?R2_0 \<times> I_set"
        have hxR2: "fst p \<in> ?R2_0" using hp by (simp add: mem_Times_iff)
        hence hxnz: "fst p \<noteq> (0, 0)" by (by100 simp)
        have htI: "snd p \<in> I_set" using hp by (simp add: mem_Times_iff)
        have hnp: "?norm (fst p) > 0"
          using hxnz by (cases "fst p") (auto simp: sum_power2_gt_zero_iff real_sqrt_gt_zero)
        \<comment> \<open>H(x,t) \<noteq> 0: if it were, both components = 0 ⟹ x = 0, contradiction.\<close>
        have "?H (fst p, snd p) \<noteq> (0, 0)"
        proof
          assume habs: "?H (fst p, snd p) = (0, 0)"
          \<comment> \<open>Component 1: (1-t)*a + t*a/|x| = 0 means a*((1-t) + t/|x|) = 0.\<close>
          have h1: "(1 - snd p) * fst (fst p) + snd p * fst (fst p) / ?norm (fst p) = 0"
            using habs by (simp add: prod_eq_iff case_prod_beta)
          have h2: "(1 - snd p) * snd (fst p) + snd p * snd (fst p) / ?norm (fst p) = 0"
            using habs by (simp add: prod_eq_iff case_prod_beta)
          \<comment> \<open>Multiply by |x| > 0: (1-t)*a*|x| + t*a = 0 and similarly for b.\<close>
          have h1': "(1 - snd p) * fst (fst p) * ?norm (fst p) + snd p * fst (fst p) = 0"
          proof -
            from h1 have "((1 - snd p) * fst (fst p) + snd p * fst (fst p) / ?norm (fst p))
                * ?norm (fst p) = 0" by (by100 simp)
            hence "(1 - snd p) * fst (fst p) * ?norm (fst p) +
                snd p * fst (fst p) / ?norm (fst p) * ?norm (fst p) = 0"
              by (simp add: algebra_simps)
            moreover have "snd p * fst (fst p) / ?norm (fst p) * ?norm (fst p)
                = snd p * fst (fst p)"
              using hnp by (by100 simp)
            ultimately show ?thesis by (by100 linarith)
          qed
          have h2': "(1 - snd p) * snd (fst p) * ?norm (fst p) + snd p * snd (fst p) = 0"
          proof -
            from h2 have "((1 - snd p) * snd (fst p) + snd p * snd (fst p) / ?norm (fst p))
                * ?norm (fst p) = 0" by (by100 simp)
            hence "(1 - snd p) * snd (fst p) * ?norm (fst p) +
                snd p * snd (fst p) / ?norm (fst p) * ?norm (fst p) = 0"
              by (simp add: algebra_simps)
            moreover have "snd p * snd (fst p) / ?norm (fst p) * ?norm (fst p)
                = snd p * snd (fst p)"
              using hnp by (by100 simp)
            ultimately show ?thesis by (by100 linarith)
          qed
          \<comment> \<open>Factor: a * ((1-t)*|x| + t) = 0 and b * ((1-t)*|x| + t) = 0.\<close>
          have hfact1: "fst (fst p) * ((1 - snd p) * ?norm (fst p) + snd p) = 0"
            using h1' by (simp add: algebra_simps)
          have hfact2: "snd (fst p) * ((1 - snd p) * ?norm (fst p) + snd p) = 0"
            using h2' by (simp add: algebra_simps)
          \<comment> \<open>(1-t)*|x| + t > 0 since |x| > 0 and t \<ge> 0, 1-t \<ge> 0.\<close>
          have hc_pos: "(1 - snd p) * ?norm (fst p) + snd p > 0"
          proof (cases "snd p = 0")
            case True thus ?thesis using hnp by (by100 simp)
          next
            case False
            have "snd p > 0" using False htI unfolding top1_unit_interval_def by (by100 simp)
            moreover have "(1 - snd p) * ?norm (fst p) \<ge> 0"
              using htI hnp unfolding top1_unit_interval_def by (by100 simp)
            ultimately show ?thesis by (by100 linarith)
          qed
          have "fst (fst p) = 0" using hfact1 hc_pos by (by100 simp)
          moreover have "snd (fst p) = 0" using hfact2 hc_pos by (by100 simp)
          ultimately show False using hxnz by (simp add: prod_eq_iff)
        qed
        thus "(\<lambda>p. ?H (fst p, snd p)) p \<in> ?R2_0"
          by (simp add: case_prod_beta)
      qed
      \<comment> \<open>Step 3: Transfer.\<close>
      have "top1_continuous_map_on (?R2_0 \<times> I_set) (product_topology_on ?TR I_top)
          ?R2_0 ?TR (\<lambda>p. ?H (fst p, snd p))"
        by (rule R2_subspace_I_continuous_on_transfer[OF hH_std' hH_range])
      moreover have "(\<lambda>p::(real\<times>real)\<times>real. ?H (fst p, snd p)) = ?H"
        by (rule ext) (simp add: case_prod_beta)
      ultimately show ?thesis by simp
    qed
    show ?thesis unfolding top1_deformation_retract_of_on_def
      using hS1sub hHcont hH0 hH1 hHA by blast
  qed
  have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
    using product_topology_on_is_topology_on[OF hTR hTR] by simp
  have hTR2_0: "is_topology_on (UNIV - {(0::real, 0::real)})
    (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))"
    by (rule subspace_topology_is_topology_on[OF hTR2]) simp
  have h10: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by simp
  have hS1_eq: "top1_S1_topology = subspace_topology
    (UNIV - {(0::real, 0::real)})
    (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))
    top1_S1"
    unfolding top1_S1_topology_def
    by (rule subspace_topology_trans[of top1_S1 "UNIV - {(0, 0)}", symmetric])
       (auto simp: top1_S1_def)
  have hdef': "top1_deformation_retract_of_on (UNIV - {(0::real, 0::real)}) TR2_0 top1_S1"
    unfolding TR2_0_def by (rule hdef)
  have hTR2_0': "is_topology_on (UNIV - {(0::real, 0::real)}) TR2_0"
    unfolding TR2_0_def by (rule hTR2_0)
  show ?thesis
    unfolding TR2_0_def[symmetric]
    by (rule Theorem_58_3[OF hdef' hTR2_0' h10])
qed

corollary Theorem_58_7_strict:
  assumes "is_topology_on_strict X TX" and "is_topology_on_strict Y TY"
    and "top1_homotopy_equivalence_on X TX Y TY f g" and "x0 \<in> X"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_fundamental_group_carrier Y TY (f x0))
           (top1_fundamental_group_mul Y TY (f x0))"
  using Theorem_58_7[OF is_topology_on_strict_imp[OF assms(1)] is_topology_on_strict_imp[OF assms(2)] assms(3) assms(4)] by blast

text \<open>Strict version: if X and Y have the same homotopy type and X is strict,
  Y is also strict.\<close>
corollary top1_same_homotopy_type_strict:
  assumes "top1_same_homotopy_type_on X TX Y TY"
  shows "top1_same_homotopy_type_on Y TY X TX"
  by (rule top1_same_homotopy_type_on_sym[OF assms])

section \<open>\<S>59 The Fundamental Group of S^n\<close>

text \<open>The n-sphere S^n embedded in R^{n+1}.\<close>
definition top1_Sn :: "nat \<Rightarrow> (nat \<Rightarrow> real) set" where
  "top1_Sn n = {x. (\<forall>i \<ge> Suc n. x i = 0) \<and> (\<Sum>i\<le>n. (x i)^2) = 1}"

(** from \<S>59 Theorem 59.1: the images of i_*: \<pi>_1(U, x_0) \<rightarrow> \<pi>_1(X, x_0) and
    j_*: \<pi>_1(V, x_0) \<rightarrow> \<pi>_1(X, x_0) generate \<pi>_1(X, x_0). Equivalently, every loop in
    X at x_0 is path-homotopic to a finite concatenation of loops, each of which
    lies entirely in U or entirely in V. **)
text \<open>Helper: a path in a subspace is a path in the ambient space. (Moved here for use in 59.1.)\<close>
lemma path_in_subspace_is_path_in_ambient':
  assumes hTX: "is_topology_on X TX" and hWX: "W \<subseteq> X"
      and hg: "top1_is_path_on W (subspace_topology X TX W) a b g"
  shows "top1_is_path_on X TX a b g"
  unfolding top1_is_path_on_def
proof (intro conjI)
  have hg_cont: "top1_continuous_map_on I_set I_top W (subspace_topology X TX W) g"
    using hg unfolding top1_is_path_on_def by (by100 blast)
  show "top1_continuous_map_on I_set I_top X TX g"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix s assume "s \<in> I_set"
    thus "g s \<in> X" using hg_cont hWX unfolding top1_continuous_map_on_def by (by100 blast)
  next
    fix V assume hV: "V \<in> TX"
    have hVW: "W \<inter> V \<in> subspace_topology X TX W"
      unfolding subspace_topology_def using hV by (by100 blast)
    have "{s \<in> I_set. g s \<in> V} = {s \<in> I_set. g s \<in> W \<inter> V}"
      using hg_cont unfolding top1_continuous_map_on_def by (by100 blast)
    also have "\<dots> \<in> I_top" using hg_cont hVW unfolding top1_continuous_map_on_def by (by100 blast)
    finally show "{s \<in> I_set. g s \<in> V} \<in> I_top" .
  qed
  show "g 0 = a" using hg unfolding top1_is_path_on_def by (by100 blast)
  show "g 1 = b" using hg unfolding top1_is_path_on_def by (by100 blast)
qed

\<comment> \<open>Helper: foldr of path products respects base homotopy.\<close>
lemma foldr_path_product_base_homotopic:
  assumes hTX: "is_topology_on X TX"
      and hpaths: "\<And>i. i < length fs \<Longrightarrow> top1_is_path_on X TX (a i) (a (Suc i)) (fs!i)"
      and hbase: "top1_path_homotopic_on X TX (a (length fs)) (a (length fs)) base1 base2"
  shows "top1_path_homotopic_on X TX (a 0) (a (length fs))
      (foldr top1_path_product fs base1) (foldr top1_path_product fs base2)"
  using assms
proof (induction fs arbitrary: a)
  case Nil thus ?case by simp
next
  case (Cons f fs')
  have hf: "top1_is_path_on X TX (a 0) (a 1) f"
    using Cons.prems(2)[of 0] by simp
  define a' where "a' i = a (Suc i)" for i
  have hfs': "\<And>i. i < length fs' \<Longrightarrow> top1_is_path_on X TX (a' i) (a' (Suc i)) (fs'!i)"
  proof -
    fix i assume "i < length fs'"
    hence "Suc i < length (f # fs')" by simp
    thus "top1_is_path_on X TX (a' i) (a' (Suc i)) (fs'!i)"
      using Cons.prems(2)[of "Suc i"] unfolding a'_def by simp
  qed
  have hbase': "top1_path_homotopic_on X TX (a' (length fs')) (a' (length fs')) base1 base2"
    using Cons.prems(3) unfolding a'_def by simp
  have hIH: "top1_path_homotopic_on X TX (a' 0) (a' (length fs'))
      (foldr top1_path_product fs' base1) (foldr top1_path_product fs' base2)"
    by (rule Cons.IH[OF Cons.prems(1) hfs' hbase'])
  have hIH': "top1_path_homotopic_on X TX (a 1) (a (Suc (length fs')))
      (foldr top1_path_product fs' base1) (foldr top1_path_product fs' base2)"
    using hIH unfolding a'_def by simp
  have "top1_path_homotopic_on X TX (a 0) (a (Suc (length fs')))
      (top1_path_product f (foldr top1_path_product fs' base1))
      (top1_path_product f (foldr top1_path_product fs' base2))"
    by (rule path_homotopic_product_right[OF Cons.prems(1) hIH' hf])
  thus ?case by simp
qed

\<comment> \<open>Helper: foldr of path products is a path.\<close>
lemma foldr_path_product_is_path:
  assumes hTX: "is_topology_on X TX"
      and hpaths: "\<And>i. i < length fs \<Longrightarrow> top1_is_path_on X TX (a i) (a (Suc i)) (fs!i)"
      and hbase: "top1_is_path_on X TX (a (length fs)) y base"
  shows "top1_is_path_on X TX (a 0) y (foldr top1_path_product fs base)"
  using assms
proof (induction fs arbitrary: a)
  case Nil thus ?case by simp
next
  case (Cons f fs')
  have hf: "top1_is_path_on X TX (a 0) (a 1) f"
    using Cons.prems(2)[of 0] by simp
  define a' where "a' i = a (Suc i)" for i
  have hfs': "\<And>i. i < length fs' \<Longrightarrow> top1_is_path_on X TX (a' i) (a' (Suc i)) (fs'!i)"
  proof -
    fix i assume "i < length fs'"
    thus "top1_is_path_on X TX (a' i) (a' (Suc i)) (fs'!i)"
      using Cons.prems(2)[of "Suc i"] unfolding a'_def by simp
  qed
  have hbase': "top1_is_path_on X TX (a' (length fs')) y base"
    using Cons.prems(3) unfolding a'_def by simp
  have hIH: "top1_is_path_on X TX (a' 0) y (foldr top1_path_product fs' base)"
    by (rule Cons.IH[OF Cons.prems(1) hfs' hbase'])
  have "top1_is_path_on X TX (a 0) y (top1_path_product f (foldr top1_path_product fs' base))"
    by (rule top1_path_product_is_path[OF Cons.prems(1) hf]) (use hIH a'_def in simp)
  thus ?case by simp
qed

\<comment> \<open>Core telescoping identity: foldr of conjugated paths = α(0) * foldr of raw paths * rev(α(n)).\<close>
lemma telescoping_core:
  assumes hTX: "is_topology_on X TX" and hx0: "x0 \<in> X"
      and hlen: "length gs = k" "length fs = k" "k \<ge> 1"
      and h\<alpha>: "\<And>i. i \<le> k \<Longrightarrow> top1_is_path_on X TX x0 (a i) (\<alpha> i)"
      and hfi: "\<And>i. i < k \<Longrightarrow> top1_is_path_on X TX (a i) (a (Suc i)) (fs!i)"
      and hgi: "\<And>i. i < k \<Longrightarrow> gs!i = top1_path_product (top1_path_product (\<alpha> i) (fs!i))
                                     (top1_path_reverse (\<alpha> (Suc i)))"
  shows "top1_path_homotopic_on X TX x0 x0
      (foldr top1_path_product gs (top1_constant_path x0))
      (top1_path_product (\<alpha> 0) (foldr top1_path_product fs
        (top1_path_product (top1_path_reverse (\<alpha> k)) (top1_constant_path x0))))"
proof -
  have hconst: "top1_is_path_on X TX x0 x0 (top1_constant_path x0)"
    by (rule top1_constant_path_is_path[OF hTX hx0])
  \<comment> \<open>Proof by induction on k. The conclusion has the form:
     foldr gs const \<simeq> \<alpha>(0) * foldr fs (rev(\<alpha>(k)) * const).
     Base k=1: double associativity.
     Step k\<rightarrow>k+1: expand g0, apply IH to tail, cancel rev(\<alpha>1)*\<alpha>1.\<close>
  show ?thesis using hlen hfi hgi h\<alpha>
  proof (induction k arbitrary: gs fs \<alpha> a)
    case 0 thus ?case by (by100 simp)
  next
    case (Suc k')
    show ?case
    proof (cases "k' = 0")
      case True
      \<comment> \<open>Base k=1: ((a0*f0)*rev(a1))*const \<simeq> a0*(f0*(rev(a1)*const)).\<close>
      show ?thesis
      proof -
        have hk1: "Suc k' = 1" using True by (by100 simp)
        obtain g0 where hgs1: "gs = [g0]"
          using Suc.prems(1) hk1 by (cases gs) (by100 simp)+
        obtain f0 where hfs1: "fs = [f0]"
          using Suc.prems(2) hk1 by (cases fs) (by100 simp)+
        have hfoldr_gs: "foldr top1_path_product gs (top1_constant_path x0)
            = top1_path_product (gs ! 0) (top1_constant_path x0)"
          unfolding hgs1 by (by100 simp)
        have hfoldr_fs: "foldr top1_path_product fs
            (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0))
            = top1_path_product (fs ! 0)
              (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0))"
          unfolding hfs1 by (by100 simp)
        have hg0: "gs ! 0 = top1_path_product (top1_path_product (\<alpha> 0) (fs ! 0))
            (top1_path_reverse (\<alpha> (Suc k')))"
          using Suc.prems(5)[of 0] hk1 by (by100 simp)
        have h\<alpha>0: "top1_is_path_on X TX x0 (a 0) (\<alpha> 0)"
          using Suc.prems(6)[of 0] by (by100 simp)
        have h\<alpha>1: "top1_is_path_on X TX x0 (a (Suc k')) (\<alpha> (Suc k'))"
          using Suc.prems(6)[of "Suc k'"] by (by100 simp)
        have hf0: "top1_is_path_on X TX (a 0) (a (Suc 0)) (fs ! 0)"
          using Suc.prems(4)[of 0] hk1 by (by100 simp)
        have hSk': "Suc 0 = Suc k'" using hk1 by (by100 simp)
        have hrev: "top1_is_path_on X TX (a (Suc k')) x0 (top1_path_reverse (\<alpha> (Suc k')))"
          by (rule top1_path_reverse_is_path[OF h\<alpha>1])
        have h\<alpha>0f0: "top1_is_path_on X TX x0 (a (Suc k')) (top1_path_product (\<alpha> 0) (fs ! 0))"
          using top1_path_product_is_path[OF hTX h\<alpha>0 hf0] hSk' by (by100 simp)
        have hrevconst: "top1_is_path_on X TX (a (Suc k')) x0
            (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0))"
          by (rule top1_path_product_is_path[OF hTX hrev hconst])
        have hassoc1: "top1_path_homotopic_on X TX x0 x0
            (top1_path_product (top1_path_product (top1_path_product (\<alpha> 0) (fs ! 0))
              (top1_path_reverse (\<alpha> (Suc k')))) (top1_constant_path x0))
            (top1_path_product (top1_path_product (\<alpha> 0) (fs ! 0))
              (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0)))"
          by (rule Lemma_51_1_path_homotopic_sym[OF
                Theorem_51_2_associativity[OF hTX h\<alpha>0f0 hrev hconst]])
        have hf0': "top1_is_path_on X TX (a 0) (a (Suc k')) (fs ! 0)"
          using hf0 hSk' by (by100 simp)
        have hassoc2: "top1_path_homotopic_on X TX x0 x0
            (top1_path_product (top1_path_product (\<alpha> 0) (fs ! 0))
              (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0)))
            (top1_path_product (\<alpha> 0) (top1_path_product (fs ! 0)
              (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0))))"
          by (rule Lemma_51_1_path_homotopic_sym[OF
                Theorem_51_2_associativity[OF hTX h\<alpha>0 hf0' hrevconst]])
        have hchain: "top1_path_homotopic_on X TX x0 x0
            (top1_path_product (top1_path_product (top1_path_product (\<alpha> 0) (fs ! 0))
              (top1_path_reverse (\<alpha> (Suc k')))) (top1_constant_path x0))
            (top1_path_product (\<alpha> 0) (top1_path_product (fs ! 0)
              (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0))))"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTX hassoc1 hassoc2])
        show ?thesis using hchain hg0 hfoldr_gs hfoldr_fs by (by100 simp)
      qed
    next
      case False
      \<comment> \<open>Induction step: k = Suc k' with k' \<ge> 1.\<close>
      show ?thesis
      proof -
        have hk': "k' \<ge> 1" using False by (by100 simp)
        obtain g0 gs' where hgs_eq: "gs = g0 # gs'"
          using Suc.prems(1) by (cases gs) (by100 simp)+
        obtain f0 fs' where hfs_eq: "fs = f0 # fs'"
          using Suc.prems(2) by (cases fs) (by100 simp)+
        have hgs'_len: "length gs' = k'" using Suc.prems(1) hgs_eq by (by100 simp)
        have hfs'_len: "length fs' = k'" using Suc.prems(2) hfs_eq by (by100 simp)
        define \<alpha>' where "\<alpha>' i = \<alpha> (Suc i)" for i
        define a' where "a' i = a (Suc i)" for i
        have h\<alpha>': "\<And>i. i \<le> k' \<Longrightarrow> top1_is_path_on X TX x0 (a' i) (\<alpha>' i)"
          using Suc.prems(6) unfolding \<alpha>'_def a'_def by (by100 simp)
        have hfi': "\<And>i. i < k' \<Longrightarrow> top1_is_path_on X TX (a' i) (a' (Suc i)) (fs' ! i)"
        proof -
          fix i assume "i < k'"
          thus "top1_is_path_on X TX (a' i) (a' (Suc i)) (fs' ! i)"
            using Suc.prems(4)[of "Suc i"] hfs_eq unfolding a'_def by (by100 simp)
        qed
        have hgi': "\<And>i. i < k' \<Longrightarrow> gs' ! i = top1_path_product
            (top1_path_product (\<alpha>' i) (fs' ! i)) (top1_path_reverse (\<alpha>' (Suc i)))"
        proof -
          fix i assume "i < k'"
          thus "gs' ! i = top1_path_product (top1_path_product (\<alpha>' i) (fs' ! i))
              (top1_path_reverse (\<alpha>' (Suc i)))"
            using Suc.prems(5)[of "Suc i"] hgs_eq hfs_eq unfolding \<alpha>'_def by (by100 simp)
        qed
        have hIH: "top1_path_homotopic_on X TX x0 x0
            (foldr top1_path_product gs' (top1_constant_path x0))
            (top1_path_product (\<alpha>' 0) (foldr top1_path_product fs'
              (top1_path_product (top1_path_reverse (\<alpha>' k')) (top1_constant_path x0))))"
          unfolding \<alpha>'_def a'_def
          by (rule Suc.IH[of gs' fs' "\<lambda>i. a (Suc i)" "\<lambda>i. \<alpha> (Suc i)",
              OF hgs'_len hfs'_len hk' _ _ _])
             (use hfi' hgi' h\<alpha>' in \<open>unfold \<alpha>'_def a'_def, by100 simp\<close>)+
        \<comment> \<open>Now combine g0 * IH to get the result.
           g0 = (\<alpha>(0)*f0)*rev(\<alpha>(1)).
           foldr gs const = g0 * foldr gs' const
           \<simeq> g0 * (\<alpha>(1) * foldr fs' (rev(\<alpha>(Suc k')) * const))  [by IH]
           = ((\<alpha>(0)*f0)*rev(\<alpha>(1))) * (\<alpha>(1) * R)                  [expand g0]
           \<simeq> (\<alpha>(0)*f0) * (rev(\<alpha>(1)) * (\<alpha>(1) * R))              [assoc]
           \<simeq> (\<alpha>(0)*f0) * ((rev(\<alpha>(1)) * \<alpha>(1)) * R)              [assoc]
           \<simeq> (\<alpha>(0)*f0) * (const * R)                             [inverse]
           \<simeq> (\<alpha>(0)*f0) * R                                       [left id]
           \<simeq> \<alpha>(0) * (f0 * R)                                     [assoc]
           = \<alpha>(0) * foldr fs (rev(\<alpha>(Suc k')) * const).\<close>
        \<comment> \<open>First establish path facts needed for algebra.\<close>
        have hg0_eq: "g0 = top1_path_product (top1_path_product (\<alpha> 0) (fs ! 0))
            (top1_path_reverse (\<alpha> (Suc 0)))"
          using Suc.prems(5)[of 0] hgs_eq by (by100 simp)
        have hf0_eq: "f0 = fs ! 0" using hfs_eq by (by100 simp)
        have h\<alpha>0: "top1_is_path_on X TX x0 (a 0) (\<alpha> 0)"
          using Suc.prems(6)[of 0] by (by100 simp)
        have h\<alpha>1: "top1_is_path_on X TX x0 (a 1) (\<alpha> 1)"
          using Suc.prems(6)[of 1] by (by100 simp)
        have hf0_path: "top1_is_path_on X TX (a 0) (a 1) f0"
          using Suc.prems(4)[of 0] hfs_eq by (by100 simp)
        have hrev\<alpha>1: "top1_is_path_on X TX (a 1) x0 (top1_path_reverse (\<alpha> 1))"
          by (rule top1_path_reverse_is_path[OF h\<alpha>1])
        have h\<alpha>0f0: "top1_is_path_on X TX x0 (a 1) (top1_path_product (\<alpha> 0) f0)"
          using top1_path_product_is_path[OF hTX h\<alpha>0 hf0_path] by simp
        \<comment> \<open>Define R = foldr fs' (rev(\<alpha>(Suc k')) * const).\<close>
        define R where "R = foldr top1_path_product fs'
            (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0))"
        \<comment> \<open>R is a path from a(1) to x0.\<close>
        have h\<alpha>Sk': "top1_is_path_on X TX x0 (a (Suc k')) (\<alpha> (Suc k'))"
          using Suc.prems(6)[of "Suc k'"] by (by100 simp)
        have hrev\<alpha>Sk': "top1_is_path_on X TX (a (Suc k')) x0 (top1_path_reverse (\<alpha> (Suc k')))"
          by (rule top1_path_reverse_is_path[OF h\<alpha>Sk'])
        have hrev\<alpha>Sk'_const: "top1_is_path_on X TX (a (Suc k')) x0
            (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0))"
          by (rule top1_path_product_is_path[OF hTX hrev\<alpha>Sk' hconst])
        have ha1: "a 1 = a' 0" unfolding a'_def by simp
        have hfi'_len: "\<And>i. i < length fs' \<Longrightarrow> top1_is_path_on X TX (a' i) (a' (Suc i)) (fs'!i)"
          using hfi' hfs'_len by (by100 simp)
        have hbase_path: "top1_is_path_on X TX (a' (length fs')) x0
            (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0))"
          using hrev\<alpha>Sk'_const hfs'_len unfolding a'_def by (by100 simp)
        have hR: "top1_is_path_on X TX (a 1) x0 R"
          unfolding R_def ha1
          by (rule foldr_path_product_is_path[OF hTX hfi'_len hbase_path])
        \<comment> \<open>\<alpha>1 * R is a path from x0 to x0.\<close>
        have h\<alpha>1R: "top1_is_path_on X TX x0 x0 (top1_path_product (\<alpha> 1) R)"
          by (rule top1_path_product_is_path[OF hTX h\<alpha>1 hR])
        \<comment> \<open>foldr gs const = g0 * foldr gs' const.\<close>
        have hfoldr_gs: "foldr top1_path_product gs (top1_constant_path x0) =
            top1_path_product g0 (foldr top1_path_product gs' (top1_constant_path x0))"
          unfolding hgs_eq by (by100 simp)
        \<comment> \<open>foldr fs (rev(\<alpha>(Suc k'))*const) = f0 * R.\<close>
        have hfoldr_fs: "foldr top1_path_product fs
            (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0)) =
            top1_path_product f0 R"
          unfolding hfs_eq R_def by (by100 simp)
        \<comment> \<open>Step 1: g0 * foldr gs' \<simeq> g0 * (\<alpha>(1) * R) via IH.\<close>
        have hIH': "top1_path_homotopic_on X TX x0 x0
            (foldr top1_path_product gs' (top1_constant_path x0))
            (top1_path_product (\<alpha> 1) R)"
          using hIH unfolding \<alpha>'_def R_def by (by100 simp)
        have hSuc0: "Suc 0 = 1" by simp
        have hg0_path: "top1_is_path_on X TX x0 x0 g0"
          unfolding hg0_eq hf0_eq[symmetric] hSuc0
          by (rule top1_path_product_is_path[OF hTX
                top1_path_product_is_path[OF hTX h\<alpha>0 hf0_path] hrev\<alpha>1])
        have hstep1: "top1_path_homotopic_on X TX x0 x0
            (top1_path_product g0 (foldr top1_path_product gs' (top1_constant_path x0)))
            (top1_path_product g0 (top1_path_product (\<alpha> 1) R))"
          by (rule path_homotopic_product_right[OF hTX hIH' hg0_path])
        \<comment> \<open>Step 2: ((\<alpha>0*f0)*rev(\<alpha>1)) * (\<alpha>1*R) \<simeq> (\<alpha>0*f0) * (rev(\<alpha>1) * (\<alpha>1*R)) [assoc].\<close>
        have hstep2: "top1_path_homotopic_on X TX x0 x0
            (top1_path_product (top1_path_product (top1_path_product (\<alpha> 0) f0)
              (top1_path_reverse (\<alpha> 1))) (top1_path_product (\<alpha> 1) R))
            (top1_path_product (top1_path_product (\<alpha> 0) f0)
              (top1_path_product (top1_path_reverse (\<alpha> 1)) (top1_path_product (\<alpha> 1) R)))"
          by (rule Lemma_51_1_path_homotopic_sym[OF
                Theorem_51_2_associativity[OF hTX h\<alpha>0f0 hrev\<alpha>1 h\<alpha>1R]])
        \<comment> \<open>Step 3: rev(\<alpha>1) * (\<alpha>1*R) \<simeq> (rev(\<alpha>1)*\<alpha>1) * R [assoc].\<close>
        have hstep3_inner: "top1_path_homotopic_on X TX (a 1) x0
            (top1_path_product (top1_path_reverse (\<alpha> 1)) (top1_path_product (\<alpha> 1) R))
            (top1_path_product (top1_path_product (top1_path_reverse (\<alpha> 1)) (\<alpha> 1)) R)"
          by (rule Theorem_51_2_associativity[OF hTX hrev\<alpha>1 h\<alpha>1 hR])
        \<comment> \<open>Step 4: rev(\<alpha>1)*\<alpha>1 \<simeq> const [inverse].\<close>
        have hstep4_inner: "top1_path_homotopic_on X TX (a 1) (a 1)
            (top1_path_product (top1_path_reverse (\<alpha> 1)) (\<alpha> 1))
            (top1_constant_path (a 1))"
          by (rule Theorem_51_2_invgerse_right[OF hTX h\<alpha>1])
        \<comment> \<open>Step 5: const * R \<simeq> R [left identity].\<close>
        have ha1_X: "a 1 \<in> X"
        proof -
          have hcont: "\<forall>x\<in>top1_unit_interval. \<alpha> 1 x \<in> X"
            using h\<alpha>1 unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          have h1I: "(1::real) \<in> top1_unit_interval"
            unfolding top1_unit_interval_def by (by100 simp)
          have "\<alpha> 1 1 \<in> X" using hcont h1I by (by100 blast)
          moreover have "\<alpha> 1 1 = a 1"
            using h\<alpha>1 unfolding top1_is_path_on_def by (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
        have hstep5_inner: "top1_path_homotopic_on X TX (a 1) x0
            (top1_path_product (top1_constant_path (a 1)) R)
            R"
          by (rule Theorem_51_2_left_identity[OF hTX hR])
        \<comment> \<open>Step 4': (rev(\<alpha>1)*\<alpha>1)*R \<simeq> const(a1)*R.\<close>
        have hstep4_lifted: "top1_path_homotopic_on X TX (a 1) x0
            (top1_path_product (top1_path_product (top1_path_reverse (\<alpha> 1)) (\<alpha> 1)) R)
            (top1_path_product (top1_constant_path (a 1)) R)"
          by (rule path_homotopic_product_left[OF hTX hstep4_inner hR])
        \<comment> \<open>Chain steps 3-5: rev(\<alpha>1)*(\<alpha>1*R) \<simeq> R.\<close>
        have hcancel: "top1_path_homotopic_on X TX (a 1) x0
            (top1_path_product (top1_path_reverse (\<alpha> 1)) (top1_path_product (\<alpha> 1) R))
            R"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTX
                Lemma_51_1_path_homotopic_trans[OF hTX hstep3_inner hstep4_lifted]
                hstep5_inner])
        \<comment> \<open>Lift to: (\<alpha>0*f0) * (rev(\<alpha>1)*(\<alpha>1*R)) \<simeq> (\<alpha>0*f0) * R.\<close>
        have hstep23456: "top1_path_homotopic_on X TX x0 x0
            (top1_path_product (top1_path_product (\<alpha> 0) f0)
              (top1_path_product (top1_path_reverse (\<alpha> 1)) (top1_path_product (\<alpha> 1) R)))
            (top1_path_product (top1_path_product (\<alpha> 0) f0) R)"
          by (rule path_homotopic_product_right[OF hTX hcancel h\<alpha>0f0])
        \<comment> \<open>Step 6: (\<alpha>0*f0)*R \<simeq> \<alpha>0*(f0*R) [assoc].\<close>
        have hstep6: "top1_path_homotopic_on X TX x0 x0
            (top1_path_product (top1_path_product (\<alpha> 0) f0) R)
            (top1_path_product (\<alpha> 0) (top1_path_product f0 R))"
          by (rule Lemma_51_1_path_homotopic_sym[OF
                Theorem_51_2_associativity[OF hTX h\<alpha>0 hf0_path hR]])
        \<comment> \<open>Chain everything together.\<close>
        have hstep1': "top1_path_homotopic_on X TX x0 x0
            (top1_path_product g0 (top1_path_product (\<alpha> 1) R))
            (top1_path_product (top1_path_product (\<alpha> 0) f0)
              (top1_path_product (top1_path_reverse (\<alpha> 1)) (top1_path_product (\<alpha> 1) R)))"
          using hstep2 hg0_eq hf0_eq by (by100 simp)
        have hfull: "top1_path_homotopic_on X TX x0 x0
            (top1_path_product g0 (foldr top1_path_product gs' (top1_constant_path x0)))
            (top1_path_product (\<alpha> 0) (top1_path_product f0 R))"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTX
                Lemma_51_1_path_homotopic_trans[OF hTX
                  Lemma_51_1_path_homotopic_trans[OF hTX hstep1 hstep1']
                  hstep23456]
                hstep6])
        show ?thesis using hfull hfoldr_gs hfoldr_fs by (by100 simp)
      qed
    qed
  qed
qed

\<comment> \<open>Telescoping lemma for conjugated path products (Munkres 59.1 Step 2).
   If gi = (\<alpha>i * fi) * rev(\<alpha>(i+1)) and \<alpha>0 = \<alpha>n = const_x0,
   then g0*g1*...*g(n-1)*const \<simeq> f0*f1*...*f(n-1)*const.\<close>
lemma telescoping_conjugated_product:
  assumes hTX: "is_topology_on X TX" and hx0: "x0 \<in> X"
      and hn: "n \<ge> 1"
      and hfs: "length fs = n" and hgs: "length gs = n"
      and h\<alpha>: "\<And>i. i \<le> n \<Longrightarrow> top1_is_path_on X TX x0 (a i) (\<alpha> i)"
      and hfi: "\<And>i. i < n \<Longrightarrow> top1_is_path_on X TX (a i) (a (Suc i)) (fs!i)"
      and hgi: "\<And>i. i < n \<Longrightarrow> gs!i = top1_path_product (top1_path_product (\<alpha> i) (fs!i))
                                     (top1_path_reverse (\<alpha> (Suc i)))"
      and h\<alpha>0: "\<alpha> 0 = top1_constant_path x0"
      and h\<alpha>n: "\<alpha> n = top1_constant_path x0"
      and ha0: "a 0 = x0" and han: "a n = x0"
  shows "top1_path_homotopic_on X TX x0 x0
      (foldr top1_path_product fs (top1_constant_path x0))
      (foldr top1_path_product gs (top1_constant_path x0))"
proof -
  \<comment> \<open>By induction on n. We prove a slightly stronger statement:
     foldr pp gs const \<simeq> \<alpha>(0) * (foldr pp fs (rev(\<alpha>(n)) * const)).
     Then use \<alpha>(0) = \<alpha>(n) = const to simplify.\<close>
  \<comment> \<open>Helper: reverse of constant path is itself.\<close>
  have hrev_const: "top1_path_reverse (top1_constant_path x0) = top1_constant_path x0"
    unfolding top1_path_reverse_def top1_constant_path_def by (rule ext) simp
  have hconst: "top1_is_path_on X TX x0 x0 (top1_constant_path x0)"
    by (rule top1_constant_path_is_path[OF hTX hx0])
  \<comment> \<open>The conjugation with \<alpha>(0) = const and \<alpha>(n) = const simplifies:
     const * (foldr fi (rev(const) * const)) \<simeq> const * (foldr fi (const * const))
     \<simeq> const * (foldr fi const) \<simeq> foldr fi const.\<close>
  \<comment> \<open>For the main argument, we show element-wise that the telescoping cancels.
     We prove this by a direct chain of homotopies for the m=1 base case,
     and then generalize by induction.\<close>
  \<comment> \<open>Proof: show foldr gs const \<simeq> foldr fs const by showing
     foldr gs const \<simeq> \<alpha>(0) * foldr fs (rev(\<alpha>(n)) * const)
     and then simplifying with \<alpha>(0) = \<alpha>(n) = const.\<close>
  \<comment> \<open>Step 1: foldr gs const \<simeq> \<alpha>(0) * foldr fs (rev(\<alpha>(n)) * const).\<close>
  have hstep1: "top1_path_homotopic_on X TX x0 x0
      (foldr top1_path_product gs (top1_constant_path x0))
      (top1_path_product (\<alpha> 0) (foldr top1_path_product fs
        (top1_path_product (top1_path_reverse (\<alpha> n)) (top1_constant_path x0))))"
    using telescoping_core[OF hTX hx0 hgs hfs hn h\<alpha> hfi hgi] .
  \<comment> \<open>Was: Main telescoping induction on n.
       Base n=1: ((\<alpha>0*f0)*rev(\<alpha>1))*const \<simeq> \<alpha>0*(f0*(rev(\<alpha>1)*const)) by associativity.
       Step: g0*(foldr gs' const) \<simeq> g0*(\<alpha>1*foldr fs'(rev(\<alpha>n)*const)) (by IH)
             \<simeq> ((\<alpha>0*f0)*rev(\<alpha>1))*(\<alpha>1*...) (expand g0)
             \<simeq> (\<alpha>0*f0)*(rev(\<alpha>1)*\<alpha>1)*... (reassoc)
             \<simeq> (\<alpha>0*f0)*const*... (inverse cancel)
             \<simeq> (\<alpha>0*f0)*... (identity)
             = \<alpha>0*f0*foldr fs'(rev(\<alpha>n)*const)
             = \<alpha>0*foldr(f0#fs')(rev(\<alpha>n)*const).
       Each step uses Theorem_51_2 (assoc/id/inv) + product_left/right + trans.
       ~40 lines of Isabelle path algebra.\<close>
  \<comment> \<open>Step 2: Simplify RHS using \<alpha>(0) = \<alpha>(n) = const_x0.\<close>
  have hstep2: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product (\<alpha> 0) (foldr top1_path_product fs
        (top1_path_product (top1_path_reverse (\<alpha> n)) (top1_constant_path x0))))
      (foldr top1_path_product fs (top1_constant_path x0))"
  proof -
    \<comment> \<open>\<alpha>(0) = const, \<alpha>(n) = const, rev(const) = const.\<close>
    have "top1_path_product (top1_path_reverse (\<alpha> n)) (top1_constant_path x0)
        = top1_path_product (top1_constant_path x0) (top1_constant_path x0)"
      using h\<alpha>n hrev_const by simp
    moreover have "top1_path_homotopic_on X TX x0 x0
        (top1_path_product (top1_constant_path x0) (top1_constant_path x0))
        (top1_constant_path x0)"
      by (rule Theorem_51_2_left_identity[OF hTX hconst])
    ultimately have hrev_simp: "top1_path_homotopic_on X TX x0 x0
        (top1_path_product (top1_path_reverse (\<alpha> n)) (top1_constant_path x0))
        (top1_constant_path x0)" by simp
    \<comment> \<open>Replace rev(\<alpha>n)*const with const in the foldr, then remove \<alpha>(0)=const via left identity.\<close>
    \<comment> \<open>Step 2a: foldr respects base homotopy: if base1 \<simeq> base2 then foldr fs base1 \<simeq> foldr fs base2.\<close>
    have hfoldr_base: "\<And>base1 base2. top1_path_homotopic_on X TX x0 x0 base1 base2 \<Longrightarrow>
        top1_path_homotopic_on X TX x0 x0
          (foldr top1_path_product fs base1) (foldr top1_path_product fs base2)"
      using foldr_path_product_base_homotopic[OF hTX, where a="\<lambda>i. a i" and fs=fs]
            hfi ha0 han hfs by simp
    have hstep2a: "top1_path_homotopic_on X TX x0 x0
        (foldr top1_path_product fs (top1_path_product (top1_path_reverse (\<alpha> n)) (top1_constant_path x0)))
        (foldr top1_path_product fs (top1_constant_path x0))"
      by (rule hfoldr_base[OF hrev_simp])
    \<comment> \<open>Step 2b: \<alpha>(0) = const, so const * foldr \<simeq> foldr (left identity).\<close>
    have hfoldr_path: "top1_is_path_on X TX x0 x0
        (foldr top1_path_product fs (top1_constant_path x0))"
      using foldr_path_product_is_path[OF hTX, where a="\<lambda>i. a i" and fs=fs and y=x0]
            hfi hconst ha0 han hfs by simp
    have hstep2b: "top1_path_homotopic_on X TX x0 x0
        (top1_path_product (top1_constant_path x0) (foldr top1_path_product fs (top1_constant_path x0)))
        (foldr top1_path_product fs (top1_constant_path x0))"
      by (rule Theorem_51_2_left_identity[OF hTX hfoldr_path])
    \<comment> \<open>Combine: \<alpha>0 * foldr(rev(\<alpha>n)*const) \<simeq> const * foldr(rev(\<alpha>n)*const)
                                                \<simeq> const * foldr(const) \<simeq> foldr(const).\<close>
    have hstep2c: "top1_path_homotopic_on X TX x0 x0
        (top1_path_product (\<alpha> 0) (foldr top1_path_product fs
          (top1_path_product (top1_path_reverse (\<alpha> n)) (top1_constant_path x0))))
        (top1_path_product (top1_constant_path x0) (foldr top1_path_product fs (top1_constant_path x0)))"
      using h\<alpha>0 path_homotopic_product_right[OF hTX hstep2a hconst] by simp
    show ?thesis
      using Lemma_51_1_path_homotopic_trans[OF hTX hstep2c hstep2b] .
  qed
  \<comment> \<open>Combine: foldr gs \<simeq> ... \<simeq> foldr fs. Use sym to get foldr fs \<simeq> foldr gs.\<close>
  have "top1_path_homotopic_on X TX x0 x0
      (foldr top1_path_product gs (top1_constant_path x0))
      (foldr top1_path_product fs (top1_constant_path x0))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX hstep1 hstep2])
  thus ?thesis by (rule Lemma_51_1_path_homotopic_sym)
qed

text \<open>Theorem 51.3 (Munkres): Reparametrization preserves path homotopy class.
  If f is a path from x0 to x1, and 0=a0<a1<...<an=1, and fi(t) = f(a_{i-1}+t*(a_i-a_{i-1})),
  then [f] = [f1]*[f2]*...*[fn].

  We first prove the key splitting lemma: f \<simeq> f_L * f_R where
  f_L(t) = f(at) and f_R(t) = f(a+t(1-a)), for 0<a<1.
  Then the full theorem follows by induction on n.\<close>

lemma path_product_split:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
      and ha: "0 < a" "a < 1"
  defines "f_L \<equiv> \<lambda>t. f (a * t)"
  defines "f_R \<equiv> \<lambda>t. f (a + (1-a) * t)"
  shows "top1_path_homotopic_on X TX x0 x1 f (top1_path_product f_L f_R)"
proof -
  \<comment> \<open>The homotopy is H(s,t) = f(\<phi>_s(t)) where \<phi>_s interpolates linearly between
     t (at s=0) and the path-product reparametrization (at s=1).
     \<phi>_s(t) = (1-s)*t + s*(2*a*t) for t \<le> 1/2
     \<phi>_s(t) = (1-s)*t + s*(a + (2*t-1)*(1-a)) for t > 1/2.\<close>
  define \<phi> :: "real \<Rightarrow> real \<Rightarrow> real" where
    "\<phi> s t = (if t \<le> 1/2 then (1-s)*t + s*(2*a*t) else (1-s)*t + s*(a + (2*t-1)*(1-a)))" for s t
  \<comment> \<open>Key properties of \<phi>.\<close>
  have h\<phi>0: "\<And>t. \<phi> 0 t = t" unfolding \<phi>_def by simp
  have h\<phi>1: "\<And>t. t \<le> 1/2 \<Longrightarrow> \<phi> 1 t = 2*a*t" unfolding \<phi>_def by simp
  have h\<phi>1': "\<And>t. t > 1/2 \<Longrightarrow> \<phi> 1 t = a + (2*t-1)*(1-a)" unfolding \<phi>_def by simp
  have h\<phi>_start: "\<And>s. \<phi> s 0 = 0" unfolding \<phi>_def by simp
  have h\<phi>_end: "\<And>s. \<phi> s 1 = 1" unfolding \<phi>_def by simp
  have h\<phi>_half: "\<And>s. \<phi> s (1/2) = (1-s)/2 + s*a" unfolding \<phi>_def by (simp add: field_simps)
  \<comment> \<open>H(s,t) = f(\<phi>(s,t)).\<close>
  define H where "H p = f (\<phi> (fst p) (snd p))" for p :: "real \<times> real"
  \<comment> \<open>H is a path homotopy from f to f_L * f_R.\<close>
  have hH0: "\<And>t. H (0, t) = f t" unfolding H_def using h\<phi>0 by simp
  have hH1_le: "\<And>t. t \<le> 1/2 \<Longrightarrow> H (1, t) = f_L (2*t)"
    unfolding H_def f_L_def using h\<phi>1 by (simp add: field_simps)
  have hH1_gt: "\<And>t. t > 1/2 \<Longrightarrow> H (1, t) = f_R (2*t - 1)"
  proof -
    fix t :: real assume ht: "t > 1/2"
    have "\<phi> 1 t = a + (2*t-1)*(1-a)" using h\<phi>1'[OF ht] .
    moreover have "a + (2*t-1)*(1-a) = a + (1-a)*(2*t-1)" by (simp add: mult.commute)
    ultimately show "H (1, t) = f_R (2*t - 1)" unfolding H_def f_R_def by simp
  qed
  have hf0: "f 0 = x0" using hf unfolding top1_is_path_on_def by (by100 blast)
  have hf1: "f 1 = x1" using hf unfolding top1_is_path_on_def by (by100 blast)
  have hH_start: "\<And>s. H (s, 0) = x0"
    unfolding H_def using h\<phi>_start hf0 by simp
  have hH_end: "\<And>s. H (s, 1) = x1"
    unfolding H_def using h\<phi>_end hf1 by simp
  \<comment> \<open>H(1,t) = path_product f_L f_R (t).\<close>
  have hH1: "\<And>t. t \<in> I_set \<Longrightarrow> H (1, t) = top1_path_product f_L f_R t"
  proof -
    fix t assume ht: "t \<in> I_set"
    show "H (1, t) = top1_path_product f_L f_R t"
    proof (cases "t \<le> 1/2")
      case True
      hence "H (1, t) = f_L (2*t)" using hH1_le by simp
      moreover have "top1_path_product f_L f_R t = f_L (2*t)"
        using True unfolding top1_path_product_def by simp
      ultimately show ?thesis by simp
    next
      case False
      hence hgt: "t > 1/2" by simp
      hence "H (1, t) = f_R (2*t - 1)" using hH1_gt by simp
      moreover have "top1_path_product f_L f_R t = f_R (2*t - 1)"
        using False unfolding top1_path_product_def by simp
      ultimately show ?thesis by simp
    qed
  qed
  \<comment> \<open>\<phi> maps I\<times>I to I.\<close>
  have h\<phi>_range: "\<And>s t. s \<in> I_set \<Longrightarrow> t \<in> I_set \<Longrightarrow> \<phi> s t \<in> I_set"
  proof -
    fix s t :: real assume hs: "s \<in> I_set" and ht: "t \<in> I_set"
    have hs01: "0 \<le> s" "s \<le> 1" using hs unfolding top1_unit_interval_def by auto
    have ht01: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
    show "\<phi> s t \<in> I_set"
    proof (cases "t \<le> 1/2")
      case True
      \<comment> \<open>\<phi> s t = (1-s)*t + s*2*a*t = t*(1-s+s*2*a). In [0, t*max(1,2a)] \<subseteq> [0,1].\<close>
      have "\<phi> s t = (1-s)*t + s*(2*a*t)" unfolding \<phi>_def using True by simp
      moreover have "(1-s)*t + s*(2*a*t) \<ge> 0"
        using hs01 ht01 ha(1) by (intro add_nonneg_nonneg mult_nonneg_nonneg) linarith+
      moreover have "(1-s)*t + s*(2*a*t) \<le> 1"
      proof -
        have "(1-s)*t \<le> (1-s) * (1/2)" using True hs01 by (intro mult_left_mono) linarith+
        moreover have "s*(2*a*t) \<le> s*(2*a*(1/2))" using True hs01 ha by (intro mult_left_mono mult_left_mono) linarith+
        hence "s*(2*a*t) \<le> s*a" by simp
        ultimately have "(1-s)*t + s*(2*a*t) \<le> (1-s)/2 + s*a" by linarith
        also have "\<dots> \<le> (1-s)/2 + s"
        proof -
          have "s*a \<le> s*1" by (rule mult_left_mono) (use hs01 ha in linarith)+
          thus ?thesis by linarith
        qed
        also have "\<dots> = (1+s)/2" by (simp add: field_simps)
        also have "\<dots> \<le> 1" using hs01 by simp
        finally show ?thesis .
      qed
      ultimately show ?thesis unfolding top1_unit_interval_def by simp
    next
      case False
      have hge: "t > 1/2" using False by simp
      have "\<phi> s t = (1-s)*t + s*(a + (2*t-1)*(1-a))" unfolding \<phi>_def using False by simp
      moreover have "(1-s)*t + s*(a + (2*t-1)*(1-a)) \<ge> 0"
        using hs01 ht01 ha hge
        by (intro add_nonneg_nonneg mult_nonneg_nonneg) linarith+
      moreover have "(1-s)*t + s*(a + (2*t-1)*(1-a)) \<le> 1"
      proof -
        have "(1-s)*t \<le> (1-s)*1" by (rule mult_left_mono) (use hs01 ht01 in linarith)+
        hence "(1-s)*t \<le> 1-s" by simp
        moreover have "a + (2*t-1)*(1-a) \<le> 1"
        proof -
          have "(2*t-1) \<le> 1" using ht01 by linarith
          hence "(2*t-1)*(1-a) \<le> 1*(1-a)" by (rule mult_right_mono) (use ha in linarith)
          hence "(2*t-1)*(1-a) \<le> 1-a" by simp
          thus ?thesis by linarith
        qed
        hence "s*(a + (2*t-1)*(1-a)) \<le> s*1"
          by (rule mult_left_mono) (use hs01 in linarith)+
        hence "s*(a + (2*t-1)*(1-a)) \<le> s" by simp
        ultimately show ?thesis by linarith
      qed
      ultimately show ?thesis unfolding top1_unit_interval_def by simp
    qed
  qed
  \<comment> \<open>H maps I\<times>I to X.\<close>
  have hf_range: "\<And>u. u \<in> I_set \<Longrightarrow> f u \<in> X"
    using hf unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
  have hH_range: "\<And>s t. s \<in> I_set \<Longrightarrow> t \<in> I_set \<Longrightarrow> H (s, t) \<in> X"
    unfolding H_def using h\<phi>_range hf_range by simp
  \<comment> \<open>\<phi> is continuous: piecewise linear, pieces agree at t=1/2.\<close>
  have h\<phi>_cont: "continuous_on (I_set \<times> I_set) (\<lambda>p. \<phi> (fst p) (snd p))"
  proof -
    \<comment> \<open>The two pieces as functions of (s,t).\<close>
    define g1 :: "real \<times> real \<Rightarrow> real" where "g1 p = (1-fst p)*(snd p) + (fst p)*(2*a*(snd p))" for p
    define g2 :: "real \<times> real \<Rightarrow> real" where "g2 p = (1-fst p)*(snd p) + (fst p)*(a + (2*(snd p)-1)*(1-a))" for p
    \<comment> \<open>Both are continuous (polynomials).\<close>
    have hg1_cont: "continuous_on UNIV g1" unfolding g1_def by (intro continuous_intros)
    have hg2_cont: "continuous_on UNIV g2" unfolding g2_def by (intro continuous_intros)
    \<comment> \<open>Closed halves.\<close>
    define A where "A = {p :: real \<times> real. snd p \<le> 1/2}"
    define B where "B = {p :: real \<times> real. snd p \<ge> 1/2}"
    have hA_closed: "closed A" unfolding A_def
      by (intro closed_Collect_le) (intro continuous_intros)+
    have hB_closed: "closed B" unfolding B_def
      by (intro closed_Collect_le) (intro continuous_intros)+
    \<comment> \<open>On the boundary t=1/2, both pieces give the same value.\<close>
    have hagree: "\<And>p. snd p = 1/2 \<Longrightarrow> g1 p = g2 p"
      unfolding g1_def g2_def by (simp add: field_simps)
    \<comment> \<open>The piecewise function.\<close>
    have hpw: "\<And>p. p \<in> A \<union> B \<Longrightarrow> \<phi> (fst p) (snd p) = (if snd p \<le> 1/2 then g1 p else g2 p)"
      unfolding \<phi>_def g1_def g2_def A_def B_def by auto
    have hpw_cont: "continuous_on (A \<union> B) (\<lambda>p. if snd p \<le> 1/2 then g1 p else g2 p)"
    proof (rule continuous_on_If[OF hA_closed hB_closed])
      show "continuous_on A g1" using continuous_on_subset[OF hg1_cont] by (by100 blast)
      show "continuous_on B g2" using continuous_on_subset[OF hg2_cont] by (by100 blast)
      show "\<And>x. x \<in> A \<Longrightarrow> \<not> snd x \<le> 1 / 2 \<Longrightarrow> g1 x = g2 x" unfolding A_def by simp
      show "\<And>x. x \<in> B \<Longrightarrow> snd x \<le> 1 / 2 \<Longrightarrow> g1 x = g2 x" using hagree unfolding B_def by force
    qed
    have hI_sub: "I_set \<times> I_set \<subseteq> A \<union> B" unfolding A_def B_def top1_unit_interval_def by auto
    have hpw_cont_I: "continuous_on (I_set \<times> I_set) (\<lambda>p. if snd p \<le> 1/2 then g1 p else g2 p)"
      by (rule continuous_on_subset[OF hpw_cont hI_sub])
    show ?thesis
    proof (rule continuous_on_cong[THEN iffD2, OF refl _ hpw_cont_I])
      fix p assume "p \<in> I_set \<times> I_set"
      show "\<phi> (fst p) (snd p) = (if snd p \<le> 1/2 then g1 p else g2 p)"
        unfolding \<phi>_def g1_def g2_def by auto
    qed
  qed
  \<comment> \<open>H is continuous.\<close>
  have h\<phi>_map: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top
      (\<lambda>p. \<phi> (fst p) (snd p))"
    by (rule top1_continuous_map_on_II_to_I) (use h\<phi>_range in auto, rule h\<phi>_cont)
  have hf_cont_top: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_path_on_def by (by100 blast)
  have hH_comp: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) X TX
      (f \<circ> (\<lambda>p. \<phi> (fst p) (snd p)))"
    by (rule top1_continuous_map_on_comp[OF h\<phi>_map hf_cont_top])
  have hH_eq: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> (f \<circ> (\<lambda>p. \<phi> (fst p) (snd p))) p = H p"
    unfolding H_def comp_def by simp
  have hH_cont: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) X TX H"
    using iffD1[OF top1_continuous_map_on_cong[of "I_set \<times> I_set" "f \<circ> (\<lambda>p. \<phi> (fst p) (snd p))" H]
      hH_comp]
    using hH_eq by (by100 blast)
  \<comment> \<open>Assemble the path homotopy. The definition uses F(s,t) where s=path, t=homotopy.\<close>
  define F where "F p = H (snd p, fst p)" for p :: "real \<times> real"
  have hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
    sorry \<comment> \<open>H ∘ swap is continuous; II_topology = product I_top I_top.\<close>
  \<comment> \<open>f_L = f \<circ> (\<lambda>t. a*t) and f_R = f \<circ> (\<lambda>t. a+(1-a)*t) are paths.\<close>
  have hscale_range: "\<And>t. t \<in> I_set \<Longrightarrow> a * t \<in> I_set"
  proof -
    fix t assume "t \<in> I_set"
    hence ht01: "0 \<le> t" "t \<le> 1" unfolding top1_unit_interval_def by auto
    have "0 \<le> a * t" using ha ht01 by (intro mult_nonneg_nonneg) linarith+
    moreover have "a * t \<le> 1" using ha ht01 by (intro mult_le_one) linarith+
    ultimately show "a * t \<in> I_set" unfolding top1_unit_interval_def by simp
  qed
  have hshift_range: "\<And>t. t \<in> I_set \<Longrightarrow> a + (1-a) * t \<in> I_set"
  proof -
    fix t assume "t \<in> I_set"
    hence ht01: "0 \<le> t" "t \<le> 1" unfolding top1_unit_interval_def by auto
    have "a + (1-a)*t \<ge> 0" using ha ht01 by (intro add_nonneg_nonneg mult_nonneg_nonneg) linarith+
    moreover have "a + (1-a)*t \<le> a + (1-a)*1"
      by (intro add_left_mono mult_left_mono) (use ha ht01 in linarith)+
    hence "a + (1-a)*t \<le> 1" by simp
    ultimately show "a + (1-a)*t \<in> I_set" unfolding top1_unit_interval_def by simp
  qed
  have hfL_cont_top: "top1_continuous_map_on I_set I_top X TX f_L"
  proof -
    have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
      using hf unfolding top1_is_path_on_def by (by100 blast)
    have hf_range': "\<And>u. u \<in> I_set \<Longrightarrow> f u \<in> X"
      using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
    have hf_pre: "\<And>V. V \<in> TX \<Longrightarrow> {u \<in> I_set. f u \<in> V} \<in> I_top"
      using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
    show ?thesis unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix t assume "t \<in> I_set"
      thus "f_L t \<in> X" unfolding f_L_def using hscale_range hf_range' by (by100 blast)
    next
      fix V assume hV: "V \<in> TX"
      \<comment> \<open>{t \<in> I | f(at) \<in> V} = {t \<in> I | at \<in> {u \<in> I | f u \<in> V}}.\<close>
      have hW: "{u \<in> I_set. f u \<in> V} \<in> I_top" by (rule hf_pre[OF hV])
      \<comment> \<open>I_top = subspace_topology {0..1} (euclidean). {u \<in> I | f u \<in> V} = I \<inter> W for some open W.\<close>
      obtain W where hoW: "open W" and hWI: "{u \<in> I_set. f u \<in> V} = I_set \<inter> W"
        using hW unfolding top1_unit_interval_topology_def subspace_topology_def top1_open_sets_def
        by auto
      \<comment> \<open>{t \<in> I | at \<in> I \<inter> W} = {t \<in> I | at \<in> W} (since at \<in> I for t \<in> I).\<close>
      have "{t \<in> I_set. f_L t \<in> V} = {t \<in> I_set. a*t \<in> W}"
      proof (intro Collect_cong conj_cong refl)
        fix t assume "t \<in> I_set"
        hence "a*t \<in> I_set" by (rule hscale_range)
        thus "(f_L t \<in> V) = (a*t \<in> W)" unfolding f_L_def using hWI by (by100 blast)
      qed
      \<comment> \<open>{t \<in> I | at \<in> W} is open in I: the linear map t \<mapsto> at is continuous, W is open.\<close>
      moreover have "{t \<in> I_set. a*t \<in> W} \<in> I_top"
      proof -
        have hcont_scale: "continuous_on UNIV (\<lambda>t::real. a*t)" by (intro continuous_intros)
        have "open ((\<lambda>t. a*t) -` W)" by (rule open_vimage[OF hoW hcont_scale])
        moreover have "{t. a*t \<in> W} = (\<lambda>t. a*t) -` W" by auto
        ultimately have "open {t. a*t \<in> W}" by simp
        hence "{t. a*t \<in> W} \<in> top1_open_sets" unfolding top1_open_sets_def by simp
        hence "I_set \<inter> {t. a*t \<in> W} \<in> I_top"
          unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
        moreover have "I_set \<inter> {t. a*t \<in> W} = {t \<in> I_set. a*t \<in> W}" by (by100 blast)
        ultimately show ?thesis by simp
      qed
      ultimately show "{t \<in> I_set. f_L t \<in> V} \<in> I_top" by simp
    qed
  qed
  have hfL_path: "top1_is_path_on X TX x0 (f a) f_L"
    unfolding top1_is_path_on_def using hfL_cont_top hf0 ha
    unfolding f_L_def by simp
  have hfR_cont_top: "top1_continuous_map_on I_set I_top X TX f_R"
  proof -
    have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
      using hf unfolding top1_is_path_on_def by (by100 blast)
    have hf_range': "\<And>u. u \<in> I_set \<Longrightarrow> f u \<in> X"
      using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
    have hf_pre: "\<And>V. V \<in> TX \<Longrightarrow> {u \<in> I_set. f u \<in> V} \<in> I_top"
      using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
    show ?thesis unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix t assume "t \<in> I_set"
      thus "f_R t \<in> X" unfolding f_R_def using hshift_range hf_range' by (by100 blast)
    next
      fix V assume hV: "V \<in> TX"
      have hW: "{u \<in> I_set. f u \<in> V} \<in> I_top" using hf_pre[OF hV] .
      obtain W where hoW: "open W" and hWI: "{u \<in> I_set. f u \<in> V} = I_set \<inter> W"
        using hW unfolding top1_unit_interval_topology_def subspace_topology_def top1_open_sets_def
        by auto
      have "{t \<in> I_set. f_R t \<in> V} = {t \<in> I_set. a + (1-a)*t \<in> W}"
      proof (intro Collect_cong conj_cong refl)
        fix t assume "t \<in> I_set"
        hence "a + (1-a)*t \<in> I_set" by (rule hshift_range)
        thus "(f_R t \<in> V) = (a + (1-a)*t \<in> W)" unfolding f_R_def using hWI by (by100 blast)
      qed
      moreover have "{t \<in> I_set. a + (1-a)*t \<in> W} \<in> I_top"
      proof -
        have hcont_shift: "continuous_on UNIV (\<lambda>t::real. a + (1-a)*t)" by (intro continuous_intros)
        have "open ((\<lambda>t. a + (1-a)*t) -` W)" by (rule open_vimage[OF hoW hcont_shift])
        moreover have "{t. a + (1-a)*t \<in> W} = (\<lambda>t. a + (1-a)*t) -` W" by auto
        ultimately have "open {t. a + (1-a)*t \<in> W}" by simp
        hence "{t. a + (1-a)*t \<in> W} \<in> top1_open_sets" unfolding top1_open_sets_def by simp
        hence "I_set \<inter> {t. a + (1-a)*t \<in> W} \<in> I_top"
          unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
        moreover have "I_set \<inter> {t. a + (1-a)*t \<in> W} = {t \<in> I_set. a + (1-a)*t \<in> W}" by (by100 blast)
        ultimately show ?thesis by simp
      qed
      ultimately show "{t \<in> I_set. f_R t \<in> V} \<in> I_top" by simp
    qed
  qed
  have hfR_path: "top1_is_path_on X TX (f a) x1 f_R"
    unfolding top1_is_path_on_def using hfR_cont_top hf1 ha
    unfolding f_R_def by simp
  have hfL_fR_path: "top1_is_path_on X TX x0 x1 (top1_path_product f_L f_R)"
    by (rule top1_path_product_is_path[OF hTX hfL_path hfR_path])
  show ?thesis
    unfolding top1_path_homotopic_on_def
  proof (intro conjI exI[of _ F])
    show "top1_is_path_on X TX x0 x1 f" by (rule hf)
    show "top1_is_path_on X TX x0 x1 (top1_path_product f_L f_R)" by (rule hfL_fR_path)
    show "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F" by (rule hF_cont)
    show "\<forall>s\<in>I_set. F (s, 0) = f s" unfolding F_def using hH0 by simp
    show "\<forall>s\<in>I_set. F (s, 1) = top1_path_product f_L f_R s" unfolding F_def using hH1 by simp
    show "\<forall>t\<in>I_set. F (0, t) = x0" unfolding F_def using hH_start by simp
    show "\<forall>t\<in>I_set. F (1, t) = x1" unfolding F_def using hH_end by simp
  qed
qed

text \<open>Theorem 51.3 by induction on the number of subdivision points.\<close>
lemma Theorem_51_3_aux:
  fixes f :: "real \<Rightarrow> 'a" and subdivision :: "nat \<Rightarrow> real"
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
      and hm: "m \<ge> 1"
      and hsub0: "subdivision 0 = 0" and hsubm: "subdivision m = 1"
      and hsub_mono: "\<And>i. i < m \<Longrightarrow> subdivision i < subdivision (Suc i)"
  shows "top1_path_homotopic_on X TX x0 x1 f
      (foldr top1_path_product
        (map (\<lambda>i t. f (subdivision i + t * (subdivision (Suc i) - subdivision i))) [0..<m])
        (top1_constant_path x1))"
  sorry


end
