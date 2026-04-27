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
          sorry
        \<comment> \<open>Now combine g0 * IH to get the result.
           g0 = (\<alpha>(0)*f0)*rev(\<alpha>(1)) = (\<alpha>(0)*f0)*rev(\<alpha>'(0)).
           The full path algebra needs associativity + inverse cancellation.
           This is the core of the telescoping step.\<close>
        show ?thesis sorry
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

theorem Theorem_59_1:
  assumes hT: "is_topology_on_strict X TX" and "openin_on X TX U" and "openin_on X TX V"
      and hUV: "U \<union> V = X" and "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and hx0: "x0 \<in> U \<inter> V"
  shows "\<forall>f. top1_is_loop_on X TX x0 f \<longrightarrow>
    (\<exists>n \<ge> 1. \<exists>gs. length gs = n \<and>
       (\<forall>i<n. top1_is_loop_on X TX x0 (gs!i)
            \<and> (gs!i ` I_set \<subseteq> U \<or> gs!i ` I_set \<subseteq> V))
       \<and> top1_path_homotopic_on X TX x0 x0 f
           (foldr (top1_path_product) gs (top1_constant_path x0)))"
  \<comment> \<open>Munkres 59.1: Step 1: Lebesgue number gives subdivision a0<...<an with f([ai,ai+1])
     in U or V and f(ai) in U\<inter>V. Step 2: Choose paths \<alpha>i in U\<inter>V from x0 to f(ai).
     Set gi = (\<alpha>_{i-1} * fi) * \<alpha>i_bar. Each gi is a loop in U or V at x0, and
     [g1]*...*[gn] = [f1]*...*[fn] = [f].\<close>
proof (intro allI impI)
  fix f assume hf: "top1_is_loop_on X TX x0 f"
  \<comment> \<open>Step 1: Lebesgue subdivision. Find a0<...<an with f([ai,ai+1]) in U or V.\<close>
  obtain m :: nat and subdivision :: "nat \<Rightarrow> real" where
    hm: "m \<ge> 1" and hsub0: "subdivision 0 = 0" and hsubm: "subdivision m = 1"
    and hsub_mono: "\<forall>i<m. subdivision i < subdivision (Suc i)"
    and hsub_UV: "\<forall>i<m. f ` {s\<in>I_set. subdivision i \<le> s \<and> s \<le> subdivision (Suc i)} \<subseteq> U
                       \<or> f ` {s\<in>I_set. subdivision i \<le> s \<and> s \<le> subdivision (Suc i)} \<subseteq> V"
    and hsub_int: "\<forall>i\<le>m. f (subdivision i) \<in> U \<inter> V"
  proof -
    \<comment> \<open>Use open_cover_subdivision_01 from Top0 to get subdivision directly.\<close>
    have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
      by (rule top1_is_loop_on_continuous[OF hf])
    have hf0: "f 0 = x0" using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hf1: "f 1 = x0" using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hTX: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
    have hUo: "U \<in> TX" using assms(2) unfolding openin_on_def by (by100 blast)
    have hVo: "V \<in> TX" using assms(3) unfolding openin_on_def by (by100 blast)
    have hpreU: "{t \<in> I_set. f t \<in> U} \<in> I_top"
      using hf_cont hUo unfolding top1_continuous_map_on_def by (by100 blast)
    have hpreV: "{t \<in> I_set. f t \<in> V} \<in> I_top"
      using hf_cont hVo unfolding top1_continuous_map_on_def by (by100 blast)
    \<comment> \<open>Standard topology bridge: get open W_U, W_V from preimages.\<close>
    obtain W_U where hWU: "open W_U" and hpreU_eq: "{t \<in> I_set. f t \<in> U} = I_set \<inter> W_U"
    proof -
      have "{t \<in> I_set. f t \<in> U} \<in> {I_set \<inter> W | W. W \<in> top1_open_sets}"
        using hpreU unfolding top1_unit_interval_topology_def subspace_topology_def by simp
      then obtain W where "W \<in> top1_open_sets" "{t \<in> I_set. f t \<in> U} = I_set \<inter> W"
        by (by100 blast)
      thus ?thesis using that unfolding top1_open_sets_def by (by100 blast)
    qed
    obtain W_V where hWV: "open W_V" and hpreV_eq: "{t \<in> I_set. f t \<in> V} = I_set \<inter> W_V"
    proof -
      have "{t \<in> I_set. f t \<in> V} \<in> {I_set \<inter> W | W. W \<in> top1_open_sets}"
        using hpreV unfolding top1_unit_interval_topology_def subspace_topology_def by simp
      then obtain W where "W \<in> top1_open_sets" "{t \<in> I_set. f t \<in> V} = I_set \<inter> W"
        by (by100 blast)
      thus ?thesis using that unfolding top1_open_sets_def by (by100 blast)
    qed
    have hcover: "{t \<in> I_set. f t \<in> U} \<union> {t \<in> I_set. f t \<in> V} = I_set"
    proof -
      have "\<forall>t \<in> I_set. f t \<in> X" using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
      thus ?thesis using hUV by (by100 blast)
    qed
    have hWcover: "I_set \<subseteq> W_U \<union> W_V" using hcover hpreU_eq hpreV_eq by (by100 blast)
    \<comment> \<open>Apply open_cover_subdivision_01 with A = {W_U, W_V}.
       Need: each s in [0,1] is in W_U or W_V (open), so has an \<epsilon>-ball inside it.\<close>
    have hpointwise: "\<forall>s::real. 0 \<le> s \<and> s \<le> 1 \<longrightarrow>
        (\<exists>W\<in>{W_U, W_V}. s \<in> W \<and> (\<exists>\<epsilon>>0. {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> W))"
    proof (intro allI impI)
      fix s :: real assume hs: "0 \<le> s \<and> s \<le> 1"
      hence "s \<in> I_set" unfolding top1_unit_interval_def by simp
      hence "s \<in> W_U \<or> s \<in> W_V" using hWcover by (by100 blast)
      thus "\<exists>W\<in>{W_U, W_V}. s \<in> W \<and> (\<exists>\<epsilon>>0. {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> W)"
      proof
        assume hsWU: "s \<in> W_U"
        have "\<exists>e>0. \<forall>y. dist y s < e \<longrightarrow> y \<in> W_U"
          using hWU hsWU unfolding open_dist by (by100 blast)
        then obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0" "\<forall>y. dist y s < \<epsilon> \<longrightarrow> y \<in> W_U" by blast
        have "{t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> W_U"
        proof
          fix t assume "t \<in> {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1}"
          hence "\<bar>t - s\<bar> < \<epsilon>" by simp
          hence "dist t s < \<epsilon>" by (simp add: dist_real_def)
          thus "t \<in> W_U" using h\<epsilon>(2) by (by100 blast)
        qed
        thus ?thesis using hsWU h\<epsilon>(1) by (by100 blast)
      next
        assume hsWV: "s \<in> W_V"
        have "\<exists>e>0. \<forall>y. dist y s < e \<longrightarrow> y \<in> W_V"
          using hWV hsWV unfolding open_dist by (by100 blast)
        then obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0" "\<forall>y. dist y s < \<epsilon> \<longrightarrow> y \<in> W_V" by blast
        have "{t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> W_V"
        proof
          fix t assume "t \<in> {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1}"
          hence "\<bar>t - s\<bar> < \<epsilon>" by simp
          hence "dist t s < \<epsilon>" by (simp add: dist_real_def)
          thus "t \<in> W_V" using h\<epsilon>(2) by (by100 blast)
        qed
        thus ?thesis using hsWV h\<epsilon>(1) by (by100 blast)
      qed
    qed
    obtain n_sub :: nat and sub0 :: "nat \<Rightarrow> real" where
      hn_sub: "n_sub \<ge> 1" and hsub0_0: "sub0 0 = 0" and hsub0_n: "sub0 n_sub = 1"
      and hsub0_mono: "\<forall>i<n_sub. sub0 i < sub0 (Suc i)"
      and hsub0_cover: "\<forall>i<n_sub. \<exists>W\<in>{W_U, W_V}.
          {s. sub0 i \<le> s \<and> s \<le> sub0 (Suc i) \<and> 0 \<le> s \<and> s \<le> 1} \<subseteq> W"
      using open_cover_subdivision_01[OF hpointwise] by blast
    \<comment> \<open>Transfer: each piece maps into U or V.\<close>
    have hsub0_UV: "\<forall>i<n_sub. f ` {s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> U
                         \<or> f ` {s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> V"
    proof (intro allI impI)
      fix i assume hi: "i < n_sub"
      obtain W where hW: "W \<in> {W_U, W_V}"
          and hWsub: "{s. sub0 i \<le> s \<and> s \<le> sub0 (Suc i) \<and> 0 \<le> s \<and> s \<le> 1} \<subseteq> W"
        using hsub0_cover hi by blast
      have hpiece_sub_W: "{s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> W"
      proof
        fix x assume "x \<in> {s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)}"
        hence "x \<in> I_set" "sub0 i \<le> x" "x \<le> sub0 (Suc i)" by auto
        hence "0 \<le> x" "x \<le> 1" unfolding top1_unit_interval_def by auto
        hence "x \<in> {s. sub0 i \<le> s \<and> s \<le> sub0 (Suc i) \<and> 0 \<le> s \<and> s \<le> 1}"
          using \<open>sub0 i \<le> x\<close> \<open>x \<le> sub0 (Suc i)\<close> by simp
        thus "x \<in> W" using hWsub by (by100 blast)
      qed
      show "f ` {s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> U
          \<or> f ` {s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> V"
      proof (cases "W = W_U")
        case True
        hence "{s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> I_set \<inter> W_U"
          using hpiece_sub_W by (by100 blast)
        hence "{s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> {t \<in> I_set. f t \<in> U}"
          using hpreU_eq by simp
        thus ?thesis by (by100 blast)
      next
        case False
        hence "W = W_V" using hW by (by100 blast)
        hence "{s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> I_set \<inter> W_V"
          using hpiece_sub_W by (by100 blast)
        hence "{s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> {t \<in> I_set. f t \<in> V}"
          using hpreV_eq by simp
        thus ?thesis by (by100 blast)
      qed
    qed
    \<comment> \<open>Endpoints: each sub0 i is in [0,1], and is in both adjacent pieces.
       If adjacent pieces map to different sets, f(sub0 i) \<in> U \<inter> V.
       After merging consecutive same-set pieces, all internal endpoints are transitions.
       f(0) = x0 \<in> U\<inter>V, f(1) = x0 \<in> U\<inter>V.\<close>
    \<comment> \<open>Munkres deletion: if f(sub0(i)) \<notin> U\<inter>V for some 0<i<n_sub, delete sub0(i).
       Both adjacent pieces map to the same set, so the merged piece still maps to U or V.
       Repeat until all internal points are in U\<inter>V. Formalized via filtering.\<close>
    define good where "good i = (i = 0 \<or> i = n_sub \<or> f (sub0 i) \<in> U \<inter> V)" for i
    define glist where "glist = filter good [0..<Suc n_sub]"
    \<comment> \<open>0 and n_sub are always good.\<close>
    have hg0: "good 0" unfolding good_def by simp
    have hgn: "good n_sub" unfolding good_def by simp
    have h0_mem: "0 \<in> set glist" unfolding glist_def using hg0 hn_sub by simp
    have hn_mem: "n_sub \<in> set glist" unfolding glist_def using hgn by simp
    have hglist_sorted: "sorted glist" unfolding glist_def
      by (metis sorted_wrt_filter sorted_upt)
    have hglist_distinct: "distinct glist" unfolding glist_def by simp
    have hglist_sub: "set glist \<subseteq> {0..n_sub}" unfolding glist_def by auto
    have h0_ne_n: "(0::nat) \<noteq> n_sub" using hn_sub by simp
    have hglist_len: "length glist \<ge> 2"
    proof -
      have "card {0, n_sub} = 2" using h0_ne_n by simp
      moreover have "{0, n_sub} \<subseteq> set glist" using h0_mem hn_mem by (by100 blast)
      moreover have "card (set glist) = length glist" using hglist_distinct by (rule distinct_card)
      ultimately show ?thesis using card_mono[OF finite_set \<open>{0, n_sub} \<subseteq> set glist\<close>] by linarith
    qed
    define n1 where "n1 = length glist - 1"
    have hn1_ge: "n1 \<ge> 1" using hglist_len unfolding n1_def by simp
    define sub1 where "sub1 j = sub0 (glist ! j)" for j
    have hgl_0: "glist ! 0 = 0"
    proof -
      obtain j where hj: "glist ! j = 0" "j < length glist"
        using h0_mem by (metis in_set_conv_nth)
      have "glist ! 0 \<le> glist ! j"
        by (rule sorted_nth_mono[OF hglist_sorted]) (use hj hglist_len in auto)
      hence "glist ! 0 \<le> 0" using hj(1) by simp
      moreover have "glist ! 0 \<ge> 0" by simp
      ultimately show ?thesis by simp
    qed
    have hgl_n: "glist ! n1 = n_sub"
    proof -
      obtain j where hj: "glist ! j = n_sub" "j < length glist"
        using hn_mem by (metis in_set_conv_nth)
      have "glist ! j \<le> glist ! n1"
        by (rule sorted_nth_mono[OF hglist_sorted])
           (use hj hglist_len in \<open>auto simp: n1_def\<close>)
      hence "n_sub \<le> glist ! n1" using hj(1) by simp
      moreover have "glist ! n1 \<le> n_sub"
      proof -
        have "glist ! n1 \<in> set glist"
          using hglist_len unfolding n1_def by (intro nth_mem) simp
        thus ?thesis using hglist_sub by auto
      qed
      ultimately show ?thesis by simp
    qed
    have hsub1_0: "sub1 0 = 0" unfolding sub1_def using hgl_0 hsub0_0 by simp
    have hsub1_n: "sub1 n1 = 1" unfolding sub1_def using hgl_n hsub0_n by simp
    have hsub0_strict_mono: "\<And>j k. j < k \<Longrightarrow> k \<le> n_sub \<Longrightarrow> sub0 j < sub0 k"
    proof -
      fix j k :: nat assume "j < k" "k \<le> n_sub"
      thus "sub0 j < sub0 k"
      proof (induction k)
        case 0 thus ?case by simp
      next
        case (Suc k)
        show ?case
        proof (cases "j = k")
          case True thus ?thesis using hsub0_mono Suc.prems by simp
        next
          case False
          hence "j < k" using Suc.prems by simp
          hence "sub0 j < sub0 k" using Suc.IH Suc.prems by simp
          also have "sub0 k < sub0 (Suc k)" using hsub0_mono Suc.prems by simp
          finally show ?thesis .
        qed
      qed
    qed
    have hsub1_mono: "\<forall>i<n1. sub1 i < sub1 (Suc i)"
    proof (intro allI impI)
      fix i assume hi: "i < n1"
      have hi_len: "i < length glist" using hi n1_def hglist_len by linarith
      have hsi_len: "Suc i < length glist" using hi n1_def hglist_len by linarith
      have "glist ! i < glist ! Suc i"
        using sorted_nth_mono[OF hglist_sorted, of i "Suc i"] hsi_len
              nth_eq_iff_index_eq[OF hglist_distinct hi_len hsi_len]
        by linarith
      moreover have "glist ! Suc i \<le> n_sub"
      proof -
        have "glist ! Suc i \<in> set glist" using hsi_len by (rule nth_mem)
        thus ?thesis using hglist_sub by auto
      qed
      ultimately show "sub1 i < sub1 (Suc i)" unfolding sub1_def
        using hsub0_strict_mono by simp
    qed
    \<comment> \<open>Key lemma: if f(sub0(k)) \<notin> U\<inter>V for 0 < k < n_sub, both adjacent original pieces
       map to the same set. Proof: sub0(k) is in both pieces. f(sub0(k)) \<in> U \<or> V (from X=U\<union>V).
       If f(sub0(k)) \<in> U - V: piece k-1 maps into f\<inverse>(U) (sub0(k) in piece k-1 and f(sub0(k)) \<in> U
       forces piece k-1 into U since it maps to U or V and intersects U).
       Similarly piece k maps into U.\<close>
    have h_deleted_same: "\<And>k. 0 < k \<Longrightarrow> k < n_sub \<Longrightarrow> f (sub0 k) \<notin> U \<inter> V \<Longrightarrow>
        (f ` {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k} \<subseteq> U
         \<and> f ` {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)} \<subseteq> U)
        \<or> (f ` {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k} \<subseteq> V
         \<and> f ` {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)} \<subseteq> V)"
    proof -
      fix k assume hk_pos: "0 < k" and hk_lt: "k < n_sub" and hk_not: "f (sub0 k) \<notin> U \<inter> V"
      have hk_prev: "k - 1 < n_sub" using hk_pos hk_lt by simp
      have hSuc_prev: "Suc (k-1) = k" using hk_pos by simp
      \<comment> \<open>Piece k-1 and piece k each map to U or V.\<close>
      have hprev: "f ` {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k} \<subseteq> U
          \<or> f ` {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k} \<subseteq> V"
        using hsub0_UV[rule_format, OF hk_prev] hSuc_prev by simp
      have hcurr: "f ` {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)} \<subseteq> U
          \<or> f ` {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)} \<subseteq> V"
        using hsub0_UV[rule_format, OF hk_lt] by simp
      \<comment> \<open>sub0(k) is in both pieces (as an I_set point).\<close>
      have hk_in_I: "sub0 k \<in> I_set"
      proof -
        have "sub0 0 \<le> sub0 k"
          using hsub0_strict_mono[of 0 k] hk_pos hk_lt by linarith
        hence "0 \<le> sub0 k" using hsub0_0 by linarith
        moreover have "sub0 k \<le> sub0 n_sub"
          using hsub0_strict_mono[of k n_sub] hk_lt by linarith
        hence "sub0 k \<le> 1" using hsub0_n by linarith
        ultimately show ?thesis unfolding top1_unit_interval_def by simp
      qed
      have "sub0 (k-1) \<le> sub0 k"
        using hsub0_mono[rule_format, of "k-1"] hk_pos hk_lt hSuc_prev by auto
      have hk_in_prev: "sub0 k \<in> {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k}"
        using hk_in_I \<open>sub0 (k-1) \<le> sub0 k\<close> by simp
      have "sub0 k \<le> sub0 (Suc k)" using hsub0_mono[rule_format, OF hk_lt] by linarith
      have hk_in_curr: "sub0 k \<in> {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)}"
        using hk_in_I \<open>sub0 k \<le> sub0 (Suc k)\<close> by simp
      \<comment> \<open>f(sub0(k)) \<in> U \<union> V but not U \<inter> V, so either U-V or V-U.\<close>
      have hfk_UV: "f (sub0 k) \<in> U \<union> V"
        using hprev hk_in_prev by (by100 blast)
      show "(f ` {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k} \<subseteq> U
         \<and> f ` {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)} \<subseteq> U)
        \<or> (f ` {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k} \<subseteq> V
         \<and> f ` {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)} \<subseteq> V)"
      proof (cases "f (sub0 k) \<in> U")
        case True
        hence "f (sub0 k) \<notin> V" using hk_not by (by100 blast)
        have "f ` {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k} \<subseteq> U"
          using hprev hk_in_prev \<open>f (sub0 k) \<notin> V\<close> by (by100 blast)
        moreover have "f ` {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)} \<subseteq> U"
          using hcurr hk_in_curr \<open>f (sub0 k) \<notin> V\<close> by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      next
        case False
        hence "f (sub0 k) \<in> V" using hfk_UV by (by100 blast)
        hence "f (sub0 k) \<notin> U" using hk_not by (by100 blast)
        have "f ` {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k} \<subseteq> V"
          using hprev hk_in_prev \<open>f (sub0 k) \<notin> U\<close> by (by100 blast)
        moreover have "f ` {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)} \<subseteq> V"
          using hcurr hk_in_curr \<open>f (sub0 k) \<notin> U\<close> by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
    qed
    \<comment> \<open>All original pieces between consecutive good points map to the same set (U or V).
       Proof by induction: if a deleted point is between them, h_deleted_same says
       both adjacent pieces map to the same set, so we can extend by one step.\<close>
    have h_range_same: "\<And>a b. a < b \<Longrightarrow> b \<le> n_sub \<Longrightarrow>
        (\<forall>k. a < k \<longrightarrow> k < b \<longrightarrow> f (sub0 k) \<notin> U \<inter> V) \<Longrightarrow>
        (\<forall>j. a \<le> j \<longrightarrow> j < b \<longrightarrow>
          f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> U)
        \<or> (\<forall>j. a \<le> j \<longrightarrow> j < b \<longrightarrow>
          f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> V)"
    proof -
      fix a b :: nat assume hab: "a < b" "b \<le> n_sub"
          and hno_good: "\<forall>k. a < k \<longrightarrow> k < b \<longrightarrow> f (sub0 k) \<notin> U \<inter> V"
      \<comment> \<open>Base: piece a maps to U or V.\<close>
      have ha_lt: "a < n_sub" using hab by simp
      have hpiece_a: "f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> U
          \<or> f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> V"
        using hsub0_UV[rule_format, OF ha_lt] by simp
      \<comment> \<open>Induction: extend from piece a to piece b-1.\<close>
      \<comment> \<open>Each piece j \<in> [a,b) maps to the same set as piece a. Prove by induction on j-a.\<close>
      have h_all_same_as_a: "\<And>j. a \<le> j \<Longrightarrow> j < b \<Longrightarrow>
          (f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> U \<longrightarrow>
           f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> U)
        \<and> (f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> V \<longrightarrow>
           f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> V)"
      proof -
        fix j assume haj: "a \<le> j" "j < b"
        \<comment> \<open>Prove: if piece a \<subseteq> S (for S = U or V), then piece j \<subseteq> S.
           By strong induction on j-a. Key step: sub0(j) \<in> piece(j-1) and piece(j-1) \<subseteq> S (IH).
           So f(sub0(j)) \<in> S. Since f(sub0(j)) \<notin> U\<inter>V, f(sub0(j)) \<in> S - (other set).
           h_deleted_same then gives piece(j) \<subseteq> S.\<close>
        have "\<And>S. S \<in> {U, V} \<Longrightarrow> f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> S \<Longrightarrow>
            f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> S"
        proof -
          fix S assume hS: "S \<in> {U, V}" and hpieceA: "f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> S"
          \<comment> \<open>By induction on j-a: all pieces in [a,j] map to S.\<close>
          have "\<And>j'. a \<le> j' \<Longrightarrow> j' < b \<Longrightarrow> f ` {s\<in>I_set. sub0 j' \<le> s \<and> s \<le> sub0 (Suc j')} \<subseteq> S"
          proof -
            fix j' assume "a \<le> j'" "j' < b"
            thus "f ` {s\<in>I_set. sub0 j' \<le> s \<and> s \<le> sub0 (Suc j')} \<subseteq> S"
            proof (induction "j' - a" arbitrary: j')
              case 0 hence "j' = a" by simp thus ?case using hpieceA by simp
            next
              case (Suc n)
              hence hj'_pos: "a < j'" by linarith
              have hj'_prev: "a \<le> j' - 1" "j' - 1 < b" using hj'_pos Suc.prems by linarith+
              have "j' - 1 - a = n" using Suc.hyps(2) by linarith
              hence hIH: "f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 (Suc (j'-1))} \<subseteq> S"
                using Suc.hyps(1)[of "j'-1"] hj'_prev by simp
              \<comment> \<open>sub0(j') \<in> piece(j'-1), so f(sub0(j')) \<in> S.\<close>
              have hSuc_eq: "Suc (j' - 1) = j'" using hj'_pos by simp
              hence hIH': "f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'} \<subseteq> S" using hIH by simp
              have hj'_lt_nsub: "j' < n_sub" using Suc.prems(2) hab(2) by simp
              have hj'_in_I: "sub0 j' \<in> I_set"
              proof -
                have "sub0 0 < sub0 j'" using hsub0_strict_mono[of 0 j'] hj'_pos hj'_lt_nsub by linarith
                hence "0 \<le> sub0 j'" using hsub0_0 by linarith
                moreover have "sub0 j' < sub0 n_sub" using hsub0_strict_mono[of j' n_sub] hj'_lt_nsub by simp
                hence "sub0 j' \<le> 1" using hsub0_n by linarith
                ultimately show ?thesis unfolding top1_unit_interval_def by simp
              qed
              have "j' - 1 < n_sub" using hj'_lt_nsub by simp
              have "sub0 (j'-1) < sub0 j'"
                using hsub0_mono[rule_format, of "j'-1"] \<open>j'-1 < n_sub\<close> hSuc_eq by simp
              hence "sub0 (j'-1) \<le> sub0 j'" by linarith
              hence "sub0 j' \<in> {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'}"
                using hj'_in_I by simp
              hence "f (sub0 j') \<in> S" using hIH' by (by100 blast)
              have hj'_not: "f (sub0 j') \<notin> U \<inter> V" using hno_good hj'_pos Suc.prems(2) by simp
              have hj'_lt: "j' < n_sub" using Suc.prems(2) hab(2) by simp
              \<comment> \<open>h_deleted_same at j': both adjacent pieces map to same set.\<close>
              have h_same: "(f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'} \<subseteq> U
                   \<and> f ` {s\<in>I_set. sub0 j' \<le> s \<and> s \<le> sub0 (Suc j')} \<subseteq> U)
                \<or> (f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'} \<subseteq> V
                   \<and> f ` {s\<in>I_set. sub0 j' \<le> s \<and> s \<le> sub0 (Suc j')} \<subseteq> V)"
                using h_deleted_same[of j'] hj'_pos hj'_lt hj'_not by simp
              \<comment> \<open>f(sub0(j')) \<in> S and \<notin> U\<inter>V. If S=U: f(sub0(j')) \<in> U-V, h_same gives U branch.
                 If S=V: f(sub0(j')) \<in> V-U, h_same gives V branch.\<close>
              show "f ` {s\<in>I_set. sub0 j' \<le> s \<and> s \<le> sub0 (Suc j')} \<subseteq> S"
              proof -
                \<comment> \<open>sub0(j') \<in> piece(j'-1) and f(sub0(j')) \<in> S, \<notin> U\<inter>V.
                   If S = U: f(sub0(j')) \<notin> V. piece(j'-1) contains sub0(j') so piece(j'-1) \<not>\<subseteq> V.
                   h_same: both \<subseteq> U or both \<subseteq> V. Since \<not>\<subseteq> V, both \<subseteq> U.
                   Similarly for S = V.\<close>
                have "f (sub0 j') \<notin> U \<or> f (sub0 j') \<notin> V" using hj'_not by (by100 blast)
                have hprev_not_other: "(S = U \<longrightarrow> \<not> f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'} \<subseteq> V)
                    \<and> (S = V \<longrightarrow> \<not> f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'} \<subseteq> U)"
                proof (intro conjI impI)
                  assume "S = U"
                  hence "f (sub0 j') \<notin> V" using \<open>f (sub0 j') \<in> S\<close> hj'_not by (by100 blast)
                  moreover have "sub0 j' \<in> {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'}"
                    using hj'_in_I \<open>sub0 (j'-1) \<le> sub0 j'\<close> by simp
                  ultimately show "\<not> f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'} \<subseteq> V"
                    by (by100 blast)
                next
                  assume "S = V"
                  hence "f (sub0 j') \<notin> U" using \<open>f (sub0 j') \<in> S\<close> hj'_not by (by100 blast)
                  moreover have "sub0 j' \<in> {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'}"
                    using hj'_in_I \<open>sub0 (j'-1) \<le> sub0 j'\<close> by simp
                  ultimately show "\<not> f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'} \<subseteq> U"
                    by (by100 blast)
                qed
                show ?thesis
                proof (cases "S = U")
                  case True thus ?thesis using h_same hprev_not_other by (by100 blast)
                next
                  case False hence hSV: "S = V" using hS by (by100 blast)
                  hence "\<not> f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'} \<subseteq> U"
                    using hprev_not_other by simp
                  thus ?thesis using h_same hSV by (by100 blast)
                qed
              qed
            qed
          qed
          thus "f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> S" using haj by simp
        qed
        note hdir = this
        show "(f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> U \<longrightarrow>
           f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> U)
        \<and> (f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> V \<longrightarrow>
           f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> V)"
          using hdir[of U] hdir[of V] by simp
      qed
      show "(\<forall>j. a \<le> j \<longrightarrow> j < b \<longrightarrow>
          f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> U)
        \<or> (\<forall>j. a \<le> j \<longrightarrow> j < b \<longrightarrow>
          f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> V)"
      proof (cases "f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> U")
        case True
        have "\<forall>j. a \<le> j \<longrightarrow> j < b \<longrightarrow>
            f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> U"
        proof (intro allI impI)
          fix j assume "a \<le> j" "j < b"
          thus "f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> U"
            using True h_all_same_as_a[of j] by simp
        qed
        thus ?thesis by (by100 blast)
      next
        case False
        hence "f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> V"
          using hpiece_a by (by100 blast)
        hence "\<forall>j. a \<le> j \<longrightarrow> j < b \<longrightarrow>
            f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> V"
          using h_all_same_as_a by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
    qed
    have hsub1_UV: "\<forall>i<n1. f ` {s\<in>I_set. sub1 i \<le> s \<and> s \<le> sub1 (Suc i)} \<subseteq> U
                         \<or> f ` {s\<in>I_set. sub1 i \<le> s \<and> s \<le> sub1 (Suc i)} \<subseteq> V"
    proof (intro allI impI)
      fix i assume hi: "i < n1"
      let ?a = "glist ! i" and ?b = "glist ! Suc i"
      have hi_len: "i < length glist" using hi n1_def hglist_len by linarith
      have hsi_len: "Suc i < length glist" using hi n1_def hglist_len by linarith
      have hab_lt: "?a < ?b"
        using sorted_nth_mono[OF hglist_sorted, of i "Suc i"] hsi_len
              nth_eq_iff_index_eq[OF hglist_distinct hi_len hsi_len] by linarith
      have hb_le: "?b \<le> n_sub"
      proof -
        have "?b \<in> set glist" using hsi_len by (rule nth_mem)
        thus ?thesis using hglist_sub by auto
      qed
      have hno_good_ab: "\<forall>k. ?a < k \<longrightarrow> k < ?b \<longrightarrow> f (sub0 k) \<notin> U \<inter> V"
      proof (intro allI impI)
        fix k assume hk: "?a < k" "k < ?b"
        \<comment> \<open>k is between consecutive glist elements, so k \<notin> set glist.\<close>
        have "k \<notin> set glist"
        proof
          assume "k \<in> set glist"
          then obtain m where hm: "m < length glist" "glist ! m = k" by (metis in_set_conv_nth)
          \<comment> \<open>glist!i < k = glist!m, and glist sorted+distinct \<Rightarrow> i < m.\<close>
          have "i \<noteq> m" using hk(1) hm(2) by auto
          have "i \<le> m \<or> m \<le> i" by linarith
          hence "i < m"
          proof
            assume "i \<le> m" thus "i < m" using \<open>i \<noteq> m\<close> by simp
          next
            assume "m \<le> i"
            hence "glist ! m \<le> glist ! i" using sorted_nth_mono[OF hglist_sorted] hi_len hm(1) by auto
            hence "k \<le> ?a" using hm(2) by simp
            thus "i < m" using hk(1) by simp
          qed
          \<comment> \<open>k = glist!m < glist!(Suc i), and sorted+distinct \<Rightarrow> m < Suc i.\<close>
          have "m \<noteq> Suc i"
          proof
            assume "m = Suc i"
            hence "glist ! m = ?b" by simp
            thus False using hm(2) hk(2) by simp
          qed
          have "m \<le> Suc i \<or> Suc i \<le> m" by linarith
          hence "m < Suc i"
          proof
            assume "m \<le> Suc i" thus ?thesis using \<open>m \<noteq> Suc i\<close> by simp
          next
            assume "Suc i \<le> m"
            hence "glist ! Suc i \<le> glist ! m" using sorted_nth_mono[OF hglist_sorted] hsi_len hm(1) by auto
            thus ?thesis using hm(2) hk(2) by simp
          qed
          thus False using \<open>i < m\<close> by simp
        qed
        have "k \<le> n_sub" using hk(2) hb_le by linarith
        hence "k \<in> set [0..<Suc n_sub]" by auto
        hence "\<not> good k" using \<open>k \<notin> set glist\<close> unfolding glist_def by auto
        moreover have "k \<noteq> 0" using hk(1) by simp
        moreover have "k \<noteq> n_sub"
        proof -
          have "k < n_sub" using \<open>k \<le> n_sub\<close> hk(2) hb_le by linarith
          thus ?thesis by simp
        qed
        ultimately show "f (sub0 k) \<notin> U \<inter> V" unfolding good_def by simp
      qed
      \<comment> \<open>h_range_same: all original pieces in [?a, ?b) map to U, or all map to V.\<close>
      have h_all: "(\<forall>j. ?a \<le> j \<longrightarrow> j < ?b \<longrightarrow>
          f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> U)
        \<or> (\<forall>j. ?a \<le> j \<longrightarrow> j < ?b \<longrightarrow>
          f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> V)"
        by (rule h_range_same[OF hab_lt hb_le hno_good_ab])
      \<comment> \<open>Every point in merged piece is in some original piece, hence f maps it to S.\<close>
      show "f ` {s\<in>I_set. sub1 i \<le> s \<and> s \<le> sub1 (Suc i)} \<subseteq> U
          \<or> f ` {s\<in>I_set. sub1 i \<le> s \<and> s \<le> sub1 (Suc i)} \<subseteq> V"
      proof -
        \<comment> \<open>For any s in merged piece, find j with sub0(j) \<le> s \<le> sub0(j+1).\<close>
        have hpoint: "\<And>s. s \<in> I_set \<Longrightarrow> sub0 ?a \<le> s \<Longrightarrow> s \<le> sub0 ?b \<Longrightarrow>
            \<exists>j. ?a \<le> j \<and> j < ?b \<and> sub0 j \<le> s \<and> s \<le> sub0 (Suc j)"
        proof -
          fix s assume hs: "s \<in> I_set" "sub0 ?a \<le> s" "s \<le> sub0 ?b"
          \<comment> \<open>Find the largest j with ?a \<le> j \<le> ?b and sub0(j) \<le> s.\<close>
          define J where "J = {j. ?a \<le> j \<and> j \<le> ?b \<and> sub0 j \<le> s}"
          have "?a \<in> J" using hs(2) hab_lt unfolding J_def by simp
          hence "J \<noteq> {}" by (by100 blast)
          have "finite J" unfolding J_def by simp
          have "J \<subseteq> {?a..?b}" unfolding J_def by auto
          obtain j where hj: "j \<in> J" "\<forall>k \<in> J. k \<le> j"
            using \<open>finite J\<close> \<open>J \<noteq> {}\<close> by (metis Max_in Max_ge)
          have "?a \<le> j" "j \<le> ?b" "sub0 j \<le> s" using hj(1) unfolding J_def by auto
          \<comment> \<open>If j = ?b, take ?b-1 instead (which works since sub0(?b-1) \<le> s \<le> sub0(?b)).\<close>
          define j' where "j' = (if j < ?b then j else ?b - 1)"
          have "?a \<le> j'" and "j' < ?b"
            unfolding j'_def using \<open>?a \<le> j\<close> hab_lt by auto
          have "sub0 j' \<le> s"
          proof (cases "j < ?b")
            case True thus ?thesis unfolding j'_def using \<open>sub0 j \<le> s\<close> by simp
          next
            case False
            hence "j = ?b" using \<open>j \<le> ?b\<close> by simp
            hence "sub0 ?b \<le> s" using \<open>sub0 j \<le> s\<close> by simp
            hence "s = sub0 ?b" using hs(3) by linarith
            have "sub0 (?b - 1) < sub0 ?b"
              using hsub0_strict_mono[of "?b-1" "?b"] hab_lt hb_le by linarith
            have "j' = ?b - 1" unfolding j'_def using False by simp
            hence "sub0 j' = sub0 (?b - 1)" by simp
            thus ?thesis using \<open>sub0 (?b - 1) < sub0 ?b\<close> \<open>s = sub0 ?b\<close> by linarith
          qed
          have "s \<le> sub0 (Suc j')"
          proof (cases "j < ?b")
            case True
            hence "j' = j" unfolding j'_def by simp
            show ?thesis
            proof (rule ccontr)
              assume "\<not> s \<le> sub0 (Suc j')"
              hence "sub0 (Suc j') \<le> s" by linarith
              hence "sub0 (Suc j) \<le> s" using \<open>j' = j\<close> by simp
              have "Suc j \<in> J" unfolding J_def
                using \<open>?a \<le> j\<close> True \<open>sub0 (Suc j) \<le> s\<close> by simp
              hence "Suc j \<le> j" using hj(2) by simp
              thus False by simp
            qed
          next
            case False
            hence hj_eq_b: "j = ?b" using \<open>j \<le> ?b\<close> by simp
            hence "j' = ?b - 1" unfolding j'_def by simp
            hence "Suc j' = ?b" using hab_lt by simp
            show ?thesis using hs(3) \<open>Suc j' = ?b\<close> by simp
          qed
          show "\<exists>j. ?a \<le> j \<and> j < ?b \<and> sub0 j \<le> s \<and> s \<le> sub0 (Suc j)"
            using \<open>?a \<le> j'\<close> \<open>j' < ?b\<close> \<open>sub0 j' \<le> s\<close> \<open>s \<le> sub0 (Suc j')\<close> by (by100 blast)
        qed
        have hfinal: "\<And>S. (\<forall>j. ?a \<le> j \<longrightarrow> j < ?b \<longrightarrow>
            f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> S)
            \<Longrightarrow> f ` {s\<in>I_set. sub0 ?a \<le> s \<and> s \<le> sub0 ?b} \<subseteq> S"
        proof -
          fix S assume hS: "\<forall>j. ?a \<le> j \<longrightarrow> j < ?b \<longrightarrow>
              f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> S"
          show "f ` {s\<in>I_set. sub0 ?a \<le> s \<and> s \<le> sub0 ?b} \<subseteq> S"
          proof
            fix y assume "y \<in> f ` {s\<in>I_set. sub0 ?a \<le> s \<and> s \<le> sub0 ?b}"
            then obtain s where hs: "s \<in> I_set" "sub0 ?a \<le> s" "s \<le> sub0 ?b" "y = f s"
              by (by100 blast)
            obtain j where hj: "?a \<le> j" "j < ?b" "sub0 j \<le> s" "s \<le> sub0 (Suc j)"
              using hpoint[OF hs(1-3)] by (by100 blast)
            have "f s \<in> S" using hS hj hs(1) by (by100 blast)
            thus "y \<in> S" using hs(4) by simp
          qed
        qed
        have hsub1_eq: "sub1 i = sub0 ?a" "sub1 (Suc i) = sub0 ?b" unfolding sub1_def by simp_all
        show ?thesis
        proof (rule disjE[OF h_all])
          assume "\<forall>j. ?a \<le> j \<longrightarrow> j < ?b \<longrightarrow> f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> U"
          hence "f ` {s\<in>I_set. sub0 ?a \<le> s \<and> s \<le> sub0 ?b} \<subseteq> U" by (rule hfinal)
          thus ?thesis unfolding sub1_def by simp
        next
          assume "\<forall>j. ?a \<le> j \<longrightarrow> j < ?b \<longrightarrow> f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> V"
          hence "f ` {s\<in>I_set. sub0 ?a \<le> s \<and> s \<le> sub0 ?b} \<subseteq> V" by (rule hfinal)
          thus ?thesis unfolding sub1_def by simp
        qed
      qed
    qed
    have hsub1_int: "\<forall>i\<le>n1. f (sub1 i) \<in> U \<inter> V"
    proof (intro allI impI)
      fix i assume "i \<le> n1"
      show "f (sub1 i) \<in> U \<inter> V"
      proof (cases "i = 0")
        case True thus ?thesis using hsub1_0 hf0 hx0 by simp
      next
        case False
        show ?thesis
        proof (cases "i = n1")
          case True thus ?thesis using hsub1_n hf1 hx0 by simp
        next
          case False
          \<comment> \<open>Internal good point: good(glist!i) holds, and glist!i \<noteq> 0, glist!i \<noteq> n_sub.\<close>
          have "0 < i" "i < n1" using \<open>i \<le> n1\<close> \<open>i \<noteq> 0\<close> \<open>i \<noteq> n1\<close> by auto
          have hi_lt_len: "i < length glist" using \<open>i < n1\<close> n1_def hglist_len by simp
          have "glist ! i \<in> set glist" by (rule nth_mem[OF hi_lt_len])
          have "set glist \<subseteq> {i. good i}" unfolding glist_def by auto
          hence "good (glist ! i)" using \<open>glist ! i \<in> set glist\<close> by (by100 blast)
          moreover have "glist ! i \<noteq> 0"
          proof
            assume "glist ! i = 0"
            hence "glist ! i = glist ! 0" using hgl_0 by simp
            have "0 < length glist" using hglist_len by linarith
            hence "i = 0" using nth_eq_iff_index_eq[OF hglist_distinct]
              hi_lt_len \<open>0 < length glist\<close> \<open>glist ! i = glist ! 0\<close> by simp
            thus False using \<open>0 < i\<close> by simp
          qed
          moreover have "glist ! i \<noteq> n_sub"
          proof
            assume "glist ! i = n_sub"
            hence "glist ! i = glist ! n1" using hgl_n by simp
            have "n1 < length glist" using hglist_len n1_def by simp
            hence "i = n1" using nth_eq_iff_index_eq[OF hglist_distinct]
              hi_lt_len \<open>n1 < length glist\<close> \<open>glist ! i = glist ! n1\<close> by simp
            thus False using \<open>i < n1\<close> by simp
          qed
          ultimately show ?thesis unfolding sub1_def good_def by simp
        qed
      qed
    qed
    show ?thesis
      by (rule that[OF hn1_ge hsub1_0 hsub1_n hsub1_mono hsub1_UV hsub1_int])
  qed
  \<comment> \<open>Step 2: For each subinterval, define fi = f restricted + reparametrized.
     Choose paths \<alpha>i in U\<inter>V from x0 to f(ai). Set gi = (\<alpha>_{i-1} * fi) * rev \<alpha>i.\<close>
  \<comment> \<open>Step 2: Construct loops gi at x0, each in U or V, with f \<simeq> g1*...*gm.
     For each i, fi = f restricted to [ai, ai+1] and reparametrized to [0,1].
     Choose \<alpha>i: paths in U\<inter>V from x0 to f(ai) (U\<inter>V path-connected, f(ai) \<in> U\<inter>V).
     Set gi = rev(\<alpha>i) * fi * \<alpha>_{i+1}. Each gi is a loop at x0 in U or V.\<close>
  \<comment> \<open>Step 2a: Choose connecting paths \<alpha>i in U\<inter>V from x0 to f(subdivision i).\<close>
  have hUV_pc: "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
    by (rule assms(5))
  have "\<forall>i\<le>m. \<exists>\<alpha>. top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0 (f (subdivision i)) \<alpha>"
  proof (intro allI impI)
    fix i assume "i \<le> m"
    have "f (subdivision i) \<in> U \<inter> V" using hsub_int \<open>i \<le> m\<close> by blast
    thus "\<exists>\<alpha>. top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0 (f (subdivision i)) \<alpha>"
      using hUV_pc hx0 unfolding top1_path_connected_on_def by (by100 blast)
  qed
  \<comment> \<open>Step 2b: Construct fi (reparametrized restrictions) and gi (conjugated loops).\<close>
  \<comment> \<open>Step 2c: Show f \<simeq> g1*...*gm and each gi is a loop in U or V.\<close>
  obtain gs :: "(real \<Rightarrow> 'a) list" where
    hgs_len: "length gs = m" and
    hgs_loops: "\<forall>i<m. top1_is_loop_on X TX x0 (gs!i)
        \<and> (gs!i ` I_set \<subseteq> U \<or> gs!i ` I_set \<subseteq> V)" and
    hgs_product: "top1_path_homotopic_on X TX x0 x0 f
        (foldr top1_path_product gs (top1_constant_path x0))"
  proof -
    \<comment> \<open>Choose connecting paths \<alpha>i from x0 to f(sub(i)) in U\<inter>V.\<close>
    have "\<forall>i\<le>m. \<exists>\<alpha>. top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0 (f (subdivision i)) \<alpha>"
    proof (intro allI impI)
      fix i assume "i \<le> m"
      have "f (subdivision i) \<in> U \<inter> V" using hsub_int \<open>i \<le> m\<close> by blast
      thus "\<exists>\<alpha>. top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0 (f (subdivision i)) \<alpha>"
        using hUV_pc hx0 unfolding top1_path_connected_on_def by (by100 blast)
    qed
    \<comment> \<open>For each i<m: define fi as f reparametrized on [sub(i), sub(i+1)].
       Define gi = rev(\<alpha>i) * fi * \<alpha>_{i+1}. Each gi is a loop at x0 in U or V.
       The telescoping product g1*...*gm = rev(\<alpha>0) * f * \<alpha>m = f (since \<alpha>0 = \<alpha>m = const_{x0}).
       Each gi maps into U or V because fi maps into U or V and \<alpha>i maps into U\<inter>V \<subseteq> U \<inter> V.\<close>
    \<comment> \<open>For each i<m, define:
       fi(t) = f(sub(i) + t*(sub(i+1)-sub(i))): reparametrization of f on [sub(i),sub(i+1)].
       gi = top1_path_product (top1_path_reverse (\<alpha>i)) (top1_path_product fi (\<alpha>(i+1))):
         loop at x0 via rev(\<alpha>i) from x0 to f(sub(i)), then fi to f(sub(i+1)), then \<alpha>(i+1) to x0.
       Each gi maps into U or V (fi maps into U or V, \<alpha>i maps into U\<inter>V \<subseteq> U,V).
       Telescoping: f \<simeq> f1*f2*...*fm (reparametrization of f)
                      \<simeq> (rev(\<alpha>0)*f1*\<alpha>1) * (rev(\<alpha>1)*f2*\<alpha>2) * ... * (rev(\<alpha>_{m-1})*fm*\<alpha>_m)
                      (by inserting \<alpha>i*rev(\<alpha>i) \<simeq> const between consecutive pieces).\<close>
    \<comment> \<open>Step 2a: Choose connecting paths \<alpha>i.\<close>
    obtain \<alpha>s where h\<alpha>s: "\<forall>i\<le>m. top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))
        x0 (f (subdivision i)) (\<alpha>s i)"
    proof -
      have "\<forall>i. \<exists>\<alpha>. i \<le> m \<longrightarrow> top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))
          x0 (f (subdivision i)) \<alpha>"
      proof
        fix i show "\<exists>\<alpha>. i \<le> m \<longrightarrow> top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))
            x0 (f (subdivision i)) \<alpha>"
        proof (cases "i \<le> m")
          case True
          hence "f (subdivision i) \<in> U \<inter> V" using hsub_int by blast
          then obtain \<alpha> where "top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))
              x0 (f (subdivision i)) \<alpha>"
            using hUV_pc hx0 unfolding top1_path_connected_on_def by (by100 blast)
          thus ?thesis by (by100 blast)
        next
          case False thus ?thesis by simp
        qed
      qed
      hence "\<exists>\<alpha>s. \<forall>i. i \<le> m \<longrightarrow> top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))
          x0 (f (subdivision i)) (\<alpha>s i)" by metis
      thus ?thesis using that by (by100 blast)
    qed
    \<comment> \<open>Modify \<alpha>s so \<alpha>s(0) = const_x0 and \<alpha>s(m) = const_x0 (Munkres convention).\<close>
    define \<alpha>s' where "\<alpha>s' i = (if i = 0 \<or> i = m then top1_constant_path x0 else \<alpha>s i)" for i
    have h\<alpha>s': "\<forall>i\<le>m. top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))
        x0 (f (subdivision i)) (\<alpha>s' i)"
    proof (intro allI impI)
      fix i assume "i \<le> m"
      show "top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0 (f (subdivision i)) (\<alpha>s' i)"
      proof (cases "i = 0 \<or> i = m")
        case True
        have h\<alpha>_const: "\<alpha>s' i = top1_constant_path x0" unfolding \<alpha>s'_def using True by simp
        have hf_x0: "f (subdivision i) = x0"
          using True hsub0 hsubm hf
          unfolding top1_is_loop_on_def top1_is_path_on_def by auto
        have hUVX: "U \<inter> V \<subseteq> X" using assms(2,3) unfolding openin_on_def by (by100 blast)
        have "is_topology_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
          by (rule subspace_topology_is_topology_on[OF is_topology_on_strict_imp[OF hT]])
             (use hUVX in blast)
        hence "top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0 x0 (top1_constant_path x0)"
          by (rule top1_constant_path_is_path) (rule hx0)
        thus ?thesis using h\<alpha>_const hf_x0 by simp
      next
        case False thus ?thesis unfolding \<alpha>s'_def using h\<alpha>s \<open>i \<le> m\<close> by simp
      qed
    qed
    have h\<alpha>s'_0: "\<alpha>s' 0 = top1_constant_path x0" unfolding \<alpha>s'_def by simp
    have h\<alpha>s'_m: "\<alpha>s' m = top1_constant_path x0" unfolding \<alpha>s'_def by simp
    \<comment> \<open>Step 2b: Define reparametrized pieces fi(t) = f(sub(i) + t*(sub(i+1)-sub(i))).\<close>
    define fi where "fi i = (\<lambda>t. f (subdivision i + t * (subdivision (Suc i) - subdivision i)))" for i
    \<comment> \<open>Step 2c: Define conjugated loops gi = (\<alpha>s' i * fi i) * rev(\<alpha>s' (Suc i)).\<close>
    define gi where "gi i = top1_path_product (top1_path_product (\<alpha>s' i) (fi i))
        (top1_path_reverse (\<alpha>s' (Suc i)))" for i
    \<comment> \<open>Step 2d: Build the list gs = [gi 0, gi 1, ..., gi (m-1)].\<close>
    define gs_list where "gs_list = map gi [0..<m]"
    have hgs_len: "length gs_list = m" unfolding gs_list_def by simp
    \<comment> \<open>Step 2e: Each gi is a loop at x0 in U or V.\<close>
    \<comment> \<open>Helper: subdivision is weakly monotone.\<close>
    have hsub_weak_mono: "\<And>j k. j \<le> k \<Longrightarrow> k \<le> m \<Longrightarrow> subdivision j \<le> subdivision k"
    proof -
      fix j k :: nat assume hjk: "j \<le> k" "k \<le> m"
      show "subdivision j \<le> subdivision k" using hjk
      proof (induction "k - j" arbitrary: k)
        case 0 thus ?case by simp
      next
        case (Suc d)
        hence "j \<le> k - 1" "k - 1 \<le> m" "k > 0" by linarith+
        have hIH: "subdivision j \<le> subdivision (k - 1)"
          using Suc.hyps(1)[of "k-1"] \<open>j \<le> k-1\<close> \<open>k-1 \<le> m\<close> Suc.hyps(2) by linarith
        have "k - 1 < m" using Suc.prems(2) \<open>k > 0\<close> by linarith
        have "Suc (k - 1) = k" using \<open>k > 0\<close> by simp
        hence "subdivision (k - 1) < subdivision k"
          using hsub_mono[rule_format, OF \<open>k-1 < m\<close>] by simp
        thus ?case using hIH by linarith
      qed
    qed
    have hsub_in_I: "\<And>j. j \<le> m \<Longrightarrow> subdivision j \<in> I_set"
    proof -
      fix j assume "j \<le> m"
      have "subdivision j \<ge> 0" using hsub_weak_mono[of 0 j] \<open>j \<le> m\<close> hsub0 by simp
      moreover have "subdivision j \<le> 1" using hsub_weak_mono[of j m] \<open>j \<le> m\<close> hsubm by simp
      ultimately show "subdivision j \<in> I_set" unfolding top1_unit_interval_def by simp
    qed
    \<comment> \<open>fi(i) is a path from f(sub(i)) to f(sub(i+1)) in X, with image in U or V.\<close>
    have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
      by (rule top1_is_loop_on_continuous[OF hf])
    have hfi_path: "\<And>i. i < m \<Longrightarrow> top1_is_path_on X TX (f (subdivision i)) (f (subdivision (Suc i))) (fi i)"
    proof -
      fix i assume hi: "i < m"
      show "top1_is_path_on X TX (f (subdivision i)) (f (subdivision (Suc i))) (fi i)"
        unfolding top1_is_path_on_def
      proof (intro conjI)
        show "top1_continuous_map_on I_set I_top X TX (fi i)"
        proof -
          define \<phi> where "\<phi> t = subdivision i + t * (subdivision (Suc i) - subdivision i)" for t
          have hfi_eq: "fi i = f \<circ> \<phi>" unfolding fi_def \<phi>_def comp_def by (rule ext) simp
          have h\<phi>_cont_on: "continuous_on I_set \<phi>" unfolding \<phi>_def by (intro continuous_intros)
          have h\<phi>_maps: "\<forall>t\<in>I_set. \<phi> t \<in> I_set"
          proof (intro ballI)
            fix t assume "t \<in> I_set"
            hence "0 \<le> t" "t \<le> 1" unfolding top1_unit_interval_def by auto
            have hDelta: "subdivision (Suc i) - subdivision i \<ge> 0"
              using hsub_mono[rule_format, OF hi] by simp
            have "\<phi> t \<ge> subdivision i" unfolding \<phi>_def
              using \<open>0 \<le> t\<close> hDelta by (simp add: mult_nonneg_nonneg)
            moreover have "\<phi> t \<le> subdivision (Suc i)"
            proof -
              have "t * (subdivision (Suc i) - subdivision i) \<le> 1 * (subdivision (Suc i) - subdivision i)"
                by (rule mult_right_mono[OF \<open>t \<le> 1\<close> hDelta])
              thus ?thesis unfolding \<phi>_def by simp
            qed
            moreover have "subdivision i \<ge> 0" using hsub_weak_mono[of 0 i] hi hsub0 by simp
            moreover have "subdivision (Suc i) \<le> 1" using hsub_weak_mono[of "Suc i" m] hi hsubm by simp
            ultimately show "\<phi> t \<in> I_set" unfolding top1_unit_interval_def by simp
          qed
          have h\<phi>_cont: "top1_continuous_map_on I_set I_top I_set I_top \<phi>"
          proof -
            have hItop: "I_top = subspace_topology UNIV top1_open_sets I_set"
              unfolding top1_unit_interval_topology_def top1_unit_interval_def by simp
            show ?thesis unfolding top1_continuous_map_on_def
            proof (intro conjI ballI)
              fix t assume "t \<in> I_set" thus "\<phi> t \<in> I_set" using h\<phi>_maps by simp
            next
              fix V assume hV: "V \<in> I_top"
              obtain W where hW: "open W" "V = I_set \<inter> W"
                using hV unfolding hItop subspace_topology_def top1_open_sets_def by auto
              have "{t \<in> I_set. \<phi> t \<in> V} = {t \<in> I_set. \<phi> t \<in> W}"
                using h\<phi>_maps hW(2) by (by100 blast)
              also have "\<dots> = I_set \<inter> \<phi> -` W" by (by100 blast)
              also have "\<dots> \<in> I_top"
              proof -
                have "\<exists>A. open A \<and> A \<inter> I_set = \<phi> -` W \<inter> I_set"
                  using iffD1[OF continuous_on_open_invariant h\<phi>_cont_on] hW(1) by simp
                then obtain A where "open A" "A \<inter> I_set = \<phi> -` W \<inter> I_set" by (by100 blast)
                hence "I_set \<inter> A \<in> I_top" unfolding hItop subspace_topology_def top1_open_sets_def
                  by (by100 blast)
                moreover have "I_set \<inter> \<phi> -` W = I_set \<inter> A"
                  using \<open>A \<inter> I_set = \<phi> -` W \<inter> I_set\<close> by (by100 blast)
                ultimately show ?thesis by simp
              qed
              finally show "{t \<in> I_set. \<phi> t \<in> V} \<in> I_top" .
            qed
          qed
          show ?thesis unfolding hfi_eq
            by (rule top1_continuous_map_on_comp[OF h\<phi>_cont hf_cont])
        qed
        show "fi i 0 = f (subdivision i)" unfolding fi_def by simp
        show "fi i 1 = f (subdivision (Suc i))" unfolding fi_def by simp
      qed
    qed
    have hfi_UV: "\<And>i. i < m \<Longrightarrow> fi i ` I_set \<subseteq> U \<or> fi i ` I_set \<subseteq> V"
    proof -
      fix i assume hi: "i < m"
      have "fi i ` I_set = f ` {s\<in>I_set. subdivision i \<le> s \<and> s \<le> subdivision (Suc i)}"
      proof (intro set_eqI iffI)
        fix y assume "y \<in> fi i ` I_set"
        then obtain t where ht: "t \<in> I_set" "y = fi i t" by (by100 blast)
        have hlb: "subdivision i + t * (subdivision (Suc i) - subdivision i) \<ge> subdivision i"
          using ht(1) hsub_mono[rule_format, OF hi]
          unfolding top1_unit_interval_def by (simp add: mult_nonneg_nonneg)
        moreover have hub: "subdivision i + t * (subdivision (Suc i) - subdivision i) \<le> subdivision (Suc i)"
        proof -
          have "t \<le> 1" using ht(1) unfolding top1_unit_interval_def by simp
          have "subdivision (Suc i) - subdivision i \<ge> 0" using hsub_mono[rule_format, OF hi] by simp
          hence "t * (subdivision (Suc i) - subdivision i) \<le> 1 * (subdivision (Suc i) - subdivision i)"
            using mult_right_mono[OF \<open>t \<le> 1\<close>] by simp
          thus ?thesis by simp
        qed
        moreover have "subdivision i + t * (subdivision (Suc i) - subdivision i) \<in> I_set"
        proof -
          have "subdivision 0 \<le> subdivision i"
          proof (cases "i = 0")
            case True thus ?thesis by simp
          next
            case False hence "0 < i" by simp
            show ?thesis
            proof (rule order.strict_implies_order)
              show "subdivision 0 < subdivision i"
                using \<open>0 < i\<close> hi hsub_mono
              proof (induction i)
                case 0 thus ?case by simp
              next
                case (Suc n)
                show ?case
                proof (cases "n = 0")
                  case True thus ?thesis using hsub_mono Suc.prems by simp
                next
                  case False
                  hence "subdivision 0 < subdivision n" using Suc by simp
                  also have "subdivision n < subdivision (Suc n)" using hsub_mono Suc.prems by simp
                  finally show ?thesis .
                qed
              qed
            qed
          qed
          hence "subdivision i \<ge> 0" using hsub0 by simp
          have "subdivision (Suc i) \<le> subdivision m"
          proof (cases "Suc i = m")
            case True thus ?thesis by simp
          next
            case False hence "Suc i < m" using hi by simp
            show ?thesis
            proof (rule order.strict_implies_order)
              show "subdivision (Suc i) < subdivision m"
                using \<open>Suc i < m\<close> hsub_mono
              proof (induction m)
                case 0 thus ?case by simp
              next
                case (Suc n)
                show ?case
                proof (cases "Suc i = n")
                  case True thus ?thesis using hsub_mono Suc.prems by simp
                next
                  case False
                  hence "Suc i < n" using Suc.prems by simp
                  hence "subdivision (Suc i) < subdivision n" using Suc by simp
                  also have "subdivision n < subdivision (Suc n)" using hsub_mono Suc.prems by simp
                  finally show ?thesis .
                qed
              qed
            qed
          qed
          hence "subdivision (Suc i) \<le> 1" using hsubm by simp
          have "0 \<le> subdivision i + t * (subdivision (Suc i) - subdivision i)"
            using \<open>subdivision i \<ge> 0\<close> hlb by linarith
          moreover have "subdivision i + t * (subdivision (Suc i) - subdivision i) \<le> 1"
            using \<open>subdivision (Suc i) \<le> 1\<close> hub by linarith
          ultimately show ?thesis unfolding top1_unit_interval_def by simp
        qed
        ultimately show "y \<in> f ` {s\<in>I_set. subdivision i \<le> s \<and> s \<le> subdivision (Suc i)}"
          using ht(2) unfolding fi_def by (by100 blast)
      next
        fix y assume "y \<in> f ` {s\<in>I_set. subdivision i \<le> s \<and> s \<le> subdivision (Suc i)}"
        then obtain s where hs: "s \<in> I_set" "subdivision i \<le> s" "s \<le> subdivision (Suc i)" "y = f s"
          by (by100 blast)
        define t where "t = (s - subdivision i) / (subdivision (Suc i) - subdivision i)"
        have hDelta: "subdivision (Suc i) - subdivision i > 0" using hsub_mono[rule_format, OF hi] by simp
        have "t \<ge> 0" unfolding t_def using hs(2) hDelta by simp
        moreover have "t \<le> 1" unfolding t_def using hs(3) hDelta by (simp add: divide_le_eq_1)
        ultimately have "t \<in> I_set" unfolding top1_unit_interval_def by simp
        moreover have "fi i t = f s"
        proof -
          have "subdivision i + (s - subdivision i) / (subdivision (Suc i) - subdivision i)
              * (subdivision (Suc i) - subdivision i) = s"
            using hDelta by simp
          thus ?thesis unfolding fi_def t_def by simp
        qed
        ultimately have "fi i t \<in> fi i ` I_set" by (by100 blast)
        thus "y \<in> fi i ` I_set" using hs(4) \<open>fi i t = f s\<close> by simp
      qed
      moreover have "f ` {s\<in>I_set. subdivision i \<le> s \<and> s \<le> subdivision (Suc i)} \<subseteq> U
          \<or> f ` {s\<in>I_set. subdivision i \<le> s \<and> s \<le> subdivision (Suc i)} \<subseteq> V"
        using hsub_UV[rule_format, OF hi] by simp
      ultimately show "fi i ` I_set \<subseteq> U \<or> fi i ` I_set \<subseteq> V" by simp
    qed
    have hgs_loops: "\<forall>i<m. top1_is_loop_on X TX x0 (gs_list!i)
        \<and> (gs_list!i ` I_set \<subseteq> U \<or> gs_list!i ` I_set \<subseteq> V)"
    proof (intro allI impI conjI)
      fix i assume hi: "i < m"
      have hTX: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
      have hUV_sub: "U \<inter> V \<subseteq> X" using assms(2,3) unfolding openin_on_def by (by100 blast)
      have h\<alpha>i: "top1_is_path_on X TX x0 (f (subdivision i)) (\<alpha>s' i)"
        by (rule path_in_subspace_is_path_in_ambient'[OF hTX hUV_sub h\<alpha>s'[rule_format]])
           (use hi in simp)
      have h\<alpha>si: "top1_is_path_on X TX x0 (f (subdivision (Suc i))) (\<alpha>s' (Suc i))"
        by (rule path_in_subspace_is_path_in_ambient'[OF hTX hUV_sub h\<alpha>s'[rule_format]])
           (use hi in simp)
      have hrev: "top1_is_path_on X TX (f (subdivision (Suc i))) x0 (top1_path_reverse (\<alpha>s' (Suc i)))"
        by (rule top1_path_reverse_is_path[OF h\<alpha>si])
      have hprod1: "top1_is_path_on X TX x0 (f (subdivision (Suc i)))
          (top1_path_product (\<alpha>s' i) (fi i))"
        by (rule top1_path_product_is_path[OF hTX h\<alpha>i hfi_path[OF hi]])
      have hgi_path: "top1_is_path_on X TX x0 x0 (gi i)"
        unfolding gi_def by (rule top1_path_product_is_path[OF hTX hprod1 hrev])
      have "gs_list ! i = gi i" unfolding gs_list_def using hi by simp
      show "top1_is_loop_on X TX x0 (gs_list ! i)"
        unfolding \<open>gs_list ! i = gi i\<close> top1_is_loop_on_def using hgi_path by simp
      \<comment> \<open>Image: \<alpha>s' \<subseteq> U\<inter>V, fi \<subseteq> U or V, rev \<subseteq> U\<inter>V.\<close>
      show "gs_list ! i ` I_set \<subseteq> U \<or> gs_list ! i ` I_set \<subseteq> V"
      proof -
        \<comment> \<open>Path product image \<subseteq> union of component images.\<close>
        have hprod_img: "\<And>f g :: real \<Rightarrow> 'a. top1_path_product f g ` I_set \<subseteq> f ` I_set \<union> g ` I_set"
        proof -
          fix f g :: "real \<Rightarrow> 'a"
          show "top1_path_product f g ` I_set \<subseteq> f ` I_set \<union> g ` I_set"
          proof
            fix y assume "y \<in> top1_path_product f g ` I_set"
            then obtain t where ht: "t \<in> I_set" "y = top1_path_product f g t" by (by100 blast)
            show "y \<in> f ` I_set \<union> g ` I_set"
            proof (cases "t \<le> 1/2")
              case True
              hence "y = f (2 * t)" using ht(2) unfolding top1_path_product_def by simp
              moreover have "2 * t \<in> I_set" using ht(1) True unfolding top1_unit_interval_def by auto
              ultimately show ?thesis by (by100 blast)
            next
              case False
              hence "y = g (2 * t - 1)" using ht(2) unfolding top1_path_product_def by simp
              moreover have "2 * t - 1 \<in> I_set" using ht(1) False unfolding top1_unit_interval_def by auto
              ultimately show ?thesis by (by100 blast)
            qed
          qed
        qed
        have hrev_img: "\<And>f :: real \<Rightarrow> 'a. top1_path_reverse f ` I_set \<subseteq> f ` I_set"
        proof -
          fix f :: "real \<Rightarrow> 'a"
          show "top1_path_reverse f ` I_set \<subseteq> f ` I_set"
          proof
            fix y assume "y \<in> top1_path_reverse f ` I_set"
            then obtain t where "t \<in> I_set" "y = f (1 - t)"
              unfolding top1_path_reverse_def by (by100 blast)
            moreover have "1 - t \<in> I_set" using \<open>t \<in> I_set\<close> unfolding top1_unit_interval_def by auto
            ultimately show "y \<in> f ` I_set" by (by100 blast)
          qed
        qed
        \<comment> \<open>gi image \<subseteq> \<alpha>s'(i) \<union> fi(i) \<union> rev(\<alpha>s'(Suc i)) images.\<close>
        have "gi i ` I_set \<subseteq> (top1_path_product (\<alpha>s' i) (fi i)) ` I_set
            \<union> (top1_path_reverse (\<alpha>s' (Suc i))) ` I_set"
          unfolding gi_def using hprod_img by (by100 blast)
        also have "\<dots> \<subseteq> \<alpha>s' i ` I_set \<union> fi i ` I_set \<union> \<alpha>s' (Suc i) ` I_set"
          using hprod_img hrev_img by (by100 blast)
        finally have hgi_img: "gi i ` I_set \<subseteq> \<alpha>s' i ` I_set \<union> fi i ` I_set \<union> \<alpha>s' (Suc i) ` I_set" .
        \<comment> \<open>\<alpha>s' images \<subseteq> U\<inter>V.\<close>
        have h\<alpha>i_maps: "\<forall>t\<in>I_set. \<alpha>s' i t \<in> U \<inter> V"
          using h\<alpha>s'[rule_format, of i] hi
          unfolding top1_is_path_on_def top1_continuous_map_on_def by simp
        have h\<alpha>i_img: "\<alpha>s' i ` I_set \<subseteq> U \<inter> V" using h\<alpha>i_maps by (by100 blast)
        have h\<alpha>si_maps: "\<forall>t\<in>I_set. \<alpha>s' (Suc i) t \<in> U \<inter> V"
          using h\<alpha>s'[rule_format, of "Suc i"] hi
          unfolding top1_is_path_on_def top1_continuous_map_on_def by simp
        have h\<alpha>si_img: "\<alpha>s' (Suc i) ` I_set \<subseteq> U \<inter> V" using h\<alpha>si_maps by (by100 blast)
        have "gi i ` I_set \<subseteq> U \<or> gi i ` I_set \<subseteq> V"
        proof (rule disjE[OF hfi_UV[OF hi]])
          assume hfiU: "fi i ` I_set \<subseteq> U"
          have hunionU: "\<alpha>s' i ` I_set \<union> fi i ` I_set \<union> \<alpha>s' (Suc i) ` I_set \<subseteq> U"
            using h\<alpha>i_img h\<alpha>si_img hfiU by (by100 blast)
          hence "gi i ` I_set \<subseteq> U" by (rule subset_trans[OF hgi_img])
          thus ?thesis by (by100 blast)
        next
          assume "fi i ` I_set \<subseteq> V"
          have h\<alpha>iV: "\<alpha>s' i ` I_set \<subseteq> V" using h\<alpha>i_img by (by100 blast)
          have h\<alpha>siV: "\<alpha>s' (Suc i) ` I_set \<subseteq> V" using h\<alpha>si_img by (by100 blast)
          have hunionV: "\<alpha>s' i ` I_set \<union> fi i ` I_set \<union> \<alpha>s' (Suc i) ` I_set \<subseteq> V"
            using h\<alpha>iV \<open>fi i ` I_set \<subseteq> V\<close> h\<alpha>siV by (by100 blast)
          hence "gi i ` I_set \<subseteq> V" by (rule subset_trans[OF hgi_img])
          thus ?thesis by (by100 blast)
        qed
        thus ?thesis unfolding \<open>gs_list ! i = gi i\<close> by simp
      qed
    qed
    \<comment> \<open>Step 2f: f \<simeq> foldr (*) gs_list const.\<close>
    \<comment> \<open>Step 2f-1: f \<simeq> f1*f2*...*fm (Theorem 51.3: reparametrization preserves homotopy class).\<close>
    define fi_list where "fi_list = map fi [0..<m]"
    have hf_fi: "top1_path_homotopic_on X TX x0 x0 f
        (foldr top1_path_product fi_list (top1_constant_path x0))"
      sorry \<comment> \<open>Theorem 51.3: f restricted to [sub(i),sub(i+1)] and reparametrized gives fi(i).
         f = f1*f2*...*fm up to reparametrization (piecewise linear). Standard path algebra.\<close>
    \<comment> \<open>Step 2f-2: f1*...*fm \<simeq> g1*...*gm (telescoping via \<alpha>i * rev(\<alpha>i) \<simeq> const).\<close>
    have hfi_gi: "top1_path_homotopic_on X TX x0 x0
        (foldr top1_path_product fi_list (top1_constant_path x0))
        (foldr top1_path_product gs_list (top1_constant_path x0))"
    proof -
      have hTX': "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
      have hx0_X: "x0 \<in> X" using hx0 assms(2) unfolding openin_on_def by (by100 blast)
      have hUV_sub: "U \<inter> V \<subseteq> X" using assms(2,3) unfolding openin_on_def by (by100 blast)
      \<comment> \<open>Lift \<alpha>s' paths to X.\<close>
      have h\<alpha>'_X: "\<And>i. i \<le> m \<Longrightarrow> top1_is_path_on X TX x0 (f (subdivision i)) (\<alpha>s' i)"
        by (rule path_in_subspace_is_path_in_ambient'[OF hTX' hUV_sub h\<alpha>s'[rule_format]]) simp
      \<comment> \<open>Textbook "direct computation": by induction on m.
         Base m=1: g0*const = ((const*f0)*rev(const))*const \<simeq> f0*const.
         Step: use gi = (\<alpha>i*fi)*rev(\<alpha>(i+1)) and cancel rev(\<alpha>k)*\<alpha>k \<simeq> const.\<close>
      \<comment> \<open>The telescoping computation, following the textbook literally.
         For each i: gi = (\<alpha>i*fi)*rev(\<alpha>(i+1)).
         The product g0*g1*...*g(m-1)*const telescopes because
         rev(\<alpha>(k))*\<alpha>(k) cancels at each junction.
         With \<alpha>0 = \<alpha>m = const, the outermost factors also simplify.\<close>
      \<comment> \<open>Key facts for the algebra:\<close>
      have hrev_const: "top1_path_reverse (top1_constant_path x0) = top1_constant_path x0"
        unfolding top1_path_reverse_def top1_constant_path_def by (rule ext) simp
      have hfi_path_X: "\<And>i. i < m \<Longrightarrow> top1_is_path_on X TX (f (subdivision i)) (f (subdivision (Suc i))) (fi i)"
        by (rule hfi_path)
      have hconst_path: "top1_is_path_on X TX x0 x0 (top1_constant_path x0)"
        by (rule top1_constant_path_is_path[OF hTX' hx0_X])
      have hf0: "f 0 = x0" using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      have hf1: "f 1 = x0" using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      have hfsub0: "f (subdivision 0) = x0" using hsub0 hf0 by simp
      have hfsubm: "f (subdivision m) = x0" using hsubm hf1 by simp
      have hgi_eq: "\<And>i. i < m \<Longrightarrow> gs_list ! i = top1_path_product
          (top1_path_product (\<alpha>s' i) (fi_list ! i)) (top1_path_reverse (\<alpha>s' (Suc i)))"
        unfolding gs_list_def fi_list_def gi_def using hm by simp
      have hfi_len: "length fi_list = m" unfolding fi_list_def by simp
      have hfi_list_path: "\<And>i. i < m \<Longrightarrow> top1_is_path_on X TX
          (f (subdivision i)) (f (subdivision (Suc i))) (fi_list ! i)"
        unfolding fi_list_def using hfi_path_X by simp
      show ?thesis
        by (rule telescoping_conjugated_product[where a="\<lambda>i. f (subdivision i)",
            OF hTX' hx0_X hm hfi_len hgs_len h\<alpha>'_X hfi_list_path hgi_eq
            h\<alpha>s'_0 h\<alpha>s'_m hfsub0 hfsubm])
    qed
    have hgs_product: "top1_path_homotopic_on X TX x0 x0 f
        (foldr top1_path_product gs_list (top1_constant_path x0))"
    proof -
      have hTX': "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
      show ?thesis using Lemma_51_1_path_homotopic_trans[OF hTX' hf_fi hfi_gi] .
    qed
    show ?thesis by (rule that[OF hgs_len hgs_loops hgs_product])
  qed
  show "\<exists>n\<ge>1. \<exists>gs. length gs = n \<and>
       (\<forall>i<n. top1_is_loop_on X TX x0 (gs ! i) \<and>
              (gs ! i ` I_set \<subseteq> U \<or> gs ! i ` I_set \<subseteq> V)) \<and>
       top1_path_homotopic_on X TX x0 x0 f
        (foldr top1_path_product gs (top1_constant_path x0))"
    using hm hgs_len hgs_loops hgs_product by (by100 auto)
qed


end





















