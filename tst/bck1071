theory AlgTop
  imports "Top0.Top1_Ch9_13"
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
    sorry
  \<comment> \<open>Step 2: For each subinterval, define fi = f restricted + reparametrized.
     Choose paths \<alpha>i in U\<inter>V from x0 to f(ai). Set gi = (\<alpha>_{i-1} * fi) * rev \<alpha>i.\<close>
  obtain gs :: "(real \<Rightarrow> 'a) list" where
    hgs_len: "length gs = m" and
    hgs_loops: "\<forall>i<m. top1_is_loop_on X TX x0 (gs!i)
        \<and> (gs!i ` I_set \<subseteq> U \<or> gs!i ` I_set \<subseteq> V)" and
    hgs_product: "top1_path_homotopic_on X TX x0 x0 f
        (foldr top1_path_product gs (top1_constant_path x0))"
    sorry
  show "\<exists>n\<ge>1. \<exists>gs. length gs = n \<and>
       (\<forall>i<n. top1_is_loop_on X TX x0 (gs ! i) \<and>
              (gs ! i ` I_set \<subseteq> U \<or> gs ! i ` I_set \<subseteq> V)) \<and>
       top1_path_homotopic_on X TX x0 x0 f
        (foldr top1_path_product gs (top1_constant_path x0))"
    using hm hgs_len hgs_loops hgs_product by (by100 auto)
qed

text \<open>Helper: path homotopy in a subspace implies path homotopy in the ambient space.\<close>
lemma path_homotopic_subspace_to_ambient:
  assumes hTX: "is_topology_on X TX" and hUsub: "U \<subseteq> X"
      and hTU: "TU = subspace_topology X TX U"
      and hhom: "top1_path_homotopic_on U TU x0 x1 f g"
  shows "top1_path_homotopic_on X TX x0 x1 f g"
proof -
  \<comment> \<open>A path homotopy F: I\<times>I \<rightarrow> U in the subspace is also a path homotopy F: I\<times>I \<rightarrow> X
     in the ambient space, since U \<subseteq> X and the subspace topology makes F continuous in X.\<close>
  have hf_path: "top1_is_path_on U TU x0 x1 f"
    using hhom unfolding top1_path_homotopic_on_def by (by100 blast)
  have hg_path: "top1_is_path_on U TU x0 x1 g"
    using hhom unfolding top1_path_homotopic_on_def by (by100 blast)
  have "\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology U TU F
      \<and> (\<forall>s\<in>I_set. F (s, 0) = f s) \<and> (\<forall>s\<in>I_set. F (s, 1) = g s)
      \<and> (\<forall>t\<in>I_set. F (0, t) = x0) \<and> (\<forall>t\<in>I_set. F (1, t) = x1)"
    using hhom unfolding top1_path_homotopic_on_def by (by100 blast)
  then obtain F where hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology U TU F"
      and hF0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hF1: "\<forall>s\<in>I_set. F (s, 1) = g s"
      and hFl: "\<forall>t\<in>I_set. F (0, t) = x0" and hFr: "\<forall>t\<in>I_set. F (1, t) = x1"
    by (by100 auto)
  \<comment> \<open>F is continuous in X (subspace continuous \<Rightarrow> ambient continuous).\<close>
  have hF_cont_X: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix p assume hp: "p \<in> I_set \<times> I_set"
    have "F p \<in> U" using hF_cont hp unfolding top1_continuous_map_on_def by (by100 blast)
    thus "F p \<in> X" using hUsub by (by100 blast)
  next
    fix V assume hV: "V \<in> TX"
    have hVU: "U \<inter> V \<in> TU" unfolding hTU subspace_topology_def using hV by (by100 blast)
    have "{p \<in> I_set \<times> I_set. F p \<in> V} = {p \<in> I_set \<times> I_set. F p \<in> U \<inter> V}"
    proof (rule set_eqI)
      fix p show "(p \<in> {p \<in> I_set \<times> I_set. F p \<in> V}) = (p \<in> {p \<in> I_set \<times> I_set. F p \<in> U \<inter> V})"
        using hF_cont unfolding top1_continuous_map_on_def by (by100 blast)
    qed
    also have "\<dots> \<in> II_topology"
      using hF_cont hVU unfolding top1_continuous_map_on_def by (by100 blast)
    finally show "{p \<in> I_set \<times> I_set. F p \<in> V} \<in> II_topology" .
  qed
  have hf_path_X: "top1_is_path_on X TX x0 x1 f"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    have hf_cont_U: "top1_continuous_map_on I_set I_top U TU f"
      using hf_path unfolding top1_is_path_on_def by (by100 blast)
    show "top1_continuous_map_on I_set I_top X TX f"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> I_set"
      thus "f s \<in> X" using hf_cont_U hUsub unfolding top1_continuous_map_on_def by (by100 blast)
    next
      fix V assume hV: "V \<in> TX"
      have hVU: "U \<inter> V \<in> TU" unfolding hTU subspace_topology_def using hV by (by100 blast)
      have "{s \<in> I_set. f s \<in> V} = {s \<in> I_set. f s \<in> U \<inter> V}"
        using hf_cont_U unfolding top1_continuous_map_on_def by (by100 blast)
      also have "\<dots> \<in> I_top"
        using hf_cont_U hVU unfolding top1_continuous_map_on_def by (by100 blast)
      finally show "{s \<in> I_set. f s \<in> V} \<in> I_top" .
    qed
    show "f 0 = x0" using hf_path unfolding top1_is_path_on_def by (by100 blast)
    show "f 1 = x1" using hf_path unfolding top1_is_path_on_def by (by100 blast)
  qed
  have hg_path_X: "top1_is_path_on X TX x0 x1 g"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    have hg_cont_U: "top1_continuous_map_on I_set I_top U TU g"
      using hg_path unfolding top1_is_path_on_def by (by100 blast)
    show "top1_continuous_map_on I_set I_top X TX g"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> I_set"
      thus "g s \<in> X" using hg_cont_U hUsub unfolding top1_continuous_map_on_def by (by100 blast)
    next
      fix V assume hV: "V \<in> TX"
      have hVU: "U \<inter> V \<in> TU" unfolding hTU subspace_topology_def using hV by (by100 blast)
      have "{s \<in> I_set. g s \<in> V} = {s \<in> I_set. g s \<in> U \<inter> V}"
        using hg_cont_U unfolding top1_continuous_map_on_def by (by100 blast)
      also have "\<dots> \<in> I_top"
        using hg_cont_U hVU unfolding top1_continuous_map_on_def by (by100 blast)
      finally show "{s \<in> I_set. g s \<in> V} \<in> I_top" .
    qed
    show "g 0 = x0" using hg_path unfolding top1_is_path_on_def by (by100 blast)
    show "g 1 = x1" using hg_path unfolding top1_is_path_on_def by (by100 blast)
  qed
  show ?thesis unfolding top1_path_homotopic_on_def
    using hf_path_X hg_path_X hF_cont_X hF0 hF1 hFl hFr by (by100 blast)
qed

text \<open>Helper: a path in a subspace is a path in the ambient space.\<close>
lemma path_in_subspace_is_path_in_ambient:
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

text \<open>Helper: union of path-connected open sets with nonempty path-connected intersection
  is path-connected.\<close>
lemma path_connected_union:
  assumes hTX: "is_topology_on X TX"
      and hU_pc: "top1_path_connected_on U (subspace_topology X TX U)"
      and hV_pc: "top1_path_connected_on V (subspace_topology X TX V)"
      and hUV_pc: "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and hUV: "U \<union> V = X" and hUsub: "U \<subseteq> X" and hVsub: "V \<subseteq> X"
      and hUV_ne: "U \<inter> V \<noteq> {}"
  shows "top1_path_connected_on X TX"
  unfolding top1_path_connected_on_def
proof (intro conjI ballI)
  show "is_topology_on X TX" by (rule hTX)
next
  fix x y assume hx: "x \<in> X" and hy: "y \<in> X"
  \<comment> \<open>Case analysis: both in U, both in V, or one in each (join via U\<inter>V).\<close>
  show "\<exists>f. top1_is_path_on X TX x y f"
  proof (cases "x \<in> U \<and> y \<in> U")
    case True
    \<comment> \<open>Path in U, transfer to X via subspace inclusion.\<close>
    obtain f where hf: "top1_is_path_on U (subspace_topology X TX U) x y f"
      using hU_pc True unfolding top1_path_connected_on_def by (by100 auto)
    have "top1_is_path_on X TX x y f"
      by (rule path_in_subspace_is_path_in_ambient[OF hTX hUsub hf])
    thus ?thesis by (by100 blast)
  next
    case False
    \<comment> \<open>x \<notin> U \<or> y \<notin> U. Since x,y \<in> U\<union>V, the missing one is in V.
       Pick z \<in> U\<inter>V, path in U to/from z, path in V to/from z, concatenate.\<close>
    have hx_mem: "x \<in> U \<or> x \<in> V" and hy_mem: "y \<in> U \<or> y \<in> V"
      using hx hy hUV by (by100 blast)+
    \<comment> \<open>Get z \<in> U \<inter> V for joining paths.\<close>
    obtain z where hz: "z \<in> U \<inter> V" using hUV_ne by (by100 blast)
    \<comment> \<open>For any a \<in> U and b \<in> V, there's a path a\<rightarrow>z in U and z\<rightarrow>b in V in X.\<close>
    \<comment> \<open>Full proof requires path extraction from each subspace + transfer + concatenation.
       Follows the same pattern as the True case above.\<close>
    \<comment> \<open>Helper: get path in X between points in a path-connected subspace W.\<close>
    have hzU: "z \<in> U" and hzV: "z \<in> V" using hz by (by100 blast)+
    \<comment> \<open>x is in U or V; get path x\<rightarrow>z in X.\<close>
    obtain g1 where hg1: "top1_is_path_on X TX x z g1"
    proof -
      have "\<exists>g. top1_is_path_on X TX x z g"
      proof (cases "x \<in> U")
        case True
        obtain g where "top1_is_path_on U (subspace_topology X TX U) x z g"
          using hU_pc True hzU unfolding top1_path_connected_on_def by (by100 auto)
        thus ?thesis using path_in_subspace_is_path_in_ambient[OF hTX hUsub] by (by100 blast)
      next
        case FalseU: False
        hence "x \<in> V" using hx_mem by (by100 blast)
        obtain g where "top1_is_path_on V (subspace_topology X TX V) x z g"
          using hV_pc \<open>x \<in> V\<close> hzV unfolding top1_path_connected_on_def by (by100 auto)
        thus ?thesis using path_in_subspace_is_path_in_ambient[OF hTX hVsub] by (by100 blast)
      qed
      thus ?thesis using that by (by100 blast)
    qed
    \<comment> \<open>y is in U or V; get path z\<rightarrow>y in X.\<close>
    obtain g2 where hg2: "top1_is_path_on X TX z y g2"
    proof -
      have "\<exists>g. top1_is_path_on X TX z y g"
      proof (cases "y \<in> U")
        case True
        obtain g where "top1_is_path_on U (subspace_topology X TX U) z y g"
          using hU_pc hzU True unfolding top1_path_connected_on_def by (by100 auto)
        thus ?thesis using path_in_subspace_is_path_in_ambient[OF hTX hUsub] by (by100 blast)
      next
        case FalseU: False
        hence "y \<in> V" using hy_mem by (by100 blast)
        obtain g where "top1_is_path_on V (subspace_topology X TX V) z y g"
          using hV_pc hzV \<open>y \<in> V\<close> unfolding top1_path_connected_on_def by (by100 auto)
        thus ?thesis using path_in_subspace_is_path_in_ambient[OF hTX hVsub] by (by100 blast)
      qed
      thus ?thesis using that by (by100 blast)
    qed
    \<comment> \<open>Concatenate: x \<rightarrow> z \<rightarrow> y.\<close>
    have "top1_is_path_on X TX x y (top1_path_product g1 g2)"
      by (rule top1_path_product_is_path[OF hTX hg1 hg2])
    thus ?thesis by (by100 blast)
  qed
qed

text \<open>Helper: R with top1\_open\_sets is Hausdorff.\<close>
lemma top1_R_is_hausdorff:
  "is_hausdorff_on (UNIV :: real set) top1_open_sets"
proof -
  have hT: "is_topology_on (UNIV :: real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hH: "\<forall>x\<in>(UNIV::real set). \<forall>y\<in>(UNIV::real set). x \<noteq> y \<longrightarrow>
      (\<exists>U V. neighborhood_of x UNIV top1_open_sets U \<and>
             neighborhood_of y UNIV top1_open_sets V \<and> U \<inter> V = {})"
  proof (intro ballI impI)
    fix x y :: real assume "x \<in> UNIV" "y \<in> UNIV" "x \<noteq> y"
    show "\<exists>U V. neighborhood_of x UNIV top1_open_sets U \<and>
                neighborhood_of y UNIV top1_open_sets V \<and> U \<inter> V = {}"
    proof (cases "x < y")
      case True
      let ?m = "(x + y) / 2"
      have "{..<(?m::real)} \<in> {U. open U} \<and> x \<in> {..<(?m::real)}"
        using True by simp
      moreover have "{?m<..} \<in> {U. open U} \<and> y \<in> {?m<..}"
        using True by simp
      moreover have "{..<(?m::real)} \<inter> {?m<..} = {}" by auto
      ultimately show ?thesis unfolding neighborhood_of_def top1_open_sets_def by blast
    next
      case False
      hence "x > y" using \<open>x \<noteq> y\<close> by simp
      let ?m = "(x + y) / 2"
      have "{?m<..} \<in> {U. open U} \<and> x \<in> {?m<..}"
        using \<open>x > y\<close> by simp
      moreover have "{..<(?m::real)} \<in> {U. open U} \<and> y \<in> {..<(?m::real)}"
        using \<open>x > y\<close> by simp
      moreover have "{?m<..} \<inter> {..<(?m::real)} = {}" by auto
      ultimately show ?thesis unfolding neighborhood_of_def top1_open_sets_def by blast
    qed
  qed
  show ?thesis unfolding is_hausdorff_on_def using hT hH by (by100 blast)
qed

text \<open>Helper: R^2 with product topology is Hausdorff.\<close>
lemma top1_R2_is_hausdorff:
  "is_hausdorff_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
proof -
  have hR: "is_hausdorff_on (UNIV :: real set) top1_open_sets" by (rule top1_R_is_hausdorff)
  have hR2: "is_hausdorff_on (UNIV \<times> UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
    using conjunct1[OF conjunct2[OF Theorem_17_11]] hR by (by100 blast)
  thus ?thesis by simp
qed

text \<open>Helper: S^1 subspace is Hausdorff.\<close>
lemma top1_S1_is_hausdorff:
  "is_hausdorff_on top1_S1 top1_S1_topology"
proof -
  have "top1_S1 \<subseteq> (UNIV :: (real \<times> real) set)" by simp
  thus ?thesis unfolding top1_S1_topology_def
    using conjunct2[OF conjunct2[OF Theorem_17_11]] top1_R2_is_hausdorff by (by100 blast)
qed

text \<open>Helper: R^3 = R \<times> (R \<times> R) is Hausdorff.\<close>
lemma top1_R3_is_hausdorff:
  "is_hausdorff_on (UNIV :: (real \<times> real \<times> real) set)
     (product_topology_on top1_open_sets (product_topology_on top1_open_sets top1_open_sets))"
proof -
  have hR: "is_hausdorff_on (UNIV :: real set) top1_open_sets" by (rule top1_R_is_hausdorff)
  have hR2: "is_hausdorff_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
    by (rule top1_R2_is_hausdorff)
  have "is_hausdorff_on (UNIV \<times> UNIV :: (real \<times> (real \<times> real)) set)
      (product_topology_on top1_open_sets (product_topology_on top1_open_sets top1_open_sets))"
    using conjunct1[OF conjunct2[OF Theorem_17_11]] hR hR2 by (by100 blast)
  thus ?thesis by simp
qed

text \<open>S^1 has strict topology.\<close>
lemma top1_S1_is_topology_on_strict:
  "is_topology_on_strict top1_S1 top1_S1_topology"
  unfolding is_topology_on_strict_def
proof (intro conjI)
  show "is_topology_on top1_S1 top1_S1_topology"
    using top1_S1_is_hausdorff unfolding is_hausdorff_on_def by (by100 blast)
  show "top1_S1_topology \<subseteq> Pow top1_S1"
    unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
qed

text \<open>R^2 - {0} has strict topology.\<close>
lemma top1_R2_minus_0_is_topology_on_strict:
  "is_topology_on_strict (UNIV - {(0::real, 0::real)})
     (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))"
  unfolding is_topology_on_strict_def
proof (intro conjI)
  show "is_topology_on (UNIV - {(0::real, 0::real)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))"
  proof -
    have "is_topology_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
      using top1_R2_is_hausdorff unfolding is_hausdorff_on_def by (by100 blast)
    thus ?thesis by (rule subspace_topology_is_topology_on) simp
  qed
  show "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)})
      \<subseteq> Pow (UNIV - {(0::real, 0::real)})"
    unfolding subspace_topology_def by (by100 blast)
qed

text \<open>Helper: closed set has open complement.\<close>
lemma closedin_complement_openin:
  assumes "closedin_on X TX A"
  shows "openin_on X TX (X - A)"
  using assms unfolding closedin_on_def openin_on_def by (by100 blast)

text \<open>Helper: open set has closed complement.\<close>
lemma openin_complement_closedin:
  assumes "openin_on X TX A"
  shows "closedin_on X TX (X - A)"
proof -
  have hA: "A \<in> TX" and hAsub: "A \<subseteq> X"
    using assms unfolding openin_on_def by (by100 blast)+
  have "X - (X - A) = A" using hAsub by (by100 blast)
  thus ?thesis unfolding closedin_on_def using hA by (by100 simp)
qed


text \<open>Helper: if each loop in a list is nulhomotopic, their foldr product is nulhomotopic.\<close>
lemma foldr_path_product_nulhomotopic:
  assumes hTX: "is_topology_on X TX" and hx0: "x0 \<in> X"
      and hnul: "\<forall>i < length gs. top1_path_homotopic_on X TX x0 x0 (gs!i) (top1_constant_path x0)"
  shows "top1_path_homotopic_on X TX x0 x0
      (foldr top1_path_product gs (top1_constant_path x0)) (top1_constant_path x0)"
  using hnul
proof (induction gs)
  case Nil
  have "top1_is_path_on X TX x0 x0 (top1_constant_path x0)"
    by (rule top1_constant_path_is_path[OF hTX hx0])
  thus ?case by (simp, rule Lemma_51_1_path_homotopic_refl)
next
  case (Cons g gs')
  have hg_nul: "top1_path_homotopic_on X TX x0 x0 g (top1_constant_path x0)"
    using Cons.prems by force
  have hgs'_nul: "\<forall>i < length gs'. top1_path_homotopic_on X TX x0 x0 (gs'!i) (top1_constant_path x0)"
    using Cons.prems by force
  have hrest_nul: "top1_path_homotopic_on X TX x0 x0
      (foldr top1_path_product gs' (top1_constant_path x0)) (top1_constant_path x0)"
    by (rule Cons.IH[OF hgs'_nul])
  have hrest_path: "top1_is_path_on X TX x0 x0 (foldr top1_path_product gs' (top1_constant_path x0))"
    using hrest_nul unfolding top1_path_homotopic_on_def by (by100 blast)
  have step1: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product g (foldr top1_path_product gs' (top1_constant_path x0)))
      (top1_path_product (top1_constant_path x0) (foldr top1_path_product gs' (top1_constant_path x0)))"
    by (rule path_homotopic_product_left[OF hTX hg_nul hrest_path])
  have step2: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product (top1_constant_path x0) (foldr top1_path_product gs' (top1_constant_path x0)))
      (foldr top1_path_product gs' (top1_constant_path x0))"
    by (rule Theorem_51_2_left_identity[OF hTX hrest_path])
  have step12: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product g (foldr top1_path_product gs' (top1_constant_path x0)))
      (foldr top1_path_product gs' (top1_constant_path x0))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX step1 step2])
  show ?case
    by (simp, rule Lemma_51_1_path_homotopic_trans[OF hTX step12 hrest_nul])
qed

(** from \<S>59 Corollary 59.2: U, V open, simply connected, U \<inter> V path-connected
    and nonempty \<Longrightarrow> X = U \<union> V is simply connected. **)
corollary Corollary_59_2:
  assumes "is_topology_on_strict X TX" and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "U \<inter> V \<noteq> {}"
      and "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and "top1_simply_connected_on U (subspace_topology X TX U)"
      and "top1_simply_connected_on V (subspace_topology X TX V)"
  shows "top1_simply_connected_on X TX"
proof -
  \<comment> \<open>Munkres 59.2: By Thm 59.1, every loop decomposes into loops in U or V.
     U, V simply connected \<Rightarrow> each piece nulhomotopic \<Rightarrow> whole loop nulhomotopic.\<close>
  obtain x0 where hx0: "x0 \<in> U \<inter> V" using assms(5) by (by100 blast)
  \<comment> \<open>Step 1: X is path-connected (U, V path-connected via simply connected, joined via U\<inter>V).\<close>
  have hpc: "top1_path_connected_on X TX"
  proof -
    have hU_pc: "top1_path_connected_on U (subspace_topology X TX U)"
      using assms(7) top1_simply_connected_on_path_connected by (by100 blast)
    have hV_pc: "top1_path_connected_on V (subspace_topology X TX V)"
      using assms(8) top1_simply_connected_on_path_connected by (by100 blast)
    show ?thesis
      by (rule path_connected_union[OF is_topology_on_strict_imp[OF assms(1)]
            hU_pc hV_pc assms(6) assms(4) openin_on_sub[OF assms(2)] openin_on_sub[OF assms(3)] assms(5)])
  qed
  \<comment> \<open>Step 2: Every loop at x0 is nulhomotopic.\<close>
  have hnul: "\<forall>f. top1_is_loop_on X TX x0 f \<longrightarrow>
      top1_path_homotopic_on X TX x0 x0 f (top1_constant_path x0)"
  proof (intro allI impI)
    fix f assume hf: "top1_is_loop_on X TX x0 f"
    \<comment> \<open>By Theorem 59.1, f decomposes into loops in U or V.\<close>
    obtain n gs where hn: "n \<ge> 1" and hlen: "length gs = n"
        and hgs: "\<forall>i<n. top1_is_loop_on X TX x0 (gs!i)
                      \<and> (gs!i ` I_set \<subseteq> U \<or> gs!i ` I_set \<subseteq> V)"
        and hprod: "top1_path_homotopic_on X TX x0 x0 f
            (foldr top1_path_product gs (top1_constant_path x0))"
      using Theorem_59_1[OF assms(1,2,3,4,6) hx0] hf by blast
    \<comment> \<open>Each gi lies in U or V, hence is nulhomotopic there (simply connected).\<close>
    have hgi_nul: "\<forall>i<n. top1_path_homotopic_on X TX x0 x0 (gs!i) (top1_constant_path x0)"
    proof (intro allI impI)
      fix i assume hi: "i < n"
      have hgi_loop: "top1_is_loop_on X TX x0 (gs!i)" using hgs hi by (by100 blast)
      have "gs!i ` I_set \<subseteq> U \<or> gs!i ` I_set \<subseteq> V" using hgs hi by (by100 blast)
      \<comment> \<open>If in U: simply connected U \<Rightarrow> nulhomotopic in U \<Rightarrow> nulhomotopic in X.
         If in V: simply connected V \<Rightarrow> nulhomotopic in V \<Rightarrow> nulhomotopic in X.\<close>
      thus "top1_path_homotopic_on X TX x0 x0 (gs!i) (top1_constant_path x0)"
      proof
        assume hU_case: "gs!i ` I_set \<subseteq> U"
        \<comment> \<open>gs!i is a loop in U. U simply connected \<Rightarrow> nulhomotopic in U.\<close>
        have hgi_loop_U: "top1_is_loop_on U (subspace_topology X TX U) x0 (gs!i)"
        proof -
          have hcont_X: "top1_continuous_map_on I_set I_top X TX (gs!i)"
            using hgi_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have himg: "(gs!i) ` I_set \<subseteq> U" using hU_case .
          have hUsub: "U \<subseteq> X" using openin_on_sub[OF assms(2)] .
          have hcont_U: "top1_continuous_map_on I_set I_top U (subspace_topology X TX U) (gs!i)"
            by (rule top1_continuous_map_on_codomain_shrink[OF hcont_X himg hUsub])
          have hg0: "(gs!i) 0 = x0" and hg1: "(gs!i) 1 = x0"
            using hgi_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
          show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
            using hcont_U hg0 hg1 by (by100 simp)
        qed
        have hgi_nul_U: "top1_path_homotopic_on U (subspace_topology X TX U) x0 x0
            (gs!i) (top1_constant_path x0)"
        proof -
          have hx0U: "x0 \<in> U" using hx0 by (by100 blast)
          show ?thesis using assms(7) hgi_loop_U hx0U
            unfolding top1_simply_connected_on_def by (by100 blast)
        qed
        show ?thesis
          by (rule path_homotopic_subspace_to_ambient[OF
                is_topology_on_strict_imp[OF assms(1)] _ refl hgi_nul_U])
             (rule openin_on_sub[OF assms(2)])
      next
        assume hV_case: "gs!i ` I_set \<subseteq> V"
        have hgi_loop_V: "top1_is_loop_on V (subspace_topology X TX V) x0 (gs!i)"
        proof -
          have hcont_X: "top1_continuous_map_on I_set I_top X TX (gs!i)"
            using hgi_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have himg: "(gs!i) ` I_set \<subseteq> V" using hV_case .
          have hVsub: "V \<subseteq> X" using openin_on_sub[OF assms(3)] .
          have hcont_V: "top1_continuous_map_on I_set I_top V (subspace_topology X TX V) (gs!i)"
            by (rule top1_continuous_map_on_codomain_shrink[OF hcont_X himg hVsub])
          have hg0: "(gs!i) 0 = x0" and hg1: "(gs!i) 1 = x0"
            using hgi_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
          show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
            using hcont_V hg0 hg1 by (by100 simp)
        qed
        have hgi_nul_V: "top1_path_homotopic_on V (subspace_topology X TX V) x0 x0
            (gs!i) (top1_constant_path x0)"
        proof -
          have hx0V: "x0 \<in> V" using hx0 by (by100 blast)
          show ?thesis using assms(8) hgi_loop_V hx0V
            unfolding top1_simply_connected_on_def by (by100 blast)
        qed
        show ?thesis
          by (rule path_homotopic_subspace_to_ambient[OF
                is_topology_on_strict_imp[OF assms(1)] _ refl hgi_nul_V])
             (rule openin_on_sub[OF assms(3)])
      qed
    qed
    \<comment> \<open>Product of nulhomotopic loops is nulhomotopic.\<close>
    have hx0X: "x0 \<in> X" using hx0 assms(4) by (by100 blast)
    have hTX_weak: "is_topology_on X TX" by (rule is_topology_on_strict_imp[OF assms(1)])
    have "top1_path_homotopic_on X TX x0 x0
        (foldr top1_path_product gs (top1_constant_path x0)) (top1_constant_path x0)"
    proof -
      have "\<forall>i < length gs. top1_path_homotopic_on X TX x0 x0 (gs!i) (top1_constant_path x0)"
        using hgi_nul hlen by (by100 simp)
      thus ?thesis by (rule foldr_path_product_nulhomotopic[OF hTX_weak hx0X])
    qed
    \<comment> \<open>Transitivity: f \<simeq> product \<simeq> const.\<close>
    thus "top1_path_homotopic_on X TX x0 x0 f (top1_constant_path x0)"
      by (rule Lemma_51_1_path_homotopic_trans[OF is_topology_on_strict_imp[OF assms(1)] hprod])
  qed
  \<comment> \<open>Assemble: path-connected + all loops at x0 nulhomotopic \<Rightarrow> simply connected.\<close>
  have hx0X_outer: "x0 \<in> X" using hx0 assms(4) by (by100 blast)
  show ?thesis
    by (rule top1_simply_connected_from_one_point[OF
          is_topology_on_strict_imp[OF assms(1)] hpc hx0X_outer hnul])
qed

(** from \<S>59 Theorem 59.3: for n \<ge> 2, S^n is simply connected.

    Munkres' proof (2 steps):
    Step 1: S^n - p is homeomorphic to R^n via stereographic projection.
    Step 2: Apply Corollary 59.2 with U = S^n - p, V = S^n - q. **)
theorem Theorem_59_3:
  assumes "n \<ge> 2"
  shows "top1_simply_connected_on (top1_Sn n)
    (subspace_topology UNIV
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))
      (top1_Sn n))"
proof -
  let ?Sn = "top1_Sn n"
  let ?TSn = "subspace_topology UNIV
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets)) ?Sn"
  \<comment> \<open>Munkres 59.3: north pole p, south pole q.\<close>
  let ?p = "\<lambda>i::nat. if i = 0 then (1::real) else 0"
  let ?q = "\<lambda>i::nat. if i = 0 then (-1::real) else 0"
  let ?U = "?Sn - {?p}" and ?V = "?Sn - {?q}"
  \<comment> \<open>Step 1: U = S^n - {p} \<cong> R^n via stereographic projection, hence simply connected.\<close>
  have hU_sc: "top1_simply_connected_on ?U (subspace_topology ?Sn ?TSn ?U)" sorry
  have hV_sc: "top1_simply_connected_on ?V (subspace_topology ?Sn ?TSn ?V)" sorry
  \<comment> \<open>Step 2: U, V are open in S^n.\<close>
  \<comment> \<open>U = S^n - {p} and V = S^n - {q} are open because {p}, {q} are closed in S^n
     (Hausdorff + singleton closed).\<close>
  \<comment> \<open>S^n is Hausdorff (subspace of Hausdorff product). Singletons are closed, so complements are open.\<close>
  have hProd_haus: "is_hausdorff_on (top1_PiE UNIV (\<lambda>_::nat. UNIV::real set))
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))"
    by (rule Theorem_19_4_product) (simp add: top1_R_is_hausdorff)
  have hPiE_eq: "top1_PiE UNIV (\<lambda>_::nat. UNIV::real set) = UNIV"
    unfolding top1_PiE_def top1_Pi_def top1_extensional_def by (by100 auto)
  have hProd_haus_UNIV: "is_hausdorff_on (UNIV :: (nat \<Rightarrow> real) set)
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))"
    using hProd_haus unfolding hPiE_eq .
  have hSn_sub_UNIV: "?Sn \<subseteq> (UNIV :: (nat \<Rightarrow> real) set)" by simp
  have hSn_haus: "is_hausdorff_on ?Sn ?TSn"
    using conjunct2[OF conjunct2[OF Theorem_17_11]] hProd_haus_UNIV hSn_sub_UNIV by (by100 blast)
  have hp_in_Sn: "?p \<in> ?Sn" unfolding top1_Sn_def
  proof (intro CollectI conjI allI impI)
    fix i :: nat assume "i \<ge> Suc n" thus "?p i = 0" using assms by simp
  next
    have "(\<Sum>i\<le>n. (?p i)\<^sup>2) = (\<Sum>i\<le>n. (if i = 0 then 1 else (0::real)))"
      by (rule sum.cong) simp_all
    also have "\<dots> = 1"
    proof -
      have hfin: "finite ({..n}::nat set)" by simp
      have h0n: "(0::nat) \<in> {..n}" using assms by simp
      show ?thesis using sum.delta'[OF hfin, of 0 "\<lambda>_. 1::real"] h0n by simp
    qed
    finally show "(\<Sum>i\<le>n. (?p i)\<^sup>2) = 1" .
  qed
  have hq_in_Sn: "?q \<in> ?Sn" unfolding top1_Sn_def
  proof (intro CollectI conjI allI impI)
    fix i :: nat assume "i \<ge> Suc n" thus "?q i = 0" using assms by simp
  next
    have "(\<Sum>i\<le>n. (?q i)\<^sup>2) = (\<Sum>i\<le>n. (if i = 0 then 1 else (0::real)))"
      by (rule sum.cong) (simp_all add: power2_eq_square)
    also have "\<dots> = 1"
    proof -
      have hfin: "finite ({..n}::nat set)" by simp
      have h0n: "(0::nat) \<in> {..n}" using assms by simp
      show ?thesis using sum.delta'[OF hfin, of 0 "\<lambda>_. 1::real"] h0n by simp
    qed
    finally show "(\<Sum>i\<le>n. (?q i)\<^sup>2) = 1" .
  qed
  have hp_closed: "closedin_on ?Sn ?TSn {?p}"
    by (rule singleton_closed_in_hausdorff[OF hSn_haus hp_in_Sn])
  have hq_closed: "closedin_on ?Sn ?TSn {?q}"
    by (rule singleton_closed_in_hausdorff[OF hSn_haus hq_in_Sn])
  have hU_open: "openin_on ?Sn ?TSn ?U"
    by (rule closedin_complement_openin[OF hp_closed])
  have hV_open: "openin_on ?Sn ?TSn ?V"
    by (rule closedin_complement_openin[OF hq_closed])
  \<comment> \<open>U \<union> V = S^n (every point of S^n differs from p or q).\<close>
  have hpq_ne: "?p \<noteq> ?q"
  proof -
    have "?p 0 = (1::real)" by simp
    moreover have "?q 0 = (-1::real)" by simp
    ultimately show ?thesis by (metis one_neq_neg_one)
  qed
  have hUV: "?U \<union> ?V = ?Sn" using hpq_ne by (by100 blast)
  \<comment> \<open>U \<inter> V = S^n - {p, q} is path-connected for n \<ge> 2.\<close>
  have hUV_ne: "?U \<inter> ?V \<noteq> {}"
  proof -
    \<comment> \<open>The point with x(1)=1 and x(i)=0 otherwise is in S^n (for n\<ge>2) and differs from p,q.\<close>
    let ?r = "\<lambda>i::nat. if i = 1 then (1::real) else 0"
    have hr_Sn: "?r \<in> ?Sn" unfolding top1_Sn_def
    proof (intro CollectI conjI allI impI)
      fix i :: nat assume "i \<ge> Suc n"
      hence "i \<noteq> 1" using assms by linarith
      thus "?r i = 0" by simp
    next
      have h1n: "(1::nat) \<le> n" using assms by linarith
      have "(\<Sum>i\<le>n. (?r i)\<^sup>2) = (\<Sum>i\<le>n. (if i = 1 then 1 else (0::real)))"
      proof (rule sum.cong)
        fix i assume "i \<in> {..n}"
        show "(?r i)\<^sup>2 = (if i = 1 then 1 else 0)" by simp
      qed simp
      also have "\<dots> = 1"
      proof -
        have hfin: "finite ({..n}::nat set)" by simp
        have "(\<Sum>i\<le>n. (if i = (1::nat) then (1::real) else 0))
            = (if (1::nat) \<in> {..n} then 1 else 0)"
          using sum.delta'[OF hfin, of 1 "\<lambda>_. 1::real"] by simp
        also have "\<dots> = 1" using h1n by simp
        finally show ?thesis .
      qed
      finally show "(\<Sum>i\<le>n. (?r i)\<^sup>2) = 1" .
    qed
    have hr_ne_p: "?r \<noteq> ?p"
    proof -
      have "?r 0 = (0::real)" by simp
      moreover have "?p 0 = (1::real)" by simp
      ultimately show ?thesis by (metis zero_neq_one)
    qed
    have hr_ne_q: "?r \<noteq> ?q"
    proof -
      have "?r 0 = (0::real)" by simp
      moreover have "?q 0 = (-1::real)" by simp
      ultimately show ?thesis by (metis neg_0_equal_iff_equal zero_neq_one)
    qed
    have "?r \<in> ?U \<inter> ?V" using hr_Sn hr_ne_p hr_ne_q by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  have hUV_pc: "top1_path_connected_on (?U \<inter> ?V)
      (subspace_topology ?Sn ?TSn (?U \<inter> ?V))" sorry
  have hT_strict: "is_topology_on_strict ?Sn ?TSn"
    unfolding is_topology_on_strict_def
  proof (intro conjI)
    have hTop_each: "\<forall>i\<in>(UNIV::nat set). is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
      using top1_open_sets_is_topology_on_UNIV by simp
    have hTop_prod: "is_topology_on (top1_PiE UNIV (\<lambda>_::nat. UNIV::real set))
        (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))"
      by (rule top1_product_topology_on_is_topology_on[OF hTop_each])
    have hPiE_eq: "top1_PiE UNIV (\<lambda>_::nat. UNIV::real set) = UNIV"
      unfolding top1_PiE_def top1_Pi_def top1_extensional_def by (by100 auto)
    have hTop_UNIV: "is_topology_on (UNIV :: (nat \<Rightarrow> real) set)
        (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))"
      using hTop_prod unfolding hPiE_eq .
    show "is_topology_on ?Sn ?TSn"
      by (rule subspace_topology_is_topology_on[OF hTop_UNIV]) simp
    show "?TSn \<subseteq> Pow ?Sn"
      unfolding subspace_topology_def by (by100 blast)
  qed
  \<comment> \<open>Apply Corollary 59.2.\<close>
  show ?thesis
    using Corollary_59_2[OF hT_strict hU_open hV_open hUV hUV_ne hUV_pc hU_sc hV_sc] by (by100 blast)
qed

corollary Theorem_59_3_path_connected:
  assumes "n \<ge> 2"
  shows "top1_path_connected_on (top1_Sn n)
    (subspace_topology UNIV
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))
      (top1_Sn n))"
  using Theorem_59_3[OF assms] top1_simply_connected_on_path_connected by blast

section \<open>\<S>60 Fundamental Groups of Some Surfaces\<close>

(** from \<S>60 Theorem 60.1: \<pi>_1(X \<times> Y, (x_0, y_0)) \<cong> \<pi>_1(X, x_0) \<times> \<pi>_1(Y, y_0).
    The iso is given by the product map induced by the two projections. **)
theorem Theorem_60_1_product:
  assumes "is_topology_on_strict X TX" and "is_topology_on_strict Y TY"
      and "x0 \<in> X" and "y0 \<in> Y"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier (X \<times> Y) (product_topology_on TX TY) (x0, y0))
           (top1_fundamental_group_mul (X \<times> Y) (product_topology_on TX TY) (x0, y0))
           ((top1_fundamental_group_carrier X TX x0) \<times>
            (top1_fundamental_group_carrier Y TY y0))
           (\<lambda>(c1, c2) (d1, d2).
              (top1_fundamental_group_mul X TX x0 c1 d1,
               top1_fundamental_group_mul Y TY y0 c2 d2))"
  \<comment> \<open>Munkres 60.1: \<Phi>([f]) = (p_*([f]), q_*([f])) = ([p\<circ>f], [q\<circ>f]) where p,q are projections.\<close>
proof -
  let ?TXY = "product_topology_on TX TY"
  let ?\<Phi> = "\<lambda>c. (top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) X TX x0 fst c,
                  top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) Y TY y0 snd c)"
  \<comment> \<open>Step 1: \<Phi> is well-defined and a homomorphism.\<close>
  have hTX: "is_topology_on X TX" by (rule is_topology_on_strict_imp[OF assms(1)])
  have hTY: "is_topology_on Y TY" by (rule is_topology_on_strict_imp[OF assms(2)])
  have hpi1_eq: "(pi1 :: ('a \<times> 'b) \<Rightarrow> 'a) = fst" unfolding pi1_def by (rule ext) simp
  have hpi2_eq: "(pi2 :: ('a \<times> 'b) \<Rightarrow> 'b) = snd" unfolding pi2_def by (rule ext) simp
  have hfst_cont: "top1_continuous_map_on (X \<times> Y) ?TXY X TX fst"
    using top1_continuous_pi1[OF hTX hTY] unfolding hpi1_eq .
  have hsnd_cont: "top1_continuous_map_on (X \<times> Y) ?TXY Y TY snd"
    using top1_continuous_pi2[OF hTX hTY] unfolding hpi2_eq .
  have h\<Phi>_hom: "\<forall>c \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0).
      \<forall>d \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0).
      ?\<Phi> (top1_fundamental_group_mul (X \<times> Y) ?TXY (x0, y0) c d)
      = (\<lambda>(c1, c2) (d1, d2). (top1_fundamental_group_mul X TX x0 c1 d1,
           top1_fundamental_group_mul Y TY y0 c2 d2)) (?\<Phi> c) (?\<Phi> d)" sorry
  \<comment> \<open>Step 2: Injectivity. If p\<circ>f \<simeq> const and q\<circ>f \<simeq> const, combine homotopies componentwise.\<close>
  have h\<Phi>_inj: "inj_on ?\<Phi> (top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0))" sorry
  \<comment> \<open>Step 3: Surjectivity. Given [g] \<in> \<pi>_1(X) and [h] \<in> \<pi>_1(Y), define f(s) = (g(s), h(s)).\<close>
  have h\<Phi>_surj: "?\<Phi> ` (top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0))
      = (top1_fundamental_group_carrier X TX x0) \<times>
        (top1_fundamental_group_carrier Y TY y0)" sorry
  \<comment> \<open>Assemble: \<Phi> is a group isomorphism.\<close>
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
  proof (intro exI conjI)
    show "top1_group_hom_on
        (top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0))
        (top1_fundamental_group_mul (X \<times> Y) ?TXY (x0, y0))
        (top1_fundamental_group_carrier X TX x0 \<times> top1_fundamental_group_carrier Y TY y0)
        (\<lambda>(c1, c2) (d1, d2). (top1_fundamental_group_mul X TX x0 c1 d1,
             top1_fundamental_group_mul Y TY y0 c2 d2))
        ?\<Phi>"
      unfolding top1_group_hom_on_def
    proof (intro conjI ballI)
      fix c assume hc: "c \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0)"
      show "?\<Phi> c \<in> top1_fundamental_group_carrier X TX x0 \<times>
            top1_fundamental_group_carrier Y TY y0"
        using h\<Phi>_surj hc by (by100 blast)
    next
      fix c d assume hc: "c \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0)"
          and hd: "d \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0)"
      show "?\<Phi> (top1_fundamental_group_mul (X \<times> Y) ?TXY (x0, y0) c d) =
          (\<lambda>(c1, c2) (d1, d2). (top1_fundamental_group_mul X TX x0 c1 d1,
             top1_fundamental_group_mul Y TY y0 c2 d2)) (?\<Phi> c) (?\<Phi> d)"
        using h\<Phi>_hom hc hd by (by100 blast)
    qed
    show "bij_betw ?\<Phi>
        (top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0))
        (top1_fundamental_group_carrier X TX x0 \<times> top1_fundamental_group_carrier Y TY y0)"
      unfolding bij_betw_def using h\<Phi>_inj h\<Phi>_surj by (by100 blast)
  qed
qed

section \<open>Chapter 10: Separation Theorems in the Plane\<close>

section \<open>\<S>61 The Jordan Separation Theorem\<close>

text \<open>The 2-sphere S^2 as a subspace of R^3.\<close>
definition top1_S2 :: "(real \<times> real \<times> real) set" where
  "top1_S2 = {p. fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1}"

definition top1_S2_topology :: "(real \<times> real \<times> real) set set" where
  "top1_S2_topology = subspace_topology UNIV
     (product_topology_on top1_open_sets
       (product_topology_on top1_open_sets top1_open_sets)) top1_S2"

text \<open>S^2 is Hausdorff (subspace of Hausdorff R^3).\<close>
lemma top1_S2_is_hausdorff:
  "is_hausdorff_on top1_S2 top1_S2_topology"
proof -
  have "top1_S2 \<subseteq> (UNIV :: (real \<times> real \<times> real) set)" by simp
  thus ?thesis unfolding top1_S2_topology_def
    using conjunct2[OF conjunct2[OF Theorem_17_11]] top1_R3_is_hausdorff by (by100 blast)
qed

text \<open>S^2 has strict topology.\<close>
lemma top1_S2_is_topology_on_strict:
  "is_topology_on_strict top1_S2 top1_S2_topology"
  unfolding is_topology_on_strict_def
proof (intro conjI)
  show "is_topology_on top1_S2 top1_S2_topology"
  proof -
    have hR3: "is_topology_on (UNIV :: (real \<times> real \<times> real) set)
        (product_topology_on top1_open_sets (product_topology_on top1_open_sets top1_open_sets))"
      using top1_R3_is_hausdorff unfolding is_hausdorff_on_def by (by100 blast)
    show ?thesis unfolding top1_S2_topology_def
      by (rule subspace_topology_is_topology_on[OF hR3]) simp
  qed
  show "top1_S2_topology \<subseteq> Pow top1_S2"
    unfolding top1_S2_topology_def subspace_topology_def by (by100 blast)
qed

text \<open>A set C separates a space X if X - C has more than one component.\<close>
definition top1_separates_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_separates_on X TX C \<longleftrightarrow>
     \<not> top1_connected_on (X - C) (subspace_topology X TX (X - C))"

lemma top1_separates_on_def_expand:
  "top1_separates_on X TX C \<Longrightarrow>
     \<not> top1_connected_on (X - C) (subspace_topology X TX (X - C))"
  unfolding top1_separates_on_def by blast

lemma top1_separates_onI:
  "\<not> top1_connected_on (X - C) (subspace_topology X TX (X - C)) \<Longrightarrow>
    top1_separates_on X TX C"
  unfolding top1_separates_on_def by (by100 blast)

(** from \<S>61 Lemma 61.1: unbounded/bounded components of R^2-h(C) correspond to
    S^2-b components under a homeomorphism h: S^2-b \<rightarrow> R^2.
    If U is a component of S^2 - C not containing b, then h(U) is a BOUNDED
    component of R^2 - h(C). If U contains b, then h(U - {b}) is the UNBOUNDED
    component of R^2 - h(C). **)
text \<open>Stereographic projection: homeomorphism S^2 - {north pole} \<cong> R^2.\<close>
definition stereographic_proj :: "real \<times> real \<times> real \<Rightarrow> real \<times> real" where
  "stereographic_proj p = (fst p / (1 - snd (snd p)), fst (snd p) / (1 - snd (snd p)))"

definition north_pole :: "real \<times> real \<times> real" where
  "north_pole = (0, 0, 1)"

lemma north_pole_in_S2: "north_pole \<in> top1_S2"
  unfolding north_pole_def top1_S2_def by simp

definition stereographic_inv :: "real \<times> real \<Rightarrow> real \<times> real \<times> real" where
  "stereographic_inv q = (let u = fst q; v = snd q; d = u^2 + v^2 + 1
     in (2*u/d, 2*v/d, (u^2 + v^2 - 1)/d))"

lemma stereo_denom_pos: "(fst q)^2 + (snd q)^2 + 1 > (0::real)"
  by (smt (verit) power2_less_0 zero_less_one)

lemma stereo_denom_ne: "(fst q)^2 + (snd q)^2 + 1 \<noteq> (0::real)"
  using stereo_denom_pos[of q] by linarith

lemma stereographic_inv_in_S2:
  "stereographic_inv q \<in> top1_S2"
proof -
  let ?u = "fst q" and ?v = "snd q"
  let ?d = "?u^2 + ?v^2 + 1"
  have hd_ne: "?d \<noteq> 0" by (rule stereo_denom_ne)
  have "stereographic_inv q = (2*?u/?d, 2*?v/?d, (?u^2 + ?v^2 - 1)/?d)"
    unfolding stereographic_inv_def Let_def by simp
  moreover have "(2*?u/?d)^2 + (2*?v/?d)^2 + ((?u^2 + ?v^2 - 1)/?d)^2 = 1"
  proof -
    have "(2*?u/?d)^2 + (2*?v/?d)^2 + ((?u^2 + ?v^2 - 1)/?d)^2
        = (4*?u^2 + 4*?v^2 + (?u^2 + ?v^2 - 1)^2) / ?d^2"
      by (simp add: power_divide add_divide_distrib[symmetric])
    also have "4*?u^2 + 4*?v^2 + (?u^2 + ?v^2 - 1)^2 = ?d^2"
      by (simp add: power2_eq_square algebra_simps)
    also have "?d^2 / ?d^2 = 1" using hd_ne by simp
    finally show ?thesis .
  qed
  ultimately show ?thesis unfolding top1_S2_def by simp
qed

lemma stereographic_inv_not_north:
  "stereographic_inv q \<noteq> north_pole"
proof
  let ?u = "fst q" and ?v = "snd q"
  let ?d = "?u^2 + ?v^2 + 1"
  assume heq: "stereographic_inv q = north_pole"
  have hinv: "stereographic_inv q = (2*?u/?d, 2*?v/?d, (?u^2+?v^2-1)/?d)"
    unfolding stereographic_inv_def Let_def by simp
  have hz: "(?u^2+?v^2-1)/?d = 1"
    using heq hinv unfolding north_pole_def by simp
  have hd_ne: "?d \<noteq> 0" by (rule stereo_denom_ne)
  have "?u^2+?v^2-1 = ?d" using hz hd_ne by (simp add: field_simps)
  hence "?u^2+?v^2-1 = ?u^2+?v^2+1" by simp
  thus False by linarith
qed

lemma stereographic_proj_inv:
  assumes "p \<in> top1_S2 - {north_pole}"
  shows "stereographic_inv (stereographic_proj p) = p"
proof -
  obtain x y z where hxyz: "p = (x, y, z)" by (cases p, cases "snd p") auto
  have hp_S2: "x^2 + y^2 + z^2 = 1"
    using assms unfolding hxyz top1_S2_def by simp
  have hz_ne: "z \<noteq> 1"
  proof
    assume "z = 1"
    hence "x^2 + y^2 = 0" using hp_S2 by simp
    hence "x = 0" "y = 0" by (simp_all add: sum_power2_eq_zero_iff)
    hence "p = north_pole" unfolding hxyz north_pole_def using \<open>z = 1\<close> by simp
    thus False using assms by simp
  qed
  hence h1mz_ne: "1 - z \<noteq> 0" by simp
  let ?u = "x / (1-z)" and ?v = "y / (1-z)"
  have hproj: "stereographic_proj p = (?u, ?v)"
    unfolding stereographic_proj_def hxyz by simp
  have hd: "?u^2 + ?v^2 + 1 = 2/(1-z)"
  proof -
    have "?u^2 + ?v^2 = (x^2 + y^2) / (1-z)^2"
      by (simp add: power_divide add_divide_distrib[symmetric])
    also have "x^2 + y^2 = 1 - z^2" using hp_S2 by linarith
    also have "1 - z^2 = (1-z)*(1+z)" by (simp add: power2_eq_square algebra_simps)
    also have "(1-z)*(1+z) / (1-z)^2 = (1+z)/(1-z)"
      using h1mz_ne by (simp add: power2_eq_square nonzero_mult_div_cancel_left)
    finally have huv_eq: "?u^2 + ?v^2 = (1+z)/(1-z)" .
    have h_rhs: "(1-z)/(1-z) = (1::real)" using h1mz_ne by simp
    have "?u^2 + ?v^2 + 1 = (1+z)/(1-z) + (1-z)/(1-z)" using huv_eq h_rhs by simp
    also have "(1+z)/(1-z) + (1-z)/(1-z) = ((1+z) + (1-z)) / (1-z)"
      by (rule add_divide_distrib[symmetric])
    also have "(1+z) + (1-z) = (2::real)" by simp
    finally show ?thesis .
  qed
  have hd_ne: "?u^2 + ?v^2 + 1 \<noteq> 0"
    using hd h1mz_ne by simp
  have hd_val: "2/(1-z) \<noteq> 0" using h1mz_ne by simp
  \<comment> \<open>First component: 2*u/d = 2*(x/(1-z)) / (2/(1-z)) = x.\<close>
  have h1: "2*?u / (?u^2 + ?v^2 + 1) = x"
    unfolding hd using h1mz_ne by (simp add: field_simps)
  \<comment> \<open>Second component: 2*v/d = y.\<close>
  have h2: "2*?v / (?u^2 + ?v^2 + 1) = y"
    unfolding hd using h1mz_ne by (simp add: field_simps)
  \<comment> \<open>Third component: (u^2+v^2-1)/d.\<close>
  have h3: "(?u^2 + ?v^2 - 1) / (?u^2 + ?v^2 + 1) = z"
  proof -
    have huvm1: "?u^2 + ?v^2 - 1 = 2/(1-z) - 2" using hd by linarith
    \<comment> \<open>Goal: (2/(1-z) - 2) / (2/(1-z)) = z. Multiply both sides by 2/(1-z).\<close>
    have h2dz: "2/(1-z) \<noteq> (0::real)" using h1mz_ne by simp
    have key: "(2/(1-z) - 2) = z * (2/(1-z))"
    proof -
      have "2*(1-z)/(1-z) = (2::real)"
        using h1mz_ne nonzero_mult_div_cancel_right by (by100 blast)
      hence "2 = 2*(1-z)/(1-z)" by simp
      hence "2/(1-z) - 2 = 2/(1-z) - 2*(1-z)/(1-z)" by simp
      also have "\<dots> = (2 - 2*(1-z))/(1-z)" by (rule diff_divide_distrib[symmetric])
      also have "(2::real) - 2*(1-z) = 2*z"
        by (simp add: left_diff_distrib)
      finally have "2/(1-z) - 2 = 2*z/(1-z)" .
      also have "2*z/(1-z) = z * (2/(1-z))" by simp
      finally show ?thesis .
    qed
    have "(?u^2 + ?v^2 - 1) / (?u^2 + ?v^2 + 1) = (2/(1-z) - 2) / (2/(1-z))"
      using huvm1 hd by simp
    also have "\<dots> = z * (2/(1-z)) / (2/(1-z))" using key by simp
    also have "\<dots> = z" using h2dz by simp
    finally show ?thesis .
  qed
  show ?thesis unfolding hproj stereographic_inv_def Let_def
    using h1 h2 h3 hxyz by simp
qed

lemma stereographic_inv_proj:
  "stereographic_proj (stereographic_inv q) = q"
proof -
  let ?u = "fst q" and ?v = "snd q"
  let ?d = "?u^2 + ?v^2 + 1"
  have hd_ne: "?d \<noteq> 0" by (rule stereo_denom_ne)
  have hd_pos: "?d > 0" by (rule stereo_denom_pos)
  have hinv: "stereographic_inv q = (2*?u/?d, 2*?v/?d, (?u^2+?v^2-1)/?d)"
    unfolding stereographic_inv_def Let_def by simp
  have hz: "snd (snd (stereographic_inv q)) = (?u^2+?v^2-1)/?d"
    using hinv by simp
  have h1mz: "1 - (?u^2+?v^2-1)/?d = 2/?d"
    using hd_ne by (simp add: field_simps)
  have h2d_ne: "2/?d \<noteq> (0::real)" using hd_ne by simp
  have hx: "fst (stereographic_inv q) = 2*?u/?d"
    using hinv by simp
  have hy: "fst (snd (stereographic_inv q)) = 2*?v/?d"
    using hinv by simp
  have hfst: "fst (stereographic_proj (stereographic_inv q)) = ?u"
  proof -
    have "fst (stereographic_proj (stereographic_inv q))
        = fst (stereographic_inv q) / (1 - snd (snd (stereographic_inv q)))"
      unfolding stereographic_proj_def by simp
    also have "\<dots> = (2*?u/?d) / (2/?d)" using hx hz h1mz by simp
    also have "\<dots> = ?u" using hd_ne by (simp add: field_simps)
    finally show ?thesis .
  qed
  have hsnd: "snd (stereographic_proj (stereographic_inv q)) = ?v"
  proof -
    have "snd (stereographic_proj (stereographic_inv q))
        = fst (snd (stereographic_inv q)) / (1 - snd (snd (stereographic_inv q)))"
      unfolding stereographic_proj_def by simp
    also have "\<dots> = (2*?v/?d) / (2/?d)" using hy hz h1mz by simp
    also have "\<dots> = ?v" using hd_ne by (simp add: field_simps)
    finally show ?thesis .
  qed
  show ?thesis by (rule prod_eqI) (simp_all add: hfst hsnd)
qed

lemma stereographic_proj_homeomorphism:
  "top1_homeomorphism_on (top1_S2 - {north_pole})
     (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
     (UNIV :: (real \<times> real) set)
     (product_topology_on top1_open_sets top1_open_sets)
     stereographic_proj"
  unfolding top1_homeomorphism_on_def
proof (intro conjI)
  let ?S = "top1_S2 - {north_pole}"
  let ?TS = "subspace_topology top1_S2 top1_S2_topology ?S"
  let ?TR2 = "product_topology_on (top1_open_sets :: real set set) top1_open_sets"
  show "is_topology_on ?S ?TS"
  proof -
    have "is_topology_on top1_S2 top1_S2_topology"
      using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
    thus ?thesis by (rule subspace_topology_is_topology_on) simp
  qed
  show "is_topology_on (UNIV :: (real \<times> real) set) ?TR2"
  proof -
    have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
      by (rule top1_open_sets_is_topology_on_UNIV)
    show ?thesis using product_topology_on_is_topology_on[OF hTR hTR] by simp
  qed
  show "bij_betw stereographic_proj ?S (UNIV :: (real \<times> real) set)"
    unfolding bij_betw_def
  proof (intro conjI)
    show "inj_on stereographic_proj ?S"
    proof (rule inj_onI)
      fix a b assume "a \<in> ?S" "b \<in> ?S" "stereographic_proj a = stereographic_proj b"
      hence "stereographic_inv (stereographic_proj a) = stereographic_inv (stereographic_proj b)"
        by simp
      thus "a = b" using stereographic_proj_inv[of a] stereographic_proj_inv[of b]
          \<open>a \<in> ?S\<close> \<open>b \<in> ?S\<close> by simp
    qed
  next
    show "stereographic_proj ` ?S = UNIV"
    proof (rule set_eqI, rule iffI)
      fix q :: "real \<times> real"
      assume "q \<in> stereographic_proj ` ?S" thus "q \<in> UNIV" by simp
    next
      fix q :: "real \<times> real" assume "q \<in> UNIV"
      have hinvS: "stereographic_inv q \<in> ?S"
        using stereographic_inv_in_S2 stereographic_inv_not_north by simp
      have "stereographic_proj (stereographic_inv q) = q"
        by (rule stereographic_inv_proj)
      hence "q = stereographic_proj (stereographic_inv q)" by simp
      thus "q \<in> stereographic_proj ` ?S" using hinvS by (by100 blast)
    qed
  qed
  show "top1_continuous_map_on ?S ?TS UNIV ?TR2 stereographic_proj"
  proof -
    \<comment> \<open>stereographic_proj is continuous on S^2-{north_pole} as a rational function
       (defined wherever z \<noteq> 1, which holds on S^2-{N}).\<close>
    have hproj_cont: "continuous_on ?S stereographic_proj"
    proof -
      have "\<And>p. p \<in> ?S \<Longrightarrow> 1 - snd (snd p) \<noteq> 0"
      proof -
        fix p assume hp: "p \<in> ?S"
        show "1 - snd (snd p) \<noteq> 0"
        proof
          assume h0: "1 - snd (snd p) = 0"
          hence hz1: "snd (snd p) = 1" by simp
          have hp_S2: "p \<in> top1_S2" using hp by simp
          hence "fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1"
            unfolding top1_S2_def by simp
          hence "fst p ^ 2 + fst (snd p) ^ 2 = 0" using hz1 by simp
          hence "fst p = 0" "fst (snd p) = 0"
            by (simp_all add: sum_power2_eq_zero_iff)
          hence "p = (0, 0, 1)" using hz1
            by (cases p, cases "snd p") simp
          hence "p = north_pole" unfolding north_pole_def by simp
          thus False using hp by simp
        qed
      qed
      thus ?thesis unfolding stereographic_proj_def
        by (intro continuous_intros continuous_on_divide) auto
    qed
    show ?thesis unfolding top1_continuous_map_on_def product_topology_on_open_sets
    proof (intro conjI ballI)
      fix p assume "p \<in> ?S" thus "stereographic_proj p \<in> UNIV" by simp
    next
      fix V :: "(real \<times> real) set"
      assume hV: "V \<in> (top1_open_sets :: (real \<times> real) set set)"
      have hVo: "open V" using hV unfolding top1_open_sets_def by (by100 blast)
      \<comment> \<open>Preimage: {p \<in> S | proj(p) \<in> V} = S \<inter> proj\<inverse>(V).\<close>
      \<comment> \<open>proj\<inverse>(V) is open in S since proj is continuous_on S.\<close>
      \<comment> \<open>By continuous_on_open_invariant: \<exists>U open. proj\<inverse>(V) \<inter> S = U \<inter> S.\<close>
      have "\<exists>A. open A \<and> A \<inter> ?S = stereographic_proj -` V \<inter> ?S"
        using iffD1[OF continuous_on_open_invariant hproj_cont] hVo by (by100 blast)
      then obtain W where hWo: "open W" and hWeq: "W \<inter> ?S = stereographic_proj -` V \<inter> ?S"
        by auto
      have "{p \<in> ?S. stereographic_proj p \<in> V} = W \<inter> ?S" using hWeq by (by100 auto)
      moreover have "W \<inter> ?S \<in> ?TS"
      proof -
        have "W \<in> (top1_open_sets :: (real \<times> real \<times> real) set set)"
          using hWo unfolding top1_open_sets_def by (by100 blast)
        hence hW_R3: "W \<in> product_topology_on top1_open_sets
            (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_open_sets by metis
        have "top1_S2 \<inter> W \<in> top1_S2_topology"
          unfolding top1_S2_topology_def subspace_topology_def using hW_R3 by (by100 blast)
        hence "?S \<inter> (top1_S2 \<inter> W) \<in> ?TS"
          unfolding subspace_topology_def by (by100 blast)
        moreover have "?S \<inter> (top1_S2 \<inter> W) = W \<inter> ?S" by (by100 blast)
        ultimately show ?thesis by simp
      qed
      ultimately show "{p \<in> ?S. stereographic_proj p \<in> V} \<in> ?TS" by simp
    qed
  qed
  show "top1_continuous_map_on UNIV ?TR2 ?S ?TS (inv_into ?S stereographic_proj)"
  proof -
    \<comment> \<open>inv_into agrees with stereographic_inv on UNIV.\<close>
    have hinv_eq: "\<And>q. inv_into ?S stereographic_proj q = stereographic_inv q"
    proof -
      fix q :: "real \<times> real"
      have "stereographic_inv q \<in> ?S"
        using stereographic_inv_in_S2 stereographic_inv_not_north by simp
      moreover have "stereographic_proj (stereographic_inv q) = q"
        by (rule stereographic_inv_proj)
      ultimately show "inv_into ?S stereographic_proj q = stereographic_inv q"
      proof (intro inv_into_f_eq)
        show "inj_on stereographic_proj ?S"
          by (rule inj_onI) (metis stereographic_proj_inv)
      qed
    qed
    \<comment> \<open>stereographic_inv is continuous on UNIV.\<close>
    have hinv_cont: "continuous_on UNIV stereographic_inv"
      unfolding stereographic_inv_def Let_def
      by (intro continuous_intros continuous_on_divide)
         (simp_all add: stereo_denom_ne)
    \<comment> \<open>Bridge: since inv_into = stereographic_inv on UNIV,
       and stereographic_inv is continuous_on UNIV with range in ?S,
       show top1_continuous_map_on.\<close>
    have hinv_map: "\<And>q. stereographic_inv q \<in> ?S"
      using stereographic_inv_in_S2 stereographic_inv_not_north by simp
    show ?thesis unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix q :: "real \<times> real" assume "q \<in> UNIV"
      show "inv_into ?S stereographic_proj q \<in> ?S"
        using hinv_eq hinv_map by simp
    next
      fix V assume hV: "V \<in> ?TS"
      then obtain W where hWS2: "W \<in> top1_S2_topology" and hVeq: "V = ?S \<inter> W"
        unfolding subspace_topology_def by (by100 blast)
      then obtain W' where hW'R3: "W' \<in> product_topology_on top1_open_sets
            (product_topology_on top1_open_sets top1_open_sets)"
          and hWeq: "W = top1_S2 \<inter> W'"
        unfolding top1_S2_topology_def subspace_topology_def by (by100 blast)
      have "W' \<in> (top1_open_sets :: (real \<times> real \<times> real) set set)"
        using hW'R3 product_topology_on_open_sets by metis
      hence hW'open: "open W'" unfolding top1_open_sets_def by (by100 blast)
      have hVeq': "V = ?S \<inter> W'" using hVeq hWeq by (by100 blast)
      \<comment> \<open>Preimage under inv_into = preimage under stereographic_inv.\<close>
      have hpre_eq: "{q \<in> UNIV. inv_into ?S stereographic_proj q \<in> V}
          = stereographic_inv -` V"
        using hinv_eq by auto
      have "stereographic_inv -` V = stereographic_inv -` (?S \<inter> W')"
        using hVeq' by simp
      also have "\<dots> = stereographic_inv -` W'"
        using hinv_map by auto
      finally have hpre: "{q \<in> UNIV. inv_into ?S stereographic_proj q \<in> V}
          = stereographic_inv -` W'" using hpre_eq by simp
      have "open (stereographic_inv -` W')"
        by (rule open_vimage[OF hW'open hinv_cont])
      hence "stereographic_inv -` W' \<in> (top1_open_sets :: (real \<times> real) set set)"
        unfolding top1_open_sets_def by (by100 blast)
      hence "stereographic_inv -` W' \<in> ?TR2"
        using product_topology_on_open_sets_real2 by metis
      thus "{q \<in> UNIV. inv_into ?S stereographic_proj q \<in> V} \<in> ?TR2"
        using hpre by simp
    qed
  qed
qed

text \<open>Key consequence: S^2 minus any point is homeomorphic to R^2, hence simply connected.\<close>
lemma R2_simply_connected:
  "top1_simply_connected_on (UNIV :: (real \<times> real) set)
     (product_topology_on top1_open_sets top1_open_sets)"
  unfolding top1_simply_connected_on_def
proof (intro conjI allI impI ballI)
  \<comment> \<open>Part 1: R2 is path-connected. Straight line between any two points.\<close>
  show "top1_path_connected_on (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets)"
  proof -
    have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hTR2: "is_topology_on (UNIV :: (real \<times> real) set)
        (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
      using product_topology_on_is_topology_on[OF hTR hTR] by simp
    have "\<forall>x\<in>(UNIV :: (real \<times> real) set). \<forall>y\<in>UNIV.
        \<exists>f. top1_is_path_on UNIV (product_topology_on top1_open_sets top1_open_sets) x y f"
    proof (intro ballI)
      fix x y :: "real \<times> real"
      assume "x \<in> UNIV" "y \<in> UNIV"
      let ?\<gamma> = "\<lambda>t::real. ((1-t)*fst x + t*fst y, (1-t)*snd x + t*snd y)"
      have h\<gamma>_cont_univ: "continuous_on UNIV ?\<gamma>"
        by (intro continuous_intros)
      have h\<gamma>_cont: "top1_continuous_map_on I_set I_top
          (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) ?\<gamma>"
        unfolding top1_continuous_map_on_def product_topology_on_open_sets
      proof (intro conjI ballI)
        fix s assume "s \<in> I_set" thus "?\<gamma> s \<in> UNIV" by simp
      next
        fix V assume hV: "V \<in> (top1_open_sets :: (real \<times> real) set set)"
        have hVopen: "open V" using hV unfolding top1_open_sets_def by (by100 blast)
        have hpre: "open (?\<gamma> -` V)"
          by (rule open_vimage[OF hVopen h\<gamma>_cont_univ])
        have hpre_os: "?\<gamma> -` V \<in> (top1_open_sets :: real set set)"
          using hpre unfolding top1_open_sets_def by (by100 blast)
        have "{s \<in> I_set. ?\<gamma> s \<in> V} = I_set \<inter> (?\<gamma> -` V)" by (by100 auto)
        thus "{s \<in> I_set. ?\<gamma> s \<in> V} \<in> I_top"
          unfolding top1_unit_interval_topology_def subspace_topology_def
          using hpre_os by (by100 blast)
      qed
      have "?\<gamma> 0 = x" by simp
      moreover have "?\<gamma> 1 = y" by simp
      ultimately show "\<exists>f. top1_is_path_on UNIV (product_topology_on top1_open_sets top1_open_sets) x y f"
        unfolding top1_is_path_on_def using h\<gamma>_cont by (by100 blast)
    qed
    thus ?thesis unfolding top1_path_connected_on_def using hTR2 by simp
  qed
next
  \<comment> \<open>Part 2: Every loop is nulhomotopic. Straight-line contraction H(s,t) = (1-t)*f(s) + t*x0.\<close>
  fix x0 :: "real \<times> real" and f
  assume hx0: "x0 \<in> (UNIV :: (real \<times> real) set)"
  assume hf: "top1_is_loop_on (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets) x0 f"
  \<comment> \<open>Define the straight-line homotopy.\<close>
  define H where "H = (\<lambda>(s::real, t::real). ((1-t) * fst (f s) + t * fst x0,
                                               (1-t) * snd (f s) + t * snd x0))"
  \<comment> \<open>H(s,0) = f(s), H(s,1) = x0, H(0,t) = (1-t)*f(0)+t*x0 = (1-t)*x0+t*x0 = x0,
     H(1,t) = (1-t)*f(1)+t*x0 = (1-t)*x0+t*x0 = x0 (since f is a loop).\<close>
  show "top1_path_homotopic_on (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets) x0 x0 f (top1_constant_path x0)"
  proof -
    have hfcont: "top1_continuous_map_on I_set I_top
        (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) f"
      using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hf0: "f 0 = x0" and hf1: "f 1 = x0"
      using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
    \<comment> \<open>Extract continuous_on I_set f (in standard Isabelle sense).\<close>
    have hf_cont_I: "continuous_on I_set f"
      unfolding continuous_on_open_invariant
    proof (intro allI impI)
      fix B :: "(real \<times> real) set" assume hBo: "open B"
      have hBos: "B \<in> (top1_open_sets :: (real \<times> real) set set)"
        using hBo unfolding top1_open_sets_def by (by100 blast)
      have hBprod: "B \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
        using hBos product_topology_on_open_sets_real2 by (by100 metis)
      have hpre: "{s \<in> I_set. f s \<in> B} \<in> I_top"
        using hBprod hfcont unfolding top1_continuous_map_on_def by (by100 blast)
      have hpre': "{s \<in> I_set. f s \<in> B} \<in> subspace_topology UNIV top1_open_sets I_set"
        using hpre unfolding top1_unit_interval_topology_def .
      obtain W where hW: "W \<in> (top1_open_sets :: real set set)"
          and heq: "{s \<in> I_set. f s \<in> B} = I_set \<inter> W"
        using hpre' unfolding subspace_topology_def by (by100 blast)
      have "open W" using hW unfolding top1_open_sets_def by (by100 blast)
      moreover have "W \<inter> I_set = f -` B \<inter> I_set" using heq by (by100 blast)
      ultimately show "\<exists>A. open A \<and> A \<inter> I_set = f -` B \<inter> I_set" by (by100 blast)
    qed
    have hfst_cont_I: "continuous_on I_set (fst \<circ> f)"
      by (intro continuous_on_compose[OF hf_cont_I] continuous_on_subset[OF continuous_on_fst]) auto
    have hsnd_cont_I: "continuous_on I_set (snd \<circ> f)"
      by (intro continuous_on_compose[OF hf_cont_I] continuous_on_subset[OF continuous_on_snd]) auto
    \<comment> \<open>Define straight-line homotopy using top1_slh_ext component-wise.\<close>
    define H_ext where "H_ext = (\<lambda>p::real\<times>real.
        (top1_slh_ext (fst \<circ> f) (fst x0) p,
         top1_slh_ext (snd \<circ> f) (snd x0) p))"
    have hH_cont_univ: "continuous_on UNIV H_ext"
      unfolding H_ext_def
      by (intro continuous_intros top1_slh_ext_continuous[OF hfst_cont_I]
              top1_slh_ext_continuous[OF hsnd_cont_I])
    have hH_eq: "\<And>s t. s \<in> I_set \<Longrightarrow> t \<in> I_set \<Longrightarrow>
        H_ext (s, t) = ((1-t) * fst (f s) + t * fst x0, (1-t) * snd (f s) + t * snd x0)"
    proof -
      fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set"
      have hst: "(s, t) \<in> I_set \<times> I_set" using hs ht by simp
      have "top1_slh_ext (fst \<circ> f) (fst x0) (s, t) = (1 - t) * (fst \<circ> f) s + t * fst x0"
        using top1_slh_ext_agrees[OF hst] by simp
      moreover have "top1_slh_ext (snd \<circ> f) (snd x0) (s, t) = (1 - t) * (snd \<circ> f) s + t * snd x0"
        using top1_slh_ext_agrees[OF hst] by simp
      ultimately show "H_ext (s, t) = ((1-t) * fst (f s) + t * fst x0, (1-t) * snd (f s) + t * snd x0)"
        unfolding H_ext_def comp_def by simp
    qed
    \<comment> \<open>Bridge to top1_continuous_map_on.\<close>
    have hH_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) H_ext"
      unfolding top1_continuous_map_on_def product_topology_on_open_sets
    proof (intro conjI ballI)
      fix p assume "p \<in> I_set \<times> I_set" thus "H_ext p \<in> UNIV" by simp
    next
      fix V :: "(real \<times> real) set"
      assume hV: "V \<in> (top1_open_sets :: (real \<times> real) set set)"
      have hVo: "open V" using hV unfolding top1_open_sets_def by (by100 blast)
      have hFV: "open (H_ext -` V)" by (rule open_vimage[OF hVo hH_cont_univ])
      have hFV_os: "H_ext -` V \<in> (top1_open_sets :: (real\<times>real) set set)"
        using hFV unfolding top1_open_sets_def by (by100 blast)
      have hFV_prod: "H_ext -` V \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
        using hFV_os product_topology_on_open_sets_real2 by metis
      have "(I_set \<times> I_set) \<inter> (H_ext -` V) \<in> product_topology_on I_top I_top"
        using hFV_prod unfolding II_topology_eq_subspace subspace_topology_def by (by100 blast)
      moreover have "{p \<in> I_set \<times> I_set. H_ext p \<in> V} = (I_set \<times> I_set) \<inter> (H_ext -` V)"
        by (by100 auto)
      ultimately show "{p \<in> I_set \<times> I_set. H_ext p \<in> V} \<in> II_topology"
        unfolding II_topology_def by simp
    qed
    \<comment> \<open>Boundary conditions.\<close>
    have hHs0: "\<forall>s\<in>I_set. H_ext (s, 0) = f s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "H_ext (s, 0) = ((1-0) * fst (f s) + 0 * fst x0, (1-0) * snd (f s) + 0 * snd x0)"
        using hH_eq[OF hs] by (simp add: top1_unit_interval_def)
      thus "H_ext (s, 0) = f s" by simp
    qed
    have hHs1: "\<forall>s\<in>I_set. H_ext (s, 1) = top1_constant_path x0 s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "H_ext (s, 1) = ((1-1) * fst (f s) + 1 * fst x0, (1-1) * snd (f s) + 1 * snd x0)"
        using hH_eq[OF hs] by (simp add: top1_unit_interval_def)
      thus "H_ext (s, 1) = top1_constant_path x0 s"
        unfolding top1_constant_path_def by simp
    qed
    have hH0t: "\<forall>t\<in>I_set. H_ext (0, t) = x0"
    proof
      fix t assume ht: "t \<in> I_set"
      have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
      have "H_ext (0, t) = ((1-t) * fst (f 0) + t * fst x0, (1-t) * snd (f 0) + t * snd x0)"
        using hH_eq[OF h0I ht] .
      also have "\<dots> = ((1-t) * fst x0 + t * fst x0, (1-t) * snd x0 + t * snd x0)"
        by (simp add: hf0)
      also have "\<dots> = x0" by (simp add: algebra_simps)
      finally show "H_ext (0, t) = x0" .
    qed
    have hH1t: "\<forall>t\<in>I_set. H_ext (1, t) = x0"
    proof
      fix t assume ht: "t \<in> I_set"
      have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
      have "H_ext (1, t) = ((1-t) * fst (f 1) + t * fst x0, (1-t) * snd (f 1) + t * snd x0)"
        using hH_eq[OF h1I ht] .
      also have "\<dots> = ((1-t) * fst x0 + t * fst x0, (1-t) * snd x0 + t * snd x0)"
        by (simp add: hf1)
      also have "\<dots> = x0" by (simp add: algebra_simps)
      finally show "H_ext (1, t) = x0" .
    qed
    \<comment> \<open>f and constant path are paths on UNIV.\<close>
    have hTR2: "is_topology_on (UNIV :: (real \<times> real) set)
        (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
    proof -
      have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
        by (rule top1_open_sets_is_topology_on_UNIV)
      show ?thesis using product_topology_on_is_topology_on[OF hTR hTR] by simp
    qed
    have hf_path: "top1_is_path_on UNIV (product_topology_on top1_open_sets top1_open_sets) x0 x0 f"
      using hf unfolding top1_is_loop_on_def by simp
    have hc_path: "top1_is_path_on UNIV (product_topology_on top1_open_sets top1_open_sets) x0 x0
        (top1_constant_path x0)"
      by (rule top1_constant_path_is_path[OF hTR2]) simp
    show ?thesis unfolding top1_path_homotopic_on_def
      using hf_path hc_path hH_cont hHs0 hHs1 hH0t hH1t
      by (intro conjI exI[of _ H_ext]) auto
  qed
qed

lemma homeomorphism_preserves_simply_connected:
  assumes hhom: "top1_homeomorphism_on X TX Y TY h"
      and hsc: "top1_simply_connected_on Y TY"
  shows "top1_simply_connected_on X TX"
  unfolding top1_simply_connected_on_def
proof (intro conjI allI impI ballI)
  have hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hbij: "bij_betw h X Y"
      and hh: "top1_continuous_map_on X TX Y TY h"
      and hg: "top1_continuous_map_on Y TY X TX (inv_into X h)"
    using hhom unfolding top1_homeomorphism_on_def by (by100 blast)+
  have hg_cont: "top1_continuous_map_on Y TY X TX (inv_into X h)" by (rule hg)
  have hinj: "inj_on h X" using hbij unfolding bij_betw_def by simp
  have hh_inv: "\<And>x. x \<in> X \<Longrightarrow> inv_into X h (h x) = x"
    by (rule inv_into_f_f[OF hinj])
  have hh_map: "\<And>x. x \<in> X \<Longrightarrow> h x \<in> Y" using hbij unfolding bij_betw_def by auto
  have hg_map: "\<And>y. y \<in> Y \<Longrightarrow> inv_into X h y \<in> X"
    using hbij unfolding bij_betw_def by (simp add: inv_into_into)
  have hg_inv: "\<And>y. y \<in> Y \<Longrightarrow> h (inv_into X h y) = y"
    using hbij unfolding bij_betw_def by (simp add: f_inv_into_f)
  \<comment> \<open>Path-connected: transfer via h and inv.\<close>
  show "top1_path_connected_on X TX"
    unfolding top1_path_connected_on_def
  proof (intro conjI ballI)
    show "is_topology_on X TX" by (rule hTX)
  next
    fix x1 x2 assume hx1: "x1 \<in> X" and hx2: "x2 \<in> X"
    have "h x1 \<in> Y" by (rule hh_map[OF hx1])
    moreover have "h x2 \<in> Y" by (rule hh_map[OF hx2])
    ultimately obtain \<alpha> where h\<alpha>: "top1_is_path_on Y TY (h x1) (h x2) \<alpha>"
      using hsc unfolding top1_simply_connected_on_def top1_path_connected_on_def by (by100 blast)
    have "top1_is_path_on X TX (inv_into X h (h x1)) (inv_into X h (h x2)) (inv_into X h \<circ> \<alpha>)"
    proof -
      have h\<alpha>_cont: "top1_continuous_map_on I_set I_top Y TY \<alpha>"
        using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
      have hinv_\<alpha>_cont: "top1_continuous_map_on I_set I_top X TX (inv_into X h \<circ> \<alpha>)"
        by (rule top1_continuous_map_on_comp[OF h\<alpha>_cont hg])
      have "(\<alpha> 0) = h x1" using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
      hence h0: "(inv_into X h \<circ> \<alpha>) 0 = inv_into X h (h x1)" by simp
      have "(\<alpha> 1) = h x2" using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
      hence h1: "(inv_into X h \<circ> \<alpha>) 1 = inv_into X h (h x2)" by simp
      show ?thesis unfolding top1_is_path_on_def using hinv_\<alpha>_cont h0 h1 by (by100 blast)
    qed
    hence "top1_is_path_on X TX x1 x2 (inv_into X h \<circ> \<alpha>)"
      using hh_inv[OF hx1] hh_inv[OF hx2] by simp
    thus "\<exists>f. top1_is_path_on X TX x1 x2 f" by (by100 blast)
  qed
next
  fix x0 f
  assume hx0: "x0 \<in> X"
  assume hf: "top1_is_loop_on X TX x0 f"
  have hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hh: "top1_continuous_map_on X TX Y TY h"
      and hg: "top1_continuous_map_on Y TY X TX (inv_into X h)"
      and hbij: "bij_betw h X Y"
    using hhom unfolding top1_homeomorphism_on_def by (by100 blast)+
  have hh_map: "\<And>x. x \<in> X \<Longrightarrow> h x \<in> Y" using hbij unfolding bij_betw_def by auto
  have hinj: "inj_on h X" using hbij unfolding bij_betw_def by simp
  have hh_inv: "\<And>x. x \<in> X \<Longrightarrow> inv_into X h (h x) = x"
    by (rule inv_into_f_f[OF hinj])
  \<comment> \<open>h\<circ>f is a loop at h(x0) in Y.\<close>
  have hhf_loop: "top1_is_loop_on Y TY (h x0) (h \<circ> f)"
    using top1_continuous_map_loop_early[OF hh hf] .
  \<comment> \<open>Y simply connected: h\<circ>f is contractible.\<close>
  have hhx0: "h x0 \<in> Y" by (rule hh_map[OF hx0])
  have hhf_contract: "top1_path_homotopic_on Y TY (h x0) (h x0)
      (h \<circ> f) (top1_constant_path (h x0))"
    using hsc hhx0 hhf_loop unfolding top1_simply_connected_on_def by (by100 blast)
  \<comment> \<open>Transfer back via inv_into: f = inv\<circ>h\<circ>f is contractible.\<close>
  have hg_transfer: "top1_path_homotopic_on X TX
      (inv_into X h (h x0)) (inv_into X h (h x0))
      (inv_into X h \<circ> (h \<circ> f)) (inv_into X h \<circ> top1_constant_path (h x0))"
    by (rule continuous_preserves_path_homotopic[OF hTY hTX hg hhf_contract])
  have "inv_into X h (h x0) = x0" by (rule hh_inv[OF hx0])
  moreover have "\<forall>s\<in>I_set. (inv_into X h \<circ> (h \<circ> f)) s = f s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "f s \<in> X" using hf hs
      unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def
      by (by100 blast)
    thus "(inv_into X h \<circ> (h \<circ> f)) s = f s" by (simp add: hh_inv)
  qed
  moreover have "\<forall>s\<in>I_set. (inv_into X h \<circ> top1_constant_path (h x0)) s = top1_constant_path x0 s"
    unfolding top1_constant_path_def using hh_inv[OF hx0] by simp
  ultimately have hinv_x0: "inv_into X h (h x0) = x0"
      and hinv_f: "\<forall>s\<in>I_set. (inv_into X h \<circ> (h \<circ> f)) s = f s"
      and hinv_c: "\<forall>s\<in>I_set. (inv_into X h \<circ> top1_constant_path (h x0)) s = top1_constant_path x0 s"
    by auto
  \<comment> \<open>Extract homotopy from hg_transfer, rebuild with I_set agreement.\<close>
  obtain H where hH_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX H"
      and hH0: "\<forall>s\<in>I_set. H (s, 0) = (inv_into X h \<circ> (h \<circ> f)) s"
      and hH1: "\<forall>s\<in>I_set. H (s, 1) = (inv_into X h \<circ> top1_constant_path (h x0)) s"
      and hHL: "\<forall>t\<in>I_set. H (0, t) = inv_into X h (h x0)"
      and hHR: "\<forall>t\<in>I_set. H (1, t) = inv_into X h (h x0)"
    using hg_transfer hinv_x0 unfolding top1_path_homotopic_on_def by auto
  have hfpath: "top1_is_path_on X TX x0 x0 f"
    using hf unfolding top1_is_loop_on_def .
  have hcpath: "top1_is_path_on X TX x0 x0 (top1_constant_path x0)"
    by (rule top1_constant_path_is_path[OF hTX hx0])
  show "top1_path_homotopic_on X TX x0 x0 f (top1_constant_path x0)"
    unfolding top1_path_homotopic_on_def
    using hfpath hcpath hH_cont
  proof (intro conjI exI[of _ H])
    show "\<forall>s\<in>I_set. H (s, 0) = f s" using hH0 hinv_f by simp
    show "\<forall>s\<in>I_set. H (s, 1) = top1_constant_path x0 s" using hH1 hinv_c by simp
    show "\<forall>t\<in>I_set. H (0, t) = x0" using hHL hinv_x0 by simp
    show "\<forall>t\<in>I_set. H (1, t) = x0" using hHR hinv_x0 by simp
  qed auto
qed

lemma S2_minus_north_pole_simply_connected:
  "top1_simply_connected_on (top1_S2 - {north_pole})
     (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))"
  by (rule homeomorphism_preserves_simply_connected[OF
      stereographic_proj_homeomorphism R2_simply_connected])

text \<open>Householder reflection: sends any point b \<in> S^2 to north_pole.
   When b \<noteq> N: R(p) = p - 2(v\<cdot>p)/(v\<cdot>v) * v where v = N - b = (-b1, -b2, 1-b3).
   When b = N: identity.\<close>
definition householder_S2 :: "real \<times> real \<times> real \<Rightarrow> real \<times> real \<times> real \<Rightarrow> real \<times> real \<times> real" where
  "householder_S2 b = (if b = north_pole then id
    else (let b1 = fst b; b2 = fst(snd b); b3 = snd(snd b)
      in (\<lambda>(x,y,z). let vdp = -b1*x+(-b2)*y+(1-b3)*z; c = 2*vdp/(2-2*b3)
          in (x-c*(-b1), y-c*(-b2), z-c*(1-b3)))))"

lemma householder_S2_homeo:
  assumes "b \<in> top1_S2"
  shows "top1_homeomorphism_on (top1_S2 - {b})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
      (top1_S2 - {north_pole})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
      (householder_S2 b)"
proof (cases "b = north_pole")
  case True
  have "householder_S2 north_pole = id" unfolding householder_S2_def by simp
  hence hid: "\<And>x. householder_S2 b x = x" using True by simp
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
  show ?thesis unfolding True top1_homeomorphism_on_def
    using hid
  proof (intro conjI)
    show "is_topology_on (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))"
      by (rule subspace_topology_is_topology_on[OF hTS2]) simp
    show "is_topology_on (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))"
      by (rule subspace_topology_is_topology_on[OF hTS2]) simp
    show "bij_betw (householder_S2 north_pole) (top1_S2 - {north_pole}) (top1_S2 - {north_pole})"
      using hid True by (simp add: bij_betw_def inj_on_def)
    show "top1_continuous_map_on (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
        (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) (householder_S2 north_pole)"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x assume "x \<in> top1_S2 - {north_pole}" thus "householder_S2 north_pole x \<in> top1_S2 - {north_pole}"
        using hid True by simp
    next
      fix V assume hV: "V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
      have "{x \<in> top1_S2 - {north_pole}. householder_S2 north_pole x \<in> V} = V \<inter> (top1_S2 - {north_pole})"
        using hid True by auto
      also have "\<dots> = V"
        using hV unfolding subspace_topology_def by (by100 blast)
      finally show "{x \<in> top1_S2 - {north_pole}. householder_S2 north_pole x \<in> V} \<in>
          subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
        using hV by simp
    qed
    show "top1_continuous_map_on (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
        (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
        (inv_into (top1_S2 - {north_pole}) (householder_S2 north_pole))"
    proof -
      have hinj: "inj_on (householder_S2 north_pole) (top1_S2 - {north_pole})"
      proof (rule inj_onI)
        fix x y assume "x \<in> top1_S2 - {north_pole}" "y \<in> top1_S2 - {north_pole}"
            "householder_S2 north_pole x = householder_S2 north_pole y"
        thus "x = y" using hid True by simp
      qed
      have hinv_eq: "\<And>x. x \<in> top1_S2 - {north_pole} \<Longrightarrow>
          inv_into (top1_S2 - {north_pole}) (householder_S2 north_pole) x = x"
      proof -
        fix x assume hx: "x \<in> top1_S2 - {north_pole}"
        have "householder_S2 north_pole x = x" using hid True by simp
        thus "inv_into (top1_S2 - {north_pole}) (householder_S2 north_pole) x = x"
          using hx hinj by (intro inv_into_f_eq) auto
      qed
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix x assume hx: "x \<in> top1_S2 - {north_pole}"
        show "inv_into (top1_S2 - {north_pole}) (householder_S2 north_pole) x \<in> top1_S2 - {north_pole}"
          using hinv_eq[OF hx] hx by simp
      next
        fix V assume hV: "V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
        have "{x \<in> top1_S2 - {north_pole}. inv_into (top1_S2 - {north_pole}) (householder_S2 north_pole) x \<in> V}
            = V \<inter> (top1_S2 - {north_pole})"
          using hinv_eq by auto
        also have "\<dots> = V" using hV unfolding subspace_topology_def by (by100 blast)
        finally show "{x \<in> top1_S2 - {north_pole}. inv_into (top1_S2 - {north_pole}) (householder_S2 north_pole) x \<in> V}
            \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
          using hV by simp
      qed
    qed
  qed
next
  case False
  \<comment> \<open>Householder reflection: v = N - b, R(p) = p - 2(v\<cdot>p)/(v\<cdot>v)*v.\<close>
  obtain b1 b2 b3 where hb_eq: "b = (b1, b2, b3)" by (cases b, cases "snd b") auto
  have hb_S2: "b1^2 + b2^2 + b3^2 = 1" using assms unfolding hb_eq top1_S2_def by simp
  have hb3_ne1: "b3 \<noteq> 1"
  proof
    assume "b3 = 1"
    hence "b1^2 + b2^2 = 0" using hb_S2 by simp
    hence "b1 = 0" "b2 = 0" by (simp_all add: sum_power2_eq_zero_iff)
    hence "b = north_pole" unfolding hb_eq north_pole_def using \<open>b3 = 1\<close> by simp
    thus False using False by simp
  qed
  \<comment> \<open>v\<cdot>v = 2 - 2*b3, which is > 0 since b3 < 1.\<close>
  have hvv: "b1^2 + b2^2 + (1-b3)^2 = 2 - 2*b3"
    using hb_S2 by (simp add: power2_eq_square algebra_simps)
  have hvv_ne: "2 - 2*b3 \<noteq> (0::real)" using hb3_ne1 by linarith
  \<comment> \<open>Define R on R^3. R is linear, hence continuous.\<close>
  define R where "R = householder_S2 b"
  have R_expand: "R = (\<lambda>(x::real,y::real,z::real).
    let vdp = -b1*x + (-b2)*y + (1-b3)*z;
        c = 2*vdp/(2 - 2*b3)
    in (x - c*(-b1), y - c*(-b2), z - c*(1-b3)))"
    unfolding R_def householder_S2_def hb_eq using False
    unfolding north_pole_def by simp
  \<comment> \<open>R maps S^2 to S^2 (isometry), R(b) = N, R is its own inverse.\<close>
  have hb12: "b1*b1 + b2*b2 = 1 - b3*b3"
    using hb_S2 by (simp add: power2_eq_square algebra_simps)
  have hR_b_N: "R b = north_pole"
  proof -
    let ?vdp = "-b1*b1 + (-b2)*b2 + (1-b3)*b3"
    have hvdp_val: "?vdp = b3 - 1" using hb_S2
      by (simp add: power2_eq_square algebra_simps)
    have hc_m1: "2*(b3-1)/(2-2*b3) = -(1::real)"
      apply (subst divide_eq_eq)
      apply (simp add: hvv_ne algebra_simps)
      apply (rule hb3_ne1)
      done
    let ?c = "2*?vdp/(2-2*b3)"
    have hc_val: "?c = -(1::real)"
      using hvdp_val hc_m1 by simp
    have "R b = (b1 - ?c*(-b1), b2 - ?c*(-b2), b3 - ?c*(1-b3))"
      unfolding R_expand hb_eq Let_def by simp
    also have "\<dots> = (b1 - (-1)*(-b1), b2 - (-1)*(-b2), b3 - (-1)*(1-b3))"
      using hc_val by simp
    also have "\<dots> = (0::real, 0, 1)" by simp
    finally show ?thesis unfolding north_pole_def .
  qed
  have hR_S2: "\<And>p. p \<in> top1_S2 \<Longrightarrow> R p \<in> top1_S2"
  proof -
    fix p assume hp: "p \<in> top1_S2"
    obtain x y z :: real where hxyz: "p = (x, y, z)" by (cases p, cases "snd p") auto
    have hp_S2: "x^2 + y^2 + z^2 = 1" using hp unfolding hxyz top1_S2_def by simp
    define vdp where "vdp = -b1*x + (-b2)*y + (1-b3)*z"
    define d where "d = (2-2*b3::real)"
    define c where "c = 2*vdp/d"
    have hd_ne: "d \<noteq> 0" unfolding d_def using hb3_ne1 by linarith
    have hvv_d: "b1^2+b2^2+(1-b3)^2 = d" unfolding d_def
      using hb_S2 by (simp add: power2_eq_square algebra_simps)
    have hcd: "c * d = 2*vdp" unfolding c_def using hd_ne by simp
    have hcancel: "c^2*d = 2*c*vdp"
    proof -
      have "c * (c * d) = c * (2*vdp)" using hcd by simp
      thus ?thesis by (simp add: power2_eq_square algebra_simps)
    qed
    have h_expand: "(x - c*(-b1))^2 + (y - c*(-b2))^2 + (z - c*(1-b3))^2
        = (x^2 + y^2 + z^2) + c^2*(b1^2+b2^2+(1-b3)^2) + 2*c*(b1*x+b2*y-(1-b3)*z)"
      by (simp add: power2_eq_square algebra_simps)
    have hvdp_neg: "b1*x+b2*y-(1-b3)*z = -vdp" unfolding vdp_def by (simp add: algebra_simps)
    have "(x - c*(-b1))^2 + (y - c*(-b2))^2 + (z - c*(1-b3))^2
        = (x^2+y^2+z^2) + c^2*d - 2*c*vdp" using h_expand hvv_d hvdp_neg by simp
    hence hiso: "(x - c*(-b1))^2 + (y - c*(-b2))^2 + (z - c*(1-b3))^2
        = (x^2+y^2+z^2)" using hcancel by linarith
    have hRp_eq: "R p = (x - c*(-b1), y - c*(-b2), z - c*(1-b3))"
    proof -
      have "R (x,y,z) = (let vdp' = -b1*x+(-b2)*y+(1-b3)*z; c' = 2*vdp'/(2-2*b3)
                         in (x-c'*(-b1), y-c'*(-b2), z-c'*(1-b3)))"
        unfolding R_expand by simp
      also have "\<dots> = (x - (2*vdp/d)*(-b1), y - (2*vdp/d)*(-b2), z - (2*vdp/d)*(1-b3))"
        unfolding Let_def vdp_def d_def by simp
      finally show ?thesis unfolding hxyz c_def .
    qed
    hence "fst (R p)^2 + fst(snd(R p))^2 + snd(snd(R p))^2 = 1"
      using hiso hp_S2 by simp
    thus "R p \<in> top1_S2" unfolding top1_S2_def by (cases "R p", cases "snd(R p)") auto
  qed
  have hR_inv: "\<And>p. R (R p) = p"
  proof -
    fix p obtain x y z :: real where hxyz: "p = (x, y, z)" by (cases p, cases "snd p") auto
    define vdp where "vdp = -b1*x + (-b2)*y + (1-b3)*z"
    define d where "d = (2-2*b3::real)"
    define c where "c = 2*vdp/d"
    have hd_ne: "d \<noteq> 0" unfolding d_def using hb3_ne1 by linarith
    have hvv_d: "b1^2+b2^2+(1-b3)^2 = d" unfolding d_def
      using hb_S2 by (simp add: power2_eq_square algebra_simps)
    have hcd: "c * d = 2*vdp" unfolding c_def using hd_ne by simp
    let ?x' = "x-c*(-b1)" and ?y' = "y-c*(-b2)" and ?z' = "z-c*(1-b3)"
    have hRp_eq: "R p = (?x', ?y', ?z')"
    proof -
      have "R (x,y,z) = (let v = -b1*x+(-b2)*y+(1-b3)*z; cc = 2*v/(2-2*b3)
                         in (x-cc*(-b1), y-cc*(-b2), z-cc*(1-b3)))"
        unfolding R_expand by simp
      also have "\<dots> = (x-(2*vdp/d)*(-b1), y-(2*vdp/d)*(-b2), z-(2*vdp/d)*(1-b3))"
        unfolding Let_def vdp_def d_def by simp
      finally show ?thesis unfolding hxyz c_def .
    qed
    define vdp' where "vdp' = -b1*?x' + (-b2)*?y' + (1-b3)*?z'"
    have "vdp' = vdp - c*(b1^2+b2^2+(1-b3)^2)"
      unfolding vdp'_def vdp_def by (simp add: power2_eq_square algebra_simps)
    hence "vdp' = vdp - c*d" using hvv_d by simp
    hence hvdp'_val: "vdp' = -vdp" using hcd by linarith
    define c' where "c' = 2*vdp'/d"
    have hc'_val: "c' = -c"
      unfolding c'_def c_def using hvdp'_val by simp
    have "R (R p) = (?x'-c'*(-b1), ?y'-c'*(-b2), ?z'-c'*(1-b3))"
    proof -
      have "R (?x', ?y', ?z') = (let v = -b1*?x'+(-b2)*?y'+(1-b3)*?z'; cc = 2*v/(2-2*b3)
                                 in (?x'-cc*(-b1), ?y'-cc*(-b2), ?z'-cc*(1-b3)))"
        unfolding R_expand by simp
      also have "\<dots> = (?x'-(2*vdp'/d)*(-b1), ?y'-(2*vdp'/d)*(-b2), ?z'-(2*vdp'/d)*(1-b3))"
        unfolding Let_def vdp'_def d_def by simp
      also have "\<dots> = (?x'-c'*(-b1), ?y'-c'*(-b2), ?z'-c'*(1-b3))"
        unfolding c'_def by simp
      finally show ?thesis using hRp_eq by simp
    qed
    also have "\<dots> = (x, y, z)" using hc'_val by simp
    finally show "R (R p) = p" unfolding hxyz .
  qed
  have hR_cont: "continuous_on UNIV R"
  proof -
    define vf :: "real \<times> real \<times> real \<Rightarrow> real" where
      "vf = (\<lambda>p. -b1*fst p + (-b2)*fst(snd p) + (1-b3)*snd(snd p))"
    define d where "d = (2-2*b3::real)"
    have hd_ne: "d \<noteq> 0" unfolding d_def using hb3_ne1 by linarith
    have hvf_cont: "continuous_on UNIV vf" unfolding vf_def by (intro continuous_intros)
    define R' :: "real \<times> real \<times> real \<Rightarrow> real \<times> real \<times> real" where
      "R' = (\<lambda>p. (fst p + 2*vf p/d*b1, fst(snd p) + 2*vf p/d*b2,
                  snd(snd p) - 2*vf p/d*(1-b3)))"
    have hR_eq: "R = R'" unfolding R_expand R'_def vf_def d_def Let_def
      by (rule ext) (simp add: case_prod_unfold)
    have "continuous_on UNIV R'" unfolding R'_def
      by (intro continuous_intros hvf_cont) (simp_all add: hd_ne)
    thus ?thesis using hR_eq by simp
  qed
  \<comment> \<open>R restricts to homeomorphism S^2 \<rightarrow> S^2.\<close>
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
  have hR_bij: "bij_betw R top1_S2 top1_S2"
    unfolding bij_betw_def
  proof (intro conjI)
    show "inj_on R top1_S2"
      by (rule inj_onI) (metis hR_inv)
    show "R ` top1_S2 = top1_S2"
    proof (rule set_eqI, rule iffI)
      fix q assume "q \<in> R ` top1_S2"
      then obtain p where "p \<in> top1_S2" "q = R p" by blast
      thus "q \<in> top1_S2" using hR_S2 by simp
    next
      fix q assume hq: "q \<in> top1_S2"
      hence "R q \<in> top1_S2" by (rule hR_S2)
      moreover have "R (R q) = q" by (rule hR_inv)
      ultimately show "q \<in> R ` top1_S2" by (metis image_eqI)
    qed
  qed
  have hR_inv_eq: "\<And>p. p \<in> top1_S2 \<Longrightarrow> inv_into top1_S2 R p = R p"
  proof -
    fix p assume hp: "p \<in> top1_S2"
    have "R p \<in> top1_S2" by (rule hR_S2[OF hp])
    moreover have "R (R p) = p" by (rule hR_inv)
    ultimately show "inv_into top1_S2 R p = R p"
      using hR_bij unfolding bij_betw_def by (intro inv_into_f_eq) auto
  qed
  \<comment> \<open>Bridge: continuous_on UNIV R \<Rightarrow> top1_continuous_map_on S^2 TS2 S^2 TS2 R.\<close>
  have hR_top1_cont: "top1_continuous_map_on top1_S2 top1_S2_topology top1_S2 top1_S2_topology R"
  proof -
    have hR_cont_S2: "continuous_on top1_S2 R"
      using continuous_on_subset[OF hR_cont] by (by100 blast)
    show ?thesis unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix p assume "p \<in> top1_S2" thus "R p \<in> top1_S2" by (rule hR_S2)
    next
      fix V assume hV: "V \<in> top1_S2_topology"
      then obtain W where hW: "W \<in> product_topology_on top1_open_sets
            (product_topology_on top1_open_sets top1_open_sets)"
          and hVeq: "V = top1_S2 \<inter> W"
        unfolding top1_S2_topology_def subspace_topology_def by (by100 blast)
      have "W \<in> (top1_open_sets :: (real \<times> real \<times> real) set set)"
        using hW product_topology_on_open_sets by metis
      hence hWopen: "open W" unfolding top1_open_sets_def by (by100 blast)
      obtain U where hUopen: "open U" and hUeq: "U \<inter> top1_S2 = R -` W \<inter> top1_S2"
        using iffD1[OF continuous_on_open_invariant hR_cont_S2] hWopen by auto
      have "{p \<in> top1_S2. R p \<in> V} = {p \<in> top1_S2. R p \<in> W}"
        unfolding hVeq using hR_S2 by (by100 auto)
      also have "\<dots> = R -` W \<inter> top1_S2" by (by100 auto)
      also have "\<dots> = U \<inter> top1_S2" using hUeq by simp
      finally have heq: "{p \<in> top1_S2. R p \<in> V} = top1_S2 \<inter> U" by (by100 blast)
      have "U \<in> (top1_open_sets :: (real \<times> real \<times> real) set set)"
        using hUopen unfolding top1_open_sets_def by (by100 blast)
      hence "U \<in> product_topology_on top1_open_sets
          (product_topology_on top1_open_sets top1_open_sets)"
        using product_topology_on_open_sets by metis
      hence "top1_S2 \<inter> U \<in> top1_S2_topology"
        unfolding top1_S2_topology_def subspace_topology_def by (by100 blast)
      thus "{p \<in> top1_S2. R p \<in> V} \<in> top1_S2_topology" using heq by simp
    qed
  qed
  have hR_homeo: "top1_homeomorphism_on top1_S2 top1_S2_topology top1_S2 top1_S2_topology R"
    unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on top1_S2 top1_S2_topology" by (rule hTS2)
    show "is_topology_on top1_S2 top1_S2_topology" by (rule hTS2)
    show "bij_betw R top1_S2 top1_S2" by (rule hR_bij)
    show "top1_continuous_map_on top1_S2 top1_S2_topology top1_S2 top1_S2_topology R"
      by (rule hR_top1_cont)
    show "top1_continuous_map_on top1_S2 top1_S2_topology top1_S2 top1_S2_topology (inv_into top1_S2 R)"
    proof -
      have "\<And>p. p \<in> top1_S2 \<Longrightarrow> inv_into top1_S2 R p = R p" by (rule hR_inv_eq)
      hence "\<And>V. V \<in> top1_S2_topology \<Longrightarrow>
          {p \<in> top1_S2. inv_into top1_S2 R p \<in> V} = {p \<in> top1_S2. R p \<in> V}"
        by auto
      thus ?thesis using hR_top1_cont hR_S2 hR_inv_eq
        unfolding top1_continuous_map_on_def by auto
    qed
  qed
  have hR_homeo_minus: "top1_homeomorphism_on (top1_S2 - {b})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
      (top1_S2 - {north_pole})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) R"
    unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))"
      by (rule subspace_topology_is_topology_on[OF hTS2]) simp
    show "is_topology_on (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))"
      by (rule subspace_topology_is_topology_on[OF hTS2]) simp
    show hbij: "bij_betw R (top1_S2 - {b}) (top1_S2 - {north_pole})"
      unfolding bij_betw_def
    proof (intro conjI)
      show "inj_on R (top1_S2 - {b})"
        by (rule inj_onI) (metis hR_inv)
      show "R ` (top1_S2 - {b}) = top1_S2 - {north_pole}"
      proof (rule set_eqI, rule iffI)
        fix q assume "q \<in> R ` (top1_S2 - {b})"
        then obtain p where hp: "p \<in> top1_S2 - {b}" "q = R p" by blast
        have "q \<in> top1_S2" using hp hR_S2 by (by100 blast)
        moreover have "q \<noteq> north_pole"
        proof
          assume "q = north_pole"
          hence "R p = north_pole" using hp by simp
          hence "R (R p) = R north_pole" by simp
          hence "p = R north_pole" using hR_inv by simp
          hence "R p = R (R north_pole)" by simp
          hence "R p = north_pole" using hR_inv by simp
          hence "p = b" using hR_b_N hR_inv
            by (metis \<open>R p = north_pole\<close>)
          thus False using hp by simp
        qed
        ultimately show "q \<in> top1_S2 - {north_pole}" by simp
      next
        fix q assume hq: "q \<in> top1_S2 - {north_pole}"
        have "R q \<in> top1_S2" using hq hR_S2 by (by100 blast)
        moreover have "R q \<noteq> b"
        proof
          assume "R q = b"
          hence "R (R q) = R b" by simp
          hence "q = north_pole" using hR_inv hR_b_N by simp
          thus False using hq by simp
        qed
        ultimately have "R q \<in> top1_S2 - {b}" by simp
        moreover have "R (R q) = q" by (rule hR_inv)
        ultimately show "q \<in> R ` (top1_S2 - {b})" by (metis image_eqI)
      qed
    qed
    have hR_not_N: "\<And>p. p \<in> top1_S2 - {b} \<Longrightarrow> R p \<noteq> north_pole"
    proof -
      fix p assume hp: "p \<in> top1_S2 - {b}"
      show "R p \<noteq> north_pole"
      proof
        assume "R p = north_pole"
        hence "R p = R b" using hR_b_N by simp
        hence "p = b" by (metis hR_inv)
        thus False using hp by simp
      qed
    qed
    \<comment> \<open>Continuity: restrict hR_top1_cont to subspaces.\<close>
    show "top1_continuous_map_on (top1_S2 - {b})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
        (top1_S2 - {north_pole})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) R"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix p assume hp: "p \<in> top1_S2 - {b}"
      thus "R p \<in> top1_S2 - {north_pole}" using hbij unfolding bij_betw_def by (by100 blast)
    next
      fix V assume hV: "V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
      then obtain W where hW: "W \<in> top1_S2_topology" and hVeq: "V = (top1_S2 - {north_pole}) \<inter> W"
        unfolding subspace_topology_def by (by100 blast)
      have "{p \<in> top1_S2 - {b}. R p \<in> V} = (top1_S2 - {b}) \<inter> {p \<in> top1_S2. R p \<in> W}"
        unfolding hVeq using hR_S2 hR_not_N by (by100 auto)
      moreover have "{p \<in> top1_S2. R p \<in> W} \<in> top1_S2_topology"
        using hR_top1_cont hW unfolding top1_continuous_map_on_def by (by100 blast)
      ultimately show "{p \<in> top1_S2 - {b}. R p \<in> V} \<in>
          subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
        unfolding subspace_topology_def by (by100 blast)
    qed
    \<comment> \<open>Inverse continuity: inv_into = R (involution), same as forward.\<close>
    show "top1_continuous_map_on (top1_S2 - {north_pole})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
        (top1_S2 - {b})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
        (inv_into (top1_S2 - {b}) R)"
    proof -
      have hR_not_b: "\<And>p. p \<in> top1_S2 - {north_pole} \<Longrightarrow> R p \<noteq> b"
        by (metis DiffD2 hR_b_N hR_inv singletonI)
      have hinv_R: "\<And>p. p \<in> top1_S2 - {north_pole} \<Longrightarrow>
          inv_into (top1_S2 - {b}) R p = R p"
      proof -
        fix p assume hp: "p \<in> top1_S2 - {north_pole}"
        have "R p \<in> top1_S2 - {b}"
        proof -
          have "R p \<in> top1_S2" using hp hR_S2 by (by100 blast)
          moreover have "R p \<noteq> b"
          proof
            assume "R p = b"
            hence "R (R p) = R b" by simp
            hence "p = north_pole" using hR_inv hR_b_N by simp
            thus False using hp by simp
          qed
          ultimately show ?thesis by simp
        qed
        moreover have "R (R p) = p" by (rule hR_inv)
        ultimately show "inv_into (top1_S2 - {b}) R p = R p"
          using hbij unfolding bij_betw_def by (intro inv_into_f_eq) auto
      qed
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix p assume hp: "p \<in> top1_S2 - {north_pole}"
        show "inv_into (top1_S2 - {b}) R p \<in> top1_S2 - {b}"
          using hinv_R[OF hp] hp hR_S2 hR_not_b[OF hp] by auto
      next
        fix V assume hV: "V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
        then obtain W where hW: "W \<in> top1_S2_topology" and hVeq: "V = (top1_S2 - {b}) \<inter> W"
          unfolding subspace_topology_def by (by100 blast)
        have "{p \<in> top1_S2 - {north_pole}. inv_into (top1_S2 - {b}) R p \<in> V}
            = (top1_S2 - {north_pole}) \<inter> {p \<in> top1_S2. R p \<in> W}"
          unfolding hVeq using hinv_R hR_S2 hR_not_b by auto
        moreover have "{p \<in> top1_S2. R p \<in> W} \<in> top1_S2_topology"
          using hR_top1_cont hW unfolding top1_continuous_map_on_def by (by100 blast)
        ultimately show "{p \<in> top1_S2 - {north_pole}. inv_into (top1_S2 - {b}) R p \<in> V} \<in>
            subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
          unfolding subspace_topology_def by (by100 blast)
      qed
    qed
  qed
  show ?thesis using hR_homeo_minus unfolding R_def .
qed

lemma S2_minus_point_simply_connected:
  assumes "b \<in> top1_S2"
  shows "top1_simply_connected_on (top1_S2 - {b})
           (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))"
proof (cases "b = north_pole")
  case True thus ?thesis using S2_minus_north_pole_simply_connected by simp
next
  case False
  show ?thesis
    by (rule homeomorphism_preserves_simply_connected[OF
        householder_S2_homeo[OF assms] S2_minus_north_pole_simply_connected])
qed

text \<open>A simple closed curve in X: image of a continuous injective map S^1 \<rightarrow> X.
  (Moved before \<S>61 to avoid forward reference.)\<close>
definition top1_simple_closed_curve_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_simple_closed_curve_on X TX C \<longleftrightarrow>
     (\<exists>f. top1_continuous_map_on top1_S1 top1_S1_topology X TX f
          \<and> inj_on f top1_S1
          \<and> f ` top1_S1 = C)"

lemma simple_closed_curve_subset:
  "top1_simple_closed_curve_on X TX C \<Longrightarrow> C \<subseteq> X"
  unfolding top1_simple_closed_curve_on_def top1_continuous_map_on_def
  by (by100 blast)

text \<open>S^2 minus two distinct points is not simply connected (homeomorphic to R^2 - {0}).\<close>
lemma R2_minus_origin_not_simply_connected:
  "\<not> top1_simply_connected_on (UNIV - {(0::real, 0::real)})
     (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))"
proof
  assume hsc: "top1_simply_connected_on (UNIV - {(0::real, 0::real)})
     (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))"
  let ?TR2_0 = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0::real, 0::real)})"
  \<comment> \<open>Simply connected means all loops at (1,0) are contractible in R^2-{0}.\<close>
  have h10_R2: "(1::real, 0::real) \<in> UNIV - {(0, 0)}" by simp
  have h_all_trivial: "\<forall>f. top1_is_loop_on (UNIV - {(0::real, 0)}) ?TR2_0 (1, 0) f
      \<longrightarrow> top1_path_homotopic_on (UNIV - {(0, 0)}) ?TR2_0 (1, 0) (1, 0) f (top1_constant_path (1, 0))"
    using hsc h10_R2 unfolding top1_simply_connected_on_def by (by100 blast)
  \<comment> \<open>In particular, the standard loop p0(s) = (cos 2\<pi>s, sin 2\<pi>s) on S^1 \<subseteq> R^2-{0}
     is a loop at (1,0) in R^2-{0}. By simply connected, it's contractible.\<close>
  let ?p0 = "\<lambda>s::real. (cos (2 * pi * s), sin (2 * pi * s))"
  have hp0_loop_R2: "top1_is_loop_on (UNIV - {(0, 0)}) ?TR2_0 (1::real, 0::real) ?p0"
  proof -
    have hp0_R2: "\<forall>s\<in>I_set. ?p0 s \<in> UNIV - {(0::real, 0)}"
    proof
      fix s :: real assume "s \<in> I_set"
      have "cos (2 * pi * s) ^ 2 + sin (2 * pi * s) ^ 2 = 1"
        using sin_cos_squared_add[of "2 * pi * s"] by (simp add: power2_eq_square)
      hence "?p0 s \<noteq> (0, 0)"
      proof -
        assume h1: "cos (2 * pi * s) ^ 2 + sin (2 * pi * s) ^ 2 = 1"
        show ?thesis
        proof
          assume h0: "?p0 s = (0, 0)"
          hence "cos (2 * pi * s) = 0" "sin (2 * pi * s) = 0" by (simp_all add: prod_eq_iff)
          hence "cos (2 * pi * s) ^ 2 + sin (2 * pi * s) ^ 2 = 0" by simp
          thus False using h1 by simp
        qed
      qed
      thus "?p0 s \<in> UNIV - {(0, 0)}" by simp
    qed
    have hp0_cont: "continuous_on UNIV ?p0" by (intro continuous_intros)
    have hp0_cont_I: "continuous_on I_set ?p0"
      using continuous_on_subset[OF hp0_cont] by (by100 blast)
    have hp0_top1: "top1_continuous_map_on I_set I_top (UNIV - {(0::real, 0)}) ?TR2_0 ?p0"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> I_set" thus "?p0 s \<in> UNIV - {(0::real, 0)}" using hp0_R2 by (by100 blast)
    next
      fix V assume hV: "V \<in> ?TR2_0"
      then obtain W where hW: "W \<in> product_topology_on top1_open_sets top1_open_sets"
          and hVeq: "V = (UNIV - {(0, 0)}) \<inter> W"
        unfolding subspace_topology_def by (by100 auto)
      have hWo: "open W"
      proof -
        have "W \<in> (top1_open_sets :: (real \<times> real) set set)"
          using hW product_topology_on_open_sets_real2 by (by100 metis)
        thus ?thesis unfolding top1_open_sets_def by (by100 blast)
      qed
      have "{s \<in> I_set. ?p0 s \<in> V} = I_set \<inter> ?p0 -` W"
        unfolding hVeq using hp0_R2 by (by100 auto)
      moreover have "open (?p0 -` W)"
      proof -
        have "open (?p0 -` W \<inter> UNIV)"
          using iffD1[OF continuous_on_open_vimage[OF open_UNIV] hp0_cont] hWo by (by100 blast)
        thus ?thesis by simp
      qed
      hence "?p0 -` W \<in> top1_open_sets" unfolding top1_open_sets_def by (by100 blast)
      ultimately show "{s \<in> I_set. ?p0 s \<in> V} \<in> I_top"
        unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
    qed
    show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
      using hp0_top1 by simp
  qed
  have hp0_contractible: "top1_path_homotopic_on (UNIV - {(0, 0)}) ?TR2_0 (1, 0) (1, 0)
      ?p0 (top1_constant_path (1, 0))"
    using h_all_trivial hp0_loop_R2 by (by100 blast)
  \<comment> \<open>But p0 is also a loop on S^1 (since cos^2 + sin^2 = 1). Under the inclusion S^1 \<hookrightarrow> R^2-{0},
     p0 contractible in R^2-{0} implies p0 contractible in S^1 (by retraction r(x)=x/|x|).\<close>
  \<comment> \<open>Then π₁(S¹) would be trivial. But π₁(S¹) ≅ ℤ (Theorem_54_5). Contradiction.\<close>
  \<comment> \<open>Actually: use the retraction r(x) = x/|x| to transfer the homotopy to S^1.\<close>
  have hp0_contractible_S1: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
      ?p0 (top1_constant_path (1, 0))"
  proof -
    \<comment> \<open>Use retraction r(x) = x/|x| from R^2-{0} to S^1. r continuous, r|S^1 = id.
       hp0_contractible gives p0 ≃ const in R^2-{0}.
       Apply r: r∘p0 ≃ r∘const in S^1. r∘p0 = p0 (on S^1), r∘const = const.\<close>
    let ?norm = "\<lambda>x::real\<times>real. sqrt (fst x ^ 2 + snd x ^ 2)"
    let ?r = "\<lambda>x::real\<times>real. (fst x / ?norm x, snd x / ?norm x)"
    \<comment> \<open>r fixes S^1.\<close>
    have hr_fix: "\<And>x. x \<in> top1_S1 \<Longrightarrow> ?r x = x"
      unfolding top1_S1_def by auto
    \<comment> \<open>r maps R^2-{0} to S^1.\<close>
    have hr_S1: "\<And>x. x \<in> UNIV - {(0::real, 0)} \<Longrightarrow> ?r x \<in> top1_S1"
    proof -
      fix x :: "real \<times> real" assume hx: "x \<in> UNIV - {(0, 0)}"
      hence hx_ne: "fst x \<noteq> 0 \<or> snd x \<noteq> 0" by (auto simp: prod_eq_iff)
      hence hsum_pos: "fst x ^ 2 + snd x ^ 2 > 0"
        using sum_power2_gt_zero_iff[of "fst x" "snd x"] by blast
      hence hnorm_pos: "?norm x > 0" by simp
      have hns: "(?norm x) ^ 2 = fst x ^ 2 + snd x ^ 2"
      proof -
        have "(?norm x) ^ 2 = ?norm x * ?norm x" by (simp add: power2_eq_square)
        also have "\<dots> = \<bar>fst x ^ 2 + snd x ^ 2\<bar>" by (simp add: power2_eq_square real_sqrt_mult_self)
        also have "\<dots> = fst x ^ 2 + snd x ^ 2" using hsum_pos by simp
        finally show ?thesis .
      qed
      have hnorm_ne: "?norm x \<noteq> 0" using hnorm_pos by (by100 linarith)
      have "(fst x / ?norm x) ^ 2 + (snd x / ?norm x) ^ 2 = 1"
      proof -
        have hne: "fst x ^ 2 + snd x ^ 2 \<noteq> 0" using hsum_pos by (by100 linarith)
        have "fst x ^ 2 / (fst x ^ 2 + snd x ^ 2) + snd x ^ 2 / (fst x ^ 2 + snd x ^ 2) = 1"
          using hne by (simp add: add_divide_distrib[symmetric])
        thus ?thesis using hns by (simp add: power_divide)
      qed
      thus "?r x \<in> top1_S1" unfolding top1_S1_def by simp
    qed
    \<comment> \<open>r is continuous R^2-{0} \<rightarrow> S^1.\<close>
    have hr_cont: "top1_continuous_map_on (UNIV - {(0, 0)}) ?TR2_0
        top1_S1 top1_S1_topology ?r"
    proof -
      \<comment> \<open>r is continuous_on (UNIV - {(0,0)}) as a composition of continuous functions.\<close>
      have hr_cont_on: "continuous_on (UNIV - {(0::real, 0)}) ?r"
      proof (intro continuous_on_Pair)
        show "continuous_on (UNIV - {(0::real, 0)}) (\<lambda>x. fst x / ?norm x)"
          by (intro continuous_intros) (auto simp: sum_power2_eq_zero_iff prod_eq_iff)
        show "continuous_on (UNIV - {(0::real, 0)}) (\<lambda>x. snd x / ?norm x)"
          by (intro continuous_intros) (auto simp: sum_power2_eq_zero_iff prod_eq_iff)
      qed
      \<comment> \<open>Transfer to top1_continuous_map_on via open_vimage.\<close>
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix x :: "real \<times> real" assume hx: "x \<in> UNIV - {(0, 0)}"
        show "?r x \<in> top1_S1" using hr_S1[OF hx] .
      next
        fix V assume hV: "V \<in> top1_S1_topology"
        then obtain W where hW: "W \<in> product_topology_on top1_open_sets top1_open_sets"
            and hVeq: "V = top1_S1 \<inter> W"
          unfolding top1_S1_topology_def subspace_topology_def by (by100 auto)
        have hWo: "open W"
        proof -
          have "W \<in> (top1_open_sets :: (real \<times> real) set set)"
            using hW product_topology_on_open_sets_real2 by (by100 metis)
          thus ?thesis unfolding top1_open_sets_def by (by100 blast)
        qed
        have hR2_open: "open (UNIV - {(0::real, 0::real)})"
          by (intro open_Diff open_UNIV finite_imp_closed) simp
        have hpre: "open (?r -` W \<inter> (UNIV - {(0, 0)}))"
          using iffD1[OF continuous_on_open_vimage[OF hR2_open] hr_cont_on] hWo by (by100 blast)
        have "{x \<in> UNIV - {(0, 0)}. ?r x \<in> V} = (UNIV - {(0, 0)}) \<inter> (?r -` W)"
          unfolding hVeq using hr_S1 by (by100 auto)
        also have "\<dots> = ?r -` W \<inter> (UNIV - {(0, 0)})" by (by100 blast)
        finally have "{x \<in> UNIV - {(0, 0)}. ?r x \<in> V} = ?r -` W \<inter> (UNIV - {(0, 0)})" .
        hence hopen: "open {x \<in> UNIV - {(0, 0)}. ?r x \<in> V}" using hpre by simp
        hence hopen_os: "{x \<in> UNIV - {(0, 0)}. ?r x \<in> V} \<in> top1_open_sets"
          unfolding top1_open_sets_def by (by100 blast)
        have hsub: "{x \<in> UNIV - {(0, 0)}. ?r x \<in> V} \<subseteq> UNIV - {(0, 0)}" by (by100 blast)
        have hprod: "(product_topology_on top1_open_sets top1_open_sets :: (real \<times> real) set set)
            = top1_open_sets" using product_topology_on_open_sets_real2 by simp
        show "{x \<in> UNIV - {(0, 0)}. ?r x \<in> V} \<in> ?TR2_0"
          unfolding subspace_topology_def hprod
          using hopen_os hsub by (by100 blast)
      qed
    qed
    \<comment> \<open>Apply r to the homotopy: r∘p0 ≃ r∘const.\<close>
    have hpsi_hom: "top1_path_homotopic_on top1_S1 top1_S1_topology
        (?r (1, 0)) (?r (1, 0)) (?r \<circ> ?p0) (?r \<circ> top1_constant_path (1, 0))"
    proof -
      have hTR2_0: "is_topology_on (UNIV - {(0::real, 0)}) ?TR2_0"
        by (rule subspace_topology_is_topology_on[OF
              product_topology_on_is_topology_on[OF
                top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV, simplified]]) simp
      have hTS1_local: "is_topology_on top1_S1 top1_S1_topology"
        unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF
              product_topology_on_is_topology_on[OF
                top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
                simplified]]) simp
      show ?thesis
        by (rule continuous_preserves_path_homotopic[OF hTR2_0 hTS1_local hr_cont hp0_contractible])
    qed
    \<comment> \<open>r(1,0) = (1,0), r∘p0 = p0 (on S^1), r∘const = const.\<close>
    have hr10: "?r (1, 0) = (1, 0)" by simp
    have hr_p0: "?r \<circ> ?p0 = ?p0"
    proof (rule ext)
      fix s :: real
      show "(?r \<circ> ?p0) s = ?p0 s"
      proof -
        have "cos (2 * pi * s) ^ 2 + sin (2 * pi * s) ^ 2 = 1"
          using sin_cos_squared_add[of "2 * pi * s"] by (simp add: power2_eq_square)
        hence "?p0 s \<in> top1_S1" unfolding top1_S1_def by simp
        thus ?thesis using hr_fix by (simp add: comp_def)
      qed
    qed
    have hr_const: "?r \<circ> top1_constant_path (1, 0) = top1_constant_path (1, 0)"
      by (rule ext) (simp add: top1_constant_path_def comp_def)
    show ?thesis using hpsi_hom unfolding hr10 hr_p0 hr_const .
  qed
  \<comment> \<open>p0 is the standard generator of π₁(S¹). Its contractibility gives π₁(S¹) = 0.\<close>
  \<comment> \<open>But π₁(S¹) ≅ ℤ ≠ 0 (Theorem 54.5). Actually we can derive False more directly:
     the n-fold winding (p0 for n=1) being contractible contradicts the covering theory
     argument from FTA Step 2 (hnontrivial).\<close>
  \<comment> \<open>Use Theorem_54_3: lift of p0 from 0 ends at 1. Lift of const ends at 0.
     If they're homotopic, endpoints equal by Thm 54.3. So 1=0. Contradiction.\<close>
  \<comment> \<open>Transfer p0 contractibility from S^1 to the covering R \<rightarrow> S^1.
     Lift of p0: s \<mapsto> s, ending at 1.
     Lift of const: s \<mapsto> 0, ending at 0.
     By Thm 54.3, if p0 ≃ const then 1 = 0. Contradiction.\<close>
  have hcov: "top1_covering_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
    by (rule Theorem_53_1)
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
    unfolding top1_S1_topology_def
    by (rule subspace_topology_is_topology_on[OF
          product_topology_on_is_topology_on[OF
            top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
            simplified]]) simp
  have hp0: "top1_R_to_S1 0 = (1, 0)" unfolding top1_R_to_S1_def by simp
  have h0R: "(0::real) \<in> (UNIV::real set)" by simp
  have h10S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
  \<comment> \<open>p0 as a loop on S^1: ?p0(s) = (cos 2\<pi>s, sin 2\<pi>s) = top1_R_to_S1(s).\<close>
  have hp0_eq: "\<And>s. ?p0 s = top1_R_to_S1 s"
    unfolding top1_R_to_S1_def by simp
  \<comment> \<open>p0 = R_to_S1 \<circ> id. Lift of p0 from 0 is id: s \<mapsto> s, ending at 1.\<close>
  have hp0_loop_S1: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) ?p0"
  proof -
    \<comment> \<open>?p0 maps into S^1 and is continuous. Same proof as hp0_loop_R2 but for S^1 codomain.\<close>
    have hp0_S1: "\<forall>s\<in>I_set. ?p0 s \<in> top1_S1"
      unfolding top1_S1_def
    proof
      fix s :: real assume "s \<in> I_set"
      have "cos (2 * pi * s) ^ 2 + sin (2 * pi * s) ^ 2 = 1"
        using sin_cos_squared_add[of "2 * pi * s"] by (simp add: power2_eq_square)
      thus "?p0 s \<in> {p. fst p ^ 2 + snd p ^ 2 = 1}" by simp
    qed
    have hp0_cont: "continuous_on UNIV ?p0" by (intro continuous_intros)
    have hp0_top1: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology ?p0"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> I_set" thus "?p0 s \<in> top1_S1" using hp0_S1 by (by100 blast)
    next
      fix V assume hV: "V \<in> top1_S1_topology"
      then obtain W where hW: "W \<in> product_topology_on top1_open_sets top1_open_sets"
          and hVeq: "V = top1_S1 \<inter> W"
        using hV unfolding top1_S1_topology_def subspace_topology_def by (by100 auto)
      have hWo: "open W"
      proof -
        have "W \<in> (top1_open_sets :: (real \<times> real) set set)"
          using hW product_topology_on_open_sets_real2 by (by100 metis)
        thus ?thesis unfolding top1_open_sets_def by (by100 blast)
      qed
      have "{s \<in> I_set. ?p0 s \<in> V} = I_set \<inter> ?p0 -` W"
        unfolding hVeq using hp0_S1 by (by100 auto)
      moreover have "open (?p0 -` W)"
      proof -
        have "open (?p0 -` W \<inter> UNIV)"
          using iffD1[OF continuous_on_open_vimage[OF open_UNIV] hp0_cont] hWo by (by100 blast)
        thus ?thesis by simp
      qed
      hence "?p0 -` W \<in> top1_open_sets" unfolding top1_open_sets_def by (by100 blast)
      ultimately show "{s \<in> I_set. ?p0 s \<in> V} \<in> I_top"
        unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
    qed
    show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
      using hp0_top1 by simp
  qed
  \<comment> \<open>If p0 ≃ const on S^1, then by Thm 54.3, lift endpoints agree: 1 = 0.\<close>
  have hft_p0: "top1_is_path_on UNIV top1_open_sets 0 1 id"
  proof -
    have hid_cont: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets id"
      unfolding top1_continuous_map_on_def top1_unit_interval_topology_def
    proof (intro conjI ballI)
      fix s :: real assume "s \<in> I_set" show "id s \<in> (UNIV::real set)" by simp
    next
      fix V :: "real set" assume "V \<in> top1_open_sets"
      have "{s \<in> I_set. id s \<in> V} = I_set \<inter> V" by auto
      also have "\<dots> \<in> subspace_topology UNIV top1_open_sets I_set"
        unfolding subspace_topology_def using \<open>V \<in> top1_open_sets\<close> by (by100 blast)
      finally show "{s \<in> I_set. id s \<in> V} \<in> subspace_topology UNIV top1_open_sets I_set" .
    qed
    show ?thesis unfolding top1_is_path_on_def using hid_cont by simp
  qed
  have hft_p0_lift: "\<forall>s\<in>I_set. top1_R_to_S1 (id s) = ?p0 s"
    using hp0_eq by simp
  have hft_const: "top1_is_path_on UNIV top1_open_sets 0 0 (\<lambda>_. 0::real)"
    unfolding top1_is_path_on_def
    using top1_continuous_map_on_const[OF top1_unit_interval_topology_is_topology_on
      top1_open_sets_is_topology_on_UNIV UNIV_I] by simp
  have hft_const_lift: "\<forall>s\<in>I_set. top1_R_to_S1 ((\<lambda>_. 0::real) s) = top1_constant_path (1, 0) s"
    unfolding top1_constant_path_def top1_R_to_S1_def by simp
  have hconst_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) (top1_constant_path (1, 0))"
    using top1_constant_path_is_loop[OF hTS1 h10S1] unfolding top1_is_loop_on_def .
  have hp0_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) ?p0"
    using hp0_loop_S1 unfolding top1_is_loop_on_def .
  have "1 = (0::real)"
    using conjunct1[OF Theorem_54_3[OF hcov top1_open_sets_is_topology_on_UNIV hTS1
      h0R hp0 hp0_path hconst_path hp0_contractible_S1
      hft_p0 hft_p0_lift hft_const hft_const_lift]] .
  thus False by simp
qed

lemma R2_minus_point_not_simply_connected:
  "p \<in> (UNIV :: (real \<times> real) set) \<Longrightarrow>
   \<not> top1_simply_connected_on (UNIV - {p})
     (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {p}))"
proof -
  assume "p \<in> (UNIV :: (real \<times> real) set)"
  \<comment> \<open>Translation \<tau>(x) = x - p is a homeomorphism R^2-{p} \<rightarrow> R^2-{0}.
     Simply connected is a homotopy invariant.
     R^2-{0} is not simply connected (proved above).\<close>
  \<comment> \<open>The translation \<tau> and its inverse \<tau>^{-1}(x) = x + p are both continuous
     (as polynomial maps on R^2) and bijective UNIV-{p} \<leftrightarrow> UNIV-{0}.\<close>
  show ?thesis
  proof
    assume hsc: "top1_simply_connected_on (UNIV - {p})
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {p}))"
    \<comment> \<open>Translate loop around p to loop around origin.\<close>
    let ?\<tau> = "\<lambda>x::real\<times>real. (fst x - fst p, snd x - snd p)"
    \<comment> \<open>The standard loop p0 around origin, shifted to go around p.\<close>
    let ?\<gamma> = "\<lambda>s::real. (fst p + cos (2 * pi * s), snd p + sin (2 * pi * s))"
    let ?b = "(fst p + 1, snd p)"
    have hb: "?b \<in> UNIV - {p}" by (cases p) auto
    \<comment> \<open>\<gamma> maps I_set into UNIV-{p}.\<close>
    have h\<gamma>_in: "\<forall>s\<in>I_set. ?\<gamma> s \<in> UNIV - {p}"
    proof
      fix s :: real assume "s \<in> I_set"
      have "?\<gamma> s \<noteq> p"
      proof
        assume h0: "?\<gamma> s = p"
        have hc: "cos (2 * pi * s) = 0" using h0 by (cases p) auto
        have hs: "sin (2 * pi * s) = 0" using h0 by (cases p) auto
        show False using sin_cos_squared_add3[of "2 * pi * s"] hc hs by simp
      qed
      thus "?\<gamma> s \<in> UNIV - {p}" by simp
    qed
    \<comment> \<open>\<tau>\<circ>\<gamma>(s) = (cos 2\<pi>s, sin 2\<pi>s) = p0.\<close>
    have h\<tau>\<gamma>_eq: "\<And>s. ?\<tau> (?\<gamma> s) = (cos (2 * pi * s), sin (2 * pi * s))" by simp
    \<comment> \<open>\<tau> is continuous UNIV-{p} \<rightarrow> UNIV-{0}.\<close>
    let ?Tp = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {p})"
    let ?T0 = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0::real, 0::real)})"
    have h\<tau>_cont: "top1_continuous_map_on (UNIV - {p}) ?Tp (UNIV - {(0::real, 0)}) ?T0 ?\<tau>"
    proof -
      have h\<tau>_map: "\<And>x. x \<in> UNIV - {p} \<Longrightarrow> ?\<tau> x \<in> UNIV - {(0, 0)}"
        by (cases p) auto
      have h\<tau>_cont_univ: "continuous_on (UNIV - {p}) ?\<tau>"
        by (intro continuous_intros continuous_on_subset[OF _ subset_UNIV])
      show ?thesis
        by (rule top1_continuous_map_on_real2_subspace_general[OF h\<tau>_map h\<tau>_cont_univ])
    qed
    \<comment> \<open>\<gamma> is a loop at ?b in UNIV-{p}.\<close>
    have h\<gamma>_loop: "top1_is_loop_on (UNIV - {p}) ?Tp ?b ?\<gamma>"
    proof -
      have h\<gamma>_cont_univ: "continuous_on UNIV ?\<gamma>" by (intro continuous_intros)
      have h\<gamma>_cont_I: "continuous_on I_set ?\<gamma>"
        using continuous_on_subset[OF h\<gamma>_cont_univ] by (by100 blast)
      have h\<gamma>_cont_top1: "top1_continuous_map_on I_set I_top (UNIV - {p}) ?Tp ?\<gamma>"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix s assume hs: "s \<in> I_set" thus "?\<gamma> s \<in> UNIV - {p}" using h\<gamma>_in by simp
      next
        fix V assume hV: "V \<in> ?Tp"
        then obtain W where hWo: "W \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
            and hVeq: "V = (UNIV - {p}) \<inter> W"
          unfolding subspace_topology_def by (by100 blast)
        have "W \<in> (top1_open_sets :: (real \<times> real) set set)"
          using hWo product_topology_on_open_sets_real2 by metis
        hence hWopen: "open W" unfolding top1_open_sets_def by (by100 blast)
        have hpre: "open (?\<gamma> -` W)"
          by (rule open_vimage[OF hWopen h\<gamma>_cont_univ])
        have hpre_os: "?\<gamma> -` W \<in> (top1_open_sets :: real set set)"
          using hpre unfolding top1_open_sets_def by (by100 blast)
        have "{s \<in> I_set. ?\<gamma> s \<in> V} = I_set \<inter> (?\<gamma> -` W)"
          unfolding hVeq using h\<gamma>_in by (by100 blast)
        thus "{s \<in> I_set. ?\<gamma> s \<in> V} \<in> I_top"
          unfolding top1_unit_interval_topology_def subspace_topology_def
          using hpre_os by (by100 blast)
      qed
      have h0: "?\<gamma> 0 = ?b" by simp
      have h1: "?\<gamma> 1 = ?b" by simp
      show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
        using h\<gamma>_cont_top1 h0 h1 by (by100 blast)
    qed
    \<comment> \<open>Simply connected \<Rightarrow> \<gamma> is contractible.\<close>
    have h\<gamma>_contract: "top1_path_homotopic_on (UNIV - {p}) ?Tp ?b ?b ?\<gamma> (top1_constant_path ?b)"
      using hsc hb h\<gamma>_loop unfolding top1_simply_connected_on_def by (by100 blast)
    \<comment> \<open>Apply \<tau>: \<tau>\<circ>\<gamma> contractible in UNIV-{0}.\<close>
    have hTR2: "is_topology_on (UNIV::(real\<times>real) set)
        (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
    proof -
      have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
        by (rule top1_open_sets_is_topology_on_UNIV)
      show ?thesis using product_topology_on_is_topology_on[OF hTR hTR] by simp
    qed
    have hTp: "is_topology_on (UNIV - {p}) ?Tp"
      by (rule subspace_topology_is_topology_on[OF hTR2]) simp
    have hT0: "is_topology_on (UNIV - {(0::real, 0)}) ?T0"
      by (rule subspace_topology_is_topology_on[OF hTR2]) simp
    have h\<tau>\<gamma>_contract: "top1_path_homotopic_on (UNIV - {(0, 0)}) ?T0
        (?\<tau> ?b) (?\<tau> ?b) (?\<tau> \<circ> ?\<gamma>) (top1_constant_path (?\<tau> ?b))"
    proof -
      have hstep: "top1_path_homotopic_on (UNIV - {(0, 0)}) ?T0
          (?\<tau> ?b) (?\<tau> ?b) (?\<tau> \<circ> ?\<gamma>) (?\<tau> \<circ> top1_constant_path ?b)"
        by (rule continuous_preserves_path_homotopic[OF hTp hT0 h\<tau>_cont h\<gamma>_contract])
      have "?\<tau> \<circ> top1_constant_path ?b = top1_constant_path (?\<tau> ?b)"
        unfolding top1_constant_path_def by (rule ext) simp
      thus ?thesis using hstep by simp
    qed
    \<comment> \<open>\<tau> ?b = (1, 0) and \<tau>\<circ>\<gamma> = p0.\<close>
    have h\<tau>b: "?\<tau> ?b = (1::real, 0::real)" by simp
    have h\<tau>\<gamma>_p0: "?\<tau> \<circ> ?\<gamma> = (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s)))"
      by (rule ext) simp
    \<comment> \<open>So p0 is contractible in UNIV-{0} at (1,0).\<close>
    have hp0_contract: "top1_path_homotopic_on (UNIV - {(0, 0)}) ?T0
        (1, 0) (1, 0) (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) (top1_constant_path (1, 0))"
      using h\<tau>\<gamma>_contract h\<tau>b h\<tau>\<gamma>_p0 by simp
    \<comment> \<open>But R^2-{0} is not simply connected: p0 is NOT contractible.\<close>
    \<comment> \<open>Transfer: UNIV-{p} simply connected \<Rightarrow> UNIV-{0} simply connected (via \<tau> and \<tau>^{-1}).\<close>
    have hsc0: "top1_simply_connected_on (UNIV - {(0::real, 0)}) ?T0"
    proof -
      let ?\<tau>inv = "\<lambda>x::real\<times>real. (fst x + fst p, snd x + snd p)"
      have h\<tau>inv_cont: "top1_continuous_map_on (UNIV - {(0, 0)}) ?T0 (UNIV - {p}) ?Tp ?\<tau>inv"
      proof -
        have hmap: "\<And>x. x \<in> UNIV - {(0::real, 0)} \<Longrightarrow> ?\<tau>inv x \<in> UNIV - {p}"
          by (cases p) auto
        have hcont: "continuous_on (UNIV - {(0::real, 0)}) ?\<tau>inv"
          by (intro continuous_intros continuous_on_subset[OF _ subset_UNIV])
        show ?thesis
          by (rule top1_continuous_map_on_real2_subspace_general[OF hmap hcont])
      qed
      show ?thesis unfolding top1_simply_connected_on_def
      proof (intro conjI allI impI ballI)
        \<comment> \<open>Path-connected: for y1, y2 in UNIV-{0}, translate to UNIV-{p},
           find path there (path-connected), translate back.\<close>
        show "top1_path_connected_on (UNIV - {(0::real, 0)}) ?T0"
          unfolding top1_path_connected_on_def
        proof (intro conjI ballI)
          show "is_topology_on (UNIV - {(0::real, 0::real)}) ?T0" by (rule hT0)
        next
          fix y1 y2 :: "real \<times> real"
          assume hy1: "y1 \<in> UNIV - {(0, 0)}" and hy2: "y2 \<in> UNIV - {(0, 0)}"
          \<comment> \<open>Translate to UNIV-{p}, find path, translate back.\<close>
          have "?\<tau>inv y1 \<in> UNIV - {p}" "?\<tau>inv y2 \<in> UNIV - {p}"
          proof -
            { fix y :: "real \<times> real" assume hy: "y \<in> UNIV - {(0::real, 0)}"
              have "?\<tau>inv y \<noteq> p"
              proof
                assume "?\<tau>inv y = p"
                hence "y = (0::real, 0)" by (cases y, cases p) simp
                thus False using hy by simp
              qed
              hence "?\<tau>inv y \<in> UNIV - {p}" by simp }
            thus "?\<tau>inv y1 \<in> UNIV - {p}" "?\<tau>inv y2 \<in> UNIV - {p}"
              using hy1 hy2 by auto
          qed
          then obtain \<alpha> where h\<alpha>: "top1_is_path_on (UNIV - {p}) ?Tp (?\<tau>inv y1) (?\<tau>inv y2) \<alpha>"
            using hsc unfolding top1_simply_connected_on_def top1_path_connected_on_def by (by100 blast)
          have h\<tau>\<alpha>: "top1_is_path_on (UNIV - {(0, 0)}) ?T0 (?\<tau> (?\<tau>inv y1)) (?\<tau> (?\<tau>inv y2)) (?\<tau> \<circ> \<alpha>)"
          proof -
            have h\<alpha>_cont: "top1_continuous_map_on I_set I_top (UNIV - {p}) ?Tp \<alpha>"
              using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
            have h\<tau>\<alpha>_cont: "top1_continuous_map_on I_set I_top (UNIV - {(0, 0)}) ?T0 (?\<tau> \<circ> \<alpha>)"
              by (rule top1_continuous_map_on_comp[OF h\<alpha>_cont h\<tau>_cont])
            have "(\<alpha> 0) = ?\<tau>inv y1" using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
            hence h0: "(?\<tau> \<circ> \<alpha>) 0 = ?\<tau> (?\<tau>inv y1)" by simp
            have "(\<alpha> 1) = ?\<tau>inv y2" using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
            hence h1: "(?\<tau> \<circ> \<alpha>) 1 = ?\<tau> (?\<tau>inv y2)" by simp
            show ?thesis unfolding top1_is_path_on_def
              using h\<tau>\<alpha>_cont h0 h1 by (by100 blast)
          qed
          have "?\<tau> (?\<tau>inv y1) = y1" "?\<tau> (?\<tau>inv y2) = y2" by simp_all
          thus "\<exists>f. top1_is_path_on (UNIV - {(0, 0)}) ?T0 y1 y2 f"
            using h\<tau>\<alpha> by (intro exI[of _ "?\<tau> \<circ> \<alpha>"]) simp
        qed
      next
        \<comment> \<open>All loops contractible: loop in UNIV-{0}, translate to UNIV-{p},
           contract (simply connected), translate back.\<close>
        fix y0 :: "real \<times> real" and g
        assume hy0: "y0 \<in> UNIV - {(0::real, 0)}"
        assume hg: "top1_is_loop_on (UNIV - {(0, 0)}) ?T0 y0 g"
        \<comment> \<open>Translate: \<tau>inv\<circ>g is a loop at \<tau>inv(y0) in UNIV-{p}.\<close>
        have h\<tau>inv_y0: "?\<tau>inv y0 \<in> UNIV - {p}"
        proof -
          have "?\<tau>inv y0 \<noteq> p"
          proof
            assume heq: "?\<tau>inv y0 = p"
            have h1: "fst y0 = 0" using heq by (cases p, cases y0) simp
            have h2: "snd y0 = 0" using heq by (cases p, cases y0) simp
            have "y0 = (0::real, 0::real)" using h1 h2 by (cases y0) simp
            thus False using hy0 by simp
          qed
          thus ?thesis by simp
        qed
        have h\<tau>inv_g: "top1_is_loop_on (UNIV - {p}) ?Tp (?\<tau>inv y0) (?\<tau>inv \<circ> g)"
          using top1_continuous_map_loop_early[OF h\<tau>inv_cont hg] by simp
        \<comment> \<open>Contract in UNIV-{p}.\<close>
        have hg_contract: "top1_path_homotopic_on (UNIV - {p}) ?Tp
            (?\<tau>inv y0) (?\<tau>inv y0) (?\<tau>inv \<circ> g) (top1_constant_path (?\<tau>inv y0))"
          using hsc h\<tau>inv_y0 h\<tau>inv_g unfolding top1_simply_connected_on_def by (by100 blast)
        \<comment> \<open>Translate back via \<tau>.\<close>
        have h\<tau>_contract: "top1_path_homotopic_on (UNIV - {(0, 0)}) ?T0
            (?\<tau> (?\<tau>inv y0)) (?\<tau> (?\<tau>inv y0))
            (?\<tau> \<circ> (?\<tau>inv \<circ> g)) (?\<tau> \<circ> top1_constant_path (?\<tau>inv y0))"
          by (rule continuous_preserves_path_homotopic[OF hTp hT0 h\<tau>_cont hg_contract])
        have h\<tau>\<tau>inv_y0: "?\<tau> (?\<tau>inv y0) = y0" by simp
        have h\<tau>\<tau>inv_g: "?\<tau> \<circ> (?\<tau>inv \<circ> g) = g" by (rule ext) simp
        have h\<tau>_const: "?\<tau> \<circ> top1_constant_path (?\<tau>inv y0) = top1_constant_path y0"
          unfolding top1_constant_path_def by (rule ext) simp
        show "top1_path_homotopic_on (UNIV - {(0, 0)}) ?T0 y0 y0 g (top1_constant_path y0)"
          using h\<tau>_contract h\<tau>\<tau>inv_y0 h\<tau>\<tau>inv_g h\<tau>_const by simp
      qed
    qed
    show False using R2_minus_origin_not_simply_connected hsc0 by (by100 blast)
  qed
qed

lemma homeomorphism_comp:
  assumes "top1_homeomorphism_on X TX Y TY f"
      and "top1_homeomorphism_on Y TY Z TZ g"
  shows "top1_homeomorphism_on X TX Z TZ (g \<circ> f)"
proof -
  have hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY" and hTZ: "is_topology_on Z TZ"
      and hfbij: "bij_betw f X Y" and hgbij: "bij_betw g Y Z"
      and hf: "top1_continuous_map_on X TX Y TY f"
      and hfinv: "top1_continuous_map_on Y TY X TX (inv_into X f)"
      and hg: "top1_continuous_map_on Y TY Z TZ g"
      and hginv: "top1_continuous_map_on Z TZ Y TY (inv_into Y g)"
    using assms unfolding top1_homeomorphism_on_def by (by100 blast)+
  have hgfbij: "bij_betw (g \<circ> f) X Z" using hfbij hgbij by (rule bij_betw_trans)
  show ?thesis unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on X TX" by (rule hTX)
    show "is_topology_on Z TZ" by (rule hTZ)
    show "bij_betw (g \<circ> f) X Z" by (rule hgfbij)
    show "top1_continuous_map_on X TX Z TZ (g \<circ> f)"
      by (rule top1_continuous_map_on_comp[OF hf hg])
    show "top1_continuous_map_on Z TZ X TX (inv_into X (g \<circ> f))"
    proof -
      have hinv_comp: "\<And>z. z \<in> Z \<Longrightarrow> inv_into X (g \<circ> f) z = (inv_into X f \<circ> inv_into Y g) z"
      proof -
        fix z assume hz: "z \<in> Z"
        have hgy: "inv_into Y g z \<in> Y"
          using hz hgbij unfolding bij_betw_def by (simp add: inv_into_into)
        have hfx: "inv_into X f (inv_into Y g z) \<in> X"
          using hgy hfbij unfolding bij_betw_def by (simp add: inv_into_into)
        have "g (f (inv_into X f (inv_into Y g z))) = g (inv_into Y g z)"
          using hgy hfbij unfolding bij_betw_def by (simp add: f_inv_into_f)
        also have "\<dots> = z"
          using hz hgbij unfolding bij_betw_def by (simp add: f_inv_into_f)
        finally have "(g \<circ> f) (inv_into X f (inv_into Y g z)) = z" by simp
        thus "inv_into X (g \<circ> f) z = (inv_into X f \<circ> inv_into Y g) z"
          using hfx hgfbij unfolding bij_betw_def
          by (intro inv_into_f_eq[OF bij_betw_imp_inj_on[OF hgfbij]]) auto
      qed
      have hinv_cont: "top1_continuous_map_on Z TZ X TX (inv_into X f \<circ> inv_into Y g)"
        by (rule top1_continuous_map_on_comp[OF hginv hfinv])
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix z assume hz: "z \<in> Z"
        show "inv_into X (g \<circ> f) z \<in> X"
          using hinv_comp[OF hz] hinv_cont hz
          unfolding top1_continuous_map_on_def by (by100 auto)
      next
        fix V assume hV: "V \<in> TX"
        have "{z \<in> Z. inv_into X (g \<circ> f) z \<in> V} = {z \<in> Z. (inv_into X f \<circ> inv_into Y g) z \<in> V}"
        proof (rule Collect_cong)
          fix z show "(z \<in> Z \<and> inv_into X (g \<circ> f) z \<in> V) = (z \<in> Z \<and> (inv_into X f \<circ> inv_into Y g) z \<in> V)"
            using hinv_comp by (cases "z \<in> Z") simp_all
        qed
        also have "\<dots> \<in> TZ" using hinv_cont hV unfolding top1_continuous_map_on_def by (by100 blast)
        finally show "{z \<in> Z. inv_into X (g \<circ> f) z \<in> V} \<in> TZ" .
      qed
    qed
  qed
qed

lemma S2_minus_point_homeo_R2:
  assumes "a \<in> top1_S2"
  shows "\<exists>h. top1_homeomorphism_on (top1_S2 - {a})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))
      (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets) h"
proof (cases "a = north_pole")
  case True
  thus ?thesis using stereographic_proj_homeomorphism by auto
next
  case False
  \<comment> \<open>Compose: householder sends S^2-{a} \<rightarrow> S^2-{N}, stereographic sends S^2-{N} \<rightarrow> R^2.\<close>
  have hR: "top1_homeomorphism_on (top1_S2 - {a})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))
      (top1_S2 - {north_pole})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
      (householder_S2 a)"
    by (rule householder_S2_homeo[OF assms])
  \<comment> \<open>Compose with stereographic: stereographic_proj \<circ> householder_S2 a.\<close>
  have "top1_homeomorphism_on (top1_S2 - {a})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))
      (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets)
      (stereographic_proj \<circ> householder_S2 a)"
    by (rule homeomorphism_comp[OF hR stereographic_proj_homeomorphism])
  thus ?thesis by (by100 blast)
qed

lemma homeomorphism_inverse:
  assumes "top1_homeomorphism_on X TX Y TY h"
  shows "top1_homeomorphism_on Y TY X TX (inv_into X h)"
proof -
  have hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hbij: "bij_betw h X Y"
      and hh: "top1_continuous_map_on X TX Y TY h"
      and hg: "top1_continuous_map_on Y TY X TX (inv_into X h)"
    using assms unfolding top1_homeomorphism_on_def by (by100 blast)+
  have hgbij: "bij_betw (inv_into X h) Y X" using hbij by (rule bij_betw_inv_into)
  have hinv_inv: "\<And>x. x \<in> X \<Longrightarrow> inv_into Y (inv_into X h) x = h x"
  proof -
    fix x assume hx: "x \<in> X"
    have "h x \<in> Y" using hx hbij unfolding bij_betw_def by auto
    moreover have "inv_into X h (h x) = x"
      using hx hbij unfolding bij_betw_def by (simp add: inv_into_f_f)
    ultimately show "inv_into Y (inv_into X h) x = h x"
      by (intro inv_into_f_eq[OF bij_betw_imp_inj_on[OF hgbij]]) auto
  qed
  show ?thesis unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on Y TY" by (rule hTY)
    show "is_topology_on X TX" by (rule hTX)
    show "bij_betw (inv_into X h) Y X" by (rule hgbij)
    show "top1_continuous_map_on Y TY X TX (inv_into X h)" by (rule hg)
    show "top1_continuous_map_on X TX Y TY (inv_into Y (inv_into X h))"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x assume hx: "x \<in> X"
      show "inv_into Y (inv_into X h) x \<in> Y" using hinv_inv[OF hx] hx hbij
        unfolding bij_betw_def by auto
    next
      fix V assume hV: "V \<in> TY"
      have "{x \<in> X. h x \<in> V} \<in> TX"
        using hh hV unfolding top1_continuous_map_on_def by (by100 blast)
      moreover have "{x \<in> X. inv_into Y (inv_into X h) x \<in> V} = {x \<in> X. h x \<in> V}"
        (is "?L = ?R")
      proof
        show "?L \<subseteq> ?R" using hinv_inv by auto
        show "?R \<subseteq> ?L" using hinv_inv by auto
      qed
      ultimately show "{x \<in> X. inv_into Y (inv_into X h) x \<in> V} \<in> TX" by simp
    qed
  qed
qed

lemma homeomorphism_preserves_simply_connected_forward:
  assumes "top1_homeomorphism_on X TX Y TY h"
      and "top1_simply_connected_on X TX"
  shows "top1_simply_connected_on Y TY"
  by (rule homeomorphism_preserves_simply_connected[OF homeomorphism_inverse[OF assms(1)] assms(2)])

lemma homeomorphism_reflects_simply_connected:
  assumes "top1_homeomorphism_on X TX Y TY h"
      and "\<not> top1_simply_connected_on X TX"
  shows "\<not> top1_simply_connected_on Y TY"
  using homeomorphism_preserves_simply_connected[OF assms(1)] assms(2) by blast

lemma homeomorphism_restrict_point:
  assumes hhom: "top1_homeomorphism_on X TX Y TY h" and hp: "p \<in> X"
  shows "top1_homeomorphism_on (X - {p}) (subspace_topology X TX (X - {p}))
             (Y - {h p}) (subspace_topology Y TY (Y - {h p})) h"
proof -
  have hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hbij: "bij_betw h X Y"
      and hh: "top1_continuous_map_on X TX Y TY h"
      and hg: "top1_continuous_map_on Y TY X TX (inv_into X h)"
    using hhom unfolding top1_homeomorphism_on_def by (by100 blast)+
  have hinj: "inj_on h X" using hbij unfolding bij_betw_def by simp
  have hmap: "\<And>x. x \<in> X \<Longrightarrow> h x \<in> Y" using hbij unfolding bij_betw_def by auto
  show ?thesis unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on (X-{p}) (subspace_topology X TX (X-{p}))"
      by (rule subspace_topology_is_topology_on[OF hTX]) simp
    show "is_topology_on (Y-{h p}) (subspace_topology Y TY (Y-{h p}))"
      by (rule subspace_topology_is_topology_on[OF hTY]) simp
    show "bij_betw h (X-{p}) (Y-{h p})"
      unfolding bij_betw_def
    proof (intro conjI)
      show "inj_on h (X-{p})" using hinj by (rule inj_on_subset) blast
      show "h ` (X-{p}) = Y-{h p}"
      proof (rule set_eqI, rule iffI)
        fix y assume "y \<in> h ` (X-{p})"
        then obtain x where hx: "x \<in> X-{p}" "y = h x" by blast
        show "y \<in> Y-{h p}" using hx hmap hinj hp
          by (metis DiffD1 DiffD2 DiffI inj_onD singletonD singletonI)
      next
        fix y assume hy: "y \<in> Y-{h p}"
        then obtain x where hx: "x \<in> X" "h x = y"
          using hbij unfolding bij_betw_def by auto
        have "x \<noteq> p" using hx hy by auto
        thus "y \<in> h ` (X-{p})" using hx by auto
      qed
    qed
    show "top1_continuous_map_on (X-{p}) (subspace_topology X TX (X-{p}))
        (Y-{h p}) (subspace_topology Y TY (Y-{h p})) h"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x assume hx: "x \<in> X-{p}"
      thus "h x \<in> Y-{h p}" using hmap hinj hp by (simp add: inj_on_eq_iff)
    next
      fix V assume hV: "V \<in> subspace_topology Y TY (Y-{h p})"
      then obtain W where hW: "W \<in> TY" and hVeq: "V = (Y-{h p}) \<inter> W"
        unfolding subspace_topology_def by (by100 blast)
      have "{x \<in> X-{p}. h x \<in> V} = (X-{p}) \<inter> {x \<in> X. h x \<in> W}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {x \<in> X-{p}. h x \<in> V}"
        thus "x \<in> (X-{p}) \<inter> {x \<in> X. h x \<in> W}" unfolding hVeq by (by100 blast)
      next
        fix x assume hx: "x \<in> (X-{p}) \<inter> {x \<in> X. h x \<in> W}"
        have "h x \<in> Y-{h p}" using hx hmap hinj hp by (simp add: inj_on_eq_iff)
        thus "x \<in> {x \<in> X-{p}. h x \<in> V}" unfolding hVeq using hx by (by100 blast)
      qed
      moreover have "{x \<in> X. h x \<in> W} \<in> TX"
        using hh hW unfolding top1_continuous_map_on_def by (by100 blast)
      ultimately show "{x \<in> X-{p}. h x \<in> V} \<in> subspace_topology X TX (X-{p})"
        unfolding subspace_topology_def by (by100 blast)
    qed
    show "top1_continuous_map_on (Y-{h p}) (subspace_topology Y TY (Y-{h p}))
        (X-{p}) (subspace_topology X TX (X-{p})) (inv_into (X-{p}) h)"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix y assume hy: "y \<in> Y-{h p}"
      have "inv_into X h y \<in> X" using hy hbij unfolding bij_betw_def by (simp add: inv_into_into)
      moreover have "inv_into X h y \<noteq> p"
      proof
        assume "inv_into X h y = p"
        hence "h (inv_into X h y) = h p" by simp
        hence "y = h p" using hy hbij unfolding bij_betw_def by (simp add: f_inv_into_f)
        thus False using hy by simp
      qed
      ultimately have "inv_into X h y \<in> X-{p}" by simp
      moreover have "inv_into (X-{p}) h y = inv_into X h y"
      proof (rule inv_into_f_eq[OF inj_on_subset[OF hinj]])
        show "X - {p} \<subseteq> X" by blast
        show "inv_into X h y \<in> X - {p}" by (rule \<open>inv_into X h y \<in> X - {p}\<close>)
        show "h (inv_into X h y) = y" using hy hbij unfolding bij_betw_def by (simp add: f_inv_into_f)
      qed
      ultimately show "inv_into (X-{p}) h y \<in> X-{p}" by simp
    next
      fix V assume hV: "V \<in> subspace_topology X TX (X-{p})"
      then obtain W where hW: "W \<in> TX" and hVeq: "V = (X-{p}) \<inter> W"
        unfolding subspace_topology_def by (by100 blast)
      have hinv_agree: "\<And>y. y \<in> Y-{h p} \<Longrightarrow> inv_into (X-{p}) h y = inv_into X h y"
      proof -
        fix y assume hy: "y \<in> Y-{h p}"
        have h1: "inv_into X h y \<in> X" using hy hbij unfolding bij_betw_def by (simp add: inv_into_into)
        have h2: "inv_into X h y \<noteq> p"
        proof
          assume "inv_into X h y = p"
          hence "y = h p" using hy hbij unfolding bij_betw_def by (metis f_inv_into_f DiffD1)
          thus False using hy by simp
        qed
        show "inv_into (X-{p}) h y = inv_into X h y"
          by (rule inv_into_f_eq[OF inj_on_subset[OF hinj]])
             (use h1 h2 hy hbij in \<open>auto simp: bij_betw_def f_inv_into_f\<close>)
      qed
      have "\<And>y. y \<in> Y - {h p} \<Longrightarrow> inv_into X h y \<in> X - {p}"
      proof -
        fix y assume hy: "y \<in> Y - {h p}"
        have "inv_into X h y \<in> X" using hy hbij unfolding bij_betw_def by (simp add: inv_into_into)
        moreover have "inv_into X h y \<noteq> p"
          using hy hbij unfolding bij_betw_def by (metis DiffD1 DiffD2 f_inv_into_f singletonI)
        ultimately show "inv_into X h y \<in> X - {p}" by simp
      qed
      have "{y \<in> Y-{h p}. inv_into (X-{p}) h y \<in> V}
          = (Y-{h p}) \<inter> {y \<in> Y. inv_into X h y \<in> W}"
        unfolding hVeq using hinv_agree \<open>\<And>y. y \<in> Y - {h p} \<Longrightarrow> inv_into X h y \<in> X - {p}\<close>
        by auto
      moreover have "{y \<in> Y. inv_into X h y \<in> W} \<in> TY"
        using hg hW unfolding top1_continuous_map_on_def by (by100 blast)
      ultimately show "{y \<in> Y-{h p}. inv_into (X-{p}) h y \<in> V} \<in>
          subspace_topology Y TY (Y-{h p})"
        unfolding subspace_topology_def by (by100 blast)
    qed
  qed
qed

lemma S2_minus_two_points_not_simply_connected:
  assumes "a \<in> top1_S2" and "b \<in> top1_S2" and "a \<noteq> b"
  shows "\<not> top1_simply_connected_on (top1_S2 - {a, b})
           (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b}))"
  \<comment> \<open>S^2-{a,b} \<cong> R^2-{point} via Householder+stereographic. Not sc by R2_minus_point.\<close>
proof
  assume hsc: "top1_simply_connected_on (top1_S2 - {a, b})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b}))"
  \<comment> \<open>Step 1: S^2-{a} \<cong> R^2 via stereographic+Householder. Already proved for S2_minus_point_sc.\<close>
  \<comment> \<open>Step 2: Restrict to S^2-{a,b} \<cong> R^2-{point}.\<close>
  \<comment> \<open>We use the fact that S^2-{a} has a homeomorphism to R^2 (the composed map).
     Restricting by removing b from S^2-{a} removes h(b) from R^2.\<close>
  \<comment> \<open>By homeomorphism_preserves_sc applied twice, S^2-{a,b} sc \<Longrightarrow> R^2-{point} sc.\<close>
  \<comment> \<open>But R^2-{point} not sc. Contradiction.\<close>
  \<comment> \<open>For now: use S2_minus_point_sc to get that S^2-{a} ≅ R^2 (homeomorphism exists),
     then restrict.\<close>
  obtain h where hh: "top1_homeomorphism_on (top1_S2 - {a})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))
      (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets) h"
    using S2_minus_point_homeo_R2[OF assms(1)] by blast
  have hb_mem: "b \<in> top1_S2 - {a}" using assms by simp
  have hh_restrict: "top1_homeomorphism_on (top1_S2 - {a} - {b})
      (subspace_topology (top1_S2 - {a}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))
        (top1_S2 - {a} - {b}))
      (UNIV - {h b})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {h b})) h"
    by (rule homeomorphism_restrict_point[OF hh hb_mem])
  have hab_eq: "top1_S2 - {a} - {b} = top1_S2 - {a, b}" by (by100 blast)
  have hsub_eq: "subspace_topology (top1_S2 - {a}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))
      (top1_S2 - {a, b}) = subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b})"
    by (rule subspace_topology_trans) blast
  have hh_restrict': "top1_homeomorphism_on (top1_S2 - {a, b})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b}))
      (UNIV - {h b})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {h b})) h"
    using hh_restrict hab_eq hsub_eq by simp
  \<comment> \<open>Transfer: S^2-{a,b} sc \<Rightarrow> R^2-{h(b)} sc. Need h^{-1} homeomorphism direction.\<close>
  have hsc_R2: "top1_simply_connected_on (UNIV - {h b})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {h b}))"
    by (rule homeomorphism_preserves_simply_connected_forward[OF hh_restrict' hsc])
  have "h b \<in> (UNIV :: (real \<times> real) set)" by simp
  show False using R2_minus_point_not_simply_connected[OF \<open>h b \<in> UNIV\<close>] hsc_R2 by (by100 blast)
qed

text \<open>Any continuous map into S^2 - {b} is nulhomotopic (since S^2-{b} is contractible).\<close>
lemma map_into_S2_minus_point_nulhomotopic:
  assumes "b \<in> top1_S2"
      and "top1_continuous_map_on A TA
             (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) f"
  shows "top1_nulhomotopic_on A TA
           (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) f"
  \<comment> \<open>S^2-{b} \<cong> R^2 (contractible). Any map into a contractible space is nulhomotopic.
     Proof: compose f with homeomorphism h: S^2-{b} \<rightarrow> R^2, contract in R^2 via
     straight-line homotopy, compose back with h^{-1}.\<close>
  sorry

lemma Lemma_61_1_components_correspond:
  fixes h :: "(real \<times> real \<times> real) \<Rightarrow> (real \<times> real)" and C :: "(real \<times> real \<times> real) set"
    and b :: "real \<times> real \<times> real" and U :: "(real \<times> real \<times> real) set"
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "C \<subseteq> top1_S2"
      and "top1_compact_on C (subspace_topology top1_S2 top1_S2_topology C)"
      and "b \<in> top1_S2 - C"
      and "top1_homeomorphism_on (top1_S2 - {b})
             (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
             (UNIV::(real \<times> real) set)
             (product_topology_on top1_open_sets top1_open_sets) h"
      and "top1_connected_on U (subspace_topology top1_S2 top1_S2_topology U)"
      and "U \<subseteq> top1_S2 - C"
  shows "(b \<notin> U \<longrightarrow> (\<exists>M. \<forall>x\<in>U. fst (h x) ^ 2 + snd (h x) ^ 2 \<le> M))
       \<and> (b \<in> U \<longrightarrow> (\<forall>M. \<exists>x\<in>U - {b}. fst (h x) ^ 2 + snd (h x) ^ 2 > M))"
proof -
  \<comment> \<open>Munkres 61.1: h maps components of S^2-C to components of R^2-h(C).
     Step 1: h(C) is compact (continuous image of compact), hence bounded in R^2.
     Step 2: Components of S^2-C not containing b map to bounded components of R^2-h(C)
     (since h|_{S^2-b} is a homeomorphism, connected components correspond).
     Step 3: The component containing b maps to the complement of a bounded set,
     which is unbounded.\<close>
  have hC_compact: "top1_compact_on (h ` (C - {b}))
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (h ` (C - {b})))" sorry
  have hC_bounded: "\<exists>M. \<forall>p \<in> h ` (C - {b}). fst p ^ 2 + snd p ^ 2 \<le> M" sorry
  show ?thesis sorry
qed

(** from \<S>61 Lemma 61.2 (Nulhomotopy lemma): any continuous map from a compact
    space A into S^2 - b whose image factors through an arc is nulhomotopic. **)
lemma Lemma_61_2_nulhomotopy:
  fixes A :: "'a set" and TA :: "'a set set" and f :: "'a \<Rightarrow> real \<times> real \<times> real"
    and b :: "real \<times> real \<times> real"
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "top1_compact_on A TA"
      and "b \<in> top1_S2"
      and "top1_continuous_map_on A TA
             (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) f"
      and "\<exists>D. D \<subseteq> top1_S2 - {b} \<and> f ` A \<subseteq> D
            \<and> (\<exists>\<gamma>. top1_continuous_map_on I_set I_top D
                     (subspace_topology top1_S2 top1_S2_topology D) \<gamma>
                  \<and> inj_on \<gamma> I_set \<and> \<gamma> ` I_set = D)"
             \<comment> \<open>f factors through an arc D\<close>
  shows "top1_nulhomotopic_on A TA
           (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) f"
proof -
  \<comment> \<open>Munkres 61.2: f factors through an arc D \<subseteq> S^2-{b}.
     Step 1: An arc D is homeomorphic to [0,1], which is convex.
     Step 2: Any map into a convex set is nulhomotopic (straight-line homotopy).
     Step 3: S^2-{b} \<cong> R^2 (stereographic projection), so the nulhomotopy transfers.\<close>
  obtain D where hD: "D \<subseteq> top1_S2 - {b}" and hfD: "f ` A \<subseteq> D"
      and "\<exists>\<gamma>. inj_on \<gamma> I_set \<and> \<gamma> ` I_set = D"
    using assms(5) by (by100 auto)
  \<comment> \<open>D is contractible (homeomorphic to [0,1]).\<close>
  \<comment> \<open>S^2-{b} is contractible (homeomorphic to R^2), so any map into it is nulhomotopic.\<close>
  show ?thesis by (rule map_into_S2_minus_point_nulhomotopic[OF assms(3) assms(4)])
qed

(** from \<S>61 Theorem 61.3: Jordan separation theorem for S^2.

    Munkres' proof sketch:
    Suppose for contradiction S^2 - C is path connected.
    Write C = A_1 \<union> A_2 (arcs meeting at {a, b}).
    Let X = S^2 - {a, b}, U = S^2 - A_1, V = S^2 - A_2.
    Then X = U \<union> V and U \<inter> V = S^2 - C (path connected by assumption).
    By Theorem 59.1, \<pi>_1(X, x_0) is generated by images of i_*, j_*.
    Using Lemma 61.2 (nulhomotopy), both i_* and j_* are trivial.
    So \<pi>_1(X, x_0) is trivial. But X \<cong> R^2 - {0} has nontrivial \<pi>_1. \<bottom> **)
theorem Theorem_61_3_JordanSeparation_S2:
  assumes hT: "is_topology_on_strict top1_S2 top1_S2_topology"
  and hC: "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  shows "top1_separates_on top1_S2 top1_S2_topology C"
proof (rule ccontr)
  assume hnot: "\<not> top1_separates_on top1_S2 top1_S2_topology C"
  \<comment> \<open>Negation: S^2 - C is connected.\<close>
  have hS2_C_connected: "top1_connected_on (top1_S2 - C)
                           (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C))"
    using hnot unfolding top1_separates_on_def by blast
  \<comment> \<open>Decompose C = A_1 \<union> A_2 (two arcs) with common endpoints a, b.\<close>
  obtain A1 A2 a b where hC_decomp: "C = A1 \<union> A2"
      and hab: "A1 \<inter> A2 = {a, b}" and hab_ne: "a \<noteq> b"
      and hA1_arc: "top1_is_arc_on A1 (subspace_topology top1_S2 top1_S2_topology A1)"
      and hA2_arc: "top1_is_arc_on A2 (subspace_topology top1_S2 top1_S2_topology A2)"
    using hC sorry
  \<comment> \<open>Let X = S^2 - {a, b}, U = S^2 - A_1, V = S^2 - A_2.\<close>
  let ?X = "top1_S2 - {a, b}" and ?U = "top1_S2 - A1" and ?V = "top1_S2 - A2"
  \<comment> \<open>X = U \<union> V and U \<inter> V = S^2 - C (path-connected by hypothesis).\<close>
  have hX_UV: "?U \<union> ?V = ?X" using hC_decomp hab by blast
  have hUV_eq: "?U \<inter> ?V = top1_S2 - C" using hC_decomp hab by blast
  \<comment> \<open>U, V are open in X.\<close>
  have hU_open: "openin_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) ?U" sorry
  have hV_open: "openin_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) ?V" sorry
  \<comment> \<open>U \<inter> V = S^2 - C is path-connected (connected + locally path-connected).\<close>
  have hUV_pc: "top1_path_connected_on (?U \<inter> ?V)
      (subspace_topology ?X (subspace_topology top1_S2 top1_S2_topology ?X) (?U \<inter> ?V))" sorry
  obtain x0 where hx0: "x0 \<in> ?U \<inter> ?V" sorry
  \<comment> \<open>By Theorem 59.1, \<pi>_1(X, x_0) is generated by images of i_*, j_*.\<close>
  \<comment> \<open>By Lemma 61.2 (nulhomotopy), every loop in U factors through A2 (an arc),
     hence is nulhomotopic. Similarly for V. So i_*, j_* are trivial.\<close>
  have h_pi1_X_trivial: "top1_simply_connected_on ?X
      (subspace_topology top1_S2 top1_S2_topology ?X)" sorry
  \<comment> \<open>But X = S^2 - {a, b} \<cong> R^2 - {0} which has nontrivial \<pi>_1.\<close>
  have hC_sub: "C \<subseteq> top1_S2" by (rule simple_closed_curve_subset[OF hC])
  have ha_S2: "a \<in> top1_S2"
    using hab hC_decomp hC_sub by (by100 blast)
  have hb_S2: "b \<in> top1_S2"
    using hab hC_decomp hC_sub by (by100 blast)
  have h_pi1_X_nontrivial: "\<not> top1_simply_connected_on ?X
      (subspace_topology top1_S2 top1_S2_topology ?X)"
    by (rule S2_minus_two_points_not_simply_connected[OF ha_S2 hb_S2 hab_ne])
  show False using h_pi1_X_trivial h_pi1_X_nontrivial by contradiction
qed

(** from \<S>61 Theorem 61.4: general separation theorem for S^2 **)
theorem Theorem_61_4_general_separation:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "A1 \<subseteq> top1_S2" and "A2 \<subseteq> top1_S2"
  and "closedin_on top1_S2 top1_S2_topology A1"
  and "closedin_on top1_S2 top1_S2_topology A2"
  and "top1_connected_on A1 (subspace_topology top1_S2 top1_S2_topology A1)"
  and "top1_connected_on A2 (subspace_topology top1_S2 top1_S2_topology A2)"
  and "card (A1 \<inter> A2) = 2"
  shows "top1_separates_on top1_S2 top1_S2_topology (A1 \<union> A2)"
proof -
  \<comment> \<open>Munkres 61.4: Write C=A1\<union>A2 with A1\<inter>A2={a,b}.
     X = S^2-{a,b} \<cong> R^2-{0}, U = S^2-A1, V = S^2-A2. X=U\<union>V.\<close>
  obtain a b where hab: "A1 \<inter> A2 = {a, b}" and hab_ne: "a \<noteq> b"
    using assms(8) card_2_iff by (by100 metis)
  let ?X = "top1_S2 - {a, b}" and ?U = "top1_S2 - A1" and ?V = "top1_S2 - A2"
  \<comment> \<open>X = U \<union> V and U \<inter> V = S^2 - (A1 \<union> A2).\<close>
  have hX_UV: "?U \<union> ?V = ?X" using hab by (by100 blast)
  have hUV_eq: "?U \<inter> ?V = top1_S2 - (A1 \<union> A2)" by (by100 blast)
  \<comment> \<open>If S^2 - (A1\<union>A2) were connected, then U\<inter>V would be path-connected.\<close>
  \<comment> \<open>By Lemma 61.2, loops in U and V are nulhomotopic (they factor through arcs).\<close>
  \<comment> \<open>So \<pi>_1(X) would be trivial. But X \<cong> R^2-{0} has nontrivial \<pi>_1. Contradiction.\<close>
  \<comment> \<open>Hence S^2 - (A1 \<union> A2) is NOT connected.\<close>
  show ?thesis unfolding top1_separates_on_def sorry
qed

section \<open>*\<S>62 Invariance of Domain\<close>

text \<open>Invariance of domain in R^2: an open injective continuous map R^2 \<rightarrow> R^2
  has open image, and its invgerse is continuous.\<close>

(** from *\<S>62 Theorem 62.3: Invariance of Domain in R^2. **)
theorem Theorem_62_3_invgariance_of_domain:
  fixes U :: "(real \<times> real) set" and f :: "real \<times> real \<Rightarrow> real \<times> real"
  assumes "U \<in> product_topology_on top1_open_sets top1_open_sets"
      and "top1_continuous_map_on U
             (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) U)
             UNIV (product_topology_on top1_open_sets top1_open_sets) f"
      and "inj_on f U"
  shows "f ` U \<in> product_topology_on top1_open_sets top1_open_sets"
proof -
  \<comment> \<open>Munkres 62.3: For x\<in>U, show f(x)\<in>Int(f(U)).
     Step 1: Take a closed ball B centered at x with B \<subseteq> U.
     Step 2: f|B is injective continuous on compact B; f(Bd B) is a simple closed
     curve in R^2 (since Bd B \<cong> S^1 and f is injective on it).
     Step 3: By the Jordan Separation Theorem (61.3), f(Bd B) separates R^2.
     Step 4: f(x) is in the bounded component W of R^2 - f(Bd B).
     Step 5: W \<subseteq> f(Int B) \<subseteq> f(U), so f(x) \<in> Int(f(U)).\<close>
  have "\<forall>x\<in>U. \<exists>W. x \<in> W \<and> W \<in> product_topology_on top1_open_sets top1_open_sets \<and> W \<subseteq> f ` U"
  proof
    fix x assume hx: "x \<in> U"
    \<comment> \<open>Step 1: Take closed ball B with x \<in> Int(B) \<subseteq> B \<subseteq> U.\<close>
    obtain B where hBsub: "B \<subseteq> U"
        and hB_compact: "top1_compact_on B (subspace_topology UNIV
            (product_topology_on top1_open_sets top1_open_sets) B)"
        and hx_int: "x \<in> B - frontier B"
        and hBd_S1: "\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
            (frontier B) (subspace_topology UNIV
              (product_topology_on top1_open_sets top1_open_sets) (frontier B)) h"
      sorry
    \<comment> \<open>Step 2: f(Bd B) is a simple closed curve (f injective on compact Bd B \<cong> S^1).\<close>
    have hfBd_curve: "top1_simple_closed_curve_on UNIV
        (product_topology_on top1_open_sets top1_open_sets) (f ` frontier B)" sorry
    \<comment> \<open>Step 3: By Jordan Curve Theorem, f(Bd B) separates R^2 into two components.\<close>
    obtain W1 W2 where hW_disj: "W1 \<inter> W2 = {}" and hW_union: "W1 \<union> W2 = UNIV - f ` frontier B"
        and hW1_ne: "W1 \<noteq> {}" and hW2_ne: "W2 \<noteq> {}"
        and hW1_open: "W1 \<in> product_topology_on top1_open_sets top1_open_sets"
      sorry \<comment> \<open>By Jordan Curve Theorem (Theorem 63.4).\<close>
    \<comment> \<open>Step 4: f(x) is in the bounded component.\<close>
    have hfx_in_W: "f x \<in> W1" sorry
    \<comment> \<open>Step 5: W1 \<subseteq> f(Int B) \<subseteq> f(U).\<close>
    have hW1_sub: "W1 \<subseteq> f ` U" sorry
    show "\<exists>W. x \<in> W \<and> W \<in> product_topology_on top1_open_sets top1_open_sets \<and> W \<subseteq> f ` U"
      sorry
  qed
  show ?thesis sorry
qed

section \<open>\<S>63 The Jordan Curve Theorem\<close>

\<comment> \<open>top1_simple_closed_curve_on defined earlier (before \<S>61).\<close>

(** from \<S>63 Theorem 63.1: if X = U \<union> V with U \<inter> V = A \<union> B (disjoint open),
    and alpha: a to b in U, beta: b to a in V, then the loop f = alpha * beta is
    nontrivial in pi_1(X, a) (plus further properties: homotopy lifts, f^m and f^k
    are nonconjugate when the components are different). Used in Munkres' proof of
    the Jordan Curve Theorem. **)
theorem Theorem_63_1_loop_nontrivial:
  assumes "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "U \<inter> V = A \<union> B" and "A \<inter> B = {}"
      and "openin_on X TX A" and "openin_on X TX B"
      and "a \<in> A" and "b \<in> B"
      and "top1_is_path_on U (subspace_topology X TX U) a b alpha"
      and "top1_is_path_on V (subspace_topology X TX V) b a beta"
  shows "\<not> top1_path_homotopic_on X TX a a
           (top1_path_product alpha beta) (top1_constant_path a)"
proof
  assume hnul: "top1_path_homotopic_on X TX a a
      (top1_path_product alpha beta) (top1_constant_path a)"
  \<comment> \<open>Munkres 63.1: Construct covering space p: E \<rightarrow> X as infinite helix.
     E = ... \<sqcup> U_0 \<sqcup> V_0 \<sqcup> U_1 \<sqcup> V_1 \<sqcup> ... with A-sheets and B-sheets glued alternately.
     Concretely: E = Z \<times> (U \<sqcup> V), identifying (n, A-point in V_n) with (n, A-point in U_n)
     and (n, B-point in U_n) with (n+1, B-point in V_n).\<close>
  \<comment> \<open>Step 1: Build the covering space E and covering map p: E \<rightarrow> X.\<close>
  have "\<exists>(E::'a set) TE (p0::'a \<Rightarrow> 'a).
      top1_covering_map_on E TE X TX p0
    \<and> (\<exists>e0\<in>E. p0 e0 = a)" sorry
  \<comment> \<open>Step 2: Lift f = \<alpha>*\<beta> starting at e0 in the covering. The lift of \<alpha> goes from
     sheet n to the same sheet; the lift of \<beta> shifts from sheet n to sheet n+1.
     So the lifted path ends at a point in a DIFFERENT sheet than it started.\<close>
  have "\<exists>(E::'a set) TE (p0::'a \<Rightarrow> 'a) e0 e1.
      top1_covering_map_on E TE X TX p0
    \<and> e0 \<in> E \<and> p0 e0 = a
    \<and> e1 \<in> E \<and> p0 e1 = a
    \<and> e0 \<noteq> e1
    \<and> (\<exists>ftilde. top1_is_path_on E TE e0 e1 ftilde
        \<and> (\<forall>s\<in>I_set. p0 (ftilde s) = top1_path_product alpha beta s))" sorry
  \<comment> \<open>Step 3: If f were nulhomotopic, the lift would be a loop (same start and end).
     But we showed the lift has different endpoints. Contradiction.\<close>
  show False sorry
qed

(** from \<S>63 Theorem 63.2: an arc D in S^2 does not separate S^2.
    Munkres' proof: by contradiction + Theorem 63.1; use that \<pi>_1(S^2) is trivial. **)
theorem Theorem_63_2_arc_no_separation:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "D \<subseteq> top1_S2"
  and "top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D)"
  shows "\<not> top1_separates_on top1_S2 top1_S2_topology D"
proof (rule ccontr)
  assume hnot: "\<not> \<not> top1_separates_on top1_S2 top1_S2_topology D"
  hence hsep: "top1_separates_on top1_S2 top1_S2_topology D" by blast
  \<comment> \<open>Munkres 63.2: Split D=D1\<union>D2 at midpoint d.\<close>
  obtain d D1 D2 where hd: "d \<in> D" and hD: "D = D1 \<union> D2" and "D1 \<inter> D2 = {d}"
      and "top1_is_arc_on D1 (subspace_topology top1_S2 top1_S2_topology D1)"
      and "top1_is_arc_on D2 (subspace_topology top1_S2 top1_S2_topology D2)"
    sorry
  \<comment> \<open>Since D separates S^2, take a\<in>A, b\<in>B in different components of S^2-D.\<close>
  obtain a b where hab: "a \<in> top1_S2 - D" "b \<in> top1_S2 - D"
      and hab_sep: "\<not> (\<exists>f. top1_is_path_on (top1_S2 - D)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D)) a b f)"
    using hsep sorry
  \<comment> \<open>X=S^2-{d}, U=S^2-D1, V=S^2-D2. Apply Theorem 63.1.\<close>
  \<comment> \<open>Get nontrivial element of \<pi>_1(X). But X\<cong>R^2 has trivial \<pi>_1. Contradiction.\<close>
  have hd_S2: "d \<in> top1_S2" using hd assms(2) by (by100 blast)
  have h_pi1_trivial: "top1_simply_connected_on (top1_S2 - {d})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {d}))"
    by (rule S2_minus_point_simply_connected[OF hd_S2])
  have h_pi1_nontrivial: "\<not> top1_simply_connected_on (top1_S2 - {d})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {d}))" sorry
  show False using h_pi1_trivial h_pi1_nontrivial by contradiction
qed

(** from \<S>63 Theorem 63.3: general non-separation theorem. **)
theorem Theorem_63_3_general_nonseparation:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "closedin_on top1_S2 top1_S2_topology D1"
  and "closedin_on top1_S2 top1_S2_topology D2"
  and "top1_simply_connected_on (top1_S2 - (D1 \<inter> D2))
         (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<inter> D2)))"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology D1"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology D2"
  shows "\<not> top1_separates_on top1_S2 top1_S2_topology (D1 \<union> D2)"
proof (rule ccontr)
  assume hnot: "\<not> \<not> top1_separates_on top1_S2 top1_S2_topology (D1 \<union> D2)"
  hence hsep: "top1_separates_on top1_S2 top1_S2_topology (D1 \<union> D2)" by blast
  \<comment> \<open>Munkres 63.3: Take a\<in>A, b\<in>B in different components of S^2-(D1\<union>D2).\<close>
  obtain a b where "a \<in> top1_S2 - (D1 \<union> D2)" "b \<in> top1_S2 - (D1 \<union> D2)"
      and hab_sep: "\<not> (\<exists>f. top1_is_path_on (top1_S2 - (D1 \<union> D2))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<union> D2))) a b f)"
    using hsep sorry
  \<comment> \<open>Since D1 doesn't separate, join a to b in S^2-D1: path \<alpha>.\<close>
  obtain \<alpha> where "top1_is_path_on (top1_S2 - D1)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D1)) a b \<alpha>"
    using assms(5) sorry
  \<comment> \<open>Since D2 doesn't separate, join b to a in S^2-D2: path \<beta>.\<close>
  obtain \<beta> where "top1_is_path_on (top1_S2 - D2)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D2)) b a \<beta>"
    using assms(6) sorry
  \<comment> \<open>The loop f = \<alpha>*\<beta> lies in X=S^2-(D1\<inter>D2). By Theorem 63.1, [f] is nontrivial.\<close>
  have hf_nontrivial: "\<exists>f. top1_is_loop_on (top1_S2 - (D1 \<inter> D2))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<inter> D2))) a f
      \<and> \<not> top1_path_homotopic_on (top1_S2 - (D1 \<inter> D2))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<inter> D2))) a a f
          (top1_constant_path a)" sorry
  \<comment> \<open>But S^2-(D1\<inter>D2) is simply connected by assumption. Contradiction.\<close>
  have ha_mem: "a \<in> top1_S2 - (D1 \<inter> D2)"
    using \<open>a \<in> top1_S2 - (D1 \<union> D2)\<close> by (by100 blast)
  show False using hf_nontrivial assms(4) ha_mem
    unfolding top1_simply_connected_on_def by (by100 blast)
qed

(** from \<S>63 Theorem 63.4: Jordan Curve Theorem.

    Munkres' proof: use Theorem 61.3 (separation) + locally connected property +
    Theorem 63.1 argument to show at most 2 components. Each component has C as
    boundary by an auxiliary argument.

    NB: Currently stated for C \<subseteq> R^2 (as in the original formalization). **)
theorem Theorem_63_4_JordanCurve:
  fixes C :: "(real \<times> real) set"
  assumes "top1_simple_closed_curve_on
    UNIV (product_topology_on top1_open_sets top1_open_sets) C"
  shows "\<exists>U V. U \<noteq> {} \<and> V \<noteq> {}
    \<and> U \<inter> V = {} \<and> U \<union> V = UNIV - C
    \<and> top1_path_connected_on U
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) U)
    \<and> top1_path_connected_on V
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) V)
    \<comment> \<open>One component is bounded (interior), the other unbounded (exterior).\<close>
    \<and> (\<exists>M. \<forall>p\<in>U. fst p ^ 2 + snd p ^ 2 \<le> M)
    \<and> (\<forall>M. \<exists>p\<in>V. fst p ^ 2 + snd p ^ 2 > M)
    \<comment> \<open>Both components have C as boundary.\<close>
    \<and> closure U = U \<union> C
    \<and> closure V = V \<union> C"
proof -
  let ?TR2 = "product_topology_on top1_open_sets top1_open_sets"
  \<comment> \<open>Step 1 (Separation): Transfer to S^2 via stereographic projection. C corresponds
     to a simple closed curve on S^2. By Theorem 61.3, S^2 - C' has \<ge> 2 components.\<close>
  have hC_sep: "\<not> top1_connected_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))" sorry
  \<comment> \<open>Step 2 (Exactly two components): Decompose C = C_1 \<union> C_2 (two arcs with endpoints a, b).
     By Theorem 63.5 (applied via 63.2 + 63.3), exactly two components.\<close>
  obtain U V where hUV_ne: "U \<noteq> {}" "V \<noteq> {}" and hUV_disj: "U \<inter> V = {}"
      and hUV_cover: "U \<union> V = UNIV - C"
      and hU_conn: "top1_connected_on U (subspace_topology UNIV ?TR2 U)"
      and hV_conn: "top1_connected_on V (subspace_topology UNIV ?TR2 V)"
    sorry
  \<comment> \<open>Step 3 (Path-connected): R^2 is locally path-connected, so components are path-connected.\<close>
  have hU_pc: "top1_path_connected_on U (subspace_topology UNIV ?TR2 U)" sorry
  have hV_pc: "top1_path_connected_on V (subspace_topology UNIV ?TR2 V)" sorry
  \<comment> \<open>Step 4 (Bounded/unbounded): Under stereographic projection, one component maps to
     the bounded component and the other to the unbounded one (Lemma 61.1).\<close>
  have hU_bdd: "\<exists>M. \<forall>p\<in>U. fst p ^ 2 + snd p ^ 2 \<le> M" sorry
  have hV_unbdd: "\<forall>M. \<exists>p\<in>V. fst p ^ 2 + snd p ^ 2 > M" sorry
  \<comment> \<open>Step 5 (Boundary = C): Both components have C as their common boundary.\<close>
  have hU_bdy: "closure U = U \<union> C" sorry
  have hV_bdy: "closure V = V \<union> C" sorry
  show ?thesis using hUV_ne hUV_disj hUV_cover hU_pc hV_pc hU_bdd hV_unbdd hU_bdy hV_bdy
    by blast
qed

(** from \<S>63 Theorem 63.5: two closed-connected sets C1, C2 with |C1\<inter>C2|=2 and neither separates S^2 imply C1\<union>C2 separates into exactly two components. **)
theorem Theorem_63_5_two_closed_connected:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "closedin_on top1_S2 top1_S2_topology C1"
  and "closedin_on top1_S2 top1_S2_topology C2"
  and "top1_connected_on C1 (subspace_topology top1_S2 top1_S2_topology C1)"
  and "top1_connected_on C2 (subspace_topology top1_S2 top1_S2_topology C2)"
  and "card (C1 \<inter> C2) = 2"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology C1"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology C2"
  shows "\<exists>U V. U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {}
    \<and> U \<union> V = top1_S2 - (C1 \<union> C2)
    \<and> top1_connected_on U
        (subspace_topology top1_S2 top1_S2_topology U)
    \<and> top1_connected_on V
        (subspace_topology top1_S2 top1_S2_topology V)"
proof -
  \<comment> \<open>Munkres 63.5: By Theorem 61.4, C1\<union>C2 separates S^2 (\<ge>2 components).
     To show exactly 2: use Theorem 63.1. If there were 3+ components,
     one could construct two independent nontrivial elements in \<pi>_1(S^2-{p,q})
     (where C1\<inter>C2 = {p,q}), but \<pi>_1(S^2-{p,q}) \<cong> Z has only one generator.
     So exactly 2 components.\<close>
  have hsep: "top1_separates_on top1_S2 top1_S2_topology (C1 \<union> C2)"
  proof -
    have hC1sub: "C1 \<subseteq> top1_S2" using assms(2) unfolding closedin_on_def by blast
    have hC2sub: "C2 \<subseteq> top1_S2" using assms(3) unfolding closedin_on_def by blast
    show ?thesis
      by (rule Theorem_61_4_general_separation[OF assms(1) hC1sub hC2sub assms(2,3,4,5,6)])
  qed
  \<comment> \<open>At least two components from separation.\<close>
  \<comment> \<open>At most two: \<pi>_1(S^2-{a,b}) \<cong> Z can distinguish at most 2 components via Theorem 63.1.\<close>
  show ?thesis sorry
qed

section \<open>\<S>65 The Winding Number of a Simple Closed Curve\<close>

text \<open>The winding number of a loop f in R^2-{0} around the origin.
  Munkres' definition: lift the loop (cos 2\<pi>t, sin 2\<pi>t)-valued normalization
  f/|f| to a path \<tilde>f in R via the covering p: R \<rightarrow> S^1, p(x) = (cos 2\<pi>x, sin 2\<pi>x),
  and define winding number = \<tilde>f(1) - \<tilde>f(0). This is an integer since f is a loop.\<close>
definition top1_winding_number_on ::
  "(real \<Rightarrow> real \<times> real) \<Rightarrow> int" where
  "top1_winding_number_on f =
     (SOME n::int.
        \<exists>ftilde. top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets ftilde
              \<and> (\<forall>s\<in>I_set. top1_R_to_S1 (ftilde s)
                   = (fst (f s) / sqrt (fst (f s)^2 + snd (f s)^2),
                      snd (f s) / sqrt (fst (f s)^2 + snd (f s)^2)))
              \<and> n = \<lfloor>ftilde 1 - ftilde 0\<rfloor>)"

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
  \<comment> \<open>Step 1: X = U \<union> V and U \<inter> V has two components A, B.\<close>
  have hUV: "?U \<union> ?V = ?X" sorry
  have hUV_components: "\<exists>A B. A \<inter> B = {} \<and> A \<union> B = ?U \<inter> ?V \<and> A \<noteq> {} \<and> B \<noteq> {}" sorry
  \<comment> \<open>Step 2: The path \<alpha> (a1→a2 via e12) lies in U, the path \<beta> (a2→a3 via e23) lies in V.
     By Theorem 63.1, the loop \<alpha>*\<beta> is nontrivial in X.\<close>
  obtain \<alpha> where h\<alpha>: "top1_is_path_on ?U (subspace_topology top1_S2 top1_S2_topology ?U) x0 x0 \<alpha>"
    sorry
  \<comment> \<open>Step 3: f is homotopic to such a loop, hence nontrivial.\<close>
  show ?thesis sorry
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
      (top1_fundamental_group_induced_on C ?TC c0 ?Xpq ?TXpq c0 (\<lambda>x. x))" sorry
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
    using hj_hom hj_inj hj_surj unfolding bij_betw_def by (by100 blast)
qed

section \<open>Chapter 11: The Seifert-van Kampen Theorem\<close>

text \<open>Group-theoretic definitions are now in the earlier subsection before \<S>52.\<close>

lemma top1_groups_isomorphic_on_refl:
  assumes "top1_is_group_on G mul e invg"
  shows "top1_groups_isomorphic_on G mul G mul"
  unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
proof (intro exI conjI)
  show "top1_group_hom_on G mul G mul id"
    unfolding top1_group_hom_on_def by simp
  show "bij_betw id G G" by simp
qed

lemma top1_groups_isomorphic_on_sym:
  assumes hiso: "top1_groups_isomorphic_on G mulG H mulH"
      and hG: "top1_is_group_on G mulG eG invgG"
      and hH: "top1_is_group_on H mulH eH invgH"
  shows "top1_groups_isomorphic_on H mulH G mulG"
proof -
  obtain f where hf_hom: "top1_group_hom_on G mulG H mulH f" and hf_bij: "bij_betw f G H"
    using hiso unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def by blast
  have hinj: "inj_on f G" using hf_bij unfolding bij_betw_def by blast
  have hsurj: "f ` G = H" using hf_bij unfolding bij_betw_def by blast
  let ?g = "the_inv_into G f"
  have hg_mem: "\<forall>y\<in>H. ?g y \<in> G"
    using the_inv_into_into[OF hinj] hsurj by blast
  have hfg_id: "\<forall>y\<in>H. f (?g y) = y"
    using f_the_inv_into_f[OF hinj] hsurj by blast
  have hgf_id: "\<forall>x\<in>G. ?g (f x) = x"
    using the_inv_into_f_f[OF hinj] by blast
  have hg_bij: "bij_betw ?g H G"
    unfolding bij_betw_def
  proof (intro conjI)
    show "inj_on ?g H"
    proof (rule inj_onI)
      fix y1 y2 assume "y1 \<in> H" "y2 \<in> H" "?g y1 = ?g y2"
      hence "f (?g y1) = f (?g y2)" by simp
      thus "y1 = y2" using hfg_id \<open>y1 \<in> H\<close> \<open>y2 \<in> H\<close> by simp
    qed
    show "?g ` H = G"
    proof
      show "?g ` H \<subseteq> G" using hg_mem by blast
      show "G \<subseteq> ?g ` H"
      proof
        fix x assume hx: "x \<in> G"
        have hfx: "f x \<in> H" using hsurj hx by blast
        have "?g (f x) = x" using hgf_id hx by blast
        thus "x \<in> ?g ` H" using hfx by force
      qed
    qed
  qed
  have hmul_cl: "\<forall>y1\<in>H. \<forall>y2\<in>H. mulH y1 y2 \<in> H"
    using hH unfolding top1_is_group_on_def by blast
  have hmulG_cl: "\<forall>x1\<in>G. \<forall>x2\<in>G. mulG x1 x2 \<in> G"
    using hG unfolding top1_is_group_on_def by blast
  have hg_hom: "top1_group_hom_on H mulH G mulG ?g"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    fix y assume "y \<in> H" thus "?g y \<in> G" using hg_mem by blast
  next
    fix y1 y2 assume hy1: "y1 \<in> H" and hy2: "y2 \<in> H"
    have hgy1: "?g y1 \<in> G" and hgy2: "?g y2 \<in> G" using hg_mem hy1 hy2 by blast+
    have hmul_H: "mulH y1 y2 \<in> H" using hmul_cl hy1 hy2 by blast
    have "f (?g (mulH y1 y2)) = mulH y1 y2" using hfg_id hmul_H by blast
    also have "... = mulH (f (?g y1)) (f (?g y2))" using hfg_id hy1 hy2 by simp
    also have "... = f (mulG (?g y1) (?g y2))"
    proof -
      have "f (mulG (?g y1) (?g y2)) = mulH (f (?g y1)) (f (?g y2))"
        using hf_hom hgy1 hgy2 unfolding top1_group_hom_on_def by blast
      thus ?thesis by (rule sym)
    qed
    finally have "f (?g (mulH y1 y2)) = f (mulG (?g y1) (?g y2))" .
    moreover have "?g (mulH y1 y2) \<in> G" using hg_mem hmul_H by blast
    moreover have "mulG (?g y1) (?g y2) \<in> G" using hmulG_cl hgy1 hgy2 by blast
    ultimately show "?g (mulH y1 y2) = mulG (?g y1) (?g y2)"
      using hinj by (meson inj_on_eq_iff)
  qed
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
    using hg_hom hg_bij by blast
qed

lemma top1_groups_isomorphic_on_trans:
  assumes hGH: "top1_groups_isomorphic_on G mulG H mulH"
      and hHK: "top1_groups_isomorphic_on H mulH K mulK"
  shows "top1_groups_isomorphic_on G mulG K mulK"
proof -
  obtain f where hf_hom: "top1_group_hom_on G mulG H mulH f" and hf_bij: "bij_betw f G H"
    using hGH unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def by blast
  obtain g where hg_hom: "top1_group_hom_on H mulH K mulK g" and hg_bij: "bij_betw g H K"
    using hHK unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def by blast
  have hgf_hom: "top1_group_hom_on G mulG K mulK (g \<circ> f)"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    fix x assume hx: "x \<in> G"
    have "f x \<in> H" using hf_hom hx unfolding top1_group_hom_on_def by blast
    thus "(g \<circ> f) x \<in> K" using hg_hom unfolding top1_group_hom_on_def comp_def by blast
  next
    fix x y assume hx: "x \<in> G" and hy: "y \<in> G"
    have "f x \<in> H" "f y \<in> H" using hf_hom hx hy unfolding top1_group_hom_on_def by blast+
    have "(g \<circ> f) (mulG x y) = g (f (mulG x y))" by simp
    also have "... = g (mulH (f x) (f y))"
    proof -
      have "f (mulG x y) = mulH (f x) (f y)"
        using hf_hom hx hy unfolding top1_group_hom_on_def by blast
      thus ?thesis by simp
    qed
    also have "... = mulK (g (f x)) (g (f y))"
      using hg_hom \<open>f x \<in> H\<close> \<open>f y \<in> H\<close> unfolding top1_group_hom_on_def by blast
    also have "... = mulK ((g \<circ> f) x) ((g \<circ> f) y)" by simp
    finally show "(g \<circ> f) (mulG x y) = mulK ((g \<circ> f) x) ((g \<circ> f) y)" .
  qed
  have hgf_bij: "bij_betw (g \<circ> f) G K" by (rule bij_betw_trans[OF hf_bij hg_bij])
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
    using hgf_hom hgf_bij by blast
qed

text \<open>Normal subgroup: N \<subseteq> G is a subgroup closed under conjugation.\<close>
definition top1_normal_subgroup_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> bool" where
  "top1_normal_subgroup_on G mul e invg N \<longleftrightarrow>
     N \<subseteq> G \<and>
     top1_is_group_on N mul e invg \<and>
     (\<forall>g\<in>G. \<forall>n\<in>N. mul (mul g n) (invg g) \<in> N)"

text \<open>Kernel of a homomorphism is a normal subgroup.\<close>
definition top1_group_kernel_on ::
  "'g set \<Rightarrow> 'h \<Rightarrow> ('g \<Rightarrow> 'h) \<Rightarrow> 'g set" where
  "top1_group_kernel_on G eH f = {x\<in>G. f x = eH}"

text \<open>Image of a group under a homomorphism.\<close>
definition top1_group_image_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'h) \<Rightarrow> 'h set" where
  "top1_group_image_on G f = f ` G"

text \<open>Quotient group G/N: cosets g N under the product (gN)(hN) = (gh)N.
  Modelled as a set of equivalence classes.\<close>
definition top1_group_coset_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g \<Rightarrow> 'g set" where
  "top1_group_coset_on G mul N g = {mul g n | n. n \<in> N}"

definition top1_quotient_group_carrier_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set set" where
  "top1_quotient_group_carrier_on G mul N = {top1_group_coset_on G mul N g | g. g \<in> G}"

text \<open>Multiplication on cosets: (gN)(hN) = (gh)N, computed as set product.\<close>
definition top1_quotient_group_mul_on ::
  "('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set \<Rightarrow> 'g set" where
  "top1_quotient_group_mul_on mul C1 C2 = {mul g h | g h. g \<in> C1 \<and> h \<in> C2}"

text \<open>Iterated product in a group (g * g * ... * g, n times).\<close>
fun top1_group_pow :: "('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> 'g \<Rightarrow> nat \<Rightarrow> 'g" where
  "top1_group_pow mul e x 0 = e"
| "top1_group_pow mul e x (Suc n) = mul x (top1_group_pow mul e x n)"

text \<open>Product of a word in (G \<union> G\<inverse>): each letter is (g, b) where b=True means g
  contributes g to the product, and b=False means invg(g) contributes. For an empty
  word the result is the identity e.\<close>
fun top1_group_word_product ::
  "('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> ('g \<times> bool) list \<Rightarrow> 'g" where
  "top1_group_word_product mul e invg [] = e"
| "top1_group_word_product mul e invg ((x, True) # ws)
     = mul x (top1_group_word_product mul e invg ws)"
| "top1_group_word_product mul e invg ((x, False) # ws)
     = mul (invg x) (top1_group_word_product mul e invg ws)"

text \<open>A word in ('g \<times> bool) list is reduced if no adjacent pair (x, b) (x, \<not>b) appears
  (which would represent x \<cdot> x\<inverse> or x\<inverse> \<cdot> x, cancelling to e).\<close>
fun top1_is_reduced_word ::
  "('g \<times> bool) list \<Rightarrow> bool" where
  "top1_is_reduced_word [] = True"
| "top1_is_reduced_word [_] = True"
| "top1_is_reduced_word ((x, b) # (y, c) # ws)
     = ((x \<noteq> y \<or> b = c) \<and> top1_is_reduced_word ((y, c) # ws))"

text \<open>Subgroup generated by a subset S \<subseteq> G.\<close>
definition top1_subgroup_generated_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set" where
  "top1_subgroup_generated_on G mul e invg S =
     \<Inter> { H. S \<subseteq> H \<and> H \<subseteq> G \<and> top1_is_group_on H mul e invg }"

definition top1_normal_subgroup_generated_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set" where
  "top1_normal_subgroup_generated_on G mul e invg S =
     \<Inter> { N. S \<subseteq> N \<and> top1_normal_subgroup_on G mul e invg N }"

text \<open>Free group on a set S: a group F(S) with \<iota>: S \<hookrightarrow> F(S) such that:
  (1) \<iota> is injective,
  (2) \<iota>(S) generates F(S), and
  (3) no non-empty reduced word in \<iota>(S) \<union> \<iota>(S)\<inverse> equals e (the freeness condition).
  Together, (2)+(3) are equivalent to the universal extension property.\<close>
definition top1_is_free_group_full_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> ('s \<Rightarrow> 'g) \<Rightarrow> 's set \<Rightarrow> bool" where
  "top1_is_free_group_full_on G mul e invg \<iota> S \<longleftrightarrow>
     top1_is_group_on G mul e invg \<and>
     (\<forall>s\<in>S. \<iota> s \<in> G) \<and>
     inj_on \<iota> S \<and>
     G = top1_subgroup_generated_on G mul e invg (\<iota> ` S) \<and>
     (\<forall>ws :: ('s \<times> bool) list.
        ws \<noteq> [] \<longrightarrow>
        top1_is_reduced_word (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<longrightarrow>
        (\<forall>i<length ws. fst (ws!i) \<in> S) \<longrightarrow>
        top1_group_word_product mul e invg (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<noteq> e)"

text \<open>External universal property for free groups: for a specific test type,
  any function S \<rightarrow> H extends uniquely to a homomorphism G \<rightarrow> H.\<close>
definition top1_free_group_universal_prop ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> ('s \<Rightarrow> 'g) \<Rightarrow> 's set \<Rightarrow>
   'h set \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> 'h) \<Rightarrow> 'h \<Rightarrow> ('h \<Rightarrow> 'h) \<Rightarrow> ('s \<Rightarrow> 'h) \<Rightarrow> bool" where
  "top1_free_group_universal_prop G mul \<iota> S H mulH eH invgH \<phi> \<longleftrightarrow>
     top1_is_group_on H mulH eH invgH \<and> (\<forall>s\<in>S. \<phi> s \<in> H) \<longrightarrow>
     (\<exists>!\<psi>. top1_group_hom_on G mul H mulH \<psi>
        \<and> (\<forall>s\<in>S. \<psi> (\<iota> s) = \<phi> s))"

text \<open>Free abelian group on a set S: abelian group G together with \<iota>: S \<hookrightarrow> G such that
  (1) \<iota> is injective, (2) \<iota>(S) generates G, and
  (3) no non-trivial finitely-supported integer combination of \<iota>(S) equals e.
  Condition (3) is the abelian freeness: for any nonzero c : S \<rightarrow> int with finite
  support, the product over s of \<iota>(s) raised to c(s) is not e.\<close>
definition top1_is_free_abelian_group_full_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> ('s \<Rightarrow> 'g) \<Rightarrow> 's set \<Rightarrow> bool" where
  "top1_is_free_abelian_group_full_on G mul e invg \<iota> S \<longleftrightarrow>
     top1_is_abelian_group_on G mul e invg \<and>
     (\<forall>s\<in>S. \<iota> s \<in> G) \<and>
     inj_on \<iota> S \<and>
     G = top1_subgroup_generated_on G mul e invg (\<iota> ` S) \<and>
     (\<forall>c :: 's \<Rightarrow> int.
        finite {s\<in>S. c s \<noteq> 0} \<longrightarrow>
        (\<exists>s\<in>S. c s \<noteq> 0) \<longrightarrow>
        foldr mul (map (\<lambda>s.
            if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
            else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s)))
          (SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs)) e
        \<noteq> e)"

text \<open>Group presentation: G is presented by generators S modulo relations R.
  Relations are reduced words in S \<union> S\<inverse> (type ('s \<times> bool) list, as for free groups).
  G \<cong> F(S)/\<langle>\<langle>R\<rangle>\<rangle> means: there is a free group F on S and a surjective homomorphism
  \<pi>: F \<rightarrow> G whose kernel is the normal subgroup of F generated by the images of
  the relator words (computed via top1_group_word_product).\<close>
definition top1_group_presented_by_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g)
   \<Rightarrow> 's set \<Rightarrow> (('s \<times> bool) list set) \<Rightarrow> bool" where
  "top1_group_presented_by_on G mul e invg S R \<longleftrightarrow>
     top1_is_group_on G mul e invg \<and>
     (\<exists>(F::'g set) mulF eF invgF \<iota> \<pi>.
        top1_is_free_group_full_on F mulF eF invgF \<iota> S
      \<and> top1_group_hom_on F mulF G mul \<pi>
      \<and> \<pi> ` F = G
      \<and> top1_group_kernel_on F e \<pi>
           = top1_normal_subgroup_generated_on F mulF eF invgF
               {r. \<exists>w\<in>R. r = top1_group_word_product mulF eF invgF
                            (map (\<lambda>(s, b). (\<iota> s, b)) w)})"

text \<open>Free product of a family of groups (Munkres §68): a group (G, mul, e, invg)
  with injective homomorphisms \<iota>_\<alpha>: G_\<alpha> \<hookrightarrow> G (one per index \<alpha>\<in>J), such that:
  (1) the images \<iota>_\<alpha>(G_\<alpha>) generate G, and
  (2) any non-empty reduced product of elements (alternating between different
      \<iota>_\<alpha>(G_\<alpha>\<setminus>{e_\<alpha>})) is not the identity of G.
  The last conjunct encodes (2): word = list of (index, element) pairs where
  each element differs from its group's identity and consecutive indices differ;
  its product in G is not e.\<close>
definition top1_is_free_product_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow>
   ('i \<Rightarrow> 'gg set) \<Rightarrow> ('i \<Rightarrow> 'gg \<Rightarrow> 'gg \<Rightarrow> 'gg) \<Rightarrow>
   ('i \<Rightarrow> 'gg \<Rightarrow> 'g) \<Rightarrow> 'i set \<Rightarrow> bool" where
  "top1_is_free_product_on G mul e invg GG mulGG \<iota>fam J \<longleftrightarrow>
     top1_is_group_on G mul e invg \<and>
     (\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<iota>fam \<alpha> x \<in> G) \<and>
     (\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<forall>y\<in>GG \<alpha>.
        \<iota>fam \<alpha> (mulGG \<alpha> x y) = mul (\<iota>fam \<alpha> x) (\<iota>fam \<alpha> y)) \<and>
     (\<forall>\<alpha>\<in>J. inj_on (\<iota>fam \<alpha>) (GG \<alpha>)) \<and>
     G = top1_subgroup_generated_on G mul e invg (\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>) \<and>
     (\<forall>indices word.
        length indices = length word \<longrightarrow>
        length indices > 0 \<longrightarrow>
        (\<forall>i<length indices. indices!i \<in> J \<and> word!i \<in> GG (indices!i)
                          \<and> \<iota>fam (indices!i) (word!i) \<noteq> e) \<longrightarrow>
        (\<forall>i. i + 1 < length indices \<longrightarrow> indices!i \<noteq> indices!(i+1)) \<longrightarrow>
        foldr mul (map (\<lambda>i. \<iota>fam (indices!i) (word!i)) [0..<length indices]) e \<noteq> e)"

text \<open>The cyclic group Z/nZ with modular addition.\<close>
definition top1_Zn_group :: "nat \<Rightarrow> int set" where
  "top1_Zn_group n = {0..<int n}"

definition top1_Zn_mul :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "top1_Zn_mul n a b = (a + b) mod int n"

definition top1_Zn_id :: "int" where
  "top1_Zn_id = 0"

definition top1_Zn_invg :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "top1_Zn_invg n a = (int n - a) mod int n"

lemma top1_Zn_is_abelian_group:
  assumes hn: "n \<ge> 1"
  shows "top1_is_abelian_group_on (top1_Zn_group n) (top1_Zn_mul n) top1_Zn_id (top1_Zn_invg n)"
proof -
  have hn_pos: "int n > 0" using hn by simp
  show ?thesis
    unfolding top1_is_abelian_group_on_def top1_is_group_on_def
              top1_Zn_group_def top1_Zn_mul_def top1_Zn_id_def top1_Zn_invg_def
  proof (intro conjI ballI)
    show "(0::int) \<in> {0..<int n}" using hn by simp
  next
    fix x y assume "x \<in> {0::int..<int n}" "y \<in> {0::int..<int n}"
    thus "(x + y) mod int n \<in> {0..<int n}" using hn_pos by simp
  next
    fix x assume "x \<in> {0::int..<int n}"
    thus "(int n - x) mod int n \<in> {0..<int n}" using hn_pos by simp
  next
    fix x y z assume hx: "x \<in> {0::int..<int n}" and hy: "y \<in> {0::int..<int n}" and hz: "z \<in> {0::int..<int n}"
    show "((x + y) mod int n + z) mod int n = (x + (y + z) mod int n) mod int n"
      by (simp add: mod_add_left_eq mod_add_right_eq add.assoc)
  next
    fix x assume hx: "x \<in> {0::int..<int n}"
    hence hx0: "0 \<le> x" and hxn: "x < int n" by auto
    show "(0 + x) mod int n = x" using hx0 hxn by simp
  next
    fix x assume hx: "x \<in> {0::int..<int n}"
    hence hx0: "0 \<le> x" and hxn: "x < int n" by auto
    show "(x + 0) mod int n = x" using hx0 hxn by simp
  next
    fix x assume hx: "x \<in> {0::int..<int n}"
    show "((int n - x) mod int n + x) mod int n = 0"
      using hx hn_pos by (simp add: mod_add_left_eq)
  next
    fix x assume hx: "x \<in> {0::int..<int n}"
    show "(x + (int n - x) mod int n) mod int n = 0"
      using hx hn_pos by (simp add: mod_add_right_eq)
  next
    fix x y assume "x \<in> {0::int..<int n}" "y \<in> {0::int..<int n}"
    show "(x + y) mod int n = (y + x) mod int n" by (simp add: add.commute)
  qed
qed

text \<open>The torsion subgroup of an abelian group.\<close>
definition top1_torsion_subgroup_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> 'g set" where
  "top1_torsion_subgroup_on G mul e =
     {x\<in>G. \<exists>n. n > 0 \<and> top1_group_pow mul e x n = e}"

text \<open>Commutator [a, b] = a b a\<inverse> b\<inverse> in a group.\<close>
definition top1_group_commutator_on ::
  "('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> 'g \<Rightarrow> 'g" where
  "top1_group_commutator_on mul invg a b = mul (mul (mul a b) (invg a)) (invg b)"

text \<open>The commutator subgroup [G, G] generated by all commutators [a, b].\<close>
definition top1_commutator_subgroup_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g set" where
  "top1_commutator_subgroup_on G mul e invg =
     top1_subgroup_generated_on G mul e invg
       { top1_group_commutator_on mul invg a b | a b. a \<in> G \<and> b \<in> G }"

text \<open>Normalizer of H in G: N(H) = {g \<in> G | gHg\<inverse> = H}.\<close>
definition top1_normalizer_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set" where
  "top1_normalizer_on G mul invg H =
     {g \<in> G. {mul (mul g h) (invg g) | h. h \<in> H} = H}"

text \<open>H is the abelianization of G: H = G/[G, G] with the induced abelian structure.
  Equivalently, H is an abelian group together with a surjective homomorphism
  \<phi>: G \<rightarrow> H whose kernel is [G, G] (the commutator subgroup).\<close>
definition top1_is_abelianization_of ::
  "'h set \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> 'h) \<Rightarrow> 'h \<Rightarrow> ('h \<Rightarrow> 'h) \<Rightarrow>
   'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow>
   ('g \<Rightarrow> 'h) \<Rightarrow> bool" where
  "top1_is_abelianization_of H mulH eH invgH G mul e invg \<phi> \<longleftrightarrow>
     top1_is_abelian_group_on H mulH eH invgH \<and>
     top1_is_group_on G mul e invg \<and>
     top1_group_hom_on G mul H mulH \<phi> \<and>
     \<phi> ` G = H \<and>
     top1_group_kernel_on G eH \<phi> = top1_commutator_subgroup_on G mul e invg"

section \<open>\<S>67 Direct Sums of Abelian Groups\<close>

text \<open>External direct sum: the set of finitely-supported functions J \<rightarrow> \<Union>G_\<alpha>.\<close>
text \<open>External direct sum: the set of finitely-supported functions f : J \<rightarrow> \<Union>_\<alpha> G_\<alpha>
  with f \<alpha> \<in> G_\<alpha> and f \<alpha> = e_\<alpha> (the identity of G_\<alpha>) for all but finitely many \<alpha>.\<close>
definition top1_direct_sum_carrier ::
  "'i set \<Rightarrow> ('i \<Rightarrow> 'g set) \<Rightarrow> ('i \<Rightarrow> 'g) \<Rightarrow> ('i \<Rightarrow> 'g) set" where
  "top1_direct_sum_carrier J G eFam =
     {f. (\<forall>i\<in>J. f i \<in> G i) \<and> (\<forall>i. i \<notin> J \<longrightarrow> f i = eFam i) \<and>
         finite {i\<in>J. f i \<noteq> eFam i}}"

text \<open>H is an (internal) direct sum of the abelian groups {G_\<alpha>}_{\<alpha>\<in>J} along
  injections \<iota>fam_\<alpha>: G_\<alpha> \<hookrightarrow> H iff H is abelian and the natural map from the
  external direct sum to H (sending f to the finite product \<Prod>_\<alpha> \<iota>fam_\<alpha>(f \<alpha>))
  is a group isomorphism whose restriction to the \<alpha>-th 'axis' is \<iota>fam_\<alpha>.\<close>
definition top1_is_direct_sum_of_on ::
  "'h set \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> 'h) \<Rightarrow> 'h \<Rightarrow> ('h \<Rightarrow> 'h) \<Rightarrow>
   'i set \<Rightarrow> ('i \<Rightarrow> 'g set) \<Rightarrow> ('i \<Rightarrow> 'g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow>
   ('i \<Rightarrow> 'g) \<Rightarrow> ('i \<Rightarrow> 'g \<Rightarrow> 'h) \<Rightarrow> bool" where
  "top1_is_direct_sum_of_on H mulH eH invgH J G mulG eG \<iota>fam \<longleftrightarrow>
     top1_is_abelian_group_on H mulH eH invgH \<and>
     (\<forall>\<alpha>\<in>J. top1_group_hom_on (G \<alpha>) (mulG \<alpha>) H mulH (\<iota>fam \<alpha>)) \<and>
     (\<forall>\<alpha>\<in>J. inj_on (\<iota>fam \<alpha>) (G \<alpha>)) \<and>
     (\<exists>\<Phi>. top1_group_iso_on
            (top1_direct_sum_carrier J G eG)
            (\<lambda>f g. \<lambda>\<alpha>. if \<alpha> \<in> J then mulG \<alpha> (f \<alpha>) (g \<alpha>) else eG \<alpha>)
            H mulH \<Phi>
          \<and> (\<forall>\<alpha>\<in>J. \<forall>x\<in>G \<alpha>. \<Phi> (\<lambda>\<beta>. if \<beta> = \<alpha> then x else eG \<beta>) = \<iota>fam \<alpha> x))"

lemma top1_direct_sum_carrier_mul_closed:
  assumes "\<forall>\<alpha>\<in>J. top1_is_abelian_group_on (G \<alpha>) (mul \<alpha>) (e \<alpha>) (invg \<alpha>)"
      and "f \<in> top1_direct_sum_carrier J G e" and "g \<in> top1_direct_sum_carrier J G e"
  shows "(\<lambda>\<alpha>. if \<alpha> \<in> J then mul \<alpha> (f \<alpha>) (g \<alpha>) else e \<alpha>) \<in> top1_direct_sum_carrier J G e"
proof -
  have hfm: "\<forall>\<alpha>\<in>J. f \<alpha> \<in> G \<alpha>" and hgm: "\<forall>\<alpha>\<in>J. g \<alpha> \<in> G \<alpha>"
    using assms(2,3) unfolding top1_direct_sum_carrier_def by blast+
  have hff: "finite {i \<in> J. f i \<noteq> e i}" and hgf: "finite {i \<in> J. g i \<noteq> e i}"
    using assms(2,3) unfolding top1_direct_sum_carrier_def by auto
  let ?h = "\<lambda>\<alpha>. if \<alpha> \<in> J then mul \<alpha> (f \<alpha>) (g \<alpha>) else e \<alpha>"
  show ?thesis unfolding top1_direct_sum_carrier_def
  proof (intro CollectI conjI)
    show "\<forall>i\<in>J. ?h i \<in> G i"
      using hfm hgm assms(1) unfolding top1_is_abelian_group_on_def top1_is_group_on_def by simp
    show "\<forall>i. i \<notin> J \<longrightarrow> ?h i = e i" by simp
    show "finite {i \<in> J. ?h i \<noteq> e i}"
    proof -
      have "{i \<in> J. ?h i \<noteq> e i} \<subseteq> {i \<in> J. f i \<noteq> e i} \<union> {i \<in> J. g i \<noteq> e i}"
      proof
        fix i assume "i \<in> {i \<in> J. ?h i \<noteq> e i}"
        hence hi: "i \<in> J" and hne: "mul i (f i) (g i) \<noteq> e i" by auto
        show "i \<in> {i \<in> J. f i \<noteq> e i} \<union> {i \<in> J. g i \<noteq> e i}"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          hence "f i = e i" "g i = e i" using hi by auto
          hence "mul i (f i) (g i) = mul i (e i) (e i)" by simp
          also have "... = e i"
            using assms(1) hi unfolding top1_is_abelian_group_on_def top1_is_group_on_def by blast
          finally show False using hne by contradiction
        qed
      qed
      thus ?thesis using finite_subset hff hgf by blast
    qed
  qed
qed

(** from \<S>67 Theorem 67.4: existence of external direct sum of abelian groups.
    The direct sum (finitely-supported coordinate-wise functions) is an abelian group,
    equipped with natural injections \<iota>fam_\<alpha> : G_\<alpha> \<hookrightarrow> \<oplus>_\<alpha> G_\<alpha>. **)
theorem Theorem_67_4_direct_sum_exists:
  assumes hG: "\<forall>\<alpha>\<in>(J::'i set). top1_is_abelian_group_on (G \<alpha>::'g set) (mul \<alpha>) (e \<alpha>) (invg \<alpha>)"
  shows "\<exists>\<iota>fam.
           top1_is_abelian_group_on
             (top1_direct_sum_carrier J G e)
             (\<lambda>f g. \<lambda>\<alpha>. if \<alpha> \<in> J then mul \<alpha> (f \<alpha>) (g \<alpha>) else e \<alpha>)
             e
             (\<lambda>f. \<lambda>\<alpha>. if \<alpha> \<in> J then invg \<alpha> (f \<alpha>) else e \<alpha>)
         \<and> (\<forall>\<alpha>\<in>J. top1_group_hom_on (G \<alpha>) (mul \<alpha>)
               (top1_direct_sum_carrier J G e)
               (\<lambda>f g. \<lambda>\<beta>. if \<beta> \<in> J then mul \<beta> (f \<beta>) (g \<beta>) else e \<beta>)
               (\<iota>fam \<alpha>))
         \<and> (\<forall>\<alpha>\<in>J. inj_on (\<iota>fam \<alpha>) (G \<alpha>))
         \<and> (\<forall>\<alpha>\<in>J. \<forall>x\<in>G \<alpha>. \<iota>fam \<alpha> x \<alpha> = x \<and>
              (\<forall>\<beta>. \<beta> \<noteq> \<alpha> \<longrightarrow> \<iota>fam \<alpha> x \<beta> = e \<beta>))"
proof -
  \<comment> \<open>Natural axis injection: \<iota>_\<alpha>(x) is the function with value x at \<alpha> and e(\<beta>) elsewhere.\<close>
  let ?\<iota> = "\<lambda>\<alpha> x. \<lambda>\<beta>. if \<beta> = \<alpha> then x else e \<beta>"
  let ?DS = "top1_direct_sum_carrier J G e"
  let ?mulDS = "\<lambda>f g. \<lambda>\<alpha>. if \<alpha> \<in> J then mul \<alpha> (f \<alpha>) (g \<alpha>) else e \<alpha>"
  let ?invDS = "\<lambda>f. \<lambda>\<alpha>. if \<alpha> \<in> J then invg \<alpha> (f \<alpha>) else e \<alpha>"
  have hGprops: "\<And>\<alpha>. \<alpha> \<in> J \<Longrightarrow> e \<alpha> \<in> G \<alpha>"
               "\<And>\<alpha> x y. \<lbrakk>\<alpha> \<in> J; x \<in> G \<alpha>; y \<in> G \<alpha>\<rbrakk> \<Longrightarrow> mul \<alpha> x y \<in> G \<alpha>"
               "\<And>\<alpha> x. \<lbrakk>\<alpha> \<in> J; x \<in> G \<alpha>\<rbrakk> \<Longrightarrow> invg \<alpha> x \<in> G \<alpha>"
               "\<And>\<alpha> x y z. \<lbrakk>\<alpha> \<in> J; x \<in> G \<alpha>; y \<in> G \<alpha>; z \<in> G \<alpha>\<rbrakk>
                  \<Longrightarrow> mul \<alpha> (mul \<alpha> x y) z = mul \<alpha> x (mul \<alpha> y z)"
               "\<And>\<alpha> x. \<lbrakk>\<alpha> \<in> J; x \<in> G \<alpha>\<rbrakk> \<Longrightarrow> mul \<alpha> (e \<alpha>) x = x"
               "\<And>\<alpha> x. \<lbrakk>\<alpha> \<in> J; x \<in> G \<alpha>\<rbrakk> \<Longrightarrow> mul \<alpha> x (e \<alpha>) = x"
               "\<And>\<alpha> x. \<lbrakk>\<alpha> \<in> J; x \<in> G \<alpha>\<rbrakk> \<Longrightarrow> mul \<alpha> (invg \<alpha> x) x = e \<alpha>"
               "\<And>\<alpha> x. \<lbrakk>\<alpha> \<in> J; x \<in> G \<alpha>\<rbrakk> \<Longrightarrow> mul \<alpha> x (invg \<alpha> x) = e \<alpha>"
               "\<And>\<alpha> x y. \<lbrakk>\<alpha> \<in> J; x \<in> G \<alpha>; y \<in> G \<alpha>\<rbrakk> \<Longrightarrow> mul \<alpha> x y = mul \<alpha> y x"
    using hG unfolding top1_is_abelian_group_on_def top1_is_group_on_def by blast+
  have hDS_mem: "\<And>f. f \<in> ?DS \<Longrightarrow> (\<forall>\<alpha>\<in>J. f \<alpha> \<in> G \<alpha>)"
    unfolding top1_direct_sum_carrier_def by blast
  have hDS_out: "\<And>f. f \<in> ?DS \<Longrightarrow> (\<forall>\<alpha>. \<alpha> \<notin> J \<longrightarrow> f \<alpha> = e \<alpha>)"
    unfolding top1_direct_sum_carrier_def by blast
  have he_DS: "e \<in> ?DS"
    unfolding top1_direct_sum_carrier_def
  proof (intro CollectI conjI)
    show "\<forall>i\<in>J. e i \<in> G i" using hGprops(1) by blast
    show "\<forall>i. i \<notin> J \<longrightarrow> e i = e i" by simp
    show "finite {i \<in> J. e i \<noteq> e i}" by simp
  qed
  have hmul_cl: "\<forall>x\<in>?DS. \<forall>y\<in>?DS. ?mulDS x y \<in> ?DS"
  proof (intro ballI)
    fix f g assume hf: "f \<in> ?DS" and hg: "g \<in> ?DS"
    show "?mulDS f g \<in> ?DS"
      unfolding top1_direct_sum_carrier_def
    proof (intro CollectI conjI)
      show "\<forall>i\<in>J. (\<lambda>\<alpha>. if \<alpha> \<in> J then mul \<alpha> (f \<alpha>) (g \<alpha>) else e \<alpha>) i \<in> G i"
        using hDS_mem[OF hf] hDS_mem[OF hg] hGprops(2) by simp
      show "\<forall>i. i \<notin> J \<longrightarrow> (\<lambda>\<alpha>. if \<alpha> \<in> J then mul \<alpha> (f \<alpha>) (g \<alpha>) else e \<alpha>) i = e i"
        by simp
      show "finite {i \<in> J. (\<lambda>\<alpha>. if \<alpha> \<in> J then mul \<alpha> (f \<alpha>) (g \<alpha>) else e \<alpha>) i \<noteq> e i}"
      proof -
        have "{i \<in> J. mul i (f i) (g i) \<noteq> e i} \<subseteq> {i \<in> J. f i \<noteq> e i} \<union> {i \<in> J. g i \<noteq> e i}"
        proof
          fix i assume "i \<in> {i \<in> J. mul i (f i) (g i) \<noteq> e i}"
          hence hi: "i \<in> J" and hne: "mul i (f i) (g i) \<noteq> e i" by auto
          show "i \<in> {i \<in> J. f i \<noteq> e i} \<union> {i \<in> J. g i \<noteq> e i}"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            hence "f i = e i" "g i = e i" using hi by auto
            hence "mul i (f i) (g i) = mul i (e i) (e i)" by simp
            also have "... = e i" using hGprops(5) hi hGprops(1) by blast
            finally show False using hne by contradiction
          qed
        qed
        moreover have "finite ({i \<in> J. f i \<noteq> e i} \<union> {i \<in> J. g i \<noteq> e i})"
          using hf hg unfolding top1_direct_sum_carrier_def by auto
        ultimately have hfin: "finite {i \<in> J. mul i (f i) (g i) \<noteq> e i}"
          using finite_subset by blast
        have "{i. (i \<in> J \<longrightarrow> mul i (f i) (g i) \<noteq> e i) \<and> i \<in> J}
              = {i \<in> J. mul i (f i) (g i) \<noteq> e i}" by auto
        then show ?thesis using hfin by simp
      qed
    qed
  qed
  have hinvg_e: "\<And>i. i \<in> J \<Longrightarrow> invg i (e i) = e i"
  proof -
    fix i assume hi: "i \<in> J"
    have "mul i (invg i (e i)) (e i) = e i" using hGprops(7) hi hGprops(1) by blast
    moreover have "mul i (e i) (e i) = e i" using hGprops(5) hi hGprops(1) by blast
    moreover have "invg i (e i) \<in> G i" using hGprops(3) hi hGprops(1) by blast
    moreover have "e i \<in> G i" using hGprops(1) hi by blast
    ultimately show "invg i (e i) = e i"
      using hGprops(6) hi by force
  qed
  have hinv_cl: "\<forall>x\<in>?DS. ?invDS x \<in> ?DS"
  proof (intro ballI)
    fix f assume hf: "f \<in> ?DS"
    show "?invDS f \<in> ?DS"
      unfolding top1_direct_sum_carrier_def
    proof (intro CollectI conjI)
      show "\<forall>i\<in>J. (\<lambda>\<alpha>. if \<alpha> \<in> J then invg \<alpha> (f \<alpha>) else e \<alpha>) i \<in> G i"
        using hDS_mem[OF hf] hGprops(3) by simp
      show "\<forall>i. i \<notin> J \<longrightarrow> (\<lambda>\<alpha>. if \<alpha> \<in> J then invg \<alpha> (f \<alpha>) else e \<alpha>) i = e i"
        by simp
      show "finite {i \<in> J. (\<lambda>\<alpha>. if \<alpha> \<in> J then invg \<alpha> (f \<alpha>) else e \<alpha>) i \<noteq> e i}"
      proof -
        have "{i \<in> J. invg i (f i) \<noteq> e i} \<subseteq> {i \<in> J. f i \<noteq> e i}"
        proof
          fix i assume "i \<in> {i \<in> J. invg i (f i) \<noteq> e i}"
          hence hi: "i \<in> J" and hne: "invg i (f i) \<noteq> e i" by auto
          show "i \<in> {i \<in> J. f i \<noteq> e i}"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            hence "f i = e i" using hi by simp
            hence "invg i (f i) = invg i (e i)" by simp
            also have "... = e i" using hinvg_e hi by blast
            finally show False using hne by contradiction
          qed
        qed
        moreover have "finite {i \<in> J. f i \<noteq> e i}"
          using hf unfolding top1_direct_sum_carrier_def by auto
        ultimately have hfin: "finite {i \<in> J. invg i (f i) \<noteq> e i}"
          using finite_subset by blast
        have "{i. (i \<in> J \<longrightarrow> invg i (f i) \<noteq> e i) \<and> i \<in> J}
              = {i \<in> J. invg i (f i) \<noteq> e i}" by auto
        then show ?thesis using hfin by simp
      qed
    qed
  qed
  have hassoc: "\<forall>x\<in>?DS. \<forall>y\<in>?DS. \<forall>z\<in>?DS.
    ?mulDS (?mulDS x y) z = ?mulDS x (?mulDS y z)"
  proof (intro ballI)
    fix f g h assume hf: "f \<in> ?DS" and hg: "g \<in> ?DS" and hh: "h \<in> ?DS"
    show "?mulDS (?mulDS f g) h = ?mulDS f (?mulDS g h)"
    proof (rule ext)
      fix \<alpha>
      show "?mulDS (?mulDS f g) h \<alpha> = ?mulDS f (?mulDS g h) \<alpha>"
      proof (cases "\<alpha> \<in> J")
        case True
        hence "?mulDS (?mulDS f g) h \<alpha> = mul \<alpha> (mul \<alpha> (f \<alpha>) (g \<alpha>)) (h \<alpha>)" by simp
        also have "... = mul \<alpha> (f \<alpha>) (mul \<alpha> (g \<alpha>) (h \<alpha>))"
          using hGprops(4) True hDS_mem[OF hf] hDS_mem[OF hg] hDS_mem[OF hh] by blast
        also have "... = ?mulDS f (?mulDS g h) \<alpha>" using True by simp
        finally show ?thesis .
      next
        case False thus ?thesis by simp
      qed
    qed
  qed
  have hid: "\<forall>x\<in>?DS. ?mulDS e x = x \<and> ?mulDS x e = x"
  proof (intro ballI conjI)
    fix f assume hf: "f \<in> ?DS"
    show "?mulDS e f = f"
    proof (rule ext)
      fix \<alpha>
      show "?mulDS e f \<alpha> = f \<alpha>"
      proof (cases "\<alpha> \<in> J")
        case True
        thus ?thesis using hGprops(5) hDS_mem[OF hf] by simp
      next
        case False thus ?thesis using hDS_out[OF hf] by simp
      qed
    qed
    show "?mulDS f e = f"
    proof (rule ext)
      fix \<alpha>
      show "?mulDS f e \<alpha> = f \<alpha>"
      proof (cases "\<alpha> \<in> J")
        case True
        thus ?thesis using hGprops(6) hDS_mem[OF hf] by simp
      next
        case False thus ?thesis using hDS_out[OF hf] by simp
      qed
    qed
  qed
  have hinv_ax: "\<forall>x\<in>?DS. ?mulDS (?invDS x) x = e \<and> ?mulDS x (?invDS x) = e"
  proof (intro ballI conjI)
    fix f assume hf: "f \<in> ?DS"
    show "?mulDS (?invDS f) f = e"
    proof (rule ext)
      fix \<alpha>
      show "?mulDS (?invDS f) f \<alpha> = e \<alpha>"
      proof (cases "\<alpha> \<in> J")
        case True
        thus ?thesis using hGprops(7) hDS_mem[OF hf] by simp
      next
        case False thus ?thesis by simp
      qed
    qed
    show "?mulDS f (?invDS f) = e"
    proof (rule ext)
      fix \<alpha>
      show "?mulDS f (?invDS f) \<alpha> = e \<alpha>"
      proof (cases "\<alpha> \<in> J")
        case True
        thus ?thesis using hGprops(8) hDS_mem[OF hf] by simp
      next
        case False thus ?thesis by simp
      qed
    qed
  qed
  have hcomm: "\<forall>x\<in>?DS. \<forall>y\<in>?DS. ?mulDS x y = ?mulDS y x"
  proof (intro ballI)
    fix f g assume hf: "f \<in> ?DS" and hg: "g \<in> ?DS"
    show "?mulDS f g = ?mulDS g f"
    proof (rule ext)
      fix \<alpha>
      show "?mulDS f g \<alpha> = ?mulDS g f \<alpha>"
      proof (cases "\<alpha> \<in> J")
        case True
        thus ?thesis using hGprops(9) hDS_mem[OF hf] hDS_mem[OF hg] by simp
      next
        case False thus ?thesis by simp
      qed
    qed
  qed
  have habel: "top1_is_abelian_group_on ?DS ?mulDS e ?invDS"
    unfolding top1_is_abelian_group_on_def top1_is_group_on_def
    using he_DS hmul_cl hinv_cl hassoc hid hinv_ax hcomm by argo
  have hhom: "\<forall>\<alpha>\<in>J. top1_group_hom_on (G \<alpha>) (mul \<alpha>)
               (top1_direct_sum_carrier J G e)
               (\<lambda>f g. \<lambda>\<beta>. if \<beta> \<in> J then mul \<beta> (f \<beta>) (g \<beta>) else e \<beta>)
               (?\<iota> \<alpha>)"
  proof (intro ballI)
    fix \<alpha> assume h\<alpha>: "\<alpha> \<in> J"
    show "top1_group_hom_on (G \<alpha>) (mul \<alpha>) (top1_direct_sum_carrier J G e)
           (\<lambda>f g. \<lambda>\<beta>. if \<beta> \<in> J then mul \<beta> (f \<beta>) (g \<beta>) else e \<beta>) (?\<iota> \<alpha>)"
      unfolding top1_group_hom_on_def
    proof (intro conjI ballI)
      fix x assume hx: "x \<in> G \<alpha>"
      show "?\<iota> \<alpha> x \<in> top1_direct_sum_carrier J G e"
        unfolding top1_direct_sum_carrier_def
      proof (intro CollectI conjI)
        show "\<forall>i\<in>J. (?\<iota> \<alpha> x) i \<in> G i"
        proof
          fix i assume "i \<in> J"
          show "(?\<iota> \<alpha> x) i \<in> G i"
          proof (cases "i = \<alpha>")
            case True thus ?thesis using hx by simp
          next
            case False
            have "e i \<in> G i" using \<open>i \<in> J\<close> hG
              unfolding top1_is_abelian_group_on_def top1_is_group_on_def by blast
            moreover have "(?\<iota> \<alpha> x) i = e i" using False by simp
            ultimately show ?thesis by simp
          qed
        qed
        show "\<forall>i. i \<notin> J \<longrightarrow> (?\<iota> \<alpha> x) i = e i"
        proof (intro allI impI)
          fix i assume "i \<notin> J"
          hence "i \<noteq> \<alpha>" using h\<alpha> by blast
          thus "(?\<iota> \<alpha> x) i = e i" by simp
        qed
        show "finite {i \<in> J. (?\<iota> \<alpha> x) i \<noteq> e i}"
        proof -
          have "{i \<in> J. (?\<iota> \<alpha> x) i \<noteq> e i} \<subseteq> {\<alpha>}" by auto
          thus ?thesis using finite_subset by blast
        qed
      qed
    next
      fix x y assume hx: "x \<in> G \<alpha>" and hy: "y \<in> G \<alpha>"
      show "?\<iota> \<alpha> (mul \<alpha> x y) = (\<lambda>f g. \<lambda>\<beta>. if \<beta> \<in> J then mul \<beta> (f \<beta>) (g \<beta>) else e \<beta>) (?\<iota> \<alpha> x) (?\<iota> \<alpha> y)"
      proof (rule ext)
        fix \<beta>
        show "?\<iota> \<alpha> (mul \<alpha> x y) \<beta> = (\<lambda>\<beta>. if \<beta> \<in> J then mul \<beta> ((?\<iota> \<alpha> x) \<beta>) ((?\<iota> \<alpha> y) \<beta>) else e \<beta>) \<beta>"
        proof (cases "\<beta> = \<alpha>")
          case True thus ?thesis using h\<alpha> by simp
        next
          case False
          hence lhs: "?\<iota> \<alpha> (mul \<alpha> x y) \<beta> = e \<beta>" by simp
          have "(?\<iota> \<alpha> x) \<beta> = e \<beta>" "(?\<iota> \<alpha> y) \<beta> = e \<beta>" using False by simp_all
          hence rhs: "(\<lambda>\<beta>. if \<beta> \<in> J then mul \<beta> ((?\<iota> \<alpha> x) \<beta>) ((?\<iota> \<alpha> y) \<beta>) else e \<beta>) \<beta>
                     = (if \<beta> \<in> J then mul \<beta> (e \<beta>) (e \<beta>) else e \<beta>)" by simp
          show ?thesis
          proof (cases "\<beta> \<in> J")
            case True
            hence "mul \<beta> (e \<beta>) (e \<beta>) = e \<beta>"
              using hG unfolding top1_is_abelian_group_on_def top1_is_group_on_def by blast
            thus ?thesis using lhs rhs True by simp
          next
            case False thus ?thesis using lhs rhs by simp
          qed
        qed
      qed
    qed
  qed
  have hinj: "\<forall>\<alpha>\<in>J. inj_on (?\<iota> \<alpha>) (G \<alpha>)"
  proof (intro ballI)
    fix \<alpha> assume h\<alpha>: "\<alpha> \<in> J"
    show "inj_on (?\<iota> \<alpha>) (G \<alpha>)"
    proof (rule inj_onI)
      fix x y assume "x \<in> G \<alpha>" "y \<in> G \<alpha>" "?\<iota> \<alpha> x = ?\<iota> \<alpha> y"
      hence "(\<lambda>\<beta>. if \<beta> = \<alpha> then x else e \<beta>) = (\<lambda>\<beta>. if \<beta> = \<alpha> then y else e \<beta>)" by simp
      hence "(\<lambda>\<beta>. if \<beta> = \<alpha> then x else e \<beta>) \<alpha> = (\<lambda>\<beta>. if \<beta> = \<alpha> then y else e \<beta>) \<alpha>"
        by (rule fun_cong)
      thus "x = y" by simp
    qed
  qed
  have haxis: "\<forall>\<alpha>\<in>J. \<forall>x\<in>G \<alpha>. ?\<iota> \<alpha> x \<alpha> = x \<and> (\<forall>\<beta>. \<beta> \<noteq> \<alpha> \<longrightarrow> ?\<iota> \<alpha> x \<beta> = e \<beta>)"
    by simp
  show ?thesis
    apply (intro exI[where x = ?\<iota>] conjI)
       apply (rule habel)
      using hhom apply blast
     using hinj apply blast
    using haxis apply blast
    done
qed

(** from \<S>67 Theorem 67.6: uniqueness of external direct sum.
    If (H_1, \<iota>_1) and (H_2, \<iota>_2) are both direct sums of a family {G_\<alpha>}_{\<alpha>\<in>J} of
    abelian groups (with injective homomorphisms \<iota>_i_\<alpha>: G_\<alpha> \<rightarrow> H_i making H_i the
    internal direct sum of their images), then H_1 \<cong> H_2 as abelian groups. **)
theorem Theorem_67_6_direct_sum_unique:
  fixes J :: "'i set"
    and G :: "'i \<Rightarrow> 'g set" and mul :: "'i \<Rightarrow> 'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and eG :: "'i \<Rightarrow> 'g" and invgG :: "'i \<Rightarrow> 'g \<Rightarrow> 'g"
    and H1 H2 :: "'h set" and mulH1 mulH2 :: "'h \<Rightarrow> 'h \<Rightarrow> 'h"
    and eH1 eH2 :: 'h and invgH1 invgH2 :: "'h \<Rightarrow> 'h"
    and \<iota>fam1 \<iota>fam2 :: "'i \<Rightarrow> 'g \<Rightarrow> 'h"
  assumes hG: "\<forall>\<alpha>\<in>J. top1_is_abelian_group_on (G \<alpha>) (mul \<alpha>) (eG \<alpha>) (invgG \<alpha>)"
      and "top1_is_direct_sum_of_on H1 mulH1 eH1 invgH1 J G mul eG \<iota>fam1"
      and "top1_is_direct_sum_of_on H2 mulH2 eH2 invgH2 J G mul eG \<iota>fam2"
  shows "top1_groups_isomorphic_on H1 mulH1 H2 mulH2"
proof -
  let ?DS = "top1_direct_sum_carrier J G eG"
  let ?mulDS = "\<lambda>f g. \<lambda>\<alpha>. if \<alpha> \<in> J then mul \<alpha> (f \<alpha>) (g \<alpha>) else eG \<alpha>"
  obtain \<Phi>1 where h\<Phi>1: "top1_group_iso_on ?DS ?mulDS H1 mulH1 \<Phi>1"
    using assms(2) unfolding top1_is_direct_sum_of_on_def by blast
  obtain \<Phi>2 where h\<Phi>2: "top1_group_iso_on ?DS ?mulDS H2 mulH2 \<Phi>2"
    using assms(3) unfolding top1_is_direct_sum_of_on_def by blast
  have hiso1: "top1_groups_isomorphic_on ?DS ?mulDS H1 mulH1"
    unfolding top1_groups_isomorphic_on_def using h\<Phi>1 by blast
  have hiso2: "top1_groups_isomorphic_on ?DS ?mulDS H2 mulH2"
    unfolding top1_groups_isomorphic_on_def using h\<Phi>2 by blast
  \<comment> \<open>H1 \<cong> DS \<cong> H2 by transitivity and symmetry.\<close>
  \<comment> \<open>Both Φ₁, Φ₂ are bijective homs DS → H_i. Construct Φ₂ ∘ Φ₁⁻¹ : H₁ → H₂.\<close>
  have hH1_group: "top1_is_group_on H1 mulH1 eH1 invgH1"
    using assms(2) unfolding top1_is_direct_sum_of_on_def top1_is_abelian_group_on_def by blast
  have hH2_group: "top1_is_group_on H2 mulH2 eH2 invgH2"
    using assms(3) unfolding top1_is_direct_sum_of_on_def top1_is_abelian_group_on_def by blast
  have hbij1: "bij_betw \<Phi>1 ?DS H1" and hhom1: "top1_group_hom_on ?DS ?mulDS H1 mulH1 \<Phi>1"
    using h\<Phi>1 unfolding top1_group_iso_on_def by blast+
  have hbij2: "bij_betw \<Phi>2 ?DS H2" and hhom2: "top1_group_hom_on ?DS ?mulDS H2 mulH2 \<Phi>2"
    using h\<Phi>2 unfolding top1_group_iso_on_def by blast+
  \<comment> \<open>Φ₁ inverse.\<close>
  have hinj1: "inj_on \<Phi>1 ?DS" using hbij1 unfolding bij_betw_def by blast
  let ?\<Psi> = "\<lambda>h. \<Phi>2 (the_inv_into ?DS \<Phi>1 h)"
  have hbij_inv1: "bij_betw (the_inv_into ?DS \<Phi>1) H1 ?DS"
    by (rule bij_betw_the_inv_into[OF hbij1])
  have hbij_comp: "bij_betw (\<Phi>2 \<circ> the_inv_into ?DS \<Phi>1) H1 H2"
    by (rule bij_betw_trans[OF hbij_inv1 hbij2])
  have hpsi_eq: "?\<Psi> = \<Phi>2 \<circ> the_inv_into ?DS \<Phi>1" by (rule ext) (simp add: comp_def)
  have hbij_psi: "bij_betw ?\<Psi> H1 H2"
    using hbij_comp unfolding hpsi_eq[symmetric] .
  have hhom_psi: "top1_group_hom_on H1 mulH1 H2 mulH2 ?\<Psi>"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    fix x assume hx: "x \<in> H1"
    have "the_inv_into ?DS \<Phi>1 x \<in> ?DS"
      using the_inv_into_into[OF hinj1] hbij1 hx unfolding bij_betw_def by blast
    thus "?\<Psi> x \<in> H2"
      using hhom2 unfolding top1_group_hom_on_def by blast
  next
    fix x y assume hx: "x \<in> H1" and hy: "y \<in> H1"
    have hxDS: "the_inv_into ?DS \<Phi>1 x \<in> ?DS"
      using the_inv_into_into[OF hinj1] hbij1 hx unfolding bij_betw_def by blast
    have hyDS: "the_inv_into ?DS \<Phi>1 y \<in> ?DS"
      using the_inv_into_into[OF hinj1] hbij1 hy unfolding bij_betw_def by blast
    have hsurj1: "\<Phi>1 ` ?DS = H1" using hbij1 unfolding bij_betw_def by blast
    \<comment> \<open>\<Phi>₁(inv(x) * inv(y)) = \<Phi>₁(inv(x)) * \<Phi>₁(inv(y)) = x * y.\<close>
    have hprod: "\<Phi>1 (?mulDS (the_inv_into ?DS \<Phi>1 x) (the_inv_into ?DS \<Phi>1 y)) = mulH1 x y"
    proof -
      have "\<Phi>1 (?mulDS (the_inv_into ?DS \<Phi>1 x) (the_inv_into ?DS \<Phi>1 y))
            = mulH1 (\<Phi>1 (the_inv_into ?DS \<Phi>1 x)) (\<Phi>1 (the_inv_into ?DS \<Phi>1 y))"
        using hhom1 hxDS hyDS unfolding top1_group_hom_on_def by blast
      also have "\<Phi>1 (the_inv_into ?DS \<Phi>1 x) = x"
        using f_the_inv_into_f[OF hinj1] hx hsurj1 by blast
      also have "\<Phi>1 (the_inv_into ?DS \<Phi>1 y) = y"
        using f_the_inv_into_f[OF hinj1] hy hsurj1 by blast
      finally show ?thesis .
    qed
    \<comment> \<open>So the_inv_into(x*y) = inv(x) * inv(y).\<close>
    have hmul_cl: "?mulDS (the_inv_into ?DS \<Phi>1 x) (the_inv_into ?DS \<Phi>1 y) \<in> ?DS"
      by (rule top1_direct_sum_carrier_mul_closed[OF hG hxDS hyDS])
    have "the_inv_into ?DS \<Phi>1 (mulH1 x y) = ?mulDS (the_inv_into ?DS \<Phi>1 x) (the_inv_into ?DS \<Phi>1 y)"
      using the_inv_into_f_f[OF hinj1 hmul_cl] hprod by simp
    hence "?\<Psi> (mulH1 x y) = \<Phi>2 (?mulDS (the_inv_into ?DS \<Phi>1 x) (the_inv_into ?DS \<Phi>1 y))"
      by simp
    also have "... = mulH2 (\<Phi>2 (the_inv_into ?DS \<Phi>1 x)) (\<Phi>2 (the_inv_into ?DS \<Phi>1 y))"
      using hhom2 hxDS hyDS unfolding top1_group_hom_on_def by blast
    finally show "?\<Psi> (mulH1 x y) = mulH2 (?\<Psi> x) (?\<Psi> y)" by simp
  qed
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
    using hhom_psi hbij_psi by blast
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
  shows "\<exists>f. bij_betw f S1 S2"
proof -
  \<comment> \<open>Munkres 67.8: Tensor with Z/2Z: G/2G is a vector space over Z/2Z of dimension
     equal to the rank. Dimension of a vector space is unique.
     Step 1: G \<cong> Z^S1 (free abelian on S1) and G \<cong> Z^S2 (free abelian on S2).
     Step 2: G/2G \<cong> (Z/2Z)^S1 \<cong> (Z/2Z)^S2.
     Step 3: Vector space dimension: |S1| = dim (Z/2Z)^S1 = dim (Z/2Z)^S2 = |S2|.
     Step 4: Hence |S1| = |S2|, i.e. there exists a bijection.\<close>
  \<comment> \<open>Step 1: Form quotient G/2G. G/2G is a vector space over Z/2Z with dimension = rank.\<close>
  let ?twoG = "{mul g g | g. g \<in> G}"
  have h_dim_S1: "\<exists>f. bij_betw f S1 (top1_quotient_group_carrier_on G mul ?twoG)" sorry
  have h_dim_S2: "\<exists>f. bij_betw f S2 (top1_quotient_group_carrier_on G mul ?twoG)" sorry
  \<comment> \<open>Step 2: Bijections S1 \<cong> G/2G \<cong> S2 compose to S1 \<cong> S2.\<close>
  show ?thesis
  proof -
    obtain f1 where hf1: "bij_betw f1 S1 (top1_quotient_group_carrier_on G mul ?twoG)"
      using h_dim_S1 by (by100 blast)
    obtain f2 where hf2: "bij_betw f2 S2 (top1_quotient_group_carrier_on G mul ?twoG)"
      using h_dim_S2 by (by100 blast)
    have hf2_inv: "bij_betw (the_inv_into S2 f2) (top1_quotient_group_carrier_on G mul ?twoG) S2"
      by (rule bij_betw_the_inv_into[OF hf2])
    have "bij_betw (the_inv_into S2 f2 \<circ> f1) S1 S2"
      by (rule bij_betw_trans[OF hf1 hf2_inv])
    thus ?thesis by (by100 blast)
  qed
qed

section \<open>\<S>68 Free Products of Groups\<close>

text \<open>Reduced words in a free product G_1 * G_2.\<close>
text \<open>Reduced words in the free product G_1 * G_2: non-empty alternating sequences
  w_1 w_2 ... w_n where each w_i is in G_1 \<setminus> {e_1} or G_2 \<setminus> {e_2}, and
  consecutive w_i's come from different factors.\<close>
definition top1_free_product_carrier ::
  "'g set \<Rightarrow> 'g \<Rightarrow> 'g set \<Rightarrow> 'g \<Rightarrow> (('g \<times> bool) list) set" where
  "top1_free_product_carrier G1 e1 G2 e2 =
     {ws. (\<forall>i<length ws.
              (snd (ws!i) \<longrightarrow> fst (ws!i) \<in> G1 \<and> fst (ws!i) \<noteq> e1)
            \<and> (\<not> snd (ws!i) \<longrightarrow> fst (ws!i) \<in> G2 \<and> fst (ws!i) \<noteq> e2))
        \<and> (\<forall>i. i+1 < length ws \<longrightarrow> snd (ws!i) \<noteq> snd (ws!(i+1)))}"
     \<comment> \<open>The boolean flag indicates which factor each element belongs to.
         Empty list represents the identity.\<close>

(** from \<S>68 Theorem 68.2: given a family of groups, a free product exists. **)
theorem Theorem_68_2_free_product_exists:
  assumes "\<forall>\<alpha>\<in>(J::'i set). top1_is_group_on (GG \<alpha>::'gg set) (mulGG \<alpha>) (eGG \<alpha>) (invgGG \<alpha>)"
  shows "\<exists>(G::'gg set) mul e invg \<iota>fam.
           top1_is_free_product_on G mul e invg GG mulGG \<iota>fam J"
proof -
  \<comment> \<open>Munkres 68.2: Construct G as the set of reduced words in the G\<alpha>'s.
     A word is a list [(i1, g1), (i2, g2), ...] with i_k \<in> J, g_k \<in> G_{i_k} \ {e_{i_k}},
     and consecutive indices differ. The empty list is the identity.
     Multiplication = concatenation + iterative reduction (cancel adjacent elements
     from the same group, contract e's).
     The natural inclusions \<iota>\<alpha>(g) = [(a, g)] are injective homomorphisms.\<close>
  \<comment> \<open>Step 1: Define the carrier G as reduced words (lists of (index, element) pairs
     with alternating indices and non-identity elements).\<close>
  \<comment> \<open>Step 2: Define multiplication as concatenation + iterative reduction.\<close>
  \<comment> \<open>Step 3: Verify group axioms.\<close>
  have hG_group: "\<exists>(G::'gg set) mul e invg.
      top1_is_group_on G mul e invg
    \<and> (\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<exists>g\<in>G. True)
    \<and> (\<forall>\<alpha>\<in>J. \<exists>\<iota>. inj_on \<iota> (GG \<alpha>) \<and> (\<forall>x\<in>GG \<alpha>. \<forall>y\<in>GG \<alpha>.
         \<iota> (mulGG \<alpha> x y) = mul (\<iota> x) (\<iota> y)))" sorry
  \<comment> \<open>Step 4: No nonempty reduced word represents the identity (freeness condition).\<close>
  have hG_free: "\<exists>(G::'gg set) mul e invg \<iota>fam.
      top1_is_group_on G mul e invg
    \<and> (\<forall>\<alpha>\<in>J. inj_on (\<iota>fam \<alpha>) (GG \<alpha>))
    \<and> (\<forall>indices word. length indices = length word \<longrightarrow> length indices > 0 \<longrightarrow>
        (\<forall>i<length indices. indices!i \<in> J \<and> word!i \<in> GG (indices!i)
                          \<and> \<iota>fam (indices!i) (word!i) \<noteq> e) \<longrightarrow>
        (\<forall>i. i + 1 < length indices \<longrightarrow> indices!i \<noteq> indices!(i+1)) \<longrightarrow>
        foldr mul (map (\<lambda>i. \<iota>fam (indices!i) (word!i)) [0..<length indices]) e \<noteq> e)" sorry
  show ?thesis sorry
qed

(** from \<S>68 Theorem 68.4: uniqueness of free product — any two
    free products of the same family are isomorphic. **)
theorem Theorem_68_4_free_product_unique:
  assumes "top1_is_free_product_on (G1::'g set) mul1 e1 invg1 GG mulGG \<iota>1 J"
      and "top1_is_free_product_on (G2::'g set) mul2 e2 invg2 GG mulGG \<iota>2 J"
  shows "top1_groups_isomorphic_on G1 mul1 G2 mul2"
proof -
  \<comment> \<open>Munkres 68.4: Both G1, G2 have the extension property (Lemma 68.3).
     Step 1: Define \<phi>: G1 \<rightarrow> G2 by extending the maps \<iota>2_\<alpha> \<circ> \<iota>1_\<alpha>\<inverse> on generators.
     Step 2: Similarly define \<psi>: G2 \<rightarrow> G1.
     Step 3: \<psi>\<circ>\<phi> extends id on the generators of G1, so \<psi>\<circ>\<phi> = id by uniqueness.
     Step 4: Similarly \<phi>\<circ>\<psi> = id. Hence \<phi> is an isomorphism.\<close>
  show ?thesis sorry
qed

(** from \<S>68 Theorem 68.7: if G = G_1 * G_2 is a free product and N_i \<lhd> G_i are
    normal, then (G_1 * G_2) / \<langle>\<langle>N_1 \<union> N_2\<rangle>\<rangle> \<cong> (G_1/N_1) * (G_2/N_2). **)
theorem Theorem_68_7_quotient_free_product:
  fixes G1 G2 :: "'g set"
    and mul1 mul2 :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e1 e2 :: 'g
    and invg1 invg2 :: "'g \<Rightarrow> 'g"
    and N1 N2 :: "'g set"
  assumes "top1_is_group_on G1 mul1 e1 invg1"
      and "top1_is_group_on G2 mul2 e2 invg2"
      and "top1_normal_subgroup_on G1 mul1 e1 invg1 N1"
      and "top1_normal_subgroup_on G2 mul2 e2 invg2 N2"
  shows "\<exists>(FP::'f set) mulFP eFP invgFP \<iota>fam12
          (FPQ::'fq set) mulFPQ eFPQ invgFPQ \<iota>famQ.
           top1_is_free_product_on FP mulFP eFP invgFP
             (\<lambda>i::nat. if i = 0 then G1 else G2)
             (\<lambda>i. if i = 0 then mul1 else mul2)
             \<iota>fam12 {0, 1}
         \<and> top1_is_free_product_on FPQ mulFPQ eFPQ invgFPQ
             (\<lambda>i::nat. if i = 0
                       then top1_quotient_group_carrier_on G1 mul1 N1
                       else top1_quotient_group_carrier_on G2 mul2 N2)
             (\<lambda>i::nat. top1_quotient_group_mul_on (if i = 0 then mul1 else mul2))
             \<iota>famQ {0, 1}
         \<and> top1_groups_isomorphic_on
             (top1_quotient_group_carrier_on FP mulFP
                (top1_normal_subgroup_generated_on FP mulFP eFP invgFP
                   (\<iota>fam12 0 ` N1 \<union> \<iota>fam12 1 ` N2)))
             (top1_quotient_group_mul_on mulFP)
             FPQ mulFPQ"
proof -
  \<comment> \<open>Munkres 68.7: The natural map \<pi>: G1*G2 \<rightarrow> (G1/N1)*(G2/N2) is a surjective
     homomorphism. Its kernel is exactly the normal closure of \<iota>1(N1) \<union> \<iota>2(N2).
     By the first isomorphism theorem, (G1*G2)/ker \<cong> (G1/N1)*(G2/N2).\<close>
  \<comment> \<open>Step 1: Build free products FP = G1*G2 and FPQ = (G1/N1)*(G2/N2).\<close>
  obtain FP mulFP eFP invgFP \<iota>fam12 where
      hFP: "top1_is_free_product_on FP mulFP eFP invgFP
        (\<lambda>i::nat. if i = 0 then G1 else G2) (\<lambda>i. if i = 0 then mul1 else mul2) \<iota>fam12 {0,1}"
    sorry
  \<comment> \<open>Step 2: Natural surjection \<pi>: FP \<rightarrow> FPQ with kernel = normal closure of \<iota>1(N1)\<union>\<iota>2(N2).\<close>
  have h_surj: "\<exists>\<pi>. top1_group_hom_on FP mulFP FP mulFP \<pi> \<and> \<pi> ` FP = FP" sorry
  \<comment> \<open>Step 3: First isomorphism theorem gives the result.\<close>
  show ?thesis sorry
qed

section \<open>\<S>69 Free Groups\<close>

text \<open>A free group on a set S is a group G together with \<iota>: S \<hookrightarrow> G such that
  \<iota>(S) generates G, \<iota> is injective, and (externally) for any group H and
  function \<phi>: S \<rightarrow> H there is a unique homomorphism \<psi>: G \<rightarrow> H with \<psi> \<circ> \<iota> = \<phi>.
  See top1_is_free_group_full_on (intrinsic) and top1_free_group_universal_prop
  (external) above.\<close>

(** from \<S>69 Theorem 69.2: free product of free groups on S1, S2 (disjoint)
    is the free group on S1 \<union> S2. **)
theorem Theorem_69_2:
  fixes G1 G2 :: "'g set"
    and mul1 mul2 :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e1 e2 :: 'g
    and invg1 invg2 :: "'g \<Rightarrow> 'g"
    and \<iota>1 \<iota>2 :: "'s \<Rightarrow> 'g"
    and S1 S2 :: "'s set"
  assumes "top1_is_free_group_full_on G1 mul1 e1 invg1 \<iota>1 S1"
      and "top1_is_free_group_full_on G2 mul2 e2 invg2 \<iota>2 S2"
      and "S1 \<inter> S2 = {}"
  shows "\<exists>(FP::'f set) mulFP eFP invgFP \<iota>fam12 \<iota>S12.
           top1_is_free_product_on FP mulFP eFP invgFP
             (\<lambda>i::nat. if i = 0 then G1 else G2)
             (\<lambda>i. if i = 0 then mul1 else mul2)
             \<iota>fam12 {0, 1}
         \<and> top1_is_free_group_full_on FP mulFP eFP invgFP \<iota>S12 (S1 \<union> S2)
         \<and> (\<forall>s\<in>S1. \<iota>S12 s = \<iota>fam12 0 (\<iota>1 s))
         \<and> (\<forall>s\<in>S2. \<iota>S12 s = \<iota>fam12 1 (\<iota>2 s))"
proof -
  \<comment> \<open>Munkres 69.2: G1 * G2 has reduced words alternating between G1 and G2 elements.
     Since G1 = free on S1 and G2 = free on S2, reduced words in G1*G2 are exactly
     reduced words in S1 \<union> S2 (with S1 \<inter> S2 = {}). So G1*G2 is free on S1\<union>S2.
     The injection \<iota>S12 maps s\<in>S1 to \<iota>fam12(0)(\<iota>1(s)) and s\<in>S2 to \<iota>fam12(1)(\<iota>2(s)).\<close>
  \<comment> \<open>Step 1: Build the free product FP = G1 * G2 (Theorem 68.2).\<close>
  obtain FP mulFP eFP invgFP \<iota>fam12 where
      hFP: "top1_is_free_product_on FP mulFP eFP invgFP
        (\<lambda>i::nat. if i = 0 then G1 else G2) (\<lambda>i. if i = 0 then mul1 else mul2) \<iota>fam12 {0,1}"
    sorry
  \<comment> \<open>Step 2: Since G1, G2 are free on S1, S2, reduced words in FP correspond to
     reduced words in S1 \<union> S2. Define \<iota>S12.\<close>
  have h_free_on_union: "\<exists>\<iota>S12. top1_is_free_group_full_on FP mulFP eFP invgFP \<iota>S12 (S1 \<union> S2)
    \<and> (\<forall>s\<in>S1. \<iota>S12 s = \<iota>fam12 0 (\<iota>1 s)) \<and> (\<forall>s\<in>S2. \<iota>S12 s = \<iota>fam12 1 (\<iota>2 s))" sorry
  show ?thesis sorry
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
  shows "\<exists>(H::'h set) mulH eH invgH \<phi> \<iota>H.
           top1_is_abelianization_of H mulH eH invgH G mul e invg \<phi>
         \<and> top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>H S
         \<and> (\<forall>s\<in>S. \<iota>H s = \<phi> (\<iota> s))"
proof -
  \<comment> \<open>Munkres 69.4: G is free on S, so G/[G,G] is the abelianization.
     The images \<phi>(\<iota>(s)) for s \<in> S freely generate G/[G,G] as an abelian group:
     Step 1: \<phi>(\<iota>(S)) generates H (since \<iota>(S) generates G and \<phi> is surjective).
     Step 2: No nontrivial integer combination of \<phi>(\<iota>(s))'s equals eH.
     Proof: if \<Sigma> n_s \<phi>(\<iota>(s)) = eH, then \<Sigma> n_s \<iota>(s) \<in> [G,G].
     But [G,G] consists of products of commutators, and a free group element
     that's a product of commutators has zero exponent sum in each generator.
     So all n_s = 0.\<close>
  \<comment> \<open>Step 1: Form the abelianization H = G/[G,G] via natural projection \<phi>.\<close>
  have h_abel: "\<exists>(H::'h set) mulH eH invgH \<phi>.
      top1_is_abelianization_of H mulH eH invgH G mul e invg \<phi>" sorry
  \<comment> \<open>Step 2: \<phi>(\<iota>(S)) generates H and satisfies no nontrivial integer relations
     (exponent sum argument in the free group).\<close>
  have h_free_abel: "\<exists>(H::'h set) mulH eH invgH \<phi> \<iota>H.
      top1_is_abelianization_of H mulH eH invgH G mul e invg \<phi>
    \<and> top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>H S
    \<and> (\<forall>s\<in>S. \<iota>H s = \<phi> (\<iota> s))" sorry
  show ?thesis sorry
qed

section \<open>\<S>70 The Seifert-van Kampen Theorem\<close>

section \<open>\<S>71 The Fundamental Group of a Wedge of Circles\<close>

text \<open>A wedge of circles at a common point p (Munkres §71): a Hausdorff space X
  with a family \<C>_\<alpha> (\<alpha>\<in>J) of subspaces, each homeomorphic to S^1, pairwise
  intersecting only at p, whose union is X. The topology on X is the weak
  topology: a set is closed iff its intersection with each C_\<alpha> is closed.\<close>
definition top1_is_wedge_of_circles_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'i set \<Rightarrow> 'a \<Rightarrow> bool" where
  "top1_is_wedge_of_circles_on X TX J p \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     is_hausdorff_on X TX \<and>
     p \<in> X \<and>
     (\<exists>C. (\<forall>\<alpha>\<in>J. C \<alpha> \<subseteq> X \<and> p \<in> C \<alpha>
             \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                      (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h))
        \<and> (\<Union>\<alpha>\<in>J. C \<alpha>) = X
        \<and> (\<forall>\<alpha>\<in>J. \<forall>\<beta>\<in>J. \<alpha> \<noteq> \<beta> \<longrightarrow> C \<alpha> \<inter> C \<beta> = {p})
        \<and> (\<forall>D. D \<subseteq> X \<longrightarrow>
             (closedin_on X TX D \<longleftrightarrow>
              (\<forall>\<alpha>\<in>J. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)))))"

text \<open>A polygonal region in R^2 with n \<ge> 3 sides: a closed convex polygon, i.e.,
  the convex hull of n vertices v_0, ..., v_{n-1} that are pairwise distinct and
  in convex position (no vertex lies in the convex hull of the others).
  The three conjuncts of the definition are: (i) vertices pairwise distinct,
  (ii) convex position (no vertex is a convex combination of the others),
  (iii) P is the convex hull as convex combinations of the vertices.\<close>
definition top1_is_polygonal_region_on :: "(real \<times> real) set \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_is_polygonal_region_on P n \<longleftrightarrow>
     n \<ge> 3 \<and>
     (\<exists>vx vy :: nat \<Rightarrow> real.
        (\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j))
      \<and> (\<forall>k<n. \<not> (\<exists>coeffs. (\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0)
                          \<and> coeffs k = 0
                          \<and> (\<Sum>i<n. coeffs i) = 1
                          \<and> vx k = (\<Sum>i<n. coeffs i * vx i)
                          \<and> vy k = (\<Sum>i<n. coeffs i * vy i)))
      \<and> P = {(x, y) | x y.
                \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0)
                       \<and> (\<Sum>i<n. coeffs i) = 1
                       \<and> x = (\<Sum>i<n. coeffs i * vx i)
                       \<and> y = (\<Sum>i<n. coeffs i * vy i)})"

text \<open>Edge scheme: a word w = y_1 y_2 ... y_n where each y_i is (label, orientation)
  specifying how boundary edges of a polygonal region are identified. Orientation
  True means forward, False means reversed.\<close>
type_synonym 'a top1_edge_scheme = "('a \<times> bool) list"

text \<open>X is the quotient space obtained from a polygonal region P (with n = length
  scheme sides, labelled by the scheme) by identifying boundary edges as the scheme
  specifies. The existential witnesses are: the polygonal region P; the quotient
  map q : P \<rightarrow> X; and the edge parametrization edge : nat \<Rightarrow> real \<Rightarrow> P (edge i
  parametrizes the i-th side of P). The conjuncts assert:
  (i) P is a polygonal region with length(scheme) sides;
  (ii) q is a quotient map;
  (iii) each edge i maps I into P;
  (iv) two edges with the same label are identified compatibly with their
      orientation (same bool \<Rightarrow> direct identification t\<sim>t; opposite bool \<Rightarrow>
      reversed identification t\<sim>1-t);
  (v) interior points of P (not on any scheme edge) have trivial q-fibre.\<close>
definition top1_quotient_of_scheme_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b top1_edge_scheme \<Rightarrow> bool" where
  "top1_quotient_of_scheme_on X TX scheme \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     (\<exists>P q (vx::nat\<Rightarrow>real) (vy::nat\<Rightarrow>real).
        top1_is_polygonal_region_on P (length scheme)
      \<and> top1_quotient_map_on P
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q
      \<comment> \<open>vx, vy are the polygon vertices, pairwise distinct and in convex position.\<close>
      \<and> (\<forall>i<length scheme. \<forall>j<length scheme.
             i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j))
      \<and> (\<forall>i<length scheme. (vx i, vy i) \<in> P)
      \<comment> \<open>Vertices are in cyclic order: non-adjacent edges don't share interior points.\<close>
      \<and> (\<forall>i<length scheme. \<forall>j<length scheme.
            i \<noteq> j \<longrightarrow> Suc i mod length scheme \<noteq> j \<longrightarrow> i \<noteq> Suc j mod length scheme \<longrightarrow>
            (\<forall>s\<in>{0<..<1}. \<forall>t\<in>{0<..<1}.
               ((1-s) * vx i + s * vx (Suc i mod length scheme),
                (1-s) * vy i + s * vy (Suc i mod length scheme))
             \<noteq> ((1-t) * vx j + t * vx (Suc j mod length scheme),
                (1-t) * vy j + t * vy (Suc j mod length scheme))))
      \<comment> \<open>The i-th edge is the segment from (vx i, vy i) to (vx ((i+1) mod n), vy ...).
          Same-label edges are identified with compatible orientation.\<close>
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
      \<comment> \<open>Interior points (not on any boundary edge) have singleton q-fibre.\<close>
      \<and> (\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
                    p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                          (1-t) * vy i + t * vy (Suc i mod length scheme)))
               \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')))"

text \<open>X is a polygonal quotient: there exists some scheme that produces X.\<close>
definition top1_is_polygonal_quotient_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_polygonal_quotient_on X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     (\<exists>scheme::(nat \<times> bool) list. top1_quotient_of_scheme_on X TX scheme)"

text \<open>Standard scheme for the n-fold torus: a_1 b_1 a_1\<inverse> b_1\<inverse> \<cdots> a_n b_n a_n\<inverse> b_n\<inverse>,
  i.e. a 4n-sided polygon with this edge-identification word.\<close>
definition top1_n_torus_scheme :: "nat \<Rightarrow> (nat \<times> bool) list" where
  "top1_n_torus_scheme n =
     concat (map (\<lambda>i. [(2*i, True), (2*i+1, True), (2*i, False), (2*i+1, False)]) [0..<n])"

text \<open>Standard scheme for the m-fold projective plane: a_1 a_1 a_2 a_2 \<cdots> a_m a_m,
  a 2m-sided polygon.\<close>
definition top1_m_projective_scheme :: "nat \<Rightarrow> (nat \<times> bool) list" where
  "top1_m_projective_scheme m =
     concat (map (\<lambda>i. [(i, True), (i, True)]) [0..<m])"

text \<open>n-fold torus T_n = quotient of a 4n-gon by the standard torus scheme.\<close>
definition top1_is_n_fold_torus_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_is_n_fold_torus_on X TX n \<longleftrightarrow>
     n > 0 \<and> top1_quotient_of_scheme_on X TX (top1_n_torus_scheme n)"

text \<open>n-fold dunce cap: quotient of B^2 where on S^1, q(z) = q(z') iff z' is a
  rotation of z by a multiple of 2\<pi>/n; on the interior, q is injective; interior
  and boundary orbits are separated.  The resulting space has \<pi>_1 = Z/nZ.\<close>
definition top1_is_dunce_cap_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_is_dunce_cap_on X TX n \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     n > 0 \<and>
     (\<exists>q. top1_quotient_map_on top1_B2 top1_B2_topology X TX q
        \<and> (\<forall>z\<in>top1_S1. \<forall>z'\<in>top1_S1.
              q z = q z' \<longleftrightarrow>
              (\<exists>k::nat. k < n \<and>
                 z' = (cos (2*pi*real k/real n) * fst z
                         - sin (2*pi*real k/real n) * snd z,
                       sin (2*pi*real k/real n) * fst z
                         + cos (2*pi*real k/real n) * snd z)))
        \<and> inj_on q (top1_B2 - top1_S1)
        \<and> (\<forall>z\<in>top1_B2 - top1_S1. \<forall>z'\<in>top1_S1. q z \<noteq> q z'))"

text \<open>m-fold projective plane P_m: quotient of a 2m-gon by the scheme a_1 a_1 ... a_m a_m.
  For m = 1 this would require a 2-gon (not a valid polygonal region, which requires
  n \<ge> 3), so we handle m = 1 separately: P_1 = real projective plane RP^2 = quotient
  of B^2 by antipodal identification on S^1 = the 2-fold dunce cap.\<close>
definition top1_is_m_fold_projective_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_is_m_fold_projective_on X TX m \<longleftrightarrow>
     (m = 1 \<and> top1_is_dunce_cap_on X TX (2::nat)) \<or>
     (m \<ge> 2 \<and> top1_quotient_of_scheme_on X TX (top1_m_projective_scheme m))"

text \<open>The torus T² = S¹ × S¹ (the 1-fold torus in Munkres' sense).\<close>
definition top1_is_torus_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_torus_on X TX \<longleftrightarrow>
     top1_is_n_fold_torus_on X TX 1"

text \<open>The standard closed 2-simplex {(x, y). x \<ge> 0 \<and> y \<ge> 0 \<and> x + y \<le> 1}.\<close>
definition top1_standard_simplex :: "(real \<times> real) set" where
  "top1_standard_simplex = {p. fst p \<ge> 0 \<and> snd p \<ge> 0 \<and> fst p + snd p \<le> 1}"

definition top1_standard_simplex_topology :: "(real \<times> real) set set" where
  "top1_standard_simplex_topology =
     subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
       top1_standard_simplex"

text \<open>Edges of the standard simplex (the three line segments on its boundary).\<close>
definition top1_standard_simplex_edges :: "(real \<times> real) set set" where
  "top1_standard_simplex_edges =
     { {p\<in>top1_standard_simplex. fst p = 0},
       {p\<in>top1_standard_simplex. snd p = 0},
       {p\<in>top1_standard_simplex. fst p + snd p = 1} }"

text \<open>Vertices of the standard simplex.\<close>
definition top1_standard_simplex_vertices :: "(real \<times> real) set" where
  "top1_standard_simplex_vertices = {(0, 0), (1, 0), (0, 1)}"

text \<open>Triangulable: X has a triangulation — a finite collection \<T> of closed subspaces,
  each homeomorphic to a 2-simplex, covering X, such that any two distinct triangles
  intersect in either \<emptyset>, a common vertex, or a common edge (the common-face property).
  We express the common-face condition via the homeomorphism images.\<close>
definition top1_is_triangulable_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_triangulable_on X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     (\<exists>(\<T> :: 'a set set) (h :: 'a set \<Rightarrow> (real \<times> real) \<Rightarrow> 'a).
        finite \<T>
      \<and> (\<Union>\<T>) = X
      \<and> (\<forall>T\<in>\<T>. T \<subseteq> X \<and> closedin_on X TX T
            \<and> top1_homeomorphism_on
                 top1_standard_simplex top1_standard_simplex_topology
                 T (subspace_topology X TX T) (h T))
      \<and> (\<forall>T1\<in>\<T>. \<forall>T2\<in>\<T>. T1 \<noteq> T2 \<longrightarrow>
            T1 \<inter> T2 = {}
          \<or> (\<exists>v1 v2. v1 \<in> top1_standard_simplex_vertices \<and>
                     v2 \<in> top1_standard_simplex_vertices \<and>
                     T1 \<inter> T2 = {h T1 v1} \<and> {h T1 v1} = {h T2 v2})
          \<or> (\<exists>E1\<in>top1_standard_simplex_edges. \<exists>E2\<in>top1_standard_simplex_edges.
                 T1 \<inter> T2 = h T1 ` E1 \<and> h T1 ` E1 = h T2 ` E2)))"

text \<open>Elementary scheme operations (Munkres §76): inductive rewrite rules on edge
  schemes preserving the resulting quotient topology. Munkres defines:
  (i) cyclic permutation (rotate), (ii) cancellation of aa\<inverse> (when length \<ge> 5),
  (iii) relabel one letter to a new fresh letter (and consistently flip the bool),
  (iv) cut: replace w_1 w_2 by w_1 c c\<inverse> w_2 for a fresh letter c, (v) paste: the
  reverse of cut when edges form an adjacent pair, (vi) inverse: flip an edge.\<close>
inductive top1_elementary_scheme_operation ::
  "'a top1_edge_scheme \<Rightarrow> 'a top1_edge_scheme \<Rightarrow> bool" where
    refl:     "top1_elementary_scheme_operation s s"
  | sym:      "top1_elementary_scheme_operation s t \<Longrightarrow>
               top1_elementary_scheme_operation t s"
  | trans:    "\<lbrakk>top1_elementary_scheme_operation s t;
                top1_elementary_scheme_operation t u\<rbrakk> \<Longrightarrow>
               top1_elementary_scheme_operation s u"
  | rotate:   "top1_elementary_scheme_operation (xs @ ys) (ys @ xs)"
  | cancel:   "top1_elementary_scheme_operation
                 (xs @ [(a, b), (a, \<not> b)] @ ys)
                 (xs @ ys)"
  | relabel:  "\<lbrakk>a \<notin> fst ` set s; a \<noteq> c\<rbrakk> \<Longrightarrow>
               top1_elementary_scheme_operation
                 s
                 (map (\<lambda>(x, b). (if x = c then a else x, b)) s)"
  | invert:   "top1_elementary_scheme_operation
                 s
                 (rev (map (\<lambda>(x, b). (x, \<not> b)) s))"
  | cut:      "\<lbrakk>c \<notin> fst ` set (xs @ ys)\<rbrakk> \<Longrightarrow>
               top1_elementary_scheme_operation
                 (xs @ ys)
                 (xs @ [(c, True), (c, False)] @ ys)"

text \<open>Subgroup index: H has index k in G iff there are exactly k left cosets g H.
  We represent the set of left cosets directly (does not require H to be normal).\<close>
definition top1_left_cosets_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set set" where
  "top1_left_cosets_on G mul H = { top1_group_coset_on G mul H g | g. g \<in> G }"

definition top1_subgroup_has_index_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_subgroup_has_index_on G mul H k \<longleftrightarrow>
     finite (top1_left_cosets_on G mul H) \<and>
     card (top1_left_cosets_on G mul H) = k"
     \<comment> \<open>Finite index only. Infinite-index subgroups are expressed by negating this
         predicate (or by asserting infinite (top1_left_cosets_on ...)), not by k = 0.\<close>


(** from \<S>71 Theorem 71.1: finite wedge of circles has free fundamental group
    generated by the individual circle loops. **)
theorem Theorem_71_1_wedge_of_circles_finite:
  fixes n :: nat and X :: "'a set" and TX :: "'a set set" and p :: 'a
  assumes "top1_is_wedge_of_circles_on X TX {..<n} p"
  shows "\<exists>(G::'g set) mul e invg (\<iota>::nat \<Rightarrow> 'g).
           top1_is_free_group_full_on G mul e invg \<iota> {..<n}
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX p)
             (top1_fundamental_group_mul X TX p)"
proof -
  \<comment> \<open>Munkres 71.1: Apply Seifert-van Kampen (Theorem 70.2) by induction on n.
     Base case n=1: X = S^1, \<pi>_1 = Z which is free on 1 generator.
     Inductive step: X = X_{n-1} \<cup> C_n where C_n \<cong> S^1.
     X_{n-1} \<inter> C_n = {p}, which is path-connected.
     By SvK, \<pi>_1(X) = \<pi>_1(X_{n-1}) * \<pi>_1(C_n) / trivial relations
     = free on (n-1) generators * Z = free on n generators.\<close>
  \<comment> \<open>Base: n=0 gives trivial group; n=1 gives \<pi>_1(S^1) \<cong> Z.\<close>
  have hbase: "n = 0 \<longrightarrow> ?thesis" sorry
  \<comment> \<open>Inductive step: decompose X = X_{n-1} \<union> C_n. Apply SvK.\<close>
  have hstep: "n > 0 \<longrightarrow> (\<exists>Xprev TXprev Cn.
      Xprev \<union> Cn = X \<and> Xprev \<inter> Cn = {p}
    \<and> top1_is_wedge_of_circles_on Xprev TXprev {..<n-1} p
    \<and> top1_groups_isomorphic_on
        (top1_fundamental_group_carrier Cn (subspace_topology X TX Cn) p)
        (top1_fundamental_group_mul Cn (subspace_topology X TX Cn) p)
        top1_Z_group top1_Z_mul)" sorry
  \<comment> \<open>By SvK (Theorem 70.2), \<pi>_1(X) \<cong> \<pi>_1(X_{n-1}) * \<pi>_1(C_n) / trivial = free on n gens.\<close>
  have hsvk: "n > 0 \<longrightarrow> ?thesis" sorry
  show ?thesis using hbase hsvk by (by100 blast)
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
  \<comment> \<open>Step 1: For each finite F \<subseteq> J, the sub-wedge X_F has free fundamental group on F.\<close>
  have hfinite: "\<forall>F. finite F \<and> F \<subseteq> J \<longrightarrow>
      (\<exists>(G::'g set) mul e invg \<iota>. top1_is_free_group_full_on G mul e invg \<iota> F
        \<and> top1_groups_isomorphic_on G mul
            (top1_fundamental_group_carrier X TX p)
            (top1_fundamental_group_mul X TX p))" sorry
  \<comment> \<open>Step 2: The direct limit of these free groups (as F ranges over finite subsets)
     is the free group on J.\<close>
  show ?thesis sorry
qed

section \<open>\<S>72 Adjoining a Two-Cell\<close>

(** from \<S>72 Theorem 72.1: attaching a 2-cell kills the homotopy class of
    the attaching map. There exists an isomorphism \<pi>_1(X, a) \<cong>
    \<pi>_1(A, a) / normal-closure(k_*[p]) where p is the standard loop of S^1
    and k : S^1 \<rightarrow> A is the restriction of h : B^2 \<rightarrow> X to the boundary. **)
theorem Theorem_72_1_attaching_two_cell:
  fixes X :: "'a set" and TX :: "'a set set" and A :: "'a set"
    and h :: "real \<times> real \<Rightarrow> 'a" and a :: 'a
  assumes "is_topology_on_strict X TX"
      and "is_hausdorff_on X TX"
      and "closedin_on X TX A"
      and "top1_path_connected_on A (subspace_topology X TX A)"
      and "top1_continuous_map_on top1_B2 top1_B2_topology X TX h"
      and "a \<in> A"
      \<comment> \<open>h restricted to Int(B²) = B² - S¹ is a homeomorphism onto X - A.\<close>
      and "top1_homeomorphism_on
             (top1_B2 - top1_S1)
             (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
             (X - A)
             (subspace_topology X TX (X - A))
             h"
      and "h ` top1_S1 \<subseteq> A"
      and "h (1, 0) = a"
  shows "\<exists>\<iota>.
            top1_continuous_map_on top1_S1 top1_S1_topology A
                 (subspace_topology X TX A) \<iota>
          \<and> (\<forall>z\<in>top1_S1. \<iota> z = h z)
          \<and> top1_groups_isomorphic_on
                (top1_fundamental_group_carrier X TX a)
                (top1_fundamental_group_mul X TX a)
                (top1_quotient_group_carrier_on
                   (top1_fundamental_group_carrier A (subspace_topology X TX A) a)
                   (top1_fundamental_group_mul A (subspace_topology X TX A) a)
                   (top1_normal_subgroup_generated_on
                      (top1_fundamental_group_carrier A (subspace_topology X TX A) a)
                      (top1_fundamental_group_mul A (subspace_topology X TX A) a)
                      (top1_fundamental_group_id A (subspace_topology X TX A) a)
                      (top1_fundamental_group_invg A (subspace_topology X TX A) a)
                      \<comment> \<open>Relator: the image under \<iota>_* of the class of the standard
                          S^1 loop p(s) = (cos 2\<pi>s, sin 2\<pi>s) based at (1, 0). This
                          class is {g. loop_equiv_on S^1 ((1,0)) p g} — the
                          equivalence class of p in \<pi>_1(S^1, (1,0)).\<close>
                      {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
                         A (subspace_topology X TX A) a \<iota>
                         {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                               (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}}))
                (top1_quotient_group_mul_on
                   (top1_fundamental_group_mul A (subspace_topology X TX A) a))"
proof -
  \<comment> \<open>Munkres 72.1: \<iota> = h restricted to S^1.\<close>
  let ?\<iota> = "\<lambda>z. h z"
  have h\<iota>_cont: "top1_continuous_map_on top1_S1 top1_S1_topology A
       (subspace_topology X TX A) ?\<iota>" sorry
  have h\<iota>_eq: "\<forall>z\<in>top1_S1. ?\<iota> z = h z" by simp
  \<comment> \<open>Step 1: \<pi>_1(X, a) is generated by \<pi>_1(A, a) (since X-A is contractible via h).\<close>
  \<comment> \<open>Step 2: The surjection \<pi>_1(A, a) \<rightarrow> \<pi>_1(X, a) has kernel = normal closure of [k\<circ>p],
     where p is the standard loop and k = h|S^1 = \<iota>.\<close>
  \<comment> \<open>This uses Seifert-van Kampen (Theorem 70.2) applied to a neighborhood of A in X
     and X-A, or equivalently, the pushout of \<pi>_1 along the attaching map.\<close>
  have hiso: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier X TX a)
        (top1_fundamental_group_mul X TX a)
        (top1_quotient_group_carrier_on
           (top1_fundamental_group_carrier A (subspace_topology X TX A) a)
           (top1_fundamental_group_mul A (subspace_topology X TX A) a)
           (top1_normal_subgroup_generated_on
              (top1_fundamental_group_carrier A (subspace_topology X TX A) a)
              (top1_fundamental_group_mul A (subspace_topology X TX A) a)
              (top1_fundamental_group_id A (subspace_topology X TX A) a)
              (top1_fundamental_group_invg A (subspace_topology X TX A) a)
              {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
                 A (subspace_topology X TX A) a ?\<iota>
                 {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                       (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}}))
        (top1_quotient_group_mul_on
           (top1_fundamental_group_mul A (subspace_topology X TX A) a))" sorry
  show ?thesis using h\<iota>_cont h\<iota>_eq hiso by (by100 blast)
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
  \<comment> \<open>Step 1: T is quotient of square \<Rightarrow> space A is wedge of 2 circles (1-skeleton).\<close>
  have hA_wedge: "\<exists>(A :: 'a set) TA p.
      top1_is_wedge_of_circles_on A TA {0::nat, 1} p \<and> A \<subseteq> T_torus" sorry
  \<comment> \<open>Step 2: \<pi>_1(A) is free on 2 generators \<alpha>, \<beta> (Theorem 71.1).\<close>
  have hpi1_A_free: "\<exists>(F::'g set) mulF eF invgF \<iota>.
      top1_is_free_group_full_on F mulF eF invgF \<iota> {0::nat, 1}" sorry
  \<comment> \<open>Step 3: Attaching the 2-cell kills the commutator \<alpha>\<beta>\<alpha>\<inverse>\<beta>\<inverse>.
     So \<pi>_1(T) \<cong> F({a,b})/\<langle>\<langle>aba\<inverse>b\<inverse>\<rangle>\<rangle> \<cong> Z\<times>Z.\<close>
  show ?thesis sorry
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
  have hA_circle: "\<exists>(A :: 'a set) TA.
      A \<subseteq> X \<and> top1_groups_isomorphic_on
        (top1_fundamental_group_carrier A TA x0)
        (top1_fundamental_group_mul A TA x0)
        top1_Z_group top1_Z_mul" sorry
  \<comment> \<open>The attaching map wraps S^1 n times around the circle A.\<close>
  \<comment> \<open>By Theorem 72.1: \<pi>_1(X) \<cong> Z/\<langle>\<langle>n\<rangle>\<rangle> = Z/nZ.\<close>
  show ?thesis sorry
qed

(** from \<S>70 Theorem 70.2 (Seifert-van Kampen, classical version): if X = U \<union> V
    with U, V, U \<inter> V open and path-connected, then \<pi>_1(X, x_0) is isomorphic to
    the free product of \<pi>_1(U, x_0) and \<pi>_1(V, x_0) amalgamated over \<pi>_1(U \<inter> V, x_0).
    Equivalently, the images i_*(\<pi>_1(U)) and j_*(\<pi>_1(V)) generate \<pi>_1(X), and the
    kernel of the natural surjection is the normal subgroup generated by elements
    of the form (i_1)_*(\<gamma>) \<cdot> ((i_2)_*(\<gamma>))^{-1} for \<gamma> \<in> \<pi>_1(U \<inter> V). **)
theorem Theorem_70_2_SvK:
  assumes "is_topology_on_strict X TX" and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and "top1_path_connected_on U (subspace_topology X TX U)"
      and "top1_path_connected_on V (subspace_topology X TX V)"
      and "x0 \<in> U \<inter> V"
  shows "\<exists>(FP::'f set) mulFP eFP invgFP \<iota>fam.
           top1_is_free_product_on FP mulFP eFP invgFP
             (\<lambda>i::nat. if i = 0
                then top1_fundamental_group_carrier U (subspace_topology X TX U) x0
                else top1_fundamental_group_carrier V (subspace_topology X TX V) x0)
             (\<lambda>i. if i = 0
                then top1_fundamental_group_mul U (subspace_topology X TX U) x0
                else top1_fundamental_group_mul V (subspace_topology X TX V) x0)
             \<iota>fam {0, 1}
         \<and> top1_groups_isomorphic_on
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)
             (top1_quotient_group_carrier_on FP mulFP
                (top1_normal_subgroup_generated_on FP mulFP eFP invgFP
                   { mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on
                        (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0
                        U (subspace_topology X TX U) x0 (\<lambda>x. x) c))
                          (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on
                            (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0
                            V (subspace_topology X TX V) x0 (\<lambda>x. x) c)))
                    | c. c \<in> top1_fundamental_group_carrier
                           (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0 }))
             (top1_quotient_group_mul_on mulFP)"
proof -
  \<comment> \<open>Seifert-van Kampen: \<pi>_1(X, x_0) \<cong> (\<pi>_1(U) \<star> \<pi>_1(V)) / \<langle>\<langle>{i_1(\<gamma>) \<cdot> i_2(\<gamma>)\<inverse> |
      \<gamma> \<in> \<pi>_1(U\<inter>V)}\<rangle>\<rangle>: the amalgamated free product over \<pi>_1(U\<inter>V).\<close>
  let ?TU = "subspace_topology X TX U" and ?TV = "subspace_topology X TX V"
  let ?TUV = "subspace_topology X TX (U \<inter> V)"
  let ?\<pi>U = "top1_fundamental_group_carrier U ?TU x0"
  let ?\<pi>V = "top1_fundamental_group_carrier V ?TV x0"
  let ?\<pi>X = "top1_fundamental_group_carrier X TX x0"
  \<comment> \<open>Step 1: Construct the free product FP = \<pi>_1(U) \<star> \<pi>_1(V) (exists by Theorem 68.2).\<close>
  obtain FP mulFP eFP invgFP \<iota>fam where
      hFP: "top1_is_free_product_on FP mulFP eFP invgFP
             (\<lambda>i::nat. if i = 0 then ?\<pi>U else ?\<pi>V)
             (\<lambda>i. if i = 0 then top1_fundamental_group_mul U ?TU x0
                  else top1_fundamental_group_mul V ?TV x0)
             \<iota>fam {0, 1}"
    sorry
  \<comment> \<open>Step 2: Define the natural map j: FP \<rightarrow> \<pi>_1(X) induced by the inclusions U, V \<hookrightarrow> X.\<close>
  \<comment> \<open>Step 3 (Surjectivity): By Theorem 59.1, every loop in X decomposes into loops in U or V.
     Hence j is surjective onto \<pi>_1(X).\<close>
  have hj_surj: "\<exists>j. top1_group_hom_on FP mulFP ?\<pi>X (top1_fundamental_group_mul X TX x0) j
      \<and> j ` FP = ?\<pi>X" sorry
  \<comment> \<open>Step 4 (Kernel): The kernel of j is the normal subgroup N generated by
     {i_1(\<gamma>) \<cdot> i_2(\<gamma>)\<inverse> | \<gamma> \<in> \<pi>_1(U\<inter>V)}.
     These elements are clearly in ker(j) since the two inclusions U\<inter>V \<hookrightarrow> U and U\<inter>V \<hookrightarrow> V
     agree when composed with the inclusions U, V \<hookrightarrow> X.
     Conversely, any element of ker(j) can be reduced to a product of such relators
     by the same Lebesgue-number subdivision argument as in Theorem 59.1.\<close>
  have hker: "\<exists>j. top1_group_hom_on FP mulFP ?\<pi>X (top1_fundamental_group_mul X TX x0) j
      \<and> top1_group_kernel_on FP (top1_fundamental_group_id X TX x0) j
        = top1_normal_subgroup_generated_on FP mulFP eFP invgFP
           { mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on
                (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c))
                    (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on
                      (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
              | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 }" sorry
  \<comment> \<open>Step 5 (First isomorphism theorem): j induces FP/N \<cong> \<pi>_1(X).\<close>
  show ?thesis using hFP hj_surj hker sorry
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
  have hcompact: "top1_compact_on X TX" sorry
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
  \<comment> \<open>Step 1: All vertices of the 4n-gon are identified to one point (1-skeleton is a wedge).\<close>
  have h_1skel: "\<exists>(A :: 'a set) TA.
      A \<subseteq> X \<and> top1_is_wedge_of_circles_on A TA {..<2*n} x0" sorry
  \<comment> \<open>Step 2: Applying Theorem 72.1 (attaching the 2-cell) gives the presentation.\<close>
  have h_attach: "\<exists>(A :: 'a set) TA.
      A \<subseteq> X \<and> top1_groups_isomorphic_on
        (top1_fundamental_group_carrier X TX x0)
        (top1_fundamental_group_mul X TX x0)
        (top1_quotient_group_carrier_on
           (top1_fundamental_group_carrier A TA x0)
           (top1_fundamental_group_mul A TA x0)
           (top1_normal_subgroup_generated_on
              (top1_fundamental_group_carrier A TA x0)
              (top1_fundamental_group_mul A TA x0)
              (top1_fundamental_group_id A TA x0)
              (top1_fundamental_group_invg A TA x0)
              {top1_fundamental_group_id A TA x0}))
        (top1_quotient_group_mul_on (top1_fundamental_group_mul A TA x0))" sorry
  show ?thesis sorry
qed

(** from \<S>74 Theorem 74.4: \<pi>_1(P_m) has presentation \<langle>a_1, \<dots>, a_m | a_1\<^sup>2 \<cdots> a_m\<^sup>2\<rangle>.
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
  \<comment> \<open>Step 1: 1-skeleton is a wedge of m circles.\<close>
  have h_1skel: "\<exists>(A :: 'a set) TA.
      A \<subseteq> X \<and> top1_is_wedge_of_circles_on A TA {..<m} x0" sorry
  \<comment> \<open>Step 2: Attaching the 2-cell with relator a_1^2...a_m^2 gives the presentation.\<close>
  have h_attach: "\<exists>(A :: 'a set) TA.
      A \<subseteq> X \<and> top1_groups_isomorphic_on
        (top1_fundamental_group_carrier X TX x0)
        (top1_fundamental_group_mul X TX x0)
        (top1_quotient_group_carrier_on
           (top1_fundamental_group_carrier A TA x0)
           (top1_fundamental_group_mul A TA x0)
           (top1_normal_subgroup_generated_on
              (top1_fundamental_group_carrier A TA x0)
              (top1_fundamental_group_mul A TA x0)
              (top1_fundamental_group_id A TA x0)
              (top1_fundamental_group_invg A TA x0)
              {top1_fundamental_group_id A TA x0}))
        (top1_quotient_group_mul_on (top1_fundamental_group_mul A TA x0))" sorry
  show ?thesis sorry
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
  shows "\<exists>(H::'h set) mulH eH invgH \<phi>.
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
  have h_comm_normal: "top1_normal_subgroup_on ?G ?mul ?e ?inv ?comm" sorry
  \<comment> \<open>Step 2: G/[G,G] is an abelian group with the natural projection \<phi>.\<close>
  have h_quotient_abelian: "\<exists>\<phi>. top1_group_hom_on ?G ?mul
      (top1_quotient_group_carrier_on ?G ?mul ?comm)
      (top1_quotient_group_mul_on ?mul) \<phi>
    \<and> \<phi> ` ?G = top1_quotient_group_carrier_on ?G ?mul ?comm
    \<and> top1_group_kernel_on ?G (top1_quotient_group_mul_on ?mul ?comm ?comm) \<phi> = ?comm" sorry
  show ?thesis sorry
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
  \<comment> \<open>Step 2: Abelianizing kills all commutators, making the relator trivial.
     So H_1(T_n) = Z^{2n} (free abelian on 2n generators).\<close>
  show ?thesis sorry
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
  \<comment> \<open>Step 2: Abelianize: H = Z^m / \<langle>2(a_1+...+a_m)\<rangle>.
     Torsion = Z/2Z, free part = Z^{m-1}.\<close>
  have h_decomp: "\<exists>(H::'h set) mulH eH invgH. card (top1_torsion_subgroup_on H mulH eH) = 2
      \<and> (\<exists>(K::'h set). K \<subseteq> H
          \<and> top1_is_free_abelian_group_full_on K mulH eH invgH (\<lambda>i. undefined) {..<m-1})" sorry
  show ?thesis sorry
qed

section \<open>*\<S>78 Constructing Compact Surfaces\<close>

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
  have h_simplex_poly: "top1_is_polygonal_region_on top1_standard_simplex 3" sorry
  \<comment> \<open>Step 3: Assemble with quotient map q = identity on interior, edge-pasting on boundary.\<close>
  show ?thesis sorry
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
  obtain \<T> q where h\<T>: "finite \<T>" "\<T> \<noteq> {}"
      and hcovers: "(\<Union>T\<in>\<T>. q ` T) = X"
    using Theorem_78_1_triangulable_surface[OF assms(1,3)] sorry
  \<comment> \<open>Iteratively merge adjacent triangles into a single polygon.\<close>
  show ?thesis sorry
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
  \<comment> \<open>Reduce the scheme via elementary operations to standard form.\<close>
  have "\<exists>scheme. top1_quotient_of_scheme_on X TX scheme
      \<and> (scheme = [] \<or>
         (\<exists>n>0. scheme = top1_n_torus_scheme n) \<or>
         (\<exists>m>0. scheme = top1_m_projective_scheme m))" sorry
  show ?thesis sorry
qed

section \<open>Chapter 13: Classification of Covering Spaces\<close>

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
  show "top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'" sorry
next
  \<comment> \<open>Backward: if subgroup images equal, use path-lifting to construct h.\<close>
  assume hH_eq: "top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
  \<comment> \<open>For e \<in> E, choose path \<alpha> in E from e0 to e. Define h(e) = lift of p\<circ>\<alpha> in E' starting at e0'.
     Equal subgroups guarantee the lift exists and is well-defined.\<close>
  show "\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e) \<and> h e0 = e0'" sorry
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
  \<comment> \<open>Let e1' = h(e0). Choose path \<gamma> in E' from e0' to e1'. Set c = [p'\<circ>\<gamma>].\<close>
  let ?e1' = "h e0"
  have h_path_exists: "\<exists>\<gamma>. top1_is_path_on E' TE' e0' ?e1' \<gamma>" sorry
  have h_conjugacy: "\<exists>c\<in>top1_fundamental_group_carrier B TB b0.
      top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    (top1_fundamental_group_invg B TB b0 c)) ` H))
          (top1_fundamental_group_image_hom E' TE' e0' B TB b0 p')" sorry
  show "\<exists>c \<in> top1_fundamental_group_carrier B TB b0.
      top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
      = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    (top1_fundamental_group_invg B TB b0 c)) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)" sorry
next
  \<comment> \<open>Backward: conjugacy means subgroups differ by a basepoint change in E'.
     Theorem 79.2 applies after adjusting basepoints.\<close>
  assume "\<exists>c \<in> top1_fundamental_group_carrier B TB b0.
      top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
      = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    (top1_fundamental_group_invg B TB b0 c)) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
  \<comment> \<open>Conjugate subgroups \<Rightarrow> there exists e1' with p'(e1')=b0 s.t. the subgroups
     become equal after basepoint change. Then Theorem 79.2 gives the equivalence.\<close>
  have "\<exists>e1'. e1' \<in> E' \<and> p' e1' = b0 \<and>
      top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' e1' B TB b0 p'" sorry
  show "\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e)" sorry
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
            unfolding top1_loop_equiv_on_def by (by100 blast)
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
          by (by100 blast)
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
        hcovE assms(10) hcovE' assms(11) assms(6,7,8,9)]] hRHS by (by100 blast)
qed

(** from \<S>80 Theorem 80.3: universal covering factors through any covering **)
theorem Theorem_80_3_universal:
  assumes "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "is_topology_on_strict Y TY"
      and "top1_covering_map_on E TE B TB p"
      and "top1_simply_connected_on E TE"
      and "top1_covering_map_on Y TY B TB r"
  shows "\<exists>q. top1_covering_map_on E TE Y TY q \<and> (\<forall>e\<in>E. r (q e) = p e)"
proof -
  \<comment> \<open>Munkres 80.3: Define q: E \<rightarrow> Y by path-lifting. For e \<in> E, choose path \<alpha> in E
     from e0 to e. Lift r\<inverse> \<circ> p \<circ> \<alpha> to Y starting at y0 (where r(y0)=b0).
     The lift's endpoint is q(e). Well-defined because E is simply connected.\<close>
  obtain e0 where he0: "e0 \<in> E" sorry
  let ?b0 = "p e0"
  obtain y0 where hy0: "y0 \<in> Y" and hry0: "r y0 = ?b0" sorry
  \<comment> \<open>For each e \<in> E, pick path \<alpha> from e0 to e. Lift p\<circ>\<alpha> to Y starting at y0.
     Simple connectivity ensures uniqueness (different \<alpha>'s give same endpoint).\<close>
  have "\<exists>q. (\<forall>e\<in>E. q e \<in> Y) \<and> (\<forall>e\<in>E. r (q e) = p e)
      \<and> top1_continuous_map_on E TE Y TY q" sorry
  \<comment> \<open>q is a covering map: evenly covered because p and r both are.\<close>
  show ?thesis sorry
qed

text \<open>Strict version of Theorem_80_3 — same statement but with simply_connected_strict.\<close>
corollary Theorem_80_3_universal_strict:
  assumes "top1_simply_connected_strict E TE"
      and "is_topology_on_strict B TB"
      and "is_topology_on_strict Y TY"
      and "top1_covering_map_on E TE B TB p"
      and "top1_covering_map_on Y TY B TB r"
  shows "\<exists>q. top1_covering_map_on E TE Y TY q \<and> (\<forall>e\<in>E. r (q e) = p e)"
  using Theorem_80_3_universal[of E TE B TB Y TY p r]
    top1_simply_connected_strict_imp[OF assms(1)]
    top1_simply_connected_strict_is_topology_strict[OF assms(1)]
    assms(2-5) by (by100 blast)

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
  have hCov_group: "\<exists>eC invgC. top1_is_group_on ?Cov (\<lambda>h k e. h (k e)) eC invgC" sorry
  \<comment> \<open>Step 2: Define \<Phi> and show it's a well-defined homomorphism into N(H)/H.\<close>
  have h\<Phi>_hom: "\<exists>\<Phi>. top1_group_hom_on ?Cov (\<lambda>h k e. h (k e))
      (top1_quotient_group_carrier_on
         (top1_normalizer_on
            (top1_fundamental_group_carrier B TB b0)
            (top1_fundamental_group_mul B TB b0)
            (top1_fundamental_group_invg B TB b0) ?H)
         (top1_fundamental_group_mul B TB b0) ?H)
      (top1_quotient_group_mul_on (top1_fundamental_group_mul B TB b0)) \<Phi>" sorry
  \<comment> \<open>Step 3: \<Phi> is injective (if h(e0)=e0 then h=id by unique lifting) and surjective
     (for [c] \<in> N(H)/H, lift c starting at e0 to get e1; the unique covering
     transformation mapping e0 to e1 is the preimage).\<close>
  have h\<Phi>_bij: "\<exists>\<Phi>. bij_betw \<Phi> ?Cov
      (top1_quotient_group_carrier_on
         (top1_normalizer_on
            (top1_fundamental_group_carrier B TB b0)
            (top1_fundamental_group_mul B TB b0)
            (top1_fundamental_group_invg B TB b0) ?H)
         (top1_fundamental_group_mul B TB b0) ?H)" sorry
  show ?thesis using hCov_group h\<Phi>_hom h\<Phi>_bij sorry
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
  \<comment> \<open>Step 1: Define E as the set of right cosets [\<alpha>]H.\<close>
  have hE_def: "\<exists>E p. (\<forall>e\<in>E. p e \<in> B) \<and> p ` E = B" sorry
  \<comment> \<open>Step 2: Define TE using basis sets B(U, [\<alpha>]) for path-connected open U in B.\<close>
  have hTE_basis: "\<exists>E TE. is_topology_on_strict E TE" sorry
  \<comment> \<open>Step 3: p is a covering map (evenly covered neighborhoods from semilocal simple connectivity).\<close>
  have hp_covering: "\<exists>E TE p. top1_covering_map_on E TE B TB p" sorry
  \<comment> \<open>Step 4: E is path-connected and locally path-connected.\<close>
  have hE_conn: "\<exists>E TE. top1_path_connected_on E TE \<and> top1_locally_path_connected_on E TE" sorry
  \<comment> \<open>Step 5: p_*(\<pi>_1(E, e0)) = H.\<close>
  have hH_match: "\<exists>E TE p e0. top1_fundamental_group_image_hom E TE e0 B TB b0 p = H" sorry
  show ?thesis sorry
qed

section \<open>Chapter 14: Applications to Group Theory\<close>

section \<open>\<S>83 Covering Spaces of a Graph\<close>

text \<open>An arc is a space homeomorphic to the closed unit interval [0, 1].\<close>
definition top1_is_arc_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_arc_on X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     (\<exists>h. top1_homeomorphism_on I_set I_top X TX h)"

text \<open>Endpoints of an arc A are the two (distinct) points p, q such that
  A - p and A - q are both connected.\<close>
definition top1_arc_endpoints_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set" where
  "top1_arc_endpoints_on A TA =
     {p. p \<in> A \<and> top1_connected_on (A - {p}) (subspace_topology A TA (A - {p}))}"

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

(** from \<S>83 Theorem 83.2: any covering space of a graph is itself a graph. **)
theorem Theorem_83_2_covering_of_graph_is_graph:
  assumes "top1_is_graph_on B TB"
      and "top1_covering_map_on E TE B TB p"
  shows "top1_is_graph_on E TE"
proof -
  \<comment> \<open>Munkres 83.2: Each arc A in B lifts to arcs in E (sheets over A).
     The covering map p is a local homeomorphism, so lifts of arcs are arcs.
     The intersection condition and weak topology lift from B to E.\<close>
  obtain \<A>B where hAB: "(\<forall>A\<in>\<A>B. A \<subseteq> B \<and> top1_is_arc_on A (subspace_topology B TB A))"
      and hcover: "(\<Union>\<A>B) = B"
    using assms(1) unfolding top1_is_graph_on_def by (by100 auto)
  \<comment> \<open>Step 1: Lift each arc A to its sheets in E.\<close>
  have "\<exists>\<A>E. (\<forall>A\<in>\<A>E. A \<subseteq> E \<and> top1_is_arc_on A (subspace_topology E TE A))
      \<and> (\<Union>\<A>E) = E
      \<and> (\<forall>A\<in>\<A>E. \<forall>C\<in>\<A>E. A \<noteq> C \<longrightarrow>
           A \<inter> C \<subseteq> top1_arc_endpoints_on A (subspace_topology E TE A)
         \<and> finite (A \<inter> C) \<and> card (A \<inter> C) \<le> 2)
      \<and> (\<forall>D. D \<subseteq> E \<longrightarrow>
           (closedin_on E TE D \<longleftrightarrow>
            (\<forall>A\<in>\<A>E. closedin_on A (subspace_topology E TE A) (A \<inter> D))))" sorry
  \<comment> \<open>Step 2: E is Hausdorff (covering space of Hausdorff is Hausdorff).\<close>
  have "is_hausdorff_on E TE" sorry
  show ?thesis unfolding top1_is_graph_on_def sorry
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
  shows "\<exists>(G::'g set) mul e invg (\<iota>::'s \<Rightarrow> 'g) S.
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
  \<comment> \<open>Step 1: Choose maximal tree T.\<close>
  obtain T where hT: "T \<subseteq> X" and hT_tree: "top1_is_tree_on T (subspace_topology X TX T)"
    sorry
  \<comment> \<open>Step 2: Collapsing T gives a wedge of circles.\<close>
  have "\<exists>W TW J p. top1_is_wedge_of_circles_on W TW J p
      \<and> top1_homotopy_equivalence_on X TX W TW
           (\<lambda>x. SOME w. True) (\<lambda>w. SOME x. True)" sorry
  \<comment> \<open>Step 3: Free group from wedge of circles (Theorem 71.3).\<close>
  show ?thesis sorry
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
  \<comment> \<open>Step 1: Realize G as \<pi>_1 of a wedge of circles X.\<close>
  have "\<exists>(X::'a set) TX x0. top1_is_graph_on X TX \<and> top1_connected_on X TX \<and> x0 \<in> X
      \<and> top1_groups_isomorphic_on G mul
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)" sorry
  \<comment> \<open>Step 2: H \<le> G \<cong> \<pi>_1(X) gives a covering space E of X with p_*(\<pi>_1(E)) \<cong> H.\<close>
  \<comment> \<open>Step 3: E is a graph (Theorem 83.2). \<pi>_1(E) is free (Theorem 84.7). H \<cong> \<pi>_1(E) is free.\<close>
  show ?thesis sorry
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
  \<comment> \<open>Step 1: Realize F as \<pi>_1 of wedge X of n+1 circles. Build k-sheeted covering E.\<close>
  have "\<exists>(X::'a set) TX x0 E TE p.
      top1_is_graph_on X TX \<and> top1_connected_on X TX
    \<and> top1_covering_map_on E TE X TX p
    \<and> top1_is_graph_on E TE \<and> top1_connected_on E TE" sorry
  \<comment> \<open>Step 2: Euler characteristic computation gives rank kn+1.\<close>
  \<comment> \<open>Step 3: H \<cong> \<pi>_1(E) is free on kn+1 generators.\<close>
  show ?thesis sorry
qed

end
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 























































































































































































































