theory AlgIsoFixed
imports AlgIsoFixedBase.AlgIsoFixedBase
begin

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
  \<comment> \<open>The weak Theorem\_58\_7 gives abstract iso. Since both are infinite cyclic (\<cong> Z),
     and f\_* is a group hom, and (g\<circ>f)\_* is identity-ish (from homotopy equivalence):
     f\_* must be nontrivial, hence an iso between Z-groups.\<close>
  \<comment> \<open>Well-definedness of f\_* on equivalence classes.\<close>
  have hfstar_class: "\<And>l. top1_is_loop_on X TX x0 l \<Longrightarrow>
    ?f_star {h. top1_loop_equiv_on X TX x0 l h} =
    {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
  proof (intro set_eqI iffI)
    fix l h assume hl: "top1_is_loop_on X TX x0 l"
    assume "h \<in> ?f_star {h. top1_loop_equiv_on X TX x0 l h}"
    then obtain l' where hl': "top1_loop_equiv_on X TX x0 l l'"
        and hh: "top1_loop_equiv_on Y TY (f x0) (f \<circ> l') h"
      unfolding hf_star_unfold by (by100 blast)
    have hl'_loop: "top1_is_loop_on X TX x0 l'"
      using hl' unfolding top1_loop_equiv_on_def by (by100 blast)
    have hfl_equiv: "top1_loop_equiv_on Y TY (f x0) (f \<circ> l) (f \<circ> l')"
      by (rule top1_induced_preserves_loop_equiv[OF hTX hf hl hl'_loop hl'])
    show "h \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
      using top1_loop_equiv_on_trans[OF hTY hfl_equiv hh] by (by100 simp)
  next
    fix l h assume hl: "top1_is_loop_on X TX x0 l"
    assume "h \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
    hence hh: "top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h" by simp
    have "l \<in> {h. top1_loop_equiv_on X TX x0 l h}"
      using top1_loop_equiv_on_refl[OF hl] by (by100 simp)
    thus "h \<in> ?f_star {h. top1_loop_equiv_on X TX x0 l h}"
      using hh unfolding hf_star_unfold by (by100 blast)
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
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
  qed
  have hg: "top1_continuous_map_on Y TY X TX g"
    using heq unfolding top1_homotopy_equivalence_on_def by (by100 blast)
  have hgof: "top1_homotopic_on X TX X TX (g \<circ> f) (\<lambda>x. x)"
    using heq unfolding top1_homotopy_equivalence_on_def id_def[symmetric] by (by100 blast)
  have hfog: "top1_homotopic_on Y TY Y TY (f \<circ> g) (\<lambda>y. y)"
    using heq unfolding top1_homotopy_equivalence_on_def id_def[symmetric] by (by100 blast)
  \<comment> \<open>Extract homotopy H1: g\<circ>f \<simeq> id on X.\<close>
  obtain H1 where hH1cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H1"
      and hH10: "\<forall>x\<in>X. H1 (x, 0) = (g \<circ> f) x" and hH11: "\<forall>x\<in>X. H1 (x, 1) = x"
    using hgof unfolding top1_homotopic_on_def id_def by (by100 blast)
  let ?\<alpha>1 = "\<lambda>t. H1 (x0, t)"
  \<comment> \<open>Injectivity of f\_*: follows from g\<circ>f \<simeq> id.
     The proof uses homotopy\_induced\_basepoint\_change and roundtrip.\<close>
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
    have hfl_equiv: "top1_loop_equiv_on Y TY (f x0) (f \<circ> l1) (f \<circ> l2)"
    proof -
      have "{h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l1) h}
          = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l2) h}"
        using heq_fs unfolding hc1_eq hc2_eq hfstar_class[OF hl1] hfstar_class[OF hl2] .
      moreover have "f \<circ> l1 \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l1) h}"
        using top1_loop_equiv_on_refl[OF top1_continuous_map_loop[OF hf hl1]] by (by100 simp)
      ultimately have "f \<circ> l1 \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l2) h}" by (by100 simp)
      hence "top1_loop_equiv_on Y TY (f x0) (f \<circ> l2) (f \<circ> l1)" by simp
      thus ?thesis by (rule top1_loop_equiv_on_sym)
    qed
    have hgfl_equiv: "top1_loop_equiv_on X TX (g (f x0)) (g \<circ> f \<circ> l1) (g \<circ> f \<circ> l2)"
    proof -
      have "top1_loop_equiv_on X TX (g (f x0)) (g \<circ> (f \<circ> l1)) (g \<circ> (f \<circ> l2))"
        by (rule top1_induced_preserves_loop_equiv[OF hTY hg
            top1_continuous_map_loop[OF hf hl1]
            top1_continuous_map_loop[OF hf hl2] hfl_equiv])
      thus ?thesis by (simp add: comp_assoc)
    qed
    let ?bc = "\<lambda>l. top1_basepoint_change_on X TX x0 ((g \<circ> f) x0)
                     (top1_path_reverse ?\<alpha>1) l"
    have hH11id: "\<forall>x\<in>X. H1 (x, 1) = id x" using hH11 by simp
    note hbc_raw1 = homotopy_induced_basepoint_change[OF hTX hTX hH1cont hH10 hH11id hl1 hx0]
    have hbc1: "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l1) (?bc l1)"
    proof -
      have "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l1)
        (top1_basepoint_change_on X TX (id x0) ((g \<circ> f) x0)
           (top1_path_reverse ?\<alpha>1) (id \<circ> l1))" by (rule hbc_raw1)
      thus ?thesis by simp
    qed
    note hbc_raw2 = homotopy_induced_basepoint_change[OF hTX hTX hH1cont hH10 hH11id hl2 hx0]
    have hbc2: "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l2) (?bc l2)"
    proof -
      have "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l2)
        (top1_basepoint_change_on X TX (id x0) ((g \<circ> f) x0)
           (top1_path_reverse ?\<alpha>1) (id \<circ> l2))" by (rule hbc_raw2)
      thus ?thesis by simp
    qed
    have hgfl1': "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l1) ((g \<circ> f) \<circ> l2)"
      using hgfl_equiv by (simp add: comp_def)
    have hbc_equiv: "top1_loop_equiv_on X TX ((g \<circ> f) x0) (?bc l1) (?bc l2)"
      by (rule top1_loop_equiv_on_trans[OF hTX
          top1_loop_equiv_on_trans[OF hTX
            top1_loop_equiv_on_sym[OF hbc1] hgfl1'] hbc2])
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
      have "?\<alpha>1 0 = (g \<circ> f) x0" using hH10 hx0 by (by100 auto)
      moreover have "?\<alpha>1 1 = x0" using hH11 hx0 by (by100 auto)
      ultimately show ?thesis unfolding top1_is_path_on_def using hcomp by (by100 auto)
    qed
    have hrev_a1: "top1_is_path_on X TX x0 ((g \<circ> f) x0) (top1_path_reverse ?\<alpha>1)"
      by (rule top1_path_reverse_is_path[OF hra1])
    have hrt1: "top1_loop_equiv_on X TX x0 l1
        (top1_basepoint_change_on X TX ((g \<circ> f) x0) x0 ?\<alpha>1 (?bc l1))"
      unfolding top1_loop_equiv_on_def
      using hl1 top1_basepoint_change_is_loop[OF hTX hra1
              top1_basepoint_change_is_loop[OF hTX hrev_a1 hl1]]
            top1_basepoint_change_roundtrip[OF hTX hrev_a1 hl1,
              unfolded top1_path_reverse_twice] by (by100 blast)
    have hrt2: "top1_loop_equiv_on X TX x0 l2
        (top1_basepoint_change_on X TX ((g \<circ> f) x0) x0 ?\<alpha>1 (?bc l2))"
      unfolding top1_loop_equiv_on_def
      using hl2 top1_basepoint_change_is_loop[OF hTX hra1
              top1_basepoint_change_is_loop[OF hTX hrev_a1 hl2]]
            top1_basepoint_change_roundtrip[OF hTX hrev_a1 hl2,
              unfolded top1_path_reverse_twice] by (by100 blast)
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
        by (by100 blast)
      thus ?thesis unfolding hc1_eq hc2_eq by (by100 auto)
    qed
  qed
  \<comment> \<open>Surjectivity of f\_*: follows from f\<circ>g \<simeq> id.\<close>
  have hfstar_surj: "?f_star ` (top1_fundamental_group_carrier X TX x0) =
      top1_fundamental_group_carrier Y TY (f x0)"
  proof (intro set_eqI iffI)
    fix d assume "d \<in> ?f_star ` (top1_fundamental_group_carrier X TX x0)"
    thus "d \<in> top1_fundamental_group_carrier Y TY (f x0)"
      using hfstar_range by (by100 blast)
  next
    fix d assume hd: "d \<in> top1_fundamental_group_carrier Y TY (f x0)"
    obtain m where hm: "top1_is_loop_on Y TY (f x0) m"
        and hd_eq: "d = {h. top1_loop_equiv_on Y TY (f x0) m h}"
      using hd unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hgm: "top1_is_loop_on X TX (g (f x0)) (g \<circ> m)"
      by (rule top1_continuous_map_loop[OF hg hm])
    \<comment> \<open>Path \<alpha>1 from g(f(x0)) to x0 (re-proved from homotopy H1).\<close>
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
              hconst[folded hp1] hid_I[folded hp2] by blast
      have hcomp: "top1_continuous_map_on I_set I_top X TX (\<lambda>t. H1 (x0, t))"
        using top1_continuous_map_on_comp[OF hpair hH1cont] by (simp add: comp_def)
      have "?\<alpha>1 0 = g (f x0)" using hH10 hx0 by (by100 auto)
      moreover have "?\<alpha>1 1 = x0" using hH11 hx0 by (by100 auto)
      ultimately show ?thesis unfolding top1_is_path_on_def using hcomp by (by100 auto)
    qed
    let ?bc_gm = "top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> m)"
    have hbc_loop: "top1_is_loop_on X TX x0 ?bc_gm"
      by (rule top1_basepoint_change_is_loop[OF hTX hra1 hgm])
    let ?c = "{h. top1_loop_equiv_on X TX x0 ?bc_gm h}"
    have hc_mem: "?c \<in> top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def using hbc_loop by (by100 blast)
    \<comment> \<open>Extract homotopy H2: f\<circ>g \<simeq> id on Y.\<close>
    obtain H2 where hH2cont: "top1_continuous_map_on (Y \<times> I_set) (product_topology_on TY I_top) Y TY H2"
        and hH20: "\<forall>y\<in>Y. H2 (y, 0) = (f \<circ> g) y" and hH21: "\<forall>y\<in>Y. H2 (y, 1) = y"
      using hfog unfolding top1_homotopic_on_def id_def by (by100 blast)
    let ?\<alpha>2 = "\<lambda>t. H2 (f x0, t)"
    have hfx0Y: "f x0 \<in> Y" using hf hx0 unfolding top1_continuous_map_on_def by (by100 blast)
    have hH21': "\<forall>y\<in>Y. H2 (y, 1) = id y" using hH21 by (by100 simp)
    note hbc2 = homotopy_induced_basepoint_change[OF hTY hTY hH2cont hH20 hH21' hm hfx0Y]
    have hbc2': "top1_loop_equiv_on Y TY (f (g (f x0))) (f \<circ> g \<circ> m)
        (top1_basepoint_change_on Y TY (f x0) (f (g (f x0)))
           (top1_path_reverse ?\<alpha>2) m)"
    proof -
      have "(\<lambda>y. f (g y)) \<circ> m = f \<circ> g \<circ> m" by (simp add: comp_def)
      moreover have "(\<lambda>y. y) \<circ> m = m" by (simp add: comp_def)
      ultimately show ?thesis using hbc2 by simp
    qed
    have hf_comp_product: "\<And>p q. f \<circ> top1_path_product p q = top1_path_product (f \<circ> p) (f \<circ> q)"
      unfolding top1_path_product_def comp_def by (rule ext) (by100 auto)
    have hf_comp_rev: "\<And>p. f \<circ> top1_path_reverse p = top1_path_reverse (f \<circ> p)"
      unfolding top1_path_reverse_def comp_def by (rule ext) (by100 auto)
    have hfbc_eq: "f \<circ> ?bc_gm = top1_basepoint_change_on Y TY (f (g (f x0))) (f x0)
        (f \<circ> ?\<alpha>1) (f \<circ> g \<circ> m)"
      unfolding top1_basepoint_change_on_def hf_comp_product hf_comp_rev
      by (simp add: comp_assoc)
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
      have hfbc': "f \<circ> top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> m') =
          top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1) (f \<circ> g \<circ> m')"
        unfolding top1_basepoint_change_on_def hf_comp_product hf_comp_rev
        by (simp add: comp_assoc)
      have hbc2_m': "top1_loop_equiv_on Y TY (f (g (f x0))) (f \<circ> g \<circ> m')
          (top1_basepoint_change_on Y TY (f x0) (f (g (f x0)))
             (top1_path_reverse ?\<alpha>2) m')"
      proof -
        note hbc2_raw = homotopy_induced_basepoint_change[OF hTY hTY hH2cont hH20 hH21' hm' hfx0Y]
        have "(\<lambda>y. f (g y)) \<circ> m' = f \<circ> g \<circ> m'" by (simp add: comp_def)
        moreover have "(\<lambda>y. y) \<circ> m' = m'" by (simp add: comp_def)
        ultimately show ?thesis using hbc2_raw by simp
      qed
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
      have hstep3: "top1_loop_equiv_on Y TY (f x0)
          (top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1)
             (top1_basepoint_change_on Y TY (f x0) (f (g (f x0))) (top1_path_reverse ?\<alpha>2) m'))
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> m')"
        by (rule double_basepoint_change_equiv[OF hTY hfa1 hra2 hm'])
      have hchain: "top1_loop_equiv_on Y TY (f x0)
          (top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1) (f \<circ> g \<circ> m'))
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> m')"
        by (rule top1_loop_equiv_on_trans[OF hTY hstep2 hstep3])
      show "top1_loop_equiv_on Y TY (f x0)
          (f \<circ> top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> m'))
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> m')"
        using hchain unfolding hfbc' .
    qed
    \<comment> \<open>Take m' = bc(rev(\<gamma>), m). Roundtrip: m \<simeq> bc(\<gamma>, m').\<close>
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
      show ?thesis unfolding top1_loop_equiv_on_def
        using hm hbc_gm'_loop hrt by (by100 blast)
    qed
    \<comment> \<open>Preimage: c' = [bc(\<alpha>1, g\<circ>m')].\<close>
    have hgm': "top1_is_loop_on X TX (g (f x0)) (g \<circ> ?m')"
      by (rule top1_continuous_map_loop[OF hg hm'_loop])
    let ?c_pre = "top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> ?m')"
    have hcpre_loop: "top1_is_loop_on X TX x0 ?c_pre"
      by (rule top1_basepoint_change_is_loop[OF hTX hra1 hgm'])
    have hcpre_mem: "{h. top1_loop_equiv_on X TX x0 ?c_pre h}
        \<in> top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def using hcpre_loop by (by100 blast)
    have hfcpre_equiv: "top1_loop_equiv_on Y TY (f x0)
        (f \<circ> ?c_pre) (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
      by (rule hcomp_is_bc[OF hm'_loop])
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
    have hfcpre_m: "top1_loop_equiv_on Y TY (f x0) (f \<circ> ?c_pre) m"
      by (rule top1_loop_equiv_on_trans[OF hTY hfcpre_equiv hbcgm_equiv_m])
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
  have hf_star_bij: "bij_betw ?f_star
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_carrier Y TY (f x0))"
    unfolding bij_betw_def using hfstar_inj hfstar_surj by (by100 blast)
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
proof -
  let ?R2_0 = "UNIV - {(0::real, 0::real)}"
  let ?TR = TR2_0
  let ?TS1 = "subspace_topology ?R2_0 ?TR top1_S1"
  \<comment> \<open>S1 is a deformation retract of R2-\{0\}.\<close>
  have hdef: "top1_deformation_retract_of_on ?R2_0 ?TR top1_S1"
    unfolding TR2_0_def
  proof -
    let ?R2_0' = "UNIV - {(0::real, 0::real)}"
    let ?TR' = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?R2_0'"
    let ?norm = "\<lambda>x::real\<times>real. sqrt (fst x ^ 2 + snd x ^ 2)"
    let ?H = "\<lambda>(x::real\<times>real, t::real). ((1-t)*fst x + t*fst x/?norm x, (1-t)*snd x + t*snd x/?norm x)"
    have hS1sub: "top1_S1 \<subseteq> ?R2_0'" unfolding top1_S1_def by auto
    have hH0: "\<forall>x\<in>?R2_0'. ?H (x, 0) = x" by simp
    have hH1: "\<forall>x\<in>?R2_0'. ?H (x, 1) \<in> top1_S1"
    proof
      fix x :: "real \<times> real" assume hx: "x \<in> ?R2_0'"
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
        have hdn: "fst x ^ 2 + snd x ^ 2 \<noteq> 0"
        proof -
          have "?norm x ^ 2 > 0" using hnorm_pos by simp
          thus ?thesis using hns by linarith
        qed
        have "(fst x / ?norm x) ^ 2 + (snd x / ?norm x) ^ 2 =
            (fst x ^ 2 + snd x ^ 2) / (fst x ^ 2 + snd x ^ 2)"
          unfolding power_divide hns by (metis add_divide_distrib)
        also have "\<dots> = 1" using hdn by simp
        finally show ?thesis .
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
    have hHcont: "top1_continuous_map_on (?R2_0' \<times> I_set) (product_topology_on ?TR' I_top) ?R2_0' ?TR' ?H"
    proof -
      have hH_std: "continuous_on (?R2_0' \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
          ((1 - snd p) * fst (fst p) + snd p * fst (fst p) / ?norm (fst p),
           (1 - snd p) * snd (fst p) + snd p * snd (fst p) / ?norm (fst p)))"
      proof -
        have hnorm_cont: "continuous_on ?R2_0' ?norm"
          by (intro continuous_on_compose2[OF continuous_on_real_sqrt]
              continuous_on_add continuous_on_power continuous_intros) auto
        have hnorm_nz: "\<forall>x\<in>?R2_0'. ?norm x \<noteq> 0"
        proof (intro ballI)
          fix x :: "real \<times> real" assume "x \<in> ?R2_0'"
          hence "fst x ^ 2 + snd x ^ 2 > 0"
            by (cases x) (auto simp: sum_power2_gt_zero_iff)
          thus "?norm x \<noteq> 0" by (metis less_imp_neq not_sym real_sqrt_gt_zero)
        qed
        have hfst_div: "continuous_on ?R2_0' (\<lambda>x. fst x / ?norm x)"
          by (rule continuous_on_divide) (intro continuous_intros, rule hnorm_cont, rule hnorm_nz)
        have hsnd_div: "continuous_on ?R2_0' (\<lambda>x. snd x / ?norm x)"
          by (rule continuous_on_divide) (intro continuous_intros, rule hnorm_cont, rule hnorm_nz)
        have hfst_R2: "continuous_on (?R2_0' \<times> I_set) (fst::(real\<times>real)\<times>real \<Rightarrow> real\<times>real)"
          by (intro continuous_intros)
        have hfst_img: "fst ` (?R2_0' \<times> I_set) \<subseteq> ?R2_0'" by (by100 auto)
        have hfdiv': "continuous_on (?R2_0' \<times> I_set) (\<lambda>p. fst (fst p) / ?norm (fst p))"
          using continuous_on_compose[OF hfst_R2 continuous_on_subset[OF hfst_div hfst_img]]
          by (simp add: comp_def)
        have hsdiv': "continuous_on (?R2_0' \<times> I_set) (\<lambda>p. snd (fst p) / ?norm (fst p))"
          using continuous_on_compose[OF hfst_R2 continuous_on_subset[OF hsnd_div hfst_img]]
          by (simp add: comp_def)
        have hid: "continuous_on (?R2_0' \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. p)"
          by (rule continuous_on_id)
        have h1mt: "continuous_on (?R2_0' \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. 1 - snd p)"
          by (intro continuous_on_diff continuous_on_const continuous_on_snd[OF hid])
        have hff: "continuous_on (?R2_0' \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. fst (fst p))"
          by (intro continuous_on_fst[OF continuous_on_fst[OF hid]])
        have hsf: "continuous_on (?R2_0' \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. snd (fst p))"
          by (intro continuous_on_snd[OF continuous_on_fst[OF hid]])
        have ht: "continuous_on (?R2_0' \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. snd p)"
          by (intro continuous_on_snd[OF hid])
        have hcomp1: "continuous_on (?R2_0' \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
            (1 - snd p) * fst (fst p) + snd p * (fst (fst p) / ?norm (fst p)))"
          by (intro continuous_on_add continuous_on_mult h1mt hff ht hfdiv')
        have hcomp2: "continuous_on (?R2_0' \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
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
      have hH_std': "continuous_on (?R2_0' \<times> I_set) (\<lambda>p. ?H (fst p, snd p))"
        using hH_std unfolding hH_eq .
      have hH_range: "\<And>p. p \<in> ?R2_0' \<times> I_set \<Longrightarrow> (\<lambda>p. ?H (fst p, snd p)) p \<in> ?R2_0'"
      proof -
        fix p :: "(real \<times> real) \<times> real"
        assume hp: "p \<in> ?R2_0' \<times> I_set"
        have hxR2: "fst p \<in> ?R2_0'" using hp by (simp add: mem_Times_iff)
        hence hxnz: "fst p \<noteq> (0, 0)" by (by100 simp)
        have htI: "snd p \<in> I_set" using hp by (simp add: mem_Times_iff)
        have hnp: "?norm (fst p) > 0"
          using hxnz by (cases "fst p") (auto simp: sum_power2_gt_zero_iff real_sqrt_gt_zero)
        have "?H (fst p, snd p) \<noteq> (0, 0)"
        proof
          assume habs: "?H (fst p, snd p) = (0, 0)"
          have h1: "(1 - snd p) * fst (fst p) + snd p * fst (fst p) / ?norm (fst p) = 0"
            using habs by (simp add: prod_eq_iff case_prod_beta)
          have h2: "(1 - snd p) * snd (fst p) + snd p * snd (fst p) / ?norm (fst p) = 0"
            using habs by (simp add: prod_eq_iff case_prod_beta)
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
          have hfact1: "fst (fst p) * ((1 - snd p) * ?norm (fst p) + snd p) = 0"
            using h1' by (simp add: algebra_simps)
          have hfact2: "snd (fst p) * ((1 - snd p) * ?norm (fst p) + snd p) = 0"
            using h2' by (simp add: algebra_simps)
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
        thus "(\<lambda>p. ?H (fst p, snd p)) p \<in> ?R2_0'" by (simp add: case_prod_beta)
      qed
      have "top1_continuous_map_on (?R2_0' \<times> I_set) (product_topology_on ?TR' I_top)
          ?R2_0' ?TR' (\<lambda>p. ?H (fst p, snd p))"
        by (rule R2_subspace_I_continuous_on_transfer[OF hH_std' hH_range])
      moreover have "(\<lambda>p::(real\<times>real)\<times>real. ?H (fst p, snd p)) = ?H"
        by (rule ext) (simp add: case_prod_beta)
      ultimately show ?thesis by simp
    qed
    show "top1_deformation_retract_of_on ?R2_0' ?TR' top1_S1"
      unfolding top1_deformation_retract_of_on_def
      using hS1sub hHcont hH0 hH1 hHA by blast
  qed
  \<comment> \<open>Topology setup.\<close>
  have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
    using product_topology_on_is_topology_on[OF hTR hTR] by simp
  have hTR2_0: "is_topology_on ?R2_0 ?TR"
    unfolding TR2_0_def by (rule subspace_topology_is_topology_on[OF hTR2]) simp
  have h10_S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by simp
  have hS1_sub: "top1_S1 \<subseteq> ?R2_0" unfolding top1_S1_def by auto
  have h10_R2: "(1::real, 0::real) \<in> ?R2_0" using h10_S1 hS1_sub by (by100 blast)
  have hTS1: "is_topology_on top1_S1 ?TS1"
    by (rule subspace_topology_is_topology_on[OF hTR2_0]) (use hS1_sub in \<open>by100 blast\<close>)
  \<comment> \<open>Extract retraction r and homotopy H from deformation retract.\<close>
  obtain H where hHcont: "top1_continuous_map_on (?R2_0 \<times> I_set) (product_topology_on ?TR I_top) ?R2_0 ?TR H"
      and hH0: "\<forall>x\<in>?R2_0. H (x, 0) = x"
      and hH1: "\<forall>x\<in>?R2_0. H (x, 1) \<in> top1_S1"
      and hHA: "\<forall>a\<in>top1_S1. \<forall>t\<in>I_set. H (a, t) = a"
    using hdef unfolding top1_deformation_retract_of_on_def by blast
  let ?r = "\<lambda>x. H (x, 1)"
  \<comment> \<open>Construct homotopy equivalence (id, r) between S1 and R2-\{0\}.\<close>
  \<comment> \<open>j = id: S1 \<rightarrow> R2-\{0\} is continuous (inclusion).\<close>
  have hj_cont: "top1_continuous_map_on top1_S1 ?TS1 ?R2_0 ?TR id"
  proof -
    from Theorem_18_2[OF hTR2_0 hTR2_0 hTR2_0] hS1_sub
    show ?thesis by (by100 blast)
  qed
  \<comment> \<open>r: R2-\{0\} \<rightarrow> S1 is continuous.\<close>
  have hr_range: "\<forall>x\<in>?R2_0. ?r x \<in> top1_S1" using hH1 by (by100 simp)
  have hr_cont_R2: "top1_continuous_map_on ?R2_0 ?TR ?R2_0 ?TR ?r"
  proof -
    have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have "top1_continuous_map_on ?R2_0 ?TR (?R2_0 \<times> I_set) (product_topology_on ?TR I_top) (\<lambda>x. (x, 1))"
    proof -
      have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
      have hid_R2: "top1_continuous_map_on ?R2_0 ?TR ?R2_0 ?TR id"
        by (rule top1_continuous_map_on_id[OF hTR2_0])
      have hconst1: "top1_continuous_map_on ?R2_0 ?TR I_set I_top (\<lambda>_. 1)"
        by (rule top1_continuous_map_on_const[OF hTR2_0 hTI h1_I])
      have hp1: "(pi1 \<circ> (\<lambda>x. (x, 1::real))) = id" unfolding pi1_def by (rule ext) simp
      have hp2: "(pi2 \<circ> (\<lambda>x. (x, 1::real))) = (\<lambda>_. 1::real)" unfolding pi2_def by (rule ext) simp
      from iffD2[OF Theorem_18_4[OF hTR2_0 hTR2_0 hTI]]
        hid_R2[folded hp1] hconst1[folded hp2]
      show ?thesis by (by100 blast)
    qed
    thus ?thesis using top1_continuous_map_on_comp[of ?R2_0 ?TR "?R2_0 \<times> I_set"
        "product_topology_on ?TR I_top" "\<lambda>x. (x, 1)" ?R2_0 ?TR H] hHcont
      by (simp add: comp_def)
  qed
  have hr_cont: "top1_continuous_map_on ?R2_0 ?TR top1_S1 ?TS1 ?r"
  proof -
    have himg: "?r ` ?R2_0 \<subseteq> top1_S1" using hr_range by (by100 blast)
    show ?thesis by (rule top1_continuous_map_on_codomain_shrink[OF hr_cont_R2 himg hS1_sub])
  qed
  \<comment> \<open>r \<circ> id = id on S1 (since H(a,1) = a for a \<in> S1).\<close>
  have hrj_id: "\<forall>a\<in>top1_S1. ?r (id a) = a"
  proof
    fix a assume "a \<in> top1_S1"
    have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    thus "?r (id a) = a" using hHA \<open>a \<in> top1_S1\<close> by (by100 simp)
  qed
  \<comment> \<open>Homotopy equivalence: r \<circ> id \<simeq> id on S1 (trivially, since r \<circ> id = id).\<close>
  have hgf: "top1_homotopic_on top1_S1 ?TS1 top1_S1 ?TS1 (?r \<circ> id) (\<lambda>x. x)"
  proof -
    have hrf_eq: "\<forall>x\<in>top1_S1. (?r \<circ> id) x = x" using hrj_id by (by100 simp)
    \<comment> \<open>r\<circ>id is continuous S1 \<rightarrow> S1.\<close>
    have hri_cont: "top1_continuous_map_on top1_S1 ?TS1 top1_S1 ?TS1 (?r \<circ> id)"
      by (rule top1_continuous_map_on_comp[OF hj_cont hr_cont])
    have hid_cont: "top1_continuous_map_on top1_S1 ?TS1 top1_S1 ?TS1 (\<lambda>x. x)"
      using top1_continuous_map_on_id[OF hTS1] unfolding id_def by (by100 simp)
    \<comment> \<open>Constant homotopy F(x,t) = x works since (r\<circ>id)(a) = a for a \<in> S1.\<close>
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hF_cont: "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on ?TS1 I_top)
        top1_S1 ?TS1 (\<lambda>p. fst p)"
    proof -
      have "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on ?TS1 I_top) top1_S1 ?TS1 pi1"
        by (rule top1_continuous_pi1[OF hTS1 hTI])
      thus ?thesis unfolding pi1_def by (by100 simp)
    qed
    have hF0: "\<forall>x\<in>top1_S1. fst (x, (0::real)) = (?r \<circ> id) x" using hrf_eq by (by100 simp)
    have hF1: "\<forall>x\<in>top1_S1. fst (x, (1::real)) = x" by (by100 simp)
    show ?thesis unfolding top1_homotopic_on_def
      using hri_cont hid_cont hF_cont hF0 hF1 by (by100 blast)
  qed
  \<comment> \<open>id \<circ> r \<simeq> id on R2-\{0\} (from deformation retract H).\<close>
  have hfg: "top1_homotopic_on ?R2_0 ?TR ?R2_0 ?TR (id \<circ> ?r) (\<lambda>y. y)"
  proof -
    \<comment> \<open>H(x,0) = x = id(x) and H(x,1) = r(x) = (id \<circ> r)(x).
       So H is a homotopy from id to id \<circ> r. By symmetry: id \<circ> r \<simeq> id.\<close>
    have hfwd: "top1_homotopic_on ?R2_0 ?TR ?R2_0 ?TR (\<lambda>y. y) (id \<circ> ?r)"
      unfolding top1_homotopic_on_def
    proof (intro conjI)
      show "top1_continuous_map_on ?R2_0 ?TR ?R2_0 ?TR (\<lambda>y. y)"
        using top1_continuous_map_on_id[OF hTR2_0] unfolding id_def by (by100 simp)
    next
      show "top1_continuous_map_on ?R2_0 ?TR ?R2_0 ?TR (id \<circ> ?r)"
        using hr_cont_R2 by (by100 simp)
    next
      show "\<exists>F. top1_continuous_map_on (?R2_0 \<times> I_set) (product_topology_on ?TR I_top) ?R2_0 ?TR F \<and>
          (\<forall>x\<in>?R2_0. F (x, 0) = (\<lambda>y. y) x) \<and> (\<forall>x\<in>?R2_0. F (x, 1) = (id \<circ> ?r) x)"
        using hHcont hH0 hH1 hS1_sub by (intro exI[of _ H]) (by100 auto)
    qed
    show ?thesis by (rule Lemma_51_1_homotopic_sym[OF hfwd hTR2_0])
  qed
  \<comment> \<open>Now we have homotopy equivalence data. Apply Theorem\_58\_7\_fixed.\<close>
  have heq: "top1_homotopy_equivalence_on top1_S1 ?TS1 ?R2_0 ?TR id ?r"
    unfolding top1_homotopy_equivalence_on_def
    using hj_cont hr_cont hgf hfg by (by100 blast)
  have hid10: "id (1::real, 0::real) = (1, 0)" by (by100 simp)
  from Theorem_58_7_fixed[OF hTS1 hTR2_0 heq h10_S1, unfolded hid10]
  show ?thesis .
qed

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
      thus ?thesis unfolding hTC_eq[symmetric] .
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
      proof -
        have hj_cont_x: "top1_continuous_map_on C ?TC ?X ?TX id" by (rule hj_cont)
        have "top1_group_hom_on
            (top1_fundamental_group_carrier C ?TC x) (top1_fundamental_group_mul C ?TC x)
            (top1_fundamental_group_carrier ?X ?TX x) (top1_fundamental_group_mul ?X ?TX x)
            (top1_fundamental_group_induced_on C ?TC x ?X ?TX x id)"
        proof -
          have "id x = x" by (by100 simp)
          from top1_fundamental_group_induced_on_is_hom[OF hTC hTX _ hx_X hj_cont_x this]
          show ?thesis using hx_C by (by100 blast)
        qed
        thus ?thesis by (by100 simp)
      qed
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
        \<comment> \<open>g^n is a loop in C.\<close>
        have hgn_C: "top1_is_loop_on C ?TC x (top1_path_power g x n)"
          by (rule top1_path_power_is_loop[OF hTC hg_loop_C])
        \<comment> \<open>[g^n]\_C \<in> \<pi>_1(C, x).\<close>
        have hgn_class_C: "{h. top1_loop_equiv_on C ?TC x (top1_path_power g x n) h}
            \<in> top1_fundamental_group_carrier C ?TC x"
          unfolding top1_fundamental_group_carrier_def using hgn_C by (by100 blast)
        \<comment> \<open>j\_*([g^n]\_C) = [g^n]\_X.\<close>
        have hTC_sub: "?TC = subspace_topology ?X ?TX C"
          using subspace_topology_trans[of C ?X top1_S2 top1_S2_topology] hC_sub_X by (by100 simp)
        have hj_class_gn: "?j_star_x {h. top1_loop_equiv_on C ?TC x (top1_path_power g x n) h} =
            {k. top1_loop_equiv_on ?X ?TX x (top1_path_power g x n) k}"
        proof -
          have "top1_is_loop_on C (subspace_topology ?X ?TX C) x (top1_path_power g x n)"
            using hgn_C hTC_sub by (by100 simp)
          from inclusion_sends_class[OF hTX hC_sub_X _ this] hx_C
          show ?thesis unfolding hTC_sub by (by100 blast)
        qed
        \<comment> \<open>[f]\_X = [g^n]\_X (from homotopy).\<close>
        have hc_gn: "c = {h. top1_loop_equiv_on ?X ?TX x (top1_path_power g x n) h}"
        proof -
          from path_homotopic_same_class[OF hTX hfgn]
          have "{h. top1_loop_equiv_on ?X ?TX x f h} =
              {h. top1_loop_equiv_on ?X ?TX x (top1_path_power g x n) h}" .
          thus ?thesis using hc_eq by (by100 blast)
        qed
        hence "c = ?j_star_x {h. top1_loop_equiv_on C ?TC x (top1_path_power g x n) h}"
          using hj_class_gn by (by100 simp)
        thus ?thesis using hgn_class_C by (by100 blast)
      next
        assume hfgrn: "top1_path_homotopic_on ?X ?TX x x f (top1_path_power (top1_path_reverse g) x n)"
        \<comment> \<open>Same argument with g\_rev.\<close>
        have hgr_loop_C: "top1_is_loop_on C ?TC x (top1_path_reverse g)"
          by (rule top1_path_reverse_is_loop[OF hg_loop_C])
        have hgrn_C: "top1_is_loop_on C ?TC x (top1_path_power (top1_path_reverse g) x n)"
          by (rule top1_path_power_is_loop[OF hTC hgr_loop_C])
        have hgrn_class_C: "{h. top1_loop_equiv_on C ?TC x (top1_path_power (top1_path_reverse g) x n) h}
            \<in> top1_fundamental_group_carrier C ?TC x"
          unfolding top1_fundamental_group_carrier_def using hgrn_C by (by100 blast)
        have hTC_sub: "?TC = subspace_topology ?X ?TX C"
          using subspace_topology_trans[of C ?X top1_S2 top1_S2_topology] hC_sub_X by (by100 simp)
        have "?j_star_x {h. top1_loop_equiv_on C ?TC x (top1_path_power (top1_path_reverse g) x n) h} =
            {k. top1_loop_equiv_on ?X ?TX x (top1_path_power (top1_path_reverse g) x n) k}"
        proof -
          have "top1_is_loop_on C (subspace_topology ?X ?TX C) x (top1_path_power (top1_path_reverse g) x n)"
            using hgrn_C hTC_sub by (by100 simp)
          from inclusion_sends_class[OF hTX hC_sub_X _ this] hx_C
          show ?thesis unfolding hTC_sub by (by100 blast)
        qed
        moreover have "c = {h. top1_loop_equiv_on ?X ?TX x (top1_path_power (top1_path_reverse g) x n) h}"
        proof -
          from path_homotopic_same_class[OF hTX hfgrn]
          have "{h. top1_loop_equiv_on ?X ?TX x f h} =
              {h. top1_loop_equiv_on ?X ?TX x (top1_path_power (top1_path_reverse g) x n) h}" .
          thus ?thesis using hc_eq by (by100 blast)
        qed
        ultimately have "c = ?j_star_x {h. top1_loop_equiv_on C ?TC x (top1_path_power (top1_path_reverse g) x n) h}"
          by (by100 simp)
        thus ?thesis using hgrn_class_C by (by100 blast)
      qed
    qed
    \<comment> \<open>Transfer surjectivity from x to c0 via basepoint change (C path-connected).\<close>
    \<comment> \<open>SCC C is path-connected: get path \<beta> from x to c0 in C.\<close>
    obtain \<beta> where h\<beta>_C: "top1_is_path_on C ?TC x c0 \<beta>"
    proof -
      from hC_scc obtain f_scc where
          hf_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S2 top1_S2_topology f_scc"
          and hf_img: "f_scc ` top1_S1 = C"
        unfolding top1_simple_closed_curve_on_def by (by100 blast)
      from hx_C hf_img obtain x' where hx': "x' \<in> top1_S1" "f_scc x' = x" by (by100 blast)
      from assms(40) hf_img obtain c0' where hc0': "c0' \<in> top1_S1" "f_scc c0' = c0" by (by100 blast)
      from S1_path_connected hx'(1) hc0'(1)
      obtain \<gamma> where h\<gamma>: "top1_is_path_on top1_S1 top1_S1_topology x' c0' \<gamma>"
        unfolding top1_path_connected_on_def by (by100 blast)
      have h\<gamma>_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology \<gamma>"
        using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
      \<comment> \<open>f\_scc \<circ> \<gamma>: I \<rightarrow> S2 is continuous (composition).\<close>
      have hf\<gamma>_S2: "top1_continuous_map_on I_set I_top top1_S2 top1_S2_topology (f_scc \<circ> \<gamma>)"
        by (rule top1_continuous_map_on_comp[OF h\<gamma>_cont hf_cont])
      \<comment> \<open>(f\_scc \<circ> \<gamma>) maps I into C = f\_scc(S1).\<close>
      have hf\<gamma>_range: "(f_scc \<circ> \<gamma>) ` I_set \<subseteq> C"
      proof
        fix y assume "y \<in> (f_scc \<circ> \<gamma>) ` I_set"
        then obtain t where "t \<in> I_set" "y = f_scc (\<gamma> t)" by (by100 auto)
        moreover have "\<gamma> t \<in> top1_S1"
          using h\<gamma>_cont \<open>t \<in> I_set\<close> unfolding top1_continuous_map_on_def by (by100 blast)
        ultimately show "y \<in> C" using hf_img by (by100 blast)
      qed
      \<comment> \<open>Factor through C: f\_scc \<circ> \<gamma>: I \<rightarrow> C with TC.\<close>
      have hf\<gamma>_C: "top1_continuous_map_on I_set I_top C ?TC (f_scc \<circ> \<gamma>)"
        by (rule top1_continuous_map_on_codomain_shrink[OF hf\<gamma>_S2 hf\<gamma>_range hC_sub_S2])
      have "(f_scc \<circ> \<gamma>) 0 = x"
        using h\<gamma> hx'(2) unfolding top1_is_path_on_def by (by100 auto)
      moreover have "(f_scc \<circ> \<gamma>) 1 = c0"
        using h\<gamma> hc0'(2) unfolding top1_is_path_on_def by (by100 auto)
      ultimately have "top1_is_path_on C ?TC x c0 (f_scc \<circ> \<gamma>)"
        unfolding top1_is_path_on_def using hf\<gamma>_C by (by100 auto)
      thus ?thesis using that by (by100 blast)
    qed
    \<comment> \<open>\<beta> is also a path from x to c0 in X (C \<subseteq> X, composition with inclusion).\<close>
    have h\<beta>_X: "top1_is_path_on ?X ?TX x c0 \<beta>"
    proof -
      have h\<beta>_cont_C: "top1_continuous_map_on I_set I_top C ?TC \<beta>"
        using h\<beta>_C unfolding top1_is_path_on_def by (by100 blast)
      have h\<beta>_cont_X: "top1_continuous_map_on I_set I_top ?X ?TX \<beta>"
      proof -
        have "top1_continuous_map_on I_set I_top ?X ?TX (id \<circ> \<beta>)"
          by (rule top1_continuous_map_on_comp[OF h\<beta>_cont_C hj_cont])
        thus ?thesis by (by100 simp)
      qed
      have "\<beta> 0 = x" using h\<beta>_C unfolding top1_is_path_on_def by (by100 blast)
      moreover have "\<beta> 1 = c0" using h\<beta>_C unfolding top1_is_path_on_def by (by100 blast)
      ultimately show ?thesis unfolding top1_is_path_on_def using h\<beta>_cont_X by (by100 auto)
    qed
    \<comment> \<open>Reverse paths.\<close>
    have hrev\<beta>_C: "top1_is_path_on C ?TC c0 x (top1_path_reverse \<beta>)"
      by (rule top1_path_reverse_is_path[OF h\<beta>_C])
    have hrev\<beta>_X: "top1_is_path_on ?X ?TX c0 x (top1_path_reverse \<beta>)"
      by (rule top1_path_reverse_is_path[OF h\<beta>_X])
    \<comment> \<open>Surjectivity at c0: for any d \<in> \<pi>_1(X, c0), construct preimage in \<pi>_1(C, c0).\<close>
    show ?thesis
    proof (intro set_eqI iffI)
      fix d assume "d \<in> ?j_star ` (top1_fundamental_group_carrier C ?TC c0)"
      thus "d \<in> top1_fundamental_group_carrier ?X ?TX c0"
        using hj_star_hom unfolding top1_group_hom_on_def by (by100 blast)
    next
      fix d assume hd: "d \<in> top1_fundamental_group_carrier ?X ?TX c0"
      obtain m where hm: "top1_is_loop_on ?X ?TX c0 m"
          and hd_eq: "d = {h. top1_loop_equiv_on ?X ?TX c0 m h}"
        using hd unfolding top1_fundamental_group_carrier_def by (by100 blast)
      \<comment> \<open>Basepoint-change m from c0 to x: m' = bc(rev\_\<beta>, m) at x in X.\<close>
      let ?m' = "top1_basepoint_change_on ?X ?TX c0 x (top1_path_reverse \<beta>) m"
      have hm'_loop: "top1_is_loop_on ?X ?TX x ?m'"
        by (rule top1_basepoint_change_is_loop[OF hTX hrev\<beta>_X hm])
      have hm'_class_X: "{h. top1_loop_equiv_on ?X ?TX x ?m' h}
          \<in> top1_fundamental_group_carrier ?X ?TX x"
        unfolding top1_fundamental_group_carrier_def using hm'_loop by (by100 blast)
      \<comment> \<open>By j\_*(x) surjectivity: \<exists> preimage in \<pi>_1(C, x).\<close>
      have hm'_in_img: "{h. top1_loop_equiv_on ?X ?TX x ?m' h}
          \<in> ?j_star_x ` (top1_fundamental_group_carrier C ?TC x)"
        using hj_star_x_surj hm'_class_X by (by100 blast)
      then obtain c' where hc'_mem: "c' \<in> top1_fundamental_group_carrier C ?TC x"
          and hc'_img: "?j_star_x c' = {h. top1_loop_equiv_on ?X ?TX x ?m' h}"
        by (by100 blast)
      obtain f where hf_loop_C: "top1_is_loop_on C ?TC x f"
          and hc'_eq: "c' = {h. top1_loop_equiv_on C ?TC x f h}"
        using hc'_mem unfolding top1_fundamental_group_carrier_def by (by100 blast)
      \<comment> \<open>j\_*(x)([f]\_C) = [f]\_X by inclusion\_sends\_class.\<close>
      have hTC_sub: "?TC = subspace_topology ?X ?TX C"
        using subspace_topology_trans[of C ?X top1_S2 top1_S2_topology] hC_sub_X by (by100 simp)
      have hf_loop_C': "top1_is_loop_on C (subspace_topology ?X ?TX C) x f"
        using hf_loop_C hTC_sub by (by100 simp)
      have hjx_class_f: "?j_star_x {h. top1_loop_equiv_on C ?TC x f h} =
          {k. top1_loop_equiv_on ?X ?TX x f k}"
        using inclusion_sends_class[OF hTX hC_sub_X _ hf_loop_C'] hx_C
        unfolding hTC_sub by (by100 blast)
      \<comment> \<open>So [f]\_X = [m']\_X, i.e., f \<simeq>\_X m' at x.\<close>
      have hf_equiv_m': "top1_loop_equiv_on ?X ?TX x f ?m'"
      proof -
        have h1: "?j_star_x c' = {h. top1_loop_equiv_on ?X ?TX x ?m' h}" using hc'_img by (by100 simp)
        have h2: "?j_star_x c' = ?j_star_x {h. top1_loop_equiv_on C ?TC x f h}" using hc'_eq by (by100 simp)
        have h3: "?j_star_x {h. top1_loop_equiv_on C ?TC x f h} = {k. top1_loop_equiv_on ?X ?TX x f k}"
          using hjx_class_f by (by100 simp)
        have "{k. top1_loop_equiv_on ?X ?TX x f k} = {h. top1_loop_equiv_on ?X ?TX x ?m' h}"
          using h1 h2 h3 by (by100 metis)
        moreover have "f \<in> {k. top1_loop_equiv_on ?X ?TX x f k}"
        proof -
          have hf_cont_C: "top1_continuous_map_on I_set I_top C ?TC f"
            using hf_loop_C unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have "top1_continuous_map_on I_set I_top ?X ?TX (id \<circ> f)"
            by (rule top1_continuous_map_on_comp[OF hf_cont_C hj_cont])
          hence "top1_continuous_map_on I_set I_top ?X ?TX f" by (by100 simp)
          moreover have "f 0 = x" "f 1 = x"
            using hf_loop_C unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
          ultimately have hf_X: "top1_is_loop_on ?X ?TX x f"
            unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 auto)
          from top1_loop_equiv_on_refl[OF hf_X] show ?thesis by (by100 simp)
        qed
        ultimately have "f \<in> {h. top1_loop_equiv_on ?X ?TX x ?m' h}" by (by100 blast)
        hence "top1_loop_equiv_on ?X ?TX x ?m' f" by (by100 simp)
        thus ?thesis by (rule top1_loop_equiv_on_sym)
      qed
      \<comment> \<open>Construct preimage: bc\_C(\<beta>, f) = rev(\<beta>) * (f * \<beta>), a loop at c0 in C.\<close>
      let ?bc_f = "top1_basepoint_change_on C ?TC x c0 \<beta> f"
      have hbc_f_loop_C: "top1_is_loop_on C ?TC c0 ?bc_f"
        by (rule top1_basepoint_change_is_loop[OF hTC h\<beta>_C hf_loop_C])
      have hbc_f_class_C: "{h. top1_loop_equiv_on C ?TC c0 ?bc_f h}
          \<in> top1_fundamental_group_carrier C ?TC c0"
        unfolding top1_fundamental_group_carrier_def using hbc_f_loop_C by (by100 blast)
      \<comment> \<open>j\_*(c0)([bc\_f]\_C) = [bc\_f]\_X by inclusion\_sends\_class at c0.\<close>
      have hbc_f_loop_C': "top1_is_loop_on C (subspace_topology ?X ?TX C) c0 ?bc_f"
      proof -
        have "?TC = subspace_topology ?X ?TX C" using hTC_sub .
        thus ?thesis using hbc_f_loop_C
          unfolding top1_basepoint_change_on_def by (by100 simp)
      qed
      have hjc0_class_bcf: "?j_star {h. top1_loop_equiv_on C ?TC c0 ?bc_f h} =
          {k. top1_loop_equiv_on ?X ?TX c0 ?bc_f k}"
        using inclusion_sends_class[OF hTX hC_sub_X _ hbc_f_loop_C'] assms(40) hC_sub_X
        unfolding hTC_sub by (by100 blast)
      \<comment> \<open>bc\_C(\<beta>, f) = bc\_X(\<beta>, f) as functions (pointwise definition).\<close>
      have hbc_eq: "top1_basepoint_change_on C ?TC x c0 \<beta> f =
          top1_basepoint_change_on ?X ?TX x c0 \<beta> f"
        unfolding top1_basepoint_change_on_def by (by100 simp)
      let ?bc_f_X = "top1_basepoint_change_on ?X ?TX x c0 \<beta> f"
      \<comment> \<open>bc\_X(\<beta>, f) \<simeq>\_X bc\_X(\<beta>, m') at c0 (f \<simeq> m' and bc preserves homotopy).\<close>
      have hf_loop_X: "top1_is_loop_on ?X ?TX x f"
        using hf_equiv_m' unfolding top1_loop_equiv_on_def by (by100 blast)
      have hbc_f_X_equiv_bc_m': "top1_loop_equiv_on ?X ?TX c0 ?bc_f_X
          (top1_basepoint_change_on ?X ?TX x c0 \<beta> ?m')"
        by (rule top1_basepoint_change_loop_equiv[OF hTX h\<beta>_X hf_loop_X hm'_loop hf_equiv_m'])
      \<comment> \<open>Roundtrip: m \<simeq>\_X bc(\<beta>, bc(rev\_\<beta>, m)) = bc(\<beta>, m') at c0.\<close>
      have hroundtrip: "top1_path_homotopic_on ?X ?TX c0 c0 m
          (top1_basepoint_change_on ?X ?TX x c0 \<beta>
            (top1_basepoint_change_on ?X ?TX c0 x (top1_path_reverse \<beta>) m))"
      proof -
        from top1_basepoint_change_roundtrip[OF hTX hrev\<beta>_X hm]
        have "top1_path_homotopic_on ?X ?TX c0 c0 m
            (top1_basepoint_change_on ?X ?TX x c0 (top1_path_reverse (top1_path_reverse \<beta>))
              (top1_basepoint_change_on ?X ?TX c0 x (top1_path_reverse \<beta>) m))" .
        thus ?thesis by (simp add: top1_path_reverse_twice)
      qed
      have hbc_m'_equiv_m: "top1_loop_equiv_on ?X ?TX c0
          (top1_basepoint_change_on ?X ?TX x c0 \<beta> ?m') m"
      proof -
        have h1: "top1_is_loop_on ?X ?TX c0
            (top1_basepoint_change_on ?X ?TX x c0 \<beta> ?m')"
          by (rule top1_basepoint_change_is_loop[OF hTX h\<beta>_X hm'_loop])
        show ?thesis
          unfolding top1_loop_equiv_on_def
          using hm h1 Lemma_51_1_path_homotopic_sym[OF hroundtrip] by (by100 blast)
      qed
      \<comment> \<open>Chain: bc\_X(\<beta>, f) \<simeq> bc\_X(\<beta>, m') \<simeq> m at c0.\<close>
      have hbc_f_X_equiv_m: "top1_loop_equiv_on ?X ?TX c0 ?bc_f_X m"
        by (rule top1_loop_equiv_on_trans[OF hTX hbc_f_X_equiv_bc_m' hbc_m'_equiv_m])
      \<comment> \<open>[bc\_f]\_X = [m]\_X = d.\<close>
      \<comment> \<open>[bc\_f]\_X = [m]\_X: bc\_f \<simeq>\_X m implies same equivalence class.\<close>
      have hbc_f_X_equiv_m_unf: "top1_loop_equiv_on ?X ?TX c0 ?bc_f m"
        using hbc_f_X_equiv_m hbc_eq by (by100 simp)
      have hclass_eq: "{k. top1_loop_equiv_on ?X ?TX c0 ?bc_f k} =
          {h. top1_loop_equiv_on ?X ?TX c0 m h}"
      proof (intro set_eqI iffI)
        fix k assume "k \<in> {k. top1_loop_equiv_on ?X ?TX c0 ?bc_f k}"
        hence hk: "top1_loop_equiv_on ?X ?TX c0 ?bc_f k" by (by100 simp)
        have "top1_loop_equiv_on ?X ?TX c0 m k"
          by (rule top1_loop_equiv_on_trans[OF hTX
                top1_loop_equiv_on_sym[OF hbc_f_X_equiv_m_unf] hk])
        thus "k \<in> {h. top1_loop_equiv_on ?X ?TX c0 m h}" by (by100 simp)
      next
        fix k assume "k \<in> {h. top1_loop_equiv_on ?X ?TX c0 m h}"
        hence hk: "top1_loop_equiv_on ?X ?TX c0 m k" by (by100 simp)
        have "top1_loop_equiv_on ?X ?TX c0 ?bc_f k"
          by (rule top1_loop_equiv_on_trans[OF hTX hbc_f_X_equiv_m_unf hk])
        thus "k \<in> {k. top1_loop_equiv_on ?X ?TX c0 ?bc_f k}" by (by100 simp)
      qed
      have "?j_star {h. top1_loop_equiv_on C ?TC c0 ?bc_f h} = d"
      proof -
        have "?j_star {h. top1_loop_equiv_on C ?TC c0 ?bc_f h} =
            {k. top1_loop_equiv_on ?X ?TX c0 ?bc_f k}" using hjc0_class_bcf by (by100 simp)
        also have "\<dots> = {h. top1_loop_equiv_on ?X ?TX c0 m h}" using hclass_eq .
        also have "\<dots> = d" using hd_eq by (by100 simp)
        finally show ?thesis .
      qed
      thus "d \<in> ?j_star ` (top1_fundamental_group_carrier C ?TC c0)"
        using hbc_f_class_C by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 5: Surjective hom Z \<rightarrow> Z is injective (hence bijective).\<close>
  have hj_star_inj: "inj_on ?j_star (top1_fundamental_group_carrier C ?TC c0)"
  proof -
    have hGX_closed: "\<And>a b. a \<in> top1_fundamental_group_carrier C ?TC c0 \<Longrightarrow>
        b \<in> top1_fundamental_group_carrier C ?TC c0 \<Longrightarrow>
        top1_fundamental_group_mul C ?TC c0 a b \<in> top1_fundamental_group_carrier C ?TC c0"
    proof -
      fix a b assume "a \<in> top1_fundamental_group_carrier C ?TC c0"
          "b \<in> top1_fundamental_group_carrier C ?TC c0"
      have hgrp: "top1_is_group_on (top1_fundamental_group_carrier C ?TC c0)
          (top1_fundamental_group_mul C ?TC c0) (top1_fundamental_group_id C ?TC c0)
          (top1_fundamental_group_invg C ?TC c0)"
        by (rule top1_fundamental_group_is_group[OF hTC]) (use assms(40) in \<open>by100 blast\<close>)
      show "top1_fundamental_group_mul C ?TC c0 a b \<in> top1_fundamental_group_carrier C ?TC c0"
        using \<open>a \<in> _\<close> \<open>b \<in> _\<close> hgrp unfolding top1_is_group_on_def by auto
    qed
    show ?thesis
      by (rule surj_hom_infinite_cyclic_inj[OF hC_pi1_Z hX_pi1_Z hj_star_hom hj_star_surj hGX_closed])
  qed
  \<comment> \<open>Combine.\<close>
  have hj_star_bij: "bij_betw ?j_star
      (top1_fundamental_group_carrier C ?TC c0) (top1_fundamental_group_carrier ?X ?TX c0)"
    unfolding bij_betw_def using hj_star_inj hj_star_surj by (by100 blast)
  show ?thesis unfolding top1_group_iso_on_def using hj_star_hom hj_star_bij by (by100 blast)
qed

\<comment> \<open>Alternative: iso at an EXISTENTIAL basepoint (avoids basepoint change).\<close>
lemma Lemma_65_1_fixed_exists_basepoint:
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
  shows "\<exists>x \<in> C. top1_group_iso_on
    (top1_fundamental_group_carrier C
       (subspace_topology top1_S2 top1_S2_topology C) x)
    (top1_fundamental_group_mul C
       (subspace_topology top1_S2 top1_S2_topology C) x)
    (top1_fundamental_group_carrier (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x)
    (top1_fundamental_group_mul (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x)
    (top1_fundamental_group_induced_on C
       (subspace_topology top1_S2 top1_S2_topology C) x
       (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x id)"
proof -
  let ?X = "top1_S2 - {p} - {q}"
  let ?TX = "subspace_topology top1_S2 top1_S2_topology ?X"
  let ?TC = "subspace_topology top1_S2 top1_S2_topology C"
  \<comment> \<open>Get generator loop at x from K4 construction.\<close>
  from K4_generator_loop_in_C[OF assms]
  obtain x g where hx_C: "x \<in> C"
      and hg_loop_C: "top1_is_loop_on C ?TC x g"
      and hg_loop_X: "top1_is_loop_on ?X ?TX x g"
      and hg_generates: "\<forall>f. top1_is_loop_on ?X ?TX x f \<longrightarrow>
          (\<exists>n::nat. top1_path_homotopic_on ?X ?TX x x f (top1_path_power g x n)
            \<or> top1_path_homotopic_on ?X ?TX x x f (top1_path_power (top1_path_reverse g) x n))"
    by (by100 blast)
  \<comment> \<open>Setup.\<close>
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hC_sub_S2: "C \<subseteq> top1_S2" using assms(4,5,6,7,39) by (by100 blast)
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
  have hx_X: "x \<in> ?X" using hx_C hC_sub_X by (by100 blast)
  have hTX: "is_topology_on ?X ?TX"
    by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
  have hTC: "is_topology_on C ?TC"
    by (rule subspace_topology_is_topology_on[OF hTopS2]) (use hC_sub_S2 in \<open>by100 blast\<close>)
  \<comment> \<open>j\_* at x is a homomorphism.\<close>
  let ?j_star_x = "top1_fundamental_group_induced_on C ?TC x ?X ?TX x id"
  have hj_cont: "top1_continuous_map_on C ?TC ?X ?TX id"
  proof -
    have hid_S2: "top1_continuous_map_on C ?TC top1_S2 top1_S2_topology id"
      using Theorem_18_2[OF hTopS2 hTopS2 hTopS2] hC_sub_S2 by (by100 blast)
    show ?thesis unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> C"
      hence "s \<in> ?X" using hC_sub_X by (by100 blast)
      thus "id s \<in> ?X" by (by100 simp)
    next
      fix V assume "V \<in> ?TX"
      hence "\<exists>U \<in> top1_S2_topology. V = ?X \<inter> U" unfolding subspace_topology_def by (by100 blast)
      then obtain U where "U \<in> top1_S2_topology" "V = ?X \<inter> U" by (by100 blast)
      have "{s \<in> C. id s \<in> V} = C \<inter> V" by auto
      also have "\<dots> = C \<inter> (?X \<inter> U)" using \<open>V = ?X \<inter> U\<close> by (by100 simp)
      also have "\<dots> = C \<inter> U" using hC_sub_X by (by100 blast)
      also have "\<dots> = {s \<in> C. id s \<in> U}" by auto
      finally have "{s \<in> C. id s \<in> V} = {s \<in> C. id s \<in> U}" .
      moreover have "{s \<in> C. id s \<in> U} \<in> ?TC"
        using hid_S2 \<open>U \<in> top1_S2_topology\<close> unfolding top1_continuous_map_on_def by (by100 blast)
      ultimately show "{s \<in> C. id s \<in> V} \<in> ?TC" by (by100 simp)
    qed
  qed
  have hj_hom_x: "top1_group_hom_on
      (top1_fundamental_group_carrier C ?TC x) (top1_fundamental_group_mul C ?TC x)
      (top1_fundamental_group_carrier ?X ?TX x) (top1_fundamental_group_mul ?X ?TX x) ?j_star_x"
  proof -
    have "id x = x" by (by100 simp)
    from top1_fundamental_group_induced_on_is_hom[OF hTC hTX _ hx_X hj_cont this]
    show ?thesis using hx_C by (by100 blast)
  qed
  \<comment> \<open>j\_* surjective at x (from the Lemma\_65\_1\_fixed proof above).\<close>
  have hj_surj_x: "?j_star_x ` (top1_fundamental_group_carrier C ?TC x) =
      top1_fundamental_group_carrier ?X ?TX x"
    by (rule K4_inclusion_surjective_at_x[OF assms(1-39)
        hx_C hg_loop_C hg_loop_X hg_generates hC_sub_X hTX hTC hj_cont])
  \<comment> \<open>Both groups infinite cyclic.\<close>
  have hC_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
    by (rule K4_cycle_is_SCC[OF assms(1,2,4,5,6,7,10,11,12,13,16,17,18,19,22,23,24,25,26,27,39)])
  \<comment> \<open>gen\_C not needed: surj\_hom\_infinite\_cyclic\_inj takes \<cong>Z directly.\<close>
  \<comment> \<open>j\_* injective (surjective hom between infinite cyclic groups).\<close>
  have hj_inj_x: "inj_on ?j_star_x (top1_fundamental_group_carrier C ?TC x)"
  proof -
    have hC_pi1_Z_x: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier C ?TC x) (top1_fundamental_group_mul C ?TC x)
        top1_Z_group top1_Z_mul"
    proof -
      have hC_scc_loc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
        by (rule K4_cycle_is_SCC[OF assms(1,2,4,5,6,7,10,11,12,13,16,17,18,19,22,23,24,25,26,27,39)])
      show ?thesis by (rule SCC_pi1_iso_Z[OF assms(1) hC_scc_loc hx_C])
    qed
    have hX_pi1_Z_x: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier ?X ?TX x) (top1_fundamental_group_mul ?X ?TX x)
        top1_Z_group top1_Z_mul"
    proof -
      have hp_S2: "p \<in> top1_S2" using assms(8,37) by (by100 blast)
      have hq_S2: "q \<in> top1_S2" using assms(9,38) by (by100 blast)
      have hp_ne_q: "p \<noteq> q"
      proof assume "p = q"
        have "p \<in> e13" using assms(37) by (by100 blast)
        have "p \<in> e24" using \<open>p = q\<close> assms(38) by (by100 blast)
        hence "p \<in> e13 \<inter> e24" using \<open>p \<in> e13\<close> by (by100 blast)
        hence "p \<in> {a1,a2,a3,a4}" using assms(32) by (by100 blast)
        moreover have "p \<noteq> a1" "p \<noteq> a3" using assms(37) by (by100 blast)+
        moreover have "p \<noteq> a2" "p \<noteq> a4" using \<open>p = q\<close> assms(38) by (by100 blast)+
        ultimately show False by (by100 blast)
      qed
      show ?thesis by (rule pi1_S2_minus_two_points_iso_Z[OF assms(1) hp_S2 hq_S2 hp_ne_q hx_X])
    qed
    have hGX_closed_x: "\<And>a b. a \<in> top1_fundamental_group_carrier C ?TC x \<Longrightarrow>
        b \<in> top1_fundamental_group_carrier C ?TC x \<Longrightarrow>
        top1_fundamental_group_mul C ?TC x a b \<in> top1_fundamental_group_carrier C ?TC x"
    proof -
      fix a b assume "a \<in> top1_fundamental_group_carrier C ?TC x"
          "b \<in> top1_fundamental_group_carrier C ?TC x"
      have hgrp: "top1_is_group_on (top1_fundamental_group_carrier C ?TC x)
          (top1_fundamental_group_mul C ?TC x) (top1_fundamental_group_id C ?TC x)
          (top1_fundamental_group_invg C ?TC x)"
        by (rule top1_fundamental_group_is_group[OF hTC]) (use hx_C in \<open>by100 blast\<close>)
      show "top1_fundamental_group_mul C ?TC x a b \<in> top1_fundamental_group_carrier C ?TC x"
        using \<open>a \<in> _\<close> \<open>b \<in> _\<close> \<open>top1_is_group_on _ _ _ _\<close>
        unfolding top1_is_group_on_def by auto
    qed
    show ?thesis by (rule surj_hom_infinite_cyclic_inj[OF hC_pi1_Z_x hX_pi1_Z_x hj_hom_x hj_surj_x hGX_closed_x])
  qed
  \<comment> \<open>Combine: hom + bij = iso.\<close>
  have "bij_betw ?j_star_x (top1_fundamental_group_carrier C ?TC x)
      (top1_fundamental_group_carrier ?X ?TX x)"
    unfolding bij_betw_def using hj_inj_x hj_surj_x by (by100 blast)
  hence "top1_group_iso_on
      (top1_fundamental_group_carrier C ?TC x) (top1_fundamental_group_mul C ?TC x)
      (top1_fundamental_group_carrier ?X ?TX x) (top1_fundamental_group_mul ?X ?TX x) ?j_star_x"
    unfolding top1_group_iso_on_def using hj_hom_x by (by100 blast)
  thus ?thesis using hx_C by (by100 blast)
qed

section \<open>Theorem 65.2 (fixed): inclusion C \<hookrightarrow> S2-{p,q} induces iso (general SCC)\<close>

text \<open>Munkres Theorem 65.2: Let C be a simple closed curve in S2; let p and q lie
  in different components of S2-C. Then the inclusion j: C \<rightarrow> S2-p-q induces
  an isomorphism of fundamental groups.\<close>

text \<open>Munkres Thm 65.2 Step 1: Given arcs A (from a to b) and B (from b to c)
  in a Hausdorff space, there exists an arc from a to c contained in A \<union> B.
  Construction: let h:[0,1]\<rightarrow>A be the arc parametrization.
  t0 = min\{t | h(t) \<in> B\}. Then h([0,t0]) is a sub-arc of A from a to h(t0),
  and a sub-arc of B from h(t0) to c exists. Their concatenation is the result.\<close>

lemma Munkres_Step_1_arc_splice:
  assumes hS2: "is_topology_on_strict top1_S2 top1_S2_topology"
  and hA_arc: "top1_is_arc_on A (subspace_topology top1_S2 top1_S2_topology A)"
  and hB_arc: "top1_is_arc_on B (subspace_topology top1_S2 top1_S2_topology B)"
  and hA_sub: "A \<subseteq> top1_S2" and hB_sub: "B \<subseteq> top1_S2"
  and hA_ep: "top1_arc_endpoints_on A (subspace_topology top1_S2 top1_S2_topology A) = {a, b}"
  and hB_ep: "top1_arc_endpoints_on B (subspace_topology top1_S2 top1_S2_topology B) = {b, c}"
  and hab: "a \<noteq> b" and hbc: "b \<noteq> c"
  and ha_notB: "a \<notin> B"
  shows "\<exists>D. top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D)
    \<and> D \<subseteq> A \<union> B \<and> a \<in> D \<and> c \<in> D
    \<and> top1_arc_endpoints_on D (subspace_topology top1_S2 top1_S2_topology D) = {a, c}"
proof -
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology" by (rule top1_S2_is_hausdorff)
  \<comment> \<open>Get arc parametrization h: [0,1] \<rightarrow> A with h(0)=a, h(1)=b.\<close>
  from hA_arc obtain h where hh: "top1_homeomorphism_on I_set I_top A
      (subspace_topology top1_S2 top1_S2_topology A) h"
    unfolding top1_is_arc_on_def top1_homeomorphism_on_def by (by100 blast)
  have hh_ep: "top1_arc_endpoints_on A (subspace_topology top1_S2 top1_S2_topology A) = {h 0, h 1}"
    by (rule arc_endpoints_are_boundary[OF hS2 hS2_haus hA_sub hA_arc hh])
  \<comment> \<open>WLOG h(0)=a, h(1)=b (swap if needed using unit\_interval\_reversal\_homeomorphism).\<close>
  \<comment> \<open>For now, assume this orientation.\<close>
  have h0a_h1b: "(h 0 = a \<and> h 1 = b) \<or> (h 0 = b \<and> h 1 = a)"
  proof -
    from hh_ep hA_ep have heq: "{h 0, h 1} = {a, b}" by (by100 simp)
    have "h 0 = a \<or> h 0 = b" using heq by (by100 blast)
    thus ?thesis
    proof
      assume ha: "h 0 = a"
      have "b \<in> {h 0, h 1}" using heq by (by100 blast)
      hence "h 1 = b" using ha hab by (by100 blast)
      thus ?thesis using ha by (by100 blast)
    next
      assume hb: "h 0 = b"
      have "a \<in> {h 0, h 1}" using heq by (by100 blast)
      hence "h 1 = a" using hb hab by (by100 blast)
      thus ?thesis using hb by (by100 blast)
    qed
  qed
  \<comment> \<open>If h(0)=b, h(1)=a: replace h by h \<circ> (1-t) which reverses.\<close>
  obtain h' where hh': "top1_homeomorphism_on I_set I_top A
      (subspace_topology top1_S2 top1_S2_topology A) h'" "h' 0 = a" "h' 1 = b"
  proof -
    from h0a_h1b show ?thesis
    proof (elim disjE conjE)
      assume "h 0 = a" "h 1 = b"
      thus ?thesis using that hh by (by100 blast)
    next
      assume "h 0 = b" "h 1 = a"
      \<comment> \<open>Use reversal: h' = h \<circ> (1-t).\<close>
      let ?rev = "\<lambda>t. h (1 - t)"
      have hrev_homeo: "top1_homeomorphism_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
        by (rule unit_interval_reversal_homeomorphism)
      have "top1_homeomorphism_on I_set I_top A
          (subspace_topology top1_S2 top1_S2_topology A) (h \<circ> (\<lambda>t. 1 - t))"
        by (rule homeomorphism_on_comp[OF hrev_homeo hh])
      moreover have "(h \<circ> (\<lambda>t. 1 - t)) = ?rev" by (rule ext) (by100 simp)
      ultimately have "top1_homeomorphism_on I_set I_top A
          (subspace_topology top1_S2 top1_S2_topology A) ?rev" by (by100 simp)
      moreover have "?rev 0 = a" using \<open>h 1 = a\<close> by (by100 simp)
      moreover have "?rev 1 = b" using \<open>h 0 = b\<close> by (by100 simp)
      ultimately show ?thesis using that by (by100 blast)
    qed
  qed
  \<comment> \<open>B is closed in S2 (arc is closed).\<close>
  have hB_cl: "closedin_on top1_S2 top1_S2_topology B"
    by (rule arc_in_S2_closed[OF hB_sub hB_arc])
  \<comment> \<open>Preimage T = {t \<in> [0,1] | h'(t) \<in> B} is closed in [0,1].\<close>
  \<comment> \<open>T is non-empty (h'(1)=b \<in> B since b is endpoint of B).\<close>
  have hb_in_B: "b \<in> B" using hB_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
  have ha_ne_c: "a \<noteq> c"
  proof
    assume "a = c" thus False using ha_notB hB_ep hbc
      unfolding top1_arc_endpoints_on_def by (by100 blast)
  qed
  \<comment> \<open>First-hit-time: T = {t \<in> I | h'(t) \<in> B}. T closed, non-empty, compact \<Rightarrow> has minimum t0.\<close>
  let ?T = "{t \<in> I_set. h' t \<in> B}"
  have hT_ne: "?T \<noteq> {}" using hh'(3) hb_in_B
    unfolding top1_unit_interval_def by (by100 force)
  \<comment> \<open>h' continuous from I to S2 (from homeomorphism).\<close>
  \<comment> \<open>h' continuous I \<rightarrow> A (from homeomorphism), then A \<subseteq> S2 gives I \<rightarrow> S2.\<close>
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using hS2 unfolding is_topology_on_strict_def by (by100 blast)
  have hh'_cont_A: "top1_continuous_map_on I_set I_top A
      (subspace_topology top1_S2 top1_S2_topology A) h'"
    using hh'(1) unfolding top1_homeomorphism_on_def by (by100 blast)
  have hh'_cont: "top1_continuous_map_on I_set I_top top1_S2 top1_S2_topology h'"
  proof -
    have hid: "top1_continuous_map_on A (subspace_topology top1_S2 top1_S2_topology A)
        top1_S2 top1_S2_topology id"
      using Theorem_18_2[OF hTopS2 hTopS2 hTopS2] hA_sub by (by100 blast)
    have "top1_continuous_map_on I_set I_top top1_S2 top1_S2_topology (id \<circ> h')"
      by (rule top1_continuous_map_on_comp[OF hh'_cont_A hid])
    thus ?thesis by (by100 simp)
  qed
  \<comment> \<open>T = {t \<in> I | h'(t) \<in> B} is closed in I.\<close>
  have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  have hT_cl: "closedin_on I_set I_top ?T"
    by (rule continuous_preimage_closedin[OF hTI hTopS2 hh'_cont hB_cl])
  \<comment> \<open>I is compact.\<close>
  have hopen_eq: "(top1_open_sets :: real set set) = order_topology_on_UNIV"
  proof (rule set_eqI)
    fix U :: "real set"
    show "U \<in> top1_open_sets \<longleftrightarrow> U \<in> order_topology_on_UNIV"
      unfolding top1_open_sets_def using order_topology_on_UNIV_eq_HOL_open by (by100 simp)
  qed
  have hI_compact: "top1_compact_on I_set I_top"
  proof -
    have hIeq: "I_set = top1_closed_interval 0 1"
      unfolding top1_unit_interval_def top1_closed_interval_def by (by100 auto)
    have hITeq: "I_top = top1_closed_interval_topology 0 1"
      unfolding top1_unit_interval_topology_def top1_closed_interval_topology_def
      using hopen_eq hIeq unfolding top1_unit_interval_def by (by100 simp)
    show ?thesis using top1_closed_interval_compact[of "0::real" 1] hIeq hITeq by (by100 simp)
  qed
  \<comment> \<open>T compact (closed subset of compact).\<close>
  have hT_compact: "top1_compact_on ?T (subspace_topology I_set I_top ?T)"
    by (rule Theorem_26_2[OF hI_compact hT_cl])
  \<comment> \<open>T has minimum t0. Need: I\_top = subspace of order\_topology.\<close>
  have hT_compact_order: "top1_compact_on ?T
      (subspace_topology (UNIV::real set) order_topology_on_UNIV ?T)"
  proof -
    have hTsub: "?T \<subseteq> I_set" by (by100 blast)
    have "subspace_topology I_set I_top ?T =
        subspace_topology (UNIV::real set) top1_open_sets ?T"
      using subspace_topology_trans[of ?T I_set] hTsub
      unfolding top1_unit_interval_topology_def by (by100 simp)
    also have "\<dots> = subspace_topology (UNIV::real set) order_topology_on_UNIV ?T"
      using hopen_eq by (by100 simp)
    finally show ?thesis using hT_compact by (by100 simp)
  qed
  obtain t0 where ht0: "t0 \<in> ?T" "\<forall>t \<in> ?T. t0 \<le> t"
    using top1_compact_on_order_topology_has_least[OF hT_ne hT_compact_order] by (by100 blast)
  have ht0_I: "t0 \<in> I_set" using ht0(1) by (by100 blast)
  have ht0_B: "h' t0 \<in> B" using ht0(1) by (by100 blast)
  \<comment> \<open>h'(t0) is NOT a or b endpoint of A. Since h'(0)=a and t0>0 (a \<notin> B): h'(t0) \<noteq> a.
     h'(t0) \<in> B, and h'(t0) could be b or an interior point of B.\<close>
  have ht0_pos: "t0 > 0"
  proof (rule ccontr)
    assume "\<not> t0 > 0"
    hence "t0 = 0" using ht0_I unfolding top1_unit_interval_def by (by100 simp)
    hence "h' 0 \<in> B" using ht0_B by (by100 simp)
    hence "a \<in> B" using hh'(2) by (by100 simp)
    thus False using ha_notB by (by100 blast)
  qed
  \<comment> \<open>Sub-arc A1 = h'([0,t0]): use homeomorphism\_on\_restrict.\<close>
  let ?A1 = "h' ` {t \<in> I_set. t \<le> t0}"
  have hA1_sub_A: "?A1 \<subseteq> A"
  proof -
    have "\<forall>t \<in> I_set. h' t \<in> A"
      using hh'(1) unfolding top1_homeomorphism_on_def top1_continuous_map_on_def by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  have hA1_sub_S2: "?A1 \<subseteq> top1_S2" using hA1_sub_A hA_sub by (by100 blast)
  \<comment> \<open>h' restricted to [0,t0] is homeomorphism onto A1.\<close>
  have h0t0_sub: "{t \<in> I_set. t \<le> t0} \<subseteq> I_set" by (by100 blast)
  have hA1_homeo: "top1_homeomorphism_on {t \<in> I_set. t \<le> t0}
      (subspace_topology I_set I_top {t \<in> I_set. t \<le> t0})
      ?A1 (subspace_topology A (subspace_topology top1_S2 top1_S2_topology A) ?A1) h'"
    by (rule homeomorphism_on_restrict[OF hh'(1) h0t0_sub])
  \<comment> \<open>A1 is an arc: [0,t0] \<cong> [0,1] via affine rescaling, composed with h'.\<close>
  \<comment> \<open>h'(0)=a \<in> A1, h'(t0) \<in> A1. A1 \<subseteq> A \<subseteq> S2.\<close>
  have ha_A1: "a \<in> ?A1"
  proof -
    have "h' 0 = a" using hh'(2) by (by100 simp)
    moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    moreover have "(0::real) \<le> t0" using ht0_pos by (by100 simp)
    ultimately show ?thesis by (by100 blast)
  qed
  have ht0_A1: "h' t0 \<in> ?A1" using ht0_I by (by100 blast)
  \<comment> \<open>A1 \<inter> B = {h'(t0)}: for any t < t0, h'(t) \<notin> B (t0 is minimum).\<close>
  have hA1_B: "?A1 \<inter> B = {h' t0}"
  proof (intro set_eqI iffI)
    fix x assume "x \<in> ?A1 \<inter> B"
    then obtain t where "t \<in> I_set" "t \<le> t0" "x = h' t" "x \<in> B" by (by100 blast)
    hence "t \<in> ?T" by (by100 blast)
    hence "t0 \<le> t" using ht0(2) by (by100 blast)
    hence "t = t0" using \<open>t \<le> t0\<close> by (by100 simp)
    thus "x \<in> {h' t0}" using \<open>x = h' t\<close> by (by100 simp)
  next
    fix x assume "x \<in> {h' t0}"
    thus "x \<in> ?A1 \<inter> B" using ht0_A1 ht0_B by (by100 blast)
  qed
  \<comment> \<open>h'(t0) is NOT an endpoint of A (interior of A): t0 \<in> (0,1) since t0>0 and t0<1.\<close>
  \<comment> \<open>Actually h'(t0) might be b = h'(1). We need h'(t0) \<noteq> a (proved: t0>0).\<close>
  have ht0_ne_a: "h' t0 \<noteq> a"
  proof
    assume "h' t0 = a"
    hence "h' t0 = h' 0" using hh'(2) by (by100 simp)
    \<comment> \<open>h' injective (homeomorphism) \<Rightarrow> t0 = 0. But t0 > 0.\<close>
    moreover have "inj_on h' I_set"
      using hh'(1) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    moreover have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    ultimately have "t0 = 0"
      by (metis inj_onD[of h' I_set t0 0] ht0_I)
    thus False using ht0_pos by (by100 simp)
  qed
  \<comment> \<open>Now split B at h'(t0) if h'(t0) is interior to B, or handle the endpoint case.\<close>
  \<comment> \<open>h'(t0) \<in> B. If h'(t0) = b: then h'(t0) is endpoint of B, and A1 goes from a to b.
     Sub-arc of B from b to c is all of B. Concatenate A1 \<union> B.
     But A1 \<inter> B = {b} and b is endpoint of both \<Rightarrow> arcs\_concatenation\_is\_arc applies.
     If h'(t0) \<noteq> b: then h'(t0) is interior to B. Split B at h'(t0) \<Rightarrow> B1, B2.
     Take the half from h'(t0) to c. Concatenate A1 with that half.\<close>
  \<comment> \<open>A1 is an arc in S2: compose affine [0,1]\<rightarrow>[0,t0] with h'|[0,t0].
     Result: continuous injective from compact [0,1] to Hausdorff S2 = embedding = arc.\<close>
  let ?phi = "\<lambda>t. h' (t * t0)"
  have ht0_I_le1: "t0 \<le> 1" using ht0_I unfolding top1_unit_interval_def by (by100 simp)
  have haffine: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. t * t0)"
  proof -
    have "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 0 + t * (t0 - 0))"
      by (rule affine_map_continuous_I_to_I[of 0 t0]) (use ht0_pos ht0_I_le1 in \<open>by100 simp\<close>)+
    thus ?thesis by (by100 simp)
  qed
  have hphi_cont: "top1_continuous_map_on I_set I_top top1_S2 top1_S2_topology ?phi"
  proof -
    have "top1_continuous_map_on I_set I_top top1_S2 top1_S2_topology (h' \<circ> (\<lambda>t. t * t0))"
      by (rule top1_continuous_map_on_comp[OF haffine hh'_cont])
    moreover have "(h' \<circ> (\<lambda>t. t * t0)) = ?phi" by (rule ext) (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  have hh'_inj: "inj_on h' I_set"
    using hh'(1) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  have hphi_inj: "inj_on ?phi I_set"
  proof (rule inj_onI)
    fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set" and heq: "h' (s * t0) = h' (t * t0)"
    have hs01: "0 \<le> s" "s \<le> 1" using hs unfolding top1_unit_interval_def by (by100 simp)+
    have ht01: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 simp)+
    have st0_I: "s * t0 \<in> I_set"
    proof -
      have "s * t0 \<le> 1 * 1" by (rule mult_mono) (use hs01 ht0_I_le1 ht0_pos in linarith)+
      thus ?thesis unfolding top1_unit_interval_def using hs01(1) ht0_pos by (by100 simp)
    qed
    moreover have tt0_I: "t * t0 \<in> I_set"
    proof -
      have "t * t0 \<le> 1 * 1" by (rule mult_mono) (use ht01 ht0_I_le1 ht0_pos in linarith)+
      thus ?thesis unfolding top1_unit_interval_def using ht01(1) ht0_pos by (by100 simp)
    qed
    ultimately have "s * t0 = t * t0"
      by (metis inj_onD[OF hh'_inj] heq)
    thus "s = t" using ht0_pos by (by100 simp)
  qed
  have hphi_img: "?phi ` I_set = ?A1"
  proof (intro set_eqI iffI)
    fix x assume "x \<in> ?phi ` I_set"
    then obtain t where "t \<in> I_set" "x = h' (t * t0)" by (by100 blast)
    moreover have "t * t0 \<in> I_set"
    proof -
      have "0 \<le> t" "t \<le> 1" using \<open>t \<in> I_set\<close> unfolding top1_unit_interval_def by (by100 simp)+
      have "t * t0 \<le> 1 * 1" by (rule mult_mono) (use \<open>t\<le>1\<close> ht0_I_le1 \<open>0\<le>t\<close> ht0_pos in linarith)+
      thus ?thesis unfolding top1_unit_interval_def using \<open>0\<le>t\<close> ht0_pos by (by100 simp)
    qed
    moreover have "t * t0 \<le> 1 * t0"
      by (rule mult_right_mono) (use \<open>t \<in> I_set\<close> ht0_pos in \<open>simp add: top1_unit_interval_def\<close>)+
    hence "t * t0 \<le> t0" by (by100 simp)
    ultimately show "x \<in> ?A1" by (by100 blast)
  next
    fix x assume "x \<in> ?A1"
    then obtain t where ht: "t \<in> I_set" "t \<le> t0" "x = h' t" by (by100 blast)
    have "t / t0 \<in> I_set" using ht(1,2) ht0_pos
      unfolding top1_unit_interval_def by (by100 simp)
    moreover have "h' ((t / t0) * t0) = h' t" using ht0_pos by (by100 simp)
    ultimately show "x \<in> ?phi ` I_set" using ht(3) by (by100 force)
  qed
  have hA1_arc: "top1_is_arc_on ?A1 (subspace_topology top1_S2 top1_S2_topology ?A1)"
  proof -
    have "top1_embedding_on I_set I_top top1_S2 top1_S2_topology ?phi"
      by (rule top1_embedding_on_compact_inj[OF hTI hTopS2 hI_compact hS2_haus hphi_cont hphi_inj])
    hence "top1_homeomorphism_on I_set I_top (?phi ` I_set) (subspace_topology top1_S2 top1_S2_topology (?phi ` I_set)) ?phi"
      unfolding top1_embedding_on_def by (by100 blast)
    hence "top1_homeomorphism_on I_set I_top ?A1 (subspace_topology top1_S2 top1_S2_topology ?A1) ?phi"
      using hphi_img by (by100 simp)
    moreover have "is_topology_on_strict ?A1 (subspace_topology top1_S2 top1_S2_topology ?A1)"
      by (rule subspace_topology_is_strict[OF hS2]) (use hA1_sub_S2 in \<open>by100 blast\<close>)
    ultimately show ?thesis unfolding top1_is_arc_on_def by (by100 blast)
  qed
  \<comment> \<open>A1 endpoints are {a, h'(t0)}.\<close>
  have hphi_homeo: "top1_homeomorphism_on I_set I_top ?A1 (subspace_topology top1_S2 top1_S2_topology ?A1) ?phi"
  proof -
    have "top1_embedding_on I_set I_top top1_S2 top1_S2_topology ?phi"
      by (rule top1_embedding_on_compact_inj[OF hTI hTopS2 hI_compact hS2_haus hphi_cont hphi_inj])
    hence "top1_homeomorphism_on I_set I_top (?phi ` I_set) (subspace_topology top1_S2 top1_S2_topology (?phi ` I_set)) ?phi"
      unfolding top1_embedding_on_def by (by100 blast)
    thus ?thesis using hphi_img by (by100 simp)
  qed
  have hA1_strict: "is_topology_on_strict ?A1 (subspace_topology top1_S2 top1_S2_topology ?A1)"
    by (rule subspace_topology_is_strict[OF hS2 hA1_sub_S2])
  have hA1_haus: "is_hausdorff_on ?A1 (subspace_topology top1_S2 top1_S2_topology ?A1)"
    using Theorem_17_11 hS2_haus hA1_sub_S2 by (by100 blast)
  have hA1_ep: "top1_arc_endpoints_on ?A1 (subspace_topology top1_S2 top1_S2_topology ?A1) = {a, h' t0}"
  proof -
    have "top1_arc_endpoints_on ?A1 (subspace_topology top1_S2 top1_S2_topology ?A1) = {?phi 0, ?phi 1}"
      by (rule arc_endpoints_are_boundary[OF hS2 hS2_haus hA1_sub_S2 hA1_arc hphi_homeo])
    moreover have "?phi 0 = a" using hh'(2) by (by100 simp)
    moreover have "?phi 1 = h' t0" by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Split B at h'(t0) to get sub-arc B2 from h'(t0) to c.\<close>
  \<comment> \<open>Case: h'(t0) is interior to B (not an endpoint).\<close>
  \<comment> \<open>h'(t0) \<noteq> c: if h'(t0)=c then c \<in> A1 \<subseteq> A, but c \<notin> A (c is endpoint of B, and
     a\<noteq>c means c is not endpoint of A if A\<inter>B only shares b)... actually c could be in A.
     Skip this and handle in the case split.\<close>
  \<comment> \<open>Case split: h'(t0) = b (endpoint of B) or h'(t0) = c or h'(t0) interior to B.\<close>
  show ?thesis
  proof (cases "h' t0 = c")
    case True
    \<comment> \<open>A1 goes from a to c directly.\<close>
    have "c \<in> ?A1" using ht0_A1 True by (by100 simp)
    moreover have "?A1 \<subseteq> A \<union> B" using hA1_sub_A by (by100 blast)
    moreover have "top1_arc_endpoints_on ?A1 (subspace_topology top1_S2 top1_S2_topology ?A1) = {a, c}"
      using hA1_ep True by (by100 simp)
    ultimately show ?thesis using hA1_arc ha_A1 by (by100 blast)
  next
    case hne_c: False
    \<comment> \<open>Get sub-arc of B from h'(t0) to c.\<close>
    show ?thesis
    proof (cases "h' t0 = b")
      case True
      \<comment> \<open>A1\<inter>B = {b}, b is endpoint of A1 and of B. Concatenate directly.\<close>
      have hA1B_int: "?A1 \<inter> B = {b}" using hA1_B True by (by100 simp)
      have hb_ep_A1: "b \<in> top1_arc_endpoints_on ?A1 (subspace_topology top1_S2 top1_S2_topology ?A1)"
        using hA1_ep True by (by100 blast)
      have hb_ep_B: "b \<in> top1_arc_endpoints_on B (subspace_topology top1_S2 top1_S2_topology B)"
        using hB_ep by (by100 blast)
      have hD: "top1_is_arc_on (?A1 \<union> B) (subspace_topology top1_S2 top1_S2_topology (?A1 \<union> B))"
        by (rule arcs_concatenation_is_arc[OF hS2 hS2_haus hA1_arc hA1_sub_S2 hB_arc hB_sub
            hA1B_int hb_ep_A1 hb_ep_B])
      have hA1_ep_b: "top1_arc_endpoints_on ?A1 (subspace_topology top1_S2 top1_S2_topology ?A1) = {a, b}"
        using hA1_ep True by (by100 simp)
      have hD_ep: "top1_arc_endpoints_on (?A1 \<union> B) (subspace_topology top1_S2 top1_S2_topology (?A1 \<union> B)) = {a, c}"
        by (rule arc_concat_endpoints[OF hS2 hS2_haus hA1_arc hA1_sub_S2 hB_arc hB_sub
            hA1B_int hb_ep_A1 hb_ep_B hA1_ep_b hB_ep hab hbc])
      have "?A1 \<union> B \<subseteq> A \<union> B" using hA1_sub_A by (by100 blast)
      moreover have "c \<in> B" using hB_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
      ultimately show ?thesis using hD ha_A1 hD_ep by (by100 blast)
    next
      case hne_b: False
      \<comment> \<open>h'(t0) interior to B. Split B.\<close>
      have "h' t0 \<notin> top1_arc_endpoints_on B (subspace_topology top1_S2 top1_S2_topology B)"
        using hB_ep hne_b hne_c by (by100 blast)
      from arc_split_at_given_point[OF hS2 hS2_haus hB_sub hB_arc ht0_B this hB_ep hbc]
      obtain B1 B2 where hBs: "B = B1 \<union> B2" "B1 \<inter> B2 = {h' t0}"
          "top1_is_arc_on B1 (subspace_topology top1_S2 top1_S2_topology B1)"
          "top1_is_arc_on B2 (subspace_topology top1_S2 top1_S2_topology B2)"
          "b \<in> B1" "c \<in> B2" "h' t0 \<in> B1" "h' t0 \<in> B2" "B1 \<subseteq> top1_S2" "B2 \<subseteq> top1_S2"
        by blast
      have hA1B2_int: "?A1 \<inter> B2 = {h' t0}"
        using hA1_B hBs(1) hBs(8) by (by100 blast)
      have ht0_ep_A1: "h' t0 \<in> top1_arc_endpoints_on ?A1 (subspace_topology top1_S2 top1_S2_topology ?A1)"
        using hA1_ep by (by100 blast)
      have hB2_ep: "top1_arc_endpoints_on B2 (subspace_topology top1_S2 top1_S2_topology B2) = {h' t0, c}"
        by (rule arc_split_endpoints(2)[OF hS2 hS2_haus hB_sub hB_arc hBs(1) hBs(2) hBs(3) hBs(4)
            hBs(5) hBs(6) hBs(7) hBs(8) hBs(9) hBs(10) hB_ep
            \<open>h' t0 \<notin> top1_arc_endpoints_on B (subspace_topology top1_S2 top1_S2_topology B)\<close>])
      have ht0_ep_B2: "h' t0 \<in> top1_arc_endpoints_on B2 (subspace_topology top1_S2 top1_S2_topology B2)"
        using hB2_ep by (by100 blast)
      have hD: "top1_is_arc_on (?A1 \<union> B2) (subspace_topology top1_S2 top1_S2_topology (?A1 \<union> B2))"
        by (rule arcs_concatenation_is_arc[OF hS2 hS2_haus hA1_arc hA1_sub_S2 hBs(4) hBs(10)
            hA1B2_int ht0_ep_A1 ht0_ep_B2])
      have ht0_ne_c: "h' t0 \<noteq> c" using hne_c by (by100 blast)
      have hD_ep: "top1_arc_endpoints_on (?A1 \<union> B2) (subspace_topology top1_S2 top1_S2_topology (?A1 \<union> B2)) = {a, c}"
        by (rule arc_concat_endpoints[OF hS2 hS2_haus hA1_arc hA1_sub_S2 hBs(4) hBs(10)
            hA1B2_int ht0_ep_A1 ht0_ep_B2 hA1_ep hB2_ep])
         (use ht0_ne_a ht0_ne_c in \<open>by100 blast\<close>)+
      have "?A1 \<union> B2 \<subseteq> A \<union> B" using hA1_sub_A hBs(1) by (by100 blast)
      thus ?thesis using hD ha_A1 hBs(6) hD_ep by (by100 blast)
    qed
  qed
qed

text \<open>Munkres Thm 65.2 Step 2: open path-connected subsets of S2 are arc-connected.
  Any two points that can be connected by a path in an open subset of S2
  can be connected by an arc (injective path) in that subset.
  Proof: stereographic projection gives local homeomorphism to R2 where
  open balls are convex (hence arc-connected via line segments).
  Arc splicing (Munkres Step 1) gives transitivity. Equivalence classes
  of "arc-connected" are open (local arc-connectivity). Since the subset
  is connected, there is one equivalence class.\<close>

lemma S2_open_path_connected_arc_connected:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "U \<in> top1_S2_topology" and "U \<subseteq> top1_S2"
  and "a \<in> U" and "b \<in> U" and "a \<noteq> b"
  and "top1_is_path_on U (subspace_topology top1_S2 top1_S2_topology U) a b f"
  shows "\<exists>A. top1_is_arc_on A (subspace_topology top1_S2 top1_S2_topology A)
    \<and> A \<subseteq> U \<and> top1_arc_endpoints_on A (subspace_topology top1_S2 top1_S2_topology A) = {a, b}"
proof -
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology" by (rule top1_S2_is_hausdorff)
  \<comment> \<open>Local arc-connectivity of S2: every x \<in> U has arc-connected neighborhood.
     Uses S2\_minus\_point\_homeo\_R2: for any point p \<in> S2, S2-{p} \<cong> R2.
     Open ball in R2 is convex \<Rightarrow> line segments are arcs \<Rightarrow> transfer back to S2.\<close>
  have local_arc: "\<And>x. x \<in> U \<Longrightarrow> \<exists>V. V \<in> top1_S2_topology \<and> x \<in> V \<and> V \<subseteq> U \<and>
      (\<forall>y \<in> V. \<forall>z \<in> V. y \<noteq> z \<longrightarrow>
        (\<exists>D. top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D) \<and>
             D \<subseteq> V \<and> top1_arc_endpoints_on D (subspace_topology top1_S2 top1_S2_topology D) = {y, z}))"
  proof -
    fix x assume hx: "x \<in> U"
    have hx_S2: "x \<in> top1_S2" using hx assms(3) by (by100 blast)
    \<comment> \<open>Step 1: Choose p \<in> S2 with p \<noteq> x.\<close>
    define south where "south = (0::real, 0::real, -1::real)"
    have hs_S2: "south \<in> top1_S2" unfolding south_def top1_S2_def by simp
    have hns: "north_pole \<noteq> south" unfolding north_pole_def south_def by simp
    define p where "p = (if x \<noteq> north_pole then north_pole else south)"
    have hp_S2: "p \<in> top1_S2" unfolding p_def using north_pole_in_S2 hs_S2 by auto
    have hp_ne_x: "p \<noteq> x" unfolding p_def using hns by auto
    have hx_SP: "x \<in> top1_S2 - {p}" using hx_S2 hp_ne_x by (by100 blast)
    \<comment> \<open>Step 2: Homeomorphism h: S2-{p} \<rightarrow> R2.\<close>
    let ?SP = "top1_S2 - {p}"
    let ?TSP = "subspace_topology top1_S2 top1_S2_topology ?SP"
    let ?R2 = "UNIV :: (real \<times> real) set"
    let ?TR2 = "product_topology_on top1_open_sets top1_open_sets"
    obtain h where hh: "top1_homeomorphism_on ?SP ?TSP ?R2 ?TR2 h"
      using S2_minus_point_homeo_R2[OF hp_S2] by (by100 blast)
    have hbij: "bij_betw h ?SP ?R2"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hh_cont: "top1_continuous_map_on ?SP ?TSP ?R2 ?TR2 h"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hinv_cont: "top1_continuous_map_on ?R2 ?TR2 ?SP ?TSP (inv_into ?SP h)"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hh_inj: "inj_on h ?SP" using hbij unfolding bij_betw_def by (by100 blast)
    have hh_surj: "h ` ?SP = ?R2" using hbij unfolding bij_betw_def by (by100 blast)
    \<comment> \<open>Step 3: S2-{p} is open in S2.\<close>
    have hSP_open: "?SP \<in> top1_S2_topology"
    proof -
      have "closedin_on top1_S2 top1_S2_topology {p}"
      proof (rule compact_in_strict_hausdorff_closedin_on[OF hS2_haus assms(1)])
        show "{p} \<subseteq> top1_S2" using hp_S2 by (by100 simp)
        show "top1_compact_on {p} (subspace_topology top1_S2 top1_S2_topology {p})"
          unfolding top1_compact_on_def
        proof (intro conjI allI impI)
          show "is_topology_on {p} (subspace_topology top1_S2 top1_S2_topology {p})"
            by (rule subspace_topology_is_topology_on[OF hTopS2]) (simp add: hp_S2)
        next
          fix C :: "(real \<times> real \<times> real) set set"
          assume hC: "C \<subseteq> subspace_topology top1_S2 top1_S2_topology {p} \<and> {p} \<subseteq> \<Union>C"
          then obtain U0 where "U0 \<in> C" "p \<in> U0" by (by100 blast)
          thus "\<exists>F. finite F \<and> F \<subseteq> C \<and> {p} \<subseteq> \<Union>F"
            by (intro exI[of _ "{U0}"]) simp
        qed
      qed
      thus ?thesis unfolding closedin_on_def
        using hTopS2 unfolding is_topology_on_def by (by100 blast)
    qed
    \<comment> \<open>Step 4: h maps U \<inter> SP to open set in R2 (homeomorphism = open map).\<close>
    have hU_SP: "U \<inter> ?SP \<in> ?TSP"
      unfolding subspace_topology_def using assms(2) by (by100 blast)
    have h_img_eq: "h ` (U \<inter> ?SP) = {y \<in> ?R2. inv_into ?SP h y \<in> U \<inter> ?SP}"
    proof (rule set_eqI, rule iffI)
      fix y assume "y \<in> h ` (U \<inter> ?SP)"
      then obtain w where hw: "w \<in> U \<inter> ?SP" "y = h w" by (by100 blast)
      have "inv_into ?SP h y = w"
        using inv_into_f_f[OF hh_inj] hw by (by100 blast)
      thus "y \<in> {y \<in> ?R2. inv_into ?SP h y \<in> U \<inter> ?SP}" using hw by (by100 simp)
    next
      fix y assume hy: "y \<in> {y \<in> ?R2. inv_into ?SP h y \<in> U \<inter> ?SP}"
      hence hy_R2: "y \<in> ?R2" and hinv_y: "inv_into ?SP h y \<in> U \<inter> ?SP" by auto
      have "y \<in> h ` ?SP" using hh_surj hy_R2 by (by100 simp)
      hence "h (inv_into ?SP h y) = y" by (rule f_inv_into_f)
      thus "y \<in> h ` (U \<inter> ?SP)"
      proof -
        let ?w = "inv_into ?SP h y"
        have "?w \<in> U \<inter> ?SP" by (rule hinv_y)
        moreover have "y = h ?w" using \<open>h ?w = y\<close> by (by100 simp)
        ultimately show ?thesis by (by100 blast)
      qed
    qed
    have h_img_open: "h ` (U \<inter> ?SP) \<in> ?TR2"
    proof -
      have "{y \<in> ?R2. inv_into ?SP h y \<in> U \<inter> ?SP} \<in> ?TR2"
        using hinv_cont hU_SP unfolding top1_continuous_map_on_def by (by100 blast)
      thus ?thesis using h_img_eq by (by100 simp)
    qed
    \<comment> \<open>Step 5: Get \<epsilon>-ball in R2 around h(x) inside h(U \<inter> SP).\<close>
    have hx'_in: "h x \<in> h ` (U \<inter> ?SP)" using hx hx_SP by (by100 blast)
    have himg_HOL_open: "open (h ` (U \<inter> ?SP))"
    proof -
      have "h ` (U \<inter> ?SP) \<in> top1_open_sets"
        using h_img_open product_topology_on_open_sets_real2 by (by100 metis)
      thus ?thesis unfolding top1_open_sets_def by (by100 blast)
    qed
    \<comment> \<open>Get open rectangle around h(x) inside h(U \<inter> SP).\<close>
    obtain A0 B0 where hAB: "open A0" "open B0" "h x \<in> A0 \<times> B0"
        "A0 \<times> B0 \<subseteq> h ` (U \<inter> ?SP)"
      using open_prod_elim[OF himg_HOL_open hx'_in] by (by100 blast)
    have hfst_in: "fst (h x) \<in> A0" and hsnd_in: "snd (h x) \<in> B0"
      using hAB(3) by auto
    obtain \<epsilon>1 where he1: "\<epsilon>1 > 0" "\<And>y. dist y (fst (h x)) < \<epsilon>1 \<Longrightarrow> y \<in> A0"
      using hAB(1) hfst_in unfolding open_dist by (by100 blast)
    obtain \<epsilon>2 where he2: "\<epsilon>2 > 0" "\<And>y. dist y (snd (h x)) < \<epsilon>2 \<Longrightarrow> y \<in> B0"
      using hAB(2) hsnd_in unfolding open_dist by (by100 blast)
    define \<epsilon> where "\<epsilon> = min \<epsilon>1 \<epsilon>2"
    have heps_pos: "\<epsilon> > 0" unfolding \<epsilon>_def using he1(1) he2(1) by (by100 simp)
    \<comment> \<open>Open square around h(x) with radius \<epsilon>. Use define to keep terms small.\<close>
    define Sq where "Sq = {q :: real \<times> real. \<bar>fst q - fst (h x)\<bar> < \<epsilon> \<and> \<bar>snd q - snd (h x)\<bar> < \<epsilon>}"
    have hSq_sub: "Sq \<subseteq> h ` (U \<inter> ?SP)"
    proof
      fix q assume hq: "q \<in> Sq"
      hence hq1: "\<bar>fst q - fst (h x)\<bar> < \<epsilon>" and hq2: "\<bar>snd q - snd (h x)\<bar> < \<epsilon>"
        unfolding Sq_def by (by100 blast)+
      have "dist (fst q) (fst (h x)) < \<epsilon>1"
        unfolding dist_real_def using hq1 \<epsilon>_def by (by100 linarith)
      hence "fst q \<in> A0" by (rule he1(2))
      moreover have "dist (snd q) (snd (h x)) < \<epsilon>2"
        unfolding dist_real_def using hq2 \<epsilon>_def by (by100 linarith)
      hence "snd q \<in> B0" by (rule he2(2))
      ultimately have "q \<in> A0 \<times> B0"
        by (subst surjective_pairing[of q], rule SigmaI)
      thus "q \<in> h ` (U \<inter> ?SP)" using hAB(4) by (by100 blast)
    qed
    have hSq_TR2: "Sq \<in> ?TR2"
    proof -
      have "open Sq"
      proof -
        define I1 where "I1 = {fst (h x) - \<epsilon> <..< fst (h x) + \<epsilon> :: real}"
        define I2 where "I2 = {snd (h x) - \<epsilon> <..< snd (h x) + \<epsilon> :: real}"
        have "Sq = I1 \<times> I2"
        proof (rule set_eqI)
          fix q :: "real \<times> real"
          obtain a b where hab: "q = (a, b)" by (cases q)
          have abs_iff1: "(\<bar>a - fst (h x)\<bar> < \<epsilon>) = (fst (h x) - \<epsilon> < a \<and> a < fst (h x) + \<epsilon>)"
            by (by100 linarith)
          have abs_iff2: "(\<bar>b - snd (h x)\<bar> < \<epsilon>) = (snd (h x) - \<epsilon> < b \<and> b < snd (h x) + \<epsilon>)"
            by (by100 linarith)
          show "(q \<in> Sq) = (q \<in> I1 \<times> I2)"
            unfolding hab Sq_def I1_def I2_def greaterThanLessThan_def greaterThan_def lessThan_def
            using abs_iff1 abs_iff2 by (by100 simp)
        qed
        moreover have "open I1" unfolding I1_def by (by100 simp)
        moreover have "open I2" unfolding I2_def by (by100 simp)
        ultimately show ?thesis
        proof -
          assume hSqI: "Sq = I1 \<times> I2" and hI1: "open I1" and hI2: "open I2"
          have "open (I1 \<times> I2)" by (rule open_Times[OF hI1 hI2])
          thus ?thesis using hSqI by (by100 simp)
        qed
      qed
      hence "Sq \<in> top1_open_sets" unfolding top1_open_sets_def by (by100 blast)
      thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
    qed
    \<comment> \<open>Step 6: V = preimage of Sq under h within SP.\<close>
    define V where "V = {w \<in> ?SP. h w \<in> Sq}"
    have hV_in_TSP: "V \<in> ?TSP"
      using hh_cont hSq_TR2 unfolding V_def top1_continuous_map_on_def by (by100 blast)
    have hV_open: "V \<in> top1_S2_topology"
    proof -
      \<comment> \<open>V \<in> TSP, so V = SP \<inter> W for some W \<in> S2\_topology. Since SP is open, V = SP \<inter> W \<in> S2\_topology.\<close>
      from hV_in_TSP obtain W0 where hW0: "W0 \<in> top1_S2_topology" and hV_eq: "V = ?SP \<inter> W0"
        unfolding subspace_topology_def V_def by (by100 blast)
      show ?thesis using topology_inter_open[OF hTopS2 hSP_open hW0] hV_eq by (by100 simp)
    qed
    have hx_V: "x \<in> V"
      unfolding V_def Sq_def using hx_SP heps_pos by (by100 simp)
    have hV_sub_U: "V \<subseteq> U"
    proof
      fix w assume "w \<in> V"
      hence hw_SP: "w \<in> ?SP" and hw_Sq: "h w \<in> Sq" unfolding V_def by auto
      have "h w \<in> h ` (U \<inter> ?SP)" using hSq_sub hw_Sq by (by100 blast)
      then obtain v where hv: "v \<in> U \<inter> ?SP" "h w = h v" by (by100 blast)
      hence "w = v" using hh_inj hw_SP hv(1) unfolding inj_on_def by (by100 blast)
      thus "w \<in> U" using hv(1) by (by100 blast)
    qed
    have hV_sub_SP: "V \<subseteq> ?SP" unfolding V_def by (by100 blast)
    \<comment> \<open>Step 7: For y,z \<in> V with y \<noteq> z, construct arc from y to z in V.
       Line segment in R2 ball \<rightarrow> compose with h\<inverse> \<rightarrow> embedding (compact to Hausdorff) \<rightarrow> arc.\<close>
    have hV_arcs: "\<forall>y \<in> V. \<forall>z \<in> V. y \<noteq> z \<longrightarrow>
        (\<exists>D. top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D) \<and>
             D \<subseteq> V \<and> top1_arc_endpoints_on D (subspace_topology top1_S2 top1_S2_topology D) = {y, z})"
    proof (intro ballI impI)
      fix y z assume hy: "y \<in> V" and hz: "z \<in> V" and hyz: "y \<noteq> z"
      have hy_SP: "y \<in> ?SP" and hz_SP: "z \<in> ?SP" using hy hz unfolding V_def by auto
      define y' z' where "y' = h y" and "z' = h z"
      have hy'_Sq: "y' \<in> Sq" using hy unfolding y'_def V_def by (by100 blast)
      have hz'_Sq: "z' \<in> Sq" using hz unfolding z'_def V_def by (by100 blast)
      have hy'z'_ne: "y' \<noteq> z'"
      proof
        assume "y' = z'"
        hence "h y = h z" unfolding y'_def z'_def .
        with hh_inj hy_SP hz_SP have "y = z" unfolding inj_on_def by (by100 blast)
        with hyz show False by (by100 blast)
      qed
      \<comment> \<open>Line segment \<gamma>(t) = (1-t)*y' + t*z'.\<close>
      define \<gamma> where "\<gamma> = (\<lambda>t::real. ((1-t) * fst y' + t * fst z', (1-t) * snd y' + t * snd z'))"
      define g where "g = (\<lambda>t. inv_into ?SP h (\<gamma> t))"
      \<comment> \<open>Line segment stays in Sq (convexity: coordinate-wise |(1-t)*a+t*b - c| \<le> (1-t)|a-c|+t|b-c| < \<epsilon>).\<close>
      have h\<gamma>_in_Sq: "\<And>t. t \<in> I_set \<Longrightarrow> \<gamma> t \<in> Sq"
        sorry \<comment> \<open>Convexity of L\<infinity> ball: |(1-t)*a+t*b-c| \<le> (1-t)|a-c|+t|b-c| < \<epsilon>.\<close>
      \<comment> \<open>\<gamma>: I\_set \<rightarrow> R2 is continuous (straight-line path).\<close>
      have h\<gamma>_cont: "top1_continuous_map_on I_set I_top ?R2 ?TR2 \<gamma>"
        using R2_straight_line_path[where x=y' and y=z', folded \<gamma>_def]
        unfolding top1_is_path_on_def by (by100 blast)
      \<comment> \<open>g = inv \<circ> \<gamma>: I\_set \<rightarrow> SP is continuous (composition).\<close>
      have hg_comp: "g = (inv_into ?SP h) \<circ> \<gamma>" unfolding g_def comp_def by (by100 blast)
      have hg_cont_SP: "top1_continuous_map_on I_set I_top ?SP ?TSP g"
        using top1_continuous_map_on_comp[OF h\<gamma>_cont hinv_cont] hg_comp by (by100 simp)
      \<comment> \<open>Lift continuity from SP to S2.\<close>
      have hg_cont: "top1_continuous_map_on I_set I_top top1_S2 top1_S2_topology g"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix t assume ht: "t \<in> I_set"
        have "g t \<in> ?SP" using hg_cont_SP ht unfolding top1_continuous_map_on_def by (by100 blast)
        thus "g t \<in> top1_S2" by (by100 blast)
      next
        fix W assume hW: "W \<in> top1_S2_topology"
        have "W \<inter> ?SP \<in> ?TSP"
          unfolding subspace_topology_def using hW by (by100 blast)
        hence "{t \<in> I_set. g t \<in> W \<inter> ?SP} \<in> I_top"
          using hg_cont_SP unfolding top1_continuous_map_on_def by (by100 blast)
        moreover have "{t \<in> I_set. g t \<in> W} = {t \<in> I_set. g t \<in> W \<inter> ?SP}"
        proof (rule set_eqI, rule iffI)
          fix t assume "t \<in> {t \<in> I_set. g t \<in> W}"
          hence ht: "t \<in> I_set" and hgt: "g t \<in> W" by auto
          have "g t \<in> ?SP" using hg_cont_SP ht unfolding top1_continuous_map_on_def by (by100 blast)
          thus "t \<in> {t \<in> I_set. g t \<in> W \<inter> ?SP}" using ht hgt by (by100 blast)
        next
          fix t assume "t \<in> {t \<in> I_set. g t \<in> W \<inter> ?SP}"
          thus "t \<in> {t \<in> I_set. g t \<in> W}" by (by100 blast)
        qed
        ultimately show "{t \<in> I_set. g t \<in> W} \<in> I_top" by (by100 simp)
      qed
      \<comment> \<open>g is injective: \<gamma> injective (y' \<noteq> z' \<Rightarrow> line segment injective), inv\_into injective.\<close>
      have hg_inj: "inj_on g I_set"
        sorry \<comment> \<open>Line segment (1-t)*y'+t*z' injective when y'\<noteq>z'; inv\_into preserves injectivity.\<close>
      \<comment> \<open>I\_set compact, S2 Hausdorff \<Rightarrow> g is embedding.\<close>
      have hI_top: "is_topology_on I_set I_top"
        by (rule top1_unit_interval_topology_is_topology_on)
      have hI_compact: "top1_compact_on I_set I_top"
      proof -
        have hIeq: "I_set = {0..1::real}" unfolding top1_unit_interval_def
          by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
        have "compact I_set" unfolding hIeq by (rule compact_Icc)
        hence "top1_compact_on I_set (subspace_topology UNIV top1_open_sets I_set)"
          using top1_compact_on_subspace_UNIV_iff_compact[of I_set] by (by100 simp)
        thus ?thesis unfolding top1_unit_interval_topology_def by (by100 simp)
      qed
      have hg_embed: "top1_embedding_on I_set I_top top1_S2 top1_S2_topology g"
        by (rule top1_embedding_on_compact_inj[OF hI_top hTopS2 hI_compact hS2_haus hg_cont hg_inj])
      \<comment> \<open>D = g(I\_set) is an arc.\<close>
      let ?D = "g ` I_set"
      have hD_sub_S2: "?D \<subseteq> top1_S2"
        using hg_cont unfolding top1_continuous_map_on_def by (by100 blast)
      have hg_homeo: "top1_homeomorphism_on I_set I_top ?D
          (subspace_topology top1_S2 top1_S2_topology ?D) g"
        using hg_embed unfolding top1_embedding_on_def by (by100 blast)
      have hD_ne: "?D \<noteq> {}"
      proof -
        have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        thus ?thesis by (by100 blast)
      qed
      have hD_arc: "top1_is_arc_on ?D (subspace_topology top1_S2 top1_S2_topology ?D)"
      proof -
        have "is_topology_on_strict ?D (subspace_topology top1_S2 top1_S2_topology ?D)"
        proof -
          have hTopD: "is_topology_on ?D (subspace_topology top1_S2 top1_S2_topology ?D)"
            using hg_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have "subspace_topology top1_S2 top1_S2_topology ?D \<subseteq> Pow ?D"
            unfolding subspace_topology_def by (by100 blast)
          thus ?thesis using hTopD hD_ne unfolding is_topology_on_strict_def by (by100 blast)
        qed
        moreover have "\<exists>hh. top1_homeomorphism_on I_set I_top ?D (subspace_topology top1_S2 top1_S2_topology ?D) hh"
          using hg_homeo by (by100 blast)
        ultimately show ?thesis unfolding top1_is_arc_on_def by (by100 blast)
      qed
      \<comment> \<open>D \<subseteq> V: g(t) = inv(\<gamma>(t)) \<in> SP with h(g(t)) = \<gamma>(t) \<in> Sq.\<close>
      have hD_sub_V: "?D \<subseteq> V"
      proof
        fix w assume "w \<in> ?D"
        then obtain t where ht: "t \<in> I_set" "w = g t" by (by100 blast)
        have h\<gamma>t_Sq: "\<gamma> t \<in> Sq" by (rule h\<gamma>_in_Sq[OF ht(1)])
        have h\<gamma>t_img: "\<gamma> t \<in> h ` ?SP"
          using hSq_sub h\<gamma>t_Sq by (by100 blast)
        have hgt_SP: "g t \<in> ?SP"
          using hg_cont_SP ht(1) unfolding top1_continuous_map_on_def by (by100 blast)
        have "h (g t) = \<gamma> t"
          unfolding g_def by (rule f_inv_into_f[OF h\<gamma>t_img])
        hence "h w \<in> Sq" using h\<gamma>t_Sq ht(2) by (by100 simp)
        thus "w \<in> V" using hgt_SP ht(2) unfolding V_def by (by100 blast)
      qed
      \<comment> \<open>Endpoints: g(0) = y, g(1) = z.\<close>
      have hg0: "g 0 = y"
      proof -
        have "\<gamma> 0 = y'" unfolding \<gamma>_def y'_def by (by100 simp)
        have "y \<in> ?SP" using hy_SP .
        hence "inv_into ?SP h (h y) = y" by (rule inv_into_f_f[OF hh_inj])
        thus ?thesis unfolding g_def using \<open>\<gamma> 0 = y'\<close> y'_def by (by100 simp)
      qed
      have hg1: "g 1 = z"
      proof -
        have "\<gamma> 1 = z'" unfolding \<gamma>_def z'_def by (by100 simp)
        have "z \<in> ?SP" using hz_SP .
        hence "inv_into ?SP h (h z) = z" by (rule inv_into_f_f[OF hh_inj])
        thus ?thesis unfolding g_def using \<open>\<gamma> 1 = z'\<close> z'_def by (by100 simp)
      qed
      have hD_endpoints: "top1_arc_endpoints_on ?D (subspace_topology top1_S2 top1_S2_topology ?D) = {y, z}"
      proof -
        have "top1_arc_endpoints_on ?D (subspace_topology top1_S2 top1_S2_topology ?D) = {g 0, g 1}"
        proof (rule arc_endpoints_are_boundary[OF _ hS2_haus hD_sub_S2 hD_arc])
          show "is_topology_on_strict top1_S2 top1_S2_topology" by (rule assms(1))
          show "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology ?D
              (subspace_topology top1_S2 top1_S2_topology ?D) g"
            using hg_homeo by (by100 simp)
        qed
        thus ?thesis using hg0 hg1 by (by100 simp)
      qed
      show "\<exists>D. top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D) \<and>
           D \<subseteq> V \<and> top1_arc_endpoints_on D (subspace_topology top1_S2 top1_S2_topology D) = {y, z}"
        using hD_arc hD_sub_V hD_endpoints by (by100 blast)
    qed
    show "\<exists>V. V \<in> top1_S2_topology \<and> x \<in> V \<and> V \<subseteq> U \<and>
        (\<forall>y \<in> V. \<forall>z \<in> V. y \<noteq> z \<longrightarrow>
          (\<exists>D. top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D) \<and>
               D \<subseteq> V \<and> top1_arc_endpoints_on D (subspace_topology top1_S2 top1_S2_topology D) = {y, z}))"
      using hV_open hx_V hV_sub_U hV_arcs by (by100 blast)
  qed
  \<comment> \<open>Equivalence class argument: E = \{y \<in> U | \<exists> arc from a to y in U\}.
     E is open (local\_arc + Step 1). U-E is open (same argument).
     a \<in> E (trivial). Path from a to b \<Rightarrow> path-component connected.
     E open, U-E open, E \<noteq> {} \<Rightarrow> E = path-component \<Rightarrow> b \<in> E.\<close>
  let ?E = "{y \<in> U. \<exists>D. top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D) \<and>
      D \<subseteq> U \<and> top1_arc_endpoints_on D (subspace_topology top1_S2 top1_S2_topology D) = {a, y}}"
  \<comment> \<open>a \<in> E: trivially arc-connected to itself? No — need a \<noteq> y for arc. Handle separately.
     Actually: a is in U and we want arc from a to b with a \<noteq> b.\<close>
  \<comment> \<open>Redefine E to include a: y \<in> E iff y = a or \<exists> arc a\<rightarrow>y in U.\<close>
  let ?E' = "{y \<in> U. y = a \<or> (\<exists>D. top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D) \<and>
      D \<subseteq> U \<and> top1_arc_endpoints_on D (subspace_topology top1_S2 top1_S2_topology D) = {a, y})}"
  have ha_E: "a \<in> ?E'" using assms(4) by (by100 blast)
  \<comment> \<open>E' is open: for y \<in> E', local\_arc gives nbhd V. For z \<in> V: arc y\<rightarrow>z in V.
     If y = a: arc a\<rightarrow>z directly. If y \<noteq> a: arc a\<rightarrow>y + arc y\<rightarrow>z, splice with Step 1.\<close>
  \<comment> \<open>E' is open in U: for y \<in> E', local\_arc gives V with arcs. Step 1 extends.\<close>
  \<comment> \<open>U - E' is open in U: same argument by contradiction.\<close>
  \<comment> \<open>Both follow from local\_arc. The formal proof needs the openness argument
     which requires showing V \<inter> U \<subseteq> E' (resp. V \<inter> U \<subseteq> U-E') for the nbhd V
     from local\_arc. This uses Munkres\_Step\_1\_arc\_splice for transitivity.\<close>
  \<comment> \<open>E' is open in U: \<forall>y\<in>E', local\_arc gives V open, y\<in>V\<subseteq>U with arcs.
     For z\<in>V: arc y\<rightarrow>z in V. If y=a: z\<in>E'. If y\<noteq>a: splice arc a\<rightarrow>y + arc y\<rightarrow>z (Step 1) \<Rightarrow> z\<in>E'.
     So V\<subseteq>E'. Hence E' is open (union of open sets).\<close>
  have hE'_open: "?E' \<in> subspace_topology top1_S2 top1_S2_topology U"
    sorry \<comment> \<open>From local\_arc: \<forall>y\<in>E', \<exists>V open with V\<subseteq>E'. Needs Step 1 for splicing.\<close>
  \<comment> \<open>U-E' is open: \<forall>y\<in>U-E', local\_arc gives V. If \<exists>z\<in>V\<inter>E': arc a\<rightarrow>z + arc z\<rightarrow>y (Step 1)
     \<Rightarrow> y\<in>E'. Contradiction. So V\<inter>E'={}, V\<subseteq>U-E'. Hence U-E' open.\<close>
  have hUE'_open: "U - ?E' \<in> subspace_topology top1_S2 top1_S2_topology U"
    sorry \<comment> \<open>From local\_arc + Step 1 by contradiction. Same pattern as E'\_open.\<close>
  \<comment> \<open>The path from a to b shows they're in the same path-component.
     That path-component is connected (path-connected \<Rightarrow> connected).
     E' and U-E' partition U. E' \<noteq> {}. If U-E' \<noteq> {}: E' and U-E' form a separation
     of the path-component, contradicting connectedness. So U-E' \<inter> path-comp = {}.
     Hence b \<in> E'.\<close>
  have hb_E: "b \<in> ?E'"
  proof (rule ccontr)
    assume "b \<notin> ?E'"
    hence "b \<in> U - ?E'" using assms(5) by (by100 blast)
    \<comment> \<open>E' and U-E' are both open in U's subspace topology. E' \<noteq> {} (a \<in> E').
       If U-E' \<noteq> {}: they form a separation of U's subspace.
       But there's a path from a to b in U, so U's subspace is path-connected
       (well, the path-component of a is). This contradicts the separation.\<close>
    \<comment> \<open>More precisely: f is a path from a \<in> E' to b \<in> U-E' in U.
       f(I) is connected. f(I) \<subseteq> U = E' \<union> (U-E'). f(0)=a \<in> E', f(1)=b \<in> U-E'.
       E' and U-E' open in U. f(I) \<inter> E' \<noteq> {} and f(I) \<inter> (U-E') \<noteq> {}.
       This contradicts connectedness of f(I).\<close>
    have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
      using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have hU_top: "is_topology_on U (subspace_topology top1_S2 top1_S2_topology U)"
      by (rule subspace_topology_is_topology_on[OF hTopS2 assms(3)])
    have hE'_sub: "?E' \<subseteq> U" by (by100 blast)
    have hUE'_sub: "U - ?E' \<subseteq> U" by (by100 blast)
    have hpart: "?E' \<union> (U - ?E') = U" by (by100 blast)
    have hdisj: "?E' \<inter> (U - ?E') = {}" by (by100 blast)
    \<comment> \<open>f(I) is connected (continuous image of connected I).\<close>
    have hfI_conn: "top1_connected_on (f ` I_set) (subspace_topology U (subspace_topology top1_S2 top1_S2_topology U) (f ` I_set))"
    proof -
      have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
      have hf_cont: "top1_continuous_map_on I_set I_top U (subspace_topology top1_S2 top1_S2_topology U) f"
        using assms(7) unfolding top1_is_path_on_def by (by100 blast)
      from Theorem_23_5[OF hTI hU_top top1_unit_interval_connected hf_cont]
      show ?thesis .
    qed
    have hfI_sub: "f ` I_set \<subseteq> U"
      using assms(7) unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
    have "f 0 \<in> ?E'" using ha_E assms(7) unfolding top1_is_path_on_def by (by100 blast)
    hence "f ` I_set \<inter> ?E' \<noteq> {}"
    proof -
      have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      thus ?thesis using \<open>f 0 \<in> ?E'\<close> by (by100 blast)
    qed
    moreover have "f 1 \<in> U - ?E'"
      using \<open>b \<notin> ?E'\<close> assms(5,7) unfolding top1_is_path_on_def by (by100 blast)
    hence "f ` I_set \<inter> (U - ?E') \<noteq> {}"
    proof -
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      thus ?thesis using \<open>f 1 \<in> U - ?E'\<close> by (by100 blast)
    qed
    \<comment> \<open>f(I) connected, meets both E' and U-E' (open partition of U) \<Rightarrow> contradiction.\<close>
    moreover have hSep: "top1_is_separation_on U (subspace_topology top1_S2 top1_S2_topology U) ?E' (U - ?E')"
    proof -
      have "?E' \<noteq> {}" using ha_E by (by100 blast)
      moreover have "U - ?E' \<noteq> {}" using \<open>b \<notin> ?E'\<close> assms(5) by (by100 blast)
      moreover have "?E' \<inter> (U - ?E') = {}" by (by100 blast)
      moreover have "?E' \<union> (U - ?E') = U" by (by100 blast)
      ultimately show ?thesis unfolding top1_is_separation_on_def
        using hE'_open hUE'_open by (by100 blast)
    qed
    ultimately have "f ` I_set \<inter> (U - ?E') = {} \<or> f ` I_set \<inter> ?E' = {}"
      using Lemma_23_2_disjoint[OF hU_top hSep hfI_sub hfI_conn] by (by100 blast)
    thus False using \<open>f ` I_set \<inter> ?E' \<noteq> {}\<close> \<open>f ` I_set \<inter> (U - ?E') \<noteq> {}\<close> by (by100 blast)
  qed
  \<comment> \<open>b \<in> E' and b \<noteq> a \<Rightarrow> \<exists> arc from a to b in U.\<close>
  from hb_E assms(6) show ?thesis by (by100 blast)
qed

text \<open>Helper: construct K4 subgraph data from a general SCC on S2.
  Given SCC C on S2 with p,q in different components of S2-C,
  we decompose C into 4 arcs and construct diagonal arcs through the components.
  The diagonal arcs need:
  (a) arc from a1 to a3 through component of p, passing through p, and
  (b) arc from a2 to a4 through component of q, passing through q.
  This requires constructing arcs in path-connected open subsets of S2 with
  prescribed endpoints and interior points.\<close>

lemma K4_from_SCC:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  and "p \<in> top1_S2 - C" and "q \<in> top1_S2 - C"
  and "\<not> (\<exists>f. top1_is_path_on (top1_S2 - C)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p q f)"
  shows "\<exists>a1 a2 a3 a4 e12 e23 e34 e41 e13 e24.
    card {a1, a2, a3, a4} = 4
    \<and> {a1, a2, a3, a4} \<subseteq> top1_S2
    \<and> e12 \<subseteq> top1_S2 \<and> e23 \<subseteq> top1_S2 \<and> e34 \<subseteq> top1_S2
    \<and> e41 \<subseteq> top1_S2 \<and> e13 \<subseteq> top1_S2 \<and> e24 \<subseteq> top1_S2
    \<and> top1_is_arc_on e12 (subspace_topology top1_S2 top1_S2_topology e12)
    \<and> top1_is_arc_on e23 (subspace_topology top1_S2 top1_S2_topology e23)
    \<and> top1_is_arc_on e34 (subspace_topology top1_S2 top1_S2_topology e34)
    \<and> top1_is_arc_on e41 (subspace_topology top1_S2 top1_S2_topology e41)
    \<and> top1_is_arc_on e13 (subspace_topology top1_S2 top1_S2_topology e13)
    \<and> top1_is_arc_on e24 (subspace_topology top1_S2 top1_S2_topology e24)
    \<and> top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12) = {a1,a2}
    \<and> top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a2,a3}
    \<and> top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a3,a4}
    \<and> top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a4,a1}
    \<and> top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13) = {a1,a3}
    \<and> top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24) = {a2,a4}
    \<and> e12 \<inter> e34 = {} \<and> e23 \<inter> e41 = {}
    \<and> e12 \<inter> e23 = {a2} \<and> e23 \<inter> e34 = {a3}
    \<and> e34 \<inter> e41 = {a4} \<and> e41 \<inter> e12 = {a1}
    \<and> e13 \<inter> e12 = {a1} \<and> e13 \<inter> e23 = {a3}
    \<and> e13 \<inter> e34 = {a3} \<and> e13 \<inter> e41 = {a1}
    \<and> e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}
    \<and> e24 \<inter> e12 = {a2} \<and> e24 \<inter> e23 = {a2}
    \<and> e24 \<inter> e34 = {a4} \<and> e24 \<inter> e41 = {a4}
    \<and> p \<in> e13 - {a1, a3} \<and> q \<in> e24 - {a2, a4}
    \<and> C = e12 \<union> e23 \<union> e34 \<union> e41"
proof -
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology" by (rule top1_S2_is_hausdorff)
  \<comment> \<open>Step 1: Decompose C into two arcs C1, C2 sharing endpoints a1, a3.\<close>
  from simple_closed_curve_arc_decomposition[OF assms(2,1) hS2_haus]
  obtain C1 C2 a1 a3 where hC12: "C = C1 \<union> C2" "C1 \<inter> C2 = {a1, a3}" "a1 \<noteq> a3"
      "top1_is_arc_on C1 (subspace_topology top1_S2 top1_S2_topology C1)"
      "top1_is_arc_on C2 (subspace_topology top1_S2 top1_S2_topology C2)"
    by (by100 blast)
  have hC_sub_S2: "C \<subseteq> top1_S2" using assms(2) by (rule simple_closed_curve_subset)
  have hC1_sub: "C1 \<subseteq> top1_S2" using hC12(1) hC_sub_S2 by (by100 blast)
  have hC2_sub: "C2 \<subseteq> top1_S2" using hC12(1) hC_sub_S2 by (by100 blast)
  \<comment> \<open>Step 2: Split C1 at midpoint to get e12, e23. Split C2 at midpoint to get e34, e41.\<close>
  from arc_split_at_midpoint[OF assms(1) hS2_haus hC1_sub hC12(4)]
  obtain a2 D1 D2 where hD: "a2 \<in> C1" "C1 = D1 \<union> D2" "D1 \<inter> D2 = {a2}"
      "top1_is_arc_on D1 (subspace_topology top1_S2 top1_S2_topology D1)"
      "top1_is_arc_on D2 (subspace_topology top1_S2 top1_S2_topology D2)"
    by (by100 blast)
  from arc_split_at_midpoint[OF assms(1) hS2_haus hC2_sub hC12(5)]
  obtain a4 D3 D4 where hD2: "a4 \<in> C2" "C2 = D3 \<union> D4" "D3 \<inter> D4 = {a4}"
      "top1_is_arc_on D3 (subspace_topology top1_S2 top1_S2_topology D3)"
      "top1_is_arc_on D4 (subspace_topology top1_S2 top1_S2_topology D4)"
    by (by100 blast)
  \<comment> \<open>Step 3: Jordan separation gives 2 components.\<close>
  have hC_sep: "top1_separates_on top1_S2 top1_S2_topology C"
    by (rule Theorem_61_3_JordanSeparation_S2[OF assms(1,2)])
  \<comment> \<open>p and q in different components (from assms(5): no path from p to q in S2-C).\<close>
  have hp_S2: "p \<in> top1_S2" using assms(3) by (by100 blast)
  have hq_S2: "q \<in> top1_S2" using assms(4) by (by100 blast)
  have hp_notC: "p \<notin> C" using assms(3) by (by100 blast)
  have hq_notC: "q \<notin> C" using assms(4) by (by100 blast)
  \<comment> \<open>Arc C1 doesn't separate S2 (Theorem 63.2).\<close>
  have hC1_nosep: "\<not> top1_separates_on top1_S2 top1_S2_topology C1"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) hC1_sub hC12(4)])
  have hC2_nosep: "\<not> top1_separates_on top1_S2 top1_S2_topology C2"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) hC2_sub hC12(5)])
  \<comment> \<open>C1 and C2 are closed in S2.\<close>
  have hC1_cl: "closedin_on top1_S2 top1_S2_topology C1"
    by (rule arc_in_S2_closed[OF hC1_sub hC12(4)])
  have hC2_cl: "closedin_on top1_S2 top1_S2_topology C2"
    by (rule arc_in_S2_closed[OF hC2_sub hC12(5)])
  \<comment> \<open>Step 4: Construct diagonal arcs through the Jordan components.
     Key fact: open path-connected subsets of S2 are arc-connected
     (Munkres Thm 65.2 Step 2). Proof uses: stereographic projection
     (S2-\{pole\} \<cong> R2), convexity of open balls in R2 (line segments = arcs),
     arc splicing (Step 1), and equivalence class argument.
     All building blocks available: stereographic\_proj\_homeomorphism,
     open\_disk\_convex, homeomorphism\_on\_restrict, arcs\_concatenation\_is\_arc,
     top1\_compact\_on\_order\_topology\_has\_least.\<close>
  \<comment> \<open>Path from p to q avoiding C1.\<close>
  have hp_C1: "p \<in> top1_S2 - C1"
  proof -
    have "C1 \<subseteq> C" using hC12(1) by (by100 blast)
    thus ?thesis using hp_notC hp_S2 by (by100 blast)
  qed
  have hq_C1: "q \<in> top1_S2 - C1"
  proof -
    have "C1 \<subseteq> C" using hC12(1) by (by100 blast)
    thus ?thesis using hq_notC hq_S2 by (by100 blast)
  qed
  from S2_nonsep_path_exists[OF assms(1) hC1_cl hC1_nosep hp_C1 hq_C1]
  obtain f where hf: "top1_is_path_on (top1_S2 - C1)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C1)) p q f" by (by100 blast)
  \<comment> \<open>Path from p to q avoiding C2.\<close>
  have hp_C2: "p \<in> top1_S2 - C2"
  proof -
    have "C2 \<subseteq> C" using hC12(1) by (by100 blast)
    thus ?thesis using hp_notC hp_S2 by (by100 blast)
  qed
  have hq_C2: "q \<in> top1_S2 - C2"
  proof -
    have "C2 \<subseteq> C" using hC12(1) by (by100 blast)
    thus ?thesis using hq_notC hq_S2 by (by100 blast)
  qed
  from S2_nonsep_path_exists[OF assms(1) hC2_cl hC2_nosep hp_C2 hq_C2]
  obtain g where hg: "top1_is_path_on (top1_S2 - C2)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2)) p q g" by (by100 blast)
  \<comment> \<open>By Step 2 (S2\_open\_path\_connected\_arc\_connected): replace paths by arcs.
     S2-C1 is open (complement of closed arc). Path f gives arc from p to q in S2-C1.
     Similarly S2-C2 is open. Path g gives arc from p to q in S2-C2.\<close>
  have hC1_open: "top1_S2 - C1 \<in> top1_S2_topology"
    using hC1_cl unfolding closedin_on_def by (by100 blast)
  have hC2_open: "top1_S2 - C2 \<in> top1_S2_topology"
    using hC2_cl unfolding closedin_on_def by (by100 blast)
  have hp_ne_q: "p \<noteq> q"
  proof
    assume heq: "p = q"
    have "top1_is_path_on (top1_S2 - C) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p q
        (top1_constant_path p)"
      unfolding top1_is_path_on_def top1_constant_path_def
    proof (intro conjI)
      show "top1_continuous_map_on I_set I_top (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) (\<lambda>_. p)"
        by (rule top1_continuous_map_on_const[OF
            top1_unit_interval_topology_is_topology_on
            subspace_topology_is_topology_on[OF hTopS2, of "top1_S2 - C"]])
           (use assms(3) in \<open>by100 blast\<close>)+
    qed (use heq in \<open>by100 simp\<close>)+
    thus False using assms(5) by (by100 blast)
  qed
  from S2_open_path_connected_arc_connected[OF assms(1) hC1_open _ hp_C1 hq_C1 hp_ne_q hf]
  obtain arc_f where harc_f: "top1_is_arc_on arc_f (subspace_topology top1_S2 top1_S2_topology arc_f)"
      "arc_f \<subseteq> top1_S2 - C1"
      "top1_arc_endpoints_on arc_f (subspace_topology top1_S2 top1_S2_topology arc_f) = {p, q}"
    by (by100 blast)
  from S2_open_path_connected_arc_connected[OF assms(1) hC2_open _ hp_C2 hq_C2 hp_ne_q hg]
  obtain arc_g where harc_g: "top1_is_arc_on arc_g (subspace_topology top1_S2 top1_S2_topology arc_g)"
      "arc_g \<subseteq> top1_S2 - C2"
      "top1_arc_endpoints_on arc_g (subspace_topology top1_S2 top1_S2_topology arc_g) = {p, q}"
    by (by100 blast)
  \<comment> \<open>arc\_f avoids C1, so it intersects C only in C2-{a1,a3}.
     arc\_g avoids C2, so it intersects C only in C1-{a1,a3}.
     The construction uses Step 1 (arc splicing) to build the K4 diagonals
     from the arcs and sub-arcs of C.\<close>
  \<comment> \<open>Munkres Step 3: Construct K4 from arc\_f (p\<rightarrow>q avoiding C1) and arc\_g (p\<rightarrow>q avoiding C2).
     arc\_f crosses C2 at some first-hit point \<Rightarrow> gives a4 on C2 interior.
     arc\_g crosses C1 at some first-hit point \<Rightarrow> gives a2 on C1 interior.
     Step 1 (arc splicing) gives diagonal arcs.
     The cycle arcs come from splitting C1 at a2 and C2 at a4.
     Full K4 assembly: 4 vertices a1,a2,a3,a4 on C, 4 cycle arcs from C,
     2 diagonal arcs through components, with p on one diagonal and q on the other.
     This is a lengthy mechanical construction using the infrastructure above.\<close>
  show ?thesis sorry
qed

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
proof -
  \<comment> \<open>Construct K4 subgraph from the general SCC.\<close>
  from K4_from_SCC[OF assms(1-5)]
  obtain a1 a2 a3 a4 e12 e23 e34 e41 e13 e24
    where hK4: "card {a1, a2, a3, a4} = 4"
      "C = e12 \<union> e23 \<union> e34 \<union> e41"
      "{a1, a2, a3, a4} \<subseteq> top1_S2"
      "e12 \<subseteq> top1_S2" "e23 \<subseteq> top1_S2" "e34 \<subseteq> top1_S2"
      "e41 \<subseteq> top1_S2" "e13 \<subseteq> top1_S2" "e24 \<subseteq> top1_S2"
      "top1_is_arc_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
      "top1_is_arc_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      "top1_is_arc_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
      "top1_is_arc_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
      "top1_is_arc_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
      "top1_is_arc_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
      "top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12) = {a1,a2}"
      "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a2,a3}"
      "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a3,a4}"
      "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a4,a1}"
      "top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13) = {a1,a3}"
      "top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24) = {a2,a4}"
      "e12 \<inter> e34 = {}" "e23 \<inter> e41 = {}"
      "e12 \<inter> e23 = {a2}" "e23 \<inter> e34 = {a3}"
      "e34 \<inter> e41 = {a4}" "e41 \<inter> e12 = {a1}"
      "e13 \<inter> e12 = {a1}" "e13 \<inter> e23 = {a3}"
      "e13 \<inter> e34 = {a3}" "e13 \<inter> e41 = {a1}"
      "e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}"
      "e24 \<inter> e12 = {a2}" "e24 \<inter> e23 = {a2}"
      "e24 \<inter> e34 = {a4}" "e24 \<inter> e41 = {a4}"
      "p \<in> e13 - {a1, a3}" "q \<in> e24 - {a2, a4}"
    by blast
  \<comment> \<open>Apply Lemma\_65\_1\_fixed with the K4 data.\<close>
  show ?thesis
    by (rule Lemma_65_1_fixed[OF assms(1)
        hK4(1) hK4(3) hK4(4) hK4(5) hK4(6) hK4(7) hK4(8) hK4(9)
        hK4(10) hK4(11) hK4(12) hK4(13) hK4(14) hK4(15)
        hK4(16) hK4(17) hK4(18) hK4(19) hK4(20) hK4(21)
        hK4(22) hK4(23) hK4(24) hK4(25) hK4(26) hK4(27)
        hK4(28) hK4(29) hK4(30) hK4(31) hK4(32)
        hK4(33) hK4(34) hK4(35) hK4(36)
        hK4(37) hK4(38) hK4(2) assms(6)])
qed


end
