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
      proof -
        fix t assume ht: "t \<in> I_set"
        have htr: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
        have hy1: "\<bar>fst y' - fst (h x)\<bar> < \<epsilon>" using hy'_Sq unfolding Sq_def by (by100 blast)
        have hy2: "\<bar>snd y' - snd (h x)\<bar> < \<epsilon>" using hy'_Sq unfolding Sq_def by (by100 blast)
        have hz1: "\<bar>fst z' - fst (h x)\<bar> < \<epsilon>" using hz'_Sq unfolding Sq_def by (by100 blast)
        have hz2: "\<bar>snd z' - snd (h x)\<bar> < \<epsilon>" using hz'_Sq unfolding Sq_def by (by100 blast)
        \<comment> \<open>fst coordinate: |(1-t)*a+t*b-c| \<le> |(1-t)*(a-c)| + |t*(b-c)| = (1-t)|a-c| + t|b-c| < \<epsilon>.\<close>
        have hf1: "fst (\<gamma> t) - fst (h x) = (1-t) * (fst y' - fst (h x)) + t * (fst z' - fst (h x))"
          unfolding \<gamma>_def by (simp add: algebra_simps)
        have "\<bar>fst (\<gamma> t) - fst (h x)\<bar> \<le> \<bar>(1-t) * (fst y' - fst (h x))\<bar> + \<bar>t * (fst z' - fst (h x))\<bar>"
          unfolding hf1 by (rule abs_triangle_ineq)
        also have "\<dots> = (1-t) * \<bar>fst y' - fst (h x)\<bar> + t * \<bar>fst z' - fst (h x)\<bar>"
          using htr by (simp add: abs_mult)
        also have "\<dots> < \<epsilon>"
        proof -
          have h_le1: "(1-t) * \<bar>fst y' - fst (h x)\<bar> \<le> (1-t) * \<epsilon>"
            by (rule mult_left_mono[OF less_imp_le[OF hy1]]) (use htr in linarith)
          have h_le2: "t * \<bar>fst z' - fst (h x)\<bar> \<le> t * \<epsilon>"
            by (rule mult_left_mono[OF less_imp_le[OF hz1]]) (use htr in linarith)
          show ?thesis
          proof (cases "t = 0")
            case True thus ?thesis using hy1 h_le2 by (simp add: algebra_simps)
          next
            case False
            hence "t > 0" using htr by (by100 linarith)
            hence hfst_strict: "t * \<bar>fst z' - fst (h x)\<bar> < t * \<epsilon>" using hz1 by (by100 simp)
            have "(1-t) * \<epsilon> + t * \<epsilon> = \<epsilon>" by (simp add: algebra_simps)
            thus ?thesis using h_le1 hfst_strict by linarith
          qed
        qed
        finally have hfst: "\<bar>fst (\<gamma> t) - fst (h x)\<bar> < \<epsilon>" .
        \<comment> \<open>snd coordinate: same argument.\<close>
        have hs1: "snd (\<gamma> t) - snd (h x) = (1-t) * (snd y' - snd (h x)) + t * (snd z' - snd (h x))"
          unfolding \<gamma>_def by (simp add: algebra_simps)
        have "\<bar>snd (\<gamma> t) - snd (h x)\<bar> \<le> \<bar>(1-t) * (snd y' - snd (h x))\<bar> + \<bar>t * (snd z' - snd (h x))\<bar>"
          unfolding hs1 by (rule abs_triangle_ineq)
        also have "\<dots> = (1-t) * \<bar>snd y' - snd (h x)\<bar> + t * \<bar>snd z' - snd (h x)\<bar>"
          using htr by (simp add: abs_mult)
        also have "\<dots> < \<epsilon>"
        proof -
          have h_le1: "(1-t) * \<bar>snd y' - snd (h x)\<bar> \<le> (1-t) * \<epsilon>"
            by (rule mult_left_mono[OF less_imp_le[OF hy2]]) (use htr in linarith)
          have h_le2: "t * \<bar>snd z' - snd (h x)\<bar> \<le> t * \<epsilon>"
            by (rule mult_left_mono[OF less_imp_le[OF hz2]]) (use htr in linarith)
          show ?thesis
          proof (cases "t = 0")
            case True thus ?thesis using hy2 h_le2 by (simp add: algebra_simps)
          next
            case False
            hence "t > 0" using htr by (by100 linarith)
            hence hsnd_strict: "t * \<bar>snd z' - snd (h x)\<bar> < t * \<epsilon>" using hz2 by (by100 simp)
            have "(1-t) * \<epsilon> + t * \<epsilon> = \<epsilon>" by (simp add: algebra_simps)
            thus ?thesis using h_le1 hsnd_strict by linarith
          qed
        qed
        finally have hsnd: "\<bar>snd (\<gamma> t) - snd (h x)\<bar> < \<epsilon>" .
        show "\<gamma> t \<in> Sq" using hfst hsnd unfolding Sq_def by (by100 blast)
      qed
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
      proof (rule inj_onI)
        fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set" and hgeq: "g s = g t"
        \<comment> \<open>\<gamma> maps I\_set into h`SP (via Sq \<subseteq> h`(U\<inter>SP) \<subseteq> h`SP).\<close>
        have hgs_img: "\<gamma> s \<in> h ` ?SP" using h\<gamma>_in_Sq[OF hs] hSq_sub by (by100 blast)
        have hgt_img: "\<gamma> t \<in> h ` ?SP" using h\<gamma>_in_Sq[OF ht] hSq_sub by (by100 blast)
        \<comment> \<open>g(s) = g(t) \<Rightarrow> inv(h, \<gamma>(s)) = inv(h, \<gamma>(t)) \<Rightarrow> \<gamma>(s) = \<gamma>(t) (since h \<circ> inv = id on image).\<close>
        from hgeq have "inv_into ?SP h (\<gamma> s) = inv_into ?SP h (\<gamma> t)" unfolding g_def .
        hence h\<gamma>_eq: "\<gamma> s = \<gamma> t"
          using f_inv_into_f[OF hgs_img] f_inv_into_f[OF hgt_img] by (by100 metis)
        \<comment> \<open>\<gamma> injective when y' \<noteq> z': from pair equality extract (s-t)*(z'-y') = 0.\<close>
        from h\<gamma>_eq have hfst_eq: "(1-s) * fst y' + s * fst z' = (1-t) * fst y' + t * fst z'"
          unfolding \<gamma>_def by (by100 simp)
        hence "(s - t) * (fst z' - fst y') = 0"
          by (simp add: algebra_simps)
        moreover from h\<gamma>_eq have hsnd_eq: "(1-s) * snd y' + s * snd z' = (1-t) * snd y' + t * snd z'"
          unfolding \<gamma>_def by (by100 simp)
        hence "(s - t) * (snd z' - snd y') = 0"
          by (simp add: algebra_simps)
        ultimately show "s = t"
        proof (cases "s = t")
          case True thus ?thesis .
        next
          case False
          hence "fst z' - fst y' = 0" and "snd z' - snd y' = 0"
            using \<open>(s - t) * (fst z' - fst y') = 0\<close> \<open>(s - t) * (snd z' - snd y') = 0\<close>
            by (by100 simp)+
          hence "fst z' = fst y'" "snd z' = snd y'" by (by100 simp)+
          hence "y' = z'" by (cases y', cases z') (by100 simp)
          with hy'z'_ne show ?thesis by (by100 blast)
        qed
      qed
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
  \<comment> \<open>E' open: each y \<in> E' has open V \<subseteq> E' (from local\_arc + Step 1 splice).
     U-E' open: same by contradiction. Both are standard equivalence-class arguments.\<close>
  \<comment> \<open>Key helper: the open cover property.\<close>
  have hE'_cover: "\<forall>y \<in> ?E'. \<exists>W \<in> top1_S2_topology. y \<in> W \<and> W \<subseteq> ?E'"
  proof
    fix y assume hy_E: "y \<in> ?E'"
    hence hy_U: "y \<in> U" by (by100 blast)
    from local_arc[OF hy_U] obtain Vy where
      hVy_all: "Vy \<in> top1_S2_topology \<and> y \<in> Vy \<and> Vy \<subseteq> U \<and>
        (\<forall>p \<in> Vy. \<forall>q \<in> Vy. p \<noteq> q \<longrightarrow>
          (\<exists>D. top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D) \<and>
               D \<subseteq> Vy \<and> top1_arc_endpoints_on D (subspace_topology top1_S2 top1_S2_topology D) = {p, q}))"
      by auto
    have hVy_open: "Vy \<in> top1_S2_topology" using hVy_all by auto
    have hVy_y: "y \<in> Vy" using hVy_all by auto
    have hVy_U: "Vy \<subseteq> U" using hVy_all by auto
    have hVy_arcs: "\<And>p q. p \<in> Vy \<Longrightarrow> q \<in> Vy \<Longrightarrow> p \<noteq> q \<Longrightarrow>
        \<exists>D. top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D) \<and>
             D \<subseteq> Vy \<and> top1_arc_endpoints_on D (subspace_topology top1_S2 top1_S2_topology D) = {p, q}"
      using hVy_all by auto
    have "Vy \<subseteq> ?E'"
    proof
      fix z assume hz_Vy: "z \<in> Vy"
      have hz_U: "z \<in> U" using hz_Vy hVy_U by (by100 blast)
      show "z \<in> ?E'"
      proof (cases "z = a")
        case True thus ?thesis using hz_U by (by100 blast)
      next
        case hz_ne_a: False
        show ?thesis
        proof (cases "y = z")
          case True thus ?thesis using hy_E by (by100 simp)
        next
          case hy_ne_z: False
          \<comment> \<open>Get arc D\_yz from y to z in Vy.\<close>
          from hVy_arcs[OF hVy_y hz_Vy hy_ne_z] obtain Dyz where
            hDyz: "top1_is_arc_on Dyz (subspace_topology top1_S2 top1_S2_topology Dyz)"
              "Dyz \<subseteq> Vy"
              "top1_arc_endpoints_on Dyz (subspace_topology top1_S2 top1_S2_topology Dyz) = {y, z}"
            by (by100 blast)
          have hDyz_U: "Dyz \<subseteq> U" using hDyz(2) hVy_U by (by100 blast)
          have hDyz_S2: "Dyz \<subseteq> top1_S2" using hDyz_U assms(3) by (by100 blast)
          show ?thesis
          proof (cases "y = a")
            case True
            \<comment> \<open>y = a: arc Dyz has endpoints {a,z}, Dyz \<subseteq> U. So z \<in> E'.\<close>
            thus ?thesis using hz_U hz_ne_a hDyz(1,3) hDyz_U True by (by100 blast)
          next
            case hy_ne_a: False
            \<comment> \<open>y \<noteq> a: have arc a\<rightarrow>y in U (from y \<in> E') and arc y\<rightarrow>z in Vy \<subseteq> U.
               Need to splice to get arc a\<rightarrow>z in U.\<close>
            from hy_E hy_ne_a obtain Day where
              hDay: "top1_is_arc_on Day (subspace_topology top1_S2 top1_S2_topology Day)"
                "Day \<subseteq> U"
                "top1_arc_endpoints_on Day (subspace_topology top1_S2 top1_S2_topology Day) = {a, y}"
              by (by100 blast)
            have hDay_S2: "Day \<subseteq> top1_S2" using hDay(2) assms(3) by (by100 blast)
            \<comment> \<open>Splice arc a\<rightarrow>y (Day) with arc y\<rightarrow>z (Dyz) to get arc a\<rightarrow>z.
               Munkres\_Step\_1 requires a \<notin> Dyz. If a \<in> Dyz: split Dyz at a, get sub-arc a\<rightarrow>z.\<close>
            show ?thesis
            proof (cases "a \<notin> Dyz")
              case True
              \<comment> \<open>a \<notin> Dyz: directly apply Munkres\_Step\_1\_arc\_splice.\<close>
              have hab: "a \<noteq> y" using hy_ne_a by (by100 blast)
              have hyz: "y \<noteq> z" using hy_ne_z by (by100 blast)
              from Munkres_Step_1_arc_splice[OF assms(1) hDay(1) hDyz(1) hDay_S2 hDyz_S2
                  hDay(3) hDyz(3) hab hyz True]
              obtain Daz where
                hDaz: "top1_is_arc_on Daz (subspace_topology top1_S2 top1_S2_topology Daz)"
                  "Daz \<subseteq> Day \<union> Dyz" "a \<in> Daz" "z \<in> Daz"
                  "top1_arc_endpoints_on Daz (subspace_topology top1_S2 top1_S2_topology Daz) = {a, z}"
                by (by100 blast)
              have "Daz \<subseteq> U" using hDaz(2) hDay(2) hDyz_U by (by100 blast)
              thus ?thesis using hz_U hz_ne_a hDaz(1,5) \<open>Daz \<subseteq> U\<close> by (by100 blast)
            next
              case False
              hence ha_Dyz: "a \<in> Dyz" by (by100 simp)
              \<comment> \<open>a \<in> Dyz but a \<notin> endpoints {y,z}, so a is interior. Split Dyz at a.\<close>
              have ha_not_ep: "a \<notin> top1_arc_endpoints_on Dyz (subspace_topology top1_S2 top1_S2_topology Dyz)"
                using hDyz(3) hy_ne_a hz_ne_a by (by100 simp)
              from arc_split_at_given_point[OF assms(1) hS2_haus hDyz_S2 hDyz(1) ha_Dyz ha_not_ep hDyz(3) hy_ne_z]
              obtain D1 D2 where hD12:
                "Dyz = D1 \<union> D2" "D1 \<inter> D2 = {a}"
                "top1_is_arc_on D1 (subspace_topology top1_S2 top1_S2_topology D1)"
                "top1_is_arc_on D2 (subspace_topology top1_S2 top1_S2_topology D2)"
                "y \<in> D1" "z \<in> D2" "a \<in> D1" "a \<in> D2" "D1 \<subseteq> top1_S2" "D2 \<subseteq> top1_S2"
                by auto
              \<comment> \<open>D2 is a sub-arc with a \<in> D2 and z \<in> D2. D2 \<subseteq> Dyz \<subseteq> U.\<close>
              have hD2_U: "D2 \<subseteq> U" using hD12(1) hDyz_U by (by100 blast)
              \<comment> \<open>The endpoints of D2 are {a, z} (a and z are the boundary points).\<close>
              have hD2_ep: "top1_arc_endpoints_on D2 (subspace_topology top1_S2 top1_S2_topology D2) = {a, z}"
                by (rule arc_split_endpoints(2)[OF assms(1) hS2_haus hDyz_S2 hDyz(1)
                    hD12(1,2,3,4,5,6,7,8,9,10) hDyz(3) ha_not_ep])
              thus ?thesis using hz_U hz_ne_a hD12(4) hD2_U hD2_ep by (by100 blast)
            qed
          qed
        qed
      qed
    qed
    thus "\<exists>W \<in> top1_S2_topology. y \<in> W \<and> W \<subseteq> ?E'" using hVy_open hVy_y by (by100 blast)
  qed
  have hE'_sub_S2: "?E' \<subseteq> top1_S2" using assms(3) by (by100 blast)
  have hE'_open_S2: "?E' \<in> top1_S2_topology"
    by (rule top1_open_of_local_subsets[OF hTopS2 hE'_sub_S2 hE'_cover])
  have hE'_open: "?E' \<in> subspace_topology top1_S2 top1_S2_topology U"
  proof -
    have "U \<inter> ?E' \<in> subspace_topology top1_S2 top1_S2_topology U"
      by (rule subspace_topology_memI[OF hE'_open_S2])
    moreover have "U \<inter> ?E' = ?E'" by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>U-E' open: same cover argument. Each y \<in> U-E' has open V \<subseteq> U-E'.\<close>
  have hUE'_cover: "\<forall>y \<in> U - ?E'. \<exists>W \<in> top1_S2_topology. y \<in> W \<and> W \<subseteq> U - ?E'"
  proof
    fix y assume hy_UE: "y \<in> U - ?E'"
    hence hy_U: "y \<in> U" and hy_notE: "y \<notin> ?E'" by auto
    from local_arc[OF hy_U] obtain Vy where
      hVy_all: "Vy \<in> top1_S2_topology \<and> y \<in> Vy \<and> Vy \<subseteq> U \<and>
        (\<forall>p \<in> Vy. \<forall>q \<in> Vy. p \<noteq> q \<longrightarrow>
          (\<exists>D. top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D) \<and>
               D \<subseteq> Vy \<and> top1_arc_endpoints_on D (subspace_topology top1_S2 top1_S2_topology D) = {p, q}))"
      by auto
    have hVy_open: "Vy \<in> top1_S2_topology" using hVy_all by auto
    have hVy_y: "y \<in> Vy" using hVy_all by auto
    have hVy_U: "Vy \<subseteq> U" using hVy_all by auto
    have hVy_arcs: "\<And>p q. p \<in> Vy \<Longrightarrow> q \<in> Vy \<Longrightarrow> p \<noteq> q \<Longrightarrow>
        \<exists>D. top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D) \<and>
             D \<subseteq> Vy \<and> top1_arc_endpoints_on D (subspace_topology top1_S2 top1_S2_topology D) = {p, q}"
      using hVy_all by auto
    \<comment> \<open>Show Vy \<subseteq> U - E' by contradiction: if z \<in> Vy \<inter> E', splice gives y \<in> E'. \<bottom>.\<close>
    have hVy_disj: "Vy \<inter> ?E' = {}"
    proof (rule ccontr)
      assume "Vy \<inter> ?E' \<noteq> {}"
      then obtain z where hz_Vy: "z \<in> Vy" and hz_E: "z \<in> ?E'" by auto
      have hz_U: "z \<in> U" using hz_Vy hVy_U by (by100 blast)
      \<comment> \<open>z \<in> E' and z \<in> Vy. Arc z\<rightarrow>y in Vy (if z \<noteq> y). Combined with arc a\<rightarrow>z from E',
         splice gives arc a\<rightarrow>y. But y \<notin> E'. Contradiction.\<close>
      show False
      proof (cases "z = y")
        case True thus ?thesis using hz_E hy_notE by (by100 blast)
      next
        case hz_ne_y: False
        \<comment> \<open>Arc z\<rightarrow>y in Vy.\<close>
        from hVy_arcs[OF hz_Vy hVy_y hz_ne_y] obtain Dzy where
          hDzy: "top1_is_arc_on Dzy (subspace_topology top1_S2 top1_S2_topology Dzy)"
            "Dzy \<subseteq> Vy"
            "top1_arc_endpoints_on Dzy (subspace_topology top1_S2 top1_S2_topology Dzy) = {z, y}"
          by (by100 blast)
        have hDzy_U: "Dzy \<subseteq> U" using hDzy(2) hVy_U by (by100 blast)
        have hDzy_S2: "Dzy \<subseteq> top1_S2" using hDzy_U assms(3) by (by100 blast)
        show False
        proof (cases "z = a")
          case True
          \<comment> \<open>z = a: arc Dzy has endpoints {a, y}, Dzy \<subseteq> U. So y \<in> E'. Contradiction.\<close>
          have "y \<in> ?E'" using hy_U hDzy(1,3) hDzy_U True
          proof -
            have hy_ne_a: "y \<noteq> a" using hy_notE hy_U by (by100 blast)
            show ?thesis using hy_U hy_ne_a hDzy(1,3) hDzy_U True by (by100 blast)
          qed
          thus False using hy_notE by (by100 blast)
        next
          case hz_ne_a: False
          \<comment> \<open>z \<noteq> a: arc a\<rightarrow>z (from z \<in> E') + arc z\<rightarrow>y. Splice.\<close>
          from hz_E hz_ne_a obtain Daz where
            hDaz: "top1_is_arc_on Daz (subspace_topology top1_S2 top1_S2_topology Daz)"
              "Daz \<subseteq> U"
              "top1_arc_endpoints_on Daz (subspace_topology top1_S2 top1_S2_topology Daz) = {a, z}"
            by (by100 blast)
          have hDaz_S2: "Daz \<subseteq> top1_S2" using hDaz(2) assms(3) by (by100 blast)
          \<comment> \<open>Need to get arc a\<rightarrow>y. Use same case split as in hE'\_cover.\<close>
          have hy_ne_a: "y \<noteq> a" using hy_notE hy_U by (by100 blast)
          show False
          proof (cases "a \<notin> Dzy")
            case True
            from Munkres_Step_1_arc_splice[OF assms(1) hDaz(1) hDzy(1) hDaz_S2 hDzy_S2
                hDaz(3) hDzy(3) _ hz_ne_y True]
            obtain Day where hDay:
              "top1_is_arc_on Day (subspace_topology top1_S2 top1_S2_topology Day)"
              "Day \<subseteq> Daz \<union> Dzy" "top1_arc_endpoints_on Day (subspace_topology top1_S2 top1_S2_topology Day) = {a, y}"
              using hz_ne_a by (by100 blast)
            have "Day \<subseteq> U" using hDay(2) hDaz(2) hDzy_U by (by100 blast)
            hence "y \<in> ?E'" using hy_U hy_ne_a hDay(1,3) \<open>Day \<subseteq> U\<close> by (by100 blast)
            thus False using hy_notE by (by100 blast)
          next
            case False
            hence "a \<in> Dzy" by (by100 simp)
            \<comment> \<open>a \<in> Dzy: split Dzy at a, get sub-arc a\<rightarrow>y directly.\<close>
            have ha_not_ep_zy: "a \<notin> top1_arc_endpoints_on Dzy (subspace_topology top1_S2 top1_S2_topology Dzy)"
              using hDzy(3) hz_ne_a hy_ne_a by (by100 simp)
            from arc_split_at_given_point[OF assms(1) hS2_haus hDzy_S2 hDzy(1) \<open>a \<in> Dzy\<close>
                ha_not_ep_zy hDzy(3) hz_ne_y]
            obtain D1' D2' where hD12':
              "Dzy = D1' \<union> D2'" "D1' \<inter> D2' = {a}"
              "top1_is_arc_on D1' (subspace_topology top1_S2 top1_S2_topology D1')"
              "top1_is_arc_on D2' (subspace_topology top1_S2 top1_S2_topology D2')"
              "z \<in> D1'" "y \<in> D2'" "a \<in> D1'" "a \<in> D2'" "D1' \<subseteq> top1_S2" "D2' \<subseteq> top1_S2"
              by auto
            have hD2'_U: "D2' \<subseteq> U" using hD12'(1) hDzy_U by (by100 blast)
            have hD2'_ep: "top1_arc_endpoints_on D2' (subspace_topology top1_S2 top1_S2_topology D2') = {a, y}"
              by (rule arc_split_endpoints(2)[OF assms(1) hS2_haus hDzy_S2 hDzy(1)
                  hD12'(1,2,3,4,5,6,7,8,9,10) hDzy(3) ha_not_ep_zy])
            hence "y \<in> ?E'" using hy_U hy_ne_a hD12'(4) hD2'_U hD2'_ep by (by100 blast)
            thus False using hy_notE by (by100 blast)
          qed
        qed
      qed
    qed
    have hVy_sub: "Vy \<subseteq> U - ?E'" using hVy_disj hVy_U by (by100 blast)
    show "\<exists>W \<in> top1_S2_topology. y \<in> W \<and> W \<subseteq> U - ?E'"
      using hVy_sub hVy_open hVy_y by auto
  qed
  have hUE'_sub_S2: "U - ?E' \<subseteq> top1_S2" using assms(3) by (by100 blast)
  have hUE'_open_S2: "U - ?E' \<in> top1_S2_topology"
    by (rule top1_open_of_local_subsets[OF hTopS2 hUE'_sub_S2 hUE'_cover])
  have hUE'_open: "U - ?E' \<in> subspace_topology top1_S2 top1_S2_topology U"
  proof -
    have "U \<inter> (U - ?E') \<in> subspace_topology top1_S2 top1_S2_topology U"
      by (rule subspace_topology_memI[OF hUE'_open_S2])
    moreover have "U \<inter> (U - ?E') = U - ?E'" by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
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

lemma scc_minus_point_connected:
  assumes hT: "is_topology_on_strict X TX" and hH: "is_hausdorff_on X TX"
  and hC: "top1_simple_closed_curve_on X TX C" and "a \<in> C"
  shows "top1_connected_on (C - {a}) (subspace_topology X TX (C - {a}))"
proof -
  \<comment> \<open>C has a continuous injective map from S1. By embedding (compact+inj+Hausdorff),
     f: S1 \<rightarrow> C is a homeomorphism. C-{a} = f(S1-{f\<inverse>(a)}). S1-{point} is an arc,
     hence connected. Homeomorphism preserves connectedness.\<close>
  obtain f where hf: "top1_continuous_map_on top1_S1 top1_S1_topology X TX f"
      "inj_on f top1_S1" "f ` top1_S1 = C"
    using hC unfolding top1_simple_closed_curve_on_def by (by100 blast)
  have hC_sub: "C \<subseteq> X" using hC by (rule simple_closed_curve_subset)
  \<comment> \<open>f is a homeomorphism S1 \<rightarrow> C (compact inj continuous to Hausdorff).\<close>
  have hf_embed: "top1_embedding_on top1_S1 top1_S1_topology X TX f"
    by (rule top1_embedding_on_compact_inj[OF
        is_topology_on_strict_imp[OF top1_S1_is_topology_on_strict]
        is_topology_on_strict_imp[OF hT] S1_compact hH hf(1,2)])
  have hf_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology C (subspace_topology X TX C) f"
    using hf_embed hf(3) unfolding top1_embedding_on_def by (by100 simp)
  \<comment> \<open>f\<inverse>(a) \<in> S1.\<close>
  have ha_S1: "inv_into top1_S1 f a \<in> top1_S1"
  proof -
    have "a \<in> f ` top1_S1" using \<open>a \<in> C\<close> hf(3) by (by100 blast)
    thus ?thesis by (rule inv_into_into)
  qed
  \<comment> \<open>S1 - {f\<inverse>(a)} is connected (S1 minus a point is an arc).\<close>
  have "top1_connected_on (top1_S1 - {inv_into top1_S1 f a})
      (subspace_topology top1_S1 top1_S1_topology (top1_S1 - {inv_into top1_S1 f a}))"
  proof -
    let ?p = "inv_into top1_S1 f a"
    \<comment> \<open>Decompose S1 into two arcs.\<close>
    have hS1_scc: "top1_simple_closed_curve_on UNIV (product_topology_on top1_open_sets top1_open_sets) top1_S1"
    proof -
      have "top1_continuous_map_on top1_S1 top1_S1_topology UNIV
          (product_topology_on top1_open_sets top1_open_sets) id"
        unfolding top1_continuous_map_on_def top1_S1_topology_def
      proof (intro conjI ballI)
        fix x assume "x \<in> top1_S1" thus "id x \<in> UNIV" by (by100 simp)
      next
        fix V :: "(real \<times> real) set"
        assume hV: "V \<in> product_topology_on top1_open_sets top1_open_sets"
        have "top1_S1 \<inter> V \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_S1"
          by (rule subspace_topology_memI) (rule hV)
        moreover have "{x \<in> top1_S1. id x \<in> V} = top1_S1 \<inter> V" by auto
        ultimately show "{x \<in> top1_S1. id x \<in> V} \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_S1"
          by (by100 simp)
      qed
      moreover have "inj_on id top1_S1" by (by100 simp)
      moreover have "id ` top1_S1 = top1_S1" by (by100 simp)
      ultimately show ?thesis unfolding top1_simple_closed_curve_on_def by (by100 blast)
    qed
    have hS1_strict: "is_topology_on_strict UNIV (product_topology_on top1_open_sets top1_open_sets :: (real \<times> real) set set)"
    proof -
      have "is_topology_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
      proof -
        have "is_topology_on (UNIV :: real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
        from product_topology_on_is_topology_on[OF this this]
        show ?thesis by (by100 simp)
      qed
      moreover have "(UNIV :: (real \<times> real) set) \<noteq> {}" by (by100 blast)
      moreover have "product_topology_on top1_open_sets top1_open_sets \<subseteq> Pow (UNIV :: (real \<times> real) set)"
        by (by100 blast)
      ultimately show ?thesis unfolding is_topology_on_strict_def by (by100 blast)
    qed
    have hR2_haus: "is_hausdorff_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
      by (rule top1_R2_is_hausdorff)
    from simple_closed_curve_arc_decomposition[OF hS1_scc hS1_strict hR2_haus]
    obtain B1 B2 e1 e2 where hB: "top1_S1 = B1 \<union> B2" "B1 \<inter> B2 = {e1, e2}" "e1 \<noteq> e2"
        "top1_is_arc_on B1 (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) B1)"
        "top1_is_arc_on B2 (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) B2)"
      by (by100 blast)
    \<comment> \<open>S1 - {p}: p is in B1 or B2 (or both = {e1,e2}).
       In each case, S1-{p} = connected pieces sharing e1 or e2.\<close>
    have "top1_connected_on (top1_S1 - {?p})
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (top1_S1 - {?p}))"
    proof -
      \<comment> \<open>Use HOL's connected via bridge lemma, then prove connected (S1-{p}) directly.\<close>
      have hbridge: "top1_connected_on (top1_S1 - {?p})
          (subspace_topology UNIV (top1_open_sets :: (real \<times> real) set set) (top1_S1 - {?p}))
        \<longleftrightarrow> connected (top1_S1 - {?p})"
        by (rule top1_connected_on_subspace_open_iff_connected)
      have hTR2_eq: "(product_topology_on top1_open_sets top1_open_sets :: (real \<times> real) set set)
          = top1_open_sets" by (rule product_topology_on_open_sets_real2)
      \<comment> \<open>Prove connected (S1-{p}) using continuous image of connected interval.\<close>
      have "connected (top1_S1 - {?p})"
      proof -
        \<comment> \<open>p \<in> S1 \<Rightarrow> \<exists>x0. top1\_R\_to\_S1(x0) = p. Then S1-{p} = R\_to\_S1 ` (x0,x0+1).\<close>
        have hp: "?p \<in> top1_S1" by (rule ha_S1)
        obtain x0 :: real where hx0: "top1_R_to_S1 x0 = ?p"
        proof -
          have "top1_R_to_S1 ` UNIV = top1_S1"
            by (rule top1_covering_map_on_surj[OF Theorem_53_1])
          hence "?p \<in> range top1_R_to_S1" using hp by (by100 blast)
          hence "\<exists>x0. top1_R_to_S1 x0 = ?p" by auto
          then obtain x0 where "top1_R_to_S1 x0 = ?p" by (by100 blast)
          thus ?thesis using that by (by100 blast)
        qed
        have "top1_S1 - {?p} = top1_R_to_S1 ` {x0 <..< x0 + 1}"
        proof (rule set_eqI, rule iffI)
          fix q assume hq: "q \<in> top1_S1 - {?p}"
          hence hq_S1: "q \<in> top1_S1" and hq_ne: "q \<noteq> ?p" by auto
          from S1_point_to_angle[OF hq_S1] obtain \<theta> where h\<theta>: "top1_R_to_S1 \<theta> = q" by auto
          \<comment> \<open>Shift \<theta> into (x0, x0+1] by adding integer.\<close>
          define k where "k = \<lfloor>x0 + 1 - \<theta>\<rfloor>"
          define t where "t = \<theta> + of_int k"
          have ht_range: "x0 < t \<and> t \<le> x0 + 1"
            unfolding t_def k_def by linarith
          have ht_img: "top1_R_to_S1 t = q"
            unfolding t_def using top1_R_to_S1_int_shift[of \<theta> k] h\<theta> by (by100 simp)
          \<comment> \<open>t \<noteq> x0+1: otherwise R\_to\_S1(t) = R\_to\_S1(x0) = p, but q \<noteq> p.\<close>
          have "t \<noteq> x0 + 1"
          proof
            assume "t = x0 + 1"
            hence "top1_R_to_S1 t = top1_R_to_S1 (x0 + 1)" by (by100 simp)
            also have "\<dots> = top1_R_to_S1 x0" using top1_R_to_S1_int_shift[of x0 1] by (by100 simp)
            also have "\<dots> = ?p" by (rule hx0)
            finally show False using ht_img hq_ne by (by100 blast)
          qed
          hence "t \<in> {x0 <..< x0 + 1}" using ht_range by (by100 simp)
          thus "q \<in> top1_R_to_S1 ` {x0 <..< x0 + 1}" using ht_img by (by100 blast)
        next
          fix q assume "q \<in> top1_R_to_S1 ` {x0 <..< x0 + 1}"
          then obtain t where ht: "t \<in> {x0 <..< x0 + 1}" "q = top1_R_to_S1 t" by (by100 blast)
          have "q \<in> top1_S1" using ht(2) unfolding top1_R_to_S1_def top1_S1_def by auto
          moreover have "q \<noteq> ?p"
          proof
            assume "q = ?p"
            hence "top1_R_to_S1 t = top1_R_to_S1 x0" using ht(2) hx0 by (by100 simp)
            hence "cos (2 * pi * t) = cos (2 * pi * x0) \<and> sin (2 * pi * t) = sin (2 * pi * x0)"
              unfolding top1_R_to_S1_def by auto
            hence "\<exists>k::int. 2 * pi * t - 2 * pi * x0 = real_of_int k * 2 * pi"
              using cos_sin_eq_imp by (by100 blast)
            then obtain k :: int where "2 * pi * t - 2 * pi * x0 = real_of_int k * 2 * pi" by auto
            hence "t - x0 = real_of_int k"
            proof -
              from \<open>2 * pi * t - 2 * pi * x0 = real_of_int k * 2 * pi\<close>
              have "(t - x0) * (2 * pi) = real_of_int k * (2 * pi)" by (simp add: algebra_simps)
              thus ?thesis using pi_gt_zero by (by100 simp)
            qed
            hence "t = x0 + real_of_int k" by (by100 linarith)
            \<comment> \<open>t \<in> (x0, x0+1), so k = 0, giving t = x0. But t > x0. Contradiction.\<close>
            moreover have "x0 < t" "t < x0 + 1" using ht(1) by auto
            ultimately have "0 < real_of_int k" "real_of_int k < 1" by linarith+
            hence "k = 0" by linarith
            hence "t = x0" using \<open>t = x0 + real_of_int k\<close> by (by100 simp)
            thus False using \<open>x0 < t\<close> by (by100 linarith)
          qed
          ultimately show "q \<in> top1_S1 - {?p}" by (by100 blast)
        qed
        moreover have "connected ({x0 <..< x0 + 1} :: real set)" by (rule connected_Ioo)
        moreover have "continuous_on {x0 <..< x0 + 1} top1_R_to_S1"
          unfolding top1_R_to_S1_def by (intro continuous_intros)
        ultimately show ?thesis
          by (metis connected_continuous_image)
      qed
      thus ?thesis using hbridge hTR2_eq by (by100 simp)
    qed
    \<comment> \<open>Transfer from R2 subspace to S1 subspace topology.\<close>
    thus ?thesis
    proof -
      have "subspace_topology top1_S1 top1_S1_topology (top1_S1 - {?p})
          = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (top1_S1 - {?p})"
        unfolding top1_S1_topology_def by (rule subspace_topology_trans[OF Diff_subset])
      thus ?thesis using \<open>top1_connected_on (top1_S1 - {?p}) _\<close> by (by100 simp)
    qed
  qed
  \<comment> \<open>Transfer: f continuous S1 \<rightarrow> X, restrict to S1-{p}. Image = C-{a}. Connected.\<close>
  let ?p = "inv_into top1_S1 f a"
  have hf_img: "f ` (top1_S1 - {?p}) = C - {a}"
  proof (rule set_eqI, rule iffI)
    fix y assume "y \<in> f ` (top1_S1 - {?p})"
    then obtain x where hx: "x \<in> top1_S1" "x \<noteq> ?p" "y = f x" by (by100 blast)
    have "y \<in> C" using hx(1,3) hf(3) by (by100 blast)
    moreover have "y \<noteq> a"
    proof
      assume "y = a" hence "f x = a" using hx(3) by (by100 simp)
      hence "x = ?p" using hf(2) hx(1) ha_S1 \<open>a \<in> C\<close> hf(3) by (metis inv_into_f_eq)
      thus False using hx(2) by (by100 blast)
    qed
    ultimately show "y \<in> C - {a}" by (by100 blast)
  next
    fix y assume "y \<in> C - {a}"
    hence hy: "y \<in> C" "y \<noteq> a" by auto
    have "y \<in> f ` top1_S1" using hy(1) hf(3) by (by100 blast)
    then obtain x where hx: "x \<in> top1_S1" "y = f x" by (by100 blast)
    have "x \<noteq> ?p"
    proof
      assume "x = ?p" hence "f x = f ?p" by (by100 simp)
      also have "f ?p = a"
      proof -
        have "a \<in> f ` top1_S1" using \<open>a \<in> C\<close> hf(3) by (by100 blast)
        thus ?thesis by (rule f_inv_into_f)
      qed
      finally show False using hy(2) hx(2) by (by100 blast)
    qed
    thus "y \<in> f ` (top1_S1 - {?p})" using hx by (by100 blast)
  qed
  have hf_cont_sub: "top1_continuous_map_on (top1_S1 - {?p})
      (subspace_topology top1_S1 top1_S1_topology (top1_S1 - {?p})) X TX f"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix x assume "x \<in> top1_S1 - {?p}" thus "f x \<in> X"
      using hf(1) unfolding top1_continuous_map_on_def by (by100 blast)
  next
    fix V assume hV: "V \<in> TX"
    have "{x \<in> top1_S1. f x \<in> V} \<in> top1_S1_topology"
      using hf(1) hV unfolding top1_continuous_map_on_def by (by100 blast)
    hence "(top1_S1 - {?p}) \<inter> {x \<in> top1_S1. f x \<in> V}
        \<in> subspace_topology top1_S1 top1_S1_topology (top1_S1 - {?p})"
      unfolding subspace_topology_def by (by100 blast)
    moreover have "{x \<in> top1_S1 - {?p}. f x \<in> V} = (top1_S1 - {?p}) \<inter> {x \<in> top1_S1. f x \<in> V}"
      by (by100 blast)
    ultimately show "{x \<in> top1_S1 - {?p}. f x \<in> V}
        \<in> subspace_topology top1_S1 top1_S1_topology (top1_S1 - {?p})" by (by100 simp)
  qed
  have hTS1p: "is_topology_on (top1_S1 - {?p})
      (subspace_topology top1_S1 top1_S1_topology (top1_S1 - {?p}))"
    by (rule subspace_topology_is_topology_on[OF
        is_topology_on_strict_imp[OF top1_S1_is_topology_on_strict]]) (by100 blast)
  have hTX: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
  from Theorem_23_5[OF hTS1p hTX \<open>top1_connected_on (top1_S1 - {?p}) _\<close> hf_cont_sub]
  have "top1_connected_on (f ` (top1_S1 - {?p})) (subspace_topology X TX (f ` (top1_S1 - {?p})))" .
  thus ?thesis using hf_img by (by100 simp)
qed

\<comment> \<open>Helper: if p \<in> A1 is not an endpoint of A1, and A1 \<inter> A2 = {p, q}, SCC C = A1 \<union> A2,
   then C-{p} is not connected. But scc\_minus\_point\_connected says it IS. Contradiction.\<close>
lemma scc_interior_contradiction:
  assumes hT: "is_topology_on_strict X TX" and hH: "is_hausdorff_on X TX"
  and hC: "top1_simple_closed_curve_on X TX C"
  and hA1: "top1_is_arc_on A1 (subspace_topology X TX A1)"
  and hA2: "top1_is_arc_on A2 (subspace_topology X TX A2)"
  and hA1_sub: "A1 \<subseteq> X" and hA2_sub: "A2 \<subseteq> X"
  and hdecomp: "C = A1 \<union> A2" and hint: "A1 \<inter> A2 = {p, q}" and hpq: "p \<noteq> q"
  and hp_A1: "p \<in> A1" and hp_not_ep: "p \<notin> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
  shows False
proof -
  \<comment> \<open>A1-{p} not connected (p is interior to arc A1).\<close>
  have "\<not> top1_connected_on (A1 - {p}) (subspace_topology A1 (subspace_topology X TX A1) (A1 - {p}))"
    using hp_not_ep hp_A1 unfolding top1_arc_endpoints_on_def by (by100 blast)
  hence hA1p_not_conn: "\<not> top1_connected_on (A1 - {p}) (subspace_topology X TX (A1 - {p}))"
  proof -
    have "subspace_topology A1 (subspace_topology X TX A1) (A1 - {p})
        = subspace_topology X TX (A1 - {p})"
      by (rule subspace_topology_trans[OF Diff_subset])
    thus ?thesis using \<open>\<not> top1_connected_on (A1 - {p}) (subspace_topology A1 (subspace_topology X TX A1) (A1 - {p}))\<close>
      by (by100 simp)
  qed
  \<comment> \<open>C-{p} connected.\<close>
  have hC_sub: "C \<subseteq> X" using hdecomp hA1_sub hA2_sub by (by100 blast)
  have "p \<in> C" using hp_A1 hdecomp by (by100 blast)
  have hCp_conn: "top1_connected_on (C - {p}) (subspace_topology X TX (C - {p}))"
    by (rule scc_minus_point_connected[OF hT hH hC \<open>p \<in> C\<close>])
  \<comment> \<open>Get separation of A1-{p}.\<close>
  have hTA1p: "is_topology_on (A1 - {p}) (subspace_topology X TX (A1 - {p}))"
    by (rule subspace_topology_is_topology_on[OF is_topology_on_strict_imp[OF hT]])
       (use hA1_sub in blast)
  obtain U V where hUV: "U \<in> subspace_topology X TX (A1 - {p})"
      "V \<in> subspace_topology X TX (A1 - {p})" "U \<noteq> {}" "V \<noteq> {}"
      "U \<inter> V = {}" "U \<union> V = A1 - {p}"
    using hA1p_not_conn hTA1p unfolding top1_connected_on_def by auto
  \<comment> \<open>q \<in> A1-{p}. Pick W = part not containing q. W \<subseteq> A1-{p,q} \<subseteq> A1-A2.\<close>
  have hq_A1p: "q \<in> A1 - {p}" using hint hpq by (by100 blast)
  define W where "W = (if q \<in> U then V else U)"
  have hW_ne: "W \<noteq> {}" unfolding W_def using hUV(3,4) by (by100 simp)
  have hW_sub: "W \<subseteq> A1 - {p}" unfolding W_def using hUV(1,2,6)
    unfolding subspace_topology_def by auto
  have "q \<notin> W" unfolding W_def using hUV(5) hq_A1p hUV(6) by auto
  hence "W \<subseteq> A1 - {p, q}" using hW_sub by (by100 blast)
  hence hW_disj: "W \<inter> (A2 - {p}) = {}" using hint by (by100 blast)
  \<comment> \<open>A1 closed in X (compact arc in Hausdorff).\<close>
  have hA1_closed: "closedin_on X TX A1"
  proof (rule compact_in_strict_hausdorff_closedin_on[OF hH hT hA1_sub])
    obtain hh where hhh: "top1_homeomorphism_on I_set I_top A1 (subspace_topology X TX A1) hh"
      using hA1 unfolding top1_is_arc_on_def by (by100 blast)
    have hTA1: "is_topology_on A1 (subspace_topology X TX A1)"
      by (rule subspace_topology_is_topology_on[OF is_topology_on_strict_imp[OF hT] hA1_sub])
    have hIeq: "I_set = {0..1::real}" unfolding top1_unit_interval_def
      by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
    have "compact I_set" unfolding hIeq by (rule compact_Icc)
    hence "top1_compact_on I_set (subspace_topology UNIV top1_open_sets I_set)"
      using top1_compact_on_subspace_UNIV_iff_compact[of I_set] by (by100 simp)
    hence hI_compact: "top1_compact_on I_set I_top" unfolding top1_unit_interval_topology_def by (by100 simp)
    have hcont: "top1_continuous_map_on I_set I_top A1 (subspace_topology X TX A1) hh"
      using hhh unfolding top1_homeomorphism_on_def by (by100 blast)
    have himg: "hh ` I_set = A1"
      using hhh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    from Theorem_26_5[OF top1_unit_interval_topology_is_topology_on hTA1 hI_compact hcont]
    have "top1_compact_on (hh ` I_set) (subspace_topology A1 (subspace_topology X TX A1) (hh ` I_set))" .
    hence "top1_compact_on A1 (subspace_topology A1 (subspace_topology X TX A1) A1)" using himg by (by100 simp)
    moreover have "subspace_topology A1 (subspace_topology X TX A1) A1 = subspace_topology X TX A1"
      unfolding subspace_topology_def by (by100 blast)
    ultimately show "top1_compact_on A1 (subspace_topology X TX A1)" by (by100 simp)
  qed
  \<comment> \<open>W closed in C-{p}: W = (A1-{p}) \<inter> (X-G) = (C-{p}) \<inter> (A1 \<inter> (X-G)), closed via intersection.\<close>
  have hW_closed: "closedin_on (C - {p}) (subspace_topology X TX (C - {p})) W"
  proof -
    define W' where "W' = (if q \<in> U then U else V)"
    have "W' \<in> subspace_topology X TX (A1 - {p})" unfolding W'_def using hUV(1,2) by (by100 simp)
    then obtain G where hG: "G \<in> TX" "W' = (A1 - {p}) \<inter> G" unfolding subspace_topology_def by (by100 blast)
    have "W = (A1 - {p}) - W'" unfolding W_def W'_def using hUV(5,6) by auto
    hence hWeq: "W = (A1 - {p}) \<inter> (X - G)" using hG(2) hA1_sub by auto
    let ?F = "A1 \<inter> (X - G)"
    have hTX: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
    have hG_sub: "G \<subseteq> X" using hG(1) hT unfolding is_topology_on_strict_def is_topology_on_def by (by100 blast)
    have "X - (A1 \<inter> (X - G)) = (X - A1) \<union> G" using hG_sub by (by100 blast)
    have "(X - A1) \<in> TX" using hA1_closed unfolding closedin_on_def by (by100 blast)
    have "{X - A1, G} \<subseteq> TX" using \<open>(X - A1) \<in> TX\<close> hG(1) by (by100 blast)
    hence "\<Union>{X - A1, G} \<in> TX" using hTX unfolding is_topology_on_def by (by100 blast)
    hence "(X - ?F) \<in> TX" using \<open>X - (A1 \<inter> (X - G)) = (X - A1) \<union> G\<close> by (by100 simp)
    hence "(C - {p}) \<inter> (X - ?F) \<in> subspace_topology X TX (C - {p})"
      unfolding subspace_topology_def by (by100 blast)
    have hCp_sub: "C - {p} \<subseteq> X" using hC_sub by (by100 blast)
    have "W = (C - {p}) \<inter> ?F" using hWeq hW_sub hdecomp by (by100 blast)
    have "(C - {p}) - W = (C - {p}) \<inter> (X - ?F)"
    proof -
      have "(C - {p}) - W = (C - {p}) - ((C - {p}) \<inter> ?F)" using \<open>W = (C - {p}) \<inter> ?F\<close> by (by100 simp)
      also have "\<dots> = (C - {p}) \<inter> (- ?F)" by (by100 blast)
      also have "\<dots> = (C - {p}) \<inter> (X - ?F)" using hCp_sub by (by100 blast)
      finally show ?thesis .
    qed
    hence "(C - {p}) - W \<in> subspace_topology X TX (C - {p})"
      using \<open>(C - {p}) \<inter> (X - ?F) \<in> subspace_topology X TX (C - {p})\<close> by (by100 simp)
    thus ?thesis unfolding closedin_on_def using \<open>W = (C - {p}) \<inter> ?F\<close> by (by100 blast)
  qed
  \<comment> \<open>C-{p}-W closed: W' closed (same pattern) + A2-{p} closed + union.\<close>
  have hCpW_closed: "closedin_on (C - {p}) (subspace_topology X TX (C - {p})) (C - {p} - W)"
  proof -
    let ?TCp = "subspace_topology X TX (C - {p})"
    have hTCp: "is_topology_on (C - {p}) ?TCp"
      by (rule subspace_topology_is_topology_on[OF is_topology_on_strict_imp[OF hT]]) (use hC_sub in blast)
    \<comment> \<open>A1-{p}-W closed in C-{p} (same proof as W, with roles of open sets swapped).\<close>
    have "closedin_on (C - {p}) ?TCp (A1 - {p} - W)"
    proof -
      have hW_open_A1: "W \<in> subspace_topology X TX (A1 - {p})" unfolding W_def using hUV(1,2) by (by100 simp)
      then obtain H where hH: "H \<in> TX" "W = (A1 - {p}) \<inter> H" unfolding subspace_topology_def by (by100 blast)
      have "A1 - {p} - W = (A1 - {p}) \<inter> (X - H)" using hH(2) hA1_sub by auto
      hence "A1 - {p} - W = (C - {p}) \<inter> (A1 \<inter> (X - H))" using hW_sub hdecomp by (by100 blast)
      have hTX: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
      have hH_sub: "H \<subseteq> X" using hH(1) hT unfolding is_topology_on_strict_def is_topology_on_def by (by100 blast)
      have "X - (A1 \<inter> (X - H)) = (X - A1) \<union> H" using hH_sub by (by100 blast)
      have "(X - A1) \<in> TX" using hA1_closed unfolding closedin_on_def by (by100 blast)
      have "{X - A1, H} \<subseteq> TX" using \<open>(X - A1) \<in> TX\<close> hH(1) by (by100 blast)
      hence "\<Union>{X - A1, H} \<in> TX" using hTX unfolding is_topology_on_def by (by100 blast)
      hence "(X - (A1 \<inter> (X - H))) \<in> TX" using \<open>X - (A1 \<inter> (X - H)) = (X - A1) \<union> H\<close> by (by100 simp)
      hence "(C - {p}) \<inter> (X - (A1 \<inter> (X - H))) \<in> ?TCp" unfolding subspace_topology_def by (by100 blast)
      have hCp_sub: "C - {p} \<subseteq> X" using hC_sub by (by100 blast)
      have "(C - {p}) - (A1 - {p} - W) = (C - {p}) \<inter> (X - (A1 \<inter> (X - H)))"
        using \<open>A1 - {p} - W = (C - {p}) \<inter> (A1 \<inter> (X - H))\<close> hCp_sub by (by100 blast)
      hence "(C - {p}) - (A1 - {p} - W) \<in> ?TCp"
        using \<open>(C - {p}) \<inter> (X - (A1 \<inter> (X - H))) \<in> ?TCp\<close> by (by100 simp)
      moreover have "A1 - {p} - W \<subseteq> C - {p}" using hdecomp by (by100 blast)
      ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
    qed
    \<comment> \<open>A2 closed, A2-{p} closed in C-{p}.\<close>
    have hA2_closed: "closedin_on X TX A2"
    proof (rule compact_in_strict_hausdorff_closedin_on[OF hH hT hA2_sub])
      obtain hh2 where hhh2: "top1_homeomorphism_on I_set I_top A2 (subspace_topology X TX A2) hh2"
        using hA2 unfolding top1_is_arc_on_def by (by100 blast)
      have hTA2: "is_topology_on A2 (subspace_topology X TX A2)"
        by (rule subspace_topology_is_topology_on[OF is_topology_on_strict_imp[OF hT] hA2_sub])
      have hIeq: "I_set = {0..1::real}" unfolding top1_unit_interval_def
        by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
      have "compact I_set" unfolding hIeq by (rule compact_Icc)
      hence hI_compact: "top1_compact_on I_set I_top"
        unfolding top1_unit_interval_topology_def
        using top1_compact_on_subspace_UNIV_iff_compact[of I_set] by (by100 simp)
      have hcont2: "top1_continuous_map_on I_set I_top A2 (subspace_topology X TX A2) hh2"
        using hhh2 unfolding top1_homeomorphism_on_def by (by100 blast)
      have himg2: "hh2 ` I_set = A2"
        using hhh2 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      from Theorem_26_5[OF top1_unit_interval_topology_is_topology_on hTA2 hI_compact hcont2]
      have "top1_compact_on (hh2 ` I_set) (subspace_topology A2 (subspace_topology X TX A2) (hh2 ` I_set))" .
      hence "top1_compact_on A2 (subspace_topology A2 (subspace_topology X TX A2) A2)" using himg2 by (by100 simp)
      moreover have "subspace_topology A2 (subspace_topology X TX A2) A2 = subspace_topology X TX A2"
        unfolding subspace_topology_def by (by100 blast)
      ultimately show "top1_compact_on A2 (subspace_topology X TX A2)" by (by100 simp)
    qed
    have "closedin_on (C - {p}) ?TCp (A2 - {p})"
      unfolding closedin_on_def
    proof (intro conjI)
      show "A2 - {p} \<subseteq> C - {p}" using hdecomp by (by100 blast)
      have "(X - A2) \<in> TX" using hA2_closed unfolding closedin_on_def by (by100 blast)
      hence "(C - {p}) \<inter> (X - A2) \<in> ?TCp" unfolding subspace_topology_def by (by100 blast)
      moreover have "(C - {p}) - (A2 - {p}) = (C - {p}) \<inter> (X - A2)"
        using hdecomp hA2_sub hA1_sub by (by100 blast)
      ultimately show "(C - {p}) - (A2 - {p}) \<in> ?TCp" by (by100 simp)
    qed
    \<comment> \<open>C-{p}-W = (A1-{p}-W) \<union> (A2-{p}). Both closed. Union closed.\<close>
    have "C - {p} - W = (A1 - {p} - W) \<union> (A2 - {p})"
      using hdecomp hW_sub hW_disj by (by100 blast)
    have "\<forall>A \<in> {A1 - {p} - W, A2 - {p}}. closedin_on (C - {p}) ?TCp A"
      using \<open>closedin_on (C - {p}) ?TCp (A1 - {p} - W)\<close> \<open>closedin_on (C - {p}) ?TCp (A2 - {p})\<close>
      by (by100 blast)
    from closedin_Union_finite[OF hTCp _ this]
    have "closedin_on (C - {p}) ?TCp ((A1 - {p} - W) \<union> (A2 - {p}))" by (by100 simp)
    thus ?thesis using \<open>C - {p} - W = (A1 - {p} - W) \<union> (A2 - {p})\<close> by (by100 simp)
  qed
  \<comment> \<open>C-{p}-W \<noteq> {} (q \<in> A2-{p}, q \<notin> W).\<close>
  have "C - {p} - W \<noteq> {}"
  proof -
    have "q \<in> A2 - {p}" using hint hpq by (by100 blast)
    hence "q \<notin> W" using hW_disj by (by100 blast)
    moreover have "q \<in> C - {p}" using \<open>q \<in> A2 - {p}\<close> hdecomp by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>W and C-{p}-W form separation \<Rightarrow> C-{p} not connected.\<close>
  have hW_sub_Cp: "W \<subseteq> C - {p}" using hW_sub hdecomp by (by100 blast)
  have hW_open: "W \<in> subspace_topology X TX (C - {p})"
  proof -
    from hCpW_closed have "(C - {p}) - (C - {p} - W) \<in> subspace_topology X TX (C - {p})"
      unfolding closedin_on_def by (by100 blast)
    moreover have "(C - {p}) - (C - {p} - W) = W" using hW_sub_Cp by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  have hCpW_open: "(C - {p} - W) \<in> subspace_topology X TX (C - {p})"
    using hW_closed unfolding closedin_on_def by (by100 blast)
  have "\<not> top1_connected_on (C - {p}) (subspace_topology X TX (C - {p}))"
    unfolding top1_connected_on_def
    using hW_open hCpW_open hW_ne \<open>C - {p} - W \<noteq> {}\<close>
    by auto (use hW_sub_Cp in blast)
  thus False using hCp_conn by (by100 blast)
qed

lemma scc_decomp_arc_endpoints:
  assumes hT: "is_topology_on_strict X TX" and hH: "is_hausdorff_on X TX"
  and hC: "top1_simple_closed_curve_on X TX C"
  and hA1: "top1_is_arc_on A1 (subspace_topology X TX A1)"
  and hA2: "top1_is_arc_on A2 (subspace_topology X TX A2)"
  and hA1_sub: "A1 \<subseteq> X" and hA2_sub: "A2 \<subseteq> X"
  and hdecomp: "C = A1 \<union> A2" and hint: "A1 \<inter> A2 = {a, b}" and hab: "a \<noteq> b"
  shows "top1_arc_endpoints_on A1 (subspace_topology X TX A1) = {a, b}"
    and "top1_arc_endpoints_on A2 (subspace_topology X TX A2) = {a, b}"
proof -
  \<comment> \<open>For an arc A with A \<inter> A' = {a,b}, A \<union> A' = SCC:
     The arc interior A - {a,b} is connected (homeomorphic to (0,1)).
     A - {a} is connected (homeomorphic to [0,1)).
     A - {b} is connected.
     But A - {p} for p \<in> A - {a,b} is disconnected (p splits the arc).
     So the arc endpoints (points whose removal leaves A connected) are exactly {a,b}.\<close>
  \<comment> \<open>endpoints(A1) \<subseteq> {a,b}: removing any p \<notin> {a,b} from A1 disconnects it.\<close>
  \<comment> \<open>endpoints(A1) \<supseteq> {a,b}: removing a (or b) from A1 leaves it connected
     because a,b are at the "boundary" of A1 within the SCC.\<close>
  \<comment> \<open>Proof: if a were interior to A1, A1-{a} has 2 components P,Q.
     b is in one (say P). Q \<subseteq> A1 - {a,b} \<subseteq> A1 - A2, so Q \<inter> A2 = {}.
     Then C-{a} = P \<union> Q \<union> (A2-{a}) with Q disjoint from the rest, contradicting
     C-{a} connected (SCC minus point).\<close>
  obtain h1 where hh1: "top1_homeomorphism_on I_set I_top A1 (subspace_topology X TX A1) h1"
    using hA1 unfolding top1_is_arc_on_def by (by100 blast)
  define e1 where "e1 = h1 0"
  define e2 where "e2 = h1 1"
  have heps_eq: "top1_arc_endpoints_on A1 (subspace_topology X TX A1) = {e1, e2}"
    unfolding e1_def e2_def
    by (rule arc_endpoints_are_boundary[OF hT hH hA1_sub hA1 hh1])
  have heps_ne: "e1 \<noteq> e2"
  proof -
    have "h1 ` I_set = A1"
      using hh1 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have h_inj: "inj_on h1 I_set"
      using hh1 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have "(0::real) \<noteq> 1" by (by100 simp)
    thus ?thesis unfolding e1_def e2_def using h_inj h0I h1I
      unfolding inj_on_def by (by100 blast)
  qed
  have he1_A1: "e1 \<in> A1" and he2_A1: "e2 \<in> A1"
  proof -
    have "h1 ` I_set = A1"
      using hh1 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    thus "e1 \<in> A1" unfolding e1_def using \<open>h1 ` I_set = A1\<close> by (by100 blast)
    have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    thus "e2 \<in> A1" unfolding e2_def using \<open>h1 ` I_set = A1\<close> by (by100 blast)
  qed
  have heps: "top1_arc_endpoints_on A1 (subspace_topology X TX A1) = {e1, e2}"
      "e1 \<noteq> e2" "e1 \<in> A1" "e2 \<in> A1"
    using heps_eq heps_ne he1_A1 he2_A1 by auto
  have ha_ep: "a \<in> {e1, e2}"
  proof (rule ccontr)
    assume ha_int: "a \<notin> {e1, e2}"
    have "a \<notin> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
      using ha_int heps(1) by (by100 simp)
    have "a \<in> A1" using hint by (by100 blast)
    show False by (rule scc_interior_contradiction[OF hT hH hC hA1 hA2 hA1_sub hA2_sub hdecomp hint hab
        \<open>a \<in> A1\<close> \<open>a \<notin> top1_arc_endpoints_on A1 (subspace_topology X TX A1)\<close>])
  qed
  have hb_ep: "b \<in> {e1, e2}"
  proof (rule ccontr)
    assume hb_int: "b \<notin> {e1, e2}"
    have "b \<in> A1" using hint by (by100 blast)
    have "\<not> top1_connected_on (A1 - {b}) (subspace_topology A1 (subspace_topology X TX A1) (A1 - {b}))"
    proof -
      have "b \<notin> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
        using hb_int heps(1) by (by100 simp)
      hence "b \<notin> {p \<in> A1. top1_connected_on (A1 - {p}) (subspace_topology A1 (subspace_topology X TX A1) (A1 - {p}))}"
        unfolding top1_arc_endpoints_on_def by (by100 simp)
      thus ?thesis using \<open>b \<in> A1\<close> by (by100 blast)
    qed
    have hC_sub: "C \<subseteq> X" using hdecomp hA1_sub hA2_sub by (by100 blast)
    have "b \<in> C" using hint hdecomp by (by100 blast)
    have hCb_conn: "top1_connected_on (C - {b}) (subspace_topology X TX (C - {b}))"
      by (rule scc_minus_point_connected[OF hT hH hC \<open>b \<in> C\<close>])
    \<comment> \<open>Same contradiction as 'a' case with a\<leftrightarrow>b swapped.\<close>
    have hA1b_not_conn_X: "\<not> top1_connected_on (A1 - {b}) (subspace_topology X TX (A1 - {b}))"
    proof -
      have "subspace_topology A1 (subspace_topology X TX A1) (A1 - {b})
          = subspace_topology X TX (A1 - {b})"
        by (rule subspace_topology_trans[OF Diff_subset])
      thus ?thesis using \<open>\<not> top1_connected_on (A1 - {b}) (subspace_topology A1 (subspace_topology X TX A1) (A1 - {b}))\<close>
        by (by100 simp)
    qed
    have hTA1b: "is_topology_on (A1 - {b}) (subspace_topology X TX (A1 - {b}))"
      by (rule subspace_topology_is_topology_on[OF is_topology_on_strict_imp[OF hT]])
         (use hA1_sub in blast)
    then obtain Ub Vb where hUVb: "Ub \<in> subspace_topology X TX (A1 - {b})"
        "Vb \<in> subspace_topology X TX (A1 - {b})" "Ub \<noteq> {}" "Vb \<noteq> {}"
        "Ub \<inter> Vb = {}" "Ub \<union> Vb = A1 - {b}"
      using hA1b_not_conn_X unfolding top1_connected_on_def by auto
    have ha_A1b: "a \<in> A1 - {b}" using hint hab by (by100 blast)
    define Wb where "Wb = (if a \<in> Ub then Vb else Ub)"
    have "Wb \<noteq> {}" unfolding Wb_def using hUVb(3,4) by (by100 simp)
    have "Wb \<subseteq> A1 - {b}" unfolding Wb_def using hUVb(1,2,6) unfolding subspace_topology_def by auto
    have "a \<notin> Wb" unfolding Wb_def using hUVb(5) ha_A1b hUVb(6) by auto
    hence "Wb \<subseteq> A1 - {a, b}" using \<open>Wb \<subseteq> A1 - {b}\<close> by (by100 blast)
    hence "Wb \<inter> (A2 - {b}) = {}" using hint by (by100 blast)
    \<comment> \<open>Wb closed in C-{b}: same argument as W in 'a' case.\<close>
    \<comment> \<open>C-{b}-Wb closed. Both non-empty. Separation. C-{b} not connected. \<bottom>.\<close>
    have "b \<notin> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
      using hb_int heps(1) by (by100 simp)
    have hint_ba: "A1 \<inter> A2 = {b, a}" using hint by (by100 blast)
    show False by (rule scc_interior_contradiction[OF hT hH hC hA1 hA2 hA1_sub hA2_sub hdecomp
        hint_ba _ \<open>b \<in> A1\<close> \<open>b \<notin> top1_arc_endpoints_on A1 (subspace_topology X TX A1)\<close>])
        (use hab in blast)
  qed
  from ha_ep hb_ep hab heps(2) show "top1_arc_endpoints_on A1 (subspace_topology X TX A1) = {a, b}"
    using heps(1) by (by100 blast)
  \<comment> \<open>A2: same argument with A1 and A2 swapped.\<close>
  show "top1_arc_endpoints_on A2 (subspace_topology X TX A2) = {a, b}"
  proof -
    \<comment> \<open>For each p \<in> {a,b}: if p \<notin> endpoints(A2), use scc\_interior\_contradiction with A2,A1 swapped.\<close>
    obtain f1 f2 where hf: "top1_arc_endpoints_on A2 (subspace_topology X TX A2) = {f1, f2}"
        "f1 \<noteq> f2" "f1 \<in> A2" "f2 \<in> A2"
    proof -
      obtain h2 where hh2: "top1_homeomorphism_on I_set I_top A2 (subspace_topology X TX A2) h2"
        using hA2 unfolding top1_is_arc_on_def by (by100 blast)
      have hh2_bij: "h2 ` I_set = A2"
        using hh2 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have hh2_inj: "inj_on h2 I_set"
        using hh2 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have heps2_eq: "top1_arc_endpoints_on A2 (subspace_topology X TX A2) = {h2 0, h2 1}"
        by (rule arc_endpoints_are_boundary[OF hT hH hA2_sub hA2 hh2])
      have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      have "h2 0 \<noteq> h2 1"
      proof
        assume "h2 0 = h2 1"
        hence "(0::real) = 1" using hh2_inj \<open>(0::real) \<in> I_set\<close> \<open>(1::real) \<in> I_set\<close>
          unfolding inj_on_def by (by100 blast)
        thus False by (by100 simp)
      qed
      show ?thesis using that[of "h2 0" "h2 1"] heps2_eq \<open>h2 0 \<noteq> h2 1\<close> hh2_bij
        \<open>(0::real) \<in> I_set\<close> \<open>(1::real) \<in> I_set\<close> by (by100 blast)
    qed
    have "a \<in> {f1, f2}"
    proof (rule ccontr)
      assume "a \<notin> {f1, f2}"
      hence "a \<notin> top1_arc_endpoints_on A2 (subspace_topology X TX A2)" using hf(1) by (by100 simp)
      have "a \<in> A2" using hint by (by100 blast)
      have "C = A2 \<union> A1" using hdecomp by (by100 blast)
      have "A2 \<inter> A1 = {a, b}" using hint by (by100 blast)
      show False by (rule scc_interior_contradiction[OF hT hH hC hA2 hA1 hA2_sub hA1_sub
          \<open>C = A2 \<union> A1\<close> \<open>A2 \<inter> A1 = {a, b}\<close> hab \<open>a \<in> A2\<close>
          \<open>a \<notin> top1_arc_endpoints_on A2 (subspace_topology X TX A2)\<close>])
    qed
    have "b \<in> {f1, f2}"
    proof (rule ccontr)
      assume "b \<notin> {f1, f2}"
      hence "b \<notin> top1_arc_endpoints_on A2 (subspace_topology X TX A2)" using hf(1) by (by100 simp)
      have "b \<in> A2" using hint by (by100 blast)
      have "C = A2 \<union> A1" using hdecomp by (by100 blast)
      have hint_ba': "A2 \<inter> A1 = {b, a}" using hint by (by100 blast)
      show False by (rule scc_interior_contradiction[OF hT hH hC hA2 hA1 hA2_sub hA1_sub
          \<open>C = A2 \<union> A1\<close> hint_ba' _ \<open>b \<in> A2\<close>
          \<open>b \<notin> top1_arc_endpoints_on A2 (subspace_topology X TX A2)\<close>])
          (use hab in blast)
    qed
    from \<open>a \<in> {f1, f2}\<close> \<open>b \<in> {f1, f2}\<close> hab hf(2) show ?thesis
      using hf(1) by (by100 blast)
  qed
qed

\<comment> \<open>Helper: homeomorphism inverse maps connected set to connected set (bridges HOL connected and top1\_).\<close>
lemma homeomorphism_inv_connected_bridge:
  fixes Y :: "(real \<times> real) set" and W :: "(real \<times> real) set"
  assumes hg: "top1_homeomorphism_on I_set I_top Y TY g"
  and hTY: "TY = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) Y"
  and hW_conn: "connected (W - {w})"
  and hW_sub: "W \<subseteq> Y"
  and hw_W: "w \<in> W"
  and ht0: "t0 \<in> I_set" "g t0 = w"
  and hS_eq: "S = {t \<in> I_set. g t \<in> W}"
  shows "connected (S - {t0})"
proof -
  have hg_bij: "bij_betw g I_set Y" using hg unfolding top1_homeomorphism_on_def by (by100 blast)
  have hg_inj: "inj_on g I_set" using hg_bij unfolding bij_betw_def by (by100 blast)
  have hg_img: "g ` I_set = Y" using hg_bij unfolding bij_betw_def by (by100 blast)
  \<comment> \<open>Step 1: HOL connected \<rightarrow> top1\_connected (for R2 subspace).\<close>
  have hWw_top1: "top1_connected_on (W - {w}) (subspace_topology (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets) (W - {w}))"
  proof -
    have "top1_connected_on (W - {w}) (subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets (W - {w}))"
      using hW_conn top1_connected_on_subspace_open_iff_connected by (by100 blast)
    moreover have "(product_topology_on top1_open_sets top1_open_sets :: (real \<times> real) set set) = top1_open_sets"
      using product_topology_on_open_sets by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Step 2: Subspace of subspace = subspace of ambient.\<close>
  have hWw_sub_Y: "W - {w} \<subseteq> Y" using hW_sub by (by100 blast)
  have hTY_eq: "TY = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) Y"
    using hTY by (by100 simp)
  have hWw_top1_Y: "top1_connected_on (W - {w})
      (subspace_topology Y TY (W - {w}))"
  proof -
    have "subspace_topology Y TY (W - {w})
        = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (W - {w})"
      using subspace_topology_trans[of "W - {w}" Y] hWw_sub_Y hTY_eq by (by100 simp)
    thus ?thesis using hWw_top1 by (by100 simp)
  qed
  \<comment> \<open>Step 3: inv\_into continuous (restriction to W-{w}).\<close>
  have hg_inv: "top1_continuous_map_on Y TY I_set I_top (inv_into I_set g)"
    using hg unfolding top1_homeomorphism_on_def by (by100 blast)
  have hY_top: "is_topology_on Y TY"
    using hg unfolding top1_homeomorphism_on_def by (by100 blast)
  have hI_top: "is_topology_on I_set I_top"
    using hg unfolding top1_homeomorphism_on_def by (by100 blast)
  have hinv_on_Ww: "top1_continuous_map_on (W - {w})
      (subspace_topology Y TY (W - {w})) I_set I_top (inv_into I_set g)"
  proof -
    show ?thesis by (rule top1_continuous_map_on_restrict_domain_simple[OF hg_inv hWw_sub_Y])
  qed
  \<comment> \<open>Step 4: inv\_into maps W-{w} to S-{t0}.\<close>
  have hinv_img: "inv_into I_set g ` (W - {w}) = S - {t0}"
  proof (intro set_eqI iffI)
    fix t assume "t \<in> inv_into I_set g ` (W - {w})"
    then obtain y where hy: "y \<in> W - {w}" "t = inv_into I_set g y" by (by100 blast)
    have "y \<in> g ` I_set" using hy(1) hWw_sub_Y hg_img by (by100 blast)
    hence ht_I: "t \<in> I_set" using hy(2) by (metis inv_into_into)
    have hgt: "g t = y" using hy(2) f_inv_into_f[OF \<open>y \<in> g ` I_set\<close>] by (by100 simp)
    hence "g t \<in> W" using hy(1) by (by100 blast)
    hence "t \<in> S" unfolding hS_eq using ht_I by (by100 blast)
    moreover have "t \<noteq> t0" using hgt hy(1) ht0(2) by auto
    ultimately show "t \<in> S - {t0}" by (by100 blast)
  next
    fix t assume "t \<in> S - {t0}"
    hence ht: "t \<in> I_set" "g t \<in> W" "t \<noteq> t0" unfolding hS_eq by auto
    have "g t \<noteq> w" using ht(1,3) ht0 inj_onD[OF hg_inj] by (by100 metis)
    hence "g t \<in> W - {w}" using ht(2) by (by100 blast)
    moreover have "inv_into I_set g (g t) = t"
      using inv_into_f_f[OF hg_inj ht(1)] by (by100 simp)
    ultimately show "t \<in> inv_into I_set g ` (W - {w})" by (by100 force)
  qed
  \<comment> \<open>Step 5: Theorem\_23\_5: connected image under continuous.\<close>
  have hI_top: "is_topology_on I_set I_top"
    using hg unfolding top1_homeomorphism_on_def by (by100 blast)
  have hWw_top: "is_topology_on (W - {w}) (subspace_topology Y TY (W - {w}))"
    by (rule subspace_topology_is_topology_on[OF hY_top hWw_sub_Y])
  have "top1_connected_on (inv_into I_set g ` (W - {w}))
      (subspace_topology I_set I_top (inv_into I_set g ` (W - {w})))"
    by (rule Theorem_23_5[OF hWw_top hI_top hWw_top1_Y hinv_on_Ww])
  have "top1_connected_on (S - {t0}) (subspace_topology I_set I_top (S - {t0}))"
    using \<open>top1_connected_on (inv_into I_set g ` (W - {w})) _\<close> hinv_img by (by100 simp)
  \<comment> \<open>Step 6: Bridge back top1\_connected \<rightarrow> HOL connected.\<close>
  hence "top1_connected_on (S - {t0}) (subspace_topology UNIV top1_open_sets (S - {t0}))"
  proof -
    have "subspace_topology I_set I_top (S - {t0}) = subspace_topology UNIV top1_open_sets (S - {t0})"
    proof -
      have "S - {t0} \<subseteq> I_set" unfolding hS_eq by (by100 blast)
      thus ?thesis using subspace_topology_trans[of "S - {t0}" I_set]
        unfolding top1_unit_interval_topology_def by (by100 simp)
    qed
    thus ?thesis using \<open>top1_connected_on (S - {t0}) (subspace_topology I_set I_top (S - {t0}))\<close>
      by (by100 simp)
  qed
  thus ?thesis using top1_connected_on_subspace_open_iff_connected by (by100 blast)
qed

\<comment> \<open>An arc endpoint in S2 is NOT an interior point of the arc.
   Hence any open neighborhood of p in S2 contains points outside Fp.
   Proof: via stereographic projection to R2, use connected\_open\_delete\_R2.\<close>
lemma arc_endpoint_not_interior_S2:
  assumes hS2: "is_topology_on_strict top1_S2 top1_S2_topology"
  and hFp: "top1_is_arc_on Fp (subspace_topology top1_S2 top1_S2_topology Fp)"
  and hFp_sub: "Fp \<subseteq> top1_S2"
  and hFp_ep: "top1_arc_endpoints_on Fp (subspace_topology top1_S2 top1_S2_topology Fp) = {p, d}"
  and hpd: "p \<noteq> d"
  and hV: "V \<in> top1_S2_topology" and hp_V: "p \<in> V"
  shows "\<exists>x \<in> V. x \<notin> Fp \<and> x \<in> top1_S2"
proof (rule ccontr)
  assume hneg: "\<not> ?thesis"
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using hS2 unfolding is_topology_on_strict_def by (by100 blast)
  have hV_sub_S2: "V \<subseteq> top1_S2"
    using hV hS2 unfolding is_topology_on_strict_def openin_on_def by (by100 blast)
  have hV_sub_Fp': "V \<subseteq> Fp"
  proof (rule subsetI)
    fix x assume "x \<in> V"
    hence "x \<in> top1_S2" using hV_sub_S2 by (by100 blast)
    with hneg \<open>x \<in> V\<close> show "x \<in> Fp" by (by100 blast)
  qed
  have hp_S2: "p \<in> top1_S2" using hFp_sub hFp_ep
    unfolding top1_arc_endpoints_on_def by (by100 blast)
  \<comment> \<open>Pick z \<in> S2 - Fp (Fp \<subsetneq> S2). Use z as stereographic pole.\<close>
  have hFp_ne_S2: "Fp \<noteq> top1_S2"
  proof
    assume hFpS2: "Fp = top1_S2"
    \<comment> \<open>Pick interior point x of Fp (not an endpoint). Removing x disconnects Fp but not S2.\<close>
    obtain hf where hhf: "top1_homeomorphism_on I_set I_top Fp
        (subspace_topology top1_S2 top1_S2_topology Fp) hf"
      using hFp unfolding top1_is_arc_on_def by (by100 blast)
    define x where "x = hf (1/2 :: real)"
    have hx_Fp: "x \<in> Fp"
    proof -
      have "(1/2::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      thus ?thesis unfolding x_def using hhf unfolding top1_homeomorphism_on_def
        top1_continuous_map_on_def by (by100 blast)
    qed
    have hx_S2: "x \<in> top1_S2" using hx_Fp hFp_sub by (by100 blast)
    have hx_not_ep: "x \<notin> top1_arc_endpoints_on Fp (subspace_topology top1_S2 top1_S2_topology Fp)"
    proof -
      have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology" by (rule top1_S2_is_hausdorff)
      have "top1_arc_endpoints_on Fp (subspace_topology top1_S2 top1_S2_topology Fp) = {hf 0, hf 1}"
        by (rule arc_endpoints_are_boundary[OF hS2 hS2_haus hFp_sub hFp hhf])
      moreover have "x \<noteq> hf 0" "x \<noteq> hf 1"
      proof -
        have hinj: "inj_on hf I_set" using hhf unfolding top1_homeomorphism_on_def bij_betw_def
          by (by100 blast)
        have h0: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        have h1: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        have h12: "(1/2::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        show "x \<noteq> hf 0" unfolding x_def
        proof
          assume "hf (1/2) = hf 0"
          hence "(1/2::real) = 0" by (metis inj_onD[OF hinj] h12 h0)
          thus False by (by100 simp)
        qed
        show "x \<noteq> hf 1" unfolding x_def
        proof
          assume "hf (1/2) = hf 1"
          hence "(1/2::real) = 1" by (metis inj_onD[OF hinj] h12 h1)
          thus False by (by100 simp)
        qed
      qed
      ultimately show ?thesis by (by100 blast)
    qed
    hence hx_ne_pd: "x \<notin> {p, d}" using hFp_ep by (by100 simp)
    \<comment> \<open>Removing non-endpoint disconnects arc (definition of endpoints).\<close>
    have "\<not> top1_connected_on (Fp - {x}) (subspace_topology Fp
        (subspace_topology top1_S2 top1_S2_topology Fp) (Fp - {x}))"
      using hx_not_ep hx_Fp unfolding top1_arc_endpoints_on_def by (by100 blast)
    \<comment> \<open>But S2-{x} is connected (simply connected implies connected).\<close>
    moreover have "top1_connected_on (top1_S2 - {x}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {x}))"
    proof -
      have "top1_simply_connected_on (top1_S2 - {x}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {x}))"
        by (rule S2_minus_point_simply_connected[OF hx_S2])
      hence "top1_path_connected_on (top1_S2 - {x}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {x}))"
        unfolding top1_simply_connected_on_def by (by100 blast)
      thus ?thesis by (rule top1_path_connected_imp_connected)
    qed
    moreover have "Fp - {x} = top1_S2 - {x}" using hFpS2 by (by100 simp)
    moreover have "subspace_topology Fp (subspace_topology top1_S2 top1_S2_topology Fp) (Fp - {x})
        = subspace_topology top1_S2 top1_S2_topology (top1_S2 - {x})"
    proof -
      have hss: "subspace_topology top1_S2 top1_S2_topology top1_S2 = top1_S2_topology"
      proof (rule set_eqI)
        fix U
        show "U \<in> subspace_topology top1_S2 top1_S2_topology top1_S2 \<longleftrightarrow> U \<in> top1_S2_topology"
        proof
          assume "U \<in> subspace_topology top1_S2 top1_S2_topology top1_S2"
          then obtain W where "W \<in> top1_S2_topology" "U = top1_S2 \<inter> W"
            unfolding subspace_topology_def by (by100 blast)
          moreover have "W \<subseteq> top1_S2" using \<open>W \<in> top1_S2_topology\<close> hS2
            unfolding is_topology_on_strict_def openin_on_def by (by100 blast)
          hence "U = W" using \<open>U = top1_S2 \<inter> W\<close> by (by100 blast)
          thus "U \<in> top1_S2_topology" using \<open>W \<in> top1_S2_topology\<close> by (by100 simp)
        next
          assume "U \<in> top1_S2_topology"
          moreover have "U \<subseteq> top1_S2" using \<open>U \<in> top1_S2_topology\<close> hS2
            unfolding is_topology_on_strict_def openin_on_def by (by100 blast)
          ultimately show "U \<in> subspace_topology top1_S2 top1_S2_topology top1_S2"
            unfolding subspace_topology_def by (by100 force)
        qed
      qed
      show ?thesis using hFpS2 hss
        by (simp add: subspace_topology_def)
    qed
    ultimately show False by (by100 metis)
  qed
  then obtain z where hz: "z \<in> top1_S2 - Fp" using hFp_sub by auto
  \<comment> \<open>Stereographic projection from z.\<close>
  obtain h where hh: "top1_homeomorphism_on (top1_S2 - {z})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {z}))
      (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) h"
    using S2_minus_point_homeo_R2[OF] hz by (by100 blast)
  \<comment> \<open>V, Fp \<subseteq> S2-{z} (since z \<notin> Fp \<supseteq> V).\<close>
  have hz_notin_V: "z \<notin> V" using hV_sub_Fp' hz by (by100 blast)
  have hV_sub_Sz: "V \<subseteq> top1_S2 - {z}" using hV_sub_S2 hz_notin_V by (by100 blast)
  have hFp_sub_Sz: "Fp \<subseteq> top1_S2 - {z}" using hFp_sub hz by (by100 blast)
  \<comment> \<open>h(V) is open in R2 (homeomorphism maps open to open via continuous inverse).\<close>
  have hV_in_sub: "V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {z})"
    unfolding subspace_topology_def using hV hV_sub_Sz by (by100 blast)
  have hinv_cont: "top1_continuous_map_on (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets)
      (top1_S2 - {z}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {z}))
      (inv_into (top1_S2 - {z}) h)"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hh_bij: "bij_betw h (top1_S2 - {z}) (UNIV :: (real \<times> real) set)"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hhV_open: "h ` V \<in> product_topology_on top1_open_sets top1_open_sets"
  proof -
    \<comment> \<open>h ` V = preimage of V under inv\_into (by bijectivity).\<close>
    have hpre: "h ` V = {y \<in> (UNIV :: (real \<times> real) set). inv_into (top1_S2 - {z}) h y \<in> V}"
    proof (intro set_eqI iffI)
      fix y assume "y \<in> h ` V"
      then obtain x where hx: "x \<in> V" "y = h x" by (by100 blast)
      have "x \<in> top1_S2 - {z}" using hx(1) hV_sub_Sz by (by100 blast)
      hence "inv_into (top1_S2 - {z}) h y = x"
        using hx(2) hh_bij unfolding bij_betw_def by (by100 force)
      thus "y \<in> {y \<in> UNIV. inv_into (top1_S2 - {z}) h y \<in> V}" using hx(1) by (by100 blast)
    next
      fix y assume "y \<in> {y \<in> UNIV. inv_into (top1_S2 - {z}) h y \<in> V}"
      hence hinv_V: "inv_into (top1_S2 - {z}) h y \<in> V" by (by100 blast)
      have hinv_Sz: "inv_into (top1_S2 - {z}) h y \<in> top1_S2 - {z}"
        using hinv_V hV_sub_Sz by (by100 blast)
      have "y \<in> h ` (top1_S2 - {z})" using hh_bij unfolding bij_betw_def by (by100 blast)
      hence "h (inv_into (top1_S2 - {z}) h y) = y" by (rule f_inv_into_f)
      thus "y \<in> h ` V" using hinv_V by (by100 force)
    qed
    \<comment> \<open>Preimage of open set under continuous map is open.\<close>
    show ?thesis unfolding hpre
      using hinv_cont hV_in_sub unfolding top1_continuous_map_on_def by (by100 blast)
  qed
  \<comment> \<open>h(V) is nonempty (p \<in> V).\<close>
  have hhV_ne: "h ` V \<noteq> {}" using hp_V by (by100 blast)
  \<comment> \<open>h(Fp) is an arc in R2, homeomorphic to [0,1].\<close>
  have hh_Fp: "top1_homeomorphism_on Fp (subspace_topology (top1_S2 - {z})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {z})) Fp)
      (h ` Fp) (subspace_topology (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets) (h ` Fp)) h"
    by (rule homeomorphism_on_restrict[OF hh hFp_sub_Sz])
  \<comment> \<open>Subspace of subspace = subspace of ambient.\<close>
  have hFp_sub_top: "subspace_topology (top1_S2 - {z})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {z})) Fp
      = subspace_topology top1_S2 top1_S2_topology Fp"
    using subspace_topology_trans[of Fp "top1_S2 - {z}"] hFp_sub_Sz by (by100 simp)
  obtain hf where hhf: "top1_homeomorphism_on I_set I_top Fp
      (subspace_topology top1_S2 top1_S2_topology Fp) hf"
    using hFp unfolding top1_is_arc_on_def by (by100 blast)
  have hhf': "top1_homeomorphism_on I_set I_top Fp
      (subspace_topology (top1_S2 - {z})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {z})) Fp) hf"
    using hhf hFp_sub_top by (by100 simp)
  \<comment> \<open>g = h \<circ> hf: homeomorphism [0,1] \<rightarrow> h(Fp). Make explicit to access g(0), g(1).\<close>
  define g where "g = h \<circ> hf"
  have hg: "top1_homeomorphism_on I_set I_top (h ` Fp)
      (subspace_topology (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) (h ` Fp)) g"
    unfolding g_def by (rule homeomorphism_compose[OF hhf' hh_Fp])
  have hg_bij: "bij_betw g I_set (h ` Fp)"
    using hg unfolding top1_homeomorphism_on_def by (by100 blast)
  have hg_inj: "inj_on g I_set" using hg_bij unfolding bij_betw_def by (by100 blast)
  have hg_img: "g ` I_set = h ` Fp" using hg_bij unfolding bij_betw_def by (by100 blast)
  \<comment> \<open>g(0) = h(hf(0)), g(1) = h(hf(1)). {hf(0), hf(1)} = {p, d}. So h(p) \<in> {g(0), g(1)}.\<close>
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology" by (rule top1_S2_is_hausdorff)
  have hhf_ep: "{hf 0, hf 1} = {p, d}"
    using arc_endpoints_are_boundary[OF hS2 hS2_haus hFp_sub hFp hhf] hFp_ep by (by100 simp)
  have hg0: "g 0 = h (hf 0)" unfolding g_def by (by100 simp)
  have hg1: "g 1 = h (hf 1)" unfolding g_def by (by100 simp)
  have hhp_in_g01: "h p \<in> {g 0, g 1}"
  proof -
    have "p \<in> {hf 0, hf 1}" using hhf_ep by (by100 blast)
    thus ?thesis unfolding hg0 hg1 by (by100 blast)
  qed
  \<comment> \<open>Inverse: since h(p) \<in> {g(0), g(1)} and g bijective, inv\_into gives 0 or 1.\<close>
  define t_p where "t_p = inv_into I_set g (h p)"
  have ht_p_01: "t_p \<in> {0, 1}"
  proof -
    have h0: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have h1: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    from hhp_in_g01 show ?thesis unfolding t_p_def
      using inv_into_f_f[OF hg_inj h0] inv_into_f_f[OF hg_inj h1] by (by100 force)
  qed
  \<comment> \<open>g\<inverse>(h(V)) open in [0,1], contains t\_p \<in> {0,1}, hence extends into (0,1).\<close>
  have hg_inv_cont: "top1_continuous_map_on (h ` Fp)
      (subspace_topology (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) (h ` Fp))
      I_set I_top (inv_into I_set g)"
    using hg unfolding top1_homeomorphism_on_def by (by100 blast)
  have hhV_in_sub: "h ` V \<in> subspace_topology (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) (h ` Fp)"
  proof -
    have "h ` V \<subseteq> h ` Fp" using hV_sub_Fp' by (by100 blast)
    thus ?thesis using hhV_open unfolding subspace_topology_def by (by100 blast)
  qed
  \<comment> \<open>g is continuous from I\_set to h(Fp). Preimage of open is open.\<close>
  have hg_cont: "top1_continuous_map_on I_set I_top (h ` Fp)
      (subspace_topology (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) (h ` Fp)) g"
    using hg unfolding top1_homeomorphism_on_def by (by100 blast)
  have hgV_open: "{t \<in> I_set. g t \<in> h ` V} \<in> I_top"
    using hg_cont hhV_in_sub unfolding top1_continuous_map_on_def by (by100 blast)
  have htp_in_gV: "t_p \<in> {t \<in> I_set. g t \<in> h ` V}"
  proof -
    have "t_p \<in> I_set" using ht_p_01 unfolding top1_unit_interval_def by (by100 force)
    moreover have "g t_p = h p"
    proof -
      have "h p \<in> h ` Fp" using hp_V hV_sub_Fp' by (by100 blast)
      hence "h p \<in> g ` I_set" using hg_img by (by100 simp)
      thus ?thesis unfolding t_p_def by (rule f_inv_into_f)
    qed
    moreover have "h p \<in> h ` V" using hp_V by (by100 blast)
    ultimately show ?thesis by (by100 force)
  qed
  \<comment> \<open>Pick t0 \<in> (0,1) with g(t0) \<in> h(V).\<close>
  obtain t0 where ht0: "t0 \<in> {0<..<1}" "g t0 \<in> h ` V"
  proof -
    \<comment> \<open>{t \<in> I\_set. g t \<in> h(V)} is open in I\_top and contains t\_p \<in> {0,1}.
       Open set in [0,1] containing 0 includes [0,\<epsilon>); containing 1 includes (1-\<epsilon>,1].
       Either way, it contains points in (0,1).\<close>
    have hgV_ne: "{t \<in> I_set. g t \<in> h ` V} \<noteq> {}" using htp_in_gV by (by100 blast)
    \<comment> \<open>U = {t \<in> I\_set. g t \<in> h(V)} is open in I\_top, contains t\_p \<in> {0,1}.\<close>
    let ?U = "{t \<in> I_set. g t \<in> h ` V}"
    \<comment> \<open>?U \<in> I\_top = subspace of R restricted to [0,1]. So ?U = I\_set \<inter> W for open W in R.\<close>
    obtain W where hW: "W \<in> top1_open_sets" "?U = I_set \<inter> W"
      using hgV_open unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
    have "t_p \<in> W" using htp_in_gV hW(2) by (by100 blast)
    \<comment> \<open>W is open in R, t\_p \<in> W. So \<exists>\<epsilon>>0 with open interval around t\_p \<subseteq> W.\<close>
    have "open W" using hW(1) unfolding top1_open_sets_def by (by100 blast)
    then obtain e where he: "e > 0" "\<forall>y. dist y t_p < e \<longrightarrow> y \<in> W"
      using \<open>t_p \<in> W\<close> unfolding open_dist by (by100 blast)
    \<comment> \<open>Pick t0 in (0,1) near t\_p. If t\_p=0: take t0 = min(e,1)/2. If t\_p=1: take t0 = 1-min(e,1)/2.\<close>
    define t0 where "t0 = (if t_p = 0 then min e 1 / 2 else 1 - min e 1 / 2)"
    have ht0_open: "t0 \<in> {0<..<1}"
    proof -
      have "e > 0" using he(1) .
      show ?thesis unfolding t0_def using ht_p_01 \<open>e > 0\<close> by auto
    qed
    moreover have "t0 \<in> W"
    proof -
      have "dist t0 t_p < e" unfolding t0_def dist_real_def using ht_p_01 he(1) by auto
      thus ?thesis using he(2) by (by100 blast)
    qed
    hence "t0 \<in> ?U"
    proof -
      have "t0 \<in> I_set" using ht0_open unfolding top1_unit_interval_def by (by100 force)
      thus ?thesis using hW(2) \<open>t0 \<in> W\<close> by (by100 blast)
    qed
    hence "g t0 \<in> h ` V" by (by100 blast)
    ultimately show ?thesis using that by (by100 blast)
  qed
  define w where "w = g t0"
  have hw_in_hV: "w \<in> h ` V" unfolding w_def using ht0(2) by (by100 blast)
  have ht0_01: "0 < t0" "t0 < 1" using ht0(1) by auto
  have ht0_I: "t0 \<in> I_set" unfolding top1_unit_interval_def using ht0_01 by (by100 simp)
  \<comment> \<open>h(V) is open in R2. Pick open ball B around w inside h(V).\<close>
  have hhV_HOL_open: "open (h ` V)"
    using hhV_open product_topology_on_open_sets unfolding top1_open_sets_def by (by100 blast)
  \<comment> \<open>h(V) is open in R2, contains w. By connected\_open\_delete\_R2 applied to connected
     component of h(V) containing w (or directly): some open connected W \<ni> w with W \<subseteq> h(V)
     and W - {w} connected.\<close>
  obtain W where hW: "W \<subseteq> h ` V" "w \<in> W" "open W" "connected W"
  proof -
    \<comment> \<open>h(V) open, w \<in> h(V). Get open rectangle around w inside h(V).\<close>
    obtain A0 B0 where hAB: "open A0" "open B0" "w \<in> A0 \<times> B0" "A0 \<times> B0 \<subseteq> h ` V"
      using open_prod_elim[OF hhV_HOL_open hw_in_hV] by (by100 blast)
    \<comment> \<open>Open rectangle in R2 is connected (product of connected sets).\<close>
    obtain a1 a2 where ha: "a1 \<in> A0" "a2 \<in> B0" "w = (a1, a2)"
      using hAB(3) by (by100 force)
    obtain e1 where he1: "e1 > 0" "\<forall>y. dist y a1 < e1 \<longrightarrow> y \<in> A0"
      using \<open>open A0\<close> \<open>a1 \<in> A0\<close> unfolding open_dist by (by100 force)
    obtain e2 where he2: "e2 > 0" "\<forall>y. dist y a2 < e2 \<longrightarrow> y \<in> B0"
      using \<open>open B0\<close> \<open>a2 \<in> B0\<close> unfolding open_dist by (by100 force)
    \<comment> \<open>Use the open interval product as the connected neighborhood.\<close>
    define W where "W = {a1 - e1 <..< a1 + e1} \<times> {a2 - e2 <..< a2 + e2}"
    have "W \<subseteq> A0 \<times> B0"
    proof (rule subsetI)
      fix p assume "p \<in> W"
      then obtain x y where "p = (x,y)" "x \<in> {a1-e1<..<a1+e1}" "y \<in> {a2-e2<..<a2+e2}"
        unfolding W_def by (by100 force)
      hence "dist x a1 < e1" "dist y a2 < e2" unfolding dist_real_def by auto
      hence "x \<in> A0" "y \<in> B0" using he1(2) he2(2) by auto
      thus "p \<in> A0 \<times> B0" using \<open>p = (x,y)\<close> by (by100 blast)
    qed
    hence "W \<subseteq> h ` V" using hAB(4) by (by100 blast)
    moreover have "w \<in> W" unfolding W_def ha(3) using he1(1) he2(1) by (by100 force)
    moreover have "open W" unfolding W_def by (rule open_Times; rule open_greaterThanLessThan)
    moreover have "connected W" unfolding W_def
      by (rule connected_Times; rule connected_Ioo)
    ultimately show ?thesis using that by (by100 blast)
  qed
  have hW_del: "connected (W - {w})" by (rule connected_open_delete_R2[OF hW(3,4)])
  \<comment> \<open>g\<inverse>(ball w r \<inter> h(Fp)) is open in [0,1], contains t0, hence contains (t0-\<delta>,t0+\<delta>).\<close>
  \<comment> \<open>g\<inverse>(ball w r \<inter> h(Fp)) - {t0} intersects both [0,t0) and (t0,1].\<close>
  \<comment> \<open>But g maps this set to (ball w r \<inter> h(Fp)) - {w} \<subseteq> (ball w r) - {w} which is connected.\<close>
  \<comment> \<open>If g maps disconnected [0,t0)\<union>(t0,\<delta>) to connected ball-{w}, then g identifies points
     from both halves, contradicting injectivity. More precisely:
     the image under g of the connected component of [0,t0) in g\<inverse>(ball) must be connected,
     but together with (t0,\<delta>) component they cover g\<inverse>(ball)-{t0}, and g maps the whole thing
     to connected ball-{w}. Since g is a homeomorphism, g\<inverse>(ball-{w}) = g\<inverse>(ball)-{t0} is connected.
     But g\<inverse>(ball) is open in [0,1] containing t0 \<in> (0,1), so g\<inverse>(ball)-{t0} intersects both
     [0,t0) and (t0,1], contradicting connectedness in [0,1]-{t0}.\<close>
  \<comment> \<open>S = {t \<in> [0,1]. g t \<in> W} is open in [0,1], contains t0 \<in> (0,1).\<close>
  have hW_sub_hFp: "W \<subseteq> h ` Fp" using hW(1) hV_sub_Fp' by (by100 blast)
  have hW_in_sub: "W \<in> subspace_topology (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets) (h ` Fp)"
    unfolding subspace_topology_def using hW(3) hW_sub_hFp
    using product_topology_on_open_sets unfolding top1_open_sets_def by (by100 blast)
  define S where "S = {t \<in> I_set. g t \<in> W}"
  have hS_open: "S \<in> I_top"
    unfolding S_def using hg_cont hW_in_sub unfolding top1_continuous_map_on_def by (by100 blast)
  have ht0_S: "t0 \<in> S"
  proof -
    have "g t0 = w" unfolding w_def by (by100 simp)
    hence "g t0 \<in> W" using hW(2) by (by100 simp)
    thus ?thesis unfolding S_def using ht0_I by (by100 blast)
  qed
  \<comment> \<open>S open in [0,1] containing t0 \<in> (0,1) \<Rightarrow> \<exists>\<delta>>0 with (t0-\<delta>,t0+\<delta>) \<inter> [0,1] \<subseteq> S.\<close>
  obtain \<delta> where hd: "\<delta> > 0" "\<forall>t. t \<in> I_set \<longrightarrow> dist t t0 < \<delta> \<longrightarrow> t \<in> S"
  proof -
    obtain WR where "WR \<in> top1_open_sets" "S = I_set \<inter> WR"
      using hS_open unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
    hence "open WR" "t0 \<in> WR" unfolding top1_open_sets_def using ht0_S by (by100 blast)+
    then obtain e where "e > 0" "\<forall>y. dist y t0 < e \<longrightarrow> y \<in> WR"
      unfolding open_dist by (by100 force)
    thus ?thesis using that \<open>S = I_set \<inter> WR\<close> by (by100 blast)
  qed
  \<comment> \<open>S - {t0} intersects both [0,t0) and (t0,1].\<close>
  obtain s1 where hs1: "s1 \<in> S" "s1 < t0"
  proof -
    define s1 where "s1 = t0 - min \<delta> t0 / 2"
    have "s1 \<in> I_set" unfolding s1_def top1_unit_interval_def using ht0_01 hd(1) by auto
    moreover have "dist s1 t0 < \<delta>" unfolding s1_def dist_real_def using hd(1) ht0_01(1) by auto
    ultimately have "s1 \<in> S" using hd(2) by (by100 blast)
    moreover have "s1 < t0" unfolding s1_def using hd(1) ht0_01(1) by auto
    ultimately show ?thesis using that by (by100 blast)
  qed
  obtain s2 where hs2: "s2 \<in> S" "s2 > t0"
  proof -
    define s2 where "s2 = t0 + min \<delta> (1 - t0) / 2"
    have "s2 \<in> I_set" unfolding s2_def top1_unit_interval_def using ht0_01 hd(1)
      by (auto simp: min_def field_simps)
    moreover have "dist s2 t0 < \<delta>" unfolding s2_def dist_real_def using hd(1) ht0_01(2) by auto
    ultimately have "s2 \<in> S" using hd(2) by (by100 blast)
    moreover have "s2 > t0" unfolding s2_def using hd(1) ht0_01(2) by auto
    ultimately show ?thesis using that by (by100 blast)
  qed
  \<comment> \<open>Key contradiction: g is a homeomorphism, so g\<inverse> maps connected W-{w} to connected S-{t0}.
     But S-{t0} \<subseteq> [0,1]-{t0} = [0,t0) \<union> (t0,1] which is disconnected, and S-{t0} spans both halves.
     A connected set spanning both halves of a clopen partition is impossible.\<close>
  \<comment> \<open>S-{t0} is NOT connected: s1 < t0 < s2, both in S, separated by {..<t0} and {t0<..}.\<close>
  have hS_minus_not_connected: "\<not> connected (S - {t0})"
  proof -
    have "s1 \<in> S - {t0}" using hs1 by auto
    moreover have "s2 \<in> S - {t0}" using hs2 by auto
    moreover have "s1 \<in> {..<t0}" using hs1(2) by (by100 simp)
    moreover have "s2 \<in> {t0<..}" using hs2(2) by (by100 simp)
    moreover have "S - {t0} \<subseteq> {..<t0} \<union> {t0<..}" by auto
    moreover have "open ({..<t0} :: real set)" by (rule open_lessThan)
    moreover have "open ({t0<..} :: real set)" by (rule open_greaterThan)
    moreover have "{..<t0} \<inter> {t0<..} = ({} :: real set)" by auto
    ultimately show ?thesis unfolding connected_def by (by100 blast)
  qed
  \<comment> \<open>S-{t0} IS connected (homeomorphism preserves connected W-{w}).
     Proof: inv\_into I\_set g maps W-{w} (HOL connected) to S-{t0}.
     HOL connected \<leftrightarrow> top1\_connected via top1\_connected\_on\_subspace\_open\_iff\_connected.
     Theorem\_23\_5: continuous image of connected = connected.
     Bridges via subspace\_topology\_trans + product\_topology\_on\_open\_sets.\<close>
  have hS_minus_connected: "connected (S - {t0})"
  proof -
    have hTY_match: "(subspace_topology (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) (h ` Fp))
        = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (h ` Fp)"
      by (by100 simp)
    show ?thesis
      by (rule homeomorphism_inv_connected_bridge[OF hg hTY_match hW_del hW_sub_hFp hW(2) ht0_I])
         (use w_def S_def in auto)
  qed
  \<comment> \<open>connected(S-{t0}) now proved via homeomorphism\_inv\_connected\_bridge helper lemma.\<close>
  show False using hS_minus_connected hS_minus_not_connected by (by100 blast)
qed

\<comment> \<open>Corollary: p is in the closure of S2 - Fp.\<close>
lemma arc_endpoint_in_closure_of_complement_S2:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "top1_is_arc_on Fp (subspace_topology top1_S2 top1_S2_topology Fp)"
  and "Fp \<subseteq> top1_S2"
  and "top1_arc_endpoints_on Fp (subspace_topology top1_S2 top1_S2_topology Fp) = {p, d}"
  and "p \<noteq> d"
  shows "p \<in> closure_on top1_S2 top1_S2_topology (top1_S2 - Fp)"
proof -
  have hp_S2: "p \<in> top1_S2" using assms(3,4)
    unfolding top1_arc_endpoints_on_def by (by100 blast)
  have hA_sub: "top1_S2 - Fp \<subseteq> top1_S2" by (by100 blast)
  show ?thesis
    unfolding Theorem_17_5a_strict[OF assms(1) hp_S2 hA_sub]
  proof (intro allI impI)
    fix V assume hV: "neighborhood_of_strict p top1_S2 top1_S2_topology V"
    then obtain U where hU: "U \<in> top1_S2_topology" "p \<in> U" "U \<subseteq> V"
      unfolding neighborhood_of_strict_def by (by100 blast)
    from arc_endpoint_not_interior_S2[OF assms(1-5) hU(1,2)]
    obtain x where "x \<in> U" "x \<notin> Fp" "x \<in> top1_S2" by (by100 blast)
    hence "x \<in> V \<inter> (top1_S2 - Fp)" using hU(3) by (by100 blast)
    thus "intersects V (top1_S2 - Fp)" unfolding intersects_def by (by100 blast)
  qed
qed

\<comment> \<open>arc\_endpoint\_accessibility removed: no longer needed.
   The K4 diagonal construction now uses Munkres\_Step\_1\_arc\_splice directly,
   bypassing boundary accessibility entirely.\<close>

\<comment> \<open>First-hit sub-arc: given arc A from p to q with A \<inter> D \<noteq> {} and p \<notin> D, D closed,
   get sub-arc Fp from p to a point d \<in> D with Fp \<inter> D = {d}.\<close>
lemma first_hit_sub_arc:
  assumes hS2: "is_topology_on_strict top1_S2 top1_S2_topology"
  and hA: "top1_is_arc_on A (subspace_topology top1_S2 top1_S2_topology A)"
  and hA_sub: "A \<subseteq> top1_S2"
  and hA_ep: "top1_arc_endpoints_on A (subspace_topology top1_S2 top1_S2_topology A) = {p, q}"
  and hpq: "p \<noteq> q"
  and hD_closed: "closedin_on top1_S2 top1_S2_topology D"
  and hAD: "A \<inter> D \<noteq> {}"
  and hp_not_D: "p \<notin> D"
  and hq_not_D: "q \<notin> D"
  shows "\<exists>Fp d. d \<in> A \<inter> D \<and> p \<in> Fp \<and> d \<in> Fp \<and>
    top1_is_arc_on Fp (subspace_topology top1_S2 top1_S2_topology Fp) \<and>
    top1_arc_endpoints_on Fp (subspace_topology top1_S2 top1_S2_topology Fp) = {p, d} \<and>
    Fp \<subseteq> A \<and> Fp \<inter> D = {d} \<and> q \<notin> Fp"
proof -
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology" by (rule top1_S2_is_hausdorff)
  \<comment> \<open>Step 1: Get homeomorphism h: [0,1] \<rightarrow> A oriented with h(0)=p.\<close>
  obtain h where hh: "top1_homeomorphism_on I_set I_top A (subspace_topology top1_S2 top1_S2_topology A) h"
    using hA unfolding top1_is_arc_on_def by (by100 blast)
  have hh_bij: "bij_betw h I_set A" using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hh_inj: "inj_on h I_set" using hh_bij unfolding bij_betw_def by (by100 blast)
  have hh_img: "h ` I_set = A" using hh_bij unfolding bij_betw_def by (by100 blast)
  have hh_cont: "top1_continuous_map_on I_set I_top A (subspace_topology top1_S2 top1_S2_topology A) h"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hh_ep: "{h 0, h 1} = {p, q}"
    using arc_endpoints_are_boundary[OF hS2 hS2_haus hA_sub hA hh] hA_ep by (by100 simp)
  \<comment> \<open>Orient: WLOG h(0) = p. If h(0) = q, compose with reversal.\<close>
  have h0_p_or_q: "h 0 = p \<or> h 0 = q" using hh_ep by auto
  \<comment> \<open>Define oriented homeomorphism.\<close>
  define h' where "h' = (if h 0 = p then h else h \<circ> (\<lambda>t. 1 - t))"
  have hh'0: "h' 0 = p"
    unfolding h'_def using hh_ep hpq by auto
  have hh'1: "h' 1 = q"
  proof (cases "h 0 = p")
    case True
    have "q \<in> {h 0, h 1}" using hh_ep by (by100 blast)
    hence "h 1 = q" using True hpq by (by100 blast)
    thus ?thesis unfolding h'_def using True by (by100 simp)
  next
    case False
    have "p \<in> {h 0, h 1}" using hh_ep by (by100 blast)
    hence "h 0 = q" using False hh_ep by (by100 blast)
    have "h 1 = p" using hh_ep \<open>h 0 = q\<close> hpq by (by100 blast)
    have "h' 1 = h (1 - 1)" unfolding h'_def using False by (by100 simp)
    thus ?thesis using \<open>h 0 = q\<close> by (by100 simp)
  qed
  have hh'_homeo: "top1_homeomorphism_on I_set I_top A (subspace_topology top1_S2 top1_S2_topology A) h'"
  proof (cases "h 0 = p")
    case True thus ?thesis unfolding h'_def using hh by (by100 simp)
  next
    case False
    hence "h 0 = q" using hh_ep by auto
    \<comment> \<open>h' = h \<circ> (\<lambda>t. 1-t). Both h and reversal are homeomorphisms. Composition is homeomorphism.\<close>
    have hrev: "top1_homeomorphism_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
      by (rule unit_interval_reversal_homeomorphism)
    have "top1_homeomorphism_on I_set I_top A (subspace_topology top1_S2 top1_S2_topology A) (h \<circ> (\<lambda>t. 1 - t))"
      by (rule homeomorphism_compose[OF hrev hh])
    thus ?thesis unfolding h'_def using False by (by100 simp)
  qed
  have hh'_bij: "bij_betw h' I_set A"
    using hh'_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hh'_inj: "inj_on h' I_set" using hh'_bij unfolding bij_betw_def by (by100 blast)
  have hh'_img: "h' ` I_set = A" using hh'_bij unfolding bij_betw_def by (by100 blast)
  \<comment> \<open>Step 2: T = {t \<in> [0,1] | h'(t) \<in> D}. Closed, non-empty, compact.\<close>
  define T where "T = {t \<in> I_set. h' t \<in> D}"
  have hT_ne: "T \<noteq> {}"
  proof -
    obtain x where "x \<in> A" "x \<in> D" using hAD by (by100 blast)
    then obtain t where "t \<in> I_set" "h' t = x"
      using hh'_img by (by100 auto)
    hence "t \<in> T" using \<open>x \<in> D\<close> unfolding T_def by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  have hT_sub: "T \<subseteq> I_set" unfolding T_def by (by100 blast)
  have hTopS2': "is_topology_on top1_S2 top1_S2_topology"
    using hS2 unfolding is_topology_on_strict_def by (by100 blast)
  have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  have hh'_cont_A: "top1_continuous_map_on I_set I_top A
      (subspace_topology top1_S2 top1_S2_topology A) h'"
    using hh'_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hid_incl: "top1_continuous_map_on A (subspace_topology top1_S2 top1_S2_topology A)
      top1_S2 top1_S2_topology id"
    using Theorem_18_2[OF hTopS2' hTopS2' hTopS2'] hA_sub by (by100 blast)
  have hh'_cont: "top1_continuous_map_on I_set I_top top1_S2 top1_S2_topology h'"
  proof -
    have "top1_continuous_map_on I_set I_top top1_S2 top1_S2_topology (id \<circ> h')"
      by (rule top1_continuous_map_on_comp[OF hh'_cont_A hid_incl])
    thus ?thesis by (by100 simp)
  qed
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
  have hT_compact: "top1_compact_on T (subspace_topology UNIV (order_topology_on_UNIV :: real set set) T)"
  proof -
    have hT_cl: "closedin_on I_set I_top T"
      unfolding T_def
      by (rule continuous_preimage_closedin[OF hTI hTopS2' hh'_cont hD_closed])
    have hT_compact_I: "top1_compact_on T (subspace_topology I_set I_top T)"
      by (rule Theorem_26_2[OF hI_compact hT_cl])
    have hTsub: "T \<subseteq> I_set" unfolding T_def by (by100 blast)
    have "subspace_topology I_set I_top T =
        subspace_topology (UNIV::real set) top1_open_sets T"
      using subspace_topology_trans[of T I_set] hTsub
      unfolding top1_unit_interval_topology_def by (by100 simp)
    also have "\<dots> = subspace_topology (UNIV::real set) order_topology_on_UNIV T"
      using hopen_eq by (by100 simp)
    finally show ?thesis using hT_compact_I by (by100 simp)
  qed
  \<comment> \<open>Step 3: t0 = min T.\<close>
  obtain t0 where ht0: "t0 \<in> T" "\<forall>t \<in> T. t0 \<le> t"
    using top1_compact_on_order_topology_has_least[OF hT_ne hT_compact] by (by100 blast)
  have ht0_I: "t0 \<in> I_set" using ht0(1) hT_sub by (by100 blast)
  have ht0_D: "h' t0 \<in> D" using ht0(1) unfolding T_def by (by100 blast)
  \<comment> \<open>Step 4: t0 > 0 (since h'(0) = p \<notin> D).\<close>
  have ht0_pos: "t0 > 0"
  proof (rule ccontr)
    assume "\<not> t0 > 0"
    have "0 \<le> t0" "t0 \<le> 1" using ht0_I unfolding top1_unit_interval_def by auto
    hence "t0 = 0" using \<open>\<not> t0 > 0\<close> by (by100 linarith)
    hence "h' 0 \<in> D" using ht0_D by (by100 simp)
    thus False using hh'0 hp_not_D by (by100 blast)
  qed
  \<comment> \<open>Step 5: Fp = h'([0, t0]) is an arc.\<close>
  define Fp where "Fp = h' ` {0..t0}"
  have hFp_sub_A: "Fp \<subseteq> A"
    unfolding Fp_def using hh'_img ht0_I unfolding top1_unit_interval_def by auto
  have hp_Fp: "p \<in> Fp" unfolding Fp_def using hh'0 ht0_pos by auto
  have hd_Fp: "h' t0 \<in> Fp" unfolding Fp_def using ht0_pos by auto
  have hd_AD: "h' t0 \<in> A \<inter> D" using hFp_sub_A hd_Fp ht0_D by (by100 blast)
  \<comment> \<open>Arc proof via affine rescaling: \<phi>(t) = h'(t \<cdot> t0).\<close>
  have ht0_le1: "t0 \<le> 1" using ht0_I unfolding top1_unit_interval_def by (by100 simp)
  have hS2_haus': "is_hausdorff_on top1_S2 top1_S2_topology" by (rule top1_S2_is_hausdorff)
  define phi where "phi = (\<lambda>t. h' (t * t0))"
  have hFp_sub_S2: "Fp \<subseteq> top1_S2" using hFp_sub_A hA_sub by (by100 blast)
  have haffine: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. t * t0)"
  proof -
    have "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 0 + t * (t0 - 0))"
      by (rule affine_map_continuous_I_to_I[of 0 t0]) (use ht0_pos ht0_le1 in \<open>by100 simp\<close>)+
    thus ?thesis by (by100 simp)
  qed
  have hphi_cont: "top1_continuous_map_on I_set I_top top1_S2 top1_S2_topology phi"
  proof -
    have "top1_continuous_map_on I_set I_top top1_S2 top1_S2_topology (h' \<circ> (\<lambda>t. t * t0))"
      by (rule top1_continuous_map_on_comp[OF haffine hh'_cont])
    moreover have "(h' \<circ> (\<lambda>t. t * t0)) = phi" unfolding phi_def by (rule ext) (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  have hphi_inj: "inj_on phi I_set"
  proof (rule inj_onI)
    fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set" and heq: "phi s = phi t"
    have hs01: "0 \<le> s" "s \<le> 1" using hs unfolding top1_unit_interval_def by (by100 simp)+
    have ht01: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 simp)+
    have st0_I: "s * t0 \<in> I_set"
    proof -
      have "s * t0 \<le> 1 * 1" by (rule mult_mono) (use hs01 ht0_le1 ht0_pos in linarith)+
      thus ?thesis unfolding top1_unit_interval_def using hs01(1) ht0_pos by (by100 simp)
    qed
    have tt0_I: "t * t0 \<in> I_set"
    proof -
      have "t * t0 \<le> 1 * 1" by (rule mult_mono) (use ht01 ht0_le1 ht0_pos in linarith)+
      thus ?thesis unfolding top1_unit_interval_def using ht01(1) ht0_pos by (by100 simp)
    qed
    have "h' (s * t0) = h' (t * t0)" using heq unfolding phi_def by (by100 simp)
    hence "s * t0 = t * t0"
      by (metis inj_onD[OF hh'_inj] st0_I tt0_I)
    thus "s = t" using ht0_pos by (by100 simp)
  qed
  have hphi_img: "phi ` I_set = Fp"
  proof (intro set_eqI iffI)
    fix x assume "x \<in> phi ` I_set"
    then obtain t where "t \<in> I_set" "x = phi t" by (by100 blast)
    have "0 \<le> t" "t \<le> 1" using \<open>t \<in> I_set\<close> unfolding top1_unit_interval_def by (by100 simp)+
    have "t * t0 \<le> 1 * t0"
      by (rule mult_right_mono) (use \<open>t\<le>1\<close> ht0_pos in \<open>by100 simp\<close>)+
    hence "t * t0 \<le> t0" by (by100 simp)
    moreover have "0 \<le> t * t0" using \<open>0\<le>t\<close> ht0_pos by (by100 simp)
    ultimately show "x \<in> Fp" using \<open>x = phi t\<close> unfolding Fp_def phi_def by (by100 force)
  next
    fix x assume "x \<in> Fp"
    then obtain s where hs: "0 \<le> s" "s \<le> t0" "x = h' s" unfolding Fp_def by auto
    have "s / t0 \<in> I_set" using hs(1,2) ht0_pos
      unfolding top1_unit_interval_def by (by100 simp)
    moreover have "phi (s / t0) = h' s" using ht0_pos unfolding phi_def by (by100 simp)
    ultimately show "x \<in> phi ` I_set" using hs(3) by (by100 force)
  qed
  have hFp_arc: "top1_is_arc_on Fp (subspace_topology top1_S2 top1_S2_topology Fp)"
  proof -
    have "top1_embedding_on I_set I_top top1_S2 top1_S2_topology phi"
      by (rule top1_embedding_on_compact_inj[OF hTI hTopS2' hI_compact hS2_haus' hphi_cont hphi_inj])
    hence "top1_homeomorphism_on I_set I_top (phi ` I_set) (subspace_topology top1_S2 top1_S2_topology (phi ` I_set)) phi"
      unfolding top1_embedding_on_def by (by100 blast)
    hence "top1_homeomorphism_on I_set I_top Fp (subspace_topology top1_S2 top1_S2_topology Fp) phi"
      using hphi_img by (by100 simp)
    moreover have "is_topology_on_strict Fp (subspace_topology top1_S2 top1_S2_topology Fp)"
      by (rule subspace_topology_is_strict[OF hS2 hFp_sub_S2])
    ultimately show ?thesis unfolding top1_is_arc_on_def by (by100 blast)
  qed
  have hFp_ep: "top1_arc_endpoints_on Fp (subspace_topology top1_S2 top1_S2_topology Fp) = {p, h' t0}"
  proof -
    have hphi_homeo: "top1_homeomorphism_on I_set I_top Fp (subspace_topology top1_S2 top1_S2_topology Fp) phi"
    proof -
      have "top1_embedding_on I_set I_top top1_S2 top1_S2_topology phi"
        by (rule top1_embedding_on_compact_inj[OF hTI hTopS2' hI_compact hS2_haus' hphi_cont hphi_inj])
      hence "top1_homeomorphism_on I_set I_top (phi ` I_set) (subspace_topology top1_S2 top1_S2_topology (phi ` I_set)) phi"
        unfolding top1_embedding_on_def by (by100 blast)
      thus ?thesis using hphi_img by (by100 simp)
    qed
    have "top1_arc_endpoints_on Fp (subspace_topology top1_S2 top1_S2_topology Fp) = {phi 0, phi 1}"
      by (rule arc_endpoints_are_boundary[OF hS2 hS2_haus' hFp_sub_S2 hFp_arc hphi_homeo])
    moreover have "phi 0 = p" unfolding phi_def using hh'0 by (by100 simp)
    moreover have "phi 1 = h' t0" unfolding phi_def by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Step 6: Fp \<inter> D = {h'(t0)} (minimality of t0).\<close>
  have hFp_D: "Fp \<inter> D = {h' t0}"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> Fp \<inter> D"
    hence hx_Fp: "x \<in> Fp" and hx_D: "x \<in> D" by auto
    from hx_Fp obtain t where ht: "t \<in> {0..t0}" "x = h' t" unfolding Fp_def by auto
    have "t \<in> I_set" using ht(1) ht0_I unfolding top1_unit_interval_def by auto
    hence "t \<in> T" using hx_D ht(2) unfolding T_def by (by100 blast)
    hence "t0 \<le> t" using ht0(2) by (by100 blast)
    have "t \<le> t0" using ht(1) by auto
    hence "t = t0" using \<open>t0 \<le> t\<close> by (by100 linarith)
    thus "x \<in> {h' t0}" using ht(2) by (by100 blast)
  next
    fix x assume "x \<in> {h' t0}" thus "x \<in> Fp \<inter> D" using hd_Fp ht0_D by (by100 blast)
  qed
  \<comment> \<open>q \<notin> Fp: d = h'(t0) \<in> D, q \<notin> D \<Rightarrow> d \<noteq> q \<Rightarrow> t0 \<noteq> 1 \<Rightarrow> t0 < 1. Then q=h'(1) \<notin> h'([0,t0]).\<close>
  have hd_ne_q: "h' t0 \<noteq> q"
  proof
    assume "h' t0 = q" thus False using ht0_D hq_not_D by (by100 blast)
  qed
  have ht0_lt1: "t0 < 1"
  proof -
    have "t0 \<le> 1" using ht0_I unfolding top1_unit_interval_def by (by100 simp)
    moreover have "t0 \<noteq> 1"
    proof
      assume "t0 = 1"
      hence "h' t0 = h' 1" by (by100 simp)
      hence "h' t0 = q" using hh'1 by (by100 simp)
      thus False using hd_ne_q by (by100 blast)
    qed
    ultimately show ?thesis by (by100 linarith)
  qed
  have hq_notin_Fp: "q \<notin> Fp"
  proof
    assume "q \<in> Fp"
    then obtain t where ht: "t \<in> {0..t0}" "q = h' t" unfolding Fp_def by auto
    have "t \<in> I_set" using ht(1) ht0_I unfolding top1_unit_interval_def by auto
    have "1 \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have "h' t = h' 1" using ht(2) hh'1 by (by100 simp)
    hence "t = 1" by (metis inj_onD[OF hh'_inj] \<open>t \<in> I_set\<close> \<open>1 \<in> I_set\<close>)
    hence "t0 \<ge> 1" using ht(1) by auto
    thus False using ht0_lt1 by (by100 linarith)
  qed
  show ?thesis using hd_AD hp_Fp hd_Fp hFp_arc hFp_ep hFp_sub_A hFp_D hq_notin_Fp by (by100 blast)
qed

lemma K4_from_SCC:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  and "p \<in> top1_S2 - C" and "q \<in> top1_S2 - C"
  and "\<not> (\<exists>f. top1_is_path_on (top1_S2 - C)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p q f)"
  shows "\<exists>a1 a2 a3 a4 e12 e23 e34 e41 e13 e24 p0 q0.
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
    \<and> q0 \<in> e13 - {a1, a3} \<and> p0 \<in> e24 - {a2, a4}
    \<and> top1_in_same_path_component_on (top1_S2 - C)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p p0
    \<and> top1_in_same_path_component_on (top1_S2 - C)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) q q0
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
  \<comment> \<open>Step 2 deferred: Split C1/C2 at crossing points (not midpoints). See below.\<close>
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
  \<comment> \<open>arc\_f avoids C1 \<Rightarrow> arc\_f \<inter> C \<subseteq> C2 - {a1,a3}. arc\_f must cross C2 (otherwise
     arc\_f gives a path from p to q avoiding all of C, contradicting separation).
     Similarly arc\_g \<inter> C \<subseteq> C1 - {a1,a3} and arc\_g must cross C1.\<close>
  have harc_f_sub_S2: "arc_f \<subseteq> top1_S2" using harc_f(2) by (by100 blast)
  have harc_g_sub_S2: "arc_g \<subseteq> top1_S2" using harc_g(2) by (by100 blast)
  \<comment> \<open>arc\_f must intersect C2 (otherwise it avoids all of C).\<close>
  have hf_meets_C2: "arc_f \<inter> C2 \<noteq> {}"
  proof (rule ccontr)
    assume "\<not> arc_f \<inter> C2 \<noteq> {}"
    hence "arc_f \<inter> C2 = {}" by (by100 simp)
    hence "arc_f \<subseteq> top1_S2 - C"
      using harc_f(2) hC12(1) by (by100 blast)
    \<comment> \<open>arc\_f is an arc from p to q in S2-C, giving a path from p to q in S2-C.\<close>
    hence harc_f_SC: "arc_f \<subseteq> top1_S2 - C" .
    \<comment> \<open>Arc arc\_f is path-connected (homeomorphic to [0,1]). Get path from p to q.\<close>
    obtain hf where hhf: "top1_homeomorphism_on I_set I_top arc_f
        (subspace_topology top1_S2 top1_S2_topology arc_f) hf"
      using harc_f(1) unfolding top1_is_arc_on_def by (by100 blast)
    have hhf_ep: "{hf 0, hf 1} = {p, q}"
      using arc_endpoints_are_boundary[OF assms(1) hS2_haus harc_f_sub_S2 harc_f(1) hhf]
        harc_f(3) by (by100 simp)
    \<comment> \<open>hf (possibly reversed) gives a path from p to q in arc\_f \<subseteq> S2-C.\<close>
    \<comment> \<open>hf is continuous I \<rightarrow> arc\_f (subspace). arc\_f \<subseteq> S2-C. Transfer to S2-C subspace.\<close>
    have hhf_cont: "top1_continuous_map_on I_set I_top arc_f
        (subspace_topology top1_S2 top1_S2_topology arc_f) hf"
      using hhf unfolding top1_homeomorphism_on_def by (by100 blast)
    have hhf_cont_SC: "top1_continuous_map_on I_set I_top (top1_S2 - C)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) hf"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix t assume "t \<in> I_set"
      thus "hf t \<in> top1_S2 - C"
        using hhf_cont harc_f_SC unfolding top1_continuous_map_on_def by (by100 blast)
    next
      fix V assume hV: "V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)"
      then obtain W where hW: "W \<in> top1_S2_topology" "V = (top1_S2 - C) \<inter> W"
        unfolding subspace_topology_def by (by100 blast)
      have "arc_f \<inter> W \<in> subspace_topology top1_S2 top1_S2_topology arc_f"
        unfolding subspace_topology_def using hW(1) by (by100 blast)
      hence "{t \<in> I_set. hf t \<in> arc_f \<inter> W} \<in> I_top"
        using hhf_cont unfolding top1_continuous_map_on_def by (by100 blast)
      moreover have "{t \<in> I_set. hf t \<in> V} = {t \<in> I_set. hf t \<in> arc_f \<inter> W}"
        using hhf_cont harc_f_SC hW(2) unfolding top1_continuous_map_on_def by (by100 blast)
      ultimately show "{t \<in> I_set. hf t \<in> V} \<in> I_top" by (by100 simp)
    qed
    \<comment> \<open>Handle endpoint orientation: either hf(0)=p or hf(0)=q.\<close>
    from hhf_ep hp_ne_q have "(hf 0 = p \<and> hf 1 = q) \<or> (hf 0 = q \<and> hf 1 = p)"
      by auto
    hence "\<exists>f. top1_is_path_on (top1_S2 - C)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p q f"
    proof
      assume "hf 0 = p \<and> hf 1 = q"
      hence "top1_is_path_on (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p q hf"
        unfolding top1_is_path_on_def using hhf_cont_SC by (by100 blast)
      thus ?thesis by (by100 blast)
    next
      assume hrev: "hf 0 = q \<and> hf 1 = p"
      define hf_rev where "hf_rev = (\<lambda>t. hf (1 - t))"
      have hrev_cont: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
        using unit_interval_reversal_homeomorphism unfolding top1_homeomorphism_on_def
        by (by100 blast)
      have "top1_continuous_map_on I_set I_top (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) (hf \<circ> (\<lambda>t. 1 - t))"
        by (rule top1_continuous_map_on_comp[OF hrev_cont hhf_cont_SC])
      hence "top1_continuous_map_on I_set I_top (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) hf_rev"
        unfolding hf_rev_def comp_def by (by100 simp)
      moreover have "hf_rev 0 = p" unfolding hf_rev_def using hrev by (by100 simp)
      moreover have "hf_rev 1 = q" unfolding hf_rev_def using hrev by (by100 simp)
      ultimately have "top1_is_path_on (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p q hf_rev"
        unfolding top1_is_path_on_def by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    thus False using assms(5) by (by100 blast)
  qed
  have hg_meets_C1: "arc_g \<inter> C1 \<noteq> {}"
  proof (rule ccontr)
    assume "\<not> arc_g \<inter> C1 \<noteq> {}"
    hence "arc_g \<inter> C1 = {}" by (by100 simp)
    hence harc_g_SC: "arc_g \<subseteq> top1_S2 - C"
      using harc_g(2) hC12(1) by (by100 blast)
    obtain hg where hhg: "top1_homeomorphism_on I_set I_top arc_g
        (subspace_topology top1_S2 top1_S2_topology arc_g) hg"
      using harc_g(1) unfolding top1_is_arc_on_def by (by100 blast)
    have hhg_ep: "{hg 0, hg 1} = {p, q}"
      using arc_endpoints_are_boundary[OF assms(1) hS2_haus harc_g_sub_S2 harc_g(1) hhg]
        harc_g(3) by (by100 simp)
    have hhg_cont: "top1_continuous_map_on I_set I_top arc_g
        (subspace_topology top1_S2 top1_S2_topology arc_g) hg"
      using hhg unfolding top1_homeomorphism_on_def by (by100 blast)
    have hhg_cont_SC: "top1_continuous_map_on I_set I_top (top1_S2 - C)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) hg"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix t assume "t \<in> I_set"
      thus "hg t \<in> top1_S2 - C"
        using hhg_cont harc_g_SC unfolding top1_continuous_map_on_def by (by100 blast)
    next
      fix V assume hV: "V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)"
      then obtain W where hW: "W \<in> top1_S2_topology" "V = (top1_S2 - C) \<inter> W"
        unfolding subspace_topology_def by (by100 blast)
      have "arc_g \<inter> W \<in> subspace_topology top1_S2 top1_S2_topology arc_g"
        unfolding subspace_topology_def using hW(1) by (by100 blast)
      hence "{t \<in> I_set. hg t \<in> arc_g \<inter> W} \<in> I_top"
        using hhg_cont unfolding top1_continuous_map_on_def by (by100 blast)
      moreover have "{t \<in> I_set. hg t \<in> V} = {t \<in> I_set. hg t \<in> arc_g \<inter> W}"
        using hhg_cont harc_g_SC hW(2) unfolding top1_continuous_map_on_def by (by100 blast)
      ultimately show "{t \<in> I_set. hg t \<in> V} \<in> I_top" by (by100 simp)
    qed
    from hhg_ep hp_ne_q have "(hg 0 = p \<and> hg 1 = q) \<or> (hg 0 = q \<and> hg 1 = p)"
      by auto
    hence "\<exists>f. top1_is_path_on (top1_S2 - C)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p q f"
    proof
      assume "hg 0 = p \<and> hg 1 = q"
      hence "top1_is_path_on (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p q hg"
        unfolding top1_is_path_on_def using hhg_cont_SC by (by100 blast)
      thus ?thesis by (by100 blast)
    next
      assume hrev: "hg 0 = q \<and> hg 1 = p"
      define hg_rev where "hg_rev = (\<lambda>t. hg (1 - t))"
      have hrev_cont: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
        using unit_interval_reversal_homeomorphism unfolding top1_homeomorphism_on_def
        by (by100 blast)
      have "top1_continuous_map_on I_set I_top (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) (hg \<circ> (\<lambda>t. 1 - t))"
        by (rule top1_continuous_map_on_comp[OF hrev_cont hhg_cont_SC])
      hence "top1_continuous_map_on I_set I_top (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) hg_rev"
        unfolding hg_rev_def comp_def by (by100 simp)
      moreover have "hg_rev 0 = p" unfolding hg_rev_def using hrev by (by100 simp)
      moreover have "hg_rev 1 = q" unfolding hg_rev_def using hrev by (by100 simp)
      ultimately have "top1_is_path_on (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p q hg_rev"
        unfolding top1_is_path_on_def by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    thus False using assms(5) by (by100 blast)
  qed
  \<comment> \<open>First-hit sub-arcs from p: Fp (p\<rightarrow>a4' in S2-C1, Fp\<inter>C2={a4'}),
     Gp (p\<rightarrow>a2' in S2-C2, Gp\<inter>C1={a2'}).\<close>
  have hp_not_C2: "p \<notin> C2" using hp_notC hC12(1) by (by100 blast)
  have hp_not_C1: "p \<notin> C1" using hp_notC hC12(1) by (by100 blast)
  have hq_not_C2: "q \<notin> C2" using hq_notC hC12(1) by (by100 blast)
  have hq_not_C1: "q \<notin> C1" using hq_notC hC12(1) by (by100 blast)
  from first_hit_sub_arc[OF assms(1) harc_f(1) harc_f_sub_S2 harc_f(3) hp_ne_q hC2_cl hf_meets_C2 hp_not_C2 hq_not_C2]
  obtain Fp a4' where hFp: "a4' \<in> arc_f \<inter> C2" "p \<in> Fp" "a4' \<in> Fp"
      "top1_is_arc_on Fp (subspace_topology top1_S2 top1_S2_topology Fp)"
      "top1_arc_endpoints_on Fp (subspace_topology top1_S2 top1_S2_topology Fp) = {p, a4'}"
      "Fp \<subseteq> arc_f" "Fp \<inter> C2 = {a4'}" "q \<notin> Fp"
    by auto
  from first_hit_sub_arc[OF assms(1) harc_g(1) harc_g_sub_S2 harc_g(3) hp_ne_q hC1_cl hg_meets_C1 hp_not_C1 hq_not_C1]
  obtain Gp a2' where hGp: "a2' \<in> arc_g \<inter> C1" "p \<in> Gp" "a2' \<in> Gp"
      "top1_is_arc_on Gp (subspace_topology top1_S2 top1_S2_topology Gp)"
      "top1_arc_endpoints_on Gp (subspace_topology top1_S2 top1_S2_topology Gp) = {p, a2'}"
      "Gp \<subseteq> arc_g" "Gp \<inter> C1 = {a2'}" "q \<notin> Gp"
    by auto
  \<comment> \<open>First-hit sub-arcs from q (symmetric, using reversed arcs).\<close>
  have hq_ne_p: "q \<noteq> p" using hp_ne_q by (by100 blast)
  have harc_f_ep_qp: "top1_arc_endpoints_on arc_f (subspace_topology top1_S2 top1_S2_topology arc_f) = {q, p}"
    using harc_f(3) by (by100 blast)
  have harc_g_ep_qp: "top1_arc_endpoints_on arc_g (subspace_topology top1_S2 top1_S2_topology arc_g) = {q, p}"
    using harc_g(3) by (by100 blast)
  from first_hit_sub_arc[OF assms(1) harc_f(1) harc_f_sub_S2 harc_f_ep_qp hq_ne_p hC2_cl hf_meets_C2 hq_not_C2 hp_not_C2]
  obtain Fq b4 where hFq: "b4 \<in> arc_f \<inter> C2" "q \<in> Fq" "b4 \<in> Fq"
      "top1_is_arc_on Fq (subspace_topology top1_S2 top1_S2_topology Fq)"
      "top1_arc_endpoints_on Fq (subspace_topology top1_S2 top1_S2_topology Fq) = {q, b4}"
      "Fq \<subseteq> arc_f" "Fq \<inter> C2 = {b4}" "p \<notin> Fq"
    by auto
  from first_hit_sub_arc[OF assms(1) harc_g(1) harc_g_sub_S2 harc_g_ep_qp hq_ne_p hC1_cl hg_meets_C1 hq_not_C1 hp_not_C1]
  obtain Gq b2 where hGq: "b2 \<in> arc_g \<inter> C1" "q \<in> Gq" "b2 \<in> Gq"
      "top1_is_arc_on Gq (subspace_topology top1_S2 top1_S2_topology Gq)"
      "top1_arc_endpoints_on Gq (subspace_topology top1_S2 top1_S2_topology Gq) = {q, b2}"
      "Gq \<subseteq> arc_g" "Gq \<inter> C1 = {b2}" "p \<notin> Gq"
    by auto
  \<comment> \<open>DIAGONAL CONSTRUCTION via Munkres Step 1 arc-splice.
     Fp (a4'\<rightarrow>p) + Gp (p\<rightarrow>a2'): splice at p gives arc D13 from a4' to a2' through p.
     Fq (b4\<rightarrow>q) + Gq (q\<rightarrow>b2): splice at q gives arc D24 from b4 to b2 through q.
     No boundary accessibility needed!\<close>
  have hFp_sub_S2: "Fp \<subseteq> top1_S2" using hFp(6) harc_f_sub_S2 by (by100 blast)
  have hGp_sub_S2: "Gp \<subseteq> top1_S2" using hGp(6) harc_g_sub_S2 by (by100 blast)
  have hFq_sub_S2: "Fq \<subseteq> top1_S2" using hFq(6) harc_f_sub_S2 by (by100 blast)
  have hGq_sub_S2: "Gq \<subseteq> top1_S2" using hGq(6) harc_g_sub_S2 by (by100 blast)
  have ha4'_ne_p: "a4' \<noteq> p" using hFp(1) harc_f(2) hC12(2) hp_not_C2 by (by100 blast)
  have hp_ne_a2': "p \<noteq> a2'" using hGp(1) harc_g(2) hC12(2) hp_not_C1 by (by100 blast)
  have hb4_ne_q: "b4 \<noteq> q" using hFq(1) harc_f(2) hC12(2) hq_not_C2 by (by100 blast)
  have hq_ne_b2: "q \<noteq> b2" using hGq(1) harc_g(2) hC12(2) hq_not_C1 by (by100 blast)
  have ha4'_notin_Gp: "a4' \<notin> Gp" using hFp(1) hGp(6) harc_g(2) by (by100 blast)
  have hb4_notin_Gq: "b4 \<notin> Gq" using hFq(1) hGq(6) harc_g(2) by (by100 blast)
  \<comment> \<open>Splice Fp + Gp into diagonal D13.\<close>
  have hFp_ep_swap: "top1_arc_endpoints_on Fp (subspace_topology top1_S2 top1_S2_topology Fp) = {a4', p}"
    using hFp(5) by (by100 blast)
  from Munkres_Step_1_arc_splice[OF assms(1) hFp(4) hGp(4) hFp_sub_S2 hGp_sub_S2
      hFp_ep_swap hGp(5) ha4'_ne_p hp_ne_a2' ha4'_notin_Gp]
  obtain D13 where hD13: "top1_is_arc_on D13 (subspace_topology top1_S2 top1_S2_topology D13)"
      "D13 \<subseteq> Fp \<union> Gp" "a4' \<in> D13" "a2' \<in> D13"
      "top1_arc_endpoints_on D13 (subspace_topology top1_S2 top1_S2_topology D13) = {a4', a2'}"
    by (by100 blast)
  have hFp_C1: "Fp \<inter> C1 = {}" using hFp(6) harc_f(2) by (by100 blast)
  have hGp_C2: "Gp \<inter> C2 = {}" using hGp(6) harc_g(2) by (by100 blast)
  have hD13_C: "D13 \<inter> C \<subseteq> {a4', a2'}"
  proof -
    have "D13 \<inter> C \<subseteq> (Fp \<union> Gp) \<inter> (C1 \<union> C2)" using hD13(2) hC12(1) by (by100 blast)
    also have "\<dots> = (Fp \<inter> C1) \<union> (Fp \<inter> C2) \<union> (Gp \<inter> C1) \<union> (Gp \<inter> C2)" by (by100 blast)
    also have "\<dots> = {} \<union> {a4'} \<union> {a2'} \<union> {}" using hFp_C1 hFp(7) hGp(7) hGp_C2 by (by100 simp)
    finally show ?thesis by (by100 blast)
  qed
  \<comment> \<open>NEW APPROACH: Use vertices {a1, a2', a3, a4'} instead of {a2', b2, a4', b4}.
     Diagonal e24 = D13 (from a2' to a4', interior in component(p)).
     Diagonal e13 from a1 to a3 (interior in component(q)) — sorry for now.
     Choose p0 from D13 interior, q0 from e13 interior.\<close>
  have ha4'_ne: "a4' \<noteq> a1" "a4' \<noteq> a3" using hFp(1) harc_f(2) hC12(2) by (by100 blast)+
  have ha2'_ne: "a2' \<noteq> a1" "a2' \<noteq> a3" using hGp(1) harc_g(2) hC12(2) by (by100 blast)+
  have ha4'_C2: "a4' \<in> C2" using hFp(1) by (by100 blast)
  have ha2'_C1: "a2' \<in> C1" using hGp(1) by (by100 blast)
  \<comment> \<open>a4' \<notin> C1 and a2' \<notin> C2 (since they are in interior of C2, C1 respectively, not at shared endpoints).\<close>
  have ha4'_notC1: "a4' \<notin> C1"
  proof
    assume "a4' \<in> C1"
    hence "a4' \<in> C1 \<inter> C2" using ha4'_C2 by (by100 blast)
    hence "a4' \<in> {a1, a3}" using hC12(2) by (by100 blast)
    thus False using ha4'_ne by (by100 blast)
  qed
  have ha2'_notC2: "a2' \<notin> C2"
  proof
    assume "a2' \<in> C2"
    hence "a2' \<in> C1 \<inter> C2" using ha2'_C1 by (by100 blast)
    hence "a2' \<in> {a1, a3}" using hC12(2) by (by100 blast)
    thus False using ha2'_ne by (by100 blast)
  qed
  have ha2'_ne_a4': "a2' \<noteq> a4'"
    using ha2'_C1 ha2'_notC2 ha4'_C2 by (by100 blast)
  \<comment> \<open>Get endpoints of C1 and C2.\<close>
  have hC1_ep: "top1_arc_endpoints_on C1 (subspace_topology top1_S2 top1_S2_topology C1) = {a1, a3}"
    by (rule scc_decomp_arc_endpoints(1)[OF assms(1) hS2_haus assms(2) hC12(4) hC12(5)
        hC1_sub hC2_sub hC12(1) hC12(2) hC12(3)])
  have hC2_ep: "top1_arc_endpoints_on C2 (subspace_topology top1_S2 top1_S2_topology C2) = {a1, a3}"
    by (rule scc_decomp_arc_endpoints(2)[OF assms(1) hS2_haus assms(2) hC12(4) hC12(5)
        hC1_sub hC2_sub hC12(1) hC12(2) hC12(3)])
  \<comment> \<open>a2' is an interior point of C1 (not an endpoint), a4' is interior to C2.\<close>
  have ha2'_not_ep: "a2' \<notin> top1_arc_endpoints_on C1 (subspace_topology top1_S2 top1_S2_topology C1)"
    using hC1_ep ha2'_ne by (by100 blast)
  have ha4'_not_ep: "a4' \<notin> top1_arc_endpoints_on C2 (subspace_topology top1_S2 top1_S2_topology C2)"
    using hC2_ep ha4'_ne by (by100 blast)
  \<comment> \<open>Split C1 at a2' into two sub-arcs: e12 (containing a1) and e23 (containing a3).\<close>
  from arc_split_at_given_point[OF assms(1) hS2_haus hC1_sub hC12(4) ha2'_C1 ha2'_not_ep hC1_ep hC12(3)]
  obtain e12 e23 where hC1_split: "C1 = e12 \<union> e23" "e12 \<inter> e23 = {a2'}"
      "top1_is_arc_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
      "top1_is_arc_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      "a1 \<in> e12" "a3 \<in> e23" "a2' \<in> e12" "a2' \<in> e23" "e12 \<subseteq> top1_S2" "e23 \<subseteq> top1_S2"
    by blast
  \<comment> \<open>Split C2 at a4' into two sub-arcs: e34 (containing a3) and e41 (containing a1).\<close>
  from arc_split_at_given_point[OF assms(1) hS2_haus hC2_sub hC12(5) ha4'_C2 ha4'_not_ep hC2_ep hC12(3)]
  obtain e34_raw e41_raw where hC2_split_raw: "C2 = e34_raw \<union> e41_raw"
      "e34_raw \<inter> e41_raw = {a4'}"
      "top1_is_arc_on e34_raw (subspace_topology top1_S2 top1_S2_topology e34_raw)"
      "top1_is_arc_on e41_raw (subspace_topology top1_S2 top1_S2_topology e41_raw)"
      "a1 \<in> e34_raw" "a3 \<in> e41_raw" "a4' \<in> e34_raw" "a4' \<in> e41_raw"
      "e34_raw \<subseteq> top1_S2" "e41_raw \<subseteq> top1_S2"
    by blast
  \<comment> \<open>Rename: e41 = e34\_raw (contains a1), e34 = e41\_raw (contains a3).\<close>
  define e41 where "e41 = e34_raw"
  define e34 where "e34 = e41_raw"
  have hC2_split: "C2 = e34 \<union> e41" "e34 \<inter> e41 = {a4'}"
      "top1_is_arc_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
      "top1_is_arc_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
      "a1 \<in> e41" "a3 \<in> e34" "a4' \<in> e41" "a4' \<in> e34"
      "e41 \<subseteq> top1_S2" "e34 \<subseteq> top1_S2"
    unfolding e41_def e34_def
    using hC2_split_raw by (by100 blast)+
  \<comment> \<open>Get endpoints of the split arcs.\<close>
  have he12_ep: "top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12) = {a1, a2'}"
    by (rule arc_split_endpoints(1)[OF assms(1) hS2_haus hC1_sub hC12(4) hC1_split(1,2,3,4)
        hC1_split(5,6,7,8,9,10) hC1_ep ha2'_not_ep])
  have he23_ep: "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a2', a3}"
    by (rule arc_split_endpoints(2)[OF assms(1) hS2_haus hC1_sub hC12(4) hC1_split(1,2,3,4)
        hC1_split(5,6,7,8,9,10) hC1_ep ha2'_not_ep])
  have he41_ep_raw: "top1_arc_endpoints_on e34_raw (subspace_topology top1_S2 top1_S2_topology e34_raw) = {a1, a4'}"
    by (rule arc_split_endpoints(1)[OF assms(1) hS2_haus hC2_sub hC12(5)
        hC2_split_raw(1,2,3,4,5,6,7,8,9,10) hC2_ep ha4'_not_ep])
  have he34_ep_raw: "top1_arc_endpoints_on e41_raw (subspace_topology top1_S2 top1_S2_topology e41_raw) = {a4', a3}"
    by (rule arc_split_endpoints(2)[OF assms(1) hS2_haus hC2_sub hC12(5)
        hC2_split_raw(1,2,3,4,5,6,7,8,9,10) hC2_ep ha4'_not_ep])
  have he41_ep: "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a1, a4'}"
    unfolding e41_def using he41_ep_raw by (by100 blast)
  have he34_ep: "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a4', a3}"
    unfolding e34_def using he34_ep_raw by (by100 blast)
  \<comment> \<open>e24 = D13 (diagonal from a2' to a4').\<close>
  define e24 where "e24 = D13"
  have he24_arc: "top1_is_arc_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
    unfolding e24_def using hD13(1) by (by100 blast)
  have he24_sub: "e24 \<subseteq> top1_S2"
    unfolding e24_def using hD13(2) hFp_sub_S2 hGp_sub_S2 by (by100 blast)
  have he24_ep: "top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24) = {a2', a4'}"
    unfolding e24_def using hD13(5) by (by100 blast)
  have he24_C: "e24 \<inter> C \<subseteq> {a4', a2'}" unfolding e24_def using hD13_C by (by100 blast)
  have ha2'_e24: "a2' \<in> e24" unfolding e24_def using hD13(4) by (by100 blast)
  have ha4'_e24: "a4' \<in> e24" unfolding e24_def using hD13(3) by (by100 blast)
  \<comment> \<open>D13 interior is in the path-component of p in S2-C.\<close>
  have hD13_interior_comp_p: "\<forall>x \<in> D13 - {a4', a2'}. x \<in> top1_S2 - C"
  proof (intro ballI)
    fix x assume "x \<in> D13 - {a4', a2'}"
    hence "x \<in> D13" "x \<noteq> a4'" "x \<noteq> a2'" by (by100 blast)+
    hence "x \<notin> C" using hD13_C by (by100 blast)
    moreover have "x \<in> top1_S2" using \<open>x \<in> D13\<close> hD13(2) hFp_sub_S2 hGp_sub_S2 by (by100 blast)
    ultimately show "x \<in> top1_S2 - C" by (by100 blast)
  qed
  \<comment> \<open>SORRY: Construct diagonal e13 from a1 to a3 with interior in component(q).
     This follows from Munkres Step 3 (line segment in R2 via stereographic projection)
     or from the fact that the boundary of each component of S2-C is C itself.\<close>
  obtain e13 where he13: "top1_is_arc_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
      "e13 \<subseteq> top1_S2"
      "top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13) = {a1, a3}"
      "e13 \<inter> C \<subseteq> {a1, a3}"
      "\<forall>x \<in> e13 - {a1, a3}. top1_in_same_path_component_on (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) q x"
    sorry \<comment> \<open>Munkres Step 3: arc from a1 to a3 through component of q.\<close>
  \<comment> \<open>Endpoints are elements of the arc.\<close>
  have ha1_e13: "a1 \<in> e13" using he13(3) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have ha3_e13: "a3 \<in> e13" using he13(3) unfolding top1_arc_endpoints_on_def by (by100 blast)
  \<comment> \<open>Choose p0 from D13 interior (in component of p) and q0 from e13 interior (in component of q).\<close>
  have hD13_interior_ne: "D13 - {a4', a2'} \<noteq> {}"
  proof -
    obtain h where hh: "top1_homeomorphism_on I_set I_top D13
        (subspace_topology top1_S2 top1_S2_topology D13) h"
      using hD13(1) unfolding top1_is_arc_on_def by (by100 blast)
    have hinj: "inj_on h I_set" using hh unfolding top1_homeomorphism_on_def bij_betw_def
      by (by100 blast)
    have himg: "\<forall>t \<in> I_set. h t \<in> D13" using hh
      unfolding top1_homeomorphism_on_def top1_continuous_map_on_def by (by100 blast)
    have h12_I: "(1/2::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have "h (1/2) \<in> D13" using himg h12_I by (by100 blast)
    have hep: "{h 0, h 1} = {a4', a2'}"
      using arc_endpoints_are_boundary[OF assms(1) hS2_haus _ hD13(1) hh] hD13(5) he24_sub
      unfolding e24_def by (by100 simp)
    have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have "h (1/2) \<noteq> h 0"
    proof
      assume "h (1/2) = h 0"
      from inj_onD[OF hinj this h12_I h0_I] show False by (by100 simp)
    qed
    moreover have "h (1/2) \<noteq> h 1"
    proof
      assume "h (1/2) = h 1"
      from inj_onD[OF hinj this h12_I h1_I] show False by (by100 simp)
    qed
    ultimately have "h (1/2) \<notin> {h 0, h 1}" by (by100 blast)
    hence "h (1/2) \<notin> {a4', a2'}" using hep by (by100 simp)
    thus ?thesis using \<open>h (1/2) \<in> D13\<close> by (by100 blast)
  qed
  have he13_interior_ne: "e13 - {a1, a3} \<noteq> {}"
  proof -
    obtain h where hh: "top1_homeomorphism_on I_set I_top e13
        (subspace_topology top1_S2 top1_S2_topology e13) h"
      using he13(1) unfolding top1_is_arc_on_def by (by100 blast)
    have hinj: "inj_on h I_set" using hh unfolding top1_homeomorphism_on_def bij_betw_def
      by (by100 blast)
    have himg: "\<forall>t \<in> I_set. h t \<in> e13" using hh
      unfolding top1_homeomorphism_on_def top1_continuous_map_on_def by (by100 blast)
    have h12_I: "(1/2::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have "h (1/2) \<in> e13" using himg h12_I by (by100 blast)
    have hep: "{h 0, h 1} = {a1, a3}"
      using arc_endpoints_are_boundary[OF assms(1) hS2_haus he13(2) he13(1) hh] he13(3)
      by (by100 simp)
    have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have "h (1/2) \<noteq> h 0"
    proof
      assume "h (1/2) = h 0"
      from inj_onD[OF hinj this h12_I h0_I] show False by (by100 simp)
    qed
    moreover have "h (1/2) \<noteq> h 1"
    proof
      assume "h (1/2) = h 1"
      from inj_onD[OF hinj this h12_I h1_I] show False by (by100 simp)
    qed
    ultimately have "h (1/2) \<notin> {h 0, h 1}" by (by100 blast)
    hence "h (1/2) \<notin> {a1, a3}" using hep by (by100 simp)
    thus ?thesis using \<open>h (1/2) \<in> e13\<close> by (by100 blast)
  qed
  from hD13_interior_ne obtain p0 where hp0: "p0 \<in> D13 - {a4', a2'}" by (by100 blast)
  from he13_interior_ne obtain q0 where hq0: "q0 \<in> e13 - {a1, a3}" by (by100 blast)
  \<comment> \<open>p0 is in the path-component of p in S2-C.\<close>
  have hp0_SC: "p0 \<in> top1_S2 - C" using hp0 hD13_interior_comp_p by (by100 blast)
  have hp0_comp_p: "top1_in_same_path_component_on (top1_S2 - C)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p p0"
  proof -
    \<comment> \<open>p0 \<in> D13 - {a4',a2'} \<subseteq> (Fp \<union> Gp) - {a4',a2'}.
       Both Fp-{a4'} and Gp-{a2'} contain p and lie in S2-C.
       D13 - {a4',a2'} \<subseteq> (Fp-{a4'}) \<union> (Gp-{a2'}), which is path-connected
       (union of connected sets sharing p). p0 is in same component as p.\<close>
    have "Fp - {a4'} \<subseteq> top1_S2 - C"
      using hFp(6) harc_f(2) hFp(7) hC12(1) by (by100 blast)
    have "Gp - {a2'} \<subseteq> top1_S2 - C"
      using hGp(6) harc_g(2) hGp(7) hC12(1) by (by100 blast)
    have hp_Fp_minus: "p \<in> Fp - {a4'}" using hFp(2) ha4'_ne_p by (by100 blast)
    have hp_Gp_minus: "p \<in> Gp - {a2'}" using hGp(2) hp_ne_a2' by (by100 blast)
    \<comment> \<open>Fp is an arc (path-connected). So Fp-{a4'} is connected and contains p.\<close>
    \<comment> \<open>Path from p to p0 exists in (Fp \<union> Gp) - {a4', a2'} \<subseteq> S2-C.\<close>
    show ?thesis sorry \<comment> \<open>Path-component of p0 = path-component of p via Fp,Gp arcs.\<close>
  qed
  have hq0_comp_q: "top1_in_same_path_component_on (top1_S2 - C)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) q q0"
    using he13(5) hq0 by (by100 blast)
  \<comment> \<open>card {a1, a2', a3, a4'} = 4.\<close>
  have hcard4: "card {a1, a2', a3, a4'} = 4"
  proof -
    have "a1 \<noteq> a2'" using ha2'_ne(1) by (by100 blast)
    moreover have "a1 \<noteq> a3" using hC12(3) by (by100 blast)
    moreover have "a1 \<noteq> a4'" using ha4'_ne(1) by (by100 blast)
    moreover have "a2' \<noteq> a3" using ha2'_ne(2) by (by100 blast)
    moreover have "a2' \<noteq> a4'" using ha2'_ne_a4' by (by100 blast)
    moreover have "a3 \<noteq> a4'" using ha4'_ne(2) by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Prove all K4 intersection conditions.\<close>
  have hC_eq: "C = e12 \<union> e23 \<union> e34 \<union> e41"
    using hC12(1) hC1_split(1) hC2_split(1) by (by100 blast)
  \<comment> \<open>a1 \<notin> e23, a1 \<notin> e34, a3 \<notin> e12, a3 \<notin> e41 (from split structure).\<close>
  have ha1_notin_e23: "a1 \<notin> e23"
  proof
    assume "a1 \<in> e23"
    hence "a1 \<in> e12 \<inter> e23" using hC1_split(5) by (by100 blast)
    hence "a1 = a2'" using hC1_split(2) by (by100 blast)
    thus False using ha2'_ne(1) by (by100 blast)
  qed
  have ha1_notin_e34: "a1 \<notin> e34"
  proof
    assume "a1 \<in> e34"
    hence "a1 \<in> e34 \<inter> e41" using hC2_split(5) by (by100 blast)
    hence "a1 = a4'" using hC2_split(2) by (by100 blast)
    thus False using ha4'_ne(1) by (by100 blast)
  qed
  have ha3_notin_e12: "a3 \<notin> e12"
  proof
    assume "a3 \<in> e12"
    hence "a3 \<in> e12 \<inter> e23" using hC1_split(6) by (by100 blast)
    hence "a3 = a2'" using hC1_split(2) by (by100 blast)
    thus False using ha2'_ne(2) by (by100 blast)
  qed
  have ha3_notin_e41: "a3 \<notin> e41"
  proof
    assume "a3 \<in> e41"
    hence "a3 \<in> e34 \<inter> e41" using hC2_split(6) by (by100 blast)
    hence "a3 = a4'" using hC2_split(2) by (by100 blast)
    thus False using ha4'_ne(2) by (by100 blast)
  qed
  \<comment> \<open>Opposite cycle edges are disjoint.\<close>
  have he12_e34: "e12 \<inter> e34 = {}"
  proof -
    have "e12 \<subseteq> C1" using hC1_split(1) by (by100 blast)
    moreover have "e34 \<subseteq> C2" using hC2_split(1) by (by100 blast)
    ultimately have "e12 \<inter> e34 \<subseteq> C1 \<inter> C2" by (by100 blast)
    also have "\<dots> = {a1, a3}" using hC12(2) by (by100 blast)
    finally have "e12 \<inter> e34 \<subseteq> {a1, a3}" .
    moreover have "a1 \<notin> e12 \<inter> e34" using ha1_notin_e34 by (by100 blast)
    moreover have "a3 \<notin> e12 \<inter> e34" using ha3_notin_e12 by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  have he23_e41: "e23 \<inter> e41 = {}"
  proof -
    have "e23 \<subseteq> C1" using hC1_split(1) by (by100 blast)
    moreover have "e41 \<subseteq> C2" using hC2_split(1) by (by100 blast)
    ultimately have "e23 \<inter> e41 \<subseteq> C1 \<inter> C2" by (by100 blast)
    also have "\<dots> = {a1, a3}" using hC12(2) by (by100 blast)
    finally have "e23 \<inter> e41 \<subseteq> {a1, a3}" .
    moreover have "a1 \<notin> e23 \<inter> e41" using ha1_notin_e23 by (by100 blast)
    moreover have "a3 \<notin> e23 \<inter> e41" using ha3_notin_e41 by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>Adjacent cycle edges share exactly one vertex.\<close>
  have he12_e23: "e12 \<inter> e23 = {a2'}" using hC1_split(2) by (by100 blast)
  have he23_e34: "e23 \<inter> e34 = {a3}"
  proof -
    have "e23 \<subseteq> C1" using hC1_split(1) by (by100 blast)
    have "e34 \<subseteq> C2" using hC2_split(1) by (by100 blast)
    have "e23 \<inter> e34 \<subseteq> C1 \<inter> C2" using \<open>e23 \<subseteq> C1\<close> \<open>e34 \<subseteq> C2\<close> by (by100 blast)
    also have "\<dots> = {a1, a3}" using hC12(2) by (by100 blast)
    finally have hsub: "e23 \<inter> e34 \<subseteq> {a1, a3}" .
    have "a3 \<in> e23 \<inter> e34" using hC1_split(6) hC2_split(6) by (by100 blast)
    moreover have "a1 \<notin> e23" using ha1_notin_e23 by (by100 blast)
    ultimately show ?thesis using hsub by (by100 blast)
  qed
  have he34_e41: "e34 \<inter> e41 = {a4'}" using hC2_split(2) by (by100 blast)
  have he41_e12: "e41 \<inter> e12 = {a1}"
  proof -
    have "e12 \<subseteq> C1" using hC1_split(1) by (by100 blast)
    have "e41 \<subseteq> C2" using hC2_split(1) by (by100 blast)
    have "e41 \<inter> e12 \<subseteq> C1 \<inter> C2" using \<open>e41 \<subseteq> C2\<close> \<open>e12 \<subseteq> C1\<close> by (by100 blast)
    also have "\<dots> = {a1, a3}" using hC12(2) by (by100 blast)
    finally have hsub: "e41 \<inter> e12 \<subseteq> {a1, a3}" .
    have "a1 \<in> e41 \<inter> e12" using hC2_split(5) hC1_split(5) by (by100 blast)
    moreover have "a3 \<notin> e41" using ha3_notin_e41 by (by100 blast)
    ultimately show ?thesis using hsub by (by100 blast)
  qed
  \<comment> \<open>Diagonal e13 intersection with cycle edges.\<close>
  have he13_e12: "e13 \<inter> e12 = {a1}"
  proof -
    have "e12 \<subseteq> C" using hC1_split(1) hC12(1) by (by100 blast)
    hence "e13 \<inter> e12 \<subseteq> e13 \<inter> C" by (by100 blast)
    also have "\<dots> \<subseteq> {a1, a3}" using he13(4) by (by100 blast)
    finally have hsub: "e13 \<inter> e12 \<subseteq> {a1, a3}" .
    have "a1 \<in> e13" using ha1_e13 by (by100 blast)
    hence "a1 \<in> e13 \<inter> e12" using hC1_split(5) by (by100 blast)
    moreover have "a3 \<notin> e12" using ha3_notin_e12 by (by100 blast)
    ultimately show ?thesis using hsub by (by100 blast)
  qed
  have he13_e23: "e13 \<inter> e23 = {a3}"
  proof -
    have "e23 \<subseteq> C" using hC1_split(1) hC12(1) by (by100 blast)
    hence "e13 \<inter> e23 \<subseteq> e13 \<inter> C" by (by100 blast)
    also have "\<dots> \<subseteq> {a1, a3}" using he13(4) by (by100 blast)
    finally have hsub: "e13 \<inter> e23 \<subseteq> {a1, a3}" .
    have "a3 \<in> e13" using ha3_e13 by (by100 blast)
    hence "a3 \<in> e13 \<inter> e23" using hC1_split(6) by (by100 blast)
    moreover have "a1 \<notin> e23" using ha1_notin_e23 by (by100 blast)
    ultimately show ?thesis using hsub by (by100 blast)
  qed
  have he13_e34: "e13 \<inter> e34 = {a3}"
  proof -
    have "e34 \<subseteq> C" using hC2_split(1) hC12(1) by (by100 blast)
    hence "e13 \<inter> e34 \<subseteq> e13 \<inter> C" by (by100 blast)
    also have "\<dots> \<subseteq> {a1, a3}" using he13(4) by (by100 blast)
    finally have hsub: "e13 \<inter> e34 \<subseteq> {a1, a3}" .
    have "a3 \<in> e13 \<inter> e34" using ha3_e13 hC2_split(6) by (by100 blast)
    moreover have "a1 \<notin> e34" using ha1_notin_e34 by (by100 blast)
    ultimately show ?thesis using hsub by (by100 blast)
  qed
  have he13_e41: "e13 \<inter> e41 = {a1}"
  proof -
    have "e41 \<subseteq> C" using hC2_split(1) hC12(1) by (by100 blast)
    hence "e13 \<inter> e41 \<subseteq> e13 \<inter> C" by (by100 blast)
    also have "\<dots> \<subseteq> {a1, a3}" using he13(4) by (by100 blast)
    finally have hsub: "e13 \<inter> e41 \<subseteq> {a1, a3}" .
    have "a1 \<in> e13 \<inter> e41" using ha1_e13 hC2_split(5) by (by100 blast)
    moreover have "a3 \<notin> e41" using ha3_notin_e41 by (by100 blast)
    ultimately show ?thesis using hsub by (by100 blast)
  qed
  \<comment> \<open>Diagonal e24 intersection with cycle edges.\<close>
  have he24_e12: "e24 \<inter> e12 = {a2'}"
  proof -
    have "e12 \<subseteq> C" using hC1_split(1) hC12(1) by (by100 blast)
    hence "e24 \<inter> e12 \<subseteq> e24 \<inter> C" by (by100 blast)
    also have "\<dots> \<subseteq> {a4', a2'}" using he24_C by (by100 blast)
    finally have hsub: "e24 \<inter> e12 \<subseteq> {a4', a2'}" .
    have "a2' \<in> e24 \<inter> e12" using hD13(4) hC1_split(7) unfolding e24_def by (by100 blast)
    moreover have "a4' \<notin> e12"
    proof
      assume "a4' \<in> e12"
      hence "a4' \<in> C1" using hC1_split(1) by (by100 blast)
      thus False using ha4'_notC1 by (by100 blast)
    qed
    ultimately show ?thesis using hsub by (by100 blast)
  qed
  have he24_e23: "e24 \<inter> e23 = {a2'}"
  proof -
    have "e23 \<subseteq> C" using hC1_split(1) hC12(1) by (by100 blast)
    hence "e24 \<inter> e23 \<subseteq> e24 \<inter> C" by (by100 blast)
    also have "\<dots> \<subseteq> {a4', a2'}" using he24_C by (by100 blast)
    finally have hsub: "e24 \<inter> e23 \<subseteq> {a4', a2'}" .
    have "a2' \<in> e24 \<inter> e23" using hD13(4) hC1_split(8) unfolding e24_def by (by100 blast)
    moreover have "a4' \<notin> e23"
    proof
      assume "a4' \<in> e23"
      hence "a4' \<in> C1" using hC1_split(1) by (by100 blast)
      thus False using ha4'_notC1 by (by100 blast)
    qed
    ultimately show ?thesis using hsub by (by100 blast)
  qed
  have he24_e34: "e24 \<inter> e34 = {a4'}"
  proof -
    have "e34 \<subseteq> C" using hC2_split(1) hC12(1) by (by100 blast)
    hence "e24 \<inter> e34 \<subseteq> e24 \<inter> C" by (by100 blast)
    also have "\<dots> \<subseteq> {a4', a2'}" using he24_C by (by100 blast)
    finally have hsub: "e24 \<inter> e34 \<subseteq> {a4', a2'}" .
    have "a4' \<in> e24 \<inter> e34" using hD13(3) hC2_split(8) unfolding e24_def by (by100 blast)
    moreover have "a2' \<notin> e34"
    proof
      assume "a2' \<in> e34"
      hence "a2' \<in> C2" using hC2_split(1) by (by100 blast)
      thus False using ha2'_notC2 by (by100 blast)
    qed
    ultimately show ?thesis using hsub by (by100 blast)
  qed
  have he24_e41: "e24 \<inter> e41 = {a4'}"
  proof -
    have "e41 \<subseteq> C" using hC2_split(1) hC12(1) by (by100 blast)
    hence "e24 \<inter> e41 \<subseteq> e24 \<inter> C" by (by100 blast)
    also have "\<dots> \<subseteq> {a4', a2'}" using he24_C by (by100 blast)
    finally have hsub: "e24 \<inter> e41 \<subseteq> {a4', a2'}" .
    have "a4' \<in> e24 \<inter> e41" using hD13(3) hC2_split(7) unfolding e24_def by (by100 blast)
    moreover have "a2' \<notin> e41"
    proof
      assume "a2' \<in> e41"
      hence "a2' \<in> C2" using hC2_split(1) by (by100 blast)
      thus False using ha2'_notC2 by (by100 blast)
    qed
    ultimately show ?thesis using hsub by (by100 blast)
  qed
  \<comment> \<open>Diagonal intersection.\<close>
  have he13_e24: "e13 \<inter> e24 \<subseteq> {a1, a2', a3, a4'}"
  proof -
    have hcomp_disj: "(e13 - {a1, a3}) \<inter> (e24 - {a2', a4'}) = {}"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain x where "x \<in> e13 - {a1, a3}" "x \<in> e24 - {a2', a4'}" by (by100 blast)
      have "x \<in> top1_S2 - C"
        using \<open>x \<in> e13 - {a1, a3}\<close> he13(2,4) by (by100 blast)
      have "x \<in> top1_S2 - C"
        using \<open>x \<in> e24 - {a2', a4'}\<close> he24_C he24_sub by (by100 blast)
      have "top1_in_same_path_component_on (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) q x"
        using he13(5) \<open>x \<in> e13 - {a1, a3}\<close> by (by100 blast)
      moreover have "top1_in_same_path_component_on (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p x"
        sorry \<comment> \<open>x \<in> D13 interior implies x in component of p.\<close>
      ultimately have "top1_in_same_path_component_on (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p q"
      proof -
        assume hqx: "top1_in_same_path_component_on (top1_S2 - C)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) q x"
        assume hpx: "top1_in_same_path_component_on (top1_S2 - C)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p x"
        have hT_SC: "is_topology_on (top1_S2 - C) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C))"
          by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
        have hxp: "top1_in_same_path_component_on (top1_S2 - C)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) x p"
          by (rule top1_in_same_path_component_on_sym[OF hT_SC hpx])
        have hqp: "top1_in_same_path_component_on (top1_S2 - C)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) q p"
          by (rule top1_in_same_path_component_on_trans[OF hT_SC hqx hxp])
        show ?thesis
          by (rule top1_in_same_path_component_on_sym[OF hT_SC hqp])
      qed
      hence "\<exists>f. top1_is_path_on (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p q f"
        unfolding top1_in_same_path_component_on_def by (by100 blast)
      thus False using assms(5) by (by100 blast)
    qed
    show ?thesis using hcomp_disj by (by100 blast)
  qed
  \<comment> \<open>Vertices subset.\<close>
  have hverts_sub: "{a1, a2', a3, a4'} \<subseteq> top1_S2"
  proof -
    have "a1 \<in> top1_S2" using hC1_split(9,5) by (by100 blast)
    moreover have "a2' \<in> top1_S2" using hC1_split(9,7) by (by100 blast)
    moreover have "a3 \<in> top1_S2" using hC1_split(10,6) by (by100 blast)
    moreover have "a4' \<in> top1_S2" using hC2_split(10,8) by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>Assemble the existential K4 conclusion.\<close>
  have hp0_e24: "p0 \<in> e24 - {a2', a4'}" using hp0 unfolding e24_def by (by100 blast)
  have hq0_e13: "q0 \<in> e13 - {a1, a3}" using hq0 by (by100 blast)
  \<comment> \<open>Adjust endpoint set orderings for the conclusion.\<close>
  have he34_ep': "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a3, a4'}"
  proof -
    have "{a4', a3} = {a3, a4'}" by (by100 blast)
    thus ?thesis using he34_ep by (by100 simp)
  qed
  have he41_ep': "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a4', a1}"
    using he41_ep by (by100 blast)
  show ?thesis
    by (rule exI[of _ a1], rule exI[of _ a2'], rule exI[of _ a3], rule exI[of _ a4'],
        rule exI[of _ e12], rule exI[of _ e23], rule exI[of _ e34], rule exI[of _ e41],
        rule exI[of _ e13], rule exI[of _ e24], rule exI[of _ p0], rule exI[of _ q0])
       (use hcard4 hverts_sub hC1_split(9,10) hC2_split(9,10) he13(2) he24_sub
            hC1_split(3,4) hC2_split(3,4) he13(1) he24_arc
            he12_ep he23_ep he34_ep' he41_ep' he13(3) he24_ep
            he12_e34 he23_e41 he12_e23 he23_e34 he34_e41 he41_e12
            he13_e12 he13_e23 he13_e34 he13_e41 he13_e24
            he24_e12 he24_e23 he24_e34 he24_e41
            hq0_e13 hp0_e24 hp0_comp_p hq0_comp_q hC_eq
        in blast)
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
  obtain a1 a2 a3 a4 e12 e23 e34 e41 e13 e24 p0 q0
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
      "q0 \<in> e13 - {a1, a3}" "p0 \<in> e24 - {a2, a4}"
      "top1_in_same_path_component_on (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p p0"
      "top1_in_same_path_component_on (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) q q0"
    by blast
  \<comment> \<open>Apply Lemma\_65\_1\_fixed with p=q0 on diagonal e13, q=p0 on diagonal e24.
     This gives iso for inclusion C \<rightarrow> S2-{q0}-{p0}.\<close>
  have hiso_p0q0: "top1_group_iso_on
    (top1_fundamental_group_carrier C (subspace_topology top1_S2 top1_S2_topology C) c0)
    (top1_fundamental_group_mul C (subspace_topology top1_S2 top1_S2_topology C) c0)
    (top1_fundamental_group_carrier (top1_S2 - {q0} - {p0})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {q0} - {p0})) c0)
    (top1_fundamental_group_mul (top1_S2 - {q0} - {p0})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {q0} - {p0})) c0)
    (top1_fundamental_group_induced_on C
       (subspace_topology top1_S2 top1_S2_topology C) c0
       (top1_S2 - {q0} - {p0})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {q0} - {p0})) c0 id)"
    by (rule Lemma_65_1_fixed[OF assms(1)
        hK4(1) hK4(3) hK4(4) hK4(5) hK4(6) hK4(7) hK4(8) hK4(9)
        hK4(10) hK4(11) hK4(12) hK4(13) hK4(14) hK4(15)
        hK4(16) hK4(17) hK4(18) hK4(19) hK4(20) hK4(21)
        hK4(22) hK4(23) hK4(24) hK4(25) hK4(26) hK4(27)
        hK4(28) hK4(29) hK4(30) hK4(31) hK4(32)
        hK4(33) hK4(34) hK4(35) hK4(36)
        hK4(37) hK4(38) hK4(2) assms(6)])
  \<comment> \<open>Step 4 (Munkres): Move punctures from (q0,p0) to (q,p) within their path-components.
     Since p0 is in the same component as p, and q0 same as q, the inclusion
     C \<rightarrow> S2-{p}-{q} also induces an isomorphism (by homotopy/translation argument).\<close>
  show ?thesis sorry \<comment> \<open>Munkres Step 4: extend iso from specific (p0,q0) to arbitrary (p,q).\<close>
qed


end
