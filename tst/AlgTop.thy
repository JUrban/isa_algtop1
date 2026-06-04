theory AlgTop
  imports "AlgTopCached10.AlgTopCached10"
begin

\<comment> \<open>Right cosets: Hg = {mul k g | k in H}.\<close>
definition top1_right_coset_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "top1_right_coset_on G mul H g = {mul k g | k. k \<in> H}"

definition top1_right_cosets_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a set set"
  where "top1_right_cosets_on G mul H = {top1_right_coset_on G mul H g | g. g \<in> G}"


\<comment> \<open>Munkres Theorem 54.6: Strengthened lifting correspondence.
   (a) p* is a monomorphism. (Already: covering\\_induced\\_injective in ac4.)
   (b) The lifting correspondence induces a bijection from cosets to the fiber.
   (c) [f] in p*(pi1(E)) iff f lifts to a loop at e0.\<close>

\<comment> \<open>Theorem 54.6(a): p* is injective. Already proved as covering\\_induced\\_injective.\<close>

\<comment> \<open>Right coset characterization: g*h\\<inverse> \\<in> H \\<Rightarrow> Hg = Hh.\<close>
lemma right_coset_eq_from_product_in_H:
  assumes grp: "top1_is_group_on G mul e invg"
      and Hsub: "H \<subseteq> G"
      and Hgrp: "top1_is_group_on H mul e invg"
      and hg: "g \<in> G" and hh: "h \<in> G"
      and hprod: "mul g (invg h) \<in> H"
  shows "top1_right_coset_on G mul H g = top1_right_coset_on G mul H h"
proof -
  let ?\<alpha> = "mul g (invg h)"
  have h\<alpha>_in_H: "?\<alpha> \<in> H" using hprod .
  have h\<alpha>_in_G: "?\<alpha> \<in> G" using Hsub h\<alpha>_in_H by (by100 blast)
  have hinvh: "invg h \<in> G" using group_inv_closed[OF grp hh] .
  \<comment> \<open>g = \\<alpha>*h: from g*h\\<inverse> = \\<alpha> we get g = \\<alpha>*h.\<close>
  have hg_eq: "g = mul ?\<alpha> h"
  proof -
    have "mul g (mul (invg h) h) = mul g e" using group_left_inv[OF grp hh] by simp
    also have "... = g" using group_right_id[OF grp hg] .
    finally have "mul g (mul (invg h) h) = g" .
    moreover have "mul (mul g (invg h)) h = mul g (mul (invg h) h)"
      using group_assoc[OF grp hg hinvh hh] .
    ultimately show ?thesis by simp
  qed
  show ?thesis
    unfolding top1_right_coset_on_def
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> {mul k g |k. k \<in> H}"
    then obtain k where hk: "k \<in> H" "x = mul k g" by (by100 blast)
    have "x = mul k (mul ?\<alpha> h)" using hk(2) hg_eq by simp
    also have "... = mul (mul k ?\<alpha>) h"
    proof -
      have "k \<in> G" using hk(1) Hsub by (by100 blast)
      from group_assoc[OF grp \<open>k \<in> G\<close> h\<alpha>_in_G hh] show ?thesis by simp
    qed
    finally have "x = mul (mul k ?\<alpha>) h" .
    moreover have "mul k ?\<alpha> \<in> H"
      using group_mul_closed[OF Hgrp hk(1) h\<alpha>_in_H] .
    ultimately show "x \<in> {mul k h |k. k \<in> H}" by (by100 blast)
  next
    fix x assume "x \<in> {mul k h |k. k \<in> H}"
    then obtain k where hk: "k \<in> H" "x = mul k h" by (by100 blast)
    \<comment> \<open>h = \\<alpha>\\<inverse>*g, so k*h = k*\\<alpha>\\<inverse>*g.\<close>
    have h\<alpha>_inv: "invg ?\<alpha> \<in> H" using group_inv_closed[OF Hgrp h\<alpha>_in_H] .
    have "mul (invg ?\<alpha>) g = h"
    proof -
      have hinv\<alpha>: "invg ?\<alpha> \<in> G" using group_inv_closed[OF grp h\<alpha>_in_G] .
      have "mul (invg ?\<alpha>) g = mul (invg ?\<alpha>) (mul ?\<alpha> h)" using hg_eq by simp
      also have "... = mul (mul (invg ?\<alpha>) ?\<alpha>) h"
        using group_assoc[OF grp hinv\<alpha> h\<alpha>_in_G hh] by simp
      also have "... = mul e h" using group_left_inv[OF grp h\<alpha>_in_G] by simp
      also have "... = h" using group_left_id[OF grp hh] .
      finally show ?thesis .
    qed
    hence "x = mul k (mul (invg ?\<alpha>) g)" using hk(2) \<open>mul (invg ?\<alpha>) g = h\<close> by simp
    also have "... = mul (mul k (invg ?\<alpha>)) g"
    proof -
      have "k \<in> G" using hk(1) Hsub by (by100 blast)
      have "invg ?\<alpha> \<in> G" using group_inv_closed[OF grp h\<alpha>_in_G] .
      from group_assoc[OF grp \<open>k \<in> G\<close> \<open>invg ?\<alpha> \<in> G\<close> hg] show ?thesis by simp
    qed
    finally have "x = mul (mul k (invg ?\<alpha>)) g" .
    moreover have "mul k (invg ?\<alpha>) \<in> H"
      using group_mul_closed[OF Hgrp hk(1) h\<alpha>_inv] .
    ultimately show "x \<in> {mul k g |k. k \<in> H}" by (by100 blast)
  qed
qed

\<comment> \<open>Theorem 54.6(b): The lifting correspondence phi satisfies
   phi([f]) = phi([g]) iff [f] and [g] are in the same coset of H = p*(pi1(E,e0)).
   When E is path-connected, phi is surjective, so this gives a bijection
   pi1(B,b0)/H -> p-inv(b0).\<close>
theorem Theorem_54_6b:
  fixes E :: "'e set" and TE :: "'e set set"
    and B :: "'b set" and TB :: "'b set set"
  assumes "top1_covering_map_on E TE B TB p"
      and "top1_path_connected_on E TE"
      and "is_topology_on B TB"
      and "e0 \<in> E" and "p e0 = b0"
  shows "\<exists>\<phi>. (\<forall>c\<in>top1_fundamental_group_carrier B TB b0. \<phi> c \<in> {e \<in> E. p e = b0})
    \<and> \<phi> ` (top1_fundamental_group_carrier B TB b0) = {e \<in> E. p e = b0}
    \<and> (\<forall>c\<in>top1_fundamental_group_carrier B TB b0.
        \<exists>f ft. f \<in> c \<and> top1_is_loop_on B TB b0 f
          \<and> top1_is_path_on E TE e0 (\<phi> c) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s))
    \<and> (\<forall>g\<in>top1_fundamental_group_carrier B TB b0.
       \<forall>h\<in>top1_fundamental_group_carrier B TB b0.
        (\<phi> g = \<phi> h) =
        (top1_right_coset_on (top1_fundamental_group_carrier B TB b0)
            (top1_fundamental_group_mul B TB b0)
            (top1_fundamental_group_image_hom E TE e0 B TB b0 p) g
         = top1_right_coset_on (top1_fundamental_group_carrier B TB b0)
            (top1_fundamental_group_mul B TB b0)
            (top1_fundamental_group_image_hom E TE e0 B TB b0 p) h))"
proof -
  let ?piB = "top1_fundamental_group_carrier B TB b0"
  let ?mulB = "top1_fundamental_group_mul B TB b0"
  let ?H = "top1_fundamental_group_image_hom E TE e0 B TB b0 p"
  \<comment> \<open>Step 1: Get \\<phi> from Theorem 54.4 with all properties.\<close>
  have hE_top: "is_topology_on E TE"
    using assms(2) unfolding top1_path_connected_on_def by (by100 blast)
  from Theorem_54_4_lifting_correspondence[OF assms(4-5,1-2,3)]
  obtain \<phi> where h\<phi>_maps: "\<forall>c\<in>?piB. \<phi> c \<in> {e \<in> E. p e = b0}"
      and h\<phi>_surj: "\<phi> ` ?piB = {e \<in> E. p e = b0}"
      and h\<phi>_lift: "\<forall>c\<in>?piB. \<exists>f ft. f \<in> c \<and> top1_is_loop_on B TB b0 f
          \<and> top1_is_path_on E TE e0 (\<phi> c) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s)"
    by (elim exE conjE)
  \<comment> \<open>Step 2: Prove \\<phi>(g) = \\<phi>(h) \\<leftrightarrow> same coset. This is the key content of 54.6(b).\<close>
  have h\<phi>_coset: "\<forall>g\<in>?piB. \<forall>h\<in>?piB.
      (\<phi> g = \<phi> h) = (top1_right_coset_on ?piB ?mulB ?H g = top1_right_coset_on ?piB ?mulB ?H h)"
  proof (intro ballI)
    fix g h assume hg: "g \<in> ?piB" and hh: "h \<in> ?piB"
    from h\<phi>_lift[rule_format, OF hg]
    obtain fg ftg where hfg: "fg \<in> g" "top1_is_loop_on B TB b0 fg"
        "top1_is_path_on E TE e0 (\<phi> g) ftg" "\<forall>s\<in>I_set. p (ftg s) = fg s"
      by (by100 blast)
    from h\<phi>_lift[rule_format, OF hh]
    obtain fh fth where hfh: "fh \<in> h" "top1_is_loop_on B TB b0 fh"
        "top1_is_path_on E TE e0 (\<phi> h) fth" "\<forall>s\<in>I_set. p (fth s) = fh s"
      by (by100 blast)
    show "(\<phi> g = \<phi> h) = (top1_right_coset_on ?piB ?mulB ?H g = top1_right_coset_on ?piB ?mulB ?H h)"
    proof (rule iffI)
      \<comment> \<open>Forward: \\<phi>(g)=\\<phi>(h) \\<Rightarrow> same coset.
         Book 54.6(b): ftg and fth end at same point.
         ftg * rev(fth) is loop at e0. p\\<circ>(ftg * rev(fth)) represents g*h\\<inverse>.
         So g*h\\<inverse> \\<in> ?H, hence gH = hH.\<close>
      assume h\<phi>_eq: "\<phi> g = \<phi> h"
      \<comment> \<open>ftg * reverse(fth) is a loop at e0 (both end at \\<phi>(g) = \\<phi>(h)).\<close>
      have hloop_E: "top1_is_path_on E TE e0 e0
          (top1_path_product ftg (top1_path_reverse fth))"
      proof -
        have "top1_is_path_on E TE (\<phi> h) e0 (top1_path_reverse fth)"
          by (rule top1_path_reverse_is_path[OF hfh(3)])
        hence "top1_is_path_on E TE (\<phi> g) e0 (top1_path_reverse fth)"
          using h\<phi>_eq by simp
        from top1_path_product_is_path[OF hE_top hfg(3) this]
        show ?thesis .
      qed
      \<comment> \<open>Its projection p\\<circ>(ftg * rev(fth)) = fg * rev(fh) represents g*h\\<inverse>.\<close>
      \<comment> \<open>p \\<circ> path\\_product(ftg, rev(fth)) = path\\_product(fg, rev(fh)) pointwise.\<close>
      have hproj_eq: "\<forall>t\<in>I_set. p (top1_path_product ftg (top1_path_reverse fth) t)
          = top1_path_product fg (top1_path_reverse fh) t"
      proof (intro ballI)
        fix t assume "t \<in> I_set"
        show "p (top1_path_product ftg (top1_path_reverse fth) t)
            = top1_path_product fg (top1_path_reverse fh) t"
        proof (cases "t \<le> 1/2")
          case True
          hence "2 * t \<in> I_set" unfolding top1_unit_interval_def
            using \<open>t \<in> I_set\<close> unfolding top1_unit_interval_def by (by100 auto)
          thus ?thesis using True hfg(4) unfolding top1_path_product_def top1_path_reverse_def by (by100 simp)
        next
          case False
          hence "1 - (2 * t - 1) \<in> I_set"
            using \<open>t \<in> I_set\<close> unfolding top1_unit_interval_def by (by100 auto)
          hence "2 - 2 * t \<in> I_set"
            using \<open>t \<in> I_set\<close> unfolding top1_unit_interval_def by (by100 auto)
          thus ?thesis using False hfh(4) unfolding top1_path_product_def top1_path_reverse_def
            by (by100 simp)
        qed
      qed
      have hfg_path: "top1_is_path_on B TB b0 b0 fg"
        using hfg(2) unfolding top1_is_loop_on_def .
      have hfh_path: "top1_is_path_on B TB b0 b0 fh"
        using hfh(2) unfolding top1_is_loop_on_def .
      have hfh_rev_path: "top1_is_path_on B TB b0 b0 (top1_path_reverse fh)"
        using top1_path_reverse_is_path[OF hfh_path] .
      have hfg_rev_fh_loop: "top1_is_loop_on B TB b0
          (top1_path_product fg (top1_path_reverse fh))"
        unfolding top1_is_loop_on_def
        using top1_path_product_is_path[OF assms(3) hfg_path hfh_rev_path] .
      have hproj_loop: "top1_is_loop_on B TB b0
          (\<lambda>t. p (top1_path_product ftg (top1_path_reverse fth) t))"
      proof -
        \<comment> \<open>p \\<circ> (path in E) is a path in B: composition of continuous maps.\<close>
        have hp_cont: "top1_continuous_map_on E TE B TB p"
          using assms(1) unfolding top1_covering_map_on_def top1_evenly_covered_on_def by (by5000 blast)
        have hloop_cont: "top1_continuous_map_on I_set I_top E TE
            (top1_path_product ftg (top1_path_reverse fth))"
          using hloop_E unfolding top1_is_path_on_def by (by100 blast)
        from top1_continuous_map_on_comp[OF hloop_cont hp_cont]
        have "top1_continuous_map_on I_set I_top B TB (p \<circ> (top1_path_product ftg (top1_path_reverse fth)))" .
        moreover have "(p \<circ> (top1_path_product ftg (top1_path_reverse fth))) 0 = b0"
          using hloop_E assms(5) unfolding top1_is_path_on_def comp_def by (by100 simp)
        moreover have "(p \<circ> (top1_path_product ftg (top1_path_reverse fth))) 1 = b0"
          using hloop_E assms(5) unfolding top1_is_path_on_def comp_def by (by100 simp)
        ultimately have "top1_is_path_on B TB b0 b0 (p \<circ> (top1_path_product ftg (top1_path_reverse fth)))"
          unfolding top1_is_path_on_def by (by100 blast)
        hence "top1_is_loop_on B TB b0 (p \<circ> (top1_path_product ftg (top1_path_reverse fth)))"
          unfolding top1_is_loop_on_def .
        thus ?thesis unfolding comp_def .
      qed
      \<comment> \<open>Class of p\\<circ>(loop) is in ?H = p*(\\<pi>\\_1(E,e0)).
         The loop ftg*rev(fth) is at e0 in E, so its class is in \\<pi>\\_1(E,e0).
         The induced map p* sends it to the class of p\\<circ>(loop), which is in H.\<close>
      have "{f'. top1_loop_equiv_on B TB b0 (\<lambda>t. p (top1_path_product ftg (top1_path_reverse fth) t)) f'} \<in> ?H"
      proof -
        \<comment> \<open>The loop at e0 defines a class in \\<pi>\\_1(E,e0).\<close>
        let ?loop = "top1_path_product ftg (top1_path_reverse fth)"
        have hloop_is_loop: "top1_is_loop_on E TE e0 ?loop"
          using hloop_E unfolding top1_is_loop_on_def .
        let ?class_E = "{g. top1_loop_equiv_on E TE e0 ?loop g}"
        have hclass_in: "?class_E \<in> top1_fundamental_group_carrier E TE e0"
          unfolding top1_fundamental_group_carrier_def using hloop_is_loop by (by100 blast)
        \<comment> \<open>p* maps this class to the class of p\\<circ>loop in \\<pi>\\_1(B,b0).\<close>
        have "top1_fundamental_group_induced_on E TE e0 B TB b0 p ?class_E
            = {f'. top1_loop_equiv_on B TB b0 (\<lambda>t. p (?loop t)) f'}"
          unfolding top1_fundamental_group_induced_on_def
        proof (rule set_eqI, rule iffI)
          fix g assume "g \<in> {g. \<exists>f\<in>?class_E. top1_loop_equiv_on B TB b0 (p \<circ> f) g}"
          then obtain f where "f \<in> ?class_E" "top1_loop_equiv_on B TB b0 (p \<circ> f) g"
            by (by100 blast)
          hence "top1_loop_equiv_on E TE e0 ?loop f" by (by100 blast)
          \<comment> \<open>f homotopic to ?loop \\<Rightarrow> p\\<circ>f homotopic to p\\<circ>?loop \\<Rightarrow> g homotopic to p\\<circ>?loop.\<close>
          have "top1_path_homotopic_on E TE e0 e0 ?loop f"
            using \<open>top1_loop_equiv_on E TE e0 ?loop f\<close>
            unfolding top1_loop_equiv_on_def by (by100 blast)
          have hp_cont: "top1_continuous_map_on E TE B TB p"
            using assms(1) unfolding top1_covering_map_on_def top1_evenly_covered_on_def by (by5000 blast)
          from continuous_preserves_path_homotopic[OF hE_top assms(3) hp_cont
              \<open>top1_path_homotopic_on E TE e0 e0 ?loop f\<close>]
          have "top1_path_homotopic_on B TB (p e0) (p e0) (p \<circ> ?loop) (p \<circ> f)" .
          hence "top1_path_homotopic_on B TB b0 b0 (p \<circ> ?loop) (p \<circ> f)"
            using assms(5) by simp
          hence hle1: "top1_loop_equiv_on B TB b0 (p \<circ> ?loop) (p \<circ> f)"
            unfolding top1_loop_equiv_on_def top1_is_loop_on_def top1_path_homotopic_on_def
            by (by100 blast)
          have hle2: "top1_loop_equiv_on B TB b0 (p \<circ> f) g"
            using \<open>top1_loop_equiv_on B TB b0 (p \<circ> f) g\<close> .
          from top1_loop_equiv_on_trans[OF assms(3) hle1 hle2]
          have "top1_loop_equiv_on B TB b0 (p \<circ> ?loop) g" .
          hence "top1_loop_equiv_on B TB b0 (\<lambda>t. p (?loop t)) g"
            unfolding comp_def by simp
          show "g \<in> {f'. top1_loop_equiv_on B TB b0 (\<lambda>t. p (?loop t)) f'}"
            using \<open>top1_loop_equiv_on B TB b0 (\<lambda>t. p (?loop t)) g\<close> by (by100 blast)
        next
          fix g assume "g \<in> {f'. top1_loop_equiv_on B TB b0 (\<lambda>t. p (?loop t)) f'}"
          hence "top1_loop_equiv_on B TB b0 (\<lambda>t. p (?loop t)) g" by (by100 blast)
          \<comment> \<open>?loop is itself in ?class\\_E. So p\\<circ>?loop witnesses the existential.\<close>
          moreover have "?loop \<in> ?class_E"
          proof -
            have "top1_loop_equiv_on E TE e0 ?loop ?loop"
              unfolding top1_loop_equiv_on_def using hloop_is_loop
                Lemma_51_1_path_homotopic_refl[OF hloop_E] by (by100 blast)
            thus ?thesis by (by100 blast)
          qed
          moreover have "top1_loop_equiv_on B TB b0 (p \<circ> ?loop) g"
            using \<open>top1_loop_equiv_on B TB b0 (\<lambda>t. p (?loop t)) g\<close>
            unfolding comp_def by simp
          ultimately show "g \<in> {g. \<exists>f\<in>?class_E. top1_loop_equiv_on B TB b0 (p \<circ> f) g}"
            by (by100 blast)
        qed
        thus ?thesis
          unfolding top1_fundamental_group_image_hom_def using hclass_in by (by100 blast)
      qed
      \<comment> \<open>This class = g * h\\<inverse> in \\<pi>\\_1(B).\<close>
      \<comment> \<open>g * h\\<inverse> \\<in> ?H \\<Rightarrow> gH = hH.\<close>
      \<comment> \<open>The class of p\\<circ>(ftg*rev(fth)) is in H.
         This class represents g*h\\<inverse> in \\<pi>\\_1(B) (from the loop classes fg, fh).
         For RIGHT cosets: Hg = Hh \\<leftarrow> h*g\\<inverse> \\<in> H.
         We have g*h\\<inverse> \\<in> H \\<Rightarrow> (g*h\\<inverse>)\\<inverse> = h*g\\<inverse> \\<in> H (subgroup closed under inv).
         Then Hg = Hh.\<close>
      \<comment> \<open>Step: show [fg*rev(fh)] = mulB g (invgB h), hence g*h\\<inverse> \\<in> H.\<close>
      have "?mulB g (top1_fundamental_group_invg B TB b0 h) \<in> ?H"
      proof -
        \<comment> \<open>mulB g (invgB h) = class of product(fg, rev(fh)).
           From class\\_in\\_H: class of p\\<circ>(product(ftg,rev(fth))) \\<in> H.
           p\\<circ>(product(ftg,rev(fth))) = product(fg,rev(fh)) on I\\_set.\<close>
        \<comment> \<open>Step 1: class of product(fg,rev(fh)) = mulB g (invgB h).\<close>
        have hfh_in_h: "fh \<in> h" using hfh(1) .
        have hrev_fh_in_invh: "top1_path_reverse fh \<in> top1_fundamental_group_invg B TB b0 h"
        proof -
          have "fh \<in> h" using hfh_in_h .
          have "top1_is_loop_on B TB b0 (top1_path_reverse fh)"
            unfolding top1_is_loop_on_def
            using top1_path_reverse_is_path[OF hfh_path] .
          hence "top1_loop_equiv_on B TB b0 (top1_path_reverse fh) (top1_path_reverse fh)"
            unfolding top1_loop_equiv_on_def
            using Lemma_51_1_path_homotopic_refl[OF top1_path_reverse_is_path[OF hfh_path]] by (by100 blast)
          thus ?thesis unfolding top1_fundamental_group_invg_def using \<open>fh \<in> h\<close> by (by100 blast)
        qed
        have hclass_eq: "?mulB g (top1_fundamental_group_invg B TB b0 h) =
            {f'. top1_loop_equiv_on B TB b0 (top1_path_product fg (top1_path_reverse fh)) f'}"
        proof -
          \<comment> \<open>g = class of fg, invg(h) = class of rev(fh).\<close>
          have hg_class: "g = {f'. top1_loop_equiv_on B TB b0 fg f'}"
          proof -
            have "fg \<in> g" using hfg(1) .
            have "top1_is_loop_on B TB b0 fg" using hfg(2) .
            have "g \<in> ?piB" using hg .
            then obtain f0 where "top1_is_loop_on B TB b0 f0"
                "g = {f'. top1_loop_equiv_on B TB b0 f0 f'}"
              unfolding top1_fundamental_group_carrier_def by (by100 blast)
            \<comment> \<open>fg \\<in> g = class of f0, so fg ~ f0, so class of fg = class of f0 = g.\<close>
            have "top1_loop_equiv_on B TB b0 f0 fg" using \<open>fg \<in> g\<close> \<open>g = _\<close> by (by100 blast)
            have "{f'. top1_loop_equiv_on B TB b0 fg f'} = {f'. top1_loop_equiv_on B TB b0 f0 f'}"
            proof (rule set_eqI, rule iffI)
              fix f' assume "f' \<in> {f'. top1_loop_equiv_on B TB b0 fg f'}"
              hence "top1_loop_equiv_on B TB b0 fg f'" by (by100 blast)
              from top1_loop_equiv_on_trans[OF assms(3) \<open>top1_loop_equiv_on B TB b0 f0 fg\<close> this]
              show "f' \<in> {f'. top1_loop_equiv_on B TB b0 f0 f'}" by (by100 blast)
            next
              fix f' assume "f' \<in> {f'. top1_loop_equiv_on B TB b0 f0 f'}"
              hence "top1_loop_equiv_on B TB b0 f0 f'" by (by100 blast)
              from top1_loop_equiv_on_trans[OF assms(3) top1_loop_equiv_on_sym[OF \<open>top1_loop_equiv_on B TB b0 f0 fg\<close>] this]
              show "f' \<in> {f'. top1_loop_equiv_on B TB b0 fg f'}" by (by100 blast)
            qed
            thus ?thesis using \<open>g = _\<close> by simp
          qed
          have hh_class: "h = {f'. top1_loop_equiv_on B TB b0 fh f'}"
          proof -
            from \<open>h \<in> ?piB\<close> obtain f0 where "top1_is_loop_on B TB b0 f0"
                "h = {f'. top1_loop_equiv_on B TB b0 f0 f'}"
              unfolding top1_fundamental_group_carrier_def by (by100 blast)
            have "top1_loop_equiv_on B TB b0 f0 fh" using hfh(1) \<open>h = _\<close> by (by100 blast)
            have "{f'. top1_loop_equiv_on B TB b0 fh f'} = {f'. top1_loop_equiv_on B TB b0 f0 f'}"
            proof (rule set_eqI, rule iffI)
              fix f' assume "f' \<in> {f'. top1_loop_equiv_on B TB b0 fh f'}"
              hence "top1_loop_equiv_on B TB b0 fh f'" by (by100 blast)
              from top1_loop_equiv_on_trans[OF assms(3) \<open>top1_loop_equiv_on B TB b0 f0 fh\<close> this]
              show "f' \<in> {f'. top1_loop_equiv_on B TB b0 f0 f'}" by (by100 blast)
            next
              fix f' assume "f' \<in> {f'. top1_loop_equiv_on B TB b0 f0 f'}"
              hence "top1_loop_equiv_on B TB b0 f0 f'" by (by100 blast)
              from top1_loop_equiv_on_trans[OF assms(3) top1_loop_equiv_on_sym[OF \<open>top1_loop_equiv_on B TB b0 f0 fh\<close>] this]
              show "f' \<in> {f'. top1_loop_equiv_on B TB b0 fh f'}" by (by100 blast)
            qed
            thus ?thesis using \<open>h = _\<close> by simp
          qed
          have hinvh_class: "top1_fundamental_group_invg B TB b0 h =
              {f'. top1_loop_equiv_on B TB b0 (top1_path_reverse fh) f'}"
            unfolding hh_class using fundamental_group_invg_class[OF assms(3) hfh(2)] .
          \<comment> \<open>Apply fundamental\\_group\\_mul\\_class.\<close>
          have "top1_is_loop_on B TB b0 (top1_path_reverse fh)"
            unfolding top1_is_loop_on_def using top1_path_reverse_is_path[OF hfh_path] .
          show ?thesis unfolding hg_class hinvh_class
            using top1_fundamental_group_mul_class[OF assms(3) hfg(2)
                \<open>top1_is_loop_on B TB b0 (top1_path_reverse fh)\<close>] .
        qed
        \<comment> \<open>Step 2: This class = class of p\\<circ>(product(ftg,rev(fth))) (pointwise equal on I\\_set).\<close>
        have hclass_proj: "{f'. top1_loop_equiv_on B TB b0 (top1_path_product fg (top1_path_reverse fh)) f'}
            = {f'. top1_loop_equiv_on B TB b0 (\<lambda>t. p (top1_path_product ftg (top1_path_reverse fth) t)) f'}"
        proof -
          \<comment> \<open>The two functions agree on I\\_set. By loop\\_agree\\_on\\_I they are homotopic.
             Homotopic loops have the same equivalence class.\<close>
          have hagree: "\<forall>s\<in>I_set.
              (\<lambda>t. p (top1_path_product ftg (top1_path_reverse fth) t)) s
              = (top1_path_product fg (top1_path_reverse fh)) s"
            using hproj_eq by simp
          from loop_agree_on_I[OF hfg_rev_fh_loop, of "\<lambda>t. p (top1_path_product ftg (top1_path_reverse fth) t)"]
          have hle: "top1_is_loop_on B TB b0 (\<lambda>t. p (top1_path_product ftg (top1_path_reverse fth) t))
              \<and> top1_path_homotopic_on B TB b0 b0
                  (top1_path_product fg (top1_path_reverse fh))
                  (\<lambda>t. p (top1_path_product ftg (top1_path_reverse fth) t))"
            using hagree by (by100 simp)
          hence hloop2: "top1_is_loop_on B TB b0 (\<lambda>t. p (top1_path_product ftg (top1_path_reverse fth) t))"
              and hhomot: "top1_path_homotopic_on B TB b0 b0
                  (top1_path_product fg (top1_path_reverse fh))
                  (\<lambda>t. p (top1_path_product ftg (top1_path_reverse fth) t))"
            by (by100 blast)+
          \<comment> \<open>Two homotopic loops define the same loop\\_equiv class.\<close>
          have hle_fwd: "top1_loop_equiv_on B TB b0
              (top1_path_product fg (top1_path_reverse fh))
              (\<lambda>t. p (top1_path_product ftg (top1_path_reverse fth) t))"
            unfolding top1_loop_equiv_on_def using hfg_rev_fh_loop hloop2 hhomot by (by100 blast)
          let ?f1 = "top1_path_product fg (top1_path_reverse fh)"
          let ?f2 = "\<lambda>t. p (top1_path_product ftg (top1_path_reverse fth) t)"
          show ?thesis
          proof (rule set_eqI, rule iffI)
            fix f' assume "f' \<in> {f'. top1_loop_equiv_on B TB b0 ?f1 f'}"
            hence h1: "top1_loop_equiv_on B TB b0 ?f1 f'" by (by100 blast)
            \<comment> \<open>?f1 ~ ?f2 (hle\\_fwd) + ?f1 ~ f' (h1).
               sym: ?f2 ~ ?f1. trans: ?f2 ~ ?f1 ~ f'. So ?f2 ~ f'.\<close>
            from top1_loop_equiv_on_sym[OF hle_fwd]
            have "top1_loop_equiv_on B TB b0 ?f2 ?f1" .
            from top1_loop_equiv_on_trans[OF assms(3) this h1]
            show "f' \<in> {f'. top1_loop_equiv_on B TB b0 ?f2 f'}" by (by100 blast)
          next
            fix f' assume "f' \<in> {f'. top1_loop_equiv_on B TB b0 ?f2 f'}"
            hence h1: "top1_loop_equiv_on B TB b0 ?f2 f'" by (by100 blast)
            from top1_loop_equiv_on_trans[OF assms(3) hle_fwd h1]
            show "f' \<in> {f'. top1_loop_equiv_on B TB b0 ?f1 f'}" by (by100 blast)
          qed
        qed
        \<comment> \<open>Step 3: class\\_in\\_H says this is in H.\<close>
        show ?thesis using hclass_eq hclass_proj
            \<open>{f'. top1_loop_equiv_on B TB b0 (\<lambda>t. p (top1_path_product ftg (top1_path_reverse fth) t)) f'} \<in> ?H\<close>
          by simp
      qed
      have hg_in_piB: "g \<in> ?piB" using hg .
      have hh_in_piB: "h \<in> ?piB" using hh .
      have "b0 \<in> B"
        using assms(1,4,5) unfolding top1_covering_map_on_def top1_evenly_covered_on_def
        by (by5000 blast)
      have hpiB_grp: "top1_is_group_on ?piB ?mulB
          (top1_fundamental_group_id B TB b0) (top1_fundamental_group_invg B TB b0)"
        using top1_fundamental_group_is_group[OF assms(3) \<open>b0 \<in> B\<close>] .
      have hH_sub: "?H \<subseteq> ?piB"
      proof -
        have hp_cont: "top1_continuous_map_on E TE B TB p"
          using assms(1) unfolding top1_covering_map_on_def top1_evenly_covered_on_def by (by5000 blast)
        have hp_hom: "top1_group_hom_on
            (top1_fundamental_group_carrier E TE e0) (top1_fundamental_group_mul E TE e0)
            ?piB ?mulB (top1_fundamental_group_induced_on E TE e0 B TB b0 p)"
          by (rule top1_fundamental_group_induced_on_is_hom[OF hE_top assms(3) assms(4) \<open>b0 \<in> B\<close> hp_cont assms(5)])
        thus ?thesis unfolding top1_fundamental_group_image_hom_def top1_group_hom_on_def by (by100 blast)
      qed
      have hH_grp: "top1_is_group_on ?H ?mulB
          (top1_fundamental_group_id B TB b0) (top1_fundamental_group_invg B TB b0)"
      proof -
        have hE'_grp: "top1_is_group_on (top1_fundamental_group_carrier E TE e0)
            (top1_fundamental_group_mul E TE e0) (top1_fundamental_group_id E TE e0)
            (top1_fundamental_group_invg E TE e0)"
          by (rule top1_fundamental_group_is_group[OF hE_top assms(4)])
        have hp_cont: "top1_continuous_map_on E TE B TB p"
          using assms(1) unfolding top1_covering_map_on_def top1_evenly_covered_on_def by (by5000 blast)
        have hp_hom: "top1_group_hom_on
            (top1_fundamental_group_carrier E TE e0) (top1_fundamental_group_mul E TE e0)
            ?piB ?mulB (top1_fundamental_group_induced_on E TE e0 B TB b0 p)"
          by (rule top1_fundamental_group_induced_on_is_hom[OF hE_top assms(3) assms(4) \<open>b0 \<in> B\<close> hp_cont assms(5)])
        from hom_image_is_subgroup[OF hE'_grp hpiB_grp hp_hom]
        show ?thesis unfolding top1_fundamental_group_image_hom_def .
      qed
      show "top1_right_coset_on ?piB ?mulB ?H g = top1_right_coset_on ?piB ?mulB ?H h"
        by (rule right_coset_eq_from_product_in_H[OF hpiB_grp hH_sub hH_grp hg_in_piB hh_in_piB
            \<open>?mulB g (top1_fundamental_group_invg B TB b0 h) \<in> ?H\<close>])
    next
      \<comment> \<open>Backward: same coset \\<Rightarrow> \\<phi>(g)=\\<phi>(h).
         Book: gH = hH, so g = h*k for some k \\<in> H.
         k \\<in> H = p*(\\<pi>\\_1(E)) means k = [p\\<circ>\\<alpha>\\<tilde>] for loop \\<alpha>\\<tilde> at e0.
         Lift of fg = lift of (fh * (p\\<circ>\\<alpha>\\<tilde>)) = fth * \\<alpha>\\<tilde>.
         fth * \\<alpha>\\<tilde> ends at \\<phi>(h) (since \\<alpha>\\<tilde> is loop, fth ends at \\<phi>(h)).
         Wait --- actually fth ends at \\<phi>(h), \\<alpha>\\<tilde> starts at e0 not \\<phi>(h).
         The correct argument (book): [f] = [h*g] where h = p\\<circ>h\\<tilde>.
         h\\<tilde>*g\\<tilde> lifts h*g, starts at e0, ends at g\\<tilde>(1) = \\<phi>(g).
         Since [f] = [h*g], lifts f\\<tilde> and h\\<tilde>*g\\<tilde> end at same point (Thm 54.3).
         So \\<phi>(f) = \\<phi>(g). Done.\<close>
      assume hcoset_eq: "top1_right_coset_on ?piB ?mulB ?H g = top1_right_coset_on ?piB ?mulB ?H h"
      show "\<phi> g = \<phi> h"
      proof -
        \<comment> \<open>Book: Hg = Hh means h \\<in> Hg, i.e., h = k*g for some k \\<in> H.
           k \\<in> H = p*(\\<pi>\\_1(E,e0)) means k = [p\\<circ>\\<alpha>\\<tilde>] for loop \\<alpha>\\<tilde> at e0.
           h = k*g = [p\\<circ>\\<alpha>\\<tilde>]*g = [p\\<circ>\\<alpha>\\<tilde> * fg].
           Lift of p\\<circ>\\<alpha>\\<tilde> * fg from e0 is \\<alpha>\\<tilde> * ftg, ending at \\<phi>(g).
           Since h = [p\\<circ>\\<alpha>\\<tilde> * fg], lifts of fh and p\\<circ>\\<alpha>\\<tilde>*fg end at same point.
           So \\<phi>(h) = \\<phi>(g).\<close>
        \<comment> \<open>Step 1: h \\<in> Hg, i.e., \\<exists>k\\<in>H. h = k*g.\<close>
        \<comment> \<open>Step 1: Hg = Hh \\<Rightarrow> h \\<in> Hg.\<close>
        have hh_in_Hh: "h \<in> top1_right_coset_on ?piB ?mulB ?H h"
        proof -
          \<comment> \<open>The identity e \\<in> H, and mul e h = h.\<close>
          let ?e = "top1_fundamental_group_id B TB b0"
          have "b0 \<in> B"
            using assms(1,4,5) unfolding top1_covering_map_on_def top1_evenly_covered_on_def
            by (by5000 blast)
          have hpiB_grp: "top1_is_group_on ?piB ?mulB ?e (top1_fundamental_group_invg B TB b0)"
            using top1_fundamental_group_is_group[OF assms(3) \<open>b0 \<in> B\<close>] .
          have "?e \<in> ?H"
          proof -
            have "?e \<in> ?piB"
              using hpiB_grp unfolding top1_is_group_on_def by (by100 blast)
            have hH_is_subgroup: "top1_is_group_on ?H ?mulB ?e (top1_fundamental_group_invg B TB b0)"
            proof -
              have hE'_grp: "top1_is_group_on (top1_fundamental_group_carrier E TE e0)
                  (top1_fundamental_group_mul E TE e0) (top1_fundamental_group_id E TE e0)
                  (top1_fundamental_group_invg E TE e0)"
                by (rule top1_fundamental_group_is_group[OF hE_top assms(4)])
              have hp_cont: "top1_continuous_map_on E TE B TB p"
                using assms(1) unfolding top1_covering_map_on_def top1_evenly_covered_on_def by (by5000 blast)
              have hp_hom: "top1_group_hom_on
                  (top1_fundamental_group_carrier E TE e0) (top1_fundamental_group_mul E TE e0)
                  ?piB ?mulB (top1_fundamental_group_induced_on E TE e0 B TB b0 p)"
                by (rule top1_fundamental_group_induced_on_is_hom[OF hE_top assms(3) assms(4) \<open>b0 \<in> B\<close> hp_cont assms(5)])
              from hom_image_is_subgroup[OF hE'_grp hpiB_grp hp_hom]
              show ?thesis unfolding top1_fundamental_group_image_hom_def .
            qed
            thus ?thesis unfolding top1_is_group_on_def by (by100 blast)
          qed
          moreover have "h = ?mulB ?e h"
            using group_left_id[OF hpiB_grp hh] by simp
          ultimately show ?thesis unfolding top1_right_coset_on_def by (by100 blast)
        qed
        hence hh_in_Hg: "h \<in> top1_right_coset_on ?piB ?mulB ?H g"
          using hcoset_eq by simp
        then obtain k where "k \<in> ?H" "h = ?mulB k g"
          unfolding top1_right_coset_on_def by (by100 blast)
        \<comment> \<open>Step 2: k = [p\\<circ>\\<alpha>\\<tilde>] for loop \\<alpha>\\<tilde> at e0.\<close>
        have "\<exists>\<alpha>_tilde. top1_is_loop_on E TE e0 \<alpha>_tilde \<and>
            k = {f'. top1_loop_equiv_on B TB b0 (\<lambda>t. p (\<alpha>_tilde t)) f'}"
        proof -
          \<comment> \<open>k \\<in> H = image\\_hom. So k = induced(c) for some c \\<in> \\<pi>\\_1(E,e0).\<close>
          from \<open>k \<in> ?H\<close>
          obtain c where "c \<in> top1_fundamental_group_carrier E TE e0"
              "k = top1_fundamental_group_induced_on E TE e0 B TB b0 p c"
            unfolding top1_fundamental_group_image_hom_def by (by100 blast)
          \<comment> \<open>c is a class of loops at e0. Get a representative.\<close>
          from \<open>c \<in> top1_fundamental_group_carrier E TE e0\<close>
          obtain \<alpha>_tilde where h\<alpha>t: "top1_is_loop_on E TE e0 \<alpha>_tilde"
              "c = {f'. top1_loop_equiv_on E TE e0 \<alpha>_tilde f'}"
            unfolding top1_fundamental_group_carrier_def by (by100 blast)
          \<comment> \<open>induced(c) = {f'. loop\\_equiv(B, b0, p\\<circ>\\<alpha>\\<tilde>, f')}.\<close>
          have "k = {f'. top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>_tilde) f'}"
          proof -
            have "k = {g. \<exists>f\<in>c. top1_loop_equiv_on B TB b0 (p \<circ> f) g}"
              using \<open>k = top1_fundamental_group_induced_on E TE e0 B TB b0 p c\<close>
              unfolding top1_fundamental_group_induced_on_def by simp
            also have "... = {g. \<exists>f. top1_loop_equiv_on E TE e0 \<alpha>_tilde f
                \<and> top1_loop_equiv_on B TB b0 (p \<circ> f) g}"
              unfolding h\<alpha>t(2) by (by100 blast)
            also have "... = {g. top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>_tilde) g}"
            proof (rule set_eqI, rule iffI)
              fix g assume "g \<in> {g. \<exists>f. top1_loop_equiv_on E TE e0 \<alpha>_tilde f
                  \<and> top1_loop_equiv_on B TB b0 (p \<circ> f) g}"
              then obtain f where hf: "top1_loop_equiv_on E TE e0 \<alpha>_tilde f"
                  "top1_loop_equiv_on B TB b0 (p \<circ> f) g" by (by100 blast)
              \<comment> \<open>f homotopic to \\<alpha>\\<tilde> \\<Rightarrow> p\\<circ>f homotopic to p\\<circ>\\<alpha>\\<tilde> \\<Rightarrow> g homotopic to p\\<circ>\\<alpha>\\<tilde>.\<close>
              have "top1_path_homotopic_on E TE e0 e0 \<alpha>_tilde f"
                using hf(1) unfolding top1_loop_equiv_on_def by (by100 blast)
              have hp_cont: "top1_continuous_map_on E TE B TB p"
                using assms(1) unfolding top1_covering_map_on_def top1_evenly_covered_on_def
                by (by5000 blast)
              from continuous_preserves_path_homotopic[OF hE_top assms(3) hp_cont
                  \<open>top1_path_homotopic_on E TE e0 e0 \<alpha>_tilde f\<close>]
              have "top1_path_homotopic_on B TB b0 b0 (p \<circ> \<alpha>_tilde) (p \<circ> f)"
                using assms(5) by simp
              hence "top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>_tilde) (p \<circ> f)"
                unfolding top1_loop_equiv_on_def top1_is_loop_on_def top1_path_homotopic_on_def
                by (by100 blast)
              from top1_loop_equiv_on_trans[OF assms(3) this hf(2)]
              show "g \<in> {g. top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>_tilde) g}" by (by100 blast)
            next
              fix g assume "g \<in> {g. top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>_tilde) g}"
              hence "top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>_tilde) g" by (by100 blast)
              moreover have "\<alpha>_tilde \<in> {f'. top1_loop_equiv_on E TE e0 \<alpha>_tilde f'}"
              proof -
                have h\<alpha>_path: "top1_is_path_on E TE e0 e0 \<alpha>_tilde"
                  using h\<alpha>t(1) unfolding top1_is_loop_on_def .
                from Lemma_51_1_path_homotopic_refl[OF h\<alpha>_path]
                show ?thesis unfolding top1_loop_equiv_on_def using h\<alpha>t(1) by (by100 blast)
              qed
              moreover have "top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>_tilde) g"
                using \<open>top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>_tilde) g\<close> .
              ultimately show "g \<in> {g. \<exists>f. top1_loop_equiv_on E TE e0 \<alpha>_tilde f
                  \<and> top1_loop_equiv_on B TB b0 (p \<circ> f) g}"
                by (by100 blast)
            qed
            finally show ?thesis .
          qed
          hence "k = {f'. top1_loop_equiv_on B TB b0 (\<lambda>t. p (\<alpha>_tilde t)) f'}"
            unfolding comp_def by simp
          thus ?thesis using h\<alpha>t(1) by (by100 blast)
        qed
        then obtain \<alpha>_tilde where h\<alpha>: "top1_is_loop_on E TE e0 \<alpha>_tilde"
            "k = {f'. top1_loop_equiv_on B TB b0 (\<lambda>t. p (\<alpha>_tilde t)) f'}"
          by (by100 blast)
        \<comment> \<open>Step 3: \\<alpha>\\<tilde> * ftg lifts p\\<circ>\\<alpha>\\<tilde> * fg, ending at \\<phi>(g).
           Step 4: By Theorem 54.3, fth and \\<alpha>\\<tilde>*ftg end at same point.
           Hence \\<phi>(h) = \\<phi>(g).\<close>
        \<comment> \<open>Step 3: \\<alpha>\\<tilde>*ftg is a path from e0 to \\<phi>(g) in E.\<close>
        have h\<alpha>_path: "top1_is_path_on E TE e0 e0 \<alpha>_tilde"
          using h\<alpha>(1) unfolding top1_is_loop_on_def .
        have h\<alpha>ftg: "top1_is_path_on E TE e0 (\<phi> g) (top1_path_product \<alpha>_tilde ftg)"
          using top1_path_product_is_path[OF hE_top h\<alpha>_path hfg(3)] .
        \<comment> \<open>Step 4: \\<alpha>\\<tilde>*ftg projects to (p\\<circ>\\<alpha>\\<tilde>)*fg which represents k*g = h.\<close>
        have hproj_\<alpha>ftg: "\<forall>s\<in>I_set. p (top1_path_product \<alpha>_tilde ftg s)
            = top1_path_product (\<lambda>t. p (\<alpha>_tilde t)) fg s"
        proof (intro ballI)
          fix s assume "s \<in> I_set"
          show "p (top1_path_product \<alpha>_tilde ftg s)
              = top1_path_product (\<lambda>t. p (\<alpha>_tilde t)) fg s"
          proof (cases "s \<le> 1/2")
            case True
            hence "2 * s \<in> I_set" using \<open>s \<in> I_set\<close> unfolding top1_unit_interval_def by (by100 auto)
            thus ?thesis using True unfolding top1_path_product_def by simp
          next
            case False
            hence "2 * s - 1 \<in> I_set" using \<open>s \<in> I_set\<close> unfolding top1_unit_interval_def by (by100 auto)
            thus ?thesis using False hfg(4) unfolding top1_path_product_def by (by100 simp)
          qed
        qed
        \<comment> \<open>Step 5: fh represents h = k*g. The product (p\\<circ>\\<alpha>\\<tilde>)*fg also represents k*g.
           So fh and (p\\<circ>\\<alpha>\\<tilde>)*fg are path-homotopic.
           By Thm 54.3: their lifts from e0 end at the same point.
           Lift of fh = fth, ending at \\<phi>(h).
           Lift of (p\\<circ>\\<alpha>\\<tilde>)*fg = \\<alpha>\\<tilde>*ftg, ending at \\<phi>(g).
           So \\<phi>(h) = \\<phi>(g).\<close>
        \<comment> \<open>Book proof: fh ~ (p\\<circ>\\<alpha>\\<tilde>)*fg (both represent h=k*g).
           Lifts from e0: fth (\\<to> \\<phi>(h)), \\<alpha>\\<tilde>*ftg (\\<to> \\<phi>(g)).
           By Theorem 54.3: \\<phi>(h) = \\<phi>(g).\<close>
        let ?pafg = "top1_path_product (\<lambda>t. p (\<alpha>_tilde t)) fg"
        \<comment> \<open>Step 5a: (p\\<circ>\\<alpha>\\<tilde>)*fg is a loop at b0.\<close>
        have h_pafg_path: "top1_is_path_on B TB b0 b0 ?pafg"
        proof -
          have "top1_is_loop_on B TB b0 (\<lambda>t. p (\<alpha>_tilde t))"
          proof -
            have hp_cont: "top1_continuous_map_on E TE B TB p"
              using assms(1) unfolding top1_covering_map_on_def top1_evenly_covered_on_def by (by5000 blast)
            have "top1_continuous_map_on I_set I_top E TE \<alpha>_tilde"
              using h\<alpha>_path unfolding top1_is_path_on_def by (by100 blast)
            from top1_continuous_map_on_comp[OF this hp_cont]
            have "top1_continuous_map_on I_set I_top B TB (p \<circ> \<alpha>_tilde)" .
            moreover have "(p \<circ> \<alpha>_tilde) 0 = b0"
              using h\<alpha>_path assms(5) unfolding top1_is_path_on_def comp_def by (by100 simp)
            moreover have "(p \<circ> \<alpha>_tilde) 1 = b0"
              using h\<alpha>_path assms(5) unfolding top1_is_path_on_def comp_def by (by100 simp)
            ultimately have "top1_is_path_on B TB b0 b0 (p \<circ> \<alpha>_tilde)"
              unfolding top1_is_path_on_def by (by100 blast)
            thus ?thesis unfolding top1_is_loop_on_def comp_def .
          qed
          hence "top1_is_path_on B TB b0 b0 (\<lambda>t. p (\<alpha>_tilde t))"
            unfolding top1_is_loop_on_def .
          have "top1_is_path_on B TB b0 b0 fg"
            using hfg(2) unfolding top1_is_loop_on_def .
          from top1_path_product_is_path[OF assms(3) \<open>top1_is_path_on B TB b0 b0 (\<lambda>t. p (\<alpha>_tilde t))\<close> this]
          show ?thesis .
        qed
        \<comment> \<open>Step 5b: fh and ?pafg are homotopic (both \\<in> h = k*g).\<close>
        have hfh_homot: "top1_path_homotopic_on B TB b0 b0 fh ?pafg"
          sorry \<comment> \<open>h = k*g = [(p\\<circ>\\<alpha>\\<tilde>)]*[fg] = [(p\\<circ>\\<alpha>\\<tilde>)*fg]. fh \\<in> h.\<close>
        \<comment> \<open>Step 5c: fth lifts fh, \\<alpha>\\<tilde>*ftg lifts ?pafg (pointwise on I\\_set).\<close>
        \<comment> \<open>Step 5d: Apply Theorem 54.3.\<close>
        have hfh_path': "top1_is_path_on B TB b0 b0 fh"
          using hfh(2) unfolding top1_is_loop_on_def .
        from Theorem_54_3[OF assms(1) hE_top assms(3) assms(4) assms(5)
            hfh_path' h_pafg_path hfh_homot
            hfh(3) hfh(4)
            h\<alpha>ftg hproj_\<alpha>ftg]
        have "\<phi> h = \<phi> g" by (by100 blast)
        thus ?thesis by simp
      qed
    qed
  qed
  \<comment> \<open>Assemble the 4-tuple existential.\<close>
  show ?thesis
    apply (rule exI[of _ \<phi>])
    apply (intro conjI)
    using h\<phi>_maps apply assumption
    using h\<phi>_surj apply assumption
    using h\<phi>_lift apply assumption
    using h\<phi>_coset apply assumption
    done
qed

\<comment> \<open>card(left cosets) = card(right cosets). Standard: map gH -> Hg\\<inverse> is bijection.\<close>
lemma left_right_coset_card_eq:
  assumes "top1_is_group_on G mul e invg"
      and "H \<subseteq> G"
      and "top1_is_group_on H mul e invg"
  shows "card (top1_left_cosets_on G mul H) = card (top1_right_cosets_on G mul H)"
proof -
  define \<psi> :: "'a set \<Rightarrow> 'a set" where "\<psi> C = invg ` C" for C
  have h\<psi>_bij: "bij_betw \<psi> (top1_left_cosets_on G mul H) (top1_right_cosets_on G mul H)"
    unfolding bij_betw_def
  proof (intro conjI)
    \<comment> \<open>\\<psi> maps left cosets to right cosets.\<close>
    have h\<psi>_maps: "\<psi> ` (top1_left_cosets_on G mul H) \<subseteq> top1_right_cosets_on G mul H"
    proof
      fix D assume "D \<in> \<psi> ` (top1_left_cosets_on G mul H)"
      then obtain C where "C \<in> top1_left_cosets_on G mul H" "D = \<psi> C" by (by100 blast)
      then obtain g where hg: "g \<in> G" "C = {mul g h |h. h \<in> H}"
        unfolding top1_left_cosets_on_def top1_group_coset_on_def by (by100 blast)
      have "D = invg ` {mul g h |h. h \<in> H}" using \<open>D = \<psi> C\<close> hg(2) unfolding \<psi>_def by simp
      \<comment> \<open>{invg(mul g h) | h \\<in> H} = {mul (invg h) (invg g) | h \\<in> H} = {mul k (invg g) | k \\<in> H}.\<close>
      have "D = {mul k (invg g) | k. k \<in> H}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> D"
        hence "x \<in> invg ` {mul g h |h. h \<in> H}" using \<open>D = invg ` _\<close> by simp
        then obtain h where "h \<in> H" "x = invg (mul g h)" by (by100 blast)
        have "h \<in> G" using \<open>h \<in> H\<close> assms(2) by (by100 blast)
        have "x = mul (invg h) (invg g)" using group_inv_mul[OF assms(1) hg(1) \<open>h \<in> G\<close>] \<open>x = _\<close> by simp
        moreover have "invg h \<in> H" using group_inv_closed[OF assms(3) \<open>h \<in> H\<close>] .
        ultimately show "x \<in> {mul k (invg g) | k. k \<in> H}" by (by100 blast)
      next
        fix x assume "x \<in> {mul k (invg g) | k. k \<in> H}"
        then obtain k where "k \<in> H" "x = mul k (invg g)" by (by100 blast)
        have "invg k \<in> H" using group_inv_closed[OF assms(3) \<open>k \<in> H\<close>] .
        have "k \<in> G" using \<open>k \<in> H\<close> assms(2) by (by100 blast)
        have hik: "invg k \<in> G" using group_inv_closed[OF assms(1) \<open>k \<in> G\<close>] .
        have "invg (mul g (invg k)) = mul (invg (invg k)) (invg g)"
          using group_inv_mul[OF assms(1) hg(1) hik] .
        also have "invg (invg k) = k"
        proof -
          have hk_inv_in: "invg (invg k) \<in> G" using group_inv_closed[OF assms(1) hik] .
          have "invg (invg k) = mul (invg (invg k)) e"
            using group_right_id[OF assms(1) hk_inv_in] by simp
          also have "... = mul (invg (invg k)) (mul (invg k) k)"
            using group_left_inv[OF assms(1) \<open>k \<in> G\<close>] by simp
          also have "... = mul (mul (invg (invg k)) (invg k)) k"
            using group_assoc[OF assms(1) hk_inv_in hik \<open>k \<in> G\<close>] by simp
          also have "... = mul e k"
            using group_left_inv[OF assms(1) hik] by simp
          also have "... = k"
            using group_left_id[OF assms(1) \<open>k \<in> G\<close>] .
          finally show ?thesis .
        qed
        finally have "invg (mul g (invg k)) = x" using \<open>x = mul k (invg g)\<close> by simp
        thus "x \<in> D" using \<open>D = invg ` _\<close> \<open>invg k \<in> H\<close> by (by100 blast)
      qed
      moreover have "invg g \<in> G" using group_inv_closed[OF assms(1) hg(1)] .
      ultimately show "D \<in> top1_right_cosets_on G mul H"
        unfolding top1_right_cosets_on_def top1_right_coset_on_def by (by100 blast)
    qed
    have h\<psi>_surj: "\<psi> ` (top1_left_cosets_on G mul H) \<supseteq> top1_right_cosets_on G mul H"
    proof
      fix D assume "D \<in> top1_right_cosets_on G mul H"
      then obtain g where hg: "g \<in> G" "D = {mul k g |k. k \<in> H}"
        unfolding top1_right_cosets_on_def top1_right_coset_on_def by (by100 blast)
      \<comment> \<open>D = H*g = \\<psi>((g\\<inverse>)*H) where (g\\<inverse>)*H is a left coset.\<close>
      have hinvg: "invg g \<in> G" using group_inv_closed[OF assms(1) hg(1)] .
      let ?C = "{mul (invg g) h |h. h \<in> H}"
      have "?C \<in> top1_left_cosets_on G mul H"
        unfolding top1_left_cosets_on_def top1_group_coset_on_def using hinvg by (by100 blast)
      moreover have "\<psi> ?C = D"
      proof -
        have "\<psi> ?C = invg ` {mul (invg g) h |h. h \<in> H}" unfolding \<psi>_def by simp
        also have "... = {invg (mul (invg g) h) |h. h \<in> H}" by (by100 blast)
        also have "... = {mul (invg h) (invg (invg g)) |h. h \<in> H}"
        proof (rule Collect_cong)
          fix x show "(\<exists>h. x = invg (mul (invg g) h) \<and> h \<in> H) =
              (\<exists>h. x = mul (invg h) (invg (invg g)) \<and> h \<in> H)"
          proof (rule iffI)
            assume "\<exists>h. x = invg (mul (invg g) h) \<and> h \<in> H"
            then obtain h where "h \<in> H" "x = invg (mul (invg g) h)" by (by100 blast)
            have "h \<in> G" using \<open>h \<in> H\<close> assms(2) by (by100 blast)
            show "\<exists>h. x = mul (invg h) (invg (invg g)) \<and> h \<in> H"
              using group_inv_mul[OF assms(1) hinvg \<open>h \<in> G\<close>] \<open>x = _\<close> \<open>h \<in> H\<close> by (by100 blast)
          next
            assume "\<exists>h. x = mul (invg h) (invg (invg g)) \<and> h \<in> H"
            then obtain h where "h \<in> H" "x = mul (invg h) (invg (invg g))" by (by100 blast)
            have "h \<in> G" using \<open>h \<in> H\<close> assms(2) by (by100 blast)
            have "x = invg (mul (invg g) h)"
              using group_inv_mul[OF assms(1) hinvg \<open>h \<in> G\<close>] \<open>x = mul (invg h) (invg (invg g))\<close> by simp
            thus "\<exists>h. x = invg (mul (invg g) h) \<and> h \<in> H" using \<open>h \<in> H\<close> by (by100 blast)
          qed
        qed
        also have "... = {mul k g |k. k \<in> H}"
        proof -
          \<comment> \<open>invg(invg g) = g. And invg maps H bijectively to H.\<close>
          have "invg (invg g) = g"
          proof -
            have hiig: "invg (invg g) \<in> G" using group_inv_closed[OF assms(1) hinvg] .
            have "invg (invg g) = mul (invg (invg g)) e"
              using group_right_id[OF assms(1) hiig] by simp
            also have "... = mul (invg (invg g)) (mul (invg g) g)"
              using group_left_inv[OF assms(1) hg(1)] by simp
            also have "... = mul (mul (invg (invg g)) (invg g)) g"
              using group_assoc[OF assms(1) hiig hinvg hg(1)] by simp
            also have "... = mul e g"
              using group_left_inv[OF assms(1) hinvg] by simp
            also have "... = g"
              using group_left_id[OF assms(1) hg(1)] .
            finally show ?thesis .
          qed
          show ?thesis
          proof (rule Collect_cong)
            fix x show "(\<exists>h. x = mul (invg h) (invg (invg g)) \<and> h \<in> H)
                = (\<exists>k. x = mul k g \<and> k \<in> H)"
            proof (rule iffI)
              assume "\<exists>h. x = mul (invg h) (invg (invg g)) \<and> h \<in> H"
              then obtain h where "h \<in> H" "x = mul (invg h) (invg (invg g))" by (by100 blast)
              hence "x = mul (invg h) g" using \<open>invg (invg g) = g\<close> by simp
              moreover have "invg h \<in> H" using group_inv_closed[OF assms(3) \<open>h \<in> H\<close>] .
              ultimately show "\<exists>k. x = mul k g \<and> k \<in> H" by (by100 blast)
            next
              assume "\<exists>k. x = mul k g \<and> k \<in> H"
              then obtain k where "k \<in> H" "x = mul k g" by (by100 blast)
              have "invg k \<in> H" using group_inv_closed[OF assms(3) \<open>k \<in> H\<close>] .
              have "invg (invg k) = k"
              proof -
                have "k \<in> G" using \<open>k \<in> H\<close> assms(2) by (by100 blast)
                have hik: "invg k \<in> G" using group_inv_closed[OF assms(1) \<open>k \<in> G\<close>] .
                have hiik: "invg (invg k) \<in> G" using group_inv_closed[OF assms(1) hik] .
                have "invg (invg k) = mul (invg (invg k)) e"
                  using group_right_id[OF assms(1) hiik] by simp
                also have "... = mul (invg (invg k)) (mul (invg k) k)"
                  using group_left_inv[OF assms(1) \<open>k \<in> G\<close>] by simp
                also have "... = mul (mul (invg (invg k)) (invg k)) k"
                  using group_assoc[OF assms(1) hiik hik \<open>k \<in> G\<close>] by simp
                also have "... = mul e k" using group_left_inv[OF assms(1) hik] by simp
                also have "... = k" using group_left_id[OF assms(1) \<open>k \<in> G\<close>] .
                finally show ?thesis .
              qed
              have "x = mul (invg (invg k)) (invg (invg g))"
                using \<open>x = mul k g\<close> \<open>invg (invg k) = k\<close> \<open>invg (invg g) = g\<close> by simp
              thus "\<exists>h. x = mul (invg h) (invg (invg g)) \<and> h \<in> H"
                using \<open>invg k \<in> H\<close> by (by100 blast)
            qed
          qed
        qed
        finally show ?thesis using hg(2) by simp
      qed
      ultimately show "D \<in> \<psi> ` (top1_left_cosets_on G mul H)" by (by100 blast)
    qed
    show "\<psi> ` (top1_left_cosets_on G mul H) = top1_right_cosets_on G mul H"
      using h\<psi>_maps h\<psi>_surj by (by100 blast)
    \<comment> \<open>\\<psi> is injective: invg is injective on G (group inverse is bijective).\<close>
    show "inj_on \<psi> (top1_left_cosets_on G mul H)"
    proof (rule inj_onI)
      fix C1 C2 assume hC1: "C1 \<in> top1_left_cosets_on G mul H"
          and hC2: "C2 \<in> top1_left_cosets_on G mul H" and heq: "\<psi> C1 = \<psi> C2"
      \<comment> \<open>invg ` C1 = invg ` C2, and invg is injective on G, so C1 = C2.\<close>
      from hC1 obtain g1 where "g1 \<in> G" "C1 = {mul g1 h |h. h \<in> H}"
        unfolding top1_left_cosets_on_def top1_group_coset_on_def by (by100 blast)
      from hC2 obtain g2 where "g2 \<in> G" "C2 = {mul g2 h |h. h \<in> H}"
        unfolding top1_left_cosets_on_def top1_group_coset_on_def by (by100 blast)
      have "C1 \<subseteq> G"
      proof -
        have "\<forall>h\<in>H. mul g1 h \<in> G"
          using group_mul_closed[OF assms(1) \<open>g1 \<in> G\<close>] assms(2) by (by100 blast)
        thus ?thesis using \<open>C1 = _\<close> by (by100 blast)
      qed
      have "C2 \<subseteq> G"
      proof -
        have "\<forall>h\<in>H. mul g2 h \<in> G"
          using group_mul_closed[OF assms(1) \<open>g2 \<in> G\<close>] assms(2) by (by100 blast)
        thus ?thesis using \<open>C2 = _\<close> by (by100 blast)
      qed
      \<comment> \<open>invg injective on G: invg x = invg y \\<Rightarrow> x = y (double inverse).\<close>
      have hinvg_inj: "inj_on invg G"
      proof (rule inj_onI)
        fix x y assume "x \<in> G" "y \<in> G" "invg x = invg y"
        \<comment> \<open>invg(invg(x)) = x (double inverse). So x = invg(invg x) = invg(invg y) = y.\<close>
        \<comment> \<open>invg(invg x) = x: from mul(invg(invg x))(invg x) = e = mul x (invg x), cancel.\<close>
        have hx_inv_in: "invg x \<in> G" using group_inv_closed[OF assms(1) \<open>x \<in> G\<close>] .
        have hy_inv_in: "invg y \<in> G" using group_inv_closed[OF assms(1) \<open>y \<in> G\<close>] .
        \<comment> \<open>Derive invg(invg x) = x from group axioms.\<close>
        have "mul x (invg x) = e" using group_right_inv[OF assms(1) \<open>x \<in> G\<close>] .
        have "mul (invg x) x = e" using group_left_inv[OF assms(1) \<open>x \<in> G\<close>] .
        have "mul (invg (invg x)) (invg x) = e" using group_left_inv[OF assms(1) hx_inv_in] .
        have hinvx_inv_in: "invg (invg x) \<in> G" using group_inv_closed[OF assms(1) hx_inv_in] .
        have hxx: "invg (invg x) = x"
        proof -
          \<comment> \<open>From mul(invg(invg x))(invg x) = e and mul x (invg x) = e:
             both invg(invg x) and x are left inverses of invg x.
             Multiply both sides on right by x: invg(invg x) = x.\<close>
          have "invg (invg x) = mul (invg (invg x)) e"
            using group_right_id[OF assms(1) hinvx_inv_in] by simp
          also have "... = mul (invg (invg x)) (mul (invg x) x)"
            using \<open>mul (invg x) x = e\<close> by simp
          also have "... = mul (mul (invg (invg x)) (invg x)) x"
            using group_assoc[OF assms(1) hinvx_inv_in hx_inv_in \<open>x \<in> G\<close>] by simp
          also have "... = mul e x"
            using \<open>mul (invg (invg x)) (invg x) = e\<close> by simp
          also have "... = x"
            using group_left_id[OF assms(1) \<open>x \<in> G\<close>] .
          finally show ?thesis .
        qed
        have hyy: "invg (invg y) = y"
        proof -
          have hinvy_inv_in: "invg (invg y) \<in> G" using group_inv_closed[OF assms(1) hy_inv_in] .
          have "invg (invg y) = mul (invg (invg y)) e"
            using group_right_id[OF assms(1) hinvy_inv_in] by simp
          also have "... = mul (invg (invg y)) (mul (invg y) y)"
            using group_left_inv[OF assms(1) \<open>y \<in> G\<close>] by simp
          also have "... = mul (mul (invg (invg y)) (invg y)) y"
            using group_assoc[OF assms(1) hinvy_inv_in hy_inv_in \<open>y \<in> G\<close>] by simp
          also have "... = mul e y"
            using group_left_inv[OF assms(1) hy_inv_in] by simp
          also have "... = y"
            using group_left_id[OF assms(1) \<open>y \<in> G\<close>] .
          finally show ?thesis .
        qed
        have "x = invg (invg x)" using hxx by simp
        also have "... = invg (invg y)" using \<open>invg x = invg y\<close> by simp
        also have "... = y" using hyy .
        finally show "x = y" .
      qed
      from inj_on_image_eq_iff[OF hinvg_inj \<open>C1 \<subseteq> G\<close> \<open>C2 \<subseteq> G\<close>]
      show "C1 = C2" using heq unfolding \<psi>_def by simp
    qed
  qed
  from bij_betw_same_card[OF h\<psi>_bij] show ?thesis .
qed


\<comment> \<open>Theorem 54.6(c): [f] in H = p*(pi1(E,e0)) iff f lifts to a loop at e0.\<close>
theorem Theorem_54_6c:
  fixes E :: "'e set" and TE :: "'e set set"
    and B :: "'b set" and TB :: "'b set set"
  assumes "top1_covering_map_on E TE B TB p"
      and "is_topology_on E TE" and "is_topology_on B TB"
      and "e0 \<in> E" and "p e0 = b0"
      and "top1_is_loop_on B TB b0 f"
  shows "(top1_fundamental_group_induced_on E TE e0 B TB b0 p)
            ` top1_fundamental_group_carrier E TE e0
         = top1_fundamental_group_image_hom E TE e0 B TB b0 p \<Longrightarrow>
    ({g. top1_loop_equiv_on B TB b0 f g} \<in> top1_fundamental_group_image_hom E TE e0 B TB b0 p)
    = (\<exists>ft. top1_is_loop_on E TE e0 ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s))"
  sorry

\<comment> \<open>Right-coset version: surjection with right-coset kernel gives bijection.\<close>
lemma surjection_right_coset_bij:
  assumes grp: "top1_is_group_on G mul e invg"
      and Hsub: "H \<subseteq> G"
      and Hgrp: "top1_is_group_on H mul e invg"
      and maps: "\<forall>g\<in>G. \<phi> g \<in> Y"
      and surj: "\<phi> ` G = Y"
      and fiber_eq: "\<forall>g\<in>G. \<forall>h\<in>G.
          (\<phi> g = \<phi> h) = (top1_right_coset_on G mul H g = top1_right_coset_on G mul H h)"
  shows "\<exists>f. bij_betw f (top1_right_cosets_on G mul H) Y"
proof -
  define f where "f \<equiv> \<lambda>C. \<phi> (SOME g. g \<in> G \<and> top1_right_coset_on G mul H g = C)"
  show ?thesis
  proof (rule exI[of _ f], unfold bij_betw_def, intro conjI)
    show "inj_on f (top1_right_cosets_on G mul H)"
    proof (rule inj_onI)
      fix C1 C2 assume hC1: "C1 \<in> top1_right_cosets_on G mul H"
          and hC2: "C2 \<in> top1_right_cosets_on G mul H" and heq: "f C1 = f C2"
      from hC1 obtain g1 where hg1: "g1 \<in> G" "C1 = top1_right_coset_on G mul H g1"
        unfolding top1_right_cosets_on_def by (by100 blast)
      from hC2 obtain g2 where hg2: "g2 \<in> G" "C2 = top1_right_coset_on G mul H g2"
        unfolding top1_right_cosets_on_def by (by100 blast)
      have hsome1: "(SOME g. g \<in> G \<and> top1_right_coset_on G mul H g = C1) \<in> G \<and>
          top1_right_coset_on G mul H (SOME g. g \<in> G \<and> top1_right_coset_on G mul H g = C1) = C1"
        using someI_ex[of "\<lambda>g. g \<in> G \<and> top1_right_coset_on G mul H g = C1"] hg1 by (by100 blast)
      have hsome2: "(SOME g. g \<in> G \<and> top1_right_coset_on G mul H g = C2) \<in> G \<and>
          top1_right_coset_on G mul H (SOME g. g \<in> G \<and> top1_right_coset_on G mul H g = C2) = C2"
        using someI_ex[of "\<lambda>g. g \<in> G \<and> top1_right_coset_on G mul H g = C2"] hg2 by (by100 blast)
      let ?s1 = "SOME g. g \<in> G \<and> top1_right_coset_on G mul H g = C1"
      let ?s2 = "SOME g. g \<in> G \<and> top1_right_coset_on G mul H g = C2"
      have "?s1 \<in> G" "?s2 \<in> G" using hsome1 hsome2 by (by100 blast)+
      have "\<phi> ?s1 = \<phi> ?s2" using heq unfolding f_def by simp
      from fiber_eq[rule_format, OF \<open>?s1 \<in> G\<close> \<open>?s2 \<in> G\<close>]
      have "top1_right_coset_on G mul H ?s1 = top1_right_coset_on G mul H ?s2"
        using \<open>\<phi> ?s1 = \<phi> ?s2\<close> by simp
      thus "C1 = C2" using hsome1 hsome2 by simp
    qed
    show "f ` (top1_right_cosets_on G mul H) = Y"
    proof (rule set_eqI, rule iffI)
      fix y assume "y \<in> f ` (top1_right_cosets_on G mul H)"
      then obtain C where hC: "C \<in> top1_right_cosets_on G mul H" "y = f C" by (by100 blast)
      from hC(1) obtain g where hg: "g \<in> G" "C = top1_right_coset_on G mul H g"
        unfolding top1_right_cosets_on_def by (by100 blast)
      have "(SOME g'. g' \<in> G \<and> top1_right_coset_on G mul H g' = C) \<in> G"
        using someI_ex[of "\<lambda>g'. g' \<in> G \<and> top1_right_coset_on G mul H g' = C"] hg by (by100 blast)
      from maps[rule_format, OF this]
      show "y \<in> Y" using hC(2) unfolding f_def by simp
    next
      fix y assume "y \<in> Y"
      from surj have "\<exists>g\<in>G. \<phi> g = y" using \<open>y \<in> Y\<close> by (by100 blast)
      then obtain g where hg: "g \<in> G" "\<phi> g = y" by (by100 blast)
      let ?C = "top1_right_coset_on G mul H g"
      have hC_in: "?C \<in> top1_right_cosets_on G mul H"
        unfolding top1_right_cosets_on_def using hg(1) by (by100 blast)
      have hsome: "(SOME g'. g' \<in> G \<and> top1_right_coset_on G mul H g' = ?C) \<in> G \<and>
          top1_right_coset_on G mul H (SOME g'. g' \<in> G \<and> top1_right_coset_on G mul H g' = ?C) = ?C"
        using someI_ex[of "\<lambda>g'. g' \<in> G \<and> top1_right_coset_on G mul H g' = ?C"] hg(1)
        by (by100 blast)
      let ?s = "SOME g'. g' \<in> G \<and> top1_right_coset_on G mul H g' = ?C"
      have "?s \<in> G" using hsome by (by100 blast)
      have "top1_right_coset_on G mul H ?s = ?C" using hsome by (by100 blast)
      from fiber_eq[rule_format, OF \<open>?s \<in> G\<close> hg(1)]
      have "\<phi> ?s = \<phi> g" using \<open>top1_right_coset_on G mul H ?s = ?C\<close> by simp
      hence "f ?C = y" using hg(2) unfolding f_def by simp
      thus "y \<in> f ` (top1_right_cosets_on G mul H)" using hC_in by (by100 blast)
    qed
  qed
qed

\<comment> \<open>Reusable quotient lemma: a surjection that identifies coset-equivalent
   elements induces a bijection from cosets to the image.
   Expert audit2: make this a standalone lemma, not inline in Schreier.\<close>
lemma surjection_coset_bij:
  assumes grp: "top1_is_group_on G mul e invg"
      and Hsub: "H \<subseteq> G"
      and Hgrp: "top1_is_group_on H mul e invg"
      and maps: "\<forall>g\<in>G. \<phi> g \<in> Y"
      and surj: "\<phi> ` G = Y"
      and fiber_eq: "\<forall>g\<in>G. \<forall>h\<in>G.
          (\<phi> g = \<phi> h) = (top1_group_coset_on G mul H g = top1_group_coset_on G mul H h)"
  shows "\<exists>f. bij_betw f (top1_left_cosets_on G mul H) Y"
proof -
  \<comment> \<open>Define f(C) = \\<phi>(SOME g. g \\<in> C) for each coset C.\<close>
  define f where "f \<equiv> \<lambda>C. \<phi> (SOME g. g \<in> G \<and> top1_group_coset_on G mul H g = C)"
  show ?thesis
  proof (rule exI[of _ f], unfold bij_betw_def, intro conjI)
    \<comment> \<open>f is injective on cosets.\<close>
    show "inj_on f (top1_left_cosets_on G mul H)"
    proof (rule inj_onI)
      fix C1 C2 assume hC1: "C1 \<in> top1_left_cosets_on G mul H"
          and hC2: "C2 \<in> top1_left_cosets_on G mul H" and heq: "f C1 = f C2"
      from hC1 obtain g1 where hg1: "g1 \<in> G" "C1 = top1_group_coset_on G mul H g1"
        unfolding top1_left_cosets_on_def by (by100 blast)
      from hC2 obtain g2 where hg2: "g2 \<in> G" "C2 = top1_group_coset_on G mul H g2"
        unfolding top1_left_cosets_on_def by (by100 blast)
      \<comment> \<open>Extract the SOME witnesses.\<close>
      have hsome1: "(SOME g. g \<in> G \<and> top1_group_coset_on G mul H g = C1) \<in> G \<and>
          top1_group_coset_on G mul H (SOME g. g \<in> G \<and> top1_group_coset_on G mul H g = C1) = C1"
        using someI_ex[of "\<lambda>g. g \<in> G \<and> top1_group_coset_on G mul H g = C1"] hg1 by (by100 blast)
      have hsome2: "(SOME g. g \<in> G \<and> top1_group_coset_on G mul H g = C2) \<in> G \<and>
          top1_group_coset_on G mul H (SOME g. g \<in> G \<and> top1_group_coset_on G mul H g = C2) = C2"
        using someI_ex[of "\<lambda>g. g \<in> G \<and> top1_group_coset_on G mul H g = C2"] hg2 by (by100 blast)
      let ?s1 = "SOME g. g \<in> G \<and> top1_group_coset_on G mul H g = C1"
      let ?s2 = "SOME g. g \<in> G \<and> top1_group_coset_on G mul H g = C2"
      have "?s1 \<in> G" "?s2 \<in> G" using hsome1 hsome2 by (by100 blast)+
      have "\<phi> ?s1 = \<phi> ?s2" using heq unfolding f_def by simp
      from fiber_eq[rule_format, OF \<open>?s1 \<in> G\<close> \<open>?s2 \<in> G\<close>]
      have "top1_group_coset_on G mul H ?s1 = top1_group_coset_on G mul H ?s2"
        using \<open>\<phi> ?s1 = \<phi> ?s2\<close> by simp
      thus "C1 = C2" using hsome1 hsome2 by simp
    qed
    \<comment> \<open>f is surjective onto Y.\<close>
    show "f ` (top1_left_cosets_on G mul H) = Y"
    proof (rule set_eqI, rule iffI)
      fix y assume "y \<in> f ` (top1_left_cosets_on G mul H)"
      then obtain C where hC: "C \<in> top1_left_cosets_on G mul H" "y = f C" by (by100 blast)
      from hC(1) obtain g where hg: "g \<in> G" "C = top1_group_coset_on G mul H g"
        unfolding top1_left_cosets_on_def by (by100 blast)
      have hsome: "(SOME g'. g' \<in> G \<and> top1_group_coset_on G mul H g' = C) \<in> G"
        using someI_ex[of "\<lambda>g'. g' \<in> G \<and> top1_group_coset_on G mul H g' = C"] hg by (by100 blast)
      from maps[rule_format, OF hsome]
      show "y \<in> Y" using hC(2) unfolding f_def by simp
    next
      fix y assume "y \<in> Y"
      from surj have "\<exists>g\<in>G. \<phi> g = y" using \<open>y \<in> Y\<close> by (by100 blast)
      then obtain g where hg: "g \<in> G" "\<phi> g = y" by (by100 blast)
      let ?C = "top1_group_coset_on G mul H g"
      have hC_in: "?C \<in> top1_left_cosets_on G mul H"
        unfolding top1_left_cosets_on_def using hg(1) by (by100 blast)
      have hsome: "(SOME g'. g' \<in> G \<and> top1_group_coset_on G mul H g' = ?C) \<in> G \<and>
          top1_group_coset_on G mul H (SOME g'. g' \<in> G \<and> top1_group_coset_on G mul H g' = ?C) = ?C"
        using someI_ex[of "\<lambda>g'. g' \<in> G \<and> top1_group_coset_on G mul H g' = ?C"] hg(1)
        by (by100 blast)
      let ?s = "SOME g'. g' \<in> G \<and> top1_group_coset_on G mul H g' = ?C"
      have "?s \<in> G" using hsome by (by100 blast)
      have "top1_group_coset_on G mul H ?s = ?C" using hsome by (by100 blast)
      \<comment> \<open>Since ?s and g are in the same coset, \\<phi>(?s) = \\<phi>(g).\<close>
      from fiber_eq[rule_format, OF \<open>?s \<in> G\<close> hg(1)]
      have "\<phi> ?s = \<phi> g" using \<open>top1_group_coset_on G mul H ?s = ?C\<close> by simp
      hence "f ?C = y" using hg(2) unfolding f_def by simp
      thus "y \<in> f ` (top1_left_cosets_on G mul H)" using hC_in by (by100 blast)
    qed
  qed
qed

\<comment> \<open>Expert audit2: extract tree Euler sub-lemmas as named lemmas.\<close>

\<comment> \<open>A finite tree with at least 2 arcs has a leaf: an arc with one endpoint
   not contained in any other arc. (Munkres 85.2 Step 1 key step.)\<close>
lemma finite_tree_has_leaf_arc:
  assumes "top1_is_tree_on T TT"
      and "\<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)"
      and "\<Union>\<A> = T"
      and "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and "finite \<A>" and "card \<A> \<ge> 2"
  shows "\<exists>A0 v. A0 \<in> \<A> \<and> v \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)
      \<and> (\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> v \<notin> B)"
  sorry

\<comment> \<open>Removing a leaf arc from a tree gives a tree.\<close>
lemma finite_tree_remove_leaf_is_tree:
  assumes "top1_is_tree_on T TT"
      and "\<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)"
      and "\<Union>\<A> = T"
      and "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and "A0 \<in> \<A>"
      and "v \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)"
      and "\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> v \<notin> B"
      and "card \<A> \<ge> 2" and "finite \<A>"
  shows "top1_is_tree_on (\<Union>(\<A> - {A0})) (subspace_topology T TT (\<Union>(\<A> - {A0})))"
  sorry

\<comment> \<open>In a tree with \\<ge> 2 arcs, a leaf vertex's other endpoint is shared with another arc.
   (Needed for V = V' \\<union> {v} in tree Euler induction.)\<close>
lemma tree_leaf_other_endpoint_shared:
  assumes "top1_is_tree_on T TT"
      and "\<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)"
      and "\<Union>\<A> = T"
      and "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and "A0 \<in> \<A>"
      and "v \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)"
      and "\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> v \<notin> B"
      and "card \<A> \<ge> 2" and "finite \<A>"
      and "x \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)" and "x \<noteq> v"
  shows "\<exists>B\<in>\<A> - {A0}. x \<in> B"
proof (rule ccontr)
  assume hcontr: "\<not> (\<exists>B\<in>\<A> - {A0}. x \<in> B)"
  hence hx_only_A0: "\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> x \<notin> B" by (by100 blast)
  \<comment> \<open>Both v and x are only in A0. So A0 is disjoint from \\<Union>(\\<A>-{A0}).\<close>
  have hA0_disj: "A0 \<inter> \<Union>(\<A> - {A0}) = {}"
  proof (rule ccontr)
    assume "A0 \<inter> \<Union>(\<A> - {A0}) \<noteq> {}"
    then obtain y where "y \<in> A0" "y \<in> \<Union>(\<A> - {A0})" by (by100 blast)
    then obtain B where "B \<in> \<A> - {A0}" "y \<in> B" by (by100 blast)
    hence "B \<in> \<A>" "B \<noteq> A0" by (by100 blast)+
    from assms(4)[rule_format, OF assms(5) \<open>B \<in> \<A>\<close>]
    have "A0 \<inter> B \<subseteq> top1_arc_endpoints_on A0 (subspace_topology T TT A0)"
      using \<open>B \<noteq> A0\<close> by (by100 blast)
    hence "y \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)"
      using \<open>y \<in> A0\<close> \<open>y \<in> B\<close> by (by100 blast)
    \<comment> \<open>y is an endpoint of A0. v and x are endpoints.
       But v \\<notin> B (leaf) and x \\<notin> B (by contradiction hypothesis). So y \\<notin> B.\<close>
    have "y \<notin> B"
    proof -
      have "y = v \<or> y = x"
      proof -
        have hstrict: "is_topology_on_strict T TT"
          using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
        have hhaus: "is_hausdorff_on T TT"
          using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
        have hA0_sub: "A0 \<subseteq> T" using assms(2,5) by (by100 blast)
        have hA0_arc: "top1_is_arc_on A0 (subspace_topology T TT A0)" using assms(2,5) by (by100 blast)
        obtain h where hh: "top1_homeomorphism_on I_set I_top A0 (subspace_topology T TT A0) h"
          using hA0_arc unfolding top1_is_arc_on_def by (by100 blast)
        have hep: "top1_arc_endpoints_on A0 (subspace_topology T TT A0) = {h 0, h 1}"
          by (rule arc_endpoints_are_boundary[OF hstrict hhaus hA0_sub hA0_arc hh])
        have h_inj: "inj_on h I_set"
          using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have hne: "h 0 \<noteq> h 1"
        proof
          assume "h 0 = h 1"
          from inj_onD[OF h_inj this] show False unfolding top1_unit_interval_def by (by100 auto)
        qed
        \<comment> \<open>endpoints = {h 0, h 1} with h0 \\<ne> h1. v and x are both in endpoints, x \\<ne> v.
           So {v, x} = {h 0, h 1}. Hence y \\<in> {h 0, h 1} = {v, x}.\<close>
        have "v \<in> {h 0, h 1}" using assms(6) hep by simp
        have "x \<in> {h 0, h 1}" using assms(10) hep by simp
        have "card {h 0, h 1} = 2" using hne by (by100 simp)
        have "card {v, x} = 2" using assms(11) by (by100 simp)
        have "{v, x} = {h 0, h 1}"
          using \<open>v \<in> {h 0, h 1}\<close> \<open>x \<in> {h 0, h 1}\<close> \<open>card {h 0, h 1} = 2\<close> \<open>card {v, x} = 2\<close>
          by (by5000 force)
        thus ?thesis using \<open>y \<in> top1_arc_endpoints_on A0 _\<close> hep \<open>{v, x} = {h 0, h 1}\<close>
          by (by100 blast)
      qed
      thus ?thesis using assms(7)[rule_format, OF \<open>B \<in> \<A>\<close> \<open>B \<noteq> A0\<close>]
          hx_only_A0[rule_format, OF \<open>B \<in> \<A>\<close> \<open>B \<noteq> A0\<close>] by (by100 blast)
    qed
    thus False using \<open>y \<in> B\<close> by contradiction
  qed
  \<comment> \<open>T = A0 \\<union> \\<Union>(\\<A>-{A0}) is a disjoint union of two nonempty sets.\<close>
  have hA0_ne: "A0 \<noteq> {}"
  proof -
    have "x \<in> A0" using assms(10) unfolding top1_arc_endpoints_on_def by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  have hrest_ne: "\<Union>(\<A> - {A0}) \<noteq> {}"
  proof -
    have "\<A> - {A0} \<noteq> {}"
    proof -
      have "card \<A> \<ge> 2" using assms(8) .
      have "card (\<A> - {A0}) = card \<A> - 1" using assms(9,5) by (by100 simp)
      hence "card (\<A> - {A0}) \<ge> 1" using \<open>card \<A> \<ge> 2\<close> by linarith
      thus ?thesis using assms(9) by (by100 force)
    qed
    then obtain B where "B \<in> \<A> - {A0}" by (by100 blast)
    have "B \<noteq> {}"
    proof -
      have "B \<in> \<A>" using \<open>B \<in> \<A> - {A0}\<close> by (by100 blast)
      hence "top1_is_arc_on B (subspace_topology T TT B)" using assms(2) by (by100 blast)
      then obtain h where "top1_homeomorphism_on I_set I_top B (subspace_topology T TT B) h"
        unfolding top1_is_arc_on_def by (by100 blast)
      hence "bij_betw h I_set B" unfolding top1_homeomorphism_on_def by (by100 blast)
      have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
      hence "h 0 \<in> B" using \<open>bij_betw h I_set B\<close> unfolding bij_betw_def by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    thus ?thesis using \<open>B \<in> \<A> - {A0}\<close> by (by100 blast)
  qed
  \<comment> \<open>T connected but A0 and \\<Union>(\\<A>-{A0}) are both closed (coherent topology) and disjoint \\<Rightarrow> contradiction.\<close>
  have hT_conn: "top1_connected_on T TT"
    using assms(1) unfolding top1_is_tree_on_def by (by100 blast)
  have "A0 \<subseteq> T" using assms(2,5) by (by100 blast)
  have "\<Union>(\<A> - {A0}) \<subseteq> T" using assms(2,3) by (by100 blast)
  have "T = A0 \<union> \<Union>(\<A> - {A0})" using assms(3,5) by (by100 blast)
  \<comment> \<open>Both sets are closed in T (by graph coherent closedness).\<close>
  have "closedin_on T TT A0"
  proof -
    have hhaus: "is_hausdorff_on T TT"
      using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
    have hA0_arc: "top1_is_arc_on A0 (subspace_topology T TT A0)" using assms(2,5) by (by100 blast)
    from arc_compact[OF hA0_arc]
    have "top1_compact_on A0 (subspace_topology T TT A0)" .
    from Theorem_26_3[OF hhaus \<open>A0 \<subseteq> T\<close> this]
    show ?thesis .
  qed
  have "closedin_on T TT (\<Union>(\<A> - {A0}))"
  proof -
    \<comment> \<open>Each arc B is compact (arc\\_compact) hence closed in Hausdorff T (Theorem 26.3).
       Finite union of closed sets is closed.\<close>
    have hhaus: "is_hausdorff_on T TT"
      using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
    have hTT: "is_topology_on T TT"
      using hhaus unfolding is_hausdorff_on_def by (by100 blast)
    have "\<forall>B\<in>\<A> - {A0}. closedin_on T TT B"
    proof (intro ballI)
      fix B assume "B \<in> \<A> - {A0}"
      hence "B \<in> \<A>" by (by100 blast)
      have "B \<subseteq> T" using assms(2) \<open>B \<in> \<A>\<close> by (by100 blast)
      have "top1_is_arc_on B (subspace_topology T TT B)" using assms(2) \<open>B \<in> \<A>\<close> by (by100 blast)
      from arc_compact[OF this]
      have "top1_compact_on B (subspace_topology T TT B)" .
      from Theorem_26_3[OF hhaus \<open>B \<subseteq> T\<close> this]
      show "closedin_on T TT B" .
    qed
    have "finite (\<A> - {A0})" using assms(9) by (by100 simp)
    from closedin_Union_finite[OF hTT \<open>finite (\<A> - {A0})\<close> \<open>\<forall>B\<in>\<A> - {A0}. closedin_on T TT B\<close>]
    show ?thesis .
  qed
  \<comment> \<open>A0 is closed + complement closed \\<Rightarrow> A0 is clopen. Connected \\<Rightarrow> A0 = {} or T.\<close>
  have hA0_open: "A0 \<in> TT"
  proof -
    have "T - \<Union>(\<A> - {A0}) = A0"
      using \<open>T = A0 \<union> \<Union>(\<A> - {A0})\<close> hA0_disj by (by100 blast)
    moreover have "T - \<Union>(\<A> - {A0}) \<in> TT"
      using \<open>closedin_on T TT (\<Union>(\<A> - {A0}))\<close> unfolding closedin_on_def by (by100 blast)
    ultimately show ?thesis by simp
  qed
  have hA0_clopen: "A0 \<in> TT \<and> closedin_on T TT A0"
    using hA0_open \<open>closedin_on T TT A0\<close> by (by100 blast)
  have hTT: "is_topology_on T TT"
    using hT_conn unfolding top1_connected_on_def by (by100 blast)
  from connected_iff_clopen[OF hTT]
  have "\<forall>U. U \<in> TT \<and> closedin_on T TT U \<longrightarrow> U = {} \<or> U = T"
    using hT_conn by (by100 blast)
  hence "A0 = {} \<or> A0 = T" using hA0_clopen by (by100 blast)
  thus False using hA0_ne \<open>T = A0 \<union> _\<close> hA0_disj hrest_ne by (by100 blast)
qed

lemma tree_euler_nat:
  fixes n :: nat
  shows "\<forall>(T :: 'a set) TT \<A>. card \<A> = n \<longrightarrow>
    top1_is_tree_on T TT \<longrightarrow>
    (\<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)) \<longrightarrow>
    \<Union>\<A> = T \<longrightarrow>
    (\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
         A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
       \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
       \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2) \<longrightarrow>
    finite \<A> \<longrightarrow> \<A> \<noteq> {} \<longrightarrow>
    card (top1_graph_vertex_set T TT \<A>) = n + 1"
  \<comment> \<open>Munkres Lemma 85.2 Step 1 by induction on n = card(\\<A>).
     Base: 1 arc, 2 endpoints.
     Step: leaf arc removal, IH for smaller tree.\<close>
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (intro allI impI)
    fix T :: "'a set" and TT :: "'a set set" and \<A> :: "'a set set"
    assume hcard: "card \<A> = n"
      and htree: "top1_is_tree_on T TT"
      and harcs: "\<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)"
      and hcover: "\<Union>\<A> = T"
      and hinter: "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and hfin: "finite \<A>" and hne: "\<A> \<noteq> {}"
    show "card (top1_graph_vertex_set T TT \<A>) = n + 1"
    proof (cases "n = 1")
      case True
      \<comment> \<open>Base: 1 arc has 2 endpoints.\<close>
      from card_1_singletonE[OF True[folded hcard]] obtain A0 where "\<A> = {A0}" .
      have hA0: "A0 \<subseteq> T \<and> top1_is_arc_on A0 (subspace_topology T TT A0)"
        using harcs \<open>\<A> = {A0}\<close> by (by100 blast)
      have hstrict: "is_topology_on_strict T TT"
        using htree unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
      have hhaus: "is_hausdorff_on T TT"
        using htree unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
      obtain h where hh: "top1_homeomorphism_on I_set I_top A0 (subspace_topology T TT A0) h"
        using hA0 unfolding top1_is_arc_on_def by (by100 blast)
      have "top1_arc_endpoints_on A0 (subspace_topology T TT A0) = {h 0, h 1}"
        by (rule arc_endpoints_are_boundary[OF hstrict hhaus conjunct1[OF hA0] conjunct2[OF hA0] hh])
      moreover have "h 0 \<noteq> h 1"
      proof
        assume "h 0 = h 1"
        have "inj_on h I_set" using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        from inj_onD[OF this \<open>h 0 = h 1\<close>] show False unfolding top1_unit_interval_def by (by100 auto)
      qed
      ultimately have "card (top1_arc_endpoints_on A0 (subspace_topology T TT A0)) = 2" by (by100 simp)
      moreover have "top1_graph_vertex_set T TT \<A> =
          top1_arc_endpoints_on A0 (subspace_topology T TT A0)"
        unfolding top1_graph_vertex_set_def using \<open>\<A> = {A0}\<close> by simp
      ultimately show ?thesis using True by simp
    next
      case False
      hence hn_ge2: "n \<ge> 2"
      proof -
        have "n \<noteq> 0" using hcard hfin hne by (by100 force)
        thus ?thesis using False by linarith
      qed
      \<comment> \<open>Induction step: leaf arc removal.
         Book: find leaf arc A0 meeting T\\_0 in one vertex.\<close>
      have hcard_ge2: "card \<A> \<ge> 2" using hn_ge2 hcard by simp
      from finite_tree_has_leaf_arc[OF htree harcs hcover hinter hfin hcard_ge2]
      have "\<exists>A0 v. A0 \<in> \<A> \<and> v \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0) \<and>
          (\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> v \<notin> B)" .
      then obtain A0 v where hA0: "A0 \<in> \<A>"
          and hv_ep: "v \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)"
          and hv_uniq: "\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> v \<notin> B"
        by (elim exE conjE)
      let ?\<A>' = "\<A> - {A0}" and ?T' = "\<Union>(\<A> - {A0})"
      have h\<A>'_fin: "finite ?\<A>'" using hfin by (by100 simp)
      have h\<A>'_ne: "?\<A>' \<noteq> {}"
      proof -
        have "card ?\<A>' = n - 1" using hcard hfin hA0 by (by100 simp)
        hence "card ?\<A>' \<ge> 1" using hn_ge2 by linarith
        thus ?thesis using h\<A>'_fin by (by100 force)
      qed
      have h\<A>'_card: "card ?\<A>' = n - 1" using hcard hfin hA0 by (by100 simp)
      have h\<A>'_lt: "n - 1 < n" using hn_ge2 by linarith
      \<comment> \<open>Transfer properties to subspace.\<close>
      have hT'_tree: "top1_is_tree_on ?T' (subspace_topology T TT ?T')"
        by (rule finite_tree_remove_leaf_is_tree[OF htree harcs hcover hinter hA0 hv_ep hv_uniq hcard_ge2 hfin])
      have h\<A>'_arcs: "\<forall>A\<in>?\<A>'. A \<subseteq> ?T' \<and>
          top1_is_arc_on A (subspace_topology ?T' (subspace_topology T TT ?T') A)"
      proof (intro ballI conjI)
        fix A assume "A \<in> ?\<A>'" thus "A \<subseteq> ?T'" by (by100 blast)
        have "A \<in> \<A>" using \<open>A \<in> ?\<A>'\<close> by (by100 blast)
        hence "top1_is_arc_on A (subspace_topology T TT A)" using harcs by (by100 blast)
        have "A \<subseteq> ?T'" using \<open>A \<in> ?\<A>'\<close> by (by100 blast)
        have "subspace_topology ?T' (subspace_topology T TT ?T') A = subspace_topology T TT A"
          using subspace_topology_trans[of A ?T' T TT] \<open>A \<subseteq> ?T'\<close> by (by100 simp)
        thus "top1_is_arc_on A (subspace_topology ?T' (subspace_topology T TT ?T') A)"
          using \<open>top1_is_arc_on A (subspace_topology T TT A)\<close> by simp
      qed
      have h\<A>'_cover: "\<Union>?\<A>' = ?T'" by (by100 blast)
      have h\<A>'_inter: "\<forall>A\<in>?\<A>'. \<forall>B\<in>?\<A>'. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?T' (subspace_topology T TT ?T') A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?T' (subspace_topology T TT ?T') B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      proof (intro ballI impI)
        fix A B assume hAB: "A \<in> ?\<A>'" "B \<in> ?\<A>'" "A \<noteq> B"
        have "A \<in> \<A>" "B \<in> \<A>" using hAB(1-2) by (by100 blast)+
        have "A \<subseteq> ?T'" "B \<subseteq> ?T'" using hAB(1-2) by (by100 blast)+
        from hinter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> hAB(3)]
        have h: "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
          \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
          \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" .
        have "subspace_topology ?T' (subspace_topology T TT ?T') A = subspace_topology T TT A"
          using subspace_topology_trans[of A ?T' T TT] \<open>A \<subseteq> ?T'\<close> by (by100 simp)
        moreover have "subspace_topology ?T' (subspace_topology T TT ?T') B = subspace_topology T TT B"
          using subspace_topology_trans[of B ?T' T TT] \<open>B \<subseteq> ?T'\<close> by (by100 simp)
        ultimately show "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?T' (subspace_topology T TT ?T') A)
          \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?T' (subspace_topology T TT ?T') B)
          \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" using h by simp
      qed
      \<comment> \<open>Apply IH via less.hyps.\<close>
      from spec[OF spec[OF spec[OF less(1)[OF h\<A>'_lt], of ?T'], of "subspace_topology T TT ?T'"], of ?\<A>']
      have hIH: "card (top1_graph_vertex_set ?T' (subspace_topology T TT ?T') ?\<A>') = (n - 1) + 1"
        using h\<A>'_card hT'_tree h\<A>'_arcs h\<A>'_cover h\<A>'_inter h\<A>'_fin h\<A>'_ne by (by100 simp)
      \<comment> \<open>Vertex counting: V = V' \\<union> {v}, v \\<notin> V'.\<close>
      have hV_union: "top1_graph_vertex_set T TT \<A> =
          top1_graph_vertex_set ?T' (subspace_topology T TT ?T') ?\<A>' \<union> {v}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> top1_graph_vertex_set T TT \<A>"
        then obtain A where hA: "A \<in> \<A>"
            "x \<in> top1_arc_endpoints_on A (subspace_topology T TT A)"
          unfolding top1_graph_vertex_set_def by (by100 blast)
        show "x \<in> top1_graph_vertex_set ?T' (subspace_topology T TT ?T') ?\<A>' \<union> {v}"
        proof (cases "A = A0")
          case False
          hence "A \<in> ?\<A>'" using hA(1) by (by100 blast)
          have "A \<subseteq> ?T'" using \<open>A \<in> ?\<A>'\<close> by (by100 blast)
          have "subspace_topology ?T' (subspace_topology T TT ?T') A = subspace_topology T TT A"
            using subspace_topology_trans[of A ?T' T TT] \<open>A \<subseteq> ?T'\<close> by (by100 simp)
          hence "x \<in> top1_arc_endpoints_on A (subspace_topology ?T' (subspace_topology T TT ?T') A)"
            using hA(2) by simp
          thus ?thesis unfolding top1_graph_vertex_set_def using \<open>A \<in> ?\<A>'\<close> by (by100 blast)
        next
          case True
          hence "x \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)" using hA(2) by simp
          thus ?thesis
          proof (cases "x = v")
            case True thus ?thesis by (by100 blast)
          next
            case False
            \<comment> \<open>x is the other endpoint of A0. x must be in some arc B \\<in> \\<A>'.\<close>
            \<comment> \<open>x is the other endpoint of A0. By tree\\_leaf\\_other\\_endpoint\\_shared,
               x is in some arc B \\<in> \\<A> - {A0}.\<close>
            have "x \<in> A0" using \<open>x \<in> top1_arc_endpoints_on A0 _\<close>
              unfolding top1_arc_endpoints_on_def by (by100 blast)
            from tree_leaf_other_endpoint_shared[OF htree harcs hcover hinter hA0 hv_ep hv_uniq hcard_ge2 hfin
                \<open>x \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)\<close> False]
            obtain B where "B \<in> \<A> - {A0}" "x \<in> B" by (by100 blast)
            hence "B \<in> ?\<A>'" by (by100 blast)
            have "B \<in> \<A>" using \<open>B \<in> \<A> - {A0}\<close> by (by100 blast)
            have "B \<noteq> A0" using \<open>B \<in> \<A> - {A0}\<close> by (by100 blast)
            have "x \<in> A0 \<inter> B" using \<open>x \<in> A0\<close> \<open>x \<in> B\<close> by (by100 blast)
            have "A0 \<in> \<A>" using hA0 .
            have "A0 \<noteq> B" using \<open>B \<noteq> A0\<close> by (by100 blast)
            from hinter[rule_format, OF \<open>A0 \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>A0 \<noteq> B\<close>]
            have "x \<in> top1_arc_endpoints_on B (subspace_topology T TT B)"
              using \<open>x \<in> A0 \<inter> B\<close> by (by100 blast)
            have "B \<subseteq> ?T'" using \<open>B \<in> ?\<A>'\<close> by (by100 blast)
            have "subspace_topology ?T' (subspace_topology T TT ?T') B = subspace_topology T TT B"
              using subspace_topology_trans[of B ?T' T TT] \<open>B \<subseteq> ?T'\<close> by (by100 simp)
            hence "x \<in> top1_arc_endpoints_on B (subspace_topology ?T' (subspace_topology T TT ?T') B)"
              using \<open>x \<in> top1_arc_endpoints_on B (subspace_topology T TT B)\<close> by simp
            thus ?thesis unfolding top1_graph_vertex_set_def using \<open>B \<in> ?\<A>'\<close> by (by100 blast)
          qed
        qed
      next
        fix x assume "x \<in> top1_graph_vertex_set ?T' (subspace_topology T TT ?T') ?\<A>' \<union> {v}"
        thus "x \<in> top1_graph_vertex_set T TT \<A>"
        proof
          assume "x \<in> top1_graph_vertex_set ?T' (subspace_topology T TT ?T') ?\<A>'"
          then obtain B where "B \<in> ?\<A>'"
              "x \<in> top1_arc_endpoints_on B (subspace_topology ?T' (subspace_topology T TT ?T') B)"
            unfolding top1_graph_vertex_set_def by (by100 blast)
          have "B \<in> \<A>" using \<open>B \<in> ?\<A>'\<close> by (by100 blast)
          have "B \<subseteq> ?T'" using \<open>B \<in> ?\<A>'\<close> by (by100 blast)
          have "subspace_topology ?T' (subspace_topology T TT ?T') B = subspace_topology T TT B"
            using subspace_topology_trans[of B ?T' T TT] \<open>B \<subseteq> ?T'\<close> by (by100 simp)
          hence "x \<in> top1_arc_endpoints_on B (subspace_topology T TT B)"
            using \<open>x \<in> top1_arc_endpoints_on B _\<close> by simp
          thus ?thesis unfolding top1_graph_vertex_set_def using \<open>B \<in> \<A>\<close> by (by100 blast)
        next
          assume "x \<in> {v}"
          hence "x = v" by (by100 blast)
          thus ?thesis unfolding top1_graph_vertex_set_def
            using hA0 hv_ep by (by100 blast)
        qed
      qed
      have hv_fresh: "v \<notin> top1_graph_vertex_set ?T' (subspace_topology T TT ?T') ?\<A>'"
      proof -
        have "v \<notin> \<Union>?\<A>'"
        proof
          assume "v \<in> \<Union>?\<A>'"
          then obtain B where "B \<in> ?\<A>'" "v \<in> B" by (by100 blast)
          hence "B \<in> \<A>" "B \<noteq> A0" by (by100 blast)+
          from hv_uniq[rule_format, OF \<open>B \<in> \<A>\<close> \<open>B \<noteq> A0\<close>]
          show False using \<open>v \<in> B\<close> by (by100 blast)
        qed
        moreover have "top1_graph_vertex_set ?T' (subspace_topology T TT ?T') ?\<A>' \<subseteq> \<Union>?\<A>'"
          unfolding top1_graph_vertex_set_def top1_arc_endpoints_on_def by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      have hfin_V': "finite (top1_graph_vertex_set ?T' (subspace_topology T TT ?T') ?\<A>')"
      proof -
        have "\<forall>A\<in>?\<A>'. finite (top1_arc_endpoints_on A (subspace_topology ?T' (subspace_topology T TT ?T') A))"
        proof (intro ballI)
          fix A assume "A \<in> ?\<A>'"
          hence "A \<in> \<A>" by (by100 blast)
          have hA_sub: "A \<subseteq> T" using harcs \<open>A \<in> \<A>\<close> by (by100 blast)
          have hA_arc: "top1_is_arc_on A (subspace_topology T TT A)" using harcs \<open>A \<in> \<A>\<close> by (by100 blast)
          have hstrict: "is_topology_on_strict T TT"
            using htree unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
          have hhaus: "is_hausdorff_on T TT"
            using htree unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
          obtain h where hh: "top1_homeomorphism_on I_set I_top A (subspace_topology T TT A) h"
            using hA_arc unfolding top1_is_arc_on_def by (by100 blast)
          have "top1_arc_endpoints_on A (subspace_topology T TT A) = {h 0, h 1}"
            by (rule arc_endpoints_are_boundary[OF hstrict hhaus hA_sub hA_arc hh])
          hence "finite (top1_arc_endpoints_on A (subspace_topology T TT A))" by (by100 simp)
          have "A \<subseteq> ?T'" using \<open>A \<in> ?\<A>'\<close> by (by100 blast)
          have "subspace_topology ?T' (subspace_topology T TT ?T') A = subspace_topology T TT A"
            using subspace_topology_trans[of A ?T' T TT] \<open>A \<subseteq> ?T'\<close> by (by100 simp)
          thus "finite (top1_arc_endpoints_on A (subspace_topology ?T' (subspace_topology T TT ?T') A))"
            using \<open>finite (top1_arc_endpoints_on A (subspace_topology T TT A))\<close> by simp
        qed
        thus ?thesis unfolding top1_graph_vertex_set_def using h\<A>'_fin by (by100 blast)
      qed
      have "card (top1_graph_vertex_set T TT \<A>) =
          card (top1_graph_vertex_set ?T' (subspace_topology T TT ?T') ?\<A>') + 1"
      proof -
        let ?V' = "top1_graph_vertex_set ?T' (subspace_topology T TT ?T') ?\<A>'"
        have "top1_graph_vertex_set T TT \<A> = insert v ?V'"
          using hV_union hv_fresh by (by100 blast)
        moreover have "card (insert v ?V') = card ?V' + 1"
          using card_insert_disjoint[OF hfin_V'] hv_fresh by (by100 simp)
        ultimately show ?thesis by simp
      qed
      thus ?thesis using hIH hn_ge2 by linarith
    qed
  qed
qed

\<comment> \<open>Corollary: universally quantified version.\<close>
lemma tree_euler_all:
  "\<forall>(T :: 'a set) TT \<A>. top1_is_tree_on T TT \<longrightarrow>
    (\<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)) \<longrightarrow>
    \<Union>\<A> = T \<longrightarrow>
    (\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
         A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
       \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
       \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2) \<longrightarrow>
    finite \<A> \<longrightarrow> \<A> \<noteq> {} \<longrightarrow>
    card (top1_graph_vertex_set T TT \<A>) = card \<A> + 1"
proof (intro allI impI)
  fix T :: "'a set" and TT \<A>
  assume h: "top1_is_tree_on T TT"
    "\<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)"
    "\<Union>\<A> = T"
    "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
         A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
       \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
       \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
    "finite \<A>" "\<A> \<noteq> {}"
  from spec[OF spec[OF spec[OF tree_euler_nat[of "card \<A>"], of T], of TT], of \<A>]
  show "card (top1_graph_vertex_set T TT \<A>) = card \<A> + 1" using h by (by100 simp)
qed

\<comment> \<open>Lemma 85.2, Step 1: \\<chi>(T) = 1 for any finite tree.
   Proof by induction on the number of arcs. If T is a tree and T = T\\_0 \\<union> A
   where T\\_0 is a tree and A is an arc meeting T\\_0 in a single vertex,
   then T has one more arc and one more vertex than T\\_0, so \\<chi> is preserved.\<close>
lemma tree_euler_number_one:
  fixes T :: "'a set" and TT :: "'a set set" and \<A> :: "'a set set"
  assumes "top1_is_tree_on T TT"
      and "\<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)"
      and "\<Union>\<A> = T"
      and "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and "finite \<A>"
      and "\<A> \<noteq> {}"
  shows "card (top1_graph_vertex_set T TT \<A>) = card \<A> + 1"
proof -
  from spec[OF spec[OF spec[OF tree_euler_all, of T], of TT], of \<A>]
  show ?thesis using assms by (by100 simp)
qed

\<comment> \<open>Detailed proof structure for tree\\_euler\\_all (informational):
   Munkres Lemma 85.2 Step 1: \\<chi>(T) = vertices - arcs = 1.
   Book proof: induction on n = card(\\<A>).
   Base (n=1): one arc has 2 endpoints, card V = 2 = 1+1.
   Step (n>1): find a leaf arc A\\_0 (endpoint not in any other arc).
   Remove it: T\\_0 = T \\ (A\\_0 \\ {shared endpoint}) is a tree with n-1 arcs.
   By IH: card V\\_0 = n. Adding A\\_0 adds 1 vertex, so card V = n+1.

   Required sub-lemmas:
   - Every finite tree with \\<ge> 2 arcs has a leaf arc
   - Removing a leaf arc from a tree gives a tree
   - Arc/intersection properties transfer to subspace
   - Vertex set V = V' \\<union> \\{leaf endpoint\\}, leaf endpoint \\<notin> V'.\<close>

(* Old detailed proof body preserved in backups.
   The proof required: leaf arc existence, tree removal, property transfer,
   IH via tree\\_euler\\_all, vertex counting. See bck1054. *)

\<comment> \<open>Also need htree\\_euler in graph\\_euler\\_rank, now via tree\\_euler\\_number\\_one.\<close>

(* Detailed induction proof body preserved in bck1054. *)


\<comment> \<open>Lemma 85.2, Step 2: for a finite connected graph with spanning tree T,
   rank(\\<pi>\\_1) = card(non-tree arcs) = card(\\<A>) - card(V) + 1.
   The tree and graph share the same vertex set (endpoints of non-tree arcs are in T),
   and \\<chi>(T) = 1, so \\<chi>(X) = 1 - card(non-tree arcs).\<close>
lemma graph_euler_rank:
  fixes Y :: "'a set" and TY :: "'a set set"
  assumes "top1_is_graph_on Y TY"
      and "top1_connected_on Y TY"
      and "y0 \<in> Y"
      and \<A>_def: "\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
      and \<A>_cover: "\<Union>\<A> = Y"
      and \<A>_inter: "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and \<A>_coh: "\<forall>C. C \<subseteq> Y \<longrightarrow>
           (closedin_on Y TY C \<longleftrightarrow>
            (\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
      and T_tree: "top1_is_tree_on T (subspace_topology Y TY T)"
      and T_sub: "T \<subseteq> Y" and T_x0: "y0 \<in> T"
      and T_subgraph: "\<forall>A\<in>\<A>. A \<subseteq> T \<or>
           A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
      and T_coverage: "T = \<Union>{A \<in> \<A>. A \<subseteq> T}"
      and NT_endpoints: "\<forall>A\<in>{A \<in> \<A>. \<not> A \<subseteq> T}. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology Y TY A). e \<in> T"
      and S_eq: "S = {A \<in> \<A>. \<not> A \<subseteq> T}"
      and "finite \<A>"
  shows "card S + card (top1_graph_vertex_set Y TY \<A>) = card \<A> + 1"
proof -
  let ?\<A>_T = "{A \<in> \<A>. A \<subseteq> T}"
  have h\<A>_partition: "\<A> = ?\<A>_T \<union> S" using S_eq by (by100 blast)
  have h\<A>_disjoint: "?\<A>_T \<inter> S = {}" using S_eq by (by100 blast)
  have h\<A>_T_fin: "finite ?\<A>_T" using assms(15) by (by100 simp)
  have hS_fin: "finite S" using S_eq assms(15) by (by100 simp)
  have hcard_partition: "card \<A> = card ?\<A>_T + card S"
  proof -
    have "card \<A> = card (?\<A>_T \<union> S)" using h\<A>_partition by simp
    also have "... = card ?\<A>_T + card S"
      using card_Un_disjoint[OF h\<A>_T_fin hS_fin] h\<A>_disjoint by simp
    finally show ?thesis .
  qed
  \<comment> \<open>The full vertex set equals the tree vertex set (non-tree arc endpoints are in tree arcs).\<close>
  have hV_eq: "top1_graph_vertex_set Y TY \<A> =
      (\<Union>A\<in>?\<A>_T. top1_arc_endpoints_on A (subspace_topology Y TY A))"
  proof (rule set_eqI, rule iffI)
    fix e assume "e \<in> top1_graph_vertex_set Y TY \<A>"
    then obtain A where hA_in: "A \<in> \<A>" and he_ep: "e \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
      unfolding top1_graph_vertex_set_def by (by100 blast)
    show "e \<in> (\<Union>A\<in>?\<A>_T. top1_arc_endpoints_on A (subspace_topology Y TY A))"
    proof (cases "A \<subseteq> T")
      case True thus ?thesis using hA_in he_ep by (by100 blast)
    next
      case False
      \<comment> \<open>A is a non-tree arc. Its endpoint e is in T.\<close>
      have he_T: "e \<in> T" using NT_endpoints hA_in False he_ep by (by100 blast)
      \<comment> \<open>e \\<in> T = \\<Union>{B \\<in> \\<A>. B \\<subseteq> T}, so e \\<in> some tree arc B.\<close>
      then obtain B where hB_in: "B \<in> \<A>" and hB_T: "B \<subseteq> T" and he_B: "e \<in> B"
        using T_coverage by (by100 blast)
      \<comment> \<open>e \\<in> A \\<inter> B and A \\<ne> B, so e is in endpoints(B).\<close>
      have hAB: "A \<noteq> B" using False hB_T by (by100 blast)
      have he_ep_A: "e \<in> A" using he_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
      have he_AB: "e \<in> A \<inter> B" using he_ep_A he_B by (by100 blast)
      from \<A>_inter[rule_format, OF hA_in hB_in hAB]
      have "e \<in> top1_arc_endpoints_on B (subspace_topology Y TY B)"
        using he_AB by (by100 blast)
      thus ?thesis using hB_in hB_T by (by100 blast)
    qed
  next
    fix e assume "e \<in> (\<Union>A\<in>?\<A>_T. top1_arc_endpoints_on A (subspace_topology Y TY A))"
    thus "e \<in> top1_graph_vertex_set Y TY \<A>"
      unfolding top1_graph_vertex_set_def by (by100 blast)
  qed
  \<comment> \<open>Apply tree\\_euler\\_number\\_one to the tree T with arc family \\<A>\\_T.\<close>
  have htree_euler: "card (\<Union>A\<in>?\<A>_T. top1_arc_endpoints_on A (subspace_topology Y TY A)) = card ?\<A>_T + 1"
  proof -
    \<comment> \<open>Need: subspace\\_topology Y TY A = subspace\\_topology T (subspace\\_topology Y TY T) A
       for tree arcs A \\<subseteq> T \\<subseteq> Y. Then vertex set matches tree\\_euler\\_number\\_one.\<close>
    have hep_eq: "\<forall>A\<in>?\<A>_T. top1_arc_endpoints_on A (subspace_topology Y TY A) =
        top1_arc_endpoints_on A (subspace_topology T (subspace_topology Y TY T) A)"
    proof (intro ballI)
      fix A assume "A \<in> ?\<A>_T"
      hence "A \<subseteq> T" by (by100 blast)
      have "subspace_topology Y TY A = subspace_topology T (subspace_topology Y TY T) A"
        using subspace_topology_trans[of A T Y TY] \<open>A \<subseteq> T\<close> by (by100 simp)
      thus "top1_arc_endpoints_on A (subspace_topology Y TY A) =
          top1_arc_endpoints_on A (subspace_topology T (subspace_topology Y TY T) A)"
        by simp
    qed
    hence "(\<Union>A\<in>?\<A>_T. top1_arc_endpoints_on A (subspace_topology Y TY A)) =
        top1_graph_vertex_set T (subspace_topology Y TY T) ?\<A>_T"
      unfolding top1_graph_vertex_set_def by simp
    moreover have "card (top1_graph_vertex_set T (subspace_topology Y TY T) ?\<A>_T) = card ?\<A>_T + 1"
    proof -
      \<comment> \<open>Need: T is a tree, \\<A>\\_T are arcs in T, etc. Most from graph\\_euler\\_rank assumptions.\<close>
      have hT_arcs: "\<forall>A\<in>?\<A>_T. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T (subspace_topology Y TY T) A)"
      proof (intro ballI conjI)
        fix A assume "A \<in> ?\<A>_T"
        thus "A \<subseteq> T" by (by100 blast)
        have "A \<in> \<A>" using \<open>A \<in> ?\<A>_T\<close> by (by100 blast)
        hence "top1_is_arc_on A (subspace_topology Y TY A)" using \<A>_def by (by100 blast)
        moreover have "subspace_topology T (subspace_topology Y TY T) A = subspace_topology Y TY A"
          using subspace_topology_trans[of A T Y TY] \<open>A \<subseteq> T\<close> by (by100 simp)
        ultimately show "top1_is_arc_on A (subspace_topology T (subspace_topology Y TY T) A)"
          by simp
      qed
      have hT_cover: "\<Union>?\<A>_T = T" using T_coverage by simp
      have hT_inter: "\<forall>A\<in>?\<A>_T. \<forall>B\<in>?\<A>_T. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T (subspace_topology Y TY T) A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T (subspace_topology Y TY T) B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      proof (intro ballI impI)
        fix A B assume "A \<in> ?\<A>_T" "B \<in> ?\<A>_T" "A \<noteq> B"
        hence "A \<in> \<A>" "B \<in> \<A>" "A \<subseteq> T" "B \<subseteq> T" by (by100 blast)+
        from \<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>A \<noteq> B\<close>]
        have h: "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
          \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
          \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" .
        have "subspace_topology T (subspace_topology Y TY T) A = subspace_topology Y TY A"
          using subspace_topology_trans[of A T Y TY] \<open>A \<subseteq> T\<close> by (by100 simp)
        moreover have "subspace_topology T (subspace_topology Y TY T) B = subspace_topology Y TY B"
          using subspace_topology_trans[of B T Y TY] \<open>B \<subseteq> T\<close> by (by100 simp)
        ultimately show "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T (subspace_topology Y TY T) A)
          \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T (subspace_topology Y TY T) B)
          \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
          using h by simp
      qed
      have hT_fin: "finite ?\<A>_T" using assms(15) by (by100 simp)
      have hT_ne: "?\<A>_T \<noteq> {}"
      proof -
        have "T \<noteq> {}" using T_x0 by (by100 blast)
        hence "\<Union>?\<A>_T \<noteq> {}" using T_coverage by simp
        thus ?thesis by (by100 blast)
      qed
      from tree_euler_number_one[OF T_tree hT_arcs hT_cover hT_inter hT_fin hT_ne]
      show ?thesis .
    qed
    ultimately show ?thesis by simp
  qed
  have "card (top1_graph_vertex_set Y TY \<A>) = card ?\<A>_T + 1"
    using hV_eq htree_euler by simp
  thus ?thesis using hcard_partition by linarith
qed

\<comment> \<open>Covering lifted arc family: \\<A>\\_E is exactly the set of path components
   of p\\<inverse>(A) for each A \\<in> \\<A>\\_X. Each base arc A lifts to exactly k arcs,
   one per sheet of the covering.\<close>
definition top1_covering_lifted_arc_family_on ::
    "'b set \<Rightarrow> 'b set set \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> ('b \<Rightarrow> 'a)
     \<Rightarrow> 'a set set \<Rightarrow> 'b set set \<Rightarrow> bool"
  where "top1_covering_lifted_arc_family_on E TE X TX p \<A>_X \<A>_E \<longleftrightarrow>
    (\<forall>B\<in>\<A>_E. \<exists>A\<in>\<A>_X. B \<subseteq> {e \<in> E. p e \<in> A} \<and> p ` B = A) \<and>
    (\<forall>A\<in>\<A>_X. \<forall>e\<in>{e' \<in> E. p e' \<in> A}. \<exists>B\<in>\<A>_E. e \<in> B \<and> B \<subseteq> {e' \<in> E. p e' \<in> A}) \<and>
    (\<forall>B1\<in>\<A>_E. \<forall>B2\<in>\<A>_E. B1 \<noteq> B2 \<longrightarrow> B1 \<inter> B2 = {} \<or>
        (\<exists>A\<in>\<A>_X. B1 \<subseteq> {e \<in> E. p e \<in> A} \<and> B2 \<subseteq> {e \<in> E. p e \<in> A}))"

\<comment> \<open>Covering multiplicity for arcs: a k-sheeted covering with lifted arc family
   has exactly k times as many arcs as the base.\<close>
lemma covering_lifted_arc_family_card:
  fixes E :: "'b set" and TE :: "'b set set" and X :: "'a set" and TX :: "'a set set"
  assumes "top1_covering_map_on E TE X TX p"
      and "top1_covering_lifted_arc_family_on E TE X TX p \<A>_X \<A>_E"
      and "finite \<A>_X"
      and "\<forall>x\<in>X. card {e \<in> E. p e = x} = k"
  shows "finite \<A>_E \<and> card \<A>_E = k * card \<A>_X"
  sorry

\<comment> \<open>Covering multiplicity for vertices.\<close>
lemma covering_lifted_vertex_set_card:
  fixes E :: "'b set" and TE :: "'b set set" and X :: "'a set" and TX :: "'a set set"
  assumes "top1_covering_map_on E TE X TX p"
      and "top1_covering_lifted_arc_family_on E TE X TX p \<A>_X \<A>_E"
      and "finite (top1_graph_vertex_set X TX \<A>_X)"
      and "\<forall>x\<in>X. card {e \<in> E. p e = x} = k"
  shows "card (top1_graph_vertex_set E TE \<A>_E) = k * card (top1_graph_vertex_set X TX \<A>_X)"
  sorry

\<comment> \<open>For the Schreier formula, we need: rank(\\<pi>\\_1(E')) = kn + 1.
   Since E' is a k-fold covering of X (wedge of n+1 circles):
   - \\<pi>\\_1(X) free of rank n+1 (from Theorem 71.3)
   - The covering E' has k times as many arcs and vertices as X
   - So rank(\\<pi>\\_1(E')) = k \\<cdot> arcs(X) - k \\<cdot> vertices(X) + 1 = k(arcs - vertices) + 1
   - arcs(X) - vertices(X) = n (from rank(\\<pi>\\_1(X)) = n+1 = arcs - vertices + 1)
   - Hence rank(\\<pi>\\_1(E')) = kn + 1.\<close>

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
  shows "\<exists>(\<iota>H :: (real \<Rightarrow> real \<times> real) set set \<Rightarrow> 'g) SH.
    top1_is_free_group_full_on H mul e invg \<iota>H SH
    \<and> finite SH \<and> card SH = k * n + 1"
proof -
  \<comment> \<open>Munkres 85.3: F = \<pi>_1(X) for a wedge of n+1 circles. H corresponds to a
     k-sheeted covering space E. By Theorem 83.2, E is a graph.
     The Euler characteristic satisfies: \<chi>(E) = k \<cdot> \<chi>(X).
     X has 1 vertex and n+1 edges, so \<chi>(X) = 1 - (n+1) = -n.
     Hence \<chi>(E) = -kn. E has k vertices (fiber over the wedge point) and
     k(n+1) edges. So 1 - rank(\<pi>_1(E)) = \<chi>(E) = k - k(n+1) = -kn.
     Hence rank(\<pi>_1(E)) = kn + 1.\<close>
  \<comment> \<open>Step 1: Realize F as \<pi>_1 of wedge X of n+1 circles.\<close>
  obtain X :: "(real \<times> real) set" and TX :: "(real \<times> real) set set" and x0 :: "real \<times> real"
    where hX_graph: "top1_is_graph_on X TX" and hX_conn: "top1_connected_on X TX"
      and hx0: "x0 \<in> X"
      and hX_compact: "top1_compact_on X TX"
      and hF_iso: "top1_groups_isomorphic_on F mul
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)"
  proof -
    have "finite S" using assms(2) by (cases "finite S", by100 simp, by100 simp)
    note hrealiz = free_group_realized_by_wedge[OF assms(1) this]
    from hrealiz obtain X' :: "(real \<times> real) set" and TX' :: "(real \<times> real) set set"
        and x0' :: "real \<times> real" where
      hconj: "top1_is_graph_on X' TX' \<and> top1_connected_on X' TX' \<and> x0' \<in> X'
      \<and> top1_compact_on X' TX'
      \<and> top1_groups_isomorphic_on F mul
          (top1_fundamental_group_carrier X' TX' x0') (top1_fundamental_group_mul X' TX' x0')"
      by (by5000 fast)
    show ?thesis
      apply (rule that[of X' TX' x0'])
      using hconj by (by100 blast)+
  qed
  \<comment> \<open>Step 2: H \<le> F corresponds to a k-sheeted covering E of X.
     By Theorem 82.1, there exists a covering E with p_*(\<pi>_1(E)) = H-image.\<close>
  obtain E' :: "(real \<Rightarrow> real \<times> real) set set" and TE' and
      p' :: "(real \<Rightarrow> real \<times> real) set \<Rightarrow> real \<times> real" and
      e0' :: "(real \<Rightarrow> real \<times> real) set"
      and f_iso85 :: "'g \<Rightarrow> _"
    where hE'_cov: "top1_covering_map_on E' TE' X TX p'"
      and hE'_graph: "top1_is_graph_on E' TE'"
      and hE'_conn: "top1_connected_on E' TE'"
      and he0': "e0' \<in> E'"
      and hE'_strict: "is_topology_on_strict E' TE'"
      and "p' e0' = x0"
      and hH_corr85: "top1_fundamental_group_induced_on E' TE' e0' X TX x0 p'
          ` top1_fundamental_group_carrier E' TE' e0' = f_iso85 ` H"
      and hf_iso85: "top1_group_iso_on F mul
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0) f_iso85"
  proof -
    from hF_iso[unfolded top1_groups_isomorphic_on_def]
    obtain f0 where hf0: "top1_group_iso_on F mul
        (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0) f0"
      by (by100 blast)
    have hf0_bij: "bij_betw f0 F (top1_fundamental_group_carrier X TX x0)"
      using hf0 unfolding top1_group_iso_on_def by (by100 blast)
    have hfH_sub: "f0 ` H \<subseteq> top1_fundamental_group_carrier X TX x0"
      using hf0_bij assms(3) unfolding bij_betw_def by (by100 blast)
    have hX_top: "is_topology_on X TX"
      using hX_graph unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
    have hX_strict: "is_topology_on_strict X TX"
      using hX_graph unfolding top1_is_graph_on_def by (by100 blast)
    have hpi1_grp: "top1_is_group_on (top1_fundamental_group_carrier X TX x0)
        (top1_fundamental_group_mul X TX x0)
        (top1_fundamental_group_id X TX x0) (top1_fundamental_group_invg X TX x0)"
      using top1_fundamental_group_is_group[OF hX_top hx0] .
    have hf0_hom: "top1_group_hom_on F mul
        (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0) f0"
      using hf0 unfolding top1_group_iso_on_def by (by100 blast)
    have hf0_maps: "\<forall>x \<in> F. f0 x \<in> top1_fundamental_group_carrier X TX x0"
      using hf0_hom unfolding top1_group_hom_on_def by (by100 blast)
    have hf0_mul: "\<forall>x \<in> F. \<forall>y \<in> F. f0 (mul x y) = top1_fundamental_group_mul X TX x0 (f0 x) (f0 y)"
      using hf0_hom unfolding top1_group_hom_on_def by (by5000 blast)
    have hfH_grp: "top1_is_group_on (f0 ` H)
        (top1_fundamental_group_mul X TX x0)
        (top1_fundamental_group_id X TX x0)
        (top1_fundamental_group_invg X TX x0)"
    proof -
      have "top1_group_hom_on H mul
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0) f0"
        unfolding top1_group_hom_on_def
      proof (intro conjI ballI)
        fix x assume "x \<in> H" thus "f0 x \<in> top1_fundamental_group_carrier X TX x0"
          using hf0_maps assms(3) by (by100 blast)
      next
        fix x y assume "x \<in> H" "y \<in> H"
        thus "f0 (mul x y) = top1_fundamental_group_mul X TX x0 (f0 x) (f0 y)"
          using hf0_mul assms(3) by (by100 blast)
      qed
      from hom_image_is_subgroup[OF assms(4) hpi1_grp this]
      show ?thesis .
    qed
    have hX_pc: "top1_path_connected_on X TX"
      using connected_locally_path_connected_imp_path_connected[OF hX_top
        hX_conn graph_locally_path_connected[OF hX_graph]] hx0 by (by100 blast)
    from Theorem_82_1_covering_existence[OF hX_strict hX_pc
        graph_locally_path_connected[OF hX_graph]
        graph_semilocally_simply_connected[OF hX_graph]
        hx0 hfH_sub hfH_grp]
    obtain E0 :: "(real \<Rightarrow> real \<times> real) set set" and TE0 and
        p0 :: "(real \<Rightarrow> real \<times> real) set \<Rightarrow> real \<times> real" and e0c :: "(real \<Rightarrow> real \<times> real) set"
      where h82: "is_topology_on_strict E0 TE0" "top1_covering_map_on E0 TE0 X TX p0"
        "top1_path_connected_on E0 TE0" "top1_locally_path_connected_on E0 TE0"
        "e0c \<in> E0" "p0 e0c = x0"
        "top1_fundamental_group_image_hom E0 TE0 e0c X TX x0 p0 = f0 ` H"
      by - ((erule exE)+, (erule conjE)+, rule that, assumption+)
    have hE0_graph: "top1_is_graph_on E0 TE0"
      by (rule graph_covering_is_graph[OF hX_graph h82(2) h82(1)])
    show ?thesis
    proof (rule that[of E0 TE0 p0 e0c f0])
      show "top1_covering_map_on E0 TE0 X TX p0" using h82(2) .
      show "top1_is_graph_on E0 TE0" using hE0_graph .
      show "top1_connected_on E0 TE0" using path_connected_imp_connected[OF h82(3)] .
      show "e0c \<in> E0" using h82(5) .
      show "is_topology_on_strict E0 TE0" using h82(1) .
      show "p0 e0c = x0" using h82(6) .
      show "top1_fundamental_group_induced_on E0 TE0 e0c X TX x0 p0
          ` top1_fundamental_group_carrier E0 TE0 e0c = f0 ` H"
        using h82(7) unfolding top1_fundamental_group_image_hom_def .
      show "top1_group_iso_on F mul
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0) f0"
        using hf0 .
    qed
  qed
  \<comment> \<open>Step 3a: pi1(E') is free (graph\\_pi1\\_free\\_weak).\<close>
  from graph_pi1_free_weak[OF hE'_graph hE'_conn he0']
  obtain \<iota>_E :: "(real \<Rightarrow> real \<times> real) set set \<Rightarrow> _" and
      S_E :: "(real \<Rightarrow> real \<times> real) set set set" and
      \<A>_E :: "(real \<Rightarrow> real \<times> real) set set set" and
      T_E :: "(real \<Rightarrow> real \<times> real) set set"
    where hfree_E: "top1_is_free_group_full_on
        (top1_fundamental_group_carrier E' TE' e0')
        (top1_fundamental_group_mul E' TE' e0')
        (top1_fundamental_group_id E' TE' e0')
        (top1_fundamental_group_invg E' TE' e0')
        \<iota>_E S_E"
      and h\<A>_E: "\<forall>A\<in>\<A>_E. A \<subseteq> E' \<and> top1_is_arc_on A (subspace_topology E' TE' A)"
      and h\<A>_E_cover: "\<Union>\<A>_E = E'"
      and h\<A>_E_inter: "\<forall>A\<in>\<A>_E. \<forall>B\<in>\<A>_E. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology E' TE' A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology E' TE' B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and h\<A>_E_coh: "\<forall>C. C \<subseteq> E' \<longrightarrow>
           (closedin_on E' TE' C \<longleftrightarrow>
            (\<forall>A\<in>\<A>_E. closedin_on A (subspace_topology E' TE' A) (A \<inter> C)))"
      and hT_E_tree: "top1_is_tree_on T_E (subspace_topology E' TE' T_E)"
      and hT_E_sub: "T_E \<subseteq> E'" and hT_E_x0: "e0' \<in> T_E"
      and hT_E_subgraph: "\<forall>A\<in>\<A>_E. A \<subseteq> T_E \<or>
           A \<inter> T_E \<subseteq> top1_arc_endpoints_on A (subspace_topology E' TE' A)"
      and hT_E_coverage: "T_E = \<Union>{A \<in> \<A>_E. A \<subseteq> T_E}"
      and hNT_E_endpoints: "\<forall>A\<in>{A \<in> \<A>_E. \<not> A \<subseteq> T_E}.
           \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology E' TE' A). e \<in> T_E"
      and hS_E_eq: "S_E = {A \<in> \<A>_E. \<not> A \<subseteq> T_E}"
    by (elim exE conjE)
  \<comment> \<open>Step 3b: H is free on S\\_E (the same basis from \\<pi>\\_1(E')).\<close>
  have hH_free_SE: "\<exists>(\<iota>H :: (real \<Rightarrow> real \<times> real) set set \<Rightarrow> 'g).
      top1_is_free_group_full_on H mul e invg \<iota>H S_E"
  proof -
    \<comment> \<open>Same proof as \\<S>85.1 step 3c.\<close>
    have hX_strict85: "is_topology_on_strict X TX"
      using hX_graph unfolding top1_is_graph_on_def by (by100 blast)
    have hp85_inj: "inj_on (top1_fundamental_group_induced_on E' TE' e0' X TX x0 p')
        (top1_fundamental_group_carrier E' TE' e0')"
      by (rule covering_induced_injective[OF hE'_cov hE'_strict hX_strict85 he0' \<open>p' e0' = x0\<close>])
    let ?p_star85 = "top1_fundamental_group_induced_on E' TE' e0' X TX x0 p'"
    let ?f_inv85 = "inv_into F f_iso85"
    let ?\<phi>85 = "?f_inv85 \<circ> ?p_star85"
    have "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier E' TE' e0')
        (top1_fundamental_group_mul E' TE' e0') H mul"
    proof -
      \<comment> \<open>Same proof as \\<S>85.1 iso composition.\<close>
      have hE_top85: "is_topology_on E' TE'"
        using hE'_strict unfolding is_topology_on_strict_def by (by100 blast)
      have hX_top85: "is_topology_on X TX"
        using hX_strict85 unfolding is_topology_on_strict_def by (by100 blast)
      have hp85_cont: "top1_continuous_map_on E' TE' X TX p'"
        using hE'_cov unfolding top1_covering_map_on_def by (by100 blast)
      have hp85_hom: "top1_group_hom_on
          (top1_fundamental_group_carrier E' TE' e0') (top1_fundamental_group_mul E' TE' e0')
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0) ?p_star85"
        by (rule top1_fundamental_group_induced_on_is_hom[OF hE_top85 hX_top85
            he0' hx0 hp85_cont \<open>p' e0' = x0\<close>])
      have hG85_grp: "top1_is_group_on F mul e invg"
        using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
      have hpiX85_grp: "top1_is_group_on (top1_fundamental_group_carrier X TX x0)
          (top1_fundamental_group_mul X TX x0) (top1_fundamental_group_id X TX x0)
          (top1_fundamental_group_invg X TX x0)"
        by (rule top1_fundamental_group_is_group[OF hX_top85 hx0])
      note hf85_inv_iso = group_iso_on_inverse[OF hf_iso85 hG85_grp hpiX85_grp]
      have hf85_inv_hom: "top1_group_hom_on
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
          F mul ?f_inv85"
        using hf85_inv_iso[unfolded top1_group_iso_on_def, THEN conjunct1] .
      \<comment> \<open>\\<phi>85 maps into H.\<close>
      have h\<phi>85_maps: "\<forall>c \<in> top1_fundamental_group_carrier E' TE' e0'. ?\<phi>85 c \<in> H"
      proof (intro ballI)
        fix c assume "c \<in> top1_fundamental_group_carrier E' TE' e0'"
        hence "?p_star85 c \<in> f_iso85 ` H" using hH_corr85 by (by100 blast)
        then obtain h where "h \<in> H" "f_iso85 h = ?p_star85 c" by (by100 blast)
        have "h \<in> F" using \<open>h \<in> H\<close> assms(3) by (by100 blast)
        have "?f_inv85 (?p_star85 c) = ?f_inv85 (f_iso85 h)" using \<open>f_iso85 h = ?p_star85 c\<close>
          by (by100 simp)
        also have "\<dots> = h"
          using inv_into_f_f[OF bij_betw_imp_inj_on[OF
              hf_iso85[unfolded top1_group_iso_on_def, THEN conjunct2]] \<open>h \<in> F\<close>]
          by (by100 simp)
        finally show "?\<phi>85 c \<in> H" using \<open>h \<in> H\<close> unfolding comp_def by (by100 simp)
      qed
      \<comment> \<open>\\<phi>85 is hom.\<close>
      have h\<phi>85_hom: "top1_group_hom_on
          (top1_fundamental_group_carrier E' TE' e0')
          (top1_fundamental_group_mul E' TE' e0') H mul ?\<phi>85"
        unfolding top1_group_hom_on_def comp_def
      proof (intro conjI ballI)
        fix c assume "c \<in> top1_fundamental_group_carrier E' TE' e0'"
        show "?f_inv85 (?p_star85 c) \<in> H" using h\<phi>85_maps \<open>c \<in> _\<close> unfolding comp_def
          by (by100 blast)
      next
        fix a b assume ha: "a \<in> top1_fundamental_group_carrier E' TE' e0'"
            and hb: "b \<in> top1_fundamental_group_carrier E' TE' e0'"
        have "?p_star85 (top1_fundamental_group_mul E' TE' e0' a b) =
            top1_fundamental_group_mul X TX x0 (?p_star85 a) (?p_star85 b)"
          using hp85_hom ha hb unfolding top1_group_hom_on_def by (by100 blast)
        moreover have "?f_inv85 (top1_fundamental_group_mul X TX x0 (?p_star85 a) (?p_star85 b)) =
            mul (?f_inv85 (?p_star85 a)) (?f_inv85 (?p_star85 b))"
        proof -
          have "?p_star85 a \<in> top1_fundamental_group_carrier X TX x0"
            using hp85_hom ha unfolding top1_group_hom_on_def by (by100 blast)
          have "?p_star85 b \<in> top1_fundamental_group_carrier X TX x0"
            using hp85_hom hb unfolding top1_group_hom_on_def by (by100 blast)
          from hf85_inv_hom[unfolded top1_group_hom_on_def]
          show ?thesis using \<open>?p_star85 a \<in> _\<close> \<open>?p_star85 b \<in> _\<close> by (by100 blast)
        qed
        ultimately show "?f_inv85 (?p_star85 (top1_fundamental_group_mul E' TE' e0' a b)) =
            mul (?f_inv85 (?p_star85 a)) (?f_inv85 (?p_star85 b))" by (by100 simp)
      qed
      \<comment> \<open>\\<phi>85 is bijective.\<close>
      have h\<phi>85_bij: "bij_betw ?\<phi>85 (top1_fundamental_group_carrier E' TE' e0') H"
        unfolding bij_betw_def
      proof (intro conjI)
        show "inj_on ?\<phi>85 (top1_fundamental_group_carrier E' TE' e0')"
        proof (rule comp_inj_on[OF hp85_inj])
          have "?p_star85 ` top1_fundamental_group_carrier E' TE' e0' = f_iso85 ` H"
            using hH_corr85 by (by100 blast)
          moreover have "inj_on ?f_inv85 (f_iso85 ` H)"
          proof (rule inj_onI)
            fix x y assume "x \<in> f_iso85 ` H" "y \<in> f_iso85 ` H" "?f_inv85 x = ?f_inv85 y"
            from \<open>x \<in> f_iso85 ` H\<close> obtain hx where "hx \<in> H" "x = f_iso85 hx" by (by100 blast)
            from \<open>y \<in> f_iso85 ` H\<close> obtain hy where "hy \<in> H" "y = f_iso85 hy" by (by100 blast)
            have "inj_on f_iso85 F" using hf_iso85 unfolding top1_group_iso_on_def bij_betw_def
              by (by100 blast)
            have "?f_inv85 x = hx"
              using inv_into_f_f[OF \<open>inj_on f_iso85 F\<close>] \<open>hx \<in> H\<close> assms(3) \<open>x = f_iso85 hx\<close>
              by (by100 blast)
            have "?f_inv85 y = hy"
              using inv_into_f_f[OF \<open>inj_on f_iso85 F\<close>] \<open>hy \<in> H\<close> assms(3) \<open>y = f_iso85 hy\<close>
              by (by100 blast)
            from \<open>?f_inv85 x = ?f_inv85 y\<close> \<open>?f_inv85 x = hx\<close> \<open>?f_inv85 y = hy\<close>
            have "hx = hy" by (by100 simp)
            thus "x = y" using \<open>x = f_iso85 hx\<close> \<open>y = f_iso85 hy\<close> by (by100 simp)
          qed
          ultimately show "inj_on ?f_inv85 (?p_star85 ` top1_fundamental_group_carrier E' TE' e0')"
            by (by100 simp)
        qed
        show "?\<phi>85 ` top1_fundamental_group_carrier E' TE' e0' = H"
        proof (rule set_eqI, rule iffI)
          fix h assume "h \<in> ?\<phi>85 ` top1_fundamental_group_carrier E' TE' e0'"
          then obtain c where "c \<in> top1_fundamental_group_carrier E' TE' e0'" "h = ?\<phi>85 c"
            by (by100 blast)
          thus "h \<in> H" using h\<phi>85_maps by (by100 blast)
        next
          fix h assume "h \<in> H"
          hence "h \<in> F" using assms(3) by (by100 blast)
          hence "f_iso85 h \<in> f_iso85 ` H" using \<open>h \<in> H\<close> by (by100 blast)
          hence "f_iso85 h \<in> ?p_star85 ` top1_fundamental_group_carrier E' TE' e0'"
            using hH_corr85 by (by100 blast)
          then obtain c where "c \<in> top1_fundamental_group_carrier E' TE' e0'"
              "?p_star85 c = f_iso85 h" by (by100 blast)
          have "inj_on f_iso85 F" using hf_iso85 unfolding top1_group_iso_on_def bij_betw_def
            by (by100 blast)
          have "?f_inv85 (f_iso85 h) = h"
            using inv_into_f_f[OF \<open>inj_on f_iso85 F\<close> \<open>h \<in> F\<close>] by (by100 simp)
          hence "?\<phi>85 c = h" using \<open>?p_star85 c = f_iso85 h\<close> unfolding comp_def by (by100 simp)
          thus "h \<in> ?\<phi>85 ` top1_fundamental_group_carrier E' TE' e0'"
            using \<open>c \<in> _\<close> by (by100 blast)
        qed
      qed
      \<comment> \<open>Package as group\\_iso\\_on.\<close>
      have "top1_group_iso_on (top1_fundamental_group_carrier E' TE' e0')
          (top1_fundamental_group_mul E' TE' e0') H mul ?\<phi>85"
        unfolding top1_group_iso_on_def using h\<phi>85_hom h\<phi>85_bij by (by100 blast)
      thus ?thesis unfolding top1_groups_isomorphic_on_def by (by100 blast)
    qed
    from free_group_iso_transfer[OF hfree_E this assms(4)]
    show ?thesis .
  qed
  \<comment> \<open>Step 3c: rank = kn+1 (Euler characteristic argument).
     Following Munkres 85.3: E' is a k-sheeted covering of X.
     X is a wedge of n+1 circles: card(arcs) - card(vertices) = n.
     E' has k times as many arcs and vertices: card(AE) - card(VE) = kn.
     rank(\\<pi>\\_1(E')) = card(AE) - card(VE) + 1 = kn + 1.
     Since H is free on S\\_E (same basis as \\<pi>\\_1(E')): card S\\_E = kn + 1.\<close>
  from hH_free_SE obtain \<iota>H :: "(real \<Rightarrow> real \<times> real) set set \<Rightarrow> 'g"
    where hfreeH_SE: "top1_is_free_group_full_on H mul e invg \<iota>H S_E"
    by (by100 blast)
  have "card S_E = k * n + 1"
  proof -
    \<comment> \<open>Munkres 85.3: Euler characteristic argument.
       X is a wedge of n+1 circles, E' is its k-sheeted covering.
       \\<chi>(X) = -n, \\<chi>(E') = k\\<cdot>\\<chi>(X) = -kn.
       rank(\\<pi>\\_1(E')) = 1 - \\<chi>(E') = kn + 1.
       S\\_E is a free basis of \\<pi>\\_1(E'), so card S\\_E = rank = kn + 1.\<close>
    \<comment> \<open>Step 1: X is finite graph. F \\<cong> \\<pi>\\_1(X) free of rank n+1.
       By free\\_group\\_rank\\_invariant\\_finite, any finite basis of \\<pi>\\_1(X) has card n+1.\<close>
    \<comment> \<open>Step 2: E' is k-sheeted covering of X (finite graph).
       By graph covering structure: arcs(E') = k \\<cdot> arcs(X), vertices(E') = k \\<cdot> vertices(X).
       Hence \\<chi>(E') = k \\<cdot> \\<chi>(X).\<close>
    \<comment> \<open>Step 3: By Lemma 85.2: rank(\\<pi>\\_1(E')) = 1 - \\<chi>(E') = 1 - k\\<chi>(X).
       From rank(\\<pi>\\_1(X)) = n+1: \\<chi>(X) = 1 - (n+1) = -n.
       So rank(\\<pi>\\_1(E')) = 1 + kn.\<close>
    \<comment> \<open>Step A: [\\<pi>\\_1(X) : p'*(\\<pi>\\_1(E'))] = k (iso preserves index).\<close>
    let ?piX = "top1_fundamental_group_carrier X TX x0"
    let ?mulX = "top1_fundamental_group_mul X TX x0"
    let ?pH = "top1_fundamental_group_induced_on E' TE' e0' X TX x0 p'
        ` top1_fundamental_group_carrier E' TE' e0'"
    have hpH_eq: "?pH = f_iso85 ` H"
      using hH_corr85 unfolding top1_fundamental_group_image_hom_def by simp
    have hf_bij: "bij_betw f_iso85 F ?piX"
      using hf_iso85 unfolding top1_group_iso_on_def by (by100 blast)
    have hf_inj: "inj_on f_iso85 F"
      using hf_bij unfolding bij_betw_def by (by100 blast)
    \<comment> \<open>The map C \\<mapsto> f\\_iso85 ` C bijects left cosets of H to left cosets of ?pH.\<close>
    have hf_hom: "\<forall>x\<in>F. \<forall>y\<in>F. f_iso85 (mul x y) = ?mulX (f_iso85 x) (f_iso85 y)"
      using hf_iso85 unfolding top1_group_iso_on_def top1_group_hom_on_def by (by5000 blast)
    have hH_sub_F: "H \<subseteq> F" using assms(3) .
    have hcoset_map: "\<And>g. g \<in> F \<Longrightarrow>
        f_iso85 ` (top1_group_coset_on F mul H g) =
        top1_group_coset_on ?piX ?mulX ?pH (f_iso85 g)"
    proof -
      fix g assume "g \<in> F"
      show "f_iso85 ` (top1_group_coset_on F mul H g) =
          top1_group_coset_on ?piX ?mulX ?pH (f_iso85 g)"
        unfolding top1_group_coset_on_def hpH_eq
      proof (rule set_eqI, rule iffI)
        fix y assume "y \<in> f_iso85 ` {mul g h |h. h \<in> H}"
        then obtain h where "h \<in> H" "y = f_iso85 (mul g h)" by (by100 blast)
        have "h \<in> F" using \<open>h \<in> H\<close> hH_sub_F by (by100 blast)
        have "y = ?mulX (f_iso85 g) (f_iso85 h)"
          using \<open>y = f_iso85 (mul g h)\<close> hf_hom \<open>g \<in> F\<close> \<open>h \<in> F\<close> by simp
        thus "y \<in> {?mulX (f_iso85 g) h' |h'. h' \<in> f_iso85 ` H}"
          using \<open>h \<in> H\<close> by (by100 blast)
      next
        fix y assume "y \<in> {?mulX (f_iso85 g) h' |h'. h' \<in> f_iso85 ` H}"
        then obtain h' where "h' \<in> f_iso85 ` H" "y = ?mulX (f_iso85 g) h'" by (by100 blast)
        then obtain h where "h \<in> H" "h' = f_iso85 h" by (by100 blast)
        have "h \<in> F" using \<open>h \<in> H\<close> hH_sub_F by (by100 blast)
        have "y = f_iso85 (mul g h)"
          using \<open>y = ?mulX (f_iso85 g) h'\<close> \<open>h' = f_iso85 h\<close> hf_hom \<open>g \<in> F\<close> \<open>h \<in> F\<close> by simp
        thus "y \<in> f_iso85 ` {mul g h |h. h \<in> H}"
          using \<open>h \<in> H\<close> by (by100 blast)
      qed
    qed
    \<comment> \<open>Index preservation: the coset map is a bijection on coset spaces.\<close>
    have hindex: "top1_subgroup_has_index_on ?piX ?mulX ?pH k"
    proof -
      have hcoset_bij: "bij_betw (\<lambda>C. f_iso85 ` C)
          (top1_left_cosets_on F mul H) (top1_left_cosets_on ?piX ?mulX ?pH)"
        unfolding bij_betw_def
      proof (intro conjI)
        show "inj_on (\<lambda>C. f_iso85 ` C) (top1_left_cosets_on F mul H)"
        proof (rule inj_onI)
          fix C1 C2 assume hC1: "C1 \<in> top1_left_cosets_on F mul H"
              and hC2: "C2 \<in> top1_left_cosets_on F mul H"
              and heq: "f_iso85 ` C1 = f_iso85 ` C2"
          from hC1 obtain g1 where "g1 \<in> F" "C1 = top1_group_coset_on F mul H g1"
            unfolding top1_left_cosets_on_def by (by100 blast)
          from hC2 obtain g2 where "g2 \<in> F" "C2 = top1_group_coset_on F mul H g2"
            unfolding top1_left_cosets_on_def by (by100 blast)
          have hF_grp: "top1_is_group_on F mul e invg"
            using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
          have "C1 \<subseteq> F"
          proof -
            have "\<forall>h\<in>H. mul g1 h \<in> F"
              using group_mul_closed[OF hF_grp \<open>g1 \<in> F\<close>] hH_sub_F by (by100 blast)
            thus ?thesis using \<open>C1 = _\<close> unfolding top1_group_coset_on_def by (by100 blast)
          qed
          have "C2 \<subseteq> F"
          proof -
            have "\<forall>h\<in>H. mul g2 h \<in> F"
              using group_mul_closed[OF hF_grp \<open>g2 \<in> F\<close>] hH_sub_F by (by100 blast)
            thus ?thesis using \<open>C2 = _\<close> unfolding top1_group_coset_on_def by (by100 blast)
          qed
          show "C1 = C2"
          proof (rule set_eqI, rule iffI)
            fix x assume "x \<in> C1"
            hence "f_iso85 x \<in> f_iso85 ` C2" using heq by (by100 blast)
            then obtain y where "y \<in> C2" "f_iso85 x = f_iso85 y" by (by100 blast)
            from inj_onD[OF hf_inj this(2)]
            show "x \<in> C2" using \<open>y \<in> C2\<close> \<open>x \<in> C1\<close> \<open>C1 \<subseteq> F\<close> \<open>C2 \<subseteq> F\<close> by (by100 blast)
          next
            fix x assume "x \<in> C2"
            hence "f_iso85 x \<in> f_iso85 ` C1" using heq by (by100 blast)
            then obtain y where "y \<in> C1" "f_iso85 x = f_iso85 y" by (by100 blast)
            from inj_onD[OF hf_inj this(2)]
            show "x \<in> C1" using \<open>y \<in> C1\<close> \<open>x \<in> C2\<close> \<open>C1 \<subseteq> F\<close> \<open>C2 \<subseteq> F\<close> by (by100 blast)
          qed
        qed
        show "(\<lambda>C. f_iso85 ` C) ` (top1_left_cosets_on F mul H) =
            top1_left_cosets_on ?piX ?mulX ?pH"
          unfolding top1_left_cosets_on_def
        proof (rule set_eqI, rule iffI)
          fix D assume "D \<in> (\<lambda>C. f_iso85 ` C) ` {top1_group_coset_on F mul H g |g. g \<in> F}"
          then obtain g where "g \<in> F" "D = f_iso85 ` top1_group_coset_on F mul H g"
            by (by100 blast)
          hence "D = top1_group_coset_on ?piX ?mulX ?pH (f_iso85 g)"
            using hcoset_map by simp
          thus "D \<in> {top1_group_coset_on ?piX ?mulX ?pH g' |g'. g' \<in> ?piX}"
            using \<open>g \<in> F\<close> hf_bij unfolding bij_betw_def by (by100 blast)
        next
          fix D assume "D \<in> {top1_group_coset_on ?piX ?mulX ?pH g' |g'. g' \<in> ?piX}"
          then obtain g' where "g' \<in> ?piX" "D = top1_group_coset_on ?piX ?mulX ?pH g'"
            by (by100 blast)
          from \<open>g' \<in> ?piX\<close> obtain g where "g \<in> F" "g' = f_iso85 g"
            using hf_bij unfolding bij_betw_def by (by100 blast)
          have "D = f_iso85 ` top1_group_coset_on F mul H g"
            using \<open>D = _\<close> \<open>g' = f_iso85 g\<close> hcoset_map[OF \<open>g \<in> F\<close>] by simp
          thus "D \<in> (\<lambda>C. f_iso85 ` C) ` {top1_group_coset_on F mul H g |g. g \<in> F}"
            using \<open>g \<in> F\<close> by (by100 blast)
        qed
      qed
      from assms(5) have hF_fin: "finite (top1_left_cosets_on F mul H)"
          and hF_card: "card (top1_left_cosets_on F mul H) = k"
        unfolding top1_subgroup_has_index_on_def by (by100 blast)+
      have hpiX_fin: "finite (top1_left_cosets_on ?piX ?mulX ?pH)"
        using bij_betw_finite[OF hcoset_bij] hF_fin by simp
      have hpiX_card: "card (top1_left_cosets_on ?piX ?mulX ?pH) = k"
        using bij_betw_same_card[OF hcoset_bij] hF_card by simp
      show ?thesis unfolding top1_subgroup_has_index_on_def
        using hpiX_fin hpiX_card by (by100 blast)
    qed
    \<comment> \<open>Steps B--E (Munkres 85.3): covering Euler multiplicity.
       The k-sheeted covering E' \\<rightarrow> X satisfies rank(\\<pi>\\_1(E')) = k(n+1-1)+1 = kn+1.
       Book proof: E' has k\\<times>arcs(X) arcs and k\\<times>verts(X) vertices,
       \\<chi>(E') = k\\<chi>(X), rank = 1-\\<chi>. Requires Lemma 85.2 + covering multiplicity.\<close>
    \<comment> \<open>Step B: Apply graph\\_pi1\\_free\\_weak to X to get its arc/tree structure.\<close>
    from graph_pi1_free_weak[OF hX_graph hX_conn hx0]
    obtain \<iota>_X :: "(real \<times> real) set \<Rightarrow> _" and
        S_X :: "(real \<times> real) set set" and
        \<A>_X :: "(real \<times> real) set set" and
        T_X :: "(real \<times> real) set"
      where hfree_X: "top1_is_free_group_full_on
          (top1_fundamental_group_carrier X TX x0)
          (top1_fundamental_group_mul X TX x0)
          (top1_fundamental_group_id X TX x0)
          (top1_fundamental_group_invg X TX x0)
          \<iota>_X S_X"
        and h\<A>_X: "\<forall>A\<in>\<A>_X. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
        and h\<A>_X_cover: "\<Union>\<A>_X = X"
        and h\<A>_X_inter: "\<forall>A\<in>\<A>_X. \<forall>B\<in>\<A>_X. A \<noteq> B \<longrightarrow>
             A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)
           \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)
           \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
        and h\<A>_X_coh: "\<forall>C. C \<subseteq> X \<longrightarrow>
             (closedin_on X TX C \<longleftrightarrow>
              (\<forall>A\<in>\<A>_X. closedin_on A (subspace_topology X TX A) (A \<inter> C)))"
        and hT_X_tree: "top1_is_tree_on T_X (subspace_topology X TX T_X)"
        and hT_X_sub: "T_X \<subseteq> X" and hT_X_x0: "x0 \<in> T_X"
        and hT_X_subgraph: "\<forall>A\<in>\<A>_X. A \<subseteq> T_X \<or>
             A \<inter> T_X \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
        and hT_X_coverage: "T_X = \<Union>{A \<in> \<A>_X. A \<subseteq> T_X}"
        and hNT_X_endpoints: "\<forall>A\<in>{A \<in> \<A>_X. \<not> A \<subseteq> T_X}.
             \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology X TX A). e \<in> T_X"
        and hS_X_eq: "S_X = {A \<in> \<A>_X. \<not> A \<subseteq> T_X}"
      by (elim exE conjE)
    \<comment> \<open>Step C: card S\\_X = n + 1 by rank invariance.
       F is free on S (card n+1) and F \\<cong> \\<pi>\\_1(X) which is free on S\\_X.
       By free\\_group\\_rank\\_invariant\\_finite: card S\\_X = card S = n+1.\<close>
    \<comment> \<open>Step D: X and E' are finite graphs. Get finiteness.\<close>
    have h\<A>_X_fin: "finite \<A>_X"
      by (rule compact_graph_finite_arcs[OF hX_graph hX_compact
          h\<A>_X h\<A>_X_cover h\<A>_X_inter h\<A>_X_coh])
    \<comment> \<open>card S\\_X = n + 1: Transfer freeness from \\<pi>\\_1(X) to F via the isomorphism,
       then rank invariance. F free on S (card n+1), \\<pi>\\_1(X) free on S\\_X,
       F \\<cong> \\<pi>\\_1(X) \\<Rightarrow> F free on S\\_X \\<Rightarrow> card S\\_X = card S = n+1.\<close>
    have hS_X_card: "card S_X = n + 1"
    proof -
      have hF_grp: "top1_is_group_on F mul e invg"
        using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
      have hpiX_grp: "top1_is_group_on ?piX ?mulX
          (top1_fundamental_group_id X TX x0) (top1_fundamental_group_invg X TX x0)"
      proof -
        have "is_topology_on X TX"
          using hX_graph unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
        from top1_fundamental_group_is_group[OF this hx0]
        show ?thesis .
      qed
      \<comment> \<open>\\<pi>\\_1(X) \\<cong> F (symmetry of isomorphism).\<close>
      have "top1_groups_isomorphic_on ?piX ?mulX F mul"
        by (rule top1_groups_isomorphic_on_sym[OF hF_iso hF_grp hpiX_grp])
      \<comment> \<open>Transfer: \\<pi>\\_1(X) free on S\\_X, \\<pi>\\_1(X) \\<cong> F \\<Rightarrow> F free on S\\_X.\<close>
      from free_group_iso_transfer[OF hfree_X this hF_grp]
      obtain \<iota>' where h\<iota>': "top1_is_free_group_full_on F mul e invg \<iota>' S_X"
        by (by100 blast)
      \<comment> \<open>Rank invariance: F free on S (card n+1) and on S\\_X \\<Rightarrow> card S\\_X = card S.\<close>
      have "finite S" using assms(2) by (cases "finite S", by100 simp, by100 simp)
      have "finite S_X" using hS_X_eq h\<A>_X_fin by (by100 simp)
      from free_group_rank_invariant_finite[OF assms(1) h\<iota>' \<open>finite S\<close> \<open>finite S_X\<close>]
      show ?thesis using assms(2) by simp
    qed
    have hV_X_fin: "finite (top1_graph_vertex_set X TX \<A>_X)"
    proof -
      have "\<forall>A\<in>\<A>_X. finite (top1_arc_endpoints_on A (subspace_topology X TX A))"
      proof (intro ballI)
        fix A assume "A \<in> \<A>_X"
        hence "A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)" using h\<A>_X by (by100 blast)
        hence "top1_is_arc_on A (subspace_topology X TX A)" by (by100 blast)
        then obtain h where "top1_homeomorphism_on I_set I_top A (subspace_topology X TX A) h"
          unfolding top1_is_arc_on_def by (by100 blast)
        have hX_strict: "is_topology_on_strict X TX"
          using hX_graph unfolding top1_is_graph_on_def by (by100 blast)
        have hX_haus: "is_hausdorff_on X TX"
          using hX_graph unfolding top1_is_graph_on_def by (by100 blast)
        from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>A \<subseteq> X \<and> _\<close>[THEN conjunct1]
            \<open>top1_is_arc_on A _\<close> \<open>top1_homeomorphism_on _ _ _ _ h\<close>]
        have "top1_arc_endpoints_on A (subspace_topology X TX A) = {h 0, h 1}" .
        thus "finite (top1_arc_endpoints_on A (subspace_topology X TX A))" by (by100 simp)
      qed
      thus ?thesis unfolding top1_graph_vertex_set_def using h\<A>_X_fin by (by100 blast)
    qed
    have h\<A>_E_fin: "finite \<A>_E" sorry
    have hV_E_fin: "finite (top1_graph_vertex_set E' TE' \<A>_E)"
    proof -
      have "\<forall>A\<in>\<A>_E. finite (top1_arc_endpoints_on A (subspace_topology E' TE' A))"
      proof (intro ballI)
        fix A assume "A \<in> \<A>_E"
        hence "A \<subseteq> E' \<and> top1_is_arc_on A (subspace_topology E' TE' A)" using h\<A>_E by (by100 blast)
        hence "top1_is_arc_on A (subspace_topology E' TE' A)" by (by100 blast)
        then obtain h where "top1_homeomorphism_on I_set I_top A (subspace_topology E' TE' A) h"
          unfolding top1_is_arc_on_def by (by100 blast)
        have hE'_haus: "is_hausdorff_on E' TE'"
          using hE'_graph unfolding top1_is_graph_on_def by (by100 blast)
        from arc_endpoints_are_boundary[OF hE'_strict hE'_haus \<open>A \<subseteq> E' \<and> _\<close>[THEN conjunct1]
            \<open>top1_is_arc_on A _\<close> \<open>top1_homeomorphism_on _ _ _ _ h\<close>]
        have "top1_arc_endpoints_on A (subspace_topology E' TE' A) = {h 0, h 1}" .
        thus "finite (top1_arc_endpoints_on A (subspace_topology E' TE' A))" by (by100 simp)
      qed
      thus ?thesis unfolding top1_graph_vertex_set_def using h\<A>_E_fin by (by100 blast)
    qed
    \<comment> \<open>Step E: Euler formula for X: card S\\_X + card V\\_X = card \\<A>\\_X + 1.
       Hence card \\<A>\\_X - card V\\_X = card S\\_X - 1 = n.\<close>
    let ?V_X = "top1_graph_vertex_set X TX \<A>_X"
    let ?V_E = "top1_graph_vertex_set E' TE' \<A>_E"
    \<comment> \<open>h\\<A>\\_X\\_inter, h\\<A>\\_X\\_coh, hT\\_X\\_subgraph, hT\\_X\\_coverage now from graph\\_pi1\\_free\\_weak.\<close>
    have heuler_X: "card S_X + card ?V_X = card \<A>_X + 1"
      by (rule graph_euler_rank[OF hX_graph hX_conn hx0 h\<A>_X h\<A>_X_cover
          h\<A>_X_inter h\<A>_X_coh hT_X_tree hT_X_sub hT_X_x0 hT_X_subgraph hT_X_coverage
          hNT_X_endpoints hS_X_eq h\<A>_X_fin])
    hence heuler_X_diff: "int (card \<A>_X) - int (card ?V_X) = int n"
      using hS_X_card by linarith
    \<comment> \<open>Step F: Covering multiplicity.\<close>
    have hfiber_card: "card {e \<in> E'. p' e = x0} = k"
    proof -
      \<comment> \<open>Book: 'the lifting correspondence Phi: pi1(X,x0)/H -> p-inv(x0) is a bijection.
         Therefore, E is a k-fold covering of X.'
         The lifting correspondence (Theorem 54.4) surjects pi1(X) onto the fiber.
         Its kernel is p*(pi1(E)), so it induces a bijection on cosets.\<close>
      have hX_top: "is_topology_on X TX"
        using hX_graph unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
      have hE'_pc: "top1_path_connected_on E' TE'"
        using connected_locally_path_connected_imp_path_connected[OF
            hE'_strict[unfolded is_topology_on_strict_def, THEN conjunct1]
            hE'_conn graph_locally_path_connected[OF hE'_graph]] he0' by (by100 blast)
      \<comment> \<open>Apply Theorem 54.6(b) to get \\<phi> with full coset-fiber equivalence.\<close>
      \<comment> \<open>Apply Theorem 54.6(b) to get \\<phi> with full coset-fiber equivalence.\<close>
      have h546b: "\<exists>\<phi>. (\<forall>c\<in>?piX. \<phi> c \<in> {e \<in> E'. p' e = x0})
          \<and> \<phi> ` ?piX = {e \<in> E'. p' e = x0}
          \<and> (\<forall>c\<in>?piX. \<exists>f ft. f \<in> c \<and> top1_is_loop_on X TX x0 f
              \<and> top1_is_path_on E' TE' e0' (\<phi> c) ft \<and> (\<forall>s\<in>I_set. p' (ft s) = f s))
          \<and> (\<forall>g\<in>?piX. \<forall>h\<in>?piX.
              (\<phi> g = \<phi> h) = (top1_right_coset_on ?piX ?mulX ?pH g = top1_right_coset_on ?piX ?mulX ?pH h))"
      proof -
        from Theorem_54_6b[OF hE'_cov hE'_pc hX_top he0' \<open>p' e0' = x0\<close>]
        have "\<exists>\<phi>. (\<forall>c\<in>?piX. \<phi> c \<in> {e \<in> E'. p' e = x0})
            \<and> \<phi> ` ?piX = {e \<in> E'. p' e = x0}
            \<and> (\<forall>c\<in>?piX. \<exists>f ft. f \<in> c \<and> top1_is_loop_on X TX x0 f
                \<and> top1_is_path_on E' TE' e0' (\<phi> c) ft \<and> (\<forall>s\<in>I_set. p' (ft s) = f s))
            \<and> (\<forall>g\<in>?piX. \<forall>h\<in>?piX.
                (\<phi> g = \<phi> h) = (top1_right_coset_on ?piX ?mulX
                    (top1_fundamental_group_image_hom E' TE' e0' X TX x0 p') g
                 = top1_right_coset_on ?piX ?mulX
                    (top1_fundamental_group_image_hom E' TE' e0' X TX x0 p') h))" .
        moreover have "top1_fundamental_group_image_hom E' TE' e0' X TX x0 p' = ?pH"
          unfolding top1_fundamental_group_image_hom_def by simp
        ultimately show ?thesis by simp
      qed
      then obtain \<phi> where h\<phi>_maps: "\<forall>c\<in>?piX. \<phi> c \<in> {e \<in> E'. p' e = x0}"
          and h\<phi>_surj: "\<phi> ` ?piX = {e \<in> E'. p' e = x0}"
          and h\<phi>_lift: "\<forall>c\<in>?piX. \<exists>f ft. f \<in> c \<and> top1_is_loop_on X TX x0 f
              \<and> top1_is_path_on E' TE' e0' (\<phi> c) ft \<and> (\<forall>s\<in>I_set. p' (ft s) = f s)"
          and h\<phi>_fiber_eq: "\<forall>g\<in>?piX. \<forall>h\<in>?piX.
              (\<phi> g = \<phi> h) = (top1_right_coset_on ?piX ?mulX ?pH g = top1_right_coset_on ?piX ?mulX ?pH h)"
        by (elim exE conjE)
      have hpiX_grp: "top1_is_group_on ?piX ?mulX
          (top1_fundamental_group_id X TX x0) (top1_fundamental_group_invg X TX x0)"
      proof -
        from top1_fundamental_group_is_group[OF hX_top hx0] show ?thesis .
      qed
      have hpH_sub: "?pH \<subseteq> ?piX"
      proof -
        have hE_top: "is_topology_on E' TE'"
          using hE'_strict unfolding is_topology_on_strict_def by (by100 blast)
        have hp_hom: "top1_group_hom_on
            (top1_fundamental_group_carrier E' TE' e0') (top1_fundamental_group_mul E' TE' e0')
            ?piX ?mulX (top1_fundamental_group_induced_on E' TE' e0' X TX x0 p')"
        proof -
          have hp_cont: "top1_continuous_map_on E' TE' X TX p'"
            using hE'_cov unfolding top1_covering_map_on_def top1_evenly_covered_on_def by (by5000 blast)
          from top1_fundamental_group_induced_on_is_hom[OF hE_top hX_top he0' hx0 hp_cont \<open>p' e0' = x0\<close>]
          show ?thesis .
        qed
        thus ?thesis unfolding top1_group_hom_on_def by (by100 blast)
      qed
      have hpH_grp: "top1_is_group_on ?pH ?mulX
          (top1_fundamental_group_id X TX x0) (top1_fundamental_group_invg X TX x0)"
      proof -
        have hE_top: "is_topology_on E' TE'"
          using hE'_strict unfolding is_topology_on_strict_def by (by100 blast)
        have hE'_grp: "top1_is_group_on (top1_fundamental_group_carrier E' TE' e0')
            (top1_fundamental_group_mul E' TE' e0')
            (top1_fundamental_group_id E' TE' e0') (top1_fundamental_group_invg E' TE' e0')"
          by (rule top1_fundamental_group_is_group[OF hE_top he0'])
        have hp_cont: "top1_continuous_map_on E' TE' X TX p'"
          using hE'_cov unfolding top1_covering_map_on_def top1_evenly_covered_on_def by (by5000 blast)
        have hp_hom: "top1_group_hom_on
            (top1_fundamental_group_carrier E' TE' e0') (top1_fundamental_group_mul E' TE' e0')
            ?piX ?mulX (top1_fundamental_group_induced_on E' TE' e0' X TX x0 p')"
          by (rule top1_fundamental_group_induced_on_is_hom[OF hE_top hX_top he0' hx0 hp_cont \<open>p' e0' = x0\<close>])
        from hom_image_is_subgroup[OF hE'_grp hpiX_grp hp_hom]
        show ?thesis .
      qed
      from surjection_right_coset_bij[OF hpiX_grp hpH_sub hpH_grp h\<phi>_maps h\<phi>_surj h\<phi>_fiber_eq]
      obtain f where "bij_betw f (top1_right_cosets_on ?piX ?mulX ?pH) {e \<in> E'. p' e = x0}"
        by (by100 blast)
      from bij_betw_same_card[OF this]
      have hright_card: "card (top1_right_cosets_on ?piX ?mulX ?pH) = card {e \<in> E'. p' e = x0}" .
      from left_right_coset_card_eq[OF hpiX_grp hpH_sub hpH_grp]
      have hlr: "card (top1_left_cosets_on ?piX ?mulX ?pH) = card (top1_right_cosets_on ?piX ?mulX ?pH)" .
      from hindex[unfolded top1_subgroup_has_index_on_def]
      have "card (top1_left_cosets_on ?piX ?mulX ?pH) = k" by (by100 blast)
      thus ?thesis using hright_card hlr by simp
    qed
    have harc_mult: "card \<A>_E = k * card \<A>_X"
      sorry \<comment> \<open>Needs lifted arc family interface (expert audit2: fix statement first).\<close>
    have hvert_mult: "card ?V_E = k * card ?V_X"
      sorry \<comment> \<open>Needs lifted arc family interface (expert audit2: fix statement first).\<close>
    \<comment> \<open>Step G: Euler formula for E': card S\\_E + card V\\_E = card \\<A>\\_E + 1.\<close>
    have hE'_sub_top: "is_topology_on E' TE'"
      using hE'_strict unfolding is_topology_on_strict_def by (by100 blast)
    \<comment> \<open>h\\<A>\\_E\\_inter, h\\<A>\\_E\\_coh, hT\\_E\\_subgraph, hT\\_E\\_coverage now from graph\\_pi1\\_free\\_weak.\<close>
    have heuler_E: "card S_E + card ?V_E = card \<A>_E + 1"
      by (rule graph_euler_rank[OF hE'_graph hE'_conn he0' h\<A>_E h\<A>_E_cover
          h\<A>_E_inter h\<A>_E_coh hT_E_tree hT_E_sub hT_E_x0 hT_E_subgraph hT_E_coverage
          hNT_E_endpoints hS_E_eq h\<A>_E_fin])
    \<comment> \<open>Step H: Combine.
       card S\\_E = card \\<A>\\_E - card V\\_E + 1
                = k \\<cdot> card \\<A>\\_X - k \\<cdot> card V\\_X + 1
                = k \\<cdot> (card \\<A>\\_X - card V\\_X) + 1
                = k \\<cdot> n + 1.\<close>
    \<comment> \<open>Use int arithmetic to avoid nat subtraction traps.\<close>
    have "int (card S_E) + int (card ?V_E) = int (card \<A>_E) + 1"
      using heuler_E by linarith
    hence "int (card S_E) = int (card \<A>_E) - int (card ?V_E) + 1" by linarith
    also have "... = int (k * card \<A>_X) - int (k * card ?V_X) + 1"
      using harc_mult hvert_mult by simp
    also have "... = int k * (int (card \<A>_X) - int (card ?V_X)) + 1"
      by (simp add: algebra_simps)
    also have "... = int k * int n + 1" using heuler_X_diff by simp
    finally have "int (card S_E) = int (k * n + 1)" by simp
    thus ?thesis by linarith
  qed
  have "finite S_E"
  proof -
    have "card S_E > 0" using \<open>card S_E = k * n + 1\<close> by (by100 linarith)
    thus ?thesis using card_gt_0_iff by (by100 blast)
  qed
  show ?thesis
    using hfreeH_SE \<open>card S_E = k * n + 1\<close> \<open>finite S_E\<close>
    by (by100 blast)
qed

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 



















































































































































































































































































(* Surface classification theorems (§74-78) — moved to end for caching. *)
lemma m_projective_scheme_CW_data:
  assumes "top1_is_m_fold_projective_on X TX m"
      and "x0 \<in> X"
  shows "\<exists>(A :: 'a set) (h :: real \<times> real \<Rightarrow> 'a) (a :: 'a).
      closedin_on X TX A
    \<and> a \<in> A
    \<and> top1_is_wedge_of_circles_on A (subspace_topology X TX A) ({..<m}::nat set) a
    \<and> top1_continuous_map_on top1_B2 top1_B2_topology X TX h
    \<and> h ` top1_S1 \<subseteq> A"
proof -
  from assms(1) have hcases: "(m = 1 \<and> top1_is_dunce_cap_on X TX (2::nat))
      \<or> (2 \<le> m \<and> top1_quotient_of_scheme_on X TX (top1_m_projective_scheme m))"
    unfolding top1_is_m_fold_projective_on_def by (by100 blast)
  show ?thesis
  proof (cases "m = 1")
    case True
    \<comment> \<open>m = 1: X is the dunce cap with n=2 (real projective plane).
       A = q(S1) is a single circle (S1/Z2 \<cong> S1), h = q (quotient map).\<close>
    have hdc: "top1_is_dunce_cap_on X TX (2::nat)"
      using hcases True by (by5000 auto)
    obtain q where hq_quot: "top1_quotient_map_on top1_B2 top1_B2_topology X TX q"
        and hq_S1: "\<forall>z\<in>top1_S1. \<forall>z'\<in>top1_S1.
              q z = q z' \<longleftrightarrow>
              (\<exists>k::nat. k < 2 \<and>
                 z' = (cos (2*pi*real k/real 2) * fst z - sin (2*pi*real k/real 2) * snd z,
                       sin (2*pi*real k/real 2) * fst z + cos (2*pi*real k/real 2) * snd z))"
        and hq_inj: "inj_on q (top1_B2 - top1_S1)"
        and hq_sep: "\<forall>z\<in>top1_B2 - top1_S1. \<forall>z'\<in>top1_S1. q z \<noteq> q z'"
      using hdc unfolding top1_is_dunce_cap_on_def
      apply (elim exE conjE)
      apply (rule that)
      apply assumption+
      done
    \<comment> \<open>A = q(S1): the image of the circle under the quotient map.\<close>
    define A where "A = q ` top1_S1"
    \<comment> \<open>q is continuous B2 \<rightarrow> X (from quotient map).\<close>
    have hq_cont: "top1_continuous_map_on top1_B2 top1_B2_topology X TX q"
      using hq_quot unfolding top1_quotient_map_on_def by (by100 blast)
    \<comment> \<open>Step 1: A is closed in X (image of compact S1 under continuous map to Hausdorff X).\<close>
    have hB2_compact: "top1_compact_on top1_B2 top1_B2_topology" by (rule B2_compact)
    have hX_haus: "is_hausdorff_on X TX"
      by (rule dunce_cap_hausdorff[OF hdc])
    have hS1_closed: "closedin_on top1_B2 top1_B2_topology top1_S1" by (rule S1_closed_in_B2)
    have hA_cl: "closedin_on X TX A"
      unfolding A_def
      by (rule compact_hausdorff_continuous_closed_map[OF hB2_compact hX_haus hq_cont hS1_closed])
    \<comment> \<open>Step 2: A is a wedge of 1 circle (A \<cong> S1).
       S1/Z2 (antipodal identification) is homeomorphic to S1.
       The map z \<mapsto> z^2 (squaring as complex numbers) gives the homeomorphism.\<close>
    \<comment> \<open>Define basepoint a = q(1,0) \<in> A.\<close>
    define a where "a = q (1::real, 0::real)"
    have ha_A: "a \<in> A"
    proof -
      have "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
      thus ?thesis unfolding a_def A_def by (by100 blast)
    qed
    have hA_wedge: "top1_is_wedge_of_circles_on A (subspace_topology X TX A)
        ({..<1}::nat set) a"
    proof -
      let ?TA = "subspace_topology X TX A"
      \<comment> \<open>A \<cong> S1 (from dunce\_cap\_skeleton\_is\_circle).\<close>
      from dunce_cap_skeleton_is_circle[OF hdc hq_quot hq_S1]
      obtain f where hf_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology
          (q ` top1_S1) (subspace_topology X TX (q ` top1_S1)) f" by (by100 blast)
      hence hf_homeo': "top1_homeomorphism_on top1_S1 top1_S1_topology A ?TA f"
        unfolding A_def by (by100 simp)
      have hA_sub: "A \<subseteq> X" using hA_cl unfolding closedin_on_def by (by100 blast)
      have hA_strict: "is_topology_on_strict A ?TA"
      proof -
        have "is_topology_on_strict X TX"
          using hdc unfolding top1_is_dunce_cap_on_def by (by100 blast)
        from subspace_topology_is_strict[OF this hA_sub] show ?thesis .
      qed
      have hA_haus: "is_hausdorff_on A ?TA"
        using conjunct2[OF conjunct2[OF Theorem_17_11]] hX_haus hA_sub by (by100 blast)
      \<comment> \<open>Build the wedge structure: C(0) = A.\<close>
      define C :: "nat \<Rightarrow> 'a set" where "C = (\<lambda>_. A)"
      have hC_props: "\<forall>j\<in>{..<1::nat}. C j \<subseteq> A \<and> a \<in> C j \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology (C j) ?TA h)"
        unfolding C_def using ha_A hf_homeo' by (by100 blast)
      moreover have "(\<Union>a\<in>{..<1::nat}. C a) = A"
      proof -
        have "{..<1::nat} = {0}" by (by100 auto)
        thus ?thesis unfolding C_def by (by100 simp)
      qed
      moreover have "\<forall>j\<in>{..<1::nat}. \<forall>k\<in>{..<1::nat}. j \<noteq> k \<longrightarrow> C j \<inter> C k = {a}"
      proof (intro ballI impI)
        fix j' k' :: nat assume "j' \<in> {..<1}" "k' \<in> {..<1}" "j' \<noteq> k'"
        hence "j' = 0" "k' = 0" by (by100 simp)+
        thus "C j' \<inter> C k' = {a}" using \<open>j' \<noteq> k'\<close> by (by100 simp)
      qed
      moreover have "\<forall>D. D \<subseteq> A \<longrightarrow>
          (closedin_on A ?TA D \<longleftrightarrow> (\<forall>j\<in>{..<1::nat}. closedin_on (C j) ?TA (C j \<inter> D)))"
      proof -
        \<comment> \<open>With C(0) = A and {..<1} = {0}, the condition reduces to:
           D closed in A iff A \<inter> D closed in A. Since D \<subseteq> A, A \<inter> D = D.\<close>
        have hC0: "C 0 = A" unfolding C_def by (by100 simp)
        have hone: "{..<1::nat} = {0}" by (by100 auto)
        show ?thesis
        proof (intro allI impI iffI ballI)
          fix D j assume "D \<subseteq> A" "closedin_on A ?TA D" "j \<in> {..<1::nat}"
          hence "j = 0" by (by100 simp)
          hence "C j \<inter> D = D" using \<open>D \<subseteq> A\<close> hC0 by (by100 blast)
          thus "closedin_on (C j) ?TA (C j \<inter> D)" using \<open>closedin_on A ?TA D\<close> \<open>j = 0\<close> hC0 by (by100 simp)
        next
          fix D assume "D \<subseteq> A" "\<forall>j\<in>{..<1::nat}. closedin_on (C j) ?TA (C j \<inter> D)"
          hence "closedin_on (C 0) ?TA (C 0 \<inter> D)" unfolding hone by (by100 simp)
          have "C 0 \<inter> D = D" using \<open>D \<subseteq> A\<close> hC0 by (by100 blast)
          thus "closedin_on A ?TA D" using \<open>closedin_on (C 0) ?TA (C 0 \<inter> D)\<close> hC0 \<open>C 0 \<inter> D = D\<close>
            by (by100 simp)
        qed
      qed
      ultimately have hcoh_and_cover_and_disj:
        "(\<forall>D. D \<subseteq> A \<longrightarrow> (closedin_on A ?TA D \<longleftrightarrow> (\<forall>j\<in>{..<1::nat}. closedin_on (C j) ?TA (C j \<inter> D))))
       \<and> (\<Union>j\<in>{..<1::nat}. C j) = A
       \<and> (\<forall>j\<in>{..<1::nat}. \<forall>k\<in>{..<1::nat}. j \<noteq> k \<longrightarrow> C j \<inter> C k = {a})"
        by (by100 blast)
      have "top1_is_wedge_of_circles_on A ?TA ({..<1}::nat set) a"
        unfolding top1_is_wedge_of_circles_on_def
      proof (intro conjI)
        show "is_topology_on_strict A ?TA" by (rule hA_strict)
        show "is_hausdorff_on A ?TA" by (rule hA_haus)
        show "a \<in> A" by (rule ha_A)
        show "\<exists>Ca. (\<forall>j\<in>{..<1::nat}. Ca j \<subseteq> A \<and> a \<in> Ca j \<and>
            (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology (Ca j)
                  (subspace_topology A ?TA (Ca j)) h))
          \<and> (\<Union>j\<in>{..<1::nat}. Ca j) = A
          \<and> (\<forall>j\<in>{..<1::nat}. \<forall>k\<in>{..<1::nat}. j \<noteq> k \<longrightarrow> Ca j \<inter> Ca k = {a})
          \<and> (\<forall>D. D \<subseteq> A \<longrightarrow> (closedin_on A ?TA D \<longleftrightarrow>
              (\<forall>j\<in>{..<1::nat}. closedin_on (Ca j) (subspace_topology A ?TA (Ca j)) (Ca j \<inter> D))))"
        proof -
          \<comment> \<open>Key: subspace\_topology A TA A = TA when TA is topology on A.\<close>
          have hTA_sub: "?TA \<subseteq> Pow A"
            using hA_strict unfolding is_topology_on_strict_def by (by100 blast)
          have hTA_self: "subspace_topology A ?TA A = ?TA"
          proof (rule set_eqI, rule iffI)
            fix U assume "U \<in> subspace_topology A ?TA A"
            then obtain V where "V \<in> ?TA" "U = A \<inter> V" unfolding subspace_topology_def by (by100 blast)
            have "V \<subseteq> A" using \<open>V \<in> ?TA\<close> hTA_sub by (by100 blast)
            hence "A \<inter> V = V" by (by100 blast)
            thus "U \<in> ?TA" using \<open>V \<in> ?TA\<close> \<open>U = A \<inter> V\<close> by (by100 simp)
          next
            fix U assume "U \<in> ?TA"
            have "U \<subseteq> A" using \<open>U \<in> ?TA\<close> hTA_sub by (by100 blast)
            hence "A \<inter> U = U" by (by100 blast)
            have "\<exists>V. V \<in> ?TA \<and> U = A \<inter> V" using \<open>U \<in> ?TA\<close> \<open>A \<inter> U = U\<close> by (by100 blast)
            thus "U \<in> subspace_topology A ?TA A" unfolding subspace_topology_def by (by100 blast)
          qed
          have hCj_eq: "\<And>j. j \<in> {..<1::nat} \<Longrightarrow> subspace_topology A ?TA (C j) = ?TA"
            unfolding C_def using hTA_self by (by100 simp)
          hence hC_match: "\<forall>j\<in>{..<1::nat}. C j \<subseteq> A \<and> a \<in> C j \<and>
              (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology (C j)
                    (subspace_topology A ?TA (C j)) h)"
            using hC_props by (by100 simp)
          \<comment> \<open>Similarly for coherent topology.\<close>
          have hcoh_match: "\<forall>D. D \<subseteq> A \<longrightarrow> (closedin_on A ?TA D \<longleftrightarrow>
              (\<forall>j\<in>{..<1::nat}. closedin_on (C j) (subspace_topology A ?TA (C j)) (C j \<inter> D)))"
            using hcoh_and_cover_and_disj \<open>\<And>j. j \<in> {..<1::nat} \<Longrightarrow> subspace_topology A ?TA (C j) = ?TA\<close>
            by (by100 simp)
          show ?thesis
            apply (rule exI[of _ C])
            using hC_match hcoh_and_cover_and_disj hcoh_match by (by5000 blast)
        qed
      qed
      thus ?thesis .
    qed
    \<comment> \<open>Step 4: q(S1) \<subseteq> A by definition.\<close>
    have hq_S1_A: "q ` top1_S1 \<subseteq> A" unfolding A_def by (by100 blast)
    \<comment> \<open>Match: {..<m} = {..<1} since m = 1.\<close>
    have hm1: "({..<m}::nat set) = {..<1}" using True by (by100 simp)
    show ?thesis unfolding hm1
      apply (rule exI[of _ A], rule exI[of _ q], rule exI[of _ a])
      apply (intro conjI)
      apply (rule hA_cl)
      apply (rule ha_A)
      apply (rule hA_wedge)
      apply (rule hq_cont)
      apply (rule hq_S1_A)
      done
  next
    case False
    \<comment> \<open>m \<ge> 2: X is a quotient of the projective scheme.
       Use scheme\_quotient\_CW\_data to extract CW structure.
       Then show the 1-skeleton is a wedge of m circles.\<close>
    have hm2: "2 \<le> m" using hcases False by (by100 blast)
    have hscheme: "top1_quotient_of_scheme_on X TX (top1_m_projective_scheme m)"
      using hcases False by (by100 blast)
    let ?scheme = "top1_m_projective_scheme m"
    have hlen: "length ?scheme \<ge> 3"
    proof -
      have "length ?scheme = 2 * m"
        unfolding top1_m_projective_scheme_def
        by (induction m, simp, simp)
      thus ?thesis using hm2 by (by100 simp)
    qed
    \<comment> \<open>Vertex connectivity for projective scheme.\<close>
    have hvc: "\<forall>(q::real\<times>real\<Rightarrow>'a) (vx::nat\<Rightarrow>real) (vy::nat\<Rightarrow>real).
        (\<forall>i<length ?scheme. \<forall>j<length ?scheme.
          fst (?scheme!i) = fst (?scheme!j) \<longrightarrow>
          (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length ?scheme),
             (1-t) * vy i + t * vy (Suc i mod length ?scheme))
           = (if snd (?scheme!i) = snd (?scheme!j)
              then q ((1-t) * vx j + t * vx (Suc j mod length ?scheme),
                      (1-t) * vy j + t * vy (Suc j mod length ?scheme))
              else q (t * vx j + (1-t) * vx (Suc j mod length ?scheme),
                      t * vy j + (1-t) * vy (Suc j mod length ?scheme)))))
        \<longrightarrow> (\<forall>i<length ?scheme. \<forall>j<length ?scheme. q (vx i, vy i) = q (vx j, vy j))"
      using projective_scheme_vertex_connectivity[OF hm2] by (by100 simp)
    \<comment> \<open>Extract CW data from scheme.\<close>
    obtain A0 h0 where
        hA0_cl: "closedin_on X TX A0"
        and hh0_cont: "top1_continuous_map_on top1_B2 top1_B2_topology X TX h0"
        and hh0_S1: "h0 ` top1_S1 \<subseteq> A0"
    proof -
      from scheme_quotient_CW_data[OF hscheme hlen hvc]
      show ?thesis
        apply (elim exE conjE)
        apply (rule that)
        apply assumption+
        done
    qed
    \<comment> \<open>Step: Show A0 is a wedge of m circles.
       For the projective scheme a1a1a2a2...amam:
       - Each label i gives a circle C(i) = image of edge 2i under q0.
       - Edges 2i and 2i+1 have the same label and direction, so they're identified.
       - All vertices map to a0. Each C(i) starts and ends at a0, forming a circle.
       - Different labels give circles sharing only a0.\<close>
    have hA0_wedge: "\<exists>a0. a0 \<in> A0 \<and> top1_is_wedge_of_circles_on A0 (subspace_topology X TX A0) ({..<m}::nat set) a0"
      sorry \<comment> \<open>1-skeleton of projective scheme quotient is wedge of m circles.\<close>
    then obtain a0 where ha0_A: "a0 \<in> A0"
        and ha0_wedge: "top1_is_wedge_of_circles_on A0 (subspace_topology X TX A0) ({..<m}::nat set) a0"
      by (by100 blast)
    show ?thesis
      apply (rule exI[of _ A0], rule exI[of _ h0], rule exI[of _ a0])
      apply (intro conjI)
      apply (rule hA0_cl)
      apply (rule ha0_A)
      apply (rule ha0_wedge)
      apply (rule hh0_cont)
      apply (rule hh0_S1)
      done
  qed
qed



(** Theorem 71.3: fully proved and cached in ac9/AlgTopCached9.thy. **)




\<comment> \<open>free\_group\_hom\_subset\_injective + Theorem\_71\_3\_pi1\_free moved to AlgTopCached9.\<close>


\<comment> \<open>Theorem 71.3 (book-faithful) is now Theorem\_71\_3 in AlgTopCached9.
   It states: \\<pi>\\_1(X, p) is free on J (the actual book statement).
   The old int-set packaging wrapper (Theorem\_71\_3\_wedge\_of\_circles\_general)
   was unused dead code and has been removed.\<close>





\<comment> \<open>§71 helpers + §74 moved to AlgTopCached8.\<close>

\<comment> \<open>Elementary scheme operations (Munkres \\<S>76).
   A scheme is a list of (edge\\_name, direction) pairs representing a polygonal identification.
   Elementary operations preserve the quotient homeomorphism type.\<close>

definition top1_inverse_edge :: "'a \<times> bool \<Rightarrow> 'a \<times> bool" where
  "top1_inverse_edge e = (fst e, \<not> snd e)"

inductive top1_elementary_scheme_operation :: "('a \<times> bool) list \<Rightarrow> ('a \<times> bool) list \<Rightarrow> bool" where
  rotate: "top1_elementary_scheme_operation (u @ v) (v @ u)" |
  cancel: "top1_elementary_scheme_operation (u @ [a, top1_inverse_edge a] @ v) (u @ v)" |
  uncancel: "top1_elementary_scheme_operation (u @ v) (u @ [a, top1_inverse_edge a] @ v)" |
  invert: "top1_elementary_scheme_operation w (rev (map top1_inverse_edge w))"

\<comment> \<open>The scheme equivalence is the reflexive-transitive closure of elementary operations.\<close>
definition top1_scheme_equiv :: "('a \<times> bool) list \<Rightarrow> ('a \<times> bool) list \<Rightarrow> bool" where
  "top1_scheme_equiv = top1_elementary_scheme_operation\<^sup>*\<^sup>*"

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
  \<comment> \<open>Prove the strong version: for ALL quotient spaces of related schemes, homeo.\<close>
  have hcases: "\<And>s t. top1_elementary_scheme_operation s t \<Longrightarrow>
      top1_quotient_of_scheme_on X1 TX1 s \<Longrightarrow>
      top1_quotient_of_scheme_on X2 TX2 t \<Longrightarrow>
      \<exists>h. top1_homeomorphism_on X1 TX1 X2 TX2 h"
  proof -
    fix s t assume hop: "top1_elementary_scheme_operation s t"
        and hs: "top1_quotient_of_scheme_on X1 TX1 s"
        and ht: "top1_quotient_of_scheme_on X2 TX2 t"
    \<comment> \<open>First prove for ANY pair of quotient spaces (needed for sym/trans cases).\<close>
    have huniv: "\<And>s t (Y1 :: 'x set) TY1 (Y2 :: 'x set) TY2.
        top1_elementary_scheme_operation s t \<Longrightarrow>
        is_topology_on_strict Y1 TY1 \<Longrightarrow> is_topology_on_strict Y2 TY2 \<Longrightarrow>
        top1_quotient_of_scheme_on Y1 TY1 s \<Longrightarrow>
        top1_quotient_of_scheme_on Y2 TY2 t \<Longrightarrow>
        \<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
      sorry \<comment> \<open>Induction on elementary\\_scheme\\_operation with 8 cases:
         refl (quotient uniqueness), sym (inverse homeo), trans (composition),
         rotate (cyclic permutation), cancel (edge cancellation),
         relabel (label renaming), invert (reflection), cut (diagonal insertion).
         Each case constructs a homeomorphism between quotient spaces.\<close>
    from huniv[OF hop assms(1) assms(2) hs ht]
    show "\<exists>h. top1_homeomorphism_on X1 TX1 X2 TX2 h" .
  qed
  show ?thesis using hcases[OF assms(3)] assms(4) by (by100 blast)
qed



\<comment> \<open>§75 + §73 + §74.4 moved to AlgTopCached8.\<close>

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
  \<comment> \<open>Step 1: By Theorem 74.4, \<pi>_1(P_m) has presentation.\<close>
  note h74_4 = Theorem_74_4_fund_group_m_projective[OF assms]
  \<comment> \<open>Step 2: Abelianize. The relator a_1^2...a_m^2 maps to 2(a_1+...+a_m).
     Smith normal form: torsion = Z/2Z, free part = Z^{m-1}.\<close>
  show ?thesis using h74_4 sorry \<comment> \<open>Abelianization + Smith normal form (uses 74.4 presentation).\<close>
qed
section \<open>*\<S>78 Constructing Compact Surfaces\<close>


\<comment> \<open>standard\_simplex moved to AlgTopCached8.\<close>


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
  show ?thesis
  proof -
    \<comment> \<open>Munkres 78.1: Place disjoint copies of standard 2-simplex in the plane.
       The triangulation gives a finite set of triangles with edge identifications.
       Define q by pasting the copies via the identification maps.\<close>
    show ?thesis sorry \<comment> \<open>Disjoint simplex copies + pasting construction.\<close>
  qed
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
  show ?thesis
  proof -
    \<comment> \<open>Munkres 78.2: Iterative merging along spanning tree of dual graph.
       The dual graph has triangles as vertices, edges where triangles share an edge.
       Since X is connected, the dual graph is connected.
       Walk a spanning tree, merging triangles along shared edges at each step.\<close>
    show ?thesis sorry \<comment> \<open>Iterative merging construction.\<close>
  qed
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
  \<comment> \<open>AUDIT NOTE (B03): The predicates top1\\_is\\_torus\\_scheme,
     top1\\_is\\_projective\\_scheme, top1\\_elementary\\_scheme\\_equiv are not yet
     defined in the active source tree. They are placeholders inside a sorry block.
     They should be defined as: torus scheme = a1 b1 a1\\<inverse> b1\\<inverse> ... an bn an\\<inverse> bn\\<inverse>,
     projective scheme = a1 a1 ... am am, and scheme\\_equiv = rtranclp of elementary moves.\<close>
  have hreduced: "(\<exists>w. scheme = w \<and> (\<forall>a\<in>set w. snd a) \<and> length w = 0)
      \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n
            \<and> top1_elementary_scheme_equiv scheme w)
      \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m
            \<and> top1_elementary_scheme_equiv scheme w)"
    sorry \<comment> \<open>Reduction to normal form via elementary operations (Theorem 76).\<close>
  \<comment> \<open>Step 3: Each normal form corresponds to the standard surface.\<close>
  show ?thesis sorry \<comment> \<open>Normal form → homeomorphism type (S², T_n, or P_m).\<close>
qed


end
