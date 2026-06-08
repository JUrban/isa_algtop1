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
        proof -
          \<comment> \<open>h = k*g. k = class(p\\<circ>\\<alpha>\\<tilde>), g = class(fg).
             mulB(k,g) = class((p\\<circ>\\<alpha>\\<tilde>)*fg) by fundamental\\_group\\_mul\\_class.
             fh \\<in> h = class((p\\<circ>\\<alpha>\\<tilde>)*fg) means fh ~ (p\\<circ>\\<alpha>\\<tilde>)*fg.\<close>
          have hk_class: "k = {f'. top1_loop_equiv_on B TB b0 (\<lambda>t. p (\<alpha>_tilde t)) f'}"
            using h\<alpha>(2) .
          have hg_class_loc: "g = {f'. top1_loop_equiv_on B TB b0 fg f'}"
          proof -
            from hg obtain f0 where "top1_is_loop_on B TB b0 f0"
                "g = {f'. top1_loop_equiv_on B TB b0 f0 f'}"
              unfolding top1_fundamental_group_carrier_def by (by100 blast)
            have "top1_loop_equiv_on B TB b0 f0 fg" using hfg(1) \<open>g = _\<close> by (by100 blast)
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
          have h_pa_loop: "top1_is_loop_on B TB b0 (\<lambda>t. p (\<alpha>_tilde t))"
          proof -
            have hp_cont: "top1_continuous_map_on E TE B TB p"
              using assms(1) unfolding top1_covering_map_on_def top1_evenly_covered_on_def by (by5000 blast)
            from top1_continuous_map_on_comp[OF
                h\<alpha>_path[unfolded top1_is_path_on_def, THEN conjunct1] hp_cont]
            have "top1_continuous_map_on I_set I_top B TB (p \<circ> \<alpha>_tilde)" .
            moreover have "(p \<circ> \<alpha>_tilde) 0 = b0"
              using h\<alpha>_path assms(5) unfolding top1_is_path_on_def comp_def by (by100 simp)
            moreover have "(p \<circ> \<alpha>_tilde) 1 = b0"
              using h\<alpha>_path assms(5) unfolding top1_is_path_on_def comp_def by (by100 simp)
            ultimately have "top1_is_path_on B TB b0 b0 (p \<circ> \<alpha>_tilde)"
              unfolding top1_is_path_on_def by (by100 blast)
            thus ?thesis unfolding top1_is_loop_on_def comp_def .
          qed
          from top1_fundamental_group_mul_class[OF assms(3) h_pa_loop hfg(2)]
          have hmul_class: "?mulB {f'. top1_loop_equiv_on B TB b0 (\<lambda>t. p (\<alpha>_tilde t)) f'}
              {f'. top1_loop_equiv_on B TB b0 fg f'}
              = {f'. top1_loop_equiv_on B TB b0 ?pafg f'}" .
          hence "h = {f'. top1_loop_equiv_on B TB b0 ?pafg f'}"
            using \<open>h = ?mulB k g\<close> hk_class hg_class_loc by simp
          hence "fh \<in> {f'. top1_loop_equiv_on B TB b0 ?pafg f'}" using hfh(1) by simp
          hence "top1_loop_equiv_on B TB b0 ?pafg fh" by (by100 blast)
          hence "top1_path_homotopic_on B TB b0 b0 ?pafg fh"
            unfolding top1_loop_equiv_on_def by (by100 blast)
          from Lemma_51_1_path_homotopic_sym[OF this] show ?thesis .
        qed
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
proof -
  assume hH_eq: "(top1_fundamental_group_induced_on E TE e0 B TB b0 p)
      ` top1_fundamental_group_carrier E TE e0
     = top1_fundamental_group_image_hom E TE e0 B TB b0 p"
  let ?H = "top1_fundamental_group_image_hom E TE e0 B TB b0 p"
  let ?fclass = "{g. top1_loop_equiv_on B TB b0 f g}"
  have hp_cont: "top1_continuous_map_on E TE B TB p"
    using assms(1) unfolding top1_covering_map_on_def by (by100 blast)
  show "(?fclass \<in> ?H) = (\<exists>ft. top1_is_loop_on E TE e0 ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s))"
  proof (rule iffI)
    \<comment> \<open>(\\<Rightarrow>) [f] \\<in> H = p*(\\<pi>\\_1(E)). So \\<exists>[\\<alpha>] \\<in> \\<pi>\\_1(E). p*([\\<alpha>]) = [f].
       Lift f from e0: get f\\_tilde with f\\_tilde(1) = ? (unknown a priori).
       \\<alpha> is a lift of p\\<circ>\\<alpha>. f ~ p\\<circ>\\<alpha>. By Thm 54.3: f\\_tilde(1) = \\<alpha>(1) = e0.
       So f\\_tilde is a loop.\<close>
    assume hfH: "?fclass \<in> ?H"
    \<comment> \<open>[f] \\<in> p*(\\<pi>\\_1(E)) \\<Rightarrow> \\<exists>\\<alpha> loop at e0 with f ~ p \\<circ> \\<alpha>.\<close>
    have "\<exists>\<alpha>. top1_is_loop_on E TE e0 \<alpha> \<and> top1_loop_equiv_on B TB b0 f (p \<circ> \<alpha>)"
    proof -
      \<comment> \<open>[f] \\<in> H = induced ` carrier. Extract c \\<in> carrier with induced(c) = [f].\<close>
      from hfH[unfolded hH_eq[symmetric]]
      obtain c where hc_carr: "c \<in> top1_fundamental_group_carrier E TE e0"
          and hc_ind: "top1_fundamental_group_induced_on E TE e0 B TB b0 p c = ?fclass"
        by (by100 blast)
      \<comment> \<open>c = [\\<alpha>] for some loop \\<alpha> at e0.\<close>
      from hc_carr obtain \<alpha> where h\<alpha>_loop: "top1_is_loop_on E TE e0 \<alpha>"
          and h\<alpha>_class: "c = {g. top1_loop_equiv_on E TE e0 \<alpha> g}"
        unfolding top1_fundamental_group_carrier_def by (by100 blast)
      \<comment> \<open>\\<alpha> \\<in> c (reflexivity).\<close>
      have "\<alpha> \<in> c" using h\<alpha>_class top1_loop_equiv_on_refl[OF h\<alpha>_loop] by (by100 blast)
      \<comment> \<open>f \\<in> induced(c) = [f] (reflexivity of loop\\_equiv for f).\<close>
      have hf_in_fclass: "f \<in> ?fclass"
        using top1_loop_equiv_on_refl[OF assms(6)] by (by100 blast)
      hence "f \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p c"
        using hc_ind by simp
      \<comment> \<open>Unfolding induced: \\<exists>f'\\<in>c. loop\\_equiv(p \\<circ> f', f).\<close>
      then obtain f' where "f' \<in> c" "top1_loop_equiv_on B TB b0 (p \<circ> f') f"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      \<comment> \<open>f' \\<in> c = [\\<alpha>], so f' ~ \\<alpha>. p preserves equiv: p \\<circ> f' ~ p \\<circ> \\<alpha>.\<close>
      have "top1_loop_equiv_on E TE e0 \<alpha> f'" using \<open>f' \<in> c\<close> h\<alpha>_class by (by100 blast)
      have hf'_loop: "top1_is_loop_on E TE e0 f'"
        using \<open>top1_loop_equiv_on E TE e0 \<alpha> f'\<close> unfolding top1_loop_equiv_on_def by (by100 blast)
      from top1_induced_preserves_loop_equiv[OF assms(2) hp_cont h\<alpha>_loop hf'_loop
          \<open>top1_loop_equiv_on E TE e0 \<alpha> f'\<close>]
      have "top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>) (p \<circ> f')" using assms(5) by simp
      \<comment> \<open>p \\<circ> \\<alpha> ~ p \\<circ> f' and p \\<circ> f' ~ f (from above). By transitivity: p \\<circ> \\<alpha> ~ f.\<close>
      from top1_loop_equiv_on_trans[OF assms(3) this \<open>top1_loop_equiv_on B TB b0 (p \<circ> f') f\<close>]
      have "top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>) f" .
      from top1_loop_equiv_on_sym[OF this]
      have "top1_loop_equiv_on B TB b0 f (p \<circ> \<alpha>)" .
      thus ?thesis using h\<alpha>_loop by (by100 blast)
    qed
    then obtain \<alpha> where h\<alpha>: "top1_is_loop_on E TE e0 \<alpha>"
        "top1_loop_equiv_on B TB b0 f (p \<circ> \<alpha>)" by (by100 blast)
    \<comment> \<open>f is a loop at b0 (path from b0 to b0). Lift f from e0.\<close>
    have hf_path: "top1_is_path_on B TB b0 b0 f"
      using assms(6) unfolding top1_is_loop_on_def .
    from Lemma_54_1_path_lifting[OF assms(1) assms(4) assms(5) hf_path assms(3) assms(2)]
    obtain ftilde where hft: "top1_is_path_on E TE e0 (ftilde 1) ftilde"
        "\<forall>s\<in>I_set. p (ftilde s) = f s" by (by100 blast)
    \<comment> \<open>\\<alpha> is a path from e0 to e0 (loop) in E. p \\<circ> \\<alpha> is a loop at b0.
       f ~ p \\<circ> \\<alpha> (loop-equivalent). By Theorem 54.3:
       the lift of f (= ftilde) and the lift of p\\<circ>\\<alpha> (= \\<alpha>) end at the same point.
       \\<alpha> ends at e0 (loop). So ftilde ends at e0.\<close>
    have h\<alpha>_path: "top1_is_path_on E TE e0 e0 \<alpha>"
      using h\<alpha>(1) unfolding top1_is_loop_on_def .
    have hp\<alpha>_path: "top1_is_path_on B TB b0 b0 (p \<circ> \<alpha>)"
    proof -
      from top1_continuous_map_loop_early[OF hp_cont h\<alpha>(1)]
      show ?thesis using assms(5) unfolding top1_is_loop_on_def by simp
    qed
    have hp\<alpha>_lift: "\<forall>s\<in>I_set. p (\<alpha> s) = (p \<circ> \<alpha>) s" by simp
    \<comment> \<open>f ~ p \\<circ> \\<alpha> (from h\\<alpha>(2)). By Thm 54.3: ftilde(1) = \\<alpha>(1) = e0.\<close>
    have hf_homotopic_p\<alpha>: "top1_path_homotopic_on B TB b0 b0 f (p \<circ> \<alpha>)"
      using h\<alpha>(2) unfolding top1_loop_equiv_on_def by (by100 blast)
    from Theorem_54_3[OF assms(1) assms(2) assms(3) assms(4) assms(5)
        hf_path hp\<alpha>_path hf_homotopic_p\<alpha> hft(1) hft(2) h\<alpha>_path hp\<alpha>_lift]
    have "ftilde 1 = e0" by (by100 blast)
    hence "top1_is_loop_on E TE e0 ftilde"
      using hft(1) unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    thus "\<exists>ft. top1_is_loop_on E TE e0 ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s)"
      using hft(2) by (by100 blast)
  next
    \<comment> \<open>(\\<Leftarrow>) ft loop at e0, p \\<circ> ft = f on I\\_set \\<Rightarrow> [f] \\<in> H.\<close>
    assume "\<exists>ft. top1_is_loop_on E TE e0 ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s)"
    then obtain ft where hft: "top1_is_loop_on E TE e0 ft" "\<forall>s\<in>I_set. p (ft s) = f s"
      by (by100 blast)
    \<comment> \<open>[ft] \\<in> \\<pi>\\_1(E). p*([ft]) = [p \\<circ> ft] = [f]. So [f] \\<in> H.\<close>
    have hft_class: "{g. top1_loop_equiv_on E TE e0 ft g} \<in>
        top1_fundamental_group_carrier E TE e0"
      unfolding top1_fundamental_group_carrier_def using hft(1) by (by100 blast)
    \<comment> \<open>p \\<circ> ft is a loop at b0, and p \\<circ> ft = f on I\\_set \\<Rightarrow> [p \\<circ> ft] = [f].\<close>
    have hpft_loop: "top1_is_loop_on B TB b0 (p \<circ> ft)"
      using top1_continuous_map_loop_early[OF hp_cont hft(1)] assms(5) by simp
    have hpft_agree: "\<forall>s\<in>I_set. f s = (p \<circ> ft) s" using hft(2) by (by100 auto)
    from conjunct2[OF loop_agree_on_I[OF hpft_loop hpft_agree]]
    have "top1_path_homotopic_on B TB b0 b0 (p \<circ> ft) f" .
    hence hpft_equiv_f: "top1_loop_equiv_on B TB b0 (p \<circ> ft) f"
      unfolding top1_loop_equiv_on_def using hpft_loop assms(6) by (by100 blast)
    \<comment> \<open>p*([ft]) = {g. \\<exists>f'\\<in>[ft]. loop\\_equiv (p \\<circ> f') g}.\<close>
    \<comment> \<open>Since ft \\<in> [ft] and loop\\_equiv (p \\<circ> ft) f, we have f \\<in> p*([ft]).\<close>
    \<comment> \<open>Hence [f] = p*([ft]) (they share element f, and equiv classes are equal or disjoint).\<close>
    have "f \<in> (top1_fundamental_group_induced_on E TE e0 B TB b0 p)
        {g. top1_loop_equiv_on E TE e0 ft g}"
      unfolding top1_fundamental_group_induced_on_def
    proof -
      have hft_path: "top1_is_path_on E TE e0 e0 ft"
        using hft(1) unfolding top1_is_loop_on_def .
      have "top1_loop_equiv_on E TE e0 ft ft"
        unfolding top1_loop_equiv_on_def
        using hft(1) Lemma_51_1_path_homotopic_refl[OF hft_path] by (by100 blast)
      hence "ft \<in> {g. top1_loop_equiv_on E TE e0 ft g}" by (by100 blast)
      moreover have "top1_loop_equiv_on B TB b0 (p \<circ> ft) f" using hpft_equiv_f .
      ultimately show "f \<in> {g. \<exists>f'\<in>{g. top1_loop_equiv_on E TE e0 ft g}.
          top1_loop_equiv_on B TB b0 (p \<circ> f') g}" by (by100 blast)
    qed
    \<comment> \<open>p*([ft]) \\<in> H (from hH\\_eq). f \\<in> p*([ft]). [f] = p*([ft]) (since both are equiv classes
       containing f). Hence [f] \\<in> H.\<close>
    \<comment> \<open>p*([ft]) \\<in> carrier(B) and \\<in> ?H. f \\<in> p*([ft]).
       p*([ft]) is an equiv class in carrier. Extract its representative f'.
       Then loop\\_equiv f' f (from f \\<in> class). And loop\\_equiv f g \\<Leftrightarrow> loop\\_equiv f' g.
       So ?fclass = p*([ft]).\<close>
    let ?pft = "top1_fundamental_group_induced_on E TE e0 B TB b0 p
        {g. top1_loop_equiv_on E TE e0 ft g}"
    have "?pft \<in> ?H" using hH_eq hft_class by (by100 blast)
    have "?pft \<in> top1_fundamental_group_carrier B TB b0"
    proof -
      have "b0 \<in> B"
      proof -
        have "p e0 \<in> B" using hp_cont assms(4) unfolding top1_continuous_map_on_def by (by100 blast)
        thus ?thesis using assms(5) by simp
      qed
      from top1_fundamental_group_induced_on_is_hom[OF assms(2) assms(3) assms(4) \<open>b0 \<in> B\<close> hp_cont assms(5)]
      have "top1_group_hom_on (top1_fundamental_group_carrier E TE e0)
          (top1_fundamental_group_mul E TE e0)
          (top1_fundamental_group_carrier B TB b0) (top1_fundamental_group_mul B TB b0)
          (top1_fundamental_group_induced_on E TE e0 B TB b0 p)" .
      thus ?thesis using hft_class unfolding top1_group_hom_on_def by (by100 blast)
    qed
    then obtain f' where "top1_is_loop_on B TB b0 f'"
        "?pft = {h. top1_loop_equiv_on B TB b0 f' h}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have "f \<in> ?pft"
      using \<open>f \<in> (top1_fundamental_group_induced_on E TE e0 B TB b0 p)
          {g. top1_loop_equiv_on E TE e0 ft g}\<close> .
    hence "top1_loop_equiv_on B TB b0 f' f"
      using \<open>?pft = {h. top1_loop_equiv_on B TB b0 f' h}\<close> by (by100 blast)
    have "?fclass = ?pft"
    proof (rule set_eqI, rule iffI)
      fix g assume "g \<in> ?fclass"
      hence "top1_loop_equiv_on B TB b0 f g" by (by100 blast)
      from top1_loop_equiv_on_trans[OF assms(3) \<open>top1_loop_equiv_on B TB b0 f' f\<close> this]
      have "top1_loop_equiv_on B TB b0 f' g" .
      thus "g \<in> ?pft" using \<open>?pft = {h. _}\<close> by (by100 blast)
    next
      fix g assume "g \<in> ?pft"
      hence "top1_loop_equiv_on B TB b0 f' g" using \<open>?pft = {h. _}\<close> by (by100 blast)
      from top1_loop_equiv_on_sym[OF \<open>top1_loop_equiv_on B TB b0 f' f\<close>]
      have "top1_loop_equiv_on B TB b0 f f'" .
      from top1_loop_equiv_on_trans[OF assms(3) this \<open>top1_loop_equiv_on B TB b0 f' g\<close>]
      show "g \<in> ?fclass" by (by100 blast)
    qed
    thus "?fclass \<in> ?H" using \<open>?pft \<in> ?H\<close> by simp
  qed
qed

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


\<comment> \<open>Expert audit3: combinatorial leaf existence for finite acyclic connected graphs.
   Purely combinatorial: no topology. Used to break circular dependency with tree\\_euler.\<close>

\<comment> \<open>A finite connected acyclic multigraph (given by vertices V, edge set E as triples
   (u,v,e) where e is an edge label and u,v are its endpoints) has a leaf vertex
   (degree 1) when |E| \\<ge> 1.

   Proof sketch: by strong induction on |E|.
   For |E|=1: the single edge has 2 endpoints, both of degree 1.
   For |E|>1: if a leaf exists, done. Otherwise all degrees \\<ge> 2.
   Connected acyclic with |E| edges has |E|+1 vertices (proved separately by induction
   with leaf removal — breaking circularity by proving leaf+Euler simultaneously).
   Sum of degrees = 2|E| = 2(|V|-1) < 2|V|. Contradiction with all degrees \\<ge> 2.

   We prove a combined statement: acyclic connected finite graph with \\<ge> 1 edge
   satisfies |V| = |E| + 1 AND has a leaf.\<close>

\<comment> \<open>For our purposes: the "graph" is abstracted as a finite set of edges E,
   each edge e has two distinct endpoints ep1(e) and ep2(e) in some set V.
   V = \\<Union>{{ep1(e), ep2(e)} | e \\<in> E}.
   Connected: for any two vertices, there's a path through edges.
   Acyclic: no sequence of distinct edges forms a cycle.
   Leaf: a vertex v with exactly one edge incident.\<close>

\<comment> \<open>Double counting: \\<Sum>v\\<in>V. card{A\\<in>E. v\\<in>f(A)} = \\<Sum>A\\<in>E. card(f(A)),
   where V = \\<Union>(f ` E). Both sides count incidence pairs.\<close>
lemma double_counting_sum:
  fixes E :: "'e set" and f :: "'e \<Rightarrow> 'v set" and V :: "'v set"
  assumes hfin_E: "finite E"
      and hfin_f: "\<forall>A\<in>E. finite (f A)"
      and hV: "V = (\<Union>A\<in>E. f A)"
  shows "(\<Sum>v\<in>V. card {A \<in> E. v \<in> f A}) = (\<Sum>A\<in>E. card (f A))"
proof -
  have hfin_V: "finite V" using hV hfin_E hfin_f by (by100 blast)
  \<comment> \<open>LHS = card(Sigma V (\\<lambda>v. {A \\<in> E. v \\<in> f A})). RHS = card(Sigma E f).
     Both = |{(v,A) | A \\<in> E \\<and> v \\<in> f(A)}|.\<close>
  have hfin_vA: "\<forall>v\<in>V. finite {A \<in> E. v \<in> f A}" using hfin_E by (by100 simp)
  \<comment> \<open>LHS as sum over Sigma.\<close>
  have "(\<Sum>v\<in>V. card {A \<in> E. v \<in> f A}) = card (SIGMA v:V. {A \<in> E. v \<in> f A})"
    using card_SigmaI[OF hfin_V hfin_vA] by simp
  \<comment> \<open>RHS as sum over Sigma.\<close>
  also have "card (SIGMA v:V. {A \<in> E. v \<in> f A}) = card (SIGMA A:E. f A)"
  proof (rule bij_betw_same_card[of "\<lambda>(v,A). (A,v)"])
    show "bij_betw (\<lambda>(v,A). (A,v))
        (SIGMA v:V. {A \<in> E. v \<in> f A}) (SIGMA A:E. f A)"
      unfolding bij_betw_def
    proof (intro conjI)
      show "inj_on (\<lambda>(v,A). (A,v)) (SIGMA v:V. {A \<in> E. v \<in> f A})"
        unfolding inj_on_def by (by100 auto)
      show "(\<lambda>(v, A). (A, v)) ` (SIGMA v:V. {A \<in> E. v \<in> f A}) = (SIGMA A:E. f A)"
      proof (rule set_eqI)
        fix p show "p \<in> (\<lambda>(v, A). (A, v)) ` (SIGMA v:V. {A \<in> E. v \<in> f A}) \<longleftrightarrow>
            p \<in> (SIGMA A:E. f A)"
          using hV by (by100 force)
      qed
    qed
  qed
  also have "card (SIGMA A:E. f A) = (\<Sum>A\<in>E. card (f A))"
    using card_SigmaI[OF hfin_E hfin_f] by simp
  finally show ?thesis .
qed

\<comment> \<open>Combinatorial lemma: in a finite graph where sum of degrees = 2*|E|,
   |V| = |E| + 1, and |E| \\<ge> 1, there is a vertex of degree 1 (leaf).
   Proof: if all degrees \\<ge> 2, sum \\<ge> 2|V| = 2(|E|+1) > 2|E|. Contradiction.\<close>
lemma degree_sum_leaf:
  fixes V :: "'v set" and deg :: "'v \<Rightarrow> nat"
  assumes hfin_V: "finite V"
      and hV_card: "card V = n + 1"
      and hn: "n \<ge> 1"
      and hdeg_sum: "(\<Sum>v\<in>V. deg v) = 2 * n"
      and hdeg_pos: "\<forall>v\<in>V. deg v \<ge> 1"
  shows "\<exists>v\<in>V. deg v = 1"
proof (rule ccontr)
  assume "\<not> (\<exists>v\<in>V. deg v = 1)"
  hence "\<forall>v\<in>V. deg v \<noteq> 1" by (by100 blast)
  hence hdeg2: "\<forall>v\<in>V. deg v \<ge> 2" using hdeg_pos by (by100 force)
  have "(\<Sum>v\<in>V. deg v) \<ge> (\<Sum>v\<in>V. (2::nat))"
    by (rule sum_mono) (use hdeg2 in blast)
  moreover have "(\<Sum>v\<in>V. (2::nat)) = 2 * card V" by simp
  ultimately have "(\<Sum>v\<in>V. deg v) \<ge> 2 * card V" by linarith
  hence "2 * n \<ge> 2 * (n + 1)" using hdeg_sum hV_card by linarith
  thus False by (by100 simp)
qed





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
      and "\<forall>C. C \<subseteq> T \<longrightarrow> (closedin_on T TT C \<longleftrightarrow> (\<forall>A\<in>\<A>. closedin_on A (subspace_topology T TT A) (A \<inter> C)))"
  shows "top1_is_tree_on (\<Union>(\<A> - {A0})) (subspace_topology T TT (\<Union>(\<A> - {A0})))
       \<and> (\<forall>C. C \<subseteq> \<Union>(\<A> - {A0}) \<longrightarrow>
           (closedin_on (\<Union>(\<A> - {A0})) (subspace_topology T TT (\<Union>(\<A> - {A0}))) C \<longleftrightarrow>
            (\<forall>A\<in>\<A> - {A0}. closedin_on A (subspace_topology (\<Union>(\<A> - {A0})) (subspace_topology T TT (\<Union>(\<A> - {A0}))) A) (A \<inter> C))))"
proof -
  let ?T' = "\<Union>(\<A> - {A0})" and ?TT' = "subspace_topology T TT (\<Union>(\<A> - {A0}))"
  \<comment> \<open>Coherent closedness for T': derived from assms(10) by restricting to \\<A>-{A0}.\<close>
  have hgraph_T: "top1_is_graph_on T TT"
    using assms(1) unfolding top1_is_tree_on_def by (by100 blast)
  have h\<A>_arcs_all: "\<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)"
    using assms(2) by (by100 blast)
  have hT'_sub: "?T' \<subseteq> T" using assms(2,3) by (by100 blast)
  have h\<B>_coh_raw: "\<forall>C. C \<subseteq> ?T' \<longrightarrow>
      (closedin_on ?T' (subspace_topology T TT ?T') C \<longleftrightarrow>
       (\<forall>A\<in>\<A> - {A0}. closedin_on A (subspace_topology T TT A) (A \<inter> C)))"
    using subgraph_coherent_topology[OF hgraph_T h\<A>_arcs_all assms(3) assms(4) assms(10),
      of "\<A> - {A0}" ?T'] by (by5000 blast)
  have h\<B>_coh: "\<forall>C. C \<subseteq> ?T' \<longrightarrow>
      (closedin_on ?T' ?TT' C \<longleftrightarrow>
       (\<forall>A\<in>\<A> - {A0}. closedin_on A (subspace_topology ?T' ?TT' A) (A \<inter> C)))"
  proof (intro allI impI)
    fix C assume hC: "C \<subseteq> ?T'"
    have "\<forall>A\<in>\<A> - {A0}. subspace_topology ?T' ?TT' A = subspace_topology T TT A"
    proof (intro ballI)
      fix A assume "A \<in> \<A> - {A0}"
      hence "A \<subseteq> ?T'" by (by100 blast)
      thus "subspace_topology ?T' ?TT' A = subspace_topology T TT A"
        using subspace_topology_trans[of A ?T' T TT] by (by100 blast)
    qed
    thus "closedin_on ?T' ?TT' C \<longleftrightarrow>
       (\<forall>A\<in>\<A> - {A0}. closedin_on A (subspace_topology ?T' ?TT' A) (A \<inter> C))"
      using h\<B>_coh_raw[rule_format, OF hC] by simp
  qed
  \<comment> \<open>Tree = graph + connected + simply\\_connected.\<close>
  have hT'_graph: "top1_is_graph_on ?T' ?TT'"
  proof -
    have hstrict: "is_topology_on_strict T TT"
      using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
    have hhaus: "is_hausdorff_on T TT"
      using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
    have hT'_sub: "?T' \<subseteq> T" using assms(2,3) by (by100 blast)
    have hT'_strict: "is_topology_on_strict ?T' ?TT'"
    proof -
      have "\<forall>U\<in>?TT'. U \<subseteq> ?T'" unfolding subspace_topology_def by (by100 blast)
      moreover have "is_topology_on ?T' ?TT'"
        using subspace_topology_is_topology_on[OF hstrict[unfolded is_topology_on_strict_def, THEN conjunct1] hT'_sub] .
      ultimately show ?thesis unfolding is_topology_on_strict_def by (by100 blast)
    qed
    have hT'_haus: "is_hausdorff_on ?T' ?TT'"
      using hhaus hT'_sub conjunct2[OF conjunct2[OF Theorem_17_11]] by (by100 blast)
    \<comment> \<open>Arc family \\<A>-{A0} covers T' and satisfies all graph properties in subspace.\<close>
    have hgraph: "top1_is_graph_on T TT"
      using assms(1) unfolding top1_is_tree_on_def by (by100 blast)
    \<comment> \<open>Each B in \\<A>-{A0} is an arc in subspace of T', using subspace\\_topology\\_trans.\<close>
    have h\<B>_arcs: "\<forall>B\<in>\<A> - {A0}. B \<subseteq> ?T' \<and> top1_is_arc_on B (subspace_topology ?T' ?TT' B)"
    proof (intro ballI conjI)
      fix B assume hB: "B \<in> \<A> - {A0}"
      show "B \<subseteq> ?T'" using hB by (by100 blast)
      have "B \<subseteq> ?T'" using hB by (by100 blast)
      have "top1_is_arc_on B (subspace_topology T TT B)" using assms(2) hB by (by100 blast)
      moreover have "subspace_topology ?T' ?TT' B = subspace_topology T TT B"
        using subspace_topology_trans[OF \<open>B \<subseteq> ?T'\<close>] by simp
      ultimately show "top1_is_arc_on B (subspace_topology ?T' ?TT' B)" by simp
    qed
    have h\<B>_cover: "\<Union>(\<A> - {A0}) = ?T'" by simp
    \<comment> \<open>Intersection properties transfer via subspace\\_topology\\_trans.\<close>
    have h\<B>_inter: "\<forall>A\<in>\<A> - {A0}. \<forall>B\<in>\<A> - {A0}. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?T' ?TT' A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?T' ?TT' B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
    proof (intro ballI impI)
      fix A B assume hA: "A \<in> \<A> - {A0}" and hB: "B \<in> \<A> - {A0}" and hAB: "A \<noteq> B"
      have hA': "A \<in> \<A>" and hB': "B \<in> \<A>" using hA hB by (by100 blast)+
      from assms(4)[rule_format, OF hA' hB' hAB]
      have hinter: "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" .
      have "subspace_topology ?T' ?TT' A = subspace_topology T TT A"
        using subspace_topology_trans[of A ?T' T TT] hA by (by100 blast)
      moreover have "subspace_topology ?T' ?TT' B = subspace_topology T TT B"
        using subspace_topology_trans[of B ?T' T TT] hB by (by100 blast)
      ultimately show "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?T' ?TT' A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?T' ?TT' B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
        using hinter by simp
    qed
    show ?thesis
      unfolding top1_is_graph_on_def
      apply (intro conjI)
        apply (rule hT'_strict)
       apply (rule hT'_haus)
      apply (rule exI[of _ "\<A> - {A0}"])
      using h\<B>_arcs h\<B>_cover h\<B>_inter h\<B>_coh
      by (by5000 blast)
  qed
  have hT'_conn: "top1_connected_on ?T' ?TT'"
  proof (rule ccontr)
    assume "\<not> top1_connected_on ?T' ?TT'"
    \<comment> \<open>If T' disconnected: T' = U \\<union> V with U,V open, disjoint, nonempty.
       w \\<in> U or V (say U). A0 connected, A0 \\<inter> T' = {w}, so A0 doesn't help V.
       T = A0 \\<union> T'. V is open in T' and also open in T (via subspace).
       T \\ V = A0 \\<union> U: this is closed in T (V open).
       So T \\ V \\<ne> {} and V \\<ne> {} disconnects T. Contradiction with T connected.\<close>
    have hT_conn: "top1_connected_on T TT"
      using assms(1) unfolding top1_is_tree_on_def by (by100 blast)
    have hTT: "is_topology_on T TT"
      using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def
          is_topology_on_strict_def by (by100 blast)
    have hT'_sub: "?T' \<subseteq> T" using assms(2,3) by (by100 blast)
    have hTT': "is_topology_on ?T' ?TT'"
      using subspace_topology_is_topology_on[OF hTT hT'_sub] .
    \<comment> \<open>T' disconnected: \\<exists> separation.\<close>
    from \<open>\<not> top1_connected_on ?T' ?TT'\<close>
    obtain U V where hU: "U \<in> ?TT'" and hV: "V \<in> ?TT'"
        and hne_U: "U \<noteq> {}" and hne_V: "V \<noteq> {}"
        and hdisj: "U \<inter> V = {}" and hcov: "U \<union> V = ?T'"
      unfolding top1_connected_on_def using hTT' by (by5000 blast)
    \<comment> \<open>U and V are open in T' = subspace of T. So U = T'\\<inter>U', V = T'\\<inter>V' for some U',V' open in T.\<close>
    from hU obtain U' where "U' \<in> TT" "U = ?T' \<inter> U'" unfolding subspace_topology_def by (by100 blast)
    from hV obtain V' where "V' \<in> TT" "V = ?T' \<inter> V'" unfolding subspace_topology_def by (by100 blast)
    \<comment> \<open>T = T' \\<union> A0 and A0 \\<inter> T' \\<subseteq> {w} (disjointness from tree\\_leaf\\_other).\<close>
    have hT_eq: "T = ?T' \<union> A0" using assms(3,5) by (by100 blast)
    \<comment> \<open>A0 is connected (arc). w \\<in> U or w \\<in> V. A0 connects to T' only at w.
       So A0 is entirely within the open set containing w (plus its interior).
       The OTHER open set (not containing w) is disjoint from A0.
       Hence that other set is open in T and creates a disconnection of T.\<close>
    \<comment> \<open>V' is open in T. V \\<subseteq> T'. If we can show A0 \\<inter> V' = {} (A0 disjoint from V' in T),
       then V' creates a separation of T: T = (T \\ V') \\<union> (T \\<inter> V') with V' open,
       V' \\<inter> T \\<ne> {} (contains V \\<ne> {}), T \\ V' \\<ne> {} (contains A0 or U).

       A0 \\<inter> V' = ? We need A0 \\<inter> T' \\<subseteq> {w} (proved as disjointness).
       w \\<in> U (or V, WLOG). If w \\<in> U: V \\<inter> A0 \\<subseteq> V \\<inter> (T' \\<inter> A0) \\<subseteq> V \\<inter> {w}.
       Since V open in T' and w \\<in> U, w \\<notin> V (disjoint). So V \\<inter> A0 = {}.
       Then V \\<subseteq> T', V \\<inter> A0 = {}, V \\<noteq> {}.
       V' open in T, V' \\<inter> T \\<supseteq> V \\<noteq> {}, T \\ V' \\<supseteq> A0 \\<noteq> {}.
       But T = (T \\<inter> V') \\<union> (T \\ V'). V' open in T, T \\ V' = complement in T.
       Need T \\ V' also open... that makes V' clopen, contradicting T connected.\<close>
    \<comment> \<open>Need w (other endpoint of A0).\<close>
    have "\<exists>w. w \<in> ?T' \<and> w \<noteq> v \<and> w \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)"
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
      have "v \<in> {h 0, h 1}" using assms(6) hep by simp
      then obtain w where hw_ep: "w \<in> {h 0, h 1}" "w \<noteq> v"
      proof (cases "v = h 0")
        case True
        have "h 1 \<in> {h 0, h 1} \<and> h 1 \<noteq> v" using hne True by (by100 simp)
        thus ?thesis using that by (by100 blast)
      next
        case False
        hence "v = h 1" using \<open>v \<in> {h 0, h 1}\<close> by (by100 blast)
        have "h 0 \<in> {h 0, h 1} \<and> h 0 \<noteq> v" using hne \<open>v = h 1\<close> by (by100 simp)
        thus ?thesis using that by (by100 blast)
      qed
      have hw_ep_A0: "w \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)"
        using hw_ep(1) hep by simp
      from tree_leaf_other_endpoint_shared[OF assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) hw_ep_A0 hw_ep(2)]
      obtain B where "B \<in> \<A> - {A0}" "w \<in> B" by (by100 blast)
      hence "w \<in> ?T'" by (by100 blast)
      thus ?thesis using hw_ep(2) hw_ep_A0 by (by100 blast)
    qed
    then obtain w where "w \<in> ?T'" "w \<noteq> v"
        "w \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)" by (by100 blast)
    have hw_in: "w \<in> U \<or> w \<in> V" using \<open>w \<in> ?T'\<close> hcov by (by100 blast)
    \<comment> \<open>WLOG w \\<in> U. Then V is disjoint from A0. V' open in T, V \\<ne> {}, T\\\\V' nonempty.\<close>
    \<comment> \<open>Similar argument for w \\<in> V (swap U and V).\<close>
    \<comment> \<open>Define f: T \\<to> {0,1} by f|T' = characteristic of U, f|A0 = constant (w\\<in>U?0:1).
       f continuous on T (coherent topology). T connected \\<Rightarrow> f constant.
       But U,V nonempty in T' \\<Rightarrow> f not constant. Contradiction.\<close>
    \<comment> \<open>A0 \\<inter> T' \\<subseteq> {w}: from the disjointness proof.\<close>
    have hA0_T'_disj: "A0 \<inter> ?T' \<subseteq> {w}"
    proof
      fix x assume "x \<in> A0 \<inter> ?T'"
      hence hx_A0: "x \<in> A0" and hx_T': "x \<in> ?T'" by (by100 blast)+
      from \<open>x \<in> ?T'\<close> obtain B where "B \<in> \<A> - {A0}" "x \<in> B" by (by100 blast)
      hence "B \<in> \<A>" "B \<noteq> A0" by (by100 blast)+
      have "x \<in> A0 \<inter> B" using hx_A0 \<open>x \<in> B\<close> by (by100 blast)
      from assms(4)[rule_format, OF assms(5) \<open>B \<in> \<A>\<close>]
      have "A0 \<inter> B \<subseteq> top1_arc_endpoints_on A0 (subspace_topology T TT A0)"
        using \<open>B \<noteq> A0\<close> by (by100 blast)
      hence "x \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)"
        using \<open>x \<in> A0 \<inter> B\<close> by (by100 blast)
      \<comment> \<open>x is an endpoint of A0 = {v, w}. v \\<notin> B (leaf). So x = w.\<close>
      have "x = v \<or> x = w"
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
        have hinj: "inj_on h I_set"
          using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have hne: "h 0 \<noteq> h 1"
        proof
          assume "h 0 = h 1"
          from inj_onD[OF hinj this] show False unfolding top1_unit_interval_def by (by100 auto)
        qed
        have "v \<in> {h 0, h 1}" using assms(6) hep by simp
        have "w \<in> {h 0, h 1}"
          using \<open>w \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)\<close> hep by simp
        have "{v, w} = {h 0, h 1}"
          using \<open>v \<in> {h 0, h 1}\<close> \<open>w \<in> {h 0, h 1}\<close> \<open>w \<noteq> v\<close> hne
          by (by5000 force)
        thus ?thesis
          using \<open>x \<in> top1_arc_endpoints_on A0 _\<close> hep \<open>{v, w} = {h 0, h 1}\<close>
          by (by100 blast)
      qed
      moreover have "x \<noteq> v" using assms(7)[rule_format, OF \<open>B \<in> \<A>\<close> \<open>B \<noteq> A0\<close>] \<open>x \<in> B\<close> by (by100 blast)
      ultimately show "x \<in> {w}" by (by100 blast)
    qed
    \<comment> \<open>If w \\<in> U: any point in A0 \\<inter> V must be in A0 \\<inter> T' \\<inter> V \\<subseteq> {w} \\<inter> V = {} (since w \\<in> U, U \\<inter> V = {}).
       So A0 \\<inter> V = {} (V \\<subseteq> T'). Then V is disjoint from A0.
       V \\<subseteq> T \\ A0 and V is open in T' = T \\<inter> subspace. V' open in T.
       V' \\<inter> T \\<ne> {} (contains V), (T \\ V') \\<ne> {} (contains A0).
       V' and U' \\<union> {preimage of A0-stuff} separate T.\<close>
    \<comment> \<open>In coherent topology: each arc B \\<in> \\<A>-{A0} is connected, so B \\<subseteq> U or B \\<subseteq> V.
       Let C1 = arcs in U, C2 = arcs in V. WLOG w \\<in> U.
       D2 = V (= \\<Union>C2). D2 closed in T: for each B \\<in> \\<A>,
       D2 \\<inter> B closed in B. For B \\<ne> A0: D2\\<inter>B = V\\<inter>B closed in B (V closed in T').
       For B = A0: D2\\<inter>A0 = V\\<inter>A0 \\<subseteq> V\\<inter>{w} = {} (w \\<in> U). {} closed.
       D2 also open in T (complement D1 = U\\<union>A0 is closed similarly).
       D2 clopen in T. T connected \\<Rightarrow> D2 = {} or T. D2 \\<ne> T (A0 \\<notin> D2). Contradiction.\<close>
    \<comment> \<open>w \\<in> U or w \\<in> V. Pick the component not containing w.\<close>
    have hV_no_A0: "\<exists>W. W \<in> {U, V} \<and> W \<noteq> {} \<and> w \<notin> W"
    proof (cases "w \<in> U")
      case True thus ?thesis using hne_V hdisj True by (by100 blast)
    next
      case False hence "w \<in> V" using hw_in by (by100 blast)
      thus ?thesis using hne_U hdisj \<open>w \<in> V\<close> by (by100 blast)
    qed
    then obtain W where "W \<in> {U, V}" "W \<noteq> {}" "w \<notin> W" by (by100 blast)
    \<comment> \<open>W \\<subseteq> T', W \\<inter> A0 = {} (since W \\<inter> A0 \\<subseteq> W \\<inter> T' \\<inter> A0 \\<subseteq> W \\<inter> {w} = {}).\<close>
    have hW_sub_T': "W \<subseteq> ?T'" using \<open>W \<in> {U, V}\<close> hcov by (by100 blast)
    have hW_disj_A0: "W \<inter> A0 = {}"
    proof -
      have "W \<inter> A0 \<subseteq> W \<inter> ?T' \<inter> A0" using hW_sub_T' by (by100 blast)
      also have "... \<subseteq> W \<inter> {w}" using hA0_T'_disj by (by100 blast)
      also have "... = {}" using \<open>w \<notin> W\<close> by (by100 blast)
      finally show ?thesis by (by100 blast)
    qed
    \<comment> \<open>W closed in T via coherent closedness.\<close>
    have "closedin_on T TT W"
    proof -
      \<comment> \<open>W closed in T' (complement of U or V, both open in T').\<close>
      have hW_closed_T': "closedin_on ?T' ?TT' W"
      proof -
        have "?T' - W \<in> ?TT'"
        proof (cases "W = U")
          case True hence "?T' - W = V" using hcov hdisj by (by100 blast)
          thus ?thesis using hV by simp
        next
          case False hence "W = V" using \<open>W \<in> {U, V}\<close> by (by100 blast)
          hence "?T' - W = U" using hcov hdisj by (by100 blast)
          thus ?thesis using hU by simp
        qed
        thus ?thesis unfolding closedin_on_def using hW_sub_T' by (by100 blast)
      qed
      \<comment> \<open>T' closed in T (finite union of compact arcs in Hausdorff).\<close>
      have hT'_closed: "closedin_on T TT ?T'"
      proof -
        have hhaus: "is_hausdorff_on T TT"
          using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
        have hfin': "finite (\<A> - {A0})" using assms(9) by (by100 simp)
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
        from closedin_Union_finite[OF hTT hfin' this]
        show ?thesis .
      qed
      \<comment> \<open>W closed in T: closed in closed \\<Rightarrow> closed in ambient.
         W closed in T' means T'-W open in T' = T'\\<inter>O for O open in T.
         T' closed \\<Rightarrow> T\\\\T' open. W = T'\\<inter>(T\\\\O) = T \\ ((T\\\\T')\\<union>O). Complement of open \\<Rightarrow> closed.\<close>
      \<comment> \<open>Closed in closed = closed in ambient: Theorem 17.3.\<close>
      from Theorem_17_3[OF hTT hT'_closed hW_closed_T']
      show "closedin_on T TT W" .
    qed
    \<comment> \<open>W open in T: show T-W is closed in T.
       T-W = (T'-W) \\<union> A0 since W \\<inter> A0 = {} and T = T' \\<union> A0.
       T'-W closed in T' (it's the other component, complement of W which is open).
       T' closed in T (finite union of compact arcs). By Thm 17.3, T'-W closed in T.
       A0 closed in T (arc \\<Rightarrow> compact \\<Rightarrow> closed in Hausdorff). Union of 2 closed = closed.\<close>
    have "W \<in> TT"
    proof -
      \<comment> \<open>T = T' \\<union> A0.\<close>
      have hT_eq: "T = ?T' \<union> A0" using assms(3,5) by (by100 blast)
      \<comment> \<open>T - W = (T' - W) \\<union> A0.\<close>
      have hTmW: "T - W = (?T' - W) \<union> A0" using hT_eq hW_disj_A0 by (by100 blast)
      \<comment> \<open>T' - W is closed in T' (complement of open set W).\<close>
      have hW_open_T': "W \<in> ?TT'"
        using \<open>W \<in> {U, V}\<close> hU hV by (by100 blast)
      have hTmW_closed_T': "closedin_on ?T' ?TT' (?T' - W)"
      proof -
        have "?T' - W \<subseteq> ?T'" by (by100 blast)
        moreover have "?T' - (?T' - W) = W" using hW_sub_T' by (by100 blast)
        hence "?T' - (?T' - W) \<in> ?TT'" using hW_open_T' by simp
        ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
      qed
      \<comment> \<open>T' closed in T.\<close>
      have hT'_closed: "closedin_on T TT ?T'"
      proof -
        have hhaus: "is_hausdorff_on T TT"
          using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
        have hfin': "finite (\<A> - {A0})" using assms(9) by (by100 simp)
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
        from closedin_Union_finite[OF hTT hfin' this]
        show ?thesis .
      qed
      \<comment> \<open>T'-W closed in T (by Thm 17.3: closed in closed = closed in ambient).\<close>
      have hTmW_closed_T: "closedin_on T TT (?T' - W)"
        using Theorem_17_3[OF hTT hT'_closed hTmW_closed_T'] .
      \<comment> \<open>A0 closed in T.\<close>
      have hA0_closed: "closedin_on T TT A0"
      proof -
        have hhaus: "is_hausdorff_on T TT"
          using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
        have hA0_sub: "A0 \<subseteq> T" using assms(2,5) by (by100 blast)
        have "top1_is_arc_on A0 (subspace_topology T TT A0)" using assms(2,5) by (by100 blast)
        from arc_compact[OF this]
        have "top1_compact_on A0 (subspace_topology T TT A0)" .
        from Theorem_26_3[OF hhaus hA0_sub this]
        show ?thesis .
      qed
      \<comment> \<open>T - W = (T'-W) \\<union> A0 is closed in T (union of 2 closed sets).\<close>
      have "closedin_on T TT ((?T' - W) \<union> A0)"
        using closedin_Union_finite[OF hTT, of "{?T' - W, A0}"] hTmW_closed_T hA0_closed by (by100 simp)
      hence "closedin_on T TT (T - W)" using hTmW by simp
      \<comment> \<open>T - W closed \\<Rightarrow> W open.\<close>
      hence "T - (T - W) \<in> TT" unfolding closedin_on_def by (by100 blast)
      moreover have "T - (T - W) = W"
        using hW_sub_T' hT'_sub by (by100 blast)
      ultimately show "W \<in> TT" by simp
    qed
    \<comment> \<open>W clopen in T. T connected \\<Rightarrow> W = {} or W = T.\<close>
    from connected_iff_clopen[OF hTT]
    have "\<forall>S. S \<in> TT \<and> closedin_on T TT S \<longrightarrow> S = {} \<or> S = T"
      using hT_conn by (by100 blast)
    hence "W = {} \<or> W = T" using \<open>W \<in> TT\<close> \<open>closedin_on T TT W\<close> by (by100 blast)
    moreover have "W \<noteq> {}" using \<open>W \<noteq> {}\<close> .
    moreover have "W \<noteq> T" using hW_disj_A0
    proof -
      have "v \<in> A0" using assms(6) unfolding top1_arc_endpoints_on_def by (by100 blast)
      hence "v \<notin> W" using hW_disj_A0 by (by100 blast)
      moreover have "v \<in> T" using \<open>v \<in> A0\<close> assms(2,3,5) by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    ultimately show False by (by100 blast)
  qed
  have hT'_sc: "top1_simply_connected_on ?T' ?TT'"
  proof -
    \<comment> \<open>T' is a retract of T: the map r(x) = x for x \\<in> T', r(x) = w for x \\<in> A0\\\\T'
       is a continuous retraction. By Lemma 55.1, loops in T' that are contractible
       in T are contractible in T'. Since T is simply connected, all loops in T' are
       contractible in T, hence in T'.\<close>
    \<comment> \<open>The other endpoint w of A0 is in T' (from tree\\_leaf\\_other\\_endpoint\\_shared).\<close>
    have hw_exists: "\<exists>w. w \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0) \<and> w \<noteq> v \<and> w \<in> ?T'"
    proof -
      \<comment> \<open>A0 has 2 endpoints. One is v. The other w \\<ne> v.\<close>
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
      \<comment> \<open>v is one of {h 0, h 1}. The other is w.\<close>
      have "v \<in> {h 0, h 1}" using assms(6) hep by simp
      have "\<exists>w. w \<in> {h 0, h 1} \<and> w \<noteq> v"
      proof (cases "v = h 0")
        case True
        have "h 1 \<in> {h 0, h 1} \<and> h 1 \<noteq> v" using hne True by (by100 simp)
        thus ?thesis by (by100 blast)
      next
        case False
        hence "v = h 1" using \<open>v \<in> {h 0, h 1}\<close> by (by100 blast)
        thus ?thesis using hne by (by100 blast)
      qed
      then obtain w where hw_ep: "w \<in> {h 0, h 1}" "w \<noteq> v" by (by100 blast)
      have "w \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)" using hw_ep(1) hep by simp
      \<comment> \<open>w is shared with another arc (from tree\\_leaf\\_other\\_endpoint\\_shared).\<close>
      have hw_ep_A0: "w \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)"
        using hw_ep(1) hep by simp
      from tree_leaf_other_endpoint_shared[OF assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) hw_ep_A0 hw_ep(2)]
      have "\<exists>B\<in>\<A> - {A0}. w \<in> B" .
      then obtain B where "B \<in> \<A> - {A0}" "w \<in> B" by (by100 blast)
      hence "w \<in> ?T'" by (by100 blast)
      thus ?thesis using \<open>w \<in> top1_arc_endpoints_on A0 _\<close> hw_ep(2) by (by100 blast)
    qed
    then obtain w where hw: "w \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)" "w \<noteq> v" "w \<in> ?T'"
      by (by100 blast)
    \<comment> \<open>T' is a retract of T.\<close>
    have "top1_retract_of_on T TT ?T'"
    proof -
      \<comment> \<open>Retraction r(x) = x for x \\<in> T', r(x) = w for x \\<in> A0\\\\T'.
         Continuity via Theorem 18.3 (pasting lemma): T = T' \\<union> A0, both closed.
         f = id on T', g = const w on A0. Both continuous. Agree on T'\\<inter>A0 = {w}.\<close>
      let ?r = "\<lambda>x. if x \<in> ?T' then x else w"
      have hT'_sub: "?T' \<subseteq> T" using assms(2,3) by (by100 blast)
      have hT_eq: "T = ?T' \<union> A0" using assms(3,5) by (by100 blast)
      have hA0_T'_w: "A0 \<inter> ?T' \<subseteq> {w}"
      proof (intro subsetI)
        fix x assume "x \<in> A0 \<inter> ?T'"
        hence "x \<in> A0" "x \<in> ?T'" by (by100 blast)+
        then obtain B where "B \<in> \<A> - {A0}" "x \<in> B" by (by100 blast)
        have "B \<in> \<A>" "B \<noteq> A0" using \<open>B \<in> \<A> - {A0}\<close> by (by100 blast)+
        have "x \<in> A0 \<inter> B" using \<open>x \<in> A0\<close> \<open>x \<in> B\<close> by (by100 blast)
        have "A0 \<noteq> B" using \<open>B \<noteq> A0\<close> by simp
        from assms(4)[rule_format, OF assms(5) \<open>B \<in> \<A>\<close> \<open>A0 \<noteq> B\<close>]
        have "A0 \<inter> B \<subseteq> top1_arc_endpoints_on A0 (subspace_topology T TT A0)"
          by (by100 blast)
        hence "x \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)"
          using \<open>x \<in> A0 \<inter> B\<close> by (by100 blast)
        \<comment> \<open>x is endpoint of A0 and x \\<in> B with B \\<ne> A0. By assms(7), v \\<notin> B, so x \\<ne> v.
           endpoints(A0) = {v, w}, so x = w.\<close>
        have "x \<noteq> v"
        proof
          assume "x = v"
          from assms(7)[rule_format, OF \<open>B \<in> \<A>\<close> \<open>B \<noteq> A0\<close>]
          show False using \<open>x \<in> B\<close> \<open>x = v\<close> by (by100 blast)
        qed
        moreover have "x \<in> {v, w}"
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
          have "v \<in> {h 0, h 1}" using assms(6) hep by simp
          have "w \<in> {h 0, h 1}" using hw(1) hep by simp
          have "h 0 \<noteq> h 1"
          proof
            assume "h 0 = h 1"
            have "inj_on h I_set" using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
            from inj_onD[OF this \<open>h 0 = h 1\<close>] show False unfolding top1_unit_interval_def by (by100 auto)
          qed
          have "{h 0, h 1} \<subseteq> {v, w}"
            using \<open>v \<in> {h 0, h 1}\<close> \<open>w \<in> {h 0, h 1}\<close> \<open>h 0 \<noteq> h 1\<close> hw(2) by (by100 blast)
          thus ?thesis using \<open>x \<in> top1_arc_endpoints_on A0 _\<close> hep by (by100 blast)
        qed
        ultimately show "x \<in> {w}" by (by100 blast)
      qed
      have hw_A0: "w \<in> A0" using hw(1) unfolding top1_arc_endpoints_on_def by (by100 blast)
      have hr_maps: "\<forall>x\<in>T. ?r x \<in> ?T'"
      proof (intro ballI)
        fix x assume "x \<in> T"
        show "?r x \<in> ?T'"
        proof (cases "x \<in> ?T'")
          case True thus ?thesis by simp
        next
          case False thus ?thesis using hw(3) by simp
        qed
      qed
      have hr_fixes: "\<forall>x\<in>?T'. ?r x = x" by simp
      \<comment> \<open>Continuity via pasting lemma.\<close>
      have hr_cont: "top1_continuous_map_on T TT ?T' ?TT' ?r"
      proof -
        have hTT_local: "is_topology_on T TT"
          using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def
              is_topology_on_strict_def by (by100 blast)
        have hT'_closed: "closedin_on T TT ?T'"
        proof -
          have hhaus2: "is_hausdorff_on T TT"
            using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
          have "\<forall>B\<in>\<A> - {A0}. closedin_on T TT B"
          proof (intro ballI)
            fix B assume "B \<in> \<A> - {A0}"
            have "B \<subseteq> T" using assms(2) \<open>B \<in> \<A> - {A0}\<close> by (by100 blast)
            have "top1_is_arc_on B (subspace_topology T TT B)" using assms(2) \<open>B \<in> \<A> - {A0}\<close> by (by100 blast)
            from Theorem_26_3[OF hhaus2 \<open>B \<subseteq> T\<close> arc_compact[OF this]] show "closedin_on T TT B" .
          qed
          from closedin_Union_finite[OF hTT_local, of "\<A> - {A0}"] this assms(9) show ?thesis by (by100 simp)
        qed
        have hA0_closed: "closedin_on T TT A0"
        proof -
          have hhaus2: "is_hausdorff_on T TT"
            using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
          have "A0 \<subseteq> T" using assms(2,5) by (by100 blast)
          from Theorem_26_3[OF hhaus2 this arc_compact[OF assms(2)[rule_format, OF assms(5), THEN conjunct2]]]
          show ?thesis .
        qed
        have hTT': "is_topology_on ?T' ?TT'"
          using subspace_topology_is_topology_on[OF hTT_local hT'_sub] .
        \<comment> \<open>f = id: T' \\<rightarrow> T' continuous.\<close>
        have hf: "top1_continuous_map_on ?T' (subspace_topology T TT ?T') ?T' ?TT' id"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix x assume "x \<in> ?T'" thus "id x \<in> ?T'" by simp
        next
          fix V assume "V \<in> ?TT'"
          have "V \<subseteq> ?T'"
          proof -
            from \<open>V \<in> ?TT'\<close> obtain U where "U \<in> TT" "V = ?T' \<inter> U"
              unfolding subspace_topology_def by (by100 blast)
            thus ?thesis by (by100 blast)
          qed
          hence "{x \<in> ?T'. id x \<in> V} = V" by (by100 auto)
          thus "{x \<in> ?T'. id x \<in> V} \<in> subspace_topology T TT ?T'"
            using \<open>V \<in> ?TT'\<close> by simp
        qed
        \<comment> \<open>g = const w: A0 \\<rightarrow> T' continuous.\<close>
        have hg: "top1_continuous_map_on A0 (subspace_topology T TT A0) ?T' ?TT' (\<lambda>x. w)"
        proof -
          have "A0 \<subseteq> T" using assms(2,5) by (by100 blast)
          have "is_topology_on A0 (subspace_topology T TT A0)"
            by (rule subspace_topology_is_topology_on[OF hTT_local \<open>A0 \<subseteq> T\<close>])
          from top1_continuous_map_on_const[OF this hTT' hw(3)]
          show ?thesis .
        qed
        have hagree: "\<forall>x\<in>?T' \<inter> A0. id x = w"
        proof (intro ballI)
          fix x assume "x \<in> ?T' \<inter> A0"
          hence "x \<in> A0 \<inter> ?T'" by (by100 blast)
          hence "x \<in> {w}" using hA0_T'_w by (by100 blast)
          thus "id x = w" by (by100 simp)
        qed
        \<comment> \<open>?r = (\\<lambda>x. if x \\<in> T' then id x else w).\<close>
        from Theorem_18_3[OF hTT_local hTT' hT'_closed hA0_closed hT_eq hf hg hagree]
        have "top1_continuous_map_on T TT ?T' ?TT' (\<lambda>x. if x \<in> ?T' then id x else w)" .
        moreover have "(\<lambda>x. if x \<in> ?T' then id x else w) = ?r" by (by100 auto)
        ultimately show ?thesis by simp
      qed
      show ?thesis unfolding top1_retract_of_on_def top1_is_retraction_on_def
        using hT'_sub hr_cont hr_fixes by (by100 blast)
    qed
    \<comment> \<open>By Lemma 55.1: loops in T' contractible in T \\<Rightarrow> contractible in T'.\<close>
    \<comment> \<open>T simply connected + retract \\<Rightarrow> T' simply connected.\<close>
    have hT_sc: "top1_simply_connected_on T TT"
      using assms(1) unfolding top1_is_tree_on_def by (by100 blast)
    show ?thesis
    proof -
      \<comment> \<open>Simply connected = path-connected + all loops contractible.\<close>
      have hT_pc: "top1_path_connected_on T TT"
        using hT_sc unfolding top1_simply_connected_on_def by (by100 blast)
      have hT'_sub: "?T' \<subseteq> T" using assms(2,3) by (by100 blast)
      have hTT: "is_topology_on T TT"
        using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def
            is_topology_on_strict_def by (by100 blast)
      have hTT': "is_topology_on ?T' ?TT'"
        using subspace_topology_is_topology_on[OF hTT hT'_sub] .
      \<comment> \<open>Step 1: T' is path-connected (retraction image of path-connected).\<close>
      have hT'_pc: "top1_path_connected_on ?T' ?TT'"
      proof -
        from \<open>top1_retract_of_on T TT ?T'\<close>
        obtain r where hr: "top1_is_retraction_on T TT ?T' r"
          unfolding top1_retract_of_on_def by (by100 blast)
        have hr_cont: "top1_continuous_map_on T TT ?T' ?TT' r"
          using hr unfolding top1_is_retraction_on_def by (by100 blast)
        have hr_maps: "\<forall>x\<in>T. r x \<in> ?T'"
          using hr_cont unfolding top1_continuous_map_on_def by (by100 blast)
        have hr_fixes: "\<forall>x\<in>?T'. r x = x"
          using hr unfolding top1_is_retraction_on_def by (by100 blast)
        have hr_surj: "r ` T = ?T'"
        proof (rule set_eqI, rule iffI)
          fix y assume "y \<in> r ` T"
          then obtain x where "x \<in> T" "y = r x" by (by100 blast)
          thus "y \<in> ?T'" using hr_maps by (by100 blast)
        next
          fix y assume "y \<in> ?T'"
          hence "y \<in> T" using hT'_sub by (by100 blast)
          have "r y = y" using hr_fixes \<open>y \<in> ?T'\<close> by (by100 blast)
          thus "y \<in> r ` T" using \<open>y \<in> T\<close> by (by100 force)
        qed
        have hTT'_sub: "subspace_topology ?T' ?TT' ?T' = ?TT'"
          using subspace_topology_trans[of ?T' ?T' T TT] by simp
        have hT'_self: "?T' \<subseteq> ?T'" by (by100 blast)
        from top1_path_connected_continuous_image[OF hT_pc hr_cont hr_maps hr_surj hT'_self _ hTT']
        have "top1_path_connected_on ?T' (subspace_topology ?T' ?TT' ?T')" by simp
        thus ?thesis using hTT'_sub by simp
      qed
      \<comment> \<open>Step 2: All loops in T' are contractible (Lemma 55.1 + T simply connected).\<close>
      have hT'_loops: "\<forall>x\<in>?T'. \<forall>f. top1_is_loop_on ?T' ?TT' x f \<longrightarrow>
          top1_path_homotopic_on ?T' ?TT' x x f (top1_constant_path x)"
      proof (intro ballI allI impI)
        fix x f assume hx: "x \<in> ?T'" and hf: "top1_is_loop_on ?T' ?TT' x f"
        \<comment> \<open>f is a loop in T' \\<subseteq> T. Hence a loop in T.\<close>
        have hf_T: "top1_is_loop_on T TT x f"
        proof -
          have hf_path: "top1_is_path_on ?T' ?TT' x x f"
            using hf unfolding top1_is_loop_on_def .
          have hf_cont: "top1_continuous_map_on I_set I_top ?T' ?TT' f"
            using hf_path unfolding top1_is_path_on_def by (by100 blast)
          \<comment> \<open>Inclusion T' \\<hookrightarrow> T is continuous (Theorem 18.2).\<close>
          have hT'_sub: "?T' \<subseteq> T" using assms(2,3) by (by100 blast)
          have hincl: "top1_continuous_map_on ?T' ?TT' T TT id"
          proof -
            \<comment> \<open>Direct: preimage of open in T under id restricted to T' is open in T'.\<close>
            show ?thesis unfolding top1_continuous_map_on_def
            proof (intro conjI ballI)
              fix x assume "x \<in> ?T'"
              have "x \<in> T" using \<open>x \<in> ?T'\<close> hT'_sub by (by100 blast)
              thus "id x \<in> T" by simp
            next
              fix U assume "U \<in> TT"
              have "{x \<in> ?T'. id x \<in> U} = ?T' \<inter> U" by (by100 auto)
              also have "?T' \<inter> U \<in> ?TT'" unfolding subspace_topology_def using \<open>U \<in> TT\<close> by (by100 blast)
              finally show "{x \<in> ?T'. id x \<in> U} \<in> ?TT'" .
            qed
          qed
          from top1_continuous_map_on_comp[OF hf_cont hincl]
          have "top1_continuous_map_on I_set I_top T TT (id \<circ> f)" .
          hence "top1_continuous_map_on I_set I_top T TT f" by simp
          moreover have "f 0 = x" using hf_path unfolding top1_is_path_on_def by (by100 blast)
          moreover have "f 1 = x" using hf_path unfolding top1_is_path_on_def by (by100 blast)
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        \<comment> \<open>T simply connected \\<Rightarrow> f contractible in T.\<close>
        have "top1_path_homotopic_on T TT x x f (top1_constant_path x)"
          using hT_sc hf_T hx hT'_sub
          unfolding top1_simply_connected_on_def by (by100 blast)
        \<comment> \<open>By Lemma 55.1: contractible in T \\<Rightarrow> contractible in T'.\<close>
        have hconst_loop: "top1_is_loop_on ?T' ?TT' x (top1_constant_path x)"
          by (rule top1_constant_path_is_loop[OF hTT' hx])
        from Lemma_55_1_retract_injective[OF \<open>top1_retract_of_on T TT ?T'\<close>
            hx hf hconst_loop \<open>top1_path_homotopic_on T TT x x f (top1_constant_path x)\<close>]
        show "top1_path_homotopic_on ?T' ?TT' x x f (top1_constant_path x)" .
      qed
      show ?thesis unfolding top1_simply_connected_on_def using hT'_pc hT'_loops by (by100 blast)
    qed
  qed
  show ?thesis
  proof (intro conjI)
    show "top1_is_tree_on ?T' ?TT'"
      unfolding top1_is_tree_on_def using hT'_graph hT'_conn hT'_sc by (by100 blast)
    show "\<forall>C. C \<subseteq> ?T' \<longrightarrow>
        (closedin_on ?T' ?TT' C \<longleftrightarrow>
         (\<forall>A\<in>\<A> - {A0}. closedin_on A (subspace_topology ?T' ?TT' A) (A \<inter> C)))"
      using h\<B>_coh .
  qed
qed
\<comment> \<open>Euler formula for trees, assuming leaf existence as a parameter.
   This breaks the circular dependency: leaf existence is proved separately
   (walk+pigeonhole), and the Euler formula uses it.\<close>
\<comment> \<open>Assumption: leaf existence for ALL trees (the topological bridge).\<close>
lemma tree_euler_from_leaf:
  fixes n :: nat
  assumes hleaf_all: "\<And>(T :: 'a set) TT \<A>.
    \<lbrakk>top1_is_tree_on T TT;
     \<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A);
     \<Union>\<A> = T;
     \<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
         A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
       \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
       \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2;
     finite \<A>; card \<A> \<ge> 2;
     \<forall>C. C \<subseteq> T \<longrightarrow> (closedin_on T TT C \<longleftrightarrow> (\<forall>A\<in>\<A>. closedin_on A (subspace_topology T TT A) (A \<inter> C)))\<rbrakk>
    \<Longrightarrow> \<exists>A0 v. A0 \<in> \<A> \<and> v \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)
        \<and> (\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> v \<notin> B)"
  shows "\<forall>(T :: 'a set) TT \<A>. card \<A> = n \<longrightarrow>
    top1_is_tree_on T TT \<longrightarrow>
    (\<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)) \<longrightarrow>
    \<Union>\<A> = T \<longrightarrow>
    (\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
         A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
       \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
       \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2) \<longrightarrow>
    finite \<A> \<longrightarrow> \<A> \<noteq> {} \<longrightarrow>
    (\<forall>C. C \<subseteq> T \<longrightarrow> (closedin_on T TT C \<longleftrightarrow> (\<forall>A\<in>\<A>. closedin_on A (subspace_topology T TT A) (A \<inter> C)))) \<longrightarrow>
    card (top1_graph_vertex_set T TT \<A>) = n + 1"
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
      and hcoh: "\<forall>C. C \<subseteq> T \<longrightarrow> (closedin_on T TT C \<longleftrightarrow> (\<forall>A\<in>\<A>. closedin_on A (subspace_topology T TT A) (A \<inter> C)))"
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
      from hleaf_all[OF htree harcs hcover hinter hfin hcard_ge2 hcoh]
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
      have hremove_result: "top1_is_tree_on ?T' (subspace_topology T TT ?T')
           \<and> (\<forall>C. C \<subseteq> ?T' \<longrightarrow>
               (closedin_on ?T' (subspace_topology T TT ?T') C \<longleftrightarrow>
                (\<forall>A\<in>?\<A>'. closedin_on A (subspace_topology ?T' (subspace_topology T TT ?T') A) (A \<inter> C))))"
        by (rule finite_tree_remove_leaf_is_tree[OF htree harcs hcover hinter hA0 hv_ep hv_uniq hcard_ge2 hfin hcoh])
      have hT'_tree: "top1_is_tree_on ?T' (subspace_topology T TT ?T')"
        using hremove_result by (by100 blast)
      have h\<A>'_coh: "\<forall>C. C \<subseteq> ?T' \<longrightarrow>
          (closedin_on ?T' (subspace_topology T TT ?T') C \<longleftrightarrow>
           (\<forall>A\<in>?\<A>'. closedin_on A (subspace_topology ?T' (subspace_topology T TT ?T') A) (A \<inter> C)))"
        using hremove_result by (by100 blast)
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
        using h\<A>'_card hT'_tree h\<A>'_arcs h\<A>'_cover h\<A>'_inter h\<A>'_fin h\<A>'_ne h\<A>'_coh by (by5000 simp)
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

\<comment> \<open>Key topological bridge: a simply connected space cannot contain a simple closed curve
   as a retract. Used to derive contradiction from SCC in tree.\<close>
lemma scc_in_sc_false:
  assumes hsc: "top1_simply_connected_on T TT"
      and hTT: "is_topology_on T TT"
      and hhaus_T: "is_hausdorff_on T TT"
      and hSCC: "top1_simple_closed_curve_on T TT C"
      and hretract: "top1_retract_of_on T TT C"
      and hC_sub: "C \<subseteq> T"
  shows False
proof -
  have hC_top: "is_topology_on C (subspace_topology T TT C)"
    using subspace_topology_is_topology_on[OF hTT hC_sub] .
  \<comment> \<open>C path-connected (SCC \\<cong> S1 which is path-connected).\<close>
  from hSCC[unfolded top1_simple_closed_curve_on_def]
  obtain h_s where hhs_cont: "top1_continuous_map_on top1_S1 top1_S1_topology T TT h_s"
      and hhs_inj: "inj_on h_s top1_S1" and hhs_img: "h_s ` top1_S1 = C"
    by (by100 blast)
  have hhs_range: "\<forall>s\<in>top1_S1. h_s s \<in> C"
  proof (intro ballI)
    fix s assume "s \<in> top1_S1"
    hence "h_s s \<in> h_s ` top1_S1" by (by100 blast)
    thus "h_s s \<in> C" using hhs_img by (by100 blast)
  qed
  have hhs_T_range: "\<forall>s\<in>top1_S1. h_s s \<in> T"
    using hhs_range hC_sub by (by100 blast)
  have hC_pc: "top1_path_connected_on C (subspace_topology T TT C)"
  proof -
    have "\<forall>s\<in>top1_S1. h_s s \<in> T" using hhs_range hC_sub by (by100 blast)
    from top1_path_connected_continuous_image[OF S1_path_connected hhs_cont
        this hhs_img hC_sub _ hTT]
    show ?thesis by simp
  qed
  \<comment> \<open>C is simply connected (from retract + T SC).\<close>
  have hC_sc: "top1_simply_connected_on C (subspace_topology T TT C)"
  proof -
    have hC_loops: "\<forall>x\<in>C. \<forall>f. top1_is_loop_on C (subspace_topology T TT C) x f \<longrightarrow>
        top1_path_homotopic_on C (subspace_topology T TT C) x x f (top1_constant_path x)"
    proof (intro ballI allI impI)
      fix x f assume hx: "x \<in> C"
          and hf: "top1_is_loop_on C (subspace_topology T TT C) x f"
      have hf_T: "top1_is_loop_on T TT x f"
      proof -
        from hf have "top1_is_path_on C (subspace_topology T TT C) x x f"
          unfolding top1_is_loop_on_def by (by100 blast)
        from path_in_subspace_is_path_in_ambient'[OF hTT hC_sub this]
        show ?thesis unfolding top1_is_loop_on_def by (by100 blast)
      qed
      have "x \<in> T" using hx hC_sub by (by100 blast)
      have hf_null_T: "top1_path_homotopic_on T TT x x f (top1_constant_path x)"
        using hsc[unfolded top1_simply_connected_on_def] hf_T \<open>x \<in> T\<close> by (by100 blast)
      have hconst: "top1_is_loop_on C (subspace_topology T TT C) x (top1_constant_path x)"
        by (rule top1_constant_path_is_loop[OF hC_top hx])
      from Lemma_55_1_retract_injective[OF hretract hx hf hconst hf_null_T]
      show "top1_path_homotopic_on C (subspace_topology T TT C) x x f (top1_constant_path x)" .
    qed
    show ?thesis unfolding top1_simply_connected_on_def using hC_pc hC_loops by (by100 blast)
  qed
  \<comment> \<open>Transfer SC to S1 via homeomorphism. But S1 is NOT SC.\<close>
  have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
    using S1_compact unfolding top1_compact_on_def by (by100 blast)
  have hhaus: "is_hausdorff_on C (subspace_topology T TT C)"
    using hhaus_T hC_sub conjunct2[OF conjunct2[OF Theorem_17_11]] by (by100 blast)
  have "top1_continuous_map_on top1_S1 top1_S1_topology C (subspace_topology T TT C) h_s"
    by (rule continuous_map_restrict_codomain[OF hhs_cont hhs_range hC_sub])
  have "bij_betw h_s top1_S1 C"
    unfolding bij_betw_def using hhs_inj hhs_img by (by100 blast)
  from Theorem_26_6[OF hS1_top hC_top S1_compact hhaus
      \<open>top1_continuous_map_on top1_S1 top1_S1_topology C _ h_s\<close> this]
  have hhomeo: "top1_homeomorphism_on top1_S1 top1_S1_topology C (subspace_topology T TT C) h_s" .
  have hhomeo_inv: "top1_homeomorphism_on C (subspace_topology T TT C)
      top1_S1 top1_S1_topology (inv_into top1_S1 h_s)"
    by (rule homeomorphism_inverse[OF hhomeo])
  have "top1_simply_connected_on top1_S1 top1_S1_topology"
    by (rule homeomorphism_preserves_simply_connected[OF hhomeo_inv hC_sc])
  \<comment> \<open>But S1 NOT simply connected.\<close>
  from top1_S1_fundamental_group_nontrivial
  obtain f0 g0 where "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f0"
      "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) g0"
      "\<not> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) f0 g0"
    by (by100 blast)
  have h10: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 auto)
  from \<open>top1_simply_connected_on top1_S1 top1_S1_topology\<close>[unfolded top1_simply_connected_on_def]
  have "\<forall>x\<in>top1_S1. \<forall>f. top1_is_loop_on top1_S1 top1_S1_topology x f \<longrightarrow>
      top1_path_homotopic_on top1_S1 top1_S1_topology x x f (top1_constant_path x)"
    using h10 by (by100 blast)
  hence "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0) f0 (top1_constant_path (1,0))"
    using \<open>top1_is_loop_on top1_S1 _ _ f0\<close> h10 by (by100 blast)
  hence "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0) g0 (top1_constant_path (1,0))"
    using \<open>\<forall>x\<in>top1_S1. \<forall>f. _\<close> \<open>top1_is_loop_on top1_S1 _ _ g0\<close> h10 by (by100 blast)
  from Lemma_51_1_path_homotopic_sym[OF this]
  have "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0) (top1_constant_path (1,0)) g0" .
  from Lemma_51_1_path_homotopic_trans[OF hS1_top
      \<open>top1_path_homotopic_on _ _ _ _ f0 (top1_constant_path _)\<close> this]
  have hfg_htpy: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0) f0 g0" .
  show False using hfg_htpy \<open>\<not> top1_path_homotopic_on _ _ _ _ f0 g0\<close> by (by100 blast)
qed

\<comment> \<open>Helper: extract free group from graph\\_pi1\\_free\\_weak (large existential).\<close>
lemma graph_is_free:
  fixes Y :: "'a set" and TY :: "'a set set"
  assumes "top1_is_graph_on Y TY" "top1_connected_on Y TY" "y0 \<in> Y"
  shows "\<exists>(\<iota> :: 'a set \<Rightarrow> _) (S :: 'a set set). top1_is_free_group_full_on
      (top1_fundamental_group_carrier Y TY y0)
      (top1_fundamental_group_mul Y TY y0)
      (top1_fundamental_group_id Y TY y0)
      (top1_fundamental_group_invg Y TY y0) \<iota> S"
proof -
  note h = graph_pi1_free_weak[OF assms]
  \<comment> \<open>h has type \\<exists>\\<iota> S \\<A> T. (big conjunction). Extract first existential.\<close>
  \<comment> \<open>h gives \\<exists>\\<iota> S \\<A> T. big\\_conj. Extract \\<exists>\\<iota> S. free using exE + conjunct1.\<close>
  from h show ?thesis
  proof (elim exE)
    fix \<iota>0 S0 \<A>0 T0
    assume hconj: "top1_is_free_group_full_on
        (top1_fundamental_group_carrier Y TY y0)
        (top1_fundamental_group_mul Y TY y0)
        (top1_fundamental_group_id Y TY y0)
        (top1_fundamental_group_invg Y TY y0) \<iota>0 S0
      \<and> (\<forall>A\<in>\<A>0. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A))
      \<and> \<Union>\<A>0 = Y
      \<and> (\<forall>A\<in>\<A>0. \<forall>B\<in>\<A>0. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2)
      \<and> (\<forall>C. C \<subseteq> Y \<longrightarrow>
           (closedin_on Y TY C \<longleftrightarrow>
            (\<forall>A\<in>\<A>0. closedin_on A (subspace_topology Y TY A) (A \<inter> C))))
      \<and> top1_is_tree_on T0 (subspace_topology Y TY T0) \<and> T0 \<subseteq> Y \<and> y0 \<in> T0
      \<and> (\<forall>A\<in>\<A>0. A \<subseteq> T0 \<or>
           A \<inter> T0 \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A))
      \<and> T0 = \<Union>{A \<in> \<A>0. A \<subseteq> T0}
      \<and> (\<forall>A\<in>{A \<in> \<A>0. \<not> A \<subseteq> T0}.
           \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology Y TY A). e \<in> T0)
      \<and> S0 = {A \<in> \<A>0. \<not> A \<subseteq> T0}"
    have hfree: "top1_is_free_group_full_on
        (top1_fundamental_group_carrier Y TY y0)
        (top1_fundamental_group_mul Y TY y0)
        (top1_fundamental_group_id Y TY y0)
        (top1_fundamental_group_invg Y TY y0) \<iota>0 S0"
      using conjunct1[OF hconj] .
    show ?thesis by (rule exI[of _ \<iota>0], rule exI[of _ S0], rule hfree)
  qed
qed

\<comment> \<open>Arc subdivision preserves V - E.
   Subdividing arc A0 at interior point p: replaces A0 with D1, D2 (sub-arcs).
   V increases by 1 (p becomes a vertex), E increases by 1 (one arc becomes two).
   So V - E is preserved.\<close>
lemma graph_subdivision_preserves_euler:
  fixes Y :: "'a set" and TY :: "'a set set"
  assumes hstrict: "is_topology_on_strict Y TY"
      and hhaus: "is_hausdorff_on Y TY"
      and h\<A>: "\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
      and h\<A>_inter: "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and hfin: "finite \<A>"
      and hA0: "A0 \<in> \<A>"
      and hp: "p \<in> A0" "p \<notin> top1_arc_endpoints_on A0 (subspace_topology Y TY A0)"
      and hep: "top1_arc_endpoints_on A0 (subspace_topology Y TY A0) = {a0, b0}" "a0 \<noteq> b0"
      and hsplit: "A0 = D1 \<union> D2" "D1 \<inter> D2 = {p}"
          "top1_is_arc_on D1 (subspace_topology Y TY D1)"
          "top1_is_arc_on D2 (subspace_topology Y TY D2)"
          "top1_arc_endpoints_on D1 (subspace_topology Y TY D1) = {a0, p}"
          "top1_arc_endpoints_on D2 (subspace_topology Y TY D2) = {p, b0}"
      and hD1_sub: "D1 \<subseteq> Y" and hD2_sub: "D2 \<subseteq> Y"
  defines "\<A>' \<equiv> (\<A> - {A0}) \<union> {D1, D2}"
  shows "int (card (top1_graph_vertex_set Y TY \<A>')) - int (card \<A>')
       = int (card (top1_graph_vertex_set Y TY \<A>)) - int (card \<A>)"
proof -
  let ?V = "top1_graph_vertex_set Y TY \<A>"
  let ?V' = "top1_graph_vertex_set Y TY \<A>'"
  let ?ep = "\<lambda>A. top1_arc_endpoints_on A (subspace_topology Y TY A)"
  \<comment> \<open>Step 1: p is not a vertex of \\<A> (interior to A0, not endpoint of any other arc).\<close>
  have hp_not_V: "p \<notin> ?V"
  proof -
    have "\<forall>B\<in>\<A>. p \<notin> ?ep B"
    proof (intro ballI)
      fix B assume "B \<in> \<A>"
      show "p \<notin> ?ep B"
      proof (cases "B = A0")
        case True thus ?thesis using hp(2) by simp
      next
        case False
        have hAB: "A0 \<inter> B \<subseteq> ?ep A0 \<and> A0 \<inter> B \<subseteq> ?ep B \<and> finite (A0 \<inter> B) \<and> card (A0 \<inter> B) \<le> 2"
          using h\<A>_inter[rule_format, OF hA0 \<open>B \<in> \<A>\<close>] False by (by100 blast)
        have "p \<in> A0" using hp(1) .
        show "p \<notin> ?ep B"
        proof
          assume "p \<in> ?ep B"
          hence "p \<in> B" unfolding top1_arc_endpoints_on_def by (by100 blast)
          hence "p \<in> A0 \<inter> B" using \<open>p \<in> A0\<close> by (by100 blast)
          hence "p \<in> ?ep A0" using hAB by (by100 blast)
          thus False using hp(2) by (by100 blast)
        qed
      qed
    qed
    thus ?thesis unfolding top1_graph_vertex_set_def by (by100 blast)
  qed
  \<comment> \<open>Step 2: V' = V \\<union> {p}.\<close>
  have hV'_eq: "?V' = ?V \<union> {p}"
  proof -
    have "?V' = (\<Union>A\<in>\<A>'. ?ep A)" unfolding top1_graph_vertex_set_def by (by100 blast)
    also have "\<dots> = (\<Union>A\<in>(\<A> - {A0}). ?ep A) \<union> ?ep D1 \<union> ?ep D2"
      unfolding \<A>'_def by (by100 blast)
    also have "\<dots> = (\<Union>A\<in>(\<A> - {A0}). ?ep A) \<union> {a0, p} \<union> {p, b0}"
      using hsplit(5) hsplit(6) by simp
    also have "\<dots> = (\<Union>A\<in>(\<A> - {A0}). ?ep A) \<union> {a0, b0, p}"
      by (by100 blast)
    also have "\<dots> = (\<Union>A\<in>(\<A> - {A0}). ?ep A) \<union> ?ep A0 \<union> {p}"
      using hep by (by100 blast)
    also have "\<dots> = ?V \<union> {p}"
      unfolding top1_graph_vertex_set_def using hA0 by (by100 blast)
    finally show ?thesis .
  qed
  \<comment> \<open>Step 3: card(V') = card(V) + 1.\<close>
  have hV_fin: "finite ?V"
  proof -
    have hep_fin: "\<forall>A\<in>\<A>. finite (?ep A)"
    proof (intro ballI)
      fix A assume "A \<in> \<A>"
      have "A \<subseteq> Y" "top1_is_arc_on A (subspace_topology Y TY A)" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)+
      then obtain h where "top1_homeomorphism_on I_set I_top A (subspace_topology Y TY A) h"
        unfolding top1_is_arc_on_def by (by100 blast)
      from arc_endpoints_are_boundary[OF hstrict hhaus \<open>A \<subseteq> Y\<close> \<open>top1_is_arc_on A _\<close> this]
      show "finite (?ep A)" by (by100 simp)
    qed
    show ?thesis unfolding top1_graph_vertex_set_def using hfin hep_fin by (by100 blast)
  qed
  have hcard_V': "card ?V' = card ?V + 1"
    using hV'_eq hp_not_V hV_fin by (by100 simp)
  \<comment> \<open>Step 4: card(\\<A>') = card(\\<A>) + 1.\<close>
  have hcard_A': "card \<A>' = card \<A> + 1"
  proof -
    \<comment> \<open>D1 \\<noteq> D2 (D1 contains a0 but D2's endpoint is {p, b0}, and a0 \\<noteq> p).\<close>
    have hpne_a0: "p \<noteq> a0"
    proof
      assume "p = a0"
      hence "p \<in> ?ep A0" using hep by (by100 blast)
      thus False using hp(2) by (by100 blast)
    qed
    have hpne_b0: "p \<noteq> b0"
    proof
      assume "p = b0"
      hence "p \<in> ?ep A0" using hep by (by100 blast)
      thus False using hp(2) by (by100 blast)
    qed
    have "D1 \<noteq> D2"
    proof
      assume "D1 = D2"
      hence "?ep D1 = ?ep D2" by simp
      hence "{a0, p} = {p, b0}" using hsplit(5) hsplit(6) by simp
      hence "a0 = b0 \<or> a0 = p" by (by100 blast)
      hence "a0 = b0" using hpne_a0 by (by100 blast)
      thus False using hep(2) by (by100 blast)
    qed
    have "A0 \<notin> \<A> - {A0}" by (by100 blast)
    have hfin': "finite (\<A> - {A0})" using hfin by (by100 blast)
    have hD1_not_rest: "D1 \<notin> \<A> - {A0} \<and> D2 \<notin> \<A> - {A0}"
    proof (intro conjI)
      show "D1 \<notin> \<A> - {A0}"
      proof
        assume "D1 \<in> \<A> - {A0}"
        hence "D1 \<in> \<A>" "D1 \<noteq> A0" by (by100 blast)+
        have "A0 \<inter> D1 \<subseteq> ?ep A0" using h\<A>_inter[rule_format, OF hA0 \<open>D1 \<in> \<A>\<close>] \<open>D1 \<noteq> A0\<close> by (by100 blast)
        have "p \<in> D1" using hsplit(2) by (by100 blast)
        hence "p \<in> A0 \<inter> D1" using hp(1) by (by100 blast)
        hence "p \<in> ?ep A0" using \<open>A0 \<inter> D1 \<subseteq> ?ep A0\<close> by (by100 blast)
        thus False using hp(2) by (by100 blast)
      qed
      show "D2 \<notin> \<A> - {A0}"
      proof
        assume "D2 \<in> \<A> - {A0}"
        hence "D2 \<in> \<A>" "D2 \<noteq> A0" by (by100 blast)+
        have "A0 \<inter> D2 \<subseteq> ?ep A0" using h\<A>_inter[rule_format, OF hA0 \<open>D2 \<in> \<A>\<close>] \<open>D2 \<noteq> A0\<close> by (by100 blast)
        have "p \<in> D2" using hsplit(2) by (by100 blast)
        hence "p \<in> A0 \<inter> D2" using hp(1) by (by100 blast)
        hence "p \<in> ?ep A0" using \<open>A0 \<inter> D2 \<subseteq> ?ep A0\<close> by (by100 blast)
        thus False using hp(2) by (by100 blast)
      qed
    qed
    have "(\<A> - {A0}) \<inter> {D1, D2} = {}" using hD1_not_rest by (by100 blast)
    have "card \<A>' = card ((\<A> - {A0}) \<union> {D1, D2})" unfolding \<A>'_def by simp
    also have "\<dots> = card (\<A> - {A0}) + card {D1, D2}"
      by (rule card_Un_disjoint[OF _ _ \<open>(\<A> - {A0}) \<inter> {D1, D2} = {}\<close>])
         (simp_all add: hfin)
    also have "\<dots> = (card \<A> - 1) + 2"
    proof -
      have "card (\<A> - {A0}) = card \<A> - 1" using hA0 hfin by (by100 simp)
      have "card {D1, D2} = 2" using \<open>D1 \<noteq> D2\<close> by (by100 simp)
      thus ?thesis using \<open>card (\<A> - {A0}) = card \<A> - 1\<close> by linarith
    qed
    also have "\<dots> = card \<A> + 1"
    proof -
      have "\<A> \<noteq> {}" using hA0 by (by100 blast)
      have "card \<A> \<ge> 1"
      proof -
        have "card \<A> \<noteq> 0" using \<open>\<A> \<noteq> {}\<close> hfin by (by100 auto)
        thus ?thesis by linarith
      qed
      thus ?thesis by linarith
    qed
    finally show ?thesis .
  qed
  \<comment> \<open>Step 5: Arithmetic.\<close>
  show ?thesis using hcard_V' hcard_A' by linarith
qed

\<comment> \<open>First entry point: a continuous path from outside a closed set to inside
   must cross the boundary. Used for the "endpoint containment" argument.\<close>
lemma closed_set_first_entry:
  assumes "closedin_on X TX B"
      and hconn: "top1_connected_on X TX"
      and hne_in: "\<exists>x \<in> X. x \<in> B"
      and hne_out: "\<exists>x \<in> X. x \<notin> B"
  shows "\<exists>y \<in> B. \<forall>U \<in> TX. y \<in> U \<longrightarrow> (\<exists>z \<in> U. z \<notin> B)"
proof (rule ccontr)
  assume hno: "\<not> (\<exists>y \<in> B. \<forall>U \<in> TX. y \<in> U \<longrightarrow> (\<exists>z \<in> U. z \<notin> B))"
  \<comment> \<open>Every y \\<in> B has a neighborhood entirely in B. So B is open.\<close>
  have "B \<in> TX"
  proof -
    have hB_sub: "B \<subseteq> X" using assms(1) unfolding closedin_on_def by (by100 blast)
    have hTX_top: "is_topology_on X TX" using hconn unfolding top1_connected_on_def by (by100 blast)
    \<comment> \<open>For every y \\<in> B: there's no open U with y \\<in> U and U not \\<subseteq> B.
       Negating: for every y \\<in> B, every open U containing y has U \\<subseteq> B.\<close>
    have hB_interior: "\<forall>y \<in> B. \<exists>U \<in> TX. y \<in> U \<and> U \<subseteq> B"
    proof (intro ballI)
      fix y assume "y \<in> B"
      \<comment> \<open>hno says: NOT (y \\<in> B and for all U open with y \\<in> U, \\<exists>z \\<in> U \\ B).
         I.e., for all y \\<in> B: \\<exists>U open, y \\<in> U, \\<forall>z \\<in> U. z \\<in> B.\<close>
      from hno \<open>y \<in> B\<close> have "\<not> (\<forall>U \<in> TX. y \<in> U \<longrightarrow> (\<exists>z \<in> U. z \<notin> B))" by (by100 blast)
      hence "\<exists>U \<in> TX. y \<in> U \<and> \<not> (\<exists>z \<in> U. z \<notin> B)" by (by100 blast)
      then obtain U where "U \<in> TX" "y \<in> U" "\<forall>z \<in> U. z \<in> B" by (by100 blast)
      thus "\<exists>U \<in> TX. y \<in> U \<and> U \<subseteq> B" by (by100 blast)
    qed
    \<comment> \<open>B = \\<Union>{U \\<in> TX. U \\<subseteq> B, \\<exists>y \\<in> B. y \\<in> U}. Union of open sets is open.\<close>
    have "B \<subseteq> \<Union>{U \<in> TX. U \<subseteq> B}"
    proof (intro subsetI)
      fix y assume "y \<in> B"
      from hB_interior[rule_format, OF this]
      obtain U where "U \<in> TX" "y \<in> U" "U \<subseteq> B" by (by100 blast)
      thus "y \<in> \<Union>{U \<in> TX. U \<subseteq> B}" by (by100 blast)
    qed
    moreover have "\<Union>{U \<in> TX. U \<subseteq> B} \<subseteq> B" by (by100 blast)
    ultimately have "B = \<Union>{U \<in> TX. U \<subseteq> B}" by (by100 blast)
    moreover have "\<Union>{U \<in> TX. U \<subseteq> B} \<in> TX"
    proof -
      have "{U \<in> TX. U \<subseteq> B} \<subseteq> TX" by (by100 blast)
      from conjunct1[OF conjunct2[OF conjunct2[OF hTX_top[unfolded is_topology_on_def]]]]
      have "\<forall>U. U \<subseteq> TX \<longrightarrow> \<Union>U \<in> TX" by (by100 blast)
      thus ?thesis using \<open>{U \<in> TX. U \<subseteq> B} \<subseteq> TX\<close> by (by100 blast)
    qed
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>B is open AND closed. B is nonempty and B \\<noteq> X.
     X \\ B is open (since B is closed, i.e., X \\ B \\<in> TX) and nonempty.
     This gives a disconnection of X, contradicting connectedness.\<close>
  have "X - B \<in> TX" using assms(1) unfolding closedin_on_def by (by100 blast)
  have hB_sub2: "B \<subseteq> X" using assms(1) unfolding closedin_on_def by (by100 blast)
  have "B \<noteq> {}" using hne_in by (by100 blast)
  have "X - B \<noteq> {}"
  proof -
    from hne_out obtain x where "x \<in> X" "x \<notin> B" by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  have "B \<inter> (X - B) = {}" by (by100 blast)
  have "B \<union> (X - B) = X" using hB_sub2 by (by100 blast)
  from hconn[unfolded top1_connected_on_def]
  have "\<not> (\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X)"
    by (by100 blast)
  from this \<open>B \<in> TX\<close> \<open>X - B \<in> TX\<close> \<open>B \<noteq> {}\<close> \<open>X - B \<noteq> {}\<close> \<open>B \<inter> (X - B) = {}\<close> \<open>B \<union> (X - B) = X\<close>
  show False by (by100 blast)
qed

\<comment> \<open>In a connected Hausdorff space, a proper nonempty closed set has nonempty boundary.
   Equivalently: there exists a point in B that is a limit point of X \\ B.\<close>

\<comment> \<open>In a Hausdorff graph, if point y is interior to arc A and y has an open neighborhood U
   such that U is contained in A, then A \\<inter> B is a neighborhood of y in A for any closed B containing y.
   (Because U \\<subseteq> A and U is open.)\<close>
\<comment> \<open>Key real-analysis fact: a closed subset of [0,1] containing an interior point t0
   (where t0 is approached by points NOT in the set) cannot have t0 as a boundary point
   if t0 has an open neighborhood entirely within the set. So if the set's interior is open
   and contains t0, then points near t0 are also in the set.\<close>

\<comment> \<open>Coherent topology holds for ANY finite arc decomposition of a graph, not just the
   one from the definition. Key insight: the (\\<Leftarrow>) direction uses finiteness of
   the alternative decomposition + compactness of arcs in Hausdorff Y.\<close>
lemma graph_coherent_any_decomposition:
  fixes Y :: "'a set" and TY :: "'a set set"
  assumes hgraph: "top1_is_graph_on Y TY"
      and h\<A>1: "\<forall>A\<in>\<A>1. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
      and h\<A>1_cover: "\<Union>\<A>1 = Y"
      and h\<A>1_inter: "\<forall>A\<in>\<A>1. \<forall>B\<in>\<A>1. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and hfin1: "finite \<A>1"
  shows "\<forall>C. C \<subseteq> Y \<longrightarrow>
      (closedin_on Y TY C \<longleftrightarrow>
       (\<forall>A\<in>\<A>1. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
proof (intro allI impI iffI)
  fix C assume "C \<subseteq> Y"
  \<comment> \<open>(\\<Rightarrow>) C closed in Y \\<Rightarrow> C \\<inter> A closed in A for each A \\<in> \\<A>1.
     Trivial: closed in ambient \\<Rightarrow> closed in subspace.\<close>
  show "closedin_on Y TY C \<Longrightarrow>
      \<forall>A\<in>\<A>1. closedin_on A (subspace_topology Y TY A) (A \<inter> C)"
  proof (intro impI ballI)
    fix A assume hC_cl: "closedin_on Y TY C" and "A \<in> \<A>1"
    have "A \<subseteq> Y" using h\<A>1 \<open>A \<in> \<A>1\<close> by (by100 blast)
    have "C \<inter> A \<subseteq> A" by (by100 blast)
    have hTY: "is_topology_on Y TY"
      using hgraph unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
    from Theorem_17_2[OF hTY \<open>A \<subseteq> Y\<close>, of "A \<inter> C"]
    have "closedin_on A (subspace_topology Y TY A) (A \<inter> C) =
        (\<exists>D. closedin_on Y TY D \<and> A \<inter> C = D \<inter> A)" .
    moreover have "\<exists>D. closedin_on Y TY D \<and> A \<inter> C = D \<inter> A"
    proof (rule exI[of _ C])
      show "closedin_on Y TY C \<and> A \<inter> C = C \<inter> A" using hC_cl by (by100 blast)
    qed
    ultimately show "closedin_on A (subspace_topology Y TY A) (A \<inter> C)" by simp
  qed
next
  fix C assume "C \<subseteq> Y"
  \<comment> \<open>(\\<Leftarrow>) \\<forall>A \\<in> \\<A>1. C \\<inter> A closed in A \\<Rightarrow> C closed in Y.
     Use original \\<A>0 coherent topology: need C \\<inter> A0 closed in A0 for each A0 \\<in> \\<A>0.
     A0 = \\<Union>{A0 \\<inter> A1 : A1 \\<in> \\<A>1} (since A0 \\<subseteq> Y = \\<Union>\\<A>1).
     C \\<inter> A0 = \\<Union>{C \\<inter> A0 \\<inter> A1 : A1 \\<in> \\<A>1}.
     Each C \\<inter> A0 \\<inter> A1 = (C \\<inter> A1) \\<inter> A0, closed in A0
     (because C \\<inter> A1 closed in A1, so C \\<inter> A1 = F \\<inter> A1 for F closed in Y,
      then (F \\<inter> A1) \\<inter> A0 = F \\<inter> (A1 \\<inter> A0), F \\<inter> A0 closed in A0, A1 \\<inter> A0 closed in A0,
      intersection of closed = closed).
     Finite union of closed sets in A0 = closed in A0. \\<checkmark>\<close>
  show "\<forall>A\<in>\<A>1. closedin_on A (subspace_topology Y TY A) (A \<inter> C) \<Longrightarrow>
      closedin_on Y TY C"
  proof -
    assume h1_cl: "\<forall>A\<in>\<A>1. closedin_on A (subspace_topology Y TY A) (A \<inter> C)"
    \<comment> \<open>Extract internal decomposition \\<A>0 with coherent topology.\<close>
    have hstrict: "is_topology_on_strict Y TY"
      using hgraph unfolding top1_is_graph_on_def by (by100 blast)
    have hhaus: "is_hausdorff_on Y TY"
      using hgraph unfolding top1_is_graph_on_def by (by100 blast)
    have hTY: "is_topology_on Y TY"
      using hstrict unfolding is_topology_on_strict_def by (by100 blast)
    \<comment> \<open>Get internal \\<A>0 with coherent topology.\<close>
    obtain \<A>0 where h\<A>0_coh: "\<forall>D. D \<subseteq> Y \<longrightarrow>
         (closedin_on Y TY D \<longleftrightarrow>
          (\<forall>A\<in>\<A>0. closedin_on A (subspace_topology Y TY A) (A \<inter> D)))"
        and h\<A>0_cover: "\<Union>\<A>0 = Y"
        and h\<A>0_arcs: "\<forall>A\<in>\<A>0. A \<subseteq> Y"
    proof -
      from hgraph[unfolded top1_is_graph_on_def]
      have hex: "\<exists>\<A>00. (\<forall>A\<in>\<A>00. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A))
          \<and> \<Union>\<A>00 = Y
          \<and> (\<forall>A\<in>\<A>00. \<forall>B\<in>\<A>00. A \<noteq> B \<longrightarrow>
               A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
             \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
             \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2)
          \<and> (\<forall>C. C \<subseteq> Y \<longrightarrow>
               (closedin_on Y TY C \<longleftrightarrow>
                (\<forall>A\<in>\<A>00. closedin_on A (subspace_topology Y TY A) (A \<inter> C))))"
        by (by100 blast)
      then obtain \<A>00 where
        h00: "(\<forall>A\<in>\<A>00. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A))
          \<and> \<Union>\<A>00 = Y
          \<and> (\<forall>A\<in>\<A>00. \<forall>B\<in>\<A>00. A \<noteq> B \<longrightarrow>
               A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
             \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
             \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2)
          \<and> (\<forall>C. C \<subseteq> Y \<longrightarrow>
               (closedin_on Y TY C \<longleftrightarrow>
                (\<forall>A\<in>\<A>00. closedin_on A (subspace_topology Y TY A) (A \<inter> C))))"
        by (by5000 auto)
      have h1: "\<forall>A\<in>\<A>00. A \<subseteq> Y" using conjunct1[OF h00] by (by100 blast)
      have h2: "\<Union>\<A>00 = Y" using conjunct1[OF conjunct2[OF h00]] .
      have h4: "\<forall>C. C \<subseteq> Y \<longrightarrow>
           (closedin_on Y TY C \<longleftrightarrow>
            (\<forall>A\<in>\<A>00. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
        using conjunct2[OF conjunct2[OF conjunct2[OF h00]]] .
      from that[OF h4 h2 h1] show ?thesis .
    qed
    \<comment> \<open>Need: C \\<inter> A0 closed in A0 for each A0 \\<in> \\<A>0.\<close>
    have "\<forall>A0\<in>\<A>0. closedin_on A0 (subspace_topology Y TY A0) (A0 \<inter> C)"
    proof (intro ballI)
      fix A0 assume "A0 \<in> \<A>0"
      have hA0_sub: "A0 \<subseteq> Y" using h\<A>0_arcs \<open>A0 \<in> \<A>0\<close> by (by100 blast)
      \<comment> \<open>A0 \\<inter> C = \\<Union>{A0 \\<inter> C \\<inter> A1 : A1 \\<in> \\<A>1}.\<close>
      have hA0C_union: "A0 \<inter> C = (\<Union>A1\<in>\<A>1. A0 \<inter> C \<inter> A1)"
      proof -
        have "A0 \<subseteq> Y" using hA0_sub .
        have "A0 \<subseteq> \<Union>\<A>1" using hA0_sub h\<A>1_cover by simp
        thus ?thesis by (by100 blast)
      qed
      \<comment> \<open>Each A0 \\<inter> C \\<inter> A1 is closed in A0.\<close>
      have "\<forall>A1\<in>\<A>1. closedin_on A0 (subspace_topology Y TY A0) (A0 \<inter> C \<inter> A1)"
      proof (intro ballI)
        fix A1 assume "A1 \<in> \<A>1"
        \<comment> \<open>C \\<inter> A1 is closed in A1 (from h1\\_cl).\<close>
        have "closedin_on A1 (subspace_topology Y TY A1) (A1 \<inter> C)"
          using h1_cl \<open>A1 \<in> \<A>1\<close> by (by100 blast)
        \<comment> \<open>C \\<inter> A1 = F \\<inter> A1 for some F closed in Y (Theorem\\_17\\_2).\<close>
        have hA1_sub: "A1 \<subseteq> Y" using h\<A>1 \<open>A1 \<in> \<A>1\<close> by (by100 blast)
        from Theorem_17_2[OF hTY hA1_sub, of "A1 \<inter> C"]
        have "closedin_on A1 (subspace_topology Y TY A1) (A1 \<inter> C) =
            (\<exists>F. closedin_on Y TY F \<and> A1 \<inter> C = F \<inter> A1)" .
        with \<open>closedin_on A1 _ (A1 \<inter> C)\<close>
        obtain F where hF: "closedin_on Y TY F" "A1 \<inter> C = F \<inter> A1" by (by100 blast)
        \<comment> \<open>A0 \\<inter> C \\<inter> A1 = (F \\<inter> A0) \\<inter> (A1 \\<inter> A0).\<close>
        have "A0 \<inter> C \<inter> A1 = A0 \<inter> (A1 \<inter> C)" by (by100 blast)
        also have "\<dots> = A0 \<inter> (F \<inter> A1)" using hF(2) by simp
        also have "\<dots> = (F \<inter> A0) \<inter> (A1 \<inter> A0)" by (by100 blast)
        finally have hACA: "A0 \<inter> C \<inter> A1 = (F \<inter> A0) \<inter> (A1 \<inter> A0)" .
        \<comment> \<open>F \\<inter> A0 closed in A0 (F closed in Y, restriction to subspace).\<close>
        have "closedin_on A0 (subspace_topology Y TY A0) (F \<inter> A0)"
        proof -
          from Theorem_17_2[OF hTY hA0_sub, of "F \<inter> A0"]
          have "closedin_on A0 (subspace_topology Y TY A0) (F \<inter> A0) =
              (\<exists>G. closedin_on Y TY G \<and> F \<inter> A0 = G \<inter> A0)" .
          moreover have "\<exists>G. closedin_on Y TY G \<and> F \<inter> A0 = G \<inter> A0"
          proof (rule exI[of _ F])
            show "closedin_on Y TY F \<and> F \<inter> A0 = F \<inter> A0" using hF(1) by (by100 blast)
          qed
          ultimately show ?thesis by simp
        qed
        \<comment> \<open>A1 \\<inter> A0 closed in A0 (A1 compact \\<Rightarrow> closed in Hausdorff \\<Rightarrow> closed in subspace).\<close>
        have "closedin_on A0 (subspace_topology Y TY A0) (A1 \<inter> A0)"
        proof -
          \<comment> \<open>A1 is compact (arc \\<cong> [0,1]), hence closed in Hausdorff Y.\<close>
          have "closedin_on Y TY A1"
          proof -
            have "top1_is_arc_on A1 (subspace_topology Y TY A1)" using h\<A>1 \<open>A1 \<in> \<A>1\<close> by (by100 blast)
            then obtain hA1c where "top1_homeomorphism_on I_set I_top A1 (subspace_topology Y TY A1) hA1c"
              unfolding top1_is_arc_on_def by (by100 blast)
            have "top1_compact_on I_set I_top"
              unfolding top1_unit_interval_def top1_unit_interval_topology_def
              using Theorem_27_1[of "0::real" 1] by (by100 simp)
            have hA1_top: "is_topology_on A1 (subspace_topology Y TY A1)"
              by (rule subspace_topology_is_topology_on[OF hTY hA1_sub])
            have hA1c_cont: "top1_continuous_map_on I_set I_top A1 (subspace_topology Y TY A1) hA1c"
              using \<open>top1_homeomorphism_on _ _ _ _ hA1c\<close> unfolding top1_homeomorphism_on_def by (by100 blast)
            have "hA1c ` I_set = A1"
              using \<open>top1_homeomorphism_on _ _ _ _ hA1c\<close> unfolding top1_homeomorphism_on_def bij_betw_def
              by (by100 blast)
            from top1_compact_on_continuous_image[OF \<open>top1_compact_on I_set I_top\<close> hA1_top hA1c_cont]
            have "top1_compact_on (hA1c ` I_set) (subspace_topology A1 (subspace_topology Y TY A1) (hA1c ` I_set))" .
            hence "top1_compact_on A1 (subspace_topology A1 (subspace_topology Y TY A1) A1)"
              using \<open>hA1c ` I_set = A1\<close> by simp
            moreover have "subspace_topology A1 (subspace_topology Y TY A1) A1 = subspace_topology Y TY A1"
            proof (rule subspace_topology_self)
              from subspace_topology_is_strict[OF hstrict hA1_sub]
              show "\<forall>U\<in>subspace_topology Y TY A1. U \<subseteq> A1"
                unfolding is_topology_on_strict_def by (by100 blast)
            qed
            ultimately have "top1_compact_on A1 (subspace_topology Y TY A1)" by simp
            from Theorem_26_3[OF hhaus hA1_sub this] show ?thesis .
          qed
          from Theorem_17_2[OF hTY hA0_sub, of "A1 \<inter> A0"]
          have "closedin_on A0 (subspace_topology Y TY A0) (A1 \<inter> A0) =
              (\<exists>G. closedin_on Y TY G \<and> A1 \<inter> A0 = G \<inter> A0)" .
          moreover have "\<exists>G. closedin_on Y TY G \<and> A1 \<inter> A0 = G \<inter> A0"
          proof (rule exI[of _ A1])
            show "closedin_on Y TY A1 \<and> A1 \<inter> A0 = A1 \<inter> A0"
              using \<open>closedin_on Y TY A1\<close> by (by100 blast)
          qed
          ultimately show ?thesis by simp
        qed
        \<comment> \<open>A0 \\<inter> C \\<inter> A1 = (F \\<inter> A0) \\<inter> (A1 \\<inter> A0). Intersection of closed = closed.\<close>
        show "closedin_on A0 (subspace_topology Y TY A0) (A0 \<inter> C \<inter> A1)"
        proof -
          have hA0_top: "is_topology_on A0 (subspace_topology Y TY A0)"
            by (rule subspace_topology_is_topology_on[OF hTY hA0_sub])
          \<comment> \<open>Complement of intersection = union of complements. Both complements are open.\<close>
          have "(A0 - (F \<inter> A0)) \<in> subspace_topology Y TY A0"
            using \<open>closedin_on A0 _ (F \<inter> A0)\<close> unfolding closedin_on_def by (by100 blast)
          have "(A0 - (A1 \<inter> A0)) \<in> subspace_topology Y TY A0"
            using \<open>closedin_on A0 _ (A1 \<inter> A0)\<close> unfolding closedin_on_def by (by100 blast)
          have "A0 - ((F \<inter> A0) \<inter> (A1 \<inter> A0)) = (A0 - (F \<inter> A0)) \<union> (A0 - (A1 \<inter> A0))" by (by100 blast)
          have "((A0 - (F \<inter> A0)) \<union> (A0 - (A1 \<inter> A0))) \<in> subspace_topology Y TY A0"
          proof -
            from conjunct1[OF conjunct2[OF conjunct2[OF hA0_top[unfolded is_topology_on_def]]]]
            have hunion: "\<forall>U. U \<subseteq> subspace_topology Y TY A0 \<longrightarrow> \<Union>U \<in> subspace_topology Y TY A0" .
            have "{(A0 - (F \<inter> A0)), (A0 - (A1 \<inter> A0))} \<subseteq> subspace_topology Y TY A0"
              using \<open>(A0 - (F \<inter> A0)) \<in> _\<close> \<open>(A0 - (A1 \<inter> A0)) \<in> _\<close> by (by100 blast)
            from hunion[rule_format, OF this]
            have "\<Union>{(A0 - (F \<inter> A0)), (A0 - (A1 \<inter> A0))} \<in> subspace_topology Y TY A0" .
            moreover have "\<Union>{(A0 - (F \<inter> A0)), (A0 - (A1 \<inter> A0))} =
                (A0 - (F \<inter> A0)) \<union> (A0 - (A1 \<inter> A0))" by (by100 blast)
            ultimately show ?thesis by simp
          qed
          have "(F \<inter> A0) \<inter> (A1 \<inter> A0) \<subseteq> A0" by (by100 blast)
          have "A0 - (A0 \<inter> C \<inter> A1) \<in> subspace_topology Y TY A0"
            using \<open>A0 - ((F \<inter> A0) \<inter> (A1 \<inter> A0)) = _\<close>
                  \<open>((A0 - (F \<inter> A0)) \<union> (A0 - (A1 \<inter> A0))) \<in> _\<close>
                  hACA by simp
          show ?thesis unfolding closedin_on_def
            using \<open>(F \<inter> A0) \<inter> (A1 \<inter> A0) \<subseteq> A0\<close> hACA
                  \<open>A0 - (A0 \<inter> C \<inter> A1) \<in> subspace_topology Y TY A0\<close>
            by (by100 blast)
        qed
      qed
      \<comment> \<open>C \\<inter> A0 = finite union of closed sets in A0 \\<Rightarrow> closed in A0.\<close>
      show "closedin_on A0 (subspace_topology Y TY A0) (A0 \<inter> C)"
      proof -
        have hA0_top: "is_topology_on A0 (subspace_topology Y TY A0)"
          by (rule subspace_topology_is_topology_on[OF hTY hA0_sub])
        \<comment> \<open>A0 \\<inter> C = \\<Union>{A0 \\<inter> C \\<inter> A1 : A1 \\<in> \\<A>1}. Finite union of closed = closed.\<close>
        from conjunct2[OF conjunct2[OF conjunct2[OF Theorem_17_1[OF hA0_top]]]]
        have hfin_closed: "\<forall>F. finite F \<longrightarrow>
            (\<forall>A\<in>F. closedin_on A0 (subspace_topology Y TY A0) A) \<longrightarrow>
            closedin_on A0 (subspace_topology Y TY A0) (\<Union>F)" by (by100 blast)
        have hfin_imgs: "finite ((\<lambda>A1. A0 \<inter> C \<inter> A1) ` \<A>1)" using hfin1 by (by100 blast)
        have hall_closed: "\<forall>A\<in>((\<lambda>A1. A0 \<inter> C \<inter> A1) ` \<A>1). closedin_on A0 (subspace_topology Y TY A0) A"
          using \<open>\<forall>A1\<in>\<A>1. closedin_on A0 _ (A0 \<inter> C \<inter> A1)\<close> by (by100 blast)
        have "closedin_on A0 (subspace_topology Y TY A0) (\<Union>((\<lambda>A1. A0 \<inter> C \<inter> A1) ` \<A>1))"
          using hfin_closed[rule_format] hfin_imgs hall_closed by (by100 blast)
        moreover have "(\<Union>((\<lambda>A1. A0 \<inter> C \<inter> A1) ` \<A>1)) = A0 \<inter> C"
          using hA0C_union by (by100 blast)
        ultimately show ?thesis by simp
      qed
    qed
    from h\<A>0_coh[rule_format, OF \<open>C \<subseteq> Y\<close>]
    show "closedin_on Y TY C" using \<open>\<forall>A0\<in>\<A>0. closedin_on A0 _ (A0 \<inter> C)\<close> by (by100 blast)
  qed
qed

\<comment> \<open>Arc interior is open in a graph with coherent topology.\<close>
lemma graph_arc_interior_open:
  fixes Y :: "'a set" and TY :: "'a set set"
  assumes hstrict: "is_topology_on_strict Y TY"
      and hhaus: "is_hausdorff_on Y TY"
      and h\<A>: "\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
      and h\<A>_cover: "\<Union>\<A> = Y"
      and h\<A>_inter: "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and h\<A>_coh: "\<forall>C. C \<subseteq> Y \<longrightarrow>
           (closedin_on Y TY C \<longleftrightarrow>
            (\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
      and hA0: "A0 \<in> \<A>"
  shows "A0 - top1_arc_endpoints_on A0 (subspace_topology Y TY A0) \<in> TY"
proof -
  let ?ep = "\<lambda>A. top1_arc_endpoints_on A (subspace_topology Y TY A)"
  let ?U = "A0 - ?ep A0"
  \<comment> \<open>Show Y \\ U is closed via coherent topology.\<close>
  have hU_sub: "?U \<subseteq> Y" using h\<A> hA0 by (by100 blast)
  have hA0_sub: "A0 \<subseteq> Y" using h\<A> hA0 by (by100 blast)
  have "closedin_on Y TY (Y - ?U)"
  proof -
    have "\<forall>B\<in>\<A>. closedin_on B (subspace_topology Y TY B) (B \<inter> (Y - ?U))"
    proof (intro ballI)
      fix B assume "B \<in> \<A>"
      show "closedin_on B (subspace_topology Y TY B) (B \<inter> (Y - ?U))"
      proof (cases "B = A0")
        case True
        \<comment> \<open>B = A0: B \\<inter> (Y \\ U) = A0 \\<inter> (Y \\ (A0 \\ ep(A0))) = ep(A0).
           ep(A0) is closed in A0 (finite set in Hausdorff subspace).\<close>
        have "B \<inter> (Y - ?U) = ?ep A0"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> B \<inter> (Y - ?U)"
          hence "x \<in> A0" "x \<notin> ?U" using True by (by100 blast)+
          hence "x \<in> ?ep A0"
          proof -
            have "?U = A0 - ?ep A0" by simp
            thus ?thesis using \<open>x \<in> A0\<close> \<open>x \<notin> ?U\<close> by (by100 blast)
          qed
          thus "x \<in> ?ep A0" .
        next
          fix x assume "x \<in> ?ep A0"
          hence "x \<in> A0" unfolding top1_arc_endpoints_on_def by (by100 blast)
          hence "x \<in> B" using True by simp
          have "x \<notin> ?U" using \<open>x \<in> ?ep A0\<close> by (by100 blast)
          have "x \<in> Y" using \<open>x \<in> A0\<close> hA0_sub by (by100 blast)
          thus "x \<in> B \<inter> (Y - ?U)" using \<open>x \<in> B\<close> \<open>x \<notin> ?U\<close> \<open>x \<in> Y\<close> by (by100 blast)
        qed
        moreover have "closedin_on A0 (subspace_topology Y TY A0) (?ep A0)"
        proof -
          \<comment> \<open>endpoints(A0) is finite (at most 2 points). Finite sets in Hausdorff are closed.\<close>
          have hA0_arc: "top1_is_arc_on A0 (subspace_topology Y TY A0)" using h\<A> hA0 by (by100 blast)
          obtain h0 where hh0: "top1_homeomorphism_on I_set I_top A0 (subspace_topology Y TY A0) h0"
            using hA0_arc unfolding top1_is_arc_on_def by (by100 blast)
          have hep_eq: "?ep A0 = {h0 0, h0 1}"
            by (rule arc_endpoints_are_boundary[OF hstrict hhaus hA0_sub hA0_arc hh0])
          have "finite (?ep A0)" using hep_eq by (by100 simp)
          have "?ep A0 \<subseteq> A0" unfolding top1_arc_endpoints_on_def by (by100 blast)
          have hA0_strict: "is_topology_on_strict A0 (subspace_topology Y TY A0)"
            by (rule subspace_topology_is_strict[OF hstrict hA0_sub])
          have hA0_haus: "is_hausdorff_on A0 (subspace_topology Y TY A0)"
            using conjunct2[OF conjunct2[OF Theorem_17_11]] hA0_sub hhaus by (by100 blast)
          \<comment> \<open>endpoints = {h0 0, h0 1}. Each singleton is closed in Hausdorff. Union of 2 closed = closed.\<close>
          have hA0_top: "is_topology_on A0 (subspace_topology Y TY A0)"
            using hA0_strict unfolding is_topology_on_strict_def by (by100 blast)
          have "h0 0 \<in> A0" "h0 1 \<in> A0"
          proof -
            have "bij_betw h0 I_set A0" using hh0 unfolding top1_homeomorphism_on_def by (by100 blast)
            have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
            have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
            show "h0 0 \<in> A0" using \<open>bij_betw h0 I_set A0\<close> \<open>0 \<in> I_set\<close> unfolding bij_betw_def by (by100 blast)
            show "h0 1 \<in> A0" using \<open>bij_betw h0 I_set A0\<close> \<open>1 \<in> I_set\<close> unfolding bij_betw_def by (by100 blast)
          qed
          have hT1: "top1_T1_on A0 (subspace_topology Y TY A0)"
            by (rule hausdorff_imp_T1_on[OF hA0_haus])
          have "closedin_on A0 (subspace_topology Y TY A0) {h0 0}"
            using hT1[unfolded top1_T1_on_def] \<open>h0 0 \<in> A0\<close> by (by100 blast)
          have "closedin_on A0 (subspace_topology Y TY A0) {h0 1}"
            using hT1[unfolded top1_T1_on_def] \<open>h0 1 \<in> A0\<close> by (by100 blast)
          have "?ep A0 = {h0 0} \<union> {h0 1}" using hep_eq by (by100 blast)
          \<comment> \<open>endpoints(A0) = {h0 0, h0 1} is closed (finite set in Hausdorff/T1 space).\<close>
          show ?thesis
          proof -
            have "?ep A0 \<subseteq> A0" unfolding top1_arc_endpoints_on_def by (by100 blast)
            have "finite (?ep A0)" using hep_eq by (by100 simp)
            have hT1': "\<forall>x\<in>A0. closedin_on A0 (subspace_topology Y TY A0) {x}"
              using hT1[unfolded top1_T1_on_def] by (by100 blast)
            \<comment> \<open>Finite union of closed singletons.\<close>
            have "?ep A0 = {h0 0, h0 1}" using hep_eq .
            have "closedin_on A0 (subspace_topology Y TY A0) {h0 0}" using hT1' \<open>h0 0 \<in> A0\<close> by (by100 blast)
            moreover have "closedin_on A0 (subspace_topology Y TY A0) {h0 1}" using hT1' \<open>h0 1 \<in> A0\<close> by (by100 blast)
            moreover have "{h0 0, h0 1} = {h0 0} \<union> {h0 1}" by (by100 blast)
            ultimately have "closedin_on A0 (subspace_topology Y TY A0) ({h0 0} \<union> {h0 1})"
            proof -
              assume h1: "closedin_on A0 (subspace_topology Y TY A0) {h0 0}"
              assume h2: "closedin_on A0 (subspace_topology Y TY A0) {h0 1}"
              assume h3: "{h0 0, h0 1} = {h0 0} \<union> {h0 1}"
              from conjunct2[OF conjunct2[OF conjunct2[OF Theorem_17_1[OF hA0_top]]]]
              have "\<forall>F. finite F \<longrightarrow> (\<forall>A\<in>F. closedin_on A0 (subspace_topology Y TY A0) A) \<longrightarrow>
                  closedin_on A0 (subspace_topology Y TY A0) (\<Union>F)" .
              from spec[OF this, of "{{h0 0}, {h0 1}}"]
              have "finite {{h0 0}, {h0 1}} \<longrightarrow> (\<forall>A\<in>{{h0 0}, {h0 1}}. closedin_on A0 (subspace_topology Y TY A0) A) \<longrightarrow>
                  closedin_on A0 (subspace_topology Y TY A0) (\<Union>{{h0 0}, {h0 1}})" .
              moreover have "finite {{h0 0}, {h0 1}}" by (by100 simp)
              moreover have "\<forall>A\<in>{{h0 0}, {h0 1}}. closedin_on A0 (subspace_topology Y TY A0) A"
                using h1 h2 by (by100 auto)
              ultimately have "closedin_on A0 (subspace_topology Y TY A0) (\<Union>{{h0 0}, {h0 1}})"
                by (by100 blast)
              thus ?thesis by (by100 simp)
            qed
            thus ?thesis using \<open>?ep A0 = {h0 0, h0 1}\<close> \<open>{h0 0, h0 1} = {h0 0} \<union> {h0 1}\<close> by simp
          qed
        qed
        ultimately show ?thesis using True by simp
      next
        case False
        \<comment> \<open>B \\<noteq> A0: B \\<inter> (A0 \\ ep(A0)) = {} (from intersection conditions).
           So B \\<inter> (Y \\ U) = B \\<inter> ((Y \\ A0) \\<union> ep(A0)) = B \\ (A0 \\ ep(A0)).
           Since B \\<inter> A0 \\<subseteq> ep(A0), we get B \\<inter> (A0 \\ ep(A0)) = {}.
           So B \\<inter> (Y \\ U) = B. B is closed in B (trivially).\<close>
        have hBA0: "B \<inter> A0 \<subseteq> ?ep A0"
        proof -
          have "A0 \<inter> B \<subseteq> ?ep A0"
            using h\<A>_inter[rule_format, OF hA0 \<open>B \<in> \<A>\<close>] False by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        have "B \<inter> ?U = {}" using hBA0 by (by100 blast)
        hence "B \<inter> (Y - ?U) = B"
        proof -
          have "B \<subseteq> Y" using h\<A> \<open>B \<in> \<A>\<close> by (by100 blast)
          thus ?thesis using \<open>B \<inter> ?U = {}\<close> by (by100 blast)
        qed
        moreover have "closedin_on B (subspace_topology Y TY B) B"
        proof -
          have "is_topology_on B (subspace_topology Y TY B)"
          proof -
            have "B \<subseteq> Y" using h\<A> \<open>B \<in> \<A>\<close> by (by100 blast)
            have "is_topology_on Y TY" using hstrict unfolding is_topology_on_strict_def by (by100 blast)
            from subspace_topology_is_topology_on[OF this \<open>B \<subseteq> Y\<close>] show ?thesis .
          qed
          have "B \<subseteq> B" by (by100 blast)
          have "(B - B) \<in> subspace_topology Y TY B"
          proof -
            have "B - B = {}" by (by100 blast)
            moreover have "{} \<in> subspace_topology Y TY B"
            proof -
              have "is_topology_on B (subspace_topology Y TY B)" using \<open>is_topology_on B _\<close> .
              thus ?thesis unfolding is_topology_on_def by (by100 blast)
            qed
            ultimately show ?thesis by simp
          qed
          thus ?thesis unfolding closedin_on_def using \<open>B \<subseteq> B\<close> by (by100 blast)
        qed
        ultimately show ?thesis by simp
      qed
    qed
    have "Y - ?U \<subseteq> Y" by (by100 blast)
    from h\<A>_coh[rule_format, OF this]
    show ?thesis using \<open>\<forall>B\<in>\<A>. closedin_on B _ _\<close> by (by100 blast)
  qed
  \<comment> \<open>Y \\ U closed \\<Rightarrow> U open.\<close>
  have "?U \<subseteq> Y" using hU_sub .
  from \<open>closedin_on Y TY (Y - ?U)\<close>
  have "(Y - (Y - ?U)) \<in> TY" unfolding closedin_on_def by (by100 blast)
  moreover have "Y - (Y - ?U) = ?U" using hU_sub by (by100 blast)
  ultimately show "?U \<in> TY" by simp
qed

\<comment> \<open>If B is an arc whose interior is open in a graph Y, and A is another arc sharing an
   interior point x with B, and the vertex sets of both decompositions are the same,
   then A \\<subseteq> B. Key argument: preimage of B\\ep(B) under hA is open,
   preimage of Y\\B is open, F\\<subseteq>{0,1}, connected (0,1), closure.\<close>
lemma graph_arc_containment_via_open_interior:
  fixes Y :: "'a set" and TY :: "'a set set"
  assumes hstrict: "is_topology_on_strict Y TY"
      and hhaus: "is_hausdorff_on Y TY"
      and hA_arc: "top1_is_arc_on A (subspace_topology Y TY A)" and hA_sub: "A \<subseteq> Y"
      and hB_arc: "top1_is_arc_on B (subspace_topology Y TY B)" and hB_sub: "B \<subseteq> Y"
      and hB_int_open: "B - top1_arc_endpoints_on B (subspace_topology Y TY B) \<in> TY"
      and hx: "x \<in> A" "x \<in> B"
         "x \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
         "x \<notin> top1_arc_endpoints_on B (subspace_topology Y TY B)"
      and hV_eq: "top1_graph_vertex_set Y TY \<A>1 = top1_graph_vertex_set Y TY \<A>2"
      and hA_in: "A \<in> \<A>1" and hB_in: "B \<in> \<A>2"
      and h\<A>1_inter: "\<forall>A\<in>\<A>1. \<forall>B\<in>\<A>1. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
      and h\<A>2_inter: "\<forall>A\<in>\<A>2. \<forall>B\<in>\<A>2. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
  shows "A \<subseteq> B"
proof -
  let ?ep = "\<lambda>C. top1_arc_endpoints_on C (subspace_topology Y TY C)"
  have hTY: "is_topology_on Y TY" using hstrict unfolding is_topology_on_strict_def by (by100 blast)
  have hI_top: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  \<comment> \<open>Step 1: Get homeomorphism hA: [0,1] \\<rightarrow> A and its properties.\<close>
  obtain hA where hhA: "top1_homeomorphism_on I_set I_top A (subspace_topology Y TY A) hA"
    using hA_arc unfolding top1_is_arc_on_def by (by100 blast)
  have hA_bij: "bij_betw hA I_set A" using hhA unfolding top1_homeomorphism_on_def by (by100 blast)
  have hA_surj: "hA ` I_set = A" using hA_bij unfolding bij_betw_def by (by100 blast)
  have hA_inj: "inj_on hA I_set" using hA_bij unfolding bij_betw_def by (by100 blast)
  have hA_cont: "top1_continuous_map_on I_set I_top A (subspace_topology Y TY A) hA"
    using hhA unfolding top1_homeomorphism_on_def by (by100 blast)
  have hTA_top: "is_topology_on A (subspace_topology Y TY A)"
    by (rule subspace_topology_is_topology_on[OF hTY hA_sub])
  have hA_cont_Y: "top1_continuous_map_on I_set I_top Y TY hA"
    using expand_range[OF hI_top hTA_top hTY, rule_format, of hA] hA_cont hA_sub by (by100 blast)
  have hA_ep: "?ep A = {hA 0, hA 1}"
    by (rule arc_endpoints_are_boundary[OF hstrict hhaus hA_sub hA_arc hhA])
  \<comment> \<open>Step 2: x = hA(t\\_x) for some t\\_x \\<in> (0,1).\<close>
  have "x \<in> hA ` I_set" using hx(1) hA_surj by simp
  then obtain t_x where ht_x: "t_x \<in> I_set" "hA t_x = x" by (by100 blast)
  have ht_x_interior: "t_x \<noteq> 0 \<and> t_x \<noteq> 1"
  proof (intro conjI)
    show "t_x \<noteq> 0"
    proof
      assume "t_x = 0"
      hence "hA t_x = hA 0" by simp
      hence "x = hA 0" using ht_x(2) by simp
      hence "x \<in> ?ep A" using hA_ep by (by100 blast)
      thus False using hx(3) by (by100 blast)
    qed
    show "t_x \<noteq> 1"
    proof
      assume "t_x = 1"
      hence "hA t_x = hA 1" by simp
      hence "x = hA 1" using ht_x(2) by simp
      hence "x \<in> ?ep A" using hA_ep by (by100 blast)
      thus False using hx(3) by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 3: B is closed in Y.\<close>
  have hB_closed: "closedin_on Y TY B"
  proof -
    obtain hBc where "top1_homeomorphism_on I_set I_top B (subspace_topology Y TY B) hBc"
      using hB_arc unfolding top1_is_arc_on_def by (by100 blast)
    have "top1_compact_on I_set I_top"
      unfolding top1_unit_interval_def top1_unit_interval_topology_def
      using Theorem_27_1[of "0::real" 1] by (by100 simp)
    have hBc_cont: "top1_continuous_map_on I_set I_top B (subspace_topology Y TY B) hBc"
      using \<open>top1_homeomorphism_on _ _ _ _ hBc\<close> unfolding top1_homeomorphism_on_def by (by100 blast)
    have hTB: "is_topology_on B (subspace_topology Y TY B)"
      by (rule subspace_topology_is_topology_on[OF hTY hB_sub])
    from top1_compact_on_continuous_image[OF \<open>top1_compact_on I_set I_top\<close> hTB hBc_cont]
    have "top1_compact_on (hBc ` I_set) (subspace_topology B (subspace_topology Y TY B) (hBc ` I_set))" .
    have "hBc ` I_set = B"
      using \<open>top1_homeomorphism_on _ _ _ _ hBc\<close> unfolding top1_homeomorphism_on_def bij_betw_def
      by (by100 blast)
    hence "top1_compact_on B (subspace_topology B (subspace_topology Y TY B) B)"
      using \<open>top1_compact_on (hBc ` I_set) _\<close> by simp
    moreover have "subspace_topology B (subspace_topology Y TY B) B = subspace_topology Y TY B"
    proof (rule subspace_topology_self)
      from subspace_topology_is_strict[OF hstrict hB_sub]
      show "\<forall>U\<in>subspace_topology Y TY B. U \<subseteq> B"
        unfolding is_topology_on_strict_def by (by100 blast)
    qed
    ultimately have "top1_compact_on B (subspace_topology Y TY B)" by simp
    from Theorem_26_3[OF hhaus hB_sub this] show ?thesis .
  qed
  \<comment> \<open>Step 4: Preimage sets.\<close>
  let ?S_int = "{t \<in> I_set. hA t \<in> B - ?ep B}"
  let ?S_out = "{t \<in> I_set. hA t \<notin> B}"
  let ?F = "{t \<in> I_set. hA t \<in> ?ep B}"
  \<comment> \<open>S\\_int open (preimage of open B\\ep(B)).\<close>
  have hS_int_open: "?S_int \<in> I_top"
  proof -
    from hA_cont_Y[unfolded top1_continuous_map_on_def]
    have "\<forall>V\<in>TY. {x \<in> I_set. hA x \<in> V} \<in> I_top" by (by100 blast)
    from this[rule_format, OF hB_int_open] show ?thesis by (by100 blast)
  qed
  \<comment> \<open>S\\_out open (complement of closed preimage).\<close>
  have hS_out_open: "?S_out \<in> I_top"
  proof -
    have "closedin_on I_set I_top {t \<in> I_set. hA t \<in> B}"
      by (rule continuous_preimage_closedin[OF hI_top hTY hA_cont_Y hB_closed])
    from this[unfolded closedin_on_def]
    have "(I_set - {t \<in> I_set. hA t \<in> B}) \<in> I_top" by (by100 blast)
    moreover have "I_set - {t \<in> I_set. hA t \<in> B} = ?S_out" by (by100 blast)
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>F \\<subseteq> {0, 1}.\<close>
  have hF_sub: "?F \<subseteq> {0, 1}"
  proof (intro subsetI)
    fix t assume "t \<in> ?F"
    hence ht_I: "t \<in> I_set" and ht_ep: "hA t \<in> ?ep B" by (by100 blast)+
    have "hA t \<in> top1_graph_vertex_set Y TY \<A>2"
      unfolding top1_graph_vertex_set_def using hB_in ht_ep by (by100 blast)
    hence "hA t \<in> top1_graph_vertex_set Y TY \<A>1" using hV_eq by simp
    have "hA t \<in> A" using ht_I hA_surj by (by100 blast)
    have "hA t \<in> ?ep A"
    proof -
      from \<open>hA t \<in> top1_graph_vertex_set Y TY \<A>1\<close>
      obtain A' where "A' \<in> \<A>1" "hA t \<in> ?ep A'"
        unfolding top1_graph_vertex_set_def by (by100 blast)
      show ?thesis
      proof (cases "A' = A")
        case True thus ?thesis using \<open>hA t \<in> ?ep A'\<close> by simp
      next
        case False
        have "hA t \<in> A'" using \<open>hA t \<in> ?ep A'\<close> unfolding top1_arc_endpoints_on_def by (by100 blast)
        hence "hA t \<in> A \<inter> A'" using \<open>hA t \<in> A\<close> by (by100 blast)
        thus ?thesis using h\<A>1_inter[rule_format, OF hA_in \<open>A' \<in> \<A>1\<close>] False by (by100 blast)
      qed
    qed
    hence "hA t \<in> {hA 0, hA 1}" using hA_ep by (by100 blast)
    have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    from \<open>hA t \<in> {hA 0, hA 1}\<close>
    have "hA t = hA 0 \<or> hA t = hA 1" by (by100 blast)
    thus "t \<in> {0, 1}"
    proof
      assume "hA t = hA 0"
      from inj_onD[OF hA_inj this ht_I h0I] show ?thesis by (by100 blast)
    next
      assume "hA t = hA 1"
      from inj_onD[OF hA_inj this ht_I h1I] show ?thesis by (by100 blast)
    qed
  qed
  \<comment> \<open>Partition and connectedness.\<close>
  have hint_partition: "\<forall>t. t \<in> I_set \<and> t \<noteq> 0 \<and> t \<noteq> 1 \<longrightarrow> t \<in> ?S_int \<or> t \<in> ?S_out"
    using hF_sub by (by100 blast)
  have h12_in: "t_x \<in> ?S_int" using ht_x hx(2) hx(4) ht_x_interior by (by100 blast)
  have hS_out_empty: "\<forall>t. 0 < t \<and> t < 1 \<longrightarrow> t \<in> I_set \<longrightarrow> hA t \<in> B"
  proof (intro allI impI)
    fix t assume ht12: "0 < t \<and> t < 1" and ht_I: "t \<in> I_set"
    show "hA t \<in> B"
    proof (rule ccontr)
      assume "hA t \<notin> B"
      hence "t \<in> ?S_out" using ht_I by (by100 blast)
      let ?I01 = "{t. (0::real) < t \<and> t < 1}"
      have hI01_sub: "?I01 \<subseteq> I_set" unfolding top1_unit_interval_def by (by100 auto)
      have h01_conn: "connected ?I01"
      proof -
        have "?I01 = {(0::real)<..<1}" by (by100 auto)
        thus ?thesis using connected_Ioo[of "0::real" 1] by simp
      qed
      obtain U_r where "open U_r" "?S_int = U_r \<inter> I_set"
      proof -
        have "?S_int \<in> subspace_topology UNIV top1_open_sets I_set"
          using hS_int_open unfolding top1_unit_interval_topology_def .
        then obtain U where "U \<in> top1_open_sets" "?S_int = U \<inter> I_set"
          unfolding subspace_topology_def by (by100 blast)
        have "open U" using \<open>U \<in> top1_open_sets\<close> unfolding top1_open_sets_def by (by100 blast)
        thus thesis using that \<open>?S_int = U \<inter> I_set\<close> by (by100 blast)
      qed
      obtain V_r where "open V_r" "?S_out = V_r \<inter> I_set"
      proof -
        have "?S_out \<in> subspace_topology UNIV top1_open_sets I_set"
          using hS_out_open unfolding top1_unit_interval_topology_def .
        then obtain V where "V \<in> top1_open_sets" "?S_out = V \<inter> I_set"
          unfolding subspace_topology_def by (by100 blast)
        have "open V" using \<open>V \<in> top1_open_sets\<close> unfolding top1_open_sets_def by (by100 blast)
        thus thesis using that \<open>?S_out = V \<inter> I_set\<close> by (by100 blast)
      qed
      have hI01_open: "open ?I01"
      proof -
        have "?I01 = {(0::real)<..<1}" by (by100 auto)
        thus ?thesis by (by100 auto)
      qed
      have "U_r \<inter> ?I01 \<noteq> {}"
        using h12_in \<open>?S_int = U_r \<inter> I_set\<close> \<open>t_x \<noteq> 0 \<and> t_x \<noteq> 1\<close> ht_x(1)
      proof -
        have "t_x \<in> ?S_int" using h12_in .
        moreover have "t_x \<in> ?I01" using ht_x_interior ht_x(1)
          unfolding top1_unit_interval_def by (by100 auto)
        ultimately show ?thesis using \<open>?S_int = U_r \<inter> I_set\<close> by (by100 blast)
      qed
      have "V_r \<inter> ?I01 \<noteq> {}" using \<open>t \<in> ?S_out\<close> \<open>?S_out = V_r \<inter> I_set\<close> ht12 by (by100 blast)
      have hU01_open: "open (U_r \<inter> ?I01)" using \<open>open U_r\<close> hI01_open by (by100 auto)
      have hV01_open: "open (V_r \<inter> ?I01)" using \<open>open V_r\<close> hI01_open by (by100 auto)
      have h_cover01: "?I01 \<subseteq> (U_r \<inter> ?I01) \<union> (V_r \<inter> ?I01)"
        using hint_partition \<open>?S_int = U_r \<inter> I_set\<close> \<open>?S_out = V_r \<inter> I_set\<close> hI01_sub
        by (by100 blast)
      have h_disj01: "(U_r \<inter> ?I01) \<inter> (V_r \<inter> ?I01) \<inter> ?I01 = {}"
      proof -
        have "?S_int \<inter> ?S_out = {}" by (by100 blast)
        thus ?thesis using \<open>?S_int = U_r \<inter> I_set\<close> \<open>?S_out = V_r \<inter> I_set\<close> hI01_sub
          by (by100 blast)
      qed
      from connectedD[OF h01_conn hU01_open hV01_open h_disj01 h_cover01]
      show False using \<open>U_r \<inter> ?I01 \<noteq> {}\<close> \<open>V_r \<inter> ?I01 \<noteq> {}\<close> by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 5: Closure — all of [0,1] maps to B.\<close>
  have "\<forall>t \<in> I_set. hA t \<in> B"
  proof (intro ballI)
    fix t assume "t \<in> I_set"
    have "closedin_on I_set I_top {t \<in> I_set. hA t \<in> B}"
      by (rule continuous_preimage_closedin[OF hI_top hTY hA_cont_Y hB_closed])
    have hI_minus_sub: "I_set - {t \<in> I_set. hA t \<in> B} \<subseteq> {0, 1}"
    proof (intro subsetI)
      fix s assume "s \<in> I_set - {t \<in> I_set. hA t \<in> B}"
      hence "s \<in> I_set" "hA s \<notin> B" by (by100 blast)+
      show "s \<in> {0, 1}"
      proof -
        have "s \<le> 0 \<or> (0 < s \<and> s < 1) \<or> 1 \<le> s" by linarith
        thus ?thesis
        proof (elim disjE)
          assume "0 < s \<and> s < 1"
          from hS_out_empty[rule_format, OF this \<open>s \<in> I_set\<close>]
          show ?thesis using \<open>hA s \<notin> B\<close> by (by100 blast)
        next
          assume "s \<le> 0"
          thus ?thesis using \<open>s \<in> I_set\<close> unfolding top1_unit_interval_def by (by100 auto)
        next
          assume "1 \<le> s"
          thus ?thesis using \<open>s \<in> I_set\<close> unfolding top1_unit_interval_def by (by100 auto)
        qed
      qed
    qed
    have "I_set - {t \<in> I_set. hA t \<in> B} = {}"
    proof (rule ccontr)
      assume "I_set - {t \<in> I_set. hA t \<in> B} \<noteq> {}"
      then obtain s where hs: "s \<in> I_set - {t \<in> I_set. hA t \<in> B}" by (by100 blast)
      hence "s \<in> {0, 1}" using hI_minus_sub by (by100 blast)
      hence "s = 0 \<or> s = 1" by (by100 blast)
      \<comment> \<open>Extract R-open set, find point in (0,1) nearby, contradiction.\<close>
      have "(I_set - {t \<in> I_set. hA t \<in> B}) \<in> I_top"
        using \<open>closedin_on I_set I_top {t \<in> I_set. hA t \<in> B}\<close>
        unfolding closedin_on_def by (by100 blast)
      hence "(I_set - {t \<in> I_set. hA t \<in> B}) \<in> subspace_topology UNIV top1_open_sets I_set"
        unfolding top1_unit_interval_topology_def .
      then obtain U where "U \<in> top1_open_sets" "(I_set - {t \<in> I_set. hA t \<in> B}) = U \<inter> I_set"
        unfolding subspace_topology_def by (by100 blast)
      have "open U" using \<open>U \<in> top1_open_sets\<close> unfolding top1_open_sets_def by (by100 blast)
      hence "\<exists>U_r. open U_r \<and> (I_set - {t \<in> I_set. hA t \<in> B}) = U_r \<inter> I_set"
        using \<open>_ = U \<inter> I_set\<close> by (by100 blast)
      then obtain U_r where "open U_r" "I_set - {t \<in> I_set. hA t \<in> B} = U_r \<inter> I_set"
        by (by100 blast)
      have "s \<in> U_r" using hs \<open>_ = U_r \<inter> I_set\<close> by (by100 blast)
      from \<open>open U_r\<close>[unfolded open_dist, rule_format, OF \<open>s \<in> U_r\<close>]
      obtain e where "e > 0" "\<forall>y. dist y s < e \<longrightarrow> y \<in> U_r" by (by100 blast)
      obtain t' where "0 < t'" "t' < 1" "dist t' s < e"
      proof -
        from \<open>s = 0 \<or> s = 1\<close> show thesis
        proof
          assume "s = 0"
          have "min (e/2) (1/2) > 0" using \<open>e > 0\<close> by (by100 simp)
          have "min (e/2) (1/2) < 1" by (by100 simp)
          have "dist (min (e/2) (1/2)) 0 < e" using \<open>e > 0\<close> by (simp add: dist_real_def)
          thus thesis using that \<open>min _ _ > 0\<close> \<open>min _ _ < 1\<close> \<open>s = 0\<close> by (by100 blast)
        next
          assume "s = 1"
          have "max (1 - e/2) (1/2) > 0" using \<open>e > 0\<close> by (by100 simp)
          have "max (1 - e/2) (1/2) < 1" using \<open>e > 0\<close> by (by100 simp)
          have "dist (max (1 - e/2) (1/2)) 1 < e" using \<open>e > 0\<close> by (simp add: dist_real_def)
          thus thesis using that \<open>max _ _ > 0\<close> \<open>max _ _ < 1\<close> \<open>s = 1\<close> by (by100 blast)
        qed
      qed
      have "t' \<in> U_r" using \<open>\<forall>y. dist y s < e \<longrightarrow> y \<in> U_r\<close> \<open>dist t' s < e\<close> by (by100 blast)
      have "t' \<in> I_set" using \<open>0 < t'\<close> \<open>t' < 1\<close> unfolding top1_unit_interval_def by (by100 auto)
      hence "t' \<in> I_set - {t \<in> I_set. hA t \<in> B}"
        using \<open>t' \<in> U_r\<close> \<open>_ = U_r \<inter> I_set\<close> by (by100 blast)
      hence "hA t' \<notin> B" by (by100 blast)
      from hS_out_empty[rule_format] \<open>0 < t'\<close> \<open>t' < 1\<close> \<open>t' \<in> I_set\<close>
      have "hA t' \<in> B" by (by100 blast)
      show False using \<open>hA t' \<in> B\<close> \<open>hA t' \<notin> B\<close> by (by100 blast)
    qed
    thus "hA t \<in> B" using \<open>t \<in> I_set\<close> by (by100 blast)
  qed
  thus ?thesis using hA_surj by (by100 blast)
qed

\<comment> \<open>Two decompositions of a graph with the same vertex set must have the same arcs.
   Proof: each arc A in \\<A>1 has endpoints {a, b}. A is a connected subset of Y between a and b
   with no other vertices in its interior. A' in \\<A>2 also connects a and b with no interior vertices.
   Since both are arcs (homeomorphic to [0,1]) with the same endpoints in a Hausdorff space,
   and both are maximal connected segments between vertices, A = A'.\<close>
lemma graph_same_vertices_same_arcs:
  fixes Y :: "'a set" and TY :: "'a set set"
  assumes hgraph: "top1_is_graph_on Y TY"
      and h\<A>1: "\<forall>A\<in>\<A>1. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
      and h\<A>1_cover: "\<Union>\<A>1 = Y"
      and h\<A>1_inter: "\<forall>A\<in>\<A>1. \<forall>B\<in>\<A>1. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and hfin1: "finite \<A>1"
      and h\<A>2: "\<forall>A\<in>\<A>2. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
      and h\<A>2_cover: "\<Union>\<A>2 = Y"
      and h\<A>2_inter: "\<forall>A\<in>\<A>2. \<forall>B\<in>\<A>2. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and hfin2: "finite \<A>2"
      and hsame_V: "top1_graph_vertex_set Y TY \<A>1 = top1_graph_vertex_set Y TY \<A>2"
  shows "\<A>1 = \<A>2"
proof (rule set_eqI, rule iffI)
  let ?V = "top1_graph_vertex_set Y TY \<A>1"
  let ?ep = "\<lambda>A. top1_arc_endpoints_on A (subspace_topology Y TY A)"
  have hstrict: "is_topology_on_strict Y TY"
    using hgraph unfolding top1_is_graph_on_def by (by100 blast)
  have hhaus: "is_hausdorff_on Y TY"
    using hgraph unfolding top1_is_graph_on_def by (by100 blast)
  \<comment> \<open>Key fact: for distinct arcs A, B in the same decomposition, int(A) \\<inter> B = {}.
     Proof: A \\<inter> B \\<subseteq> endpoints(A) (from intersection conditions), so (A \\ endpoints(A)) \\<inter> B = {}.\<close>
  fix A assume hA_in_1: "A \<in> \<A>1"
  \<comment> \<open>Goal: A \\<in> \\<A>2.\<close>
  \<comment> \<open>Step 1: Pick an interior point x of A. x \\<in> Y \\ V.\<close>
  have hA_sub: "A \<subseteq> Y" and hA_arc: "top1_is_arc_on A (subspace_topology Y TY A)"
    using h\<A>1 hA_in_1 by (by100 blast)+
  obtain hA where hhA: "top1_homeomorphism_on I_set I_top A (subspace_topology Y TY A) hA"
    using hA_arc unfolding top1_is_arc_on_def by (by100 blast)
  have hA_ep: "?ep A = {hA 0, hA 1}"
    by (rule arc_endpoints_are_boundary[OF hstrict hhaus hA_sub hA_arc hhA])
  have hA01_ne: "hA 0 \<noteq> hA 1"
  proof
    assume "hA 0 = hA 1"
    have "inj_on hA I_set" using hhA unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    from inj_onD[OF this \<open>hA 0 = hA 1\<close>] show False unfolding top1_unit_interval_def by (by100 auto)
  qed
  let ?x = "hA (1/2)"
  have hx_in_A: "?x \<in> A"
  proof -
    have "bij_betw hA I_set A" using hhA unfolding top1_homeomorphism_on_def by (by100 blast)
    have "(1/2::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    thus ?thesis using \<open>bij_betw hA I_set A\<close> unfolding bij_betw_def by (by100 blast)
  qed
  have hx_not_ep: "?x \<notin> ?ep A"
  proof -
    have "inj_on hA I_set" using hhA unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have h12I: "(1/2::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have "?x \<noteq> hA 0"
    proof -
      have "(1/2::real) \<noteq> 0" by (by100 simp)
      thus ?thesis using \<open>inj_on hA I_set\<close> h12I h0I unfolding inj_on_def by (by100 blast)
    qed
    moreover have "?x \<noteq> hA 1"
    proof -
      have "(1/2::real) \<noteq> 1" by (by100 simp)
      thus ?thesis using \<open>inj_on hA I_set\<close> h12I h1I unfolding inj_on_def by (by100 blast)
    qed
    ultimately show ?thesis using hA_ep by (by100 blast)
  qed
  have hx_not_V: "?x \<notin> ?V"
  proof -
    have "\<forall>B\<in>\<A>1. ?x \<notin> ?ep B"
    proof (intro ballI)
      fix B assume "B \<in> \<A>1"
      show "?x \<notin> ?ep B"
      proof (cases "B = A")
        case True thus ?thesis using hx_not_ep by simp
      next
        case False
        have hAB: "A \<inter> B \<subseteq> ?ep A"
          using h\<A>1_inter[rule_format, OF hA_in_1 \<open>B \<in> \<A>1\<close>] False by (by100 blast)
        show ?thesis
        proof
          assume "?x \<in> ?ep B"
          hence "?x \<in> B" unfolding top1_arc_endpoints_on_def by (by100 blast)
          hence "?x \<in> A \<inter> B" using hx_in_A by (by100 blast)
          hence "?x \<in> ?ep A" using hAB by (by100 blast)
          thus False using hx_not_ep by (by100 blast)
        qed
      qed
    qed
    thus ?thesis unfolding top1_graph_vertex_set_def by (by100 blast)
  qed
  have "?x \<notin> top1_graph_vertex_set Y TY \<A>2" using hx_not_V hsame_V by simp
  \<comment> \<open>Step 2: x \\<in> Y = \\<Union>\\<A>2, so x \\<in> some arc B \\<in> \\<A>2.\<close>
  have "?x \<in> Y" using hx_in_A hA_sub by (by100 blast)
  have "?x \<in> \<Union>\<A>2" using \<open>?x \<in> Y\<close> h\<A>2_cover by simp
  then obtain B where hB_in_2: "B \<in> \<A>2" and hx_in_B: "?x \<in> B" by (by100 blast)
  have hB_sub: "B \<subseteq> Y" and hB_arc: "top1_is_arc_on B (subspace_topology Y TY B)"
    using h\<A>2 hB_in_2 by (by100 blast)+
  \<comment> \<open>Step 3: x is interior to B (since x \\<notin> V2 = V1).\<close>
  have hx_not_epB: "?x \<notin> ?ep B"
  proof
    assume "?x \<in> ?ep B"
    hence "?x \<in> top1_graph_vertex_set Y TY \<A>2"
      unfolding top1_graph_vertex_set_def using hB_in_2 by (by100 blast)
    thus False using \<open>?x \<notin> top1_graph_vertex_set Y TY \<A>2\<close> by (by100 blast)
  qed
  \<comment> \<open>Step 4: Show A = B.
     Both are arcs with x as interior point. Endpoints of B are in V = V1.
     The endpoints of B must be endpoints of A (argument via intersection conditions).
     Then A and B are arcs with the same endpoints, sharing interior point x.
     Since the arc interiors are disjoint within each decomposition and cover Y \\ V,
     A must equal B.\<close>
  \<comment> \<open>Step 4a: endpoints of B are in V1. Let {c, d} = endpoints(B).\<close>
  obtain hB where hhB: "top1_homeomorphism_on I_set I_top B (subspace_topology Y TY B) hB"
    using hB_arc unfolding top1_is_arc_on_def by (by100 blast)
  have hBep_raw: "?ep B = {hB 0, hB 1}"
    by (rule arc_endpoints_are_boundary[OF hstrict hhaus hB_sub hB_arc hhB])
  have hB01_ne: "hB 0 \<noteq> hB 1"
  proof
    assume "hB 0 = hB 1"
    have "inj_on hB I_set" using hhB unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    from inj_onD[OF this \<open>hB 0 = hB 1\<close>] show False unfolding top1_unit_interval_def by (by100 auto)
  qed
  let ?c = "hB 0" and ?d = "hB 1"
  have hBep: "?ep B = {?c, ?d}" using hBep_raw .
  have hcd_ne: "?c \<noteq> ?d" using hB01_ne .
  have "?c \<in> ?V" "?d \<in> ?V"
  proof -
    have "?c \<in> ?ep B" using hBep by (by100 blast)
    hence "?c \<in> top1_graph_vertex_set Y TY \<A>2"
      unfolding top1_graph_vertex_set_def using hB_in_2 by (by100 blast)
    thus "?c \<in> ?V" using hsame_V by simp
  next
    have "?d \<in> ?ep B" using hBep by (by100 blast)
    hence "?d \<in> top1_graph_vertex_set Y TY \<A>2"
      unfolding top1_graph_vertex_set_def using hB_in_2 by (by100 blast)
    thus "?d \<in> ?V" using hsame_V by simp
  qed
  \<comment> \<open>Step 4b: c and d are in A (via the covering argument).
     c \\<in> V1 = \\<Union>{endpoints(A') : A' \\<in> \\<A>1}. So c \\<in> endpoints(A') for some A' \\<in> \\<A>1.
     c \\<in> B (endpoint of B). x \\<in> A \\<inter> B. B connected.
     If c \\<notin> A, then c is in A' \\<noteq> A. B connects c (in A') and x (in A).
     B is connected and goes from A' to A, so B must pass through a vertex of V1
     at the boundary of A... This needs the coherent topology.\<close>
  \<comment> \<open>Actually: endpoints of B are {c, d}. Since B is an arc from c to d,
     and x \\<in> A \\<inter> B with x interior to both A and B:
     B goes from c through x to d. B \\<subseteq> Y = \\<Union>\\<A>1.
     At x, B is in arc A \\<in> \\<A>1. As B moves away from x toward c:
     B either stays in A (so c \\<in> A) or exits A at an endpoint of A.
     If B exits A at endpoint a, then a \\<in> B. a \\<in> V1 = V2, so a is endpoint of B.
     Hence a \\<in> {c, d}. So c = a or d = a, meaning one endpoint of B is an endpoint of A.
     Similarly for the other direction.\<close>
  have hTY_top: "is_topology_on Y TY"
    using hstrict unfolding is_topology_on_strict_def by (by100 blast)
  have hI_top: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  \<comment> \<open>Helper: B is closed in Y (compact in Hausdorff).\<close>
  have hB_closed: "closedin_on Y TY B"
  proof -
    have "top1_compact_on B (subspace_topology Y TY B)"
    proof -
      obtain hBc where "top1_homeomorphism_on I_set I_top B (subspace_topology Y TY B) hBc"
        using hB_arc unfolding top1_is_arc_on_def by (by100 blast)
      have "top1_compact_on I_set I_top"
        unfolding top1_unit_interval_def top1_unit_interval_topology_def
        using Theorem_27_1[of "0::real" 1] by (by100 simp)
      have hBc_cont: "top1_continuous_map_on I_set I_top B (subspace_topology Y TY B) hBc"
        using \<open>top1_homeomorphism_on _ _ _ _ hBc\<close> unfolding top1_homeomorphism_on_def by (by100 blast)
      have hB_top2: "is_topology_on B (subspace_topology Y TY B)"
        by (rule subspace_topology_is_topology_on[OF hTY_top hB_sub])
      from top1_compact_on_continuous_image[OF \<open>top1_compact_on I_set I_top\<close> hB_top2 hBc_cont]
      have "top1_compact_on (hBc ` I_set) (subspace_topology B (subspace_topology Y TY B) (hBc ` I_set))" .
      have "hBc ` I_set = B"
        using \<open>top1_homeomorphism_on _ _ _ _ hBc\<close> unfolding top1_homeomorphism_on_def bij_betw_def
        by (by100 blast)
      hence "top1_compact_on B (subspace_topology B (subspace_topology Y TY B) B)"
        using \<open>top1_compact_on (hBc ` I_set) _\<close> by simp
      moreover have "subspace_topology B (subspace_topology Y TY B) B = subspace_topology Y TY B"
      proof (rule subspace_topology_self)
        from subspace_topology_is_strict[OF hstrict hB_sub]
        show "\<forall>U\<in>subspace_topology Y TY B. U \<subseteq> B"
          unfolding is_topology_on_strict_def by (by100 blast)
      qed
      ultimately show ?thesis by simp
    qed
    from Theorem_26_3[OF hhaus hB_sub this] show ?thesis .
  qed
  \<comment> \<open>Helper: hA continuous from I\\_set to Y.\<close>
  have hA_cont: "top1_continuous_map_on I_set I_top A (subspace_topology Y TY A) hA"
    using hhA unfolding top1_homeomorphism_on_def by (by100 blast)
  have hTA_top: "is_topology_on A (subspace_topology Y TY A)"
    by (rule subspace_topology_is_topology_on[OF hTY_top hA_sub])
  have hA_cont_Y: "top1_continuous_map_on I_set I_top Y TY hA"
    using expand_range[OF hI_top hTA_top hTY_top, rule_format, of hA]
        hA_cont hA_sub by (by100 blast)
  \<comment> \<open>Note: \\<A>0 extraction from graph\\_on is no longer needed here.
     The proof uses coherent topology for \\<A>2 (via graph\\_coherent\\_any\\_decomposition) directly.\<close>
  \<comment> \<open>CLEANER PROOF using graph\\_coherent\\_any\\_decomposition:
     B \\ ep(B) is open in Y (from graph\\_arc\\_interior\\_open + coherent topology for \\<A>2).
     The preimage {t. hA(t) \\<in> B \\ ep(B)} is open in [0,1].
     The preimage {t. hA(t) \\<notin> B} is open in [0,1] (complement of closed).
     F = {t. hA(t) \\<in> ep(B)} has |F| \\<le> 2, and F \\<subseteq> {0, 1} (since ep(B) \\<subseteq> V2 = V1, and
     points of V1 on A are endpoints of A = {hA(0), hA(1)}).
     So (0,1) = open1 \\<union> open2 (disjoint). Connected (0,1): one must be empty.
     1/2 \\<in> open1 \\<Rightarrow> open2 = {} \\<Rightarrow> hA(t) \\<in> B for all t \\<in> (0,1).
     B closed \\<Rightarrow> hA(t) \\<in> B for all t \\<in> [0,1]. In particular v = hA(0) \\<in> B.\<close>
  \<comment> \<open>Get coherent topology for \\<A>2.\<close>
  have h\<A>2_coh: "\<forall>C. C \<subseteq> Y \<longrightarrow>
      (closedin_on Y TY C \<longleftrightarrow>
       (\<forall>A\<in>\<A>2. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
    by (rule graph_coherent_any_decomposition[OF hgraph h\<A>2 h\<A>2_cover h\<A>2_inter hfin2])
  \<comment> \<open>B \\ ep(B) is open in Y.\<close>
  have hB_int_open: "B - ?ep B \<in> TY"
    by (rule graph_arc_interior_open[OF hstrict hhaus h\<A>2 h\<A>2_cover h\<A>2_inter h\<A>2_coh hB_in_2])
  \<comment> \<open>KEY FACT: every point of A is in B. Proved by connectedness of (0,1).\<close>
  have hA_sub_B: "A \<subseteq> B"
  proof -
    have h1_inter_ep: "\<forall>A\<in>\<A>1. \<forall>B\<in>\<A>1. A \<noteq> B \<longrightarrow> A \<inter> B \<subseteq> ?ep A"
      using h\<A>1_inter by (by100 blast)
    have h2_inter_ep: "\<forall>A\<in>\<A>2. \<forall>B\<in>\<A>2. A \<noteq> B \<longrightarrow> A \<inter> B \<subseteq> ?ep A"
      using h\<A>2_inter by (by100 blast)
    from graph_arc_containment_via_open_interior[OF hstrict hhaus hA_arc hA_sub
        hB_arc hB_sub hB_int_open hx_in_A hx_in_B hx_not_ep hx_not_epB
        hsame_V hA_in_1 hB_in_2 h1_inter_ep h2_inter_ep]
    show ?thesis .
  qed
  have hep_A_sub_B: "?ep A \<subseteq> ?ep B"
  proof (intro subsetI)
    fix v assume "v \<in> ?ep A"
    \<comment> \<open>v \\<in> A (endpoint of A). A \\<subseteq> B. So v \\<in> B.\<close>
    have "v \<in> A" using \<open>v \<in> ?ep A\<close> unfolding top1_arc_endpoints_on_def by (by100 blast)
    have "v \<in> B" using \<open>v \<in> A\<close> hA_sub_B by (by100 blast)
    \<comment> \<open>v \\<in> B. Show v \\<in> ep(B): v \\<in> V1 = V2, so v is endpoint of some arc C \\<in> \\<A>2.
       If C = B: done. If C \\<noteq> B: v \\<in> B \\<inter> C \\<subseteq> ep(B).\<close>
    have "v \<in> ?V" using \<open>v \<in> ?ep A\<close> hA_in_1
      unfolding top1_graph_vertex_set_def by (by100 blast)
    hence "v \<in> top1_graph_vertex_set Y TY \<A>2" using hsame_V by simp
    from \<open>v \<in> top1_graph_vertex_set Y TY \<A>2\<close>
    obtain C where "C \<in> \<A>2" "v \<in> ?ep C"
      unfolding top1_graph_vertex_set_def by (by100 blast)
    show "v \<in> ?ep B"
    proof (cases "C = B")
      case True thus ?thesis using \<open>v \<in> ?ep C\<close> by simp
    next
      case False
      have "v \<in> C" using \<open>v \<in> ?ep C\<close> unfolding top1_arc_endpoints_on_def by (by100 blast)
      hence "v \<in> B \<inter> C" using \<open>v \<in> B\<close> by (by100 blast)
      have "B \<inter> C \<subseteq> ?ep B"
        using h\<A>2_inter[rule_format, OF hB_in_2 \<open>C \<in> \<A>2\<close>] False by (by100 blast)
      thus ?thesis using \<open>v \<in> B \<inter> C\<close> by (by100 blast)
    qed
  qed
  \<comment> \<open>A = B via A \\<subseteq> B (hA\\_sub\\_B) and B \\<subseteq> A (symmetric, using graph\\_arc\\_containment\\_via\\_open\\_interior).\<close>
  have "B \<subseteq> A"
  proof -
    have h\<A>1_coh_here: "\<forall>C. C \<subseteq> Y \<longrightarrow>
        (closedin_on Y TY C \<longleftrightarrow>
         (\<forall>D\<in>\<A>1. closedin_on D (subspace_topology Y TY D) (D \<inter> C)))"
      by (rule graph_coherent_any_decomposition[OF hgraph h\<A>1 h\<A>1_cover h\<A>1_inter hfin1])
    have hA_int_open_here: "A - ?ep A \<in> TY"
      by (rule graph_arc_interior_open[OF hstrict hhaus h\<A>1 h\<A>1_cover h\<A>1_inter h\<A>1_coh_here hA_in_1])
    have h2_inter_ep: "\<forall>C\<in>\<A>2. \<forall>D\<in>\<A>2. C \<noteq> D \<longrightarrow> C \<inter> D \<subseteq> ?ep C"
      using h\<A>2_inter by (by100 blast)
    have h1_inter_ep: "\<forall>C\<in>\<A>1. \<forall>D\<in>\<A>1. C \<noteq> D \<longrightarrow> C \<inter> D \<subseteq> ?ep C"
      using h\<A>1_inter by (by100 blast)
    from graph_arc_containment_via_open_interior[OF hstrict hhaus hB_arc hB_sub
        hA_arc hA_sub hA_int_open_here hx_in_B hx_in_A hx_not_epB hx_not_ep
        hsame_V[symmetric] hB_in_2 hA_in_1 h2_inter_ep h1_inter_ep]
    show ?thesis .
  qed
  have "A = B" using hA_sub_B \<open>B \<subseteq> A\<close> by (by100 blast)
  show "A \<in> \<A>2" using \<open>A = B\<close> hB_in_2 by simp
next
  \<comment> \<open>Symmetric: A \\<in> \\<A>2 \\<Rightarrow> A \\<in> \\<A>1. Identical argument with \\<A>1\\<leftrightarrow>\\<A>2 swapped.\<close>
  fix A assume hA_in_2: "A \<in> \<A>2"
  \<comment> \<open>Pick interior point, find B \\<in> \\<A>1 containing it, show A = B.\<close>
  let ?V = "top1_graph_vertex_set Y TY \<A>1"
  let ?ep = "\<lambda>A. top1_arc_endpoints_on A (subspace_topology Y TY A)"
  have hstrict: "is_topology_on_strict Y TY"
    using hgraph unfolding top1_is_graph_on_def by (by100 blast)
  have hhaus: "is_hausdorff_on Y TY"
    using hgraph unfolding top1_is_graph_on_def by (by100 blast)
  have hA_sub: "A \<subseteq> Y" and hA_arc: "top1_is_arc_on A (subspace_topology Y TY A)"
    using h\<A>2 hA_in_2 by (by100 blast)+
  obtain hA where hhA: "top1_homeomorphism_on I_set I_top A (subspace_topology Y TY A) hA"
    using hA_arc unfolding top1_is_arc_on_def by (by100 blast)
  have hA_ep: "?ep A = {hA 0, hA 1}"
    by (rule arc_endpoints_are_boundary[OF hstrict hhaus hA_sub hA_arc hhA])
  let ?x = "hA (1/2)"
  have hx_in_A: "?x \<in> A"
  proof -
    have "bij_betw hA I_set A" using hhA unfolding top1_homeomorphism_on_def by (by100 blast)
    have "(1/2::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    thus ?thesis using \<open>bij_betw hA I_set A\<close> unfolding bij_betw_def by (by100 blast)
  qed
  have hx_not_ep: "?x \<notin> ?ep A"
  proof -
    have "inj_on hA I_set" using hhA unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have h12I: "(1/2::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have "?x \<noteq> hA 0"
    proof -
      have "(1/2::real) \<noteq> 0" by (by100 simp)
      thus ?thesis using \<open>inj_on hA I_set\<close> h12I h0I unfolding inj_on_def by (by100 blast)
    qed
    moreover have "?x \<noteq> hA 1"
    proof -
      have "(1/2::real) \<noteq> 1" by (by100 simp)
      thus ?thesis using \<open>inj_on hA I_set\<close> h12I h1I unfolding inj_on_def by (by100 blast)
    qed
    ultimately show ?thesis using hA_ep by (by100 blast)
  qed
  \<comment> \<open>x not in V2 (same argument as forward direction for V1).\<close>
  have hx_not_V2: "?x \<notin> top1_graph_vertex_set Y TY \<A>2"
  proof -
    have "\<forall>B\<in>\<A>2. ?x \<notin> ?ep B"
    proof (intro ballI)
      fix B assume "B \<in> \<A>2"
      show "?x \<notin> ?ep B"
      proof (cases "B = A")
        case True thus ?thesis using hx_not_ep by simp
      next
        case False
        show ?thesis
        proof
          assume "?x \<in> ?ep B"
          hence "?x \<in> B" unfolding top1_arc_endpoints_on_def by (by100 blast)
          hence "?x \<in> A \<inter> B" using hx_in_A by (by100 blast)
          have "A \<inter> B \<subseteq> ?ep A"
            using h\<A>2_inter[rule_format, OF hA_in_2 \<open>B \<in> \<A>2\<close>] False by (by100 blast)
          hence "?x \<in> ?ep A" using \<open>?x \<in> A \<inter> B\<close> by (by100 blast)
          thus False using hx_not_ep by (by100 blast)
        qed
      qed
    qed
    thus ?thesis unfolding top1_graph_vertex_set_def by (by100 blast)
  qed
  have "?x \<notin> ?V" using hx_not_V2 hsame_V by simp
  \<comment> \<open>x \\<in> Y = \\<Union>\\<A>1, find B \\<in> \\<A>1 containing x.\<close>
  have "?x \<in> Y" using hx_in_A hA_sub by (by100 blast)
  have "?x \<in> \<Union>\<A>1" using \<open>?x \<in> Y\<close> h\<A>1_cover by simp
  then obtain B where hB_in_1: "B \<in> \<A>1" and hx_in_B: "?x \<in> B" by (by100 blast)
  have hB_sub: "B \<subseteq> Y" and hB_arc: "top1_is_arc_on B (subspace_topology Y TY B)"
    using h\<A>1 hB_in_1 by (by100 blast)+
  have hx_not_epB: "?x \<notin> ?ep B"
  proof
    assume "?x \<in> ?ep B"
    hence "?x \<in> top1_graph_vertex_set Y TY \<A>1"
      unfolding top1_graph_vertex_set_def using hB_in_1 by (by100 blast)
    hence "?x \<in> ?V" by simp
    thus False using \<open>?x \<notin> ?V\<close> by (by100 blast)
  qed
  \<comment> \<open>A \\<subseteq> B via graph\\_arc\\_containment\\_via\\_open\\_interior (with \\<A>1\\<leftrightarrow>\\<A>2).\<close>
  have h\<A>1_coh_here: "\<forall>C. C \<subseteq> Y \<longrightarrow>
      (closedin_on Y TY C \<longleftrightarrow>
       (\<forall>D\<in>\<A>1. closedin_on D (subspace_topology Y TY D) (D \<inter> C)))"
    by (rule graph_coherent_any_decomposition[OF hgraph h\<A>1 h\<A>1_cover h\<A>1_inter hfin1])
  have hB_int_open: "B - ?ep B \<in> TY"
    by (rule graph_arc_interior_open[OF hstrict hhaus h\<A>1 h\<A>1_cover h\<A>1_inter h\<A>1_coh_here hB_in_1])
  have hA_sub_B: "A \<subseteq> B"
  proof -
    have h2_inter_ep: "\<forall>C\<in>\<A>2. \<forall>D\<in>\<A>2. C \<noteq> D \<longrightarrow> C \<inter> D \<subseteq> ?ep C"
      using h\<A>2_inter by (by100 blast)
    have h1_inter_ep: "\<forall>C\<in>\<A>1. \<forall>D\<in>\<A>1. C \<noteq> D \<longrightarrow> C \<inter> D \<subseteq> ?ep C"
      using h\<A>1_inter by (by100 blast)
    from graph_arc_containment_via_open_interior[OF hstrict hhaus hA_arc hA_sub
        hB_arc hB_sub hB_int_open hx_in_A hx_in_B hx_not_ep hx_not_epB
        hsame_V[symmetric] hA_in_2 hB_in_1 h2_inter_ep h1_inter_ep]
    show ?thesis .
  qed
  \<comment> \<open>B \\<subseteq> A via symmetric application.\<close>
  have "B \<subseteq> A"
  proof -
    have h\<A>2_coh_here: "\<forall>C. C \<subseteq> Y \<longrightarrow>
        (closedin_on Y TY C \<longleftrightarrow>
         (\<forall>D\<in>\<A>2. closedin_on D (subspace_topology Y TY D) (D \<inter> C)))"
      by (rule graph_coherent_any_decomposition[OF hgraph h\<A>2 h\<A>2_cover h\<A>2_inter hfin2])
    have hA_int_open: "A - ?ep A \<in> TY"
      by (rule graph_arc_interior_open[OF hstrict hhaus h\<A>2 h\<A>2_cover h\<A>2_inter h\<A>2_coh_here hA_in_2])
    have h1_inter_ep: "\<forall>C\<in>\<A>1. \<forall>D\<in>\<A>1. C \<noteq> D \<longrightarrow> C \<inter> D \<subseteq> ?ep C"
      using h\<A>1_inter by (by100 blast)
    have h2_inter_ep: "\<forall>C\<in>\<A>2. \<forall>D\<in>\<A>2. C \<noteq> D \<longrightarrow> C \<inter> D \<subseteq> ?ep C"
      using h\<A>2_inter by (by100 blast)
    from graph_arc_containment_via_open_interior[OF hstrict hhaus hB_arc hB_sub
        hA_arc hA_sub hA_int_open hx_in_B hx_in_A hx_not_epB hx_not_ep
        hsame_V hB_in_1 hA_in_2 h1_inter_ep h2_inter_ep]
    show ?thesis .
  qed
  have "A = B" using hA_sub_B \<open>B \<subseteq> A\<close> by (by100 blast)
  show "A \<in> \<A>1" using \<open>A = B\<close> hB_in_1 by simp
qed

\<comment> \<open>Iterated subdivision: refine a decomposition by adding finitely many new vertices.
   Each vertex that is not already a vertex of \\<A> must be interior to some arc.
   Subdividing at each such vertex preserves V - E (graph\\_subdivision\\_preserves\\_euler).
   The result has vertex set V(\\<A>) \\<union> P.\<close>
lemma graph_iterated_subdivision_exists:
  fixes Y :: "'a set" and TY :: "'a set set"
  assumes hstrict: "is_topology_on_strict Y TY"
      and hhaus: "is_hausdorff_on Y TY"
      and h\<A>: "\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
      and h\<A>_cover: "\<Union>\<A> = Y"
      and h\<A>_inter: "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and hfin: "finite \<A>"
      and hP: "finite P" "P \<subseteq> Y"
      and hP_int: "\<forall>p\<in>P. p \<notin> top1_graph_vertex_set Y TY \<A>"
  shows "\<exists>\<A>'. (\<forall>A\<in>\<A>'. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A))
      \<and> \<Union>\<A>' = Y
      \<and> (\<forall>A\<in>\<A>'. \<forall>B\<in>\<A>'. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2)
      \<and> top1_graph_vertex_set Y TY \<A>' = top1_graph_vertex_set Y TY \<A> \<union> P
      \<and> int (card (top1_graph_vertex_set Y TY \<A>')) - int (card \<A>')
          = int (card (top1_graph_vertex_set Y TY \<A>)) - int (card \<A>)
      \<and> finite \<A>'"
  using hP hP_int h\<A> h\<A>_cover h\<A>_inter hfin
proof (induction "card P" arbitrary: P \<A> rule: less_induct)
  case (less P \<A>)
  show ?case
  proof (cases "P = {}")
    case True
    show ?thesis
    proof (rule exI[of _ \<A>], intro conjI)
      show "\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)" using less.prems(4) .
      show "\<Union>\<A> = Y" using less.prems(5) .
      show "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" using less.prems(6) .
      show "top1_graph_vertex_set Y TY \<A> = top1_graph_vertex_set Y TY \<A> \<union> P"
        using True by (by100 simp)
      show "int (card (top1_graph_vertex_set Y TY \<A>)) - int (card \<A>)
          = int (card (top1_graph_vertex_set Y TY \<A>)) - int (card \<A>)" by simp
      show "finite \<A>" using less.prems(7) .
    qed
  next
    case False
    \<comment> \<open>Step: P \\<noteq> {}, pick p \\<in> P.\<close>
    then obtain p where "p \<in> P" by (by100 blast)
    let ?P' = "P - {p}"
    have hP'_card: "card ?P' < card P"
    proof -
      have "card (P - {p}) = card P - 1" using \<open>p \<in> P\<close> less.prems(1) by simp
      have "P \<noteq> {}" using \<open>p \<in> P\<close> by (by100 blast)
      have "card P > 0"
      proof -
        have "card P \<noteq> 0" using \<open>P \<noteq> {}\<close> less.prems(1) by (by100 auto)
        thus ?thesis by linarith
      qed
      thus ?thesis using \<open>card (P - {p}) = card P - 1\<close> by linarith
    qed
    have hP'_fin: "finite ?P'" using less.prems(1) by (by100 blast)
    have hP'_sub: "?P' \<subseteq> Y" using less.prems(2) by (by100 blast)
    \<comment> \<open>p is interior to some arc A0.\<close>
    have "p \<in> Y" using \<open>p \<in> P\<close> less.prems(2) by (by100 blast)
    have "p \<notin> top1_graph_vertex_set Y TY \<A>" using \<open>p \<in> P\<close> less.prems(3) by (by100 blast)
    have "p \<in> \<Union>\<A>" using \<open>p \<in> Y\<close> less.prems(5) by simp
    then obtain A0 where hA0: "A0 \<in> \<A>" "p \<in> A0" by (by100 blast)
    have hp_not_ep: "p \<notin> top1_arc_endpoints_on A0 (subspace_topology Y TY A0)"
    proof
      assume "p \<in> top1_arc_endpoints_on A0 (subspace_topology Y TY A0)"
      hence "p \<in> top1_graph_vertex_set Y TY \<A>"
        unfolding top1_graph_vertex_set_def using hA0(1) by (by100 blast)
      thus False using \<open>p \<notin> top1_graph_vertex_set Y TY \<A>\<close> by (by100 blast)
    qed
    \<comment> \<open>Split A0 at p and apply graph\\_subdivision\\_preserves\\_euler.\<close>
    \<comment> \<open>This gives a new decomposition \\<A>1 with V(\\<A>1) = V(\\<A>) \\<union> {p} and same V - E.\<close>
    \<comment> \<open>Then apply IH on \\<A>1 and P'.\<close>
    \<comment> \<open>Step 1: Get endpoints and split arc A0 at p.\<close>
    have hA0_sub: "A0 \<subseteq> Y" using less.prems(4) hA0(1) by (by100 blast)
    have hA0_arc: "top1_is_arc_on A0 (subspace_topology Y TY A0)" using less.prems(4) hA0(1) by (by100 blast)
    obtain hA0h where hhA0: "top1_homeomorphism_on I_set I_top A0 (subspace_topology Y TY A0) hA0h"
      using hA0_arc unfolding top1_is_arc_on_def by (by100 blast)
    have hA0_ep: "top1_arc_endpoints_on A0 (subspace_topology Y TY A0) = {hA0h 0, hA0h 1}"
      by (rule arc_endpoints_are_boundary[OF hstrict hhaus hA0_sub hA0_arc hhA0])
    have hA0h_ne: "hA0h 0 \<noteq> hA0h 1"
    proof
      assume "hA0h 0 = hA0h 1"
      have "inj_on hA0h I_set" using hhA0 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      from inj_onD[OF this \<open>hA0h 0 = hA0h 1\<close>] show False
        unfolding top1_unit_interval_def by (by100 auto)
    qed
    from arc_split_at_given_point[OF hstrict hhaus hA0_sub hA0_arc
        hA0(2) hp_not_ep hA0_ep hA0h_ne]
    obtain D1 D2 where hsplit: "A0 = D1 \<union> D2" "D1 \<inter> D2 = {p}"
        "top1_is_arc_on D1 (subspace_topology Y TY D1)"
        "top1_is_arc_on D2 (subspace_topology Y TY D2)"
        "hA0h 0 \<in> D1" "hA0h 1 \<in> D2" "p \<in> D1" "p \<in> D2" "D1 \<subseteq> Y" "D2 \<subseteq> Y"
      by (by5000 auto)
    have hep_D1: "top1_arc_endpoints_on D1 (subspace_topology Y TY D1) = {hA0h 0, p}"
      by (rule arc_split_endpoints(1)[OF hstrict hhaus hA0_sub hA0_arc
          hsplit(1) hsplit(2) hsplit(3) hsplit(4) hsplit(5) hsplit(6) hsplit(7) hsplit(8) hsplit(9)
          hsplit(10) hA0_ep hp_not_ep])
    have hep_D2: "top1_arc_endpoints_on D2 (subspace_topology Y TY D2) = {p, hA0h 1}"
      by (rule arc_split_endpoints(2)[OF hstrict hhaus hA0_sub hA0_arc
          hsplit(1) hsplit(2) hsplit(3) hsplit(4) hsplit(5) hsplit(6) hsplit(7) hsplit(8) hsplit(9)
          hsplit(10) hA0_ep hp_not_ep])
    \<comment> \<open>Step 2: Form new decomposition and apply graph\\_subdivision\\_preserves\\_euler.\<close>
    let ?\<A>1 = "(\<A> - {A0}) \<union> {D1, D2}"
    have heuler_step: "int (card (top1_graph_vertex_set Y TY ?\<A>1)) - int (card ?\<A>1)
        = int (card (top1_graph_vertex_set Y TY \<A>)) - int (card \<A>)"
      by (rule graph_subdivision_preserves_euler[OF hstrict hhaus less.prems(4) less.prems(6)
          less.prems(7) hA0(1) hA0(2) hp_not_ep hA0_ep hA0h_ne
          hsplit(1) hsplit(2) hsplit(3) hsplit(4) hep_D1 hep_D2 hsplit(9) hsplit(10)])
    \<comment> \<open>Step 3: V(\\<A>1) = V(\\<A>) \\<union> {p}.\<close>
    have hV_step: "top1_graph_vertex_set Y TY ?\<A>1 = top1_graph_vertex_set Y TY \<A> \<union> {p}"
    proof -
      let ?ep = "\<lambda>A. top1_arc_endpoints_on A (subspace_topology Y TY A)"
      have "top1_graph_vertex_set Y TY ?\<A>1 = (\<Union>A\<in>?\<A>1. ?ep A)"
        unfolding top1_graph_vertex_set_def by (by100 blast)
      also have "\<dots> = (\<Union>A\<in>(\<A> - {A0}). ?ep A) \<union> ?ep D1 \<union> ?ep D2"
        by (by100 blast)
      also have "\<dots> = (\<Union>A\<in>(\<A> - {A0}). ?ep A) \<union> {hA0h 0, p} \<union> {p, hA0h 1}"
        using hep_D1 hep_D2 by simp
      also have "\<dots> = (\<Union>A\<in>(\<A> - {A0}). ?ep A) \<union> {hA0h 0, hA0h 1, p}"
        by (by100 blast)
      also have "\<dots> = (\<Union>A\<in>(\<A> - {A0}). ?ep A) \<union> ?ep A0 \<union> {p}"
        using hA0_ep by (by100 blast)
      also have "\<dots> = top1_graph_vertex_set Y TY \<A> \<union> {p}"
        unfolding top1_graph_vertex_set_def using hA0(1) by (by100 blast)
      finally show ?thesis .
    qed
    \<comment> \<open>Step 4: \\<A>1 satisfies graph conditions.\<close>
    have h\<A>1_arcs: "\<forall>A\<in>?\<A>1. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
    proof (intro ballI conjI)
      fix A assume "A \<in> ?\<A>1"
      hence "A \<in> \<A> - {A0} \<or> A = D1 \<or> A = D2" by (by100 blast)
      thus "A \<subseteq> Y" using less.prems(4) hsplit(9) hsplit(10) by (by100 blast)
      show "top1_is_arc_on A (subspace_topology Y TY A)"
        using \<open>A \<in> ?\<A>1\<close> less.prems(4) hsplit(3) hsplit(4) by (by100 blast)
    qed
    have h\<A>1_cover: "\<Union>?\<A>1 = Y"
    proof -
      have "\<Union>(\<A> - {A0}) \<union> D1 \<union> D2 = \<Union>\<A>"
        using hsplit(1) hA0(1) by (by100 blast)
      moreover have "\<Union>?\<A>1 = \<Union>(\<A> - {A0}) \<union> D1 \<union> D2" by (by100 blast)
      ultimately show ?thesis using less.prems(5) by simp
    qed
    have h\<A>1_inter: "\<forall>A\<in>?\<A>1. \<forall>B\<in>?\<A>1. A \<noteq> B \<longrightarrow>
         A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
       \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
       \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
    proof (intro ballI impI)
      fix A B assume hAi: "A \<in> ?\<A>1" and hBi: "B \<in> ?\<A>1" and hne: "A \<noteq> B"
      let ?ep = "\<lambda>C. top1_arc_endpoints_on C (subspace_topology Y TY C)"
      \<comment> \<open>Case analysis: each of A, B is either in \\<A> - {A0}, or = D1, or = D2.\<close>
      show "A \<inter> B \<subseteq> ?ep A \<and> A \<inter> B \<subseteq> ?ep B \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      proof (cases "A \<in> \<A> - {A0}")
        case hA_old: True
        show ?thesis
        proof (cases "B \<in> \<A> - {A0}")
          case True \<comment> \<open>Both old arcs.\<close>
          have "A \<in> \<A>" "B \<in> \<A>" using hA_old True by (by100 blast)+
          from less.prems(6)[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> hne]
          show ?thesis .
        next
          case False \<comment> \<open>A old, B = D1 or D2.\<close>
          hence "B = D1 \<or> B = D2" using hBi by (by100 blast)
          have "A \<in> \<A>" "A \<noteq> A0" using hA_old by (by100 blast)+
          have hA_A0: "A \<inter> A0 \<subseteq> ?ep A \<and> A \<inter> A0 \<subseteq> ?ep A0 \<and> finite (A \<inter> A0) \<and> card (A \<inter> A0) \<le> 2"
            using less.prems(6)[rule_format, OF \<open>A \<in> \<A>\<close> hA0(1) \<open>A \<noteq> A0\<close>] .
          \<comment> \<open>A \\<inter> B \\<subseteq> A \\<inter> A0 (since B \\<subseteq> A0 = D1 \\<union> D2).\<close>
          have "B \<subseteq> A0" using \<open>B = D1 \<or> B = D2\<close> hsplit(1) by (by100 blast)
          hence "A \<inter> B \<subseteq> A \<inter> A0" by (by100 blast)
          have hAB_sub_epA: "A \<inter> B \<subseteq> ?ep A" using \<open>A \<inter> B \<subseteq> A \<inter> A0\<close> hA_A0 by (by100 blast)
          have hAB_fin: "finite (A \<inter> B)"
            using finite_subset[OF \<open>A \<inter> B \<subseteq> A \<inter> A0\<close>] hA_A0 by (by100 blast)
          have hAB_card: "card (A \<inter> B) \<le> 2"
          proof -
            from card_mono[OF _ \<open>A \<inter> B \<subseteq> A \<inter> A0\<close>] hA_A0
            have "card (A \<inter> B) \<le> card (A \<inter> A0)" by (by100 blast)
            thus ?thesis using hA_A0 by linarith
          qed
          have hAB_sub_epB: "A \<inter> B \<subseteq> ?ep B"
          proof -
            \<comment> \<open>A \\<inter> B \\<subseteq> A \\<inter> A0 \\<subseteq> ep(A0). Points of ep(A0) in D1 are ep(D1) (endpoints of A0 are
               endpoints of sub-arcs). Points of ep(A0) in D2 are ep(D2).\<close>
            have hAB_ep_A0: "A \<inter> B \<subseteq> ?ep A0"
            proof -
              have "A \<inter> A0 \<subseteq> ?ep A0" using hA_A0 by (by100 blast)
              thus ?thesis using \<open>A \<inter> B \<subseteq> A \<inter> A0\<close> by (by100 blast)
            qed
            \<comment> \<open>ep(A0) = {hA0h 0, hA0h 1}. hA0h 0 \\<in> D1, hA0h 1 \\<in> D2.
               If B = D1: A \\<inter> D1 \\<subseteq> ep(A0) \\<inter> D1 = {hA0h 0, p} \\<inter> ... = {hA0h 0} (since p \\<notin> ep(A0)).
               Actually ep(A0) \\<inter> D1 \\<subseteq> ep(D1) = {hA0h 0, p}.\<close>
            \<comment> \<open>A \\<inter> B \\<subseteq> ep(A0) \\<inter> B. ep(A0) = {hA0h 0, hA0h 1}.
               If B = D1: hA0h 1 \\<notin> D1 (hA0h 1 \\<in> D2, D1 \\<inter> D2 = {p}, hA0h 1 \\<noteq> p).
               So ep(A0) \\<inter> D1 = {hA0h 0} \\<subseteq> ep(D1). Similarly for D2.\<close>
            have "hA0h 0 \<notin> D2 \<or> hA0h 0 = p"
            proof (cases "hA0h 0 \<in> D2")
              case True
              hence "hA0h 0 \<in> D1 \<inter> D2" using hsplit(5) by (by100 blast)
              hence "hA0h 0 = p" using hsplit(2) by (by100 blast)
              thus ?thesis by simp
            qed simp
            have "hA0h 1 \<notin> D1 \<or> hA0h 1 = p"
            proof (cases "hA0h 1 \<in> D1")
              case True
              hence "hA0h 1 \<in> D1 \<inter> D2" using hsplit(6) by (by100 blast)
              hence "hA0h 1 = p" using hsplit(2) by (by100 blast)
              thus ?thesis by simp
            qed simp
            have hp_ne_0: "p \<noteq> hA0h 0" using hp_not_ep hA0_ep by (by100 blast)
            have hp_ne_1: "p \<noteq> hA0h 1" using hp_not_ep hA0_ep by (by100 blast)
            have "hA0h 1 \<notin> D1" using \<open>hA0h 1 \<notin> D1 \<or> hA0h 1 = p\<close> hp_ne_1 by (by100 blast)
            have "hA0h 0 \<notin> D2" using \<open>hA0h 0 \<notin> D2 \<or> hA0h 0 = p\<close> hp_ne_0 by (by100 blast)
            show "A \<inter> B \<subseteq> ?ep B"
            proof -
              from \<open>B = D1 \<or> B = D2\<close> show ?thesis
              proof
                assume "B = D1"
                have "?ep A0 \<inter> D1 \<subseteq> {hA0h 0}"
                  using hA0_ep \<open>hA0h 1 \<notin> D1\<close> by (by100 blast)
                hence "A \<inter> B \<subseteq> {hA0h 0}" using hAB_ep_A0 \<open>B = D1\<close> by (by100 blast)
                thus ?thesis using hep_D1 \<open>B = D1\<close> by (by100 blast)
              next
                assume "B = D2"
                have "?ep A0 \<inter> D2 \<subseteq> {hA0h 1}"
                proof -
                  have "?ep A0 = {hA0h 0, hA0h 1}" using hA0_ep .
                  thus ?thesis using \<open>hA0h 0 \<notin> D2\<close> by (by100 auto)
                qed
                hence "A \<inter> B \<subseteq> {hA0h 1}" using hAB_ep_A0 \<open>B = D2\<close> by (by100 blast)
                thus ?thesis using hep_D2 \<open>B = D2\<close> by (by100 blast)
              qed
            qed
          qed
          show ?thesis using hAB_sub_epA hAB_sub_epB hAB_fin hAB_card by (by100 blast)
        qed
      next
        case hA_new: False
        hence "A = D1 \<or> A = D2" using hAi by (by100 blast)
        show ?thesis
        proof (cases "B \<in> \<A> - {A0}")
          case True \<comment> \<open>A = D1 or D2, B old: symmetric to above.\<close>
          \<comment> \<open>Symmetric: A = D1 or D2, B old.\<close>
          have "B \<in> \<A>" "B \<noteq> A0" using True by (by100 blast)+
          have hB_A0: "B \<inter> A0 \<subseteq> ?ep B \<and> B \<inter> A0 \<subseteq> ?ep A0 \<and> finite (B \<inter> A0) \<and> card (B \<inter> A0) \<le> 2"
            using less.prems(6)[rule_format, OF \<open>B \<in> \<A>\<close> hA0(1) \<open>B \<noteq> A0\<close>] .
          have "A \<subseteq> A0" using \<open>A = D1 \<or> A = D2\<close> hsplit(1) by (by100 blast)
          hence "A \<inter> B \<subseteq> A0 \<inter> B" by (by100 blast)
          have hAB_sub_epB: "A \<inter> B \<subseteq> ?ep B"
          proof -
            have "A0 \<inter> B \<subseteq> ?ep B" using hB_A0 by (by100 blast)
            thus ?thesis using \<open>A \<inter> B \<subseteq> A0 \<inter> B\<close> by (by100 blast)
          qed
          have hAB_fin: "finite (A \<inter> B)"
          proof -
            have "finite (B \<inter> A0)" using hB_A0 by (by100 blast)
            hence "finite (A0 \<inter> B)" by (simp add: Int_commute)
            from finite_subset[OF \<open>A \<inter> B \<subseteq> A0 \<inter> B\<close> this] show ?thesis .
          qed
          have hAB_card: "card (A \<inter> B) \<le> 2"
          proof -
            have "finite (B \<inter> A0)" using hB_A0 by (by100 blast)
            hence "finite (A0 \<inter> B)" by (simp add: Int_commute)
            from card_mono[OF this \<open>A \<inter> B \<subseteq> A0 \<inter> B\<close>]
            have "card (A \<inter> B) \<le> card (A0 \<inter> B)" .
            have "card (B \<inter> A0) \<le> 2" using hB_A0 by (by100 blast)
            hence "card (A0 \<inter> B) \<le> 2" by (simp add: Int_commute)
            thus ?thesis using \<open>card (A \<inter> B) \<le> card (A0 \<inter> B)\<close> by linarith
          qed
          \<comment> \<open>A \\<inter> B \\<subseteq> ep(A): same argument as the forward case for ep(B).\<close>
          have hAB_ep_A0': "A \<inter> B \<subseteq> ?ep A0"
          proof -
            have "B \<inter> A0 \<subseteq> ?ep A0" using hB_A0 by (by100 blast)
            hence "A0 \<inter> B \<subseteq> ?ep A0" by (by100 blast)
            thus ?thesis using \<open>A \<inter> B \<subseteq> A0 \<inter> B\<close> by (by100 blast)
          qed
          have hp_ne_0: "p \<noteq> hA0h 0" using hp_not_ep hA0_ep by (by100 blast)
          have hp_ne_1: "p \<noteq> hA0h 1" using hp_not_ep hA0_ep by (by100 blast)
          have "hA0h 1 \<notin> D1"
          proof (cases "hA0h 1 \<in> D1")
            case True hence "hA0h 1 \<in> D1 \<inter> D2" using hsplit(6) by (by100 blast)
            hence "hA0h 1 = p" using hsplit(2) by (by100 blast)
            thus ?thesis using hp_ne_1 by (by100 blast)
          qed simp
          have "hA0h 0 \<notin> D2"
          proof (cases "hA0h 0 \<in> D2")
            case True hence "hA0h 0 \<in> D1 \<inter> D2" using hsplit(5) by (by100 blast)
            hence "hA0h 0 = p" using hsplit(2) by (by100 blast)
            thus ?thesis using hp_ne_0 by (by100 blast)
          qed simp
          have hAB_sub_epA: "A \<inter> B \<subseteq> ?ep A"
          proof -
            from \<open>A = D1 \<or> A = D2\<close> show ?thesis
            proof
              assume "A = D1"
              have "?ep A0 \<inter> D1 \<subseteq> {hA0h 0}"
              proof -
                have "?ep A0 = {hA0h 0, hA0h 1}" using hA0_ep .
                thus ?thesis using \<open>hA0h 1 \<notin> D1\<close> by (by100 auto)
              qed
              hence "A \<inter> B \<subseteq> {hA0h 0}" using hAB_ep_A0' \<open>A = D1\<close> by (by100 blast)
              thus ?thesis using hep_D1 \<open>A = D1\<close> by (by100 blast)
            next
              assume "A = D2"
              have "?ep A0 \<inter> D2 \<subseteq> {hA0h 1}"
              proof -
                have "?ep A0 = {hA0h 0, hA0h 1}" using hA0_ep .
                thus ?thesis using \<open>hA0h 0 \<notin> D2\<close> by (by100 auto)
              qed
              hence "A \<inter> B \<subseteq> {hA0h 1}" using hAB_ep_A0' \<open>A = D2\<close> by (by100 blast)
              thus ?thesis using hep_D2 \<open>A = D2\<close> by (by100 blast)
            qed
          qed
          show ?thesis using hAB_sub_epA hAB_sub_epB hAB_fin hAB_card by (by100 blast)
        next
          case False \<comment> \<open>Both A, B are D1 or D2.\<close>
          hence "B = D1 \<or> B = D2" using hBi by (by100 blast)
          \<comment> \<open>Since A \\<noteq> B and both are D1 or D2: {A, B} = {D1, D2}.\<close>
          have "{A, B} = {D1, D2}" using \<open>A = D1 \<or> A = D2\<close> \<open>B = D1 \<or> B = D2\<close> hne by (by100 blast)
          \<comment> \<open>D1 \\<inter> D2 = {p}. {p} \\<subseteq> ep(D1) and {p} \\<subseteq> ep(D2). finite, card = 1 \\<le> 2.\<close>
          have "A \<inter> B = {p}"
            using \<open>A = D1 \<or> A = D2\<close> \<open>B = D1 \<or> B = D2\<close> hne hsplit(2)
            by (by100 auto)
          have "{p} \<subseteq> ?ep A" using \<open>A = D1 \<or> A = D2\<close> hep_D1 hep_D2 by (by100 blast)
          have "{p} \<subseteq> ?ep B" using \<open>B = D1 \<or> B = D2\<close> hep_D1 hep_D2 by (by100 blast)
          show ?thesis using \<open>A \<inter> B = {p}\<close> \<open>{p} \<subseteq> ?ep A\<close> \<open>{p} \<subseteq> ?ep B\<close> by (by100 simp)
        qed
      qed
    qed
    have h\<A>1_fin: "finite ?\<A>1" using less.prems(7) by (by100 blast)
    \<comment> \<open>Step 5: P' interior to \\<A>1.\<close>
    have hP'_int: "\<forall>q\<in>?P'. q \<notin> top1_graph_vertex_set Y TY ?\<A>1"
    proof (intro ballI)
      fix q assume "q \<in> ?P'"
      hence "q \<in> P" "q \<noteq> p" by (by100 blast)+
      hence "q \<notin> top1_graph_vertex_set Y TY \<A>" using less.prems(3) by (by100 blast)
      have "q \<notin> top1_graph_vertex_set Y TY \<A> \<union> {p}"
        using \<open>q \<notin> top1_graph_vertex_set Y TY \<A>\<close> \<open>q \<noteq> p\<close> by (by100 blast)
      thus "q \<notin> top1_graph_vertex_set Y TY ?\<A>1" using hV_step by simp
    qed
    \<comment> \<open>Step 6: Apply IH.\<close>
    from less.hyps[OF hP'_card hP'_fin hP'_sub hP'_int h\<A>1_arcs h\<A>1_cover h\<A>1_inter h\<A>1_fin]
    obtain \<A>' where h\<A>':
        "(\<forall>A\<in>\<A>'. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A))
        \<and> \<Union>\<A>' = Y
        \<and> (\<forall>A\<in>\<A>'. \<forall>B\<in>\<A>'. A \<noteq> B \<longrightarrow>
             A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
           \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
           \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2)
        \<and> top1_graph_vertex_set Y TY \<A>' = top1_graph_vertex_set Y TY ?\<A>1 \<union> ?P'
        \<and> int (card (top1_graph_vertex_set Y TY \<A>')) - int (card \<A>')
            = int (card (top1_graph_vertex_set Y TY ?\<A>1)) - int (card ?\<A>1)
        \<and> finite \<A>'"
      by (by5000 auto)
    \<comment> \<open>Step 7: Chain vertex sets and Euler.\<close>
    have hV_chain: "top1_graph_vertex_set Y TY \<A>' = top1_graph_vertex_set Y TY \<A> \<union> P"
    proof -
      have "top1_graph_vertex_set Y TY \<A>' = top1_graph_vertex_set Y TY ?\<A>1 \<union> ?P'"
        using h\<A>' by (by100 blast)
      also have "\<dots> = (top1_graph_vertex_set Y TY \<A> \<union> {p}) \<union> (P - {p})"
        using hV_step by simp
      also have "\<dots> = top1_graph_vertex_set Y TY \<A> \<union> P"
        using \<open>p \<in> P\<close> by (by100 blast)
      finally show ?thesis .
    qed
    have hE_chain: "int (card (top1_graph_vertex_set Y TY \<A>')) - int (card \<A>')
        = int (card (top1_graph_vertex_set Y TY \<A>)) - int (card \<A>)"
      using h\<A>' heuler_step by linarith
    have hf1: "\<forall>A\<in>\<A>'. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
      using conjunct1[OF h\<A>'] .
    have hf2: "\<Union>\<A>' = Y" using conjunct1[OF conjunct2[OF h\<A>']] .
    have hf3: "\<forall>A\<in>\<A>'. \<forall>B\<in>\<A>'. A \<noteq> B \<longrightarrow>
         A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
       \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
       \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      using conjunct1[OF conjunct2[OF conjunct2[OF h\<A>']]] .
    have hf6: "finite \<A>'"
      using conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF h\<A>']]]]] .
    show ?thesis
      apply (rule exI[of _ \<A>'])
      using hf1 hf2 hf3 hV_chain hE_chain hf6
      apply (intro conjI)
      apply (by100 blast)+
      done
  qed
qed

\<comment> \<open>Euler invariance: V - E is the same for any two finite arc decompositions of a graph.
   Proof idea: common refinement via arc subdivision. Each subdivision adds 1 vertex and 1 arc,
   preserving V - E. Both decompositions refine to the same common refinement.\<close>
lemma graph_euler_invariance:
  fixes Y :: "'a set" and TY :: "'a set set"
  assumes hgraph: "top1_is_graph_on Y TY"
      and h\<A>1: "\<forall>A\<in>\<A>1. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
      and h\<A>1_cover: "\<Union>\<A>1 = Y"
      and h\<A>1_inter: "\<forall>A\<in>\<A>1. \<forall>B\<in>\<A>1. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and hfin1: "finite \<A>1"
      and h\<A>2: "\<forall>A\<in>\<A>2. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
      and h\<A>2_cover: "\<Union>\<A>2 = Y"
      and h\<A>2_inter: "\<forall>A\<in>\<A>2. \<forall>B\<in>\<A>2. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and hfin2: "finite \<A>2"
  shows "int (card (top1_graph_vertex_set Y TY \<A>1)) - int (card \<A>1)
       = int (card (top1_graph_vertex_set Y TY \<A>2)) - int (card \<A>2)"
proof -
  let ?V1 = "top1_graph_vertex_set Y TY \<A>1"
  let ?V2 = "top1_graph_vertex_set Y TY \<A>2"
  have hstrict: "is_topology_on_strict Y TY"
    using hgraph unfolding top1_is_graph_on_def by (by100 blast)
  have hhaus: "is_hausdorff_on Y TY"
    using hgraph unfolding top1_is_graph_on_def by (by100 blast)
  \<comment> \<open>Step 1: Refine \\<A>1 at V2 \\ V1 to get \\<A>1' with vertices V1 \\<union> V2.
     By induction on |V2 \\ V1|, each subdivision preserves V - E.\<close>
  \<comment> \<open>Step 1a: Iterated subdivision of \\<A>1. Each vertex of V2 \\ V1 lies in the interior
     of some arc of \\<A>1 (because V2 \\<subseteq> Y = \\<Union>\\<A>1 and V2 \\ V1 not endpoints).\<close>
  obtain \<A>1' where h\<A>1': "\<forall>A\<in>\<A>1'. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
      and h\<A>1'_cover: "\<Union>\<A>1' = Y"
      and h\<A>1'_inter: "\<forall>A\<in>\<A>1'. \<forall>B\<in>\<A>1'. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and h\<A>1'_V: "top1_graph_vertex_set Y TY \<A>1' = ?V1 \<union> ?V2"
      and h\<A>1'_euler: "int (card (top1_graph_vertex_set Y TY \<A>1')) - int (card \<A>1')
          = int (card ?V1) - int (card \<A>1)"
      and h\<A>1'_fin: "finite \<A>1'"
  proof -
    \<comment> \<open>V2 finite.\<close>
    have hV2_fin: "finite ?V2"
    proof -
      have "\<forall>A\<in>\<A>2. finite (top1_arc_endpoints_on A (subspace_topology Y TY A))"
      proof (intro ballI)
        fix A assume "A \<in> \<A>2"
        have "A \<subseteq> Y" "top1_is_arc_on A (subspace_topology Y TY A)" using h\<A>2 \<open>A \<in> \<A>2\<close> by (by100 blast)+
        obtain h where "top1_homeomorphism_on I_set I_top A (subspace_topology Y TY A) h"
          using \<open>top1_is_arc_on A _\<close> unfolding top1_is_arc_on_def by (by100 blast)
        from arc_endpoints_are_boundary[OF hstrict hhaus \<open>A \<subseteq> Y\<close> \<open>top1_is_arc_on A _\<close> this]
        show "finite (top1_arc_endpoints_on A (subspace_topology Y TY A))" by (by100 simp)
      qed
      thus ?thesis unfolding top1_graph_vertex_set_def using hfin2 by (by100 blast)
    qed
    have hP_fin: "finite (?V2 - ?V1)" using hV2_fin by (by100 blast)
    have hP_sub: "?V2 - ?V1 \<subseteq> Y"
    proof -
      have "?V2 \<subseteq> Y"
      proof -
        have "\<forall>A\<in>\<A>2. top1_arc_endpoints_on A (subspace_topology Y TY A) \<subseteq> A"
          unfolding top1_arc_endpoints_on_def by (by100 blast)
        hence "\<forall>A\<in>\<A>2. top1_arc_endpoints_on A (subspace_topology Y TY A) \<subseteq> Y"
          using h\<A>2 by (by100 blast)
        thus ?thesis unfolding top1_graph_vertex_set_def by (by100 blast)
      qed
      thus ?thesis by (by100 blast)
    qed
    have hP_int: "\<forall>p\<in>?V2 - ?V1. p \<notin> ?V1" by (by100 blast)
    from graph_iterated_subdivision_exists[OF hstrict hhaus h\<A>1 h\<A>1_cover h\<A>1_inter hfin1
        hP_fin hP_sub hP_int]
    obtain \<A>1'x where hx: "(\<forall>A\<in>\<A>1'x. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A))
        \<and> \<Union>\<A>1'x = Y
        \<and> (\<forall>A\<in>\<A>1'x. \<forall>B\<in>\<A>1'x. A \<noteq> B \<longrightarrow>
             A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
           \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
           \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2)
        \<and> top1_graph_vertex_set Y TY \<A>1'x = ?V1 \<union> (?V2 - ?V1)
        \<and> int (card (top1_graph_vertex_set Y TY \<A>1'x)) - int (card \<A>1'x)
            = int (card ?V1) - int (card \<A>1)
        \<and> finite \<A>1'x" by (by5000 auto)
    \<comment> \<open>V1 \\<union> (V2 \\ V1) = V1 \\<union> V2.\<close>
    note hc1 = conjunct1[OF hx]
    note hc2 = conjunct1[OF conjunct2[OF hx]]
    note hc3 = conjunct1[OF conjunct2[OF conjunct2[OF hx]]]
    note hc4 = conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF hx]]]]
    note hc5 = conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF hx]]]]]
    note hc6 = conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF hx]]]]]
    have hc4': "top1_graph_vertex_set Y TY \<A>1'x = ?V1 \<union> ?V2"
    proof -
      define V1a where "V1a = ?V1"
      define V2a where "V2a = ?V2"
      have "V1a \<union> (V2a - V1a) = V1a \<union> V2a" by blast
      moreover have "top1_graph_vertex_set Y TY \<A>1'x = V1a \<union> (V2a - V1a)"
        using hc4 unfolding V1a_def V2a_def .
      ultimately have "top1_graph_vertex_set Y TY \<A>1'x = V1a \<union> V2a" by simp
      thus ?thesis unfolding V1a_def V2a_def .
    qed
    from that[OF hc1 hc2 hc3 hc4' hc5 hc6] show ?thesis .
  qed
  \<comment> \<open>Step 2: Similarly refine \\<A>2.\<close>
  obtain \<A>2' where h\<A>2': "\<forall>A\<in>\<A>2'. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
      and h\<A>2'_cover: "\<Union>\<A>2' = Y"
      and h\<A>2'_inter: "\<forall>A\<in>\<A>2'. \<forall>B\<in>\<A>2'. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and h\<A>2'_V: "top1_graph_vertex_set Y TY \<A>2' = ?V1 \<union> ?V2"
      and h\<A>2'_euler: "int (card (top1_graph_vertex_set Y TY \<A>2')) - int (card \<A>2')
          = int (card ?V2) - int (card \<A>2)"
      and h\<A>2'_fin: "finite \<A>2'"
  proof -
    \<comment> \<open>V1 finite (same argument as V2 above).\<close>
    have hV1_fin: "finite ?V1"
    proof -
      have "\<forall>A\<in>\<A>1. finite (top1_arc_endpoints_on A (subspace_topology Y TY A))"
      proof (intro ballI)
        fix A assume "A \<in> \<A>1"
        have "A \<subseteq> Y" "top1_is_arc_on A (subspace_topology Y TY A)" using h\<A>1 \<open>A \<in> \<A>1\<close> by (by100 blast)+
        obtain h where "top1_homeomorphism_on I_set I_top A (subspace_topology Y TY A) h"
          using \<open>top1_is_arc_on A _\<close> unfolding top1_is_arc_on_def by (by100 blast)
        from arc_endpoints_are_boundary[OF hstrict hhaus \<open>A \<subseteq> Y\<close> \<open>top1_is_arc_on A _\<close> this]
        show "finite (top1_arc_endpoints_on A (subspace_topology Y TY A))" by (by100 simp)
      qed
      thus ?thesis unfolding top1_graph_vertex_set_def using hfin1 by (by100 blast)
    qed
    have hP_fin: "finite (?V1 - ?V2)" using hV1_fin by (by100 blast)
    have hP_sub: "?V1 - ?V2 \<subseteq> Y"
    proof -
      have "?V1 \<subseteq> Y"
      proof -
        have "\<forall>A\<in>\<A>1. top1_arc_endpoints_on A (subspace_topology Y TY A) \<subseteq> A"
          unfolding top1_arc_endpoints_on_def by (by100 blast)
        hence "\<forall>A\<in>\<A>1. top1_arc_endpoints_on A (subspace_topology Y TY A) \<subseteq> Y"
          using h\<A>1 by (by100 blast)
        thus ?thesis unfolding top1_graph_vertex_set_def by (by100 blast)
      qed
      thus ?thesis by (by100 blast)
    qed
    have hP_int: "\<forall>p\<in>?V1 - ?V2. p \<notin> ?V2" by (by100 blast)
    from graph_iterated_subdivision_exists[OF hstrict hhaus h\<A>2 h\<A>2_cover h\<A>2_inter hfin2
        hP_fin hP_sub hP_int]
    obtain \<A>2'x where hx: "(\<forall>A\<in>\<A>2'x. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A))
        \<and> \<Union>\<A>2'x = Y
        \<and> (\<forall>A\<in>\<A>2'x. \<forall>B\<in>\<A>2'x. A \<noteq> B \<longrightarrow>
             A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
           \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
           \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2)
        \<and> top1_graph_vertex_set Y TY \<A>2'x = ?V2 \<union> (?V1 - ?V2)
        \<and> int (card (top1_graph_vertex_set Y TY \<A>2'x)) - int (card \<A>2'x)
            = int (card ?V2) - int (card \<A>2)
        \<and> finite \<A>2'x" by (by5000 auto)
    note hc1 = conjunct1[OF hx]
    note hc2 = conjunct1[OF conjunct2[OF hx]]
    note hc3 = conjunct1[OF conjunct2[OF conjunct2[OF hx]]]
    note hc4 = conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF hx]]]]
    note hc5 = conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF hx]]]]]
    note hc6 = conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF hx]]]]]
    have hc4': "top1_graph_vertex_set Y TY \<A>2'x = ?V1 \<union> ?V2"
    proof -
      define V1a where "V1a = ?V1"
      define V2a where "V2a = ?V2"
      have "V2a \<union> (V1a - V2a) = V1a \<union> V2a" by blast
      moreover have "top1_graph_vertex_set Y TY \<A>2'x = V2a \<union> (V1a - V2a)"
        using hc4 unfolding V1a_def V2a_def .
      ultimately have "top1_graph_vertex_set Y TY \<A>2'x = V1a \<union> V2a" by simp
      thus ?thesis unfolding V1a_def V2a_def .
    qed
    from that[OF hc1 hc2 hc3 hc4' hc5 hc6] show ?thesis .
  qed
  \<comment> \<open>Step 3: Both refinements have the same vertex set, so same arcs.\<close>
  have h\<A>_eq: "\<A>1' = \<A>2'"
    by (rule graph_same_vertices_same_arcs[OF hgraph h\<A>1' h\<A>1'_cover h\<A>1'_inter h\<A>1'_fin
        h\<A>2' h\<A>2'_cover h\<A>2'_inter h\<A>2'_fin])
       (simp add: h\<A>1'_V h\<A>2'_V)
  \<comment> \<open>Step 4: Chain the equalities.\<close>
  have "int (card ?V1) - int (card \<A>1) = int (card (top1_graph_vertex_set Y TY \<A>1')) - int (card \<A>1')"
    using h\<A>1'_euler by linarith
  also have "\<dots> = int (card (top1_graph_vertex_set Y TY \<A>2')) - int (card \<A>2')"
    using h\<A>_eq by simp
  also have "\<dots> = int (card ?V2) - int (card \<A>2)"
    using h\<A>2'_euler by linarith
  finally show ?thesis .
qed


\<comment> \<open>Attached-arc retract: if C is path-connected, A is an arc meeting C,
   then C \\<union> A retracts onto C.
   Card 1 (A \\<inter> C = {v}): collapse A to v.
   Card 2 (A \\<inter> C = {u,v}): map A along a path in C from u to v.\<close>
lemma retract_attached_arc:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes htop: "is_topology_on X TX"
      and hstrict: "is_topology_on_strict X TX"
      and hhaus: "is_hausdorff_on X TX"
      and hC_sub: "C \<subseteq> X" and hA_sub: "A \<subseteq> X"
      and hC_pc: "top1_path_connected_on C (subspace_topology X TX C)"
      and hA_arc: "top1_is_arc_on A (subspace_topology X TX A)"
      and hmeet: "A \<inter> C \<noteq> {}"
      and hinter_ep: "A \<inter> C \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
      and hC_closed: "closedin_on X TX C"
  shows "top1_retract_of_on (C \<union> A) (subspace_topology X TX (C \<union> A)) C"
proof -
  let ?CuA = "C \<union> A"
  let ?TCuA = "subspace_topology X TX ?CuA"
  let ?TC = "subspace_topology X TX C"
  let ?CuA = "C \<union> A"
  \<comment> \<open>A is closed in X (compact arc in Hausdorff).\<close>
  have hA_compact: "top1_compact_on A (subspace_topology X TX A)"
    using arc_compact[OF hA_arc] .
  have hA_closed: "closedin_on X TX A"
    by (rule Theorem_26_3[OF hhaus hA_sub hA_compact])
  \<comment> \<open>Both C and A are closed in C \\<union> A (closed in X \\<Rightarrow> closed in subspace).\<close>
  have hCuA_sub: "?CuA \<subseteq> X" using hC_sub hA_sub by (by100 blast)
  \<comment> \<open>From A \\<inter> C \\<subseteq> ep(A), get the intersection structure.\<close>
  from hmeet obtain v where hv: "v \<in> A" "v \<in> C" by (by100 blast)
  \<comment> \<open>Get arc homeomorphism and endpoints.\<close>
  obtain h where hh: "top1_homeomorphism_on I_set I_top A (subspace_topology X TX A) h"
    using hA_arc unfolding top1_is_arc_on_def by (by100 blast)
  have hep: "top1_arc_endpoints_on A (subspace_topology X TX A) = {h 0, h 1}"
    by (rule arc_endpoints_are_boundary[OF hstrict hhaus hA_sub hA_arc hh])
  \<comment> \<open>A \\<inter> C \\<subseteq> {h 0, h 1}.\<close>
  have hAC_sub_h: "A \<inter> C \<subseteq> {h 0, h 1}" using hinter_ep hep by (by100 blast)
  \<comment> \<open>Case split: card(A \\<inter> C) = 1 or 2.\<close>
  \<comment> \<open>Get a path \\<gamma> in C connecting any two points of A \\<inter> C.
     For card 1: \\<gamma> is trivial (constant). For card 2: \\<gamma> is a path from u to v.
     In both cases, define r(x) = x on C, r(x) = \\<gamma>(h\\<inverse>(x)) on A.
     This maps A onto a path in C while fixing C.\<close>
  \<comment> \<open>h 0 and h 1 are the endpoints of A. A \\<inter> C \\<subseteq> {h 0, h 1}.\<close>
  have hh0_A: "h 0 \<in> A" and hh1_A: "h 1 \<in> A"
  proof -
    have "bij_betw h I_set A" using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    hence "h ` I_set = A" unfolding bij_betw_def by (by100 blast)
    have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    show "h 0 \<in> A" using \<open>h ` I_set = A\<close> \<open>0 \<in> I_set\<close> by (by100 blast)
    show "h 1 \<in> A" using \<open>h ` I_set = A\<close> \<open>1 \<in> I_set\<close> by (by100 blast)
  qed
  \<comment> \<open>v \\<in> A \\<inter> C, so v \\<in> {h 0, h 1}.\<close>
  have "v \<in> {h 0, h 1}" using hv hAC_sub_h by (by100 blast)
  \<comment> \<open>Since C is pc and v \\<in> C, there's a path from v to any other point in A \\<inter> C.
     For card 2: both h 0 and h 1 are in C, so there's a path h0 \\<to> h1 in C.\<close>
  \<comment> \<open>Define retraction: r(x) = x for x \\<in> C, r(x) = v for x \\<in> A \\ C.\<close>
  \<comment> \<open>This works for BOTH cases because:
     - Card 1: A \\<inter> C = {v}, so on A \\<inter> C: id(v) = v = const(v). Agreement. \\<checkmark>
     - Card 2: A \\<inter> C = {u,v}. We need r(u) = u and r(v) = v from the A side.
       Constant map r|A = v fails at u (r(u) = v \\<noteq> u).
       So card 2 needs the PATH MAP approach, not constant.\<close>
  \<comment> \<open>For simplicity, handle card 1 first. Card 2 needs more work.\<close>
  show ?thesis
  proof (cases "A \<inter> C = {v}")
    case True
    \<comment> \<open>Card 1: A meets C at exactly v. Collapse A to v.\<close>
    define r where "r x = (if x \<in> C then x else v)" for x
    show ?thesis unfolding top1_retract_of_on_def top1_is_retraction_on_def
    proof (intro exI[of _ r] conjI)
      show "C \<subseteq> ?CuA" by (by100 blast)
      show "\<forall>a \<in> C. r a = a" unfolding r_def by (by100 simp)
      \<comment> \<open>Simplify codomain topology: subspace (C\\<union>A) (subspace X TX (C\\<union>A)) C = subspace X TX C.\<close>
      have hC_sub_CuA: "C \<subseteq> ?CuA" by (by100 blast)
      have "subspace_topology ?CuA (subspace_topology X TX ?CuA) C = subspace_topology X TX C"
        using subspace_topology_trans[OF hC_sub_CuA] by simp
      \<comment> \<open>Use pasting\\_lemma\\_two\\_closed: r continuous on C and A in subspace of C\\<union>A.\<close>
      show "top1_continuous_map_on ?CuA (subspace_topology X TX ?CuA) C (subspace_topology ?CuA (subspace_topology X TX ?CuA) C) r"
        unfolding \<open>subspace_topology ?CuA _ C = subspace_topology X TX C\<close>
      proof (rule pasting_lemma_two_closed)
        show "is_topology_on ?CuA (subspace_topology X TX ?CuA)"
          by (rule subspace_topology_is_topology_on[OF htop hCuA_sub])
        show "is_topology_on C (subspace_topology X TX C)"
          by (rule subspace_topology_is_topology_on[OF htop hC_sub])
        \<comment> \<open>C and A closed in C \\<union> A (from closed in X via Theorem\\_17\\_2).\<close>
        show "closedin_on ?CuA (subspace_topology X TX ?CuA) C"
          using Theorem_17_2[OF htop hCuA_sub, of C] hC_closed by (by100 blast)
        show "closedin_on ?CuA (subspace_topology X TX ?CuA) A"
          using Theorem_17_2[OF htop hCuA_sub, of A] hA_closed by (by100 blast)
        show "C \<union> A = ?CuA" by simp
        show "\<forall>x \<in> ?CuA. r x \<in> C" unfolding r_def using hv(2) by (by100 simp)
        \<comment> \<open>r continuous on C: r|C = id, inclusion is continuous.\<close>
        have hC_sub_CuA2: "C \<subseteq> ?CuA" by (by100 blast)
        have hA_sub_CuA2: "A \<subseteq> ?CuA" by (by100 blast)
        have hsubC: "subspace_topology ?CuA (subspace_topology X TX ?CuA) C = subspace_topology X TX C"
          using subspace_topology_trans[OF hC_sub_CuA2] by simp
        have hsubA: "subspace_topology ?CuA (subspace_topology X TX ?CuA) A = subspace_topology X TX A"
          using subspace_topology_trans[OF hA_sub_CuA2] by simp
        show "top1_continuous_map_on C (subspace_topology ?CuA (subspace_topology X TX ?CuA) C) C (subspace_topology X TX C) r"
          unfolding hsubC top1_continuous_map_on_def
        proof (intro conjI ballI allI impI)
          fix x assume "x \<in> C" thus "r x \<in> C" unfolding r_def by simp
        next
          fix V assume hV: "V \<in> subspace_topology X TX C"
          then obtain U where "U \<in> TX" "V = C \<inter> U" unfolding subspace_topology_def
            by (by5000 auto)
          hence "V \<subseteq> C" by (by100 blast)
          have "{x \<in> C. r x \<in> V} = V"
          proof -
            have hr_id: "\<forall>x. x \<in> C \<longrightarrow> r x = x" unfolding r_def by simp
            have "{x \<in> C. r x \<in> V} = {x \<in> C. x \<in> V}"
              using hr_id by (by5000 force)
            also have "\<dots> = V" using \<open>V \<subseteq> C\<close> by (by100 blast)
            finally show ?thesis .
          qed
          thus "{x \<in> C. r x \<in> V} \<in> subspace_topology X TX C" using hV by simp
        qed
        show "top1_continuous_map_on A (subspace_topology ?CuA (subspace_topology X TX ?CuA) A) C (subspace_topology X TX C) r"
        proof -
          \<comment> \<open>r|A = const v.\<close>
          have hr_const: "\<forall>x. x \<in> A \<longrightarrow> r x = v" unfolding r_def using True by (by5000 force)
          \<comment> \<open>Constant map v: A \\<to> C is continuous (Theorem\\_18\\_2(1)).\<close>
          have hTA: "is_topology_on A (subspace_topology X TX A)"
            by (rule subspace_topology_is_topology_on[OF htop hA_sub])
          have hTC: "is_topology_on C (subspace_topology X TX C)"
            by (rule subspace_topology_is_topology_on[OF htop hC_sub])
          have "top1_continuous_map_on A (subspace_topology X TX A) C (subspace_topology X TX C) r"
            unfolding top1_continuous_map_on_def
          proof (intro conjI ballI allI impI)
            fix x assume "x \<in> A" thus "r x \<in> C" using hr_const hv(2) by simp
          next
            fix V assume hV: "V \<in> subspace_topology X TX C"
            have "{x \<in> A. r x \<in> V} = (if v \<in> V then A else {})"
              using hr_const by (by5000 force)
            moreover have "(if v \<in> V then A else {}) \<in> subspace_topology X TX A"
            proof (cases "v \<in> V")
              case True
              have "A \<in> subspace_topology X TX A"
              proof -
                have "X \<in> TX" using htop unfolding is_topology_on_def by (by100 blast)
                hence "A \<inter> X \<in> {A \<inter> U | U. U \<in> TX}" by (by100 blast)
                moreover have "A \<inter> X = A" using hA_sub by (by100 blast)
                ultimately show ?thesis unfolding subspace_topology_def by simp
              qed
              thus ?thesis using True by simp
            next
              case False
              have "{} \<in> subspace_topology X TX A"
              proof -
                have "{} \<in> TX" using htop unfolding is_topology_on_def by (by100 blast)
                hence "A \<inter> {} \<in> {A \<inter> U | U. U \<in> TX}" by (by100 blast)
                moreover have "A \<inter> {} = {}" by (by100 blast)
                ultimately show ?thesis unfolding subspace_topology_def by simp
              qed
              thus ?thesis using False by simp
            qed
            ultimately show "{x \<in> A. r x \<in> V} \<in> subspace_topology X TX A" by simp
          qed
          thus ?thesis using hsubA by simp
        qed
      qed
    qed
  next
    case False
    \<comment> \<open>Card 2: A meets C at 2 points {h 0, h 1}. Map A along path in C.\<close>
    \<comment> \<open>Both endpoints h 0, h 1 are in C.\<close>
    have hh0_C: "h 0 \<in> C" and hh1_C: "h 1 \<in> C"
    proof -
      \<comment> \<open>A \\<inter> C \\<subseteq> {h 0, h 1}, A \\<inter> C \\<noteq> {v} for any single v (from False), A \\<inter> C \\<noteq> {}.
         So A \\<inter> C = {h 0, h 1}.\<close>
      have hh01_ne: "h 0 \<noteq> h 1"
      proof
        assume "h 0 = h 1"
        have "inj_on h I_set" using hh unfolding top1_homeomorphism_on_def bij_betw_def
          by (by100 blast)
        from inj_onD[OF this \<open>h 0 = h 1\<close>] show False
          unfolding top1_unit_interval_def by (by100 auto)
      qed
      have "A \<inter> C = {h 0, h 1}"
      proof -
        \<comment> \<open>v \\<in> A \\<inter> C, A \\<inter> C \\<subseteq> {h 0, h 1}, A \\<inter> C \\<noteq> {v}. So A \\<inter> C = {h 0, h 1}.\<close>
        have "v \<in> {h 0, h 1}" using hv hAC_sub_h by (by100 blast)
        from False have "A \<inter> C \<noteq> {v}" .
        \<comment> \<open>Since v \\<in> A\\<inter>C, A\\<inter>C \\<noteq> {v}, there's another element w \\<in> A\\<inter>C, w \\<noteq> v.\<close>
        then obtain w where "w \<in> A \<inter> C" "w \<noteq> v" using hv by (by100 blast)
        hence "w \<in> {h 0, h 1}" using hAC_sub_h by (by100 blast)
        \<comment> \<open>{v, w} \\<subseteq> A\\<inter>C, v \\<noteq> w, both in {h 0, h 1}. So {v,w} = {h 0, h 1}.\<close>
        have "{v, w} \<subseteq> A \<inter> C" using hv \<open>w \<in> A \<inter> C\<close> by (by100 blast)
        have "{v, w} \<subseteq> {h 0, h 1}" using \<open>v \<in> {h 0, h 1}\<close> \<open>w \<in> {h 0, h 1}\<close> by (by100 blast)
        have "card {v, w} = 2" using \<open>w \<noteq> v\<close> by (by100 simp)
        have "card {h 0, h 1} = 2" using hh01_ne by (by100 simp)
        from card_subset_eq[of "{h 0, h 1}" "{v, w}"]
        have "{v, w} = {h 0, h 1}" using \<open>{v, w} \<subseteq> {h 0, h 1}\<close> \<open>card {v, w} = 2\<close>
            \<open>card {h 0, h 1} = 2\<close> by (by100 auto)
        hence "{h 0, h 1} \<subseteq> A \<inter> C" using \<open>{v, w} \<subseteq> A \<inter> C\<close> by simp
        thus "A \<inter> C = {h 0, h 1}" using hAC_sub_h by (by100 blast)
      qed
      thus "h 0 \<in> C" "h 1 \<in> C" by (by100 blast)+
    qed
    \<comment> \<open>Get path \\<gamma> in C from h 0 to h 1 (C is path-connected).\<close>
    have "top1_path_connected_on C (subspace_topology X TX C)" using hC_pc .
    then obtain \<gamma> where h\<gamma>: "top1_is_path_on C (subspace_topology X TX C) (h 0) (h 1) \<gamma>"
      unfolding top1_path_connected_on_def using hh0_C hh1_C by (by100 blast)
    \<comment> \<open>h\\<inverse>: A \\<to> [0,1] is the inverse homeomorphism.\<close>
    let ?hinv = "inv_into I_set h"
    \<comment> \<open>Define r: r|C = id, r|A = \\<gamma> \\<circ> h\\<inverse>.\<close>
    define r where "r x = (if x \<in> C then x else \<gamma> (?hinv x))" for x
    \<comment> \<open>r is a retraction C \\<union> A \\<to> C.\<close>
    show ?thesis unfolding top1_retract_of_on_def top1_is_retraction_on_def
    proof (intro exI[of _ r] conjI)
      show "C \<subseteq> ?CuA" by (by100 blast)
      show "\<forall>a \<in> C. r a = a" unfolding r_def by (by100 simp)
      \<comment> \<open>Continuity via pasting lemma, same structure as card 1.\<close>
      have hC_sub_CuA2: "C \<subseteq> ?CuA" by (by100 blast)
      have hA_sub_CuA2: "A \<subseteq> ?CuA" by (by100 blast)
      have hsubC: "subspace_topology ?CuA (subspace_topology X TX ?CuA) C = subspace_topology X TX C"
        using subspace_topology_trans[OF hC_sub_CuA2] by simp
      have hsubA: "subspace_topology ?CuA (subspace_topology X TX ?CuA) A = subspace_topology X TX A"
        using subspace_topology_trans[OF hA_sub_CuA2] by simp
      show "top1_continuous_map_on ?CuA (subspace_topology X TX ?CuA) C
          (subspace_topology ?CuA (subspace_topology X TX ?CuA) C) r"
        unfolding hsubC
      proof (rule pasting_lemma_two_closed)
        show "is_topology_on ?CuA (subspace_topology X TX ?CuA)"
          by (rule subspace_topology_is_topology_on[OF htop hCuA_sub])
        show "is_topology_on C (subspace_topology X TX C)"
          by (rule subspace_topology_is_topology_on[OF htop hC_sub])
        show "closedin_on ?CuA (subspace_topology X TX ?CuA) C"
          using Theorem_17_2[OF htop hCuA_sub, of C] hC_closed by (by100 blast)
        show "closedin_on ?CuA (subspace_topology X TX ?CuA) A"
          using Theorem_17_2[OF htop hCuA_sub, of A] hA_closed by (by100 blast)
        show "C \<union> A = ?CuA" by simp
        show "\<forall>x \<in> ?CuA. r x \<in> C"
        proof (intro ballI)
          fix x assume "x \<in> ?CuA"
          show "r x \<in> C"
          proof (cases "x \<in> C")
            case True thus ?thesis unfolding r_def by simp
          next
            case False
            hence "x \<in> A" using \<open>x \<in> ?CuA\<close> by (by100 blast)
            have "r x = \<gamma> (?hinv x)" unfolding r_def using False by simp
            \<comment> \<open>\\<gamma> maps into C (from path definition: \\<gamma>: [0,1] \\<to> C).\<close>
            have "\<gamma> (?hinv x) \<in> C"
            proof -
              \<comment> \<open>h\\<inverse>(x) \\<in> I\\_set since h is bij I\\_set A and x \\<in> A.\<close>
              have "bij_betw h I_set A" using hh unfolding top1_homeomorphism_on_def by (by100 blast)
              hence "?hinv x \<in> I_set" using \<open>x \<in> A\<close>
                by (by100 simp) (metis bij_betw_imp_surj_on inv_into_into)
              \<comment> \<open>\\<gamma> maps I\\_set to C (from is\\_path: continuous [0,1] \\<to> C, \\<gamma>(t) \\<in> C for t \\<in> I\\_set).\<close>
              have "\<gamma> ` I_set \<subseteq> C"
                using h\<gamma> unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
              thus ?thesis using \<open>?hinv x \<in> I_set\<close> by (by100 blast)
            qed
            thus ?thesis using \<open>r x = \<gamma> (?hinv x)\<close> by simp
          qed
        qed
        \<comment> \<open>r|C = id continuous (same as card 1).\<close>
        show "top1_continuous_map_on C (subspace_topology ?CuA (subspace_topology X TX ?CuA) C) C (subspace_topology X TX C) r"
          unfolding hsubC top1_continuous_map_on_def
        proof (intro conjI ballI allI impI)
          fix x assume "x \<in> C" thus "r x \<in> C" unfolding r_def by simp
        next
          fix V assume hV: "V \<in> subspace_topology X TX C"
          then obtain U where "U \<in> TX" "V = C \<inter> U" unfolding subspace_topology_def by (by5000 auto)
          hence "V \<subseteq> C" by (by100 blast)
          have hr_id: "\<forall>x. x \<in> C \<longrightarrow> r x = x" unfolding r_def by simp
          have "{x \<in> C. r x \<in> V} = {x \<in> C. x \<in> V}" using hr_id by (by5000 force)
          also have "\<dots> = V" using \<open>V \<subseteq> C\<close> by (by100 blast)
          finally show "{x \<in> C. r x \<in> V} \<in> subspace_topology X TX C" using hV by simp
        qed
        \<comment> \<open>r|A = \\<gamma> \\<circ> h\\<inverse> continuous.\<close>
        \<comment> \<open>r = \\<gamma> \\<circ> h\\<inverse> on A (including at intersection {h 0, h 1}).\<close>
        have hAC_eq: "A \<inter> C = {h 0, h 1}" using hAC_sub_h hh0_C hh1_C hh0_A hh1_A by (by100 blast)
        have hr_on_A: "\<forall>x \<in> A. r x = \<gamma> (?hinv x)"
        proof
          fix x assume "x \<in> A"
          show "r x = \<gamma> (?hinv x)"
          proof (cases "x \<in> C")
            case False
            thus ?thesis unfolding r_def by simp
          next
            case True
            hence "x \<in> A \<inter> C" using \<open>x \<in> A\<close> by (by100 blast)
            hence hx_h01: "x \<in> {h 0, h 1}" using hAC_eq by simp
            have "r x = x" unfolding r_def using True by simp
            have h_inj: "inj_on h I_set"
              using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
            have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
            have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
            have hinv_h0: "?hinv (h 0) = 0"
              using inv_into_f_f[OF h_inj h0_I] .
            have hinv_h1: "?hinv (h 1) = 1"
              using inv_into_f_f[OF h_inj h1_I] .
            have h\<gamma>0: "\<gamma> 0 = h 0" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
            have h\<gamma>1: "\<gamma> 1 = h 1" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
            have "x = h 0 \<or> x = h 1" using hx_h01 by (by100 blast)
            thus ?thesis
            proof
              assume "x = h 0"
              hence "\<gamma> (?hinv x) = \<gamma> 0" using hinv_h0 by simp
              also have "\<dots> = h 0" using h\<gamma>0 .
              finally show ?thesis using \<open>r x = x\<close> \<open>x = h 0\<close> by simp
            next
              assume "x = h 1"
              hence "\<gamma> (?hinv x) = \<gamma> 1" using hinv_h1 by simp
              also have "\<dots> = h 1" using h\<gamma>1 .
              finally show ?thesis using \<open>r x = x\<close> \<open>x = h 1\<close> by simp
            qed
          qed
        qed
        \<comment> \<open>r|A = \\<gamma> \\<circ> h\\<inverse>: continuous composition. Use subspace transitivity + composition.\<close>
        have hA_sub_CuA2: "A \<subseteq> ?CuA" by (by100 blast)
        have hsubA2: "subspace_topology ?CuA (subspace_topology X TX ?CuA) A = subspace_topology X TX A"
          using subspace_topology_trans[OF hA_sub_CuA2] by simp
        \<comment> \<open>r = \\<gamma> \\<circ> h\\<inverse> on A. Already proved as hr\\_on\\_A. Both continuous. Composition continuous.\<close>
        have h\<gamma>_cont2: "top1_continuous_map_on I_set I_top C (subspace_topology X TX C) \<gamma>"
          using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
        have hhinv_cont2: "top1_continuous_map_on A (subspace_topology X TX A) I_set I_top ?hinv"
          using hh unfolding top1_homeomorphism_on_def by (by100 blast)
        have hcomp2: "top1_continuous_map_on A (subspace_topology X TX A) C (subspace_topology X TX C) (\<gamma> \<circ> ?hinv)"
          using top1_continuous_map_on_comp[OF hhinv_cont2 h\<gamma>_cont2] .
        \<comment> \<open>r and \\<gamma> \\<circ> h\\<inverse> agree on A (from hr\\_on\\_A).\<close>
        have "top1_continuous_map_on A (subspace_topology X TX A) C (subspace_topology X TX C) r"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI allI impI)
          fix x assume "x \<in> A"
          show "r x \<in> C" using hr_on_A \<open>x \<in> A\<close>
            hcomp2[unfolded top1_continuous_map_on_def] by (by100 force)
        next
          fix V assume hV: "V \<in> subspace_topology X TX C"
          \<comment> \<open>{x \\<in> A. r x \\<in> V} = {x \\<in> A. (\\<gamma> \\<circ> h\\<inverse>) x \\<in> V} (since r = \\<gamma> \\<circ> h\\<inverse> on A).\<close>
          have "\<forall>x \<in> A. (r x \<in> V) = ((\<gamma> \<circ> ?hinv) x \<in> V)"
            using hr_on_A by (by100 simp)
          hence "{x \<in> A. r x \<in> V} = {x \<in> A. (\<gamma> \<circ> ?hinv) x \<in> V}"
            by (by5000 force)
          also have "\<dots> \<in> subspace_topology X TX A"
            using hcomp2 hV unfolding top1_continuous_map_on_def by (by100 blast)
          finally show "{x \<in> A. r x \<in> V} \<in> subspace_topology X TX A" .
        qed
        thus "top1_continuous_map_on A (subspace_topology ?CuA (subspace_topology X TX ?CuA) A) C (subspace_topology X TX C) r"
          unfolding hsubA2 .
      qed
    qed
  qed
qed

\<comment> \<open>Graph connected subunion retract: in a tree with graph decomposition,
   a path-connected union of arcs from \\<A> is a retract of T.
   (Per expert audit 7: the old version without path-connectedness was false.)\<close>
lemma graph_cycle_retract:
  fixes T :: "'a set" and TT :: "'a set set"
  assumes "top1_is_tree_on T TT"
      and "\<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)"
      and "\<Union>\<A> = T"
      and "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and "finite \<A>"
      and "\<forall>C. C \<subseteq> T \<longrightarrow> (closedin_on T TT C \<longleftrightarrow>
          (\<forall>A\<in>\<A>. closedin_on A (subspace_topology T TT A) (A \<inter> C)))"
      and "\<S> \<subseteq> \<A>"
      and "\<S> \<noteq> {}"
      and "top1_path_connected_on (\<Union>\<S>) (subspace_topology T TT (\<Union>\<S>))"
  shows "top1_retract_of_on T TT (\<Union>\<S>)"
  using assms
proof (induction "card (\<A> - \<S>)" arbitrary: \<A> \<S> rule: less_induct)
  case (less \<A> \<S>)
  show ?case
  proof (cases "\<A> = \<S>")
    case True
    \<comment> \<open>Base: T = C. Identity retraction.\<close>
    hence "T = \<Union>\<S>" using less.prems(3) by (by100 simp)
    have "top1_retract_of_on T TT T"
      unfolding top1_retract_of_on_def top1_is_retraction_on_def
    proof (intro exI[of _ id] conjI)
      show "T \<subseteq> T" by (by100 blast)
      show "top1_continuous_map_on T TT T (subspace_topology T TT T) id"
      proof -
        have htop: "is_topology_on T TT"
          using less.prems(1) unfolding top1_is_tree_on_def top1_is_graph_on_def
            is_topology_on_strict_def by (by100 blast)
        \<comment> \<open>Use inclusion: id on T is the inclusion T \\<hookrightarrow> T, continuous by Theorem 18.2(2).\<close>
        from Theorem_18_2(2)[OF htop htop htop, rule_format, of T]
        have hincl: "top1_continuous_map_on T (subspace_topology T TT T) T TT id"
          using Theorem_18_2(2)[OF htop htop htop, rule_format, of T] by (by100 blast)
        \<comment> \<open>But we need id: (T, TT) \\<to> (T, subspace T TT T), not the other direction.
           Since subspace\\_topology T TT T = TT, both are the same.\<close>
        have hstrict: "is_topology_on_strict T TT"
          using less.prems(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
        have "subspace_topology T TT T = TT"
          by (rule subspace_topology_self_carrier)
             (use hstrict in \<open>unfold is_topology_on_strict_def, by100 blast\<close>)
        thus ?thesis using hincl by simp
      qed
      show "\<forall>a\<in>T. id a = a" by (by100 simp)
    qed
    thus ?thesis using \<open>T = \<Union>\<S>\<close> by simp
  next
    case False
    \<comment> \<open>Step: pick A0 \<in> \<A> - \<S> that meets C = \<Union>\<S> (adjacent outside arc).
       Per expert audit 7: use A0 with A0 \<inter> C \<noteq> {} to maintain path-connectedness.\<close>
    let ?C = "\<Union>\<S>"
    obtain A0 where hA0: "A0 \<in> \<A>" "A0 \<notin> \<S>" "A0 \<inter> ?C \<noteq> {}"
    proof -
      \<comment> \<open>By contradiction: if no outside arc meets C, T is disconnected.\<close>
      { assume hno: "\<forall>A \<in> \<A> - \<S>. A \<inter> ?C = {}"
        have hT_eq: "?C \<union> \<Union>(\<A> - \<S>) = T"
          using less.prems(3,7) by (by100 blast)
        have hdisjoint: "?C \<inter> \<Union>(\<A> - \<S>) = {}"
          using hno by (by100 blast)
        have "?C \<noteq> {}"
        proof -
          from less.prems(8) obtain B where "B \<in> \<S>" by (by100 blast)
          hence "B \<in> \<A>" using less.prems(7) by (by100 blast)
          hence "top1_is_arc_on B (subspace_topology T TT B)" using less.prems(2) by (by100 blast)
          then obtain g where "top1_homeomorphism_on I_set I_top B (subspace_topology T TT B) g"
            unfolding top1_is_arc_on_def by (by100 blast)
          hence "bij_betw g I_set B" unfolding top1_homeomorphism_on_def by (by100 blast)
          hence "B \<noteq> {}" unfolding bij_betw_def top1_unit_interval_def by (by100 auto)
          thus ?thesis using \<open>B \<in> \<S>\<close> by (by100 blast)
        qed
        have "\<Union>(\<A> - \<S>) \<noteq> {}"
        proof -
          from False have "\<A> - \<S> \<noteq> {}" using less.prems(7) by (by100 blast)
          then obtain B where "B \<in> \<A> - \<S>" by (by100 blast)
          hence "B \<in> \<A>" by (by100 blast)
          hence "top1_is_arc_on B (subspace_topology T TT B)" using less.prems(2) by (by100 blast)
          then obtain g where "top1_homeomorphism_on I_set I_top B (subspace_topology T TT B) g"
            unfolding top1_is_arc_on_def by (by100 blast)
          hence "bij_betw g I_set B" unfolding top1_homeomorphism_on_def by (by100 blast)
          hence "B \<noteq> {}" unfolding bij_betw_def top1_unit_interval_def by (by100 auto)
          thus ?thesis using \<open>B \<in> \<A> - \<S>\<close> by (by100 blast)
        qed
        \<comment> \<open>Both C and \\<Union>(\\<A>-\\<S>) are closed in T (coherent topology).\<close>
        have hhaus: "is_hausdorff_on T TT"
          using less.prems(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
        have htop: "is_topology_on T TT"
          using less.prems(1) unfolding top1_is_tree_on_def top1_is_graph_on_def
            is_topology_on_strict_def by (by100 blast)
        \<comment> \<open>Each arc is compact (arc\\_compact) \\<Rightarrow> closed in Hausdorff T (Theorem\\_26\\_3).\<close>
        have hclosed_arcs: "\<forall>A \<in> \<A>. closedin_on T TT A"
        proof (intro ballI)
          fix A assume "A \<in> \<A>"
          have "A \<subseteq> T" using less.prems(2) \<open>A \<in> \<A>\<close> by (by100 blast)
          have "top1_is_arc_on A (subspace_topology T TT A)" using less.prems(2) \<open>A \<in> \<A>\<close> by (by100 blast)
          hence "top1_compact_on A (subspace_topology T TT A)" using arc_compact by (by100 blast)
          thus "closedin_on T TT A" by (rule Theorem_26_3[OF hhaus \<open>A \<subseteq> T\<close>])
        qed
        have "closedin_on T TT ?C"
        proof -
          have "\<forall>A \<in> \<S>. closedin_on T TT A" using hclosed_arcs less.prems(7) by (by100 blast)
          have "finite \<S>" using finite_subset[OF less.prems(7) less.prems(5)] .
          show ?thesis by (rule closedin_on_finite_Union[OF htop \<open>\<forall>A \<in> \<S>. closedin_on T TT A\<close> \<open>finite \<S>\<close>])
        qed
        have "closedin_on T TT (\<Union>(\<A> - \<S>))"
        proof -
          have "\<forall>A \<in> \<A> - \<S>. closedin_on T TT A" using hclosed_arcs by (by100 blast)
          have "finite (\<A> - \<S>)" using less.prems(5) by (by100 blast)
          show ?thesis by (rule closedin_on_finite_Union[OF htop \<open>\<forall>A \<in> \<A> - \<S>. closedin_on T TT A\<close> \<open>finite (\<A> - \<S>)\<close>])
        qed
        \<comment> \<open>T is connected.\<close>
        have "top1_connected_on T TT"
          using less.prems(1) unfolding top1_is_tree_on_def by (by100 blast)
        \<comment> \<open>Connected space cannot have two non-empty disjoint closed sets covering it.\<close>
        \<comment> \<open>C is closed \\<Rightarrow> T \\ C is open. \\<Union>(\\<A>-\\<S>) = T \\ C (disjoint + cover).
           So \\<Union>(\\<A>-\\<S>) is open. Similarly C is open. Separation \\<Rightarrow> \\<not> connected.\<close>
        have "T - ?C \<in> TT"
          using \<open>closedin_on T TT ?C\<close> unfolding closedin_on_def by (by100 blast)
        have "T - \<Union>(\<A> - \<S>) \<in> TT"
          using \<open>closedin_on T TT (\<Union>(\<A> - \<S>))\<close> unfolding closedin_on_def by (by100 blast)
        have hC_sub_T: "?C \<subseteq> T" using hT_eq by (by100 blast)
        have hR_sub_T: "\<Union>(\<A> - \<S>) \<subseteq> T" using hT_eq by (by100 blast)
        have "T - ?C = \<Union>(\<A> - \<S>)" using hT_eq hdisjoint hC_sub_T hR_sub_T by (by100 blast)
        have "T - \<Union>(\<A> - \<S>) = ?C" using hT_eq hdisjoint hC_sub_T hR_sub_T by (by100 blast)
        hence "?C \<in> TT" using \<open>T - \<Union>(\<A> - \<S>) \<in> TT\<close> by simp
        have "\<Union>(\<A> - \<S>) \<in> TT" using \<open>T - ?C \<in> TT\<close> \<open>T - ?C = \<Union>(\<A> - \<S>)\<close> by simp
        \<comment> \<open>Now we have a separation: C and \\<Union>(\\<A>-\\<S>) are both open, non-empty, disjoint, cover T.\<close>
        have "top1_is_separation_on T TT ?C (\<Union>(\<A> - \<S>))"
          unfolding top1_is_separation_on_def
          using \<open>?C \<in> TT\<close> \<open>\<Union>(\<A> - \<S>) \<in> TT\<close> \<open>?C \<noteq> {}\<close> \<open>\<Union>(\<A> - \<S>) \<noteq> {}\<close>
            hdisjoint hT_eq by (by100 blast)
        have False
          using Lemma_23_1[of T TT] \<open>top1_connected_on T TT\<close>
            \<open>top1_is_separation_on T TT ?C (\<Union>(\<A> - \<S>))\<close> by (by100 blast)
      }
      \<comment> \<open>So \\<exists> adjacent arc.\<close>
      hence "\<exists>A. A \<in> \<A> \<and> A \<notin> \<S> \<and> A \<inter> ?C \<noteq> {}" by (by100 blast)
      thus ?thesis using that by (by100 blast)
    qed
    let ?\<S>' = "insert A0 \<S>"
    have hcard_lt: "card (\<A> - ?\<S>') < card (\<A> - \<S>)"
    proof -
      have "\<A> - ?\<S>' = (\<A> - \<S>) - {A0}" by (by100 blast)
      have "A0 \<in> \<A> - \<S>" using hA0(1-2) by (by100 blast)
      have "finite (\<A> - \<S>)" using less.prems(5) by (by100 blast)
      have "\<A> - \<S> \<noteq> {}" using \<open>A0 \<in> \<A> - \<S>\<close> by (by100 blast)
      have "card (\<A> - \<S>) > 0" using \<open>finite (\<A> - \<S>)\<close> \<open>\<A> - \<S> \<noteq> {}\<close> by (by100 auto)
      show ?thesis using \<open>\<A> - ?\<S>' = (\<A> - \<S>) - {A0}\<close>
          \<open>A0 \<in> \<A> - \<S>\<close> \<open>finite (\<A> - \<S>)\<close> \<open>card _ > 0\<close> by (by100 simp)
    qed
    have "?\<S>' \<subseteq> \<A>" using less.prems(7) hA0(1) by (by100 blast)
    have "?\<S>' \<noteq> {}" by (by100 simp)
    have "A0 \<subseteq> T" using less.prems(2) hA0(1) by (by100 blast)
    \<comment> \<open>C' = C \<union> A0 is path-connected (C pc, A0 pc, A0 \<inter> C \<noteq> {}).\<close>
    have hS'_pc: "top1_path_connected_on (\<Union>?\<S>') (subspace_topology T TT (\<Union>?\<S>'))"
    proof -
      \<comment> \<open>C is pc, A0 is pc (arc), both contain a common point from A0 \\<inter> C.\<close>
      from hA0(3) obtain p where "p \<in> A0 \<inter> ?C" by (by100 blast)
      hence hp_A0: "p \<in> A0" and hp_C: "p \<in> ?C" by (by100 blast)+
      \<comment> \<open>Use path\\_connected\\_finite\\_union\\_common\\_point with F = {C, A0}, common point p.\<close>
      have hS'_eq: "\<Union>?\<S>' = ?C \<union> A0" by (by100 blast)
      let ?F = "{?C, A0}"
      have "finite ?F" by (by100 simp)
      have "\<forall>A \<in> ?F. A \<subseteq> \<Union>?\<S>'" using hS'_eq by (by100 blast)
      have "\<forall>A \<in> ?F. p \<in> A" using hp_A0 hp_C by (by100 blast)
      have "\<Union>?\<S>' = \<Union>?F" using hS'_eq by (by100 auto)
      have htop_S': "is_topology_on (\<Union>?\<S>') (subspace_topology T TT (\<Union>?\<S>'))"
      proof -
        have htop: "is_topology_on T TT"
          using less.prems(1) unfolding top1_is_tree_on_def top1_is_graph_on_def
            is_topology_on_strict_def by (by100 blast)
        have "?C \<subseteq> T"
        proof -
          have "\<forall>A \<in> \<S>. A \<subseteq> T" using less.prems(2,7) by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        have "\<Union>?\<S>' \<subseteq> T" using \<open>?C \<subseteq> T\<close> \<open>A0 \<subseteq> T\<close> hS'_eq by (by100 blast)
        show ?thesis by (rule subspace_topology_is_topology_on[OF htop \<open>\<Union>?\<S>' \<subseteq> T\<close>])
      qed
      have hpc_each: "\<forall>A \<in> ?F. top1_path_connected_on A (subspace_topology (\<Union>?\<S>') (subspace_topology T TT (\<Union>?\<S>')) A)"
      proof (intro ballI)
        fix A assume "A \<in> ?F"
        hence "A = ?C \<or> A = A0" by (by100 blast)
        thus "top1_path_connected_on A (subspace_topology (\<Union>?\<S>') (subspace_topology T TT (\<Union>?\<S>')) A)"
        proof
          assume "A = ?C"
          have "?C \<subseteq> \<Union>?\<S>'" using hS'_eq by (by100 blast)
          have "subspace_topology (\<Union>?\<S>') (subspace_topology T TT (\<Union>?\<S>')) ?C
              = subspace_topology T TT ?C"
            using subspace_topology_trans[OF \<open>?C \<subseteq> \<Union>?\<S>'\<close>] by simp
          thus ?thesis using less.prems(9) \<open>A = ?C\<close> by simp
        next
          assume "A = A0"
          have "A0 \<subseteq> \<Union>?\<S>'" using hS'_eq by (by100 blast)
          have "subspace_topology (\<Union>?\<S>') (subspace_topology T TT (\<Union>?\<S>')) A0
              = subspace_topology T TT A0"
            using subspace_topology_trans[OF \<open>A0 \<subseteq> \<Union>?\<S>'\<close>] by simp
          \<comment> \<open>A0 is pc in subspace T TT A0 (arc = homeo to [0,1] = pc).\<close>
          have "top1_path_connected_on A0 (subspace_topology T TT A0)"
          proof (rule connected_locally_path_connected_imp_path_connected)
            have htop_T: "is_topology_on T TT"
              using less.prems(1) unfolding top1_is_tree_on_def top1_is_graph_on_def
                is_topology_on_strict_def by (by100 blast)
            show "is_topology_on A0 (subspace_topology T TT A0)"
              by (rule subspace_topology_is_topology_on[OF htop_T \<open>A0 \<subseteq> T\<close>])
            have hA0_arc: "top1_is_arc_on A0 (subspace_topology T TT A0)"
              using less.prems(2) hA0(1) by (by100 blast)
            show "top1_connected_on A0 (subspace_topology T TT A0)"
              using arc_connected[OF hA0_arc] .
            show "top1_locally_path_connected_on A0 (subspace_topology T TT A0)"
              using arc_locally_path_connected[OF hA0_arc htop_T \<open>A0 \<subseteq> T\<close>] .
            show "A0 \<noteq> {}"
            proof -
              obtain g where "top1_homeomorphism_on I_set I_top A0 (subspace_topology T TT A0) g"
                using hA0_arc unfolding top1_is_arc_on_def by (by100 blast)
              hence "bij_betw g I_set A0" unfolding top1_homeomorphism_on_def by (by100 blast)
              hence "A0 \<noteq> {}" unfolding bij_betw_def top1_unit_interval_def by (by100 auto)
              thus ?thesis .
            qed
          qed
          thus ?thesis using \<open>A = A0\<close> \<open>subspace_topology _ _ A0 = _\<close> by simp
        qed
      qed
      from path_connected_finite_union_common_point[OF htop_S' \<open>finite ?F\<close>
          \<open>\<forall>A \<in> ?F. A \<subseteq> \<Union>?\<S>'\<close> this \<open>\<forall>A \<in> ?F. p \<in> A\<close>]
      show ?thesis using \<open>\<Union>?\<S>' = \<Union>?F\<close> by simp
    qed
    \<comment> \<open>By IH: T retracts onto C \<union> A0.\<close>
    from less.hyps[OF hcard_lt less.prems(1-6) \<open>?\<S>' \<subseteq> \<A>\<close> \<open>?\<S>' \<noteq> {}\<close> hS'_pc]
    have hret_ext: "top1_retract_of_on T TT (\<Union>?\<S>')" .
    have hC'_eq: "\<Union>?\<S>' = ?C \<union> A0" by (by100 blast)
    hence hret_CuA: "top1_retract_of_on T TT (?C \<union> A0)" using hret_ext by simp
    \<comment> \<open>Compose with retraction C \<union> A0 \<to> C (attached-arc retract).\<close>
    \<comment> \<open>Local retraction C \\<union> A0 \\<to> C, then compose with hret\\_CuA.\<close>
    have hlocal_retract: "top1_retract_of_on (?C \<union> A0) (subspace_topology T TT (?C \<union> A0)) ?C"
    proof -
      have htop: "is_topology_on T TT"
        using less.prems(1) unfolding top1_is_tree_on_def top1_is_graph_on_def
          is_topology_on_strict_def by (by100 blast)
      have hstrict: "is_topology_on_strict T TT"
        using less.prems(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
      have hhaus: "is_hausdorff_on T TT"
        using less.prems(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
      have "?C \<subseteq> T"
      proof -
        have "\<forall>A \<in> \<S>. A \<subseteq> T" using less.prems(2,7) by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      have hA0_arc: "top1_is_arc_on A0 (subspace_topology T TT A0)"
        using less.prems(2) hA0(1) by (by100 blast)
      have hA0C_sub_ep: "A0 \<inter> ?C \<subseteq> top1_arc_endpoints_on A0 (subspace_topology T TT A0)"
      proof -
        have "\<forall>B \<in> \<S>. A0 \<inter> B \<subseteq> top1_arc_endpoints_on A0 (subspace_topology T TT A0)"
        proof (intro ballI)
          fix B assume "B \<in> \<S>"
          hence "B \<in> \<A>" using less.prems(7) by (by100 blast)
          have "A0 \<noteq> B" using hA0(2) \<open>B \<in> \<S>\<close> by (by100 blast)
          from less.prems(4)[rule_format, OF hA0(1) \<open>B \<in> \<A>\<close> \<open>A0 \<noteq> B\<close>]
          show "A0 \<inter> B \<subseteq> top1_arc_endpoints_on A0 (subspace_topology T TT A0)" by (by100 blast)
        qed
        thus ?thesis by (by100 blast)
      qed
      have hC_closed: "closedin_on T TT ?C"
      proof -
        have "\<forall>A \<in> \<S>. closedin_on T TT A"
        proof (intro ballI)
          fix B assume "B \<in> \<S>"
          hence "B \<in> \<A>" using less.prems(7) by (by100 blast)
          have "B \<subseteq> T" using less.prems(2) \<open>B \<in> \<A>\<close> by (by100 blast)
          have "top1_is_arc_on B (subspace_topology T TT B)" using less.prems(2) \<open>B \<in> \<A>\<close> by (by100 blast)
          hence "top1_compact_on B (subspace_topology T TT B)" using arc_compact by (by100 blast)
          thus "closedin_on T TT B" by (rule Theorem_26_3[OF hhaus \<open>B \<subseteq> T\<close>])
        qed
        have "finite \<S>" using finite_subset[OF less.prems(7) less.prems(5)] .
        show ?thesis by (rule closedin_on_finite_Union[OF htop \<open>\<forall>A \<in> \<S>. closedin_on T TT A\<close> \<open>finite \<S>\<close>])
      qed
      show ?thesis
        by (rule retract_attached_arc[OF htop hstrict hhaus \<open>?C \<subseteq> T\<close> \<open>A0 \<subseteq> T\<close>
            less.prems(9) hA0_arc hA0(3) hA0C_sub_ep hC_closed])
    qed
    \<comment> \<open>Compose: r = r2 \\<circ> r1 where r1: T \\<to> C \\<union> A0, r2: C \\<union> A0 \\<to> C.\<close>
    from hret_CuA obtain r1 where hr1: "top1_is_retraction_on T TT (?C \<union> A0) r1"
      unfolding top1_retract_of_on_def by (by100 blast)
    from hlocal_retract obtain r2
      where hr2: "top1_is_retraction_on (?C \<union> A0) (subspace_topology T TT (?C \<union> A0)) ?C r2"
      unfolding top1_retract_of_on_def by (by100 blast)
    have hr1_cont: "top1_continuous_map_on T TT (?C \<union> A0) (subspace_topology T TT (?C \<union> A0)) r1"
      using hr1 unfolding top1_is_retraction_on_def by (by100 blast)
    have hr2_cont: "top1_continuous_map_on (?C \<union> A0) (subspace_topology T TT (?C \<union> A0))
        ?C (subspace_topology (?C \<union> A0) (subspace_topology T TT (?C \<union> A0)) ?C) r2"
      using hr2 unfolding top1_is_retraction_on_def by (by100 blast)
    \<comment> \<open>Subspace transitivity: subspace (C\\<union>A0) (subspace T TT (C\\<union>A0)) C = subspace T TT C.\<close>
    have hC_sub_CuA: "?C \<subseteq> ?C \<union> A0" by (by100 blast)
    have "subspace_topology (?C \<union> A0) (subspace_topology T TT (?C \<union> A0)) ?C = subspace_topology T TT ?C"
      using subspace_topology_trans[OF hC_sub_CuA] by simp
    hence hr2_cont': "top1_continuous_map_on (?C \<union> A0) (subspace_topology T TT (?C \<union> A0))
        ?C (subspace_topology T TT ?C) r2"
      using hr2_cont by simp
    have hcomp_cont: "top1_continuous_map_on T TT ?C (subspace_topology T TT ?C) (r2 \<circ> r1)"
      using top1_continuous_map_on_comp[OF hr1_cont hr2_cont'] .
    have hcomp_fix: "\<forall>a \<in> ?C. (r2 \<circ> r1) a = a"
    proof (intro ballI)
      fix a assume "a \<in> ?C"
      hence "a \<in> ?C \<union> A0" by (by100 blast)
      hence "r1 a = a" using hr1 unfolding top1_is_retraction_on_def by (by100 blast)
      hence "(r2 \<circ> r1) a = r2 a" by (by100 simp)
      also have "\<dots> = a" using hr2 \<open>a \<in> ?C\<close> unfolding top1_is_retraction_on_def by (by100 blast)
      finally show "(r2 \<circ> r1) a = a" .
    qed
    have "?C \<subseteq> T"
    proof -
      have "\<forall>A \<in> \<S>. A \<subseteq> T" using less.prems(2,7) by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    show ?thesis unfolding top1_retract_of_on_def top1_is_retraction_on_def
      using hcomp_cont hcomp_fix \<open>?C \<subseteq> T\<close>
    proof (intro exI[of _ "r2 \<circ> r1"] conjI)
      show "?C \<subseteq> T" using \<open>?C \<subseteq> T\<close> .
      show "top1_continuous_map_on T TT ?C (subspace_topology T TT ?C) (r2 \<circ> r1)"
        using hcomp_cont .
      show "\<forall>a \<in> ?C. (r2 \<circ> r1) a = a" using hcomp_fix .
    qed
  qed
qed


\<comment> \<open>Arc merge: two arcs sharing one endpoint form an arc.
   If A is an arc from a to v and B is an arc from v to b, with A inter B = {v},
   then A union B is an arc from a to b.
   Proof: path product gives continuous bijection [0,1] to A union B;
   Theorem 26.6 (compact-to-Hausdorff) gives homeomorphism.\<close>
lemma arc_merge_at_endpoint:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes hstrict: "is_topology_on_strict X TX"
      and hhaus: "is_hausdorff_on X TX"
      and hA_arc: "top1_is_arc_on A (subspace_topology X TX A)"
      and hB_arc: "top1_is_arc_on B (subspace_topology X TX B)"
      and hA_sub: "A \<subseteq> X" and hB_sub: "B \<subseteq> X"
      and hAB_inter: "A \<inter> B = {v}"
      and hep_A: "top1_arc_endpoints_on A (subspace_topology X TX A) = {a, v}"
      and hep_B: "top1_arc_endpoints_on B (subspace_topology X TX B) = {v, b}"
      and ha_ne_v: "a \<noteq> v" and hb_ne_v: "b \<noteq> v"
  shows "top1_is_arc_on (A \<union> B) (subspace_topology X TX (A \<union> B))
    \<and> top1_arc_endpoints_on (A \<union> B) (subspace_topology X TX (A \<union> B)) = {a, b}"
proof -
  have htop: "is_topology_on X TX"
    using hstrict unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>Step 1: Get homeomorphisms hA: [0,1] \\<to> A with hA(0)=a, hA(1)=v
     and hB: [0,1] \\<to> B with hB(0)=v, hB(1)=b.\<close>
  obtain hA where hhA: "top1_homeomorphism_on I_set I_top A (subspace_topology X TX A) hA"
      and hhA0: "hA 0 = a" and hhA1: "hA 1 = v"
  proof -
    obtain h0 where hh0: "top1_homeomorphism_on I_set I_top A (subspace_topology X TX A) h0"
      using hA_arc unfolding top1_is_arc_on_def by (by100 blast)
    have heps0: "top1_arc_endpoints_on A (subspace_topology X TX A) = {h0 0, h0 1}"
      by (rule arc_endpoints_are_boundary[OF hstrict hhaus hA_sub hA_arc hh0])
    have hab_h0: "{h0 0, h0 1} = {a, v}" using heps0 hep_A by simp
    have "h0 0 \<noteq> h0 1"
    proof
      assume "h0 0 = h0 1"
      hence "{h0 0, h0 1} = {h0 0}" by simp
      hence "card {a, v} \<le> 1" using hab_h0 by simp
      thus False using ha_ne_v by simp
    qed
    from doubleton_eq_iff[OF hab_h0 this]
    show ?thesis
    proof
      assume "h0 0 = a \<and> h0 1 = v" thus ?thesis using that[OF hh0] by (by100 blast)
    next
      assume "h0 0 = v \<and> h0 1 = a"
      have hcomp: "top1_homeomorphism_on I_set I_top A (subspace_topology X TX A) (h0 \<circ> (\<lambda>t::real. 1-t))"
        by (rule homeomorphism_on_comp[OF unit_interval_reversal_homeomorphism hh0])
      have "(h0 \<circ> (\<lambda>t::real. 1-t)) 0 = a" unfolding comp_def using \<open>h0 0 = v \<and> h0 1 = a\<close> by simp
      moreover have "(h0 \<circ> (\<lambda>t::real. 1-t)) 1 = v" unfolding comp_def using \<open>h0 0 = v \<and> h0 1 = a\<close> by simp
      ultimately show ?thesis using that[OF hcomp] by (by100 blast)
    qed
  qed
  obtain hB where hhB: "top1_homeomorphism_on I_set I_top B (subspace_topology X TX B) hB"
      and hhB0: "hB 0 = v" and hhB1: "hB 1 = b"
  proof -
    obtain h0 where hh0: "top1_homeomorphism_on I_set I_top B (subspace_topology X TX B) h0"
      using hB_arc unfolding top1_is_arc_on_def by (by100 blast)
    have heps0: "top1_arc_endpoints_on B (subspace_topology X TX B) = {h0 0, h0 1}"
      by (rule arc_endpoints_are_boundary[OF hstrict hhaus hB_sub hB_arc hh0])
    have hvb_h0: "{h0 0, h0 1} = {v, b}" using heps0 hep_B by simp
    have "h0 0 \<noteq> h0 1"
    proof
      assume "h0 0 = h0 1"
      hence "{h0 0, h0 1} = {h0 0}" by simp
      hence "card {v, b} \<le> 1" using hvb_h0 by simp
      thus False using hb_ne_v by simp
    qed
    from doubleton_eq_iff[OF hvb_h0 this]
    show ?thesis
    proof
      assume "h0 0 = v \<and> h0 1 = b" thus ?thesis using that[OF hh0] by (by100 blast)
    next
      assume "h0 0 = b \<and> h0 1 = v"
      have hcomp: "top1_homeomorphism_on I_set I_top B (subspace_topology X TX B) (h0 \<circ> (\<lambda>t::real. 1-t))"
        by (rule homeomorphism_on_comp[OF unit_interval_reversal_homeomorphism hh0])
      have "(h0 \<circ> (\<lambda>t::real. 1-t)) 0 = v" unfolding comp_def using \<open>h0 0 = b \<and> h0 1 = v\<close> by simp
      moreover have "(h0 \<circ> (\<lambda>t::real. 1-t)) 1 = b" unfolding comp_def using \<open>h0 0 = b \<and> h0 1 = v\<close> by simp
      ultimately show ?thesis using that[OF hcomp] by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 2: Define H = path\\_product hA hB : [0,1] \\<to> A \\<union> B.\<close>
  let ?H = "top1_path_product hA hB"
  have hmatch: "hA 1 = hB 0" using hhA1 hhB0 by simp
  \<comment> \<open>Step 3: H is continuous as a map [0,1] \\<to> X.\<close>
  have hI_top: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  have hA_top: "is_topology_on A (subspace_topology X TX A)"
    by (rule subspace_topology_is_topology_on[OF htop hA_sub])
  have hB_top: "is_topology_on B (subspace_topology X TX B)"
    by (rule subspace_topology_is_topology_on[OF htop hB_sub])
  have hhA_cont: "top1_continuous_map_on I_set I_top X TX hA"
  proof -
    have hcA: "top1_continuous_map_on I_set I_top A (subspace_topology X TX A) hA"
      using hhA unfolding top1_homeomorphism_on_def by (by100 blast)
    from Theorem_18_2(6)[OF hI_top hA_top htop, rule_format, of hA]
    show ?thesis using hcA hA_sub by (by100 blast)
  qed
  have hhB_cont: "top1_continuous_map_on I_set I_top X TX hB"
  proof -
    have hcB: "top1_continuous_map_on I_set I_top B (subspace_topology X TX B) hB"
      using hhB unfolding top1_homeomorphism_on_def by (by100 blast)
    from Theorem_18_2(6)[OF hI_top hB_top htop, rule_format, of hB]
    show ?thesis using hcB hB_sub by (by100 blast)
  qed
  have hH_cont: "top1_continuous_map_on I_set I_top X TX ?H"
    by (rule top1_path_product_continuous[OF htop hhA_cont hhB_cont hmatch])
  \<comment> \<open>Step 4: H maps I\\_set into A \\<union> B.\<close>
  have hH_range: "\<forall>t\<in>I_set. ?H t \<in> A \<union> B"
  proof (intro ballI)
    fix t assume "t \<in> I_set"
    show "?H t \<in> A \<union> B"
    proof (cases "t \<le> 1/2")
      case True
      have "2 * t \<in> I_set"
        using \<open>t \<in> I_set\<close> True unfolding top1_unit_interval_def by (by100 auto)
      have hA_in: "hA (2*t) \<in> A"
        using hhA \<open>2 * t \<in> I_set\<close> unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have "?H t = hA (2 * t)" unfolding top1_path_product_def using True by simp
      thus ?thesis using hA_in by simp
    next
      case False
      have "2 * t - 1 \<in> I_set"
        using \<open>t \<in> I_set\<close> False unfolding top1_unit_interval_def by (by100 auto)
      have hB_in: "hB (2*t - 1) \<in> B"
        using hhB \<open>2 * t - 1 \<in> I_set\<close> unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have "?H t = hB (2 * t - 1)" unfolding top1_path_product_def using False by simp
      thus ?thesis using hB_in by simp
    qed
  qed
  \<comment> \<open>Step 5: H is surjective onto A \\<union> B.
     Left half [0,1/2] maps onto A via hA, right half [1/2,1] maps onto B via hB.\<close>
  have hH_surj: "?H ` I_set = A \<union> B"
  proof
    show "?H ` I_set \<subseteq> A \<union> B" using hH_range by (by100 blast)
  next
    have hA_bij: "bij_betw hA I_set A" using hhA unfolding top1_homeomorphism_on_def by (by100 blast)
    have hB_bij: "bij_betw hB I_set B" using hhB unfolding top1_homeomorphism_on_def by (by100 blast)
    show "A \<union> B \<subseteq> ?H ` I_set"
    proof
      fix x assume "x \<in> A \<union> B"
      thus "x \<in> ?H ` I_set"
      proof
        assume "x \<in> A"
        then obtain t where ht: "t \<in> I_set" "hA t = x"
          using hA_bij unfolding bij_betw_def by (by100 blast)
        have "t/2 \<in> I_set" using ht(1) unfolding top1_unit_interval_def by (by100 auto)
        have "t/2 \<le> 1/2" using ht(1) unfolding top1_unit_interval_def by (by100 auto)
        have "?H (t/2) = hA (2 * (t/2))" unfolding top1_path_product_def using \<open>t/2 \<le> 1/2\<close> by simp
        hence "?H (t/2) = hA t" by simp
        hence "?H (t/2) = x" using ht(2) by simp
        thus "x \<in> ?H ` I_set" using \<open>t/2 \<in> I_set\<close> by (by100 blast)
      next
        assume "x \<in> B"
        then obtain t where ht: "t \<in> I_set" "hB t = x"
          using hB_bij unfolding bij_betw_def by (by100 blast)
        show "x \<in> ?H ` I_set"
        proof (cases "t = 0")
          case True
          \<comment> \<open>t=0: hB(0)=v=hA(1). H(1/2)=hA(1)=v=hB(0)=x.\<close>
          have "?H (1/2) = hA (2 * (1/2::real))" unfolding top1_path_product_def by simp
          hence "?H (1/2) = hA 1" by simp
          hence "?H (1/2) = v" using hhA1 by simp
          hence "?H (1/2) = x" using ht(2) True hhB0 by simp
          moreover have "(1/2::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
          ultimately show ?thesis by (by100 blast)
        next
          case False
          have "(t+1)/2 \<in> I_set" using ht(1) unfolding top1_unit_interval_def by (by100 auto)
          have "t > 0" using ht(1) False unfolding top1_unit_interval_def by (by100 auto)
          hence "\<not> ((t+1)/2 \<le> (1::real)/2)"
            by (simp add: field_simps)
          have "?H ((t+1)/2) = hB (2 * ((t+1)/2) - 1)" unfolding top1_path_product_def
            using \<open>\<not> ((t+1)/2 \<le> 1/2)\<close> by simp
          have "2 * ((t+1)/2) - 1 = (t::real)" by (simp add: field_simps)
          hence "?H ((t+1)/2) = hB t" using \<open>?H ((t+1)/2) = hB (2 * ((t+1)/2) - 1)\<close> by simp
          hence "?H ((t+1)/2) = x" using ht(2) by simp
          thus ?thesis using \<open>(t+1)/2 \<in> I_set\<close> by (by100 blast)
        qed
      qed
    qed
  qed
  \<comment> \<open>Step 6: H is injective on I\\_set.\<close>
  have hH_inj: "inj_on ?H I_set"
  proof (rule inj_onI)
    fix t1 t2 assume ht1: "t1 \<in> I_set" and ht2: "t2 \<in> I_set" and heq: "?H t1 = ?H t2"
    have hA_inj: "inj_on hA I_set" using hhA unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have hB_inj: "inj_on hB I_set" using hhB unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have hA_bij: "bij_betw hA I_set A" using hhA unfolding top1_homeomorphism_on_def by (by100 blast)
    have hB_bij: "bij_betw hB I_set B" using hhB unfolding top1_homeomorphism_on_def by (by100 blast)
    show "t1 = t2"
    proof (cases "t1 \<le> 1/2")
      case True note ht1_le = this
      show ?thesis
      proof (cases "t2 \<le> 1/2")
        case True
        \<comment> \<open>Both in left half: use hA injectivity.\<close>
        have "hA (2*t1) = hA (2*t2)"
          using heq ht1_le True unfolding top1_path_product_def by simp
        moreover have "2*t1 \<in> I_set" using ht1 ht1_le unfolding top1_unit_interval_def by (by100 auto)
        moreover have "2*t2 \<in> I_set" using ht2 True unfolding top1_unit_interval_def by (by100 auto)
        ultimately have "2*t1 = 2*t2" using inj_onD[OF hA_inj] by (by100 blast)
        thus ?thesis by linarith
      next
        case False
        \<comment> \<open>t1 in left, t2 in right: H(t1) \\<in> A, H(t2) \\<in> B\\{v}. Disjoint by A \\<inter> B = {v}.\<close>
        have h1: "?H t1 = hA (2*t1)" using ht1_le unfolding top1_path_product_def by simp
        have h2: "?H t2 = hB (2*t2-1)" using False unfolding top1_path_product_def by simp
        have "2*t1 \<in> I_set" using ht1 ht1_le unfolding top1_unit_interval_def by (by100 auto)
        have "hA (2*t1) \<in> A" using hA_bij \<open>2*t1 \<in> I_set\<close> unfolding bij_betw_def by (by100 blast)
        have "2*t2-1 \<in> I_set" using ht2 False unfolding top1_unit_interval_def by (by100 auto)
        have "hB (2*t2-1) \<in> B" using hB_bij \<open>2*t2-1 \<in> I_set\<close> unfolding bij_betw_def by (by100 blast)
        have "2*t2-1 > 0" using False ht2 unfolding top1_unit_interval_def by (by100 auto)
        hence "2*t2-1 \<noteq> 0" by linarith
        hence "hB (2*t2-1) \<noteq> v"
          using inj_onD[OF hB_inj _ _ , of "2*t2-1" 0] \<open>2*t2-1 \<in> I_set\<close> hhB0
          unfolding top1_unit_interval_def by (by100 auto)
        hence "hB (2*t2-1) \<notin> A" using hAB_inter \<open>hB (2*t2-1) \<in> B\<close> by (by100 blast)
        have "hA (2*t1) \<in> A" by (rule \<open>hA (2*t1) \<in> A\<close>)
        have "hB (2*t2-1) \<notin> A" by (rule \<open>hB (2*t2-1) \<notin> A\<close>)
        have "hA (2*t1) \<noteq> hB (2*t2-1)"
        proof
          assume "hA (2*t1) = hB (2*t2-1)"
          thus False using \<open>hA (2*t1) \<in> A\<close> \<open>hB (2*t2-1) \<notin> A\<close> by simp
        qed
        thus ?thesis using heq h1 h2 by (by100 force)
      qed
    next
      case False note ht1_gt = this
      show ?thesis
      proof (cases "t2 \<le> 1/2")
        case True
        \<comment> \<open>Symmetric to the t1 left, t2 right case.\<close>
        have h1: "?H t1 = hB (2*t1-1)" using ht1_gt unfolding top1_path_product_def by simp
        have h2: "?H t2 = hA (2*t2)" using True unfolding top1_path_product_def by simp
        have "2*t1-1 \<in> I_set" using ht1 ht1_gt unfolding top1_unit_interval_def by (by100 auto)
        have "hB (2*t1-1) \<in> B" using hB_bij \<open>2*t1-1 \<in> I_set\<close> unfolding bij_betw_def by (by100 blast)
        have "2*t1-1 > 0" using ht1_gt ht1 unfolding top1_unit_interval_def by (by100 auto)
        hence "2*t1-1 \<noteq> 0" by linarith
        hence "hB (2*t1-1) \<noteq> v"
          using inj_onD[OF hB_inj, of "2*t1-1" 0] \<open>2*t1-1 \<in> I_set\<close> hhB0
          unfolding top1_unit_interval_def by (by100 auto)
        hence "hB (2*t1-1) \<notin> A" using hAB_inter \<open>hB (2*t1-1) \<in> B\<close> by (by100 blast)
        have "2*t2 \<in> I_set" using ht2 True unfolding top1_unit_interval_def by (by100 auto)
        have "hA (2*t2) \<in> A" using hA_bij \<open>2*t2 \<in> I_set\<close> unfolding bij_betw_def by (by100 blast)
        have "hB (2*t1-1) \<noteq> hA (2*t2)"
        proof
          assume "hB (2*t1-1) = hA (2*t2)"
          thus False using \<open>hB (2*t1-1) \<notin> A\<close> \<open>hA (2*t2) \<in> A\<close> by simp
        qed
        thus ?thesis using heq h1 h2 by (by100 force)
      next
        case False
        \<comment> \<open>Both in right half: use hB injectivity.\<close>
        have "hB (2*t1-1) = hB (2*t2-1)"
          using heq ht1_gt False unfolding top1_path_product_def by simp
        moreover have "2*t1-1 \<in> I_set" using ht1 ht1_gt unfolding top1_unit_interval_def by (by100 auto)
        moreover have "2*t2-1 \<in> I_set" using ht2 False unfolding top1_unit_interval_def by (by100 auto)
        ultimately have "2*t1-1 = 2*t2-1" using inj_onD[OF hB_inj] by (by100 blast)
        thus ?thesis by linarith
      qed
    qed
  qed
  \<comment> \<open>Step 7: H is a bijection I\\_set \\<to> A \\<union> B.\<close>
  have hH_bij: "bij_betw ?H I_set (A \<union> B)"
    unfolding bij_betw_def using hH_inj hH_surj by (by100 blast)
  \<comment> \<open>Step 8: A \\<union> B with subspace topology is Hausdorff.\<close>
  have hAB_sub: "A \<union> B \<subseteq> X" using hA_sub hB_sub by (by100 blast)
  have hAB_top: "is_topology_on (A \<union> B) (subspace_topology X TX (A \<union> B))"
    by (rule subspace_topology_is_topology_on[OF htop hAB_sub])
  have hAB_haus: "is_hausdorff_on (A \<union> B) (subspace_topology X TX (A \<union> B))"
    using hhaus hAB_sub conjunct2[OF conjunct2[OF Theorem_17_11]] by (by100 blast)
  \<comment> \<open>Step 9: H is continuous I\\_set \\<to> (A \\<union> B, subspace\\_topology).\<close>
  have hH_cont_sub: "top1_continuous_map_on I_set I_top (A \<union> B) (subspace_topology X TX (A \<union> B)) ?H"
    by (rule continuous_map_restrict_codomain[OF hH_cont hH_range hAB_sub])
  \<comment> \<open>Step 10: Apply Theorem 26.6 (compact-to-Hausdorff bijection is homeomorphism).\<close>
  have hI_top: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  have hI_compact: "top1_compact_on I_set I_top"
    unfolding top1_unit_interval_def top1_unit_interval_topology_def
    using Theorem_27_1[of "0::real" 1] by (by100 simp)
  from Theorem_26_6[OF hI_top hAB_top hI_compact hAB_haus hH_cont_sub hH_bij]
  have "top1_homeomorphism_on I_set I_top (A \<union> B) (subspace_topology X TX (A \<union> B)) ?H" .
  have hAB_strict: "is_topology_on_strict (A \<union> B) (subspace_topology X TX (A \<union> B))"
  proof -
    have "\<forall>U\<in>subspace_topology X TX (A \<union> B). U \<subseteq> A \<union> B"
      unfolding subspace_topology_def by (by100 blast)
    thus ?thesis using hAB_top unfolding is_topology_on_strict_def by (by100 blast)
  qed
  have hAB_arc: "top1_is_arc_on (A \<union> B) (subspace_topology X TX (A \<union> B))"
    unfolding top1_is_arc_on_def using hAB_strict
    \<open>top1_homeomorphism_on I_set I_top (A \<union> B) (subspace_topology X TX (A \<union> B)) ?H\<close>
    by (by100 blast)
  \<comment> \<open>Step 11: Endpoints of A \\<union> B are {a, b}.\<close>
  have hep_AB: "top1_arc_endpoints_on (A \<union> B) (subspace_topology X TX (A \<union> B)) = {a, b}"
  proof -
    from arc_endpoints_are_boundary[OF hstrict hhaus hAB_sub hAB_arc
        \<open>top1_homeomorphism_on I_set I_top (A \<union> B) (subspace_topology X TX (A \<union> B)) ?H\<close>]
    have "top1_arc_endpoints_on (A \<union> B) (subspace_topology X TX (A \<union> B)) = {?H 0, ?H 1}" .
    moreover have "?H 0 = a"
      unfolding top1_path_product_def using hhA0 by simp
    moreover have "?H 1 = b"
      unfolding top1_path_product_def using hhB1 by simp
    ultimately show ?thesis by simp
  qed
  show ?thesis using hAB_arc hep_AB by (by100 blast)
qed

\<comment> \<open>A cycle of \\<ge> 2 arcs with consecutive sharing 1 vertex forms a simple closed curve.
   Uses arc\\_merge\\_at\\_endpoint iteratively on butlast ws, then arcs\\_form\\_simple\\_closed\\_curve.\<close>
lemma cycle_arcs_form_scc:
  fixes T :: "'a set" and TT :: "'a set set" and ws :: "'a set list"
  assumes "is_topology_on_strict T TT" and "is_hausdorff_on T TT"
      and "\<forall>A\<in>set ws. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)"
      and "\<forall>A\<in>set ws. \<forall>B\<in>set ws. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and "length ws \<ge> 2" and "distinct ws"
      and "\<forall>i < length ws. card (ws ! i \<inter> ws ! ((i + 1) mod length ws)) = 1"
      and "\<forall>i < length ws. \<forall>j < length ws. i \<noteq> j \<longrightarrow>
          (\<forall>v w. ws ! i \<inter> ws ! ((i + 1) mod length ws) = {v} \<longrightarrow>
                 ws ! j \<inter> ws ! ((j + 1) mod length ws) = {w} \<longrightarrow> v \<noteq> w)"
  shows "top1_simple_closed_curve_on T TT (\<Union>(set ws))"
proof -
  let ?k = "length ws"
  have hk_pos: "?k > 0" using assms(5) by linarith
  \<comment> \<open>Define shared vertices: sv i = THE unique vertex in ws!i \\<inter> ws!((i+1) mod k).\<close>
  define sv where "sv i = (THE v. ws ! i \<inter> ws ! ((i + 1) mod ?k) = {v})" for i
  have hsv_eq: "\<forall>i < ?k. ws ! i \<inter> ws ! ((i + 1) mod ?k) = {sv i}"
  proof (intro allI impI)
    fix i assume "i < ?k"
    from assms(7)[rule_format, OF this]
    have hcard: "card (ws ! i \<inter> ws ! ((i + 1) mod ?k)) = 1" .
    then obtain v where hv: "ws ! i \<inter> ws ! ((i + 1) mod ?k) = {v}" by (rule card_1_singletonE)
    hence "(THE v. ws ! i \<inter> ws ! ((i + 1) mod ?k) = {v}) = v"
      by (intro the_equality) (by100 auto)+
    thus "ws ! i \<inter> ws ! ((i + 1) mod ?k) = {sv i}" unfolding sv_def using hv by simp
  qed
  have hsv_distinct: "\<forall>i < ?k. \<forall>j < ?k. i \<noteq> j \<longrightarrow> sv i \<noteq> sv j"
  proof (intro allI impI)
    fix i j assume "i < ?k" "j < ?k" "i \<noteq> j"
    from assms(8)[rule_format, OF \<open>i < ?k\<close> \<open>j < ?k\<close> \<open>i \<noteq> j\<close>]
    show "sv i \<noteq> sv j" using hsv_eq[rule_format, OF \<open>i < ?k\<close>] hsv_eq[rule_format, OF \<open>j < ?k\<close>]
      by (by100 blast)
  qed
  \<comment> \<open>Length \\<ge> 3 (length 2 contradicts hsv\\_distinct).\<close>
  have hlen_ge3: "?k \<ge> 3"
  proof (rule ccontr)
    assume "\<not> ?k \<ge> 3"
    hence "?k = 2" using assms(5) by linarith
    hence "ws ! 0 \<inter> ws ! 1 = {sv 0}" using hsv_eq[rule_format, of 0] by simp
    moreover have "ws ! 1 \<inter> ws ! 0 = {sv 1}" using hsv_eq[rule_format, of 1] \<open>?k = 2\<close> by simp
    ultimately have "{sv 0} = {sv 1}" by (by100 blast)
    hence "sv 0 = sv 1" by simp
    from hsv_distinct[rule_format, of 0 1] show False using \<open>?k = 2\<close> \<open>sv 0 = sv 1\<close> by simp
  qed
  \<comment> \<open>Endpoints of ws!i are {sv((i-1) mod k), sv i}.\<close>
  have hep_eq: "\<forall>i < ?k. top1_arc_endpoints_on (ws ! i) (subspace_topology T TT (ws ! i))
      = {sv ((i + ?k - 1) mod ?k), sv i}"
  proof (intro allI impI)
    fix i assume "i < ?k"
    let ?ep = "top1_arc_endpoints_on (ws ! i) (subspace_topology T TT (ws ! i))"
    have hwsi: "ws ! i \<in> set ws" using \<open>i < ?k\<close> by simp
    have hwsi_A: "ws ! i \<subseteq> T \<and> top1_is_arc_on (ws ! i) (subspace_topology T TT (ws ! i))"
      using assms(3) hwsi by (by100 blast)
    \<comment> \<open>Arc has exactly 2 endpoints.\<close>
    obtain a b where hab: "a \<noteq> b" "?ep = {a, b}"
    proof -
      obtain h where hh: "top1_homeomorphism_on I_set I_top (ws ! i) (subspace_topology T TT (ws ! i)) h"
        using hwsi_A unfolding top1_is_arc_on_def by (by100 blast)
      have "?ep = {h 0, h 1}"
        by (rule arc_endpoints_are_boundary[OF assms(1) assms(2) _ _ hh]) (use hwsi_A in \<open>(by100 blast)+\<close>)
      moreover have "h 0 \<noteq> h 1"
      proof
        assume "h 0 = h 1"
        have "inj_on h I_set" using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        from inj_onD[OF this \<open>h 0 = h 1\<close>] show False unfolding top1_unit_interval_def by (by100 auto)
      qed
      ultimately show ?thesis using that by (by100 blast)
    qed
    \<comment> \<open>sv i \\<in> ep(ws!i): from hsv\\_eq, sv i is in ws!i \\<inter> ws!((i+1) mod k), hence in both.\<close>
    have "sv i \<in> ws ! i" using hsv_eq[rule_format, OF \<open>i < ?k\<close>] by (by100 blast)
    have hi1_mod: "(i+1) mod ?k < ?k" using hk_pos by simp
    have hwsi1: "ws ! ((i+1) mod ?k) \<in> set ws" using nth_mem[OF hi1_mod] .
    have hwsi_ne_i1: "ws ! i \<noteq> ws ! ((i+1) mod ?k)"
    proof -
      have "(i+1) mod ?k \<noteq> i"
      proof (cases "i + 1 < ?k")
        case True thus ?thesis by simp
      next
        case False hence "i + 1 = ?k" using \<open>i < ?k\<close> by linarith
        thus ?thesis using assms(5) by simp
      qed
      thus ?thesis using nth_eq_iff_index_eq[OF assms(6) \<open>i < ?k\<close> hi1_mod] by simp
    qed
    from assms(4)[rule_format, OF hwsi hwsi1 hwsi_ne_i1]
    have "sv i \<in> ?ep" using \<open>sv i \<in> ws ! i\<close> hsv_eq[rule_format, OF \<open>i < ?k\<close>] by (by100 blast)
    \<comment> \<open>sv((i-1) mod k) \\<in> ep(ws!i): similarly.\<close>
    have him1: "(i + ?k - 1) mod ?k < ?k" using hk_pos by simp
    have "sv ((i + ?k - 1) mod ?k) \<in> ws ! i"
    proof -
      \<comment> \<open>((i-1) mod k + 1) mod k = i.\<close>
      have hmod_eq: "((i + ?k - 1) mod ?k + 1) mod ?k = i"
      proof -
        have "((i + ?k - 1) mod ?k + 1) mod ?k = (i + ?k - 1 + 1) mod ?k"
        proof -
          have "Suc ((i + ?k - 1) mod ?k) mod ?k = Suc (i + ?k - 1) mod ?k"
            by (rule mod_Suc_eq)
          thus ?thesis by simp
        qed
        also have "i + ?k - 1 + 1 = i + ?k" using \<open>i < ?k\<close> hk_pos by linarith
        finally have "((i + ?k - 1) mod ?k + 1) mod ?k = (i + ?k) mod ?k" .
        also have "\<dots> = i" using \<open>i < ?k\<close> by simp
        finally show ?thesis .
      qed
      from hsv_eq[rule_format, OF him1]
      have "ws ! ((i + ?k - 1) mod ?k) \<inter> ws ! (((i + ?k - 1) mod ?k + 1) mod ?k)
          = {sv ((i + ?k - 1) mod ?k)}" .
      hence "ws ! ((i + ?k - 1) mod ?k) \<inter> ws ! i = {sv ((i + ?k - 1) mod ?k)}"
        using hmod_eq by simp
      thus ?thesis by (by100 blast)
    qed
    have hwsim1: "ws ! ((i + ?k - 1) mod ?k) \<in> set ws" using nth_mem[OF him1] .
    have hwsi_ne_im1: "ws ! i \<noteq> ws ! ((i + ?k - 1) mod ?k)"
    proof -
      have "i \<noteq> (i + ?k - 1) mod ?k"
      proof (cases "i = 0")
        case True thus ?thesis using assms(5) by simp
      next
        case False
        hence "(i + ?k - 1) mod ?k = i - 1"
        proof -
          have "i + ?k - 1 = ?k + (i - 1)" using False by linarith
          hence "(i + ?k - 1) mod ?k = (i - 1) mod ?k" by simp
          also have "\<dots> = i - 1" using False \<open>i < ?k\<close> by simp
          finally show ?thesis .
        qed
        thus ?thesis using False by linarith
      qed
      thus ?thesis using nth_eq_iff_index_eq[OF assms(6) \<open>i < ?k\<close> him1] by simp
    qed
    have "sv ((i + ?k - 1) mod ?k) \<in> ws ! i \<inter> ws ! ((i + ?k - 1) mod ?k)"
    proof -
      from hsv_eq[rule_format, OF him1]
      have "ws ! ((i + ?k - 1) mod ?k) \<inter> ws ! (((i + ?k - 1) mod ?k + 1) mod ?k)
          = {sv ((i + ?k - 1) mod ?k)}" .
      thus ?thesis using \<open>sv ((i + ?k - 1) mod ?k) \<in> ws ! i\<close> by (by100 blast)
    qed
    from assms(4)[rule_format, OF hwsi hwsim1 hwsi_ne_im1]
    have "ws ! i \<inter> ws ! ((i + ?k - 1) mod ?k) \<subseteq> ?ep" by (by100 blast)
    hence "sv ((i + ?k - 1) mod ?k) \<in> ?ep"
      using \<open>sv ((i + ?k - 1) mod ?k) \<in> ws ! i \<inter> ws ! ((i + ?k - 1) mod ?k)\<close> by (by100 blast)
    \<comment> \<open>They are distinct.\<close>
    have "sv ((i + ?k - 1) mod ?k) \<noteq> sv i"
    proof -
      have "(i + ?k - 1) mod ?k \<noteq> i"
      proof (cases "i = 0")
        case True thus ?thesis using assms(5) by simp
      next
        case False
        hence "(i + ?k - 1) mod ?k = i - 1"
        proof -
          have "i + ?k - 1 = ?k + (i - 1)" using False by linarith
          hence "(i + ?k - 1) mod ?k = (i - 1) mod ?k" by simp
          also have "\<dots> = i - 1" using False \<open>i < ?k\<close> by simp
          finally show ?thesis .
        qed
        thus ?thesis using False by linarith
      qed
      thus ?thesis using hsv_distinct[rule_format, OF him1 \<open>i < ?k\<close>] by (by100 blast)
    qed
    \<comment> \<open>2-element set equality.\<close>
    have "sv i \<in> {a, b}" using \<open>sv i \<in> ?ep\<close> hab(2) by simp
    have "sv ((i + ?k - 1) mod ?k) \<in> {a, b}" using \<open>sv ((i + ?k - 1) mod ?k) \<in> ?ep\<close> hab(2) by simp
    have "card {a, b} = 2" using hab(1) by simp
    have "card {sv ((i + ?k - 1) mod ?k), sv i} = 2" using \<open>sv ((i + ?k - 1) mod ?k) \<noteq> sv i\<close> by simp
    have "{sv ((i + ?k - 1) mod ?k), sv i} \<subseteq> {a, b}"
      using \<open>sv i \<in> {a, b}\<close> \<open>sv ((i + ?k - 1) mod ?k) \<in> {a, b}\<close> by (by100 blast)
    have "finite {a, b}" by simp
    from card_subset_eq[OF this \<open>{sv ((i + ?k - 1) mod ?k), sv i} \<subseteq> {a, b}\<close>]
    have "{sv ((i + ?k - 1) mod ?k), sv i} = {a, b}"
      using \<open>card {sv ((i + ?k - 1) mod ?k), sv i} = 2\<close> \<open>card {a, b} = 2\<close> by simp
    thus "?ep = {sv ((i + ?k - 1) mod ?k), sv i}" using hab(2) by simp
  qed
  \<comment> \<open>Merge butlast ws into single arc A1 by induction.\<close>
  have hmerge: "\<forall>n. 1 \<le> n \<and> n \<le> ?k - 1 \<longrightarrow>
      top1_is_arc_on (\<Union>(set (take n ws))) (subspace_topology T TT (\<Union>(set (take n ws))))
      \<and> \<Union>(set (take n ws)) \<subseteq> T
      \<and> top1_arc_endpoints_on (\<Union>(set (take n ws))) (subspace_topology T TT (\<Union>(set (take n ws))))
          = {sv (?k - 1), sv (n - 1)}"
  proof (intro allI impI, goal_cases)
    case (1 n)
    hence hn1: "1 \<le> n" and hn2: "n \<le> ?k - 1" by (by100 blast)+
    show ?case using hn1 hn2
    proof (induction n rule: nat_induct_at_least)
      case base
      have hws_ne: "ws \<noteq> []" using assms(5) by (by100 force)
      have "take 1 ws = [ws ! 0]"
        using hws_ne by (simp add: take_Suc hd_conv_nth)
      hence "\<Union>(set (take 1 ws)) = ws ! 0" by simp
      moreover have "ws ! 0 \<in> set ws" using hk_pos by simp
      moreover have "ws ! 0 \<subseteq> T" using assms(3) calculation(2) by (by100 blast)
      moreover have "top1_is_arc_on (ws ! 0) (subspace_topology T TT (ws ! 0))"
        using assms(3) calculation(2) by (by100 blast)
      moreover have "top1_arc_endpoints_on (ws ! 0) (subspace_topology T TT (ws ! 0)) = {sv (?k - 1), sv 0}"
      proof -
        from hep_eq[rule_format, OF hk_pos]
        have "top1_arc_endpoints_on (ws ! 0) (subspace_topology T TT (ws ! 0))
            = {sv ((0 + ?k - 1) mod ?k), sv 0}" by simp
        moreover have "(0 + ?k - 1) mod ?k = ?k - 1" using hk_pos by simp
        ultimately show ?thesis by simp
      qed
      ultimately show ?case by simp
    next
      case (Suc n)
      hence "n \<ge> 1" by linarith
      have "n \<le> ?k - 1" using Suc.prems by linarith
      have "Suc n \<le> ?k - 1" using Suc.prems .
      hence "Suc n < ?k" by linarith
      have "n < ?k" using \<open>n \<le> ?k - 1\<close> hk_pos by linarith
      from Suc.IH[OF \<open>n \<le> ?k - 1\<close>]
      have IH_arc: "top1_is_arc_on (\<Union>(set (take n ws))) (subspace_topology T TT (\<Union>(set (take n ws))))"
        and IH_sub: "\<Union>(set (take n ws)) \<subseteq> T"
        and IH_ep: "top1_arc_endpoints_on (\<Union>(set (take n ws))) (subspace_topology T TT (\<Union>(set (take n ws))))
            = {sv (?k - 1), sv (n - 1)}" by (by100 blast)+
      have hwsn: "ws ! n \<in> set ws" using \<open>n < ?k\<close> by simp
      have hwsn_arc: "top1_is_arc_on (ws ! n) (subspace_topology T TT (ws ! n))"
        using assms(3) hwsn by (by100 blast)
      have hwsn_sub: "ws ! n \<subseteq> T" using assms(3) hwsn by (by100 blast)
      have hwsn_ep: "top1_arc_endpoints_on (ws ! n) (subspace_topology T TT (ws ! n)) = {sv (n - 1), sv n}"
      proof -
        from hep_eq[rule_format, OF \<open>n < ?k\<close>]
        show ?thesis
        proof -
          have "(n + ?k - 1) mod ?k = n - 1"
          proof -
            have "n + ?k - 1 = ?k + (n - 1)" using \<open>n \<ge> 1\<close> by linarith
            hence "(n + ?k - 1) mod ?k = (n - 1) mod ?k" by simp
            thus ?thesis using \<open>n \<ge> 1\<close> \<open>n < ?k\<close> by simp
          qed
          thus ?thesis using hep_eq[rule_format, OF \<open>n < ?k\<close>] by simp
        qed
      qed
      \<comment> \<open>Intersection: \\<Union>(take n ws) \\<inter> ws!n = {sv(n-1)}.\<close>
      have hinter_n: "(\<Union>(set (take n ws))) \<inter> ws ! n = {sv (n - 1)}"
      proof -
        have hws_n1: "ws ! (n - 1) \<inter> ws ! n = {sv (n - 1)}"
        proof -
          have "n - 1 < ?k" using \<open>n < ?k\<close> by linarith
          from hsv_eq[rule_format, OF this]
          have "ws ! (n - 1) \<inter> ws ! ((n - 1 + 1) mod ?k) = {sv (n - 1)}" .
          moreover have "(n - 1 + 1) mod ?k = n" using \<open>n \<ge> 1\<close> \<open>n < ?k\<close> by simp
          ultimately show ?thesis by simp
        qed
        have "\<forall>j. j < n - 1 \<longrightarrow> ws ! j \<inter> ws ! n = {}"
        proof (intro allI impI)
          fix j assume "j < n - 1"
          hence "j < ?k" using \<open>n < ?k\<close> by linarith
          have "j \<noteq> n" using \<open>j < n - 1\<close> by linarith
          have "ws ! j \<noteq> ws ! n" using nth_eq_iff_index_eq[OF assms(6) \<open>j < ?k\<close> \<open>n < ?k\<close>] \<open>j \<noteq> n\<close> by simp
          from assms(4)[rule_format, OF nth_mem[OF \<open>j < ?k\<close>] hwsn this]
          have "ws ! j \<inter> ws ! n \<subseteq>
              top1_arc_endpoints_on (ws ! j) (subspace_topology T TT (ws ! j))
              \<inter> top1_arc_endpoints_on (ws ! n) (subspace_topology T TT (ws ! n))" by (by100 blast)
          also have "\<dots> = {sv ((j + ?k - 1) mod ?k), sv j} \<inter> {sv (n - 1), sv n}"
            using hep_eq[rule_format, OF \<open>j < ?k\<close>] hwsn_ep by simp
          finally have hsub: "ws ! j \<inter> ws ! n \<subseteq> {sv ((j + ?k - 1) mod ?k), sv j} \<inter> {sv (n - 1), sv n}" .
          have hjm1: "(j + ?k - 1) mod ?k = (if j = 0 then ?k - 1 else j - 1)"
          proof (cases "j = 0")
            case True thus ?thesis using hk_pos by simp
          next
            case False
            hence "j + ?k - 1 = ?k + (j - 1)" by linarith
            hence "(j + ?k - 1) mod ?k = (j - 1) mod ?k" by simp
            also have "\<dots> = j - 1" using False \<open>j < ?k\<close> by simp
            finally show ?thesis using False by simp
          qed
          have "sv ((j + ?k - 1) mod ?k) \<noteq> sv (n - 1)"
          proof -
            have "(j + ?k - 1) mod ?k \<noteq> n - 1"
            proof (cases "j = 0")
              case True hence "(j + ?k - 1) mod ?k = ?k - 1" using hjm1 by simp
              thus ?thesis using \<open>Suc n \<le> ?k - 1\<close> by linarith
            next
              case False hence "(j + ?k - 1) mod ?k = j - 1" using hjm1 by simp
              thus ?thesis using \<open>j < n - 1\<close> by linarith
            qed
            moreover have "(j + ?k - 1) mod ?k < ?k" using hk_pos by simp
            moreover have "n - 1 < ?k" using \<open>n < ?k\<close> by linarith
            ultimately show ?thesis using hsv_distinct[rule_format] by (by100 blast)
          qed
          moreover have "sv ((j + ?k - 1) mod ?k) \<noteq> sv n"
          proof -
            have "(j + ?k - 1) mod ?k \<noteq> n"
            proof (cases "j = 0")
              case True hence "(j + ?k - 1) mod ?k = ?k - 1" using hjm1 by simp
              thus ?thesis using \<open>Suc n \<le> ?k - 1\<close> by linarith
            next
              case False hence "(j + ?k - 1) mod ?k = j - 1" using hjm1 by simp
              thus ?thesis using \<open>j < n - 1\<close> by linarith
            qed
            moreover have "(j + ?k - 1) mod ?k < ?k" using hk_pos by simp
            ultimately show ?thesis using hsv_distinct[rule_format, OF _ \<open>n < ?k\<close>] by (by100 blast)
          qed
          moreover have "sv j \<noteq> sv (n - 1)"
          proof -
            have "j \<noteq> n - 1" using \<open>j < n - 1\<close> by linarith
            have "n - 1 < ?k" using \<open>n < ?k\<close> by linarith
            show ?thesis using hsv_distinct[rule_format, OF \<open>j < ?k\<close> \<open>n - 1 < ?k\<close> \<open>j \<noteq> n - 1\<close>] .
          qed
          moreover have "sv j \<noteq> sv n"
            using hsv_distinct[rule_format, OF \<open>j < ?k\<close> \<open>n < ?k\<close> \<open>j \<noteq> n\<close>] .
          ultimately have "{sv ((j + ?k - 1) mod ?k), sv j} \<inter> {sv (n - 1), sv n} = {}" by (by100 blast)
          thus "ws ! j \<inter> ws ! n = {}" using hsub by (by100 blast)
        qed
        show ?thesis
        proof
          show "\<Union>(set (take n ws)) \<inter> ws ! n \<subseteq> {sv (n - 1)}"
          proof
            fix x assume hx: "x \<in> \<Union>(set (take n ws)) \<inter> ws ! n"
            hence "x \<in> \<Union>(set (take n ws))" "x \<in> ws ! n" by (by100 blast)+
            then obtain A where "A \<in> set (take n ws)" "x \<in> A" by (by100 blast)
            then obtain j where "j < length (take n ws)" "take n ws ! j = A"
              using in_set_conv_nth by (by100 metis)
            hence "j < n" using \<open>n < ?k\<close> by (simp add: min_def)
            have "x \<in> ws ! j" using \<open>x \<in> A\<close> \<open>take n ws ! j = A\<close> \<open>j < n\<close> \<open>n < ?k\<close> by simp
            show "x \<in> {sv (n - 1)}"
            proof (cases "j = n - 1")
              case True thus ?thesis using \<open>x \<in> ws ! j\<close> \<open>x \<in> ws ! n\<close> hws_n1 by (by100 blast)
            next
              case False hence "j < n - 1" using \<open>j < n\<close> by linarith
              thus ?thesis using \<open>x \<in> ws ! j\<close> \<open>x \<in> ws ! n\<close>
                  \<open>\<forall>j. j < n - 1 \<longrightarrow> ws ! j \<inter> ws ! n = {}\<close>[rule_format, OF \<open>j < n - 1\<close>]
                by (by100 blast)
            qed
          qed
        next
          show "{sv (n - 1)} \<subseteq> \<Union>(set (take n ws)) \<inter> ws ! n"
          proof -
            have "sv (n - 1) \<in> ws ! (n - 1)" using hws_n1 by (by100 blast)
            have "ws ! (n - 1) \<in> set (take n ws)"
            proof -
              have "n - 1 < n" using \<open>n \<ge> 1\<close> by linarith
              hence "n - 1 < length (take n ws)" using \<open>n < ?k\<close> by (simp add: min_def)
              hence "take n ws ! (n - 1) \<in> set (take n ws)" using nth_mem by (by100 blast)
              moreover have "take n ws ! (n - 1) = ws ! (n - 1)"
                using \<open>n - 1 < n\<close> \<open>n < ?k\<close> by simp
              ultimately show ?thesis by simp
            qed
            hence "sv (n - 1) \<in> \<Union>(set (take n ws))" using \<open>sv (n - 1) \<in> ws ! (n - 1)\<close> by (by100 blast)
            moreover have "sv (n - 1) \<in> ws ! n" using hws_n1 by (by100 blast)
            ultimately show ?thesis by (by100 blast)
          qed
        qed
      qed
      \<comment> \<open>Apply arc\\_merge\\_at\\_endpoint.\<close>
      have hne1: "sv (?k - 1) \<noteq> sv (n - 1)"
      proof -
        have "?k - 1 \<noteq> n - 1" using \<open>Suc n \<le> ?k - 1\<close> by linarith
        moreover have "?k - 1 < ?k" using hk_pos by linarith
        moreover have "n - 1 < ?k" using \<open>n < ?k\<close> by linarith
        ultimately show ?thesis using hsv_distinct[rule_format] by (by100 blast)
      qed
      have hne2: "sv n \<noteq> sv (n - 1)"
      proof -
        have "n \<noteq> n - 1" using \<open>n \<ge> 1\<close> by linarith
        moreover have "n - 1 < ?k" using \<open>n < ?k\<close> by linarith
        ultimately show ?thesis using hsv_distinct[rule_format, OF \<open>n < ?k\<close>] by (by100 blast)
      qed
      from arc_merge_at_endpoint[OF assms(1) assms(2) IH_arc hwsn_arc IH_sub hwsn_sub
          hinter_n IH_ep hwsn_ep hne1 hne2]
      have hmerge_result: "top1_is_arc_on (\<Union>(set (take n ws)) \<union> ws ! n)
          (subspace_topology T TT (\<Union>(set (take n ws)) \<union> ws ! n))
          \<and> top1_arc_endpoints_on (\<Union>(set (take n ws)) \<union> ws ! n)
              (subspace_topology T TT (\<Union>(set (take n ws)) \<union> ws ! n)) = {sv (?k - 1), sv n}" .
      have "set (take (Suc n) ws) = set (take n ws) \<union> {ws ! n}"
        using \<open>Suc n < ?k\<close> by (simp add: take_Suc_conv_app_nth)
      hence hunion: "\<Union>(set (take (Suc n) ws)) = \<Union>(set (take n ws)) \<union> ws ! n" by (by100 blast)
      show ?case using hmerge_result hunion IH_sub hwsn_sub by simp
    qed
  qed
  \<comment> \<open>A1 = \\<Union>(set (butlast ws)) with endpoints {sv(k-1), sv(k-2)}.\<close>
  have hbt: "take (?k - 1) ws = butlast ws" using assms(5) by (simp add: butlast_conv_take)
  from hmerge[rule_format, of "?k - 1"]
  have hA1: "top1_is_arc_on (\<Union>(set (butlast ws))) (subspace_topology T TT (\<Union>(set (butlast ws))))
      \<and> \<Union>(set (butlast ws)) \<subseteq> T
      \<and> top1_arc_endpoints_on (\<Union>(set (butlast ws))) (subspace_topology T TT (\<Union>(set (butlast ws))))
          = {sv (?k - 1), sv (?k - 2)}"
    using hlen_ge3 hbt by (simp add: numeral_2_eq_2)
  \<comment> \<open>A2 = last ws, with endpoints {sv(k-2), sv(k-1)}.\<close>
  have hA2_ep: "top1_arc_endpoints_on (last ws) (subspace_topology T TT (last ws))
      = {sv (?k - 2), sv (?k - 1)}"
  proof -
    have hk1: "?k - 1 < ?k" using hk_pos by linarith
    have "last ws = ws ! (?k - 1)" using last_conv_nth[of ws] hk_pos by simp
    moreover from hep_eq[rule_format, OF hk1]
    have "top1_arc_endpoints_on (ws ! (?k - 1)) (subspace_topology T TT (ws ! (?k - 1)))
        = {sv ((?k - 1 + ?k - 1) mod ?k), sv (?k - 1)}" by simp
    moreover have "(?k - 1 + ?k - 1) mod ?k = ?k - 2"
    proof -
      have "?k - 1 + ?k - 1 = ?k + (?k - 2)" using hlen_ge3 by linarith
      hence "(?k - 1 + ?k - 1) mod ?k = (?k + (?k - 2)) mod ?k" by simp
      also have "\<dots> = (?k - 2) mod ?k" by simp
      also have "\<dots> = ?k - 2" using hlen_ge3 by simp
      finally show ?thesis .
    qed
    ultimately show ?thesis by simp
  qed
  have hws_ne: "ws \<noteq> []" using assms(5) by (by100 force)
  have hlast_in: "last ws \<in> set ws" using last_in_set[OF hws_ne] .
  have hA2_arc: "top1_is_arc_on (last ws) (subspace_topology T TT (last ws))"
    using assms(3) hlast_in by (by100 blast)
  have hA2_sub: "last ws \<subseteq> T"
    using assms(3) hlast_in by (by100 blast)
  \<comment> \<open>A1 \\<inter> A2 = {sv(k-1), sv(k-2)} (both endpoints).\<close>
  have hA1A2_inter: "\<Union>(set (butlast ws)) \<inter> last ws = {sv (?k - 1), sv (?k - 2)}"
  proof -
    have hlast_eq: "last ws = ws ! (?k - 1)" using last_conv_nth[of ws] hk_pos by simp
    \<comment> \<open>\\<Union>(set (butlast ws)) \\<inter> ws!(k-1) = \\<Union>{ws!j \\<inter> ws!(k-1) | j < k-1}.\<close>
    have hbt_set: "set (butlast ws) = {ws ! j | j. j < ?k - 1}"
    proof
      show "set (butlast ws) \<subseteq> {ws ! j |j. j < ?k - 1}"
      proof
        fix x assume "x \<in> set (butlast ws)"
        then obtain j where "j < length (butlast ws)" "butlast ws ! j = x"
          using in_set_conv_nth by (by100 metis)
        hence "j < ?k - 1" "ws ! j = x" using hk_pos by (simp_all add: nth_butlast min_def)
        thus "x \<in> {ws ! j |j. j < ?k - 1}" by (by100 blast)
      qed
    next
      show "{ws ! j |j. j < ?k - 1} \<subseteq> set (butlast ws)"
      proof
        fix x assume "x \<in> {ws ! j |j. j < ?k - 1}"
        then obtain j where "j < ?k - 1" "x = ws ! j" by (by100 blast)
        hence "j < length (butlast ws)" using hk_pos by (simp add: min_def)
        hence "butlast ws ! j \<in> set (butlast ws)" using nth_mem by (by100 blast)
        moreover have "butlast ws ! j = ws ! j" using \<open>j < ?k - 1\<close> hk_pos by (simp add: nth_butlast)
        ultimately show "x \<in> set (butlast ws)" using \<open>x = ws ! j\<close> by simp
      qed
    qed
    have "\<Union>(set (butlast ws)) \<inter> last ws = (\<Union>j < ?k - 1. ws ! j \<inter> ws ! (?k - 1))"
    proof -
      have h1: "\<Union>(set (butlast ws)) = (\<Union>j \<in> {j. j < ?k - 1}. ws ! j)"
      proof
        show "\<Union>(set (butlast ws)) \<subseteq> (\<Union>j \<in> {j. j < ?k - 1}. ws ! j)"
        proof
          fix x assume "x \<in> \<Union>(set (butlast ws))"
          then obtain A where "A \<in> set (butlast ws)" "x \<in> A" by (by100 blast)
          hence "A \<in> {ws ! j |j. j < ?k - 1}" using hbt_set by (by100 blast)
          then obtain j where "j < ?k - 1" "A = ws ! j" by (by100 blast)
          thus "x \<in> (\<Union>j \<in> {j. j < ?k - 1}. ws ! j)" using \<open>x \<in> A\<close> by (by100 blast)
        qed
      next
        show "(\<Union>j \<in> {j. j < ?k - 1}. ws ! j) \<subseteq> \<Union>(set (butlast ws))"
        proof
          fix x assume "x \<in> (\<Union>j \<in> {j. j < ?k - 1}. ws ! j)"
          then obtain j where "j < ?k - 1" "x \<in> ws ! j" by (by100 blast)
          hence "ws ! j \<in> {ws ! j |j. j < ?k - 1}" by (by100 blast)
          hence "ws ! j \<in> set (butlast ws)" using hbt_set by (by100 blast)
          thus "x \<in> \<Union>(set (butlast ws))" using \<open>x \<in> ws ! j\<close> by (by100 blast)
        qed
      qed
      show ?thesis
      proof
        show "\<Union>(set (butlast ws)) \<inter> last ws \<subseteq> (\<Union>j < ?k - 1. ws ! j \<inter> ws ! (?k - 1))"
        proof
          fix x assume "x \<in> \<Union>(set (butlast ws)) \<inter> last ws"
          hence "x \<in> \<Union>(set (butlast ws))" "x \<in> last ws" by (by100 blast)+
          from \<open>x \<in> \<Union>(set (butlast ws))\<close> h1
          obtain j where "j < ?k - 1" "x \<in> ws ! j" by (by100 blast)
          hence "x \<in> ws ! j \<inter> ws ! (?k - 1)" using \<open>x \<in> last ws\<close> hlast_eq by simp
          thus "x \<in> (\<Union>j < ?k - 1. ws ! j \<inter> ws ! (?k - 1))" using \<open>j < ?k - 1\<close> by (by100 blast)
        qed
      next
        show "(\<Union>j < ?k - 1. ws ! j \<inter> ws ! (?k - 1)) \<subseteq> \<Union>(set (butlast ws)) \<inter> last ws"
        proof
          fix x assume "x \<in> (\<Union>j < ?k - 1. ws ! j \<inter> ws ! (?k - 1))"
          then obtain j where "j < ?k - 1" "x \<in> ws ! j" "x \<in> ws ! (?k - 1)" by (by100 blast)
          have "ws ! j \<in> set (butlast ws)" using hbt_set \<open>j < ?k - 1\<close> by (by100 blast)
          hence "x \<in> \<Union>(set (butlast ws))" using \<open>x \<in> ws ! j\<close> by (by100 blast)
          thus "x \<in> \<Union>(set (butlast ws)) \<inter> last ws" using \<open>x \<in> ws ! (?k - 1)\<close> hlast_eq by simp
        qed
      qed
    qed
    also have "\<dots> = {sv (?k - 1), sv (?k - 2)}"
    proof -
      \<comment> \<open>ws!0 \\<inter> ws!(k-1) = {sv(k-1)} (from cycle structure).\<close>
      have hint_0: "ws ! 0 \<inter> ws ! (?k - 1) = {sv (?k - 1)}"
      proof -
        have "?k - 1 < ?k" using hk_pos by linarith
        from hsv_eq[rule_format, OF this]
        have "ws ! (?k - 1) \<inter> ws ! ((?k - 1 + 1) mod ?k) = {sv (?k - 1)}" .
        moreover have "(?k - 1 + 1) mod ?k = 0" using hk_pos by simp
        ultimately have "ws ! (?k - 1) \<inter> ws ! 0 = {sv (?k - 1)}" by simp
        thus ?thesis by (by100 blast)
      qed
      \<comment> \<open>ws!(k-2) \\<inter> ws!(k-1) = {sv(k-2)} (from hsv\\_eq at i=k-2).\<close>
      have hint_k2: "ws ! (?k - 2) \<inter> ws ! (?k - 1) = {sv (?k - 2)}"
      proof -
        have "?k - 2 < ?k" using hlen_ge3 by linarith
        from hsv_eq[rule_format, OF this]
        have "ws ! (?k - 2) \<inter> ws ! ((?k - 2 + 1) mod ?k) = {sv (?k - 2)}" .
        moreover have "(?k - 2 + 1) mod ?k = ?k - 1" using hlen_ge3 by simp
        ultimately show ?thesis by simp
      qed
      \<comment> \<open>For 0 < j < k-2: ws!j \\<inter> ws!(k-1) = {} (endpoints disjoint).\<close>
      have hint_mid: "\<forall>j. 0 < j \<and> j < ?k - 2 \<longrightarrow> ws ! j \<inter> ws ! (?k - 1) = {}"
      proof (intro allI impI)
        fix j assume hjp: "0 < j \<and> j < ?k - 2"
        have hj_lt: "j < ?k" using hjp by linarith
        have hk1_lt: "?k - 1 < ?k" using hk_pos by linarith
        have "ws ! j \<in> set ws" using hj_lt by simp
        have "ws ! (?k - 1) \<in> set ws" using hk1_lt by simp
        have "j \<noteq> ?k - 1" using hjp by linarith
        have "ws ! j \<noteq> ws ! (?k - 1)"
          using nth_eq_iff_index_eq[OF assms(6) hj_lt hk1_lt] \<open>j \<noteq> ?k - 1\<close> by simp
        from assms(4)[rule_format, OF \<open>ws ! j \<in> set ws\<close> \<open>ws ! (?k - 1) \<in> set ws\<close> this]
        have "ws ! j \<inter> ws ! (?k - 1) \<subseteq>
            top1_arc_endpoints_on (ws ! j) (subspace_topology T TT (ws ! j))
            \<inter> top1_arc_endpoints_on (ws ! (?k - 1)) (subspace_topology T TT (ws ! (?k - 1)))"
          by (by100 blast)
        also have "\<dots> = {sv ((j + ?k - 1) mod ?k), sv j} \<inter> {sv (?k - 2), sv (?k - 1)}"
        proof -
          have "(?k - 1 + ?k - 1) mod ?k = ?k - 2"
          proof -
            have "?k - 1 + ?k - 1 = ?k + (?k - 2)" using hlen_ge3 by linarith
            hence "(?k - 1 + ?k - 1) mod ?k = (?k - 2) mod ?k" by simp
            thus ?thesis using hlen_ge3 by simp
          qed
          thus ?thesis using hep_eq[rule_format, OF hj_lt] hep_eq[rule_format, OF hk1_lt] by simp
        qed
        finally have hsub: "ws ! j \<inter> ws ! (?k - 1) \<subseteq> {sv ((j + ?k - 1) mod ?k), sv j} \<inter> {sv (?k - 2), sv (?k - 1)}" .
        \<comment> \<open>All 4 sv indices are distinct.\<close>
        have hjm1: "(j + ?k - 1) mod ?k = j - 1"
        proof -
          have "j + ?k - 1 = ?k + (j - 1)" using hjp by linarith
          hence "(j + ?k - 1) mod ?k = (j - 1) mod ?k" by simp
          thus ?thesis using hjp hj_lt by simp
        qed
        have "sv (j - 1) \<noteq> sv (?k - 2)"
          using hsv_distinct[rule_format] hjp hj_lt hlen_ge3 by (by100 force)
        moreover have "sv (j - 1) \<noteq> sv (?k - 1)"
          using hsv_distinct[rule_format] hjp hj_lt hk1_lt by (by100 force)
        moreover have "sv j \<noteq> sv (?k - 2)"
          using hsv_distinct[rule_format] hjp hj_lt hlen_ge3 by (by100 force)
        moreover have "sv j \<noteq> sv (?k - 1)"
          using hsv_distinct[rule_format] hjp hj_lt hk1_lt by (by100 force)
        ultimately have "{sv (j - 1), sv j} \<inter> {sv (?k - 2), sv (?k - 1)} = {}" by (by100 blast)
        hence "{sv ((j + ?k - 1) mod ?k), sv j} \<inter> {sv (?k - 2), sv (?k - 1)} = {}"
          using hjm1 by simp
        thus "ws ! j \<inter> ws ! (?k - 1) = {}" using hsub by (by100 blast)
      qed
      \<comment> \<open>Combine: only j=0 and j=k-2 contribute.\<close>
      have "(\<Union>j < ?k - 1. ws ! j \<inter> ws ! (?k - 1))
          = (ws ! 0 \<inter> ws ! (?k - 1)) \<union> (ws ! (?k - 2) \<inter> ws ! (?k - 1))"
      proof -
        have "\<forall>j < ?k - 1. ws ! j \<inter> ws ! (?k - 1) \<subseteq> (ws ! 0 \<inter> ws ! (?k - 1)) \<union> (ws ! (?k - 2) \<inter> ws ! (?k - 1))"
        proof (intro allI impI)
          fix j assume "j < ?k - 1"
          show "ws ! j \<inter> ws ! (?k - 1) \<subseteq> (ws ! 0 \<inter> ws ! (?k - 1)) \<union> (ws ! (?k - 2) \<inter> ws ! (?k - 1))"
          proof (cases "j = 0")
            case True thus ?thesis by (by100 blast)
          next
            case False
            show ?thesis
            proof (cases "j = ?k - 2")
              case True thus ?thesis by (by100 blast)
            next
              case False2: False
              hence "0 < j \<and> j < ?k - 2" using False \<open>j < ?k - 1\<close> by linarith
              from hint_mid[rule_format, OF this] show ?thesis by simp
            qed
          qed
        qed
        moreover have "(ws ! 0 \<inter> ws ! (?k - 1)) \<subseteq> (\<Union>j < ?k - 1. ws ! j \<inter> ws ! (?k - 1))"
          using hlen_ge3 by (by100 force)
        moreover have "(ws ! (?k - 2) \<inter> ws ! (?k - 1)) \<subseteq> (\<Union>j < ?k - 1. ws ! j \<inter> ws ! (?k - 1))"
          using hlen_ge3 by (by100 force)
        ultimately show ?thesis by (by100 blast)
      qed
      also have "\<dots> = {sv (?k - 1)} \<union> {sv (?k - 2)}" using hint_0 hint_k2 by simp
      also have "\<dots> = {sv (?k - 1), sv (?k - 2)}" by (by100 blast)
      finally show ?thesis .
    qed
    finally show ?thesis .
  qed
  \<comment> \<open>sv(k-1) \\<noteq> sv(k-2).\<close>
  have ha_ne: "sv (?k - 1) \<noteq> sv (?k - 2)"
    using hsv_distinct[rule_format] hlen_ge3 by (by100 force)
  \<comment> \<open>A1 \\<union> A2 = \\<Union>(set ws).\<close>
  have hA1A2_union: "\<Union>(set (butlast ws)) \<union> last ws = \<Union>(set ws)"
  proof -
    have "ws = butlast ws @ [last ws]" using hws_ne by simp
    hence "set ws = set (butlast ws @ [last ws])" by simp
    also have "\<dots> = set (butlast ws) \<union> set [last ws]" by simp
    also have "\<dots> = set (butlast ws) \<union> {last ws}" by simp
    finally show ?thesis by (by100 blast)
  qed
  \<comment> \<open>Endpoint set of A1 = {sv(k-1), sv(k-2)} = A1 \\<inter> A2 endpoints.\<close>
  have hA1_arc2: "top1_is_arc_on (\<Union>(set (butlast ws))) (subspace_topology T TT (\<Union>(set (butlast ws))))"
    using hA1 by (by100 blast)
  have hA1_sub2: "\<Union>(set (butlast ws)) \<subseteq> T" using hA1 by (by100 blast)
  have hA1_ep2: "top1_arc_endpoints_on (\<Union>(set (butlast ws))) (subspace_topology T TT (\<Union>(set (butlast ws))))
      = {sv (?k - 1), sv (?k - 2)}" using hA1 by (by100 blast)
  \<comment> \<open>Normalize: A2 endpoints = {sv(k-2), sv(k-1)} = {sv(k-1), sv(k-2)} as sets.\<close>
  have hA2_ep2: "top1_arc_endpoints_on (last ws) (subspace_topology T TT (last ws))
      = {sv (?k - 1), sv (?k - 2)}" using hA2_ep by (by100 blast)
  \<comment> \<open>Apply arcs\\_form\\_simple\\_closed\\_curve.\<close>
  have "top1_simple_closed_curve_on T TT (\<Union>(set (butlast ws)) \<union> last ws)"
    by (rule arcs_form_simple_closed_curve[OF assms(1) assms(2)
        hA1_arc2 hA1_sub2 hA2_arc hA2_sub hA1A2_inter ha_ne hA1_ep2 hA2_ep2])
  thus ?thesis using hA1A2_union by simp
qed

\<comment> \<open>Combinatorial acyclicity transfer: SC graph \\<Rightarrow> no cycle of distinct arcs.
   A "cycle" here means a sequence of \\<ge> 2 distinct arcs A1, ..., Ak such that
   consecutive arcs share exactly 1 vertex, and the sequence forms a closed path.
   This is the topological bridge: it connects SC (topological) to acyclicity (combinatorial).
   From Munkres Theorem 84.7: pi1 of graph is free on non-tree arcs; CREP gives non-trivial element.\<close>
lemma sc_graph_no_cycle:
  fixes T :: "'a set" and TT :: "'a set set" and \<A> :: "'a set set"
  assumes "top1_is_tree_on T TT"
      and "\<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)"
      and "\<Union>\<A> = T"
      and "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and "finite \<A>"
      and "\<forall>C. C \<subseteq> T \<longrightarrow> (closedin_on T TT C \<longleftrightarrow>
          (\<forall>A\<in>\<A>. closedin_on A (subspace_topology T TT A) (A \<inter> C)))"
      \<comment> \<open>"Cycle": \\<ge> 2 distinct arcs, consecutive share exactly 1 vertex, shared vertices all distinct.\<close>
      and "length ws \<ge> 2"
      and "distinct ws" and "set ws \<subseteq> \<A>"
      \<comment> \<open>Consecutive arcs share exactly 1 vertex.\<close>
      and hcard1: "\<forall>i < length ws. card (ws ! i \<inter> ws ! ((i + 1) mod length ws)) = 1"
      \<comment> \<open>The shared vertices are pairwise distinct (simple polygon, not star graph).\<close>
      and hdist_v: "\<forall>i < length ws. \<forall>j < length ws. i \<noteq> j \<longrightarrow>
          (\<forall>v w. ws ! i \<inter> ws ! ((i + 1) mod length ws) = {v} \<longrightarrow>
                 ws ! j \<inter> ws ! ((j + 1) mod length ws) = {w} \<longrightarrow> v \<noteq> w)"
  shows False
proof -
  \<comment> \<open>Strategy: The cycle C = \\<Union>(set ws) is homeomorphic to S1 (a simple closed curve).
     C is a retract of T (collapse non-cycle arcs to cycle vertices using coherent topology).
     Apply scc\\_in\\_sc\\_false: SC + SCC retract \\<Rightarrow> False.

     Proof by induction on card(\\<A>) - length(ws) (number of non-cycle arcs).
     Base (card = length): T = C. Identity retraction. SCC construction.
     Step: Find a "leaf" non-cycle arc (pendant arc not in cycle).
           Remove it (leaf removal preserves SC).
           Apply IH to the smaller graph.\<close>
  have hSC: "top1_simply_connected_on T TT"
    using assms(1) unfolding top1_is_tree_on_def by (by100 blast)
  have hgraph: "top1_is_graph_on T TT"
    using assms(1) unfolding top1_is_tree_on_def by (by100 blast)
  have hconn: "top1_connected_on T TT"
    using assms(1) unfolding top1_is_tree_on_def by (by100 blast)
  have htop: "is_topology_on T TT"
    using hgraph unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
  have hhaus: "is_hausdorff_on T TT"
    using hgraph unfolding top1_is_graph_on_def by (by100 blast)
  have hstrict: "is_topology_on_strict T TT"
    using hgraph unfolding top1_is_graph_on_def by (by100 blast)
  \<comment> \<open>The cycle subgraph C = \\<Union>(set ws) is a simple closed curve (homeomorphic to S1).
     This follows from the path product construction: concatenate k arc homeomorphisms
     around the cycle, then identify endpoints to get S1 \\<to> C.\<close>
  let ?C = "\<Union>(set ws)"
  have hC_sub: "?C \<subseteq> T"
  proof -
    have "\<forall>A\<in>set ws. A \<subseteq> T" using assms(2) assms(9) by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  have hC_SCC: "top1_simple_closed_curve_on T TT ?C"
  proof -
    have harcs_ws: "\<forall>A\<in>set ws. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)"
      using assms(2) assms(9) by (by100 blast)
    have hinter_ws: "\<forall>A\<in>set ws. \<forall>B\<in>set ws. A \<noteq> B \<longrightarrow>
         A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
       \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
       \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      using assms(4) assms(9) by (by100 blast)
    show ?thesis by (rule cycle_arcs_form_scc[OF hstrict hhaus harcs_ws hinter_ws
        assms(7) assms(8) hcard1 hdist_v])
  qed
  \<comment> \<open>C is a retract of T. Collapse non-cycle arcs to cycle vertices.\<close>
  have hC_retract: "top1_retract_of_on T TT ?C"
  proof -
    have "set ws \<noteq> {}" using assms(7) by (by100 force)
    have hws_pc: "top1_path_connected_on ?C (subspace_topology T TT ?C)"
    proof -
      \<comment> \<open>C is the image of S1 under the SCC homeomorphism. S1 is pc. Continuous image of pc = pc.\<close>
      from hC_SCC obtain f where hf: "top1_continuous_map_on top1_S1 top1_S1_topology T TT f"
          "inj_on f top1_S1" "f ` top1_S1 = ?C"
        unfolding top1_simple_closed_curve_on_def by (by100 blast)
      have "\<forall>x \<in> top1_S1. f x \<in> T"
        using hf(1) unfolding top1_continuous_map_on_def by (by100 blast)
      have "subspace_topology T TT ?C = subspace_topology T TT ?C" by simp
      show ?thesis
        by (rule top1_path_connected_continuous_image[OF S1_path_connected hf(1)
            \<open>\<forall>x \<in> top1_S1. f x \<in> T\<close> hf(3) hC_sub
            \<open>subspace_topology T TT ?C = subspace_topology T TT ?C\<close> htop])
    qed
    show ?thesis by (rule graph_cycle_retract[OF assms(1-6) assms(9) \<open>set ws \<noteq> {}\<close> hws_pc])
  qed
  \<comment> \<open>Apply scc\\_in\\_sc\\_false.\<close>
  from scc_in_sc_false[OF hSC htop hhaus hC_SCC hC_retract hC_sub]
  show False .
qed

\<comment> \<open>Leaf existence in acyclic graphs: some vertex has degree \\<le> 1.
   Extracted from forest\\_euler\\_formula's walk argument for reuse in induction.\<close>
lemma acyclic_graph_has_leaf:
  fixes \<A> :: "'a set set"
  assumes "\<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)"
      and "\<Union>\<A> = T"
      and "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 1"
      and "finite \<A>"
      and "is_topology_on_strict T TT"
      and "is_hausdorff_on T TT"
      and "\<forall>ws. length ws \<ge> 2 \<longrightarrow> distinct ws \<longrightarrow> set ws \<subseteq> \<A> \<longrightarrow>
          (\<forall>i < length ws. card (ws ! i \<inter> ws ! ((i + 1) mod length ws)) = 1) \<longrightarrow> False"
      and "\<A> \<noteq> {}"
  shows "\<exists>v\<in>top1_graph_vertex_set T TT \<A>.
      card {A \<in> \<A>. v \<in> top1_arc_endpoints_on A (subspace_topology T TT A)} \<le> 1"
proof -
  note harcs = assms(1) note hcover = assms(2) note hinter = assms(3)
  note hfin = assms(4) note hstrict = assms(5) note hhaus = assms(6)
  note hacyclic = assms(7) note hne = assms(8)
  let ?V = "top1_graph_vertex_set T TT \<A>"
  let ?ep = "\<lambda>A. top1_arc_endpoints_on A (subspace_topology T TT A)"
  \<comment> \<open>Each arc has exactly 2 endpoints.\<close>
  have h2ep: "\<forall>A0\<in>\<A>. \<exists>a0 b0. a0 \<noteq> b0 \<and> ?ep A0 = {a0, b0}"
  proof (intro ballI)
    fix A0 assume "A0 \<in> \<A>"
    have "A0 \<subseteq> T" "top1_is_arc_on A0 (subspace_topology T TT A0)"
      using harcs \<open>A0 \<in> \<A>\<close> by (by100 blast)+
    then obtain h where hh: "top1_homeomorphism_on I_set I_top A0 (subspace_topology T TT A0) h"
      unfolding top1_is_arc_on_def by (by100 blast)
    have "?ep A0 = {h 0, h 1}"
      by (rule arc_endpoints_are_boundary[OF hstrict hhaus \<open>A0 \<subseteq> T\<close> \<open>top1_is_arc_on A0 _\<close> hh])
    moreover have "h 0 \<noteq> h 1"
    proof
      assume "h 0 = h 1"
      have "inj_on h I_set" using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      from inj_onD[OF this \<open>h 0 = h 1\<close>] show False unfolding top1_unit_interval_def by (by100 auto)
    qed
    ultimately show "\<exists>a0 b0. a0 \<noteq> b0 \<and> ?ep A0 = {a0, b0}" by (by100 blast)
  qed
  have hep_fin: "\<forall>A0\<in>\<A>. finite (?ep A0)" using h2ep by (by100 force)
  have hV_fin: "finite ?V" unfolding top1_graph_vertex_set_def using hfin hep_fin by (by100 blast)
  have hep_card: "\<forall>A0\<in>\<A>. card (?ep A0) = 2"
  proof (intro ballI)
    fix A0 assume "A0 \<in> \<A>"
    from h2ep[rule_format, OF this] obtain a0 b0 where "a0 \<noteq> b0" "?ep A0 = {a0, b0}" by (by100 blast)
    thus "card (?ep A0) = 2" using \<open>a0 \<noteq> b0\<close> by (by100 simp)
  qed
  \<comment> \<open>Use double counting: sum of endpoint cardinalities = 2 * card(\\<A>).\<close>
  have "?V = (\<Union>A\<in>\<A>. ?ep A)" unfolding top1_graph_vertex_set_def by (by100 blast)
  have hsum: "(\<Sum>v\<in>?V. card {A \<in> \<A>. v \<in> ?ep A}) = 2 * card \<A>"
  proof -
    from double_counting_sum[OF hfin hep_fin \<open>?V = (\<Union>A\<in>\<A>. ?ep A)\<close>]
    have "(\<Sum>v\<in>?V. card {A \<in> \<A>. v \<in> ?ep A}) = (\<Sum>A\<in>\<A>. card (?ep A))" .
    also have "\<dots> = (\<Sum>A\<in>\<A>. 2)" using hep_card by simp
    also have "\<dots> = 2 * card \<A>" by simp
    finally show ?thesis .
  qed
  \<comment> \<open>Key: every vertex has degree \\<ge> 1 (it is an endpoint of some arc).\<close>
  have hdeg_pos: "\<forall>v\<in>?V. card {A \<in> \<A>. v \<in> ?ep A} \<ge> 1"
  proof (intro ballI)
    fix v assume "v \<in> ?V"
    then obtain A0 where "A0 \<in> \<A>" "v \<in> ?ep A0"
      unfolding top1_graph_vertex_set_def by (by100 blast)
    hence "{A0} \<subseteq> {A \<in> \<A>. v \<in> ?ep A}" by (by100 blast)
    moreover have hfin_deg: "finite {A \<in> \<A>. v \<in> ?ep A}" using hfin by (by100 simp)
    ultimately have "card {A0} \<le> card {A \<in> \<A>. v \<in> ?ep A}"
      using card_mono by (by100 blast)
    thus "card {A \<in> \<A>. v \<in> ?ep A} \<ge> 1" by simp
  qed
  \<comment> \<open>Sum of degrees \\<ge> V (each degree \\<ge> 1). Combined with sum = 2E:
     2E \\<ge> V, so E \\<ge> V/2. But we want V \\<ge> E+1.
     This doesn't directly give what we want. Need stronger argument using acyclicity.
     Use: acyclic \\<Rightarrow> at most V-1 arcs. Proof: induction on E, bridge removal.\<close>
  \<comment> \<open>Direct proof: acyclic \\<Rightarrow> card(\\<A>) \\<le> card(?V) - 1.
     By contradiction: if card(\\<A>) \\<ge> card(?V), then by pigeonhole, some vertex has degree \\<ge> 2.
     Actually this doesn't immediately help. Use the bridge argument instead.\<close>
  \<comment> \<open>First show: acyclic \\<Rightarrow> some vertex has degree \\<le> 1 (i.e., a leaf exists).
     Proof: if no leaf (all degrees \\<ge> 2), construct walk. Walk never revisits vertex
     (revisiting would create cycle, contradicting acyclicity). Finite \\<Rightarrow> walk must stop.
     But degree \\<ge> 2 means walk never stops. Contradiction.\<close>
  have "\<exists>v\<in>?V. card {A \<in> \<A>. v \<in> ?ep A} \<le> 1"
  proof (rule ccontr)
    assume "\<not> (\<exists>v\<in>?V. card {A \<in> \<A>. v \<in> ?ep A} \<le> 1)"
    hence hdeg_ge2: "\<forall>v\<in>?V. card {A \<in> \<A>. v \<in> ?ep A} \<ge> 2" by (by100 force)
    \<comment> \<open>Degree sum = 2E \\<ge> 2V, so E \\<ge> V.\<close>
    have "2 * card \<A> \<ge> 2 * card ?V"
    proof -
      have "(\<Sum>v\<in>?V. card {A \<in> \<A>. v \<in> ?ep A}) \<ge> (\<Sum>v\<in>?V. 2)"
        by (rule sum_mono) (use hdeg_ge2 in auto)
      thus ?thesis using hsum by simp
    qed
    hence "card \<A> \<ge> card ?V" by linarith
    \<comment> \<open>But acyclic + connected: V \\<ge> E + 1 (proved below via leaf induction from IH or directly).
       Actually, we derive the contradiction differently:
       all degrees \\<ge> 2 + sum = 2E gives 2E \\<ge> 2V, so E \\<ge> V.
       But V \\<ge> 1 (from hne). And each arc adds at most 2 new vertices.
       With E arcs and at most 2E vertex-slots: V \\<le> 2E.
       From E \\<ge> V: V \\<le> 2V, which is always true. No contradiction yet.

       The contradiction comes from the walk argument:
       all degrees \\<ge> 2 + acyclic + finite \\<Rightarrow> False.
       Walk visits distinct vertices (acyclic prevents revisits).
       Finite \\<Rightarrow> walk must terminate. But degree \\<ge> 2 \\<Rightarrow> walk never terminates.
       This is a pigeonhole argument on the vertex set.\<close>
    \<comment> \<open>Walk construction: define walk\\_v :: nat \\<Rightarrow> 'a (vertex at step n)
       and walk\\_e :: nat \\<Rightarrow> 'a set (arc at step n).
       At each step: pick an arc \\<noteq> previous arc containing current vertex.
       The vertices walk\\_v 0, walk\\_v 1, ... are all distinct (acyclicity).
       After card(V) steps: no more new vertices. But walk continues. Contradiction.\<close>
    \<comment> \<open>Define the non-backtracking walk. At each step, choose an arc different from the previous one.
       walk\\_state :: nat \\<Rightarrow> 'a \\<times> 'a set gives (current vertex, last arc used).\<close>
    obtain v0 where hv0: "v0 \<in> ?V"
    proof -
      obtain A0 where "A0 \<in> \<A>" using hne by (by100 blast)
      from h2ep[rule_format, OF this]
      obtain a0 b0 where "?ep A0 = {a0, b0}" by (by100 blast)
      hence "a0 \<in> ?V" unfolding top1_graph_vertex_set_def using \<open>A0 \<in> \<A>\<close> by (by100 blast)
      thus ?thesis using that by (by100 blast)
    qed
    obtain e0 where he0: "e0 \<in> \<A>" "v0 \<in> ?ep e0"
    proof -
      from hv0 obtain A0 where "A0 \<in> \<A>" "v0 \<in> ?ep A0"
        unfolding top1_graph_vertex_set_def by (by100 blast)
      thus ?thesis using that by (by100 blast)
    qed
    \<comment> \<open>Step function: given (v, e\\_prev), find next arc e' \\<noteq> e\\_prev with v \\<in> ep(e'),
       then v' = the other endpoint of e'.\<close>
    define next_arc :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
      "next_arc v e_prev = (SOME e'. e' \<in> \<A> \<and> v \<in> ?ep e' \<and> e' \<noteq> e_prev)" for v e_prev
    define other_ep :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a" where
      "other_ep v e = (SOME v'. v' \<in> ?ep e \<and> v' \<noteq> v)" for v e
    define walk_state :: "nat \<Rightarrow> 'a \<times> 'a set" where
      "walk_state = rec_nat (other_ep v0 e0, e0)
        (\<lambda>n (v, e). let e' = next_arc v e in (other_ep v e', e'))"
    let ?wv = "\<lambda>n. fst (walk_state n)"
    let ?we = "\<lambda>n. snd (walk_state n)"
    \<comment> \<open>Properties of the walk (each requires proof):
       1. ?wv n \\<in> V for all n.
       2. ?we n \\<in> \\<A> for all n.
       3. ?wv n \\<noteq> ?wv m for n \\<noteq> m (injectivity, from acyclicity).
       4. After card V steps: injective function on {0..card V} into V. Pigeonhole \\<Rightarrow> False.\<close>
    \<comment> \<open>Step 1: SOME properties for next\\_arc and other\\_ep.\<close>
    have hnext: "\<forall>v\<in>?V. \<forall>e\<in>\<A>. v \<in> ?ep e \<longrightarrow>
        next_arc v e \<in> \<A> \<and> v \<in> ?ep (next_arc v e) \<and> next_arc v e \<noteq> e"
    proof (intro ballI impI)
      fix v e assume "v \<in> ?V" "e \<in> \<A>" "v \<in> ?ep e"
      from hdeg_ge2[rule_format, OF \<open>v \<in> ?V\<close>]
      have "card {A \<in> \<A>. v \<in> ?ep A} \<ge> 2" .
      hence "\<exists>e'\<in>\<A>. e' \<noteq> e \<and> v \<in> ?ep e'"
      proof -
        have he_in: "e \<in> {A \<in> \<A>. v \<in> ?ep A}" using \<open>e \<in> \<A>\<close> \<open>v \<in> ?ep e\<close> by (by100 blast)
        have hfin_deg: "finite {A \<in> \<A>. v \<in> ?ep A}" using hfin by (by100 simp)
        from \<open>card {A \<in> \<A>. v \<in> ?ep A} \<ge> 2\<close>
        have "{A \<in> \<A>. v \<in> ?ep A} \<noteq> {e}"
        proof -
          have "card {e} = 1" by simp
          thus ?thesis using \<open>card {A \<in> \<A>. v \<in> ?ep A} \<ge> 2\<close> by (by100 force)
        qed
        then obtain e' where "e' \<in> {A \<in> \<A>. v \<in> ?ep A}" "e' \<noteq> e"
          using he_in by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      hence "\<exists>e'. e' \<in> \<A> \<and> v \<in> ?ep e' \<and> e' \<noteq> e" by (by100 blast)
      from someI_ex[OF this]
      show "next_arc v e \<in> \<A> \<and> v \<in> ?ep (next_arc v e) \<and> next_arc v e \<noteq> e"
        unfolding next_arc_def by (by100 blast)
    qed
    have hother: "\<forall>v. \<forall>e\<in>\<A>. v \<in> ?ep e \<longrightarrow> other_ep v e \<in> ?ep e \<and> other_ep v e \<noteq> v"
    proof (intro allI ballI impI)
      fix v e assume "e \<in> \<A>" "v \<in> ?ep e"
      from h2ep[rule_format, OF \<open>e \<in> \<A>\<close>]
      obtain a b where hab: "a \<noteq> b" "?ep e = {a, b}" by (by100 blast)
      hence "\<exists>v'. v' \<in> ?ep e \<and> v' \<noteq> v" using \<open>v \<in> ?ep e\<close> by (by100 blast)
      from someI_ex[OF this]
      show "other_ep v e \<in> ?ep e \<and> other_ep v e \<noteq> v"
        unfolding other_ep_def by (by100 blast)
    qed
    \<comment> \<open>Step 2: Walk invariant by induction.\<close>
    have hwalk_suc_fst: "\<And>n. ?wv (Suc n) = other_ep (?wv n) (next_arc (?wv n) (?we n))"
      unfolding walk_state_def by (simp add: case_prod_beta Let_def)
    have hwalk_suc_snd: "\<And>n. ?we (Suc n) = next_arc (?wv n) (?we n)"
      unfolding walk_state_def by (simp add: case_prod_beta Let_def)
    have hwalk_props: "\<And>n. ?wv n \<in> ?V \<and> ?we n \<in> \<A> \<and> ?wv n \<in> ?ep (?we n)"
    proof -
      fix n show "?wv n \<in> ?V \<and> ?we n \<in> \<A> \<and> ?wv n \<in> ?ep (?we n)"
      proof (induction n)
        case 0
        have "walk_state 0 = (other_ep v0 e0, e0)" unfolding walk_state_def by simp
        hence h0v: "?wv 0 = other_ep v0 e0" and h0e: "?we 0 = e0" by simp_all
        from hother[rule_format, OF he0(1) he0(2)]
        have "other_ep v0 e0 \<in> ?ep e0" "other_ep v0 e0 \<noteq> v0" by (by100 blast)+
        hence "?wv 0 \<in> ?ep e0" using h0v by simp
        moreover have "?wv 0 \<in> ?V" unfolding top1_graph_vertex_set_def
          using \<open>?wv 0 \<in> ?ep e0\<close> he0(1) by (by100 blast)
        ultimately show ?case using h0e he0(1) by (by100 blast)
      next
        case (Suc n)
        from Suc.IH have hv: "?wv n \<in> ?V" and he: "?we n \<in> \<A>" and hve: "?wv n \<in> ?ep (?we n)"
          by (by100 blast)+
        let ?e' = "next_arc (?wv n) (?we n)"
        from hnext[rule_format, OF hv he hve]
        have he': "?e' \<in> \<A>" and hve': "?wv n \<in> ?ep ?e'" by (by100 blast)+
        from hother[rule_format, OF he' hve']
        have hv': "other_ep (?wv n) ?e' \<in> ?ep ?e'" by (by100 blast)
        have hsuc_fst: "?wv (Suc n) = other_ep (?wv n) ?e'" using hwalk_suc_fst by simp
        have hsuc_snd: "?we (Suc n) = ?e'" using hwalk_suc_snd by simp
        have "?wv (Suc n) \<in> ?V"
        proof -
          have "other_ep (?wv n) ?e' \<in> ?ep ?e'" using hv' .
          hence "other_ep (?wv n) ?e' \<in> (\<Union>A\<in>\<A>. ?ep A)" using he' by (by100 blast)
          thus ?thesis using hsuc_fst unfolding top1_graph_vertex_set_def by simp
        qed
        moreover have "?we (Suc n) \<in> \<A>" using hsuc_snd he' by simp
        moreover have "?wv (Suc n) \<in> ?ep (?we (Suc n))"
          using hsuc_fst hsuc_snd hv' by simp
        ultimately show ?case by (by100 blast)
      qed
    qed
    \<comment> \<open>Step 3: Pigeonhole — vertex repeats after card(V)+1 steps.\<close>
    have "\<exists>i j. i < j \<and> j \<le> card ?V \<and> ?wv i = ?wv j"
    proof (rule ccontr)
      assume "\<not> (\<exists>i j. i < j \<and> j \<le> card ?V \<and> ?wv i = ?wv j)"
      hence hinj: "\<forall>i j. i \<le> card ?V \<longrightarrow> j \<le> card ?V \<longrightarrow> i \<noteq> j \<longrightarrow> ?wv i \<noteq> ?wv j"
      proof (intro allI impI)
        fix i j assume "i \<le> card ?V" "j \<le> card ?V" "i \<noteq> j"
        show "?wv i \<noteq> ?wv j"
        proof (cases "i < j")
          case True thus ?thesis using \<open>\<not> (\<exists>i j. i < j \<and> j \<le> card ?V \<and> ?wv i = ?wv j)\<close> \<open>j \<le> card ?V\<close>
            by (by100 blast)
        next
          case False hence "j < i" using \<open>i \<noteq> j\<close> by linarith
          show ?thesis
          proof
            assume "?wv i = ?wv j"
            hence "?wv j = ?wv i" by simp
            with \<open>j < i\<close> \<open>i \<le> card ?V\<close> have "\<exists>i j. i < j \<and> j \<le> card ?V \<and> ?wv i = ?wv j"
              by (by100 blast)
            with \<open>\<not> (\<exists>i j. i < j \<and> j \<le> card ?V \<and> ?wv i = ?wv j)\<close> show False by (by100 blast)
          qed
        qed
      qed
      have "inj_on ?wv {..card ?V}"
        unfolding inj_on_def using hinj by (by100 blast)
      moreover have "?wv ` {..card ?V} \<subseteq> ?V"
      proof (intro image_subsetI)
        fix n assume "n \<in> {..card ?V}"
        thus "?wv n \<in> ?V" using hwalk_props by (by100 blast)
      qed
      moreover have "card {..card ?V} = card ?V + 1" by simp
      ultimately have "card ?V + 1 \<le> card ?V"
        using card_inj_on_le[OF \<open>inj_on _ _\<close> \<open>_ ` _ \<subseteq> ?V\<close> hV_fin] by linarith
      thus False by linarith
    qed
    then obtain i j where hij: "i < j" "j \<le> card ?V" "?wv i = ?wv j" by (by100 blast)
    \<comment> \<open>Step 4: Extract cycle arcs and derive False via hacyclic.\<close>
    \<comment> \<open>The arcs ?we(Suc i), ..., ?we(j) form a cycle of \\<ge> 2 arcs
       with consecutive sharing 1 vertex. hacyclic gives False.\<close>
    \<comment> \<open>Take minimum revisit distance.\<close>
    define dmin where "dmin = (LEAST d. \<exists>i' j'. i' < j' \<and> j' \<le> card ?V \<and> ?wv i' = ?wv j' \<and> j' - i' = d)"
    \<comment> \<open>Use LEAST to find minimum revisit distance.\<close>
    have "\<exists>d. \<exists>i' j'. i' < j' \<and> j' \<le> card ?V \<and> ?wv i' = ?wv j' \<and> j' - i' = d"
      using hij by (by100 blast)
    then obtain d0 where "d0 = dmin" and hd0: "\<exists>i' j'. i' < j' \<and> j' \<le> card ?V \<and> ?wv i' = ?wv j' \<and> j' - i' = dmin"
    proof -
      let ?P = "\<lambda>d. \<exists>i' j'. i' < j' \<and> j' \<le> card ?V \<and> ?wv i' = ?wv j' \<and> j' - i' = d"
      have "?P (j - i)" using hij by (by100 blast)
      from LeastI_ex[of ?P] \<open>\<exists>d. ?P d\<close>
      have "?P (LEAST d. ?P d)" by (by100 blast)
      hence "?P dmin" unfolding dmin_def .
      thus ?thesis using that by simp
    qed
    from hd0 obtain i0 j0 where hij0: "i0 < j0" "j0 \<le> card ?V" "?wv i0 = ?wv j0" "j0 - i0 = dmin"
      by (by100 blast)
    have hmin: "\<forall>i' j'. i' < j' \<and> j' \<le> card ?V \<and> ?wv i' = ?wv j' \<longrightarrow> dmin \<le> j' - i'"
    proof (intro allI impI)
      fix i' j' assume h: "i' < j' \<and> j' \<le> card ?V \<and> ?wv i' = ?wv j'"
      let ?P = "\<lambda>d. \<exists>i' j'. i' < j' \<and> j' \<le> card ?V \<and> ?wv i' = ?wv j' \<and> j' - i' = d"
      have "?P (j' - i')" using h by (by100 blast)
      hence "dmin \<le> j' - i'" unfolding dmin_def by (rule Least_le)
      thus "dmin \<le> j' - i'" .
    qed
    \<comment> \<open>j0 - i0 \\<ge> 2 (walk never backtracks to same vertex in 1 step).\<close>
    have hdmin_ge2: "dmin \<ge> 2"
    proof -
      have "?wv (Suc i0) \<noteq> ?wv i0"
      proof -
        let ?e' = "next_arc (?wv i0) (?we i0)"
        have "?wv (Suc i0) = other_ep (?wv i0) ?e'" using hwalk_suc_fst by simp
        moreover have "?e' \<in> \<A>" and "?wv i0 \<in> ?ep ?e'"
          using hnext hwalk_props by (by100 blast)+
        moreover have "other_ep (?wv i0) ?e' \<noteq> ?wv i0"
          using hother \<open>?e' \<in> \<A>\<close> \<open>?wv i0 \<in> ?ep ?e'\<close> by (by100 blast)
        ultimately show ?thesis by simp
      qed
      hence "Suc i0 \<noteq> j0" using hij0(3) by (by100 force)
      thus ?thesis using hij0(1) hij0(4) by linarith
    qed
    \<comment> \<open>Extract cycle arcs.\<close>
    let ?ws = "map (\<lambda>k. ?we (Suc i0 + k)) [0..<dmin]"
    have hws_len: "length ?ws = dmin" by simp
    have hws_ge2: "length ?ws \<ge> 2" using hdmin_ge2 by simp
    have hws_sub: "set ?ws \<subseteq> \<A>"
    proof -
      have "\<forall>k < dmin. ?we (Suc i0 + k) \<in> \<A>" using hwalk_props by (by100 blast)
      thus ?thesis by (by100 auto)
    qed
    \<comment> \<open>Consecutive arcs share a vertex from the walk structure.\<close>
    have hwalk_shared: "\<forall>k. ?wv k \<in> ?we k \<and> ?wv k \<in> ?we (Suc k)"
    proof
      fix k
      have "?wv k \<in> ?ep (?we k)" using hwalk_props by (by100 blast)
      hence h1: "?wv k \<in> ?we k" unfolding top1_arc_endpoints_on_def by (by100 blast)
      have "?we (Suc k) = next_arc (?wv k) (?we k)" using hwalk_suc_snd .
      moreover have "?wv k \<in> ?ep (next_arc (?wv k) (?we k))"
        using hnext hwalk_props by (by100 blast)
      hence "?wv k \<in> next_arc (?wv k) (?we k)"
        unfolding top1_arc_endpoints_on_def by (by100 blast)
      ultimately have h2: "?wv k \<in> ?we (Suc k)" by simp
      show "?wv k \<in> ?we k \<and> ?wv k \<in> ?we (Suc k)" using h1 h2 by (by100 blast)
    qed
    \<comment> \<open>Consecutive cycle arcs share exactly 1 vertex (from card \\<le> 1).\<close>
    \<comment> \<open>Non-backtracking: consecutive walk arcs differ.\<close>
    have hnonback: "\<forall>k. ?we (Suc k) \<noteq> ?we k"
    proof
      fix k
      have "?we (Suc k) = next_arc (?wv k) (?we k)" using hwalk_suc_snd .
      moreover have "next_arc (?wv k) (?we k) \<noteq> ?we k"
        using hnext hwalk_props by (by100 blast)
      ultimately show "?we (Suc k) \<noteq> ?we k" by simp
    qed
    \<comment> \<open>Intermediate vertices distinct (from minimum revisit).\<close>
    have hv_dist: "\<forall>k l. Suc i0 \<le> k \<and> k < j0 \<and> Suc i0 \<le> l \<and> l < j0 \<and> k \<noteq> l
        \<longrightarrow> ?wv k \<noteq> ?wv l"
    proof (intro allI impI)
      fix k l assume hkl: "Suc i0 \<le> k \<and> k < j0 \<and> Suc i0 \<le> l \<and> l < j0 \<and> k \<noteq> l"
      show "?wv k \<noteq> ?wv l"
      proof
        assume "?wv k = ?wv l"
        have "k < l \<or> l < k" using hkl by linarith
        thus False
        proof
          assume "k < l"
          have "l - k < dmin" using hkl hij0(4) by linarith
          moreover have "k < l \<and> l \<le> card ?V \<and> ?wv k = ?wv l"
            using \<open>k < l\<close> \<open>?wv k = ?wv l\<close> hkl hij0(2) by linarith
          moreover from hmin[rule_format, OF this]
          have "dmin \<le> l - k" .
          ultimately show False using hij0(4) by linarith
        next
          assume "l < k"
          have "k - l < dmin" using hkl hij0(4) by linarith
          have "k - l < dmin" using hkl hij0(4) by linarith
          have "?wv l = ?wv k" using \<open>?wv k = ?wv l\<close> by simp
          have "k \<le> card ?V" using hkl hij0(2) by linarith
          have "l < k \<and> k \<le> card ?V \<and> ?wv l = ?wv k"
            using \<open>l < k\<close> \<open>?wv l = ?wv k\<close> \<open>k \<le> card ?V\<close> by (by100 blast)
          from hmin[rule_format, OF this]
          have "dmin \<le> k - l" .
          with \<open>k - l < dmin\<close> show False by linarith
        qed
      qed
    qed
    \<comment> \<open>Walk arc at index: ws!idx = we(Suc i0 + idx).\<close>
    have hws_nth: "\<forall>idx < dmin. ?ws ! idx = ?we (Suc i0 + idx)"
    proof (intro allI impI)
      fix idx assume "idx < dmin"
      have "idx < length [0..<dmin]" using \<open>idx < dmin\<close> by simp
      thus "?ws ! idx = ?we (Suc i0 + idx)"
        using nth_map[OF \<open>idx < length [0..<dmin]\<close>, of "\<lambda>k. ?we (Suc i0 + k)"]
        by simp
    qed
    \<comment> \<open>Consecutive walk arcs are distinct (non-backtracking).\<close>
    have hcons_ne: "\<forall>idx < dmin. ?we (Suc i0 + idx) \<noteq> ?we (Suc i0 + Suc idx)"
    proof (intro allI impI)
      fix idx assume "idx < dmin"
      show "?we (Suc i0 + idx) \<noteq> ?we (Suc i0 + Suc idx)"
        using hnonback[rule_format, of "Suc i0 + idx"] by simp
    qed
    \<comment> \<open>Wraparound arcs distinct: we(j0) \\<noteq> we(Suc i0).\<close>
    have hwrap_ne: "?we j0 \<noteq> ?we (Suc i0)"
    proof (cases "dmin = 2")
      case True
      hence "j0 = Suc (Suc i0)" using hij0(1) hij0(4) by linarith
      thus ?thesis using hnonback[rule_format, of "Suc i0"] by simp
    next
      case False hence hdmin3: "dmin \<ge> 3" using hdmin_ge2 by linarith
      show ?thesis
      proof
        assume heq: "?we j0 = ?we (Suc i0)"
        \<comment> \<open>Both wv(i0) and wv(j0-1) are endpoints of we(j0) = we(Suc i0).
           wv(i0) = wv(j0). wv(j0-1) \\<noteq> wv(j0) (from other\\_ep at step j0).
           Similarly wv(Suc i0) \\<noteq> wv(i0). Arc has 2 endpoints = {wv(i0), wv(Suc i0)}.
           So wv(j0-1) = wv(Suc i0). But Suc i0 and j0-1 have distance < dmin. Contradiction.\<close>
        have hwvi0_ep: "?wv i0 \<in> ?ep (?we (Suc i0))"
          using hnext hwalk_props hwalk_suc_snd by (by100 simp)
        have hwvsi0_ep: "?wv (Suc i0) \<in> ?ep (?we (Suc i0))"
          using hwalk_props by (by100 blast)
        have hwvsi0_ne: "?wv (Suc i0) \<noteq> ?wv i0"
          using hother hnext hwalk_props hwalk_suc_fst by (by100 simp)
        have hep2: "?ep (?we (Suc i0)) = {?wv i0, ?wv (Suc i0)}"
        proof -
          have "?we (Suc i0) \<in> \<A>" using hwalk_props by (by100 blast)
          from h2ep[rule_format, OF this]
          obtain a b where "a \<noteq> b" "?ep (?we (Suc i0)) = {a, b}" by (by100 blast)
          thus ?thesis using hwvi0_ep hwvsi0_ep hwvsi0_ne
            by (by100 force)
        qed
        have "j0 = Suc (j0 - 1)" using hij0(1) by linarith
        have hwvj01_ep: "?wv (j0 - 1) \<in> ?ep (?we j0)"
          using hnext hwalk_props hwalk_suc_snd[of "j0 - 1"] \<open>j0 = Suc (j0 - 1)\<close>
          by (by100 simp)
        have "?wv (j0 - 1) \<noteq> ?wv j0"
        proof -
          let ?ej = "next_arc (?wv (j0-1)) (?we (j0-1))"
          have "?ej \<in> \<A>" using hnext hwalk_props by (by100 blast)
          have "?wv (j0-1) \<in> ?ep ?ej" using hnext hwalk_props by (by100 blast)
          have "?wv j0 = other_ep (?wv (j0-1)) ?ej"
            using hwalk_suc_fst[of "j0-1"] \<open>j0 = Suc (j0-1)\<close> by simp
          moreover have "other_ep (?wv (j0-1)) ?ej \<noteq> ?wv (j0-1)"
            using hother \<open>?ej \<in> \<A>\<close> \<open>?wv (j0-1) \<in> ?ep ?ej\<close> by (by100 blast)
          ultimately show ?thesis by simp
        qed
        hence "?wv (j0 - 1) \<noteq> ?wv i0" using hij0(3) by simp
        hence "?wv (j0 - 1) \<in> {?wv i0, ?wv (Suc i0)}"
          using hwvj01_ep heq hep2 by simp
        hence "?wv (j0 - 1) = ?wv (Suc i0)"
          using \<open>?wv (j0 - 1) \<noteq> ?wv i0\<close> by (by100 blast)
        \<comment> \<open>But Suc i0 and j0-1 have distance j0-1-(Suc i0) < dmin. hv\\_dist contradiction.\<close>
        have "Suc i0 \<le> j0 - 1" using hdmin3 hij0(4) hij0(1) by linarith
        have "j0 - 1 < j0" using hij0(1) by linarith
        have "j0 - 1 \<noteq> Suc i0" using hdmin3 hij0(4) hij0(1) by linarith
        have "Suc i0 \<le> j0 - 1 \<and> j0 - 1 < j0 \<and> Suc i0 \<le> Suc i0 \<and> Suc i0 < j0 \<and> j0 - 1 \<noteq> Suc i0"
          using \<open>Suc i0 \<le> j0 - 1\<close> \<open>j0 - 1 < j0\<close> hdmin3 hij0(4) hij0(1) \<open>j0 - 1 \<noteq> Suc i0\<close>
          by linarith
        from hv_dist[rule_format, OF this]
        show False using \<open>?wv (j0 - 1) = ?wv (Suc i0)\<close> by simp
      qed
    qed
    \<comment> \<open>Consecutive cycle arcs share exactly 1 vertex.\<close>
    have hws_card1: "\<forall>idx < length ?ws. card (?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws)) = 1"
    proof (intro allI impI)
      fix idx assume "idx < length ?ws"
      hence hidx: "idx < dmin" using hws_len by simp
      have hmod: "(idx + 1) mod dmin < dmin" using hdmin_ge2 by simp
      \<comment> \<open>The two arcs are distinct.\<close>
      have hAB_ne: "?ws ! idx \<noteq> ?ws ! ((idx + 1) mod length ?ws)"
      proof (cases "idx + 1 < dmin")
        case True
        hence "(idx + 1) mod dmin = idx + 1" by simp
        thus ?thesis
          using hws_nth[rule_format, OF hidx] hws_nth[rule_format, OF True]
              hcons_ne[rule_format, OF hidx] hws_len by simp
      next
        case False
        hence "idx = dmin - 1" using hidx by linarith
        hence "(idx + 1) mod dmin = 0" using hdmin_ge2 by simp
        have "Suc i0 + (dmin - 1) = j0" using hij0(4) hij0(1) hdmin_ge2 by linarith
        show ?thesis
          using hws_nth[rule_format, OF hidx] hws_nth[rule_format, of 0] hwrap_ne
              hws_len hdmin_ge2 \<open>idx = dmin - 1\<close> \<open>Suc i0 + (dmin - 1) = j0\<close>
              \<open>(idx + 1) mod dmin = 0\<close> by simp
      qed
      \<comment> \<open>Both are in \\<A>.\<close>
      have hA_in: "?ws ! idx \<in> \<A>"
        using hws_sub nth_mem \<open>idx < length ?ws\<close> by (by100 blast)
      have hB_in: "?ws ! ((idx + 1) mod length ?ws) \<in> \<A>"
      proof -
        have "(idx + 1) mod length ?ws < length ?ws" using hws_len hdmin_ge2 by simp
        hence "?ws ! ((idx + 1) mod length ?ws) \<in> set ?ws" using nth_mem by (by100 blast)
        thus ?thesis using hws_sub by (by100 blast)
      qed
      \<comment> \<open>They share a vertex (walk vertex).\<close>
      have hne: "?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws) \<noteq> {}"
      proof (cases "idx + 1 < dmin")
        case True \<comment> \<open>Non-wraparound: shared vertex wv(Suc i0 + idx).\<close>
        have "?wv (Suc i0 + idx) \<in> ?we (Suc i0 + idx)"
          using hwalk_shared by (by100 blast)
        moreover have "?wv (Suc i0 + idx) \<in> ?we (Suc i0 + Suc idx)"
          using hwalk_shared[rule_format, of "Suc i0 + idx"] by simp
        ultimately have "?wv (Suc i0 + idx) \<in> ?ws ! idx \<inter> ?ws ! (idx + 1)"
          using hws_nth[rule_format, OF hidx] hws_nth[rule_format, OF True] by simp
        hence "?ws ! idx \<inter> ?ws ! (idx + 1) \<noteq> {}" by (by100 blast)
        moreover have "(idx + 1) mod length ?ws = idx + 1" using True hws_len by simp
        ultimately show ?thesis by simp
      next
        case False \<comment> \<open>Wraparound: shared vertex wv(i0) = wv(j0).\<close>
        hence "idx = dmin - 1" using hidx by linarith
        have "Suc i0 + (dmin - 1) = j0" using hij0(4) hij0(1) hdmin_ge2 by linarith
        have "?wv j0 \<in> ?we j0" using hwalk_shared by (by100 blast)
        hence "?wv i0 \<in> ?we j0" using hij0(3) by simp
        moreover have "?wv i0 \<in> ?we (Suc i0)" using hwalk_shared by (by100 blast)
        ultimately have "?wv i0 \<in> ?ws ! idx \<inter> ?ws ! 0"
          using hws_nth[rule_format, OF hidx] hws_nth[rule_format, of 0] hdmin_ge2
              \<open>idx = dmin - 1\<close> \<open>Suc i0 + (dmin - 1) = j0\<close> by simp
        hence "?ws ! idx \<inter> ?ws ! 0 \<noteq> {}" by (by100 blast)
        moreover have "(idx + 1) mod length ?ws = 0" using \<open>idx = dmin - 1\<close> hws_len hdmin_ge2 by simp
        ultimately show ?thesis by simp
      qed
      \<comment> \<open>card \\<le> 1 from hinter, card \\<ge> 1 from non-empty.\<close>
      have hfin: "finite (?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws))"
        using hinter[rule_format, OF hA_in hB_in hAB_ne] by (by100 blast)
      have "card (?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws)) \<ge> 1"
      proof -
        have "card (?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws)) \<noteq> 0"
          using hfin hne by (by100 simp)
        thus ?thesis by linarith
      qed
      moreover have "card (?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws)) \<le> 1"
        using hinter[rule_format, OF hA_in hB_in hAB_ne] by (by100 blast)
      ultimately show "card (?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws)) = 1" by linarith
    qed
    \<comment> \<open>Arcs are distinct.\<close>
    have hws_dist: "distinct ?ws"
    proof (rule distinct_conv_nth[THEN iffD2], intro allI impI)
      fix k l assume hkl: "k < length ?ws" "l < length ?ws" "k \<noteq> l"
      hence hk: "k < dmin" and hl: "l < dmin" using hws_len by simp_all
      show "?ws ! k \<noteq> ?ws ! l"
      proof
        assume heq: "?ws ! k = ?ws ! l"
        \<comment> \<open>Same arc. The "arrived-at" vertex wv(Suc i0+k) is an endpoint.
           wv(Suc i0+k) \\<noteq> wv(Suc i0+l) from hv\\_dist (both in {Suc i0,...,j0-1}).
           But same arc has only 2 endpoints. Same arc + card \\<le> 1 means distinct arcs
           have \\<le> 1 common vertex, so same arc means same endpoint set.
           Cross-matching of arrived-at vs departed-from vertices forces |k-l|=1,
           then non-backtracking gives contradiction.\<close>
        \<comment> \<open>The arrived-at vertices differ (from hv\\_dist).\<close>
        have hvk_ne_vl: "?wv (Suc i0 + k) \<noteq> ?wv (Suc i0 + l)"
        proof -
          \<comment> \<open>Both Suc i0+k and Suc i0+l are in {Suc i0,...,j0}.
             If both < j0: hv\\_dist gives \\<noteq>. If one = j0: use wv(j0) = wv(i0)
             and hmin to get contradiction with a shorter revisit.\<close>
          have hk_le: "Suc i0 + k \<le> j0" using hk hij0(4) hij0(1) by linarith
          have hl_le: "Suc i0 + l \<le> j0" using hl hij0(4) hij0(1) by linarith
          have hkl_ne: "Suc i0 + k \<noteq> Suc i0 + l" using hkl(3) by linarith
          show ?thesis
          proof (cases "Suc i0 + k < j0 \<and> Suc i0 + l < j0")
            case True
            have "Suc i0 \<le> Suc i0 + k \<and> Suc i0 + k < j0 \<and> Suc i0 \<le> Suc i0 + l \<and> Suc i0 + l < j0 \<and> Suc i0 + k \<noteq> Suc i0 + l"
              using True hkl_ne by linarith
            thus ?thesis using hv_dist[rule_format] by (by100 blast)
          next
            case False
            \<comment> \<open>One of them = j0. Use wv(j0) = wv(i0) and hmin.\<close>
            hence "Suc i0 + k = j0 \<or> Suc i0 + l = j0" using hk_le hl_le by linarith
            thus ?thesis
            proof
              assume "Suc i0 + k = j0"
              hence "?wv (Suc i0 + k) = ?wv i0" using hij0(3) by simp
              show ?thesis
              proof
                assume heqv: "?wv (Suc i0 + k) = ?wv (Suc i0 + l)"
                hence "?wv i0 = ?wv (Suc i0 + l)" using \<open>?wv (Suc i0 + k) = ?wv i0\<close> by simp
                have "Suc i0 + l < j0" using hl_le hkl_ne \<open>Suc i0 + k = j0\<close> by linarith
                have "i0 < Suc i0 + l" by linarith
                have "Suc i0 + l \<le> card ?V" using \<open>Suc i0 + l < j0\<close> hij0(2) by linarith
                from hmin[rule_format, of i0 "Suc i0 + l"]
                have "dmin \<le> (Suc i0 + l) - i0"
                  using \<open>i0 < Suc i0 + l\<close> \<open>Suc i0 + l \<le> card ?V\<close> \<open>?wv i0 = ?wv (Suc i0 + l)\<close>
                  by (by100 blast)
                hence "dmin \<le> l + 1" by linarith
                hence "l = dmin - 1" using hl by linarith
                hence "Suc i0 + l = j0" using hij0(4) hij0(1) hdmin_ge2 by linarith
                thus False using \<open>Suc i0 + l < j0\<close> by linarith
              qed
            next
              assume "Suc i0 + l = j0"
              hence "?wv (Suc i0 + l) = ?wv i0" using hij0(3) by simp
              show ?thesis
              proof
                assume heqv: "?wv (Suc i0 + k) = ?wv (Suc i0 + l)"
                hence "?wv (Suc i0 + k) = ?wv i0" using \<open>?wv (Suc i0 + l) = ?wv i0\<close> by simp
                have "Suc i0 + k < j0" using hk_le hkl_ne \<open>Suc i0 + l = j0\<close> by linarith
                have "i0 < Suc i0 + k" by linarith
                have "Suc i0 + k \<le> card ?V" using \<open>Suc i0 + k < j0\<close> hij0(2) by linarith
                have "?wv i0 = ?wv (Suc i0 + k)" using \<open>?wv (Suc i0 + k) = ?wv i0\<close> by simp
                from hmin[rule_format, of i0 "Suc i0 + k"]
                have "dmin \<le> (Suc i0 + k) - i0"
                  using \<open>i0 < Suc i0 + k\<close> \<open>Suc i0 + k \<le> card ?V\<close> \<open>?wv i0 = ?wv (Suc i0 + k)\<close>
                  by (by100 blast)
                hence "dmin \<le> k + 1" by linarith
                hence "k = dmin - 1" using hk by linarith
                hence "Suc i0 + k = j0" using hij0(4) hij0(1) hdmin_ge2 by linarith
                thus False using \<open>Suc i0 + k < j0\<close> by linarith
              qed
            qed
          qed
        qed
        \<comment> \<open>Both are endpoints of the same arc we(Suc i0+k) = we(Suc i0+l).\<close>
        have hek: "?ws ! k = ?we (Suc i0 + k)" using hws_nth[rule_format, OF hk] .
        have hel: "?ws ! l = ?we (Suc i0 + l)" using hws_nth[rule_format, OF hl] .
        \<comment> \<open>wv(i0+k) and wv(Suc i0+k) are the 2 endpoints of we(Suc i0+k).\<close>
        have hep_k: "?wv (Suc i0 + k) \<in> ?ep (?we (Suc i0 + k))"
          using hwalk_props by (by100 blast)
        have hep_k2: "?wv (i0 + k) \<in> ?ep (?we (Suc i0 + k))"
          using hnext hwalk_props hwalk_suc_snd[of "i0 + k"] by simp
        have hne_k: "?wv (Suc i0 + k) \<noteq> ?wv (i0 + k)"
        proof -
          let ?ek = "next_arc (?wv (i0+k)) (?we (i0+k))"
          have "?ek \<in> \<A>" using hnext hwalk_props by (by100 blast)
          have "?wv (i0+k) \<in> ?ep ?ek" using hnext hwalk_props by (by100 blast)
          have "?wv (Suc i0+k) = other_ep (?wv (i0+k)) ?ek" using hwalk_suc_fst[of "i0+k"] by simp
          moreover have "other_ep (?wv (i0+k)) ?ek \<noteq> ?wv (i0+k)"
            using hother \<open>?ek \<in> \<A>\<close> \<open>?wv (i0+k) \<in> ?ep ?ek\<close> by (by100 blast)
          ultimately show ?thesis by simp
        qed
        \<comment> \<open>ep = {wv(i0+k), wv(Suc i0+k)}.\<close>
        have hep_set_k: "?ep (?we (Suc i0 + k)) = {?wv (i0 + k), ?wv (Suc i0 + k)}"
        proof -
          have "?we (Suc i0 + k) \<in> \<A>" using hwalk_props by (by100 blast)
          from h2ep[rule_format, OF this]
          obtain a b where "a \<noteq> b" "?ep (?we (Suc i0 + k)) = {a, b}" by (by100 blast)
          thus ?thesis using hep_k hep_k2 hne_k by (by100 force)
        qed
        \<comment> \<open>Same for l.\<close>
        have hep_l: "?wv (Suc i0 + l) \<in> ?ep (?we (Suc i0 + l))"
          using hwalk_props by (by100 blast)
        have hep_l2: "?wv (i0 + l) \<in> ?ep (?we (Suc i0 + l))"
          using hnext hwalk_props hwalk_suc_snd[of "i0 + l"] by simp
        have hne_l: "?wv (Suc i0 + l) \<noteq> ?wv (i0 + l)"
        proof -
          let ?el = "next_arc (?wv (i0+l)) (?we (i0+l))"
          have "?el \<in> \<A>" using hnext hwalk_props by (by100 blast)
          have "?wv (i0+l) \<in> ?ep ?el" using hnext hwalk_props by (by100 blast)
          have "?wv (Suc i0+l) = other_ep (?wv (i0+l)) ?el" using hwalk_suc_fst[of "i0+l"] by simp
          moreover have "other_ep (?wv (i0+l)) ?el \<noteq> ?wv (i0+l)"
            using hother \<open>?el \<in> \<A>\<close> \<open>?wv (i0+l) \<in> ?ep ?el\<close> by (by100 blast)
          ultimately show ?thesis by simp
        qed
        have hep_set_l: "?ep (?we (Suc i0 + l)) = {?wv (i0 + l), ?wv (Suc i0 + l)}"
        proof -
          have "?we (Suc i0 + l) \<in> \<A>" using hwalk_props by (by100 blast)
          from h2ep[rule_format, OF this]
          obtain a b where "a \<noteq> b" "?ep (?we (Suc i0 + l)) = {a, b}" by (by100 blast)
          thus ?thesis using hep_l hep_l2 hne_l by (by100 force)
        qed
        \<comment> \<open>Same arc \\<Rightarrow> same ep. So {wv(i0+k), wv(Suc i0+k)} = {wv(i0+l), wv(Suc i0+l)}.\<close>
        have hep_same: "{?wv (i0 + k), ?wv (Suc i0 + k)} = {?wv (i0 + l), ?wv (Suc i0 + l)}"
          using hep_set_k hep_set_l heq hek hel by simp
        \<comment> \<open>Cross-matching: wv(Suc i0+k) \\<in> {wv(i0+l), wv(Suc i0+l)}.\<close>
        have "?wv (Suc i0 + k) \<in> {?wv (i0 + l), ?wv (Suc i0 + l)}"
          using hep_same hne_k by (by100 blast)
        hence "?wv (Suc i0 + k) = ?wv (i0 + l)"
          using hvk_ne_vl by (by100 blast)
        \<comment> \<open>Similarly: wv(i0+k) = wv(Suc i0+l).\<close>
        have "?wv (i0 + k) \<in> {?wv (i0 + l), ?wv (Suc i0 + l)}"
          using hep_same by (by100 blast)
        hence "?wv (i0 + k) = ?wv (Suc i0 + l)"
        proof -
          have "?wv (i0 + k) \<noteq> ?wv (i0 + l)"
          proof
            assume "?wv (i0 + k) = ?wv (i0 + l)"
            hence "?wv (Suc i0 + k) = ?wv (i0 + k)"
              using \<open>?wv (Suc i0 + k) = ?wv (i0 + l)\<close> by simp
            thus False using hne_k by simp
          qed
          thus ?thesis using \<open>?wv (i0 + k) \<in> {?wv (i0 + l), ?wv (Suc i0 + l)}\<close> by (by100 blast)
        qed
        \<comment> \<open>From wv(Suc i0+k) = wv(i0+l): Suc i0+k and i0+l are walk positions
           with same vertex. If both in {Suc i0,...,j0-1}: hv\\_dist gives Suc i0+k = i0+l, so k+1=l.
           Boundary cases handled similarly.\<close>
        have "k + 1 = l \<or> l + 1 = k"
        proof (rule ccontr)
          assume "\<not> (k + 1 = l \<or> l + 1 = k)"
          hence hkl_ne1: "Suc i0 + k \<noteq> i0 + l" and hkl_ne2: "i0 + k \<noteq> Suc i0 + l" by linarith+
          \<comment> \<open>Apply hmin on pair 2: wv(i0+k) = wv(Suc i0+l), positions i0+k and Suc i0+l.\<close>
          have hsk_le: "Suc i0 + k \<le> j0" using hk hij0(4) hij0(1) by linarith
          have hsl_le: "Suc i0 + l \<le> j0" using hl hij0(4) hij0(1) by linarith
          have hk_ge: "i0 + k \<ge> i0" by simp
          have hl_ge: "i0 + l \<ge> i0" by simp
          show False
          proof (cases "i0 + k < Suc i0 + l")
            case True
            have "?wv (i0 + k) = ?wv (Suc i0 + l)"
              using \<open>?wv (i0 + k) = ?wv (Suc i0 + l)\<close> .
            have "i0 + k < Suc i0 + l \<and> Suc i0 + l \<le> card ?V \<and> ?wv (i0 + k) = ?wv (Suc i0 + l)"
              using True hsl_le hij0(2) \<open>?wv (i0 + k) = ?wv (Suc i0 + l)\<close> by linarith
            from hmin[rule_format, OF this]
            have "dmin \<le> (Suc i0 + l) - (i0 + k)" .
            \<comment> \<open>= l - k + 1. Also from pair 1: dmin \\<le> |Suc i0 + k - (i0 + l)| = |k - l + 1| = k - l + 1 (since k > l from True: k < l + 1 is False...).\<close>
            \<comment> \<open>Actually: True says i0+k < Suc i0+l, so k < l + 1, so k \\<le> l. Distance = l - k + 1.\<close>
            hence "dmin \<le> l - k + 1" by linarith
            \<comment> \<open>Also apply hmin on pair 1 (in the reverse direction if needed).\<close>
            have "Suc i0 + k \<le> card ?V" using hsk_le hij0(2) by linarith
            show False
            proof (cases "i0 + l < Suc i0 + k")
              case True2: True
              have "?wv (i0 + l) = ?wv (Suc i0 + k)" using \<open>?wv (Suc i0 + k) = ?wv (i0 + l)\<close> by simp
              have "i0 + l < Suc i0 + k \<and> Suc i0 + k \<le> card ?V \<and> ?wv (i0 + l) = ?wv (Suc i0 + k)"
                using True2 \<open>Suc i0 + k \<le> card ?V\<close> \<open>?wv (i0 + l) = ?wv (Suc i0 + k)\<close> by (by100 blast)
              from hmin[rule_format, OF this]
              have "dmin \<le> (Suc i0 + k) - (i0 + l)" .
              hence "dmin \<le> k - l + 1" by linarith
              \<comment> \<open>Now: dmin \\<le> l - k + 1 AND dmin \\<le> k - l + 1. Sum: 2*dmin \\<le> 2. So dmin \\<le> 1.\<close>
              thus False using hdmin_ge2 \<open>dmin \<le> l - k + 1\<close> by linarith
            next
              case False2: False
              \<comment> \<open>i0+l \\<ge> Suc i0+k. hkl\\_ne1: Suc i0+k \\<noteq> i0+l. So i0+l > Suc i0+k.\<close>
              hence "Suc i0 + k < i0 + l" using hkl_ne1 by linarith
              have "?wv (Suc i0 + k) = ?wv (i0 + l)" using \<open>?wv (Suc i0 + k) = ?wv (i0 + l)\<close> .
              have "i0 + l \<le> j0" using hl hij0(4) hij0(1) by linarith
              have "Suc i0 + k < i0 + l \<and> i0 + l \<le> card ?V \<and> ?wv (Suc i0 + k) = ?wv (i0 + l)"
                using \<open>Suc i0 + k < i0 + l\<close> \<open>i0 + l \<le> j0\<close> hij0(2) \<open>?wv (Suc i0 + k) = ?wv (i0 + l)\<close> by linarith
              from hmin[rule_format, OF this]
              have "dmin \<le> (i0 + l) - (Suc i0 + k)" .
              \<comment> \<open>= l - k - 1 \\<le> l - 1 < dmin. Contradiction.\<close>
              hence "dmin \<le> l - 1" by linarith
              thus False using hl by linarith
            qed
          next
            case False
            hence "Suc i0 + l \<le> i0 + k" using hkl_ne2 by linarith
            hence "l + 1 \<le> k" by linarith
            have "?wv (Suc i0 + l) = ?wv (i0 + k)" using \<open>?wv (i0 + k) = ?wv (Suc i0 + l)\<close> by simp
            have "Suc i0 + l < i0 + k \<or> Suc i0 + l = i0 + k" using \<open>Suc i0 + l \<le> i0 + k\<close> by linarith
            thus False
            proof
              assume "Suc i0 + l < i0 + k"
              have "i0 + k \<le> card ?V" using hsk_le hij0(2) by linarith
              have "Suc i0 + l < i0 + k \<and> i0 + k \<le> card ?V \<and> ?wv (Suc i0 + l) = ?wv (i0 + k)"
                using \<open>Suc i0 + l < i0 + k\<close> \<open>i0 + k \<le> card ?V\<close> \<open>?wv (Suc i0 + l) = ?wv (i0 + k)\<close>
                by (by100 blast)
              from hmin[rule_format, OF this]
              have "dmin \<le> (i0 + k) - (Suc i0 + l)" .
              hence "dmin \<le> k - l - 1" by linarith
              \<comment> \<open>And from pair 1 (Suc i0+k > i0+l since k > l):\<close>
              have "i0 + l < Suc i0 + k" using \<open>l + 1 \<le> k\<close> by linarith
              have "?wv (i0 + l) = ?wv (Suc i0 + k)" using \<open>?wv (Suc i0 + k) = ?wv (i0 + l)\<close> by simp
              have "i0 + l < Suc i0 + k \<and> Suc i0 + k \<le> card ?V \<and> ?wv (i0 + l) = ?wv (Suc i0 + k)"
                using \<open>i0 + l < Suc i0 + k\<close> hsk_le hij0(2) \<open>?wv (i0 + l) = ?wv (Suc i0 + k)\<close> by linarith
              from hmin[rule_format, OF this]
              have "dmin \<le> (Suc i0 + k) - (i0 + l)" .
              hence "dmin \<le> k - l + 1" by linarith
              \<comment> \<open>dmin \\<le> k - l - 1. With l \\<ge> 0 and k \\<ge> l+2: k - l - 1 \\<le> k - 1 < dmin.\<close>
              have "k - l - 1 \<le> k" by linarith
              hence "dmin \<le> k" using \<open>dmin \<le> k - l - 1\<close> by linarith
              thus False using hk by linarith
            next
              assume "Suc i0 + l = i0 + k"
              hence "l + 1 = k" by linarith
              thus False using \<open>\<not> (k + 1 = l \<or> l + 1 = k)\<close> by simp
            qed
          qed
        qed
        \<comment> \<open>Either way: consecutive arcs equal \\<Rightarrow> hnonback contradiction.\<close>
        thus False
        proof
          assume "k + 1 = l"
          hence "Suc i0 + l = Suc (Suc i0 + k)" by linarith
          hence "?we (Suc i0 + k) = ?we (Suc (Suc i0 + k))" using heq hek hel by simp
          thus False using hnonback[rule_format, of "Suc i0 + k"] by simp
        next
          assume "l + 1 = k"
          hence "Suc i0 + k = Suc (Suc i0 + l)" by linarith
          hence "?we (Suc i0 + l) = ?we (Suc (Suc i0 + l))" using heq hek hel by simp
          thus False using hnonback[rule_format, of "Suc i0 + l"] by simp
        qed
      qed
    qed
    \<comment> \<open>Apply hacyclic.\<close>
    from hacyclic[rule_format, OF hws_ge2 hws_dist]
    show False using hws_sub hws_card1 by (by100 blast)
  qed
  from \<open>\<exists>v\<in>?V. card {A \<in> \<A>. v \<in> ?ep A} \<le> 1\<close>
  show ?thesis .
qed


\<comment> \<open>Forest Euler formula (purely combinatorial, no topology):
   In a graph (finite vertex set V, finite arc set \\<A>, each arc has 2 distinct endpoints in V)
   that is acyclic (no cycle of distinct arcs), V \\<ge> E + 1.
   Proof: by induction on E. Key step: acyclic \\<Rightarrow> every arc is a bridge (removing disconnects).
   Bridge removal splits into 2 components; IH on each gives V1 \\<ge> E1+1 and V2 \\<ge> E2+1,
   so V = V1+V2 \\<ge> E1+E2+2 = (E-1)+2 = E+1.\<close>
lemma forest_euler_formula:
  fixes \<A> :: "'a set set"
  assumes harcs: "\<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)"
      and hcover: "\<Union>\<A> = T"
      and hinter: "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 1"
      and hfin: "finite \<A>"
      and hstrict: "is_topology_on_strict T TT"
      and hhaus: "is_hausdorff_on T TT"
      \<comment> \<open>Acyclicity: no cycle of \\<ge> 2 distinct arcs forming a closed walk.\<close>
      and hacyclic: "\<forall>ws. length ws \<ge> 2 \<longrightarrow> distinct ws \<longrightarrow> set ws \<subseteq> \<A> \<longrightarrow>
          (\<forall>i < length ws. card (ws ! i \<inter> ws ! ((i + 1) mod length ws)) = 1) \<longrightarrow> False"
      and hne: "\<A> \<noteq> {}"
  shows "card (top1_graph_vertex_set T TT \<A>) \<ge> card \<A> + 1"
proof -
  let ?V = "top1_graph_vertex_set T TT \<A>"
  let ?ep = "\<lambda>A. top1_arc_endpoints_on A (subspace_topology T TT A)"
  \<comment> \<open>Leaf existence from the walk argument (proved in acyclic\\_graph\\_has\\_leaf).\<close>
  have hleaf: "\<exists>v\<in>?V. card {A \<in> \<A>. v \<in> ?ep A} \<le> 1"
    by (rule acyclic_graph_has_leaf[OF harcs hcover hinter hfin hstrict hhaus hacyclic hne])
  \<comment> \<open>From the leaf, do induction on card(\\<A>) to get V \\<ge> E + 1.
     Base (card=1): V = 2 \\<ge> 2 = 1+1.
     Step (card\\<ge>2): remove the leaf arc. The remaining graph is still acyclic.
     By IH: V(remaining) \\<ge> E(remaining) + 1.
     The leaf vertex adds 1 to V without adding to E. So V \\<ge> E + 1.\<close>
  \<comment> \<open>V \\<ge> E + 1 by strong induction on card(\\<A>), using the leaf existence.\<close>
  \<comment> \<open>V \\<ge> E + 1 by strong induction on card(\\<A>), using the leaf existence.\<close>
  show ?thesis using hfin hne harcs hcover hinter hstrict hhaus hacyclic
  proof (induction "card \<A>" arbitrary: \<A> T TT rule: less_induct)
    case (less \<A> T TT)
    \<comment> \<open>Unpack the assumptions from less.prems.\<close>
    note hfin' = less.prems(1)
    note hne' = less.prems(2)
    note harcs' = less.prems(3)
    note hcover' = less.prems(4)
    note hinter' = less.prems(5)
    note hstrict' = less.prems(6)
    note hhaus' = less.prems(7)
    note hacyclic' = less.prems(8)
    let ?ep = "\<lambda>A. top1_arc_endpoints_on A (subspace_topology T TT A)"
    let ?V = "top1_graph_vertex_set T TT \<A>"
    show ?case
    proof (cases "card \<A> = 1")
      case True
      \<comment> \<open>Base: single arc has 2 distinct endpoints, so V = 2 \\<ge> 2.\<close>
      then obtain A0 where h\<A>_eq: "\<A> = {A0}"
        using card_1_singletonE hfin' by (by100 metis)
      have "card ?V = 2"
      proof -
        have "A0 \<in> \<A>" using h\<A>_eq by simp
        have hA0_sub: "A0 \<subseteq> T" and hA0_arc: "top1_is_arc_on A0 (subspace_topology T TT A0)"
          using harcs'[rule_format, OF \<open>A0 \<in> \<A>\<close>] by (by100 blast)+
        obtain h where hh: "top1_homeomorphism_on I_set I_top A0 (subspace_topology T TT A0) h"
          using hA0_arc unfolding top1_is_arc_on_def by (by100 blast)
        have hep: "?ep A0 = {h 0, h 1}"
          by (rule arc_endpoints_are_boundary[OF hstrict' hhaus' hA0_sub hA0_arc hh])
        have "h 0 \<noteq> h 1"
        proof
          assume "h 0 = h 1"
          have "inj_on h I_set" using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
          from inj_onD[OF this \<open>h 0 = h 1\<close>] show False unfolding top1_unit_interval_def by (by100 auto)
        qed
        hence "card (?ep A0) = 2" using hep by simp
        have "?V = ?ep A0"
          unfolding top1_graph_vertex_set_def using h\<A>_eq by (by100 blast)
        thus ?thesis using \<open>card (?ep A0) = 2\<close> by simp
      qed
      thus ?thesis using True by linarith
    next
      case False
      hence hcard_ge2: "card \<A> \<ge> 2"
      proof -
        have "card \<A> \<noteq> 0" using hne' hfin' by (by100 simp)
        thus ?thesis using False \<open>card \<A> \<noteq> 1\<close> by linarith
      qed
      \<comment> \<open>Leaf existence (re-derive from walk argument, same as outer proof).\<close>
      have hleaf: "\<exists>v\<in>?V. card {A \<in> \<A>. v \<in> ?ep A} \<le> 1"
        by (rule acyclic_graph_has_leaf[OF harcs' hcover' hinter' hfin' hstrict' hhaus' hacyclic' hne'])
      then obtain v where hv_V: "v \<in> ?V" "card {A \<in> \<A>. v \<in> ?ep A} \<le> 1"
        by (by100 blast)
      \<comment> \<open>Degree = 1 (\\<ge> 1 from V membership).\<close>
      have "card {A \<in> \<A>. v \<in> ?ep A} \<ge> 1"
      proof -
        from hv_V(1) obtain A0 where "A0 \<in> \<A>" "v \<in> ?ep A0"
          unfolding top1_graph_vertex_set_def by (by100 blast)
        hence "A0 \<in> {A \<in> \<A>. v \<in> ?ep A}" by (by100 blast)
        hence hne_deg: "{A \<in> \<A>. v \<in> ?ep A} \<noteq> {}" by (by100 blast)
        have "finite {A \<in> \<A>. v \<in> ?ep A}" using hfin' by (by100 simp)
        hence "card {A \<in> \<A>. v \<in> ?ep A} \<noteq> 0" using hne_deg by (by100 simp)
        thus ?thesis by linarith
      qed
      hence "card {A \<in> \<A>. v \<in> ?ep A} = 1" using hv_V(2) by linarith
      then obtain A0 where hA0_eq: "{A \<in> \<A>. v \<in> ?ep A} = {A0}"
        by (rule card_1_singletonE)
      hence hA0_in: "A0 \<in> \<A>" by (by100 blast)
      \<comment> \<open>v only in A0: v is an endpoint of A0 only.\<close>
      have hv_in_A0: "v \<in> A0"
      proof -
        have "v \<in> ?ep A0" using hA0_eq by (by100 blast)
        thus ?thesis unfolding top1_arc_endpoints_on_def by (by100 blast)
      qed
      have hv_only: "\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> v \<notin> B"
      proof (intro ballI impI)
        fix B assume "B \<in> \<A>" "B \<noteq> A0"
        show "v \<notin> B"
        proof
          assume "v \<in> B"
          hence "v \<in> A0 \<inter> B" using hv_in_A0 by (by100 blast)
          have "A0 \<noteq> B" using \<open>B \<noteq> A0\<close> by simp
          from hinter'[rule_format, OF hA0_in \<open>B \<in> \<A>\<close> \<open>A0 \<noteq> B\<close>]
          have "A0 \<inter> B \<subseteq> ?ep B" by (by100 blast)
          hence "v \<in> ?ep B" using \<open>v \<in> A0 \<inter> B\<close> by (by100 blast)
          hence "B \<in> {A \<in> \<A>. v \<in> ?ep A}" using \<open>B \<in> \<A>\<close> by (by100 blast)
          hence "B = A0" using hA0_eq by (by100 blast)
          thus False using \<open>B \<noteq> A0\<close> by simp
        qed
      qed
      \<comment> \<open>\\<A>' = \\<A> \\ {A0}. V' = V \\ {v}.\<close>
      let ?\<A>' = "\<A> - {A0}"
      let ?T' = "\<Union>?\<A>'"
      let ?TT' = "subspace_topology T TT ?T'"
      have h\<A>'_ne: "?\<A>' \<noteq> {}"
      proof -
        have "card \<A> \<ge> 2" using hcard_ge2 .
        have "card {A0} = 1" by simp
        hence "\<A> \<noteq> {A0}" using \<open>card \<A> \<ge> 2\<close> by (by100 force)
        then obtain B where "B \<in> \<A>" "B \<noteq> A0" using hA0_in by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      have h\<A>'_fin: "finite ?\<A>'" using hfin' by (by100 simp)
      have hcard': "card ?\<A>' < card \<A>"
      proof -
        have "A0 \<in> \<A>" using hA0_in .
        have "card (\<A> - {A0}) = card \<A> - 1" using hfin' hA0_in by simp
        thus ?thesis using hcard_ge2 by linarith
      qed
      \<comment> \<open>Subspace topology: for A \\<in> \\<A>', subspace T' TT' A = subspace T TT A.\<close>
      have hT'_sub: "?T' \<subseteq> T" using harcs' by (by100 blast)
      have hsub_trans: "\<forall>A\<in>?\<A>'. subspace_topology ?T' ?TT' A = subspace_topology T TT A"
      proof (intro ballI)
        fix A assume "A \<in> ?\<A>'"
        hence "A \<subseteq> ?T'" by (by100 blast)
        from subspace_topology_trans[OF this]
        show "subspace_topology ?T' ?TT' A = subspace_topology T TT A" .
      qed
      \<comment> \<open>All premises transfer to \\<A>' on T'.\<close>
      have harcs_r: "\<forall>A\<in>?\<A>'. A \<subseteq> ?T' \<and> top1_is_arc_on A (subspace_topology ?T' ?TT' A)"
      proof (intro ballI conjI)
        fix A assume "A \<in> ?\<A>'"
        thus "A \<subseteq> ?T'" by (by100 blast)
        have "A \<in> \<A>" using \<open>A \<in> ?\<A>'\<close> by (by100 blast)
        hence "top1_is_arc_on A (subspace_topology T TT A)" using harcs' by (by100 blast)
        thus "top1_is_arc_on A (subspace_topology ?T' ?TT' A)"
          using hsub_trans \<open>A \<in> ?\<A>'\<close> by simp
      qed
      have hcover_r: "\<Union>?\<A>' = ?T'" by simp
      have hinter_r: "\<forall>A\<in>?\<A>'. \<forall>B\<in>?\<A>'. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?T' ?TT' A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?T' ?TT' B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 1"
      proof (intro ballI impI)
        fix A B assume "A \<in> ?\<A>'" "B \<in> ?\<A>'" "A \<noteq> B"
        hence "A \<in> \<A>" "B \<in> \<A>" by (by100 blast)+
        from hinter'[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>A \<noteq> B\<close>]
        show "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?T' ?TT' A)
            \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?T' ?TT' B)
            \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 1"
          using hsub_trans \<open>A \<in> ?\<A>'\<close> \<open>B \<in> ?\<A>'\<close> by simp
      qed
      have htop': "is_topology_on T TT" using hstrict' unfolding is_topology_on_strict_def by (by100 blast)
      have hstrict_r: "is_topology_on_strict ?T' ?TT'"
        by (rule subspace_topology_is_strict[OF hstrict' hT'_sub])
      have hhaus_r: "is_hausdorff_on ?T' ?TT'"
        by (rule hausdorff_subspace[OF hhaus' hT'_sub])
      have hacyclic_r: "\<forall>ws. length ws \<ge> 2 \<longrightarrow> distinct ws \<longrightarrow> set ws \<subseteq> ?\<A>' \<longrightarrow>
          (\<forall>i < length ws. card (ws ! i \<inter> ws ! ((i + 1) mod length ws)) = 1) \<longrightarrow> False"
        using hacyclic' by (by100 blast)
      \<comment> \<open>Apply IH.\<close>
      from less.hyps[OF hcard' h\<A>'_fin h\<A>'_ne harcs_r hcover_r hinter_r hstrict_r hhaus_r hacyclic_r]
      have hIH: "card (top1_graph_vertex_set ?T' ?TT' ?\<A>') \<ge> card ?\<A>' + 1" .
      \<comment> \<open>V'(on T') = V'(on T) because arc subspace topologies agree.\<close>
      have hV'_eq: "top1_graph_vertex_set ?T' ?TT' ?\<A>' = top1_graph_vertex_set T TT ?\<A>'"
        unfolding top1_graph_vertex_set_def using hsub_trans by simp
      \<comment> \<open>V = V' + 1, E = E' + 1.\<close>
      have hv_not_V': "v \<notin> top1_graph_vertex_set T TT ?\<A>'"
      proof
        assume "v \<in> top1_graph_vertex_set T TT ?\<A>'"
        then obtain B where "B \<in> ?\<A>'" "v \<in> ?ep B"
          unfolding top1_graph_vertex_set_def by (by100 blast)
        hence "B \<in> \<A>" "B \<noteq> A0" by (by100 blast)+
        have "v \<in> B" using \<open>v \<in> ?ep B\<close> unfolding top1_arc_endpoints_on_def by (by100 blast)
        thus False using hv_only[rule_format, OF \<open>B \<in> \<A>\<close> \<open>B \<noteq> A0\<close>] by simp
      qed
      \<comment> \<open>V \\<supseteq> {v} \\<union> V', so card V \\<ge> card V' + 1.\<close>
      have hV'_sub: "top1_graph_vertex_set T TT ?\<A>' \<subseteq> ?V"
        unfolding top1_graph_vertex_set_def by (by100 blast)
      have hep_fin': "\<forall>A0\<in>\<A>. finite (?ep A0)"
      proof (intro ballI)
        fix B assume "B \<in> \<A>"
        have "B \<subseteq> T" and "top1_is_arc_on B (subspace_topology T TT B)"
          using harcs'[rule_format, OF \<open>B \<in> \<A>\<close>] by (by100 blast)+
        obtain h where "top1_homeomorphism_on I_set I_top B (subspace_topology T TT B) h"
          using \<open>top1_is_arc_on B _\<close> unfolding top1_is_arc_on_def by (by100 blast)
        have "?ep B = {h 0, h 1}"
          by (rule arc_endpoints_are_boundary[OF hstrict' hhaus' \<open>B \<subseteq> T\<close> \<open>top1_is_arc_on B _\<close> \<open>top1_homeomorphism_on _ _ _ _ h\<close>])
        thus "finite (?ep B)" by simp
      qed
      have hV_fin': "finite ?V"
        unfolding top1_graph_vertex_set_def using hfin' hep_fin' by (by100 blast)
      have "card ?V \<ge> card (top1_graph_vertex_set T TT ?\<A>') + 1"
      proof -
        have "insert v (top1_graph_vertex_set T TT ?\<A>') \<subseteq> ?V"
          using hV'_sub hv_V by (by100 blast)
        have "finite (top1_graph_vertex_set T TT ?\<A>')"
          using hV_fin' hV'_sub by (rule finite_subset[rotated])
        hence "card (insert v (top1_graph_vertex_set T TT ?\<A>')) = card (top1_graph_vertex_set T TT ?\<A>') + 1"
          using hv_not_V' by simp
        moreover have "card (insert v (top1_graph_vertex_set T TT ?\<A>')) \<le> card ?V"
          using card_mono[OF hV_fin' \<open>insert v _ \<subseteq> ?V\<close>] .
        ultimately show ?thesis by linarith
      qed
      have "card \<A> = card ?\<A>' + 1"
      proof -
        have "card (\<A> - {A0}) = card \<A> - 1" using hfin' hA0_in by simp
        thus ?thesis using hcard_ge2 by linarith
      qed
      have "card (top1_graph_vertex_set T TT ?\<A>') \<ge> card ?\<A>' + 1"
        using hIH hV'_eq by simp
      thus ?thesis using \<open>card ?V \<ge> card (top1_graph_vertex_set T TT ?\<A>') + 1\<close>
          \<open>card \<A> = card ?\<A>' + 1\<close> by linarith
    qed
  qed
qed


\<comment> \<open>Topological bridge: leaf existence in SC graphs with coherent topology.
   Munkres Lemma 84.2 converse: every finite tree with \\<ge> 2 arcs has a leaf.
   Uses sc\\_graph\\_no\\_cycle for the acyclicity transfer, then combinatorial leaf existence.\<close>
lemma tree_leaf_existence_bridge:
  fixes T :: "'a set" and TT :: "'a set set" and \<A> :: "'a set set"
  assumes "top1_is_tree_on T TT"
      and "\<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)"
      and "\<Union>\<A> = T"
      and "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and "finite \<A>" and "card \<A> \<ge> 2"
      and "\<forall>C. C \<subseteq> T \<longrightarrow> (closedin_on T TT C \<longleftrightarrow>
          (\<forall>A\<in>\<A>. closedin_on A (subspace_topology T TT A) (A \<inter> C)))"
  shows "\<exists>A0 v. A0 \<in> \<A> \<and> v \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)
      \<and> (\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> v \<notin> B)"
proof (rule ccontr)
  assume hno_leaf: "\<not> (\<exists>A0 v. A0 \<in> \<A> \<and> v \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)
      \<and> (\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> v \<notin> B))"
  \<comment> \<open>Step 1: Every endpoint of every arc is shared with another arc (degree \\<ge> 2).\<close>
  have hshared: "\<forall>A0\<in>\<A>. \<forall>v\<in>top1_arc_endpoints_on A0 (subspace_topology T TT A0).
      \<exists>B\<in>\<A>. B \<noteq> A0 \<and> v \<in> B"
  proof (intro ballI)
    fix A0 v assume "A0 \<in> \<A>" "v \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)"
    show "\<exists>B\<in>\<A>. B \<noteq> A0 \<and> v \<in> B"
    proof (rule ccontr)
      assume "\<not> (\<exists>B\<in>\<A>. B \<noteq> A0 \<and> v \<in> B)"
      hence "\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> v \<notin> B" by (by100 blast)
      with \<open>A0 \<in> \<A>\<close> \<open>v \<in> top1_arc_endpoints_on A0 _\<close>
      have "\<exists>A0 v. A0 \<in> \<A> \<and> v \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0) \<and>
          (\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> v \<notin> B)" by (by100 blast)
      with hno_leaf show False by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 2: Each arc has exactly 2 distinct endpoints.\<close>
  have hstrict: "is_topology_on_strict T TT"
    using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
  have hhaus: "is_hausdorff_on T TT"
    using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
  have h2ep: "\<forall>A0\<in>\<A>. \<exists>a0 b0. a0 \<noteq> b0 \<and>
      top1_arc_endpoints_on A0 (subspace_topology T TT A0) = {a0, b0}"
  proof (intro ballI)
    fix A0 assume "A0 \<in> \<A>"
    have "A0 \<subseteq> T" "top1_is_arc_on A0 (subspace_topology T TT A0)"
      using assms(2) \<open>A0 \<in> \<A>\<close> by (by100 blast)+
    then obtain h where hh: "top1_homeomorphism_on I_set I_top A0 (subspace_topology T TT A0) h"
      unfolding top1_is_arc_on_def by (by100 blast)
    have "top1_arc_endpoints_on A0 (subspace_topology T TT A0) = {h 0, h 1}"
      by (rule arc_endpoints_are_boundary[OF hstrict hhaus \<open>A0 \<subseteq> T\<close>
          \<open>top1_is_arc_on A0 _\<close> hh])
    moreover have "h 0 \<noteq> h 1"
    proof
      assume "h 0 = h 1"
      have "inj_on h I_set" using hh unfolding top1_homeomorphism_on_def bij_betw_def
        by (by100 blast)
      from inj_onD[OF this \<open>h 0 = h 1\<close>] show False
        unfolding top1_unit_interval_def by (by100 auto)
    qed
    ultimately show "\<exists>a0 b0. a0 \<noteq> b0 \<and>
        top1_arc_endpoints_on A0 (subspace_topology T TT A0) = {a0, b0}" by (by100 blast)
  qed
  \<comment> \<open>Step 3: Construct non-backtracking walk. By finiteness, revisit a vertex.
     Munkres: "begin with a vertex x0, choose edge e1 having x0 as end point,
     let x1 be the other end point. Let e2 be an edge different from e1 having x1
     as a vertex. Continue. Since T is finite, there must be an index n such that
     xn = xi for some i < n. Then xi, xi+1, ..., xn determines a CREP."

     The CREP + SC \\<Rightarrow> contradiction is the topological bridge:
     a non-backtracking cycle of arcs in an SC graph with coherent topology
     contradicts simply connectedness.\<close>
  \<comment> \<open>The walk + CREP argument is formalized by the following sorry.
     It requires showing: a CREP in a graph (1-dim CW complex) gives a non-trivial
     \\<pi>1 element. This follows from Theorem 84.7 (\\<pi>1 of graph is free on non-tree arcs)
     + the fact that CREPs correspond to reduced words in the free group.\<close>
  have hSC: "top1_simply_connected_on T TT"
    using assms(1) unfolding top1_is_tree_on_def by (by100 blast)
  \<comment> \<open>Step 4: Construct the walk. At each vertex, degree \\<ge> 2 gives a non-backtracking step.
     Walk visits finitely many directed arcs. By pigeonhole, some directed arc repeats.
     Between the two uses: a closed non-backtracking walk (CREP).
     The CREP in an SC space gives \\<bottom>.\<close>
  let ?V = "top1_graph_vertex_set T TT \<A>"
  have hep_fin: "\<forall>A0\<in>\<A>. finite (top1_arc_endpoints_on A0 (subspace_topology T TT A0))"
    using h2ep by (by100 force)
  have hV_fin: "finite ?V"
    unfolding top1_graph_vertex_set_def using assms(5) hep_fin by (by100 blast)
  \<comment> \<open>The vertex set is non-empty (card \\<ge> 2 arcs, each with endpoints).\<close>
  obtain x0 where hx0: "x0 \<in> ?V"
  proof -
    obtain A0 where "A0 \<in> \<A>" using assms(6) by (by100 force)
    from h2ep[rule_format, OF this]
    obtain a0 b0 where "top1_arc_endpoints_on A0 (subspace_topology T TT A0) = {a0, b0}" by (by100 blast)
    hence "a0 \<in> ?V" unfolding top1_graph_vertex_set_def using \<open>A0 \<in> \<A>\<close> by (by100 blast)
    thus ?thesis using that by (by100 blast)
  qed
  \<comment> \<open>Step 4: Case split on acyclicity.
     Case A (acyclic): forest\\_euler\\_formula gives V \\<ge> E + 1. But degree sum = 2E \\<ge> 2V
     gives E \\<ge> V. So E \\<ge> V \\<ge> E + 1, contradiction.
     Case B (has cycle): sc\\_graph\\_no\\_cycle gives \\<bottom> directly.\<close>
  show False
  proof (cases "\<exists>ws :: 'a set list. length ws \<ge> 2 \<and> distinct ws \<and> set ws \<subseteq> \<A> \<and>
      (\<forall>i < length ws. card (ws ! i \<inter> ws ! ((i + 1) mod length ws)) = 1) \<and>
      (\<forall>i < length ws. \<forall>j < length ws. i \<noteq> j \<longrightarrow>
          (\<forall>v w. ws ! i \<inter> ws ! ((i + 1) mod length ws) = {v} \<longrightarrow>
                 ws ! j \<inter> ws ! ((j + 1) mod length ws) = {w} \<longrightarrow> v \<noteq> w))")
    case True \<comment> \<open>Case B: has a simple cycle (card = 1, distinct shared vertices).\<close>
    then obtain ws :: "'a set list" where hwsB: "length ws \<ge> 2" "distinct ws" "set ws \<subseteq> \<A>"
        "\<forall>i < length ws. card (ws ! i \<inter> ws ! ((i + 1) mod length ws)) = 1"
        "\<forall>i < length ws. \<forall>j < length ws. i \<noteq> j \<longrightarrow>
          (\<forall>v w. ws ! i \<inter> ws ! ((i + 1) mod length ws) = {v} \<longrightarrow>
                 ws ! j \<inter> ws ! ((j + 1) mod length ws) = {w} \<longrightarrow> v \<noteq> w)"
      by (by100 auto)
    from sc_graph_no_cycle[OF assms(1) assms(2) assms(3) assms(4) assms(5) assms(7)
        this(1) this(2) this(3) this(4) this(5)]
    show False .
  next
    case False \<comment> \<open>Case A: acyclic (no simple cycle).\<close>
    hence hacyclic: "\<forall>ws :: 'a set list. length ws \<ge> 2 \<longrightarrow> distinct ws \<longrightarrow> set ws \<subseteq> \<A> \<longrightarrow>
        (\<forall>i < length ws. card (ws ! i \<inter> ws ! ((i + 1) mod length ws)) = 1) \<longrightarrow>
        (\<forall>i < length ws. \<forall>j < length ws. i \<noteq> j \<longrightarrow>
          (\<forall>v w. ws ! i \<inter> ws ! ((i + 1) mod length ws) = {v} \<longrightarrow>
                 ws ! j \<inter> ws ! ((j + 1) mod length ws) = {w} \<longrightarrow> v \<noteq> w)) \<longrightarrow> False"
      by (by100 blast)
    \<comment> \<open>Acyclic + all degrees \\<ge> 2 + finite \\<Rightarrow> False.
       Walk from any vertex: non-backtracking. Acyclic \\<Rightarrow> walk visits new vertices.
       Finite V \\<Rightarrow> walk must stop after card(V) steps.
       But degree \\<ge> 2 \\<Rightarrow> walk never stops. Contradiction.
       This is Munkres' proof of Lemma 84.2, purely combinatorial.\<close>
    \<comment> \<open>Construct the walk. Define step function and iterate.
       At each vertex v with previous arc e\\_prev: pick next arc e \\<noteq> e\\_prev containing v.
       Degree \\<ge> 2 guarantees such e exists. The walk visits new vertices (acyclicity).\<close>
    \<comment> \<open>For each vertex v and arc e with v \\<in> ep(e): the "other endpoint" of e from v.\<close>
    let ?ep2 = "\<lambda>A. top1_arc_endpoints_on A (subspace_topology T TT A)"
    have hshared_arc: "\<forall>v\<in>?V. \<forall>e\<in>\<A>. v \<in> ?ep2 e \<longrightarrow>
        (\<exists>e'\<in>\<A>. e' \<noteq> e \<and> v \<in> ?ep2 e')"
    proof (intro ballI impI)
      fix v e assume "v \<in> ?V" "e \<in> \<A>" "v \<in> ?ep2 e"
      from hshared[rule_format, OF \<open>e \<in> \<A>\<close> \<open>v \<in> ?ep2 e\<close>]
      obtain B where "B \<in> \<A>" "B \<noteq> e" "v \<in> B" by (by100 blast)
      have "v \<in> ?ep2 B"
      proof -
        have "v \<in> e \<inter> B" using \<open>v \<in> ?ep2 e\<close> \<open>v \<in> B\<close> unfolding top1_arc_endpoints_on_def by (by100 blast)
        have "e \<noteq> B" using \<open>B \<noteq> e\<close> by simp
        from assms(4)[rule_format, OF \<open>e \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>e \<noteq> B\<close>]
        have "e \<inter> B \<subseteq> ?ep2 B" by (by100 blast)
        thus ?thesis using \<open>v \<in> e \<inter> B\<close> by (by100 blast)
      qed
      thus "\<exists>e'\<in>\<A>. e' \<noteq> e \<and> v \<in> ?ep2 e'" using \<open>B \<in> \<A>\<close> \<open>B \<noteq> e\<close> by (by100 blast)
    qed
    \<comment> \<open>The walk visits distinct vertices. After card(V)+1 steps: must revisit.
       But revisit creates cycle (contradicting hacyclic). So walk can't reach card(V)+1 steps.
       But degree \\<ge> 2 guarantees it does. Contradiction.\<close>
    \<comment> \<open>Pick starting vertex and arc.\<close>
    obtain v0 where hv0: "v0 \<in> ?V"
    proof -
      obtain A0 where "A0 \<in> \<A>" using assms(6) by (by100 force)
      from h2ep[rule_format, OF this]
      obtain a0 b0 where "top1_arc_endpoints_on A0 (subspace_topology T TT A0) = {a0, b0}" by (by100 blast)
      hence "a0 \<in> ?V" unfolding top1_graph_vertex_set_def using \<open>A0 \<in> \<A>\<close> by (by100 blast)
      thus ?thesis using that by (by100 blast)
    qed
    obtain e0 where he0: "e0 \<in> \<A>" "v0 \<in> ?ep2 e0"
    proof -
      from hv0 obtain A0 where "A0 \<in> \<A>" "v0 \<in> ?ep2 A0"
        unfolding top1_graph_vertex_set_def by (by100 blast)
      thus ?thesis using that by (by100 blast)
    qed
    \<comment> \<open>The walk. At each step: current vertex v, previous arc e.
       Pick next arc e' \\<noteq> e with v \\<in> ep(e'). Go to the other endpoint v' of e'.\<close>
    \<comment> \<open>For the walk, we need the "other endpoint" function.\<close>
    \<comment> \<open>Actually, the walk visits vertices. We show the walk function is injective on
       {0..card(V)} using acyclicity. Pigeonhole gives the contradiction.\<close>
    \<comment> \<open>Simplified argument: the walk can take at least card(V) steps (degree \\<ge> 2 at each vertex).
       At each step it visits a new vertex (acyclic \\<Rightarrow> no revisit, because revisit \\<Rightarrow> cycle).
       So after card(V) steps: card(V) + 1 distinct vertices \\<subseteq> V, card(V) + 1 > card(V). Impossible.\<close>
    \<comment> \<open>Define the walk. walk n = (vertex at step n, arc used to reach it).
       At each step, pick a non-backtracking arc (using hshared\\_arc) and go to its other endpoint.\<close>
    define next_arc where "next_arc v e = (SOME e'. e' \<in> \<A> \<and> v \<in> ?ep2 e' \<and> e' \<noteq> e)" for v e
    define other_endpt where "other_endpt v e = (SOME v'. v' \<in> ?ep2 e \<and> v' \<noteq> v)" for v e
    \<comment> \<open>Walk: walk n = (current vertex, last arc used).\<close>
    define walk where "walk = rec_nat (v0, e0)
      (\<lambda>n (v, e). let e' = next_arc v e in (other_endpt v e', e'))"
    \<comment> \<open>Key properties of the walk (by induction on n):\<close>
    \<comment> \<open>Helper: next\\_arc gives a valid arc (from hshared\\_arc + SOME).\<close>
    have hnext_arc: "\<forall>v\<in>?V. \<forall>e\<in>\<A>. v \<in> ?ep2 e \<longrightarrow>
        next_arc v e \<in> \<A> \<and> v \<in> ?ep2 (next_arc v e) \<and> next_arc v e \<noteq> e"
    proof (intro ballI impI)
      fix v e assume "v \<in> ?V" "e \<in> \<A>" "v \<in> ?ep2 e"
      from hshared_arc[rule_format, OF this]
      have "\<exists>e'\<in>\<A>. e' \<noteq> e \<and> v \<in> ?ep2 e'" .
      hence "\<exists>e'. e' \<in> \<A> \<and> v \<in> ?ep2 e' \<and> e' \<noteq> e" by (by100 blast)
      from someI_ex[OF this]
      show "next_arc v e \<in> \<A> \<and> v \<in> ?ep2 (next_arc v e) \<and> next_arc v e \<noteq> e"
        unfolding next_arc_def by (by100 blast)
    qed
    \<comment> \<open>Helper: other\\_endpt gives the other endpoint.\<close>
    have hother_endpt: "\<forall>v. \<forall>e\<in>\<A>. v \<in> ?ep2 e \<longrightarrow>
        other_endpt v e \<in> ?ep2 e \<and> other_endpt v e \<noteq> v"
    proof (intro allI ballI impI)
      fix v e assume "e \<in> \<A>" "v \<in> ?ep2 e"
      from h2ep[rule_format, OF \<open>e \<in> \<A>\<close>]
      obtain a0 b0 where hab: "a0 \<noteq> b0" "?ep2 e = {a0, b0}" by (by100 blast)
      have "v \<in> {a0, b0}" using \<open>v \<in> ?ep2 e\<close> hab(2) by simp
      hence "\<exists>v'. v' \<in> ?ep2 e \<and> v' \<noteq> v" using hab by (by100 blast)
      from someI_ex[OF this]
      show "other_endpt v e \<in> ?ep2 e \<and> other_endpt v e \<noteq> v"
        unfolding other_endpt_def by (by100 blast)
    qed
    \<comment> \<open>Unfold walk at Suc n.\<close>
    have hwalk_suc: "\<And>n. walk (Suc n) = (let (v, e) = walk n in
        let e' = next_arc v e in (other_endpt v e', e'))"
      unfolding walk_def by simp
    have hwalk_suc_fst: "\<And>n. fst (walk (Suc n)) = other_endpt (fst (walk n)) (next_arc (fst (walk n)) (snd (walk n)))"
      using hwalk_suc by (simp add: case_prod_beta Let_def)
    have hwalk_suc_snd: "\<And>n. snd (walk (Suc n)) = next_arc (fst (walk n)) (snd (walk n))"
      using hwalk_suc by (simp add: case_prod_beta Let_def)
    have hwalk_props: "\<And>n. fst (walk n) \<in> ?V \<and> snd (walk n) \<in> \<A>
        \<and> fst (walk n) \<in> ?ep2 (snd (walk n))"
    proof -
      fix n show "fst (walk n) \<in> ?V \<and> snd (walk n) \<in> \<A> \<and> fst (walk n) \<in> ?ep2 (snd (walk n))"
      proof (induction n)
        case 0
        have "walk 0 = (v0, e0)" unfolding walk_def by simp
        thus ?case using hv0 he0 by simp
      next
        case (Suc n)
        have hv: "fst (walk n) \<in> ?V" and he: "snd (walk n) \<in> \<A>"
            and hve: "fst (walk n) \<in> ?ep2 (snd (walk n))"
          using Suc.IH by (by100 blast)+
        let ?e' = "next_arc (fst (walk n)) (snd (walk n))"
        from hnext_arc[rule_format, OF hv he hve]
        have he': "?e' \<in> \<A>" and hve': "fst (walk n) \<in> ?ep2 ?e'" and hne': "?e' \<noteq> snd (walk n)"
          by (by100 blast)+
        from hother_endpt[rule_format, OF he' hve']
        have hv': "other_endpt (fst (walk n)) ?e' \<in> ?ep2 ?e'"
            and hv'_ne: "other_endpt (fst (walk n)) ?e' \<noteq> fst (walk n)"
          by (by100 blast)+
        have hsuc_fst: "fst (walk (Suc n)) = other_endpt (fst (walk n)) ?e'"
          using hwalk_suc_fst by simp
        have hsuc_snd: "snd (walk (Suc n)) = ?e'" using hwalk_suc_snd by simp
        have "fst (walk (Suc n)) \<in> ?V"
        proof -
          have "other_endpt (fst (walk n)) ?e' \<in> ?ep2 ?e'" using hv' .
          hence "other_endpt (fst (walk n)) ?e' \<in> (\<Union>A\<in>\<A>. ?ep2 A)" using he' by (by100 blast)
          thus ?thesis using hsuc_fst unfolding top1_graph_vertex_set_def by simp
        qed
        moreover have "snd (walk (Suc n)) \<in> \<A>" using hsuc_snd he' by simp
        moreover have "fst (walk (Suc n)) \<in> ?ep2 (snd (walk (Suc n)))"
          using hsuc_fst hsuc_snd hv' by simp
        ultimately show ?case by (by100 blast)
      qed
    qed
    \<comment> \<open>Walk visits at most card(V) distinct vertices. By pigeonhole: must revisit.\<close>
    have "\<exists>i j. i < j \<and> j \<le> card ?V \<and> fst (walk i) = fst (walk j)"
    proof (rule ccontr)
      assume hno_rev: "\<not> (\<exists>i j. i < j \<and> j \<le> card ?V \<and> fst (walk i) = fst (walk j))"
      hence hinj: "\<forall>i j. i \<le> card ?V \<longrightarrow> j \<le> card ?V \<longrightarrow> i \<noteq> j \<longrightarrow> fst (walk i) \<noteq> fst (walk j)"
      proof (intro allI impI)
        fix i j assume "i \<le> card ?V" "j \<le> card ?V" "i \<noteq> j"
        show "fst (walk i) \<noteq> fst (walk j)"
        proof (cases "i < j")
          case True thus ?thesis using hno_rev \<open>j \<le> card ?V\<close> by (by100 blast)
        next
          case False
          hence "j < i" using \<open>i \<noteq> j\<close> by linarith
          show ?thesis
          proof
            assume heq: "fst (walk i) = fst (walk j)"
            hence "fst (walk j) = fst (walk i)" by simp
            with \<open>j < i\<close> \<open>i \<le> card ?V\<close> have "\<exists>i j. i < j \<and> j \<le> card ?V \<and> fst (walk i) = fst (walk j)"
              by (by100 blast)
            with hno_rev show False by (by100 blast)
          qed
        qed
      qed
      have "inj_on (fst \<circ> walk) {..card ?V}"
        unfolding inj_on_def comp_def using hinj by (by100 blast)
      moreover have "(fst \<circ> walk) ` {..card ?V} \<subseteq> ?V"
      proof (intro image_subsetI)
        fix n assume "n \<in> {..card ?V}"
        hence "n \<le> card ?V" by simp
        thus "(fst \<circ> walk) n \<in> ?V" using hwalk_props by (by100 force)
      qed
      moreover have "card {..card ?V} = card ?V + 1" by simp
      ultimately have "card ?V + 1 \<le> card ?V"
        using card_inj_on_le[OF \<open>inj_on _ _\<close> \<open>_ ` _ \<subseteq> ?V\<close> hV_fin] by linarith
      thus False by linarith
    qed
    \<comment> \<open>Pick the SHORTEST revisit (minimize j - i) for the distinctness argument.\<close>
    then obtain i0 j0 where "i0 < j0" "j0 \<le> card ?V" "fst (walk i0) = fst (walk j0)"
      by (by100 blast)
    \<comment> \<open>Find the minimum difference among all revisit pairs.\<close>
    define P where "P d \<longleftrightarrow> (\<exists>i' j'. i' < j' \<and> j' \<le> card ?V \<and> fst (walk i') = fst (walk j') \<and> j' - i' = d)" for d
    have "P (j0 - i0)" unfolding P_def using \<open>i0 < j0\<close> \<open>j0 \<le> card ?V\<close> \<open>fst (walk i0) = fst (walk j0)\<close>
      by (by100 blast)
    define dmin where "dmin = (LEAST d. P d)"
    have hP_dmin: "P dmin"
    proof -
      have "\<exists>d. P d" using \<open>P (j0 - i0)\<close> by (by100 blast)
      then obtain d0 where "P d0" by (by100 blast)
      have "(LEAST d. P d) \<le> d0" by (rule Least_le) (rule \<open>P d0\<close>)
      show ?thesis unfolding dmin_def
        using LeastI_ex[OF \<open>\<exists>d. P d\<close>] by simp
    qed
    have hP_min: "\<forall>d. P d \<longrightarrow> dmin \<le> d"
    proof (intro allI impI)
      fix d assume "P d"
      show "dmin \<le> d" unfolding dmin_def by (rule Least_le) (rule \<open>P d\<close>)
    qed
    from hP_dmin obtain i j where hij: "i < j" "j \<le> card ?V" "fst (walk i) = fst (walk j)"
        and hdmin_eq: "j - i = dmin" unfolding P_def by (by100 blast)
    have hmin: "\<forall>i' j'. i' < j' \<and> j' \<le> card ?V \<and> fst (walk i') = fst (walk j') \<longrightarrow> j - i \<le> j' - i'"
    proof (intro allI impI)
      fix i' j' assume "i' < j' \<and> j' \<le> card ?V \<and> fst (walk i') = fst (walk j')"
      hence "P (j' - i')" unfolding P_def by (by100 blast)
      from hP_min[rule_format, OF this] show "j - i \<le> j' - i'" using hdmin_eq by linarith
    qed
    \<comment> \<open>The arcs walk(i+1), ..., walk(j) form a cycle. Extract them and apply hacyclic.\<close>
    \<comment> \<open>The cycle is: [snd(walk(i+1)), ..., snd(walk(j))], with j-i \\<ge> 1 arcs.
       Actually need \\<ge> 2 arcs for hacyclic. Since arcs have distinct endpoints,
       a 1-arc cycle is impossible (would need fst(walk i) = fst(walk(i+1)) but
       the "other endpoint" is always different). So j - i \\<ge> 2.\<close>
    \<comment> \<open>j - i \\<ge> 2: walk(i+1) has different vertex from walk(i) (other\\_endpt gives v \\<noteq> prev\\_v).\<close>
    have hji_ge2: "j - i \<ge> 2"
    proof -
      \<comment> \<open>fst(walk(Suc i)) \\<noteq> fst(walk i): other\\_endpt gives different vertex.\<close>
      have "fst (walk (Suc i)) \<noteq> fst (walk i)"
      proof -
        let ?v = "fst (walk i)" and ?e = "snd (walk i)"
        let ?e' = "next_arc ?v ?e"
        have "fst (walk (Suc i)) = other_endpt ?v ?e'" using hwalk_suc_fst by simp
        moreover have "?e' \<in> \<A>" and "?v \<in> ?ep2 ?e'"
          using hnext_arc hwalk_props by (by100 blast)+
        moreover have "other_endpt ?v ?e' \<noteq> ?v"
          using hother_endpt \<open>?e' \<in> \<A>\<close> \<open>?v \<in> ?ep2 ?e'\<close> by (by100 blast)
        ultimately show ?thesis by simp
      qed
      \<comment> \<open>Since fst(walk i) = fst(walk j) but fst(walk(Suc i)) \\<noteq> fst(walk i):
         Suc i \\<noteq> j (otherwise fst(walk(Suc i)) = fst(walk j) = fst(walk i)). So j > Suc i.\<close>
      hence "fst (walk (Suc i)) \<noteq> fst (walk j)" using hij(3) by simp
      hence "Suc i \<noteq> j" by (by100 force)
      hence "j > Suc i" using hij(1) by linarith
      thus ?thesis by linarith
    qed
    \<comment> \<open>Form the cycle: list of arcs from walk(i+1) to walk(j).\<close>
    let ?ws = "map (\<lambda>k. snd (walk k)) [Suc i ..< Suc j]"
    have hws_len: "length ?ws = j - i"
      using hij(1) by simp
    hence hws_len2: "length ?ws \<ge> 2" using hji_ge2 by linarith
    have hws_sub: "set ?ws \<subseteq> \<A>"
    proof -
      have "\<forall>k. Suc i \<le> k \<and> k < Suc j \<longrightarrow> snd (walk k) \<in> \<A>"
        using hwalk_props by (by100 blast)
      thus ?thesis by (by100 auto)
    qed
    \<comment> \<open>Consecutive arcs share a vertex (from the walk structure).\<close>
    \<comment> \<open>Key: fst(walk k) is a point in both snd(walk k) and snd(walk(Suc k)).
       This gives adjacency of consecutive arcs in the cycle.\<close>
    have hwalk_shared: "\<And>k. fst (walk k) \<in> snd (walk k) \<and> fst (walk k) \<in> snd (walk (Suc k))"
    proof -
      fix k
      have "fst (walk k) \<in> ?ep2 (snd (walk k))" using hwalk_props by (by100 blast)
      hence hk: "fst (walk k) \<in> snd (walk k)"
        unfolding top1_arc_endpoints_on_def by (by100 blast)
      have "snd (walk (Suc k)) = next_arc (fst (walk k)) (snd (walk k))" using hwalk_suc_snd .
      moreover have "fst (walk k) \<in> ?ep2 (next_arc (fst (walk k)) (snd (walk k)))"
        using hnext_arc hwalk_props by (by100 blast)
      hence "fst (walk k) \<in> next_arc (fst (walk k)) (snd (walk k))"
        unfolding top1_arc_endpoints_on_def by (by100 blast)
      ultimately have "fst (walk k) \<in> snd (walk (Suc k))" by simp
      with hk show "fst (walk k) \<in> snd (walk k) \<and> fst (walk k) \<in> snd (walk (Suc k))" by (by100 blast)
    qed
    \<comment> \<open>Consecutive arcs in the cycle share a vertex. Needs nth\\_map lemma for lists.\<close>
    \<comment> \<open>nth of the walk cycle: ?ws ! idx = snd(walk(Suc i + idx)).\<close>
    have hws_nth: "\<And>idx. idx < j - i \<Longrightarrow> ?ws ! idx = snd (walk (Suc i + idx))"
    proof -
      fix idx assume hidx: "idx < j - i"
      \<comment> \<open>length [Suc i..<Suc j] = Suc j - Suc i = j - i (since i < j).\<close>
      have hlen_upt: "length [Suc i..<Suc j] = j - i" using hij(1) by simp
      hence hidx_len: "idx < length [Suc i..<Suc j]" using hidx by linarith
      \<comment> \<open>nth\\_map: (map f xs) ! n = f (xs ! n) when n < length xs.\<close>
      have h1: "(map (\<lambda>k. snd (walk k)) [Suc i..<Suc j]) ! idx =
          (\<lambda>k. snd (walk k)) ([Suc i..<Suc j] ! idx)"
        using nth_map[OF hidx_len, of "\<lambda>k. snd (walk k)"] .
      \<comment> \<open>nth\\_upt: [a..<b] ! k = a + k when a + k < b.\<close>
      have "Suc i + idx < Suc j" using hidx hij(1) by linarith
      hence h2: "[Suc i..<Suc j] ! idx = Suc i + idx" by (rule nth_upt)
      show "?ws ! idx = snd (walk (Suc i + idx))" using h1 h2 by simp
    qed
    have hws_adj: "\<forall>idx < length ?ws. ?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws) \<noteq> {}"
    proof (intro allI impI)
      fix idx assume hidx: "idx < length ?ws"
      hence hidx': "idx < j - i" using hws_len by linarith
      show "?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws) \<noteq> {}"
      proof (cases "idx + 1 < j - i")
        case True \<comment> \<open>Not the wrap-around.\<close>
        hence hmod: "(idx + 1) mod length ?ws = idx + 1" using hws_len by simp
        have "?ws ! idx = snd (walk (Suc i + idx))" using hws_nth hidx' .
        moreover have "?ws ! (idx + 1) = snd (walk (Suc (Suc i + idx)))"
          using hws_nth[OF True] by simp
        moreover have "fst (walk (Suc i + idx)) \<in> snd (walk (Suc i + idx))"
            and "fst (walk (Suc i + idx)) \<in> snd (walk (Suc (Suc i + idx)))"
          using hwalk_shared by (by100 blast)+
        ultimately have "fst (walk (Suc i + idx)) \<in> ?ws ! idx \<inter> ?ws ! (idx + 1)" by (by100 blast)
        hence "?ws ! idx \<inter> ?ws ! (idx + 1) \<noteq> {}" by (by100 blast)
        thus ?thesis using hmod by simp
      next
        case False \<comment> \<open>Wrap-around: idx = j - i - 1.\<close>
        hence "idx = j - i - 1" using hidx' by linarith
        hence "idx + 1 = j - i" using hidx' by linarith
        hence hmod: "(idx + 1) mod length ?ws = 0"
          using hws_len hji_ge2 by simp
        have "?ws ! idx = snd (walk j)"
          using hws_nth[OF hidx'] \<open>idx = j - i - 1\<close> hij(1) by simp
        moreover have "?ws ! 0 = snd (walk (Suc i))"
        proof -
          have "0 < j - i" using hji_ge2 by linarith
          from hws_nth[OF this] show ?thesis by simp
        qed
        \<comment> \<open>Shared point: fst(walk i) = fst(walk j).\<close>
        moreover have "fst (walk j) \<in> snd (walk j)" using hwalk_shared by (by100 blast)
        moreover have "fst (walk i) \<in> snd (walk (Suc i))" using hwalk_shared by (by100 blast)
        ultimately have "fst (walk j) \<in> snd (walk j)" and "fst (walk j) \<in> snd (walk (Suc i))"
          using hij(3) by simp_all
        hence "fst (walk j) \<in> ?ws ! idx \<inter> ?ws ! 0"
          using \<open>?ws ! idx = snd (walk j)\<close> \<open>?ws ! 0 = snd (walk (Suc i))\<close> by (by100 blast)
        hence "?ws ! idx \<inter> ?ws ! 0 \<noteq> {}" by (by100 blast)
        thus ?thesis using hmod by simp
      qed
    qed
    \<comment> \<open>Vertex distinctness: walk vertices in {Suc i, ..., j-1} are pairwise distinct.\<close>
    have hv_distinct: "\<forall>k l. Suc i \<le> k \<and> k < j \<and> Suc i \<le> l \<and> l < j \<and> k \<noteq> l
        \<longrightarrow> fst (walk k) \<noteq> fst (walk l)"
      proof (intro allI impI)
        fix k l assume hkl: "Suc i \<le> k \<and> k < j \<and> Suc i \<le> l \<and> l < j \<and> k \<noteq> l"
        show "fst (walk k) \<noteq> fst (walk l)"
        proof
          assume heq: "fst (walk k) = fst (walk l)"
          have "k < l \<or> l < k" using hkl by linarith
          thus False
          proof
            assume "k < l"
            hence "l - k < j - i" using hkl by linarith
            moreover have "k < l \<and> l \<le> card ?V \<and> fst (walk k) = fst (walk l)"
              using \<open>k < l\<close> heq hkl hij(2) by linarith
            ultimately show False using hmin[rule_format, of k l] by linarith
          next
            assume "l < k"
            hence "k - l < j - i" using hkl by linarith
            have "fst (walk l) = fst (walk k)" using heq by simp
            have "l < k \<and> k \<le> card ?V \<and> fst (walk l) = fst (walk k)"
              using \<open>l < k\<close> \<open>fst (walk l) = fst (walk k)\<close> hkl hij(2) by linarith
            hence "j - i \<le> k - l" using hmin[rule_format] by (by100 blast)
            thus False using \<open>k - l < j - i\<close> by linarith
          qed
        qed
      qed
    \<comment> \<open>Arcs are distinct (from vertex distinctness + endpoint analysis).\<close>
    have hws_dist: "distinct ?ws"
    proof -
      \<comment> \<open>Second: distinct vertices \\<Rightarrow> distinct arcs. If snd(walk k) = snd(walk l) for k \\<noteq> l,
         then the arc connects the same endpoint pair. But fst(walk(k-1)) and fst(walk k) are
         both endpoints of snd(walk k). Similarly for l. Since intermediate vertices are distinct,
         the endpoint pairs must differ, so the arcs differ.\<close>
      \<comment> \<open>More precisely: the arc snd(walk k) for Suc i \\<le> k \\<le> j has fst(walk(k-1)) and fst(walk k)
         as its two endpoints (one arrived-from, one arrived-at). Different k values give
         different arrived-at vertices (from hv\\_distinct), hence different arcs.\<close>
      \<comment> \<open>Proof: ?ws is distinct iff ?ws ! k \\<noteq> ?ws ! l for all 0 \\<le> k < l < length ?ws.\<close>
      show "distinct ?ws"
      proof (rule distinct_conv_nth[THEN iffD2], intro allI impI)
        fix k l assume hkl: "k < length ?ws" "l < length ?ws" "k \<noteq> l"
        show "?ws ! k \<noteq> ?ws ! l"
        proof
          assume "?ws ! k = ?ws ! l"
          \<comment> \<open>?ws ! k = snd(walk(Suc i + k)), ?ws ! l = snd(walk(Suc i + l)).\<close>
          have hk: "k < j - i" using hkl(1) hws_len by linarith
          have hl: "l < j - i" using hkl(2) hws_len by linarith
          have "snd (walk (Suc i + k)) = snd (walk (Suc i + l))"
            using \<open>?ws ! k = ?ws ! l\<close> hws_nth[OF hk] hws_nth[OF hl] by simp
          \<comment> \<open>Both arcs have the walk vertex as an endpoint (the "arrived-at" vertex).
             fst(walk(Suc i + k)) \\<in> ep(snd(walk(Suc i + k))) and
             fst(walk(Suc i + l)) \\<in> ep(snd(walk(Suc i + l))).
             Same arc \\<Rightarrow> same endpoint set \\<Rightarrow> {fst(walk(Suc i + k - 1)), fst(walk(Suc i + k))}
             = {fst(walk(Suc i + l - 1)), fst(walk(Suc i + l))}.
             But these are distinct vertices. Contradiction.\<close>
          \<comment> \<open>The walk arc snd(walk m) has endpoints fst(walk(m-1)) and fst(walk m)
             (where fst(walk(m-1)) is the vertex we came from, fst(walk m) = other\\_endpt).\<close>
          \<comment> \<open>Actually, snd(walk m) has fst(walk(m-1)) as an endpoint (from next\\_arc: fst(walk(m-1)) \\<in> ep)
             and fst(walk m) as the other endpoint (from other\\_endpt).\<close>
          \<comment> \<open>So ep(snd(walk m)) = {fst(walk(m-1)), fst(walk m)} for m \\<ge> 1.\<close>
          \<comment> \<open>Same arc \\<Rightarrow> same endpoint set. With distinct vertices: gives equality of pairs \\<Rightarrow> k = l.\<close>
          \<comment> \<open>The arc snd(walk(Suc i + k)) has endpoint set {fst(walk(i+k)), fst(walk(Suc i+k))}.
             Same arc implies same endpoint set. But with k \\<noteq> l and distinct intermediate
             vertices (hv\\_distinct), the endpoint pairs cannot match. Contradiction.\<close>
          \<comment> \<open>Key: fst(walk(Suc i + k)) is determined by its arc (it's the unique vertex in ep
             that differs from fst(walk(i+k))). Same arc + different predecessor vertex
             = different arrived-at vertex. But same arc means same endpoint pair, forcing
             equal predecessor and arrived-at vertices. With hv\\_distinct: k = l.\<close>
          \<comment> \<open>Endpoint pair: ep(snd(walk m)) = {fst(walk(m-1)), fst(walk m)} for the walk.\<close>
          let ?mk = "Suc i + k" and ?ml = "Suc i + l"
          have hpred_k: "fst (walk (i + k)) \<in> ?ep2 (snd (walk ?mk))"
          proof -
            have "snd (walk ?mk) = next_arc (fst (walk (i + k))) (snd (walk (i + k)))"
              using hwalk_suc_snd[of "i + k"] by simp
            moreover have "fst (walk (i+k)) \<in> ?ep2 (next_arc (fst (walk (i+k))) (snd (walk (i+k))))"
              using hnext_arc hwalk_props by (by100 blast)
            ultimately show ?thesis by simp
          qed
          have hpred_l: "fst (walk (i + l)) \<in> ?ep2 (snd (walk ?ml))"
          proof -
            have "snd (walk ?ml) = next_arc (fst (walk (i + l))) (snd (walk (i + l)))"
              using hwalk_suc_snd[of "i + l"] by simp
            moreover have "fst (walk (i+l)) \<in> ?ep2 (next_arc (fst (walk (i+l))) (snd (walk (i+l))))"
              using hnext_arc hwalk_props by (by100 blast)
            ultimately show ?thesis by simp
          qed
          have harr_k: "fst (walk ?mk) \<in> ?ep2 (snd (walk ?mk))" using hwalk_props by (by100 blast)
          have harr_l: "fst (walk ?ml) \<in> ?ep2 (snd (walk ?ml))" using hwalk_props by (by100 blast)
          have hne_k: "fst (walk ?mk) \<noteq> fst (walk (i + k))"
          proof -
            have "fst (walk ?mk) = other_endpt (fst (walk (i+k))) (next_arc (fst (walk (i+k))) (snd (walk (i+k))))"
              using hwalk_suc_fst[of "i+k"] by simp
            moreover have "next_arc (fst (walk (i+k))) (snd (walk (i+k))) \<in> \<A>"
              using hnext_arc hwalk_props by (by100 blast)
            moreover have hik_ep: "fst (walk (i+k)) \<in> ?ep2 (next_arc (fst (walk (i+k))) (snd (walk (i+k))))"
              using hnext_arc hwalk_props by (by100 blast)
            moreover have hik_arc: "next_arc (fst (walk (i+k))) (snd (walk (i+k))) \<in> \<A>"
              using hnext_arc hwalk_props by (by100 blast)
            moreover have "other_endpt (fst (walk (i+k))) (next_arc (fst (walk (i+k))) (snd (walk (i+k)))) \<noteq> fst (walk (i+k))"
              using hother_endpt[rule_format, OF hik_arc hik_ep] by (by100 blast)
            ultimately show ?thesis by simp
          qed
          \<comment> \<open>ep has exactly 2 elements, both known. Same arc \\<Rightarrow> same ep.\<close>
          have "?ep2 (snd (walk ?mk)) = ?ep2 (snd (walk ?ml))"
            using \<open>snd (walk ?mk) = snd (walk ?ml)\<close> by simp
          hence hep_eq: "{fst (walk (i+k)), fst (walk ?mk)} \<subseteq> ?ep2 (snd (walk ?ml))
              \<and> {fst (walk (i+l)), fst (walk ?ml)} \<subseteq> ?ep2 (snd (walk ?mk))"
            using hpred_k harr_k hpred_l harr_l by (by100 blast)
          \<comment> \<open>The arrived-at vertex fst(walk ?mk) is in ep(snd(walk ?ml)) = {fst(walk(i+l)), fst(walk ?ml)}.
             So fst(walk ?mk) = fst(walk(i+l)) or fst(walk ?mk) = fst(walk ?ml).\<close>
          have "fst (walk ?mk) \<in> {fst (walk (i+l)), fst (walk ?ml)}"
          proof -
            have "fst (walk ?mk) \<in> ?ep2 (snd (walk ?ml))"
              using harr_k \<open>?ep2 (snd (walk ?mk)) = ?ep2 (snd (walk ?ml))\<close> by simp
            moreover from h2ep[rule_format] hwalk_props
            have "?ep2 (snd (walk ?ml)) \<subseteq> {fst (walk (i+l)), fst (walk ?ml)}"
            proof -
              have "snd (walk ?ml) \<in> \<A>" using hwalk_props by (by100 blast)
              from h2ep[rule_format, OF this]
              obtain a b where hab: "a \<noteq> b" "?ep2 (snd (walk ?ml)) = {a, b}" by (by100 blast)
              have "fst (walk (i+l)) \<in> {a, b}" using hpred_l hab(2) by simp
              have "fst (walk ?ml) \<in> {a, b}" using harr_l hab(2) by simp
              have "fst (walk ?ml) \<noteq> fst (walk (i+l))"
              proof -
                have "fst (walk ?ml) = other_endpt (fst (walk (i+l))) (next_arc (fst (walk (i+l))) (snd (walk (i+l))))"
                  using hwalk_suc_fst[of "i+l"] by simp
                moreover have "next_arc (fst (walk (i+l))) (snd (walk (i+l))) \<in> \<A>"
                  using hnext_arc hwalk_props by (by100 blast)
                moreover have hil_ep: "fst (walk (i+l)) \<in> ?ep2 (next_arc (fst (walk (i+l))) (snd (walk (i+l))))"
                  using hnext_arc hwalk_props by (by100 blast)
                moreover have hil_arc: "next_arc (fst (walk (i+l))) (snd (walk (i+l))) \<in> \<A>"
                  using hnext_arc hwalk_props by (by100 blast)
                moreover have "other_endpt (fst (walk (i+l))) (next_arc (fst (walk (i+l))) (snd (walk (i+l)))) \<noteq> fst (walk (i+l))"
                  using hother_endpt[rule_format, OF hil_arc hil_ep] by (by100 blast)
                ultimately show ?thesis by simp
              qed
              hence "{a, b} = {fst (walk (i+l)), fst (walk ?ml)}"
                using \<open>fst (walk (i+l)) \<in> {a, b}\<close> \<open>fst (walk ?ml) \<in> {a, b}\<close> hab(1) by (by100 force)
              thus ?thesis using hab(2) by (by100 blast)
            qed
            ultimately show ?thesis by (by100 blast)
          qed
          hence "fst (walk ?mk) = fst (walk (i+l)) \<or> fst (walk ?mk) = fst (walk ?ml)"
            by (by100 blast)
          thus False
          proof
            assume hmk_ml: "fst (walk ?mk) = fst (walk ?ml)"
            \<comment> \<open>Both ?mk, ?ml \\<in> {Suc i, ..., j}. Need case split for boundary j.\<close>
            have "?mk \<le> j" using hk by linarith
            have "?ml \<le> j" using hl by linarith
            \<comment> \<open>If both < j: hv\\_distinct gives ?mk = ?ml, hence k = l. Contradiction.\<close>
            \<comment> \<open>If ?mk = j: fst(walk j) = fst(walk i). Then fst(walk ?ml) = fst(walk i).
               hmin gives j-i \\<le> ?ml - i = l+1 and j-i \\<le> j - ?ml = j-i-l-1. Second gives l+1+j-i-l-1 \\<le> j-i, trivially true.
               But also ?ml < j (from hl: l < j-i, so ?ml = Suc i+l < Suc i + j-i = j+1, but could be = j).
               If ?ml = j too: k = l = j-i-1, contradicting k \\<noteq> l... unless both = j-i-1.
               Since k \\<noteq> l and both \\<le> j-i-1: at most one = j-i-1.\<close>
            \<comment> \<open>Actually: if ?mk = j and ?ml < j: fst(walk(j)) = fst(walk(i)) and fst(walk ?ml) = fst(walk(j)) = fst(walk(i)).
               Then hmin: j-i \\<le> ?ml - i = l+1. But l < j-i. So l+1 \\<le> j-i \\<le> l+1, giving j-i = l+1.
               Also ?mk = j means k = j-i-1 = l. So k = l. Contradiction with k \\<noteq> l.\<close>
            have "?mk = ?ml"
            proof (cases "?mk < j")
              case True
              show ?thesis
              proof (cases "?ml < j")
                case True
                from hv_distinct[rule_format, of ?mk ?ml]
                show ?thesis using hmk_ml \<open>?mk < j\<close> True by (by100 force)
              next
                case False
                hence "?ml = j" using \<open>?ml \<le> j\<close> by linarith
                hence "fst (walk ?ml) = fst (walk i)" using hij(3) by simp
                hence "fst (walk ?mk) = fst (walk i)" using hmk_ml by simp
                \<comment> \<open>?mk \\<in> {Suc i, ..., j-1}. fst(walk ?mk) = fst(walk i). hmin: j-i \\<le> ?mk - i.\<close>
                have "fst (walk i) = fst (walk ?mk)" using \<open>fst (walk ?mk) = fst (walk i)\<close> by simp
                have "i < ?mk \<and> ?mk \<le> card ?V \<and> fst (walk i) = fst (walk ?mk)"
                  using \<open>?mk < j\<close> hij(2) \<open>fst (walk i) = fst (walk ?mk)\<close> by linarith
                hence "j - i \<le> ?mk - i" using hmin[rule_format] by (by100 blast)
                hence "j \<le> ?mk" by linarith
                thus ?thesis using \<open>?mk < j\<close> by linarith
              qed
            next
              case False
              hence "?mk = j" using \<open>?mk \<le> j\<close> by linarith
              show ?thesis
              proof (cases "?ml < j")
                case True
                have "fst (walk ?mk) = fst (walk i)" using \<open>?mk = j\<close> hij(3) by simp
                hence "fst (walk ?ml) = fst (walk i)" using hmk_ml by simp
                have "fst (walk i) = fst (walk ?ml)" using \<open>fst (walk ?ml) = fst (walk i)\<close> by simp
                have "i < ?ml \<and> ?ml \<le> card ?V \<and> fst (walk i) = fst (walk ?ml)"
                  using True hij(2) \<open>fst (walk i) = fst (walk ?ml)\<close> by linarith
                hence "j - i \<le> ?ml - i" using hmin[rule_format] by (by100 blast)
                hence "j \<le> ?ml" by linarith
                thus ?thesis using True by linarith
              next
                case False
                hence "?ml = j" using \<open>?ml \<le> j\<close> by linarith
                thus ?thesis using \<open>?mk = j\<close> by linarith
              qed
            qed
            hence "k = l" by linarith
            thus False using hkl(3) by (by100 blast)
          next
            assume heq: "fst (walk ?mk) = fst (walk (i + l))"
            \<comment> \<open>Case 2 of doubleton equality: cross-matching.
               fst(walk(Suc i+k)) = fst(walk(i+l)) and fst(walk(i+k)) = fst(walk(Suc i+l)).
               Analysis with hv\\_distinct + hmin + boundary cases gives contradiction.\<close>
            \<comment> \<open>From same arc + fst(walk ?mk) = fst(walk(i+l)):
               the other equality gives fst(walk(i+k)) = fst(walk ?ml) or fst(walk(i+k)) = fst(walk(i+l)).
               Case fst(walk(i+k)) = fst(walk(i+l)): hv\\_distinct/hmin gives k=l. Contradiction.
               Case fst(walk(i+k)) = fst(walk ?ml): gives k = l+1 from hv\\_distinct/hmin.
               Then j-i = 2 (from hmin + revisit). So k=1, l=0.
               But then snd(walk(Suc i)) = snd(walk(Suc i+1)) = consecutive arcs.
               Non-backtracking: snd(walk(Suc m)) \\<noteq> snd(walk m). Contradiction.\<close>
            \<comment> \<open>Step 1: fst(walk(i+k)) must be in {fst(walk(i+l)), fst(walk ?ml)} (from ep of the same arc).\<close>
            have "fst (walk (i+k)) \<in> ?ep2 (snd (walk ?mk))" using hpred_k .
            hence "fst (walk (i+k)) \<in> ?ep2 (snd (walk ?ml))"
              using \<open>?ep2 (snd (walk ?mk)) = ?ep2 (snd (walk ?ml))\<close> by simp
            \<comment> \<open>ep(snd(walk ?ml)) = {fst(walk(i+l)), fst(walk ?ml)} (2-element set, both known endpoints).\<close>
            \<comment> \<open>So fst(walk(i+k)) \\<in> {fst(walk(i+l)), fst(walk ?ml)}.\<close>
            \<comment> \<open>Step 2: If fst(walk(i+k)) = fst(walk(i+l)): hv\\_distinct/hmin gives k = l \\<Rightarrow> contradiction.\<close>
            \<comment> \<open>Step 3: If fst(walk(i+k)) = fst(walk ?ml): gives k = l+1 then j-i = 2, k=1, l=0.
               Non-backtracking on consecutive arcs gives contradiction.\<close>
            \<comment> \<open>The non-backtracking property: snd(walk(Suc m)) \\<noteq> snd(walk m).\<close>
            have hnonback: "\<And>m. snd (walk (Suc m)) \<noteq> snd (walk m)"
            proof -
              fix m
              have "snd (walk (Suc m)) = next_arc (fst (walk m)) (snd (walk m))" using hwalk_suc_snd .
              moreover have "next_arc (fst (walk m)) (snd (walk m)) \<noteq> snd (walk m)"
                using hnext_arc hwalk_props by (by100 blast)
              ultimately show "snd (walk (Suc m)) \<noteq> snd (walk m)" by simp
            qed
            \<comment> \<open>The full argument for Case 2 requires careful position arithmetic
               with boundary handling at i and j. All cases lead to either:
               (a) k = l via hv\\_distinct/hmin, or
               (b) |k - l| = 1, giving consecutive arcs equal, violating non-backtracking.\<close>
            \<comment> \<open>|k - l| = 1 \\<Rightarrow> consecutive arcs equal \\<Rightarrow> hnonback contradiction.\<close>
            have hkl_ne_1: "\<not> (k + 1 = l \<or> l + 1 = k)"
            proof
              assume "k + 1 = l \<or> l + 1 = k"
              thus False
              proof
                assume "k + 1 = l"
                hence "Suc i + l = Suc (Suc i + k)" by linarith
                hence "snd (walk (Suc (Suc i + k))) = snd (walk (Suc i + k))"
                  using \<open>snd (walk ?mk) = snd (walk ?ml)\<close> by simp
                thus False using hnonback[of "Suc i + k"] by simp
              next
                assume "l + 1 = k"
                hence "Suc i + k = Suc (Suc i + l)" by linarith
                hence "snd (walk (Suc (Suc i + l))) = snd (walk (Suc i + l))"
                  using \<open>snd (walk ?mk) = snd (walk ?ml)\<close> by simp
                thus False using hnonback[of "Suc i + l"] by simp
              qed
            qed
            \<comment> \<open>From heq (fst(walk ?mk) = fst(walk(i+l))) and hv\\_distinct/hmin:
               ?mk and i+l are "close" (same vertex \\<Rightarrow> same position mod boundary).
               Combined with |k-l| \\<noteq> 1: derive contradiction.\<close>
            \<comment> \<open>heq: fst(walk ?mk) = fst(walk(i+l)). Positions ?mk = Suc i+k and i+l.
               Both \\<le> j. If both in {Suc i, ..., j-1}: hv\\_distinct gives Suc i+k = i+l, k+1=l. But hkl\\_ne\\_1.\<close>
            \<comment> \<open>Detailed position analysis with hv\\_distinct + hmin + hkl\\_ne\\_1:
               Interior case: Suc i+k = i+l \\<Rightarrow> k+1=l \\<Rightarrow> contradicts hkl\\_ne\\_1.
               Boundary cases: k=j-i-1, l=0, j=i+2, |k-l|=1 \\<Rightarrow> contradicts hkl\\_ne\\_1.\<close>
            \<comment> \<open>Case analysis on whether positions are in interior or boundary.\<close>
            show False
            proof (cases "l = 0")
              case True \<comment> \<open>l = 0: heq gives fst(walk(Suc i+k)) = fst(walk(i)) = fst(walk(j)).\<close>
              hence "fst (walk ?mk) = fst (walk i)" using heq by simp
              \<comment> \<open>hmin gives j-i \\<le> ?mk - i = k+1. With k < j-i: k+1 = j-i, so ?mk = j.\<close>
              have "i < ?mk" by linarith
              have "?mk \<le> card ?V" using hk hij(2) by linarith
              have "fst (walk i) = fst (walk ?mk)" using \<open>fst (walk ?mk) = fst (walk i)\<close> by simp
              hence "j - i \<le> ?mk - i" using hmin[rule_format, of i ?mk] \<open>i < ?mk\<close> \<open>?mk \<le> card ?V\<close>
                by (by100 blast)
              hence "k + 1 \<ge> j - i" by linarith
              hence "k = j - i - 1" using hk by linarith
              \<comment> \<open>Now: same arc snd(walk j) = snd(walk(Suc i)). Both have fst(walk(j-1)) resp fst(walk(i))
                 as one endpoint. fst(walk(j)) = fst(walk(i)). Same arc \\<Rightarrow> same ep set.
                 The other endpoint: fst(walk(j-1)) = fst(walk(Suc i)) (from ep set equality).
                 hv\\_distinct: j-1 = Suc i \\<Rightarrow> j = i+2, j-i = 2.
                 Then k = 1, l = 0, l+1 = 1 = k. hkl\\_ne\\_1 gives \\<bottom>.\<close>
              \<comment> \<open>Shortcut: with k = j-i-1 and l = 0, we have l+1 = 1 and k = j-i-1.
                 If j-i = 2: l+1 = k. hkl\\_ne\\_1 gives False.
                 If j-i > 2: k > 1 and l = 0. Not consecutive. But need another argument.
                 Use: fst(walk(j)) = fst(walk(i)) and snd(walk(j)) = snd(walk(Suc i)).
                 Arc snd(walk(Suc i)) has ep = {fst(walk(i)), fst(walk(Suc i))}.
                 Arc snd(walk(j)) has ep = {fst(walk(j-1)), fst(walk(j))} = {fst(walk(j-1)), fst(walk(i))}.
                 Same arc \\<Rightarrow> {fst(walk(i)), fst(walk(Suc i))} = {fst(walk(j-1)), fst(walk(i))}.
                 So fst(walk(Suc i)) = fst(walk(j-1)).
                 hv\\_distinct: both in {Suc i, ..., j-1}. Suc i and j-1. If Suc i \\<noteq> j-1: contradiction.
                 If Suc i = j-1: j = i+2. Then k = 1, l+1 = 1 = k. hkl\\_ne\\_1.\<close>
              have hj_eq: "j - i = 2"
              proof -
                \<comment> \<open>fst(walk(Suc i)) and fst(walk(j-1)) are both in {Suc i,...,j-1}.
                   Same arc \\<Rightarrow> same ep. fst(walk j) = fst(walk i) is in both eps.
                   The other elements must match: fst(walk(Suc i)) = fst(walk(j-1)).\<close>
                have "?mk = j" using \<open>k = j - i - 1\<close> hij(1) by linarith
                hence "snd (walk j) = snd (walk (Suc i))"
                  using \<open>snd (walk ?mk) = snd (walk ?ml)\<close> True by simp
                \<comment> \<open>Both fst(walk(Suc i)) and fst(walk(j-1)) are endpoints of this arc,
                   and both differ from fst(walk(i)). With 2-element ep set: they must be equal.\<close>
                have "fst (walk (Suc i)) \<in> ?ep2 (snd (walk (Suc i)))" using hwalk_props by (by100 blast)
                have "fst (walk i) \<in> ?ep2 (snd (walk (Suc i)))"
                proof -
                  have "snd (walk (Suc i)) = next_arc (fst (walk i)) (snd (walk i))"
                    using hwalk_suc_snd[of i] by simp
                  moreover have "fst (walk i) \<in> ?ep2 (next_arc (fst (walk i)) (snd (walk i)))"
                    using hnext_arc hwalk_props by (by100 blast)
                  ultimately show ?thesis by simp
                qed
                have "fst (walk (j - 1)) \<in> ?ep2 (snd (walk j))"
                proof -
                  have "j = Suc (j - 1)" using hij(1) by linarith
                  hence "snd (walk j) = next_arc (fst (walk (j-1))) (snd (walk (j-1)))"
                    using hwalk_suc_snd[of "j-1"] by simp
                  moreover have "fst (walk (j-1)) \<in> ?ep2 (next_arc (fst (walk (j-1))) (snd (walk (j-1))))"
                    using hnext_arc hwalk_props by (by100 blast)
                  ultimately show ?thesis by simp
                qed
                hence "fst (walk (j-1)) \<in> ?ep2 (snd (walk (Suc i)))"
                  using \<open>snd (walk j) = snd (walk (Suc i))\<close> by simp
                \<comment> \<open>ep(snd(walk(Suc i))) has 2 elements: fst(walk i) and fst(walk(Suc i)).
                   fst(walk(j-1)) is in this set. And fst(walk(j-1)) \\<noteq> fst(walk i) unless j-1 = i (impossible).\<close>
                have "Suc i \<le> j - 1" using hji_ge2 by linarith
                have "j - 1 < j" using hij(1) by linarith
                \<comment> \<open>If fst(walk(j-1)) = fst(walk i): from hmin, j-i \\<le> (j-1)-i = j-i-1. Impossible.\<close>
                have "fst (walk (j-1)) \<noteq> fst (walk i)"
                proof
                  assume "fst (walk (j-1)) = fst (walk i)"
                  have "fst (walk i) = fst (walk (j-1))" using \<open>fst (walk (j-1)) = fst (walk i)\<close> by simp
                  have "i < j-1" using hji_ge2 by linarith
                  have "j-1 \<le> card ?V" using hij(2) by linarith
                  hence "j - i \<le> (j-1) - i" using hmin[rule_format, of i "j-1"]
                      \<open>i < j-1\<close> \<open>j-1 \<le> card ?V\<close> \<open>fst (walk i) = fst (walk (j-1))\<close> by (by100 blast)
                  thus False using hji_ge2 by linarith
                qed
                \<comment> \<open>So fst(walk(j-1)) = fst(walk(Suc i)) (the only other element of the 2-element ep set).\<close>
                \<comment> \<open>From hv\\_distinct: j-1 = Suc i, giving j = i + 2.\<close>
                have "fst (walk (j-1)) = fst (walk (Suc i))"
                proof -
                  have "snd (walk (Suc i)) \<in> \<A>" using hwalk_props by (by100 blast)
                  from h2ep[rule_format, OF this]
                  obtain a b where hab: "a \<noteq> b" "?ep2 (snd (walk (Suc i))) = {a, b}" by (by100 blast)
                  have "fst (walk i) \<in> {a, b}" using \<open>fst (walk i) \<in> ?ep2 (snd (walk (Suc i)))\<close> hab(2) by simp
                  have "fst (walk (Suc i)) \<in> {a, b}" using \<open>fst (walk (Suc i)) \<in> ?ep2 (snd (walk (Suc i)))\<close> hab(2) by simp
                  have "fst (walk (j-1)) \<in> {a, b}" using \<open>fst (walk (j-1)) \<in> ?ep2 (snd (walk (Suc i)))\<close> hab(2) by simp
                  have "fst (walk (Suc i)) \<noteq> fst (walk i)"
                  proof -
                    let ?ei = "next_arc (fst (walk i)) (snd (walk i))"
                    have "fst (walk (Suc i)) = other_endpt (fst (walk i)) ?ei"
                      using hwalk_suc_fst by simp
                    moreover have "?ei \<in> \<A>" using hnext_arc hwalk_props by (by100 blast)
                    moreover have "fst (walk i) \<in> ?ep2 ?ei" using hnext_arc hwalk_props by (by100 blast)
                    moreover have "other_endpt (fst (walk i)) ?ei \<noteq> fst (walk i)"
                      using hother_endpt calculation(2) calculation(3) by (by100 blast)
                    ultimately show ?thesis by simp
                  qed
                  \<comment> \<open>2-element set {a,b}: fst(walk i) and fst(walk(Suc i)) are the two elements.
                     fst(walk(j-1)) is also in {a,b} and \\<noteq> fst(walk i). So = fst(walk(Suc i)).\<close>
                  show ?thesis using \<open>fst (walk (j-1)) \<in> {a,b}\<close> \<open>fst (walk i) \<in> {a,b}\<close>
                      \<open>fst (walk (Suc i)) \<in> {a,b}\<close> \<open>fst (walk (j-1)) \<noteq> fst (walk i)\<close>
                      \<open>fst (walk (Suc i)) \<noteq> fst (walk i)\<close> hab(1) by (by100 force)
                qed
                from hv_distinct[rule_format, of "j-1" "Suc i"]
                have "j - 1 \<noteq> Suc i \<longrightarrow> fst (walk (j-1)) \<noteq> fst (walk (Suc i))"
                  using \<open>Suc i \<le> j - 1\<close> \<open>j - 1 < j\<close> by (by100 force)
                hence "j - 1 = Suc i" using \<open>fst (walk (j-1)) = fst (walk (Suc i))\<close> by (by100 blast)
                thus "j - i = 2" by linarith
              qed
              hence "k = 1" using \<open>k = j - i - 1\<close> by linarith
              hence "l + 1 = k" using True by linarith
              thus False using hkl_ne_1 by (by100 blast)
            next
              case False \<comment> \<open>l \\<ge> 1.\<close>
              hence hl1: "l \<ge> 1" by linarith
              show False
              proof (cases "Suc i + k < j")
                case True \<comment> \<open>?mk < j and i+l \\<ge> Suc i: both in hv\\_distinct range.\<close>
                have "Suc i \<le> i + l" using hl1 by linarith
                have "i + l < j" using hl by linarith
                from hv_distinct[rule_format, of ?mk "i+l"]
                have "?mk \<noteq> i+l \<longrightarrow> fst (walk ?mk) \<noteq> fst (walk (i+l))"
                  using True \<open>Suc i \<le> i+l\<close> \<open>i+l < j\<close> by (by100 force)
                hence "?mk = i + l" using heq by (by100 blast)
                hence "k + 1 = l" by linarith
                thus False using hkl_ne_1 by (by100 blast)
              next
                case False \<comment> \<open>?mk = j: fst(walk(j)) = fst(walk(i+l)).\<close>
                hence "?mk = j" using hk by linarith
                hence "fst (walk j) = fst (walk (i+l))" using heq by simp
                hence "fst (walk i) = fst (walk (i+l))" using hij(3) by simp
                \<comment> \<open>hmin: j-i \\<le> (i+l) - i = l. But l < j-i. Contradiction.\<close>
                have "i < i + l" using hl1 by linarith
                have "i + l \<le> card ?V" using hl hij(2) by linarith
                hence "j - i \<le> (i+l) - i" using hmin[rule_format, of i "i+l"]
                    \<open>i < i+l\<close> \<open>i+l \<le> card ?V\<close> \<open>fst (walk i) = fst (walk (i+l))\<close> by (by100 blast)
                hence "j - i \<le> l" by linarith
                thus False using hl by linarith
              qed
            qed
          qed
        qed
      qed
    qed
    \<comment> \<open>Case split on j - i: for j-i \\<ge> 3 use hacyclic (card = 1); for j-i = 2 use sc\\_graph\\_no\\_cycle.\<close>
    show False
    proof (cases "j - i \<ge> 3")
      case True
      \<comment> \<open>j-i \\<ge> 3: all consecutive pairs have card = 1 (distinct vertices 2 apart). Apply hacyclic.\<close>
      have hws_adj_card: "\<forall>idx < length ?ws. card (?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws)) = 1"
    proof (intro allI impI)
      fix idx assume hidx: "idx < length ?ws"
      have hidx': "idx < j - i" using hidx hws_len by linarith
      \<comment> \<open>Get arc membership and intersection properties.\<close>
      have hwsA: "?ws ! idx \<in> \<A>"
        using nth_mem[OF hidx] hws_sub by (by100 blast)
      have hlen_pos: "length ?ws > 0" using hws_len2 by linarith
      have hmod_lt: "(idx + 1) mod length ?ws < length ?ws" using hlen_pos by simp
      have hwsB: "?ws ! ((idx + 1) mod length ?ws) \<in> \<A>"
        using nth_mem[OF hmod_lt] hws_sub by (by100 blast)
      have hwsAB_ne: "?ws ! idx \<noteq> ?ws ! ((idx + 1) mod length ?ws)"
      proof -
        have "idx \<noteq> (idx + 1) mod length ?ws"
        proof (cases "idx + 1 < length ?ws")
          case True thus ?thesis by simp
        next
          case False
          hence "idx + 1 = length ?ws" using hidx by linarith
          hence "(idx + 1) mod length ?ws = 0" using hws_len2 by simp
          moreover have "idx > 0" using \<open>idx + 1 = length ?ws\<close> hws_len2 by linarith
          ultimately show ?thesis by linarith
        qed
        thus ?thesis using nth_eq_iff_index_eq[OF hws_dist hidx hmod_lt] by (by100 blast)
      qed
      from assms(4)[rule_format, OF hwsA hwsB hwsAB_ne]
      have hinter_props: "finite (?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws))
          \<and> card (?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws)) \<le> 2" by (by100 blast)
      \<comment> \<open>card \\<ge> 1 from hws\\_adj.\<close>
      have hge1: "card (?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws)) \<ge> 1"
      proof -
        from hws_adj[rule_format, OF hidx]
        have hne: "?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws) \<noteq> {}" .
        have hfin: "finite (?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws))"
          using hinter_props by (by100 blast)
        have "card (?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws)) \<noteq> 0"
        proof
          assume "card (?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws)) = 0"
          hence "?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws) = {}" using hfin by simp
          thus False using hne by simp
        qed
        thus ?thesis by linarith
      qed
      \<comment> \<open>card \\<noteq> 2: if card = 2, arcs share both endpoints, contradicting hv\\_distinct.\<close>
      \<comment> \<open>card \\<noteq> 2: use named walk arcs to avoid ?ws expansion.\<close>
      define arc_k where "arc_k = snd (walk (Suc i + idx))"
      define arc_next where "arc_next = snd (walk (Suc i + ((idx + 1) mod (j - i))))"
      have harc_k_eq: "?ws ! idx = arc_k" using hws_nth[OF hidx'] unfolding arc_k_def by simp
      have hnxt: "(idx + 1) mod (j - i) < j - i" using hidx' hji_ge2 by simp
      have harc_next_eq: "?ws ! ((idx + 1) mod length ?ws) = arc_next"
        using hws_nth[OF hnxt] hws_len unfolding arc_next_def by simp
      have hne2: "card (?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws)) \<noteq> 2"
      proof
        assume "card (?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws)) = 2"
        hence hcard2: "card (arc_k \<inter> arc_next) = 2"
          using harc_k_eq harc_next_eq by simp
        \<comment> \<open>card = 2 with intersection \\<subseteq> ep(arc\\_k) (2 elements) \\<Rightarrow> intersection = ep(arc\\_k).
           walk\\_v(i+idx) \\<in> ep(arc\\_k) (predecessor endpoint).
           So walk\\_v(i+idx) \\<in> ep(arc\\_next).
           ep(arc\\_next) = {walk\\_v(Suc i + idx), walk\\_v(Suc i + ((idx+1) mod k))}.
           walk\\_v(i+idx) \\<noteq> walk\\_v(Suc i+idx) (other\\_endpt).
           So walk\\_v(i+idx) = walk\\_v(Suc i + ((idx+1) mod k)).
           For j-i \\<ge> 3: hv\\_distinct/hmin gives contradiction.\<close>
        \<comment> \<open>intersection \\<subseteq> ep(arc\\_k). card = 2, card(ep) = 2 \\<Rightarrow> intersection = ep.\<close>
        have harc_k_in: "arc_k \<in> \<A>" using hwsA harc_k_eq by simp
        have harc_next_in: "arc_next \<in> \<A>" using hwsB harc_next_eq by simp
        have harc_ne: "arc_k \<noteq> arc_next" using hwsAB_ne harc_k_eq harc_next_eq by simp
        have hinter_sub_ep: "arc_k \<inter> arc_next \<subseteq> ?ep2 arc_k"
          using assms(4)[rule_format, OF harc_k_in harc_next_in harc_ne] by (by100 blast)
        have hcard_ep_k: "card (?ep2 arc_k) = 2"
        proof -
          from h2ep[rule_format, OF harc_k_in]
          obtain a0 b0 where "a0 \<noteq> b0" "?ep2 arc_k = {a0, b0}" by (by100 blast)
          thus ?thesis using \<open>a0 \<noteq> b0\<close> by (by100 simp)
        qed
        have hfin_ep_k: "finite (?ep2 arc_k)"
        proof (rule ccontr)
          assume "\<not> finite (?ep2 arc_k)"
          hence "card (?ep2 arc_k) = 0" by (rule card.infinite)
          thus False using hcard_ep_k by simp
        qed
        have "card (arc_k \<inter> arc_next) = card (?ep2 arc_k)"
          using hcard2 hcard_ep_k by simp
        hence hinter_eq: "arc_k \<inter> arc_next = ?ep2 arc_k"
          by (rule card_subset_eq[OF hfin_ep_k hinter_sub_ep])
        \<comment> \<open>walk\\_v(i+idx) \\<in> ep(arc\\_k) (predecessor endpoint).\<close>
        have "fst (walk (i + idx)) \<in> ?ep2 arc_k"
        proof -
          have "snd (walk (Suc i + idx)) = next_arc (fst (walk (i + idx))) (snd (walk (i + idx)))"
            using hwalk_suc_snd[of "i + idx"] by simp
          moreover have "fst (walk (i+idx)) \<in> ?ep2 (next_arc (fst (walk (i+idx))) (snd (walk (i+idx))))"
            using hnext_arc hwalk_props by (by100 blast)
          ultimately show ?thesis unfolding arc_k_def by simp
        qed
        \<comment> \<open>So walk\\_v(i+idx) \\<in> ep(arc\\_next) (via intersection = ep).\<close>
        hence "fst (walk (i + idx)) \<in> ?ep2 arc_next"
          using hinter_eq assms(4)[rule_format, OF harc_k_in harc_next_in harc_ne]
          by (by100 blast)
        \<comment> \<open>ep(arc\\_next) has walk\\_v(Suc i+idx) in it. And walk\\_v(i+idx) \\<noteq> walk\\_v(Suc i+idx).
           ep has 2 elements. So walk\\_v(i+idx) = the OTHER element of ep(arc\\_next).
           The other element is walk\\_v at the "next-next" position.
           For j-i \\<ge> 3: hv\\_distinct/hmin gives contradiction.\<close>
        \<comment> \<open>walk\\_v(Suc i+idx) \\<in> ep(arc\\_next) (it's the shared walk vertex).\<close>
        have "fst (walk (Suc i + idx)) \<in> ?ep2 arc_next"
        proof -
          have "fst (walk (Suc i + idx)) \<in> snd (walk (Suc i + idx))"
            using hwalk_shared by (by100 blast)
          hence "fst (walk (Suc i + idx)) \<in> arc_k" unfolding arc_k_def by simp
          moreover have "fst (walk (Suc i + idx)) \<in> snd (walk (Suc (Suc i + idx)))"
            using hwalk_shared by (by100 blast)
          \<comment> \<open>For non-wrap: Suc (Suc i + idx) = Suc i + (idx+1). For wrap: need walk\\_v(j) = walk\\_v(i).\<close>
          moreover have "fst (walk (Suc i + idx)) \<in> arc_next"
          proof (cases "idx + 1 < j - i")
            case True \<comment> \<open>Non-wrap: Suc(Suc i + idx) = Suc i + (idx+1) = walk position of arc\\_next.\<close>
            hence "(idx + 1) mod (j - i) = idx + 1" by simp
            hence "arc_next = snd (walk (Suc i + (idx + 1)))" unfolding arc_next_def by simp
            hence "arc_next = snd (walk (Suc (Suc i + idx)))" by simp
            thus ?thesis using \<open>fst (walk (Suc i + idx)) \<in> snd (walk (Suc (Suc i + idx)))\<close> by simp
          next
            case False \<comment> \<open>Wrap: idx = j-i-1. arc\\_next = snd(walk(Suc i)). Use walk\\_v(j) = walk\\_v(i).\<close>
            hence "idx = j - i - 1" using hidx' by linarith
            hence "idx + 1 = j - i" using hidx' by linarith
            hence "(idx + 1) mod (j - i) = 0" using hji_ge2 by simp
            hence "arc_next = snd (walk (Suc i))" unfolding arc_next_def by simp
            have "Suc i + idx = j" using \<open>idx = j - i - 1\<close> hij(1) by linarith
            hence "fst (walk (Suc i + idx)) = fst (walk j)" by simp
            hence "fst (walk (Suc i + idx)) = fst (walk i)" using hij(3) by simp
            moreover have "fst (walk i) \<in> snd (walk (Suc i))" using hwalk_shared by (by100 blast)
            ultimately show ?thesis using \<open>arc_next = snd (walk (Suc i))\<close> by simp
          qed
          ultimately have "fst (walk (Suc i + idx)) \<in> arc_k \<inter> arc_next" by (by100 blast)
          thus ?thesis using assms(4)[rule_format, OF harc_k_in harc_next_in harc_ne] by (by100 blast)
        qed
        \<comment> \<open>ep(arc\\_next) has 2 elements. Both walk\\_v(i+idx) and walk\\_v(Suc i+idx) are in it.
           walk\\_v(i+idx) \\<noteq> walk\\_v(Suc i+idx). So these ARE the 2 elements.
           But walk\\_v(i+idx) is ALSO in ep (proved above). ep has only 2 elements.
           walk\\_v(i+idx) = walk\\_v(Suc i+idx) or walk\\_v(i+idx) = walk\\_v(Suc i + nxt).
           First is impossible (other\\_endpt). So walk\\_v(i+idx) = walk\\_v(Suc i + nxt).
           hv\\_distinct/hmin: these are at positions i+idx and Suc i + nxt. For j-i \\<ge> 3: distinct.\<close>
        have hne_step: "fst (walk (i + idx)) \<noteq> fst (walk (Suc i + idx))"
        proof -
          have "fst (walk (Suc i + idx)) = other_endpt (fst (walk (i+idx))) (next_arc (fst (walk (i+idx))) (snd (walk (i+idx))))"
            using hwalk_suc_fst[of "i+idx"] by simp
          moreover have "next_arc (fst (walk (i+idx))) (snd (walk (i+idx))) \<in> \<A>"
            using hnext_arc hwalk_props by (by100 blast)
          moreover have hna_in: "fst (walk (i+idx)) \<in> ?ep2 (next_arc (fst (walk (i+idx))) (snd (walk (i+idx))))"
            using hnext_arc hwalk_props by (by100 blast)
          moreover have hna_arc: "next_arc (fst (walk (i+idx))) (snd (walk (i+idx))) \<in> \<A>"
            using hnext_arc hwalk_props by (by100 blast)
          moreover have "other_endpt (fst (walk (i+idx))) (next_arc (fst (walk (i+idx))) (snd (walk (i+idx)))) \<noteq> fst (walk (i+idx))"
            using hother_endpt[rule_format, OF hna_arc hna_in] by (by100 blast)
          ultimately show ?thesis by simp
        qed
        \<comment> \<open>walk\\_v(i+idx) \\<in> ep(arc\\_next) and walk\\_v(Suc i+idx) \\<in> ep(arc\\_next) and they differ.
           ep has 2 elements. walk\\_v(i+idx) is also in ep. So walk\\_v(i+idx) is one of the 2.
           Since walk\\_v(i+idx) \\<noteq> walk\\_v(Suc i+idx): walk\\_v(i+idx) is the OTHER one.
           hv\\_distinct/hmin gives contradiction.\<close>
        \<comment> \<open>The arrival vertex of arc\\_next is also in ep(arc\\_next).\<close>
        let ?nxt_pos = "Suc i + ((idx + 1) mod (j - i))"
        have hnxt_in_ep: "fst (walk ?nxt_pos) \<in> ?ep2 arc_next"
          using hwalk_props unfolding arc_next_def by (by100 blast)
        \<comment> \<open>ep(arc\\_next) = {fst(walk(Suc i+idx)), fst(walk(?nxt\\_pos))} since card = 2 and both \\<in> ep.\<close>
        \<comment> \<open>fst(walk(i+idx)) \\<in> ep and \\<noteq> fst(walk(Suc i+idx)). So = fst(walk(?nxt\\_pos)).\<close>
        have "fst (walk (i + idx)) = fst (walk ?nxt_pos)"
        proof -
          \<comment> \<open>3 points in a 2-element set. Two are distinct. Third = one of them.\<close>
          have hcard_ep_next: "card (?ep2 arc_next) = 2"
          proof -
            from h2ep[rule_format, OF harc_next_in]
            obtain a0 b0 where "a0 \<noteq> b0" "?ep2 arc_next = {a0, b0}" by (by100 blast)
            thus ?thesis using \<open>a0 \<noteq> b0\<close> by (by100 simp)
          qed
          \<comment> \<open>fst(walk(i+idx)), fst(walk(Suc i+idx)), fst(walk(?nxt\\_pos)) all \\<in> ep(arc\\_next).
             card(ep) = 2. fst(walk(i+idx)) \\<noteq> fst(walk(Suc i+idx)).
             So one of: fst(walk(i+idx)) = fst(walk(?nxt\\_pos))
                     or fst(walk(Suc i+idx)) = fst(walk(?nxt\\_pos)).\<close>
          have h3_in_2: "{fst (walk (i+idx)), fst (walk (Suc i+idx)), fst (walk ?nxt_pos)} \<subseteq> ?ep2 arc_next"
            using \<open>fst (walk (i+idx)) \<in> ?ep2 arc_next\<close>
                  \<open>fst (walk (Suc i+idx)) \<in> ?ep2 arc_next\<close> hnxt_in_ep by (by100 blast)
          have "card {fst (walk (i+idx)), fst (walk (Suc i+idx)), fst (walk ?nxt_pos)} \<le> 2"
          proof -
            have "finite (?ep2 arc_next)"
            proof (rule ccontr)
              assume "\<not> finite (?ep2 arc_next)"
              thus False using hcard_ep_next card.infinite by (by100 force)
            qed
            from card_mono[OF this h3_in_2] show ?thesis using hcard_ep_next by linarith
          qed
          \<comment> \<open>3 elements with card \\<le> 2 \\<Rightarrow> two are equal. Since fst(i+idx) \\<noteq> fst(Suc i+idx):
             fst(i+idx) = fst(?nxt) or fst(Suc i+idx) = fst(?nxt).\<close>
          hence "fst (walk (i+idx)) = fst (walk (Suc i+idx))
              \<or> fst (walk (i+idx)) = fst (walk ?nxt_pos)
              \<or> fst (walk (Suc i+idx)) = fst (walk ?nxt_pos)"
          proof -
            from h2ep[rule_format, OF harc_next_in]
            obtain x y where hxy: "x \<noteq> y" "?ep2 arc_next = {x, y}" by (by100 blast)
            have "fst (walk (i+idx)) \<in> {x, y}"
              using \<open>fst (walk (i+idx)) \<in> ?ep2 arc_next\<close> hxy(2) by simp
            moreover have "fst (walk (Suc i+idx)) \<in> {x, y}"
              using \<open>fst (walk (Suc i+idx)) \<in> ?ep2 arc_next\<close> hxy(2) by simp
            moreover have "fst (walk ?nxt_pos) \<in> {x, y}"
              using hnxt_in_ep hxy(2) by simp
            ultimately show ?thesis by (by100 force)
          qed
          hence "fst (walk (i+idx)) = fst (walk ?nxt_pos)
              \<or> fst (walk (Suc i+idx)) = fst (walk ?nxt_pos)"
            using hne_step by (by100 blast)
          thus ?thesis
          proof
            assume "fst (walk (i+idx)) = fst (walk ?nxt_pos)" thus ?thesis .
          next
            assume "fst (walk (Suc i+idx)) = fst (walk ?nxt_pos)"
            \<comment> \<open>This would mean the walk arc has both endpoints equal. But other\\_endpt says \\<noteq>.\<close>
            \<comment> \<open>Actually: fst(walk(Suc i+idx)) = fst(walk(?nxt\\_pos)) means the arrival vertex
               of arc\\_next equals the predecessor vertex. But these are different by other\\_endpt
               of arc\\_next's walk step.\<close>
            \<comment> \<open>Derive False: fst(walk(Suc i+idx)) is the predecessor vertex of arc\\_next,
               and fst(walk(?nxt\\_pos)) is the arrival vertex = other\\_endpt \\<noteq> predecessor.\<close>
            show ?thesis
            proof (cases "idx + 1 < j - i")
              case True \<comment> \<open>Non-wrap: ?nxt\\_pos = Suc(Suc i + idx).\<close>
              hence "?nxt_pos = Suc (Suc i + idx)" by simp
              \<comment> \<open>fst(walk(Suc(Suc i+idx))) = other\\_endpt(fst(walk(Suc i+idx)), ...) \\<noteq> fst(walk(Suc i+idx)).\<close>
              have "fst (walk (Suc (Suc i + idx))) = other_endpt (fst (walk (Suc i + idx)))
                  (next_arc (fst (walk (Suc i + idx))) (snd (walk (Suc i + idx))))"
                using hwalk_suc_fst[of "Suc i + idx"] by simp
              moreover have hna_arc2: "next_arc (fst (walk (Suc i+idx))) (snd (walk (Suc i+idx))) \<in> \<A>"
                using hnext_arc hwalk_props by (by100 blast)
              moreover have hna_in2: "fst (walk (Suc i+idx)) \<in> ?ep2 (next_arc (fst (walk (Suc i+idx))) (snd (walk (Suc i+idx))))"
                using hnext_arc hwalk_props by (by100 blast)
              moreover have "other_endpt (fst (walk (Suc i+idx))) (next_arc (fst (walk (Suc i+idx))) (snd (walk (Suc i+idx)))) \<noteq> fst (walk (Suc i+idx))"
                using hother_endpt[rule_format, OF hna_arc2 hna_in2] by (by100 blast)
              ultimately have "fst (walk (Suc (Suc i+idx))) \<noteq> fst (walk (Suc i+idx))" by simp
              hence False using \<open>fst (walk (Suc i+idx)) = fst (walk ?nxt_pos)\<close> \<open>?nxt_pos = Suc (Suc i + idx)\<close> by simp
              thus ?thesis by simp
            next
              case False \<comment> \<open>Wrap: idx = j-i-1, ?nxt\\_pos = Suc i.\<close>
              hence "idx = j - i - 1" using hidx' by linarith
              have "idx + 1 = j - i" using \<open>idx = j - i - 1\<close> hji_ge2 hij(1) by linarith
              hence "(idx + 1) mod (j - i) = 0" by simp
              hence h_nxt_si: "?nxt_pos = Suc i" by simp
              have "Suc i + idx = j" using \<open>idx = j - i - 1\<close> hij(1) by linarith
              hence "fst (walk (Suc i + idx)) = fst (walk i)" using hij(3) by simp
              hence "fst (walk i) = fst (walk (Suc i))"
                using \<open>fst (walk (Suc i+idx)) = fst (walk ?nxt_pos)\<close> h_nxt_si by simp
              \<comment> \<open>But fst(walk(Suc i)) = other\\_endpt(fst(walk i), ...) \\<noteq> fst(walk i).\<close>
              have "fst (walk (Suc i)) = other_endpt (fst (walk i)) (next_arc (fst (walk i)) (snd (walk i)))"
                using hwalk_suc_fst[of i] by simp
              moreover have hna_arc3: "next_arc (fst (walk i)) (snd (walk i)) \<in> \<A>"
                using hnext_arc hwalk_props by (by100 blast)
              moreover have hna_in3: "fst (walk i) \<in> ?ep2 (next_arc (fst (walk i)) (snd (walk i)))"
                using hnext_arc hwalk_props by (by100 blast)
              moreover have "other_endpt (fst (walk i)) (next_arc (fst (walk i)) (snd (walk i))) \<noteq> fst (walk i)"
                using hother_endpt[rule_format, OF hna_arc3 hna_in3] by (by100 blast)
              ultimately have "fst (walk (Suc i)) \<noteq> fst (walk i)" by simp
              hence False using \<open>fst (walk i) = fst (walk (Suc i))\<close> by simp
              thus ?thesis by simp
            qed
          qed
        qed
        \<comment> \<open>fst(walk(i+idx)) = fst(walk(?nxt\\_pos)). For j-i \\<ge> 3: these are at different positions. Contradiction.\<close>
        show False
        proof (cases "idx + 1 < j - i")
          case True \<comment> \<open>Non-wrap: ?nxt\\_pos = Suc i + (idx+1) = i + idx + 2.\<close>
          hence "?nxt_pos = i + idx + 2" by simp
          have heq_pos: "fst (walk (i + idx)) = fst (walk (i + idx + 2))"
            using \<open>fst (walk (i + idx)) = fst (walk ?nxt_pos)\<close> \<open>?nxt_pos = i + idx + 2\<close> by simp
          \<comment> \<open>Positions i+idx and i+idx+2. hv\\_distinct or hmin: distinct for j-i \\<ge> 3.\<close>
          show False
          proof (cases "idx = 0")
            case True \<comment> \<open>i+idx = i, i+idx+2 = i+2. hmin: j-i \\<le> 2. But j-i \\<ge> 3. Contradiction.\<close>
            have "fst (walk i) = fst (walk (i+2))" using heq_pos True by simp
            have "i < i + 2" by linarith
            have "i + 2 \<le> card ?V" using \<open>idx + 1 < j - i\<close> True hij(2) by linarith
            have "fst (walk i) = fst (walk (i+2))" by (rule \<open>fst (walk i) = fst (walk (i+2))\<close>)
            have "i < i + 2 \<and> i + 2 \<le> card ?V \<and> fst (walk i) = fst (walk (i+2))"
              using \<open>i < i+2\<close> \<open>i+2 \<le> card ?V\<close> \<open>fst (walk i) = fst (walk (i+2))\<close> by (by100 blast)
            hence "j - i \<le> (i+2) - i" using hmin[rule_format] by (by100 blast)
            hence "j - i \<le> 2" by linarith
            thus False using \<open>j - i \<ge> 3\<close> by linarith
          next
            case False \<comment> \<open>idx \\<ge> 1. Both i+idx and i+idx+2 in {Suc i, ..., j-1}. hv\\_distinct.\<close>
            have "Suc i \<le> i + idx" using False by linarith
            have "i + idx < j" using hidx' by linarith
            have "Suc i \<le> i + idx + 2" by linarith
            have "i + idx + 2 \<le> j" using \<open>idx + 1 < j - i\<close> by linarith
            have "i + idx + 2 < j"
            proof (rule ccontr)
              assume "\<not> i + idx + 2 < j"
              hence "i + idx + 2 = j" using \<open>i + idx + 2 \<le> j\<close> by linarith
              hence "fst (walk (i+idx+2)) = fst (walk j)" by simp
              hence "fst (walk (i+idx)) = fst (walk i)" using heq_pos hij(3) by simp
              have "fst (walk i) = fst (walk (i+idx))" using \<open>fst (walk (i+idx)) = fst (walk i)\<close> by simp
              have "i < i + idx" using False by linarith
              have "i + idx \<le> card ?V" using hidx' hij(2) by linarith
              have "i < i+idx \<and> i+idx \<le> card ?V \<and> fst (walk i) = fst (walk (i+idx))"
                using \<open>i < i+idx\<close> \<open>i+idx \<le> card ?V\<close> \<open>fst (walk i) = fst (walk (i+idx))\<close> by (by100 blast)
              hence "j - i \<le> (i+idx) - i" using hmin[rule_format] by (by100 blast)
              hence "j - i \<le> idx" by linarith
              thus False using hidx' by linarith
            qed
            have "i + idx \<noteq> i + idx + 2" by linarith
            from hv_distinct[rule_format, of "i+idx" "i+idx+2"]
                \<open>Suc i \<le> i+idx\<close> \<open>i+idx < j\<close> \<open>Suc i \<le> i+idx+2\<close> \<open>i+idx+2 < j\<close> \<open>i+idx \<noteq> i+idx+2\<close>
            have "fst (walk (i+idx)) \<noteq> fst (walk (i+idx+2))" by (by100 blast)
            thus False using \<open>fst (walk (i+idx)) = fst (walk (i+idx+2))\<close> by simp
          qed
        next
          case False \<comment> \<open>Wrap: idx = j-i-1. ?nxt\\_pos = Suc i. fst(walk(j-1)) = fst(walk(Suc i)).\<close>
          hence "idx = j - i - 1" using hidx' by linarith
          hence "idx + 1 = j - i" using hji_ge2 hij(1) by linarith
          hence "?nxt_pos = Suc i" using hji_ge2 by simp
          have "i + idx = j - 1" using \<open>idx = j - i - 1\<close> hij(1) by linarith
          have "fst (walk (j - 1)) = fst (walk (Suc i))"
            using \<open>fst (walk (i+idx)) = fst (walk ?nxt_pos)\<close> \<open>i+idx = j-1\<close> \<open>?nxt_pos = Suc i\<close> by simp
          \<comment> \<open>j-1 and Suc i are both in {Suc i, ..., j-1}. j-1 \\<noteq> Suc i since j-i \\<ge> 3.\<close>
          have "Suc i \<le> j - 1" using hji_ge2 by linarith
          have "j - 1 < j" using hij(1) by linarith
          have "j - 1 \<noteq> Suc i" using \<open>j - i \<ge> 3\<close> by linarith
          from hv_distinct[rule_format, of "j-1" "Suc i"]
              \<open>Suc i \<le> j-1\<close> \<open>j-1 < j\<close>
          have "j - 1 \<noteq> Suc i \<longrightarrow> fst (walk (j-1)) \<noteq> fst (walk (Suc i))"
            by (by100 force)
          thus False using \<open>j-1 \<noteq> Suc i\<close> \<open>fst (walk (j-1)) = fst (walk (Suc i))\<close> by simp
        qed
      qed
      show "card (?ws ! idx \<inter> ?ws ! ((idx + 1) mod length ?ws)) = 1"
        using hge1 hinter_props hne2 by linarith
    qed
      \<comment> \<open>The shared vertex of consecutive arcs ii and (ii+1) mod len is fst(walk(Suc i + ii)).
         This is in both arcs (hwalk\\_shared). Since card = 1 (hws\\_adj\\_card), it equals the unique element.\<close>
      have hshared_eq: "\<And>ii. ii < j - i \<Longrightarrow>
        fst (walk (Suc i + ii)) \<in> ?ws ! ii \<inter> ?ws ! ((ii + 1) mod length ?ws)"
      proof -
        fix ii assume hii: "ii < j - i"
        have "fst (walk (Suc i + ii)) \<in> snd (walk (Suc i + ii))" using hwalk_shared by (by100 blast)
        hence hin_ii: "fst (walk (Suc i + ii)) \<in> ?ws ! ii" using hws_nth[OF hii] by simp
        have hin_next: "fst (walk (Suc i + ii)) \<in> ?ws ! ((ii + 1) mod length ?ws)"
        proof (cases "ii + 1 < j - i")
          case True
          hence "(ii + 1) mod (j - i) = ii + 1" by simp
          hence "?ws ! ((ii + 1) mod length ?ws) = snd (walk (Suc (Suc i + ii)))"
            using hws_nth[OF True] hws_len by simp
          moreover have "fst (walk (Suc i + ii)) \<in> snd (walk (Suc (Suc i + ii)))"
            using hwalk_shared by (by100 blast)
          ultimately show ?thesis by simp
        next
          case False
          hence "ii = j - i - 1" using hii by linarith
          have "ii + 1 = j - i" using \<open>ii = j - i - 1\<close> hji_ge2 hij(1) by linarith
          hence "(ii + 1) mod (j - i) = 0" by simp
          hence "?ws ! ((ii + 1) mod length ?ws) = ?ws ! 0" using hws_len by simp
          moreover have "?ws ! 0 = snd (walk (Suc i))"
          proof -
            have "0 < j - i" using hji_ge2 by linarith
            thus ?thesis using hws_nth by simp
          qed
          moreover have "fst (walk (Suc i + ii)) = fst (walk i)"
          proof -
            have "Suc i + ii = j" using \<open>ii = j - i - 1\<close> hij(1) by linarith
            thus ?thesis using hij(3) by simp
          qed
          moreover have "fst (walk i) \<in> snd (walk (Suc i))" using hwalk_shared by (by100 blast)
          ultimately show ?thesis by simp
        qed
        show "fst (walk (Suc i + ii)) \<in> ?ws ! ii \<inter> ?ws ! ((ii + 1) mod length ?ws)"
          using hin_ii hin_next by (by100 blast)
      qed
      have hws_vdist: "\<forall>ii < length ?ws. \<forall>jj < length ?ws. ii \<noteq> jj \<longrightarrow>
          (\<forall>v w. ?ws ! ii \<inter> ?ws ! ((ii + 1) mod length ?ws) = {v} \<longrightarrow>
                 ?ws ! jj \<inter> ?ws ! ((jj + 1) mod length ?ws) = {w} \<longrightarrow> v \<noteq> w)"
      proof (intro allI impI)
        fix ii jj v w
        assume hii: "ii < length ?ws" and hjj: "jj < length ?ws" and hne: "ii \<noteq> jj"
        assume hv: "?ws ! ii \<inter> ?ws ! ((ii + 1) mod length ?ws) = {v}"
        assume hw: "?ws ! jj \<inter> ?ws ! ((jj + 1) mod length ?ws) = {w}"
        have hii': "ii < j - i" using hii hws_len by linarith
        have hjj': "jj < j - i" using hjj hws_len by linarith
        \<comment> \<open>v = fst(walk(Suc i + ii)) and w = fst(walk(Suc i + jj)).\<close>
        have "fst (walk (Suc i + ii)) \<in> {v}" using hshared_eq[OF hii'] hv by (by100 blast)
        hence hveq: "v = fst (walk (Suc i + ii))" by simp
        have "fst (walk (Suc i + jj)) \<in> {w}" using hshared_eq[OF hjj'] hw by (by100 blast)
        hence hweq: "w = fst (walk (Suc i + jj))" by simp
        \<comment> \<open>Show fst(walk(Suc i+ii)) \\<noteq> fst(walk(Suc i+jj)).\<close>
        show "v \<noteq> w" unfolding hveq hweq
        proof
          assume heq: "fst (walk (Suc i + ii)) = fst (walk (Suc i + jj))"
          let ?pi = "Suc i + ii" and ?pj = "Suc i + jj"
          have "?pi \<le> j" using hii' by linarith
          have "?pj \<le> j" using hjj' by linarith
          \<comment> \<open>Case analysis on boundary positions.\<close>
          show False
          proof (cases "?pi < j \<and> ?pj < j")
            case True \<comment> \<open>Both interior: hv\\_distinct gives them equal, hence ii = jj.\<close>
            from hv_distinct[rule_format, of ?pi ?pj]
              True hne
            show False using heq by (by100 force)
          next
            case False
            hence "?pi = j \<or> ?pj = j" using \<open>?pi \<le> j\<close> \<open>?pj \<le> j\<close> by linarith
            thus False
            proof
              assume hpi_j: "?pi = j"
              hence "fst (walk ?pi) = fst (walk i)" using hij(3) by simp
              hence "fst (walk i) = fst (walk ?pj)" using heq by simp
              show False
              proof (cases "?pj < j")
                case True \<comment> \<open>?pj in interior. fst(walk(i)) = fst(walk(?pj)). hmin contradiction.\<close>
                have "i < ?pj" by linarith
                have "?pj \<le> card ?V" using True hij(2) by linarith
                hence "j - i \<le> ?pj - i" using hmin[rule_format, of i ?pj]
                    \<open>i < ?pj\<close> \<open>?pj \<le> card ?V\<close> \<open>fst (walk i) = fst (walk ?pj)\<close> by (by100 blast)
                hence "j - i \<le> jj + 1" by linarith
                hence "jj \<ge> j - i - 1" by linarith
                hence "jj = j - i - 1" using hjj' by linarith
                hence "ii = j - i - 1" using hpi_j by linarith
                thus False using hne \<open>jj = j - i - 1\<close> by linarith
              next
                case False
                hence "?pj = j" using \<open>?pj \<le> j\<close> by linarith
                hence "ii = jj" using hpi_j by linarith
                thus False using hne by simp
              qed
            next
              assume hpj_j: "?pj = j"
              hence "fst (walk ?pj) = fst (walk i)" using hij(3) by simp
              hence "fst (walk i) = fst (walk ?pi)" using heq by simp
              show False
              proof (cases "?pi < j")
                case True
                have "i < ?pi" by linarith
                have "?pi \<le> card ?V" using True hij(2) by linarith
                hence "j - i \<le> ?pi - i" using hmin[rule_format, of i ?pi]
                    \<open>i < ?pi\<close> \<open>?pi \<le> card ?V\<close> \<open>fst (walk i) = fst (walk ?pi)\<close> by (by100 blast)
                hence "j - i \<le> ii + 1" by linarith
                hence "ii \<ge> j - i - 1" by linarith
                hence "ii = j - i - 1" using hii' by linarith
                hence "jj = j - i - 1" using hpj_j by linarith
                thus False using hne \<open>ii = j - i - 1\<close> by linarith
              next
                case False
                hence "?pi = j" using \<open>?pi \<le> j\<close> by linarith
                hence "ii = jj" using hpj_j by linarith
                thus False using hne by simp
              qed
            qed
          qed
        qed
      qed
      show False using hacyclic hws_len2 hws_dist hws_sub hws_adj_card hws_vdist by (by100 blast)
    next
      case False
      hence "j - i = 2" using hji_ge2 by linarith
      \<comment> \<open>j - i = 2: two arcs sharing 2 endpoints. Apply sc\\_graph\\_no\\_cycle for k=2 case.\<close>
      \<comment> \<open>The two arcs ws!0 and ws!1 share both endpoints walk\\_v(i) and walk\\_v(i+1).
         This means: they are 2 distinct arcs from walk\\_v(i) to walk\\_v(i+1).
         Their union \\<cong> S1 \\<Rightarrow> retract of T \\<Rightarrow> scc\\_in\\_sc\\_false \\<Rightarrow> \\<bottom>.\<close>
      \<comment> \<open>Two arcs sharing 2 endpoints in SC graph. Their union \\<cong> S1.
         Need SCC construction for 2 arcs + retraction + scc\\_in\\_sc\\_false.
         This is independent of sc\\_graph\\_no\\_cycle (which handles card = 1 cycles).
         It's the "topological bridge for k = 2" case.\<close>
      \<comment> \<open>Reduce to sc\\_graph\\_no\\_cycle via arc subdivision:
         Split one arc at an interior point, creating a 3-arc cycle with card-1 intersections.\<close>
      let ?arcA = "snd (walk (Suc i))" and ?arcB = "snd (walk (Suc i + 1))"
      have harcA_in: "?arcA \<in> \<A>" using hwalk_props by (by100 blast)
      have harcB_in: "?arcB \<in> \<A>" using hwalk_props by (by100 blast)
      have hAB_ne: "?arcA \<noteq> ?arcB"
      proof -
        have "snd (walk (Suc (Suc i))) \<noteq> snd (walk (Suc i))"
        proof -
          have "snd (walk (Suc (Suc i))) = next_arc (fst (walk (Suc i))) (snd (walk (Suc i)))"
            using hwalk_suc_snd[of "Suc i"] by simp
          moreover have "next_arc (fst (walk (Suc i))) (snd (walk (Suc i))) \<noteq> snd (walk (Suc i))"
            using hnext_arc hwalk_props by (by100 blast)
          ultimately show ?thesis by simp
        qed
        thus ?thesis by simp
      qed
      \<comment> \<open>Both arcs share vertices fst(walk i) and fst(walk(Suc i)).\<close>
      have hvi_inA: "fst (walk i) \<in> ?arcA" using hwalk_shared by (by100 blast)
      have hj_eq: "j = i + 2" using \<open>j - i = 2\<close> hij(1) by linarith
      have hvi_inB: "fst (walk i) \<in> ?arcB"
      proof -
        have "fst (walk j) \<in> snd (walk j)" using hwalk_shared by (by100 blast)
        moreover have "fst (walk j) = fst (walk i)" using hij(3) by simp
        moreover have "snd (walk j) = snd (walk (Suc i + 1))" using hj_eq by simp
        ultimately show ?thesis by simp
      qed
      have hvsi_inA: "fst (walk (Suc i)) \<in> ?arcA" using hwalk_shared by (by100 blast)
      have hvsi_inB: "fst (walk (Suc i)) \<in> ?arcB"
      proof -
        have "fst (walk (Suc i)) \<in> snd (walk (Suc (Suc i)))" using hwalk_shared by (by100 blast)
        have "snd (walk (Suc (Suc i))) = snd (walk (Suc i + 1))" by simp
        thus ?thesis using \<open>fst (walk (Suc i)) \<in> snd (walk (Suc (Suc i)))\<close> by simp
      qed
      \<comment> \<open>Direct approach: arcA \\<union> arcB is an SCC, graph\\_cycle\\_retract gives retraction,
         scc\\_in\\_sc\\_false gives False. No subdivision needed.\<close>
      let ?vi = "fst (walk i)" and ?vsi = "fst (walk (Suc i))"
      have hvi_ne: "?vi \<noteq> ?vsi"
      proof
        assume "?vi = ?vsi"
        have "Suc i \<le> card ?V" using hij(2) hj_eq by linarith
        from hmin[rule_format, of i "Suc i"]
        have "j - i \<le> Suc i - i" using hij(1) \<open>Suc i \<le> card ?V\<close> \<open>?vi = ?vsi\<close> by (by100 blast)
        hence "j - i \<le> 1" by linarith
        thus False using \<open>j - i = 2\<close> by linarith
      qed
      \<comment> \<open>Derive intersection and endpoint equalities.\<close>
      have harcA_sub: "?arcA \<subseteq> T" using assms(2) harcA_in by (by100 blast)
      have harcB_sub: "?arcB \<subseteq> T" using assms(2) harcB_in by (by100 blast)
      have harcA_arc: "top1_is_arc_on ?arcA (subspace_topology T TT ?arcA)"
        using assms(2) harcA_in by (by100 blast)
      have harcB_arc: "top1_is_arc_on ?arcB (subspace_topology T TT ?arcB)"
        using assms(2) harcB_in by (by100 blast)
      have hAB_props: "?arcA \<inter> ?arcB \<subseteq> top1_arc_endpoints_on ?arcA (subspace_topology T TT ?arcA)
          \<and> ?arcA \<inter> ?arcB \<subseteq> top1_arc_endpoints_on ?arcB (subspace_topology T TT ?arcB)
          \<and> finite (?arcA \<inter> ?arcB) \<and> card (?arcA \<inter> ?arcB) \<le> 2"
        using assms(4)[rule_format, OF harcA_in harcB_in hAB_ne] by (by100 blast)
      have hvi_inter: "?vi \<in> ?arcA \<inter> ?arcB" using hvi_inA hvi_inB by (by100 blast)
      have hvsi_inter: "?vsi \<in> ?arcA \<inter> ?arcB" using hvsi_inA hvsi_inB by (by100 blast)
      have hAB_eq: "?arcA \<inter> ?arcB = {?vi, ?vsi}"
      proof -
        have hsub: "{?vi, ?vsi} \<subseteq> ?arcA \<inter> ?arcB" using hvi_inter hvsi_inter by (by100 blast)
        have hfin: "finite (?arcA \<inter> ?arcB)" using hAB_props by (by100 blast)
        have "card {?vi, ?vsi} = 2" using hvi_ne by (by100 simp)
        have "card (?arcA \<inter> ?arcB) \<ge> 2"
          using card_mono[OF hfin hsub] \<open>card {?vi, ?vsi} = 2\<close> by linarith
        have hAB_card2: "card (?arcA \<inter> ?arcB) = 2" using hAB_props \<open>card (?arcA \<inter> ?arcB) \<ge> 2\<close> by linarith
        from card_subset_eq[OF hfin hsub] hAB_card2 \<open>card {?vi, ?vsi} = 2\<close>
        show ?thesis by (by100 auto)
      qed
      have hep_arcA: "top1_arc_endpoints_on ?arcA (subspace_topology T TT ?arcA) = {?vi, ?vsi}"
      proof -
        have "{?vi, ?vsi} \<subseteq> top1_arc_endpoints_on ?arcA (subspace_topology T TT ?arcA)"
          using hAB_props hAB_eq by (by100 blast)
        moreover from h2ep[rule_format, OF harcA_in]
        obtain a0 b0 where "a0 \<noteq> b0"
            "top1_arc_endpoints_on ?arcA (subspace_topology T TT ?arcA) = {a0, b0}"
          by (by100 blast)
        hence hcard_epA: "card (top1_arc_endpoints_on ?arcA (subspace_topology T TT ?arcA)) = 2"
          using \<open>a0 \<noteq> b0\<close> by (by100 simp)
        have hfin_epA: "finite (top1_arc_endpoints_on ?arcA (subspace_topology T TT ?arcA))"
          using hep_fin harcA_in by (by100 blast)
        have hcard_vi: "card {?vi, ?vsi} = 2" using hvi_ne by (by100 simp)
        moreover have "card {?vi, ?vsi} = card (top1_arc_endpoints_on ?arcA (subspace_topology T TT ?arcA))"
          using hcard_epA hcard_vi by linarith
        ultimately show ?thesis using card_subset_eq[OF hfin_epA] by (by100 blast)
      qed
      have hep_arcB: "top1_arc_endpoints_on ?arcB (subspace_topology T TT ?arcB) = {?vi, ?vsi}"
      proof -
        have "{?vi, ?vsi} \<subseteq> top1_arc_endpoints_on ?arcB (subspace_topology T TT ?arcB)"
          using hAB_props hAB_eq by (by100 blast)
        moreover from h2ep[rule_format, OF harcB_in]
        obtain a0 b0 where "a0 \<noteq> b0"
            "top1_arc_endpoints_on ?arcB (subspace_topology T TT ?arcB) = {a0, b0}"
          by (by100 blast)
        hence hcard_epB: "card (top1_arc_endpoints_on ?arcB (subspace_topology T TT ?arcB)) = 2"
          using \<open>a0 \<noteq> b0\<close> by (by100 simp)
        have hfin_epB: "finite (top1_arc_endpoints_on ?arcB (subspace_topology T TT ?arcB))"
          using hep_fin harcB_in by (by100 blast)
        have hcard_vi: "card {?vi, ?vsi} = 2" using hvi_ne by (by100 simp)
        moreover have "card {?vi, ?vsi} = card (top1_arc_endpoints_on ?arcB (subspace_topology T TT ?arcB))"
          using hcard_epB hcard_vi by linarith
        ultimately show ?thesis using card_subset_eq[OF hfin_epB] by (by100 blast)
      qed
      have hSCC: "top1_simple_closed_curve_on T TT (?arcA \<union> ?arcB)"
        by (rule arcs_form_simple_closed_curve[OF hstrict hhaus harcA_arc harcA_sub
               harcB_arc harcB_sub hAB_eq hvi_ne hep_arcA hep_arcB])
      have hretract: "top1_retract_of_on T TT (?arcA \<union> ?arcB)"
      proof -
        let ?S2 = "{?arcA, ?arcB}"
        have "?S2 \<subseteq> \<A>" using harcA_in harcB_in by (by100 blast)
        have "?S2 \<noteq> {}" by (by100 simp)
        have hS2_pc: "top1_path_connected_on (\<Union>?S2) (subspace_topology T TT (\<Union>?S2))"
        proof -
          \<comment> \<open>Use path\\_connected\\_finite\\_union\\_common\\_point with common point vi.\<close>
          have htop_T: "is_topology_on T TT"
            using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def
              is_topology_on_strict_def by (by100 blast)
          have htop_CuA: "is_topology_on (\<Union>?S2) (subspace_topology T TT (\<Union>?S2))"
            by (rule subspace_topology_is_topology_on[OF htop_T])
               (use harcA_sub harcB_sub in \<open>by100 blast\<close>)
          have hfin: "finite ?S2" by (by100 simp)
          have "\<forall>A \<in> ?S2. A \<subseteq> \<Union>?S2" by (by100 blast)
          have hpc_each: "\<forall>A \<in> ?S2. top1_path_connected_on A (subspace_topology (\<Union>?S2) (subspace_topology T TT (\<Union>?S2)) A)"
          proof (intro ballI)
            fix A assume "A \<in> ?S2"
            hence "A \<subseteq> \<Union>?S2" by (by100 blast)
            have "subspace_topology (\<Union>?S2) (subspace_topology T TT (\<Union>?S2)) A = subspace_topology T TT A"
              using subspace_topology_trans[OF \<open>A \<subseteq> \<Union>?S2\<close>] by simp
            moreover have "top1_path_connected_on A (subspace_topology T TT A)"
            proof (rule connected_locally_path_connected_imp_path_connected)
              have "A \<in> \<A>" using \<open>A \<in> ?S2\<close> harcA_in harcB_in by (by100 blast)
              have "A \<subseteq> T" using assms(2) \<open>A \<in> \<A>\<close> by (by100 blast)
              have hA_arc: "top1_is_arc_on A (subspace_topology T TT A)"
                using assms(2) \<open>A \<in> \<A>\<close> by (by100 blast)
              show "is_topology_on A (subspace_topology T TT A)"
                by (rule subspace_topology_is_topology_on[OF htop_T \<open>A \<subseteq> T\<close>])
              show "top1_connected_on A (subspace_topology T TT A)"
                using arc_connected[OF hA_arc] .
              show "top1_locally_path_connected_on A (subspace_topology T TT A)"
                using arc_locally_path_connected[OF hA_arc htop_T \<open>A \<subseteq> T\<close>] .
              obtain g where "top1_homeomorphism_on I_set I_top A (subspace_topology T TT A) g"
                using hA_arc unfolding top1_is_arc_on_def by (by100 blast)
              hence "bij_betw g I_set A" unfolding top1_homeomorphism_on_def by (by100 blast)
              thus "A \<noteq> {}" unfolding bij_betw_def top1_unit_interval_def by (by100 auto)
            qed
            ultimately show "top1_path_connected_on A (subspace_topology (\<Union>?S2) (subspace_topology T TT (\<Union>?S2)) A)" by simp
          qed
          have "\<forall>A \<in> ?S2. ?vi \<in> A" using hvi_inA hvi_inB by (by100 blast)
          have "\<Union>?S2 = \<Union>?S2" by simp
          from path_connected_finite_union_common_point[OF htop_CuA hfin
              \<open>\<forall>A \<in> ?S2. A \<subseteq> \<Union>?S2\<close> hpc_each \<open>\<forall>A \<in> ?S2. ?vi \<in> A\<close>]
          show ?thesis by simp
        qed
        from graph_cycle_retract[OF assms(1) assms(2) assms(3) assms(4) assms(5) assms(7)
            \<open>?S2 \<subseteq> \<A>\<close> \<open>?S2 \<noteq> {}\<close> hS2_pc]
        show ?thesis by (by100 simp)
      qed
      have hSC: "top1_simply_connected_on T TT"
        using assms(1) unfolding top1_is_tree_on_def by (by100 blast)
      have htop_T: "is_topology_on T TT"
        using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def
          is_topology_on_strict_def by (by100 blast)
      have hhaus_T: "is_hausdorff_on T TT"
        using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
      from scc_in_sc_false[OF hSC htop_T hhaus_T hSCC hretract]
      show False using harcA_sub harcB_sub by (by100 blast)
    qed
  qed
qed

\<comment> \<open>Combined Euler + leaf lemma for finite trees, proved by induction on card \\<A>.
   Breaks the circular dependency between tree\\_euler and finite\\_tree\\_has\\_leaf\\_arc.
   Uses degree\\_sum\\_leaf for the leaf existence in the induction step.\<close>

\<comment> \<open>Helper: two arcs A, B with the same endpoints {a,b} and A inter B = {a,b} in an SC space give False.
   Proof: A union B is homeomorphic to S1 (simple closed curve). Identity retraction.
   Apply scc\\_in\\_sc\\_false.\<close>
lemma two_arcs_same_endpoints_sc_false:
  fixes T' :: "'a set" and TT' :: "'a set set"
  assumes hsc: "top1_simply_connected_on T' TT'"
      and htop: "is_topology_on T' TT'"
      and hhaus: "is_hausdorff_on T' TT'"
      and hstrict: "is_topology_on_strict T' TT'"
      and hA_arc: "top1_is_arc_on A (subspace_topology T' TT' A)"
      and hB_arc: "top1_is_arc_on B (subspace_topology T' TT' B)"
      and hA_sub: "A \<subseteq> T'" and hB_sub: "B \<subseteq> T'"
      and hAB_inter: "A \<inter> B = {a, b}" and hab: "a \<noteq> b"
      and hep_A: "top1_arc_endpoints_on A (subspace_topology T' TT' A) = {a, b}"
      and hep_B: "top1_arc_endpoints_on B (subspace_topology T' TT' B) = {a, b}"
      and hcover: "A \<union> B = T'"
  shows False
proof -
  \<comment> \<open>Step 1: Construct homeomorphism S1 \\<to> T' = A \\<union> B.
     Use top half of S1 \\<to> A (via hA) and bottom half \\<to> B (via hB).
     Compose with parametrizations of the semicircles.\<close>
  have hC_eq: "T' = A \<union> B" using hcover by simp
  \<comment> \<open>T' = A \\<union> B is a simple closed curve.\<close>
  have hSCC: "top1_simple_closed_curve_on T' TT' T'"
  proof -
    \<comment> \<open>Get oriented homeomorphisms hA: [0,1] \\<to> A with hA(0) = a, hA(1) = b.
       hB: [0,1] \\<to> B with hB(0) = b, hB(1) = a.\<close>
    obtain hAf where hhAf: "top1_homeomorphism_on I_set I_top A (subspace_topology T' TT' A) hAf"
        and hhAf0: "hAf 0 = a" and hhAf1: "hAf 1 = b"
    proof -
      obtain h0 where hh0: "top1_homeomorphism_on I_set I_top A (subspace_topology T' TT' A) h0"
        using hA_arc unfolding top1_is_arc_on_def by (by100 blast)
      have heps0: "top1_arc_endpoints_on A (subspace_topology T' TT' A) = {h0 0, h0 1}"
        by (rule arc_endpoints_are_boundary[OF hstrict hhaus hA_sub hA_arc hh0])
      have "h0 0 \<noteq> h0 1"
      proof
        assume "h0 0 = h0 1"
        hence "{h0 0, h0 1} = {h0 0}" by simp
        hence "card {a, b} \<le> 1" using heps0 hep_A by simp
        thus False using hab by simp
      qed
      have hab_h0: "{h0 0, h0 1} = {a, b}" using heps0 hep_A by simp
      from doubleton_eq_iff[OF hab_h0 \<open>h0 0 \<noteq> h0 1\<close>]
      show ?thesis
      proof
        assume "h0 0 = a \<and> h0 1 = b" thus ?thesis using that[OF hh0] by (by100 blast)
      next
        assume "h0 0 = b \<and> h0 1 = a"
        have hcomp: "top1_homeomorphism_on I_set I_top A (subspace_topology T' TT' A) (h0 \<circ> (\<lambda>t::real. 1-t))"
          by (rule homeomorphism_on_comp[OF unit_interval_reversal_homeomorphism hh0])
        have "(h0 \<circ> (\<lambda>t::real. 1-t)) 0 = a" unfolding comp_def
          using \<open>h0 0 = b \<and> h0 1 = a\<close> by simp
        moreover have "(h0 \<circ> (\<lambda>t::real. 1-t)) 1 = b" unfolding comp_def
          using \<open>h0 0 = b \<and> h0 1 = a\<close> by simp
        ultimately show ?thesis using that[OF hcomp] by (by100 blast)
      qed
    qed
    obtain hBf where hhBf: "top1_homeomorphism_on I_set I_top B (subspace_topology T' TT' B) hBf"
        and hhBf0: "hBf 0 = b" and hhBf1: "hBf 1 = a"
    proof -
      obtain h0 where hh0: "top1_homeomorphism_on I_set I_top B (subspace_topology T' TT' B) h0"
        using hB_arc unfolding top1_is_arc_on_def by (by100 blast)
      have heps0: "top1_arc_endpoints_on B (subspace_topology T' TT' B) = {h0 0, h0 1}"
        by (rule arc_endpoints_are_boundary[OF hstrict hhaus hB_sub hB_arc hh0])
      have "h0 0 \<noteq> h0 1"
      proof
        assume "h0 0 = h0 1"
        hence "{h0 0, h0 1} = {h0 0}" by simp
        hence "card {a, b} \<le> 1" using heps0 hep_B by simp
        thus False using hab by simp
      qed
      have hab_h0B: "{h0 0, h0 1} = {a, b}" using heps0 hep_B by simp
      from doubleton_eq_iff[OF hab_h0B \<open>h0 0 \<noteq> h0 1\<close>]
      show ?thesis
      proof
        assume "h0 0 = a \<and> h0 1 = b"
        have hcomp: "top1_homeomorphism_on I_set I_top B (subspace_topology T' TT' B) (h0 \<circ> (\<lambda>t::real. 1-t))"
          by (rule homeomorphism_on_comp[OF unit_interval_reversal_homeomorphism hh0])
        have "(h0 \<circ> (\<lambda>t::real. 1-t)) 0 = b" unfolding comp_def
          using \<open>h0 0 = a \<and> h0 1 = b\<close> by simp
        moreover have "(h0 \<circ> (\<lambda>t::real. 1-t)) 1 = a" unfolding comp_def
          using \<open>h0 0 = a \<and> h0 1 = b\<close> by simp
        ultimately show ?thesis using that[OF hcomp] by (by100 blast)
      next
        assume "h0 0 = b \<and> h0 1 = a" thus ?thesis using that[OF hh0] by (by100 blast)
      qed
    qed
    \<comment> \<open>Use loop\\_factors\\_through\\_S1 for the SCC construction.
       hAf is a path a \\<to> b in T'. hBf is a path b \\<to> a. Path product gives a loop.
       loop\\_factors\\_through\\_S1 gives continuous h: S1 \\<to> T'. Then show h is inj + surj.\<close>
    \<comment> \<open>hAf, hBf are continuous into T' (from subspace to ambient).\<close>
    have hI_top: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hAf_cont_T: "top1_continuous_map_on I_set I_top T' TT' hAf"
    proof -
      have hAf_cont_sub: "top1_continuous_map_on I_set I_top A (subspace_topology T' TT' A) hAf"
        using hhAf unfolding top1_homeomorphism_on_def by (by100 blast)
      \<comment> \<open>Continuous into subspace + subspace \\<subseteq> ambient \\<Rightarrow> continuous into ambient (Theorem 18.2 clause 6).\<close>
      from Theorem_18_2[OF hI_top htop htop] have
        "\<forall>W f. top1_continuous_map_on I_set I_top T' TT' f \<and> T' \<subseteq> W
          \<and> TT' = subspace_topology W TT' T' \<longrightarrow> top1_continuous_map_on I_set I_top W TT' f"
        by (by100 blast)
      \<comment> \<open>Actually use clause: continuous into subspace \\<Rightarrow> continuous into ambient.\<close>
      have hTA: "is_topology_on A (subspace_topology T' TT' A)"
        by (rule subspace_topology_is_topology_on[OF htop hA_sub])
      have "top1_continuous_map_on I_set I_top A (subspace_topology T' TT' A) hAf
          \<and> A \<subseteq> T' \<and> subspace_topology T' TT' A = subspace_topology T' TT' A"
        using hAf_cont_sub hA_sub by simp
      thus ?thesis using Theorem_18_2(6)[OF hI_top hTA htop, rule_format] by (by100 blast)
    qed
    have hBf_cont_T: "top1_continuous_map_on I_set I_top T' TT' hBf"
    proof -
      have hBf_cont_sub: "top1_continuous_map_on I_set I_top B (subspace_topology T' TT' B) hBf"
        using hhBf unfolding top1_homeomorphism_on_def by (by100 blast)
      have hTB: "is_topology_on B (subspace_topology T' TT' B)"
        by (rule subspace_topology_is_topology_on[OF htop hB_sub])
      have "top1_continuous_map_on I_set I_top B (subspace_topology T' TT' B) hBf
          \<and> B \<subseteq> T' \<and> subspace_topology T' TT' B = subspace_topology T' TT' B"
        using hBf_cont_sub hB_sub by simp
      thus ?thesis using Theorem_18_2(6)[OF hI_top hTB htop, rule_format] by (by100 blast)
    qed
    \<comment> \<open>hAf is a path from a to b in T'. hBf is a path from b to a.\<close>
    have hAf_path: "top1_is_path_on T' TT' a b hAf"
      unfolding top1_is_path_on_def using hAf_cont_T hhAf0 hhAf1 by (by100 blast)
    have hBf_path: "top1_is_path_on T' TT' b a hBf"
      unfolding top1_is_path_on_def using hBf_cont_T hhBf0 hhBf1 by (by100 blast)
    \<comment> \<open>Path product is a loop at a.\<close>
    define g where "g = top1_path_product hAf hBf"
    have hg_loop: "top1_is_loop_on T' TT' a g"
    proof -
      from top1_path_product_is_path[OF htop hAf_path hBf_path]
      have "top1_is_path_on T' TT' a a g" unfolding g_def .
      thus ?thesis unfolding top1_is_loop_on_def .
    qed
    \<comment> \<open>Factor through S1: get continuous h: S1 \\<to> T'.\<close>
    from loop_factors_through_S1[OF htop hg_loop]
    obtain h where hh_cont: "top1_continuous_map_on top1_S1 top1_S1_topology T' TT' h"
        and hh_base: "h (1, 0) = a"
        and hh_lift: "\<forall>s\<in>I_set. g s = h (top1_R_to_S1 s)"
      by (by100 blast)
    \<comment> \<open>h is injective and surjective.\<close>
    \<comment> \<open>g is injective on [0, 1): hAf injective on [0,1/2], hBf on (1/2,1), images disjoint.\<close>
    have hAf_inj: "inj_on hAf I_set" using hhAf unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have hBf_inj: "inj_on hBf I_set" using hhBf unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have hAf_surj: "hAf ` I_set = A" using hhAf unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have hBf_surj: "hBf ` I_set = B" using hhBf unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    have hg_inj_half: "inj_on g {s. 0 \<le> s \<and> s < 1}"
    proof (rule inj_onI)
      fix s1 s2 assume hs1: "s1 \<in> {s. 0 \<le> s \<and> s < 1}" and hs2: "s2 \<in> {s. 0 \<le> s \<and> s < 1}"
        and hgs: "g s1 = g s2"
      have hs1_ge: "s1 \<ge> 0" and hs1_lt: "s1 < 1" using hs1 by simp_all
      have hs2_ge: "s2 \<ge> 0" and hs2_lt: "s2 < 1" using hs2 by simp_all
      show "s1 = s2"
      proof (cases "s1 \<le> 1/2")
        case True note hs1_le = this
        show ?thesis
        proof (cases "s2 \<le> 1/2")
          case True \<comment> \<open>Both in [0, 1/2]: g = hAf(2*s). hAf injective \\<Rightarrow> s1 = s2.\<close>
          have "g s1 = hAf (2 * s1)" unfolding g_def top1_path_product_def using hs1_le by simp
          have "g s2 = hAf (2 * s2)" unfolding g_def top1_path_product_def using True by simp
          hence "hAf (2 * s1) = hAf (2 * s2)" using hgs \<open>g s1 = hAf (2 * s1)\<close> by simp
          have "2 * s1 \<in> I_set" using hs1_ge hs1_le unfolding top1_unit_interval_def by (by100 auto)
          have "2 * s2 \<in> I_set" using hs2_ge True unfolding top1_unit_interval_def by (by100 auto)
          from inj_onD[OF hAf_inj \<open>hAf (2*s1) = hAf (2*s2)\<close> \<open>2*s1 \<in> I_set\<close> \<open>2*s2 \<in> I_set\<close>]
          show ?thesis by simp
        next
          case False \<comment> \<open>s1 \\<le> 1/2, s2 > 1/2: g(s1) \\<in> A, g(s2) \\<in> B \\<setminus> {a,b}. A \\<inter> (B\\<setminus>{a,b}) = \\<emptyset>.\<close>
          hence hs2_gt: "s2 > 1/2" by linarith
          have "g s1 = hAf (2 * s1)" unfolding g_def top1_path_product_def using hs1_le by simp
          hence "g s1 \<in> A" using hAf_surj hs1_ge hs1_le
            unfolding top1_unit_interval_def by (by100 force)
          have "\<not> (s2 \<le> 1/2)" using hs2_gt by linarith
          hence "g s2 = hBf (2 * s2 - 1)" unfolding g_def top1_path_product_def by simp
          have "2 * s2 - 1 \<in> {x. 0 < x \<and> x < 1}" using hs2_gt hs2_lt by simp
          hence "2 * s2 - 1 \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
          have "2 * s2 - 1 \<noteq> 0" using hs2_gt by linarith
          have "2 * s2 - 1 \<noteq> 1" using hs2_lt by linarith
          have "g s2 \<noteq> b"
          proof
            assume "g s2 = b"
            hence "hBf (2*s2-1) = b" using \<open>g s2 = hBf (2*s2-1)\<close> by simp
            hence "hBf (2*s2-1) = hBf 0" using hhBf0 by simp
            from inj_onD[OF hBf_inj this \<open>2*s2-1 \<in> I_set\<close> h0_I]
            show False using \<open>2*s2-1 \<noteq> 0\<close> by simp
          qed
          have "g s2 \<noteq> a"
          proof
            assume "g s2 = a"
            hence "hBf (2*s2-1) = a" using \<open>g s2 = hBf (2*s2-1)\<close> by simp
            hence "hBf (2*s2-1) = hBf 1" using hhBf1 by simp
            from inj_onD[OF hBf_inj this \<open>2*s2-1 \<in> I_set\<close> h1_I]
            show False using \<open>2*s2-1 \<noteq> 1\<close> by simp
          qed
          have "g s2 \<in> B" using hBf_surj \<open>g s2 = hBf (2*s2-1)\<close> \<open>2*s2-1 \<in> I_set\<close> by (by100 blast)
          have "g s1 \<in> A \<inter> B" using \<open>g s1 \<in> A\<close> \<open>g s2 \<in> B\<close> hgs by (by100 force)
          hence "g s1 \<in> {a, b}" using hAB_inter by simp
          hence "g s1 = a \<or> g s1 = b" by (by100 blast)
          hence "g s2 = a \<or> g s2 = b" using hgs by simp
          thus ?thesis using \<open>g s2 \<noteq> a\<close> \<open>g s2 \<noteq> b\<close> by simp
        qed
      next
        case False note hs1_gt = this
        hence hs1_gt': "s1 > 1/2" by linarith
        show ?thesis
        proof (cases "s2 \<le> 1/2")
          case True \<comment> \<open>Symmetric to above.\<close>
          have "g s2 = hAf (2 * s2)" unfolding g_def top1_path_product_def using True by simp
          hence "g s2 \<in> A" using hAf_surj hs2_ge True
            unfolding top1_unit_interval_def by (by100 force)
          have "\<not> (s1 \<le> 1/2)" using hs1_gt' by linarith
          hence "g s1 = hBf (2 * s1 - 1)" unfolding g_def top1_path_product_def by simp
          have "2 * s1 - 1 \<in> I_set" using hs1_gt' hs1_lt unfolding top1_unit_interval_def by (by100 auto)
          have "2 * s1 - 1 \<noteq> 0" using hs1_gt' by linarith
          have "2 * s1 - 1 \<noteq> 1" using hs1_lt by linarith
          have "g s1 \<noteq> b"
          proof
            assume "g s1 = b"
            hence "hBf (2*s1-1) = hBf 0" using \<open>g s1 = hBf (2*s1-1)\<close> hhBf0 by simp
            from inj_onD[OF hBf_inj this \<open>2*s1-1 \<in> I_set\<close> h0_I]
            show False using \<open>2*s1-1 \<noteq> 0\<close> by simp
          qed
          have "g s1 \<noteq> a"
          proof
            assume "g s1 = a"
            hence "hBf (2*s1-1) = hBf 1" using \<open>g s1 = hBf (2*s1-1)\<close> hhBf1 by simp
            from inj_onD[OF hBf_inj this \<open>2*s1-1 \<in> I_set\<close> h1_I]
            show False using \<open>2*s1-1 \<noteq> 1\<close> by simp
          qed
          have "g s1 \<in> B" using hBf_surj \<open>g s1 = hBf (2*s1-1)\<close> \<open>2*s1-1 \<in> I_set\<close> by (by100 blast)
          have "g s2 \<in> A \<inter> B" using \<open>g s2 \<in> A\<close> \<open>g s1 \<in> B\<close> hgs by (by100 force)
          hence "g s2 \<in> {a, b}" using hAB_inter by simp
          hence "g s1 = a \<or> g s1 = b" using hgs by (by100 force)
          thus ?thesis using \<open>g s1 \<noteq> a\<close> \<open>g s1 \<noteq> b\<close> by simp
        next
          case False \<comment> \<open>Both > 1/2: g = hBf(2*s - 1). hBf injective \\<Rightarrow> s1 = s2.\<close>
          hence hs2_gt: "s2 > 1/2" by linarith
          have "\<not> (s1 \<le> 1/2)" using hs1_gt' by linarith
          have "\<not> (s2 \<le> 1/2)" using hs2_gt by linarith
          have "g s1 = hBf (2*s1-1)" unfolding g_def top1_path_product_def using \<open>\<not> (s1 \<le> 1/2)\<close> by simp
          have "g s2 = hBf (2*s2-1)" unfolding g_def top1_path_product_def using \<open>\<not> (s2 \<le> 1/2)\<close> by simp
          hence "hBf (2*s1-1) = hBf (2*s2-1)" using hgs \<open>g s1 = hBf (2*s1-1)\<close> by simp
          have "2*s1-1 \<in> I_set" using hs1_gt' hs1_lt unfolding top1_unit_interval_def by (by100 auto)
          have "2*s2-1 \<in> I_set" using hs2_gt hs2_lt unfolding top1_unit_interval_def by (by100 auto)
          from inj_onD[OF hBf_inj \<open>hBf (2*s1-1) = hBf (2*s2-1)\<close> \<open>2*s1-1 \<in> I_set\<close> \<open>2*s2-1 \<in> I_set\<close>]
          show ?thesis by simp
        qed
      qed
    qed
    \<comment> \<open>h is injective on S1: for p, q \\<in> S1, find preimages in [0,1), use g-injectivity.\<close>
    have hh_inj: "inj_on h top1_S1"
    proof (rule inj_onI)
      fix p q assume hp: "p \<in> top1_S1" and hq: "q \<in> top1_S1" and hpq: "h p = h q"
      \<comment> \<open>Find \\<theta>p, \\<theta>q \\<in> [0,1) with R\\_to\\_S1(\\<theta>) = p, q.\<close>
      from S1_point_to_angle[OF hp] obtain tp where htp: "top1_R_to_S1 tp = p" by (by100 blast)
      from S1_point_to_angle[OF hq] obtain tq where htq: "top1_R_to_S1 tq = q" by (by100 blast)
      \<comment> \<open>Normalize to [0, 1) using integer shifts.\<close>
      define sp where "sp = tp - of_int \<lfloor>tp\<rfloor>"
      define sq where "sq = tq - of_int \<lfloor>tq\<rfloor>"
      have hsp_range: "0 \<le> sp \<and> sp < 1" unfolding sp_def by linarith
      have hsq_range: "0 \<le> sq \<and> sq < 1" unfolding sq_def by linarith
      have hsp_S1: "top1_R_to_S1 sp = p"
        using htp top1_R_to_S1_int_shift[of "tp - of_int \<lfloor>tp\<rfloor>" "\<lfloor>tp\<rfloor>"] unfolding sp_def by simp
      have hsq_S1: "top1_R_to_S1 sq = q"
        using htq top1_R_to_S1_int_shift[of "tq - of_int \<lfloor>tq\<rfloor>" "\<lfloor>tq\<rfloor>"] unfolding sq_def by simp
      have hsp_I: "sp \<in> I_set" using hsp_range unfolding top1_unit_interval_def by (by100 auto)
      have hsq_I: "sq \<in> I_set" using hsq_range unfolding top1_unit_interval_def by (by100 auto)
      have "g sp = h (top1_R_to_S1 sp)" using hh_lift[rule_format, OF hsp_I] by simp
      hence "g sp = h p" using hsp_S1 by simp
      have "g sq = h (top1_R_to_S1 sq)" using hh_lift[rule_format, OF hsq_I] by simp
      hence "g sq = h q" using hsq_S1 by simp
      hence "g sp = g sq" using \<open>g sp = h p\<close> hpq by simp
      have hsp_mem: "sp \<in> {s. 0 \<le> s \<and> s < 1}" using hsp_range by simp
      have hsq_mem: "sq \<in> {s. 0 \<le> s \<and> s < 1}" using hsq_range by simp
      from inj_onD[OF hg_inj_half \<open>g sp = g sq\<close> hsp_mem hsq_mem]
      have "sp = sq" .
      thus "p = q" using hsp_S1 hsq_S1 by simp
    qed
    have hh_img: "h ` top1_S1 = T'"
    proof
      \<comment> \<open>h(S1) \\<subseteq> T': h is continuous into T'.\<close>
      show "h ` top1_S1 \<subseteq> T'"
        using hh_cont unfolding top1_continuous_map_on_def by (by100 blast)
    next
      \<comment> \<open>T' \\<subseteq> h(S1): g surjects I\\_set \\<to> A \\<union> B = T', and g = h \\<circ> R\\_to\\_S1.\<close>
      have hAf_surj: "hAf ` I_set = A" using hhAf unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have hBf_surj: "hBf ` I_set = B" using hhBf unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      show "T' \<subseteq> h ` top1_S1"
      proof
        fix z assume hz: "z \<in> T'"
        hence "z \<in> A \<union> B" using hcover by simp
        thus "z \<in> h ` top1_S1"
        proof
          assume "z \<in> A"
          then obtain t where ht: "t \<in> I_set" "hAf t = z" using hAf_surj by (by100 blast)
          \<comment> \<open>g(t/2) = hAf(2*(t/2)) = hAf(t) = z for t/2 \\<in> [0, 1/2] \\<subseteq> I\\_set.\<close>
          have "t \<ge> 0 \<and> t \<le> 1" using ht(1) unfolding top1_unit_interval_def by (by100 auto)
          hence ht2: "t/2 \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
          have "t/2 \<le> 1/2" using \<open>t \<ge> 0 \<and> t \<le> 1\<close> by linarith
          hence "g (t/2) = hAf (2 * (t/2))" unfolding g_def top1_path_product_def by simp
          hence "g (t/2) = z" using ht(2) by simp
          have "top1_R_to_S1 (t/2) \<in> top1_S1" unfolding top1_S1_def top1_R_to_S1_def by simp
          moreover have "h (top1_R_to_S1 (t/2)) = z"
            using hh_lift[rule_format, OF ht2] \<open>g (t/2) = z\<close> by simp
          ultimately show ?thesis by (by100 blast)
        next
          assume "z \<in> B"
          then obtain t where ht: "t \<in> I_set" "hBf t = z" using hBf_surj by (by100 blast)
          have "t \<ge> 0 \<and> t \<le> 1" using ht(1) unfolding top1_unit_interval_def by (by100 auto)
          show ?thesis
          proof (cases "t = 0")
            case True \<comment> \<open>t = 0: z = hBf(0) = b. g(1/2) = hAf(1) = b = z.\<close>
            hence "z = b" using ht(2) hhBf0 by simp
            have h12: "(1::real)/2 \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
            have "g (1/2) = hAf 1" unfolding g_def top1_path_product_def by simp
            hence "g (1/2) = b" using hhAf1 by simp
            hence "g (1/2) = z" using \<open>z = b\<close> by simp
            have "top1_R_to_S1 (1/2) \<in> top1_S1" unfolding top1_S1_def top1_R_to_S1_def by simp
            moreover have "h (top1_R_to_S1 (1/2)) = z"
              using hh_lift[rule_format, OF h12] \<open>g (1/2) = z\<close> by simp
            ultimately show ?thesis by (by100 blast)
          next
            case False \<comment> \<open>t > 0: use (t+1)/2 > 1/2.\<close>
            hence "t > 0" using \<open>t \<ge> 0 \<and> t \<le> 1\<close> by linarith
            have ht2: "(t + 1) / 2 \<in> I_set" using \<open>t \<ge> 0 \<and> t \<le> 1\<close>
              unfolding top1_unit_interval_def by (by100 auto)
            have "(t + 1) / 2 > 1/2" using \<open>t > 0\<close> by simp
            hence "\<not> ((t + 1) / 2 \<le> 1/2)" by linarith
            define s where "s = (t + 1) / (2::real)"
            have hs_gt: "\<not> (s \<le> 1/2)" using \<open>t > 0\<close> unfolding s_def by simp
            have "g s = hBf (2 * s - 1)" unfolding g_def top1_path_product_def using hs_gt by simp
            have "2 * s = t + 1" unfolding s_def by simp
            hence "2 * s - 1 = t" by linarith
            hence "g s = hBf t" using \<open>g s = hBf (2 * s - 1)\<close> by simp
            hence "g ((t + 1) / 2) = z" using ht(2) s_def by simp
            hence "g ((t + 1) / 2) = z" using ht(2) by simp
            have "top1_R_to_S1 ((t + 1) / 2) \<in> top1_S1"
              unfolding top1_S1_def top1_R_to_S1_def by simp
            moreover have "h (top1_R_to_S1 ((t + 1) / 2)) = z"
              using hh_lift[rule_format, OF ht2] \<open>g ((t + 1) / 2) = z\<close> by simp
            ultimately show ?thesis by (by100 blast)
          qed
        qed
      qed
    qed
    show ?thesis unfolding top1_simple_closed_curve_on_def
      using hh_cont hh_inj hh_img by (by100 blast)
  qed
  \<comment> \<open>T' is a retract of itself (identity).\<close>
  have hretract: "top1_retract_of_on T' TT' T'"
    unfolding top1_retract_of_on_def top1_is_retraction_on_def
  proof (rule exI[of _ id], intro conjI)
    show "T' \<subseteq> T'" by (by100 blast)
    show "top1_continuous_map_on T' TT' T' (subspace_topology T' TT' T') id"
      unfolding top1_continuous_map_on_def subspace_topology_def
    proof (intro conjI ballI allI impI)
      fix x assume "x \<in> T'" thus "id x \<in> T'" by (by100 simp)
    next
      fix V assume "V \<in> {T' \<inter> U |U. U \<in> TT'}"
      then obtain U where hU: "U \<in> TT'" "V = T' \<inter> U" by (by100 blast)
      have "T' \<in> TT'" using htop unfolding is_topology_on_def by (by100 blast)
      have hfin_TU: "finite {T', U}" by (by100 simp)
      have hne_TU: "{T', U} \<noteq> {}" by (by100 simp)
      have hsub_TU: "{T', U} \<subseteq> TT'" using \<open>T' \<in> TT'\<close> hU(1) by (by100 blast)
      have "\<Inter>{T', U} \<in> TT'"
        using htop[unfolded is_topology_on_def, THEN conjunct2, THEN conjunct2, THEN conjunct2,
            rule_format, of "{T', U}"] hfin_TU hne_TU hsub_TU by (by100 blast)
      hence "T' \<inter> U \<in> TT'" by (by100 simp)
      have "{x \<in> T'. id x \<in> V} = T' \<inter> U" using hU(2) by (by100 force)
      thus "{x \<in> T'. id x \<in> V} \<in> TT'" using \<open>T' \<inter> U \<in> TT'\<close> by simp
    qed
    show "\<forall>a\<in>T'. id a = a" by (by100 simp)
  qed
  from scc_in_sc_false[OF hsc htop hhaus hSCC hretract]
  show False by simp
qed


\<comment> \<open>Tree Euler formula V = E + 1 for SC graphs, proved via building order.
   Key: SC prevents chord arcs, so the graph can be built entirely with pendant arcs.
   Each pendant arc adds 1 vertex and 1 arc, preserving V = E + 1.
   Uses: graph\\_euler\\_invariance, graph\\_pi1\\_free\\_weak, Lemma\\_84\\_2\\_tree\\_union\\_arc.\<close>
lemma tree_euler_from_sc:
  fixes T' :: "'a set" and TT' :: "'a set set"
  assumes htree: "top1_is_tree_on T' TT'"
      and h\<A>: "\<forall>A\<in>\<A>'. A \<subseteq> T' \<and> top1_is_arc_on A (subspace_topology T' TT' A)"
      and h\<A>_cover: "\<Union>\<A>' = T'"
      and h\<A>_inter: "\<forall>A\<in>\<A>'. \<forall>B\<in>\<A>'. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T' TT' A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T' TT' B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and hfin: "finite \<A>'" and hne: "\<A>' \<noteq> {}"
  shows "card (top1_graph_vertex_set T' TT' \<A>') = card \<A>' + 1"
  \<comment> \<open>Proof via graph\\_euler\\_invariance:
     V' - card(\\<A>') is the same for all decompositions (graph\\_euler\\_invariance).
     We show there EXISTS a decomposition with card = 1, giving V - E = 2 - 1 = 1.
     Construction: merge adjacent arcs sharing exactly 1 vertex until card = 1.
     SC guarantees we can always find such a pair (the "all share 2" case is impossible
     because it would give a circle/bundle with non-trivial \\<pi>1).\<close>
  using hfin hne h\<A> h\<A>_cover h\<A>_inter
proof (induction "card \<A>'" arbitrary: \<A>' rule: less_induct)
  case (less \<A>')
  show ?case
  proof (cases "card \<A>' \<le> 1")
    case True
    \<comment> \<open>Base: card = 1 (can't be 0 since \\<A>' \\<noteq> {}).\<close>
    have "card \<A>' = 1"
    proof -
      have "card \<A>' \<noteq> 0" using less.prems(2) less.prems(1) card_eq_0_iff by (by100 auto)
      thus ?thesis using True by linarith
    qed
    from card_1_singletonE[OF this] obtain A0 where h\<A>_eq: "\<A>' = {A0}" by (by100 blast)
    have hA0_arc: "top1_is_arc_on A0 (subspace_topology T' TT' A0)" using less.prems(3) h\<A>_eq by (by100 blast)
    have hA0_sub: "A0 \<subseteq> T'" using less.prems(3) h\<A>_eq by (by100 blast)
    have hstrict: "is_topology_on_strict T' TT'"
      using htree unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
    have hhaus: "is_hausdorff_on T' TT'"
      using htree unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
    obtain h where hh: "top1_homeomorphism_on I_set I_top A0 (subspace_topology T' TT' A0) h"
      using hA0_arc unfolding top1_is_arc_on_def by (by100 blast)
    have "top1_arc_endpoints_on A0 (subspace_topology T' TT' A0) = {h 0, h 1}"
      by (rule arc_endpoints_are_boundary[OF hstrict hhaus hA0_sub hA0_arc hh])
    moreover have "h 0 \<noteq> h 1"
    proof
      assume "h 0 = h 1"
      have "inj_on h I_set" using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      from inj_onD[OF this \<open>h 0 = h 1\<close>] show False unfolding top1_unit_interval_def by (by100 auto)
    qed
    ultimately have "card (top1_arc_endpoints_on A0 (subspace_topology T' TT' A0)) = 2" by (by100 simp)
    have "top1_graph_vertex_set T' TT' \<A>' = top1_arc_endpoints_on A0 (subspace_topology T' TT' A0)"
      unfolding top1_graph_vertex_set_def using h\<A>_eq by simp
    thus ?thesis using \<open>card _ = 2\<close> \<open>card \<A>' = 1\<close> by simp
  next
    case False
    hence hcard_ge2: "card \<A>' \<ge> 2"
    proof -
      have "card \<A>' \<noteq> 0" using less.prems(2) less.prems(1) card_eq_0_iff by (by100 auto)
      thus ?thesis using False by linarith
    qed
    \<comment> \<open>Strategy: use graph\\_pi1\\_free\\_weak to get a decomposition \\<A>0 with coherent topology.
       For SC: all arcs are tree arcs (S0 = {}). Use tree\\_euler\\_from\\_leaf with leaf oracle
       to get V(\\<A>0) = card(\\<A>0) + 1. Transfer via euler\\_invariance.\<close>
    have hgraph: "top1_is_graph_on T' TT'"
      using htree unfolding top1_is_tree_on_def by (by100 blast)
    have hconn: "top1_connected_on T' TT'"
      using htree unfolding top1_is_tree_on_def by (by100 blast)
    have hSC: "top1_simply_connected_on T' TT'"
      using htree unfolding top1_is_tree_on_def by (by100 blast)
    \<comment> \<open>Step 1: Derive coherent topology for our decomposition (graph\\_coherent\\_any\\_decomposition).\<close>
    have hcoh: "\<forall>C. C \<subseteq> T' \<longrightarrow>
        (closedin_on T' TT' C \<longleftrightarrow>
         (\<forall>A\<in>\<A>'. closedin_on A (subspace_topology T' TT' A) (A \<inter> C)))"
      by (rule graph_coherent_any_decomposition[OF hgraph less.prems(3) less.prems(4)
          less.prems(5) less.prems(1)])
    \<comment> \<open>Step 2: Leaf existence oracle (topological bridge sorry).
       In a tree with coherent topology and card \\<ge> 2, there exists a leaf.
       Proof sketch (Munkres Lemma 84.2): if no leaf, all degrees \\<ge> 2.
       Non-backtracking walk + pigeonhole gives a closed reduced edge path (CREP).
       CREP in a CW-complex (coherent topology) gives non-trivial \\<pi>1 element.
       But \\<pi>1 = 1 (SC). Contradiction.\<close>
    have hleaf_oracle: "\<And>(T0 :: 'a set) TT0 \<B>.
      \<lbrakk>top1_is_tree_on T0 TT0;
       \<forall>A\<in>\<B>. A \<subseteq> T0 \<and> top1_is_arc_on A (subspace_topology T0 TT0 A);
       \<Union>\<B> = T0;
       \<forall>A\<in>\<B>. \<forall>B\<in>\<B>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T0 TT0 A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T0 TT0 B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2;
       finite \<B>; card \<B> \<ge> 2;
       \<forall>C. C \<subseteq> T0 \<longrightarrow> (closedin_on T0 TT0 C \<longleftrightarrow>
           (\<forall>A\<in>\<B>. closedin_on A (subspace_topology T0 TT0 A) (A \<inter> C)))\<rbrakk>
      \<Longrightarrow> \<exists>A0 v. A0 \<in> \<B> \<and> v \<in> top1_arc_endpoints_on A0 (subspace_topology T0 TT0 A0)
          \<and> (\<forall>B\<in>\<B>. B \<noteq> A0 \<longrightarrow> v \<notin> B)"
      by (rule tree_leaf_existence_bridge)
    \<comment> \<open>Step 3: Apply tree\\_euler\\_from\\_leaf with the leaf oracle to get V = E + 1.\<close>
    from tree_euler_from_leaf[OF hleaf_oracle]
    have "\<forall>(T0 :: 'a set) TT0 \<B>. card \<B> = card \<A>' \<longrightarrow>
        top1_is_tree_on T0 TT0 \<longrightarrow>
        (\<forall>A\<in>\<B>. A \<subseteq> T0 \<and> top1_is_arc_on A (subspace_topology T0 TT0 A)) \<longrightarrow>
        \<Union>\<B> = T0 \<longrightarrow>
        (\<forall>A\<in>\<B>. \<forall>B\<in>\<B>. A \<noteq> B \<longrightarrow>
             A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T0 TT0 A)
           \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T0 TT0 B)
           \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2) \<longrightarrow>
        finite \<B> \<longrightarrow> \<B> \<noteq> {} \<longrightarrow>
        (\<forall>C. C \<subseteq> T0 \<longrightarrow> (closedin_on T0 TT0 C \<longleftrightarrow>
            (\<forall>A\<in>\<B>. closedin_on A (subspace_topology T0 TT0 A) (A \<inter> C)))) \<longrightarrow>
        card (top1_graph_vertex_set T0 TT0 \<B>) = card \<A>' + 1" .
    \<comment> \<open>Step 4: Instantiate for our specific T', TT', \\<A>'.\<close>
    from spec[OF spec[OF spec[OF this, of T'], of TT'], of \<A>']
    show ?thesis using htree less.prems hcoh by (by5000 simp)
  qed
qed

\<comment> \<open>Standalone leaf existence for finite trees.
   Uses tree\\_euler\\_from\\_sc + degree\\_sum\\_leaf.\<close>
lemma finite_tree_has_leaf:
  assumes "top1_is_tree_on T' TT'"
      and "\<forall>A\<in>\<A>'. A \<subseteq> T' \<and> top1_is_arc_on A (subspace_topology T' TT' A)"
      and "\<Union>\<A>' = T'"
      and "\<forall>A\<in>\<A>'. \<forall>B\<in>\<A>'. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T' TT' A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T' TT' B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and "finite \<A>'" and "card \<A>' \<ge> 2"
      and "\<forall>C. C \<subseteq> T' \<longrightarrow> (closedin_on T' TT' C \<longleftrightarrow>
          (\<forall>A\<in>\<A>'. closedin_on A (subspace_topology T' TT' A) (A \<inter> C)))"
  shows "\<exists>A0 v. A0 \<in> \<A>' \<and> v \<in> top1_arc_endpoints_on A0 (subspace_topology T' TT' A0)
      \<and> (\<forall>B\<in>\<A>'. B \<noteq> A0 \<longrightarrow> v \<notin> B)"
  proof -
    \<comment> \<open>Step 1: Each arc has exactly 2 distinct endpoints.\<close>
    have hstrict': "is_topology_on_strict T' TT'"
      using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
    have hhaus': "is_hausdorff_on T' TT'"
      using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
    have h2ep: "\<forall>A\<in>\<A>'. \<exists>a b. a \<noteq> b \<and>
        top1_arc_endpoints_on A (subspace_topology T' TT' A) = {a, b}"
    proof (intro ballI)
      fix A assume "A \<in> \<A>'"
      have "A \<subseteq> T'" "top1_is_arc_on A (subspace_topology T' TT' A)"
        using assms(2) \<open>A \<in> \<A>'\<close> by (by100 blast)+
      then obtain h where "top1_homeomorphism_on I_set I_top A (subspace_topology T' TT' A) h"
        unfolding top1_is_arc_on_def by (by100 blast)
      have "top1_arc_endpoints_on A (subspace_topology T' TT' A) = {h 0, h 1}"
        by (rule arc_endpoints_are_boundary[OF hstrict' hhaus' \<open>A \<subseteq> T'\<close>
            \<open>top1_is_arc_on A _\<close> \<open>top1_homeomorphism_on _ _ _ _ h\<close>])
      moreover have "h 0 \<noteq> h 1"
      proof
        assume "h 0 = h 1"
        have "inj_on h I_set" using \<open>top1_homeomorphism_on _ _ _ _ h\<close>
            unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        from inj_onD[OF this \<open>h 0 = h 1\<close>] show False
          unfolding top1_unit_interval_def by (by100 auto)
      qed
      ultimately show "\<exists>a b. a \<noteq> b \<and>
          top1_arc_endpoints_on A (subspace_topology T' TT' A) = {a, b}"
        by (by100 blast)
    qed
    \<comment> \<open>Step 2: Degree of each vertex is \\<ge> 1 (every vertex is endpoint of some arc).
       If no leaf exists: all vertices have degree \\<ge> 2.\<close>
    \<comment> \<open>Step 3: The topological bridge. By contradiction: assume no leaf exists.
       Then every vertex has degree \\<ge> 2. Construct a non-backtracking walk.
       By finiteness, revisit a VERTEX. This gives a cycle of distinct arcs.
       The cycle forms a loop in T'. Since T' is SC (tree), the loop is null-homotopic.
       But the loop, being a cycle of distinct arcs, is non-null-homotopic.
       Contradiction.
       The key claim: a non-backtracking cycle of arcs gives a NON-null-homotopic loop.
       This is the topological bridge.\<close>
    \<comment> \<open>Step 3: The walk+pigeonhole argument (Munkres Lemma 84.2 converse).
       Assume no leaf (all degrees \\<ge> 2). Construct non-backtracking walk.
       By finiteness, revisit a vertex. This gives a "closed reduced edge path."
       Bridge: in an SC graph, no closed reduced edge path exists.
       Contradiction.\<close>
    \<comment> \<open>Assume for contradiction: no leaf exists.\<close>
    show ?thesis
    proof (rule ccontr)
      assume hno: "\<not> (\<exists>A0 v. A0 \<in> \<A>' \<and> v \<in> top1_arc_endpoints_on A0 (subspace_topology T' TT' A0) \<and>
          (\<forall>B\<in>\<A>'. B \<noteq> A0 \<longrightarrow> v \<notin> B))"
      \<comment> \<open>Every endpoint of every arc is shared with another arc (degree \\<ge> 2).\<close>
      have hshared: "\<forall>A0\<in>\<A>'. \<forall>v\<in>top1_arc_endpoints_on A0 (subspace_topology T' TT' A0).
          \<exists>B\<in>\<A>'. B \<noteq> A0 \<and> v \<in> B"
      proof (intro ballI)
        fix A0 v assume "A0 \<in> \<A>'" "v \<in> top1_arc_endpoints_on A0 (subspace_topology T' TT' A0)"
        show "\<exists>B\<in>\<A>'. B \<noteq> A0 \<and> v \<in> B"
        proof (rule ccontr)
          assume "\<not> (\<exists>B\<in>\<A>'. B \<noteq> A0 \<and> v \<in> B)"
          hence "\<forall>B\<in>\<A>'. B \<noteq> A0 \<longrightarrow> v \<notin> B" by (by100 blast)
          with \<open>A0 \<in> \<A>'\<close> \<open>v \<in> top1_arc_endpoints_on A0 _\<close>
          have "\<exists>A0 v. A0 \<in> \<A>' \<and> v \<in> top1_arc_endpoints_on A0 (subspace_topology T' TT' A0) \<and>
              (\<forall>B\<in>\<A>'. B \<noteq> A0 \<longrightarrow> v \<notin> B)" by (by100 blast)
          with hno show False by (by100 blast)
        qed
      qed
      \<comment> \<open>The topological bridge: SC graph with all vertices shared \\<Rightarrow> \\<bottom>.
         In Munkres' terms: the walk+pigeonhole constructs a closed reduced edge path,
         but SC trees have no such paths.
         Formally: this requires showing that a non-backtracking cycle of distinct arcs
         gives a non-null-homotopic loop in the graph. For the SPECIFIC decompositions
         arising from graph\\_pi1\\_free\\_weak, this follows from the spanning tree construction.
         For arbitrary decompositions, this is the topological bridge sorry.\<close>
      \<comment> \<open>Proof via building order + deformation retract:
         Build T' arc by arc. Each arc is pendant (1 shared vertex) or chord (2 shared).
         Pendant: DR preserves \\<pi>1. Chord: \\<pi>1 grows (free product with Z).
         If any chord: \\<pi>1(T') \\<noteq> 1, contradiction with SC.
         So all pendant: V = E + 1. Degree sum: 2E \\<ge> 2V = 2E + 2. Contradiction.\<close>
      \<comment> \<open>Step 1: Build T' arc by arc. Use Euler invariance to get V = E + 1.\<close>
      have hgraph': "top1_is_graph_on T' TT'"
        using assms(1) unfolding top1_is_tree_on_def by (by100 blast)
      have hconn': "top1_connected_on T' TT'"
        using assms(1) unfolding top1_is_tree_on_def by (by100 blast)
      have hSC': "top1_simply_connected_on T' TT'"
        using assms(1) unfolding top1_is_tree_on_def by (by100 blast)
      \<comment> \<open>V' = card(\\<A>') + 1 from graph\\_euler\\_invariance + building argument.\<close>
      \<comment> \<open>Prove V = E + 1 by graph\\_euler\\_invariance.
         Use the internal decomposition from graph\\_pi1\\_free\\_weak where S0 = {} (SC tree).
         Then V0 - card(\\<A>0) = V' - card(\\<A>') (Euler invariance).
         Need: V0 = card(\\<A>0) + 1 for the internal decomposition.
         This follows from tree\\_euler\\_number\\_one... which depends on THIS lemma.
         INSTEAD: use the building order argument directly.\<close>
      have hV_eq: "card (top1_graph_vertex_set T' TT' \<A>') = card \<A>' + 1"
      proof -
        have "\<A>' \<noteq> {}" using assms(6) by (by100 force)
        from tree_euler_from_sc[OF assms(1) assms(2) assms(3) assms(4) assms(5) this]
        show ?thesis .
      qed
      \<comment> \<open>Step 2: Degree counting gives contradiction.\<close>
      let ?V = "top1_graph_vertex_set T' TT' \<A>'"
      let ?deg = "\<lambda>v. card {A \<in> \<A>'. v \<in> top1_arc_endpoints_on A (subspace_topology T' TT' A)}"
      have hep_fin: "\<forall>A\<in>\<A>'. finite (top1_arc_endpoints_on A (subspace_topology T' TT' A))"
      proof (intro ballI)
        fix A assume "A \<in> \<A>'"
        have "A \<subseteq> T'" "top1_is_arc_on A (subspace_topology T' TT' A)" using assms(2) \<open>A \<in> \<A>'\<close> by (by100 blast)+
        then obtain h where "top1_homeomorphism_on I_set I_top A (subspace_topology T' TT' A) h"
          unfolding top1_is_arc_on_def by (by100 blast)
        from arc_endpoints_are_boundary[OF hstrict' hhaus' \<open>A \<subseteq> T'\<close> \<open>top1_is_arc_on A _\<close> this]
        show "finite (top1_arc_endpoints_on A (subspace_topology T' TT' A))" by (by100 simp)
      qed
      have hV_fin: "finite ?V" unfolding top1_graph_vertex_set_def using assms(5) hep_fin by (by100 blast)
      have hep_card: "\<forall>A\<in>\<A>'. card (top1_arc_endpoints_on A (subspace_topology T' TT' A)) = 2"
      proof (intro ballI)
        fix A assume "A \<in> \<A>'"
        from h2ep[rule_format, OF this] obtain a b where
          "a \<noteq> b" "top1_arc_endpoints_on A (subspace_topology T' TT' A) = {a, b}" by (by100 blast)
        thus "card (top1_arc_endpoints_on A (subspace_topology T' TT' A)) = 2"
          using \<open>a \<noteq> b\<close> by (by100 simp)
      qed
      have hsum: "(\<Sum>v\<in>?V. ?deg v) = 2 * card \<A>'"
      proof -
        let ?ep = "\<lambda>A. top1_arc_endpoints_on A (subspace_topology T' TT' A)"
        have "?V = (\<Union>A\<in>\<A>'. ?ep A)" unfolding top1_graph_vertex_set_def by (by100 blast)
        from double_counting_sum[OF assms(5) hep_fin this]
        have "(\<Sum>v\<in>?V. card {A \<in> \<A>'. v \<in> ?ep A}) = (\<Sum>A\<in>\<A>'. card (?ep A))" .
        also have "\<dots> = (\<Sum>A\<in>\<A>'. 2)" using hep_card by simp
        also have "\<dots> = 2 * card \<A>'" by simp
        finally show ?thesis .
      qed
      \<comment> \<open>hdeg\\_pos not needed for the main argument; hdeg\\_ge2 suffices.\<close>
      \<comment> \<open>All degrees \\<ge> 2 (from hshared + degree definition).\<close>
      have hdeg_ge2: "\<forall>v\<in>?V. ?deg v \<ge> 2"
      proof (intro ballI)
        fix v assume "v \<in> ?V"
        then obtain A0 where hA0: "A0 \<in> \<A>'" "v \<in> top1_arc_endpoints_on A0 (subspace_topology T' TT' A0)"
          unfolding top1_graph_vertex_set_def by (by100 blast)
        from hshared[rule_format, OF hA0(1) hA0(2)]
        obtain B where hB: "B \<in> \<A>'" "B \<noteq> A0" "v \<in> B" by (by100 blast)
        have "v \<in> top1_arc_endpoints_on B (subspace_topology T' TT' B)"
        proof -
          have "v \<in> A0 \<inter> B" using hA0(2) hB(3) unfolding top1_arc_endpoints_on_def by (by100 blast)
          have "A0 \<noteq> B" using hB(2) by simp
          from assms(4)[rule_format, OF hA0(1) hB(1) \<open>A0 \<noteq> B\<close>]
          have "A0 \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T' TT' B)" by (by100 blast)
          thus ?thesis using \<open>v \<in> A0 \<inter> B\<close> by (by100 blast)
        qed
        have hfin_deg: "finite {A \<in> \<A>'. v \<in> top1_arc_endpoints_on A (subspace_topology T' TT' A)}"
          by (rule finite_subset[of _ \<A>']) (simp_all add: assms(5))
        have "{A0, B} \<subseteq> {A \<in> \<A>'. v \<in> top1_arc_endpoints_on A (subspace_topology T' TT' A)}"
          using hA0 hB(1) \<open>v \<in> top1_arc_endpoints_on B _\<close> by (by100 blast)
        from card_mono[OF hfin_deg this]
        have "card {A0, B} \<le> ?deg v" .
        moreover have "card {A0, B} = 2" using hB(2) by (by100 simp)
        ultimately show "?deg v \<ge> 2" by linarith
      qed
      \<comment> \<open>Contradiction: 2E = \\<Sigma>deg \\<ge> 2V = 2(E+1) = 2E + 2.\<close>
      have "2 * card \<A>' \<ge> 2 * card ?V"
      proof -
        have "(\<Sum>v\<in>?V. ?deg v) \<ge> (\<Sum>v\<in>?V. 2)"
          by (rule sum_mono) (use hdeg_ge2 in auto)
        hence "2 * card \<A>' \<ge> 2 * card ?V" using hsum by simp
        thus ?thesis .
      qed
      hence "card \<A>' \<ge> card ?V" by linarith
      hence "card \<A>' \<ge> card \<A>' + 1" using hV_eq by linarith
      show False using \<open>card \<A>' \<ge> card \<A>' + 1\<close> by linarith
    qed
  qed

lemma tree_euler_and_leaf_combined:
  fixes T :: "'a set" and TT :: "'a set set" and \<A> :: "'a set set"
  assumes "top1_is_tree_on T TT"
      and "\<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)"
      and "\<Union>\<A> = T"
      and "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and "finite \<A>" and "\<A> \<noteq> {}"
      and "\<forall>C. C \<subseteq> T \<longrightarrow> (closedin_on T TT C \<longleftrightarrow> (\<forall>A\<in>\<A>. closedin_on A (subspace_topology T TT A) (A \<inter> C)))"
  shows "card (top1_graph_vertex_set T TT \<A>) = card \<A> + 1
    \<and> (card \<A> \<ge> 2 \<longrightarrow> (\<exists>A0 v. A0 \<in> \<A> \<and> v \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)
        \<and> (\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> v \<notin> B)))"
proof -
  \<comment> \<open>Universal leaf existence by walk+pigeonhole (topological bridge; no Euler needed).\<close>
  have hleaf_universal: "\<And>(T' :: 'a set) TT' \<A>'.
    \<lbrakk>top1_is_tree_on T' TT';
     \<forall>A\<in>\<A>'. A \<subseteq> T' \<and> top1_is_arc_on A (subspace_topology T' TT' A);
     \<Union>\<A>' = T';
     \<forall>A\<in>\<A>'. \<forall>B\<in>\<A>'. A \<noteq> B \<longrightarrow>
         A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T' TT' A)
       \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T' TT' B)
       \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2;
     finite \<A>'; card \<A>' \<ge> 2;
     \<forall>C. C \<subseteq> T' \<longrightarrow> (closedin_on T' TT' C \<longleftrightarrow> (\<forall>A\<in>\<A>'. closedin_on A (subspace_topology T' TT' A) (A \<inter> C)))\<rbrakk>
    \<Longrightarrow> \<exists>A0 v. A0 \<in> \<A>' \<and> v \<in> top1_arc_endpoints_on A0 (subspace_topology T' TT' A0)
        \<and> (\<forall>B\<in>\<A>'. B \<noteq> A0 \<longrightarrow> v \<notin> B)"
    by (rule finite_tree_has_leaf)
  \<comment> \<open>OLD PROOF REMOVED: Walk+pigeonhole approach with retract sorrys.
     Replaced by delegation to standalone finite\\_tree\\_has\\_leaf lemma (expert audit4 Step 2).
     The old proof was ~600 lines and contained 5 sorrys (hno\\_bridge, hr\\_const\\_on\\_A,
     orient\\_map continuity, 3-arc retract, general pigeonhole).
     All are now consolidated into the single finite\\_tree\\_has\\_leaf sorry.\<close>

  \<comment> \<open>Euler formula by induction on card \\<A>, using hleaf\\_universal.\<close>
  have heuler: "card (top1_graph_vertex_set T TT \<A>) = card \<A> + 1"
  proof -
    \<comment> \<open>tree\\_euler\\_from\\_leaf[OF hleaf\\_universal] gives the Euler formula for trees
       where leaf existence is guaranteed by hleaf\\_universal.\<close>
    have h: "\<forall>(T' :: 'a set) TT' \<A>'. card \<A>' = card \<A> \<longrightarrow>
        top1_is_tree_on T' TT' \<longrightarrow>
        (\<forall>A\<in>\<A>'. A \<subseteq> T' \<and> top1_is_arc_on A (subspace_topology T' TT' A)) \<longrightarrow>
        \<Union>\<A>' = T' \<longrightarrow>
        (\<forall>A\<in>\<A>'. \<forall>B\<in>\<A>'. A \<noteq> B \<longrightarrow>
             A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T' TT' A)
           \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T' TT' B)
           \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2) \<longrightarrow>
        finite \<A>' \<longrightarrow> \<A>' \<noteq> {} \<longrightarrow>
        (\<forall>C. C \<subseteq> T' \<longrightarrow> (closedin_on T' TT' C \<longleftrightarrow>
            (\<forall>A\<in>\<A>'. closedin_on A (subspace_topology T' TT' A) (A \<inter> C)))) \<longrightarrow>
        card (top1_graph_vertex_set T' TT' \<A>') = card \<A> + 1"
      by (rule tree_euler_from_leaf[OF hleaf_universal])
    from spec[OF spec[OF spec[OF h, of T], of TT], of \<A>]
    show ?thesis using assms by (by5000 simp)
  qed
  \<comment> \<open>Now derive hleaf from heuler using degree\\_sum\\_leaf.\<close>
  have hleaf: "card \<A> \<ge> 2 \<longrightarrow> (\<exists>A0 v. A0 \<in> \<A> \<and>
      v \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0) \<and>
      (\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> v \<notin> B))"
  proof (intro impI)
    assume hge2: "card \<A> \<ge> 2"
    let ?V = "top1_graph_vertex_set T TT \<A>"
    let ?deg = "\<lambda>v. card {A \<in> \<A>. v \<in> top1_arc_endpoints_on A (subspace_topology T TT A)}"
    have hstrict: "is_topology_on_strict T TT"
      using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
    have hhaus: "is_hausdorff_on T TT"
      using assms(1) unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
    have hep_fin: "\<forall>A\<in>\<A>. finite (top1_arc_endpoints_on A (subspace_topology T TT A))"
    proof (intro ballI)
      fix A assume "A \<in> \<A>"
      have "A \<subseteq> T" "top1_is_arc_on A (subspace_topology T TT A)"
        using assms(2) \<open>A \<in> \<A>\<close> by (by100 blast)+
      then obtain h where "top1_homeomorphism_on I_set I_top A (subspace_topology T TT A) h"
        unfolding top1_is_arc_on_def by (by100 blast)
      from arc_endpoints_are_boundary[OF hstrict hhaus \<open>A \<subseteq> T\<close> \<open>top1_is_arc_on A _\<close> this]
      show "finite (top1_arc_endpoints_on A (subspace_topology T TT A))" by (by100 simp)
    qed
    have hV_fin: "finite ?V"
      unfolding top1_graph_vertex_set_def using assms(5) hep_fin by (by100 blast)
    have hep_card: "\<forall>A\<in>\<A>. card (top1_arc_endpoints_on A (subspace_topology T TT A)) = 2"
    proof (intro ballI)
      fix A assume "A \<in> \<A>"
      have "A \<subseteq> T" "top1_is_arc_on A (subspace_topology T TT A)"
        using assms(2) \<open>A \<in> \<A>\<close> by (by100 blast)+
      then obtain h where hh: "top1_homeomorphism_on I_set I_top A (subspace_topology T TT A) h"
        unfolding top1_is_arc_on_def by (by100 blast)
      from arc_endpoints_are_boundary[OF hstrict hhaus \<open>A \<subseteq> T\<close> \<open>top1_is_arc_on A _\<close> hh]
      have "top1_arc_endpoints_on A (subspace_topology T TT A) = {h 0, h 1}" .
      moreover have "h 0 \<noteq> h 1"
      proof
        assume "h 0 = h 1"
        have "inj_on h I_set" using hh unfolding top1_homeomorphism_on_def bij_betw_def
          by (by100 blast)
        from inj_onD[OF this \<open>h 0 = h 1\<close>] show False
          unfolding top1_unit_interval_def by (by100 auto)
      qed
      ultimately show "card (top1_arc_endpoints_on A (subspace_topology T TT A)) = 2"
        by (by100 simp)
    qed
    have hsum: "(\<Sum>v\<in>?V. ?deg v) = 2 * card \<A>"
    proof -
      let ?ep = "\<lambda>A. top1_arc_endpoints_on A (subspace_topology T TT A)"
      have "?V = (\<Union>A\<in>\<A>. ?ep A)" unfolding top1_graph_vertex_set_def by (by100 blast)
      from double_counting_sum[OF assms(5) hep_fin this]
      have "(\<Sum>v\<in>?V. card {A \<in> \<A>. v \<in> ?ep A}) = (\<Sum>A\<in>\<A>. card (?ep A))" .
      also have "\<dots> = (\<Sum>A\<in>\<A>. 2)" using hep_card by simp
      also have "\<dots> = 2 * card \<A>" by simp
      finally show ?thesis .
    qed
    have hdeg_pos: "\<forall>v\<in>?V. ?deg v \<ge> 1"
    proof (intro ballI)
      fix v assume "v \<in> ?V"
      then obtain A0 where "A0 \<in> \<A>" "v \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)"
        unfolding top1_graph_vertex_set_def by (by100 blast)
      hence "{A0} \<subseteq> {A \<in> \<A>. v \<in> top1_arc_endpoints_on A (subspace_topology T TT A)}"
        by (by100 blast)
      moreover have hfin_S: "finite {A \<in> \<A>. v \<in> top1_arc_endpoints_on A (subspace_topology T TT A)}"
        using assms(5) by (by100 simp)
      ultimately have "card {A \<in> \<A>. v \<in> top1_arc_endpoints_on A (subspace_topology T TT A)} \<ge> card {A0}"
        using card_mono[OF hfin_S] by (by100 blast)
      thus "?deg v \<ge> 1" by (by100 simp)
    qed
    have hn_ge1: "card \<A> \<ge> 1" using hge2 by linarith
    from degree_sum_leaf[OF hV_fin heuler hn_ge1 hsum hdeg_pos]
    obtain v where hv_V: "v \<in> ?V" and hv_deg: "?deg v = 1"
      by (by100 blast)
    have hcard1: "card {A \<in> \<A>. v \<in> top1_arc_endpoints_on A (subspace_topology T TT A)} = 1"
      using \<open>?deg v = 1\<close> by simp
    from card_1_singletonE[OF hcard1]
    obtain A0 where hA0_sing: "{A \<in> \<A>. v \<in> top1_arc_endpoints_on A (subspace_topology T TT A)} = {A0}"
      by (by100 blast)
    have hA0: "A0 \<in> \<A>" using hA0_sing by (by100 blast)
    have hv_ep: "v \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)" using hA0_sing by (by100 blast)
    have "\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> v \<notin> B"
    proof (intro ballI impI)
      fix B assume "B \<in> \<A>" "B \<noteq> A0"
      show "v \<notin> B"
      proof
        assume "v \<in> B"
        have "v \<in> A0" using hv_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
        hence "v \<in> A0 \<inter> B" using \<open>v \<in> B\<close> by (by100 blast)
        hence "v \<in> top1_arc_endpoints_on B (subspace_topology T TT B)"
          using assms(4)[rule_format, OF hA0 \<open>B \<in> \<A>\<close> \<open>B \<noteq> A0\<close>[symmetric]] by (by100 blast)
        hence "B \<in> {A0}" using \<open>B \<in> \<A>\<close> hA0_sing by (by100 blast)
        with \<open>B \<noteq> A0\<close> show False by (by100 blast)
      qed
    qed
    show "\<exists>A0 v. A0 \<in> \<A> \<and> v \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0) \<and>
        (\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> v \<notin> B)"
      using hA0 hv_ep \<open>\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> v \<notin> B\<close> by (by5000 blast)
  qed
  show ?thesis using heuler hleaf by (by100 blast)
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
      and "\<forall>C. C \<subseteq> T \<longrightarrow> (closedin_on T TT C \<longleftrightarrow> (\<forall>A\<in>\<A>. closedin_on A (subspace_topology T TT A) (A \<inter> C)))"
  shows "\<exists>A0 v. A0 \<in> \<A> \<and> v \<in> top1_arc_endpoints_on A0 (subspace_topology T TT A0)
      \<and> (\<forall>B\<in>\<A>. B \<noteq> A0 \<longrightarrow> v \<notin> B)"
  \<comment> \<open>Derives from tree\\_euler\\_and\\_leaf\\_combined.\<close>
proof -
  have h\<A>_ne: "\<A> \<noteq> {}" using assms(6) by (by100 force)
  from tree_euler_and_leaf_combined[OF assms(1) assms(2) assms(3) assms(4) assms(5) h\<A>_ne assms(7)]
  show ?thesis using assms(6) by (by100 blast)
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
    (\<forall>C. C \<subseteq> T \<longrightarrow> (closedin_on T TT C \<longleftrightarrow> (\<forall>A\<in>\<A>. closedin_on A (subspace_topology T TT A) (A \<inter> C)))) \<longrightarrow>
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
      and hcoh: "\<forall>C. C \<subseteq> T \<longrightarrow> (closedin_on T TT C \<longleftrightarrow> (\<forall>A\<in>\<A>. closedin_on A (subspace_topology T TT A) (A \<inter> C)))"
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
      from finite_tree_has_leaf_arc[OF htree harcs hcover hinter hfin hcard_ge2 hcoh]
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
      have hremove_result: "top1_is_tree_on ?T' (subspace_topology T TT ?T')
           \<and> (\<forall>C. C \<subseteq> ?T' \<longrightarrow>
               (closedin_on ?T' (subspace_topology T TT ?T') C \<longleftrightarrow>
                (\<forall>A\<in>?\<A>'. closedin_on A (subspace_topology ?T' (subspace_topology T TT ?T') A) (A \<inter> C))))"
        by (rule finite_tree_remove_leaf_is_tree[OF htree harcs hcover hinter hA0 hv_ep hv_uniq hcard_ge2 hfin hcoh])
      have hT'_tree: "top1_is_tree_on ?T' (subspace_topology T TT ?T')"
        using hremove_result by (by100 blast)
      have h\<A>'_coh: "\<forall>C. C \<subseteq> ?T' \<longrightarrow>
          (closedin_on ?T' (subspace_topology T TT ?T') C \<longleftrightarrow>
           (\<forall>A\<in>?\<A>'. closedin_on A (subspace_topology ?T' (subspace_topology T TT ?T') A) (A \<inter> C)))"
        using hremove_result by (by100 blast)
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
        using h\<A>'_card hT'_tree h\<A>'_arcs h\<A>'_cover h\<A>'_inter h\<A>'_fin h\<A>'_ne h\<A>'_coh by (by5000 simp)
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
    (\<forall>C. C \<subseteq> T \<longrightarrow> (closedin_on T TT C \<longleftrightarrow> (\<forall>A\<in>\<A>. closedin_on A (subspace_topology T TT A) (A \<inter> C)))) \<longrightarrow>
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
    "\<forall>C. C \<subseteq> T \<longrightarrow> (closedin_on T TT C \<longleftrightarrow> (\<forall>A\<in>\<A>. closedin_on A (subspace_topology T TT A) (A \<inter> C)))"
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
      and "\<forall>C. C \<subseteq> T \<longrightarrow> (closedin_on T TT C \<longleftrightarrow> (\<forall>A\<in>\<A>. closedin_on A (subspace_topology T TT A) (A \<inter> C)))"
  shows "card (top1_graph_vertex_set T TT \<A>) = card \<A> + 1"
  using tree_euler_and_leaf_combined[OF assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7)]
  by (by100 blast)

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
      have hT_coh: "\<forall>C. C \<subseteq> T \<longrightarrow>
          (closedin_on T (subspace_topology Y TY T) C \<longleftrightarrow>
           (\<forall>A\<in>?\<A>_T. closedin_on A (subspace_topology T (subspace_topology Y TY T) A) (A \<inter> C)))"
      proof -
        have hgraph_Y: "top1_is_graph_on Y TY" using assms(1) .
        have h\<A>_arcs: "\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
          using assms(4) by (by100 blast)
        from subgraph_coherent_topology[OF hgraph_Y h\<A>_arcs assms(5) assms(6) \<A>_coh,
          of "?\<A>_T" T]
        have hraw: "\<forall>C. C \<subseteq> T \<longrightarrow>
            (closedin_on T (subspace_topology Y TY T) C \<longleftrightarrow>
             (\<forall>A\<in>?\<A>_T. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
          using T_coverage by (by5000 blast)
        show ?thesis
        proof (intro allI impI)
          fix C assume "C \<subseteq> T"
          have "\<forall>A\<in>?\<A>_T. subspace_topology T (subspace_topology Y TY T) A = subspace_topology Y TY A"
          proof (intro ballI)
            fix A assume "A \<in> ?\<A>_T"
            hence "A \<subseteq> T" by (by100 blast)
            thus "subspace_topology T (subspace_topology Y TY T) A = subspace_topology Y TY A"
              using subspace_topology_trans[of A T Y TY] by (by100 blast)
          qed
          thus "closedin_on T (subspace_topology Y TY T) C \<longleftrightarrow>
             (\<forall>A\<in>?\<A>_T. closedin_on A (subspace_topology T (subspace_topology Y TY T) A) (A \<inter> C))"
            using hraw[rule_format, OF \<open>C \<subseteq> T\<close>] by simp
        qed
      qed
      from tree_euler_number_one[OF T_tree hT_arcs hT_cover hT_inter hT_fin hT_ne hT_coh]
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
    \<comment> \<open>Clause 1: each lift maps bijectively onto some base arc, preserving endpoints.\<close>
    (\<forall>B\<in>\<A>_E. \<exists>A\<in>\<A>_X. B \<subseteq> {e \<in> E. p e \<in> A} \<and> p ` B = A \<and> inj_on p B
      \<and> p ` (top1_arc_endpoints_on B (subspace_topology E TE B))
        = top1_arc_endpoints_on A (subspace_topology X TX A)) \<and>
    \<comment> \<open>Clause 2: every fiber point over a base arc is in some lift that maps onto the full arc.\<close>
    (\<forall>A\<in>\<A>_X. \<forall>e\<in>{e' \<in> E. p e' \<in> A}. \<exists>B\<in>\<A>_E. e \<in> B \<and> B \<subseteq> {e' \<in> E. p e' \<in> A} \<and> p ` B = A) \<and>
    \<comment> \<open>Clause 3: lifts over the same base arc are pairwise disjoint.\<close>
    (\<forall>A\<in>\<A>_X. \<forall>B1\<in>\<A>_E. \<forall>B2\<in>\<A>_E.
      B1 \<subseteq> {e \<in> E. p e \<in> A} \<and> B2 \<subseteq> {e \<in> E. p e \<in> A} \<and> B1 \<noteq> B2
      \<longrightarrow> B1 \<inter> B2 = {})"

\<comment> \<open>Covering multiplicity for arcs: a k-sheeted covering with lifted arc family
   has exactly k times as many arcs as the base.\<close>
lemma covering_lifted_arc_family_card:
  fixes E :: "'b set" and TE :: "'b set set" and X :: "'a set" and TX :: "'a set set"
  assumes "top1_covering_map_on E TE X TX p"
      and "top1_covering_lifted_arc_family_on E TE X TX p \<A>_X \<A>_E"
      and "finite \<A>_X"
      and "\<forall>x\<in>X. card {e \<in> E. p e = x} = k"
      and "\<forall>A\<in>\<A>_X. A \<subseteq> X \<and> A \<noteq> {}"
      and "k > 0"
  shows "finite \<A>_E \<and> card \<A>_E = k * card \<A>_X"
proof -
  \<comment> \<open>For each base arc A \\<in> \\<A>\\_X, the lifts of A partition {e \\<in> E | p(e) \\<in> A} into
     connected components, one for each point in the fiber of any point of A.
     By the covering property, each component maps homeomorphically onto A,
     so there are exactly k components = k lifted arcs over A.\<close>
  let ?lift = "\<lambda>A. {B \<in> \<A>_E. B \<subseteq> {e \<in> E. p e \<in> A} \<and> p ` B = A}"
  \<comment> \<open>Step 1: Each lifted arc maps onto exactly one base arc (existence + uniqueness).\<close>
  note hdef = assms(2)[unfolded top1_covering_lifted_arc_family_on_def]
  have h_clause1: "\<forall>B\<in>\<A>_E. \<exists>A\<in>\<A>_X. B \<subseteq> {e \<in> E. p e \<in> A} \<and> p ` B = A \<and> inj_on p B
      \<and> p ` (top1_arc_endpoints_on B (subspace_topology E TE B))
        = top1_arc_endpoints_on A (subspace_topology X TX A)"
    using conjunct1[OF hdef] .
  have h_clause2: "\<forall>A\<in>\<A>_X. \<forall>e\<in>{e' \<in> E. p e' \<in> A}. \<exists>B\<in>\<A>_E. e \<in> B \<and> B \<subseteq> {e' \<in> E. p e' \<in> A} \<and> p ` B = A"
    using conjunct1[OF conjunct2[OF hdef]] .
  have h_exists: "\<forall>B\<in>\<A>_E. \<exists>A\<in>\<A>_X. B \<subseteq> {e \<in> E. p e \<in> A} \<and> p ` B = A \<and> inj_on p B
      \<and> p ` (top1_arc_endpoints_on B (subspace_topology E TE B))
        = top1_arc_endpoints_on A (subspace_topology X TX A)"
    using h_clause1 .
  \<comment> \<open>The base arc is uniquely determined: p ` B = A.\<close>
  \<comment> \<open>Step 2: For each base arc, there are exactly k lifted arcs.\<close>
  have h_clause3: "\<forall>A\<in>\<A>_X. \<forall>B1\<in>\<A>_E. \<forall>B2\<in>\<A>_E.
      B1 \<subseteq> {e \<in> E. p e \<in> A} \<and> B2 \<subseteq> {e \<in> E. p e \<in> A} \<and> B1 \<noteq> B2
      \<longrightarrow> B1 \<inter> B2 = {}"
    using conjunct2[OF conjunct2[OF hdef]] .
  have h_k_lifts: "\<forall>A\<in>\<A>_X. card (?lift A) = k"
  proof (intro ballI)
    fix A assume "A \<in> \<A>_X"
    \<comment> \<open>Pick any x \\<in> A (arcs are nonempty). Build bijection ?lift A \\<leftrightarrow> fiber(x).\<close>
    \<comment> \<open>Each B \\<in> ?lift A has p injective on B and p ` B = A \\<ni> x.
       So \\<exists>!e \\<in> B. p(e) = x. This gives the bijection.\<close>
    have hA_ne: "A \<noteq> {}" using assms(5) \<open>A \<in> \<A>_X\<close> by (by100 blast)
    then obtain x where "x \<in> A" by (by100 blast)
    define f where "f = (\<lambda>B. THE e. e \<in> B \<and> p e = x)"
    have huniq: "\<forall>B\<in>?lift A. \<exists>!e. e \<in> B \<and> p e = x"
    proof (intro ballI)
      fix B assume "B \<in> ?lift A"
      hence "B \<in> \<A>_E" "B \<subseteq> {e \<in> E. p e \<in> A}" "p ` B = A" by (by100 blast)+
      from h_clause1[rule_format, OF \<open>B \<in> \<A>_E\<close>]
      obtain A' where "p ` B = A'" "inj_on p B" by (by100 blast)
      have "\<exists>e\<in>B. p e = x" using \<open>p ` B = A\<close> \<open>x \<in> A\<close> by (by100 blast)
      moreover have "\<forall>e1 e2. e1 \<in> B \<and> p e1 = x \<longrightarrow> e2 \<in> B \<and> p e2 = x \<longrightarrow> e1 = e2"
      proof (intro allI impI)
        fix e1 e2 assume "e1 \<in> B \<and> p e1 = x" "e2 \<in> B \<and> p e2 = x"
        from inj_onD[OF \<open>inj_on p B\<close>]
        show "e1 = e2" using \<open>e1 \<in> B \<and> p e1 = x\<close> \<open>e2 \<in> B \<and> p e2 = x\<close> by (by100 blast)
      qed
      ultimately show "\<exists>!e. e \<in> B \<and> p e = x" by (by100 blast)
    qed
    \<comment> \<open>f is a bijection from ?lift A to fiber(x).\<close>
    have hf_bij: "bij_betw f (?lift A) {e \<in> E. p e = x}"
      unfolding bij_betw_def
    proof (intro conjI)
      show "inj_on f (?lift A)"
      proof (rule inj_onI)
        fix B1 B2 assume "B1 \<in> ?lift A" "B2 \<in> ?lift A" "f B1 = f B2"
        have "f B1 \<in> B1" using theI'[OF huniq[rule_format, OF \<open>B1 \<in> ?lift A\<close>]]
            unfolding f_def by (by100 blast)
        have "f B2 \<in> B2" using theI'[OF huniq[rule_format, OF \<open>B2 \<in> ?lift A\<close>]]
            unfolding f_def by (by100 blast)
        have "f B1 \<in> B2" using \<open>f B2 \<in> B2\<close> \<open>f B1 = f B2\<close> by simp
        have "f B1 \<in> B1 \<inter> B2" using \<open>f B1 \<in> B1\<close> \<open>f B1 \<in> B2\<close> by (by100 blast)
        have "B1 \<in> \<A>_E" "B2 \<in> \<A>_E" using \<open>B1 \<in> ?lift A\<close> \<open>B2 \<in> ?lift A\<close> by (by100 blast)+
        have "B1 \<subseteq> {e \<in> E. p e \<in> A}" "B2 \<subseteq> {e \<in> E. p e \<in> A}"
          using \<open>B1 \<in> ?lift A\<close> \<open>B2 \<in> ?lift A\<close> by (by100 blast)+
        from h_clause3[rule_format, OF \<open>A \<in> \<A>_X\<close> \<open>B1 \<in> \<A>_E\<close> \<open>B2 \<in> \<A>_E\<close>]
        show "B1 = B2" using \<open>f B1 \<in> B1 \<inter> B2\<close>
            \<open>B1 \<subseteq> {e \<in> E. p e \<in> A}\<close> \<open>B2 \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 blast)
      qed
      show "f ` (?lift A) = {e \<in> E. p e = x}"
      proof (rule set_eqI, rule iffI)
        fix e assume "e \<in> f ` (?lift A)"
        then obtain B where "B \<in> ?lift A" "e = f B" by (by100 blast)
        have "e \<in> B \<and> p e = x"
          using theI'[OF huniq[rule_format, OF \<open>B \<in> ?lift A\<close>]]
          unfolding f_def \<open>e = f B\<close> by (by100 blast)
        have "B \<subseteq> E" using \<open>B \<in> ?lift A\<close> by (by100 blast)
        thus "e \<in> {e \<in> E. p e = x}" using \<open>e \<in> B \<and> p e = x\<close> \<open>B \<subseteq> E\<close> by (by100 blast)
      next
        fix e assume "e \<in> {e \<in> E. p e = x}"
        hence "e \<in> E" "p e = x" by (by100 blast)+
        hence "e \<in> {e' \<in> E. p e' \<in> A}" using \<open>x \<in> A\<close> by (by100 blast)
        from h_clause2[rule_format, OF \<open>A \<in> \<A>_X\<close> this]
        obtain B where "B \<in> \<A>_E" "e \<in> B" "B \<subseteq> {e' \<in> E. p e' \<in> A}" "p ` B = A"
          by (by100 blast)
        have "B \<in> ?lift A" using \<open>B \<in> \<A>_E\<close> \<open>B \<subseteq> {e' \<in> E. p e' \<in> A}\<close> \<open>p ` B = A\<close>
          by (by100 blast)
        have "e \<in> B \<and> p e = x" using \<open>e \<in> B\<close> \<open>p e = x\<close> by (by100 blast)
        have "f B = e" unfolding f_def
          by (rule the1_equality[OF huniq[rule_format, OF \<open>B \<in> ?lift A\<close>] \<open>e \<in> B \<and> p e = x\<close>])
        thus "e \<in> f ` (?lift A)" using \<open>B \<in> ?lift A\<close> by (by100 blast)
      qed
    qed
    from bij_betw_same_card[OF hf_bij]
    have "card (?lift A) = card {e \<in> E. p e = x}" by simp
    also have "... = k"
    proof -
      have "A \<subseteq> X" using assms(5) \<open>A \<in> \<A>_X\<close> by (by100 blast)
      hence "x \<in> X" using \<open>x \<in> A\<close> by (by100 blast)
      thus ?thesis using assms(4) by (by100 blast)
    qed
    finally show "card (?lift A) = k" .
  qed
  \<comment> \<open>Step 3: The lifts of different base arcs are disjoint (since p`B determines A).\<close>
  have h_disjoint: "\<forall>A1\<in>\<A>_X. \<forall>A2\<in>\<A>_X. A1 \<noteq> A2 \<longrightarrow> ?lift A1 \<inter> ?lift A2 = {}"
  proof (intro ballI impI)
    fix A1 A2 assume "A1 \<in> \<A>_X" "A2 \<in> \<A>_X" "A1 \<noteq> A2"
    show "?lift A1 \<inter> ?lift A2 = {}"
    proof (rule ccontr)
      assume "?lift A1 \<inter> ?lift A2 \<noteq> {}"
      then obtain B where "B \<in> ?lift A1" "B \<in> ?lift A2" by (by100 blast)
      hence "p ` B = A1" "p ` B = A2" by (by100 blast)+
      hence "A1 = A2" by simp
      with \<open>A1 \<noteq> A2\<close> show False by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 4: Every lifted arc is in some base arc's lifts.\<close>
  have h_covers: "\<A>_E = (\<Union>A\<in>\<A>_X. ?lift A)"
  proof (rule set_eqI, rule iffI)
    fix B assume "B \<in> \<A>_E"
    from h_exists[rule_format, OF this]
    obtain A where "A \<in> \<A>_X" "B \<subseteq> {e \<in> E. p e \<in> A}" "p ` B = A" "inj_on p B"
      by (by100 blast)
    thus "B \<in> (\<Union>A\<in>\<A>_X. ?lift A)" using \<open>B \<in> \<A>_E\<close> by (by100 blast)
  next
    fix B assume "B \<in> (\<Union>A\<in>\<A>_X. ?lift A)"
    thus "B \<in> \<A>_E" by (by100 blast)
  qed
  \<comment> \<open>Step 5: Combine to get card(\\<A>\\_E) = k * card(\\<A>\\_X).\<close>
  have h_fin_lifts: "\<forall>A\<in>\<A>_X. finite (?lift A)"
  proof (intro ballI)
    fix A assume "A \<in> \<A>_X"
    have "card (?lift A) = k" using h_k_lifts \<open>A \<in> \<A>_X\<close> by (by100 blast)
    hence "card (?lift A) > 0" using assms(6) by simp
    thus "finite (?lift A)" using card_gt_0_iff by (by100 blast)
  qed
  have "finite \<A>_E"
  proof -
    have "finite (\<Union>A\<in>\<A>_X. ?lift A)"
      using assms(3) h_fin_lifts by (by100 blast)
    thus ?thesis using h_covers by simp
  qed
  moreover have "card \<A>_E = k * card \<A>_X"
  proof -
    have "card \<A>_E = card (\<Union>A\<in>\<A>_X. ?lift A)" using h_covers by simp
    also have "... = (\<Sum>A\<in>\<A>_X. card (?lift A))"
      using card_UN_disjoint[OF assms(3) h_fin_lifts h_disjoint] by simp
    also have "... = (\<Sum>A\<in>\<A>_X. k)" using h_k_lifts by simp
    also have "... = k * card \<A>_X" by simp
    finally show ?thesis .
  qed
  ultimately show ?thesis by (by100 blast)
qed

\<comment> \<open>Covering multiplicity for vertices.\<close>
lemma covering_lifted_vertex_set_card:
  fixes E :: "'b set" and TE :: "'b set set" and X :: "'a set" and TX :: "'a set set"
  assumes "top1_covering_map_on E TE X TX p"
      and "top1_covering_lifted_arc_family_on E TE X TX p \<A>_X \<A>_E"
      and "finite (top1_graph_vertex_set X TX \<A>_X)"
      and "\<forall>x\<in>X. card {e \<in> E. p e = x} = k"
      and "\<forall>A\<in>\<A>_X. A \<subseteq> X \<and> A \<noteq> {}"
      and "k > 0"
  shows "card (top1_graph_vertex_set E TE \<A>_E) = k * card (top1_graph_vertex_set X TX \<A>_X)"
proof -
  let ?V_X = "top1_graph_vertex_set X TX \<A>_X"
  let ?V_E = "top1_graph_vertex_set E TE \<A>_E"
  \<comment> \<open>Step 1: V\\_E = \\<Union>{p\\<inverse>{v} \\<inter> E | v \\<in> V\\_X} (vertex fiber equality).\<close>
  note hdef2 = assms(2)[unfolded top1_covering_lifted_arc_family_on_def]
  have h_clause1v: "\<forall>B\<in>\<A>_E. \<exists>A\<in>\<A>_X. B \<subseteq> {e \<in> E. p e \<in> A} \<and> p ` B = A \<and> inj_on p B
      \<and> p ` (top1_arc_endpoints_on B (subspace_topology E TE B))
        = top1_arc_endpoints_on A (subspace_topology X TX A)"
    using conjunct1[OF hdef2] .
  have h_clause2v: "\<forall>A\<in>\<A>_X. \<forall>e\<in>{e' \<in> E. p e' \<in> A}. \<exists>B\<in>\<A>_E. e \<in> B \<and> B \<subseteq> {e' \<in> E. p e' \<in> A} \<and> p ` B = A"
    using conjunct1[OF conjunct2[OF hdef2]] .
  have hV_eq: "?V_E = (\<Union>v\<in>?V_X. {e \<in> E. p e = v})"
  proof (rule set_eqI, rule iffI)
    fix e assume "e \<in> ?V_E"
    \<comment> \<open>e is an endpoint of some B \\<in> A\\_E. From clause 1: p maps endpoints of B to endpoints of A.\<close>
    then obtain B where "B \<in> \<A>_E"
        "e \<in> top1_arc_endpoints_on B (subspace_topology E TE B)"
      unfolding top1_graph_vertex_set_def by (by100 blast)
    from h_clause1v[rule_format, OF \<open>B \<in> \<A>_E\<close>]
    obtain A where "A \<in> \<A>_X" "B \<subseteq> {e \<in> E. p e \<in> A}" "inj_on p B"
        "p ` (top1_arc_endpoints_on B (subspace_topology E TE B))
          = top1_arc_endpoints_on A (subspace_topology X TX A)"
      by (by5000 blast)
    have "p e \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
      using \<open>e \<in> top1_arc_endpoints_on B _\<close>
          \<open>p ` (top1_arc_endpoints_on B _) = top1_arc_endpoints_on A _\<close>
      by (by100 blast)
    hence "p e \<in> ?V_X" unfolding top1_graph_vertex_set_def using \<open>A \<in> \<A>_X\<close> by (by100 blast)
    have "e \<in> E" using \<open>e \<in> top1_arc_endpoints_on B _\<close> \<open>B \<subseteq> {e \<in> E. p e \<in> A}\<close>
        unfolding top1_arc_endpoints_on_def by (by100 blast)
    thus "e \<in> (\<Union>v\<in>?V_X. {e \<in> E. p e = v})" using \<open>p e \<in> ?V_X\<close> \<open>e \<in> E\<close> by (by100 blast)
  next
    fix e assume "e \<in> (\<Union>v\<in>?V_X. {e \<in> E. p e = v})"
    then obtain v where "v \<in> ?V_X" "e \<in> E" "p e = v" by (by100 blast)
    \<comment> \<open>v is an endpoint of some A \\<in> A\\_X.\<close>
    from \<open>v \<in> ?V_X\<close> obtain A where "A \<in> \<A>_X"
        "v \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
      unfolding top1_graph_vertex_set_def by (by100 blast)
    \<comment> \<open>v \\<in> A (endpoints \\<subseteq> A). e \\<in> fiber(A). From clause 2: e in some lift B.\<close>
    have "v \<in> A" using \<open>v \<in> top1_arc_endpoints_on A _\<close>
        unfolding top1_arc_endpoints_on_def by (by100 blast)
    hence "e \<in> {e' \<in> E. p e' \<in> A}" using \<open>e \<in> E\<close> \<open>p e = v\<close> by (by100 blast)
    from h_clause2v[rule_format, OF \<open>A \<in> \<A>_X\<close> this]
    obtain B where "B \<in> \<A>_E" "e \<in> B" "B \<subseteq> {e' \<in> E. p e' \<in> A}" "p ` B = A" by (by100 blast)
    \<comment> \<open>From clause 1: p|B injective and p maps endpoints(B) to endpoints(A).
       v = p(e) \\<in> endpoints(A) = p ` endpoints(B). So \\<exists>e' \\<in> endpoints(B). p(e') = v = p(e).
       Since e, e' \\<in> B and p injective on B: e = e'. So e \\<in> endpoints(B).\<close>
    from h_clause1v[rule_format, OF \<open>B \<in> \<A>_E\<close>]
    obtain A' where "A' \<in> \<A>_X" "p ` B = A'" "inj_on p B"
        "p ` (top1_arc_endpoints_on B (subspace_topology E TE B))
          = top1_arc_endpoints_on A' (subspace_topology X TX A')"
      by (by5000 blast)
    \<comment> \<open>A' = A (from p ` B = A and p ` B = A').\<close>
    have "A' = A" using \<open>p ` B = A'\<close> \<open>p ` B = A\<close> by simp
    hence "p ` (top1_arc_endpoints_on B (subspace_topology E TE B))
          = top1_arc_endpoints_on A (subspace_topology X TX A)"
      using \<open>p ` (top1_arc_endpoints_on B _) = top1_arc_endpoints_on A' _\<close> by simp
    have "v \<in> p ` (top1_arc_endpoints_on B (subspace_topology E TE B))"
      using \<open>v \<in> top1_arc_endpoints_on A _\<close>
          \<open>p ` (top1_arc_endpoints_on B _) = top1_arc_endpoints_on A _\<close>
      by (by100 blast)
    then obtain e' where "e' \<in> top1_arc_endpoints_on B (subspace_topology E TE B)" "p e' = v"
      by (by100 blast)
    have "e' \<in> B" using \<open>e' \<in> top1_arc_endpoints_on B _\<close>
        unfolding top1_arc_endpoints_on_def by (by100 blast)
    from inj_onD[OF \<open>inj_on p B\<close>] have "e = e'"
      using \<open>e \<in> B\<close> \<open>e' \<in> B\<close> \<open>p e = v\<close> \<open>p e' = v\<close> by (by100 blast)
    hence "e \<in> top1_arc_endpoints_on B (subspace_topology E TE B)"
      using \<open>e' \<in> top1_arc_endpoints_on B _\<close> by simp
    thus "e \<in> ?V_E" unfolding top1_graph_vertex_set_def using \<open>B \<in> \<A>_E\<close> by (by100 blast)
  qed
  \<comment> \<open>Step 2: The fibers are pairwise disjoint.\<close>
  have hV_disj: "\<forall>v1\<in>?V_X. \<forall>v2\<in>?V_X. v1 \<noteq> v2 \<longrightarrow>
      {e \<in> E. p e = v1} \<inter> {e \<in> E. p e = v2} = {}"
    by (by100 blast)
  \<comment> \<open>Step 3: Each fiber has k elements.\<close>
  have hV_X_sub: "?V_X \<subseteq> X"
    unfolding top1_graph_vertex_set_def top1_arc_endpoints_on_def
    using assms(5) by (by100 blast)
  have hV_card: "\<forall>v\<in>?V_X. card {e \<in> E. p e = v} = k"
    using assms(4) hV_X_sub by (by100 blast)
  \<comment> \<open>Step 4: Finite fibers.\<close>
  have hV_fin: "\<forall>v\<in>?V_X. finite {e \<in> E. p e = v}"
  proof (intro ballI)
    fix v assume "v \<in> ?V_X"
    hence "v \<in> X" using hV_X_sub by (by100 blast)
    have "card {e \<in> E. p e = v} = k" using assms(4) \<open>v \<in> X\<close> by (by100 blast)
    hence "card {e \<in> E. p e = v} > 0" using assms(6) by simp
    thus "finite {e \<in> E. p e = v}" using card_gt_0_iff by (by100 blast)
  qed
  \<comment> \<open>Step 5: card(V\\_E) = \\<Sum>v\\<in>V\\_X. k = k * card(V\\_X).\<close>
  have "card ?V_E = card (\<Union>v\<in>?V_X. {e \<in> E. p e = v})" using hV_eq by simp
  also have "... = (\<Sum>v\<in>?V_X. card {e \<in> E. p e = v})"
    using card_UN_disjoint[OF assms(3) hV_fin hV_disj] by simp
  also have "... = (\<Sum>v\<in>?V_X. k)" using hV_card by simp
  also have "... = k * card ?V_X" by simp
  finally show ?thesis .
qed

\<comment> \<open>For the Schreier formula, we need: rank(\\<pi>\\_1(E')) = kn + 1.
   Since E' is a k-fold covering of X (wedge of n+1 circles):
   - \\<pi>\\_1(X) free of rank n+1 (from Theorem 71.3)
   - The covering E' has k times as many arcs and vertices as X
   - So rank(\\<pi>\\_1(E')) = k \\<cdot> arcs(X) - k \\<cdot> vertices(X) + 1 = k(arcs - vertices) + 1
   - arcs(X) - vertices(X) = n (from rank(\\<pi>\\_1(X)) = n+1 = arcs - vertices + 1)
   - Hence rank(\\<pi>\\_1(E')) = kn + 1.\<close>

\<comment> \<open>Finite-sheeted covering of compact space is compact.
   Standard argument: cover X by evenly covered sets, lift finite subcover to E.\<close>
lemma finite_covering_compact:
  assumes "top1_covering_map_on E TE X TX p"
      and "top1_compact_on X TX"
      and "is_topology_on X TX" and "is_topology_on E TE"
      and "\<forall>x\<in>X. card {e \<in> E. p e = x} = k"
      and "k > 0"
  shows "top1_compact_on E TE"
  unfolding top1_compact_on_def
proof (intro conjI allI impI)
  show "is_topology_on E TE" using assms(4) .
next
  fix Uc assume hUc: "Uc \<subseteq> TE \<and> E \<subseteq> \<Union>Uc"
  \<comment> \<open>For each x \\<in> X, get evenly covered nbhd and refine. Use compactness of X.\<close>
  \<comment> \<open>Step 1: For each e \\<in> E, choose Ue \\<in> Uc with e \\<in> Ue.\<close>
  \<comment> \<open>Step 2: For each x \\<in> X, get evenly covered Vx. p\\<inverse>(Vx) = \\<Union>slices.
     Each slice contains one fiber point. That fiber point is in some Ue.
     Intersect Ue with the slice: open in E. Project to X: open nbhd Wx \\<subseteq> Vx of x.\<close>
  \<comment> \<open>Step 3: {Wx | x \\<in> X} covers X. Finite subcover by compactness of X.\<close>
  \<comment> \<open>Step 4: Lift back: finitely many Uc elements cover E.\<close>
  \<comment> \<open>For each e \\<in> E, pick Ue \\<in> Uc with e \\<in> Ue (axiom of choice).\<close>
  have "\<forall>e\<in>E. \<exists>Ue. Ue \<in> Uc \<and> e \<in> Ue" using hUc by (by100 blast)
  from bchoice[OF this]
  obtain g where hg: "\<forall>e\<in>E. g e \<in> Uc \<and> e \<in> g e" by (by100 blast)
  \<comment> \<open>For each x \\<in> X, choose an evenly covered nbhd Vx with slices V1,...,Vk.
     For each slice Vi, pick a fiber point ei (the preimage of x in Vi).
     The open set g(ei) \\<inter> Vi projects to an open subset of Vx containing x.
     The intersection of these k projections gives Wx \\<subseteq> Vx, open, containing x.\<close>
  \<comment> \<open>The cover {Wx | x \\<in> X} of X has a finite subcover (X compact).
     For each xi in the finite subcover, the k open sets g(eij) cover p\\<inverse>(Wxi).
     So finitely many g(eij) cover E.\<close>
  \<comment> \<open>p surjects E onto X.\<close>
  have hp_surj: "p ` E = X"
    using assms(1) unfolding top1_covering_map_on_def by (by100 blast)
  have hp_cont: "top1_continuous_map_on E TE X TX p"
    using assms(1) unfolding top1_covering_map_on_def by (by100 blast)
  \<comment> \<open>For each x \\<in> X, construct open Wx \\<in> TX containing x, such that
     p\\<inverse>(Wx) is covered by finitely many elements of Uc.\<close>
  have hcover_X: "\<forall>x\<in>X. \<exists>Wx\<in>TX. x \<in> Wx \<and> Wx \<subseteq> X \<and>
      (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> {e \<in> E. p e \<in> Wx} \<subseteq> \<Union>F)"
  proof (intro ballI)
    fix x assume "x \<in> X"
    \<comment> \<open>Get evenly covered nbhd Vx.\<close>
    from top1_covering_map_on_evenly_covered[OF assms(1) \<open>x \<in> X\<close>]
    obtain Vx where hVx: "x \<in> Vx" "top1_evenly_covered_on E TE X TX p Vx" by (by100 blast)
    \<comment> \<open>Extract slices.\<close>
    from hVx(2)[unfolded top1_evenly_covered_on_def]
    obtain V where hV_props: "(\<forall>Vi\<in>V. openin_on E TE Vi) \<and>
        (\<forall>Vi\<in>V. \<forall>Vj\<in>V. Vi \<noteq> Vj \<longrightarrow> Vi \<inter> Vj = {}) \<and>
        {e \<in> E. p e \<in> Vx} = \<Union>V \<and>
        (\<forall>Vi\<in>V. top1_homeomorphism_on Vi (subspace_topology E TE Vi)
            Vx (subspace_topology X TX Vx) p)"
        and hVx_open: "openin_on X TX Vx"
      by (by100 auto)
    have hV_open: "\<forall>Vi\<in>V. openin_on E TE Vi" using hV_props by (by100 blast)
    have hV_disj: "\<forall>Vi\<in>V. \<forall>Vj\<in>V. Vi \<noteq> Vj \<longrightarrow> Vi \<inter> Vj = {}" using hV_props by (by100 blast)
    have hV_union: "{e \<in> E. p e \<in> Vx} = \<Union>V" using hV_props by (by100 blast)
    have hV_homeo: "\<forall>Vi\<in>V. top1_homeomorphism_on Vi (subspace_topology E TE Vi)
        Vx (subspace_topology X TX Vx) p" using hV_props by (by100 blast)
    have hVx_sub: "Vx \<subseteq> X" using hVx_open unfolding openin_on_def by (by100 blast)
    have hVx_TX: "Vx \<in> TX" using hVx_open unfolding openin_on_def by (by100 blast)
    \<comment> \<open>V has exactly k slices (from fiber card = k).\<close>
    \<comment> \<open>Each slice Vi contains exactly one preimage of x.\<close>
    have "x \<in> Vx" using hVx(1) .
    have huniq: "\<forall>Vi\<in>V. \<exists>!e. e \<in> Vi \<and> p e = x"
    proof (intro ballI)
      fix Vi assume "Vi \<in> V"
      from hV_homeo[rule_format, OF this]
      have "bij_betw p Vi Vx" unfolding top1_homeomorphism_on_def by (by100 blast)
      from bij_betw_imp_surj_on[OF this]
      have "\<exists>e\<in>Vi. p e = x" using \<open>x \<in> Vx\<close> by (by100 blast)
      moreover have "\<forall>e1 e2. e1 \<in> Vi \<and> p e1 = x \<longrightarrow> e2 \<in> Vi \<and> p e2 = x \<longrightarrow> e1 = e2"
      proof (intro allI impI)
        fix e1 e2 assume "e1 \<in> Vi \<and> p e1 = x" "e2 \<in> Vi \<and> p e2 = x"
        have "inj_on p Vi" using bij_betw_imp_inj_on[OF \<open>bij_betw p Vi Vx\<close>] .
        from inj_onD[OF this]
        show "e1 = e2" using \<open>e1 \<in> Vi \<and> p e1 = x\<close> \<open>e2 \<in> Vi \<and> p e2 = x\<close> by (by100 blast)
      qed
      ultimately show "\<exists>!e. e \<in> Vi \<and> p e = x" by (by100 blast)
    qed
    define f where "f = (\<lambda>Vi. THE e. e \<in> Vi \<and> p e = x)"
    have hbij: "bij_betw f V {e \<in> E. p e = x}"
      unfolding bij_betw_def
    proof (intro conjI)
      show "inj_on f V"
      proof (rule inj_onI)
        fix Vi Vj assume "Vi \<in> V" "Vj \<in> V" "f Vi = f Vj"
        have hfVi: "f Vi \<in> Vi \<and> p (f Vi) = x"
          using theI'[OF huniq[rule_format, OF \<open>Vi \<in> V\<close>]]
          unfolding f_def by (by100 blast)
        have hfVj: "f Vj \<in> Vj \<and> p (f Vj) = x"
          using theI'[OF huniq[rule_format, OF \<open>Vj \<in> V\<close>]]
          unfolding f_def by (by100 blast)
        have "f Vi \<in> Vi" using hfVi by (by100 blast)
        have "f Vj \<in> Vj" using hfVj by (by100 blast)
        have "f Vi \<in> Vj" using \<open>f Vj \<in> Vj\<close> \<open>f Vi = f Vj\<close> by simp
        hence "f Vi \<in> Vi \<inter> Vj" using \<open>f Vi \<in> Vi\<close> by (by100 blast)
        thus "Vi = Vj" using hV_disj \<open>Vi \<in> V\<close> \<open>Vj \<in> V\<close> by (by100 blast)
      qed
      show "f ` V = {e \<in> E. p e = x}"
      proof (rule set_eqI, rule iffI)
        fix e assume "e \<in> f ` V"
        then obtain Vi where "Vi \<in> V" "e = f Vi" by (by100 blast)
        have "e \<in> Vi \<and> p e = x"
          using theI'[OF huniq[rule_format, OF \<open>Vi \<in> V\<close>]]
          unfolding f_def \<open>e = f Vi\<close> by (by100 blast)
        have "Vi \<subseteq> E" using hV_open \<open>Vi \<in> V\<close> unfolding openin_on_def by (by100 blast)
        thus "e \<in> {e \<in> E. p e = x}" using \<open>e \<in> Vi \<and> p e = x\<close> \<open>Vi \<subseteq> E\<close> by (by100 blast)
      next
        fix e assume "e \<in> {e \<in> E. p e = x}"
        hence "e \<in> E" "p e = x" by (by100 blast)+
        have "p e \<in> Vx" using \<open>p e = x\<close> hVx(1) by simp
        hence "e \<in> \<Union>V" using \<open>e \<in> E\<close> hV_union by (by100 blast)
        then obtain Vi where "Vi \<in> V" "e \<in> Vi" by (by100 blast)
        have "e \<in> Vi \<and> p e = x" using \<open>e \<in> Vi\<close> \<open>p e = x\<close> by (by100 blast)
        have "f Vi = e" unfolding f_def
          by (rule the1_equality[OF huniq[rule_format, OF \<open>Vi \<in> V\<close>]
              \<open>e \<in> Vi \<and> p e = x\<close>])
        thus "e \<in> f ` V" using \<open>Vi \<in> V\<close> by (by100 blast)
      qed
    qed
    \<comment> \<open>card V = k: via the bijection f.\<close>
    have hV_card: "card V = k"
    proof -
      have "card {e \<in> E. p e = x} = k" using assms(5) \<open>x \<in> X\<close> by (by100 blast)
      moreover have "card {e \<in> E. p e = x} = card V"
        using bij_betw_same_card[OF hbij] by simp
      ultimately show ?thesis by simp
    qed
    have hV_fin: "finite V"
    proof -
      have "k > 0" using assms(6) .
      hence "card V > 0" using hV_card by simp
      thus ?thesis using card_gt_0_iff by (by100 blast)
    qed
    \<comment> \<open>For each slice Vi, the unique preimage of x is some ei, covered by g(ei).
       Project g(ei) \\<inter> Vi to get an open subset of Vx containing x.\<close>
    \<comment> \<open>Wx = Vx \\<inter> \\<Inter>{p ` (Vi \\<inter> g(ei)) | Vi \\<in> V}: open in X, contains x.\<close>
    \<comment> \<open>p\\<inverse>(Wx) \\<subseteq> \\<Union>{g(ei) | Vi \\<in> V}: finitely many elements of Uc.\<close>
    \<comment> \<open>f(Vi) properties: f Vi \\<in> Vi, p(f Vi) = x, f Vi \\<in> E.\<close>
    have hf_in: "\<forall>Vi\<in>V. f Vi \<in> Vi \<and> p (f Vi) = x"
    proof (intro ballI conjI)
      fix Vi assume "Vi \<in> V"
      from theI'[OF huniq[rule_format, OF \<open>Vi \<in> V\<close>]]
      show "f Vi \<in> Vi" "p (f Vi) = x" unfolding f_def by (by100 blast)+
    qed
    have hf_E: "\<forall>Vi\<in>V. f Vi \<in> E"
    proof (intro ballI)
      fix Vi assume "Vi \<in> V"
      have "Vi \<subseteq> E" using hV_open \<open>Vi \<in> V\<close> unfolding openin_on_def by (by100 blast)
      thus "f Vi \<in> E" using hf_in \<open>Vi \<in> V\<close> by (by100 blast)
    qed
    \<comment> \<open>g(f Vi) \\<in> Uc and f Vi \\<in> g(f Vi).\<close>
    have hgf: "\<forall>Vi\<in>V. g (f Vi) \<in> Uc \<and> f Vi \<in> g (f Vi)"
      using hg hf_E by (by100 blast)
    \<comment> \<open>For each Vi, p ` (Vi \\<inter> g(f Vi)) is open in X and contains x.
       p|Vi: Vi \\<rightarrow> Vx is a homeomorphism, hence an open map.
       Vi \\<inter> g(f Vi) is open in Vi (both open in E). Its image under p is open in Vx.
       Since Vx is open in X, the image is open in X.\<close>
    have hproj_open: "\<forall>Vi\<in>V. p ` (Vi \<inter> g (f Vi)) \<in> TX"
    proof (intro ballI)
      fix Vi assume "Vi \<in> V"
      \<comment> \<open>Vi \\<inter> g(f Vi) is open in the subspace topology of Vi.\<close>
      have "Vi \<in> TE" using hV_open \<open>Vi \<in> V\<close> unfolding openin_on_def by (by100 blast)
      have "g (f Vi) \<in> TE" using hgf hf_E \<open>Vi \<in> V\<close> hUc by (by100 blast)
      have "Vi \<inter> g (f Vi) \<in> subspace_topology E TE Vi"
        unfolding subspace_topology_def using \<open>g (f Vi) \<in> TE\<close> by (by100 blast)
      \<comment> \<open>p|Vi is a homeomorphism Vi \\<rightarrow> Vx. Hence p maps open subsets of Vi to open subsets of Vx.\<close>
      have hhomeo: "top1_homeomorphism_on Vi (subspace_topology E TE Vi)
          Vx (subspace_topology X TX Vx) p"
        using hV_homeo \<open>Vi \<in> V\<close> by (by100 blast)
      \<comment> \<open>The inverse of p|Vi maps open sets in Vx back to open sets in Vi.
         So p maps open sets in Vi to open sets in Vx.\<close>
      have "p ` (Vi \<inter> g (f Vi)) \<in> subspace_topology X TX Vx"
      proof -
        \<comment> \<open>p|Vi open map: from homeomorphism, p maps opens in Vi to opens in Vx.\<close>
        obtain pinv where hpinv:
            "top1_continuous_map_on Vx (subspace_topology X TX Vx)
            Vi (subspace_topology E TE Vi) pinv"
            "bij_betw p Vi Vx"
            "\<forall>e\<in>Vi. pinv (p e) = e" "\<forall>y\<in>Vx. p (pinv y) = y"
          using hhomeo unfolding top1_homeomorphism_on_def
          by (metis bij_betw_def f_inv_into_f inv_into_f_f)
        \<comment> \<open>pinv continuous Vx \\<rightarrow> Vi: preimage of open in Vi under pinv = open in Vx.
           p ` U = pinv\\<inverse>(U) for U \\<subseteq> Vi (since p and pinv are inverses).\<close>
        have "Vi \<inter> g (f Vi) \<subseteq> Vi" by (by100 blast)
        \<comment> \<open>pinv\\<inverse>(Vi \\<inter> g(f Vi)) = {y \\<in> Vx. pinv y \\<in> Vi \\<inter> g(f Vi)}.\<close>
        have "{y \<in> Vx. pinv y \<in> Vi \<inter> g (f Vi)} \<in> subspace_topology X TX Vx"
          using hpinv(1) \<open>Vi \<inter> g (f Vi) \<in> subspace_topology E TE Vi\<close>
          unfolding top1_continuous_map_on_def by (by100 blast)
        moreover have "p ` (Vi \<inter> g (f Vi)) = {y \<in> Vx. pinv y \<in> Vi \<inter> g (f Vi)}"
        proof (rule set_eqI, rule iffI)
          fix y assume "y \<in> p ` (Vi \<inter> g (f Vi))"
          then obtain e where "e \<in> Vi \<inter> g (f Vi)" "y = p e" by (by100 blast)
          have "y \<in> Vx" using \<open>e \<in> Vi \<inter> g (f Vi)\<close> \<open>y = p e\<close>
              bij_betw_apply[OF hpinv(2)] by (by100 blast)
          have "pinv y = e" using hpinv(3) \<open>e \<in> Vi \<inter> g (f Vi)\<close> \<open>y = p e\<close> by (by100 blast)
          thus "y \<in> {y \<in> Vx. pinv y \<in> Vi \<inter> g (f Vi)}"
            using \<open>y \<in> Vx\<close> \<open>e \<in> Vi \<inter> g (f Vi)\<close> by (by100 blast)
        next
          fix y assume "y \<in> {y \<in> Vx. pinv y \<in> Vi \<inter> g (f Vi)}"
          hence "y \<in> Vx" "pinv y \<in> Vi \<inter> g (f Vi)" by (by100 blast)+
          have "p (pinv y) = y" using hpinv(4) \<open>y \<in> Vx\<close> by (by100 blast)
          thus "y \<in> p ` (Vi \<inter> g (f Vi))"
            using \<open>pinv y \<in> Vi \<inter> g (f Vi)\<close> by (by100 force)
        qed
        ultimately show ?thesis by simp
      qed
      \<comment> \<open>Open in Vx (subspace of X) + Vx open in X \\<Rightarrow> open in X.\<close>
      then obtain W where "W \<in> TX" "p ` (Vi \<inter> g (f Vi)) = Vx \<inter> W"
        unfolding subspace_topology_def by (by100 blast)
      have "Vx \<inter> W \<in> TX" by (rule topology_inter_open[OF assms(3) hVx_TX \<open>W \<in> TX\<close>])
      thus "p ` (Vi \<inter> g (f Vi)) \<in> TX" using \<open>p ` (Vi \<inter> g (f Vi)) = Vx \<inter> W\<close> by simp
    qed
    have hproj_x: "\<forall>Vi\<in>V. x \<in> p ` (Vi \<inter> g (f Vi))"
    proof (intro ballI)
      fix Vi assume "Vi \<in> V"
      have "f Vi \<in> Vi \<inter> g (f Vi)" using hf_in hgf \<open>Vi \<in> V\<close> by (by100 blast)
      moreover have "p (f Vi) = x" using hf_in \<open>Vi \<in> V\<close> by (by100 blast)
      ultimately show "x \<in> p ` (Vi \<inter> g (f Vi))" by (by100 blast)
    qed
    \<comment> \<open>Wx = \\<Inter>{p ` (Vi \\<inter> g(f Vi)) | Vi \\<in> V}: finite intersection of open sets containing x.\<close>
    let ?Wx = "\<Inter>Vi\<in>V. p ` (Vi \<inter> g (f Vi))"
    have hWx_open: "?Wx \<in> TX"
    proof -
      have "V \<noteq> {}" using hV_fin hV_card assms(6) by (by100 force)
      let ?S = "(\<lambda>Vi. p ` (Vi \<inter> g (f Vi))) ` V"
      have "finite ?S" using hV_fin by (by100 simp)
      have "?S \<noteq> {}" using \<open>V \<noteq> {}\<close> by (by100 blast)
      have "?S \<subseteq> TX" using hproj_open by (by100 blast)
      \<comment> \<open>is\\_topology\\_on: finite nonempty F \\<subseteq> TX \\<Rightarrow> \\<Inter>F \\<in> TX.\<close>
      from assms(3)[unfolded is_topology_on_def]
      have "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TX \<longrightarrow> \<Inter>F \<in> TX" by (by100 blast)
      hence "\<Inter>?S \<in> TX" using \<open>finite ?S\<close> \<open>?S \<noteq> {}\<close> \<open>?S \<subseteq> TX\<close> by (by100 blast)
      moreover have "\<Inter>?S = ?Wx" by (by100 blast)
      ultimately show ?thesis by simp
    qed
    have hWx_x: "x \<in> ?Wx" using hproj_x by (by100 blast)
    have hWx_sub: "?Wx \<subseteq> X"
    proof -
      have "V \<noteq> {}" using hV_fin hV_card assms(6) by (by100 force)
      then obtain Vi0 where "Vi0 \<in> V" by (by100 blast)
      have "?Wx \<subseteq> p ` (Vi0 \<inter> g (f Vi0))" using \<open>Vi0 \<in> V\<close> by (by100 blast)
      also have "... \<subseteq> p ` Vi0" by (by100 blast)
      also have "... = Vx"
        using hV_homeo[rule_format, OF \<open>Vi0 \<in> V\<close>]
        unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      finally show ?thesis using hVx_sub by (by100 blast)
    qed
    \<comment> \<open>p\\<inverse>(?Wx) covered by {g(f Vi) | Vi \\<in> V}.\<close>
    have hWx_covered: "{e \<in> E. p e \<in> ?Wx} \<subseteq> \<Union>((\<lambda>Vi. g (f Vi)) ` V)"
    proof (intro subsetI)
      fix e assume "e \<in> {e \<in> E. p e \<in> ?Wx}"
      hence he: "e \<in> E" "p e \<in> ?Wx" by (by100 blast)+
      have "p e \<in> Vx"
      proof -
        have "V \<noteq> {}" using hV_fin hV_card assms(6) by (by100 force)
        then obtain Vi0 where "Vi0 \<in> V" by (by100 blast)
        have "p e \<in> p ` (Vi0 \<inter> g (f Vi0))" using he(2) \<open>Vi0 \<in> V\<close> by (by100 blast)
        hence "p e \<in> p ` Vi0" by (by100 blast)
        also have "p ` Vi0 = Vx"
          using hV_homeo[rule_format, OF \<open>Vi0 \<in> V\<close>]
          unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        finally show ?thesis .
      qed
      hence "e \<in> \<Union>V" using he(1) hV_union by (by100 blast)
      then obtain Vj where "Vj \<in> V" "e \<in> Vj" by (by100 blast)
      have "p e \<in> p ` (Vj \<inter> g (f Vj))" using he(2) \<open>Vj \<in> V\<close> by (by100 blast)
      then obtain e' where "e' \<in> Vj \<inter> g (f Vj)" "p e = p e'" by (by100 auto)
      have "inj_on p Vj"
        using hV_homeo[rule_format, OF \<open>Vj \<in> V\<close>]
        unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      from inj_onD[OF this \<open>p e = p e'\<close> \<open>e \<in> Vj\<close>]
      have "e = e'" using \<open>e' \<in> Vj \<inter> g (f Vj)\<close> by (by100 blast)
      hence "e \<in> g (f Vj)" using \<open>e' \<in> Vj \<inter> g (f Vj)\<close> by (by100 blast)
      thus "e \<in> \<Union>((\<lambda>Vi. g (f Vi)) ` V)" using \<open>Vj \<in> V\<close> by (by100 blast)
    qed
    \<comment> \<open>Assemble the result.\<close>
    let ?F = "(\<lambda>Vi. g (f Vi)) ` V"
    show "\<exists>Wx\<in>TX. x \<in> Wx \<and> Wx \<subseteq> X \<and>
        (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> {e \<in> E. p e \<in> Wx} \<subseteq> \<Union>F)"
    proof (rule bexI[of _ ?Wx], intro conjI)
      show "x \<in> ?Wx" using hWx_x .
      show "?Wx \<subseteq> X" using hWx_sub .
      show "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> {e \<in> E. p e \<in> ?Wx} \<subseteq> \<Union>F"
      proof (rule exI[of _ ?F], intro conjI)
        show "finite ?F" using hV_fin by (by100 simp)
        show "?F \<subseteq> Uc" using hgf by (by100 blast)
        show "{e \<in> E. p e \<in> ?Wx} \<subseteq> \<Union>?F" using hWx_covered .
      qed
    next
      show "?Wx \<in> TX" using hWx_open .
    qed
  qed
  \<comment> \<open>Use bchoice to get Wx for each x.\<close>
  have hcover_X': "\<forall>x\<in>X. \<exists>Wx. Wx \<in> TX \<and> x \<in> Wx \<and> Wx \<subseteq> X \<and>
      (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> {e \<in> E. p e \<in> Wx} \<subseteq> \<Union>F)"
  proof (intro ballI)
    fix x assume "x \<in> X"
    from hcover_X[rule_format, OF this]
    obtain Wx where "Wx \<in> TX" "x \<in> Wx" "Wx \<subseteq> X"
        "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> {e \<in> E. p e \<in> Wx} \<subseteq> \<Union>F" by (by100 blast)
    thus "\<exists>Wx. Wx \<in> TX \<and> x \<in> Wx \<and> Wx \<subseteq> X \<and>
        (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> {e \<in> E. p e \<in> Wx} \<subseteq> \<Union>F)" by (by100 blast)
  qed
  from bchoice[OF hcover_X']
  obtain W where hW: "\<forall>x\<in>X. W x \<in> TX \<and> x \<in> W x \<and> W x \<subseteq> X \<and>
      (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> {e \<in> E. p e \<in> W x} \<subseteq> \<Union>F)" by (by100 blast)
  \<comment> \<open>{W x | x \\<in> X} is an open cover of X.\<close>
  have hWcover: "W ` X \<subseteq> TX \<and> X \<subseteq> \<Union>(W ` X)"
  proof (intro conjI)
    show "W ` X \<subseteq> TX" using hW by (by100 blast)
    show "X \<subseteq> \<Union>(W ` X)" using hW by (by100 blast)
  qed
  \<comment> \<open>Compactness: finite subcover.\<close>
  from assms(2)[unfolded top1_compact_on_def, THEN conjunct2, rule_format, of "W ` X"]
  have "\<exists>F0. finite F0 \<and> F0 \<subseteq> W ` X \<and> X \<subseteq> \<Union>F0" using hWcover by (by100 blast)
  then obtain Wfin where hWfin: "finite Wfin" "Wfin \<subseteq> W ` X" "X \<subseteq> \<Union>Wfin"
    by (elim exE conjE) (rule that, assumption+)
  \<comment> \<open>For each W \\<in> Wfin, get finitely many Uc elements covering p\\<inverse>(W).\<close>
  \<comment> \<open>Union of these finite sets covers E.\<close>
  show "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> E \<subseteq> \<Union>F"
  proof -
    have "\<forall>W\<in>Wfin. \<exists>FW. finite FW \<and> FW \<subseteq> Uc \<and> {e \<in> E. p e \<in> W} \<subseteq> \<Union>FW"
    proof (intro ballI)
      fix Ww assume "Ww \<in> Wfin"
      hence "Ww \<in> W ` X" using hWfin(2) by (by100 blast)
      then obtain x where "x \<in> X" "Ww = W x" by (by100 blast)
      thus "\<exists>FW. finite FW \<and> FW \<subseteq> Uc \<and> {e \<in> E. p e \<in> Ww} \<subseteq> \<Union>FW"
        using hW by (by100 blast)
    qed
    from bchoice[OF this]
    obtain h where hh: "\<forall>W\<in>Wfin. finite (h W) \<and> h W \<subseteq> Uc \<and> {e \<in> E. p e \<in> W} \<subseteq> \<Union>(h W)"
      by (by100 blast)
    let ?F = "\<Union>W\<in>Wfin. h W"
    have "finite ?F" using hWfin(1) hh by (by100 blast)
    moreover have "?F \<subseteq> Uc" using hh by (by100 blast)
    moreover have "E \<subseteq> \<Union>?F"
    proof (intro subsetI)
      fix e assume "e \<in> E"
      have "p e \<in> X" using hp_cont \<open>e \<in> E\<close> unfolding top1_continuous_map_on_def by (by100 blast)
      hence "p e \<in> \<Union>Wfin" using hWfin(3) by (by100 blast)
      then obtain W where "W \<in> Wfin" "p e \<in> W" by (by100 blast)
      hence "e \<in> {e \<in> E. p e \<in> W}" using \<open>e \<in> E\<close> by (by100 blast)
      hence "e \<in> \<Union>(h W)" using hh \<open>W \<in> Wfin\<close> by (by100 blast)
      thus "e \<in> \<Union>?F" using \<open>W \<in> Wfin\<close> by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
qed


\<comment> \<open>For a k-fold covering p: E \\<rightarrow> X of a finite connected graph,
   if \\<pi>\\_1(X) is free of rank n+1, then \\<pi>\\_1(E) is free of rank kn+1.
   Proof: lift the arc family of X to E (path components of preimages).
   Each arc lifts to k arcs, each vertex lifts to k vertices.
   Euler: rank = arcs - vertices + 1 = k*arcs\\_X - k*vertices\\_X + 1 = kn + 1.\<close>
lemma covering_graph_pi1_rank:
  assumes hgraph_X: "top1_is_graph_on X TX"
      and hconn_X: "top1_connected_on X TX"
      and hx0: "x0 \<in> X"
      and hcov: "top1_covering_map_on E TE X TX p"
      and hstrict_E: "is_topology_on_strict E TE"
      and hconn_E: "top1_connected_on E TE"
      and he0: "e0 \<in> E" and hpe0: "p e0 = x0"
      and hfiber: "\<forall>x\<in>X. card {e \<in> E. p e = x} = k"
      and hk: "k > 0"
      and hfree_X: "top1_is_free_group_full_on
          (top1_fundamental_group_carrier X TX x0)
          (top1_fundamental_group_mul X TX x0)
          (top1_fundamental_group_id X TX x0)
          (top1_fundamental_group_invg X TX x0)
          \<iota>X SX"
      and hcard_SX: "card SX = n + 1"
      and hfin_SX: "finite SX"
      and hcompact_X: "top1_compact_on X TX"
  shows "\<exists>(\<iota>L :: nat \<Rightarrow> _) (SL :: nat set). top1_is_free_group_full_on
      (top1_fundamental_group_carrier E TE e0)
      (top1_fundamental_group_mul E TE e0)
      (top1_fundamental_group_id E TE e0)
      (top1_fundamental_group_invg E TE e0)
      \<iota>L SL \<and> card SL = k * n + 1"
proof -
  \<comment> \<open>Step 1: Get arc family and tree from graph\\_pi1\\_free\\_weak on X.\<close>
  from graph_pi1_free_weak[OF hgraph_X hconn_X hx0]
  obtain \<iota>w Sw \<A>w Tw
    where hfree_w: "top1_is_free_group_full_on
        (top1_fundamental_group_carrier X TX x0)
        (top1_fundamental_group_mul X TX x0)
        (top1_fundamental_group_id X TX x0)
        (top1_fundamental_group_invg X TX x0)
        \<iota>w Sw"
      and h\<A>w: "\<forall>A\<in>\<A>w. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
      and h\<A>w_cover: "\<Union>\<A>w = X"
      and h\<A>w_inter: "\<forall>A\<in>\<A>w. \<forall>B\<in>\<A>w. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and h\<A>w_coh: "\<forall>C. C \<subseteq> X \<longrightarrow>
           (closedin_on X TX C \<longleftrightarrow>
            (\<forall>A\<in>\<A>w. closedin_on A (subspace_topology X TX A) (A \<inter> C)))"
      and hTw_tree: "top1_is_tree_on Tw (subspace_topology X TX Tw)"
      and hTw_sub: "Tw \<subseteq> X" and hTw_x0: "x0 \<in> Tw"
      and hTw_subgraph: "\<forall>A\<in>\<A>w. A \<subseteq> Tw \<or>
           A \<inter> Tw \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
      and hTw_coverage: "Tw = \<Union>{A \<in> \<A>w. A \<subseteq> Tw}"
      and hNTw_endpoints: "\<forall>A\<in>{A \<in> \<A>w. \<not> A \<subseteq> Tw}.
           \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology X TX A). e \<in> Tw"
      and hSw_eq: "Sw = {A \<in> \<A>w. \<not> A \<subseteq> Tw}"
    by (elim exE conjE)
  \<comment> \<open>card Sw = n+1 by rank invariance with hfree\\_X.\<close>
  have h\<A>w_fin: "finite \<A>w"
    by (rule compact_graph_finite_arcs[OF hgraph_X hcompact_X h\<A>w h\<A>w_cover h\<A>w_inter h\<A>w_coh])
  have hSw_fin: "finite Sw" using hSw_eq h\<A>w_fin by (by100 simp)
  have hSw_card: "card Sw = n + 1"
  proof -
    from free_group_rank_invariant_finite[OF hfree_X hfree_w hfin_SX hSw_fin]
    show ?thesis using hcard_SX by simp
  qed
  \<comment> \<open>Step 2: Construct lifted arc family.
     \\<A>\\_L = \\<Union>{ connected components of p^{-1}(A) \\<inter> E | A \\<in> \\<A>w }.
     This is exactly what Theorem 83.4 constructs internally.\<close>
  \<comment> \<open>Step 2: Construct lifted arc family.
     \\<A>\\_L = path components of p^{-1}(A) for each A \\<in> \\<A>w.
     Book: "the path components of p^{-1}(A) are edges of E, each mapped by p homeomorphically onto A."
     This is exactly what Theorem 83.4 constructs internally.\<close>
  let ?\<A>_L = "\<Union>A\<in>\<A>w. {B. top1_max_conn_comp {e \<in> E. p e \<in> A}
      (subspace_topology E TE {e \<in> E. p e \<in> A}) B}"
  \<comment> \<open>Step 3: \\<A>\\_L satisfies the lifted arc family interface.
     This gives us: card(\\<A>\\_L) = k * card(\\<A>w) and card(V\\_L) = k * card(V\\_X).\<close>
  have hTE: "is_topology_on E TE"
    using hstrict_E unfolding is_topology_on_strict_def by (by100 blast)
  have hTX: "is_topology_on X TX"
    using hgraph_X unfolding top1_is_graph_on_def is_hausdorff_on_def by (by100 blast)
  have hTX_strict: "is_topology_on_strict X TX"
    using hgraph_X unfolding top1_is_graph_on_def by (by100 blast)
  have hX_haus: "is_hausdorff_on X TX"
    using hgraph_X unfolding top1_is_graph_on_def by (by100 blast)
  have hp_cont: "top1_continuous_map_on E TE X TX p"
    using hcov unfolding top1_covering_map_on_def by (by100 blast)
  have hp_surj: "p ` E = X"
    using hcov unfolding top1_covering_map_on_def by (by100 blast)
  \<comment> \<open>Helper: for each A in Aw, restriction p: p^{-1}(A) -> A is a covering (Theorem 53.2).\<close>
  have h_cov_restrict: "\<forall>A\<in>\<A>w. top1_covering_map_on {e \<in> E. p e \<in> A}
      (subspace_topology E TE {e \<in> E. p e \<in> A}) A (subspace_topology X TX A) p"
  proof (intro ballI)
    fix A assume "A \<in> \<A>w"
    have "A \<subseteq> X" using h\<A>w \<open>A \<in> \<A>w\<close> by (by100 blast)
    show "top1_covering_map_on {e \<in> E. p e \<in> A}
        (subspace_topology E TE {e \<in> E. p e \<in> A}) A (subspace_topology X TX A) p"
      by (rule Theorem_53_2[OF hcov hstrict_E hTX_strict \<open>A \<subseteq> X\<close>, of "{e \<in> E. p e \<in> A}"]) (by100 simp)
  qed
  \<comment> \<open>Helper: max conn comps of the same set are disjoint.\<close>
  have h_mcc_disjoint: "\<And>S TS (B1 :: 'b set) B2. \<lbrakk>is_topology_on S TS;
      top1_max_conn_comp S TS B1; top1_max_conn_comp S TS B2; B1 \<noteq> B2\<rbrakk>
      \<Longrightarrow> B1 \<inter> B2 = {}"
  proof -
    fix S :: "'b set" and TS and B1 :: "'b set" and B2
    assume hST: "is_topology_on S TS"
        and hB1: "top1_max_conn_comp S TS B1"
        and hB2: "top1_max_conn_comp S TS B2"
        and hne: "B1 \<noteq> B2"
    show "B1 \<inter> B2 = {}"
    proof (rule ccontr)
      assume "B1 \<inter> B2 \<noteq> {}"
      then obtain e where "e \<in> B1" "e \<in> B2" by (by100 blast)
      have hB1_sub: "B1 \<subseteq> S" using max_conn_comp_sub[OF hB1] .
      have hB2_sub: "B2 \<subseteq> S" using max_conn_comp_sub[OF hB2] .
      have hB1_conn: "top1_connected_on B1 (subspace_topology S TS B1)"
        using hB1 unfolding top1_max_conn_comp_def by (by100 blast)
      have hB2_conn: "top1_connected_on B2 (subspace_topology S TS B2)"
        using hB2 unfolding top1_max_conn_comp_def by (by100 blast)
      have hU_sub: "B1 \<union> B2 \<subseteq> S" using hB1_sub hB2_sub by (by100 blast)
      have hU_conn: "top1_connected_on (B1 \<union> B2) (subspace_topology S TS (B1 \<union> B2))"
      proof -
        define f where "f \<equiv> (\<lambda>b::bool. if b then B1 else B2)"
        have hf_eq: "B1 \<union> B2 = (\<Union>i\<in>{True, False}. f i)"
          unfolding f_def by (by100 auto)
        have h_sub: "\<forall>i\<in>{True, False}. f i \<subseteq> S"
          unfolding f_def using hB1_sub hB2_sub by (by100 auto)
        have h_conn: "\<forall>i\<in>{True, False}. top1_connected_on (f i) (subspace_topology S TS (f i))"
        proof (intro ballI)
          fix i :: bool assume "i \<in> {True, False}"
          show "top1_connected_on (f i) (subspace_topology S TS (f i))"
            unfolding f_def using hB1_conn hB2_conn by (cases i) simp_all
        qed
        have he_inter: "e \<in> \<Inter>(f ` {True, False})"
          unfolding f_def using \<open>e \<in> B1\<close> \<open>e \<in> B2\<close> by (by100 auto)
        have hI_ne: "{True, False} \<noteq> ({}::bool set)" by (by100 blast)
        from Theorem_23_3[OF hST hI_ne h_sub h_conn he_inter]
        have "top1_connected_on (\<Union>(f ` {True, False})) (subspace_topology S TS (\<Union>(f ` {True, False})))" .
        moreover have "\<Union>(f ` {True, False}) = B1 \<union> B2"
          unfolding f_def by (by100 auto)
        ultimately show ?thesis by simp
      qed
      from hB1[unfolded top1_max_conn_comp_def, THEN conjunct2, THEN conjunct2,
          THEN conjunct2, rule_format, OF _ hU_sub hU_conn]
      have "B1 \<union> B2 = B1" by (by100 blast)
      hence "B2 \<subseteq> B1" by (by100 blast)
      from hB2[unfolded top1_max_conn_comp_def, THEN conjunct2, THEN conjunct2,
          THEN conjunct2, rule_format, OF _ hU_sub hU_conn]
      have "B1 \<union> B2 = B2" by (by100 blast)
      hence "B1 \<subseteq> B2" by (by100 blast)
      from \<open>B2 \<subseteq> B1\<close> \<open>B1 \<subseteq> B2\<close> have "B1 = B2" by (by100 blast)
      with hne show False by (by100 blast)
    qed
  qed
  \<comment> \<open>Helper: connected subset sharing a point with a max conn comp is inside the max conn comp.\<close>
  have h_mcc_absorb: "\<And>S TS (C :: 'b set) B0. \<lbrakk>is_topology_on S TS;
      top1_max_conn_comp S TS B0; top1_connected_on C (subspace_topology S TS C);
      C \<subseteq> S; C \<inter> B0 \<noteq> {}\<rbrakk> \<Longrightarrow> C \<subseteq> B0"
  proof -
    fix S :: "'b set" and TS and C :: "'b set" and B0
    assume hST: "is_topology_on S TS"
        and hB0: "top1_max_conn_comp S TS B0"
        and hC_conn: "top1_connected_on C (subspace_topology S TS C)"
        and hC_sub: "C \<subseteq> S" and hC_meet: "C \<inter> B0 \<noteq> {}"
    then obtain e where "e \<in> C" "e \<in> B0" by (by100 blast)
    have hB0_sub: "B0 \<subseteq> S" using max_conn_comp_sub[OF hB0] .
    have hB0_conn: "top1_connected_on B0 (subspace_topology S TS B0)"
      using hB0 unfolding top1_max_conn_comp_def by (by100 blast)
    have hU_sub: "C \<union> B0 \<subseteq> S" using hC_sub hB0_sub by (by100 blast)
    have hU_conn: "top1_connected_on (C \<union> B0) (subspace_topology S TS (C \<union> B0))"
    proof -
      define f where "f \<equiv> (\<lambda>b::bool. if b then C else B0)"
      have hf_eq: "C \<union> B0 = (\<Union>i\<in>{True, False}. f i)" unfolding f_def by (by100 auto)
      have hf_sub: "\<forall>i\<in>{True, False}. f i \<subseteq> S"
        unfolding f_def using hC_sub hB0_sub by (by100 auto)
      have hf_conn: "\<forall>i\<in>{True, False}. top1_connected_on (f i) (subspace_topology S TS (f i))"
      proof (intro ballI)
        fix i :: bool assume "i \<in> {True, False}"
        show "top1_connected_on (f i) (subspace_topology S TS (f i))"
          unfolding f_def using hC_conn hB0_conn by (cases i) simp_all
      qed
      have hf_inter: "e \<in> \<Inter>(f ` {True, False})"
        unfolding f_def using \<open>e \<in> C\<close> \<open>e \<in> B0\<close> by (by100 auto)
      have hI_ne: "{True, False} \<noteq> ({}::bool set)" by (by100 blast)
      from Theorem_23_3[OF hST hI_ne hf_sub hf_conn hf_inter]
      have "top1_connected_on (\<Union>(f ` {True, False}))
          (subspace_topology S TS (\<Union>(f ` {True, False})))" .
      moreover have "\<Union>(f ` {True, False}) = C \<union> B0" unfolding f_def by (by100 auto)
      ultimately show ?thesis by simp
    qed
    from hB0[unfolded top1_max_conn_comp_def, THEN conjunct2, THEN conjunct2,
        THEN conjunct2, rule_format, OF _ hU_sub hU_conn]
    show "C \<subseteq> B0" by (by100 blast)
  qed
  \<comment> \<open>Helper: a max conn comp of preimage(A) surjects onto A via p.
     Proof: p(B) is open in A (covering sheets), closed in A (complement argument),
     nonempty (B \\<ne> {}), A connected \\<Rightarrow> p(B) = A.\<close>
  have h_comp_surj: "\<And>A B. \<lbrakk>A \<in> \<A>w;
      top1_max_conn_comp {e \<in> E. p e \<in> A} (subspace_topology E TE {e \<in> E. p e \<in> A}) B\<rbrakk>
      \<Longrightarrow> p ` B = A"
  proof -
    fix A B
    assume hA_in: "A \<in> \<A>w"
        and hB_comp: "top1_max_conn_comp {e \<in> E. p e \<in> A} (subspace_topology E TE {e \<in> E. p e \<in> A}) B"
    let ?pre = "{e \<in> E. p e \<in> A}"
    have hA_sub: "A \<subseteq> X" using h\<A>w hA_in by (by100 blast)
    have hA_arc: "top1_is_arc_on A (subspace_topology X TX A)" using h\<A>w hA_in by (by100 blast)
    have hTA: "is_topology_on A (subspace_topology X TX A)"
      by (rule subspace_topology_is_topology_on[OF hTX hA_sub])
    have hB_sub: "B \<subseteq> ?pre" using max_conn_comp_sub[OF hB_comp] .
    have hB_ne: "B \<noteq> {}" using max_conn_comp_ne[OF hB_comp] .
    have hpB_sub: "p ` B \<subseteq> A" using hB_sub by (by100 blast)
    have hpB_ne: "p ` B \<noteq> {}" using hB_ne by (by100 blast)
    \<comment> \<open>A is connected (arc is path-connected, hence connected).\<close>
    have hA_conn: "top1_connected_on A (subspace_topology X TX A)"
      by (rule arc_connected[OF hA_arc])
    \<comment> \<open>p(B) is open in A: use covering sheets.\<close>
    have hpB_open: "openin_on A (subspace_topology X TX A) (p ` B)"
    proof -
      have hpre_sub: "?pre \<subseteq> E" by (by100 blast)
      have hpre_top: "is_topology_on ?pre (subspace_topology E TE ?pre)"
        by (rule subspace_topology_is_topology_on[OF hTE hpre_sub])
      have hcov_A: "top1_covering_map_on ?pre (subspace_topology E TE ?pre) A (subspace_topology X TX A) p"
        using h_cov_restrict hA_in by (by100 blast)
      \<comment> \<open>For each a \\<in> p(B), get a covering sheet W at the preimage point in B.\<close>
      have "\<forall>a\<in>p ` B. \<exists>U. U \<in> subspace_topology X TX A \<and> a \<in> U \<and> U \<subseteq> p ` B"
      proof (intro ballI)
        fix a assume "a \<in> p ` B"
        then obtain e where he_B: "e \<in> B" and hpe: "p e = a" by (by100 blast)
        have he_pre: "e \<in> ?pre" using he_B hB_sub by (by100 blast)
        from covering_sheet_over_arc_path_connected[OF hcov_A hA_arc hpre_top hTA he_pre]
        obtain W where hW_sub: "W \<subseteq> ?pre" and hW_open: "openin_on ?pre (subspace_topology E TE ?pre) W"
            and hW_e: "e \<in> W"
            and hW_pc: "top1_path_connected_on W (subspace_topology ?pre (subspace_topology E TE ?pre) W)"
            and hW_homeo: "top1_homeomorphism_on W (subspace_topology ?pre (subspace_topology E TE ?pre) W)
                (p ` W) (subspace_topology A (subspace_topology X TX A) (p ` W)) p"
            and hW_ev: "top1_evenly_covered_on ?pre (subspace_topology E TE ?pre)
                A (subspace_topology X TX A) p (p ` W)"
          by (by100 blast)
        \<comment> \<open>W \\<subseteq> B by maximality of B (W connected, shares point e with B).\<close>
        have hW_sub_B: "W \<subseteq> B"
        proof -
          have hW_conn: "top1_connected_on W (subspace_topology ?pre (subspace_topology E TE ?pre) W)"
            by (rule path_connected_imp_connected[OF hW_pc])
          \<comment> \<open>W \\<union> B connected (share e), W \\<union> B \\<subseteq> preimage(A).\<close>
          have hWB_sub: "W \<union> B \<subseteq> ?pre" using hW_sub hB_sub by (by100 blast)
          have hWB_conn: "top1_connected_on (W \<union> B) (subspace_topology ?pre (subspace_topology E TE ?pre) (W \<union> B))"
          proof -
            define g where "g \<equiv> (\<lambda>b::bool. if b then W else B)"
            have hg_sub: "\<forall>i\<in>{True, False}. g i \<subseteq> ?pre"
              unfolding g_def using hW_sub hB_sub by (by100 auto)
            have hg_conn: "\<forall>i\<in>{True, False}. top1_connected_on (g i)
                (subspace_topology ?pre (subspace_topology E TE ?pre) (g i))"
            proof (intro ballI)
              fix i :: bool assume "i \<in> {True, False}"
              show "top1_connected_on (g i) (subspace_topology ?pre (subspace_topology E TE ?pre) (g i))"
              proof (cases i)
                case True thus ?thesis unfolding g_def using hW_conn by simp
              next
                case False
                have "top1_connected_on B (subspace_topology ?pre (subspace_topology E TE ?pre) B)"
                  using hB_comp unfolding top1_max_conn_comp_def by (by100 blast)
                thus ?thesis unfolding g_def using False by simp
              qed
            qed
            have "e \<in> \<Inter>(g ` {True, False})"
              unfolding g_def using hW_e he_B by (by100 auto)
            have "{True, False} \<noteq> ({}::bool set)" by (by100 blast)
            from Theorem_23_3[OF hpre_top this hg_sub hg_conn \<open>e \<in> \<Inter>(g ` _)\<close>]
            have "top1_connected_on (\<Union>(g ` {True, False}))
                (subspace_topology ?pre (subspace_topology E TE ?pre) (\<Union>(g ` {True, False})))" .
            moreover have "\<Union>(g ` {True, False}) = W \<union> B" unfolding g_def by (by100 auto)
            ultimately show ?thesis by simp
          qed
          from hB_comp[unfolded top1_max_conn_comp_def, THEN conjunct2, THEN conjunct2,
              THEN conjunct2, rule_format, OF _ hWB_sub hWB_conn]
          show ?thesis by (by100 blast)
        qed
        \<comment> \<open>p(W) is open in A (from homeomorphism + W open in preimage).\<close>
        have "p ` W \<in> subspace_topology X TX A"
        proof -
          from top1_evenly_covered_on_openin_on[OF hW_ev]
          have "openin_on A (subspace_topology X TX A) (p ` W)" .
          thus ?thesis unfolding openin_on_def by (by100 blast)
        qed
        have "a \<in> p ` W" using hpe hW_e by (by100 blast)
        have "p ` W \<subseteq> p ` B" using hW_sub_B by (by100 blast)
        thus "\<exists>U. U \<in> subspace_topology X TX A \<and> a \<in> U \<and> U \<subseteq> p ` B"
          using \<open>p ` W \<in> subspace_topology X TX A\<close> \<open>a \<in> p ` W\<close> \<open>p ` W \<subseteq> p ` B\<close> by (by100 blast)
      qed
      \<comment> \<open>p(B) = union of open sets (the U's), hence open.\<close>
      have "p ` B = \<Union>{U. U \<in> subspace_topology X TX A \<and> U \<subseteq> p ` B}"
      proof (rule set_eqI, rule iffI)
        fix a assume "a \<in> p ` B"
        with \<open>\<forall>a\<in>p ` B. _\<close> obtain U where "U \<in> subspace_topology X TX A" "a \<in> U" "U \<subseteq> p ` B"
          by (by100 blast)
        thus "a \<in> \<Union>{U. U \<in> subspace_topology X TX A \<and> U \<subseteq> p ` B}" by (by100 blast)
      next
        fix a assume "a \<in> \<Union>{U. U \<in> subspace_topology X TX A \<and> U \<subseteq> p ` B}"
        thus "a \<in> p ` B" by (by100 blast)
      qed
      moreover have "\<Union>{U. U \<in> subspace_topology X TX A \<and> U \<subseteq> p ` B} \<in> subspace_topology X TX A"
      proof -
        have hsub_TA: "{U. U \<in> subspace_topology X TX A \<and> U \<subseteq> p ` B} \<subseteq> subspace_topology X TX A"
          by (by100 blast)
        have "\<forall>U\<subseteq>subspace_topology X TX A. \<Union>U \<in> subspace_topology X TX A"
          using hTA unfolding is_topology_on_def by (by100 blast)
        thus ?thesis using hsub_TA by (by100 blast)
      qed
      ultimately have "p ` B \<in> subspace_topology X TX A" by simp
      thus ?thesis unfolding openin_on_def using hpB_sub by (by100 blast)
    qed
    \<comment> \<open>p(B) is closed in A: A \\ p(B) is open.\<close>
    \<comment> \<open>p(B) closed = complement open. A \\ p(B) = union of p-images of other components.\<close>
    have hpB_closed: "closedin_on A (subspace_topology X TX A) (p ` B)"
    proof -
      \<comment> \<open>Show A \\ p(B) is open. For a \\<in> A \\ p(B): a has a preimage in some other component C.
         The covering sheet at that preimage maps to open p(W') \\<subseteq> A \\ p(B).
         So A \\ p(B) is open, hence p(B) is closed.\<close>
      have "openin_on A (subspace_topology X TX A) (A - p ` B)"
      proof -
        have "\<forall>a\<in>A - p ` B. \<exists>U. U \<in> subspace_topology X TX A \<and> a \<in> U \<and> U \<subseteq> A - p ` B"
        proof (intro ballI)
          fix a assume ha: "a \<in> A - p ` B"
          hence "a \<in> A" "a \<notin> p ` B" by (by100 blast)+
          \<comment> \<open>a \\<in> A \\<subseteq> X = p(E), so \\<exists>e' \\<in> E with p(e') = a. e' \\<in> preimage(A).\<close>
          have "a \<in> X" using \<open>a \<in> A\<close> hA_sub by (by100 blast)
          have "a \<in> p ` E" using hp_surj \<open>a \<in> X\<close> by simp
          then obtain e' where "e' \<in> E" "p e' = a" by (by100 blast)
          have "e' \<in> ?pre" using \<open>e' \<in> E\<close> \<open>p e' = a\<close> \<open>a \<in> A\<close> by (by100 blast)
          \<comment> \<open>e' \\<notin> B (since a = p(e') \\<notin> p(B)).\<close>
          have "e' \<notin> B" using \<open>p e' = a\<close> \<open>a \<notin> p ` B\<close> by (by100 blast)
          \<comment> \<open>Get covering sheet at e'.\<close>
          have hcov_A: "top1_covering_map_on ?pre (subspace_topology E TE ?pre) A (subspace_topology X TX A) p"
            using h_cov_restrict hA_in by (by100 blast)
          have hpre_sub: "?pre \<subseteq> E" by (by100 blast)
          have hpre_top: "is_topology_on ?pre (subspace_topology E TE ?pre)"
            by (rule subspace_topology_is_topology_on[OF hTE hpre_sub])
          from covering_sheet_over_arc_path_connected[OF hcov_A hA_arc hpre_top hTA \<open>e' \<in> ?pre\<close>]
          obtain W' where hW'_sub: "W' \<subseteq> ?pre"
              and hW'_e: "e' \<in> W'"
              and hW'_pc: "top1_path_connected_on W' (subspace_topology ?pre (subspace_topology E TE ?pre) W')"
              and hW'_homeo: "top1_homeomorphism_on W' (subspace_topology ?pre (subspace_topology E TE ?pre) W')
                  (p ` W') (subspace_topology A (subspace_topology X TX A) (p ` W')) p"
              and hW'_ev: "top1_evenly_covered_on ?pre (subspace_topology E TE ?pre) A (subspace_topology X TX A) p (p ` W')"
            by (by100 blast)
          \<comment> \<open>p(W') is open in A.\<close>
          have "openin_on A (subspace_topology X TX A) (p ` W')"
            using top1_evenly_covered_on_openin_on[OF hW'_ev] .
          hence "p ` W' \<in> subspace_topology X TX A"
            unfolding openin_on_def by (by100 blast)
          \<comment> \<open>W' \\<subseteq> some max conn comp C of preimage(A). C \\<ne> B (since e' \\<in> W' \\<subseteq> C, e' \\<notin> B).\<close>
          \<comment> \<open>p(W') \\<inter> p(B) = {} because W' \\<subseteq> C, C \\<inter> B = {} (disjoint components).\<close>
          \<comment> \<open>So p(W') \\<subseteq> A \\ p(B).\<close>
          \<comment> \<open>Key: p(W') \\<inter> p(B) = {}. Proof via evenly covered sheets:
             If z \\<in> p(W') \\<inter> p(B), get b \\<in> B with p(b)=z. b is in some sheet Vb over p(W').
             Vb is connected, meets B (at b), so Vb \\<subseteq> B (maximality). p(Vb) = p(W') (homeo).
             So a \\<in> p(W') = p(Vb) \\<subseteq> p(B), contradicting a \\<notin> p(B).\<close>
          have "p ` W' \<inter> p ` B = {}"
          proof (rule ccontr)
            assume "p ` W' \<inter> p ` B \<noteq> {}"
            then obtain z where "z \<in> p ` W'" "z \<in> p ` B" by (by100 blast)
            from \<open>z \<in> p ` B\<close> obtain b where "b \<in> B" "p b = z" by (by100 blast)
            have "b \<in> ?pre" using \<open>b \<in> B\<close> hB_sub by (by100 blast)
            have "p b \<in> p ` W'" using \<open>p b = z\<close> \<open>z \<in> p ` W'\<close> by simp
            hence "b \<in> {e \<in> ?pre. p e \<in> p ` W'}" using \<open>b \<in> ?pre\<close> by (by100 blast)
            \<comment> \<open>From evenly covered: get sheets over p(W'). b is in some sheet Vb.\<close>
            from hW'_ev[unfolded top1_evenly_covered_on_def]
            obtain \<V>' where
                hV'_open: "\<forall>V\<in>\<V>'. openin_on ?pre (subspace_topology E TE ?pre) V"
                and hV'_disj: "\<forall>V\<in>\<V>'. \<forall>V'\<in>\<V>'. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
                and hV'_union: "{e \<in> ?pre. p e \<in> p ` W'} = \<Union>\<V>'"
                and hV'_homeo: "\<forall>V\<in>\<V>'. top1_homeomorphism_on V
                    (subspace_topology ?pre (subspace_topology E TE ?pre) V)
                    (p ` W') (subspace_topology A (subspace_topology X TX A) (p ` W')) p"
              by (elim conjE exE) (rule that, assumption+)
            from hV'_union have "b \<in> \<Union>\<V>'" using \<open>b \<in> {e \<in> ?pre. p e \<in> p ` W'}\<close> by simp
            then obtain Vb where "Vb \<in> \<V>'" "b \<in> Vb" by (by100 blast)
            \<comment> \<open>Vb is connected (path-connected from homeomorphism).\<close>
            \<comment> \<open>Vb meets B (at b). Vb \\<subseteq> preimage(A) (from sheet structure).\<close>
            \<comment> \<open>By maximality of B: Vb \\<subseteq> B.\<close>
            \<comment> \<open>Then p(Vb) = p(W') (homeomorphism). So p(W') \\<subseteq> p(B).\<close>
            \<comment> \<open>a \\<in> p(W') \\<subseteq> p(B), contradicting a \\<notin> p(B).\<close>
            have "Vb \<subseteq> ?pre" using hV'_union \<open>Vb \<in> \<V>'\<close> by (by100 blast)
            have hVb_homeo: "top1_homeomorphism_on Vb
                (subspace_topology ?pre (subspace_topology E TE ?pre) Vb)
                (p ` W') (subspace_topology A (subspace_topology X TX A) (p ` W')) p"
              using hV'_homeo \<open>Vb \<in> \<V>'\<close> by (by100 blast)
            have "p ` Vb = p ` W'"
              using hVb_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
            \<comment> \<open>Vb \\<subseteq> B: Vb connected (homeo to p(W') which is connected), meets B at b.\<close>
            have hVb_sub_B: "Vb \<subseteq> B"
            proof -
              have hVb_conn: "top1_connected_on Vb (subspace_topology ?pre (subspace_topology E TE ?pre) Vb)"
              proof -
                \<comment> \<open>p(W') is path-connected (from W' PC + homeomorphism W' \\<rightarrow> p(W')).\<close>
                have hpW'_pc: "top1_path_connected_on (p ` W')
                    (subspace_topology A (subspace_topology X TX A) (p ` W'))"
                  by (rule homeomorphism_preserves_path_connected[OF hW'_homeo hW'_pc])
                \<comment> \<open>Inverse of hVb\\_homeo: p(W') \\<rightarrow> Vb is a homeomorphism.\<close>
                have hinv_Vb: "top1_homeomorphism_on (p ` W')
                    (subspace_topology A (subspace_topology X TX A) (p ` W'))
                    Vb (subspace_topology ?pre (subspace_topology E TE ?pre) Vb)
                    (inv_into Vb p)"
                  by (rule homeomorphism_inverse[OF hVb_homeo])
                \<comment> \<open>Vb is path-connected (from inverse homeomorphism + p(W') PC).\<close>
                have "top1_path_connected_on Vb
                    (subspace_topology ?pre (subspace_topology E TE ?pre) Vb)"
                  by (rule homeomorphism_preserves_path_connected[OF hinv_Vb hpW'_pc])
                thus ?thesis by (rule path_connected_imp_connected)
              qed
              have "Vb \<inter> B \<noteq> {}" using \<open>b \<in> Vb\<close> \<open>b \<in> B\<close> by (by100 blast)
              from h_mcc_absorb[OF hpre_top hB_comp hVb_conn \<open>Vb \<subseteq> ?pre\<close> this]
              show ?thesis .
            qed
            have "p ` W' \<subseteq> p ` B"
              using \<open>p ` Vb = p ` W'\<close> hVb_sub_B by (by100 blast)
            have "a \<in> p ` W'" using \<open>p e' = a\<close> hW'_e by (by100 blast)
            hence "a \<in> p ` B" using \<open>p ` W' \<subseteq> p ` B\<close> by (by100 blast)
            thus False using \<open>a \<notin> p ` B\<close> by (by100 blast)
          qed
          hence "p ` W' \<subseteq> A - p ` B" using hW'_sub by (by100 blast)
          have "a \<in> p ` W'" using \<open>p e' = a\<close> hW'_e by (by100 blast)
          thus "\<exists>U. U \<in> subspace_topology X TX A \<and> a \<in> U \<and> U \<subseteq> A - p ` B"
            using \<open>p ` W' \<in> subspace_topology X TX A\<close> \<open>a \<in> p ` W'\<close> \<open>p ` W' \<subseteq> A - p ` B\<close>
            by (by100 blast)
        qed
        \<comment> \<open>A \\ p(B) = union of open sets, hence open.\<close>
        have "A - p ` B = \<Union>{U. U \<in> subspace_topology X TX A \<and> U \<subseteq> A - p ` B}"
        proof (rule set_eqI, rule iffI)
          fix a assume ha: "a \<in> A - p ` B"
          from \<open>\<forall>a\<in>A - p ` B. _\<close>[rule_format, OF ha]
          obtain U where "U \<in> subspace_topology X TX A" "a \<in> U" "U \<subseteq> A - p ` B"
            by (by100 blast)
          thus "a \<in> \<Union>{U. U \<in> subspace_topology X TX A \<and> U \<subseteq> A - p ` B}" by (by100 blast)
        next
          fix a assume "a \<in> \<Union>{U. U \<in> subspace_topology X TX A \<and> U \<subseteq> A - p ` B}"
          thus "a \<in> A - p ` B" by (by100 blast)
        qed
        moreover have "\<Union>{U. U \<in> subspace_topology X TX A \<and> U \<subseteq> A - p ` B} \<in> subspace_topology X TX A"
        proof -
          have "{U. U \<in> subspace_topology X TX A \<and> U \<subseteq> A - p ` B} \<subseteq> subspace_topology X TX A"
            by (by100 blast)
          have "\<forall>U\<subseteq>subspace_topology X TX A. \<Union>U \<in> subspace_topology X TX A"
            using hTA unfolding is_topology_on_def by (by100 blast)
          thus ?thesis
            using \<open>{U. U \<in> subspace_topology X TX A \<and> U \<subseteq> A - p ` B} \<subseteq> subspace_topology X TX A\<close>
            by (by100 blast)
        qed
        ultimately have "A - p ` B \<in> subspace_topology X TX A" by simp
        thus ?thesis unfolding openin_on_def by (by100 blast)
      qed
      have "A - p ` B \<in> subspace_topology X TX A"
        using \<open>openin_on A (subspace_topology X TX A) (A - p ` B)\<close>
        unfolding openin_on_def by (by100 blast)
      thus ?thesis unfolding closedin_on_def using hpB_sub by (by100 blast)
    qed
    \<comment> \<open>Connected + open + closed + nonempty \\<Rightarrow> p(B) = A.\<close>
    have hA_strict: "is_topology_on_strict A (subspace_topology X TX A)"
      by (rule subspace_topology_is_strict[OF hTX_strict hA_sub])
    from connected_iff_clopen_openin_on[OF hA_strict, THEN iffD1, OF hA_conn,
        THEN conjunct2, rule_format, OF conjI[OF hpB_open hpB_closed]]
    have "p ` B = {} \<or> p ` B = A" by (by100 blast)
    thus "p ` B = A" using hpB_ne by (by100 blast)
  qed
  have h_lifted: "top1_covering_lifted_arc_family_on E TE X TX p \<A>w ?\<A>_L"
    unfolding top1_covering_lifted_arc_family_on_def
  proof (intro conjI)
    \<comment> \<open>Clause 1: each lift maps bijectively onto some base arc with endpoint preservation.\<close>
    show "\<forall>B\<in>?\<A>_L. \<exists>A\<in>\<A>w. B \<subseteq> {e \<in> E. p e \<in> A} \<and> p ` B = A \<and> inj_on p B
        \<and> p ` (top1_arc_endpoints_on B (subspace_topology E TE B))
          = top1_arc_endpoints_on A (subspace_topology X TX A)"
    proof (intro ballI)
      fix B assume "B \<in> ?\<A>_L"
      then obtain A0 where hA0: "A0 \<in> \<A>w"
          and hB_comp0: "top1_max_conn_comp {e \<in> E. p e \<in> A0}
              (subspace_topology E TE {e \<in> E. p e \<in> A0}) B"
        by (by100 blast)
      have hB_sub0: "B \<subseteq> {e \<in> E. p e \<in> A0}" using max_conn_comp_sub[OF hB_comp0] .
      have hpB_eq: "p ` B = A0" by (rule h_comp_surj[OF hA0 hB_comp0])
      \<comment> \<open>Injectivity: Theorem 54.3 + A0 simply connected.\<close>
      \<comment> \<open>Setup for injectivity proof (following AlgTopCached5 Theorem\\_83\\_4 lines 994-1084).\<close>
      let ?pre0 = "{e \<in> E. p e \<in> A0}"
      have hpre0_sub: "?pre0 \<subseteq> E" by (by100 blast)
      have hpre0_top: "is_topology_on ?pre0 (subspace_topology E TE ?pre0)"
        by (rule subspace_topology_is_topology_on[OF hTE hpre0_sub])
      have hA0_sub: "A0 \<subseteq> X" using h\<A>w hA0 by (by100 blast)
      have hA0_arc: "top1_is_arc_on A0 (subspace_topology X TX A0)" using h\<A>w hA0 by (by100 blast)
      have hTA0: "is_topology_on A0 (subspace_topology X TX A0)"
        by (rule subspace_topology_is_topology_on[OF hTX hA0_sub])
      have hcov_A0: "top1_covering_map_on ?pre0 (subspace_topology E TE ?pre0)
          A0 (subspace_topology X TX A0) p"
        using h_cov_restrict hA0 by (by100 blast)
      \<comment> \<open>B is path-connected (from covering\\_component\\_over\\_arc\\_path\\_connected).\<close>
      have hB_pc: "top1_path_connected_on B (subspace_topology E TE B)"
      proof -
        from covering_component_over_arc_path_connected[OF hcov_A0 hA0_arc hpre0_top hTA0 hB_comp0]
        have "top1_path_connected_on B (subspace_topology ?pre0 (subspace_topology E TE ?pre0) B)" .
        moreover have "subspace_topology ?pre0 (subspace_topology E TE ?pre0) B = subspace_topology E TE B"
          by (rule subspace_topology_trans[OF hB_sub0])
        ultimately show ?thesis by simp
      qed
      \<comment> \<open>A0 is simply connected (arc is SC).\<close>
      have hA0_sc: "top1_simply_connected_on A0 (subspace_topology X TX A0)"
      proof -
        \<comment> \<open>Get homeomorphism h\\_arc: [0,1] \\<rightarrow> A0.\<close>
        obtain h_arc where hh_arc: "top1_homeomorphism_on top1_unit_interval
            top1_unit_interval_topology A0 (subspace_topology X TX A0) h_arc"
          using hA0_arc unfolding top1_is_arc_on_def by (by100 blast)
        \<comment> \<open>Get endpoint.\<close>
        have hep_ne: "top1_arc_endpoints_on A0 (subspace_topology X TX A0) \<noteq> {}"
        proof -
          from arc_endpoints_are_boundary[OF hTX_strict hX_haus hA0_sub hA0_arc hh_arc]
          show ?thesis by (by100 blast)
        qed
        then obtain ep where hep: "ep \<in> top1_arc_endpoints_on A0 (subspace_topology X TX A0)"
          by (by100 blast)
        \<comment> \<open>DR to endpoint.\<close>
        have hA0_dr: "top1_deformation_retract_of_on A0 (subspace_topology X TX A0) {ep}"
          by (rule arc_deformation_retract_to_endpoint[OF hA0_arc hep])
        \<comment> \<open>Arc path-connected: [0,1] is PC, homeomorphism preserves PC.\<close>
        have hA0_pc: "top1_path_connected_on A0 (subspace_topology X TX A0)"
        proof -
          have hI_pc: "top1_path_connected_on top1_unit_interval top1_unit_interval_topology"
            unfolding top1_path_connected_on_def
          proof (intro conjI ballI)
            show "is_topology_on top1_unit_interval top1_unit_interval_topology"
              by (rule top1_unit_interval_topology_is_topology_on)
          next
            fix x y assume hx: "x \<in> top1_unit_interval" and hy: "y \<in> top1_unit_interval"
            let ?f = "\<lambda>t::real. (1 - t) * x + t * y"
            have hf_range: "\<forall>t\<in>top1_unit_interval. ?f t \<in> top1_unit_interval"
            proof (intro ballI)
              fix t assume "t \<in> top1_unit_interval"
              hence "0 \<le> t" "t \<le> 1" using hx hy
                unfolding top1_unit_interval_def by (by100 auto)+
              have "0 \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1"
                using hx hy unfolding top1_unit_interval_def by (by100 auto)+
              have "0 \<le> (1-t)*x + t*y"
                using \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> \<open>0 \<le> x\<close> \<open>0 \<le> y\<close>
                by (intro add_nonneg_nonneg mult_nonneg_nonneg) linarith+
              moreover have "(1-t)*x + t*y \<le> 1"
              proof -
                have "(1-t)*x \<le> (1-t)*1" using \<open>x \<le> 1\<close> \<open>t \<le> 1\<close>
                  by (intro mult_left_mono) linarith+
                moreover have "t*y \<le> t*1" using \<open>y \<le> 1\<close> \<open>0 \<le> t\<close>
                  by (intro mult_left_mono) linarith+
                moreover have "(1-t)*1 + t*1 = (1::real)" by (by100 simp)
                ultimately show ?thesis by linarith
              qed
              ultimately show "?f t \<in> top1_unit_interval"
                unfolding top1_unit_interval_def by (by100 auto)
            qed
            have hf_cont: "continuous_on top1_unit_interval ?f"
              by (intro continuous_intros)
            from top1_continuous_map_on_subspace_open_sets_on[OF _ hf_cont] hf_range
            have "top1_continuous_map_on top1_unit_interval
                (subspace_topology UNIV top1_open_sets top1_unit_interval)
                top1_unit_interval
                (subspace_topology UNIV top1_open_sets top1_unit_interval) ?f"
              by (by100 blast)
            hence hf_top: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                top1_unit_interval top1_unit_interval_topology ?f"
              unfolding top1_unit_interval_topology_def by (by100 simp)
            have "?f 0 = x" by (by100 simp)
            moreover have "?f 1 = y" by (by100 simp)
            ultimately show "\<exists>f. top1_is_path_on top1_unit_interval top1_unit_interval_topology x y f"
              unfolding top1_is_path_on_def using hf_top by (by100 blast)
          qed
          from homeomorphism_preserves_path_connected[OF hh_arc hI_pc]
          show ?thesis .
        qed
        have "ep \<in> A0" using hep unfolding top1_arc_endpoints_on_def by (by100 blast)
        from deformation_retract_to_singleton_imp_simply_connected[OF hTA0 \<open>ep \<in> A0\<close> hA0_pc hA0_dr]
        show ?thesis .
      qed
      have hB_inj: "inj_on p B"
      proof (intro inj_onI)
        fix e1 e2 assume he1: "e1 \<in> B" and he2: "e2 \<in> B" and hpeq12: "p e1 = p e2"
        let ?a0 = "p e1"
        \<comment> \<open>Get path \\<gamma> from e1 to e2 in B (path-connected).\<close>
        from hB_pc[unfolded top1_path_connected_on_def]
        have "\<exists>f. top1_is_path_on B (subspace_topology E TE B) e1 e2 f"
          using he1 he2 by (by100 blast)
        then obtain \<gamma> where h\<gamma>: "top1_is_path_on B (subspace_topology E TE B) e1 e2 \<gamma>"
          by (by100 blast)
        \<comment> \<open>Lift \\<gamma> to preimage(A0).\<close>
        have h\<gamma>_pre: "top1_is_path_on ?pre0 (subspace_topology E TE ?pre0) e1 e2 \<gamma>"
        proof -
          have h\<gamma>_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              B (subspace_topology E TE B) \<gamma>"
            using h\<gamma> unfolding top1_is_path_on_def by (by5000 blast)
          from top1_continuous_map_on_codomain_enlarge[OF h\<gamma>_cont hB_sub0 hpre0_sub]
          have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              ?pre0 (subspace_topology E TE ?pre0) \<gamma>" .
          moreover have "\<gamma> 0 = e1" "\<gamma> 1 = e2"
            using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)+
          ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
        qed
        \<comment> \<open>p \\<circ> \\<gamma> is a loop at ?a0 in A0.\<close>
        have hp_cont_pre: "top1_continuous_map_on ?pre0 (subspace_topology E TE ?pre0)
            A0 (subspace_topology X TX A0) p"
        proof -
          have hp_cont_E: "top1_continuous_map_on E TE X TX p"
            using hcov unfolding top1_covering_map_on_def by (by100 blast)
          have "top1_continuous_map_on ?pre0 (subspace_topology E TE ?pre0) X TX p"
            by (rule top1_continuous_map_on_subspace_restrict[OF hp_cont_E hpre0_sub])
          have hp_range: "\<forall>e \<in> ?pre0. p e \<in> A0" by (by100 blast)
          from continuous_map_restrict_codomain[OF
              \<open>top1_continuous_map_on ?pre0 (subspace_topology E TE ?pre0) X TX p\<close>
              hp_range hA0_sub]
          show ?thesis .
        qed
        have h_pg: "top1_is_path_on A0 (subspace_topology X TX A0) ?a0 ?a0 (p \<circ> \<gamma>)"
        proof -
          have h\<gamma>_cont2: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              ?pre0 (subspace_topology E TE ?pre0) \<gamma>"
            using h\<gamma>_pre unfolding top1_is_path_on_def by (by100 blast)
          from top1_continuous_map_on_comp[OF h\<gamma>_cont2 hp_cont_pre]
          have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              A0 (subspace_topology X TX A0) (p \<circ> \<gamma>)" .
          moreover have "(p \<circ> \<gamma>) 0 = ?a0"
            using h\<gamma> unfolding top1_is_path_on_def by (by100 simp)
          moreover have "(p \<circ> \<gamma>) 1 = ?a0"
            using h\<gamma> hpeq12 unfolding top1_is_path_on_def by (by100 simp)
          ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
        qed
        \<comment> \<open>Constant path at ?a0 in A0.\<close>
        have h_const: "top1_is_path_on A0 (subspace_topology X TX A0) ?a0 ?a0 (top1_constant_path ?a0)"
        proof -
          have "?a0 \<in> A0" using he1 hB_sub0 by (by100 blast)
          from top1_constant_path_is_path[OF hTA0 this] show ?thesis .
        qed
        \<comment> \<open>A0 SC \\<Rightarrow> loop p\\<circ>\\<gamma> is null-homotopic.\<close>
        have h_loop_pg: "top1_is_loop_on A0 (subspace_topology X TX A0) ?a0 (p \<circ> \<gamma>)"
          unfolding top1_is_loop_on_def using h_pg by (by100 blast)
        have h_htpy: "top1_path_homotopic_on A0 (subspace_topology X TX A0) ?a0 ?a0
            (p \<circ> \<gamma>) (top1_constant_path ?a0)"
        proof -
          have "?a0 \<in> A0" using he1 hB_sub0 by (by100 blast)
          from hA0_sc[unfolded top1_simply_connected_on_def, THEN conjunct2, rule_format,
              OF \<open>?a0 \<in> A0\<close> h_loop_pg]
          show ?thesis .
        qed
        \<comment> \<open>\\<gamma> is a lift of p\\<circ>\\<gamma>. constant\\_e1 is a lift of constant\\_?a0.\<close>
        have h\<gamma>_lift: "\<forall>s\<in>I_set. p (\<gamma> s) = (p \<circ> \<gamma>) s" by (by100 simp)
        have hconst_lift: "top1_is_path_on ?pre0 (subspace_topology E TE ?pre0) e1 e1
            (top1_constant_path e1)"
        proof -
          have "e1 \<in> ?pre0" using he1 hB_sub0 by (by100 blast)
          from top1_constant_path_is_path[OF hpre0_top this] show ?thesis .
        qed
        have hconst_proj: "\<forall>s\<in>I_set. p (top1_constant_path e1 s) = (top1_constant_path ?a0) s"
          unfolding top1_constant_path_def by (by100 simp)
        \<comment> \<open>Apply Theorem 54.3: homotopic paths lift to paths with same endpoint.\<close>
        have he1_pre: "e1 \<in> ?pre0" using he1 hB_sub0 by (by100 blast)
        have hpe1_eq: "p e1 = ?a0" by (by100 simp)
        from Theorem_54_3[OF hcov_A0 hpre0_top hTA0 he1_pre hpe1_eq h_pg h_const h_htpy
            h\<gamma>_pre h\<gamma>_lift hconst_lift hconst_proj]
        have "e2 = e1" by (by100 blast)
        thus "e1 = e2" by (by100 simp)
      qed
      \<comment> \<open>Endpoint preservation: p is a homeomorphism B \\<rightarrow> A0 (from inj + surj + compact/Hausdorff).
         Homeomorphisms map boundary to boundary. Arc endpoints = boundary.\<close>
      have hB_ep: "p ` (top1_arc_endpoints_on B (subspace_topology E TE B))
          = top1_arc_endpoints_on A0 (subspace_topology X TX A0)"
      proof -
        \<comment> \<open>p|B is a homeomorphism B \\<rightarrow> A0 (continuous bijection, compact \\<rightarrow> Hausdorff).\<close>
        have hB_sub_E: "B \<subseteq> E" using hB_sub0 by (by100 blast)
        have hp_homeo_B: "top1_homeomorphism_on B (subspace_topology E TE B)
            A0 (subspace_topology X TX A0) p"
          unfolding top1_homeomorphism_on_def
        proof (intro conjI)
          show "is_topology_on B (subspace_topology E TE B)"
            by (rule subspace_topology_is_topology_on[OF hTE hB_sub_E])
          show "is_topology_on A0 (subspace_topology X TX A0)" by (rule hTA0)
          show "bij_betw p B A0" unfolding bij_betw_def using hB_inj hpB_eq by (by100 blast)
          \<comment> \<open>p continuous on B (restriction of continuous p: E \\<rightarrow> X).\<close>
          show "top1_continuous_map_on B (subspace_topology E TE B) A0 (subspace_topology X TX A0) p"
          proof -
            have "top1_continuous_map_on B (subspace_topology E TE B) X TX p"
              by (rule top1_continuous_map_on_subspace_restrict[OF hp_cont hB_sub_E])
            have "\<forall>e\<in>B. p e \<in> A0" using hB_sub0 by (by100 blast)
            from continuous_map_restrict_codomain[OF
                \<open>top1_continuous_map_on B (subspace_topology E TE B) X TX p\<close>
                this hA0_sub]
            show ?thesis .
          qed
          \<comment> \<open>inv\\_into B p continuous on A0 (p is open map from covering).\<close>
          \<comment> \<open>Inverse continuity via: p|B is an open map (from covering sheets + B absorbs sheets).
             Open bijection has continuous inverse.\<close>
          have hp_open_on_B: "\<forall>U. openin_on B (subspace_topology E TE B) U \<longrightarrow>
              openin_on A0 (subspace_topology X TX A0) (p ` U)"
          proof (intro allI impI)
            fix U assume hU: "openin_on B (subspace_topology E TE B) U"
            \<comment> \<open>Show p(U) open: every point has an open neighborhood in p(U).\<close>
            have hU_sub: "U \<subseteq> B" using hU unfolding openin_on_def by (by100 blast)
            have hpU_sub: "p ` U \<subseteq> A0" using hU_sub hpB_eq by (by100 blast)
            have "\<forall>a\<in>p ` U. \<exists>V. V \<in> subspace_topology X TX A0 \<and> a \<in> V \<and> V \<subseteq> p ` U"
            proof (intro ballI)
              fix a assume "a \<in> p ` U"
              then obtain b where "b \<in> U" "p b = a" by (by100 blast)
              have "b \<in> B" using \<open>b \<in> U\<close> hU_sub by (by100 blast)
              have "b \<in> ?pre0" using \<open>b \<in> B\<close> hB_sub0 by (by100 blast)
              \<comment> \<open>Covering sheet at b.\<close>
              from covering_sheet_over_arc_path_connected[OF hcov_A0 hA0_arc hpre0_top hTA0 \<open>b \<in> ?pre0\<close>]
              obtain Wb where hWb_sub: "Wb \<subseteq> ?pre0"
                  and hWb_open: "openin_on ?pre0 (subspace_topology E TE ?pre0) Wb"
                  and hWb_b: "b \<in> Wb"
                  and hWb_pc: "top1_path_connected_on Wb (subspace_topology ?pre0 (subspace_topology E TE ?pre0) Wb)"
                  and hWb_homeo: "top1_homeomorphism_on Wb (subspace_topology ?pre0 (subspace_topology E TE ?pre0) Wb)
                      (p ` Wb) (subspace_topology A0 (subspace_topology X TX A0) (p ` Wb)) p"
                  and hWb_ev: "top1_evenly_covered_on ?pre0 (subspace_topology E TE ?pre0) A0
                      (subspace_topology X TX A0) p (p ` Wb)"
                by (by100 blast)
              \<comment> \<open>Wb \\<subseteq> B (connected sheet meets B at b, B is max conn comp).\<close>
              have hWb_conn: "top1_connected_on Wb (subspace_topology ?pre0 (subspace_topology E TE ?pre0) Wb)"
                by (rule path_connected_imp_connected[OF hWb_pc])
              have "Wb \<inter> B \<noteq> {}" using hWb_b \<open>b \<in> B\<close> by (by100 blast)
              have hWb_sub_B: "Wb \<subseteq> B"
                by (rule h_mcc_absorb[OF hpre0_top hB_comp0 hWb_conn hWb_sub \<open>Wb \<inter> B \<noteq> {}\<close>])
              \<comment> \<open>Wb \\<inter> U open in sub(preimage,sub(E,TE,preimage), Wb).
                 Since p|Wb is a homeomorphism, p(Wb \\<inter> U) open in sub(A0,sub(X,TX,A0), p(Wb)).\<close>
              \<comment> \<open>U open in sub(E,TE,B). Wb \\<subseteq> B. So Wb \\<inter> U open in sub(E,TE,Wb).\<close>
              have "p ` Wb \<in> subspace_topology X TX A0"
              proof -
                from top1_evenly_covered_on_openin_on[OF hWb_ev]
                show ?thesis unfolding openin_on_def by (by100 blast)
              qed
              \<comment> \<open>Wb \\<inter> U nonempty (b \\<in> both). a \\<in> p(Wb \\<inter> U).\<close>
              have "a \<in> p ` Wb" using \<open>p b = a\<close> hWb_b by (by100 blast)
              \<comment> \<open>Key: p(Wb) \\<subseteq> p(U). Since Wb \\<subseteq> B and... wait, Wb might not be \\<subseteq> U.
                 Actually p(Wb) might be bigger than what we need.
                 We need p(Wb) \\<inter> p(U) to contain an open nbhd of a.
                 Since p|B is injective, p(Wb \\<inter> U) = p(Wb) \\<inter> p(U).
                 And p(Wb \\<inter> U) \\<subseteq> p(U). So if p(Wb \\<inter> U) is open in A0, we're done.\<close>
              \<comment> \<open>p(Wb \\<inter> U) = p(Wb) \\<inter> p(U) (from injectivity of p on B, since Wb, U \\<subseteq> B).\<close>
              \<comment> \<open>p(Wb) open in A0 (from evenly covered). p(U) \\<subseteq> A0.
                 p(Wb) \\<inter> p(U) open in A0? Not directly (intersection of open with arbitrary).\<close>
              \<comment> \<open>Better: p(Wb) open in A0. a \\<in> p(Wb). p(Wb) \\<subseteq> p(B) = A0.
                 So p(Wb) is an open nbhd of a in A0. If p(Wb) \\<subseteq> p(U)... not true in general.\<close>
              \<comment> \<open>What IS true: p(Wb \\<inter> U) is open in p(Wb) (from homeomorphism).
                 p(Wb) open in A0. Open subset of open subset = open in A0.
                 p(Wb \\<inter> U) open in p(Wb) (homeo maps open to open).
                 p(Wb \\<inter> U) open in A0 (sub-open of open = open).\<close>
              have hWbU_open_in_pWb: "openin_on (p ` Wb) (subspace_topology A0 (subspace_topology X TX A0) (p ` Wb)) (p ` (Wb \<inter> U))"
              proof -
                \<comment> \<open>Wb \\<inter> U is open in sub(?pre0, sub(E,TE,?pre0), Wb).
                   Proof: U open in sub(E,TE,B) \\<Rightarrow> U = V0 \\<inter> B for V0 \\<in> TE.
                   Wb \\<inter> U = Wb \\<inter> V0 \\<inter> B = Wb \\<inter> V0 (since Wb \\<subseteq> B).
                   Wb \\<inter> V0 = V0 \\<inter> Wb \\<in> sub(E,TE,Wb) = sub(?pre0, sub(E,TE,?pre0), Wb).\<close>
                have hWbU_open_Wb: "Wb \<inter> U \<in> subspace_topology ?pre0 (subspace_topology E TE ?pre0) Wb"
                proof -
                  from hU[unfolded openin_on_def]
                  have "U \<in> subspace_topology E TE B" by (by100 blast)
                  then obtain V0 where "V0 \<in> TE" "U = V0 \<inter> B"
                    unfolding subspace_topology_def by (by100 blast)
                  have "Wb \<inter> U = V0 \<inter> Wb" using \<open>U = V0 \<inter> B\<close> hWb_sub_B by (by100 blast)
                  moreover have "V0 \<inter> Wb \<in> subspace_topology E TE Wb"
                    unfolding subspace_topology_def using \<open>V0 \<in> TE\<close> by (by100 blast)
                  moreover have "subspace_topology E TE Wb = subspace_topology ?pre0 (subspace_topology E TE ?pre0) Wb"
                    by (rule subspace_topology_trans[OF hWb_sub, symmetric])
                  ultimately show ?thesis by simp
                qed
                \<comment> \<open>p|Wb homeomorphism maps open Wb\\<inter>U to open p(Wb\\<inter>U).\<close>
                \<comment> \<open>The homeomorphism on\\_def says: f continuous + f\\<inverse> continuous + bijective.
                   Continuous \\<Rightarrow> preimage of open is open. Equivalently: image of open is open (from inverse).\<close>
                have "openin_on Wb (subspace_topology ?pre0 (subspace_topology E TE ?pre0) Wb) (Wb \<inter> U)"
                  unfolding openin_on_def using hWbU_open_Wb hU_sub hWb_sub_B by (by100 blast)
                \<comment> \<open>Homeomorphism: continuous inverse means p maps open to open.\<close>
                have hp_inv_cont: "top1_continuous_map_on (p ` Wb)
                    (subspace_topology A0 (subspace_topology X TX A0) (p ` Wb))
                    Wb (subspace_topology ?pre0 (subspace_topology E TE ?pre0) Wb) (inv_into Wb p)"
                  using hWb_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
                \<comment> \<open>Preimage of (Wb\\<inter>U) under inv\\_into is {a \\<in> p(Wb). inv(a) \\<in> Wb\\<inter>U} = p(Wb\\<inter>U).
                   Since inv\\_into is continuous, this preimage is open.\<close>
                have "{a \<in> p ` Wb. inv_into Wb p a \<in> Wb \<inter> U} = p ` (Wb \<inter> U)"
                proof (rule set_eqI, rule iffI)
                  fix a assume "a \<in> {a \<in> p ` Wb. inv_into Wb p a \<in> Wb \<inter> U}"
                  hence "a \<in> p ` Wb" "inv_into Wb p a \<in> Wb \<inter> U" by (by100 blast)+
                  have "p (inv_into Wb p a) = a" using f_inv_into_f[OF \<open>a \<in> p ` Wb\<close>] .
                  hence "a = p (inv_into Wb p a)" by simp
                  thus "a \<in> p ` (Wb \<inter> U)" using \<open>inv_into Wb p a \<in> Wb \<inter> U\<close> by (by100 blast)
                next
                  fix a assume "a \<in> p ` (Wb \<inter> U)"
                  then obtain w where "w \<in> Wb" "w \<in> U" "a = p w" by (by100 blast)
                  have "a \<in> p ` Wb" using \<open>w \<in> Wb\<close> \<open>a = p w\<close> by (by100 blast)
                  have hinj_Wb: "inj_on p Wb"
                    using hWb_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
                  have "inv_into Wb p a = w" using inv_into_f_f[OF hinj_Wb \<open>w \<in> Wb\<close>] \<open>a = p w\<close> by simp
                  thus "a \<in> {a \<in> p ` Wb. inv_into Wb p a \<in> Wb \<inter> U}"
                    using \<open>a \<in> p ` Wb\<close> \<open>w \<in> Wb\<close> \<open>w \<in> U\<close> \<open>inv_into Wb p a = w\<close> by (by100 blast)
                qed
                from hp_inv_cont[unfolded top1_continuous_map_on_def, THEN conjunct2,
                    rule_format, OF hWbU_open_Wb]
                have "{a \<in> p ` Wb. inv_into Wb p a \<in> Wb \<inter> U}
                    \<in> subspace_topology A0 (subspace_topology X TX A0) (p ` Wb)" .
                hence "p ` (Wb \<inter> U) \<in> subspace_topology A0 (subspace_topology X TX A0) (p ` Wb)"
                  using \<open>{a \<in> p ` Wb. inv_into Wb p a \<in> Wb \<inter> U} = p ` (Wb \<inter> U)\<close> by simp
                moreover have "p ` (Wb \<inter> U) \<subseteq> p ` Wb" by (by100 blast)
                ultimately show ?thesis unfolding openin_on_def by (by100 blast)
              qed
              have "a \<in> p ` (Wb \<inter> U)" using \<open>p b = a\<close> hWb_b \<open>b \<in> U\<close> by (by100 blast)
              have "p ` (Wb \<inter> U) \<subseteq> p ` U" by (by100 blast)
              \<comment> \<open>p(Wb \\<inter> U) is open in A0 (open in open subset of A0).\<close>
              have "p ` (Wb \<inter> U) \<in> subspace_topology X TX A0"
              proof -
                from hWbU_open_in_pWb[unfolded openin_on_def]
                \<comment> \<open>Use subspace\\_topology\\_trans to collapse double subspace.\<close>
                have hpWb_sub_A0: "p ` Wb \<subseteq> A0"
                  using hWb_sub hB_sub0 hpB_eq hWb_sub_B by (by100 blast)
                have "subspace_topology A0 (subspace_topology X TX A0) (p ` Wb)
                    = subspace_topology X TX (p ` Wb)"
                  by (rule subspace_topology_trans[OF hpWb_sub_A0])
                \<comment> \<open>p ` (Wb \\<inter> U) \\<in> sub(X,TX,p(Wb)): from openin\\_on and topology collapse.\<close>
                have "p ` (Wb \<inter> U) \<in> subspace_topology X TX (p ` Wb)"
                proof -
                  from hWbU_open_in_pWb[unfolded openin_on_def]
                  have "p ` (Wb \<inter> U) \<in> subspace_topology A0 (subspace_topology X TX A0) (p ` Wb)"
                    by (by100 blast)
                  thus ?thesis using \<open>subspace_topology A0 _ _ = subspace_topology X TX _\<close> by simp
                qed
                \<comment> \<open>So p ` (Wb \\<inter> U) = V \\<inter> p(Wb) for V \\<in> TX.\<close>
                then obtain VR where "VR \<in> TX" "p ` (Wb \<inter> U) = VR \<inter> p ` Wb"
                proof -
                  assume hgoal: "\<And>VR. VR \<in> TX \<Longrightarrow> p ` (Wb \<inter> U) = VR \<inter> p ` Wb \<Longrightarrow> thesis"
                  from \<open>p ` (Wb \<inter> U) \<in> subspace_topology X TX (p ` Wb)\<close>
                  obtain VR0 where "VR0 \<in> TX" "p ` (Wb \<inter> U) = VR0 \<inter> p ` Wb"
                    unfolding subspace_topology_def by (by100 auto)
                  from hgoal[OF this] show thesis .
                qed
                \<comment> \<open>p(Wb) = V2 \\<inter> A0 for V2 \\<in> TX.\<close>
                obtain V2 where "V2 \<in> TX" "p ` Wb = V2 \<inter> A0"
                  using \<open>p ` Wb \<in> subspace_topology X TX A0\<close>
                  unfolding subspace_topology_def by (by100 blast)
                \<comment> \<open>p(Wb \\<inter> U) = V \\<inter> V2 \\<inter> A0, and V \\<inter> V2 \\<in> TX.\<close>
                have "p ` (Wb \<inter> U) = (VR \<inter> V2) \<inter> A0"
                  using \<open>p ` (Wb \<inter> U) = VR \<inter> p ` Wb\<close> \<open>p ` Wb = V2 \<inter> A0\<close> by (by100 blast)
                moreover have "VR \<inter> V2 \<in> TX"
                proof -
                  have hfin_inter: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TX \<longrightarrow> \<Inter>F \<in> TX"
                    using hTX unfolding is_topology_on_def by (by100 blast)
                  have "finite {VR, V2} \<and> {VR, V2} \<noteq> {} \<and> {VR, V2} \<subseteq> TX"
                    using \<open>VR \<in> TX\<close> \<open>V2 \<in> TX\<close> by (by100 simp)
                  from hfin_inter[rule_format, OF this]
                  have "\<Inter>{VR, V2} \<in> TX" .
                  thus ?thesis by (by100 simp)
                qed
                ultimately have "p ` (Wb \<inter> U) \<in> subspace_topology X TX A0"
                  unfolding subspace_topology_def using \<open>VR \<inter> V2 \<in> TX\<close> by (by100 blast)
                thus ?thesis .
              qed
              thus "\<exists>V. V \<in> subspace_topology X TX A0 \<and> a \<in> V \<and> V \<subseteq> p ` U"
                using \<open>a \<in> p ` (Wb \<inter> U)\<close> \<open>p ` (Wb \<inter> U) \<subseteq> p ` U\<close> by (by100 blast)
            qed
            \<comment> \<open>p(U) = union of open sets \\<Rightarrow> open.\<close>
            have "p ` U = \<Union>{V. V \<in> subspace_topology X TX A0 \<and> V \<subseteq> p ` U}"
            proof (rule set_eqI, rule iffI)
              fix a assume "a \<in> p ` U"
              with \<open>\<forall>a\<in>p ` U. _\<close>[rule_format, OF this]
              obtain V where "V \<in> subspace_topology X TX A0" "a \<in> V" "V \<subseteq> p ` U" by (by100 blast)
              thus "a \<in> \<Union>{V. V \<in> subspace_topology X TX A0 \<and> V \<subseteq> p ` U}" by (by100 blast)
            next
              fix a assume "a \<in> \<Union>{V. V \<in> subspace_topology X TX A0 \<and> V \<subseteq> p ` U}"
              thus "a \<in> p ` U" by (by100 blast)
            qed
            moreover have "\<Union>{V. V \<in> subspace_topology X TX A0 \<and> V \<subseteq> p ` U} \<in> subspace_topology X TX A0"
            proof -
              have hsub_TA0: "{V. V \<in> subspace_topology X TX A0 \<and> V \<subseteq> p ` U} \<subseteq> subspace_topology X TX A0"
                by (by100 blast)
              have "\<forall>S\<subseteq>subspace_topology X TX A0. \<Union>S \<in> subspace_topology X TX A0"
                using hTA0 unfolding is_topology_on_def by (by100 blast)
              thus ?thesis using hsub_TA0 by (by100 blast)
            qed
            ultimately have "p ` U \<in> subspace_topology X TX A0" by simp
            thus "openin_on A0 (subspace_topology X TX A0) (p ` U)"
              unfolding openin_on_def using hpU_sub by (by100 blast)
          qed
          \<comment> \<open>Open bijection has continuous inverse.\<close>
          show "top1_continuous_map_on A0 (subspace_topology X TX A0) B (subspace_topology E TE B)
              (inv_into B p)"
          proof -
            have hTB: "is_topology_on B (subspace_topology E TE B)"
              by (rule subspace_topology_is_topology_on[OF hTE hB_sub_E])
            show ?thesis unfolding top1_continuous_map_on_def
            proof (intro conjI ballI)
              fix a assume "a \<in> A0"
              have "a \<in> p ` B" using \<open>a \<in> A0\<close> hpB_eq by simp
              from inv_into_into[OF this] show "inv_into B p a \<in> B" .
            next
              fix V assume "V \<in> subspace_topology E TE B"
              \<comment> \<open>{a \\<in> A0. inv\\_into B p a \\<in> V} = p(V \\<inter> B) = p(V) (since V \\<subseteq> B from subspace).\<close>
              have "V \<subseteq> B"
              proof -
                from \<open>V \<in> subspace_topology E TE B\<close>
                obtain W where "W \<in> TE" "V = W \<inter> B" unfolding subspace_topology_def by (by100 blast)
                thus ?thesis by (by100 blast)
              qed
              have "{a \<in> A0. inv_into B p a \<in> V} = p ` V"
              proof (rule set_eqI, rule iffI)
                fix a assume "a \<in> {a \<in> A0. inv_into B p a \<in> V}"
                hence "a \<in> A0" "inv_into B p a \<in> V" by (by100 blast)+
                have "inv_into B p a \<in> B" using \<open>inv_into B p a \<in> V\<close> \<open>V \<subseteq> B\<close> by (by100 blast)
                have "p (inv_into B p a) = a"
                proof -
                  have "a \<in> p ` B" using \<open>a \<in> A0\<close> hpB_eq by simp
                  from f_inv_into_f[OF this] show ?thesis .
                qed
                hence "a = p (inv_into B p a)" by simp
                thus "a \<in> p ` V" using \<open>inv_into B p a \<in> V\<close> by (by100 blast)
              next
                fix a assume "a \<in> p ` V"
                then obtain v where "v \<in> V" "a = p v" by (by100 blast)
                have "v \<in> B" using \<open>v \<in> V\<close> \<open>V \<subseteq> B\<close> by (by100 blast)
                have "a \<in> A0" using \<open>a = p v\<close> \<open>v \<in> B\<close> hpB_eq by (by100 blast)
                have "inv_into B p a = v"
                  using inv_into_f_f[OF hB_inj \<open>v \<in> B\<close>] \<open>a = p v\<close> by simp
                thus "a \<in> {a \<in> A0. inv_into B p a \<in> V}" using \<open>a \<in> A0\<close> \<open>v \<in> V\<close>
                    \<open>inv_into B p a = v\<close> by (by100 blast)
              qed
              \<comment> \<open>V open in sub(E,TE,B). openin\\_on B ... V. p(V) open in A0.\<close>
              have "openin_on B (subspace_topology E TE B) V"
                unfolding openin_on_def using \<open>V \<subseteq> B\<close> \<open>V \<in> subspace_topology E TE B\<close> by (by100 blast)
              from hp_open_on_B[rule_format, OF this]
              have "openin_on A0 (subspace_topology X TX A0) (p ` V)" .
              hence "p ` V \<in> subspace_topology X TX A0" unfolding openin_on_def by (by100 blast)
              thus "{a \<in> A0. inv_into B p a \<in> V} \<in> subspace_topology X TX A0"
                using \<open>{a \<in> A0. inv_into B p a \<in> V} = p ` V\<close> by simp
            qed
          qed
        qed
        \<comment> \<open>Get homeomorphism h\\_A0: [0,1] \\<rightarrow> A0.\<close>
        obtain h_A0 where hh_A0: "top1_homeomorphism_on top1_unit_interval
            top1_unit_interval_topology A0 (subspace_topology X TX A0) h_A0"
          using hA0_arc unfolding top1_is_arc_on_def by (by100 blast)
        \<comment> \<open>Compose: (p|B)^{-1} \\<circ> h\\_A0: [0,1] \\<rightarrow> B is a homeomorphism.\<close>
        \<comment> \<open>Then B is an arc.\<close>
        \<comment> \<open>endpoints\\_A0 = {h\\_A0(0), h\\_A0(1)}. endpoints\\_B = {g(0), g(1)} where g = inv \\<circ> h\\_A0.\<close>
        \<comment> \<open>p(g(0)) = p(inv(h\\_A0(0))) = h\\_A0(0). Similarly p(g(1)) = h\\_A0(1).\<close>
        \<comment> \<open>So p ` endpoints\\_B = endpoints\\_A0.\<close>
        have hep_A0: "top1_arc_endpoints_on A0 (subspace_topology X TX A0) = {h_A0 0, h_A0 1}"
          by (rule arc_endpoints_are_boundary[OF hTX_strict hX_haus hA0_sub hA0_arc hh_A0])
        \<comment> \<open>The inverse p|B^{-1}: A0 \\<rightarrow> B is well-defined.\<close>
        let ?invp = "inv_into B p"
        have hinvp_range: "\<forall>a\<in>A0. ?invp a \<in> B"
        proof (intro ballI)
          fix a assume "a \<in> A0"
          hence "a \<in> p ` B" using hpB_eq by simp
          from inv_into_into[OF this] show "?invp a \<in> B" .
        qed
        \<comment> \<open>g = inv\\_p \\<circ> h\\_A0: [0,1] \\<rightarrow> B is a homeomorphism.\<close>
        let ?g = "?invp \<circ> h_A0"
        have hg_homeo: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
            B (subspace_topology E TE B) ?g"
        proof -
          have hinvp_homeo: "top1_homeomorphism_on A0 (subspace_topology X TX A0)
              B (subspace_topology E TE B) ?invp"
            by (rule homeomorphism_inverse[OF hp_homeo_B])
          from homeomorphism_comp[OF hh_A0 hinvp_homeo]
          show ?thesis .
        qed
        \<comment> \<open>B is an arc.\<close>
        have hB_strict: "is_topology_on_strict B (subspace_topology E TE B)"
          by (rule subspace_topology_is_strict[OF hstrict_E hB_sub_E])
        have hB_arc: "top1_is_arc_on B (subspace_topology E TE B)"
          unfolding top1_is_arc_on_def using hB_strict hg_homeo by (by100 blast)
        \<comment> \<open>endpoints\\_B = {g(0), g(1)} = {inv\\_p(h\\_A0(0)), inv\\_p(h\\_A0(1))}.\<close>
        have hE_strict: "is_topology_on_strict E TE" using hstrict_E .
        have hE_haus: "is_hausdorff_on E TE"
        proof -
          have "top1_is_graph_on E TE"
            by (rule Theorem_83_4_covering_of_graph_is_graph[OF hgraph_X hcov hstrict_E])
          thus ?thesis unfolding top1_is_graph_on_def by (by100 blast)
        qed
        have hep_B: "top1_arc_endpoints_on B (subspace_topology E TE B) = {?g 0, ?g 1}"
          by (rule arc_endpoints_are_boundary[OF hE_strict hE_haus hB_sub_E hB_arc hg_homeo])
        \<comment> \<open>p(g(0)) = p(inv\\_p(h\\_A0(0))) = h\\_A0(0). Similarly for 1.\<close>
        have h_bij_A0: "bij_betw h_A0 top1_unit_interval A0"
          using hh_A0 unfolding top1_homeomorphism_on_def by (by100 blast)
        have h0_I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
        have h1_I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
        have h_A0_0: "h_A0 0 \<in> A0"
          using h_bij_A0 h0_I unfolding bij_betw_def by (by100 blast)
        have h_A0_1: "h_A0 1 \<in> A0"
          using h_bij_A0 h1_I unfolding bij_betw_def by (by100 blast)
        have "h_A0 0 \<in> p ` B" using h_A0_0 hpB_eq by simp
        have "h_A0 1 \<in> p ` B" using h_A0_1 hpB_eq by simp
        \<comment> \<open>f(inv\\_into A f x) = x when x \\<in> f ` A.\<close>
        have "p (?g 0) = h_A0 0"
          using f_inv_into_f[OF \<open>h_A0 0 \<in> p ` B\<close>] by (by100 simp)
        have "p (?g 1) = h_A0 1"
          using f_inv_into_f[OF \<open>h_A0 1 \<in> p ` B\<close>] by (by100 simp)
        show ?thesis
          using hep_A0 hep_B \<open>p (?g 0) = h_A0 0\<close> \<open>p (?g 1) = h_A0 1\<close> by (by100 auto)
      qed
      have hconj: "B \<subseteq> {e \<in> E. p e \<in> A0} \<and> p ` B = A0 \<and> inj_on p B
          \<and> p ` (top1_arc_endpoints_on B (subspace_topology E TE B))
            = top1_arc_endpoints_on A0 (subspace_topology X TX A0)"
        using hB_sub0 hpB_eq hB_inj hB_ep by (by100 blast)
      show "\<exists>A\<in>\<A>w. B \<subseteq> {e \<in> E. p e \<in> A} \<and> p ` B = A \<and> inj_on p B
          \<and> p ` (top1_arc_endpoints_on B (subspace_topology E TE B))
            = top1_arc_endpoints_on A (subspace_topology X TX A)"
        apply (rule bexI[of _ A0])
         apply (rule hconj)
        apply (rule hA0)
        done
    qed
  next
    \<comment> \<open>Clause 2: every fiber point over a base arc is in some lift.\<close>
    show "\<forall>A\<in>\<A>w. \<forall>e\<in>{e' \<in> E. p e' \<in> A}. \<exists>B\<in>?\<A>_L. e \<in> B \<and> B \<subseteq> {e' \<in> E. p e' \<in> A} \<and> p ` B = A"
    proof (intro ballI)
      fix A e assume hA: "A \<in> \<A>w" and he: "e \<in> {e' \<in> E. p e' \<in> A}"
      let ?pre = "{e' \<in> E. p e' \<in> A}"
      have hpre_sub: "?pre \<subseteq> E" by (by100 blast)
      have hpre_top: "is_topology_on ?pre (subspace_topology E TE ?pre)"
        by (rule subspace_topology_is_topology_on[OF hTE hpre_sub])
      have he_pre: "e \<in> ?pre" using he by (by100 blast)
      \<comment> \<open>By max\\_conn\\_comp\\_covers: e is in some max conn comp B of preimage(A).\<close>
      from max_conn_comp_covers[OF hpre_top he_pre]
      obtain B where hB_comp: "top1_max_conn_comp ?pre (subspace_topology E TE ?pre) B"
          and he_B: "e \<in> B" by (by100 blast)
      have hB_sub: "B \<subseteq> ?pre" using max_conn_comp_sub[OF hB_comp] .
      \<comment> \<open>B \\<in> ?\\<A>\\_L by construction (B is a max conn comp of preimage(A) for A \\<in> \\<A>w).\<close>
      have hB_in: "B \<in> ?\<A>_L"
      proof -
        have "B \<in> {B'. top1_max_conn_comp ?pre (subspace_topology E TE ?pre) B'}"
          using hB_comp by (by100 blast)
        thus ?thesis using hA by (by100 blast)
      qed
      \<comment> \<open>Surjectivity: p ` B = A. By path lifting: for any a \\<in> A, lift a path from p(e) to a.
         The lift stays in preimage(A) and in B (connected component). End maps to a.\<close>
      have hp_surj_B: "p ` B = A"
        by (rule h_comp_surj[OF hA hB_comp])
      show "\<exists>B\<in>?\<A>_L. e \<in> B \<and> B \<subseteq> {e' \<in> E. p e' \<in> A} \<and> p ` B = A"
        using hB_in he_B hB_sub hp_surj_B by (by100 blast)
    qed
  next
    \<comment> \<open>Clause 3: lifts over the same base arc are pairwise disjoint.
       If B1, B2 are max conn comps of preimage(A) and B1 \\<ne> B2, disjoint by h\\_mcc\\_disjoint.
       If they come from different arcs' preimages, the fact that both \\<subseteq> preimage(A)
       and max conn comp maximality forces containment in the same max conn comp of preimage(A).\<close>
    show "\<forall>A\<in>\<A>w. \<forall>B1\<in>?\<A>_L. \<forall>B2\<in>?\<A>_L.
        B1 \<subseteq> {e \<in> E. p e \<in> A} \<and> B2 \<subseteq> {e \<in> E. p e \<in> A} \<and> B1 \<noteq> B2
        \<longrightarrow> B1 \<inter> B2 = {}"
    proof (intro ballI impI)
      fix A B1 B2
      assume hA: "A \<in> \<A>w" and hB1L: "B1 \<in> ?\<A>_L" and hB2L: "B2 \<in> ?\<A>_L"
          and hconj: "B1 \<subseteq> {e \<in> E. p e \<in> A} \<and> B2 \<subseteq> {e \<in> E. p e \<in> A} \<and> B1 \<noteq> B2"
      have hB1_sub: "B1 \<subseteq> {e \<in> E. p e \<in> A}" and hB2_sub: "B2 \<subseteq> {e \<in> E. p e \<in> A}"
          and hne: "B1 \<noteq> B2" using hconj by (by100 blast)+
      \<comment> \<open>B1 is connected (from max conn comp). B1 \\<subseteq> preimage(A).
         So B1 is in some max conn comp C1 of preimage(A).
         Similarly B2 \\<subseteq> C2. If B1 \\<inter> B2 \\<ne> {}, then C1 = C2 (max conn comps form partition).
         But then both B1, B2 \\<subseteq> C1, and C1 is a max conn comp of preimage(A).
         If C1 \\<inter> B1 \\<ne> {} and C1 \\<inter> B2 \\<ne> {}, we can derive B1 = C1 = B2 via maximality
         (since B1 \\<union> C1 connected and B1 is max in its own preimage).
         Actually, for the same-arc case this is immediate from h\\_mcc\\_disjoint.
         The cross-arc case: show B1 \\<subseteq> C1 and B2 \\<subseteq> C1, then use h\\_mcc\\_disjoint on C1.\<close>
      \<comment> \<open>Both are connected and in preimage(A). If they overlap, both are in the same
         max conn comp C of preimage(A). Leads to B1=C=B2, contradicting B1\\<ne>B2.\<close>
      show "B1 \<inter> B2 = {}"
      proof (rule ccontr)
        assume "B1 \<inter> B2 \<noteq> {}"
        \<comment> \<open>B1 is max conn comp of preimage(A1) for some A1. By h\\_comp\\_surj: p`B1 = A1.
           B1 \\<subseteq> preimage(A) \\<Rightarrow> p`B1 \\<subseteq> A \\<Rightarrow> A1 \\<subseteq> A. Similarly A2 \\<subseteq> A.
           In a graph: A1, A are arcs in \\<A>w with A1 \\<subseteq> A. Since arcs cover X and meet only at
           endpoints, A1 \\<subseteq> A and A1 is an arc (nonempty interior) forces A1 = A.
           Similarly A2 = A. Then B1, B2 are max conn comps of preimage(A), and
           h\\_mcc\\_disjoint gives B1 \\<inter> B2 = {} since B1 \\<ne> B2.\<close>
        obtain A1 where hA1: "A1 \<in> \<A>w"
            and hB1_comp: "top1_max_conn_comp {e \<in> E. p e \<in> A1}
                (subspace_topology E TE {e \<in> E. p e \<in> A1}) B1"
          using hB1L by (by100 blast)
        obtain A2 where hA2: "A2 \<in> \<A>w"
            and hB2_comp: "top1_max_conn_comp {e \<in> E. p e \<in> A2}
                (subspace_topology E TE {e \<in> E. p e \<in> A2}) B2"
          using hB2L by (by100 blast)
        \<comment> \<open>p`B1 = A1 (from h\\_comp\\_surj). A1 \\<subseteq> A (from B1 \\<subseteq> preimage(A)).\<close>
        have "p ` B1 = A1" by (rule h_comp_surj[OF hA1 hB1_comp])
        have "p ` B1 \<subseteq> A" using hB1_sub by (by100 blast)
        hence "A1 \<subseteq> A" using \<open>p ` B1 = A1\<close> by simp
        \<comment> \<open>A1 \\<subseteq> A and both are arcs in \\<A>w. A1 = A.\<close>
        have "A1 = A"
        proof (rule ccontr)
          assume "A1 \<noteq> A"
          \<comment> \<open>A1 \\<inter> A \\<subseteq> endpoints(A1). But A1 \\<subseteq> A \\<Rightarrow> A1 \\<inter> A = A1. So A1 \\<subseteq> endpoints(A1).
             Endpoints have card \\<le> 2. But A1 is an arc, so card A1 is infinite. Contradiction.\<close>
          have "A1 \<inter> A \<subseteq> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
            using h\<A>w_inter[rule_format, OF hA1 hA \<open>A1 \<noteq> A\<close>] by (by100 blast)
          hence "A1 \<subseteq> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
            using \<open>A1 \<subseteq> A\<close> by (by100 blast)
          moreover have "finite (top1_arc_endpoints_on A1 (subspace_topology X TX A1))"
          proof -
            have "top1_is_arc_on A1 (subspace_topology X TX A1)" using h\<A>w hA1 by (by100 blast)
            then obtain h1 where hh1: "top1_homeomorphism_on I_set I_top A1 (subspace_topology X TX A1) h1"
              unfolding top1_is_arc_on_def by (by100 blast)
            have "A1 \<subseteq> X" using h\<A>w hA1 by (by100 blast)
            from arc_endpoints_are_boundary[OF hTX_strict hX_haus \<open>A1 \<subseteq> X\<close>
                \<open>top1_is_arc_on A1 _\<close> hh1]
            show ?thesis by (by100 simp)
          qed
          moreover have "\<not> finite A1"
          proof -
            have "top1_is_arc_on A1 (subspace_topology X TX A1)" using h\<A>w hA1 by (by100 blast)
            then obtain h1 where hh1: "top1_homeomorphism_on I_set I_top A1 (subspace_topology X TX A1) h1"
              unfolding top1_is_arc_on_def by (by100 blast)
            have "bij_betw h1 I_set A1" using hh1 unfolding top1_homeomorphism_on_def by (by100 blast)
            hence "h1 ` I_set = A1" unfolding bij_betw_def by (by100 blast)
            moreover have "\<not> finite I_set"
            proof -
              have "infinite {x::real. 0 \<le> x \<and> x \<le> 1}"
              proof -
                have "{0::real..1} = {x. 0 \<le> x \<and> x \<le> 1}"
                  unfolding atLeastAtMost_def atLeast_def atMost_def by (by100 blast)
                moreover have "infinite {0::real..1}" by (rule infinite_Icc) linarith
                ultimately show ?thesis by simp
              qed
              thus ?thesis unfolding top1_unit_interval_def by (by100 simp)
            qed
            moreover have "inj_on h1 I_set" using \<open>bij_betw h1 I_set A1\<close>
              unfolding bij_betw_def by (by100 blast)
            ultimately show ?thesis using finite_imageD by (by100 blast)
          qed
          ultimately show False using finite_subset by (by100 blast)
        qed
        \<comment> \<open>Similarly A2 = A.\<close>
        have "p ` B2 = A2" by (rule h_comp_surj[OF hA2 hB2_comp])
        have "p ` B2 \<subseteq> A" using hB2_sub by (by100 blast)
        hence "A2 \<subseteq> A" using \<open>p ` B2 = A2\<close> by simp
        have "A2 = A"
        proof (rule ccontr)
          assume "A2 \<noteq> A"
          have "A2 \<inter> A \<subseteq> top1_arc_endpoints_on A2 (subspace_topology X TX A2)"
            using h\<A>w_inter[rule_format, OF hA2 hA \<open>A2 \<noteq> A\<close>] by (by100 blast)
          hence "A2 \<subseteq> top1_arc_endpoints_on A2 (subspace_topology X TX A2)"
            using \<open>A2 \<subseteq> A\<close> by (by100 blast)
          moreover have "finite (top1_arc_endpoints_on A2 (subspace_topology X TX A2))"
          proof -
            have "top1_is_arc_on A2 (subspace_topology X TX A2)" using h\<A>w hA2 by (by100 blast)
            then obtain h2 where hh2: "top1_homeomorphism_on I_set I_top A2 (subspace_topology X TX A2) h2"
              unfolding top1_is_arc_on_def by (by100 blast)
            have "A2 \<subseteq> X" using h\<A>w hA2 by (by100 blast)
            from arc_endpoints_are_boundary[OF hTX_strict hX_haus \<open>A2 \<subseteq> X\<close>
                \<open>top1_is_arc_on A2 _\<close> hh2]
            show ?thesis by (by100 simp)
          qed
          moreover have "\<not> finite A2"
          proof -
            have "top1_is_arc_on A2 (subspace_topology X TX A2)" using h\<A>w hA2 by (by100 blast)
            then obtain h2 where hh2: "top1_homeomorphism_on I_set I_top A2 (subspace_topology X TX A2) h2"
              unfolding top1_is_arc_on_def by (by100 blast)
            have "bij_betw h2 I_set A2" using hh2 unfolding top1_homeomorphism_on_def by (by100 blast)
            hence "h2 ` I_set = A2" unfolding bij_betw_def by (by100 blast)
            moreover have "\<not> finite I_set"
            proof -
              have "infinite {0::real..1}" by (rule infinite_Icc) linarith
              hence "infinite {x::real. 0 \<le> x \<and> x \<le> 1}"
              proof -
                have "{0::real..1} = {x. 0 \<le> x \<and> x \<le> 1}"
                  unfolding atLeastAtMost_def atLeast_def atMost_def by (by100 blast)
                thus ?thesis using \<open>infinite {0::real..1}\<close> by simp
              qed
              thus ?thesis unfolding top1_unit_interval_def by (by100 simp)
            qed
            moreover have "inj_on h2 I_set" using \<open>bij_betw h2 I_set A2\<close>
              unfolding bij_betw_def by (by100 blast)
            ultimately show ?thesis using finite_imageD by (by100 blast)
          qed
          ultimately show False using finite_subset by (by100 blast)
        qed
        \<comment> \<open>Now B1, B2 are max conn comps of preimage(A). h\\_mcc\\_disjoint gives B1 \\<inter> B2 = {}.\<close>
        have "B1 \<inter> B2 = {}"
        proof -
          have hpre_top: "is_topology_on {e \<in> E. p e \<in> A} (subspace_topology E TE {e \<in> E. p e \<in> A})"
            by (rule subspace_topology_is_topology_on[OF hTE]) (by100 blast)
          have hB1_compA: "top1_max_conn_comp {e \<in> E. p e \<in> A}
              (subspace_topology E TE {e \<in> E. p e \<in> A}) B1"
            using hB1_comp \<open>A1 = A\<close> by simp
          have hB2_compA: "top1_max_conn_comp {e \<in> E. p e \<in> A}
              (subspace_topology E TE {e \<in> E. p e \<in> A}) B2"
            using hB2_comp \<open>A2 = A\<close> by simp
          from h_mcc_disjoint[OF hpre_top hB1_compA hB2_compA hne]
          show ?thesis .
        qed
        with \<open>B1 \<inter> B2 \<noteq> {}\<close> show False by (by100 blast)
      qed
    qed
  qed
  have h\<A>w_sub: "\<forall>A\<in>\<A>w. A \<subseteq> X \<and> A \<noteq> {}"
  proof (intro ballI conjI)
    fix A assume "A \<in> \<A>w"
    show "A \<subseteq> X" using h\<A>w \<open>A \<in> \<A>w\<close> by (by100 blast)
    show "A \<noteq> {}"
    proof -
      have "top1_is_arc_on A (subspace_topology X TX A)" using h\<A>w \<open>A \<in> \<A>w\<close> by (by100 blast)
      then obtain h where "top1_homeomorphism_on I_set I_top A (subspace_topology X TX A) h"
        unfolding top1_is_arc_on_def by (by100 blast)
      hence "h ` I_set = A" unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      moreover have "I_set \<noteq> {}" unfolding top1_unit_interval_def by (by100 auto)
      ultimately show ?thesis by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 4: Apply multiplicity lemmas.
     card(\\<A>\\_L) = k * card(\\<A>w) and card(V\\_L) = k * card(V\\_X).\<close>
  have h\<A>_L_card: "finite ?\<A>_L \<and> card ?\<A>_L = k * card \<A>w"
    by (rule covering_lifted_arc_family_card[OF hcov h_lifted h\<A>w_fin hfiber h\<A>w_sub hk])
  have hV_X_fin: "finite (top1_graph_vertex_set X TX \<A>w)"
  proof -
    have hstrict_X: "is_topology_on_strict X TX"
      using hgraph_X unfolding top1_is_graph_on_def by (by100 blast)
    have hhaus_X: "is_hausdorff_on X TX"
      using hgraph_X unfolding top1_is_graph_on_def by (by100 blast)
    have "\<forall>A\<in>\<A>w. finite (top1_arc_endpoints_on A (subspace_topology X TX A))"
    proof (intro ballI)
      fix A assume "A \<in> \<A>w"
      have "top1_is_arc_on A (subspace_topology X TX A)" using h\<A>w \<open>A \<in> \<A>w\<close> by (by100 blast)
      have "A \<subseteq> X" using h\<A>w \<open>A \<in> \<A>w\<close> by (by100 blast)
      then obtain h where "top1_homeomorphism_on I_set I_top A (subspace_topology X TX A) h"
        using \<open>top1_is_arc_on A _\<close> unfolding top1_is_arc_on_def by (by100 blast)
      from arc_endpoints_are_boundary[OF hstrict_X hhaus_X \<open>A \<subseteq> X\<close> \<open>top1_is_arc_on A _\<close> this]
      have "top1_arc_endpoints_on A (subspace_topology X TX A) = {h 0, h 1}" .
      thus "finite (top1_arc_endpoints_on A (subspace_topology X TX A))" by (by100 simp)
    qed
    thus ?thesis unfolding top1_graph_vertex_set_def using h\<A>w_fin by (by100 blast)
  qed
  have hV_L_card: "card (top1_graph_vertex_set E TE ?\<A>_L) = k * card (top1_graph_vertex_set X TX \<A>w)"
    by (rule covering_lifted_vertex_set_card[OF hcov h_lifted hV_X_fin hfiber h\<A>w_sub hk])
  \<comment> \<open>Step 5: E is a graph. Apply graph\\_pi1\\_free\\_weak to E.
     This gives \\<pi>\\_1(E) free on some basis. The rank = number of non-tree arcs.\<close>
  have hE_graph: "top1_is_graph_on E TE"
    by (rule Theorem_83_4_covering_of_graph_is_graph[OF hgraph_X hcov hstrict_E])
  \<comment> \<open>Extract free group from graph\\_pi1\\_free\\_weak via Isar block.\<close>
  from graph_pi1_free_weak[OF hE_graph hconn_E he0]
  obtain \<iota>E_raw SE_raw \<A>E_raw TE_raw where hbig_E: "top1_is_free_group_full_on
      (top1_fundamental_group_carrier E TE e0)
      (top1_fundamental_group_mul E TE e0)
      (top1_fundamental_group_id E TE e0)
      (top1_fundamental_group_invg E TE e0) \<iota>E_raw SE_raw \<and>
    (\<forall>A\<in>\<A>E_raw. A \<subseteq> E \<and> top1_is_arc_on A (subspace_topology E TE A)) \<and>
    \<Union>\<A>E_raw = E \<and>
    (\<forall>A\<in>\<A>E_raw. \<forall>B\<in>\<A>E_raw. A \<noteq> B \<longrightarrow>
         A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology E TE A)
       \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology E TE B)
       \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2) \<and>
    (\<forall>C. C \<subseteq> E \<longrightarrow>
         (closedin_on E TE C \<longleftrightarrow>
          (\<forall>A\<in>\<A>E_raw. closedin_on A (subspace_topology E TE A) (A \<inter> C)))) \<and>
    top1_is_tree_on TE_raw (subspace_topology E TE TE_raw) \<and> TE_raw \<subseteq> E \<and> e0 \<in> TE_raw \<and>
    (\<forall>A\<in>\<A>E_raw. A \<subseteq> TE_raw \<or>
         A \<inter> TE_raw \<subseteq> top1_arc_endpoints_on A (subspace_topology E TE A)) \<and>
    TE_raw = \<Union>{A \<in> \<A>E_raw. A \<subseteq> TE_raw} \<and>
    (\<forall>A\<in>{A \<in> \<A>E_raw. \<not> A \<subseteq> TE_raw}.
         \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology E TE A). e \<in> TE_raw) \<and>
    SE_raw = {A \<in> \<A>E_raw. \<not> A \<subseteq> TE_raw}"
    by (elim exE) (rule that, assumption)
  have hfree_E: "top1_is_free_group_full_on
      (top1_fundamental_group_carrier E TE e0)
      (top1_fundamental_group_mul E TE e0)
      (top1_fundamental_group_id E TE e0)
      (top1_fundamental_group_invg E TE e0) \<iota>E_raw SE_raw"
    using conjunct1[OF hbig_E] .
  \<comment> \<open>Extract individual conjuncts from hbig\\_E for later use.\<close>
  have h\<A>E_arcs: "\<forall>A\<in>\<A>E_raw. A \<subseteq> E \<and> top1_is_arc_on A (subspace_topology E TE A)"
    using hbig_E by (by5000 fast)
  have h\<A>E_cover: "\<Union>\<A>E_raw = E"
    using hbig_E by (by5000 fast)
  have h\<A>E_inter: "\<forall>A\<in>\<A>E_raw. \<forall>B\<in>\<A>E_raw. A \<noteq> B \<longrightarrow>
       A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology E TE A)
     \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology E TE B)
     \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
    using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF hbig_E]]]] .
  have h\<A>E_coh: "\<forall>C. C \<subseteq> E \<longrightarrow> (closedin_on E TE C \<longleftrightarrow>
      (\<forall>A\<in>\<A>E_raw. closedin_on A (subspace_topology E TE A) (A \<inter> C)))"
    using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF hbig_E]]]]] .
  \<comment> \<open>Extract remaining conjuncts level by level.\<close>
  note hrest5 = conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF hbig_E]]]]]
  have hTE_tree: "top1_is_tree_on TE_raw (subspace_topology E TE TE_raw)"
    using conjunct1[OF hrest5] .
  have hTE_sub: "TE_raw \<subseteq> E"
    using conjunct1[OF conjunct2[OF hrest5]] .
  have he0_TE: "e0 \<in> TE_raw"
    using conjunct1[OF conjunct2[OF conjunct2[OF hrest5]]] .
  have hTE_subgraph: "\<forall>A\<in>\<A>E_raw. A \<subseteq> TE_raw \<or>
       A \<inter> TE_raw \<subseteq> top1_arc_endpoints_on A (subspace_topology E TE A)"
    using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF hrest5]]]] .
  have hTE_coverage: "TE_raw = \<Union>{A \<in> \<A>E_raw. A \<subseteq> TE_raw}"
    using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF hrest5]]]]] .
  have hNTE_endpoints: "\<forall>A\<in>{A \<in> \<A>E_raw. \<not> A \<subseteq> TE_raw}.
       \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology E TE A). e \<in> TE_raw"
    using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF hrest5]]]]]] .
  have hSE_eq: "SE_raw = {A \<in> \<A>E_raw. \<not> A \<subseteq> TE_raw}"
    using conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF hrest5]]]]]] .
  \<comment> \<open>Step 6: Euler characteristic argument.
     From graph\\_pi1\\_free\\_weak on E: card(SE) = rank(\\<pi>\\_1(E)).
     From Euler formula (heuler\\_X): card(\\<A>w) - card(V\\_X) = card(Sw) - 1 = n.
     Lifted family: card(\\<A>\\_L) - card(V\\_L) = k * (card(\\<A>w) - card(V\\_X)) = kn.
     By Euler invariance (rank is independent of decomposition):
     rank(\\<pi>\\_1(E)) = card(\\<A>\\_L) - card(V\\_L) + 1 = kn + 1.
     By rank invariance: card(SE) = kn + 1.\<close>
  \<comment> \<open>Step 6a: From X data, derive card(\\<A>w) - card(V\\_X) = n.
     Sw = non-tree arcs, card(Sw) = n+1.
     Tree Euler: card(V\\_Tw) = card(tree\\_arcs) + 1.
     card(\\<A>w) = card(tree\\_arcs) + card(Sw).
     card(V\\_X) = card(V\\_Tw) = card(tree\\_arcs) + 1.
     So card(\\<A>w) - card(V\\_X) = card(Sw) - 1 = n.\<close>
  \<comment> \<open>Expert audit4 \\<S>3 Step 3: use rank + card V = card A + 1 form.
     For base X: (n+1) + card(V\\_X) = card(\\<A>w) + 1 gives \\<chi>\\_X = n.
     For lifted E: rank(E) + card(V\\_L) = card(\\<A>\\_L) + 1 gives rank = kn+1.\<close>
  \<comment> \<open>Step 6a: Rank formula for base graph X with supplied decomposition \\<A>w + Tw.\<close>
  \<comment> \<open>Decompose into: partition of \\<A>w + tree Euler + vertex equality.\<close>
  let ?tree_arcs = "{A \<in> \<A>w. A \<subseteq> Tw}"
  have hpart: "\<A>w = ?tree_arcs \<union> Sw" using hSw_eq by (by100 blast)
  have hpart_disj: "?tree_arcs \<inter> Sw = {}" using hSw_eq by (by100 blast)
  have htree_arcs_fin: "finite ?tree_arcs"
    by (rule finite_subset[of _ \<A>w]) (simp_all add: h\<A>w_fin)
  have hpart_card: "card \<A>w = card ?tree_arcs + card Sw"
    using card_Un_disjoint[OF htree_arcs_fin hSw_fin hpart_disj] hpart by simp
  \<comment> \<open>Tree Euler: card(V\\_Tw) = card(tree\\_arcs) + 1.
     This is the fundamental tree property, needing the leaf existence chain.\<close>
  have htree_euler: "card (top1_graph_vertex_set Tw (subspace_topology X TX Tw) ?tree_arcs)
      = card ?tree_arcs + 1"
  proof -
    \<comment> \<open>Apply tree\\_euler\\_number\\_one to Tw with tree arcs.
       Conditions: tree, arcs, cover, intersection, finite, nonempty, coherent.\<close>
    have hta_arcs: "\<forall>A\<in>?tree_arcs. A \<subseteq> Tw \<and> top1_is_arc_on A (subspace_topology Tw (subspace_topology X TX Tw) A)"
    proof (intro ballI conjI)
      fix A assume "A \<in> ?tree_arcs"
      hence "A \<subseteq> Tw" "A \<in> \<A>w" by (by100 blast)+
      show "A \<subseteq> Tw" using \<open>A \<subseteq> Tw\<close> .
      have "top1_is_arc_on A (subspace_topology X TX A)" using h\<A>w \<open>A \<in> \<A>w\<close> by (by100 blast)
      moreover have "subspace_topology Tw (subspace_topology X TX Tw) A = subspace_topology X TX A"
        by (rule subspace_topology_trans[OF \<open>A \<subseteq> Tw\<close>])
      ultimately show "top1_is_arc_on A (subspace_topology Tw (subspace_topology X TX Tw) A)" by simp
    qed
    have hta_inter: "\<forall>A\<in>?tree_arcs. \<forall>B\<in>?tree_arcs. A \<noteq> B \<longrightarrow>
         A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Tw (subspace_topology X TX Tw) A)
       \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Tw (subspace_topology X TX Tw) B)
       \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
    proof (intro ballI impI)
      fix A B assume "A \<in> ?tree_arcs" "B \<in> ?tree_arcs" "A \<noteq> B"
      have "A \<in> \<A>w" "B \<in> \<A>w" using \<open>A \<in> ?tree_arcs\<close> \<open>B \<in> ?tree_arcs\<close> by (by100 blast)+
      have "A \<subseteq> Tw" "B \<subseteq> Tw" using \<open>A \<in> ?tree_arcs\<close> \<open>B \<in> ?tree_arcs\<close> by (by100 blast)+
      from h\<A>w_inter[rule_format, OF \<open>A \<in> \<A>w\<close> \<open>B \<in> \<A>w\<close> \<open>A \<noteq> B\<close>]
      have "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)
          \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)
          \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" .
      moreover have "subspace_topology Tw (subspace_topology X TX Tw) A = subspace_topology X TX A"
        by (rule subspace_topology_trans[OF \<open>A \<subseteq> Tw\<close>])
      moreover have "subspace_topology Tw (subspace_topology X TX Tw) B = subspace_topology X TX B"
        by (rule subspace_topology_trans[OF \<open>B \<subseteq> Tw\<close>])
      ultimately show "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Tw (subspace_topology X TX Tw) A)
          \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Tw (subspace_topology X TX Tw) B)
          \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" by simp
    qed
    have hta_ne: "?tree_arcs \<noteq> {}"
    proof -
      have "x0 \<in> Tw" using hTw_x0 .
      have "x0 \<in> X" using hx0 .
      have "x0 \<in> \<Union>\<A>w" using h\<A>w_cover \<open>x0 \<in> X\<close> by simp
      then obtain A0 where "A0 \<in> \<A>w" "x0 \<in> A0" by (by100 blast)
      from hTw_subgraph[rule_format, OF \<open>A0 \<in> \<A>w\<close>]
      have "A0 \<subseteq> Tw \<or> A0 \<inter> Tw \<subseteq> top1_arc_endpoints_on A0 (subspace_topology X TX A0)" .
      thus ?thesis
      proof
        assume "A0 \<subseteq> Tw" thus ?thesis using \<open>A0 \<in> \<A>w\<close> by (by100 blast)
      next
        assume "A0 \<inter> Tw \<subseteq> top1_arc_endpoints_on A0 (subspace_topology X TX A0)"
        have "x0 \<in> A0 \<inter> Tw" using \<open>x0 \<in> A0\<close> \<open>x0 \<in> Tw\<close> by (by100 blast)
        \<comment> \<open>x0 is in the arc's endpoints but also in Tw. Arc has nonempty tree part.\<close>
        \<comment> \<open>Need: Tw = \\<Union>(tree\\_arcs), and x0 \\<in> Tw implies x0 \\<in> some tree arc.\<close>
        have "x0 \<in> \<Union>?tree_arcs" using hTw_coverage \<open>x0 \<in> Tw\<close> by simp
        thus ?thesis by (by100 blast)
      qed
    qed
    have hta_cover: "\<Union>?tree_arcs = Tw" using hTw_coverage by simp
    have hta_coh: "\<forall>C. C \<subseteq> Tw \<longrightarrow> (closedin_on Tw (subspace_topology X TX Tw) C \<longleftrightarrow>
        (\<forall>A\<in>?tree_arcs. closedin_on A (subspace_topology Tw (subspace_topology X TX Tw) A) (A \<inter> C)))"
    proof (intro allI impI)
      fix C assume "C \<subseteq> Tw"
      have hta_sub_Aw: "?tree_arcs \<subseteq> \<A>w" by (by100 blast)
      from subgraph_coherent_topology[OF hgraph_X h\<A>w h\<A>w_cover h\<A>w_inter h\<A>w_coh
          hta_sub_Aw hta_cover[symmetric], rule_format, OF \<open>C \<subseteq> Tw\<close>]
      have "closedin_on Tw (subspace_topology X TX Tw) C =
          (\<forall>A\<in>?tree_arcs. closedin_on A (subspace_topology X TX A) (A \<inter> C))" .
      \<comment> \<open>Convert sub(X,TX,A) to sub(Tw, sub(X,TX,Tw), A) via subspace\\_topology\\_trans.\<close>
      moreover have "\<forall>A\<in>?tree_arcs. closedin_on A (subspace_topology X TX A) (A \<inter> C) =
          closedin_on A (subspace_topology Tw (subspace_topology X TX Tw) A) (A \<inter> C)"
      proof (intro ballI)
        fix A assume "A \<in> ?tree_arcs"
        have "A \<subseteq> Tw" using \<open>A \<in> ?tree_arcs\<close> by (by100 blast)
        have "subspace_topology Tw (subspace_topology X TX Tw) A = subspace_topology X TX A"
          by (rule subspace_topology_trans[OF \<open>A \<subseteq> Tw\<close>])
        thus "closedin_on A (subspace_topology X TX A) (A \<inter> C) =
            closedin_on A (subspace_topology Tw (subspace_topology X TX Tw) A) (A \<inter> C)" by simp
      qed
      ultimately show "closedin_on Tw (subspace_topology X TX Tw) C =
          (\<forall>A\<in>?tree_arcs. closedin_on A (subspace_topology Tw (subspace_topology X TX Tw) A) (A \<inter> C))"
        by simp
    qed
    from tree_euler_number_one[OF hTw_tree hta_arcs hta_cover hta_inter htree_arcs_fin hta_ne hta_coh]
    show ?thesis .
  qed
  \<comment> \<open>Vertex equality: V\\_X = V\\_Tw (all endpoints of non-tree arcs are in Tw).\<close>
  have hV_eq: "top1_graph_vertex_set X TX \<A>w = top1_graph_vertex_set Tw (subspace_topology X TX Tw) ?tree_arcs"
  proof -
    \<comment> \<open>V\\_Tw uses sub(Tw, sub(X,TX,Tw), A) = sub(X,TX,A) for A \\<subseteq> Tw.\<close>
    have hV_Tw_eq: "top1_graph_vertex_set Tw (subspace_topology X TX Tw) ?tree_arcs
        = (\<Union>A\<in>?tree_arcs. top1_arc_endpoints_on A (subspace_topology X TX A))"
    proof -
      have "\<forall>A\<in>?tree_arcs. top1_arc_endpoints_on A (subspace_topology Tw (subspace_topology X TX Tw) A)
          = top1_arc_endpoints_on A (subspace_topology X TX A)"
      proof (intro ballI)
        fix A assume "A \<in> ?tree_arcs"
        hence "A \<subseteq> Tw" by (by100 blast)
        have "subspace_topology Tw (subspace_topology X TX Tw) A = subspace_topology X TX A"
          by (rule subspace_topology_trans[OF \<open>A \<subseteq> Tw\<close>])
        thus "top1_arc_endpoints_on A (subspace_topology Tw (subspace_topology X TX Tw) A)
            = top1_arc_endpoints_on A (subspace_topology X TX A)" by simp
      qed
      thus ?thesis unfolding top1_graph_vertex_set_def by simp
    qed
    have hV_X_eq: "top1_graph_vertex_set X TX \<A>w
        = (\<Union>A\<in>\<A>w. top1_arc_endpoints_on A (subspace_topology X TX A))"
      unfolding top1_graph_vertex_set_def by simp
    \<comment> \<open>\\<supseteq>: tree\\_arcs \\<subseteq> \\<A>w.\<close>
    have hVsup: "(\<Union>A\<in>?tree_arcs. top1_arc_endpoints_on A (subspace_topology X TX A))
        \<subseteq> (\<Union>A\<in>\<A>w. top1_arc_endpoints_on A (subspace_topology X TX A))"
      by (by100 blast)
    \<comment> \<open>\\<subseteq>: for non-tree arcs, endpoints are in Tw, hence in some tree arc's endpoints.\<close>
    have hVsub: "(\<Union>A\<in>\<A>w. top1_arc_endpoints_on A (subspace_topology X TX A))
        \<subseteq> (\<Union>A\<in>?tree_arcs. top1_arc_endpoints_on A (subspace_topology X TX A))"
    proof (intro UN_least subsetI)
      fix A v assume hA: "A \<in> \<A>w" and hv: "v \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
      show "v \<in> (\<Union>A\<in>?tree_arcs. top1_arc_endpoints_on A (subspace_topology X TX A))"
      proof (cases "A \<subseteq> Tw")
        case True
        hence "A \<in> ?tree_arcs" using hA by (by100 blast)
        thus ?thesis using hv by (by100 blast)
      next
        case False
        \<comment> \<open>A is a non-tree arc. v is an endpoint of A. v \\<in> Tw (from hNTw\\_endpoints).\<close>
        have "A \<in> Sw" using hA False hSw_eq by (by100 blast)
        have "v \<in> Tw" using hNTw_endpoints hA False hv hSw_eq by (by100 blast)
        \<comment> \<open>v \\<in> Tw = \\<Union>(tree\\_arcs). So v \\<in> some tree arc B.\<close>
        have "v \<in> \<Union>?tree_arcs" using \<open>v \<in> Tw\<close> hTw_coverage by simp
        then obtain B where "B \<in> ?tree_arcs" "v \<in> B" by (by100 blast)
        have "B \<in> \<A>w" using \<open>B \<in> ?tree_arcs\<close> by (by100 blast)
        \<comment> \<open>v \\<in> A \\<inter> B. A \\<ne> B (A non-tree, B tree). So v \\<in> endpoints(B).\<close>
        have "A \<noteq> B" using False \<open>B \<in> ?tree_arcs\<close> by (by100 blast)
        have "v \<in> A" using hv unfolding top1_arc_endpoints_on_def by (by100 blast)
        have "v \<in> A \<inter> B" using \<open>v \<in> A\<close> \<open>v \<in> B\<close> by (by100 blast)
        have "A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)"
          using h\<A>w_inter[rule_format, OF hA \<open>B \<in> \<A>w\<close> \<open>A \<noteq> B\<close>] by (by100 blast)
        hence "v \<in> top1_arc_endpoints_on B (subspace_topology X TX B)"
          using \<open>v \<in> A \<inter> B\<close> by (by100 blast)
        thus ?thesis using \<open>B \<in> ?tree_arcs\<close> by (by100 blast)
      qed
    qed
    from hVsup hVsub have "(\<Union>A\<in>\<A>w. top1_arc_endpoints_on A (subspace_topology X TX A))
        = (\<Union>A\<in>?tree_arcs. top1_arc_endpoints_on A (subspace_topology X TX A))"
      by (by100 blast)
    thus ?thesis using hV_Tw_eq hV_X_eq by simp
  qed
  have hrank_X_formula: "int (card Sw) + int (card (top1_graph_vertex_set X TX \<A>w))
      = int (card \<A>w) + 1"
  proof -
    have "card (top1_graph_vertex_set X TX \<A>w) = card ?tree_arcs + 1"
      using htree_euler hV_eq by simp
    thus ?thesis using hpart_card by linarith
  qed
  have hchi_X: "int (card \<A>w) - int (card (top1_graph_vertex_set X TX \<A>w)) = int n"
    using hrank_X_formula hSw_card by linarith
  \<comment> \<open>Step 6b: Multiplicity gives lifted Euler.\<close>
  have hchi_L: "int (card ?\<A>_L) - int (card (top1_graph_vertex_set E TE ?\<A>_L)) = int k * int n"
  proof -
    have "int (card ?\<A>_L) = int k * int (card \<A>w)" using h\<A>_L_card by simp
    moreover have "int (card (top1_graph_vertex_set E TE ?\<A>_L)) = int k * int (card (top1_graph_vertex_set X TX \<A>w))"
      using hV_L_card by simp
    ultimately show ?thesis using hchi_X by (simp add: algebra_simps)
  qed
  \<comment> \<open>Step 6c: Rank formula for covering graph E with supplied decomposition \\<A>\\_L.\<close>
  have hrank_E_formula: "int (card SE_raw) + int (card (top1_graph_vertex_set E TE ?\<A>_L))
      = int (card ?\<A>_L) + 1"
  proof -
    \<comment> \<open>From \\<A>E\\_raw: rank + V\\_E\\_raw = E\\_raw + 1 (from tree Euler via sorry #1).\<close>
    have hrank_E_raw: "int (card SE_raw) + int (card (top1_graph_vertex_set E TE \<A>E_raw))
        = int (card \<A>E_raw) + 1"
    proof -
      \<comment> \<open>Same pattern as hrank\\_X\\_formula: partition + tree Euler + V\\_eq.\<close>
      let ?tree_arcs_E = "{A \<in> \<A>E_raw. A \<subseteq> TE_raw}"
      have hpartE: "\<A>E_raw = ?tree_arcs_E \<union> SE_raw" using hSE_eq by (by100 blast)
      have hpartE_disj: "?tree_arcs_E \<inter> SE_raw = {}" using hSE_eq by (by100 blast)
      have h\<A>E_fin: "finite \<A>E_raw"
      proof -
        have hTX_top: "is_topology_on X TX"
          using hgraph_X unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
        have hTE_top: "is_topology_on E TE"
          using hstrict_E unfolding is_topology_on_strict_def by (by100 blast)
        have hE_compact: "top1_compact_on E TE"
          by (rule finite_covering_compact[OF hcov hcompact_X hTX_top hTE_top hfiber hk])
        from compact_graph_finite_arcs[OF hE_graph hE_compact h\<A>E_arcs h\<A>E_cover h\<A>E_inter h\<A>E_coh]
        show ?thesis .
      qed
      have htreeE_fin: "finite ?tree_arcs_E"
        by (rule finite_subset[of _ \<A>E_raw]) (simp_all add: h\<A>E_fin)
      have hSE_fin: "finite SE_raw"
      proof -
        have "SE_raw \<subseteq> \<A>E_raw" using hSE_eq by (by100 blast)
        from finite_subset[OF this h\<A>E_fin] show ?thesis .
      qed
      have hpartE_card: "card \<A>E_raw = card ?tree_arcs_E + card SE_raw"
        using card_Un_disjoint[OF htreeE_fin hSE_fin hpartE_disj] hpartE by simp
      \<comment> \<open>Tree Euler for TE\\_raw (flows through sorry #1 via tree\\_euler\\_number\\_one).\<close>
      have htreeE_euler: "card (top1_graph_vertex_set TE_raw (subspace_topology E TE TE_raw) ?tree_arcs_E)
          = card ?tree_arcs_E + 1"
      proof -
        have hta_cover_E: "\<Union>?tree_arcs_E = TE_raw" using hTE_coverage by simp
        have hta_arcs_E: "\<forall>A\<in>?tree_arcs_E. A \<subseteq> TE_raw \<and> top1_is_arc_on A (subspace_topology TE_raw (subspace_topology E TE TE_raw) A)"
        proof (intro ballI conjI)
          fix A assume "A \<in> ?tree_arcs_E"
          show "A \<subseteq> TE_raw" using \<open>A \<in> ?tree_arcs_E\<close> by (by100 blast)
          have "A \<in> \<A>E_raw" using \<open>A \<in> ?tree_arcs_E\<close> by (by100 blast)
          have "top1_is_arc_on A (subspace_topology E TE A)" using h\<A>E_arcs \<open>A \<in> \<A>E_raw\<close> by (by100 blast)
          moreover have "subspace_topology TE_raw (subspace_topology E TE TE_raw) A = subspace_topology E TE A"
            by (rule subspace_topology_trans) (use \<open>A \<in> ?tree_arcs_E\<close> in blast)
          ultimately show "top1_is_arc_on A (subspace_topology TE_raw (subspace_topology E TE TE_raw) A)" by simp
        qed
        have hta_inter_E: "\<forall>A\<in>?tree_arcs_E. \<forall>B\<in>?tree_arcs_E. A \<noteq> B \<longrightarrow>
             A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology TE_raw (subspace_topology E TE TE_raw) A)
           \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology TE_raw (subspace_topology E TE TE_raw) B)
           \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
        proof (intro ballI impI)
          fix A B assume "A \<in> ?tree_arcs_E" "B \<in> ?tree_arcs_E" "A \<noteq> B"
          have "A \<in> \<A>E_raw" "B \<in> \<A>E_raw" using \<open>A \<in> ?tree_arcs_E\<close> \<open>B \<in> ?tree_arcs_E\<close> by (by100 blast)+
          from h\<A>E_inter[rule_format, OF \<open>A \<in> \<A>E_raw\<close> \<open>B \<in> \<A>E_raw\<close> \<open>A \<noteq> B\<close>]
          have h_raw: "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology E TE A)
              \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology E TE B)
              \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" .
          have "subspace_topology TE_raw (subspace_topology E TE TE_raw) A = subspace_topology E TE A"
            by (rule subspace_topology_trans) (use \<open>A \<in> ?tree_arcs_E\<close> in blast)
          moreover have "subspace_topology TE_raw (subspace_topology E TE TE_raw) B = subspace_topology E TE B"
            by (rule subspace_topology_trans) (use \<open>B \<in> ?tree_arcs_E\<close> in blast)
          ultimately show "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology TE_raw (subspace_topology E TE TE_raw) A)
              \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology TE_raw (subspace_topology E TE TE_raw) B)
              \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" using h_raw by simp
        qed
        have hta_ne_E: "?tree_arcs_E \<noteq> {}"
        proof -
          have "e0 \<in> TE_raw" using he0_TE .
          have "e0 \<in> \<Union>?tree_arcs_E" using hTE_coverage \<open>e0 \<in> TE_raw\<close> by simp
          thus ?thesis by (by100 blast)
        qed
        have hta_coh_E: "\<forall>C. C \<subseteq> TE_raw \<longrightarrow> (closedin_on TE_raw (subspace_topology E TE TE_raw) C \<longleftrightarrow>
            (\<forall>A\<in>?tree_arcs_E. closedin_on A (subspace_topology TE_raw (subspace_topology E TE TE_raw) A) (A \<inter> C)))"
        proof (intro allI impI)
          fix C assume "C \<subseteq> TE_raw"
          have "{A \<in> \<A>E_raw. A \<subseteq> TE_raw} \<subseteq> \<A>E_raw" by (by100 blast)
          from subgraph_coherent_topology[OF hE_graph h\<A>E_arcs h\<A>E_cover h\<A>E_inter h\<A>E_coh
              this hta_cover_E[symmetric], rule_format, OF \<open>C \<subseteq> TE_raw\<close>]
          have "closedin_on TE_raw (subspace_topology E TE TE_raw) C =
              (\<forall>A\<in>?tree_arcs_E. closedin_on A (subspace_topology E TE A) (A \<inter> C))" .
          moreover have "\<forall>A\<in>?tree_arcs_E. closedin_on A (subspace_topology E TE A) (A \<inter> C) =
              closedin_on A (subspace_topology TE_raw (subspace_topology E TE TE_raw) A) (A \<inter> C)"
          proof (intro ballI)
            fix A assume "A \<in> ?tree_arcs_E"
            have "subspace_topology TE_raw (subspace_topology E TE TE_raw) A = subspace_topology E TE A"
              by (rule subspace_topology_trans) (use \<open>A \<in> ?tree_arcs_E\<close> in blast)
            thus "closedin_on A (subspace_topology E TE A) (A \<inter> C) =
                closedin_on A (subspace_topology TE_raw (subspace_topology E TE TE_raw) A) (A \<inter> C)" by simp
          qed
          ultimately show "closedin_on TE_raw (subspace_topology E TE TE_raw) C =
              (\<forall>A\<in>?tree_arcs_E. closedin_on A (subspace_topology TE_raw (subspace_topology E TE TE_raw) A) (A \<inter> C))"
            by simp
        qed
        from tree_euler_number_one[OF hTE_tree hta_arcs_E hta_cover_E hta_inter_E htreeE_fin hta_ne_E hta_coh_E]
        show ?thesis .
      qed
      \<comment> \<open>Vertex equality: V(\\<A>E\\_raw) = V(tree\\_arcs\\_E).\<close>
      have hVE_eq: "top1_graph_vertex_set E TE \<A>E_raw =
          top1_graph_vertex_set TE_raw (subspace_topology E TE TE_raw) ?tree_arcs_E"
      proof -
        have hV_TE_eq: "top1_graph_vertex_set TE_raw (subspace_topology E TE TE_raw) ?tree_arcs_E
            = (\<Union>A\<in>?tree_arcs_E. top1_arc_endpoints_on A (subspace_topology E TE A))"
        proof -
          have "\<forall>A\<in>?tree_arcs_E. top1_arc_endpoints_on A (subspace_topology TE_raw (subspace_topology E TE TE_raw) A)
              = top1_arc_endpoints_on A (subspace_topology E TE A)"
          proof (intro ballI)
            fix A assume "A \<in> ?tree_arcs_E"
            have "subspace_topology TE_raw (subspace_topology E TE TE_raw) A = subspace_topology E TE A"
              by (rule subspace_topology_trans) (use \<open>A \<in> ?tree_arcs_E\<close> in blast)
            thus "top1_arc_endpoints_on A (subspace_topology TE_raw (subspace_topology E TE TE_raw) A)
                = top1_arc_endpoints_on A (subspace_topology E TE A)" by simp
          qed
          thus ?thesis unfolding top1_graph_vertex_set_def by simp
        qed
        have hV_E_eq: "top1_graph_vertex_set E TE \<A>E_raw
            = (\<Union>A\<in>\<A>E_raw. top1_arc_endpoints_on A (subspace_topology E TE A))"
          unfolding top1_graph_vertex_set_def by simp
        have hVsupE: "(\<Union>A\<in>?tree_arcs_E. top1_arc_endpoints_on A (subspace_topology E TE A))
            \<subseteq> (\<Union>A\<in>\<A>E_raw. top1_arc_endpoints_on A (subspace_topology E TE A))"
          by (by100 blast)
        have hVsubE: "(\<Union>A\<in>\<A>E_raw. top1_arc_endpoints_on A (subspace_topology E TE A))
            \<subseteq> (\<Union>A\<in>?tree_arcs_E. top1_arc_endpoints_on A (subspace_topology E TE A))"
        proof (intro UN_least subsetI)
          fix A v assume hA: "A \<in> \<A>E_raw" and hv: "v \<in> top1_arc_endpoints_on A (subspace_topology E TE A)"
          show "v \<in> (\<Union>A\<in>?tree_arcs_E. top1_arc_endpoints_on A (subspace_topology E TE A))"
          proof (cases "A \<subseteq> TE_raw")
            case True thus ?thesis using hA hv by (by100 blast)
          next
            case False
            have "v \<in> TE_raw" using hNTE_endpoints hA False hv hSE_eq by (by100 blast)
            have "v \<in> \<Union>?tree_arcs_E" using \<open>v \<in> TE_raw\<close> hTE_coverage by simp
            then obtain B where "B \<in> ?tree_arcs_E" "v \<in> B" by (by100 blast)
            have "B \<in> \<A>E_raw" using \<open>B \<in> ?tree_arcs_E\<close> by (by100 blast)
            have "A \<noteq> B" using False \<open>B \<in> ?tree_arcs_E\<close> by (by100 blast)
            have "v \<in> A" using hv unfolding top1_arc_endpoints_on_def by (by100 blast)
            have "v \<in> A \<inter> B" using \<open>v \<in> A\<close> \<open>v \<in> B\<close> by (by100 blast)
            have "A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology E TE B)"
              using h\<A>E_inter[rule_format, OF hA \<open>B \<in> \<A>E_raw\<close> \<open>A \<noteq> B\<close>] by (by100 blast)
            hence "v \<in> top1_arc_endpoints_on B (subspace_topology E TE B)"
              using \<open>v \<in> A \<inter> B\<close> by (by100 blast)
            thus ?thesis using \<open>B \<in> ?tree_arcs_E\<close> by (by100 blast)
          qed
        qed
        from hVsupE hVsubE have "(\<Union>A\<in>\<A>E_raw. top1_arc_endpoints_on A (subspace_topology E TE A))
            = (\<Union>A\<in>?tree_arcs_E. top1_arc_endpoints_on A (subspace_topology E TE A))"
          by (by100 blast)
        thus ?thesis using hV_TE_eq hV_E_eq by simp
      qed
      show ?thesis
      proof -
        have "card (top1_graph_vertex_set E TE \<A>E_raw) = card ?tree_arcs_E + 1"
          using htreeE_euler hVE_eq by simp
        thus ?thesis using hpartE_card by linarith
      qed
    qed
    \<comment> \<open>Euler invariance: V\\_L - \\<A>\\_L = V\\_E\\_raw - \\<A>E\\_raw.\<close>
    have heuler_inv: "int (card (top1_graph_vertex_set E TE ?\<A>_L)) - int (card ?\<A>_L)
        = int (card (top1_graph_vertex_set E TE \<A>E_raw)) - int (card \<A>E_raw)"
    proof -
      have h\<A>E_arcs: "\<forall>A\<in>\<A>E_raw. A \<subseteq> E \<and> top1_is_arc_on A (subspace_topology E TE A)"
        using conjunct1[OF conjunct2[OF hbig_E]] .
      have h\<A>E_cover: "\<Union>\<A>E_raw = E"
        using conjunct1[OF conjunct2[OF conjunct2[OF hbig_E]]] .
      have h\<A>E_inter: "\<forall>A\<in>\<A>E_raw. \<forall>B\<in>\<A>E_raw. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology E TE A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology E TE B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
        using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF hbig_E]]]] .
      \<comment> \<open>Need: \\<A>\\_L satisfies the graph decomposition conditions.\<close>
      \<comment> \<open>Extract ANY valid decomposition from hE\\_graph to use in Euler invariance.
         We use \\<A>E\\_raw itself (which is already extracted from graph\\_pi1\\_free\\_weak).\<close>
      \<comment> \<open>Actually, graph\\_euler\\_invariance needs TWO decompositions. We have \\<A>E\\_raw.
         For the second: use \\<A>E\\_raw again (trivially gives V - E = V - E).
         BUT we need V\\_L - card(\\<A>\\_L) = V\\_E\\_raw - card(\\<A>E\\_raw).
         This requires \\<A>\\_L as a valid decomposition, which needs the conditions below.
         ALTERNATIVELY: bypass graph\\_euler\\_invariance and prove hrank\\_E\\_formula differently.\<close>
      \<comment> \<open>Simpler approach: since we need V\\_L - card(\\<A>\\_L) = V\\_E\\_raw - card(\\<A>E\\_raw),
         and we have V\\_L = k * V\\_X and card(\\<A>\\_L) = k * card(\\<A>w), we need:
         k * V\\_X - k * card(\\<A>w) = V\\_E\\_raw - card(\\<A>E\\_raw).
         I.e., k * (V\\_X - card(\\<A>w)) = V\\_E\\_raw - card(\\<A>E\\_raw).
         The LHS = k * (-n) = -kn (from hchi\\_X: card(\\<A>w) - V\\_X = n).
         So we need: V\\_E\\_raw - card(\\<A>E\\_raw) = -kn.
         From hrank\\_E\\_raw: card(SE\\_raw) + V\\_E\\_raw = card(\\<A>E\\_raw) + 1.
         So V\\_E\\_raw - card(\\<A>E\\_raw) = 1 - card(SE\\_raw).
         Need: 1 - card(SE\\_raw) = -kn, i.e., card(SE\\_raw) = kn + 1.
         This IS what we're trying to prove! Circular.\<close>
      \<comment> \<open>Previous approach: extracted \\<A>\\_G from hE\\_graph, but couldn't identify with \\<A>\\_L.
         Current approach: prove \\<A>\\_L conditions directly, use Euler invariance.\<close>
      have hE_compact: "top1_compact_on E TE"
      proof -
        have hTX_top: "is_topology_on X TX"
          using hgraph_X unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
        have hTE_top: "is_topology_on E TE"
          using hstrict_E unfolding is_topology_on_strict_def by (by100 blast)
        from finite_covering_compact[OF hcov hcompact_X hTX_top hTE_top hfiber hk]
        show ?thesis .
      qed
      have h\<A>E_fin: "finite \<A>E_raw"
      proof -
        have h\<A>E_coh: "\<forall>C. C \<subseteq> E \<longrightarrow> (closedin_on E TE C \<longleftrightarrow>
            (\<forall>A\<in>\<A>E_raw. closedin_on A (subspace_topology E TE A) (A \<inter> C)))"
          using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF hbig_E]]]]] .
        from compact_graph_finite_arcs[OF hE_graph hE_compact h\<A>E_arcs h\<A>E_cover h\<A>E_inter h\<A>E_coh]
        show ?thesis .
      qed
      \<comment> \<open>Extract covering interface clauses (moved up for use in \\<A>\\_L proofs).\<close>
      note hclause1 = h_lifted[unfolded top1_covering_lifted_arc_family_on_def, THEN conjunct1]
      note hclause2 = h_lifted[unfolded top1_covering_lifted_arc_family_on_def,
          THEN conjunct2, THEN conjunct1]
      note hclause3 = h_lifted[unfolded top1_covering_lifted_arc_family_on_def,
          THEN conjunct2, THEN conjunct2]
      \<comment> \<open>Prove \\<A>\\_L graph conditions, then apply Euler invariance directly to \\<A>\\_L and \\<A>E\\_raw.\<close>
      have hE_haus: "is_hausdorff_on E TE"
      proof -
        have "top1_is_graph_on E TE"
          by (rule Theorem_83_4_covering_of_graph_is_graph[OF hgraph_X hcov hstrict_E])
        thus ?thesis unfolding top1_is_graph_on_def by (by100 blast)
      qed
      have hTE_top: "is_topology_on E TE"
        using hstrict_E unfolding is_topology_on_strict_def by (by100 blast)
      have hTX_top: "is_topology_on X TX"
        using hgraph_X unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
      have hX_haus: "is_hausdorff_on X TX"
        using hgraph_X unfolding top1_is_graph_on_def by (by100 blast)
      have hp_cont: "top1_continuous_map_on E TE X TX p"
        by (rule top1_covering_map_on_continuous[OF hcov])
      have h\<A>L_arcs: "\<forall>B\<in>?\<A>_L. B \<subseteq> E \<and> top1_is_arc_on B (subspace_topology E TE B)"
      proof (intro ballI conjI)
        fix B assume hBL: "B \<in> ?\<A>_L"
        then obtain A0 where hA0: "A0 \<in> \<A>w" and hB_comp: "top1_max_conn_comp {e \<in> E. p e \<in> A0}
            (subspace_topology E TE {e \<in> E. p e \<in> A0}) B" by (by100 blast)
        have hB_sub_pre: "B \<subseteq> {e \<in> E. p e \<in> A0}" using max_conn_comp_sub[OF hB_comp] .
        show "B \<subseteq> E" using hB_sub_pre by (by100 blast)
        \<comment> \<open>From Clause 1: p\`B = A0', inj\\_on p B, where A0' = A0.\<close>
        from hclause1[rule_format, OF hBL]
        obtain A0' where hA0': "A0' \<in> \<A>w" and hB_sub': "B \<subseteq> {e \<in> E. p e \<in> A0'}"
            and hpB: "p ` B = A0'" and hinj: "inj_on p B"
            and hep: "p ` (top1_arc_endpoints_on B (subspace_topology E TE B))
              = top1_arc_endpoints_on A0' (subspace_topology X TX A0')"
          by (by100 auto)
        \<comment> \<open>A0' is an arc.\<close>
        have hA0'_arc: "top1_is_arc_on A0' (subspace_topology X TX A0')"
          using h\<A>w hA0' by (by100 blast)
        have hA0'_sub: "A0' \<subseteq> X" using h\<A>w hA0' by (by100 blast)
        \<comment> \<open>A0' is compact (homeomorphic to [0,1]).\<close>
        have hA0'_compact: "top1_compact_on A0' (subspace_topology X TX A0')"
        proof -
          obtain h0 where hh0: "top1_homeomorphism_on I_set I_top A0' (subspace_topology X TX A0') h0"
            using hA0'_arc unfolding top1_is_arc_on_def by (by100 blast)
          have hI_compact: "top1_compact_on I_set I_top"
            unfolding top1_unit_interval_def top1_unit_interval_topology_def
            using Theorem_27_1[of "0::real" 1] by (by100 simp)
          have hh0_cont: "top1_continuous_map_on I_set I_top A0' (subspace_topology X TX A0') h0"
            using hh0 unfolding top1_homeomorphism_on_def by (by100 blast)
          have hh0_surj: "h0 ` I_set = A0'"
            using hh0 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
          have hA0'_top: "is_topology_on A0' (subspace_topology X TX A0')"
            by (rule subspace_topology_is_topology_on[OF hTX_top hA0'_sub])
          from top1_compact_on_continuous_image[OF hI_compact hA0'_top hh0_cont]
          have "top1_compact_on (h0 ` I_set) (subspace_topology A0' (subspace_topology X TX A0') (h0 ` I_set))" .
          hence "top1_compact_on A0' (subspace_topology A0' (subspace_topology X TX A0') A0')"
            using hh0_surj by simp
          moreover have "subspace_topology A0' (subspace_topology X TX A0') A0'
              = subspace_topology X TX A0'"
          proof (rule subspace_topology_self)
            have "is_topology_on_strict X TX"
              using hgraph_X unfolding top1_is_graph_on_def by (by100 blast)
            from subspace_topology_is_strict[OF this hA0'_sub]
            show "\<forall>U\<in>subspace_topology X TX A0'. U \<subseteq> A0'"
              unfolding is_topology_on_strict_def by (by100 blast)
          qed
          ultimately show ?thesis by simp
        qed
        \<comment> \<open>A0 is also an arc and compact (for closedness of preimage).\<close>
        have hA0_arc: "top1_is_arc_on A0 (subspace_topology X TX A0)"
          using h\<A>w hA0 by (by100 blast)
        have hA0_sub: "A0 \<subseteq> X" using h\<A>w hA0 by (by100 blast)
        have hA0_compact: "top1_compact_on A0 (subspace_topology X TX A0)"
        proof -
          obtain h0 where "top1_homeomorphism_on I_set I_top A0 (subspace_topology X TX A0) h0"
            using hA0_arc unfolding top1_is_arc_on_def by (by100 blast)
          have hI_compact: "top1_compact_on I_set I_top"
            unfolding top1_unit_interval_def top1_unit_interval_topology_def
            using Theorem_27_1[of "0::real" 1] by (by100 simp)
          have hA0_top: "is_topology_on A0 (subspace_topology X TX A0)"
            by (rule subspace_topology_is_topology_on[OF hTX_top hA0_sub])
          have hh0_cont: "top1_continuous_map_on I_set I_top A0 (subspace_topology X TX A0) h0"
            using \<open>top1_homeomorphism_on I_set I_top A0 _ h0\<close>
            unfolding top1_homeomorphism_on_def by (by100 blast)
          have hh0_surj: "h0 ` I_set = A0"
            using \<open>top1_homeomorphism_on I_set I_top A0 _ h0\<close>
            unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
          from top1_compact_on_continuous_image[OF hI_compact hA0_top hh0_cont]
          have "top1_compact_on (h0 ` I_set) (subspace_topology A0 (subspace_topology X TX A0) (h0 ` I_set))" .
          hence "top1_compact_on A0 (subspace_topology A0 (subspace_topology X TX A0) A0)"
            using hh0_surj by simp
          moreover have "subspace_topology A0 (subspace_topology X TX A0) A0
              = subspace_topology X TX A0"
          proof (rule subspace_topology_self)
            have "is_topology_on_strict X TX"
              using hgraph_X unfolding top1_is_graph_on_def by (by100 blast)
            from subspace_topology_is_strict[OF this hA0_sub]
            show "\<forall>U\<in>subspace_topology X TX A0. U \<subseteq> A0"
              unfolding is_topology_on_strict_def by (by100 blast)
          qed
          ultimately show ?thesis by simp
        qed
        have hA0_closed: "closedin_on X TX A0"
          by (rule Theorem_26_3[OF hX_haus hA0_sub hA0_compact])
        \<comment> \<open>Preimage of A0 is closed in E.\<close>
        let ?pre = "{e \<in> E. p e \<in> A0}"
        have hpre_closed: "closedin_on E TE ?pre"
          by (rule continuous_preimage_closedin[OF hTE_top hTX_top hp_cont hA0_closed])
        have hpre_compact: "top1_compact_on ?pre (subspace_topology E TE ?pre)"
          by (rule Theorem_26_2[OF hE_compact hpre_closed])
        \<comment> \<open>B is closed in ?pre (connected component is closed).
           Proof: closure of B in ?pre is connected (Theorem 23.4),
           contains B, is contained in ?pre. By maximality of B: closure = B.\<close>
        have hpre_top: "is_topology_on ?pre (subspace_topology E TE ?pre)"
          by (rule subspace_topology_is_topology_on[OF hTE_top]) (by100 blast)
        have hpre_sub: "?pre \<subseteq> E" by (by100 blast)
        \<comment> \<open>B is connected in the subspace topology of ?pre.\<close>
        have hB_conn_pre: "top1_connected_on B (subspace_topology E TE B)"
        proof -
          have "top1_connected_on B (subspace_topology ?pre (subspace_topology E TE ?pre) B)"
            using hB_comp unfolding top1_max_conn_comp_def by (by100 blast)
          moreover have "subspace_topology ?pre (subspace_topology E TE ?pre) B
              = subspace_topology E TE B"
            by (rule subspace_topology_trans[OF hB_sub_pre])
          ultimately show ?thesis by simp
        qed
        have hB_closed_pre: "closedin_on ?pre (subspace_topology E TE ?pre) B"
        proof -
          let ?TS = "subspace_topology E TE ?pre"
          \<comment> \<open>closure of B in ?pre.\<close>
          have hcl_sub: "closure_on ?pre ?TS B \<subseteq> ?pre"
            by (rule closure_on_subset_carrier[OF hpre_top hB_sub_pre])
          have hcl_sup: "B \<subseteq> closure_on ?pre ?TS B"
            by (rule subset_closure_on)
          \<comment> \<open>closure of connected is connected.\<close>
          have hcl_conn: "top1_connected_on (closure_on ?pre ?TS B)
              (subspace_topology ?pre ?TS (closure_on ?pre ?TS B))"
            by (rule closure_of_connected_is_connected[OF hpre_top hB_sub_pre
                hB_comp[unfolded top1_max_conn_comp_def, THEN conjunct2, THEN conjunct2,
                    THEN conjunct1]])
          \<comment> \<open>By maximality of B as connected component: closure = B.\<close>
          have "closure_on ?pre ?TS B = B"
          proof -
            have hmax: "\<forall>C. C \<supseteq> B \<longrightarrow> C \<subseteq> ?pre \<longrightarrow>
                top1_connected_on C (subspace_topology ?pre ?TS C) \<longrightarrow> C = B"
              using hB_comp unfolding top1_max_conn_comp_def by (by100 blast)
            from hmax[rule_format, OF hcl_sup hcl_sub hcl_conn]
            show ?thesis .
          qed
          hence "closure_on ?pre ?TS B \<subseteq> B" by simp
          \<comment> \<open>closure \\<subseteq> B and B closed in ?pre.\<close>
          have "closedin_on ?pre ?TS (closure_on ?pre ?TS B)"
            by (rule closure_on_closed[OF hpre_top hB_sub_pre])
          thus ?thesis using \<open>closure_on ?pre ?TS B = B\<close> by simp
        qed
        \<comment> \<open>B is closed in E (transitivity: closed in closed = closed).\<close>
        have hB_closed_E: "closedin_on E TE B"
          by (rule Theorem_17_3[OF hTE_top hpre_closed hB_closed_pre])
        \<comment> \<open>B is compact (closed in compact E).\<close>
        have hB_compact: "top1_compact_on B (subspace_topology E TE B)"
          by (rule Theorem_26_2[OF hE_compact hB_closed_E])
        \<comment> \<open>B subspace is Hausdorff.\<close>
        have hB_haus: "is_hausdorff_on B (subspace_topology E TE B)"
          using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>B \<subseteq> E\<close> hE_haus by (by100 blast)
        have hB_strict: "is_topology_on_strict B (subspace_topology E TE B)"
          by (rule subspace_topology_is_strict[OF hstrict_E \<open>B \<subseteq> E\<close>])
        have hB_top: "is_topology_on B (subspace_topology E TE B)"
          using hB_strict unfolding is_topology_on_strict_def by (by100 blast)
        have hA0'_top: "is_topology_on A0' (subspace_topology X TX A0')"
          by (rule subspace_topology_is_topology_on[OF hTX_top hA0'_sub])
        have hA0'_haus: "is_hausdorff_on A0' (subspace_topology X TX A0')"
          using conjunct2[OF conjunct2[OF Theorem_17_11]] hA0'_sub hX_haus by (by100 blast)
        \<comment> \<open>p|B: B \\<rightarrow> A0' is continuous bijection.\<close>
        have hp_cont_B: "top1_continuous_map_on B (subspace_topology E TE B)
            A0' (subspace_topology X TX A0') p"
        proof -
          \<comment> \<open>Step 1: restrict domain to B.\<close>
          have hp_cont_B_X: "top1_continuous_map_on B (subspace_topology E TE B) X TX p"
            using restrict_domain[OF hTE_top hTX_top hTX_top, rule_format,
                of p B] hp_cont \<open>B \<subseteq> E\<close> by (by100 blast)
          \<comment> \<open>Step 2: restrict range to A0'.\<close>
          have "p ` B \<subseteq> A0'" using hpB by (by100 blast)
          from restrict_range[OF hB_top hTX_top hA0'_top, rule_format, of p]
              hp_cont_B_X hA0'_sub \<open>p ` B \<subseteq> A0'\<close>
          show ?thesis by (by100 blast)
        qed
        have hp_bij_B: "bij_betw p B A0'"
          unfolding bij_betw_def using hinj hpB by (by100 blast)
        from Theorem_26_6[OF hB_top hA0'_top hB_compact hA0'_haus hp_cont_B hp_bij_B]
        have hp_homeo: "top1_homeomorphism_on B (subspace_topology E TE B)
            A0' (subspace_topology X TX A0') p" .
        \<comment> \<open>A0' is an arc: get homeomorphism g: [0,1] \\<rightarrow> A0'.\<close>
        obtain g where hg: "top1_homeomorphism_on I_set I_top A0' (subspace_topology X TX A0') g"
          using hA0'_arc unfolding top1_is_arc_on_def by (by100 blast)
        \<comment> \<open>Inverse of p gives continuous map from A0' to B.\<close>
        have hinv_cont: "top1_continuous_map_on A0' (subspace_topology X TX A0')
            B (subspace_topology E TE B) (inv_into B p)"
          using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        \<comment> \<open>Compose: (inv\\_into B p) \\<circ> g: [0,1] \\<rightarrow> B is continuous.\<close>
        have hg_cont: "top1_continuous_map_on I_set I_top A0' (subspace_topology X TX A0') g"
          using hg unfolding top1_homeomorphism_on_def by (by100 blast)
        have hcomp_cont: "top1_continuous_map_on I_set I_top B (subspace_topology E TE B)
            ((inv_into B p) \<circ> g)"
          by (rule top1_continuous_map_on_comp[OF hg_cont hinv_cont])
        have hg_bij: "bij_betw g I_set A0'"
          using hg unfolding top1_homeomorphism_on_def by (by100 blast)
        have hinv_bij: "bij_betw (inv_into B p) A0' B"
          using hp_bij_B by (rule bij_betw_inv_into)
        have hcomp_bij: "bij_betw ((inv_into B p) \<circ> g) I_set B"
          by (rule bij_betw_trans[OF hg_bij hinv_bij])
        have hI_compact: "top1_compact_on I_set I_top"
          unfolding top1_unit_interval_def top1_unit_interval_topology_def
          using Theorem_27_1[of "0::real" 1] by (by100 simp)
        have hI_top: "is_topology_on I_set I_top"
          by (rule top1_unit_interval_topology_is_topology_on)
        from Theorem_26_6[OF hI_top hB_top hI_compact hB_haus hcomp_cont hcomp_bij]
        have hcomp_homeo: "top1_homeomorphism_on I_set I_top B (subspace_topology E TE B)
            ((inv_into B p) \<circ> g)" .
        show "top1_is_arc_on B (subspace_topology E TE B)"
          unfolding top1_is_arc_on_def using hB_strict hcomp_homeo by (by100 blast)
      qed
      have h\<A>L_cover: "\<Union>?\<A>_L = E"
      proof (rule set_eqI, rule iffI)
        fix e assume "e \<in> \<Union>?\<A>_L"
        then obtain B where "B \<in> ?\<A>_L" "e \<in> B" by (by100 blast)
        then obtain A0 where "A0 \<in> \<A>w" and hB_comp: "top1_max_conn_comp {e' \<in> E. p e' \<in> A0}
            (subspace_topology E TE {e' \<in> E. p e' \<in> A0}) B" by (by100 blast)
        have "B \<subseteq> {e' \<in> E. p e' \<in> A0}" using max_conn_comp_sub[OF hB_comp] .
        thus "e \<in> E" using \<open>e \<in> B\<close> by (by100 blast)
      next
        fix e assume "e \<in> E"
        have "p e \<in> X" using \<open>e \<in> E\<close> hp_surj by (by100 blast)
        hence "p e \<in> \<Union>\<A>w" using h\<A>w_cover by simp
        then obtain A0 where "A0 \<in> \<A>w" "p e \<in> A0" by (by100 blast)
        hence "e \<in> {e' \<in> E. p e' \<in> A0}" using \<open>e \<in> E\<close> by (by100 blast)
        have hpre_top: "is_topology_on {e' \<in> E. p e' \<in> A0}
            (subspace_topology E TE {e' \<in> E. p e' \<in> A0})"
          by (rule subspace_topology_is_topology_on[OF hTE]) (by100 blast)
        from max_conn_comp_covers[OF hpre_top \<open>e \<in> {e' \<in> E. p e' \<in> A0}\<close>]
        obtain B where hB_comp: "top1_max_conn_comp {e' \<in> E. p e' \<in> A0}
            (subspace_topology E TE {e' \<in> E. p e' \<in> A0}) B" and "e \<in> B" by (by100 blast)
        have "B \<in> ?\<A>_L" using \<open>A0 \<in> \<A>w\<close> hB_comp by (by100 blast)
        thus "e \<in> \<Union>?\<A>_L" using \<open>e \<in> B\<close> by (by100 blast)
      qed
      have h\<A>L_inter: "\<forall>B1\<in>?\<A>_L. \<forall>B2\<in>?\<A>_L. B1 \<noteq> B2 \<longrightarrow>
           B1 \<inter> B2 \<subseteq> top1_arc_endpoints_on B1 (subspace_topology E TE B1)
         \<and> B1 \<inter> B2 \<subseteq> top1_arc_endpoints_on B2 (subspace_topology E TE B2)
         \<and> finite (B1 \<inter> B2) \<and> card (B1 \<inter> B2) \<le> 2"
      proof (intro ballI impI)
        fix B1 B2 assume hB1: "B1 \<in> ?\<A>_L" and hB2: "B2 \<in> ?\<A>_L" and hne: "B1 \<noteq> B2"
        \<comment> \<open>B1 is max conn comp of preimage(A1), B2 of preimage(A2).\<close>
        obtain A1 where hA1: "A1 \<in> \<A>w" and hB1_comp: "top1_max_conn_comp {e \<in> E. p e \<in> A1}
            (subspace_topology E TE {e \<in> E. p e \<in> A1}) B1" using hB1 by (by100 blast)
        obtain A2 where hA2: "A2 \<in> \<A>w" and hB2_comp: "top1_max_conn_comp {e \<in> E. p e \<in> A2}
            (subspace_topology E TE {e \<in> E. p e \<in> A2}) B2" using hB2 by (by100 blast)
        \<comment> \<open>From Clause 1: p`B1 = A1, inj\\_on p B1, endpoint preservation.\<close>
        from hclause1[rule_format, OF hB1]
        obtain A1' where hA1'_in: "A1' \<in> \<A>w" and hB1_sub: "B1 \<subseteq> {e \<in> E. p e \<in> A1'}"
            and hpB1: "p ` B1 = A1'" and hinj1: "inj_on p B1"
            and hep1: "p ` (top1_arc_endpoints_on B1 (subspace_topology E TE B1))
              = top1_arc_endpoints_on A1' (subspace_topology X TX A1')"
          by (by100 blast)
        from hclause1[rule_format, OF hB2]
        obtain A2' where hA2'_in: "A2' \<in> \<A>w" and hB2_sub: "B2 \<subseteq> {e \<in> E. p e \<in> A2'}"
            and hpB2: "p ` B2 = A2'" and hinj2: "inj_on p B2"
            and hep2: "p ` (top1_arc_endpoints_on B2 (subspace_topology E TE B2))
              = top1_arc_endpoints_on A2' (subspace_topology X TX A2')"
          by (by100 blast)
        show "B1 \<inter> B2 \<subseteq> top1_arc_endpoints_on B1 (subspace_topology E TE B1)
            \<and> B1 \<inter> B2 \<subseteq> top1_arc_endpoints_on B2 (subspace_topology E TE B2)
            \<and> finite (B1 \<inter> B2) \<and> card (B1 \<inter> B2) \<le> 2"
        proof (cases "A1' = A2'")
          case True
          \<comment> \<open>Same base arc: B1, B2 are lifts over A1' = A2'. Clause 3: B1 \\<inter> B2 = {}.\<close>
          have "B1 \<inter> B2 = {}"
            using hclause3[rule_format, OF hA1'_in hB1 hB2] hB1_sub hB2_sub hne True
            by (by5000 blast)
          thus ?thesis by (by100 simp)
        next
          case False
          \<comment> \<open>Different base arcs: p(B1 \\<inter> B2) \\<subseteq> A1' \\<inter> A2' \\<subseteq> endpoints.\<close>
          have "B1 \<inter> B2 \<subseteq> {e \<in> E. p e \<in> A1' \<inter> A2'}"
            using hB1_sub hB2_sub by (by100 blast)
          have hA12_inter: "A1' \<inter> A2' \<subseteq> top1_arc_endpoints_on A1' (subspace_topology X TX A1')
              \<and> A1' \<inter> A2' \<subseteq> top1_arc_endpoints_on A2' (subspace_topology X TX A2')
              \<and> finite (A1' \<inter> A2') \<and> card (A1' \<inter> A2') \<le> 2"
            using h\<A>w_inter[rule_format, OF hA1'_in hA2'_in False] .
          \<comment> \<open>For e \\<in> B1 \\<inter> B2: p(e) \\<in> A1' \\<inter> A2' \\<subseteq> endpoints(A1').
             From hep1: p maps endpoints(B1) onto endpoints(A1').
             Since p injective on B1: e is in endpoints(B1) iff p(e) \\<in> endpoints(A1').
             p(e) \\<in> endpoints(A1') \\<Rightarrow> e \\<in> p\\<inverse>(endpoints(A1')) \\<inter> B1 = endpoints(B1).\<close>
          have hB1_inter_sub: "B1 \<inter> B2 \<subseteq> top1_arc_endpoints_on B1 (subspace_topology E TE B1)"
          proof (intro subsetI)
            fix e assume "e \<in> B1 \<inter> B2"
            hence "e \<in> B1" "e \<in> B2" by (by100 blast)+
            have "p e \<in> A1' \<inter> A2'" using \<open>e \<in> B1\<close> \<open>e \<in> B2\<close> hB1_sub hB2_sub by (by100 blast)
            hence "p e \<in> top1_arc_endpoints_on A1' (subspace_topology X TX A1')"
              using hA12_inter by (by100 blast)
            \<comment> \<open>p(e) is in the image of endpoints(B1) under p (from hep1).
               Since p injective on B1 and e \\<in> B1: e is the unique preimage.\<close>
            have "p e \<in> p ` (top1_arc_endpoints_on B1 (subspace_topology E TE B1))"
              using hep1 \<open>p e \<in> top1_arc_endpoints_on A1' _\<close> by simp
            then obtain e' where "e' \<in> top1_arc_endpoints_on B1 (subspace_topology E TE B1)"
                "p e' = p e" by (by100 auto)
            have "e' \<in> B1" using \<open>e' \<in> top1_arc_endpoints_on B1 _\<close>
              unfolding top1_arc_endpoints_on_def by (by100 blast)
            from inj_onD[OF hinj1 \<open>p e' = p e\<close>[symmetric] \<open>e \<in> B1\<close> \<open>e' \<in> B1\<close>]
            have "e = e'" .
            thus "e \<in> top1_arc_endpoints_on B1 (subspace_topology E TE B1)"
              using \<open>e' \<in> top1_arc_endpoints_on B1 _\<close> by simp
          qed
          have hB2_inter_sub: "B1 \<inter> B2 \<subseteq> top1_arc_endpoints_on B2 (subspace_topology E TE B2)"
          proof (intro subsetI)
            fix e assume "e \<in> B1 \<inter> B2"
            hence "e \<in> B1" "e \<in> B2" by (by100 blast)+
            have "p e \<in> A1' \<inter> A2'" using \<open>e \<in> B1\<close> \<open>e \<in> B2\<close> hB1_sub hB2_sub by (by100 blast)
            hence "p e \<in> top1_arc_endpoints_on A2' (subspace_topology X TX A2')"
              using hA12_inter by (by100 blast)
            have "p e \<in> p ` (top1_arc_endpoints_on B2 (subspace_topology E TE B2))"
              using hep2 \<open>p e \<in> top1_arc_endpoints_on A2' _\<close> by simp
            then obtain e' where "e' \<in> top1_arc_endpoints_on B2 (subspace_topology E TE B2)"
                "p e' = p e" by (by100 auto)
            have "e' \<in> B2" using \<open>e' \<in> top1_arc_endpoints_on B2 _\<close>
              unfolding top1_arc_endpoints_on_def by (by100 blast)
            from inj_onD[OF hinj2 \<open>p e' = p e\<close>[symmetric] \<open>e \<in> B2\<close> \<open>e' \<in> B2\<close>]
            have "e = e'" .
            thus "e \<in> top1_arc_endpoints_on B2 (subspace_topology E TE B2)"
              using \<open>e' \<in> top1_arc_endpoints_on B2 _\<close> by simp
          qed
          \<comment> \<open>Finiteness and card \\<le> 2: B1 \\<inter> B2 maps injectively into A1' \\<inter> A2' (card \\<le> 2).\<close>
          have hfin_inter: "finite (B1 \<inter> B2) \<and> card (B1 \<inter> B2) \<le> 2"
          proof -
            have "inj_on p (B1 \<inter> B2)"
              using hinj1 by (rule inj_on_subset) (by100 blast)
            have "p ` (B1 \<inter> B2) \<subseteq> A1' \<inter> A2'"
              using hB1_sub hB2_sub by (by100 blast)
            have "finite (A1' \<inter> A2')" using hA12_inter by (by100 blast)
            have "card (A1' \<inter> A2') \<le> 2" using hA12_inter by (by100 blast)
            have "finite (B1 \<inter> B2)"
            proof -
              from finite_imageD[OF finite_subset[OF \<open>p ` (B1 \<inter> B2) \<subseteq> A1' \<inter> A2'\<close>
                  \<open>finite (A1' \<inter> A2')\<close>] \<open>inj_on p (B1 \<inter> B2)\<close>]
              show ?thesis .
            qed
            moreover have "card (B1 \<inter> B2) \<le> 2"
            proof -
              from card_inj_on_le[OF \<open>inj_on p (B1 \<inter> B2)\<close> \<open>p ` (B1 \<inter> B2) \<subseteq> A1' \<inter> A2'\<close>
                  \<open>finite (A1' \<inter> A2')\<close>]
              show ?thesis using \<open>card (A1' \<inter> A2') \<le> 2\<close> by linarith
            qed
            ultimately show ?thesis by (by100 blast)
          qed
          show ?thesis using hB1_inter_sub hB2_inter_sub hfin_inter by (by100 blast)
        qed
      qed
      have h\<A>L_fin: "finite ?\<A>_L" using h\<A>_L_card by (by100 blast)
      \<comment> \<open>Direct Euler invariance between \\<A>\\_L and \\<A>E\\_raw.\<close>
      from graph_euler_invariance[OF hE_graph h\<A>L_arcs h\<A>L_cover h\<A>L_inter h\<A>L_fin
          h\<A>E_arcs h\<A>E_cover h\<A>E_inter h\<A>E_fin]
      have hstep2: "int (card (top1_graph_vertex_set E TE ?\<A>_L)) - int (card ?\<A>_L)
          = int (card (top1_graph_vertex_set E TE \<A>E_raw)) - int (card \<A>E_raw)" .
      show ?thesis using hstep2 by linarith
    qed
    \<comment> \<open>Combine: rank + V\\_L = \\<A>\\_L + 1.\<close>
    show ?thesis using hrank_E_raw heuler_inv by linarith
  qed
  have hrank_E: "int (card SE_raw) = int (card ?\<A>_L) - int (card (top1_graph_vertex_set E TE ?\<A>_L)) + 1"
    using hrank_E_formula by linarith
  \<comment> \<open>Step 6d: Combine to get card(SE\\_raw) = k*n + 1.\<close>
  have "int (card SE_raw) = int k * int n + 1"
    using hrank_E hchi_L by linarith
  hence hcard_SE: "card SE_raw = k * n + 1"
  proof -
    assume h: "int (card SE_raw) = int k * int n + 1"
    have "int (card SE_raw) = int (k * n) + 1" using h by simp
    hence "int (card SE_raw) = int (k * n + 1)" by simp
    thus "card SE_raw = k * n + 1" using of_nat_eq_iff by (by100 blast)
  qed
  \<comment> \<open>Step 6e: Transfer to nat-indexed basis.
     hfree\\_E gives free group on SE\\_raw ('a set set) with card = k*n+1.
     Re-index via bijection SE\\_raw \\<leftrightarrow> {..<k*n+1} to get nat set.\<close>
  have hSE_fin: "finite SE_raw"
    using hcard_SE by (cases "finite SE_raw") simp_all
  show ?thesis
  proof -
    \<comment> \<open>Construct nat-indexed basis via bijection.\<close>
    obtain f :: "nat \<Rightarrow> 'b set" where hf: "bij_betw f {..<card SE_raw} SE_raw"
    proof -
      from ex_bij_betw_nat_finite[OF hSE_fin]
      obtain g where "bij_betw g {0..<card SE_raw} SE_raw" by (by100 blast)
      have "{0..<card SE_raw} = {..<card SE_raw}" by (by100 auto)
      hence "bij_betw g {..<card SE_raw} SE_raw" using \<open>bij_betw g _ _\<close> by simp
      thus thesis using that by (by100 blast)
    qed
    let ?\<iota>N = "\<lambda>i::nat. \<iota>E_raw (f i)"
    let ?SN = "{..<card SE_raw}"
    have "top1_is_free_group_full_on
        (top1_fundamental_group_carrier E TE e0)
        (top1_fundamental_group_mul E TE e0)
        (top1_fundamental_group_id E TE e0)
        (top1_fundamental_group_invg E TE e0) ?\<iota>N ?SN"
    proof -
      from free_group_full_reindex[OF hfree_E hf]
      have "top1_is_free_group_full_on
          (top1_fundamental_group_carrier E TE e0)
          (top1_fundamental_group_mul E TE e0)
          (top1_fundamental_group_id E TE e0)
          (top1_fundamental_group_invg E TE e0) (\<iota>E_raw \<circ> f) ?SN" .
      moreover have "(\<iota>E_raw \<circ> f) = ?\<iota>N" by (by100 auto)
      ultimately show ?thesis by simp
    qed
    moreover have "card ?SN = k * n + 1" using hcard_SE by simp
    ultimately show ?thesis by (by100 blast)
  qed
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
    \<comment> \<open>Step F: Covering multiplicity.\<close>
    have hfiber_card_and_fin: "card {e \<in> E'. p' e = x0} = k \<and> finite {e \<in> E'. p' e = x0}"
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
      have hk_eq: "card (top1_left_cosets_on ?piX ?mulX ?pH) = k" by (by100 blast)
      have hcard_eq: "card {e \<in> E'. p' e = x0} = k" using hright_card hlr hk_eq by simp
      have "finite (top1_left_cosets_on ?piX ?mulX ?pH)"
        using hindex unfolding top1_subgroup_has_index_on_def by (by100 blast)
      hence "finite (top1_right_cosets_on ?piX ?mulX ?pH)"
      proof -
        assume "finite (top1_left_cosets_on ?piX ?mulX ?pH)"
        have "card (top1_left_cosets_on ?piX ?mulX ?pH) = card (top1_right_cosets_on ?piX ?mulX ?pH)"
          using hlr .
        show ?thesis
        proof (rule ccontr)
          assume "\<not> finite (top1_right_cosets_on ?piX ?mulX ?pH)"
          hence "card (top1_right_cosets_on ?piX ?mulX ?pH) = 0" by simp
          hence "card (top1_left_cosets_on ?piX ?mulX ?pH) = 0" using hlr by simp
          hence "top1_left_cosets_on ?piX ?mulX ?pH = {}"
            using \<open>finite (top1_left_cosets_on ?piX ?mulX ?pH)\<close> by simp
          moreover have "top1_left_cosets_on ?piX ?mulX ?pH \<noteq> {}"
          proof -
            have "top1_fundamental_group_id X TX x0 \<in> ?piX"
              using top1_fundamental_group_is_group[OF hX_top hx0]
              unfolding top1_is_group_on_def by (by100 blast)
            hence "top1_group_coset_on ?piX ?mulX ?pH (top1_fundamental_group_id X TX x0)
                \<in> top1_left_cosets_on ?piX ?mulX ?pH"
              unfolding top1_left_cosets_on_def by (by100 blast)
            thus ?thesis by (by100 blast)
          qed
          ultimately show False using finite_subset by (by100 blast)
        qed
      qed
      have "finite {e \<in> E'. p' e = x0}"
        using bij_betw_finite[OF \<open>bij_betw f _ _\<close>]
            \<open>finite (top1_right_cosets_on ?piX ?mulX ?pH)\<close> by (by100 blast)
      thus ?thesis using hcard_eq by (by100 blast)
    qed
    have hfiber_card: "card {e \<in> E'. p' e = x0} = k"
      using hfiber_card_and_fin by (by100 blast)
    have hfiber_fin: "finite {e \<in> E'. p' e = x0}"
      using hfiber_card_and_fin by (by100 blast)
    have hX_top: "is_topology_on X TX"
      using hX_graph unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
    have hE'_top: "is_topology_on E' TE'"
      using hE'_strict unfolding is_topology_on_strict_def by (by100 blast)
    have hfiber_all: "\<forall>x\<in>X. card {e \<in> E'. p' e = x} = k"
    proof -
        \<comment> \<open>The set {x \\<in> X. card(fiber(x)) = k} is clopen in X and contains x0.
           X connected \\<Rightarrow> this set = X.\<close>
        let ?S = "{x \<in> X. card {e \<in> E'. p' e = x} = k}"
        have hx0_S: "x0 \<in> ?S" using hfiber_card hx0 by (by100 blast)
        \<comment> \<open>?S is open: for any x \\<in> ?S, the evenly covered nbhd Vx has constant fiber card.\<close>
        \<comment> \<open>Fiber card is locally constant: in any evenly covered U, all points have same fiber card.\<close>
        have hlocal_const: "\<forall>x\<in>X. \<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> X \<and>
            (\<forall>y\<in>U. card {e \<in> E'. p' e = y} = card {e \<in> E'. p' e = x})"
        proof (intro ballI)
          fix x assume "x \<in> X"
          \<comment> \<open>Get evenly covered nbhd U of x.\<close>
          from top1_covering_map_on_evenly_covered[OF hE'_cov \<open>x \<in> X\<close>]
          obtain U where hU: "x \<in> U" "top1_evenly_covered_on E' TE' X TX p' U" by (by100 blast)
          have hU_open: "openin_on X TX U"
            using hU(2) unfolding top1_evenly_covered_on_def by (by100 blast)
          from hU(2)[unfolded top1_evenly_covered_on_def]
          obtain V where hV_props: "(\<forall>Vi\<in>V. openin_on E' TE' Vi) \<and>
              (\<forall>Vi\<in>V. \<forall>Vj\<in>V. Vi \<noteq> Vj \<longrightarrow> Vi \<inter> Vj = {}) \<and>
              {e \<in> E'. p' e \<in> U} = \<Union>V \<and>
              (\<forall>Vi\<in>V. top1_homeomorphism_on Vi (subspace_topology E' TE' Vi)
                  U (subspace_topology X TX U) p')"
            by (by100 auto)
          have hV_open: "\<forall>Vi\<in>V. openin_on E' TE' Vi" using hV_props by (by100 blast)
          have hV_disj: "\<forall>Vi\<in>V. \<forall>Vj\<in>V. Vi \<noteq> Vj \<longrightarrow> Vi \<inter> Vj = {}" using hV_props by (by100 blast)
          have hV_union: "{e \<in> E'. p' e \<in> U} = \<Union>V" using hV_props by (by100 blast)
          have hV_homeo: "\<forall>Vi\<in>V. top1_homeomorphism_on Vi (subspace_topology E' TE' Vi)
                  U (subspace_topology X TX U) p'" using hV_props by (by100 blast)
          have hU_TX: "U \<in> TX" using hU_open unfolding openin_on_def by (by100 blast)
          have hU_sub: "U \<subseteq> X" using hU_open unfolding openin_on_def by (by100 blast)
          \<comment> \<open>For each y \\<in> U: fiber(y) has exactly |V| elements (one per slice).
             Hence all y \\<in> U have same fiber card.\<close>
          have hcard_eq: "\<forall>y\<in>U. card {e \<in> E'. p' e = y} = card V"
          proof (intro ballI)
            fix y assume "y \<in> U"
            \<comment> \<open>Construct bijection: for each Vi \\<in> V, the unique e \\<in> Vi with p'(e) = y.\<close>
            have "\<forall>Vi\<in>V. \<exists>!e. e \<in> Vi \<and> p' e = y"
            proof (intro ballI)
              fix Vi assume "Vi \<in> V"
              from hV_homeo[rule_format, OF this]
              have hhomeo: "top1_homeomorphism_on Vi (subspace_topology E' TE' Vi)
                  U (subspace_topology X TX U) p'" .
              hence hbij: "bij_betw p' Vi U"
                unfolding top1_homeomorphism_on_def by (by100 blast)
              from bij_betw_imp_surj_on[OF hbij]
              have "\<forall>y\<in>U. \<exists>e\<in>Vi. p' e = y" by (by100 blast)
              hence "\<exists>e. e \<in> Vi \<and> p' e = y" using \<open>y \<in> U\<close> by (by100 blast)
              moreover have "\<forall>e1 e2. e1 \<in> Vi \<and> p' e1 = y \<longrightarrow> e2 \<in> Vi \<and> p' e2 = y \<longrightarrow> e1 = e2"
              proof (intro allI impI)
                fix e1 e2 assume "e1 \<in> Vi \<and> p' e1 = y" "e2 \<in> Vi \<and> p' e2 = y"
                from bij_betw_imp_inj_on[OF hbij]
                have "inj_on p' Vi" .
                from inj_onD[OF this] show "e1 = e2"
                  using \<open>e1 \<in> Vi \<and> p' e1 = y\<close> \<open>e2 \<in> Vi \<and> p' e2 = y\<close> by (by100 blast)
              qed
              ultimately show "\<exists>!e. e \<in> Vi \<and> p' e = y" by (by100 blast)
            qed
            \<comment> \<open>Define f: V \\<rightarrow> E' mapping Vi to the unique e.\<close>
            define f where "f = (\<lambda>Vi. THE e. e \<in> Vi \<and> p' e = y)"
            \<comment> \<open>f is a bijection from V to {e \\<in> E'. p' e = y}.\<close>
            have hf_bij: "bij_betw f V {e \<in> E'. p' e = y}"
              unfolding bij_betw_def
            proof (intro conjI)
              show "inj_on f V"
              proof (rule inj_onI)
                fix Vi Vj assume "Vi \<in> V" "Vj \<in> V" "f Vi = f Vj"
                have hfVi: "f Vi \<in> Vi \<and> p' (f Vi) = y"
                  using theI'[OF \<open>\<forall>Vi\<in>V. \<exists>!e. _\<close>[rule_format, OF \<open>Vi \<in> V\<close>]]
                  unfolding f_def by (by100 blast)
                have hfVj: "f Vj \<in> Vj \<and> p' (f Vj) = y"
                  using theI'[OF \<open>\<forall>Vi\<in>V. \<exists>!e. _\<close>[rule_format, OF \<open>Vj \<in> V\<close>]]
                  unfolding f_def by (by100 blast)
                have "f Vi \<in> Vi" using hfVi by (by100 blast)
                have "f Vj \<in> Vj" using hfVj by (by100 blast)
                have "f Vi \<in> Vj" using \<open>f Vj \<in> Vj\<close> \<open>f Vi = f Vj\<close> by simp
                hence "f Vi \<in> Vi \<inter> Vj" using \<open>f Vi \<in> Vi\<close> by (by100 blast)
                thus "Vi = Vj" using hV_disj \<open>Vi \<in> V\<close> \<open>Vj \<in> V\<close> by (by100 blast)
              qed
              show "f ` V = {e \<in> E'. p' e = y}"
              proof (rule set_eqI, rule iffI)
                fix e assume "e \<in> f ` V"
                then obtain Vi where "Vi \<in> V" "e = f Vi" by (by100 blast)
                have he_props: "e \<in> Vi \<and> p' e = y"
                  using theI'[OF \<open>\<forall>Vi\<in>V. \<exists>!e. _\<close>[rule_format, OF \<open>Vi \<in> V\<close>]]
                  unfolding f_def \<open>e = f Vi\<close> by (by100 blast)
                have "Vi \<subseteq> E'" using hV_open \<open>Vi \<in> V\<close> unfolding openin_on_def by (by100 blast)
                thus "e \<in> {e \<in> E'. p' e = y}" using he_props \<open>Vi \<subseteq> E'\<close> by (by100 blast)
              next
                fix e assume "e \<in> {e \<in> E'. p' e = y}"
                hence "e \<in> E'" "p' e = y" by (by100 blast)+
                have "p' e \<in> U" using \<open>p' e = y\<close> \<open>y \<in> U\<close> by simp
                hence "e \<in> {e \<in> E'. p' e \<in> U}" using \<open>e \<in> E'\<close> by (by100 blast)
                hence "e \<in> \<Union>V" using hV_union by (by100 blast)
                then obtain Vi where "Vi \<in> V" "e \<in> Vi" by (by100 blast)
                have "f Vi = e"
                proof -
                  have "\<exists>!e. e \<in> Vi \<and> p' e = y"
                    using \<open>\<forall>Vi\<in>V. \<exists>!e. _\<close> \<open>Vi \<in> V\<close> by (by100 blast)
                  moreover have "e \<in> Vi \<and> p' e = y" using \<open>e \<in> Vi\<close> \<open>p' e = y\<close> by (by100 blast)
                  ultimately show ?thesis unfolding f_def
                    by (rule the1_equality)
                qed
                thus "e \<in> f ` V" using \<open>Vi \<in> V\<close> by (by100 blast)
              qed
            qed
            from bij_betw_same_card[OF hf_bij]
            show "card {e \<in> E'. p' e = y} = card V" by simp
          qed
          hence "\<forall>y\<in>U. card {e \<in> E'. p' e = y} = card {e \<in> E'. p' e = x}"
            using \<open>x \<in> U\<close> by simp
          thus "\<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> X \<and>
              (\<forall>y\<in>U. card {e \<in> E'. p' e = y} = card {e \<in> E'. p' e = x})"
            using hU_TX hU(1) hU_sub by (by100 blast)
        qed
        have hS_open: "?S \<in> TX"
        proof -
          \<comment> \<open>?S = \\<Union>{U | x \\<in> ?S, U evenly covered nbhd of x with constant fiber card}.\<close>
          have "\<forall>x\<in>?S. \<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> ?S"
          proof (intro ballI)
            fix x assume "x \<in> ?S"
            hence "x \<in> X" "card {e \<in> E'. p' e = x} = k" by (by100 blast)+
            from hlocal_const[rule_format, OF \<open>x \<in> X\<close>]
            obtain U where "U \<in> TX" "x \<in> U" "U \<subseteq> X"
                "\<forall>y\<in>U. card {e \<in> E'. p' e = y} = card {e \<in> E'. p' e = x}" by (by100 blast)
            have "U \<subseteq> ?S"
            proof (intro subsetI)
              fix y assume "y \<in> U"
              have "y \<in> X" using \<open>U \<subseteq> X\<close> \<open>y \<in> U\<close> by (by100 blast)
              have "card {e \<in> E'. p' e = y} = k"
                using \<open>\<forall>y\<in>U. _\<close> \<open>y \<in> U\<close> \<open>card {e \<in> E'. p' e = x} = k\<close> by simp
              thus "y \<in> ?S" using \<open>y \<in> X\<close> by (by100 blast)
            qed
            thus "\<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> ?S" using \<open>U \<in> TX\<close> \<open>x \<in> U\<close> by (by100 blast)
          qed
          hence "?S = \<Union>{U \<in> TX. U \<subseteq> ?S}" by (by100 blast)
          moreover have "{U \<in> TX. U \<subseteq> ?S} \<subseteq> TX" by (by100 blast)
          hence "\<Union>{U \<in> TX. U \<subseteq> ?S} \<in> TX"
            using hX_top unfolding is_topology_on_def by (by5000 blast)
          ultimately show ?thesis by simp
        qed
        \<comment> \<open>?S is closed: X \\ ?S is open (same argument with \\<noteq> k).\<close>
        have hS_closed: "closedin_on X TX ?S"
        proof -
          have "X - ?S \<in> TX"
          proof -
            have "\<forall>x\<in>X - ?S. \<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> X - ?S"
            proof (intro ballI)
              fix x assume "x \<in> X - ?S"
              hence "x \<in> X" "card {e \<in> E'. p' e = x} \<noteq> k" by (by100 blast)+
              from hlocal_const[rule_format, OF \<open>x \<in> X\<close>]
              obtain U where "U \<in> TX" "x \<in> U" "U \<subseteq> X"
                  "\<forall>y\<in>U. card {e \<in> E'. p' e = y} = card {e \<in> E'. p' e = x}" by (by100 blast)
              have "U \<subseteq> X - ?S"
              proof (intro subsetI DiffI)
                fix y assume "y \<in> U"
                show "y \<in> X" using \<open>U \<subseteq> X\<close> \<open>y \<in> U\<close> by (by100 blast)
                show "y \<notin> ?S"
                proof
                  assume "y \<in> ?S"
                  hence "card {e \<in> E'. p' e = y} = k" by (by100 blast)
                  moreover have "card {e \<in> E'. p' e = y} = card {e \<in> E'. p' e = x}"
                    using \<open>\<forall>y\<in>U. _\<close> \<open>y \<in> U\<close> by (by100 blast)
                  ultimately show False using \<open>card {e \<in> E'. p' e = x} \<noteq> k\<close> by simp
                qed
              qed
              thus "\<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> X - ?S" using \<open>U \<in> TX\<close> \<open>x \<in> U\<close> by (by100 blast)
            qed
            hence "X - ?S = \<Union>{U \<in> TX. U \<subseteq> X - ?S}" by (by100 blast)
            moreover have "{U \<in> TX. U \<subseteq> X - ?S} \<subseteq> TX" by (by100 blast)
            hence "\<Union>{U \<in> TX. U \<subseteq> X - ?S} \<in> TX"
              using hX_top unfolding is_topology_on_def by (by5000 blast)
            ultimately show ?thesis by simp
          qed
          moreover have "?S \<subseteq> X" by (by100 blast)
          ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
        qed
        \<comment> \<open>X connected, ?S clopen and non-empty \\<Rightarrow> ?S = X.\<close>
        have "?S = {} \<or> ?S = X"
          using connected_iff_clopen[OF hX_top] hX_conn hS_open hS_closed by (by100 blast)
        hence "?S = X" using hx0_S by (by100 blast)
        thus ?thesis by (by100 blast)
    qed
    have hk_pos: "k > 0"
    proof -
      from assms(5) have "card (top1_left_cosets_on F mul H) = k"
        unfolding top1_subgroup_has_index_on_def by (by100 blast)
      moreover have "top1_left_cosets_on F mul H \<noteq> {}"
      proof -
        have "e \<in> F" using assms(1) unfolding top1_is_free_group_full_on_def
            top1_is_group_on_def by (by100 blast)
        hence "top1_group_coset_on F mul H e \<in> top1_left_cosets_on F mul H"
          unfolding top1_left_cosets_on_def by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      moreover have "finite (top1_left_cosets_on F mul H)"
        using assms(5) unfolding top1_subgroup_has_index_on_def by (by100 blast)
      ultimately show "k > 0" by (by100 force)
    qed
    have hE'_compact: "top1_compact_on E' TE'"
      using finite_covering_compact[OF hE'_cov hX_compact hX_top hE'_top hfiber_all hk_pos] .
    have h\<A>_E_fin: "finite \<A>_E"
      by (rule compact_graph_finite_arcs[OF hE'_graph hE'_compact h\<A>_E h\<A>_E_cover h\<A>_E_inter h\<A>_E_coh])
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
    \<comment> \<open>Euler characteristic multiplicity: card(S\\_E) - 1 = k * (card(S\\_X) - 1).
       Munkres 85.3: E' has k times as many arcs and vertices as X.
       The proof constructs the lifted arc family from \\<A>\\_X (connected components
       of p'^{-1}(A) for each A \\<in> \\<A>\\_X). Each arc lifts to k arcs (since arcs
       are simply connected, the covering over each arc is trivial: k disjoint sheets).
       Similarly, each vertex lifts to k vertices (fibers of points).
       The lifted family gives an Euler formula with the same rank as \\<pi>\\_1(E').
       By rank invariance, card(S\\_E) for ANY valid decomposition equals kn+1.\<close>
    have hk_pos: "k > 0"
    proof -
      have "e0' \<in> {e \<in> E'. p' e = x0}" using he0' \<open>p' e0' = x0\<close> by (by100 blast)
      hence "{e \<in> E'. p' e = x0} \<noteq> {}" by (by100 blast)
      moreover have "card {e \<in> E'. p' e = x0} = k" using hfiber_card .
      ultimately show "k > 0"
      proof -
        assume "{e \<in> E'. p' e = x0} \<noteq> {}" "card {e \<in> E'. p' e = x0} = k"
        show "k > 0"
        proof (rule ccontr)
          assume "\<not> k > 0"
          hence "k = 0" by simp
          hence "card {e \<in> E'. p' e = x0} = 0" using \<open>card _ = k\<close> by simp
          hence "{e \<in> E'. p' e = x0} = {}" using hfiber_fin by simp
          with \<open>{e \<in> E'. p' e = x0} \<noteq> {}\<close> show False by (by100 blast)
        qed
      qed
    qed
    \<comment> \<open>Step G--H: Compute rank(\\<pi>\\_1(E')) = kn + 1 via rank invariance.
       Munkres 85.3: construct the lifted arc family \\<A>\\_L from \\<A>\\_X.
       Each arc of X lifts to k arcs (arc = simply connected \\<Rightarrow> trivial covering).
       Each vertex of X has k preimages.
       card(\\<A>\\_L) = k * card(\\<A>\\_X), card(V\\_L) = k * card(V\\_X).
       A spanning tree of the lifted graph has card(V\\_L) - 1 arcs.
       Non-tree arcs: card(\\<A>\\_L) - (card(V\\_L) - 1) = k*(card(\\<A>\\_X) - card(V\\_X)) + 1 = kn + 1.
       By graph\\_pi1\\_free\\_weak: \\<pi>\\_1(E') is free on these kn+1 non-tree arcs.
       By rank invariance: card(S\\_E) = kn + 1.\<close>
    have "\<exists>(\<iota>L :: nat \<Rightarrow> _) (SL :: nat set). top1_is_free_group_full_on
        (top1_fundamental_group_carrier E' TE' e0')
        (top1_fundamental_group_mul E' TE' e0')
        (top1_fundamental_group_id E' TE' e0')
        (top1_fundamental_group_invg E' TE' e0')
        \<iota>L SL \<and> card SL = k * n + 1"
    proof (rule covering_graph_pi1_rank)
      show "top1_is_graph_on X TX" using hX_graph .
      show "top1_connected_on X TX" using hX_conn .
      show "x0 \<in> X" using hx0 .
      show "top1_covering_map_on E' TE' X TX p'" using hE'_cov .
      show "is_topology_on_strict E' TE'" using hE'_strict .
      show "top1_connected_on E' TE'" using hE'_conn .
      show "e0' \<in> E'" using he0' .
      show "p' e0' = x0" using \<open>p' e0' = x0\<close> .
      show "\<forall>x\<in>X. card {e \<in> E'. p' e = x} = k" using hfiber_all .
      show "k > 0" using hk_pos .
      show "top1_is_free_group_full_on
          (top1_fundamental_group_carrier X TX x0)
          (top1_fundamental_group_mul X TX x0)
          (top1_fundamental_group_id X TX x0)
          (top1_fundamental_group_invg X TX x0)
          \<iota>_X S_X" using hfree_X .
      show "card S_X = n + 1" using hS_X_card .
      show "finite S_X" using hS_X_eq h\<A>_X_fin by (by100 simp)
      show "top1_compact_on X TX" using hX_compact .
    qed
    then obtain \<iota>L :: "nat \<Rightarrow> _" and SL :: "nat set"
      where hfreeL: "top1_is_free_group_full_on
        (top1_fundamental_group_carrier E' TE' e0')
        (top1_fundamental_group_mul E' TE' e0')
        (top1_fundamental_group_id E' TE' e0')
        (top1_fundamental_group_invg E' TE' e0')
        \<iota>L SL"
      and hcard_SL: "card SL = k * n + 1" by (by100 blast)
    \<comment> \<open>Now transfer: H \\<cong> \\<pi>\\_1(E') free on S\\_E AND \\<pi>\\_1(E') free on SL with card kn+1.
       Rank invariance: card(S\\_E) = card(SL) = kn+1.\<close>
    have hSL_fin: "finite SL"
    proof -
      have "card SL > 0" using hcard_SL by linarith
      thus ?thesis using card_gt_0_iff by (by100 blast)
    qed
    \<comment> \<open>Transfer freeL from \\<pi>\\_1(E') to H via the iso, then compare with hfreeH\\_SE.\<close>
    have hpiE_free_SE: "top1_is_free_group_full_on
        (top1_fundamental_group_carrier E' TE' e0')
        (top1_fundamental_group_mul E' TE' e0')
        (top1_fundamental_group_id E' TE' e0')
        (top1_fundamental_group_invg E' TE' e0')
        \<iota>_E S_E" using hfree_E .
    have hSE_fin: "finite S_E" using hS_E_eq h\<A>_E_fin by (by100 simp)
    from free_group_rank_invariant_finite[OF hpiE_free_SE hfreeL hSE_fin hSL_fin]
    have "card S_E = card SL" .
    thus ?thesis using hcard_SL by simp
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
  invert: "top1_elementary_scheme_operation w (rev (map top1_inverse_edge w))" |
  \<comment> \<open>Relabel: replace all occurrences of label old by label new.
     Book \\<S>76 operation (iii): "replace all occurrences of any given label by some other
     label that does not appear elsewhere in the scheme."\<close>
  relabel: "top1_elementary_scheme_operation w (map (\<lambda>(l,b). (if l = old then new else l, b)) w)" |
  \<comment> \<open>Flip orientation: change sign of exponent of all occurrences of a given label.
     Book \\<S>76 operation (iii): "one can change the sign of the exponent of all occurrences
     of a given label a; this amounts to reversing the orientations of all edges labelled a."\<close>
  flip_label: "top1_elementary_scheme_operation w (map (\<lambda>(l,b). (l, if l = a then \<not>b else b)) w)" |
  \<comment> \<open>Cut-and-repaste: the combined effect of Munkres \\<S>76 Theorem 76.1 on a single polygon.
     Cut at position between u1 and u2, introducing new label c.
     Flip one piece. Paste along label a (which appears in both pieces).
     Net effect on scheme: [u1] a [u2] a [u3] \\<sim> [u1] a a [u2\\<inverse>] [u3].
     This brings two copies of label a (same orientation) together.
     Formally: rotate one piece around and paste, cancelling u2 into u2\\<inverse>.\<close>
  cut_paste: "top1_elementary_scheme_operation
      (u1 @ [(a, True)] @ u2 @ [(a, True)] @ u3)
      (u1 @ [(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3)" |
  \<comment> \<open>Cut-paste variant 2 (Figure 77.2): rearrange with a new label.
     Transforms y0 a y1 a y2 into b y2 b (y1 y0\\<inverse>) where b is new.
     This is the book's Figure 77.2 operation from \\<S>77 Lemma 77.1 Step 2.\<close>
  cut_paste2: "top1_elementary_scheme_operation
      (u0 @ [(a, True)] @ u1 @ [(a, True)] @ u2)
      ([(b, True)] @ u2 @ [(b, True)] @ u1 @ rev (map top1_inverse_edge u0))" |
  \<comment> \<open>Cut-paste for opposite-orientation labels (Figure 77.3).
     Net effect: move u1 from before a to after a\\<inverse>.
     u0 @ u1 @ [(a,T)] @ u2 @ [(a,F)] @ u3 \\<to> u0 @ [(a,T)] @ u2 @ [(a,F)] @ u1 @ u3.\<close>
  cut_paste_opp: "top1_elementary_scheme_operation
      (u0 @ u1 @ [(a, True)] @ u2 @ [(a, False)] @ u3)
      (u0 @ [(a, True)] @ u2 @ [(a, False)] @ u1 @ u3)"

\<comment> \<open>The scheme equivalence is the reflexive-transitive closure of elementary operations.\<close>
definition top1_scheme_equiv :: "('a \<times> bool) list \<Rightarrow> ('a \<times> bool) list \<Rightarrow> bool" where
  "top1_scheme_equiv = top1_elementary_scheme_operation\<^sup>*\<^sup>*"

section \<open>\<S>76 Cutting and Pasting\<close>

\<comment> \<open>Quotient uniqueness: two quotient maps on the same space with the same fibres
   give homeomorphic quotient spaces. Follows from Theorem 22.2 applied both ways.\<close>
lemma quotient_same_fibres_homeomorphic:
  fixes X :: "'a set" and TX :: "'a set set"
    and Y1 :: "'b set" and TY1 :: "'b set set"
    and Y2 :: "'c set" and TY2 :: "'c set set"
  assumes hp1: "top1_quotient_map_on X TX Y1 TY1 p1"
      and hp2: "top1_quotient_map_on X TX Y2 TY2 p2"
      and hfibres: "\<forall>x\<in>X. \<forall>y\<in>X. (p1 x = p1 y) \<longleftrightarrow> (p2 x = p2 y)"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  \<comment> \<open>p2 is constant on fibres of p1 (from hfibres).\<close>
  have hp2_range: "\<forall>x\<in>X. p2 x \<in> Y2"
    using hp2 unfolding top1_quotient_map_on_def top1_continuous_map_on_def by (by100 blast)
  have hp2_const: "\<forall>x\<in>X. \<forall>y\<in>X. p1 x = p1 y \<longrightarrow> p2 x = p2 y"
    using hfibres by (by100 blast)
  \<comment> \<open>By Theorem 22.2: p2 factors through p1 as f: Y1 \\<to> Y2.\<close>
  from Theorem_22_2[OF hp1 hp2_range hp2_const]
  obtain f where hf_range: "\<forall>y\<in>Y1. f y \<in> Y2"
      and hf_comp: "\<forall>x\<in>X. f (p1 x) = p2 x"
      and hf_cont_iff: "top1_continuous_map_on Y1 TY1 Y2 TY2 f \<longleftrightarrow> top1_continuous_map_on X TX Y2 TY2 p2"
      and hf_quot_iff: "top1_quotient_map_on Y1 TY1 Y2 TY2 f \<longleftrightarrow> top1_quotient_map_on X TX Y2 TY2 p2"
    by (by100 blast)
  \<comment> \<open>Similarly p1 factors through p2 as g: Y2 \\<to> Y1.\<close>
  have hp1_range: "\<forall>x\<in>X. p1 x \<in> Y1"
    using hp1 unfolding top1_quotient_map_on_def top1_continuous_map_on_def by (by100 blast)
  have hp1_const: "\<forall>x\<in>X. \<forall>y\<in>X. p2 x = p2 y \<longrightarrow> p1 x = p1 y"
    using hfibres by (by100 blast)
  from Theorem_22_2[OF hp2 hp1_range hp1_const]
  obtain g where hg_range: "\<forall>y\<in>Y2. g y \<in> Y1"
      and hg_comp: "\<forall>x\<in>X. g (p2 x) = p1 x"
      and hg_cont_iff: "top1_continuous_map_on Y2 TY2 Y1 TY1 g \<longleftrightarrow> top1_continuous_map_on X TX Y1 TY1 p1"
      and hg_quot_iff: "top1_quotient_map_on Y2 TY2 Y1 TY1 g \<longleftrightarrow> top1_quotient_map_on X TX Y1 TY1 p1"
    by (by100 blast)
  \<comment> \<open>f is a quotient map (since p2 is).\<close>
  have hf_quot: "top1_quotient_map_on Y1 TY1 Y2 TY2 f"
    using hf_quot_iff hp2 by simp
  \<comment> \<open>f is bijective: injective (from g \\<circ> f = id on Y1) and surjective (quotient maps are surjective).\<close>
  have hf_surj: "f ` Y1 = Y2"
  proof -
    have "p2 ` X = Y2" using hp2 unfolding top1_quotient_map_on_def by (by100 blast)
    have "p1 ` X = Y1" using hp1 unfolding top1_quotient_map_on_def by (by100 blast)
    show ?thesis
    proof
      show "f ` Y1 \<subseteq> Y2" using hf_range by (by100 blast)
    next
      show "Y2 \<subseteq> f ` Y1"
      proof
        fix y2 assume "y2 \<in> Y2"
        hence "\<exists>x\<in>X. p2 x = y2" using \<open>p2 ` X = Y2\<close> by (by100 blast)
        then obtain x where "x \<in> X" "p2 x = y2" by (by100 blast)
        hence "f (p1 x) = y2" using hf_comp by simp
        moreover have "p1 x \<in> Y1" using hp1_range \<open>x \<in> X\<close> by (by100 blast)
        ultimately show "y2 \<in> f ` Y1" by (by100 blast)
      qed
    qed
  qed
  have hgf_id: "\<forall>y\<in>Y1. g (f y) = y"
  proof
    fix y1 assume "y1 \<in> Y1"
    have "p1 ` X = Y1" using hp1 unfolding top1_quotient_map_on_def by (by100 blast)
    then obtain x where "x \<in> X" "p1 x = y1" using \<open>y1 \<in> Y1\<close> by (by100 blast)
    have "f y1 = f (p1 x)" using \<open>p1 x = y1\<close> by simp
    also have "\<dots> = p2 x" using hf_comp \<open>x \<in> X\<close> by simp
    finally have "f y1 = p2 x" .
    hence "g (f y1) = g (p2 x)" by simp
    also have "\<dots> = p1 x" using hg_comp \<open>x \<in> X\<close> by simp
    finally show "g (f y1) = y1" using \<open>p1 x = y1\<close> by simp
  qed
  have hf_inj: "inj_on f Y1"
  proof (rule inj_onI)
    fix y1 y1' assume "y1 \<in> Y1" "y1' \<in> Y1" "f y1 = f y1'"
    have "g (f y1) = y1" using hgf_id \<open>y1 \<in> Y1\<close> by simp
    have "g (f y1') = y1'" using hgf_id \<open>y1' \<in> Y1\<close> by simp
    from \<open>f y1 = f y1'\<close> have "g (f y1) = g (f y1')" by simp
    thus "y1 = y1'" using \<open>g (f y1) = y1\<close> \<open>g (f y1') = y1'\<close> by simp
  qed
  have "bij_betw f Y1 Y2" unfolding bij_betw_def using hf_inj hf_surj by simp
  \<comment> \<open>Bijective quotient map = homeomorphism.\<close>
  from top1_bij_quotient_map_on_imp_homeomorphism_on[OF hf_quot this]
  show ?thesis by (by100 blast)
qed

\<comment> \<open>Elementary operations preserve quotient\\_of\\_scheme\\_on for the SAME space.
   If Y is a quotient of scheme s, and s → t via an elementary operation,
   then Y is also a quotient of scheme t (same polygon, adjusted vertex labeling).\<close>
lemma elementary_operation_preserves_quotient:
  assumes "top1_quotient_of_scheme_on Y TY s"
      and "top1_elementary_scheme_operation s t"
  shows "top1_quotient_of_scheme_on Y TY t"
  sorry \<comment> \<open>For each elementary operation, the same polygon P with adjusted vertex positions
     satisfies all quotient\\_of\\_scheme\\_on conditions for the new scheme t.
     rotate: shift vertex indices. invert: reverse vertex order.
     relabel/flip\\_label: rename/flip labels (doesn't change polygon).
     cancel/uncancel: fold/unfold polygon.
     cut\\_paste/cut\\_paste2/cut\\_paste\\_opp: rearrange polygon via cut-flip-paste.\<close>

\<comment> \<open>Two convex n-gons in R² are homeomorphic via a boundary-preserving map.
   The homeomorphism maps vertex i of P1 to vertex i of P2, and maps each edge linearly.\<close>
lemma convex_polygon_homeomorphism:
  assumes "top1_is_polygonal_region_on P1 n" and "top1_is_polygonal_region_on P2 n"
  shows "\<exists>\<phi>. top1_homeomorphism_on P1
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P1)
      P2
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P2) \<phi>"
  sorry \<comment> \<open>Construct \\<phi> by radial projection from centroid: for each direction, map the
     boundary point of P1 to the corresponding boundary point of P2 (same angular position
     relative to vertex ordering). Continuous and bijective between compact Hausdorff spaces
     \\<Rightarrow> homeomorphism.\<close>

\<comment> \<open>Quotient-of-scheme uniqueness: any two quotient spaces of the same scheme are homeomorphic.
   Proof: both are quotients of convex n-gons by the same identification pattern.
   The n-gons are homeomorphic (convex compact in R²), and the homeomorphism respects
   the boundary identifications. So the quotient spaces are homeomorphic.\<close>
lemma scheme_quotient_uniqueness:
  assumes "is_topology_on_strict Y1 TY1" and "is_topology_on_strict Y2 TY2"
      and "top1_quotient_of_scheme_on Y1 TY1 scheme"
      and "top1_quotient_of_scheme_on Y2 TY2 scheme"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  \<comment> \<open>Extract polygon data for both quotients.\<close>
  from assms(3) obtain P1 q1 vx1 vy1 where
      hP1: "top1_is_polygonal_region_on P1 (length scheme)"
      and hq1: "top1_quotient_map_on P1
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P1) Y1 TY1 q1"
    unfolding top1_quotient_of_scheme_on_def by (by5000 auto)
  from assms(4) obtain P2 q2 vx2 vy2 where
      hP2: "top1_is_polygonal_region_on P2 (length scheme)"
      and hq2: "top1_quotient_map_on P2
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P2) Y2 TY2 q2"
    unfolding top1_quotient_of_scheme_on_def by (by5000 auto)
  \<comment> \<open>Get homeomorphism \\<phi>: P1 \\<to> P2 from convex\\_polygon\\_homeomorphism.\<close>
  from convex_polygon_homeomorphism[OF hP1 hP2]
  obtain \<phi> where h\<phi>: "top1_homeomorphism_on P1
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P1) P2
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P2) \<phi>"
    by (by100 blast)
  \<comment> \<open>q2 \\<circ> \\<phi>: P1 \\<to> Y2 is a quotient map with same fibres as q1.
     Apply quotient\\_same\\_fibres\\_homeomorphic to get Y1 \\<cong> Y2.\<close>
  show ?thesis sorry
qed

\<comment> \<open>Scheme rotation preserves quotient type: quotient(u@v) \\<cong> quotient(v@u).
   The edge identifications are the same up to cyclic shift.\<close>
lemma scheme_rotate_homeomorphic:
  assumes "is_topology_on_strict Y1 TY1" and "is_topology_on_strict Y2 TY2"
      and "top1_quotient_of_scheme_on Y1 TY1 (u @ v)"
      and "top1_quotient_of_scheme_on Y2 TY2 (v @ u)"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  \<comment> \<open>Book proof (Munkres \\<S>76 operation iv): "Permute. Renumbering the vertices of the
     polygonal region so as to begin with a different vertex does not affect the quotient space."
     Formal argument: u@v and v@u have the same length n = |u|+|v|. Define shifted vertex
     positions vx'(i) = vx((i+|u|) mod n). The polygon P is unchanged (same convex hull).
     The quotient map q is unchanged. The scheme (v@u)!i = (u@v)!((i+|u|) mod n), so all
     identification conditions transfer. Apply quotient\\_same\\_fibres\\_homeomorphic.\<close>
  let ?n = "length u + length v"
  \<comment> \<open>Strategy: Show Y1 is ALSO a quotient of v@u (same polygon, rotated vertices).
     Then Y1 and Y2 are both quotients of v@u. Apply scheme\\_quotient\\_uniqueness.\<close>
  \<comment> \<open>The scheme v@u has the same length.\<close>
  have hlen_eq: "length (v @ u) = ?n" by simp
  have hlen_uv: "length (u @ v) = ?n" by simp
  \<comment> \<open>Key: (v@u)!i = (u@v)!((i + length u) mod n) for i < n.\<close>
  have hshift: "\<forall>i < ?n. (v @ u) ! i = (u @ v) ! ((i + length u) mod ?n)"
  proof (intro allI impI)
    fix i assume "i < ?n"
    show "(v @ u) ! i = (u @ v) ! ((i + length u) mod ?n)"
    proof (cases "i < length v")
      case True
      hence "(v @ u) ! i = v ! i" by (simp add: nth_append)
      moreover have "(i + length u) mod ?n = i + length u"
        using True by simp
      moreover have "(u @ v) ! (i + length u) = v ! i"
        using True by (simp add: nth_append)
      ultimately show ?thesis by simp
    next
      case False
      hence "i \<ge> length v" by linarith
      hence "(v @ u) ! i = u ! (i - length v)" by (simp add: nth_append)
      moreover have "(i + length u) mod ?n = i - length v"
      proof -
        have "i + length u = ?n + (i - length v)" using \<open>i \<ge> length v\<close> by linarith
        hence "(i + length u) mod ?n = (?n + (i - length v)) mod ?n"
          by (metis add.commute)
        also have "\<dots> = (i - length v) mod ?n" by simp
        also have "\<dots> = i - length v"
          using \<open>i < ?n\<close> \<open>i \<ge> length v\<close> by simp
        finally show ?thesis .
      qed
      moreover have "(u @ v) ! (i - length v) = u ! (i - length v)"
      proof -
        have "i - length v < length u" using \<open>i < ?n\<close> \<open>i \<ge> length v\<close> by linarith
        thus ?thesis by (simp add: nth_append)
      qed
      ultimately show ?thesis by simp
    qed
  qed
  \<comment> \<open>Y1 is also a quotient of v@u (same polygon, rotated vertex numbering).\<close>
  have hY1_vu: "top1_quotient_of_scheme_on Y1 TY1 (v @ u)"
    by (rule elementary_operation_preserves_quotient[OF assms(3) top1_elementary_scheme_operation.rotate])
  \<comment> \<open>Both Y1 and Y2 are quotients of v@u. Apply scheme\\_quotient\\_uniqueness.\<close>
  show ?thesis by (rule scheme_quotient_uniqueness[OF assms(1) assms(2) hY1_vu assms(4)])
qed

\<comment> \<open>Scheme cancellation preserves quotient type: quotient(u@[a,a\\<inverse>]@v) \\<cong> quotient(u@v).
   Folding two adjacent inverse edges doesn't change the quotient space.\<close>
lemma scheme_cancel_homeomorphic:
  assumes "is_topology_on_strict Y1 TY1" and "is_topology_on_strict Y2 TY2"
      and "top1_quotient_of_scheme_on Y1 TY1 (u @ [a, top1_inverse_edge a] @ v)"
      and "top1_quotient_of_scheme_on Y2 TY2 (u @ v)"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  \<comment> \<open>Book proof (Munkres \\<S>76 operation vi): "Cancel. Replace w = y0 a a\\<inverse> y1 by y0 y1."
     Formal: The (n+2)-gon for u@[a,a\\<inverse>]@v has two adjacent edges labeled a, a\\<inverse>.
     These edges are identified in the quotient. "Folding" the polygon along these edges
     gives an n-gon. The fold map is a quotient map P(n+2) \\<to> P(n) that preserves
     all other edge identifications.
     Compose: q1: P(n+2) \\<to> Y1, fold: P(n+2) \\<to> P(n), and q2\\<inverse>: P(n) \\<to> Y2.
     The composition gives a homeomorphism Y1 \\<to> Y2.\<close>
  \<comment> \<open>Step 1: Extract quotient data from assms(3) and assms(4).\<close>
  \<comment> \<open>Step 2: Construct the fold map \\<phi>: P(n+2) \\<to> P(n) that collapses the two
     cancelling edges (edge |u| and edge |u|+1) to a single vertex.\<close>
  \<comment> \<open>Step 3: Show q2 \\<circ> \\<phi> has the same fibres as q1 on P(n+2).
     Interior points: \\<phi> is bijective away from the fold line.
     Boundary: the cancelling edges are already identified by q1 (same label, inverse direction).
     Other edges: \\<phi> maps them linearly, preserving the identification pattern.\<close>
  \<comment> \<open>Step 4: Apply quotient\\_same\\_fibres\\_homeomorphic (or Theorem 22.2 directly).\<close>
  show ?thesis sorry
qed

\<comment> \<open>Scheme inversion preserves quotient type: quotient(w) \\<cong> quotient(rev(map inverse w)).
   Reflecting the polygon preserves the quotient space.\<close>
lemma scheme_invert_homeomorphic:
  assumes "is_topology_on_strict Y1 TY1" and "is_topology_on_strict Y2 TY2"
      and "top1_quotient_of_scheme_on Y1 TY1 w"
      and "top1_quotient_of_scheme_on Y2 TY2 (rev (map top1_inverse_edge w))"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  \<comment> \<open>Book proof (Munkres \\<S>76 operation v): "Flip. Flipping the polygonal region over.
     The order of the vertices is reversed, and so is the orientation of each edge."
     Formal: Reflecting the polygon (reversing vertex order) gives a valid quotient
     of rev(map inverse w). Then scheme\\_quotient\\_uniqueness gives Y1 \\<cong> Y2.\<close>
  have hY1_inv: "top1_quotient_of_scheme_on Y1 TY1 (rev (map top1_inverse_edge w))"
    by (rule elementary_operation_preserves_quotient[OF assms(3) top1_elementary_scheme_operation.invert])
  \<comment> \<open>Originally: Extract (P,q,vx,vy) from assms(3). Define reflected vertices:
       vx'(i) = vx(n-1-i), vy'(i) = vy(n-1-i) (reverse order).
       The same polygon P (reflection is a homeomorphism), same quotient map q.
       Edge i in the reflected scheme = inverse of edge (n-1-i) in w.
       All conditions transfer via the reversal.\<close>
  show ?thesis by (rule scheme_quotient_uniqueness[OF assms(1) assms(2) hY1_inv assms(4)])
qed
  \<comment> \<open>Reflect the polygon (reverse vertex order + flip orientations).
     The reflection map commutes with the identification.\<close>

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
    proof -
      fix s t and Y1 :: "'x set" and TY1 and Y2 :: "'x set" and TY2
      assume hop: "top1_elementary_scheme_operation s t"
          and hY1: "is_topology_on_strict Y1 TY1" and hY2: "is_topology_on_strict Y2 TY2"
          and hs: "top1_quotient_of_scheme_on Y1 TY1 s"
          and ht: "top1_quotient_of_scheme_on Y2 TY2 t"
      show "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h" using hop
      proof (cases rule: top1_elementary_scheme_operation.cases)
        case (rotate u v)
        then show ?thesis using scheme_rotate_homeomorphic[OF hY1 hY2] hs ht by simp
      next
        case (cancel u a v)
        then show ?thesis using scheme_cancel_homeomorphic[OF hY1 hY2] hs ht by simp
      next
        case (uncancel u v a)
        \<comment> \<open>Uncancel = reverse of cancel. s = u@v, t = u@[a, a\\<inverse>]@v.\<close>
        have hs2: "top1_quotient_of_scheme_on Y1 TY1 (u @ v)" using hs uncancel by simp
        have ht2: "top1_quotient_of_scheme_on Y2 TY2 (u @ [a, top1_inverse_edge a] @ v)"
          using ht uncancel by simp
        from scheme_cancel_homeomorphic[OF hY2 hY1 ht2 hs2]
        obtain h where "top1_homeomorphism_on Y2 TY2 Y1 TY1 h" by (by100 blast)
        from homeomorphism_inverse[OF this]
        show ?thesis by (by100 blast)
      next
        case invert
        then show ?thesis using scheme_invert_homeomorphic[OF hY1 hY2] hs ht by simp
      next
        case (relabel old new)
        \<comment> \<open>Relabeling preserves the quotient: same polygon, same q, renamed labels.
           Y1 is also a quotient of the relabeled scheme. Then scheme\\_quotient\\_uniqueness.\<close>
        have hop_relabel: "top1_elementary_scheme_operation s (map (\<lambda>(l,b). (if l = old then new else l, b)) s)"
          by (rule top1_elementary_scheme_operation.relabel)
        have hY1_relabel: "top1_quotient_of_scheme_on Y1 TY1 (map (\<lambda>(l,b). (if l = old then new else l, b)) s)"
          by (rule elementary_operation_preserves_quotient[OF hs hop_relabel])
        moreover have "top1_quotient_of_scheme_on Y2 TY2 (map (\<lambda>(l,b). (if l = old then new else l, b)) s)"
          using ht relabel by simp
        ultimately show ?thesis using scheme_quotient_uniqueness[OF hY1 hY2] by (by100 blast)
      next
        case (flip_label a)
        \<comment> \<open>Flipping orientations: same polygon, same q, flipped edge directions.
           Y1 is also a quotient of the flipped scheme.\<close>
        have "top1_quotient_of_scheme_on Y1 TY1 (map (\<lambda>(l,bo). (l, if l = a then \<not>bo else bo)) s)"
          by (rule elementary_operation_preserves_quotient[OF hs top1_elementary_scheme_operation.flip_label])
        moreover have "top1_quotient_of_scheme_on Y2 TY2 (map (\<lambda>(l,bo). (l, if l = a then \<not>bo else bo)) s)"
          using ht flip_label by simp
        ultimately show ?thesis using scheme_quotient_uniqueness[OF hY1 hY2] by (by100 blast)
      next
        case (cut_paste u1 a u2 u3)
        \<comment> \<open>Cut-and-repaste: \\<S>76 Theorem 76.1. Cut, flip, paste preserves quotient.\<close>
        have "top1_quotient_of_scheme_on Y1 TY1
            (u1 @ [(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3)"
        proof -
          have "top1_quotient_of_scheme_on Y1 TY1 (u1 @ [(a, True)] @ u2 @ [(a, True)] @ u3)"
            using hs cut_paste by simp
          from elementary_operation_preserves_quotient[OF this top1_elementary_scheme_operation.cut_paste[of u1 a u2 u3]]
          show ?thesis .
        qed
        moreover have "top1_quotient_of_scheme_on Y2 TY2
            (u1 @ [(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3)"
          using ht cut_paste by simp
        ultimately show ?thesis using scheme_quotient_uniqueness[OF hY1 hY2] by (by100 blast)
      next
        case (cut_paste2 u0 a u1 u2 b)
        have "top1_quotient_of_scheme_on Y1 TY1
            ([(b, True)] @ u2 @ [(b, True)] @ u1 @ rev (map top1_inverse_edge u0))"
        proof -
          have "top1_quotient_of_scheme_on Y1 TY1 (u0 @ [(a, True)] @ u1 @ [(a, True)] @ u2)"
            using hs cut_paste2 by simp
          from elementary_operation_preserves_quotient[OF this top1_elementary_scheme_operation.cut_paste2[of u0 a u1 u2 b]]
          show ?thesis .
        qed
        moreover have "top1_quotient_of_scheme_on Y2 TY2
            ([(b, True)] @ u2 @ [(b, True)] @ u1 @ rev (map top1_inverse_edge u0))"
          using ht cut_paste2 by simp
        ultimately show ?thesis using scheme_quotient_uniqueness[OF hY1 hY2] by (by100 blast)
      next
        case (cut_paste_opp u0 u1 a u2 u3)
        have "top1_quotient_of_scheme_on Y1 TY1
            (u0 @ [(a, True)] @ u2 @ [(a, False)] @ u1 @ u3)"
        proof -
          have "top1_quotient_of_scheme_on Y1 TY1 (u0 @ u1 @ [(a, True)] @ u2 @ [(a, False)] @ u3)"
            using hs cut_paste_opp by simp
          from elementary_operation_preserves_quotient[OF this top1_elementary_scheme_operation.cut_paste_opp[of u0 u1 a u2 u3]]
          show ?thesis .
        qed
        moreover have "top1_quotient_of_scheme_on Y2 TY2
            (u0 @ [(a, True)] @ u2 @ [(a, False)] @ u1 @ u3)"
          using ht cut_paste_opp by simp
        ultimately show ?thesis using scheme_quotient_uniqueness[OF hY1 hY2] by (by100 blast)
      qed
    qed
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
  \<comment> \<open>Translation preserves polygonal region.\<close>
  have htranslate_poly: "\<And>P n c. top1_is_polygonal_region_on P n \<Longrightarrow>
      top1_is_polygonal_region_on ((\<lambda>(x,y). (x + c, y)) ` P) n"
  proof -
    fix P :: "(real \<times> real) set" and n :: nat and c :: real
    assume hP: "top1_is_polygonal_region_on P n"
    from hP obtain vx vy where hn: "n \<ge> 3"
        and hdist: "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)"
        and hndeg: "\<forall>k<n. \<not> (\<exists>coeffs. (\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0)
                          \<and> coeffs k = 0 \<and> (\<Sum>i<n. coeffs i) = 1
                          \<and> vx k = (\<Sum>i<n. coeffs i * vx i) \<and> vy k = (\<Sum>i<n. coeffs i * vy i))"
        and hP_eq: "P = {(x, y) | x y. \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
                       \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
      unfolding top1_is_polygonal_region_on_def by (by5000 auto)
    \<comment> \<open>Translated vertices.\<close>
    define vx' where "vx' i = vx i + c" for i
    define vy' where "vy' = vy"
    \<comment> \<open>Key arithmetic: \\<Sum>(\\<alpha>*(vx+c)) = \\<Sum>(\\<alpha>*vx) + c when \\<Sum>\\<alpha>=1.\<close>
    have hsum_dist0: "\<And>coeffs :: nat \<Rightarrow> real. (\<Sum>i<n. coeffs i) = 1 \<Longrightarrow>
        (\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i) + c"
    proof -
      fix coeffs :: "nat \<Rightarrow> real" assume "(\<Sum>i<n. coeffs i) = 1"
      have "(\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i + coeffs i * c)"
        by (rule sum.cong) (simp_all add: distrib_left)
      also have "\<dots> = (\<Sum>i<n. coeffs i * vx i) + (\<Sum>i<n. coeffs i * c)"
        by (rule sum.distrib)
      also have "(\<Sum>i<n. coeffs i * c) = c * (\<Sum>i<n. coeffs i)"
        by (simp add: sum_distrib_left mult.commute)
      also have "\<dots> = c" using \<open>(\<Sum>i<n. coeffs i) = 1\<close> by simp
      finally show "(\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i) + c" .
    qed
    \<comment> \<open>Vertex distinctness.\<close>
    have hdist': "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> (vx' i, vy' i) \<noteq> (vx' j, vy' j)"
      using hdist unfolding vx'_def vy'_def by simp
    \<comment> \<open>Non-degeneracy.\<close>
    have hndeg': "\<forall>k<n. \<not> (\<exists>coeffs. (\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0)
                        \<and> coeffs k = 0 \<and> (\<Sum>i<n. coeffs i) = 1
                        \<and> vx' k = (\<Sum>i<n. coeffs i * vx' i) \<and> vy' k = (\<Sum>i<n. coeffs i * vy' i))"
    proof (intro allI impI notI)
      fix k assume "k < n"
      assume "\<exists>coeffs. (\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0 \<and> (\<Sum>i<n. coeffs i) = 1
          \<and> vx' k = (\<Sum>i<n. coeffs i * vx' i) \<and> vy' k = (\<Sum>i<n. coeffs i * vy' i)"
      then obtain coeffs where hc: "(\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0)" "coeffs k = 0"
          "(\<Sum>i<n. coeffs i) = 1"
          "vx' k = (\<Sum>i<n. coeffs i * vx' i)" "vy' k = (\<Sum>i<n. coeffs i * vy' i)"
        by (by100 blast)
      \<comment> \<open>From hsum\\_dist: \\<Sum>(coeffs * vx') = \\<Sum>(coeffs * vx) + c.\<close>
      have "(\<Sum>i<n. coeffs i * vx' i) = (\<Sum>i<n. coeffs i * vx i) + c"
        unfolding vx'_def using hsum_dist0[OF hc(3)] by simp
      hence "vx k = (\<Sum>i<n. coeffs i * vx i)"
        using hc(4) unfolding vx'_def by linarith
      moreover have "vy k = (\<Sum>i<n. coeffs i * vy i)"
        using hc(5) unfolding vy'_def by simp
      moreover have "(\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0 \<and> (\<Sum>i<n. coeffs i) = 1"
        using hc(1) hc(2) hc(3) by (by100 blast)
      ultimately have "\<exists>coeffs. (\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0 \<and> (\<Sum>i<n. coeffs i) = 1
          \<and> vx k = (\<Sum>i<n. coeffs i * vx i) \<and> vy k = (\<Sum>i<n. coeffs i * vy i)"
        by (by100 blast)
      with hndeg[rule_format, OF \<open>k < n\<close>] show False by simp
    qed
    \<comment> \<open>Translated hull.\<close>
    have hP'_eq: "(\<lambda>(x,y). (x + c, y)) ` P = {(x, y) | x y. \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0)
                  \<and> (\<Sum>i<n. coeffs i) = 1
                  \<and> x = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)}"
    proof -
      have hsum_dist: "\<And>coeffs. (\<Sum>i<n. coeffs i) = 1 \<Longrightarrow>
          (\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i) + c"
      proof -
        fix coeffs :: "nat \<Rightarrow> real" assume hsum1: "(\<Sum>i<n. coeffs i) = 1"
        have "(\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i + coeffs i * c)"
          by (rule sum.cong) (simp_all add: distrib_left)
        also have "\<dots> = (\<Sum>i<n. coeffs i * vx i) + (\<Sum>i<n. coeffs i * c)"
          by (rule sum.distrib)
        also have "(\<Sum>i<n. coeffs i * c) = c * (\<Sum>i<n. coeffs i)"
          by (simp add: sum_distrib_left mult.commute)
        also have "\<dots> = c" using \<open>(\<Sum>i<n. coeffs i) = 1\<close> by simp
        finally show "(\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i) + c" .
      qed
      show ?thesis
      proof
        show "(\<lambda>(x, y). (x + c, y)) ` P \<subseteq>
            {(x, y) |x y. \<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
                \<and> x = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)}"
        proof
          fix p assume "p \<in> (\<lambda>(x, y). (x + c, y)) ` P"
          then obtain x y where hp: "p = (x + c, y)" "(x, y) \<in> P" by (by100 force)
          then obtain coeffs where hc: "(\<forall>i<n. 0 \<le> coeffs i)" "(\<Sum>i<n. coeffs i) = 1"
              "x = (\<Sum>i<n. coeffs i * vx i)" "y = (\<Sum>i<n. coeffs i * vy i)"
            unfolding hP_eq by (by100 auto)
          have hxc: "x + c = (\<Sum>i<n. coeffs i * vx' i)" unfolding vx'_def using hsum_dist[OF hc(2)] hc(3) by simp
          have hyv: "y = (\<Sum>i<n. coeffs i * vy' i)" unfolding vy'_def using hc(4) by simp
          have "\<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
              \<and> (x + c) = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)"
            using hc(1) hc(2) hxc hyv by (by100 blast)
          thus "p \<in> {(x, y) |x y. \<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
              \<and> x = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)}"
            using hp(1) by (by100 blast)
        qed
      next
        show "{(x, y) |x y. \<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
                \<and> x = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)}
              \<subseteq> (\<lambda>(x, y). (x + c, y)) ` P"
        proof
          fix p assume "p \<in> {(x, y) |x y. \<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
              \<and> x = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)}"
          then obtain x' y coeffs where hp: "p = (x', y)"
              and hc: "(\<forall>i<n. 0 \<le> coeffs i)" "(\<Sum>i<n. coeffs i) = 1"
              "x' = (\<Sum>i<n. coeffs i * vx' i)" "y = (\<Sum>i<n. coeffs i * vy' i)" by (by5000 auto)
          have "x' = (\<Sum>i<n. coeffs i * vx i) + c"
            using hc(3) unfolding vx'_def using hsum_dist[OF hc(2)] by simp
          hence hx_orig: "x' - c = (\<Sum>i<n. coeffs i * vx i)" by simp
          have hy_orig: "y = (\<Sum>i<n. coeffs i * vy i)" using hc(4) unfolding vy'_def by simp
          have "(x' - c, y) \<in> P" unfolding hP_eq using hc(1) hc(2) hx_orig hy_orig by (by100 blast)
          hence "(x' - c + c, y) = p" using hp by simp
          hence "(\<lambda>(x,y). (x+c, y)) (x' - c, y) = p" by simp
          thus "p \<in> (\<lambda>(x, y). (x + c, y)) ` P" using \<open>(x' - c, y) \<in> P\<close> by (by100 force)
        qed
      qed
    qed
    show "top1_is_polygonal_region_on ((\<lambda>(x,y). (x + c, y)) ` P) n"
      unfolding top1_is_polygonal_region_on_def
      using hn hdist' hndeg' hP'_eq by (by100 blast)
  qed
  \<comment> \<open>Step 4: Construct disjoint copies of standard simplex in R², one per triangle.\<close>
  \<comment> \<open>Enumerate the triangles.\<close>
  obtain tlist where htlist: "set tlist = \<T>0" "distinct tlist"
    using finite_distinct_list[OF h\<T>0(1)] by (by100 blast)
  let ?m = "length tlist"
  have h\<T>0_ne: "\<T>0 \<noteq> {}"
  proof -
    have "X \<noteq> {}" using assms(1) unfolding top1_is_surface_on_def by (by100 blast)
    thus ?thesis using h\<T>0(2) by (by100 blast)
  qed
  have hm_pos: "?m > 0"
    using h\<T>0_ne htlist(1) by (by100 force)
  \<comment> \<open>Place the i-th simplex copy at position (3*i, 0) to ensure disjointness.\<close>
  define \<Delta>copy :: "nat \<Rightarrow> (real \<times> real) set" where
    "\<Delta>copy i = (\<lambda>(x,y). (x + 3 * real i, y)) ` top1_standard_simplex" for i
  let ?\<T> = "{\<Delta>copy i | i. i < ?m}"
  \<comment> \<open>Define q: on \\<Delta>copy i, apply h0(tlist!i) composed with the inverse translation.\<close>
  define q_map :: "(real \<times> real) \<Rightarrow> 'a" where
    "q_map p = (let i = (SOME i. i < ?m \<and> p \<in> \<Delta>copy i) in
                h0 (tlist ! i) ((fst p - 3 * real i, snd p)))" for p
  \<comment> \<open>Show the required properties.\<close>
  have "finite ?\<T>"
  proof -
    have "?\<T> = (\<lambda>i. \<Delta>copy i) ` {..<?m}" by (by100 blast)
    thus ?thesis by simp
  qed
  moreover have "?\<T> \<noteq> {}"
  proof -
    have "\<Delta>copy 0 \<in> ?\<T>" using hm_pos by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  moreover have "\<forall>T \<in> ?\<T>. top1_is_polygonal_region_on T 3"
  proof (intro ballI)
    fix T assume "T \<in> ?\<T>"
    then obtain i where "i < ?m" "T = \<Delta>copy i" by (by100 blast)
    \<comment> \<open>\\<Delta>copy i = translation of standard simplex. Translation preserves polygonal region.
       The standard simplex has vertices (vx j, vy j) for j < 3 (from h\\_simplex\\_poly).
       \\<Delta>copy i has vertices (vx j + 3*i, vy j). Same convex hull structure.\<close>
    show "top1_is_polygonal_region_on T 3"
      using \<open>T = \<Delta>copy i\<close> unfolding \<Delta>copy_def
      using htranslate_poly[OF h_simplex_poly] by simp
  qed
  moreover have "\<forall>T \<in> ?\<T>. top1_continuous_map_on T
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) X TX q_map" sorry
  moreover have "(\<Union>T\<in>?\<T>. q_map ` T) = X" sorry
  moreover have "\<forall>U. U \<subseteq> X \<longrightarrow>
      (U \<in> TX \<longleftrightarrow> (\<forall>T\<in>?\<T>. {p\<in>T. q_map p \<in> U} \<in>
        subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T))" sorry
  ultimately show ?thesis by (by100 blast)
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
  \<comment> \<open>Step 1: By Theorem 78.1, X is a quotient of finitely many triangular regions.\<close>
  from Theorem_78_1_triangulable_surface[OF assms(1) assms(3)]
  obtain \<T> q_tri where h\<T>: "finite \<T>" "\<T> \<noteq> {}"
      "\<forall>T \<in> \<T>. top1_is_polygonal_region_on T 3"
      "\<forall>T \<in> \<T>. top1_continuous_map_on T
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) X TX q_tri"
      "(\<Union>T\<in>\<T>. q_tri ` T) = X"
      "\<forall>U. U \<subseteq> X \<longrightarrow>
          (U \<in> TX \<longleftrightarrow> (\<forall>T\<in>\<T>. {p\<in>T. q_tri p \<in> U} \<in>
              subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T))"
    by (by100 auto)
  \<comment> \<open>Step 2: Iteratively paste triangles along shared edges using Theorem 76.1 (\\<S>76).
     Book proof: "As long as two regions have edges bearing the same label, we can
     paste them together. Eventually either one has a single polygon (theorem proved)
     or several polygons with no shared labels. The latter gives a disconnected space,
     contradicting X connected."
     Formally: induction on card(\\<T>). If card = 1: done. If card > 1: find two regions
     sharing a label, paste them (§76.1), reducing card by 1. Apply IH.\<close>
  show ?thesis
    sorry \<comment> \<open>Induction on card(\\<T>). At each step: find shared edge label between two regions
       (guaranteed by X connected). Paste them (Theorem 76.1). Result: fewer regions, same X.
       When card = 1: X is quotient of a single polygon. Done.\<close>
qed

section \<open>\<S>77 The Classification Theorem\<close>

\<comment> \<open>Lemma 77.1 Step 1, subcase y2 = []: a y1 a ~ aa y1\\<inverse>.
   Sequence: rotate \\<to> invert \\<to> flip\\_label a.
   Requires: a does not appear in y1 (from proper scheme).\<close>
lemma Lemma_77_1_step1_y2_empty:
  assumes "\<forall>e \<in> set y1. fst e \<noteq> a"
  shows "top1_scheme_equiv
      ([(a, True)] @ y1 @ [(a, True)])
      ([(a, True), (a, True)] @ rev (map top1_inverse_edge y1))"
proof -
  \<comment> \<open>Step 1: Rotate: [(a,T)] @ y1 @ [(a,T)] \\<to> y1 @ [(a,T),(a,T)].\<close>
  have h1: "top1_elementary_scheme_operation
      ([(a, True)] @ (y1 @ [(a, True)]))
      ((y1 @ [(a, True)]) @ [(a, True)])"
    by (rule top1_elementary_scheme_operation.rotate)
  \<comment> \<open>Step 2: Invert: y1 @ [(a,T),(a,T)] \\<to> [(a,F),(a,F)] @ inv(y1).\<close>
  have h2: "top1_elementary_scheme_operation
      (y1 @ [(a, True), (a, True)])
      (rev (map top1_inverse_edge (y1 @ [(a, True), (a, True)])))"
    by (rule top1_elementary_scheme_operation.invert)
  \<comment> \<open>Simplify: rev(map inv (y1 @ [(a,T),(a,T)])) = [(a,F),(a,F)] @ rev(map inv y1).\<close>
  have h2_simp: "rev (map top1_inverse_edge (y1 @ [(a, True), (a, True)]))
      = [(a, False), (a, False)] @ rev (map top1_inverse_edge y1)"
    unfolding top1_inverse_edge_def by simp
  \<comment> \<open>Step 3: flip\\_label a: [(a,F),(a,F)] @ inv(y1) \\<to> [(a,T),(a,T)] @ inv(y1).
     (Since a not in y1, flip\\_label only affects the two a-edges.)\<close>
  have h3: "top1_elementary_scheme_operation
      ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))
      (map (\<lambda>(l,b). (l, if l = a then \<not>b else b))
           ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1)))"
    by (rule top1_elementary_scheme_operation.flip_label)
  have h3_simp: "map (\<lambda>(l,b). (l, if l = a then \<not>b else b))
      ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))
      = [(a, True), (a, True)] @ rev (map top1_inverse_edge y1)"
  proof -
    have "map (\<lambda>(l,b). (l, if l = a then \<not>b else b)) [(a, False), (a, False)]
        = [(a, True), (a, True)]" by simp
    moreover have "map (\<lambda>(l,b). (l, if l = a then \<not>b else b)) (rev (map top1_inverse_edge y1))
        = rev (map top1_inverse_edge y1)"
    proof (rule map_idI)
      fix e assume "e \<in> set (rev (map top1_inverse_edge y1))"
      hence "e \<in> set (map top1_inverse_edge y1)" by simp
      then obtain e0 where "e0 \<in> set y1" "e = top1_inverse_edge e0" by (by100 auto)
      hence "fst e = fst e0" unfolding top1_inverse_edge_def by (by100 simp)
      have "fst e0 \<noteq> a" using assms \<open>e0 \<in> set y1\<close> by (by100 blast)
      hence "fst e \<noteq> a" using \<open>fst e = fst e0\<close> by simp
      thus "(case e of (l, b) \<Rightarrow> (l, if l = a then \<not> b else b)) = e"
        using \<open>fst e \<noteq> a\<close> by (cases e) simp
    qed
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>Chain: w \\<to> w1 \\<to> w2 \\<to> w3.\<close>
  \<comment> \<open>Chain the 3 operations via rtranclp.\<close>
  have step1: "top1_scheme_equiv ([(a, True)] @ y1 @ [(a, True)]) (y1 @ [(a, True), (a, True)])"
    unfolding top1_scheme_equiv_def using h1 by simp
  have step2: "top1_scheme_equiv (y1 @ [(a, True), (a, True)])
      ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))"
    unfolding top1_scheme_equiv_def using h2 h2_simp by simp
  have step3: "top1_scheme_equiv ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))
      ([(a, True), (a, True)] @ rev (map top1_inverse_edge y1))"
    unfolding top1_scheme_equiv_def using h3 h3_simp by simp
  \<comment> \<open>Chain: step1 \\<to> step2 \\<to> step3.\<close>
  from step1 step2 have "top1_scheme_equiv ([(a, True)] @ y1 @ [(a, True)])
      ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))"
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
  from this step3 show ?thesis
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
qed

\<comment> \<open>Lemma 77.1 (Munkres): If w = [y0] a [y1] a [y2] (proper scheme with a appearing twice
   with same exponent), then w ~ aa [y0 y1\\<inverse> y2].\<close>
lemma Lemma_77_1_projective_collection:
  assumes "\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> a"
      and "\<exists>b::'a. b \<noteq> a \<and> (\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> b)"
  shows "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      ([(a, True), (a, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
proof (cases "y0 = []")
  case True
  \<comment> \<open>Step 1: y0 empty. Show a y1 a y2 ~ aa y1\\<inverse> y2.\<close>
  show ?thesis
  proof (cases "y1 = []")
    case True
    \<comment> \<open>y1 = []: a a y2 ~ aa y2. Trivially same (reflexivity).\<close>
    show ?thesis using \<open>y0 = []\<close> True unfolding top1_scheme_equiv_def by simp
  next
    case False
    show ?thesis
    proof (cases "y2 = []")
      case True
      \<comment> \<open>y2 = []: a y1 a ~ aa y1\\<inverse>. Use Lemma\\_77\\_1\\_step1\\_y2\\_empty.\<close>
      have "\<forall>e \<in> set y1. fst e \<noteq> a" using assms by (by100 blast)
      from Lemma_77_1_step1_y2_empty[OF this]
      show ?thesis using \<open>y0 = []\<close> True by simp
    next
      case False2: False
      \<comment> \<open>Both y1, y2 non-empty: direct from cut\\_paste operation.\<close>
      have "top1_elementary_scheme_operation
          ([] @ [(a, True)] @ y1 @ [(a, True)] @ y2)
          ([] @ [(a, True), (a, True)] @ rev (map top1_inverse_edge y1) @ y2)"
        by (rule top1_elementary_scheme_operation.cut_paste)
      hence "top1_scheme_equiv
          ([(a, True)] @ y1 @ [(a, True)] @ y2)
          ([(a, True), (a, True)] @ rev (map top1_inverse_edge y1) @ y2)"
        unfolding top1_scheme_equiv_def by simp
      thus ?thesis using \<open>y0 = []\<close> by simp
    qed
  qed
next
  case False
  \<comment> \<open>Step 2: y0 non-empty. Book proof (Munkres Figure 77.2):
     y0 a y1 a y2 \\<sim> b y2 b (y1 y0\\<inverse>) \\<sim> bb y2\\<inverse> y1 y0\\<inverse> \\<sim> aa y0 y1\\<inverse> y2.\<close>
  \<comment> \<open>Choose a fresh label b \\<noteq> a (exists because labels are from an infinite type).\<close>
  obtain b :: 'a where hb: "b \<noteq> a" "\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> b"
    using assms(2) by (by100 blast)
  \<comment> \<open>Step 2a: y0 a y1 a y2 \\<sim> b y2 b (y1 y0\\<inverse>) via cut\\_paste2.\<close>
  have step2a: "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      ([(b, True)] @ y2 @ [(b, True)] @ y1 @ rev (map top1_inverse_edge y0))"
    unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.cut_paste2[of y0 a y1 y2 b] by simp
  \<comment> \<open>Step 2b: b y2 b (y1 y0\\<inverse>) \\<sim> bb y2\\<inverse> y1 y0\\<inverse> via cut\\_paste (Step 1).\<close>
  have step2b: "top1_scheme_equiv
      ([(b, True)] @ y2 @ [(b, True)] @ y1 @ rev (map top1_inverse_edge y0))
      ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))"
    unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.cut_paste[of "[]" b y2 "y1 @ rev (map top1_inverse_edge y0)"]
    by simp
  \<comment> \<open>Step 2c: bb y2\\<inverse> y1 y0\\<inverse> \\<sim> (y0 y1\\<inverse> y2) b\\<inverse> b\\<inverse> via invert.\<close>
  have step2c: "top1_scheme_equiv
      ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))
      (y0 @ rev (map top1_inverse_edge y1) @ y2 @ [(b, False), (b, False)])"
  proof -
    have "top1_elementary_scheme_operation
        ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))
        (rev (map top1_inverse_edge ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))))"
      by (rule top1_elementary_scheme_operation.invert)
    moreover have "rev (map top1_inverse_edge ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0)))
        = y0 @ rev (map top1_inverse_edge y1) @ y2 @ [(b, False), (b, False)]"
    proof -
      have hinv_inv: "\<And>x. top1_inverse_edge (top1_inverse_edge x) = x"
        unfolding top1_inverse_edge_def by (by100 simp)
      have hmap_inv_inv: "\<And>xs :: ('a \<times> bool) list. map top1_inverse_edge (map top1_inverse_edge xs) = xs"
        by (simp add: hinv_inv map_idI)
      have hrev_inv: "\<And>xs :: ('a \<times> bool) list. map top1_inverse_edge (rev (map top1_inverse_edge xs)) = rev xs"
      proof -
        fix xs :: "('a \<times> bool) list"
        have "map top1_inverse_edge (rev (map top1_inverse_edge xs))
            = rev (map top1_inverse_edge (map top1_inverse_edge xs))"
          by (simp add: rev_map)
        also have "\<dots> = rev xs" using hmap_inv_inv by simp
        finally show "map top1_inverse_edge (rev (map top1_inverse_edge xs)) = rev xs" .
      qed
      have hcomp_id: "top1_inverse_edge \<circ> top1_inverse_edge = id"
      proof (rule ext)
        fix x show "(top1_inverse_edge \<circ> top1_inverse_edge) x = id x" using hinv_inv by simp
      qed
      have hmap_comp_id: "\<And>xs :: ('a \<times> bool) list. map (top1_inverse_edge \<circ> top1_inverse_edge) xs = xs"
      proof -
        fix xs :: "('a \<times> bool) list"
        have "map (top1_inverse_edge \<circ> top1_inverse_edge) xs = map id xs"
          by (rule arg_cong[of _ _ "\<lambda>f. map f xs"]) (rule hcomp_id)
        thus "map (top1_inverse_edge \<circ> top1_inverse_edge) xs = xs" by simp
      qed
      show ?thesis
        by (simp add: rev_map hmap_comp_id hrev_inv top1_inverse_edge_def)
    qed
    ultimately show ?thesis unfolding top1_scheme_equiv_def by simp
  qed
  \<comment> \<open>Step 2d: rotate to b\\<inverse> b\\<inverse> (y0 y1\\<inverse> y2).\<close>
  have step2d: "top1_scheme_equiv
      (y0 @ rev (map top1_inverse_edge y1) @ y2 @ [(b, False), (b, False)])
      ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
    unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.rotate[of
        "y0 @ rev (map top1_inverse_edge y1) @ y2" "[(b, False), (b, False)]"]
    by simp
  \<comment> \<open>Step 2e: flip\\_label b: b\\<inverse>b\\<inverse> \\<to> bb.\<close>
  have step2e: "top1_scheme_equiv
      ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
      ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
  proof -
    have "top1_elementary_scheme_operation
        ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        (map (\<lambda>(l, bo). (l, if l = b then \<not> bo else bo))
             ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2))"
      by (rule top1_elementary_scheme_operation.flip_label)
    moreover have "map (\<lambda>(l, bo). (l, if l = b then \<not> bo else bo))
        ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        = [(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2"
    proof -
      have "\<And>xs. (\<forall>e \<in> set xs. fst e \<noteq> b) \<Longrightarrow>
          map (\<lambda>(l, bo). (l, if l = b then \<not> bo else bo)) xs = xs"
        by (rule map_idI) (by100 auto)
      moreover have "\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> b" using hb(2) by (by100 blast)
      moreover have "\<forall>e \<in> set (rev (map top1_inverse_edge y1)). fst e \<noteq> b"
        using hb(2) unfolding top1_inverse_edge_def by (by100 auto)
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis unfolding top1_scheme_equiv_def by simp
  qed
  \<comment> \<open>Step 2f: relabel b \\<to> a.\<close>
  have step2f: "top1_scheme_equiv
      ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
      ([(a, True), (a, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
  proof -
    have "top1_elementary_scheme_operation
        ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        (map (\<lambda>(l, bo). (if l = b then a else l, bo))
             ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2))"
      by (rule top1_elementary_scheme_operation.relabel)
    moreover have "map (\<lambda>(l, bo). (if l = b then a else l, bo))
        ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        = [(a, True), (a, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2"
    proof -
      have hmap_relabel: "\<And>xs :: ('a \<times> bool) list. (\<forall>e \<in> set xs. fst e \<noteq> b) \<Longrightarrow>
          map (\<lambda>(l, bo). (if l = b then a else l, bo)) xs = xs"
        by (rule map_idI) (by100 auto)
      have "\<forall>e \<in> set y0. fst e \<noteq> b" using hb(2) by (by100 blast)
      have "\<forall>e \<in> set (rev (map top1_inverse_edge y1)). fst e \<noteq> b"
        using hb(2) unfolding top1_inverse_edge_def by (by100 auto)
      have "\<forall>e \<in> set y2. fst e \<noteq> b" using hb(2) by (by100 blast)
      show ?thesis
        using hmap_relabel[OF \<open>\<forall>e \<in> set y0. fst e \<noteq> b\<close>]
            hmap_relabel[OF \<open>\<forall>e \<in> set (rev (map top1_inverse_edge y1)). fst e \<noteq> b\<close>]
            hmap_relabel[OF \<open>\<forall>e \<in> set y2. fst e \<noteq> b\<close>]
        by simp
    qed
    ultimately show ?thesis unfolding top1_scheme_equiv_def by simp
  qed
  \<comment> \<open>Chain all steps.\<close>
  \<comment> \<open>Chain all steps via transitivity.\<close>
  from step2a step2b have s_ab: "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))"
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
  from s_ab step2c have s_abc: "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      (y0 @ rev (map top1_inverse_edge y1) @ y2 @ [(b, False), (b, False)])"
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
  from s_abc step2d have s_abcd: "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
  from s_abcd step2e have s_abcde: "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
  from s_abcde step2f show ?thesis
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
qed

\<comment> \<open>Lemma 77.3 (Munkres): If w = [w0] a b [w1] a\\<inverse> b\\<inverse> [w2] (torus-type with commutator),
   then w ~ (aba\\<inverse>b\\<inverse>) [w0 w1 w2].\<close>
lemma Lemma_77_3_torus_extraction:
  shows "top1_scheme_equiv
      (w0 @ [(a, True), (b, True)] @ w1 @ [(a, False), (b, False)] @ w2)
      ([(a, True), (b, True), (a, False), (b, False)] @ w0 @ w1 @ w2)"
  sorry \<comment> \<open>Book proof (Munkres \\<S>77 Lemma 77.3): Three cuttings and pastings.
     Step 1: cut\\_paste\\_opp on a moves w0's tail past a⁻¹.
     Step 2: cut\\_paste\\_opp rearranges to get b and a⁻¹ adjacent.
     Step 3: cut\\_paste\\_opp rearranges to get the full commutator block.
     Step 4: rotate to bring commutator to front.
     Each step uses cut\\_paste\\_opp + relabel. Very elaborate (book says "most elaborate").\<close>

\<comment> \<open>Main normal form theorem (Munkres \\<S>77 Theorem 77.5 core):
   Every proper labelling scheme is equivalent to one of:
   (1) aa\\<inverse>bb\\<inverse> (sphere, length 4)
   (2) a1a1...amam (projective, m \\<ge> 1)
   (3) a1b1a1\\<inverse>b1\\<inverse>...anbnanbnan\\<inverse>bn\\<inverse> (torus, n \\<ge> 1)\<close>
lemma scheme_normal_form:
  fixes scheme :: "(nat \<times> bool) list"
  assumes "length scheme \<ge> 4"
      and "\<forall>label. card {i. i < length scheme \<and> fst (scheme ! i) = label} \<in> {0, 2}"
      \<comment> \<open>Proper: each label appears exactly 0 or 2 times.\<close>
  shows "(\<exists>a b. a \<noteq> b \<and> top1_scheme_equiv scheme [(a, True), (a, False), (b, True), (b, False)])
       \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_scheme_equiv scheme w)
       \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_scheme_equiv scheme w)"
  sorry \<comment> \<open>Munkres \\<S>77: Induction on length of scheme.
     Step 1 (projective type): Use Lemma 77.1 to collect all same-exponent pairs.
     Step 2 (torus type): Use Lemma 77.3 to extract commutator blocks.
     Step 3: Handle base cases (length 4).
     Each step uses elementary operations (rotate, cancel, cut, paste, relabel, flip).\<close>

\<comment> \<open>Predicate: a scheme w is the standard n-fold torus scheme
   a1 b1 a1\\<inverse> b1\\<inverse> ... an bn an\\<inverse> bn\\<inverse> (4n edges).\<close>
definition top1_is_torus_scheme :: "(nat \<times> bool) list \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_is_torus_scheme w n \<longleftrightarrow> n > 0 \<and> w = top1_n_torus_scheme n"

\<comment> \<open>Predicate: a scheme w is the standard m-fold projective scheme
   a1 a1 a2 a2 ... am am (2m edges).\<close>
definition top1_is_projective_scheme :: "(nat \<times> bool) list \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_is_projective_scheme w m \<longleftrightarrow> m > 0 \<and> w = top1_m_projective_scheme m"

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
  \<comment> \<open>Step 1: Extract edge scheme from the polygonal quotient.
     The polygon P has n edges. The quotient map q identifies boundary edges in pairs.
     For each pair of identified edges: assign a shared label. The direction (same or opposite)
     determines the exponent (True/False). This gives the edge scheme.
     The scheme satisfies quotient\\_of\\_scheme\\_on by construction.\<close>
  obtain scheme :: "(nat \<times> bool) list" where hsch: "top1_quotient_of_scheme_on X TX scheme"
    sorry \<comment> \<open>Extract scheme from polygonal quotient. Construction:
       1. P has n vertices. Edge i goes from vertex i to vertex (i+1) mod n.
       2. q identifies edge i with some edge j (possibly reversed).
       3. Assign label k to both edges i and j. Direction: True if same, False if reversed.
       4. The resulting list of (label, direction) pairs is the scheme.
       5. Verify all conditions of quotient\\_of\\_scheme\\_on (P is the polygon, q is the map,
          vertex positions are the polygon's vertices).\<close>
  \<comment> \<open>Step 2: Apply elementary operations (Theorem 76) to reduce scheme.
     Operations: relabel, rotate, cancel, cut, paste, flip.
     Step 2a: Bring all vertices to one equivalence class.
     Step 2b: Collect pairs aa into adjacent positions (projective type).
     Step 2c: Pair remaining letters into commutator blocks aba\<inverse>b\<inverse> (torus type).\<close>
  \<comment> \<open>NOTE: top1\\_is\\_torus\\_scheme, top1\\_is\\_projective\\_scheme now defined (\\<S>77 section).
     top1\\_scheme\\_equiv = rtranclp of elementary operations (defined before \\<S>76).\<close>
  have hreduced: "(\<exists>w. scheme = w \<and> (\<forall>a\<in>set w. snd a) \<and> length w = 0)
      \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n
            \<and> top1_scheme_equiv scheme w)
      \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m
            \<and> top1_scheme_equiv scheme w)"
    sorry \<comment> \<open>From scheme\\_normal\\_form: scheme is proper (each label twice) and length \\<ge> 4.
       Properness follows from the polygonal quotient structure. Length \\<ge> 4 from surface.
       scheme\\_normal\\_form gives equivalence to sphere/torus/projective normal form.\<close>
  \<comment> \<open>Step 3: Each normal form corresponds to the standard surface.
     - Empty/sphere: cancellation gives S² (a@a⁻¹@b@b⁻¹ with cancellation).
     - Torus scheme: the standard n-torus IS the quotient of this scheme
       (by definition top1\\_is\\_n\\_fold\\_torus\\_on). scheme\\_quotient\\_uniqueness gives homeo.
     - Projective scheme: similarly, top1\\_is\\_m\\_fold\\_projective\\_on.
     Plus: Theorem 76 preserves quotient homeomorphism type, so scheme\\_equiv gives homeo.\<close>
  show ?thesis
  proof -
    \<comment> \<open>If scheme\\_equiv to a normal form: Theorem 76 gives homeomorphism preservation.
       The normal form's quotient = the standard surface. So X \\<cong> standard surface.\<close>
    from hreduced show ?thesis
    proof (elim disjE exE conjE)
      \<comment> \<open>Case 1: scheme is empty (length 0) — gives S².\<close>
      fix w assume "scheme = w" "\<forall>a\<in>set w. snd a" "length w = 0"
      show ?thesis sorry
    next
      \<comment> \<open>Case 2: scheme \\<sim> torus normal form.\<close>
      fix n w assume "n > 0" "top1_is_torus_scheme w n" "top1_scheme_equiv scheme w"
      \<comment> \<open>X is quotient of scheme. scheme \\<sim> w. Theorem 76 (iterated) gives X \\<cong> quotient(w).
         quotient(w) = quotient(torus\\_scheme n) = n-fold torus by definition.\<close>
      show ?thesis sorry
    next
      \<comment> \<open>Case 3: scheme \\<sim> projective normal form.\<close>
      fix m w assume "m > 0" "top1_is_projective_scheme w m" "top1_scheme_equiv scheme w"
      show ?thesis sorry
    qed
  qed
qed


end
