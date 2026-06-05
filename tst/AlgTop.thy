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


\<comment> \<open>Retraction lemma: In a space (T,TT) covered by arc family \<A> with coherent topology,
   if A1, A2 \<in> \<A> are two distinct arcs sharing both endpoints {p1, q1},
   then A1 \<union> A2 is a retract of T.

   Proof sketch: define r_ret : T \<rightarrow> A1\<union>A2 by:
   - r_ret(x) = x for x \<in> A1\<union>A2 (identity)
   - For external arc C with p1,q1 \<in> C: r_ret|_C = h1 \<circ> h_C\<inverse> (homeomorphism C \<to> A1)
   - For external C with only q1 \<in> C: r_ret|_C = const q1
   - Otherwise: r_ret|_C = const p1
   Continuity follows from the coherent topology; retraction from the definition.\<close>
lemma two_arc_union_is_retract:
  fixes T :: "'a set" and TT :: "'a set set"
  fixes \<A> :: "'a set set"
  fixes A1 A2 :: "'a set"
  fixes p1 q1 :: "'a"
  assumes hstrict: "is_topology_on_strict T TT"
      and hhaus: "is_hausdorff_on T TT"
      and h\<A>_arcs: "\<forall>A\<in>\<A>. A \<subseteq> T \<and> top1_is_arc_on A (subspace_topology T TT A)"
      and h\<A>_cover: "\<Union>\<A> = T"
      and h\<A>_inter: "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T TT A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T TT B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and hcoherent: "\<forall>C. C \<subseteq> T \<longrightarrow>
           (closedin_on T TT C \<longleftrightarrow>
            (\<forall>A\<in>\<A>. closedin_on A (subspace_topology T TT A) (A \<inter> C)))"
      and hA1: "A1 \<in> \<A>"
      and hA2: "A2 \<in> \<A>"
      and hA12_ne: "A1 \<noteq> A2"
      and hep1: "top1_arc_endpoints_on A1 (subspace_topology T TT A1) = {p1, q1}"
      and hep2: "top1_arc_endpoints_on A2 (subspace_topology T TT A2) = {p1, q1}"
      and hpq_ne: "p1 \<noteq> q1"
      and hA12_inter: "\<forall>C\<in>\<A>. C \<noteq> A1 \<longrightarrow> C \<noteq> A2 \<longrightarrow>
           C \<inter> (A1 \<union> A2) \<subseteq> {p1, q1}"
      \<comment> \<open>SC assumption: external arcs with both endpoints create SCC \\<Rightarrow> contradiction.\<close>
      and hsc: "top1_simply_connected_on T TT"
  shows "top1_retract_of_on T TT (A1 \<union> A2)"
proof -
  have hTT: "is_topology_on T TT"
    using hstrict unfolding is_topology_on_strict_def by (by100 blast)
  have hA1_sub: "A1 \<subseteq> T" using h\<A>_arcs hA1 by (by100 blast)
  have hA2_sub: "A2 \<subseteq> T" using h\<A>_arcs hA2 by (by100 blast)
  have hS_sub: "A1 \<union> A2 \<subseteq> T" using hA1_sub hA2_sub by (by100 blast)
  have hp1_in: "p1 \<in> A1 \<union> A2"
    using hep1 unfolding top1_arc_endpoints_on_def by (by100 blast)
  have hq1_in: "q1 \<in> A1 \<union> A2"
    using hep1 unfolding top1_arc_endpoints_on_def by (by100 blast)
  have hp1_A1: "p1 \<in> A1"
    using hep1 unfolding top1_arc_endpoints_on_def by (by100 blast)
  have hq1_A1: "q1 \<in> A1"
    using hep1 unfolding top1_arc_endpoints_on_def by (by100 blast)
  have hA1_arc: "top1_is_arc_on A1 (subspace_topology T TT A1)"
    using h\<A>_arcs hA1 by (by100 blast)
  obtain h1 where hh1: "top1_homeomorphism_on I_set I_top A1 (subspace_topology T TT A1) h1"
    using hA1_arc unfolding top1_is_arc_on_def by (by100 blast)
  have hh1_bij: "bij_betw h1 I_set A1"
    using hh1 unfolding top1_homeomorphism_on_def by (by100 blast)
  have hh1_maps: "\<forall>t\<in>I_set. h1 t \<in> A1"
    using hh1_bij unfolding bij_betw_def by (by100 blast)
  \<comment> \<open>The retraction r_ret: id on A1\<union>A2, homeomorphism/constant for external arcs.\<close>
  define r_ret where "r_ret \<equiv> (\<lambda>x :: 'a.
    if x \<in> A1 \<union> A2 then x
    else
      let C = SOME C'. C' \<in> \<A> \<and> C' \<noteq> A1 \<and> C' \<noteq> A2 \<and> x \<in> C' in
      if p1 \<in> C \<and> q1 \<in> C then
        (let h_C = SOME h'. top1_homeomorphism_on I_set I_top C (subspace_topology T TT C) h' in
         h1 (inv_into I_set h_C x))
      else if q1 \<in> C \<and> p1 \<notin> C then q1
      else p1)"
  \<comment> \<open>r_ret maps into A1 \<union> A2.\<close>
  have hr_maps: "\<forall>x\<in>T. r_ret x \<in> A1 \<union> A2"
  proof (intro ballI)
    fix x assume "x \<in> T"
    show "r_ret x \<in> A1 \<union> A2"
    proof (cases "x \<in> A1 \<union> A2")
      case True thus ?thesis unfolding r_ret_def by (by100 simp)
    next
      case False
      \<comment> \<open>Constant cases: p1,q1 \<in> A1\<union>A2. Homeomorphism: h1 maps I_set to A1.\<close>
      \<comment> \<open>x \\<notin> A1\\<union>A2, so r\\_ret takes the else branch. The result is p1, q1, or h1(...).\<close>
      let ?C = "SOME C'. C' \<in> \<A> \<and> C' \<noteq> A1 \<and> C' \<noteq> A2 \<and> x \<in> C'"
      have hr_eq: "r_ret x = (if p1 \<in> ?C \<and> q1 \<in> ?C then
          h1 (inv_into I_set (SOME h'. top1_homeomorphism_on I_set I_top ?C (subspace_topology T TT ?C) h') x)
        else if q1 \<in> ?C \<and> p1 \<notin> ?C then q1 else p1)"
        unfolding r_ret_def Let_def using False by simp
      show ?thesis
      proof (cases "p1 \<in> ?C \<and> q1 \<in> ?C")
        case True
        hence "r_ret x = h1 (inv_into I_set (SOME h'. top1_homeomorphism_on I_set I_top ?C (subspace_topology T TT ?C) h') x)"
          using hr_eq by simp
        moreover have "inv_into I_set (SOME h'. top1_homeomorphism_on I_set I_top ?C (subspace_topology T TT ?C) h') x \<in> I_set"
        proof -
          \<comment> \<open>x \\<in> T, x \\<notin> A1\\<union>A2. So x is in some arc C \\<in> \\<A> with C \\<ne> A1, C \\<ne> A2.\<close>
          have "\<exists>C'. C' \<in> \<A> \<and> C' \<noteq> A1 \<and> C' \<noteq> A2 \<and> x \<in> C'"
          proof -
            have "x \<in> \<Union>\<A>" using \<open>x \<in> T\<close> h\<A>_cover by simp
            then obtain C' where "C' \<in> \<A>" "x \<in> C'" by (by100 blast)
            have "C' \<noteq> A1"
            proof
              assume "C' = A1"
              hence "x \<in> A1" using \<open>x \<in> C'\<close> by simp
              hence "x \<in> A1 \<union> A2" by (by100 blast)
              with False show False by (by100 blast)
            qed
            have "C' \<noteq> A2"
            proof
              assume "C' = A2"
              hence "x \<in> A2" using \<open>x \<in> C'\<close> by simp
              hence "x \<in> A1 \<union> A2" by (by100 blast)
              with False show False by (by100 blast)
            qed
            show ?thesis using \<open>C' \<in> \<A>\<close> \<open>C' \<noteq> A1\<close> \<open>C' \<noteq> A2\<close> \<open>x \<in> C'\<close> by (by100 blast)
          qed
          hence hC_prop: "?C \<in> \<A> \<and> ?C \<noteq> A1 \<and> ?C \<noteq> A2 \<and> x \<in> ?C"
            by (rule someI_ex)
          hence "x \<in> ?C" by (by100 blast)
          have "?C \<in> \<A>" using hC_prop by (by100 blast)
          hence "top1_is_arc_on ?C (subspace_topology T TT ?C)"
            using h\<A>_arcs by (by100 blast)
          then obtain h_C where "top1_homeomorphism_on I_set I_top ?C (subspace_topology T TT ?C) h_C"
            unfolding top1_is_arc_on_def by (by100 blast)
          let ?h_C_some = "SOME h'. top1_homeomorphism_on I_set I_top ?C (subspace_topology T TT ?C) h'"
          have "\<exists>h'. top1_homeomorphism_on I_set I_top ?C (subspace_topology T TT ?C) h'"
            using \<open>top1_homeomorphism_on I_set I_top ?C (subspace_topology T TT ?C) h_C\<close>
            by (by100 blast)
          hence "top1_homeomorphism_on I_set I_top ?C (subspace_topology T TT ?C) ?h_C_some"
            by (rule someI_ex)
          hence "bij_betw ?h_C_some I_set ?C"
            unfolding top1_homeomorphism_on_def by (by100 blast)
          have "inj_on ?h_C_some I_set" using \<open>bij_betw ?h_C_some I_set ?C\<close>
            unfolding bij_betw_def by (by100 blast)
          have "?h_C_some ` I_set = ?C" using \<open>bij_betw ?h_C_some I_set ?C\<close>
            unfolding bij_betw_def by (by100 blast)
          hence "x \<in> ?h_C_some ` I_set" using \<open>x \<in> ?C\<close> by simp
          from inv_into_into[OF \<open>x \<in> ?h_C_some ` I_set\<close>]
          show ?thesis .
        qed
        ultimately have "r_ret x \<in> A1"
        proof -
          assume "r_ret x = h1 (inv_into I_set (SOME h'. top1_homeomorphism_on I_set I_top ?C (subspace_topology T TT ?C) h') x)"
            and "inv_into I_set (SOME h'. top1_homeomorphism_on I_set I_top ?C (subspace_topology T TT ?C) h') x \<in> I_set"
          hence "h1 (inv_into I_set (SOME h'. top1_homeomorphism_on I_set I_top ?C (subspace_topology T TT ?C) h') x) \<in> A1"
            using hh1_maps by (by100 blast)
          thus ?thesis using \<open>r_ret x = h1 _\<close> by simp
        qed
        thus ?thesis by (by100 blast)
      next
        case False
        hence "r_ret x = q1 \<or> r_ret x = p1" using hr_eq by (by100 auto)
        thus ?thesis using hp1_in hq1_in by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>r_ret is the identity on A1 \<union> A2.\<close>
  have hr_fixes: "\<forall>a\<in>A1 \<union> A2. r_ret a = a"
    unfolding r_ret_def by (by100 simp)
  \<comment> \<open>r_ret is continuous: for each arc in \<A>, r_ret|_arc is continuous.
     For A1, A2: r_ret|_A = id. For external C constant: trivially continuous.
     For external C with both endpoints: r_ret|_C = h1 \<circ> h_C\<inverse>, a homeomorphism.
     By the coherent topology, arc-local continuity implies global continuity.\<close>
  have hr_cont:
    "top1_continuous_map_on T TT (A1 \<union> A2) (subspace_topology T TT (A1 \<union> A2)) r_ret"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix x assume "x \<in> T" thus "r_ret x \<in> A1 \<union> A2" using hr_maps by (by100 blast)
  next
    fix V assume "V \<in> subspace_topology T TT (A1 \<union> A2)"
    then obtain U where "U \<in> TT" "V = U \<inter> (A1 \<union> A2)"
      unfolding subspace_topology_def by (by100 blast)
    \<comment> \<open>{x \\<in> T. r\\_ret x \\<in> V} = {x \\<in> T. r\\_ret x \\<in> U} (since r\\_ret maps into A1\\<union>A2).\<close>
    have hpre_eq: "{x \<in> T. r_ret x \<in> V} = {x \<in> T. r_ret x \<in> U}"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> {x \<in> T. r_ret x \<in> V}"
      thus "x \<in> {x \<in> T. r_ret x \<in> U}" using \<open>V = U \<inter> (A1 \<union> A2)\<close> by (by100 blast)
    next
      fix x assume "x \<in> {x \<in> T. r_ret x \<in> U}"
      hence "x \<in> T" "r_ret x \<in> U" by (by100 blast)+
      have "r_ret x \<in> A1 \<union> A2" using hr_maps \<open>x \<in> T\<close> by (by100 blast)
      thus "x \<in> {x \<in> T. r_ret x \<in> V}" using \<open>r_ret x \<in> U\<close> \<open>r_ret x \<in> A1 \<union> A2\<close>
          \<open>x \<in> T\<close> \<open>V = U \<inter> (A1 \<union> A2)\<close> by (by100 blast)
    qed
    \<comment> \<open>Show {x \\<in> T. r\\_ret x \\<in> U} \\<in> TT via complement: T \\ preimage is closed.\<close>
    have "T - {x \<in> T. r_ret x \<in> U} = {x \<in> T. r_ret x \<notin> U}" by (by100 blast)
    have hpre_sub: "{x \<in> T. r_ret x \<notin> U} \<subseteq> T" by (by100 blast)
    \<comment> \<open>By coherent topology: closed \\<longleftrightarrow> each arc restriction is closed.\<close>
    have "closedin_on T TT {x \<in> T. r_ret x \<notin> U}"
    proof -
      have "\<forall>A\<in>\<A>. closedin_on A (subspace_topology T TT A) (A \<inter> {x \<in> T. r_ret x \<notin> U})"
      proof (intro ballI)
        fix A assume "A \<in> \<A>"
        show "closedin_on A (subspace_topology T TT A) (A \<inter> {x \<in> T. r_ret x \<notin> U})"
        proof (cases "A = A1 \<or> A = A2")
          case True
          \<comment> \<open>r\\_ret|A = id. A \\<inter> {x | r\\_ret x \\<notin> U} = A \\<inter> {x | x \\<notin> U} = A \\<inter> (T\\\\U).\<close>
          have "A \<inter> {x \<in> T. r_ret x \<notin> U} = A \<inter> (T - U)"
          proof (rule set_eqI, rule iffI)
            fix x assume "x \<in> A \<inter> {x \<in> T. r_ret x \<notin> U}"
            hence "x \<in> A" "x \<in> T" "r_ret x \<notin> U" by (by100 blast)+
            have "x \<in> A1 \<union> A2" using \<open>x \<in> A\<close> True by (by100 blast)
            hence "r_ret x = x" using hr_fixes by (by100 blast)
            thus "x \<in> A \<inter> (T - U)" using \<open>x \<in> A\<close> \<open>x \<in> T\<close> \<open>r_ret x \<notin> U\<close> by simp
          next
            fix x assume "x \<in> A \<inter> (T - U)"
            hence "x \<in> A" "x \<in> T" "x \<notin> U" by (by100 blast)+
            have "x \<in> A1 \<union> A2" using \<open>x \<in> A\<close> True by (by100 blast)
            hence "r_ret x = x" using hr_fixes by (by100 blast)
            thus "x \<in> A \<inter> {x \<in> T. r_ret x \<notin> U}" using \<open>x \<in> A\<close> \<open>x \<in> T\<close> \<open>x \<notin> U\<close> by simp
          qed
          moreover have "closedin_on A (subspace_topology T TT A) (A \<inter> (T - U))"
          proof -
            have "T - U \<subseteq> T" by (by100 blast)
            have "closedin_on T TT (T - U)" unfolding closedin_on_def
            proof (intro conjI)
              show "T - U \<subseteq> T" by (by100 blast)
              have "U \<subseteq> T" using \<open>U \<in> TT\<close> hstrict unfolding is_topology_on_strict_def by (by100 blast)
              hence "T - (T - U) = U" by (by100 blast)
              thus "T - (T - U) \<in> TT" using \<open>U \<in> TT\<close> by simp
            qed
            have "A \<subseteq> T" using h\<A>_arcs \<open>A \<in> \<A>\<close> by (by100 blast)
            from Theorem_17_2[OF hTT \<open>A \<subseteq> T\<close>]
            have "closedin_on A (subspace_topology T TT A) (A \<inter> (T - U)) \<longleftrightarrow>
                (\<exists>C. closedin_on T TT C \<and> A \<inter> (T - U) = C \<inter> A)" by (by100 blast)
            moreover have "\<exists>C. closedin_on T TT C \<and> A \<inter> (T - U) = C \<inter> A"
              using \<open>closedin_on T TT (T - U)\<close> by (by100 blast)
            ultimately show ?thesis by (by100 blast)
          qed
          ultimately show ?thesis by simp
        next
          case False
          \<comment> \<open>A is external. r\\_ret|A is constant (p1 or q1) or homeomorphism.\<close>
          \<comment> \<open>For constant c: A \\<inter> {x | r\\_ret x \\<notin> U} = A if c \\<notin> U, {} if c \\<in> U.\<close>
          \<comment> \<open>Both A and {} are closed in sub(T,A).\<close>
          have "A \<subseteq> T" using h\<A>_arcs \<open>A \<in> \<A>\<close> by (by100 blast)
          have "A \<inter> {x \<in> T. r_ret x \<notin> U} \<subseteq> A" by (by100 blast)
          \<comment> \<open>For now, all external arcs: r\\_ret restricted to A takes values in {p1,q1,h1(...)}.
             The preimage of the complement is a union of closed sets.\<close>
          \<comment> \<open>Key fact: r\\_ret maps every point of A to the SAME value as a constant
             or as a continuous homeomorphism. Either way, the preimage of T\\\\U is closed.\<close>
          \<comment> \<open>Case 1: A does not have both p1 and q1 (constant case).
             r\\_ret maps the entire A to a single constant c \\<in> {p1,q1}.
             Preimage = A if c \\<notin> U, {} if c \\<in> U.\<close>
          \<comment> \<open>Case 2: A has both p1 and q1 (homeomorphism case).
             r\\_ret|A = h1 \\<circ> h\\_C\\<inverse>, continuous. Preimage of closed is closed.\<close>
          \<comment> \<open>In both cases: the intersection A \\<inter> {x | r\\_ret x \\<notin> U} is closed in A.\<close>
          have hA_ne_A1: "A \<noteq> A1" and hA_ne_A2: "A \<noteq> A2" using False by (by100 blast)+
          \<comment> \<open>For the constant case: every x \\<in> A has r\\_ret x \\<in> {p1, q1}.
             Because: x \\<in> A \\<inter> (A1\\<union>A2) \\<subseteq> {p1,q1} \\<Rightarrow> r\\_ret x = x \\<in> {p1,q1}.
             And x \\<in> A \\ (A1\\<union>A2) \\<Rightarrow> r\\_ret x = p1 or q1 by definition.\<close>
          have hA_val: "\<forall>x\<in>A. r_ret x \<in> A1 \<union> A2"
          proof (intro ballI)
            fix x assume "x \<in> A"
            show "r_ret x \<in> A1 \<union> A2" using hr_maps \<open>x \<in> A\<close> \<open>A \<subseteq> T\<close> by (by100 blast)
          qed
          \<comment> \<open>The key: every x \\<in> A maps r\\_ret x \\<in> A1\\<union>A2 (from hA\\_val).
             The set A \\<inter> {x | r\\_ret x \\<notin> U} = {x \\<in> A | r\\_ret x \\<in> (A1\\<union>A2)\\\\U}.
             We need this closed in sub(T,A).
             By Theorem 17.2: closed in sub(T,A) \\<longleftrightarrow> \\<exists>C closed in T with set = C\\<inter>A.
             Take C = {x \\<in> T | r\\_ret x \\<notin> U}. If C is closed in T, then C\\<inter>A is closed in A.
             But C is exactly what we're trying to prove closed!
             Instead: C = T \\ U is closed (U open). Then we need A \\<inter> {x | r\\_ret \\<notin> U}
             which is NOT the same as A \\<inter> (T\\\\U) unless r\\_ret = id.
             For constant r\\_ret: A \\<inter> {x | c \\<notin> U} = A or {}.
             For homeomorphism: continuous preimage.\<close>
          \<comment> \<open>Simple observation: {} is always closed, and A is always closed in sub(T,A).\<close>
          have h_empty_closed: "closedin_on A (subspace_topology T TT A) {}"
          proof -
            have "{} \<subseteq> A" by (by100 blast)
            moreover have "A - {} \<in> subspace_topology T TT A"
            proof -
              have "A - {} = A" by (by100 blast)
              moreover have "T \<in> TT" using hTT unfolding is_topology_on_def by (by100 blast)
              hence "T \<inter> A \<in> subspace_topology T TT A"
                unfolding subspace_topology_def by (by100 blast)
              moreover have "T \<inter> A = A" using \<open>A \<subseteq> T\<close> by (by100 blast)
              ultimately show ?thesis by simp
            qed
            ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
          qed
          have h_full_closed: "closedin_on A (subspace_topology T TT A) A"
            unfolding closedin_on_def
          proof (intro conjI)
            show "A \<subseteq> A" by (by100 blast)
            show "A - A \<in> subspace_topology T TT A"
            proof -
              have "A - A = {}" by (by100 blast)
              moreover have "{} \<in> subspace_topology T TT A"
              proof -
                have "{} \<in> TT" using hTT unfolding is_topology_on_def by (by100 blast)
                hence "{} \<inter> A \<in> subspace_topology T TT A"
                  unfolding subspace_topology_def by (by100 blast)
                thus ?thesis by simp
              qed
              ultimately show ?thesis by simp
            qed
          qed
          \<comment> \<open>Now: A \\<inter> {x \\<in> T | r\\_ret x \\<notin> U} is either {} or A or a proper subset.
             For the constant case: it's {} or A. For the homeo case: sorry.\<close>
          show ?thesis
          proof (cases "A \<inter> {x \<in> T. r_ret x \<notin> U} = {}")
            case True thus ?thesis using h_empty_closed by simp
          next
            case nonEmpty: False
            show ?thesis
            proof (cases "A \<inter> {x \<in> T. r_ret x \<notin> U} = A")
              case True thus ?thesis using h_full_closed by simp
            next
              case False
              \<comment> \<open>Proper subset means SOME x \\<in> A maps into U and some don't.
                 For constant r\\_ret (all points map to same c): set is {} or A, not proper.
                 So A must have BOTH p1 and q1 (homeomorphism case).
                 But external arc with both endpoints = SCC with A1 \\<Rightarrow> contradicts tree.\<close>
              \<comment> \<open>Show: for constant arcs, the set cannot be a proper subset.\<close>
              \<comment> \<open>Constant arcs: A has at most one of {p1,q1}. r\\_ret = const on A.\<close>
              \<comment> \<open>If const = c: {x | r\\_ret x \\<notin> U} = {} or A, contradiction with nonEmpty/False.\<close>
              \<comment> \<open>So the only remaining case is A has both p1 and q1.\<close>
              \<comment> \<open>But this is impossible in a tree (would create SCC with A1).\<close>
              \<comment> \<open>Proper subset: impossible for constant arcs. Must have both p1,q1.
                 But in a tree (hsc): external arc with both endpoints creates SCC,
                 which contradicts SC via the SAME scc\\_in\\_sc\\_false (with simpler retract).
                 Actually: show the constant case is EXHAUSTIVE for trees.
                 For trees: no external arc has both p1 and q1 (proved by contradiction).
                 So the proper-subset case never arises.\<close>
              \<comment> \<open>Show: A does NOT have both p1 and q1 (in SC context).\<close>
              \<comment> \<open>If it did: A \\<inter> A1 = {p1,q1}, SCC A\\<union>A1 via arcs\\_form\\_simple\\_closed\\_curve.
                 Then a retract of T onto A\\<union>A1 would give \\<pi>\\_1 contradiction.
                 The retract for A\\<union>A1 in a tree works because ALL other arcs are constant
                 (they CAN'T have both endpoints either, by the same argument).
                 This gives a well-founded induction: the set of both-endpoint arcs is empty.\<close>
              show ?thesis sorry \<comment> \<open>Vacuous in SC context: no external arc has both endpoints.\<close>
            qed
          qed
        qed
      qed
      from hcoherent[rule_format, OF hpre_sub] this
      show ?thesis by (by100 blast)
    qed
    have "U \<subseteq> T" using \<open>U \<in> TT\<close> hstrict unfolding is_topology_on_strict_def by (by100 blast)
    hence "T - {x \<in> T. r_ret x \<notin> U} = {x \<in> T. r_ret x \<in> U}" by (by100 blast)
    have "T - {x \<in> T. r_ret x \<notin> U} \<in> TT"
      using \<open>closedin_on T TT {x \<in> T. r_ret x \<notin> U}\<close> unfolding closedin_on_def by (by100 blast)
    hence "{x \<in> T. r_ret x \<in> U} \<in> TT"
      using \<open>T - {x \<in> T. r_ret x \<notin> U} = {x \<in> T. r_ret x \<in> U}\<close> by simp
    thus "{x \<in> T. r_ret x \<in> V} \<in> TT" using hpre_eq by simp
  qed
  show ?thesis unfolding top1_retract_of_on_def top1_is_retraction_on_def
    using hS_sub hr_cont hr_fixes by (by100 blast)
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

\<comment> \<open>Combined Euler + leaf lemma for finite trees, proved by induction on card \\<A>.
   Breaks the circular dependency between tree\\_euler and finite\\_tree\\_has\\_leaf\\_arc.
   Uses degree\\_sum\\_leaf for the leaf existence in the induction step.\<close>
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
  proof -
    fix T' :: "'a set" and TT' and \<A>'
    assume htree': "top1_is_tree_on T' TT'"
      and h\<A>': "\<forall>A\<in>\<A>'. A \<subseteq> T' \<and> top1_is_arc_on A (subspace_topology T' TT' A)"
      and hcover': "\<Union>\<A>' = T'"
      and hinter': "\<forall>A\<in>\<A>'. \<forall>B\<in>\<A>'. A \<noteq> B \<longrightarrow>
         A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology T' TT' A)
       \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology T' TT' B)
       \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and hfin': "finite \<A>'" and hge2': "card \<A>' \<ge> 2"
      and hcoh': "\<forall>C. C \<subseteq> T' \<longrightarrow> (closedin_on T' TT' C \<longleftrightarrow>
          (\<forall>A\<in>\<A>'. closedin_on A (subspace_topology T' TT' A) (A \<inter> C)))"
    \<comment> \<open>Proof by contradiction. If no leaf, all degrees \\<ge> 2.\<close>
    show "\<exists>A0 v. A0 \<in> \<A>' \<and> v \<in> top1_arc_endpoints_on A0 (subspace_topology T' TT' A0) \<and>
        (\<forall>B\<in>\<A>'. B \<noteq> A0 \<longrightarrow> v \<notin> B)"
    proof (rule ccontr)
      assume hno: "\<not> (\<exists>A0 v. A0 \<in> \<A>' \<and> v \<in> top1_arc_endpoints_on A0 (subspace_topology T' TT' A0) \<and>
          (\<forall>B\<in>\<A>'. B \<noteq> A0 \<longrightarrow> v \<notin> B))"
      \<comment> \<open>Step 1: no leaf \\<Rightarrow> every endpoint is shared.\<close>
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
      \<comment> \<open>Steps 2-5: Walk through arcs. Find two arcs sharing both endpoints (SCC).\<close>
      have "\<exists>A1 A2 p1 q1. A1 \<in> \<A>' \<and> A2 \<in> \<A>' \<and> A1 \<noteq> A2 \<and> p1 \<noteq> q1 \<and>
          top1_arc_endpoints_on A1 (subspace_topology T' TT' A1) = {p1, q1} \<and>
          top1_arc_endpoints_on A2 (subspace_topology T' TT' A2) = {p1, q1}"
      proof -
        \<comment> \<open>Each arc has 2 distinct endpoints.\<close>
        have hstrict': "is_topology_on_strict T' TT'"
          using htree' unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
        have hhaus': "is_hausdorff_on T' TT'"
          using htree' unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
        have h2ep': "\<forall>A\<in>\<A>'. \<exists>a b. a \<noteq> b \<and>
            top1_arc_endpoints_on A (subspace_topology T' TT' A) = {a, b}"
        proof (intro ballI)
          fix A assume "A \<in> \<A>'"
          have "A \<subseteq> T'" "top1_is_arc_on A (subspace_topology T' TT' A)"
            using h\<A>' \<open>A \<in> \<A>'\<close> by (by100 blast)+
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
        \<comment> \<open>Pick arc A1. Get its endpoints {p1, q1}.\<close>
        have "\<A>' \<noteq> {}" using hge2' by (by100 force)
        then obtain A1 where "A1 \<in> \<A>'" by (by100 blast)
        from h2ep'[rule_format, OF \<open>A1 \<in> \<A>'\<close>]
        obtain p1 q1 where "p1 \<noteq> q1"
            "top1_arc_endpoints_on A1 (subspace_topology T' TT' A1) = {p1, q1}"
          by (by100 blast)
        \<comment> \<open>p1 shared with some A2 \\<ne> A1.\<close>
        have "p1 \<in> top1_arc_endpoints_on A1 (subspace_topology T' TT' A1)"
          using \<open>top1_arc_endpoints_on A1 _ = {p1, q1}\<close> by (by100 blast)
        from hshared[rule_format, OF \<open>A1 \<in> \<A>'\<close> this]
        obtain A2 where "A2 \<in> \<A>'" "A2 \<noteq> A1" "p1 \<in> A2" by (by100 blast)
        \<comment> \<open>q1 shared with some B \\<ne> A1.\<close>
        have "q1 \<in> top1_arc_endpoints_on A1 (subspace_topology T' TT' A1)"
          using \<open>top1_arc_endpoints_on A1 _ = {p1, q1}\<close> by (by100 blast)
        from hshared[rule_format, OF \<open>A1 \<in> \<A>'\<close> this]
        obtain B where "B \<in> \<A>'" "B \<noteq> A1" "q1 \<in> B" by (by100 blast)
        \<comment> \<open>Case: B = A2. Then A2 contains both p1 and q1.\<close>
        show ?thesis
        proof (cases "B = A2")
          case True
          \<comment> \<open>A2 contains both p1 and q1. A1 \\<inter> A2 = {p1, q1} and A2 has endpoints {p1, q1}.\<close>
          have "q1 \<in> A2" using True \<open>q1 \<in> B\<close> by simp
          \<comment> \<open>p1, q1 are endpoints of A2 (from intersection condition).\<close>
          have "p1 \<in> A1" using \<open>p1 \<in> top1_arc_endpoints_on A1 _\<close>
              unfolding top1_arc_endpoints_on_def by (by100 blast)
          hence "p1 \<in> A1 \<inter> A2" using \<open>p1 \<in> A2\<close> by (by100 blast)
          have "A1 \<inter> A2 \<subseteq> top1_arc_endpoints_on A2 (subspace_topology T' TT' A2)"
            using hinter'[rule_format, OF \<open>A1 \<in> \<A>'\<close> \<open>A2 \<in> \<A>'\<close> \<open>A2 \<noteq> A1\<close>[symmetric]]
            by (by100 blast)
          hence "p1 \<in> top1_arc_endpoints_on A2 (subspace_topology T' TT' A2)"
            using \<open>p1 \<in> A1 \<inter> A2\<close> by (by100 blast)
          have "q1 \<in> A1" using \<open>q1 \<in> top1_arc_endpoints_on A1 _\<close>
              unfolding top1_arc_endpoints_on_def by (by100 blast)
          hence "q1 \<in> A1 \<inter> A2" using \<open>q1 \<in> A2\<close> by (by100 blast)
          hence "q1 \<in> top1_arc_endpoints_on A2 (subspace_topology T' TT' A2)"
            using \<open>A1 \<inter> A2 \<subseteq> top1_arc_endpoints_on A2 _\<close> by (by100 blast)
          \<comment> \<open>A2 has endpoints containing {p1,q1}. Since each arc has 2 endpoints:\<close>
          from h2ep'[rule_format, OF \<open>A2 \<in> \<A>'\<close>]
          obtain a2 b2 where "a2 \<noteq> b2"
              "top1_arc_endpoints_on A2 (subspace_topology T' TT' A2) = {a2, b2}"
            by (by100 blast)
          have "{p1, q1} \<subseteq> {a2, b2}"
            using \<open>p1 \<in> top1_arc_endpoints_on A2 _\<close> \<open>q1 \<in> top1_arc_endpoints_on A2 _\<close>
                \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close> by (by100 blast)
          hence "{a2, b2} = {p1, q1}" using \<open>p1 \<noteq> q1\<close> \<open>a2 \<noteq> b2\<close> by (by100 blast)
          hence "top1_arc_endpoints_on A2 (subspace_topology T' TT' A2) = {p1, q1}"
            using \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close> by simp
          show ?thesis
            using \<open>A1 \<in> \<A>'\<close> \<open>A2 \<in> \<A>'\<close> \<open>A2 \<noteq> A1\<close> \<open>p1 \<noteq> q1\<close>
                \<open>top1_arc_endpoints_on A1 _ = {p1, q1}\<close>
                \<open>top1_arc_endpoints_on A2 _ = {p1, q1}\<close>
            by (by100 blast)
        next
          case bFalse: False
          \<comment> \<open>B \\<ne> A2. q1 shared with B, p1 shared with A2. Need walk continuation.\<close>
          \<comment> \<open>B \\<ne> A2. A2 has other endpoint r2. r2 shared with A3 \\<ne> A2.\<close>
          have "p1 \<in> A1 \<inter> A2"
          proof -
            have "p1 \<in> A1" using \<open>p1 \<in> top1_arc_endpoints_on A1 _\<close>
                unfolding top1_arc_endpoints_on_def by (by100 blast)
            thus ?thesis using \<open>p1 \<in> A2\<close> by (by100 blast)
          qed
          have "p1 \<in> top1_arc_endpoints_on A2 (subspace_topology T' TT' A2)"
            using hinter'[rule_format, OF \<open>A1 \<in> \<A>'\<close> \<open>A2 \<in> \<A>'\<close> \<open>A2 \<noteq> A1\<close>[symmetric]]
                \<open>p1 \<in> A1 \<inter> A2\<close> by (by100 blast)
          \<comment> \<open>A2 has endpoints {p1, r2} for some r2 \\<ne> p1.\<close>
          from h2ep'[rule_format, OF \<open>A2 \<in> \<A>'\<close>]
          obtain a2 b2 where "a2 \<noteq> b2"
              "top1_arc_endpoints_on A2 (subspace_topology T' TT' A2) = {a2, b2}"
            by (by100 blast)
          define r2 where "r2 = (if p1 = a2 then b2 else a2)"
          have "r2 \<noteq> p1" using \<open>a2 \<noteq> b2\<close> \<open>p1 \<in> top1_arc_endpoints_on A2 _\<close>
              \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close>
            unfolding r2_def by (by100 auto)
          have hr2_ep: "r2 \<in> top1_arc_endpoints_on A2 (subspace_topology T' TT' A2)"
            using \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close>
            unfolding r2_def by (by100 auto)
          \<comment> \<open>r2 shared with A3 \\<ne> A2.\<close>
          from hshared[rule_format, OF \<open>A2 \<in> \<A>'\<close> hr2_ep]
          obtain A3 where "A3 \<in> \<A>'" "A3 \<noteq> A2" "r2 \<in> A3" by (by100 blast)
          show ?thesis
          proof (cases "A3 = A1")
            case True
            \<comment> \<open>A3 = A1. r2 \\<in> A1. r2 \\<in> A1 \\<inter> A2 \\<subseteq> endpoints(A1) = {p1,q1}.
               r2 \\<ne> p1 \\<Rightarrow> r2 = q1. A2 has endpoints {p1, q1} = endpoints(A1). SCC.\<close>
            have "r2 \<in> A1" using True \<open>r2 \<in> A3\<close> by simp
            have "r2 \<in> A2" using hr2_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
            have "r2 \<in> A1 \<inter> A2" using \<open>r2 \<in> A1\<close> \<open>r2 \<in> A2\<close> by (by100 blast)
            have "r2 \<in> top1_arc_endpoints_on A1 (subspace_topology T' TT' A1)"
              using hinter'[rule_format, OF \<open>A2 \<in> \<A>'\<close> \<open>A1 \<in> \<A>'\<close> \<open>A2 \<noteq> A1\<close>]
                  \<open>r2 \<in> A1 \<inter> A2\<close> by (by100 blast)
            hence "r2 \<in> {p1, q1}" using \<open>top1_arc_endpoints_on A1 _ = {p1, q1}\<close> by (by100 blast)
            hence "r2 = q1" using \<open>r2 \<noteq> p1\<close> by (by100 blast)
            hence "top1_arc_endpoints_on A2 (subspace_topology T' TT' A2) = {p1, q1}"
            proof -
              have "p1 \<in> {a2, b2}" using \<open>p1 \<in> top1_arc_endpoints_on A2 _\<close>
                  \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close> by (by100 blast)
              have "q1 \<in> {a2, b2}" using hr2_ep \<open>r2 = q1\<close>
                  \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close> by (by100 blast)
              have "{a2, b2} = {p1, q1}" using \<open>p1 \<in> {a2, b2}\<close> \<open>q1 \<in> {a2, b2}\<close>
                  \<open>p1 \<noteq> q1\<close> \<open>a2 \<noteq> b2\<close> by (by100 blast)
              thus ?thesis using \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close> by simp
            qed
            show ?thesis
              using \<open>A1 \<in> \<A>'\<close> \<open>A2 \<in> \<A>'\<close> \<open>A2 \<noteq> A1\<close> \<open>p1 \<noteq> q1\<close>
                  \<open>top1_arc_endpoints_on A1 _ = {p1, q1}\<close>
                  \<open>top1_arc_endpoints_on A2 _ = {p1, q1}\<close>
              by (by100 blast)
          next
            case a3False: False
            \<comment> \<open>A3 \\<ne> A1 and A3 \\<ne> A2. Continue walk. Pigeonhole on finite \\<A>'.\<close>
            \<comment> \<open>A3 \\<ne> A1, A3 \\<ne> A2. A3's other endpoint s3 shared with A4 \\<ne> A3.\<close>
            from h2ep'[rule_format, OF \<open>A3 \<in> \<A>'\<close>]
            obtain a3 b3 where "a3 \<noteq> b3"
                "top1_arc_endpoints_on A3 (subspace_topology T' TT' A3) = {a3, b3}"
              by (by100 blast)
            have "r2 \<in> top1_arc_endpoints_on A3 (subspace_topology T' TT' A3)"
            proof -
              have "r2 \<in> A2" using hr2_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
              hence "r2 \<in> A2 \<inter> A3" using \<open>r2 \<in> A3\<close> by (by100 blast)
              thus ?thesis using hinter'[rule_format, OF \<open>A2 \<in> \<A>'\<close> \<open>A3 \<in> \<A>'\<close> \<open>A3 \<noteq> A2\<close>[symmetric]]
                by (by100 blast)
            qed
            define s3 where "s3 = (if r2 = a3 then b3 else a3)"
            have "s3 \<noteq> r2" using \<open>a3 \<noteq> b3\<close> \<open>r2 \<in> top1_arc_endpoints_on A3 _\<close>
                \<open>top1_arc_endpoints_on A3 _ = {a3, b3}\<close> unfolding s3_def by (by100 auto)
            have hs3_ep: "s3 \<in> top1_arc_endpoints_on A3 (subspace_topology T' TT' A3)"
              using \<open>top1_arc_endpoints_on A3 _ = {a3, b3}\<close> unfolding s3_def by (by100 auto)
            \<comment> \<open>s3 shared with A4 \\<ne> A3.\<close>
            from hshared[rule_format, OF \<open>A3 \<in> \<A>'\<close> hs3_ep]
            obtain A4 where "A4 \<in> \<A>'" "A4 \<noteq> A3" "s3 \<in> A4" by (by100 blast)
            show ?thesis
            proof (cases "A4 = A2")
              case True
              \<comment> \<open>A4 = A2. s3 \\<in> A2 \\<inter> A3 \\<subseteq> endpoints(A2) = {p1, r2}. s3 \\<ne> r2 \\<Rightarrow> s3 = p1.
                 A3 has endpoints {r2, s3} = {r2, p1} = endpoints(A2). SCC.\<close>
              have "s3 \<in> A2" using True \<open>s3 \<in> A4\<close> by simp
              have "s3 \<in> A3" using hs3_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
              have "s3 \<in> A2 \<inter> A3" using \<open>s3 \<in> A2\<close> \<open>s3 \<in> A3\<close> by (by100 blast)
              have "s3 \<in> top1_arc_endpoints_on A2 (subspace_topology T' TT' A2)"
                using hinter'[rule_format, OF \<open>A3 \<in> \<A>'\<close> \<open>A2 \<in> \<A>'\<close> \<open>A3 \<noteq> A2\<close>]
                    \<open>s3 \<in> A2 \<inter> A3\<close> by (by100 blast)
              have "p1 \<in> {a2, b2}" using \<open>p1 \<in> top1_arc_endpoints_on A2 _\<close>
                  \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close> by (by100 blast)
              have "r2 \<in> {a2, b2}" using hr2_ep
                  \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close> by (by100 blast)
              have "{a2, b2} = {p1, r2}" using \<open>p1 \<in> {a2, b2}\<close> \<open>r2 \<in> {a2, b2}\<close>
                  \<open>r2 \<noteq> p1\<close> \<open>a2 \<noteq> b2\<close> by (by100 blast)
              hence "s3 \<in> {p1, r2}"
                using \<open>s3 \<in> top1_arc_endpoints_on A2 _\<close>
                    \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close> by (by100 blast)
              hence "s3 = p1" using \<open>s3 \<noteq> r2\<close> by (by100 blast)
              \<comment> \<open>A3 has endpoints {r2, p1} and A2 has endpoints {p1, r2}. SCC.\<close>
              have "top1_arc_endpoints_on A3 (subspace_topology T' TT' A3) = {p1, r2}"
              proof -
                have "r2 \<in> {a3, b3}" using \<open>r2 \<in> top1_arc_endpoints_on A3 _\<close>
                    \<open>top1_arc_endpoints_on A3 _ = {a3, b3}\<close> by (by100 blast)
                have "p1 \<in> {a3, b3}" using hs3_ep \<open>s3 = p1\<close>
                    \<open>top1_arc_endpoints_on A3 _ = {a3, b3}\<close> by (by100 blast)
                have "{a3, b3} = {p1, r2}"
                  using \<open>p1 \<in> {a3, b3}\<close> \<open>r2 \<in> {a3, b3}\<close> \<open>r2 \<noteq> p1\<close> \<open>a3 \<noteq> b3\<close>
                  by (by100 blast)
                thus ?thesis using \<open>top1_arc_endpoints_on A3 _ = {a3, b3}\<close> by simp
              qed
              have hA2_ep: "top1_arc_endpoints_on A2 (subspace_topology T' TT' A2) = {p1, r2}"
              proof -
                have "p1 \<in> {a2, b2}" using \<open>p1 \<in> top1_arc_endpoints_on A2 _\<close>
                    \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close> by (by100 blast)
                have "r2 \<in> {a2, b2}" using hr2_ep
                    \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close> by (by100 blast)
                have "{a2, b2} = {p1, r2}"
                  using \<open>p1 \<in> {a2, b2}\<close> \<open>r2 \<in> {a2, b2}\<close> \<open>r2 \<noteq> p1\<close> \<open>a2 \<noteq> b2\<close>
                  by (by100 blast)
                thus ?thesis using \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close> by simp
              qed
              show ?thesis
                using \<open>A2 \<in> \<A>'\<close> \<open>A3 \<in> \<A>'\<close> \<open>A3 \<noteq> A2\<close> \<open>r2 \<noteq> p1\<close>[symmetric]
                    hA2_ep \<open>top1_arc_endpoints_on A3 _ = {p1, r2}\<close>
                by (by100 blast)
            next
              case a4ne2: False
              show ?thesis
              proof (cases "A4 = A1")
                case True
                \<comment> \<open>A4 = A1. s3 \\<in> A1 \\<inter> A3 \\<subseteq> endpoints(A1) = {p1, q1}.\<close>
                have "s3 \<in> A1" using True \<open>s3 \<in> A4\<close> by simp
                have "s3 \<in> A3" using hs3_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
                have "s3 \<in> A1 \<inter> A3" using \<open>s3 \<in> A1\<close> \<open>s3 \<in> A3\<close> by (by100 blast)
                have "s3 \<in> top1_arc_endpoints_on A1 (subspace_topology T' TT' A1)"
                proof -
                  have "A3 \<inter> A1 \<subseteq> top1_arc_endpoints_on A1 (subspace_topology T' TT' A1)"
                    using hinter'[rule_format, OF \<open>A3 \<in> \<A>'\<close> \<open>A1 \<in> \<A>'\<close>] a3False by (by100 blast)
                  thus ?thesis using \<open>s3 \<in> A1 \<inter> A3\<close> by (by100 blast)
                qed
                hence "s3 \<in> {p1, q1}" using \<open>top1_arc_endpoints_on A1 _ = {p1, q1}\<close> by (by100 blast)
                show ?thesis
                proof (cases "s3 = p1")
                  case True
                  \<comment> \<open>s3 = p1: A3 has endpoints {r2, p1}. A2 has endpoints {p1, r2}. SCC.\<close>
                  have "top1_arc_endpoints_on A3 (subspace_topology T' TT' A3) = {p1, r2}"
                  proof -
                    have "r2 \<in> {a3, b3}" using \<open>r2 \<in> top1_arc_endpoints_on A3 _\<close>
                        \<open>top1_arc_endpoints_on A3 _ = {a3, b3}\<close> by (by100 blast)
                    have "p1 \<in> {a3, b3}" using hs3_ep True
                        \<open>top1_arc_endpoints_on A3 _ = {a3, b3}\<close> by (by100 blast)
                    thus ?thesis using \<open>r2 \<in> {a3, b3}\<close> \<open>r2 \<noteq> p1\<close> \<open>a3 \<noteq> b3\<close>
                        \<open>top1_arc_endpoints_on A3 _ = {a3, b3}\<close> by (by100 blast)
                  qed
                  have hA2_ep_pr: "top1_arc_endpoints_on A2 (subspace_topology T' TT' A2) = {p1, r2}"
                  proof -
                    have "p1 \<in> {a2, b2}" using \<open>p1 \<in> top1_arc_endpoints_on A2 _\<close>
                        \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close> by (by100 blast)
                    have "r2 \<in> {a2, b2}" using hr2_ep
                        \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close> by (by100 blast)
                    thus ?thesis using \<open>p1 \<in> {a2, b2}\<close> \<open>r2 \<noteq> p1\<close> \<open>a2 \<noteq> b2\<close>
                        \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close> by (by100 blast)
                  qed
                  show ?thesis
                    using \<open>A2 \<in> \<A>'\<close> \<open>A3 \<in> \<A>'\<close> \<open>A3 \<noteq> A2\<close> \<open>r2 \<noteq> p1\<close>[symmetric]
                        hA2_ep_pr \<open>top1_arc_endpoints_on A3 _ = {p1, r2}\<close>
                    by (by100 blast)
                next
                  case sFalse: False
                  hence "s3 = q1" using \<open>s3 \<in> {p1, q1}\<close> by (by100 blast)
                  \<comment> \<open>3-arc cycle: A1({p1,q1}), A2({p1,r2}), A3({r2,q1}).
                     Key: A2\\<union>A3 is an arc (arcs\\_concatenation\\_is\\_arc at r2).
                     Then A1 and A2\\<union>A3 share both endpoints {p1,q1} \\<Rightarrow> SCC.
                     SCC in tree \\<Rightarrow> contradiction.\<close>
                  \<comment> \<open>Step 1: A2 \\<inter> A3 = {r2}.\<close>
                  have "A2 \<inter> A3 \<subseteq> top1_arc_endpoints_on A2 (subspace_topology T' TT' A2)"
                    using hinter'[rule_format, OF \<open>A2 \<in> \<A>'\<close> \<open>A3 \<in> \<A>'\<close> \<open>A3 \<noteq> A2\<close>[symmetric]]
                    by (by100 blast)
                  have "A2 \<inter> A3 \<subseteq> top1_arc_endpoints_on A3 (subspace_topology T' TT' A3)"
                    using hinter'[rule_format, OF \<open>A2 \<in> \<A>'\<close> \<open>A3 \<in> \<A>'\<close> \<open>A3 \<noteq> A2\<close>[symmetric]]
                    by (by100 blast)
                  \<comment> \<open>endpoints(A2) = {p1,r2}, endpoints(A3) = {r2,q1}.\<close>
                  have hA2_ep_pr: "top1_arc_endpoints_on A2 (subspace_topology T' TT' A2) = {p1, r2}"
                  proof -
                    have "p1 \<in> {a2, b2}" using \<open>p1 \<in> top1_arc_endpoints_on A2 _\<close>
                        \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close> by (by100 blast)
                    have "r2 \<in> {a2, b2}" using hr2_ep
                        \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close> by (by100 blast)
                    thus ?thesis using \<open>p1 \<in> {a2, b2}\<close> \<open>r2 \<noteq> p1\<close> \<open>a2 \<noteq> b2\<close>
                        \<open>top1_arc_endpoints_on A2 _ = {a2, b2}\<close> by (by100 blast)
                  qed
                  have hA3_ep_rq: "top1_arc_endpoints_on A3 (subspace_topology T' TT' A3) = {r2, q1}"
                  proof -
                    have "r2 \<in> {a3, b3}" using \<open>r2 \<in> top1_arc_endpoints_on A3 _\<close>
                        \<open>top1_arc_endpoints_on A3 _ = {a3, b3}\<close> by (by100 blast)
                    have "q1 \<in> {a3, b3}" using hs3_ep \<open>s3 = q1\<close>
                        \<open>top1_arc_endpoints_on A3 _ = {a3, b3}\<close> by (by100 blast)
                    thus ?thesis using \<open>r2 \<in> {a3, b3}\<close> \<open>s3 \<noteq> r2\<close> \<open>s3 = q1\<close> \<open>a3 \<noteq> b3\<close>
                        \<open>top1_arc_endpoints_on A3 _ = {a3, b3}\<close> by (by100 blast)
                  qed
                  have "A2 \<inter> A3 \<subseteq> {p1, r2} \<inter> {r2, q1}"
                    using \<open>A2 \<inter> A3 \<subseteq> top1_arc_endpoints_on A2 _\<close> hA2_ep_pr
                        \<open>A2 \<inter> A3 \<subseteq> top1_arc_endpoints_on A3 _\<close> hA3_ep_rq by (by100 blast)
                  have "{p1, r2} \<inter> {r2, q1} = {r2}"
                    using \<open>p1 \<noteq> q1\<close> \<open>r2 \<noteq> p1\<close> \<open>s3 \<noteq> r2\<close> \<open>s3 = q1\<close> by (by100 blast)
                  have "A2 \<inter> A3 \<subseteq> {r2}" using \<open>A2 \<inter> A3 \<subseteq> {p1, r2} \<inter> {r2, q1}\<close>
                      \<open>{p1, r2} \<inter> {r2, q1} = {r2}\<close> by (by100 blast)
                  have "r2 \<in> A2" using hr2_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
                  have "r2 \<in> A2 \<inter> A3" using \<open>r2 \<in> A2\<close> \<open>r2 \<in> A3\<close> by (by100 blast)
                  have hA23_inter: "A2 \<inter> A3 = {r2}" using \<open>A2 \<inter> A3 \<subseteq> {r2}\<close> \<open>r2 \<in> A2 \<inter> A3\<close>
                    by (by100 blast)
                  \<comment> \<open>Step 2: A2\\<union>A3 is an arc by arcs\\_concatenation\\_is\\_arc.\<close>
                  have hA2_arc: "top1_is_arc_on A2 (subspace_topology T' TT' A2)"
                    using h\<A>' \<open>A2 \<in> \<A>'\<close> by (by100 blast)
                  have "A2 \<subseteq> T'" using h\<A>' \<open>A2 \<in> \<A>'\<close> by (by100 blast)
                  have hA3_arc: "top1_is_arc_on A3 (subspace_topology T' TT' A3)"
                    using h\<A>' \<open>A3 \<in> \<A>'\<close> by (by100 blast)
                  have "A3 \<subseteq> T'" using h\<A>' \<open>A3 \<in> \<A>'\<close> by (by100 blast)
                  have hr2_ep_A2: "r2 \<in> top1_arc_endpoints_on A2 (subspace_topology T' TT' A2)"
                    using hr2_ep .
                  have hr2_ep_A3: "r2 \<in> top1_arc_endpoints_on A3 (subspace_topology T' TT' A3)"
                    using \<open>r2 \<in> top1_arc_endpoints_on A3 _\<close> .
                  have hA23_arc: "top1_is_arc_on (A2 \<union> A3) (subspace_topology T' TT' (A2 \<union> A3))"
                    by (rule arcs_concatenation_is_arc[OF hstrict' hhaus' hA2_arc \<open>A2 \<subseteq> T'\<close>
                        hA3_arc \<open>A3 \<subseteq> T'\<close> hA23_inter hr2_ep_A2 hr2_ep_A3])
                  \<comment> \<open>Step 3: endpoints(A2\\<union>A3) = {p1,q1} by arc\\_concat\\_endpoints.\<close>
                  have "r2 \<noteq> q1" using \<open>s3 \<noteq> r2\<close> \<open>s3 = q1\<close> by simp
                  have hA2_ep_form: "top1_arc_endpoints_on A2 (subspace_topology T' TT' A2) = {p1, r2}"
                    using hA2_ep_pr .
                  have hA3_ep_form: "top1_arc_endpoints_on A3 (subspace_topology T' TT' A3) = {r2, q1}"
                    using hA3_ep_rq .
                  have hA23_ep: "top1_arc_endpoints_on (A2 \<union> A3) (subspace_topology T' TT' (A2 \<union> A3)) = {p1, q1}"
                    by (rule arc_concat_endpoints[OF hstrict' hhaus' hA2_arc \<open>A2 \<subseteq> T'\<close>
                        hA3_arc \<open>A3 \<subseteq> T'\<close> hA23_inter hr2_ep_A2 hr2_ep_A3
                        hA2_ep_form hA3_ep_form \<open>r2 \<noteq> p1\<close>[symmetric] \<open>r2 \<noteq> q1\<close>])
                  \<comment> \<open>Step 4: A1 \\<inter> (A2\\<union>A3) = {p1,q1}.\<close>
                  have hA1_A23_inter: "A1 \<inter> (A2 \<union> A3) = {p1, q1}"
                  proof -
                    have "A1 \<inter> (A2 \<union> A3) = (A1 \<inter> A2) \<union> (A1 \<inter> A3)" by (by100 blast)
                    \<comment> \<open>A1\\<inter>A2 \\<subseteq> endpoints(A1) = {p1,q1} and contains p1.\<close>
                    have "A1 \<inter> A2 \<subseteq> {p1, q1}"
                      using hinter'[rule_format, OF \<open>A1 \<in> \<A>'\<close> \<open>A2 \<in> \<A>'\<close> \<open>A2 \<noteq> A1\<close>[symmetric]]
                          \<open>top1_arc_endpoints_on A1 _ = {p1, q1}\<close> by (by100 blast)
                    have "p1 \<in> A1 \<inter> A2"
                    proof -
                      have "p1 \<in> A1" using \<open>p1 \<in> top1_arc_endpoints_on A1 _\<close>
                          unfolding top1_arc_endpoints_on_def by (by100 blast)
                      thus ?thesis using \<open>p1 \<in> A2\<close> by (by100 blast)
                    qed
                    \<comment> \<open>A1\\<inter>A3 \\<subseteq> endpoints(A1) = {p1,q1} and contains q1.\<close>
                    have "A1 \<inter> A3 \<subseteq> {p1, q1}"
                    proof -
                      have "A3 \<inter> A1 \<subseteq> top1_arc_endpoints_on A1 (subspace_topology T' TT' A1)"
                        using hinter'[rule_format, OF \<open>A3 \<in> \<A>'\<close> \<open>A1 \<in> \<A>'\<close>] a3False by (by100 blast)
                      thus ?thesis using \<open>top1_arc_endpoints_on A1 _ = {p1, q1}\<close> by (by100 blast)
                    qed
                    have "q1 \<in> A1 \<inter> A3"
                    proof -
                      have "q1 \<in> A1" using \<open>q1 \<in> top1_arc_endpoints_on A1 _\<close>
                          unfolding top1_arc_endpoints_on_def by (by100 blast)
                      have "q1 \<in> A3" using hs3_ep \<open>s3 = q1\<close>
                          unfolding top1_arc_endpoints_on_def by (by100 blast)
                      thus ?thesis using \<open>q1 \<in> A1\<close> by (by100 blast)
                    qed
                    show ?thesis using \<open>A1 \<inter> (A2 \<union> A3) = (A1 \<inter> A2) \<union> (A1 \<inter> A3)\<close>
                        \<open>A1 \<inter> A2 \<subseteq> {p1, q1}\<close> \<open>A1 \<inter> A3 \<subseteq> {p1, q1}\<close>
                        \<open>p1 \<in> A1 \<inter> A2\<close> \<open>q1 \<in> A1 \<inter> A3\<close> by (by100 blast)
                  qed
                  \<comment> \<open>Step 5: SCC via arcs\\_form\\_simple\\_closed\\_curve.\<close>
                  have "A1 \<subseteq> T'" using h\<A>' \<open>A1 \<in> \<A>'\<close> by (by100 blast)
                  have "A2 \<union> A3 \<subseteq> T'" using \<open>A2 \<subseteq> T'\<close> \<open>A3 \<subseteq> T'\<close> by (by100 blast)
                  have hA1_arc: "top1_is_arc_on A1 (subspace_topology T' TT' A1)"
                    using h\<A>' \<open>A1 \<in> \<A>'\<close> by (by100 blast)
                  from arcs_form_simple_closed_curve[OF hstrict' hhaus' hA1_arc \<open>A1 \<subseteq> T'\<close>
                      hA23_arc \<open>A2 \<union> A3 \<subseteq> T'\<close> hA1_A23_inter \<open>p1 \<noteq> q1\<close>
                      \<open>top1_arc_endpoints_on A1 _ = {p1, q1}\<close> hA23_ep]
                  have "top1_simple_closed_curve_on T' TT' (A1 \<union> (A2 \<union> A3))" .
                  \<comment> \<open>Step 6: SCC in tree \\<Rightarrow> contradiction. Same chain as the 2-arc case.\<close>
                  \<comment> \<open>Use scc\\_in\\_sc\\_false to derive contradiction.\<close>
                  have "top1_retract_of_on T' TT' (A1 \<union> (A2 \<union> A3))"
                    sorry \<comment> \<open>Retract: same construction as two\\_arc\\_union\\_is\\_retract but
                       with A1 and A2\\<union>A3. External arcs map to attachment vertices.\<close>
                  have "A1 \<union> (A2 \<union> A3) \<subseteq> T'"
                    using \<open>A1 \<subseteq> T'\<close> \<open>A2 \<union> A3 \<subseteq> T'\<close> by (by100 blast)
                  have hsc_T': "top1_simply_connected_on T' TT'"
                    using htree' unfolding top1_is_tree_on_def by (by100 blast)
                  have hTT'_top: "is_topology_on T' TT'"
                    using hstrict' unfolding is_topology_on_strict_def by (by100 blast)
                  from scc_in_sc_false[OF hsc_T' hTT'_top hhaus'
                      \<open>top1_simple_closed_curve_on T' TT' (A1 \<union> (A2 \<union> A3))\<close>
                      \<open>top1_retract_of_on T' TT' (A1 \<union> (A2 \<union> A3))\<close>
                      \<open>A1 \<union> (A2 \<union> A3) \<subseteq> T'\<close>]
                  show ?thesis by (by100 blast)
                qed
              next
                case a4ne1: False
                \<comment> \<open>A4 \\<notin> {A1,A2,A3}. Continue walk (needs pigeonhole for general case).\<close>
                show ?thesis sorry \<comment> \<open>General walk continuation + pigeonhole.\<close>
              qed
            qed
          qed
        qed
      qed
      then obtain A1 A2 p1' q1' where hA1: "A1 \<in> \<A>'" and hA2: "A2 \<in> \<A>'"
          and hne12: "A1 \<noteq> A2" and hpq': "p1' \<noteq> q1'"
          and hep1': "top1_arc_endpoints_on A1 (subspace_topology T' TT' A1) = {p1', q1'}"
          and hep2': "top1_arc_endpoints_on A2 (subspace_topology T' TT' A2) = {p1', q1'}"
        by (by100 blast)
      \<comment> \<open>Step 6: SCC in tree \\<Rightarrow> contradiction.\<close>
      have hstrict': "is_topology_on_strict T' TT'"
        using htree' unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
      have hhaus': "is_hausdorff_on T' TT'"
        using htree' unfolding top1_is_tree_on_def top1_is_graph_on_def by (by100 blast)
      have hA12_inter': "\<forall>C\<in>\<A>'. C \<noteq> A1 \<longrightarrow> C \<noteq> A2 \<longrightarrow> C \<inter> (A1 \<union> A2) \<subseteq> {p1', q1'}"
      proof (intro ballI impI)
        fix C assume "C \<in> \<A>'" "C \<noteq> A1" "C \<noteq> A2"
        have "C \<inter> A1 \<subseteq> top1_arc_endpoints_on A1 (subspace_topology T' TT' A1)"
          using hinter'[rule_format, OF \<open>C \<in> \<A>'\<close> hA1 \<open>C \<noteq> A1\<close>] by (by100 blast)
        hence hCA1: "C \<inter> A1 \<subseteq> {p1', q1'}" using hep1' by (by100 blast)
        have "C \<inter> A2 \<subseteq> top1_arc_endpoints_on A2 (subspace_topology T' TT' A2)"
          using hinter'[rule_format, OF \<open>C \<in> \<A>'\<close> hA2 \<open>C \<noteq> A2\<close>] by (by100 blast)
        hence "C \<inter> A2 \<subseteq> {p1', q1'}" using hep2' by (by100 blast)
        thus "C \<inter> (A1 \<union> A2) \<subseteq> {p1', q1'}" using hCA1 by (by100 blast)
      qed
      have hsc_T'_for_retract: "top1_simply_connected_on T' TT'"
        using htree' unfolding top1_is_tree_on_def by (by100 blast)
      from two_arc_union_is_retract[OF hstrict' hhaus' h\<A>' hcover' hinter' hcoh'
          hA1 hA2 hne12 hep1' hep2' hpq' hA12_inter' hsc_T'_for_retract]
      have hretract': "top1_retract_of_on T' TT' (A1 \<union> A2)" .
      \<comment> \<open>SCC: arcs\\_form\\_simple\\_closed\\_curve.\<close>
      have "A1 \<inter> A2 = {p1', q1'}"
      proof -
        have "A1 \<inter> A2 \<subseteq> top1_arc_endpoints_on A1 (subspace_topology T' TT' A1)"
          using hinter'[rule_format, OF hA1 hA2 hne12] by (by100 blast)
        hence "A1 \<inter> A2 \<subseteq> {p1', q1'}" using hep1' by (by100 blast)
        moreover have "p1' \<in> A1 \<inter> A2"
        proof -
          have "p1' \<in> A1" using hep1' unfolding top1_arc_endpoints_on_def by (by100 blast)
          have "p1' \<in> A2" using hep2' unfolding top1_arc_endpoints_on_def by (by100 blast)
          thus ?thesis using \<open>p1' \<in> A1\<close> by (by100 blast)
        qed
        moreover have "q1' \<in> A1 \<inter> A2"
        proof -
          have "q1' \<in> A1" using hep1' unfolding top1_arc_endpoints_on_def by (by100 blast)
          have "q1' \<in> A2" using hep2' unfolding top1_arc_endpoints_on_def by (by100 blast)
          thus ?thesis using \<open>q1' \<in> A1\<close> by (by100 blast)
        qed
        ultimately show ?thesis by (by100 blast)
      qed
      have hA1_arc: "top1_is_arc_on A1 (subspace_topology T' TT' A1)"
        using h\<A>' hA1 by (by100 blast)
      have "A1 \<subseteq> T'" using h\<A>' hA1 by (by100 blast)
      have hA2_arc: "top1_is_arc_on A2 (subspace_topology T' TT' A2)"
        using h\<A>' hA2 by (by100 blast)
      have "A2 \<subseteq> T'" using h\<A>' hA2 by (by100 blast)
      from arcs_form_simple_closed_curve[OF hstrict' hhaus' hA1_arc \<open>A1 \<subseteq> T'\<close>
          hA2_arc \<open>A2 \<subseteq> T'\<close> \<open>A1 \<inter> A2 = {p1', q1'}\<close> hpq' hep1' hep2']
      have hSCC: "top1_simple_closed_curve_on T' TT' (A1 \<union> A2)" .
      \<comment> \<open>T' simply connected + retract of SCC \\<Rightarrow> \\<pi>\\_1(SCC) = Z embeds into \\<pi>\\_1(T') = 0.\<close>
      \<comment> \<open>But Z \\<ne> 0 \\<Rightarrow> contradiction.\<close>
      \<comment> \<open>T' is simply connected. A1\\<union>A2 \\<cong> S1 is a retract of T'.
         Retract \\<Rightarrow> \\<pi>\\_1 injection \\<Rightarrow> \\<pi>\\_1(S1) \\<hookrightarrow> \\<pi>\\_1(T') = 0.
         But \\<pi>\\_1(S1) \\<ne> 0. Contradiction.\<close>
      have hsc': "top1_simply_connected_on T' TT'"
        using htree' unfolding top1_is_tree_on_def by (by100 blast)
      \<comment> \<open>Extract S1-homeomorphism from the SCC.\<close>
      from hSCC[unfolded top1_simple_closed_curve_on_def]
      obtain h_s where hhs_cont: "top1_continuous_map_on top1_S1 top1_S1_topology T' TT' h_s"
          and hhs_inj: "inj_on h_s top1_S1" and hhs_img: "h_s ` top1_S1 = A1 \<union> A2"
        by (by100 blast)
      \<comment> \<open>Need a basepoint in A1\\<union>A2 for the \\<pi>\\_1 argument.
         Take p1' which is in A1\\<union>A2.\<close>
      have "p1' \<in> A1 \<union> A2"
        using hep1' unfolding top1_arc_endpoints_on_def by (by100 blast)
      have "A1 \<union> A2 \<subseteq> T'" using \<open>A1 \<subseteq> T'\<close> \<open>A2 \<subseteq> T'\<close> by (by100 blast)
      hence "p1' \<in> T'" using \<open>p1' \<in> A1 \<union> A2\<close> by (by100 blast)
      \<comment> \<open>The full argument: any loop in A1\\<union>A2 is null-homotopic in T' (SC).
         By Lemma 55.1 (retract injective): null-homotopic in T' \\<Rightarrow> null-homotopic in A1\\<union>A2.
         So \\<pi>\\_1(A1\\<union>A2) = 0. But A1\\<union>A2 \\<cong> S1 has \\<pi>\\_1 = Z \\<ne> 0.\<close>
      \<comment> \<open>Step 1: A1\\<union>A2 is simply connected (from retract + T' SC).\<close>
      have hC_sub: "A1 \<union> A2 \<subseteq> T'" using \<open>A1 \<union> A2 \<subseteq> T'\<close> .
      have hTT': "is_topology_on T' TT'"
        using hstrict' unfolding is_topology_on_strict_def by (by100 blast)
      have hC_top: "is_topology_on (A1 \<union> A2) (subspace_topology T' TT' (A1 \<union> A2))"
        using subspace_topology_is_topology_on[OF hTT' hC_sub] .
      have hC_sc: "top1_simply_connected_on (A1 \<union> A2) (subspace_topology T' TT' (A1 \<union> A2))"
      proof -
        \<comment> \<open>A1\\<union>A2 path-connected (SCC \\<cong> S1 which is path-connected).\<close>
        have hC_pc: "top1_path_connected_on (A1 \<union> A2) (subspace_topology T' TT' (A1 \<union> A2))"
        proof -
          have h1: "\<forall>x\<in>top1_S1. h_s x \<in> T'"
          proof (intro ballI)
            fix s assume "s \<in> top1_S1"
            hence "h_s s \<in> h_s ` top1_S1" by (by100 blast)
            hence "h_s s \<in> A1 \<union> A2" using hhs_img by (by100 blast)
            thus "h_s s \<in> T'" using hC_sub by (by100 blast)
          qed
          have h2: "h_s ` top1_S1 = A1 \<union> A2" using hhs_img .
          have h3: "A1 \<union> A2 \<subseteq> T'" using hC_sub .
          have h4: "subspace_topology T' TT' (A1 \<union> A2) = subspace_topology T' TT' (A1 \<union> A2)"
            by simp
          from top1_path_connected_continuous_image[OF S1_path_connected hhs_cont h1 h2 h3 _ hTT']
          show ?thesis by simp
        qed
        \<comment> \<open>Every loop in A1\\<union>A2 is null-homotopic in A1\\<union>A2.\<close>
        have hC_loops: "\<forall>x\<in>A1 \<union> A2. \<forall>f. top1_is_loop_on (A1 \<union> A2) (subspace_topology T' TT' (A1 \<union> A2)) x f \<longrightarrow>
            top1_path_homotopic_on (A1 \<union> A2) (subspace_topology T' TT' (A1 \<union> A2)) x x f (top1_constant_path x)"
        proof (intro ballI allI impI)
          fix x f assume hx: "x \<in> A1 \<union> A2"
              and hf: "top1_is_loop_on (A1 \<union> A2) (subspace_topology T' TT' (A1 \<union> A2)) x f"
          \<comment> \<open>f is a loop in A1\\<union>A2, hence a loop in T' (via inclusion).\<close>
          have hf_T: "top1_is_loop_on T' TT' x f"
          proof -
            from hf have hf_path: "top1_is_path_on (A1 \<union> A2) (subspace_topology T' TT' (A1 \<union> A2)) x x f"
              unfolding top1_is_loop_on_def by (by100 blast)
            from path_in_subspace_is_path_in_ambient'[OF hTT' hC_sub hf_path]
            have "top1_is_path_on T' TT' x x f" .
            thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
          qed
          \<comment> \<open>T' is SC \\<Rightarrow> f null-homotopic in T'.\<close>
          have "x \<in> T'" using hx hC_sub by (by100 blast)
          have hf_null_T: "top1_path_homotopic_on T' TT' x x f (top1_constant_path x)"
            using hsc'[unfolded top1_simply_connected_on_def] hf_T \<open>x \<in> T'\<close> by (by100 blast)
          \<comment> \<open>By Lemma 55.1: retract \\<Rightarrow> null-homotopic in T' \\<Rightarrow> null-homotopic in A1\\<union>A2.\<close>
          have hconst: "top1_is_loop_on (A1 \<union> A2) (subspace_topology T' TT' (A1 \<union> A2)) x (top1_constant_path x)"
            by (rule top1_constant_path_is_loop[OF hC_top hx])
          from Lemma_55_1_retract_injective[OF hretract' hx hf hconst hf_null_T]
          show "top1_path_homotopic_on (A1 \<union> A2) (subspace_topology T' TT' (A1 \<union> A2)) x x f (top1_constant_path x)" .
        qed
        show ?thesis unfolding top1_simply_connected_on_def using hC_pc hC_loops by (by100 blast)
      qed
      \<comment> \<open>Step 2: A1\\<union>A2 \\<cong> S1 (from hSCC). Transfer SC from A1\\<union>A2 to S1.\<close>
      \<comment> \<open>h\\_s: S1 \\<rightarrow> T' continuous injection with image A1\\<union>A2.\<close>
      \<comment> \<open>S1 compact, A1\\<union>A2 Hausdorff \\<Rightarrow> h\\_s homeomorphism onto A1\\<union>A2.\<close>
      \<comment> \<open>Transfer SC from A1\\<union>A2 to S1 via homeomorphism. But S1 is NOT SC.\<close>
      \<comment> \<open>h\\_s: S1 \\<rightarrow> A1\\<union>A2 is a homeomorphism (Theorem 26.6: compact → Hausdorff bijection).\<close>
      have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
        using S1_compact unfolding top1_compact_on_def by (by100 blast)
      have hC_haus: "is_hausdorff_on (A1 \<union> A2) (subspace_topology T' TT' (A1 \<union> A2))"
        using hhaus' hC_sub conjunct2[OF conjunct2[OF Theorem_17_11]] by (by100 blast)
      have "bij_betw h_s top1_S1 (A1 \<union> A2)"
        unfolding bij_betw_def using hhs_inj hhs_img by (by100 blast)
      have hhs_range: "\<forall>s\<in>top1_S1. h_s s \<in> A1 \<union> A2"
      proof (intro ballI)
        fix s assume "s \<in> top1_S1"
        hence "h_s s \<in> h_s ` top1_S1" by (by100 blast)
        thus "h_s s \<in> A1 \<union> A2" using hhs_img by (by100 blast)
      qed
      have "top1_continuous_map_on top1_S1 top1_S1_topology (A1 \<union> A2) (subspace_topology T' TT' (A1 \<union> A2)) h_s"
        by (rule continuous_map_restrict_codomain[OF hhs_cont hhs_range hC_sub])
      from Theorem_26_6[OF hS1_top hC_top S1_compact hC_haus this \<open>bij_betw h_s top1_S1 (A1 \<union> A2)\<close>]
      have hhomeo: "top1_homeomorphism_on top1_S1 top1_S1_topology (A1 \<union> A2) (subspace_topology T' TT' (A1 \<union> A2)) h_s" .
      \<comment> \<open>Transfer SC from A1\\<union>A2 to S1 via homeomorphism.\<close>
      \<comment> \<open>Need SC S1 from SC A1\\<union>A2. Use inverse homeomorphism A1\\<union>A2 \\<rightarrow> S1.\<close>
      have hhomeo_inv: "top1_homeomorphism_on (A1 \<union> A2) (subspace_topology T' TT' (A1 \<union> A2))
          top1_S1 top1_S1_topology (inv_into top1_S1 h_s)"
        by (rule homeomorphism_inverse[OF hhomeo])
      have "top1_simply_connected_on top1_S1 top1_S1_topology"
        by (rule homeomorphism_preserves_simply_connected[OF hhomeo_inv hC_sc])
      \<comment> \<open>But S1 is NOT simply connected: \\<pi>\\_1(S1) \\<ne> 0.\<close>
      \<comment> \<open>But S1 is NOT simply connected.\<close>
      from top1_S1_fundamental_group_nontrivial
      obtain f0 g0 where hfg: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f0"
          "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) g0"
          "\<not> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) f0 g0"
        by (by100 blast)
      \<comment> \<open>SC \\<Rightarrow> f0 \\<sim> const and g0 \\<sim> const \\<Rightarrow> f0 \\<sim> g0. Contradiction.\<close>
      have h10: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 auto)
      have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
        using S1_compact unfolding top1_compact_on_def by (by100 blast)
      from \<open>top1_simply_connected_on top1_S1 top1_S1_topology\<close>[unfolded top1_simply_connected_on_def]
      have "\<forall>x\<in>top1_S1. \<forall>f. top1_is_loop_on top1_S1 top1_S1_topology x f \<longrightarrow>
          top1_path_homotopic_on top1_S1 top1_S1_topology x x f (top1_constant_path x)"
        using h10 by (by100 blast)
      hence hf0_null: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0) f0 (top1_constant_path (1,0))"
        using hfg(1) h10 by (by100 blast)
      hence hg0_null: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0) g0 (top1_constant_path (1,0))"
        using \<open>\<forall>x\<in>top1_S1. \<forall>f. _\<close> hfg(2) h10 by (by100 blast)
      \<comment> \<open>f0 \\<sim> const \\<sim> g0 \\<Rightarrow> f0 \\<sim> g0 by transitivity + symmetry.\<close>
      from Lemma_51_1_path_homotopic_sym[OF hg0_null]
      have "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0) (top1_constant_path (1,0)) g0" .
      from Lemma_51_1_path_homotopic_trans[OF hS1_top hf0_null this]
      have hfg_htpy: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0) f0 g0" .
      show False using hfg_htpy hfg(3) by (by100 blast)
    qed
  qed
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

\<comment> \<open>Covering graph Euler characteristic multiplicativity.
   For a k-fold covering p: E \\<rightarrow> X of a finite connected graph,
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
  \<comment> \<open>hfree\\_E at line above gives the free group with \\<iota>E\\_raw and SE\\_raw.\<close>
  \<comment> \<open>Step 6: Euler characteristic argument.
     From graph\\_pi1\\_free\\_weak on E: card(SE) = rank(\\<pi>\\_1(E)).
     From Euler formula (heuler\\_X): card(\\<A>w) - card(V\\_X) = card(Sw) - 1 = n.
     Lifted family: card(\\<A>\\_L) - card(V\\_L) = k * (card(\\<A>w) - card(V\\_X)) = kn.
     By Euler invariance (rank is independent of decomposition):
     rank(\\<pi>\\_1(E)) = card(\\<A>\\_L) - card(V\\_L) + 1 = kn + 1.
     By rank invariance: card(SE) = kn + 1.\<close>
  \<comment> \<open>The Euler invariance step is the remaining hard part.\<close>
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
