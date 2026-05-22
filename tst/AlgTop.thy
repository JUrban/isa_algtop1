theory AlgTop
  imports "AlgTopGroups.AlgTopGroups"
begin
text \<open>Existence part of universal property.\<close>
lemma free_group_hom_exists:
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
      and "top1_is_group_on H mulH eH invgH"
      and "\<forall>s\<in>S. \<phi> s \<in> H"
  shows "\<exists>\<psi>. top1_group_hom_on G mul H mulH \<psi> \<and> (\<forall>s\<in>S. \<psi> (\<iota> s) = \<phi> s)"
proof -
  have hG_grp: "top1_is_group_on G mul e invg"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hG_in: "\<forall>s\<in>S. \<iota> s \<in> G"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hG_gen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  \<comment> \<open>Step 1: The set of word-products equals G.
     Define W = {top1\_group\_word\_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ws)
                | ws. \<forall>i<length ws. fst(ws!i) \<in> S}.
     W is a subgroup of G containing \<iota>(S), hence W = \<langle>\<iota>(S)\<rangle> = G.\<close>
  let ?eval_G = "\<lambda>ws. top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
  let ?eval_H = "\<lambda>ws. top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ws)"
  let ?W = "{?eval_G ws | ws. \<forall>i<length ws. fst (ws ! i) \<in> S}"
  have hW_eq_G: "?W = G"
  proof (rule set_eqI, rule iffI)
    \<comment> \<open>W \<subseteq> G: word products are in G.\<close>
    fix g assume "g \<in> ?W"
    then obtain ws where hws: "\<forall>i<length ws. fst (ws ! i) \<in> S" and hg: "g = ?eval_G ws"
      by (by100 blast)
    have "\<forall>i<length (map (\<lambda>(s,b). (\<iota> s, b)) ws). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! i) \<in> G"
    proof (intro allI impI)
      fix j assume "j < length (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
      hence hj: "j < length ws" by (by100 simp)
      obtain s b where hwj: "ws ! j = (s, b)" by (cases "ws!j") (by100 blast)
      have "s \<in> S" using hws hj hwj by (by100 force)
      thus "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G"
        using hG_in hj hwj by simp
    qed
    thus "g \<in> G" using hg word_product_in_group[OF hG_grp] by (by100 simp)
  next
    \<comment> \<open>G \<subseteq> W: G = \<langle>\<iota>(S)\<rangle> and W is a subgroup containing \<iota>(S).\<close>
    fix g assume hg: "g \<in> G"
    \<comment> \<open>W is a subgroup of G containing \<iota>(S).\<close>
    \<comment> \<open>Helper: mapped word elements are in G.\<close>
    have hmapped_G: "\<And>ws. \<forall>i<length ws. fst (ws ! i) \<in> S \<Longrightarrow>
        \<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ws). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G"
    proof (intro allI impI)
      fix ws and j
      assume h: "\<forall>i<length ws. fst (ws ! i) \<in> S" and hj: "j < length (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
      hence hjw: "j < length ws" by (by100 simp)
      obtain sj bj where hwj: "ws ! j = (sj, bj)" by (cases "ws!j") (by100 blast)
      have "sj \<in> S" using h hjw hwj by (by100 force)
      thus "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G" using hG_in hjw hwj by simp
    qed
    have hW_grp: "top1_is_group_on ?W mul e invg"
    proof -
      have he: "e \<in> ?W"
        apply (rule CollectI) apply (rule exI[of _ "[]"]) by (by100 simp)
      have hcl: "\<forall>x\<in>?W. \<forall>y\<in>?W. mul x y \<in> ?W"
      proof (intro ballI)
        fix x y assume "x \<in> ?W" "y \<in> ?W"
        then obtain ws1 ws2 where h1: "\<forall>i<length ws1. fst(ws1!i) \<in> S" "x = ?eval_G ws1"
            and h2: "\<forall>i<length ws2. fst(ws2!i) \<in> S" "y = ?eval_G ws2" by (by100 blast)
        have hmap_app: "map (\<lambda>(s,b). (\<iota> s, b)) (ws1 @ ws2) =
            map (\<lambda>(s,b). (\<iota> s, b)) ws1 @ map (\<lambda>(s,b). (\<iota> s, b)) ws2" by (by100 simp)
        have "mul x y = ?eval_G (ws1 @ ws2)"
          using h1(2) h2(2) word_product_append[OF hG_grp hmapped_G[OF h1(1)] hmapped_G[OF h2(1)]]
                hmap_app by (by100 simp)
        moreover have "\<forall>i<length (ws1@ws2). fst((ws1@ws2)!i) \<in> S"
          using h1(1) h2(1) by (simp add: nth_append)
        ultimately show "mul x y \<in> ?W" by (by100 blast)
      qed
      have hinv: "\<forall>x\<in>?W. invg x \<in> ?W"
      proof (intro ballI)
        fix x assume "x \<in> ?W"
        then obtain ws where hws: "\<forall>i<length ws. fst(ws!i) \<in> S" "x = ?eval_G ws" by (by100 blast)
        let ?rws = "map (\<lambda>(s,b). (s, \<not>b)) (rev ws)"
        have hrev_map: "map (\<lambda>(s,b). (\<iota> s, b)) ?rws
            = map (\<lambda>(x,b). (x, \<not>b)) (rev (map (\<lambda>(s,b). (\<iota> s, b)) ws))"
          by (induct ws) auto
        have "invg x = ?eval_G ?rws"
          using hws(2) word_product_rev_inv[OF hG_grp hmapped_G[OF hws(1)]] hrev_map by (by100 simp)
        moreover have "\<forall>i<length ?rws. fst(?rws!i) \<in> S"
        proof (intro allI impI)
          fix i assume "i < length ?rws"
          hence hi: "i < length ws" by (by100 simp)
          have "length ws - 1 - i < length ws" using hi by (by100 simp)
          obtain si bi where "ws ! (length ws - 1 - i) = (si, bi)"
            by (cases "ws!(length ws - 1 - i)") (by100 blast)
          hence hsi_S: "si \<in> S" using hws(1) \<open>length ws - 1 - i < length ws\<close> by (by100 force)
          have hrev_i: "rev ws ! i = ws ! (length ws - 1 - i)" using rev_nth[of i ws] hi by (by100 simp)
          hence hrev_si: "rev ws ! i = (si, bi)" using \<open>ws ! (length ws - 1 - i) = (si, bi)\<close> by (by100 simp)
          have "?rws ! i = (case rev ws ! i of (s, b) \<Rightarrow> (s, \<not>b))" using hi by (by100 simp)
          hence "?rws ! i = (si, \<not>bi)" using hrev_si by (by100 simp)
          thus "fst(?rws!i) \<in> S" using hsi_S by (by100 simp)
        qed
        ultimately show "invg x \<in> ?W" by (by100 blast)
      qed
      \<comment> \<open>W \<subseteq> G for group axioms.\<close>
      have hWG: "?W \<subseteq> G"
      proof
        fix g assume "g \<in> ?W"
        then obtain ws where "g = ?eval_G ws" "\<forall>i<length ws. fst(ws!i) \<in> S" by (by100 blast)
        thus "g \<in> G" using word_product_in_group[OF hG_grp hmapped_G] by (by100 simp)
      qed
      show ?thesis unfolding top1_is_group_on_def
      proof (intro conjI)
        show "e \<in> ?W" by (rule he)
        show "\<forall>x\<in>?W. \<forall>y\<in>?W. mul x y \<in> ?W" by (rule hcl)
        show "\<forall>x\<in>?W. invg x \<in> ?W" by (rule hinv)
      next
        show "\<forall>x\<in>?W. \<forall>y\<in>?W. \<forall>z\<in>?W. mul (mul x y) z = mul x (mul y z)"
          using hWG hG_grp unfolding top1_is_group_on_def by blast
        show "\<forall>x\<in>?W. mul e x = x \<and> mul x e = x"
          using hWG hG_grp unfolding top1_is_group_on_def by blast
        show "\<forall>x\<in>?W. mul (invg x) x = e \<and> mul x (invg x) = e"
          using hWG hG_grp unfolding top1_is_group_on_def by blast
      qed
    qed
    have hW_sub: "?W \<subseteq> G"
    proof
      fix g assume "g \<in> ?W"
      then obtain ws where hws: "\<forall>i<length ws. fst (ws ! i) \<in> S" "g = ?eval_G ws" by (by100 blast)
      have "\<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ws). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G"
      proof (intro allI impI)
        fix j assume "j < length (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
        hence hj: "j < length ws" by (by100 simp)
        obtain s b where "ws ! j = (s, b)" by (cases "ws!j") (by100 blast)
        have "fst (ws ! j) \<in> S" using hws(1) hj by (by100 blast)
        thus "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G"
          using hG_in hj \<open>ws ! j = (s, b)\<close> by simp
      qed
      thus "g \<in> G" using hws(2) word_product_in_group[OF hG_grp] by (by100 simp)
    qed
    have hiotaS_W: "\<iota> ` S \<subseteq> ?W"
    proof (intro image_subsetI)
      fix s assume hs: "s \<in> S"
      have "?eval_G [(s, True)] = mul (\<iota> s) e" by (by100 simp)
      also have "\<dots> = \<iota> s" using hG_grp hG_in hs unfolding top1_is_group_on_def by (by100 blast)
      finally have "\<iota> s = ?eval_G [(s, True)]" by (by100 simp)
      moreover have "\<forall>i<length [(s, True)]. fst ([(s, True)] ! i) \<in> S"
        using hs by (by100 simp)
      ultimately show "\<iota> s \<in> ?W" by (by100 blast)
    qed
    have hW_in: "?W \<in> {K. \<iota> ` S \<subseteq> K \<and> K \<subseteq> G \<and> top1_is_group_on K mul e invg}"
      using hiotaS_W hW_sub hW_grp by (by100 blast)
    hence "top1_subgroup_generated_on G mul e invg (\<iota> ` S) \<subseteq> ?W"
      unfolding top1_subgroup_generated_on_def
      using Inter_lower[OF hW_in] by (by100 blast)
    thus "g \<in> ?W" using hg hG_gen by (by100 blast)
  qed
  \<comment> \<open>Step 2: Define \<psi> via SOME word representation.\<close>
  let ?\<psi> = "\<lambda>g. ?eval_H (SOME ws. (\<forall>i<length ws. fst (ws ! i) \<in> S) \<and> ?eval_G ws = g)"
  \<comment> \<open>Helper: mapped word elements are in G.\<close>
  have hmapped_G: "\<And>ws. \<forall>i<length ws. fst (ws ! i) \<in> S \<Longrightarrow>
      \<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ws). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G"
  proof (intro allI impI)
    fix ws and j
    assume h: "\<forall>i<length ws. fst (ws ! i) \<in> S" and hj: "j < length (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
    hence hjw: "j < length ws" by (by100 simp)
    obtain sj bj where hwj: "ws ! j = (sj, bj)" by (cases "ws!j") (by100 blast)
    have "sj \<in> S" using h hjw hwj by (by100 force)
    thus "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G" using hG_in hjw hwj by simp
  qed
  \<comment> \<open>Step 3: \<psi> is well-defined: any two word representations give the same H-value.\<close>
  \<comment> \<open>Helper: flip-rev preserves S-generators and commutes with map.\<close>
  have hfliprev_S: "\<And>ws. \<forall>i<length ws. fst (ws ! i) \<in> S \<Longrightarrow>
      \<forall>i<length (map (\<lambda>(s,b). (s, \<not>b)) (rev ws)). fst (map (\<lambda>(s,b). (s, \<not>b)) (rev ws) ! i) \<in> S"
  proof (intro allI impI)
    fix ws and i
    assume h: "\<forall>i<length ws. fst (ws ! i) \<in> S" and hi: "i < length (map (\<lambda>(s,b). (s, \<not>b)) (rev ws))"
    hence hiw: "i < length ws" by (by100 simp)
    have "length ws - 1 - i < length ws" using hiw by (by100 simp)
    obtain s b where hsb: "ws ! (length ws - 1 - i) = (s, b)" by (cases "ws!(length ws-1-i)") (by100 blast)
    have "s \<in> S" using h \<open>length ws - 1 - i < length ws\<close> hsb by (by100 force)
    have hrev: "rev ws ! i = (s, b)" using rev_nth[of i ws] hiw hsb by (by100 simp)
    have "map (\<lambda>(s,b). (s, \<not>b)) (rev ws) ! i = (s, \<not>b)" using hiw hrev by simp
    thus "fst (map (\<lambda>(s,b). (s, \<not>b)) (rev ws) ! i) \<in> S" using \<open>s \<in> S\<close> by (by100 simp)
  qed
  have hmap_fliprev: "\<And>ws. map (\<lambda>(s,b). (\<iota> s, b)) (map (\<lambda>(s,b). (s, \<not>b)) (rev ws))
      = map (\<lambda>(x,b). (x, \<not>b)) (rev (map (\<lambda>(s,b). (\<iota> s, b)) ws))"
    by (induct_tac ws) auto
  have hwd: "\<And>ws1 ws2. \<forall>i<length ws1. fst (ws1 ! i) \<in> S \<Longrightarrow>
      \<forall>i<length ws2. fst (ws2 ! i) \<in> S \<Longrightarrow>
      ?eval_G ws1 = ?eval_G ws2 \<Longrightarrow>
      ?eval_H ws1 = ?eval_H ws2"
  proof (goal_cases)
    case (1 ws1 ws2)
    let ?fr2 = "map (\<lambda>(s,b). (s, \<not>b)) (rev ws2)"
    let ?ws3 = "ws1 @ ?fr2"
    \<comment> \<open>ws3 generators from S.\<close>
    have hfr2_S: "\<forall>i<length ?fr2. fst (?fr2 ! i) \<in> S" by (rule hfliprev_S[OF 1(2)])
    have hws3_S: "\<forall>i<length ?ws3. fst (?ws3 ! i) \<in> S"
      using 1(1) hfr2_S by (simp add: nth_append)
    \<comment> \<open>eval\_G(ws3) = e.\<close>
    have hmG1: "\<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ws1). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws1 ! j) \<in> G"
      by (rule hmapped_G[OF 1(1)])
    have hmGr: "\<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ?fr2). fst (map (\<lambda>(s,b). (\<iota> s, b)) ?fr2 ! j) \<in> G"
      by (rule hmapped_G[OF hfr2_S])
    have hmG2: "\<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ws2). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws2 ! j) \<in> G"
      by (rule hmapped_G[OF 1(2)])
    have happ_map: "map (\<lambda>(s,b). (\<iota> s, b)) ?ws3 =
        map (\<lambda>(s,b). (\<iota> s, b)) ws1 @ map (\<lambda>(s,b). (\<iota> s, b)) ?fr2" by (by100 simp)
    have heval_G_split: "?eval_G ?ws3 = mul (?eval_G ws1) (?eval_G ?fr2)"
      using word_product_append[OF hG_grp hmG1 hmGr] happ_map by (by100 simp)
    have heval_G_rev: "?eval_G ?fr2 = invg (?eval_G ws2)"
      using word_product_rev_inv[OF hG_grp hmG2] hmap_fliprev by (by100 simp)
    have heval_G_e: "?eval_G ?ws3 = e"
    proof -
      have "?eval_G ?ws3 = mul (?eval_G ws1) (invg (?eval_G ws2))"
        using heval_G_split heval_G_rev by (by100 simp)
      also have "\<dots> = mul (?eval_G ws1) (invg (?eval_G ws1))" using 1(3) by (by100 simp)
      also have "\<dots> = e"
      proof -
        have "?eval_G ws1 \<in> G" using word_product_in_group[OF hG_grp hmG1] by (by100 simp)
        thus ?thesis using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      qed
      finally show ?thesis .
    qed
    \<comment> \<open>By word\_kernel: eval\_H(ws3) = eH.\<close>
    have heval_H_e: "?eval_H ?ws3 = eH"
      by (rule free_group_word_kernel[OF assms(1) assms(2) assms(3) hws3_S heval_G_e])
    \<comment> \<open>Decompose eval\_H similarly.\<close>
    have hmH_mapped: "\<And>ws. \<forall>i<length ws. fst(ws!i) \<in> S \<Longrightarrow>
        \<forall>j<length (map (\<lambda>(s,b). (\<phi> s, b)) ws). fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! j) \<in> H"
    proof (intro allI impI)
      fix ws and j
      assume h: "\<forall>i<length ws. fst(ws!i) \<in> S" and hj: "j < length (map (\<lambda>(s,b). (\<phi> s, b)) ws)"
      hence hjw: "j < length ws" by (by100 simp)
      obtain sj bj where hwj: "ws ! j = (sj, bj)" by (cases "ws!j") (by100 blast)
      have "sj \<in> S" using h hjw hwj by (by100 force)
      hence "\<phi> sj \<in> H" using assms(3) by (by100 blast)
      thus "fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! j) \<in> H" using hjw hwj by simp
    qed
    have hmap_fliprev_H: "map (\<lambda>(s,b). (\<phi> s, b)) ?fr2
        = map (\<lambda>(x,b). (x, \<not>b)) (rev (map (\<lambda>(s,b). (\<phi> s, b)) ws2))"
      by (induct ws2) auto
    have heval_H_split: "?eval_H ?ws3 = mulH (?eval_H ws1) (?eval_H ?fr2)"
    proof -
      have "map (\<lambda>(s,b). (\<phi> s, b)) ?ws3 =
          map (\<lambda>(s,b). (\<phi> s, b)) ws1 @ map (\<lambda>(s,b). (\<phi> s, b)) ?fr2" by (by100 simp)
      thus ?thesis
        using word_product_append[OF assms(2) hmH_mapped[OF 1(1)] hmH_mapped[OF hfr2_S]] by (by100 simp)
    qed
    have heval_H_rev: "?eval_H ?fr2 = invgH (?eval_H ws2)"
      using word_product_rev_inv[OF assms(2) hmH_mapped[OF 1(2)]] hmap_fliprev_H by (by100 simp)
    \<comment> \<open>Combine: mulH (eval\_H ws1) (invgH (eval\_H ws2)) = eH.\<close>
    have "mulH (?eval_H ws1) (invgH (?eval_H ws2)) = eH"
      using heval_H_e heval_H_split heval_H_rev by (by100 simp)
    \<comment> \<open>Right-multiply by eval\_H ws2.\<close>
    hence "mulH (mulH (?eval_H ws1) (invgH (?eval_H ws2))) (?eval_H ws2) = mulH eH (?eval_H ws2)"
      by (by100 simp)
    hence "?eval_H ws1 = ?eval_H ws2"
    proof -
      have hH1: "?eval_H ws1 \<in> H" using word_product_in_group[OF assms(2) hmH_mapped[OF 1(1)]] by (by100 simp)
      have hH2: "?eval_H ws2 \<in> H" using word_product_in_group[OF assms(2) hmH_mapped[OF 1(2)]] by (by100 simp)
      have hiH2: "invgH (?eval_H ws2) \<in> H" using assms(2) hH2 unfolding top1_is_group_on_def by (by100 blast)
      \<comment> \<open>a \<cdot> b\<inverse> = eH \<Longrightarrow> a = b.\<close>
      \<comment> \<open>a \<cdot> b\<inverse> = eH implies a \<cdot> b\<inverse> \<cdot> b = eH \<cdot> b = b, and a \<cdot> (b\<inverse> \<cdot> b) = a \<cdot> eH = a. So a = b.\<close>
      have hcancel: "mulH (invgH (?eval_H ws2)) (?eval_H ws2) = eH"
        using assms(2) hH2 unfolding top1_is_group_on_def by (by100 blast)
      have hid_r: "mulH (?eval_H ws1) eH = ?eval_H ws1"
        using assms(2) hH1 unfolding top1_is_group_on_def by (by100 blast)
      have "?eval_H ws1 = mulH (?eval_H ws1) eH"
        using hid_r by (by100 simp)
      also have "\<dots> = mulH (?eval_H ws1) (mulH (invgH (?eval_H ws2)) (?eval_H ws2))"
        using hcancel by (by100 simp)
      also have "\<dots> = mulH (mulH (?eval_H ws1) (invgH (?eval_H ws2))) (?eval_H ws2)"
      proof -
        have "mulH (mulH (?eval_H ws1) (invgH (?eval_H ws2))) (?eval_H ws2)
            = mulH (?eval_H ws1) (mulH (invgH (?eval_H ws2)) (?eval_H ws2))"
          using assms(2) hH1 hiH2 hH2 unfolding top1_is_group_on_def by (by100 blast)
        thus ?thesis by (by100 simp)
      qed
      also have "\<dots> = mulH eH (?eval_H ws2)"
        using \<open>mulH (?eval_H ws1) (invgH (?eval_H ws2)) = eH\<close> by (by100 simp)
      also have "\<dots> = ?eval_H ws2"
        using assms(2) hH2 unfolding top1_is_group_on_def by (by100 blast)
      finally show ?thesis .
    qed
    thus ?case .
  qed
  \<comment> \<open>Helper: mapped word elements are in H.\<close>
  have hmH_mapped: "\<And>ws. \<forall>i<length ws. fst(ws!i) \<in> S \<Longrightarrow>
      \<forall>j<length (map (\<lambda>(s,b). (\<phi> s, b)) ws). fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! j) \<in> H"
  proof (intro allI impI)
    fix ws and j
    assume h: "\<forall>i<length ws. fst(ws!i) \<in> S" and hj: "j < length (map (\<lambda>(s,b). (\<phi> s, b)) ws)"
    hence hjw: "j < length ws" by (by100 simp)
    obtain sj bj where hwj: "ws ! j = (sj, bj)" by (cases "ws!j") (by100 blast)
    have "sj \<in> S" using h hjw hwj by (by100 force)
    hence "\<phi> sj \<in> H" using assms(3) by (by100 blast)
    thus "fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! j) \<in> H" using hjw hwj by simp
  qed
  \<comment> \<open>Helper: for g \<in> G, SOME picks a valid word, and \<psi>(g) = eval\_H of any valid word.\<close>
  have hpsi_wd: "\<And>g ws. g \<in> G \<Longrightarrow> (\<forall>i<length ws. fst (ws ! i) \<in> S) \<Longrightarrow> ?eval_G ws = g \<Longrightarrow>
      ?\<psi> g = ?eval_H ws"
  proof -
    fix g ws
    assume hg: "g \<in> G" and hws: "\<forall>i<length ws. fst (ws ! i) \<in> S" and heval: "?eval_G ws = g"
    \<comment> \<open>SOME picks some word ws' with eval\_G(ws') = g.\<close>
    have "\<exists>ws'. (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<and> ?eval_G ws' = g"
      using hws heval by (by100 blast)
    hence hsome: "(\<forall>i<length (SOME ws'. (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<and> ?eval_G ws' = g).
        fst ((SOME ws'. (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<and> ?eval_G ws' = g) ! i) \<in> S)
      \<and> ?eval_G (SOME ws'. (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<and> ?eval_G ws' = g) = g"
      by (rule someI_ex)
    \<comment> \<open>By well-definedness, eval\_H of SOME word = eval\_H of ws.\<close>
    let ?ws' = "SOME ws'. (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<and> ?eval_G ws' = g"
    have hsome1: "\<forall>i<length ?ws'. fst (?ws' ! i) \<in> S" using hsome by (by100 blast)
    have hsome2: "?eval_G ?ws' = g" using hsome by (by100 blast)
    have "?eval_G ?ws' = ?eval_G ws" using hsome2 heval by (by100 simp)
    thus "?\<psi> g = ?eval_H ws" by (rule hwd[OF hsome1 hws])
  qed
  \<comment> \<open>Step 4: \<psi> is a homomorphism.\<close>
  have hhom: "top1_group_hom_on G mul H mulH ?\<psi>"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    \<comment> \<open>\<psi>(g) \<in> H for g \<in> G.\<close>
    fix g assume hg: "g \<in> G"
    have "g \<in> ?W" using hg hW_eq_G by (by100 simp)
    then obtain ws where hws: "\<forall>i<length ws. fst (ws ! i) \<in> S" "?eval_G ws = g"
      by (by100 blast)
    have "?\<psi> g = ?eval_H ws" by (rule hpsi_wd[OF hg hws(1) hws(2)])
    also have "\<dots> \<in> H" by (rule word_product_in_group[OF assms(2) hmH_mapped[OF hws(1)]])
    finally show "?\<psi> g \<in> H" .
  next
    \<comment> \<open>\<psi>(g1 \<cdot> g2) = mulH(\<psi> g1)(\<psi> g2).\<close>
    fix g1 g2 assume hg1: "g1 \<in> G" and hg2: "g2 \<in> G"
    \<comment> \<open>Get word representations.\<close>
    have "g1 \<in> ?W" using hg1 hW_eq_G by (by100 simp)
    then obtain ws1 where hws1: "\<forall>i<length ws1. fst (ws1 ! i) \<in> S" "?eval_G ws1 = g1"
      by (by100 blast)
    have "g2 \<in> ?W" using hg2 hW_eq_G by (by100 simp)
    then obtain ws2 where hws2: "\<forall>i<length ws2. fst (ws2 ! i) \<in> S" "?eval_G ws2 = g2"
      by (by100 blast)
    \<comment> \<open>ws1 @ ws2 is a word for mul g1 g2.\<close>
    have happ_S: "\<forall>i<length (ws1 @ ws2). fst ((ws1 @ ws2) ! i) \<in> S"
      using hws1(1) hws2(1) by (simp add: nth_append)
    have hmap_app: "map (\<lambda>(s,b). (\<iota> s, b)) (ws1 @ ws2) =
        map (\<lambda>(s,b). (\<iota> s, b)) ws1 @ map (\<lambda>(s,b). (\<iota> s, b)) ws2" by (by100 simp)
    have heval_app: "?eval_G (ws1 @ ws2) = mul g1 g2"
      using word_product_append[OF hG_grp hmapped_G[OF hws1(1)] hmapped_G[OF hws2(1)]]
            hmap_app hws1(2) hws2(2) by (by100 simp)
    have hmul_G: "mul g1 g2 \<in> G"
      using hG_grp hg1 hg2 unfolding top1_is_group_on_def by (by100 blast)
    \<comment> \<open>\<psi>(mul g1 g2) = eval\_H(ws1 @ ws2) by well-definedness.\<close>
    have "?\<psi> (mul g1 g2) = ?eval_H (ws1 @ ws2)"
      by (rule hpsi_wd[OF hmul_G happ_S heval_app])
    \<comment> \<open>eval\_H(ws1 @ ws2) = mulH(eval\_H ws1)(eval\_H ws2).\<close>
    also have "\<dots> = mulH (?eval_H ws1) (?eval_H ws2)"
    proof -
      have "map (\<lambda>(s,b). (\<phi> s, b)) (ws1 @ ws2) =
          map (\<lambda>(s,b). (\<phi> s, b)) ws1 @ map (\<lambda>(s,b). (\<phi> s, b)) ws2" by (by100 simp)
      thus ?thesis
        using word_product_append[OF assms(2) hmH_mapped[OF hws1(1)] hmH_mapped[OF hws2(1)]]
        by (by100 simp)
    qed
    \<comment> \<open>eval\_H(wsi) = \<psi>(gi) by well-definedness.\<close>
    also have "?eval_H ws1 = ?\<psi> g1" using hpsi_wd[OF hg1 hws1(1) hws1(2)] by (by100 simp)
    also have "?eval_H ws2 = ?\<psi> g2" using hpsi_wd[OF hg2 hws2(1) hws2(2)] by (by100 simp)
    finally show "?\<psi> (mul g1 g2) = mulH (?\<psi> g1) (?\<psi> g2)" by (by100 simp)
  qed
  \<comment> \<open>Step 5: \<psi>(\<iota>(s)) = \<phi>(s).\<close>
  have hext: "\<forall>s\<in>S. ?\<psi> (\<iota> s) = \<phi> s"
  proof (intro ballI)
    fix s assume hs: "s \<in> S"
    \<comment> \<open>The word [(s, True)] evaluates to \<iota>(s) in G.\<close>
    have hws_S: "\<forall>i<length [(s, True)]. fst ([(s, True)] ! i) \<in> S"
      using hs by (by100 simp)
    have heval_s: "?eval_G [(s, True)] = \<iota> s"
    proof -
      have "?eval_G [(s, True)] = mul (\<iota> s) e" by (by100 simp)
      also have "\<dots> = \<iota> s"
        using hG_grp hG_in hs unfolding top1_is_group_on_def by (by100 blast)
      finally show ?thesis .
    qed
    have hiota_G: "\<iota> s \<in> G" using hG_in hs by (by100 blast)
    \<comment> \<open>By well-definedness: \<psi>(\<iota> s) = eval\_H([(s, True)]).\<close>
    have "?\<psi> (\<iota> s) = ?eval_H [(s, True)]"
      by (rule hpsi_wd[OF hiota_G hws_S heval_s])
    \<comment> \<open>eval\_H([(s, True)]) = \<phi>(s).\<close>
    also have "\<dots> = mulH (\<phi> s) eH" by (by100 simp)
    also have "\<dots> = \<phi> s"
      using assms(2,3) hs unfolding top1_is_group_on_def by (by100 blast)
    finally show "?\<psi> (\<iota> s) = \<phi> s" .
  qed
  show ?thesis using hhom hext by (by100 blast)
qed

lemma free_group_universal_property:
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
      and "top1_is_group_on H mulH eH invgH"
      and "\<forall>s\<in>S. \<phi> s \<in> H"
  shows "\<exists>\<psi>. top1_group_hom_on G mul H mulH \<psi> \<and> (\<forall>s\<in>S. \<psi> (\<iota> s) = \<phi> s)
      \<and> (\<forall>\<psi>'. top1_group_hom_on G mul H mulH \<psi>' \<and> (\<forall>s\<in>S. \<psi>' (\<iota> s) = \<phi> s)
          \<longrightarrow> (\<forall>g\<in>G. \<psi>' g = \<psi> g))"
proof -
  have hG: "top1_is_group_on G mul e invg"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hgen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hS: "\<forall>s\<in>S. \<iota> s \<in> G"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  obtain \<psi> where h\<psi>: "top1_group_hom_on G mul H mulH \<psi>"
      and h\<psi>_ext: "\<forall>s\<in>S. \<psi> (\<iota> s) = \<phi> s"
    using free_group_hom_exists[OF assms] by (by100 blast)
  have huniq: "\<forall>\<psi>'. top1_group_hom_on G mul H mulH \<psi>' \<and> (\<forall>s\<in>S. \<psi>' (\<iota> s) = \<phi> s)
      \<longrightarrow> (\<forall>g\<in>G. \<psi>' g = \<psi> g)"
  proof (intro allI impI)
    fix \<psi>' assume h': "top1_group_hom_on G mul H mulH \<psi>' \<and> (\<forall>s\<in>S. \<psi>' (\<iota> s) = \<phi> s)"
    have h'_hom: "top1_group_hom_on G mul H mulH \<psi>'" using h' by (by100 blast)
    have "\<forall>s\<in>S. \<psi>' (\<iota> s) = \<psi> (\<iota> s)" using h' h\<psi>_ext by (by100 simp)
    thus "\<forall>g\<in>G. \<psi>' g = \<psi> g"
      by (rule free_group_hom_unique[OF hG assms(2) hgen hS h'_hom h\<psi>])
  qed
  show ?thesis using h\<psi> h\<psi>_ext huniq by (by100 blast)
qed

text \<open>Corollary: the exponent sum homomorphism. For each generator s0,
  there is a homomorphism \<epsilon>_{s0}: G \<rightarrow> (Z, +) counting the s0-exponent.\<close>
lemma free_group_exponent_sum:
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
      and "s0 \<in> S"
  shows "\<exists>\<epsilon>. top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>
           \<and> \<epsilon> (\<iota> s0) = 1
           \<and> (\<forall>s\<in>S. s \<noteq> s0 \<longrightarrow> \<epsilon> (\<iota> s) = 0)"
proof -
  let ?\<phi> = "\<lambda>s. if s = s0 then (1::int) else (0::int)"
  have hZ_grp: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
    unfolding top1_is_group_on_def by (by100 auto)
  have hphi_in: "\<forall>s\<in>S. ?\<phi> s \<in> (UNIV::int set)" by (by100 blast)
  from free_group_hom_exists[OF assms(1) hZ_grp hphi_in]
  obtain \<psi> where h\<psi>: "top1_group_hom_on G mul (UNIV::int set) (+) \<psi>"
      and h\<psi>_ext: "\<forall>s\<in>S. \<psi> (\<iota> s) = ?\<phi> s"
    by (by100 blast)
  have "\<psi> (\<iota> s0) = 1" using h\<psi>_ext assms(2) by (by100 simp)
  moreover have "\<forall>s\<in>S. s \<noteq> s0 \<longrightarrow> \<psi> (\<iota> s) = 0" using h\<psi>_ext by (by100 auto)
  ultimately show ?thesis using h\<psi> by (by100 blast)
qed

text \<open>Commutator subgroup elements have zero exponent sum for all generators.\<close>
lemma commutator_zero_exponent:
  assumes "top1_is_group_on G mul e invg"
      and "top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>"
  shows "\<forall>g\<in>top1_commutator_subgroup_on G mul e invg. \<epsilon> g = 0"
proof (intro ballI)
  fix g assume hg: "g \<in> top1_commutator_subgroup_on G mul e invg"
  have hZ_abel: "top1_is_abelian_group_on (UNIV::int set) (+) (0::int) uminus"
    unfolding top1_is_abelian_group_on_def top1_is_group_on_def by (by100 auto)
  have hcomm_ker: "top1_commutator_subgroup_on G mul e invg
      \<subseteq> top1_group_kernel_on G (0::int) \<epsilon>"
    by (rule Lemma_69_3_commutator_in_kernel[OF assms(1) hZ_abel assms(2)])
  hence "g \<in> top1_group_kernel_on G (0::int) \<epsilon>" using hg by (by100 blast)
  thus "\<epsilon> g = 0" unfolding top1_group_kernel_on_def by (by100 blast)
qed

lemma group_pow_in_group:
  assumes "top1_is_group_on G mul e invg" and "x \<in> G"
  shows "top1_group_pow mul e x n \<in> G"
proof (induction n)
  case 0 thus ?case using assms(1) unfolding top1_is_group_on_def by (by100 simp)
next
  case (Suc n)
  have "mul x (top1_group_pow mul e x n) \<in> G"
    using assms Suc.IH unfolding top1_is_group_on_def by (by100 blast)
  thus ?case by (by100 simp)
qed

text \<open>Integer group\_pow: iterated addition = multiplication.\<close>
lemma int_group_pow: "top1_group_pow (+) (0::int) k n = int n * k"
proof (induction n)
  case 0 show ?case by (by100 simp)
next
  case (Suc n)
  have "top1_group_pow (+) (0::int) k (Suc n) = k + top1_group_pow (+) (0::int) k n"
    by (by100 simp)
  also have "\<dots> = k + int n * k" using Suc.IH by (by100 simp)
  also have "\<dots> = (1 + int n) * k" by (by100 algebra)
  also have "\<dots> = int (Suc n) * k" by (by100 simp)
  finally show ?case .
qed

text \<open>Homomorphism distributes over group\_pow.\<close>
lemma hom_group_pow:
  assumes hG: "top1_is_group_on G mul e invg"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hhom: "top1_group_hom_on G mul H mulH f"
      and hx: "x \<in> G"
  shows "f (top1_group_pow mul e x n) = top1_group_pow mulH eH (f x) n"
proof (induction n)
  case 0
  have "f (top1_group_pow mul e x 0) = f e" by (by100 simp)
  also have "\<dots> = eH" by (rule hom_preserves_id[OF hG hH hhom])
  finally show ?case by (by100 simp)
next
  case (Suc n)
  have hpow_G: "top1_group_pow mul e x n \<in> G" by (rule group_pow_in_group[OF hG hx])
  have "f (top1_group_pow mul e x (Suc n)) = f (mul x (top1_group_pow mul e x n))"
    by (by100 simp)
  also have "\<dots> = mulH (f x) (f (top1_group_pow mul e x n))"
    using hhom hx hpow_G unfolding top1_group_hom_on_def by (by100 blast)
  also have "\<dots> = mulH (f x) (top1_group_pow mulH eH (f x) n)"
    using Suc.IH by (by100 simp)
  finally show ?case by (by100 simp)
qed

text \<open>Homomorphism distributes over foldr mul.\<close>
lemma hom_foldr_mul:
  assumes hG: "top1_is_group_on G mul e invg"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hhom: "top1_group_hom_on G mul H mulH f"
      and hxs: "\<forall>i<length xs. xs!i \<in> G"
  shows "f (foldr mul xs e) = foldr mulH (map f xs) eH"
  using hxs
proof (induction xs)
  case Nil show ?case using hom_preserves_id[OF hG hH hhom] by (by100 simp)
next
  case (Cons a xs')
  have ha: "a \<in> G" using Cons.prems by (by100 force)
  have hxs': "\<forall>i<length xs'. xs'!i \<in> G" using Cons.prems by (by100 force)
  have hprod: "foldr mul xs' e \<in> G"
    by (rule foldr_mul_closed[OF hG hxs'])
  have "f (foldr mul (a # xs') e) = f (mul a (foldr mul xs' e))" by (by100 simp)
  also have "\<dots> = mulH (f a) (f (foldr mul xs' e))"
    using hhom ha hprod unfolding top1_group_hom_on_def by (by100 blast)
  also have "\<dots> = mulH (f a) (foldr mulH (map f xs') eH)"
    using Cons.IH[OF hxs'] by (by100 simp)
  finally show ?case by (by100 simp)
qed

text \<open>The quotient map G \<rightarrow> G/[G,G] is injective on generators of a free group.
  Extracted from Theorem 69.4 proof for reuse.\<close>
lemma abelianization_injective_on_generators:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and \<iota> :: "'s \<Rightarrow> 'g" and S :: "'s set"
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
  shows "inj_on (\<lambda>s. top1_group_coset_on G mul
      (top1_commutator_subgroup_on G mul e invg) (\<iota> s)) S"
proof -
  have hG: "top1_is_group_on G mul e invg"
    using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hgen_in_G: "\<forall>s\<in>S. \<iota> s \<in> G"
    using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
  let ?N = "top1_commutator_subgroup_on G mul e invg"
  let ?\<phi> = "\<lambda>g. top1_group_coset_on G mul ?N g"
  show ?thesis
  proof (rule inj_onI)
    fix s1 s2 assume hs1: "s1 \<in> S" and hs2: "s2 \<in> S" and heq: "?\<phi> (\<iota> s1) = ?\<phi> (\<iota> s2)"
    show "s1 = s2"
    proof (rule ccontr)
      assume hne: "s1 \<noteq> s2"
      obtain \<epsilon> where heps_hom: "top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>"
          and heps_s1: "\<epsilon> (\<iota> s1) = 1"
          and heps_other: "\<forall>s\<in>S. s \<noteq> s1 \<longrightarrow> \<epsilon> (\<iota> s) = 0"
        using free_group_exponent_sum[OF assms hs1] by (by100 blast)
      have h_comm_ker: "\<forall>g\<in>?N. \<epsilon> g = 0"
        by (rule commutator_zero_exponent[OF hG heps_hom])
      have hs1G: "\<iota> s1 \<in> G" using hgen_in_G hs1 by (by100 blast)
      have hs2G: "\<iota> s2 \<in> G" using hgen_in_G hs2 by (by100 blast)
      \<comment> \<open>Coset equality \<Rightarrow> \<iota>(s1)\<cdot>invg(\<iota>(s2)) \<in> [G,G].\<close>
      have hprod_N: "mul (\<iota> s1) (invg (\<iota> s2)) \<in> ?N"
      proof -
        have hN_normal: "top1_normal_subgroup_on G mul e invg ?N"
          by (rule commutator_subgroup_is_normal[OF hG])
        have heq_sym: "?\<phi> (\<iota> s2) = ?\<phi> (\<iota> s1)" using heq by (by100 simp)
        have "mul (invg (\<iota> s2)) (\<iota> s1) \<in> ?N"
          using normal_coset_eq[OF hG hN_normal hs2G hs1G] heq_sym by (by100 blast)
        have hinvs2: "invg (\<iota> s2) \<in> G" using hG hs2G unfolding top1_is_group_on_def by (by100 blast)
        have hconj0: "mul (mul (\<iota> s1) (mul (invg (\<iota> s2)) (\<iota> s1))) (invg (\<iota> s1)) \<in> ?N"
          using hN_normal hs1G \<open>mul (invg (\<iota> s2)) (\<iota> s1) \<in> ?N\<close>
          unfolding top1_normal_subgroup_on_def by (by100 blast)
        have "mul (mul (invg (\<iota> s2)) (\<iota> s1)) (invg (\<iota> s1)) = invg (\<iota> s2)"
        proof -
          have "mul (mul (invg (\<iota> s2)) (\<iota> s1)) (invg (\<iota> s1))
              = mul (invg (\<iota> s2)) (mul (\<iota> s1) (invg (\<iota> s1)))"
            using hG hinvs2 hs1G unfolding top1_is_group_on_def by (by100 blast)
          also have "mul (\<iota> s1) (invg (\<iota> s1)) = e"
            using hG hs1G unfolding top1_is_group_on_def by (by100 blast)
          also have "mul (invg (\<iota> s2)) e = invg (\<iota> s2)"
            using hG hinvs2 unfolding top1_is_group_on_def by (by100 blast)
          finally show ?thesis .
        qed
        have hprod_in_G: "mul (invg (\<iota> s2)) (\<iota> s1) \<in> G"
          using hG hinvs2 hs1G unfolding top1_is_group_on_def by (by100 blast)
        have hinvs1: "invg (\<iota> s1) \<in> G" using hG hs1G unfolding top1_is_group_on_def by (by100 blast)
        have "mul (mul (\<iota> s1) (mul (invg (\<iota> s2)) (\<iota> s1))) (invg (\<iota> s1))
            = mul (\<iota> s1) (mul (mul (invg (\<iota> s2)) (\<iota> s1)) (invg (\<iota> s1)))"
          using hG hs1G hprod_in_G hinvs1 unfolding top1_is_group_on_def by (by100 blast)
        hence "mul (\<iota> s1) (mul (mul (invg (\<iota> s2)) (\<iota> s1)) (invg (\<iota> s1))) \<in> ?N"
          using hconj0 by (by100 simp)
        hence "mul (\<iota> s1) (invg (\<iota> s2)) \<in> ?N"
          using \<open>mul (mul (invg (\<iota> s2)) (\<iota> s1)) (invg (\<iota> s1)) = invg (\<iota> s2)\<close> by (by100 simp)
        thus ?thesis .
      qed
      \<comment> \<open>\<epsilon>-value contradiction.\<close>
      have heps_zero: "\<epsilon> (mul (\<iota> s1) (invg (\<iota> s2))) = 0" using h_comm_ker hprod_N by (by100 blast)
      have hinvG_s2: "invg (\<iota> s2) \<in> G"
        using hG hs2G unfolding top1_is_group_on_def by (by100 blast)
      have "\<epsilon> (mul (\<iota> s1) (invg (\<iota> s2))) = \<epsilon> (\<iota> s1) + \<epsilon> (invg (\<iota> s2))"
        using heps_hom hs1G hinvG_s2 unfolding top1_group_hom_on_def by (by100 blast)
      moreover have "\<epsilon> (invg (\<iota> s2)) = - \<epsilon> (\<iota> s2)"
      proof -
        have hZ_grp: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
          unfolding top1_is_group_on_def by (by100 auto)
        show ?thesis by (rule hom_preserves_inv[OF hG hZ_grp heps_hom hs2G])
      qed
      moreover have "\<epsilon> (\<iota> s2) = 0" using heps_other hs2 hne[symmetric] by (by100 blast)
      ultimately show False using heps_s1 heps_zero by (by100 simp)
    qed
  qed
qed

text \<open>Independence of generators in the abelianization.
  Extracted from Theorem 69.4 proof for reuse.\<close>
lemma abelianization_independence_on_generators:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and \<iota> :: "'s \<Rightarrow> 'g" and S :: "'s set"
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
      and "finite {s\<in>S. c s \<noteq> 0}" and "\<exists>s\<in>S. c s \<noteq> 0"
  shows "foldr (top1_quotient_group_mul_on mul)
      (map (\<lambda>s.
          if c s \<ge> 0 then top1_group_pow (top1_quotient_group_mul_on mul)
              (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) e)
              (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) (\<iota> s))
              (nat (c s))
          else top1_group_pow (top1_quotient_group_mul_on mul)
              (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) e)
              ((\<lambda>C. top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg)
                 (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul
                    (top1_commutator_subgroup_on G mul e invg) g)))
               (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) (\<iota> s)))
              (nat (- c s)))
        (SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs))
      (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) e)
    \<noteq> top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) e"
proof -
  have hG: "top1_is_group_on G mul e invg"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hgen_in_G: "\<forall>s\<in>S. \<iota> s \<in> G"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  let ?N = "top1_commutator_subgroup_on G mul e invg"
  let ?mulH = "top1_quotient_group_mul_on mul"
  let ?eH = "top1_group_coset_on G mul ?N e"
  let ?invgH = "\<lambda>C. top1_group_coset_on G mul ?N (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul ?N g))"
  let ?\<phi> = "\<lambda>g. top1_group_coset_on G mul ?N g"
  let ?\<iota>H = "\<lambda>s. ?\<phi> (\<iota> s)"
  have h_abel: "top1_is_abelianization_of
      (top1_quotient_group_carrier_on G mul ?N) ?mulH ?eH ?invgH G mul e invg ?\<phi>"
    by (rule abelianization_concrete[OF hG])
  have hH_abel: "top1_is_abelian_group_on
      (top1_quotient_group_carrier_on G mul ?N) ?mulH ?eH ?invgH"
    using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
  have hphi_hom: "top1_group_hom_on G mul (top1_quotient_group_carrier_on G mul ?N) ?mulH ?\<phi>"
    using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
  \<comment> \<open>The proof follows the same structure as Theorem 69.4's hH\_indep.
     For the given nonzero c with support s0, use the exponent sum \<epsilon>
     to show the G-level product has \<epsilon>-value c(s0) \<noteq> 0,
     contradicting membership in [G,G].\<close>
  from assms(3) obtain s0 where hs0: "s0 \<in> S" "c s0 \<noteq> 0" by (by100 blast)
  obtain \<epsilon> where heps: "top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>"
      and heps_s0: "\<epsilon> (\<iota> s0) = 1"
      and heps_other: "\<forall>s\<in>S. s \<noteq> s0 \<longrightarrow> \<epsilon> (\<iota> s) = 0"
    using free_group_exponent_sum[OF assms(1) hs0(1)] by (by100 blast)
  have hcomm_ker: "\<forall>g\<in>?N. \<epsilon> g = 0"
    by (rule commutator_zero_exponent[OF hG heps])
  let ?xs = "SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs"
  let ?gp = "foldr mul (map (\<lambda>s.
        if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
        else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s)))
      ?xs) e"
  \<comment> \<open>\<epsilon>(gp) = c(s0) (proved in Theorem 69.4).\<close>
  have heps_gp: "\<epsilon> ?gp = c s0"
  proof -
    have hZ: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
      unfolding top1_is_group_on_def by (by100 auto)
    \<comment> \<open>Step 1: \<epsilon> of each term = c(s)\<cdot>\<epsilon>(\<iota>(s)).\<close>
    have heps_term: "\<And>s. s \<in> S \<Longrightarrow>
        \<epsilon> (if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
            else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))) = c s * \<epsilon> (\<iota> s)"
    proof -
      fix s assume hs: "s \<in> S"
      have h\<iota>s: "\<iota> s \<in> G" using hgen_in_G hs by (by100 blast)
      have hinvs: "invg (\<iota> s) \<in> G" using hG h\<iota>s unfolding top1_is_group_on_def by (by100 blast)
      show "\<epsilon> (if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
          else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))) = c s * \<epsilon> (\<iota> s)"
      proof (cases "c s \<ge> 0")
        case True
        have "\<epsilon> (top1_group_pow mul e (\<iota> s) (nat (c s)))
            = top1_group_pow (+) (0::int) (\<epsilon> (\<iota> s)) (nat (c s))"
          by (rule hom_group_pow[OF hG hZ heps h\<iota>s])
        also have "\<dots> = int (nat (c s)) * \<epsilon> (\<iota> s)" by (rule int_group_pow)
        also have "int (nat (c s)) = c s" using True by (by100 simp)
        finally show ?thesis using True by (by100 simp)
      next
        case False
        have "\<epsilon> (top1_group_pow mul e (invg (\<iota> s)) (nat (- c s)))
            = top1_group_pow (+) (0::int) (\<epsilon> (invg (\<iota> s))) (nat (- c s))"
          by (rule hom_group_pow[OF hG hZ heps hinvs])
        also have "\<dots> = int (nat (- c s)) * \<epsilon> (invg (\<iota> s))" by (rule int_group_pow)
        also have "\<epsilon> (invg (\<iota> s)) = - \<epsilon> (\<iota> s)"
          by (rule hom_preserves_inv[OF hG hZ heps h\<iota>s])
        also have "int (nat (- c s)) * (- \<epsilon> (\<iota> s)) = c s * \<epsilon> (\<iota> s)"
          using False by (by100 simp)
        finally show ?thesis using False by (by100 simp)
      qed
    qed
    \<comment> \<open>Step 2: \<epsilon> distributes over foldr.\<close>
    let ?gterm = "\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
        else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))"
    {fix ys :: "'s list"
     assume hys: "\<forall>i<length ys. ys!i \<in> S"
     hence "\<epsilon> (foldr mul (map ?gterm ys) e) = (\<Sum>s\<leftarrow>ys. c s * \<epsilon> (\<iota> s))"
     proof (induction ys)
       case Nil show ?case using hom_preserves_id[OF hG hZ heps] by (by100 simp)
     next
       case (Cons s ys')
       have hs: "s \<in> S" using Cons.prems by (by100 force)
       have hys': "\<forall>i<length ys'. ys'!i \<in> S" using Cons.prems by (by100 force)
       have hgs: "?gterm s \<in> G"
       proof -
         have h\<iota>s: "\<iota> s \<in> G" using hgen_in_G hs by (by100 blast)
         have hinvs: "invg (\<iota> s) \<in> G" using hG h\<iota>s unfolding top1_is_group_on_def by (by100 blast)
         show ?thesis using group_pow_in_group[OF hG h\<iota>s] group_pow_in_group[OF hG hinvs] by (by100 auto)
       qed
       have hprod: "foldr mul (map ?gterm ys') e \<in> G"
       proof (rule foldr_mul_closed[OF hG])
         show "\<forall>i<length (map ?gterm ys'). (map ?gterm ys')!i \<in> G"
         proof (intro allI impI)
           fix i assume hi: "i < length (map ?gterm ys')"
           have hsi: "ys'!i \<in> S" using hys' hi by (by100 simp)
           have h\<iota>si: "\<iota> (ys'!i) \<in> G" using hgen_in_G hsi by (by100 blast)
           have hinvsi: "invg (\<iota> (ys'!i)) \<in> G" using hG h\<iota>si unfolding top1_is_group_on_def by (by100 blast)
           show "(map ?gterm ys')!i \<in> G" using hi group_pow_in_group[OF hG h\<iota>si] group_pow_in_group[OF hG hinvsi] by (by100 auto)
         qed
       qed
       have "\<epsilon> (foldr mul (map ?gterm (s # ys')) e)
           = \<epsilon> (mul (?gterm s) (foldr mul (map ?gterm ys') e))" by (by100 simp)
       also have "\<dots> = \<epsilon> (?gterm s) + \<epsilon> (foldr mul (map ?gterm ys') e)"
         using heps hgs hprod unfolding top1_group_hom_on_def by (by100 blast)
       also have "\<epsilon> (?gterm s) = c s * \<epsilon> (\<iota> s)" by (rule heps_term[OF hs])
       also have "c s * \<epsilon> (\<iota> s) + \<epsilon> (foldr mul (map ?gterm ys') e)
           = c s * \<epsilon> (\<iota> s) + (\<Sum>s\<leftarrow>ys'. c s * \<epsilon> (\<iota> s))"
         using Cons.IH[OF hys'] by (by100 simp)
       finally show ?case by (by100 simp)
     qed}
    moreover have hxs_S: "\<forall>i<length ?xs. ?xs!i \<in> S"
    proof (intro allI impI)
      fix i assume hi: "i < length ?xs"
      have "\<exists>xs. set xs = {s \<in> S. c s \<noteq> 0} \<and> distinct xs"
        using finite_distinct_list[OF assms(2)] by (by100 blast)
      hence "set ?xs = {s \<in> S. c s \<noteq> 0} \<and> distinct ?xs" by (rule someI_ex)
      thus "?xs!i \<in> S" using nth_mem[OF hi] by (by100 blast)
    qed
    ultimately have hfoldr: "\<epsilon> ?gp = (\<Sum>s\<leftarrow>?xs. c s * \<epsilon> (\<iota> s))" by (by100 simp)
    \<comment> \<open>Step 3: Kronecker delta: sum = c(s0).\<close>
    have hprop: "set ?xs = {s \<in> S. c s \<noteq> 0} \<and> distinct ?xs"
    proof -
      have "\<exists>xs. set xs = {s \<in> S. c s \<noteq> 0} \<and> distinct xs"
        using finite_distinct_list[OF assms(2)] by (by100 blast)
      thus ?thesis by (rule someI_ex)
    qed
    have hs0_in: "s0 \<in> set ?xs" using hprop hs0 by (by100 blast)
    have hdist: "distinct ?xs" using hprop by (by100 blast)
    have "\<And>s. s \<in> set ?xs \<Longrightarrow> c s * \<epsilon> (\<iota> s) = (if s = s0 then c s0 else 0)"
    proof -
      fix s assume hs_in: "s \<in> set ?xs"
      have hs_S: "s \<in> S" using hs_in hprop by (by100 blast)
      show "c s * \<epsilon> (\<iota> s) = (if s = s0 then c s0 else 0)"
      proof (cases "s = s0")
        case True thus ?thesis using heps_s0 by (by100 simp)
      next
        case False thus ?thesis using heps_other hs_S by (by100 simp)
      qed
    qed
    have "map (\<lambda>s. c s * \<epsilon> (\<iota> s)) ?xs = map (\<lambda>s. if s = s0 then c s0 else (0::int)) ?xs"
    proof (rule nth_equalityI)
      show "length (map (\<lambda>s. c s * \<epsilon> (\<iota> s)) ?xs) = length (map (\<lambda>s. if s = s0 then c s0 else 0) ?xs)"
        by (by100 simp)
    next
      fix i assume "i < length (map (\<lambda>s. c s * \<epsilon> (\<iota> s)) ?xs)"
      hence hi: "i < length ?xs" by (by100 simp)
      hence "?xs!i \<in> set ?xs" by (rule nth_mem)
      thus "map (\<lambda>s. c s * \<epsilon> (\<iota> s)) ?xs ! i = map (\<lambda>s. if s = s0 then c s0 else (0::int)) ?xs ! i"
        using \<open>\<And>s. s \<in> set ?xs \<Longrightarrow> c s * \<epsilon> (\<iota> s) = (if s = s0 then c s0 else 0)\<close> hi by (by100 simp)
    qed
    hence "sum_list (map (\<lambda>s. c s * \<epsilon> (\<iota> s)) ?xs) = sum_list (map (\<lambda>s. if s = s0 then c s0 else (0::int)) ?xs)"
      by (rule arg_cong[of _ _ sum_list])
    hence "(\<Sum>s\<leftarrow>?xs. c s * \<epsilon> (\<iota> s)) = (\<Sum>s\<leftarrow>?xs. if s = s0 then c s0 else 0)" by (by100 simp)
    also have "\<dots> = c s0"
    proof -
      {fix ys :: "'s list"
       assume hyin: "s0 \<in> set ys" and hdist: "distinct ys"
       hence "(\<Sum>s\<leftarrow>ys. if s = s0 then c s0 else (0::int)) = c s0"
       proof (induction ys)
         case Nil thus ?case by (by100 simp)
       next
         case (Cons a ys')
         show ?case
         proof (cases "a = s0")
           case True
           hence "s0 \<notin> set ys'" using Cons.prems(2) by (by100 force)
           hence "(\<Sum>s\<leftarrow>ys'. if s = s0 then c s0 else (0::int)) = 0"
             by (induction ys') (by100 auto)+
           thus ?thesis using True by (by100 simp)
         next
           case False
           hence "s0 \<in> set ys'" using Cons.prems(1) by (by100 simp)
           moreover have "distinct ys'" using Cons.prems(2) by (by100 simp)
           ultimately show ?thesis using False Cons.IH by (by100 simp)
         qed
       qed}
      thus ?thesis using hs0_in hdist by (by100 blast)
    qed
    finally show ?thesis using hfoldr by (by100 simp)
  qed
  hence "?gp \<notin> ?N" using hcomm_ker hs0(2) by (by100 force)
  \<comment> \<open>The H-product = \<phi>(gp).\<close>
  have hH_grp: "top1_is_group_on (top1_quotient_group_carrier_on G mul ?N) ?mulH ?eH ?invgH"
    using hH_abel unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hH_prod_eq: "foldr ?mulH (map (\<lambda>s.
        if c s \<ge> 0 then top1_group_pow ?mulH ?eH (?\<iota>H s) (nat (c s))
        else top1_group_pow ?mulH ?eH (?invgH (?\<iota>H s)) (nat (- c s)))
      ?xs) ?eH = ?\<phi> ?gp"
  proof -
    let ?hterm = "\<lambda>s. if c s \<ge> 0 then top1_group_pow ?mulH ?eH (?\<iota>H s) (nat (c s))
        else top1_group_pow ?mulH ?eH (?invgH (?\<iota>H s)) (nat (- c s))"
    let ?gterm = "\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
        else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))"
    \<comment> \<open>h\_term\_eq: \<phi>(gterm s) = hterm s for each s \<in> S.\<close>
    have h_term_eq: "\<And>s. s \<in> S \<Longrightarrow> ?\<phi> (?gterm s) = ?hterm s"
    proof -
      fix s assume hs: "s \<in> S"
      have h\<iota>s: "\<iota> s \<in> G" using hgen_in_G hs by (by100 blast)
      have hinvs: "invg (\<iota> s) \<in> G" using hG h\<iota>s unfolding top1_is_group_on_def by (by100 blast)
      show "?\<phi> (?gterm s) = ?hterm s"
      proof (cases "c s \<ge> 0")
        case True
        have "?\<phi> (top1_group_pow mul e (\<iota> s) (nat (c s)))
            = top1_group_pow ?mulH ?eH (?\<phi> (\<iota> s)) (nat (c s))"
          by (rule hom_group_pow[OF hG hH_grp hphi_hom h\<iota>s])
        thus ?thesis using True by (by100 simp)
      next
        case False
        have "?\<phi> (top1_group_pow mul e (invg (\<iota> s)) (nat (- c s)))
            = top1_group_pow ?mulH ?eH (?\<phi> (invg (\<iota> s))) (nat (- c s))"
          by (rule hom_group_pow[OF hG hH_grp hphi_hom hinvs])
        moreover have "?\<phi> (invg (\<iota> s)) = ?invgH (?\<phi> (\<iota> s))"
          by (rule hom_preserves_inv[OF hG hH_grp hphi_hom h\<iota>s])
        ultimately show ?thesis using False by (by100 simp)
      qed
    qed
    \<comment> \<open>Induction on ?xs.\<close>
    {fix ys :: "'s list"
     assume hys: "\<forall>i<length ys. ys!i \<in> S"
     hence "foldr ?mulH (map ?hterm ys) ?eH = ?\<phi> (foldr mul (map ?gterm ys) e)"
     proof (induction ys)
       case Nil show ?case using hom_preserves_id[OF hG hH_grp hphi_hom] by (by100 simp)
     next
       case (Cons s ys')
       have hs: "s \<in> S" using Cons.prems by (by100 force)
       have hys': "\<forall>i<length ys'. ys'!i \<in> S" using Cons.prems by (by100 force)
       have hgs: "?gterm s \<in> G"
       proof -
         have h\<iota>s: "\<iota> s \<in> G" using hgen_in_G hs by (by100 blast)
         have hinvs: "invg (\<iota> s) \<in> G" using hG h\<iota>s unfolding top1_is_group_on_def by (by100 blast)
         show ?thesis using group_pow_in_group[OF hG h\<iota>s] group_pow_in_group[OF hG hinvs]
           by (by100 auto)
       qed
       have hprod: "foldr mul (map ?gterm ys') e \<in> G"
       proof (rule foldr_mul_closed[OF hG])
         show "\<forall>i<length (map ?gterm ys'). (map ?gterm ys')!i \<in> G"
         proof (intro allI impI)
           fix i assume hi: "i < length (map ?gterm ys')"
           have hsi: "ys'!i \<in> S" using hys' hi by (by100 simp)
           have h\<iota>si: "\<iota> (ys'!i) \<in> G" using hgen_in_G hsi by (by100 blast)
           have hinvsi: "invg (\<iota> (ys'!i)) \<in> G" using hG h\<iota>si unfolding top1_is_group_on_def by (by100 blast)
           show "(map ?gterm ys')!i \<in> G" using hi
             group_pow_in_group[OF hG h\<iota>si] group_pow_in_group[OF hG hinvsi] by (by100 auto)
         qed
       qed
       have "foldr ?mulH (map ?hterm (s # ys')) ?eH
           = ?mulH (?hterm s) (foldr ?mulH (map ?hterm ys') ?eH)" by (by100 simp)
       also have "\<dots> = ?mulH (?hterm s) (?\<phi> (foldr mul (map ?gterm ys') e))"
         using Cons.IH[OF hys'] by (by100 simp)
       also have "?hterm s = ?\<phi> (?gterm s)" using h_term_eq[OF hs] by (by100 simp)
       also have "?mulH (?\<phi> (?gterm s)) (?\<phi> (foldr mul (map ?gterm ys') e))
           = ?\<phi> (mul (?gterm s) (foldr mul (map ?gterm ys') e))"
         using hphi_hom hgs hprod unfolding top1_group_hom_on_def by (by100 blast)
       also have "mul (?gterm s) (foldr mul (map ?gterm ys') e)
           = foldr mul (map ?gterm (s # ys')) e" by (by100 simp)
       finally show ?case by (by100 simp)
     qed}
    moreover have "\<forall>i<length ?xs. ?xs!i \<in> S"
    proof (intro allI impI)
      fix i assume hi: "i < length ?xs"
      have "\<exists>xs. set xs = {s \<in> S. c s \<noteq> 0} \<and> distinct xs"
        using finite_distinct_list[OF assms(2)] by (by100 blast)
      hence "set ?xs = {s \<in> S. c s \<noteq> 0} \<and> distinct ?xs" by (rule someI_ex)
      thus "?xs!i \<in> S" using nth_mem[OF hi] by (by100 blast)
    qed
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>If the H-product = ?eH, then \<phi>(gp) = ?eH, so gp \<in> [G,G]. Contradiction.\<close>
  show ?thesis
  proof
    assume heq: "foldr ?mulH (map (\<lambda>s.
        if c s \<ge> 0 then top1_group_pow ?mulH ?eH (?\<iota>H s) (nat (c s))
        else top1_group_pow ?mulH ?eH (?invgH (?\<iota>H s)) (nat (- c s)))
      ?xs) ?eH = ?eH"
    hence "?\<phi> ?gp = ?eH" using hH_prod_eq by (by100 simp)
    hence "?gp \<in> ?N"
    proof -
      assume hphi_e: "?\<phi> ?gp = ?eH"
      have hker_eq: "top1_group_kernel_on G ?eH ?\<phi> = ?N"
        using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
      have hgp_G: "?gp \<in> G"
      proof (rule foldr_mul_closed[OF hG])
        show "\<forall>i<length (map (\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
            else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))) ?xs).
          (map (\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
            else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))) ?xs) ! i \<in> G"
        proof (intro allI impI)
          fix i assume hi: "i < length (map (\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
            else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))) ?xs)"
          have hsi: "?xs ! i \<in> S"
          proof -
            have "\<exists>xs. set xs = {s \<in> S. c s \<noteq> 0} \<and> distinct xs"
              using finite_distinct_list[OF assms(2)] by (by100 blast)
            hence "set ?xs = {s \<in> S. c s \<noteq> 0} \<and> distinct ?xs" by (rule someI_ex)
            thus ?thesis using nth_mem hi by (by100 force)
          qed
          have h\<iota>si: "\<iota> (?xs!i) \<in> G" using hgen_in_G hsi by (by100 blast)
          have hinvsi: "invg (\<iota> (?xs!i)) \<in> G"
            using hG h\<iota>si unfolding top1_is_group_on_def by (by100 blast)
          show "(map (\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
            else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))) ?xs) ! i \<in> G"
            using hi group_pow_in_group[OF hG h\<iota>si] group_pow_in_group[OF hG hinvsi]
            by (by100 auto)
        qed
      qed
      have "?gp \<in> top1_group_kernel_on G ?eH ?\<phi>"
        unfolding top1_group_kernel_on_def using hgp_G hphi_e by (by100 blast)
      thus "?gp \<in> ?N" using hker_eq by (by100 simp)
    qed
    thus False using \<open>?gp \<notin> ?N\<close> by (by100 blast)
  qed
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
  shows "\<exists>(H :: 'g set set) mulH eH invgH \<phi> \<iota>H.
           top1_is_abelianization_of H mulH eH invgH G mul e invg \<phi>
         \<and> top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>H S
         \<and> (\<forall>s\<in>S. \<iota>H s = \<phi> (\<iota> s))"
proof -
  have hG: "top1_is_group_on G mul e invg"
    using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
  let ?N = "top1_commutator_subgroup_on G mul e invg"
  let ?H = "top1_quotient_group_carrier_on G mul ?N"
  let ?mulH = "top1_quotient_group_mul_on mul"
  let ?eH = "top1_group_coset_on G mul ?N e"
  let ?invgH = "\<lambda>C. top1_group_coset_on G mul ?N
         (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul ?N g))"
  let ?\<phi> = "\<lambda>g. top1_group_coset_on G mul ?N g"
  have h_abel: "top1_is_abelianization_of ?H ?mulH ?eH ?invgH G mul e invg ?\<phi>"
    by (rule abelianization_concrete[OF hG])
  \<comment> \<open>Step 2: \<phi>(\<iota>(S)) generates H and satisfies no nontrivial integer relations
     (exponent sum argument in the free group).\<close>
  let ?\<iota>H = "\<lambda>s. ?\<phi> (\<iota> s)"
  \<comment> \<open>Step 2a: H is abelian (from abelianization).\<close>
  have hH_abel: "top1_is_abelian_group_on ?H ?mulH ?eH ?invgH"
    using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
  \<comment> \<open>Step 2b: \<iota>(s) \<in> G for each s, so \<phi>(\<iota>(s)) \<in> H.\<close>
  have hgen_in_G: "\<forall>s\<in>S. \<iota> s \<in> G"
    using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hphi_surj: "?\<phi> ` G = ?H"
    using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
  have hiotaH_in_H: "\<forall>s\<in>S. ?\<iota>H s \<in> ?H"
  proof (intro ballI)
    fix s assume "s \<in> S"
    hence "\<iota> s \<in> G" using hgen_in_G by (by100 blast)
    thus "?\<iota>H s \<in> ?H" using hphi_surj by (by100 blast)
  qed
  \<comment> \<open>Step 2c: \<iota>H injective on S.
     Proof: if ?\<phi>(\<iota> s1) = ?\<phi>(\<iota> s2), then \<iota> s1 \<cdot> invg(\<iota> s2) \<in> [G,G].
     But in a free group, \<iota> s1 \<cdot> invg(\<iota> s2) for s1 \<noteq> s2 is a non-trivial reduced word,
     and its exponent sums are nonzero, so it cannot be in [G,G].
     (The exponent sum of s1 is +1, of s2 is -1.)\<close>
  have hiotaH_inj: "inj_on ?\<iota>H S"
    by (rule abelianization_injective_on_generators[OF assms])
  \<comment> \<open>Step 2d: H = \<langle>\<iota>H(S)\<rangle> (generated by images of generators).
     Since G = \<langle>\<iota>(S)\<rangle> and \<phi> is surjective, H = \<phi>(G) = \<phi>(\<langle>\<iota>(S)\<rangle>) = \<langle>\<phi>(\<iota>(S))\<rangle> = \<langle>\<iota>H(S)\<rangle>.\<close>
  have hH_gen: "?H = top1_subgroup_generated_on ?H ?mulH ?eH ?invgH (?\<iota>H ` S)"
  proof -
    have hH_grp: "top1_is_group_on ?H ?mulH ?eH ?invgH"
      using hH_abel unfolding top1_is_abelian_group_on_def by (by100 blast)
    have hphi_hom: "top1_group_hom_on G mul ?H ?mulH ?\<phi>"
      using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
    have hphi_surj: "?\<phi> ` G = ?H"
      using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
    have hiotaS_sub: "\<iota> ` S \<subseteq> G"
      using hgen_in_G by (by100 blast)
    have hG_gen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
      using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
    have "?H = top1_subgroup_generated_on ?H ?mulH ?eH ?invgH (?\<phi> ` (\<iota> ` S))"
      by (rule surj_hom_generated[OF hG hH_grp hphi_hom hphi_surj hiotaS_sub hG_gen])
    moreover have "?\<phi> ` (\<iota> ` S) = ?\<iota>H ` S" by (by100 force)
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Step 2e: No nontrivial integer relations.
     For c: S \<rightarrow> Z with finite support and some c(s) \<noteq> 0:
     \<Pi> \<iota>H(s)^{c(s)} = ?\<phi>(\<Pi> \<iota>(s)^{c(s)}) \<noteq> ?eH.
     Because \<Pi> \<iota>(s)^{c(s)} \<notin> ker(\<phi>) = [G,G] (exponent sum argument:
     the exponent sum of s0 in \<Pi> \<iota>(s)^{c(s)} equals c(s0) \<noteq> 0,
     but all elements of [G,G] have zero exponent sums).\<close>
  have hH_indep: "\<forall>c :: 's \<Rightarrow> int.
      finite {s\<in>S. c s \<noteq> 0} \<longrightarrow>
      (\<exists>s\<in>S. c s \<noteq> 0) \<longrightarrow>
      foldr ?mulH (map (\<lambda>s.
          if c s \<ge> 0 then top1_group_pow ?mulH ?eH (?\<iota>H s) (nat (c s))
          else top1_group_pow ?mulH ?eH (?invgH (?\<iota>H s)) (nat (- c s)))
        (SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs)) ?eH \<noteq> ?eH"
    using abelianization_independence_on_generators[OF assms] by (by100 blast)
  \<comment> \<open>Step 2f: Assemble all conditions into free abelian group definition.\<close>
  have h_free_abel: "\<exists>\<iota>H.
      top1_is_free_abelian_group_full_on ?H ?mulH ?eH ?invgH \<iota>H S
    \<and> (\<forall>s\<in>S. \<iota>H s = ?\<phi> (\<iota> s))"
  proof (intro exI conjI)
    show "top1_is_free_abelian_group_full_on ?H ?mulH ?eH ?invgH ?\<iota>H S"
      unfolding top1_is_free_abelian_group_full_on_def
    proof (intro conjI)
      show "top1_is_abelian_group_on ?H ?mulH ?eH ?invgH" by (rule hH_abel)
      show "\<forall>s\<in>S. ?\<iota>H s \<in> ?H" by (rule hiotaH_in_H)
      show "inj_on ?\<iota>H S" by (rule hiotaH_inj)
      show "?H = top1_subgroup_generated_on ?H ?mulH ?eH ?invgH (?\<iota>H ` S)" by (rule hH_gen)
      show "\<forall>c::'s \<Rightarrow> int.
        finite {s \<in> S. c s \<noteq> 0} \<longrightarrow>
        (\<exists>s\<in>S. c s \<noteq> 0) \<longrightarrow>
        foldr ?mulH
         (map (\<lambda>s. if 0 \<le> c s then top1_group_pow ?mulH ?eH (?\<iota>H s) (nat (c s))
                   else top1_group_pow ?mulH ?eH (?invgH (?\<iota>H s)) (nat (- c s)))
           (SOME xs. set xs = {s \<in> S. c s \<noteq> 0} \<and> distinct xs))
         ?eH \<noteq> ?eH" by (rule hH_indep)
    qed
    show "\<forall>s\<in>S. ?\<iota>H s = ?\<phi> (\<iota> s)" by (by100 simp)
  qed
  show ?thesis using h_abel h_free_abel by (by100 blast)
qed

text \<open>Key algebraic fact: if G = F/N where F is free on S and N \<subseteq> [F,F],
  then the abelianization G/[G,G] is isomorphic to F/[F,F] (free abelian on S).
  Proof via first isomorphism theorem: the composition F \<rightarrow> G \<rightarrow> G/[G,G]
  is surjective with kernel [F,F]\<cdot>N = [F,F] (since N \<subseteq> [F,F]).\<close>
text \<open>Independence transfers through group isomorphism: if G has independence
  and f: G \<rightarrow> H is an iso, then H has independence (via f\<inverse>).\<close>
lemma free_abelian_independence_transfer:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and \<iota> :: "'s \<Rightarrow> 'g" and S :: "'s set"
    and H :: "'h set" and mulH :: "'h \<Rightarrow> 'h \<Rightarrow> 'h"
    and eH :: 'h and invgH :: "'h \<Rightarrow> 'h"
    and f :: "'g \<Rightarrow> 'h"
  assumes hG_grp: "top1_is_group_on G mul e invg"
      and hH_grp: "top1_is_group_on H mulH eH invgH"
      and hf_hom: "top1_group_hom_on G mul H mulH f"
      and hf_bij: "bij_betw f G H"
      and h\<iota>_in: "\<forall>s\<in>S. \<iota> s \<in> G"
      and hG_indep: "\<And>c. finite {s\<in>S. c s \<noteq> 0} \<Longrightarrow> (\<exists>s\<in>S. c s \<noteq> 0) \<Longrightarrow>
          foldr mul (map (\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
              else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s)))
            (SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs)) e \<noteq> e"
      and hfin: "finite {s\<in>S. c s \<noteq> 0}" and hex: "\<exists>s\<in>S. c s \<noteq> 0"
  shows "foldr mulH (map (\<lambda>s.
          if c s \<ge> 0 then top1_group_pow mulH eH (f (\<iota> s)) (nat (c s))
          else top1_group_pow mulH eH (invgH (f (\<iota> s))) (nat (- c s)))
        (SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs)) eH \<noteq> eH"
proof -
  let ?gterm = "\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
      else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))"
  let ?hterm = "\<lambda>s. if c s \<ge> 0 then top1_group_pow mulH eH (f (\<iota> s)) (nat (c s))
      else top1_group_pow mulH eH (invgH (f (\<iota> s))) (nat (- c s))"
  let ?xs = "SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs"
  \<comment> \<open>H-product = f(G-product) by induction.\<close>
  {fix ys :: "'s list"
   assume hys: "\<forall>i<length ys. ys!i \<in> S"
   hence "foldr mulH (map ?hterm ys) eH = f (foldr mul (map ?gterm ys) e)"
   proof (induction ys)
     case Nil show ?case using hom_preserves_id[OF hG_grp hH_grp hf_hom] by (by100 simp)
   next
     case (Cons s ys')
     have hs: "s \<in> S" using Cons.prems by (by100 force)
     have hys': "\<forall>i<length ys'. ys'!i \<in> S" using Cons.prems by (by100 force)
     have h\<iota>s: "\<iota> s \<in> G" using h\<iota>_in hs by (by100 blast)
     have hinvs: "invg (\<iota> s) \<in> G" using hG_grp h\<iota>s unfolding top1_is_group_on_def by (by100 blast)
     have hgs: "?gterm s \<in> G"
       using group_pow_in_group[OF hG_grp h\<iota>s] group_pow_in_group[OF hG_grp hinvs] by (by100 auto)
     have hprod: "foldr mul (map ?gterm ys') e \<in> G"
     proof (rule foldr_mul_closed[OF hG_grp])
       show "\<forall>i<length (map ?gterm ys'). (map ?gterm ys')!i \<in> G"
       proof (intro allI impI)
         fix i assume hi: "i < length (map ?gterm ys')"
         have hsi: "ys'!i \<in> S" using hys' hi by (by100 simp)
         have h\<iota>si: "\<iota> (ys'!i) \<in> G" using h\<iota>_in hsi by (by100 blast)
         have hinvsi: "invg (\<iota> (ys'!i)) \<in> G" using hG_grp h\<iota>si unfolding top1_is_group_on_def by (by100 blast)
         show "(map ?gterm ys')!i \<in> G" using hi
           group_pow_in_group[OF hG_grp h\<iota>si] group_pow_in_group[OF hG_grp hinvsi] by (by100 auto)
       qed
     qed
     have h_eq: "f (?gterm s) = ?hterm s"
     proof (cases "c s \<ge> 0")
       case True
       have "f (top1_group_pow mul e (\<iota> s) (nat (c s)))
           = top1_group_pow mulH eH (f (\<iota> s)) (nat (c s))"
         by (rule hom_group_pow[OF hG_grp hH_grp hf_hom h\<iota>s])
       thus ?thesis using True by (by100 simp)
     next
       case False
       have "f (top1_group_pow mul e (invg (\<iota> s)) (nat (- c s)))
           = top1_group_pow mulH eH (f (invg (\<iota> s))) (nat (- c s))"
         by (rule hom_group_pow[OF hG_grp hH_grp hf_hom hinvs])
       moreover have "f (invg (\<iota> s)) = invgH (f (\<iota> s))"
         by (rule hom_preserves_inv[OF hG_grp hH_grp hf_hom h\<iota>s])
       ultimately show ?thesis using False by (by100 simp)
     qed
     have "foldr mulH (map ?hterm (s # ys')) eH
         = mulH (?hterm s) (foldr mulH (map ?hterm ys') eH)" by (by100 simp)
     also have "\<dots> = mulH (?hterm s) (f (foldr mul (map ?gterm ys') e))"
       using Cons.IH[OF hys'] by (by100 simp)
     also have "?hterm s = f (?gterm s)" using h_eq by (by100 simp)
     also have "mulH (f (?gterm s)) (f (foldr mul (map ?gterm ys') e))
         = f (mul (?gterm s) (foldr mul (map ?gterm ys') e))"
     proof -
       have "f (mul (?gterm s) (foldr mul (map ?gterm ys') e))
           = mulH (f (?gterm s)) (f (foldr mul (map ?gterm ys') e))"
         using hf_hom hgs hprod unfolding top1_group_hom_on_def by (by100 blast)
       thus ?thesis by (by100 simp)
     qed
     also have "mul (?gterm s) (foldr mul (map ?gterm ys') e)
         = foldr mul (map ?gterm (s # ys')) e" by (by100 simp)
     finally show ?case by (by100 simp)
   qed}
  moreover have hxs_S: "\<forall>i<length ?xs. ?xs!i \<in> S"
  proof (intro allI impI)
    fix i assume hi: "i < length ?xs"
    have "\<exists>xs. set xs = {s \<in> S. c s \<noteq> 0} \<and> distinct xs"
      using finite_distinct_list[OF hfin] by (by100 blast)
    hence "set ?xs = {s \<in> S. c s \<noteq> 0} \<and> distinct ?xs" by (rule someI_ex)
    thus "?xs!i \<in> S" using nth_mem[OF hi] by (by100 blast)
  qed
  ultimately have hH_eq: "foldr mulH (map ?hterm ?xs) eH = f (foldr mul (map ?gterm ?xs) e)"
    by (by100 simp)
  \<comment> \<open>Contradiction via injectivity.\<close>
  show ?thesis
  proof
    assume heq: "foldr mulH (map ?hterm ?xs) eH = eH"
    have "f (foldr mul (map ?gterm ?xs) e) = eH" using heq hH_eq by (by100 simp)
    moreover have "f e = eH" by (rule hom_preserves_id[OF hG_grp hH_grp hf_hom])
    moreover have "inj_on f G" using hf_bij unfolding bij_betw_def by (by100 blast)
    moreover have "foldr mul (map ?gterm ?xs) e \<in> G"
    proof (rule foldr_mul_closed[OF hG_grp])
      show "\<forall>i<length (map ?gterm ?xs). (map ?gterm ?xs)!i \<in> G"
      proof (intro allI impI)
        fix i assume hi: "i < length (map ?gterm ?xs)"
        have hsi: "?xs!i \<in> S" using hxs_S hi by (by100 simp)
        have h\<iota>si: "\<iota> (?xs!i) \<in> G" using h\<iota>_in hsi by (by100 blast)
        have hinvsi: "invg (\<iota> (?xs!i)) \<in> G" using hG_grp h\<iota>si unfolding top1_is_group_on_def by (by100 blast)
        show "(map ?gterm ?xs)!i \<in> G" using hi
          group_pow_in_group[OF hG_grp h\<iota>si] group_pow_in_group[OF hG_grp hinvsi] by (by100 auto)
      qed
    qed
    moreover have "e \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
    ultimately have "foldr mul (map ?gterm ?xs) e = e"
    proof -
      assume h1: "f (foldr mul (map ?gterm ?xs) e) = eH"
         and h2: "f e = eH" and h3: "inj_on f G"
         and h4: "foldr mul (map ?gterm ?xs) e \<in> G" and h5: "e \<in> G"
      have "f (foldr mul (map ?gterm ?xs) e) = f e" using h1 h2 by (by100 simp)
      thus ?thesis using h3 h4 h5 unfolding inj_on_def by (by100 blast)
    qed
    thus False using hG_indep[OF hfin hex] by (by100 blast)
  qed
qed

text \<open>Free abelian groups are preserved under group isomorphism.\<close>
lemma free_abelian_invariant_under_iso:
  assumes "top1_is_free_abelian_group_full_on G mul e invg \<iota> S"
      and "top1_group_iso_on G mul H mulH f"
      and "top1_is_abelian_group_on H mulH eH invgH"
  shows "\<exists>\<iota>'. top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>' S"
proof -
  define \<iota>' where "\<iota>' s = f (\<iota> s)" for s
  have hG_grp: "top1_is_group_on G mul e invg"
    using assms(1) unfolding top1_is_free_abelian_group_full_on_def
      top1_is_abelian_group_on_def by (by100 blast)
  have hH_grp: "top1_is_group_on H mulH eH invgH"
    using assms(3) unfolding top1_is_abelian_group_on_def by (by100 blast)
  have h\<iota>_in: "\<forall>s\<in>S. \<iota> s \<in> G"
    using assms(1) unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  have h\<iota>_inj: "inj_on \<iota> S"
    using assms(1) unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  have hf_hom: "top1_group_hom_on G mul H mulH f"
    using assms(2) unfolding top1_group_iso_on_def by (by100 blast)
  have hf_bij: "bij_betw f G H"
    using assms(2) unfolding top1_group_iso_on_def by (by100 blast)
  \<comment> \<open>Part 1: \<iota>' maps S into H.\<close>
  have h1: "\<forall>s\<in>S. \<iota>' s \<in> H"
    unfolding \<iota>'_def using h\<iota>_in hf_bij unfolding bij_betw_def by (by100 blast)
  \<comment> \<open>Part 2: \<iota>' is injective.\<close>
  have h2: "inj_on \<iota>' S"
    unfolding \<iota>'_def
  proof (rule inj_onI)
    fix x y assume hx: "x \<in> S" and hy: "y \<in> S" and hfeq: "f (\<iota> x) = f (\<iota> y)"
    have "inj_on f G" using hf_bij unfolding bij_betw_def by (by100 blast)
    hence "\<iota> x = \<iota> y" using hfeq h\<iota>_in hx hy unfolding inj_on_def by (by100 blast)
    thus "x = y" using h\<iota>_inj hx hy unfolding inj_on_def by (by100 blast)
  qed
  \<comment> \<open>Part 3: \<iota>'(S) generates H.\<close>
  have h3: "H = top1_subgroup_generated_on H mulH eH invgH (\<iota>' ` S)"
  proof -
    have "\<iota>' ` S = f ` (\<iota> ` S)" unfolding \<iota>'_def image_image by (by100 blast)
    moreover have "f ` G = H" using hf_bij unfolding bij_betw_def by (by100 blast)
    moreover have "\<iota> ` S \<subseteq> G" using h\<iota>_in by (by100 blast)
    moreover have "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
      using assms(1) unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
    ultimately show ?thesis
      by (metis surj_hom_generated[OF hG_grp hH_grp hf_hom _ _ _])
  qed
  \<comment> \<open>Part 4: Independence via free\_abelian\_independence\_transfer.\<close>
  have "top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>' S"
    unfolding top1_is_free_abelian_group_full_on_def \<iota>'_def
  proof (intro conjI)
    show "top1_is_abelian_group_on H mulH eH invgH" by (rule assms(3))
    show "\<forall>s\<in>S. f (\<iota> s) \<in> H" using h1 unfolding \<iota>'_def by (by100 blast)
    show "inj_on (\<lambda>s. f (\<iota> s)) S" using h2 unfolding \<iota>'_def by (by100 blast)
    show "H = top1_subgroup_generated_on H mulH eH invgH ((\<lambda>s. f (\<iota> s)) ` S)"
      using h3 unfolding \<iota>'_def by (by100 blast)
  next
    show "\<forall>c. finite {s \<in> S. c s \<noteq> 0} \<longrightarrow> (\<exists>s\<in>S. c s \<noteq> 0) \<longrightarrow>
        foldr mulH (map (\<lambda>s. if 0 \<le> c s then top1_group_pow mulH eH (f (\<iota> s)) (nat (c s))
            else top1_group_pow mulH eH (invgH (f (\<iota> s))) (nat (- c s)))
          (SOME xs. set xs = {s \<in> S. c s \<noteq> 0} \<and> distinct xs)) eH \<noteq> eH"
      using free_abelian_independence_transfer[OF hG_grp hH_grp hf_hom hf_bij h\<iota>_in]
        assms(1) unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  qed
  thus ?thesis by (by100 blast)
qed

text \<open>Concrete corollary: the quotient G/[G,G] is free abelian on S
  (extracts the concrete quotient from Theorem 69.4 by re-using the same proof).\<close>
lemma Theorem_69_4_concrete_free_abelian:
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
  shows "\<exists>\<iota>H. top1_is_free_abelian_group_full_on
      (top1_quotient_group_carrier_on G mul (top1_commutator_subgroup_on G mul e invg))
      (top1_quotient_group_mul_on mul)
      (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) e)
      (\<lambda>C. top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg)
         (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul
            (top1_commutator_subgroup_on G mul e invg) g)))
      \<iota>H S"
proof -
  \<comment> \<open>The abelianization property holds for the concrete quotient.\<close>
  have hG: "top1_is_group_on G mul e invg"
    using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
  let ?N = "top1_commutator_subgroup_on G mul e invg"
  let ?H = "top1_quotient_group_carrier_on G mul ?N"
  let ?mulH = "top1_quotient_group_mul_on mul"
  let ?eH = "top1_group_coset_on G mul ?N e"
  let ?invgH = "\<lambda>C. top1_group_coset_on G mul ?N (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul ?N g))"
  let ?\<phi> = "\<lambda>g. top1_group_coset_on G mul ?N g"
  let ?\<iota>H = "\<lambda>s. ?\<phi> (\<iota> s)"
  have h_abel: "top1_is_abelianization_of ?H ?mulH ?eH ?invgH G mul e invg ?\<phi>"
    by (rule abelianization_concrete[OF hG])
  \<comment> \<open>The proof of Theorem\_69\_4 returns exactly ?H, ?mulH, etc. as witnesses.
     We need: free\_abelian\_full\_on ?H ?mulH ?eH ?invgH ?\<iota>H S.
     Since this IS what Theorem\_69\_4's proof establishes (h\_free\_abel fact),
     we re-derive the key parts inline.\<close>
  \<comment> \<open>Step 1: ?\<iota>H maps S into ?H.\<close>
  have h\<iota>H_in: "\<forall>s\<in>S. ?\<iota>H s \<in> ?H"
  proof (intro ballI)
    fix s assume hs: "s \<in> S"
    have "\<iota> s \<in> G" using assms hs unfolding top1_is_free_group_full_on_def by (by100 blast)
    hence "?\<phi> (\<iota> s) \<in> ?\<phi> ` G" by (by100 blast)
    also have "?\<phi> ` G = ?H" using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
    finally show "?\<iota>H s \<in> ?H" by (by100 simp)
  qed
  \<comment> \<open>Step 2: ?\<iota>H is injective on S.\<close>
  have h\<iota>H_inj: "inj_on ?\<iota>H S"
    by (rule abelianization_injective_on_generators[OF assms])
  \<comment> \<open>Step 3: ?\<iota>H(S) generates ?H.\<close>
  have hH_gen: "?H = top1_subgroup_generated_on ?H ?mulH ?eH ?invgH (?\<iota>H ` S)"
  proof -
    have hH_grp: "top1_is_group_on ?H ?mulH ?eH ?invgH"
      using h_abel unfolding top1_is_abelianization_of_def top1_is_abelian_group_on_def
      by (by100 blast)
    have hphi_hom: "top1_group_hom_on G mul ?H ?mulH ?\<phi>"
      using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
    have hphi_surj: "?\<phi> ` G = ?H"
      using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
    have hG_gen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
      using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
    have h\<iota>S_sub: "\<iota> ` S \<subseteq> G"
      using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
    have "?\<iota>H ` S = ?\<phi> ` (\<iota> ` S)" by (by100 force)
    thus ?thesis
      by (metis surj_hom_generated[OF hG hH_grp hphi_hom hphi_surj h\<iota>S_sub hG_gen])
  qed
  \<comment> \<open>Step 4: Independence (no nontrivial integer combination = ?eH).\<close>
  have hH_indep: "\<And>c. finite {s\<in>S. c s \<noteq> 0} \<Longrightarrow> (\<exists>s\<in>S. c s \<noteq> 0) \<Longrightarrow>
      foldr ?mulH (map (\<lambda>s.
          if c s \<ge> 0 then top1_group_pow ?mulH ?eH (?\<iota>H s) (nat (c s))
          else top1_group_pow ?mulH ?eH (?invgH (?\<iota>H s)) (nat (- c s)))
        (SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs)) ?eH \<noteq> ?eH"
    by (rule abelianization_independence_on_generators[OF assms])
  \<comment> \<open>Step 5: ?H is abelian.\<close>
  have hH_abel: "top1_is_abelian_group_on ?H ?mulH ?eH ?invgH"
    using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
  show ?thesis
    apply (rule exI[of _ ?\<iota>H])
    unfolding top1_is_free_abelian_group_full_on_def
    using hH_abel h\<iota>H_in h\<iota>H_inj hH_gen hH_indep by (by100 blast)
qed


lemma abelianization_of_presented_group:
  fixes F :: "'g set" and mulF :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and eF :: 'g and invgF :: "'g \<Rightarrow> 'g"
    and \<iota> :: "'s \<Rightarrow> 'g" and S :: "'s set"
    and G :: "'h set" and mulG :: "'h \<Rightarrow> 'h \<Rightarrow> 'h"
    and eG :: 'h and invgG :: "'h \<Rightarrow> 'h"
    and \<pi> :: "'g \<Rightarrow> 'h"
  assumes hF_free: "top1_is_free_group_full_on F mulF eF invgF \<iota> S"
      and hG_grp: "top1_is_group_on G mulG eG invgG"
      and hpi_hom: "top1_group_hom_on F mulF G mulG \<pi>"
      and hpi_surj: "\<pi> ` F = G"
      and hker_sub_comm: "top1_group_kernel_on F eG \<pi> \<subseteq>
          top1_commutator_subgroup_on F mulF eF invgF"
  shows "\<exists>(H :: 'h set set) mulH eH invgH \<phi> \<iota>H.
      top1_is_abelianization_of H mulH eH invgH G mulG eG invgG \<phi>
    \<and> top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>H S"
proof -
  \<comment> \<open>Step 1: Get the concrete abelianization of F.\<close>
  have hF_grp: "top1_is_group_on F mulF eF invgF"
    using hF_free unfolding top1_is_free_group_full_on_def by (by100 blast)
  let ?NF = "top1_commutator_subgroup_on F mulF eF invgF"
  \<comment> \<open>Step 2: Compose \<pi> with projection G \<rightarrow> G/[G,G].\<close>
  let ?NG = "top1_commutator_subgroup_on G mulG eG invgG"
  let ?HG = "top1_quotient_group_carrier_on G mulG ?NG"
  let ?mulHG = "top1_quotient_group_mul_on mulG"
  let ?eHG = "top1_group_coset_on G mulG ?NG eG"
  let ?\<phi>G = "\<lambda>g. top1_group_coset_on G mulG ?NG g"
  have habel_G: "top1_is_abelianization_of ?HG ?mulHG ?eHG
      (\<lambda>C. top1_group_coset_on G mulG ?NG (invgG (SOME g. g \<in> G \<and> C = ?\<phi>G g)))
      G mulG eG invgG ?\<phi>G"
    by (rule abelianization_concrete[OF hG_grp])
  \<comment> \<open>Step 3: The composition j = \<phi>G \<circ> \<pi>: F \<rightarrow> G/[G,G] is surjective with kernel [F,F].
     Surjective: \<pi> surjective + \<phi>G surjective.
     Kernel = {f \<in> F | \<phi>G(\<pi>(f)) = ?eHG} = {f \<in> F | \<pi>(f) \<in> [G,G]}
     = \<pi>\<inverse>([G,G]). Since \<pi> maps [F,F] to [G,G] and ker(\<pi>) \<subseteq> [F,F]:
     \<pi>\<inverse>([G,G]) = [F,F] \<cdot> ker(\<pi>) = [F,F] (since ker(\<pi>) \<subseteq> [F,F]).\<close>
  \<comment> \<open>Step 4: By first iso theorem: F/[F,F] \<cong> G/[G,G].\<close>
  \<comment> \<open>Step 5: By Theorem 69.4: F/[F,F] is free abelian on S.\<close>
  \<comment> \<open>Step 5-6: F/[F,F] is free abelian (Theorem 69.4).
     F/[F,F] \<cong> G/[G,G] via first iso theorem on j = \<phi>G\<circ>\<pi>.
     Transfer the free abelian structure from F/[F,F] to G/[G,G].\<close>
  \<comment> \<open>F/[F,F] is free abelian on S by Theorem 69.4.\<close>
  have hfab: "\<exists>(HF :: 'g set set) mulHF eHF invgHF \<phi>F \<iota>HF.
      top1_is_abelianization_of HF mulHF eHF invgHF F mulF eF invgF \<phi>F
    \<and> top1_is_free_abelian_group_full_on HF mulHF eHF invgHF \<iota>HF S"
    using Theorem_69_4[OF hF_free] by (by100 blast)
  \<comment> \<open>Transfer: F/[F,F] \<cong> G/[G,G] via first iso theorem on j = \<phi>G\<circ>\<pi>.
     The kernel of the composed map j: F \<rightarrow> G/[G,G] is:
     ker(j) = {f \<in> F | \<phi>G(\<pi>(f)) = eHG} = {f \<in> F | \<pi>(f) \<in> [G,G]}
     Since \<pi> maps [F,F] onto [G,G] and ker(\<pi>) \<subseteq> [F,F]:
     ker(j) = [F,F] \<cdot> ker(\<pi>) = [F,F].
     By first iso theorem: F/ker(j) = F/[F,F] \<cong> im(j) = G/[G,G].
     The free abelian structure transfers.\<close>
  \<comment> \<open>Compute ker(j) where j = \<phi>G \<circ> \<pi>.\<close>
  \<comment> \<open>Step A: \<pi>([F,F]) = [G,G] (surjective hom maps commutator subgroup onto commutator subgroup).\<close>
  have hpi_comm: "\<pi> ` ?NF \<supseteq> ?NG"
  proof -
    \<comment> \<open>Every commutator in G lifts to a commutator in F (via surjectivity of \<pi>).\<close>
    have hcomms_in_image: "{top1_group_commutator_on mulG invgG g h |g h. g \<in> G \<and> h \<in> G}
        \<subseteq> \<pi> ` ?NF"
    proof (rule subsetI, clarify)
      fix g h assume hg: "g \<in> G" and hh: "h \<in> G"
      obtain a where ha: "a \<in> F" "\<pi> a = g" using hpi_surj hg by (by100 blast)
      obtain b where hb: "b \<in> F" "\<pi> b = h" using hpi_surj hh by (by100 blast)
      \<comment> \<open>[a,b] \<in> [F,F]: commutator is a generator of commutator subgroup.\<close>
      have hcomms_sub_F: "{top1_group_commutator_on mulF invgF x y |x y. x \<in> F \<and> y \<in> F} \<subseteq> F"
      proof (rule subsetI, clarify)
        fix x y assume "x \<in> F" "y \<in> F"
        have hinvx: "invgF x \<in> F" using hF_grp \<open>x \<in> F\<close> unfolding top1_is_group_on_def by (by100 blast)
        have hinvy: "invgF y \<in> F" using hF_grp \<open>y \<in> F\<close> unfolding top1_is_group_on_def by (by100 blast)
        show "top1_group_commutator_on mulF invgF x y \<in> F"
          unfolding top1_group_commutator_on_def
          using hF_grp \<open>x \<in> F\<close> \<open>y \<in> F\<close> hinvx hinvy unfolding top1_is_group_on_def by (by100 blast)
      qed
      have "top1_group_commutator_on mulF invgF a b
          \<in> {top1_group_commutator_on mulF invgF x y |x y. x \<in> F \<and> y \<in> F}"
        using ha(1) hb(1) by (by100 blast)
      hence hab_NF: "top1_group_commutator_on mulF invgF a b \<in> ?NF"
        unfolding top1_commutator_subgroup_on_def
        by (rule subgroup_generated_contains[OF hF_grp hcomms_sub_F])
      \<comment> \<open>\<pi>([a,b]) = [\<pi>(a),\<pi>(b)] = [g,h]: hom preserves commutator.\<close>
      have hinva: "invgF a \<in> F" using hF_grp ha(1) unfolding top1_is_group_on_def by (by100 blast)
      have hinvb: "invgF b \<in> F" using hF_grp hb(1) unfolding top1_is_group_on_def by (by100 blast)
      have hab_F: "mulF a b \<in> F" using hF_grp ha(1) hb(1) unfolding top1_is_group_on_def by (by100 blast)
      have habinva: "mulF (mulF a b) (invgF a) \<in> F"
        using hF_grp hab_F hinva unfolding top1_is_group_on_def by (by100 blast)
      have "\<pi> (top1_group_commutator_on mulF invgF a b)
          = top1_group_commutator_on mulG invgG g h"
        unfolding top1_group_commutator_on_def
        using hpi_hom ha hb hinva hinvb hab_F habinva
        unfolding top1_group_hom_on_def
        using hom_preserves_inv[OF hF_grp hG_grp hpi_hom ha(1)]
              hom_preserves_inv[OF hF_grp hG_grp hpi_hom hb(1)]
        by (by100 simp)
      thus "top1_group_commutator_on mulG invgG g h \<in> \<pi> ` ?NF"
        using hab_NF by (by100 force)
    qed
    \<comment> \<open>[G,G] = ⟨commutators⟩ \<subseteq> \<pi>([F,F]) since \<pi>([F,F]) is a subgroup containing commutators.\<close>
    have himage_sub: "\<pi> ` ?NF \<subseteq> G"
    proof (rule image_subsetI)
      fix x assume "x \<in> ?NF"
      hence "x \<in> F" using commutator_subgroup_is_normal[OF hF_grp]
        unfolding top1_normal_subgroup_on_def by (by100 blast)
      thus "\<pi> x \<in> G" using hpi_hom unfolding top1_group_hom_on_def by (by100 blast)
    qed
    have himage_grp: "top1_is_group_on (\<pi> ` ?NF) mulG eG invgG"
    proof -
      have hNF_grp: "top1_is_group_on ?NF mulF eF invgF"
        using commutator_subgroup_is_normal[OF hF_grp] unfolding top1_normal_subgroup_on_def
        by (by100 blast)
      have hNF_sub: "?NF \<subseteq> F" using hNF_grp commutator_subgroup_is_normal[OF hF_grp]
        unfolding top1_normal_subgroup_on_def by (by100 blast)
      \<comment> \<open>Identity: eG = \<pi>(eF) \<in> \<pi>([F,F]).\<close>
      have heF_NF: "eF \<in> ?NF" using hNF_grp unfolding top1_is_group_on_def by (by100 blast)
      have heG_im: "eG \<in> \<pi> ` ?NF"
      proof -
        have "\<pi> eF = eG" by (rule hom_preserves_id[OF hF_grp hG_grp hpi_hom])
        thus ?thesis using heF_NF by (by100 force)
      qed
      \<comment> \<open>Closure: \<pi>(x) \<cdot> \<pi>(y) = \<pi>(x\<cdot>y) \<in> \<pi>([F,F]).\<close>
      have hclos: "\<forall>x\<in>\<pi> ` ?NF. \<forall>y\<in>\<pi> ` ?NF. mulG x y \<in> \<pi> ` ?NF"
      proof (intro ballI)
        fix px py assume "px \<in> \<pi> ` ?NF" "py \<in> \<pi> ` ?NF"
        then obtain x y where hx: "x \<in> ?NF" "px = \<pi> x" and hy: "y \<in> ?NF" "py = \<pi> y"
          by (by100 blast)
        have "\<pi> (mulF x y) = mulG (\<pi> x) (\<pi> y)"
          using hpi_hom hx(1) hy(1) hNF_sub unfolding top1_group_hom_on_def by (by100 blast)
        hence "mulG px py = \<pi> (mulF x y)" using hx(2) hy(2) by (by100 simp)
        moreover have "mulF x y \<in> ?NF"
          using hNF_grp hx(1) hy(1) unfolding top1_is_group_on_def by (by100 blast)
        ultimately show "mulG px py \<in> \<pi> ` ?NF" by (by100 force)
      qed
      \<comment> \<open>Inverse: invgG(\<pi>(x)) = \<pi>(invgF(x)) \<in> \<pi>([F,F]).\<close>
      have hinv: "\<forall>x\<in>\<pi> ` ?NF. invgG x \<in> \<pi> ` ?NF"
      proof (intro ballI)
        fix px assume "px \<in> \<pi> ` ?NF"
        then obtain x where hx: "x \<in> ?NF" "px = \<pi> x" by (by100 blast)
        have hxF: "x \<in> F" using hx(1) hNF_sub by (by100 blast)
        have "invgG px = \<pi> (invgF x)"
          using hx(2) hom_preserves_inv[OF hF_grp hG_grp hpi_hom hxF] by (by100 simp)
        moreover have "invgF x \<in> ?NF"
          using hNF_grp hx(1) unfolding top1_is_group_on_def by (by100 blast)
        ultimately show "invgG px \<in> \<pi> ` ?NF" by (by100 force)
      qed
      \<comment> \<open>Group axioms (associativity, identity, inverse) from G restricted to image.\<close>
      have hassoc: "\<forall>x\<in>\<pi>`?NF. \<forall>y\<in>\<pi>`?NF. \<forall>z\<in>\<pi>`?NF.
          mulG (mulG x y) z = mulG x (mulG y z)"
        using hG_grp himage_sub unfolding top1_is_group_on_def by (by100 blast)
      have hid: "\<forall>x\<in>\<pi>`?NF. mulG eG x = x \<and> mulG x eG = x"
        using hG_grp himage_sub unfolding top1_is_group_on_def by (by100 blast)
      have hinvax: "\<forall>x\<in>\<pi>`?NF. mulG (invgG x) x = eG \<and> mulG x (invgG x) = eG"
        using hG_grp himage_sub unfolding top1_is_group_on_def by (by100 blast)
      show ?thesis unfolding top1_is_group_on_def
        using heG_im hclos hinv hassoc hid hinvax by (by100 blast)
    qed
    have "top1_subgroup_generated_on G mulG eG invgG
        {top1_group_commutator_on mulG invgG g h |g h. g \<in> G \<and> h \<in> G}
      \<subseteq> \<pi> ` ?NF"
      by (rule subgroup_generated_minimal[OF hcomms_in_image himage_sub himage_grp])
    thus ?thesis unfolding top1_commutator_subgroup_on_def by (by100 blast)
  qed
  have hpi_comm2: "\<pi> ` ?NF \<subseteq> ?NG"
  proof -
    \<comment> \<open>G/[G,G] is abelian, so [G,G] \<subseteq> ker of the projection G \<rightarrow> G/[G,G].
       Equivalently, [F,F] maps into ker of F \<rightarrow> G \<rightarrow> G/[G,G] which contains [G,G].\<close>
    \<comment> \<open>More directly: the image of [F,F] under any hom to any group lands in [G,G]
       because hom preserves commutators.\<close>
    have hNG_normal: "top1_normal_subgroup_on G mulG eG invgG ?NG"
      by (rule commutator_subgroup_is_normal[OF hG_grp])
    have hNG_sub: "?NG \<subseteq> G" using hNG_normal unfolding top1_normal_subgroup_on_def by (by100 blast)
    have hHG_abel: "top1_is_abelian_group_on ?HG ?mulHG ?eHG
        (\<lambda>C. top1_group_coset_on G mulG ?NG (invgG (SOME g. g \<in> G \<and> C = ?\<phi>G g)))"
      using habel_G unfolding top1_is_abelianization_of_def by (by100 blast)
    have hphiG_hom: "top1_group_hom_on G mulG ?HG ?mulHG ?\<phi>G"
      using habel_G unfolding top1_is_abelianization_of_def by (by100 blast)
    \<comment> \<open>\<phi>G \<circ> \<pi> maps [F,F] into ker(\<phi>G) = [G,G] because G/[G,G] is abelian.\<close>
    have hj_hom: "top1_group_hom_on F mulF ?HG ?mulHG (\<lambda>f. ?\<phi>G (\<pi> f))"
    proof -
      show ?thesis unfolding top1_group_hom_on_def
      proof (intro conjI ballI)
        fix f assume hf: "f \<in> F"
        have "\<pi> f \<in> G" using hpi_hom hf unfolding top1_group_hom_on_def by (by100 blast)
        thus "?\<phi>G (\<pi> f) \<in> ?HG" using hphiG_hom unfolding top1_group_hom_on_def by (by100 blast)
      next
        fix f1 f2 assume hf1: "f1 \<in> F" and hf2: "f2 \<in> F"
        have h1: "\<pi> f1 \<in> G" using hpi_hom hf1 unfolding top1_group_hom_on_def by (by100 blast)
        have h2: "\<pi> f2 \<in> G" using hpi_hom hf2 unfolding top1_group_hom_on_def by (by100 blast)
        have "\<pi> (mulF f1 f2) = mulG (\<pi> f1) (\<pi> f2)"
          using hpi_hom hf1 hf2 unfolding top1_group_hom_on_def by (by100 blast)
        hence "?\<phi>G (\<pi> (mulF f1 f2)) = ?\<phi>G (mulG (\<pi> f1) (\<pi> f2))"
          by (by100 simp)
        also have "\<dots> = ?mulHG (?\<phi>G (\<pi> f1)) (?\<phi>G (\<pi> f2))"
          using hphiG_hom h1 h2 unfolding top1_group_hom_on_def by (by100 blast)
        finally show "?\<phi>G (\<pi> (mulF f1 f2)) = ?mulHG (?\<phi>G (\<pi> f1)) (?\<phi>G (\<pi> f2))" .
      qed
    qed
    have "?NF \<subseteq> top1_group_kernel_on F ?eHG (\<lambda>f. ?\<phi>G (\<pi> f))"
      by (rule Lemma_69_3_commutator_in_kernel[OF hF_grp hHG_abel hj_hom])
    hence "\<forall>f\<in>?NF. ?\<phi>G (\<pi> f) = ?eHG"
      unfolding top1_group_kernel_on_def by (by100 blast)
    hence "\<forall>f\<in>?NF. \<pi> f \<in> ?NG"
    proof (intro ballI)
      fix f assume hf: "f \<in> ?NF" and hall: "\<forall>f\<in>?NF. ?\<phi>G (\<pi> f) = ?eHG"
      have hfF: "f \<in> F" using hf commutator_subgroup_is_normal[OF hF_grp]
        unfolding top1_normal_subgroup_on_def by (by100 blast)
      have hpif: "\<pi> f \<in> G" using hpi_hom hfF unfolding top1_group_hom_on_def by (by100 blast)
      have "?\<phi>G (\<pi> f) = ?eHG" using hall hf by (by100 blast)
      have "top1_group_kernel_on G ?eHG ?\<phi>G = ?NG"
        using habel_G unfolding top1_is_abelianization_of_def by (by100 blast)
      thus "\<pi> f \<in> ?NG" using \<open>?\<phi>G (\<pi> f) = ?eHG\<close> hpif
        unfolding top1_group_kernel_on_def by (by100 blast)
    qed
    thus ?thesis by (by100 blast)
  qed
  \<comment> \<open>Step B: ker(j) = [F,F].\<close>
  let ?j = "\<lambda>f. ?\<phi>G (\<pi> f)"
  have hker_j: "top1_group_kernel_on F ?eHG ?j = ?NF"
  proof (rule set_eqI, rule iffI)
    \<comment> \<open>\<supseteq>: f \<in> [F,F] \<Longrightarrow> \<pi>(f) \<in> [G,G] \<Longrightarrow> \<phi>G(\<pi>(f)) = eHG.\<close>
    fix f assume "f \<in> ?NF"
    hence "\<pi> f \<in> ?NG" using hpi_comm2 by (by100 blast)
    hence "?\<phi>G (\<pi> f) = ?eHG"
      using habel_G unfolding top1_is_abelianization_of_def top1_group_kernel_on_def
      by (by100 blast)
    moreover have "f \<in> F"
    proof -
      have "?NF \<subseteq> F" using commutator_subgroup_is_normal[OF hF_grp]
        unfolding top1_normal_subgroup_on_def by (by100 blast)
      thus ?thesis using \<open>f \<in> ?NF\<close> by (by100 blast)
    qed
    ultimately show "f \<in> top1_group_kernel_on F ?eHG ?j"
      unfolding top1_group_kernel_on_def by (by100 blast)
  next
    \<comment> \<open>\<subseteq>: f \<in> ker(j) \<Longrightarrow> \<pi>(f) \<in> [G,G] = \<pi>([F,F]).
       Pick c \<in> [F,F] with \<pi>(c) = \<pi>(f). Then f\<cdot>c\<inverse> \<in> ker(\<pi>) \<subseteq> [F,F].
       Hence f = (f\<cdot>c\<inverse>)\<cdot>c \<in> [F,F]\<cdot>[F,F] = [F,F].\<close>
    fix f assume hf: "f \<in> top1_group_kernel_on F ?eHG ?j"
    hence hfF: "f \<in> F" and hfker: "?\<phi>G (\<pi> f) = ?eHG"
      unfolding top1_group_kernel_on_def by (by100 blast)+
    \<comment> \<open>\<pi>(f) \<in> [G,G] (from \<phi>G(\<pi>(f)) = eHG and ker(\<phi>G) = [G,G]).\<close>
    have hpif_NG: "\<pi> f \<in> ?NG"
    proof -
      have "top1_group_kernel_on G ?eHG ?\<phi>G = ?NG"
        using habel_G unfolding top1_is_abelianization_of_def by (by100 blast)
      moreover have "\<pi> f \<in> G" using hpi_hom hfF unfolding top1_group_hom_on_def by (by100 blast)
      ultimately show ?thesis using hfker unfolding top1_group_kernel_on_def by (by100 blast)
    qed
    \<comment> \<open>Pick c \<in> [F,F] with \<pi>(c) = \<pi>(f).\<close>
    have "\<pi> f \<in> \<pi> ` ?NF" using hpif_NG hpi_comm by (by100 blast)
    then obtain c where hc: "c \<in> ?NF" "\<pi> c = \<pi> f" by (by100 auto)
    \<comment> \<open>f\<cdot>c\<inverse> \<in> ker(\<pi>).\<close>
    have hcF: "c \<in> F" using hc(1) commutator_subgroup_is_normal[OF hF_grp]
      unfolding top1_normal_subgroup_on_def by (by100 blast)
    have hinvc: "invgF c \<in> F" using hF_grp hcF unfolding top1_is_group_on_def by (by100 blast)
    have hfc: "mulF f (invgF c) \<in> F" using hF_grp hfF hinvc
      unfolding top1_is_group_on_def by (by100 blast)
    have "\<pi> (mulF f (invgF c)) = mulG (\<pi> f) (invgG (\<pi> c))"
    proof -
      have "\<pi> (mulF f (invgF c)) = mulG (\<pi> f) (\<pi> (invgF c))"
        using hpi_hom hfF hinvc unfolding top1_group_hom_on_def by (by100 blast)
      moreover have "\<pi> (invgF c) = invgG (\<pi> c)"
        by (rule hom_preserves_inv[OF hF_grp hG_grp hpi_hom hcF])
      ultimately show ?thesis by (by100 simp)
    qed
    also have "mulG (\<pi> f) (invgG (\<pi> c)) = mulG (\<pi> f) (invgG (\<pi> f))"
      using hc(2) by (by100 simp)
    also have "\<dots> = eG" using hG_grp hpi_hom hfF
      unfolding top1_group_hom_on_def top1_is_group_on_def by (by100 blast)
    finally have "mulF f (invgF c) \<in> top1_group_kernel_on F eG \<pi>"
      unfolding top1_group_kernel_on_def using hfc by (by100 blast)
    hence "mulF f (invgF c) \<in> ?NF" using hker_sub_comm by (by100 blast)
    \<comment> \<open>f = (f\<cdot>c\<inverse>)\<cdot>c \<in> [F,F].\<close>
    have "f = mulF (mulF f (invgF c)) c"
    proof -
      have "mulF (mulF f (invgF c)) c = mulF f (mulF (invgF c) c)"
        using hF_grp hfF hinvc hcF unfolding top1_is_group_on_def by (by100 blast)
      also have "mulF (invgF c) c = eF"
        using hF_grp hcF unfolding top1_is_group_on_def by (by100 blast)
      also have "mulF f eF = f"
        using hF_grp hfF unfolding top1_is_group_on_def by (by100 blast)
      finally show ?thesis by (by100 simp)
    qed
    moreover have "mulF (mulF f (invgF c)) c \<in> ?NF"
    proof -
      have hNF_grp: "top1_is_group_on ?NF mulF eF invgF"
        using commutator_subgroup_is_normal[OF hF_grp]
        unfolding top1_normal_subgroup_on_def by (by100 blast)
      have "\<forall>x\<in>?NF. \<forall>y\<in>?NF. mulF x y \<in> ?NF"
        using hNF_grp unfolding top1_is_group_on_def by (by100 blast)
      thus ?thesis using \<open>mulF f (invgF c) \<in> ?NF\<close> hc(1) by (by100 blast)
    qed
    ultimately show "f \<in> ?NF" by (by100 simp)
  qed
  \<comment> \<open>Step C: Apply first iso theorem: F/[F,F] \<cong> G/[G,G].\<close>
  \<comment> \<open>Then transfer free abelian from F/[F,F] (via Theorem 69.4) to G/[G,G].\<close>
  \<comment> \<open>Step C1: j = \<phi>G \<circ> \<pi> is a surjective hom with kernel [F,F].\<close>
  let ?j = "\<lambda>f. ?\<phi>G (\<pi> f)"
  have hj_hom: "top1_group_hom_on F mulF ?HG ?mulHG ?j"
  proof -
    have hphiG_hom: "top1_group_hom_on G mulG ?HG ?mulHG ?\<phi>G"
      using habel_G unfolding top1_is_abelianization_of_def by (by100 blast)
    show ?thesis unfolding top1_group_hom_on_def
    proof (intro conjI ballI)
      fix f assume hf: "f \<in> F"
      have "\<pi> f \<in> G" using hpi_hom hf unfolding top1_group_hom_on_def by (by100 blast)
      thus "?j f \<in> ?HG" using hphiG_hom unfolding top1_group_hom_on_def by (by100 blast)
    next
      fix f1 f2 assume hf1: "f1 \<in> F" and hf2: "f2 \<in> F"
      have h1: "\<pi> f1 \<in> G" using hpi_hom hf1 unfolding top1_group_hom_on_def by (by100 blast)
      have h2: "\<pi> f2 \<in> G" using hpi_hom hf2 unfolding top1_group_hom_on_def by (by100 blast)
      have "\<pi> (mulF f1 f2) = mulG (\<pi> f1) (\<pi> f2)"
        using hpi_hom hf1 hf2 unfolding top1_group_hom_on_def by (by100 blast)
      hence "?j (mulF f1 f2) = ?\<phi>G (mulG (\<pi> f1) (\<pi> f2))" by (by100 simp)
      also have "\<dots> = ?mulHG (?j f1) (?j f2)"
        using hphiG_hom h1 h2 unfolding top1_group_hom_on_def by (by100 blast)
      finally show "?j (mulF f1 f2) = ?mulHG (?j f1) (?j f2)" .
    qed
  qed
  have hj_surj: "?j ` F = ?HG"
  proof -
    have "?j ` F = ?\<phi>G ` (\<pi> ` F)" by (by100 auto)
    also have "\<pi> ` F = G" by (rule hpi_surj)
    also have "?\<phi>G ` G = ?HG"
      using habel_G unfolding top1_is_abelianization_of_def by (by100 blast)
    finally show ?thesis .
  qed
  have hNF_normal: "top1_normal_subgroup_on F mulF eF invgF ?NF"
    by (rule commutator_subgroup_is_normal[OF hF_grp])
  have hHG_grp: "top1_is_group_on ?HG ?mulHG ?eHG
      (\<lambda>C. top1_group_coset_on G mulG ?NG (invgG (SOME g. g \<in> G \<and> C = ?\<phi>G g)))"
    using habel_G unfolding top1_is_abelianization_of_def top1_is_abelian_group_on_def
    by (by100 blast)
  \<comment> \<open>Step C2: By first iso theorem: G/[G,G] \<cong> F/[F,F].\<close>
  have hiso: "top1_groups_isomorphic_on ?HG ?mulHG
      (top1_quotient_group_carrier_on F mulF ?NF)
      (top1_quotient_group_mul_on mulF)"
    by (rule first_isomorphism_theorem[OF hF_grp hNF_normal hHG_grp hj_hom hj_surj hker_j])
  \<comment> \<open>Step C3: F/[F,F] is free abelian on S (Theorem 69.4).\<close>
  \<comment> \<open>Step C4: Transfer via iso G/[G,G] \<cong> F/[F,F] + free\_abelian\_invariant\_under\_iso.\<close>
  \<comment> \<open>Step C3-C4: F/[F,F] is free abelian on S. Transfer to G/[G,G] via iso.\<close>
  have hfab_F: "\<exists>\<iota>HF. top1_is_free_abelian_group_full_on
      (top1_quotient_group_carrier_on F mulF ?NF) (top1_quotient_group_mul_on mulF)
      (top1_group_coset_on F mulF ?NF eF)
      (\<lambda>C. top1_group_coset_on F mulF ?NF (invgF (SOME g. g \<in> F \<and>
          C = top1_group_coset_on F mulF ?NF g))) \<iota>HF S"
  proof -
    \<comment> \<open>Theorem\_69\_4 gives some (HF :: 'g set set) that's free abelian on S.\<close>
    show ?thesis by (rule Theorem_69_4_concrete_free_abelian[OF hF_free])
  qed
  \<comment> \<open>The iso gives G/[G,G] \<cong> F/[F,F]. Transfer free abelian.\<close>
  from hfab_F obtain \<iota>HF where hfa_F:
    "top1_is_free_abelian_group_full_on
      (top1_quotient_group_carrier_on F mulF ?NF) (top1_quotient_group_mul_on mulF)
      (top1_group_coset_on F mulF ?NF eF)
      (\<lambda>C. top1_group_coset_on F mulF ?NF (invgF (SOME g. g \<in> F \<and>
          C = top1_group_coset_on F mulF ?NF g))) \<iota>HF S"
    by (by100 blast)
  \<comment> \<open>G/[G,G] is abelian.\<close>
  have hHG_abel: "top1_is_abelian_group_on ?HG ?mulHG ?eHG
      (\<lambda>C. top1_group_coset_on G mulG ?NG (invgG (SOME g. g \<in> G \<and> C = ?\<phi>G g)))"
    using habel_G unfolding top1_is_abelianization_of_def by (by100 blast)
  \<comment> \<open>Use isomorphism + free\_abelian\_invariant\_under\_iso.\<close>
  from hiso obtain fiso where hfiso:
    "top1_group_iso_on ?HG ?mulHG
      (top1_quotient_group_carrier_on F mulF ?NF) (top1_quotient_group_mul_on mulF) fiso"
    unfolding top1_groups_isomorphic_on_def by (by100 blast)
  \<comment> \<open>The inverse iso transfers free abelian from F/[F,F] to G/[G,G].\<close>
  \<comment> \<open>Reverse iso: F/[F,F] \<cong> G/[G,G].\<close>
  have hHG_grp2: "top1_is_group_on ?HG ?mulHG ?eHG
      (\<lambda>C. top1_group_coset_on G mulG ?NG (invgG (SOME g. g \<in> G \<and> C = ?\<phi>G g)))"
    using hHG_abel unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hFN_grp: "top1_is_group_on (top1_quotient_group_carrier_on F mulF ?NF)
      (top1_quotient_group_mul_on mulF)
      (top1_group_coset_on F mulF ?NF eF)
      (\<lambda>C. top1_group_coset_on F mulF ?NF (invgF (SOME g. g \<in> F \<and>
          C = top1_group_coset_on F mulF ?NF g)))"
    by (rule quotient_group_is_group[OF hF_grp hNF_normal])
  have hrev_iso: "top1_groups_isomorphic_on
      (top1_quotient_group_carrier_on F mulF ?NF) (top1_quotient_group_mul_on mulF)
      ?HG ?mulHG"
    by (rule top1_groups_isomorphic_on_sym[OF hiso hHG_grp2 hFN_grp])
  \<comment> \<open>Transfer free abelian from F/[F,F] to G/[G,G] via reverse iso.\<close>
  have hFN_abel: "top1_is_abelian_group_on (top1_quotient_group_carrier_on F mulF ?NF)
      (top1_quotient_group_mul_on mulF)
      (top1_group_coset_on F mulF ?NF eF)
      (\<lambda>C. top1_group_coset_on F mulF ?NF (invgF (SOME g. g \<in> F \<and>
          C = top1_group_coset_on F mulF ?NF g)))"
  proof -
    have h_ab_F: "top1_is_abelianization_of
        (top1_quotient_group_carrier_on F mulF ?NF) (top1_quotient_group_mul_on mulF)
        (top1_group_coset_on F mulF ?NF eF)
        (\<lambda>C. top1_group_coset_on F mulF ?NF (invgF (SOME g. g \<in> F \<and>
            C = top1_group_coset_on F mulF ?NF g)))
        F mulF eF invgF (\<lambda>g. top1_group_coset_on F mulF ?NF g)"
      by (rule abelianization_concrete[OF hF_grp])
    thus ?thesis unfolding top1_is_abelianization_of_def by (by100 blast)
  qed
  from hrev_iso obtain f_rev where hf_rev:
    "top1_group_iso_on (top1_quotient_group_carrier_on F mulF ?NF)
      (top1_quotient_group_mul_on mulF) ?HG ?mulHG f_rev"
    unfolding top1_groups_isomorphic_on_def by (by100 blast)
  have "\<exists>\<iota>'. top1_is_free_abelian_group_full_on ?HG ?mulHG ?eHG
      (\<lambda>C. top1_group_coset_on G mulG ?NG (invgG (SOME g. g \<in> G \<and> C = ?\<phi>G g))) \<iota>' S"
    by (rule free_abelian_invariant_under_iso[OF hfa_F hf_rev hHG_abel])
  then obtain \<iota>H where hfa_G: "top1_is_free_abelian_group_full_on ?HG ?mulHG ?eHG
      (\<lambda>C. top1_group_coset_on G mulG ?NG (invgG (SOME g. g \<in> G \<and> C = ?\<phi>G g))) \<iota>H S"
    by (by100 blast)
  show ?thesis
    apply (rule exI[of _ ?HG], rule exI[of _ ?mulHG], rule exI[of _ ?eHG])
    apply (rule exI[of _ "\<lambda>C. top1_group_coset_on G mulG ?NG (invgG (SOME g. g \<in> G \<and> C = ?\<phi>G g))"])
    apply (rule exI[of _ ?\<phi>G], rule exI[of _ \<iota>H])
    using habel_G hfa_G by (by100 blast)
qed


text \<open>Rank of a finitely generated free group is invariant.\<close>
lemma free_group_rank_invariant_finite:
  assumes "top1_is_free_group_full_on G mul e invg \<iota>1 S1"
      and "top1_is_free_group_full_on G mul e invg \<iota>2 S2"
      and "finite S1" and "finite S2"
  shows "card S1 = card S2"
proof -
  \<comment> \<open>Munkres: Abelianize G. G/[G,G] is free abelian on both p(S1) and p(S2).
     By Theorem 67.8, |p(S1)| = |p(S2)|. Since p is injective on generators
     of a free group, |S1| = |p(S1)| and |S2| = |p(S2)|.\<close>
  \<comment> \<open>Proof: Abelianize G via Theorem 69.4. G/[G,G] is free abelian
     on both p(S1) and p(S2). Theorem 67.8 gives |S1| = |S2|.
     Depends on Theorem\_69\_4 (defined later) and Theorem\_67\_8.\<close>
  \<comment> \<open>Munkres Corollary 69.5: Abelianize G via Theorem 69.4. G/[G,G] is free abelian
     on S1 (from first free group structure) and on S2 (from second).
     By Theorem 67.8, |S1| = |S2|.\<close>
  \<comment> \<open>Step 1: Get the concrete abelianization = G/[G,G].\<close>
  have hG: "top1_is_group_on G mul e invg"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  let ?N = "top1_commutator_subgroup_on G mul e invg"
  let ?H = "top1_quotient_group_carrier_on G mul ?N"
  let ?mulH = "top1_quotient_group_mul_on mul"
  let ?eH = "top1_group_coset_on G mul ?N e"
  let ?invgH = "\<lambda>C. top1_group_coset_on G mul ?N (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul ?N g))"
  \<comment> \<open>Step 2: Apply Theorem 69.4 to get free abelian on S1.\<close>
  let ?\<phi> = "\<lambda>g. top1_group_coset_on G mul ?N g"
  let ?\<iota>H1 = "\<lambda>s. ?\<phi> (\<iota>1 s)"
  let ?\<iota>H2 = "\<lambda>s. ?\<phi> (\<iota>2 s)"
  \<comment> \<open>Both Theorem\_69\_4 applications return the same concrete H, mulH, eH, invgH.\<close>
  have hfab1: "\<exists>\<iota>H. top1_is_free_abelian_group_full_on ?H ?mulH ?eH ?invgH \<iota>H S1"
    by (rule Theorem_69_4_concrete_free_abelian[OF assms(1)])
  have hfab2: "\<exists>\<iota>H. top1_is_free_abelian_group_full_on ?H ?mulH ?eH ?invgH \<iota>H S2"
    by (rule Theorem_69_4_concrete_free_abelian[OF assms(2)])
  \<comment> \<open>Step 3: Both are free abelian on the same H. Apply Theorem 67.8.\<close>
  from hfab1 obtain \<iota>H1 where hfa1: "top1_is_free_abelian_group_full_on ?H ?mulH ?eH ?invgH \<iota>H1 S1"
    by (by100 blast)
  from hfab2 obtain \<iota>H2 where hfa2: "top1_is_free_abelian_group_full_on ?H ?mulH ?eH ?invgH \<iota>H2 S2"
    by (by100 blast)
  from Theorem_67_8_rank_unique[OF hfa1 hfa2 assms(3,4)]
  obtain f where "bij_betw f S1 S2" by (by100 blast)
  thus "card S1 = card S2" using bij_betw_same_card by (by100 blast)
qed




\<comment> \<open>Helper: Z/nZ is the quotient of Z by the subgroup nZ.
   More precisely: the quotient of (UNIV::int set, +) by the normal subgroup
   generated by {int n} is isomorphic to (top1_Zn_group n, top1_Zn_mul n).\<close>
lemma Z_quotient_nZ_iso:
  assumes "n \<ge> 1"
  shows "top1_groups_isomorphic_on
      (top1_quotient_group_carrier_on (UNIV::int set) (+)
         (top1_normal_subgroup_generated_on (UNIV::int set) (+) (0::int) uminus {int n}))
      (top1_quotient_group_mul_on (+))
      (top1_Zn_group n) (top1_Zn_mul n)"
proof -
  \<comment> \<open>Step 1: The normal subgroup generated by {n} in (Z,+) is nZ = {k*n | k}.\<close>
  let ?nZ = "top1_normal_subgroup_generated_on (UNIV::int set) (+) (0::int) uminus {int n}"
  have hnZ_eq: "?nZ = {k * int n | k. True}"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> ?nZ"
    \<comment> \<open>?nZ \<subseteq> every normal subgroup containing {n}. nZ is such a subgroup.\<close>
    have hnZ_normal: "top1_normal_subgroup_on (UNIV::int set) (+) 0 uminus {k * int n | k. True}"
      unfolding top1_normal_subgroup_on_def
    proof (intro conjI)
      show "{k * int n |k. True} \<subseteq> (UNIV::int set)" by (by100 blast)
      show "top1_is_group_on {k * int n |k. True} (+) 0 uminus"
        unfolding top1_is_group_on_def
      proof (intro conjI)
        show "(0::int) \<in> {k * int n |k. True}"
        proof -
          have "(0::int) = (0::int) * int n" by (by100 simp)
          thus ?thesis by (by100 blast)
        qed
        show "\<forall>x\<in>{k * int n |k. True}. \<forall>y\<in>{k * int n |k. True}. x + y \<in> {k * int n |k. True}"
        proof (intro ballI)
          fix x y :: int assume "x \<in> {k * int n |k. True}" "y \<in> {k * int n |k. True}"
          then obtain kx ky where "x = kx * int n" "y = ky * int n" by (by100 blast)
          hence "x + y = (kx + ky) * int n" using distrib_right[of kx ky "int n"] by (by100 simp)
          thus "x + y \<in> {k * int n |k. True}" by (by100 blast)
        qed
        show "\<forall>x\<in>{k * int n |k. True}. uminus x \<in> {k * int n |k. True}"
        proof (intro ballI)
          fix x :: int assume "x \<in> {k * int n |k. True}"
          then obtain kx where "x = kx * int n" by (by100 blast)
          hence "uminus x = (-kx) * int n" by (by100 simp)
          thus "uminus x \<in> {k * int n |k. True}" by (by100 blast)
        qed
        show "\<forall>x\<in>{k * int n |k. True}. \<forall>y\<in>{k * int n |k. True}.
            \<forall>z\<in>{k * int n |k. True}. x + y + z = x + (y + z)" by (by100 simp)
        show "\<forall>x\<in>{k * int n |k. True}. (0::int) + x = x \<and> x + 0 = x" by (by100 simp)
        show "\<forall>x\<in>{k * int n |k. True}. uminus x + x = (0::int) \<and> x + uminus x = 0" by (by100 simp)
      qed
      show "\<forall>g\<in>(UNIV::int set). \<forall>h\<in>{k * int n |k. True}. g + h + uminus g \<in> {k * int n |k. True}"
      proof (intro ballI)
        fix g h :: int assume "g \<in> (UNIV::int set)" "h \<in> {k * int n |k. True}"
        then obtain kh where "h = kh * int n" by (by100 blast)
        hence "g + h + uminus g = kh * int n" by (by100 simp)
        thus "g + h + uminus g \<in> {k * int n |k. True}" by (by100 blast)
      qed
    qed
    have "{int n} \<subseteq> {k * int n |k. True}"
    proof -
      have "int n = (1::int) * int n" by (by100 simp)
      thus ?thesis by (by100 blast)
    qed
    hence "?nZ \<subseteq> {k * int n |k. True}"
      unfolding top1_normal_subgroup_generated_on_def using hnZ_normal by (by100 blast)
    thus "x \<in> {k * int n |k. True}" using \<open>x \<in> ?nZ\<close> by (by100 blast)
  next
    fix x assume "x \<in> {k * int n |k. True}"
    then obtain k :: int where hk: "x = k * int n" by (by100 blast)
    \<comment> \<open>n \<in> ?nZ and ?nZ is a group, so k*n \<in> ?nZ by closure.\<close>
    have hZ_grp: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
      using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
        top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 simp)
    have hn_in_nZ: "int n \<in> ?nZ"
    proof -
      have "{int n} \<subseteq> ?nZ"
        unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    have hN_sub: "?nZ \<subseteq> (UNIV::int set)" by (by100 blast)
    have hN_grp: "top1_is_group_on ?nZ (+) (0::int) uminus"
      using normal_subgroup_generated_is_normal[OF hZ_grp, of "{int n}"]
      unfolding top1_normal_subgroup_on_def by (by100 blast)
    \<comment> \<open>Induction: k*n \<in> ?nZ for all k.\<close>
    have "k * int n \<in> ?nZ"
    proof (cases "k \<ge> 0")
      case True
      have "\<forall>j::int. j \<ge> 0 \<longrightarrow> j * int n \<in> ?nZ"
      proof (rule allI, rule impI)
        fix j :: int assume "j \<ge> 0"
        then obtain jn :: nat where "j = int jn" using nonneg_int_cases by (by100 blast)
        show "j * int n \<in> ?nZ"
        proof -
          have "int jn * int n \<in> ?nZ"
          proof (induct jn)
            case 0
            have "(0::int) \<in> ?nZ" using hN_grp unfolding top1_is_group_on_def by (by100 blast)
            thus ?case by (by100 simp)
          next
            case (Suc jn)
            have hS: "int (Suc jn) * int n = int jn * int n + int n"
            proof -
              have "int (Suc jn) = 1 + int jn" by (by100 simp)
              hence "int (Suc jn) * int n = (1 + int jn) * int n" by (by100 simp)
              also have "\<dots> = 1 * int n + int jn * int n"
                using distrib_right[of 1 "int jn" "int n"] by (by100 simp)
              finally show ?thesis by (by100 simp)
            qed
            have "int jn * int n + int n \<in> ?nZ"
            proof -
              have "\<forall>x\<in>?nZ. \<forall>y\<in>?nZ. x + y \<in> ?nZ"
                using hN_grp unfolding top1_is_group_on_def by (by100 blast)
              thus ?thesis using Suc hn_in_nZ by (by100 blast)
            qed
            thus ?case using hS by (by100 simp)
          qed
          thus ?thesis using \<open>j = int jn\<close> by (by100 simp)
        qed
      qed
      thus ?thesis using True by (by100 blast)
    next
      case False
      hence "k < 0" by (by100 simp)
      hence "-k > 0" by (by100 simp)
      have "(-k) * int n \<in> ?nZ"
      proof -
        have "-k \<ge> 0" using \<open>-k > 0\<close> by (by100 simp)
        then obtain jn :: nat where "-k = int jn" using nonneg_int_cases by (by100 blast)
        have "int jn * int n \<in> ?nZ"
        proof (induct jn)
          case 0 thus ?case using hN_grp unfolding top1_is_group_on_def by (by100 simp)
        next
          case (Suc jn)
          have "int (Suc jn) * int n = int jn * int n + int n"
          proof -
            have "int (Suc jn) = 1 + int jn" by (by100 simp)
            hence "int (Suc jn) * int n = (1 + int jn) * int n" by (by100 simp)
            also have "\<dots> = 1 * int n + int jn * int n"
              using distrib_right[of 1 "int jn" "int n"] by (by100 simp)
            finally show ?thesis by (by100 simp)
          qed
          have "int jn * int n + int n \<in> ?nZ"
          proof -
            have "\<forall>x\<in>?nZ. \<forall>y\<in>?nZ. x + y \<in> ?nZ"
              using hN_grp unfolding top1_is_group_on_def by (by100 blast)
            thus ?thesis using Suc hn_in_nZ by (by100 blast)
          qed
          thus ?case using \<open>int (Suc jn) * int n = int jn * int n + int n\<close> by (by100 simp)
        qed
        thus ?thesis using \<open>-k = int jn\<close> by (by100 simp)
      qed
      hence "uminus ((-k) * int n) \<in> ?nZ" using hN_grp unfolding top1_is_group_on_def by (by100 blast)
      moreover have "uminus ((-k) * int n) = k * int n" by (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    thus "x \<in> ?nZ" using hk by (by100 simp)
  qed
  \<comment> \<open>Step 2: Define the quotient map \<phi>: Z \<rightarrow> Z/nZ by \<phi>(k) = k mod n.\<close>
  let ?\<phi> = "\<lambda>k::int. k mod int n"
  \<comment> \<open>Step 3: \<phi> is a surjective group homomorphism with kernel nZ.\<close>
  have hphi_hom: "\<forall>a::int. \<forall>b::int. ?\<phi> (a + b) = top1_Zn_mul n (?\<phi> a) (?\<phi> b)"
    unfolding top1_Zn_mul_def
  proof (intro allI)
    fix a b :: int
    show "(a + b) mod int n = (a mod int n + b mod int n) mod int n"
      using mod_add_eq[of a "int n" b] by (by100 simp)
  qed
  have hphi_surj: "?\<phi> ` (UNIV::int set) = top1_Zn_group n"
    unfolding top1_Zn_group_def
  proof (rule equalityI)
    show "(\<lambda>k::int. k mod int n) ` UNIV \<subseteq> {0..<int n}"
      using assms by (by100 auto)
    show "{0..<int n} \<subseteq> (\<lambda>k::int. k mod int n) ` UNIV"
    proof
      fix x :: int assume hx: "x \<in> {0..<int n}"
      hence hxmod: "x mod int n = x" using assms by (by100 auto)
      show "x \<in> (\<lambda>k. k mod int n) ` UNIV"
        apply (rule image_eqI[of _ _ x])
        using hxmod apply (by100 simp)
        apply (by100 simp)
        done
    qed
  qed
  have hphi_ker: "{k::int. ?\<phi> k = 0} = ?nZ"
    unfolding hnZ_eq
  proof (rule set_eqI, rule iffI)
    fix k :: int assume "k \<in> {k. k mod int n = 0}"
    hence "k mod int n = 0" by (by100 blast)
    hence "int n dvd k"
    proof -
      have "k div int n * int n + k mod int n = k" by (rule div_mult_mod_eq)
      hence "k = k div int n * int n" using \<open>k mod int n = 0\<close> by (by100 simp)
      hence "k = int n * (k div int n)" using mult.commute[of "k div int n" "int n"] by (by100 simp)
      thus ?thesis unfolding dvd_def by (by100 blast)
    qed
    then obtain j where "k = int n * j" unfolding dvd_def by (by100 blast)
    hence "k = j * int n" using mult.commute[of "int n" j] by (by100 simp)
    thus "k \<in> {k * int n |k. True}" by (by100 blast)
  next
    fix k :: int assume "k \<in> {k * int n |k. True}"
    then obtain j where hk: "k = j * int n" by (by100 blast)
    hence "k mod int n = 0" using assms by (by100 simp)
    thus "k \<in> {k. k mod int n = 0}" by (by100 blast)
  qed
  \<comment> \<open>Step 4: By first isomorphism theorem: Z/nZ \<cong> im(\<phi>) = Z_n.\<close>
  have hZ_grp: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
    using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
      top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 simp)
  have hN_normal: "top1_normal_subgroup_on (UNIV::int set) (+) (0::int) uminus ?nZ"
    by (rule normal_subgroup_generated_is_normal[OF hZ_grp]) (by100 simp)
  have hZn_grp: "top1_is_group_on (top1_Zn_group n) (top1_Zn_mul n)
      (0::int) (top1_Zn_invg n)"
    using top1_Zn_is_abelian_group[OF assms] unfolding top1_is_abelian_group_on_def top1_Zn_id_def
    by (by100 blast)
  have hphi_hom_on: "top1_group_hom_on (UNIV::int set) (+) (top1_Zn_group n) (top1_Zn_mul n) ?\<phi>"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    fix x :: int show "?\<phi> x \<in> top1_Zn_group n"
      unfolding top1_Zn_group_def using assms by (by100 auto)
    fix y :: int show "?\<phi> (x + y) = top1_Zn_mul n (?\<phi> x) (?\<phi> y)"
      using hphi_hom by (by100 blast)
  qed
  have hphi_ker_on: "top1_group_kernel_on (UNIV::int set) (0::int) ?\<phi> = ?nZ"
  proof -
    have "top1_group_kernel_on (UNIV::int set) (0::int) ?\<phi> = {k::int. ?\<phi> k = 0} \<inter> UNIV"
      unfolding top1_group_kernel_on_def by (by100 blast)
    also have "\<dots> = {k::int. ?\<phi> k = 0}" by (by100 simp)
    also have "\<dots> = ?nZ" by (rule hphi_ker)
    finally show ?thesis .
  qed
  from first_isomorphism_theorem[OF hZ_grp hN_normal hZn_grp hphi_hom_on hphi_surj hphi_ker_on]
  show ?thesis
    by (rule top1_groups_isomorphic_on_sym[OF _ hZn_grp quotient_group_is_group[OF hZ_grp hN_normal]])
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
  \<comment> \<open>Step 1: For each finite F \<subseteq> J, the sub-wedge X_F has free \<pi>_1 on F
     (by Theorem 71.1 for finite wedges).\<close>
  \<comment> \<open>Step 2: The inclusions X_F \<hookrightarrow> X_G for F \<subseteq> G give a directed system.
     The direct limit of free groups on finite subsets = free group on J.\<close>
  \<comment> \<open>Step 3: \<pi>_1(X) = direct limit of \<pi>_1(X_F) by the weak topology on X
     (a loop in X is compact, hence contained in some finite sub-wedge).\<close>
  show ?thesis sorry \<comment> \<open>Direct limit argument: finite sub-wedges (Thm 71.1) + compactness of loops.\<close>
qed


text \<open>For any natural number n, a wedge of n circles exists as a topological space.\<close>
lemma wedge_of_circles_exists:
  "\<exists>(X :: (real \<times> real) set) TX (p :: real \<times> real).
      top1_is_wedge_of_circles_on X TX {..<n} p"
  sorry

text \<open>Bridge: compact in HOL Analysis equals top1\_compact\_on for R^2 subspaces.\<close>
lemma compact_R2_bridge:
  assumes "compact (A :: (real \<times> real) set)"
  shows "top1_compact_on A (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) A)"
proof -
  let ?R2 = "UNIV :: (real \<times> real) set"
  let ?T = "product_topology_on top1_open_sets top1_open_sets"
  let ?TA = "subspace_topology ?R2 ?T A"
  \<comment> \<open>The subspace topology is a topology.\<close>
  have hA_sub: "A \<subseteq> ?R2" by (by100 blast)
  have hT_top: "is_topology_on ?R2 ?T"
  proof -
    have "is_topology_on (UNIV::real set) top1_open_sets"
      unfolding top1_open_sets_def is_topology_on_def
      using open_UNIV open_empty open_Un open_Int by (by5000 auto)
    hence "is_topology_on ((UNIV::real set) \<times> (UNIV::real set)) ?T"
      using product_topology_on_is_topology_on by (by100 blast)
    thus ?thesis by (by100 simp)
  qed
  have hTA_top: "is_topology_on A ?TA"
    by (rule subspace_topology_is_topology_on[OF hT_top hA_sub])
  \<comment> \<open>Every cover of A from ?TA has a finite subcover.\<close>
  have hcover: "\<And>Uc. Uc \<subseteq> ?TA \<Longrightarrow> A \<subseteq> \<Union>Uc \<Longrightarrow> \<exists>F. finite F \<and> F \<subseteq> Uc \<and> A \<subseteq> \<Union>F"
  proof -
    fix Uc assume hUc: "Uc \<subseteq> ?TA" and hcover: "A \<subseteq> \<Union>Uc"
    \<comment> \<open>Each U \<in> Uc is A \<inter> V for some V \<in> ?T. The V's form an open cover of A.\<close>
    \<comment> \<open>Each V \<in> ?T corresponds to an open set (product topology = standard topology).\<close>
    \<comment> \<open>compact A gives a finite subcover of V's, hence of U's.\<close>
    \<comment> \<open>For each U \<in> Uc, extract V \<in> R^2\_top with U = A \<inter> V.\<close>
    define VV where "VV U = (SOME V. V \<in> ?T \<and> U = A \<inter> V)" for U
    have hVV: "\<And>U. U \<in> Uc \<Longrightarrow> VV U \<in> ?T \<and> U = A \<inter> VV U"
    proof -
      fix U assume "U \<in> Uc"
      hence "U \<in> ?TA" using hUc by (by100 blast)
      hence "\<exists>V. V \<in> ?T \<and> U = A \<inter> V"
        unfolding subspace_topology_def by (by5000 blast)
      thus "VV U \<in> ?T \<and> U = A \<inter> VV U" unfolding VV_def by (rule someI_ex)
    qed
    \<comment> \<open>The V's cover A.\<close>
    have hV_cover: "A \<subseteq> \<Union>(VV ` Uc)"
    proof (rule subsetI)
      fix x assume "x \<in> A"
      from hcover \<open>x \<in> A\<close> obtain U where "U \<in> Uc" "x \<in> U" by (by100 blast)
      hence "x \<in> A \<inter> VV U" using hVV by (by100 blast)
      hence "x \<in> VV U" by (by100 blast)
      thus "x \<in> \<Union>(VV ` Uc)" using \<open>U \<in> Uc\<close> by (by100 blast)
    qed
    \<comment> \<open>Each VV U is open (product topology = standard open sets).\<close>
    have hV_open: "\<And>U. U \<in> Uc \<Longrightarrow> open (VV U)"
    proof -
      fix U assume "U \<in> Uc"
      from hVV[OF this] have hvu: "VV U \<in> ?T" by (by100 blast)
      have "?T = top1_open_sets" by (rule product_topology_on_open_sets)
      hence "VV U \<in> top1_open_sets" using hvu by (by5000 fast)
      thus "open (VV U)" unfolding top1_open_sets_def by (by100 blast)
    qed
    \<comment> \<open>compact A gives a finite subcover.\<close>
    have "\<exists>F. finite F \<and> F \<subseteq> VV ` Uc \<and> A \<subseteq> \<Union>F"
    proof -
      have hopen: "\<forall>V \<in> VV ` Uc. open V" using hV_open by (by100 blast)
      from assms have hHB: "\<And>C. (\<forall>c\<in>C. open c) \<Longrightarrow> A \<subseteq> \<Union>C \<Longrightarrow> \<exists>D\<subseteq>C. finite D \<and> A \<subseteq> \<Union>D"
        unfolding compact_eq_Heine_Borel by (by100 blast)
      from hHB[OF hopen hV_cover]
      obtain D where "D \<subseteq> VV ` Uc" "finite D" "A \<subseteq> \<Union>D" by (by5000 blast)
      thus ?thesis by (by100 blast)
    qed
    then obtain FV where hFV_fin: "finite FV" and hFV_sub: "FV \<subseteq> VV ` Uc"
      and hFV_cover: "A \<subseteq> \<Union>FV" by (by5000 fast)
    \<comment> \<open>Map back: for each V \<in> FV, pick one representative U \<in> Uc with VV U = V.\<close>
    define rep where "rep V = (SOME U. U \<in> Uc \<and> VV U = V)" for V
    have hrep: "\<And>V. V \<in> FV \<Longrightarrow> rep V \<in> Uc \<and> VV (rep V) = V"
    proof -
      fix V assume "V \<in> FV"
      hence "V \<in> VV ` Uc" using hFV_sub by (by100 blast)
      hence "\<exists>U. U \<in> Uc \<and> VV U = V" by (by100 blast)
      thus "rep V \<in> Uc \<and> VV (rep V) = V" unfolding rep_def by (rule someI_ex)
    qed
    define FU where "FU = rep ` FV"
    have "finite FU" unfolding FU_def using hFV_fin by (by100 blast)
    have "FU \<subseteq> Uc" unfolding FU_def using hrep by (by100 blast)
    have "A \<subseteq> \<Union>FU"
    proof (rule subsetI)
      fix x assume "x \<in> A"
      from hFV_cover \<open>x \<in> A\<close> obtain V where "V \<in> FV" "x \<in> V" by (by100 blast)
      have "rep V \<in> FU" unfolding FU_def using \<open>V \<in> FV\<close> by (by100 blast)
      moreover have "x \<in> rep V"
        using hVV[OF conjunct1[OF hrep[OF \<open>V \<in> FV\<close>]]] \<open>x \<in> A\<close> \<open>x \<in> V\<close>
          conjunct2[OF hrep[OF \<open>V \<in> FV\<close>]] by (by100 blast)
      ultimately show "x \<in> \<Union>FU" by (by100 blast)
    qed
    show "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> A \<subseteq> \<Union>F"
      using \<open>finite FU\<close> \<open>FU \<subseteq> Uc\<close> \<open>A \<subseteq> \<Union>FU\<close> by (by100 blast)
  qed
  show ?thesis unfolding top1_compact_on_def using hTA_top hcover by (by100 blast)
qed

text \<open>Helper: 2D cross product (signed area of parallelogram).\<close>
definition cross2 :: "real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> real" where
  "cross2 a b = fst a * snd b - snd a * fst b"

text \<open>For a convex polygon with centroid c, the cross products cross(v_i - c, d)
  sum to 0 for any direction d. This means there exists a sign change,
  giving the sector containing d.\<close>
lemma cross2_centroid_sum_zero:
  fixes vx vy :: "nat \<Rightarrow> real" and n :: nat and dx dy :: real
  assumes "n \<ge> 1"
  defines "cx \<equiv> (\<Sum>i<n. vx i) / real n" and "cy \<equiv> (\<Sum>i<n. vy i) / real n"
  shows "(\<Sum>i<n. cross2 (vx i - cx, vy i - cy) (dx, dy)) = 0"
proof -
  have hvx_sum: "(\<Sum>i<n. vx i) = real n * cx" unfolding cx_def using assms by (by100 simp)
  have hvy_sum: "(\<Sum>i<n. vy i) = real n * cy" unfolding cy_def using assms by (by100 simp)
  \<comment> \<open>The sum telescopes: cross2(v_i-c, d) = (vx_i-cx)*dy - (vy_i-cy)*dx.
     \<Sum> = dy*(\<Sum>vx_i - n*cx) - dx*(\<Sum>vy_i - n*cy) = dy*0 - dx*0 = 0.\<close>
  have hstep1: "\<And>i. (vx i - cx) * dy - (vy i - cy) * dx
      = vx i * dy - cx * dy - (vy i * dx - cy * dx)"
    by (simp add: algebra_simps)
  \<comment> \<open>Step 1: Expand cross2.\<close>
  have heq1: "(\<Sum>i<n. cross2 (vx i - cx, vy i - cy) (dx, dy))
      = (\<Sum>i<n. (vx i - cx) * dy - (vy i - cy) * dx)"
    unfolding cross2_def by (by100 simp)
  \<comment> \<open>Step 2: Split sum of differences.\<close>
  have heq2: "(\<Sum>i<n. (vx i - cx) * dy - (vy i - cy) * dx)
      = (\<Sum>i<n. (vx i - cx) * dy) - (\<Sum>i<n. (vy i - cy) * dx)"
    using sum_subtractf[of "\<lambda>i. (vx i - cx) * dy" "\<lambda>i. (vy i - cy) * dx" "{..<n}", symmetric]
    by (by5000 simp)
  \<comment> \<open>Step 3: Each sub-sum is zero because \<Sum>(vx_i - cx) = \<Sum>vx_i - n*cx = 0.\<close>
  have hvx_diff_sum: "(\<Sum>i<n. vx i - cx) = 0"
    using sum_subtractf[of vx "\<lambda>_. cx" "{..<n}"] hvx_sum by (by5000 simp)
  have hvy_diff_sum: "(\<Sum>i<n. vy i - cy) = 0"
    using sum_subtractf[of vy "\<lambda>_. cy" "{..<n}"] hvy_sum by (by5000 simp)
  have hx_zero: "(\<Sum>i<n. (vx i - cx) * dy) = 0"
  proof -
    have "(\<Sum>i<n. (vx i - cx) * dy) = (\<Sum>i<n. (vx i - cx)) * dy"
      using sum_distrib_right[of "\<lambda>i. vx i - cx" "{..<n}" dy, symmetric] by (by100 simp)
    thus ?thesis using hvx_diff_sum by (by100 simp)
  qed
  have hy_zero: "(\<Sum>i<n. (vy i - cy) * dx) = 0"
  proof -
    have "(\<Sum>i<n. (vy i - cy) * dx) = (\<Sum>i<n. (vy i - cy)) * dx"
      using sum_distrib_right[of "\<lambda>i. vy i - cy" "{..<n}" dx, symmetric] by (by100 simp)
    thus ?thesis using hvy_diff_sum by (by100 simp)
  qed
  show ?thesis using heq1 heq2 hx_zero hy_zero by (by100 simp)
qed

text \<open>If a sequence of reals sums to 0 and is not all zero, there exists an index
  where consecutive elements have opposite signs (a sign change).\<close>
lemma cyclic_sign_change:
  fixes f :: "nat \<Rightarrow> real" and n :: nat
  assumes "n \<ge> 2" and "(\<Sum>i<n. f i) = 0" and "\<exists>i<n. f i \<noteq> 0"
  shows "\<exists>i<n. f i \<ge> 0 \<and> f ((i+1) mod n) \<le> 0"
proof -
  \<comment> \<open>Since \<Sum>f_i = 0 and not all zero, there exist positive and negative values.\<close>
  \<comment> \<open>If no f_i \<ge> 0 had successor f_{i+1} \<le> 0, then every f_i \<ge> 0 implies f_{i+1} \<ge> 0.
     This transitivity around the cycle would force all f_i \<ge> 0 (starting from any
     positive element). But \<Sum>f_i = 0 with all f_i \<ge> 0 forces all = 0, contradicting \<exists>f_i \<noteq> 0.\<close>
  show ?thesis
  proof (rule ccontr)
    assume hno: "\<not> (\<exists>i<n. f i \<ge> 0 \<and> f ((i+1) mod n) \<le> 0)"
    hence htrans: "\<forall>i<n. f i \<ge> 0 \<longrightarrow> f ((i+1) mod n) > 0" by (by100 force)
    \<comment> \<open>From htrans: any non-negative f_i implies f_{i+1} > 0 (hence \<ge> 0), which propagates.\<close>
    \<comment> \<open>Either all f_i < 0 (contradicts \<Sum>=0 + not all zero → some must be \<ge> 0),
       or some f_i \<ge> 0, which propagates to all f_j > 0, contradicting \<Sum>=0.\<close>
    \<comment> \<open>Case 1: All f_i < 0. Then \<Sum>f_i < 0 (n \<ge> 2), contradicting \<Sum>=0.\<close>
    \<comment> \<open>Case 2: Some f_k \<ge> 0. By htrans, f_{k+1} > 0 \<ge> 0, f_{k+2} > 0, etc.
       After n steps: all f_i > 0. But \<Sum>f_i > 0, contradicting \<Sum>=0.\<close>
    show False
    proof (cases "\<forall>i<n. f i < 0")
      case True
      have "(\<Sum>i<n. f i) < 0"
      proof -
        have "(\<Sum>i<n. f i) \<le> 0"
          using sum_nonpos[of "{..<n}" f] True by (by5000 force)
        moreover have "(\<Sum>i<n. f i) \<noteq> 0"
        proof
          assume "(\<Sum>i<n. f i) = 0"
          have "(\<Sum>i<n. - f i) = - (\<Sum>i<n. f i)"
            using sum_negf by (by100 blast)
          hence "(\<Sum>i<n. - f i) = 0" using \<open>(\<Sum>i<n. f i) = 0\<close> by (by100 simp)
          have hnn: "\<And>x. x \<in> {..<n} \<Longrightarrow> 0 \<le> - f x"
            using True by (by100 force)
          hence "\<forall>i\<in>{..<n}. - f i = 0"
            using sum_nonneg_eq_0_iff[of "{..<n}" "\<lambda>i. - f i"]
              \<open>(\<Sum>i<n. - f i) = 0\<close> hnn by (by100 blast)
          hence "\<forall>i<n. f i = 0" by (by100 force)
          thus False using assms(3) by (by100 blast)
        qed
        ultimately show ?thesis by (by100 linarith)
      qed
      thus False using assms(2) by (by100 simp)
    next
      case False
      then obtain k where hk: "k < n" "f k \<ge> 0" by (by100 force)
      \<comment> \<open>Propagate: f_k \<ge> 0 \<Rightarrow> f_{k+1} > 0 \<Rightarrow> f_{k+2} > 0 \<Rightarrow> ... \<Rightarrow> all > 0.\<close>
      have hprop: "\<And>j. j < n \<Longrightarrow> f ((k + j) mod n) \<ge> 0"
      proof -
        fix j show "j < n \<Longrightarrow> f ((k + j) mod n) \<ge> 0"
        proof (induction j)
          case 0 thus ?case using hk by (by100 simp)
        next
          case (Suc j)
          hence hj: "j < n" by (by100 simp)
          have hjmod: "(k + j) mod n < n" using assms(1) by (by100 simp)
          have hfj: "f ((k + j) mod n) \<ge> 0" using Suc.IH hj by (by100 blast)
          from htrans[rule_format, OF hjmod hfj]
          have "f (((k + j) mod n + 1) mod n) > 0" .
          moreover have "((k + j) mod n + 1) mod n = (k + Suc j) mod n"
          proof -
            have "((k + j) mod n + 1) mod n = (k + j + 1) mod n"
              using mod_add_left_eq[of "k+j" n 1] by (by100 simp)
            thus ?thesis by (by100 simp)
          qed
          ultimately show ?case by (by100 simp)
        qed
      qed
      have "\<forall>i<n. f i \<ge> 0"
      proof (intro allI impI)
        fix i assume "i < n"
        \<comment> \<open>i = (k + ((i - k) mod n)) mod n, and (i - k) mod n < n.\<close>
        have "\<exists>j<n. (k + j) mod n = i"
        proof (cases "k \<le> i")
          case True
          show ?thesis
            apply (rule exI[of _ "i - k"])
            using True \<open>i < n\<close> hk(1) by (by100 simp)
        next
          case False
          hence hki: "k > i" by (by100 simp)
          show ?thesis
            apply (rule exI[of _ "n - k + i"])
            using hki \<open>i < n\<close> hk(1) by (by5000 simp)
        qed
        then obtain j where "j < n" "(k + j) mod n = i" by (by100 blast)
        thus "f i \<ge> 0" using hprop[of j] by (by100 simp)
      qed
      hence "\<forall>i<n. f i = 0"
        using sum_nonneg_eq_0_iff[of "{..<n}" f] assms(2)
        by (by5000 force)
      thus False using assms(3) by (by100 blast)
    qed
  qed
qed

text \<open>A convex polygon in R^2 is homeomorphic to B^2 (the closed unit disk).
  This is a standard topology fact (radial projection from centroid).\<close>
lemma polygon_homeomorphic_to_disk:
  assumes "top1_is_polygonal_region_on P n" and "n \<ge> 3"
  shows "\<exists>\<psi>. top1_homeomorphism_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P)
    top1_B2 top1_B2_topology \<psi>"
proof -
  \<comment> \<open>Following Munkres §74 (paragraph before Theorem 74.2):
     Pick a point p in Int P. For each x in Bd P, the line segment from p to x
     intersects Bd P in exactly one point (convexity). The boundary map
     h: Bd P \<rightarrow> S^1 extends radially to \<psi>: P \<rightarrow> B^2 by
     \<psi>((1-t)\<cdot>p + t\<cdot>x) = t \<cdot> h(x) for t \<in> [0,1], x \<in> Bd P.
     Since P is compact and B^2 is Hausdorff, a continuous bijection P \<rightarrow> B^2
     is automatically a homeomorphism.\<close>
  \<comment> \<open>Step 1: P is compact (closed bounded subset of R^2).\<close>
  have hP_compact: "top1_compact_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P)"
  proof -
    have "compact P"
    proof -
      \<comment> \<open>P is a convex hull of finitely many points in R^2, hence bounded and closed.
         Compact follows from closed\_subset\_compact + compact\_Icc\_Times.\<close>
      from assms(1)[unfolded top1_is_polygonal_region_on_def]
      obtain vx vy where
        hdist: "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)" and
        hgp: "\<forall>k<n. \<not> (\<exists>coeffs. (\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0)
                          \<and> coeffs k = 0 \<and> (\<Sum>i<n. coeffs i) = 1
                          \<and> vx k = (\<Sum>i<n. coeffs i * vx i)
                          \<and> vy k = (\<Sum>i<n. coeffs i * vy i))" and
        hP: "P = {(x, y) | x y. \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
              \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
        by (elim conjE exE) (rule that, assumption+)
      \<comment> \<open>P is bounded: convex combinations of bounded coords are bounded.\<close>
      define M where "M = 1 + Max ((\<lambda>i. max (abs (vx i)) (abs (vy i))) ` {..<n})"
      have hP_bdd: "P \<subseteq> {-M..M} \<times> {-M..M}"
      proof (rule subsetI)
        fix p assume "p \<in> P"
        obtain x y where hp: "p = (x, y)" by (cases p) (by100 blast)
        from \<open>p \<in> P\<close> hp hP
        have "\<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
              \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)"
          by (by5000 auto)
        then obtain coeffs where
          hcge: "\<forall>i<n. coeffs i \<ge> 0" and hcsum: "(\<Sum>i<n. coeffs i) = 1"
          and hx: "x = (\<Sum>i<n. coeffs i * vx i)" and hy: "y = (\<Sum>i<n. coeffs i * vy i)"
          by (by100 blast)
        have hn_pos: "n > 0" using assms(2) by (by100 simp)
        have hM_ge: "\<And>i. i < n \<Longrightarrow> abs (vx i) \<le> M \<and> abs (vy i) \<le> M"
        proof -
          fix i assume "i < n"
          have hfin: "finite ((\<lambda>i. max (abs (vx i)) (abs (vy i))) ` {..<n})" by (by100 blast)
          have hne: "(\<lambda>i. max (abs (vx i)) (abs (vy i))) ` {..<n} \<noteq> {}"
            using hn_pos by (by100 blast)
          have hin: "max (abs (vx i)) (abs (vy i)) \<in> (\<lambda>i. max (abs (vx i)) (abs (vy i))) ` {..<n}"
            using \<open>i < n\<close> by (by100 blast)
          have "max (abs (vx i)) (abs (vy i)) \<le> Max ((\<lambda>i. max (abs (vx i)) (abs (vy i))) ` {..<n})"
            by (rule Max_ge[OF hfin hin])
          also have "\<dots> \<le> M" unfolding M_def by (by100 simp)
          finally show "abs (vx i) \<le> M \<and> abs (vy i) \<le> M" by (by100 simp)
        qed
        \<comment> \<open>Bound x: |x| = |\<Sum> c_i * vx_i| \<le> \<Sum> |c_i * vx_i| \<le> \<Sum> c_i * M = M.\<close>
        have hx_bdd: "x \<in> {-M..M}"
        proof -
          have hci_vx: "\<And>i. i < n \<Longrightarrow> coeffs i * vx i \<le> coeffs i * M"
          proof -
            fix i assume "i < n"
            have "vx i \<le> M" using hM_ge[OF \<open>i < n\<close>] by (by100 linarith)
            moreover have "0 \<le> coeffs i" using hcge \<open>i < n\<close> by (by100 blast)
            ultimately show "coeffs i * vx i \<le> coeffs i * M"
              by (rule mult_left_mono)
          qed
          hence "x \<le> (\<Sum>i<n. coeffs i * M)"
            unfolding hx using sum_mono[of "{..<n}" "\<lambda>i. coeffs i * vx i" "\<lambda>i. coeffs i * M"]
            by (by100 simp)
          also have "\<dots> = M * (\<Sum>i<n. coeffs i)"
            using sum_distrib_right[of coeffs "{..<n}" M, symmetric]
            by (by100 simp)
          also have "\<dots> = M" using hcsum by (by100 simp)
          finally have h1: "x \<le> M" .
          have "\<And>i. i < n \<Longrightarrow> coeffs i * (- M) \<le> coeffs i * vx i"
          proof -
            fix i assume "i < n"
            have "- M \<le> vx i" using hM_ge[OF \<open>i < n\<close>] by (by100 linarith)
            moreover have "0 \<le> coeffs i" using hcge \<open>i < n\<close> by (by100 blast)
            ultimately show "coeffs i * (- M) \<le> coeffs i * vx i"
              by (rule mult_left_mono)
          qed
          hence hlo: "(\<Sum>i<n. coeffs i * (- M)) \<le> (\<Sum>i<n. coeffs i * vx i)"
            using sum_mono[of "{..<n}" "\<lambda>i. coeffs i * (- M)" "\<lambda>i. coeffs i * vx i"]
            by (by100 simp)
          have "(\<Sum>i<n. coeffs i * (- M)) = (- M) * (\<Sum>i<n. coeffs i)"
            using sum_distrib_right[of coeffs "{..<n}" "- M", symmetric]
            by (by100 simp)
          also have "\<dots> = - M" using hcsum by (by100 simp)
          finally have "- M \<le> x" unfolding hx using hlo by (by100 linarith)
          thus ?thesis using h1 by (by100 simp)
        qed
        \<comment> \<open>Bound y: symmetric to x.\<close>
        have hy_bdd: "y \<in> {-M..M}"
        proof -
          have "\<And>i. i < n \<Longrightarrow> coeffs i * vy i \<le> coeffs i * M"
          proof -
            fix i assume "i < n"
            have "vy i \<le> M" using hM_ge[OF \<open>i < n\<close>] by (by100 linarith)
            moreover have "0 \<le> coeffs i" using hcge \<open>i < n\<close> by (by100 blast)
            ultimately show "coeffs i * vy i \<le> coeffs i * M"
              by (rule mult_left_mono)
          qed
          hence "y \<le> (\<Sum>i<n. coeffs i * M)"
            unfolding hy using sum_mono[of "{..<n}" "\<lambda>i. coeffs i * vy i" "\<lambda>i. coeffs i * M"]
            by (by100 simp)
          also have "\<dots> = M * (\<Sum>i<n. coeffs i)"
            using sum_distrib_right[of coeffs "{..<n}" M, symmetric]
            by (by100 simp)
          also have "\<dots> = M" using hcsum by (by100 simp)
          finally have h1: "y \<le> M" .
          have "\<And>i. i < n \<Longrightarrow> coeffs i * (- M) \<le> coeffs i * vy i"
          proof -
            fix i assume "i < n"
            have "- M \<le> vy i" using hM_ge[OF \<open>i < n\<close>] by (by100 linarith)
            moreover have "0 \<le> coeffs i" using hcge \<open>i < n\<close> by (by100 blast)
            ultimately show "coeffs i * (- M) \<le> coeffs i * vy i"
              by (rule mult_left_mono)
          qed
          hence hlo: "(\<Sum>i<n. coeffs i * (- M)) \<le> (\<Sum>i<n. coeffs i * vy i)"
            using sum_mono[of "{..<n}" "\<lambda>i. coeffs i * (- M)" "\<lambda>i. coeffs i * vy i"]
            by (by100 simp)
          have "(\<Sum>i<n. coeffs i * (- M)) = (- M) * (\<Sum>i<n. coeffs i)"
            using sum_distrib_right[of coeffs "{..<n}" "- M", symmetric]
            by (by100 simp)
          also have "\<dots> = - M" using hcsum by (by100 simp)
          finally have "- M \<le> y" unfolding hy using hlo by (by100 linarith)
          thus ?thesis using h1 by (by100 simp)
        qed
        show "p \<in> {-M..M} \<times> {-M..M}" using hp hx_bdd hy_bdd by (by100 blast)
      qed
      \<comment> \<open>Direct compactness via inductive hull construction.\<close>
      define Pk where "Pk k = {(x, y) | x y. \<exists>coeffs. (\<forall>i<k. coeffs i \<ge> 0)
          \<and> (\<Sum>i<k. coeffs i) = 1 \<and> x = (\<Sum>i<k. coeffs i * vx i)
          \<and> y = (\<Sum>i<k. coeffs i * vy i)}" for k :: nat
      have hPk_compact: "n \<ge> 1 \<Longrightarrow> compact (Pk n)"
      proof (rule nat_induct_at_least[of 1 n "\<lambda>k. compact (Pk k)"])
        show "1 \<le> n" using assms(2) by (by100 simp)
      next
        \<comment> \<open>Base: Pk 1 = {(vx 0, vy 0)}, compact as singleton.\<close>
        show "compact (Pk 1)"
        proof -
          have "Pk 1 = {(vx 0, vy 0)}"
          proof (rule set_eqI)
            fix p :: "real \<times> real"
            show "p \<in> Pk 1 \<longleftrightarrow> p \<in> {(vx 0, vy 0)}"
            proof
              assume "p \<in> Pk 1"
              then obtain x y coeffs where hp: "p = (x, y)"
                  and hcge: "\<forall>i<(1::nat). coeffs i \<ge> 0" and hcsum: "(\<Sum>i<1. coeffs i) = 1"
                  and hx: "x = (\<Sum>i<1. coeffs i * vx i)" and hy: "y = (\<Sum>i<1. coeffs i * vy i)"
                unfolding Pk_def by (by5000 auto)
              have "coeffs 0 = 1" using hcsum by (by100 simp)
              hence "x = vx 0" "y = vy 0" using hx hy by (by100 simp)+
              thus "p \<in> {(vx 0, vy 0)}" using hp by (by100 simp)
            next
              assume "p \<in> {(vx 0, vy 0)}"
              hence hp: "p = (vx 0, vy 0)" by (by100 simp)
              have "(vx 0, vy 0) \<in> Pk 1" unfolding Pk_def
                using exI[of _ "\<lambda>_::nat. 1::real"] by (by5000 auto)
              thus "p \<in> Pk 1" using hp by (by100 simp)
            qed
          qed
          thus ?thesis using compact_singleton by (by100 simp)
        qed
      next
        \<comment> \<open>Step: Pk (Suc k) = continuous image of Pk k × [0,1], hence compact.\<close>
        fix k assume "1 \<le> k" "compact (Pk k)"
        have hdom_compact: "compact (Pk k \<times> {0..1::real})"
          by (rule compact_Times_general[OF \<open>compact (Pk k)\<close> compact_Icc])
        have hset: "Pk (Suc k) = (\<lambda>(p, t). ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))
            ` (Pk k \<times> {0..1})"
        proof (rule equalityI)
          \<comment> \<open>(\<subseteq>): element of Pk(Suc k) is a convex combo with k+1 vertices;
             let t = c_k, normalize remaining c_i by (1-t) to get point in Pk k.\<close>
          show "Pk (Suc k) \<subseteq> (\<lambda>(p, t). ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))
              ` (Pk k \<times> {0..1})"
          proof (rule subsetI)
            fix q assume "q \<in> Pk (Suc k)"
            then obtain qx qy c where hq: "q = (qx, qy)"
                and hcge: "\<forall>i<Suc k. c i \<ge> 0" and hcsum: "(\<Sum>i<Suc k. c i) = 1"
                and hqx: "qx = (\<Sum>i<Suc k. c i * vx i)" and hqy: "qy = (\<Sum>i<Suc k. c i * vy i)"
              unfolding Pk_def by (by5000 auto)
            let ?t = "c k"
            have ht_ge: "?t \<ge> 0" using hcge by (by100 simp)
            have hrest: "(\<Sum>i<k. c i) = 1 - ?t" using hcsum by (by100 simp)
            have ht_le: "?t \<le> 1"
            proof -
              have "(\<Sum>i<k. c i) \<ge> 0"
                using hcge by (intro sum_nonneg) (by100 simp)
              thus ?thesis using hrest by (by100 linarith)
            qed
            show "q \<in> (\<lambda>(p, t). ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))
                ` (Pk k \<times> {0..1})"
            proof (cases "?t = 1")
              case True
              \<comment> \<open>All other c_i = 0, q = (vx k, vy k).\<close>
              have hrest0: "(\<Sum>i<k. c i) = 0" using hrest True by (by100 simp)
              have hci0: "\<And>i. i < k \<Longrightarrow> c i = 0"
              proof -
                fix i assume "i < k"
                have "c i \<ge> 0" using hcge \<open>i < k\<close> by (by100 simp)
                moreover have "c i \<le> (\<Sum>i<k. c i)"
                  using hcge \<open>i < k\<close> by (intro member_le_sum) (by100 auto)
                ultimately show "c i = 0" using hrest0 by (by100 simp)
              qed
              have "qx = vx k" using hqx hci0 True by (by100 simp)
              moreover have "qy = vy k" using hqy hci0 True by (by100 simp)
              ultimately have hq_vk: "q = (vx k, vy k)" using hq by (by100 simp)
              \<comment> \<open>v_0 \<in> Pk k (since k \<ge> 1).\<close>
              have hv0: "(vx 0, vy 0) \<in> Pk k"
              proof -
                define c0 where "c0 = (\<lambda>i::nat. if i = 0 then (1::real) else 0)"
                have hc0ge: "\<forall>i<k. c0 i \<ge> 0" unfolding c0_def by (by100 simp)
                have hc0_eq: "\<And>f. (\<Sum>i<k. c0 i * f i) = f 0"
                proof -
                  fix f :: "nat \<Rightarrow> real"
                  from \<open>1 \<le> k\<close> obtain k' where hk': "k = Suc k'" by (cases k) (by100 auto)
                  have "(\<Sum>i<k. c0 i * f i) = (\<Sum>i<Suc k'. c0 i * f i)" unfolding hk' ..
                  also have "\<dots> = c0 0 * f 0 + (\<Sum>i<k'. c0 (Suc i) * f (Suc i))"
                    using sum.lessThan_Suc_shift[of "\<lambda>i. c0 i * f i" k'] by (by100 simp)
                  also have "(\<Sum>i<k'. c0 (Suc i) * f (Suc i)) = 0"
                    unfolding c0_def by (by100 simp)
                  finally show "(\<Sum>i<k. c0 i * f i) = f 0" unfolding c0_def by (by100 simp)
                qed
                have hc0sum: "(\<Sum>i<k. c0 i) = 1"
                proof -
                  have "(\<Sum>i<k. c0 i) = (\<Sum>i<k. c0 i * 1)" by (by100 simp)
                  also have "\<dots> = 1" using hc0_eq[of "\<lambda>_. 1"] by (by100 simp)
                  finally show ?thesis .
                qed
                have hc0x: "(\<Sum>i<k. c0 i * vx i) = vx 0" by (rule hc0_eq)
                have hc0y: "(\<Sum>i<k. c0 i * vy i) = vy 0" by (rule hc0_eq)
                show ?thesis unfolding Pk_def using hc0ge hc0sum hc0x hc0y by (by5000 auto)
              qed
              have "q = ((1 - 1) * fst (vx 0, vy 0) + 1 * vx k,
                         (1 - 1) * snd (vx 0, vy 0) + 1 * vy k)"
                unfolding hq_vk by (by100 simp)
              hence "q = (case ((vx 0, vy 0), 1::real) of (p, t) \<Rightarrow>
                  ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))"
                by (by100 simp)
              moreover have "((vx 0, vy 0), 1::real) \<in> Pk k \<times> {0..1}" using hv0 by (by100 simp)
              ultimately show ?thesis by (by100 blast)
            next
              case False
              hence hlt: "?t < 1" using ht_le by (by100 simp)
              hence h1t_pos: "1 - ?t > 0" by (by100 simp)
              \<comment> \<open>Normalize: c'_i = c_i / (1-t).\<close>
              define c' where "c' i = c i / (1 - ?t)" for i
              have hc'ge: "\<forall>i<k. c' i \<ge> 0" using hcge h1t_pos unfolding c'_def by (by100 simp)
              have hc'sum: "(\<Sum>i<k. c' i) = 1"
                using hrest h1t_pos unfolding c'_def
                using sum_divide_distrib[of c "{..<k}" "1 - ?t"] by (by100 simp)
              define px where "px = (\<Sum>i<k. c' i * vx i)"
              define py where "py = (\<Sum>i<k. c' i * vy i)"
              have hp_in: "(px, py) \<in> Pk k" unfolding Pk_def
                using hc'ge hc'sum unfolding px_def py_def by (by5000 auto)
              \<comment> \<open>Show q = (1-t)*p + t*v_k.\<close>
              have "(\<Sum>i<k. c i * vx i) = (1 - ?t) * px"
              proof -
                have "(1 - ?t) * px = (1 - ?t) * (\<Sum>i<k. c' i * vx i)" unfolding px_def ..
                also have "\<dots> = (\<Sum>i<k. (1 - ?t) * (c' i * vx i))"
                  using sum_distrib_left[of "1-?t" "\<lambda>i. c' i * vx i" "{..<k}", symmetric]
                  by (by100 simp)
                also have "\<dots> = (\<Sum>i<k. c i * vx i)"
                proof (rule sum.cong)
                  fix i assume "i \<in> {..<k}"
                  show "(1 - ?t) * (c' i * vx i) = c i * vx i"
                    unfolding c'_def using h1t_pos by (by100 simp)
                qed (by100 simp)
                finally show ?thesis by (by100 simp)
              qed
              hence hqx_eq: "qx = (1 - ?t) * px + ?t * vx k"
                using hqx by (by100 simp)
              have "(\<Sum>i<k. c i * vy i) = (1 - ?t) * py"
              proof -
                have "(1 - ?t) * py = (1 - ?t) * (\<Sum>i<k. c' i * vy i)" unfolding py_def ..
                also have "\<dots> = (\<Sum>i<k. (1 - ?t) * (c' i * vy i))"
                  using sum_distrib_left[of "1-?t" "\<lambda>i. c' i * vy i" "{..<k}", symmetric]
                  by (by100 simp)
                also have "\<dots> = (\<Sum>i<k. c i * vy i)"
                proof (rule sum.cong)
                  fix i assume "i \<in> {..<k}"
                  show "(1 - ?t) * (c' i * vy i) = c i * vy i"
                    unfolding c'_def using h1t_pos by (by100 simp)
                qed (by100 simp)
                finally show ?thesis by (by100 simp)
              qed
              hence hqy_eq: "qy = (1 - ?t) * py + ?t * vy k"
                using hqy by (by100 simp)
              have "q = ((1 - ?t) * fst (px, py) + ?t * vx k,
                         (1 - ?t) * snd (px, py) + ?t * vy k)"
                using hq hqx_eq hqy_eq by (by100 simp)
              hence "q = (case ((px, py), ?t) of (p, t) \<Rightarrow>
                  ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))"
                by (by100 simp)
              moreover have "((px, py), ?t) \<in> Pk k \<times> {0..1}" using hp_in ht_ge ht_le by (by100 simp)
              ultimately show ?thesis by (by100 blast)
            qed
          qed
          \<comment> \<open>(\<supseteq>): given p \<in> Pk k with coeffs d_i, and t \<in> [0,1],
             define c_i = (1-t)*d_i for i<k, c_k = t. Then \<Sum> c_i = 1.\<close>
          show "(\<lambda>(p, t). ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))
              ` (Pk k \<times> {0..1}) \<subseteq> Pk (Suc k)"
          proof (rule subsetI)
            fix q assume "q \<in> (\<lambda>(p, t). ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))
                ` (Pk k \<times> {0..1})"
            then obtain pt where hpt_in: "pt \<in> Pk k \<times> {0..1::real}"
                and hq: "q = (case pt of (p, t) \<Rightarrow> ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))"
              by (by100 blast)
            obtain p t where hpt: "pt = (p, t)" by (cases pt) (by100 blast)
            have hp: "p \<in> Pk k" and ht: "t \<in> {0..1::real}" using hpt_in hpt by (by100 blast)+
            have hq2: "q = ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k)"
              using hq hpt by (by100 simp)
            from hp obtain px py d where hpp: "p = (px, py)"
                and hdge: "\<forall>i<k. d i \<ge> 0" and hdsum: "(\<Sum>i<k. d i) = 1"
                and hpx: "px = (\<Sum>i<k. d i * vx i)" and hpy: "py = (\<Sum>i<k. d i * vy i)"
              unfolding Pk_def by (by5000 auto)
            define c where "c i = (if i < k then (1-t) * d i else if i = k then t else 0)" for i
            have ht01: "0 \<le> t" "t \<le> 1" using ht by (by100 auto)+
            have hcge: "\<forall>i<Suc k. c i \<ge> 0"
            proof (intro allI impI)
              fix i assume "i < Suc k"
              show "c i \<ge> 0"
              proof (cases "i < k")
                case True thus ?thesis unfolding c_def using ht01 hdge by (by100 auto)
              next
                case False hence "i = k" using \<open>i < Suc k\<close> by (by100 simp)
                thus ?thesis unfolding c_def using ht01 by (by100 simp)
              qed
            qed
            have hcsum: "(\<Sum>i<Suc k. c i) = 1"
            proof -
              have "(\<Sum>i<Suc k. c i) = (\<Sum>i<k. c i) + c k" by (by100 simp)
              also have "(\<Sum>i<k. c i) = (\<Sum>i<k. (1 - t) * d i)" unfolding c_def by (by100 simp)
              also have "\<dots> = (1 - t) * (\<Sum>i<k. d i)"
                using sum_distrib_left[of "1-t" d "{..<k}", symmetric] by (by100 simp)
              also have "\<dots> = 1 - t" using hdsum by (by100 simp)
              finally show ?thesis unfolding c_def by (by100 simp)
            qed
            have hqx: "fst q = (\<Sum>i<Suc k. c i * vx i)"
            proof -
              have "fst q = (1-t) * px + t * vx k" using hq2 hpp by (by100 simp)
              also have "\<dots> = (1-t) * (\<Sum>i<k. d i * vx i) + t * vx k" unfolding hpx ..
              also have "(1-t) * (\<Sum>i<k. d i * vx i) = (\<Sum>i<k. (1-t) * (d i * vx i))"
                using sum_distrib_left[of "1-t" "\<lambda>i. d i * vx i" "{..<k}", symmetric]
                by (by100 simp)
              also have "\<dots> = (\<Sum>i<k. c i * vx i)" unfolding c_def
                by (rule sum.cong) (by100 simp)+
              finally show ?thesis unfolding c_def by (by100 simp)
            qed
            have hqy: "snd q = (\<Sum>i<Suc k. c i * vy i)"
            proof -
              have "snd q = (1-t) * py + t * vy k" using hq2 hpp by (by100 simp)
              also have "\<dots> = (1-t) * (\<Sum>i<k. d i * vy i) + t * vy k" unfolding hpy ..
              also have "(1-t) * (\<Sum>i<k. d i * vy i) = (\<Sum>i<k. (1-t) * (d i * vy i))"
                using sum_distrib_left[of "1-t" "\<lambda>i. d i * vy i" "{..<k}", symmetric]
                by (by100 simp)
              also have "\<dots> = (\<Sum>i<k. c i * vy i)" unfolding c_def
                by (rule sum.cong) (by100 simp)+
              finally show ?thesis unfolding c_def by (by100 simp)
            qed
            obtain qx qy where hqq: "q = (qx, qy)" by (cases q) (by100 blast)
            have "qx = (\<Sum>i<Suc k. c i * vx i)" using hqx hqq by (by100 simp)
            moreover have "qy = (\<Sum>i<Suc k. c i * vy i)" using hqy hqq by (by100 simp)
            moreover note hcge hcsum
            ultimately show "q \<in> Pk (Suc k)" unfolding Pk_def hqq
              by (by5000 auto)
          qed
        qed
        have hcont: "continuous_on (Pk k \<times> {0..1})
            (\<lambda>(p, t). ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))"
        proof -
          have hcont_eq: "(\<lambda>(p, t). ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))
              = (\<lambda>pt. ((1 - snd pt) * fst (fst pt) + snd pt * vx k,
                        (1 - snd pt) * snd (fst pt) + snd pt * vy k))"
            by (by100 auto)
          show ?thesis unfolding hcont_eq
            by (intro continuous_on_Pair continuous_on_add continuous_on_mult
                continuous_on_fst continuous_on_snd continuous_on_const
                continuous_on_diff) (by100 auto)+
        qed
        show "compact (Pk (Suc k))"
          unfolding hset by (rule compact_continuous_image[OF hcont hdom_compact])
      qed
      have "Pk n = P" unfolding Pk_def hP by (by100 simp)
      have "n \<ge> 1" using assms(2) by (by100 simp)
      hence "compact P" using hPk_compact \<open>Pk n = P\<close> by (by100 simp)
      thus ?thesis .
    qed
    thus ?thesis by (rule compact_R2_bridge)
  qed
  \<comment> \<open>Step 2: B^2 is Hausdorff.\<close>
  have hB2_haus: "is_hausdorff_on top1_B2 top1_B2_topology"
  proof -
    have "top1_B2 \<subseteq> (UNIV :: (real \<times> real) set)" by (by100 blast)
    thus ?thesis
      using Theorem_17_11 top1_R2_is_hausdorff
      unfolding top1_B2_topology_def by (by5000 blast)
  qed
  \<comment> \<open>Step 3: Construct the continuous bijection \<psi>: P \<rightarrow> B^2.\<close>
  \<comment> \<open>This uses the radial projection from an interior point of P.\<close>
  \<comment> \<open>Extract vertices for the radial projection construction.\<close>
  from assms(1)[unfolded top1_is_polygonal_region_on_def]
  obtain vx vy where
    hdist: "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)" and
    hgp: "\<forall>k<n. \<not> (\<exists>coeffs. (\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0)
                        \<and> coeffs k = 0 \<and> (\<Sum>i<n. coeffs i) = 1
                        \<and> vx k = (\<Sum>i<n. coeffs i * vx i)
                        \<and> vy k = (\<Sum>i<n. coeffs i * vy i))" and
    hP_eq: "P = {(x, y) | x y. \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
            \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
    by (elim conjE exE) (rule that, assumption+)
  \<comment> \<open>Centroid of vertices: p0 = (1/n * \<Sum> vx_i, 1/n * \<Sum> vy_i).\<close>
  define cx where "cx = (\<Sum>i<n. vx i) / real n"
  define cy where "cy = (\<Sum>i<n. vy i) / real n"
  \<comment> \<open>The centroid is an interior point of P (strict convex combination).\<close>
  have hc_in_P: "(cx, cy) \<in> P"
  proof -
    define c0 where "c0 = (\<lambda>i::nat. 1 / real n)"
    have hc0ge: "\<forall>i<n. c0 i \<ge> 0" unfolding c0_def using assms(2) by (by100 simp)
    have hc0sum: "(\<Sum>i<n. c0 i) = 1" unfolding c0_def using assms(2) by (by100 simp)
    have hc0x: "(\<Sum>i<n. c0 i * vx i) = cx" unfolding c0_def cx_def
      using assms(2) sum_divide_distrib[of vx "{..<n}" "real n", symmetric] by (by100 simp)
    have hc0y: "(\<Sum>i<n. c0 i * vy i) = cy" unfolding c0_def cy_def
      using assms(2) sum_divide_distrib[of vy "{..<n}" "real n", symmetric] by (by100 simp)
    show ?thesis unfolding hP_eq using hc0ge hc0sum hc0x hc0y by (by5000 auto)
  qed
  \<comment> \<open>Boundary of P = union of edges (segments between consecutive vertices).\<close>
  define BdP where "BdP = (\<Union>i<n.
      {((1-t) * vx i + t * vx ((i+1) mod n),
        (1-t) * vy i + t * vy ((i+1) mod n)) | t::real. 0 \<le> t \<and> t \<le> 1})"
  \<comment> \<open>Following Munkres §74 step by step:
     Step A: Define target polygon Q = regular n-gon inscribed in unit circle.
     Step B: Define boundary map h: Bd P \<rightarrow> Bd Q (piecewise linear on edges).
     Step C: Extend to interior: \<psi>((1-s)\<cdot>c + s\<cdot>x) = s \<cdot> h(x) for x \<in> Bd P, s \<in> [0,1].
     The map \<psi> is a continuous bijection P \<rightarrow> B^2 (actually onto Q which equals B^2
     for the regular n-gon case, where Q is itself the convex hull of points on S^1).

     Key simplification: we define \<psi> piecewise on each "cone" from the centroid
     to an edge, using barycentric coordinates. On cone_i = conv({c, v_i, v_{i+1}}),
     z = \<alpha>\<cdot>c + \<beta>\<cdot>v_i + \<gamma>\<cdot>v_{i+1} maps to \<beta>\<cdot>q_i + \<gamma>\<cdot>q_{i+1}
     where q_j = (cos(2\<pi>j/n), sin(2\<pi>j/n)).\<close>
  \<comment> \<open>Step A: Target vertices on S^1.\<close>
  define qx where "qx j = cos (2 * pi * real j / real n)" for j :: nat
  define qy where "qy j = sin (2 * pi * real j / real n)" for j :: nat
  \<comment> \<open>Step B: The map \<psi> is defined piecewise. For z \<in> P, find the "cone" containing z,
     i.e., find i such that z is in conv({centroid, v_i, v_{i+1 mod n}}).
     Write z = \<alpha>\<cdot>c + \<beta>\<cdot>v_i + \<gamma>\<cdot>v_{i+1} (barycentric coords within the cone).
     Map to \<beta>\<cdot>q_i + \<gamma>\<cdot>q_{i+1}.\<close>
  \<comment> \<open>For each i, define the affine map on cone_i.\<close>
  \<comment> \<open>Normalized cone map: sends (α,β,γ) to (1-α) · normalize(β·q_i + γ·q_{i+1}).
     This fills B^2 (not just the inscribed polygon).\<close>
  define cone_map where "cone_map i \<alpha> \<beta> \<gamma> = (
      let w = (\<beta> * qx i + \<gamma> * qx ((i+1) mod n), \<beta> * qy i + \<gamma> * qy ((i+1) mod n));
          r = sqrt (fst w ^ 2 + snd w ^ 2)
      in if r = 0 then (0, 0) else ((1 - \<alpha>) * fst w / r, (1 - \<alpha>) * snd w / r)
      )" for i :: nat and \<alpha> \<beta> \<gamma> :: real
  \<comment> \<open>For z \<in> P, we need to find the cone index i and barycentric coords.
     This is the decomposition z = \<alpha>\<cdot>(cx,cy) + \<beta>\<cdot>(vx i, vy i) + \<gamma>\<cdot>(vx(i+1),vy(i+1))
     with \<alpha>+\<beta>+\<gamma>=1, \<alpha>,\<beta>,\<gamma> \<ge> 0.
     The cone index i is determined by: z lies in the triangle (c, v_i, v_{i+1}).\<close>
  \<comment> \<open>Helper: check if z is in cone i (triangle c, v_i, v_{i+1}).\<close>
  define in_cone where "in_cone i z \<longleftrightarrow>
      (\<exists>\<alpha> \<beta> \<gamma>. \<alpha> \<ge> 0 \<and> \<beta> \<ge> 0 \<and> \<gamma> \<ge> 0 \<and> \<alpha> + \<beta> + \<gamma> = 1
        \<and> fst z = \<alpha> * cx + \<beta> * vx i + \<gamma> * vx ((i+1) mod n)
        \<and> snd z = \<alpha> * cy + \<beta> * vy i + \<gamma> * vy ((i+1) mod n))" for i :: nat and z :: "real \<times> real"
  \<comment> \<open>P = union of cones (triangulation from centroid).\<close>
  have hP_cones: "\<forall>z \<in> P. \<exists>i<n. in_cone i z"
  proof (intro ballI)
    fix z assume "z \<in> P"
    \<comment> \<open>Book: "P is the union of all line segments joining p and points of Bd P."
       For z = centroid: z is in any cone (take \<alpha> = 1, \<beta> = \<gamma> = 0).
       For z \<noteq> centroid: the ray from centroid through z hits Bd P at some edge i.
       Then z lies on the segment from centroid to that boundary point, hence in cone_i.\<close>
    show "\<exists>i<n. in_cone i z"
    proof (cases "z = (cx, cy)")
      case True
      \<comment> \<open>z = centroid: in cone 0 with \<alpha>=1, \<beta>=\<gamma>=0.\<close>
      have "0 < n" using assms(2) by (by100 linarith)
      moreover have "in_cone 0 (cx, cy)" unfolding in_cone_def
        by (rule exI[of _ 1], rule exI[of _ 0], rule exI[of _ 0]) (by100 simp)
      ultimately show ?thesis using True by (by100 blast)
    next
      case False
      \<comment> \<open>Following book: "P is the union of all line segments joining p and points of Bd P."
         The ray from c through z (extended) exits P at some boundary point b on edge i.
         Then z = (1-s)\<cdot>c + s\<cdot>b where s = |z-c|/|b-c| \<in> (0,1]. Since b is on edge i,
         b = (1-u)\<cdot>v_i + u\<cdot>v_{i+1}. So z = (1-s)\<cdot>c + s(1-u)\<cdot>v_i + su\<cdot>v_{i+1} \<in> cone_i.\<close>
      \<comment> \<open>Step 1: The ray from c through z is parameterized by t \<ge> 0:
         r(t) = (1-t)\<cdot>c + t\<cdot>z = c + t\<cdot>(z - c).
         At t=0: c \<in> P. At t=1: z \<in> P. For large t: outside P (bounded).\<close>
      \<comment> \<open>Step 2: Let t* = sup{t \<ge> 0 | r(t) \<in> P}. Since P bounded, t* < \<infinity>.
         Since t=1 gives z \<in> P, t* \<ge> 1. The point b = r(t*) is on Bd P.\<close>
      \<comment> \<open>Step 3: b \<in> Bd P means b is on some edge i: b = (1-u)\<cdot>v_i + u\<cdot>v_{i+1}.\<close>
      \<comment> \<open>Step 4: z = r(1) = (1 - 1/t*)\<cdot>c + (1/t*)\<cdot>b. Set s = 1/t* \<in> (0,1].
         Then z = (1-s)\<cdot>c + s\<cdot>((1-u)\<cdot>v_i + u\<cdot>v_{i+1})
                = (1-s)\<cdot>c + s(1-u)\<cdot>v_i + su\<cdot>v_{i+1} \<in> cone_i.\<close>
      obtain b i u where hb_bd: "b \<in> BdP" and hi: "i < n"
          and hu: "0 \<le> u" "u \<le> 1"
          and hb_edge: "b = ((1-u) * vx i + u * vx ((i+1) mod n),
                             (1-u) * vy i + u * vy ((i+1) mod n))"
          and "\<exists>s. 0 < s \<and> s \<le> 1
              \<and> fst z = (1-s) * cx + s * fst b
              \<and> snd z = (1-s) * cy + s * snd b"
      proof -
        \<comment> \<open>Algebraic approach: solve z - c = \<beta>'·(v_i - c) + \<gamma>'·(v_{i+1} - c) via
           2D cross product determinants. For the right i, \<beta>' \<ge> 0, \<gamma>' \<ge> 0, \<beta>'+\<gamma>' \<le> 1.

           Define cross(a,b) = fst a * snd b - snd a * fst b.
           For each i, the determinant D_i = cross(v_i - c, v_{i+1} - c).
           The solution is:
             \<beta>'_i = cross(z - c, v_{i+1} - c) / D_i
             \<gamma>'_i = cross(v_i - c, z - c) / D_i

           For a convex polygon with centroid c: D_i > 0 for all i (counterclockwise).
           The sector containing z-c has \<beta>' \<ge> 0 and \<gamma>' \<ge> 0.
           z \<in> P ensures \<beta>'+\<gamma>' \<le> 1 (not beyond boundary).\<close>
        \<comment> \<open>Use cross2\_centroid\_sum\_zero + cyclic\_sign\_change to find the sector.\<close>
        let ?dx = "fst z - cx" let ?dy = "snd z - cy"
        have hsum0: "(\<Sum>i<n. cross2 (vx i - cx, vy i - cy) (?dx, ?dy)) = 0"
          using cross2_centroid_sum_zero[of n vx vy ?dx ?dy] assms(2) cx_def cy_def
          by (by100 simp)
        have hne: "\<exists>i<n. cross2 (vx i - cx, vy i - cy) (?dx, ?dy) \<noteq> 0"
        proof (rule ccontr)
          assume "\<not> (\<exists>i<n. cross2 (vx i - cx, vy i - cy) (?dx, ?dy) \<noteq> 0)"
          hence hall0: "\<forall>i<n. cross2 (vx i - cx, vy i - cy) (?dx, ?dy) = 0" by (by100 blast)
          \<comment> \<open>cross2(a, d) = 0 means fst a * snd d = snd a * fst d (parallel).
             If this holds for two linearly independent a's, then d = 0.\<close>
          \<comment> \<open>Since vertices are in convex position (n \<ge> 3), not all v_i - c are parallel.
             So there exist i, j with cross2(v_i-c, v_j-c) \<noteq> 0.\<close>
          have "\<exists>i<n. \<exists>j<n. cross2 (vx i - cx, vy i - cy) (vx j - cx, vy j - cy) \<noteq> 0"
          proof (rule ccontr)
            assume "\<not> (\<exists>i<n. \<exists>j<n. cross2 (vx i - cx, vy i - cy) (vx j - cx, vy j - cy) \<noteq> 0)"
            hence hall_par: "\<forall>i<n. \<forall>j<n. cross2 (vx i - cx, vy i - cy) (vx j - cx, vy j - cy) = 0"
              by (by100 blast)
            \<comment> \<open>All v_i - c are parallel: cross2 = 0 means the 2D vectors are parallel.
               With n \<ge> 3 distinct vertices on a line through c, the general position
               assumption (hgp) is violated: the "middle" vertex is in the hull of others.\<close>
            \<comment> \<open>Specifically: vertices 0, 1, 2 are collinear (on the line through c).
               One of them is between the other two. Say v_k is between v_i, v_j.
               Then v_k = t*v_i + (1-t)*v_j for some t \<in> (0,1), contradicting hgp.\<close>
            \<comment> \<open>From hall\_par: all v_i - c are parallel. Since n \<ge> 3, vertices 0,1,2 are
               collinear. One of them is "between" the other two. That one is a convex
               combination of the other two with zero coefficients for all remaining vertices.
               This contradicts hgp (general position: no vertex in hull of others).\<close>
            \<comment> \<open>cross2(v_0-c, v_1-c) = 0 means v_0,c,v_1 are collinear.
               cross2(v_0-c, v_2-c) = 0 means v_0,c,v_2 are collinear.
               All three on the line through c parallel to v_0-c.
               The "middle" one is a strict convex combination of the other two.\<close>
            show False
            proof -
              have h0n: "(0::nat) < n" using assms(2) by (by100 linarith)
              have h1n: "(1::nat) < n" using assms(2) by (by100 linarith)
              have h2n: "(2::nat) < n" using assms(2) by (by100 linarith)
              \<comment> \<open>From cross2 = 0: v_j - c is scalar multiple of v_0 - c.\<close>
              have hc01: "cross2 (vx 0 - cx, vy 0 - cy) (vx 1 - cx, vy 1 - cy) = 0"
                using hall_par h0n h1n by (by100 blast)
              have hc02: "cross2 (vx 0 - cx, vy 0 - cy) (vx 2 - cx, vy 2 - cy) = 0"
                using hall_par h0n h2n by (by100 blast)
              \<comment> \<open>cross2(a,b) = 0 means a_x*b_y = a_y*b_x (collinear from origin).\<close>
              have hcol1: "(vx 0 - cx) * (vy 1 - cy) = (vy 0 - cy) * (vx 1 - cx)"
                using hc01 unfolding cross2_def by (by100 simp)
              have hcol2: "(vx 0 - cx) * (vy 2 - cy) = (vy 0 - cy) * (vx 2 - cx)"
                using hc02 unfolding cross2_def by (by100 simp)
              \<comment> \<open>Vertices 0,1,2 are on a line through c. The middle one (in terms of
                 parameter along the line) is a convex combination of the other two.
                 This contradicts hgp.\<close>
              \<comment> \<open>Formal proof: parameterize as v_i = c + t_i*(v_0 - c) where possible,
                 or handle case v_0 = c separately.\<close>
              \<comment> \<open>From hcol1, hcol2: v_0, v_1, v_2 are collinear (on a line through c).
                 The "middle" one is a convex combination of the other two.
                 This contradicts hgp for that vertex.\<close>
              \<comment> \<open>Specifically: cross2(v_1-v_0, v_2-v_0) = 0 from the collinearity conditions.
                 Then among the 3 distinct collinear points, one is between the other two.\<close>
              have hcross012: "cross2 (vx 1 - vx 0, vy 1 - vy 0) (vx 2 - vx 0, vy 2 - vy 0) = 0"
              proof -
                \<comment> \<open>Let a = vx0-cx, b = vy0-cy, a1 = vx1-cx, b1 = vy1-cy, etc.
                   From hcol1: a*b1 = b*a1. From hcol2: a*b2 = b*a2.
                   Want: (a1-a)*(b2-b) - (b1-b)*(a2-a) = 0.
                   = a1*b2 - a1*b - a*b2 + a*b - b1*a2 + b1*a + b*a2 - b*a
                   = a1*b2 - b1*a2 + a*(b - b2) + b*(a2 - a) + a1*(-b) + b1*a ... messy.
                   Direct: multiply hcol1 by (vx2-cx) and hcol2 by (vx1-cx), subtract.
                   (vx0-cx)*(vy1-cy)*(vx2-cx) = (vy0-cy)*(vx1-cx)*(vx2-cx)
                   (vx0-cx)*(vy2-cy)*(vx1-cx) = (vy0-cy)*(vx2-cx)*(vx1-cx)
                   Subtract: (vx0-cx)*[(vy1-cy)*(vx2-cx) - (vy2-cy)*(vx1-cx)] = 0.
                   So either vx0=cx or the bracket = 0.
                   The bracket = cross2(v1-c, v2-c). And cross2(v1-v0, v2-v0) relates to these.\<close>
                have hc12: "cross2 (vx 1 - cx, vy 1 - cy) (vx 2 - cx, vy 2 - cy) = 0"
                  using hall_par h1n h2n by (by100 blast)
                \<comment> \<open>cross2(v1-v0, v2-v0) = cross2(v1-c-(v0-c), v2-c-(v0-c))
                   = cross2(v1-c, v2-c) - cross2(v0-c, v2-c) - cross2(v1-c, v0-c) + cross2(v0-c, v0-c)
                   = 0 - 0 - (-0) + 0 = 0 (all pairwise cross2 = 0).\<close>
                have "cross2 (vx 1 - vx 0, vy 1 - vy 0) (vx 2 - vx 0, vy 2 - vy 0)
                    = cross2 (vx 1 - cx - (vx 0 - cx), vy 1 - cy - (vy 0 - cy))
                             (vx 2 - cx - (vx 0 - cx), vy 2 - cy - (vy 0 - cy))"
                  by (by100 simp)
                also have "\<dots> = cross2 (vx 1 - cx, vy 1 - cy) (vx 2 - cx, vy 2 - cy)
                    - cross2 (vx 0 - cx, vy 0 - cy) (vx 2 - cx, vy 2 - cy)
                    - cross2 (vx 1 - cx, vy 1 - cy) (vx 0 - cx, vy 0 - cy)
                    + cross2 (vx 0 - cx, vy 0 - cy) (vx 0 - cx, vy 0 - cy)"
                  unfolding cross2_def by (simp add: algebra_simps)
                also have "cross2 (vx 0 - cx, vy 0 - cy) (vx 2 - cx, vy 2 - cy) = 0"
                  using hall_par h0n h2n by (by100 blast)
                also have "cross2 (vx 1 - cx, vy 1 - cy) (vx 0 - cx, vy 0 - cy) = 0"
                  using hall_par h1n h0n by (by100 blast)
                also have "cross2 (vx 0 - cx, vy 0 - cy) (vx 0 - cx, vy 0 - cy) = 0"
                  unfolding cross2_def by (by100 simp)
                finally show ?thesis using hc12 by (by100 simp)
              qed
              \<comment> \<open>Three distinct collinear points: middle is in hull of endpoints.\<close>
              \<comment> \<open>This contradicts hgp for the middle vertex.\<close>
              \<comment> \<open>3 collinear distinct points: one is between the other two.
                 Use cross2 = 0 meaning (vx1-vx0)*(vy2-vy0) = (vy1-vy0)*(vx2-vx0).
                 If vx0 \<noteq> vx1: parameter t = (vx2-vx0)/(vx1-vx0) satisfies
                   v_2 = (1-t)*v_0 + t*v_1. If 0<t<1, v_2 is between v_0 and v_1.
                 If vx0=vx1: then (vy1-vy0)*(vx2-vx0) = 0. If vx0\<noteq>vx2: swap roles.
                   If vx0=vx1=vx2: use y-coordinates similarly.\<close>
              \<comment> \<open>From hcross012: (vx1-vx0)*(vy2-vy0) = (vy1-vy0)*(vx2-vx0).\<close>
              have hcol_eq: "(vx 1 - vx 0)*(vy 2 - vy 0) = (vy 1 - vy 0)*(vx 2 - vx 0)"
                using hcross012 unfolding cross2_def by (by100 simp)
              have h01_ne: "(vx 0, vy 0) \<noteq> (vx 1, vy 1)"
                using hdist[rule_format, OF h0n h1n] by (by100 simp)
              have h02_ne: "(vx 0, vy 0) \<noteq> (vx 2, vy 2)"
                using hdist[rule_format, OF h0n h2n] by (by100 simp)
              have h12_ne: "(vx 1, vy 1) \<noteq> (vx 2, vy 2)"
                using hdist[rule_format, OF h1n h2n] by (by100 simp)
              \<comment> \<open>v_0, v_1, v_2 are 3 distinct collinear points. One is between the other two.
                 The between one is a convex combination, contradicting hgp.
                 This is a fundamental fact about collinear points in R; the formal proof
                 requires real arithmetic and case analysis on the ordering.\<close>
              \<comment> \<open>Strategy: show v_1 is a convex combination of v_0 and v_2 (or circular permutation).
                 From hcol\_eq + distinctness, we get the parameterization.\<close>
              \<comment> \<open>First show vx0 \<noteq> vx2 or vy0 \<noteq> vy2 (from h02\_ne).\<close>
              show False
              proof (cases "vx 0 \<noteq> vx 2")
                case True
                \<comment> \<open>t = (vx1-vx0)/(vx2-vx0). Then v1 = (1-t)*v0 + t*v2.\<close>
                let ?t = "(vx 1 - vx 0) / (vx 2 - vx 0)"
                have ht_fact: "?t * (vx 2 - vx 0) = vx 1 - vx 0"
                  using True by (by100 simp)
                \<comment> \<open>Introduce auxiliary real t' to avoid division in arithmetic.\<close>
                obtain t' where ht'_def: "t' = ?t" and ht'_fact: "t' * (vx 2 - vx 0) = vx 1 - vx 0"
                  using ht_fact by (by100 blast)
                have hvx1_eq: "vx 1 = (1 - ?t) * vx 0 + ?t * vx 2"
                proof -
                  have "vx 1 = vx 0 + t' * (vx 2 - vx 0)" using ht'_fact by (by100 linarith)
                  also have "\<dots> = (1 - t') * vx 0 + t' * vx 2"
                    by (simp add: right_diff_distrib left_diff_distrib algebra_simps)
                  finally show ?thesis unfolding ht'_def .
                qed
                have hvy1_eq: "vy 1 = (1 - ?t) * vy 0 + ?t * vy 2"
                proof -
                  have "t' * (vy 2 - vy 0) = vy 1 - vy 0"
                  proof -
                    from hcol_eq have h_eq: "(vx 1 - vx 0) * (vy 2 - vy 0) = (vy 1 - vy 0) * (vx 2 - vx 0)" .
                    \<comment> \<open>Substitute vx1 - vx0 = t'*(vx2-vx0) into h\_eq:
                       t'*(vx2-vx0)*(vy2-vy0) = (vy1-vy0)*(vx2-vx0).
                       Cancel (vx2-vx0) \<noteq> 0: t'*(vy2-vy0) = vy1-vy0.\<close>
                    have "(vx 1 - vx 0) = t' * (vx 2 - vx 0)" using ht'_fact True by (by100 simp)
                    hence "t' * (vx 2 - vx 0) * (vy 2 - vy 0) = (vy 1 - vy 0) * (vx 2 - vx 0)"
                      using h_eq by (by100 simp)
                    hence "t' * (vy 2 - vy 0) * (vx 2 - vx 0) = (vy 1 - vy 0) * (vx 2 - vx 0)"
                      by (simp add: mult.commute mult.left_commute)
                    thus ?thesis using True by (by100 simp)
                  qed
                  hence "vy 1 = vy 0 + t' * (vy 2 - vy 0)" by (by100 linarith)
                  also have "\<dots> = (1 - t') * vy 0 + t' * vy 2"
                    by (simp add: right_diff_distrib left_diff_distrib algebra_simps)
                  finally show ?thesis unfolding ht'_def .
                qed
                \<comment> \<open>?t \<noteq> 0 (v0 \<noteq> v1 means vx0\<noteq>vx1 or vy0\<noteq>vy1 but if all same x...)\<close>
                have ht_ne0: "?t \<noteq> 0" using h01_ne hvx1_eq hvy1_eq by (by100 force)
                have ht_ne1: "?t \<noteq> 1" using h12_ne hvx1_eq hvy1_eq by (by100 force)
                \<comment> \<open>Now we know v_1 = (1-t)*v_0 + t*v_2 with t \<noteq> 0 and t \<noteq> 1.
                   If 0 < t < 1: v_1 is in hull of others → hgp contradiction for k=1.
                   If t < 0 or t > 1: v_0 or v_2 is the middle point.\<close>
                \<comment> \<open>Case analysis on t: 0<t<1 means v_1 between v_0 and v_2.
                   t\<le>0 or t\<ge>1 handled by symmetry (v_0 or v_2 is middle).\<close>
                show False
                proof (cases "0 < ?t \<and> ?t < 1")
                  case True
                  \<comment> \<open>v_1 = (1-t)*v_0 + t*v_2. Construct coefficients for hgp contradiction.\<close>
                  have hgp1: "\<not> (\<exists>coeffs. (\<forall>i<n. i \<noteq> 1 \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs 1 = 0
                        \<and> (\<Sum>i<n. coeffs i) = 1
                        \<and> vx 1 = (\<Sum>i<n. coeffs i * vx i) \<and> vy 1 = (\<Sum>i<n. coeffs i * vy i))"
                    using hgp h1n by (by100 blast)
                  define coeffs where "coeffs = (\<lambda>i::nat. if i = 0 then 1 - ?t
                      else if i = 2 then ?t else 0::real)"
                  have hnn: "\<forall>i<n. i \<noteq> 1 \<longrightarrow> coeffs i \<ge> 0"
                    using True unfolding coeffs_def by (by100 auto)
                  have hc1: "coeffs 1 = 0" unfolding coeffs_def by (by100 simp)
                  have hcoeffs_rest: "\<And>i. i \<ge> 3 \<Longrightarrow> i < n \<Longrightarrow> coeffs i = 0"
                    unfolding coeffs_def by (by100 simp)
                  have hcoeffs_rest_mul: "\<And>f. (\<Sum>i\<in>{3..<n}. coeffs i * f i) = 0"
                    apply (rule sum.neutral) using hcoeffs_rest by (by100 force)
                  have hcoeffs_rest_sum: "(\<Sum>i\<in>{3..<n}. coeffs i) = 0"
                    apply (rule sum.neutral) using hcoeffs_rest by (by100 force)
                  have hsplit: "{..<n} = {0,1,2} \<union> {3..<n}" using assms(2) by (by100 auto)
                  have hcsum: "(\<Sum>i<n. coeffs i) = 1"
                  proof -
                    have "(\<Sum>i<n. coeffs i) = (\<Sum>i\<in>{0,1,2}. coeffs i) + (\<Sum>i\<in>{3..<n}. coeffs i)"
                      using hsplit by (simp add: sum.union_disjoint)
                    thus ?thesis using hcoeffs_rest_sum unfolding coeffs_def by (by100 simp)
                  qed
                  have hcvx: "vx 1 = (\<Sum>i<n. coeffs i * vx i)"
                  proof -
                    have "(\<Sum>i<n. coeffs i * vx i) = (\<Sum>i\<in>{0,1,2}. coeffs i * vx i) + (\<Sum>i\<in>{3..<n}. coeffs i * vx i)"
                      using hsplit by (simp add: sum.union_disjoint)
                    thus ?thesis using hcoeffs_rest_mul[of vx] hvx1_eq unfolding coeffs_def by (by100 simp)
                  qed
                  have hcvy: "vy 1 = (\<Sum>i<n. coeffs i * vy i)"
                  proof -
                    have "(\<Sum>i<n. coeffs i * vy i) = (\<Sum>i\<in>{0,1,2}. coeffs i * vy i) + (\<Sum>i\<in>{3..<n}. coeffs i * vy i)"
                      using hsplit by (simp add: sum.union_disjoint)
                    thus ?thesis using hcoeffs_rest_mul[of vy] hvy1_eq unfolding coeffs_def by (by100 simp)
                  qed
                  have "\<exists>coeffs. (\<forall>i<n. i \<noteq> 1 \<longrightarrow> 0 \<le> coeffs i) \<and> coeffs 1 = 0
                      \<and> (\<Sum>i<n. coeffs i) = 1 \<and> vx 1 = (\<Sum>i<n. coeffs i * vx i)
                      \<and> vy 1 = (\<Sum>i<n. coeffs i * vy i)"
                    using hnn hc1 hcsum hcvx hcvy by (by100 blast)
                  thus False using hgp1 by (by100 blast)
                next
                  case False
                  hence "?t < 0 \<or> ?t > 1" using ht_ne0 ht_ne1 by (by100 linarith)
                  thus False
                  proof
                    assume "?t < 0"
                    \<comment> \<open>v_0 = (1/(1-t))*v_1 + (-t/(1-t))*v_2, a convex combo since -t>0, 1/(1-t)>0.\<close>
                    \<comment> \<open>This contradicts hgp for vertex 0.\<close>
                    show False using hvx1_eq hvy1_eq \<open>?t < 0\<close> hgp h0n h1n h2n assms(2)
                      sorry \<comment> \<open>Symmetric to case 0<t<1 with vertex 0 as middle point.\<close>
                  next
                    assume "?t > 1"
                    \<comment> \<open>v_2 = (1/t)*v_1 + (1-1/t)*v_0, a convex combo since 1/t \<in> (0,1).\<close>
                    show False using hvx1_eq hvy1_eq \<open>?t > 1\<close> hgp h0n h1n h2n assms(2)
                      sorry \<comment> \<open>Symmetric to case 0<t<1 with vertex 2 as middle point.\<close>
                  qed
                qed
              next
                case False
                hence hvy_ne: "vy 0 \<noteq> vy 2" using h02_ne by (by100 force)
                \<comment> \<open>Symmetric to the vx0\<noteq>vx2 case: use t = (vy1-vy0)/(vy2-vy0).\<close>
                show False using hcol_eq hvy_ne hdist h0n h1n h2n hgp h01_ne h02_ne h12_ne assms(2)
                  sorry \<comment> \<open>Identical proof structure to the True case but with vy parameterization.\<close>
              qed
            qed
          qed
          then obtain i' j' where hi': "i' < n" and hj': "j' < n"
              and hdet: "cross2 (vx i' - cx, vy i' - cy) (vx j' - cx, vy j' - cy) \<noteq> 0"
            by (by100 blast)
          \<comment> \<open>From hall0: (vx_i-cx)*?dy = (vy_i-cy)*?dx for all i.
             From hdet: the matrix [v_i'-c | v_j'-c] is invertible.
             The system (vx_i'-cx)*?dy = (vy_i'-cy)*?dx and
                        (vx_j'-cx)*?dy = (vy_j'-cy)*?dx
             with non-singular coefficient matrix forces ?dx = ?dy = 0.\<close>
          have h0i: "(vx i' - cx) * ?dy - (vy i' - cy) * ?dx = 0"
            using hall0[rule_format, OF hi'] unfolding cross2_def by (by100 simp)
          have h0j: "(vx j' - cx) * ?dy - (vy j' - cy) * ?dx = 0"
            using hall0[rule_format, OF hj'] unfolding cross2_def by (by100 simp)
          \<comment> \<open>Solve: if det \<noteq> 0 and both equations hold, then ?dx = ?dy = 0.\<close>
          have "?dx = 0 \<and> ?dy = 0"
          proof -
            \<comment> \<open>From h0i: (vx_i'-cx)*dy - (vy_i'-cy)*dx = 0.
               From h0j: (vx_j'-cx)*dy - (vy_j'-cy)*dx = 0.
               Multiply first by (vx_j'-cx), second by (vx_i'-cx), subtract:
               cross2(v_i'-c, v_j'-c) * dy = 0. Since cross2 \<noteq> 0, dy = 0.
               Similarly dx = 0.\<close>
            \<comment> \<open>Cramer's rule: multiply h0i by (vx_j'-cx) and h0j by (vx_i'-cx), subtract.\<close>
            let ?D = "(vx i' - cx) * (vy j' - cy) - (vy i' - cy) * (vx j' - cx)"
            have hdet': "?D \<noteq> 0"
              using hdet unfolding cross2_def by (by100 simp)
            \<comment> \<open>(vx_j'-cx) * h0i - (vx_i'-cx) * h0j gives ?D * ?dy = 0.\<close>
            \<comment> \<open>From h0i: (vx_i'-cx)*dy = (vy_i'-cy)*dx.
               From h0j: (vx_j'-cx)*dy = (vy_j'-cy)*dx.
               Multiply h0i by (vy_j'-cy): (vx_i'-cx)*(vy_j'-cy)*dy = (vy_i'-cy)*(vy_j'-cy)*dx
               Multiply h0j by (vy_i'-cy): (vx_j'-cx)*(vy_i'-cy)*dy = (vy_j'-cy)*(vy_i'-cy)*dx
               Subtract: ((vx_i'-cx)*(vy_j'-cy) - (vx_j'-cx)*(vy_i'-cy))*dy = 0
               i.e. D*dy = 0.\<close>
            have hi_eq: "(vx i' - cx) * ?dy = (vy i' - cy) * ?dx" using h0i by (by100 linarith)
            have hj_eq: "(vx j' - cx) * ?dy = (vy j' - cy) * ?dx" using h0j by (by100 linarith)
            have hdy_eq: "?D * ?dy = 0"
            proof -
              let ?a = "vx i' - cx" let ?b = "vy i' - cy"
              let ?c = "vx j' - cx" let ?d = "vy j' - cy"
              \<comment> \<open>From hi_eq: ?a*?dy = ?b*?dx. Multiply by ?d: ?a*?d*?dy = ?b*?d*?dx.\<close>
              have "?a * ?d * ?dy = ?b * ?dx * ?d"
                using hi_eq by (by100 simp)
              hence h1: "?a * ?d * ?dy = ?b * ?d * ?dx"
                by (simp add: mult.commute mult.left_commute)
              \<comment> \<open>From hj_eq: ?c*?dy = ?d*?dx. Multiply by ?b: ?b*?c*?dy = ?b*?d*?dx.\<close>
              have "?b * (?c * ?dy) = ?b * (?d * ?dx)"
                using hj_eq by (by100 simp)
              hence h2: "?b * ?c * ?dy = ?b * ?d * ?dx"
                by (simp add: mult.assoc)
              \<comment> \<open>Subtract: (?a*?d - ?b*?c)*?dy = ?b*?d*?dx - ?b*?d*?dx = 0.\<close>
              from h1 h2 have h3: "?a * ?d * ?dy - ?b * ?c * ?dy = 0" by (by100 linarith)
              have "?D * ?dy = ?a * ?d * ?dy - ?b * ?c * ?dy"
                by (simp add: algebra_simps)
              thus ?thesis using h3 by (by100 simp)
            qed
            have hdy0: "?dy = 0" using hdy_eq hdet' by (by100 simp)
            have hdx0: "?dx = 0"
            proof -
              from hi_eq hdy0 have h1: "(vy i' - cy) * ?dx = 0" by (by100 simp)
              from hj_eq hdy0 have h2: "(vy j' - cy) * ?dx = 0" by (by100 simp)
              have "vy i' - cy \<noteq> 0 \<or> vy j' - cy \<noteq> 0"
              proof (rule ccontr)
                assume "\<not> (vy i' - cy \<noteq> 0 \<or> vy j' - cy \<noteq> 0)"
                hence "vy i' = cy" "vy j' = cy" by (by100 simp)+
                hence "?D = 0" by (simp add: algebra_simps)
                thus False using hdet' by (by100 blast)
              qed
              thus "?dx = 0" using h1 h2 by (by100 force)
            qed
            show ?thesis using hdy0 hdx0 by (by100 auto)
          qed
          hence "z = (cx, cy)" by (by100 auto)
          thus False using False by (by100 simp)
        qed
        have hn2: "n \<ge> 2" using assms(2) by (by100 linarith)
        from cyclic_sign_change[OF hn2 hsum0 hne]
        obtain i where hi: "i < n"
            and hpos: "cross2 (vx i - cx, vy i - cy) (?dx, ?dy) \<ge> 0"
            and hneg: "cross2 (vx ((i+1) mod n) - cx, vy ((i+1) mod n) - cy) (?dx, ?dy) \<le> 0"
          by (by100 blast)
        \<comment> \<open>The sign conditions mean z-c is in the sector between v_i-c and v_{i+1}-c.
           Solve the 2\<times>2 linear system for barycentric coordinates.\<close>
        let ?vi1 = "(i+1) mod n"
        let ?D = "cross2 (vx i - cx, vy i - cy) (vx ?vi1 - cx, vy ?vi1 - cy)"
        \<comment> \<open>D > 0 for convex polygon with counterclockwise vertices from centroid.\<close>
        have hD_ne: "?D \<noteq> 0"
          sorry \<comment> \<open>Convex position: adjacent vertices and centroid form non-degenerate triangle.\<close>
        \<comment> \<open>\<beta>' = cross2(z-c, v_{i+1}-c) / D, \<gamma>' = cross2(v_i-c, z-c) / D.\<close>
        define \<beta>' where "\<beta>' = cross2 (fst z - cx, snd z - cy) (vx ?vi1 - cx, vy ?vi1 - cy) / ?D"
        define \<gamma>' where "\<gamma>' = cross2 (vx i - cx, vy i - cy) (fst z - cx, snd z - cy) / ?D"
        \<comment> \<open>\<beta>' \<ge> 0: cross2(z-c, v_{i+1}-c) = -cross2(v_{i+1}-c, z-c) \<ge> 0 from hneg.
           \<gamma>' \<ge> 0: cross2(v_i-c, z-c) \<ge> 0 from hpos. Both divided by D > 0.\<close>
        have hnum_\<beta>: "cross2 (fst z - cx, snd z - cy) (vx ?vi1 - cx, vy ?vi1 - cy) \<ge> 0"
        proof -
          have "cross2 (vx ?vi1 - cx, vy ?vi1 - cy) (?dx, ?dy) \<le> 0" using hneg .
          hence "- cross2 (fst z - cx, snd z - cy) (vx ?vi1 - cx, vy ?vi1 - cy) \<le> 0"
            unfolding cross2_def by (simp add: algebra_simps)
          thus ?thesis by (by100 linarith)
        qed
        have hnum_\<gamma>: "cross2 (vx i - cx, vy i - cy) (fst z - cx, snd z - cy) \<ge> 0"
          using hpos .
        \<comment> \<open>Derive D > 0: numerator sum = num_\<beta> + num_\<gamma> > 0 (since z \<noteq> c, not both 0).
           \<beta>'+\<gamma>' = (num_\<beta> + num_\<gamma>)/D must be > 0 (from z \<noteq> c via Cramer).
           Since numerator sum \<ge> 0 and must give positive quotient, D > 0.\<close>
        have hnum_sum_pos: "cross2 (fst z - cx, snd z - cy) (vx ?vi1 - cx, vy ?vi1 - cy) +
            cross2 (vx i - cx, vy i - cy) (fst z - cx, snd z - cy) > 0"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          hence "cross2 (fst z - cx, snd z - cy) (vx ?vi1 - cx, vy ?vi1 - cy) = 0
              \<and> cross2 (vx i - cx, vy i - cy) (fst z - cx, snd z - cy) = 0"
            using hnum_\<beta> hnum_\<gamma> by (by100 linarith)
          \<comment> \<open>Both numerators 0 means z-c = 0 (by Cramer with D \<noteq> 0).\<close>
          hence h_both0: "cross2 (fst z - cx, snd z - cy) (vx ?vi1 - cx, vy ?vi1 - cy) = 0"
              "cross2 (vx i - cx, vy i - cy) (fst z - cx, snd z - cy) = 0"
            by (by100 blast)+
          hence "fst z - cx = 0 \<and> snd z - cy = 0"
          proof -
            \<comment> \<open>Cramer: h_both0 gives (fst z-cx)*(vy_{i+1}-cy) = (snd z-cy)*(vx_{i+1}-cx)
               and (vx_i-cx)*(snd z-cy) = (vy_i-cy)*(fst z-cx).
               With D \<noteq> 0, same argument as in hne proof.\<close>
            have h_eq1: "(fst z - cx) * (vy ?vi1 - cy) - (snd z - cy) * (vx ?vi1 - cx) = 0"
              using h_both0(1) unfolding cross2_def by (by100 simp)
            have h_eq2: "(vx i - cx) * (snd z - cy) - (vy i - cy) * (fst z - cx) = 0"
              using h_both0(2) unfolding cross2_def by (by100 simp)
            \<comment> \<open>Same Cramer derivation: D*(snd z-cy) = 0, D*(fst z-cx) = 0.\<close>
            have "?D * (snd z - cy) = 0"
            proof -
              let ?a = "vx i - cx" let ?b = "vy i - cy"
              let ?c = "vx ?vi1 - cx" let ?d = "vy ?vi1 - cy"
              have h_i: "?a * (snd z - cy) = ?b * (fst z - cx)" using h_eq2 by (by100 linarith)
              have h_i1: "(fst z - cx) * ?d = (snd z - cy) * ?c" using h_eq1 by (by100 linarith)
              have "?a * ?d * (snd z - cy) = ?b * (fst z - cx) * ?d"
                using h_i by (by100 simp)
              also have "\<dots> = ?b * (snd z - cy) * ?c"
                using h_i1 by (simp add: mult.commute mult.left_commute)
              finally have "?a * ?d * (snd z - cy) = ?b * ?c * (snd z - cy)"
                by (simp add: mult.commute mult.left_commute)
              hence "?a * ?d * (snd z - cy) - ?b * ?c * (snd z - cy) = 0"
                by (by100 linarith)
              hence "(?a * ?d - ?b * ?c) * (snd z - cy) = 0"
                by (simp add: algebra_simps)
              moreover have "?D = ?a * ?d - ?b * ?c" unfolding cross2_def by (by100 simp)
              ultimately show ?thesis by (by100 simp)
            qed
            hence "snd z - cy = 0" using hD_ne by (by100 simp)
            moreover hence "fst z - cx = 0" using h_eq2 hD_ne
              unfolding cross2_def
            proof -
              from h_eq2 \<open>snd z - cy = 0\<close>
              have "(vy i - cy) * (fst z - cx) = 0" by (by100 simp)
              moreover from h_eq1 \<open>snd z - cy = 0\<close>
              have "(vy ?vi1 - cy) * (fst z - cx) = 0" by (simp add: algebra_simps)
              moreover have "vy i - cy \<noteq> 0 \<or> vy ?vi1 - cy \<noteq> 0"
              proof (rule ccontr)
                assume "\<not> (vy i - cy \<noteq> 0 \<or> vy ?vi1 - cy \<noteq> 0)"
                hence "vy i = cy" "vy ?vi1 = cy" by (by100 simp)+
                hence "?D = 0" unfolding cross2_def by (simp add: algebra_simps)
                thus False using hD_ne by (by100 blast)
              qed
              ultimately show "fst z - cx = 0" by (by100 force)
            qed
            ultimately show ?thesis by (by100 blast)
          qed
          hence "z = (cx, cy)" by (by100 auto)
          thus False using False by (by100 simp)
        qed
        have hD_pos: "?D > 0"
          sorry \<comment> \<open>Convex polygon: cross2(v_i-c, v_{i+1}-c) > 0 for all adjacent pairs.
             This is equivalent to the polygon having positive (CCW) orientation from c.
             Proof requires the convex position assumption (hgp) + centroid is interior.\<close>
        have h\<beta>_nn: "\<beta>' \<ge> 0" unfolding \<beta>'_def
          using hnum_\<beta> hD_pos by (by100 simp)
        have h\<gamma>_nn: "\<gamma>' \<ge> 0" unfolding \<gamma>'_def
          using hnum_\<gamma> hD_pos by (by100 simp)
        \<comment> \<open>z - c = \<beta>'*(v_i - c) + \<gamma>'*(v_{i+1} - c): by definition of \<beta>', \<gamma>' via Cramer.\<close>
        have hzc_x: "fst z - cx = \<beta>' * (vx i - cx) + \<gamma>' * (vx ?vi1 - cx)"
        proof -
          \<comment> \<open>Cramer: \<beta>'*(vx_i-cx) + \<gamma>'*(vx_{i+1}-cx)
             = (cross2(z-c,v_{i+1}-c)*(vx_i-cx) + cross2(v_i-c,z-c)*(vx_{i+1}-cx)) / D
             = ((fst z-cx)*(vy_{i+1}-cy) - (snd z-cy)*(vx_{i+1}-cx))*(vx_i-cx) / D
             + ((vx_i-cx)*(snd z-cy) - (vy_i-cy)*(fst z-cx))*(vx_{i+1}-cx) / D
             Numerator = (fst z-cx) * [(vy_{i+1}-cy)*(vx_i-cx) - (vy_i-cy)*(vx_{i+1}-cx)]
                       + (snd z-cy) * [-(vx_{i+1}-cx)*(vx_i-cx) + (vx_i-cx)*(vx_{i+1}-cx)]
                       = (fst z-cx) * D + 0 = (fst z-cx) * D.
             So the whole expression = (fst z-cx) * D / D = fst z - cx.\<close>
          have "\<beta>' * (vx i - cx) + \<gamma>' * (vx ?vi1 - cx) =
              (cross2 (fst z - cx, snd z - cy) (vx ?vi1 - cx, vy ?vi1 - cy) * (vx i - cx) +
               cross2 (vx i - cx, vy i - cy) (fst z - cx, snd z - cy) * (vx ?vi1 - cx)) / ?D"
            unfolding \<beta>'_def \<gamma>'_def by (simp add: add_divide_distrib)
          also have "\<dots> = (fst z - cx) * ?D / ?D"
            unfolding cross2_def by (simp add: algebra_simps)
          also have "\<dots> = fst z - cx" using hD_ne by (by100 simp)
          finally show ?thesis by (by100 simp)
        qed
        have hzc_y: "snd z - cy = \<beta>' * (vy i - cy) + \<gamma>' * (vy ?vi1 - cy)"
        proof -
          have "\<beta>' * (vy i - cy) + \<gamma>' * (vy ?vi1 - cy) =
              (cross2 (fst z - cx, snd z - cy) (vx ?vi1 - cx, vy ?vi1 - cy) * (vy i - cy) +
               cross2 (vx i - cx, vy i - cy) (fst z - cx, snd z - cy) * (vy ?vi1 - cy)) / ?D"
            unfolding \<beta>'_def \<gamma>'_def by (simp add: add_divide_distrib)
          also have "\<dots> = (snd z - cy) * ?D / ?D"
            unfolding cross2_def by (simp add: algebra_simps)
          also have "\<dots> = snd z - cy" using hD_ne by (by100 simp)
          finally show ?thesis by (by100 simp)
        qed
        \<comment> \<open>\<beta>' + \<gamma>' \<le> 1: since z \<in> P (convex hull) and c is the centroid.\<close>
        have hsum_le: "\<beta>' + \<gamma>' \<le> 1" sorry
        \<comment> \<open>z \<noteq> c means \<beta>' + \<gamma>' > 0.\<close>
        have hsum_pos: "\<beta>' + \<gamma>' > 0"
        proof (rule ccontr)
          assume "\<not> (\<beta>' + \<gamma>' > 0)"
          hence "\<beta>' + \<gamma>' \<le> 0" by (by100 simp)
          hence "\<beta>' = 0" "\<gamma>' = 0" using h\<beta>_nn h\<gamma>_nn by (by100 linarith)+
          hence "fst z - cx = 0" "snd z - cy = 0" using hzc_x hzc_y by (by100 simp)+
          hence "z = (cx, cy)" by (by100 auto)
          thus False using False by (by100 simp)
        qed
        \<comment> \<open>Now set: s = \<beta>' + \<gamma>', u = \<gamma>' / (\<beta>' + \<gamma>'), b = (1-u)*v_i + u*v_{i+1}.\<close>
        define s where "s = \<beta>' + \<gamma>'"
        define u where "u = \<gamma>' / s"
        define b where "b = ((1-u) * vx i + u * vx ?vi1, (1-u) * vy i + u * vy ?vi1)"
        \<comment> \<open>Verify all conditions.\<close>
        have hs: "0 < s" "s \<le> 1" using hsum_pos hsum_le unfolding s_def by (by100 simp)+
        have hu: "0 \<le> u" "u \<le> 1"
        proof -
          show "0 \<le> u" unfolding u_def s_def using h\<gamma>_nn hsum_pos by (by100 simp)
          show "u \<le> 1" unfolding u_def s_def
            using h\<beta>_nn h\<gamma>_nn hsum_pos divide_le_eq_1 by (by5000 simp)
        qed
        have hb_in: "b \<in> BdP"
          unfolding BdP_def b_def using hi hu by (by5000 force)
        \<comment> \<open>Key: s * fst b = s * ((1-u)*vx_i + u*vx_{i+1}) = s*(1-\<gamma>'/s)*vx_i + s*(\<gamma>'/s)*vx_{i+1}
             = (s - \<gamma>')*vx_i + \<gamma>'*vx_{i+1} = \<beta>'*vx_i + \<gamma>'*vx_{i+1}.\<close>
        have hs1u: "s * (1 - u) = \<beta>'" unfolding u_def s_def using hsum_pos
          by (simp add: field_simps)
        have hsu: "s * u = \<gamma>'" unfolding u_def s_def using hsum_pos by (by100 simp)
        have hs_fst_b: "s * fst b = \<beta>' * vx i + \<gamma>' * vx ?vi1"
        proof -
          have "s * fst b = s * (1 - u) * vx i + s * u * vx ?vi1"
            unfolding b_def by (simp add: algebra_simps)
          thus ?thesis using hs1u hsu by (by100 simp)
        qed
        have hs_snd_b: "s * snd b = \<beta>' * vy i + \<gamma>' * vy ?vi1"
        proof -
          have "s * snd b = s * (1 - u) * vy i + s * u * vy ?vi1"
            unfolding b_def by (simp add: algebra_simps)
          thus ?thesis using hs1u hsu by (by100 simp)
        qed
        have hzx_eq: "fst z = (1-s) * cx + s * fst b"
        proof -
          have "(1-s) * cx + s * fst b = cx - s * cx + (\<beta>' * vx i + \<gamma>' * vx ?vi1)"
            using hs_fst_b by (simp add: algebra_simps)
          also have "\<dots> = cx + \<beta>' * (vx i - cx) + \<gamma>' * (vx ?vi1 - cx)"
            unfolding s_def by (simp add: algebra_simps)
          also have "\<dots> = cx + (fst z - cx)" using hzc_x by (by100 simp)
          finally show ?thesis by (by100 simp)
        qed
        have hzy_eq: "snd z = (1-s) * cy + s * snd b"
        proof -
          have "(1-s) * cy + s * snd b = cy - s * cy + (\<beta>' * vy i + \<gamma>' * vy ?vi1)"
            using hs_snd_b by (simp add: algebra_simps)
          also have "\<dots> = cy + \<beta>' * (vy i - cy) + \<gamma>' * (vy ?vi1 - cy)"
            unfolding s_def by (simp add: algebra_simps)
          also have "\<dots> = cy + (snd z - cy)" using hzc_y by (by100 simp)
          finally show ?thesis by (by100 simp)
        qed
        show ?thesis
        proof (rule that[of b i u])
          show "b \<in> BdP" by (rule hb_in)
          show "i < n" by (rule hi)
          show "0 \<le> u" by (rule hu(1))
          show "u \<le> 1" by (rule hu(2))
          show "b = ((1 - u) * vx i + u * vx ((i + 1) mod n),
                     (1 - u) * vy i + u * vy ((i + 1) mod n))"
            unfolding b_def by (by100 simp)
          show "\<exists>s. 0 < s \<and> s \<le> 1 \<and> fst z = (1 - s) * cx + s * fst b
              \<and> snd z = (1 - s) * cy + s * snd b"
            using hs hzx_eq hzy_eq by (by100 blast)
        qed
      qed
      then obtain s where hs: "0 < s" "s \<le> 1"
          and hzx: "fst z = (1-s) * cx + s * fst b"
          and hzy: "snd z = (1-s) * cy + s * snd b"
        by (by100 blast)
      \<comment> \<open>Now z = (1-s)\<cdot>c + s\<cdot>b = (1-s)\<cdot>c + s(1-u)\<cdot>v_i + su\<cdot>v_{i+1}.\<close>
      \<comment> \<open>z = (1-s)*c + s*((1-u)*v_i + u*v_{i+1}) = (1-s)*c + s(1-u)*v_i + su*v_{i+1}.\<close>
      have "in_cone i z" unfolding in_cone_def
      proof -
        have hfst_b: "fst b = (1-u)*vx i + u*vx((i+1) mod n)" using hb_edge by (by100 simp)
        have hsnd_b: "snd b = (1-u)*vy i + u*vy((i+1) mod n)" using hb_edge by (by100 simp)
        \<comment> \<open>Witnesses: \<alpha> = 1-s, \<beta> = s*(1-u), \<gamma> = s*u.\<close>
        let ?\<alpha> = "1 - s" let ?\<beta> = "s * (1 - u)" let ?\<gamma> = "s * u"
        have h1: "?\<alpha> \<ge> 0" using hs by (by100 simp)
        have h2: "?\<beta> \<ge> 0" using hs hu by (by100 simp)
        have h3: "?\<gamma> \<ge> 0" using hs hu by (by100 simp)
        have hsu: "s * (1 - u) + s * u = s"
          using right_diff_distrib[of s 1 u] by (by100 simp)
        have h4: "?\<alpha> + ?\<beta> + ?\<gamma> = 1"
          using hsu by (by100 linarith)
        have h5: "fst z = ?\<alpha> * cx + ?\<beta> * vx i + ?\<gamma> * vx ((i+1) mod n)"
        proof -
          have "s * fst b = s * ((1-u)*vx i + u*vx((i+1) mod n))"
            using hfst_b by (by100 simp)
          also have "\<dots> = s*(1-u)*vx i + s*u*vx((i+1) mod n)"
            using distrib_left[of s "(1-u)*vx i" "u*vx((i+1) mod n)"]
            using mult.assoc by (by100 simp)
          finally show ?thesis using hzx by (by100 simp)
        qed
        have h6: "snd z = ?\<alpha> * cy + ?\<beta> * vy i + ?\<gamma> * vy ((i+1) mod n)"
        proof -
          have "s * snd b = s * ((1-u)*vy i + u*vy((i+1) mod n))"
            using hsnd_b by (by100 simp)
          also have "\<dots> = s*(1-u)*vy i + s*u*vy((i+1) mod n)"
            using distrib_left[of s "(1-u)*vy i" "u*vy((i+1) mod n)"]
            using mult.assoc by (by100 simp)
          finally show ?thesis using hzy by (by100 simp)
        qed
        show "\<exists>\<alpha> \<beta> \<gamma>. 0 \<le> \<alpha> \<and> 0 \<le> \<beta> \<and> 0 \<le> \<gamma> \<and> \<alpha> + \<beta> + \<gamma> = 1 \<and>
            fst z = \<alpha> * cx + \<beta> * vx i + \<gamma> * vx ((i + 1) mod n) \<and>
            snd z = \<alpha> * cy + \<beta> * vy i + \<gamma> * vy ((i + 1) mod n)"
          using h1 h2 h3 h4 h5 h6 by (by100 blast)
      qed
      thus ?thesis using hi by (by100 blast)
    qed
  qed
  \<comment> \<open>Define \<psi> using the cone decomposition.\<close>
  define \<psi> where "\<psi> z = (
      let i = (SOME i. i < n \<and> in_cone i z);
          \<alpha> = (SOME \<alpha>. \<exists>\<beta> \<gamma>. \<alpha> \<ge> 0 \<and> \<beta> \<ge> 0 \<and> \<gamma> \<ge> 0 \<and> \<alpha> + \<beta> + \<gamma> = 1
              \<and> fst z = \<alpha> * cx + \<beta> * vx i + \<gamma> * vx ((i+1) mod n)
              \<and> snd z = \<alpha> * cy + \<beta> * vy i + \<gamma> * vy ((i+1) mod n));
          \<beta> = (SOME \<beta>. \<exists>\<gamma>. \<alpha> \<ge> 0 \<and> \<beta> \<ge> 0 \<and> \<gamma> \<ge> 0 \<and> \<alpha> + \<beta> + \<gamma> = 1
              \<and> fst z = \<alpha> * cx + \<beta> * vx i + \<gamma> * vx ((i+1) mod n)
              \<and> snd z = \<alpha> * cy + \<beta> * vy i + \<gamma> * vy ((i+1) mod n));
          \<gamma> = 1 - \<alpha> - \<beta>
      in cone_map i \<alpha> \<beta> \<gamma>)" for z
  have "\<exists>\<psi>. continuous_on P \<psi> \<and> \<psi> ` P = top1_B2 \<and> inj_on \<psi> P"
  proof (rule exI[of _ \<psi>])
    \<comment> \<open>Step C: Verify the three properties following Munkres.
       Continuity: on each cone, \<psi> is affine (hence continuous).
         The cones cover P and agree on shared edges/vertices.
         A piecewise continuous map on a finite closed cover is continuous.
       Surjectivity: the target Q = conv({q_0,...,q_{n-1}}) = B^2 (for regular n-gon on S^1).
         Each sector of Q is the image of the corresponding cone of P.
       Injectivity: on each cone, the map is an affine bijection (non-degenerate triangle
         maps to non-degenerate triangle). Between cones, images are disjoint sectors.\<close>
    \<comment> \<open>NOTE: The piecewise affine map targets the inscribed n-gon Q = conv({q_i}),
       NOT the full disk B^2. Need a radial stretch Q \<rightarrow> B^2 as second step.
       For z \<in> Q, z = r\<cdot>(cos \<theta>, sin \<theta>): stretch to (r/\<rho>(\<theta>))\<cdot>(cos \<theta>, sin \<theta>)
       where \<rho>(\<theta>) = boundary distance of Q. Then \<psi> = stretch \<circ> piecewise\_affine.
       Both maps are continuous bijections, so composition is too.
       Alternatively: redefine \<psi> directly using the normalized formula:
       \<psi>(z) = (1-\<alpha>) \<cdot> (q_target) / |q_target| where q_target = \<beta>\<cdot>q_i + \<gamma>\<cdot>q_{i+1}
       and \<alpha>,\<beta>,\<gamma> are barycentric coords in cone_i. This sends the cone to
       a sector of B^2 and is a homeomorphism on each cone.\<close>
    have h\<psi>_cont: "continuous_on P \<psi>"
      sorry \<comment> \<open>Piecewise continuous on finite closed cover (cones).
         On each cone: affine map followed by normalization. Continuous.
         Piecewise continuous on closed cover = globally continuous.\<close>
    have h\<psi>_surj: "\<psi> ` P = top1_B2"
      sorry \<comment> \<open>Image of P under piecewise cone map covers all of B^2.
         Each sector of B^2 (angle range [2\<pi>i/n, 2\<pi>(i+1)/n]) is the
         image of the corresponding cone of P. Union of sectors = B^2.\<close>
    have h\<psi>_inj: "inj_on \<psi> P"
      sorry \<comment> \<open>On each cone interior: the map is a composition of a non-degenerate
         affine map with normalization, hence injective. Between cones:
         images lie in different sectors of B^2, hence disjoint.\<close>
    show "continuous_on P \<psi> \<and> \<psi> ` P = top1_B2 \<and> inj_on \<psi> P"
      using h\<psi>_cont h\<psi>_surj h\<psi>_inj by (by100 blast)
  qed
  \<comment> \<open>Step 4: Continuous bijection from compact to Hausdorff is homeomorphism.\<close>
  \<comment> \<open>Step 4: Apply Theorem 26.6 (compact + Hausdorff + continuous bijection = homeomorphism).\<close>
  from \<open>\<exists>\<psi>. continuous_on P \<psi> \<and> \<psi> ` P = top1_B2 \<and> inj_on \<psi> P\<close>
  obtain \<psi> where h\<psi>_cont: "continuous_on P \<psi>"
      and h\<psi>_surj: "\<psi> ` P = top1_B2" and h\<psi>_inj: "inj_on \<psi> P" by (by100 blast)
  have h\<psi>_bij: "bij_betw \<psi> P top1_B2"
    unfolding bij_betw_def using h\<psi>_surj h\<psi>_inj by (by100 blast)
  \<comment> \<open>Bridge: continuous\_on P \<psi> \<Rightarrow> top1\_continuous\_map\_on via real2\_subspace\_general.\<close>
  let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
  have h\<psi>_top1: "top1_continuous_map_on P ?TP top1_B2 top1_B2_topology \<psi>"
  proof -
    have himg: "\<And>p. p \<in> P \<Longrightarrow> \<psi> p \<in> top1_B2" using h\<psi>_surj by (by100 blast)
    have "top1_B2_topology = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_B2"
      unfolding top1_B2_topology_def ..
    thus ?thesis using top1_continuous_map_on_real2_subspace_general[of P \<psi> top1_B2]
      himg h\<psi>_cont by (by5000 simp)
  qed
  \<comment> \<open>Apply Theorem 26.6: compact P + Hausdorff B² + continuous bijection = homeomorphism.\<close>
  have hR: "is_topology_on (UNIV::real set) top1_open_sets"
    unfolding top1_open_sets_def is_topology_on_def
    using open_UNIV open_empty open_Un open_Int by (by5000 auto)
  have hR2: "is_topology_on ((UNIV::real set) \<times> (UNIV::real set))
      (product_topology_on top1_open_sets top1_open_sets)"
    using hR product_topology_on_is_topology_on by (by100 blast)
  hence hR2': "is_topology_on (UNIV::(real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets)" by (by100 simp)
  have hTP_top: "is_topology_on P ?TP"
  proof -
    have "P \<subseteq> (UNIV::(real \<times> real) set)" by (by100 blast)
    thus ?thesis by (rule subspace_topology_is_topology_on[OF hR2'])
  qed
  have hTB2: "is_topology_on top1_B2 top1_B2_topology"
    unfolding top1_B2_topology_def
    by (rule subspace_topology_is_topology_on[OF hR2']) (by100 blast)
  from Theorem_26_6[OF hTP_top hTB2 hP_compact hB2_haus h\<psi>_top1 h\<psi>_bij]
  show ?thesis by (by100 blast)
qed

text \<open>Key helper: a scheme quotient provides the attaching data for Theorem 72.1.
  The 1-skeleton A = q(boundary of polygon) is closed and path-connected.
  The attaching map h = q composed with polygon-to-disk homeomorphism is continuous.
  The interior of the disk maps homeomorphically to X - A.\<close>
lemma scheme_quotient_CW_data:
  assumes "top1_quotient_of_scheme_on X TX scheme"
      and "length scheme \<ge> 3"
  shows "\<exists>(A :: 'a set) (h :: real \<times> real \<Rightarrow> 'a) (a :: 'a).
      closedin_on X TX A
    \<and> top1_path_connected_on A (subspace_topology X TX A)
    \<and> top1_continuous_map_on top1_B2 top1_B2_topology X TX h
    \<and> a \<in> A
    \<and> top1_homeomorphism_on
        (top1_B2 - top1_S1) (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
        (X - A) (subspace_topology X TX (X - A)) h
    \<and> h ` top1_S1 \<subseteq> A
    \<and> (\<forall>z\<in>top1_S1. h z \<in> A)"
proof -
  \<comment> \<open>Step 1: Extract (P, q, vx, vy) from the scheme definition.\<close>
  obtain P q vx vy where
    hP: "top1_is_polygonal_region_on P (length scheme)" and
    hq: "top1_quotient_map_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q" and
    hlen3: "length scheme \<ge> 3" and
    hverts: "\<forall>i<length scheme. (vx i, vy i) \<in> P" and
    hedge: "\<forall>i<length scheme. \<forall>j<length scheme.
        fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
           (1-t) * vy i + t * vy (Suc i mod length scheme))
         = (if snd (scheme!i) = snd (scheme!j)
            then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                    (1-t) * vy j + t * vy (Suc j mod length scheme))
            else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                    t * vy j + (1-t) * vy (Suc j mod length scheme))))" and
    hint: "\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
          p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                (1-t) * vy i + t * vy (Suc i mod length scheme)))
       \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
    using assms(1)[unfolded top1_quotient_of_scheme_on_def] assms(2)
    by (elim conjE exE) (rule that, assumption+)
  \<comment> \<open>Step 2: Get homeomorphism \<psi>: P \<rightarrow> B^2 from polygon\_homeomorphic\_to\_disk.\<close>
  let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
  from polygon_homeomorphic_to_disk[OF hP hlen3]
  obtain \<psi> where h\<psi>: "top1_homeomorphism_on P ?TP top1_B2 top1_B2_topology \<psi>" by (by100 blast)
  \<comment> \<open>Step 3: Define A = q(Bd P) where Bd P = union of edges.\<close>
  define BdP where "BdP = (\<Union>i<length scheme.
      {((1-t) * vx i + t * vx (Suc i mod length scheme),
        (1-t) * vy i + t * vy (Suc i mod length scheme)) | t. t \<in> I_set})"
  define A where "A = q ` BdP"
  \<comment> \<open>Step 4: Define h = q \<circ> \<psi>^{-1}: B^2 \<rightarrow> X.\<close>
  let ?\<psi>inv = "inv_into P \<psi>"
  have h\<psi>inv: "top1_homeomorphism_on top1_B2 top1_B2_topology P ?TP ?\<psi>inv"
    by (rule homeomorphism_inverse[OF h\<psi>])
  have h\<psi>_bij: "bij_betw \<psi> P top1_B2"
    using h\<psi> unfolding top1_homeomorphism_on_def by (by100 blast)
  have h\<psi>inv_inv: "\<forall>z\<in>top1_B2. \<psi> (?\<psi>inv z) = z"
  proof (intro ballI)
    fix z assume "z \<in> top1_B2"
    hence "z \<in> \<psi> ` P" using h\<psi>_bij unfolding bij_betw_def by (by100 simp)
    thus "\<psi> (?\<psi>inv z) = z" by (rule f_inv_into_f)
  qed
  have h\<psi>inv_inv2: "\<forall>p\<in>P. ?\<psi>inv (\<psi> p) = p"
  proof (intro ballI)
    fix p assume "p \<in> P"
    have "inj_on \<psi> P" using h\<psi>_bij unfolding bij_betw_def by (by100 blast)
    thus "?\<psi>inv (\<psi> p) = p" using \<open>p \<in> P\<close> by (rule inv_into_f_f)
  qed
  define h where "h z = q (inv_into P \<psi> z)" for z
  define a where "a = q (vx 0, vy 0)"
  \<comment> \<open>Step 5: Verify all CW data properties.\<close>
  have hA_closed: "closedin_on X TX A"
    sorry \<comment> \<open>A = q(BdP). BdP compact (finite union of segments). q continuous (quotient map).
       top1\_compact\_on image of compact under continuous is compact.
       Compact subset of Hausdorff is closed (closedin\_on).
       Requires bridging between R² compact/closed and custom topology.\<close>
  have hA_pc: "top1_path_connected_on A (subspace_topology X TX A)"
    sorry \<comment> \<open>A = q(Bd P) is path-connected: edges are paths, all vertices identified.\<close>
  have hh_cont: "top1_continuous_map_on top1_B2 top1_B2_topology X TX h"
  proof -
    have hq_cont: "top1_continuous_map_on P ?TP X TX q"
      using hq unfolding top1_quotient_map_on_def by (by100 blast)
    have h\<psi>inv_cont: "top1_continuous_map_on top1_B2 top1_B2_topology P ?TP (inv_into P \<psi>)"
      using h\<psi>inv unfolding top1_homeomorphism_on_def by (by100 blast)
    from top1_continuous_map_on_comp[OF h\<psi>inv_cont hq_cont]
    have "top1_continuous_map_on top1_B2 top1_B2_topology X TX (q \<circ> inv_into P \<psi>)" .
    moreover have "h = q \<circ> inv_into P \<psi>" unfolding h_def comp_def by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  have ha_A: "a \<in> A"
  proof -
    have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have hlen_pos: "length scheme > 0" using assms(2) by (by100 linarith)
    have "0 < length scheme" using hlen_pos .
    have hv0_bd: "(vx 0, vy 0) \<in> BdP" unfolding BdP_def
    proof -
      have "((1-(0::real)) * vx 0 + 0 * vx (Suc 0 mod length scheme),
             (1-0) * vy 0 + 0 * vy (Suc 0 mod length scheme)) = (vx 0, vy 0)"
        by (by100 simp)
      moreover have "(0::real) \<in> I_set" using h0_I .
      ultimately show "(vx 0, vy 0) \<in> (\<Union>i<length scheme. {((1-t) * vx i + t * vx (Suc i mod length scheme),
          (1-t) * vy i + t * vy (Suc i mod length scheme)) | t. t \<in> I_set})"
        using hlen_pos h0_I by (by5000 force)
    qed
    thus ?thesis unfolding a_def A_def by (by100 blast)
  qed
  have hh_homeo: "top1_homeomorphism_on (top1_B2 - top1_S1)
      (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
      (X - A) (subspace_topology X TX (X - A)) h"
    sorry \<comment> \<open>\<psi>inv maps Int B^2 to Int P, q is injective on Int P (hint), so h = q\<circ>\<psi>inv is
       a bijection Int B^2 \<rightarrow> X - A. Continuous + bijection + open map = homeomorphism.\<close>
  have hh_S1: "h ` top1_S1 \<subseteq> A"
    sorry \<comment> \<open>\<psi>inv(S^1) = Bd P (boundary maps to boundary), so h(S^1) = q(Bd P) = A.\<close>
  have hh_S1': "\<forall>z\<in>top1_S1. h z \<in> A" using hh_S1 by (by100 blast)
  show ?thesis
    apply (rule exI[of _ A])
    apply (rule exI[of _ h])
    apply (rule exI[of _ a])
    using hA_closed hA_pc hh_cont ha_A hh_homeo hh_S1 hh_S1' by (by100 blast)
qed

text \<open>For the torus scheme, the 1-skeleton is a wedge of 2 circles.
  For the dunce cap, the 1-skeleton is a single circle.\<close>
lemma torus_scheme_CW_data:
  assumes "top1_is_torus_on X TX"
      and "x0 \<in> X"
  shows "\<exists>(A :: 'a set) (h :: real \<times> real \<Rightarrow> 'a).
      closedin_on X TX A
    \<and> top1_is_wedge_of_circles_on A (subspace_topology X TX A) {0::nat, 1} x0
    \<and> top1_continuous_map_on top1_B2 top1_B2_topology X TX h
    \<and> h ` top1_S1 \<subseteq> A"
  sorry

lemma n_torus_scheme_CW_data:
  assumes "top1_is_n_fold_torus_on X TX n"
      and "x0 \<in> X"
  shows "\<exists>(A :: 'a set) (h :: real \<times> real \<Rightarrow> 'a).
      closedin_on X TX A
    \<and> top1_is_wedge_of_circles_on A (subspace_topology X TX A) ({..<2*n}::nat set) x0
    \<and> top1_continuous_map_on top1_B2 top1_B2_topology X TX h
    \<and> h ` top1_S1 \<subseteq> A"
  sorry

lemma dunce_cap_scheme_CW_data:
  assumes "top1_is_dunce_cap_on X TX m"
      and "x0 \<in> X" and "m > 0"
  shows "\<exists>(A :: 'a set) (h :: real \<times> real \<Rightarrow> 'a).
      closedin_on X TX A
    \<and> (\<exists>f. top1_homeomorphism_on top1_S1 top1_S1_topology A (subspace_topology X TX A) f)
    \<and> top1_continuous_map_on top1_B2 top1_B2_topology X TX h
    \<and> h ` top1_S1 \<subseteq> A
    \<and> x0 \<in> A \<and> A \<subseteq> X"
  sorry

lemma m_projective_scheme_CW_data:
  assumes "top1_is_m_fold_projective_on X TX m"
      and "x0 \<in> X"
  shows "\<exists>(A :: 'a set) (h :: real \<times> real \<Rightarrow> 'a).
      closedin_on X TX A
    \<and> top1_is_wedge_of_circles_on A (subspace_topology X TX A) ({..<m}::nat set) x0
    \<and> top1_continuous_map_on top1_B2 top1_B2_topology X TX h
    \<and> h ` top1_S1 \<subseteq> A"
  sorry

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
  \<comment> \<open>Step 1: The torus is the quotient of the square by scheme aba\<inverse>b\<inverse>. Extract the
     attaching data: 1-skeleton A (wedge of 2 circles), attaching map h: B² \<rightarrow> T.\<close>
  obtain A :: "'a set" and h :: "real \<times> real \<Rightarrow> 'a"
    where hA_sub: "closedin_on T_torus TT A"
      and hA_wedge: "top1_is_wedge_of_circles_on A (subspace_topology T_torus TT A) {0::nat, 1} x0"
      and hh_cont: "top1_continuous_map_on top1_B2 top1_B2_topology T_torus TT h"
      and hh_S1_A: "h ` top1_S1 \<subseteq> A"
    using torus_scheme_CW_data[OF assms] by (by100 blast)
  \<comment> \<open>Step 2: By Theorem 72.1, \<pi>_1(T) \<cong> \<pi>_1(A)/\<langle>\<langle>k_*([p])\<rangle>\<rangle> where k = h|_{S¹}.
     \<pi>_1(A) is free on {a, b}. The relator is aba\<inverse>b\<inverse>.\<close>
  have hA_free: "\<exists>(F::int set) mulF eF invgF (\<iota>F::nat \<Rightarrow> int).
      top1_is_free_group_full_on F mulF eF invgF \<iota>F {0::nat, 1}
      \<and> top1_groups_isomorphic_on F mulF
          (top1_fundamental_group_carrier A (subspace_topology T_torus TT A) x0)
          (top1_fundamental_group_mul A (subspace_topology T_torus TT A) x0)"
  proof -
    have hset_eq: "{0::nat, 1} = {..<(2::nat)}" by (by100 auto)
    have hwedge2: "top1_is_wedge_of_circles_on A (subspace_topology T_torus TT A) {..<(2::nat)} x0"
      using hA_wedge hset_eq by (by100 simp)
    from Theorem_71_1_wedge_of_circles_finite[OF hwedge2]
    obtain G0 :: "int set" and mul0 e0 invg0 and \<iota>0 :: "nat \<Rightarrow> int" where
        hG0f: "top1_is_free_group_full_on G0 mul0 e0 invg0 \<iota>0 {..<2::nat}" and
        hG0i: "top1_groups_isomorphic_on G0 mul0
            (top1_fundamental_group_carrier A (subspace_topology T_torus TT A) x0)
            (top1_fundamental_group_mul A (subspace_topology T_torus TT A) x0)"
      by (elim exE conjE) (rule that, assumption+)
    have "top1_is_free_group_full_on G0 mul0 e0 invg0 \<iota>0 {0::nat, 1}"
      using hG0f hset_eq by (by100 simp)
    thus ?thesis using hG0i by (by100 blast)
  qed
  \<comment> \<open>Step 3: The quotient F({a,b})/\<langle>\<langle>aba\<inverse>b\<inverse>\<rangle>\<rangle>: since aba\<inverse>b\<inverse>=1 means ab=ba,
     the quotient is the free abelian group on {a,b}, which is Z \<times> Z.\<close>
  \<comment> \<open>Step 3a: Need additional CW data: h|_{int B²} homeomorphism onto T-A, h(1,0) = x0.\<close>
  have hCW_full: "\<exists>h'. top1_continuous_map_on top1_B2 top1_B2_topology T_torus TT h'
      \<and> h' ` top1_S1 \<subseteq> A
      \<and> top1_homeomorphism_on (top1_B2 - top1_S1)
            (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
            (T_torus - A) (subspace_topology T_torus TT (T_torus - A)) h'
      \<and> h' (1, 0) = x0"
    sorry \<comment> \<open>Needs scheme\_quotient\_CW\_data with homeomorphism condition + basepoint.\<close>
  \<comment> \<open>Step 3b: Apply Theorem 72.1 to get \<pi>_1(T) \<cong> \<pi>_1(A)/\<langle>\<langle>relator\<rangle>\<rangle>.\<close>
  have hThm721: "\<exists>\<iota>. top1_groups_isomorphic_on
      (top1_fundamental_group_carrier T_torus TT x0)
      (top1_fundamental_group_mul T_torus TT x0)
      (top1_quotient_group_carrier_on
         (top1_fundamental_group_carrier A (subspace_topology T_torus TT A) x0)
         (top1_fundamental_group_mul A (subspace_topology T_torus TT A) x0)
         (top1_normal_subgroup_generated_on
            (top1_fundamental_group_carrier A (subspace_topology T_torus TT A) x0)
            (top1_fundamental_group_mul A (subspace_topology T_torus TT A) x0)
            (top1_fundamental_group_id A (subspace_topology T_torus TT A) x0)
            (top1_fundamental_group_invg A (subspace_topology T_torus TT A) x0)
            {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
               A (subspace_topology T_torus TT A) x0 \<iota>
               {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                     (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}}))
      (top1_quotient_group_mul_on
         (top1_fundamental_group_mul A (subspace_topology T_torus TT A) x0))"
    sorry \<comment> \<open>Apply Theorem\_72\_1 with the CW data.\<close>
  \<comment> \<open>Step 3c: The relator is aba\<inverse>b\<inverse> = [a,b]. Quotient by [a,b] = abelianization.
     F({a,b})/[F,F] = free abelian on {a,b} = Z \<times> Z (Theorem 69.4 + 67.8).\<close>
  have hquotient_ZZ: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier T_torus TT x0)
      (top1_fundamental_group_mul T_torus TT x0)
      (UNIV::(int \<times> int) set) (\<lambda>(a1,a2) (b1,b2). (a1+b1, a2+b2))"
    sorry \<comment> \<open>Compose: \<pi>_1(T) \<cong> \<pi>_1(A)/\<langle>\<langle>[a,b]\<rangle>\<rangle> \<cong> Abel(F(a,b)) \<cong> Z\<times>Z.\<close>
  show ?thesis by (rule hquotient_ZZ)
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
  \<comment> \<open>Step 1: The dunce cap has 1-skeleton A = single circle (\<cong> S¹).
     The attaching map wraps S¹ n times around A.\<close>
  \<comment> \<open>Extract quotient map q from dunce cap definition.\<close>
  obtain q where hq_quot: "top1_quotient_map_on top1_B2 top1_B2_topology X TX q"
      and hq_S1: "\<forall>z\<in>top1_S1. \<forall>z'\<in>top1_S1.
            q z = q z' \<longleftrightarrow>
            (\<exists>k::nat. k < n \<and>
               z' = (cos (2*pi*real k/real n) * fst z - sin (2*pi*real k/real n) * snd z,
                     sin (2*pi*real k/real n) * fst z + cos (2*pi*real k/real n) * snd z))"
      and hq_inj: "inj_on q (top1_B2 - top1_S1)"
      and hq_sep: "\<forall>z\<in>top1_B2 - top1_S1. \<forall>z'\<in>top1_S1. q z \<noteq> q z'"
    using assms(2) unfolding top1_is_dunce_cap_on_def
    apply (elim exE conjE)
    apply (rule that)
    apply assumption+
    done
  \<comment> \<open>A = q(S1) is the 1-skeleton, h = q is the attaching map.\<close>
  let ?A_loc = "q ` top1_S1"
  have hq_cont: "top1_continuous_map_on top1_B2 top1_B2_topology X TX q"
    using hq_quot unfolding top1_quotient_map_on_def by (by100 blast)
  obtain A :: "'a set" and h :: "real \<times> real \<Rightarrow> 'a"
    where hA_circle: "\<exists>f. top1_homeomorphism_on top1_S1 top1_S1_topology
             A (subspace_topology X TX A) f"
      and hh_att: "top1_continuous_map_on top1_B2 top1_B2_topology X TX h"
      and hh_wrap: "\<forall>s\<in>I_set. h (cos (2*pi*s), sin (2*pi*s)) = h (cos (2*pi*n*s), sin (2*pi*n*s))"
      and hx0_A: "x0 \<in> A" and hA_sub: "A \<subseteq> X"
    sorry \<comment> \<open>From dunce cap: A = q(S1), h = q. Circle homeomorphism from quotient structure.
       Uses dunce\_cap\_scheme\_CW\_data for basic structure; wrapping from dunce cap definition.\<close>
  \<comment> \<open>Step 2: \<pi>_1(A) \<cong> Z (fundamental group of circle).\<close>
  have hA_Z: "\<exists>f. top1_group_iso_on
      (top1_fundamental_group_carrier A (subspace_topology X TX A) x0)
      (top1_fundamental_group_mul A (subspace_topology X TX A) x0)
      (UNIV::int set) (\<lambda>a b. a + b) f"
  proof -
    let ?TA = "subspace_topology X TX A"
    \<comment> \<open>Extract homeomorphism h_circ: S1 \<rightarrow> A.\<close>
    obtain h_circ where h_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology A ?TA h_circ"
      using hA_circle by (by100 blast)
    \<comment> \<open>\<pi>_1(S1, (1,0)) \<cong> (Z, +) by Theorem 54.5.\<close>
    have hS1_Z: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        top1_Z_group top1_Z_mul"
      by (rule Theorem_54_5_iso)
    \<comment> \<open>By Corollary 52.5: homeomorphism S1 \<cong> A gives \<pi>_1(S1, (1,0)) \<cong> \<pi>_1(A, h_circ(1,0)).\<close>
    have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
      using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
    have hTA_top: "is_topology_on A ?TA"
    proof -
      have hTX: "is_topology_on X TX"
        using assms(2) unfolding top1_is_dunce_cap_on_def is_topology_on_strict_def by (by100 blast)
      show ?thesis by (rule subspace_topology_is_topology_on[OF hTX hA_sub])
    qed
    have h10_S1: "(1::real, 0::real) \<in> top1_S1"
      unfolding top1_S1_def by (by100 simp)
    have hS1_A_iso: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_carrier A ?TA (h_circ (1, 0)))
        (top1_fundamental_group_mul A ?TA (h_circ (1, 0)))"
      by (rule Corollary_52_5_homeomorphism_iso[OF hS1_top hTA_top h_homeo h10_S1]) (by100 simp)
    \<comment> \<open>Chain: \<pi>_1(A, h_circ(1,0)) \<cong> \<pi>_1(S1, (1,0)) \<cong> Z.\<close>
    have hA_hc_Z: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier A ?TA (h_circ (1, 0)))
        (top1_fundamental_group_mul A ?TA (h_circ (1, 0)))
        top1_Z_group top1_Z_mul"
    proof -
      have hA_S1: "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier A ?TA (h_circ (1, 0)))
          (top1_fundamental_group_mul A ?TA (h_circ (1, 0)))
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
          (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))"
      proof -
        have hgrpS1: "top1_is_group_on
            (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_id top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_invg top1_S1 top1_S1_topology (1, 0))"
          by (rule top1_fundamental_group_is_group[OF hS1_top h10_S1])
        have hhc_A: "h_circ (1, 0) \<in> A"
          using h_homeo h10_S1 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have hgrpA: "top1_is_group_on
            (top1_fundamental_group_carrier A ?TA (h_circ (1, 0)))
            (top1_fundamental_group_mul A ?TA (h_circ (1, 0)))
            (top1_fundamental_group_id A ?TA (h_circ (1, 0)))
            (top1_fundamental_group_invg A ?TA (h_circ (1, 0)))"
          by (rule top1_fundamental_group_is_group[OF hTA_top hhc_A])
        show ?thesis by (rule top1_groups_isomorphic_on_sym[OF hS1_A_iso hgrpS1 hgrpA])
      qed
      show ?thesis by (rule groups_isomorphic_trans_fwd[OF hA_S1 hS1_Z])
    qed
    \<comment> \<open>Base change: \<pi>_1(A, x0) \<cong> \<pi>_1(A, h_circ(1,0)) (since A is path-connected).\<close>
    have hA_pc: "top1_path_connected_on A ?TA"
    proof -
      have "top1_path_connected_on top1_S1 top1_S1_topology"
        by (rule S1_path_connected)
      thus ?thesis
        by (rule homeomorphism_preserves_path_connected[OF h_homeo])
    qed
    have hhc_A: "h_circ (1, 0) \<in> A"
      using h_homeo h10_S1 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have hA_bc: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier A ?TA x0)
        (top1_fundamental_group_mul A ?TA x0)
        (top1_fundamental_group_carrier A ?TA (h_circ (1, 0)))
        (top1_fundamental_group_mul A ?TA (h_circ (1, 0)))"
      by (rule Corollary_52_2_basepoint_independent[OF hA_pc hx0_A hhc_A])
    \<comment> \<open>Chain: \<pi>_1(A, x0) \<cong> \<pi>_1(A, h_circ(1,0)) \<cong> Z.\<close>
    have hA_x0_Z: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier A ?TA x0)
        (top1_fundamental_group_mul A ?TA x0)
        top1_Z_group top1_Z_mul"
      by (rule groups_isomorphic_trans_fwd[OF hA_bc hA_hc_Z])
    \<comment> \<open>Unfold Z definitions.\<close>
    have "top1_Z_group = (UNIV :: int set)" unfolding top1_Z_group_def by (by100 simp)
    moreover have "top1_Z_mul = (\<lambda>a b. a + b)" unfolding top1_Z_mul_def by (rule ext)+ (by100 simp)
    ultimately show ?thesis using hA_x0_Z unfolding top1_groups_isomorphic_on_def by (by100 simp)
  qed
  \<comment> \<open>Step 3: By Theorem 72.1, \<pi>_1(X) \<cong> Z/\<langle>\<langle>n\<rangle>\<rangle> = Z/nZ.
     The relator is aⁿ (the standard loop wrapped n times).\<close>
  \<comment> \<open>Step 3a: Apply Theorem 72.1 to get \<pi>_1(X) \<cong> \<pi>_1(A)/\<langle>\<langle>[k\<circ>p]\<rangle>\<rangle>.\<close>
  \<comment> \<open>Need: is_topology_on_strict, Hausdorff, A closed, A path-connected,
     h continuous B2\<rightarrow>X, a \<in> A, h|_{Int B2} homeomorphism, h(S1)\<subseteq>A, h(1,0)=a.\<close>
  have hThm72: "\<exists>\<iota>.
      top1_continuous_map_on top1_S1 top1_S1_topology A
           (subspace_topology X TX A) \<iota>
    \<and> (\<forall>z\<in>top1_S1. \<iota> z = h z)
    \<and> top1_groups_isomorphic_on
          (top1_fundamental_group_carrier X TX x0)
          (top1_fundamental_group_mul X TX x0)
          (top1_quotient_group_carrier_on
             (top1_fundamental_group_carrier A (subspace_topology X TX A) x0)
             (top1_fundamental_group_mul A (subspace_topology X TX A) x0)
             (top1_normal_subgroup_generated_on
                (top1_fundamental_group_carrier A (subspace_topology X TX A) x0)
                (top1_fundamental_group_mul A (subspace_topology X TX A) x0)
                (top1_fundamental_group_id A (subspace_topology X TX A) x0)
                (top1_fundamental_group_invg A (subspace_topology X TX A) x0)
                {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
                    A (subspace_topology X TX A) x0
                    (\<lambda>z. h z)
                  {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                      (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) g}}))
          (top1_quotient_group_mul_on
             (top1_fundamental_group_mul A (subspace_topology X TX A) x0))"
    sorry \<comment> \<open>Apply Theorem_72_1. Needs all hypotheses verified.\<close>
  \<comment> \<open>Step 3b: The relator [k\<circ>p] in \<pi>_1(A) corresponds to n \<in> Z.
     Since \<pi>_1(A) \<cong> Z, the normal closure of {n} is nZ.
     Z/nZ \<cong> (top1_Zn_group n, top1_Zn_mul n) by Z_quotient_nZ_iso.\<close>
  \<comment> \<open>Step 3c: Compose isomorphisms: \<pi>_1(X) \<cong> \<pi>_1(A)/\<langle>\<langle>[k\<circ>p]\<rangle>\<rangle> \<cong> Z/\<langle>\<langle>n\<rangle>\<rangle> \<cong> Z/nZ.\<close>
  show ?thesis sorry \<comment> \<open>Compose the three isomorphisms.\<close>
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


text \<open>Cone superset: cone(conv n, v_n) \<subseteq> conv(Suc n).\<close>
lemma convex_hull_cone_sup:
  fixes vx vy :: "nat \<Rightarrow> real"
  shows "(\<lambda>(t, x', y'). ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))
      ` ({0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
          \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)})
    \<subseteq> {(x, y). \<exists>c. (\<forall>i<Suc n. c i \<ge> 0) \<and> (\<Sum>i<Suc n. c i) = 1
      \<and> x = (\<Sum>i<Suc n. c i * vx i) \<and> y = (\<Sum>i<Suc n. c i * vy i)}"
proof (rule subsetI)
  fix q assume hq_mem: "q \<in> (\<lambda>(t, x', y'). ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))
      ` ({0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
          \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)})"
  then obtain p where hp: "p \<in> {0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
      \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      and hq: "q = (case p of (t, x', y') \<Rightarrow> ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))"
    by (by100 blast)
  obtain t r where htr: "p = (t, r)" "t \<in> {0..1}" by (cases p) (use hp in \<open>(by100 auto)\<close>)
  obtain x' y' where hr: "r = (x', y')" by (cases r)
  have ht: "0 \<le> t" "t \<le> 1" using htr(2) by (by100 auto)+
  have hq_eq: "q = ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n)"
    using hq htr(1) hr by (by100 simp)
  obtain c' where hc': "\<forall>i<n. (0::real) \<le> c' i" "(\<Sum>i<n. c' i) = 1"
      "x' = (\<Sum>i<n. c' i * vx i)" "y' = (\<Sum>i<n. c' i * vy i)"
    using hp htr(1) hr by (by100 blast)
  let ?c = "\<lambda>i. if i < n then (1-t) * c' i else if i = n then t else 0 :: real"
  have hc_nn: "\<forall>i<Suc n. 0 \<le> ?c i" using ht hc'(1) by (by100 force)
  have hc_sum: "(\<Sum>i<Suc n. ?c i) = 1"
  proof -
    have "(\<Sum>i<n. ?c i) = (\<Sum>i<n. (1-t) * c' i)" by (rule sum.cong) (by100 simp)+
    also have "\<dots> = (1-t)" using hc'(2) by (simp add: sum_distrib_left[symmetric])
    finally show ?thesis by (by100 simp)
  qed
  have hc_x: "(\<Sum>i<Suc n. ?c i * vx i) = (1-t)*x' + t*vx n"
  proof -
    have "(\<Sum>i<n. ?c i * vx i) = (\<Sum>i<n. (1-t) * c' i * vx i)"
      by (rule sum.cong) (by100 simp)+
    also have "\<dots> = (1-t) * x'" using hc'(3) by (simp add: sum_distrib_left mult.assoc)
    finally show ?thesis by (by100 simp)
  qed
  have hc_y: "(\<Sum>i<Suc n. ?c i * vy i) = (1-t)*y' + t*vy n"
  proof -
    have "(\<Sum>i<n. ?c i * vy i) = (\<Sum>i<n. (1-t) * c' i * vy i)"
      by (rule sum.cong) (by100 simp)+
    also have "\<dots> = (1-t) * y'" using hc'(4) by (simp add: sum_distrib_left mult.assoc)
    finally show ?thesis by (by100 simp)
  qed
  show "q \<in> {(x, y). \<exists>c. (\<forall>i<Suc n. c i \<ge> 0) \<and> (\<Sum>i<Suc n. c i) = 1
      \<and> x = (\<Sum>i<Suc n. c i * vx i) \<and> y = (\<Sum>i<Suc n. c i * vy i)}"
    unfolding hq_eq
    apply simp
    apply (rule_tac x="?c" in exI)
    using hc_nn hc_sum hc_x hc_y by force
qed

text \<open>Cone subset: conv(Suc n) \<subseteq> cone(conv n, v_n).\<close>
lemma convex_hull_cone_sub:
  fixes vx vy :: "nat \<Rightarrow> real"
  assumes "n \<ge> 1"
  shows "{(x, y). \<exists>c. (\<forall>i<Suc n. c i \<ge> 0) \<and> (\<Sum>i<Suc n. c i) = 1
      \<and> x = (\<Sum>i<Suc n. c i * vx i) \<and> y = (\<Sum>i<Suc n. c i * vy i)}
    \<subseteq> (\<lambda>(t, x', y'). ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))
      ` ({0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
          \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)})"
proof (rule subsetI)
  fix q assume "q \<in> {(x, y). \<exists>c. (\<forall>i<Suc n. c i \<ge> 0) \<and> (\<Sum>i<Suc n. c i) = 1
      \<and> x = (\<Sum>i<Suc n. c i * vx i) \<and> y = (\<Sum>i<Suc n. c i * vy i)}"
  then obtain x y c where hq: "q = (x, y)"
      and hc: "\<forall>i<Suc n. (0::real) \<le> c i" "(\<Sum>i<Suc n. c i) = 1"
      "x = (\<Sum>i<Suc n. c i * vx i)" "y = (\<Sum>i<Suc n. c i * vy i)"
    by (by100 blast)
  let ?t = "c n"
  have ht0: "0 \<le> ?t" using hc(1) by (by100 force)
  have ht1: "?t \<le> 1"
    by (rule order_trans[OF member_le_sum[of n "{..<Suc n}" c]]) (use hc in auto)
  show "q \<in> (\<lambda>(t, x', y'). ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))
      ` ({0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
          \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)})"
  proof (cases "?t = 1")
    case True
    have hsum0: "(\<Sum>i<n. c i) = 0" using hc(2) True by simp
    have hall0: "\<forall>i<n. c i = 0"
    proof (intro allI impI)
      fix i assume "i < n"
      have "c i \<le> (\<Sum>i<n. c i)" by (rule member_le_sum) (use hc(1) \<open>i<n\<close> in auto)
      moreover have "0 \<le> c i" using hc(1) \<open>i<n\<close> by (by100 force)
      ultimately show "c i = 0" using hsum0 by (by100 linarith)
    qed
    have hx_vn: "x = vx n" using hc(3) hall0 True by simp
    have hy_vn: "y = vy n" using hc(4) hall0 True by simp
    \<comment> \<open>n \<ge> 1 (from induction hypothesis), so Pn is non-empty: (vx 0, vy 0) \<in> Pn.\<close>
    have hn1: "n \<ge> 1" using assms .
    let ?d = "\<lambda>i::nat. if i = 0 then 1::real else 0"
    have "(vx 0, vy 0) \<in> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      apply simp
      apply (rule_tac x="?d" in exI)
    proof (intro conjI allI impI)
      fix i :: nat assume "i < n" thus "0 \<le> ?d i" by (by100 simp)
    next
      show "(\<Sum>i<n. ?d i) = 1" using hn1 by simp
    next
      show "vx 0 = (\<Sum>i<n. ?d i * vx i)"
      proof -
        have "(\<Sum>i<n. ?d i * vx i) = ?d 0 * vx 0 + (\<Sum>i\<in>{..<n}-{0}. ?d i * vx i)"
          using hn1 by (intro sum.remove) auto
        also have "(\<Sum>i\<in>{..<n}-{0}. ?d i * vx i) = 0"
          by (rule sum.neutral) (by100 simp)
        finally show ?thesis by (by100 simp)
      qed
    next
      show "vy 0 = (\<Sum>i<n. ?d i * vy i)"
      proof -
        have "(\<Sum>i<n. ?d i * vy i) = ?d 0 * vy 0 + (\<Sum>i\<in>{..<n}-{0}. ?d i * vy i)"
          using hn1 by (intro sum.remove) auto
        also have "(\<Sum>i\<in>{..<n}-{0}. ?d i * vy i) = 0"
          by (rule sum.neutral) (by100 simp)
        finally show ?thesis by (by100 simp)
      qed
    qed
    hence hpn_ne: "\<exists>p'. p' \<in> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}" by (by100 blast)
    then obtain x0 y0 where hxy0: "(x0, y0) \<in> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}" by (by100 blast)
    have "(1::real, (x0, y0)) \<in> {0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      using hxy0 by auto
    moreover have "q = (case (1::real, (x0, y0)) of (t, x', y') \<Rightarrow>
        ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))"
      using hq hx_vn hy_vn by (by100 simp)
    ultimately show ?thesis by (by100 blast)
  next
    case htnot1: False
    have hlt1: "?t < 1" using htnot1 ht1 by (by100 linarith)
    hence h1mt: "1 - ?t > 0" by (by100 linarith)
    let ?c' = "\<lambda>i. c i / (1 - ?t)"
    have hc'_nn: "\<forall>i<n. ?c' i \<ge> 0" using hc(1) h1mt by (by100 force)
    have hc'_sum: "(\<Sum>i<n. ?c' i) = 1"
    proof -
      have "(\<Sum>i<n. ?c' i) = (\<Sum>i<n. c i) / (1 - ?t)"
        by (simp add: sum_divide_distrib)
      also have "(\<Sum>i<n. c i) = 1 - ?t" using hc(2) by simp
      finally show ?thesis using h1mt by simp
    qed
    let ?x' = "\<Sum>i<n. ?c' i * vx i"
    let ?y' = "\<Sum>i<n. ?c' i * vy i"
    have hrescale_x: "(1-?t)*?x' = (\<Sum>i<n. c i * vx i)"
    proof -
      have "(1-?t)*?x' = (\<Sum>i<n. (1-?t) * (?c' i * vx i))"
        by (simp add: sum_distrib_left)
      also have "\<dots> = (\<Sum>i<n. c i * vx i)"
        using h1mt by (intro sum.cong) (simp_all add: field_simps)
      finally show ?thesis .
    qed
    have hrescale_y: "(1-?t)*?y' = (\<Sum>i<n. c i * vy i)"
    proof -
      have "(1-?t)*?y' = (\<Sum>i<n. (1-?t) * (?c' i * vy i))"
        by (simp add: sum_distrib_left)
      also have "\<dots> = (\<Sum>i<n. c i * vy i)"
        using h1mt by (intro sum.cong) (simp_all add: field_simps)
      finally show ?thesis .
    qed
    have hx_eq: "x = (1-?t)*?x' + ?t*vx n" using hc(3) hrescale_x by simp
    have hy_eq: "y = (1-?t)*?y' + ?t*vy n" using hc(4) hrescale_y by simp
    have "(?x', ?y') \<in> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      apply simp
      apply (rule_tac x="?c'" in exI)
      using hc'_nn hc'_sum by (by100 auto)
    have ht_in: "?t \<in> {0..1}" using ht0 ht1 by (by100 auto)
    hence "(?t, (?x', ?y')) \<in> {0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      using \<open>(?x', ?y') \<in> _\<close> by (by100 blast)
    moreover have "q = (case (?t, (?x', ?y')) of (t, x', y') \<Rightarrow>
        ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))"
      using hq hx_eq hy_eq by (by100 simp)
    ultimately show ?thesis by (by100 blast)
  qed
qed

text \<open>A convex hull of n \<ge> 3 points in R^2 is compact.\<close>
text \<open>Convex hull of n \<ge> 1 points is compact, by induction on n.
  Base: single point. Step: conv(n+1) = image of [0,1] \<times> conv(n) under continuous cone map.\<close>
lemma convex_hull_compact_general:
  fixes vx vy :: "nat \<Rightarrow> real" and n :: nat
  assumes "n \<ge> 1"
  shows "compact {(x, y). \<exists>coeffs. (\<forall>i<n. (coeffs i :: real) \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
      \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
  using assms
proof (induction n rule: nat_induct_at_least)
  case base
  \<comment> \<open>n=1: P = {(vx 0, vy 0)}, a single point — trivially compact.\<close>
  have "{(x::real, y::real). \<exists>coeffs. (\<forall>i<1. coeffs i \<ge> 0) \<and> (\<Sum>i<1. coeffs i) = 1
      \<and> x = (\<Sum>i<1. coeffs i * vx i) \<and> y = (\<Sum>i<1. coeffs i * vy i)}
    = {(vx 0, vy 0)}"
  proof
    show "{(vx 0, vy 0)} \<subseteq> {(x, y). \<exists>coeffs. (\<forall>i<1. coeffs i \<ge> 0) \<and>
        (\<Sum>i<1. coeffs i) = 1 \<and> x = (\<Sum>i<1. coeffs i * vx i) \<and> y = (\<Sum>i<1. coeffs i * vy i)}"
      by (rule subsetI) (auto intro: exI[of _ "\<lambda>_. 1"])
  next
    show "{(x, y). \<exists>coeffs. (\<forall>i<1. coeffs i \<ge> 0) \<and> (\<Sum>i<1. coeffs i) = 1 \<and>
        x = (\<Sum>i<1. coeffs i * vx i) \<and> y = (\<Sum>i<1. coeffs i * vy i)} \<subseteq> {(vx 0, vy 0)}"
      by auto
  qed
  moreover have "compact {(vx 0, vy 0)}"
  proof (rule compactI)
    fix \<U> :: "(real \<times> real) set set"
    assume "\<forall>U\<in>\<U>. open U" "{(vx 0, vy 0)} \<subseteq> \<Union>\<U>"
    then obtain U where "U \<in> \<U>" "(vx 0, vy 0) \<in> U" by (by100 blast)
    thus "\<exists>\<F>\<subseteq>\<U>. finite \<F> \<and> {(vx 0, vy 0)} \<subseteq> \<Union>\<F>"
      by (rule_tac x="{U}" in exI) (by100 blast)
  qed
  ultimately show ?case by (by100 simp)
next
  case (Suc n)
  \<comment> \<open>Inductive step: conv(n+1 points) = cone from v_n over conv(n points).
     (x,y) \<in> conv(n+1) iff \<exists>t\<in>[0,1]. \<exists>(x',y')\<in>conv(n).
       x = (1-t)*x' + t*vx(n)  and  y = (1-t)*y' + t*vy(n).
     This is the image of [0,1] \<times> conv(n) under a continuous map.\<close>
  let ?Pn = "{(x::real, y::real). \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
      \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
  let ?Pn1 = "{(x::real, y::real). \<exists>coeffs. (\<forall>i<Suc n. coeffs i \<ge> 0) \<and> (\<Sum>i<Suc n. coeffs i) = 1
      \<and> x = (\<Sum>i<Suc n. coeffs i * vx i) \<and> y = (\<Sum>i<Suc n. coeffs i * vy i)}"
  have hPn_compact: "compact ?Pn" by (rule Suc.IH)
  \<comment> \<open>f: [0,1] \<times> ?Pn \<rightarrow> ?Pn1 via f(t, (x',y')) = ((1-t)*x' + t*vx n, (1-t)*y' + t*vy n).\<close>
  let ?f = "\<lambda>(t::real, (x'::real, y'::real)). ((1-t)*x' + t*vx n, (1-t)*y' + t*vy n)"
  \<comment> \<open>[0,1] \<times> ?Pn is compact.\<close>
  have hdom_compact: "compact ({0..1::real} \<times> ?Pn)"
    by (rule compact_Times_general[OF compact_Icc hPn_compact])
  \<comment> \<open>?f is continuous.\<close>
  have hf_cont: "continuous_on ({0..1} \<times> ?Pn) ?f"
  proof -
    have "continuous_on UNIV ?f"
      unfolding split_def
      by (intro continuous_on_Pair continuous_on_add continuous_on_mult continuous_on_id
          continuous_on_diff continuous_on_fst continuous_on_snd continuous_on_const)
    thus ?thesis by (rule continuous_on_subset) (by100 blast)
  qed
  \<comment> \<open>?Pn1 = ?f ` ({0..1} \<times> ?Pn).\<close>
  have hPn1_eq: "?Pn1 = ?f ` ({0..1} \<times> ?Pn)"
    by (rule equalityI[OF convex_hull_cone_sub[OF Suc(1)] convex_hull_cone_sup])
  show ?case unfolding hPn1_eq
    by (rule compact_continuous_image[OF hf_cont hdom_compact])
qed

lemma convex_hull_compact:
  fixes vx vy :: "nat \<Rightarrow> real" and n :: nat
  assumes "n \<ge> 3"
  shows "compact {(x, y). \<exists>coeffs. (\<forall>i<n. (coeffs i :: real) \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
      \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
  using convex_hull_compact_general[of n vx vy] assms by (by100 linarith)

\<comment> \<open>Strict polygonal quotient: all scheme properties + no extra identifications.
   Uses a SINGLE set of existentials (scheme, P, q, vx, vy) to avoid witness matching.\<close>
definition top1_is_polygonal_quotient_strict_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_polygonal_quotient_strict_on X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     (\<exists>(scheme :: (nat \<times> bool) list) P q (vx::nat\<Rightarrow>real) (vy::nat\<Rightarrow>real).
        top1_is_polygonal_region_on P (length scheme)
      \<and> top1_quotient_map_on P
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q
      \<and> (\<forall>i<length scheme. \<forall>j<length scheme. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j))
      \<and> (\<forall>i<length scheme. (vx i, vy i) \<in> P)
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
      \<and> (\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
                    p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                          (1-t) * vy i + t * vy (Suc i mod length scheme)))
               \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p'))
      \<and> (\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
            q ((1-t) * vx i + t * vx (Suc i mod length scheme),
               (1-t) * vy i + t * vy (Suc i mod length scheme))
          = q ((1-s) * vx j + s * vx (Suc j mod length scheme),
               (1-s) * vy j + s * vy (Suc j mod length scheme))
          \<longrightarrow> (i = j \<and> t = s)
            \<or> (fst (scheme!i) = fst (scheme!j) \<and>
               (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))))"

\<comment> \<open>Richer extraction from scheme: gives vertices, edge identification, interior singleton fibers.\<close>
lemma quotient_of_scheme_extract_full:
  assumes "top1_quotient_of_scheme_on X TX scheme"
  obtains P q vx vy where
    "top1_is_polygonal_region_on P (length scheme)"
    "top1_quotient_map_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q"
    "length scheme \<ge> 3"
    "\<forall>i<length scheme. (vx i, vy i) \<in> P"
    "\<forall>i<length scheme. \<forall>j<length scheme.
        fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set.
           q ((1-t) * vx i + t * vx (Suc i mod length scheme),
              (1-t) * vy i + t * vy (Suc i mod length scheme))
         = (if snd (scheme!i) = snd (scheme!j)
            then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                    (1-t) * vy j + t * vy (Suc j mod length scheme))
            else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                    t * vy j + (1-t) * vy (Suc j mod length scheme))))"
    "\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
              p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                    (1-t) * vy i + t * vy (Suc i mod length scheme)))
         \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
proof -
  from assms obtain P q vx vy where
    h1: "top1_is_polygonal_region_on P (length scheme)" and
    h2: "top1_quotient_map_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q" and
    h3: "\<forall>i<length scheme. (vx i, vy i) \<in> P" and
    h4: "\<forall>i<length scheme. \<forall>j<length scheme.
        fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
            (1-t) * vy i + t * vy (Suc i mod length scheme))
         = (if snd (scheme!i) = snd (scheme!j)
            then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                    (1-t) * vy j + t * vy (Suc j mod length scheme))
            else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                    t * vy j + (1-t) * vy (Suc j mod length scheme))))" and
    h5: "\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
          p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                (1-t) * vy i + t * vy (Suc i mod length scheme)))
       \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
    using assms unfolding top1_quotient_of_scheme_on_def
    by (elim conjE exE) blast
  have h6: "length scheme \<ge> 3"
    using h1 unfolding top1_is_polygonal_region_on_def by (by100 blast)
  show ?thesis by (rule that[OF h1 h2 h6 h3 h4 h5])
qed

\<comment> \<open>Note: quotient\_strict\_extract was removed because automation can't handle the
   50+ atom obtains formula. The "no extra identifications" condition has a proof gap
   directly in Theorem\_74\_1 instead. The top1\_is\_polygonal\_quotient\_strict\_on
   definition remains available for future use if the automation issue is resolved.\<close>

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
  \<comment> \<open>Extract scheme + P + q + vx + vy from the (non-strict) polygonal quotient definition.\<close>
  have "\<exists>scheme :: (nat \<times> bool) list. top1_quotient_of_scheme_on X TX scheme"
    using assms(2) unfolding top1_is_polygonal_quotient_on_def by (by100 blast)
  then obtain scheme :: "(nat \<times> bool) list" where hsch: "top1_quotient_of_scheme_on X TX scheme"
    by (by100 auto)
  obtain P q vx vy where
      hP_full: "top1_is_polygonal_region_on P (length scheme)"
      and hq_full: "top1_quotient_map_on P
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q"
      and hlen_full: "length scheme \<ge> 3"
      and hvert_full: "\<forall>i<length scheme. (vx i, vy i) \<in> P"
      and hedge_full: "\<forall>i<length scheme. \<forall>j<length scheme. fst (scheme!i) = fst (scheme!j) \<longrightarrow>
          (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
              (1-t) * vy i + t * vy (Suc i mod length scheme))
           = (if snd (scheme!i) = snd (scheme!j)
              then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                      (1-t) * vy j + t * vy (Suc j mod length scheme))
              else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                      t * vy j + (1-t) * vy (Suc j mod length scheme))))"
      and hinterior_full: "\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
              p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                    (1-t) * vy i + t * vy (Suc i mod length scheme)))
           \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
    by (rule quotient_of_scheme_extract_full[OF hsch])
  \<comment> \<open>The "no extra identifications" condition: proof gap. This requires
     the polygonal quotient to have ONLY the scheme-specified identifications
     on the boundary. The current definition doesn't guarantee this.\<close>
  have hno_extra_full: "\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
              q ((1-t) * vx i + t * vx (Suc i mod length scheme),
                 (1-t) * vy i + t * vy (Suc i mod length scheme))
            = q ((1-s) * vx j + s * vx (Suc j mod length scheme),
                 (1-s) * vy j + s * vy (Suc j mod length scheme))
            \<longrightarrow> (i = j \<and> t = s)
              \<or> (fst (scheme!i) = fst (scheme!j) \<and>
                 (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
    sorry \<comment> \<open>Definition gap: needs "no extra identifications" condition.\<close>
  have hcompact: "top1_compact_on X TX"
  proof -
    let ?TP_c = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
    \<comment> \<open>Reuse P, q from the extraction above.\<close>
    have hP: "top1_is_polygonal_region_on P (length scheme)" by (rule hP_full)
    have hq: "top1_quotient_map_on P ?TP_c X TX q" by (rule hq_full)
    let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
    \<comment> \<open>Step 1: P is compact (convex hull of finitely many points in R^2).\<close>
    have hP_compact: "top1_compact_on P ?TP"
    proof -
      \<comment> \<open>Bridge: product_topology_on top1_open_sets top1_open_sets = top1_open_sets for R^2.\<close>
      have hTP_eq: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
        using product_topology_on_open_sets_real2 by (by100 simp)
      \<comment> \<open>By bridge lemma: top1_compact_on P (subspace UNIV open P) \<longleftrightarrow> compact P.\<close>
      have "top1_compact_on P (subspace_topology UNIV top1_open_sets P) \<longleftrightarrow> compact P"
        by (rule top1_compact_on_subspace_UNIV_iff_compact)
      \<comment> \<open>Need: compact P (polygonal region is compact in R^2).
         P is a closed bounded convex hull, hence compact.\<close>
      moreover have "compact P"
      proof -
        \<comment> \<open>P is the convex hull of finitely many points.
           P = union of n-2 triangles (fan triangulation from vertex 0).
           Each triangle is compact (continuous image of compact [0,1]^2).
           Finite union of compact is compact.\<close>
        obtain vx vy :: "nat \<Rightarrow> real" where hn: "length scheme \<ge> 3"
            and hP_eq: "P = {(x, y). \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
                \<and> (\<Sum>i<length scheme. coeffs i) = 1
                \<and> x = (\<Sum>i<length scheme. coeffs i * vx i)
                \<and> y = (\<Sum>i<length scheme. coeffs i * vy i)}"
          using hP unfolding top1_is_polygonal_region_on_def by blast
        show "compact P" unfolding hP_eq by (rule convex_hull_compact[OF hn])
      qed
      ultimately have "top1_compact_on P (subspace_topology UNIV top1_open_sets P)" by (by100 simp)
      thus ?thesis using hTP_eq by (by100 simp)
    qed
    \<comment> \<open>Step 2: q is continuous (from quotient map).\<close>
    have hq_cont: "top1_continuous_map_on P ?TP X TX q"
      using hq unfolding top1_quotient_map_on_def by (by100 blast)
    \<comment> \<open>Step 3: q is surjective (from quotient map).\<close>
    have hq_surj: "q ` P = X"
      using hq unfolding top1_quotient_map_on_def by (by100 blast)
    \<comment> \<open>Step 4: X = q(P) is compact (continuous image of compact).\<close>
    have hTX_top: "is_topology_on X TX"
      using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have "top1_compact_on (q ` P) (subspace_topology X TX (q ` P))"
      by (rule top1_compact_on_continuous_image[OF hP_compact hTX_top hq_cont])
    hence "top1_compact_on X (subspace_topology X TX X)" using hq_surj by (by100 simp)
    moreover have "subspace_topology X TX X = TX"
    proof -
      have "\<forall>U\<in>TX. U \<subseteq> X" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
      thus ?thesis by (rule subspace_topology_self)
    qed
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Hausdorff: P is a subspace of R^2 (Hausdorff). The quotient identifies
     finitely many boundary pairs. Prove via: P Hausdorff \<Rightarrow> closed map \<Rightarrow> Hausdorff quotient.\<close>
  have hhausdorff: "is_hausdorff_on X TX"
  proof -
    \<comment> \<open>Reuse P, q, vx, vy, scheme from the outer extraction.\<close>
    have hP_loc: "top1_is_polygonal_region_on P (length scheme)" by (rule hP_full)
    have hq_loc: "top1_quotient_map_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q"
      by (rule hq_full)
    have hlen_loc: "length scheme \<ge> 3" by (rule hlen_full)
    have hvert_loc: "\<forall>i<length scheme. (vx i, vy i) \<in> P" by (rule hvert_full)
    have hedge_loc: "\<forall>i<length scheme. \<forall>j<length scheme. fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
            (1-t) * vy i + t * vy (Suc i mod length scheme))
         = (if snd (scheme!i) = snd (scheme!j)
            then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                    (1-t) * vy j + t * vy (Suc j mod length scheme))
            else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                    t * vy j + (1-t) * vy (Suc j mod length scheme))))"
      by (rule hedge_full)
    have hinterior_loc: "\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
          p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                (1-t) * vy i + t * vy (Suc i mod length scheme)))
       \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
      by (rule hinterior_full)
    have hno_extra: "\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
          q ((1-t) * vx i + t * vx (Suc i mod length scheme),
             (1-t) * vy i + t * vy (Suc i mod length scheme))
        = q ((1-s) * vx j + s * vx (Suc j mod length scheme),
             (1-s) * vy j + s * vy (Suc j mod length scheme))
        \<longrightarrow> (i = j \<and> t = s)
          \<or> (fst (scheme!i) = fst (scheme!j) \<and>
             (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
      by (rule hno_extra_full)
    let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
    \<comment> \<open>Step 1: R^2 is Hausdorff.\<close>
    have hR_haus: "is_hausdorff_on (UNIV::real set) top1_open_sets"
      by (rule top1_R_is_hausdorff)
    have hR2_prod_haus: "\<And>X1 T1 X2 T2. is_hausdorff_on X1 T1 \<Longrightarrow> is_hausdorff_on X2 T2 \<Longrightarrow>
        is_hausdorff_on (X1 \<times> X2) (product_topology_on T1 T2)"
      using Theorem_17_11 by (by100 blast)
    have hR2_sub_haus: "\<And>X T Y. is_hausdorff_on X T \<Longrightarrow> Y \<subseteq> X \<Longrightarrow>
        is_hausdorff_on Y (subspace_topology X T Y)"
      using Theorem_17_11 by (by100 blast)
    have hR2_haus: "is_hausdorff_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
      by (rule hR2_prod_haus[OF hR_haus hR_haus, simplified])
    have hP_haus: "is_hausdorff_on P ?TP"
      by (rule hR2_sub_haus[OF hR2_haus]) (by100 blast)
    \<comment> \<open>Step 2: The full Hausdorff argument for the quotient.\<close>
    \<comment> \<open>The equivalence relation R = {(a,b)\<in>P\<times>P | q a = q b} is closed in P\<times>P.
       For polygonal quotients: R is a finite union of pairs of boundary segments,
       each compact (continuous image of [0,1]), hence closed.
       Closed R on compact Hausdorff P \<Rightarrow> P/R Hausdorff.\<close>
    have hR_closed: "closedin_on (P \<times> P)
        (product_topology_on ?TP ?TP)
        {(a, b). a \<in> P \<and> b \<in> P \<and> q a = q b}"
    proof -
      let ?n = "length scheme"
      let ?R = "{(a, b). a \<in> P \<and> b \<in> P \<and> q a = q b}"
      \<comment> \<open>Define boundary: the union of all edges.\<close>
      let ?edge = "\<lambda>i t. ((1-t) * vx i + t * vx (Suc i mod ?n),
                          (1-t) * vy i + t * vy (Suc i mod ?n))"
      let ?bdy = "\<Union>i\<in>{..<length scheme}. ?edge i ` I_set"
      \<comment> \<open>Interior points have singleton q-fibers (from hinterior\_loc).\<close>
      \<comment> \<open>So R \<subseteq> diagonal \<union> (?bdy \<times> ?bdy).\<close>
      have hR_sub: "?R \<subseteq> {(a, b). a \<in> P \<and> b \<in> P \<and> a = b} \<union> (?bdy \<times> ?bdy)"
      proof
        fix x assume "x \<in> ?R"
        then obtain a b where hx: "x = (a, b)" "a \<in> P" "b \<in> P" "q a = q b"
          by (cases x) (by100 blast)
        show "x \<in> {(a, b). a \<in> P \<and> b \<in> P \<and> a = b} \<union> (?bdy \<times> ?bdy)"
        proof (cases "a = b")
          case True thus ?thesis using hx by (by100 blast)
        next
          case False
          have "a \<in> ?bdy"
          proof (rule ccontr)
            assume "a \<notin> ?bdy"
            hence "\<forall>i<length scheme. \<forall>t\<in>I_set. a \<noteq> ?edge i t" by (by100 blast)
            from hinterior_loc hx(2) this hx(3) hx(4)
            have "a = b" by (by100 blast)
            thus False using False by (by100 simp)
          qed
          have "b \<in> ?bdy"
          proof (rule ccontr)
            assume "b \<notin> ?bdy"
            hence "\<forall>i<length scheme. \<forall>t\<in>I_set. b \<noteq> ?edge i t" by (by100 blast)
            from hinterior_loc hx(3) this hx(2) hx(4)[symmetric]
            have "b = a" by (by100 blast)
            thus False using False by (by100 simp)
          qed
          from \<open>a \<in> ?bdy\<close> \<open>b \<in> ?bdy\<close> show ?thesis using hx(1) by (by100 blast)
        qed
      qed
      \<comment> \<open>The diagonal is closed (P\<times>P Hausdorff, equalizer of pi1, pi2).\<close>
      have hPP_haus: "is_hausdorff_on (P \<times> P) (product_topology_on ?TP ?TP)"
        using hR2_prod_haus[OF hP_haus hP_haus] .
      have hTP_top: "is_topology_on P ?TP"
        using hP_haus unfolding is_hausdorff_on_def by (by100 blast)
      have hTPP: "is_topology_on (P \<times> P) (product_topology_on ?TP ?TP)"
        by (rule product_topology_on_is_topology_on[OF hTP_top hTP_top])
      have hpi1_cont: "top1_continuous_map_on (P \<times> P) (product_topology_on ?TP ?TP) P ?TP pi1"
        by (rule top1_continuous_pi1[OF hTP_top hTP_top])
      have hpi2_cont: "top1_continuous_map_on (P \<times> P) (product_topology_on ?TP ?TP) P ?TP pi2"
        by (rule top1_continuous_pi2[OF hTP_top hTP_top])
      have hDiag_eq: "{(a, b). a \<in> P \<and> b \<in> P \<and> a = b}
          = {x \<in> P \<times> P. pi1 x = pi2 x}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {(a, b). a \<in> P \<and> b \<in> P \<and> a = b}"
        then obtain a b where "x = (a, b)" "a \<in> P" "b \<in> P" "a = b" by (by100 blast)
        thus "x \<in> {x \<in> P \<times> P. pi1 x = pi2 x}" unfolding pi1_def pi2_def by (by100 simp)
      next
        fix x assume "x \<in> {x \<in> P \<times> P. pi1 x = pi2 x}"
        hence "x \<in> P \<times> P" "pi1 x = pi2 x" by (by100 blast)+
        then obtain a b where "x = (a, b)" "a \<in> P" "b \<in> P" by (by100 blast)
        have "a = b" using \<open>pi1 x = pi2 x\<close> \<open>x = (a, b)\<close> unfolding pi1_def pi2_def by (by100 simp)
        thus "x \<in> {(a, b). a \<in> P \<and> b \<in> P \<and> a = b}" using \<open>a \<in> P\<close> \<open>b \<in> P\<close> \<open>x = (a, b)\<close> by (by100 blast)
      qed
      have hDiag_closed: "closedin_on (P \<times> P) (product_topology_on ?TP ?TP)
          {(a, b). a \<in> P \<and> b \<in> P \<and> a = b}"
      proof -
        have "closedin_on (P \<times> P) (product_topology_on ?TP ?TP)
            {x \<in> P \<times> P. pi1 x = pi2 x}"
          by (rule top1_closedin_equalizer_of_continuous_maps[OF hTPP hP_haus hpi1_cont hpi2_cont])
        thus ?thesis using hDiag_eq by (by100 simp)
      qed
      \<comment> \<open>?bdy \<times> ?bdy is compact (each edge is compact image of [0,1],
         finite union of compact = compact, product of compact = compact).\<close>
      \<comment> \<open>Boundary compact: each edge is compact image of [0,1], finite union compact.\<close>
      \<comment> \<open>P is compact (polygonal region = convex hull).\<close>
      have hP_compact_here: "top1_compact_on P ?TP"
      proof -
        have hTP_eq: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
          using product_topology_on_open_sets_real2 by (by100 simp)
        have "compact P"
        proof -
          obtain vx' vy' :: "nat \<Rightarrow> real" where hn': "length scheme \<ge> 3"
              and hP_eq: "P = {(x, y). \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
                  \<and> (\<Sum>i<length scheme. coeffs i) = 1
                  \<and> x = (\<Sum>i<length scheme. coeffs i * vx' i)
                  \<and> y = (\<Sum>i<length scheme. coeffs i * vy' i)}"
            using hP_loc unfolding top1_is_polygonal_region_on_def by blast
          show "compact P" unfolding hP_eq by (rule convex_hull_compact[OF hn'])
        qed
        hence "top1_compact_on P (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets P)"
          using iffD2[OF top1_compact_on_subspace_UNIV_iff_compact] by (by100 blast)
        thus ?thesis using hTP_eq by (by100 simp)
      qed
      have hbdy_sub_P: "?bdy \<subseteq> P"
      proof
        fix x assume "x \<in> ?bdy"
        then obtain i t where hi: "i < length scheme" "t \<in> I_set" "x = ?edge i t"
          by (by100 blast)
        have ht: "t \<ge> 0" "t \<le> 1" using \<open>t \<in> I_set\<close> unfolding top1_unit_interval_def
          by (by100 simp)+
        have hvi: "(vx i, vy i) \<in> P" using hvert_loc hi(1) by (by100 blast)
        have hj: "Suc i mod length scheme < length scheme"
        proof -
          have "length scheme > 0" using hlen_loc by (by100 linarith)
          thus ?thesis by (by100 simp)
        qed
        have hvi1: "(vx (Suc i mod length scheme), vy (Suc i mod length scheme)) \<in> P"
          using hvert_loc hj by (by100 blast)
        \<comment> \<open>P is convex hull: (1-t)*v_i + t*v_{i+1} is in P for t \<in> [0,1].\<close>
        show "x \<in> P"
        proof -
          \<comment> \<open>Define coefficients: all zero except i and (i+1 mod n).\<close>
          obtain vx' vy' where hP_eq: "P = {(x, y). \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
              \<and> (\<Sum>i<length scheme. coeffs i) = 1
              \<and> x = (\<Sum>i<length scheme. coeffs i * vx' i)
              \<and> y = (\<Sum>i<length scheme. coeffs i * vy' i)}"
            using hP_loc unfolding top1_is_polygonal_region_on_def by blast
          \<comment> \<open>From hvi and hvi1: vertices are in P, so the edge point is too.\<close>
          \<comment> \<open>v_i and v_{i+1} are in P (convex hull). P is convex, so
             (1-t)*v_i + t*v_{i+1} \<in> P. Proof: combine coefficients.\<close>
          from hvi obtain c1 where hc1: "\<forall>j<length scheme. c1 j \<ge> 0"
              "(\<Sum>j<length scheme. c1 j) = 1"
              "fst (vx i, vy i) = (\<Sum>j<length scheme. c1 j * vx' j)"
              "snd (vx i, vy i) = (\<Sum>j<length scheme. c1 j * vy' j)"
            unfolding hP_eq by auto
          from hvi1 obtain c2 where hc2: "\<forall>j<length scheme. c2 j \<ge> 0"
              "(\<Sum>j<length scheme. c2 j) = 1"
              "fst (vx (Suc i mod length scheme), vy (Suc i mod length scheme)) = (\<Sum>j<length scheme. c2 j * vx' j)"
              "snd (vx (Suc i mod length scheme), vy (Suc i mod length scheme)) = (\<Sum>j<length scheme. c2 j * vy' j)"
            unfolding hP_eq by auto
          let ?c = "\<lambda>j. (1-t) * c1 j + t * c2 j"
          have hc_nn: "\<forall>j<length scheme. ?c j \<ge> 0"
          proof (intro allI impI)
            fix j assume "j < length scheme"
            have "c1 j \<ge> 0" using hc1(1) \<open>j < length scheme\<close> by (by100 blast)
            have "c2 j \<ge> 0" using hc2(1) \<open>j < length scheme\<close> by (by100 blast)
            show "?c j \<ge> 0" using \<open>c1 j \<ge> 0\<close> \<open>c2 j \<ge> 0\<close> ht by (by100 simp)
          qed
          have hc_sum: "(\<Sum>j<length scheme. ?c j) = 1"
          proof -
            have "(\<Sum>j<length scheme. ?c j) = (\<Sum>j<length scheme. (1-t) * c1 j) + (\<Sum>j<length scheme. t * c2 j)"
              by (simp add: sum.distrib)
            also have "\<dots> = (1-t) * (\<Sum>j<length scheme. c1 j) + t * (\<Sum>j<length scheme. c2 j)"
              by (simp add: sum_distrib_left)
            finally show ?thesis using hc1(2) hc2(2) ht by (by100 simp)
          qed
          have hc_x: "fst (?edge i t) = (\<Sum>j<length scheme. ?c j * vx' j)"
          proof -
            have "(\<Sum>j<length scheme. ?c j * vx' j) =
                (\<Sum>j<length scheme. (1-t) * c1 j * vx' j) + (\<Sum>j<length scheme. t * c2 j * vx' j)"
              by (simp add: sum.distrib ring_distribs)
            also have "\<dots> = (1-t) * (\<Sum>j<length scheme. c1 j * vx' j) + t * (\<Sum>j<length scheme. c2 j * vx' j)"
              by (simp add: sum_distrib_left mult.assoc)
            finally show ?thesis using hc1(3) hc2(3) by (by100 simp)
          qed
          have hc_y: "snd (?edge i t) = (\<Sum>j<length scheme. ?c j * vy' j)"
          proof -
            have "(\<Sum>j<length scheme. ?c j * vy' j) =
                (\<Sum>j<length scheme. (1-t) * c1 j * vy' j) + (\<Sum>j<length scheme. t * c2 j * vy' j)"
              by (simp add: sum.distrib ring_distribs)
            also have "\<dots> = (1-t) * (\<Sum>j<length scheme. c1 j * vy' j) + t * (\<Sum>j<length scheme. c2 j * vy' j)"
              by (simp add: sum_distrib_left mult.assoc)
            finally show ?thesis using hc1(4) hc2(4) by (by100 simp)
          qed
          show ?thesis unfolding hP_eq hi(3)
            using hc_nn hc_sum hc_x hc_y by auto
        qed
      qed
      have hbdy_closed_P: "closedin_on P ?TP ?bdy"
      proof -
        \<comment> \<open>Each edge is compact in R^2 (continuous image of [0,1]).\<close>
        have "compact ?bdy"
        proof -
          have "\<forall>i \<in> {..<length scheme}. compact (?edge i ` I_set)"
          proof (intro ballI)
            fix i assume "i \<in> {..<length scheme}"
            let ?f = "\<lambda>t::real. ((1-t) * vx i + t * vx (Suc i mod length scheme),
                (1-t) * vy i + t * vy (Suc i mod length scheme))"
            have "continuous_on UNIV ?f" by (intro continuous_intros)
            hence "continuous_on I_set ?f"
              using continuous_on_subset by (by100 blast)
            moreover have "compact I_set"
              unfolding top1_unit_interval_def by (by100 simp)
            ultimately have "compact (?f ` I_set)" by (rule compact_continuous_image)
            moreover have "?f ` I_set = ?edge i ` I_set" by (by100 simp)
            ultimately show "compact (?edge i ` I_set)" by (by100 simp)
          qed
          moreover have "finite {..<length scheme}" by (by100 simp)
          ultimately show "compact ?bdy"
          proof -
            assume hcomp: "\<forall>i \<in> {..<length scheme}. compact (?edge i ` I_set)"
            assume hfin: "finite {..<length scheme}"
            show ?thesis
              unfolding UN_simps
              apply (rule compact_Union)
              apply (rule finite_imageI[OF hfin])
              using hcomp by (by100 blast)
          qed
        qed
        \<comment> \<open>compact in Hausdorff P \<Rightarrow> closed in P.\<close>
        have "top1_compact_on ?bdy (subspace_topology P ?TP ?bdy)"
        proof -
          have hTP_eq: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
            using product_topology_on_open_sets_real2 by (by100 simp)
          have "top1_compact_on ?bdy (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets ?bdy)"
            using iffD2[OF top1_compact_on_subspace_UNIV_iff_compact] \<open>compact ?bdy\<close> by (by100 blast)
          moreover have "subspace_topology (UNIV::(real\<times>real) set) top1_open_sets ?bdy
              = subspace_topology P ?TP ?bdy"
          proof -
            have "subspace_topology P (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets P) ?bdy
                = subspace_topology (UNIV::(real\<times>real) set) top1_open_sets ?bdy"
              by (rule subspace_topology_trans[OF hbdy_sub_P])
            thus ?thesis using hTP_eq by (by100 simp)
          qed
          ultimately show ?thesis by simp
        qed
        thus ?thesis
          by (rule Theorem_26_3[OF hP_haus hbdy_sub_P])
      qed
      have hbdy_compact_P: "top1_compact_on ?bdy (subspace_topology P ?TP ?bdy)"
        by (rule Theorem_26_2[OF hP_compact_here hbdy_closed_P])
      have hbdy_compact: "top1_compact_on (?bdy \<times> ?bdy)
          (subspace_topology (P \<times> P) (product_topology_on ?TP ?TP) (?bdy \<times> ?bdy))"
      proof -
        have "top1_compact_on (?bdy \<times> ?bdy)
            (product_topology_on (subspace_topology P ?TP ?bdy) (subspace_topology P ?TP ?bdy))"
          by (rule Theorem_26_7[OF hbdy_compact_P hbdy_compact_P])
        moreover have "product_topology_on (subspace_topology P ?TP ?bdy) (subspace_topology P ?TP ?bdy)
            = subspace_topology (P \<times> P) (product_topology_on ?TP ?TP) (?bdy \<times> ?bdy)"
          by (rule Theorem_16_3[OF hTP_top hTP_top])
        ultimately show ?thesis by simp
      qed
      \<comment> \<open>?R \<inter> (?bdy \<times> ?bdy) is compact: it's a finite union of edge-pair identification
         sets, each compact (image of [0,1] under continuous map t \<mapsto> (edge\_i(t), edge\_j(f(t)))).\<close>
      have hR_bdy_compact: "top1_compact_on (?R \<inter> (?bdy \<times> ?bdy))
          (subspace_topology (P \<times> P) (product_topology_on ?TP ?TP) (?R \<inter> (?bdy \<times> ?bdy)))"
      proof -
        \<comment> \<open>Step 1: compact ?bdy in HOL-Analysis.\<close>
        have hbdy_compact_HA: "compact ?bdy"
        proof -
          have "\<forall>i \<in> {..<length scheme}. compact (?edge i ` I_set)"
          proof (intro ballI)
            fix i assume "i \<in> {..<length scheme}"
            let ?f = "\<lambda>t::real. ((1-t) * vx i + t * vx (Suc i mod length scheme),
                (1-t) * vy i + t * vy (Suc i mod length scheme))"
            have "continuous_on UNIV ?f" by (intro continuous_intros)
            hence "continuous_on I_set ?f" using continuous_on_subset by (by100 blast)
            moreover have "compact I_set" unfolding top1_unit_interval_def by (by100 simp)
            ultimately have "compact (?f ` I_set)" by (rule compact_continuous_image)
            moreover have "?f ` I_set = ?edge i ` I_set" by (by100 simp)
            ultimately show "compact (?edge i ` I_set)" by (by100 simp)
          qed
          hence hcomp_all: "\<forall>S \<in> (\<lambda>i. ?edge i ` I_set) ` {..<length scheme}. compact S" by (by100 blast)
          have hfin_set: "finite ((\<lambda>i. ?edge i ` I_set) ` {..<length scheme})" by (by100 simp)
          have "compact (\<Union> ((\<lambda>i. ?edge i ` I_set) ` {..<length scheme}))"
            by (rule compact_Union[OF hfin_set hcomp_all])
          moreover have "\<Union> ((\<lambda>i. ?edge i ` I_set) ` {..<length scheme}) = ?bdy" by (by100 auto)
          ultimately show "compact ?bdy" by (by100 simp)
        qed
        \<comment> \<open>Step 2: compact (bdy \<times> bdy) via compact\_Times\_general.\<close>
        have hbdybdy_compact_HA: "compact (?bdy \<times> ?bdy)"
          by (rule compact_Times_general[OF hbdy_compact_HA hbdy_compact_HA])
        \<comment> \<open>Step 3: R \<inter> bdy\<times>bdy \<subseteq> bdy\<times>bdy, and bdy\<times>bdy is compact,
           so R\<inter>bdy\<times>bdy is bounded. Need closedness to get compactness.\<close>
        \<comment> \<open>Alternative: show R\<inter>bdy\<times>bdy is ITSELF a finite union of compact sets.\<close>
        have "compact (?R \<inter> (?bdy \<times> ?bdy))"
        proof -
          \<comment> \<open>R\<inter>bdy\<times>bdy \<subseteq> diagonal\_on\_bdy \<union> edge\_pair\_curves.\<close>
          \<comment> \<open>Each curve is compact (continuous image of compact [0,1]).\<close>
          \<comment> \<open>Diagonal on bdy: image of bdy under x\<mapsto>(x,x). Compact.\<close>
          let ?D = "(\<lambda>x. (x, x)) ` ?bdy"
          have hD_compact: "compact ?D"
          proof -
            have "continuous_on ?bdy (\<lambda>x. (x, x))" by (intro continuous_intros)
            thus ?thesis using compact_continuous_image hbdy_compact_HA by (by100 blast)
          qed
          \<comment> \<open>Edge pair curves: for each (i,j) with same label.\<close>
          \<comment> \<open>?R \<inter> (?bdy \<times> ?bdy) \<subseteq> ?D \<union> (edge pair curves). Plus reverse.\<close>
          \<comment> \<open>Since both directions need the scheme structure,\<close>
          \<comment> \<open>we show R\<inter>bdy\<times>bdy is closed in the compact bdy\<times>bdy.\<close>
          \<comment> \<open>R\<inter>bdy\<times>bdy closed: equal to ?D \<union> finite union of compact sets.\<close>
          \<comment> \<open>?D compact \<Rightarrow> closed (in Hausdorff R^4). Each edge pair compact \<Rightarrow> closed.\<close>
          \<comment> \<open>Finite union of closed = closed. Closed subset of compact = compact.\<close>
          have hR_bdy_closed_HA: "closed (?R \<inter> (?bdy \<times> ?bdy))"
          proof -
            \<comment> \<open>R\<inter>bdy\<times>bdy = D \<union> \<Union>{C\_ij | same label}.\<close>
            \<comment> \<open>D = diagonal on bdy (compact \<Rightarrow> closed). Each C\_ij compact \<Rightarrow> closed.\<close>
            \<comment> \<open>Finite union of closed = closed.\<close>
            \<comment> \<open>Define edge pair curves.\<close>
            let ?n = "length scheme"
            let ?curves = "(\<lambda>(i,j). if fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j
                then (if snd (scheme!i) = snd (scheme!j)
                      then (\<lambda>t. (?edge i t, ?edge j t)) ` I_set
                      else (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set)
                else {}) ` ({..<?n} \<times> {..<?n})"
            \<comment> \<open>R\<inter>bdy\<times>bdy \<subseteq> ?D \<union> \<Union>?curves.\<close>
            have hR_bdy_sub_DC: "?R \<inter> (?bdy \<times> ?bdy) \<subseteq> ?D \<union> \<Union>?curves"
            proof
              fix x assume "x \<in> ?R \<inter> (?bdy \<times> ?bdy)"
              then obtain a b where hx: "x = (a, b)" "a \<in> P" "b \<in> P" "q a = q b"
                  "a \<in> ?bdy" "b \<in> ?bdy"
                by (cases x) (by100 blast)
              \<comment> \<open>a on some edge i at parameter t, b on edge j at parameter s.\<close>
              from hx(5) obtain i t where hi: "i < length scheme" "t \<in> I_set" "a = ?edge i t"
                by (by100 blast)
              from hx(6) obtain j s where hj: "j < length scheme" "s \<in> I_set" "b = ?edge j s"
                by (by100 blast)
              \<comment> \<open>Apply hno\_extra: q(edge\_i(t)) = q(edge\_j(s)) \<Rightarrow> diagonal or scheme pair.\<close>
              from hno_extra[rule_format, OF hi(1) hj(1) hi(2) hj(2)]
              have "q a = q b \<longrightarrow> (i = j \<and> t = s) \<or> (fst (scheme!i) = fst (scheme!j) \<and>
                  (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
                using hi(3) hj(3) by simp
              hence "(i = j \<and> t = s) \<or> (fst (scheme!i) = fst (scheme!j) \<and>
                  (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
                using hx(4) by (by100 blast)
              thus "x \<in> ?D \<union> \<Union>?curves"
              proof
                assume "i = j \<and> t = s"
                hence "a = b" using hi(3) hj(3) by (by100 simp)
                thus ?thesis using hx(1,5) by (by100 blast)
              next
                assume hpair: "fst (scheme!i) = fst (scheme!j) \<and>
                    (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t)"
                show ?thesis
                proof (cases "i = j")
                  case True
                  hence "t = s" using hpair by (by100 auto)
                  hence "a = b" using hi(3) hj(3) True by (by100 simp)
                  thus ?thesis using hx(1,5) by (by100 blast)
                next
                  case False
                  \<comment> \<open>(a,b) is on an edge pair curve.\<close>
                  \<comment> \<open>(a,b) = (edge\_i(t), edge\_j(s)) with same label and s = f(t).\<close>
                  have "fst (scheme!i) = fst (scheme!j)" using hpair by (by100 blast)
                  show ?thesis
                  proof (cases "snd (scheme!i) = snd (scheme!j)")
                    case True
                    hence "s = t" using hpair by (by100 auto)
                    hence "x = (?edge i t, ?edge j t)" using hx(1) hi(3) hj(3) by (by100 simp)
                    hence "x \<in> (\<lambda>t. (?edge i t, ?edge j t)) ` I_set" using hi(2) by auto
                    moreover have "(\<lambda>t. (?edge i t, ?edge j t)) ` I_set \<in> ?curves"
                    proof -
                      have "(i, j) \<in> {..<length scheme} \<times> {..<length scheme}"
                        using hi(1) hj(1) by (by100 blast)
                      moreover have "(case (i, j) of (i, j) \<Rightarrow>
                          if fst (scheme ! i) = fst (scheme ! j) \<and> i \<noteq> j
                          then (if snd (scheme ! i) = snd (scheme ! j)
                                then (\<lambda>t. (?edge i t, ?edge j t)) ` I_set
                                else (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set)
                          else {}) = (\<lambda>t. (?edge i t, ?edge j t)) ` I_set"
                        using \<open>fst (scheme!i) = fst (scheme!j)\<close> False True by (by100 simp)
                      ultimately show ?thesis
                        apply -
                        apply (rule image_eqI[where x="(i,j)"])
                        apply (by100 simp)
                        apply (by100 blast)
                        done
                    qed
                    hence "x \<in> \<Union>?curves" using \<open>x \<in> (\<lambda>t. (?edge i t, ?edge j t)) ` I_set\<close>
                      by blast
                    thus ?thesis by blast
                  next
                    case sndF: False
                    hence "s = 1 - t" using hpair by (by100 auto)
                    hence "x = (?edge i t, ?edge j (1-t))" using hx(1) hi(3) hj(3) by simp
                    hence hx_in: "x \<in> (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set" using hi(2) by auto
                    have "(\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set \<in> ?curves"
                    proof -
                      have "(i, j) \<in> {..<length scheme} \<times> {..<length scheme}"
                        using hi(1) hj(1) by (by100 blast)
                      moreover have "(case (i, j) of (i, j) \<Rightarrow>
                          if fst (scheme ! i) = fst (scheme ! j) \<and> i \<noteq> j
                          then (if snd (scheme ! i) = snd (scheme ! j)
                                then (\<lambda>t. (?edge i t, ?edge j t)) ` I_set
                                else (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set)
                          else {}) = (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set"
                        using \<open>fst (scheme!i) = fst (scheme!j)\<close> False sndF by (by100 simp)
                      ultimately show ?thesis
                        apply -
                        apply (rule image_eqI[where x="(i,j)"])
                        apply (by100 simp)
                        apply (by100 blast)
                        done
                    qed
                    hence "x \<in> \<Union>?curves" using hx_in by blast
                    thus ?thesis by blast
                  qed
                qed
              qed
            qed
            \<comment> \<open>?D \<union> \<Union>?curves \<subseteq> ?R \<inter> (?bdy\<times>?bdy).\<close>
            have hDC_sub_R_bdy: "?D \<union> \<Union>?curves \<subseteq> ?R \<inter> (?bdy \<times> ?bdy)"
            proof
              fix x assume "x \<in> ?D \<union> \<Union>?curves"
              thus "x \<in> ?R \<inter> (?bdy \<times> ?bdy)"
              proof
                \<comment> \<open>Case 1: x \<in> ?D (diagonal on boundary).\<close>
                assume "x \<in> ?D"
                then obtain a where ha: "a \<in> ?bdy" "x = (a, a)" by (by100 blast)
                have "a \<in> P" using ha(1) hbdy_sub_P by (by100 blast)
                thus "x \<in> ?R \<inter> (?bdy \<times> ?bdy)" using ha by (by100 blast)
              next
                \<comment> \<open>Case 2: x \<in> \<Union>?curves (edge pair curve).\<close>
                assume "x \<in> \<Union>?curves"
                then obtain C where "C \<in> ?curves" "x \<in> C" by (by100 blast)
                then obtain i j where hij: "i < ?n" "j < ?n"
                    "C = (if fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j
                          then (if snd (scheme!i) = snd (scheme!j)
                                then (\<lambda>t. (?edge i t, ?edge j t)) ` I_set
                                else (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set)
                          else {})" by auto
                show "x \<in> ?R \<inter> (?bdy \<times> ?bdy)"
                proof (cases "fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j")
                  case False thus ?thesis using \<open>x \<in> C\<close> hij(3) by auto
                next
                  case True
                  hence hsamelabel: "fst (scheme!i) = fst (scheme!j)" by (by100 blast)
                  show ?thesis
                  proof (cases "snd (scheme!i) = snd (scheme!j)")
                    case True
                    \<comment> \<open>Same direction: x = (edge\_i(t), edge\_j(t)).\<close>
                    then obtain t where ht: "t \<in> I_set" "x = (?edge i t, ?edge j t)"
                      using \<open>x \<in> C\<close> hij(3) \<open>fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j\<close> by auto
                    have "q (?edge i t) = q (?edge j t)"
                    proof -
                      have "\<forall>t\<in>I_set. q (?edge i t) =
                          (if snd (scheme!i) = snd (scheme!j) then q (?edge j t) else q (?edge j (1-t)))"
                      proof (intro ballI)
                        fix t assume "t \<in> I_set"
                        show "q (?edge i t) = (if snd (scheme!i) = snd (scheme!j) then q (?edge j t) else q (?edge j (1-t)))"
                          using hedge_loc[rule_format, OF hij(1) hij(2) hsamelabel \<open>t \<in> I_set\<close>] by simp
                      qed
                      thus ?thesis using True ht(1) by (by100 simp)
                    qed
                    moreover have hei: "?edge i t \<in> ?bdy" using hij(1) ht(1) by (by100 blast)
                    moreover have hej: "?edge j t \<in> ?bdy" using hij(2) ht(1) by (by100 blast)
                    moreover have "?edge i t \<in> P" using subsetD[OF hbdy_sub_P hei] .
                    moreover have "?edge j t \<in> P" using subsetD[OF hbdy_sub_P hej] .
                    ultimately show ?thesis using ht(2) by auto
                  next
                    case False
                    \<comment> \<open>Opposite direction: x = (edge\_i(t), edge\_j(1-t)).\<close>
                    then obtain t where ht: "t \<in> I_set" "x = (?edge i t, ?edge j (1-t))"
                      using \<open>x \<in> C\<close> hij(3) \<open>fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j\<close> by auto
                    have "q (?edge i t) = q (?edge j (1-t))"
                    proof -
                      have "\<forall>t\<in>I_set. q (?edge i t) =
                          (if snd (scheme!i) = snd (scheme!j) then q (?edge j t) else q (?edge j (1-t)))"
                      proof (intro ballI)
                        fix t assume "t \<in> I_set"
                        show "q (?edge i t) = (if snd (scheme!i) = snd (scheme!j) then q (?edge j t) else q (?edge j (1-t)))"
                          using hedge_loc[rule_format, OF hij(1) hij(2) hsamelabel \<open>t \<in> I_set\<close>] by simp
                      qed
                      thus ?thesis using False ht(1) by (by100 simp)
                    qed
                    moreover have hei2: "?edge i t \<in> ?bdy" using hij(1) ht(1) by (by100 blast)
                    moreover have h1t_I: "1 - t \<in> I_set" using ht(1) unfolding top1_unit_interval_def by auto
                    moreover have hej2: "?edge j (1-t) \<in> ?bdy" using hij(2) h1t_I by (by100 blast)
                    moreover have "?edge i t \<in> P" using subsetD[OF hbdy_sub_P hei2] .
                    moreover have "?edge j (1-t) \<in> P" using subsetD[OF hbdy_sub_P hej2] .
                    ultimately show ?thesis using ht(2) by auto
                  qed
                qed
              qed
            qed
            \<comment> \<open>So ?R \<inter> (?bdy \<times> ?bdy) = ?D \<union> \<Union>?curves.\<close>
            have hR_bdy_eq: "?R \<inter> (?bdy \<times> ?bdy) = ?D \<union> \<Union>?curves"
              using hR_bdy_sub_DC hDC_sub_R_bdy by (by100 blast)
            \<comment> \<open>?D is closed (compact \<Rightarrow> closed in R^4).\<close>
            have hD_closed: "closed ?D"
              using hD_compact compact_imp_closed by (by100 blast)
            \<comment> \<open>Each curve in ?curves is closed (compact \<Rightarrow> closed).\<close>
            have hcurves_closed: "\<forall>C \<in> ?curves. closed C"
            proof (intro ballI)
              fix C assume "C \<in> ?curves"
              then obtain i j where hij: "C = (if fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j
                  then (if snd (scheme!i) = snd (scheme!j)
                        then (\<lambda>t. (?edge i t, ?edge j t)) ` I_set
                        else (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set)
                  else {})" "i < ?n" "j < ?n" by auto
              show "closed C"
              proof (cases "fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j")
                case False thus ?thesis using hij(1) by auto
              next
                case True
                have "compact C"
                proof (cases "snd (scheme!i) = snd (scheme!j)")
                  case True
                  hence hC_eq: "C = (\<lambda>t. (?edge i t, ?edge j t)) ` I_set"
                    using hij(1) \<open>fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j\<close> by (by100 auto)
                  have "continuous_on UNIV (\<lambda>t::real. (?edge i t, ?edge j t))"
                    by (intro continuous_intros)
                  hence "continuous_on I_set (\<lambda>t. (?edge i t, ?edge j t))"
                    using continuous_on_subset by (by100 blast)
                  moreover have "compact I_set" unfolding top1_unit_interval_def by (by100 simp)
                  ultimately show ?thesis unfolding hC_eq by (rule compact_continuous_image)
                next
                  case False
                  hence hC_eq: "C = (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set"
                    using hij(1) \<open>fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j\<close> by (by100 auto)
                  have "continuous_on UNIV (\<lambda>t::real. (?edge i t, ?edge j (1-t)))"
                    by (intro continuous_intros)
                  hence "continuous_on I_set (\<lambda>t. (?edge i t, ?edge j (1-t)))"
                    using continuous_on_subset by (by100 blast)
                  moreover have "compact I_set" unfolding top1_unit_interval_def by (by100 simp)
                  ultimately show ?thesis unfolding hC_eq by (rule compact_continuous_image)
                qed
                thus ?thesis using compact_imp_closed by (by100 blast)
              qed
            qed
            \<comment> \<open>Finite union of closed = closed.\<close>
            have "finite ?curves" by (by100 simp)
            have "closed (\<Union>?curves)"
              by (rule closed_Union[OF \<open>finite ?curves\<close> hcurves_closed])
            thus ?thesis using hR_bdy_eq hD_closed by auto
          qed
          from compact_Int_closed[OF hbdybdy_compact_HA hR_bdy_closed_HA]
          have "compact ((?bdy \<times> ?bdy) \<inter> (?R \<inter> (?bdy \<times> ?bdy)))" .
          moreover have "(?bdy \<times> ?bdy) \<inter> (?R \<inter> (?bdy \<times> ?bdy)) = ?R \<inter> (?bdy \<times> ?bdy)" by auto
          ultimately show "compact (?R \<inter> (?bdy \<times> ?bdy))" by simp
        qed
        \<comment> \<open>Step 4: Bridge compact to top1\_compact\_on.\<close>
        hence "top1_compact_on (?R \<inter> (?bdy \<times> ?bdy))
            (subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set)
                top1_open_sets (?R \<inter> (?bdy \<times> ?bdy)))"
          using iffD2[OF top1_compact_on_subspace_UNIV_iff_compact] by (by100 blast)
        moreover have "subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set)
            top1_open_sets (?R \<inter> (?bdy \<times> ?bdy))
            = subspace_topology (P \<times> P) (product_topology_on ?TP ?TP) (?R \<inter> (?bdy \<times> ?bdy))"
        proof -
          have hTP_eq: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
            using product_topology_on_open_sets_real2 by (by100 simp)
          have hTP_eq_sub: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
            using product_topology_on_open_sets_real2 by (by100 simp)
          have "product_topology_on ?TP ?TP =
              subspace_topology ((UNIV::(real\<times>real) set) \<times> (UNIV::(real\<times>real) set))
                  (product_topology_on top1_open_sets top1_open_sets) (P \<times> P)"
          proof -
            have hT_R2: "is_topology_on (UNIV::(real\<times>real) set) top1_open_sets"
              by (rule top1_open_sets_is_topology_on_UNIV)
            show ?thesis using Theorem_16_3[OF hT_R2 hT_R2] hTP_eq_sub by simp
          qed
          also have "subspace_topology ((UNIV::(real\<times>real) set) \<times> (UNIV::(real\<times>real) set))
                  (product_topology_on top1_open_sets top1_open_sets) (P \<times> P)
              = subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set) top1_open_sets (P \<times> P)"
          proof -
            have h1: "(UNIV::(real\<times>real) set) \<times> (UNIV::(real\<times>real) set) = (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set)"
              by (by100 simp)
            have h2: "product_topology_on (top1_open_sets::(real\<times>real) set set) (top1_open_sets::(real\<times>real) set set)
                = (top1_open_sets :: ((real \<times> real) \<times> (real \<times> real)) set set)"
              by (rule product_topology_on_open_sets)
            show ?thesis using h1 h2 by (by100 simp)
          qed
          finally have hPP_eq: "product_topology_on ?TP ?TP =
              subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set) top1_open_sets (P \<times> P)" .
          have hR_bdy_sub_PP: "?R \<inter> (?bdy \<times> ?bdy) \<subseteq> P \<times> P" by (by100 blast)
          have "subspace_topology (P \<times> P) (product_topology_on ?TP ?TP) (?R \<inter> (?bdy \<times> ?bdy))
              = subspace_topology (P \<times> P)
                  (subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set) top1_open_sets (P \<times> P))
                  (?R \<inter> (?bdy \<times> ?bdy))"
            using hPP_eq by (by100 simp)
          also have "\<dots> = subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set) top1_open_sets
              (?R \<inter> (?bdy \<times> ?bdy))"
            by (rule subspace_topology_trans[OF hR_bdy_sub_PP])
          finally show ?thesis by simp
        qed
        ultimately show ?thesis by simp
      qed
      \<comment> \<open>Compact in Hausdorff is closed.\<close>
      have hR_bdy_sub: "?R \<inter> (?bdy \<times> ?bdy) \<subseteq> P \<times> P" by (by100 blast)
      have hR_bdy_closed: "closedin_on (P \<times> P) (product_topology_on ?TP ?TP) (?R \<inter> (?bdy \<times> ?bdy))"
        by (rule Theorem_26_3[OF hPP_haus hR_bdy_sub hR_bdy_compact])
      \<comment> \<open>R \<subseteq> diagonal \<union> (?bdy \<times> ?bdy), so R = (R \<inter> diagonal) \<union> (R \<inter> (?bdy \<times> ?bdy)).
         R \<inter> diagonal = diagonal (on P\<times>P). Both parts closed. Union closed.\<close>
      have hR_decomp: "?R = {(a, b). a \<in> P \<and> b \<in> P \<and> a = b} \<union> (?R \<inter> (?bdy \<times> ?bdy))"
        using hR_sub by auto
      have "closedin_on (P \<times> P) (product_topology_on ?TP ?TP) ?R"
      proof -
        have "closedin_on (P \<times> P) (product_topology_on ?TP ?TP)
            ({(a, b). a \<in> P \<and> b \<in> P \<and> a = b} \<union> (?R \<inter> (?bdy \<times> ?bdy)))"
        proof -
          let ?F = "{{(a, b). a \<in> P \<and> b \<in> P \<and> a = b}, ?R \<inter> (?bdy \<times> ?bdy)}"
          have "finite ?F" by (by100 simp)
          have "\<forall>A \<in> ?F. closedin_on (P \<times> P) (product_topology_on ?TP ?TP) A"
            using hDiag_closed hR_bdy_closed by (by100 blast)
          from closedin_Union_finite[OF hTPP \<open>finite ?F\<close> this]
          have "closedin_on (P \<times> P) (product_topology_on ?TP ?TP) (\<Union>?F)" .
          moreover have "\<Union>?F = {(a, b). a \<in> P \<and> b \<in> P \<and> a = b} \<union> (?R \<inter> (?bdy \<times> ?bdy))"
            by (by100 simp)
          ultimately show ?thesis by auto
        qed
        thus ?thesis using hR_decomp by auto
      qed
      thus ?thesis .
    qed
    \<comment> \<open>Closed equivalence relation on compact Hausdorff \<Rightarrow> Hausdorff quotient.\<close>
    have hclosed_R_haus: "\<And>P' TP' X' TX' q'.
        is_hausdorff_on P' TP' \<Longrightarrow> top1_compact_on P' TP' \<Longrightarrow>
        top1_quotient_map_on P' TP' X' TX' q' \<Longrightarrow>
        closedin_on (P' \<times> P') (product_topology_on TP' TP')
            {(a, b). a \<in> P' \<and> b \<in> P' \<and> q' a = q' b} \<Longrightarrow>
        is_hausdorff_on X' TX'"
    proof -
      fix P' TP' X' TX' q'
      assume hP'H: "is_hausdorff_on P' TP'" and hP'C: "top1_compact_on P' TP'"
          and hq'Q: "top1_quotient_map_on P' TP' X' TX' q'"
          and hR'cl: "closedin_on (P' \<times> P') (product_topology_on TP' TP')
              {(a, b). a \<in> P' \<and> b \<in> P' \<and> q' a = q' b}"
      let ?R = "{(a, b). a \<in> P' \<and> b \<in> P' \<and> q' a = q' b}"
      have hTP': "is_topology_on P' TP'" using hP'H unfolding is_hausdorff_on_def by (by100 blast)
      have hTX': "is_topology_on X' TX'" using hq'Q unfolding top1_quotient_map_on_def by (by100 blast)
      have hq'_cont: "top1_continuous_map_on P' TP' X' TX' q'"
        using hq'Q unfolding top1_quotient_map_on_def by (by100 blast)
      have hq'_surj: "q' ` P' = X'" using hq'Q unfolding top1_quotient_map_on_def by (by100 blast)
      \<comment> \<open>P' compact Hausdorff \<Rightarrow> normal.\<close>
      have hP'N: "top1_normal_on P' TP'" by (rule Theorem_32_3[OF hP'C hP'H])
      show "is_hausdorff_on X' TX'" unfolding is_hausdorff_on_def
      proof (intro conjI)
        show "is_topology_on X' TX'" by (rule hTX')
      next
        show "\<forall>x\<in>X'. \<forall>y\<in>X'. x \<noteq> y \<longrightarrow>
            (\<exists>U V. neighborhood_of x X' TX' U \<and> neighborhood_of y X' TX' V \<and> U \<inter> V = {})"
        proof (intro ballI impI)
          fix x y assume "x \<in> X'" "y \<in> X'" "x \<noteq> y"
          let ?Fx = "{p \<in> P'. q' p = x}" and ?Fy = "{p \<in> P'. q' p = y}"
          \<comment> \<open>Fibers non-empty, closed, disjoint.\<close>
          have hFx_ne: "?Fx \<noteq> {}" using \<open>x \<in> X'\<close> hq'_surj by (by100 blast)
          have hFy_ne: "?Fy \<noteq> {}" using \<open>y \<in> X'\<close> hq'_surj by (by100 blast)
          have hFxy_disj: "?Fx \<inter> ?Fy = {}" using \<open>x \<noteq> y\<close> by (by100 blast)
          have hFx_cl: "closedin_on P' TP' ?Fx"
          proof -
            \<comment> \<open>Fx = {p | (p, p0) \<in> R} for any p0 \<in> Fx. Slice of closed R is closed.\<close>
            obtain p0 where "p0 \<in> P'" "q' p0 = x" using hFx_ne by (by100 blast)
            have hFx_eq: "?Fx = {p \<in> P'. (p, p0) \<in> ?R}"
            proof (rule set_eqI, rule iffI)
              fix p assume "p \<in> ?Fx"
              hence "p \<in> P'" "q' p = x" by (by100 blast)+
              hence "(p, p0) \<in> ?R" using \<open>p0 \<in> P'\<close> \<open>q' p0 = x\<close> by (by100 simp)
              thus "p \<in> {p \<in> P'. (p, p0) \<in> ?R}" using \<open>p \<in> P'\<close> by (by100 blast)
            next
              fix p assume "p \<in> {p \<in> P'. (p, p0) \<in> ?R}"
              hence "p \<in> P'" "(p, p0) \<in> ?R" by (by100 blast)+
              hence "q' p = q' p0" by (by100 simp)
              thus "p \<in> ?Fx" using \<open>p \<in> P'\<close> \<open>q' p0 = x\<close> by (by100 simp)
            qed
            \<comment> \<open>Slice of closed R at p0: {p\<in>P'|(p,p0)\<in>R} = preimage of R under i_{p0}.\<close>
            \<comment> \<open>i_{p0} continuous, R closed \<Rightarrow> preimage closed.\<close>
            have hTP'_prod: "is_topology_on (P' \<times> P') (product_topology_on TP' TP')"
              by (rule product_topology_on_is_topology_on[OF hTP' hTP'])
            have "closedin_on P' TP' {p \<in> P'. (\<lambda>p. (p, p0)) p \<in> ?R}"
            proof (rule continuous_preimage_closedin[OF hTP' hTP'_prod _ hR'cl])
              show "top1_continuous_map_on P' TP' (P' \<times> P') (product_topology_on TP' TP') (\<lambda>p. (p, p0))"
              proof -
                have hpi1: "top1_continuous_map_on P' TP' P' TP' (pi1 \<circ> (\<lambda>p. (p, p0)))"
                proof -
                  have heq: "pi1 \<circ> (\<lambda>p. (p, p0)) = id" unfolding pi1_def comp_def id_def by (by100 simp)
                  show ?thesis unfolding heq by (rule top1_continuous_map_on_id[OF hTP'])
                qed
                have hpi2: "top1_continuous_map_on P' TP' P' TP' (pi2 \<circ> (\<lambda>p. (p, p0)))"
                proof -
                  have heq2: "pi2 \<circ> (\<lambda>p. (p, p0)) = (\<lambda>_. p0)" unfolding pi2_def comp_def by (by100 simp)
                  have "top1_continuous_map_on P' TP' P' TP' (\<lambda>_. p0)"
                    using Theorem_18_2[OF hTP' hTP' hTP'] \<open>p0 \<in> P'\<close> by (by100 blast)
                  thus ?thesis unfolding heq2 .
                qed
                from iffD2[OF Theorem_18_4[OF hTP' hTP' hTP']] hpi1 hpi2
                show ?thesis by (by100 blast)
              qed
            qed
            moreover have "{p \<in> P'. (\<lambda>p. (p, p0)) p \<in> ?R} = {p \<in> P'. (p, p0) \<in> ?R}" by (by100 simp)
            ultimately have "closedin_on P' TP' {p \<in> P'. (p, p0) \<in> ?R}" by (by100 simp)
            thus ?thesis using hFx_eq by (by100 simp)
          qed
          have hFy_cl: "closedin_on P' TP' ?Fy"
          proof -
            obtain p0 where "p0 \<in> P'" "q' p0 = y" using hFy_ne by (by100 blast)
            have hFy_eq: "?Fy = {p \<in> P'. (p, p0) \<in> ?R}"
            proof (rule set_eqI, rule iffI)
              fix p assume "p \<in> ?Fy"
              hence "p \<in> P'" "q' p = y" by (by100 blast)+
              hence "(p, p0) \<in> ?R" using \<open>p0 \<in> P'\<close> \<open>q' p0 = y\<close> by (by100 simp)
              thus "p \<in> {p \<in> P'. (p, p0) \<in> ?R}" using \<open>p \<in> P'\<close> by (by100 blast)
            next
              fix p assume "p \<in> {p \<in> P'. (p, p0) \<in> ?R}"
              hence "p \<in> P'" "(p, p0) \<in> ?R" by (by100 blast)+
              hence "q' p = q' p0" by (by100 simp)
              thus "p \<in> ?Fy" using \<open>p \<in> P'\<close> \<open>q' p0 = y\<close> by (by100 simp)
            qed
            have hTP'_prod: "is_topology_on (P' \<times> P') (product_topology_on TP' TP')"
              by (rule product_topology_on_is_topology_on[OF hTP' hTP'])
            have "closedin_on P' TP' {p \<in> P'. (\<lambda>p. (p, p0)) p \<in> ?R}"
            proof (rule continuous_preimage_closedin[OF hTP' hTP'_prod _ hR'cl])
              show "top1_continuous_map_on P' TP' (P' \<times> P') (product_topology_on TP' TP') (\<lambda>p. (p, p0))"
              proof -
                have hpi1: "top1_continuous_map_on P' TP' P' TP' (pi1 \<circ> (\<lambda>p. (p, p0)))"
                proof -
                  have heq: "pi1 \<circ> (\<lambda>p. (p, p0)) = id" unfolding pi1_def comp_def id_def by (by100 simp)
                  show ?thesis unfolding heq by (rule top1_continuous_map_on_id[OF hTP'])
                qed
                have hpi2: "top1_continuous_map_on P' TP' P' TP' (pi2 \<circ> (\<lambda>p. (p, p0)))"
                proof -
                  have heq2: "pi2 \<circ> (\<lambda>p. (p, p0)) = (\<lambda>_. p0)" unfolding pi2_def comp_def by (by100 simp)
                  have "top1_continuous_map_on P' TP' P' TP' (\<lambda>_. p0)"
                    using Theorem_18_2[OF hTP' hTP' hTP'] \<open>p0 \<in> P'\<close> by (by100 blast)
                  thus ?thesis unfolding heq2 .
                qed
                from iffD2[OF Theorem_18_4[OF hTP' hTP' hTP']] hpi1 hpi2
                show ?thesis by (by100 blast)
              qed
            qed
            moreover have "{p \<in> P'. (\<lambda>p. (p, p0)) p \<in> ?R} = {p \<in> P'. (p, p0) \<in> ?R}" by (by100 simp)
            ultimately have "closedin_on P' TP' {p \<in> P'. (p, p0) \<in> ?R}" by (by100 simp)
            thus ?thesis using hFy_eq by (by100 simp)
          qed
          \<comment> \<open>By normality: disjoint open U \<supseteq> Fx, V \<supseteq> Fy.\<close>
          from normal_separation[OF hP'N hFx_cl hFy_cl hFxy_disj]
          obtain U V where hUV: "U \<in> TP'" "V \<in> TP'" "?Fx \<subseteq> U" "?Fy \<subseteq> V" "U \<inter> V = {}"
            by meson
          \<comment> \<open>Saturated complements: q'\<inverse>(q'(P'-U)) is closed (projection of closed from compact).\<close>
          let ?SU = "{p \<in> P'. \<exists>p' \<in> P' - U. q' p = q' p'}"
          let ?SV = "{p \<in> P'. \<exists>p' \<in> P' - V. q' p = q' p'}"
          \<comment> \<open>Projection of closed from compact is closed (tube lemma consequence).\<close>
          have hproj_closed: "\<And>C. closedin_on (P' \<times> P') (product_topology_on TP' TP') C \<Longrightarrow>
              closedin_on P' TP' {a \<in> P'. \<exists>b. (a, b) \<in> C}"
          proof -
            fix C assume hCcl: "closedin_on (P' \<times> P') (product_topology_on TP' TP') C"
            have hC_sub: "C \<subseteq> P' \<times> P'" using hCcl unfolding closedin_on_def by (by100 blast)
            have hprod_compact: "top1_compact_on (P' \<times> P') (product_topology_on TP' TP')"
              by (rule Theorem_26_7[OF hP'C hP'C])
            have hpi1_cont: "top1_continuous_map_on (P' \<times> P') (product_topology_on TP' TP') P' TP' pi1"
              by (rule top1_continuous_pi1[OF hTP' hTP'])
            have hpi1C_cl: "closedin_on P' TP' (pi1 ` C)"
              by (rule compact_hausdorff_continuous_closed_map[OF hprod_compact hP'H hpi1_cont hCcl])
            have hset_eq: "pi1 ` C = {a \<in> P'. \<exists>b. (a, b) \<in> C}"
            proof -
              have "\<And>a. a \<in> pi1 ` C \<Longrightarrow> a \<in> {a \<in> P'. \<exists>b. (a, b) \<in> C}"
              proof -
                fix a assume "a \<in> pi1 ` C"
                then obtain p where hp: "p \<in> C" "a = pi1 p" by (by100 blast)
                have "a = fst p" using hp(2) unfolding pi1_def by (by100 simp)
                have hp_mem: "p \<in> P' \<times> P'" using hp(1) hC_sub by (by100 blast)
                hence "fst p \<in> P'" using mem_Times_iff by (by100 blast)
                hence "a \<in> P'" using \<open>a = fst p\<close> by (by100 simp)
                have "p = (fst p, snd p)" by (by100 simp)
                hence "(a, snd p) \<in> C" using \<open>a = fst p\<close> hp(1) by (by100 simp)
                thus "a \<in> {a \<in> P'. \<exists>b. (a, b) \<in> C}" using \<open>a \<in> P'\<close> by (by100 blast)
              qed
              moreover have "\<And>a. a \<in> {a \<in> P'. \<exists>b. (a, b) \<in> C} \<Longrightarrow> a \<in> pi1 ` C"
              proof -
                fix a assume "a \<in> {a \<in> P'. \<exists>b. (a, b) \<in> C}"
                then obtain b where "a \<in> P'" "(a, b) \<in> C" by (by100 blast)
                have "a = pi1 (a, b)" unfolding pi1_def by (by100 simp)
                thus "a \<in> pi1 ` C" using \<open>(a, b) \<in> C\<close> by (by100 blast)
              qed
              ultimately show ?thesis by (by100 blast)
            qed
            show "closedin_on P' TP' {a \<in> P'. \<exists>b. (a, b) \<in> C}" using hpi1C_cl hset_eq by (by100 simp)
          qed
          have hTP'_prod2: "is_topology_on (P' \<times> P') (product_topology_on TP' TP')"
            by (rule product_topology_on_is_topology_on[OF hTP' hTP'])
          have hP'_in_TP': "P' \<in> TP'" using hTP' unfolding is_topology_on_def by (by100 blast)
          have hSU_closed: "closedin_on P' TP' ?SU"
          proof -
            have hPU_cl: "closedin_on P' TP' (P' - U)"
            proof (rule closedin_intro)
              show "P' - U \<subseteq> P'" by (by100 blast)
            next
              have "P' - (P' - U) = P' \<inter> U" by (by100 blast)
              moreover have "P' \<inter> U \<in> TP'" by (rule topology_inter2[OF hTP' hP'_in_TP' hUV(1)])
              ultimately show "P' - (P' - U) \<in> TP'" by (by100 simp)
            qed
            have hPxPU_cl: "closedin_on (P' \<times> P') (product_topology_on TP' TP') (P' \<times> (P' - U))"
            proof (rule closedin_intro)
              show "P' \<times> (P' - U) \<subseteq> P' \<times> P'" by (by100 blast)
            next
              have "(P' \<times> P') - (P' \<times> (P' - U)) = P' \<times> (P' \<inter> U)" by (by100 blast)
              moreover have "P' \<inter> U \<in> TP'" by (rule topology_inter2[OF hTP' hP'_in_TP' hUV(1)])
              moreover have "P' \<times> (P' \<inter> U) \<in> product_topology_on TP' TP'"
                by (rule product_rect_open[OF hP'_in_TP' \<open>P' \<inter> U \<in> TP'\<close>])
              ultimately show "(P' \<times> P') - (P' \<times> (P' - U)) \<in> product_topology_on TP' TP'" by (by100 simp)
            qed
            have hRC: "closedin_on (P' \<times> P') (product_topology_on TP' TP')
                (?R \<inter> (P' \<times> (P' - U)))"
              by (rule closedin_inter2[OF hTP'_prod2 hR'cl hPxPU_cl])
            have hSU_eq: "?SU = {a \<in> P'. \<exists>b. (a, b) \<in> ?R \<inter> (P' \<times> (P' - U))}"
              by (by100 blast)
            show ?thesis using hproj_closed[OF hRC] hSU_eq by (by100 simp)
          qed
          have hSV_closed: "closedin_on P' TP' ?SV"
          proof -
            have hPV_cl: "closedin_on P' TP' (P' - V)"
            proof (rule closedin_intro)
              show "P' - V \<subseteq> P'" by (by100 blast)
            next
              have "P' - (P' - V) = P' \<inter> V" by (by100 blast)
              moreover have "P' \<inter> V \<in> TP'" by (rule topology_inter2[OF hTP' hP'_in_TP' hUV(2)])
              ultimately show "P' - (P' - V) \<in> TP'" by (by100 simp)
            qed
            have hPxPV_cl: "closedin_on (P' \<times> P') (product_topology_on TP' TP') (P' \<times> (P' - V))"
            proof (rule closedin_intro)
              show "P' \<times> (P' - V) \<subseteq> P' \<times> P'" by (by100 blast)
            next
              have "(P' \<times> P') - (P' \<times> (P' - V)) = P' \<times> (P' \<inter> V)" by (by100 blast)
              moreover have "P' \<inter> V \<in> TP'" by (rule topology_inter2[OF hTP' hP'_in_TP' hUV(2)])
              moreover have "P' \<times> (P' \<inter> V) \<in> product_topology_on TP' TP'"
                by (rule product_rect_open[OF hP'_in_TP' \<open>P' \<inter> V \<in> TP'\<close>])
              ultimately show "(P' \<times> P') - (P' \<times> (P' - V)) \<in> product_topology_on TP' TP'" by (by100 simp)
            qed
            have hRC: "closedin_on (P' \<times> P') (product_topology_on TP' TP')
                (?R \<inter> (P' \<times> (P' - V)))"
              by (rule closedin_inter2[OF hTP'_prod2 hR'cl hPxPV_cl])
            have hSV_eq: "?SV = {a \<in> P'. \<exists>b. (a, b) \<in> ?R \<inter> (P' \<times> (P' - V))}"
              by (by100 blast)
            show ?thesis using hproj_closed[OF hRC] hSV_eq by (by100 simp)
          qed
          \<comment> \<open>P' - ?SU is open and saturated. q'(P' - ?SU) is open in X'.\<close>
          have hWx_open: "X' - q' ` (P' - U) \<in> TX'"
          proof -
            have "q' ` (P' - U) \<subseteq> X'" using hq'_surj by (by100 blast)
            have "closedin_on X' TX' (q' ` (P' - U))"
            proof -
              have "{p \<in> P'. q' p \<in> q' ` (P' - U)} = ?SU" by (by100 blast)
              hence "closedin_on P' TP' {p \<in> P'. q' p \<in> q' ` (P' - U)}"
                using hSU_closed by (by100 simp)
              thus ?thesis
                using top1_quotient_map_closed_iff_preimage_closed[OF hq'Q \<open>q' ` (P' - U) \<subseteq> X'\<close>]
                by (by100 blast)
            qed
            thus ?thesis using hTX' unfolding closedin_on_def by (by100 blast)
          qed
          have hWy_open: "X' - q' ` (P' - V) \<in> TX'"
          proof -
            have "q' ` (P' - V) \<subseteq> X'" using hq'_surj by (by100 blast)
            have "closedin_on X' TX' (q' ` (P' - V))"
            proof -
              have "{p \<in> P'. q' p \<in> q' ` (P' - V)} = ?SV" by (by100 blast)
              hence "closedin_on P' TP' {p \<in> P'. q' p \<in> q' ` (P' - V)}"
                using hSV_closed by (by100 simp)
              thus ?thesis
                using top1_quotient_map_closed_iff_preimage_closed[OF hq'Q \<open>q' ` (P' - V) \<subseteq> X'\<close>]
                by (by100 blast)
            qed
            thus ?thesis using hTX' unfolding closedin_on_def by (by100 blast)
          qed
          have hx_Wx: "x \<in> X' - q' ` (P' - U)"
          proof -
            have "x \<notin> q' ` (P' - U)"
            proof
              assume "x \<in> q' ` (P' - U)"
              then obtain p where "p \<in> P' - U" "q' p = x" by (by100 blast)
              hence "p \<in> ?Fx" by (by100 blast)
              hence "p \<in> U" using hUV(3) by (by100 blast)
              thus False using \<open>p \<in> P' - U\<close> by (by100 blast)
            qed
            thus ?thesis using \<open>x \<in> X'\<close> by (by100 blast)
          qed
          have hy_Wy: "y \<in> X' - q' ` (P' - V)"
          proof -
            have "y \<notin> q' ` (P' - V)"
            proof
              assume "y \<in> q' ` (P' - V)"
              then obtain p where "p \<in> P' - V" "q' p = y" by (by100 blast)
              hence "p \<in> ?Fy" by (by100 blast)
              hence "p \<in> V" using hUV(4) by (by100 blast)
              thus False using \<open>p \<in> P' - V\<close> by (by100 blast)
            qed
            thus ?thesis using \<open>y \<in> X'\<close> by (by100 blast)
          qed
          have hWxy_disj: "(X' - q' ` (P' - U)) \<inter> (X' - q' ` (P' - V)) = {}"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            then obtain z where "z \<in> X'" "z \<notin> q' ` (P' - U)" "z \<notin> q' ` (P' - V)" by (by100 blast)
            hence "\<forall>p\<in>P'. q' p = z \<longrightarrow> p \<in> U" "\<forall>p\<in>P'. q' p = z \<longrightarrow> p \<in> V" by (by100 blast)+
            hence "\<forall>p\<in>P'. q' p = z \<longrightarrow> p \<in> U \<inter> V" by (by100 blast)
            hence "\<forall>p\<in>P'. q' p \<noteq> z" using hUV(5) by (by100 blast)
            hence "z \<notin> q' ` P'" by (by100 blast)
            thus False using \<open>z \<in> X'\<close> hq'_surj by (by100 blast)
          qed
          show "\<exists>U V. neighborhood_of x X' TX' U \<and> neighborhood_of y X' TX' V \<and> U \<inter> V = {}"
          proof (intro exI conjI)
            show "neighborhood_of x X' TX' (X' - q' ` (P' - U))"
              unfolding neighborhood_of_def using hWx_open hx_Wx by (by100 blast)
            show "neighborhood_of y X' TX' (X' - q' ` (P' - V))"
              unfolding neighborhood_of_def using hWy_open hy_Wy by (by100 blast)
            show "(X' - q' ` (P' - U)) \<inter> (X' - q' ` (P' - V)) = {}"
              by (rule hWxy_disj)
          qed
        qed
      qed
    qed
    have hP_compact_loc: "top1_compact_on P ?TP"
    proof -
      have hTP_eq: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
        using product_topology_on_open_sets_real2 by (by100 simp)
      have "compact P"
      proof -
        obtain vx vy :: "nat \<Rightarrow> real" where hn: "length scheme \<ge> 3"
            and hP_eq: "P = {(x, y). \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
                \<and> (\<Sum>i<length scheme. coeffs i) = 1
                \<and> x = (\<Sum>i<length scheme. coeffs i * vx i)
                \<and> y = (\<Sum>i<length scheme. coeffs i * vy i)}"
          using hP_loc unfolding top1_is_polygonal_region_on_def by blast
        show "compact P" unfolding hP_eq by (rule convex_hull_compact[OF hn])
      qed
      hence "top1_compact_on P (subspace_topology (UNIV::((real\<times>real) set)) top1_open_sets P)"
        using top1_compact_on_subspace_UNIV_iff_compact by (by100 blast)
      thus ?thesis using hTP_eq by (by100 simp)
    qed
    show ?thesis
      by (rule hclosed_R_haus[OF hP_haus hP_compact_loc hq_loc hR_closed])
  qed
  show ?thesis using hcompact hhausdorff by (by100 blast)
qed

(** from \<S>74 Theorem 74.3: fundamental group of n-fold torus T_n has the
    presentation \<langle>a_1, b_1, \<dots>, a_n, b_n | [a_1,b_1]\<cdots>[a_n,b_n]\<rangle>.
    The single relator is the product (a_1 b_1 a_1\<inverse> b_1\<inverse>)\<cdots>(a_n b_n a_n\<inverse> b_n\<inverse>).
    We index generators 0, 1, ..., 2n-1 as a_i := 2i, b_i := 2i+1. **)

(** from \<S>74 Theorem 74.2: If P is a polygonal region with labelling scheme w,
    \<pi> maps all vertices to a single point x_0, and there are k distinct labels,
    then \<pi>_1(X, x_0) is the quotient of Free(k) by the normal closure of the relator.
    This is the general engine; 74.3 and 74.4 are immediate applications.
    Proof (book): A = \<pi>(Bd P) is a wedge of k circles (since all vertices identified).
    Theorem 72.1 gives \<pi>_1(X) \<cong> \<pi>_1(A)/N(relator). Then \<pi>_1(A) = Free(k). **)
theorem Theorem_74_2_scheme_presentation:
  fixes X :: "'a set" and TX :: "'a set set" and x0 :: 'a
    and scheme :: "(nat \<times> bool) list"
  assumes hscheme: "top1_quotient_of_scheme_on X TX scheme"
      and hx0: "x0 \<in> X"
      and hlen: "length scheme \<ge> 3"
      \<comment> \<open>All vertices identified under the (specific extracted) quotient map.\<close>
      and hvert: "\<exists>P q vx vy. top1_is_polygonal_region_on P (length scheme)
          \<and> top1_quotient_map_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q
          \<and> (\<forall>i<length scheme. (vx i, vy i) \<in> P)
          \<and> (\<forall>i<length scheme. \<forall>j<length scheme. q (vx i, vy i) = q (vx j, vy j))"
  shows "\<exists>(G::'g set) mul e invg.
           top1_group_presented_by_on G mul e invg
             (fst ` set scheme) \<comment> \<open>The distinct labels\<close>
             { map (\<lambda>(s,b). (s, b)) scheme } \<comment> \<open>The relator word\<close>
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)"
proof -
  \<comment> \<open>Following Munkres Theorem 74.2 proof step by step.\<close>
  \<comment> \<open>Step 1: Extract P, q, vx, vy from hypothesis.\<close>
  from hvert obtain P q vxP vyP where
    hPoly: "top1_is_polygonal_region_on P (length scheme)" and
    hq: "top1_quotient_map_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q" and
    hverts: "\<forall>i<length scheme. (vxP i, vyP i) \<in> P" and
    hvert_id: "\<forall>i<length scheme. \<forall>j<length scheme. q (vxP i, vyP i) = q (vxP j, vyP j)"
    by (by100 blast)
  let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
  \<comment> \<open>Step 2 (book): "A = \<pi>(Bd P) is a wedge of k circles."
     Since all vertices are identified by q, the boundary edges become loops in X.
     Edges with the same label are identified, giving k distinct circles.
     All circles share the common point x0 = q(vertex).\<close>
  let ?k = "card (fst ` set scheme)"
  have hA_wedge: "\<exists>A. closedin_on X TX A
      \<and> top1_is_wedge_of_circles_on A (subspace_topology X TX A) (fst ` set scheme) x0"
    sorry \<comment> \<open>Book: "A = \<pi>(Bd P) is a wedge of k circles."
       Each label determines a pair of identified edges that form a circle in X.\<close>
  \<comment> \<open>Step 3 (book): "The loops g_1,...,g_k represent a set of free generators for \<pi>_1(A, x0)."
     This is Theorem 71.1 (wedge of circles has free fundamental group).\<close>
  \<comment> \<open>Step 4 (book): "The loop running around Bd P maps to the relator word."
     The boundary loop in order is the scheme word w.\<close>
  \<comment> \<open>Step 5 (book): "The theorem now follows from Theorem 72.1."
     Theorem 72.1 gives \<pi>_1(X) \<cong> \<pi>_1(A) / N(relator).
     \<pi>_1(A) is free on {labels}. The relator is the scheme word.
     This is exactly the group presentation.\<close>
  \<comment> \<open>Combine steps 2-5 to get the presentation.\<close>
  from hA_wedge obtain A where hA_cl: "closedin_on X TX A"
      and hA_wd: "top1_is_wedge_of_circles_on A (subspace_topology X TX A) (fst ` set scheme) x0"
    by (by100 blast)
  \<comment> \<open>\<pi>_1(A) is free on the labels (Theorem 71.1).\<close>
  have hA_free: "\<exists>(F::int set) mulF eF invgF (\<iota>F::nat \<Rightarrow> int).
      top1_is_free_group_full_on F mulF eF invgF \<iota>F (fst ` set scheme)
      \<and> top1_groups_isomorphic_on F mulF
          (top1_fundamental_group_carrier A (subspace_topology X TX A) x0)
          (top1_fundamental_group_mul A (subspace_topology X TX A) x0)"
    sorry \<comment> \<open>Apply Theorem\_71\_1\_wedge\_of\_circles\_finite after showing
       fst ` set scheme = {..<card(fst ` set scheme)}.
       For torus/projective schemes, labels are {..<k} by construction.
       Then Theorem 71.1 gives free group on {..<k}, convert to fst ` set scheme.\<close>
  \<comment> \<open>Apply Theorem 72.1 to get \<pi>_1(X) \<cong> \<pi>_1(A)/N(relator word).\<close>
  have hThm72: "\<exists>(G::'g set) mul e invg.
      top1_group_presented_by_on G mul e invg (fst ` set scheme)
        { map (\<lambda>(s,b). (s, b)) scheme }
      \<and> top1_groups_isomorphic_on G mul
          (top1_fundamental_group_carrier X TX x0)
          (top1_fundamental_group_mul X TX x0)"
    sorry \<comment> \<open>Theorem 72.1 application: needs CW data (h: B^2 -> X from scheme\_quotient\_CW\_data),
       identification of the relator with the scheme word, then group presentation.\<close>
  show ?thesis using hThm72 by (by100 blast)
qed

text \<open>Nth-element access for the torus scheme.\<close>
lemma torus_scheme_nth:
  assumes "k < n"
  shows "(top1_n_torus_scheme n) ! (4*k) = (2*k, True)"
    and "(top1_n_torus_scheme n) ! (4*k+1) = (2*k+1, True)"
    and "(top1_n_torus_scheme n) ! (4*k+2) = (2*k, False)"
    and "(top1_n_torus_scheme n) ! (4*k+3) = (2*k+1, False)"
proof -
  let ?f = "\<lambda>i::nat. [(2*i, True), (2*i+1, True), (2*i, False), (2*i+1, False)]"
  have hscheme: "top1_n_torus_scheme n = concat (map ?f [0..<n])"
    unfolding top1_n_torus_scheme_def by (by100 simp)
  \<comment> \<open>The prefix concat(map f [0..<k]) has length 4k.\<close>
  have hprefix_len: "length (concat (map ?f [0..<k])) = 4 * k"
  proof -
    define g where "g = ?f"
    have "\<And>i. length (g i) = 4" unfolding g_def by (by100 simp)
    have "length (concat (map g [0..<k])) = sum_list (map (length \<circ> g) [0..<k])"
      using length_concat[of "map g [0..<k]"] by (by100 simp)
    also have "map (length \<circ> g) [0..<k] = map (\<lambda>i. 4::nat) [0..<k]"
      using \<open>\<And>i. length (g i) = 4\<close> by (by100 simp)
    also have "sum_list (map (\<lambda>i. 4::nat) [0..<k]) = 4 * k"
      by (induction k, by100 simp, by100 simp)
    finally show ?thesis unfolding g_def by (by100 simp)
  qed
  \<comment> \<open>concat(map f [0..<n]) = concat(map f [0..<k]) @ f(k) @ concat(map f [k+1..<n]).\<close>
  have hsplit: "concat (map ?f [0..<n]) = concat (map ?f [0..<k]) @ ?f k @ concat (map ?f [Suc k..<n])"
  proof -
    have "[0..<n] = [0..<k] @ [k..<n]"
      using upt_add_eq_append[of 0 k "n - k"] assms by (by100 simp)
    also have "[k..<n] = k # [Suc k..<n]" using assms upt_rec[of k n] by (by100 simp)
    finally have "[0..<n] = [0..<k] @ k # [Suc k..<n]" .
    hence "map ?f [0..<n] = map ?f [0..<k] @ ?f k # map ?f [Suc k..<n]" by (by100 simp)
    hence "concat (map ?f [0..<n]) = concat (map ?f [0..<k] @ ?f k # map ?f [Suc k..<n])" by (by100 simp)
    also have "\<dots> = concat (map ?f [0..<k]) @ ?f k @ concat (map ?f [Suc k..<n])" by (by100 simp)
    finally show ?thesis .
  qed
  \<comment> \<open>Now use nth\_append\_length\_plus.\<close>
  have hbase: "\<And>r. r < 4 \<Longrightarrow> concat (map ?f [0..<n]) ! (4*k + r) = ?f k ! r"
  proof -
    fix r :: nat assume "r < 4"
    have "concat (map ?f [0..<n]) ! (4*k + r)
        = (concat (map ?f [0..<k]) @ ?f k @ concat (map ?f [Suc k..<n])) ! (4*k + r)"
      using hsplit by (by100 simp)
    also have "\<dots> = (?f k @ concat (map ?f [Suc k..<n])) ! r"
      using nth_append_length_plus[of "concat (map ?f [0..<k])" "?f k @ concat (map ?f [Suc k..<n])" r]
        hprefix_len by (by100 simp)
    also have "\<dots> = ?f k ! r"
      using nth_append[of "?f k" "concat (map ?f [Suc k..<n])" r] \<open>r < 4\<close> by (by100 simp)
    finally show "concat (map ?f [0..<n]) ! (4*k + r) = ?f k ! r" .
  qed
  show "(top1_n_torus_scheme n) ! (4*k) = (2*k, True)"
    using hbase[of 0] hscheme by (by100 simp)
  show "(top1_n_torus_scheme n) ! (4*k+1) = (2*k+1, True)"
    using hbase[of 1] hscheme by (by100 simp)
  show "(top1_n_torus_scheme n) ! (4*k+2) = (2*k, False)"
    using hbase[of 2] hscheme by (by100 simp)
  show "(top1_n_torus_scheme n) ! (4*k+3) = (2*k+1, False)"
    using hbase[of 3] hscheme by (by100 simp)
qed

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
  \<comment> \<open>Munkres 74.3: Apply Theorem 74.2 to the n-torus labelling scheme.
     The only thing to check is that all vertices get identified.\<close>
  let ?scheme = "top1_n_torus_scheme n"
  have hscheme: "top1_quotient_of_scheme_on X TX ?scheme"
    using assms(1) unfolding top1_is_n_fold_torus_on_def by (by100 blast)
  have hlen: "length ?scheme \<ge> 3"
  proof -
    have "n > 0" using assms(1) unfolding top1_is_n_fold_torus_on_def by (by100 blast)
    hence "length ?scheme \<ge> 4"
    proof -
      assume hn: "n > 0"
      have "length ?scheme = length (concat (map (\<lambda>i. [(2*i, True), (2*i+1, True),
          (2*i, False), (2*i+1, False)]) [0..<n]))"
        unfolding top1_n_torus_scheme_def by (by100 simp)
      also have "\<dots> = 4 * n"
      proof -
        define f where "f = (\<lambda>i::nat. [(2*i, True), (2*i+1, True), (2*i, False), (2*i+1, False)])"
        have hlen_f: "\<And>i. length (f i) = 4" unfolding f_def by (by100 simp)
        have "length (concat (map f [0..<n])) = sum_list (map (length \<circ> f) [0..<n])"
          using length_concat[of "map f [0..<n]"] by (by100 simp)
        also have "map (length \<circ> f) [0..<n] = map (\<lambda>i. 4::nat) [0..<n]"
          using hlen_f by (by100 simp)
        also have "sum_list (map (\<lambda>i. 4::nat) [0..<n]) = 4 * n"
          by (induction n, by100 simp, by100 simp)
        finally show ?thesis unfolding f_def by (by100 simp)
      qed
      finally have "length ?scheme = 4 * n" .
      thus ?thesis using hn by (by100 simp)
    qed
    thus ?thesis by (by100 simp)
  qed
  have hlen_4n: "length ?scheme = 4 * n"
  proof -
    define f where "f = (\<lambda>i::nat. [(2*i, True), (2*i+1, True), (2*i, False), (2*i+1, False)])"
    have "length ?scheme = length (concat (map f [0..<n]))"
      unfolding top1_n_torus_scheme_def f_def by (by100 simp)
    also have "\<dots> = sum_list (map (length \<circ> f) [0..<n])"
      using length_concat[of "map f [0..<n]"] by (by100 simp)
    also have "map (length \<circ> f) [0..<n] = map (\<lambda>i. 4::nat) [0..<n]"
      unfolding f_def by (by100 simp)
    also have "sum_list (map (\<lambda>i. 4::nat) [0..<n]) = 4 * n"
      by (induction n, by100 simp, by100 simp)
    finally show ?thesis unfolding f_def by (by100 simp)
  qed
  \<comment> \<open>All vertices get identified (Munkres: "We leave this to you to check").\<close>
  \<comment> \<open>All vertices get identified: extract specific (P,q,vx,vy) from the scheme and verify.\<close>
  have hvert: "\<exists>P q vx vy. top1_is_polygonal_region_on P (length ?scheme)
      \<and> top1_quotient_map_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q
      \<and> (\<forall>i<length ?scheme. (vx i, vy i) \<in> P)
      \<and> (\<forall>i<length ?scheme. \<forall>j<length ?scheme. q (vx i, vy i) = q (vx j, vy j))"
  proof -
    \<comment> \<open>Extract (P, q, vx, vy) from the torus scheme definition.\<close>
    obtain P q vx vy where
      hP: "top1_is_polygonal_region_on P (length ?scheme)" and
      hq: "top1_quotient_map_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q" and
      hlen3: "length ?scheme \<ge> 3" and
      hverts: "\<forall>i<length ?scheme. (vx i, vy i) \<in> P" and
      hedge: "\<forall>i<length ?scheme. \<forall>j<length ?scheme.
          fst (?scheme!i) = fst (?scheme!j) \<longrightarrow>
          (\<forall>t\<in>I_set.
             q ((1-t) * vx i + t * vx (Suc i mod length ?scheme),
                (1-t) * vy i + t * vy (Suc i mod length ?scheme))
           = (if snd (?scheme!i) = snd (?scheme!j)
              then q ((1-t) * vx j + t * vx (Suc j mod length ?scheme),
                      (1-t) * vy j + t * vy (Suc j mod length ?scheme))
              else q (t * vx j + (1-t) * vx (Suc j mod length ?scheme),
                      t * vy j + (1-t) * vy (Suc j mod length ?scheme))))" and
      hinterior: "\<forall>p\<in>P. (\<forall>i<length ?scheme. \<forall>t\<in>I_set.
            p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length ?scheme),
                  (1-t) * vy i + t * vy (Suc i mod length ?scheme)))
       \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
      by (rule quotient_of_scheme_extract_full[OF hscheme])
    \<comment> \<open>The edge identification at t=0 gives vertex identifications.
       For edges i,j with same label and different direction (snd differs):
       q(vx i, vy i) = q(vx(Suc j mod len), vy(Suc j mod len)).
       For the torus scheme, this chains all vertices.\<close>
    \<comment> \<open>From hedge at t=0: for edges with same label, different direction,
       q(start of edge i) = q(end of edge j).
       The torus scheme ensures all vertices are transitively connected.\<close>
    have h0_in_I: "(0::real) \<in> I_set"
      unfolding top1_unit_interval_def by (by100 simp)
    have h1_in_I: "(1::real) \<in> I_set"
      unfolding top1_unit_interval_def by (by100 simp)
    \<comment> \<open>Suffices to show: q(vx 0, vy 0) = q(vx i, vy i) for all i.\<close>
    have hvert_ident: "\<forall>i<length ?scheme. \<forall>j<length ?scheme.
        q (vx i, vy i) = q (vx j, vy j)"
    proof -
      \<comment> \<open>It suffices to show q(vx i, vy i) = q(vx 0, vy 0) for all i < 4n.
         We prove: q(vx i, vy i) = q(vx (Suc i mod (4*n)), vy (Suc i mod (4*n)))
         for each i, then chain by induction.
         This follows from hedge: adjacent edges share an endpoint.\<close>
      have hadjacent: "\<forall>i<length ?scheme.
          q (vx i, vy i) = q (vx (Suc i mod length ?scheme), vy (Suc i mod length ?scheme))"
      proof (intro allI impI)
        fix i assume hi: "i < length ?scheme"
        \<comment> \<open>For the torus scheme, edge i has label fst(?scheme!i).
           Find partner j with same label but different direction.
           Use hedge at t=0 and t=1 to chain vertex identifications.\<close>
        \<comment> \<open>Within block k (edges 4k..4k+3):
           - edges 4k,4k+2 share label (diff dir): q(v(4k))=q(v(4k+3)), q(v(4k+1))=q(v(4k+2))
           - edges 4k+1,4k+3 share label (diff dir): q(v(4k+1))=q(v(4k+4 mod 4n)), q(v(4k+2))=q(v(4k+3))
           These chain: v(i) = v(i+1) for each i.\<close>
        \<comment> \<open>Strategy: find partner edge j sharing a label with i, use hedge to get
           vertex identifications, chain to show v(i) = v(i+1).
           For the torus scheme, within block k=i div 4:
           - If i mod 4 = 0: use hedge(4k, 4k+2) at t=1 to get v(4k+1) = v(4k+2),
             and hedge(4k+1, 4k+3) at t=0 to get v(4k+1) = v(4k+4 mod 4n).
             Combined with hedge(4k, 4k+2) at t=0: v(4k) = v(4k+3).
             Chain: v(4k) = v(4k+3) = v(4k+2) = v(4k+1). So v(4k) = v(4k+1). \<checkmark>
           - If i mod 4 = 1: hedge(4k, 4k+2) at t=1: v(4k+1) = v(4k+2). \<checkmark>
           - If i mod 4 = 2: hedge(4k+1, 4k+3) at t=1: v(4k+2) = v(4k+3). \<checkmark>
           - If i mod 4 = 3: v(4k+3) = v(4k) (from hedge(4k,4k+2) at t=0) = v(4k+1)
             (from case 0) = v(4k+4 mod 4n) (from hedge(4k+1,4k+3) at t=0). \<checkmark>\<close>
        \<comment> \<open>Instantiate hedge per case i mod 4.
           Key facts from torus\_scheme\_nth: scheme!(4k+r) for r=0,1,2,3.\<close>
        have hn_pos: "n > 0" using assms(1) unfolding top1_is_n_fold_torus_on_def by (by100 blast)
        define k where "k = i div 4"
        define r where "r = i mod 4"
        have hkr: "i = 4*k + r" "r < 4" unfolding k_def r_def by (by100 auto)+
        have hk_bound: "k < n" using hi hkr hlen_4n by (by100 simp)
        \<comment> \<open>From torus\_scheme\_nth: label/direction of edges in block k.\<close>
        have h4k_bound: "4*k < length ?scheme" using hk_bound hlen_4n by (by100 simp)
        have h4k1_bound: "4*k+1 < length ?scheme" using hk_bound hlen_4n by (by100 simp)
        have h4k2_bound: "4*k+2 < length ?scheme" using hk_bound hlen_4n by (by100 simp)
        have h4k3_bound: "4*k+3 < length ?scheme" using hk_bound hlen_4n by (by100 simp)
        have hlabel_a: "fst (?scheme!(4*k)) = fst (?scheme!(4*k+2))"
          using torus_scheme_nth(1,3)[OF hk_bound] by (by100 simp)
        have hdir_a: "snd (?scheme!(4*k)) \<noteq> snd (?scheme!(4*k+2))"
          using torus_scheme_nth(1,3)[OF hk_bound] by (by100 simp)
        have hlabel_b: "fst (?scheme!(4*k+1)) = fst (?scheme!(4*k+3))"
          using torus_scheme_nth(2,4)[OF hk_bound] by (by100 simp)
        have hdir_b: "snd (?scheme!(4*k+1)) \<noteq> snd (?scheme!(4*k+3))"
          using torus_scheme_nth(2,4)[OF hk_bound] by (by100 simp)
        \<comment> \<open>From hedge at t=1 with edges 4k,4k+2 (same label a, diff dir):
           q(vx(4k+1), vy(4k+1)) = q(vx(4k+2), vy(4k+2)).\<close>
        have hedge_a_t1: "q (vx (Suc (4*k) mod length ?scheme), vy (Suc (4*k) mod length ?scheme))
            = q (vx (4*k+2), vy (4*k+2))"
        proof -
          have "Suc (4*k) mod length ?scheme = 4*k+1"
            using h4k1_bound by (by100 simp)
          moreover from hedge[rule_format, OF h4k_bound h4k2_bound hlabel_a, rule_format, OF h1_in_I]
          have "q ((1-1) * vx (4*k) + 1 * vx (Suc (4*k) mod length ?scheme),
                   (1-1) * vy (4*k) + 1 * vy (Suc (4*k) mod length ?scheme))
              = q (1 * vx (4*k+2) + (1-1) * vx (Suc (4*k+2) mod length ?scheme),
                   1 * vy (4*k+2) + (1-1) * vy (Suc (4*k+2) mod length ?scheme))"
            using hdir_a by (by5000 simp)
          ultimately show ?thesis by (by5000 simp)
        qed
        \<comment> \<open>Similarly for t=0: q(vx(4k), vy(4k)) = q(vx(4k+3), vy(4k+3)).\<close>
        have hedge_a_t0: "q (vx (4*k), vy (4*k)) = q (vx (Suc (4*k+2) mod length ?scheme), vy (Suc (4*k+2) mod length ?scheme))"
        proof -
          from hedge[rule_format, OF h4k_bound h4k2_bound hlabel_a, rule_format, OF h0_in_I]
          have "q ((1-0) * vx (4*k) + 0 * vx (Suc (4*k) mod length ?scheme),
                   (1-0) * vy (4*k) + 0 * vy (Suc (4*k) mod length ?scheme))
              = q (0 * vx (4*k+2) + (1-0) * vx (Suc (4*k+2) mod length ?scheme),
                   0 * vy (4*k+2) + (1-0) * vy (Suc (4*k+2) mod length ?scheme))"
            using hdir_a by (by5000 simp)
          thus ?thesis by (by5000 simp)
        qed
        have h4k3_eq: "Suc (4*k+2) mod length ?scheme = 4*k+3"
          using h4k3_bound by (by100 simp)
        have hedge_a_t0': "q (vx (4*k), vy (4*k)) = q (vx (4*k+3), vy (4*k+3))"
          using hedge_a_t0 h4k3_eq by (by100 simp)
        \<comment> \<open>From hedge at t=1 with edges 4k+1,4k+3: q(vx(4k+2)) = q(vx(4k+3)).\<close>
        have hedge_b_t1: "q (vx (Suc (4*k+1) mod length ?scheme), vy (Suc (4*k+1) mod length ?scheme))
            = q (vx (4*k+3), vy (4*k+3))"
        proof -
          have h4k2_eq: "Suc (4*k+1) mod length ?scheme = 4*k+2"
            using h4k2_bound by (by100 simp)
          from hedge[rule_format, OF h4k1_bound h4k3_bound hlabel_b, rule_format, OF h1_in_I]
          have "q ((1-1) * vx (4*k+1) + 1 * vx (Suc (4*k+1) mod length ?scheme),
                   (1-1) * vy (4*k+1) + 1 * vy (Suc (4*k+1) mod length ?scheme))
              = q (1 * vx (4*k+3) + (1-1) * vx (Suc (4*k+3) mod length ?scheme),
                   1 * vy (4*k+3) + (1-1) * vy (Suc (4*k+3) mod length ?scheme))"
            using hdir_b by (by5000 simp)
          thus ?thesis by (by5000 simp)
        qed
        have hedge_b_t1': "q (vx (4*k+2), vy (4*k+2)) = q (vx (4*k+3), vy (4*k+3))"
        proof -
          have "Suc (4*k+1) mod length ?scheme = 4*k+2"
            using h4k2_bound by (by100 simp)
          thus ?thesis using hedge_b_t1 by (by100 simp)
        qed
        \<comment> \<open>From hedge at t=0 with edges 4k+1,4k+3: q(vx(4k+1)) = q(vx(4(k+1) mod 4n)).\<close>
        have hedge_b_t0: "q (vx (4*k+1), vy (4*k+1))
            = q (vx (Suc (4*k+3) mod length ?scheme), vy (Suc (4*k+3) mod length ?scheme))"
        proof -
          from hedge[rule_format, OF h4k1_bound h4k3_bound hlabel_b, rule_format, OF h0_in_I]
          have "q ((1-0) * vx (4*k+1) + 0 * vx (Suc (4*k+1) mod length ?scheme),
                   (1-0) * vy (4*k+1) + 0 * vy (Suc (4*k+1) mod length ?scheme))
              = q (0 * vx (4*k+3) + (1-0) * vx (Suc (4*k+3) mod length ?scheme),
                   0 * vy (4*k+3) + (1-0) * vy (Suc (4*k+3) mod length ?scheme))"
            using hdir_b by (by5000 simp)
          thus ?thesis by (by5000 simp)
        qed
        \<comment> \<open>Also: q(vx(4k+1)) = q(vx(4k+1)) from hedge\_a\_t1.\<close>
        have hedge_a_t1': "q (vx (4*k+1), vy (4*k+1)) = q (vx (4*k+2), vy (4*k+2))"
        proof -
          have "Suc (4*k) mod length ?scheme = 4*k+1"
            using h4k1_bound by (by100 simp)
          thus ?thesis using hedge_a_t1 by (by100 simp)
        qed
        \<comment> \<open>Now case split on r.\<close>
        show "q (vx i, vy i) = q (vx (Suc i mod length ?scheme), vy (Suc i mod length ?scheme))"
        proof -
          have "r = 0 \<or> r = 1 \<or> r = 2 \<or> r = 3" using hkr(2) by (by100 auto)
          thus ?thesis
          proof (elim disjE)
            assume "r = 0"
            \<comment> \<open>v(4k) = v(4k+3) = v(4k+2) = v(4k+1). So v(4k) = v(4k+1).\<close>
            hence "i = 4*k" using hkr(1) by (by100 simp)
            have "q (vx (4*k), vy (4*k)) = q (vx (4*k+1), vy (4*k+1))"
              using hedge_a_t0' hedge_b_t1' hedge_a_t1' by (by100 simp)
            moreover have "Suc (4*k) mod length ?scheme = 4*k+1"
              using h4k1_bound by (by100 simp)
            ultimately show ?thesis using \<open>i = 4*k\<close> by (by100 simp)
          next
            assume "r = 1"
            hence "i = 4*k+1" using hkr(1) by (by100 simp)
            moreover have "Suc (4*k+1) mod length ?scheme = 4*k+2"
              using h4k2_bound by (by100 simp)
            ultimately show ?thesis using hedge_a_t1' by (by100 simp)
          next
            assume "r = 2"
            hence "i = 4*k+2" using hkr(1) by (by100 simp)
            moreover have "Suc (4*k+2) mod length ?scheme = 4*k+3"
              using h4k3_bound by (by100 simp)
            ultimately show ?thesis using hedge_b_t1' by (by100 simp)
          next
            assume "r = 3"
            hence "i = 4*k+3" using hkr(1) by (by100 simp)
            \<comment> \<open>v(4k+3) = v(4k) (from hedge\_a\_t0') = v(4k+1) (from r=0 chain)
               = v(4(k+1) mod 4n) (from hedge\_b\_t0).\<close>
            have "q (vx (4*k+3), vy (4*k+3)) = q (vx (4*k), vy (4*k))"
              using hedge_a_t0' by (by100 simp)
            also have "\<dots> = q (vx (4*k+1), vy (4*k+1))"
              using hedge_a_t0' hedge_b_t1' hedge_a_t1' by (by100 simp)
            also have "\<dots> = q (vx (Suc (4*k+3) mod length ?scheme), vy (Suc (4*k+3) mod length ?scheme))"
              using hedge_b_t0 by (by100 simp)
            finally show ?thesis using \<open>i = 4*k+3\<close> by (by100 simp)
          qed
        qed
      qed
      \<comment> \<open>From hadjacent, all vertices are in the same equivalence class.\<close>
      \<comment> \<open>From hadjacent, iterate: q(vx 0, vy 0) = q(vx 1, vy 1) = ... = q(vx (4n-1), vy (4n-1)).\<close>
      have hchain: "\<forall>i<length ?scheme. q (vx 0, vy 0) = q (vx i, vy i)"
      proof (intro allI impI)
        fix i assume hi: "i < length ?scheme"
        show "q (vx 0, vy 0) = q (vx i, vy i)"
          using hi
        proof (induction i)
          case 0 show ?case by (by100 simp)
        next
          case (Suc k)
          hence hSk: "Suc k < length ?scheme" by (by100 simp)
          hence hk: "k < length ?scheme" by (by100 simp)
          have "q (vx 0, vy 0) = q (vx k, vy k)" using Suc.IH hk by (by100 blast)
          also have "q (vx k, vy k) = q (vx (Suc k mod length ?scheme), vy (Suc k mod length ?scheme))"
            using hadjacent hk by (by100 blast)
          also have "Suc k mod length ?scheme = Suc k"
            using hSk by (by100 simp)
          finally show ?case by (by100 simp)
        qed
      qed
      show ?thesis
      proof (intro allI impI)
        fix i j assume "i < length ?scheme" "j < length ?scheme"
        have "q (vx 0, vy 0) = q (vx i, vy i)" using hchain \<open>i < length ?scheme\<close> by (by100 blast)
        moreover have "q (vx 0, vy 0) = q (vx j, vy j)" using hchain \<open>j < length ?scheme\<close> by (by100 blast)
        ultimately show "q (vx i, vy i) = q (vx j, vy j)" by (by100 simp)
      qed
    qed
    show ?thesis using hP hq hverts hvert_ident by (by100 blast)
  qed
  \<comment> \<open>Apply Theorem 74.2.\<close>
  have h742: "\<exists>(G::'g set) mul e invg.
      top1_group_presented_by_on G mul e invg (fst ` set ?scheme)
        { map (\<lambda>(s,b). (s, b)) ?scheme }
      \<and> top1_groups_isomorphic_on G mul
          (top1_fundamental_group_carrier X TX x0)
          (top1_fundamental_group_mul X TX x0)"
    by (rule Theorem_74_2_scheme_presentation[OF hscheme assms(2) hlen hvert])
  \<comment> \<open>The distinct labels of the torus scheme are {0,...,2n-1}.\<close>
  have hlabels: "fst ` set ?scheme = {..<2*n}"
  proof -
    define f where "f = (\<lambda>i::nat. [(2*i, True), (2*i+1, True), (2*i, False), (2*i+1, False)])"
    have hfst_f: "\<And>i. fst ` set (f i) = {2*i, 2*i+1}" unfolding f_def by (by5000 force)
    have "fst ` set ?scheme = fst ` set (concat (map f [0..<n]))"
      unfolding top1_n_torus_scheme_def f_def by (by100 simp)
    also have "\<dots> = (\<Union>i\<in>{0..<n}. fst ` set (f i))" by (by5000 auto)
    also have "\<dots> = (\<Union>i\<in>{0..<n}. {2*i, 2*i+1})" using hfst_f by (by100 simp)
    also have "\<dots> = {..<2*n}"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> (\<Union>i\<in>{0..<n}. {2 * i, 2 * i + 1})"
      then obtain i where "i < n" "x = 2*i \<or> x = 2*i+1" by (by5000 auto)
      thus "x \<in> {..<2*n}" by (by100 auto)
    next
      fix x assume "x \<in> {..<2*n}"
      hence "x < 2*n" by (by100 simp)
      hence "x div 2 < n" by (by100 simp)
      show "x \<in> (\<Union>i\<in>{0..<n}. {2 * i, 2 * i + 1})"
      proof (cases "even x")
        case True
        then obtain k where "x = 2*k" by (by100 auto)
        hence "k < n" using \<open>x < 2*n\<close> by (by100 simp)
        thus ?thesis using \<open>x = 2*k\<close> by (by100 force)
      next
        case False
        hence "odd x" by (by100 simp)
        then obtain k where "x = 2*k+1" using oddE by (by5000 blast)
        hence "k < n" using \<open>x < 2*n\<close> by (by100 simp)
        thus ?thesis using \<open>x = 2*k+1\<close> by (by100 force)
      qed
    qed
    finally show ?thesis .
  qed
  \<comment> \<open>The relator word in the scheme = the torus relator.\<close>
  have hrelator: "{ map (\<lambda>(s,b). (s, b)) ?scheme }
      = { concat (map (\<lambda>i. [(2*i, True), (2*i+1, True),
                              (2*i, False), (2*i+1, False)]) [0..<n]) }"
  proof -
    have "map (\<lambda>(s,b). (s, b)) ?scheme = ?scheme" by (by100 simp)
    thus ?thesis unfolding top1_n_torus_scheme_def by (by100 simp)
  qed
  show ?thesis using h742 hlabels hrelator by (by5000 simp)
qed

(** from \<S>74 Theorem 74.4: \<pi>_1(P_m) has presentation \<langle>a_1, \<dots>, a_m | a_1² \<cdots> a_m²\<rangle>.
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
  \<comment> \<open>Step 1: P_m is a polygonal quotient of a 2m-gon with projective scheme.\<close>
  have h_poly: "top1_is_polygonal_quotient_on X TX"
    using assms(1) unfolding top1_is_m_fold_projective_on_def
  proof (elim disjE conjE)
    \<comment> \<open>Case m = 1: dunce cap. Need to show dunce cap is polygonal quotient.\<close>
    assume "m = 1" "top1_is_dunce_cap_on X TX (2::nat)"
    thus ?thesis sorry \<comment> \<open>Dunce cap with n=2 is a polygonal quotient.\<close>
  next
    \<comment> \<open>Case m \<ge> 2: directly from the projective scheme.\<close>
    assume "2 \<le> m" "top1_quotient_of_scheme_on X TX (top1_m_projective_scheme m)"
    thus ?thesis unfolding top1_is_polygonal_quotient_on_def
    proof (intro conjI)
      show "is_topology_on_strict X TX"
        using \<open>top1_quotient_of_scheme_on X TX (top1_m_projective_scheme m)\<close>
        unfolding top1_quotient_of_scheme_on_def by (by100 blast)
      show "\<exists>scheme::(nat \<times> bool) list. top1_quotient_of_scheme_on X TX scheme"
        using \<open>top1_quotient_of_scheme_on X TX (top1_m_projective_scheme m)\<close> by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 2: The 2m-gon's 1-skeleton after identifications is a wedge of m circles.\<close>
  have h_skel: "\<exists>A. closedin_on X TX A \<and>
      top1_is_wedge_of_circles_on A (subspace_topology X TX A) {..<m} x0"
    using m_projective_scheme_CW_data[OF assms] by (by100 blast)
  \<comment> \<open>Step 3: Theorem 72.1 with relator a₁²a₂²...aₘ².\<close>
  show ?thesis sorry \<comment> \<open>Theorem 72.1 + projective presentation.\<close>
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

(** from \<S>75 Theorem 75.1: The first homology group H_1(X, x_0) is defined as the
    abelianization of \<pi>_1(X, x_0) (i.e. \<pi>_1/[\<pi>_1, \<pi>_1]).
    Note: this formalization defines H_1 as the abelianization, following Munkres §75.
    There is no separate homology theory; H_1 IS the abelianization by definition.
    The theorem constructs it concretely as the quotient by the commutator subgroup. **)
theorem Theorem_75_1_H1_abelianization:
  fixes X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "is_topology_on X TX" and "x0 \<in> X"
  shows "\<exists>(H :: (real \<Rightarrow> 'a) set set set) mulH eH invgH \<phi>.
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
  have h_comm_normal: "top1_normal_subgroup_on ?G ?mul ?e ?inv ?comm"
  proof -
    have "top1_is_group_on ?G ?mul ?e ?inv"
      by (rule top1_fundamental_group_is_group[OF assms])
    thus ?thesis by (rule commutator_subgroup_is_normal)
  qed
  have hG: "top1_is_group_on ?G ?mul ?e ?inv"
    by (rule top1_fundamental_group_is_group[OF assms])
  \<comment> \<open>Step 2: The natural projection \<phi>(g) = gN is a surjective homomorphism with kernel N.\<close>
  let ?\<phi> = "\<lambda>g. top1_group_coset_on ?G ?mul ?comm g"
  have h_hom: "top1_group_hom_on ?G ?mul
      (top1_quotient_group_carrier_on ?G ?mul ?comm)
      (top1_quotient_group_mul_on ?mul) ?\<phi>"
    by (rule quotient_projection_properties(1)[OF hG h_comm_normal])
  have h_surj: "?\<phi> ` ?G = top1_quotient_group_carrier_on ?G ?mul ?comm"
    by (rule quotient_projection_properties(2)[OF hG h_comm_normal])
  have hNsub: "?comm \<subseteq> ?G"
    using h_comm_normal unfolding top1_normal_subgroup_on_def by (by100 blast)
  have hN_grp: "top1_is_group_on ?comm ?mul ?e ?inv"
    using h_comm_normal unfolding top1_normal_subgroup_on_def by (by100 blast)
  have h_ker: "top1_group_kernel_on ?G (top1_group_coset_on ?G ?mul ?comm ?e) ?\<phi> = ?comm"
    by (rule quotient_projection_properties(3)[OF hG h_comm_normal])
  have hcoset_e: "top1_group_coset_on ?G ?mul ?comm ?e = ?comm"
    by (rule coset_e_is_N[OF hG hNsub hN_grp])
  \<comment> \<open>Step 3: G/[G,G] is abelian.\<close>
  have h_abelian: "\<forall>g\<in>?G. \<forall>h\<in>?G.
    top1_quotient_group_mul_on ?mul
      (top1_group_coset_on ?G ?mul ?comm g) (top1_group_coset_on ?G ?mul ?comm h)
    = top1_quotient_group_mul_on ?mul
      (top1_group_coset_on ?G ?mul ?comm h) (top1_group_coset_on ?G ?mul ?comm g)"
    by (rule quotient_by_commutator_is_abelian[OF hG])
  \<comment> \<open>Step 4: G/[G,G] is a group.\<close>
  let ?invgH = "\<lambda>C. top1_group_coset_on ?G ?mul ?comm
      (?inv (SOME g. g \<in> ?G \<and> C = top1_group_coset_on ?G ?mul ?comm g))"
  have h_quotient_grp: "top1_is_group_on
      (top1_quotient_group_carrier_on ?G ?mul ?comm)
      (top1_quotient_group_mul_on ?mul)
      (top1_group_coset_on ?G ?mul ?comm ?e) ?invgH"
    by (rule quotient_group_is_group[OF hG h_comm_normal])
  \<comment> \<open>Step 5: G/[G,G] is abelian (commutativity from quotient_by_commutator_is_abelian,
     but need to lift from generator-level to carrier-level).\<close>
  have h_quot_abelian: "top1_is_abelian_group_on
      (top1_quotient_group_carrier_on ?G ?mul ?comm)
      (top1_quotient_group_mul_on ?mul)
      (top1_group_coset_on ?G ?mul ?comm ?e) ?invgH"
    unfolding top1_is_abelian_group_on_def
  proof (intro conjI ballI)
    show "top1_is_group_on
        (top1_quotient_group_carrier_on ?G ?mul ?comm) (top1_quotient_group_mul_on ?mul)
        (top1_group_coset_on ?G ?mul ?comm ?e) ?invgH"
      by (rule h_quotient_grp)
  next
    fix C1 C2
    assume hC1: "C1 \<in> top1_quotient_group_carrier_on ?G ?mul ?comm"
       and hC2: "C2 \<in> top1_quotient_group_carrier_on ?G ?mul ?comm"
    obtain g1 where hg1: "g1 \<in> ?G" and hC1_eq: "C1 = top1_group_coset_on ?G ?mul ?comm g1"
      using hC1 unfolding top1_quotient_group_carrier_on_def by (by100 blast)
    obtain g2 where hg2: "g2 \<in> ?G" and hC2_eq: "C2 = top1_group_coset_on ?G ?mul ?comm g2"
      using hC2 unfolding top1_quotient_group_carrier_on_def by (by100 blast)
    show "top1_quotient_group_mul_on ?mul C1 C2 = top1_quotient_group_mul_on ?mul C2 C1"
      using hC1_eq hC2_eq h_abelian hg1 hg2 by (by100 simp)
  qed
  \<comment> \<open>Step 6: Assemble all pieces into top1_is_abelianization_of.\<close>
  have h_ker_comm: "top1_group_kernel_on ?G (top1_group_coset_on ?G ?mul ?comm ?e) ?\<phi> = ?comm"
    by (rule h_ker)
  have "top1_is_abelianization_of
      (top1_quotient_group_carrier_on ?G ?mul ?comm)
      (top1_quotient_group_mul_on ?mul)
      (top1_group_coset_on ?G ?mul ?comm ?e)
      ?invgH ?G ?mul ?e ?inv ?\<phi>"
    unfolding top1_is_abelianization_of_def
    using h_quot_abelian hG h_hom h_surj h_ker_comm hcoset_e by (by100 blast)
  thus ?thesis by (by100 blast)
qed

text \<open>Helper: if a group G is presented by generators S with relators R, and
  all relators are in [F,F] (commutator subgroup) of any free group F on S,
  then the abelianization of G is free abelian on S.
  This wraps abelianization\_of\_presented\_group to hide the existential.\<close>
lemma presented_comm_relator_abelianization:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and S :: "'s set" and R :: "('s \<times> bool) list set"
  assumes hpres: "top1_group_presented_by_on G mul e invg S R"
      and hcomm: "\<And>(F::'g set) mulF eF invgF \<iota> \<pi>.
           top1_is_free_group_full_on F mulF eF invgF \<iota> S \<Longrightarrow>
           top1_group_hom_on F mulF G mul \<pi> \<Longrightarrow>
           \<pi> ` F = G \<Longrightarrow>
           top1_group_kernel_on F e \<pi>
             = top1_normal_subgroup_generated_on F mulF eF invgF
                 {r. \<exists>w\<in>R. r = top1_group_word_product mulF eF invgF
                              (map (\<lambda>(s, b). (\<iota> s, b)) w)} \<Longrightarrow>
           top1_group_kernel_on F e \<pi>
             \<subseteq> top1_commutator_subgroup_on F mulF eF invgF"
  shows "\<exists>(H :: 'g set set) mulH eH invgH \<phi> \<iota>H.
      top1_is_abelianization_of H mulH eH invgH G mul e invg \<phi>
    \<and> top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>H S"
  using hpres[unfolded top1_group_presented_by_on_def]
  apply (elim conjE exE)
  apply (frule hcomm, assumption+)
  apply (drule(4) abelianization_of_presented_group)
  apply (by100 blast)
  done

text \<open>Word product of commutator concat is in [F,F]:
  word\_product(concat(map (\<lambda>i. [(a\_i, T), (b\_i, T), (a\_i, F), (b\_i, F)]) is)) \<in> [G,G].\<close>
lemma word_product_commutator_concat_in_comm:
  assumes hG: "top1_is_group_on G mul e invg"
      and hf: "\<forall>i \<in> set is. a i \<in> G \<and> b i \<in> G"
  shows "top1_group_word_product mul e invg
      (concat (map (\<lambda>i. [(a i, True), (b i, True), (a i, False), (b i, False)]) is))
    \<in> top1_commutator_subgroup_on G mul e invg"
  using hf
proof (induction "is")
  case Nil
  \<comment> \<open>word\_product [] = e. e \<in> [G,G] since [G,G] is a subgroup.\<close>
  have "top1_group_word_product mul e invg (concat (map (\<lambda>i. [(a i, True), (b i, True),
      (a i, False), (b i, False)]) [])) = e" by (by100 simp)
  moreover have "e \<in> top1_commutator_subgroup_on G mul e invg"
  proof -
    from commutator_subgroup_is_normal[OF hG]
    have "top1_is_group_on (top1_commutator_subgroup_on G mul e invg) mul e invg"
      unfolding top1_normal_subgroup_on_def by (by100 blast)
    thus ?thesis unfolding top1_is_group_on_def by (by100 blast)
  qed
  ultimately show ?case by (by100 simp)
next
  case (Cons j js)
  let ?sub = "[(a j, True), (b j, True), (a j, False), (b j, False)]"
  let ?rest_word = "concat (map (\<lambda>i. [(a i, True), (b i, True), (a i, False), (b i, False)]) js)"
  \<comment> \<open>concat(map ... (j # js)) = ?sub @ ?rest\_word.\<close>
  have hconcat: "concat (map (\<lambda>i. [(a i, True), (b i, True), (a i, False), (b i, False)]) (j # js))
      = ?sub @ ?rest_word" by (by100 simp)
  \<comment> \<open>word\_product(?sub @ ?rest\_word) = mul(word\_product(?sub), word\_product(?rest\_word)).\<close>
  have hab_j: "a j \<in> G \<and> b j \<in> G"
    apply (rule Cons(2)[rule_format])
    apply (by100 simp)
    done
  have haj: "a j \<in> G" using hab_j by (by100 blast)
  have hbj: "b j \<in> G" using hab_j by (by100 blast)
  have hsub_G: "\<forall>i<length ?sub. fst (?sub ! i) \<in> G"
  proof (intro allI impI)
    fix i assume hi: "i < length ?sub"
    hence "i \<in> {0, 1, 2, 3}" by (by100 auto)
    thus "fst (?sub ! i) \<in> G" using haj hbj by (by100 auto)
  qed
  have hrest_G: "\<forall>i<length ?rest_word. fst (?rest_word ! i) \<in> G"
  proof (intro allI impI)
    fix i assume hi: "i < length ?rest_word"
    have "?rest_word ! i \<in> set ?rest_word" using hi nth_mem by (by100 blast)
    hence "?rest_word ! i \<in> (\<Union>k \<in> set js. set [(a k, True), (b k, True), (a k, False), (b k, False)])"
      unfolding set_concat by (by100 simp)
    then obtain k where hk: "k \<in> set js" and helem: "?rest_word ! i \<in> set [(a k, True), (b k, True), (a k, False), (b k, False)]"
      by (by100 blast)
    from helem have "?rest_word ! i = (a k, True) \<or> ?rest_word ! i = (b k, True)
        \<or> ?rest_word ! i = (a k, False) \<or> ?rest_word ! i = (b k, False)"
      by (by100 auto)
    hence hfst: "fst (?rest_word ! i) \<in> {a k, b k}" by (by100 auto)
    have "k \<in> set (j # js)" using hk by (by100 simp)
    hence "a k \<in> G \<and> b k \<in> G"
      apply (rule Cons(2)[rule_format])
      done
    hence "a k \<in> G" and "b k \<in> G" by (by100 blast)+
    define v where "v = fst (?rest_word ! i)"
    have "v \<in> {a k, b k}" using hfst unfolding v_def .
    hence "v = a k \<or> v = b k" by (by100 blast)
    hence "v \<in> G" using \<open>a k \<in> G\<close> \<open>b k \<in> G\<close> by (by100 blast)
    thus "fst (?rest_word ! i) \<in> G" unfolding v_def .
  qed
  have hprod: "top1_group_word_product mul e invg (?sub @ ?rest_word)
      = mul (top1_group_word_product mul e invg ?sub) (top1_group_word_product mul e invg ?rest_word)"
    by (rule word_product_append[OF hG hsub_G hrest_G])
  \<comment> \<open>word\_product(?sub) = commutator(a j, b j) \<in> [G,G].\<close>
  have hcomm_elem: "top1_group_word_product mul e invg ?sub
      \<in> top1_commutator_subgroup_on G mul e invg"
  proof -
    \<comment> \<open>word\_product of [(a,T),(b,T),(a,F),(b,F)] = mul(a, mul(b, mul(invg a, mul(invg b, e))))
       = commutator(a, b) after simplification with group axioms.\<close>
    have "top1_group_word_product mul e invg ?sub
        = top1_group_commutator_on mul invg (a j) (b j)"
    proof -
      \<comment> \<open>wp [(a,T),(b,T),(a,F),(b,F)] = mul(a, mul(b, mul(invg a, mul(invg b, e))))
         = mul(a, mul(b, mul(invg a, invg b)))  [right identity on invg b]
         = mul(mul(mul(a, b), invg a), invg b)  [associativity]
         = commutator(a, b).\<close>
      have hrid_invb: "mul (invg (b j)) e = invg (b j)"
        using hG hbj unfolding top1_is_group_on_def by (by100 blast)
      \<comment> \<open>Step-by-step unfolding of word\_product.\<close>
      have "top1_group_word_product mul e invg ?sub
          = mul (a j) (mul (b j) (mul (invg (a j)) (mul (invg (b j)) e)))"
        by (by5000 simp)
      also have "\<dots> = mul (a j) (mul (b j) (mul (invg (a j)) (invg (b j))))"
        using hrid_invb by (by100 simp)
      also have "\<dots> = top1_group_commutator_on mul invg (a j) (b j)"
      proof -
        have hassoc: "\<forall>x\<in>G. \<forall>y\<in>G. \<forall>z\<in>G. mul (mul x y) z = mul x (mul y z)"
          using hG unfolding top1_is_group_on_def by (by100 blast)
        have hinva: "invg (a j) \<in> G" using hG haj unfolding top1_is_group_on_def by (by100 blast)
        have hinvb: "invg (b j) \<in> G" using hG hbj unfolding top1_is_group_on_def by (by100 blast)
        have hab: "mul (a j) (b j) \<in> G" using hG haj hbj unfolding top1_is_group_on_def by (by100 blast)
        \<comment> \<open>mul(a, mul(b, mul(ia, ib))) = mul(mul(a, b), mul(ia, ib)) [assoc on a,b,mul(ia,ib)]\<close>
        have h1: "mul (a j) (mul (b j) (mul (invg (a j)) (invg (b j))))
            = mul (mul (a j) (b j)) (mul (invg (a j)) (invg (b j)))"
        proof -
          have "mul (invg (a j)) (invg (b j)) \<in> G"
            using hG hinva hinvb unfolding top1_is_group_on_def by (by100 blast)
          have "mul (mul (a j) (b j)) (mul (invg (a j)) (invg (b j)))
              = mul (a j) (mul (b j) (mul (invg (a j)) (invg (b j))))"
            apply (rule hassoc[unfolded Ball_def, THEN spec, THEN mp, THEN spec, THEN mp, THEN spec, THEN mp])
            apply (rule haj) apply (rule hbj) apply (rule \<open>mul (invg (a j)) (invg (b j)) \<in> G\<close>)
            done
          thus ?thesis by (by100 simp)
        qed
        \<comment> \<open>mul(mul(a,b), mul(ia, ib)) = mul(mul(mul(a,b), ia), ib) [assoc on ab, ia, ib]\<close>
        have h2: "mul (mul (a j) (b j)) (mul (invg (a j)) (invg (b j)))
            = mul (mul (mul (a j) (b j)) (invg (a j))) (invg (b j))"
        proof -
          have "mul (mul (mul (a j) (b j)) (invg (a j))) (invg (b j))
              = mul (mul (a j) (b j)) (mul (invg (a j)) (invg (b j)))"
            apply (rule hassoc[unfolded Ball_def, THEN spec, THEN mp, THEN spec, THEN mp, THEN spec, THEN mp])
            apply (rule hab) apply (rule hinva) apply (rule hinvb)
            done
          thus ?thesis by (by100 simp)
        qed
        show ?thesis unfolding top1_group_commutator_on_def using h1 h2 by (by100 simp)
      qed
      finally show ?thesis .
    qed
    moreover have "top1_group_commutator_on mul invg (a j) (b j)
        \<in> top1_commutator_subgroup_on G mul e invg"
    proof -
      have "top1_group_commutator_on mul invg (a j) (b j)
          \<in> {top1_group_commutator_on mul invg x y | x y. x \<in> G \<and> y \<in> G}"
        using haj hbj by (by100 blast)
      hence "top1_group_commutator_on mul invg (a j) (b j)
          \<in> top1_subgroup_generated_on G mul e invg
              {top1_group_commutator_on mul invg x y | x y. x \<in> G \<and> y \<in> G}"
      proof -
        have hcomms_sub: "{top1_group_commutator_on mul invg x y | x y. x \<in> G \<and> y \<in> G} \<subseteq> G"
        proof (rule subsetI)
          fix c assume "c \<in> {top1_group_commutator_on mul invg x y | x y. x \<in> G \<and> y \<in> G}"
          then obtain x y where "x \<in> G" "y \<in> G" "c = top1_group_commutator_on mul invg x y"
            by (by100 blast)
          thus "c \<in> G" using hG unfolding top1_group_commutator_on_def top1_is_group_on_def
            by (by5000 blast)
        qed
        thus ?thesis using subgroup_generated_contains[OF hG hcomms_sub]
          \<open>top1_group_commutator_on mul invg (a j) (b j) \<in> {top1_group_commutator_on mul invg x y | x y. x \<in> G \<and> y \<in> G}\<close>
          by (by100 blast)
      qed
      thus ?thesis unfolding top1_commutator_subgroup_on_def .
    qed
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>word\_product(?rest\_word) \<in> [G,G] by IH.\<close>
  have hIH: "top1_group_word_product mul e invg ?rest_word
      \<in> top1_commutator_subgroup_on G mul e invg"
  proof -
    have "\<forall>i \<in> set js. a i \<in> G \<and> b i \<in> G"
    proof (intro ballI)
      fix i assume "i \<in> set js"
      hence "i \<in> set (j # js)" by (by100 simp)
      thus "a i \<in> G \<and> b i \<in> G"
        apply (rule Cons(2)[rule_format])
        done
    qed
    thus ?thesis by (rule Cons(1))
  qed
  \<comment> \<open>mul of two [G,G] elements \<in> [G,G].\<close>
  have hcomm_grp: "top1_is_group_on (top1_commutator_subgroup_on G mul e invg) mul e invg"
    using commutator_subgroup_is_normal[OF hG] unfolding top1_normal_subgroup_on_def by (by100 blast)
  have "mul (top1_group_word_product mul e invg ?sub) (top1_group_word_product mul e invg ?rest_word)
      \<in> top1_commutator_subgroup_on G mul e invg"
    using hcomm_grp hcomm_elem hIH unfolding top1_is_group_on_def by (by100 blast)
  thus ?case using hconcat hprod by (by100 simp)
qed

text \<open>The torus relator [a₁,b₁]⋯[aₙ,bₙ] is a product of commutators, so
  for any free group F on S with quotient π, the kernel of π (= normal closure
  of the relator) is contained in [F,F].\<close>
lemma torus_relator_commutator:
  fixes n :: nat
  assumes hfree: "top1_is_free_group_full_on F mulF eF invgF \<iota> ({..<2*n}::nat set)"
      and hpi: "top1_group_hom_on F mulF G mul \<pi>"
      and hsurj: "\<pi> ` F = G"
      and hker: "top1_group_kernel_on F eG \<pi>
           = top1_normal_subgroup_generated_on F mulF eF invgF
               {r. \<exists>w\<in>{ concat (map (\<lambda>i. [(2*i, True), (2*i+1, True),
                          (2*i, False), (2*i+1, False)]) [0..<n]) }.
                   r = top1_group_word_product mulF eF invgF
                        (map (\<lambda>(s, b). (\<iota> s, b)) w)}"
  shows "top1_group_kernel_on F eG \<pi>
       \<subseteq> top1_commutator_subgroup_on F mulF eF invgF"
proof -
  have hF_grp: "top1_is_group_on F mulF eF invgF"
    using hfree unfolding top1_is_free_group_full_on_def by (by5000 blast)
  let ?R = "{ concat (map (\<lambda>i. [(2*i, True), (2*i+1, True),
                (2*i, False), (2*i+1, False)]) [0..<n]) }"
  let ?relators = "{r. \<exists>w\<in>?R. r = top1_group_word_product mulF eF invgF
                        (map (\<lambda>(s, b). (\<iota> s, b)) w)}"
  \<comment> \<open>The relator set has one element: the word product of the commutator word.\<close>
  \<comment> \<open>This word product is a product of commutators [a_{2i}, a_{2i+1}] for i < n.
     Each commutator is in [F,F]. The product is in [F,F] (subgroup).\<close>
  \<comment> \<open>The relator word evaluates to a product of commutators \<in> [F,F].
     [F,F] is normal, so normal closure of relators \<subseteq> [F,F] = ker \<subseteq> [F,F].\<close>
  have "?relators \<subseteq> top1_commutator_subgroup_on F mulF eF invgF"
  proof (rule subsetI)
    fix r assume "r \<in> ?relators"
    then obtain w where hw: "w \<in> ?R" and hr: "r = top1_group_word_product mulF eF invgF
        (map (\<lambda>(s, b). (\<iota> s, b)) w)" by (by100 blast)
    \<comment> \<open>w is the single relator word: concat(map (\<lambda>i. ...) [0..<n]).
       word\_product of this = product of commutators [\<iota>(2i), \<iota>(2i+1)] for i < n.
       Each commutator \<in> [F,F], and [F,F] is a subgroup, so the product \<in> [F,F].\<close>
    \<comment> \<open>w is the single relator: concat of commutator sub-words.
       The word product is a product of commutator elements, each in [F,F].\<close>
    have hw_eq: "w = concat (map (\<lambda>i. [(2*i, True), (2*i+1, True),
                    (2*i, False), (2*i+1, False)]) [0..<n])"
      using hw by (by100 blast)
    \<comment> \<open>By induction on n: word\_product of this concat \<in> [F,F].\<close>
    \<comment> \<open>Rewrite: map \<iota> w = concat(map (\<lambda>i. [(\<iota>(2i),T),(\<iota>(2i+1),T),(\<iota>(2i),F),(\<iota>(2i+1),F)]) [0..<n]).\<close>
    have hmap_w: "map (\<lambda>(s,b). (\<iota> s, b)) w
        = concat (map (\<lambda>i. [(\<iota> (2*i), True), (\<iota> (2*i+1), True),
                    (\<iota> (2*i), False), (\<iota> (2*i+1), False)]) [0..<n])"
    proof -
      \<comment> \<open>General fact: map f (concat xss) = concat (map (map f) xss).\<close>
      have h1: "map (\<lambda>(s,b). (\<iota> s, b)) (concat (map (\<lambda>i. [(2*i, True), (2*i+1, True),
                (2*i, False), (2*i+1, False)]) [0..<n]))
          = concat (map (map (\<lambda>(s,b). (\<iota> s, b))) (map (\<lambda>i. [(2*i, True), (2*i+1, True),
                (2*i, False), (2*i+1, False)]) [0..<n]))"
        by (rule map_concat)
      \<comment> \<open>Simplify: map (map f) (map g xs) = map (map f \<circ> g) xs.\<close>
      have h2: "map (map (\<lambda>(s,b). (\<iota> s, b))) (map (\<lambda>i. [(2*i, True), (2*i+1, True),
                (2*i, False), (2*i+1, False)]) [0..<n])
          = map (\<lambda>i. map (\<lambda>(s,b). (\<iota> s, b)) [(2*i, True), (2*i+1, True),
                (2*i, False), (2*i+1, False)]) [0..<n]"
        by (by100 simp)
      \<comment> \<open>Each sub-list: map f [(2i,T),(2i+1,T),(2i,F),(2i+1,F)] = [(\<iota>(2i),T),...].\<close>
      have h3: "map (\<lambda>i. map (\<lambda>(s,b). (\<iota> s, b)) [(2*i, True), (2*i+1, True),
                (2*i, False), (2*i+1, False)]) [0..<n]
          = map (\<lambda>i. [(\<iota> (2*i), True), (\<iota> (2*i+1), True),
                    (\<iota> (2*i), False), (\<iota> (2*i+1), False)]) [0..<n]"
        by (by100 simp)
      from h1[unfolded h2 h3] hw_eq show ?thesis by (by100 simp)
    qed
    have "top1_group_word_product mulF eF invgF (map (\<lambda>(s,b). (\<iota> s, b)) w)
      \<in> top1_commutator_subgroup_on F mulF eF invgF"
    proof -
      have h\<iota>_in: "\<forall>s \<in> ({..<2*n}::nat set). \<iota> s \<in> F"
        using hfree unfolding top1_is_free_group_full_on_def by (by100 blast)
      have "\<forall>i \<in> set [0..<n]. \<iota> (2*i) \<in> F \<and> \<iota> (2*i+1) \<in> F"
      proof (intro ballI conjI)
        fix i assume "i \<in> set [0..<n]"
        hence "i < n" by (by100 simp)
        hence "2*i < 2*n" and "2*i+1 < 2*n" by (by100 simp)+
        show "\<iota> (2*i) \<in> F"
          apply (rule h\<iota>_in[rule_format]) using \<open>2*i < 2*n\<close> by (by100 simp)
        show "\<iota> (2*i+1) \<in> F"
          apply (rule h\<iota>_in[rule_format]) using \<open>2*i+1 < 2*n\<close> by (by100 simp)
      qed
      hence "top1_group_word_product mulF eF invgF
          (concat (map (\<lambda>i. [(\<iota> (2*i), True), (\<iota> (2*i+1), True),
                      (\<iota> (2*i), False), (\<iota> (2*i+1), False)]) [0..<n]))
        \<in> top1_commutator_subgroup_on F mulF eF invgF"
        by (rule word_product_commutator_concat_in_comm[OF hF_grp])
      thus "top1_group_word_product mulF eF invgF (map (\<lambda>(s,b). (\<iota> s, b)) w)
        \<in> top1_commutator_subgroup_on F mulF eF invgF"
        using hmap_w by (by100 simp)
    qed
    thus "r \<in> top1_commutator_subgroup_on F mulF eF invgF"
      using hr by (by100 simp)
  qed
  hence "top1_normal_subgroup_generated_on F mulF eF invgF ?relators
      \<subseteq> top1_commutator_subgroup_on F mulF eF invgF"
    by (rule normal_closure_least[OF hF_grp commutator_subgroup_is_normal[OF hF_grp]])
  thus ?thesis using hker by (by100 simp)
qed

(** from \<S>75 Theorem 75.3: H_1 of n-fold torus is free abelian of rank 2n.
    The abelianization of \<pi>_1(T_n) is free abelian on 2n generators. **)
text \<open>Transfer abelianization via isomorphism: if G \<cong> G' and H is the abelianization
  of G (with free abelian structure), then H is also the abelianization of G'.\<close>
lemma hom_image_commutator_sub:
  assumes hG: "top1_is_group_on G mulG eG invgG"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hf: "top1_group_hom_on G mulG H mulH f"
  shows "f ` (top1_commutator_subgroup_on G mulG eG invgG)
       \<subseteq> top1_commutator_subgroup_on H mulH eH invgH"
proof -
  \<comment> \<open>Key fact: for x \<in> [G,G], f(x) \<in> [H,H] because the quotient H \<rightarrow> H/[H,H]
     composed with f gives a hom G \<rightarrow> H/[H,H] (abelian target),
     so [G,G] \<subseteq> ker(\<phi> \<circ> f), meaning \<phi>(f(x)) = e for x \<in> [G,G], so f(x) \<in> [H,H].\<close>
  let ?CG = "top1_commutator_subgroup_on G mulG eG invgG"
  let ?CH = "top1_commutator_subgroup_on H mulH eH invgH"
  let ?QH = "top1_quotient_group_carrier_on H mulH ?CH"
  let ?mulQH = "top1_quotient_group_mul_on mulH"
  have h_abel_QH: "top1_is_abelianization_of ?QH ?mulQH
      (top1_group_coset_on H mulH ?CH eH)
      (\<lambda>C. top1_group_coset_on H mulH ?CH (invgH (SOME g. g \<in> H \<and> C = top1_group_coset_on H mulH ?CH g)))
      H mulH eH invgH (\<lambda>h. top1_group_coset_on H mulH ?CH h)"
    by (rule abelianization_concrete[OF hH])
  let ?\<phi> = "\<lambda>h. top1_group_coset_on H mulH ?CH h"
  let ?eQH = "top1_group_coset_on H mulH ?CH eH"
  have hQH_abel: "top1_is_abelian_group_on ?QH ?mulQH ?eQH
      (\<lambda>C. top1_group_coset_on H mulH ?CH (invgH (SOME g. g \<in> H \<and> C = top1_group_coset_on H mulH ?CH g)))"
    using h_abel_QH unfolding top1_is_abelianization_of_def by (by100 blast)
  have hQH_grp: "top1_is_group_on ?QH ?mulQH ?eQH
      (\<lambda>C. top1_group_coset_on H mulH ?CH (invgH (SOME g. g \<in> H \<and> C = top1_group_coset_on H mulH ?CH g)))"
    using hQH_abel unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hphi_hom: "top1_group_hom_on H mulH ?QH ?mulQH ?\<phi>"
    using h_abel_QH unfolding top1_is_abelianization_of_def by (by100 blast)
  have hphi_ker: "top1_group_kernel_on H ?eQH ?\<phi> = ?CH"
    using h_abel_QH unfolding top1_is_abelianization_of_def by (by100 blast)
  \<comment> \<open>\<phi> \<circ> f: G \<rightarrow> QH is a hom into an abelian group.\<close>
  have hcomp_hom: "top1_group_hom_on G mulG ?QH ?mulQH (?\<phi> \<circ> f)"
    using group_hom_comp[OF hf hphi_hom] by (by100 simp)
  \<comment> \<open>By Lemma 69.3: [G,G] \<subseteq> ker(\<phi> \<circ> f).\<close>
  have hCG_sub_ker: "?CG \<subseteq> top1_group_kernel_on G ?eQH (?\<phi> \<circ> f)"
    by (rule Lemma_69_3_commutator_in_kernel[OF hG hQH_abel hcomp_hom])
  \<comment> \<open>For x \<in> [G,G]: (\<phi> \<circ> f)(x) = eQH, meaning \<phi>(f(x)) = eQH, meaning f(x) \<in> ker(\<phi>) = [H,H].\<close>
  show ?thesis
  proof (rule image_subsetI)
    fix x assume hx: "x \<in> ?CG"
    have "x \<in> G" using hx commutator_subgroup_is_normal[OF hG]
      unfolding top1_normal_subgroup_on_def by (by100 blast)
    have "x \<in> top1_group_kernel_on G ?eQH (?\<phi> \<circ> f)"
      using hCG_sub_ker hx by (by100 blast)
    hence "(?\<phi> \<circ> f) x = ?eQH"
      unfolding top1_group_kernel_on_def by (by100 blast)
    hence "?\<phi> (f x) = ?eQH" by (by100 simp)
    have "f x \<in> H" using hf \<open>x \<in> G\<close> unfolding top1_group_hom_on_def by (by100 blast)
    hence "f x \<in> top1_group_kernel_on H ?eQH ?\<phi>"
      using \<open>?\<phi> (f x) = ?eQH\<close> unfolding top1_group_kernel_on_def by (by100 blast)
    thus "f x \<in> ?CH" using hphi_ker by (by100 simp)
  qed
qed

lemma surj_hom_image_commutator:
  assumes hG: "top1_is_group_on G mulG eG invgG"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hf: "top1_group_hom_on G mulG H mulH f"
      and hsurj: "f ` G = H"
  shows "f ` (top1_commutator_subgroup_on G mulG eG invgG)
       = top1_commutator_subgroup_on H mulH eH invgH"
proof (rule set_eqI, rule iffI)
  let ?CG = "top1_commutator_subgroup_on G mulG eG invgG"
  let ?CH = "top1_commutator_subgroup_on H mulH eH invgH"
  fix y assume "y \<in> f ` ?CG"
  thus "y \<in> ?CH" using hom_image_commutator_sub[OF hG hH hf] by (by100 blast)
next
  let ?CG = "top1_commutator_subgroup_on G mulG eG invgG"
  let ?CH = "top1_commutator_subgroup_on H mulH eH invgH"
  let ?commsH = "{top1_group_commutator_on mulH invgH x y | x y. x \<in> H \<and> y \<in> H}"
  \<comment> \<open>Every H-commutator is in f(?CG).\<close>
  have hcomms_in_image: "?commsH \<subseteq> f ` ?CG"
  proof (rule subsetI, clarify)
    fix h1 h2 assume hh1: "h1 \<in> H" and hh2: "h2 \<in> H"
    from hsurj hh1 obtain g1 where hg1: "g1 \<in> G" "f g1 = h1" by (by100 blast)
    from hsurj hh2 obtain g2 where hg2: "g2 \<in> G" "f g2 = h2" by (by100 blast)
    \<comment> \<open>f([g1,g2]) = [h1,h2] and [g1,g2] \<in> [G,G].\<close>
    have hinvg1: "invgG g1 \<in> G" using hG hg1(1) unfolding top1_is_group_on_def by (by100 blast)
    have hinvg2: "invgG g2 \<in> G" using hG hg2(1) unfolding top1_is_group_on_def by (by100 blast)
    have hg12: "mulG g1 g2 \<in> G" using hG hg1(1) hg2(1) unfolding top1_is_group_on_def by (by100 blast)
    have hg12inv1: "mulG (mulG g1 g2) (invgG g1) \<in> G"
      using hG hg12 hinvg1 unfolding top1_is_group_on_def by (by100 blast)
    \<comment> \<open>f(commutator) = commutator of images.\<close>
    have heq_unf: "f (mulG (mulG (mulG g1 g2) (invgG g1)) (invgG g2))
        = mulH (mulH (mulH h1 h2) (invgH h1)) (invgH h2)"
      using hf hg1 hg2 hinvg1 hinvg2 hg12 hg12inv1
        hom_preserves_inv[OF hG hH hf hg1(1)]
        hom_preserves_inv[OF hG hH hf hg2(1)]
      unfolding top1_group_hom_on_def by (by5000 simp)
    \<comment> \<open>[g1,g2] \<in> [G,G]: commutator is a generator of commutator subgroup.\<close>
    have hcommsG_sub_G: "{top1_group_commutator_on mulG invgG x y | x y. x \<in> G \<and> y \<in> G} \<subseteq> G"
    proof (rule subsetI, clarify)
      fix x y assume "x \<in> G" "y \<in> G"
      show "top1_group_commutator_on mulG invgG x y \<in> G"
        unfolding top1_group_commutator_on_def
        using hG \<open>x \<in> G\<close> \<open>y \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
    qed
    have "top1_group_commutator_on mulG invgG g1 g2
        \<in> {top1_group_commutator_on mulG invgG x y | x y. x \<in> G \<and> y \<in> G}"
      using hg1(1) hg2(1) by (by100 blast)
    hence hcomm_CG: "top1_group_commutator_on mulG invgG g1 g2 \<in> ?CG"
      unfolding top1_commutator_subgroup_on_def
      using subgroup_generated_contains[OF hG hcommsG_sub_G] by (by100 blast)
    \<comment> \<open>f maps this commutator to [h1,h2].\<close>
    have "f (top1_group_commutator_on mulG invgG g1 g2)
        = top1_group_commutator_on mulH invgH h1 h2"
      using heq_unf unfolding top1_group_commutator_on_def by (by100 simp)
    thus "top1_group_commutator_on mulH invgH h1 h2 \<in> f ` ?CG"
      using hcomm_CG by (by100 force)
  qed
  \<comment> \<open>f(?CG) is a subgroup of H containing all H-commutators, so [H,H] \<subseteq> f(?CG).\<close>
  have hCG_grp: "top1_is_group_on ?CG mulG eG invgG"
    using commutator_subgroup_is_normal[OF hG]
    unfolding top1_normal_subgroup_on_def by (by100 blast)
  have himage_sub: "f ` ?CG \<subseteq> H"
  proof (rule image_subsetI)
    fix x assume "x \<in> ?CG"
    hence "x \<in> G" using commutator_subgroup_is_normal[OF hG]
      unfolding top1_normal_subgroup_on_def by (by100 blast)
    thus "f x \<in> H" using hf unfolding top1_group_hom_on_def by (by100 blast)
  qed
  have himage_grp: "top1_is_group_on (f ` ?CG) mulH eH invgH"
  proof -
    have heG_CG: "eG \<in> ?CG" using hCG_grp unfolding top1_is_group_on_def by (by100 blast)
    have heH_im: "eH \<in> f ` ?CG"
      using hom_preserves_id[OF hG hH hf] heG_CG by (by100 force)
    have hmul: "\<forall>x \<in> f ` ?CG. \<forall>y \<in> f ` ?CG. mulH x y \<in> f ` ?CG"
    proof (intro ballI)
      fix fx fy assume "fx \<in> f ` ?CG" "fy \<in> f ` ?CG"
      then obtain x y where hx: "x \<in> ?CG" "fx = f x" and hy: "y \<in> ?CG" "fy = f y"
        by (by100 blast)
      have hxG: "x \<in> G" using hx(1) commutator_subgroup_is_normal[OF hG]
        unfolding top1_normal_subgroup_on_def by (by100 blast)
      have hyG: "y \<in> G" using hy(1) commutator_subgroup_is_normal[OF hG]
        unfolding top1_normal_subgroup_on_def by (by100 blast)
      have "mulG x y \<in> ?CG" using hCG_grp hx(1) hy(1)
        unfolding top1_is_group_on_def by (by100 blast)
      moreover have "mulH fx fy = f (mulG x y)"
        using hf hxG hyG hx(2) hy(2) unfolding top1_group_hom_on_def by (by100 simp)
      ultimately show "mulH fx fy \<in> f ` ?CG" by (by100 force)
    qed
    have hinv: "\<forall>x \<in> f ` ?CG. invgH x \<in> f ` ?CG"
    proof (intro ballI)
      fix fx assume "fx \<in> f ` ?CG"
      then obtain x where hx: "x \<in> ?CG" "fx = f x" by (by100 blast)
      have hxG: "x \<in> G" using hx(1) commutator_subgroup_is_normal[OF hG]
        unfolding top1_normal_subgroup_on_def by (by100 blast)
      have "invgG x \<in> ?CG" using hCG_grp hx(1)
        unfolding top1_is_group_on_def by (by100 blast)
      moreover have "invgH fx = f (invgG x)"
        using hom_preserves_inv[OF hG hH hf hxG] hx(2) by (by100 simp)
      ultimately show "invgH fx \<in> f ` ?CG" by (by100 force)
    qed
    \<comment> \<open>Assoc, id, inv all inherited from H since f(?CG) \<subseteq> H.\<close>
    have hassoc: "\<forall>x\<in>f ` ?CG. \<forall>y\<in>f ` ?CG. \<forall>z\<in>f ` ?CG.
        mulH (mulH x y) z = mulH x (mulH y z)"
      using hH himage_sub unfolding top1_is_group_on_def by (by100 blast)
    have hid: "\<forall>x\<in>f ` ?CG. mulH eH x = x \<and> mulH x eH = x"
      using hH himage_sub unfolding top1_is_group_on_def by (by100 blast)
    have hinverse: "\<forall>x\<in>f ` ?CG. mulH (invgH x) x = eH \<and> mulH x (invgH x) = eH"
      using hH himage_sub unfolding top1_is_group_on_def by (by100 blast)
    show ?thesis unfolding top1_is_group_on_def
      using heH_im hmul hinv hassoc hid hinverse by (by5000 fast)
  qed
  \<comment> \<open>By subgroup\_generated\_minimal: [H,H] = ⟨commsH⟩ \<subseteq> f(?CG).\<close>
  have h_CH_eq: "?CH = top1_subgroup_generated_on H mulH eH invgH ?commsH"
    unfolding top1_commutator_subgroup_on_def by (by100 simp)
  have h_CH_sub: "?CH \<subseteq> f ` ?CG"
    using subgroup_generated_minimal[OF hcomms_in_image himage_sub himage_grp]
    h_CH_eq by (by100 simp)
  fix y assume hy: "y \<in> ?CH"
  thus "y \<in> f ` ?CG" using h_CH_sub by (by100 blast)
qed

lemma abelianization_transfer_iso:
  assumes habel: "top1_is_abelianization_of H mulH eH invgH G mulG eG invgG \<phi>"
      and hfab: "top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>H S"
      and hiso: "top1_groups_isomorphic_on G mulG G' mulG'"
      and hG': "top1_is_group_on G' mulG' eG' invgG'"
  shows "\<exists>\<phi>' \<iota>H'.
      top1_is_abelianization_of H mulH eH invgH G' mulG' eG' invgG' \<phi>'
    \<and> top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>H' S"
proof -
  \<comment> \<open>Extract facts from habel.\<close>
  have hH_abel: "top1_is_abelian_group_on H mulH eH invgH"
    using habel unfolding top1_is_abelianization_of_def by (by100 blast)
  have hG: "top1_is_group_on G mulG eG invgG"
    using habel unfolding top1_is_abelianization_of_def by (by100 blast)
  have hphi_hom: "top1_group_hom_on G mulG H mulH \<phi>"
    using habel unfolding top1_is_abelianization_of_def by (by100 blast)
  have hphi_surj: "\<phi> ` G = H"
    using habel unfolding top1_is_abelianization_of_def by (by100 blast)
  have hphi_ker: "top1_group_kernel_on G eH \<phi> = top1_commutator_subgroup_on G mulG eG invgG"
    using habel unfolding top1_is_abelianization_of_def by (by100 blast)
  \<comment> \<open>Extract f: G \<rightarrow> G' from hiso.\<close>
  from hiso obtain f where hf_iso: "top1_group_iso_on G mulG G' mulG' f"
    unfolding top1_groups_isomorphic_on_def by (by100 blast)
  have hf_hom: "top1_group_hom_on G mulG G' mulG' f"
    using hf_iso unfolding top1_group_iso_on_def by (by100 blast)
  have hf_bij: "bij_betw f G G'"
    using hf_iso unfolding top1_group_iso_on_def by (by100 blast)
  \<comment> \<open>Get g = inv_into G f: G' \<rightarrow> G.\<close>
  let ?g = "inv_into G f"
  have hg_hom: "top1_group_hom_on G' mulG' G mulG ?g"
    by (rule bij_hom_inv_is_hom[OF hG hG' hf_bij hf_hom])
  have hg_bij: "bij_betw ?g G' G"
    using bij_betw_inv_into[OF hf_bij] by (by100 simp)
  have hg_surj: "?g ` G' = G"
    using hg_bij unfolding bij_betw_def by (by100 blast)
  \<comment> \<open>Define \<phi>' = \<phi> \<circ> g: G' \<rightarrow> H.\<close>
  let ?\<phi>' = "\<phi> \<circ> ?g"
  \<comment> \<open>\<phi>' is a homomorphism.\<close>
  have hphi'_hom: "top1_group_hom_on G' mulG' H mulH ?\<phi>'"
    using group_hom_comp[OF hg_hom hphi_hom] by (by100 simp)
  \<comment> \<open>\<phi>' is surjective.\<close>
  have hphi'_surj: "?\<phi>' ` G' = H"
  proof -
    have "?\<phi>' ` G' = \<phi> ` (?g ` G')" by (by100 auto)
    also have "\<dots> = \<phi> ` G" using hg_surj by (by100 simp)
    also have "\<dots> = H" using hphi_surj by (by100 simp)
    finally show ?thesis .
  qed
  \<comment> \<open>ker(\<phi>') = [G', G']. Key step: g maps [G',G'] onto [G,G] (surjective iso).\<close>
  have hphi'_ker: "top1_group_kernel_on G' eH ?\<phi>' = top1_commutator_subgroup_on G' mulG' eG' invgG'"
  proof (rule set_eqI, rule iffI)
    fix x' assume hx': "x' \<in> top1_group_kernel_on G' eH ?\<phi>'"
    \<comment> \<open>(\<phi> \<circ> g)(x') = eH, so g(x') \<in> ker(\<phi>) = [G,G].\<close>
    have "x' \<in> G'" using hx' unfolding top1_group_kernel_on_def by (by100 blast)
    have "\<phi> (?g x') = eH" using hx' unfolding top1_group_kernel_on_def by (by100 simp)
    have "?g x' \<in> G" using \<open>x' \<in> G'\<close> hg_hom unfolding top1_group_hom_on_def by (by100 blast)
    hence "?g x' \<in> top1_group_kernel_on G eH \<phi>"
      using \<open>\<phi> (?g x') = eH\<close> unfolding top1_group_kernel_on_def by (by100 blast)
    hence "?g x' \<in> top1_commutator_subgroup_on G mulG eG invgG"
      using hphi_ker by (by100 simp)
    \<comment> \<open>g(x') \<in> [G,G]. Apply f: f(g(x')) = x' (since f \<circ> g = id on G').\<close>
    \<comment> \<open>f([G,G]) = [G',G'] (surjective iso preserves commutator subgroup).\<close>
    have hf_image_comm: "f ` (top1_commutator_subgroup_on G mulG eG invgG)
        = top1_commutator_subgroup_on G' mulG' eG' invgG'"
      by (rule surj_hom_image_commutator[OF hG hG' hf_hom])
         (use hf_bij in \<open>unfold bij_betw_def, by100 blast\<close>)
    have "f (?g x') \<in> top1_commutator_subgroup_on G' mulG' eG' invgG'"
      using \<open>?g x' \<in> top1_commutator_subgroup_on G mulG eG invgG\<close>
        hf_image_comm by (by100 blast)
    moreover have "f (?g x') = x'"
    proof -
      have "?g x' \<in> G" using hg_hom \<open>x' \<in> G'\<close> unfolding top1_group_hom_on_def by (by100 blast)
      have "f ` G = G'" using hf_bij unfolding bij_betw_def by (by100 blast)
      hence "x' \<in> f ` G" using \<open>x' \<in> G'\<close> by (by100 blast)
      thus ?thesis by (rule f_inv_into_f)
    qed
    ultimately show "x' \<in> top1_commutator_subgroup_on G' mulG' eG' invgG'"
      by (by100 simp)
  next
    fix x' assume hx': "x' \<in> top1_commutator_subgroup_on G' mulG' eG' invgG'"
    \<comment> \<open>x' \<in> [G',G']. g(x') \<in> g([G',G']) \<subseteq> [G,G] = ker(\<phi>).\<close>
    have "x' \<in> G'" using hx' commutator_subgroup_is_normal[OF hG']
      unfolding top1_normal_subgroup_on_def by (by100 blast)
    have "?g x' \<in> ?g ` (top1_commutator_subgroup_on G' mulG' eG' invgG')"
      using hx' by (by100 blast)
    moreover have "?g ` (top1_commutator_subgroup_on G' mulG' eG' invgG')
        \<subseteq> top1_commutator_subgroup_on G mulG eG invgG"
      by (rule hom_image_commutator_sub[OF hG' hG hg_hom])
    ultimately have "?g x' \<in> top1_commutator_subgroup_on G mulG eG invgG"
      by (by100 blast)
    hence "?g x' \<in> top1_group_kernel_on G eH \<phi>"
      using hphi_ker by (by100 simp)
    hence "\<phi> (?g x') = eH"
      unfolding top1_group_kernel_on_def by (by100 blast)
    thus "x' \<in> top1_group_kernel_on G' eH ?\<phi>'"
      using \<open>x' \<in> G'\<close> unfolding top1_group_kernel_on_def by (by100 simp)
  qed
  \<comment> \<open>Assemble abelianization.\<close>
  have "top1_is_abelianization_of H mulH eH invgH G' mulG' eG' invgG' ?\<phi>'"
    unfolding top1_is_abelianization_of_def
    using hH_abel hG' hphi'_hom hphi'_surj hphi'_ker by (by100 blast)
  thus ?thesis using hfab by (by100 blast)
qed

(** from \<S>75 Theorem 75.3: The abelianization of \<pi>_1(T_n) is free abelian of rank 2n.
    Equivalently (by our definition): H_1(T_n) \<cong> Z^{2n}.
    Note: this theorem's own proof has 0 sorry, but it depends on Theorem 74.3
    (n-torus \<pi>_1 presentation) which has sorrys in the CW structure extraction. **)
theorem Theorem_75_3_H1_n_torus:
  fixes n :: nat and X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "top1_is_n_fold_torus_on X TX n"
      and "x0 \<in> X"
  shows "\<exists>(H :: 'g set set) mulH eH invgH \<iota>_S \<phi>.
           top1_is_abelianization_of H mulH eH invgH
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)
             (top1_fundamental_group_id X TX x0)
             (top1_fundamental_group_invg X TX x0)
             \<phi>
         \<and> top1_is_free_abelian_group_full_on H mulH eH invgH
             \<iota>_S ({..<2*n}::nat set)"
proof -
  \<comment> \<open>Munkres 75.3: \<pi>_1(T_n) has presentation \<langle>a_1,...,b_n | [a_1,b_1]...[a_n,b_n]\<rangle>.
     Abelianizing: the commutator relation becomes trivial, so H_1(T_n) \<cong> Z^{2n}.\<close>
  \<comment> \<open>Step 1: By Theorem 74.3, \<pi>_1(T_n) has presentation with relator [a_1,b_1]...[a_n,b_n].\<close>
  have h_presentation: "\<exists>(G::'g set) mul e invg.
      top1_group_presented_by_on G mul e invg ({..<2*n}::nat set)
        { concat (map (\<lambda>i. [(2*i, True), (2*i+1, True),
                              (2*i, False), (2*i+1, False)]) [0..<n]) }
      \<and> top1_groups_isomorphic_on G mul
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)"
    using Theorem_74_3_fund_group_n_torus[OF assms] by (by100 auto)
  \<comment> \<open>Step 2: Abelianize. The presentation ⟨a₁,b₁,...|[a₁,b₁]...[aₙ,bₙ]⟩ abelianizes to
     the free abelian group on 2n generators (commutator relator becomes trivial).\<close>
  \<comment> \<open>Step 2: Apply presented\_comm\_relator\_abelianization + abelianization\_transfer\_iso.\<close>
  from h_presentation obtain G0 :: "'g set" and mul0 e0 invg0
    where hpres0: "top1_group_presented_by_on G0 mul0 e0 invg0 ({..<2*n}::nat set)
        { concat (map (\<lambda>i. [(2*i, True), (2*i+1, True),
                              (2*i, False), (2*i+1, False)]) [0..<n]) }"
      and hiso0: "top1_groups_isomorphic_on G0 mul0
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)"
    by (by100 auto)
  \<comment> \<open>Abelianize the presented group G0: Abel(G0) is free abelian on {..<2n}.\<close>
  have habel0: "\<exists>(H :: 'g set set) mulH eH invgH \<phi> \<iota>H.
      top1_is_abelianization_of H mulH eH invgH G0 mul0 e0 invg0 \<phi>
    \<and> top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>H ({..<2*n}::nat set)"
    using hpres0[unfolded top1_group_presented_by_on_def]
    apply (elim conjE exE)
    apply (frule torus_relator_commutator, assumption+)
    apply (drule(4) abelianization_of_presented_group)
    apply (by100 blast)
    done
  \<comment> \<open>Extract the abelianization witnesses.\<close>
  from habel0 obtain H0 :: "'g set set" and mulH0 eH0 invgH0 \<phi>0 \<iota>H0
    where habel0': "top1_is_abelianization_of H0 mulH0 eH0 invgH0 G0 mul0 e0 invg0 \<phi>0"
      and hfab0: "top1_is_free_abelian_group_full_on H0 mulH0 eH0 invgH0 \<iota>H0 ({..<2*n}::nat set)"
    by (by100 blast)
  \<comment> \<open>Transfer via G0 \<cong> \<pi>_1(X) using abelianization\_transfer\_iso.\<close>
  have hpi1_grp: "top1_is_group_on
      (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_id X TX x0) (top1_fundamental_group_invg X TX x0)"
  proof -
    have "is_topology_on X TX"
      using assms(1) unfolding top1_is_n_fold_torus_on_def
        top1_quotient_of_scheme_on_def is_topology_on_strict_def by (by100 blast)
    thus ?thesis using assms(2)
      by (rule top1_fundamental_group_is_group)
  qed
  from abelianization_transfer_iso[OF habel0' hfab0 hiso0 hpi1_grp]
  show ?thesis by (by100 blast)
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
  \<comment> \<open>Step 2: Abelianize. The relator a₁²...aₘ² maps to 2(a₁+...+aₘ) in the abelianization.
     H₁ = Z^m/⟨2·sum⟩. Decompose: torsion = Z/2Z (class of sum), free = Z^{m-1}.\<close>
  show ?thesis sorry \<comment> \<open>Abelianization + Smith normal form decomposition.\<close>
qed

section \<open>*\<S>78 Constructing Compact Surfaces\<close>

lemma standard_simplex_is_polygonal_region:
  "top1_is_polygonal_region_on top1_standard_simplex 3"
proof -
  let ?vx = "\<lambda>i::nat. if i = 0 then (0::real) else if i = 1 then 1 else 0"
  let ?vy = "\<lambda>i::nat. if i = 0 then (0::real) else if i = 1 then 0 else 1"
  \<comment> \<open>Precompute: {..<3} = {0,1,2} and sum expansions.\<close>
  have h3eq: "{..<(3::nat)} = {0,1,2}" by (by100 auto)
  have hsx: "\<And>c::nat\<Rightarrow>real. (\<Sum>i<3. c i * ?vx i) = c 1"
    unfolding h3eq by (by100 simp)
  have hsy: "\<And>c::nat\<Rightarrow>real. (\<Sum>i<3. c i * ?vy i) = c 2"
    unfolding h3eq by (by100 simp)
  have hsc: "\<And>c::nat\<Rightarrow>real. (\<Sum>i<3. c i) = c 0 + c 1 + c 2"
    unfolding h3eq by (by100 simp)
  \<comment> \<open>Part 1: vertices are distinct.\<close>
  have hd: "\<forall>i<3. \<forall>j<3. i \<noteq> j \<longrightarrow> (?vx i, ?vy i) \<noteq> (?vx j, ?vy j)"
  proof (intro allI impI)
    fix i j :: nat assume "i < 3" "j < 3" "i \<noteq> j"
    hence "i \<in> {0,1,2}" "j \<in> {0,1,2}" by (by100 auto)+
    thus "(?vx i, ?vy i) \<noteq> (?vx j, ?vy j)" using \<open>i \<noteq> j\<close> by (by100 force)
  qed
  \<comment> \<open>Part 2: no vertex is convex combination of others.\<close>
  have he: "\<forall>k<3. \<not> (\<exists>c. (\<forall>i<3. i \<noteq> k \<longrightarrow> (0::real) \<le> c i)
      \<and> c k = 0 \<and> (\<Sum>i<3. c i) = 1
      \<and> ?vx k = (\<Sum>i<3. c i * ?vx i) \<and> ?vy k = (\<Sum>i<3. c i * ?vy i))"
  proof (intro allI impI)
    fix k :: nat assume hk: "k < 3"
    show "\<not> (\<exists>c. (\<forall>i<3. i \<noteq> k \<longrightarrow> 0 \<le> c i) \<and> c k = 0 \<and> (\<Sum>i<3. c i) = 1
        \<and> ?vx k = (\<Sum>i<3. c i * ?vx i) \<and> ?vy k = (\<Sum>i<3. c i * ?vy i))"
    proof
      assume "\<exists>c. (\<forall>i<3. i \<noteq> k \<longrightarrow> 0 \<le> c i) \<and> c k = 0 \<and> (\<Sum>i<3. c i) = 1
          \<and> ?vx k = (\<Sum>i<3. c i * ?vx i) \<and> ?vy k = (\<Sum>i<3. c i * ?vy i)"
      then obtain c where hc: "(\<forall>i<3. i \<noteq> k \<longrightarrow> 0 \<le> c i) \<and> c k = 0
          \<and> (\<Sum>i<3. c i) = 1 \<and> ?vx k = (\<Sum>i<3. c i * ?vx i)
          \<and> ?vy k = (\<Sum>i<3. c i * ?vy i)" by (by100 blast)
      have hck: "c k = 0" using hc by (by100 blast)
      have hcsum: "c 0 + c 1 + c 2 = 1" using hc hsc by (by100 simp)
      have hcx: "?vx k = c 1" using hc hsx by (by100 simp)
      have hcy: "?vy k = c 2" using hc hsy by (by100 simp)
      show False
      proof (cases "k = 0")
        case True thus False using hck hcx hcy hcsum by (by100 simp)
      next
        case False
        show False
        proof (cases "k = 1")
          case True thus False using hck hcx by (by100 simp)
        next
          case False
          hence "k = 2" using hk \<open>k \<noteq> 0\<close> by (by100 simp)
          thus False using hck hcy by (by100 simp)
        qed
      qed
    qed
  qed
  \<comment> \<open>Part 3: set equality. The simplex {(x,y)|x\<ge>0,y\<ge>0,x+y\<le>1} equals the convex hull.\<close>
  have hs: "top1_standard_simplex = {(x, y) | x y.
      \<exists>c. (\<forall>i<3. (0::real) \<le> c i) \<and> (\<Sum>i<3. c i) = 1
      \<and> x = (\<Sum>i<3. c i * ?vx i) \<and> y = (\<Sum>i<3. c i * ?vy i)}"
  proof (rule set_eqI)
    fix p :: "real \<times> real"
    obtain x y where hp: "p = (x, y)" by (cases p) (by100 blast)
    show "p \<in> top1_standard_simplex \<longleftrightarrow>
        p \<in> {(x, y) | x y. \<exists>c. (\<forall>i<3. 0 \<le> c i) \<and> (\<Sum>i<3. c i) = 1
            \<and> x = (\<Sum>i<3. c i * ?vx i) \<and> y = (\<Sum>i<3. c i * ?vy i)}"
    proof
      assume "p \<in> top1_standard_simplex"
      hence hx: "x \<ge> 0" and hy: "y \<ge> 0" and hxy: "x + y \<le> 1"
        using hp unfolding top1_standard_simplex_def by (by100 auto)+
      let ?c = "\<lambda>i::nat. if i = 0 then 1 - x - y else if i = 1 then x else y"
      have hcge: "\<forall>i<3. (0::real) \<le> ?c i" using hx hy hxy by (by100 auto)
      have hcsum: "(\<Sum>i<3. ?c i) = 1" using hsc by (by100 simp)
      have hcvx: "x = (\<Sum>i<3. ?c i * ?vx i)" using hsx by (by100 simp)
      have hcvy: "y = (\<Sum>i<3. ?c i * ?vy i)" using hsy by (by100 simp)
      have "\<exists>c. (\<forall>i<3. (0::real) \<le> c i) \<and> (\<Sum>i<3. c i) = 1
          \<and> x = (\<Sum>i<3. c i * ?vx i) \<and> y = (\<Sum>i<3. c i * ?vy i)"
        apply (rule exI[of _ ?c])
        using hcge hcsum hcvx hcvy by (by100 blast)
      thus "p \<in> {(x, y) | x y. \<exists>c. (\<forall>i<3. 0 \<le> c i) \<and> (\<Sum>i<3. c i) = 1
          \<and> x = (\<Sum>i<3. c i * ?vx i) \<and> y = (\<Sum>i<3. c i * ?vy i)}"
        using hp by blast
    next
      assume "p \<in> {(x, y) | x y. \<exists>c. (\<forall>i<3. 0 \<le> c i) \<and> (\<Sum>i<3. c i) = 1
          \<and> x = (\<Sum>i<3. c i * ?vx i) \<and> y = (\<Sum>i<3. c i * ?vy i)}"
      then obtain x' y' where hxy: "p = (x', y')" and "\<exists>c. (\<forall>i<3. (0::real) \<le> c i) \<and> (\<Sum>i<3. c i) = 1
          \<and> x' = (\<Sum>i<3. c i * ?vx i) \<and> y' = (\<Sum>i<3. c i * ?vy i)"
        by (by100 blast)
      hence "x = x'" "y = y'" using hp by (by100 simp)+
      then obtain c where hcge: "\<forall>i<3. (0::real) \<le> c i"
          and hcsum: "(\<Sum>i<3. c i) = 1"
          and hpx_raw: "x = (\<Sum>i<3. c i * ?vx i)" and hpy_raw: "y = (\<Sum>i<3. c i * ?vy i)"
        using \<open>\<exists>c. _\<close> by (by100 blast)
      have hpx: "x = c 1" using hpx_raw hsx by (by100 simp)
      have hpy: "y = c 2" using hpy_raw hsy by (by100 simp)
      have "c 0 + c 1 + c 2 = 1" using hcsum hsc by (by100 simp)
      have "c 0 \<ge> 0" "c 1 \<ge> 0" "c 2 \<ge> 0" using hcge by (by100 auto)+
      hence "x \<ge> 0" "y \<ge> 0" "x + y \<le> 1" using hpx hpy \<open>c 0 + c 1 + c 2 = 1\<close> \<open>c 0 \<ge> 0\<close>
        by (by100 linarith)+
      thus "p \<in> top1_standard_simplex" using hp unfolding top1_standard_simplex_def
        by (by100 auto)
    qed
  qed
  show ?thesis unfolding top1_is_polygonal_region_on_def
    apply (intro conjI)
     apply (by100 simp)
    apply (rule exI[of _ ?vx])
    apply (rule exI[of _ ?vy])
    using hd he hs unfolding top1_standard_simplex_def by (by100 blast)
qed

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
  have hreduced: "(\<exists>w. scheme = w \<and> (\<forall>a\<in>set w. snd a) \<and> length w = 0)
      \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n
            \<and> top1_elementary_scheme_equiv scheme w)
      \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m
            \<and> top1_elementary_scheme_equiv scheme w)"
    sorry \<comment> \<open>Reduction to normal form via elementary operations (Theorem 76).\<close>
  \<comment> \<open>Step 3: Each normal form corresponds to the standard surface.\<close>
  show ?thesis sorry \<comment> \<open>Normal form → homeomorphism type (S², T_n, or P_m).\<close>
qed

section \<open>Chapter 13: Classification of Covering Spaces\<close>

subsection \<open>Reviewer-requested covering space infrastructure lemmas\<close>

text \<open>Covering map is surjective.\<close>
lemma covering_map_surjective:
  assumes "top1_covering_map_on E TE B TB p"
  shows "p ` E = B"
  using assms unfolding top1_covering_map_on_def by (by100 blast)

text \<open>Every point has an evenly covered neighborhood.\<close>
lemma covering_map_evenly_covered_neighborhood:
  assumes "top1_covering_map_on E TE B TB p"
      and "b \<in> B"
  shows "\<exists>U. b \<in> U \<and> top1_evenly_covered_on E TE B TB p U"
  using assms unfolding top1_covering_map_on_def by (by100 blast)

text \<open>Unique path lifting.\<close>
lemma covering_lift_unique_path:
  assumes "top1_covering_map_on E TE B TB p"
      and "is_topology_on_strict E TE"
      and "top1_is_path_on B TB b0 b1 f"
      and "e0 \<in> E" and "p e0 = b0"
      and "top1_is_path_on E TE e0 e1 ftilde1"
      and "top1_is_path_on E TE e0 e1' ftilde2"
      and "\<forall>t\<in>I_set. p (ftilde1 t) = f t"
      and "\<forall>t\<in>I_set. p (ftilde2 t) = f t"
  shows "\<forall>t\<in>I_set. ftilde1 t = ftilde2 t"
  by (rule Lemma_54_1_uniqueness[OF assms(1,4,5,3,6,8,7,9)])

text \<open>The induced homomorphism p_*: \<pi>_1(E, e0) \<rightarrow> \<pi>_1(B, b0) is injective.\<close>
lemma covering_induced_injective:
  assumes "top1_covering_map_on E TE B TB p"
      and "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "e0 \<in> E" and "p e0 = b0"
  shows "inj_on (top1_fundamental_group_induced_on E TE e0 B TB b0 p)
      (top1_fundamental_group_carrier E TE e0)"
proof (rule inj_onI)
  fix c1 c2
  assume hc1: "c1 \<in> top1_fundamental_group_carrier E TE e0"
     and hc2: "c2 \<in> top1_fundamental_group_carrier E TE e0"
     and heq: "top1_fundamental_group_induced_on E TE e0 B TB b0 p c1
             = top1_fundamental_group_induced_on E TE e0 B TB b0 p c2"
  \<comment> \<open>Munkres: p*([α]) = p*([β]) means p∘α ~ p∘β in B.
     α, β are loops at e0 that are lifts of p∘α, p∘β.
     By Theorem 54.3: since p∘α ~ p∘β and lifts start at e0, lifts are path-homotopic in E.
     So [α] = [β].\<close>
  \<comment> \<open>Pick representatives.\<close>
  have hTE: "is_topology_on E TE" using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
  obtain \<alpha> where h\<alpha>: "\<alpha> \<in> c1" "top1_is_loop_on E TE e0 \<alpha>"
  proof -
    from hc1 obtain f where hf: "top1_is_loop_on E TE e0 f"
      and hc1_eq: "c1 = {g. top1_loop_equiv_on E TE e0 f g}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have "f \<in> c1" using hc1_eq top1_loop_equiv_on_refl[OF hf] by (by100 blast)
    thus ?thesis using that hf by (by100 blast)
  qed
  obtain \<beta> where h\<beta>: "\<beta> \<in> c2" "top1_is_loop_on E TE e0 \<beta>"
  proof -
    from hc2 obtain f where hf: "top1_is_loop_on E TE e0 f"
      and hc2_eq: "c2 = {g. top1_loop_equiv_on E TE e0 f g}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have "f \<in> c2" using hc2_eq top1_loop_equiv_on_refl[OF hf] by (by100 blast)
    thus ?thesis using that hf by (by100 blast)
  qed
  \<comment> \<open>p∘α and p∘β are path-homotopic in B (from heq).\<close>
  have hp_cont: "top1_continuous_map_on E TE B TB p"
    using assms(1) by (rule top1_covering_map_on_continuous)
  have hpa_loop: "top1_is_loop_on B TB b0 (p \<circ> \<alpha>)"
    using top1_continuous_map_loop_early[OF hp_cont h\<alpha>(2)] assms(5) by (by100 simp)
  have hpb_loop: "top1_is_loop_on B TB b0 (p \<circ> \<beta>)"
    using top1_continuous_map_loop_early[OF hp_cont h\<beta>(2)] assms(5) by (by100 simp)
  have hpab_hom: "top1_path_homotopic_on B TB b0 b0 (p \<circ> \<alpha>) (p \<circ> \<beta>)"
  proof -
    have hTB: "is_topology_on B TB" using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
    \<comment> \<open>p* is a group homomorphism, so p*(c2) \<in> \<pi>_1(B, b0).\<close>
    have hp_hom: "top1_group_hom_on
        (top1_fundamental_group_carrier E TE e0) (top1_fundamental_group_mul E TE e0)
        (top1_fundamental_group_carrier B TB b0) (top1_fundamental_group_mul B TB b0)
        (top1_fundamental_group_induced_on E TE e0 B TB b0 p)"
    proof -
      have "b0 \<in> B" using assms(1,4,5) unfolding top1_covering_map_on_def by (by100 blast)
      thus ?thesis
        by (rule top1_fundamental_group_induced_on_is_hom[OF hTE hTB assms(4) _ hp_cont assms(5)])
    qed
    have hp_c2: "top1_fundamental_group_induced_on E TE e0 B TB b0 p c2
        \<in> top1_fundamental_group_carrier B TB b0"
      using hp_hom hc2 unfolding top1_group_hom_on_def by (by100 blast)
    \<comment> \<open>p\<circ>\<alpha> \<in> p*(c1) = p*(c2) and p\<circ>\<beta> \<in> p*(c2).\<close>
    have hpa_in: "p \<circ> \<alpha> \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p c1"
      unfolding top1_fundamental_group_induced_on_def
      using h\<alpha>(1) top1_loop_equiv_on_refl[OF hpa_loop] by (by100 blast)
    have hpb_in: "p \<circ> \<beta> \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p c2"
      unfolding top1_fundamental_group_induced_on_def
      using h\<beta>(1) top1_loop_equiv_on_refl[OF hpb_loop] by (by100 blast)
    \<comment> \<open>Since p*(c1) = p*(c2), both p\<circ>\<alpha> and p\<circ>\<beta> are in p*(c2) \<in> \<pi>_1(B, b0).\<close>
    have hpa_in2: "p \<circ> \<alpha> \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p c2"
      using hpa_in heq by (by100 simp)
    \<comment> \<open>Two members of the same \<pi>_1 class are loop-equivalent.\<close>
    have "top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>) (p \<circ> \<beta>)"
      by (rule fundamental_group_class_members_equiv[OF hTB hp_c2 hpa_in2 hpb_in])
    thus ?thesis unfolding top1_loop_equiv_on_def by (by100 blast)
  qed
  \<comment> \<open>α, β lift p∘α, p∘β from e0.\<close>
  have h\<alpha>_lift: "\<forall>s\<in>I_set. p (\<alpha> s) = (p \<circ> \<alpha>) s" by (by100 simp)
  have h\<beta>_lift: "\<forall>s\<in>I_set. p (\<beta> s) = (p \<circ> \<beta>) s" by (by100 simp)
  \<comment> \<open>Apply Theorem 54.3.\<close>
  have h\<alpha>_path: "top1_is_path_on E TE e0 e0 \<alpha>"
    using h\<alpha>(2) unfolding top1_is_loop_on_def by (by100 blast)
  have h\<beta>_path: "top1_is_path_on E TE e0 e0 \<beta>"
    using h\<beta>(2) unfolding top1_is_loop_on_def by (by100 blast)
  have hpa_path: "top1_is_path_on B TB b0 b0 (p \<circ> \<alpha>)"
    using hpa_loop unfolding top1_is_loop_on_def by (by100 blast)
  have hpb_path: "top1_is_path_on B TB b0 b0 (p \<circ> \<beta>)"
    using hpb_loop unfolding top1_is_loop_on_def by (by100 blast)
  have hTB: "is_topology_on B TB" using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
  from Theorem_54_3[OF assms(1) hTE hTB assms(4,5) hpa_path hpb_path hpab_hom
      h\<alpha>_path h\<alpha>_lift h\<beta>_path h\<beta>_lift]
  have h\<alpha>\<beta>_hom: "top1_path_homotopic_on E TE e0 e0 \<alpha> \<beta>" by (by100 blast)
  \<comment> \<open>Path homotopic loops are loop-equivalent.\<close>
  hence h\<alpha>\<beta>_equiv: "top1_loop_equiv_on E TE e0 \<alpha> \<beta>"
    unfolding top1_loop_equiv_on_def top1_is_loop_on_def
    using h\<alpha>_path h\<beta>_path by (by100 blast)
  \<comment> \<open>So c1 = c2: \<alpha> \<in> c1, \<beta> \<in> c2, and \<alpha> ~ \<beta>.\<close>
  show "c1 = c2"
  proof -
    \<comment> \<open>c1 and c2 are equivalence classes; members of the same class implies classes equal.\<close>
    from hc1 obtain f1 where hf1: "top1_is_loop_on E TE e0 f1"
      "c1 = {g. top1_loop_equiv_on E TE e0 f1 g}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    from hc2 obtain f2 where hf2: "top1_is_loop_on E TE e0 f2"
      "c2 = {g. top1_loop_equiv_on E TE e0 f2 g}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>\<alpha> \<in> c1 means f1 ~ \<alpha>. \<beta> \<in> c2 means f2 ~ \<beta>.
       f1 ~ \<alpha> ~ \<beta> ~ f2 \<Rightarrow> f1 ~ f2 (transitivity + symmetry).
       So c1 = {g. f1 ~ g} = {g. f2 ~ g} = c2.\<close>
    have "top1_loop_equiv_on E TE e0 f1 \<alpha>" using h\<alpha>(1) hf1(2) by (by100 blast)
    moreover have "top1_loop_equiv_on E TE e0 f2 \<beta>" using h\<beta>(1) hf2(2) by (by100 blast)
    ultimately have "top1_loop_equiv_on E TE e0 f1 f2"
    proof -
      assume hf1a: "top1_loop_equiv_on E TE e0 f1 \<alpha>"
         and hf2b: "top1_loop_equiv_on E TE e0 f2 \<beta>"
      have "top1_loop_equiv_on E TE e0 f1 \<beta>"
        by (rule top1_loop_equiv_on_trans[OF hTE hf1a h\<alpha>\<beta>_equiv])
      hence "top1_loop_equiv_on E TE e0 f1 f2"
        using top1_loop_equiv_on_sym[OF hf2b]
        by (rule top1_loop_equiv_on_trans[OF hTE])
      thus ?thesis .
    qed
    hence "\<And>g. top1_loop_equiv_on E TE e0 f1 g \<longleftrightarrow> top1_loop_equiv_on E TE e0 f2 g"
    proof -
      fix g
      assume hf12: "top1_loop_equiv_on E TE e0 f1 f2"
      show "top1_loop_equiv_on E TE e0 f1 g \<longleftrightarrow> top1_loop_equiv_on E TE e0 f2 g"
      proof
        assume h: "top1_loop_equiv_on E TE e0 f1 g"
        show "top1_loop_equiv_on E TE e0 f2 g"
          by (rule top1_loop_equiv_on_trans[OF hTE top1_loop_equiv_on_sym[OF hf12] h])
      next
        assume h: "top1_loop_equiv_on E TE e0 f2 g"
        show "top1_loop_equiv_on E TE e0 f1 g"
          by (rule top1_loop_equiv_on_trans[OF hTE hf12 h])
      qed
    qed
    thus "c1 = c2" using hf1(2) hf2(2) by (by100 blast)
  qed
qed

text \<open>deck\_transformation\_homeomorphism and deck\_transformations\_group are defined
  after the top1\_covering\_transformation\_on definition in \<S>81.\<close>

text \<open>General lift uniqueness: if two continuous maps into a covering space
  agree at one point, both lift the same base map, and the domain is connected,
  then they agree everywhere.\<close>
lemma covering_lift_unique_connected:
  assumes hcov: "top1_covering_map_on E TE B TB p"
      and hTY: "is_topology_on Y TY" and hTB: "is_topology_on B TB" and hTE: "is_topology_on E TE"
      and hconn: "top1_connected_on Y TY"
      and hf1: "top1_continuous_map_on Y TY E TE f1"
      and hf2: "top1_continuous_map_on Y TY E TE f2"
      and hlift1: "\<forall>y\<in>Y. p (f1 y) = p (f2 y)"
      and hagree: "y0 \<in> Y" and hf1f2: "f1 y0 = f2 y0"
  shows "\<forall>y\<in>Y. f1 y = f2 y"
proof -
  \<comment> \<open>S = agreement set = {y \<in> Y | f1(y) = f2(y)}. Show S is open, closed, non-empty in Y.
     Y connected \<Rightarrow> S = Y.\<close>
  let ?S = "{y \<in> Y. f1 y = f2 y}"
  have hS_ne: "?S \<noteq> {}" using hagree hf1f2 by (by100 blast)
  \<comment> \<open>S is open: for y \<in> S, p(f1(y)) = p(f2(y)) has an evenly covered nbhd U.
     f1(y) = f2(y) lies in one sheet V₀. Near y, both f1 and f2 map into V₀
     (by continuity), and p is injective on V₀, so f1 = f2 near y.\<close>
  have hS_open: "?S \<in> TY"
  proof -
    \<comment> \<open>For each y \<in> S, find open neighborhood contained in S.\<close>
    have "\<forall>y\<in>?S. \<exists>W\<in>TY. y \<in> W \<and> W \<subseteq> ?S"
    proof (intro ballI)
      fix y assume hy: "y \<in> ?S"
      hence hyY: "y \<in> Y" and hf12: "f1 y = f2 y" by (by100 blast)+
      have hf1Y: "f1 y \<in> E" using hf1 hyY unfolding top1_continuous_map_on_def by (by100 blast)
      have hpf1: "p (f1 y) \<in> B"
        using hcov hf1Y unfolding top1_covering_map_on_def top1_continuous_map_on_def by (by100 blast)
      \<comment> \<open>Get evenly covered U of p(f1(y)).\<close>
      obtain U where hU: "p (f1 y) \<in> U" and hec: "top1_evenly_covered_on E TE B TB p U"
        using hcov hpf1 unfolding top1_covering_map_on_def by (by100 blast)
      obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E TE V"
          and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
          and hV_cover: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
          and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                       (subspace_topology B TB U) p"
        using hec unfolding top1_evenly_covered_on_def by blast
      \<comment> \<open>f1(y) is in some sheet V₀.\<close>
      have "f1 y \<in> {x\<in>E. p x \<in> U}" using hf1Y hU by (by100 blast)
      hence "f1 y \<in> \<Union>\<V>" using hV_cover by (by100 simp)
      then obtain V0 where hV0: "V0 \<in> \<V>" and hf1V0: "f1 y \<in> V0" by (by100 blast)
      \<comment> \<open>f2(y) = f1(y) \<in> V₀.\<close>
      have hf2V0: "f2 y \<in> V0" using hf12 hf1V0 by (by100 simp)
      \<comment> \<open>V₀ is open in E.\<close>
      have hV0_openE: "openin_on E TE V0" using hV_open hV0 by (by100 blast)
      have hV0_sub: "V0 \<subseteq> E" using hV0_openE unfolding openin_on_def by (by100 blast)
      have hV0_TE: "V0 \<in> TE" using hV0_openE unfolding openin_on_def by (by100 blast)
      \<comment> \<open>f1⁻¹(V₀) and f2⁻¹(V₀) are open in Y.\<close>
      have hf1_preV0: "{y\<in>Y. f1 y \<in> V0} \<in> TY"
        using hf1 hV0_TE unfolding top1_continuous_map_on_def by (by100 blast)
      have hf2_preV0: "{y\<in>Y. f2 y \<in> V0} \<in> TY"
        using hf2 hV0_TE unfolding top1_continuous_map_on_def by (by100 blast)
      \<comment> \<open>W = f1⁻¹(V₀) \<inter> f2⁻¹(V₀) is open in Y.\<close>
      let ?W = "{y\<in>Y. f1 y \<in> V0} \<inter> {y\<in>Y. f2 y \<in> V0}"
      have hW_TY: "?W \<in> TY"
      proof -
        have "{y\<in>Y. f1 y \<in> V0} \<inter> {y\<in>Y. f2 y \<in> V0} \<in> TY"
        proof -
          have hinter: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TY \<longrightarrow> \<Inter>F \<in> TY"
            using hTY unfolding is_topology_on_def by (by100 blast)
          let ?A = "{y\<in>Y. f1 y \<in> V0}" and ?B = "{y\<in>Y. f2 y \<in> V0}"
          have hfin: "finite {?A, ?B}" by (by100 simp)
          have hne: "{?A, ?B} \<noteq> {}" by (by100 blast)
          have hsub: "{?A, ?B} \<subseteq> TY" using hf1_preV0 hf2_preV0 by (by100 blast)
          have "\<Inter>{?A, ?B} \<in> TY"
            using hinter hfin hne hsub by (by100 blast)
          moreover have "\<Inter>{?A, ?B} = ?A \<inter> ?B" by (by100 auto)
          ultimately show ?thesis by (by100 simp)
        qed
        thus ?thesis by (by100 simp)
      qed
      have hyW: "y \<in> ?W" using hyY hf1V0 hf2V0 by (by100 blast)
      \<comment> \<open>On W, f1 = f2 (p injective on V₀).\<close>
      have hW_sub_S: "?W \<subseteq> ?S"
      proof (rule subsetI)
        fix z assume hz: "z \<in> ?W"
        hence hzY: "z \<in> Y" and hf1z_V0: "f1 z \<in> V0" and hf2z_V0: "f2 z \<in> V0"
          by (by100 blast)+
        have "p (f1 z) = p (f2 z)" using hlift1 hzY by (by100 blast)
        \<comment> \<open>p is injective on V₀ (homeomorphism, hence bij_betw, hence inj_on).\<close>
        have hp_inj: "inj_on p V0"
          using hV_homeo hV0 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have "f1 z = f2 z" using hp_inj hf1z_V0 hf2z_V0 \<open>p (f1 z) = p (f2 z)\<close>
          unfolding inj_on_def by (by100 blast)
        thus "z \<in> ?S" using hzY by (by100 blast)
      qed
      show "\<exists>W\<in>TY. y \<in> W \<and> W \<subseteq> ?S"
        apply (rule bexI[where x="?W"])
        using hyW hW_sub_S hW_TY by (by100 blast)+
    qed
    \<comment> \<open>S is a union of open sets, hence open.\<close>
    have "?S = \<Union>{W \<in> TY. W \<subseteq> ?S}"
    proof (rule set_eqI)
      fix y show "y \<in> ?S \<longleftrightarrow> y \<in> \<Union>{W \<in> TY. W \<subseteq> ?S}"
      proof
        assume "y \<in> ?S"
        then obtain W where "W \<in> TY" "y \<in> W" "W \<subseteq> ?S"
          using \<open>\<forall>y\<in>?S. _\<close> by (by100 blast)
        thus "y \<in> \<Union>{W \<in> TY. W \<subseteq> ?S}" by (by100 blast)
      next
        assume "y \<in> \<Union>{W \<in> TY. W \<subseteq> ?S}"
        thus "y \<in> ?S" by (by100 blast)
      qed
    qed
    moreover have "\<Union>{W \<in> TY. W \<subseteq> ?S} \<in> TY"
    proof -
      have hunion: "\<forall>U. U \<subseteq> TY \<longrightarrow> \<Union>U \<in> TY"
        using hTY unfolding is_topology_on_def by (by100 blast)
      have "{W \<in> TY. W \<subseteq> ?S} \<subseteq> TY" by (by100 blast)
      thus ?thesis using hunion by (by100 blast)
    qed
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Y \ S is open: for y \<in> Y \ S, f1(y) \<noteq> f2(y). Since p(f1(y)) = p(f2(y)),
     f1(y) and f2(y) lie in different sheets V₁, V₂ over the same U.
     Near y, f1 maps into V₁ and f2 into V₂ (continuity), so f1 \<noteq> f2 near y.\<close>
  have hYmS_open: "Y - ?S \<in> TY"
  proof -
    \<comment> \<open>For each y \<in> Y \ S, find open neighborhood disjoint from S.\<close>
    have "\<forall>y\<in>Y - ?S. \<exists>W\<in>TY. y \<in> W \<and> W \<subseteq> Y - ?S"
    proof (intro ballI)
      fix y assume hy: "y \<in> Y - ?S"
      hence hyY: "y \<in> Y" and hf12_ne: "f1 y \<noteq> f2 y" by (by100 blast)+
      have hf1Y: "f1 y \<in> E" using hf1 hyY unfolding top1_continuous_map_on_def by (by100 blast)
      have hf2Y: "f2 y \<in> E" using hf2 hyY unfolding top1_continuous_map_on_def by (by100 blast)
      have hpf1: "p (f1 y) \<in> B"
        using hcov hf1Y unfolding top1_covering_map_on_def top1_continuous_map_on_def by (by100 blast)
      obtain U where hU: "p (f1 y) \<in> U" and hec: "top1_evenly_covered_on E TE B TB p U"
        using hcov hpf1 unfolding top1_covering_map_on_def by (by100 blast)
      obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E TE V"
          and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
          and hV_cover: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
          and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                       (subspace_topology B TB U) p"
        using hec unfolding top1_evenly_covered_on_def by blast
      \<comment> \<open>f1(y) and f2(y) are in different sheets (p(f1(y)) = p(f2(y)) but f1(y) \<noteq> f2(y)).\<close>
      have "f1 y \<in> {x\<in>E. p x \<in> U}" using hf1Y hU by (by100 blast)
      then obtain V1 where hV1: "V1 \<in> \<V>" and hf1V1: "f1 y \<in> V1"
        using hV_cover by (by100 blast)
      have hpf2: "p (f2 y) \<in> U"
      proof -
        have "p (f1 y) = p (f2 y)" using hlift1 hyY by (by100 blast)
        thus ?thesis using hU by (by100 simp)
      qed
      have "f2 y \<in> {x\<in>E. p x \<in> U}" using hf2Y hpf2 by (by100 blast)
      then obtain V2 where hV2: "V2 \<in> \<V>" and hf2V2: "f2 y \<in> V2"
        using hV_cover by (by100 blast)
      have hV12_ne: "V1 \<noteq> V2"
      proof
        assume "V1 = V2"
        hence "f2 y \<in> V1" using hf2V2 by (by100 simp)
        have hp_inj: "inj_on p V1"
          using hV_homeo hV1 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have "p (f1 y) = p (f2 y)" using hlift1 hyY by (by100 blast)
        hence "f1 y = f2 y"
          using hp_inj hf1V1 \<open>f2 y \<in> V1\<close> unfolding inj_on_def by (by100 blast)
        thus False using hf12_ne by (by100 blast)
      qed
      have hV1_TE: "V1 \<in> TE" using hV_open hV1 unfolding openin_on_def by (by100 blast)
      have hV2_TE: "V2 \<in> TE" using hV_open hV2 unfolding openin_on_def by (by100 blast)
      \<comment> \<open>W = f1⁻¹(V1) \<inter> f2⁻¹(V2) is open and f1 \<noteq> f2 on W (different sheets, disjoint).\<close>
      let ?W = "{y\<in>Y. f1 y \<in> V1} \<inter> {y\<in>Y. f2 y \<in> V2}"
      have hf1_pre: "{y\<in>Y. f1 y \<in> V1} \<in> TY"
        using hf1 hV1_TE unfolding top1_continuous_map_on_def by (by100 blast)
      have hf2_pre: "{y\<in>Y. f2 y \<in> V2} \<in> TY"
        using hf2 hV2_TE unfolding top1_continuous_map_on_def by (by100 blast)
      have hinter': "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TY \<longrightarrow> \<Inter>F \<in> TY"
        using hTY unfolding is_topology_on_def by (by100 blast)
      let ?A' = "{y\<in>Y. f1 y \<in> V1}" and ?B' = "{y\<in>Y. f2 y \<in> V2}"
      have hW_TY: "?W \<in> TY"
      proof -
        have hfin': "finite {?A', ?B'}" by (by100 simp)
        have hne': "{?A', ?B'} \<noteq> {}" by (by100 blast)
        have hsub': "{?A', ?B'} \<subseteq> TY" using hf1_pre hf2_pre by (by100 blast)
        have "\<Inter>{?A', ?B'} \<in> TY"
          using hinter' hfin' hne' hsub' by (by100 blast)
        moreover have "\<Inter>{?A', ?B'} = ?A' \<inter> ?B'" by (by100 auto)
        ultimately show ?thesis by (by100 simp)
      qed
      have hyW: "y \<in> ?W" using hyY hf1V1 hf2V2 by (by100 blast)
      have hW_disj: "?W \<subseteq> Y - ?S"
      proof (rule subsetI)
        fix z assume hz: "z \<in> ?W"
        hence hzY: "z \<in> Y" and hf1z_V1: "f1 z \<in> V1" and hf2z_V2: "f2 z \<in> V2"
          by (by100 blast)+
        have hV12_disj: "V1 \<inter> V2 = {}" using hV_disj hV1 hV2 hV12_ne by (by100 blast)
        have "f1 z \<noteq> f2 z"
        proof
          assume "f1 z = f2 z"
          hence "f1 z \<in> V2" using hf2z_V2 by (by100 simp)
          hence "f1 z \<in> V1 \<inter> V2" using hf1z_V1 by (by100 blast)
          thus False using hV12_disj by (by100 blast)
        qed
        thus "z \<in> Y - ?S" using hzY by (by100 blast)
      qed
      show "\<exists>W\<in>TY. y \<in> W \<and> W \<subseteq> Y - ?S"
        apply (rule bexI[where x="?W"])
        using hyW hW_disj hW_TY by (by100 blast)+
    qed
    have "Y - ?S = \<Union>{W \<in> TY. W \<subseteq> Y - ?S}"
    proof (rule set_eqI)
      fix y show "y \<in> Y - ?S \<longleftrightarrow> y \<in> \<Union>{W \<in> TY. W \<subseteq> Y - ?S}"
      proof
        assume "y \<in> Y - ?S"
        then obtain W where "W \<in> TY" "y \<in> W" "W \<subseteq> Y - ?S"
          using \<open>\<forall>y\<in>Y - ?S. _\<close> by (by100 blast)
        thus "y \<in> \<Union>{W \<in> TY. W \<subseteq> Y - ?S}" by (by100 blast)
      next
        assume "y \<in> \<Union>{W \<in> TY. W \<subseteq> Y - ?S}" thus "y \<in> Y - ?S" by (by100 blast)
      qed
    qed
    moreover have "\<Union>{W \<in> TY. W \<subseteq> Y - ?S} \<in> TY"
    proof -
      have hunion: "\<forall>U. U \<subseteq> TY \<longrightarrow> \<Union>U \<in> TY"
        using hTY unfolding is_topology_on_def by (by100 blast)
      have "{W \<in> TY. W \<subseteq> Y - ?S} \<subseteq> TY" by (by100 blast)
      thus ?thesis using hunion by (by100 blast)
    qed
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Y connected + S non-empty + S open + complement open \<Rightarrow> S = Y.\<close>
  have "?S = Y"
  proof -
    have "?S \<subseteq> Y" by (by100 blast)
    moreover have "?S \<in> TY" by (rule hS_open)
    moreover have "Y - ?S \<in> TY" by (rule hYmS_open)
    moreover have "?S \<noteq> {}" by (rule hS_ne)
    ultimately show ?thesis using hconn unfolding top1_connected_on_def by (by100 blast)
  qed
  thus ?thesis by (by100 blast)
qed

text \<open>Helper: path-connected implies connected.\<close>
lemma path_connected_imp_connected:
  assumes "top1_path_connected_on X TX"
  shows "top1_connected_on X TX"
  unfolding top1_connected_on_def
proof (intro conjI)
  have hTX: "is_topology_on X TX"
    using assms unfolding top1_path_connected_on_def by (by100 blast)
  show "is_topology_on X TX" by (rule hTX)
  show "\<nexists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X"
  proof (rule notI)
    assume "\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X"
    then obtain U0 V0 where hU0: "U0 \<in> TX" and hV0: "V0 \<in> TX" and hU0ne: "U0 \<noteq> {}"
        and hV0ne: "V0 \<noteq> {}" and hdisj: "U0 \<inter> V0 = {}" and hcover: "U0 \<union> V0 = X"
      by blast
    obtain a where ha: "a \<in> U0" using hU0ne by blast
    obtain b where hb: "b \<in> V0" using hV0ne by blast
    have haX: "a \<in> X"
    proof -
      have "a \<in> U0 \<union> V0" using ha by (by100 blast)
      thus ?thesis using hcover by (by100 simp)
    qed
    have hbX: "b \<in> X"
    proof -
      have "b \<in> U0 \<union> V0" using hb by (by100 blast)
      thus ?thesis using hcover by (by100 simp)
    qed
    \<comment> \<open>Path from a to b (path-connected).\<close>
    obtain \<gamma> where h\<gamma>: "top1_is_path_on X TX a b \<gamma>"
      using assms haX hbX unfolding top1_path_connected_on_def by (by100 auto)
    \<comment> \<open>\<gamma> maps [0,1] into X = U0 \<union> V0. The preimages \<gamma>⁻¹(U0) and \<gamma>⁻¹(V0) cover [0,1].
       \<gamma>(0) = a \<in> U0 and \<gamma>(1) = b \<in> V0. Since [0,1] is connected,
       \<gamma>⁻¹(U0) \<inter> \<gamma>⁻¹(V0) \<noteq> {}. But U0 \<inter> V0 = {}, contradiction.\<close>
    have h\<gamma>0: "\<gamma> 0 = a" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
    have h\<gamma>1: "\<gamma> 1 = b" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
    have h\<gamma>_cont: "top1_continuous_map_on I_set I_top X TX \<gamma>"
      using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
    \<comment> \<open>Preimages of U0 and V0 under \<gamma> are open in [0,1].\<close>
    have hpreU: "{s \<in> I_set. \<gamma> s \<in> U0} \<in> I_top"
      using h\<gamma>_cont hU0 unfolding top1_continuous_map_on_def by (by100 blast)
    have hpreV: "{s \<in> I_set. \<gamma> s \<in> V0} \<in> I_top"
      using h\<gamma>_cont hV0 unfolding top1_continuous_map_on_def by (by100 blast)
    \<comment> \<open>They cover [0,1] and are disjoint.\<close>
    have hcov_I: "{s \<in> I_set. \<gamma> s \<in> U0} \<union> {s \<in> I_set. \<gamma> s \<in> V0} = I_set"
    proof (rule set_eqI)
      fix s show "s \<in> {s \<in> I_set. \<gamma> s \<in> U0} \<union> {s \<in> I_set. \<gamma> s \<in> V0} \<longleftrightarrow> s \<in> I_set"
      proof
        assume "s \<in> {s \<in> I_set. \<gamma> s \<in> U0} \<union> {s \<in> I_set. \<gamma> s \<in> V0}" thus "s \<in> I_set" by (by100 blast)
      next
        assume hs: "s \<in> I_set"
        hence "\<gamma> s \<in> X" using h\<gamma>_cont unfolding top1_continuous_map_on_def by (by100 blast)
        hence "\<gamma> s \<in> U0 \<or> \<gamma> s \<in> V0" using hcover by (by100 blast)
        thus "s \<in> {s \<in> I_set. \<gamma> s \<in> U0} \<union> {s \<in> I_set. \<gamma> s \<in> V0}" using hs by (by100 blast)
      qed
    qed
    have hdisj_I: "{s \<in> I_set. \<gamma> s \<in> U0} \<inter> {s \<in> I_set. \<gamma> s \<in> V0} = {}"
      using hdisj by (by100 blast)
    have hneU: "{s \<in> I_set. \<gamma> s \<in> U0} \<noteq> {}"
    proof -
      have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      moreover have "\<gamma> 0 \<in> U0" using h\<gamma>0 ha by (by100 simp)
      ultimately show ?thesis by (by100 blast)
    qed
    have hneV: "{s \<in> I_set. \<gamma> s \<in> V0} \<noteq> {}"
    proof -
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      moreover have "\<gamma> 1 \<in> V0" using h\<gamma>1 hb by (by100 simp)
      ultimately show ?thesis by (by100 blast)
    qed
    \<comment> \<open>[0,1] is connected (I_set with I_top).\<close>
    have hI_conn: "top1_connected_on I_set I_top"
      by (rule top1_unit_interval_connected)
    \<comment> \<open>Contradiction: connected set separated by two disjoint nonempty open sets.\<close>
    show False using hI_conn hpreU hpreV hneU hneV hdisj_I hcov_I
      unfolding top1_connected_on_def by (by100 blast)
  qed
qed

text \<open>General lifting criterion (Munkres Theorem 79.1): given a covering map p: E \<rightarrow> B,
  a continuous map f: Y \<rightarrow> B with Y path-connected and locally path-connected,
  if f_*(\<pi>_1(Y)) \<subseteq> p_*(\<pi>_1(E)), then f lifts to a continuous map \<tilde>f: Y \<rightarrow> E
  with p \<circ> \<tilde>f = f and \<tilde>f(y0) = e0.\<close>
lemma general_lifting_criterion:
  assumes hcov: "top1_covering_map_on E TE B TB p"
      and hTY: "is_topology_on Y TY" and hTB: "is_topology_on B TB" and hTE: "is_topology_on E TE"
      and hf: "top1_continuous_map_on Y TY B TB f"
      and hYpc: "top1_path_connected_on Y TY"
      and hYlpc: "top1_locally_path_connected_on Y TY"
      and hy0: "y0 \<in> Y" and he0: "e0 \<in> E" and hfy0: "f y0 = p e0"
      and hsubgrp: "top1_fundamental_group_image_hom Y TY y0 B TB (p e0) f
          \<subseteq> top1_fundamental_group_image_hom E TE e0 B TB (p e0) p"
  shows "\<exists>ftilde. (\<forall>y\<in>Y. ftilde y \<in> E) \<and> (\<forall>y\<in>Y. p (ftilde y) = f y)
      \<and> ftilde y0 = e0 \<and> top1_continuous_map_on Y TY E TE ftilde"
proof -
  \<comment> \<open>Step 1: Define ftilde(y) for each y \<in> Y.
     Pick path \<alpha> from y0 to y (Y path-connected).
     f\<circ>\<alpha> is a path from f(y0) = p(e0) to f(y) in B.
     Lift f\<circ>\<alpha> to E starting at e0.
     ftilde(y) = lift endpoint.\<close>
  let ?b0 = "p e0"
  \<comment> \<open>For each y \<in> Y, obtain a path from y0 to y.\<close>
  have hpath_exists: "\<forall>y\<in>Y. \<exists>\<alpha>. top1_is_path_on Y TY y0 y \<alpha>"
    using hYpc hy0 unfolding top1_path_connected_on_def by (by100 auto)
  \<comment> \<open>For each path \<alpha>, f\<circ>\<alpha> can be lifted to E.\<close>
  have hlift_exists: "\<forall>y\<in>Y. \<forall>\<alpha>. top1_is_path_on Y TY y0 y \<alpha> \<longrightarrow>
      (\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s)))"
  proof (intro ballI allI impI)
    fix y \<alpha> assume hy: "y \<in> Y" and h\<alpha>: "top1_is_path_on Y TY y0 y \<alpha>"
    have hf\<alpha>: "top1_is_path_on B TB ?b0 (f y) (f \<circ> \<alpha>)"
    proof -
      have "top1_continuous_map_on I_set I_top B TB (f \<circ> \<alpha>)"
        by (rule top1_continuous_map_on_comp)
           (use h\<alpha> hf in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
      moreover have "(f \<circ> \<alpha>) 0 = ?b0"
        using h\<alpha> hfy0 unfolding top1_is_path_on_def by (by100 simp)
      moreover have "(f \<circ> \<alpha>) 1 = f y"
        using h\<alpha> unfolding top1_is_path_on_def by (by100 simp)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    have "\<exists>ft'. top1_is_path_on E TE e0 (ft' 1) ft' \<and> (\<forall>s\<in>I_set. p (ft' s) = (f \<circ> \<alpha>) s)"
    proof (rule Lemma_54_1_path_lifting)
      show "top1_covering_map_on E TE B TB p" by (rule hcov)
      show "e0 \<in> E" by (rule he0)
      show "p e0 = p e0" by (by100 simp)
      show "top1_is_path_on B TB (p e0) (f y) (f \<circ> \<alpha>)" by (rule hf\<alpha>)
      show "is_topology_on B TB" by (rule hTB)
      show "is_topology_on E TE" by (rule hTE)
    qed
    then obtain ft where hft: "top1_is_path_on E TE e0 (ft 1) ft"
        and hftp: "\<forall>s\<in>I_set. p (ft s) = (f \<circ> \<alpha>) s" by (by100 blast)
    have "\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s)" using hftp by (by100 simp)
    thus "\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s))"
      using hft by (by100 blast)
  qed
  \<comment> \<open>Step 2: Well-definedness. Any two paths \<alpha>1, \<alpha>2 from y0 to y give the same lift endpoint.
     \<alpha>1\<cdot>\<alpha>2\<inverse> is a loop at y0. f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) is a loop at p(e0) in B.
     [f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>)] \<in> f_*(\<pi>_1(Y)) \<subseteq> p_*(\<pi>_1(E)) (by hsubgrp).
     So there exists a loop \<delta> at e0 in E with p\<circ>\<delta> \<simeq> f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>).
     By Theorem_54_3: lifts from e0 of path-homotopic loops have same endpoints.
     The lift of f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) from e0 is a loop (since it lifts p\<circ>\<delta> which is homotopic,
     and \<delta> lifts to itself, ending at e0).
     This loop decomposes as: lift(f\<circ>\<alpha>1) followed by reverse(lift(f\<circ>\<alpha>2)).
     Both starting at e0, so the endpoints of lift(f\<circ>\<alpha>1) and lift(f\<circ>\<alpha>2) agree.\<close>
  have hwd: "\<forall>y\<in>Y. \<forall>\<alpha>1 \<alpha>2 ft1 ft2.
      top1_is_path_on Y TY y0 y \<alpha>1 \<longrightarrow>
      top1_is_path_on Y TY y0 y \<alpha>2 \<longrightarrow>
      top1_is_path_on E TE e0 (ft1 1) ft1 \<longrightarrow> (\<forall>s\<in>I_set. p (ft1 s) = f (\<alpha>1 s)) \<longrightarrow>
      top1_is_path_on E TE e0 (ft2 1) ft2 \<longrightarrow> (\<forall>s\<in>I_set. p (ft2 s) = f (\<alpha>2 s)) \<longrightarrow>
      ft1 1 = ft2 1"
  proof (intro ballI allI impI)
    fix y \<alpha>1 \<alpha>2 ft1 ft2
    assume hy: "y \<in> Y"
        and h\<alpha>1: "top1_is_path_on Y TY y0 y \<alpha>1"
        and h\<alpha>2: "top1_is_path_on Y TY y0 y \<alpha>2"
        and hft1: "top1_is_path_on E TE e0 (ft1 1) ft1"
        and hft1p: "\<forall>s\<in>I_set. p (ft1 s) = f (\<alpha>1 s)"
        and hft2: "top1_is_path_on E TE e0 (ft2 1) ft2"
        and hft2p: "\<forall>s\<in>I_set. p (ft2 s) = f (\<alpha>2 s)"
    \<comment> \<open>f\<circ>\<alpha>1 and f\<circ>\<alpha>2 are paths from p(e0) to f(y) in B.\<close>
    have hf\<alpha>1: "top1_is_path_on B TB ?b0 (f y) (f \<circ> \<alpha>1)"
    proof -
      have "top1_continuous_map_on I_set I_top B TB (f \<circ> \<alpha>1)"
        by (rule top1_continuous_map_on_comp)
           (use h\<alpha>1 hf in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
      moreover have "(f \<circ> \<alpha>1) 0 = ?b0" using h\<alpha>1 hfy0 unfolding top1_is_path_on_def by (by100 simp)
      moreover have "(f \<circ> \<alpha>1) 1 = f y" using h\<alpha>1 unfolding top1_is_path_on_def by (by100 simp)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    have hf\<alpha>2: "top1_is_path_on B TB ?b0 (f y) (f \<circ> \<alpha>2)"
    proof -
      have "top1_continuous_map_on I_set I_top B TB (f \<circ> \<alpha>2)"
        by (rule top1_continuous_map_on_comp)
           (use h\<alpha>2 hf in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
      moreover have "(f \<circ> \<alpha>2) 0 = ?b0" using h\<alpha>2 hfy0 unfolding top1_is_path_on_def by (by100 simp)
      moreover have "(f \<circ> \<alpha>2) 1 = f y" using h\<alpha>2 unfolding top1_is_path_on_def by (by100 simp)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    \<comment> \<open>ft1 lifts f\<circ>\<alpha>1 from e0, ft2 lifts f\<circ>\<alpha>2 from e0.\<close>
    have hft1_lift: "\<forall>s\<in>I_set. p (ft1 s) = (f \<circ> \<alpha>1) s"
      using hft1p by (by100 simp)
    have hft2_lift: "\<forall>s\<in>I_set. p (ft2 s) = (f \<circ> \<alpha>2) s"
      using hft2p by (by100 simp)
    \<comment> \<open>\<alpha>1\<cdot>\<alpha>2\<inverse> is a loop at y0. f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) is a loop at p(e0) in B.\<close>
    have h\<alpha>2_rev: "top1_is_path_on Y TY y y0 (top1_path_reverse \<alpha>2)"
      by (rule top1_path_reverse_is_path[OF h\<alpha>2])
    have hloop_Y: "top1_is_loop_on Y TY y0 (top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
    proof -
      have "top1_is_path_on Y TY y0 y0 (top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
        by (rule top1_path_product_is_path[OF hTY h\<alpha>1 h\<alpha>2_rev])
      thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
    qed
    \<comment> \<open>[f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>)] \<in> p_*(\<pi>_1(E,e0)): from hsubgrp (f_* \<subseteq> p_*).\<close>
    \<comment> \<open>\<Rightarrow> \<exists> loop \<delta> at e0 in E with [p\<circ>\<delta>] = [f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>)].\<close>
    \<comment> \<open>\<delta> lifts p\<circ>\<delta> from e0, ending at e0 (loop).\<close>
    \<comment> \<open>By Theorem_54_3: lift of f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) from e0 also ends at e0.\<close>
    \<comment> \<open>Now the lift of (f\<circ>\<alpha>1)\<cdot>(f\<circ>\<alpha>2)\<inverse> from e0 is: ft1 followed by lift of (f\<circ>\<alpha>2)\<inverse> from ft1(1).
       Since this composite ends at e0, the second part goes from ft1(1) to e0.
       Its reverse lifts f\<circ>\<alpha>2 from e0 to ft1(1).
       By Lemma_54_1_uniqueness: ft2 agrees with this reverse \<Rightarrow> ft2(1) = ft1(1).\<close>
    \<comment> \<open>Get \<delta>: loop at e0 in E with p\<circ>\<delta> ~ f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>).\<close>
    have hfloop: "top1_is_loop_on B TB ?b0 (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
    proof -
      have "top1_is_path_on Y TY y0 y0 (top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
        by (rule top1_path_product_is_path[OF hTY h\<alpha>1 h\<alpha>2_rev])
      hence "top1_is_path_on B TB ?b0 ?b0 (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
      proof -
        have "top1_continuous_map_on I_set I_top B TB (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
          by (rule top1_continuous_map_on_comp)
             (use \<open>top1_is_path_on Y TY y0 y0 _\<close> hf in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
        moreover have "(f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) 0 = ?b0"
          using \<open>top1_is_path_on Y TY y0 y0 _\<close> hfy0 unfolding top1_is_path_on_def by (by100 simp)
        moreover have "(f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) 1 = ?b0"
          using \<open>top1_is_path_on Y TY y0 y0 _\<close> hfy0 unfolding top1_is_path_on_def by (by100 simp)
        ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
      qed
      thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
    qed
    \<comment> \<open>[f\<circ>loop] \<in> p_*(\<pi>_1(E)). Extract \<delta> with p\<circ>\<delta> ~ f\<circ>loop.\<close>
    \<comment> \<open>The loop class of f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) is in f_*(\<pi>_1(Y)) \<subseteq> p_*(\<pi>_1(E)).\<close>
    let ?\<beta> = "top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)"
    have hclass_in_Y: "top1_fundamental_group_induced_on Y TY y0 B TB ?b0 f
        {g. top1_loop_equiv_on Y TY y0 ?\<beta> g}
      \<in> top1_fundamental_group_image_hom Y TY y0 B TB ?b0 f"
    proof -
      have "{g. top1_loop_equiv_on Y TY y0 ?\<beta> g} \<in> top1_fundamental_group_carrier Y TY y0"
        unfolding top1_fundamental_group_carrier_def
        using top1_loop_equiv_on_refl[OF hloop_Y] hloop_Y by (by100 blast)
      thus ?thesis unfolding top1_fundamental_group_image_hom_def by (by100 blast)
    qed
    \<comment> \<open>So the induced class is in p_*(\<pi>_1(E)).\<close>
    have hclass_in_E: "top1_fundamental_group_induced_on Y TY y0 B TB ?b0 f
        {g. top1_loop_equiv_on Y TY y0 ?\<beta> g}
      \<in> top1_fundamental_group_image_hom E TE e0 B TB ?b0 p"
      using hsubgrp hclass_in_Y by (by100 blast)
    \<comment> \<open>Extract \<delta>: loop at e0 with [p\<circ>\<delta>] = induced_f([loop]).\<close>
    obtain \<delta> where h\<delta>_loop: "top1_is_loop_on E TE e0 \<delta>"
        and h\<delta>_hom: "top1_path_homotopic_on B TB ?b0 ?b0
            (p \<circ> \<delta>) (f \<circ> ?\<beta>)"
    proof -
      \<comment> \<open>Unpack: hclass_in_E says the f-induced class is in the p-image of \<pi>_1(E).\<close>
      from hclass_in_E obtain c where hc: "c \<in> top1_fundamental_group_carrier E TE e0"
          and hpc: "top1_fundamental_group_induced_on E TE e0 B TB ?b0 p c
              = top1_fundamental_group_induced_on Y TY y0 B TB ?b0 f
                  {g. top1_loop_equiv_on Y TY y0 ?\<beta> g}"
        unfolding top1_fundamental_group_image_hom_def by (by100 blast)
      \<comment> \<open>c = {g. loop_equiv(E, e0, \<delta>, g)} for some loop \<delta> at e0.\<close>
      from hc obtain \<delta>' where h\<delta>': "top1_is_loop_on E TE e0 \<delta>'"
          and hc_eq: "c = {g. top1_loop_equiv_on E TE e0 \<delta>' g}"
        unfolding top1_fundamental_group_carrier_def by (by100 blast)
      \<comment> \<open>p_*(c) = {g. loop_equiv(B, p e0, p\<circ>\<delta>', g)}.\<close>
      have hp_c: "top1_fundamental_group_induced_on E TE e0 B TB ?b0 p c
          = {g. \<exists>h\<in>c. top1_loop_equiv_on B TB ?b0 (p \<circ> h) g}"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      \<comment> \<open>f_*([β]) = {g. loop_equiv(B, p e0, f\<circ>β, g)} (approximately).\<close>
      \<comment> \<open>From hpc: the two induced classes are equal as sets.
         \<delta>' \<in> c, so p\<circ>\<delta>' gives a representative of p_*(c).
         β gives a representative of f_*([β]).
         Equal classes \<Rightarrow> p\<circ>\<delta>' ~ f\<circ>β.\<close>
      have h\<delta>'_in_c: "\<delta>' \<in> c" using hc_eq top1_loop_equiv_on_refl[OF h\<delta>'] by (by100 blast)
      \<comment> \<open>p\<circ>\<delta>' is loop-equiv to itself, so it's in p_*(c).\<close>
      have hp\<delta>'_in: "p \<circ> \<delta>' \<in> {g. \<exists>h\<in>c. top1_loop_equiv_on B TB ?b0 (p \<circ> h) g}"
      proof -
        have "top1_is_loop_on B TB ?b0 (p \<circ> \<delta>')"
        proof -
          have h\<delta>'_path: "top1_is_path_on E TE e0 e0 \<delta>'"
            using h\<delta>' unfolding top1_is_loop_on_def by (by100 blast)
          have "top1_continuous_map_on I_set I_top B TB (p \<circ> \<delta>')"
            by (rule top1_continuous_map_on_comp)
               (use h\<delta>'_path top1_covering_map_on_continuous[OF hcov] in
                  \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
          moreover have "(p \<circ> \<delta>') 0 = ?b0"
            using h\<delta>'_path unfolding top1_is_path_on_def by (by100 simp)
          moreover have "(p \<circ> \<delta>') 1 = ?b0"
            using h\<delta>'_path unfolding top1_is_path_on_def by (by100 simp)
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
            by (by100 blast)
        qed
        hence "top1_loop_equiv_on B TB ?b0 (p \<circ> \<delta>') (p \<circ> \<delta>')"
          by (rule top1_loop_equiv_on_refl)
        thus ?thesis using h\<delta>'_in_c by (by100 blast)
      qed
      \<comment> \<open>f\<circ>β is loop-equiv to itself, so it's in f_*([β]).\<close>
      have hf\<beta>_in: "f \<circ> ?\<beta> \<in> {g. \<exists>h\<in>{g. top1_loop_equiv_on Y TY y0 ?\<beta> g}.
          top1_loop_equiv_on B TB ?b0 (f \<circ> h) g}"
      proof -
        have "?\<beta> \<in> {g. top1_loop_equiv_on Y TY y0 ?\<beta> g}"
          using top1_loop_equiv_on_refl[OF hloop_Y] by (by100 blast)
        moreover have "top1_loop_equiv_on B TB ?b0 (f \<circ> ?\<beta>) (f \<circ> ?\<beta>)"
          by (rule top1_loop_equiv_on_refl[OF hfloop])
        ultimately show ?thesis by (by100 blast)
      qed
      \<comment> \<open>Since p_*(c) = f_*([β]) and p\<circ>\<delta>' \<in> p_*(c), f\<circ>β \<in> f_*([β]),
         and both are equivalence classes, p\<circ>\<delta>' ~ f\<circ>β.\<close>
      have "p \<circ> \<delta>' \<in> top1_fundamental_group_induced_on E TE e0 B TB ?b0 p c"
        using hp\<delta>'_in hp_c by (by100 simp)
      hence "p \<circ> \<delta>' \<in> top1_fundamental_group_induced_on Y TY y0 B TB ?b0 f
          {g. top1_loop_equiv_on Y TY y0 ?\<beta> g}"
        using hpc by (by100 simp)
      hence "\<exists>h. top1_loop_equiv_on Y TY y0 ?\<beta> h \<and> top1_loop_equiv_on B TB ?b0 (f \<circ> h) (p \<circ> \<delta>')"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      then obtain \<beta>' where h\<beta>': "top1_loop_equiv_on Y TY y0 ?\<beta> \<beta>'"
          and hp\<delta>'_f\<beta>': "top1_loop_equiv_on B TB ?b0 (f \<circ> \<beta>') (p \<circ> \<delta>')" by (by100 blast)
      \<comment> \<open>f\<circ>β ~ f\<circ>β' (since β ~ β') and f\<circ>β' ~ p\<circ>δ'. So f\<circ>β ~ p\<circ>δ'.\<close>
      have hf\<beta>_f\<beta>': "top1_loop_equiv_on B TB ?b0 (f \<circ> ?\<beta>) (f \<circ> \<beta>')"
      proof -
        have h\<beta>'_loop: "top1_is_loop_on Y TY y0 \<beta>'"
          using h\<beta>' unfolding top1_loop_equiv_on_def by (by100 blast)
        have "top1_loop_equiv_on B TB (f y0) (f \<circ> ?\<beta>) (f \<circ> \<beta>')"
          by (rule top1_induced_preserves_loop_equiv[OF hTY hf hloop_Y h\<beta>'_loop h\<beta>'])
        thus ?thesis using hfy0 by (by100 simp)
      qed
      \<comment> \<open>Chain: f\<circ>β ~ f\<circ>β' (by hf\<beta>_f\<beta>'), f\<circ>β' ~ p\<circ>δ' (sym of hp\<delta>'_f\<beta>').\<close>
      \<comment> \<open>hp\<delta>'_f\<beta>' says f\<circ>\<beta>' ~ p\<circ>\<delta>', which is already the right direction.\<close>
      have hf\<beta>_p\<delta>': "top1_loop_equiv_on B TB ?b0 (f \<circ> ?\<beta>) (p \<circ> \<delta>')"
        by (rule top1_loop_equiv_on_trans[OF hTB hf\<beta>_f\<beta>' hp\<delta>'_f\<beta>'])
      have hp\<delta>'_f\<beta>: "top1_loop_equiv_on B TB ?b0 (p \<circ> \<delta>') (f \<circ> ?\<beta>)"
        by (rule top1_loop_equiv_on_sym[OF hf\<beta>_p\<delta>'])
      have "top1_path_homotopic_on B TB ?b0 ?b0 (p \<circ> \<delta>') (f \<circ> ?\<beta>)"
        using hp\<delta>'_f\<beta> unfolding top1_loop_equiv_on_def by (by100 blast)
      thus ?thesis using h\<delta>' that by (by100 blast)
    qed
    \<comment> \<open>By Theorem_54_3: \<delta> lifts p\<circ>\<delta> from e0 (loop \<Rightarrow> ends at e0).
       The lift of f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) from e0 also ends at e0.\<close>
    \<comment> \<open>Get a lift of f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) from e0.\<close>
    have hfloop_path: "top1_is_path_on B TB ?b0 ?b0
        (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
      using hfloop unfolding top1_is_loop_on_def by (by100 blast)
    have "\<exists>ft'. top1_is_path_on E TE e0 (ft' 1) ft'
        \<and> (\<forall>s\<in>I_set. p (ft' s) = (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) s)"
    proof (rule Lemma_54_1_path_lifting)
      show "top1_covering_map_on E TE B TB p" by (rule hcov)
      show "e0 \<in> E" by (rule he0)
      show "p e0 = p e0" by (by100 simp)
      show "top1_is_path_on B TB (p e0) ?b0
          (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))" using hfloop_path by (by100 simp)
      show "is_topology_on B TB" by (rule hTB)
      show "is_topology_on E TE" by (rule hTE)
    qed
    then obtain ft_loop where hft_loop: "top1_is_path_on E TE e0 (ft_loop 1) ft_loop"
        and hft_loop_lift: "\<forall>s\<in>I_set. p (ft_loop s) = (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) s"
      by (by100 blast)
    \<comment> \<open>By Theorem_54_3 with p\<circ>\<delta> ~ f\<circ>loop: ft_loop(1) = \<delta>(1) = e0.\<close>
    have hft_loop_end: "ft_loop 1 = e0"
    proof -
      have h\<delta>_path: "top1_is_path_on E TE e0 e0 \<delta>"
        using h\<delta>_loop unfolding top1_is_loop_on_def by (by100 blast)
      have h\<delta>_lift: "\<forall>s\<in>I_set. p (\<delta> s) = (p \<circ> \<delta>) s" by (by100 simp)
      have hp\<delta>_path: "top1_is_path_on B TB ?b0 ?b0 (p \<circ> \<delta>)"
      proof -
        have "top1_continuous_map_on I_set I_top B TB (p \<circ> \<delta>)"
          by (rule top1_continuous_map_on_comp)
             (use h\<delta>_path top1_covering_map_on_continuous[OF hcov] in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
        moreover have "(p \<circ> \<delta>) 0 = ?b0"
          using h\<delta>_path unfolding top1_is_path_on_def by (by100 simp)
        moreover have "(p \<circ> \<delta>) 1 = ?b0"
          using h\<delta>_path unfolding top1_is_path_on_def by (by100 simp)
        ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
      qed
      have "e0 = ft_loop 1 \<and> top1_path_homotopic_on E TE e0 e0 \<delta> ft_loop"
      proof (rule Theorem_54_3[OF hcov hTE hTB he0])
        show "p e0 = p e0" by (by100 simp)
        show "top1_is_path_on B TB (p e0) (p e0) (p \<circ> \<delta>)" using hp\<delta>_path by (by100 simp)
        show "top1_is_path_on B TB (p e0) (p e0) (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
          using hfloop_path by (by100 simp)
        show "top1_path_homotopic_on B TB (p e0) (p e0) (p \<circ> \<delta>)
            (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))" using h\<delta>_hom by (by100 simp)
        show "top1_is_path_on E TE e0 e0 \<delta>" by (rule h\<delta>_path)
        show "\<forall>s\<in>I_set. p (\<delta> s) = (p \<circ> \<delta>) s" by (by100 simp)
        show "top1_is_path_on E TE e0 (ft_loop 1) ft_loop" by (rule hft_loop)
        show "\<forall>s\<in>I_set. p (ft_loop s) = (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) s"
          by (rule hft_loop_lift)
      qed
      thus ?thesis by (by100 blast)
    qed
    \<comment> \<open>ft_loop lifts f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) from e0, ending at e0.
       Now use Lemma_54_1_uniqueness to relate ft_loop to ft1 and ft2.\<close>
    \<comment> \<open>The first half of ft_loop (rescaled to [0,1]) lifts f\<circ>\<alpha>1.
       By uniqueness with ft1: they agree, in particular ft_loop(1/2) = ft1(1).
       The second half reversed lifts f\<circ>\<alpha>2.
       By uniqueness with ft2: ft_loop(1/2) = ft2(1).
       So ft1(1) = ft2(1).\<close>
    \<comment> \<open>First half of ft_loop (rescaled) lifts f\<circ>\<alpha>1 from e0.
       By uniqueness with ft1: ft_loop(1/2) = ft1(1).
       Second half reversed lifts f\<circ>\<alpha>2 from e0 (since ft_loop ends at e0).
       By uniqueness with ft2: ft_loop(1/2) = ft2(1).
       Therefore ft1(1) = ft2(1).\<close>
    \<comment> \<open>g1(s) = ft_loop(s/2) is a path lifting f\<circ>\<alpha>1 from e0.\<close>
    let ?g1 = "\<lambda>s. ft_loop (s / 2)"
    have hg1_path: "top1_is_path_on E TE e0 (ft_loop (1/2)) ?g1"
    proof -
      have hft_cont: "top1_continuous_map_on I_set I_top E TE ft_loop"
        using hft_loop unfolding top1_is_path_on_def by (by100 blast)
      \<comment> \<open>The linear map s \<mapsto> s/2 is continuous from I_set to I_set.\<close>
      have hlin_cont: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>s. s / 2)"
      proof -
        have "\<And>s::real. s \<in> I_set \<Longrightarrow> s / 2 \<in> I_set"
          unfolding top1_unit_interval_def by (by100 simp)
        moreover have "continuous_on (UNIV::real set) (\<lambda>s::real. s / 2)"
          by (intro continuous_intros continuous_on_divide) auto
        ultimately have "top1_continuous_map_on I_set
            (subspace_topology (UNIV::real set) top1_open_sets I_set)
            I_set (subspace_topology (UNIV::real set) top1_open_sets I_set) (\<lambda>s. s / 2)"
          by (rule top1_continuous_map_on_real_subspace_open_sets)
        moreover have "I_top = subspace_topology (UNIV::real set) top1_open_sets I_set"
          unfolding top1_unit_interval_topology_def by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      have "top1_continuous_map_on I_set I_top E TE (\<lambda>s. ft_loop (s / 2))"
      proof -
        have "top1_continuous_map_on I_set I_top E TE (ft_loop \<circ> (\<lambda>s. s / 2))"
          by (rule top1_continuous_map_on_comp[OF hlin_cont hft_cont])
        moreover have "ft_loop \<circ> (\<lambda>s. s / 2) = (\<lambda>s. ft_loop (s / 2))"
          by (rule ext) (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      moreover have "ft_loop (0 / 2) = e0"
        using hft_loop unfolding top1_is_path_on_def by (by100 simp)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    have hg1_lift: "\<forall>s\<in>I_set. p (?g1 s) = (f \<circ> \<alpha>1) s"
    proof (intro ballI)
      fix s assume hs: "s \<in> I_set"
      hence hs01: "0 \<le> s" "s \<le> 1" unfolding top1_unit_interval_def by (by100 simp)+
      have hs2: "s / 2 \<in> I_set" unfolding top1_unit_interval_def using hs01 by (by100 simp)
      have "p (ft_loop (s / 2)) = (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (s / 2)"
        using hft_loop_lift hs2 by (by100 blast)
      also have "\<dots> = f ((top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (s / 2))" by (by100 simp)
      also have "(top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (s / 2) = \<alpha>1 (2 * (s / 2))"
        unfolding top1_path_product_def using hs01 by (by100 simp)
      also have "2 * (s / 2) = s" by (by100 simp)
      finally show "p (?g1 s) = (f \<circ> \<alpha>1) s" by (by100 simp)
    qed
    \<comment> \<open>By uniqueness: ?g1 agrees with ft1 \<Rightarrow> ft_loop(1/2) = ft1(1).\<close>
    have "ft_loop (1/2) = ft1 1"
    proof -
      have "\<forall>s\<in>I_set. ?g1 s = ft1 s"
      proof (rule Lemma_54_1_uniqueness[OF hcov he0])
        show "p e0 = p e0" by (by100 simp)
        show "top1_is_path_on B TB (p e0) (f y) (f \<circ> \<alpha>1)" using hf\<alpha>1 by (by100 simp)
        show "top1_is_path_on E TE e0 (ft_loop (1/2)) ?g1" by (rule hg1_path)
        show "\<forall>s\<in>I_set. p (?g1 s) = (f \<circ> \<alpha>1) s" by (rule hg1_lift)
        show "top1_is_path_on E TE e0 (ft1 1) ft1" by (rule hft1)
        show "\<forall>s\<in>I_set. p (ft1 s) = (f \<circ> \<alpha>1) s" using hft1_lift by (by100 simp)
      qed
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      hence "?g1 1 = ft1 1" using \<open>\<forall>s\<in>I_set. ?g1 s = ft1 s\<close> by (by100 blast)
      thus ?thesis by (by100 simp)
    qed
    \<comment> \<open>g2(s) = ft_loop(1 - s/2) lifts f\<circ>\<alpha>2 from e0 (since ft_loop(1) = e0).\<close>
    let ?g2 = "\<lambda>s. ft_loop (1 - s / 2)"
    have hg2_path: "top1_is_path_on E TE e0 (ft_loop (1/2)) ?g2"
    proof -
      have hft_cont: "top1_continuous_map_on I_set I_top E TE ft_loop"
        using hft_loop unfolding top1_is_path_on_def by (by100 blast)
      have hlin_cont2: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>s. 1 - s / 2)"
      proof -
        have "\<And>s::real. s \<in> I_set \<Longrightarrow> 1 - s / 2 \<in> I_set"
          unfolding top1_unit_interval_def by (by100 simp)
        moreover have "continuous_on (UNIV::real set) (\<lambda>s::real. 1 - s / 2)"
          by (intro continuous_intros continuous_on_divide) auto
        ultimately have "top1_continuous_map_on I_set
            (subspace_topology (UNIV::real set) top1_open_sets I_set)
            I_set (subspace_topology (UNIV::real set) top1_open_sets I_set) (\<lambda>s. 1 - s / 2)"
          by (rule top1_continuous_map_on_real_subspace_open_sets)
        moreover have "I_top = subspace_topology (UNIV::real set) top1_open_sets I_set"
          unfolding top1_unit_interval_topology_def by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      have "top1_continuous_map_on I_set I_top E TE (\<lambda>s. ft_loop (1 - s / 2))"
      proof -
        have "top1_continuous_map_on I_set I_top E TE (ft_loop \<circ> (\<lambda>s. 1 - s / 2))"
          by (rule top1_continuous_map_on_comp[OF hlin_cont2 hft_cont])
        moreover have "ft_loop \<circ> (\<lambda>s. 1 - s / 2) = (\<lambda>s. ft_loop (1 - s / 2))"
          by (rule ext) (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      moreover have "ft_loop (1 - 0 / 2) = e0"
      proof -
        have "ft_loop 1 = e0" by (rule hft_loop_end)
        thus ?thesis by (by100 simp)
      qed
      moreover have "ft_loop (1 - 1 / 2) = ft_loop (1/2)" by (by100 simp)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    have hg2_lift: "\<forall>s\<in>I_set. p (?g2 s) = (f \<circ> \<alpha>2) s"
    proof (intro ballI)
      fix s assume hs: "s \<in> I_set"
      hence hs01: "0 \<le> s" "s \<le> 1" unfolding top1_unit_interval_def by (by100 simp)+
      have hs2: "1 - s / 2 \<in> I_set" unfolding top1_unit_interval_def using hs01 by (by100 simp)
      have "p (ft_loop (1 - s / 2)) = (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2)"
        using hft_loop_lift hs2 by (by100 blast)
      also have "\<dots> = f ((top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2))" by (by100 simp)
      also have "\<dots> = f (\<alpha>2 s)"
      proof (cases "s = 1")
        case True
        \<comment> \<open>At s=1: path_product at 1/2 gives \<alpha>1(1) = y. f(\<alpha>1(1)) = f(y) = f(\<alpha>2(1)).\<close>
        have "1 - s / 2 = 1 / 2" using True by (by100 simp)
        hence "(top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2) = \<alpha>1 (2 * (1/2))"
          unfolding top1_path_product_def by (by100 simp)
        hence "f ((top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2)) = f (\<alpha>1 1)"
          by (by100 simp)
        moreover have "\<alpha>1 1 = y" using h\<alpha>1 unfolding top1_is_path_on_def by (by100 blast)
        moreover have "\<alpha>2 1 = y" using h\<alpha>2 unfolding top1_is_path_on_def by (by100 blast)
        ultimately show ?thesis using True by (by100 simp)
      next
        case False
        hence "1 - s / 2 > 1 / 2" using hs01 by (by100 linarith)
        hence "\<not> (1 - s / 2 \<le> 1 / 2)" by (by100 linarith)
        hence "(top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2)
            = (top1_path_reverse \<alpha>2) (2 * (1 - s / 2) - 1)"
          unfolding top1_path_product_def by (by100 simp)
        hence "f ((top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2))
            = f ((top1_path_reverse \<alpha>2) (1 - s))" by (by100 simp)
        moreover have "(top1_path_reverse \<alpha>2) (1 - s) = \<alpha>2 s"
          unfolding top1_path_reverse_def by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      finally show "p (?g2 s) = (f \<circ> \<alpha>2) s" by (by100 simp)
    qed
    have "ft_loop (1/2) = ft2 1"
    proof -
      have "\<forall>s\<in>I_set. ?g2 s = ft2 s"
      proof (rule Lemma_54_1_uniqueness[OF hcov he0])
        show "p e0 = p e0" by (by100 simp)
        show "top1_is_path_on B TB (p e0) (f y) (f \<circ> \<alpha>2)" using hf\<alpha>2 by (by100 simp)
        show "top1_is_path_on E TE e0 (ft_loop (1/2)) ?g2" by (rule hg2_path)
        show "\<forall>s\<in>I_set. p (?g2 s) = (f \<circ> \<alpha>2) s" by (rule hg2_lift)
        show "top1_is_path_on E TE e0 (ft2 1) ft2" by (rule hft2)
        show "\<forall>s\<in>I_set. p (ft2 s) = (f \<circ> \<alpha>2) s" using hft2_lift by (by100 simp)
      qed
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      hence "?g2 1 = ft2 1" using \<open>\<forall>s\<in>I_set. ?g2 s = ft2 s\<close> by (by100 blast)
      thus ?thesis by (by100 simp)
    qed
    show "ft1 1 = ft2 1" using \<open>ft_loop (1/2) = ft1 1\<close> \<open>ft_loop (1/2) = ft2 1\<close> by (by100 simp)
  qed
  \<comment> \<open>Step 3: Define ftilde.\<close>
  define ftilde where "ftilde y = (let \<alpha> = SOME \<alpha>. top1_is_path_on Y TY y0 y \<alpha>;
      ft = SOME ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s))
    in ft 1)" for y
  \<comment> \<open>Step 4: ftilde has the required properties.\<close>
  have hft_props: "(\<forall>y\<in>Y. ftilde y \<in> E) \<and> (\<forall>y\<in>Y. p (ftilde y) = f y) \<and> ftilde y0 = e0"
  proof -
    \<comment> \<open>For each y \<in> Y: the SOME-chosen path and lift satisfy the properties.\<close>
    have hsome_props: "\<forall>y\<in>Y. (\<exists>\<alpha> ft. top1_is_path_on Y TY y0 y \<alpha>
        \<and> top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s))
        \<and> ftilde y = ft 1)"
    proof (intro ballI)
      fix y assume hy: "y \<in> Y"
      let ?\<alpha> = "SOME \<alpha>. top1_is_path_on Y TY y0 y \<alpha>"
      have "\<exists>\<alpha>. top1_is_path_on Y TY y0 y \<alpha>" using hpath_exists hy by (by100 blast)
      hence h\<alpha>: "top1_is_path_on Y TY y0 y ?\<alpha>" by (rule someI_ex)
      let ?ft = "SOME ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (?\<alpha> s))"
      have "\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (?\<alpha> s))"
        using hlift_exists hy h\<alpha> by (by100 blast)
      hence hft: "top1_is_path_on E TE e0 (?ft 1) ?ft \<and> (\<forall>s\<in>I_set. p (?ft s) = f (?\<alpha> s))"
        by (rule someI_ex)
      have "ftilde y = ?ft 1" unfolding ftilde_def by (by100 simp)
      thus "\<exists>\<alpha> ft. top1_is_path_on Y TY y0 y \<alpha>
          \<and> top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s))
          \<and> ftilde y = ft 1"
        using h\<alpha> hft by (by100 blast)
    qed
    show ?thesis proof (intro conjI)
    show "\<forall>y\<in>Y. ftilde y \<in> E"
    proof (intro ballI)
      fix y assume "y \<in> Y"
      from hsome_props[rule_format, OF this]
      obtain \<alpha> ft where "top1_is_path_on E TE e0 (ft 1) ft" and "ftilde y = ft 1"
        by (by100 blast)
      have "ft 1 \<in> E"
      proof -
        have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        thus ?thesis using \<open>top1_is_path_on E TE e0 (ft 1) ft\<close>
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      qed
      thus "ftilde y \<in> E" using \<open>ftilde y = ft 1\<close> by (by100 simp)
    qed
  next
    show "\<forall>y\<in>Y. p (ftilde y) = f y"
    proof (intro ballI)
      fix y assume "y \<in> Y"
      from hsome_props[rule_format, OF this]
      obtain \<alpha> ft where h\<alpha>: "top1_is_path_on Y TY y0 y \<alpha>"
          and hft: "top1_is_path_on E TE e0 (ft 1) ft"
          and hftp: "\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s)"
          and hftilde: "ftilde y = ft 1" by (by100 blast)
      have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      have "p (ft 1) = f (\<alpha> 1)" using hftp h1I by (by100 blast)
      moreover have "\<alpha> 1 = y" using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
      ultimately show "p (ftilde y) = f y" using hftilde by (by100 simp)
    qed
  next
    show "ftilde y0 = e0"
    proof -
      \<comment> \<open>The SOME-chosen path from y0 to y0 gives a lift; any lift from e0 of a
         loop at p(e0) has some endpoint. But by well-definedness, the endpoint
         is the same for all paths. The constant path at y0 lifts to constant at e0.\<close>
      from hsome_props[rule_format, OF hy0]
      obtain \<alpha> ft where h\<alpha>: "top1_is_path_on Y TY y0 y0 \<alpha>"
          and hft: "top1_is_path_on E TE e0 (ft 1) ft"
          and hftp: "\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s)"
          and hftilde: "ftilde y0 = ft 1" by (by100 blast)
      \<comment> \<open>The constant path at y0 also lifts to constant at e0.\<close>
      have hconst_path: "top1_is_path_on Y TY y0 y0 (top1_constant_path y0)"
        by (rule top1_constant_path_is_path[OF hTY hy0])
      have hconst_lift: "top1_is_path_on E TE e0 e0 (top1_constant_path e0)"
        by (rule top1_constant_path_is_path[OF hTE he0])
      have hconst_liftp: "\<forall>s\<in>I_set. p ((top1_constant_path e0) s) = f ((top1_constant_path y0) s)"
      proof (intro ballI)
        fix s assume "s \<in> I_set"
        show "p ((top1_constant_path e0) s) = f ((top1_constant_path y0) s)"
          unfolding top1_constant_path_def using hfy0 by (by100 simp)
      qed
      \<comment> \<open>By well-definedness (hwd): ft 1 = e0.\<close>
      have "ft 1 = (top1_constant_path e0) 1"
      proof -
        have hcl2: "top1_is_path_on E TE e0 ((top1_constant_path e0) 1) (top1_constant_path e0)"
        proof -
          have "(top1_constant_path e0) 1 = e0" unfolding top1_constant_path_def by (by100 simp)
          thus ?thesis using hconst_lift by (by100 simp)
        qed
        from hwd[rule_format, OF hy0, of \<alpha> "top1_constant_path y0" ft "top1_constant_path e0"]
        show ?thesis using h\<alpha> hconst_path hft hftp hcl2 hconst_liftp by (by100 blast)
      qed
      hence "ft 1 = e0" unfolding top1_constant_path_def by (by100 simp)
      thus ?thesis using hftilde by (by100 simp)
    qed
    qed
  qed
  \<comment> \<open>Helper: ftilde(y') equals the endpoint of ANY lift of f\<circ>\<alpha> from e0, for any path \<alpha> from y0 to y'.\<close>
  have ftilde_eq_lift: "\<And>y' \<alpha> ft'. y' \<in> Y \<Longrightarrow> top1_is_path_on Y TY y0 y' \<alpha> \<Longrightarrow>
      top1_is_path_on E TE e0 (ft' 1) ft' \<Longrightarrow> (\<forall>s\<in>I_set. p (ft' s) = f (\<alpha> s)) \<Longrightarrow>
      ftilde y' = ft' 1"
  proof -
    fix y' \<alpha>' ft'
    assume hy': "y' \<in> Y" and h\<alpha>': "top1_is_path_on Y TY y0 y' \<alpha>'"
        and hft': "top1_is_path_on E TE e0 (ft' 1) ft'"
        and hft'p: "\<forall>s\<in>I_set. p (ft' s) = f (\<alpha>' s)"
    \<comment> \<open>Get the SOME-chosen path and lift for ftilde(y').\<close>
    let ?\<alpha>_s = "SOME \<alpha>. top1_is_path_on Y TY y0 y' \<alpha>"
    have "\<exists>\<alpha>. top1_is_path_on Y TY y0 y' \<alpha>" using hpath_exists hy' by (by100 blast)
    hence h\<alpha>_s: "top1_is_path_on Y TY y0 y' ?\<alpha>_s" by (rule someI_ex)
    let ?ft_s = "SOME ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (?\<alpha>_s s))"
    have "\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (?\<alpha>_s s))"
      using hlift_exists hy' h\<alpha>_s by (by100 blast)
    hence hft_s: "top1_is_path_on E TE e0 (?ft_s 1) ?ft_s \<and> (\<forall>s\<in>I_set. p (?ft_s s) = f (?\<alpha>_s s))"
      by (rule someI_ex)
    have hftilde_eq: "ftilde y' = ?ft_s 1" unfolding ftilde_def by (by100 simp)
    \<comment> \<open>By hwd: ft' 1 = ft_s 1.\<close>
    from hwd[rule_format, OF hy', of \<alpha>' ?\<alpha>_s ft' ?ft_s]
    have "ft' 1 = ?ft_s 1" using h\<alpha>' h\<alpha>_s hft' hft'p hft_s by (by100 blast)
    thus "ftilde y' = ft' 1" using hftilde_eq by (by100 simp)
  qed
  \<comment> \<open>Step 5: ftilde is continuous.
     For y \<in> Y, let U be evenly covered nbhd of f(y) in B.
     By local path-connectivity of Y, get path-connected open V \<ni> y with f(V) \<subseteq> U.
     Let W0 be the sheet over U containing ftilde(y).
     For y' \<in> V: extend path (y0\<rightarrow>y) with segment (y\<rightarrow>y' in V).
     The lift of the segment stays in W0 (sheets are homeomorphic to U).
     So ftilde|_V = (p|_{W0})\<inverse> \<circ> f|_V, which is continuous.\<close>
  have hft_cont: "top1_continuous_map_on Y TY E TE ftilde"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>y\<in>Y. ftilde y \<in> E" using hft_props by (by100 blast)
  next
    show "\<forall>W\<in>TE. {y \<in> Y. ftilde y \<in> W} \<in> TY"
    proof (intro ballI)
      fix W assume hW: "W \<in> TE"
      \<comment> \<open>For each y in the preimage, find a neighborhood mapping into W.\<close>
      have "\<forall>y \<in> {y \<in> Y. ftilde y \<in> W}. \<exists>V\<in>TY. y \<in> V \<and> V \<subseteq> {y \<in> Y. ftilde y \<in> W}"
      proof (intro ballI)
        fix y assume hy_pre: "y \<in> {y \<in> Y. ftilde y \<in> W}"
        hence hyY: "y \<in> Y" and hfty_W: "ftilde y \<in> W" by (by100 blast)+
        have hfty_E: "ftilde y \<in> E" using hft_props hyY by (by100 blast)
        have hfy: "p (ftilde y) = f y" using hft_props hyY by (by100 blast)
        have hfy_B: "f y \<in> B"
          using hf hyY unfolding top1_continuous_map_on_def by (by100 blast)
        \<comment> \<open>Get evenly covered U of f(y) in B.\<close>
        obtain U where hU: "f y \<in> U" and hec: "top1_evenly_covered_on E TE B TB p U"
          using hcov hfy_B unfolding top1_covering_map_on_def by (by100 blast)
        obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E TE V"
            and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
            and hV_cover: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
            and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                         (subspace_topology B TB U) p"
          using hec unfolding top1_evenly_covered_on_def by blast
        \<comment> \<open>ftilde(y) is in some sheet W0.\<close>
        have "ftilde y \<in> {x\<in>E. p x \<in> U}"
        proof -
          have "ftilde y \<in> E" by (rule hfty_E)
          moreover have "p (ftilde y) \<in> U" using hfy hU by (by100 simp)
          ultimately show ?thesis by (by100 blast)
        qed
        hence "ftilde y \<in> \<Union>\<V>" using hV_cover by (by100 simp)
        then obtain W0 where hW0: "W0 \<in> \<V>" and hfty_W0: "ftilde y \<in> W0" by (by100 blast)
        \<comment> \<open>W0 \<inter> W is open in E, contains ftilde(y).\<close>
        have hW0_open: "W0 \<in> TE" using hV_open hW0 unfolding openin_on_def by (by100 blast)
        \<comment> \<open>p is a homeomorphism on W0 → U.\<close>
        have hp_homeo: "top1_homeomorphism_on W0 (subspace_topology E TE W0) U
            (subspace_topology B TB U) p" using hV_homeo hW0 by (by100 blast)
        have hp_inj: "inj_on p W0"
          using hp_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        \<comment> \<open>U is open in B.\<close>
        have hU_open: "openin_on B TB U"
          using hec unfolding top1_evenly_covered_on_def by (by100 blast)
        have hU_TB: "U \<in> TB" using hU_open unfolding openin_on_def by (by100 blast)
        \<comment> \<open>f\<inverse>(U) is open in Y.\<close>
        have hfU: "{y\<in>Y. f y \<in> U} \<in> TY"
          using hf hU_TB unfolding top1_continuous_map_on_def by (by100 blast)
        \<comment> \<open>By local path-connectivity: get path-connected open V \<subseteq> f\<inverse>(U) with y \<in> V.\<close>
        obtain V0 where hV0_TY: "V0 \<in> TY" and hy_V0: "y \<in> V0"
            and hV0_sub: "V0 \<subseteq> {y\<in>Y. f y \<in> U}"
            and hV0_pc: "top1_path_connected_on V0 (subspace_topology Y TY V0)"
        proof -
          \<comment> \<open>f\<inverse>(U) is open in Y, contains y.\<close>
          have hfU_nbhd: "neighborhood_of y Y TY {y\<in>Y. f y \<in> U}"
            unfolding neighborhood_of_def using hfU hyY hU by (by100 blast)
          have hfU_sub: "{y\<in>Y. f y \<in> U} \<subseteq> Y" by (by100 blast)
          \<comment> \<open>By local path-connectivity of Y at y: get path-connected open V0 \<subseteq> f\<inverse>(U).\<close>
          have hlpc_y: "top1_locally_path_connected_at Y TY y"
            using hYlpc hyY unfolding top1_locally_path_connected_on_def by (by100 blast)
          obtain V0' where hV0'_nbhd: "neighborhood_of y Y TY V0'"
              and hV0'_sub: "V0' \<subseteq> {y\<in>Y. f y \<in> U}" and hV0'_Y: "V0' \<subseteq> Y"
              and hV0'_pc: "top1_path_connected_on V0' (subspace_topology Y TY V0')"
          proof -
            from hlpc_y[unfolded top1_locally_path_connected_at_def,
                rule_format, of "{y\<in>Y. f y \<in> U}"]
            show ?thesis using hfU_nbhd hfU_sub that by (by100 blast)
          qed
          \<comment> \<open>neighborhood_of means V0' \<in> TY \<and> y \<in> V0'.\<close>
          have hV0'_TY: "V0' \<in> TY" using hV0'_nbhd unfolding neighborhood_of_def by (by100 blast)
          have hy_V0': "y \<in> V0'" using hV0'_nbhd unfolding neighborhood_of_def by (by100 blast)
          show ?thesis using that[OF hV0'_TY hy_V0' hV0'_sub hV0'_pc] .
        qed
        \<comment> \<open>For y' \<in> V0: ftilde(y') \<in> W0 because the lift stays in the sheet.\<close>
        \<comment> \<open>ftilde maps V0 into W0: for y' \<in> V0, the lift of f\<circ>\<sigma> (path y\<rightarrow>y' in V0)
           from ftilde(y) stays in W0 (since f\<circ>\<sigma> stays in U and p|_{W0}: W0 \<cong> U).\<close>
        \<comment> \<open>p|_{W0} is a bijection W0 → U.\<close>
        have hp_bij: "bij_betw p W0 U"
          using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        \<comment> \<open>ftilde(y) = inv_into W0 p (f y).\<close>
        have hfty_inv: "ftilde y = inv_into W0 p (f y)"
          using inv_into_f_eq[OF hp_inj hfty_W0] hfy by (by100 simp)
        have hftilde_V0: "\<forall>y'\<in>V0. ftilde y' \<in> W0"
        proof (intro ballI)
          fix y' assume hy'V0: "y' \<in> V0"
          have hy'Y: "y' \<in> Y" using hy'V0 hV0_sub by (by100 blast)
          have hfy'U: "f y' \<in> U" using hy'V0 hV0_sub by (by100 blast)
          have hfy'_pW0: "f y' \<in> p ` W0" using hp_bij hfy'U unfolding bij_betw_def by (by100 blast)
          have hinv_y'_W0: "inv_into W0 p (f y') \<in> W0" by (rule inv_into_into[OF hfy'_pW0])
          \<comment> \<open>Path from y to y' in V0.\<close>
          obtain \<sigma> where h\<sigma>: "top1_is_path_on V0 (subspace_topology Y TY V0) y y' \<sigma>"
            using hV0_pc hy_V0 hy'V0 unfolding top1_path_connected_on_def by (by100 auto)
          \<comment> \<open>\<sigma> as ambient path.\<close>
          have hV0_sub_Y: "V0 \<subseteq> Y" using hV0_sub by (by100 blast)
          have h\<sigma>_cont_V0: "top1_continuous_map_on I_set I_top V0 (subspace_topology Y TY V0) \<sigma>"
            using h\<sigma> unfolding top1_is_path_on_def by (by100 blast)
          have h\<sigma>_in_V0: "\<forall>s\<in>I_set. \<sigma> s \<in> V0"
            using h\<sigma>_cont_V0 unfolding top1_continuous_map_on_def by (by100 blast)
          have h\<sigma>_Y: "top1_is_path_on Y TY y y' \<sigma>"
          proof -
            have hincl: "top1_continuous_map_on V0 (subspace_topology Y TY V0) Y TY (\<lambda>x. x)"
            proof -
              have "top1_continuous_map_on V0 (subspace_topology Y TY V0) Y TY (\<lambda>x. x)"
                by (rule top1_continuous_map_on_restrict_domain_simple[OF
                  top1_continuous_map_on_id[OF hTY, unfolded id_def] hV0_sub_Y])
              thus ?thesis .
            qed
            have "top1_continuous_map_on I_set I_top Y TY ((\<lambda>x. x) \<circ> \<sigma>)"
              by (rule top1_continuous_map_on_comp[OF h\<sigma>_cont_V0 hincl])
            moreover have "(\<lambda>x::'c. x) \<circ> \<sigma> = \<sigma>" by (rule ext) (by100 simp)
            ultimately have h\<sigma>_cont_Y: "top1_continuous_map_on I_set I_top Y TY \<sigma>" by (by100 simp)
            have "\<sigma> 0 = y" using h\<sigma> unfolding top1_is_path_on_def by (by100 blast)
            have "\<sigma> 1 = y'" using h\<sigma> unfolding top1_is_path_on_def by (by100 blast)
            show ?thesis unfolding top1_is_path_on_def using h\<sigma>_cont_Y \<open>\<sigma> 0 = y\<close> \<open>\<sigma> 1 = y'\<close>
              by (by100 blast)
          qed
          \<comment> \<open>Path from y0 to y.\<close>
          obtain \<alpha>0 where h\<alpha>0: "top1_is_path_on Y TY y0 y \<alpha>0"
            using hpath_exists hyY by (by100 blast)
          \<comment> \<open>Lift of f\<circ>\<alpha>0 from e0.\<close>
          obtain ft0 where hft0: "top1_is_path_on E TE e0 (ft0 1) ft0"
              and hft0p: "\<forall>s\<in>I_set. p (ft0 s) = f (\<alpha>0 s)"
            using hlift_exists hyY h\<alpha>0 by (by100 blast)
          \<comment> \<open>ft0 1 = ftilde y (by ftilde_eq_lift).\<close>
          have hft0_end: "ft0 1 = ftilde y"
            using ftilde_eq_lift[OF hyY h\<alpha>0 hft0 hft0p] by (by100 simp)
          \<comment> \<open>Concatenate: \<alpha>0\<cdot>\<sigma> is a path from y0 to y'.\<close>
          have h\<alpha>0\<sigma>: "top1_is_path_on Y TY y0 y' (top1_path_product \<alpha>0 \<sigma>)"
            by (rule top1_path_product_is_path[OF hTY h\<alpha>0 h\<sigma>_Y])
          \<comment> \<open>Construct the lift of f\<circ>(\<alpha>0\<cdot>\<sigma>) as ft0 \<cdot> (inv_into W0 p \<circ> f \<circ> \<sigma>).\<close>
          let ?inv_lift = "\<lambda>s. inv_into W0 p (f (\<sigma> s))"
          \<comment> \<open>?inv_lift is a path in W0 \<subseteq> E from ftilde(y) to inv_into W0 p (f y').\<close>
          have hinvl_path: "top1_is_path_on E TE (ftilde y) (inv_into W0 p (f y')) ?inv_lift"
          proof -
            \<comment> \<open>Continuity: inv_into W0 p \<circ> f \<circ> \<sigma> is continuous I_set \<rightarrow> E.\<close>
            \<comment> \<open>f\<circ>\<sigma>: I_set \<rightarrow> U (f continuous, \<sigma> maps V0 \<subseteq> f\<inverse>(U)).\<close>
            \<comment> \<open>inv_into W0 p: U \<rightarrow> W0 \<subseteq> E (inverse of homeomorphism).\<close>
            have hinv_cont: "top1_continuous_map_on U (subspace_topology B TB U) W0 (subspace_topology E TE W0)
                (inv_into W0 p)"
              using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
            \<comment> \<open>f\<circ>\<sigma> maps I_set into U (via V0).\<close>
            have hf\<sigma>_cont: "top1_continuous_map_on I_set I_top U (subspace_topology B TB U) (f \<circ> \<sigma>)"
            proof -
              \<comment> \<open>\<sigma>: I \<rightarrow> Y continuous, f: Y \<rightarrow> B continuous. f\<circ>\<sigma>: I \<rightarrow> B continuous.\<close>
              have h\<sigma>_cont_Y: "top1_continuous_map_on I_set I_top Y TY \<sigma>"
                using h\<sigma>_Y unfolding top1_is_path_on_def by (by100 blast)
              have "top1_continuous_map_on I_set I_top B TB (f \<circ> \<sigma>)"
                by (rule top1_continuous_map_on_comp[OF h\<sigma>_cont_Y hf])
              \<comment> \<open>f\<circ>\<sigma> maps into U (V0 \<subseteq> f\<inverse>(U) and \<sigma> maps into V0).\<close>
              moreover have "\<forall>s\<in>I_set. (f \<circ> \<sigma>) s \<in> U"
              proof (intro ballI)
                fix s assume "s \<in> I_set"
                hence "\<sigma> s \<in> V0" using h\<sigma>_in_V0 by (by100 blast)
                hence "f (\<sigma> s) \<in> U" using hV0_sub by (by100 blast)
                thus "(f \<circ> \<sigma>) s \<in> U" by (by100 simp)
              qed
              \<comment> \<open>Restrict codomain to U with subspace topology.\<close>
              moreover have hU_sub_B: "U \<subseteq> B"
                using hU_open unfolding openin_on_def by (by100 blast)
              ultimately show ?thesis
              proof -
                assume hf\<sigma>B: "top1_continuous_map_on I_set I_top B TB (f \<circ> \<sigma>)"
                    and hrange: "\<forall>s\<in>I_set. (f \<circ> \<sigma>) s \<in> U"
                show ?thesis
                  by (rule continuous_map_restrict_codomain[OF hf\<sigma>B hrange hU_sub_B])
              qed
            qed
            \<comment> \<open>Composition: inv_into \<circ> f \<circ> \<sigma> maps I_set to W0.\<close>
            have "top1_continuous_map_on I_set I_top W0 (subspace_topology E TE W0) (inv_into W0 p \<circ> (f \<circ> \<sigma>))"
              by (rule top1_continuous_map_on_comp[OF hf\<sigma>_cont hinv_cont])
            moreover have "(inv_into W0 p \<circ> (f \<circ> \<sigma>)) = ?inv_lift"
              by (rule ext) (by100 simp)
            ultimately have hinvl_cont_W0: "top1_continuous_map_on I_set I_top W0 (subspace_topology E TE W0) ?inv_lift"
              by (by100 simp)
            \<comment> \<open>W0 \<subseteq> E, so compose with inclusion to get continuity into E.\<close>
            have hW0_sub: "W0 \<subseteq> E" using hV_open hW0 unfolding openin_on_def by (by100 blast)
            have hW0_incl: "top1_continuous_map_on W0 (subspace_topology E TE W0) E TE (\<lambda>x. x)"
              using top1_continuous_map_on_restrict_domain_simple[OF
                top1_continuous_map_on_id[OF hTE, unfolded id_def] hW0_sub] by (by100 simp)
            have "top1_continuous_map_on I_set I_top E TE ((\<lambda>x. x) \<circ> ?inv_lift)"
              by (rule top1_continuous_map_on_comp[OF hinvl_cont_W0 hW0_incl])
            moreover have "(\<lambda>x::'a. x) \<circ> ?inv_lift = ?inv_lift" by (rule ext) (by100 simp)
            ultimately have hinvl_cont_E: "top1_continuous_map_on I_set I_top E TE ?inv_lift"
              by (by100 simp)
            \<comment> \<open>Endpoints.\<close>
            have hinvl_0: "?inv_lift 0 = ftilde y"
            proof -
              have "\<sigma> 0 = y" using h\<sigma>_Y unfolding top1_is_path_on_def by (by100 blast)
              hence "?inv_lift 0 = inv_into W0 p (f y)" by (by100 simp)
              also have "\<dots> = ftilde y" using hfty_inv by (by100 simp)
              finally show ?thesis .
            qed
            have hinvl_1: "?inv_lift 1 = inv_into W0 p (f y')"
            proof -
              have "\<sigma> 1 = y'" using h\<sigma>_Y unfolding top1_is_path_on_def by (by100 blast)
              thus ?thesis by (by100 simp)
            qed
            show ?thesis unfolding top1_is_path_on_def
              using hinvl_cont_E hinvl_0 hinvl_1 by (by100 blast)
          qed
          have hinvl_lift: "\<forall>s\<in>I_set. p (?inv_lift s) = f (\<sigma> s)"
          proof (intro ballI)
            fix s assume hs: "s \<in> I_set"
            have "\<sigma> s \<in> V0" using h\<sigma>_in_V0 hs by (by100 blast)
            hence "f (\<sigma> s) \<in> U" using hV0_sub by (by100 blast)
            hence "f (\<sigma> s) \<in> p ` W0" using hp_bij unfolding bij_betw_def by (by100 blast)
            show "p (?inv_lift s) = f (\<sigma> s)" by (rule f_inv_into_f[OF \<open>f (\<sigma> s) \<in> p ` W0\<close>])
          qed
          \<comment> \<open>The concatenation ft0 \<cdot> inv_lift is a path from e0 to inv_into W0 p (f y').\<close>
          define cl where "cl = top1_path_product ft0 ?inv_lift"
          have hcl_path: "top1_is_path_on E TE e0 (inv_into W0 p (f y')) cl"
          proof -
            have "ft0 1 = ftilde y" by (rule hft0_end)
            hence hft0': "top1_is_path_on E TE e0 (ftilde y) ft0"
              using hft0 by (by100 simp)
            show ?thesis unfolding cl_def by (rule top1_path_product_is_path[OF hTE hft0' hinvl_path])
          qed
          have hcl_lift: "\<forall>s\<in>I_set. p (cl s) = f ((top1_path_product \<alpha>0 \<sigma>) s)"
          proof (intro ballI)
            fix s assume hs: "s \<in> I_set"
            hence hs01: "0 \<le> s" "s \<le> 1" unfolding top1_unit_interval_def by (by100 simp)+
            show "p (cl s) = f ((top1_path_product \<alpha>0 \<sigma>) s)"
            proof (cases "s \<le> 1/2")
              case True
              have "cl s = ft0 (2 * s)" unfolding cl_def top1_path_product_def using True by (by100 simp)
              moreover have "p (ft0 (2 * s)) = f (\<alpha>0 (2 * s))"
              proof -
                have "2 * s \<in> I_set" unfolding top1_unit_interval_def using hs01 True by (by100 simp)
                thus ?thesis using hft0p by (by100 blast)
              qed
              moreover have "(top1_path_product \<alpha>0 \<sigma>) s = \<alpha>0 (2 * s)"
                unfolding top1_path_product_def using True by (by100 simp)
              ultimately show ?thesis by (by5000 simp)
            next
              case False
              hence hgt: "s > 1/2" by (by100 simp)
              have "cl s = ?inv_lift (2 * s - 1)" unfolding cl_def top1_path_product_def using False by (by100 simp)
              moreover have "p (?inv_lift (2 * s - 1)) = f (\<sigma> (2 * s - 1))"
              proof -
                have "2 * s - 1 \<in> I_set" unfolding top1_unit_interval_def using hs01 hgt by (by100 simp)
                thus ?thesis using hinvl_lift by (by100 blast)
              qed
              moreover have "(top1_path_product \<alpha>0 \<sigma>) s = \<sigma> (2 * s - 1)"
                unfolding top1_path_product_def using False by (by100 simp)
              ultimately show ?thesis by (by5000 simp)
            qed
          qed
          \<comment> \<open>By ftilde_eq_lift: ftilde(y') = endpoint of this lift = inv_into W0 p (f y').\<close>
          \<comment> \<open>cl 1 = inv_into W0 p (f y') (endpoint computation).\<close>
          have hcl_end: "cl 1 = inv_into W0 p (f y')"
          proof -
            have "cl 1 = ?inv_lift (2 * (1::real) - 1)" unfolding cl_def top1_path_product_def by (by100 simp)
            moreover have "(2::real) * 1 - 1 = (1::real)" by (by100 simp)
            ultimately have "cl 1 = ?inv_lift 1" by (by100 simp)
            moreover have "?inv_lift 1 = inv_into W0 p (f (\<sigma> 1))" by (by100 simp)
            moreover have "\<sigma> 1 = y'" using h\<sigma>_Y unfolding top1_is_path_on_def by (by100 blast)
            ultimately show ?thesis by (by100 simp)
          qed
          \<comment> \<open>ftilde(y') = cl 1 (by ftilde_eq_lift).\<close>
          have hcl_lift2: "\<forall>s\<in>I_set. p (cl s) = f (top1_path_product \<alpha>0 \<sigma> s)"
            using hcl_lift by (by100 simp)
          have hcl_path2: "top1_is_path_on E TE e0 (cl 1) cl"
          proof -
            have "cl 1 = inv_into W0 p (f y')" using hcl_end .
            thus ?thesis using hcl_path by (by100 simp)
          qed
          have "ftilde y' = cl 1"
            by (rule ftilde_eq_lift[OF hy'Y h\<alpha>0\<sigma> hcl_path2 hcl_lift2])
          hence "ftilde y' = inv_into W0 p (f y')" using hcl_end by (by100 simp)
          thus "ftilde y' \<in> W0" using hinv_y'_W0 by (by100 simp)
        qed
        \<comment> \<open>hftilde_V0 proved above.\<close>
        \<comment> \<open>V' = V0 \<inter> ftilde\<inverse>(W0 \<inter> W). Since ftilde(V0) \<subseteq> W0, this simplifies.\<close>
        \<comment> \<open>Actually, we need V' \<subseteq> {y \<in> Y. ftilde y \<in> W}. Use W0 \<inter> W.\<close>
        \<comment> \<open>W0 \<inter> W is open in E. p maps W0 homeomorphically to U.
           So p(W0 \<inter> W) is open in U, hence open in B.
           V' = V0 \<inter> f\<inverse>(p(W0 \<inter> W)) is open in Y.\<close>
        \<comment> \<open>ftilde on V0 equals (p|_{W0})\<inverse> \<circ> f. For ftilde(y') \<in> W, need f(y') \<in> p(W0 \<inter> W).\<close>
        have hftilde_eq: "\<forall>y'\<in>V0. ftilde y' = inv_into W0 p (f y')"
        proof (intro ballI)
          fix y' assume "y' \<in> V0"
          hence "ftilde y' \<in> W0" using hftilde_V0 by (by100 blast)
          have hy'Y: "y' \<in> Y" using \<open>y' \<in> V0\<close> hV0_sub by (by100 blast)
          have "p (ftilde y') = f y'" using hft_props hy'Y by (by100 blast)
          thus "ftilde y' = inv_into W0 p (f y')"
            using inv_into_f_eq[OF hp_inj \<open>ftilde y' \<in> W0\<close> \<open>p (ftilde y') = f y'\<close>]
            by (by100 simp)
        qed
        \<comment> \<open>p(W0 \<inter> W) is open in B (p homeo on W0, W0 \<inter> W open in W0).\<close>
        have hpWW: "p ` (W0 \<inter> W) \<subseteq> U"
        proof -
          have "W0 \<subseteq> {x\<in>E. p x \<in> U}" using hV_cover hW0 by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        have hpWW_open: "{y\<in>Y. f y \<in> p ` (W0 \<inter> W)} \<in> TY"
        proof -
          \<comment> \<open>p(W0 \<inter> W) is open in B.\<close>
          \<comment> \<open>W0 \<inter> W is open in E. Its intersection with W0 (= W0 \<inter> W) is open in
             the subspace W0. p maps open subsets of W0 to open subsets of U (homeomorphism).
             U open in B, so the image is open in B.\<close>
          have "p ` (W0 \<inter> W) \<in> TB"
          proof -
            \<comment> \<open>W0 \<inter> W is open in the subspace topology of W0.\<close>
            have hWW_sub: "W0 \<inter> W \<in> subspace_topology E TE W0"
              unfolding subspace_topology_def using hW hW0_open by (by100 blast)
            \<comment> \<open>p maps W0 homeomorphically to U. Open subsets map to open subsets.\<close>
            have hp_bij: "bij_betw p W0 U"
              using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
            have hp_cont_W0: "top1_continuous_map_on W0 (subspace_topology E TE W0) U (subspace_topology B TB U) p"
              using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
            \<comment> \<open>The inverse p\<inverse> is continuous on U → W0.\<close>
            have hinv_cont: "top1_continuous_map_on U (subspace_topology B TB U) W0 (subspace_topology E TE W0) (inv_into W0 p)"
              using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
            \<comment> \<open>Preimage of W0\<inter>W under p\<inverse> = p(W0\<inter>W). By continuity of p\<inverse>, this is open in U.\<close>
            have "{u \<in> U. inv_into W0 p u \<in> W0 \<inter> W} \<in> subspace_topology B TB U"
              using hinv_cont hWW_sub unfolding top1_continuous_map_on_def by (by100 blast)
            \<comment> \<open>{u \<in> U | inv(u) \<in> W0\<inter>W} = p(W0\<inter>W) (since p is bijection on W0).\<close>
            have "{u \<in> U. inv_into W0 p u \<in> W0 \<inter> W} = p ` (W0 \<inter> W)"
            proof (rule set_eqI)
              fix u show "u \<in> {u \<in> U. inv_into W0 p u \<in> W0 \<inter> W} \<longleftrightarrow> u \<in> p ` (W0 \<inter> W)"
              proof
                assume hu: "u \<in> {u \<in> U. inv_into W0 p u \<in> W0 \<inter> W}"
                hence "inv_into W0 p u \<in> W0 \<inter> W" and "u \<in> U" by (by100 blast)+
                have "u \<in> p ` W0" using hp_bij \<open>u \<in> U\<close> unfolding bij_betw_def by (by100 blast)
                have "p (inv_into W0 p u) = u" by (rule f_inv_into_f[OF \<open>u \<in> p ` W0\<close>])
                thus "u \<in> p ` (W0 \<inter> W)" using \<open>inv_into W0 p u \<in> W0 \<inter> W\<close> by (by100 force)
              next
                assume "u \<in> p ` (W0 \<inter> W)"
                then obtain e where he: "e \<in> W0 \<inter> W" and hue: "u = p e" by (by100 blast)
                have "e \<in> W0" using he by (by100 blast)
                have "u \<in> U" using hpWW \<open>u \<in> p ` (W0 \<inter> W)\<close> by (by100 blast)
                have "inv_into W0 p u = e"
                  using inv_into_f_eq[OF hp_inj \<open>e \<in> W0\<close>] hue by (by100 simp)
                thus "u \<in> {u \<in> U. inv_into W0 p u \<in> W0 \<inter> W}"
                  using \<open>u \<in> U\<close> he by (by100 simp)
              qed
            qed
            \<comment> \<open>So p(W0\<inter>W) is open in the subspace U of B.\<close>
            hence "p ` (W0 \<inter> W) \<in> subspace_topology B TB U"
              using \<open>{u \<in> U. inv_into W0 p u \<in> W0 \<inter> W} \<in> subspace_topology B TB U\<close>
              by (by100 simp)
            \<comment> \<open>Open in U subspace = V \<inter> U for some V \<in> TB. Since U \<in> TB and V \<in> TB, V\<inter>U \<in> TB.\<close>
            then obtain V where hV_TB: "V \<in> TB" and hpWW_eq: "p ` (W0 \<inter> W) = U \<inter> V"
              unfolding subspace_topology_def by (by100 auto)
            have "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TB \<longrightarrow> \<Inter>F \<in> TB"
              using hTB unfolding is_topology_on_def by (by100 blast)
            hence "U \<inter> V \<in> TB"
            proof -
              have "finite {U, V}" by (by100 simp)
              moreover have "{U, V} \<noteq> {}" by (by100 blast)
              moreover have "{U, V} \<subseteq> TB" using hU_TB hV_TB by (by100 blast)
              ultimately have "\<Inter>{U, V} \<in> TB"
                using \<open>\<forall>F. _\<close> by (by100 blast)
              moreover have "\<Inter>{U, V} = U \<inter> V" by (by100 auto)
              ultimately show ?thesis by (by5000 simp)
            qed
            thus "p ` (W0 \<inter> W) \<in> TB" using hpWW_eq by (by100 simp)
          qed
          thus ?thesis using hf unfolding top1_continuous_map_on_def by (by100 blast)
        qed
        let ?V' = "V0 \<inter> {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}"
        have hV'_TY: "?V' \<in> TY"
        proof -
          have "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TY \<longrightarrow> \<Inter>F \<in> TY"
            using hTY unfolding is_topology_on_def by (by100 blast)
          hence "V0 \<inter> {y\<in>Y. f y \<in> p ` (W0 \<inter> W)} \<in> TY"
          proof -
            have hfin: "finite {V0, {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}}" by (by100 simp)
            have hne: "{V0, {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}} \<noteq> {}" by (by100 blast)
            have hsub: "{V0, {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}} \<subseteq> TY"
              using hV0_TY hpWW_open by (by100 blast)
            have "\<Inter>{V0, {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}} \<in> TY"
              using \<open>\<forall>F. _\<close> hfin hne hsub by (by100 blast)
            moreover have "\<Inter>{V0, {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}} = V0 \<inter> {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}"
              by (by100 auto)
            ultimately show ?thesis by (by100 simp)
          qed
          thus ?thesis by (by100 simp)
        qed
        have hy_V': "y \<in> ?V'"
        proof -
          have "y \<in> V0" by (rule hy_V0)
          moreover have "y \<in> Y" by (rule hyY)
          moreover have "f y \<in> p ` (W0 \<inter> W)"
          proof -
            have "ftilde y \<in> W0 \<inter> W" using hfty_W0 hfty_W by (by100 blast)
            hence "p (ftilde y) \<in> p ` (W0 \<inter> W)" by (by100 blast)
            thus ?thesis using hfy by (by100 simp)
          qed
          ultimately show ?thesis by (by100 blast)
        qed
        have hV'_sub: "?V' \<subseteq> {y \<in> Y. ftilde y \<in> W}"
        proof (rule subsetI)
          fix y' assume hy': "y' \<in> ?V'"
          hence hy'V0: "y' \<in> V0" and hy'Y: "y' \<in> Y" and hfy'_pWW: "f y' \<in> p ` (W0 \<inter> W)"
            by (by100 blast)+
          \<comment> \<open>f(y') \<in> p(W0 \<inter> W) means \<exists>e \<in> W0 \<inter> W. p(e) = f(y').
             ftilde(y') = inv_into W0 p (f y') = e \<in> W0 \<inter> W \<subseteq> W.\<close>
          from hfy'_pWW obtain e where he: "e \<in> W0" "e \<in> W" and hpe: "p e = f y'" by (by100 auto)
          have "ftilde y' \<in> W0" using hftilde_V0 hy'V0 by (by100 blast)
          have "p (ftilde y') = f y'" using hft_props hy'Y by (by100 blast)
          hence "ftilde y' = e"
          proof -
            have "p (ftilde y') = p e" using \<open>p (ftilde y') = f y'\<close> hpe by (by100 simp)
            moreover have "ftilde y' \<in> W0" by (rule \<open>ftilde y' \<in> W0\<close>)
            moreover have "e \<in> W0" using he by (by100 blast)
            ultimately show ?thesis using hp_inj unfolding inj_on_def by (by100 fast)
          qed
          hence "ftilde y' \<in> W" using he by (by100 blast)
          thus "y' \<in> {y \<in> Y. ftilde y \<in> W}" using hy'Y by (by100 blast)
        qed
        show "\<exists>V\<in>TY. y \<in> V \<and> V \<subseteq> {y \<in> Y. ftilde y \<in> W}"
          apply (rule bexI[where x="?V'"])
          using hy_V' hV'_sub hV'_TY by (by100 blast)+
      qed
      \<comment> \<open>Preimage is union of open neighborhoods, hence open.\<close>
      have "{y \<in> Y. ftilde y \<in> W} = \<Union>{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}}"
      proof (rule set_eqI)
        fix y show "y \<in> {y \<in> Y. ftilde y \<in> W} \<longleftrightarrow> y \<in> \<Union>{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}}"
        proof
          assume "y \<in> {y \<in> Y. ftilde y \<in> W}"
          then obtain V where "V \<in> TY" "y \<in> V" "V \<subseteq> {y \<in> Y. ftilde y \<in> W}"
            using \<open>\<forall>y \<in> {y \<in> Y. ftilde y \<in> W}. _\<close> by (by100 blast)
          thus "y \<in> \<Union>{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}}" by (by100 blast)
        next
          assume "y \<in> \<Union>{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}}" thus "y \<in> {y \<in> Y. ftilde y \<in> W}"
            by (by100 blast)
        qed
      qed
      moreover have "\<Union>{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}} \<in> TY"
      proof -
        have "\<forall>U. U \<subseteq> TY \<longrightarrow> \<Union>U \<in> TY"
          using hTY unfolding is_topology_on_def by (by100 blast)
        moreover have "{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}} \<subseteq> TY" by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      ultimately show "{y \<in> Y. ftilde y \<in> W} \<in> TY" by (by100 simp)
    qed
  qed
  show ?thesis using hft_props hft_cont by (by100 blast)
qed

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
      and "e0 \<in> E" and "e0' \<in> E'" and "b0 \<in> B"
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
  \<comment> \<open>p_*(π₁(E)) = p'_*(π₁(E')) because p=p'∘h on E, h_* is bijective (homeomorphism),
     and functoriality gives p_* = p'_* ∘ h_*. So im(p_*) = im(p'_* ∘ h_*) = im(p'_*).\<close>
  \<comment> \<open>By functoriality + p=p'\<circ>h on E + h_* bijective:
     p_* = (p'\<circ>h)_* = p'_* \<circ> h_*, so im(p_*) = p'_*(im(h_*)) = p'_*(π₁(E')).\<close>
  show "top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
  proof -
    have hTE: "is_topology_on E TE"
      using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have hTE': "is_topology_on E' TE'"
      using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
    have hTB: "is_topology_on B TB"
      using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
    have hh_cont: "top1_continuous_map_on E TE E' TE' h"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hh_bij: "bij_betw h E E'"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hh_inv_cont: "top1_continuous_map_on E' TE' E TE (inv_into E h)"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hh_inj: "inj_on h E"
      using hh_bij unfolding bij_betw_def by (by100 blast)
    have hp_cont: "top1_continuous_map_on E TE B TB p"
      by (rule top1_covering_map_on_continuous[OF assms(4)])
    have hp'_cont: "top1_continuous_map_on E' TE' B TB p'"
      by (rule top1_covering_map_on_continuous[OF assms(6)])
    have hp'h_cont: "top1_continuous_map_on E TE B TB (p' \<circ> h)"
      by (rule top1_continuous_map_on_comp[OF hh_cont hp'_cont])
    \<comment> \<open>p and p'∘h agree on E: ∀e∈E. p(e) = (p'∘h)(e).\<close>
    have hp_agree: "\<forall>e\<in>E. p e = (p' \<circ> h) e"
      using hp by (by100 auto)
    have hp'h_e0: "(p' \<circ> h) e0 = b0"
      using he assms(7) by (by100 simp)
    \<comment> \<open>Basepoint membership.\<close>
    note he0_E = assms(12) and he0'_E' = assms(13) and hb0_B = assms(14)
    \<comment> \<open>h_* maps carrier(E) to carrier(E') (group hom property).\<close>
    have hh_hom: "top1_group_hom_on
        (top1_fundamental_group_carrier E TE e0) (top1_fundamental_group_mul E TE e0)
        (top1_fundamental_group_carrier E' TE' e0') (top1_fundamental_group_mul E' TE' e0')
        (top1_fundamental_group_induced_on E TE e0 E' TE' e0' h)"
      by (rule top1_fundamental_group_induced_on_is_hom[OF hTE hTE' he0_E he0'_E' hh_cont he])
    \<comment> \<open>h⁻¹ setup\<close>
    have hinv_e0': "inv_into E h e0' = e0"
      using inv_into_f_f[OF hh_inj he0_E] he by (by100 simp)
    have hhinv_hom: "top1_group_hom_on
        (top1_fundamental_group_carrier E' TE' e0') (top1_fundamental_group_mul E' TE' e0')
        (top1_fundamental_group_carrier E TE e0) (top1_fundamental_group_mul E TE e0)
        (top1_fundamental_group_induced_on E' TE' e0' E TE e0 (inv_into E h))"
      by (rule top1_fundamental_group_induced_on_is_hom[OF hTE' hTE he0'_E' he0_E hh_inv_cont hinv_e0'])
    \<comment> \<open>⊆: for c ∈ carrier(E, e0), induced_p(c) = induced_p'(h_*(c)) ∈ image_hom(E', p').\<close>
    \<comment> \<open>⊇: for c' ∈ carrier(E', e0'), induced_p'(c') = induced_p(h⁻¹_*(c')) ∈ image_hom(E, p).\<close>
    show ?thesis unfolding top1_fundamental_group_image_hom_def
    proof (rule set_eqI, rule iffI)
      fix d
      assume "d \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p `
                 top1_fundamental_group_carrier E TE e0"
      then obtain c where hc: "c \<in> top1_fundamental_group_carrier E TE e0"
          and hd: "d = top1_fundamental_group_induced_on E TE e0 B TB b0 p c"
        by (by100 blast)
      \<comment> \<open>By induced_agree: induced_p(c) = induced_{p'∘h}(c).\<close>
      have hstep1: "top1_fundamental_group_induced_on E TE e0 B TB b0 p c
          = top1_fundamental_group_induced_on E TE e0 B TB b0 (p' \<circ> h) c"
        by (rule fundamental_group_induced_agree[OF hTE hTB he0_E hp_cont hp'h_cont hp_agree assms(5) hp'h_e0 hc])
      \<comment> \<open>By induced_comp: induced_{p'∘h}(c) = induced_p'(induced_h(c)).\<close>
      have hstep2: "top1_fundamental_group_induced_on E TE e0 B TB b0 (p' \<circ> h) c
          = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
              (top1_fundamental_group_induced_on E TE e0 E' TE' e0' h c)"
        by (rule fundamental_group_induced_comp[OF hTE hTE' hTB hh_cont hp'_cont he0_E he assms(7) hc])
      \<comment> \<open>h_*(c) ∈ carrier(E', e0') (since h_* is a group hom).\<close>
      have hh_star: "top1_fundamental_group_induced_on E TE e0 E' TE' e0' h c
          \<in> top1_fundamental_group_carrier E' TE' e0'"
        using hh_hom hc unfolding top1_group_hom_on_def by (by100 blast)
      show "d \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' `
               top1_fundamental_group_carrier E' TE' e0'"
        using hd hstep1 hstep2 hh_star by (by100 blast)
    next
      fix d
      assume "d \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' `
                 top1_fundamental_group_carrier E' TE' e0'"
      then obtain c' where hc': "c' \<in> top1_fundamental_group_carrier E' TE' e0'"
          and hd: "d = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' c'"
        by (by100 blast)
      \<comment> \<open>p' agrees with p∘h⁻¹ on E'.\<close>
      have hp'_agree: "\<forall>e'\<in>E'. p' e' = (p \<circ> inv_into E h) e'"
      proof (intro ballI)
        fix e' assume he': "e' \<in> E'"
        have "e' \<in> h ` E" using he' hh_bij unfolding bij_betw_def by (by100 blast)
        hence hinv_E: "inv_into E h e' \<in> E"
          by (rule inv_into_into)
        have "e' \<in> h ` E" using he' hh_bij unfolding bij_betw_def by (by100 blast)
        hence "h (inv_into E h e') = e'"
          by (rule f_inv_into_f)
        hence "p' e' = p' (h (inv_into E h e'))" by (by100 simp)
        also have "\<dots> = p (inv_into E h e')" using hp hinv_E by (by100 blast)
        finally show "p' e' = (p \<circ> inv_into E h) e'" by (by100 simp)
      qed
      have hphinv_cont: "top1_continuous_map_on E' TE' B TB (p \<circ> inv_into E h)"
        by (rule top1_continuous_map_on_comp[OF hh_inv_cont hp_cont])
      have hphinv_e0': "(p \<circ> inv_into E h) e0' = b0"
        using hinv_e0' assms(5) by (by100 simp)
      have hstep1': "top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' c'
          = top1_fundamental_group_induced_on E' TE' e0' B TB b0 (p \<circ> inv_into E h) c'"
        by (rule fundamental_group_induced_agree[OF hTE' hTB he0'_E' hp'_cont hphinv_cont hp'_agree assms(7) hphinv_e0' hc'])
      have hstep2': "top1_fundamental_group_induced_on E' TE' e0' B TB b0 (p \<circ> inv_into E h) c'
          = top1_fundamental_group_induced_on E TE e0 B TB b0 p
              (top1_fundamental_group_induced_on E' TE' e0' E TE e0 (inv_into E h) c')"
        by (rule fundamental_group_induced_comp[OF hTE' hTE hTB hh_inv_cont hp_cont he0'_E' hinv_e0' assms(5) hc'])
      have hhinv_star: "top1_fundamental_group_induced_on E' TE' e0' E TE e0 (inv_into E h) c'
          \<in> top1_fundamental_group_carrier E TE e0"
        using hhinv_hom hc' unfolding top1_group_hom_on_def by (by100 blast)
      show "d \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p `
               top1_fundamental_group_carrier E TE e0"
        using hd hstep1' hstep2' hhinv_star by (by100 blast)
    qed
  qed
next
  \<comment> \<open>Backward: if subgroup images equal, use path-lifting to construct h.\<close>
  assume hH_eq: "top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
  \<comment> \<open>Construct h: E \<rightarrow> E' via path-lifting. For each e \<in> E, pick path \<alpha> from e0 to e,
     lift p\<circ>\<alpha> to E' starting at e0'. The endpoint is h(e).\<close>
  have hTE: "is_topology_on E TE"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hTE': "is_topology_on E' TE'"
    using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
  have hTB: "is_topology_on B TB"
    using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
  have hp_cont: "top1_continuous_map_on E TE B TB p"
    by (rule top1_covering_map_on_continuous[OF assms(4)])
  have hp'_cont: "top1_continuous_map_on E' TE' B TB p'"
    by (rule top1_covering_map_on_continuous[OF assms(6)])
  \<comment> \<open>For each e \<in> E, paths from e0 exist (path-connected).\<close>
  \<comment> \<open>For each path, p\<circ>\<alpha> can be lifted to E' (Lemma_54_1).\<close>
  \<comment> \<open>The lift endpoint is independent of the chosen path (well-definedness via Theorem_54_3
     + subgroup equality hH_eq).\<close>
  \<comment> \<open>Define h via some path choice.\<close>
  \<comment> \<open>Apply general lifting criterion to construct h and h'.\<close>
  have hpe0: "p e0 = b0" by (rule assms(5))
  have hp'e0': "p' e0' = b0" by (rule assms(7))
  \<comment> \<open>For h: lift p (base map E\<rightarrow>B) to E' via p' (covering E'\<rightarrow>B).\<close>
  have h_exists: "\<exists>h. (\<forall>e\<in>E. h e \<in> E') \<and> (\<forall>e\<in>E. p' (h e) = p e) \<and> h e0 = e0'
      \<and> top1_continuous_map_on E TE E' TE' h"
  proof -
    \<comment> \<open>Subgroup condition: p_*(\<pi>_1(E)) \<subseteq> p'_*(\<pi>_1(E')), with basepoints at p'(e0') = b0.\<close>
    have hsubgrp: "top1_fundamental_group_image_hom E TE e0 B TB (p' e0') p
        \<subseteq> top1_fundamental_group_image_hom E' TE' e0' B TB (p' e0') p'"
      using hH_eq hp'e0' hpe0 by (by100 simp)
    show ?thesis
      using general_lifting_criterion[OF assms(6) hTE hTB hTE' hp_cont assms(8,10,12,13)
            _ hsubgrp] hpe0 hp'e0' by (by100 simp)
  qed
  \<comment> \<open>For h': lift p' (base map E'\<rightarrow>B) to E via p (covering E\<rightarrow>B).\<close>
  have h'_exists: "\<exists>h'. (\<forall>e'\<in>E'. h' e' \<in> E) \<and> (\<forall>e'\<in>E'. p (h' e') = p' e') \<and> h' e0' = e0
      \<and> top1_continuous_map_on E' TE' E TE h'"
  proof -
    have hsubgrp: "top1_fundamental_group_image_hom E' TE' e0' B TB (p e0) p'
        \<subseteq> top1_fundamental_group_image_hom E TE e0 B TB (p e0) p"
      using hH_eq hp'e0' hpe0 by (by100 simp)
    show ?thesis
      using general_lifting_criterion[OF assms(4) hTE' hTB hTE hp'_cont assms(9,11,13,12)
            _ hsubgrp] hpe0 hp'e0' by (by100 simp)
  qed
  obtain h where hh_E': "\<forall>e\<in>E. h e \<in> E'" and hh_lift: "\<forall>e\<in>E. p' (h e) = p e"
      and hh_e0: "h e0 = e0'" and hh_cont: "top1_continuous_map_on E TE E' TE' h"
    using h_exists by (by100 blast)
  obtain h' where hh'_E: "\<forall>e'\<in>E'. h' e' \<in> E" and hh'_lift: "\<forall>e'\<in>E'. p (h' e') = p' e'"
      and hh'_e0: "h' e0' = e0" and hh'_cont: "top1_continuous_map_on E' TE' E TE h'"
    using h'_exists by (by100 blast)
  \<comment> \<open>h' \<circ> h = id on E: both lift p (i.e. p \<circ> (h'\<circ>h) = p \<circ> id = p on E),
     and agree at e0 (h'(h(e0)) = h'(e0') = e0). By covering_lift_unique_connected,
     h'\<circ>h = id on the connected space E.\<close>
  have hh'h_id: "\<forall>e\<in>E. h' (h e) = e"
  proof -
    have hh'h_cont: "top1_continuous_map_on E TE E TE (h' \<circ> h)"
      by (rule top1_continuous_map_on_comp[OF hh_cont hh'_cont])
    have hh'h_lift: "\<forall>e\<in>E. p ((h' \<circ> h) e) = p (id e)"
    proof (intro ballI)
      fix e assume he: "e \<in> E"
      have "h e \<in> E'" using hh_E' he by (by100 blast)
      hence "p (h' (h e)) = p' (h e)" using hh'_lift by (by100 blast)
      also have "\<dots> = p e" using hh_lift he by (by100 blast)
      finally show "p ((h' \<circ> h) e) = p (id e)" by (by100 simp)
    qed
    have hh'h_e0: "(h' \<circ> h) e0 = id e0"
      using hh_e0 hh'_e0 by (by100 simp)
    have hid_cont: "top1_continuous_map_on E TE E TE id"
      using top1_continuous_map_on_id[OF hTE] .
    have hE_conn: "top1_connected_on E TE"
      by (rule path_connected_imp_connected[OF assms(8)])
    from covering_lift_unique_connected[OF assms(4) hTE hTB hTE hE_conn
        hh'h_cont hid_cont hh'h_lift assms(12) hh'h_e0]
    show ?thesis by (by100 simp)
  qed
  \<comment> \<open>h \<circ> h' = id on E': symmetric argument.\<close>
  have hhh'_id: "\<forall>e'\<in>E'. h (h' e') = e'"
  proof -
    have hhh'_cont: "top1_continuous_map_on E' TE' E' TE' (h \<circ> h')"
      by (rule top1_continuous_map_on_comp[OF hh'_cont hh_cont])
    have hhh'_lift: "\<forall>e'\<in>E'. p' ((h \<circ> h') e') = p' (id e')"
    proof (intro ballI)
      fix e' assume he': "e' \<in> E'"
      have "h' e' \<in> E" using hh'_E he' by (by100 blast)
      hence "p' (h (h' e')) = p (h' e')" using hh_lift by (by100 blast)
      also have "\<dots> = p' e'" using hh'_lift he' by (by100 blast)
      finally show "p' ((h \<circ> h') e') = p' (id e')" by (by100 simp)
    qed
    have hhh'_e0: "(h \<circ> h') e0' = id e0'"
      using hh'_e0 hh_e0 by (by100 simp)
    have hid_cont': "top1_continuous_map_on E' TE' E' TE' id"
      using top1_continuous_map_on_id[OF hTE'] .
    have hE'_conn: "top1_connected_on E' TE'"
      by (rule path_connected_imp_connected[OF assms(9)])
    from covering_lift_unique_connected[OF assms(6) hTE' hTB hTE' hE'_conn
        hhh'_cont hid_cont' hhh'_lift assms(13) hhh'_e0]
    show ?thesis by (by100 simp)
  qed
  \<comment> \<open>h is a homeomorphism: continuous bijection with continuous inverse h'.\<close>
  have hh_bij: "bij_betw h E E'"
  proof (unfold bij_betw_def, intro conjI)
    show "inj_on h E"
    proof (rule inj_onI)
      fix x y assume "x \<in> E" "y \<in> E" "h x = h y"
      have "x = h' (h x)" using hh'h_id[rule_format, OF \<open>x \<in> E\<close>] by (by100 simp)
      also have "\<dots> = h' (h y)" using \<open>h x = h y\<close> by (by100 simp)
      also have "\<dots> = y" using hh'h_id[rule_format, OF \<open>y \<in> E\<close>] by (by100 simp)
      finally show "x = y" .
    qed
    show "h ` E = E'"
    proof (rule set_eqI)
      fix e' show "e' \<in> h ` E \<longleftrightarrow> e' \<in> E'"
      proof
        assume "e' \<in> h ` E"
        then obtain e where "e \<in> E" "e' = h e" by (by100 blast)
        thus "e' \<in> E'" using hh_E' by (by100 blast)
      next
        assume "e' \<in> E'"
        hence "h (h' e') = e'" using hhh'_id by (by100 blast)
        moreover have hh'e'_E: "h' e' \<in> E" using hh'_E \<open>e' \<in> E'\<close> by (by100 blast)
        ultimately have "h (h' e') = e'" by (by100 simp)
        hence "e' = h (h' e')" by (by100 simp)
        thus "e' \<in> h ` E" using hh'e'_E by (by100 force)
      qed
    qed
  qed
  have hh_inv_cont: "top1_continuous_map_on E' TE' E TE (inv_into E h)"
  proof -
    have "\<forall>e'\<in>E'. inv_into E h e' = h' e'"
    proof (intro ballI)
      fix e' assume "e' \<in> E'"
      have "h' e' \<in> E" using hh'_E \<open>e' \<in> E'\<close> by (by100 blast)
      moreover have "h (h' e') = e'" using hhh'_id \<open>e' \<in> E'\<close> by (by100 blast)
      ultimately show "inv_into E h e' = h' e'"
        using inv_into_f_eq[of h E "h' e'" e'] hh_bij
        unfolding bij_betw_def by (by100 blast)
    qed
    \<comment> \<open>inv_into agrees with h' on E', and h' is continuous.\<close>
    show ?thesis unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix e' assume he': "e' \<in> E'"
      have "inv_into E h e' = h' e'" using \<open>\<forall>e'\<in>E'. inv_into E h e' = h' e'\<close> he' by (by100 blast)
      moreover have "h' e' \<in> E" using hh'_E he' by (by100 blast)
      ultimately show "inv_into E h e' \<in> E" by (by100 simp)
    next
      fix V assume "V \<in> TE"
      \<comment> \<open>{e'\<in>E'. inv_into E h e' \<in> V} = {e'\<in>E'. h' e' \<in> V}\<close>
      have hset_eq: "{e'\<in>E'. inv_into E h e' \<in> V} = {e'\<in>E'. h' e' \<in> V}"
      proof (rule Collect_cong)
        fix e' show "(e' \<in> E' \<and> inv_into E h e' \<in> V) = (e' \<in> E' \<and> h' e' \<in> V)"
          using \<open>\<forall>e'\<in>E'. inv_into E h e' = h' e'\<close> by (by100 auto)
      qed
      have "{e'\<in>E'. h' e' \<in> V} \<in> TE'"
        using hh'_cont \<open>V \<in> TE\<close> unfolding top1_continuous_map_on_def by (by100 blast)
      thus "{e'\<in>E'. inv_into E h e' \<in> V} \<in> TE'"
        using hset_eq by (by100 simp)
    qed
  qed
  have hhomeo: "top1_homeomorphism_on E TE E' TE' h"
    unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on E TE" by (rule hTE)
    show "is_topology_on E' TE'" by (rule hTE')
    show "bij_betw h E E'" by (rule hh_bij)
    show "top1_continuous_map_on E TE E' TE' h" by (rule hh_cont)
    show "top1_continuous_map_on E' TE' E TE (inv_into E h)" by (rule hh_inv_cont)
  qed
  show "\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e) \<and> h e0 = e0'"
    using hhomeo hh_lift hh_e0 by (by100 blast)
qed

text \<open>Basepoint change for image_hom: if \<alpha> is a path from e0 to e1 in a covering space E,
  then p_*(\<pi>_1(E, e1)) is the conjugate of p_*(\<pi>_1(E, e0)) by [p\<circ>\<alpha>]\<inverse>.\<close>
lemma basepoint_change_image_hom:
  assumes hcov: "top1_covering_map_on E TE B TB p"
      and hTE: "is_topology_on E TE" and hTB: "is_topology_on B TB"
      and he0: "e0 \<in> E" and he1: "e1 \<in> E"
      and h\<alpha>: "top1_is_path_on E TE e0 e1 \<alpha>"
      and hpe0: "p e0 = b0" and hpe1: "p e1 = b0"
      and hEpc: "top1_path_connected_on E TE"
  shows "top1_fundamental_group_image_hom E TE e1 B TB b0 p
      = (\<lambda>H. top1_fundamental_group_mul B TB b0
            (top1_fundamental_group_invg B TB b0 {g. top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>) g})
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    {g. top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>) g}) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
  \<comment> \<open>Proof via loop conjugation in E: for each direction, conjugate by \<alpha> resp. \<alpha>\<inverse>.\<close>
  \<comment> \<open>\<subseteq>: For d \<in> image_hom(E, e1): d = [p\<circ>g] for loop g at e1.
     Form \<alpha>\<cdot>g\<cdot>\<alpha>\<inverse> (loop at e0). [p\<circ>(\<alpha>\<cdot>g\<cdot>\<alpha>\<inverse>)] = [p\<circ>\<alpha>]\<cdot>[p\<circ>g]\<cdot>[rev(p\<circ>\<alpha>)] = c\<cdot>d\<cdot>inv(c).
     So c\<cdot>d\<cdot>inv(c) \<in> image_hom(E, e0). Thus d = inv(c)\<cdot>(c\<cdot>d\<cdot>inv(c))\<cdot>c \<in> conj(image_hom(E, e0)).\<close>
  \<comment> \<open>\<supseteq>: For h \<in> image_hom(E, e0): h = [p\<circ>f] for loop f at e0.
     Form \<alpha>\<inverse>\<cdot>f\<cdot>\<alpha> (loop at e1). [p\<circ>(\<alpha>\<inverse>\<cdot>f\<cdot>\<alpha>)] = inv(c)\<cdot>[p\<circ>f]\<cdot>c = inv(c)\<cdot>h\<cdot>c.
     So inv(c)\<cdot>h\<cdot>c \<in> image_hom(E, e1). This means inv(c)\<cdot>(h\<cdot>c) = inv(c)\<cdot>h\<cdot>c \<in> image_hom(E, e1).\<close>
  \<comment> \<open>Key identities:
     p \<circ> path_product(path_product(rev(\<alpha>), f), \<alpha>)
     = path_product(path_product(p\<circ>rev(\<alpha>), p\<circ>f), p\<circ>\<alpha>)   (comp_path_product twice)
     = path_product(path_product(rev(p\<circ>\<alpha>), p\<circ>f), p\<circ>\<alpha>)   (comp_path_reverse)
     And rev(\<alpha>)\<cdot>f\<cdot>\<alpha> is a loop at e1 (for f loop at e0).
     Similarly \<alpha>\<cdot>g\<cdot>rev(\<alpha>) is a loop at e0 (for g loop at e1).\<close>
proof -
  let ?mulB = "top1_fundamental_group_mul B TB b0"
  let ?invB = "top1_fundamental_group_invg B TB b0"
  let ?c = "{g. top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>) g}"
  have hp_cont: "top1_continuous_map_on E TE B TB p" by (rule top1_covering_map_on_continuous[OF hcov])
  have hb0_B: "b0 \<in> B" using hp_cont he0 hpe0 unfolding top1_continuous_map_on_def by (by100 blast)
  have h\<alpha>_rev: "top1_is_path_on E TE e1 e0 (top1_path_reverse \<alpha>)"
    by (rule top1_path_reverse_is_path[OF h\<alpha>])
  have hp\<alpha>_loop: "top1_is_loop_on B TB b0 (p \<circ> \<alpha>)"
  proof -
    have "top1_continuous_map_on I_set I_top B TB (p \<circ> \<alpha>)"
      by (rule top1_continuous_map_on_comp)
         (use h\<alpha> hp_cont in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
    moreover have "(p \<circ> \<alpha>) 0 = b0" using h\<alpha> hpe0 unfolding top1_is_path_on_def by (by100 simp)
    moreover have "(p \<circ> \<alpha>) 1 = b0" using h\<alpha> hpe1 unfolding top1_is_path_on_def by (by100 simp)
    ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
  qed
  have hp\<alpha>_rev_loop: "top1_is_loop_on B TB b0 (top1_path_reverse (p \<circ> \<alpha>))"
    by (rule top1_path_reverse_is_loop[OF hp\<alpha>_loop])
  show ?thesis
  proof (rule set_eqI)
    fix d
    show "d \<in> top1_fundamental_group_image_hom E TE e1 B TB b0 p \<longleftrightarrow>
        d \<in> (\<lambda>H. ?mulB (?invB ?c) ` ((\<lambda>h. ?mulB h ?c) ` H))
            (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
    proof
      \<comment> \<open>\<Rightarrow>: d = [p\<circ>g] for loop g at e1. Conjugate: \<alpha>\<cdot>g\<cdot>rev(\<alpha>) is loop at e0.\<close>
      assume "d \<in> top1_fundamental_group_image_hom E TE e1 B TB b0 p"
      then obtain g where hg_loop: "top1_is_loop_on E TE e1 g"
          and hd_eq: "d = top1_fundamental_group_induced_on E TE e1 B TB b0 p
              {k. top1_loop_equiv_on E TE e1 g k}"
        unfolding top1_fundamental_group_image_hom_def top1_fundamental_group_carrier_def
        by (by100 blast)
      \<comment> \<open>\<alpha>\<cdot>g\<cdot>rev(\<alpha>) is a loop at e0.\<close>
      have hg_path: "top1_is_path_on E TE e1 e1 g"
        using hg_loop unfolding top1_is_loop_on_def by (by100 blast)
      have h_conj_loop: "top1_is_loop_on E TE e0
          (top1_path_product (top1_path_product \<alpha> g) (top1_path_reverse \<alpha>))"
      proof -
        have "top1_is_path_on E TE e0 e1 (top1_path_product \<alpha> g)"
          by (rule top1_path_product_is_path[OF hTE h\<alpha> hg_path])
        hence "top1_is_path_on E TE e0 e0 (top1_path_product (top1_path_product \<alpha> g) (top1_path_reverse \<alpha>))"
          by (rule top1_path_product_is_path[OF hTE _ h\<alpha>_rev])
        thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
      qed
      \<comment> \<open>[p\<circ>(\<alpha>\<cdot>g\<cdot>rev(\<alpha>))] = c \<cdot> d \<cdot> inv(c) \<in> image_hom(E, e0).\<close>
      \<comment> \<open>p\<circ>(\<alpha>\<cdot>g\<cdot>rev(\<alpha>)) = (p\<circ>\<alpha>)\<cdot>(p\<circ>g)\<cdot>rev(p\<circ>\<alpha>) by comp_path_product/reverse.\<close>
      have hp_conj: "p \<circ> (top1_path_product (top1_path_product \<alpha> g) (top1_path_reverse \<alpha>))
          = top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))"
        by (simp only: comp_path_product comp_path_reverse)
      \<comment> \<open>So [p\<circ>conj] = mul(mul(c, d), inv(c)) and this is in image_hom(E, e0).\<close>
      \<comment> \<open>Then d = inv(c) \<cdot> [p\<circ>conj] \<cdot> c, so d \<in> conj(image_hom(E, e0)).\<close>
      show "d \<in> (\<lambda>H. ?mulB (?invB ?c) ` ((\<lambda>h. ?mulB h ?c) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
      proof -
        \<comment> \<open>d = [p\<circ>g], the class of p\<circ>g at b0.\<close>
        have hg_loop_E: "top1_is_loop_on E TE e1 g" by (rule hg_loop)
        have hpg_loop: "top1_is_loop_on B TB b0 (p \<circ> g)"
        proof -
          have "top1_continuous_map_on I_set I_top B TB (p \<circ> g)"
            by (rule top1_continuous_map_on_comp)
               (use hg_loop hp_cont in \<open>unfold top1_is_loop_on_def top1_is_path_on_def, by100 blast\<close>)+
          moreover have "(p \<circ> g) 0 = b0" using hg_loop hpe1 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          moreover have "(p \<circ> g) 1 = b0" using hg_loop hpe1 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        have hd_class: "d = {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
        proof -
          have "d = top1_fundamental_group_induced_on E TE e1 B TB b0 p
              {k. top1_loop_equiv_on E TE e1 g k}" by (rule hd_eq)
          also have "\<dots> = {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
          proof (rule set_eqI, rule iffI)
            fix k assume "k \<in> top1_fundamental_group_induced_on E TE e1 B TB b0 p
                {k. top1_loop_equiv_on E TE e1 g k}"
            then obtain g' where hg'_eq: "top1_loop_equiv_on E TE e1 g g'"
                and hk': "top1_loop_equiv_on B TB b0 (p \<circ> g') k"
              unfolding top1_fundamental_group_induced_on_def by (by100 blast)
            have hg'_loop: "top1_is_loop_on E TE e1 g'"
              using hg'_eq unfolding top1_loop_equiv_on_def by (by100 blast)
            have "top1_loop_equiv_on B TB b0 (p \<circ> g) (p \<circ> g')"
              using top1_induced_preserves_loop_equiv[OF hTE hp_cont hg_loop hg'_loop hg'_eq] hpe1
              by (by100 simp)
            from top1_loop_equiv_on_trans[OF hTB this hk']
            show "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}" by (by100 blast)
          next
            fix k assume "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
            hence hk: "top1_loop_equiv_on B TB b0 (p \<circ> g) k" by (by100 blast)
            have "g \<in> {k. top1_loop_equiv_on E TE e1 g k}"
              using top1_loop_equiv_on_refl[OF hg_loop] by (by100 blast)
            thus "k \<in> top1_fundamental_group_induced_on E TE e1 B TB b0 p
                {k. top1_loop_equiv_on E TE e1 g k}"
              unfolding top1_fundamental_group_induced_on_def using hk by (by100 blast)
          qed
          finally show ?thesis .
        qed
        \<comment> \<open>The conjugate \<alpha>\<cdot>g\<cdot>rev(\<alpha>) is in image_hom(E, e0) via h_conj_loop.\<close>
        let ?conj_loop = "top1_path_product (top1_path_product \<alpha> g) (top1_path_reverse \<alpha>)"
        have hconj_in: "top1_fundamental_group_induced_on E TE e0 B TB b0 p
            {k. top1_loop_equiv_on E TE e0 ?conj_loop k}
          \<in> top1_fundamental_group_image_hom E TE e0 B TB b0 p"
          unfolding top1_fundamental_group_image_hom_def top1_fundamental_group_carrier_def
          using h_conj_loop top1_loop_equiv_on_refl[OF h_conj_loop] by (by100 blast)
        \<comment> \<open>This class = {k | loop_equiv((p\<circ>\<alpha>)\<cdot>(p\<circ>g)\<cdot>rev(p\<circ>\<alpha>), k)}.\<close>
        have hconj_class: "top1_fundamental_group_induced_on E TE e0 B TB b0 p
            {k. top1_loop_equiv_on E TE e0 ?conj_loop k}
          = {k. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) k}"
        proof (rule set_eqI, rule iffI)
          fix k assume "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 ?conj_loop k}"
          then obtain f' where hf': "top1_loop_equiv_on E TE e0 ?conj_loop f'"
              and hk: "top1_loop_equiv_on B TB b0 (p \<circ> f') k"
            unfolding top1_fundamental_group_induced_on_def by (by100 blast)
          have hf'_loop: "top1_is_loop_on E TE e0 f'"
            using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
          have "top1_loop_equiv_on B TB b0 (p \<circ> ?conj_loop) (p \<circ> f')"
            using top1_induced_preserves_loop_equiv[OF hTE hp_cont h_conj_loop hf'_loop hf'] hpe0
            by (by100 simp)
          hence "top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> f')"
            using hp_conj by (by100 simp)
          from top1_loop_equiv_on_trans[OF hTB this hk]
          show "k \<in> {k. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) k}"
            by (by100 blast)
        next
          fix k assume "k \<in> {k. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) k}"
          hence hk: "top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) k"
            by (by100 blast)
          have "p \<circ> ?conj_loop = top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))"
            by (rule hp_conj)
          hence "top1_loop_equiv_on B TB b0 (p \<circ> ?conj_loop) k" using hk by (by100 simp)
          moreover have "?conj_loop \<in> {k. top1_loop_equiv_on E TE e0 ?conj_loop k}"
            using top1_loop_equiv_on_refl[OF h_conj_loop] by (by100 blast)
          ultimately show "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 ?conj_loop k}"
            unfolding top1_fundamental_group_induced_on_def by (by100 blast)
        qed
        \<comment> \<open>Now compute inv(c) \<cdot> (h_conj \<cdot> c) and show it equals d = [p\<circ>g].\<close>
        let ?h_conj_class = "{k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) k}"
        have hpg_rev_p\<alpha>_loop: "top1_is_loop_on B TB b0
            (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>)))"
          by (rule top1_path_product_is_loop[OF hTB
                top1_path_product_is_loop[OF hTB hp\<alpha>_loop hpg_loop] hp\<alpha>_rev_loop])
        \<comment> \<open>h_conj \<cdot> c = [conj_path] \<cdot> [p\<circ>\<alpha>] = [conj_path \<cdot> (p\<circ>\<alpha>)].\<close>
        have hh_c: "?mulB ?h_conj_class ?c = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)) k}"
          by (rule top1_fundamental_group_mul_class[OF hTB hpg_rev_p\<alpha>_loop hp\<alpha>_loop])
        \<comment> \<open>inv(c) \<cdot> (h_conj \<cdot> c) = [rev(p\<circ>\<alpha>)] \<cdot> [above].\<close>
        have hh_c_loop: "top1_is_loop_on B TB b0
            (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))"
          by (rule top1_path_product_is_loop[OF hTB hpg_rev_p\<alpha>_loop hp\<alpha>_loop])
        have hinv_hc: "?mulB (?invB ?c) (?mulB ?h_conj_class ?c) = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
              (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}"
        proof -
          have "?invB ?c = {k. top1_loop_equiv_on B TB b0 (top1_path_reverse (p \<circ> \<alpha>)) k}"
            by (rule fundamental_group_invg_class[OF hTB hp\<alpha>_loop])
          hence "?mulB (?invB ?c) (?mulB ?h_conj_class ?c)
              = ?mulB {k. top1_loop_equiv_on B TB b0 (top1_path_reverse (p \<circ> \<alpha>)) k}
                  {k. top1_loop_equiv_on B TB b0
                    (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)) k}"
            using hh_c by (by100 simp)
          also have "\<dots> = {k. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}"
            by (rule top1_fundamental_group_mul_class[OF hTB hp\<alpha>_rev_loop hh_c_loop])
          finally show ?thesis .
        qed
        \<comment> \<open>Path algebra: rev(A) \<cdot> ((A\<cdot>B\<cdot>rev(A)) \<cdot> A) ~ B, where A = p\<circ>\<alpha>, B = p\<circ>g.\<close>
        have hp\<alpha>_path: "top1_is_path_on B TB b0 b0 (p \<circ> \<alpha>)"
          using hp\<alpha>_loop unfolding top1_is_loop_on_def by (by100 blast)
        have hpg_path: "top1_is_path_on B TB b0 b0 (p \<circ> g)"
          using hpg_loop unfolding top1_is_loop_on_def by (by100 blast)
        have hp\<alpha>_rev_path: "top1_is_path_on B TB b0 b0 (top1_path_reverse (p \<circ> \<alpha>))"
          using hp\<alpha>_rev_loop unfolding top1_is_loop_on_def by (by100 blast)
        \<comment> \<open>Associativity gives f\<cdot>(g\<cdot>h) ~ (f\<cdot>g)\<cdot>h (right-to-left).\<close>
        have hAB_path: "top1_is_path_on B TB b0 b0 (top1_path_product (p \<circ> \<alpha>) (p \<circ> g))"
          by (rule top1_path_product_is_path[OF hTB hp\<alpha>_path hpg_path])
        \<comment> \<open>Step 1: ((A\<cdot>B)\<cdot>rev(A))\<cdot>A ~ (A\<cdot>B)\<cdot>(rev(A)\<cdot>A) by sym(assoc).\<close>
        note s1_raw = Theorem_51_2_associativity[OF hTB hAB_path hp\<alpha>_rev_path hp\<alpha>_path]
        note s1 = Lemma_51_1_path_homotopic_sym[OF s1_raw]
        \<comment> \<open>s1: ((A\<cdot>B)\<cdot>rev(A))\<cdot>A ~ (A\<cdot>B)\<cdot>(rev(A)\<cdot>A)\<close>
        \<comment> \<open>Step 2: rev(A)\<cdot>A ~ const(b0) by inverse_right.\<close>
        have s2: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> \<alpha>)) (top1_constant_path b0)"
          by (rule Theorem_51_2_invgerse_right[OF hTB hp\<alpha>_path])
        \<comment> \<open>Step 3: (A\<cdot>B)\<cdot>(rev(A)\<cdot>A) ~ (A\<cdot>B)\<cdot>const.\<close>
        have s3: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> \<alpha>)))
            (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_constant_path b0))"
          by (rule path_homotopic_product_right[OF hTB s2 hAB_path])
        have s4: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_constant_path b0))
            (top1_path_product (p \<circ> \<alpha>) (p \<circ> g))"
          by (rule Theorem_51_2_right_identity[OF hTB hAB_path])
        have s14: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))
            (top1_path_product (p \<circ> \<alpha>) (p \<circ> g))"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTB s1
                Lemma_51_1_path_homotopic_trans[OF hTB s3 s4]])
        \<comment> \<open>Step 5: rev(A) \<cdot> ((A\<cdot>B\<cdot>rev(A))\<cdot>A) ~ rev(A) \<cdot> (A\<cdot>B).\<close>
        have s5: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
              (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)))
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)))"
          by (rule path_homotopic_product_right[OF hTB s14 hp\<alpha>_rev_path])
        \<comment> \<open>Step 6: rev(A) \<cdot> (A\<cdot>B) ~ (rev(A)\<cdot>A)\<cdot>B by assoc (direction f\<cdot>(g\<cdot>h) ~ (f\<cdot>g)\<cdot>h).\<close>
        note s6 = Theorem_51_2_associativity[OF hTB hp\<alpha>_rev_path hp\<alpha>_path hpg_path]
        \<comment> \<open>Step 7: (rev(A)\<cdot>A)\<cdot>B ~ const\<cdot>B by inverse.\<close>
        have s7: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> \<alpha>)) (p \<circ> g))
            (top1_path_product (top1_constant_path b0) (p \<circ> g))"
          by (rule path_homotopic_product_left[OF hTB s2 hpg_path])
        \<comment> \<open>Step 8: const\<cdot>B ~ B by left identity.\<close>
        have s8: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_constant_path b0) (p \<circ> g)) (p \<circ> g)"
          by (rule Theorem_51_2_left_identity[OF hTB hpg_path])
        have s_full: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
              (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)))
            (p \<circ> g)"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTB s5
                Lemma_51_1_path_homotopic_trans[OF hTB s6
                  Lemma_51_1_path_homotopic_trans[OF hTB s7 s8]]])
        \<comment> \<open>So the two loop classes are equal.\<close>
        have hbig_loop: "top1_is_loop_on B TB b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
              (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)))"
          by (rule top1_path_product_is_loop[OF hTB hp\<alpha>_rev_loop hh_c_loop])
        have hclass_eq: "{k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
              (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}
          = {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
        proof (rule set_eqI)
          fix k
          have hLR: "top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)))
              (p \<circ> g)"
            using s_full hbig_loop hpg_loop unfolding top1_loop_equiv_on_def by (by100 blast)
          have hRL: "top1_loop_equiv_on B TB b0 (p \<circ> g)
              (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)))"
            by (rule top1_loop_equiv_on_sym[OF hLR])
          show "k \<in> {k. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}
            \<longleftrightarrow> k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
          proof
            assume "k \<in> {k. top1_loop_equiv_on B TB b0
                (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                  (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}"
            from top1_loop_equiv_on_trans[OF hTB hRL this[simplified]]
            show "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}" by (by100 blast)
          next
            assume "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
            from top1_loop_equiv_on_trans[OF hTB hLR this[simplified]]
            show "k \<in> {k. top1_loop_equiv_on B TB b0
                (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                  (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}"
              by (by100 blast)
          qed
        qed
        \<comment> \<open>Conclusion: inv(c) \<cdot> (h_conj \<cdot> c) = d.\<close>
        have "?mulB (?invB ?c) (?mulB ?h_conj_class ?c) = d"
          using hinv_hc hclass_eq hd_class by (by100 simp)
        moreover have "?h_conj_class = top1_fundamental_group_induced_on E TE e0 B TB b0 p
            {k. top1_loop_equiv_on E TE e0 ?conj_loop k}"
          using hconj_class by (by100 simp)
        ultimately have "?mulB (?invB ?c)
            (?mulB (top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 ?conj_loop k}) ?c) = d"
          by (by100 simp)
        thus ?thesis using hconj_in by (by100 blast)
      qed
    next
      \<comment> \<open>\<Leftarrow>: h \<in> image_hom(E, e0). Conjugate: rev(\<alpha>)\<cdot>f\<cdot>\<alpha> is loop at e1.\<close>
      assume "d \<in> (\<lambda>H. ?mulB (?invB ?c) ` ((\<lambda>h. ?mulB h ?c) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
      then obtain h where hh: "h \<in> top1_fundamental_group_image_hom E TE e0 B TB b0 p"
          and hd_conj: "d = ?mulB (?invB ?c) (?mulB h ?c)" by (by100 blast)
      \<comment> \<open>h = [p\<circ>f] for loop f at e0.\<close>
      obtain f where hf_loop: "top1_is_loop_on E TE e0 f"
          and hh_eq: "h = top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 f k}"
        using hh unfolding top1_fundamental_group_image_hom_def top1_fundamental_group_carrier_def
        by (by100 blast)
      \<comment> \<open>rev(\<alpha>)\<cdot>f\<cdot>\<alpha> is a loop at e1.\<close>
      have hf_path: "top1_is_path_on E TE e0 e0 f"
        using hf_loop unfolding top1_is_loop_on_def by (by100 blast)
      have h_conj2: "top1_is_loop_on E TE e1
          (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>)"
      proof -
        have "top1_is_path_on E TE e1 e0 (top1_path_product (top1_path_reverse \<alpha>) f)"
          by (rule top1_path_product_is_path[OF hTE h\<alpha>_rev hf_path])
        hence "top1_is_path_on E TE e1 e1 (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>)"
          by (rule top1_path_product_is_path[OF hTE _ h\<alpha>])
        thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
      qed
      \<comment> \<open>p\<circ>(rev(\<alpha>)\<cdot>f\<cdot>\<alpha>) = rev(p\<circ>\<alpha>)\<cdot>(p\<circ>f)\<cdot>(p\<circ>\<alpha>) = path producing inv(c)\<cdot>h\<cdot>c.\<close>
      have hp_conj2: "p \<circ> (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>)
          = top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)"
        by (simp only: comp_path_product comp_path_reverse)
      \<comment> \<open>[p\<circ>(rev(\<alpha>)\<cdot>f\<cdot>\<alpha>)] = inv(c) \<cdot> h \<cdot> c = d. So d \<in> image_hom(E, e1).\<close>
      \<comment> \<open>[p\<circ>(rev(\<alpha>)\<cdot>f\<cdot>\<alpha>)] \<in> image_hom(E, e1).\<close>
      have hconj2_in: "top1_fundamental_group_induced_on E TE e1 B TB b0 p
          {k. top1_loop_equiv_on E TE e1 (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>) k}
        \<in> top1_fundamental_group_image_hom E TE e1 B TB b0 p"
        unfolding top1_fundamental_group_image_hom_def top1_fundamental_group_carrier_def
        using h_conj2 top1_loop_equiv_on_refl[OF h_conj2] by (by100 blast)
      \<comment> \<open>This class = {k | loop_equiv(B, rev(p\<circ>\<alpha>)\<cdot>(p\<circ>f)\<cdot>(p\<circ>\<alpha>), k)} by hp_conj2.\<close>
      have "top1_fundamental_group_induced_on E TE e1 B TB b0 p
          {k. top1_loop_equiv_on E TE e1 (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>) k}
        = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k}"
      proof (rule set_eqI, rule iffI)
        fix k assume "k \<in> top1_fundamental_group_induced_on E TE e1 B TB b0 p
            {k. top1_loop_equiv_on E TE e1 (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>) k}"
        then obtain f' where hf': "top1_loop_equiv_on E TE e1
            (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>) f'"
            and hk: "top1_loop_equiv_on B TB b0 (p \<circ> f') k"
          unfolding top1_fundamental_group_induced_on_def by (by100 blast)
        have hf'_loop: "top1_is_loop_on E TE e1 f'"
          using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
        \<comment> \<open>p\<circ>conj_loop ~ p\<circ>f' (by induced_preserves_loop_equiv).\<close>
        have "top1_loop_equiv_on B TB b0 (p \<circ> (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>)) (p \<circ> f')"
          using top1_induced_preserves_loop_equiv[OF hTE hp_cont h_conj2 hf'_loop hf'] hpe1
          by (by100 simp)
        \<comment> \<open>p\<circ>conj_loop = rev(p\<circ>\<alpha>)\<cdot>(p\<circ>f)\<cdot>(p\<circ>\<alpha>) (pointwise by hp_conj2).\<close>
        hence "top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) (p \<circ> f')"
          using hp_conj2 by (by100 simp)
        from top1_loop_equiv_on_trans[OF hTB this hk]
        show "k \<in> {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k}"
          by (by100 blast)
      next
        fix k assume "k \<in> {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k}"
        hence hk: "top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k"
          by (by100 blast)
        \<comment> \<open>The conjugated loop itself is in its own class.\<close>
        let ?conj2 = "top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>"
        have "?conj2 \<in> {k. top1_loop_equiv_on E TE e1 ?conj2 k}"
          using top1_loop_equiv_on_refl[OF h_conj2] by (by100 blast)
        \<comment> \<open>p\<circ>conj2 = the target path (pointwise).\<close>
        have "p \<circ> ?conj2 = top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)"
          by (rule hp_conj2)
        hence "top1_loop_equiv_on B TB b0 (p \<circ> ?conj2) k" using hk by simp
        show "k \<in> top1_fundamental_group_induced_on E TE e1 B TB b0 p
            {k. top1_loop_equiv_on E TE e1 ?conj2 k}"
          unfolding top1_fundamental_group_induced_on_def
          using \<open>?conj2 \<in> _\<close> \<open>top1_loop_equiv_on B TB b0 (p \<circ> ?conj2) k\<close> by (by100 blast)
      qed
      \<comment> \<open>This class = inv(c) \<cdot> h \<cdot> c = d.\<close>
      moreover have "\<dots> = ?mulB (?invB ?c) (?mulB h ?c)"
      proof -
        \<comment> \<open>Setup: p\<circ>f is a loop at b0.\<close>
        have hpf_loop: "top1_is_loop_on B TB b0 (p \<circ> f)"
        proof -
          have "top1_continuous_map_on I_set I_top B TB (p \<circ> f)"
            by (rule top1_continuous_map_on_comp)
               (use hf_loop hp_cont in \<open>unfold top1_is_loop_on_def top1_is_path_on_def, by100 blast\<close>)+
          moreover have "(p \<circ> f) 0 = b0" using hf_loop hpe0 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          moreover have "(p \<circ> f) 1 = b0" using hf_loop hpe0 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        \<comment> \<open>h = induced([f]) = {k | loop_equiv(p\<circ>f, k)} (from the definition).\<close>
        have hh_class: "h = {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
        proof -
          have "h = top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 f k}" by (rule hh_eq)
          also have "\<dots> = {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
          proof (rule set_eqI, rule iffI)
            fix k assume "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
                {k. top1_loop_equiv_on E TE e0 f k}"
            then obtain f' where hf'_eq: "top1_loop_equiv_on E TE e0 f f'"
                and hk': "top1_loop_equiv_on B TB b0 (p \<circ> f') k"
              unfolding top1_fundamental_group_induced_on_def by (by100 blast)
            have hf'_loop: "top1_is_loop_on E TE e0 f'"
              using hf'_eq unfolding top1_loop_equiv_on_def by (by100 blast)
            have "top1_loop_equiv_on B TB b0 (p \<circ> f) (p \<circ> f')"
              using top1_induced_preserves_loop_equiv[OF hTE hp_cont hf_loop hf'_loop hf'_eq] hpe0
              by (by100 simp)
            from top1_loop_equiv_on_trans[OF hTB this hk']
            show "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}" by (by100 blast)
          next
            fix k assume "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
            hence hk: "top1_loop_equiv_on B TB b0 (p \<circ> f) k" by (by100 blast)
            have "f \<in> {k. top1_loop_equiv_on E TE e0 f k}"
              using top1_loop_equiv_on_refl[OF hf_loop] by (by100 blast)
            thus "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
                {k. top1_loop_equiv_on E TE e0 f k}"
              unfolding top1_fundamental_group_induced_on_def using hk by (by100 blast)
          qed
          finally show ?thesis .
        qed
        \<comment> \<open>inv(c) = [rev(p\<circ>\<alpha>)].\<close>
        have hinvc: "?invB ?c = {k. top1_loop_equiv_on B TB b0 (top1_path_reverse (p \<circ> \<alpha>)) k}"
          by (rule fundamental_group_invg_class[OF hTB hp\<alpha>_loop])
        \<comment> \<open>h \<cdot> c = [p\<circ>f] \<cdot> [p\<circ>\<alpha>] = [(p\<circ>f)\<cdot>(p\<circ>\<alpha>)].\<close>
        have hh_c: "?mulB h ?c = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (p \<circ> f) (p \<circ> \<alpha>)) k}"
          using hh_class top1_fundamental_group_mul_class[OF hTB hpf_loop hp\<alpha>_loop] by (by100 simp)
        \<comment> \<open>inv(c) \<cdot> (h \<cdot> c) = [rev(p\<circ>\<alpha>)] \<cdot> [(p\<circ>f)\<cdot>(p\<circ>\<alpha>)] = [rev(p\<circ>\<alpha>)\<cdot>(p\<circ>f)\<cdot>(p\<circ>\<alpha>)].\<close>
        have hpf_p\<alpha>_loop: "top1_is_loop_on B TB b0 (top1_path_product (p \<circ> f) (p \<circ> \<alpha>))"
          using top1_path_product_is_loop[OF hTB hpf_loop hp\<alpha>_loop] .
        have "?mulB (?invB ?c) (?mulB h ?c)
            = ?mulB {k. top1_loop_equiv_on B TB b0 (top1_path_reverse (p \<circ> \<alpha>)) k}
                {k. top1_loop_equiv_on B TB b0 (top1_path_product (p \<circ> f) (p \<circ> \<alpha>)) k}"
          using hinvc hh_c by (by100 simp)
        also have "\<dots> = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (top1_path_product (p \<circ> f) (p \<circ> \<alpha>))) k}"
          by (rule top1_fundamental_group_mul_class[OF hTB hp\<alpha>_rev_loop hpf_p\<alpha>_loop])
        \<comment> \<open>By associativity: rev(p\<circ>\<alpha>) \<cdot> ((p\<circ>f) \<cdot> (p\<circ>\<alpha>)) \<simeq> (rev(p\<circ>\<alpha>) \<cdot> (p\<circ>f)) \<cdot> (p\<circ>\<alpha>).\<close>
        also have "\<dots> = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k}"
        proof (rule set_eqI)
          fix k
          have hp\<alpha>_rev_path: "top1_is_path_on B TB b0 b0 (top1_path_reverse (p \<circ> \<alpha>))"
            using hp\<alpha>_rev_loop unfolding top1_is_loop_on_def by (by100 blast)
          have hpf_path: "top1_is_path_on B TB b0 b0 (p \<circ> f)"
            using hpf_loop unfolding top1_is_loop_on_def by (by100 blast)
          have hp\<alpha>_path: "top1_is_path_on B TB b0 b0 (p \<circ> \<alpha>)"
            using hp\<alpha>_loop unfolding top1_is_loop_on_def by (by100 blast)
          have hassoc: "top1_path_homotopic_on B TB b0 b0
              (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (top1_path_product (p \<circ> f) (p \<circ> \<alpha>)))
              (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>))"
            by (rule Theorem_51_2_associativity[OF hTB hp\<alpha>_rev_path hpf_path hp\<alpha>_path])
          let ?L = "top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (top1_path_product (p \<circ> f) (p \<circ> \<alpha>))"
          let ?R = "top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)"
          have hL_loop: "top1_is_loop_on B TB b0 ?L"
            by (rule top1_path_product_is_loop[OF hTB hp\<alpha>_rev_loop hpf_p\<alpha>_loop])
          have hR_loop: "top1_is_loop_on B TB b0 ?R"
          proof -
            have "top1_is_loop_on B TB b0 (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f))"
              by (rule top1_path_product_is_loop[OF hTB hp\<alpha>_rev_loop hpf_loop])
            thus ?thesis by (rule top1_path_product_is_loop[OF hTB _ hp\<alpha>_loop])
          qed
          have hLR: "top1_loop_equiv_on B TB b0 ?L ?R"
            using hassoc hL_loop hR_loop unfolding top1_loop_equiv_on_def by (by100 blast)
          have hRL: "top1_loop_equiv_on B TB b0 ?R ?L"
            by (rule top1_loop_equiv_on_sym[OF hLR])
          show "k \<in> {k. top1_loop_equiv_on B TB b0 ?L k}
            \<longleftrightarrow> k \<in> {k. top1_loop_equiv_on B TB b0 ?R k}"
          proof
            assume "k \<in> {k. top1_loop_equiv_on B TB b0 ?L k}"
            from top1_loop_equiv_on_trans[OF hTB hRL this[simplified]]
            show "k \<in> {k. top1_loop_equiv_on B TB b0 ?R k}" by (by100 blast)
          next
            assume "k \<in> {k. top1_loop_equiv_on B TB b0 ?R k}"
            from top1_loop_equiv_on_trans[OF hTB hLR this[simplified]]
            show "k \<in> {k. top1_loop_equiv_on B TB b0 ?L k}" by (by100 blast)
          qed
        qed
        finally have calc_eq: "?mulB (?invB ?c) (?mulB h ?c)
            = {k. top1_loop_equiv_on B TB b0
                (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k}" .
        show ?thesis using calc_eq by (by100 simp)
      qed
      moreover note hd_conj
      ultimately show "d \<in> top1_fundamental_group_image_hom E TE e1 B TB b0 p"
        using hconj2_in by (by100 simp)
    qed
  qed
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
      and "e0 \<in> E" and "e0' \<in> E'" and "b0 \<in> B"
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
  \<comment> \<open>Let e1' = h(e0). Choose path γ in E' from e0' to e1'. Set c = [p'∘γ].
     Then p_*(E,e0) = p'_*(E',e1') = c · p'_*(E',e0') · c⁻¹ (basepoint change).\<close>
  \<comment> \<open>Setup: let e1' = h(e0). Since p'∘h = p on E: p'(e1') = p(e0) = b0.\<close>
  let ?e1' = "h e0"
  have hTE: "is_topology_on E TE"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hTE': "is_topology_on E' TE'"
    using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
  have hTB: "is_topology_on B TB"
    using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
  have hh_cont: "top1_continuous_map_on E TE E' TE' h"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hh_bij: "bij_betw h E E'"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  note he0_E = assms(12)
  have he1'_E': "?e1' \<in> E'"
    using he0_E hh_bij unfolding bij_betw_def by (by100 blast)
  have hp'e1': "p' ?e1' = b0"
    using hp he0_E assms(5) by (by100 auto)
  have hb0_B: "b0 \<in> B"
    using hp'e1' top1_covering_map_on_surj[OF assms(6)] he1'_E' by (by100 blast)
  \<comment> \<open>Step 1: Get path γ from e0' to e1' in E' (path-connectedness).\<close>
  have he0'_E': "e0' \<in> E'" by (rule assms(13))
  obtain \<gamma> where h\<gamma>: "top1_is_path_on E' TE' e0' ?e1' \<gamma>"
    using assms(9) he0'_E' he1'_E' unfolding top1_path_connected_on_def by (by100 blast)
  \<comment> \<open>Step 2: c = [p'∘γ] is a loop class in π₁(B, b0).\<close>
  have hp'_cont: "top1_continuous_map_on E' TE' B TB p'"
    by (rule top1_covering_map_on_continuous[OF assms(6)])
  have h\<gamma>_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology E' TE' \<gamma>"
    using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
  have hp'\<gamma>_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology B TB (p' \<circ> \<gamma>)"
    by (rule top1_continuous_map_on_comp[OF h\<gamma>_cont hp'_cont])
  have hp'\<gamma>_0: "(p' \<circ> \<gamma>) 0 = b0"
    using h\<gamma> assms(7) unfolding top1_is_path_on_def by (by100 simp)
  have hp'\<gamma>_1: "(p' \<circ> \<gamma>) 1 = b0"
    using h\<gamma> hp'e1' unfolding top1_is_path_on_def by (by100 simp)
  have hp'\<gamma>_loop: "top1_is_loop_on B TB b0 (p' \<circ> \<gamma>)"
    unfolding top1_is_loop_on_def top1_is_path_on_def
    using hp'\<gamma>_cont hp'\<gamma>_0 hp'\<gamma>_1 by (by100 blast)
  let ?c = "{g. top1_loop_equiv_on B TB b0 (p' \<circ> \<gamma>) g}"
  have hc_carrier: "?c \<in> top1_fundamental_group_carrier B TB b0"
    unfolding top1_fundamental_group_carrier_def using hp'\<gamma>_loop by (by100 blast)
  \<comment> \<open>Step 3: By Theorem 79.2 forward (with e1' as basepoint in E'):
     image_hom(E, e0, p) = image_hom(E', e1', p').\<close>
  have himg_eq: "top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
  proof -
    have "(\<exists>h'. top1_homeomorphism_on E TE E' TE' h' \<and> (\<forall>e\<in>E. p' (h' e) = p e)
               \<and> h' e0 = ?e1') \<longleftrightarrow>
          top1_fundamental_group_image_hom E TE e0 B TB b0 p
            = top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
      by (rule Theorem_79_2[OF assms(1,2,3,4) assms(5) assms(6) hp'e1' assms(8,9,10,11)
            he0_E he1'_E' hb0_B])
    moreover have "\<exists>h'. top1_homeomorphism_on E TE E' TE' h' \<and> (\<forall>e\<in>E. p' (h' e) = p e)
               \<and> h' e0 = ?e1'"
      using hh hp by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>Step 4: By basepoint change (Lemma 79.3):
     image_hom(E', e1', p') = c⁻¹ · image_hom(E', e0', p') · c.
     Rearranging: image_hom(E', e0', p') = c · image_hom(E', e1', p') · c⁻¹
                = c · image_hom(E, e0, p) · c⁻¹.\<close>
  \<comment> \<open>Lemma 79.3: image_hom(E', e0', p') = c · image_hom(E', e1', p') · c⁻¹.
     Proof: for f loop at e0', basepoint_change(γ, f) = γ⁻¹*f*γ is a loop at e1',
     and p'∘(γ⁻¹*f*γ) = (p'∘γ)⁻¹*(p'∘f)*(p'∘γ) (by comp_basepoint_change).
     In π₁(B): [p'∘(γ⁻¹*f*γ)] = c⁻¹·[p'∘f]·c, so [p'∘f] = c·[p'∘(γ⁻¹*f*γ)]·c⁻¹.\<close>
  have hconjugate: "top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
      = (\<lambda>H. (top1_fundamental_group_mul B TB b0 ?c)
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    (top1_fundamental_group_invg B TB b0 ?c)) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
  proof (rule set_eqI, rule iffI)
    fix d
    \<comment> \<open>⊆: d ∈ image_hom(E', e0', p') ⟹ d ∈ c · image_hom(E, e0, p) · c⁻¹.\<close>
    assume "d \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
    then obtain c0 where hc0: "c0 \<in> top1_fundamental_group_carrier E' TE' e0'"
        and hd_eq: "d = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' c0"
      unfolding top1_fundamental_group_image_hom_def by (by100 blast)
    \<comment> \<open>c0 = class(f) for some loop f at e0'.\<close>
    from hc0 obtain f where hf_loop: "top1_is_loop_on E' TE' e0' f"
        and hc0_eq: "c0 = {g. top1_loop_equiv_on E' TE' e0' f g}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>β = basepoint_change(γ, f) = γ⁻¹*f*γ is a loop at e1'.\<close>
    let ?\<beta> = "top1_basepoint_change_on E' TE' e0' ?e1' \<gamma> f"
    have h\<beta>_loop: "top1_is_loop_on E' TE' ?e1' ?\<beta>"
      by (rule top1_basepoint_change_is_loop[OF hTE' h\<gamma> hf_loop])
    \<comment> \<open>p'∘β = basepoint_change(p'∘γ, p'∘f) pointwise (comp_basepoint_change).\<close>
    have hp'\<beta>: "p' \<circ> ?\<beta> = top1_basepoint_change_on B TB b0 b0 (p' \<circ> \<gamma>) (p' \<circ> f)"
      using comp_basepoint_change[of p' E' TE' e0' ?e1' \<gamma> f B TB] assms(7) hp'e1' by (by100 simp)
    \<comment> \<open>[p'∘β] ∈ image_hom(E', e1', p') = image_hom(E, e0, p) (by himg_eq).\<close>
    have h\<beta>_class: "{g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}
        \<in> top1_fundamental_group_carrier E' TE' ?e1'"
      unfolding top1_fundamental_group_carrier_def using h\<beta>_loop by (by100 blast)
    have hp'\<beta>_in: "top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}
        \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
      unfolding top1_fundamental_group_image_hom_def using h\<beta>_class by (by100 blast)
    hence hp'\<beta>_imE: "top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}
        \<in> top1_fundamental_group_image_hom E TE e0 B TB b0 p"
      using himg_eq by (by100 simp)
    \<comment> \<open>Key: d = [p'∘f] = c · [p'∘β] · c⁻¹ in the fundamental group.
       This follows from: p'∘β = (p'∘γ)⁻¹*(p'∘f)*(p'∘γ), so
       [p'∘f] = [p'∘γ] · [p'∘β] · [(p'∘γ)⁻¹] = c · [p'∘β] · invg(c).\<close>
    \<comment> \<open>p'∘f is a loop at b0.\<close>
    have hp'f_loop: "top1_is_loop_on B TB b0 (p' \<circ> f)"
    proof -
      have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology E' TE' f"
        using hf_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      hence "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology B TB (p' \<circ> f)"
        by (rule top1_continuous_map_on_comp[OF _ hp'_cont])
      moreover have "(p' \<circ> f) 0 = b0" using hf_loop assms(7)
        unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
      moreover have "(p' \<circ> f) 1 = b0" using hf_loop assms(7)
        unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
      ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    qed
    \<comment> \<open>Key computation: class(basepoint_change(p'∘γ, p'∘f)) = invg(c) · class(p'∘f) · c.
       Uses: basepoint_change = reverse(α)*g*α, then mul_class twice + invg_class.\<close>
    let ?\<alpha> = "p' \<circ> \<gamma>" and ?g' = "p' \<circ> f"
    have h\<alpha>_loop: "top1_is_loop_on B TB b0 ?\<alpha>" by (rule hp'\<gamma>_loop)
    have hg'_loop: "top1_is_loop_on B TB b0 ?g'" by (rule hp'f_loop)
    have hr\<alpha>_loop: "top1_is_loop_on B TB b0 (top1_path_reverse ?\<alpha>)"
      using h\<alpha>_loop unfolding top1_is_loop_on_def by (rule top1_path_reverse_is_path)
    have hg'\<alpha>_loop: "top1_is_loop_on B TB b0 (top1_path_product ?g' ?\<alpha>)"
      by (rule top1_path_product_is_loop[OF hTB hg'_loop h\<alpha>_loop])
    \<comment> \<open>class(reverse(α) * (g * α)) = mul(invg(class(α)), mul(class(g), class(α)))\<close>
    have hbc_class: "{h. top1_loop_equiv_on B TB b0
          (top1_basepoint_change_on B TB b0 b0 ?\<alpha> ?g') h}
        = top1_fundamental_group_mul B TB b0
            (top1_fundamental_group_invg B TB b0 ?c)
            (top1_fundamental_group_mul B TB b0
              {h. top1_loop_equiv_on B TB b0 ?g' h} ?c)"
    proof -
      have "top1_fundamental_group_mul B TB b0
            {h. top1_loop_equiv_on B TB b0 (top1_path_reverse ?\<alpha>) h}
            {h. top1_loop_equiv_on B TB b0 (top1_path_product ?g' ?\<alpha>) h}
          = {h. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_reverse ?\<alpha>) (top1_path_product ?g' ?\<alpha>)) h}"
        by (rule top1_fundamental_group_mul_class[OF hTB hr\<alpha>_loop hg'\<alpha>_loop])
      moreover have "top1_fundamental_group_mul B TB b0
            {h. top1_loop_equiv_on B TB b0 ?g' h} ?c
          = {h. top1_loop_equiv_on B TB b0 (top1_path_product ?g' ?\<alpha>) h}"
        by (rule top1_fundamental_group_mul_class[OF hTB hg'_loop h\<alpha>_loop])
      moreover have "top1_fundamental_group_invg B TB b0 ?c
          = {h. top1_loop_equiv_on B TB b0 (top1_path_reverse ?\<alpha>) h}"
        by (rule fundamental_group_invg_class[OF hTB h\<alpha>_loop])
      moreover have "{h. top1_loop_equiv_on B TB b0
            (top1_basepoint_change_on B TB b0 b0 ?\<alpha> ?g') h}
          = {h. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_reverse ?\<alpha>) (top1_path_product ?g' ?\<alpha>)) h}"
        unfolding top1_basepoint_change_on_def by (by100 simp)
      ultimately show ?thesis by metis
    qed
    \<comment> \<open>Now: induced_p'(class(β)) = class(p'∘β) = class(basepoint_change(p'∘γ, p'∘f)).\<close>
    have hind_eq: "top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}
      = {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>) h}"
    proof (rule set_eqI, rule iffI)
      fix k assume "k \<in> top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
          {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}"
      then obtain f' where hf'_eq: "top1_loop_equiv_on E' TE' ?e1' ?\<beta> f'"
          and hk: "top1_loop_equiv_on B TB b0 (p' \<circ> f') k"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      have hf'_loop: "top1_is_loop_on E' TE' ?e1' f'"
        using hf'_eq unfolding top1_loop_equiv_on_def by (by100 blast)
      have "top1_loop_equiv_on B TB (p' ?e1') (p' \<circ> ?\<beta>) (p' \<circ> f')"
        by (rule top1_induced_preserves_loop_equiv[OF hTE' hp'_cont h\<beta>_loop hf'_loop hf'_eq])
      hence "top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>) (p' \<circ> f')"
        using hp'e1' by (by100 simp)
      from top1_loop_equiv_on_trans[OF hTB this hk]
      show "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>) h}" by (by100 blast)
    next
      fix k assume "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>) h}"
      moreover have "?\<beta> \<in> {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}"
        using top1_loop_equiv_on_refl[OF h\<beta>_loop] by (by100 blast)
      ultimately show "k \<in> top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
          {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
    qed
    \<comment> \<open>d = induced_p'(class(f)) = class(p'∘f).\<close>
    have hd_class: "d = {h. top1_loop_equiv_on B TB b0 (p' \<circ> f) h}"
    proof -
      have "d = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' c0" by (rule hd_eq)
      also have "\<dots> = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
          {g. top1_loop_equiv_on E' TE' e0' f g}" by (simp only: hc0_eq)
      also have "\<dots> = {h. top1_loop_equiv_on B TB b0 (p' \<circ> f) h}"
      proof (rule set_eqI, rule iffI)
        fix k assume "k \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
            {g. top1_loop_equiv_on E' TE' e0' f g}"
        then obtain f' where hf': "top1_loop_equiv_on E' TE' e0' f f'"
            and hk: "top1_loop_equiv_on B TB b0 (p' \<circ> f') k"
          unfolding top1_fundamental_group_induced_on_def by (by100 blast)
        have hf'_loop2: "top1_is_loop_on E' TE' e0' f'"
          using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
        have "top1_loop_equiv_on B TB (p' e0') (p' \<circ> f) (p' \<circ> f')"
          by (rule top1_induced_preserves_loop_equiv[OF hTE' hp'_cont hf_loop hf'_loop2 hf'])
        hence "top1_loop_equiv_on B TB b0 (p' \<circ> f) (p' \<circ> f')"
          using assms(7) by (by100 simp)
        from top1_loop_equiv_on_trans[OF hTB this hk]
        show "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> f) h}" by (by100 blast)
      next
        fix k assume "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> f) h}"
        moreover have "f \<in> {g. top1_loop_equiv_on E' TE' e0' f g}"
          using top1_loop_equiv_on_refl[OF hf_loop] by (by100 blast)
        ultimately show "k \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
            {g. top1_loop_equiv_on E' TE' e0' f g}"
          unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      qed
      finally show ?thesis .
    qed
    \<comment> \<open>Assembly: d = class(p'∘f). class(p'∘β) = invg(c) · d · c (from hbc_class + hp'β).
       Group algebra: d = c · class(p'∘β) · invg(c).\<close>
    \<comment> \<open>Chain: z = class(p'∘β) = class(bc(α,g')) = invg(c)·d·c. Then d = c·z·invg(c) by group algebra.\<close>
    let ?z = "top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}"
    have hz_eq1: "?z = {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>) h}" by (rule hind_eq)
    have hz_eq2: "?z = {h. top1_loop_equiv_on B TB b0
        (top1_basepoint_change_on B TB b0 b0 ?\<alpha> ?g') h}"
      using hz_eq1 hp'\<beta> by (by100 simp)
    have hz_eq3: "?z = top1_fundamental_group_mul B TB b0
        (top1_fundamental_group_invg B TB b0 ?c)
        (top1_fundamental_group_mul B TB b0 d ?c)"
      using hz_eq2 hbc_class hd_class by (by100 simp)
    \<comment> \<open>Group algebra: z = invg(c) · d · c ⟹ d = c · z · invg(c).\<close>
    have hgrp: "top1_is_group_on
        (top1_fundamental_group_carrier B TB b0)
        (top1_fundamental_group_mul B TB b0)
        (top1_fundamental_group_id B TB b0)
        (top1_fundamental_group_invg B TB b0)"
      by (rule top1_fundamental_group_is_group[OF hTB hb0_B])
    let ?mulB = "top1_fundamental_group_mul B TB b0"
    let ?invB = "top1_fundamental_group_invg B TB b0"
    let ?eB = "top1_fundamental_group_id B TB b0"
    let ?G = "top1_fundamental_group_carrier B TB b0"
    have hc_in: "?c \<in> ?G" by (rule hc_carrier)
    have hd_in: "d \<in> ?G"
    proof -
      have "d \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
        using \<open>d \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'\<close> .
      then obtain c0' where "c0' \<in> top1_fundamental_group_carrier E' TE' e0'"
          "d = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' c0'"
        unfolding top1_fundamental_group_image_hom_def by (by100 blast)
      thus ?thesis
        using top1_fundamental_group_induced_on_is_hom[OF hTE' hTB he0'_E' hb0_B hp'_cont assms(7)]
        unfolding top1_group_hom_on_def by (by100 blast)
    qed
    have hz_in: "?z \<in> ?G"
    proof -
      have hhom': "top1_group_hom_on
          (top1_fundamental_group_carrier E' TE' ?e1')
          (top1_fundamental_group_mul E' TE' ?e1') ?G ?mulB
          (top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p')"
        by (rule top1_fundamental_group_induced_on_is_hom[OF hTE' hTB he1'_E' hb0_B hp'_cont hp'e1'])
      have "?z \<in> ?G"
        using hhom' h\<beta>_class unfolding top1_group_hom_on_def by (by100 blast)
      thus ?thesis .
    qed
    have hinvc_in: "?invB ?c \<in> ?G" by (rule group_inv_closed[OF hgrp hc_in])
    \<comment> \<open>c · z · c⁻¹ = c · (invg(c) · d · c) · c⁻¹ = d\<close>
    \<comment> \<open>Expand z, apply associativity + cancellation step by step.\<close>
    have hdc_in: "?mulB d ?c \<in> ?G" by (rule group_mul_closed[OF hgrp hd_in hc_in])
    have hinvdc_in: "?mulB (?invB ?c) (?mulB d ?c) \<in> ?G"
      by (rule group_mul_closed[OF hgrp hinvc_in hdc_in])
    \<comment> \<open>Step A: c · (c⁻¹ · (d · c)) · c⁻¹ → (c · c⁻¹) · (d · c) · c⁻¹ (assoc on outer)\<close>
    have hstepA: "?mulB ?c (?mulB (?mulB (?invB ?c) (?mulB d ?c)) (?invB ?c))
        = ?mulB (?mulB ?c (?mulB (?invB ?c) (?mulB d ?c))) (?invB ?c)"
      using group_assoc[OF hgrp hc_in hinvdc_in hinvc_in] by (by100 metis)
    \<comment> \<open>Step B: c · (c⁻¹ · (d · c)) → (c · c⁻¹) · (d · c) (inner assoc)\<close>
    have hstepB: "?mulB ?c (?mulB (?invB ?c) (?mulB d ?c))
        = ?mulB (?mulB ?c (?invB ?c)) (?mulB d ?c)"
      using group_assoc[OF hgrp hc_in hinvc_in hdc_in] by (by100 metis)
    \<comment> \<open>Step C: c · c⁻¹ = e\<close>
    have hstepC: "?mulB ?c (?invB ?c) = ?eB" by (rule group_inv_right[OF hgrp hc_in])
    \<comment> \<open>Step D: e · (d · c) = d · c\<close>
    have hstepD: "?mulB ?eB (?mulB d ?c) = ?mulB d ?c"
      by (rule group_id_left[OF hgrp hdc_in])
    \<comment> \<open>Step E: (d · c) · c⁻¹ = d · (c · c⁻¹) (assoc)\<close>
    have hstepE: "?mulB (?mulB d ?c) (?invB ?c) = ?mulB d (?mulB ?c (?invB ?c))"
      by (rule group_assoc[OF hgrp hd_in hc_in hinvc_in])
    \<comment> \<open>Step F: d · e = d\<close>
    have hstepF: "?mulB d ?eB = d" by (rule group_id_right[OF hgrp hd_in])
    \<comment> \<open>Chain: c·z·c⁻¹ = c·(c⁻¹·d·c)·c⁻¹ [hz_eq3] = ... = d\<close>
    have "?mulB ?c (?mulB ?z (?invB ?c))
        = ?mulB ?c (?mulB (?mulB (?invB ?c) (?mulB d ?c)) (?invB ?c))"
      using hz_eq3 by (by100 simp)
    also have "\<dots> = ?mulB (?mulB ?c (?mulB (?invB ?c) (?mulB d ?c))) (?invB ?c)"
      using hstepA by (by100 simp)
    also have "\<dots> = ?mulB (?mulB (?mulB ?c (?invB ?c)) (?mulB d ?c)) (?invB ?c)"
      using hstepB by (by100 simp)
    also have "\<dots> = ?mulB (?mulB ?eB (?mulB d ?c)) (?invB ?c)"
      using hstepC by (by100 simp)
    also have "\<dots> = ?mulB (?mulB d ?c) (?invB ?c)"
      using hstepD by (by100 simp)
    also have "\<dots> = ?mulB d (?mulB ?c (?invB ?c))"
      using hstepE by (by100 simp)
    also have "\<dots> = ?mulB d ?eB"
      using hstepC by (by100 simp)
    also have "\<dots> = d" using hstepF by (by100 simp)
    finally have hd_conj: "d = ?mulB ?c (?mulB ?z (?invB ?c))" by (by100 metis)
    show "d \<in> (\<lambda>H. (top1_fundamental_group_mul B TB b0 ?c)
        ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                  (top1_fundamental_group_invg B TB b0 ?c)) ` H))
        (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
      using hd_conj hp'\<beta>_imE by (by100 blast)
  next
    fix d
    \<comment> \<open>⊇: d ∈ c · image_hom(E, e0, p) · c⁻¹ ⟹ d ∈ image_hom(E', e0', p').\<close>
    assume "d \<in> (\<lambda>H. (top1_fundamental_group_mul B TB b0 ?c)
        ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                  (top1_fundamental_group_invg B TB b0 ?c)) ` H))
        (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
    then obtain x where hx_in: "x \<in> top1_fundamental_group_image_hom E TE e0 B TB b0 p"
        and hd_eq: "d = top1_fundamental_group_mul B TB b0 ?c
            (top1_fundamental_group_mul B TB b0 x (top1_fundamental_group_invg B TB b0 ?c))"
      by (by100 blast)
    \<comment> \<open>x ∈ image_hom(E, e0, p) = image_hom(E', e1', p') (by himg_eq).\<close>
    have hx_imE'1: "x \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
      using hx_in himg_eq by (by100 simp)
    \<comment> \<open>x = induced_p'(class(β)) for some loop β at e1'.
       γ*β*γ⁻¹ is a loop at e0', and d = c · x · c⁻¹ = [p'∘(γ*β*γ⁻¹)] ∈ image_hom(E', e0', p').\<close>
    \<comment> \<open>x ∈ image_hom(E', e1', p') means x = induced_p'(class(β')) for some loop β' at e1'.\<close>
    from hx_imE'1 obtain c1' where hc1': "c1' \<in> top1_fundamental_group_carrier E' TE' ?e1'"
        and hx_eq: "x = top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p' c1'"
      unfolding top1_fundamental_group_image_hom_def by (by100 blast)
    from hc1' obtain \<beta>' where h\<beta>'_loop: "top1_is_loop_on E' TE' ?e1' \<beta>'"
        and hc1'_eq: "c1' = {g. top1_loop_equiv_on E' TE' ?e1' \<beta>' g}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>γ * β' * γ⁻¹ is a loop at e0' (reverse basepoint change).\<close>
    let ?\<gamma>R = "top1_path_reverse \<gamma>"
    let ?\<beta>0 = "top1_basepoint_change_on E' TE' ?e1' e0' ?\<gamma>R \<beta>'"
    have h\<gamma>R: "top1_is_path_on E' TE' ?e1' e0' ?\<gamma>R"
      by (rule top1_path_reverse_is_path[OF h\<gamma>])
    have h\<beta>0_loop: "top1_is_loop_on E' TE' e0' ?\<beta>0"
      by (rule top1_basepoint_change_is_loop[OF hTE' h\<gamma>R h\<beta>'_loop])
    \<comment> \<open>class(p'∘β0) ∈ image_hom(E', e0', p').\<close>
    have h\<beta>0_class: "{g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}
        \<in> top1_fundamental_group_carrier E' TE' e0'"
      unfolding top1_fundamental_group_carrier_def using h\<beta>0_loop by (by100 blast)
    have "top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}
        \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
      unfolding top1_fundamental_group_image_hom_def using h\<beta>0_class by (by100 blast)
    \<comment> \<open>d = class(p'∘β0) by symmetric group algebra argument.
       p'∘β0 = bc(p'∘γ⁻¹, p'∘β') = (p'∘γ) * (p'∘β') * (p'∘γ)⁻¹ = c · x · c⁻¹ = d.\<close>
    moreover have "d = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}"
    proof -
      \<comment> \<open>Step 1: induced_p'(class(β0)) = class(p'∘β0) — same as hind_eq but at e0'.\<close>
      have hind2: "top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
          {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}
        = {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) h}"
      proof (rule set_eqI, rule iffI)
        fix k assume "k \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
            {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}"
        then obtain f' where hf': "top1_loop_equiv_on E' TE' e0' ?\<beta>0 f'"
            and hk: "top1_loop_equiv_on B TB b0 (p' \<circ> f') k"
          unfolding top1_fundamental_group_induced_on_def by (by100 blast)
        have "top1_is_loop_on E' TE' e0' f'"
          using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
        have "top1_loop_equiv_on B TB (p' e0') (p' \<circ> ?\<beta>0) (p' \<circ> f')"
          by (rule top1_induced_preserves_loop_equiv[OF hTE' hp'_cont h\<beta>0_loop \<open>top1_is_loop_on E' TE' e0' f'\<close> hf'])
        hence "top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) (p' \<circ> f')"
          using assms(7) by (by100 simp)
        from top1_loop_equiv_on_trans[OF hTB this hk]
        show "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) h}" by (by100 blast)
      next
        fix k assume "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) h}"
        moreover have "?\<beta>0 \<in> {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}"
          using top1_loop_equiv_on_refl[OF h\<beta>0_loop] by (by100 blast)
        ultimately show "k \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
            {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}"
          unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      qed
      \<comment> \<open>Step 2: p'∘β0 = bc(p'∘γR, p'∘β') = bc(reverse(p'∘γ), p'∘β').\<close>
      have hp'\<beta>0: "p' \<circ> ?\<beta>0 = top1_basepoint_change_on B TB (p' ?e1') (p' e0') (p' \<circ> ?\<gamma>R) (p' \<circ> \<beta>')"
        using comp_basepoint_change[of p' E' TE' ?e1' e0' ?\<gamma>R \<beta>' B TB] by (by100 simp)
      have hp'\<gamma>R: "p' \<circ> ?\<gamma>R = top1_path_reverse (p' \<circ> \<gamma>)"
        by (rule comp_path_reverse)
      \<comment> \<open>bc(reverse(α), f) = reverse(reverse(α)) * f * reverse(α) = α * f * reverse(α).\<close>
      have hbc_expand: "top1_basepoint_change_on B TB b0 b0 (top1_path_reverse (p' \<circ> \<gamma>)) (p' \<circ> \<beta>')
          = top1_path_product (p' \<circ> \<gamma>) (top1_path_product (p' \<circ> \<beta>') (top1_path_reverse (p' \<circ> \<gamma>)))"
      proof -
        have "top1_basepoint_change_on B TB b0 b0 (top1_path_reverse (p' \<circ> \<gamma>)) (p' \<circ> \<beta>')
            = top1_path_product (top1_path_reverse (top1_path_reverse (p' \<circ> \<gamma>)))
                (top1_path_product (p' \<circ> \<beta>') (top1_path_reverse (p' \<circ> \<gamma>)))"
          unfolding top1_basepoint_change_on_def by (by100 simp)
        also have "top1_path_reverse (top1_path_reverse (p' \<circ> \<gamma>)) = p' \<circ> \<gamma>"
          by (rule path_reverse_involution)
        finally show ?thesis .
      qed
      \<comment> \<open>Step 3: class(α * f * reverse(α)) = mul(class(α), mul(class(f), invg(class(α)))).\<close>
      let ?\<alpha>B = "p' \<circ> \<gamma>" and ?g'B = "p' \<circ> \<beta>'"
      have h\<alpha>B_loop: "top1_is_loop_on B TB b0 ?\<alpha>B" by (rule hp'\<gamma>_loop)
      have hg'B_loop: "top1_is_loop_on B TB b0 ?g'B"
      proof -
        have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology E' TE' \<beta>'"
          using h\<beta>'_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        hence "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology B TB (p' \<circ> \<beta>')"
          by (rule top1_continuous_map_on_comp[OF _ hp'_cont])
        moreover have "(p' \<circ> \<beta>') 0 = b0" using h\<beta>'_loop hp'e1'
          unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
        moreover have "(p' \<circ> \<beta>') 1 = b0" using h\<beta>'_loop hp'e1'
          unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
        ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      qed
      have hr\<alpha>B_loop: "top1_is_loop_on B TB b0 (top1_path_reverse ?\<alpha>B)"
        using h\<alpha>B_loop unfolding top1_is_loop_on_def by (rule top1_path_reverse_is_path)
      have hg'\<alpha>R_loop: "top1_is_loop_on B TB b0 (top1_path_product ?g'B (top1_path_reverse ?\<alpha>B))"
        by (rule top1_path_product_is_loop[OF hTB hg'B_loop hr\<alpha>B_loop])
      have hclass_eq: "{h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) h}
          = top1_fundamental_group_mul B TB b0 ?c
              (top1_fundamental_group_mul B TB b0
                {h. top1_loop_equiv_on B TB b0 ?g'B h}
                (top1_fundamental_group_invg B TB b0 ?c))"
      proof -
        have "top1_fundamental_group_mul B TB b0
              {h. top1_loop_equiv_on B TB b0 ?\<alpha>B h}
              {h. top1_loop_equiv_on B TB b0 (top1_path_product ?g'B (top1_path_reverse ?\<alpha>B)) h}
            = {h. top1_loop_equiv_on B TB b0 (top1_path_product ?\<alpha>B (top1_path_product ?g'B (top1_path_reverse ?\<alpha>B))) h}"
          by (rule top1_fundamental_group_mul_class[OF hTB h\<alpha>B_loop hg'\<alpha>R_loop])
        moreover have "top1_fundamental_group_mul B TB b0
              {h. top1_loop_equiv_on B TB b0 ?g'B h}
              (top1_fundamental_group_invg B TB b0 ?c)
            = top1_fundamental_group_mul B TB b0
              {h. top1_loop_equiv_on B TB b0 ?g'B h}
              {h. top1_loop_equiv_on B TB b0 (top1_path_reverse ?\<alpha>B) h}"
          using fundamental_group_invg_class[OF hTB h\<alpha>B_loop] by (by100 simp)
        hence "top1_fundamental_group_mul B TB b0
              {h. top1_loop_equiv_on B TB b0 ?g'B h}
              (top1_fundamental_group_invg B TB b0 ?c)
            = {h. top1_loop_equiv_on B TB b0 (top1_path_product ?g'B (top1_path_reverse ?\<alpha>B)) h}"
          using top1_fundamental_group_mul_class[OF hTB hg'B_loop hr\<alpha>B_loop] by (by100 simp)
        moreover have "{h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) h}
            = {h. top1_loop_equiv_on B TB b0 (top1_path_product ?\<alpha>B (top1_path_product ?g'B (top1_path_reverse ?\<alpha>B))) h}"
          using hp'\<beta>0 hp'\<gamma>R hbc_expand hp'e1' assms(7) by (by100 simp)
        ultimately show ?thesis by (by100 metis)
      qed
      \<comment> \<open>Step 4: x = class(p'∘β'), so class(p'∘β0) = mul(c, mul(x, invg(c))).\<close>
      have hx_class: "x = {h. top1_loop_equiv_on B TB b0 ?g'B h}"
      proof -
        have "x = top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p' c1'" by (rule hx_eq)
        also have "\<dots> = top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
            {g. top1_loop_equiv_on E' TE' ?e1' \<beta>' g}" by (simp only: hc1'_eq)
        also have "\<dots> = {h. top1_loop_equiv_on B TB b0 (p' \<circ> \<beta>') h}"
        proof (rule set_eqI, rule iffI)
          fix k assume "k \<in> top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
              {g. top1_loop_equiv_on E' TE' ?e1' \<beta>' g}"
          then obtain f'' where hf'': "top1_loop_equiv_on E' TE' ?e1' \<beta>' f''"
              and hk: "top1_loop_equiv_on B TB b0 (p' \<circ> f'') k"
            unfolding top1_fundamental_group_induced_on_def by (by100 blast)
          have "top1_is_loop_on E' TE' ?e1' f''"
            using hf'' unfolding top1_loop_equiv_on_def by (by100 blast)
          have "top1_loop_equiv_on B TB (p' ?e1') (p' \<circ> \<beta>') (p' \<circ> f'')"
            by (rule top1_induced_preserves_loop_equiv[OF hTE' hp'_cont h\<beta>'_loop \<open>top1_is_loop_on E' TE' ?e1' f''\<close> hf''])
          hence "top1_loop_equiv_on B TB b0 (p' \<circ> \<beta>') (p' \<circ> f'')"
            using hp'e1' by (by100 simp)
          from top1_loop_equiv_on_trans[OF hTB this hk]
          show "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> \<beta>') h}" by (by100 blast)
        next
          fix k assume "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> \<beta>') h}"
          moreover have "\<beta>' \<in> {g. top1_loop_equiv_on E' TE' ?e1' \<beta>' g}"
            using top1_loop_equiv_on_refl[OF h\<beta>'_loop] by (by100 blast)
          ultimately show "k \<in> top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
              {g. top1_loop_equiv_on E' TE' ?e1' \<beta>' g}"
            unfolding top1_fundamental_group_induced_on_def by (by100 blast)
        qed
        finally show ?thesis .
      qed
      \<comment> \<open>Step 5: Assembly.\<close>
      have "top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
          {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}
        = top1_fundamental_group_mul B TB b0 ?c
            (top1_fundamental_group_mul B TB b0 x (top1_fundamental_group_invg B TB b0 ?c))"
        using hind2 hclass_eq hx_class by (by100 simp)
      thus ?thesis using hd_eq by (by100 simp)
    qed
    ultimately show "d \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
      by (by100 simp)
  qed
  show "\<exists>c \<in> top1_fundamental_group_carrier B TB b0.
      top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
      = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    (top1_fundamental_group_invg B TB b0 c)) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
    using hc_carrier hconjugate by (by100 blast)
next
  \<comment> \<open>Backward: conjugacy means subgroups differ by a basepoint change in E'.
     Theorem 79.2 applies after adjusting basepoints.\<close>
  assume "\<exists>c \<in> top1_fundamental_group_carrier B TB b0.
      top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
      = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    (top1_fundamental_group_invg B TB b0 c)) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
  \<comment> \<open>Conjugate subgroups \<Rightarrow> \<exists>e1' with p'(e1')=b0 s.t. subgroups equal after basepoint change.
     Then Theorem 79.2 gives the pointed equivalence, and we forget the basepoint.\<close>
  then obtain c where hc: "c \<in> top1_fundamental_group_carrier B TB b0"
      and hconj: "top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
        = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
            ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                      (top1_fundamental_group_invg B TB b0 c)) ` H))
            (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
    by blast
  \<comment> \<open>c = [\<gamma>] for some loop \<gamma> at b0. Lift \<gamma>\<inverse> to E' from e0'. The endpoint is e1'.
     Then p'_*(\<pi>_1(E', e1')) = c\<inverse> \<cdot> p'_*(\<pi>_1(E', e0')) \<cdot> c = p_*(\<pi>_1(E, e0)).\<close>
  \<comment> \<open>From the basepoint change: after conjugation by c\<inverse>,
     p'_*(E', e1') = p_*(E, e0). Apply Theorem 79.2 with basepoint e1'.\<close>
  have "\<exists>e1'. e1' \<in> E' \<and> p' e1' = b0 \<and>
      top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' e1' B TB b0 p'"
  proof -
    have hTE': "is_topology_on E' TE'"
      using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
    have hTB: "is_topology_on B TB"
      using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
    have hp'_cont: "top1_continuous_map_on E' TE' B TB p'"
      by (rule top1_covering_map_on_continuous[OF assms(6)])
    \<comment> \<open>c has a representative loop \<gamma> at b0.\<close>
    obtain \<gamma> where h\<gamma>_loop: "top1_is_loop_on B TB b0 \<gamma>"
        and hc_eq: "c = {g. top1_loop_equiv_on B TB b0 \<gamma> g}"
      using hc unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>Lift \<gamma> to E' from e0'. Endpoint = e1'.\<close>
    have h\<gamma>_path: "top1_is_path_on B TB b0 b0 \<gamma>" using h\<gamma>_loop unfolding top1_is_loop_on_def by (by100 blast)
    obtain \<delta> where h\<delta>: "top1_is_path_on E' TE' e0' (\<delta> 1) \<delta>"
        and h\<delta>p: "\<forall>s\<in>I_set. p' (\<delta> s) = \<gamma> s"
    proof -
      have "\<exists>ft. top1_is_path_on E' TE' e0' (ft 1) ft \<and> (\<forall>s\<in>I_set. p' (ft s) = \<gamma> s)"
      proof (rule Lemma_54_1_path_lifting)
        show "top1_covering_map_on E' TE' B TB p'" by (rule assms(6))
        show "e0' \<in> E'" by (rule assms(13))
        show "p' e0' = b0" by (rule assms(7))
        show "top1_is_path_on B TB b0 b0 \<gamma>" by (rule h\<gamma>_path)
        show "is_topology_on B TB" by (rule hTB)
        show "is_topology_on E' TE'" by (rule hTE')
      qed
      then obtain ft' where hft': "top1_is_path_on E' TE' e0' (ft' 1) ft'"
          and hft'p: "\<forall>s\<in>I_set. p' (ft' s) = \<gamma> s" by (by100 blast)
      show ?thesis using that[OF hft' hft'p] .
    qed
    let ?e1' = "\<delta> 1"
    have he1': "?e1' \<in> E'"
    proof -
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      thus ?thesis using h\<delta> unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
    qed
    have hp'e1': "p' ?e1' = b0"
    proof -
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      hence "p' (\<delta> 1) = \<gamma> 1" using h\<delta>p by (by100 blast)
      moreover have "\<gamma> 1 = b0" using h\<gamma>_path unfolding top1_is_path_on_def by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Basepoint change: p'_*(\<pi>_1(E', e1')) = [p'\<circ>\<delta>]\<inverse> \<cdot> p'_*(\<pi>_1(E', e0')) \<cdot> [p'\<circ>\<delta>].
       Since p'\<circ>\<delta> = \<gamma> and [\<gamma>] = c: p'_*(E', e1') = c\<inverse> \<cdot> p'_*(E', e0') \<cdot> c.
       Using hconj: p'_*(E', e0') = c \<cdot> p_*(E) \<cdot> c\<inverse>.
       So: p'_*(E', e1') = c\<inverse> \<cdot> (c \<cdot> p_*(E) \<cdot> c\<inverse>) \<cdot> c = p_*(E).\<close>
    \<comment> \<open>Apply basepoint change: image_hom(E', e1') = c'\<inverse> \<cdot> image_hom(E', e0') \<cdot> c'
       where c' = [p'\<circ>\<delta>] = [\<gamma>] = c.\<close>
    \<comment> \<open>Basepoint change + conjugacy cancellation:
       image_hom(E', e1') = inv(c) \<cdot> image_hom(E', e0') \<cdot> c (basepoint change by \<delta>)
       image_hom(E', e0') = c \<cdot> image_hom(E, e0) \<cdot> inv(c) (hconj)
       Combined: image_hom(E', e1') = inv(c) \<cdot> c \<cdot> image_hom(E, e0) \<cdot> inv(c) \<cdot> c = image_hom(E, e0)
       Proof uses: basepoint_change_image_hom + group algebra cancellation.\<close>
    \<comment> \<open>Step: [p'\<circ>\<delta>] = c. Since p'\<circ>\<delta> = \<gamma> on I_set, their loop classes agree.\<close>
    have hp'\<delta>_eq_\<gamma>: "\<And>s. s \<in> I_set \<Longrightarrow> (p' \<circ> \<delta>) s = \<gamma> s" using h\<delta>p by (by100 simp)
    have hp'\<delta>_loop: "top1_is_loop_on B TB b0 (p' \<circ> \<delta>)"
    proof -
      have "top1_continuous_map_on I_set I_top B TB (p' \<circ> \<delta>)"
        by (rule top1_continuous_map_on_comp)
           (use h\<delta> hp'_cont in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
      moreover have "(p' \<circ> \<delta>) 0 = b0"
        using hp'\<delta>_eq_\<gamma> h\<gamma>_path unfolding top1_is_path_on_def top1_unit_interval_def by (by100 auto)
      moreover have "(p' \<circ> \<delta>) 1 = b0"
        using hp'\<delta>_eq_\<gamma> h\<gamma>_path unfolding top1_is_path_on_def top1_unit_interval_def by (by100 auto)
      ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    qed
    have hclass_p'\<delta>_eq_c: "{g. top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) g}
        = {g. top1_loop_equiv_on B TB b0 \<gamma> g}"
    proof (rule set_eqI)
      fix k
      \<comment> \<open>p'\<circ>\<delta> and \<gamma> agree on I_set, so they are path-homotopic via the identity homotopy.\<close>
      have hp'\<delta>_\<gamma>_equiv: "top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) \<gamma>"
        unfolding top1_loop_equiv_on_def
      proof (intro conjI)
        show "top1_is_loop_on B TB b0 (p' \<circ> \<delta>)" by (rule hp'\<delta>_loop)
        show "top1_is_loop_on B TB b0 \<gamma>" by (rule h\<gamma>_loop)
        \<comment> \<open>Path homotopy via constant homotopy F(s,t) = (p'\<circ>\<delta>)(s).\<close>
        show "top1_path_homotopic_on B TB b0 b0 (p' \<circ> \<delta>) \<gamma>"
          unfolding top1_path_homotopic_on_def
        proof (intro conjI)
          show "top1_is_path_on B TB b0 b0 (p' \<circ> \<delta>)"
            using hp'\<delta>_loop unfolding top1_is_loop_on_def by (by100 blast)
          show "top1_is_path_on B TB b0 b0 \<gamma>" by (rule h\<gamma>_path)
          show "\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology B TB F
              \<and> (\<forall>s\<in>I_set. F (s, 0) = (p' \<circ> \<delta>) s) \<and> (\<forall>s\<in>I_set. F (s, 1) = \<gamma> s)
              \<and> (\<forall>t\<in>I_set. F (0, t) = b0) \<and> (\<forall>t\<in>I_set. F (1, t) = b0)"
          proof (rule exI[of _ "\<lambda>p. (p' \<circ> \<delta>) (fst p)"], intro conjI)
            have h_p'\<delta>_cont: "top1_continuous_map_on I_set I_top B TB (p' \<circ> \<delta>)"
              using hp'\<delta>_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
            show "top1_continuous_map_on (I_set \<times> I_set) II_topology B TB (\<lambda>p. (p' \<circ> \<delta>) (fst p))"
              by (rule path_homotopy_const_continuous[OF h_p'\<delta>_cont])
            show "\<forall>s\<in>I_set. (p' \<circ> \<delta>) (fst (s, (0::real))) = (p' \<circ> \<delta>) s" by (by100 simp)
            show "\<forall>s\<in>I_set. (p' \<circ> \<delta>) (fst (s, (1::real))) = \<gamma> s"
              using hp'\<delta>_eq_\<gamma> by (by100 simp)
            show "\<forall>t\<in>I_set. (p' \<circ> \<delta>) (fst ((0::real), t)) = b0"
            proof
              fix t assume "t \<in> I_set"
              have "(p' \<circ> \<delta>) 0 = b0"
                using h\<delta> assms(7) unfolding top1_is_path_on_def by (by100 simp)
              thus "(p' \<circ> \<delta>) (fst ((0::real), t)) = b0" by (by100 simp)
            qed
            show "\<forall>t\<in>I_set. (p' \<circ> \<delta>) (fst ((1::real), t)) = b0"
            proof
              fix t assume "t \<in> I_set"
              show "(p' \<circ> \<delta>) (fst ((1::real), t)) = b0"
                using hp'e1' by (by100 simp)
            qed
          qed
        qed
      qed
      have h\<gamma>_p'\<delta>_equiv: "top1_loop_equiv_on B TB b0 \<gamma> (p' \<circ> \<delta>)"
        by (rule top1_loop_equiv_on_sym[OF hp'\<delta>_\<gamma>_equiv])
      show "k \<in> {g. top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) g}
          \<longleftrightarrow> k \<in> {g. top1_loop_equiv_on B TB b0 \<gamma> g}"
      proof
        assume "k \<in> {g. top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) g}"
        from top1_loop_equiv_on_trans[OF hTB h\<gamma>_p'\<delta>_equiv this[simplified]]
        show "k \<in> {g. top1_loop_equiv_on B TB b0 \<gamma> g}" by (by100 blast)
      next
        assume "k \<in> {g. top1_loop_equiv_on B TB b0 \<gamma> g}"
        from top1_loop_equiv_on_trans[OF hTB hp'\<delta>_\<gamma>_equiv this[simplified]]
        show "k \<in> {g. top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) g}" by (by100 blast)
      qed
    qed
    \<comment> \<open>Apply basepoint_change_image_hom: image_hom(E', e1') = inv([p'\<circ>\<delta>]) \<cdot> image_hom(E', e0') \<cdot> [p'\<circ>\<delta>].\<close>
    let ?c' = "{g. top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) g}"
    have hbpc: "top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'
        = (\<lambda>H. top1_fundamental_group_mul B TB b0
              (top1_fundamental_group_invg B TB b0 ?c')
            ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h ?c') ` H))
            (top1_fundamental_group_image_hom E' TE' e0' B TB b0 p')"
      by (rule basepoint_change_image_hom[OF assms(6) hTE' hTB assms(13) he1' h\<delta> assms(7) hp'e1' assms(9)])
    \<comment> \<open>Replace ?c' with c using hclass_p'\<delta>_eq_c and hc_eq.\<close>
    have hc'_eq_c: "?c' = c" using hclass_p'\<delta>_eq_c hc_eq by (by100 simp)
    \<comment> \<open>So image_hom(E', e1') = inv(c) \<cdot> image_hom(E', e0') \<cdot> c.\<close>
    have hbpc2: "top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'
        = (\<lambda>H. top1_fundamental_group_mul B TB b0
              (top1_fundamental_group_invg B TB b0 c)
            ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h c) ` H))
            (top1_fundamental_group_image_hom E' TE' e0' B TB b0 p')"
      using hbpc hc'_eq_c by (by100 simp)
    \<comment> \<open>Substitute hconj: image_hom(E', e0') = c \<cdot> image_hom(E, e0) \<cdot> inv(c).\<close>
    \<comment> \<open>After substitution: image_hom(E', e1') = inv(c) \<cdot> (c \<cdot> image_hom(E, e0) \<cdot> inv(c)) \<cdot> c.\<close>
    \<comment> \<open>This double conjugation cancels: = image_hom(E, e0).\<close>
    have himg_match: "top1_fundamental_group_image_hom E TE e0 B TB b0 p
        = top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
    proof -
      let ?mulB = "top1_fundamental_group_mul B TB b0"
      let ?invB = "top1_fundamental_group_invg B TB b0"
      let ?eB = "top1_fundamental_group_id B TB b0"
      let ?G = "top1_fundamental_group_carrier B TB b0"
      let ?img = "top1_fundamental_group_image_hom E TE e0 B TB b0 p"
      \<comment> \<open>Group axioms from the fundamental group of (B, b0).\<close>
      have hb0B: "b0 \<in> B" using assms(14) .
      have hgrp: "top1_is_group_on ?G ?mulB ?eB ?invB"
        by (rule top1_fundamental_group_is_group[OF hTB hb0B])
      have hc_G: "c \<in> ?G" by (rule hc)
      note hgrp_raw = hgrp[unfolded top1_is_group_on_def]
      note hmul_cl_raw = hgrp_raw[THEN conjunct2, THEN conjunct1]
      note hinv_cl_raw = hgrp_raw[THEN conjunct2, THEN conjunct2, THEN conjunct1]
      note hassoc_raw = hgrp_raw[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
      note hid_raw = hgrp_raw[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
      note hinv_raw = hgrp_raw[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]
      have hmul_cl: "\<And>x y. x \<in> ?G \<Longrightarrow> y \<in> ?G \<Longrightarrow> ?mulB x y \<in> ?G"
        using hmul_cl_raw by (by100 blast)
      have hinv_cl: "\<And>x. x \<in> ?G \<Longrightarrow> ?invB x \<in> ?G"
        using hinv_cl_raw by (by100 blast)
      have hinvc_G: "?invB c \<in> ?G" by (rule hinv_cl[OF hc_G])
      have hassoc: "\<And>x y z. x \<in> ?G \<Longrightarrow> y \<in> ?G \<Longrightarrow> z \<in> ?G \<Longrightarrow>
          ?mulB (?mulB x y) z = ?mulB x (?mulB y z)"
        using hassoc_raw by (by100 blast)
      have hlinv: "\<And>x. x \<in> ?G \<Longrightarrow> ?mulB (?invB x) x = ?eB"
        using hinv_raw by (by100 blast)
      have hrid: "\<And>x. x \<in> ?G \<Longrightarrow> ?mulB x ?eB = x"
        using hid_raw by (by100 blast)
      have hlid: "\<And>x. x \<in> ?G \<Longrightarrow> ?mulB ?eB x = x"
        using hid_raw by (by100 blast)
      \<comment> \<open>Image hom elements are in the carrier.\<close>
      have himg_sub: "?img \<subseteq> ?G"
      proof
        fix d assume "d \<in> ?img"
        then obtain f where hf_loop: "top1_is_loop_on E TE e0 f"
            and hd_eq: "d = top1_fundamental_group_induced_on E TE e0 B TB b0 p
                {k. top1_loop_equiv_on E TE e0 f k}"
          unfolding top1_fundamental_group_image_hom_def top1_fundamental_group_carrier_def
          by (by100 blast)
        have hTE_loc: "is_topology_on E TE"
          using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
        have hp_cont: "top1_continuous_map_on E TE B TB p"
          by (rule top1_covering_map_on_continuous[OF assms(4)])
        have hpf_loop: "top1_is_loop_on B TB b0 (p \<circ> f)"
        proof -
          have "top1_continuous_map_on I_set I_top B TB (p \<circ> f)"
            by (rule top1_continuous_map_on_comp)
               (use hf_loop hp_cont in \<open>unfold top1_is_loop_on_def top1_is_path_on_def, by100 blast\<close>)+
          moreover have "(p \<circ> f) 0 = b0" using hf_loop assms(5) unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          moreover have "(p \<circ> f) 1 = b0" using hf_loop assms(5) unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        \<comment> \<open>induced([f]) = [p\<circ>f] (same as hh_class proof pattern).\<close>
        have hd_class: "d = {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
        proof -
          have "d = top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 f k}" by (rule hd_eq)
          also have "\<dots> = {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
          proof (rule set_eqI, rule iffI)
            fix k assume "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
                {k. top1_loop_equiv_on E TE e0 f k}"
            then obtain f' where hf': "top1_loop_equiv_on E TE e0 f f'"
                and hk: "top1_loop_equiv_on B TB b0 (p \<circ> f') k"
              unfolding top1_fundamental_group_induced_on_def by (by100 blast)
            have hf'_loop: "top1_is_loop_on E TE e0 f'"
              using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
            have "top1_loop_equiv_on B TB b0 (p \<circ> f) (p \<circ> f')"
              using top1_induced_preserves_loop_equiv[OF hTE_loc hp_cont hf_loop hf'_loop hf'] assms(5)
              by (by100 simp)
            from top1_loop_equiv_on_trans[OF hTB this hk]
            show "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}" by (by100 blast)
          next
            fix k assume "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
            moreover have "f \<in> {k. top1_loop_equiv_on E TE e0 f k}"
              using top1_loop_equiv_on_refl[OF hf_loop] by (by100 blast)
            ultimately show "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
                {k. top1_loop_equiv_on E TE e0 f k}"
              unfolding top1_fundamental_group_induced_on_def by (by100 blast)
          qed
          finally show ?thesis .
        qed
        \<comment> \<open>[p\<circ>f] \<in> carrier(B, b0) since p\<circ>f is a loop at b0.\<close>
        show "d \<in> ?G"
          unfolding hd_class top1_fundamental_group_carrier_def
          using hpf_loop top1_loop_equiv_on_refl[OF hpf_loop] by (by100 blast)
      qed
      \<comment> \<open>Key: inv(c) \<cdot> ((c \<cdot> (h \<cdot> inv(c))) \<cdot> c) = h for h \<in> G.\<close>
      have hcancel: "\<And>h. h \<in> ?G \<Longrightarrow>
          ?mulB (?invB c) (?mulB (?mulB c (?mulB h (?invB c))) c) = h"
      proof -
        fix h assume hh: "h \<in> ?G"
        have hhinvc: "?mulB h (?invB c) \<in> ?G" by (rule hmul_cl[OF hh hinvc_G])
        have hchinvc: "?mulB c (?mulB h (?invB c)) \<in> ?G" by (rule hmul_cl[OF hc_G hhinvc])
        \<comment> \<open>Step 1: (c \<cdot> (h \<cdot> inv(c))) \<cdot> c = c \<cdot> ((h \<cdot> inv(c)) \<cdot> c) by assoc.\<close>
        have s1: "?mulB (?mulB c (?mulB h (?invB c))) c
            = ?mulB c (?mulB (?mulB h (?invB c)) c)"
          by (rule hassoc[OF hc_G hhinvc hc_G])
        \<comment> \<open>Step 2: (h \<cdot> inv(c)) \<cdot> c = h \<cdot> (inv(c) \<cdot> c) by assoc.\<close>
        have s2: "?mulB (?mulB h (?invB c)) c = ?mulB h (?mulB (?invB c) c)"
          by (rule hassoc[OF hh hinvc_G hc_G])
        \<comment> \<open>Step 3: inv(c) \<cdot> c = e by left inverse.\<close>
        have s3: "?mulB (?invB c) c = ?eB" by (rule hlinv[OF hc_G])
        \<comment> \<open>Step 4: h \<cdot> e = h.\<close>
        have s4: "?mulB h ?eB = h" by (rule hrid[OF hh])
        \<comment> \<open>Combine inner: (c \<cdot> (h \<cdot> inv(c))) \<cdot> c = c \<cdot> h.\<close>
        have inner: "?mulB (?mulB c (?mulB h (?invB c))) c = ?mulB c h"
          using s1 s2 s3 s4 by (by100 simp)
        \<comment> \<open>Step 5: inv(c) \<cdot> (c \<cdot> h) = (inv(c) \<cdot> c) \<cdot> h = e \<cdot> h = h.\<close>
        have hch: "?mulB c h \<in> ?G" by (rule hmul_cl[OF hc_G hh])
        have s5: "?mulB (?invB c) (?mulB c h) = ?mulB (?mulB (?invB c) c) h"
          by (rule hassoc[OF hinvc_G hc_G hh, symmetric])
        have s6: "?mulB (?mulB (?invB c) c) h = ?mulB ?eB h" using s3 by (by100 simp)
        have s7: "?mulB ?eB h = h" by (rule hlid[OF hh])
        show "?mulB (?invB c) (?mulB (?mulB c (?mulB h (?invB c))) c) = h"
          using inner s5 s6 s7 by (by100 simp)
      qed
      \<comment> \<open>Now show set equality using hbpc2 + hconj + cancellation.\<close>
      show ?thesis
      proof (rule set_eqI)
        fix d
        show "d \<in> ?img \<longleftrightarrow> d \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
        proof
          \<comment> \<open>(\<Rightarrow>) h \<in> img(E,e0). Conjugate by c to get in img(E',e0'), then by inv(c) to get in img(E',e1'). Cancellation gives h back.\<close>
          assume hd: "d \<in> ?img"
          hence hd_G: "d \<in> ?G" using himg_sub by (by100 blast)
          \<comment> \<open>c \<cdot> (d \<cdot> inv(c)) \<in> img(E', e0') via hconj.\<close>
          let ?k = "?mulB c (?mulB d (?invB c))"
          have hk_in: "?k \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
            using hd hconj by (by100 blast)
          \<comment> \<open>inv(c) \<cdot> (k \<cdot> c) \<in> img(E', e1') via hbpc2.\<close>
          let ?d' = "?mulB (?invB c) (?mulB ?k c)"
          have hd'_in: "?d' \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
            using hk_in hbpc2 by (by100 blast)
          \<comment> \<open>?d' = d by cancellation.\<close>
          have "?d' = d" by (rule hcancel[OF hd_G])
          thus "d \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
            using hd'_in by (by100 simp)
        next
          \<comment> \<open>(\<Leftarrow>) Decompose via hbpc2 and hconj, then use cancellation.\<close>
          assume "d \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
          hence "d \<in> ?mulB (?invB c) ` ((\<lambda>h. ?mulB h c) ` (top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'))"
            using hbpc2 by (by100 simp)
          then obtain k where hk: "k \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
              and hd_eq: "d = ?mulB (?invB c) (?mulB k c)" by (by100 blast)
          have "k \<in> ?mulB c ` ((\<lambda>h. ?mulB h (?invB c)) ` ?img)"
            using hk hconj by (by100 simp)
          then obtain h where hh: "h \<in> ?img"
              and hk_eq: "k = ?mulB c (?mulB h (?invB c))" by (by100 blast)
          have hh_G: "h \<in> ?G" using hh himg_sub by (by100 blast)
          have "d = ?mulB (?invB c) (?mulB (?mulB c (?mulB h (?invB c))) c)"
            using hd_eq hk_eq by (by100 simp)
          also have "\<dots> = h" by (rule hcancel[OF hh_G])
          finally show "d \<in> ?img" using hh by (by100 simp)
        qed
      qed
    qed
    show ?thesis using he1' hp'e1' himg_match by (by100 blast)
  qed
  then obtain e1' where he1': "e1' \<in> E'" and hp'e1': "p' e1' = b0"
      and himg_eq: "top1_fundamental_group_image_hom E TE e0 B TB b0 p
          = top1_fundamental_group_image_hom E' TE' e1' B TB b0 p'"
    by (by100 blast)
  \<comment> \<open>Apply Theorem 79.2 backward with basepoint e1': get h with h(e0) = e1'.\<close>
  have "(\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e)
           \<and> h e0 = e1') \<longleftrightarrow>
       top1_fundamental_group_image_hom E TE e0 B TB b0 p
         = top1_fundamental_group_image_hom E' TE' e1' B TB b0 p'"
    by (rule Theorem_79_2[OF assms(1,2,3,4) assms(5) assms(6) hp'e1' assms(8,9,10,11)
          assms(12) he1' assms(14)])
  hence "\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e) \<and> h e0 = e1'"
    using himg_eq by (by100 blast)
  thus "\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e)"
    by (by100 blast)
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
            unfolding top1_loop_equiv_on_def by blast
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
          by (by100 fast)
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
        hcovE assms(10) hcovE' assms(11) assms(6,7,8,9) assms(12,13) hb0_B]] hRHS by (by100 blast)
qed

text \<open>Restriction of a homeomorphism to an open subset (preimage) gives a homeomorphism.\<close>
lemma homeomorphism_restrict_open:
  assumes hf: "top1_homeomorphism_on X TX Y TY f"
      and hV: "openin_on Y TY V"
      and hVY: "V \<subseteq> Y"
      and hTX: "is_topology_on X TX"
      and hTY: "is_topology_on Y TY"
  shows "top1_homeomorphism_on {x \<in> X. f x \<in> V} (subspace_topology X TX {x \<in> X. f x \<in> V})
             V (subspace_topology Y TY V) f"
proof -
  let ?X' = "{x \<in> X. f x \<in> V}"
  let ?TX' = "subspace_topology X TX ?X'"
  let ?TY' = "subspace_topology Y TY V"
  have hXsub: "?X' \<subseteq> X" by (by100 blast)
  have hbij: "bij_betw f X Y" using hf unfolding top1_homeomorphism_on_def by (by100 blast)
  have hf_cont: "top1_continuous_map_on X TX Y TY f"
    using hf unfolding top1_homeomorphism_on_def by (by100 blast)
  have hfinv_cont: "top1_continuous_map_on Y TY X TX (inv_into X f)"
    using hf unfolding top1_homeomorphism_on_def by (by100 blast)
  show ?thesis unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on ?X' ?TX'" by (rule subspace_topology_is_topology_on[OF hTX hXsub])
    show "is_topology_on V ?TY'" by (rule subspace_topology_is_topology_on[OF hTY hVY])
    \<comment> \<open>bij_betw: f maps ?X' bijectively to V.\<close>
    show "bij_betw f ?X' V"
    proof -
      have "inj_on f X" using hbij unfolding bij_betw_def by (by100 blast)
      hence "inj_on f ?X'" by (rule inj_on_subset) (by100 blast)
      moreover have "f ` ?X' = V"
      proof (rule set_eqI)
        fix y show "y \<in> f ` ?X' \<longleftrightarrow> y \<in> V"
        proof
          assume "y \<in> f ` ?X'" thus "y \<in> V" by (by100 blast)
        next
          assume "y \<in> V"
          hence "y \<in> Y" using hVY by (by100 blast)
          hence "\<exists>x\<in>X. f x = y" using hbij unfolding bij_betw_def by (by100 blast)
          then obtain x where hx: "x \<in> X" and hfx: "f x = y" by (by100 blast)
          hence "x \<in> ?X'" using \<open>y \<in> V\<close> by (by100 blast)
          thus "y \<in> f ` ?X'" using hfx by (by100 blast)
        qed
      qed
      ultimately show ?thesis unfolding bij_betw_def by (by100 blast)
    qed
    \<comment> \<open>Continuity: f restricted to ?X' \<rightarrow> V.\<close>
    show "top1_continuous_map_on ?X' ?TX' V ?TY' f"
    proof -
      have hf_restr: "top1_continuous_map_on ?X' ?TX' Y TY f"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF hf_cont hXsub])
      have himg: "f ` ?X' \<subseteq> V" by (by100 blast)
      show ?thesis by (rule top1_continuous_map_on_codomain_shrink[OF hf_restr himg hVY])
    qed
    \<comment> \<open>Inverse continuity.\<close>
    show "top1_continuous_map_on V ?TY' ?X' ?TX' (inv_into ?X' f)"
    proof -
      \<comment> \<open>inv_into X' f = inv_into X f on V (since X' \<subseteq> X, f injective, image = V).\<close>
      have hinj: "inj_on f X" using hbij unfolding bij_betw_def by (by100 blast)
      have hfinv_agree: "\<forall>y\<in>V. inv_into ?X' f y = inv_into X f y"
      proof
        fix y assume "y \<in> V"
        hence "y \<in> Y" using hVY by (by100 blast)
        hence "y \<in> f ` X" using hbij unfolding bij_betw_def by (by100 blast)
        hence "inv_into X f y \<in> X" by (rule inv_into_into)
        moreover have "f (inv_into X f y) = y"
          using \<open>y \<in> f ` X\<close> by (rule f_inv_into_f)
        hence "f (inv_into X f y) \<in> V" using \<open>y \<in> V\<close> by (by100 simp)
        hence "inv_into X f y \<in> ?X'" using calculation by (by100 blast)
        thus "inv_into ?X' f y = inv_into X f y"
          by (intro inv_into_f_eq[OF inj_on_subset[OF hinj hXsub]])
             (use \<open>f (inv_into X f y) = y\<close> in \<open>by100 blast\<close>)
      qed
      \<comment> \<open>Restrict inv_into X f: Y \<rightarrow> X to V \<rightarrow> X'.\<close>
      have hfinv_restr: "top1_continuous_map_on V ?TY' X TX (inv_into X f)"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF hfinv_cont hVY])
      \<comment> \<open>Codomain shrink from X to X'.\<close>
      have hfinv_img: "(inv_into X f) ` V \<subseteq> ?X'"
      proof
        fix x assume "x \<in> (inv_into X f) ` V"
        then obtain y where hy: "y \<in> V" and hx: "x = inv_into X f y" by (by100 blast)
        have "inv_into X f y \<in> ?X'"
        proof -
          have "y \<in> f ` X" using hy hVY hbij unfolding bij_betw_def by (by100 blast)
          hence hiy_X: "inv_into X f y \<in> X" by (rule inv_into_into)
          have "f (inv_into X f y) = y" using \<open>y \<in> f ` X\<close> by (rule f_inv_into_f)
          hence "f (inv_into X f y) \<in> V" using hy by (by100 simp)
          thus ?thesis using hiy_X by (by100 blast)
        qed
        thus "x \<in> ?X'" using hx by (by100 simp)
      qed
      have hfinv_shrink: "top1_continuous_map_on V ?TY' ?X' ?TX' (inv_into X f)"
        by (rule top1_continuous_map_on_codomain_shrink[OF hfinv_restr hfinv_img hXsub])
      \<comment> \<open>inv_into X' f = inv_into X f on V, so continuity transfers.\<close>
      \<comment> \<open>Transfer: inv_into X' f and inv_into X f agree on V, so same continuity.\<close>
      have "\<forall>y\<in>V. inv_into ?X' f y = inv_into X f y" by (rule hfinv_agree)
      show ?thesis
        by (rule top1_continuous_map_on_agree'[OF hfinv_shrink])
           (use hfinv_agree in \<open>by100 simp\<close>)
    qed
  qed
qed

text \<open>Helper: open subset of an evenly covered set is evenly covered.
  If U is evenly covered by p and V \<subseteq> U is open in B, then V is evenly covered by p.\<close>
lemma evenly_covered_open_subset:
  assumes hcov: "top1_evenly_covered_on E TE B TB p U"
      and hV: "openin_on B TB V" and hVU: "V \<subseteq> U"
      and hTE: "is_topology_on E TE" and hTB: "is_topology_on B TB"
  shows "top1_evenly_covered_on E TE B TB p V"
proof -
  \<comment> \<open>Extract sheets of U.\<close>
  obtain \<V>U where h\<V>_open: "\<forall>W\<in>\<V>U. openin_on E TE W"
      and h\<V>_disj: "\<forall>W\<in>\<V>U. \<forall>W'\<in>\<V>U. W \<noteq> W' \<longrightarrow> W \<inter> W' = {}"
      and h\<V>_union: "{x\<in>E. p x \<in> U} = \<Union>\<V>U"
      and h\<V>_homeo: "\<forall>W\<in>\<V>U. top1_homeomorphism_on W (subspace_topology E TE W) U
                                    (subspace_topology B TB U) p"
    using hcov unfolding top1_evenly_covered_on_def
    by (elim conjE exE) (by100 blast)
  \<comment> \<open>Define restricted sheets: W' = {x \<in> W | p x \<in> V} for each W \<in> \<V>U.\<close>
  let ?\<V>V = "(\<lambda>W. {x \<in> W. p x \<in> V}) ` \<V>U"
  show ?thesis unfolding top1_evenly_covered_on_def
  proof (intro conjI exI[of _ ?\<V>V])
    show "openin_on B TB V" by (rule hV)
  next
    \<comment> \<open>Each restricted sheet is open in E.\<close>
    show "\<forall>W'\<in>?\<V>V. openin_on E TE W'"
    proof
      fix W' assume "W' \<in> ?\<V>V"
      then obtain W where hW: "W \<in> \<V>U" and hW': "W' = {x \<in> W. p x \<in> V}" by (by100 blast)
      \<comment> \<open>p|_W: W \<rightarrow> U is a homeomorphism. V is open in subspace(B,U). Preimage of V is open in W.\<close>
      have hW_open: "openin_on E TE W" using h\<V>_open hW by (by100 blast)
      have hW_homeo: "top1_homeomorphism_on W (subspace_topology E TE W) U (subspace_topology B TB U) p"
        using h\<V>_homeo hW by (by100 blast)
      \<comment> \<open>V is open in subspace_topology B TB U (since V \<in> TB and V \<subseteq> U).\<close>
      have hV_in_TU: "V \<in> subspace_topology B TB U"
        unfolding subspace_topology_def using hV hVU unfolding openin_on_def by (by100 blast)
      \<comment> \<open>p continuous W \<rightarrow> U means preimage of V (open in U) is open in W.\<close>
      have hp_cont_WU: "top1_continuous_map_on W (subspace_topology E TE W) U (subspace_topology B TB U) p"
        using hW_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have "{x \<in> W. p x \<in> V} \<in> subspace_topology E TE W"
        using hp_cont_WU hV_in_TU unfolding top1_continuous_map_on_def by (by100 blast)
      \<comment> \<open>Open in subspace(E, W) and W open in E implies open in E.\<close>
      hence "{x \<in> W. p x \<in> V} \<in> TE"
      proof -
        have "{x \<in> W. p x \<in> V} \<in> subspace_topology E TE W" by (rule \<open>{x \<in> W. p x \<in> V} \<in> subspace_topology E TE W\<close>)
        then obtain T_open where hTo: "T_open \<in> TE" and heq: "{x \<in> W. p x \<in> V} = W \<inter> T_open"
          unfolding subspace_topology_def by (by100 blast)
        have "W \<in> TE" using hW_open unfolding openin_on_def by (by100 blast)
        hence "W \<inter> T_open \<in> TE" by (rule topology_inter2[OF hTE _ hTo])
        thus ?thesis using heq by (by100 simp)
      qed
      moreover have "{x \<in> W. p x \<in> V} \<subseteq> E"
      proof -
        have "W \<subseteq> E" using hW_open unfolding openin_on_def by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      ultimately show "openin_on E TE W'" unfolding hW' openin_on_def by (by100 blast)
    qed
  next
    \<comment> \<open>Restricted sheets are pairwise disjoint.\<close>
    show "\<forall>W'\<in>?\<V>V. \<forall>W''\<in>?\<V>V. W' \<noteq> W'' \<longrightarrow> W' \<inter> W'' = {}"
    proof (intro ballI impI)
      fix W' W'' assume "W' \<in> ?\<V>V" "W'' \<in> ?\<V>V" "W' \<noteq> W''"
      then obtain W1 W2 where hW1: "W1 \<in> \<V>U" and hW1': "W' = {x \<in> W1. p x \<in> V}"
          and hW2: "W2 \<in> \<V>U" and hW2': "W'' = {x \<in> W2. p x \<in> V}" by (by100 blast)
      show "W' \<inter> W'' = {}"
      proof (cases "W1 = W2")
        case True thus ?thesis using \<open>W' \<noteq> W''\<close> hW1' hW2' by (by100 simp)
      next
        case False
        hence "W1 \<inter> W2 = {}" using h\<V>_disj hW1 hW2 by (by100 blast)
        thus ?thesis using hW1' hW2' by (by100 blast)
      qed
    qed
  next
    \<comment> \<open>Union of restricted sheets = p\<inverse>(V) \<inter> E.\<close>
    show "{x\<in>E. p x \<in> V} = \<Union>?\<V>V"
    proof (rule set_eqI)
      fix x show "x \<in> {x\<in>E. p x \<in> V} \<longleftrightarrow> x \<in> \<Union>?\<V>V"
      proof
        assume "x \<in> {x\<in>E. p x \<in> V}"
        hence hxE: "x \<in> E" and hpxV: "p x \<in> V" by (by100 blast)+
        hence "p x \<in> U" using hVU by (by100 blast)
        hence "x \<in> {x\<in>E. p x \<in> U}" using hxE by (by100 blast)
        hence "x \<in> \<Union>\<V>U" using h\<V>_union by (by100 simp)
        then obtain W where hW: "W \<in> \<V>U" and hxW: "x \<in> W" by (by100 blast)
        have "x \<in> {x \<in> W. p x \<in> V}" using hxW hpxV by (by100 blast)
        moreover have "{x \<in> W. p x \<in> V} \<in> ?\<V>V" using hW by (by100 blast)
        ultimately show "x \<in> \<Union>?\<V>V" by (by100 blast)
      next
        assume "x \<in> \<Union>?\<V>V"
        then obtain W where hW: "W \<in> \<V>U" and hx: "x \<in> {x \<in> W. p x \<in> V}" by (by100 blast)
        hence hxW: "x \<in> W" and hpxV: "p x \<in> V" by (by100 blast)+
        have "x \<in> \<Union>\<V>U" using hW hxW by (by100 blast)
        hence "x \<in> {x\<in>E. p x \<in> U}" using h\<V>_union by (by100 simp)
        thus "x \<in> {x\<in>E. p x \<in> V}" using hpxV by (by100 blast)
      qed
    qed
  next
    \<comment> \<open>Each restricted sheet is homeomorphic to V via p.\<close>
    show "\<forall>W'\<in>?\<V>V. top1_homeomorphism_on W' (subspace_topology E TE W') V
                          (subspace_topology B TB V) p"
    proof
      fix W' assume "W' \<in> ?\<V>V"
      then obtain W where hW: "W \<in> \<V>U" and hW': "W' = {x \<in> W. p x \<in> V}" by (by100 blast)
      have hW_homeo: "top1_homeomorphism_on W (subspace_topology E TE W) U (subspace_topology B TB U) p"
        using h\<V>_homeo hW by (by100 blast)
      have hW_open: "openin_on E TE W" using h\<V>_open hW by (by100 blast)
      have hWsub: "W \<subseteq> E" using hW_open unfolding openin_on_def by (by100 blast)
      have hW'sub: "W' \<subseteq> W" unfolding hW' by (by100 blast)
      have hW'E: "W' \<subseteq> E" using hW'sub hWsub by (by100 blast)
      have hUopen: "openin_on B TB U" using hcov unfolding top1_evenly_covered_on_def by (by100 blast)
      have hUsub: "U \<subseteq> B" using hUopen unfolding openin_on_def by (by100 blast)
      have hVsub: "V \<subseteq> B" using hV unfolding openin_on_def by (by100 blast)
      \<comment> \<open>V is open in subspace(B, U).\<close>
      have hV_in_TU: "V \<in> subspace_topology B TB U"
        unfolding subspace_topology_def using hV hVU unfolding openin_on_def by (by100 blast)
      have hV_open_sub: "openin_on U (subspace_topology B TB U) V"
        unfolding openin_on_def using hV_in_TU hVU by (by100 blast)
      have hTW: "is_topology_on W (subspace_topology E TE W)"
        by (rule subspace_topology_is_topology_on[OF hTE hWsub])
      have hTU: "is_topology_on U (subspace_topology B TB U)"
        by (rule subspace_topology_is_topology_on[OF hTB hUsub])
      \<comment> \<open>Apply homeomorphism_restrict_open to p: W \<cong> U with open V \<subseteq> U.\<close>
      note hrestr = homeomorphism_restrict_open[OF hW_homeo hV_open_sub hVU hTW hTU]
      \<comment> \<open>subspace_topology_trans: subspace(W, subspace(E,W), W') = subspace(E, W').\<close>
      have hTW'_eq: "subspace_topology W (subspace_topology E TE W) {x \<in> W. p x \<in> V}
          = subspace_topology E TE {x \<in> W. p x \<in> V}"
        by (rule subspace_topology_trans) (by100 force)
      have hTV'_eq: "subspace_topology U (subspace_topology B TB U) V
          = subspace_topology B TB V"
        by (rule subspace_topology_trans[OF hVU])
      show "top1_homeomorphism_on W' (subspace_topology E TE W') V (subspace_topology B TB V) p"
        using hrestr hTW'_eq hTV'_eq unfolding hW' by (by100 simp)
    qed
  qed
qed

lemma covering_base_locally_path_connected:
  assumes "top1_covering_map_on E TE B TB p"
      and "top1_locally_path_connected_on E TE"
      and "is_topology_on E TE" and "is_topology_on B TB"
  shows "top1_locally_path_connected_on B TB"
  unfolding top1_locally_path_connected_on_def
proof (intro conjI ballI)
  show "is_topology_on B TB" by (rule assms(4))
next
  fix b assume hb: "b \<in> B"
  show "top1_locally_path_connected_at B TB b"
    unfolding top1_locally_path_connected_at_def
  proof (intro allI impI)
    fix U assume hU: "neighborhood_of b B TB U \<and> U \<subseteq> B"
    \<comment> \<open>Get U0 open with b \<in> U0 \<subseteq> U, and Uc evenly covered by p.\<close>
    obtain U0 where hU0: "U0 \<in> TB" "b \<in> U0" "U0 \<subseteq> U"
      using hU unfolding neighborhood_of_def by (by100 blast)
    obtain Uc where hUc_b: "b \<in> Uc" and hUc_cov: "top1_evenly_covered_on E TE B TB p Uc"
      using hb assms(1) unfolding top1_covering_map_on_def by (by100 blast)
    have hUc_open: "Uc \<in> TB"
      using hUc_cov unfolding top1_evenly_covered_on_def openin_on_def by (by100 blast)
    let ?V = "U0 \<inter> Uc"
    have hV_open: "?V \<in> TB" by (rule topology_inter2[OF assms(4) hU0(1) hUc_open])
    have hV_b: "b \<in> ?V" using hU0(2) hUc_b by (by100 blast)
    have "openin_on B TB Uc" using hUc_cov unfolding top1_evenly_covered_on_def by (by100 blast)
    hence "Uc \<subseteq> B" unfolding openin_on_def by (by100 blast)
    have hV_sub_B: "?V \<subseteq> B" using \<open>Uc \<subseteq> B\<close> by (by100 blast)
    have hV_openin: "openin_on B TB ?V"
      using hV_open hV_sub_B unfolding openin_on_def by (by100 blast)
    have hV_cov: "top1_evenly_covered_on E TE B TB p ?V"
      by (rule evenly_covered_open_subset[OF hUc_cov hV_openin _ assms(3) assms(4)]) (by100 blast)
    \<comment> \<open>Get p-slice W and preimage e of b.\<close>
    obtain e where he: "e \<in> E" "p e = b"
      using hb top1_covering_map_on_surj[OF assms(1)] by (by100 blast)
    obtain \<V> where h\<V>_open: "\<forall>W\<in>\<V>. openin_on E TE W"
        and h\<V>_union: "{x\<in>E. p x \<in> ?V} = \<Union>\<V>"
        and h\<V>_homeo: "\<forall>W\<in>\<V>. top1_homeomorphism_on W (subspace_topology E TE W)
            ?V (subspace_topology B TB ?V) p"
      using hV_cov unfolding top1_evenly_covered_on_def
      by (elim conjE exE) (by100 blast)
    have he_pV: "e \<in> {x\<in>E. p x \<in> ?V}" using he hV_b by (by100 blast)
    hence "e \<in> \<Union>\<V>" using h\<V>_union by (by100 simp)
    then obtain W where hW: "W \<in> \<V>" "e \<in> W" by (by100 blast)
    have hW_open: "W \<in> TE" using h\<V>_open hW(1) unfolding openin_on_def by (by100 blast)
    have hW_sub_E: "W \<subseteq> E" using h\<V>_open hW(1) unfolding openin_on_def by (by100 blast)
    \<comment> \<open>W is open and lpc. Path component C of e in W is open and path-connected.\<close>
    have hW_lpc: "top1_locally_path_connected_on W (subspace_topology E TE W)"
      by (rule open_subset_locally_path_connected[OF assms(2) hW_open hW_sub_E])
    have hW_top: "is_topology_on W (subspace_topology E TE W)"
      using hW_lpc unfolding top1_locally_path_connected_on_def by (by100 blast)
    let ?C = "top1_path_component_of_on W (subspace_topology E TE W) e"
    have hPC: "?C \<in> subspace_topology E TE W"
      by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hW_top hW_lpc hW(2)])
    \<comment> \<open>C is open in E.\<close>
    have hC_TE: "?C \<in> TE"
    proof -
      from hPC obtain U' where hU'_TE: "U' \<in> TE" and hC_eq: "?C = W \<inter> U'"
        unfolding subspace_topology_def by (by100 blast)
      have "W \<inter> U' \<in> TE" by (rule topology_inter2[OF assms(3) hW_open hU'_TE])
      thus ?thesis using hC_eq by (by100 simp)
    qed
    \<comment> \<open>Key facts about C and the homeomorphism.\<close>
    have he_C: "e \<in> ?C"
      by (rule top1_path_component_of_on_self_mem[OF hW_top hW(2)])
    have hC_sub_W: "?C \<subseteq> W"
      by (rule top1_path_component_of_on_subset[OF hW_top hW(2)])
    have hp_homeo: "top1_homeomorphism_on W (subspace_topology E TE W)
        ?V (subspace_topology B TB ?V) p"
      using h\<V>_homeo hW(1) by (by100 blast)
    have hp_bij: "bij_betw p W ?V"
      using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    \<comment> \<open>p(C) is open in B: use homeomorphism inverse continuity.\<close>
    have hpC_open_sub: "p ` ?C \<in> subspace_topology B TB ?V"
    proof -
      have hinv_cont: "top1_continuous_map_on ?V (subspace_topology B TB ?V) W
          (subspace_topology E TE W) (inv_into W p)"
        using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have "p ` ?C = {u \<in> ?V. (inv_into W p) u \<in> ?C}"
      proof (rule set_eqI, rule iffI)
        fix u assume "u \<in> p ` ?C"
        then obtain e' where he': "e' \<in> ?C" "u = p e'" by (by100 blast)
        have "e' \<in> W" using he' hC_sub_W by (by100 blast)
        have "u \<in> ?V" using \<open>e' \<in> W\<close> \<open>u = p e'\<close> hp_bij unfolding bij_betw_def by (by100 blast)
        have "u \<in> p ` W" using \<open>e' \<in> W\<close> \<open>u = p e'\<close> by (by100 blast)
        have "inj_on p W" using hp_bij unfolding bij_betw_def by (by100 blast)
        have "inv_into W p (p e') = e'"
          by (rule inv_into_f_f[OF \<open>inj_on p W\<close> \<open>e' \<in> W\<close>])
        hence "inv_into W p u = e'" using \<open>u = p e'\<close> by (by100 simp)
        thus "u \<in> {u \<in> ?V. (inv_into W p) u \<in> ?C}" using \<open>u \<in> ?V\<close> he'(1) by (by100 simp)
      next
        fix u assume hu: "u \<in> {u \<in> ?V. (inv_into W p) u \<in> ?C}"
        hence "u \<in> ?V" "(inv_into W p) u \<in> ?C" by (by100 blast)+
        have "u \<in> p ` W" using \<open>u \<in> ?V\<close> hp_bij unfolding bij_betw_def by (by100 blast)
        have "p (inv_into W p u) = u" by (rule f_inv_into_f[OF \<open>u \<in> p ` W\<close>])
        show "u \<in> p ` ?C"
        proof (rule image_eqI)
          show "u = p (inv_into W p u)" using \<open>p (inv_into W p u) = u\<close> by (by100 simp)
          show "inv_into W p u \<in> ?C" using \<open>(inv_into W p) u \<in> ?C\<close> by (by100 simp)
        qed
      qed
      have hpreimg: "{u \<in> ?V. (inv_into W p) u \<in> ?C} \<in> subspace_topology B TB ?V"
        using hinv_cont hPC unfolding top1_continuous_map_on_def by (by100 blast)
      thus ?thesis using \<open>p ` ?C = {u \<in> ?V. (inv_into W p) u \<in> ?C}\<close> by (by100 simp)
    qed
    have hpC_TB: "p ` ?C \<in> TB"
    proof -
      from hpC_open_sub obtain T' where hT': "T' \<in> TB" and hpC_eq: "p ` ?C = ?V \<inter> T'"
        unfolding subspace_topology_def by (by100 blast)
      have "?V \<inter> T' \<in> TB" by (rule topology_inter2[OF assms(4) hV_open hT'])
      thus ?thesis using hpC_eq by (by100 simp)
    qed
    have hpC_nhd: "neighborhood_of b B TB (p ` ?C)"
    proof -
      have "b \<in> p ` ?C" using he_C he(2) by (by100 blast)
      thus ?thesis using hpC_TB unfolding neighborhood_of_def by (by100 blast)
    qed
    have hpC_sub_U: "p ` ?C \<subseteq> U"
    proof -
      have "?C \<subseteq> W" by (rule hC_sub_W)
      hence "p ` ?C \<subseteq> p ` W" by (by100 blast)
      also have "p ` W = ?V" using hp_bij unfolding bij_betw_def by (by100 blast)
      also have "?V \<subseteq> U0" by (by100 blast)
      also have "U0 \<subseteq> U" by (rule hU0(3))
      finally show ?thesis .
    qed
    have hpC_sub_B: "p ` ?C \<subseteq> B"
    proof -
      have "p ` ?C \<subseteq> p ` W" using hC_sub_W by (by100 blast)
      also have "p ` W = ?V" using hp_bij unfolding bij_betw_def by (by100 blast)
      also have "?V \<subseteq> B" by (rule hV_sub_B)
      finally show ?thesis .
    qed
    have hC_pc: "top1_path_connected_on ?C (subspace_topology E TE ?C)"
    proof -
      have "top1_path_connected_on ?C (subspace_topology W (subspace_topology E TE W) ?C)"
        by (rule top1_path_component_of_on_path_connected[OF hW_top hW(2)])
      moreover have "subspace_topology W (subspace_topology E TE W) ?C = subspace_topology E TE ?C"
        by (rule subspace_topology_trans[OF hC_sub_W])
      ultimately show ?thesis by (by100 simp)
    qed
    have hpC_pc: "top1_path_connected_on (p ` ?C) (subspace_topology B TB (p ` ?C))"
    proof -
      \<comment> \<open>Restrict homeomorphism p|_W to C: p|_C: C \<cong> p(C).\<close>
      have hC_openin_V: "openin_on ?V (subspace_topology B TB ?V) (p ` ?C)"
        using hpC_open_sub unfolding openin_on_def
      proof (intro conjI)
        show "p ` ?C \<subseteq> ?V" using hC_sub_W hp_bij unfolding bij_betw_def by (by100 blast)
        show "p ` ?C \<in> subspace_topology B TB ?V" by (rule hpC_open_sub)
      qed
      have hpC_homeo: "top1_homeomorphism_on ?C (subspace_topology E TE ?C)
          (p ` ?C) (subspace_topology B TB (p ` ?C)) p"
      proof -
        have hC_openin_W: "openin_on W (subspace_topology E TE W) ?C"
          using hPC hC_sub_W unfolding openin_on_def by (by100 blast)
        have hpC_sub_V: "p ` ?C \<subseteq> ?V"
          using hC_sub_W hp_bij unfolding bij_betw_def by (by100 blast)
        have hTV: "is_topology_on ?V (subspace_topology B TB ?V)"
          using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        have hrestr: "top1_homeomorphism_on {x \<in> W. p x \<in> p ` ?C}
            (subspace_topology W (subspace_topology E TE W) {x \<in> W. p x \<in> p ` ?C})
            (p ` ?C) (subspace_topology ?V (subspace_topology B TB ?V) (p ` ?C)) p"
          by (rule homeomorphism_restrict_open[OF hp_homeo hC_openin_V hpC_sub_V hW_top hTV])
        have hsub1: "subspace_topology W (subspace_topology E TE W) {x \<in> W. p x \<in> p ` ?C}
            = subspace_topology E TE {x \<in> W. p x \<in> p ` ?C}"
        proof -
          have "{x \<in> W. p x \<in> p ` ?C} \<subseteq> W" by (by100 blast)
          thus ?thesis by (rule subspace_topology_trans)
        qed
        have hsub2: "subspace_topology ?V (subspace_topology B TB ?V) (p ` ?C)
            = subspace_topology B TB (p ` ?C)"
          by (rule subspace_topology_trans[OF hpC_sub_V])
        have "top1_homeomorphism_on {x \<in> W. p x \<in> p ` ?C}
            (subspace_topology E TE {x \<in> W. p x \<in> p ` ?C})
            (p ` ?C) (subspace_topology B TB (p ` ?C)) p"
          using hrestr hsub1 hsub2 by simp
        moreover have "{x \<in> W. p x \<in> p ` ?C} = ?C"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> {x \<in> W. p x \<in> p ` ?C}"
          hence "x \<in> W" "p x \<in> p ` ?C" by (by100 blast)+
          then obtain c where "c \<in> ?C" "p x = p c" by (by100 blast)
          have "c \<in> W" using \<open>c \<in> ?C\<close> hC_sub_W by (by100 blast)
          have "inj_on p W" using hp_bij unfolding bij_betw_def by (by100 blast)
          hence "x = c" using \<open>x \<in> W\<close> \<open>c \<in> W\<close> \<open>p x = p c\<close> unfolding inj_on_def by (by100 blast)
          thus "x \<in> ?C" using \<open>c \<in> ?C\<close> by (by100 simp)
        next
          fix x assume "x \<in> ?C"
          thus "x \<in> {x \<in> W. p x \<in> p ` ?C}" using hC_sub_W by (by100 blast)
        qed
        ultimately show ?thesis by (by100 simp)
      qed
      from homeomorphism_preserves_path_connected[OF hpC_homeo hC_pc]
      show ?thesis .
    qed
    show "\<exists>V. neighborhood_of b B TB V \<and> V \<subseteq> U \<and> V \<subseteq> B \<and>
        top1_path_connected_on V (subspace_topology B TB V)"
      using hpC_nhd hpC_sub_U hpC_sub_B hpC_pc by (by100 blast)
  qed
qed

(** from \<S>80 Theorem 80.3: universal covering factors through any covering **)
theorem Theorem_80_3_universal:
  assumes "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "is_topology_on_strict Y TY"
      and "top1_covering_map_on E TE B TB p"
      and "top1_simply_connected_on E TE"
      and "top1_covering_map_on Y TY B TB r"
      and "top1_locally_path_connected_on E TE"
      and "top1_path_connected_on Y TY"
  shows "\<exists>q. top1_covering_map_on E TE Y TY q \<and> (\<forall>e\<in>E. r (q e) = p e)"
proof (cases "E = {}")
  case True
  \<comment> \<open>Empty case: E = {} implies B = {} (surjectivity of p) implies Y = {} (surjectivity of r).
     Any function from {} to {} is a covering map.\<close>
  have hB_empty: "B = {}" using True top1_covering_map_on_surj[OF assms(4)] by (by100 blast)
  have hY_empty: "Y = {}" using hB_empty top1_covering_map_on_surj[OF assms(6)] by (by100 blast)
  have "top1_covering_map_on E TE Y TY (\<lambda>e. undefined)"
    unfolding top1_covering_map_on_def top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix x assume "x \<in> E" thus "(undefined :: 'c) \<in> Y" using True by (by100 blast)
  next
    fix V assume "V \<in> TY" show "{x \<in> E. (undefined :: 'c) \<in> V} \<in> TE"
      using True assms(1) unfolding is_topology_on_strict_def is_topology_on_def by (by100 auto)
  next
    show "(\<lambda>e. undefined :: 'c) ` E = Y" using True hY_empty by (by100 blast)
  next
    fix b assume "b \<in> Y" thus "\<exists>U. b \<in> U \<and> top1_evenly_covered_on E TE Y TY (\<lambda>e. undefined) U"
      using hY_empty by (by100 blast)
  qed
  thus ?thesis using True by (by100 blast)
next
  case False
  \<comment> \<open>Munkres 80.3: Define q: E \<rightarrow> Y by path-lifting. For e \<in> E, choose path \<alpha> in E
     from e0 to e. Lift r\<inverse> \<circ> p \<circ> \<alpha> to Y starting at y0 (where r(y0)=b0).
     The lift's endpoint is q(e). Well-defined because E is simply connected.\<close>
  obtain e0 where he0: "e0 \<in> E" using False by (by100 blast)
  let ?b0 = "p e0"
  have hb0_B: "?b0 \<in> B"
    using he0 top1_covering_map_on_surj[OF assms(4)] by (by100 blast)
  have hr_surj: "r ` Y = B" by (rule top1_covering_map_on_surj[OF assms(6)])
  have "?b0 \<in> r ` Y" using hb0_B hr_surj by (by100 simp)
  then obtain y0 where hy0: "y0 \<in> Y" and hry0: "r y0 = ?b0"
    unfolding image_def by (by100 auto)
  \<comment> \<open>For each e \<in> E, pick path \<alpha> from e0 to e. Lift p\<circ>\<alpha> to Y starting at y0.
     Simple connectivity ensures uniqueness (different \<alpha>'s give same endpoint).\<close>
  have "\<exists>q. (\<forall>e\<in>E. q e \<in> Y) \<and> (\<forall>e\<in>E. r (q e) = p e)
      \<and> q e0 = y0 \<and> top1_continuous_map_on E TE Y TY q"
  proof -
    have hTE: "is_topology_on E TE" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have hTB: "is_topology_on B TB" using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
    have hTY: "is_topology_on Y TY" using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
    have hp_cont: "top1_continuous_map_on E TE B TB p"
      by (rule top1_covering_map_on_continuous[OF assms(4)])
    have hE_pc: "top1_path_connected_on E TE"
      using assms(5) unfolding top1_simply_connected_on_def by (by100 blast)
    \<comment> \<open>E is locally path-connected (covering space of locally path-connected B,
       or directly from the covering structure + local homeomorphisms).\<close>
    have hE_lpc: "top1_locally_path_connected_on E TE" by (rule assms(7))
    have hpe0: "p e0 = r y0" using hry0 by (by100 simp)
    \<comment> \<open>E simply connected \<Rightarrow> p_*(\<pi>_1(E)) = {e} \<subseteq> r_*(\<pi>_1(Y)).\<close>
    have himg_triv: "top1_fundamental_group_image_hom E TE e0 B TB (r y0) p
        = {top1_fundamental_group_id B TB (r y0)}"
      by (rule simply_connected_trivial_image[OF assms(5) assms(4) he0 hpe0 hTB])
    have hsubgrp: "top1_fundamental_group_image_hom E TE e0 B TB (r y0) p
        \<subseteq> top1_fundamental_group_image_hom Y TY y0 B TB (r y0) r"
    proof -
      \<comment> \<open>{e} is in any image_hom (the identity class is always in the image).\<close>
      have "top1_fundamental_group_id B TB (r y0)
          \<in> top1_fundamental_group_image_hom Y TY y0 B TB (r y0) r"
      proof -
        \<comment> \<open>id_Y \<in> carrier(Y). induced(id_Y) = {g | loop_equiv(r\<circ>const_y0, g)} = id_B.\<close>
        have hid_Y: "top1_fundamental_group_id Y TY y0 \<in> top1_fundamental_group_carrier Y TY y0"
          using top1_fundamental_group_is_group[OF hTY hy0] unfolding top1_is_group_on_def by (by100 blast)
        have "top1_fundamental_group_induced_on Y TY y0 B TB (r y0) r
            (top1_fundamental_group_id Y TY y0)
          = top1_fundamental_group_id B TB (r y0)"
        proof -
          \<comment> \<open>induced(id) = {g | \<exists>f\<in>id. loop_equiv(r\<circ>f, g)} = {g | loop_equiv(r\<circ>const, g)} = id_B.\<close>
          have hconst_in: "top1_constant_path y0 \<in> top1_fundamental_group_id Y TY y0"
            unfolding top1_fundamental_group_id_def
            using top1_loop_equiv_on_refl[OF top1_constant_path_is_loop[OF hTY hy0]] by (by100 blast)
          have hrconst: "r \<circ> top1_constant_path y0 = top1_constant_path (r y0)"
            unfolding top1_constant_path_def by (rule ext) (by100 simp)
          show ?thesis
            unfolding top1_fundamental_group_induced_on_def top1_fundamental_group_id_def
          proof (rule set_eqI, rule iffI)
            fix k
            assume "k \<in> {g'. \<exists>fa\<in>{g. top1_loop_equiv_on Y TY y0 (top1_constant_path y0) g}.
                top1_loop_equiv_on B TB (r y0) (r \<circ> fa) g'}"
            then obtain fa where hfa: "top1_loop_equiv_on Y TY y0 (top1_constant_path y0) fa"
                and hk: "top1_loop_equiv_on B TB (r y0) (r \<circ> fa) k" by (by100 blast)
            have hfa_loop: "top1_is_loop_on Y TY y0 fa"
              using hfa unfolding top1_loop_equiv_on_def by (by100 blast)
            have "top1_loop_equiv_on B TB (r y0) (r \<circ> top1_constant_path y0) (r \<circ> fa)"
            proof -
              have "top1_loop_equiv_on B TB (r y0) (r \<circ> top1_constant_path y0) (r \<circ> fa)"
                using top1_induced_preserves_loop_equiv[OF hTY
                  top1_covering_map_on_continuous[OF assms(6)]
                  top1_constant_path_is_loop[OF hTY hy0] hfa_loop hfa] by (by100 simp)
              thus ?thesis .
            qed
            hence "top1_loop_equiv_on B TB (r y0) (top1_constant_path (r y0)) (r \<circ> fa)"
              using hrconst by (by100 simp)
            from top1_loop_equiv_on_trans[OF hTB this hk]
            show "k \<in> {g. top1_loop_equiv_on B TB (r y0) (top1_constant_path (r y0)) g}" by (by100 blast)
          next
            fix k assume "k \<in> {g. top1_loop_equiv_on B TB (r y0) (top1_constant_path (r y0)) g}"
            hence "top1_loop_equiv_on B TB (r y0) (top1_constant_path (r y0)) k" by (by100 blast)
            hence "top1_loop_equiv_on B TB (r y0) (r \<circ> top1_constant_path y0) k"
              using hrconst by (by100 simp)
            show "k \<in> {g'. \<exists>fa\<in>{g. top1_loop_equiv_on Y TY y0 (top1_constant_path y0) g}.
                top1_loop_equiv_on B TB (r y0) (r \<circ> fa) g'}"
              apply (rule CollectI)
              apply (rule bexI[of _ "top1_constant_path y0"])
              apply (rule \<open>top1_loop_equiv_on B TB (r y0) (r \<circ> top1_constant_path y0) k\<close>)
              using hconst_in unfolding top1_fundamental_group_id_def by (by100 blast)
          qed
        qed
        thus ?thesis unfolding top1_fundamental_group_image_hom_def using hid_Y by (by100 force)
      qed
      thus ?thesis using himg_triv by (by100 simp)
    qed
    from general_lifting_criterion[OF assms(6) hTE hTB hTY hp_cont hE_pc hE_lpc he0 hy0
        hpe0 hsubgrp]
    obtain q where "\<forall>e\<in>E. q e \<in> Y" "\<forall>e\<in>E. r (q e) = p e"
        "q e0 = y0" "top1_continuous_map_on E TE Y TY q" by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  then obtain q where hq_Y: "\<forall>e\<in>E. q e \<in> Y" and hq_rp: "\<forall>e\<in>E. r (q e) = p e"
      and hq_e0: "q e0 = y0" and hq_cont: "top1_continuous_map_on E TE Y TY q" by (by100 blast)
  \<comment> \<open>q is a covering map: evenly covered because p and r both are.
     For each y \<in> Y, take b = r(y). Take U evenly covered by both p and r.
     Slices of p\<inverse>(U) are {U_\<alpha>}, slices of r\<inverse>(U) are {V_\<beta>}.
     q maps each U_\<alpha> into some V_\<beta> (connectedness).
     q restricted to U_\<alpha> = r_\<beta>\<inverse> \<circ> p_\<alpha>, a homeomorphism.
     So q evenly covers each V_\<beta>.\<close>
  have hTE: "is_topology_on E TE" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hTB: "is_topology_on B TB" using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
  have hTY: "is_topology_on Y TY" using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
  have hq_surj: "q ` E = Y"
  proof (rule equalityI)
    show "q ` E \<subseteq> Y" using hq_Y by (by100 blast)
    show "Y \<subseteq> q ` E"
    proof -
      \<comment> \<open>q(E) is non-empty (contains y0).\<close>
      have hy0_qE: "y0 \<in> q ` E" using hq_e0 he0 by (by100 blast)
      \<comment> \<open>q(E) is open in Y: for each y = q(e), use covering structure to find
         a neighborhood of y contained in q(E). The r-slice containing y maps
         homeomorphically to an open U \<subseteq> B. The p-slice containing e maps
         homeomorphically to U. So q = r^{-1} \<circ> p maps a neighborhood of e
         onto a neighborhood of y, giving y \<in> interior of q(E).\<close>
      have hqE_open: "openin_on Y TY (q ` E)"
      proof -
        have hqE_sub: "q ` E \<subseteq> Y" using hq_Y by (by100 blast)
        \<comment> \<open>For each e, build an open neighborhood of q(e) in q(E).\<close>
        have "\<forall>e\<in>E. \<exists>Ve. Ve \<in> TY \<and> q e \<in> Ve \<and> Ve \<subseteq> q ` E"
        proof
          fix e assume he: "e \<in> E"
          let ?b = "p e"
          have hb: "?b \<in> B"
            using he top1_covering_map_on_surj[OF assms(4)] by (by100 blast)
          \<comment> \<open>Get U evenly covered by both p and r.\<close>
          obtain Up where "?b \<in> Up" "top1_evenly_covered_on E TE B TB p Up"
            using hb assms(4) unfolding top1_covering_map_on_def by (by100 blast)
          obtain Ur where "?b \<in> Ur" "top1_evenly_covered_on Y TY B TB r Ur"
            using hb assms(6) unfolding top1_covering_map_on_def by (by100 blast)
          have hUp_open: "openin_on B TB Up"
            using \<open>top1_evenly_covered_on E TE B TB p Up\<close>
            unfolding top1_evenly_covered_on_def by (by100 blast)
          have hUr_open: "openin_on B TB Ur"
            using \<open>top1_evenly_covered_on Y TY B TB r Ur\<close>
            unfolding top1_evenly_covered_on_def by (by100 blast)
          let ?U = "Up \<inter> Ur"
          have hU_open: "openin_on B TB ?U"
          proof -
            have "Up \<in> TB" using hUp_open unfolding openin_on_def by (by100 blast)
            moreover have "Ur \<in> TB" using hUr_open unfolding openin_on_def by (by100 blast)
            ultimately have "Up \<inter> Ur \<in> TB" by (rule topology_inter2[OF hTB])
            moreover have "Up \<inter> Ur \<subseteq> B" using hUp_open unfolding openin_on_def by (by100 blast)
            ultimately show ?thesis unfolding openin_on_def by (by100 blast)
          qed
          have hU_b: "?b \<in> ?U" using \<open>?b \<in> Up\<close> \<open>?b \<in> Ur\<close> by (by100 blast)
          \<comment> \<open>Restrict both coverings to U.\<close>
          have hU_cov_p: "top1_evenly_covered_on E TE B TB p ?U"
            by (rule evenly_covered_open_subset[OF \<open>top1_evenly_covered_on E TE B TB p Up\<close>
                hU_open _ hTE hTB]) (by100 blast)
          have hU_cov_r: "top1_evenly_covered_on Y TY B TB r ?U"
            by (rule evenly_covered_open_subset[OF \<open>top1_evenly_covered_on Y TY B TB r Ur\<close>
                hU_open _ hTY hTB]) (by100 blast)
          \<comment> \<open>Get p-slice W containing e.\<close>
          obtain \<V>p where h\<V>p: "\<forall>V\<in>\<V>p. openin_on E TE V"
              "\<forall>V\<in>\<V>p. \<forall>V'\<in>\<V>p. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
              "{x\<in>E. p x \<in> ?U} = \<Union>\<V>p"
              "\<forall>V\<in>\<V>p. top1_homeomorphism_on V (subspace_topology E TE V) ?U
                              (subspace_topology B TB ?U) p"
            using hU_cov_p unfolding top1_evenly_covered_on_def
            by (elim conjE exE) (by100 blast)
          have he_pU: "e \<in> {x\<in>E. p x \<in> ?U}" using he hU_b by (by100 blast)
          hence "e \<in> \<Union>\<V>p" using h\<V>p(3) by (by100 simp)
          then obtain W where hW: "W \<in> \<V>p" "e \<in> W" by (by100 blast)
          \<comment> \<open>Get r-slice V containing q(e) = y.\<close>
          obtain \<V>r where h\<V>r: "\<forall>V\<in>\<V>r. openin_on Y TY V"
              "\<forall>V\<in>\<V>r. \<forall>V'\<in>\<V>r. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
              "{x\<in>Y. r x \<in> ?U} = \<Union>\<V>r"
              "\<forall>V\<in>\<V>r. top1_homeomorphism_on V (subspace_topology Y TY V) ?U
                              (subspace_topology B TB ?U) r"
            using hU_cov_r unfolding top1_evenly_covered_on_def
            by (elim conjE exE) (by100 blast)
          have hqe_Y: "q e \<in> Y" using he hq_Y by (by100 blast)
          have hrqe: "r (q e) = p e" using he hq_rp by (by100 blast)
          have "r (q e) \<in> ?U" using hrqe hU_b by (by100 simp)
          have hqe_rU: "q e \<in> {x\<in>Y. r x \<in> ?U}" using hqe_Y \<open>r (q e) \<in> ?U\<close> by (by100 blast)
          hence "q e \<in> \<Union>\<V>r" using h\<V>r(3) by (by100 simp)
          then obtain V where hV: "V \<in> \<V>r" "q e \<in> V" by (by100 blast)
          \<comment> \<open>V is open in Y.\<close>
          have hV_TY: "V \<in> TY"
            using h\<V>r(1) hV(1) unfolding openin_on_def by (by100 blast)
          \<comment> \<open>W' = W \<inter> q\<inverse>(V) is open in E and contains e.\<close>
          let ?W' = "W \<inter> {e' \<in> E. q e' \<in> V}"
          have hW_TE: "W \<in> TE" using h\<V>p(1) hW(1) unfolding openin_on_def by (by100 blast)
          have hqV_TE: "{e' \<in> E. q e' \<in> V} \<in> TE"
            using hq_cont hV_TY unfolding top1_continuous_map_on_def by (by100 blast)
          have hW'_TE: "?W' \<in> TE" by (rule topology_inter2[OF hTE hW_TE hqV_TE])
          have he_W': "e \<in> ?W'" using hW(2) he hV(2) by (by100 blast)
          \<comment> \<open>Key: q(W') = {v \<in> V | r v \<in> p ` W'}, which is open in V hence in Y.\<close>
          \<comment> \<open>Key: q(W') = {v \<in> V | r v \<in> p ` W'}.\<close>
          have hV_homeo: "top1_homeomorphism_on V (subspace_topology Y TY V) ?U
                              (subspace_topology B TB ?U) r"
            using h\<V>r(4) hV(1) by (by100 blast)
          have hr_bij: "bij_betw r V ?U"
            using hV_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have hr_inj: "inj_on r V" using hr_bij unfolding bij_betw_def by (by100 blast)
          have hW_homeo: "top1_homeomorphism_on W (subspace_topology E TE W) ?U
                              (subspace_topology B TB ?U) p"
            using h\<V>p(4) hW(1) by (by100 blast)
          have hqW'_eq: "q ` ?W' = {v \<in> V. r v \<in> p ` ?W'}"
          proof (rule set_eqI, rule iffI)
            fix v assume "v \<in> q ` ?W'"
            then obtain e' where he': "e' \<in> ?W'" "v = q e'" by (by100 blast)
            have "e' \<in> E" using he' by (by100 blast)
            have "v \<in> V" using he' by (by100 blast)
            have "r v = r (q e')" using he'(2) by (by100 simp)
            also have "\<dots> = p e'" using \<open>e' \<in> E\<close> hq_rp by (by100 blast)
            finally have "r v = p e'" .
            hence "r v \<in> p ` ?W'" using he'(1) by (by100 blast)
            thus "v \<in> {v \<in> V. r v \<in> p ` ?W'}" using \<open>v \<in> V\<close> by (by100 blast)
          next
            fix v assume hv: "v \<in> {v \<in> V. r v \<in> p ` ?W'}"
            hence "v \<in> V" "r v \<in> p ` ?W'" by (by100 blast)+
            then obtain e' where he': "e' \<in> ?W'" "r v = p e'" by (by100 blast)
            have "e' \<in> E" using he' by (by100 blast)
            have "q e' \<in> V" using he' by (by100 blast)
            have "r (q e') = p e'" using \<open>e' \<in> E\<close> hq_rp by (by100 blast)
            hence "r v = r (q e')" using he'(2) by (by100 simp)
            hence "v = q e'" using hr_inj \<open>v \<in> V\<close> \<open>q e' \<in> V\<close>
              unfolding inj_on_def by (by100 blast)
            thus "v \<in> q ` ?W'" using he'(1) by (by100 blast)
          qed
          \<comment> \<open>p(W') is open in U-subspace: homeomorphism inverse is continuous,
             so preimage of W' (open in W-subspace) under inv_into W p is open.\<close>
          have hp_inv_cont: "top1_continuous_map_on ?U (subspace_topology B TB ?U)
              W (subspace_topology E TE W) (inv_into W p)"
            using hW_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have hW'_sub_W: "?W' \<subseteq> W" by (by100 blast)
          have hW'_subspace: "?W' \<in> subspace_topology E TE W"
            using hW'_TE hW'_sub_W unfolding subspace_topology_def by (by100 blast)
          have hpW'_open: "p ` ?W' \<in> subspace_topology B TB ?U"
          proof -
            have "p ` ?W' = {u \<in> ?U. (inv_into W p) u \<in> ?W'}"
            proof (rule set_eqI, rule iffI)
              fix u assume "u \<in> p ` ?W'"
              then obtain e' where he': "e' \<in> ?W'" "u = p e'" by (by100 blast)
              have "e' \<in> W" using he' by (by100 blast)
              have hp_bij: "bij_betw p W ?U"
                using hW_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
              have "u \<in> ?U" using he' hp_bij unfolding bij_betw_def by (by100 blast)
              have "inv_into W p u = e'"
                using inv_into_f_f[of p W e'] hp_bij \<open>e' \<in> W\<close> he'(2)
                unfolding bij_betw_def by (by100 blast)
              thus "u \<in> {u \<in> ?U. (inv_into W p) u \<in> ?W'}" using \<open>u \<in> ?U\<close> he'(1) by (by100 simp)
            next
              fix u assume hu: "u \<in> {u \<in> ?U. (inv_into W p) u \<in> ?W'}"
              hence "u \<in> ?U" "(inv_into W p) u \<in> ?W'" by (by100 blast)+
              have "(inv_into W p) u \<in> W" using \<open>(inv_into W p) u \<in> ?W'\<close> by (by100 blast)
              have hp_bij: "bij_betw p W ?U"
                using hW_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
              have "u \<in> p ` W" using hp_bij \<open>u \<in> ?U\<close> unfolding bij_betw_def by (by100 blast)
              have "p ((inv_into W p) u) = u" by (rule f_inv_into_f[OF \<open>u \<in> p ` W\<close>])
              show "u \<in> p ` ?W'"
              proof (rule image_eqI)
                show "u = p (inv_into W p u)"
                  using \<open>p ((inv_into W p) u) = u\<close> by (by100 simp)
                show "inv_into W p u \<in> ?W'"
                  using \<open>(inv_into W p) u \<in> ?W'\<close> by (by100 simp)
              qed
            qed
            have hpreimg: "{u \<in> ?U. (inv_into W p) u \<in> ?W'} \<in> subspace_topology B TB ?U"
              using hp_inv_cont hW'_subspace
              unfolding top1_continuous_map_on_def by (by100 blast)
            thus ?thesis using \<open>p ` ?W' = {u \<in> ?U. (inv_into W p) u \<in> ?W'}\<close> by (by100 simp)
          qed
          \<comment> \<open>Preimage of p(W') under r is open in V-subspace.\<close>
          have hr_cont_on_V: "top1_continuous_map_on V (subspace_topology Y TY V) ?U
              (subspace_topology B TB ?U) r"
            using hV_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have hqW'_subV: "{v \<in> V. r v \<in> p ` ?W'} \<in> subspace_topology Y TY V"
            using hr_cont_on_V hpW'_open
            unfolding top1_continuous_map_on_def by (by100 blast)
          \<comment> \<open>Open in V-subspace + V open in Y \<Rightarrow> open in Y.\<close>
          have hqW'_in_sub: "q ` ?W' \<in> subspace_topology Y TY V"
            using hqW'_subV hqW'_eq by (by100 simp)
          have hqW'_TY: "q ` ?W' \<in> TY"
          proof -
            from hqW'_in_sub obtain T' where hT'_TY: "T' \<in> TY" and hqW'_VT': "q ` ?W' = V \<inter> T'"
              unfolding subspace_topology_def by (by100 blast)
            have "V \<inter> T' \<in> TY" by (rule topology_inter2[OF hTY hV_TY hT'_TY])
            thus ?thesis using hqW'_VT' by (by100 simp)
          qed
          \<comment> \<open>q(e) \<in> q(W') \<subseteq> q(E).\<close>
          have "q e \<in> q ` ?W'" using he_W' by (by100 blast)
          moreover have "q ` ?W' \<subseteq> q ` E" by (by100 blast)
          ultimately show "\<exists>Ve. Ve \<in> TY \<and> q e \<in> Ve \<and> Ve \<subseteq> q ` E"
            using hqW'_TY by (by100 blast)
        qed
        \<comment> \<open>q(E) = \<Union>{Ve | e \<in> E}, union of open sets, hence open.\<close>
        hence "\<exists>S. S \<subseteq> TY \<and> q ` E = \<Union>S"
        proof -
          let ?S = "{Ve. \<exists>e\<in>E. Ve \<in> TY \<and> q e \<in> Ve \<and> Ve \<subseteq> q ` E}"
          have "?S \<subseteq> TY" by (by100 blast)
          moreover have "q ` E = \<Union>?S"
          proof (rule set_eqI, rule iffI)
            fix y assume "y \<in> q ` E"
            then obtain e where "e \<in> E" "y = q e" by (by100 blast)
            then obtain Ve where "Ve \<in> TY" "q e \<in> Ve" "Ve \<subseteq> q ` E"
              using \<open>\<forall>e\<in>E. \<exists>Ve. Ve \<in> TY \<and> q e \<in> Ve \<and> Ve \<subseteq> q ` E\<close> by (by100 blast)
            thus "y \<in> \<Union>?S" using \<open>e \<in> E\<close> \<open>y = q e\<close> by (by100 blast)
          next
            fix y assume "y \<in> \<Union>?S"
            then obtain Ve where "Ve \<subseteq> q ` E" "y \<in> Ve" by (by100 blast)
            thus "y \<in> q ` E" by (by100 blast)
          qed
          ultimately show ?thesis by (by100 blast)
        qed
        then obtain S where hS: "S \<subseteq> TY" "q ` E = \<Union>S" by (elim exE conjE) (by100 blast)
        have hunion: "\<forall>U. U \<subseteq> TY \<longrightarrow> \<Union>U \<in> TY"
          using hTY unfolding is_topology_on_def by (by100 blast)
        have "\<Union>S \<in> TY" using hunion hS(1) by (by100 blast)
        hence "q ` E \<in> TY" using hS(2) by (by100 simp)
        thus ?thesis using hqE_sub unfolding openin_on_def by (by100 blast)
      qed
      \<comment> \<open>Direct surjectivity via path-lifting: for y \<in> Y, take path \<gamma> from y0 to y,
         lift r\<circ>\<gamma> to E via p, then q\<circ>lift = \<gamma> by uniqueness, so y = q(lift(1)).\<close>
      show "Y \<subseteq> q ` E"
      proof
        fix y assume hy: "y \<in> Y"
        \<comment> \<open>Y is path-connected, so there exists a path \<gamma> from y0 to y.\<close>
        obtain \<gamma> where h\<gamma>: "top1_is_path_on Y TY y0 y \<gamma>"
          using assms(8) hy hy0 unfolding top1_path_connected_on_def by (by100 blast)
        \<comment> \<open>r \<circ> \<gamma> is a path in B from b0 to r(y).\<close>
        have hr_cont: "top1_continuous_map_on Y TY B TB r"
          by (rule top1_covering_map_on_continuous[OF assms(6)])
        have h\<gamma>_cont: "top1_continuous_map_on I_set I_top Y TY \<gamma>"
          using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
        have hr\<gamma>_cont: "top1_continuous_map_on I_set I_top B TB (r \<circ> \<gamma>)"
          by (rule top1_continuous_map_on_comp[OF h\<gamma>_cont hr_cont])
        have h\<gamma>0: "\<gamma> 0 = y0" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
        have h\<gamma>1: "\<gamma> 1 = y" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
        have hr\<gamma>0: "(r \<circ> \<gamma>) 0 = p e0" using h\<gamma>0 hry0 by (by100 simp)
        have hr\<gamma>1: "(r \<circ> \<gamma>) 1 = r y" using h\<gamma>1 by (by100 simp)
        have h_r\<gamma>: "top1_is_path_on B TB (p e0) (r y) (r \<circ> \<gamma>)"
          unfolding top1_is_path_on_def using hr\<gamma>_cont hr\<gamma>0 hr\<gamma>1 by (by100 blast)
        \<comment> \<open>Lift r \<circ> \<gamma> to E via p, starting at e0.\<close>
        have "\<exists>\<alpha>. top1_is_path_on E TE e0 (\<alpha> 1) \<alpha> \<and> (\<forall>s\<in>I_set. p (\<alpha> s) = (r \<circ> \<gamma>) s)"
          using Lemma_54_1_path_lifting[OF assms(4) he0 _ h_r\<gamma> hTB hTE] by (by100 simp)
        then obtain \<alpha> where h\<alpha>_path: "top1_is_path_on E TE e0 (\<alpha> 1) \<alpha>"
            and h\<alpha>_lift: "\<forall>s\<in>I_set. p (\<alpha> s) = (r \<circ> \<gamma>) s" by (by100 blast)
        \<comment> \<open>q \<circ> \<alpha> is a lift of r \<circ> \<gamma> via r, starting at y0.\<close>
        have h\<alpha>0: "\<alpha> 0 = e0" using h\<alpha>_path unfolding top1_is_path_on_def by (by100 blast)
        have hq\<alpha>_start: "(q \<circ> \<alpha>) 0 = y0" using h\<alpha>0 hq_e0 by (by100 simp)
        have hq\<alpha>_lift: "\<forall>s\<in>I_set. r ((q \<circ> \<alpha>) s) = (r \<circ> \<gamma>) s"
        proof (intro ballI)
          fix s assume hs: "s \<in> I_set"
          have h\<alpha>s_E: "\<alpha> s \<in> E"
          proof -
            have "top1_continuous_map_on I_set I_top E TE \<alpha>"
              using h\<alpha>_path unfolding top1_is_path_on_def by (by100 blast)
            thus ?thesis using hs unfolding top1_continuous_map_on_def by (by100 blast)
          qed
          have "r (q (\<alpha> s)) = p (\<alpha> s)" using hq_rp h\<alpha>s_E by (by100 blast)
          also have "\<dots> = (r \<circ> \<gamma>) s" using h\<alpha>_lift hs by (by100 blast)
          finally show "r ((q \<circ> \<alpha>) s) = (r \<circ> \<gamma>) s" by (by100 simp)
        qed
        \<comment> \<open>q \<circ> \<alpha> is a path in Y from y0 to q(\<alpha>(1)).\<close>
        have h\<alpha>_cont: "top1_continuous_map_on I_set I_top E TE \<alpha>"
          using h\<alpha>_path unfolding top1_is_path_on_def by (by100 blast)
        have hq\<alpha>_cont: "top1_continuous_map_on I_set I_top Y TY (q \<circ> \<alpha>)"
          by (rule top1_continuous_map_on_comp[OF h\<alpha>_cont hq_cont])
        have hq\<alpha>1: "(q \<circ> \<alpha>) 1 = q (\<alpha> 1)" by (by100 simp)
        have hq\<alpha>_path: "top1_is_path_on Y TY y0 (q (\<alpha> 1)) (q \<circ> \<alpha>)"
          unfolding top1_is_path_on_def using hq\<alpha>_cont hq\<alpha>_start hq\<alpha>1 by (by100 blast)
        \<comment> \<open>\<gamma> lifts r\<circ>\<gamma> via r trivially.\<close>
        have h\<gamma>_lift: "\<forall>s\<in>I_set. r (\<gamma> s) = (r \<circ> \<gamma>) s" by (by100 simp)
        \<comment> \<open>By uniqueness of path lifts for r: q \<circ> \<alpha> = \<gamma> on I_set.\<close>
        have heq: "\<forall>s\<in>I_set. (q \<circ> \<alpha>) s = \<gamma> s"
          using Lemma_54_1_uniqueness[OF assms(6) hy0 hry0 h_r\<gamma>
              hq\<alpha>_path hq\<alpha>_lift h\<gamma> h\<gamma>_lift] by (by100 blast)
        \<comment> \<open>At s=1: q(\<alpha>(1)) = \<gamma>(1) = y.\<close>
        have "q (\<alpha> 1) = \<gamma> 1"
        proof -
          have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
          hence "(q \<circ> \<alpha>) 1 = \<gamma> 1" using heq by (by100 blast)
          thus ?thesis by (by100 simp)
        qed
        hence "q (\<alpha> 1) = y" using h\<gamma>1 by (by100 simp)
        moreover have "\<alpha> 1 \<in> E"
        proof -
          have "top1_continuous_map_on I_set I_top E TE \<alpha>"
            using h\<alpha>_path unfolding top1_is_path_on_def by (by100 blast)
          have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
          thus ?thesis using h\<alpha>_cont unfolding top1_continuous_map_on_def by (by100 blast)
        qed
        ultimately show "y \<in> q ` E" by (by100 blast)
      qed
    qed
  qed
  have hq_cov: "\<forall>y\<in>Y. \<exists>V. y \<in> V \<and> top1_evenly_covered_on E TE Y TY q V"
  proof
    fix y assume hy: "y \<in> Y"
    let ?b = "r y"
    have hb_B: "?b \<in> B"
      using hy top1_covering_map_on_surj[OF assms(6)] by (by100 blast)
    \<comment> \<open>Take U evenly covered by both p and r.\<close>
    obtain Up where hUp_b: "?b \<in> Up" and hUp_cov_p: "top1_evenly_covered_on E TE B TB p Up"
      using hb_B assms(4) unfolding top1_covering_map_on_def by (by100 blast)
    obtain Ur where hUr_b: "?b \<in> Ur" and hUr_cov_r: "top1_evenly_covered_on Y TY B TB r Ur"
      using hb_B assms(6) unfolding top1_covering_map_on_def by (by100 blast)
    let ?U = "Up \<inter> Ur"
    \<comment> \<open>U = Up \<inter> Ur is open, contains b, and is evenly covered by both p and r.\<close>
    have hU_b: "?b \<in> ?U" using hUp_b hUr_b by (by100 blast)
    \<comment> \<open>The restriction of a covering to an open subset is still a covering.\<close>
    \<comment> \<open>Get the slice of r\<inverse>(U) containing y. This will be the evenly covered neighborhood.\<close>
    obtain \<V>r where h\<V>r_open: "\<forall>V\<in>\<V>r. openin_on Y TY V"
        and h\<V>r_disj: "\<forall>V\<in>\<V>r. \<forall>V'\<in>\<V>r. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
        and h\<V>r_union: "{x\<in>Y. r x \<in> Ur} = \<Union>\<V>r"
        and h\<V>r_homeo: "\<forall>V\<in>\<V>r. top1_homeomorphism_on V (subspace_topology Y TY V) Ur
                                      (subspace_topology B TB Ur) r"
      using hUr_cov_r unfolding top1_evenly_covered_on_def
      by (elim conjE exE) (by100 blast)
    \<comment> \<open>y is in r\<inverse>(Ur), so y \<in> \<Union>\<V>r. Pick the slice V0 containing y.\<close>
    have hy_in_rU: "y \<in> {x\<in>Y. r x \<in> Ur}" using hy hUr_b by (by100 blast)
    hence "y \<in> \<Union>\<V>r" using h\<V>r_union by (by100 simp)
    then obtain V0 where hV0: "V0 \<in> \<V>r" and hy_V0: "y \<in> V0" by (by100 blast)
    \<comment> \<open>V0 is our evenly covered neighborhood.\<close>
    \<comment> \<open>To show: top1_evenly_covered_on E TE Y TY q V0.\<close>
    \<comment> \<open>Each slice U_\<alpha> of p\<inverse>(U) that maps into V0 maps homeomorphically via q.\<close>
    \<comment> \<open>Restrict p-covering to Up\<inter>Ur.\<close>
    have hTE: "is_topology_on E TE" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have hTB: "is_topology_on B TB" using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
    have hTY: "is_topology_on Y TY" using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
    have hUp_open: "openin_on B TB Up"
      using hUp_cov_p unfolding top1_evenly_covered_on_def by (by100 blast)
    have hUr_open: "openin_on B TB Ur"
      using hUr_cov_r unfolding top1_evenly_covered_on_def by (by100 blast)
    have hU_open: "openin_on B TB ?U"
    proof -
      have "Up \<in> TB" using hUp_open unfolding openin_on_def by (by100 blast)
      moreover have "Ur \<in> TB" using hUr_open unfolding openin_on_def by (by100 blast)
      ultimately have "Up \<inter> Ur \<in> TB" by (rule topology_inter2[OF hTB])
      moreover have "Up \<inter> Ur \<subseteq> B" using hUp_open unfolding openin_on_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by (by100 blast)
    qed
    have hU_cov_p: "top1_evenly_covered_on E TE B TB p ?U"
      by (rule evenly_covered_open_subset[OF hUp_cov_p hU_open _ hTE hTB]) (by100 blast)
    have hU_cov_r: "top1_evenly_covered_on Y TY B TB r ?U"
      by (rule evenly_covered_open_subset[OF hUr_cov_r hU_open _ hTY hTB]) (by100 blast)
    \<comment> \<open>Get p-slices and r-slices over U = Up\<inter>Ur.\<close>
    obtain \<V>p where h\<V>p_open: "\<forall>V\<in>\<V>p. openin_on E TE V"
        and h\<V>p_disj: "\<forall>V\<in>\<V>p. \<forall>V'\<in>\<V>p. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
        and h\<V>p_union: "{x\<in>E. p x \<in> ?U} = \<Union>\<V>p"
        and h\<V>p_homeo: "\<forall>V\<in>\<V>p. top1_homeomorphism_on V (subspace_topology E TE V) ?U
                                      (subspace_topology B TB ?U) p"
      using hU_cov_p unfolding top1_evenly_covered_on_def
      by (elim conjE exE) (by100 blast)
    obtain \<V>r' where h\<V>r'_open: "\<forall>V\<in>\<V>r'. openin_on Y TY V"
        and h\<V>r'_disj: "\<forall>V\<in>\<V>r'. \<forall>V'\<in>\<V>r'. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
        and h\<V>r'_union: "{x\<in>Y. r x \<in> ?U} = \<Union>\<V>r'"
        and h\<V>r'_homeo: "\<forall>V\<in>\<V>r'. top1_homeomorphism_on V (subspace_topology Y TY V) ?U
                                      (subspace_topology B TB ?U) r"
      using hU_cov_r unfolding top1_evenly_covered_on_def
      by (elim conjE exE) (by100 blast)
    \<comment> \<open>Refine U to path-connected using B locally path-connected.\<close>
    have hB_lpc: "top1_locally_path_connected_on B TB"
      by (rule covering_base_locally_path_connected[OF assms(4) assms(7) hTE hTB])
    have hU_TB: "?U \<in> TB" using hU_open unfolding openin_on_def by (by100 blast)
    have hU_sub_B: "?U \<subseteq> B" using hU_open unfolding openin_on_def by (by100 blast)
    have "\<exists>U''. U'' \<in> TB \<and> ?b \<in> U'' \<and> U'' \<subseteq> ?U \<and> U'' \<subseteq> B
        \<and> top1_path_connected_on U'' (subspace_topology B TB U'')"
    proof -
      \<comment> \<open>By Theorem 25.4: B lpc \<Rightarrow> path components of open sets are open.\<close>
      have hpc_open: "\<forall>P \<in> top1_path_components_on ?U (subspace_topology B TB ?U). P \<in> TB"
        using iffD1[OF Theorem_25_4[OF hTB]] hB_lpc hU_TB hU_sub_B by (by100 blast)
      \<comment> \<open>Path component of b in U.\<close>
      let ?P = "top1_path_component_of_on ?U (subspace_topology B TB ?U) ?b"
      have hU_top: "is_topology_on ?U (subspace_topology B TB ?U)"
      proof -
        have "top1_locally_path_connected_on ?U (subspace_topology B TB ?U)"
          by (rule open_subset_locally_path_connected[OF hB_lpc hU_TB hU_sub_B])
        thus ?thesis unfolding top1_locally_path_connected_on_def by (by100 blast)
      qed
      have hP_comp: "?P \<in> top1_path_components_on ?U (subspace_topology B TB ?U)"
        using hU_b unfolding top1_path_components_on_def by (by100 blast)
      have hP_TB: "?P \<in> TB" using hpc_open hP_comp by (by100 blast)
      have hP_b: "?b \<in> ?P" by (rule top1_path_component_of_on_self_mem[OF hU_top hU_b])
      have hP_sub: "?P \<subseteq> ?U" by (rule top1_path_component_of_on_subset[OF hU_top hU_b])
      have hP_sub_B: "?P \<subseteq> B" using hP_sub hU_sub_B by (by100 blast)
      have hP_pc: "top1_path_connected_on ?P (subspace_topology ?U (subspace_topology B TB ?U) ?P)"
        by (rule top1_path_component_of_on_path_connected[OF hU_top hU_b])
      have "subspace_topology ?U (subspace_topology B TB ?U) ?P = subspace_topology B TB ?P"
        by (rule subspace_topology_trans[OF hP_sub])
      hence "top1_path_connected_on ?P (subspace_topology B TB ?P)" using hP_pc by (by100 simp)
      thus ?thesis using hP_TB hP_b hP_sub hP_sub_B by (by100 blast)
    qed
    then obtain U'' where hU''_TB: "U'' \<in> TB" and hU''_b: "?b \<in> U''" and hU''_sub: "U'' \<subseteq> ?U"
        and hU''_sub_B: "U'' \<subseteq> B"
        and hU''_pc: "top1_path_connected_on U'' (subspace_topology B TB U'')"
      by (by100 blast)
    have hU''_openin: "openin_on B TB U''"
      using hU''_TB hU''_sub_B unfolding openin_on_def by (by100 blast)
    \<comment> \<open>Restrict coverings to path-connected U''.\<close>
    have hU''_sub_Up: "U'' \<subseteq> Up" using hU''_sub by (by100 blast)
    have hU''_sub_Ur: "U'' \<subseteq> Ur" using hU''_sub by (by100 blast)
    have hU''_cov_p: "top1_evenly_covered_on E TE B TB p U''"
      by (rule evenly_covered_open_subset[OF hUp_cov_p hU''_openin hU''_sub_Up hTE hTB])
    have hU''_cov_r: "top1_evenly_covered_on Y TY B TB r U''"
      by (rule evenly_covered_open_subset[OF hUr_cov_r hU''_openin hU''_sub_Ur hTY hTB])
    \<comment> \<open>Get r-slice V1 containing y over path-connected U''.\<close>
    obtain \<W>r where h\<W>r_open: "\<forall>W\<in>\<W>r. openin_on Y TY W"
        and h\<W>r_disj: "\<forall>W\<in>\<W>r. \<forall>W'\<in>\<W>r. W \<noteq> W' \<longrightarrow> W \<inter> W' = {}"
        and h\<W>r_union: "{x\<in>Y. r x \<in> U''} = \<Union>\<W>r"
        and h\<W>r_homeo: "\<forall>W\<in>\<W>r. top1_homeomorphism_on W (subspace_topology Y TY W)
            U'' (subspace_topology B TB U'') r"
      using hU''_cov_r unfolding top1_evenly_covered_on_def
      by (elim conjE exE) (by100 blast)
    have "r y \<in> U''" using hU''_b by (by100 simp)
    hence "y \<in> {x\<in>Y. r x \<in> U''}" using hy by (by100 blast)
    hence "y \<in> \<Union>\<W>r" using h\<W>r_union by (by100 simp)
    then obtain V1 where hV1: "V1 \<in> \<W>r" "y \<in> V1" by (by100 blast)
    have hV1_open: "openin_on Y TY V1" using h\<W>r_open hV1(1) by (by100 blast)
    \<comment> \<open>V1 is evenly covered by q.\<close>
    show "\<exists>V. y \<in> V \<and> top1_evenly_covered_on E TE Y TY q V"
    proof (rule exI[of _ V1], intro conjI)
      show "y \<in> V1" by (rule hV1(2))
      show "top1_evenly_covered_on E TE Y TY q V1"
      proof -
        \<comment> \<open>Get p-slices over U''.\<close>
        obtain \<W>p where h\<W>p_open: "\<forall>W\<in>\<W>p. openin_on E TE W"
            and h\<W>p_disj: "\<forall>W\<in>\<W>p. \<forall>W'\<in>\<W>p. W \<noteq> W' \<longrightarrow> W \<inter> W' = {}"
            and h\<W>p_union: "{x\<in>E. p x \<in> U''} = \<Union>\<W>p"
            and h\<W>p_homeo: "\<forall>W\<in>\<W>p. top1_homeomorphism_on W (subspace_topology E TE W)
                U'' (subspace_topology B TB U'') p"
          using hU''_cov_p unfolding top1_evenly_covered_on_def
          by (elim conjE exE) (by100 blast)
        \<comment> \<open>Each p-slice W is connected (homeomorphic to path-connected U'').\<close>
        \<comment> \<open>By lift uniqueness, q maps each W entirely into one r-slice.\<close>
        \<comment> \<open>Family: those W mapping into V1.\<close>
        let ?\<V>q = "{W \<in> \<W>p. \<exists>e \<in> W. q e \<in> V1}"
        show ?thesis unfolding top1_evenly_covered_on_def
        proof (intro conjI exI[of _ ?\<V>q])
          show "openin_on Y TY V1" by (rule hV1_open)
          show "\<forall>W\<in>?\<V>q. openin_on E TE W"
            using h\<W>p_open by (by100 blast)
          show "\<forall>W\<in>?\<V>q. \<forall>W'\<in>?\<V>q. W \<noteq> W' \<longrightarrow> W \<inter> W' = {}"
            using h\<W>p_disj by (by100 blast)
          \<comment> \<open>Key: each p-slice W is connected, so q maps W entirely into one r-slice.\<close>
          have hW_connected: "\<forall>W\<in>\<W>p. top1_connected_on W (subspace_topology E TE W)"
          proof (intro ballI)
            fix W assume "W \<in> \<W>p"
            have "top1_homeomorphism_on W (subspace_topology E TE W) U'' (subspace_topology B TB U'') p"
              using h\<W>p_homeo \<open>W \<in> \<W>p\<close> by (by100 blast)
            from homeomorphism_inverse[OF this]
            have "top1_homeomorphism_on U'' (subspace_topology B TB U'') W (subspace_topology E TE W)
                (inv_into W p)" .
            from homeomorphism_preserves_path_connected[OF this hU''_pc]
            have "top1_path_connected_on W (subspace_topology E TE W)" .
            thus "top1_connected_on W (subspace_topology E TE W)"
              by (rule top1_path_connected_imp_connected)
          qed
          have hV1_homeo: "top1_homeomorphism_on V1 (subspace_topology Y TY V1)
              U'' (subspace_topology B TB U'') r"
            using h\<W>r_homeo hV1(1) by (by100 blast)
          have hr_bij_V1: "bij_betw r V1 U''"
            using hV1_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have hr_inj_V1: "inj_on r V1" using hr_bij_V1 unfolding bij_betw_def by (by100 blast)
          \<comment> \<open>Shared fact: for each W \<in> \<V>q, q = (inv_into V1 r) \<circ> p on W.\<close>
          have hq_eq_h_all: "\<forall>W\<in>?\<V>q. \<forall>e'\<in>W. q e' = inv_into V1 r (p e')"
          proof (intro ballI)
            fix W e' assume hWq: "W \<in> ?\<V>q" and he': "e' \<in> W"
            \<comment> \<open>This follows from the internal hq\_eq\_h established in hW\_all\_V1.\<close>
            \<comment> \<open>We re-derive it via covering\_lift\_unique\_connected.\<close>
            have hW_mem: "W \<in> \<W>p" using hWq by (by100 blast)
            obtain e0 where he0_W: "e0 \<in> W" "q e0 \<in> V1" using hWq by (by100 blast)
            have hW_sub_E: "W \<subseteq> E" using hW_mem h\<W>p_open unfolding openin_on_def by (by100 blast)
            have hW_conn: "top1_connected_on W (subspace_topology E TE W)"
              using hW_connected hW_mem by (by100 blast)
            have hW_TE: "W \<in> TE" using hW_mem h\<W>p_open unfolding openin_on_def by (by100 blast)
            have hW_top: "is_topology_on W (subspace_topology E TE W)"
            proof -
              have "top1_locally_path_connected_on W (subspace_topology E TE W)"
                by (rule open_subset_locally_path_connected[OF assms(7) hW_TE hW_sub_E])
              thus ?thesis unfolding top1_locally_path_connected_on_def by (by100 blast)
            qed
            let ?h = "\<lambda>e. inv_into V1 r (p e)"
            have hW_pU: "\<forall>e1\<in>W. p e1 \<in> U''"
            proof (intro ballI)
              fix e1 assume "e1 \<in> W"
              thus "p e1 \<in> U''" using hW_mem h\<W>p_union by (by100 blast)
            qed
            have hh_V1: "\<forall>e1\<in>W. ?h e1 \<in> V1"
            proof (intro ballI)
              fix e1 assume "e1 \<in> W"
              have "p e1 \<in> r ` V1" using hr_bij_V1 hW_pU \<open>e1 \<in> W\<close> unfolding bij_betw_def by (by100 blast)
              thus "?h e1 \<in> V1" using inv_into_into[OF \<open>p e1 \<in> r ` V1\<close>] by (by100 simp)
            qed
            \<comment> \<open>q(e0) = h(e0) by injectivity of r on V1.\<close>
            have "?h e0 = q e0"
            proof -
              have "p e0 \<in> r ` V1" using hr_bij_V1 hW_pU he0_W(1) unfolding bij_betw_def by (by100 blast)
              have "r (?h e0) = p e0" by (rule f_inv_into_f[OF \<open>p e0 \<in> r ` V1\<close>])
              have "r (q e0) = p e0" using hq_rp he0_W(1) hW_sub_E by (by100 blast)
              have "?h e0 \<in> V1" using hh_V1 he0_W(1) by (by100 blast)
              have "r (?h e0) = r (q e0)" using \<open>r (?h e0) = p e0\<close> \<open>r (q e0) = p e0\<close> by (by100 simp)
              thus ?thesis using hr_inj_V1 \<open>?h e0 \<in> V1\<close> he0_W(2)
                unfolding inj_on_def by (by100 blast)
            qed
            \<comment> \<open>Both lifts of p through r, agree at e0, W connected \<Rightarrow> agree everywhere.\<close>
            have hq_cont_W: "top1_continuous_map_on W (subspace_topology E TE W) Y TY q"
            proof -
              have "\<forall>A f. top1_continuous_map_on E TE Y TY f \<and> A \<subseteq> E \<longrightarrow>
                  top1_continuous_map_on A (subspace_topology E TE A) Y TY f"
                using Theorem_18_2[OF hTE hTY hTY] by (by100 blast)
              thus ?thesis using hq_cont hW_sub_E by (by100 blast)
            qed
            have hh_cont_W: "top1_continuous_map_on W (subspace_topology E TE W) Y TY ?h"
            proof -
              have hp_W: "top1_continuous_map_on W (subspace_topology E TE W)
                  U'' (subspace_topology B TB U'') p"
                using h\<W>p_homeo hW_mem unfolding top1_homeomorphism_on_def by (by100 blast)
              have hinv_r: "top1_continuous_map_on U'' (subspace_topology B TB U'')
                  V1 (subspace_topology Y TY V1) (inv_into V1 r)"
                using homeomorphism_inverse[OF hV1_homeo]
                unfolding top1_homeomorphism_on_def by (by100 blast)
              have "top1_continuous_map_on W (subspace_topology E TE W)
                  V1 (subspace_topology Y TY V1) (inv_into V1 r \<circ> p)"
                by (rule top1_continuous_map_on_comp[OF hp_W hinv_r])
              hence hcomp: "top1_continuous_map_on W (subspace_topology E TE W)
                  V1 (subspace_topology Y TY V1) ?h"
                unfolding comp_def by (by100 simp)
              have hV1_sub_Y: "V1 \<subseteq> Y" using hV1_open unfolding openin_on_def by (by100 blast)
              show ?thesis unfolding top1_continuous_map_on_def
              proof (intro conjI ballI)
                fix e1 assume "e1 \<in> W"
                thus "?h e1 \<in> Y" using hh_V1 \<open>e1 \<in> W\<close> hV1_sub_Y by (by100 blast)
              next
                fix V assume "V \<in> TY"
                have "{e1 \<in> W. ?h e1 \<in> V} = {e1 \<in> W. ?h e1 \<in> V \<inter> V1}" using hh_V1 by (by100 blast)
                moreover have "V \<inter> V1 \<in> subspace_topology Y TY V1"
                  using \<open>V \<in> TY\<close> unfolding subspace_topology_def by (by100 blast)
                hence "{e1 \<in> W. ?h e1 \<in> V \<inter> V1} \<in> subspace_topology E TE W"
                  using hcomp unfolding top1_continuous_map_on_def by (by100 blast)
                ultimately show "{e1 \<in> W. ?h e1 \<in> V} \<in> subspace_topology E TE W" by (by100 simp)
              qed
            qed
            have hrq_eq_rh: "\<forall>e1\<in>W. r (q e1) = r (?h e1)"
            proof (intro ballI)
              fix e1 assume "e1 \<in> W"
              have "r (q e1) = p e1" using hq_rp \<open>e1 \<in> W\<close> hW_sub_E by (by100 blast)
              have "p e1 \<in> r ` V1" using hr_bij_V1 hW_pU \<open>e1 \<in> W\<close> unfolding bij_betw_def by (by100 blast)
              have "r (?h e1) = p e1" by (rule f_inv_into_f[OF \<open>p e1 \<in> r ` V1\<close>])
              show "r (q e1) = r (?h e1)" using \<open>r (q e1) = p e1\<close> \<open>r (?h e1) = p e1\<close> by (by100 simp)
            qed
            from covering_lift_unique_connected[OF assms(6) hW_top hTB hTY hW_conn
                hq_cont_W hh_cont_W hrq_eq_rh he0_W(1) \<open>?h e0 = q e0\<close>[symmetric]]
            show "q e' = inv_into V1 r (p e')" using he' by (by100 blast)
          qed
          \<comment> \<open>For W \<in> \<W>p with q(e) \<in> V1 for some e \<in> W: q maps ALL of W into V1.\<close>
          have hW_all_V1: "\<forall>W\<in>?\<V>q. \<forall>e\<in>W. q e \<in> V1"
          proof (intro ballI)
            fix W e assume hWq: "W \<in> ?\<V>q" and he_W: "e \<in> W"
            have hW_mem: "W \<in> \<W>p" using hWq by (by100 blast)
            obtain e0 where he0_W: "e0 \<in> W" "q e0 \<in> V1" using hWq by (by100 blast)
            have hW_conn: "top1_connected_on W (subspace_topology E TE W)"
              using hW_connected hW_mem by (by100 blast)
            \<comment> \<open>Define h = (inv_into V1 r) \<circ> p: W \<rightarrow> V1. Both q and h lift p through r.\<close>
            let ?h = "\<lambda>e. inv_into V1 r (p e)"
            \<comment> \<open>h maps W into V1 and r \<circ> h = p on W.\<close>
            have hW_sub_E: "W \<subseteq> E" using hW_mem h\<W>p_open unfolding openin_on_def by (by100 blast)
            have hW_pU: "\<forall>e'\<in>W. p e' \<in> U''"
            proof (intro ballI)
              fix e' assume "e' \<in> W"
              have "e' \<in> {x\<in>E. p x \<in> U''}" using \<open>e' \<in> W\<close> hW_mem h\<W>p_union by (by100 blast)
              thus "p e' \<in> U''" by (by100 blast)
            qed
            have hh_V1: "\<forall>e'\<in>W. ?h e' \<in> V1"
            proof (intro ballI)
              fix e' assume "e' \<in> W"
              have "p e' \<in> U''" using hW_pU \<open>e' \<in> W\<close> by (by100 blast)
              have "p e' \<in> r ` V1" using hr_bij_V1 \<open>p e' \<in> U''\<close> unfolding bij_betw_def by (by100 blast)
              thus "?h e' \<in> V1" using inv_into_into[OF \<open>p e' \<in> r ` V1\<close>] by (by100 simp)
            qed
            have hrh: "\<forall>e'\<in>W. r (?h e') = p e'"
            proof (intro ballI)
              fix e' assume "e' \<in> W"
              have "p e' \<in> U''" using hW_pU \<open>e' \<in> W\<close> by (by100 blast)
              have "p e' \<in> r ` V1" using hr_bij_V1 \<open>p e' \<in> U''\<close> unfolding bij_betw_def by (by100 blast)
              show "r (?h e') = p e'" by (rule f_inv_into_f[OF \<open>p e' \<in> r ` V1\<close>])
            qed
            \<comment> \<open>h(e0) = q(e0): both in V1, r(h(e0)) = p(e0) = r(q(e0)), r injective on V1.\<close>
            have "?h e0 = q e0"
            proof -
              have "r (?h e0) = p e0" using hrh he0_W(1) by (by100 blast)
              have "r (q e0) = p e0"
              proof -
                have "e0 \<in> E" using he0_W(1) hW_sub_E by (by100 blast)
                thus ?thesis using hq_rp by (by100 blast)
              qed
              have "?h e0 \<in> V1" using hh_V1 he0_W(1) by (by100 blast)
              have "q e0 \<in> V1" by (rule he0_W(2))
              from \<open>r (?h e0) = p e0\<close> \<open>r (q e0) = p e0\<close>
              have "r (?h e0) = r (q e0)" by (by100 simp)
              thus "?h e0 = q e0"
                using hr_inj_V1 \<open>?h e0 \<in> V1\<close> \<open>q e0 \<in> V1\<close> unfolding inj_on_def by (by100 blast)
            qed
            \<comment> \<open>By covering\_lift\_unique\_connected: q = h on W.\<close>
            \<comment> \<open>Both q|_W and h|_W: W \<rightarrow> Y lift p through r, W connected, agree at e0.\<close>
            \<comment> \<open>Apply covering\_lift\_unique\_connected: r covering, W connected domain,
               q|_W and h|_W both lift p through r, agree at e0.\<close>
            have hW_TE: "W \<in> TE" using hW_mem h\<W>p_open unfolding openin_on_def by (by100 blast)
            have hW_top: "is_topology_on W (subspace_topology E TE W)"
            proof -
              have "top1_locally_path_connected_on W (subspace_topology E TE W)"
                by (rule open_subset_locally_path_connected[OF assms(7) hW_TE hW_sub_E])
              thus ?thesis unfolding top1_locally_path_connected_on_def by (by100 blast)
            qed
            have hq_cont_W: "top1_continuous_map_on W (subspace_topology E TE W) Y TY q"
            proof -
              have "\<forall>A f. top1_continuous_map_on E TE Y TY f \<and> A \<subseteq> E \<longrightarrow>
                  top1_continuous_map_on A (subspace_topology E TE A) Y TY f"
                using Theorem_18_2[OF hTE hTY hTY] by (by100 blast)
              thus ?thesis using hq_cont hW_sub_E by (by100 blast)
            qed
            have hh_cont_W: "top1_continuous_map_on W (subspace_topology E TE W) Y TY ?h"
            proof -
              have hp_W_U: "top1_continuous_map_on W (subspace_topology E TE W)
                  U'' (subspace_topology B TB U'') p"
                using h\<W>p_homeo hW_mem unfolding top1_homeomorphism_on_def by (by100 blast)
              have hinv_U_V1: "top1_continuous_map_on U'' (subspace_topology B TB U'')
                  V1 (subspace_topology Y TY V1) (inv_into V1 r)"
                using homeomorphism_inverse[OF hV1_homeo]
                unfolding top1_homeomorphism_on_def by (by100 blast)
              have hcomp0: "top1_continuous_map_on W (subspace_topology E TE W)
                  V1 (subspace_topology Y TY V1) (inv_into V1 r \<circ> p)"
                by (rule top1_continuous_map_on_comp[OF hp_W_U hinv_U_V1])
              have hcomp_eq: "(inv_into V1 r \<circ> p) = (\<lambda>e. inv_into V1 r (p e))"
                unfolding comp_def by (by100 simp)
              have hcomp: "top1_continuous_map_on W (subspace_topology E TE W)
                  V1 (subspace_topology Y TY V1) (\<lambda>e. inv_into V1 r (p e))"
                using hcomp0 hcomp_eq by (by100 simp)
              \<comment> \<open>Lift from V1-subspace to Y: direct proof.\<close>
              have hV1_sub_Y: "V1 \<subseteq> Y" using hV1_open unfolding openin_on_def by (by100 blast)
              show ?thesis unfolding top1_continuous_map_on_def
              proof (intro conjI ballI)
                fix e' assume "e' \<in> W"
                thus "inv_into V1 r (p e') \<in> Y" using hh_V1 \<open>e' \<in> W\<close> hV1_sub_Y by (by100 blast)
              next
                fix V assume "V \<in> TY"
                have "V \<inter> V1 \<in> subspace_topology Y TY V1"
                  using \<open>V \<in> TY\<close> unfolding subspace_topology_def by (by100 blast)
                hence "{e' \<in> W. inv_into V1 r (p e') \<in> V \<inter> V1} \<in> subspace_topology E TE W"
                  using hcomp unfolding top1_continuous_map_on_def by (by100 blast)
                moreover have "{e' \<in> W. inv_into V1 r (p e') \<in> V} =
                    {e' \<in> W. inv_into V1 r (p e') \<in> V \<inter> V1}"
                  using hh_V1 by (by100 blast)
                ultimately show "{e' \<in> W. inv_into V1 r (p e') \<in> V} \<in> subspace_topology E TE W"
                  by (by100 simp)
              qed
            qed
            have hrq_eq_rh: "\<forall>e'\<in>W. r (q e') = r (?h e')"
            proof (intro ballI)
              fix e' assume "e' \<in> W"
              have "e' \<in> E" using \<open>e' \<in> W\<close> hW_sub_E by (by100 blast)
              have "r (q e') = p e'" using hq_rp \<open>e' \<in> E\<close> by (by100 blast)
              have "r (?h e') = p e'" using hrh \<open>e' \<in> W\<close> by (by100 blast)
              show "r (q e') = r (?h e')" using \<open>r (q e') = p e'\<close> \<open>r (?h e') = p e'\<close> by (by100 simp)
            qed
            have hq_eq_h: "\<forall>e'\<in>W. q e' = ?h e'"
              using covering_lift_unique_connected[OF assms(6) hW_top hTB hTY hW_conn
                  hq_cont_W hh_cont_W hrq_eq_rh he0_W(1) \<open>?h e0 = q e0\<close>[symmetric]]
              by (by100 blast)
            have "q e = ?h e" using hq_eq_h he_W by (by100 blast)
            thus "q e \<in> V1" using hh_V1 he_W by (by100 simp)
          qed
          show "{x \<in> E. q x \<in> V1} = \<Union>?\<V>q"
          proof (rule set_eqI, rule iffI)
            fix x assume "x \<in> {x \<in> E. q x \<in> V1}"
            hence hx: "x \<in> E" "q x \<in> V1" by (by100 blast)+
            have "r (q x) \<in> U''"
            proof -
              have "q x \<in> V1" by (rule hx(2))
              hence "q x \<in> \<Union>\<W>r" using hV1(1) by (by100 blast)
              hence "q x \<in> {x\<in>Y. r x \<in> U''}" using h\<W>r_union by (by100 simp)
              thus ?thesis by (by100 blast)
            qed
            hence "p x \<in> U''" using hq_rp hx(1) by (by100 simp)
            hence "x \<in> {x\<in>E. p x \<in> U''}" using hx(1) by (by100 blast)
            hence "x \<in> \<Union>\<W>p" using h\<W>p_union by (by100 simp)
            then obtain W where "W \<in> \<W>p" "x \<in> W" by (by100 blast)
            moreover have "W \<in> ?\<V>q" using \<open>W \<in> \<W>p\<close> \<open>x \<in> W\<close> hx(2) by (by100 blast)
            ultimately show "x \<in> \<Union>?\<V>q" by (by100 blast)
          next
            fix x assume "x \<in> \<Union>?\<V>q"
            then obtain W where "W \<in> ?\<V>q" "x \<in> W" by (by100 blast)
            hence "x \<in> E" using h\<W>p_open unfolding openin_on_def by (by100 blast)
            moreover have "q x \<in> V1" using hW_all_V1 \<open>W \<in> ?\<V>q\<close> \<open>x \<in> W\<close> by (by100 blast)
            ultimately show "x \<in> {x \<in> E. q x \<in> V1}" by (by100 blast)
          qed
          show "\<forall>W\<in>?\<V>q. top1_homeomorphism_on W (subspace_topology E TE W)
              V1 (subspace_topology Y TY V1) q"
          proof (intro ballI)
            fix W assume hWq: "W \<in> ?\<V>q"
            have hW_mem: "W \<in> \<W>p" using hWq by (by100 blast)
            \<comment> \<open>Re-derive q = h on W.\<close>
            have hW_sub_E: "W \<subseteq> E" using hW_mem h\<W>p_open unfolding openin_on_def by (by100 blast)
            have hq_eq_h_W: "\<forall>e'\<in>W. q e' = inv_into V1 r (p e')"
              using hq_eq_h_all hWq by (by100 blast)
            \<comment> \<open>Composition of homeomorphisms: (inv_into V1 r) \<circ> p: W \<cong> V1.\<close>
            have hp_homeo_W: "top1_homeomorphism_on W (subspace_topology E TE W)
                U'' (subspace_topology B TB U'') p"
              using h\<W>p_homeo hW_mem by (by100 blast)
            have hinv_homeo: "top1_homeomorphism_on U'' (subspace_topology B TB U'')
                V1 (subspace_topology Y TY V1) (inv_into V1 r)"
              by (rule homeomorphism_inverse[OF hV1_homeo])
            have hcomp_homeo: "top1_homeomorphism_on W (subspace_topology E TE W)
                V1 (subspace_topology Y TY V1) (inv_into V1 r \<circ> p)"
              by (rule homeomorphism_compose[OF hp_homeo_W hinv_homeo])
            \<comment> \<open>q agrees with inv_into V1 r \<circ> p on W, so transfer homeomorphism.\<close>
            have hq_eq_comp: "\<forall>x\<in>W. q x = (inv_into V1 r \<circ> p) x"
              using hq_eq_h_W by (by100 simp)
            \<comment> \<open>Transfer: same function on carrier \<Rightarrow> same homeomorphism.\<close>
            show "top1_homeomorphism_on W (subspace_topology E TE W)
                V1 (subspace_topology Y TY V1) q"
            proof -
              let ?g = "inv_into V1 r \<circ> p"
              \<comment> \<open>bij_betw: q and g agree on W, g is bijective W \<rightarrow> V1.\<close>
              have hg_bij: "bij_betw ?g W V1"
                using hcomp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
              have hq_bij: "bij_betw q W V1"
              proof -
                have "q ` W = ?g ` W"
                proof (rule set_eqI, rule iffI)
                  fix y assume "y \<in> q ` W"
                  then obtain w where "w \<in> W" "y = q w" by (by100 blast)
                  hence "y = ?g w" using hq_eq_comp by (by100 blast)
                  thus "y \<in> ?g ` W" using \<open>w \<in> W\<close> by (by100 blast)
                next
                  fix y assume "y \<in> ?g ` W"
                  then obtain w where "w \<in> W" "y = ?g w" by (by100 blast)
                  have "q w = ?g w" using hq_eq_comp \<open>w \<in> W\<close> by (by100 blast)
                  hence "y = q w" using \<open>y = ?g w\<close> by (by100 simp)
                  thus "y \<in> q ` W" using \<open>w \<in> W\<close> by (by100 blast)
                qed
                have "inj_on q W"
                proof (rule inj_onI)
                  fix x y assume "x \<in> W" "y \<in> W" "q x = q y"
                  have "?g x = ?g y"
                    using hq_eq_comp \<open>x \<in> W\<close> \<open>y \<in> W\<close> \<open>q x = q y\<close> by (by100 simp)
                  have "inj_on ?g W" using hg_bij unfolding bij_betw_def by (by100 blast)
                  thus "x = y" using \<open>x \<in> W\<close> \<open>y \<in> W\<close> \<open>?g x = ?g y\<close>
                    unfolding inj_on_def by (by100 blast)
                qed
                thus ?thesis using hg_bij \<open>q ` W = ?g ` W\<close>
                  unfolding bij_betw_def by (by100 blast)
              qed
              \<comment> \<open>Continuity: q and g agree on W.\<close>
              have hq_cont_WV1: "top1_continuous_map_on W (subspace_topology E TE W)
                  V1 (subspace_topology Y TY V1) q"
                using iffD2[OF top1_continuous_map_on_cong[of W q ?g]] hq_eq_comp
                  hcomp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
              \<comment> \<open>Inverse continuity: inv_into W q agrees with inv_into W g on V1.\<close>
              have hinv_cont: "top1_continuous_map_on V1 (subspace_topology Y TY V1)
                  W (subspace_topology E TE W) (inv_into W q)"
              proof -
                have hg_inv_cont: "top1_continuous_map_on V1 (subspace_topology Y TY V1)
                    W (subspace_topology E TE W) (inv_into W ?g)"
                  using hcomp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
                have "\<forall>y\<in>V1. inv_into W q y = inv_into W ?g y"
                proof (intro ballI)
                  fix y assume "y \<in> V1"
                  have "y \<in> q ` W" using hq_bij \<open>y \<in> V1\<close> unfolding bij_betw_def by (by100 blast)
                  then obtain w where "w \<in> W" "q w = y" by (by100 blast)
                  have hinj_q: "inj_on q W" using hq_bij unfolding bij_betw_def by (by100 blast)
                  have "inv_into W q (q w) = w" by (rule inv_into_f_f[OF hinj_q \<open>w \<in> W\<close>])
                  hence "inv_into W q y = w" using \<open>q w = y\<close> by (by100 simp)
                  have "q w = ?g w" using hq_eq_comp \<open>w \<in> W\<close> by (by100 blast)
                  hence "?g w = y" using \<open>q w = y\<close> by (by100 simp)
                  have hinj_g: "inj_on ?g W" using hg_bij unfolding bij_betw_def by (by100 blast)
                  have "inv_into W ?g (?g w) = w" by (rule inv_into_f_f[OF hinj_g \<open>w \<in> W\<close>])
                  hence "inv_into W ?g y = w" using \<open>?g w = y\<close> by (by100 simp)
                  thus "inv_into W q y = inv_into W ?g y"
                    using \<open>inv_into W q y = w\<close> by (by100 simp)
                qed
                thus ?thesis
                  using iffD2[OF top1_continuous_map_on_cong[of V1 "inv_into W q" "inv_into W ?g"]]
                    hg_inv_cont by (by100 blast)
              qed
              have hW_top_loc: "is_topology_on W (subspace_topology E TE W)"
                using hp_homeo_W unfolding top1_homeomorphism_on_def by (by100 blast)
              have hV1_top: "is_topology_on V1 (subspace_topology Y TY V1)"
                using hV1_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
              show ?thesis unfolding top1_homeomorphism_on_def
                using hW_top_loc hV1_top hq_bij hq_cont_WV1 hinv_cont by (by100 blast)
            qed
          qed
        qed
      qed
    qed
  qed
  show ?thesis
  proof (rule exI[of _ q])
    show "top1_covering_map_on E TE Y TY q \<and> (\<forall>e\<in>E. r (q e) = p e)"
      unfolding top1_covering_map_on_def using hq_cont hq_surj hq_cov hq_rp by (by100 blast)
  qed
qed

text \<open>Strict version of Theorem_80_3 — same statement but with simply_connected_strict.\<close>
corollary Theorem_80_3_universal_strict:
  assumes "top1_simply_connected_strict E TE"
      and "is_topology_on_strict B TB"
      and "is_topology_on_strict Y TY"
      and "top1_covering_map_on E TE B TB p"
      and "top1_covering_map_on Y TY B TB r"
      and "top1_locally_path_connected_on E TE"
      and "top1_path_connected_on Y TY"
  shows "\<exists>q. top1_covering_map_on E TE Y TY q \<and> (\<forall>e\<in>E. r (q e) = p e)"
  using Theorem_80_3_universal[of E TE B TB Y TY p r]
    top1_simply_connected_strict_imp[OF assms(1)]
    top1_simply_connected_strict_is_topology_strict[OF assms(1)]
    assms(2-7) by (by100 blast)

section \<open>*\<S>81 Covering Transformations\<close>

text \<open>A covering transformation of p : E \<rightarrow> B is a homeomorphism h : E \<rightarrow> E
  with p \<circ> h = p. We require h = id outside E so that covering transformations
  form a group under (total) function composition.\<close>
definition top1_covering_transformation_on :: "'e set \<Rightarrow> 'e set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> ('e \<Rightarrow> 'e) \<Rightarrow> bool" where
  "top1_covering_transformation_on E TE B TB p h \<longleftrightarrow>
     top1_homeomorphism_on E TE E TE h \<and> (\<forall>e\<in>E. p (h e) = p e)
     \<and> (\<forall>e. e \<notin> E \<longrightarrow> h e = e)"

text \<open>Reviewer-requested: deck transformations are homeomorphisms (immediate from definition).\<close>
lemma deck_transformation_homeomorphism:
  assumes "top1_covering_transformation_on E TE B TB p h"
  shows "top1_homeomorphism_on E TE E TE h"
  using assms unfolding top1_covering_transformation_on_def by (by100 blast)

text \<open>Reviewer-requested: deck transformations form a group under composition.\<close>
lemma deck_transformations_group:
  assumes "top1_covering_map_on E TE B TB p"
      and "is_topology_on_strict E TE"
  shows "\<exists>eC invgC. top1_is_group_on
      {h. top1_covering_transformation_on E TE B TB p h}
      (\<lambda>h k e. h (k e)) eC invgC"
proof -
  let ?Cov = "{h. top1_covering_transformation_on E TE B TB p h}"
  let ?mul = "\<lambda>h k e. h (k e)"
  \<comment> \<open>Identity: id is a covering transformation.\<close>
  have hTE: "is_topology_on E TE" using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>id is continuous E \<rightarrow> E.\<close>
  have hid_cont: "top1_continuous_map_on E TE E TE id"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix x assume "x \<in> E" thus "id x \<in> E" by (by100 simp)
  next
    fix V assume hV: "V \<in> TE"
    have "V \<subseteq> E" using assms(2) hV unfolding is_topology_on_strict_def by (by100 blast)
    hence "{x \<in> E. id x \<in> V} = V" by (by100 auto)
    thus "{x \<in> E. id x \<in> V} \<in> TE" using hV by (by100 simp)
  qed
  have hid_homeo: "top1_homeomorphism_on E TE E TE id"
    unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on E TE" by (rule hTE)
    show "is_topology_on E TE" by (rule hTE)
    show "bij_betw id E E" by (by100 simp)
    show "top1_continuous_map_on E TE E TE id" by (rule hid_cont)
    show "top1_continuous_map_on E TE E TE (inv_into E id)"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x assume "x \<in> E" thus "inv_into E id x \<in> E"
        using inv_into_f_f[of id E, simplified] by (by100 simp)
    next
      fix V assume hV: "V \<in> TE"
      have "V \<subseteq> E" using assms(2) hV unfolding is_topology_on_strict_def by (by100 blast)
      hence "{x \<in> E. inv_into E id x \<in> V} = V"
        using inv_into_f_f[of id E, simplified] by (by100 auto)
      thus "{x \<in> E. inv_into E id x \<in> V} \<in> TE" using hV by (by100 simp)
    qed
  qed
  have hid_ct: "top1_covering_transformation_on E TE B TB p id"
    unfolding top1_covering_transformation_on_def using hid_homeo by (by100 simp)
  \<comment> \<open>Composition of CTs is a CT; inverse CT is a CT.\<close>
  have hmul_closed: "\<And>h k. top1_covering_transformation_on E TE B TB p h \<Longrightarrow>
      top1_covering_transformation_on E TE B TB p k \<Longrightarrow>
      top1_covering_transformation_on E TE B TB p (\<lambda>e. h (k e))"
  proof -
    fix h k assume hh: "top1_covering_transformation_on E TE B TB p h"
      and hk: "top1_covering_transformation_on E TE B TB p k"
    have hh_homeo: "top1_homeomorphism_on E TE E TE h"
      using hh unfolding top1_covering_transformation_on_def by (by100 blast)
    have hk_homeo: "top1_homeomorphism_on E TE E TE k"
      using hk unfolding top1_covering_transformation_on_def by (by100 blast)
    have hh_p: "\<forall>e\<in>E. p (h e) = p e"
      using hh unfolding top1_covering_transformation_on_def by (by100 blast)
    have hk_p: "\<forall>e\<in>E. p (k e) = p e"
      using hk unfolding top1_covering_transformation_on_def by (by100 blast)
    have hh_out: "\<forall>e. e \<notin> E \<longrightarrow> h e = e"
      using hh unfolding top1_covering_transformation_on_def by (by100 blast)
    have hk_out: "\<forall>e. e \<notin> E \<longrightarrow> k e = e"
      using hk unfolding top1_covering_transformation_on_def by (by100 blast)
    \<comment> \<open>Composition h\<circ>k is homeomorphism E \<rightarrow> E.\<close>
    have hcomp_homeo: "top1_homeomorphism_on E TE E TE (\<lambda>e. h (k e))"
    proof -
      have "top1_homeomorphism_on E TE E TE (h \<circ> k)"
        by (rule homeomorphism_compose[OF hk_homeo hh_homeo])
      moreover have "(h \<circ> k) = (\<lambda>e. h (k e))" unfolding comp_def by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>p \<circ> (h\<circ>k) = p: for e \<in> E, p(h(k(e))) = p(k(e)) = p(e).\<close>
    have hcomp_p: "\<forall>e\<in>E. p (h (k e)) = p e"
    proof (intro ballI)
      fix e assume he: "e \<in> E"
      have "k e \<in> E" using hk_homeo he unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      hence "p (h (k e)) = p (k e)" using hh_p by (by100 blast)
      also have "p (k e) = p e" using hk_p he by (by100 blast)
      finally show "p (h (k e)) = p e" .
    qed
    \<comment> \<open>Outside E: h(k(e)) = h(e) = e.\<close>
    have hcomp_out: "\<forall>e. e \<notin> E \<longrightarrow> h (k e) = e"
    proof (intro allI impI)
      fix e assume he: "e \<notin> E"
      have "k e = e" using hk_out he by (by100 blast)
      hence "h (k e) = h e" by (by100 simp)
      also have "h e = e" using hh_out he by (by100 blast)
      finally show "h (k e) = e" .
    qed
    show "top1_covering_transformation_on E TE B TB p (\<lambda>e. h (k e))"
      unfolding top1_covering_transformation_on_def
      using hcomp_homeo hcomp_p hcomp_out by (by100 blast)
  qed
  \<comment> \<open>Use modified inverse: identity outside E, inv\_into inside E.\<close>
  let ?invC = "\<lambda>h. (\<lambda>e. if e \<in> E then inv_into E h e else e)"
  have hinv: "\<And>h. top1_covering_transformation_on E TE B TB p h \<Longrightarrow>
      top1_covering_transformation_on E TE B TB p (?invC h)"
  proof -
    fix h assume hh: "top1_covering_transformation_on E TE B TB p h"
    have hh_homeo: "top1_homeomorphism_on E TE E TE h"
      using hh unfolding top1_covering_transformation_on_def by (by100 blast)
    have hh_p: "\<forall>e\<in>E. p (h e) = p e"
      using hh unfolding top1_covering_transformation_on_def by (by100 blast)
    have hh_out: "\<forall>e. e \<notin> E \<longrightarrow> h e = e"
      using hh unfolding top1_covering_transformation_on_def by (by100 blast)
    have hbij: "bij_betw h E E" using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    have hinj: "inj_on h E" using hbij unfolding bij_betw_def by (by100 blast)
    have hsurj: "h ` E = E" using hbij unfolding bij_betw_def by (by100 blast)
    \<comment> \<open>Condition 1: homeomorphism (via agree-on-E with inv\_into E h).\<close>
    have hinv_raw: "top1_homeomorphism_on E TE E TE (inv_into E h)"
      by (rule homeomorphism_inverse[OF hh_homeo])
    have hagree: "\<forall>e\<in>E. (?invC h) e = inv_into E h e" by (by100 simp)
    have h_homeo: "top1_homeomorphism_on E TE E TE (?invC h)"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      show "is_topology_on E TE" by (rule hTE)
      show "is_topology_on E TE" by (rule hTE)
      \<comment> \<open>bij\_betw: since ?invC h agrees with inv\_into E h on E.\<close>
      have hbij_raw: "bij_betw (inv_into E h) E E"
        using hinv_raw unfolding top1_homeomorphism_on_def by (by100 blast)
      show "bij_betw (?invC h) E E"
      proof -
        have "inj_on (?invC h) E"
        proof (rule inj_onI)
          fix x y assume hx: "x \<in> E" and hy: "y \<in> E"
            and heq: "(?invC h) x = (?invC h) y"
          from heq hx hy have "inv_into E h x = inv_into E h y" by (by100 simp)
          thus "x = y" using hbij_raw hx hy
            unfolding bij_betw_def inj_on_def by (by100 blast)
        qed
        moreover have "(?invC h) ` E = E"
        proof -
          have "\<forall>e\<in>E. (?invC h) e = inv_into E h e" by (by100 simp)
          hence "(?invC h) ` E = inv_into E h ` E" by (by100 force)
          also have "\<dots> = E" using hbij_raw unfolding bij_betw_def by (by100 blast)
          finally show ?thesis .
        qed
        ultimately show ?thesis unfolding bij_betw_def by (by100 blast)
      qed
      \<comment> \<open>Continuity: via cong with inv\_into E h.\<close>
      have hcont_raw: "top1_continuous_map_on E TE E TE (inv_into E h)"
        using hinv_raw unfolding top1_homeomorphism_on_def by (by100 blast)
      show "top1_continuous_map_on E TE E TE (?invC h)"
        using top1_continuous_map_on_cong[of E "?invC h" "inv_into E h"] hagree hcont_raw
        by (by100 blast)
      \<comment> \<open>Inverse continuity: inv\_into E (?invC h) agrees with h on E.\<close>
      show "top1_continuous_map_on E TE E TE (inv_into E (?invC h))"
      proof -
        \<comment> \<open>inv\_into E (?invC h) agrees with h on E.\<close>
        have "\<forall>e\<in>E. inv_into E (?invC h) e = h e"
        proof (intro ballI)
          fix e assume he: "e \<in> E"
          have hhe: "h e \<in> E" using hsurj he by (by100 blast)
          have "(?invC h) (h e) = inv_into E h (h e)" using hhe by (by100 simp)
          also have "\<dots> = e" by (rule inv_into_f_f[OF hinj he])
          finally have "(?invC h) (h e) = e" .
          moreover have "h e \<in> E" by (rule hhe)
          moreover have "inj_on (?invC h) E"
          proof (rule inj_onI)
            fix x y assume hx: "x \<in> E" and hy: "y \<in> E"
              and heq: "(?invC h) x = (?invC h) y"
            from heq hx hy have "inv_into E h x = inv_into E h y" by (by100 simp)
            thus "x = y" using hbij_raw hx hy
              unfolding bij_betw_def inj_on_def by (by100 blast)
          qed
          ultimately show "inv_into E (?invC h) e = h e"
          proof -
            assume h1: "(?invC h) (h e) = e" and h2: "h e \<in> E"
               and h3: "inj_on (?invC h) E"
            have "inv_into E (?invC h) ((?invC h) (h e)) = h e"
              by (rule inv_into_f_f[OF h3 h2])
            thus ?thesis using h1 by (by100 simp)
          qed
        qed
        hence "top1_continuous_map_on E TE E TE (inv_into E (?invC h))
             \<longleftrightarrow> top1_continuous_map_on E TE E TE h"
          by (rule top1_continuous_map_on_cong)
        moreover have "top1_continuous_map_on E TE E TE h"
          using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
    qed
    \<comment> \<open>Condition 2: p-preservation.\<close>
    have h_p: "\<forall>e\<in>E. p ((?invC h) e) = p e"
    proof (intro ballI)
      fix e assume he: "e \<in> E"
      have "e \<in> h ` E" using he hsurj by (by100 blast)
      have hinv_E: "inv_into E h e \<in> E" using inv_into_into[OF \<open>e \<in> h ` E\<close>] by (by100 blast)
      have "(?invC h) e = inv_into E h e" using he by (by100 simp)
      moreover have "p (inv_into E h e) = p e"
      proof -
        have "p (h (inv_into E h e)) = p (inv_into E h e)"
          using hh_p hinv_E by (by100 blast)
        moreover have "h (inv_into E h e) = e"
          using f_inv_into_f[OF \<open>e \<in> h ` E\<close>] by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      ultimately show "p ((?invC h) e) = p e" by (by100 simp)
    qed
    \<comment> \<open>Condition 3: identity outside E (trivial from if-then-else).\<close>
    have h_out: "\<forall>e. e \<notin> E \<longrightarrow> (?invC h) e = e" by (by100 simp)
    show "top1_covering_transformation_on E TE B TB p (?invC h)"
      unfolding top1_covering_transformation_on_def
      using h_homeo h_p h_out by (by100 blast)
  qed
  \<comment> \<open>Group axioms: associativity, identity, inverse.\<close>
  have hassoc: "\<forall>h\<in>?Cov. \<forall>k\<in>?Cov. \<forall>l\<in>?Cov.
      ?mul (?mul h k) l = ?mul h (?mul k l)"
    by (by100 blast)
  have hident: "\<forall>h\<in>?Cov. ?mul id h = h \<and> ?mul h id = h"
    by (by100 auto)
  have hinverse: "\<forall>h\<in>?Cov. ?mul (?invC h) h = id \<and> ?mul h (?invC h) = id"
  proof (intro ballI conjI ext)
    fix h e assume hh: "h \<in> ?Cov"
    have hh_homeo: "top1_homeomorphism_on E TE E TE h"
      using hh unfolding top1_covering_transformation_on_def by (by100 blast)
    have hh_out: "\<forall>e. e \<notin> E \<longrightarrow> h e = e"
      using hh unfolding top1_covering_transformation_on_def by (by100 blast)
    have hbij: "bij_betw h E E" using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    have hinj: "inj_on h E" using hbij unfolding bij_betw_def by (by100 blast)
    have hsurj: "h ` E = E" using hbij unfolding bij_betw_def by (by100 blast)
    \<comment> \<open>Left inverse: (?invC h)(h e) = e.\<close>
    show "?mul (?invC h) h e = id e"
    proof (cases "e \<in> E")
      case True
      have "h e \<in> E" using True hsurj by (by100 blast)
      hence "?mul (?invC h) h e = inv_into E h (h e)" by (by100 simp)
      also have "\<dots> = e" by (rule inv_into_f_f[OF hinj True])
      finally show ?thesis by (by100 simp)
    next
      case False
      hence "h e = e" using hh_out by (by100 blast)
      hence "?mul (?invC h) h e = (if e \<in> E then inv_into E h e else e)" by (by100 simp)
      also have "\<dots> = e" using False by (by100 simp)
      finally show ?thesis by (by100 simp)
    qed
  next
    fix h e assume hh: "h \<in> ?Cov"
    have hh_homeo: "top1_homeomorphism_on E TE E TE h"
      using hh unfolding top1_covering_transformation_on_def by (by100 blast)
    have hh_out: "\<forall>e. e \<notin> E \<longrightarrow> h e = e"
      using hh unfolding top1_covering_transformation_on_def by (by100 blast)
    have hbij: "bij_betw h E E" using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    have hsurj: "h ` E = E" using hbij unfolding bij_betw_def by (by100 blast)
    \<comment> \<open>Right inverse: h((?invC h) e) = e.\<close>
    show "?mul h (?invC h) e = id e"
    proof (cases "e \<in> E")
      case True
      have "e \<in> h ` E" using True hsurj by (by100 blast)
      have "?mul h (?invC h) e = h (inv_into E h e)" using True by (by100 simp)
      also have "\<dots> = e" using f_inv_into_f[OF \<open>e \<in> h ` E\<close>] by (by100 blast)
      finally show ?thesis by (by100 simp)
    next
      case False
      hence "?mul h (?invC h) e = h e" by (by100 simp)
      also have "\<dots> = e" using hh_out False by (by100 blast)
      finally show ?thesis by (by100 simp)
    qed
  qed
  show ?thesis
    apply (rule exI[of _ id], rule exI[of _ ?invC])
    unfolding top1_is_group_on_def
    using hid_ct hmul_closed hinv hassoc hident hinverse by (by100 blast)
qed

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
  have hCov_group: "\<exists>eC invgC. top1_is_group_on ?Cov (\<lambda>h k e. h (k e)) eC invgC"
  proof -
    let ?mul = "\<lambda>h k e. h (k e)" \<comment> \<open>= \<circ> (function composition)\<close>
    let ?eC = "id :: 'e \<Rightarrow> 'e"
    let ?invC = "\<lambda>h e. if e \<in> E then inv_into E h e else e"
    have hTE: "is_topology_on E TE"
      using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    \<comment> \<open>id is a covering transformation.\<close>
    have hid_homeo: "top1_homeomorphism_on E TE E TE id"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      show "is_topology_on E TE" by (rule hTE)
      show "is_topology_on E TE" by (rule hTE)
      show "bij_betw id E E" by (by100 simp)
      show "top1_continuous_map_on E TE E TE id" using top1_continuous_map_on_id[OF hTE] .
      have hinv_id: "\<forall>x\<in>E. inv_into E id x = id x"
      proof (intro ballI)
        fix x assume "x \<in> E"
        thus "inv_into E id x = id x" using inv_into_f_f[of id E x] by (by100 simp)
      qed
      show "top1_continuous_map_on E TE E TE (inv_into E id)"
        using top1_continuous_map_on_cong[of E "inv_into E id" id]
          hinv_id top1_continuous_map_on_id[OF hTE] by (by100 blast)
    qed
    have hid_cov: "?eC \<in> ?Cov"
      using hid_homeo unfolding top1_covering_transformation_on_def by (by100 simp)
    \<comment> \<open>Composition of covering transformations.\<close>
    have hcomp_cov: "\<forall>h\<in>?Cov. \<forall>k\<in>?Cov. ?mul h k \<in> ?Cov"
    proof (intro ballI)
      fix h k assume hh: "h \<in> ?Cov" and hk: "k \<in> ?Cov"
      have hh_homeo: "top1_homeomorphism_on E TE E TE h"
        using hh unfolding top1_covering_transformation_on_def by (by100 blast)
      have hk_homeo: "top1_homeomorphism_on E TE E TE k"
        using hk unfolding top1_covering_transformation_on_def by (by100 blast)
      have hh_p: "\<forall>e\<in>E. p (h e) = p e"
        using hh unfolding top1_covering_transformation_on_def by (by100 blast)
      have hk_p: "\<forall>e\<in>E. p (k e) = p e"
        using hk unfolding top1_covering_transformation_on_def by (by100 blast)
      have hh_out: "\<forall>e. e \<notin> E \<longrightarrow> h e = e"
        using hh unfolding top1_covering_transformation_on_def by (by100 blast)
      have hk_out: "\<forall>e. e \<notin> E \<longrightarrow> k e = e"
        using hk unfolding top1_covering_transformation_on_def by (by100 blast)
      have "top1_homeomorphism_on E TE E TE (h \<circ> k)"
        by (rule homeomorphism_compose[OF hk_homeo hh_homeo])
      moreover have "\<forall>e\<in>E. p ((h \<circ> k) e) = p e"
      proof (intro ballI)
        fix e assume "e \<in> E"
        have "k e \<in> E"
        proof -
          have "bij_betw k E E" using hk_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          thus ?thesis using \<open>e \<in> E\<close> unfolding bij_betw_def by (by100 blast)
        qed
        thus "p ((h \<circ> k) e) = p e" using hh_p hk_p \<open>e \<in> E\<close> by (by100 simp)
      qed
      moreover have "\<forall>e. e \<notin> E \<longrightarrow> (h \<circ> k) e = e"
        using hh_out hk_out by (by100 simp)
      moreover have "?mul h k = h \<circ> k" by (rule ext) (by100 simp)
      ultimately show "?mul h k \<in> ?Cov"
        unfolding top1_covering_transformation_on_def by (by100 simp)
    qed
    \<comment> \<open>Inverse of covering transformation.\<close>
    have hinv_cov: "\<forall>h\<in>?Cov. ?invC h \<in> ?Cov"
    proof (intro ballI)
      fix h assume hh: "h \<in> ?Cov"
      have hh_homeo: "top1_homeomorphism_on E TE E TE h"
        using hh unfolding top1_covering_transformation_on_def by (by100 blast)
      have hh_p: "\<forall>e\<in>E. p (h e) = p e"
        using hh unfolding top1_covering_transformation_on_def by (by100 blast)
      have hh_out: "\<forall>e. e \<notin> E \<longrightarrow> h e = e"
        using hh unfolding top1_covering_transformation_on_def by (by100 blast)
      \<comment> \<open>inv_into E h is the inverse homeomorphism.\<close>
      have hinv_homeo_raw: "top1_homeomorphism_on E TE E TE (inv_into E h)"
        by (rule homeomorphism_inverse[OF hh_homeo])
      \<comment> \<open>The modified inverse ?invC h agrees with inv_into E h on E.\<close>
      have hagree: "\<forall>e\<in>E. (\<lambda>e. if e \<in> E then inv_into E h e else e) e = inv_into E h e"
        by (by100 simp)
      \<comment> \<open>Transfer bij_betw: functions agreeing on E have the same bij_betw on E.\<close>
      have hbij_raw: "bij_betw (inv_into E h) E E"
        using hinv_homeo_raw unfolding top1_homeomorphism_on_def by (by100 blast)
      have hbij: "bij_betw (\<lambda>e. if e \<in> E then inv_into E h e else e) E E"
      proof -
        have "inj_on (\<lambda>e. if e \<in> E then inv_into E h e else e) E"
        proof (rule inj_onI)
          fix x y assume hx: "x \<in> E" and hy: "y \<in> E"
            and heq: "(if x \<in> E then inv_into E h x else x) = (if y \<in> E then inv_into E h y else y)"
          from heq hx hy have "inv_into E h x = inv_into E h y" by (by100 simp)
          thus "x = y" using inj_on_eq_iff[of "inv_into E h" E x y] hbij_raw hx hy
            unfolding bij_betw_def by (by100 blast)
        qed
        moreover have "(\<lambda>e. if e \<in> E then inv_into E h e else e) ` E = E"
        proof -
          have "(inv_into E h) ` E = E" using hbij_raw unfolding bij_betw_def by (by100 blast)
          moreover have "\<forall>e\<in>E. (\<lambda>e. if e \<in> E then inv_into E h e else e) e = inv_into E h e"
            by (by100 simp)
          ultimately show ?thesis by (by100 force)
        qed
        ultimately show ?thesis unfolding bij_betw_def by (by100 blast)
      qed
      \<comment> \<open>Transfer continuity via cong.\<close>
      have hcont_raw: "top1_continuous_map_on E TE E TE (inv_into E h)"
        using hinv_homeo_raw unfolding top1_homeomorphism_on_def by (by100 blast)
      have hcont: "top1_continuous_map_on E TE E TE (\<lambda>e. if e \<in> E then inv_into E h e else e)"
        using top1_continuous_map_on_cong[of E "\<lambda>e. if e \<in> E then inv_into E h e else e"
              "inv_into E h"] hagree hcont_raw by (by100 blast)
      \<comment> \<open>Inverse of ?invC h on E equals h.\<close>
      have hbij_h: "bij_betw h E E"
        using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have hinj_h: "inj_on h E"
        using hbij_h unfolding bij_betw_def by (by100 blast)
      have hinj_mod: "inj_on (\<lambda>e. if e \<in> E then inv_into E h e else e) E"
      proof (rule inj_onI)
        fix x y assume hx: "x \<in> E" and hy: "y \<in> E"
          and heqm: "(if x \<in> E then inv_into E h x else x) = (if y \<in> E then inv_into E h y else y)"
        from heqm hx hy have "inv_into E h x = inv_into E h y" by (by100 simp)
        thus "x = y" using inj_on_eq_iff[of "inv_into E h" E x y] hbij_raw hx hy
          unfolding bij_betw_def by (by100 blast)
      qed
      have hinv_inv_agree: "\<forall>e\<in>E. inv_into E (\<lambda>e. if e \<in> E then inv_into E h e else e) e = h e"
      proof (intro ballI)
        fix e assume he: "e \<in> E"
        have hhe_E: "h e \<in> E" using hbij_h he unfolding bij_betw_def by (by100 blast)
        have "(\<lambda>e. if e \<in> E then inv_into E h e else e) (h e)
            = inv_into E h (h e)" using hhe_E by (by100 simp)
        also have "\<dots> = e" by (rule inv_into_f_f[OF hinj_h he])
        finally have hfeq: "(\<lambda>e. if e \<in> E then inv_into E h e else e) (h e) = e" .
        let ?g = "\<lambda>e. if e \<in> E then inv_into E h e else e"
        have "inv_into E ?g e = h e"
          using inv_into_f_eq[OF hinj_mod hhe_E hfeq] by (by100 simp)
        thus "inv_into E (\<lambda>e. if e \<in> E then inv_into E h e else e) e = h e" by (by100 simp)
      qed
      have hcont_h: "top1_continuous_map_on E TE E TE h"
        using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have hcont_inv: "top1_continuous_map_on E TE E TE
          (inv_into E (\<lambda>e. if e \<in> E then inv_into E h e else e))"
        using top1_continuous_map_on_cong[of E
              "inv_into E (\<lambda>e. if e \<in> E then inv_into E h e else e)" h]
              hinv_inv_agree hcont_h by (by100 blast)
      \<comment> \<open>Assemble homeomorphism.\<close>
      have hinv_homeo: "top1_homeomorphism_on E TE E TE (\<lambda>e. if e \<in> E then inv_into E h e else e)"
        unfolding top1_homeomorphism_on_def using hTE hbij hcont hcont_inv by (by100 blast)
      \<comment> \<open>p-preservation on E (same as before, since ?invC h = inv_into E h on E).\<close>
      moreover have "\<forall>e\<in>E. p ((\<lambda>e. if e \<in> E then inv_into E h e else e) e) = p e"
      proof (intro ballI)
        fix e assume "e \<in> E"
        have hsurj_loc: "h ` E = E" using hbij_h unfolding bij_betw_def by (by100 blast)
        have "e \<in> h ` E" using \<open>e \<in> E\<close> hsurj_loc by (by100 blast)
        have "inv_into E h e \<in> E" using inv_into_into[OF \<open>e \<in> h ` E\<close>] .
        have "h (inv_into E h e) = e" using f_inv_into_f[OF \<open>e \<in> h ` E\<close>] .
        hence "p e = p (h (inv_into E h e))" by (by100 simp)
        also have "\<dots> = p (inv_into E h e)" using hh_p \<open>inv_into E h e \<in> E\<close> by (by100 blast)
        finally have "p (inv_into E h e) = p e" by (by100 simp)
        thus "p ((\<lambda>e. if e \<in> E then inv_into E h e else e) e) = p e"
          using \<open>e \<in> E\<close> by (by100 simp)
      qed
      \<comment> \<open>Trivially id outside E.\<close>
      moreover have "\<forall>e. e \<notin> E \<longrightarrow> (\<lambda>e. if e \<in> E then inv_into E h e else e) e = e"
        by (by100 simp)
      ultimately show "?invC h \<in> ?Cov"
        unfolding top1_covering_transformation_on_def by (by100 blast)
    qed
    \<comment> \<open>Associativity.\<close>
    have hassoc: "\<forall>h\<in>?Cov. \<forall>k\<in>?Cov. \<forall>l\<in>?Cov. ?mul (?mul h k) l = ?mul h (?mul k l)"
      by (by100 auto)
    \<comment> \<open>Identity.\<close>
    have hident: "\<forall>h\<in>?Cov. ?mul ?eC h = h \<and> ?mul h ?eC = h"
      by (by100 auto)
    \<comment> \<open>Inverse: ?invC h \<circ> h = id and h \<circ> ?invC h = id.
       Works because h = id outside E (from the extended definition) and
       inv_into E h inverts h on E.\<close>
    have hinverse: "\<forall>h\<in>?Cov. ?mul (?invC h) h = ?eC \<and> ?mul h (?invC h) = ?eC"
    proof (intro ballI conjI)
      fix h assume hh: "h \<in> ?Cov"
      have hbij: "bij_betw h E E"
        using hh unfolding top1_covering_transformation_on_def top1_homeomorphism_on_def
        by (by100 blast)
      have hinj: "inj_on h E" using hbij unfolding bij_betw_def by (by100 blast)
      have hsurj: "h ` E = E" using hbij unfolding bij_betw_def by (by100 blast)
      have hout: "\<forall>e. e \<notin> E \<longrightarrow> h e = e"
        using hh unfolding top1_covering_transformation_on_def by (by100 blast)
      \<comment> \<open>?invC h \<circ> h = id\<close>
      show "?mul (?invC h) h = ?eC"
      proof (rule ext)
        fix e show "?mul (?invC h) h e = ?eC e"
        proof (cases "e \<in> E")
          case True
          have "h e \<in> E" using hbij True unfolding bij_betw_def by (by100 blast)
          hence "?mul (?invC h) h e = inv_into E h (h e)" by (by100 simp)
          also have "\<dots> = e" by (rule inv_into_f_f[OF hinj True])
          finally show ?thesis by (by100 simp)
        next
          case False
          hence "h e = e" using hout by (by100 blast)
          hence "?mul (?invC h) h e = (\<lambda>e. if e \<in> E then inv_into E h e else e) e"
            by (by100 simp)
          also have "\<dots> = e" using False by (by100 simp)
          finally show ?thesis by (by100 simp)
        qed
      qed
      \<comment> \<open>h \<circ> ?invC h = id\<close>
      show "?mul h (?invC h) = ?eC"
      proof (rule ext)
        fix e show "?mul h (?invC h) e = ?eC e"
        proof (cases "e \<in> E")
          case True
          have "e \<in> h ` E" using True hsurj by (by100 blast)
          have "inv_into E h e \<in> E" using inv_into_into[OF \<open>e \<in> h ` E\<close>] .
          have "(?invC h) e = inv_into E h e" using True by (by100 simp)
          hence "?mul h (?invC h) e = h (inv_into E h e)" by (by100 simp)
          also have "\<dots> = e" by (rule f_inv_into_f[OF \<open>e \<in> h ` E\<close>])
          finally show ?thesis by (by100 simp)
        next
          case False
          hence "?mul h (?invC h) e = h e" by (by100 simp)
          also have "\<dots> = e" using hout False by (by100 blast)
          finally show ?thesis by (by100 simp)
        qed
      qed
    qed
    show ?thesis
      apply (rule exI[of _ ?eC], rule exI[of _ ?invC])
      unfolding top1_is_group_on_def
      using hid_cov hcomp_cov hinv_cov hassoc hident hinverse by (by100 blast)
  qed
  \<comment> \<open>Step 2-3: Define \<Phi>: Cov(p) \<rightarrow> N(H)/H and show it's a group isomorphism.\<close>
  let ?Q = "top1_quotient_group_carrier_on
         (top1_normalizer_on
            (top1_fundamental_group_carrier B TB b0)
            (top1_fundamental_group_mul B TB b0)
            (top1_fundamental_group_invg B TB b0) ?H)
         (top1_fundamental_group_mul B TB b0) ?H"
  let ?mulQ = "top1_quotient_group_mul_on (top1_fundamental_group_mul B TB b0)"
  have h_iso: "top1_groups_isomorphic_on ?Cov (\<lambda>h k e. h (k e)) ?Q ?mulQ"
  proof -
    \<comment> \<open>Munkres 81.2: Construct \<Phi>\<inverse>\<circ>\<Psi>: Cov(p) \<rightarrow> N(H)/H.
       \<Psi>(h) = h(e0) maps each covering transformation to its value at e0.
       \<Phi>: N(H)/H \<rightarrow> p\<inverse>(b0) is the lifting correspondence.
       Step 1: For h \<in> Cov(p), pick a path \<gamma>: e0 \<rightarrow> h(e0) in E.
       Then p\<circ>\<gamma> is a loop at b0, and [p\<circ>\<gamma>] \<in> N(H).
       Define f(h) = [p\<circ>\<gamma>] \<cdot> H (the coset in N(H)/H).
       Step 2: f is well-defined (different paths give same coset).
       Step 3: f is a group homomorphism:
         f(h\<circ>k) = [p\<circ>(\<gamma>*(h\<circ>\<delta>))] \<cdot> H = [p\<circ>\<gamma>]*[p\<circ>\<delta>] \<cdot> H = f(h) \<cdot> f(k).
       Step 4: f is bijective (from Lemma 81.1 + injectivity of \<Psi>).\<close>
    show ?thesis sorry \<comment> \<open>Construct the isomorphism f and verify all properties.\<close>
  qed
  obtain eC invgC where hCov_grp: "top1_is_group_on ?Cov (\<lambda>h k e. h (k e)) eC invgC"
    using hCov_group by (by100 blast)
  show ?thesis
    apply (rule exI[where x="?Cov"])
    apply (rule exI[where x=eC])
    apply (rule exI[where x=invgC])
    using hCov_grp h_iso by (by100 blast)
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
  \<comment> \<open>Construction: E = path-homotopy classes modulo H-cosets.
     All steps (topology, covering, connectivity, subgroup matching) are combined.
     The full proof requires constructing the coset space E, defining basis topology,
     proving evenly-covered property (using semilocal simple connectivity),
     and matching p_*(\<pi>_1(E,e0)) = H.\<close>
  have hTB: "is_topology_on B TB" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>===== CONSTRUCTION (Munkres §82) =====\<close>
  \<comment> \<open>Step 1: Define coset relation. Two paths \<alpha>,\<beta> from b0 are in the same H-coset
     iff [rev(\<alpha>)\<cdot>\<beta>] \<in> H. This is an equivalence relation on paths from b0.\<close>
  \<comment> \<open>Step 2: E = set of H-cosets of path classes from b0.
     E = {{g. coset_rel \<alpha> g} | \<alpha>. path from b0}.
     Projection p: E \<rightarrow> B sends coset to endpoint \<alpha>(1).
     Base point e0 = coset of constant path at b0.\<close>
  \<comment> \<open>Step 3: Topology on E. Basis: for coset c and open U \<ni> p(c),
     B(c, U) = {cosets reachable by extending paths in c by paths in U}.
     This is well-defined and forms a basis (Munkres Lemma 82.2).\<close>
  \<comment> \<open>Step 4: p is a covering map. For each b \<in> B, take U semilocally simply connected
     around b. The fiber p\<inverse>(b) = H-cosets of loops at b0 via paths to b.
     Each slice maps homeomorphically to U via p (Munkres Theorem 82.1 main argument).\<close>
  \<comment> \<open>Step 5: E path-connected: for coset [\<alpha>]H, the path t \<mapsto> [\<alpha>_t]H connects e0 to [\<alpha>]H.
     E locally path-connected: basis elements are path-connected.\<close>
  \<comment> \<open>Step 6: p_*(\<pi>_1(E, e0)) = H. A loop \<gamma> at b0 lifts to a path from e0 = [const]H
     to [\<gamma>]H. Lift is a loop iff [\<gamma>]H = [const]H iff [\<gamma>] \<in> H.\<close>
  \<comment> \<open>===== Step 1: Define the H-coset equivalence on paths =====\<close>
  \<comment> \<open>\<alpha> \<sim>_H \<beta> iff \<alpha>(1) = \<beta>(1) and [\<alpha> * rev(\<beta>)] \<in> H.
     This is an equivalence relation on paths from b0.\<close>
  \<comment> \<open>coset\_rel \<alpha> \<beta> \<equiv> \<alpha>(1) = \<beta>(1) \<and> [\<alpha> * rev(\<beta>)] \<in> H.\<close>
  \<comment> \<open>===== Step 2: Define E, p, e0 =====\<close>
  \<comment> \<open>E = set of coset classes. p maps class to endpoint. e0 = class of constant path.\<close>
  \<comment> \<open>For the formal construction, we use an abstract type for the equivalence classes.\<close>
  \<comment> \<open>===== Step 3: Topology on E via basis B(U, \<alpha>) =====\<close>
  \<comment> \<open>For each coset class c and path-connected open U containing p(c):
     B(U, c) = {classes reachable by extending any path in c by a path in U}.\<close>
  \<comment> \<open>===== Step 4: Verify p is a covering map =====\<close>
  \<comment> \<open>For each b \<in> B, take U semilocally simply connected around b.
     The sets B(U, \<alpha>_i) for different \<alpha>_i ending at b partition p\<inverse>(U).
     Each B(U, \<alpha>_i) maps homeomorphically to U via p.\<close>
  \<comment> \<open>===== Step 5: E path-connected and locally path-connected =====\<close>
  \<comment> \<open>Path-connected: for any coset [\<alpha>]_H, the map t \<mapsto> [\<alpha>_t]_H (prefix of \<alpha>)
     gives a path from e0 to [\<alpha>]_H in E.
     Locally path-connected: basis elements B(U,\<alpha>) are path-connected.\<close>
  \<comment> \<open>===== Step 6: p_*(\<pi>_1(E, e0)) = H =====\<close>
  \<comment> \<open>A loop \<gamma> at b0 lifts to a path from e0 = [const]_H to [\<gamma>]_H.
     Lift is a loop iff [\<gamma>]_H = [const]_H iff [\<gamma>] \<in> H.\<close>
  show ?thesis
  proof -
    \<comment> \<open>Munkres 82.1: Construct E = paths from b0 modulo H-equivalence.
       Step 1: E = {α\<sharp> | α path from b0}. p(α\<sharp>) = α(1).
       Step 2: Topology on E via basis B(U,α) = {(α*δ)\<sharp> | δ path in U from α(1)}.
       Step 3: p is a covering map (each U evenly covered by sheets B(U,α)).
       Step 4: E is path-connected (prefix paths give connectivity).
       Step 5: E is locally path-connected (basis elements path-connected).
       Step 6: p_*(π₁(E,e0)) = H (loop γ lifts to loop iff [γ] ∈ H).\<close>
    show ?thesis sorry \<comment> \<open>Full 6-step construction of covering space.\<close>
  qed
qed

section \<open>Chapter 14: Applications to Group Theory\<close>

section \<open>\<S>83 Covering Spaces of a Graph\<close>

text \<open>An arc is a space homeomorphic to the closed unit interval [0, 1].\<close>


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

(** from \<S>83 Theorem 83.4 (Munkres numbering): any covering space of a graph is itself a graph. **)
theorem Theorem_83_4_covering_of_graph_is_graph:
  assumes "top1_is_graph_on B TB"
      and "top1_covering_map_on E TE B TB p"
      and "is_topology_on_strict E TE"
  shows "top1_is_graph_on E TE"
proof -
  \<comment> \<open>Munkres 83.2: Each arc A in B lifts to arcs in E (sheets over A).
     The covering map p is a local homeomorphism, so lifts of arcs are arcs.
     The intersection condition and weak topology lift from B to E.\<close>
  obtain \<A>B where hAB: "(\<forall>A\<in>\<A>B. A \<subseteq> B \<and> top1_is_arc_on A (subspace_topology B TB A))"
      and hcover: "(\<Union>\<A>B) = B"
    using assms(1) unfolding top1_is_graph_on_def by (by100 auto)
  \<comment> \<open>Step 1: For each arc A \<in> \<A>B, the preimage p\<inverse>(A) splits into sheets.
     Each sheet is homeomorphic to A via p (local homeomorphism), hence an arc.\<close>
  have hAE: "\<exists>\<A>E. (\<forall>A'\<in>\<A>E. A' \<subseteq> E \<and> top1_is_arc_on A' (subspace_topology E TE A'))
      \<and> (\<Union>\<A>E) = E
      \<and> (\<forall>A'\<in>\<A>E. \<forall>B'\<in>\<A>E. A' \<noteq> B' \<longrightarrow>
           A' \<inter> B' \<subseteq> top1_arc_endpoints_on A' (subspace_topology E TE A')
         \<and> A' \<inter> B' \<subseteq> top1_arc_endpoints_on B' (subspace_topology E TE B')
         \<and> finite (A' \<inter> B') \<and> card (A' \<inter> B') \<le> 2)
      \<and> (\<forall>C. C \<subseteq> E \<longrightarrow>
           (closedin_on E TE C \<longleftrightarrow>
            (\<forall>A'\<in>\<A>E. closedin_on A' (subspace_topology E TE A') (A' \<inter> C))))"
  proof -
    \<comment> \<open>Munkres 83.4: Lift graph structure from B to E.
       Step 1: For each arc A \<in> \<A>B, the path components of p\<inverse>(A) are arcs in E.
       Since A is path-connected and simply connected (an arc), p restricted to each
       path component B is a homeomorphism B \<rightarrow> A (by Theorem 54.4: lifting
       correspondence is bijective for simply-connected base).
       Step 2: These lifted arcs cover E (since \<A>B covers B and p is surjective on arcs).
       Different lifted arcs from different base arcs intersect at most in endpoints
       (from the intersection property of the base graph + homeomorphism of sheets).
       Step 3: E has the coherent (weak) topology with respect to the lifted arcs
       (from the covering map property: open sets in E are determined by sheets).\<close>
    \<comment> \<open>Define \<A>E = path components of p\<inverse>(A) for each A \<in> \<A>B.\<close>
    let ?\<A>E = "\<Union>A\<in>\<A>B. {B. B \<noteq> {} \<and> B \<subseteq> {e \<in> E. p e \<in> A}
        \<and> top1_connected_on B (subspace_topology E TE B)
        \<and> (\<forall>C. C \<supseteq> B \<longrightarrow> C \<subseteq> {e \<in> E. p e \<in> A}
            \<longrightarrow> top1_connected_on C (subspace_topology E TE C)
            \<longrightarrow> C = B)}"
    \<comment> \<open>Each B \<in> \<A>E is an arc (homeomorphic to A via p|_B).\<close>
    have hAE_arcs: "\<forall>B'\<in>?\<A>E. B' \<subseteq> E \<and> top1_is_arc_on B' (subspace_topology E TE B')"
      sorry \<comment> \<open>p|\_B: B \<rightarrow> A is a covering map of simply-connected A;
         by Thm 54.4, p|\_B is a homeomorphism; A is an arc, so B is an arc.\<close>
    have hAE_cover: "\<Union>?\<A>E = E"
      sorry \<comment> \<open>\<A>B covers B; p is surjective; path components cover preimage.\<close>
    have hAE_intersect: "\<forall>A'\<in>?\<A>E. \<forall>B'\<in>?\<A>E. A' \<noteq> B' \<longrightarrow>
         A' \<inter> B' \<subseteq> top1_arc_endpoints_on A' (subspace_topology E TE A')
       \<and> A' \<inter> B' \<subseteq> top1_arc_endpoints_on B' (subspace_topology E TE B')
       \<and> finite (A' \<inter> B') \<and> card (A' \<inter> B') \<le> 2"
      sorry \<comment> \<open>If A'\<noteq>B' come from same base arc: disjoint (different sheets).
         If from different base arcs: intersect in at most an endpoint.\<close>
    have hAE_topology: "\<forall>C. C \<subseteq> E \<longrightarrow>
         (closedin_on E TE C \<longleftrightarrow>
          (\<forall>A'\<in>?\<A>E. closedin_on A' (subspace_topology E TE A') (A' \<inter> C)))"
      sorry \<comment> \<open>E has coherent topology: W open iff W \<inter> B open in B for all B.
         Proof: p(W) open in X (coherent topology of X); then W open via slices.\<close>
    show ?thesis
      apply (rule exI[of _ ?\<A>E])
      using hAE_arcs hAE_cover hAE_intersect hAE_topology by (by100 blast)
  qed
  \<comment> \<open>Step 2: E is Hausdorff (covering space of Hausdorff is Hausdorff).\<close>
  have hE_hausdorff: "is_hausdorff_on E TE"
  proof -
    have hB_haus: "is_hausdorff_on B TB"
      using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
    have hTB: "is_topology_on B TB"
      using hB_haus unfolding is_hausdorff_on_def by (by100 blast)
    have hTE: "is_topology_on E TE"
      using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
    have hp_cont: "top1_continuous_map_on E TE B TB p"
      using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
    have hp_surj: "p ` E = B"
      using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
    show ?thesis unfolding is_hausdorff_on_def neighborhood_of_def
    proof (intro conjI ballI impI)
      show "is_topology_on E TE" by (rule hTE)
    next
      fix x y assume hx: "x \<in> E" and hy: "y \<in> E" and hne: "x \<noteq> y"
      show "\<exists>U V. (U \<in> TE \<and> x \<in> U) \<and> (V \<in> TE \<and> y \<in> V) \<and> U \<inter> V = {}"
      proof (cases "p x = p y")
        case False
        \<comment> \<open>Separate in B, pull back preimages.\<close>
        have hpx: "p x \<in> B" using hp_surj hx by (by100 blast)
        have hpy: "p y \<in> B" using hp_surj hy by (by100 blast)
        obtain U1 V1 where hU1: "U1 \<in> TB" "p x \<in> U1" and hV1: "V1 \<in> TB" "p y \<in> V1"
            and hdisj: "U1 \<inter> V1 = {}"
          using hB_haus hpx hpy False unfolding is_hausdorff_on_def neighborhood_of_def
          by (by100 blast)
        have hpU: "{e \<in> E. p e \<in> U1} \<in> TE"
          using hp_cont hU1(1) unfolding top1_continuous_map_on_def by (by100 blast)
        have hpV: "{e \<in> E. p e \<in> V1} \<in> TE"
          using hp_cont hV1(1) unfolding top1_continuous_map_on_def by (by100 blast)
        have "x \<in> {e \<in> E. p e \<in> U1}" using hx hU1(2) by (by100 blast)
        moreover have "y \<in> {e \<in> E. p e \<in> V1}" using hy hV1(2) by (by100 blast)
        moreover have "{e \<in> E. p e \<in> U1} \<inter> {e \<in> E. p e \<in> V1} = {}"
          using hdisj by (by100 blast)
        ultimately show ?thesis using hpU hpV by (by100 blast)
      next
        case True
        \<comment> \<open>Same fiber: x, y in different sheets.\<close>
        have hb: "p x \<in> B" using hp_surj hx by (by100 blast)
        obtain U0 where hbU: "p x \<in> U0"
            and hev: "top1_evenly_covered_on E TE B TB p U0"
          using assms(2) hb unfolding top1_covering_map_on_def by (by100 blast)
        obtain \<V> where hV_all: "(\<forall>V\<in>\<V>. openin_on E TE V)
            \<and> (\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {})
            \<and> {e \<in> E. p e \<in> U0} = \<Union>\<V>
            \<and> (\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V)
                U0 (subspace_topology B TB U0) p)"
          using hev unfolding top1_evenly_covered_on_def
          apply (elim conjE exE)
          apply (rule that)
          apply (by100 blast)+
          done
        have hV_open: "\<forall>V\<in>\<V>. openin_on E TE V" using hV_all by (by100 blast)
        have hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}" using hV_all by (by100 blast)
        have hV_union: "{e \<in> E. p e \<in> U0} = \<Union>\<V>" using hV_all by (by100 blast)
        have hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V)
            U0 (subspace_topology B TB U0) p" using hV_all by (by100 blast)
        have hx_in_V: "x \<in> \<Union>\<V>" using hx hbU hV_union by (by100 blast)
        have "p y \<in> U0" using hbU True by (by100 simp)
        have hy_in_V: "y \<in> \<Union>\<V>" using hy \<open>p y \<in> U0\<close> hV_union by (by100 blast)
        obtain Vx where hVx: "Vx \<in> \<V>" "x \<in> Vx" using hx_in_V by (by100 blast)
        obtain Vy where hVy: "Vy \<in> \<V>" "y \<in> Vy" using hy_in_V by (by100 blast)
        have "Vx \<noteq> Vy"
        proof
          assume heq: "Vx = Vy"
          \<comment> \<open>p is injective on Vx (homeomorphism), p x = p y, so x = y. Contradiction.\<close>
          have "inj_on p Vx"
            using hV_homeo hVx(1) unfolding top1_homeomorphism_on_def bij_betw_def
            by (by100 blast)
          have "y \<in> Vx" using hVy(2) heq by (by100 simp)
          have "x = y" using inj_onD[OF \<open>inj_on p Vx\<close> True hVx(2) \<open>y \<in> Vx\<close>] .
          thus False using hne by (by100 simp)
        qed
        hence "Vx \<inter> Vy = {}" using hV_disj hVx(1) hVy(1) by (by100 blast)
        moreover have "Vx \<in> TE" using hV_open hVx(1)
          unfolding openin_on_def by (by100 blast)
        moreover have "Vy \<in> TE" using hV_open hVy(1)
          unfolding openin_on_def by (by100 blast)
        ultimately show ?thesis using hVx(2) hVy(2) by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>Step 3: Combine all conditions into top1_is_graph_on.\<close>
  show ?thesis unfolding top1_is_graph_on_def
    using assms(3) hE_hausdorff hAE by (by100 blast)
qed

subsection \<open>Reviewer-requested graph theory infrastructure lemmas\<close>

text \<open>A connected graph has a maximal tree (Munkres Lemma 84.3).\<close>
text \<open>A connected graph has a maximal tree (Munkres Lemma 84.3).
  Moved after top1\_is\_tree\_on definition in \<S>84.\<close>

text \<open>tree\_contractible (= tree\_simply\_connected) is defined after top1\_is\_tree\_on in \<S>84.\<close>

text \<open>Quotient of a graph by a maximal tree is a wedge of circles (Munkres Lemma 84.5).\<close>
text \<open>Quotient of a graph by a maximal tree is a wedge of circles (Munkres Lemma 84.5).
  Moved after top1\_is\_tree\_on definition in \<S>84.\<close>

text \<open>The fundamental group of a wedge of circles is free.\<close>
lemma wedge_circles_pi1_free:
  assumes "top1_is_wedge_of_circles_on X TX {..<(n::nat)} p"
  shows "\<exists>(G::int set) mul e invg (\<iota>::nat \<Rightarrow> int).
      top1_is_free_group_full_on G mul e invg \<iota> {..<n}
    \<and> top1_groups_isomorphic_on G mul
        (top1_fundamental_group_carrier X TX p)
        (top1_fundamental_group_mul X TX p)"
  using Theorem_71_1_wedge_of_circles_finite[OF assms]
  by (by100 blast)

text \<open>Covering space of a graph is a graph (Munkres Theorem 83.4).\<close>
lemma graph_covering_is_graph:
  assumes "top1_is_graph_on B TB"
      and "top1_covering_map_on E TE B TB p"
      and "is_topology_on_strict E TE"
  shows "top1_is_graph_on E TE"
  by (rule Theorem_83_4_covering_of_graph_is_graph[OF assms])

text \<open>Schreier rank formula: if F is free of rank n and H has index k,
  then H is free of rank kn - k + 1 = k(n-1) + 1.\<close>
lemma schreier_rank_formula:
  assumes "top1_is_free_group_full_on F mul e invg \<iota> S"
      and "finite S" and "card S = n"
      and "top1_is_subgroup_on F mul e invg H"
      and "card (top1_quotient_group_carrier_on F mul H) = k"
      and "k > 0"
  shows "\<exists>\<iota>H SH. top1_is_free_group_full_on H mul e invg \<iota>H SH
    \<and> finite SH \<and> card SH = k * (n - 1) + 1"
proof -
  \<comment> \<open>Munkres 85.3: Realize F = \<pi>_1(X, x0) where X is a wedge of n+1 circles.\<close>
  obtain X :: "'a set" and TX :: "'a set set" and x0 :: 'a
    where hgraph: "top1_is_graph_on X TX" and hconn: "top1_connected_on X TX"
      and hx0: "x0 \<in> X"
      and hiso: "top1_groups_isomorphic_on F mul
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)"
    sorry \<comment> \<open>Wedge of n+1 circles realizes F.\<close>
  \<comment> \<open>Choose covering E \<rightarrow> X with p_*(\<pi>_1(E)) = H. E is k-fold cover.\<close>
  obtain E :: "'b set" and TE :: "'b set set" and p :: "'b \<Rightarrow> 'a" and e0 :: 'b
    where hcov: "top1_covering_map_on E TE X TX p"
      and hE_conn: "top1_connected_on E TE"
      and he0: "e0 \<in> E"
    sorry \<comment> \<open>Covering existence (Theorem 82.1) + covering of graph is graph (Theorem 83.2).\<close>
  \<comment> \<open>E is a graph (Theorem 83.4). \<pi>_1(E) is free (Theorem 84.7).
     E has k \<times> (edges of X) edges and k \<times> (vertices of X) vertices.
     \<chi>(E) = k \<cdot> \<chi>(X) = k \<cdot> (-n). So rank = 1 - \<chi>(E) = 1 + kn = k(n-1) + 1.\<close>
  show ?thesis
    sorry \<comment> \<open>\<pi>_1(E) is free (Theorem 84.7). Euler char gives rank kn+1.\<close>
qed

section \<open>\<S>84 The Fundamental Group of a Graph\<close>

text \<open>A tree is a connected graph with no nontrivial loops (simply connected).\<close>
definition top1_is_tree_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_tree_on X TX \<longleftrightarrow>
     top1_is_graph_on X TX \<and>
     top1_connected_on X TX \<and>
     top1_simply_connected_on X TX"

text \<open>Reviewer-requested: tree is contractible (simply connected).\<close>
lemma tree_simply_connected:
  assumes "top1_is_tree_on T TT"
  shows "top1_simply_connected_on T TT"
  using assms unfolding top1_is_tree_on_def by (by100 blast)

text \<open>Reviewer-requested: connected graph has a maximal tree (Munkres Lemma 84.3).
  A maximal tree T is one where no strictly larger subtree of X is also a tree.\<close>
lemma connected_graph_has_maximal_tree:
  assumes "top1_is_graph_on X TX"
      and "top1_connected_on X TX"
      and "x0 \<in> X"
  shows "\<exists>T. top1_is_tree_on T (subspace_topology X TX T)
    \<and> T \<subseteq> X \<and> x0 \<in> T
    \<and> (\<forall>T'. T' \<subseteq> X \<longrightarrow> T \<subseteq> T' \<longrightarrow>
          top1_is_tree_on T' (subspace_topology X TX T') \<longrightarrow> T' = T)"
proof -
  \<comment> \<open>Following Munkres Lemma 84.5 (Zorn's lemma argument).
     Let \<A> = {T \<subseteq> X | T is a tree, x0 \<in> T}, ordered by inclusion.
     Step 1: \<A> is non-empty ({x0} is a tree).
     Step 2: Every chain C in \<A> has an upper bound (\<Union>C \<in> \<A>):
       - \<Union>C is connected (any two points are in some T_i ∈ C, hence connected there)
       - \<Union>C is simply connected (any loop is compact, hence in some T_i, hence nulhomotopic)
       - x0 \<in> \<Union>C (from any element of C)
     Step 3: By Zorn's Lemma, \<A> has a maximal element T.\<close>
  define \<A> where "\<A> = {T \<in> Pow X. top1_is_tree_on T (subspace_topology X TX T) \<and> x0 \<in> T}"
  have h\<A>_ne: "\<A> \<noteq> {}"
    sorry \<comment> \<open>X is a graph containing x0, so there exists an arc A containing x0.
       A single arc is a graph, connected, and simply connected (contractible), hence a tree.
       So A \<in> \<A>.\<close>
  have hchain: "\<forall>C \<in> chains \<A>. \<Union>C \<in> \<A>"
    sorry \<comment> \<open>Union of chain of trees is a tree (connected + simply connected + x0).\<close>
  from Zorn_Lemma[OF hchain]
  obtain M where "M \<in> \<A>" and hmax: "\<forall>X'\<in>\<A>. M \<subseteq> X' \<longrightarrow> X' = M" by (by100 blast)
  from \<open>M \<in> \<A>\<close> have hM_tree: "top1_is_tree_on M (subspace_topology X TX M)"
      and hM_sub: "M \<subseteq> X" and hM_x0: "x0 \<in> M"
    unfolding \<A>_def by (by100 blast)+
  have hM_maximal: "\<forall>T'. T' \<subseteq> X \<longrightarrow> M \<subseteq> T' \<longrightarrow>
      top1_is_tree_on T' (subspace_topology X TX T') \<longrightarrow> T' = M"
  proof (intro allI impI)
    fix T' assume "T' \<subseteq> X" "M \<subseteq> T'" "top1_is_tree_on T' (subspace_topology X TX T')"
    hence "T' \<in> \<A>" unfolding \<A>_def using hM_x0 by (by100 blast)
    thus "T' = M" using hmax \<open>M \<subseteq> T'\<close> by (by100 blast)
  qed
  show ?thesis using hM_tree hM_sub hM_x0 hM_maximal by (by100 blast)
qed

text \<open>Reviewer-requested: quotient of graph by maximal tree = wedge of circles (Lemma 84.5).\<close>
lemma graph_quotient_by_tree_wedge_of_circles:
  assumes "top1_is_graph_on X TX"
      and "top1_connected_on X TX"
      and "top1_is_tree_on T (subspace_topology X TX T)"
      and "T \<subseteq> X" and "x0 \<in> T"
  shows "\<exists>(n::nat) W TW q pw.
      top1_is_wedge_of_circles_on W TW {..<n} pw
    \<and> top1_quotient_map_on X TX W TW q
    \<and> (\<forall>x\<in>T. q x = pw)"
proof -
  \<comment> \<open>Munkres Lemma 84.5: Collapse the tree T to a point.
     Each edge of X not in T becomes a loop (circle) in X/T.
     Step 1: Extract the arcs of X.\<close>
  obtain \<A> where h\<A>: "\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
      and h\<A>_cover: "\<Union>\<A> = X"
    using assms(1) unfolding top1_is_graph_on_def by (by100 auto)
  \<comment> \<open>Step 2: Let n = number of edges of X not in T.
     Each such edge has both endpoints in T (since T contains all vertices).\<close>
  \<comment> \<open>Step 3: Define quotient map q: X \<rightarrow> X/T by collapsing T to a point pw.
     Each non-tree edge A becomes a loop S\<alpha> in X/T.
     X/T is a wedge of n circles.\<close>
  show ?thesis sorry \<comment> \<open>Quotient construction: collapse T, non-tree edges become circles.\<close>
qed

(** from \<S>84 Theorem 84.7: the fundamental group of a connected graph is free.
    Specifically, \<pi>_1(X, x_0) is isomorphic to a free group on a set of generators
    (one per loop in a spanning-tree complement). **)
theorem Theorem_84_7_fund_group_graph_is_free:
  fixes X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "top1_is_graph_on X TX"
      and "top1_connected_on X TX"
      and "x0 \<in> X"
  shows "\<exists>(G::int set) mul e invg (\<iota>::nat \<Rightarrow> int) S.
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
  \<comment> \<open>Step 1: X is a graph, so extract arcs.\<close>
  obtain \<A> where h\<A>: "\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
      and h\<A>_cover: "\<Union>\<A> = X"
    using assms(1) unfolding top1_is_graph_on_def by (by100 auto)
  \<comment> \<open>Step 2: Choose a maximal tree T \<subseteq> X. A maximal tree exists by Zorn's lemma
     (or, for countable graphs, by explicit construction).\<close>
  obtain T :: "'a set" where hT_tree: "top1_is_tree_on T (subspace_topology X TX T)"
      and hT_sub: "T \<subseteq> X"
      and hT_max: "\<forall>v\<in>X. \<exists>A\<in>\<A>. v \<in> A \<and> (\<exists>w\<in>T. w \<in> A)"
      and hx0_T: "x0 \<in> T"
    sorry \<comment> \<open>Existence of maximal tree containing x0 (Munkres Lemma 84.3).\<close>
  \<comment> \<open>Step 3: X/T is a wedge of circles (one per edge not in T).
     The edges not in T form loops when their endpoints are identified via T-collapse.\<close>
  obtain n :: nat and W :: "'b set" and TW :: "'b set set" and q :: "'a \<Rightarrow> 'b" and pw :: 'b
    where hW_wedge: "top1_is_wedge_of_circles_on W TW {..<n} pw"
      and hq_quotient: "top1_quotient_map_on X TX W TW q"
      and hq_T: "\<forall>x\<in>T. q x = pw"
    using graph_quotient_by_tree_wedge_of_circles[OF assms(1) assms(2) hT_tree hT_sub hx0_T]
    by (by5000 fast)
  \<comment> \<open>Step 4: The quotient map q: X \<rightarrow> X/T is a homotopy equivalence
     (since T is contractible in X).\<close>
  have hq_equiv: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_carrier W TW (q x0))
      (top1_fundamental_group_mul W TW (q x0))"
    sorry \<comment> \<open>Homotopy equivalence of quotient: Theorem 58.7 or direct SvK argument.\<close>
  \<comment> \<open>Step 5: \<pi>_1(X/T) = \<pi>_1(wedge of n circles) is free on n generators (Theorem 71.1).
     Need q(x0) = pw for Theorem_71_1. Then apply Theorem_71_1 to the wedge W.\<close>
  have hqx0: "q x0 = pw"
    using hq_T hx0_T by (by100 blast)
  from Theorem_71_1_wedge_of_circles_finite[OF hW_wedge]
  obtain G0 :: "int set" and mul0 e0 invg0 and \<iota>0 :: "nat \<Rightarrow> int"
    where hfree: "top1_is_free_group_full_on G0 mul0 e0 invg0 \<iota>0 {..<n}"
      and hW_iso: "top1_groups_isomorphic_on G0 mul0
          (top1_fundamental_group_carrier W TW pw)
          (top1_fundamental_group_mul W TW pw)"
    by (by100 blast)
  \<comment> \<open>Rewrite using hqx0.\<close>
  have hW_iso': "top1_groups_isomorphic_on G0 mul0
      (top1_fundamental_group_carrier W TW (q x0))
      (top1_fundamental_group_mul W TW (q x0))"
    using hW_iso unfolding hqx0 .
  \<comment> \<open>Step 6: Combine: \<pi>_1(X) \<cong> \<pi>_1(W) (hq_equiv) and \<pi>_1(W) \<cong> free (hW_iso').
     By transitivity: \<pi>_1(X) \<cong> free group.\<close>
  have hiso_sym: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier W TW (q x0))
      (top1_fundamental_group_mul W TW (q x0)) G0 mul0"
  proof -
    have hgrpW: "top1_is_group_on
        (top1_fundamental_group_carrier W TW (q x0))
        (top1_fundamental_group_mul W TW (q x0))
        (top1_fundamental_group_id W TW (q x0))
        (top1_fundamental_group_invg W TW (q x0))"
    proof -
      have hTW: "is_topology_on W TW"
        using hW_wedge unfolding top1_is_wedge_of_circles_on_def is_topology_on_strict_def
        by (by100 blast)
      have hqx0_W: "q x0 \<in> W"
        using hW_wedge hqx0 unfolding top1_is_wedge_of_circles_on_def by (by100 simp)
      show ?thesis by (rule top1_fundamental_group_is_group[OF hTW hqx0_W])
    qed
    have hgrpG0: "top1_is_group_on G0 mul0 e0 invg0"
      using hfree unfolding top1_is_free_group_full_on_def by (by100 blast)
    show ?thesis by (rule top1_groups_isomorphic_on_sym[OF hW_iso' hgrpG0 hgrpW])
  qed
  have hchain: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0) G0 mul0"
    by (rule groups_isomorphic_trans_fwd[OF hq_equiv hiso_sym])
  have hchain_sym: "top1_groups_isomorphic_on G0 mul0
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)"
  proof -
    have hgrpX: "top1_is_group_on
        (top1_fundamental_group_carrier X TX x0)
        (top1_fundamental_group_mul X TX x0)
        (top1_fundamental_group_id X TX x0)
        (top1_fundamental_group_invg X TX x0)"
    proof -
      have hTX: "is_topology_on X TX"
        using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
      show ?thesis by (rule top1_fundamental_group_is_group[OF hTX assms(3)])
    qed
    have hgrpG0: "top1_is_group_on G0 mul0 e0 invg0"
      using hfree unfolding top1_is_free_group_full_on_def by (by100 blast)
    show ?thesis by (rule top1_groups_isomorphic_on_sym[OF hchain hgrpX hgrpG0])
  qed
  show ?thesis using hfree hchain_sym by (by100 blast)
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
  \<comment> \<open>Step 1: Realize G as \<pi>_1(X, x0) where X is a wedge of |S| circles.
     By the free group realization theorem, every free group on S is isomorphic
     to \<pi>_1 of a wedge of |S| circles.\<close>
  obtain X :: "'a set" and TX :: "'a set set" and x0 :: 'a
    where "top1_is_graph_on X TX" "top1_connected_on X TX" "x0 \<in> X"
      and hiso: "top1_groups_isomorphic_on G mul
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)"
    sorry \<comment> \<open>Wedge of |S| circles realizes the free group G.\<close>
  \<comment> \<open>Step 2: H \<le> G \<cong> \<pi>_1(X) gives a covering space E of X with p_*(\<pi>_1(E)) \<cong> H.
     Use Theorem 82.1 (existence of covering spaces) with the subgroup
     corresponding to H under the isomorphism G \<cong> \<pi>_1(X).\<close>
  obtain E' :: "'b set" and TE' :: "'b set set" and p' :: "'b \<Rightarrow> 'a" and e0' :: 'b
    where "top1_covering_map_on E' TE' X TX p'" "top1_connected_on E' TE'"
      and "e0' \<in> E'"
    sorry \<comment> \<open>Existence of covering space (Theorem 82.1) for the H-image in \<pi>_1(X).\<close>
  \<comment> \<open>Step 3: E is a graph (Theorem 83.2: covering of graph is graph).
     \<pi>_1(E) is free (Theorem 84.7: fund group of connected graph is free).
     p_* injective (covering maps induce injections on \<pi>_1).
     H \<cong> p_*(\<pi>_1(E)) which is free (subgroup of free = free via injection).\<close>
  show ?thesis sorry \<comment> \<open>Combine: E graph (Thm 83.2) \<Rightarrow> \<pi>_1(E) free (Thm 84.7) \<Rightarrow> H free.\<close>
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
  \<comment> \<open>Step 1: Realize F as \<pi>_1 of wedge X of n+1 circles.\<close>
  obtain X :: "'a set" and TX :: "'a set set" and x0 :: 'a
    where hX_graph: "top1_is_graph_on X TX" and hX_conn: "top1_connected_on X TX"
      and hx0: "x0 \<in> X"
      and hF_iso: "top1_groups_isomorphic_on F mul
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)"
    sorry \<comment> \<open>Wedge of n+1 circles realizes F.\<close>
  \<comment> \<open>Step 2: H \<le> F corresponds to a k-sheeted covering E of X.
     By Theorem 82.1, there exists a covering E with p_*(\<pi>_1(E)) = H-image.\<close>
  obtain E' :: "'b set" and TE' :: "'b set set" and p' :: "'b \<Rightarrow> 'a"
    where hE'_cov: "top1_covering_map_on E' TE' X TX p'"
      and hE'_graph: "top1_is_graph_on E' TE'"
      and hE'_conn: "top1_connected_on E' TE'"
    sorry \<comment> \<open>Covering existence (Theorem 82.1) + covering of graph is graph (Theorem 83.2).\<close>
  \<comment> \<open>Step 3: Euler characteristic. X has 1 vertex, n+1 edges, \<chi>(X) = -n.
     E has k sheets, so \<chi>(E) = k \<cdot> \<chi>(X) = -kn.
     E has k vertices, k(n+1) edges, rank(\<pi>_1(E)) = kn+1.\<close>
  have hE'_free: "\<exists>(\<iota>H::'t \<Rightarrow> 'g) SH.
      top1_is_free_group_full_on H mul e invg \<iota>H SH \<and> card SH = k * n + 1"
    sorry \<comment> \<open>\<pi>_1(E) is free (Theorem 84.7). Euler char gives rank kn+1.\<close>
  show ?thesis using hE'_free by (by100 blast)
qed

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 


















































































































































































































































































end



























































































































































































































































































 
  
   
    



  








 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
  
 
































































