theory AlgTopCached12
  imports "AlgTopCached11.AlgTopCached11"
begin

\<comment> \<open>Hybrid of Theorem\_69\_4 + Theorem\_69\_4\_concrete\_free\_abelian:
   concrete quotient carrier AND generator-image identity.
   Proof follows the same pattern as the concrete version but keeps
   \<iota>H = \<lambda>s. p(\<iota> s) explicit instead of hiding it behind \<exists>.\<close>
lemma Theorem_69_4_concrete_image_basis:
  assumes hfree: "top1_is_free_group_full_on G mul e invg \<iota> S"
  shows "top1_is_free_abelian_group_full_on
      (top1_quotient_group_carrier_on G mul (top1_commutator_subgroup_on G mul e invg))
      (top1_quotient_group_mul_on mul)
      (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) e)
      (\<lambda>C. top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg)
         (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul
            (top1_commutator_subgroup_on G mul e invg) g)))
      (\<lambda>s. top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) (\<iota> s))
      S"
proof -
  let ?N = "top1_commutator_subgroup_on G mul e invg"
  let ?H = "top1_quotient_group_carrier_on G mul ?N"
  let ?mulH = "top1_quotient_group_mul_on mul"
  let ?eH = "top1_group_coset_on G mul ?N e"
  let ?invH = "\<lambda>C. top1_group_coset_on G mul ?N
       (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul ?N g))"
  let ?p = "\<lambda>g. top1_group_coset_on G mul ?N g"
  let ?\<iota>H = "\<lambda>s. ?p (\<iota> s)"
  have hG: "top1_is_group_on G mul e invg"
    using hfree unfolding top1_is_free_group_full_on_def by (by100 blast)
  have h_abel: "top1_is_abelianization_of ?H ?mulH ?eH ?invH G mul e invg ?p"
    by (rule abelianization_concrete[OF hG])
  \<comment> \<open>H is abelian.\<close>
  have hH_abel: "top1_is_abelian_group_on ?H ?mulH ?eH ?invH"
    using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
  \<comment> \<open>\<iota>H maps S into H.\<close>
  have h\<iota>H_in: "\<forall>s\<in>S. ?\<iota>H s \<in> ?H"
  proof (intro ballI)
    fix s assume "s \<in> S"
    hence "\<iota> s \<in> G" using hfree unfolding top1_is_free_group_full_on_def by (by100 blast)
    thus "?\<iota>H s \<in> ?H"
      using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
  qed
  \<comment> \<open>\<iota>H injective.\<close>
  have h\<iota>H_inj: "inj_on ?\<iota>H S"
    by (rule abelianization_injective_on_generators[OF hfree])
  \<comment> \<open>\<iota>H(S) generates H.\<close>
  have hH_gen: "?H = top1_subgroup_generated_on ?H ?mulH ?eH ?invH (?\<iota>H ` S)"
  proof -
    have hH_grp: "top1_is_group_on ?H ?mulH ?eH ?invH"
      using hH_abel unfolding top1_is_abelian_group_on_def by (by100 blast)
    have h\<iota>S_sub: "\<iota> ` S \<subseteq> G"
      using hfree unfolding top1_is_free_group_full_on_def by (by100 blast)
    have hG_gen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
      using hfree unfolding top1_is_free_group_full_on_def by (by100 blast)
    have hphi_hom: "top1_group_hom_on G mul ?H ?mulH ?p"
      using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
    have hphi_surj: "?p ` G = ?H"
      using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
    have "?H = top1_subgroup_generated_on ?H ?mulH ?eH ?invH (?p ` (\<iota> ` S))"
      by (rule surj_hom_generated[OF hG hH_grp hphi_hom hphi_surj h\<iota>S_sub hG_gen])
    moreover have "?p ` (\<iota> ` S) = ?\<iota>H ` S" by (by100 force)
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Independence (no nontrivial integer relations).\<close>
  have hH_indep: "\<And>c. finite {s\<in>S. c s \<noteq> 0} \<Longrightarrow> (\<exists>s\<in>S. c s \<noteq> 0) \<Longrightarrow>
      foldr ?mulH (map (\<lambda>s.
          if c s \<ge> 0 then top1_group_pow ?mulH ?eH (?\<iota>H s) (nat (c s))
          else top1_group_pow ?mulH ?eH (?invH (?\<iota>H s)) (nat (- c s)))
        (SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs)) ?eH \<noteq> ?eH"
    by (rule abelianization_independence_on_generators[OF hfree])
  \<comment> \<open>Assemble.\<close>
  show ?thesis
    unfolding top1_is_free_abelian_group_full_on_def
    using hH_abel h\<iota>H_in h\<iota>H_inj hH_gen hH_indep by (by100 blast)
qed

\<comment> \<open>Sorry-free helpers for Theorem 75.4\<close>
lemma singleton_Bex_simp: "{r. \<exists>w'\<in>{w}. r = (f :: 'b \<Rightarrow> 'a) w'} = {f w}"
  by (by100 blast)

\<comment> \<open>If a list of booleans maps to ±c with sum 0, then #True = #False.\<close>
lemma foldr_plus_map_bool:
  "foldr (+) (map (\<lambda>b. if b then (c::int) else -c) bs) (0::int)
   = c * (int (length (filter id bs)) - int (length (filter Not bs)))"
proof (induct bs)
  case Nil show ?case by (by100 simp)
next
  case (Cons b rest)
  show ?case
  proof (cases b)
    case True
    have "c + c * (int (length (filter id rest)) - int (length (filter Not rest)))
        = c * (1 + int (length (filter id rest)) - int (length (filter Not rest)))"
      by (by100 algebra)
    thus ?thesis using Cons True unfolding id_def by (by100 simp)
  next
    case False
    have "- c + c * (int (length (filter id rest)) - int (length (filter Not rest)))
        = c * (int (length (filter id rest)) - (1 + int (length (filter Not rest))))"
      by (by100 algebra)
    thus ?thesis using Cons False unfolding id_def by (by100 simp)
  qed
qed

lemma balanced_from_sum_zero:
  fixes c :: int
  assumes hc: "c > 0"
      and hsum: "foldr (+) (map (\<lambda>b. if b then c else -c) bs) (0::int) = 0"
  shows "length (filter id bs) = length (filter Not bs)"
proof -
  from hsum have "c * (int (length (filter id bs)) - int (length (filter Not bs))) = 0"
    using foldr_plus_map_bool by (by100 simp)
  hence "int (length (filter id bs)) - int (length (filter Not bs)) = 0"
    using hc by (by100 simp)
  thus ?thesis by (by100 simp)
qed

\<comment> \<open>In an abelian group, every subgroup is normal.\<close>
lemma abelian_subgroup_is_normal:
  assumes hab: "top1_is_abelian_group_on G mul e invg"
      and hsub: "H \<subseteq> G"
      and hgrp: "top1_is_group_on H mul e invg"
  shows "top1_normal_subgroup_on G mul e invg H"
  unfolding top1_normal_subgroup_on_def
proof (intro conjI)
  show "H \<subseteq> G" by (rule hsub)
  show "top1_is_group_on H mul e invg" by (rule hgrp)
  show "\<forall>g\<in>G. \<forall>n\<in>H. mul (mul g n) (invg g) \<in> H"
  proof (intro ballI)
    fix g n assume hg: "g \<in> G" and hn: "n \<in> H"
    have hn_G: "n \<in> G" using hn hsub by (by100 blast)
    have hinvg: "invg g \<in> G" using hab hg
      unfolding top1_is_abelian_group_on_def top1_is_group_on_def by (by100 blast)
    have hcomm: "mul g n = mul n g"
      using hab hg hn_G unfolding top1_is_abelian_group_on_def top1_is_group_on_def
      by (by100 blast)
    have hassoc: "mul (mul n g) (invg g) = mul n (mul g (invg g))"
      using hab hn_G hg hinvg
      unfolding top1_is_abelian_group_on_def top1_is_group_on_def by (by100 blast)
    have "mul g (invg g) = e"
      using hab hg unfolding top1_is_abelian_group_on_def top1_is_group_on_def by (by100 blast)
    hence "mul (mul g n) (invg g) = mul n e"
      using hcomm hassoc by (by100 simp)
    also have "\<dots> = n"
      using hab hn_G unfolding top1_is_abelian_group_on_def top1_is_group_on_def by (by100 blast)
    finally show "mul (mul g n) (invg g) \<in> H" using hn by (by100 simp)
  qed
qed

\<comment> \<open>In an abelian group, the product of squares equals the square of the product:
   (a0^2)(a1^2)...(an^2) = (a0*a1*...*an)^2.\<close>
lemma abelian_foldr_concat_double:
  assumes "top1_is_abelian_group_on G mul e invg"
      and "\<forall>i < length xs. xs ! i \<in> G"
  shows "foldr mul (concat (map (\<lambda>x. [x, x]) xs)) e = mul (foldr mul xs e) (foldr mul xs e)"
  using assms(2)
proof (induct xs)
  case Nil
  have "e \<in> G" using assms(1) unfolding top1_is_abelian_group_on_def top1_is_group_on_def
    by (by100 blast)
  hence "mul e e = e" using assms(1) unfolding top1_is_abelian_group_on_def top1_is_group_on_def
    by (by100 blast)
  thus ?case by (by100 simp)
next
  case (Cons a xs)
  have ha: "a \<in> G" using Cons(2) by (by100 auto)
  have hxs: "\<forall>i<length xs. xs ! i \<in> G" using Cons(2) by (by100 auto)
  have hIH: "foldr mul (concat (map (\<lambda>x. [x, x]) xs)) e = mul (foldr mul xs e) (foldr mul xs e)"
    using Cons(1) hxs by (by100 blast)
  have hG: "top1_is_group_on G mul e invg"
    using assms(1) unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hcl: "\<And>x y. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> mul x y \<in> G"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  have hassoc: "\<And>x y z. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> z \<in> G \<Longrightarrow> mul (mul x y) z = mul x (mul y z)"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  have hcomm: "\<And>x y. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> mul x y = mul y x"
    using assms(1) unfolding top1_is_abelian_group_on_def top1_is_group_on_def by (by100 blast)
  have hfxs: "foldr mul xs e \<in> G"
    using foldr_mul_closed[OF hG] hxs by (by100 blast)
  \<comment> \<open>LHS: foldr mul (a # a # concat(map...xs)) e = mul a (mul a (foldr ... xs))\<close>
  have "foldr mul (concat (map (\<lambda>x. [x, x]) (a # xs))) e
      = mul a (mul a (foldr mul (concat (map (\<lambda>x. [x, x]) xs)) e))"
    by (by100 simp)
  also have "\<dots> = mul a (mul a (mul (foldr mul xs e) (foldr mul xs e)))"
    using hIH by (by100 simp)
  \<comment> \<open>RHS: mul (mul a (foldr xs)) (mul a (foldr xs))\<close>
  \<comment> \<open>Need: a*(a*(P*P)) = (a*P)*(a*P) where P = foldr xs.
     a*(a*(P*P)) = a*((a*P)*P)     [assoc]
                 = a*((P*a)*P)     [comm a P]
                 = a*(P*(a*P))     [assoc]
                 = (a*P)*(a*P)     [assoc]\<close>
  also have "\<dots> = mul (mul a (foldr mul xs e)) (mul a (foldr mul xs e))"
  proof -
    have "mul a (mul a (mul (foldr mul xs e) (foldr mul xs e)))
        = mul a (mul (mul a (foldr mul xs e)) (foldr mul xs e))"
      using hassoc[OF ha hfxs hfxs] hassoc[OF ha _ hfxs] hcl ha hfxs by (by100 metis)
    also have "\<dots> = mul a (mul (foldr mul xs e) (mul a (foldr mul xs e)))"
      using hcomm[OF ha hfxs] hassoc hcl ha hfxs by (by100 metis)
    also have "\<dots> = mul (mul a (foldr mul xs e)) (mul a (foldr mul xs e))"
    proof -
      have "mul a (foldr mul xs e) \<in> G" using hcl ha hfxs by (by100 blast)
      thus ?thesis using hassoc ha hfxs by (by100 metis)
    qed
    finally show ?thesis .
  qed
  also have "\<dots> = mul (foldr mul (a # xs) e) (foldr mul (a # xs) e)"
    by (by100 simp)
  finally show ?case .
qed

\<comment> \<open>word\_product with entries (g, x=g) reconstructs foldr when each x is g or invg(g).\<close>
lemma word_product_rel_invrel_as_foldr:
  fixes mul :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and e :: 'a and invg :: "'a \<Rightarrow> 'a" and g :: 'a
  assumes hne: "invg g \<noteq> g"
  shows "\<And>xs. (\<forall>i<length xs. xs!i = g \<or> xs!i = invg g) \<Longrightarrow>
      top1_group_word_product mul e invg
        (map (\<lambda>(s,b). (g, b)) (map (\<lambda>x. (()::unit, x = g)) xs))
      = foldr mul xs e"
proof -
  fix xs :: "'a list"
  show "(\<forall>i<length xs. xs!i = g \<or> xs!i = invg g) \<Longrightarrow>
      top1_group_word_product mul e invg
        (map (\<lambda>(s,b). (g, b)) (map (\<lambda>x. (()::unit, x = g)) xs))
      = foldr mul xs e"
  proof (induct xs)
    case Nil show ?case by (by100 simp)
  next
    case (Cons x rest)
    have hx: "x = g \<or> x = invg g" using Cons(2) by (by100 auto)
    have hrest: "\<forall>i<length rest. rest!i = g \<or> rest!i = invg g" using Cons(2) by (by100 auto)
    have hIH: "top1_group_word_product mul e invg
        (map (\<lambda>(s,b). (g, b)) (map (\<lambda>x. (()::unit, x = g)) rest))
      = foldr mul rest e" using Cons(1)[OF hrest] .
    from hx show ?case
    proof (elim disjE)
      assume "x = g" thus ?thesis using hIH by (by100 simp)
    next
      assume "x = invg g"
      hence "(x = g) = False" using hne by (by100 simp)
      thus ?thesis using hIH \<open>x = invg g\<close> by (by100 simp)
    qed
  qed
qed

\<comment> \<open>Reindex a free abelian group via a bijection on the index set.\<close>
lemma free_abelian_reindex:
  assumes hfab: "top1_is_free_abelian_group_full_on G mul e invg \<iota> S"
      and hbij: "bij_betw f S' S"
  shows "top1_is_free_abelian_group_full_on G mul e invg (\<iota> \<circ> f) S'"
  unfolding top1_is_free_abelian_group_full_on_def
proof (intro conjI)
  \<comment> \<open>1. Abelian.\<close>
  show "top1_is_abelian_group_on G mul e invg"
    using hfab unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  \<comment> \<open>2. Generators in G.\<close>
  show "\<forall>s\<in>S'. (\<iota> \<circ> f) s \<in> G"
  proof (intro ballI)
    fix s assume "s \<in> S'"
    hence "f s \<in> S" using hbij unfolding bij_betw_def by (by100 blast)
    thus "(\<iota> \<circ> f) s \<in> G"
      using hfab unfolding top1_is_free_abelian_group_full_on_def by (by100 auto)
  qed
  \<comment> \<open>3. Injective.\<close>
  show "inj_on (\<iota> \<circ> f) S'"
  proof -
    have "inj_on \<iota> S" using hfab unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
    moreover have "inj_on f S'" using hbij unfolding bij_betw_def by (by100 blast)
    moreover have "f ` S' \<subseteq> S" using hbij unfolding bij_betw_def by (by100 blast)
    ultimately have "inj_on \<iota> (f ` S')" "inj_on f S'"
      using inj_on_subset by (by100 blast)+
    thus ?thesis using comp_inj_on by (by100 fast)
  qed
  \<comment> \<open>4. Generation: (\<iota>\<circ>f)(S') = \<iota>(f(S')) = \<iota>(S), so same subgroup.\<close>
  show "G = top1_subgroup_generated_on G mul e invg ((\<iota> \<circ> f) ` S')"
  proof -
    have "(\<iota> \<circ> f) ` S' = \<iota> ` (f ` S')" by (by100 auto)
    also have "f ` S' = S" using hbij unfolding bij_betw_def by (by100 blast)
    finally have "(\<iota> \<circ> f) ` S' = \<iota> ` S" .
    thus ?thesis using hfab unfolding top1_is_free_abelian_group_full_on_def by (by100 simp)
  qed
  \<comment> \<open>5. Independence: transfer via f bijection.
     For any c: S' \<rightarrow> int with finite support, define c' = c \<circ> (inv f): S \<rightarrow> int.
     The foldr product over S' with c equals the foldr product over S with c'.
     Independence on S gives the result.\<close>
  show "\<forall>c. finite {s \<in> S'. c s \<noteq> 0} \<longrightarrow>
      (\<exists>s\<in>S'. c s \<noteq> 0) \<longrightarrow>
      foldr mul
       (map (\<lambda>s. if 0 \<le> c s then top1_group_pow mul e ((\<iota> \<circ> f) s) (nat (c s))
                 else top1_group_pow mul e (invg ((\<iota> \<circ> f) s)) (nat (- c s)))
         (SOME xs. set xs = {s \<in> S'. c s \<noteq> 0} \<and> distinct xs))
       e \<noteq> e"
  proof (intro allI impI)
    fix c :: "'c \<Rightarrow> int"
    assume hfin: "finite {s \<in> S'. c s \<noteq> 0}" and hex: "\<exists>s\<in>S'. c s \<noteq> 0"
    \<comment> \<open>Define c' = c \<circ> (inv\_into S' f) on S. Then (\<iota> \<circ> f)(s') with c(s')
       equals \<iota>(f(s')) with c(s') = \<iota>(t) with c'(t) where t = f(s').\<close>
    let ?c' = "c \<circ> inv_into S' f"
    have hfinj: "inj_on f S'" using hbij unfolding bij_betw_def by (by100 blast)
    have hfsurj: "f ` S' = S" using hbij unfolding bij_betw_def by (by100 blast)
    have hsupp_eq: "{s \<in> S. ?c' s \<noteq> 0} = f ` {s' \<in> S'. c s' \<noteq> 0}"
    proof (rule set_eqI, rule iffI)
      fix s assume hs: "s \<in> {s \<in> S. ?c' s \<noteq> 0}"
      hence "s \<in> S" "c (inv_into S' f s) \<noteq> 0" by (by100 auto)+
      have "inv_into S' f s \<in> S'"
      proof -
        from \<open>s \<in> S\<close> hfsurj have "s \<in> f ` S'" by (by100 simp)
        thus ?thesis by (rule inv_into_into)
      qed
      moreover have "c (inv_into S' f s) \<noteq> 0" using \<open>c (inv_into S' f s) \<noteq> 0\<close> .
      moreover have "f (inv_into S' f s) = s"
      proof -
        have "s \<in> f ` S'" using \<open>s \<in> S\<close> hfsurj by (by100 simp)
        thus ?thesis by (rule f_inv_into_f)
      qed
      ultimately have "inv_into S' f s \<in> {s' \<in> S'. c s' \<noteq> 0}" "f (inv_into S' f s) = s"
        by (by100 auto)+
      thus "s \<in> f ` {s' \<in> S'. c s' \<noteq> 0}" by (by100 force)
    next
      fix s assume "s \<in> f ` {s' \<in> S'. c s' \<noteq> 0}"
      then obtain s' where hs': "s' \<in> S'" "c s' \<noteq> 0" "s = f s'" by (by100 blast)
      hence "s \<in> S" using hfsurj by (by100 blast)
      moreover have "?c' s = c s'"
        using inv_into_f_f[OF hfinj \<open>s' \<in> S'\<close>] hs' by (by100 simp)
      ultimately show "s \<in> {s \<in> S. ?c' s \<noteq> 0}" using hs' by (by100 simp)
    qed
    have hfin': "finite {s \<in> S. ?c' s \<noteq> 0}"
      unfolding hsupp_eq using hfin by (by100 blast)
    have hex': "\<exists>s\<in>S. ?c' s \<noteq> 0"
    proof -
      from hex obtain s' where "s' \<in> S'" "c s' \<noteq> 0" by (by100 blast)
      hence "f s' \<in> {s \<in> S. ?c' s \<noteq> 0}" using hsupp_eq by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    \<comment> \<open>By independence on S: the foldr product for c' on S with \<iota> is \<noteq> e.\<close>
    have hindep: "foldr mul
       (map (\<lambda>s. if 0 \<le> ?c' s then top1_group_pow mul e (\<iota> s) (nat (?c' s))
                 else top1_group_pow mul e (invg (\<iota> s)) (nat (- ?c' s)))
         (SOME xs. set xs = {s \<in> S. ?c' s \<noteq> 0} \<and> distinct xs))
       e \<noteq> e"
      using hfab[unfolded top1_is_free_abelian_group_full_on_def] hfin' hex' by (by100 blast)
    \<comment> \<open>The foldr product for c on S' with \<iota>\<circ>f equals the one for c' on S with \<iota>
       (in the abelian group, the products are equal since the terms match).\<close>
    show "foldr mul
       (map (\<lambda>s. if 0 \<le> c s then top1_group_pow mul e ((\<iota> \<circ> f) s) (nat (c s))
                 else top1_group_pow mul e (invg ((\<iota> \<circ> f) s)) (nat (- c s)))
         (SOME xs. set xs = {s \<in> S'. c s \<noteq> 0} \<and> distinct xs))
       e \<noteq> e"
    proof -
      let ?g = "\<lambda>s. if 0 \<le> c s then top1_group_pow mul e ((\<iota> \<circ> f) s) (nat (c s))
                   else top1_group_pow mul e (invg ((\<iota> \<circ> f) s)) (nat (- c s))"
      let ?g' = "\<lambda>s. if 0 \<le> ?c' s then top1_group_pow mul e (\<iota> s) (nat (?c' s))
                    else top1_group_pow mul e (invg (\<iota> s)) (nat (- ?c' s))"
      \<comment> \<open>Key: ?g(s') = ?g'(f(s')) for s' \<in> supp(c) \<subseteq> S'.\<close>
      have hterm_eq: "\<forall>s'\<in>{s' \<in> S'. c s' \<noteq> 0}. ?g s' = ?g' (f s')"
      proof (intro ballI)
        fix s' assume "s' \<in> {s' \<in> S'. c s' \<noteq> 0}"
        hence hs': "s' \<in> S'" by (by100 blast)
        have "?c' (f s') = c s'"
          using inv_into_f_f[OF hfinj hs'] by (by100 simp)
        thus "?g s' = ?g' (f s')" by (by100 simp)
      qed
      \<comment> \<open>foldr for ?g on supp\_S' = foldr for ?g' on supp\_S (same multiset of terms).\<close>
      have "foldr mul (map ?g (SOME xs. set xs = {s \<in> S'. c s \<noteq> 0} \<and> distinct xs)) e
          = foldr mul (map ?g' (SOME xs. set xs = {s \<in> S. ?c' s \<noteq> 0} \<and> distinct xs)) e"
      proof -
        let ?xs = "SOME xs. set xs = {s \<in> S'. c s \<noteq> 0} \<and> distinct xs"
        let ?ys = "SOME xs. set xs = {s \<in> S. ?c' s \<noteq> 0} \<and> distinct xs"
        have hxs_prop: "set ?xs = {s \<in> S'. c s \<noteq> 0} \<and> distinct ?xs"
          using finite_distinct_list[OF hfin] by (rule someI_ex)
        have hys_prop: "set ?ys = {s \<in> S. ?c' s \<noteq> 0} \<and> distinct ?ys"
          using finite_distinct_list[OF hfin'] by (rule someI_ex)
        \<comment> \<open>map ?g ?xs = map (?g' \<circ> f) ?xs since ?g(s') = ?g'(f(s')).\<close>
        have hmap_eq: "map ?g ?xs = map (?g' \<circ> f) ?xs"
        proof (rule map_cong)
          show "?xs = ?xs" ..
          fix s' assume "s' \<in> set ?xs"
          hence "s' \<in> {s' \<in> S'. c s' \<noteq> 0}" using hxs_prop by (by100 blast)
          thus "?g s' = (?g' \<circ> f) s'" using hterm_eq by (by100 auto)
        qed
        \<comment> \<open>map (?g' \<circ> f) ?xs = map ?g' (map f ?xs).\<close>
        have "map (?g' \<circ> f) ?xs = map ?g' (map f ?xs)" by (by100 simp)
        \<comment> \<open>map f ?xs is a distinct list with set = supp\_S, same as ?ys.\<close>
        have hdist_fxs: "distinct (map f ?xs)"
        proof -
          have hsub: "set ?xs \<subseteq> S'" using hxs_prop by (by100 auto)
          have "inj_on f (set ?xs)"
          proof (rule inj_onI)
            fix x y assume "x \<in> set ?xs" "y \<in> set ?xs" "f x = f y"
            hence "x \<in> S'" "y \<in> S'" using hsub by (by100 blast)+
            thus "x = y" using \<open>f x = f y\<close> hfinj unfolding inj_on_def by (by100 blast)
          qed
          thus ?thesis using hxs_prop distinct_map by (by100 blast)
        qed
        have hset_fxs: "set (map f ?xs) = set ?ys"
          using hxs_prop hys_prop hsupp_eq by (by100 auto)
        \<comment> \<open>By abelian permutation: foldr on map f ?xs = foldr on ?ys.\<close>
        have habel: "top1_is_abelian_group_on G mul e invg"
          using hfab unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
        have hg'_in: "\<forall>x \<in> set (map f ?xs). ?g' x \<in> G"
        proof (intro ballI)
          fix s assume "s \<in> set (map f ?xs)"
          hence "s \<in> S" using hset_fxs hys_prop by (by100 auto)
          have hG: "top1_is_group_on G mul e invg"
            using habel unfolding top1_is_abelian_group_on_def by (by100 blast)
          have "\<iota> s \<in> G"
            using hfab \<open>s \<in> S\<close> unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
          hence hpow: "top1_group_pow mul e (\<iota> s) n \<in> G" for n
            using group_pow_in_group'[OF hG] by (by100 blast)
          have "invg (\<iota> s) \<in> G" using hG \<open>\<iota> s \<in> G\<close>
            unfolding top1_is_group_on_def by (by100 fast)
          hence hpow_inv: "top1_group_pow mul e (invg (\<iota> s)) n \<in> G" for n
            using group_pow_in_group'[OF hG] by (by100 blast)
          show "?g' s \<in> G" using hpow hpow_inv by (by100 simp)
        qed
        have "foldr mul (map ?g' (map f ?xs)) e = foldr mul (map ?g' ?ys) e"
          using abelian_foldr_map_perm_distinct[OF habel hg'_in hdist_fxs]
            hys_prop hset_fxs by (by100 blast)
        \<comment> \<open>Chain: map g xs = map (g'\<circ>f) xs = map g' (map f xs), then foldr = foldr g' ys.\<close>
        have hmap_eq2: "map ?g ?xs = map (?g' \<circ> f) ?xs"
        proof (rule map_cong)
          show "?xs = ?xs" ..
          fix s' assume "s' \<in> set ?xs"
          hence "s' \<in> {s' \<in> S'. c s' \<noteq> 0}" using hxs_prop by (by100 blast)
          thus "?g s' = (?g' \<circ> f) s'" using hterm_eq by (by100 auto)
        qed
        have "foldr mul (map ?g ?xs) e = foldr mul (map (?g' \<circ> f) ?xs) e"
          unfolding hmap_eq2 by (by100 simp)
        also have "\<dots> = foldr mul (map ?g' (map f ?xs)) e" by (by100 simp)
        also have "\<dots> = foldr mul (map ?g' ?ys) e"
          using abelian_foldr_map_perm_distinct[OF habel hg'_in hdist_fxs]
            hys_prop hset_fxs by (by100 blast)
        finally show ?thesis .
      qed
      thus ?thesis using hindep by (by100 simp)
    qed
  qed
qed

\<comment> \<open>In a free abelian group on finite S, if all coordinates are 0, then x = e.
   Proof by induction on |S|: strip one coordinate at a time via kernel.\<close>
lemma free_abelian_all_coords_zero_imp_e:
  assumes hfab: "top1_is_free_abelian_group_full_on G mul e invg \<iota> S"
      and hfin: "finite S"
      and hx: "x \<in> G"
      and hcoords: "\<forall>s0 \<in> S. \<forall>\<epsilon>. top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>
          \<longrightarrow> \<epsilon> (\<iota> s0) = 1 \<longrightarrow> (\<forall>s\<in>S. s \<noteq> s0 \<longrightarrow> \<epsilon> (\<iota> s) = 0) \<longrightarrow> \<epsilon> x = 0"
  shows "x = e"
using hfin hfab hx hcoords proof (induct S arbitrary: G x rule: finite_induct)
  case empty
  \<comment> \<open>Free abelian on \<emptyset>. G generated by \<iota> ` \<emptyset> = \<emptyset>. subgroup\_generated = {e}.\<close>
  have "G = top1_subgroup_generated_on G mul e invg (\<iota> ` {})"
    using empty(1) unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  hence "G = top1_subgroup_generated_on G mul e invg {}"
    by (by100 simp)
  moreover have "top1_subgroup_generated_on G mul e invg {} \<subseteq> {e}"
  proof (rule subsetI)
    fix g assume "g \<in> top1_subgroup_generated_on G mul e invg {}"
    have hgrp: "top1_is_group_on G mul e invg"
      using empty(1) unfolding top1_is_free_abelian_group_full_on_def
        top1_is_abelian_group_on_def by (by100 blast)
    from subgroup_generated_word_repr[OF hgrp _ \<open>g \<in> top1_subgroup_generated_on G mul e invg {}\<close>]
    have "g = e \<or> (\<exists>ws. length ws > 0
        \<and> (\<forall>i<length ws. ws!i \<in> {} \<or> (\<exists>s\<in>{}. ws!i = invg s))
        \<and> foldr mul ws e = g)" by (by100 blast)
    moreover have "\<not>(\<exists>ws. length ws > 0
        \<and> (\<forall>i<length ws. ws!i \<in> {} \<or> (\<exists>s\<in>{}. ws!i = invg s))
        \<and> foldr mul ws e = g)"
      by (by100 auto)
    ultimately show "g \<in> {e}" by (by100 blast)
  qed
  ultimately show ?case using empty(2) by (by100 blast)
next
  case (insert s0 T')
  \<comment> \<open>Free abelian on insert s_0 T'. Get coordinate \<epsilon>_{s_0}.\<close>
  from free_abelian_coordinate_projection[OF insert(4) insertI1]
  obtain \<epsilon> where h\<epsilon>_hom: "top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>"
      and h\<epsilon>_s0: "\<epsilon> (\<iota> s0) = 1"
      and h\<epsilon>_rest: "\<forall>s \<in> insert s0 T'. s \<noteq> s0 \<longrightarrow> \<epsilon> (\<iota> s) = 0"
    by (by100 blast)
  \<comment> \<open>\<epsilon>(x) = 0.\<close>
  have h\<epsilon>x: "\<epsilon> x = 0"
    using insert(6) h\<epsilon>_hom h\<epsilon>_s0 h\<epsilon>_rest by (by100 blast)
  \<comment> \<open>ker(\<epsilon>) is free abelian on T'.\<close>
  have hK_fab: "top1_is_free_abelian_group_full_on {g \<in> G. \<epsilon> g = 0} mul e invg \<iota> T'"
  proof -
    have "insert s0 T' - {s0} = T'" using insert(2) by (by100 blast)
    from free_abelian_kernel_coordinate[OF insert(4) insertI1 h\<epsilon>_hom h\<epsilon>_s0 h\<epsilon>_rest]
    show ?thesis using \<open>insert s0 T' - {s0} = T'\<close> by (by100 simp)
  qed
  have hx_ker: "x \<in> {g \<in> G. \<epsilon> g = 0}" using insert(5) h\<epsilon>x by (by100 blast)
  \<comment> \<open>Coordinates for T' in the kernel are still zero.
     For s' \<in> T', the coordinate projection \<epsilon>_{s'} of the kernel gives \<epsilon>'_{s'}(x) = 0.
     But the kernel's coordinate projections may differ from G's.\<close>
  \<comment> \<open>Actually: free\_abelian\_coordinate\_projection applied to hK\_fab gives
     new projections \<epsilon>' on ker(\<epsilon>). We need \<epsilon>'(x) = 0 for these.\<close>
  have hcoords': "\<forall>s0' \<in> T'. \<forall>\<epsilon>'. top1_group_hom_on {g \<in> G. \<epsilon> g = 0} mul (UNIV::int set) (+) \<epsilon>'
      \<longrightarrow> \<epsilon>' (\<iota> s0') = 1 \<longrightarrow> (\<forall>s\<in>T'. s \<noteq> s0' \<longrightarrow> \<epsilon>' (\<iota> s) = 0) \<longrightarrow> \<epsilon>' x = 0"
  proof (intro ballI allI impI)
    fix s0' \<epsilon>'
    assume hs0': "s0' \<in> T'"
      and h\<epsilon>'_hom: "top1_group_hom_on {g \<in> G. \<epsilon> g = 0} mul (UNIV::int set) (+) \<epsilon>'"
      and h\<epsilon>'_s0: "\<epsilon>' (\<iota> s0') = 1"
      and h\<epsilon>'_rest: "\<forall>s\<in>T'. s \<noteq> s0' \<longrightarrow> \<epsilon>' (\<iota> s) = 0"
    \<comment> \<open>Extend \<epsilon>' to a hom on G using Lemma\_67\_7 with assignment:
       \<psi>(s') = 1, \<psi>(s) = 0 for s \<in> T' with s \<noteq> s', \<psi>(s_0) = 0.\<close>
    let ?\<psi>_gen = "\<lambda>s. if s = s0' then (1::int) else 0"
    have hZ_abel: "top1_is_abelian_group_on (UNIV::int set) (+) (0::int) uminus"
      using top1_Z_is_abelian_group unfolding top1_Z_group_def top1_Z_mul_def
        top1_Z_id_def top1_Z_invg_def by (by100 simp)
    have h\<psi>_gen_in: "\<forall>s \<in> insert s0 T'. ?\<psi>_gen s \<in> (UNIV::int set)" by (by100 blast)
    from Lemma_67_7_free_abelian_extension[OF insert(4) hZ_abel h\<psi>_gen_in]
    obtain \<psi> where h\<psi>_hom: "top1_group_hom_on G mul (UNIV::int set) (+) \<psi>"
        and h\<psi>_gen: "\<forall>s \<in> insert s0 T'. \<psi> (\<iota> s) = ?\<psi>_gen s"
      by (by100 blast)
    \<comment> \<open>\<psi> is a coordinate projection on G for s'. Verify generator values.\<close>
    have h\<psi>_s0': "\<psi> (\<iota> s0') = 1"
      using h\<psi>_gen hs0' by (by100 simp)
    have h\<psi>_rest': "\<forall>s \<in> insert s0 T'. s \<noteq> s0' \<longrightarrow> \<psi> (\<iota> s) = 0"
      using h\<psi>_gen by (by100 auto)
    \<comment> \<open>By hcoords (insert(6)): \<psi>(x) = 0.\<close>
    have h\<psi>x: "\<psi> x = 0"
      using insert(6) h\<psi>_hom h\<psi>_s0' h\<psi>_rest' hs0' by (by100 blast)
    \<comment> \<open>\<psi> restricted to ker(\<epsilon>) agrees with \<epsilon>' on generators of ker(\<epsilon>).
       By uniqueness (free\_group\_hom\_unique), \<psi>|_{ker(\<epsilon>)} = \<epsilon>' on ker(\<epsilon>).\<close>
    have hK_grp: "top1_is_group_on {g \<in> G. \<epsilon> g = 0} mul e invg"
      using hK_fab unfolding top1_is_free_abelian_group_full_on_def
        top1_is_abelian_group_on_def by (by100 blast)
    have hK_gen: "{g \<in> G. \<epsilon> g = 0} = top1_subgroup_generated_on {g \<in> G. \<epsilon> g = 0} mul e invg (\<iota> ` T')"
      using hK_fab unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
    have h\<iota>T'_in: "\<forall>s \<in> T'. \<iota> s \<in> {g \<in> G. \<epsilon> g = 0}"
      using hK_fab unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
    \<comment> \<open>\<psi> restricted to ker(\<epsilon>) is a hom ker(\<epsilon>) \<rightarrow> Z.\<close>
    have h\<psi>_restr_hom: "top1_group_hom_on {g \<in> G. \<epsilon> g = 0} mul (UNIV::int set) (+) \<psi>"
      using h\<psi>_hom unfolding top1_group_hom_on_def by (by100 blast)
    \<comment> \<open>\<psi> and \<epsilon>' agree on generators \<iota>(T').\<close>
    have hZ_grp: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
      using hZ_abel unfolding top1_is_abelian_group_on_def by (by100 blast)
    have h_agree: "\<forall>s \<in> T'. \<psi> (\<iota> s) = \<epsilon>' (\<iota> s)"
    proof (intro ballI)
      fix s assume "s \<in> T'"
      show "\<psi> (\<iota> s) = \<epsilon>' (\<iota> s)"
      proof (cases "s = s0'")
        case True thus ?thesis using h\<psi>_s0' h\<epsilon>'_s0 by (by100 simp)
      next
        case False
        have "\<psi> (\<iota> s) = 0" using h\<psi>_rest' \<open>s \<in> T'\<close> False by (by100 blast)
        moreover have "\<epsilon>' (\<iota> s) = 0" using h\<epsilon>'_rest \<open>s \<in> T'\<close> False by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
    qed
    \<comment> \<open>By free\_group\_hom\_unique: \<psi> = \<epsilon>' on ker(\<epsilon>).\<close>
    from free_group_hom_unique[OF hK_grp hZ_grp hK_gen _ h\<psi>_restr_hom h\<epsilon>'_hom h_agree]
        h\<iota>T'_in
    have "\<forall>g \<in> {g \<in> G. \<epsilon> g = 0}. \<psi> g = \<epsilon>' g" by (by100 blast)
    hence "\<psi> x = \<epsilon>' x" using hx_ker by (by100 blast)
    thus "\<epsilon>' x = 0" using h\<psi>x by (by100 simp)
  qed
  \<comment> \<open>Apply IH.\<close>
  from insert(3)[OF hK_fab hx_ker hcoords']
  show ?case .
qed

\<comment> \<open>In an abelian group: pow(mul a b, n) = mul(pow(a,n))(pow(b,n)).\<close>
lemma abelian_group_pow_mul:
  assumes habel: "top1_is_abelian_group_on G mul e invg"
      and ha: "a \<in> G" and hb: "b \<in> G"
  shows "top1_group_pow mul e (mul a b) n = mul (top1_group_pow mul e a n) (top1_group_pow mul e b n)"
proof (induct n)
  case 0 thus ?case
  proof -
    have "e \<in> G"
      using habel unfolding top1_is_abelian_group_on_def top1_is_group_on_def by (by100 blast)
    have "mul e e = e"
      using habel \<open>e \<in> G\<close> unfolding top1_is_abelian_group_on_def top1_is_group_on_def by (by100 blast)
    thus ?thesis by (by100 simp)
  qed
next
  case (Suc n)
  have hgrp: "top1_is_group_on G mul e invg"
    using habel unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hpow_a: "top1_group_pow mul e a n \<in> G"
    using group_pow_in_group[OF hgrp ha] by (by100 blast)
  have hpow_b: "top1_group_pow mul e b n \<in> G"
    using group_pow_in_group[OF hgrp hb] by (by100 blast)
  have hab: "mul a b \<in> G"
    using hgrp ha hb unfolding top1_is_group_on_def by (by100 blast)
  \<comment> \<open>pow(mul a b, Suc n) = mul (mul a b) (pow(mul a b, n))
     = mul (mul a b) (mul(pow a n)(pow b n))  [IH]
     Rearrange using abelian + assoc.\<close>
  have "top1_group_pow mul e (mul a b) (Suc n)
      = mul (mul a b) (top1_group_pow mul e (mul a b) n)"
    by (by100 simp)
  also have "\<dots> = mul (mul a b) (mul (top1_group_pow mul e a n) (top1_group_pow mul e b n))"
    using Suc by (by100 simp)
  also have "\<dots> = mul (top1_group_pow mul e a (Suc n)) (top1_group_pow mul e b (Suc n))"
  proof -
    let ?pa = "top1_group_pow mul e a n"
    let ?pb = "top1_group_pow mul e b n"
    have hassoc: "\<forall>x\<in>G. \<forall>y\<in>G. \<forall>z\<in>G. mul (mul x y) z = mul x (mul y z)"
      using hgrp[unfolded top1_is_group_on_def] by (by100 blast)
    have hcomm: "\<forall>x\<in>G. \<forall>y\<in>G. mul x y = mul y x"
      using habel[unfolded top1_is_abelian_group_on_def top1_is_group_on_def] by (by100 blast)
    have hpa_pb: "mul ?pa ?pb \<in> G"
      using hgrp hpow_a hpow_b unfolding top1_is_group_on_def by (by100 blast)
    \<comment> \<open>Step 1: (a\<cdot>b)\<cdot>(pa\<cdot>pb) = a\<cdot>(b\<cdot>(pa\<cdot>pb)).\<close>
    have h1: "mul (mul a b) (mul ?pa ?pb) = mul a (mul b (mul ?pa ?pb))"
      using hassoc ha hb hpa_pb by (by100 blast)
    \<comment> \<open>Step 2: b\<cdot>(pa\<cdot>pb) = (b\<cdot>pa)\<cdot>pb.\<close>
    have h_bpa: "mul b ?pa \<in> G"
      using hgrp hb hpow_a unfolding top1_is_group_on_def by (by100 blast)
    have h2: "mul b (mul ?pa ?pb) = mul (mul b ?pa) ?pb"
    proof -
      from hassoc hb hpow_a hpow_b have "mul (mul b ?pa) ?pb = mul b (mul ?pa ?pb)"
        by (by100 blast)
      thus ?thesis by (by100 simp)
    qed
    \<comment> \<open>Step 3: b\<cdot>pa = pa\<cdot>b.\<close>
    have h3: "mul b ?pa = mul ?pa b" using hcomm hb hpow_a by (by100 blast)
    \<comment> \<open>Step 4: pa\<cdot>(b\<cdot>pb) = (pa\<cdot>b)\<cdot>pb — wait, we need pa\<cdot>b\<cdot>pb = pa\<cdot>(b\<cdot>pb).\<close>
    have h_bpb: "mul b ?pb \<in> G"
      using hgrp hb hpow_b unfolding top1_is_group_on_def by (by100 blast)
    have h4: "mul (mul ?pa b) ?pb = mul ?pa (mul b ?pb)"
      using hassoc hpow_a hb hpow_b by (by100 blast)
    \<comment> \<open>Step 5: a\<cdot>(pa\<cdot>(b\<cdot>pb)) = (a\<cdot>pa)\<cdot>(b\<cdot>pb).\<close>
    have h5: "mul a (mul ?pa (mul b ?pb)) = mul (mul a ?pa) (mul b ?pb)"
    proof -
      from hassoc ha hpow_a h_bpb have "mul (mul a ?pa) (mul b ?pb) = mul a (mul ?pa (mul b ?pb))"
        by (by100 blast)
      thus ?thesis by (by100 simp)
    qed
    \<comment> \<open>Chain: (a\<cdot>b)\<cdot>(pa\<cdot>pb) = a\<cdot>(b\<cdot>(pa\<cdot>pb)) = a\<cdot>((b\<cdot>pa)\<cdot>pb)
       = a\<cdot>((pa\<cdot>b)\<cdot>pb) = a\<cdot>(pa\<cdot>(b\<cdot>pb)) = (a\<cdot>pa)\<cdot>(b\<cdot>pb).\<close>
    have "mul (mul a b) (mul ?pa ?pb) = mul a (mul (mul b ?pa) ?pb)"
      using h1 h2 by (by100 simp)
    also have "\<dots> = mul a (mul (mul ?pa b) ?pb)" using h3 by (by100 simp)
    also have "\<dots> = mul a (mul ?pa (mul b ?pb))" using h4 by (by100 simp)
    also have "\<dots> = mul (mul a ?pa) (mul b ?pb)" using h5 by (by100 simp)
    finally show ?thesis by (by100 simp)
  qed
  finally show ?case .
qed

\<comment> \<open>A free abelian group is torsion-free: if pow(x,n) = e with n > 0, then x = e.
   Proof: use coordinate projections \<epsilon>_s. hom\_group\_pow gives \<epsilon>_s(pow(x,n)) = n\<cdot>\<epsilon>_s(x).
   If pow(x,n) = e, then n\<cdot>\<epsilon>_s(x) = 0 for all s, so \<epsilon>_s(x) = 0.
   Then independence forces x = e.\<close>
lemma free_abelian_torsion_free:
  assumes hfab: "top1_is_free_abelian_group_full_on G mul e invg \<iota> S"
      and hfin: "finite S"
      and hx: "x \<in> G"
      and hn: "n > 0"
      and hpow: "top1_group_pow mul e x n = e"
  shows "x = e"
proof (rule ccontr)
  assume hne: "x \<noteq> e"
  \<comment> \<open>Extract group properties.\<close>
  have hgrp: "top1_is_group_on G mul e invg"
    using hfab unfolding top1_is_free_abelian_group_full_on_def
      top1_is_abelian_group_on_def by (by100 blast)
  \<comment> \<open>For some s_0 \<in> S, the coordinate \<epsilon>_{s_0}(x) \<noteq> 0.\<close>
  \<comment> \<open>Then \<epsilon>_{s_0}(pow(x,n)) = n \<cdot> \<epsilon>_{s_0}(x) \<noteq> 0 in Z. But pow(x,n) = e, \<epsilon>(e) = 0. Contradiction.\<close>
  \<comment> \<open>Step 1: For every s_0 \<in> S, get coordinate projection.\<close>
  have "\<forall>s0 \<in> S. \<exists>\<epsilon>. top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>
      \<and> \<epsilon> (\<iota> s0) = 1 \<and> (\<forall>s\<in>S. s \<noteq> s0 \<longrightarrow> \<epsilon> (\<iota> s) = 0)"
  proof (intro ballI)
    fix s0 assume "s0 \<in> S"
    thus "\<exists>\<epsilon>. top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>
        \<and> \<epsilon> (\<iota> s0) = 1 \<and> (\<forall>s\<in>S. s \<noteq> s0 \<longrightarrow> \<epsilon> (\<iota> s) = 0)"
      using free_abelian_coordinate_projection[OF hfab] by (by100 blast)
  qed
  \<comment> \<open>Step 2: For every s_0 \<in> S, \<epsilon>_{s_0}(x) = 0 (from pow(x,n) = e).\<close>
  have hcoords_zero: "\<forall>s0 \<in> S. \<forall>\<epsilon>. top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>
      \<longrightarrow> \<epsilon> (\<iota> s0) = 1 \<longrightarrow> (\<forall>s\<in>S. s \<noteq> s0 \<longrightarrow> \<epsilon> (\<iota> s) = 0)
      \<longrightarrow> \<epsilon> x = 0"
  proof (intro ballI allI impI)
    fix s0 \<epsilon>
    assume hs0: "s0 \<in> S"
      and h\<epsilon>_hom: "top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>"
      and h\<epsilon>_s0: "\<epsilon> (\<iota> s0) = 1"
      and h\<epsilon>_rest: "\<forall>s\<in>S. s \<noteq> s0 \<longrightarrow> \<epsilon> (\<iota> s) = 0"
    have hZ_grp: "top1_is_group_on (UNIV::int set) (+) 0 uminus"
      using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
        top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 blast)
    have "\<epsilon> (top1_group_pow mul e x n) = top1_group_pow (+) (0::int) (\<epsilon> x) n"
      using hom_group_pow[OF hgrp hZ_grp h\<epsilon>_hom hx] by (by100 blast)
    hence "\<epsilon> e = top1_group_pow (+) 0 (\<epsilon> x) n" using hpow by (by100 simp)
    hence "0 = top1_group_pow (+) 0 (\<epsilon> x) n"
      using hom_preserves_id[OF hgrp hZ_grp h\<epsilon>_hom] by (by100 simp)
    hence "0 = int n * \<epsilon> x" using int_group_pow by (by100 simp)
    hence "int n * \<epsilon> x = 0" by (by100 simp)
    thus "\<epsilon> x = 0" using hn by (by100 simp)
  qed
  \<comment> \<open>Step 3: All coordinates zero + x \<noteq> e contradicts independence.
     The coordinate map separates points in a free abelian group:
     if \<epsilon>_{s_0}(x) = 0 for all s_0 \<in> S, then x = e.\<close>
  \<comment> \<open>This needs: if x \<in> G, x \<noteq> e, then \<exists>s_0 \<in> S with \<epsilon>_{s_0}(x) \<noteq> 0.
     Equivalently: if all coordinates are 0, x = e.\<close>
  \<comment> \<open>Step 3: x \<noteq> e, x \<in> G = subgroup\_generated(\<iota> ` S). Get word representation.\<close>
  have hgen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
    using hfab unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  have h\<iota>_in: "\<forall>s \<in> S. \<iota> s \<in> G"
    using hfab unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  have h\<iota>_sub: "\<iota> ` S \<subseteq> G" using h\<iota>_in by (by100 blast)
  have hx_sg: "x \<in> top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
    using hx hgen by (by100 simp)
  from subgroup_generated_word_repr[OF hgrp h\<iota>_sub hx_sg]
  have "x = e \<or> (\<exists>ws. length ws > 0
      \<and> (\<forall>i<length ws. ws!i \<in> \<iota> ` S \<or> (\<exists>s\<in>\<iota> ` S. ws!i = invg s))
      \<and> foldr mul ws e = x)" by (by100 blast)
  hence "\<exists>ws. length ws > 0
      \<and> (\<forall>i<length ws. ws!i \<in> \<iota> ` S \<or> (\<exists>s\<in>\<iota> ` S. ws!i = invg s))
      \<and> foldr mul ws e = x" using hne by (by100 blast)
  then obtain ws where hlen: "length ws > 0"
      and hws: "\<forall>i<length ws. ws!i \<in> \<iota> ` S \<or> (\<exists>s\<in>\<iota> ` S. ws!i = invg s)"
      and hprod_ws: "foldr mul ws e = x" by (by100 blast)

  \<comment> \<open>By free\_abelian\_all\_coords\_zero\_imp\_e: x = e.\<close>
  from free_abelian_all_coords_zero_imp_e[OF hfab hfin hx hcoords_zero]
  show False using hne by (by100 simp)
qed


\<comment> \<open>Theorem 75.4 and its proved decomposition lemma\<close>
\<comment> \<open>In an abelian group G generated by A, if every generator decomposes as
   k or k\<cdot>t where k \<in> K (subgroup) and t has order 2, then every element does.\<close>
lemma abelian_generated_decomposes_via_order2:
  assumes habel: "top1_is_abelian_group_on G mul e invg"
      and hgen: "G = top1_subgroup_generated_on G mul e invg A"
      and hK_grp: "top1_is_group_on K mul e invg"
      and hK_sub: "K \<subseteq> G"
      and ht_in: "t \<in> G"
      and ht_ord2: "mul t t = e"
      and hA_sub: "A \<subseteq> G"
      and hA_decomp: "\<forall>a\<in>A. a \<in> K \<or> (\<exists>k\<in>K. a = mul k t)"
  shows "\<forall>g\<in>G. \<exists>k\<in>K. g = k \<or> g = mul k t"
proof (intro ballI)
  fix g assume hg: "g \<in> G"
  have hgrp: "top1_is_group_on G mul e invg"
    using habel unfolding top1_is_abelian_group_on_def by (by100 blast)
  \<comment> \<open>g \<in> subgroup\_generated(A). Word representation.\<close>
  have hg_sg: "g \<in> top1_subgroup_generated_on G mul e invg A"
    using hg hgen by (by100 simp)
  from subgroup_generated_word_repr[OF hgrp hA_sub hg_sg]
  have "g = e \<or> (\<exists>ws. length ws > 0
      \<and> (\<forall>i<length ws. ws!i \<in> A \<or> (\<exists>s\<in>A. ws!i = invg s))
      \<and> foldr mul ws e = g)" by (by100 blast)
  thus "\<exists>k\<in>K. g = k \<or> g = mul k t"
  proof (elim disjE)
    assume "g = e"
    moreover have "e \<in> K" using hK_grp unfolding top1_is_group_on_def by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  next
    assume "\<exists>ws. length ws > 0
        \<and> (\<forall>i<length ws. ws!i \<in> A \<or> (\<exists>s\<in>A. ws!i = invg s))
        \<and> foldr mul ws e = g"
    then obtain ws where hlen: "length ws > 0"
        and hws: "\<forall>i<length ws. ws!i \<in> A \<or> (\<exists>s\<in>A. ws!i = invg s)"
        and hprod: "foldr mul ws e = g" by (by100 blast)
    \<comment> \<open>Each ws!i decomposes into K \<cup> K\<cdot>{t}:
       - If ws!i \<in> A: ws!i \<in> K or ws!i = k\<cdot>t by hA\_decomp
       - If ws!i = invg(a) for a \<in> A:
         - If a \<in> K: invg(a) \<in> K
         - If a = k\<cdot>t: invg(a) = invg(t)\<cdot>invg(k) = t\<cdot>invg(k) (abelian, invg(t)=t).
           So invg(a) = mul(invg(k))(t) (abelian), invg(k) \<in> K.\<close>
    \<comment> \<open>By induction on ws: foldr mul ws e \<in> K \<cup> K\<cdot>{t}.
       Base: foldr mul [] e = e \<in> K.
       Step: foldr mul (a#rest) e = mul a (foldr mul rest e).
         a \<in> K \<cup> K\<cdot>{t}, foldr \<in> K \<cup> K\<cdot>{t} by IH.
         - K\<cdot>K = K (K is subgroup)
         - K\<cdot>(K\<cdot>t) = K\<cdot>t (K is subgroup, abelian)
         - (K\<cdot>t)\<cdot>K = K\<cdot>t (abelian)
         - (K\<cdot>t)\<cdot>(K\<cdot>t) = K\<cdot>t\<cdot>t = K (since t^2=e).\<close>
    \<comment> \<open>invg(t) = t (since t^2 = e in group).\<close>
    have ht_inv: "invg t = t"
    proof -
      have "mul t t = e" using ht_ord2 .
      have "mul t (invg t) = e"
        using hgrp ht_in unfolding top1_is_group_on_def by (by100 fast)
      hence heq: "mul t t = mul t (invg t)" using ht_ord2 by (by100 simp)
      have hinvt_in: "invg t \<in> G" using hgrp ht_in unfolding top1_is_group_on_def by (by100 fast)
      from group_left_cancel[OF hgrp ht_in hinvt_in ht_in heq]
      show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Each ws!i decomposes.\<close>
    have hws_decomp: "\<forall>i<length ws. \<exists>k\<in>K. ws!i = k \<or> ws!i = mul k t"
    proof (intro allI impI)
      fix i assume hi: "i < length ws"
      from hws hi have "ws!i \<in> A \<or> (\<exists>s\<in>A. ws!i = invg s)" by (by100 blast)
      thus "\<exists>k\<in>K. ws!i = k \<or> ws!i = mul k t"
      proof (elim disjE)
        assume "ws!i \<in> A"
        from hA_decomp this show ?thesis by (by100 blast)
      next
        assume "\<exists>s\<in>A. ws!i = invg s"
        then obtain a where ha: "a \<in> A" "ws!i = invg a" by (by100 blast)
        from hA_decomp ha(1) have "a \<in> K \<or> (\<exists>k\<in>K. a = mul k t)" by (by100 blast)
        thus ?thesis
        proof (elim disjE)
          assume "a \<in> K"
          hence "invg a \<in> K" using hK_grp unfolding top1_is_group_on_def by (by100 fast)
          thus ?thesis using ha(2) by (by100 blast)
        next
          assume "\<exists>k\<in>K. a = mul k t"
          then obtain k0 where hk0: "k0 \<in> K" "a = mul k0 t" by (by100 blast)
          \<comment> \<open>invg(a) = invg(mul k0 t) = mul(invg t)(invg k0) = mul t (invg k0) = mul(invg k0) t (abelian).\<close>
          have "invg a = mul (invg k0) t"
          proof -
            have hk0_in: "k0 \<in> G" using hk0(1) hK_sub by (by100 blast)
            have "invg a = invg (mul k0 t)" using hk0(2) by (by100 simp)
            also have "\<dots> = mul (invg t) (invg k0)"
              using group_inv_mul[OF hgrp hk0_in ht_in] by (by100 blast)
            also have "invg t = t" using ht_inv .
            also have "mul t (invg k0) = mul (invg k0) t"
            proof -
              have "invg k0 \<in> G" using hgrp hk0_in unfolding top1_is_group_on_def by (by100 fast)
              from habel[unfolded top1_is_abelian_group_on_def] this ht_in
              show ?thesis by (by100 blast)
            qed
            finally show ?thesis .
          qed
          moreover have "invg k0 \<in> K" using hK_grp hk0(1) unfolding top1_is_group_on_def by (by100 fast)
          ultimately have "ws!i = mul (invg k0) t" using ha(2) by (by100 simp)
          thus ?thesis using \<open>invg k0 \<in> K\<close> by (by100 blast)
        qed
      qed
    qed
    \<comment> \<open>Induction: foldr mul ws e \<in> K \<union> K\<cdot>{t}.\<close>
    have hfoldr_decomp: "\<forall>i<length ws. \<exists>k\<in>K. ws!i = k \<or> ws!i = mul k t \<Longrightarrow>
        \<forall>i<length ws. ws!i \<in> G \<Longrightarrow>
        \<exists>k\<in>K. foldr mul ws e = k \<or> foldr mul ws e = mul k t"
    proof (induct ws)
      case Nil
      have "e \<in> K" using hK_grp unfolding top1_is_group_on_def by (by100 blast)
      moreover have "foldr mul [] e = e" by (by100 simp)
      ultimately show ?case by (by100 blast)
    next
      case (Cons a rest)
      have hrest_dec: "\<forall>i<length rest. \<exists>k\<in>K. rest!i = k \<or> rest!i = mul k t"
      proof (intro allI impI)
        fix i assume hi: "i < length rest"
        hence "Suc i < length (a # rest)" by (by100 simp)
        from Cons(2)[rule_format, OF this] show "\<exists>k\<in>K. rest!i = k \<or> rest!i = mul k t"
          by (by100 simp)
      qed
      have hrest_in: "\<forall>i<length rest. rest!i \<in> G"
        using Cons(3) by (by100 auto)
      from Cons(1)[OF hrest_dec hrest_in] obtain kr where hkr: "kr \<in> K"
          and hkr_dec: "foldr mul rest e = kr \<or> foldr mul rest e = mul kr t"
        by (by100 blast)
      have ha_dec: "\<exists>k\<in>K. a = k \<or> a = mul k t"
      proof -
        have "0 < length (a # rest)" by (by100 simp)
        from Cons(2)[rule_format, OF this] show ?thesis by (by100 simp)
      qed
      then obtain ka where hka: "ka \<in> K" and hka_dec: "a = ka \<or> a = mul ka t" by (by100 blast)
      have hka_in: "ka \<in> G" using hka hK_sub by (by100 blast)
      have hkr_in: "kr \<in> G" using hkr hK_sub by (by100 blast)
      \<comment> \<open>K is closed under mul.\<close>
      have hK_mul_cl: "\<forall>x\<in>K. \<forall>y\<in>K. mul x y \<in> K"
        using hK_grp[unfolded top1_is_group_on_def] by (by100 blast)
      have hmul_K: "mul ka kr \<in> K" using hK_mul_cl hka hkr by (by100 blast)
      \<comment> \<open>Extract associativity, commutativity, identity from abelian group.\<close>
      have hassoc_r: "\<forall>x\<in>G. \<forall>y\<in>G. \<forall>z\<in>G. mul (mul x y) z = mul x (mul y z)"
        using hgrp[unfolded top1_is_group_on_def] by (by100 blast)
      have hassoc_l: "\<forall>x\<in>G. \<forall>y\<in>G. \<forall>z\<in>G. mul x (mul y z) = mul (mul x y) z"
      proof (intro ballI)
        fix x y z assume "x \<in> G" "y \<in> G" "z \<in> G"
        from hassoc_r this have "mul (mul x y) z = mul x (mul y z)" by (by100 blast)
        thus "mul x (mul y z) = mul (mul x y) z" by (by100 simp)
      qed
      have hcomm: "\<forall>x\<in>G. \<forall>y\<in>G. mul x y = mul y x"
        using habel[unfolded top1_is_abelian_group_on_def top1_is_group_on_def] by (by100 blast)
      have hid_r: "\<forall>x\<in>G. mul x e = x"
        using hgrp[unfolded top1_is_group_on_def] by (by100 blast)
      \<comment> \<open>4 cases.\<close>
      show ?case
      proof (cases "a = ka"; cases "foldr mul rest e = kr")
        assume ha_eq: "a = ka" and hr_eq: "foldr mul rest e = kr"
        \<comment> \<open>mul ka kr \<in> K.\<close>
        have hmul_K: "mul ka kr \<in> K"
        proof -
          from hK_grp[unfolded top1_is_group_on_def] have "\<forall>x\<in>K. \<forall>y\<in>K. mul x y \<in> K" by (by100 blast)
          thus ?thesis using hka hkr by (by100 blast)
        qed
        have "foldr mul (a # rest) e = mul ka kr"
          using ha_eq hr_eq by (by100 simp)
        thus ?case using hmul_K by (by100 blast)
      next
        assume ha_eq: "a = ka" and hr_neq: "foldr mul rest e \<noteq> kr"
        hence hr_eq: "foldr mul rest e = mul kr t" using hkr_dec by (by100 blast)
        \<comment> \<open>mul ka (mul kr t) = mul (mul ka kr) t.\<close>
        have "mul ka kr \<in> K" using hmul_K .
        moreover have "foldr mul (a # rest) e = mul (mul ka kr) t"
        proof -
          have "foldr mul (a # rest) e = mul ka (mul kr t)"
            using ha_eq hr_eq by (by100 simp)
          also have "\<dots> = mul (mul ka kr) t"
            using hassoc_l hka_in hkr_in ht_in by (by100 blast)
          finally show ?thesis .
        qed
        ultimately show ?case by (by100 blast)
      next
        assume ha_neq: "a \<noteq> ka" and hr_eq: "foldr mul rest e = kr"
        hence ha_eq: "a = mul ka t" using hka_dec by (by100 blast)
        have "mul ka kr \<in> K" using hmul_K .
        moreover have "foldr mul (a # rest) e = mul (mul ka kr) t"
        proof -
          have "foldr mul (a # rest) e = mul (mul ka t) kr"
            using ha_eq hr_eq by (by100 simp)
          \<comment> \<open>Abelian: mul (mul ka t) kr = mul ka (mul t kr) = mul ka (mul kr t) = mul (mul ka kr) t.\<close>
          also have "\<dots> = mul ka (mul t kr)"
            using hassoc_r hka_in ht_in hkr_in by (by100 blast)
          also have "mul t kr = mul kr t"
            using hcomm ht_in hkr_in by (by100 blast)
          also have "mul ka (mul kr t) = mul (mul ka kr) t"
            using hassoc_l hka_in hkr_in ht_in by (by100 blast)
          finally show ?thesis .
        qed
        ultimately show ?case by (by100 blast)
      next
        assume ha_neq: "a \<noteq> ka" and hr_neq: "foldr mul rest e \<noteq> kr"
        hence ha_eq: "a = mul ka t" using hka_dec by (by100 blast)
        hence hr_eq: "foldr mul rest e = mul kr t" using hkr_dec hr_neq by (by100 blast)
        have "mul ka kr \<in> K" using hmul_K .
        moreover have "foldr mul (a # rest) e = mul ka kr"
        proof -
          have "foldr mul (a # rest) e = mul (mul ka t) (mul kr t)"
            using ha_eq hr_eq by (by100 simp)
          \<comment> \<open>= mul ka (mul t (mul kr t)) = mul ka (mul (mul t kr) t)
             = mul ka (mul (mul kr t) t) [comm] = mul ka (mul kr (mul t t))
             = mul ka (mul kr e) = mul ka kr.\<close>
          also have "\<dots> = mul ka (mul t (mul kr t))"
          proof -
            have "mul kr t \<in> G"
              using hgrp hkr_in ht_in unfolding top1_is_group_on_def by (by100 blast)
            from hassoc_r hka_in ht_in this
            show ?thesis by (by100 blast)
          qed
          also have "mul t (mul kr t) = mul (mul t kr) t"
            using hassoc_l ht_in hkr_in by (by100 blast)
          also have "mul t kr = mul kr t"
            using hcomm ht_in hkr_in by (by100 blast)
          also have "mul (mul kr t) t = mul kr (mul t t)"
            using hassoc_r hkr_in ht_in by (by100 blast)
          also have "mul t t = e" using ht_ord2 .
          also have "mul kr e = kr"
            using hid_r hkr_in by (by100 blast)
          finally have "foldr mul (a # rest) e = mul ka kr" .
          thus ?thesis .
        qed
        ultimately show ?case by (by100 blast)
      qed
    qed
    \<comment> \<open>Apply the induction.\<close>
    moreover have "\<forall>i<length ws. ws!i \<in> G"
    proof (intro allI impI)
      fix i assume "i < length ws"
      from hws this have "ws!i \<in> A \<or> (\<exists>s\<in>A. ws!i = invg s)" by (by100 blast)
      thus "ws!i \<in> G"
      proof (elim disjE)
        assume "ws!i \<in> A" thus ?thesis using hA_sub by (by100 blast)
      next
        assume "\<exists>s\<in>A. ws!i = invg s"
        then obtain s where "s \<in> A" "ws!i = invg s" by (by100 blast)
        hence "s \<in> G" using hA_sub by (by100 blast)
        hence "invg s \<in> G" using hgrp unfolding top1_is_group_on_def by (by100 fast)
        thus ?thesis using \<open>ws!i = invg s\<close> by (by100 simp)
      qed
    qed
    ultimately show ?thesis using hprod hws_decomp by (by100 blast)
  qed
qed

theorem Theorem_75_4_H1_m_projective:
  fixes m :: nat and X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "top1_is_m_fold_projective_on X TX m"
      and "x0 \<in> X"
  shows "\<exists>(H :: (real \<Rightarrow> 'a) set set set set) mulH eH invgH \<phi>.
           top1_is_abelianization_of H mulH eH invgH
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)
             (top1_fundamental_group_id X TX x0)
             (top1_fundamental_group_invg X TX x0)
             \<phi>
         \<and> card (top1_torsion_subgroup_on H mulH eH) = 2
         \<and> (\<exists>(K :: (real \<Rightarrow> 'a) set set set set)
              (\<iota>_S :: nat \<Rightarrow> (real \<Rightarrow> 'a) set set set).
              K \<subseteq> H
            \<and> top1_is_free_abelian_group_full_on K mulH eH invgH \<iota>_S {..<m-1}
            \<and> K \<inter> top1_torsion_subgroup_on H mulH eH = {eH}
            \<and> (\<forall>h\<in>H. \<exists>k\<in>K. \<exists>t\<in>top1_torsion_subgroup_on H mulH eH.
                  h = mulH k t))"
proof -
  \<comment> \<open>Munkres 75.4: \<pi>_1(P_m) has presentation \<langle>a_1,...,a_m | a_1^2...a_m^2\<rangle>.
     Abelianizing: H_1 = Z^m / \<langle>2(\<alpha>_1+...+\<alpha>_m)\<rangle>.
     Change basis: \<beta> = \<alpha>_1+...+\<alpha>_m, keep \<alpha>_1,...,\<alpha>_{m-1}.
     Then H_1 \<cong> Z^{m-1} \<times> Z/2Z.
     Torsion = Z/2Z (generated by \<beta> mod 2\<beta>), free part = Z^{m-1}.\<close>

  let ?\<pi>G = "top1_fundamental_group_carrier X TX x0"
  let ?\<pi>mul = "top1_fundamental_group_mul X TX x0"
  let ?\<pi>e = "top1_fundamental_group_id X TX x0"
  let ?\<pi>inv = "top1_fundamental_group_invg X TX x0"

  \<comment> \<open>Step 1: By Theorem 74.4, \<pi>_1(P_m) has a presentation.\<close>
  note h74_4 = Theorem_74_4_fund_group_m_projective[OF assms]
  let ?relator = "concat (map (\<lambda>i. [(i, True), (i, True)]) [0..<m])"
  from h74_4 obtain G0 :: "(real \<Rightarrow> 'a) set set set"
    and mul0 e0 invg0
    where hpres: "top1_group_presented_by_on G0 mul0 e0 invg0
        ({..<m}::nat set) { ?relator }"
      and hiso: "top1_groups_isomorphic_on G0 mul0 ?\<pi>G ?\<pi>mul"
    by (by100 blast)

  \<comment> \<open>Step 2: Extract the free group F and surjection \<pi>: F \<rightarrow> G_0.\<close>
  have hG0: "top1_is_group_on G0 mul0 e0 invg0"
    using hpres unfolding top1_group_presented_by_on_def by (by100 blast)
  \<comment> \<open>Extract the free group data from the presentation.
     (Structural plumbing: unwrap presentation definition + simplify singleton Bex.)\<close>
  obtain F :: "int set" and mulF eF invgF and \<iota> :: "nat \<Rightarrow> int" and \<pi>F
    where hF_free: "top1_is_free_group_full_on F mulF eF invgF \<iota> ({..<m}::nat set)"
      and h\<pi>_hom: "top1_group_hom_on F mulF G0 mul0 \<pi>F"
      and h\<pi>_surj: "\<pi>F ` F = G0"
      and h\<pi>_ker: "top1_group_kernel_on F e0 \<pi>F =
          top1_normal_subgroup_generated_on F mulF eF invgF
            {top1_group_word_product mulF eF invgF
              (map (\<lambda>(s,b). (\<iota> s, b)) ?relator)}"
  proof -
    have hsimp: "\<And>f. {r. \<exists>w'\<in>{?relator}. r = f w'} = {f ?relator}"
      by (by100 blast)
    show ?thesis
      using hpres[unfolded top1_group_presented_by_on_def]
      apply (elim conjE exE)
      subgoal for F0 mulF0 eF0 invgF0 \<iota>0 \<pi>0
        apply (rule that[of F0 mulF0 eF0 invgF0 \<iota>0 \<pi>0, simplified])
        apply assumption
        apply assumption
        apply assumption
        using hsimp apply (by100 simp)
        done
      done
  qed

  have hF_grp: "top1_is_group_on F mulF eF invgF"
    using hF_free unfolding top1_is_free_group_full_on_def by (by100 blast)

  \<comment> \<open>Step 3: Abelianization of F is free abelian on {..<m}.\<close>
  let ?CF = "top1_commutator_subgroup_on F mulF eF invgF"
  let ?AbelF = "top1_quotient_group_carrier_on F mulF ?CF"
  let ?mulA = "top1_quotient_group_mul_on mulF"
  let ?eA = "top1_group_coset_on F mulF ?CF eF"
  let ?invgA = "\<lambda>C. top1_group_coset_on F mulF ?CF
      (invgF (SOME g. g \<in> F \<and> C = top1_group_coset_on F mulF ?CF g))"
  let ?p = "\<lambda>f. top1_group_coset_on F mulF ?CF f"

  \<comment> \<open>Define \<iota>A = p \<circ> \<iota>: the natural generators of Abel(F) are cosets of free generators.
     Theorem 69.4 (full version) proves that these form a free abelian basis.\<close>
  let ?\<iota>A = "\<lambda>s. ?p (\<iota> s)"
  have h\<iota>A:
    "top1_is_free_abelian_group_full_on ?AbelF ?mulA ?eA ?invgA ?\<iota>A ({..<m}::nat set)"
    using Theorem_69_4_concrete_image_basis[OF hF_free] by (by100 simp)

  have hAbelF_abel: "top1_is_abelian_group_on ?AbelF ?mulA ?eA ?invgA"
    using h\<iota>A unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)

  have hAbelF_grp: "top1_is_group_on ?AbelF ?mulA ?eA ?invgA"
    using hAbelF_abel unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hAbelF_invg_cl: "\<forall>x\<in>?AbelF. ?invgA x \<in> ?AbelF"
  proof -
    from hAbelF_grp[unfolded top1_is_group_on_def]
    show ?thesis by (by100 fast)
  qed
  \<comment> \<open>Extract group axioms for AbelF. Some time out with by100 fast due to
     large let-expanded terms, using by5000 or sorry where needed.\<close>
  have hAbelF_id_l: "\<forall>x\<in>?AbelF. ?mulA ?eA x = x"
    using hAbelF_grp[unfolded top1_is_group_on_def] by (by100 fast)
  have hAbelF_id_r: "\<forall>x\<in>?AbelF. ?mulA x ?eA = x"
    using hAbelF_grp[unfolded top1_is_group_on_def] by (by100 fast)
  have hAbelF_inv_l: "\<forall>x\<in>?AbelF. ?mulA (?invgA x) x = ?eA"
    using hAbelF_grp[unfolded top1_is_group_on_def] by (by100 fast)
  have hAbelF_inv_r: "\<forall>x\<in>?AbelF. ?mulA x (?invgA x) = ?eA"
    using hAbelF_grp[unfolded top1_is_group_on_def] by (by100 fast)
  have hAbelF_e_in: "?eA \<in> ?AbelF"
    using hAbelF_grp[unfolded top1_is_group_on_def] by (by100 fast)
  have hAbelF_mul_cl: "\<forall>x\<in>?AbelF. \<forall>y\<in>?AbelF. ?mulA x y \<in> ?AbelF"
  proof (intro ballI)
    fix x y assume hx: "x \<in> ?AbelF" and hy: "y \<in> ?AbelF"
    have "\<forall>i<length [x, y]. [x, y] ! i \<in> ?AbelF"
    proof (intro allI impI)
      fix i assume "i < length [x, y]"
      hence "i = 0 \<or> i = 1" by (by100 auto)
      thus "[x, y] ! i \<in> ?AbelF" using hx hy by (by100 auto)
    qed
    from foldr_mul_closed[OF hAbelF_grp this]
    have "foldr ?mulA [x, y] ?eA \<in> ?AbelF" .
    hence "?mulA x (?mulA y ?eA) \<in> ?AbelF" by (by100 simp)
    moreover have "?mulA y ?eA = y" using hAbelF_id_r hy by (by100 blast)
    ultimately show "?mulA x y \<in> ?AbelF" by (by100 simp)
  qed
  have hAbelF_assoc: "\<forall>x\<in>?AbelF. \<forall>y\<in>?AbelF. \<forall>z\<in>?AbelF. ?mulA (?mulA x y) z = ?mulA x (?mulA y z)"
  proof (intro ballI)
    fix x y z assume hx: "x \<in> ?AbelF" and hy: "y \<in> ?AbelF" and hz: "z \<in> ?AbelF"
    \<comment> \<open>Use foldr\_mul\_append with two different splits of [x,y,z].\<close>
    have hxy: "\<forall>i<length [x,y]. [x,y]!i \<in> ?AbelF" using hx hy
      by (intro allI impI, auto simp: nth_Cons split: nat.splits)
    have hz1: "\<forall>i<length [z]. [z]!i \<in> ?AbelF" using hz by (by100 auto)
    have hx1: "\<forall>i<length [x]. [x]!i \<in> ?AbelF" using hx by (by100 auto)
    have hyz: "\<forall>i<length [y,z]. [y,z]!i \<in> ?AbelF" using hy hz
      by (intro allI impI, auto simp: nth_Cons split: nat.splits)
    have lhs: "foldr ?mulA ([x,y] @ [z]) ?eA = ?mulA (foldr ?mulA [x,y] ?eA) (foldr ?mulA [z] ?eA)"
      using foldr_mul_append[OF hAbelF_grp hxy hz1] by (by100 blast)
    have rhs: "foldr ?mulA ([x] @ [y,z]) ?eA = ?mulA (foldr ?mulA [x] ?eA) (foldr ?mulA [y,z] ?eA)"
      using foldr_mul_append[OF hAbelF_grp hx1 hyz] by (by100 blast)
    have "foldr ?mulA [x,y] ?eA = ?mulA x y"
      using hAbelF_id_r hy by (by100 simp)
    moreover have "foldr ?mulA [z] ?eA = z"
      using hAbelF_id_r hz by (by100 simp)
    moreover have "foldr ?mulA [x] ?eA = x"
      using hAbelF_id_r hx by (by100 simp)
    moreover have "foldr ?mulA [y,z] ?eA = ?mulA y z"
      using hAbelF_id_r hz by (by100 simp)
    moreover have "([x,y] @ [z]) = ([x] @ [y,z])" by (by100 simp)
    ultimately show "?mulA (?mulA x y) z = ?mulA x (?mulA y z)"
      using lhs rhs by (by100 simp)
  qed

  \<comment> \<open>Step 4: Get the concrete abelianization of G_0.\<close>
  let ?CG = "top1_commutator_subgroup_on G0 mul0 e0 invg0"
  let ?AbelG = "top1_quotient_group_carrier_on G0 mul0 ?CG"
  let ?mulAG = "top1_quotient_group_mul_on mul0"
  let ?eAG = "top1_group_coset_on G0 mul0 ?CG e0"
  let ?invgAG = "\<lambda>C. top1_group_coset_on G0 mul0 ?CG
      (invg0 (SOME g. g \<in> G0 \<and> C = top1_group_coset_on G0 mul0 ?CG g))"
  let ?pG = "\<lambda>g. top1_group_coset_on G0 mul0 ?CG g"

  have hAbelG_abelianization: "top1_is_abelianization_of ?AbelG ?mulAG ?eAG ?invgAG
      G0 mul0 e0 invg0 ?pG"
    using abelianization_concrete[OF hG0] by (by100 simp)

  have hAbelG_grp: "top1_is_group_on ?AbelG ?mulAG ?eAG ?invgAG"
    using quotient_group_is_group[OF hG0 commutator_subgroup_is_normal[OF hG0]] by (by100 simp)

  have hAbelG_abel: "top1_is_abelian_group_on ?AbelG ?mulAG ?eAG ?invgAG"
    using hAbelG_abelianization unfolding top1_is_abelianization_of_def by (by100 blast)

  \<comment> \<open>Step 5: The composition F \<rightarrow> G_0 \<rightarrow> Abel(G_0) factors through Abel(F).
     f = p_G \<circ> \<pi>_F : F \<rightarrow> Abel(G_0). Since Abel(G_0) is abelian, [F,F] \<subseteq> ker(f).
     By universal property of quotient, get \<phi>: Abel(F) \<rightarrow> Abel(G_0).\<close>
  let ?f = "?pG \<circ> \<pi>F"

  have hCG_normal: "top1_normal_subgroup_on G0 mul0 e0 invg0 ?CG"
    using commutator_subgroup_is_normal[OF hG0] by (by100 simp)
  have hpG_hom: "top1_group_hom_on G0 mul0 ?AbelG ?mulAG ?pG"
    using quotient_projection_properties(1)[OF hG0 hCG_normal] by (by100 simp)
  have hpG_surj: "?pG ` G0 = ?AbelG"
    using quotient_projection_properties(2)[OF hG0 hCG_normal] by (by100 simp)

  have hf_hom: "top1_group_hom_on F mulF ?AbelG ?mulAG ?f"
    using group_hom_comp[OF h\<pi>_hom hpG_hom] by (by100 simp)

  have hf_surj: "?f ` F = ?AbelG"
  proof -
    have "?f ` F = ?pG ` (\<pi>F ` F)" by (by100 auto)
    also have "\<dots> = ?pG ` G0" using h\<pi>_surj by (by100 simp)
    also have "\<dots> = ?AbelG" using hpG_surj by (by100 simp)
    finally show ?thesis .
  qed

  have hCF_sub_ker_f: "?CF \<subseteq> top1_group_kernel_on F ?eAG ?f"
    using Lemma_69_3_commutator_in_kernel[OF hF_grp hAbelG_abel hf_hom] by (by100 simp)

  \<comment> \<open>Step 6: The normal subgroup ?CF is normal in F.\<close>
  have hCF_normal: "top1_normal_subgroup_on F mulF eF invgF ?CF"
    using commutator_subgroup_is_normal[OF hF_grp] by (by100 simp)

  \<comment> \<open>Step 7: By universal property, get \<phi>_bar: Abel(F) \<rightarrow> Abel(G_0).\<close>
  from quotient_group_universal_property[OF hF_grp hCF_normal hAbelG_grp hf_hom hCF_sub_ker_f]
  obtain \<phi>_bar where
    h\<phi>_hom: "top1_group_hom_on ?AbelF ?mulA ?AbelG ?mulAG \<phi>_bar"
    and h\<phi>_factor: "\<forall>g \<in> F. \<phi>_bar (?p g) = ?f g"
    by (by5000 blast)

  \<comment> \<open>Step 8: \<phi>_bar is surjective (since f is surjective).\<close>
  have h\<phi>_surj: "\<phi>_bar ` ?AbelF = ?AbelG"
  proof (rule set_eqI, rule iffI)
    fix y assume "y \<in> \<phi>_bar ` ?AbelF"
    then obtain x where "x \<in> ?AbelF" "\<phi>_bar x = y" by (by100 blast)
    thus "y \<in> ?AbelG" using h\<phi>_hom unfolding top1_group_hom_on_def by (by5000 blast)
  next
    fix y assume hy: "y \<in> ?AbelG"
    \<comment> \<open>y = pG(g) for some g \<in> G0, and g = \<pi>F(f0) for some f0 \<in> F.\<close>
    from hy obtain g where hg: "g \<in> G0" "y = ?pG g"
      unfolding top1_quotient_group_carrier_on_def by (by100 blast)
    from hg(1) h\<pi>_surj obtain f0 where hf0: "f0 \<in> F" "\<pi>F f0 = g" by (by100 blast)
    have "?p f0 \<in> ?AbelF"
      unfolding top1_quotient_group_carrier_on_def using hf0(1) by (by100 blast)
    moreover have "\<phi>_bar (?p f0) = y"
      using h\<phi>_factor hf0 hg by (by100 simp)
    ultimately show "y \<in> \<phi>_bar ` ?AbelF" by (by100 blast)
  qed

  have hpG_ker: "top1_group_kernel_on G0 ?eAG ?pG = ?CG"
    using quotient_projection_properties(3)[OF hG0 hCG_normal] by (by100 simp)

  \<comment> \<open>Step 9: ker(\<phi>_bar) = image of ker(\<pi>_F) under p.
     More precisely: ker(\<phi>_bar) = p(ker(\<pi>_F) \<cdot> [F,F]) / [F,F]
     = normal subgroup of Abel(F) generated by p(relator).\<close>
  let ?rel_in_F = "top1_group_word_product mulF eF invgF
      (map (\<lambda>(s,b). (\<iota> s, b)) ?relator)"
  let ?rel_in_AbelF = "?p ?rel_in_F"
  let ?N_AbelF = "top1_normal_subgroup_generated_on ?AbelF ?mulA ?eA ?invgA
      {?rel_in_AbelF}"

  have hrel_in_ker_\<pi>: "?rel_in_F \<in> top1_group_kernel_on F e0 \<pi>F"
  proof -
    have "?rel_in_F \<in> top1_normal_subgroup_generated_on F mulF eF invgF {?rel_in_F}"
      unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
    thus ?thesis using h\<pi>_ker by (by100 simp)
  qed
  have hrel_in_F: "?rel_in_F \<in> F"
    using hrel_in_ker_\<pi> unfolding top1_group_kernel_on_def by (by100 blast)
  have hN_in_AbelF: "{?rel_in_AbelF} \<subseteq> ?AbelF"
    unfolding top1_quotient_group_carrier_on_def using hrel_in_F by (by100 blast)
  have hN_normal: "top1_normal_subgroup_on ?AbelF ?mulA ?eA ?invgA ?N_AbelF"
    using normal_subgroup_generated_is_normal[OF hAbelF_grp hN_in_AbelF] by (by100 simp)

  have hker_\<phi>: "top1_group_kernel_on ?AbelF ?eAG \<phi>_bar = ?N_AbelF"
  proof (rule set_eqI, rule iffI)
    \<comment> \<open>Direction (\<supseteq>): ?N_AbelF \<subseteq> ker(\<phi>_bar). Since p(relator) \<in> ker(\<phi>_bar)
       and ker(\<phi>_bar) is a normal subgroup, the normal closure of {p(relator)} is contained.\<close>
    fix x assume hx: "x \<in> ?N_AbelF"
    from hrel_in_ker_\<pi> have "\<pi>F ?rel_in_F = e0" unfolding top1_group_kernel_on_def by (by100 blast)
    have hrel_in_F: "?rel_in_F \<in> F"
      using hrel_in_ker_\<pi> unfolding top1_group_kernel_on_def by (by100 blast)
    have hprel_in_AbelF: "?rel_in_AbelF \<in> ?AbelF"
      unfolding top1_quotient_group_carrier_on_def using hrel_in_F by (by100 blast)
    have h\<phi>_eq: "\<phi>_bar ?rel_in_AbelF = ?eAG"
    proof -
      have "\<phi>_bar ?rel_in_AbelF = ?f ?rel_in_F"
        using h\<phi>_factor hrel_in_F by (by100 simp)
      also have "\<dots> = ?pG (\<pi>F ?rel_in_F)" by (by100 simp)
      also have "\<dots> = ?pG e0" using \<open>\<pi>F ?rel_in_F = e0\<close> by (by100 simp)
      finally show ?thesis by (by100 simp)
    qed
    have hprel_in_ker: "?rel_in_AbelF \<in> top1_group_kernel_on ?AbelF ?eAG \<phi>_bar"
      using hprel_in_AbelF h\<phi>_eq unfolding top1_group_kernel_on_def by (by100 blast)
    \<comment> \<open>ker(\<phi>_bar) is a normal subgroup of Abel(F).\<close>
    have hker_normal: "top1_normal_subgroup_on ?AbelF ?mulA ?eA ?invgA
        (top1_group_kernel_on ?AbelF ?eAG \<phi>_bar)"
      using kernel_is_normal_subgroup[OF hAbelF_grp hAbelG_grp h\<phi>_hom] by (by100 simp)
    \<comment> \<open>By normal_closure_least: ?N_AbelF \<subseteq> ker(\<phi>_bar).\<close>
    have "?N_AbelF \<subseteq> top1_group_kernel_on ?AbelF ?eAG \<phi>_bar"
      using normal_closure_least[OF hAbelF_grp hker_normal] hprel_in_ker by (by100 blast)
    thus "x \<in> top1_group_kernel_on ?AbelF ?eAG \<phi>_bar" using hx by (by100 blast)
  next
    \<comment> \<open>Direction (\<subseteq>): ker(\<phi>_bar) \<subseteq> ?N_AbelF.
       For x \<in> ker(\<phi>_bar): x = p(g) for some g \<in> F.
       \<phi>_bar(p(g)) = pG(\<pi>F(g)) = eAG, so \<pi>F(g) \<in> [G_0,G_0].
       Since \<pi>F surjective, [G_0,G_0] = \<pi>F([F,F]).
       So g = c \<cdot> k where c \<in> [F,F], k \<in> ker(\<pi>F).
       p(g) = p(k) (since c \<in> [F,F] = ker(p)).
       k \<in> normal_closure({relator}) \<Longrightarrow> p(k) \<in> \<langle>p(relator)\<rangle> in Abel(F) (abelian!).\<close>
    fix x assume hx: "x \<in> top1_group_kernel_on ?AbelF ?eAG \<phi>_bar"
    \<comment> \<open>x \<in> Abel(F) and \<phi>_bar(x) = eAG.\<close>
    have hx_in: "x \<in> ?AbelF" using hx unfolding top1_group_kernel_on_def by (by100 blast)
    have h\<phi>x: "\<phi>_bar x = ?eAG" using hx unfolding top1_group_kernel_on_def by (by100 blast)
    \<comment> \<open>x = p(g) for some g \<in> F.\<close>
    from hx_in obtain g where hg: "g \<in> F" "x = ?p g"
      unfolding top1_quotient_group_carrier_on_def by (by100 blast)
    \<comment> \<open>\<phi>_bar(p(g)) = f(g) = pG(\<pi>F(g)) = eAG, so \<pi>F(g) \<in> [G_0,G_0].\<close>
    have "\<phi>_bar (?p g) = ?f g" using h\<phi>_factor hg(1) by (by100 simp)
    hence "?pG (\<pi>F g) = ?eAG" using h\<phi>x hg(2) by (by100 simp)
    hence h\<pi>g_in_CG: "\<pi>F g \<in> ?CG"
    proof -
      have "\<pi>F g \<in> G0" using h\<pi>_hom hg(1) unfolding top1_group_hom_on_def by (by100 blast)
      have "?pG (\<pi>F g) = ?eAG" using \<open>?pG (\<pi>F g) = ?eAG\<close> .
      hence "\<pi>F g \<in> top1_group_kernel_on G0 ?eAG ?pG"
        using \<open>\<pi>F g \<in> G0\<close> unfolding top1_group_kernel_on_def by (by100 blast)
      thus "\<pi>F g \<in> ?CG" using hpG_ker by (by100 simp)
    qed
    \<comment> \<open>\<pi>F surjective maps [F,F] onto [G_0,G_0]:
       \<pi>F(g) \<in> [G_0,G_0] = \<pi>F([F,F]).
       So \<pi>F(g) = \<pi>F(c) for some c \<in> [F,F],
       giving g = c \<cdot> k where k = invgF(c) \<cdot> g \<in> ker(\<pi>F).\<close>
    have h\<pi>_comm: "\<pi>F ` ?CF = ?CG"
      using surj_hom_image_commutator[OF hF_grp hG0 h\<pi>_hom h\<pi>_surj] by (by100 simp)
    have "\<pi>F g \<in> \<pi>F ` ?CF" using h\<pi>g_in_CG h\<pi>_comm by (by100 simp)
    then obtain c where hc: "c \<in> ?CF" "\<pi>F c = \<pi>F g" by (by100 blast)
    have hc_in_F: "c \<in> F" using hc(1) hCF_normal
      unfolding top1_normal_subgroup_on_def by (by100 blast)
    \<comment> \<open>k = mulF(invgF(c))(g) \<in> ker(\<pi>F).\<close>
    have hinvc: "invgF c \<in> F" using hF_grp hc_in_F unfolding top1_is_group_on_def by (by100 blast)
    let ?k = "mulF (invgF c) g"
    have hk_in_F: "?k \<in> F" using hF_grp hinvc hg(1) unfolding top1_is_group_on_def by (by100 blast)
    have "\<pi>F ?k = mul0 (\<pi>F (invgF c)) (\<pi>F g)"
      using h\<pi>_hom hinvc hg(1) unfolding top1_group_hom_on_def by (by100 blast)
    also have "\<dots> = mul0 (invg0 (\<pi>F c)) (\<pi>F g)"
      using hom_preserves_inv[OF hF_grp hG0 h\<pi>_hom hc_in_F] by (by100 simp)
    also have "\<dots> = mul0 (invg0 (\<pi>F g)) (\<pi>F g)" using hc(2) by (by100 simp)
    also have "\<dots> = e0"
    proof -
      have "\<pi>F g \<in> G0" using h\<pi>_hom hg(1) unfolding top1_group_hom_on_def by (by100 blast)
      thus ?thesis using hG0 unfolding top1_is_group_on_def by (by5000 blast)
    qed
    finally have hk_in_ker: "?k \<in> top1_group_kernel_on F e0 \<pi>F"
      using hk_in_F unfolding top1_group_kernel_on_def by (by100 blast)
    \<comment> \<open>p(g) = p(c \<cdot> k) = mulA(p(c), p(k)) = mulA(eA, p(k)) = p(k)
       since c \<in> [F,F] = ker(p).\<close>
    have hpc: "?p c = ?eA"
    proof -
      have "c \<in> ?CF" using hc(1) .
      have "?CF = top1_group_kernel_on F ?eA ?p"
        using quotient_projection_properties(3)[OF hF_grp hCF_normal] by (by100 simp)
      hence "c \<in> top1_group_kernel_on F ?eA ?p" using hc(1) by (by100 blast)
      thus "?p c = ?eA" unfolding top1_group_kernel_on_def by (by100 blast)
    qed
    have "x = ?p g" using hg(2) .
    \<comment> \<open>p is a hom, so p(g) = p(mulF(c)(mulF(invgF(c))(g))) = mulA(p(c), p(k)).\<close>
    have hassocF: "\<forall>x\<in>F. \<forall>y\<in>F. \<forall>z\<in>F. mulF (mulF x y) z = mulF x (mulF y z)"
      using hF_grp unfolding top1_is_group_on_def by (by100 blast)
    have hinv_rF: "\<forall>x\<in>F. mulF x (invgF x) = eF"
      using hF_grp unfolding top1_is_group_on_def by (by100 blast)
    have hid_lF: "\<forall>x\<in>F. mulF eF x = x"
      using hF_grp unfolding top1_is_group_on_def by (by100 blast)
    have hg_decomp: "g = mulF c ?k"
    proof -
      have "mulF c ?k = mulF (mulF c (invgF c)) g"
        using hassocF hc_in_F hinvc hg(1) by (by100 metis)
      also have "\<dots> = mulF eF g" using hinv_rF hc_in_F by (by100 simp)
      also have "\<dots> = g" using hid_lF hg(1) by (by100 blast)
      finally show ?thesis by (by100 simp)
    qed
    have hpF_hom: "top1_group_hom_on F mulF ?AbelF ?mulA ?p"
      using quotient_projection_properties(1)[OF hF_grp hCF_normal] by (by100 simp)
    have "?p (mulF c ?k) = ?mulA (?p c) (?p ?k)"
      using hpF_hom hc_in_F hk_in_F unfolding top1_group_hom_on_def by (by100 blast)
    hence "?p g = ?mulA (?p c) (?p ?k)" using hg_decomp by (by100 simp)
    also have "\<dots> = ?mulA ?eA (?p ?k)" using hpc by (by100 simp)
    also have "\<dots> = ?p ?k"
    proof -
      have "?p ?k \<in> ?AbelF"
        unfolding top1_quotient_group_carrier_on_def using hk_in_F by (by100 blast)
      thus ?thesis using hAbelF_grp unfolding top1_is_group_on_def by (by5000 blast)
    qed
    finally have hx_eq_pk: "x = ?p ?k" using hg(2) by (by100 simp)
    \<comment> \<open>k \<in> ker(\<pi>F) = normal\_closure({relator}).
       In the abelian group Abel(F), p maps normal\_closure(\{r\}) to
       the subgroup generated by {p(r)}. Since Abel(F) is abelian,
       subgroup generated = normal closure.
       So p(k) \<in> ?N_AbelF.\<close>
    have hk_in_ncl: "?k \<in> top1_normal_subgroup_generated_on F mulF eF invgF {?rel_in_F}"
      using hk_in_ker h\<pi>_ker by (by100 simp)
    \<comment> \<open>Preimage trick: M = {g \<in> F. p(g) \<in> N\_AbelF} is normal in F, contains relator,
       so normal\_closure({relator}) \<subseteq> M, hence k \<in> M, hence p(k) \<in> N\_AbelF.\<close>
    let ?M = "{g \<in> F. ?p g \<in> ?N_AbelF}"
    have hM_normal: "top1_normal_subgroup_on F mulF eF invgF ?M"
      using preimage_normal_subgroup[OF hF_grp hAbelF_grp hpF_hom hN_normal] by (by100 simp)
    have hrel_in_M: "?rel_in_F \<in> ?M"
    proof -
      have "?rel_in_F \<in> F" using hrel_in_F .
      have "?rel_in_AbelF \<in> ?N_AbelF"
        unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
      thus ?thesis using \<open>?rel_in_F \<in> F\<close> by (by100 blast)
    qed
    have "{?rel_in_F} \<subseteq> ?M" using hrel_in_M by (by100 blast)
    have "top1_normal_subgroup_generated_on F mulF eF invgF {?rel_in_F} \<subseteq> ?M"
      using normal_closure_least[OF hF_grp hM_normal \<open>{?rel_in_F} \<subseteq> ?M\<close>] by (by100 simp)
    hence "?k \<in> ?M" using hk_in_ncl by (by100 blast)
    hence "?p ?k \<in> ?N_AbelF" by (by100 blast)
    thus "x \<in> ?N_AbelF" using hx_eq_pk by (by100 simp)
  qed

  \<comment> \<open>Step 10: In the abelian group Abel(F), the normal closure of {?rel_in_AbelF}
     is just the cyclic subgroup generated by ?rel_in_AbelF.
     Since Abel(F) is abelian, normal closure = subgroup generated.\<close>

  \<comment> \<open>Step 11: The relator image in Abel(F).
     In the free group F: relator = \<iota>(0)^2 \<cdot> \<iota>(1)^2 \<cdot> ... \<cdot> \<iota>(m-1)^2.
     In Abel(F): p(relator) = \<iota>A(0)^2 \<cdot> \<iota>A(1)^2 \<cdot> ... \<cdot> \<iota>A(m-1)^2
     (using that p is a hom and p(\<iota>(i)) relates to \<iota>A(i)).
     This is "2 \<cdot> \<beta>" where \<beta> = \<iota>A(0) \<cdot> ... \<cdot> \<iota>A(m-1) in additive notation.\<close>

  \<comment> \<open>Step 12: By first isomorphism theorem, Abel(G_0) \<cong> Abel(F)/N.
     So the structure of Abel(G_0) is determined by Abel(F)/\<langle>2\<beta>\<rangle>.\<close>

  have hAbelG_iso: "top1_groups_isomorphic_on ?AbelG ?mulAG
      (top1_quotient_group_carrier_on ?AbelF ?mulA ?N_AbelF)
      (top1_quotient_group_mul_on ?mulA)"
    using first_isomorphism_theorem[OF hAbelF_grp hN_normal hAbelG_grp h\<phi>_hom h\<phi>_surj hker_\<phi>]
    by (by100 simp)

  \<comment> \<open>Step 13: Analyze torsion subgroup of Abel(G_0).
     In Abel(F)/\<langle>2\<beta>\<rangle>, torsion elements h satisfy n\<cdot>h = 0 for some n > 0.
     This means n\<cdot>h \<in> \<langle>2\<beta>\<rangle>.
     Write h = c_0\<cdot>\<iota>A(0) + ... + c_{m-1}\<cdot>\<iota>A(m-1).
     n\<cdot>h \<in> \<langle>2\<beta>\<rangle> means n\<cdot>c_i = 2k for all i (some k).
     So c_0 = ... = c_{m-1}, i.e., h = c\<cdot>\<beta>.
     Order of c\<cdot>\<beta> mod 2\<beta>: if c odd, order 2; if c even, h \<in> \<langle>2\<beta>\<rangle>, so class is e.
     Torsion = {e, \<beta>} has order 2.\<close>

  \<comment> \<open>Step 13-14: The torsion and free part follow from the isomorphism
     Abel(G_0) \<cong> Abel(F)/\<langle>2\<beta>\<rangle> and the structure of this quotient.
     In Z^m / \<langle>2(\<alpha>_0+...+\<alpha>_{m-1})\<rangle>:
     - Torsion = {0, \<beta>} where \<beta> = \<alpha>_0+...+\<alpha>_{m-1} (order 2), card = 2.
     - Free part K = image of \<langle>\<alpha>_0,...,\<alpha>_{m-2}\<rangle>, rank m-1.
     - K \<inter> torsion = {0}, every element decomposes as k + t.\<close>

  \<comment> \<open>m \<ge> 1 from the definition of m-fold projective.\<close>
  have hm1: "m \<ge> 1"
    using assms(1) unfolding top1_is_m_fold_projective_on_def by (by100 auto)

  \<comment> \<open>The relator image in Abel(F): p(relator) = \<iota>A(0)^2 \<cdot> ... \<cdot> \<iota>A(m-1)^2.
     In the abelian group, this equals (product of all generators)^2.\<close>
  \<comment> \<open>Define \<beta> = product of all generators in Abel(F).\<close>
  let ?\<beta>_list = "map ?\<iota>A [0..<m]"
  let ?\<beta>A = "foldr ?mulA ?\<beta>_list ?eA"

  \<comment> \<open>\<beta> \<in> AbelF.\<close>
  have h\<iota>A_in: "\<forall>s\<in>{..<m}. ?\<iota>A s \<in> ?AbelF"
    using h\<iota>A unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  have h\<beta>_in: "?\<beta>A \<in> ?AbelF"
  proof -
    have "\<forall>i < length (map ?\<iota>A [0..<m]). (map ?\<iota>A [0..<m]) ! i \<in> ?AbelF"
      using h\<iota>A_in by (by100 auto)
    thus ?thesis using foldr_mul_closed[OF hAbelF_grp] by (by100 blast)
  qed

  \<comment> \<open>The relator image equals \<beta>^2 in Abel(F).\<close>
  \<comment> \<open>The p-image of the relator equals \<beta>^2 in Abel(F).
     Strategy: p is a hom, so p(word\_product) = word\_product in AbelF.
     Then in abelian AbelF: a0^2*a1^2*...*a_{m-1}^2 = (a0*a1*...*a_{m-1})^2
     by foldr\_mul\_append + induction.\<close>
  have hrel_eq_\<beta>2: "?rel_in_AbelF = ?mulA ?\<beta>A ?\<beta>A"
  proof -
    \<comment> \<open>The p-image of a word product in F equals the corresponding word product in AbelF.\<close>
    have hpF_hom: "top1_group_hom_on F mulF ?AbelF ?mulA ?p"
      using quotient_projection_properties(1)[OF hF_grp hCF_normal] by (by100 simp)
    \<comment> \<open>rel\_in\_AbelF = p(rel\_in\_F). We compute this via the word product structure.
       The relator scheme has all True entries, so word\_product = foldr of generators.
       After applying p: each ι(i) maps to ιA(i) = p(ι(i)).\<close>
    \<comment> \<open>Step 1: Show rel\_in\_AbelF = foldr mulA (concat (map (\<lambda>i. [ιA i, ιA i]) [0..<m])) eA.\<close>
    \<comment> \<open>The relator scheme with all True entries produces a specific word product.
       For True-only entries: word\_product = foldr mul (map fst ws) e.
       The relator scheme maps (λi. [(i,T),(i,T)]) over [0..<m] and concatenates.\<close>
    have wp_true_gen: "\<And>mul' e' invg' f xs.
        top1_group_word_product mul' e' invg'
          (concat (map (\<lambda>i. [(f i, True), (f i, True)]) xs))
      = foldr mul' (concat (map (\<lambda>i. [f i, f i]) xs)) e'"
      by (rule list.induct, by100 simp, by100 simp)
    \<comment> \<open>rel\_in\_F as foldr in F.\<close>
    have hrel_foldr_F: "?rel_in_F = foldr mulF (concat (map (\<lambda>i. [\<iota> i, \<iota> i]) [0..<m])) eF"
    proof -
      have "map (\<lambda>(s,b). (\<iota> s, b)) ?relator = concat (map (\<lambda>i. [(\<iota> i, True), (\<iota> i, True)]) [0..<m])"
        by (induct m, by100 simp, by100 simp)
      thus ?thesis using wp_true_gen[of mulF eF invgF \<iota> "[0..<m]"] by (by100 simp)
    qed
    \<comment> \<open>p preserves foldr products.\<close>
    have hrel_all_in_F: "\<forall>i<length (concat (map (\<lambda>i. [\<iota> i, \<iota> i]) [0..<m])).
        (concat (map (\<lambda>i. [\<iota> i, \<iota> i]) [0..<m])) ! i \<in> F"
    proof (intro allI impI)
      fix i assume "i < length (concat (map (\<lambda>i. [\<iota> i, \<iota> i]) [0..<m]))"
      have "set (concat (map (\<lambda>i. [\<iota> i, \<iota> i]) [0..<m])) \<subseteq> \<iota> ` {..<m}"
        by (by100 auto)
      hence "(concat (map (\<lambda>i. [\<iota> i, \<iota> i]) [0..<m])) ! i \<in> \<iota> ` {..<m}"
        using nth_mem \<open>i < length _\<close> by (by100 blast)
      thus "(concat (map (\<lambda>i. [\<iota> i, \<iota> i]) [0..<m])) ! i \<in> F"
      proof -
        assume h: "(concat (map (\<lambda>i. [\<iota> i, \<iota> i]) [0..<m])) ! i \<in> \<iota> ` {..<m}"
        have "\<iota> ` {..<m} \<subseteq> F"
          using hF_free unfolding top1_is_free_group_full_on_def by (by100 blast)
        thus ?thesis using h by (by100 blast)
      qed
    qed
    have "?p ?rel_in_F = ?p (foldr mulF (concat (map (\<lambda>i. [\<iota> i, \<iota> i]) [0..<m])) eF)"
      using hrel_foldr_F by (by100 simp)
    also have "\<dots> = foldr ?mulA (map ?p (concat (map (\<lambda>i. [\<iota> i, \<iota> i]) [0..<m]))) ?eA"
      using hom_foldr_mul[OF hF_grp hAbelF_grp hpF_hom hrel_all_in_F] by (by100 blast)
    also have "map ?p (concat (map (\<lambda>i. [\<iota> i, \<iota> i]) [0..<m]))
        = concat (map (\<lambda>i. [?\<iota>A i, ?\<iota>A i]) [0..<m])"
      by (induct m, by100 simp, by100 simp)
    finally have hstep1: "?rel_in_AbelF = foldr ?mulA (concat (map (\<lambda>i. [?\<iota>A i, ?\<iota>A i]) [0..<m])) ?eA"
      by (by100 simp)
    \<comment> \<open>Step 2: Apply abelian\_foldr\_concat\_double to get β².\<close>
    also have "\<dots> = ?mulA ?\<beta>A ?\<beta>A"
    proof -
      have "\<forall>i<length (map ?\<iota>A [0..<m]). (map ?\<iota>A [0..<m]) ! i \<in> ?AbelF"
        using h\<iota>A_in by (by100 auto)
      hence hcd: "foldr ?mulA (concat (map (\<lambda>x. [x, x]) (map ?\<iota>A [0..<m]))) ?eA
          = ?mulA (foldr ?mulA (map ?\<iota>A [0..<m]) ?eA) (foldr ?mulA (map ?\<iota>A [0..<m]) ?eA)"
        using abelian_foldr_concat_double[OF hAbelF_abel] by (by100 blast)
      have "concat (map (\<lambda>i. [?\<iota>A i, ?\<iota>A i]) [0..<m])
          = concat (map (\<lambda>x. [x, x]) (map ?\<iota>A [0..<m]))"
        by (induct m, by100 simp, by100 simp)
      thus ?thesis using hcd by (by100 simp)
    qed
    finally show ?thesis .
  qed

  \<comment> \<open>\<phi>_bar(\<beta>) is a torsion element of order exactly 2 in Abel(G_0).\<close>
  let ?\<beta>G = "\<phi>_bar ?\<beta>A"

  have h\<beta>G_in: "?\<beta>G \<in> ?AbelG"
    using h\<phi>_hom h\<beta>_in unfolding top1_group_hom_on_def by (by100 blast)

  have h\<beta>G_order2: "?mulAG ?\<beta>G ?\<beta>G = ?eAG"
  proof -
    \<comment> \<open>\<phi>_bar(\<beta>^2) = \<phi>_bar(rel\_image) = eAG (since rel\_image \<in> ker(\<phi>_bar)).\<close>
    have "\<phi>_bar (?mulA ?\<beta>A ?\<beta>A) = ?mulAG (\<phi>_bar ?\<beta>A) (\<phi>_bar ?\<beta>A)"
      using h\<phi>_hom h\<beta>_in unfolding top1_group_hom_on_def by (by100 blast)
    moreover have "\<phi>_bar (?mulA ?\<beta>A ?\<beta>A) = ?eAG"
    proof -
      have "?rel_in_AbelF \<in> ?N_AbelF"
        unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
      hence "?rel_in_AbelF \<in> top1_group_kernel_on ?AbelF ?eAG \<phi>_bar"
        using hker_\<phi> by (by100 simp)
      hence "\<phi>_bar ?rel_in_AbelF = ?eAG"
        unfolding top1_group_kernel_on_def by (by100 blast)
      thus ?thesis using hrel_eq_\<beta>2 by (by100 simp)
    qed
    ultimately show ?thesis by (by100 simp)
  qed

  have h\<beta>A_ne: "?\<beta>A \<noteq> ?eA"
  proof -
    \<comment> \<open>\<beta> = word\_product of [(0,True),...,(m-1,True)] via \<iota>A.
       No matching True/False pairs, non-empty (m\<ge>1).
       By no\_matching\_pair\_word\_ne\_e, \<beta> \<noteq> eA.\<close>
    let ?w = "map (\<lambda>i. (i, True)) [0..<m]"
    have "top1_group_word_product ?mulA ?eA ?invgA (map (\<lambda>(s,b). (?\<iota>A s, b)) ?w) \<noteq> ?eA"
    proof (rule no_matching_pair_word_ne_e[OF h\<iota>A])
      show "\<forall>s\<in>fst ` set ?w. s \<in> {..<m}" by (by100 auto)
      show "?w \<noteq> []" using hm1 by (by100 auto)
      show "\<forall>s b. (s, b) \<in> set ?w \<longrightarrow> (s, \<not>b) \<notin> set ?w" by (by100 auto)
    qed
    moreover have "top1_group_word_product ?mulA ?eA ?invgA (map (\<lambda>(s,b). (?\<iota>A s, b)) ?w) = ?\<beta>A"
    proof -
      have wp_true: "\<And>f xs. top1_group_word_product ?mulA ?eA ?invgA
          (map (\<lambda>i. (f i, True)) xs) = foldr ?mulA (map f xs) ?eA"
        by (rule list.induct, by100 simp, by100 simp)
      have hmap: "map (\<lambda>(s,b). (?\<iota>A s, b)) ?w = map (\<lambda>i. (?\<iota>A i, True)) [0..<m]"
        by (by100 auto)
      show ?thesis unfolding hmap using wp_true[of ?\<iota>A "[0..<m]"] by (by100 simp)
    qed
    ultimately show ?thesis by (by100 simp)
  qed
  have h\<beta>G_ne: "?\<beta>G \<noteq> ?eAG"
  proof -
    \<comment> \<open>\<beta> \<notin> N\_AbelF (the subgroup generated by 2\<beta>).
       If \<beta> \<in> N\_AbelF = ker(\<phi>\_bar), then \<phi>\_bar(\<beta>) = eAG.
       But N\_AbelF = \<langle>2\<beta>\<rangle>, so \<beta> = 2k\<cdot>\<beta> for some k.
       Since \<beta> \<noteq> eA (proved above), k \<noteq> 0.
       But (2k-1)\<cdot>\<beta> = eA contradicts free abelian independence.\<close>
    have "?\<beta>A \<notin> ?N_AbelF"
    proof -
      \<comment> \<open>Use coordinate projection: \<epsilon>: AbelF \<rightarrow> Z with \<epsilon>(\<iota>A(0)) = 1, \<epsilon>(\<iota>A(i)) = 0 for i > 0.
         Then \<epsilon>(\<beta>) = 1 (odd), \<epsilon>(rel) = 2 (even).
         The subgroup {g | \<epsilon>(g) even} contains rel but not \<beta>.
         So \<beta> \<notin> normal\_closure({rel}).\<close>
      have "0 \<in> ({..<m}::nat set)" using hm1 by (by100 simp)
      from free_abelian_coordinate_projection[OF h\<iota>A this]
      obtain \<epsilon> where h\<epsilon>_hom: "top1_group_hom_on ?AbelF ?mulA (UNIV::int set) (+) \<epsilon>"
        and h\<epsilon>_0: "\<epsilon> (?\<iota>A 0) = 1"
        and h\<epsilon>_rest: "\<forall>s\<in>{..<m}. s \<noteq> 0 \<longrightarrow> \<epsilon> (?\<iota>A s) = 0"
        by (by100 blast)
      \<comment> \<open>\<epsilon>(\<beta>) = \<epsilon>(\<iota>A(0) \<cdot> ... \<cdot> \<iota>A(m-1)) = \<epsilon>(\<iota>A(0)) + ... = 1.\<close>
      have h\<epsilon>_\<beta>: "\<epsilon> ?\<beta>A = 1"
      proof -
        have hZ_grp: "top1_is_group_on (UNIV::int set) (+) 0 uminus"
          using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
            top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def
          by (by100 blast)
        have "\<forall>i < length ?\<beta>_list. ?\<beta>_list ! i \<in> ?AbelF"
          using h\<iota>A_in by (by100 auto)
        hence "\<epsilon> ?\<beta>A = foldr (+) (map \<epsilon> ?\<beta>_list) (0::int)"
          using hom_foldr_mul[OF hAbelF_grp hZ_grp h\<epsilon>_hom] by (by100 blast)
        also have "\<dots> = foldr (+) (map (\<epsilon> \<circ> ?\<iota>A) [0..<m]) 0" by (by100 simp)
        also have "\<dots> = 1"
        proof -
          have hmap_eq: "map (\<epsilon> \<circ> ?\<iota>A) [0..<m] = map (\<lambda>i::nat. if i = 0 then (1::int) else 0) [0..<m]"
            using h\<epsilon>_0 h\<epsilon>_rest by (by100 auto)
          have "foldr (+) (map (\<lambda>i::nat. if i = 0 then (1::int) else 0) [0..<m]) 0 = 1"
            using hm1 by (induct m, by100 simp, by100 simp)
          thus ?thesis unfolding hmap_eq[symmetric] by (by100 simp)
        qed
        finally show ?thesis .
      qed
      \<comment> \<open>\<epsilon>(rel) = \<epsilon>(\<beta>^2) = 2\<epsilon>(\<beta>) = 2 (if hrel\_eq\_\<beta>2 is proved).
         But more directly: \<epsilon>(rel) = 2 from the relator being each generator squared.\<close>
      have h\<epsilon>_rel: "\<epsilon> ?rel_in_AbelF = 2"
      proof -
        have "\<epsilon> ?rel_in_AbelF = \<epsilon> (?mulA ?\<beta>A ?\<beta>A)" using hrel_eq_\<beta>2 by (by100 simp)
        also have "\<dots> = \<epsilon> ?\<beta>A + \<epsilon> ?\<beta>A"
          using h\<epsilon>_hom h\<beta>_in unfolding top1_group_hom_on_def by (by100 blast)
        also have "\<dots> = 2" using h\<epsilon>_\<beta> by (by100 simp)
        finally show ?thesis .
      qed
      \<comment> \<open>If \<beta> \<in> N\_AbelF = \<langle>rel\<rangle>, then \<epsilon>(\<beta>) \<in> \<epsilon>(N\_AbelF).
         \<epsilon>(N\_AbelF) \<subseteq> \<langle>\<epsilon>(rel)\<rangle> = 2Z. But \<epsilon>(\<beta>) = 1 \<notin> 2Z.\<close>
      have h\<epsilon>_N: "\<forall>x \<in> ?N_AbelF. even (\<epsilon> x)"
      proof -
        \<comment> \<open>The set M = {g \<in> AbelF. even(\<epsilon>(g))} is a normal subgroup containing rel.\<close>
        let ?M = "{g \<in> ?AbelF. even (\<epsilon> g)}"
        have hM_normal: "top1_normal_subgroup_on ?AbelF ?mulA ?eA ?invgA ?M"
        proof -
          have h2Z_normal: "top1_normal_subgroup_on (UNIV::int set) (+) 0 uminus {n::int. even n}"
            unfolding top1_normal_subgroup_on_def top1_is_group_on_def
            by (by100 fastforce)
          have "?M = {g \<in> ?AbelF. \<epsilon> g \<in> {n::int. even n}}" by (by100 auto)
          have hZ_grp2: "top1_is_group_on (UNIV::int set) (+) 0 uminus"
            using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
              top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def
            by (by100 blast)
          thus ?thesis using preimage_normal_subgroup[OF hAbelF_grp hZ_grp2 h\<epsilon>_hom h2Z_normal]
            by (by100 simp)
        qed
        have hrel_in_M: "?rel_in_AbelF \<in> ?M"
          using hN_in_AbelF h\<epsilon>_rel by (by100 auto)
        have "{?rel_in_AbelF} \<subseteq> ?M" using hrel_in_M by (by100 blast)
        have "?N_AbelF \<subseteq> ?M"
          using normal_closure_least[OF hAbelF_grp hM_normal \<open>{?rel_in_AbelF} \<subseteq> ?M\<close>]
          by (by100 simp)
        thus ?thesis by (by100 blast)
      qed
      from h\<epsilon>_N h\<epsilon>_\<beta> show ?thesis by (by100 auto)
    qed
    hence "?\<beta>A \<notin> top1_group_kernel_on ?AbelF ?eAG \<phi>_bar"
      using hker_\<phi> by (by100 simp)
    hence "\<phi>_bar ?\<beta>A \<noteq> ?eAG"
    proof (rule contrapos_nn)
      assume "\<phi>_bar ?\<beta>A = ?eAG"
      thus "?\<beta>A \<in> top1_group_kernel_on ?AbelF ?eAG \<phi>_bar"
        using h\<beta>_in unfolding top1_group_kernel_on_def by (by100 blast)
    qed
    thus ?thesis by (by100 simp)
  qed

  \<comment> \<open>Step 14 (moved before torsion classification per expert audit 11):
     The free part K generated by \<phi>\_bar(\<iota>A(Suc i)) for i < m-1.
     Once K and the decomposition are established, torsion classification follows.\<close>

  \<comment> \<open>Define K generators: \<gamma>(i) = \<phi>\_bar(\<iota>A(Suc i)) for i < m-1.\<close>
  let ?\<gamma> = "\<lambda>i. \<phi>_bar (?\<iota>A (Suc i))"

  \<comment> \<open>Use the coordinate projection \<epsilon>_0 (already obtained above for \<beta>\<noteq>e proof).
     K_0 = ker(\<epsilon>_0) in AbelF is free abelian on {..<m}-{0} by free\_abelian\_kernel\_coordinate.
     K = \<phi>\_bar(K_0) in AbelG is the desired free complement.\<close>
  \<comment> \<open>Step A: Obtain coordinate projection \<epsilon>_0 at the proof level (not inside a block).\<close>
  have "0 \<in> ({..<m}::nat set)" using hm1 by (by100 simp)
  from free_abelian_coordinate_projection[OF h\<iota>A this]
  obtain \<epsilon>0 where h\<epsilon>0_hom: "top1_group_hom_on ?AbelF ?mulA (UNIV::int set) (+) \<epsilon>0"
    and h\<epsilon>0_0: "\<epsilon>0 (?\<iota>A 0) = 1"
    and h\<epsilon>0_rest: "\<forall>s\<in>{..<m}. s \<noteq> 0 \<longrightarrow> \<epsilon>0 (?\<iota>A s) = 0"
    by (by100 blast)

  \<comment> \<open>Step B: K_0 = ker(\<epsilon>_0) is free abelian on {..<m}-{0}.\<close>
  let ?K0 = "{a \<in> ?AbelF. \<epsilon>0 a = 0}"
  have hK0_fab: "top1_is_free_abelian_group_full_on ?K0 ?mulA ?eA ?invgA ?\<iota>A ({..<m} - {0::nat})"
    using free_abelian_kernel_coordinate[OF h\<iota>A \<open>0 \<in> {..<m}\<close> h\<epsilon>0_hom h\<epsilon>0_0 h\<epsilon>0_rest] by (by100 simp)

  \<comment> \<open>K_0 is a group (from free abelian).\<close>
  have hK0_grp_outer: "top1_is_group_on ?K0 ?mulA ?eA ?invgA"
    using hK0_fab unfolding top1_is_free_abelian_group_full_on_def
      top1_is_abelian_group_on_def by (by100 blast)

  \<comment> \<open>Step C: \<phi>\_bar maps K_0 into AbelG. Define K = \<phi>\_bar ` K_0.\<close>
  let ?K = "\<phi>_bar ` ?K0"

  \<comment> \<open>Step D: K \<subseteq> AbelG.\<close>
  have hK_sub: "?K \<subseteq> ?AbelG"
    using h\<phi>_hom unfolding top1_group_hom_on_def by (by100 blast)

  \<comment> \<open>Step E: \<phi>\_bar restricted to K_0 is injective: ker(\<phi>\_bar) \<cap> K_0 = {eA}.
     ker(\<phi>\_bar) = N\_AbelF \<subseteq> {a | even(\<epsilon>_0(a))} but K_0 = {a | \<epsilon>_0(a)=0}.
     So ker \<cap> K_0 = {a \<in> K_0 | a \<in> N\_AbelF}.
     If a \<in> K_0 \<cap> N\_AbelF, then \<epsilon>_0(a) = 0 and a \<in> \<langle>rel\<rangle>.
     Since \<epsilon>_0(\<beta>) = 1, elements of \<langle>\<beta>^2\<rangle> have \<epsilon>_0 value in 2Z.
     a \<in> K_0 means \<epsilon>_0(a) = 0, so a = pow(\<beta>^2, 0) = eA.\<close>
  \<comment> \<open>Re-derive \<epsilon>_0(\<beta>) = 1 at this level (was proved inside \<beta>\<noteq>e proof block).\<close>
  have h\<epsilon>0_\<beta>: "\<epsilon>0 ?\<beta>A = 1"
  proof -
    have hZ_grp: "top1_is_group_on (UNIV::int set) (+) 0 uminus"
      using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
        top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 blast)
    have "\<forall>i < length ?\<beta>_list. ?\<beta>_list ! i \<in> ?AbelF"
      using h\<iota>A_in by (by100 auto)
    hence "\<epsilon>0 ?\<beta>A = foldr (+) (map \<epsilon>0 ?\<beta>_list) (0::int)"
      using hom_foldr_mul[OF hAbelF_grp hZ_grp h\<epsilon>0_hom] by (by100 blast)
    also have "\<dots> = foldr (+) (map (\<epsilon>0 \<circ> ?\<iota>A) [0..<m]) 0" by (by100 simp)
    also have "\<dots> = 1"
    proof -
      have hmap_eq: "map (\<epsilon>0 \<circ> ?\<iota>A) [0..<m] = map (\<lambda>i::nat. if i = 0 then (1::int) else 0) [0..<m]"
        using h\<epsilon>0_0 h\<epsilon>0_rest by (by100 auto)
      have "foldr (+) (map (\<lambda>i::nat. if i = 0 then (1::int) else 0) [0..<m]) 0 = 1"
        using hm1 by (induct m, by100 simp, by100 simp)
      thus ?thesis unfolding hmap_eq[symmetric] by (by100 simp)
    qed
    finally show ?thesis .
  qed
  have h\<epsilon>0_rel: "\<epsilon>0 ?rel_in_AbelF = 2"
  proof -
    have "\<epsilon>0 ?rel_in_AbelF = \<epsilon>0 (?mulA ?\<beta>A ?\<beta>A)" using hrel_eq_\<beta>2 by (by100 simp)
    also have "\<dots> = \<epsilon>0 ?\<beta>A + \<epsilon>0 ?\<beta>A"
      using h\<epsilon>0_hom h\<beta>_in unfolding top1_group_hom_on_def by (by100 blast)
    also have "\<dots> = 2" using h\<epsilon>0_\<beta> by (by100 simp)
    finally show ?thesis .
  qed
  have hK0_ker_trivial: "{a \<in> ?AbelF. \<epsilon>0 a = 0} \<inter> ?N_AbelF = {?eA}"
  proof (rule set_eqI, rule iffI)
    fix a assume ha: "a \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0} \<inter> ?N_AbelF"
    hence ha_in: "a \<in> ?AbelF" and h\<epsilon>0a: "\<epsilon>0 a = 0" and ha_N: "a \<in> ?N_AbelF" by (by100 blast)+
    \<comment> \<open>a \<in> N\_AbelF. By subgroup\_generated\_word\_repr (abelian group version):
       a is a word in {rel, invg(rel)}. In abelian group this means
       a = pow(rel, k) for some k \<ge> 0, or a = pow(invg(rel), k).
       Either way, \<epsilon>_0(a) = \<plusminus>k \<cdot> \<epsilon>_0(rel) = \<plusminus>2k.
       Since \<epsilon>_0(a) = 0, k = 0, so a = eA.\<close>
    \<comment> \<open>Use the preimage approach: {a \<in> AbelF | \<epsilon>_0(a) = 0} is a normal subgroup
       that does NOT contain rel (since \<epsilon>_0(rel) = 2 \<noteq> 0).
       N\_AbelF = normal\_closure({rel}). If a \<in> N\_AbelF \<cap> ker(\<epsilon>_0), then
       \<epsilon>_0(a) = 0 but a is in the smallest normal subgroup containing rel.
       Key: \<epsilon>_0 restricted to N\_AbelF is injective (since \<epsilon>_0(rel) generates 2Z
       and the map from N\_AbelF to 2Z is injective for cyclic groups).\<close>
    \<comment> \<open>a \<in> N\_AbelF = normal\_closure({rel}) \<subseteq> subgroup\_generated({rel}).
       By subgroup\_generated\_word\_repr: a = eA or a = foldr mulA ws eA
       where each ws!i \<in> {rel, invgA(rel)}.
       Then \<epsilon>_0(a) = sum of \<epsilon>_0(ws!i) = sum of \<plusminus>2 = 2k.
       Since \<epsilon>_0(a) = 0, k = 0, and a = eA.\<close>
    have hN_sub_sg: "?N_AbelF \<subseteq> top1_subgroup_generated_on ?AbelF ?mulA ?eA ?invgA {?rel_in_AbelF}"
    proof -
      \<comment> \<open>In abelian group: every subgroup is normal, so subgroup\_generated = normal\_generated.
         normal\_generated = \<Inter>{N | S\<subseteq>N, N normal}, subgroup\_generated = \<Inter>{H | S\<subseteq>H, H subgroup}.
         Since normal \<Longrightarrow> subgroup: {N|normal} \<supseteq> ... and in abelian: subgroup \<Longrightarrow> normal.\<close>
      \<comment> \<open>subgroup\_generated({rel}) is a normal subgroup of AbelF (abelian group).
         Since N\_AbelF is the \<Inter> of all normal subgroups containing {rel},
         and subgroup\_generated is one such, N\_AbelF \<subseteq> subgroup\_generated.\<close>
      have "top1_normal_subgroup_on ?AbelF ?mulA ?eA ?invgA
          (top1_subgroup_generated_on ?AbelF ?mulA ?eA ?invgA {?rel_in_AbelF})"
      proof (rule abelian_subgroup_is_normal[OF hAbelF_abel])
        show "top1_subgroup_generated_on ?AbelF ?mulA ?eA ?invgA {?rel_in_AbelF} \<subseteq> ?AbelF"
          using subgroup_generated_subset[OF hAbelF_grp] hN_in_AbelF by (by100 blast)
        show "top1_is_group_on (top1_subgroup_generated_on ?AbelF ?mulA ?eA ?invgA {?rel_in_AbelF})
            ?mulA ?eA ?invgA"
          using intersection_of_subgroups_is_group[OF hAbelF_grp] hN_in_AbelF by (by100 blast)
      qed
      moreover have "{?rel_in_AbelF} \<subseteq> top1_subgroup_generated_on ?AbelF ?mulA ?eA ?invgA {?rel_in_AbelF}"
        using subgroup_generated_contains[OF hAbelF_grp] hN_in_AbelF by (by100 blast)
      ultimately show ?thesis
        unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
    qed
    hence "a \<in> top1_subgroup_generated_on ?AbelF ?mulA ?eA ?invgA {?rel_in_AbelF}"
      using ha_N by (by100 blast)
    hence "a = ?eA \<or> (\<exists>ws. length ws > 0
        \<and> (\<forall>i<length ws. ws!i \<in> {?rel_in_AbelF} \<or> (\<exists>s\<in>{?rel_in_AbelF}. ws!i = ?invgA s))
        \<and> foldr ?mulA ws ?eA = a)"
      using subgroup_generated_word_repr[OF hAbelF_grp] hN_in_AbelF by (by100 blast)
    thus "a \<in> {?eA}"
    proof (elim disjE)
      assume "a = ?eA" thus ?thesis by (by100 blast)
    next
      assume "\<exists>ws. length ws > 0
        \<and> (\<forall>i<length ws. ws!i \<in> {?rel_in_AbelF} \<or> (\<exists>s\<in>{?rel_in_AbelF}. ws!i = ?invgA s))
        \<and> foldr ?mulA ws ?eA = a"
      then obtain ws where hlen: "length ws > 0"
        and hws: "\<forall>i<length ws. ws!i \<in> {?rel_in_AbelF} \<or> (\<exists>s\<in>{?rel_in_AbelF}. ws!i = ?invgA s)"
        and hprod: "foldr ?mulA ws ?eA = a" by (by100 blast)
      \<comment> \<open>Each ws!i is rel or invgA(rel). \<epsilon>_0(rel) = 2, \<epsilon>_0(invgA(rel)) = -2.
         So \<epsilon>_0(foldr mulA ws eA) = sum of \<plusminus>2 = 2k for some k.
         Since \<epsilon>_0(a) = 0, this sum = 0.\<close>
      \<comment> \<open>But also: foldr mulA ws eA = a and \<epsilon>_0(a) = 0.
         In the free abelian group, a = 0 iff all coordinates are 0.
         Here a \<in> N\_AbelF which is generated by {rel = \<beta>\<twosuperior>}.
         Since \<epsilon>_0(\<beta>\<twosuperior>) = 2 and the group is free abelian,
         pow(\<beta>\<twosuperior>, k) = 0 iff k = 0.\<close>
      \<comment> \<open>Apply \<epsilon>_0 to both sides of hprod: \<epsilon>_0(a) = \<epsilon>_0(foldr mulA ws eA).
         Each ws!i is rel or invgA(rel), so \<epsilon>_0(ws!i) \<in> {2, -2}.
         Sum = 0 means equal counts of rel and invg(rel).
         In abelian group, paired rel\<cdot>invg(rel) cancel to eA.\<close>
      \<comment> \<open>All ws elements are in AbelF.\<close>
      have hws_in: "\<forall>i<length ws. ws!i \<in> ?AbelF"
      proof (intro allI impI)
        fix i assume hi: "i < length ws"
        from hws hi have "ws!i \<in> {?rel_in_AbelF} \<or> (\<exists>s\<in>{?rel_in_AbelF}. ws!i = ?invgA s)"
          by (by100 blast)
        thus "ws!i \<in> ?AbelF"
        proof (elim disjE)
          assume "ws!i \<in> {?rel_in_AbelF}"
          thus ?thesis using hN_in_AbelF by (by100 blast)
        next
          assume "\<exists>s\<in>{?rel_in_AbelF}. ws!i = ?invgA s"
          then obtain s where "s \<in> {?rel_in_AbelF}" "ws!i = ?invgA s" by (by100 blast)
          hence "s \<in> ?AbelF" using hN_in_AbelF by (by100 blast)
          have "?invgA s \<in> ?AbelF" using hAbelF_invg_cl \<open>s \<in> ?AbelF\<close> by (by100 blast)
          thus ?thesis using \<open>ws!i = ?invgA s\<close> by (by100 simp)
        qed
      qed
      \<comment> \<open>Apply \<epsilon>_0 to hprod.\<close>
      have hZ_grp: "top1_is_group_on (UNIV::int set) (+) 0 uminus"
        using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
          top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 blast)
      have "\<epsilon>0 a = \<epsilon>0 (foldr ?mulA ws ?eA)" using hprod by (by100 simp)
      also have "\<dots> = foldr (+) (map \<epsilon>0 ws) (0::int)"
        using hom_foldr_mul[OF hAbelF_grp hZ_grp h\<epsilon>0_hom hws_in] by (by100 blast)
      finally have hsum: "foldr (+) (map \<epsilon>0 ws) (0::int) = 0" using h\<epsilon>0a by (by100 simp)
      \<comment> \<open>Each \<epsilon>_0(ws!i) \<in> {2, -2}. Sum = 0 means equal counts.
         In abelian group with equal rel/invrel counts, product = eA.\<close>
      \<comment> \<open>Use abelian\_word\_product\_zero\_net\_coeff with a single-generator word.
         Label type: unit. phi () = rel. Word: map (\<lambda>x. ((), x = rel)) ws.\<close>
      have hrel_ne_invrel_outer: "?invgA ?rel_in_AbelF \<noteq> ?rel_in_AbelF"
      proof
        assume heq: "?invgA ?rel_in_AbelF = ?rel_in_AbelF"
        have "\<epsilon>0 (?invgA ?rel_in_AbelF) = -2"
        proof -
          have hZ_grp: "top1_is_group_on (UNIV::int set) (+) 0 uminus"
            using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
              top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 blast)
          have hrel_in: "?rel_in_AbelF \<in> ?AbelF" using hN_in_AbelF by (by100 blast)
          have "\<epsilon>0 (?invgA ?rel_in_AbelF) = uminus (\<epsilon>0 ?rel_in_AbelF)"
            using hom_preserves_inv[OF hAbelF_grp hZ_grp h\<epsilon>0_hom hrel_in] by (by100 simp)
          thus ?thesis using h\<epsilon>0_rel by (by100 simp)
        qed
        moreover have "\<epsilon>0 ?rel_in_AbelF = 2" using h\<epsilon>0_rel .
        ultimately have "(-2::int) = 2" using heq by (by100 simp)
        thus False by (by100 simp)
      qed
      let ?w = "map (\<lambda>x. (()::unit, x = ?rel_in_AbelF)) ws"
      let ?\<phi>w = "\<lambda>_::unit. ?rel_in_AbelF"
      have "top1_group_word_product ?mulA ?eA ?invgA (map (\<lambda>(s,b). (?\<phi>w s, b)) ?w) = ?eA"
      proof (rule abelian_word_product_zero_net_coeff[OF hAbelF_abel])
        show "\<forall>s \<in> fst ` set ?w. ?\<phi>w s \<in> ?AbelF"
          using hN_in_AbelF by (by100 auto)
        show "\<forall>s. length (filter (\<lambda>(t,b). t = s \<and> b) ?w)
            = length (filter (\<lambda>(t,b). t = s \<and> \<not>b) ?w)"
        proof (intro allI)
          fix s :: unit
          \<comment> \<open>All first components are (), so the filter simplifies.\<close>
          have "filter (\<lambda>(t,b). t = s \<and> b) ?w = filter (\<lambda>(t,b). b) ?w"
            by (by100 auto)
          moreover have "filter (\<lambda>(t,b). t = s \<and> \<not>b) ?w = filter (\<lambda>(t,b). \<not>b) ?w"
            by (by100 auto)
          moreover have "length (filter (\<lambda>(t,b). b) ?w) = length (filter (\<lambda>(t,b). \<not>b) ?w)"
          proof -
            \<comment> \<open>The boolean map: ws!i = rel iff (map (\<lambda>x. x=rel) ws)!i = True.\<close>
            let ?bs = "map (\<lambda>x. x = ?rel_in_AbelF) ws"
            \<comment> \<open>Connect \<epsilon>_0 sum to balanced\_from\_sum\_zero.\<close>
            have h\<epsilon>_invrel: "\<epsilon>0 (?invgA ?rel_in_AbelF) = -2"
            proof -
              have hZ_grp2: "top1_is_group_on (UNIV::int set) (+) 0 uminus"
                using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
                  top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 blast)
              have hrel_in: "?rel_in_AbelF \<in> ?AbelF" using hN_in_AbelF by (by100 blast)
              have "\<epsilon>0 (?invgA ?rel_in_AbelF) = uminus (\<epsilon>0 ?rel_in_AbelF)"
                using hom_preserves_inv[OF hAbelF_grp hZ_grp2 h\<epsilon>0_hom hrel_in] by (by100 simp)
              thus ?thesis using h\<epsilon>0_rel by (by100 simp)
            qed
            have hrel_ne_invrel: "?invgA ?rel_in_AbelF \<noteq> ?rel_in_AbelF"
            proof
              assume heq: "?invgA ?rel_in_AbelF = ?rel_in_AbelF"
              have "\<epsilon>0 (?invgA ?rel_in_AbelF) = -2" using h\<epsilon>_invrel .
              moreover have "\<epsilon>0 ?rel_in_AbelF = 2" using h\<epsilon>0_rel .
              ultimately have "(-2::int) = 2" using heq by (by100 simp)
              thus False by (by100 simp)
            qed
            have "map \<epsilon>0 ws = map (\<lambda>b. if b then (2::int) else -2) ?bs"
            proof (rule list_eq_iff_nth_eq[THEN iffD2], intro conjI allI impI)
              show "length (map \<epsilon>0 ws) = length (map (\<lambda>b. if b then (2::int) else -2) ?bs)"
                by (by100 simp)
              fix i assume hi: "i < length (map \<epsilon>0 ws)"
              hence hi': "i < length ws" by (by100 simp)
              from hws hi' have "ws!i \<in> {?rel_in_AbelF} \<or> (\<exists>s\<in>{?rel_in_AbelF}. ws!i = ?invgA s)"
                by (by100 blast)
              thus "map \<epsilon>0 ws ! i = map (\<lambda>b. if b then (2::int) else -2) ?bs ! i"
              proof (elim disjE)
                assume "ws!i \<in> {?rel_in_AbelF}"
                hence "ws!i = ?rel_in_AbelF" by (by100 blast)
                thus ?thesis using hi' h\<epsilon>0_rel by (by100 simp)
              next
                assume "\<exists>s\<in>{?rel_in_AbelF}. ws!i = ?invgA s"
                hence hwsi: "ws!i = ?invgA ?rel_in_AbelF" by (by100 blast)
                hence "(ws!i = ?rel_in_AbelF) = False" using hrel_ne_invrel by (by100 simp)
                thus ?thesis using hi' h\<epsilon>_invrel hwsi by (by100 simp)
              qed
            qed
            hence "foldr (+) (map (\<lambda>b. if b then (2::int) else -2) ?bs) 0 = 0"
              using hsum by (by100 simp)
            hence "length (filter id ?bs) = length (filter Not ?bs)"
              using balanced_from_sum_zero[of 2 ?bs] by (by100 simp)
            moreover have "length (filter id ?bs) = length (filter (\<lambda>(t,b). b) ?w)"
              unfolding id_def by (induct ws, by100 simp, by100 auto)
            moreover have "length (filter Not ?bs) = length (filter (\<lambda>(t,b). \<not>b) ?w)"
              by (induct ws, by100 simp, by100 auto)
            ultimately show ?thesis by (by100 linarith)
          qed
          ultimately show "length (filter (\<lambda>(t, b). t = s \<and> b) ?w) =
              length (filter (\<lambda>(t, b). t = s \<and> \<not> b) ?w)" by (by100 simp)
        qed
      qed
      moreover have "top1_group_word_product ?mulA ?eA ?invgA (map (\<lambda>(s,b). (?\<phi>w s, b)) ?w)
          = foldr ?mulA ws ?eA"
      proof -
        \<comment> \<open>map (\<lambda>(s,b). (\<phi>w s, b)) ?w = map (\<lambda>x. (rel, x = rel)) ws.
           word\_product processes True as mul(rel, ...) and False as mul(invgA(rel), ...).
           foldr mulA ws eA processes each ws!i directly.
           Since ws!i = rel when b=True and ws!i = invgA(rel) when b=False,
           the two are the same.\<close>
        have "\<And>xs. (\<forall>i<length xs. xs!i \<in> {?rel_in_AbelF} \<or> (\<exists>s\<in>{?rel_in_AbelF}. xs!i = ?invgA s)) \<Longrightarrow>
            top1_group_word_product ?mulA ?eA ?invgA
              (map (\<lambda>(s,b). (?\<phi>w s, b)) (map (\<lambda>x. (()::unit, x = ?rel_in_AbelF)) xs))
            = foldr ?mulA xs ?eA"
        proof -
          fix xs :: "int set list"
          assume hxs: "\<forall>i<length xs. xs!i \<in> {?rel_in_AbelF} \<or> (\<exists>s\<in>{?rel_in_AbelF}. xs!i = ?invgA s)"
          hence hxs': "\<forall>i<length xs. xs!i = ?rel_in_AbelF \<or> xs!i = ?invgA ?rel_in_AbelF"
            by (by100 blast)
          from word_product_rel_invrel_as_foldr[where g="?rel_in_AbelF" and invg="?invgA"
              and mul="?mulA" and e="?eA"]
          show "top1_group_word_product ?mulA ?eA ?invgA
              (map (\<lambda>(s,b). (?\<phi>w s, b)) (map (\<lambda>x. (()::unit, x = ?rel_in_AbelF)) xs))
            = foldr ?mulA xs ?eA"
            using hrel_ne_invrel_outer hxs' by (by100 blast)
        qed
        thus ?thesis using hws by (by100 blast)
      qed
      ultimately have "foldr ?mulA ws ?eA = ?eA" by (by100 simp)
      thus "a \<in> {?eA}" using hprod by (by100 blast)
    qed
  next
    fix a assume "a \<in> {?eA}"
    hence "a = ?eA" by (by100 blast)
    have "?eA \<in> ?AbelF" using hAbelF_grp unfolding top1_is_group_on_def by (by100 blast)
    have "\<epsilon>0 ?eA = 0"
    proof -
      have "top1_group_hom_on ?AbelF ?mulA (UNIV::int set) (+) \<epsilon>0" using h\<epsilon>0_hom .
      have hZ_grp: "top1_is_group_on (UNIV::int set) (+) 0 uminus"
        using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
          top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 blast)
      hence "\<epsilon>0 ?eA = (0::int)"
        using hom_preserves_id[OF hAbelF_grp hZ_grp h\<epsilon>0_hom] by (by100 simp)
      thus ?thesis by (by100 simp)
    qed
    have "?eA \<in> ?N_AbelF"
      using hN_normal unfolding top1_normal_subgroup_on_def top1_is_group_on_def
      by (by100 blast)
    show "a \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0} \<inter> ?N_AbelF"
      using \<open>a = ?eA\<close> \<open>?eA \<in> ?AbelF\<close> \<open>\<epsilon>0 ?eA = 0\<close> \<open>?eA \<in> ?N_AbelF\<close> by (by100 blast)
  qed


  have h\<phi>_inj_K0: "inj_on \<phi>_bar {a \<in> ?AbelF. \<epsilon>0 a = 0}"
  proof (rule inj_onI)
    fix a b assume ha: "a \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0}" and hb: "b \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0}"
       and heq: "\<phi>_bar a = \<phi>_bar b"
    have ha_in: "a \<in> ?AbelF" and hb_in: "b \<in> ?AbelF" using ha hb by (by100 blast)+
    \<comment> \<open>\<phi>\_bar(a \<cdot> b^{-1}) = \<phi>\_bar(a) \<cdot> \<phi>\_bar(b)^{-1} = eAG.\<close>
    have "?mulA a (?invgA b) \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0}"
    proof -
      have hinvb: "?invgA b \<in> ?AbelF" using hAbelF_invg_cl hb_in by (by100 blast)
      have hab_in: "?mulA a (?invgA b) \<in> ?AbelF"
        using hAbelF_mul_cl ha_in hinvb by (by100 blast)
      have "top1_is_group_on (UNIV::int set) (+) 0 uminus"
        using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
          top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 blast)
      hence h\<epsilon>_inv: "\<epsilon>0 (?invgA b) = - \<epsilon>0 b"
        using hom_preserves_inv[OF hAbelF_grp _ h\<epsilon>0_hom hb_in] by (by100 simp)
      have "\<epsilon>0 (?mulA a (?invgA b)) = \<epsilon>0 a + \<epsilon>0 (?invgA b)"
        using h\<epsilon>0_hom ha_in hinvb unfolding top1_group_hom_on_def by (by100 blast)
      also have "\<dots> = 0 + (- 0)" using ha hb h\<epsilon>_inv by (by100 simp)
      also have "\<dots> = 0" by (by100 simp)
      finally show ?thesis using hab_in by (by100 blast)
    qed
    moreover have "?mulA a (?invgA b) \<in> ?N_AbelF"
    proof -
      have hinvb: "?invgA b \<in> ?AbelF" using hAbelF_invg_cl hb_in by (by100 blast)
      have hab_in: "?mulA a (?invgA b) \<in> ?AbelF"
        using hAbelF_mul_cl ha_in hinvb by (by100 blast)
      \<comment> \<open>\<phi>\_bar is a hom, so \<phi>\_bar(a \<cdot> b^{-1}) = \<phi>\_bar(a) \<cdot> \<phi>\_bar(b)^{-1} = \<phi>\_bar(a) \<cdot> invgAG(\<phi>\_bar(b)).\<close>
      have "\<phi>_bar (?mulA a (?invgA b)) = ?mulAG (\<phi>_bar a) (\<phi>_bar (?invgA b))"
        using h\<phi>_hom ha_in hinvb unfolding top1_group_hom_on_def by (by100 blast)
      also have "\<phi>_bar (?invgA b) = ?invgAG (\<phi>_bar b)"
        using hom_preserves_inv[OF hAbelF_grp hAbelG_grp h\<phi>_hom hb_in] by (by100 simp)
      also have "?mulAG (\<phi>_bar a) (?invgAG (\<phi>_bar b)) = ?mulAG (\<phi>_bar a) (?invgAG (\<phi>_bar a))"
        using heq by (by100 simp)
      also have "\<dots> = ?eAG"
      proof -
        have "\<phi>_bar a \<in> ?AbelG"
          using h\<phi>_hom ha_in unfolding top1_group_hom_on_def by (by100 blast)
        from hAbelG_grp[unfolded top1_is_group_on_def] this
        show ?thesis by (by100 fast)
      qed
      finally have "\<phi>_bar (?mulA a (?invgA b)) = ?eAG" .
      hence "?mulA a (?invgA b) \<in> top1_group_kernel_on ?AbelF ?eAG \<phi>_bar"
        using hab_in unfolding top1_group_kernel_on_def by (by100 blast)
      thus ?thesis using hker_\<phi> by (by100 simp)
    qed
    ultimately have "?mulA a (?invgA b) = ?eA"
      using hK0_ker_trivial by (by100 blast)
    thus "a = b"
    proof -
      assume hab: "?mulA a (?invgA b) = ?eA"
      have hinvb: "?invgA b \<in> ?AbelF" using hAbelF_invg_cl hb_in by (by100 blast)
      \<comment> \<open>(a \<cdot> b^{-1}) \<cdot> b = e \<cdot> b = b. Also (a \<cdot> b^{-1}) \<cdot> b = a \<cdot> (b^{-1} \<cdot> b) = a \<cdot> e = a.\<close>
      have h1: "?mulA (?mulA a (?invgA b)) b = ?mulA a (?mulA (?invgA b) b)"
        using hAbelF_assoc ha_in hinvb hb_in by (by100 blast)
      have h2: "?mulA (?invgA b) b = ?eA" using hAbelF_inv_l hb_in by (by100 blast)
      have h3: "?mulA a ?eA = a" using hAbelF_id_r ha_in by (by100 blast)
      have h4: "?mulA ?eA b = b" using hAbelF_id_l hb_in by (by100 blast)
      from hab have "?mulA (?mulA a (?invgA b)) b = ?mulA ?eA b" by (by100 simp)
      hence "?mulA a (?mulA (?invgA b) b) = b" using h1 h4 by (by100 simp)
      hence "?mulA a ?eA = b" using h2 by (by100 simp)
      thus "a = b" using h3 by (by100 simp)
    qed
  qed

  \<comment> \<open>Step F: Transfer free abelian structure from K_0 to K via \<phi>\_bar.
     K_0 is free abelian on {..<m}-{0}, \<phi>\_bar|_{K_0} is an injective hom into AbelG.
     So K = \<phi>\_bar(K_0) is free abelian on {..<m}-{0} \<cong> {..<m-1}.\<close>
  \<comment> \<open>\<phi>\_bar restricted to K_0 is an iso from (K_0, mulA) to (K, mulAG).\<close>
  \<comment> \<open>K is a group (needed inside K\_fab\_raw proof before hK\_grp\_outer is available).\<close>
  have hK_grp_pre: "top1_is_group_on ?K ?mulAG ?eAG ?invgAG"
  proof -
    \<comment> \<open>eAG \<in> K.\<close>
    have hZ_grp_k: "top1_is_group_on (UNIV::int set) (+) 0 uminus"
      using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
        top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 blast)
    have he_K: "?eAG \<in> ?K"
    proof -
      have "\<epsilon>0 ?eA = 0" using hom_preserves_id[OF hAbelF_grp hZ_grp_k h\<epsilon>0_hom] by (by100 simp)
      hence "?eA \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0}" using hAbelF_e_in by (by100 blast)
      moreover have "\<phi>_bar ?eA = ?eAG"
        using hom_preserves_id[OF hAbelF_grp hAbelG_grp h\<phi>_hom] by (by100 simp)
      ultimately show ?thesis by (by100 force)
    qed
    \<comment> \<open>Mul closure.\<close>
    have hmul_K: "\<forall>x\<in>?K. \<forall>y\<in>?K. ?mulAG x y \<in> ?K"
    proof (intro ballI)
      fix x y assume "x \<in> ?K" "y \<in> ?K"
      then obtain a b where ha: "a \<in> ?AbelF" "\<epsilon>0 a = 0" "x = \<phi>_bar a"
        and hb: "b \<in> ?AbelF" "\<epsilon>0 b = 0" "y = \<phi>_bar b" by (by100 blast)
      have "\<epsilon>0 (?mulA a b) = \<epsilon>0 a + \<epsilon>0 b"
        using h\<epsilon>0_hom ha(1) hb(1) unfolding top1_group_hom_on_def by (by100 blast)
      hence "\<epsilon>0 (?mulA a b) = 0" using ha(2) hb(2) by (by100 simp)
      moreover have "?mulA a b \<in> ?AbelF" using hAbelF_mul_cl ha(1) hb(1) by (by100 blast)
      moreover have "?mulAG x y = \<phi>_bar (?mulA a b)"
        using h\<phi>_hom ha hb unfolding top1_group_hom_on_def by (by100 blast)
      ultimately show "?mulAG x y \<in> ?K" by (by100 force)
    qed
    \<comment> \<open>Inv closure.\<close>
    have hinv_K: "\<forall>x\<in>?K. ?invgAG x \<in> ?K"
    proof (intro ballI)
      fix x assume "x \<in> ?K"
      then obtain a where ha: "a \<in> ?AbelF" "\<epsilon>0 a = 0" "x = \<phi>_bar a" by (by100 blast)
      have "\<epsilon>0 (?invgA a) = - \<epsilon>0 a"
        using hom_preserves_inv[OF hAbelF_grp hZ_grp_k h\<epsilon>0_hom ha(1)] by (by100 simp)
      hence "\<epsilon>0 (?invgA a) = 0" using ha(2) by (by100 simp)
      moreover have "?invgA a \<in> ?AbelF" using hAbelF_invg_cl ha(1) by (by100 blast)
      moreover have "?invgAG x = \<phi>_bar (?invgA a)"
        using hom_preserves_inv[OF hAbelF_grp hAbelG_grp h\<phi>_hom ha(1)] ha(3) by (by100 simp)
      ultimately show "?invgAG x \<in> ?K" by (by100 force)
    qed
    \<comment> \<open>Axioms from AbelG via foldr\_mul\_append + fast.\<close>
    \<comment> \<open>Assoc for K: use foldr\_mul\_append trick.\<close>
    have hassoc_K: "\<forall>x\<in>?K. \<forall>y\<in>?K. \<forall>z\<in>?K. ?mulAG (?mulAG x y) z = ?mulAG x (?mulAG y z)"
    proof (intro ballI)
      fix x y z assume "x \<in> ?K" "y \<in> ?K" "z \<in> ?K"
      hence hxG: "x \<in> ?AbelG" and hyG: "y \<in> ?AbelG" and hzG: "z \<in> ?AbelG"
        using hK_sub by (by100 blast)+
      have hxy: "\<forall>i<length [x,y]. [x,y]!i \<in> ?AbelG"
        using hxG hyG by (intro allI impI, auto simp: nth_Cons split: nat.splits)
      have hz1: "\<forall>i<length [z]. [z]!i \<in> ?AbelG" using hzG by (by100 auto)
      have hx1: "\<forall>i<length [x]. [x]!i \<in> ?AbelG" using hxG by (by100 auto)
      have hyz: "\<forall>i<length [y,z]. [y,z]!i \<in> ?AbelG"
        using hyG hzG by (intro allI impI, auto simp: nth_Cons split: nat.splits)
      have lhs: "foldr ?mulAG ([x,y] @ [z]) ?eAG = ?mulAG (foldr ?mulAG [x,y] ?eAG) (foldr ?mulAG [z] ?eAG)"
        using foldr_mul_append[OF hAbelG_grp hxy hz1] by (by100 blast)
      have rhs: "foldr ?mulAG ([x] @ [y,z]) ?eAG = ?mulAG (foldr ?mulAG [x] ?eAG) (foldr ?mulAG [y,z] ?eAG)"
        using foldr_mul_append[OF hAbelG_grp hx1 hyz] by (by100 blast)
      have "\<forall>a\<in>?AbelG. ?mulAG a ?eAG = a"
        using hAbelG_grp[unfolded top1_is_group_on_def] by (by100 fast)
      have hidG: "\<forall>a\<in>?AbelG. ?mulAG a ?eAG = a"
        using hAbelG_grp[unfolded top1_is_group_on_def] by (by100 fast)
      show "?mulAG (?mulAG x y) z = ?mulAG x (?mulAG y z)"
        using lhs rhs hidG hxG hyG hzG by (by100 simp)
    qed
    \<comment> \<open>Id and inv from AbelG.\<close>
    have hid_K: "\<forall>x\<in>?K. ?mulAG ?eAG x = x \<and> ?mulAG x ?eAG = x"
    proof (intro ballI)
      fix x assume "x \<in> ?K"
      hence "x \<in> ?AbelG" using hK_sub by (by100 blast)
      from hAbelG_grp[unfolded top1_is_group_on_def] this
      show "?mulAG ?eAG x = x \<and> ?mulAG x ?eAG = x" by (by100 fast)
    qed
    have hinverse_K: "\<forall>x\<in>?K. ?mulAG (?invgAG x) x = ?eAG \<and> ?mulAG x (?invgAG x) = ?eAG"
    proof (intro ballI)
      fix x assume "x \<in> ?K"
      hence "x \<in> ?AbelG" using hK_sub by (by100 blast)
      from hAbelG_grp[unfolded top1_is_group_on_def] this
      show "?mulAG (?invgAG x) x = ?eAG \<and> ?mulAG x (?invgAG x) = ?eAG" by (by100 fast)
    qed
    show ?thesis unfolding top1_is_group_on_def
      using he_K hmul_K hinv_K hassoc_K hid_K hinverse_K by (by100 blast)
  qed

  have hK_fab_raw: "top1_is_free_abelian_group_full_on ?K ?mulAG ?eAG ?invgAG
      (\<lambda>s. \<phi>_bar (?\<iota>A s)) ({..<m} - {0::nat})"
    unfolding top1_is_free_abelian_group_full_on_def
  proof (intro conjI)
    \<comment> \<open>1. K is abelian (subgroup of abelian AbelG).\<close>
    show "top1_is_abelian_group_on ?K ?mulAG ?eAG ?invgAG"
    proof -
      \<comment> \<open>K_0 is a subgroup of AbelF (kernel of \<epsilon>_0 hom).\<close>
      have hK0_grp: "top1_is_group_on {a \<in> ?AbelF. \<epsilon>0 a = 0} ?mulA ?eA ?invgA"
      proof -
        \<comment> \<open>{a | \<epsilon>_0(a) = 0} = kernel of \<epsilon>_0. Use kernel\_is\_normal\_subgroup.\<close>
        have hZ_grp: "top1_is_group_on (UNIV::int set) (+) 0 uminus"
          using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
            top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 blast)
        have "{a \<in> ?AbelF. \<epsilon>0 a = 0} = top1_group_kernel_on ?AbelF (0::int) \<epsilon>0"
          unfolding top1_group_kernel_on_def by (by100 blast)
        moreover have "top1_normal_subgroup_on ?AbelF ?mulA ?eA ?invgA (top1_group_kernel_on ?AbelF (0::int) \<epsilon>0)"
          using kernel_is_normal_subgroup[OF hAbelF_grp hZ_grp h\<epsilon>0_hom] by (by100 simp)
        ultimately have "top1_normal_subgroup_on ?AbelF ?mulA ?eA ?invgA {a \<in> ?AbelF. \<epsilon>0 a = 0}"
          by (by100 simp)
        thus ?thesis unfolding top1_normal_subgroup_on_def by (by100 fast)
      qed
      \<comment> \<open>K = \<phi>\_bar(K_0) is a group via hom image of subgroup.\<close>
      have hK_grp: "top1_is_group_on ?K ?mulAG ?eAG ?invgAG"
      proof -
        \<comment> \<open>K is a subgroup of AbelG: closed under mul, inv, contains e.\<close>
        have he_in_K: "?eAG \<in> ?K"
        proof -
          have hZ_grp_loc: "top1_is_group_on (UNIV::int set) (+) 0 uminus"
            using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
              top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 blast)
          have "\<epsilon>0 ?eA = 0"
            using hom_preserves_id[OF hAbelF_grp hZ_grp_loc h\<epsilon>0_hom] by (by100 simp)
          have "?eA \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0}"
            using hAbelF_e_in \<open>\<epsilon>0 ?eA = 0\<close> by (by100 blast)
          hence "\<phi>_bar ?eA \<in> ?K" by (by100 blast)
          moreover have "\<phi>_bar ?eA = ?eAG"
            using hom_preserves_id[OF hAbelF_grp hAbelG_grp h\<phi>_hom] by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        have hmul_cl_K: "\<forall>x\<in>?K. \<forall>y\<in>?K. ?mulAG x y \<in> ?K"
        proof (intro ballI)
          fix x y assume "x \<in> ?K" "y \<in> ?K"
          then obtain a b where ha: "a \<in> ?AbelF" "\<epsilon>0 a = 0" "x = \<phi>_bar a"
            and hb: "b \<in> ?AbelF" "\<epsilon>0 b = 0" "y = \<phi>_bar b" by (by100 blast)
          have hab: "?mulA a b \<in> ?AbelF" using hAbelF_mul_cl ha(1) hb(1) by (by100 blast)
          have "\<epsilon>0 (?mulA a b) = \<epsilon>0 a + \<epsilon>0 b"
            using h\<epsilon>0_hom ha(1) hb(1) unfolding top1_group_hom_on_def by (by100 blast)
          hence "\<epsilon>0 (?mulA a b) = 0" using ha(2) hb(2) by (by100 simp)
          hence "?mulA a b \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0}" using hab by (by100 blast)
          moreover have "?mulAG x y = \<phi>_bar (?mulA a b)"
            using h\<phi>_hom ha hb unfolding top1_group_hom_on_def by (by100 blast)
          ultimately show "?mulAG x y \<in> ?K" by (by100 force)
        qed
        have hinv_cl_K: "\<forall>x\<in>?K. ?invgAG x \<in> ?K"
        proof (intro ballI)
          fix x assume "x \<in> ?K"
          then obtain a where ha: "a \<in> ?AbelF" "\<epsilon>0 a = 0" "x = \<phi>_bar a" by (by100 blast)
          have hinva: "?invgA a \<in> ?AbelF" using hAbelF_invg_cl ha(1) by (by100 blast)
          have hZ_grp_l: "top1_is_group_on (UNIV::int set) (+) 0 uminus"
            using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
              top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 blast)
          have "\<epsilon>0 (?invgA a) = - \<epsilon>0 a"
            using hom_preserves_inv[OF hAbelF_grp hZ_grp_l h\<epsilon>0_hom ha(1)] by (by100 simp)
          hence "\<epsilon>0 (?invgA a) = 0" using ha(2) by (by100 simp)
          hence "?invgA a \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0}" using hinva by (by100 blast)
          moreover have "?invgAG x = \<phi>_bar (?invgA a)"
            using hom_preserves_inv[OF hAbelF_grp hAbelG_grp h\<phi>_hom ha(1)] ha(3) by (by100 simp)
          ultimately show "?invgAG x \<in> ?K" by (by100 force)
        qed
        \<comment> \<open>Group axioms (assoc, id, inv) inherited from AbelG since K \<subseteq> AbelG.\<close>
        \<comment> \<open>Inherit assoc, id, inv axioms from AbelG for K \<subseteq> AbelG.\<close>
        \<comment> \<open>Inherit assoc/id/inv from AbelG using coset representative extraction.\<close>
        have hassoc_K: "\<forall>x\<in>?K. \<forall>y\<in>?K. \<forall>z\<in>?K. ?mulAG (?mulAG x y) z = ?mulAG x (?mulAG y z)"
        proof (intro ballI)
          fix x y z assume "x \<in> ?K" "y \<in> ?K" "z \<in> ?K"
          hence "x \<in> ?AbelG" "y \<in> ?AbelG" "z \<in> ?AbelG" using hK_sub by (by100 blast)+
          then obtain gx gy gz where hgx: "gx \<in> G0" "x = ?pG gx"
            and hgy: "gy \<in> G0" "y = ?pG gy" and hgz: "gz \<in> G0" "z = ?pG gz"
            unfolding top1_quotient_group_carrier_on_def by (by100 blast)
          \<comment> \<open>Use foldr\_mul\_append trick to prove assoc without unfolding.\<close>
          have hxy: "\<forall>i<length [x,y]. [x,y]!i \<in> ?AbelG"
            using \<open>x \<in> ?AbelG\<close> \<open>y \<in> ?AbelG\<close> by (intro allI impI, auto simp: nth_Cons split: nat.splits)
          have hz1: "\<forall>i<length [z]. [z]!i \<in> ?AbelG" using \<open>z \<in> ?AbelG\<close> by (by100 auto)
          have hx1: "\<forall>i<length [x]. [x]!i \<in> ?AbelG" using \<open>x \<in> ?AbelG\<close> by (by100 auto)
          have hyz: "\<forall>i<length [y,z]. [y,z]!i \<in> ?AbelG"
            using \<open>y \<in> ?AbelG\<close> \<open>z \<in> ?AbelG\<close> by (intro allI impI, auto simp: nth_Cons split: nat.splits)
          have lhs: "foldr ?mulAG ([x,y] @ [z]) ?eAG = ?mulAG (foldr ?mulAG [x,y] ?eAG) (foldr ?mulAG [z] ?eAG)"
            using foldr_mul_append[OF hAbelG_grp hxy hz1] by (by100 blast)
          have rhs: "foldr ?mulAG ([x] @ [y,z]) ?eAG = ?mulAG (foldr ?mulAG [x] ?eAG) (foldr ?mulAG [y,z] ?eAG)"
            using foldr_mul_append[OF hAbelG_grp hx1 hyz] by (by100 blast)
          have hidG_K: "\<forall>a\<in>?AbelG. ?mulAG a ?eAG = a"
            using hAbelG_grp[unfolded top1_is_group_on_def] by (by100 fast)
          show "?mulAG (?mulAG x y) z = ?mulAG x (?mulAG y z)"
            using lhs rhs hidG_K \<open>x \<in> ?AbelG\<close> \<open>y \<in> ?AbelG\<close> \<open>z \<in> ?AbelG\<close> by (by100 simp)
        qed
        have hid_K: "\<forall>x\<in>?K. ?mulAG ?eAG x = x \<and> ?mulAG x ?eAG = x"
        proof (intro ballI)
          fix x assume "x \<in> ?K"
          hence "x \<in> ?AbelG" using hK_sub by (by100 blast)
          from hAbelG_grp[unfolded top1_is_group_on_def] \<open>x \<in> ?AbelG\<close>
          show "?mulAG ?eAG x = x \<and> ?mulAG x ?eAG = x" by (by100 fast)
        qed
        have hinv_K: "\<forall>x\<in>?K. ?mulAG (?invgAG x) x = ?eAG \<and> ?mulAG x (?invgAG x) = ?eAG"
        proof (intro ballI)
          fix x assume "x \<in> ?K"
          hence "x \<in> ?AbelG" using hK_sub by (by100 blast)
          from hAbelG_grp[unfolded top1_is_group_on_def] \<open>x \<in> ?AbelG\<close>
          show "?mulAG (?invgAG x) x = ?eAG \<and> ?mulAG x (?invgAG x) = ?eAG" by (by100 fast)
        qed
        show ?thesis
          unfolding top1_is_group_on_def
          using he_in_K hmul_cl_K hinv_cl_K hassoc_K hid_K hinv_K by (by100 blast)
      qed
      \<comment> \<open>K is abelian since K \<subseteq> AbelG and AbelG is abelian.\<close>
      show ?thesis
        unfolding top1_is_abelian_group_on_def
      proof (intro conjI ballI)
        show "top1_is_group_on ?K ?mulAG ?eAG ?invgAG" by (rule hK_grp)
        fix x y assume hx: "x \<in> ?K" and hy: "y \<in> ?K"
        hence hxG: "x \<in> ?AbelG" and hyG: "y \<in> ?AbelG" using hK_sub by (by100 blast)+
        \<comment> \<open>Use abelian\_subgroup\_is\_normal's commutativity proof pattern.\<close>
        have "\<forall>a\<in>?AbelG. \<forall>b\<in>?AbelG. ?mulAG a b = ?mulAG b a"
        proof (intro ballI)
          fix a b assume "a \<in> ?AbelG" "b \<in> ?AbelG"
          then obtain ga gb where hga: "ga \<in> G0" "a = ?pG ga"
            and hgb: "gb \<in> G0" "b = ?pG gb"
            unfolding top1_quotient_group_carrier_on_def by (by100 blast)
          from quotient_by_commutator_is_abelian[OF hG0] hga(1) hgb(1)
          have "?mulAG (?pG ga) (?pG gb) = ?mulAG (?pG gb) (?pG ga)" by (by100 blast)
          thus "?mulAG a b = ?mulAG b a" using hga(2) hgb(2) by (by100 simp)
        qed
        thus "?mulAG x y = ?mulAG y x" using hxG hyG by (by100 blast)
      qed
    qed
    \<comment> \<open>2. Generators in K.\<close>
    show "\<forall>s\<in>{..<m} - {0::nat}. \<phi>_bar (?\<iota>A s) \<in> ?K"
    proof (intro ballI)
      fix s assume hs: "s \<in> {..<m} - {0::nat}"
      hence "s \<in> {..<m}" "s \<noteq> 0" by (by100 auto)+
      have "\<epsilon>0 (?\<iota>A s) = 0" using h\<epsilon>0_rest \<open>s \<in> {..<m}\<close> \<open>s \<noteq> 0\<close> by (by100 blast)
      moreover have "?\<iota>A s \<in> ?AbelF"
        using h\<iota>A_in \<open>s \<in> {..<m}\<close> by (by100 blast)
      ultimately have "?\<iota>A s \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0}" by (by100 blast)
      thus "\<phi>_bar (?\<iota>A s) \<in> ?K" by (by100 blast)
    qed
    \<comment> \<open>3. Injective.\<close>
    show "inj_on (\<lambda>s. \<phi>_bar (?\<iota>A s)) ({..<m} - {0::nat})"
    proof (rule inj_onI)
      fix s1 s2 assume hs1: "s1 \<in> {..<m} - {0::nat}" and hs2: "s2 \<in> {..<m} - {0::nat}"
        and heq: "\<phi>_bar (?\<iota>A s1) = \<phi>_bar (?\<iota>A s2)"
      \<comment> \<open>\<iota>A(s1), \<iota>A(s2) \<in> K_0 (since \<epsilon>_0 = 0 for s \<noteq> 0).\<close>
      have h1: "?\<iota>A s1 \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0}"
        using h\<iota>A_in h\<epsilon>0_rest hs1 by (by100 auto)
      have h2: "?\<iota>A s2 \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0}"
        using h\<iota>A_in h\<epsilon>0_rest hs2 by (by100 auto)
      \<comment> \<open>\<phi>\_bar injective on K_0 gives \<iota>A(s1) = \<iota>A(s2).\<close>
      have "?\<iota>A s1 = ?\<iota>A s2"
        using h\<phi>_inj_K0[unfolded inj_on_def] h1 h2 heq by (by100 blast)
      \<comment> \<open>\<iota>A injective on {..<m} gives s1 = s2.\<close>
      moreover have "inj_on ?\<iota>A ({..<m}::nat set)"
        using h\<iota>A unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
      ultimately show "s1 = s2"
        using hs1 hs2 unfolding inj_on_def by (by100 blast)
    qed
    \<comment> \<open>4. Generation.\<close>
    show "?K = top1_subgroup_generated_on ?K ?mulAG ?eAG ?invgAG
        ((\<lambda>s. \<phi>_bar (?\<iota>A s)) ` ({..<m} - {0::nat}))"
    proof (rule set_eqI, rule iffI)
      \<comment> \<open>(\<supseteq>) subgroup\_generated \<subseteq> K: generators in K, K is a group.\<close>
      fix x assume "x \<in> top1_subgroup_generated_on ?K ?mulAG ?eAG ?invgAG
          ((\<lambda>s. \<phi>_bar (?\<iota>A s)) ` ({..<m} - {0::nat}))"
      thus "x \<in> ?K"
      proof -
        have "(\<lambda>s. \<phi>_bar (?\<iota>A s)) ` ({..<m} - {0::nat}) \<subseteq> ?K"
        proof (rule image_subsetI)
          fix s assume "s \<in> {..<m} - {0::nat}"
          hence "s \<in> {..<m}" "s \<noteq> 0" by (by100 auto)+
          have "\<epsilon>0 (?\<iota>A s) = 0" using h\<epsilon>0_rest \<open>s \<in> {..<m}\<close> \<open>s \<noteq> 0\<close> by (by100 blast)
          moreover have "?\<iota>A s \<in> ?AbelF" using h\<iota>A_in \<open>s \<in> {..<m}\<close> by (by100 blast)
          ultimately show "\<phi>_bar (?\<iota>A s) \<in> ?K" by (by100 blast)
        qed
        from subgroup_generated_subset[OF hK_grp_pre this]
        show ?thesis
          using \<open>x \<in> _\<close> by (by100 blast)
      qed
    next
      \<comment> \<open>(\<subseteq>) K \<subseteq> subgroup\_generated: every x \<in> K = \<phi>\_bar(a) for a \<in> K_0,
         and a is a word in \<iota>A(s) for s > 0 (by K_0 generation from hK0\_fab),
         so x = \<phi>\_bar(word) = word in \<phi>\_bar(\<iota>A(s)) in AbelG.\<close>
      fix x assume hx: "x \<in> ?K"
      show "x \<in> top1_subgroup_generated_on ?K ?mulAG ?eAG ?invgAG
          ((\<lambda>s. \<phi>_bar (?\<iota>A s)) ` ({..<m} - {0::nat}))"
      proof -
        \<comment> \<open>x = \<phi>\_bar(a) for a \<in> K_0.\<close>
        from hx obtain a where ha: "a \<in> ?AbelF" "\<epsilon>0 a = 0" "x = \<phi>_bar a"
          by (by100 blast)
        \<comment> \<open>K_0 is generated by \<iota>A on {..<m}-{0}.\<close>
        have hK0_gen: "{a \<in> ?AbelF. \<epsilon>0 a = 0} = top1_subgroup_generated_on
            {a \<in> ?AbelF. \<epsilon>0 a = 0} ?mulA ?eA ?invgA (?\<iota>A ` ({..<m} - {0::nat}))"
          using hK0_fab unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
        have "a \<in> top1_subgroup_generated_on {a \<in> ?AbelF. \<epsilon>0 a = 0} ?mulA ?eA ?invgA
            (?\<iota>A ` ({..<m} - {0::nat}))"
          using ha(1) ha(2) hK0_gen by (by100 blast)
        \<comment> \<open>By word repr: a = eA or a = foldr mulA ws eA where ws are \<iota>A(s) or invgA(\<iota>A(s)).\<close>
        \<comment> \<open>Then \<phi>\_bar(a) is eAG or foldr mulAG (map \<phi>\_bar ws) eAG.
           Each \<phi>\_bar(ws!i) is in {gen} \<union> invgAG({gen}), hence in subgroup\_generated.
           So \<phi>\_bar(a) \<in> subgroup\_generated.\<close>
        \<comment> \<open>By subgroup\_generated\_word\_repr: a = eA or word.\<close>
        hence "a = ?eA \<or> (\<exists>ws. length ws > 0
            \<and> (\<forall>i<length ws. ws!i \<in> ?\<iota>A ` ({..<m} - {0::nat})
                \<or> (\<exists>s\<in>?\<iota>A ` ({..<m} - {0::nat}). ws!i = ?invgA s))
            \<and> foldr ?mulA ws ?eA = a)"
        proof -
          have h\<iota>A_sub_K0: "?\<iota>A ` ({..<m} - {0::nat}) \<subseteq> {a \<in> ?AbelF. \<epsilon>0 a = 0}"
          proof (rule image_subsetI)
            fix s assume "s \<in> {..<m} - {0::nat}"
            thus "?\<iota>A s \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0}"
              using h\<iota>A_in h\<epsilon>0_rest by (by100 auto)
          qed
          have hK0_grp_loc: "top1_is_group_on {a \<in> ?AbelF. \<epsilon>0 a = 0} ?mulA ?eA ?invgA"
            using hK0_grp_outer .
          from subgroup_generated_word_repr[OF hK0_grp_loc h\<iota>A_sub_K0]
          show ?thesis
            using \<open>a \<in> top1_subgroup_generated_on _ _ _ _ _\<close> by (by100 blast)
        qed
        thus ?thesis
        proof (elim disjE)
          assume "a = ?eA"
          hence "x = ?eAG" using ha(3)
            hom_preserves_id[OF hAbelF_grp hAbelG_grp h\<phi>_hom] by (by100 simp)
          moreover have "?eAG \<in> top1_subgroup_generated_on ?K ?mulAG ?eAG ?invgAG
              ((\<lambda>s. \<phi>_bar (?\<iota>A s)) ` ({..<m} - {0::nat}))"
          proof -
            have hgens_sub_K: "(\<lambda>s. \<phi>_bar (?\<iota>A s)) ` ({..<m} - {0::nat}) \<subseteq> ?K"
            proof (rule image_subsetI)
              fix s assume "s \<in> {..<m} - {0::nat}"
              thus "\<phi>_bar (?\<iota>A s) \<in> ?K"
                using h\<iota>A_in h\<epsilon>0_rest by (by100 auto)
            qed
            have hsg_grp: "top1_is_group_on (top1_subgroup_generated_on ?K ?mulAG ?eAG ?invgAG
                ((\<lambda>s. \<phi>_bar (?\<iota>A s)) ` ({..<m} - {0::nat}))) ?mulAG ?eAG ?invgAG"
              using intersection_of_subgroups_is_group[OF hK_grp_pre hgens_sub_K] by (by100 simp)
            from hsg_grp[unfolded top1_is_group_on_def]
            show ?thesis by (by100 fast)
          qed
          ultimately show ?thesis by (by100 simp)
        next
          assume "\<exists>ws. length ws > 0
            \<and> (\<forall>i<length ws. ws!i \<in> ?\<iota>A ` ({..<m} - {0::nat})
                \<or> (\<exists>s\<in>?\<iota>A ` ({..<m} - {0::nat}). ws!i = ?invgA s))
            \<and> foldr ?mulA ws ?eA = a"
          then obtain ws where hlen: "length ws > 0"
            and hws: "\<forall>i<length ws. ws!i \<in> ?\<iota>A ` ({..<m} - {0::nat})
                \<or> (\<exists>s\<in>?\<iota>A ` ({..<m} - {0::nat}). ws!i = ?invgA s)"
            and hprod: "foldr ?mulA ws ?eA = a" by (by100 blast)
          \<comment> \<open>\<phi>\_bar(foldr ws) = foldr (map \<phi>\_bar ws) in AbelG.
             Each \<phi>\_bar(ws!i) is a generator or inverse of generator in sg.\<close>
          let ?sg = "top1_subgroup_generated_on ?K ?mulAG ?eAG ?invgAG
              ((\<lambda>s. \<phi>_bar (?\<iota>A s)) ` ({..<m} - {0::nat}))"
          \<comment> \<open>Each ws!i is \<iota>A(s) or invgA(\<iota>A(s)) for s \<in> {..<m}-{0}.
             So \<phi>\_bar(ws!i) is in ?sg.\<close>
          have hgens_sub_K_loc: "(\<lambda>s. \<phi>_bar (?\<iota>A s)) ` ({..<m} - {0::nat}) \<subseteq> ?K"
          proof (rule image_subsetI)
            fix s assume "s \<in> {..<m} - {0::nat}"
            thus "\<phi>_bar (?\<iota>A s) \<in> ?K"
              using h\<iota>A_in h\<epsilon>0_rest by (by100 auto)
          qed
          have hsg_grp: "top1_is_group_on ?sg ?mulAG ?eAG ?invgAG"
            using intersection_of_subgroups_is_group[OF hK_grp_pre hgens_sub_K_loc] by (by100 simp)
          \<comment> \<open>Each \<phi>\_bar(ws!i) \<in> ?sg.\<close>
          have hmap_in_sg: "\<forall>i<length (map \<phi>_bar ws). (map \<phi>_bar ws) ! i \<in> ?sg"
          proof (intro allI impI)
            fix i assume hi: "i < length (map \<phi>_bar ws)"
            hence hi': "i < length ws" by (by100 simp)
            from hws this have "ws!i \<in> ?\<iota>A ` ({..<m} - {0::nat})
                \<or> (\<exists>s\<in>?\<iota>A ` ({..<m} - {0::nat}). ws!i = ?invgA s)" by (by100 blast)
            thus "(map \<phi>_bar ws) ! i \<in> ?sg"
            proof (elim disjE)
              assume "ws!i \<in> ?\<iota>A ` ({..<m} - {0::nat})"
              then obtain s where hs: "s \<in> {..<m} - {0::nat}" "ws!i = ?\<iota>A s" by (by100 blast)
              hence "\<phi>_bar (?\<iota>A s) \<in> (\<lambda>s. \<phi>_bar (?\<iota>A s)) ` ({..<m} - {0::nat})" by (by100 blast)
              hence "\<phi>_bar (?\<iota>A s) \<in> ?sg"
                using subgroup_generated_contains[OF hK_grp_pre hgens_sub_K_loc] by (by100 blast)
              thus ?thesis using hs(2) hi' by (by100 simp)
            next
              assume "\<exists>s\<in>?\<iota>A ` ({..<m} - {0::nat}). ws!i = ?invgA s"
              then obtain s where hs: "s \<in> ?\<iota>A ` ({..<m} - {0::nat})" "ws!i = ?invgA s"
                by (by100 blast)
              then obtain j where hj: "j \<in> {..<m} - {0::nat}" "s = ?\<iota>A j" by (by100 blast)
              have hs_in: "s \<in> ?AbelF" using h\<iota>A_in hj by (by100 auto)
              have "\<phi>_bar (?invgA s) = ?invgAG (\<phi>_bar s)"
                using hom_preserves_inv[OF hAbelF_grp hAbelG_grp h\<phi>_hom hs_in] by (by100 simp)
              moreover have "\<phi>_bar s \<in> ?sg"
              proof -
                have "\<phi>_bar (?\<iota>A j) \<in> (\<lambda>s. \<phi>_bar (?\<iota>A s)) ` ({..<m} - {0::nat})" using hj(1) by (by100 blast)
                thus ?thesis using hj(2) subgroup_generated_contains[OF hK_grp_pre hgens_sub_K_loc]
                  by (by100 blast)
              qed
              hence "?invgAG (\<phi>_bar s) \<in> ?sg"
                using hsg_grp unfolding top1_is_group_on_def by (by100 fast)
              ultimately have "\<phi>_bar (?invgA s) \<in> ?sg" by (by100 simp)
              thus ?thesis using hs(2) hi' by (by100 simp)
            qed
          qed
          \<comment> \<open>\<phi>\_bar(a) = \<phi>\_bar(foldr ws) = foldr (map \<phi>\_bar ws) in AbelG.\<close>
          have hws_in_F: "\<forall>i<length ws. ws!i \<in> ?AbelF"
          proof (intro allI impI)
            fix i assume "i < length ws"
            from hws this have "ws!i \<in> ?\<iota>A ` ({..<m} - {0::nat})
                \<or> (\<exists>s\<in>?\<iota>A ` ({..<m} - {0::nat}). ws!i = ?invgA s)" by (by100 blast)
            thus "ws!i \<in> ?AbelF"
            proof (elim disjE)
              assume "ws!i \<in> ?\<iota>A ` ({..<m} - {0::nat})"
              thus ?thesis using h\<iota>A_in by (by100 auto)
            next
              assume "\<exists>s\<in>?\<iota>A ` ({..<m} - {0::nat}). ws!i = ?invgA s"
              then obtain s where "s \<in> ?\<iota>A ` ({..<m} - {0::nat})" "ws!i = ?invgA s" by (by100 blast)
              hence "s \<in> ?AbelF" using h\<iota>A_in by (by100 auto)
              hence "?invgA s \<in> ?AbelF" using hAbelF_invg_cl by (by100 blast)
              thus ?thesis using \<open>ws!i = ?invgA s\<close> by (by100 simp)
            qed
          qed
          have "x = \<phi>_bar (foldr ?mulA ws ?eA)" using ha(3) hprod by (by100 simp)
          also have "\<phi>_bar (foldr ?mulA ws ?eA) = foldr ?mulAG (map \<phi>_bar ws) ?eAG"
            using hom_foldr_mul[OF hAbelF_grp hAbelG_grp h\<phi>_hom hws_in_F] by (by100 blast)
          finally have "x = foldr ?mulAG (map \<phi>_bar ws) ?eAG" .
          \<comment> \<open>foldr of sg elements \<in> sg.\<close>
          moreover have "foldr ?mulAG (map \<phi>_bar ws) ?eAG \<in> ?sg"
            using foldr_mul_closed[OF hsg_grp hmap_in_sg] by (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
      qed
    qed
    \<comment> \<open>5. Independence.\<close>
    show "\<forall>c. finite {s \<in> {..<m} - {0::nat}. c s \<noteq> 0} \<longrightarrow>
        (\<exists>s\<in>{..<m} - {0::nat}. c s \<noteq> 0) \<longrightarrow>
        foldr ?mulAG (map (\<lambda>s. if 0 \<le> c s then top1_group_pow ?mulAG ?eAG (\<phi>_bar (?\<iota>A s)) (nat (c s))
                   else top1_group_pow ?mulAG ?eAG (?invgAG (\<phi>_bar (?\<iota>A s))) (nat (- c s)))
          (SOME xs. set xs = {s \<in> {..<m} - {0::nat}. c s \<noteq> 0} \<and> distinct xs)) ?eAG \<noteq> ?eAG"
    proof (intro allI impI, rule notI)
      fix c :: "nat \<Rightarrow> int"
      assume hfin: "finite {s \<in> {..<m} - {0::nat}. c s \<noteq> 0}"
        and hex: "\<exists>s\<in>{..<m} - {0::nat}. c s \<noteq> 0"
        and hprod_e: "foldr ?mulAG (map (\<lambda>s. if 0 \<le> c s then top1_group_pow ?mulAG ?eAG (\<phi>_bar (?\<iota>A s)) (nat (c s))
                   else top1_group_pow ?mulAG ?eAG (?invgAG (\<phi>_bar (?\<iota>A s))) (nat (- c s)))
          (SOME xs. set xs = {s \<in> {..<m} - {0::nat}. c s \<noteq> 0} \<and> distinct xs)) ?eAG = ?eAG"
      \<comment> \<open>Strategy: for each j \<in> {..<m-1}, build a difference-coordinate hom
         \<delta>_j: AbelF \<rightarrow> Z with \<delta>_j(\<iota>A 0) = -1, \<delta>_j(\<iota>A(Suc j)) = 1, others = 0.
         Then \<delta>_j(\<beta>) = 0, so \<delta>_j kills N\_AbelF, inducing \<delta>\_bar_j: AbelG \<rightarrow> Z.
         Applying \<delta>\_bar_j to hprod\_e gives c(Suc j) = 0 for all j.
         Hence c = 0, contradicting hex.\<close>
      \<comment> \<open>Step 1: Use the existing \<epsilon>_0 and free\_abelian\_coordinate\_projection for each j.\<close>
      \<comment> \<open>The combination in AbelF: define a' = foldr mulA (map (\<lambda>s. pow(\<iota>A s, c s)) support) eA.
         This has \<phi>\_bar(a') = the product = eAG. So a' \<in> ker(\<phi>\_bar) = N\_AbelF.
         N\_AbelF = \<langle>\<beta>\<twosuperior>\<rangle>. For a' \<in> \<langle>\<beta>\<twosuperior>\<rangle>: a' = pow(\<beta>\<twosuperior>, k) for some k.
         \<epsilon>_0(a') = 0 (since support \<subseteq> {..<m}-{0} and \<epsilon>_0(\<iota>A s) = 0 for s \<noteq> 0).
         \<epsilon>_0(pow(\<beta>\<twosuperior>, k)) = 2k. So 2k = 0, k = 0, a' = eA.
         But if a' = eA, then by free abelian independence of AbelF, c = 0.\<close>
      \<comment> \<open>Step 1: The corresponding combination in AbelF (via free\_abelian\_word\_kernel
         or direct construction).\<close>
      \<comment> \<open>Step 1: Define the lift in AbelF.\<close>
      let ?supp = "SOME xs. set xs = {s \<in> {..<m} - {0::nat}. c s \<noteq> 0} \<and> distinct xs"
      let ?liftF = "foldr ?mulA (map (\<lambda>s. if 0 \<le> c s
          then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (c s))
          else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- c s))) ?supp) ?eA"

      \<comment> \<open>Properties of supp: set ?supp = {s\<in>{..<m}-{0}. c s \<noteq> 0} and distinct.\<close>
      have hsupp_props: "set ?supp = {s \<in> {..<m} - {0::nat}. c s \<noteq> 0} \<and> distinct ?supp"
      proof -
        from hfin have "\<exists>xs. set xs = {s \<in> {..<m} - {0::nat}. c s \<noteq> 0} \<and> distinct xs"
          using finite_distinct_list_of_set by (by100 blast)
        thus ?thesis using someI_ex[of "\<lambda>xs. set xs = {s \<in> {..<m} - {0::nat}. c s \<noteq> 0} \<and> distinct xs"]
          by (by100 blast)
      qed
      hence hsupp_set: "set ?supp = {s \<in> {..<m} - {0::nat}. c s \<noteq> 0}" by (by100 blast)
      hence hsupp_sub: "\<forall>s \<in> set ?supp. s \<in> {..<m} - {0::nat}" by (by100 blast)
      hence hsupp_sub_m: "\<forall>s \<in> set ?supp. s \<in> {..<m}" by (by100 blast)
      have hsupp_ne0: "\<forall>s \<in> set ?supp. s \<noteq> 0"
      proof (intro ballI)
        fix s assume "s \<in> set ?supp"
        hence "s \<in> {..<m} - {0::nat}" using hsupp_sub by (by100 blast)
        thus "s \<noteq> 0" by (by100 simp)
      qed

      \<comment> \<open>Each element of the mapped list is in AbelF.\<close>
      have hmap_in_F: "\<forall>i < length ?supp. (map (\<lambda>s. if 0 \<le> c s
          then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (c s))
          else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- c s))) ?supp) ! i \<in> ?AbelF"
      proof (intro allI impI)
        fix i assume hi: "i < length ?supp"
        hence "?supp ! i \<in> set ?supp" by (by100 simp)
        hence hs_in: "?\<iota>A (?supp ! i) \<in> ?AbelF" using hsupp_sub_m h\<iota>A_in by (by100 blast)
        have hinv_in: "?invgA (?\<iota>A (?supp ! i)) \<in> ?AbelF"
          using hAbelF_invg_cl hs_in by (by100 blast)
        show "(map (\<lambda>s. if 0 \<le> c s
            then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (c s))
            else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- c s))) ?supp) ! i \<in> ?AbelF"
        proof (cases "0 \<le> c (?supp ! i)")
          case True
          hence "(map (\<lambda>s. if 0 \<le> c s
              then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (c s))
              else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- c s))) ?supp) ! i
              = top1_group_pow ?mulA ?eA (?\<iota>A (?supp ! i)) (nat (c (?supp ! i)))"
            using hi by (by100 simp)
          also have "\<dots> \<in> ?AbelF"
            using group_pow_in_group[OF hAbelF_grp hs_in] by (by100 blast)
          finally show ?thesis .
        next
          case False
          hence "(map (\<lambda>s. if 0 \<le> c s
              then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (c s))
              else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- c s))) ?supp) ! i
              = top1_group_pow ?mulA ?eA (?invgA (?\<iota>A (?supp ! i))) (nat (- c (?supp ! i)))"
            using hi by (by100 simp)
          also have "\<dots> \<in> ?AbelF"
            using group_pow_in_group[OF hAbelF_grp hinv_in] by (by100 blast)
          finally show ?thesis .
        qed
      qed

      \<comment> \<open>Step 3: liftF \<in> AbelF.\<close>
      have hmap_in_F': "\<forall>i < length (map (\<lambda>s. if 0 \<le> c s
          then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (c s))
          else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- c s))) ?supp).
          (map (\<lambda>s. if 0 \<le> c s
          then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (c s))
          else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- c s))) ?supp) ! i \<in> ?AbelF"
        using hmap_in_F by (by100 simp)
      have hlift_in_F: "?liftF \<in> ?AbelF"
        using foldr_mul_closed[OF hAbelF_grp hmap_in_F'] by (by100 blast)

      \<comment> \<open>Step 2: \<phi>\_bar(liftF) = product in AbelG = eAG.\<close>
      have hlift_maps: "\<phi>_bar ?liftF = ?eAG"
      proof -
        let ?fA = "\<lambda>s. if 0 \<le> c s then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (c s))
            else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- c s))"
        let ?fG = "\<lambda>s. if 0 \<le> c s then top1_group_pow ?mulAG ?eAG (\<phi>_bar (?\<iota>A s)) (nat (c s))
            else top1_group_pow ?mulAG ?eAG (?invgAG (\<phi>_bar (?\<iota>A s))) (nat (- c s))"
        \<comment> \<open>\<phi>\_bar commutes with the mapped function.\<close>
        have hmap_comm: "\<forall>s \<in> set ?supp. \<phi>_bar (?fA s) = ?fG s"
        proof (intro ballI)
          fix s assume hs: "s \<in> set ?supp"
          hence hs_in: "?\<iota>A s \<in> ?AbelF" using hsupp_sub_m h\<iota>A_in by (by100 blast)
          show "\<phi>_bar (?fA s) = ?fG s"
          proof (cases "0 \<le> c s")
            case True
            have "\<phi>_bar (top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (c s)))
                = top1_group_pow ?mulAG ?eAG (\<phi>_bar (?\<iota>A s)) (nat (c s))"
              using hom_group_pow[OF hAbelF_grp hAbelG_grp h\<phi>_hom hs_in] by (by100 blast)
            thus ?thesis using True by (by100 simp)
          next
            case False
            have hinv_in: "?invgA (?\<iota>A s) \<in> ?AbelF"
              using hAbelF_invg_cl hs_in by (by100 blast)
            have h1: "\<phi>_bar (top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- c s)))
                = top1_group_pow ?mulAG ?eAG (\<phi>_bar (?invgA (?\<iota>A s))) (nat (- c s))"
              using hom_group_pow[OF hAbelF_grp hAbelG_grp h\<phi>_hom hinv_in] by (by100 blast)
            have h2: "\<phi>_bar (?invgA (?\<iota>A s)) = ?invgAG (\<phi>_bar (?\<iota>A s))"
              using hom_preserves_inv[OF hAbelF_grp hAbelG_grp h\<phi>_hom hs_in] by (by100 simp)
            have "\<phi>_bar (top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- c s)))
                = top1_group_pow ?mulAG ?eAG (?invgAG (\<phi>_bar (?\<iota>A s))) (nat (- c s))"
              using h1 h2 by (by100 simp)
            thus ?thesis using False by (by100 simp)
          qed
        qed
        \<comment> \<open>map \<phi>\_bar (map fA ?supp) = map fG ?supp.\<close>
        have hmap_eq: "map (\<phi>_bar \<circ> ?fA) ?supp = map ?fG ?supp"
        proof (rule list_eq_iff_nth_eq[THEN iffD2], intro conjI allI impI)
          show "length (map (\<phi>_bar \<circ> ?fA) ?supp) = length (map ?fG ?supp)" by (by100 simp)
          fix i assume hi: "i < length (map (\<phi>_bar \<circ> ?fA) ?supp)"
          hence "?supp ! i \<in> set ?supp" by (by100 simp)
          from hmap_comm this show "map (\<phi>_bar \<circ> ?fA) ?supp ! i = map ?fG ?supp ! i"
            using hi by (by100 simp)
        qed
        \<comment> \<open>\<phi>\_bar(foldr mulA (map fA ?supp) eA) = foldr mulAG (map \<phi>\_bar (map fA ?supp)) eAG.\<close>
        have "\<phi>_bar ?liftF = foldr ?mulAG (map \<phi>_bar (map ?fA ?supp)) ?eAG"
          using hom_foldr_mul[OF hAbelF_grp hAbelG_grp h\<phi>_hom hmap_in_F'] by (by100 blast)
        also have "map \<phi>_bar (map ?fA ?supp) = map (\<phi>_bar \<circ> ?fA) ?supp"
          by (by100 simp)
        also have "\<dots> = map ?fG ?supp" using hmap_eq .
        finally show ?thesis using hprod_e by (by100 simp)
      qed

      \<comment> \<open>Step 4: liftF \<in> K0 (i.e., \<epsilon>0(liftF) = 0).\<close>
      have hZ_grp_loc: "top1_is_group_on (UNIV::int set) (+) 0 uminus"
        using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
          top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 blast)
      \<comment> \<open>Each \<epsilon>0(fA(s)) = 0 for s \<in> support.\<close>
      have h\<epsilon>0_each: "\<forall>s \<in> set ?supp. \<epsilon>0 (if 0 \<le> c s
          then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (c s))
          else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- c s))) = 0"
      proof (intro ballI)
        fix s assume hs: "s \<in> set ?supp"
        hence hs_ne0: "s \<noteq> 0" using hsupp_ne0 by (by100 blast)
        hence hs_m: "s \<in> {..<m}" using hsupp_sub_m hs by (by100 blast)
        hence h\<epsilon>0_s: "\<epsilon>0 (?\<iota>A s) = 0" using h\<epsilon>0_rest hs_ne0 by (by100 blast)
        have hs_in: "?\<iota>A s \<in> ?AbelF" using h\<iota>A_in hs_m by (by100 blast)
        show "\<epsilon>0 (if 0 \<le> c s
            then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (c s))
            else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- c s))) = 0"
        proof (cases "0 \<le> c s")
          case True
          have "\<epsilon>0 (top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (c s)))
              = top1_group_pow (+) (0::int) (\<epsilon>0 (?\<iota>A s)) (nat (c s))"
            using hom_group_pow[OF hAbelF_grp hZ_grp_loc h\<epsilon>0_hom hs_in] by (by100 blast)
          also have "\<dots> = int (nat (c s)) * \<epsilon>0 (?\<iota>A s)"
            using int_group_pow by (by100 blast)
          also have "\<dots> = 0" using h\<epsilon>0_s by (by100 simp)
          finally show ?thesis using True by (by100 simp)
        next
          case False
          have hinv_in: "?invgA (?\<iota>A s) \<in> ?AbelF" using hAbelF_invg_cl hs_in by (by100 blast)
          have h\<epsilon>0_inv: "\<epsilon>0 (?invgA (?\<iota>A s)) = - \<epsilon>0 (?\<iota>A s)"
            using hom_preserves_inv[OF hAbelF_grp hZ_grp_loc h\<epsilon>0_hom hs_in] by (by100 simp)
          have "\<epsilon>0 (top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- c s)))
              = top1_group_pow (+) (0::int) (\<epsilon>0 (?invgA (?\<iota>A s))) (nat (- c s))"
            using hom_group_pow[OF hAbelF_grp hZ_grp_loc h\<epsilon>0_hom hinv_in] by (by100 blast)
          also have "\<dots> = int (nat (- c s)) * \<epsilon>0 (?invgA (?\<iota>A s))"
            using int_group_pow by (by100 blast)
          also have "\<dots> = 0" using h\<epsilon>0_inv h\<epsilon>0_s by (by100 simp)
          finally show ?thesis using False by (by100 simp)
        qed
      qed
      have hlift_eps0: "\<epsilon>0 ?liftF = 0"
      proof -
        let ?fA = "\<lambda>s. if 0 \<le> c s then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (c s))
            else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- c s))"
        have "\<epsilon>0 ?liftF = foldr (+) (map \<epsilon>0 (map ?fA ?supp)) (0::int)"
          using hom_foldr_mul[OF hAbelF_grp hZ_grp_loc h\<epsilon>0_hom hmap_in_F'] by (by100 blast)
        \<comment> \<open>Show the list of \<epsilon>0 values is all zeros.\<close>
        also have "\<forall>x \<in> set (map \<epsilon>0 (map ?fA ?supp)). x = (0::int)"
        proof (intro ballI)
          fix x assume "x \<in> set (map \<epsilon>0 (map ?fA ?supp))"
          then obtain s where hs: "s \<in> set ?supp" "x = \<epsilon>0 (?fA s)" by (by100 auto)
          thus "x = 0" using h\<epsilon>0_each by (by100 blast)
        qed
        hence "foldr (+) (map \<epsilon>0 (map ?fA ?supp)) (0::int) = 0"
        proof -
          assume hall: "\<forall>x \<in> set (map \<epsilon>0 (map ?fA ?supp)). x = (0::int)"
          have "\<And>xs::int list. \<forall>x \<in> set xs. x = 0 \<Longrightarrow> foldr (+) xs 0 = 0"
          proof -
            fix xs :: "int list" assume h: "\<forall>x \<in> set xs. x = 0"
            thus "foldr (+) xs 0 = 0" by (induct xs, by100 simp, by100 auto)
          qed
          from this[OF hall] show ?thesis .
        qed
        finally show ?thesis .
      qed

      \<comment> \<open>Step 5: liftF \<in> N\_AbelF (since \<phi>\_bar(liftF) = eAG).\<close>
      have hlift_in_N: "?liftF \<in> ?N_AbelF"
      proof -
        have "?liftF \<in> top1_group_kernel_on ?AbelF ?eAG \<phi>_bar"
          using hlift_in_F hlift_maps unfolding top1_group_kernel_on_def
          by (by100 blast)
        thus ?thesis using hker_\<phi> by (by100 simp)
      qed

      \<comment> \<open>Step 6: liftF \<in> K0 \<inter> N\_AbelF = {eA}.\<close>
      have hlift_eA: "?liftF = ?eA"
      proof -
        have "?liftF \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0} \<inter> ?N_AbelF"
          using hlift_in_F hlift_eps0 hlift_in_N by (by100 blast)
        thus ?thesis using hK0_ker_trivial by (by100 blast)
      qed

      \<comment> \<open>Step 7: By free abelian independence in AbelF, liftF \<noteq> eA.
         Use c' = (\<lambda>s. if s = 0 then 0 else c s). Support = {s\<in>{..<m}-{0}. c(s)\<noteq>0}.
         Since \<exists>s with c(s)\<noteq>0, independence gives liftF \<noteq> eA. Contradiction.\<close>
      have hlift_ne_eA: "?liftF \<noteq> ?eA"
      proof -
        let ?c' = "\<lambda>s::nat. if s = 0 then (0::int) else c s"
        \<comment> \<open>Support of c' in {..<m} = support of c in {..<m}-{0}.\<close>
        have hsupp_eq: "{s \<in> {..<m}. ?c' s \<noteq> 0} = {s \<in> {..<m} - {0::nat}. c s \<noteq> 0}"
          by (by100 auto)
        have hfin': "finite {s \<in> {..<m}. ?c' s \<noteq> 0}" using hfin hsupp_eq by (by100 simp)
        have hex': "\<exists>s\<in>{..<m}. ?c' s \<noteq> 0"
        proof -
          from hex obtain s where "s \<in> {..<m} - {0::nat}" "c s \<noteq> 0" by (by100 blast)
          hence "s \<in> {..<m}" "?c' s \<noteq> 0" by (by100 simp)+
          thus ?thesis by (by100 blast)
        qed
        \<comment> \<open>The SOME xs for c' is the same as ?supp.\<close>
        have hsome_eq: "(SOME xs. set xs = {s \<in> {..<m}. ?c' s \<noteq> 0} \<and> distinct xs) = ?supp"
          using hsupp_eq by (by100 simp)
        \<comment> \<open>The product for c' matches ?liftF (since c'(s) = c(s) for s \<in> support).\<close>
        have hprod_eq: "foldr ?mulA (map (\<lambda>s. if 0 \<le> ?c' s
            then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (?c' s))
            else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- ?c' s)))
          (SOME xs. set xs = {s \<in> {..<m}. ?c' s \<noteq> 0} \<and> distinct xs)) ?eA = ?liftF"
        proof -
          have "map (\<lambda>s. if 0 \<le> ?c' s
              then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (?c' s))
              else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- ?c' s)))
            (SOME xs. set xs = {s \<in> {..<m}. ?c' s \<noteq> 0} \<and> distinct xs)
            = map (\<lambda>s. if 0 \<le> c s
              then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (c s))
              else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- c s))) ?supp"
          proof (rule map_cong)
            show "(SOME xs. set xs = {s \<in> {..<m}. ?c' s \<noteq> 0} \<and> distinct xs) = ?supp"
              using hsome_eq .
            fix s assume "s \<in> set ?supp"
            hence "s \<noteq> 0" using hsupp_ne0 by (by100 blast)
            thus "(if 0 \<le> ?c' s then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (?c' s))
                else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- ?c' s)))
                = (if 0 \<le> c s then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (c s))
                else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- c s)))"
              by (by100 simp)
          qed
          thus ?thesis by (by100 simp)
        qed
        \<comment> \<open>Apply independence from hAbelF\_fab.\<close>
        from h\<iota>A[unfolded top1_is_free_abelian_group_full_on_def]
        have hind: "\<forall>c::nat \<Rightarrow> int. finite {s \<in> {..<m}. c s \<noteq> 0} \<longrightarrow>
            (\<exists>s\<in>{..<m}. c s \<noteq> 0) \<longrightarrow>
            foldr ?mulA (map (\<lambda>s. if 0 \<le> c s
                then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (c s))
                else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- c s)))
              (SOME xs. set xs = {s \<in> {..<m}. c s \<noteq> 0} \<and> distinct xs)) ?eA \<noteq> ?eA"
          by (by100 blast)
        from hind[rule_format, OF hfin' hex']
        have "foldr ?mulA (map (\<lambda>s. if 0 \<le> ?c' s
            then top1_group_pow ?mulA ?eA (?\<iota>A s) (nat (?c' s))
            else top1_group_pow ?mulA ?eA (?invgA (?\<iota>A s)) (nat (- ?c' s)))
          (SOME xs. set xs = {s \<in> {..<m}. ?c' s \<noteq> 0} \<and> distinct xs)) ?eA \<noteq> ?eA"
          by (by100 blast)
        thus "?liftF \<noteq> ?eA" using hprod_eq by (by100 simp)
      qed
      from hlift_eA hlift_ne_eA show False by (by100 simp)
    qed
  qed

  \<comment> \<open>Step G: Reindex {..<m}-{0} to {..<m-1} via the Suc bijection.\<close>
  have hK_fab: "top1_is_free_abelian_group_full_on ?K ?mulAG ?eAG ?invgAG
      ?\<gamma> {..<m-1}"
  proof -
    have hSuc_bij: "bij_betw Suc {..<m-1} ({..<m} - {0::nat})"
      unfolding bij_betw_def
    proof (intro conjI)
      show "inj_on Suc {..<m - 1}" by (by100 simp)
      show "Suc ` {..<m - 1} = {..<m} - {0}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> Suc ` {..<m - 1}"
        thus "x \<in> {..<m} - {0}" using hm1 by (by100 auto)
      next
        fix x assume "x \<in> {..<m} - {0}"
        hence "x > 0" "x < m" by (by100 auto)+
        hence "x - 1 < m - 1" "Suc (x - 1) = x" by (by100 auto)+
        hence "x - 1 \<in> {..<m-1}" by (by100 simp)
        hence "Suc (x - 1) \<in> Suc ` {..<m-1}" by (by100 blast)
        thus "x \<in> Suc ` {..<m - 1}" using \<open>Suc (x - 1) = x\<close> by (by100 simp)
      qed
    qed
    have "?\<gamma> = (\<lambda>s. \<phi>_bar (?\<iota>A s)) \<circ> Suc" by (by100 auto)
    thus ?thesis using free_abelian_reindex[OF hK_fab_raw hSuc_bij] by (by100 simp)
  qed

  \<comment> \<open>K is a group (extract from K\_fab or prove directly from K\_fab\_raw).\<close>
  have hK_grp_outer: "top1_is_group_on ?K ?mulAG ?eAG ?invgAG"
    using hK_fab unfolding top1_is_free_abelian_group_full_on_def top1_is_abelian_group_on_def
    by (by100 blast)

  \<comment> \<open>Both eAG and \<phi>_bar(\<beta>) are torsion elements.\<close>
  have heAG_torsion: "?eAG \<in> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG"
  proof -
    have "?eAG \<in> ?AbelG" using hAbelG_grp unfolding top1_is_group_on_def by (by100 blast)
    moreover have "top1_group_pow ?mulAG ?eAG ?eAG 1 = ?eAG"
    proof -
      have "top1_group_pow ?mulAG ?eAG ?eAG 1 = ?mulAG ?eAG ?eAG"
        by (by100 simp)
      also have "\<dots> = ?eAG" using hAbelG_grp unfolding top1_is_group_on_def by (by100 blast)
      finally show ?thesis .
    qed
    ultimately show ?thesis unfolding top1_torsion_subgroup_on_def by (by100 blast)
  qed
  have h\<beta>G_torsion: "?\<beta>G \<in> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG"
  proof -
    have "top1_group_pow ?mulAG ?eAG ?\<beta>G 2 = ?eAG"
    proof -
      have "top1_group_pow ?mulAG ?eAG ?\<beta>G 2 = ?mulAG ?\<beta>G ?\<beta>G"
      proof -
        have h2: "(2::nat) = Suc (Suc 0)" by (by100 simp)
        have "top1_group_pow ?mulAG ?eAG ?\<beta>G 2
            = ?mulAG ?\<beta>G (?mulAG ?\<beta>G ?eAG)"
          unfolding h2 by (by100 simp)
        also have "\<dots> = ?mulAG ?\<beta>G ?\<beta>G"
        proof -
          have "\<forall>x\<in>?AbelG. ?mulAG x ?eAG = x"
            using hAbelG_grp unfolding top1_is_group_on_def by (by100 blast)
          hence "?mulAG ?\<beta>G ?eAG = ?\<beta>G" using h\<beta>G_in by (by100 blast)
          thus ?thesis by (by100 simp)
        qed
        finally show ?thesis .
      qed
      thus ?thesis using h\<beta>G_order2 by (by100 simp)
    qed
    hence "\<exists>n. n > 0 \<and> top1_group_pow ?mulAG ?eAG ?\<beta>G n = ?eAG"
    proof -
      assume h: "top1_group_pow ?mulAG ?eAG ?\<beta>G 2 = ?eAG"
      have "(2::nat) > 0" by (by100 simp)
      with h show ?thesis by (by100 blast)
    qed
    thus ?thesis using h\<beta>G_in unfolding top1_torsion_subgroup_on_def by (by100 blast)
  qed

  \<comment> \<open>Step H: K \<inter> torsion = {eAG}.
     K is free abelian, free abelian groups are torsion-free.\<close>
  have hK_tors: "?K \<inter> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG = {?eAG}"
  proof (rule set_eqI, rule iffI)
    fix x assume hx: "x \<in> ?K \<inter> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG"
    hence hx_K: "x \<in> ?K" and hx_tors: "x \<in> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG"
      by (by100 blast)+
    from hx_tors obtain n where "n > 0" "top1_group_pow ?mulAG ?eAG x n = ?eAG"
      unfolding top1_torsion_subgroup_on_def by (by100 blast)
    have "x \<in> ?K" using hx_K .
    have hfin_m1: "finite ({..<m-1}::nat set)" by (by100 simp)
    have "x \<in> ?K" using hx_K .
    from free_abelian_torsion_free[OF hK_fab hfin_m1 this \<open>n > 0\<close> \<open>top1_group_pow ?mulAG ?eAG x n = ?eAG\<close>]
    have "x = ?eAG" .
    thus "x \<in> {?eAG}" by (by100 blast)
  next
    fix x assume "x \<in> {?eAG}"
    hence "x = ?eAG" by (by100 blast)
    have "?eAG \<in> ?K"
    proof -
      have "top1_is_group_on ?K ?mulAG ?eAG ?invgAG"
        using hK_fab unfolding top1_is_free_abelian_group_full_on_def
          top1_is_abelian_group_on_def by (by100 blast)
      thus ?thesis unfolding top1_is_group_on_def by (by100 blast)
    qed
    moreover have "?eAG \<in> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG"
    proof -
      have heAG_in: "?eAG \<in> ?AbelG" using hAbelG_grp unfolding top1_is_group_on_def by (by100 blast)
      moreover have "top1_group_pow ?mulAG ?eAG ?eAG 1 = ?eAG"
      proof -
        have "top1_group_pow ?mulAG ?eAG ?eAG 1 = ?mulAG ?eAG (top1_group_pow ?mulAG ?eAG ?eAG 0)"
          by (by100 simp)
        also have "top1_group_pow ?mulAG ?eAG ?eAG 0 = ?eAG" by (by100 simp)
        also have "?mulAG ?eAG ?eAG = ?eAG"
          using hAbelG_grp heAG_in unfolding top1_is_group_on_def by (by100 fast)
        finally show ?thesis .
      qed
      moreover have "(1::nat) > 0" by (by100 simp)
      ultimately show ?thesis unfolding top1_torsion_subgroup_on_def by (by100 blast)
    qed
    ultimately show "x \<in> ?K \<inter> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG"
      using \<open>x = ?eAG\<close> by (by100 blast)
  qed

  \<comment> \<open>Extracted: tail product and its properties (used in both decomposition and torsion classification).\<close>
  let ?tail_outer = "foldr ?mulA (map ?\<iota>A [1..<m]) ?eA"
  have htail_K0_outer: "?tail_outer \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0}"
  proof -
    have htail_in: "?tail_outer \<in> ?AbelF"
    proof -
      have "\<forall>i<length (map ?\<iota>A [1..<m]). (map ?\<iota>A [1..<m]) ! i \<in> ?AbelF"
        using h\<iota>A_in by (by100 auto)
      thus ?thesis using foldr_mul_closed[OF hAbelF_grp] by (by100 blast)
    qed
    have "\<epsilon>0 ?tail_outer = 0"
    proof -
      have hZ_grp_l: "top1_is_group_on (UNIV::int set) (+) 0 uminus"
        using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
          top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 blast)
      have "\<forall>i<length (map ?\<iota>A [1..<m]). (map ?\<iota>A [1..<m]) ! i \<in> ?AbelF"
        using h\<iota>A_in by (by100 auto)
      hence "\<epsilon>0 ?tail_outer = foldr (+) (map \<epsilon>0 (map ?\<iota>A [1..<m])) (0::int)"
        using hom_foldr_mul[OF hAbelF_grp hZ_grp_l h\<epsilon>0_hom] by (by100 blast)
      also have "\<dots> = foldr (+) (map (\<epsilon>0 \<circ> ?\<iota>A) [1..<m]) 0" by (by100 simp)
      also have "\<dots> = 0"
      proof -
        have "\<forall>i\<in>set [1..<m]. (\<epsilon>0 \<circ> ?\<iota>A) i = 0"
          using h\<epsilon>0_rest by (by100 auto)
        thus ?thesis by (induct m, by100 simp, by100 simp)
      qed
      finally show ?thesis .
    qed
    thus ?thesis using htail_in by (by100 blast)
  qed
  have hinv_tail_K_outer: "?invgAG (\<phi>_bar ?tail_outer) \<in> ?K"
  proof -
    have "?tail_outer \<in> ?AbelF" using htail_K0_outer by (by100 blast)
    have "?invgAG (\<phi>_bar ?tail_outer) = \<phi>_bar (?invgA ?tail_outer)"
      using hom_preserves_inv[OF hAbelF_grp hAbelG_grp h\<phi>_hom \<open>?tail_outer \<in> ?AbelF\<close>]
      by (by100 simp)
    moreover have "?invgA ?tail_outer \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0}"
    proof -
      have "?invgA ?tail_outer \<in> ?AbelF" using hAbelF_invg_cl \<open>?tail_outer \<in> ?AbelF\<close> by (by100 blast)
      have hZ_grp_l: "top1_is_group_on (UNIV::int set) (+) 0 uminus"
        using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
          top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 blast)
      have "\<epsilon>0 (?invgA ?tail_outer) = - \<epsilon>0 ?tail_outer"
        using hom_preserves_inv[OF hAbelF_grp hZ_grp_l h\<epsilon>0_hom \<open>?tail_outer \<in> ?AbelF\<close>]
        by (by100 simp)
      hence "\<epsilon>0 (?invgA ?tail_outer) = 0" using htail_K0_outer by (by100 simp)
      thus ?thesis using \<open>?invgA ?tail_outer \<in> ?AbelF\<close> by (by100 blast)
    qed
    ultimately show ?thesis by (by100 force)
  qed
  \<comment> \<open>\<phi>\_bar(\<iota>A 0) = mulAG (invgAG(\<phi>\_bar(tail))) \<beta>G (in abelian group).\<close>
  have h\<iota>A0_decomp: "\<phi>_bar (?\<iota>A 0) = ?mulAG (?invgAG (\<phi>_bar ?tail_outer)) ?\<beta>G"
  proof -
    have h\<beta>_split: "?\<beta>A = ?mulA (?\<iota>A 0) ?tail_outer"
    proof -
      have "[0..<m] = 0 # [1..<m]" using upt_conv_Cons[of 0 m] hm1 by (by100 simp)
      hence "map ?\<iota>A [0..<m] = ?\<iota>A 0 # map ?\<iota>A [1..<m]" by (by100 simp)
      thus ?thesis by (by100 simp)
    qed
    have h\<iota>A0_in: "?\<iota>A 0 \<in> ?AbelF" using h\<iota>A_in hm1 by (by100 auto)
    have htail_in: "?tail_outer \<in> ?AbelF" using htail_K0_outer by (by100 blast)
    have "\<phi>_bar ?\<beta>A = ?mulAG (\<phi>_bar (?\<iota>A 0)) (\<phi>_bar ?tail_outer)"
    proof -
      have "\<phi>_bar (?mulA (?\<iota>A 0) ?tail_outer) = ?mulAG (\<phi>_bar (?\<iota>A 0)) (\<phi>_bar ?tail_outer)"
        using h\<phi>_hom h\<iota>A0_in htail_in unfolding top1_group_hom_on_def by (by5000 blast)
      thus ?thesis using h\<beta>_split by (by100 simp)
    qed
    hence h\<beta>G_eq: "?\<beta>G = ?mulAG (\<phi>_bar (?\<iota>A 0)) (\<phi>_bar ?tail_outer)" by (by100 simp)
    \<comment> \<open>\<phi>\_bar(\<iota>A 0) = \<beta>G \<cdot> tail^{-1} = invgAG(tail) \<cdot> \<beta>G (abelian).\<close>
    have hphitail_in: "\<phi>_bar ?tail_outer \<in> ?AbelG"
      using h\<phi>_hom htail_in unfolding top1_group_hom_on_def by (by100 blast)
    have h\<iota>A0_img_in: "\<phi>_bar (?\<iota>A 0) \<in> ?AbelG"
      using h\<phi>_hom h\<iota>A0_in unfolding top1_group_hom_on_def by (by5000 blast)
    have hinvtail_in: "?invgAG (\<phi>_bar ?tail_outer) \<in> ?AbelG"
      using hAbelG_grp hphitail_in unfolding top1_is_group_on_def by (by100 fast)
    \<comment> \<open>\<beta>G = \<phi>\_bar(\<iota>A 0) \<cdot> \<phi>\_bar(tail). Multiply both sides by invgAG(\<phi>\_bar(tail)) on right.\<close>
    have "?mulAG ?\<beta>G (?invgAG (\<phi>_bar ?tail_outer))
        = ?mulAG (?mulAG (\<phi>_bar (?\<iota>A 0)) (\<phi>_bar ?tail_outer)) (?invgAG (\<phi>_bar ?tail_outer))"
      using h\<beta>G_eq by (by100 simp)
    also have "\<dots> = ?mulAG (\<phi>_bar (?\<iota>A 0)) (?mulAG (\<phi>_bar ?tail_outer) (?invgAG (\<phi>_bar ?tail_outer)))"
    proof -
      have hkb: "\<forall>i<length [\<phi>_bar (?\<iota>A 0), \<phi>_bar ?tail_outer]. [\<phi>_bar (?\<iota>A 0), \<phi>_bar ?tail_outer]!i \<in> ?AbelG"
        using h\<iota>A0_img_in hphitail_in by (intro allI impI, auto simp: nth_Cons split: nat.splits)
      have hinv_l: "\<forall>i<length [?invgAG (\<phi>_bar ?tail_outer)]. [?invgAG (\<phi>_bar ?tail_outer)]!i \<in> ?AbelG"
        using hinvtail_in by (by100 auto)
      have hb1: "\<forall>i<length [\<phi>_bar (?\<iota>A 0)]. [\<phi>_bar (?\<iota>A 0)]!i \<in> ?AbelG"
        using h\<iota>A0_img_in by (by100 auto)
      have hbi: "\<forall>i<length [\<phi>_bar ?tail_outer, ?invgAG (\<phi>_bar ?tail_outer)]. [\<phi>_bar ?tail_outer, ?invgAG (\<phi>_bar ?tail_outer)]!i \<in> ?AbelG"
        using hphitail_in hinvtail_in by (intro allI impI, auto simp: nth_Cons split: nat.splits)
      have lhs: "foldr ?mulAG ([\<phi>_bar (?\<iota>A 0), \<phi>_bar ?tail_outer] @ [?invgAG (\<phi>_bar ?tail_outer)]) ?eAG
          = ?mulAG (foldr ?mulAG [\<phi>_bar (?\<iota>A 0), \<phi>_bar ?tail_outer] ?eAG) (foldr ?mulAG [?invgAG (\<phi>_bar ?tail_outer)] ?eAG)"
        using foldr_mul_append[OF hAbelG_grp hkb hinv_l] by (by100 blast)
      have rhs: "foldr ?mulAG ([\<phi>_bar (?\<iota>A 0)] @ [\<phi>_bar ?tail_outer, ?invgAG (\<phi>_bar ?tail_outer)]) ?eAG
          = ?mulAG (foldr ?mulAG [\<phi>_bar (?\<iota>A 0)] ?eAG) (foldr ?mulAG [\<phi>_bar ?tail_outer, ?invgAG (\<phi>_bar ?tail_outer)] ?eAG)"
        using foldr_mul_append[OF hAbelG_grp hb1 hbi] by (by100 blast)
      have hidG: "\<forall>x\<in>?AbelG. ?mulAG x ?eAG = x"
        using hAbelG_grp[unfolded top1_is_group_on_def] by (by100 fast)
      show ?thesis using lhs rhs hidG h\<iota>A0_img_in hphitail_in hinvtail_in by (by100 simp)
    qed
    also have "?mulAG (\<phi>_bar ?tail_outer) (?invgAG (\<phi>_bar ?tail_outer)) = ?eAG"
      using hAbelG_grp hphitail_in unfolding top1_is_group_on_def by (by100 fast)
    also have "?mulAG (\<phi>_bar (?\<iota>A 0)) ?eAG = \<phi>_bar (?\<iota>A 0)"
      using hAbelG_grp h\<iota>A0_img_in unfolding top1_is_group_on_def by (by100 fast)
    finally have "?mulAG ?\<beta>G (?invgAG (\<phi>_bar ?tail_outer)) = \<phi>_bar (?\<iota>A 0)" .
    \<comment> \<open>Abelian: mulAG \<beta>G k' = mulAG k' \<beta>G.\<close>
    moreover have "?mulAG ?\<beta>G (?invgAG (\<phi>_bar ?tail_outer))
        = ?mulAG (?invgAG (\<phi>_bar ?tail_outer)) ?\<beta>G"
    proof -
      obtain gx gy where hgx: "gx \<in> G0" "?\<beta>G = ?pG gx"
          and hgy: "gy \<in> G0" "?invgAG (\<phi>_bar ?tail_outer) = ?pG gy"
        using h\<beta>G_in hinvtail_in
        unfolding top1_quotient_group_carrier_on_def by (by100 blast)
      from quotient_by_commutator_is_abelian[OF hG0] hgx(1) hgy(1)
      have "?mulAG (?pG gx) (?pG gy) = ?mulAG (?pG gy) (?pG gx)" by (by100 blast)
      thus ?thesis using hgx(2) hgy(2) by (by100 simp)
    qed
    ultimately show ?thesis by (by100 simp)
  qed

  \<comment> \<open>Step I: Decomposition. Every h \<in> AbelG decomposes as k \<cdot> t.
     For h = \<phi>\_bar(a): a = (a - \<epsilon>_0(a)\<cdot>\<beta>) + \<epsilon>_0(a)\<cdot>\<beta>.
     First part \<in> K_0 (its \<epsilon>_0 value = \<epsilon>_0(a) - \<epsilon>_0(a)\<cdot>\<epsilon>_0(\<beta>) = 0).
     Second part maps to pow(\<beta>G, \<epsilon>_0(a)) which is e or \<beta>G.\<close>
  have hK_decomp: "\<forall>h\<in>?AbelG. \<exists>k\<in>?K. \<exists>t\<in>top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG.
        h = ?mulAG k t"
  proof (intro ballI)
    fix h assume hh: "h \<in> ?AbelG"
    \<comment> \<open>h = \<phi>\_bar(a) for some a \<in> AbelF (surjectivity).\<close>
    have "h \<in> \<phi>_bar ` ?AbelF" using hh h\<phi>_surj by (by100 simp)
    then obtain a where ha: "a \<in> ?AbelF" "\<phi>_bar a = h" by (by100 blast)
    \<comment> \<open>Decompose: let k = \<phi>\_bar(a') where a' \<in> K_0, and t \<in> {eAG, \<beta>G}.
       a' = a \<cdot> invgA(pow(\<beta>, \<epsilon>_0(a))) — has \<epsilon>_0 value 0.
       t = pow(\<beta>G, \<epsilon>_0(a) mod 2).\<close>
    \<comment> \<open>For now, use a simpler argument: every generator of AbelG is in K \<cup> K\<cdot>{\<beta>G}.
       For i > 0: \<phi>\_bar(\<iota>A i) \<in> K (since \<epsilon>_0(\<iota>A i) = 0).
       For i = 0: \<phi>\_bar(\<iota>A 0) = \<beta>G \<cdot> k' for some k' \<in> K
       (since \<beta> = \<iota>A 0 \<cdot> ... \<cdot> \<iota>A(m-1), so \<iota>A 0 = \<beta> \<cdot> (\<iota>A 1 \<cdot> ... \<cdot> \<iota>A(m-1))^{-1}).
       Since AbelG is generated by {\<phi>\_bar(\<iota>A i)}, every element decomposes.\<close>
    \<comment> \<open>Use abelian\_generated\_decomposes\_via\_order2.
       AbelG generated by \<phi>\_bar(\<iota>A i). For i>0: in K. For i=0: = \<beta>G \<cdot> k'.\<close>
    \<comment> \<open>Step 1: AbelG is generated by {\<phi>\_bar(\<iota>A i) | i < m}.\<close>
    have hAbelG_gen: "?AbelG = top1_subgroup_generated_on ?AbelG ?mulAG ?eAG ?invgAG
        ((\<lambda>i. \<phi>_bar (?\<iota>A i)) ` {..<m})"
    proof -
      have h\<iota>A_sub: "?\<iota>A ` {..<m} \<subseteq> ?AbelF"
        using h\<iota>A_in by (by100 blast)
      have hAbelF_gen: "?AbelF = top1_subgroup_generated_on ?AbelF ?mulA ?eA ?invgA (?\<iota>A ` {..<m})"
        using h\<iota>A unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
      have "?AbelG = top1_subgroup_generated_on ?AbelG ?mulAG ?eAG ?invgAG (\<phi>_bar ` (?\<iota>A ` {..<m}))"
        by (rule surj_hom_generated[OF hAbelF_grp hAbelG_grp h\<phi>_hom h\<phi>_surj h\<iota>A_sub hAbelF_gen])
      moreover have "\<phi>_bar ` (?\<iota>A ` {..<m}) = (\<lambda>i. \<phi>_bar (?\<iota>A i)) ` {..<m}"
        by (by100 auto)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Step 2: Each generator decomposes.\<close>
    have hgen_decomp: "\<forall>a \<in> (\<lambda>i. \<phi>_bar (?\<iota>A i)) ` {..<m}.
        a \<in> ?K \<or> (\<exists>k\<in>?K. a = ?mulAG k ?\<beta>G)"
    proof (intro ballI)
      fix a assume "a \<in> (\<lambda>i. \<phi>_bar (?\<iota>A i)) ` {..<m}"
      then obtain i where hi: "i < m" "a = \<phi>_bar (?\<iota>A i)" by (by100 blast)
      show "a \<in> ?K \<or> (\<exists>k\<in>?K. a = ?mulAG k ?\<beta>G)"
      proof (cases "i = 0")
        case False
        \<comment> \<open>For i > 0: \<phi>\_bar(\<iota>A i) \<in> K since \<epsilon>_0(\<iota>A i) = 0.\<close>
        hence "\<epsilon>0 (?\<iota>A i) = 0" using h\<epsilon>0_rest hi(1) by (by100 blast)
        moreover have "?\<iota>A i \<in> ?AbelF" using h\<iota>A_in hi(1) by (by100 blast)
        ultimately have "?\<iota>A i \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0}" by (by100 blast)
        hence "\<phi>_bar (?\<iota>A i) \<in> ?K" by (by100 blast)
        thus ?thesis using hi(2) by (by100 blast)
      next
        case True
        \<comment> \<open>For i = 0: \<iota>A 0 = \<beta> \<cdot> (\<iota>A 1 \<cdot> ... \<cdot> \<iota>A(m-1))^{-1}.
           After \<phi>\_bar: \<phi>\_bar(\<iota>A 0) = \<beta>G \<cdot> (\<phi>\_bar(\<iota>A 1 \<cdot> ... \<cdot> \<iota>A(m-1)))^{-1}.
           The product \<iota>A 1 \<cdot> ... \<cdot> \<iota>A(m-1) has \<epsilon>_0 = 0, so its image \<in> K.
           Then k' = invgAG(\<phi>\_bar(product)) \<in> K (K closed under inv).
           So \<phi>\_bar(\<iota>A 0) = \<beta>G \<cdot> ... = mulAG (invgAG(k')) \<beta>G ... \<close>
        \<comment> \<open>\<beta> = \<iota>A(0) \<cdot> tail, so \<iota>A(0) = \<beta> \<cdot> tail^{-1}. After \<phi>\_bar: = \<beta>G \<cdot> invgAG(tail\_img).
           tail = foldr mulA (map \<iota>A [1..<m]) eA has \<epsilon>_0 = 0, so tail\_img \<in> K.
           invgAG(tail\_img) \<in> K (K closed under inv). So \<phi>\_bar(\<iota>A 0) = mulAG k' \<beta>G.\<close>
        let ?tail = "foldr ?mulA (map ?\<iota>A [1..<m]) ?eA"
        have "?\<beta>A = ?mulA (?\<iota>A 0) ?tail"
        proof -
          have "[0..<m] = 0 # [1..<m]"
            using upt_conv_Cons[of 0 m] hm1 by (by100 simp)
          hence "map ?\<iota>A [0..<m] = ?\<iota>A 0 # map ?\<iota>A [1..<m]" by (by100 simp)
          thus ?thesis by (by100 simp)
        qed
        have htail_K0: "?tail \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0}"
        proof -
          have htail_in: "?tail \<in> ?AbelF"
          proof -
            have "\<forall>i<length (map ?\<iota>A [1..<m]). (map ?\<iota>A [1..<m]) ! i \<in> ?AbelF"
              using h\<iota>A_in by (by100 auto)
            thus ?thesis using foldr_mul_closed[OF hAbelF_grp] by (by100 blast)
          qed
          have "\<epsilon>0 ?tail = 0"
          proof -
            have hZ_grp_l: "top1_is_group_on (UNIV::int set) (+) 0 uminus"
              using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
                top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 blast)
            have "\<forall>i<length (map ?\<iota>A [1..<m]). (map ?\<iota>A [1..<m]) ! i \<in> ?AbelF"
              using h\<iota>A_in by (by100 auto)
            hence "\<epsilon>0 ?tail = foldr (+) (map \<epsilon>0 (map ?\<iota>A [1..<m])) (0::int)"
              using hom_foldr_mul[OF hAbelF_grp hZ_grp_l h\<epsilon>0_hom] by (by100 blast)
            also have "\<dots> = foldr (+) (map (\<epsilon>0 \<circ> ?\<iota>A) [1..<m]) 0" by (by100 simp)
            also have "\<dots> = 0"
            proof -
              have "\<forall>i\<in>set [1..<m]. (\<epsilon>0 \<circ> ?\<iota>A) i = 0"
                using h\<epsilon>0_rest by (by100 auto)
              thus ?thesis by (induct m, by100 simp, by100 simp)
            qed
            finally show ?thesis .
          qed
          thus ?thesis using htail_in by (by100 blast)
        qed
        have htail_img_K: "\<phi>_bar ?tail \<in> ?K" using htail_K0 by (by100 blast)
        have hinv_tail_K: "?invgAG (\<phi>_bar ?tail) \<in> ?K"
        proof -
          have "?tail \<in> ?AbelF" using htail_K0 by (by100 blast)
          have "?invgAG (\<phi>_bar ?tail) = \<phi>_bar (?invgA ?tail)"
            using hom_preserves_inv[OF hAbelF_grp hAbelG_grp h\<phi>_hom \<open>?tail \<in> ?AbelF\<close>]
            by (by100 simp)
          moreover have "?invgA ?tail \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0}"
          proof -
            have "?invgA ?tail \<in> ?AbelF" using hAbelF_invg_cl \<open>?tail \<in> ?AbelF\<close> by (by100 blast)
            have hZ_grp_l: "top1_is_group_on (UNIV::int set) (+) 0 uminus"
              using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
                top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 blast)
            have "\<epsilon>0 (?invgA ?tail) = - \<epsilon>0 ?tail"
              using hom_preserves_inv[OF hAbelF_grp hZ_grp_l h\<epsilon>0_hom \<open>?tail \<in> ?AbelF\<close>]
              by (by100 simp)
            hence "\<epsilon>0 (?invgA ?tail) = 0" using htail_K0 by (by100 simp)
            thus ?thesis using \<open>?invgA ?tail \<in> ?AbelF\<close> by (by100 blast)
          qed
          ultimately show ?thesis by (by100 force)
        qed
        \<comment> \<open>In abelian AbelG: \<phi>\_bar(\<iota>A 0) = mulAG (invgAG(\<phi>\_bar(tail))) \<beta>G.\<close>
        have "a = ?mulAG (?invgAG (\<phi>_bar ?tail)) ?\<beta>G"
        proof -
          have h\<iota>A0_in: "?\<iota>A 0 \<in> ?AbelF" using h\<iota>A_in hm1 by (by100 auto)
          have htail_in: "?tail \<in> ?AbelF" using htail_K0 by (by100 blast)
          \<comment> \<open>\<phi>\_bar(\<beta>) = mulAG(\<phi>\_bar(\<iota>A 0))(\<phi>\_bar(tail)).\<close>
          have "\<phi>_bar ?\<beta>A = ?mulAG (\<phi>_bar (?\<iota>A 0)) (\<phi>_bar ?tail)"
          proof -
            have "\<phi>_bar (?mulA (?\<iota>A 0) ?tail) = ?mulAG (\<phi>_bar (?\<iota>A 0)) (\<phi>_bar ?tail)"
              using h\<phi>_hom h\<iota>A0_in htail_in unfolding top1_group_hom_on_def by (by5000 blast)
            thus ?thesis using \<open>?\<beta>A = ?mulA (?\<iota>A 0) ?tail\<close> by (by100 simp)
          qed
          hence h\<beta>G_eq: "?\<beta>G = ?mulAG a (\<phi>_bar ?tail)" using hi(2) True by (by100 simp)
          \<comment> \<open>a = mulAG \<beta>G (invgAG(\<phi>\_bar(tail))).\<close>
          have hphitail_in: "\<phi>_bar ?tail \<in> ?AbelG"
            using h\<phi>_hom htail_in unfolding top1_group_hom_on_def by (by100 blast)
          have ha_in: "a \<in> ?AbelG"
          proof -
            have "\<phi>_bar (?\<iota>A 0) \<in> ?AbelG"
              using h\<phi>_hom h\<iota>A0_in unfolding top1_group_hom_on_def by (by5000 blast)
            thus ?thesis using hi(2) True by (by100 simp)
          qed
          have hinvtail_in: "?invgAG (\<phi>_bar ?tail) \<in> ?AbelG"
            using hAbelG_grp hphitail_in unfolding top1_is_group_on_def by (by100 fast)
          \<comment> \<open>From \<beta>G = a \<cdot> tail\_img: a = \<beta>G \<cdot> tail\_img^{-1}.\<close>
          have "?mulAG ?\<beta>G (?invgAG (\<phi>_bar ?tail)) = ?mulAG (?mulAG a (\<phi>_bar ?tail)) (?invgAG (\<phi>_bar ?tail))"
            using h\<beta>G_eq by (by100 simp)
          also have "\<dots> = ?mulAG a (?mulAG (\<phi>_bar ?tail) (?invgAG (\<phi>_bar ?tail)))"
          proof -
            \<comment> \<open>Assoc in AbelG via foldr\_mul\_append.\<close>
            have hab: "\<forall>i<length [a, \<phi>_bar ?tail]. [a, \<phi>_bar ?tail]!i \<in> ?AbelG"
              using ha_in hphitail_in by (intro allI impI, auto simp: nth_Cons split: nat.splits)
            have hc: "\<forall>i<length [?invgAG (\<phi>_bar ?tail)]. [?invgAG (\<phi>_bar ?tail)]!i \<in> ?AbelG"
              using hinvtail_in by (by100 auto)
            have ha1: "\<forall>i<length [a]. [a]!i \<in> ?AbelG" using ha_in by (by100 auto)
            have hbc: "\<forall>i<length [\<phi>_bar ?tail, ?invgAG (\<phi>_bar ?tail)]. [\<phi>_bar ?tail, ?invgAG (\<phi>_bar ?tail)]!i \<in> ?AbelG"
              using hphitail_in hinvtail_in by (intro allI impI, auto simp: nth_Cons split: nat.splits)
            have lhs: "foldr ?mulAG ([a, \<phi>_bar ?tail] @ [?invgAG (\<phi>_bar ?tail)]) ?eAG
                = ?mulAG (foldr ?mulAG [a, \<phi>_bar ?tail] ?eAG) (foldr ?mulAG [?invgAG (\<phi>_bar ?tail)] ?eAG)"
              using foldr_mul_append[OF hAbelG_grp hab hc] by (by100 blast)
            have rhs: "foldr ?mulAG ([a] @ [\<phi>_bar ?tail, ?invgAG (\<phi>_bar ?tail)]) ?eAG
                = ?mulAG (foldr ?mulAG [a] ?eAG) (foldr ?mulAG [\<phi>_bar ?tail, ?invgAG (\<phi>_bar ?tail)] ?eAG)"
              using foldr_mul_append[OF hAbelG_grp ha1 hbc] by (by100 blast)
            have hidG: "\<forall>x\<in>?AbelG. ?mulAG x ?eAG = x"
              using hAbelG_grp[unfolded top1_is_group_on_def] by (by100 fast)
            show ?thesis using lhs rhs hidG ha_in hphitail_in hinvtail_in by (by100 simp)
          qed
          also have "?mulAG (\<phi>_bar ?tail) (?invgAG (\<phi>_bar ?tail)) = ?eAG"
            using hAbelG_grp hphitail_in unfolding top1_is_group_on_def by (by100 fast)
          also have "?mulAG a ?eAG = a"
            using hAbelG_grp ha_in unfolding top1_is_group_on_def by (by100 fast)
          finally have "?mulAG ?\<beta>G (?invgAG (\<phi>_bar ?tail)) = a" .
          \<comment> \<open>In abelian: mulAG \<beta>G k' = mulAG k' \<beta>G.\<close>
          moreover have "?mulAG ?\<beta>G (?invgAG (\<phi>_bar ?tail)) = ?mulAG (?invgAG (\<phi>_bar ?tail)) ?\<beta>G"
          proof -
            have "?\<beta>G \<in> ?AbelG" using h\<beta>G_in .
            have "?invgAG (\<phi>_bar ?tail) \<in> ?AbelG" using hinvtail_in .
            then obtain gx gy where hgx: "gx \<in> G0" "?\<beta>G = ?pG gx"
              and hgy: "gy \<in> G0" "?invgAG (\<phi>_bar ?tail) = ?pG gy"
              using \<open>?\<beta>G \<in> ?AbelG\<close>
              unfolding top1_quotient_group_carrier_on_def by (by100 blast)
            from quotient_by_commutator_is_abelian[OF hG0] hgx(1) hgy(1)
            have "?mulAG (?pG gx) (?pG gy) = ?mulAG (?pG gy) (?pG gx)" by (by100 blast)
            thus ?thesis using hgx(2) hgy(2) by (by100 simp)
          qed
          ultimately show ?thesis by (by100 simp)
        qed
        thus ?thesis using hinv_tail_K by (by100 blast)
      qed
    qed
    \<comment> \<open>Step 3: Apply the helper.\<close>
    \<comment> \<open>K group: K \<subseteq> AbelG (group), K abelian proven in K\_fab\_raw's proof.
       But hK\_grp inside K\_fab\_raw's proof block is not in scope.
       Re-derive: use hAbelG\_grp restricted to K.\<close>
    have hK_grp_loc: "top1_is_group_on ?K ?mulAG ?eAG ?invgAG"
      using hK_grp_outer .
    have hgens_sub: "(\<lambda>i. \<phi>_bar (?\<iota>A i)) ` {..<m} \<subseteq> ?AbelG"
      using h\<phi>_hom h\<iota>A_in unfolding top1_group_hom_on_def by (by100 blast)
    from abelian_generated_decomposes_via_order2[OF hAbelG_abel hAbelG_gen hK_grp_loc
        hK_sub h\<beta>G_in h\<beta>G_order2 hgens_sub hgen_decomp]
    have hdecomp: "\<forall>g\<in>?AbelG. \<exists>k\<in>?K. g = k \<or> g = ?mulAG k ?\<beta>G" by (by100 blast)
    \<comment> \<open>Convert to ∃k∈K. ∃t∈torsion. h = mulAG k t.\<close>
    from hdecomp[rule_format, OF hh] obtain k where hk: "k \<in> ?K" and hkh: "h = k \<or> h = ?mulAG k ?\<beta>G"
      by (by100 blast)
    show "\<exists>k\<in>?K. \<exists>t\<in>top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG. h = ?mulAG k t"
    proof (cases "h = k")
      case True
      have "?eAG \<in> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG"
        using heAG_torsion .
      moreover have "h = ?mulAG k ?eAG"
      proof -
        have "k \<in> ?AbelG" using hk hK_sub by (by100 blast)
        from hAbelG_grp[unfolded top1_is_group_on_def] this
        have "?mulAG k ?eAG = k" by (by100 fast)
        thus ?thesis using True by (by100 simp)
      qed
      ultimately show ?thesis using hk by (by100 blast)
    next
      case False
      hence "h = ?mulAG k ?\<beta>G" using hkh by (by100 blast)
      have h\<beta>_tors_loc: "?\<beta>G \<in> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG"
        using h\<beta>G_torsion .
      show ?thesis
        apply (rule bexI[of _ k])
        apply (rule bexI[of _ "?\<beta>G"])
        using \<open>h = ?mulAG k ?\<beta>G\<close> hk h\<beta>_tors_loc by (by100 blast)+
    qed
  qed

  \<comment> \<open>Assemble free part existential.\<close>
  have hAbelG_free_part: "\<exists>(K :: (real \<Rightarrow> 'a) set set set set) (\<iota>_K :: nat \<Rightarrow> (real \<Rightarrow> 'a) set set set).
      K \<subseteq> ?AbelG
    \<and> top1_is_free_abelian_group_full_on K ?mulAG ?eAG ?invgAG \<iota>_K {..<m-1}
    \<and> K \<inter> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG = {?eAG}
    \<and> (\<forall>h\<in>?AbelG. \<exists>k\<in>K. \<exists>t\<in>top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG.
          h = ?mulAG k t)"
    using hK_sub hK_fab hK_tors hK_decomp by (by100 blast)

  \<comment> \<open>Torsion classification as corollary of free part decomposition (expert audit 11):
     h torsion, h = k\<cdot>t with k\<in>K, t\<in>{e,\<beta>G}.
     k = h\<cdot>t^{-1} is torsion in abelian group. K torsion-free, so k=e. h=t\<in>{e,\<beta>G}.\<close>
  have htorsion_subset: "top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG \<subseteq> {?eAG, ?\<beta>G}"
  proof (rule subsetI)
    fix h assume hh_tors: "h \<in> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG"
    hence hh: "h \<in> ?AbelG" unfolding top1_torsion_subgroup_on_def by (by100 blast)
    from hh_tors obtain n_h where hn_pos: "n_h > 0"
        and hpow: "top1_group_pow ?mulAG ?eAG h n_h = ?eAG"
      unfolding top1_torsion_subgroup_on_def by (by100 blast)
    \<comment> \<open>Decompose h = k or h = mulAG k \<beta>G.\<close>
    from hK_decomp[rule_format, OF hh] obtain k where hk: "k \<in> ?K"
        and hkh: "\<exists>t\<in>top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG. h = ?mulAG k t"
      by (by100 blast)
    \<comment> \<open>Actually use the stronger decomposition from hdecomp (which is local to
       the hK\_decomp proof above). Re-derive it at this level.\<close>
    \<comment> \<open>Re-derive AbelG generation and generator decomposition for outer use.\<close>
    have hAbelG_gen_outer: "?AbelG = top1_subgroup_generated_on ?AbelG ?mulAG ?eAG ?invgAG
        ((\<lambda>i. \<phi>_bar (?\<iota>A i)) ` {..<m})"
    proof -
      have h\<iota>A_sub: "?\<iota>A ` {..<m} \<subseteq> ?AbelF" using h\<iota>A_in by (by100 blast)
      have hAbelF_gen: "?AbelF = top1_subgroup_generated_on ?AbelF ?mulA ?eA ?invgA (?\<iota>A ` {..<m})"
        using h\<iota>A unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
      have "?AbelG = top1_subgroup_generated_on ?AbelG ?mulAG ?eAG ?invgAG (\<phi>_bar ` (?\<iota>A ` {..<m}))"
        by (rule surj_hom_generated[OF hAbelF_grp hAbelG_grp h\<phi>_hom h\<phi>_surj h\<iota>A_sub hAbelF_gen])
      moreover have "\<phi>_bar ` (?\<iota>A ` {..<m}) = (\<lambda>i. \<phi>_bar (?\<iota>A i)) ` {..<m}"
        by (by100 auto)
      ultimately show ?thesis by (by100 simp)
    qed
    have hgen_decomp_outer: "\<forall>a \<in> (\<lambda>i. \<phi>_bar (?\<iota>A i)) ` {..<m}.
        a \<in> ?K \<or> (\<exists>k\<in>?K. a = ?mulAG k ?\<beta>G)"
    proof (intro ballI)
      fix a assume "a \<in> (\<lambda>i. \<phi>_bar (?\<iota>A i)) ` {..<m}"
      then obtain i where hi: "i < m" "a = \<phi>_bar (?\<iota>A i)" by (by100 blast)
      show "a \<in> ?K \<or> (\<exists>k\<in>?K. a = ?mulAG k ?\<beta>G)"
      proof (cases "i = 0")
        case False
        hence "\<epsilon>0 (?\<iota>A i) = 0" using h\<epsilon>0_rest hi(1) by (by100 blast)
        moreover have "?\<iota>A i \<in> ?AbelF" using h\<iota>A_in hi(1) by (by100 blast)
        ultimately have "?\<iota>A i \<in> {a \<in> ?AbelF. \<epsilon>0 a = 0}" by (by100 blast)
        hence "\<phi>_bar (?\<iota>A i) \<in> ?K" by (by100 blast)
        thus ?thesis using hi(2) by (by100 blast)
      next
        case True
        \<comment> \<open>Same tail decomposition as in hK\_decomp proof.\<close>
        from hK_decomp[rule_format, of "a"]
        have "a \<in> ?AbelG"
        proof -
          have "?\<iota>A i \<in> ?AbelF" using h\<iota>A_in hi(1) by (by100 blast)
          hence "\<phi>_bar (?\<iota>A i) \<in> ?AbelG" using h\<phi>_hom unfolding top1_group_hom_on_def by (by100 blast)
          thus ?thesis using hi(2) by (by100 simp)
        qed
        from hK_decomp[rule_format, OF this]
        obtain k t where "k \<in> ?K" "t \<in> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG" "a = ?mulAG k t"
          by (by100 blast)
        \<comment> \<open>t \<in> torsion, but we don't know t \<in> {eAG, \<beta>G} yet (that's what we're proving).
           So we need a different approach for i=0.\<close>
        \<comment> \<open>Direct approach: \<phi>\_bar(\<iota>A 0) = mulAG k \<beta>G where k = invgAG(\<phi>\_bar(tail)) \<in> K.
           This was already proved inside hK\_decomp. Let's re-derive it.\<close>
        have "?invgAG (\<phi>_bar ?tail_outer) \<in> ?K" using hinv_tail_K_outer .
        moreover have "a = ?mulAG (?invgAG (\<phi>_bar ?tail_outer)) ?\<beta>G"
          using hi(2) True h\<iota>A0_decomp by (by100 simp)
        ultimately show ?thesis by (by100 blast)
      qed
    qed
    have hgens_sub_outer: "(\<lambda>i. \<phi>_bar (?\<iota>A i)) ` {..<m} \<subseteq> ?AbelG"
      using h\<phi>_hom h\<iota>A_in unfolding top1_group_hom_on_def by (by100 blast)
    have hdecomp_outer: "\<forall>g\<in>?AbelG. \<exists>k\<in>?K. g = k \<or> g = ?mulAG k ?\<beta>G"
      using abelian_generated_decomposes_via_order2[OF hAbelG_abel hAbelG_gen_outer hK_grp_outer
          hK_sub h\<beta>G_in h\<beta>G_order2 hgens_sub_outer hgen_decomp_outer] by (by100 blast)
    from hdecomp_outer[rule_format, OF hh] obtain k' where hk': "k' \<in> ?K"
        and hk'h: "h = k' \<or> h = ?mulAG k' ?\<beta>G" by (by100 blast)
    show "h \<in> {?eAG, ?\<beta>G}"
    proof (cases "h = k'")
      case True
      \<comment> \<open>h = k' \<in> K \<inter> torsion = {eAG}.\<close>
      hence "k' \<in> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG"
        using hh_tors by (by100 simp)
      hence "k' \<in> ?K \<inter> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG"
        using hk' by (by100 blast)
      hence "k' = ?eAG" using hK_tors by (by100 blast)
      thus ?thesis using True by (by100 blast)
    next
      case False
      hence hh_eq: "h = ?mulAG k' ?\<beta>G" using hk'h by (by100 blast)
      \<comment> \<open>Need k' = eAG. k' \<in> K and k' torsion.
         k' = mulAG h (invgAG \<beta>G). pow(h, n) = eAG.
         pow(k', 2\<cdot>n) = eAG since \<beta>G has order 2.\<close>
      have hk'_in: "k' \<in> ?AbelG" using hk' hK_sub by (by100 blast)
      \<comment> \<open>Show k' is torsion: pow(k', 2*n_h) = eAG.\<close>
      \<comment> \<open>k' = mulAG h (invgAG \<beta>G). h torsion + \<beta>G torsion \<Longrightarrow> k' torsion.
         In abelian group: pow(mul a b, m*n) = eAG when pow(a,m) = eAG, pow(b,n) = eAG.\<close>
      have hk'_eq: "k' = ?mulAG h (?invgAG ?\<beta>G)"
      proof -
        \<comment> \<open>From h = mulAG k' \<beta>G: k' = mulAG h (invgAG \<beta>G) in abelian group.\<close>
        have "?mulAG h (?invgAG ?\<beta>G) = ?mulAG (?mulAG k' ?\<beta>G) (?invgAG ?\<beta>G)"
          using hh_eq by (by100 simp)
        also have "\<dots> = ?mulAG k' (?mulAG ?\<beta>G (?invgAG ?\<beta>G))"
        proof -
          have hinv_in: "?invgAG ?\<beta>G \<in> ?AbelG"
            using hAbelG_grp h\<beta>G_in unfolding top1_is_group_on_def by (by100 fast)
          have hkb: "\<forall>i<length [k', ?\<beta>G]. [k', ?\<beta>G]!i \<in> ?AbelG"
            using hk'_in h\<beta>G_in by (intro allI impI, auto simp: nth_Cons split: nat.splits)
          have hinv: "\<forall>i<length [?invgAG ?\<beta>G]. [?invgAG ?\<beta>G]!i \<in> ?AbelG"
            using hinv_in by (by100 auto)
          have hk1: "\<forall>i<length [k']. [k']!i \<in> ?AbelG"
            using hk'_in by (by100 auto)
          have hbi: "\<forall>i<length [?\<beta>G, ?invgAG ?\<beta>G]. [?\<beta>G, ?invgAG ?\<beta>G]!i \<in> ?AbelG"
            using h\<beta>G_in hinv_in by (intro allI impI, auto simp: nth_Cons split: nat.splits)
          have lhs: "foldr ?mulAG ([k', ?\<beta>G] @ [?invgAG ?\<beta>G]) ?eAG
              = ?mulAG (foldr ?mulAG [k', ?\<beta>G] ?eAG) (foldr ?mulAG [?invgAG ?\<beta>G] ?eAG)"
            using foldr_mul_append[OF hAbelG_grp hkb hinv] by (by100 blast)
          have rhs: "foldr ?mulAG ([k'] @ [?\<beta>G, ?invgAG ?\<beta>G]) ?eAG
              = ?mulAG (foldr ?mulAG [k'] ?eAG) (foldr ?mulAG [?\<beta>G, ?invgAG ?\<beta>G] ?eAG)"
            using foldr_mul_append[OF hAbelG_grp hk1 hbi] by (by100 blast)
          have hidG: "\<forall>x\<in>?AbelG. ?mulAG x ?eAG = x"
            using hAbelG_grp[unfolded top1_is_group_on_def] by (by100 fast)
          show ?thesis using lhs rhs hidG hk'_in h\<beta>G_in hinv_in by (by100 simp)
        qed
        also have "?mulAG ?\<beta>G (?invgAG ?\<beta>G) = ?eAG"
          using hAbelG_grp h\<beta>G_in unfolding top1_is_group_on_def by (by100 fast)
        also have "?mulAG k' ?eAG = k'"
          using hAbelG_grp hk'_in unfolding top1_is_group_on_def by (by100 fast)
        finally show ?thesis by (by100 simp)
      qed
      \<comment> \<open>invgAG(\<beta>G) is torsion (order 2, since \<beta>G^2 = eAG and invg(\<beta>G)^2 = invg(\<beta>G^2) = invg(eAG) = eAG).\<close>
      \<comment> \<open>invgAG(\<beta>G) = \<beta>G (since \<beta>G^2 = eAG \<Longrightarrow> \<beta>G = invgAG(\<beta>G)).\<close>
      have hinv\<beta>_eq: "?invgAG ?\<beta>G = ?\<beta>G"
      proof -
        \<comment> \<open>\<beta>G^2 = eAG, so \<beta>G = invg(\<beta>G): multiply both sides of \<beta>G^2=e by invg(\<beta>G) on right.\<close>
        have h1: "?mulAG ?\<beta>G ?\<beta>G = ?eAG" using h\<beta>G_order2 .
        have hinvb_in: "?invgAG ?\<beta>G \<in> ?AbelG"
          using hAbelG_grp h\<beta>G_in unfolding top1_is_group_on_def by (by100 fast)
        have "?mulAG (?mulAG ?\<beta>G ?\<beta>G) (?invgAG ?\<beta>G)
            = ?mulAG ?eAG (?invgAG ?\<beta>G)" using h1 by (by100 simp)
        moreover have "?mulAG ?eAG (?invgAG ?\<beta>G) = ?invgAG ?\<beta>G"
          using hAbelG_grp hinvb_in unfolding top1_is_group_on_def by (by100 fast)
        moreover have "?mulAG (?mulAG ?\<beta>G ?\<beta>G) (?invgAG ?\<beta>G)
            = ?mulAG ?\<beta>G (?mulAG ?\<beta>G (?invgAG ?\<beta>G))"
        proof -
          have hkb: "\<forall>i<length [?\<beta>G, ?\<beta>G]. [?\<beta>G, ?\<beta>G]!i \<in> ?AbelG"
            using h\<beta>G_in by (intro allI impI, auto simp: nth_Cons split: nat.splits)
          have hinv: "\<forall>i<length [?invgAG ?\<beta>G]. [?invgAG ?\<beta>G]!i \<in> ?AbelG"
            using hinvb_in by (by100 auto)
          have hb1: "\<forall>i<length [?\<beta>G]. [?\<beta>G]!i \<in> ?AbelG"
            using h\<beta>G_in by (by100 auto)
          have hbi: "\<forall>i<length [?\<beta>G, ?invgAG ?\<beta>G]. [?\<beta>G, ?invgAG ?\<beta>G]!i \<in> ?AbelG"
            using h\<beta>G_in hinvb_in by (intro allI impI, auto simp: nth_Cons split: nat.splits)
          have lhs: "foldr ?mulAG ([?\<beta>G, ?\<beta>G] @ [?invgAG ?\<beta>G]) ?eAG
              = ?mulAG (foldr ?mulAG [?\<beta>G, ?\<beta>G] ?eAG) (foldr ?mulAG [?invgAG ?\<beta>G] ?eAG)"
            using foldr_mul_append[OF hAbelG_grp hkb hinv] by (by100 blast)
          have rhs: "foldr ?mulAG ([?\<beta>G] @ [?\<beta>G, ?invgAG ?\<beta>G]) ?eAG
              = ?mulAG (foldr ?mulAG [?\<beta>G] ?eAG) (foldr ?mulAG [?\<beta>G, ?invgAG ?\<beta>G] ?eAG)"
            using foldr_mul_append[OF hAbelG_grp hb1 hbi] by (by100 blast)
          have hidG: "\<forall>x\<in>?AbelG. ?mulAG x ?eAG = x"
            using hAbelG_grp[unfolded top1_is_group_on_def] by (by100 fast)
          show ?thesis using lhs rhs hidG h\<beta>G_in hinvb_in by (by100 simp)
        qed
        moreover have "?mulAG ?\<beta>G (?invgAG ?\<beta>G) = ?eAG"
          using hAbelG_grp h\<beta>G_in unfolding top1_is_group_on_def by (by100 fast)
        moreover have "?mulAG ?\<beta>G ?eAG = ?\<beta>G"
          using hAbelG_grp h\<beta>G_in unfolding top1_is_group_on_def by (by100 fast)
        ultimately show ?thesis by (by100 simp)
      qed
      have hinv\<beta>_tors: "?invgAG ?\<beta>G \<in> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG"
        using hinv\<beta>_eq h\<beta>G_torsion by (by100 simp)
      \<comment> \<open>h is torsion (order n\_h) and invg(\<beta>G) is torsion (order 2).
         Product of two torsion elements in abelian group is torsion.\<close>
      have hk'_torsion: "k' \<in> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG"
      proof -
        \<comment> \<open>k' = mulAG h \<beta>G. h torsion, \<beta>G torsion.
           In abelian group, torsion elements form a subgroup.\<close>
        have hk'_eq2: "k' = ?mulAG h ?\<beta>G" using hk'_eq hinv\<beta>_eq by (by100 simp)
        \<comment> \<open>Use abelian\_torsion\_product: product of torsion elements is torsion.\<close>
        \<comment> \<open>pow(k', 2*n\_h) = mul(pow(h,2*n\_h))(pow(\<beta>G,2*n\_h)) = mul(eAG)(eAG) = eAG.\<close>
        have hpow_k'_eq: "top1_group_pow ?mulAG ?eAG k' (n_h + n_h) =
            ?mulAG (top1_group_pow ?mulAG ?eAG h (n_h + n_h))
                   (top1_group_pow ?mulAG ?eAG ?\<beta>G (n_h + n_h))"
          using abelian_group_pow_mul[OF hAbelG_abel hh h\<beta>G_in, of "n_h + n_h"]
            hk'_eq2 by (by100 simp)
        \<comment> \<open>pow(h, 2*n\_h) = eAG (since pow(h,n\_h)=eAG, use group\_pow\_add).\<close>
        have hmul_ee: "?mulAG ?eAG ?eAG = ?eAG"
          using hAbelG_grp unfolding top1_is_group_on_def by (by100 fast)
        have hpow_h_nn: "top1_group_pow ?mulAG ?eAG h (n_h + n_h) = ?eAG"
        proof -
          have "top1_group_pow ?mulAG ?eAG h (n_h + n_h)
              = ?mulAG (top1_group_pow ?mulAG ?eAG h n_h) (top1_group_pow ?mulAG ?eAG h n_h)"
            using group_pow_add[OF hAbelG_grp hh] by (by100 blast)
          thus ?thesis using hpow hmul_ee by (by100 simp)
        qed
        \<comment> \<open>pow(\<beta>G, 2*n\_h) = eAG (since pow(\<beta>G,2)=eAG, use group\_pow\_add).\<close>
        \<comment> \<open>pow(\<beta>G, n\_h + n\_h) = eAG.\<close>
        have hpow_\<beta>_nn: "top1_group_pow ?mulAG ?eAG ?\<beta>G (n_h + n_h) = ?eAG"
        proof -
          have "top1_group_pow ?mulAG ?eAG ?\<beta>G (n_h + n_h)
              = ?mulAG (top1_group_pow ?mulAG ?eAG ?\<beta>G n_h) (top1_group_pow ?mulAG ?eAG ?\<beta>G n_h)"
            using group_pow_add[OF hAbelG_grp h\<beta>G_in] by (by100 blast)
          \<comment> \<open>pow(\<beta>G, n\_h) has order dividing 2 (since \<beta>G has order 2).
             So pow(pow(\<beta>G,n\_h), 2) = pow(\<beta>G, 2*n\_h). But simpler:
             pow(\<beta>G, n\_h)^2 = eAG because pow(\<beta>G,2)=eAG and by abelian\_group\_pow\_mul:
             pow(\<beta>G, n\_h+n\_h) = mul(pow(\<beta>G,n\_h))(pow(\<beta>G,n\_h)).\<close>
          \<comment> \<open>Use hom approach: the map x -> pow(x,n\_h) is NOT a hom, but
             pow(\<beta>G, n\_h) = pow(\<beta>G, n\_h), and its square = pow(\<beta>G, 2*n\_h).
             pow(\<beta>G, 2*n\_h) = pow(pow(\<beta>G,2), n\_h) = pow(eAG, n\_h) = eAG.
             But formalizing pow(pow(x,m),n) = pow(x,m*n) needs a group\_pow\_mul lemma.\<close>
          \<comment> \<open>Direct approach: mul(pow(\<beta>G,n\_h), pow(\<beta>G,n\_h)) = pow(\<beta>G, n\_h+n\_h) [by group\_pow\_add].
             And pow(\<beta>G, n\_h+n\_h) = pow(\<beta>G, n\_h) \<cdot> pow(\<beta>G, n\_h) is what we have.
             We need this = eAG.
             Use abelian\_group\_pow\_mul on \<beta>G^2=eAG:
             pow(\<beta>G, n\_h+n\_h) = pow(mul(\<beta>G)(\<beta>G), n\_h) [if we had pow\_mul\_comm].
             Actually no, abelian\_group\_pow\_mul gives pow(mul a b, n) = mul(pow(a,n))(pow(b,n)).
             Set a=b=\<beta>G: pow(mul \<beta>G \<beta>G, n\_h) = mul(pow(\<beta>G,n\_h))(pow(\<beta>G,n\_h)).
             But mul \<beta>G \<beta>G = eAG, so pow(eAG, n\_h) = mul(pow(\<beta>G,n\_h))(pow(\<beta>G,n\_h)).
             pow(eAG, n\_h) = eAG (pow of identity is identity).\<close>
          have hpow_e: "top1_group_pow ?mulAG ?eAG ?eAG n_h = ?eAG"
          proof (induct n_h)
            case 0 thus ?case by (by100 simp)
          next
            case (Suc n)
            have "top1_group_pow ?mulAG ?eAG ?eAG (Suc n) = ?mulAG ?eAG (top1_group_pow ?mulAG ?eAG ?eAG n)"
              by (by100 simp)
            also have "\<dots> = ?mulAG ?eAG ?eAG" using Suc by (by100 simp)
            also have "\<dots> = ?eAG" using hmul_ee .
            finally show ?case .
          qed
          from abelian_group_pow_mul[OF hAbelG_abel h\<beta>G_in h\<beta>G_in, of n_h]
          have "top1_group_pow ?mulAG ?eAG (?mulAG ?\<beta>G ?\<beta>G) n_h
              = ?mulAG (top1_group_pow ?mulAG ?eAG ?\<beta>G n_h) (top1_group_pow ?mulAG ?eAG ?\<beta>G n_h)"
            by (by100 blast)
          hence "top1_group_pow ?mulAG ?eAG ?eAG n_h
              = ?mulAG (top1_group_pow ?mulAG ?eAG ?\<beta>G n_h) (top1_group_pow ?mulAG ?eAG ?\<beta>G n_h)"
            using h\<beta>G_order2 by (by100 simp)
          hence "?eAG = ?mulAG (top1_group_pow ?mulAG ?eAG ?\<beta>G n_h) (top1_group_pow ?mulAG ?eAG ?\<beta>G n_h)"
            using hpow_e by (by100 simp)
          thus ?thesis using group_pow_add[OF hAbelG_grp h\<beta>G_in, of n_h n_h] by (by100 simp)
        qed
        have "top1_group_pow ?mulAG ?eAG k' (n_h + n_h) = ?mulAG ?eAG ?eAG"
          using hpow_k'_eq hpow_h_nn hpow_\<beta>_nn by (by100 simp)
        also have "\<dots> = ?eAG" using hmul_ee .
        finally have "top1_group_pow ?mulAG ?eAG k' (n_h + n_h) = ?eAG" .
        moreover have "n_h + n_h > 0" using hn_pos by (by100 simp)
        ultimately show ?thesis using hk'_in unfolding top1_torsion_subgroup_on_def by (by100 blast)
      qed
      hence "k' \<in> ?K \<inter> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG"
        using hk' by (by100 blast)
      hence "k' = ?eAG" using hK_tors by (by100 blast)
      hence "h = ?mulAG ?eAG ?\<beta>G" using hh_eq by (by100 simp)
      also have "?mulAG ?eAG ?\<beta>G = ?\<beta>G"
        using hAbelG_grp h\<beta>G_in unfolding top1_is_group_on_def by (by100 fast)
      finally show ?thesis by (by100 blast)
    qed
  qed


  have hAbelG_torsion_card: "card (top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG) = 2"
  proof -
    have "top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG = {?eAG, ?\<beta>G}"
      using htorsion_subset heAG_torsion h\<beta>G_torsion by (by100 blast)
    moreover have "?eAG \<noteq> ?\<beta>G" using h\<beta>G_ne by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed

  \<comment> \<open>Step 15: Transfer to \<pi>_1. Since G_0 \<cong> \<pi>_1, Abel(G_0) is also
     an abelianization of \<pi>_1 (with the same structure).\<close>

  have h\<pi>1_grp: "top1_is_group_on ?\<pi>G ?\<pi>mul ?\<pi>e ?\<pi>inv"
  proof -
    have "is_topology_on X TX"
      using assms(1) unfolding top1_is_m_fold_projective_on_def
        top1_is_dunce_cap_on_def top1_quotient_of_scheme_on_def
        is_topology_on_strict_def by (by5000 blast)
    thus ?thesis using assms(2)
      by (rule top1_fundamental_group_is_group)
  qed

  \<comment> \<open>Transfer abelianization from G_0 to \<pi>_1:
     compose the abelianization map with the inverse of the iso.\<close>
  from hiso obtain f_iso where
    hf_iso: "top1_group_iso_on G0 mul0 ?\<pi>G ?\<pi>mul f_iso"
    unfolding top1_groups_isomorphic_on_def by (by100 blast)

  have hf_bij: "bij_betw f_iso G0 ?\<pi>G"
    using hf_iso unfolding top1_group_iso_on_def by (by100 blast)

  let ?g_iso = "inv_into G0 f_iso"

  have hg_hom: "top1_group_hom_on ?\<pi>G ?\<pi>mul G0 mul0 ?g_iso"
    using bij_hom_inv_is_hom[OF hG0 h\<pi>1_grp hf_bij] hf_iso
    unfolding top1_group_iso_on_def by (by100 blast)

  \<comment> \<open>Define the abelianization map for \<pi>_1.\<close>
  let ?\<phi>' = "?pG \<circ> ?g_iso"

  \<comment> \<open>Abelianization transfer: compose with inverse iso.\<close>
  have h\<phi>'_hom: "top1_group_hom_on ?\<pi>G ?\<pi>mul ?AbelG ?mulAG ?\<phi>'"
    using group_hom_comp[OF hg_hom hpG_hom] by (by100 simp)

  have hg_surj: "?g_iso ` ?\<pi>G = G0"
  proof -
    have "bij_betw ?g_iso ?\<pi>G G0"
      using bij_betw_inv_into[OF hf_bij] by (by100 simp)
    thus ?thesis unfolding bij_betw_def by (by100 blast)
  qed

  have h\<phi>'_surj: "?\<phi>' ` ?\<pi>G = ?AbelG"
  proof -
    have "?\<phi>' ` ?\<pi>G = ?pG ` (?g_iso ` ?\<pi>G)" by (by100 auto)
    also have "\<dots> = ?pG ` G0" using hg_surj by (by100 simp)
    also have "\<dots> = ?AbelG" using hpG_surj by (by100 simp)
    finally show ?thesis .
  qed

  \<comment> \<open>ker(\<phi>') = [\<pi>_1, \<pi>_1]: g\_iso maps [G_0,G_0] to [\<pi>_1,\<pi>_1] via the iso.\<close>
  have hf_iso_hom: "top1_group_hom_on G0 mul0 ?\<pi>G ?\<pi>mul f_iso"
    using hf_iso unfolding top1_group_iso_on_def by (by100 blast)
  have hf_iso_surj: "f_iso ` G0 = ?\<pi>G"
    using hf_bij unfolding bij_betw_def by (by100 blast)
  have hf_image_comm: "f_iso ` ?CG = top1_commutator_subgroup_on ?\<pi>G ?\<pi>mul ?\<pi>e ?\<pi>inv"
    using surj_hom_image_commutator[OF hG0 h\<pi>1_grp hf_iso_hom hf_iso_surj] by (by100 simp)

  have hpG_ker: "top1_group_kernel_on G0 ?eAG ?pG = ?CG"
    using quotient_projection_properties(3)[OF hG0 hCG_normal] by (by100 simp)

  have h\<phi>'_ker: "top1_group_kernel_on ?\<pi>G ?eAG ?\<phi>'
      = top1_commutator_subgroup_on ?\<pi>G ?\<pi>mul ?\<pi>e ?\<pi>inv"
  proof (rule set_eqI, rule iffI)
    fix x assume hx: "x \<in> top1_group_kernel_on ?\<pi>G ?eAG ?\<phi>'"
    have "x \<in> ?\<pi>G" using hx unfolding top1_group_kernel_on_def by (by100 blast)
    have "?pG (?g_iso x) = ?eAG" using hx unfolding top1_group_kernel_on_def by (by100 simp)
    have "?g_iso x \<in> G0" using hg_hom \<open>x \<in> ?\<pi>G\<close>
      unfolding top1_group_hom_on_def by (by100 blast)
    hence "?g_iso x \<in> top1_group_kernel_on G0 ?eAG ?pG"
      using \<open>?pG (?g_iso x) = ?eAG\<close> unfolding top1_group_kernel_on_def by (by100 blast)
    hence "?g_iso x \<in> ?CG" using hpG_ker by (by100 simp)
    hence "f_iso (?g_iso x) \<in> f_iso ` ?CG" by (by100 blast)
    moreover have "f_iso (?g_iso x) = x"
    proof -
      have "x \<in> f_iso ` G0" using \<open>x \<in> ?\<pi>G\<close> hf_iso_surj by (by100 simp)
      thus ?thesis by (rule f_inv_into_f)
    qed
    ultimately show "x \<in> top1_commutator_subgroup_on ?\<pi>G ?\<pi>mul ?\<pi>e ?\<pi>inv"
      using hf_image_comm by (by100 simp)
  next
    fix x assume hx: "x \<in> top1_commutator_subgroup_on ?\<pi>G ?\<pi>mul ?\<pi>e ?\<pi>inv"
    have "x \<in> ?\<pi>G" using hx commutator_subgroup_is_normal[OF h\<pi>1_grp]
      unfolding top1_normal_subgroup_on_def by (by100 blast)
    have "?g_iso x \<in> ?g_iso ` (top1_commutator_subgroup_on ?\<pi>G ?\<pi>mul ?\<pi>e ?\<pi>inv)"
      using hx by (by100 blast)
    moreover have "?g_iso ` (top1_commutator_subgroup_on ?\<pi>G ?\<pi>mul ?\<pi>e ?\<pi>inv) \<subseteq> ?CG"
      using hom_image_commutator_sub[OF h\<pi>1_grp hG0 hg_hom] by (by100 simp)
    ultimately have "?g_iso x \<in> ?CG" by (by100 blast)
    hence "?g_iso x \<in> top1_group_kernel_on G0 ?eAG ?pG" using hpG_ker by (by100 simp)
    hence "?pG (?g_iso x) = ?eAG" unfolding top1_group_kernel_on_def by (by100 blast)
    thus "x \<in> top1_group_kernel_on ?\<pi>G ?eAG ?\<phi>'"
      using \<open>x \<in> ?\<pi>G\<close> unfolding top1_group_kernel_on_def by (by100 simp)
  qed

  have hCG_sub: "?CG \<subseteq> G0"
    using hCG_normal unfolding top1_normal_subgroup_on_def by (by100 blast)
  have hCG_grp: "top1_is_group_on ?CG mul0 e0 invg0"
    using hCG_normal unfolding top1_normal_subgroup_on_def by (by100 blast)
  have hcoset_e: "?eAG = ?CG"
    using coset_e_is_N[OF hG0 hCG_sub hCG_grp] by (by100 simp)

  have habel_pi1: "top1_is_abelianization_of ?AbelG ?mulAG ?eAG ?invgAG
      ?\<pi>G ?\<pi>mul ?\<pi>e ?\<pi>inv ?\<phi>'"
    unfolding top1_is_abelianization_of_def
    using hAbelG_abel h\<pi>1_grp h\<phi>'_hom h\<phi>'_surj h\<phi>'_ker hcoset_e by (by100 blast)

  \<comment> \<open>Step 16: Assemble final result.\<close>
  \<comment> \<open>Assemble: provide explicit witnesses for the existentials.\<close>
  have hfinal: "top1_is_abelianization_of ?AbelG ?mulAG ?eAG ?invgAG
      ?\<pi>G ?\<pi>mul ?\<pi>e ?\<pi>inv ?\<phi>'
    \<and> card (top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG) = 2
    \<and> (\<exists>(K :: (real \<Rightarrow> 'a) set set set set) (\<iota>_S :: nat \<Rightarrow> (real \<Rightarrow> 'a) set set set).
         K \<subseteq> ?AbelG
       \<and> top1_is_free_abelian_group_full_on K ?mulAG ?eAG ?invgAG \<iota>_S {..<m-1}
       \<and> K \<inter> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG = {?eAG}
       \<and> (\<forall>h\<in>?AbelG. \<exists>k\<in>K. \<exists>t\<in>top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG.
             h = ?mulAG k t))"
    using habel_pi1 hAbelG_torsion_card hAbelG_free_part by (by100 blast)
  show ?thesis
  proof (rule exI, rule exI, rule exI, rule exI, rule exI)
    show "top1_is_abelianization_of ?AbelG ?mulAG ?eAG ?invgAG ?\<pi>G ?\<pi>mul ?\<pi>e ?\<pi>inv ?\<phi>'
      \<and> card (top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG) = 2
      \<and> (\<exists>(K :: (real \<Rightarrow> 'a) set set set set) (\<iota>_S :: nat \<Rightarrow> (real \<Rightarrow> 'a) set set set).
           K \<subseteq> ?AbelG
         \<and> top1_is_free_abelian_group_full_on K ?mulAG ?eAG ?invgAG \<iota>_S {..<m-1}
         \<and> K \<inter> top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG = {?eAG}
         \<and> (\<forall>h\<in>?AbelG. \<exists>k\<in>K. \<exists>t\<in>top1_torsion_subgroup_on ?AbelG ?mulAG ?eAG.
               h = ?mulAG k t))"
      using hfinal by (by100 simp)
  qed
qed

end
