theory AlgTop
  imports "AlgTop0.AlgTop0"
begin

text \<open>Bridge: the order topology on R equals top1_open_sets (= {U. open U}).
  Hence top1_closed_interval_topology 0 1 = I_top.\<close>
lemma open_ray_gt_is_open: "open (open_ray_gt (a::real))"
proof -
  have "open_ray_gt a = {x. a < x}" unfolding open_ray_gt_def by (by100 blast)
  moreover have "open {x::real. a < x}" using open_greaterThan unfolding greaterThan_def by (by100 blast)
  ultimately show ?thesis by (by100 simp)
qed

lemma open_ray_lt_is_open: "open (open_ray_lt (a::real))"
proof -
  have "open_ray_lt a = {x. x < a}" unfolding open_ray_lt_def by (by100 blast)
  moreover have "open {x::real. x < a}" using open_lessThan unfolding lessThan_def by (by100 blast)
  ultimately show ?thesis by (by100 simp)
qed

lemma open_interval_is_open: "open (open_interval (a::real) c)"
proof -
  have "open_interval a c = open_ray_gt a \<inter> open_ray_lt c"
    unfolding open_interval_def open_ray_gt_def open_ray_lt_def by (by100 blast)
  thus ?thesis using open_Int[OF open_ray_gt_is_open open_ray_lt_is_open] by (by100 simp)
qed

lemma top1_open_sets_sub_order_topology_real:
  "(top1_open_sets :: real set set) \<subseteq> order_topology_on_UNIV"
proof
  fix U :: "real set"
  \<comment> \<open>Direction 2: open \<Rightarrow> in order_topology.
     open = generate_topology(rays). Rays in basis. order_topology is a topology.\<close>
  assume "U \<in> top1_open_sets"
  hence "open U" unfolding top1_open_sets_def by (by100 blast)
  hence hgen: "generate_topology (range (\<lambda>a::real. {..< a}) \<union> range (\<lambda>a. {a <..})) U"
    unfolding open_generated_order .
  \<comment> \<open>Show by induction on generate_topology that U \<in> order_topology_on_UNIV.\<close>
  have hOT: "is_topology_on (UNIV::real set) (order_topology_on_UNIV::real set set)"
    unfolding order_topology_on_UNIV_def
    by (rule topology_generated_by_basis_is_topology_on[OF basis_order_topology_is_basis_on_UNIV])
  \<comment> \<open>Open rays are in basis, hence in order_topology.\<close>
  have hlt_in: "\<And>a::real. {..<a} \<in> order_topology_on_UNIV"
  proof -
    fix a :: real
    have "open_ray_lt a \<in> basis_order_topology"
      unfolding basis_order_topology_def by (by100 blast)
    hence "open_ray_lt a \<in> order_topology_on_UNIV"
      unfolding order_topology_on_UNIV_def topology_generated_by_basis_def
    proof (intro CollectI conjI ballI)
      show "open_ray_lt a \<subseteq> UNIV" by (by100 simp)
      fix x assume "x \<in> open_ray_lt a"
      show "\<exists>b\<in>basis_order_topology. x \<in> b \<and> b \<subseteq> open_ray_lt a"
        using \<open>x \<in> open_ray_lt a\<close> \<open>open_ray_lt a \<in> basis_order_topology\<close> by (by100 blast)
    qed
    thus "{..<a} \<in> order_topology_on_UNIV"
      unfolding open_ray_lt_def lessThan_def by (by100 simp)
  qed
  have hgt_in: "\<And>a::real. {a<..} \<in> order_topology_on_UNIV"
  proof -
    fix a :: real
    have hgt_basis: "open_ray_gt a \<in> basis_order_topology"
      unfolding basis_order_topology_def by (by100 blast)
    hence "open_ray_gt a \<in> order_topology_on_UNIV"
      unfolding order_topology_on_UNIV_def topology_generated_by_basis_def
    proof (intro CollectI conjI ballI)
      show "open_ray_gt a \<subseteq> UNIV" by (by100 simp)
      fix x assume "x \<in> open_ray_gt a"
      show "\<exists>b\<in>basis_order_topology. x \<in> b \<and> b \<subseteq> open_ray_gt a"
        using \<open>x \<in> open_ray_gt a\<close> hgt_basis by (by100 blast)
    qed
    thus "{a<..} \<in> order_topology_on_UNIV"
      unfolding open_ray_gt_def greaterThan_def by (by100 simp)
  qed
  \<comment> \<open>Induction on generate_topology: UNIV \<in> T, \<inter> closed, \<union> closed, basis \<in> T.\<close>
  from hgen show "U \<in> order_topology_on_UNIV"
  proof (induction rule: generate_topology.induct)
    case UNIV
    show ?case using hOT unfolding is_topology_on_def by (by100 blast)
  next
    case (Int a b)
    have "{a} \<subseteq> order_topology_on_UNIV" "{b} \<subseteq> order_topology_on_UNIV"
      using Int.IH by (by100 blast)+
    hence "{a} \<union> {b} \<subseteq> order_topology_on_UNIV" by (by100 blast)
    hence "finite ({a,b}) \<and> {a,b} \<noteq> {} \<and> {a,b} \<subseteq> order_topology_on_UNIV" by (by100 simp)
    hence "\<Inter>{a,b} \<in> order_topology_on_UNIV"
      using hOT unfolding is_topology_on_def by (by100 blast)
    thus ?case by (by100 simp)
  next
    case (UN K)
    have "K \<subseteq> order_topology_on_UNIV" using UN.IH by (by100 blast)
    hence "\<Union>K \<in> order_topology_on_UNIV"
      using hOT unfolding is_topology_on_def by (by100 blast)
    thus ?case .
  next
    case (Basis s)
    hence "s \<in> range (\<lambda>a::real. {..< a}) \<union> range (\<lambda>a. {a <..})" .
    hence "(\<exists>a. s = {..<a}) \<or> (\<exists>a. s = {a<..})" by (by100 blast)
    thus ?case using hlt_in hgt_in by (by100 blast)
  qed
qed

lemma I_top_sub_closed_interval_top:
  "I_top \<subseteq> top1_closed_interval_topology 0 1"
proof
  fix V assume "V \<in> I_top"
  hence "V \<in> subspace_topology UNIV top1_open_sets I_set"
    unfolding top1_unit_interval_topology_def .
  then obtain W where hW: "W \<in> top1_open_sets" and hV: "V = I_set \<inter> W"
    unfolding subspace_topology_def by (by100 blast)
  have "W \<in> order_topology_on_UNIV"
    using top1_open_sets_sub_order_topology_real hW by (by100 blast)
  have hCI_eq: "top1_closed_interval 0 1 = I_set"
    unfolding top1_closed_interval_def top1_unit_interval_def by (by100 auto)
  have "V = top1_closed_interval 0 1 \<inter> W" unfolding hCI_eq hV ..
  moreover have "W \<in> order_topology_on_UNIV" by (rule \<open>W \<in> order_topology_on_UNIV\<close>)
  ultimately show "V \<in> top1_closed_interval_topology 0 1"
    unfolding top1_closed_interval_topology_def subspace_topology_def by (by100 blast)
qed

text \<open>Continuity transfer: if \<phi> continuous X \<rightarrow> [0,1] (closed_interval_topology),
  then \<phi> continuous X \<rightarrow> I_set (I_top), since I_top \<subseteq> closed_interval_topology.\<close>
lemma continuous_closed_interval_imp_I_top:
  assumes "top1_continuous_map_on X TX (top1_closed_interval 0 1)
               (top1_closed_interval_topology 0 1) f"
  shows "top1_continuous_map_on X TX I_set I_top f"
proof -
  have hCI_eq: "top1_closed_interval 0 1 = I_set"
    unfolding top1_closed_interval_def top1_unit_interval_def by (by100 auto)
  show ?thesis unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix x assume "x \<in> X"
    have "f x \<in> top1_closed_interval 0 1"
      using assms \<open>x \<in> X\<close> unfolding top1_continuous_map_on_def by (by100 blast)
    thus "f x \<in> I_set" unfolding hCI_eq .
  next
    fix V assume "V \<in> I_top"
    hence "V \<in> top1_closed_interval_topology 0 1" using I_top_sub_closed_interval_top by (by100 blast)
    thus "{x \<in> X. f x \<in> V} \<in> TX"
      using assms unfolding top1_continuous_map_on_def by (by100 blast)
  qed
qed

text \<open>Tietze extension to R (unbounded version). Uses Theorem_35_1 (bounded version)
  plus homeomorphism R \<cong> (-1,1) and Urysohn to avoid boundary.\<close>
lemma Theorem_35_1_R:
  assumes hX: "top1_normal_on X TX" and hA: "closedin_on X TX A"
  assumes hf: "top1_continuous_map_on A (subspace_topology X TX A)
      (UNIV::real set) order_topology_on_UNIV f"
  shows "\<exists>F. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV F
           \<and> (\<forall>x\<in>A. F x = f x)"
proof -
  have hTopX: "is_topology_on X TX"
    using hX unfolding top1_normal_on_def top1_T1_on_def by (by100 blast)
  have hAX: "A \<subseteq> X" by (rule closedin_sub[OF hA])
  \<comment> \<open>Step 1: h: R \<rightarrow> (-1,1), h(x) = x / (1+|x|). Continuous bijection.\<close>
  define h :: "real \<Rightarrow> real" where "h = (\<lambda>x. x / (1 + \<bar>x\<bar>))"
  define h_inv :: "real \<Rightarrow> real" where "h_inv = (\<lambda>y. y / (1 - \<bar>y\<bar>))"
  have hh_range: "\<And>x::real. h x \<in> {y. -1 < y \<and> y < 1}"
  proof -
    fix x :: real
    have hpos: "1 + \<bar>x\<bar> > 0" by (by100 linarith)
    have hne: "1 + \<bar>x\<bar> \<noteq> 0" using hpos by (by100 linarith)
    have "- 1 < h x"
    proof -
      have "-1 - \<bar>x\<bar> < x" by (by100 linarith)
      hence "(-1 - \<bar>x\<bar>) / (1 + \<bar>x\<bar>) < x / (1 + \<bar>x\<bar>)"
        using hpos by (rule divide_strict_right_mono)
      moreover have "(-1 - \<bar>x\<bar>) / (1 + \<bar>x\<bar>) = -1"
      proof -
        have h_eq: "(-1 - \<bar>x\<bar>) = -(1 + \<bar>x\<bar>)" by (by100 linarith)
        have "(1 + \<bar>x\<bar>) / (1 + \<bar>x\<bar>) = (1::real)" using hne by (by100 simp)
        hence "-(1 + \<bar>x\<bar>) / (1 + \<bar>x\<bar>) = -(1::real)" by (by100 linarith)
        thus ?thesis unfolding h_eq[symmetric] .
      qed
      ultimately show ?thesis unfolding h_def by (by100 linarith)
    qed
    moreover have "h x < 1"
    proof -
      have "x < 1 + \<bar>x\<bar>" by (by100 linarith)
      hence "x / (1 + \<bar>x\<bar>) < (1 + \<bar>x\<bar>) / (1 + \<bar>x\<bar>)"
        using hpos by (rule divide_strict_right_mono)
      moreover have "(1 + \<bar>x\<bar>) / (1 + \<bar>x\<bar>) = 1" using hne by (by100 simp)
      ultimately show ?thesis unfolding h_def by (by100 linarith)
    qed
    ultimately show "h x \<in> {y. -1 < y \<and> y < 1}" by (by100 simp)
  qed
  have hh_inv: "\<And>y::real. -1 < y \<Longrightarrow> y < 1 \<Longrightarrow> h (h_inv y) = y"
  proof -
    fix y :: real assume hy1: "-1 < y" and hy2: "y < 1"
    have habs: "\<bar>y\<bar> < 1" using hy1 hy2 by (by100 linarith)
    have hpos: "1 - \<bar>y\<bar> > 0" using habs by (by100 linarith)
    have hne: "1 - \<bar>y\<bar> \<noteq> 0" using hpos by (by100 linarith)
    have h_hinv: "h_inv y = y / (1 - \<bar>y\<bar>)" unfolding h_inv_def by (by100 simp)
    have h_abs_hinv: "\<bar>h_inv y\<bar> = \<bar>y\<bar> / (1 - \<bar>y\<bar>)"
    proof -
      have "\<bar>y / (1 - \<bar>y\<bar>)\<bar> = \<bar>y\<bar> / \<bar>1 - \<bar>y\<bar>\<bar>" by (rule abs_divide)
      moreover have "\<bar>1 - \<bar>y\<bar>\<bar> = 1 - \<bar>y\<bar>" using hpos by (by100 linarith)
      ultimately show ?thesis unfolding h_inv_def by simp
    qed
    \<comment> \<open>Key: (1 + |h_inv y|) * (1 - |y|) = 1.\<close>
    have key: "(1 + \<bar>h_inv y\<bar>) * (1 - \<bar>y\<bar>) = 1"
    proof -
      have hd: "\<bar>y\<bar> / (1 - \<bar>y\<bar>) * (1 - \<bar>y\<bar>) = \<bar>y\<bar>"
        using hne by simp
      have "(1 + \<bar>y\<bar> / (1 - \<bar>y\<bar>)) * (1 - \<bar>y\<bar>)
          = 1 * (1 - \<bar>y\<bar>) + \<bar>y\<bar> / (1 - \<bar>y\<bar>) * (1 - \<bar>y\<bar>)"
        using distrib_right[of 1 "\<bar>y\<bar> / (1 - \<bar>y\<bar>)" "1 - \<bar>y\<bar>"] by simp
      also have "\<dots> = (1 - \<bar>y\<bar>) + \<bar>y\<bar>" using hd by (by100 simp)
      also have "\<dots> = 1" by (by100 simp)
      finally show ?thesis unfolding h_abs_hinv .
    qed
    have hne2: "1 + \<bar>h_inv y\<bar> \<noteq> 0"
    proof -
      from key have "(1 + \<bar>h_inv y\<bar>) * (1 - \<bar>y\<bar>) \<noteq> 0" by (by100 simp)
      thus ?thesis by (by100 simp)
    qed
    show "h (h_inv y) = y"
    proof -
      have "h (h_inv y) = h_inv y / (1 + \<bar>h_inv y\<bar>)" unfolding h_def by (by100 simp)
      also have "\<dots> = (y / (1 - \<bar>y\<bar>)) / (1 + \<bar>h_inv y\<bar>)" unfolding h_hinv by (by100 simp)
      also have "\<dots> = y / ((1 - \<bar>y\<bar>) * (1 + \<bar>h_inv y\<bar>))"
        using hne hne2 by (by100 simp)
      also have "(1 - \<bar>y\<bar>) * (1 + \<bar>h_inv y\<bar>) = (1 + \<bar>h_inv y\<bar>) * (1 - \<bar>y\<bar>)"
        by (rule mult.commute)
      also have "\<dots> = 1" by (rule key)
      finally show ?thesis by (by100 simp)
    qed
  qed
  have hh_inv2: "\<And>x::real. h_inv (h x) = x"
  proof -
    fix x :: real
    have hpos: "1 + \<bar>x\<bar> > 0" by (by100 linarith)
    have hne: "1 + \<bar>x\<bar> \<noteq> 0" using hpos by (by100 linarith)
    \<comment> \<open>h(x) = x/(1+|x|), |h(x)| = |x|/(1+|x|), 1-|h(x)| = 1/(1+|x|).\<close>
    have h_hx: "h x = x / (1 + \<bar>x\<bar>)" unfolding h_def by (by100 simp)
    have h_abs_hx: "\<bar>h x\<bar> = \<bar>x\<bar> / (1 + \<bar>x\<bar>)"
    proof -
      have "\<bar>x / (1 + \<bar>x\<bar>)\<bar> = \<bar>x\<bar> / \<bar>1 + \<bar>x\<bar>\<bar>" by (rule abs_divide)
      moreover have "\<bar>1 + \<bar>x\<bar>\<bar> = 1 + \<bar>x\<bar>" using hpos by (by100 linarith)
      ultimately show ?thesis unfolding h_def by (by100 simp)
    qed
    \<comment> \<open>(1 - |h x|) * (1 + |x|) = 1, so h_inv(h x) = h x / (1-|h x|) = x.\<close>
    have key: "(1 - \<bar>h x\<bar>) * (1 + \<bar>x\<bar>) = 1"
    proof -
      have "(1 - \<bar>x\<bar> / (1 + \<bar>x\<bar>)) * (1 + \<bar>x\<bar>) = 1 * (1 + \<bar>x\<bar>) - \<bar>x\<bar> / (1 + \<bar>x\<bar>) * (1 + \<bar>x\<bar>)"
        using left_diff_distrib[of 1 "\<bar>x\<bar> / (1 + \<bar>x\<bar>)" "1 + \<bar>x\<bar>"] by (by100 simp)
      also have "\<bar>x\<bar> / (1 + \<bar>x\<bar>) * (1 + \<bar>x\<bar>) = \<bar>x\<bar>"
        using hne by (by100 simp)
      finally have "(1 - \<bar>x\<bar> / (1 + \<bar>x\<bar>)) * (1 + \<bar>x\<bar>) = (1 + \<bar>x\<bar>) - \<bar>x\<bar>"
        by (by100 simp)
      also have "\<dots> = 1" by (by100 simp)
      finally show ?thesis unfolding h_abs_hx .
    qed
    have h_1_minus_ne: "1 - \<bar>h x\<bar> \<noteq> 0"
    proof -
      from key have "(1 - \<bar>h x\<bar>) * (1 + \<bar>x\<bar>) \<noteq> 0" by (by100 simp)
      thus ?thesis by (by100 simp)
    qed
    show "h_inv (h x) = x"
    proof -
      have "h_inv (h x) = h x / (1 - \<bar>h x\<bar>)" unfolding h_inv_def by (by100 simp)
      also have "\<dots> = (x / (1 + \<bar>x\<bar>)) / (1 - \<bar>h x\<bar>)" unfolding h_hx by (by100 simp)
      also have "\<dots> = x / ((1 + \<bar>x\<bar>) * (1 - \<bar>h x\<bar>))"
        using hne h_1_minus_ne by (by100 simp)
      also have "(1 + \<bar>x\<bar>) * (1 - \<bar>h x\<bar>) = (1 - \<bar>h x\<bar>) * (1 + \<bar>x\<bar>)"
        by (rule mult.commute)
      also have "\<dots> = 1" by (rule key)
      finally show ?thesis by (by100 simp)
    qed
  qed
  \<comment> \<open>Step 2: h \<circ> f: A \<rightarrow> (-1,1) \<subset> [-1,1]. Compose, extend via Theorem_35_1.\<close>
  have hhf_range: "\<forall>a\<in>A. h (f a) \<in> top1_closed_interval (-1) 1"
  proof (intro ballI)
    fix a assume "a \<in> A"
    have "h (f a) \<in> {y. -1 < y \<and> y < 1}" by (rule hh_range)
    thus "h (f a) \<in> top1_closed_interval (-1) 1"
      unfolding top1_closed_interval_def by (by100 simp)
  qed
  have hhf_cont: "top1_continuous_map_on A (subspace_topology X TX A)
      (top1_closed_interval (-1) 1) (top1_closed_interval_topology (-1) 1) (\<lambda>x. h (f x))"
  proof -
    \<comment> \<open>h continuous on R in standard (HOL) sense.\<close>
    have hh_cont_on: "continuous_on (UNIV::real set) h"
    proof -
      have "\<And>x::real. 1 + \<bar>x\<bar> \<noteq> 0" by (by100 linarith)
      thus ?thesis unfolding h_def by (intro continuous_intros) (by100 blast)
    qed
    \<comment> \<open>Bridge to order topology = top1_open_sets.\<close>
    have hh_top1: "top1_continuous_map_on (UNIV::real set) (order_topology_on_UNIV::real set set)
        (UNIV::real set) (order_topology_on_UNIV::real set set) h"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x :: real show "h x \<in> (UNIV::real set)" by (by100 simp)
    next
      fix V :: "real set" assume hV: "V \<in> (order_topology_on_UNIV::real set set)"
      hence "open V" using order_topology_on_UNIV_eq_HOL_open by (by100 blast)
      hence "open (h -` V)" using hh_cont_on by (rule open_vimage)
      hence "h -` V \<in> (order_topology_on_UNIV::real set set)"
        using order_topology_on_UNIV_eq_HOL_open by (by100 blast)
      moreover have "{x \<in> (UNIV::real set). h x \<in> V} = h -` V" by (by100 blast)
      ultimately show "{x \<in> (UNIV::real set). h x \<in> V} \<in> (order_topology_on_UNIV::real set set)"
        by (by100 simp)
    qed
    \<comment> \<open>Compose f: A \<rightarrow> R with h: R \<rightarrow> R.\<close>
    have hTA: "is_topology_on A (subspace_topology X TX A)"
      by (rule subspace_topology_is_topology_on[OF hTopX hAX])
    have hTR: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
      by (rule order_topology_on_UNIV_is_topology_on)
    have "top1_continuous_map_on A (subspace_topology X TX A)
        (UNIV::real set) order_topology_on_UNIV (h \<circ> f)"
      by (rule top1_continuous_map_on_comp[OF hf hh_top1])
    hence hhf_R: "top1_continuous_map_on A (subspace_topology X TX A)
        (UNIV::real set) order_topology_on_UNIV (\<lambda>x. h (f x))"
      unfolding comp_def .
    \<comment> \<open>Restrict codomain to [-1,1].\<close>
    let ?I = "top1_closed_interval (-1::real) 1"
    let ?TI = "top1_closed_interval_topology (-1::real) 1"
    have hI_sub: "?I \<subseteq> (UNIV::real set)" by (by100 simp)
    have himg: "(\<lambda>x. h (f x)) ` A \<subseteq> ?I" using hhf_range by (by100 blast)
    have hTI_sub: "?TI = subspace_topology (UNIV::real set) order_topology_on_UNIV ?I"
      unfolding top1_closed_interval_topology_def by (by100 blast)
    show ?thesis unfolding hTI_sub
      by (rule top1_continuous_map_on_codomain_shrink[OF hhf_R himg hI_sub])
  qed
  obtain g where hg: "top1_continuous_map_on X TX (top1_closed_interval (-1) 1)
      (top1_closed_interval_topology (-1) 1) g"
      and hg_ext: "\<forall>x\<in>A. g x = h (f x)"
    using Theorem_35_1[OF hX hA hhf_cont] by (by100 blast)
  \<comment> \<open>Step 3: B = g\<inverse>({-1,1}) closed, disjoint from A. Urysohn separation.\<close>
  define B where "B = {x \<in> X. g x = -1 \<or> g x = 1}"
  have hB_closed: "closedin_on X TX B"
  proof -
    let ?I = "top1_closed_interval (-1::real) 1"
    let ?TI = "top1_closed_interval_topology (-1::real) 1"
    have hTopI: "is_topology_on ?I ?TI"
    proof -
      have "?I \<subseteq> (UNIV::real set)" by (by100 simp)
      thus ?thesis unfolding top1_closed_interval_topology_def
        by (rule subspace_topology_is_topology_on[OF order_topology_on_UNIV_is_topology_on])
    qed
    \<comment> \<open>{-1, 1} is closed in [-1,1].\<close>
    have hend_closed: "closedin_on ?I ?TI {-1::real, 1}"
    proof (rule closedin_intro)
      show "{-1::real, 1} \<subseteq> ?I" unfolding top1_closed_interval_def by (by100 auto)
      \<comment> \<open>[-1,1] \ {-1,1} = (-1,1) which is open in the subspace topology.\<close>
      have "?I - {-1::real, 1} = {x. -1 < x \<and> x < 1}"
        unfolding top1_closed_interval_def by (by100 auto)
      moreover have "{x::real. -1 < x \<and> x < 1} \<in> ?TI"
      proof -
        have "{x::real. -1 < x \<and> x < 1} = ?I \<inter> {x. -1 < x \<and> x < 1}"
          unfolding top1_closed_interval_def by (by100 auto)
        moreover have "{x::real. -1 < x \<and> x < 1} \<in> order_topology_on_UNIV"
          using order_topology_on_UNIV_eq_HOL_open open_interval_is_open
          unfolding open_interval_def by (by100 blast)
        moreover have "?TI = subspace_topology UNIV order_topology_on_UNIV ?I"
          unfolding top1_closed_interval_topology_def by (by100 blast)
        ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
      qed
      ultimately show "?I - {-1::real, 1} \<in> ?TI" by (by100 simp)
    qed
    \<comment> \<open>B = {x \<in> X. g x \<in> {-1,1}}: preimage of closed under continuous.\<close>
    have hB_eq: "B = {x \<in> X. g x \<in> {-1::real, 1}}" unfolding B_def by (by100 blast)
    show ?thesis unfolding hB_eq
      by (rule continuous_preimage_closedin[OF hTopX hTopI hg hend_closed])
  qed
  have hAB_disj: "A \<inter> B = {}"
  proof (rule equals0I)
    fix x assume "x \<in> A \<inter> B"
    hence hxA: "x \<in> A" and hxB: "x \<in> B" by (by100 blast)+
    have "g x = h (f x)" using hg_ext hxA by (by100 blast)
    moreover have "h (f x) \<in> {y. -1 < y \<and> y < 1}" by (rule hh_range)
    ultimately have "g x \<noteq> -1 \<and> g x \<noteq> 1" by (by100 simp)
    thus False using hxB unfolding B_def by (by100 blast)
  qed
  \<comment> \<open>Step 4: Urysohn \<phi>: X \<rightarrow> [0,1] with \<phi>|_A = 1, \<phi>|_B = 0.\<close>
  obtain \<phi> where h\<phi>: "top1_continuous_map_on X TX (top1_closed_interval 0 1)
      (top1_closed_interval_topology 0 1) \<phi>"
      and h\<phi>A: "\<forall>x\<in>A. \<phi> x = 0" and h\<phi>B: "\<forall>x\<in>B. \<phi> x = 1"
    using Theorem_33_1[OF hX hA hB_closed hAB_disj, of 0 1] by (by100 auto)
  \<comment> \<open>Step 5: Define F(x) = h_inv((1-\<phi>(x)) \<cdot> g(x)).
     On A: \<phi>=0, g=h\<circ>f, so (1-0)\<cdot>h(f(x)) = h(f(x)), F(x)=h_inv(h(f(x)))=f(x).
     On B: \<phi>=1, so (1-1)\<cdot>g(x)=0, F(x)=h_inv(0)=0. Avoids \<pm>1.
     Elsewhere: |g(x)|<1 (x\<notin>B), |(1-\<phi>(x))\<cdot>g(x)| \<le> |g(x)| < 1.\<close>
  define F where "F = (\<lambda>x. h_inv ((1 - \<phi> x) * g x))"
  have hF_ext: "\<forall>x\<in>A. F x = f x"
  proof (intro ballI)
    fix x assume hx: "x \<in> A"
    have "\<phi> x = 0" using h\<phi>A hx by (by100 blast)
    hence "F x = h_inv (g x)" unfolding F_def by (by100 simp)
    also have "\<dots> = h_inv (h (f x))" using hg_ext hx by (by100 simp)
    also have "\<dots> = f x" by (rule hh_inv2)
    finally show "F x = f x" .
  qed
  have hF_cont: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV F"
  proof -
    let ?TRI = "top1_closed_interval_topology (-1::real) 1"
    let ?I = "top1_closed_interval (-1::real) 1"
    \<comment> \<open>(1-\<phi>)\<cdot>g maps X into (-1,1): key range argument.\<close>
    have hrange: "\<forall>x\<in>X. -1 < (1 - \<phi> x) * g x \<and> (1 - \<phi> x) * g x < 1"
    proof (intro ballI conjI)
      fix x assume hx: "x \<in> X"
      have h\<phi>01: "0 \<le> \<phi> x \<and> \<phi> x \<le> 1"
        using h\<phi> hx unfolding top1_continuous_map_on_def top1_closed_interval_def by (by100 blast)
      have hg_bounds: "-1 \<le> g x \<and> g x \<le> 1"
        using hg hx unfolding top1_continuous_map_on_def top1_closed_interval_def by (by100 blast)
      \<comment> \<open>Abs value bound: |(1-\<phi>)\<cdot>g| \<le> |g| \<le> 1, strict when x \<notin> B.\<close>
      have h1\<phi>: "0 \<le> 1 - \<phi> x \<and> 1 - \<phi> x \<le> 1" using h\<phi>01 by (by100 linarith)
      have habs_bound: "\<bar>(1 - \<phi> x) * g x\<bar> \<le> \<bar>g x\<bar>"
      proof -
        have "\<bar>(1 - \<phi> x) * g x\<bar> = \<bar>1 - \<phi> x\<bar> * \<bar>g x\<bar>" by (rule abs_mult)
        moreover have "\<bar>1 - \<phi> x\<bar> = 1 - \<phi> x" using h1\<phi> by (by100 linarith)
        moreover have "(1 - \<phi> x) * \<bar>g x\<bar> \<le> 1 * \<bar>g x\<bar>"
        proof -
          have "1 - \<phi> x \<le> 1" using h1\<phi> by (by100 linarith)
          thus ?thesis using abs_ge_zero[of "g x"] by (rule mult_right_mono)
        qed
        ultimately have "\<bar>(1 - \<phi> x) * g x\<bar> \<le> 1 * \<bar>g x\<bar>" by (by100 linarith)
        thus ?thesis by (by100 simp)
      qed
      have habs_g: "\<bar>g x\<bar> \<le> 1" using hg_bounds by (by100 linarith)
      show "-1 < (1 - \<phi> x) * g x"
      proof (cases "x \<in> B")
        case True hence "\<phi> x = 1" using h\<phi>B by (by100 blast)
        thus ?thesis by (by100 simp)
      next
        case False
        hence "g x \<noteq> -1 \<and> g x \<noteq> 1" unfolding B_def using hx by (by100 blast)
        hence "\<bar>g x\<bar> < 1" using hg_bounds by (by100 linarith)
        hence "\<bar>(1 - \<phi> x) * g x\<bar> < 1" using habs_bound by (by100 linarith)
        thus ?thesis by (by100 linarith)
      qed
      show "(1 - \<phi> x) * g x < 1"
      proof (cases "x \<in> B")
        case True hence "\<phi> x = 1" using h\<phi>B by (by100 blast)
        thus ?thesis by (by100 simp)
      next
        case False
        hence "g x \<noteq> -1 \<and> g x \<noteq> 1" unfolding B_def using hx by (by100 blast)
        hence "\<bar>g x\<bar> < 1" using hg_bounds by (by100 linarith)
        hence "\<bar>(1 - \<phi> x) * g x\<bar> < 1" using habs_bound by (by100 linarith)
        thus ?thesis by (by100 linarith)
      qed
    qed
    \<comment> \<open>(1-\<phi>)\<cdot>g continuous X \<rightarrow> R, then h_inv continuous on (-1,1), compose.\<close>
    have hprod_cont: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV
        (\<lambda>x. (1 - \<phi> x) * g x)"
    proof -
      let ?TOR = "order_topology_on_UNIV :: real set set"
      have hTR: "is_topology_on (UNIV::real set) ?TOR" by (rule order_topology_on_UNIV_is_topology_on)
      have hTRR: "is_topology_on ((UNIV::real set) \<times> (UNIV::real set)) (product_topology_on ?TOR ?TOR)"
        by (rule product_topology_on_is_topology_on[OF hTR hTR])
      \<comment> \<open>Enlarge codomain of g to R.\<close>
      have hg_R: "top1_continuous_map_on X TX (UNIV::real set) ?TOR g"
      proof -
        have hg_sub: "top1_continuous_map_on X TX ?I (subspace_topology UNIV ?TOR ?I) g"
          using hg unfolding top1_closed_interval_topology_def by (by100 simp)
        have "top1_continuous_map_on X TX (UNIV::real set) (subspace_topology UNIV ?TOR UNIV) g"
          using top1_continuous_map_on_codomain_enlarge[OF hg_sub] by (by100 simp)
        thus ?thesis unfolding subspace_topology_UNIV_self .
      qed
      \<comment> \<open>Enlarge codomain of \<phi> to R, then form 1-\<phi>.\<close>
      have h\<phi>_R: "top1_continuous_map_on X TX (UNIV::real set) ?TOR \<phi>"
      proof -
        have h\<phi>_sub: "top1_continuous_map_on X TX (top1_closed_interval 0 1) (subspace_topology UNIV ?TOR (top1_closed_interval 0 1)) \<phi>"
          using h\<phi> unfolding top1_closed_interval_topology_def by (by100 simp)
        have "top1_continuous_map_on X TX (UNIV::real set) (subspace_topology UNIV ?TOR UNIV) \<phi>"
          using top1_continuous_map_on_codomain_enlarge[OF h\<phi>_sub] by (by100 simp)
        thus ?thesis unfolding subspace_topology_UNIV_self .
      qed
      \<comment> \<open>1-\<phi> continuous: compose with negation and addition.\<close>
      have hTR_eq: "(order_topology_on_UNIV :: real set set) = top1_open_sets"
      proof (rule set_eqI)
        fix U :: "real set"
        show "U \<in> order_topology_on_UNIV \<longleftrightarrow> U \<in> top1_open_sets"
          using order_topology_on_UNIV_eq_HOL_open unfolding top1_open_sets_def by (by100 simp)
      qed
      have h1\<phi>_R: "top1_continuous_map_on X TX (UNIV::real set) ?TOR (\<lambda>x. 1 - \<phi> x)"
      proof -
        \<comment> \<open>Constant 1 continuous.\<close>
        have hconst: "top1_continuous_map_on X TX (UNIV::real set) ?TOR (\<lambda>_. 1::real)"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix x assume "x \<in> X" show "(1::real) \<in> UNIV" by (by100 simp)
        next
          fix V assume "V \<in> ?TOR"
          have hX_open: "X \<in> TX" using hTopX unfolding is_topology_on_def by (by100 blast)
          have hempty: "{} \<in> TX" using hTopX unfolding is_topology_on_def by (by100 blast)
          show "{x \<in> X. (1::real) \<in> V} \<in> TX"
          proof -
            have "((1::real) \<in> V \<and> {x \<in> X. (1::real) \<in> V} = X) \<or>
                  ((1::real) \<notin> V \<and> {x \<in> X. (1::real) \<in> V} = {})" by (by100 blast)
            thus ?thesis using hX_open hempty by (by100 auto)
          qed
        qed
        \<comment> \<open>Pair (const 1, \<phi>) and compose with subtraction.\<close>
        have hpair_sub: "top1_continuous_map_on X TX ((UNIV::real set)\<times>(UNIV::real set)) (product_topology_on ?TOR ?TOR) (\<lambda>x. (1::real, \<phi> x))"
        proof -
          have hpi1_p: "pi1 \<circ> (\<lambda>x. (1::real, \<phi> x)) = (\<lambda>_. 1::real)"
            unfolding pi1_def by (rule ext) (by100 simp)
          have hpi2_p: "pi2 \<circ> (\<lambda>x. (1::real, \<phi> x)) = \<phi>"
            unfolding pi2_def by (rule ext) (by100 simp)
          have "top1_continuous_map_on X TX (UNIV::real set) ?TOR (pi1 \<circ> (\<lambda>x. (1::real, \<phi> x)))"
            unfolding hpi1_p by (rule hconst)
          moreover have "top1_continuous_map_on X TX (UNIV::real set) ?TOR (pi2 \<circ> (\<lambda>x. (1::real, \<phi> x)))"
            unfolding hpi2_p by (rule h\<phi>_R)
          ultimately show ?thesis using iffD2[OF Theorem_18_4[OF hTopX hTR hTR]] by (by100 blast)
        qed
        have cont_sub: "top1_continuous_map_on ((UNIV::real set)\<times>(UNIV::real set)) (product_topology_on ?TOR ?TOR) (UNIV::real set) ?TOR (\<lambda>p::real\<times>real. pi1 p - pi2 p)"
          using Lemma_21_4(2) by (by100 simp)
        have "top1_continuous_map_on X TX (UNIV::real set) ?TOR ((\<lambda>p. pi1 p - pi2 p) \<circ> (\<lambda>x. (1::real, \<phi> x)))"
          by (rule top1_continuous_map_on_comp[OF hpair_sub cont_sub])
        moreover have "(\<lambda>p::real\<times>real. pi1 p - pi2 p) \<circ> (\<lambda>x. (1, \<phi> x)) = (\<lambda>x. 1 - \<phi> x)"
          unfolding pi1_def pi2_def by (rule ext) (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>Pair (1-\<phi>, g) and compose with multiplication.\<close>
      have hpair: "top1_continuous_map_on X TX ((UNIV::real set) \<times> (UNIV::real set)) (product_topology_on ?TOR ?TOR)
          (\<lambda>x. (1 - \<phi> x, g x))"
      proof -
        have hpi1_p: "pi1 \<circ> (\<lambda>x. (1 - \<phi> x, g x)) = (\<lambda>x. 1 - \<phi> x)"
          unfolding pi1_def by (rule ext) (by100 simp)
        have hpi2_p: "pi2 \<circ> (\<lambda>x. (1 - \<phi> x, g x)) = g"
          unfolding pi2_def by (rule ext) (by100 simp)
        have "top1_continuous_map_on X TX (UNIV::real set) ?TOR (pi1 \<circ> (\<lambda>x. (1 - \<phi> x, g x)))"
          unfolding hpi1_p by (rule h1\<phi>_R)
        moreover have "top1_continuous_map_on X TX (UNIV::real set) ?TOR (pi2 \<circ> (\<lambda>x. (1 - \<phi> x, g x)))"
          unfolding hpi2_p by (rule hg_R)
        ultimately show ?thesis using iffD2[OF Theorem_18_4[OF hTopX hTR hTR]] by (by100 blast)
      qed
      have cont_mul: "top1_continuous_map_on ((UNIV::real set) \<times> (UNIV::real set)) (product_topology_on ?TOR ?TOR) (UNIV::real set) ?TOR (\<lambda>p::real\<times>real. pi1 p * pi2 p)"
        using Lemma_21_4(3) by (by100 simp)
      have "top1_continuous_map_on X TX (UNIV::real set) ?TOR ((\<lambda>p. pi1 p * pi2 p) \<circ> (\<lambda>x. (1 - \<phi> x, g x)))"
        by (rule top1_continuous_map_on_comp[OF hpair cont_mul])
      moreover have "(\<lambda>p::real\<times>real. pi1 p * pi2 p) \<circ> (\<lambda>x. (1 - \<phi> x, g x)) = (\<lambda>x. (1 - \<phi> x) * g x)"
        unfolding pi1_def pi2_def by (rule ext) (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>h_inv continuous (-1,1) \<rightarrow> R: h_inv(y) = y/(1-|y|), denominator > 0 on (-1,1).\<close>
    have hhinv_cont: "continuous_on {y::real. -1 < y \<and> y < 1} h_inv"
    proof -
      let ?S = "{y::real. -1 < y \<and> y < 1}"
      have hnum: "continuous_on ?S (\<lambda>y::real. y)" by (rule continuous_on_id)
      have hden: "continuous_on ?S (\<lambda>y::real. 1 - \<bar>y\<bar>)"
        by (intro continuous_intros)
      have hne: "\<forall>y\<in>?S. 1 - \<bar>y\<bar> \<noteq> (0::real)"
      proof (intro ballI)
        fix y :: real assume "y \<in> ?S"
        hence "-1 < y" "y < 1" by (by100 simp)+
        hence "\<bar>y\<bar> < 1" by (by100 linarith)
        thus "1 - \<bar>y\<bar> \<noteq> 0" by (by100 linarith)
      qed
      have "continuous_on ?S (\<lambda>y. y / (1 - \<bar>y\<bar>))"
        using continuous_on_divide[OF hnum hden] hne by (by100 blast)
      thus ?thesis unfolding h_inv_def by (by100 simp)
    qed
    \<comment> \<open>Compose: F = h_inv \<circ> ((1-\<phi>)\<cdot>g). Range in (-1,1), compose continuous.\<close>
    let ?OI = "{y::real. -1 < y \<and> y < 1}" \<comment> \<open>open interval (-1,1)\<close>
    let ?TOR = "order_topology_on_UNIV :: real set set"
    have hTR: "is_topology_on (UNIV::real set) ?TOR" by (rule order_topology_on_UNIV_is_topology_on)
    \<comment> \<open>Restrict codomain of (1-\<phi>)\<cdot>g to (-1,1).\<close>
    have hprod_img: "(\<lambda>x. (1 - \<phi> x) * g x) ` X \<subseteq> ?OI"
      using hrange by (by100 blast)
    have hOI_sub: "?OI \<subseteq> (UNIV::real set)" by (by100 simp)
    have hprod_OI: "top1_continuous_map_on X TX ?OI (subspace_topology UNIV ?TOR ?OI) (\<lambda>x. (1 - \<phi> x) * g x)"
      by (rule top1_continuous_map_on_codomain_shrink[OF hprod_cont hprod_img hOI_sub])
    \<comment> \<open>h_inv continuous (-1,1) \<rightarrow> R in top1 sense.\<close>
    have hhinv_top1: "top1_continuous_map_on ?OI (subspace_topology UNIV ?TOR ?OI) (UNIV::real set) ?TOR h_inv"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix y assume "y \<in> ?OI" show "h_inv y \<in> (UNIV::real set)" by (by100 simp)
    next
      fix V :: "real set" assume hV: "V \<in> ?TOR"
      hence hVopen: "open V" using order_topology_on_UNIV_eq_HOL_open by (by100 blast)
      have "\<exists>W. open W \<and> W \<inter> ?OI = h_inv -` V \<inter> ?OI"
        using hhinv_cont hVopen unfolding continuous_on_open_invariant by (by100 blast)
      then obtain W where hW: "open W" and hfW: "W \<inter> ?OI = h_inv -` V \<inter> ?OI" by (by100 auto)
      have hW_OT: "W \<in> ?TOR" using hW order_topology_on_UNIV_eq_HOL_open by (by100 blast)
      have "{y \<in> ?OI. h_inv y \<in> V} = ?OI \<inter> W" using hfW by (by100 blast)
      thus "{y \<in> ?OI. h_inv y \<in> V} \<in> subspace_topology UNIV ?TOR ?OI"
        unfolding subspace_topology_def using hW_OT by (by100 blast)
    qed
    \<comment> \<open>Compose.\<close>
    have "top1_continuous_map_on X TX (UNIV::real set) ?TOR (h_inv \<circ> (\<lambda>x. (1 - \<phi> x) * g x))"
      by (rule top1_continuous_map_on_comp[OF hprod_OI hhinv_top1])
    moreover have "h_inv \<circ> (\<lambda>x. (1 - \<phi> x) * g x) = F" unfolding F_def by (rule ext) (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  show ?thesis using hF_cont hF_ext by (by100 blast)
qed

section \<open>Additional Corollaries from \<S>51-\<S>60 (Main Theorems in Cached Sessions)\<close>

text \<open>S^1 is path-connected: for any two points, compose the covering map
  R \<rightarrow> S^1 with a linear path in R.\<close>
lemma S1_path_connected: "top1_path_connected_on top1_S1 top1_S1_topology"
  unfolding top1_path_connected_on_def
proof (intro conjI ballI)
  show "is_topology_on top1_S1 top1_S1_topology"
  proof -
    have hR: "is_topology_on (UNIV::real set) top1_open_sets"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have "is_topology_on ((UNIV::real set) \<times> (UNIV::real set))
        (product_topology_on top1_open_sets top1_open_sets)"
      by (rule product_topology_on_is_topology_on[OF hR hR])
    hence "is_topology_on (UNIV::(real\<times>real) set)
        (product_topology_on top1_open_sets top1_open_sets)" by (by100 simp)
    thus ?thesis unfolding top1_S1_topology_def
      by (rule subspace_topology_is_topology_on) (by100 blast)
  qed
next
  fix p q assume hp: "p \<in> top1_S1" and hq: "q \<in> top1_S1"
  \<comment> \<open>Get preimages under covering map.\<close>
  obtain s where hs: "p = (cos (2 * pi * s), sin (2 * pi * s))"
  proof -
    obtain a b where hab: "p = (a, b)" by (cases p)
    have "a^2 + b^2 = 1"
    proof -
      have "(fst p)^2 + (snd p)^2 = 1" using hp unfolding top1_S1_def by (by100 blast)
      thus ?thesis using hab by simp
    qed
    obtain t where ht: "a = cos t" "b = sin t"
      using sincos_total_2pi[OF \<open>a^2+b^2=1\<close>] by blast
    let ?s = "t / (2 * pi)"
    have "2 * pi * ?s = t" using pi_gt_zero by (by100 simp)
    hence "p = (cos (2 * pi * ?s), sin (2 * pi * ?s))"
      using hab ht by (by100 simp)
    thus ?thesis using that by (by100 blast)
  qed
  obtain u where hu: "q = (cos (2 * pi * u), sin (2 * pi * u))"
  proof -
    obtain a b where hab: "q = (a, b)" by (cases q)
    have "a^2 + b^2 = 1"
    proof -
      have "(fst q)^2 + (snd q)^2 = 1" using hq unfolding top1_S1_def by (by100 blast)
      thus ?thesis using hab by simp
    qed
    obtain t where ht: "a = cos t" "b = sin t"
      using sincos_total_2pi[OF \<open>a^2+b^2=1\<close>] by blast
    let ?u = "t / (2 * pi)"
    have "2 * pi * ?u = t" using pi_gt_zero by (by100 simp)
    hence "q = (cos (2 * pi * ?u), sin (2 * pi * ?u))"
      using hab ht by (by100 simp)
    thus ?thesis using that by (by100 blast)
  qed
  \<comment> \<open>Define path via linear interpolation in R, composed with covering map.\<close>
  let ?f = "\<lambda>t. (cos (2 * pi * ((1 - t) * s + t * u)), sin (2 * pi * ((1 - t) * s + t * u)))"
  have hf0: "?f 0 = p" using hs by (by100 simp)
  have hf1: "?f 1 = q" using hu by (by100 simp)
  have hf_on_S1: "\<forall>t. ?f t \<in> top1_S1"
  proof
    fix t :: real
    have "(cos (2 * pi * ((1-t)*s + t*u)))^2 + (sin (2 * pi * ((1-t)*s + t*u)))^2 = 1"
      by (rule sin_cos_squared_add2)
    thus "?f t \<in> top1_S1" unfolding top1_S1_def by (by100 force)
  qed
  have hf_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
      top1_S1 top1_S1_topology ?f"
  proof -
    \<comment> \<open>Step 1: f is continuous as a map ℝ → ℝ².\<close>
    have hcont_UNIV: "continuous_on (UNIV::real set) ?f"
      by (intro continuous_on_Pair continuous_intros)
    \<comment> \<open>Step 2: f maps into S¹.\<close>
    have hf_maps: "\<forall>t::real. ?f t \<in> top1_S1" using hf_on_S1 by (by100 blast)
    \<comment> \<open>Step 3: Bridge to top1_continuous_map_on UNIV → S¹.\<close>
    have h1: "top1_continuous_map_on (UNIV::real set) top1_open_sets
        top1_S1 (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_S1) ?f"
      by (rule top1_continuous_map_on_R_to_R2_subspace) (use hf_on_S1 hcont_UNIV in blast)+
    \<comment> \<open>Step 4: S¹ topology = subspace topology.\<close>
    have hS1_eq: "top1_S1_topology = subspace_topology UNIV
        (product_topology_on top1_open_sets top1_open_sets) top1_S1"
      unfolding top1_S1_topology_def ..
    have h2: "top1_continuous_map_on (UNIV::real set) top1_open_sets top1_S1 top1_S1_topology ?f"
      using h1 hS1_eq by (by100 simp)
    \<comment> \<open>Step 5: Restrict domain to I_set.\<close>
    have h3: "top1_continuous_map_on top1_unit_interval
        (subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval) top1_S1 top1_S1_topology ?f"
      by (rule top1_continuous_map_on_restrict_domain_simple[OF h2]) (by100 blast)
    \<comment> \<open>Step 6: Unit interval topology = subspace topology.\<close>
    thus ?thesis unfolding top1_unit_interval_topology_def .
  qed
  show "\<exists>f. top1_is_path_on top1_S1 top1_S1_topology p q f"
    using hf_cont hf0 hf1 unfolding top1_is_path_on_def by (by100 blast)
qed

text \<open>Corollary 52.2 (Munkres): If X is path connected and x0, x1 \<in> X, then
  \<pi>_1(X, x0) is isomorphic to \<pi>_1(X, x1).\<close>
corollary Corollary_52_2_basepoint_independent:
  assumes "top1_path_connected_on X TX" and "x0 \<in> X" and "x1 \<in> X"
  shows "top1_groups_isomorphic_on
    (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
    (top1_fundamental_group_carrier X TX x1) (top1_fundamental_group_mul X TX x1)"
proof -
  have "is_topology_on X TX"
    using assms(1) unfolding top1_path_connected_on_def by (by100 blast)
  thus ?thesis by (rule Theorem_52_1_iso[OF _ assms])
qed

text \<open>Lemma 52.3 (Munkres): In a simply connected space, any two paths with the same
  initial and terminal points are path homotopic.
  Already proved as simply_connected_paths_homotopic in Top1_Ch9_13.\<close>
lemma Lemma_52_3_simply_connected_unique_paths:
  assumes "top1_simply_connected_on X TX"
      and "top1_is_path_on X TX x0 x1 f" and "top1_is_path_on X TX x0 x1 g"
      and "x0 \<in> X"
  shows "top1_path_homotopic_on X TX x0 x1 f g"
  by (rule simply_connected_paths_homotopic[OF assms])

text \<open>Corollary 52.5 (Munkres): If h: (X, x0) \<rightarrow> (Y, y0) is a homeomorphism then
  h_* : \<pi>_1(X, x0) \<rightarrow> \<pi>_1(Y, y0) is an isomorphism.\<close>
corollary Corollary_52_5_homeomorphism_iso:
  assumes "is_topology_on X TX" and "is_topology_on Y TY"
      and "top1_homeomorphism_on X TX Y TY h"
      and "x0 \<in> X" and "h x0 = y0"
  shows "top1_groups_isomorphic_on
    (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
    (top1_fundamental_group_carrier Y TY y0) (top1_fundamental_group_mul Y TY y0)"
proof -
  \<comment> \<open>A homeomorphism is a homotopy equivalence, so apply Theorem 58.7.\<close>
  let ?g = "inv_into X h"
  have hh_cont: "top1_continuous_map_on X TX Y TY h"
    using assms(3) unfolding top1_homeomorphism_on_def by (by100 blast)
  have hg_cont: "top1_continuous_map_on Y TY X TX ?g"
    using assms(3) unfolding top1_homeomorphism_on_def by (by100 blast)
  have hbij: "bij_betw h X Y"
    using assms(3) unfolding top1_homeomorphism_on_def by (by100 blast)
  have hinj: "inj_on h X" using hbij unfolding bij_betw_def by (by100 blast)
  \<comment> \<open>g \<circ> h = id on X (by inv_into property), so g \<circ> h \<simeq> id.\<close>
  have hgh_eq: "\<forall>x\<in>X. (inv_into X h \<circ> h) x = x"
  proof (intro ballI)
    fix x assume "x \<in> X"
    thus "(inv_into X h \<circ> h) x = x" using inv_into_f_f[OF hinj] by (by100 simp)
  qed
  have hid_cont: "top1_continuous_map_on X TX X TX id"
    by (rule top1_continuous_map_on_id[OF assms(1)])
  \<comment> \<open>g \<circ> h continuous on X.\<close>
  have hgh_cont: "top1_continuous_map_on X TX X TX (?g \<circ> h)"
    by (rule top1_continuous_map_on_comp[OF hh_cont hg_cont])
  \<comment> \<open>g \<circ> h agrees with id on X, so they are homotopic (both continuous, same values).\<close>
  have hgh_htpy: "top1_homotopic_on X TX X TX (?g \<circ> h) (\<lambda>x. x)"
    unfolding top1_homotopic_on_def
  proof (intro conjI)
    show "top1_continuous_map_on X TX X TX (?g \<circ> h)" by (rule hgh_cont)
    show "top1_continuous_map_on X TX X TX (\<lambda>x. x)"
      using hid_cont unfolding id_def by (by100 simp)
    \<comment> \<open>Homotopy F(x,t) = (g \<circ> h)(x): constant in t, equals g \<circ> h at t=0 and id at t=1.\<close>
    show "\<exists>F. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX F
        \<and> (\<forall>x\<in>X. F (x, 0) = (?g \<circ> h) x) \<and> (\<forall>x\<in>X. F (x, 1) = x)"
    proof (rule exI[of _ "\<lambda>p. (?g \<circ> h) (fst p)"])
      have hF_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX
          (\<lambda>p. (?g \<circ> h) (fst p))"
        by (rule homotopy_const_continuous[OF hgh_cont assms(1)])
      show "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX
            (\<lambda>p. (?g \<circ> h) (fst p))
          \<and> (\<forall>x\<in>X. (?g \<circ> h) (fst (x, 0::real)) = (?g \<circ> h) x)
          \<and> (\<forall>x\<in>X. (?g \<circ> h) (fst (x, 1::real)) = x)"
        using hF_cont hgh_eq by (by100 simp)
    qed
  qed
  \<comment> \<open>h \<circ> g = id on Y — symmetric argument.\<close>
  have hhg_htpy: "top1_homotopic_on Y TY Y TY (h \<circ> ?g) (\<lambda>y. y)"
    unfolding top1_homotopic_on_def
  proof (intro conjI)
    show "top1_continuous_map_on Y TY Y TY (h \<circ> ?g)"
      by (rule top1_continuous_map_on_comp[OF hg_cont hh_cont])
    show "top1_continuous_map_on Y TY Y TY (\<lambda>y. y)"
      using top1_continuous_map_on_id[OF assms(2)] unfolding id_def by (by100 simp)
    have hhg_eq: "\<forall>y\<in>Y. (h \<circ> ?g) y = y"
    proof (intro ballI)
      fix y assume "y \<in> Y"
      hence "?g y \<in> X" using hg_cont unfolding top1_continuous_map_on_def by (by100 blast)
      have "h (?g y) = y"
      proof -
        have "y \<in> h ` X" using hbij \<open>y \<in> Y\<close> unfolding bij_betw_def by (by100 blast)
        thus ?thesis by (rule f_inv_into_f)
      qed
      thus "(h \<circ> ?g) y = y" by (by100 simp)
    qed
    show "\<exists>F. top1_continuous_map_on (Y \<times> I_set) (product_topology_on TY I_top) Y TY F
        \<and> (\<forall>y\<in>Y. F (y, 0) = (h \<circ> ?g) y) \<and> (\<forall>y\<in>Y. F (y, 1) = y)"
    proof (rule exI[of _ "\<lambda>p. (h \<circ> ?g) (fst p)"])
      have "top1_continuous_map_on (Y \<times> I_set) (product_topology_on TY I_top) Y TY
          (\<lambda>p. (h \<circ> ?g) (fst p))"
        by (rule homotopy_const_continuous[OF top1_continuous_map_on_comp[OF hg_cont hh_cont] assms(2)])
      thus "top1_continuous_map_on (Y \<times> I_set) (product_topology_on TY I_top) Y TY
            (\<lambda>p. (h \<circ> ?g) (fst p))
          \<and> (\<forall>y\<in>Y. (h \<circ> ?g) (fst (y, 0::real)) = (h \<circ> ?g) y)
          \<and> (\<forall>y\<in>Y. (h \<circ> ?g) (fst (y, 1::real)) = y)"
        using hhg_eq by (by100 simp)
    qed
  qed
  have heq: "top1_homotopy_equivalence_on X TX Y TY h ?g"
    unfolding top1_homotopy_equivalence_on_def
    using hh_cont hg_cont hgh_htpy hhg_htpy by (by100 blast)
  show ?thesis using Theorem_58_7[OF assms(1,2) heq assms(4)] assms(5) by (by100 simp)
qed

text \<open>Theorem 57.2 (Munkres): There is no continuous antipode-preserving map g : S^2 \<rightarrow> S^1.
  Proof: restricting g to the equator S^1 \<hookrightarrow> S^2 gives an antipode-preserving
  S^1 \<rightarrow> S^1 map, which by Theorem 57.1 is not nulhomotopic. But the upper hemisphere
  E \<cong> B^2 extends g|_{S^1} to B^2, making it nulhomotopic. Contradiction.\<close>
theorem Theorem_57_2_no_antipode_S2_to_S1:
  assumes "top1_continuous_map_on top1_S2 top1_S2_topology top1_S1 top1_S1_topology g"
      and "\<forall>x\<in>top1_S2. g (- fst x, - fst (snd x), - snd (snd x)) =
             (- fst (g x), - snd (g x))"
  shows False
  \<comment> \<open>Proof: define h: S¹→S¹ as g restricted to equator S¹⊂S² (with normalization).
     h is continuous and antipode-preserving → NOT nulhomotopic by Theorem 57.1.
     But g|_{upper hemisphere} extends h to B² → h IS nulhomotopic by Lemma 55.3.
     Contradiction.\<close>
  sorry

text \<open>Transitivity of group isomorphism (used early, moved here from later).\<close>
lemma groups_isomorphic_trans_fwd:
  assumes "top1_groups_isomorphic_on G mulG H mulH"
      and "top1_groups_isomorphic_on H mulH K mulK"
  shows "top1_groups_isomorphic_on G mulG K mulK"
proof -
  obtain f where hf: "top1_group_hom_on G mulG H mulH f" "bij_betw f G H"
    using assms(1) unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def by blast
  obtain g where hg: "top1_group_hom_on H mulH K mulK g" "bij_betw g H K"
    using assms(2) unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def by blast
  have "top1_group_hom_on G mulG K mulK (g \<circ> f)"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    fix x assume "x \<in> G"
    thus "(g \<circ> f) x \<in> K"
      using hf(1) hg(1) unfolding top1_group_hom_on_def comp_def by (by100 blast)
  next
    fix x y assume "x \<in> G" "y \<in> G"
    thus "(g \<circ> f) (mulG x y) = mulK ((g \<circ> f) x) ((g \<circ> f) y)"
      using hf(1) hg(1) unfolding top1_group_hom_on_def comp_def by (by100 force)
  qed
  moreover have "bij_betw (g \<circ> f) G K"
    by (rule bij_betw_trans[OF hf(2) hg(2)])
  ultimately show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def by (by100 blast)
qed

text \<open>Product of isomorphic groups: if G₁ ≅ H₁ and G₂ ≅ H₂ then G₁×G₂ ≅ H₁×H₂.\<close>
lemma product_groups_isomorphic:
  assumes "top1_groups_isomorphic_on G1 mul1 H1 mulH1"
      and "top1_groups_isomorphic_on G2 mul2 H2 mulH2"
  shows "top1_groups_isomorphic_on
    (G1 \<times> G2) (\<lambda>(a1,a2) (b1,b2). (mul1 a1 b1, mul2 a2 b2))
    (H1 \<times> H2) (\<lambda>(a1,a2) (b1,b2). (mulH1 a1 b1, mulH2 a2 b2))"
proof -
  obtain f1 where hf1_hom: "top1_group_hom_on G1 mul1 H1 mulH1 f1"
      and hf1_bij: "bij_betw f1 G1 H1"
    using assms(1) unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def by blast
  obtain f2 where hf2_hom: "top1_group_hom_on G2 mul2 H2 mulH2 f2"
      and hf2_bij: "bij_betw f2 G2 H2"
    using assms(2) unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def by blast
  let ?f = "\<lambda>(a, b). (f1 a, f2 b)"
  have hf_hom: "top1_group_hom_on (G1 \<times> G2)
      (\<lambda>(a1,a2) (b1,b2). (mul1 a1 b1, mul2 a2 b2))
      (H1 \<times> H2) (\<lambda>(a1,a2) (b1,b2). (mulH1 a1 b1, mulH2 a2 b2)) ?f"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    fix p assume "p \<in> G1 \<times> G2"
    then obtain a b where "p = (a,b)" "a \<in> G1" "b \<in> G2" by (by100 blast)
    thus "?f p \<in> H1 \<times> H2"
      using hf1_hom hf2_hom unfolding top1_group_hom_on_def by (by100 force)
  next
    fix p q assume "p \<in> G1 \<times> G2" "q \<in> G1 \<times> G2"
    then obtain a1 a2 b1 b2 where hp: "p = (a1,a2)" "a1 \<in> G1" "a2 \<in> G2"
        and hq: "q = (b1,b2)" "b1 \<in> G1" "b2 \<in> G2" by (by100 force)
    show "?f ((\<lambda>(a1,a2) (b1,b2). (mul1 a1 b1, mul2 a2 b2)) p q)
        = (\<lambda>(a1,a2) (b1,b2). (mulH1 a1 b1, mulH2 a2 b2)) (?f p) (?f q)"
      using hp hq hf1_hom hf2_hom unfolding top1_group_hom_on_def by (by100 force)
  qed
  have hf_bij: "bij_betw ?f (G1 \<times> G2) (H1 \<times> H2)"
    unfolding bij_betw_def
  proof (intro conjI)
    show "inj_on ?f (G1 \<times> G2)"
    proof (rule inj_onI)
      fix p q assume "p \<in> G1 \<times> G2" "q \<in> G1 \<times> G2" "?f p = ?f q"
      then obtain a1 a2 b1 b2 where hp: "p = (a1,a2)" "a1 \<in> G1" "a2 \<in> G2"
          and hq: "q = (b1,b2)" "b1 \<in> G1" "b2 \<in> G2" by (by100 force)
      from \<open>?f p = ?f q\<close> have "f1 a1 = f1 b1" "f2 a2 = f2 b2"
        using hp hq by (by100 simp)+
      hence "a1 = b1" "a2 = b2"
        using hf1_bij hf2_bij hp hq unfolding bij_betw_def
        by (metis inj_onD)+
      thus "p = q" using hp hq by (by100 simp)
    qed
    show "?f ` (G1 \<times> G2) = H1 \<times> H2"
    proof
      show "?f ` (G1 \<times> G2) \<subseteq> H1 \<times> H2"
        using hf1_bij hf2_bij unfolding bij_betw_def by (by100 force)
      show "H1 \<times> H2 \<subseteq> ?f ` (G1 \<times> G2)"
      proof
        fix p assume "p \<in> H1 \<times> H2"
        then obtain h1 h2 where hp: "p = (h1,h2)" "h1 \<in> H1" "h2 \<in> H2" by (by100 blast)
        obtain g1 where "g1 \<in> G1" "f1 g1 = h1"
          using hf1_bij hp(2) unfolding bij_betw_def by (by100 force)
        obtain g2 where "g2 \<in> G2" "f2 g2 = h2"
          using hf2_bij hp(3) unfolding bij_betw_def by (by100 force)
        show "p \<in> ?f ` (G1 \<times> G2)"
          using hp \<open>g1 \<in> G1\<close> \<open>g2 \<in> G2\<close> \<open>f1 g1 = h1\<close> \<open>f2 g2 = h2\<close> by (by100 force)
      qed
    qed
  qed
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
    using hf_hom hf_bij by (by100 blast)
qed

text \<open>Corollary 60.2 (Munkres): pi_1(T^2) is isomorphic to Z x Z.\<close>
corollary Corollary_60_2_torus_pi1:
  assumes "is_topology_on X TX" and "is_topology_on Y TY"
      and "top1_homeomorphism_on X TX (top1_S1 \<times> top1_S1)
             (product_topology_on top1_S1_topology top1_S1_topology) h"
      and "x0 \<in> X"
  shows "top1_groups_isomorphic_on
    (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
    (UNIV :: (int \<times> int) set) (\<lambda>(a1, a2) (b1, b2). (a1 + b1, a2 + b2))"
proof -
  let ?T2 = "top1_S1 \<times> top1_S1"
  let ?TT2 = "product_topology_on top1_S1_topology top1_S1_topology"
  let ?p = "h x0"
  \<comment> \<open>Step 1: h(x0) \<in> S^1 \<times> S^1.\<close>
  have hx0_T2: "?p \<in> ?T2"
    using assms(3,4) unfolding top1_homeomorphism_on_def top1_continuous_map_on_def by (by100 blast)
  \<comment> \<open>Step 2: \<pi>_1(X, x0) \<cong> \<pi>_1(S^1 \<times> S^1, h(x0)) by homeomorphism.\<close>
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
  proof -
    have hR: "is_topology_on (UNIV::real set) top1_open_sets"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have "is_topology_on ((UNIV::real set) \<times> (UNIV::real set))
        (product_topology_on top1_open_sets top1_open_sets)"
      by (rule product_topology_on_is_topology_on[OF hR hR])
    hence hR2: "is_topology_on (UNIV::(real\<times>real) set)
        (product_topology_on top1_open_sets top1_open_sets)" by (by100 simp)
    show ?thesis unfolding top1_S1_topology_def
      by (rule subspace_topology_is_topology_on[OF hR2]) (by100 blast)
  qed
  have hTT2: "is_topology_on ?T2 ?TT2"
    by (rule product_topology_on_is_topology_on[OF hTS1 hTS1])
  have h_iso1: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_carrier ?T2 ?TT2 ?p)
      (top1_fundamental_group_mul ?T2 ?TT2 ?p)"
    by (rule Corollary_52_5_homeomorphism_iso[OF assms(1) hTT2 assms(3) assms(4) refl])
  \<comment> \<open>Step 3: \<pi>_1(S^1 \<times> S^1, (p1,p2)) \<cong> \<pi>_1(S^1, p1) \<times> \<pi>_1(S^1, p2).\<close>
  obtain p1 p2 where hp: "?p = (p1, p2)" and hp1: "p1 \<in> top1_S1" and hp2: "p2 \<in> top1_S1"
    using hx0_T2 by (by100 force)
  \<comment> \<open>Step 4: Apply Theorem 60.1 (product of fundamental groups).\<close>
  have hS1_strict: "is_topology_on_strict top1_S1 top1_S1_topology"
    by (rule top1_S1_is_topology_on_strict)
  have h_iso2: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier ?T2 ?TT2 ?p)
      (top1_fundamental_group_mul ?T2 ?TT2 ?p)
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology p1 \<times>
       top1_fundamental_group_carrier top1_S1 top1_S1_topology p2)
      (\<lambda>(c1,c2) (d1,d2). (top1_fundamental_group_mul top1_S1 top1_S1_topology p1 c1 d1,
                           top1_fundamental_group_mul top1_S1 top1_S1_topology p2 c2 d2))"
    using Theorem_60_1_product[OF hS1_strict hS1_strict hp1 hp2] hp by (by100 simp)
  \<comment> \<open>Step 5: Basepoint change \<pi>_1(S^1, p_i) \<cong> \<pi>_1(S^1, (1,0)) using path connectivity.\<close>
  have h10_S1: "(1::real, 0::real) \<in> top1_S1"
    unfolding top1_S1_def by (by100 force)
  have h_iso3a: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology p1)
      (top1_fundamental_group_mul top1_S1 top1_S1_topology p1)
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))"
    by (rule Corollary_52_2_basepoint_independent[OF S1_path_connected hp1 h10_S1])
  have h_iso3b: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology p2)
      (top1_fundamental_group_mul top1_S1 top1_S1_topology p2)
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))"
    by (rule Corollary_52_2_basepoint_independent[OF S1_path_connected hp2 h10_S1])
  \<comment> \<open>Step 6: \<pi>_1(S^1, (1,0)) \<cong> Z by Theorem 54.5.\<close>
  have h_iso4: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
      top1_Z_group top1_Z_mul"
    by (rule Theorem_54_5_iso)
  \<comment> \<open>Step 7: Compose: \<pi>_1(S^1,p1) \<cong> Z and \<pi>_1(S^1,p2) \<cong> Z.\<close>
  have h_iso5a: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology p1)
      (top1_fundamental_group_mul top1_S1 top1_S1_topology p1)
      top1_Z_group top1_Z_mul"
    by (rule groups_isomorphic_trans_fwd[OF h_iso3a h_iso4])
  have h_iso5b: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology p2)
      (top1_fundamental_group_mul top1_S1 top1_S1_topology p2)
      top1_Z_group top1_Z_mul"
    by (rule groups_isomorphic_trans_fwd[OF h_iso3b h_iso4])
  \<comment> \<open>Step 8: Product: \<pi>_1(S^1,p1) \<times> \<pi>_1(S^1,p2) \<cong> Z \<times> Z.\<close>
  have h_iso6: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology p1 \<times>
       top1_fundamental_group_carrier top1_S1 top1_S1_topology p2)
      (\<lambda>(c1,c2) (d1,d2). (top1_fundamental_group_mul top1_S1 top1_S1_topology p1 c1 d1,
                           top1_fundamental_group_mul top1_S1 top1_S1_topology p2 c2 d2))
      (top1_Z_group \<times> top1_Z_group) (\<lambda>(a1,a2) (b1,b2). (top1_Z_mul a1 b1, top1_Z_mul a2 b2))"
    by (rule product_groups_isomorphic[OF h_iso5a h_iso5b])
  \<comment> \<open>Step 9: Z \<times> Z = UNIV \<times> UNIV = UNIV :: (int\<times>int) set,
     with mul (a1,a2)(b1,b2) = (a1+b1, a2+b2).\<close>
  have hZZ_eq: "top1_Z_group \<times> top1_Z_group = (UNIV :: (int \<times> int) set)"
    unfolding top1_Z_group_def by (by100 auto)
  have hZZ_mul: "(\<lambda>(a1,a2) (b1,b2). (top1_Z_mul a1 b1, top1_Z_mul a2 b2))
    = (\<lambda>(a1::int, a2::int) (b1, b2). (a1 + b1, a2 + b2))"
    unfolding top1_Z_mul_def by (rule ext)+ (by100 simp)
  \<comment> \<open>Step 10: Chain all isomorphisms.\<close>
  have h_chain: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
      (UNIV :: (int \<times> int) set) (\<lambda>(a1, a2) (b1, b2). (a1 + b1, a2 + b2))"
  proof -
    have c1: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology p1 \<times>
         top1_fundamental_group_carrier top1_S1 top1_S1_topology p2)
        (\<lambda>(c1,c2) (d1,d2). (top1_fundamental_group_mul top1_S1 top1_S1_topology p1 c1 d1,
                             top1_fundamental_group_mul top1_S1 top1_S1_topology p2 c2 d2))"
      by (rule groups_isomorphic_trans_fwd[OF h_iso1 h_iso2])
    have c2: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
        (top1_Z_group \<times> top1_Z_group) (\<lambda>(a1,a2) (b1,b2). (top1_Z_mul a1 b1, top1_Z_mul a2 b2))"
      by (rule groups_isomorphic_trans_fwd[OF c1 h_iso6])
    show ?thesis using c2 hZZ_eq hZZ_mul by (by100 simp)
  qed
  show ?thesis by (rule h_chain)
qed

text \<open>Lemma 60.5 (Munkres): The fundamental group of the figure eight is not abelian.\<close>
lemma Lemma_60_5_figure_eight_not_abelian:
  assumes "is_topology_on X TX"
      and "top1_is_wedge_of_circles_on X TX {0::nat, 1} p"
  shows "\<not> (\<forall>a\<in>top1_fundamental_group_carrier X TX p.
             \<forall>b\<in>top1_fundamental_group_carrier X TX p.
               top1_fundamental_group_mul X TX p a b = top1_fundamental_group_mul X TX p b a)"
  sorry

section \<open>*\<S>62 Invariance of Domain\<close>

text \<open>Lemma 62.1 (Homotopy extension lemma). If X \<times> I is normal, A closed in X,
  f: A \<rightarrow> Y continuous where Y open in R^n, and f nulhomotopic, then f extends to g: X \<rightarrow> Y.
  This is the key tool for the Borsuk lemma. Uses Tietze extension (Theorem_35_1),
  tube lemma (Lemma_26_8), Urysohn separation (Theorem_33_1).\<close>
lemma Lemma_62_1_homotopy_extension:
  fixes f :: "'a \<Rightarrow> real \<times> real"
  assumes hTX_top: "is_topology_on X TX"
      and hX_normal: "top1_normal_on X TX"
      and hXI_normal: "top1_normal_on (X \<times> I_set) (product_topology_on TX I_top)"
      and hA_closed: "closedin_on X TX A"
      and hY_open: "Y \<in> product_topology_on top1_open_sets top1_open_sets"
      and hf: "top1_continuous_map_on A (subspace_topology X TX A) Y
               (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) Y) f"
      and hnul: "top1_nulhomotopic_on A (subspace_topology X TX A) Y
               (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) Y) f"
  shows "\<exists>g. top1_continuous_map_on X TX Y
               (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) Y) g
             \<and> (\<forall>x\<in>A. g x = f x)
             \<and> top1_nulhomotopic_on X TX Y
               (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) Y) g"
proof -
  let ?TR2 = "product_topology_on top1_open_sets top1_open_sets :: (real\<times>real) set set"
  let ?TY = "subspace_topology UNIV ?TR2 Y"
  have hTX: "is_topology_on X TX" by (rule hTX_top)
  have hAX: "A \<subseteq> X" using hA_closed by (rule closedin_sub)
  \<comment> \<open>Step 1: Get nulhomotopy F: A \<times> I \<rightarrow> Y with F(a,0) = f(a), F(a,1) = y0.\<close>
  obtain y0 where hy0: "y0 \<in> Y"
      and hF_hom: "top1_homotopic_on A (subspace_topology X TX A) Y ?TY f (\<lambda>_. y0)"
    using hnul unfolding top1_nulhomotopic_on_def by (by100 blast)
  obtain F where hF: "top1_continuous_map_on (A \<times> I_set)
      (product_topology_on (subspace_topology X TX A) I_top)
      Y ?TY F"
      and hF0: "\<forall>a\<in>A. F (a, 0) = f a"
      and hF1: "\<forall>a\<in>A. F (a, 1) = y0"
    using hF_hom unfolding top1_homotopic_on_def by (by100 blast)
  \<comment> \<open>Step 2: Extend F to (A\<times>I) \<union> (X\<times>{1}) by setting F(x,1) = y0.
     Fe agrees with F on A\<times>I and maps (x,1) to y0 for all x \<in> X.\<close>
  let ?S = "(A \<times> I_set) \<union> (X \<times> {1::real})"
  define Fe where "Fe = (\<lambda>(x, t). if x \<in> A then F (x, t) else y0)"
  have hFe_agree_AI: "\<forall>p\<in>A \<times> I_set. Fe p = F p"
    unfolding Fe_def by (by100 auto)
  have hFe_X1: "\<forall>x\<in>X. Fe (x, 1) = y0"
    unfolding Fe_def using hF1 by (by100 auto)
  have hFe_range: "\<forall>p\<in>?S. Fe p \<in> Y"
  proof (intro ballI)
    fix p assume "p \<in> ?S"
    hence "p \<in> A \<times> I_set \<or> p \<in> X \<times> {1::real}" by (by100 blast)
    thus "Fe p \<in> Y"
    proof
      assume "p \<in> A \<times> I_set"
      hence "Fe p = F p" using hFe_agree_AI by (by100 blast)
      moreover have "F p \<in> Y" using hF \<open>p \<in> A \<times> I_set\<close> unfolding top1_continuous_map_on_def
        by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    next
      assume "p \<in> X \<times> {1::real}"
      then obtain x where hxX: "x \<in> X" and hp: "p = (x, 1)" by (by100 blast)
      have "Fe p = y0"
      proof (cases "x \<in> A")
        case True thus ?thesis unfolding hp Fe_def using hF1 True by (by100 simp)
      next
        case False thus ?thesis unfolding hp Fe_def by (by100 simp)
      qed
      thus ?thesis using hy0 by (by100 simp)
    qed
  qed
  \<comment> \<open>Step 3: Tietze-extend Fe coordinatewise to G: X\<times>I \<rightarrow> R^2.
     Each coordinate of Fe: ?S \<rightarrow> [-M,M] for large M. Tietze extends to X\<times>I.\<close>
  \<comment> \<open>Step 3a: ?S is closed in X\<times>I.\<close>
  have hTXI: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
    by (rule product_topology_on_is_topology_on[OF hTX top1_unit_interval_topology_is_topology_on])
  have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  have hAI_closed: "closedin_on (X \<times> I_set) (product_topology_on TX I_top) (A \<times> I_set)"
  proof (rule closedin_intro)
    show "A \<times> I_set \<subseteq> X \<times> I_set" using hAX by (by100 blast)
    have hXA_open: "X - A \<in> TX"
      using hA_closed unfolding closedin_on_def by (by100 blast)
    have "(X \<times> I_set) - (A \<times> I_set) = (X - A) \<times> I_set"
      by (by100 blast)
    moreover have "(X - A) \<times> I_set \<in> product_topology_on TX I_top"
    proof -
      have "I_set \<in> I_top" using hTI unfolding is_topology_on_def by (by100 blast)
      thus ?thesis by (rule product_rect_open[OF hXA_open])
    qed
    ultimately show "(X \<times> I_set) - (A \<times> I_set) \<in> product_topology_on TX I_top" by (by100 simp)
  qed
  have h1_closed_I: "closedin_on I_set I_top {1::real}"
  proof (rule closedin_intro)
    show "{1::real} \<subseteq> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have "I_set - {1::real} = I_set \<inter> {x. x < 1}"
      unfolding top1_unit_interval_def by (by100 auto)
    moreover have "{x::real. x < 1} \<in> top1_open_sets"
      unfolding top1_open_sets_def using open_lessThan[of "1::real"] unfolding lessThan_def by (by100 blast)
    moreover have "I_top = subspace_topology (UNIV::real set) top1_open_sets I_set"
      unfolding top1_unit_interval_topology_def top1_unit_interval_def by (by100 simp)
    ultimately show "I_set - {1::real} \<in> I_top"
      unfolding top1_unit_interval_topology_def top1_unit_interval_def subspace_topology_def
      by (by100 auto)
  qed
  have hX1_closed: "closedin_on (X \<times> I_set) (product_topology_on TX I_top) (X \<times> {1::real})"
  proof (rule closedin_intro)
    show "X \<times> {1::real} \<subseteq> X \<times> I_set"
      unfolding top1_unit_interval_def by (by100 auto)
    have "(X \<times> I_set) - (X \<times> {1::real}) = X \<times> (I_set - {1::real})"
      by (by100 blast)
    moreover have "I_set - {1::real} \<in> I_top"
      using h1_closed_I unfolding closedin_on_def by (by100 blast)
    moreover have "X \<in> TX" using hTX unfolding is_topology_on_def by (by100 blast)
    ultimately show "(X \<times> I_set) - (X \<times> {1::real}) \<in> product_topology_on TX I_top"
      by (by100 simp) (rule product_rect_open)
  qed
  have hS_closed: "closedin_on (X \<times> I_set) (product_topology_on TX I_top) ?S"
  proof -
    have hfin: "finite {(A \<times> I_set), (X \<times> {1::real})}" by (by100 simp)
    have hall: "\<forall>C \<in> {(A \<times> I_set), (X \<times> {1::real})}. closedin_on (X \<times> I_set) (product_topology_on TX I_top) C"
      using hAI_closed hX1_closed by (by100 blast)
    have "closedin_on (X \<times> I_set) (product_topology_on TX I_top)
      (\<Union>{(A \<times> I_set), (X \<times> {1::real})})"
      by (rule closedin_Union_finite[OF hTXI hfin hall])
    moreover have "\<Union>{(A \<times> I_set), (X \<times> {1::real})} = ?S" by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Step 3b: Fe continuous on ?S via closed pasting lemma.\<close>
  have hFe_cont: "top1_continuous_map_on ?S (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?S) Y ?TY Fe"
  proof -
    \<comment> \<open>Fe on A\<times>I = F: continuous by hF (with subspace topology adjustment).\<close>
    have hFe_AI: "top1_continuous_map_on (A \<times> I_set)
        (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) (A \<times> I_set)) Y ?TY Fe"
    proof -
      \<comment> \<open>On A\<times>I, Fe = F. Bridge topology: subspace of product = product of subspace.\<close>
      have hbridge: "subspace_topology (X \<times> I_set) (product_topology_on TX I_top) (A \<times> I_set)
          = product_topology_on (subspace_topology X TX A) I_top"
      proof -
        have "subspace_topology (X \<times> I_set) (product_topology_on TX I_top) (A \<times> I_set)
            = product_topology_on (subspace_topology X TX A) (subspace_topology I_set I_top I_set)"
          using Theorem_16_3[OF hTX hTI, of A I_set, symmetric] .
        moreover have "subspace_topology I_set I_top I_set = I_top"
        proof (rule subspace_topology_self)
          show "\<forall>U\<in>I_top. U \<subseteq> I_set"
          proof (intro ballI)
            fix U assume "U \<in> I_top"
            then obtain W where "U = I_set \<inter> W"
              unfolding top1_unit_interval_topology_def top1_unit_interval_def subspace_topology_def
              by (by100 blast)
            thus "U \<subseteq> I_set" by (by100 blast)
          qed
        qed
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>Fe = F on A\<times>I_set.\<close>
      have hFe_eq_F: "\<forall>p\<in>A \<times> I_set. Fe p = F p" using hFe_agree_AI by (by100 blast)
      \<comment> \<open>F continuous A\<times>I with product (subspace A) \<times> I_top.\<close>
      show ?thesis unfolding hbridge top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix p assume hp: "p \<in> A \<times> I_set"
        have "Fe p = F p" using hFe_eq_F hp by (by100 blast)
        moreover have "F p \<in> Y" using hF hp unfolding top1_continuous_map_on_def by (by100 blast)
        ultimately show "Fe p \<in> Y" by (by100 simp)
      next
        fix V assume hV: "V \<in> ?TY"
        have "{p \<in> A \<times> I_set. Fe p \<in> V} = {p \<in> A \<times> I_set. F p \<in> V}"
          using hFe_eq_F by (by100 auto)
        moreover have "{p \<in> A \<times> I_set. F p \<in> V} \<in> product_topology_on (subspace_topology X TX A) I_top"
          using hF hV unfolding top1_continuous_map_on_def by (by100 blast)
        ultimately show "{p \<in> A \<times> I_set. Fe p \<in> V} \<in> product_topology_on (subspace_topology X TX A) I_top"
          by (by100 simp)
      qed
    qed
    \<comment> \<open>Fe on X\<times>{1} = constant y0: continuous.\<close>
    have hFe_X1: "top1_continuous_map_on (X \<times> {1::real})
        (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) (X \<times> {1::real})) Y ?TY Fe"
    proof -
      \<comment> \<open>On X\<times>\{1\}, Fe(x,1) = y0 for all x \<in> X.\<close>
      have hFe_const: "\<forall>p\<in>X \<times> {1::real}. Fe p = y0"
      proof (intro ballI)
        fix p assume "p \<in> X \<times> {1::real}"
        then obtain x where hx: "x \<in> X" and hp: "p = (x, 1)" by (by100 blast)
        show "Fe p = y0" unfolding hp Fe_def using hF1 by (by100 auto)
      qed
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix p assume hp: "p \<in> X \<times> {1::real}"
        have "Fe p = y0" using hFe_const hp by (by100 blast)
        thus "Fe p \<in> Y" using hy0 by (by100 simp)
      next
        fix V assume hV: "V \<in> ?TY"
        show "{p \<in> X \<times> {1::real}. Fe p \<in> V} \<in>
            subspace_topology (X \<times> I_set) (product_topology_on TX I_top) (X \<times> {1::real})"
        proof (cases "y0 \<in> V")
          case True
          have "\<forall>p\<in>X \<times> {1::real}. Fe p \<in> V"
            using hFe_const True by (by100 simp)
          hence "{p \<in> X \<times> {1::real}. Fe p \<in> V} = X \<times> {1::real}" by (by100 blast)
          moreover have "X \<times> {1::real} \<in> subspace_topology (X \<times> I_set) (product_topology_on TX I_top) (X \<times> {1::real})"
          proof -
            have hXI_open: "(X \<times> I_set) \<in> product_topology_on TX I_top"
              using hTXI unfolding is_topology_on_def by (by100 blast)
            have "X \<times> {1::real} = (X \<times> {1::real}) \<inter> (X \<times> I_set)"
              unfolding top1_unit_interval_def by (by100 auto)
            thus ?thesis unfolding subspace_topology_def using hXI_open by (by100 blast)
          qed
          ultimately show ?thesis by (by100 simp)
        next
          case False
          have "\<forall>p\<in>X \<times> {1::real}. Fe p \<notin> V"
            using hFe_const False by (by100 simp)
          hence heq: "{p \<in> X \<times> {1::real}. Fe p \<in> V} = {}" by (by100 blast)
          have "{} \<in> subspace_topology (X \<times> I_set) (product_topology_on TX I_top) (X \<times> {1::real})"
          proof -
            have "{} \<in> product_topology_on TX I_top"
              using hTXI unfolding is_topology_on_def by (by100 blast)
            have "(X \<times> {1::real}) \<inter> {} = {}" by (by100 blast)
            thus ?thesis unfolding subspace_topology_def
              using \<open>{} \<in> product_topology_on TX I_top\<close> by (by100 blast)
          qed
          thus ?thesis unfolding heq .
        qed
      qed
    qed
    \<comment> \<open>Paste: both are closed in X\<times>I, their union is ?S.\<close>
    have hS_union: "(A \<times> I_set) \<union> (X \<times> {1::real}) = ?S" by (by100 blast)
    have hS_sub: "?S \<subseteq> X \<times> I_set" using hAX unfolding top1_unit_interval_def by (by100 auto)
    have hAI_closed_S: "closedin_on ?S (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?S) (A \<times> I_set)"
    proof -
      have "A \<times> I_set = (A \<times> I_set) \<inter> ?S" by (by100 blast)
      thus ?thesis using iffD2[OF Theorem_17_2[OF hTXI hS_sub]] hAI_closed by (by100 blast)
    qed
    have hX1_closed_S: "closedin_on ?S (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?S) (X \<times> {1::real})"
    proof -
      have "X \<times> {1::real} = (X \<times> {1::real}) \<inter> ?S"
        unfolding top1_unit_interval_def by (by100 auto)
      thus ?thesis using iffD2[OF Theorem_17_2[OF hTXI hS_sub]] hX1_closed by (by100 blast)
    qed
    have hTS: "is_topology_on ?S (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?S)"
    proof -
      have "?S \<subseteq> X \<times> I_set" using hAX unfolding top1_unit_interval_def by (by100 auto)
      thus ?thesis by (rule subspace_topology_is_topology_on[OF hTXI])
    qed
    have hTY_top: "is_topology_on Y ?TY"
    proof -
      have hTR2: "is_topology_on (UNIV::(real\<times>real) set) ?TR2"
        using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by (by100 simp)
      have "Y \<subseteq> (UNIV::(real\<times>real) set)" by (by100 simp)
      thus ?thesis by (rule subspace_topology_is_topology_on[OF hTR2])
    qed
    \<comment> \<open>Adjust continuity from subspace of X\<times>I to subspace of ?S.\<close>
    have hFe_AI_S: "top1_continuous_map_on (A \<times> I_set)
        (subspace_topology ?S (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?S) (A \<times> I_set)) Y ?TY Fe"
    proof -
      have hAI_sub_S: "A \<times> I_set \<subseteq> ?S" by (by100 blast)
      have "subspace_topology ?S (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?S) (A \<times> I_set)
          = subspace_topology (X \<times> I_set) (product_topology_on TX I_top) (A \<times> I_set)"
        by (rule subspace_topology_trans[OF hAI_sub_S])
      thus ?thesis using hFe_AI by (by100 simp)
    qed
    have hFe_X1_S: "top1_continuous_map_on (X \<times> {1::real})
        (subspace_topology ?S (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?S) (X \<times> {1::real})) Y ?TY Fe"
    proof -
      have hX1_sub_S: "X \<times> {1::real} \<subseteq> ?S"
        unfolding top1_unit_interval_def by (by100 auto)
      have "subspace_topology ?S (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?S) (X \<times> {1::real})
          = subspace_topology (X \<times> I_set) (product_topology_on TX I_top) (X \<times> {1::real})"
        by (rule subspace_topology_trans[OF hX1_sub_S])
      thus ?thesis using hFe_X1 by (by100 simp)
    qed
    have hFe_range: "\<forall>x\<in>?S. Fe x \<in> Y"
      using \<open>\<forall>p\<in>?S. Fe p \<in> Y\<close> by (by100 blast)
    show ?thesis
      by (rule pasting_lemma_two_closed[OF hTS hTY_top hAI_closed_S hX1_closed_S hS_union hFe_range hFe_AI_S hFe_X1_S])
  qed
  \<comment> \<open>Step 3c: Apply Tietze coordinatewise. Each coordinate of Fe is continuous
     ?S \<rightarrow> R. By Theorem_35_1_R (Tietze for R target), extend to X\<times>I \<rightarrow> R.
     Combine two coordinate extensions into G: X\<times>I \<rightarrow> R^2.\<close>
  obtain G :: "'a \<times> real \<Rightarrow> real \<times> real" where
      hG_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
          UNIV ?TR2 G"
      and hG_ext: "\<forall>p\<in>?S. G p = Fe p"
  proof -
    let ?TOR = "order_topology_on_UNIV :: real set set"
    have hTR: "is_topology_on (UNIV::real set) ?TOR" by (rule order_topology_on_UNIV_is_topology_on)
    have hTR_eq: "(order_topology_on_UNIV :: real set set) = top1_open_sets"
    proof (rule set_eqI)
      fix U :: "real set"
      show "U \<in> order_topology_on_UNIV \<longleftrightarrow> U \<in> top1_open_sets"
        using order_topology_on_UNIV_eq_HOL_open unfolding top1_open_sets_def by (by100 simp)
    qed
    \<comment> \<open>Projections continuous from R^2.\<close>
    have hfst_cont: "top1_continuous_map_on (UNIV::(real\<times>real) set) ?TR2 (UNIV::real set) ?TOR fst"
    proof -
      have hTOS_R: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
        by (rule top1_open_sets_is_topology_on_UNIV)
      have "top1_continuous_map_on ((UNIV::real set) \<times> (UNIV::real set))
          (product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set))
          (UNIV::real set) (top1_open_sets::real set set) pi1"
        by (rule top1_continuous_pi1[OF hTOS_R hTOS_R])
      hence "top1_continuous_map_on (UNIV::(real\<times>real) set) ?TR2 (UNIV::real set) ?TOR pi1"
        unfolding hTR_eq by (by100 simp)
      moreover have "pi1 = (fst :: real\<times>real \<Rightarrow> real)" unfolding pi1_def by (rule ext) (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    have hsnd_cont: "top1_continuous_map_on (UNIV::(real\<times>real) set) ?TR2 (UNIV::real set) ?TOR snd"
    proof -
      have hTOS_R: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
        by (rule top1_open_sets_is_topology_on_UNIV)
      have "top1_continuous_map_on ((UNIV::real set) \<times> (UNIV::real set))
          (product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set))
          (UNIV::real set) (top1_open_sets::real set set) pi2"
        by (rule top1_continuous_pi2[OF hTOS_R hTOS_R])
      hence "top1_continuous_map_on (UNIV::(real\<times>real) set) ?TR2 (UNIV::real set) ?TOR pi2"
        unfolding hTR_eq by (by100 simp)
      moreover have "pi2 = (snd :: real\<times>real \<Rightarrow> real)" unfolding pi2_def by (rule ext) (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Fe continuous S \<rightarrow> Y (proved). Compose with fst/snd projections.\<close>
    have hFe_cont_Y: "top1_continuous_map_on ?S
        (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?S)
        (UNIV::(real\<times>real) set) ?TR2 Fe"
    proof -
      have hY_sub: "Y \<subseteq> (UNIV::(real\<times>real) set)" by (by100 simp)
      have "top1_continuous_map_on ?S
          (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?S)
          (UNIV::(real\<times>real) set) (subspace_topology (UNIV::(real\<times>real) set) ?TR2 (UNIV::(real\<times>real) set)) Fe"
        using top1_continuous_map_on_codomain_enlarge[OF hFe_cont] by (by100 simp)
      thus ?thesis unfolding subspace_topology_UNIV_self .
    qed
    have hFe1: "top1_continuous_map_on ?S (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?S)
        (UNIV::real set) ?TOR (fst \<circ> Fe)"
      by (rule top1_continuous_map_on_comp[OF hFe_cont_Y hfst_cont])
    have hFe2: "top1_continuous_map_on ?S (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?S)
        (UNIV::real set) ?TOR (snd \<circ> Fe)"
      by (rule top1_continuous_map_on_comp[OF hFe_cont_Y hsnd_cont])
    \<comment> \<open>Apply Theorem_35_1_R to each coordinate.\<close>
    obtain G1 where hG1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
        (UNIV::real set) ?TOR G1" and hG1_ext: "\<forall>p\<in>?S. G1 p = fst (Fe p)"
    proof -
      from Theorem_35_1_R[OF hXI_normal hS_closed hFe1]
      obtain F1 where "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) UNIV ?TOR F1"
          "\<forall>p\<in>?S. F1 p = (fst \<circ> Fe) p" by (by100 blast)
      thus ?thesis using that unfolding comp_def by (by100 blast)
    qed
    obtain G2 where hG2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
        (UNIV::real set) ?TOR G2" and hG2_ext: "\<forall>p\<in>?S. G2 p = snd (Fe p)"
    proof -
      from Theorem_35_1_R[OF hXI_normal hS_closed hFe2]
      obtain F2 where "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) UNIV ?TOR F2"
          "\<forall>p\<in>?S. F2 p = (snd \<circ> Fe) p" by (by100 blast)
      thus ?thesis using that unfolding comp_def by (by100 blast)
    qed
    \<comment> \<open>Combine G = (G1, G2) via Theorem_18_4.\<close>
    define G where "G = (\<lambda>p. (G1 p, G2 p))"
    have hG_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::(real\<times>real) set) ?TR2 G"
    proof -
      have hpi1_G: "pi1 \<circ> G = G1" unfolding G_def pi1_def by (rule ext) (by100 simp)
      have hpi2_G: "pi2 \<circ> G = G2" unfolding G_def pi2_def by (rule ext) (by100 simp)
      have hG1': "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
          (UNIV::real set) top1_open_sets G1" using hG1 unfolding hTR_eq .
      have hG2': "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
          (UNIV::real set) top1_open_sets G2" using hG2 unfolding hTR_eq .
      have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
          (UNIV::real set) top1_open_sets (pi1 \<circ> G)" unfolding hpi1_G by (rule hG1')
      moreover have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
          (UNIV::real set) top1_open_sets (pi2 \<circ> G)" unfolding hpi2_G by (rule hG2')
      ultimately have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
          ((UNIV::real set) \<times> (UNIV::real set)) (product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set)) G"
      proof -
        have hTOS: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
          by (rule top1_open_sets_is_topology_on_UNIV)
        assume h1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) (top1_open_sets::real set set) (pi1 \<circ> G)"
        assume h2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) (top1_open_sets::real set set) (pi2 \<circ> G)"
        show ?thesis using iffD2[OF Theorem_18_4[OF hTXI hTOS hTOS]] h1 h2 by (by100 blast)
      qed
      thus ?thesis by (by100 simp)
    qed
    have hG_ext: "\<forall>p\<in>?S. G p = Fe p"
    proof (intro ballI)
      fix p assume "p \<in> ?S"
      have "G p = (G1 p, G2 p)" unfolding G_def by (by100 simp)
      also have "G1 p = fst (Fe p)" using hG1_ext \<open>p \<in> ?S\<close> by (by100 blast)
      also have "G2 p = snd (Fe p)" using hG2_ext \<open>p \<in> ?S\<close> by (by100 blast)
      finally show "G p = Fe p" by (by100 simp)
    qed
    show ?thesis using hG_cont hG_ext by (rule that)
  qed
  \<comment> \<open>Step 4: U = G^{-1}(Y) is open in X\<times>I, contains ?S.\<close>
  let ?U_pre = "{p \<in> X \<times> I_set. G p \<in> Y}"
  have hU_open: "?U_pre \<in> product_topology_on TX I_top"
    using hG_cont hY_open unfolding top1_continuous_map_on_def by (by100 blast)
  have hU_contains: "?S \<subseteq> ?U_pre"
  proof
    fix p assume "p \<in> ?S"
    have "p \<in> X \<times> I_set"
      using \<open>p \<in> ?S\<close> hAX unfolding top1_unit_interval_def by (by100 auto)
    moreover have "G p \<in> Y"
    proof -
      have "G p = Fe p" using hG_ext \<open>p \<in> ?S\<close> by (by100 blast)
      moreover have "Fe p \<in> Y" using hFe_range \<open>p \<in> ?S\<close> by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    ultimately show "p \<in> ?U_pre" by (by100 blast)
  qed
  \<comment> \<open>Step 5: Tube lemma: I_set compact, ?S \<supseteq> A\<times>I, U open containing A\<times>I.
     So \<exists>W open in X with A \<subseteq> W and W\<times>I \<subseteq> U.\<close>
  obtain W where hW_open: "W \<in> TX" and hA_W: "A \<subseteq> W"
      and hW_sub: "W \<subseteq> X" and hWI_U: "W \<times> I_set \<subseteq> ?U_pre"
  proof -
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hI_comp: "top1_compact_on I_set I_top"
    proof -
      have hI_01: "I_set = {0..1::real}" unfolding top1_unit_interval_def by (by100 auto)
      have "compact ({0..1} :: real set)" by (rule compact_Icc)
      hence "compact I_set" unfolding hI_01 .
      hence "top1_compact_on I_set (subspace_topology UNIV top1_open_sets I_set)"
        using top1_compact_on_subspace_UNIV_iff_compact by (by100 blast)
      thus ?thesis unfolding top1_unit_interval_topology_def .
    qed
    \<comment> \<open>For each a \<in> A: {a}\<times>I \<subseteq> ?U_pre (since A\<times>I \<subseteq> ?S \<subseteq> ?U_pre).
       By tube lemma: \<exists>Wa neighborhood of a with Wa\<times>I \<subseteq> ?U_pre.\<close>
    have "\<forall>a\<in>A. \<exists>Wa. Wa \<in> TX \<and> a \<in> Wa \<and> Wa \<times> I_set \<subseteq> ?U_pre"
    proof (intro ballI)
      fix a assume ha: "a \<in> A"
      have "{a} \<times> I_set \<subseteq> ?U_pre"
      proof
        fix p assume "p \<in> {a} \<times> I_set"
        hence "p \<in> A \<times> I_set" using ha by (by100 blast)
        hence "p \<in> ?S" by (by100 blast)
        thus "p \<in> ?U_pre" using hU_contains by (by100 blast)
      qed
      have "a \<in> X" using ha hAX by (by100 blast)
      obtain Wa where hWa: "neighborhood_of a X TX Wa" and hWaI: "Wa \<times> I_set \<subseteq> ?U_pre"
        using Lemma_26_8[OF hI_comp hTX hTI hU_open \<open>a \<in> X\<close> \<open>{a} \<times> I_set \<subseteq> ?U_pre\<close>]
        by (by100 blast)
      obtain U_a where hUa: "U_a \<in> TX" and ha_Ua: "a \<in> U_a" and hUa_Wa: "U_a \<subseteq> Wa"
        using hWa unfolding neighborhood_of_def by (by100 blast)
      have "U_a \<times> I_set \<subseteq> ?U_pre" using hUa_Wa hWaI by (by100 blast)
      thus "\<exists>Wa. Wa \<in> TX \<and> a \<in> Wa \<and> Wa \<times> I_set \<subseteq> ?U_pre"
        using hUa ha_Ua by (by100 blast)
    qed
    \<comment> \<open>W = \<Union>{Wa | a \<in> A} is open, contains A, and W\<times>I \<subseteq> U.\<close>
    define W where "W = \<Union>{Wa. \<exists>a\<in>A. Wa \<in> TX \<and> a \<in> Wa \<and> Wa \<times> I_set \<subseteq> ?U_pre}"
    have "W \<in> TX"
    proof -
      have "{Wa. \<exists>a\<in>A. Wa \<in> TX \<and> a \<in> Wa \<and> Wa \<times> I_set \<subseteq> ?U_pre} \<subseteq> TX"
        by (by100 blast)
      thus ?thesis using hTX unfolding is_topology_on_def W_def by (by100 blast)
    qed
    moreover have "A \<subseteq> W"
      using \<open>\<forall>a\<in>A. \<exists>Wa. Wa \<in> TX \<and> a \<in> Wa \<and> Wa \<times> I_set \<subseteq> ?U_pre\<close>
      unfolding W_def by (by100 blast)
    moreover have hWI: "W \<times> I_set \<subseteq> ?U_pre"
      unfolding W_def by (by100 blast)
    moreover have "W \<subseteq> X"
    proof -
      have "W \<times> I_set \<subseteq> X \<times> I_set" using hWI by (by100 blast)
      moreover have "I_set \<noteq> {}" unfolding top1_unit_interval_def by (by100 auto)
      ultimately show ?thesis by (by100 blast)
    qed
    ultimately show ?thesis using that by (by100 blast)
  qed
  \<comment> \<open>Step 6: Urysohn: \<phi>: X \<rightarrow> [0,1] with \<phi>|A = 0, \<phi>|X-W = 1.\<close>
  note hX_normal_loc = hX_normal
  have hXW_closed: "closedin_on X TX (X - W)"
  proof (rule closedin_intro)
    show "X - W \<subseteq> X" by (by100 blast)
    show "X - (X - W) \<in> TX"
    proof -
      have "X - (X - W) = X \<inter> W" by (by100 blast)
      also have "... = W" using hW_sub by (by100 blast)
      finally show ?thesis using hW_open by (by100 simp)
    qed
  qed
  have hA_XW_disj: "A \<inter> (X - W) = {}" using hA_W by (by100 blast)
  obtain \<phi> where h\<phi>: "top1_continuous_map_on X TX
      (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) \<phi>"
      and h\<phi>A: "\<forall>x\<in>A. \<phi> x = 0" and h\<phi>XW: "\<forall>x\<in>X-W. \<phi> x = 1"
    using Theorem_33_1[OF hX_normal hA_closed hXW_closed hA_XW_disj zero_le_one]
    by (by100 blast)
  \<comment> \<open>Step 7: g(x) = G(x, \<phi>(x)). Maps X to Y (since (x,\<phi>(x)) \<in> ?U_pre).
     Extends f (since \<phi>(a)=0, G(a,0)=Fe(a,0)=F(a,0)=f(a)).
     Nulhomotopic via H(x,t) = G(x, (1-t)\<phi>(x)+t).\<close>
  define g where "g x = G (x, \<phi> x)" for x
  \<comment> \<open>g extends f: for a \<in> A, \<phi>(a) = 0, G(a,0) = Fe(a,0) = F(a,0) = f(a).\<close>
  have hg_ext: "\<forall>x\<in>A. g x = f x"
  proof (intro ballI)
    fix a assume ha: "a \<in> A"
    have "\<phi> a = 0" using h\<phi>A ha by (by100 blast)
    have "g a = G (a, 0)" unfolding g_def using \<open>\<phi> a = 0\<close> by (by100 simp)
    also have "... = Fe (a, 0)" using hG_ext ha hAX
    proof -
      have "(a, 0::real) \<in> ?S"
      proof -
        have "a \<in> A" by (rule ha)
        moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        ultimately show ?thesis by (by100 blast)
      qed
      thus ?thesis using hG_ext by (by100 blast)
    qed
    also have "... = F (a, 0)" unfolding Fe_def using ha by (by100 simp)
    also have "... = f a" using hF0 ha by (by100 blast)
    finally show "g a = f a" .
  qed
  \<comment> \<open>g maps X to Y: for x \<in> X, (x, \<phi>(x)) \<in> ?U_pre, so G(x,\<phi>(x)) \<in> Y.\<close>
  have hg_range: "\<forall>x\<in>X. g x \<in> Y"
  proof (intro ballI)
    fix x assume hx: "x \<in> X"
    have h\<phi>_01: "\<phi> x \<in> top1_closed_interval 0 1"
      using h\<phi> hx unfolding top1_continuous_map_on_def by (by100 blast)
    hence h\<phi>_I: "\<phi> x \<in> I_set"
      unfolding top1_closed_interval_def top1_unit_interval_def by (by100 auto)
    \<comment> \<open>If x \<in> W: (x, \<phi>(x)) \<in> W\<times>I \<subseteq> ?U_pre.\<close>
    \<comment> \<open>If x \<notin> W: \<phi>(x) = 1, so (x, 1) \<in> X\<times>{1} \<subseteq> ?S \<subseteq> ?U_pre.\<close>
    have "(x, \<phi> x) \<in> ?U_pre"
    proof (cases "x \<in> W")
      case True
      hence "(x, \<phi> x) \<in> W \<times> I_set" using h\<phi>_I by (by100 blast)
      thus ?thesis using hWI_U by (by100 blast)
    next
      case False
      hence "x \<in> X - W" using hx by (by100 blast)
      hence "\<phi> x = 1" using h\<phi>XW by (by100 blast)
      hence "(x, \<phi> x) = (x, 1::real)" by (by100 simp)
      moreover have "(x, 1::real) \<in> ?S" using hx by (by100 blast)
      ultimately show ?thesis using hU_contains by (by100 blast)
    qed
    thus "g x \<in> Y" unfolding g_def by (by100 blast)
  qed
  \<comment> \<open>g continuous: composition of G: X\<times>I \<rightarrow> R^2 with (x \<mapsto> (x,\<phi>(x))): X \<rightarrow> X\<times>I.\<close>
  have hg_cont: "top1_continuous_map_on X TX Y ?TY g"
  proof -
    \<comment> \<open>The map x \<mapsto> (x, \<phi> x) : X \<rightarrow> X \<times> I is continuous (Theorem 18.4 + identity + \<phi>).\<close>
    \<comment> \<open>Bridge \<phi> from closed_interval_topology to I_top.\<close>
    have h\<phi>_I: "top1_continuous_map_on X TX I_set I_top \<phi>"
      by (rule continuous_closed_interval_imp_I_top[OF h\<phi>])
    have hpair_cont: "top1_continuous_map_on X TX (X \<times> I_set) (product_topology_on TX I_top)
        (\<lambda>x. (x, \<phi> x))"
    proof -
      have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
      have hid: "top1_continuous_map_on X TX X TX id" by (rule top1_continuous_map_on_id[OF hTX])
      have hpi1: "pi1 \<circ> (\<lambda>x. (x, \<phi> x)) = id" unfolding pi1_def by (rule ext) (by100 simp)
      have hpi2: "pi2 \<circ> (\<lambda>x. (x, \<phi> x)) = \<phi>" unfolding pi2_def by (rule ext) (by100 simp)
      have "top1_continuous_map_on X TX X TX (pi1 \<circ> (\<lambda>x. (x, \<phi> x)))"
        unfolding hpi1 by (rule hid)
      moreover have "top1_continuous_map_on X TX I_set I_top (pi2 \<circ> (\<lambda>x. (x, \<phi> x)))"
        unfolding hpi2 by (rule h\<phi>_I)
      ultimately show ?thesis using iffD2[OF Theorem_18_4[OF hTX hTX hTI]]
        by (by100 blast)
    qed
    \<comment> \<open>g = G \<circ> (x \<mapsto> (x, \<phi>(x))): composition of continuous maps.\<close>
    have hcomp: "top1_continuous_map_on X TX UNIV ?TR2 (G \<circ> (\<lambda>x. (x, \<phi> x)))"
      by (rule top1_continuous_map_on_comp[OF hpair_cont hG_cont])
    have hg_eq: "\<And>x. x \<in> X \<Longrightarrow> g x = (G \<circ> (\<lambda>x. (x, \<phi> x))) x"
      unfolding g_def comp_def by (by100 simp)
    \<comment> \<open>g continuous X \<rightarrow> R^2, then restrict codomain to Y.\<close>
    have hg_R2: "top1_continuous_map_on X TX UNIV ?TR2 g"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x assume "x \<in> X" show "g x \<in> (UNIV :: (real\<times>real) set)" by (by100 simp)
    next
      fix V assume hV: "V \<in> ?TR2"
      have "{x \<in> X. g x \<in> V} = {x \<in> X. (G \<circ> (\<lambda>x. (x, \<phi> x))) x \<in> V}"
        using hg_eq by (by100 auto)
      moreover have "{x \<in> X. (G \<circ> (\<lambda>x. (x, \<phi> x))) x \<in> V} \<in> TX"
        using hcomp hV unfolding top1_continuous_map_on_def by (by100 blast)
      ultimately show "{x \<in> X. g x \<in> V} \<in> TX" by (by100 simp)
    qed
    have hg_img: "g ` X \<subseteq> Y"
      using hg_range by (by100 blast)
    have hY_sub: "Y \<subseteq> (UNIV :: (real\<times>real) set)" by (by100 simp)
    show ?thesis
      by (rule top1_continuous_map_on_codomain_shrink[OF hg_R2 hg_img hY_sub])
  qed
  \<comment> \<open>g nulhomotopic: H(x,t) = G(x, (1-t)\<phi>(x) + t) is homotopy from g to const y0.
     H(x,0) = G(x, \<phi>(x)) = g(x). H(x,1) = G(x, 1) = Fe(x,1) = y0.\<close>
  have hg_nul: "top1_nulhomotopic_on X TX Y ?TY g"
  proof -
    \<comment> \<open>H(x,t) = G(x, (1-t)\<phi>(x)+t). Homotopy from g to const y0.\<close>
    define H where "H = (\<lambda>(x::'a, t::real). G (x, (1-t) * \<phi> x + t))"
    have hH0: "\<forall>x\<in>X. H (x, 0) = g x" unfolding H_def g_def by (by100 simp)
    have hH1: "\<forall>x\<in>X. H (x, 1) = y0"
    proof (intro ballI)
      fix x assume hx: "x \<in> X"
      have "H (x, 1) = G (x, 1)" unfolding H_def by (by100 simp)
      also have "... = Fe (x, 1)"
      proof -
        have "(x, 1::real) \<in> ?S" using hx by (by100 blast)
        thus ?thesis using hG_ext by (by100 blast)
      qed
      also have "... = y0" using hFe_X1 hx by (by100 blast)
      finally show "H (x, 1) = y0" .
    qed
    \<comment> \<open>H maps X\<times>I to Y (range check).\<close>
    have hH_range: "\<forall>p\<in>X \<times> I_set. H p \<in> Y"
    proof (intro ballI)
      fix p assume hp: "p \<in> X \<times> I_set"
      obtain x t where hxt: "p = (x, t)" "x \<in> X" "t \<in> I_set" using hp by (by100 blast)
      have ht01: "0 \<le> t" "t \<le> 1" using hxt(3) unfolding top1_unit_interval_def by (by100 auto)+
      have "\<phi> x \<in> top1_closed_interval 0 1"
        using h\<phi> hxt(2) unfolding top1_continuous_map_on_def by (by100 blast)
      hence h\<phi>01: "0 \<le> \<phi> x" "\<phi> x \<le> 1"
        unfolding top1_closed_interval_def by (by100 blast)+
      have hs_I: "(1-t) * \<phi> x + t \<in> I_set"
      proof -
        have "0 \<le> (1-t) * \<phi> x" using ht01 h\<phi>01 by (intro mult_nonneg_nonneg) (by100 linarith)+
        hence "0 \<le> (1-t) * \<phi> x + t" using ht01 by (by100 linarith)
        moreover have "(1-t) * \<phi> x + t \<le> 1"
        proof -
          have "1 - t \<ge> 0" using ht01 by (by100 linarith)
          have "(1-t) * \<phi> x \<le> (1-t)"
          proof -
            have "(1-t) * \<phi> x \<le> (1-t) * 1"
              using h\<phi>01 \<open>1-t \<ge> 0\<close> by (intro mult_left_mono) (by100 linarith)+
            thus ?thesis by (by100 simp)
          qed
          thus ?thesis by (by100 linarith)
        qed
        ultimately show ?thesis unfolding top1_unit_interval_def by (by100 auto)
      qed
      have "(x, (1-t) * \<phi> x + t) \<in> ?U_pre"
      proof (cases "x \<in> W")
        case True thus ?thesis using hWI_U hs_I by (by100 blast)
      next
        case False hence "\<phi> x = 1" using h\<phi>XW hxt(2) by (by100 blast)
        hence "(1-t) * \<phi> x + t = 1" by (by100 simp)
        hence "(x, (1-t) * \<phi> x + t) = (x, 1::real)" by (by100 simp)
        moreover have "(x, 1::real) \<in> ?S" using hxt(2) by (by100 blast)
        ultimately show ?thesis using hU_contains by (by100 blast)
      qed
      have "H p = G (x, (1-t) * \<phi> x + t)" unfolding H_def hxt(1) by (by100 simp)
      moreover have "G (x, (1-t) * \<phi> x + t) \<in> Y"
        using \<open>(x, (1-t) * \<phi> x + t) \<in> ?U_pre\<close> by (by100 blast)
      ultimately show "H p \<in> Y" by (by100 simp)
    qed
    \<comment> \<open>H continuous: composition.\<close>
    have hH_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y ?TY H"
    proof -
      \<comment> \<open>\<psi>(x,t) = (x, (1-t)\<phi>(x)+t) : X\<times>I \<rightarrow> X\<times>I continuous.\<close>
      let ?\<psi> = "\<lambda>(x::'a, t::real). (x, (1-t) * \<phi> x + t)"
      have h\<psi>_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
          (X \<times> I_set) (product_topology_on TX I_top) ?\<psi>"
      proof -
        have hTXI: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
          by (rule product_topology_on_is_topology_on[OF hTX top1_unit_interval_topology_is_topology_on])
        have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
        \<comment> \<open>\<pi>1 \<circ> \<psi> = \<pi>1: continuous.\<close>
        have hpi1_\<psi>: "pi1 \<circ> ?\<psi> = pi1"
        proof (rule ext)
          fix p show "(pi1 \<circ> ?\<psi>) p = pi1 p"
            unfolding pi1_def comp_def by (cases p) (by100 simp)
        qed
        have hpi1_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX pi1"
          by (rule top1_continuous_pi1[OF hTX_top hTI])
        \<comment> \<open>\<pi>2 \<circ> \<psi>(x,t) = (1-t)\<phi>(x)+t: continuous X\<times>I \<rightarrow> I.\<close>
        have hpi2_\<psi>: "pi2 \<circ> ?\<psi> = (\<lambda>(x,t). (1-t) * \<phi> x + t)"
        proof (rule ext)
          fix p show "(pi2 \<circ> ?\<psi>) p = (\<lambda>(x,t). (1-t) * \<phi> x + t) p"
            unfolding pi2_def comp_def by (cases p) (by100 simp)
        qed
        have hpi2_\<psi>_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top
            (\<lambda>(x,t). (1-t) * \<phi> x + t)"
        proof -
          \<comment> \<open>Key bridge: order_topology_on_UNIV = top1_open_sets for reals.\<close>
          have hTR_eq: "(order_topology_on_UNIV :: real set set) = top1_open_sets"
          proof (rule set_eqI)
            fix U :: "real set"
            show "U \<in> order_topology_on_UNIV \<longleftrightarrow> U \<in> top1_open_sets"
              using order_topology_on_UNIV_eq_HOL_open unfolding top1_open_sets_def
              by (by100 simp)
          qed
          let ?TR = "top1_open_sets :: real set set"
          let ?TRR = "product_topology_on ?TR ?TR :: (real \<times> real) set set"
          have hTR: "is_topology_on (UNIV::real set) ?TR"
            by (rule top1_open_sets_is_topology_on_UNIV)
          have hTRR: "is_topology_on ((UNIV::real set) \<times> (UNIV::real set)) ?TRR"
            by (rule product_topology_on_is_topology_on[OF hTR hTR])
          \<comment> \<open>Arithmetic ops continuous on R\<times>R (Lemma 21.4).\<close>
          have cont_add: "top1_continuous_map_on (UNIV \<times> UNIV) ?TRR UNIV ?TR (\<lambda>p::real\<times>real. pi1 p + pi2 p)"
            using Lemma_21_4(1) unfolding hTR_eq[symmetric] by (by100 simp)
          have cont_mul: "top1_continuous_map_on (UNIV \<times> UNIV) ?TRR UNIV ?TR (\<lambda>p::real\<times>real. pi1 p * pi2 p)"
            using Lemma_21_4(3) unfolding hTR_eq[symmetric] by (by100 simp)
          have cont_sub: "top1_continuous_map_on (UNIV \<times> UNIV) ?TRR UNIV ?TR (\<lambda>p::real\<times>real. pi1 p - pi2 p)"
            using Lemma_21_4(2) unfolding hTR_eq[symmetric] by (by100 simp)
          \<comment> \<open>I_top = subspace_topology UNIV top1_open_sets I_set.\<close>
          have hItop_eq: "I_top = subspace_topology (UNIV::real set) ?TR I_set"
            unfolding top1_unit_interval_topology_def top1_unit_interval_def by (by100 simp)
          \<comment> \<open>\<phi> continuous X \<rightarrow> I.\<close>
          have h\<phi>_I: "top1_continuous_map_on X TX I_set I_top \<phi>"
            by (rule continuous_closed_interval_imp_I_top[OF h\<phi>])
          \<comment> \<open>\<phi>\<circ>\<pi>1 continuous X\<times>I \<rightarrow> I.\<close>
          have h\<phi>_pi1_I: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top (\<phi> \<circ> pi1)"
            by (rule top1_continuous_map_on_comp[OF hpi1_cont h\<phi>_I])
          \<comment> \<open>Enlarge codomain of \<phi>\<circ>\<pi>1 from I_set to UNIV.\<close>
          have h\<phi>_pi1_R: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) ?TR (\<phi> \<circ> pi1)"
          proof -
            have h1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set (subspace_topology UNIV ?TR I_set) (\<phi> \<circ> pi1)"
              using h\<phi>_pi1_I unfolding hItop_eq .
            have h2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) (subspace_topology UNIV ?TR UNIV) (\<phi> \<circ> pi1)"
              using top1_continuous_map_on_codomain_enlarge[OF h1] by (by100 simp)
            thus ?thesis unfolding subspace_topology_UNIV_self .
          qed
          \<comment> \<open>\<pi>2 continuous X\<times>I \<rightarrow> I, then enlarge to UNIV.\<close>
          have hpi2_I: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top pi2"
            by (rule top1_continuous_pi2[OF hTX_top hTI])
          have hpi2_R: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) ?TR pi2"
          proof -
            have h1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set (subspace_topology UNIV ?TR I_set) pi2"
              using hpi2_I unfolding hItop_eq .
            have h2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) (subspace_topology UNIV ?TR UNIV) pi2"
              using top1_continuous_map_on_codomain_enlarge[OF h1] by (by100 simp)
            thus ?thesis unfolding subspace_topology_UNIV_self .
          qed
          \<comment> \<open>Pair (\<phi>\<circ>\<pi>1, \<pi>2) continuous X\<times>I \<rightarrow> R\<times>R.\<close>
          have hpair1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
              ((UNIV::real set) \<times> (UNIV::real set)) ?TRR (\<lambda>p. (\<phi> (pi1 p), pi2 p))"
          proof -
            have hpi1_pair: "pi1 \<circ> (\<lambda>p. (\<phi> (pi1 p), pi2 p)) = (\<phi> \<circ> pi1)"
              unfolding pi1_def by (rule ext) (by100 simp)
            have hpi2_pair: "pi2 \<circ> (\<lambda>p. (\<phi> (pi1 p), pi2 p)) = pi2"
              unfolding pi2_def by (rule ext) (by100 simp)
            have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) ?TR (pi1 \<circ> (\<lambda>p. (\<phi> (pi1 p), pi2 p)))"
              unfolding hpi1_pair by (rule h\<phi>_pi1_R)
            moreover have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) ?TR (pi2 \<circ> (\<lambda>p. (\<phi> (pi1 p), pi2 p)))"
              unfolding hpi2_pair by (rule hpi2_R)
            ultimately show ?thesis using iffD2[OF Theorem_18_4[OF hTXI hTR hTR]] by (by100 blast)
          qed
          \<comment> \<open>Compose with mult: \<phi>(x)*t continuous X\<times>I \<rightarrow> R.\<close>
          have h\<phi>t: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) ?TR
              (\<lambda>p. \<phi> (pi1 p) * pi2 p)"
          proof -
            have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) ?TR
                ((\<lambda>p. pi1 p * pi2 p) \<circ> (\<lambda>p. (\<phi> (pi1 p), pi2 p)))"
              by (rule top1_continuous_map_on_comp[OF hpair1 cont_mul])
            moreover have "(\<lambda>p. pi1 p * pi2 p) \<circ> (\<lambda>p. (\<phi> (pi1 p), pi2 p)) = (\<lambda>p. \<phi> (pi1 p) * pi2 p)"
              unfolding pi1_def pi2_def by (rule ext) (by100 simp)
            ultimately show ?thesis by (by100 simp)
          qed
          \<comment> \<open>Pair (\<phi>\<circ>\<pi>1, \<phi>*\<pi>2) and subtract: \<phi>(x) - \<phi>(x)*t = (1-t)*\<phi>(x).\<close>
          have hpair2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
              ((UNIV::real set) \<times> (UNIV::real set)) ?TRR (\<lambda>p. (\<phi> (pi1 p), \<phi> (pi1 p) * pi2 p))"
          proof -
            have hpi1_p: "pi1 \<circ> (\<lambda>p. (\<phi> (pi1 p), \<phi> (pi1 p) * pi2 p)) = (\<phi> \<circ> pi1)"
              unfolding pi1_def by (rule ext) (by100 simp)
            have hpi2_p: "pi2 \<circ> (\<lambda>p. (\<phi> (pi1 p), \<phi> (pi1 p) * pi2 p)) = (\<lambda>p. \<phi> (pi1 p) * pi2 p)"
              unfolding pi2_def by (rule ext) (by100 simp)
            have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) ?TR (pi1 \<circ> (\<lambda>p. (\<phi> (pi1 p), \<phi> (pi1 p) * pi2 p)))"
              unfolding hpi1_p by (rule h\<phi>_pi1_R)
            moreover have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) ?TR (pi2 \<circ> (\<lambda>p. (\<phi> (pi1 p), \<phi> (pi1 p) * pi2 p)))"
              unfolding hpi2_p by (rule h\<phi>t)
            ultimately show ?thesis using iffD2[OF Theorem_18_4[OF hTXI hTR hTR]] by (by100 blast)
          qed
          have h1t\<phi>: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) ?TR
              (\<lambda>p. \<phi> (pi1 p) - \<phi> (pi1 p) * pi2 p)"
          proof -
            have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) ?TR
                ((\<lambda>p. pi1 p - pi2 p) \<circ> (\<lambda>p. (\<phi> (pi1 p), \<phi> (pi1 p) * pi2 p)))"
              by (rule top1_continuous_map_on_comp[OF hpair2 cont_sub])
            moreover have "(\<lambda>p. pi1 p - pi2 p) \<circ> (\<lambda>p. (\<phi> (pi1 p), \<phi> (pi1 p) * pi2 p)) = (\<lambda>p. \<phi> (pi1 p) - \<phi> (pi1 p) * pi2 p)"
              unfolding pi1_def pi2_def by (rule ext) (by100 simp)
            ultimately show ?thesis by (by100 simp)
          qed
          \<comment> \<open>Pair ((1-t)*\<phi>(x), t) and add.\<close>
          have hpair3: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
              ((UNIV::real set) \<times> (UNIV::real set)) ?TRR (\<lambda>p. (\<phi> (pi1 p) - \<phi> (pi1 p) * pi2 p, pi2 p))"
          proof -
            have hpi1_p: "pi1 \<circ> (\<lambda>p. (\<phi> (pi1 p) - \<phi> (pi1 p) * pi2 p, pi2 p)) = (\<lambda>p. \<phi> (pi1 p) - \<phi> (pi1 p) * pi2 p)"
              unfolding pi1_def by (rule ext) (by100 simp)
            have hpi2_p: "pi2 \<circ> (\<lambda>p. (\<phi> (pi1 p) - \<phi> (pi1 p) * pi2 p, pi2 p)) = pi2"
              unfolding pi2_def by (rule ext) (by100 simp)
            have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) ?TR (pi1 \<circ> (\<lambda>p. (\<phi> (pi1 p) - \<phi> (pi1 p) * pi2 p, pi2 p)))"
              unfolding hpi1_p by (rule h1t\<phi>)
            moreover have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) ?TR (pi2 \<circ> (\<lambda>p. (\<phi> (pi1 p) - \<phi> (pi1 p) * pi2 p, pi2 p)))"
              unfolding hpi2_p by (rule hpi2_R)
            ultimately show ?thesis using iffD2[OF Theorem_18_4[OF hTXI hTR hTR]] by (by100 blast)
          qed
          have hresult_R: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) ?TR
              (\<lambda>p. (\<phi> (pi1 p) - \<phi> (pi1 p) * pi2 p) + pi2 p)"
          proof -
            have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) ?TR
                ((\<lambda>p. pi1 p + pi2 p) \<circ> (\<lambda>p. (\<phi> (pi1 p) - \<phi> (pi1 p) * pi2 p, pi2 p)))"
              by (rule top1_continuous_map_on_comp[OF hpair3 cont_add])
            moreover have "(\<lambda>p. pi1 p + pi2 p) \<circ> (\<lambda>p. (\<phi> (pi1 p) - \<phi> (pi1 p) * pi2 p, pi2 p)) = (\<lambda>p. (\<phi> (pi1 p) - \<phi> (pi1 p) * pi2 p) + pi2 p)"
              unfolding pi1_def pi2_def by (rule ext) (by100 simp)
            ultimately show ?thesis by (by100 simp)
          qed
          \<comment> \<open>Rewrite: \<phi>(x) - \<phi>(x)*t + t = (1-t)*\<phi>(x) + t.\<close>
          have hfun_eq: "\<And>p. p \<in> X \<times> I_set \<Longrightarrow> (\<phi> (pi1 p) - \<phi> (pi1 p) * pi2 p) + pi2 p = (case p of (x,t) \<Rightarrow> (1-t) * \<phi> x + t)"
          proof -
            fix p assume "p \<in> X \<times> I_set"
            obtain x t where hp: "p = (x, t)" by (cases p)
            have halg: "\<phi> x - \<phi> x * t = (1 - t) * \<phi> x"
              using left_diff_distrib[of 1 t "\<phi> x"] by (by100 simp)
            show "(\<phi> (pi1 p) - \<phi> (pi1 p) * pi2 p) + pi2 p = (case p of (x,t) \<Rightarrow> (1-t) * \<phi> x + t)"
              unfolding hp pi1_def pi2_def using halg by (by100 simp)
          qed
          \<comment> \<open>Transfer continuity to our target function.\<close>
          have hresult_R': "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) (UNIV::real set) ?TR
              (\<lambda>(x,t). (1-t) * \<phi> x + t)"
            unfolding top1_continuous_map_on_def
          proof (intro conjI ballI)
            fix p assume "p \<in> X \<times> I_set" show "(case p of (x,t) \<Rightarrow> (1-t) * \<phi> x + t) \<in> (UNIV::real set)" by (by100 simp)
          next
            fix V assume hV: "V \<in> ?TR"
            have "{p \<in> X \<times> I_set. (case p of (x,t) \<Rightarrow> (1-t) * \<phi> x + t) \<in> V} =
                  {p \<in> X \<times> I_set. (\<phi> (pi1 p) - \<phi> (pi1 p) * pi2 p) + pi2 p \<in> V}"
              using hfun_eq by (by100 auto)
            moreover have "{p \<in> X \<times> I_set. (\<phi> (pi1 p) - \<phi> (pi1 p) * pi2 p) + pi2 p \<in> V} \<in> product_topology_on TX I_top"
              using hresult_R hV unfolding top1_continuous_map_on_def by (by100 blast)
            ultimately show "{p \<in> X \<times> I_set. (case p of (x,t) \<Rightarrow> (1-t) * \<phi> x + t) \<in> V} \<in> product_topology_on TX I_top"
              by (by100 simp)
          qed
          \<comment> \<open>Range: (1-t)*\<phi>(x)+t \<in> I_set for x \<in> X, t \<in> I_set.\<close>
          have hrange: "(\<lambda>(x,t). (1-t) * \<phi> x + t) ` (X \<times> I_set) \<subseteq> I_set"
          proof (rule image_subsetI)
            fix p assume "p \<in> X \<times> I_set"
            then obtain x t where hp: "p = (x,t)" and hx: "x \<in> X" and ht: "t \<in> I_set" by (by100 blast)
            have h\<phi>01: "\<phi> x \<in> I_set" using h\<phi>_I hx unfolding top1_continuous_map_on_def by (by100 blast)
            hence h\<phi>0: "0 \<le> \<phi> x" and h\<phi>1: "\<phi> x \<le> 1"
              unfolding top1_unit_interval_def by (by100 simp)+
            have ht0: "0 \<le> t" and ht1: "t \<le> 1"
              using ht unfolding top1_unit_interval_def by (by100 simp)+
            have "(1-t) * \<phi> x + t = (1-t) * \<phi> x + t * 1" by (by100 simp)
            have h1t: "0 \<le> 1 - t" using ht1 by (by100 linarith)
            have h_low: "0 \<le> (1-t) * \<phi> x + t"
            proof -
              have "0 \<le> (1-t) * \<phi> x" using h1t h\<phi>0 by (rule mult_nonneg_nonneg)
              thus ?thesis using ht0 by (by100 linarith)
            qed
            have h_high: "(1-t) * \<phi> x + t \<le> 1"
            proof -
              have "(1-t) * \<phi> x \<le> (1-t) * 1" using h\<phi>1 h1t by (rule mult_left_mono)
              hence "(1-t) * \<phi> x \<le> 1 - t" by (by100 simp)
              thus ?thesis by (by100 linarith)
            qed
            show "(case p of (x,t) \<Rightarrow> (1-t) * \<phi> x + t) \<in> I_set"
              unfolding hp top1_unit_interval_def using h_low h_high by (by100 simp)
          qed
          \<comment> \<open>Shrink codomain from UNIV to I_set with I_top.\<close>
          have hI_sub: "I_set \<subseteq> (UNIV::real set)" by (by100 simp)
          have hI_top_sub: "I_top = subspace_topology (UNIV::real set) ?TR I_set"
            by (rule hItop_eq)
          show ?thesis
            using top1_continuous_map_on_codomain_shrink[OF hresult_R' hrange hI_sub]
            unfolding hI_top_sub[symmetric] .
        qed
        have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX (pi1 \<circ> ?\<psi>)"
          unfolding hpi1_\<psi> by (rule hpi1_cont)
        moreover have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top (pi2 \<circ> ?\<psi>)"
          unfolding hpi2_\<psi> by (rule hpi2_\<psi>_cont)
        ultimately show ?thesis
          using iffD2[OF Theorem_18_4[OF hTXI hTX hTI]] by (by100 blast)
      qed
      \<comment> \<open>H = G \<circ> \<psi>: composition of continuous maps.\<close>
      have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
          UNIV ?TR2 (G \<circ> ?\<psi>)"
        by (rule top1_continuous_map_on_comp[OF h\<psi>_cont hG_cont])
      \<comment> \<open>H = G \<circ> \<psi> pointwise, then restrict codomain to Y.\<close>
      have hH_eq: "\<And>p. p \<in> X \<times> I_set \<Longrightarrow> H p = (G \<circ> ?\<psi>) p"
      proof -
        fix p assume "p \<in> X \<times> I_set"
        obtain x t where hp: "p = (x, t)" by (cases p)
        show "H p = (G \<circ> ?\<psi>) p" unfolding H_def comp_def hp by (by100 simp)
      qed
      hence hH_R2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) UNIV ?TR2 H"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix p assume "p \<in> X \<times> I_set" show "H p \<in> (UNIV :: (real\<times>real) set)" by (by100 simp)
      next
        fix V assume hV: "V \<in> ?TR2"
        have "{p \<in> X \<times> I_set. H p \<in> V} = {p \<in> X \<times> I_set. (G \<circ> ?\<psi>) p \<in> V}"
          using \<open>\<And>p. p \<in> X \<times> I_set \<Longrightarrow> H p = (G \<circ> ?\<psi>) p\<close> by (by100 auto)
        moreover have "{p \<in> X \<times> I_set. (G \<circ> ?\<psi>) p \<in> V} \<in> product_topology_on TX I_top"
          using \<open>top1_continuous_map_on _ _ UNIV ?TR2 (G \<circ> ?\<psi>)\<close> hV
          unfolding top1_continuous_map_on_def by (by100 blast)
        ultimately show "{p \<in> X \<times> I_set. H p \<in> V} \<in> product_topology_on TX I_top"
          by (by100 simp)
      qed
      have hH_img: "H ` (X \<times> I_set) \<subseteq> Y"
        using hH_range by (by100 blast)
      have hY_sub: "Y \<subseteq> (UNIV :: (real\<times>real) set)" by (by100 simp)
      show ?thesis
        by (rule top1_continuous_map_on_codomain_shrink[OF hH_R2 hH_img hY_sub])
    qed
    have "top1_homotopic_on X TX Y ?TY g (\<lambda>_. y0)"
      unfolding top1_homotopic_on_def using hg_cont
    proof (intro conjI exI[of _ H])
      show "top1_continuous_map_on X TX Y ?TY (\<lambda>_. y0)"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix x assume "x \<in> X" show "y0 \<in> Y" by (rule hy0)
      next
        fix V assume "V \<in> ?TY"
        show "{x \<in> X. y0 \<in> V} \<in> TX"
        proof (cases "y0 \<in> V")
          case True hence "{x \<in> X. y0 \<in> V} = X" by (by100 blast)
          moreover have "X \<in> TX"
            using conjunct1[OF conjunct2[OF hTX[unfolded is_topology_on_def]]] .
          ultimately show ?thesis by (by100 simp)
        next
          case False hence heq: "{x \<in> X. y0 \<in> V} = {}" by (by100 blast)
          show ?thesis unfolding heq
            using conjunct1[OF hTX[unfolded is_topology_on_def]] .
        qed
      qed
      show "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y ?TY H"
        by (rule hH_cont)
      show "\<forall>x\<in>X. H (x, 0) = g x" by (rule hH0)
      show "\<forall>x\<in>X. H (x, 1) = y0" by (rule hH1)
    qed
    thus ?thesis unfolding top1_nulhomotopic_on_def using hy0 by (by100 blast)
  qed
  show ?thesis using hg_cont hg_ext hg_nul by (by100 blast)
qed

text \<open>Lemma 62.2 (Borsuk lemma): if f: A \<rightarrow> S^2-{a,b} is continuous, injective, compact domain,
  and nulhomotopic, then a and b lie in the same component of S^2-f(A).\<close>

lemma Lemma_62_2_BorsukLemma:
  fixes A :: "'a set" and TA :: "'a set set" and f :: "'a \<Rightarrow> real \<times> real \<times> real"
    and a b :: "real \<times> real \<times> real"
  assumes hT: "is_topology_on_strict top1_S2 top1_S2_topology"
      and hcomp: "top1_compact_on A TA"
      and ha: "a \<in> top1_S2" and hb: "b \<in> top1_S2" and hab: "a \<noteq> b"
      and hf: "top1_continuous_map_on A TA
             (top1_S2 - {a, b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b})) f"
      and hinj: "inj_on f A"
      and hnul: "top1_nulhomotopic_on A TA
             (top1_S2 - {a, b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b})) f"
  shows "\<exists>C. C \<in> top1_components_on (top1_S2 - f ` A)
         (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A))
         \<and> a \<in> C \<and> b \<in> C"
proof -
  let ?S2 = top1_S2 and ?TS2 = top1_S2_topology
  let ?TR2 = "product_topology_on top1_open_sets top1_open_sets :: (real\<times>real) set set"
  \<comment> \<open>Step 1: Transfer to R^2. Stereographic projection from b gives h: S^2-{b} \<rightarrow> R^2.
     Map a to 0 (the origin). Then the image g = h \<circ> f maps A into R^2-{0}.
     The statement becomes: 0 and \<infinity> are in the same component of S^2-f(A),
     i.e., 0 is in the unbounded component of R^2-g(A).\<close>
  obtain h where hh: "top1_homeomorphism_on (?S2 - {b})
      (subspace_topology ?S2 ?TS2 (?S2 - {b}))
      (UNIV :: (real\<times>real) set) ?TR2 h"
    using S2_minus_point_homeo_R2[OF hb] by (by100 blast)
  \<comment> \<open>Step 2: g = h \<circ> f : A \<rightarrow> R^2. g is continuous, injective, nulhomotopic.
     g(A) \<subseteq> R^2 - {h(a)} since f(A) \<subseteq> S^2 - {a,b} and h maps S^2-{b} to R^2.\<close>
  let ?g = "h \<circ> f"
  let ?origin = "h a"  \<comment> \<open>The image of a under stereographic projection\<close>
  \<comment> \<open>Step 3: g = h \<circ> f maps A into R^2. K = g(A) compact. K \<subseteq> R^2 - {?origin}.\<close>
  have hg_cont: "top1_continuous_map_on A TA (UNIV::(real\<times>real) set) ?TR2 ?g"
  proof -
    \<comment> \<open>h continuous: extract from homeomorphism.\<close>
    have hh_cont: "top1_continuous_map_on (?S2 - {b}) (subspace_topology ?S2 ?TS2 (?S2 - {b}))
        (UNIV::(real\<times>real) set) ?TR2 h"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    \<comment> \<open>f maps A into S^2-{a,b} \<subseteq> S^2-{b}. Enlarge codomain.\<close>
    have hf_S2b: "top1_continuous_map_on A TA (?S2 - {b}) (subspace_topology ?S2 ?TS2 (?S2 - {b})) f"
    proof -
      have hsub: "?S2 - {a, b} \<subseteq> ?S2 - {b}" by (by100 blast)
      have hS2b_sub: "?S2 - {b} \<subseteq> ?S2" by (by100 blast)
      show ?thesis
        using top1_continuous_map_on_codomain_enlarge[OF hf hsub hS2b_sub] .
    qed
    \<comment> \<open>Compose: g = h \<circ> f.\<close>
    show ?thesis by (rule top1_continuous_map_on_comp[OF hf_S2b hh_cont])
  qed
  let ?K = "?g ` A"
  have hK_compact: "compact ?K"
  proof -
    have hTR2_top: "is_topology_on (UNIV::(real\<times>real) set) ?TR2"
      using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV]
      by (by100 simp)
    have hK_top1: "top1_compact_on ?K (subspace_topology UNIV ?TR2 ?K)"
      by (rule top1_compact_on_continuous_image[OF hcomp hTR2_top hg_cont])
    \<comment> \<open>Bridge: ?TR2 = top1_open_sets for (real\<times>real).\<close>
    have hTR2_eq: "?TR2 = (top1_open_sets :: (real\<times>real) set set)"
      using product_topology_on_open_sets_real2 by (by100 metis)
    have "top1_compact_on ?K (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets ?K)"
      using hK_top1 unfolding hTR2_eq .
    thus ?thesis using top1_compact_on_subspace_UNIV_iff_compact by (by100 blast)
  qed
  have hK_sub: "?K \<subseteq> UNIV - {?origin}"
  proof (rule image_subsetI)
    fix x assume hx: "x \<in> A"
    have hfx: "f x \<in> ?S2 - {a, b}" using hf hx unfolding top1_continuous_map_on_def by (by100 blast)
    hence hfx_ne_a: "f x \<noteq> a" by (by100 blast)
    have hfx_in_S2b: "f x \<in> ?S2 - {b}" using hfx by (by100 blast)
    have ha_in_S2b: "a \<in> ?S2 - {b}" using ha hab by (by100 blast)
    have h_inj: "inj_on h (?S2 - {b})"
      using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have "h (f x) \<noteq> h a"
      using inj_on_eq_iff[OF h_inj hfx_in_S2b ha_in_S2b] hfx_ne_a by (by100 blast)
    thus "(h \<circ> f) x \<in> UNIV - {?origin}" unfolding comp_def by (by100 blast)
  qed
  have hK_closed: "closed ?K" using hK_compact by (rule compact_imp_closed)
  \<comment> \<open>Step 4: g nulhomotopic in R^2 - {?origin}. Equivalently, inclusion K \<hookrightarrow> R^2-{?origin} nulhomotopic.\<close>
  have hj_nul: "top1_nulhomotopic_on ?K (subspace_topology UNIV ?TR2 ?K)
      (UNIV - {?origin}) (subspace_topology UNIV ?TR2 (UNIV - {?origin})) (\<lambda>x. x)"
  proof -
    \<comment> \<open>Step 1: Transfer f nulhomotopic in S^2-{a,b} to g nulhomotopic in R^2-{origin}.\<close>
    have hg_nul: "top1_nulhomotopic_on A TA
        (UNIV - {?origin}) (subspace_topology UNIV ?TR2 (UNIV - {?origin})) ?g"
    proof -
      let ?Sab = "?S2 - {a, b}" and ?TSab = "subspace_topology ?S2 ?TS2 (?S2 - {a, b})"
      let ?Y = "UNIV - {?origin} :: (real\<times>real) set" and ?TY = "subspace_topology UNIV ?TR2 (UNIV - {?origin})"
      \<comment> \<open>From nulhomotopy of f: get homotopy H: A\<times>I \<rightarrow> S^2-{a,b}.\<close>
      obtain c where hc: "c \<in> ?Sab" and hfhom: "top1_homotopic_on A TA ?Sab ?TSab f (\<lambda>_. c)"
        using hnul unfolding top1_nulhomotopic_on_def by (by100 blast)
      obtain H where hH: "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top) ?Sab ?TSab H"
          and hH0: "\<forall>x\<in>A. H (x, 0) = f x" and hH1: "\<forall>x\<in>A. H (x, 1) = c"
        using hfhom unfolding top1_homotopic_on_def by (by100 blast)
      \<comment> \<open>h restricts to continuous S^2-{a,b} \<rightarrow> R^2-{origin} (enlarge domain to S^2-{b}, restrict codomain).\<close>
      have hh_Sab: "top1_continuous_map_on ?Sab ?TSab ?Y ?TY h"
      proof -
        have hsub: "?Sab \<subseteq> ?S2 - {b}" by (by100 blast)
        have hh_cont: "top1_continuous_map_on (?S2 - {b}) (subspace_topology ?S2 ?TS2 (?S2 - {b})) (UNIV::(real\<times>real) set) ?TR2 h"
          using hh unfolding top1_homeomorphism_on_def by (by100 blast)
        have hTopS2: "is_topology_on ?S2 ?TS2"
          using hT unfolding is_topology_on_strict_def by (by100 blast)
        have hS2b_sub: "?S2 - {b} \<subseteq> ?S2" by (by100 blast)
        have hTopS2b: "is_topology_on (?S2 - {b}) (subspace_topology ?S2 ?TS2 (?S2 - {b}))"
          by (rule subspace_topology_is_topology_on[OF hTopS2 hS2b_sub])
        \<comment> \<open>Restrict h to S^2-{a,b}: use subspace restriction + transitivity.\<close>
        have hTR2_top: "is_topology_on (UNIV::(real\<times>real) set) ?TR2"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV]
          by (by100 simp)
        have hh_Sab_R2: "top1_continuous_map_on ?Sab (subspace_topology (?S2 - {b}) (subspace_topology ?S2 ?TS2 (?S2 - {b})) ?Sab) (UNIV::(real\<times>real) set) ?TR2 h"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix x assume "x \<in> ?Sab"
          hence "x \<in> ?S2 - {b}" using hsub by (by100 blast)
          thus "h x \<in> (UNIV::(real\<times>real) set)" by (by100 simp)
        next
          fix V assume hV: "V \<in> ?TR2"
          have "{x \<in> ?Sab. h x \<in> V} = ?Sab \<inter> {x \<in> ?S2 - {b}. h x \<in> V}" by (by100 blast)
          moreover have hpre: "{x \<in> ?S2 - {b}. h x \<in> V} \<in> subspace_topology ?S2 ?TS2 (?S2 - {b})"
            using hh_cont hV unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately have "{x \<in> ?Sab. h x \<in> V} = ?Sab \<inter> {x \<in> ?S2 - {b}. h x \<in> V}" by (by100 blast)
          moreover have "?Sab \<inter> {x \<in> ?S2 - {b}. h x \<in> V} \<in>
            subspace_topology (?S2 - {b}) (subspace_topology ?S2 ?TS2 (?S2 - {b})) ?Sab"
            unfolding subspace_topology_def
            apply (rule CollectI)
            apply (rule exI[of _ "{x \<in> ?S2 - {b}. h x \<in> V}"])
            apply (intro conjI)
             apply (by100 blast)
            using hpre unfolding subspace_topology_def apply (by100 blast)
            done
          ultimately show "{x \<in> ?Sab. h x \<in> V} \<in>
            subspace_topology (?S2 - {b}) (subspace_topology ?S2 ?TS2 (?S2 - {b})) ?Sab"
            by (by100 simp)
        qed
        have hh_Sab_R2': "top1_continuous_map_on ?Sab ?TSab (UNIV::(real\<times>real) set) ?TR2 h"
        proof -
          have "subspace_topology (?S2 - {b}) (subspace_topology ?S2 ?TS2 (?S2 - {b})) ?Sab
              = subspace_topology ?S2 ?TS2 ?Sab"
            by (rule subspace_topology_trans) (by100 blast)
          moreover have "subspace_topology ?S2 ?TS2 ?Sab = ?TSab" by (by100 simp)
          ultimately have "subspace_topology (?S2 - {b}) (subspace_topology ?S2 ?TS2 (?S2 - {b})) ?Sab = ?TSab"
            by (by100 simp)
          thus ?thesis using hh_Sab_R2 by (by100 simp)
        qed
        \<comment> \<open>Restrict codomain to UNIV - {origin}.\<close>
        have himg: "h ` ?Sab \<subseteq> ?Y"
        proof (rule image_subsetI)
          fix x assume "x \<in> ?Sab"
          hence "x \<in> ?S2 - {b}" and "x \<noteq> a" by (by100 blast)+
          have "a \<in> ?S2 - {b}" using ha hab by (by100 blast)
          have h_inj: "inj_on h (?S2 - {b})"
            using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
          have "h x \<noteq> h a" using inj_on_eq_iff[OF h_inj \<open>x \<in> ?S2 - {b}\<close> \<open>a \<in> ?S2 - {b}\<close>] \<open>x \<noteq> a\<close>
            by (by100 blast)
          thus "h x \<in> ?Y" by (by100 blast)
        qed
        have hY_sub: "?Y \<subseteq> (UNIV::(real\<times>real) set)" by (by100 simp)
        show ?thesis
          by (rule top1_continuous_map_on_codomain_shrink[OF hh_Sab_R2' himg hY_sub])
      qed
      \<comment> \<open>Compose: h \<circ> H : A\<times>I \<rightarrow> R^2-{origin}.\<close>
      have hHg: "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top) ?Y ?TY (h \<circ> H)"
        by (rule top1_continuous_map_on_comp[OF hH hh_Sab])
      have hhc: "h c \<in> ?Y"
        using hh_Sab hc unfolding top1_continuous_map_on_def by (by100 blast)
      \<comment> \<open>h \<circ> H is a homotopy from h \<circ> f to constant h(c).\<close>
      have "top1_homotopic_on A TA ?Y ?TY (h \<circ> f) (\<lambda>_. h c)"
        unfolding top1_homotopic_on_def
      proof (intro conjI exI[of _ "h \<circ> H"])
        show "top1_continuous_map_on A TA ?Y ?TY (h \<circ> f)"
          by (rule top1_continuous_map_on_comp[OF hf hh_Sab])
        show "top1_continuous_map_on A TA ?Y ?TY (\<lambda>_. h c)"
        proof -
          have hTA: "is_topology_on A TA"
            using hcomp unfolding top1_compact_on_def by (by100 blast)
          have hTY: "is_topology_on ?Y ?TY"
          proof -
            have hTR2_top: "is_topology_on (UNIV::(real\<times>real) set) ?TR2"
              using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV]
              by (by100 simp)
            show ?thesis by (rule subspace_topology_is_topology_on[OF hTR2_top]) (by100 simp)
          qed
          have "h c \<in> ?Y" by (rule hhc)
          have "\<forall>y0\<in>?Y. top1_continuous_map_on A TA ?Y ?TY (\<lambda>_. y0)"
            by (rule Theorem_18_2(1)[OF hTA hTY hTY])
          thus ?thesis using hhc by (by100 blast)
        qed
        show "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top) ?Y ?TY (h \<circ> H)"
          by (rule hHg)
        show "\<forall>x\<in>A. (h \<circ> H) (x, 0) = (h \<circ> f) x"
          using hH0 unfolding comp_def by (by100 auto)
        show "\<forall>x\<in>A. (h \<circ> H) (x, 1) = (\<lambda>_. h c) x"
          using hH1 unfolding comp_def by (by100 auto)
      qed
      thus ?thesis unfolding top1_nulhomotopic_on_def using hhc by (by100 blast)
    qed
    \<comment> \<open>Step 2: g injective A \<rightarrow> K = g(A). A compact, R^2 Hausdorff.
       By Theorem 26.6, g: A \<rightarrow> K is homeomorphism. So g^{-1}: K \<rightarrow> A exists continuous.\<close>
    have hg_inj: "inj_on ?g A"
    proof -
      have h_inj: "inj_on h (?S2 - {b})"
        using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have hfA_sub: "f ` A \<subseteq> ?S2 - {b}"
        using hf unfolding top1_continuous_map_on_def by (by100 blast)
      show ?thesis using comp_inj_on[OF hinj inj_on_subset[OF h_inj hfA_sub]] .
    qed
    \<comment> \<open>Step 3: Compose nulhomotopy of g with g^{-1}: K \<rightarrow> A.
       inclusion K \<hookrightarrow> R^2-{origin} = g \<circ> g^{-1}, so nulhomotopic.\<close>
    \<comment> \<open>g: A \<cong> K via Theorem 26.6 (compact, Hausdorff, continuous bijection).\<close>
    let ?Y = "UNIV - {?origin} :: (real\<times>real) set"
    let ?TY = "subspace_topology UNIV ?TR2 (UNIV - {?origin})"
    have hTK: "is_topology_on ?K (subspace_topology UNIV ?TR2 ?K)"
    proof -
      have "is_topology_on (UNIV::(real\<times>real) set) ?TR2"
        using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV]
        by (by100 simp)
      thus ?thesis by (rule subspace_topology_is_topology_on) (by100 simp)
    qed
    have hK_haus: "is_hausdorff_on ?K (subspace_topology UNIV ?TR2 ?K)"
    proof -
      have hTOS_eq: "(order_topology_on_UNIV :: real set set) = top1_open_sets"
        using order_topology_on_UNIV_eq_HOL_open unfolding top1_open_sets_def by (by100 auto)
      have hR_haus: "is_hausdorff_on (UNIV::real set) (top1_open_sets::real set set)"
        using conjunct1[OF Theorem_17_11[where 'a=real]] unfolding hTOS_eq .
      have "is_hausdorff_on ((UNIV::real set) \<times> (UNIV::real set))
          (product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set))"
        using conjunct1[OF conjunct2[OF Theorem_17_11]] hR_haus by (by100 blast)
      hence hR2_haus: "is_hausdorff_on (UNIV::(real\<times>real) set) ?TR2" by (by100 simp)
      thus ?thesis using conjunct2[OF conjunct2[OF Theorem_17_11]] by (by100 blast)
    qed
    have hg_K: "top1_continuous_map_on A TA ?K (subspace_topology UNIV ?TR2 ?K) ?g"
      by (rule top1_continuous_map_on_codomain_shrink[OF hg_cont]) (by100 simp)+
    have hg_bij: "bij_betw ?g A ?K"
      unfolding bij_betw_def using hg_inj by (by100 blast)
    have hTA: "is_topology_on A TA" using hcomp unfolding top1_compact_on_def by (by100 blast)
    have hg_homeo: "top1_homeomorphism_on A TA ?K (subspace_topology UNIV ?TR2 ?K) ?g"
      by (rule Theorem_26_6[OF hTA hTK hcomp hK_haus hg_K hg_bij])
    \<comment> \<open>g^{-1}: K \<rightarrow> A continuous.\<close>
    have hginv: "top1_continuous_map_on ?K (subspace_topology UNIV ?TR2 ?K) A TA (inv_into A ?g)"
      using hg_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    \<comment> \<open>Compose nulhomotopy of g with g^{-1}: H(g^{-1}(y), t) is a nulhomotopy of inclusion.\<close>
    obtain c where hcY: "c \<in> ?Y"
        and hghom: "top1_homotopic_on A TA ?Y ?TY ?g (\<lambda>_. c)"
      using hg_nul unfolding top1_nulhomotopic_on_def by (by100 blast)
    obtain H where hH: "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top) ?Y ?TY H"
        and hH0: "\<forall>x\<in>A. H (x, 0) = ?g x" and hH1: "\<forall>x\<in>A. H (x, 1) = c"
      using hghom unfolding top1_homotopic_on_def by (by100 blast)
    \<comment> \<open>H': K \<times> I \<rightarrow> R^2-{origin}, H'(y,t) = H(g^{-1}(y), t).\<close>
    define H' where "H' = (\<lambda>(y,t). H (inv_into A ?g y, t))"
    have hH'_cont: "top1_continuous_map_on (?K \<times> I_set) (product_topology_on (subspace_topology UNIV ?TR2 ?K) I_top)
        ?Y ?TY H'"
    proof -
      \<comment> \<open>H' = H \<circ> (g^{-1} \<times> id). Both g^{-1} and id are continuous.\<close>
      have hpair: "top1_continuous_map_on (?K \<times> I_set) (product_topology_on (subspace_topology UNIV ?TR2 ?K) I_top)
          (A \<times> I_set) (product_topology_on TA I_top) (\<lambda>(y,t). (inv_into A ?g y, t))"
      proof -
        have hTKI: "is_topology_on (?K \<times> I_set) (product_topology_on (subspace_topology UNIV ?TR2 ?K) I_top)"
          by (rule product_topology_on_is_topology_on[OF hTK top1_unit_interval_topology_is_topology_on])
        have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
        \<comment> \<open>\<pi>1 \<circ> pair = g^{-1}: continuous by hginv.\<close>
        have hpi1_p: "pi1 \<circ> (\<lambda>(y,t). (inv_into A ?g y, t)) = inv_into A ?g \<circ> pi1"
          unfolding pi1_def comp_def by (rule ext, simp add: case_prod_beta)
        have hpi2_p: "pi2 \<circ> (\<lambda>(y,t). (inv_into A ?g y, t)) = pi2"
          unfolding pi2_def comp_def by (rule ext, simp add: case_prod_beta)
        have hpi1_cont: "top1_continuous_map_on (?K \<times> I_set) (product_topology_on (subspace_topology UNIV ?TR2 ?K) I_top) ?K (subspace_topology UNIV ?TR2 ?K) pi1"
          by (rule top1_continuous_pi1[OF hTK hTI])
        have "top1_continuous_map_on (?K \<times> I_set) (product_topology_on (subspace_topology UNIV ?TR2 ?K) I_top)
            A TA (pi1 \<circ> (\<lambda>(y,t). (inv_into A ?g y, t)))"
          unfolding hpi1_p by (rule top1_continuous_map_on_comp[OF hpi1_cont hginv])
        moreover have "top1_continuous_map_on (?K \<times> I_set) (product_topology_on (subspace_topology UNIV ?TR2 ?K) I_top)
            I_set I_top (pi2 \<circ> (\<lambda>(y,t). (inv_into A ?g y, t)))"
          unfolding hpi2_p by (rule top1_continuous_pi2[OF hTK hTI])
        ultimately show ?thesis using iffD2[OF Theorem_18_4[OF hTKI hTA hTI]] by (by100 blast)
      qed
      have "top1_continuous_map_on (?K \<times> I_set) (product_topology_on (subspace_topology UNIV ?TR2 ?K) I_top)
          ?Y ?TY (H \<circ> (\<lambda>(y,t). (inv_into A ?g y, t)))"
        by (rule top1_continuous_map_on_comp[OF hpair hH])
      moreover have "H \<circ> (\<lambda>(y,t). (inv_into A ?g y, t)) = H'"
      proof (rule ext)
        fix p show "(H \<circ> (\<lambda>(y,t). (inv_into A ?g y, t))) p = H' p"
          unfolding H'_def comp_def by (cases p) (by100 simp)
      qed
      ultimately show ?thesis by (by100 simp)
    qed
    have hH'0: "\<forall>y\<in>?K. H' (y, 0) = y"
    proof (intro ballI)
      fix y assume "y \<in> ?K"
      then obtain x where hx: "x \<in> A" and hy: "y = ?g x" by (by100 blast)
      have "inv_into A ?g y = x" unfolding hy using inv_into_f_f[OF hg_inj hx] by (by100 simp)
      hence "H' (y, 0) = H (x, 0)" unfolding H'_def by (by100 simp)
      also have "\<dots> = ?g x" using hH0 hx by (by100 blast)
      finally show "H' (y, 0) = y" using hy by (by100 simp)
    qed
    have hH'1: "\<forall>y\<in>?K. H' (y, 1) = c"
    proof (intro ballI)
      fix y assume "y \<in> ?K"
      then obtain x where hx: "x \<in> A" and hy: "y = ?g x" by (by100 blast)
      have "inv_into A ?g y = x" unfolding hy using inv_into_f_f[OF hg_inj hx] by (by100 simp)
      hence "H' (y, 1) = H (x, 1)" unfolding H'_def by (by100 simp)
      also have "\<dots> = c" using hH1 hx by (by100 blast)
      finally show "H' (y, 1) = c" .
    qed
    \<comment> \<open>The inclusion id: K \<rightarrow> R^2-{origin} is nulhomotopic via H'.\<close>
    have hid_cont: "top1_continuous_map_on ?K (subspace_topology UNIV ?TR2 ?K) ?Y ?TY (\<lambda>x. x)"
    proof -
      have hKsub: "?K \<subseteq> ?Y" using hK_sub by (by100 blast)
      have hKY: "?K \<subseteq> (UNIV::(real\<times>real) set)" by (by100 simp)
      have hTR2_top: "is_topology_on (UNIV::(real\<times>real) set) ?TR2"
        using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV]
        by (by100 simp)
      have hTR2_top2: "is_topology_on (UNIV::(real\<times>real) set) ?TR2" by (rule hTR2_top)
      have "top1_continuous_map_on ?K (subspace_topology UNIV ?TR2 ?K) (UNIV::(real\<times>real) set) ?TR2 id"
      proof -
        have "\<forall>A. A \<subseteq> (UNIV::(real\<times>real) set) \<longrightarrow> top1_continuous_map_on A (subspace_topology UNIV ?TR2 A) (UNIV::(real\<times>real) set) ?TR2 id"
          using Theorem_18_2(2)[OF hTR2_top hTR2_top hTR2_top2] by (by100 blast)
        thus ?thesis by (by100 simp)
      qed
      hence hid_R2: "top1_continuous_map_on ?K (subspace_topology UNIV ?TR2 ?K) (UNIV::(real\<times>real) set) ?TR2 (\<lambda>x. x)"
        unfolding id_def .
      have himg_Y: "(\<lambda>x. x) ` ?K \<subseteq> ?Y" using hKsub by (by100 blast)
      have hY_sub_UNIV: "?Y \<subseteq> (UNIV::(real\<times>real) set)" by (by100 simp)
      have "top1_continuous_map_on ?K (subspace_topology UNIV ?TR2 ?K)
          ?Y (subspace_topology (UNIV::(real\<times>real) set) ?TR2 ?Y) (\<lambda>x. x)"
        by (rule top1_continuous_map_on_codomain_shrink[OF hid_R2 himg_Y hY_sub_UNIV])
      thus ?thesis by (by100 simp)
    qed
    have hconst_cont: "top1_continuous_map_on ?K (subspace_topology UNIV ?TR2 ?K) ?Y ?TY (\<lambda>_. c)"
    proof -
      have hTY: "is_topology_on ?Y ?TY"
      proof -
        have hTR2_top: "is_topology_on (UNIV::(real\<times>real) set) ?TR2"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV]
          by (by100 simp)
        show ?thesis by (rule subspace_topology_is_topology_on[OF hTR2_top]) (by100 simp)
      qed
      have "\<forall>y0\<in>?Y. top1_continuous_map_on ?K (subspace_topology UNIV ?TR2 ?K) ?Y ?TY (\<lambda>_. y0)"
        using Theorem_18_2(1)[OF hTK hTY hTY] by (by100 blast)
      thus ?thesis using hcY by (by100 blast)
    qed
    have "top1_homotopic_on ?K (subspace_topology UNIV ?TR2 ?K) ?Y ?TY (\<lambda>x. x) (\<lambda>_. c)"
      unfolding top1_homotopic_on_def
      using hid_cont hconst_cont hH'_cont hH'0 hH'1 by (by100 blast)
    thus ?thesis unfolding top1_nulhomotopic_on_def using hcY by (by100 blast)
  qed
  \<comment> \<open>Step 5 (Contradiction argument, following Munkres):
     Suppose for contradiction that ?origin is in a BOUNDED component C of R^2-K.
     Let D = union of other components. C, D open disjoint, R^2-K = C \<union> D.
     Apply Lemma 62.1 to X = C \<union> K, A = K, Y = R^2-{?origin}:
       extend inclusion K \<hookrightarrow> R^2-{0} to k: C \<union> K \<rightarrow> R^2-{0}.
     Paste k with identity on D: define h(x) = k(x) for x \<in> C, h(x) = x for x \<in> D \<union> K.
     h: R^2 \<rightarrow> R^2-{0}, h = identity on D \<union> K.
     Large ball B centered at 0 containing C \<union> K: h|_\<partial>B = id (since \<partial>B \<subseteq> D).
     r: R^2-{0} \<rightarrow> \<partial>B (radial projection). r \<circ> h|_B : B \<rightarrow> \<partial>B retraction.
     Contradiction with Theorem_55_2.\<close>
  \<comment> \<open>Key helper: R^2 is metrizable, hence normal. C \<union> K metrizable, hence (C\<union>K)\<times>I normal.\<close>
  have hR2_Y_open: "UNIV - {?origin} \<in> ?TR2"
  proof -
    have "open (UNIV - {?origin} :: (real\<times>real) set)"
      by (intro open_Diff open_UNIV finite_imp_closed) (by100 simp)
    hence "UNIV - {?origin} \<in> (top1_open_sets :: (real\<times>real) set set)"
      unfolding top1_open_sets_def by (by100 blast)
    thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
  qed
  \<comment> \<open>The R^2 version of the Borsuk conclusion:
     0 lies in the unbounded component of R^2 - K.\<close>
  have horigin_not_in_K: "?origin \<in> UNIV - ?K"
    using hK_sub by (by100 blast)
  \<comment> \<open>The R^2 version of the Borsuk conclusion:
     0 lies in the unbounded component of R^2 - K.
     "Unbounded" means: for any R > 0, C intersects the complement of the ball of radius R.
     The proof is by contradiction: assume 0 in a compact-closure component.
     Apply Lemma 62.1 to extend, paste with identity, get retraction contradiction.\<close>
  have hTR2: "is_topology_on (UNIV::(real\<times>real) set) ?TR2"
    using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV]
    by (by100 simp)
  \<comment> \<open>K closed in R^2 in the top1 sense.\<close>
  have hK_closedin: "closedin_on (UNIV::(real\<times>real) set) ?TR2 ?K"
  proof -
    have "closed ?K" by (rule hK_closed)
    hence "UNIV - ?K \<in> (top1_open_sets :: (real\<times>real) set set)"
      unfolding top1_open_sets_def using open_Diff[OF open_UNIV hK_closed] by (by100 blast)
    hence "UNIV - ?K \<in> ?TR2" using product_topology_on_open_sets_real2 by (by100 metis)
    thus ?thesis unfolding closedin_on_def by (by100 blast)
  qed
  \<comment> \<open>Now we have G: R^2 \<rightarrow> R^2-{origin} with G|_K = id and G nulhomotopic.
     The key consequence: origin \<notin> G(R^2), so ?origin has no G-preimage.
     This contradicts the existence of a bounded component containing origin.\<close>
  \<comment> \<open>Origin is in UNIV-K (proved). Get the component containing it.\<close>
  have hUK_open: "UNIV - ?K \<in> ?TR2"
  proof -
    have "closed ?K" by (rule hK_closed)
    hence "open (- ?K :: (real\<times>real) set)" using open_closed by (by100 blast)
    hence "open (UNIV - ?K :: (real\<times>real) set)" unfolding Compl_eq_Diff_UNIV[symmetric] .
    hence "(UNIV - ?K) \<in> (top1_open_sets :: (real\<times>real) set set)" unfolding top1_open_sets_def by (by100 blast)
    thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
  qed
  \<comment> \<open>The origin is in a component of UNIV-K, and that component is unbounded.\<close>
  \<comment> \<open>UNIV-K has subspace topology from TR2.\<close>
  let ?T_UK = "subspace_topology UNIV ?TR2 (UNIV - ?K)"
  have hT_UK: "is_topology_on (UNIV - ?K) ?T_UK"
    by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
  \<comment> \<open>Part 1: origin is in a component of UNIV-K.\<close>
  let ?C0 = "top1_component_of_on (UNIV - ?K) ?T_UK ?origin"
  have hC0_comp: "?C0 \<in> top1_components_on (UNIV - ?K) ?T_UK"
    unfolding top1_components_on_def using horigin_not_in_K by (by100 blast)
  have horigin_C0: "?origin \<in> ?C0"
    by (rule top1_component_of_on_self_mem[OF hT_UK horigin_not_in_K])
  \<comment> \<open>Part 2: C0 is unbounded.\<close>
  have hR2_claim: "\<exists>C0. C0 \<in> top1_components_on (UNIV - ?K) ?T_UK
         \<and> ?origin \<in> C0
         \<and> (\<forall>R > 0. \<exists>x \<in> C0. (fst x)^2 + (snd x)^2 > R^2)"
  proof (intro exI[of _ ?C0] conjI)
    show "?C0 \<in> top1_components_on (UNIV - ?K) ?T_UK" by (rule hC0_comp)
    show "?origin \<in> ?C0" by (rule horigin_C0)
    show "\<forall>R>0. \<exists>x\<in>?C0. R\<^sup>2 < (fst x)\<^sup>2 + (snd x)\<^sup>2"
    proof (rule ccontr)
      assume hneg: "\<not> (\<forall>R>0. \<exists>x\<in>?C0. R\<^sup>2 < (fst x)\<^sup>2 + (snd x)\<^sup>2)"
      hence "\<exists>R>0. \<forall>x\<in>?C0. \<not> (R\<^sup>2 < (fst x)\<^sup>2 + (snd x)\<^sup>2)" by (by100 blast)
      then obtain R where hR: "R > 0" and hbnd': "\<forall>x\<in>?C0. \<not> (R\<^sup>2 < (fst x)\<^sup>2 + (snd x)\<^sup>2)"
        by (by100 blast)
      have hbnd: "\<forall>x\<in>?C0. (fst x)\<^sup>2 + (snd x)\<^sup>2 \<le> R\<^sup>2"
      proof (intro ballI)
        fix x assume "x \<in> ?C0"
        from hbnd'[THEN bspec, OF this] show "(fst x)\<^sup>2 + (snd x)\<^sup>2 \<le> R\<^sup>2" by (by100 linarith)
      qed
      \<comment> \<open>C0 \<subseteq> UNIV-K (component is subset).\<close>
      have hC0_sub_UK: "?C0 \<subseteq> UNIV - ?K"
        unfolding top1_component_of_on_def by (by100 blast)
      \<comment> \<open>C0 bounded: contained in ball of radius R.\<close>
      have hC0_bounded: "\<forall>x\<in>?C0. (fst x)\<^sup>2 + (snd x)\<^sup>2 \<le> R\<^sup>2" by (rule hbnd)
      \<comment> \<open>K bounded: compact \<Longrightarrow> bounded.\<close>
      have hK_bounded: "\<exists>R'. \<forall>x\<in>?K. (fst x)\<^sup>2 + (snd x)\<^sup>2 \<le> R'"
      proof (cases "?K = {}")
        case True thus ?thesis by (by100 blast)
      next
        case False
        have "continuous_on ?K (\<lambda>x::(real\<times>real). (fst x)\<^sup>2 + (snd x)\<^sup>2)"
          by (intro continuous_intros)
        from continuous_attains_sup[OF hK_compact False this]
        obtain x0 where "x0 \<in> ?K" "\<forall>y\<in>?K. (fst y)\<^sup>2 + (snd y)\<^sup>2 \<le> (fst x0)\<^sup>2 + (snd x0)\<^sup>2"
          by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      \<comment> \<open>C0 \<union> K closed in R^2 (\<partial>C0 \<subseteq> K, so complement D is open).\<close>
      have hCK_closed: "closed (?C0 \<union> ?K)"
      proof -
        \<comment> \<open>D = UNIV-(C0\<union>K) is open. For each x \<in> D, find open connected nbhd avoiding C0.\<close>
        \<comment> \<open>Use open_subopen: open S if for each x \<in> S, \<exists> open T. x \<in> T \<subseteq> S.\<close>
        \<comment> \<open>For x \<in> D: x \<in> UNIV-K (open). Get open nbhd U \<subseteq> UNIV-K.
           U is open in R^2. Need: U is connected (or restrict to connected component of x in U).
           If U (or a connected part of U) doesn't intersect C0, then it's \<subseteq> D.
           If it does intersect C0, then x is in the same component as C0, contradicting x \<notin> C0.\<close>
        \<comment> \<open>Key issue: prod :: metric_space not registered, so can't use dist/ball/openE.
           Use HOL's open_prod_def directly: open in product topology = union of open rectangles.\<close>
        have "open (UNIV - (?C0 \<union> ?K) :: (real\<times>real) set)"
        proof -
          have hUK_open_HOL: "open (UNIV - ?K :: (real\<times>real) set)"
          proof -
            have "open (- ?K :: (real\<times>real) set)" using open_closed hK_closed by (by100 blast)
            thus ?thesis unfolding Compl_eq_Diff_UNIV[symmetric] .
          qed
          \<comment> \<open>For each x \<in> D: find open rectangle in UNIV-K avoiding C0.\<close>
          have "\<forall>x \<in> UNIV - (?C0 \<union> ?K). \<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> UNIV - (?C0 \<union> ?K)"
          proof (intro ballI)
            fix x :: "real \<times> real" assume hx: "x \<in> UNIV - (?C0 \<union> ?K)"
            hence hxUK: "x \<in> UNIV - ?K" and hxnC0: "x \<notin> ?C0" by (by100 blast)+
            \<comment> \<open>Get open rectangle A\<times>B around x in UNIV-K.\<close>
            obtain A0 B0 where hA0: "open A0" and hB0: "open B0"
                and hxAB: "x \<in> A0 \<times> B0" and hABsub: "A0 \<times> B0 \<subseteq> UNIV - ?K"
              using open_prod_elim[OF hUK_open_HOL hxUK] by (by100 blast)
            \<comment> \<open>Refine to connected open rectangle: open intervals inside A0, B0.\<close>
            have hfstA: "fst x \<in> A0" and hsndB: "snd x \<in> B0" using hxAB by (by100 auto)
            obtain e1 where he1: "e1 > 0" and hI1: "\<forall>y. dist y (fst x) < e1 \<longrightarrow> y \<in> A0"
              using hA0 hfstA unfolding open_dist by (by100 blast)
            obtain e2 where he2: "e2 > 0" and hI2: "\<forall>y. dist y (snd x) < e2 \<longrightarrow> y \<in> B0"
              using hB0 hsndB unfolding open_dist by (by100 blast)
            let ?Ix = "{fst x - e1 <..< fst x + e1}" and ?Iy = "{snd x - e2 <..< snd x + e2}"
            let ?R = "?Ix \<times> ?Iy"
            have hIx_sub: "?Ix \<subseteq> A0"
            proof (rule subsetI)
              fix y assume "y \<in> ?Ix"
              hence "\<bar>y - fst x\<bar> < e1" by (by100 auto)
              hence "dist y (fst x) < e1" unfolding dist_real_def by (by100 linarith)
              thus "y \<in> A0" using hI1 by (by100 blast)
            qed
            have hIy_sub: "?Iy \<subseteq> B0"
            proof (rule subsetI)
              fix y assume "y \<in> ?Iy"
              hence "\<bar>y - snd x\<bar> < e2" by (by100 auto)
              hence "dist y (snd x) < e2" unfolding dist_real_def by (by100 linarith)
              thus "y \<in> B0" using hI2 by (by100 blast)
            qed
            have hR_sub: "?R \<subseteq> A0 \<times> B0" using hIx_sub hIy_sub by (by100 blast)
            have hR_conn: "connected ?R" by (rule connected_Times[OF connected_Ioo connected_Ioo])
            have hR_sub_UK: "?R \<subseteq> UNIV - ?K" by (rule subset_trans[OF hR_sub hABsub])
            have hx_R: "x \<in> ?R" using he1 he2 by (cases x) (by100 simp)
            \<comment> \<open>R connected, R \<subseteq> UNIV-K. If R \<inter> C0 \<noteq> {}, contradiction.\<close>
            have "?R \<inter> ?C0 = {}"
            proof (rule ccontr)
              assume hne: "\<not> (?R \<inter> ?C0 = {})"
              \<comment> \<open>R connected, C0 contains origin, R \<union> C0 \<subseteq> UNIV-K.
                 By component_of definition: R (connected, intersects C0, ⊆ UNIV-K) ⊆ C0.\<close>
              have "?R \<subseteq> ?C0"
              proof -
                obtain z where hz_R: "z \<in> ?R" and hz_C0: "z \<in> ?C0" using hne by (by100 blast)
                \<comment> \<open>R connected (HOL) \<rightarrow> top1_connected_on R (subspace UNIV TR2 R).\<close>
                have hTR2_eq: "?TR2 = (top1_open_sets :: (real\<times>real) set set)"
                  using product_topology_on_open_sets_real2 by (by100 metis)
                have "top1_connected_on ?R (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets ?R)"
                  using top1_connected_on_subspace_open_iff_connected hR_conn by (by100 blast)
                hence hR_top1_conn: "top1_connected_on ?R (subspace_topology (UNIV::(real\<times>real) set) ?TR2 ?R)"
                  unfolding hTR2_eq .
                \<comment> \<open>Subspace transitivity: subspace(UNIV, TR2, R) = subspace(UNIV-K, T_UK, R).\<close>
                have hR_sub_UK': "?R \<subseteq> UNIV - ?K" by (rule hR_sub_UK)
                have hsub_eq_R: "subspace_topology (UNIV - ?K) ?T_UK ?R = subspace_topology UNIV ?TR2 ?R"
                  by (rule subspace_topology_trans[OF hR_sub_UK'])
                have hR_conn_UK: "top1_connected_on ?R (subspace_topology (UNIV - ?K) ?T_UK ?R)"
                  unfolding hsub_eq_R using hR_top1_conn .
                \<comment> \<open>R connected, R \<subseteq> UNIV-K, z \<in> R, z \<in> C0.
                   By component_of definition: R \<subseteq> C0 = component_of origin.\<close>
                have "z \<in> ?C0" by (rule hz_C0)
                hence "top1_component_of_on (UNIV - ?K) ?T_UK z = ?C0"
                  by (rule top1_component_of_on_eq_of_mem[OF hT_UK])
                moreover have "?R \<subseteq> top1_component_of_on (UNIV - ?K) ?T_UK z"
                  unfolding top1_component_of_on_def
                proof (rule Union_upper)
                  show "?R \<in> {C. C \<subseteq> UNIV - ?K \<and> z \<in> C \<and> top1_connected_on C (subspace_topology (UNIV - ?K) ?T_UK C)}"
                    using hR_sub_UK hz_R hR_conn_UK by (by100 blast)
                qed
                ultimately show "?R \<subseteq> ?C0" by (by100 simp)
              qed
              hence "x \<in> ?C0" using hx_R by (by100 blast)
              thus False using hxnC0 by (by100 blast)
            qed
            have "?R \<subseteq> UNIV - (?C0 \<union> ?K)"
            proof (rule subsetI)
              fix y assume "y \<in> ?R"
              have "y \<in> UNIV - ?K" by (rule subsetD[OF hR_sub_UK \<open>y \<in> ?R\<close>])
              hence "y \<notin> ?K" by (by100 simp)
              moreover have "y \<notin> ?C0" using \<open>?R \<inter> ?C0 = {}\<close> \<open>y \<in> ?R\<close> by (by100 blast)
              ultimately show "y \<in> UNIV - (?C0 \<union> ?K)" by (by100 blast)
            qed
            moreover have "open ?R" by (rule open_Times[OF open_greaterThanLessThan open_greaterThanLessThan])
            ultimately show "\<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> UNIV - (?C0 \<union> ?K)"
              using hx_R by (by100 blast)
          qed
          thus ?thesis using open_subopen by (by100 blast)
        qed
        hence "closed (- (UNIV - (?C0 \<union> ?K)) :: (real\<times>real) set)" using open_closed by (by100 blast)
        thus ?thesis by (by100 simp)
      qed
      \<comment> \<open>C0 \<union> K bounded + closed \<Longrightarrow> compact (Heine-Borel).\<close>
      have hCK_compact: "compact (?C0 \<union> ?K)"
      proof -
        \<comment> \<open>C0\<union>K \<subseteq> big closed square. Show the square is compact, C0\<union>K closed \<Longrightarrow> compact.\<close>
        obtain R' where hR': "\<forall>x\<in>?K. (fst x)\<^sup>2 + (snd x)\<^sup>2 \<le> R'" using hK_bounded by (by100 blast)
        define M where "M = max (R\<^sup>2) R' + 1"
        have hM_pos: "M > 0" unfolding M_def
        proof -
          have "R\<^sup>2 > 0" using hR by (by100 simp)
          thus "0 < max (R\<^sup>2) R' + 1" by (by100 linarith)
        qed
        have hCK_sub_sq: "?C0 \<union> ?K \<subseteq> {- sqrt M .. sqrt M} \<times> {- sqrt M .. sqrt M}"
        proof (rule subsetI)
          fix x assume "x \<in> ?C0 \<union> ?K"
          hence "(fst x)\<^sup>2 + (snd x)\<^sup>2 \<le> M"
          proof
            assume "x \<in> ?C0"
            hence "(fst x)\<^sup>2 + (snd x)\<^sup>2 \<le> R\<^sup>2" using hbnd by (by100 blast)
            also have "R\<^sup>2 \<le> max (R\<^sup>2) R'" by (by100 simp)
            finally show ?thesis unfolding M_def by (by100 linarith)
          next
            assume "x \<in> ?K"
            hence "(fst x)\<^sup>2 + (snd x)\<^sup>2 \<le> R'" using hR' by (by100 blast)
            also have "R' \<le> max (R\<^sup>2) R'" by (by100 simp)
            finally show ?thesis unfolding M_def by (by100 linarith)
          qed
          have hfst: "(fst x)\<^sup>2 \<le> M"
          proof -
            have "(snd x)\<^sup>2 \<ge> 0" by (by100 simp)
            thus ?thesis using \<open>(fst x)\<^sup>2 + (snd x)\<^sup>2 \<le> M\<close> by (by100 linarith)
          qed
          have hsnd: "(snd x)\<^sup>2 \<le> M"
          proof -
            have "(fst x)\<^sup>2 \<ge> 0" by (by100 simp)
            thus ?thesis using \<open>(fst x)\<^sup>2 + (snd x)\<^sup>2 \<le> M\<close> by (by100 linarith)
          qed
          have "\<bar>fst x\<bar> \<le> sqrt M"
          proof -
            have "\<bar>fst x\<bar>\<^sup>2 \<le> M" using hfst by (by100 simp)
            hence "\<bar>fst x\<bar> \<le> sqrt M" using real_le_rsqrt by (by100 blast)
            thus ?thesis .
          qed
          moreover have "\<bar>snd x\<bar> \<le> sqrt M"
          proof -
            have "\<bar>snd x\<bar>\<^sup>2 \<le> M" using hsnd by (by100 simp)
            hence "\<bar>snd x\<bar> \<le> sqrt M" using real_le_rsqrt by (by100 blast)
            thus ?thesis .
          qed
          ultimately have "- sqrt M \<le> fst x \<and> fst x \<le> sqrt M \<and> - sqrt M \<le> snd x \<and> snd x \<le> sqrt M"
            by (by100 linarith)
          thus "x \<in> {- sqrt M .. sqrt M} \<times> {- sqrt M .. sqrt M}"
            by (cases x) (by100 simp)
        qed
        \<comment> \<open>The square is compact (via top1 product of compact intervals + bridge).\<close>
        have hsq_compact: "compact ({- sqrt M .. sqrt M} \<times> {- sqrt M .. sqrt M} :: (real\<times>real) set)"
        proof -
          have h1: "compact ({- sqrt M .. sqrt M} :: real set)" by (rule compact_Icc)
          have h1': "top1_compact_on {- sqrt M .. sqrt M}
              (subspace_topology (UNIV::real set) top1_open_sets {- sqrt M .. sqrt M})"
            using top1_compact_on_subspace_UNIV_iff_compact h1 by (by100 blast)
          have hprod: "top1_compact_on ({- sqrt M .. sqrt M} \<times> {- sqrt M .. sqrt M})
              (product_topology_on (subspace_topology UNIV top1_open_sets {- sqrt M .. sqrt M})
                                   (subspace_topology UNIV top1_open_sets {- sqrt M .. sqrt M}))"
            by (rule Theorem_26_7[OF h1' h1'])
          have hTR2_eq: "?TR2 = (top1_open_sets :: (real\<times>real) set set)"
            using product_topology_on_open_sets_real2 by (by100 metis)
          have heq: "product_topology_on (subspace_topology UNIV top1_open_sets {- sqrt M .. sqrt M})
                                         (subspace_topology UNIV top1_open_sets {- sqrt M .. sqrt M})
              = subspace_topology (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)
                  ({- sqrt M .. sqrt M} \<times> {- sqrt M .. sqrt M})"
            using Theorem_16_3[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
                of "{- sqrt M .. sqrt M}" "{- sqrt M .. sqrt M}"] by (by100 simp)
          have "top1_compact_on ({- sqrt M .. sqrt M} \<times> {- sqrt M .. sqrt M})
              (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets ({- sqrt M .. sqrt M} \<times> {- sqrt M .. sqrt M}))"
            using hprod unfolding heq hTR2_eq by (by100 simp)
          thus ?thesis using top1_compact_on_subspace_UNIV_iff_compact by (by100 blast)
        qed
        have "compact ({- sqrt M .. sqrt M} \<times> {- sqrt M .. sqrt M} \<inter> (?C0 \<union> ?K))"
          by (rule compact_Int_closed[OF hsq_compact hCK_closed])
        moreover have "{- sqrt M .. sqrt M} \<times> {- sqrt M .. sqrt M} \<inter> (?C0 \<union> ?K) = ?C0 \<union> ?K"
          using hCK_sub_sq by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>Compact \<Longrightarrow> top1_compact_on \<Longrightarrow> Hausdorff \<Longrightarrow> normal (Theorem_32_3).\<close>
      have hCK_normal: "top1_normal_on (?C0 \<union> ?K) (subspace_topology UNIV ?TR2 (?C0 \<union> ?K))"
      proof -
        \<comment> \<open>Bridge: HOL compact \<rightarrow> top1_compact_on.\<close>
        have hTR2_eq: "?TR2 = (top1_open_sets :: (real\<times>real) set set)"
          using product_topology_on_open_sets_real2 by (by100 metis)
        have hCK_top1_compact: "top1_compact_on (?C0 \<union> ?K) (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets (?C0 \<union> ?K))"
          using top1_compact_on_subspace_UNIV_iff_compact hCK_compact by (by100 blast)
        hence "top1_compact_on (?C0 \<union> ?K) (subspace_topology UNIV ?TR2 (?C0 \<union> ?K))"
          unfolding hTR2_eq .
        moreover have "is_hausdorff_on (?C0 \<union> ?K) (subspace_topology UNIV ?TR2 (?C0 \<union> ?K))"
        proof -
          have "is_hausdorff_on (UNIV::(real\<times>real) set) ?TR2"
          proof -
            have hTOS_eq: "(order_topology_on_UNIV :: real set set) = top1_open_sets"
              using order_topology_on_UNIV_eq_HOL_open unfolding top1_open_sets_def by (by100 auto)
            have "is_hausdorff_on (UNIV::real set) (top1_open_sets::real set set)"
              using conjunct1[OF Theorem_17_11[where 'a=real]] unfolding hTOS_eq by (by100 simp)
            hence "is_hausdorff_on ((UNIV::real set) \<times> (UNIV::real set))
                (product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set))"
              using conjunct1[OF conjunct2[OF Theorem_17_11]] by (by100 blast)
            thus ?thesis by (by100 simp)
          qed
          thus ?thesis using conjunct2[OF conjunct2[OF Theorem_17_11]] by (by100 blast)
        qed
        ultimately show ?thesis by (rule Theorem_32_3)
      qed
      have hCKI_normal: "top1_normal_on ((?C0 \<union> ?K) \<times> I_set)
          (product_topology_on (subspace_topology UNIV ?TR2 (?C0 \<union> ?K)) I_top)"
      proof -
        \<comment> \<open>I compact in top1.\<close>
        have "compact (I_set :: real set)"
        proof -
          have "I_set = {0..1::real}" unfolding top1_unit_interval_def by (by100 auto)
          moreover have "compact ({0..1::real})" by (rule compact_Icc)
          ultimately show ?thesis by (by100 simp)
        qed
        hence "top1_compact_on I_set (subspace_topology (UNIV::real set) top1_open_sets I_set)"
          using top1_compact_on_subspace_UNIV_iff_compact by (by100 blast)
        hence hI_compact: "top1_compact_on I_set I_top"
          unfolding top1_unit_interval_topology_def top1_unit_interval_def by (by100 simp)
        \<comment> \<open>C0\<union>K compact in top1.\<close>
        have hTR2_eq: "?TR2 = (top1_open_sets :: (real\<times>real) set set)"
          using product_topology_on_open_sets_real2 by (by100 metis)
        have hCK_top1: "top1_compact_on (?C0 \<union> ?K) (subspace_topology UNIV ?TR2 (?C0 \<union> ?K))"
        proof -
          have "top1_compact_on (?C0 \<union> ?K) (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets (?C0 \<union> ?K))"
            using top1_compact_on_subspace_UNIV_iff_compact hCK_compact by (by100 blast)
          thus ?thesis unfolding hTR2_eq .
        qed
        \<comment> \<open>Product compact.\<close>
        have "top1_compact_on ((?C0 \<union> ?K) \<times> I_set)
            (product_topology_on (subspace_topology UNIV ?TR2 (?C0 \<union> ?K)) I_top)"
          by (rule Theorem_26_7[OF hCK_top1 hI_compact])
        moreover have "is_hausdorff_on ((?C0 \<union> ?K) \<times> I_set)
            (product_topology_on (subspace_topology UNIV ?TR2 (?C0 \<union> ?K)) I_top)"
        proof -
          have "is_hausdorff_on (?C0 \<union> ?K) (subspace_topology UNIV ?TR2 (?C0 \<union> ?K))"
          proof -
            have "is_hausdorff_on (UNIV::(real\<times>real) set) ?TR2"
            proof -
              have hTOS_eq: "(order_topology_on_UNIV :: real set set) = top1_open_sets"
                using order_topology_on_UNIV_eq_HOL_open unfolding top1_open_sets_def by (by100 auto)
              have "is_hausdorff_on (UNIV::real set) (top1_open_sets::real set set)"
                using conjunct1[OF Theorem_17_11[where 'a=real]] unfolding hTOS_eq by (by100 simp)
              hence "is_hausdorff_on ((UNIV::real set) \<times> (UNIV::real set))
                  (product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set))"
                using conjunct1[OF conjunct2[OF Theorem_17_11]] by (by100 blast)
              thus ?thesis by (by100 simp)
            qed
            thus ?thesis using conjunct2[OF conjunct2[OF Theorem_17_11]] by (by100 blast)
          qed
          moreover have "is_hausdorff_on I_set I_top"
          proof -
            have "is_hausdorff_on (UNIV::real set) (order_topology_on_UNIV::real set set)"
              using conjunct1[OF Theorem_17_11[where 'a=real]] .
            have hTOS: "(order_topology_on_UNIV :: real set set) = top1_open_sets"
              using order_topology_on_UNIV_eq_HOL_open unfolding top1_open_sets_def by (by100 auto)
            hence "is_hausdorff_on (UNIV::real set) (top1_open_sets::real set set)"
              using conjunct1[OF Theorem_17_11[where 'a=real]] by (by100 simp)
            hence "is_hausdorff_on I_set (subspace_topology UNIV top1_open_sets I_set)"
              using conjunct2[OF conjunct2[OF Theorem_17_11]] by (by100 blast)
            thus ?thesis unfolding top1_unit_interval_topology_def top1_unit_interval_def by (by100 simp)
          qed
          ultimately show ?thesis using conjunct1[OF conjunct2[OF Theorem_17_11]] by (by100 blast)
        qed
        ultimately show ?thesis by (rule Theorem_32_3)
      qed
      \<comment> \<open>K closed in C0\<union>K.\<close>
      have hK_closedin_CK: "closedin_on (?C0 \<union> ?K) (subspace_topology UNIV ?TR2 (?C0 \<union> ?K)) ?K"
      proof -
        have hCK_sub: "?C0 \<union> ?K \<subseteq> UNIV" by (by100 simp)
        have "?K = ?K \<inter> (?C0 \<union> ?K)" by (by100 blast)
        thus ?thesis using iffD2[OF Theorem_17_2[OF hTR2 hCK_sub]] hK_closedin by (by100 blast)
      qed
      \<comment> \<open>Apply Lemma 62.1 to X = C0\<union>K, A = K, Y = R^2-{origin}.\<close>
      have hTCK: "is_topology_on (?C0 \<union> ?K) (subspace_topology UNIV ?TR2 (?C0 \<union> ?K))"
        by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
      \<comment> \<open>Inclusion K \<hookrightarrow> R^2-{origin} continuous from C0\<union>K subspace.\<close>
      have hK_sub_CK: "?K \<subseteq> ?C0 \<union> ?K" by (by100 blast)
      have hsubspace_trans: "subspace_topology (?C0 \<union> ?K) (subspace_topology UNIV ?TR2 (?C0 \<union> ?K)) ?K
          = subspace_topology UNIV ?TR2 ?K"
        by (rule subspace_topology_trans[OF hK_sub_CK])
      \<comment> \<open>Extract continuity of inclusion from nulhomotopy.\<close>
      have hj_cont_UK: "top1_continuous_map_on ?K (subspace_topology UNIV ?TR2 ?K)
          (UNIV - {?origin}) (subspace_topology UNIV ?TR2 (UNIV - {?origin})) (\<lambda>x. x)"
      proof -
        from hj_nul obtain c where "top1_homotopic_on ?K (subspace_topology UNIV ?TR2 ?K)
            (UNIV - {?origin}) (subspace_topology UNIV ?TR2 (UNIV - {?origin})) (\<lambda>x. x) (\<lambda>_. c)"
          unfolding top1_nulhomotopic_on_def by (by100 blast)
        thus ?thesis unfolding top1_homotopic_on_def by (by100 blast)
      qed
      have hj_cont_CK: "top1_continuous_map_on ?K (subspace_topology (?C0 \<union> ?K) (subspace_topology UNIV ?TR2 (?C0 \<union> ?K)) ?K)
          (UNIV - {?origin}) (subspace_topology UNIV ?TR2 (UNIV - {?origin})) (\<lambda>x. x)"
        unfolding hsubspace_trans by (rule hj_cont_UK)
      have hj_nul_CK: "top1_nulhomotopic_on ?K (subspace_topology (?C0 \<union> ?K) (subspace_topology UNIV ?TR2 (?C0 \<union> ?K)) ?K)
          (UNIV - {?origin}) (subspace_topology UNIV ?TR2 (UNIV - {?origin})) (\<lambda>x. x)"
        unfolding hsubspace_trans by (rule hj_nul)
      obtain k where hk: "top1_continuous_map_on (?C0 \<union> ?K) (subspace_topology UNIV ?TR2 (?C0 \<union> ?K))
          (UNIV - {?origin}) (subspace_topology UNIV ?TR2 (UNIV - {?origin})) k"
          and hk_ext: "\<forall>x\<in>?K. k x = x"
        using Lemma_62_1_homotopy_extension[OF hTCK hCK_normal hCKI_normal hK_closedin_CK hR2_Y_open hj_cont_CK hj_nul_CK]
        by blast
      \<comment> \<open>Paste k with identity on D\<union>K: h(x) = k(x) for x \<in> C0, h(x) = x for x \<in> D\<union>K.
         Both maps continuous, agree on K. C0\<union>K and D\<union>K closed. Pasting lemma gives h continuous.\<close>
      \<comment> \<open>h: R^2 \<rightarrow> R^2-{origin}. For large ball B: h|_\<partial>B = id (since \<partial>B \<subseteq> D).
         Radial projection r: R^2-{origin} \<rightarrow> \<partial>B gives r \<circ> h|_B retraction.
         Contradiction with Theorem_55_2_no_retraction.\<close>
      \<comment> \<open>Step 1: Define h(x) = k(x) for x \<in> C0\<union>K, h(x) = x for x \<notin> C0.
         Since k|_K = id, both definitions agree on K.\<close>
      define hmap where "hmap = (\<lambda>x. if x \<in> ?C0 then k x else x)"
      \<comment> \<open>h maps R^2 to R^2-{origin}: for x \<in> C0, k(x) \<in> R^2-{origin} (from k range).
         For x \<notin> C0: x \<noteq> origin? Yes, since origin \<in> C0.\<close>
      have hmap_avoids: "\<forall>x. hmap x \<noteq> ?origin"
      proof
        fix x show "hmap x \<noteq> ?origin"
        proof (cases "x \<in> ?C0")
          case True
          hence "hmap x = k x" unfolding hmap_def by (by100 simp)
          moreover have "k x \<in> UNIV - {?origin}"
          proof -
            have "x \<in> ?C0 \<union> ?K" using True by (by100 blast)
            thus ?thesis using hk unfolding top1_continuous_map_on_def by (by100 blast)
          qed
          ultimately have "hmap x \<in> UNIV - {?origin}" by (by100 simp)
          thus ?thesis by (by100 simp)
        next
          case False
          hence "hmap x = x" unfolding hmap_def by (by100 simp)
          moreover have "x \<noteq> ?origin" using False horigin_C0 by (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
      qed
      \<comment> \<open>Step 2: h = id outside C0 (in particular on \<partial>B for large B).\<close>
      have hmap_id_outside: "\<forall>x. x \<notin> ?C0 \<longrightarrow> hmap x = x"
        unfolding hmap_def by (by100 simp)
      \<comment> \<open>Step 3: C0 is open (same argument as CK closed, by component maximality).\<close>
      have hC0_open: "open (?C0 :: (real\<times>real) set)"
      proof (rule openI)
        fix x :: "real\<times>real" assume hx_C0: "x \<in> ?C0"
        hence hx_UK: "x \<in> UNIV - ?K" using hC0_sub_UK by (by100 blast)
        have hUK_HOL: "open (UNIV - ?K :: (real\<times>real) set)"
        proof -
          have "open (- ?K :: (real\<times>real) set)" using open_closed hK_closed by (by100 blast)
          thus ?thesis unfolding Compl_eq_Diff_UNIV[symmetric] .
        qed
        obtain A0 B0 where "open A0" "open B0" "x \<in> A0 \<times> B0" "A0 \<times> B0 \<subseteq> UNIV - ?K"
          using open_prod_elim[OF hUK_HOL hx_UK] by (by100 blast)
        obtain e1 where he1: "e1 > 0" and hI1: "\<forall>y. dist y (fst x) < e1 \<longrightarrow> y \<in> A0"
          using \<open>open A0\<close> \<open>x \<in> A0 \<times> B0\<close> unfolding open_dist by (by100 auto)
        obtain e2 where he2: "e2 > 0" and hI2: "\<forall>y. dist y (snd x) < e2 \<longrightarrow> y \<in> B0"
          using \<open>open B0\<close> \<open>x \<in> A0 \<times> B0\<close> unfolding open_dist by (by100 auto)
        let ?Rx = "{fst x - e1 <..< fst x + e1} \<times> {snd x - e2 <..< snd x + e2}"
        have hRx_sub: "?Rx \<subseteq> UNIV - ?K"
        proof (rule subset_trans[of _ "A0 \<times> B0"])
          show "?Rx \<subseteq> A0 \<times> B0"
          proof (rule subsetI)
            fix y assume hy: "y \<in> ?Rx"
            have "dist (fst y) (fst x) < e1" using hy unfolding dist_real_def by (by100 auto)
            hence "fst y \<in> A0" using hI1 by (by100 blast)
            moreover have "dist (snd y) (snd x) < e2" using hy unfolding dist_real_def by (by100 auto)
            hence "snd y \<in> B0" using hI2 by (by100 blast)
            ultimately show "y \<in> A0 \<times> B0" by (cases y) (by100 simp)
          qed
        qed (rule \<open>A0 \<times> B0 \<subseteq> UNIV - ?K\<close>)
        have "?Rx \<subseteq> ?C0"
        proof -
          have hTR2_eq: "?TR2 = (top1_open_sets :: (real\<times>real) set set)"
            using product_topology_on_open_sets_real2 by (by100 metis)
          have "connected ?Rx" by (rule connected_Times[OF connected_Ioo connected_Ioo])
          hence "top1_connected_on ?Rx (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets ?Rx)"
            using top1_connected_on_subspace_open_iff_connected by (by100 blast)
          hence hRx_conn_TR2: "top1_connected_on ?Rx (subspace_topology UNIV ?TR2 ?Rx)" unfolding hTR2_eq .
          have hsub_eq: "subspace_topology (UNIV - ?K) ?T_UK ?Rx = subspace_topology UNIV ?TR2 ?Rx"
            by (rule subspace_topology_trans[OF hRx_sub])
          have hRx_conn: "top1_connected_on ?Rx (subspace_topology (UNIV - ?K) ?T_UK ?Rx)"
            unfolding hsub_eq using hRx_conn_TR2 .
          have hx_Rx: "x \<in> ?Rx" using he1 he2 by (cases x) (by100 simp)
          have "?Rx \<subseteq> top1_component_of_on (UNIV - ?K) ?T_UK x"
            unfolding top1_component_of_on_def
            apply (rule Union_upper)
            using hRx_sub hx_Rx hRx_conn by (by100 blast)
          thus ?thesis using top1_component_of_on_eq_of_mem[OF hT_UK hx_C0] by (by100 simp)
        qed
        moreover have "open ?Rx" by (rule open_Times[OF open_greaterThanLessThan open_greaterThanLessThan])
        moreover have "x \<in> ?Rx" using he1 he2 by (cases x) (by100 simp)
        ultimately show "\<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> ?C0" by (by100 blast)
      qed
      \<comment> \<open>Step 4: h continuous. On C0 (open): hmap = k, continuous.
         On UNIV-C0 (closed since C0 open): hmap = id, continuous.
         Agree on C0 \<inter> (UNIV-C0) = {} (trivially). But actually need on boundary.\<close>
      \<comment> \<open>Actually: hmap continuous because:
         - On the open set C0: hmap = k (continuous from C0\<union>K restricted to C0)
         - On the open set UNIV-(C0\<union>K) = D: hmap = id (continuous)
         - C0 \<union> D = UNIV-K (open). On UNIV-K, hmap is continuous (open cover pasting).
         - On K (closed): hmap = id = k (both continuous, agree). So hmap continuous on K.
         - UNIV = (UNIV-K) \<union> K, open \<union> closed = UNIV.
         - Pasting of continuous on open UNIV-K and continuous on closed K gives continuous on UNIV.\<close>
      \<comment> \<open>Step 5: Large ball, radial projection, retraction, Theorem_55_2.\<close>
      \<comment> \<open>Step 4: hmap continuous on UNIV.
         Use continuous_on_If with s = C0\<union>K (closed) and t = UNIV-C0 (closed).
         On s: f = k (continuous). On t: g = id (continuous).
         Agreement on s \<inter> \<not>P: x \<in> C0\<union>K, x \<notin> C0, so x \<in> K, k(x) = x.
         On t \<inter> P: vacuously true (UNIV-C0 \<inter> C0 = {}).\<close>
      have hk_cont_HOL: "continuous_on (?C0 \<union> ?K) k"
      proof -
        \<comment> \<open>Bridge: top1_continuous_map_on to continuous_on via preimage argument.\<close>
        {
          fix U :: "(real \<times> real) set" assume hUo: "open U"
          have hU_os: "U \<in> (top1_open_sets :: (real\<times>real) set set)"
            using hUo unfolding top1_open_sets_def by (by100 blast)
          have hU_prod: "U \<in> ?TR2"
            using hU_os product_topology_on_open_sets_real2 by (by100 metis)
          \<comment> \<open>V = (UNIV-{origin}) \<inter> U is open in the codomain subspace topology.\<close>
          have hV_in: "(UNIV - {?origin}) \<inter> U \<in> subspace_topology UNIV ?TR2 (UNIV - {?origin})"
            unfolding subspace_topology_def using hU_prod by (by100 blast)
          have hpre: "{x \<in> ?C0 \<union> ?K. k x \<in> (UNIV - {?origin}) \<inter> U}
              \<in> subspace_topology UNIV ?TR2 (?C0 \<union> ?K)"
            using hk hV_in unfolding top1_continuous_map_on_def by (by100 blast)
          \<comment> \<open>Since k maps into UNIV-{origin}, preimage of U = preimage of (UNIV-{0})\<inter>U.\<close>
          have hk_range: "\<forall>x\<in>?C0 \<union> ?K. k x \<in> UNIV - {?origin}"
            using hk unfolding top1_continuous_map_on_def by (by100 blast)
          have hpre_eq: "{x \<in> ?C0 \<union> ?K. k x \<in> U} = {x \<in> ?C0 \<union> ?K. k x \<in> (UNIV - {?origin}) \<inter> U}"
            using hk_range by (by100 blast)
          have hpre2: "{x \<in> ?C0 \<union> ?K. k x \<in> U} \<in> subspace_topology UNIV ?TR2 (?C0 \<union> ?K)"
          proof -
            have "{x \<in> ?C0 \<union> ?K. k x \<in> (UNIV - {?origin}) \<inter> U}
                \<in> subspace_topology UNIV ?TR2 (?C0 \<union> ?K)" by (rule hpre)
            thus ?thesis using hpre_eq by (by100 simp)
          qed
          then obtain W where hW: "W \<in> ?TR2" and hW_eq: "{x \<in> ?C0 \<union> ?K. k x \<in> U} = (?C0 \<union> ?K) \<inter> W"
            unfolding subspace_topology_def by (by100 auto)
          have hW_os: "W \<in> (top1_open_sets :: (real\<times>real) set set)"
            using hW product_topology_on_open_sets_real2 by (by100 metis)
          have hWo: "open W" using hW_os unfolding top1_open_sets_def by (by100 simp)
          have "\<exists>A. open A \<and> A \<inter> (?C0 \<union> ?K) = k -` U \<inter> (?C0 \<union> ?K)"
          proof (intro exI[of _ W] conjI)
            show "open W" by (rule hWo)
            show "W \<inter> (?C0 \<union> ?K) = k -` U \<inter> (?C0 \<union> ?K)"
            proof (rule set_eqI)
              fix x show "x \<in> W \<inter> (?C0 \<union> ?K) \<longleftrightarrow> x \<in> k -` U \<inter> (?C0 \<union> ?K)"
                using hW_eq by (by100 blast)
            qed
          qed
        } note hstep = this
        show ?thesis unfolding continuous_on_open_invariant
        proof (intro allI impI)
          fix B :: "(real \<times> real) set" assume "open B"
          thus "\<exists>A. open A \<and> A \<inter> (?C0 \<union> ?K) = k -` B \<inter> (?C0 \<union> ?K)" by (rule hstep)
        qed
      qed
      have hmap_cont_UNIV: "continuous_on UNIV hmap"
      proof -
        have hclosed_compl: "closed (UNIV - ?C0 :: (real\<times>real) set)"
          using hC0_open open_closed by (by100 blast)
        have huniv: "(?C0 \<union> ?K) \<union> (UNIV - ?C0) = (UNIV :: (real\<times>real) set)"
          by (by100 blast)
        have hk_agree: "\<And>x. x \<in> ?C0 \<union> ?K \<Longrightarrow> x \<notin> ?C0 \<Longrightarrow> k x = x"
          using hk_ext by (by100 blast)
        have hvac: "\<And>x::real\<times>real. x \<in> UNIV - ?C0 \<Longrightarrow> x \<in> ?C0 \<Longrightarrow> k x = x"
          by (by100 blast)
        have "continuous_on ((?C0 \<union> ?K) \<union> (UNIV - ?C0)) (\<lambda>x. if x \<in> ?C0 then k x else x)"
          by (rule continuous_on_If[OF hCK_closed hclosed_compl hk_cont_HOL continuous_on_id hk_agree hvac])
        hence "continuous_on UNIV (\<lambda>x. if x \<in> ?C0 then k x else x)"
          using huniv by (by100 simp)
        thus ?thesis unfolding hmap_def .
      qed
      \<comment> \<open>Step 5: Retraction contradiction via Theorem_55_2.\<close>
      \<comment> \<open>C0 bounded by R, K bounded by some R'. Choose S for the ball.\<close>
      obtain R' where hR': "\<forall>x\<in>?K. (fst x)\<^sup>2 + (snd x)\<^sup>2 \<le> R'"
        using hK_bounded by (by100 blast)
      define S where "S = 1 + sqrt (max (R\<^sup>2) (max R' 0))"
      have hS_pos: "S > 0" unfolding S_def
        using real_sqrt_ge_zero[of "max (R\<^sup>2) (max R' 0)"] by (by100 linarith)
      have hCK_in_ball: "\<forall>x\<in>?C0 \<union> ?K. (fst x)\<^sup>2 + (snd x)\<^sup>2 < S\<^sup>2"
      proof (intro ballI)
        fix x assume "x \<in> ?C0 \<union> ?K"
        have hx_bnd: "(fst x)\<^sup>2 + (snd x)\<^sup>2 \<le> max (R\<^sup>2) (max R' 0)"
        proof (cases "x \<in> ?C0")
          case True
          hence "(fst x)\<^sup>2 + (snd x)\<^sup>2 \<le> R\<^sup>2" using hbnd by (by100 blast)
          thus ?thesis by (by100 linarith)
        next
          case False
          hence "x \<in> ?K" using \<open>x \<in> ?C0 \<union> ?K\<close> by (by100 blast)
          hence "(fst x)\<^sup>2 + (snd x)\<^sup>2 \<le> R'" using hR' by (by100 blast)
          moreover have "(0::real) \<le> (fst x)\<^sup>2 + (snd x)\<^sup>2" by (by100 simp)
          ultimately have "(fst x)\<^sup>2 + (snd x)\<^sup>2 \<le> max R' 0" by (by100 linarith)
          thus ?thesis by (by100 linarith)
        qed
        let ?M = "max (R\<^sup>2) (max R' 0)"
        have hM_nonneg: "?M \<ge> 0" using hR by (by100 simp)
        have "sqrt ?M < S" unfolding S_def by (by100 linarith)
        hence "?M < S\<^sup>2"
        proof -
          have hsqrt_nonneg: "sqrt ?M \<ge> 0" using real_sqrt_ge_zero[of ?M] by (by100 linarith)
          have hsqrt_lt: "sqrt ?M < S" using \<open>sqrt ?M < S\<close> .
          have hsqrt_sq: "sqrt ?M * sqrt ?M = ?M"
            using real_sqrt_mult_self[of ?M] hM_nonneg by (by100 linarith)
          have "sqrt ?M * sqrt ?M < S * S"
          proof -
            have "sqrt ?M \<le> S" using hsqrt_lt by (by100 linarith)
            hence "sqrt ?M * sqrt ?M \<le> sqrt ?M * S"
              using hsqrt_nonneg by (rule mult_left_mono)
            also have "sqrt ?M * S < S * S"
              using hsqrt_lt hS_pos by (rule mult_strict_right_mono)
            finally show ?thesis .
          qed
          thus "?M < S\<^sup>2" using hsqrt_sq unfolding power2_eq_square by (by100 linarith)
        qed
        thus "(fst x)\<^sup>2 + (snd x)\<^sup>2 < S\<^sup>2" using hx_bnd by (by100 linarith)
      qed
      have hmap_fix_outside: "\<forall>x. (fst x)\<^sup>2 + (snd x)\<^sup>2 \<ge> S\<^sup>2 \<longrightarrow> hmap x = x"
      proof (intro allI impI)
        fix x :: "real \<times> real" assume hx: "(fst x)\<^sup>2 + (snd x)\<^sup>2 \<ge> S\<^sup>2"
        have "x \<notin> ?C0"
        proof
          assume "x \<in> ?C0"
          hence "(fst x)\<^sup>2 + (snd x)\<^sup>2 < S\<^sup>2" using hCK_in_ball by (by100 blast)
          with hx show False by (by100 linarith)
        qed
        thus "hmap x = x" using hmap_id_outside by (by100 blast)
      qed
      \<comment> \<open>Radial projection retracts R^2-{0} onto S^1 (in top1 framework, from Ch9_13).\<close>
      \<comment> \<open>Construct ret(x) = r(hmap(S*x))/S for x in B^2, where r is radial projection.\<close>
      \<comment> \<open>Translate so origin maps to (0,0). Define hmap' = T o hmap o T^{-1}.\<close>
      define hmap' where "hmap' = (\<lambda>x::real\<times>real. (fst (hmap (fst x + fst ?origin, snd x + snd ?origin)) - fst ?origin,
                                                    snd (hmap (fst x + fst ?origin, snd x + snd ?origin)) - snd ?origin))"
      have hmap'_avoids: "\<forall>x. hmap' x \<noteq> (0::real, 0::real)"
      proof (intro allI)
        fix x :: "real \<times> real"
        let ?y = "(fst x + fst ?origin, snd x + snd ?origin)"
        have "hmap ?y \<noteq> ?origin" using hmap_avoids by (by100 blast)
        hence "fst (hmap ?y) - fst ?origin \<noteq> 0 \<or> snd (hmap ?y) - snd ?origin \<noteq> 0"
          by (cases "hmap ?y") (by100 auto)
        thus "hmap' x \<noteq> (0, 0)" unfolding hmap'_def by (by100 auto)
      qed
      have hmap'_cont: "continuous_on UNIV hmap'"
      proof -
        let ?T = "\<lambda>x::real\<times>real. (fst x + fst ?origin, snd x + snd ?origin)"
        have hT_cont: "continuous_on UNIV ?T"
          by (intro continuous_on_Pair continuous_on_add continuous_on_fst continuous_on_snd continuous_on_const continuous_on_id)
        have hcomp: "continuous_on UNIV (\<lambda>x. hmap (?T x))"
        proof -
          have "continuous_on UNIV (hmap \<circ> ?T)"
          proof (rule continuous_on_compose[OF hT_cont])
            have "?T ` UNIV = (UNIV :: (real\<times>real) set)"
            proof (rule set_eqI, rule iffI)
              fix y :: "real \<times> real" assume "y \<in> ?T ` UNIV" thus "y \<in> UNIV" by (by100 simp)
            next
              fix y :: "real \<times> real" assume "y \<in> UNIV"
              let ?x = "(fst y - fst ?origin, snd y - snd ?origin)"
              have "?T ?x = y" by (by100 simp)
              hence "y = ?T ?x" by (by100 simp)
              thus "y \<in> ?T ` UNIV" by (by100 blast)
            qed
            thus "continuous_on (?T ` UNIV) hmap" using hmap_cont_UNIV by (by100 simp)
          qed
          thus ?thesis unfolding comp_def .
        qed
        have hfst: "continuous_on UNIV (\<lambda>x. fst (hmap (?T x)))"
          by (rule continuous_on_fst[OF hcomp])
        have hsnd: "continuous_on UNIV (\<lambda>x. snd (hmap (?T x)))"
          by (rule continuous_on_snd[OF hcomp])
        show ?thesis unfolding hmap'_def
          by (intro continuous_on_Pair continuous_on_diff hfst hsnd continuous_on_const)
      qed
      have hmap'_fix: "\<forall>x. x \<notin> (\<lambda>p. (fst p - fst ?origin, snd p - snd ?origin)) ` ?C0 \<longrightarrow> hmap' x = x"
      proof (intro allI impI)
        fix x :: "real \<times> real"
        assume hx: "x \<notin> (\<lambda>p. (fst p - fst ?origin, snd p - snd ?origin)) ` ?C0"
        let ?y = "(fst x + fst ?origin, snd x + snd ?origin)"
        have "?y \<notin> ?C0"
        proof
          assume "?y \<in> ?C0"
          hence "(fst ?y - fst ?origin, snd ?y - snd ?origin) \<in> (\<lambda>p. (fst p - fst ?origin, snd p - snd ?origin)) ` ?C0"
            by (rule imageI)
          moreover have "(fst ?y - fst ?origin, snd ?y - snd ?origin) = x" by (by100 simp)
          ultimately show False using hx by (by100 simp)
        qed
        hence "hmap ?y = ?y" using hmap_id_outside by (by100 blast)
        thus "hmap' x = x" unfolding hmap'_def by (by100 simp)
      qed
      \<comment> \<open>The translated C0 is bounded (C0 bounded + translation).\<close>
      \<comment> \<open>Choose S' large enough, use standard retraction from Ch9_13.\<close>
      \<comment> \<open>T(C0) bounded: if x in C0, then T(x) = x - origin, and |x| \<le> S, |origin| \<le> S,
         so |T(x)| \<le> |x| + |origin| \<le> 2S. More precisely, work with CK_in_ball.\<close>
      have horigin_bnd: "(fst ?origin)\<^sup>2 + (snd ?origin)\<^sup>2 < S\<^sup>2"
        using hCK_in_ball horigin_C0 by (by100 blast)
      have hTC0_bounded: "\<forall>x\<in>(\<lambda>p. (fst p - fst ?origin, snd p - snd ?origin)) ` ?C0.
          (fst x)\<^sup>2 + (snd x)\<^sup>2 < (2*S)\<^sup>2"
      proof (intro ballI)
        fix x assume "x \<in> (\<lambda>p. (fst p - fst ?origin, snd p - snd ?origin)) ` ?C0"
        then obtain p where hp: "p \<in> ?C0" and hx_eq: "x = (fst p - fst ?origin, snd p - snd ?origin)"
          by (by100 blast)
        have hp_bnd: "(fst p)\<^sup>2 + (snd p)\<^sup>2 < S\<^sup>2"
          using hCK_in_ball hp by (by100 blast)
        \<comment> \<open>Key inequality: (a-b)^2 \<le> 2a^2 + 2b^2, since 0 \<le> (a+b)^2 = a^2 + 2ab + b^2.\<close>
        have hfst: "(fst p - fst ?origin)\<^sup>2 \<le> 2 * (fst p)\<^sup>2 + 2 * (fst ?origin)\<^sup>2"
        proof -
          have "0 \<le> (fst p + fst ?origin)\<^sup>2" by (by100 simp)
          moreover have "(fst p - fst ?origin)\<^sup>2 + (fst p + fst ?origin)\<^sup>2
              = 2 * (fst p)\<^sup>2 + 2 * (fst ?origin)\<^sup>2"
            by (by100 algebra)
          ultimately show ?thesis by (by100 linarith)
        qed
        have hsnd: "(snd p - snd ?origin)\<^sup>2 \<le> 2 * (snd p)\<^sup>2 + 2 * (snd ?origin)\<^sup>2"
        proof -
          have "0 \<le> (snd p + snd ?origin)\<^sup>2" by (by100 simp)
          moreover have "(snd p - snd ?origin)\<^sup>2 + (snd p + snd ?origin)\<^sup>2
              = 2 * (snd p)\<^sup>2 + 2 * (snd ?origin)\<^sup>2"
            by (by100 algebra)
          ultimately show ?thesis by (by100 linarith)
        qed
        have "(fst x)\<^sup>2 + (snd x)\<^sup>2 = (fst p - fst ?origin)\<^sup>2 + (snd p - snd ?origin)\<^sup>2"
          using hx_eq by (by100 simp)
        also have "\<dots> \<le> (2 * (fst p)\<^sup>2 + 2 * (fst ?origin)\<^sup>2) + (2 * (snd p)\<^sup>2 + 2 * (snd ?origin)\<^sup>2)"
          using hfst hsnd by (by100 linarith)
        also have "\<dots> = 2 * ((fst p)\<^sup>2 + (snd p)\<^sup>2) + 2 * ((fst ?origin)\<^sup>2 + (snd ?origin)\<^sup>2)"
          by (by100 algebra)
        also have "\<dots> < 2 * S\<^sup>2 + 2 * S\<^sup>2"
        proof -
          have "2 * ((fst p)\<^sup>2 + (snd p)\<^sup>2) < 2 * S\<^sup>2"
            using hp_bnd by (by100 simp)
          moreover have "2 * ((fst ?origin)\<^sup>2 + (snd ?origin)\<^sup>2) < 2 * S\<^sup>2"
            using horigin_bnd by (by100 simp)
          ultimately show ?thesis by (by100 linarith)
        qed
        also have "\<dots> = (2*S)\<^sup>2" by (by100 algebra)
        finally show "(fst x)\<^sup>2 + (snd x)\<^sup>2 < (2*S)\<^sup>2" .
      qed
      \<comment> \<open>For |x| \<ge> 2*S: x not in T(C0), so hmap'(x) = x.\<close>
      have hmap'_fix_outside: "\<forall>x. (fst x)\<^sup>2 + (snd x)\<^sup>2 \<ge> (2*S)\<^sup>2 \<longrightarrow> hmap' x = x"
      proof (intro allI impI)
        fix x :: "real \<times> real" assume hx: "(fst x)\<^sup>2 + (snd x)\<^sup>2 \<ge> (2*S)\<^sup>2"
        have "x \<notin> (\<lambda>p. (fst p - fst ?origin, snd p - snd ?origin)) ` ?C0"
        proof
          assume "x \<in> (\<lambda>p. (fst p - fst ?origin, snd p - snd ?origin)) ` ?C0"
          hence "(fst x)\<^sup>2 + (snd x)\<^sup>2 < (2*S)\<^sup>2" using hTC0_bounded by (by100 blast)
          with hx show False by (by100 linarith)
        qed
        thus "hmap' x = x" using hmap'_fix by (by100 blast)
      qed
      \<comment> \<open>Radial projection + scaling retraction.\<close>
      let ?norm = "\<lambda>x::real\<times>real. sqrt (fst x ^ 2 + snd x ^ 2)"
      let ?r = "\<lambda>x::real\<times>real. (fst x / ?norm x, snd x / ?norm x)"
      let ?S' = "2 * S"
      let ?ret = "\<lambda>x::real\<times>real. ?r (hmap' (?S' * fst x, ?S' * snd x))"
      have hS'_pos: "?S' > 0" using hS_pos by (by100 linarith)
      \<comment> \<open>ret maps B^2 into S^1 (r normalizes any nonzero vector to norm 1).\<close>
      have hret_maps: "\<forall>x\<in>top1_B2. ?ret x \<in> top1_S1"
      proof (intro ballI)
        fix x :: "real \<times> real" assume "x \<in> top1_B2"
        let ?y = "hmap' (?S' * fst x, ?S' * snd x)"
        define y where "y = hmap' (?S' * fst x, ?S' * snd x)"
        have hy_ne: "y \<noteq> (0::real, 0::real)" using hmap'_avoids unfolding y_def by (by100 blast)
        hence hpos: "fst y ^ 2 + snd y ^ 2 > 0"
          by (cases y) (auto simp: sum_power2_gt_zero_iff)
        define n where "n = sqrt (fst y ^ 2 + snd y ^ 2)"
        have hn_pos: "n > 0" unfolding n_def by (rule real_sqrt_gt_zero[OF hpos])
        have hn_sq: "n ^ 2 = fst y ^ 2 + snd y ^ 2" unfolding n_def
          using hpos by (by100 simp)
        have hret_eq: "?ret x = (fst y / n, snd y / n)" unfolding y_def n_def by (by100 simp)
        have "(fst y / n) ^ 2 + (snd y / n) ^ 2 = 1"
        proof -
          have "(fst y / n) ^ 2 + (snd y / n) ^ 2 = fst y ^ 2 / n ^ 2 + snd y ^ 2 / n ^ 2"
            unfolding power_divide ..
          also have "\<dots> = (fst y ^ 2 + snd y ^ 2) / n ^ 2"
            by (rule add_divide_distrib[symmetric])
          also have "\<dots> = n ^ 2 / n ^ 2" using hn_sq by (by100 simp)
          also have "\<dots> = 1" using hn_pos by (by100 simp)
          finally show ?thesis .
        qed
        thus "?ret x \<in> top1_S1" unfolding top1_S1_def hret_eq by (by100 simp)
      qed
      \<comment> \<open>ret fixes S^1.\<close>
      have hret_fix: "\<forall>x\<in>top1_S1. ?ret x = x"
      proof (intro ballI)
        fix x :: "real \<times> real" assume hx: "x \<in> top1_S1"
        hence hx_eq: "(fst x)^2 + (snd x)^2 = 1" unfolding top1_S1_def by (by100 simp)
        \<comment> \<open>S'*x has norm S' since |x|=1.\<close>
        have "(?S' * fst x)^2 + (?S' * snd x)^2 = ?S'^2"
        proof -
          have "(?S' * fst x)^2 = ?S'^2 * (fst x)^2" unfolding power_mult_distrib by (by100 simp)
          moreover have "(?S' * snd x)^2 = ?S'^2 * (snd x)^2" unfolding power_mult_distrib by (by100 simp)
          ultimately have "(?S' * fst x)^2 + (?S' * snd x)^2 = ?S'^2 * ((fst x)^2 + (snd x)^2)"
            using distrib_left[of "?S'^2" "(fst x)^2" "(snd x)^2"] by (by100 linarith)
          also have "\<dots> = ?S'^2" using hx_eq by (by100 simp)
          finally show ?thesis .
        qed
        hence "(fst (?S' * fst x, ?S' * snd x))\<^sup>2 + (snd (?S' * fst x, ?S' * snd x))\<^sup>2 \<ge> ?S'\<^sup>2"
          by (by100 simp)
        hence "hmap' (?S' * fst x, ?S' * snd x) = (?S' * fst x, ?S' * snd x)"
          using spec[OF hmap'_fix_outside, of "(?S' * fst x, ?S' * snd x)"] by (by100 blast)
        hence "?ret x = ?r (?S' * fst x, ?S' * snd x)" by (by100 simp)
        also have "\<dots> = x"
        proof -
          have hnorm: "?norm (?S' * fst x, ?S' * snd x) = ?S'"
          proof -
            have "(?S' * fst x)^2 + (?S' * snd x)^2 = ?S'^2"
              using \<open>(?S' * fst x)^2 + (?S' * snd x)^2 = ?S'^2\<close> .
            hence "sqrt ((?S' * fst x)^2 + (?S' * snd x)^2) = sqrt (?S'^2)" by (by100 simp)
            also have "\<dots> = \<bar>?S'\<bar>" using real_sqrt_abs by (by100 metis)
            also have "\<dots> = ?S'" using hS'_pos by (by100 simp)
            finally show ?thesis by (by100 simp)
          qed
          have "?r (?S' * fst x, ?S' * snd x) = (?S' * fst x / ?S', ?S' * snd x / ?S')"
            using hnorm by (by100 simp)
          also have "\<dots> = (fst x, snd x)" using hS'_pos by (by100 simp)
          also have "\<dots> = x" by (by100 simp)
          finally show ?thesis .
        qed
        finally show "?ret x = x" .
      qed
      \<comment> \<open>ret continuous on B^2.\<close>
      have hret_cont: "continuous_on top1_B2 ?ret"
      proof -
        \<comment> \<open>Step 1: Scaling continuous.\<close>
        have hscale_cont: "continuous_on top1_B2 (\<lambda>x::real\<times>real. (?S' * fst x, ?S' * snd x))"
          by (intro continuous_on_Pair continuous_on_mult continuous_on_const
              continuous_on_fst continuous_on_snd continuous_on_id)
        \<comment> \<open>Step 2: hmap' continuous on UNIV, hence on any subset.\<close>
        have hmap'_cont_sub: "continuous_on ((\<lambda>x. (?S' * fst x, ?S' * snd x)) ` top1_B2) hmap'"
          using continuous_on_subset[OF hmap'_cont] by (by100 blast)
        \<comment> \<open>Step 3: Compose scaling + hmap'.\<close>
        have hcomp: "continuous_on top1_B2 (\<lambda>x. hmap' (?S' * fst x, ?S' * snd x))"
        proof (rule continuous_on_compose2[OF hmap'_cont_sub hscale_cont])
          show "(\<lambda>x::real\<times>real. (?S' * fst x, ?S' * snd x)) ` top1_B2
              \<subseteq> (\<lambda>x. (?S' * fst x, ?S' * snd x)) ` top1_B2" ..
        qed
        \<comment> \<open>Step 4: Radial projection continuous on R^2-{0}.\<close>
        have hr_cont: "continuous_on (UNIV - {(0::real, 0)}) ?r"
        proof (rule continuous_on_Pair)
          have hnorm_cont: "continuous_on (UNIV - {(0::real, 0)}) ?norm"
            by (intro continuous_on_compose2[OF continuous_on_real_sqrt]
                continuous_on_add continuous_on_power
                continuous_on_fst continuous_on_snd continuous_on_id) (by100 auto)
          have hnorm_nz: "\<forall>x\<in>UNIV - {(0::real, 0)}. ?norm x \<noteq> 0"
          proof (intro ballI)
            fix x :: "real \<times> real" assume "x \<in> UNIV - {(0, 0)}"
            hence "x \<noteq> (0, 0)" by (by100 blast)
            hence "fst x ^ 2 + snd x ^ 2 > 0"
              by (cases x) (auto simp: sum_power2_gt_zero_iff)
            hence "?norm x > 0" by (rule real_sqrt_gt_zero)
            thus "?norm x \<noteq> 0" by (by100 linarith)
          qed
          have hfst_cont: "continuous_on (UNIV - {(0::real, 0)}) fst"
            by (intro continuous_intros)
          have hsnd_cont: "continuous_on (UNIV - {(0::real, 0)}) snd"
            by (intro continuous_intros)
          show "continuous_on (UNIV - {(0, 0)}) (\<lambda>x. fst x / ?norm x)"
            by (rule continuous_on_divide[OF hfst_cont hnorm_cont hnorm_nz])
          show "continuous_on (UNIV - {(0, 0)}) (\<lambda>x. snd x / ?norm x)"
            by (rule continuous_on_divide[OF hsnd_cont hnorm_cont hnorm_nz])
        qed
        \<comment> \<open>Step 5: Image of hmap' avoids (0,0).\<close>
        have himg_sub: "(\<lambda>x. hmap' (?S' * fst x, ?S' * snd x)) ` top1_B2 \<subseteq> UNIV - {(0, 0)}"
        proof (rule subsetI)
          fix y assume "y \<in> (\<lambda>x. hmap' (?S' * fst x, ?S' * snd x)) ` top1_B2"
          then obtain x where "x \<in> top1_B2" and "y = hmap' (?S' * fst x, ?S' * snd x)"
            by (by100 blast)
          have "hmap' (?S' * fst x, ?S' * snd x) \<noteq> (0, 0)" using hmap'_avoids by (by100 blast)
          hence "y \<noteq> (0, 0)" using \<open>y = hmap' (?S' * fst x, ?S' * snd x)\<close> by (by100 simp)
          thus "y \<in> UNIV - {(0, 0)}" by (by100 simp)
        qed
        \<comment> \<open>Step 6: Compose all three.\<close>
        have hr_cont_sub: "continuous_on ((\<lambda>x. hmap' (?S' * fst x, ?S' * snd x)) ` top1_B2) ?r"
          using continuous_on_subset[OF hr_cont himg_sub] .
        show ?thesis by (rule continuous_on_compose2[OF hr_cont_sub hcomp subset_refl])
      qed
      \<comment> \<open>Bridge to top1_retract_of_on.\<close>
      have hretract: "top1_retract_of_on top1_B2 top1_B2_topology top1_S1"
      proof -
        have hS1_B2: "top1_S1 \<subseteq> top1_B2" unfolding top1_S1_def top1_B2_def by (by100 auto)
        have hret_top1: "top1_continuous_map_on top1_B2
            (subspace_topology UNIV ?TR2 top1_B2)
            top1_S1 (subspace_topology UNIV ?TR2 top1_S1) ?ret"
          by (rule top1_continuous_map_on_real2_subspace_general)
             (use hret_maps in \<open>by100 blast\<close>, rule hret_cont)
        have hB2_eq: "subspace_topology UNIV ?TR2 top1_B2 = top1_B2_topology"
          unfolding top1_B2_topology_def ..
        have hS1_eq: "subspace_topology UNIV ?TR2 top1_S1
            = subspace_topology top1_B2 top1_B2_topology top1_S1"
          unfolding top1_B2_topology_def using subspace_topology_trans[OF hS1_B2] by (by100 simp)
        have "top1_continuous_map_on top1_B2 top1_B2_topology
            top1_S1 (subspace_topology top1_B2 top1_B2_topology top1_S1) ?ret"
          using hret_top1 unfolding hB2_eq hS1_eq .
        thus ?thesis unfolding top1_retract_of_on_def top1_is_retraction_on_def
          using hS1_B2 hret_fix by (by100 blast)
      qed
      show False using hretract Theorem_55_2_no_retraction by (by100 blast)
    qed
  qed
  \<comment> \<open>Transfer back to S^2 via h^{-1}.\<close>
  \<comment> \<open>Transfer from R^2 to S^2. The key: h^{-1}(C0) \<union> {b} is connected in S^2-f(A).\<close>
  show ?thesis
  proof -
    obtain C0 where hC0: "C0 \<in> top1_components_on (UNIV - ?K) (subspace_topology UNIV ?TR2 (UNIV - ?K))"
        and horigin_in: "?origin \<in> C0"
        and hunbnd: "\<forall>R>0. \<exists>x\<in>C0. R\<^sup>2 < (fst x)\<^sup>2 + (snd x)\<^sup>2"
      using hR2_claim by (by100 blast)
    \<comment> \<open>h^{-1} maps C0 into S^2-{b}-f(A). a = h^{-1}(origin) \<in> h^{-1}(C0).\<close>
    let ?hinv = "inv_into (?S2 - {b}) h"
    have hinv_cont: "top1_continuous_map_on (UNIV::(real\<times>real) set) ?TR2
        (?S2 - {b}) (subspace_topology ?S2 ?TS2 (?S2 - {b})) ?hinv"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    \<comment> \<open>h^{-1}(C0) \<subseteq> S^2-{b}-f(A) and connected.\<close>
    have hC0_sub: "C0 \<subseteq> UNIV - ?K" using hC0
      unfolding top1_components_on_def top1_component_of_on_def by (by100 blast)
    \<comment> \<open>h^{-1}(C0) \<union> {b} is connected in S^2-f(A) and contains both a and b.
       Connectedness: every open nbhd of b in S^2 meets h^{-1}(C0) since C0 is unbounded.
       In stereographic: nbhd of b = complement of compact in R^2, which C0 intersects.\<close>
    have "\<exists>D. top1_connected_on D (subspace_topology ?S2 ?TS2 D) \<and> D \<subseteq> ?S2 - f ` A
        \<and> a \<in> D \<and> b \<in> D"
    proof (intro exI[of _ "?hinv ` C0 \<union> {b}"] conjI)
      let ?D = "?hinv ` C0 \<union> {b}"
      \<comment> \<open>D connected: h^{-1}(C0) connected, b in closure, Theorem_23_4.\<close>
      show "top1_connected_on ?D (subspace_topology ?S2 ?TS2 ?D)"
      proof -
        have hTopS2: "is_topology_on ?S2 ?TS2"
          using hT unfolding is_topology_on_strict_def by (by100 blast)
        \<comment> \<open>Step 1: h^{-1}(C0) connected.\<close>
        have hinvC0_conn: "top1_connected_on (?hinv ` C0) (subspace_topology ?S2 ?TS2 (?hinv ` C0))"
        proof -
          have hTR2: "is_topology_on (UNIV::(real\<times>real) set) ?TR2"
            using product_topology_on_is_topology_on[OF
              top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by (by100 simp)
          let ?T_UK = "subspace_topology UNIV ?TR2 (UNIV - ?K)"
          have hT_UK: "is_topology_on (UNIV - ?K) ?T_UK"
            by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
          \<comment> \<open>C0 connected: component of UNIV-K is connected (Theorem 25.1).\<close>
          obtain x where hxUK: "x \<in> UNIV - ?K" and hC0eq: "C0 = top1_component_of_on (UNIV - ?K) ?T_UK x"
            using hC0 unfolding top1_components_on_def by (by100 blast)
          have hC0_conn_UK: "top1_connected_on C0 (subspace_topology (UNIV - ?K) ?T_UK C0)"
            unfolding hC0eq by (rule top1_component_of_on_connected[OF hT_UK hxUK])
          have hC0_conn: "top1_connected_on C0 (subspace_topology UNIV ?TR2 C0)"
            using hC0_conn_UK unfolding subspace_topology_trans[OF hC0_sub] .
          \<comment> \<open>Restrict hinv to C0, apply Theorem_23_5.\<close>
          have hinv_C0: "top1_continuous_map_on C0 (subspace_topology UNIV ?TR2 C0)
              (?S2 - {b}) (subspace_topology ?S2 ?TS2 (?S2 - {b})) ?hinv"
            by (rule top1_continuous_map_on_restrict_domain_simple[OF hinv_cont]) (by100 simp)
          have hTC0: "is_topology_on C0 (subspace_topology UNIV ?TR2 C0)"
            by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
          have hTS2b: "is_topology_on (?S2 - {b}) (subspace_topology ?S2 ?TS2 (?S2 - {b}))"
            by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
          have himg_conn: "top1_connected_on (?hinv ` C0)
              (subspace_topology (?S2 - {b}) (subspace_topology ?S2 ?TS2 (?S2 - {b})) (?hinv ` C0))"
            by (rule Theorem_23_5[OF hTC0 hTS2b hC0_conn hinv_C0])
          \<comment> \<open>Subspace transitivity.\<close>
          have hinvC0_sub_S2b: "?hinv ` C0 \<subseteq> ?S2 - {b}"
          proof (rule image_subsetI)
            fix c assume "c \<in> C0"
            thus "?hinv c \<in> ?S2 - {b}"
              using hinv_cont unfolding top1_continuous_map_on_def by (by100 blast)
          qed
          have "subspace_topology (?S2 - {b}) (subspace_topology ?S2 ?TS2 (?S2 - {b})) (?hinv ` C0)
              = subspace_topology ?S2 ?TS2 (?hinv ` C0)"
            by (rule subspace_topology_trans[OF hinvC0_sub_S2b])
          with himg_conn show ?thesis by (by100 simp)
        qed
        \<comment> \<open>Step 2: h^{-1}(C0) \<subseteq> S^2.\<close>
        have hinvC0_sub: "?hinv ` C0 \<subseteq> ?S2"
        proof (rule subsetI)
          fix x assume "x \<in> ?hinv ` C0"
          then obtain c where "c \<in> C0" and "x = ?hinv c" by (by100 blast)
          have "?hinv c \<in> ?S2 - {b}"
            using hinv_cont \<open>c \<in> C0\<close> unfolding top1_continuous_map_on_def by (by100 blast)
          thus "x \<in> ?S2" using \<open>x = ?hinv c\<close> by (by100 blast)
        qed
        \<comment> \<open>Step 3: b in closure of h^{-1}(C0) in S^2.\<close>
        have hb_closure: "b \<in> closure_on ?S2 ?TS2 (?hinv ` C0)"
        proof (rule iffD2[OF Theorem_17_5a[OF hTopS2 hb hinvC0_sub]])
          \<comment> \<open>Show: every neighborhood of b intersects hinv(C0).\<close>
          show "\<forall>U. neighborhood_of b ?S2 ?TS2 U \<longrightarrow> intersects U (?hinv ` C0)"
          proof (intro allI impI)
            fix U assume hU: "neighborhood_of b ?S2 ?TS2 U"
            hence hU_open: "U \<in> ?TS2" and hb_U: "b \<in> U"
              unfolding neighborhood_of_def by (by100 blast)+
            \<comment> \<open>S^2 - U is closed in S^2, S^2 compact \<Longrightarrow> S^2 - U compact in S^2.\<close>
            \<comment> \<open>S^2 - U \<subseteq> S^2 - {b}, h maps it to R^2. Image is compact, hence bounded.\<close>
            \<comment> \<open>C0 unbounded \<Longrightarrow> C0 not contained in image. Get c \<in> C0 - h(S^2-U).\<close>
            \<comment> \<open>Then hinv(c) \<in> U \<inter> hinv(C0).\<close>
            \<comment> \<open>S^2 compact (top1_compact_on).\<close>
            have hS2_compact: "top1_compact_on ?S2 ?TS2"
            proof -
              have "?TS2 = subspace_topology UNIV (top1_open_sets :: (real \<times> real \<times> real) set set) ?S2"
                unfolding top1_S2_topology_def
                using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                      product_topology_on_open_sets[where ?'a=real and ?'b=real] by (by100 simp)
              hence "top1_compact_on ?S2 ?TS2 = compact ?S2"
                using top1_compact_on_subspace_UNIV_iff_compact[of ?S2] by (by100 simp)
              thus ?thesis using S2_compact_standard by (by100 simp)
            qed
            \<comment> \<open>S^2-U closed in S^2, hence compact.\<close>
            have hU_sub_S2: "U \<subseteq> ?S2"
              using hT hU_open unfolding is_topology_on_strict_def
              by (by100 fast)
            have hS2U_closed: "closedin_on ?S2 ?TS2 (?S2 - U)"
            proof -
              have "?S2 - (?S2 - U) = U" using hU_sub_S2 by (by100 blast)
              thus ?thesis unfolding closedin_on_def using hU_open by (by100 simp)
            qed
            have hS2U_compact: "top1_compact_on (?S2 - U) (subspace_topology ?S2 ?TS2 (?S2 - U))"
              by (rule Theorem_26_2[OF hS2_compact hS2U_closed])
            \<comment> \<open>S^2-U \<subseteq> S^2-{b}, h maps it to a compact subset of R^2.\<close>
            have hS2U_sub: "?S2 - U \<subseteq> ?S2 - {b}" using hb_U by (by100 blast)
            \<comment> \<open>h(S^2-U) compact in R^2. Compact in R^2 \<Longrightarrow> bounded.\<close>
            \<comment> \<open>C0 unbounded: \<exists>c \<in> C0 not in h(S^2-U).\<close>
            have "\<exists>c\<in>C0. c \<notin> h ` (?S2 - U)"
            proof -
              \<comment> \<open>Step A: h restricted to S^2-U is continuous.\<close>
              have hh_cont: "top1_continuous_map_on (?S2 - {b})
                  (subspace_topology ?S2 ?TS2 (?S2 - {b}))
                  (UNIV::(real\<times>real) set) ?TR2 h"
                using hh unfolding top1_homeomorphism_on_def by (by100 blast)
              have hh_restr: "top1_continuous_map_on (?S2 - U)
                  (subspace_topology (?S2 - {b}) (subspace_topology ?S2 ?TS2 (?S2 - {b})) (?S2 - U))
                  (UNIV::(real\<times>real) set) ?TR2 h"
                by (rule top1_continuous_map_on_restrict_domain_simple[OF hh_cont hS2U_sub])
              \<comment> \<open>Step B: Subspace topology transitivity.\<close>
              have hsub_eq: "subspace_topology (?S2 - {b}) (subspace_topology ?S2 ?TS2 (?S2 - {b})) (?S2 - U)
                  = subspace_topology ?S2 ?TS2 (?S2 - U)"
                by (rule subspace_topology_trans[OF hS2U_sub])
              have hh_restr2: "top1_continuous_map_on (?S2 - U)
                  (subspace_topology ?S2 ?TS2 (?S2 - U))
                  (UNIV::(real\<times>real) set) ?TR2 h"
                using hh_restr unfolding hsub_eq .
              \<comment> \<open>Step C: h(S^2-U) is compact in R^2 (top1 sense).\<close>
              have hTR2: "is_topology_on (UNIV::(real\<times>real) set) ?TR2"
                using product_topology_on_is_topology_on[OF
                  top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by (by100 simp)
              have hTS2U: "is_topology_on (?S2 - U) (subspace_topology ?S2 ?TS2 (?S2 - U))"
                by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
              have himg_compact: "top1_compact_on (h ` (?S2 - U))
                  (subspace_topology UNIV ?TR2 (h ` (?S2 - U)))"
                by (rule Theorem_26_5[OF hTS2U hTR2 hS2U_compact hh_restr2])
              \<comment> \<open>Step D: Bridge to HOL compact, then bounded via continuous_attains_sup.\<close>
              have hTR2_eq: "?TR2 = (top1_open_sets :: (real\<times>real) set set)"
                using product_topology_on_open_sets_real2 by (by100 metis)
              have himg_HOL_compact: "compact (h ` (?S2 - U))"
                using himg_compact top1_compact_on_subspace_UNIV_iff_compact[of "h ` (?S2 - U)"]
                unfolding hTR2_eq by (by100 simp)
              \<comment> \<open>Step E: h(S^2-U) bounded.\<close>
              have "\<exists>M. \<forall>y\<in>h ` (?S2 - U). (fst y)\<^sup>2 + (snd y)\<^sup>2 \<le> M"
              proof (cases "h ` (?S2 - U) = {}")
                case True thus ?thesis by (by100 blast)
              next
                case False
                have "continuous_on (h ` (?S2 - U)) (\<lambda>y::(real\<times>real). (fst y)\<^sup>2 + (snd y)\<^sup>2)"
                  by (intro continuous_intros)
                from continuous_attains_sup[OF himg_HOL_compact False this]
                obtain y0 where "y0 \<in> h ` (?S2 - U)"
                    and "\<forall>y\<in>h ` (?S2 - U). (fst y)\<^sup>2 + (snd y)\<^sup>2 \<le> (fst y0)\<^sup>2 + (snd y0)\<^sup>2"
                  by (by100 blast)
                thus ?thesis by (by100 blast)
              qed
              then obtain M where hM: "\<forall>y\<in>h ` (?S2 - U). (fst y)\<^sup>2 + (snd y)\<^sup>2 \<le> M"
                by (by100 blast)
              \<comment> \<open>Step F: C0 unbounded \<Longrightarrow> c \<in> C0 outside the bound.\<close>
              obtain c where "c \<in> C0" and "(fst c)\<^sup>2 + (snd c)\<^sup>2 > max M 0"
              proof -
                have "max M 0 \<ge> 0" by (by100 simp)
                have "sqrt (max M 0) + 1 > 0" using real_sqrt_ge_zero[of "max M 0"] by (by100 linarith)
                from hunbnd[THEN spec[of _ "sqrt (max M 0) + 1"], THEN mp[OF _ this]]
                obtain c where "c \<in> C0" and "(sqrt (max M 0) + 1)\<^sup>2 < (fst c)\<^sup>2 + (snd c)\<^sup>2"
                  by (by100 blast)
                moreover have "(sqrt (max M 0) + 1)\<^sup>2 > max M 0"
                proof -
                  have "sqrt (max M 0) \<ge> 0" using real_sqrt_ge_zero[of "max M 0"] by (by100 linarith)
                  have "(sqrt (max M 0) + 1)\<^sup>2 = (sqrt (max M 0))\<^sup>2 + 2 * sqrt (max M 0) + 1"
                    by (by100 algebra)
                  moreover have "(sqrt (max M 0))\<^sup>2 = max M 0"
                    using real_sqrt_pow2[of "max M 0"] by (by100 simp)
                  ultimately have "(sqrt (max M 0) + 1)\<^sup>2 = max M 0 + 2 * sqrt (max M 0) + 1"
                    by (by100 linarith)
                  thus ?thesis using \<open>sqrt (max M 0) \<ge> 0\<close> by (by100 linarith)
                qed
                ultimately have "(fst c)\<^sup>2 + (snd c)\<^sup>2 > max M 0" by (by100 linarith)
                thus ?thesis using that \<open>c \<in> C0\<close> by (by100 blast)
              qed
              hence "c \<notin> h ` (?S2 - U)"
                using hM by (by100 force)
              thus ?thesis using \<open>c \<in> C0\<close> by (by100 blast)
            qed
            then obtain c where hcC0: "c \<in> C0" and hc_out: "c \<notin> h ` (?S2 - U)"
              by (by100 blast)
            \<comment> \<open>hinv(c) \<in> S^2-{b} and hinv(c) \<notin> S^2-U, so hinv(c) \<in> U.\<close>
            have "?hinv c \<in> ?S2 - {b}"
              using hinv_cont hcC0 unfolding top1_continuous_map_on_def by (by100 blast)
            have "?hinv c \<notin> ?S2 - U"
            proof
              assume "?hinv c \<in> ?S2 - U"
              hence "h (?hinv c) \<in> h ` (?S2 - U)" by (by100 blast)
              moreover have "h (?hinv c) = c"
              proof -
                have hsurj: "h ` (?S2 - {b}) = (UNIV::(real\<times>real) set)"
                  using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
                have "c \<in> h ` (?S2 - {b})" using hsurj by (by100 blast)
                thus ?thesis by (rule f_inv_into_f)
              qed
              ultimately show False using hc_out by (by100 simp)
            qed
            hence "?hinv c \<in> U" using \<open>?hinv c \<in> ?S2 - {b}\<close> by (by100 blast)
            moreover have "?hinv c \<in> ?hinv ` C0" using hcC0 by (by100 blast)
            ultimately show "intersects U (?hinv ` C0)"
              unfolding intersects_def by (by100 blast)
          qed
        qed
        \<comment> \<open>Step 4: Apply Theorem_23_4: A \<subseteq> B \<subseteq> closure(A), A connected \<Longrightarrow> B connected.\<close>
        have hD_sub_S2: "?D \<subseteq> ?S2" using hinvC0_sub hb by (by100 blast)
        have hA_sub_D: "?hinv ` C0 \<subseteq> ?D" by (by100 blast)
        have hD_sub_cl: "?D \<subseteq> closure_on ?S2 ?TS2 (?hinv ` C0)"
          using subset_closure_on[of "?hinv ` C0" ?S2 ?TS2] hinvC0_sub hb_closure
          by (by100 blast)
        show ?thesis
          by (rule Theorem_23_4[OF hTopS2 hinvC0_sub hD_sub_S2 hA_sub_D hD_sub_cl hinvC0_conn])
      qed
      \<comment> \<open>D \<subseteq> S^2 - f(A).\<close>
      show "?D \<subseteq> ?S2 - f ` A"
      proof (rule subsetI)
        fix x assume "x \<in> ?D"
        hence "x \<in> ?hinv ` C0 \<or> x = b" by (by100 blast)
        thus "x \<in> ?S2 - f ` A"
        proof
          assume "x \<in> ?hinv ` C0"
          then obtain c where hc: "c \<in> C0" and hxc: "x = ?hinv c" by (by100 blast)
          \<comment> \<open>c \<in> C0 \<subseteq> UNIV-K, so h^{-1}(c) \<in> S^2-{b}-f(A).\<close>
          have "c \<in> UNIV - ?K" using hC0_sub hc by (by100 blast)
          \<comment> \<open>hinv maps UNIV to S^2-{b}.\<close>
          have "?hinv c \<in> ?S2 - {b}"
            using hinv_cont hc unfolding top1_continuous_map_on_def by (by100 blast)
          moreover have "?hinv c \<notin> f ` A"
          proof
            assume "?hinv c \<in> f ` A"
            then obtain y where "y \<in> A" and "f y = ?hinv c" by (by100 auto)
            hence "h (f y) = h (?hinv c)" by (by100 simp)
            \<comment> \<open>h(h^{-1}(c)) = c since c \<in> UNIV = range h.\<close>
            have hsurj: "h ` (?S2 - {b}) = (UNIV::(real\<times>real) set)"
              using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
            hence "c \<in> h ` (?S2 - {b})" by (by100 blast)
            hence "h (?hinv c) = c"
              by (rule f_inv_into_f)
            hence "h (f y) = c" using \<open>f y = ?hinv c\<close> by (by100 simp)
            hence "c = (h \<circ> f) y" unfolding comp_def by (by100 simp)
            hence "c \<in> ?K" using \<open>y \<in> A\<close> by (by100 blast)
            with \<open>c \<in> UNIV - ?K\<close> show False by (by100 blast)
          qed
          ultimately have "?hinv c \<in> ?S2 - f ` A" by (by100 blast)
          thus "x \<in> ?S2 - f ` A" using hxc by (by100 simp)
        next
          assume "x = b"
          have "f ` A \<subseteq> ?S2 - {a, b}"
            using hf unfolding top1_continuous_map_on_def by (by100 blast)
          hence "b \<notin> f ` A" by (by100 blast)
          thus "x \<in> ?S2 - f ` A" using \<open>x = b\<close> hb by (by100 blast)
        qed
      qed
      \<comment> \<open>a \<in> D: a = h^{-1}(origin) \<in> h^{-1}(C0) since origin \<in> C0.\<close>
      show "a \<in> ?D"
      proof -
        have "a \<in> ?S2 - {b}" using ha hab by (by100 blast)
        have hinj: "inj_on h (?S2 - {b})"
          using hh unfolding top1_homeomorphism_on_def bij_betw_def
          by (by100 blast)
        have "?hinv ?origin = a"
          by (rule inv_into_f_f[OF hinj \<open>a \<in> ?S2 - {b}\<close>])
        moreover have "?origin \<in> C0" by (rule horigin_in)
        ultimately have "a \<in> ?hinv ` C0"
          by (by100 force)
        thus ?thesis by (by100 blast)
      qed
      \<comment> \<open>b \<in> D: by construction.\<close>
      show "b \<in> ?D" by (by100 blast)
    qed
    then obtain D where hDconn: "top1_connected_on D (subspace_topology ?S2 ?TS2 D)"
        and hD_sub: "D \<subseteq> ?S2 - f ` A" and ha_D: "a \<in> D" and hb_D: "b \<in> D"
      by (by100 blast)
    \<comment> \<open>D is contained in some component of S^2-f(A), which also contains a and b.\<close>
    let ?C = "top1_component_of_on (?S2 - f ` A) (subspace_topology ?S2 ?TS2 (?S2 - f ` A)) a"
    have ha_in_S2fA: "a \<in> ?S2 - f ` A"
    proof -
      have "f ` A \<subseteq> ?S2 - {a, b}" using hf unfolding top1_continuous_map_on_def by (by100 blast)
      thus ?thesis using ha by (by100 blast)
    qed
    have hT_S2fA: "is_topology_on (?S2 - f ` A) (subspace_topology ?S2 ?TS2 (?S2 - f ` A))"
    proof -
      have hTopS2: "is_topology_on ?S2 ?TS2" using hT unfolding is_topology_on_strict_def by (by100 blast)
      show ?thesis by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
    qed
    have ha_C: "a \<in> ?C" by (rule top1_component_of_on_self_mem[OF hT_S2fA ha_in_S2fA])
    \<comment> \<open>b is in the same component as a (since D connects them).\<close>
    have hb_C: "b \<in> ?C"
    proof -
      \<comment> \<open>D is a connected set containing a, so D \<subseteq> component_of a.\<close>
      have "D \<subseteq> ?C"
        unfolding top1_component_of_on_def
      proof (rule Union_upper)
        show "D \<in> {C. C \<subseteq> ?S2 - f ` A \<and> a \<in> C \<and> top1_connected_on C (subspace_topology (?S2 - f ` A) (subspace_topology ?S2 ?TS2 (?S2 - f ` A)) C)}"
        proof -
          have "D \<subseteq> ?S2 - f ` A" by (rule hD_sub)
          moreover have "a \<in> D" by (rule ha_D)
          moreover have "top1_connected_on D (subspace_topology (?S2 - f ` A) (subspace_topology ?S2 ?TS2 (?S2 - f ` A)) D)"
          proof -
            have "subspace_topology (?S2 - f ` A) (subspace_topology ?S2 ?TS2 (?S2 - f ` A)) D
                = subspace_topology ?S2 ?TS2 D"
              by (rule subspace_topology_trans[OF hD_sub])
            thus ?thesis using hDconn by (by100 simp)
          qed
          ultimately show ?thesis by (by100 blast)
        qed
      qed
      thus ?thesis using hb_D by (by100 blast)
    qed
    have hC_comp: "?C \<in> top1_components_on (?S2 - f ` A) (subspace_topology ?S2 ?TS2 (?S2 - f ` A))"
      unfolding top1_components_on_def using ha_in_S2fA by (by100 blast)
    show ?thesis using hC_comp ha_C hb_C by (by100 blast)
  qed
qed

text \<open>Define frontier (boundary) for the standard euclidean topology.
  HOL-Analysis is not imported, so frontier_def is unavailable.
  We define it here using closure and interior from HOL's topological_space class.\<close>

definition frontier :: "'a::topological_space set \<Rightarrow> 'a set" where
  "frontier S = {x. (\<forall>U. open U \<longrightarrow> x \<in> U \<longrightarrow> U \<inter> S \<noteq> {}) \<and>
                     (\<forall>U. open U \<longrightarrow> x \<in> U \<longrightarrow> U \<inter> (- S) \<noteq> {})}"

lemma frontier_closed_sub: "closed (S :: 'a::topological_space set) \<Longrightarrow> frontier S \<subseteq> S"
proof
  fix x assume hcl: "closed S" and hx: "x \<in> frontier S"
  show "x \<in> S"
  proof (rule ccontr)
    assume "x \<notin> S"
    hence "x \<in> - S" by (by100 blast)
    have "open (- S)" using hcl by (rule open_Compl)
    have "(-S) \<inter> S \<noteq> {}"
      using hx \<open>open (- S)\<close> \<open>x \<in> - S\<close> unfolding frontier_def by (by100 blast)
    thus False by (by100 blast)
  qed
qed

text \<open>Nulhomotopy via convex extension: if B is a closed convex set in R^2 containing x,
  frontier B \<subseteq> B, f continuous on B mapping into Y, then f|_{frontier B} is nulhomotopic in Y.
  Uses the straight-line homotopy H(y,t) = f((1-t)*y + t*x).\<close>

lemma nulhomotopic_via_convex_R2:
  fixes B :: "(real \<times> real) set" and Y :: "(real \<times> real) set"
    and f :: "real \<times> real \<Rightarrow> real \<times> real" and x :: "real \<times> real"
  assumes hconv: "\<forall>y\<in>B. \<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow>
      ((1-t) * fst y + t * fst x, (1-t) * snd y + t * snd x) \<in> B"
      and hx: "x \<in> B"
      and hfr_sub: "frontier B \<subseteq> B"
      and hcont: "continuous_on B f"
      and hfB_Y: "\<forall>y\<in>B. f y \<in> Y"
  shows "top1_nulhomotopic_on (frontier B)
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (frontier B))
      Y (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) Y) f"
proof -
  let ?TR2 = "product_topology_on top1_open_sets top1_open_sets :: (real\<times>real) set set"
  let ?TfB = "subspace_topology UNIV ?TR2 (frontier B)"
  let ?TY = "subspace_topology UNIV ?TR2 Y"
  \<comment> \<open>The homotopy: H(y,t) = f((1-t)*y + t*x).\<close>
  define H where "H = (\<lambda>(yt :: (real\<times>real) \<times> real).
    f ((1 - snd yt) *\<^sub>R fst (fst yt) + snd yt *\<^sub>R fst x,
       (1 - snd yt) *\<^sub>R snd (fst yt) + snd yt *\<^sub>R snd x))"
  let ?c = "f x"
  \<comment> \<open>c \<in> Y.\<close>
  have hc_Y: "?c \<in> Y" using hfB_Y hx by (by100 blast)
  \<comment> \<open>H maps frontier B \<times> I into Y.\<close>
  have hH_maps: "\<forall>p \<in> frontier B \<times> I_set. H p \<in> Y"
  proof (intro ballI)
    fix p assume hp: "p \<in> frontier B \<times> I_set"
    then obtain y t where hyt: "p = (y, t)" and hy: "y \<in> frontier B" and ht: "t \<in> I_set"
      by (by100 blast)
    have ht01: "0 \<le> t \<and> t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)
    let ?z = "((1-t) * fst y + t * fst x, (1-t) * snd y + t * snd x)"
    have "?z \<in> B"
    proof -
      have "y \<in> B" using hy hfr_sub by (by100 blast)
      thus ?thesis using hconv ht01 by (by100 blast)
    qed
    hence "f ?z \<in> Y" using hfB_Y by (by100 blast)
    thus "H p \<in> Y" unfolding H_def hyt by (by100 simp)
  qed
  \<comment> \<open>H(y,0) = f(y).\<close>
  have hH0: "\<forall>y \<in> frontier B. H (y, 0) = f y"
    unfolding H_def by (by100 simp)
  \<comment> \<open>H(y,1) = f(x) = c.\<close>
  have hH1: "\<forall>y \<in> frontier B. H (y, 1) = ?c"
    unfolding H_def by (by100 simp)
  \<comment> \<open>H continuous on frontier B \<times> I.\<close>
  have hH_cont_HOL: "continuous_on (frontier B \<times> I_set) H"
  proof -
    have "continuous_on (frontier B \<times> I_set) (\<lambda>yt.
        ((1 - snd yt) * fst (fst yt) + snd yt * fst x,
         (1 - snd yt) * snd (fst yt) + snd yt * snd x))"
      by (intro continuous_on_Pair continuous_on_add continuous_on_mult
          continuous_on_diff continuous_on_snd continuous_on_fst
          continuous_on_compose2[OF continuous_on_fst]
          continuous_on_compose2[OF continuous_on_snd]
          continuous_on_const continuous_on_id) (by100 auto)+
    moreover have hlin_in_B: "\<forall>yt \<in> frontier B \<times> I_set.
        ((1 - snd yt) * fst (fst yt) + snd yt * fst x,
         (1 - snd yt) * snd (fst yt) + snd yt * snd x) \<in> B"
    proof (intro ballI)
      fix yt assume "yt \<in> frontier B \<times> I_set"
      then obtain y t where "yt = (y, t)" and "y \<in> frontier B" and "t \<in> I_set" by (by100 blast)
      hence "y \<in> B" using hfr_sub by (by100 blast)
      moreover have "0 \<le> t \<and> t \<le> 1" using \<open>t \<in> I_set\<close> unfolding top1_unit_interval_def by (by100 auto)
      ultimately show "((1 - snd yt) * fst (fst yt) + snd yt * fst x,
         (1 - snd yt) * snd (fst yt) + snd yt * snd x) \<in> B"
        using hconv \<open>yt = (y, t)\<close> by (by100 simp)
    qed
    ultimately have "continuous_on (frontier B \<times> I_set) (\<lambda>yt.
        f ((1 - snd yt) * fst (fst yt) + snd yt * fst x,
           (1 - snd yt) * snd (fst yt) + snd yt * snd x))"
    proof -
      let ?g = "\<lambda>yt. ((1 - snd yt) * fst (fst yt) + snd yt * fst x,
         (1 - snd yt) * snd (fst yt) + snd yt * snd x)"
      assume hg_cont: "continuous_on (frontier B \<times> I_set) ?g"
      have "?g ` (frontier B \<times> I_set) \<subseteq> B" using hlin_in_B by (by100 blast)
      hence "continuous_on (?g ` (frontier B \<times> I_set)) f"
        using continuous_on_subset[OF hcont] by (by100 blast)
      have hg_img: "?g ` (frontier B \<times> I_set) \<subseteq> B"
        using hlin_in_B by (by100 force)
      have "continuous_on (?g ` (frontier B \<times> I_set)) f"
        using continuous_on_subset[OF hcont hg_img] .
      have "continuous_on (frontier B \<times> I_set) (f \<circ> ?g)"
        by (rule continuous_on_compose[OF hg_cont \<open>continuous_on (?g ` (frontier B \<times> I_set)) f\<close>])
      thus ?thesis unfolding comp_def by (by100 simp)
    qed
    thus ?thesis unfolding H_def by (by100 simp)
  qed
  \<comment> \<open>Bridge to top1 continuous.\<close>
  have hH_top1: "top1_continuous_map_on (frontier B \<times> I_set)
      (product_topology_on ?TfB I_top) Y ?TY H"
    by (rule R2_subspace_I_continuous_on_transfer[OF hH_cont_HOL])
       (use hH_maps in \<open>by100 blast\<close>)
  \<comment> \<open>f continuous on frontier B in top1.\<close>
  have hf_cont_top1: "top1_continuous_map_on (frontier B) ?TfB Y ?TY f"
  proof -
    have hf_cont_fB: "continuous_on (frontier B) f"
      using continuous_on_subset[OF hcont hfr_sub] .
    have hf_maps: "\<And>p. p \<in> frontier B \<Longrightarrow> f p \<in> Y"
      using hfB_Y hfr_sub by (by100 blast)
    from top1_continuous_map_on_real2_subspace_general[OF hf_maps hf_cont_fB]
    show ?thesis .
  qed
  \<comment> \<open>Constant map continuous.\<close>
  have hconst_cont: "top1_continuous_map_on (frontier B) ?TfB Y ?TY (\<lambda>_. ?c)"
  proof -
    have "continuous_on (frontier B) (\<lambda>_::real\<times>real. ?c)" by (rule continuous_on_const)
    from top1_continuous_map_on_real2_subspace_general[OF _ this]
    show ?thesis using hc_Y by (by100 blast)
  qed
  \<comment> \<open>Assemble nulhomotopic.\<close>
  show ?thesis unfolding top1_nulhomotopic_on_def top1_homotopic_on_def
    using hc_Y hf_cont_top1 hconst_cont hH_top1 hH0 hH1 by (by100 blast)
qed

text \<open>Borsuk for R^2: if K is a compact set in R^2, f: K \<rightarrow> R^2 is injective continuous,
  f nulhomotopic in R^2 - {a, b}, and a, b \<in> R^2 - f(K), then a and b are in the same
  connected component of R^2 - f(K).\<close>

lemma Borsuk_R2:
  fixes K :: "(real \<times> real) set" and TK :: "(real \<times> real) set set"
    and f :: "real \<times> real \<Rightarrow> real \<times> real"
    and a b :: "real \<times> real"
  assumes hTK: "is_topology_on K TK"
      and hcomp: "top1_compact_on K TK"
      and hcont: "top1_continuous_map_on K TK (UNIV::(real\<times>real) set)
           (product_topology_on top1_open_sets top1_open_sets) f"
      and hinj: "inj_on f K"
      and ha: "a \<notin> f ` K" and hb: "b \<notin> f ` K"
      and hnul: "top1_nulhomotopic_on K TK
           (UNIV - {a, b}) (subspace_topology UNIV
             (product_topology_on top1_open_sets top1_open_sets) (UNIV - {a, b})) f"
  shows "\<exists>C. top1_connected_on C (subspace_topology UNIV
           (product_topology_on top1_open_sets top1_open_sets) C)
         \<and> C \<subseteq> UNIV - f ` K \<and> a \<in> C \<and> b \<in> C"
proof (cases "a = b")
  case True
  \<comment> \<open>Trivial: a = b, take any connected set containing a.\<close>
  let ?C = "top1_component_of_on (UNIV - f ` K)
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - f ` K)) a"
  have hTR2': "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
    using product_topology_on_is_topology_on[OF
      top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by (by100 simp)
  let ?T_compl = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - f ` K)"
  have hT_compl: "is_topology_on (UNIV - f ` K) ?T_compl"
    by (rule subspace_topology_is_topology_on[OF hTR2']) (by100 simp)
  have "a \<in> UNIV - f ` K" using ha by (by100 blast)
  hence "a \<in> ?C"
    by (rule top1_component_of_on_self_mem[OF hT_compl])
  moreover have "top1_connected_on ?C (subspace_topology UNIV
      (product_topology_on top1_open_sets top1_open_sets) ?C)"
  proof -
    have "top1_connected_on ?C (subspace_topology (UNIV - f ` K) ?T_compl ?C)"
      by (rule top1_component_of_on_connected[OF hT_compl \<open>a \<in> UNIV - f ` K\<close>])
    moreover have "?C \<subseteq> UNIV - f ` K"
      unfolding top1_component_of_on_def by (by100 blast)
    hence "subspace_topology (UNIV - f ` K) ?T_compl ?C =
        subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?C"
      by (rule subspace_topology_trans)
    ultimately show ?thesis by (by100 simp)
  qed
  moreover have "?C \<subseteq> UNIV - f ` K"
    unfolding top1_component_of_on_def by (by100 blast)
  ultimately show ?thesis using True by (by100 blast)
next
  case False
  hence hab: "a \<noteq> b" .
  \<comment> \<open>Get stereographic projection \<sigma>: S^2-{N} \<rightarrow> R^2.\<close>
  let ?N = "north_pole :: real \<times> real \<times> real"
  let ?TR2 = "product_topology_on top1_open_sets top1_open_sets :: (real\<times>real) set set"
  obtain \<sigma> where h\<sigma>: "top1_homeomorphism_on (top1_S2 - {?N})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {?N}))
      (UNIV :: (real\<times>real) set) ?TR2 \<sigma>"
    using S2_minus_point_homeo_R2[OF north_pole_in_S2] by (by100 blast)
  let ?\<sigma>inv = "inv_into (top1_S2 - {?N}) \<sigma>"
  \<comment> \<open>Properties of \<sigma>.\<close>
  have h\<sigma>_bij: "bij_betw \<sigma> (top1_S2 - {?N}) UNIV"
    using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
  have h\<sigma>_surj: "\<sigma> ` (top1_S2 - {?N}) = UNIV"
    using h\<sigma>_bij unfolding bij_betw_def by (by100 blast)
  have h\<sigma>_inj: "inj_on \<sigma> (top1_S2 - {?N})"
    using h\<sigma>_bij unfolding bij_betw_def by (by100 blast)
  \<comment> \<open>\<sigma>^{-1} maps R^2 to S^2-{N}.\<close>
  have h\<sigma>inv_mem: "\<And>p :: real\<times>real. ?\<sigma>inv p \<in> top1_S2 - {?N}"
  proof -
    fix p :: "real \<times> real"
    have "p \<in> \<sigma> ` (top1_S2 - {?N})" using h\<sigma>_surj by (by100 blast)
    thus "?\<sigma>inv p \<in> top1_S2 - {?N}" by (rule inv_into_into)
  qed
  have h\<sigma>inv_S2: "\<And>p. ?\<sigma>inv p \<in> top1_S2"
    using h\<sigma>inv_mem by (by100 blast)
  have h\<sigma>_\<sigma>inv: "\<And>p :: real\<times>real. \<sigma> (?\<sigma>inv p) = p"
  proof -
    fix p :: "real \<times> real"
    have "p \<in> \<sigma> ` (top1_S2 - {?N})" using h\<sigma>_surj by (by100 blast)
    thus "\<sigma> (?\<sigma>inv p) = p" by (rule f_inv_into_f)
  qed
  have h\<sigma>inv_\<sigma>: "\<And>p. p \<in> top1_S2 - {?N} \<Longrightarrow> ?\<sigma>inv (\<sigma> p) = p"
    by (rule inv_into_f_f[OF h\<sigma>_inj])
  \<comment> \<open>Map a, b into S^2.\<close>
  let ?a_S2 = "?\<sigma>inv a" and ?b_S2 = "?\<sigma>inv b"
  have ha_S2: "?a_S2 \<in> top1_S2" by (rule h\<sigma>inv_S2)
  have hb_S2: "?b_S2 \<in> top1_S2" by (rule h\<sigma>inv_S2)
  have hab_S2: "?a_S2 \<noteq> ?b_S2"
  proof
    assume "?a_S2 = ?b_S2"
    hence "\<sigma> ?a_S2 = \<sigma> ?b_S2" by (by100 simp)
    hence "a = b" using h\<sigma>_\<sigma>inv by (by100 simp)
    thus False using hab by (by100 blast)
  qed
  \<comment> \<open>Compose: g = \<sigma>^{-1} \<circ> f : K \<rightarrow> S^2-{N}.\<close>
  let ?g = "?\<sigma>inv \<circ> f"
  \<comment> \<open>g maps into S^2-{\<sigma>^{-1}(a), \<sigma>^{-1}(b)}.\<close>
  have hg_maps: "\<forall>x\<in>K. ?g x \<in> top1_S2 - {?a_S2, ?b_S2}"
  proof (intro ballI)
    fix y assume hy: "y \<in> K"
    have hgy: "?g y = ?\<sigma>inv (f y)" by (by100 simp)
    have "?g y \<in> top1_S2 - {?N}" unfolding hgy by (rule h\<sigma>inv_mem)
    moreover have "?g y \<noteq> ?a_S2"
    proof
      assume "?g y = ?a_S2"
      hence "\<sigma> (?g y) = \<sigma> ?a_S2" by (by100 simp)
      hence "f y = a" using h\<sigma>_\<sigma>inv by (by100 simp)
      hence "a \<in> f ` K" using hy by (by100 blast)
      thus False using ha by (by100 blast)
    qed
    moreover have "?g y \<noteq> ?b_S2"
    proof
      assume "?g y = ?b_S2"
      hence "\<sigma> (?g y) = \<sigma> ?b_S2" by (by100 simp)
      hence "f y = b" using h\<sigma>_\<sigma>inv by (by100 simp)
      hence "b \<in> f ` K" using hy by (by100 blast)
      thus False using hb by (by100 blast)
    qed
    ultimately show "?g y \<in> top1_S2 - {?a_S2, ?b_S2}" by (by100 blast)
  qed
  \<comment> \<open>g continuous, injective, compact domain, nulhomotopic.\<close>
  have hg_cont: "top1_continuous_map_on K TK
      (top1_S2 - {?a_S2, ?b_S2}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {?a_S2, ?b_S2})) ?g"
  proof -
    \<comment> \<open>\<sigma>^{-1} continuous from R^2 to S^2-{N}.\<close>
    have h\<sigma>inv_cont: "top1_continuous_map_on UNIV ?TR2
        (top1_S2 - {?N}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {?N})) ?\<sigma>inv"
      using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
    \<comment> \<open>Enlarge codomain to S^2.\<close>
    have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
      using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
    have h\<sigma>inv_S2: "top1_continuous_map_on UNIV ?TR2 top1_S2 top1_S2_topology ?\<sigma>inv"
    proof -
      have "top1_S2 - {?N} \<subseteq> top1_S2" by (by100 blast)
      from top1_continuous_map_on_codomain_enlarge[OF h\<sigma>inv_cont this subset_refl]
      have "top1_continuous_map_on UNIV ?TR2 top1_S2
          (subspace_topology top1_S2 top1_S2_topology top1_S2) ?\<sigma>inv" .
      moreover have "subspace_topology top1_S2 top1_S2_topology top1_S2 = top1_S2_topology"
      proof (rule set_eqI, rule iffI)
        fix V assume "V \<in> subspace_topology top1_S2 top1_S2_topology top1_S2"
        then obtain U where "U \<in> top1_S2_topology" and "V = top1_S2 \<inter> U"
          unfolding subspace_topology_def by (by100 auto)
        moreover have "U \<subseteq> top1_S2"
          using \<open>U \<in> top1_S2_topology\<close> top1_S2_is_topology_on_strict
          unfolding is_topology_on_strict_def by (by100 blast)
        hence "V = U" using \<open>U \<subseteq> top1_S2\<close> \<open>V = top1_S2 \<inter> U\<close> by (by100 blast)
        thus "V \<in> top1_S2_topology" using \<open>U \<in> top1_S2_topology\<close> by (by100 simp)
      next
        fix V assume "V \<in> top1_S2_topology"
        have "V \<subseteq> top1_S2"
          using \<open>V \<in> top1_S2_topology\<close> top1_S2_is_topology_on_strict
          unfolding is_topology_on_strict_def by (by100 blast)
        hence "top1_S2 \<inter> V = V" by (by100 blast)
        thus "V \<in> subspace_topology top1_S2 top1_S2_topology top1_S2"
          unfolding subspace_topology_def using \<open>V \<in> top1_S2_topology\<close> by (by100 blast)
      qed
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Compose f then \<sigma>^{-1}: K \<rightarrow> S^2.\<close>
    have hg_S2: "top1_continuous_map_on K TK top1_S2 top1_S2_topology ?g"
      by (rule top1_continuous_map_on_comp[OF hcont h\<sigma>inv_S2])
    \<comment> \<open>Shrink codomain to S^2-{a_S2,b_S2} (g maps K into it).\<close>
    have hg_img: "?g ` K \<subseteq> top1_S2 - {?a_S2, ?b_S2}"
    proof (rule image_subsetI)
      fix x assume "x \<in> K"
      thus "?g x \<in> top1_S2 - {?a_S2, ?b_S2}" using hg_maps by (by100 blast)
    qed
    have hg_sub: "top1_S2 - {?a_S2, ?b_S2} \<subseteq> top1_S2" by (by100 blast)
    show ?thesis
      by (rule top1_continuous_map_on_codomain_shrink[OF hg_S2 hg_img hg_sub])
  qed
  have hg_inj: "inj_on ?g K"
  proof (rule comp_inj_on[OF hinj])
    show "inj_on ?\<sigma>inv (f ` K)"
    proof (rule inj_onI)
      fix x y assume "x \<in> f ` K" "y \<in> f ` K" "?\<sigma>inv x = ?\<sigma>inv y"
      hence "\<sigma> (?\<sigma>inv x) = \<sigma> (?\<sigma>inv y)" by (by100 simp)
      thus "x = y" using h\<sigma>_\<sigma>inv by (by100 simp)
    qed
  qed
  have hg_nul: "top1_nulhomotopic_on K TK
      (top1_S2 - {?a_S2, ?b_S2}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {?a_S2, ?b_S2})) ?g"
  proof -
    let ?Y_R2 = "UNIV - {a, b} :: (real\<times>real) set"
    let ?TY_R2 = "subspace_topology UNIV ?TR2 ?Y_R2"
    let ?Y_S2 = "top1_S2 - {?a_S2, ?b_S2}"
    let ?TY_S2 = "subspace_topology top1_S2 top1_S2_topology ?Y_S2"
    \<comment> \<open>\<sigma>^{-1} continuous from R^2-{a,b} to S^2-{a_S2,b_S2}.\<close>
    have h\<sigma>inv_Y: "top1_continuous_map_on ?Y_R2 ?TY_R2 ?Y_S2 ?TY_S2 ?\<sigma>inv"
    proof -
      have h\<sigma>inv_cont: "top1_continuous_map_on UNIV ?TR2
          (top1_S2 - {?N}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {?N})) ?\<sigma>inv"
        using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
      have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
        using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
      \<comment> \<open>Enlarge codomain to S^2.\<close>
      have h\<sigma>inv_S2: "top1_continuous_map_on UNIV ?TR2 top1_S2 top1_S2_topology ?\<sigma>inv"
      proof -
        have "top1_S2 - {?N} \<subseteq> top1_S2" by (by100 blast)
        from top1_continuous_map_on_codomain_enlarge[OF h\<sigma>inv_cont this subset_refl]
        have "top1_continuous_map_on UNIV ?TR2 top1_S2
            (subspace_topology top1_S2 top1_S2_topology top1_S2) ?\<sigma>inv" .
        moreover have "subspace_topology top1_S2 top1_S2_topology top1_S2 = top1_S2_topology"
        proof (rule set_eqI, rule iffI)
          fix V assume "V \<in> subspace_topology top1_S2 top1_S2_topology top1_S2"
          then obtain U where "U \<in> top1_S2_topology" "V = top1_S2 \<inter> U"
            unfolding subspace_topology_def by (by100 auto)
          moreover have "U \<subseteq> top1_S2"
            using \<open>U \<in> top1_S2_topology\<close> top1_S2_is_topology_on_strict
            unfolding is_topology_on_strict_def by (by100 blast)
          hence "V = U" using \<open>V = top1_S2 \<inter> U\<close> by (by100 blast)
          ultimately show "V \<in> top1_S2_topology" by (by100 simp)
        next
          fix V assume "V \<in> top1_S2_topology"
          have "V \<subseteq> top1_S2" using \<open>V \<in> top1_S2_topology\<close> top1_S2_is_topology_on_strict
            unfolding is_topology_on_strict_def by (by100 blast)
          hence "top1_S2 \<inter> V = V" by (by100 blast)
          thus "V \<in> subspace_topology top1_S2 top1_S2_topology top1_S2"
            unfolding subspace_topology_def using \<open>V \<in> top1_S2_topology\<close> by (by100 blast)
        qed
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>Restrict domain to R^2-{a,b}.\<close>
      have h\<sigma>inv_R2ab: "top1_continuous_map_on ?Y_R2 ?TY_R2 top1_S2 top1_S2_topology ?\<sigma>inv"
      proof -
        have "?Y_R2 \<subseteq> (UNIV::(real\<times>real) set)" by (by100 blast)
        from top1_continuous_map_on_restrict_domain_simple[OF h\<sigma>inv_S2 this]
        have "top1_continuous_map_on ?Y_R2 (subspace_topology UNIV ?TR2 ?Y_R2)
            top1_S2 top1_S2_topology ?\<sigma>inv" .
        thus ?thesis .
      qed
      \<comment> \<open>Shrink codomain to S^2-{a_S2,b_S2}.\<close>
      have himg: "?\<sigma>inv ` ?Y_R2 \<subseteq> ?Y_S2"
      proof (rule image_subsetI)
        fix p assume "p \<in> ?Y_R2"
        hence "p \<noteq> a" "p \<noteq> b" by (by100 blast)+
        have "?\<sigma>inv p \<in> top1_S2" using h\<sigma>inv_mem[of p] by (by100 blast)
        moreover have "?\<sigma>inv p \<noteq> ?a_S2"
        proof
          assume "?\<sigma>inv p = ?a_S2"
          hence "\<sigma> (?\<sigma>inv p) = \<sigma> ?a_S2" by (by100 simp)
          hence "p = a" using h\<sigma>_\<sigma>inv by (by100 simp)
          with \<open>p \<noteq> a\<close> show False by (by100 blast)
        qed
        moreover have "?\<sigma>inv p \<noteq> ?b_S2"
        proof
          assume "?\<sigma>inv p = ?b_S2"
          hence "\<sigma> (?\<sigma>inv p) = \<sigma> ?b_S2" by (by100 simp)
          hence "p = b" using h\<sigma>_\<sigma>inv by (by100 simp)
          with \<open>p \<noteq> b\<close> show False by (by100 blast)
        qed
        ultimately show "?\<sigma>inv p \<in> ?Y_S2" by (by100 blast)
      qed
      show ?thesis
        by (rule top1_continuous_map_on_codomain_shrink[OF h\<sigma>inv_R2ab himg]) (by100 blast)
    qed
    \<comment> \<open>Compose: nulhomotopy F with \<sigma>^{-1} gives nulhomotopy \<sigma>^{-1}\<circ>F.\<close>
    from hnul obtain c where hc: "c \<in> ?Y_R2"
        and hhom: "top1_homotopic_on K TK ?Y_R2 ?TY_R2 f (\<lambda>_. c)"
      unfolding top1_nulhomotopic_on_def by (by100 blast)
    from hhom obtain F where
        hf_cont': "top1_continuous_map_on K TK ?Y_R2 ?TY_R2 f"
        and hconst: "top1_continuous_map_on K TK ?Y_R2 ?TY_R2 (\<lambda>_. c)"
        and hF: "top1_continuous_map_on (K \<times> I_set) (product_topology_on TK I_top) ?Y_R2 ?TY_R2 F"
        and hF0: "\<forall>x\<in>K. F (x, 0) = f x"
        and hF1: "\<forall>x\<in>K. F (x, 1) = c"
      unfolding top1_homotopic_on_def by (by100 blast)
    \<comment> \<open>G = \<sigma>^{-1} \<circ> F.\<close>
    let ?G = "?\<sigma>inv \<circ> F"
    let ?c' = "?\<sigma>inv c"
    have hc'_mem: "?c' \<in> ?Y_S2"
    proof -
      have "c \<in> ?Y_R2" by (rule hc)
      thus ?thesis using h\<sigma>inv_Y unfolding top1_continuous_map_on_def by (by100 blast)
    qed
    have hG_cont: "top1_continuous_map_on (K \<times> I_set) (product_topology_on TK I_top) ?Y_S2 ?TY_S2 ?G"
      by (rule top1_continuous_map_on_comp[OF hF h\<sigma>inv_Y])
    have hG0: "\<forall>x\<in>K. ?G (x, 0) = ?g x" using hF0 by (by100 simp)
    have hG1: "\<forall>x\<in>K. ?G (x, 1) = ?c'" using hF1 by (by100 simp)
    have hg_cont_Y: "top1_continuous_map_on K TK ?Y_S2 ?TY_S2 ?g"
      by (rule top1_continuous_map_on_comp[OF hf_cont' h\<sigma>inv_Y])
    have hconst_Y: "top1_continuous_map_on K TK ?Y_S2 ?TY_S2 (\<lambda>_. ?c')"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x assume "x \<in> K" show "?c' \<in> ?Y_S2" by (rule hc'_mem)
    next
      fix V assume "V \<in> ?TY_S2"
      show "{x \<in> K. ?c' \<in> V} \<in> TK"
      proof -
        have "K \<in> TK" using hTK unfolding is_topology_on_def by (by100 blast)
        moreover have "{} \<in> TK" using hTK unfolding is_topology_on_def by (by100 blast)
        have "{x \<in> K. ?c' \<in> V} = K \<or> {x \<in> K. ?c' \<in> V} = {}"
          by (by100 blast)
        thus ?thesis using \<open>K \<in> TK\<close> \<open>{} \<in> TK\<close> by (by100 metis)
      qed
    qed
    show ?thesis unfolding top1_nulhomotopic_on_def top1_homotopic_on_def
      using hc'_mem hg_cont_Y hconst_Y hG_cont hG0 hG1
      by (by100 blast)
  qed
  \<comment> \<open>Apply Borsuk on S^2.\<close>
  have hT_S2: "is_topology_on_strict top1_S2 top1_S2_topology"
    by (rule top1_S2_is_topology_on_strict)
  from Lemma_62_2_BorsukLemma[OF hT_S2 hcomp ha_S2 hb_S2 hab_S2 hg_cont hg_inj hg_nul]
  obtain C_S2 where hC_S2: "C_S2 \<in> top1_components_on (top1_S2 - ?g ` K)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?g ` K))"
    and ha_C: "?a_S2 \<in> C_S2" and hb_C: "?b_S2 \<in> C_S2"
    by (by100 blast)
  \<comment> \<open>Transfer back to R^2: \<sigma>(C_S2 \<inter> (S^2-{N})) is connected in R^2 and contains a, b.\<close>
  let ?C = "\<sigma> ` (C_S2 - {?N})"
  show ?thesis
  proof (intro exI[of _ ?C] conjI)
    show "a \<in> ?C"
    proof -
      have "?a_S2 \<in> C_S2 - {?N}" using ha_C h\<sigma>inv_mem by (by100 blast)
      hence "\<sigma> ?a_S2 \<in> ?C" by (by100 blast)
      thus ?thesis using h\<sigma>_\<sigma>inv by (by100 simp)
    qed
    show "b \<in> ?C"
    proof -
      have "?b_S2 \<in> C_S2 - {?N}" using hb_C h\<sigma>inv_mem by (by100 blast)
      hence "\<sigma> ?b_S2 \<in> ?C" by (by100 blast)
      thus ?thesis using h\<sigma>_\<sigma>inv by (by100 simp)
    qed
    show "?C \<subseteq> UNIV - f ` K"
    proof (rule subsetI)
      fix p assume "p \<in> ?C"
      then obtain q where hq: "q \<in> C_S2 - {?N}" and hp: "p = \<sigma> q" by (by100 blast)
      have "q \<in> top1_S2 - ?g ` K"
        using hC_S2 hq unfolding top1_components_on_def top1_component_of_on_def by (by100 blast)
      hence "q \<notin> ?g ` K" by (by100 blast)
      hence "p \<notin> f ` K"
      proof (rule contrapos_nn)
        assume "p \<in> f ` K"
        then obtain y where "y \<in> K" and "f y = p" by (by100 blast)
        hence "?g y = ?\<sigma>inv p" by (by100 simp)
        moreover have "?\<sigma>inv p = ?\<sigma>inv (\<sigma> q)" using hp by (by100 simp)
        moreover have "q \<in> top1_S2 - {?N}"
          using hC_S2 hq unfolding top1_components_on_def top1_component_of_on_def by (by100 blast)
        hence "?\<sigma>inv (\<sigma> q) = q" by (rule h\<sigma>inv_\<sigma>)
        ultimately have "?g y = q" by (by100 simp)
        thus "q \<in> ?g ` K" using \<open>y \<in> K\<close> by (by100 blast)
      qed
      thus "p \<in> UNIV - f ` K" by (by100 blast)
    qed
    show "top1_connected_on ?C (subspace_topology UNIV ?TR2 ?C)"
    proof -
      \<comment> \<open>C_S2 connected in S^2.\<close>
      have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
        using hT_S2 unfolding is_topology_on_strict_def by (by100 blast)
      let ?T_compl_S2 = "subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?g ` K)"
      have hT_compl_S2: "is_topology_on (top1_S2 - ?g ` K) ?T_compl_S2"
        by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
      obtain z where hz: "z \<in> top1_S2 - ?g ` K" and hCeq: "C_S2 = top1_component_of_on (top1_S2 - ?g ` K) ?T_compl_S2 z"
        using hC_S2 unfolding top1_components_on_def by (by100 blast)
      have hC_conn_S2: "top1_connected_on C_S2 (subspace_topology (top1_S2 - ?g ` K) ?T_compl_S2 C_S2)"
        unfolding hCeq by (rule top1_component_of_on_connected[OF hT_compl_S2 hz])
      have hC_sub_S2: "C_S2 \<subseteq> top1_S2 - ?g ` K"
        using hC_S2 unfolding top1_components_on_def top1_component_of_on_def by (by100 blast)
      hence hC_sub_S2': "C_S2 \<subseteq> top1_S2" by (by100 blast)
      \<comment> \<open>C_S2-{N} connected.\<close>
      have hC_minus_N_conn: "top1_connected_on (C_S2 - {?N}) (subspace_topology top1_S2 top1_S2_topology (C_S2 - {?N}))"
      proof (cases "?N \<in> C_S2")
        case False
        hence "C_S2 - {?N} = C_S2" by (by100 blast)
        hence "subspace_topology top1_S2 top1_S2_topology (C_S2 - {?N})
            = subspace_topology top1_S2 top1_S2_topology C_S2" by (by100 simp)
        moreover have "top1_connected_on C_S2 (subspace_topology top1_S2 top1_S2_topology C_S2)"
        proof -
          have "subspace_topology (top1_S2 - ?g ` K) ?T_compl_S2 C_S2
              = subspace_topology top1_S2 top1_S2_topology C_S2"
            by (rule subspace_topology_trans[OF hC_sub_S2])
          with hC_conn_S2 show ?thesis by (by100 simp)
        qed
        ultimately show ?thesis using \<open>C_S2 - {?N} = C_S2\<close> by (by100 simp)
      next
        case True
        \<comment> \<open>N \<in> C_S2, and C_S2 is open in S^2-g(K) (component of open set).
           C_S2 connected, open in S^2-g(K). Need: C_S2 open in S^2 if S^2-g(K) open in S^2.\<close>
        \<comment> \<open>Apply connected_open_delete_S2: C_S2 open in S^2, connected, N \<in> C_S2.\<close>
        \<comment> \<open>Need: C_S2 open in S^2, which requires g(K) closed (compact image in Hausdorff).\<close>
        \<comment> \<open>Step 1: g(K) compact in S^2 (image of compact under continuous).\<close>
        have hgK_compact: "top1_compact_on (?g ` K)
            (subspace_topology top1_S2 top1_S2_topology (?g ` K))"
        proof -
          have "top1_compact_on (?g ` K) (subspace_topology (top1_S2 - {?a_S2, ?b_S2})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {?a_S2, ?b_S2})) (?g ` K))"
            by (rule Theorem_26_5[OF hTK
                  subspace_topology_is_topology_on[OF hTopS2, of "top1_S2 - {?a_S2, ?b_S2}"]
                  hcomp hg_cont]) (by100 blast)
          moreover have "?g ` K \<subseteq> top1_S2 - {?a_S2, ?b_S2}"
            using hg_maps by (by100 force)
          hence "subspace_topology (top1_S2 - {?a_S2, ?b_S2})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {?a_S2, ?b_S2})) (?g ` K)
              = subspace_topology top1_S2 top1_S2_topology (?g ` K)"
            by (rule subspace_topology_trans)
          ultimately show ?thesis by (by100 simp)
        qed
        \<comment> \<open>Step 2: g(K) closed in S^2 (compact in Hausdorff).\<close>
        have hgK_closed: "closedin_on top1_S2 top1_S2_topology (?g ` K)"
        proof (rule compact_in_strict_hausdorff_closedin_on)
          show "is_hausdorff_on top1_S2 top1_S2_topology"
            using top1_S2_is_hausdorff by (by100 blast)
          show "is_topology_on_strict top1_S2 top1_S2_topology" by (rule hT_S2)
          show "?g ` K \<subseteq> top1_S2" using hg_maps by (by100 force)
          show "top1_compact_on (?g ` K) (subspace_topology top1_S2 top1_S2_topology (?g ` K))"
            by (rule hgK_compact)
        qed
        \<comment> \<open>Step 3: S^2-g(K) open in S^2.\<close>
        have hS2gK_open: "top1_S2 - ?g ` K \<in> top1_S2_topology"
          using hgK_closed unfolding closedin_on_def by (by100 blast)
        \<comment> \<open>Step 4: C_S2 open in S^2 (component of open set in locally connected space).\<close>
        have hC_open_S2: "C_S2 \<in> top1_S2_topology"
        proof -
          have hS2_lpc: "top1_locally_path_connected_on top1_S2 top1_S2_topology"
            by (rule S2_locally_path_connected)
          \<comment> \<open>S^2 locally connected (from locally path connected).\<close>
          have hS2_lc: "top1_locally_connected_on top1_S2 top1_S2_topology"
          proof -
            have "\<forall>x\<in>top1_S2. top1_locally_connected_at top1_S2 top1_S2_topology x"
            proof (intro ballI)
              fix x assume hx: "x \<in> top1_S2"
              have "top1_locally_path_connected_at top1_S2 top1_S2_topology x"
                using hS2_lpc hx unfolding top1_locally_path_connected_on_def by (by100 blast)
              show "top1_locally_connected_at top1_S2 top1_S2_topology x"
                unfolding top1_locally_connected_at_def
              proof (intro allI impI)
                fix U assume hU: "neighborhood_of x top1_S2 top1_S2_topology U \<and> U \<subseteq> top1_S2"
                have "\<exists>V. neighborhood_of x top1_S2 top1_S2_topology V \<and> V \<subseteq> U \<and> V \<subseteq> top1_S2
                    \<and> top1_path_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
                  using \<open>top1_locally_path_connected_at top1_S2 top1_S2_topology x\<close> hU
                  unfolding top1_locally_path_connected_at_def by (by100 blast)
                then obtain V where hV: "neighborhood_of x top1_S2 top1_S2_topology V"
                    and hVU: "V \<subseteq> U" and hVS: "V \<subseteq> top1_S2"
                    and hVpc: "top1_path_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
                  by (by100 blast)
                have "top1_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
                  using hVpc path_connected_imp_connected by (by100 blast)
                thus "\<exists>V. neighborhood_of x top1_S2 top1_S2_topology V \<and> V \<subseteq> U \<and> V \<subseteq> top1_S2
                    \<and> top1_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
                  using hV hVU hVS by (by100 blast)
              qed
            qed
            thus ?thesis unfolding top1_locally_connected_on_def
              using hTopS2 by (by100 blast)
          qed
          \<comment> \<open>Apply Theorem_25_3: components of open sets are open in lc space.\<close>
          have "top1_S2 - ?g ` K \<in> top1_S2_topology" by (rule hS2gK_open)
          moreover have "top1_S2 - ?g ` K \<subseteq> top1_S2" by (by100 blast)
          moreover have "C_S2 \<in> top1_components_on (top1_S2 - ?g ` K)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?g ` K))"
            by (rule hC_S2)
          ultimately show ?thesis
            using iffD1[OF Theorem_25_3[OF hTopS2]] hS2_lc by (by100 blast)
        qed
        \<comment> \<open>Step 5: C_S2 connected in S^2.\<close>
        have hC_conn_S2_top: "top1_connected_on C_S2 (subspace_topology top1_S2 top1_S2_topology C_S2)"
        proof -
          have "subspace_topology (top1_S2 - ?g ` K) ?T_compl_S2 C_S2
              = subspace_topology top1_S2 top1_S2_topology C_S2"
            by (rule subspace_topology_trans[OF hC_sub_S2])
          with hC_conn_S2 show ?thesis by (by100 simp)
        qed
        \<comment> \<open>Step 6: C_S2 - {N} connected. Two cases: K={} or K\<noteq>{}.\<close>
        have "connected (C_S2 - {?N})"
        proof (cases "K = {}")
          case True
          \<comment> \<open>K={} \<Longrightarrow> g(K)={} \<Longrightarrow> S^2-g(K) = S^2. S^2 connected \<Longrightarrow> C_S2 = S^2 (only component).
             S^2-{N} connected (homeomorphic to R^2 via \<sigma>).\<close>
          have "connected (top1_S2 - {?N})"
          proof -
            have "top1_simply_connected_on (top1_S2 - {?N})
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {?N}))"
              by (rule S2_minus_point_simply_connected[OF north_pole_in_S2])
            hence "top1_path_connected_on (top1_S2 - {?N})
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {?N}))"
              unfolding top1_simply_connected_on_def by (by100 blast)
            hence "top1_connected_on (top1_S2 - {?N})
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {?N}))"
              using path_connected_imp_connected by (by100 blast)
            hence "top1_connected_on (top1_S2 - {?N})
                (subspace_topology (UNIV::(real\<times>real\<times>real) set) top1_open_sets (top1_S2 - {?N}))"
            proof -
              have "top1_S2 - {?N} \<subseteq> top1_S2" by (by100 blast)
              hence "subspace_topology top1_S2 top1_S2_topology (top1_S2 - {?N})
                  = subspace_topology UNIV
                    (product_topology_on top1_open_sets (product_topology_on top1_open_sets top1_open_sets))
                    (top1_S2 - {?N})"
                unfolding top1_S2_topology_def by (rule subspace_topology_trans)
              also have "\<dots> = subspace_topology (UNIV::(real\<times>real\<times>real) set) top1_open_sets (top1_S2 - {?N})"
                using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                      product_topology_on_open_sets[where ?'a=real and ?'b=real] by (by100 simp)
              finally have "subspace_topology top1_S2 top1_S2_topology (top1_S2 - {?N})
                  = subspace_topology UNIV top1_open_sets (top1_S2 - {?N})" .
              with \<open>top1_connected_on (top1_S2 - {?N}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {?N}))\<close>
              show ?thesis by (by100 simp)
            qed
            thus ?thesis using top1_connected_on_subspace_open_iff_connected by (by100 blast)
          qed
          moreover have "C_S2 = top1_S2"
          proof -
            have "?g ` K = {}" using True by (by100 blast)
            hence "top1_S2 - ?g ` K = top1_S2" by (by100 blast)
            hence hS2_eq: "top1_S2 - ?g ` K = top1_S2" by (by100 blast)
            \<comment> \<open>T_compl_S2 restricted to S^2 = TS2.\<close>
            have hT_eq: "?T_compl_S2 = top1_S2_topology"
            proof -
              have "?T_compl_S2 = subspace_topology top1_S2 top1_S2_topology top1_S2"
                using hS2_eq by (by100 simp)
              also have "\<dots> = top1_S2_topology"
              proof (rule set_eqI, rule iffI)
                fix V assume "V \<in> subspace_topology top1_S2 top1_S2_topology top1_S2"
                then obtain U where "U \<in> top1_S2_topology" "V = top1_S2 \<inter> U"
                  unfolding subspace_topology_def by (by100 auto)
                moreover have "U \<subseteq> top1_S2" using \<open>U \<in> top1_S2_topology\<close>
                  top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
                hence "V = U" using \<open>U \<subseteq> top1_S2\<close> \<open>V = top1_S2 \<inter> U\<close> by (by100 blast)
                thus "V \<in> top1_S2_topology" using \<open>U \<in> top1_S2_topology\<close> by (by100 simp)
              next
                fix V assume "V \<in> top1_S2_topology"
                have "V \<subseteq> top1_S2" using \<open>V \<in> top1_S2_topology\<close>
                  top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
                thus "V \<in> subspace_topology top1_S2 top1_S2_topology top1_S2"
                  unfolding subspace_topology_def using \<open>V \<in> top1_S2_topology\<close> by (by100 blast)
              qed
              finally show ?thesis .
            qed
            \<comment> \<open>S^2 connected, z \<in> S^2 \<Longrightarrow> component_of z = S^2.\<close>
            have "top1_component_of_on top1_S2 top1_S2_topology z = top1_S2"
            proof -
              have hS2_conn: "top1_connected_on top1_S2 top1_S2_topology"
                by (rule S2_connected)
              have hz_S2: "z \<in> top1_S2" using hz hS2_eq by (by100 blast)
              have "subspace_topology top1_S2 top1_S2_topology top1_S2 = top1_S2_topology"
                using hT_eq hS2_eq by (by100 simp)
              hence hS2_conn_sub: "top1_connected_on top1_S2 (subspace_topology top1_S2 top1_S2_topology top1_S2)"
                using hS2_conn by (by100 simp)
              have "top1_S2 \<subseteq> top1_component_of_on top1_S2 top1_S2_topology z"
                using top1_connected_subspace_subset_component_of[OF subset_refl hz_S2 hS2_conn_sub] .
              moreover have "top1_component_of_on top1_S2 top1_S2_topology z \<subseteq> top1_S2"
                unfolding top1_component_of_on_def by (by100 blast)
              ultimately show ?thesis by (by100 blast)
            qed
            thus ?thesis using hCeq hS2_eq hT_eq by (by100 simp)
          qed
          ultimately show ?thesis by (by100 simp)
        next
          case False
          \<comment> \<open>K\<noteq>{} \<Longrightarrow> g(K)\<noteq>{} \<Longrightarrow> \<exists>c \<in> S^2 not in C_S2.\<close>
          then obtain y where "y \<in> K" by (by100 blast)
          have "?g y \<in> top1_S2 - {?a_S2, ?b_S2}" using hg_maps \<open>y \<in> K\<close> by (by100 blast)
          hence "?g y \<in> top1_S2" and "?g y \<in> ?g ` K" using \<open>y \<in> K\<close> by (by100 blast)+
          hence "?g y \<notin> C_S2" using hC_sub_S2 by (by100 blast)
          hence "\<exists>c. c \<in> top1_S2 \<and> c \<notin> C_S2" using \<open>?g y \<in> top1_S2\<close> by (by100 blast)
          thus ?thesis
            by (rule connected_open_delete_S2[OF hC_open_S2 hC_conn_S2_top True])
        qed
        \<comment> \<open>Bridge HOL connected to top1_connected_on.\<close>
        hence "top1_connected_on (C_S2 - {?N})
            (subspace_topology (UNIV::(real\<times>real\<times>real) set) top1_open_sets (C_S2 - {?N}))"
          using top1_connected_on_subspace_open_iff_connected by (by100 blast)
        \<comment> \<open>Bridge: subspace UNIV top1_open_sets = subspace S^2 TS2 for subsets of S^2.\<close>
        moreover have "subspace_topology (UNIV::(real\<times>real\<times>real) set) top1_open_sets (C_S2 - {?N})
            = subspace_topology top1_S2 top1_S2_topology (C_S2 - {?N})"
        proof -
          have hprod_eq: "(top1_open_sets :: (real\<times>real\<times>real) set set) =
              product_topology_on top1_open_sets (product_topology_on top1_open_sets top1_open_sets)"
            using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                  product_topology_on_open_sets[where ?'a=real and ?'b=real] by (by100 simp)
          have hTS2_eq: "top1_S2_topology = subspace_topology UNIV
              (product_topology_on top1_open_sets (product_topology_on top1_open_sets top1_open_sets)) top1_S2"
            unfolding top1_S2_topology_def by (by100 simp)
          have "C_S2 - {?N} \<subseteq> top1_S2" using hC_sub_S2' by (by100 blast)
          have "subspace_topology top1_S2
              (subspace_topology UNIV (product_topology_on top1_open_sets
                  (product_topology_on top1_open_sets top1_open_sets)) top1_S2) (C_S2 - {?N})
              = subspace_topology UNIV (product_topology_on top1_open_sets
                  (product_topology_on top1_open_sets top1_open_sets)) (C_S2 - {?N})"
            by (rule subspace_topology_trans[OF \<open>C_S2 - {?N} \<subseteq> top1_S2\<close>])
          hence "subspace_topology top1_S2 top1_S2_topology (C_S2 - {?N})
              = subspace_topology UNIV (product_topology_on top1_open_sets
                  (product_topology_on top1_open_sets top1_open_sets)) (C_S2 - {?N})"
            unfolding hTS2_eq .
          thus ?thesis using hprod_eq by (by100 simp)
        qed
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>C_S2-{N} \<subseteq> S^2-{N}. \<sigma> continuous from S^2-{N} to R^2.\<close>
      have hC_sub_S2N: "C_S2 - {?N} \<subseteq> top1_S2 - {?N}" using hC_sub_S2' by (by100 blast)
      have h\<sigma>_cont_S2: "top1_continuous_map_on (top1_S2 - {?N})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {?N})) UNIV ?TR2 \<sigma>"
        using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
      have h\<sigma>_cont_C: "top1_continuous_map_on (C_S2 - {?N})
          (subspace_topology (top1_S2 - {?N}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {?N})) (C_S2 - {?N}))
          UNIV ?TR2 \<sigma>"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF h\<sigma>_cont_S2 hC_sub_S2N])
      have hsub_trans: "subspace_topology (top1_S2 - {?N})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {?N})) (C_S2 - {?N})
          = subspace_topology top1_S2 top1_S2_topology (C_S2 - {?N})"
        by (rule subspace_topology_trans[OF hC_sub_S2N])
      have h\<sigma>_cont_C': "top1_continuous_map_on (C_S2 - {?N})
          (subspace_topology top1_S2 top1_S2_topology (C_S2 - {?N})) UNIV ?TR2 \<sigma>"
        using h\<sigma>_cont_C unfolding hsub_trans .
      have hTC_N: "is_topology_on (C_S2 - {?N}) (subspace_topology top1_S2 top1_S2_topology (C_S2 - {?N}))"
        by (rule subspace_topology_is_topology_on[OF hTopS2]) (use hC_sub_S2' in \<open>by100 blast\<close>)
      \<comment> \<open>Image connected by Theorem_23_5.\<close>
      have "top1_connected_on (\<sigma> ` (C_S2 - {?N}))
          (subspace_topology UNIV ?TR2 (\<sigma> ` (C_S2 - {?N})))"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) ?TR2"
          using product_topology_on_is_topology_on[OF
            top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by (by100 simp)
        thus ?thesis by (rule Theorem_23_5[OF hTC_N _ hC_minus_N_conn h\<sigma>_cont_C'])
      qed
      thus ?thesis .
    qed
  qed
qed

text \<open>Invariance of domain in R^2.\<close>

theorem Theorem_62_3_invariance_of_domain:
  fixes U :: "(real \<times> real) set" and f :: "real \<times> real \<Rightarrow> real \<times> real"
  assumes "U \<in> product_topology_on top1_open_sets top1_open_sets"
      and "top1_continuous_map_on U
             (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) U)
             UNIV (product_topology_on top1_open_sets top1_open_sets) f"
      and "inj_on f U"
  shows "f ` U \<in> product_topology_on top1_open_sets top1_open_sets"
proof -
  let ?TR2 = "product_topology_on top1_open_sets top1_open_sets :: (real\<times>real) set set"
  \<comment> \<open>Show: for every y \<in> f(U), there exists open W with y \<in> W \<subseteq> f(U).
     Strategy (Munkres): For x = f\<inverse>(y) \<in> U, take closed ball B around x with B \<subseteq> U.
     Then f(Int B) is open (by JCT + Borsuk) and y = f(x) \<in> f(Int B) \<subseteq> f(U).\<close>
  have "\<forall>y\<in>f ` U. \<exists>W. y \<in> W \<and> W \<in> ?TR2 \<and> W \<subseteq> f ` U"
  proof
    fix y assume "y \<in> f ` U"
    then obtain x where hx: "x \<in> U" and hy: "y = f x" by (by100 blast)
    \<comment> \<open>Step 1: Closed ball B around x with B \<subseteq> U, Bd(B) \<cong> S^1.\<close>
    \<comment> \<open>U is open in R^2. Take a closed ball B \<subseteq> U around x.\<close>
    have hU_open: "open U"
    proof -
      have "?TR2 = (top1_open_sets :: (real\<times>real) set set)"
        by (rule product_topology_on_open_sets_real2)
      hence "U \<in> (top1_open_sets :: (real\<times>real) set set)" using assms(1) by (by100 simp)
      thus ?thesis unfolding top1_open_sets_def by (by100 blast)
    qed
    \<comment> \<open>Get rectangular neighborhood from open_prod_def.\<close>
    obtain A0 B0 where hA0: "open A0" and hB0: "open B0"
        and hx_AB: "x \<in> A0 \<times> B0" and hAB_U: "A0 \<times> B0 \<subseteq> U"
      using open_prod_elim[OF hU_open hx] by (by100 blast)
    \<comment> \<open>Get small radius: open intervals around fst x, snd x.\<close>
    have hfx_A0: "fst x \<in> A0" and hsx_B0: "snd x \<in> B0"
      using hx_AB by (by100 auto)+
    obtain ra where hra: "ra > 0" and hra_sub: "\<forall>t. dist t (fst x) < ra \<longrightarrow> t \<in> A0"
      using hA0 hfx_A0 unfolding open_dist by (by100 blast)
    obtain rb where hrb: "rb > 0" and hrb_sub: "\<forall>t. dist t (snd x) < rb \<longrightarrow> t \<in> B0"
      using hB0 hsx_B0 unfolding open_dist by (by100 blast)
    define r where "r = min ra rb / 2"
    have hr: "r > 0" unfolding r_def using hra hrb by (by100 simp)
    \<comment> \<open>Define closed ball of radius r centered at x.\<close>
    define B where "B = {y :: real \<times> real. (fst y - fst x)^2 + (snd y - snd x)^2 \<le> r^2}"
    \<comment> \<open>B \<subseteq> U: any point in the disk has each coordinate within distance r of x.\<close>
    have hBsub: "B \<subseteq> U"
    proof
      fix y assume hy: "y \<in> B"
      have hle: "(fst y - fst x)^2 + (snd y - snd x)^2 \<le> r^2"
        using hy unfolding B_def by (by100 blast)
      have hfst: "(fst y - fst x)^2 \<le> r^2"
      proof -
        have "(snd y - snd x)^2 \<ge> 0" by (by100 simp)
        thus ?thesis using hle by (by100 linarith)
      qed
      have hsnd: "(snd y - snd x)^2 \<le> r^2"
      proof -
        have "(fst y - fst x)^2 \<ge> 0" by (by100 simp)
        thus ?thesis using hle by (by100 linarith)
      qed
      have hfst_dist: "dist (fst y) (fst x) \<le> r"
      proof -
        have "r \<ge> 0" using hr by (by100 linarith)
        have "abs (fst y - fst x) ^ 2 = (fst y - fst x)^2" by (rule power2_abs)
        hence "\<bar>fst y - fst x\<bar>^2 \<le> r^2" using hfst by (by100 linarith)
        hence "\<bar>fst y - fst x\<bar> \<le> r" using \<open>r \<ge> 0\<close>
          using power2_le_imp_le by (by100 blast)
        thus ?thesis unfolding dist_real_def by (by100 simp)
      qed
      have hsnd_dist: "dist (snd y) (snd x) \<le> r"
      proof -
        have "r \<ge> 0" using hr by (by100 linarith)
        have "abs (snd y - snd x) ^ 2 = (snd y - snd x)^2" by (rule power2_abs)
        hence "\<bar>snd y - snd x\<bar>^2 \<le> r^2" using hsnd by (by100 linarith)
        hence "\<bar>snd y - snd x\<bar> \<le> r" using \<open>r \<ge> 0\<close>
          using power2_le_imp_le by (by100 blast)
        thus ?thesis unfolding dist_real_def by (by100 simp)
      qed
      have hr_ra: "r < ra" unfolding r_def using hra hrb by (by100 linarith)
      have hr_rb: "r < rb" unfolding r_def using hra hrb by (by100 linarith)
      have "dist (fst y) (fst x) < ra" using hfst_dist hr_ra by (by100 linarith)
      hence "fst y \<in> A0" using hra_sub by (by100 blast)
      moreover have "dist (snd y) (snd x) < rb" using hsnd_dist hr_rb by (by100 linarith)
      hence "snd y \<in> B0" using hrb_sub by (by100 blast)
      ultimately have "y \<in> A0 \<times> B0" using mem_Times_iff[of y A0 B0] by (by100 simp)
      thus "y \<in> U" using hAB_U by (by100 blast)
    qed
    \<comment> \<open>B closed: {y | continuous_function(y) \<le> constant} is closed.\<close>
    have hBclosed: "closed B"
    proof -
      let ?g = "\<lambda>y :: real \<times> real. (fst y - fst x)^2 + (snd y - snd x)^2"
      have hcont: "continuous_on UNIV ?g" by (intro continuous_intros)
      have "B = ?g -` {..r^2}" unfolding B_def by (by100 auto)
      moreover have "closed (?g -` {..r^2})"
        using closed_vimage[OF closed_atMost hcont] by (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>x \<in> B - frontier B: x is the center of the disk.\<close>
    have hx_int: "x \<in> B - frontier B"
    proof -
      have hxB: "x \<in> B" unfolding B_def using hr by (by100 simp)
      have "x \<notin> frontier B"
      proof
        assume hxf: "x \<in> frontier B"
        \<comment> \<open>The open ball Br of radius r around x is inside B.\<close>
        define Br where "Br = {y :: real \<times> real. (fst y - fst x)^2 + (snd y - snd x)^2 < r^2}"
        have hBr_open: "open Br"
        proof -
          have "Br = (\<lambda>y. (fst y - fst x)^2 + (snd y - snd x)^2) -` {..<r^2}"
            unfolding Br_def by (by100 auto)
          moreover have "open ((\<lambda>y :: real \<times> real. (fst y - fst x)^2 + (snd y - snd x)^2) -` {..<r^2})"
            by (rule open_vimage) (auto intro!: continuous_intros)
          ultimately show ?thesis by (by100 simp)
        qed
        have hx_Br: "x \<in> Br" unfolding Br_def using hr by (by100 simp)
        have hBr_sub: "Br \<subseteq> B" unfolding Br_def B_def by (by100 auto)
        \<comment> \<open>frontier B: every open nbhd of x meets -B. But Br \<subseteq> B, so Br \<inter> (-B) = {}.\<close>
        have "Br \<inter> (- B) = {}" using hBr_sub by (by100 blast)
        moreover have "Br \<inter> (- B) \<noteq> {}"
          using hxf hBr_open hx_Br unfolding frontier_def by (by100 blast)
        ultimately show False by (by100 blast)
      qed
      thus ?thesis using hxB by (by100 blast)
    qed
    \<comment> \<open>frontier B = circle of radius r centered at x.\<close>
    let ?circle = "{y :: real \<times> real. (fst y - fst x)^2 + (snd y - snd x)^2 = r^2}"
    have hfr_eq_top: "frontier B = ?circle"
    proof (intro set_eqI iffI)
      fix y assume hy: "y \<in> frontier B"
      let ?g = "\<lambda>y :: real \<times> real. (fst y - fst x)^2 + (snd y - snd x)^2"
      have hg_cont: "continuous_on UNIV ?g" by (intro continuous_intros)
      show "y \<in> ?circle"
      proof (rule ccontr)
        assume "y \<notin> ?circle" hence "?g y \<noteq> r^2" by (by100 blast)
        thus False
        proof (cases "?g y < r^2")
          case True
          have "open (?g -` {..<r^2})" by (rule open_vimage[OF open_lessThan hg_cont])
          moreover have "y \<in> ?g -` {..<r^2}" using True by (by100 blast)
          moreover have "?g -` {..<r^2} \<inter> (- B) = {}" unfolding B_def by (by100 auto)
          ultimately show False using hy unfolding frontier_def by (by100 blast)
        next
          case False hence "?g y > r^2" using \<open>?g y \<noteq> r^2\<close> by (by100 linarith)
          have "open (?g -` {r^2<..})" by (rule open_vimage[OF open_greaterThan hg_cont])
          moreover have "y \<in> ?g -` {r^2<..}" using \<open>?g y > r^2\<close> by (by100 blast)
          moreover have "?g -` {r^2<..} \<inter> B = {}" unfolding B_def by (by100 auto)
          ultimately show False using hy unfolding frontier_def by (by100 blast)
        qed
      qed
    next
      fix y assume hy: "y \<in> ?circle"
      hence hg_eq: "(fst y - fst x)^2 + (snd y - snd x)^2 = r^2" by (by100 blast)
      show "y \<in> frontier B" unfolding frontier_def
      proof (intro CollectI conjI allI impI)
        fix V :: "(real \<times> real) set" assume hV: "open V" and hyV: "y \<in> V"
        show "V \<inter> B \<noteq> {}"
        proof -
          have "y \<in> B" unfolding B_def using hg_eq by (by100 auto)
          thus ?thesis using hyV by (by100 blast)
        qed
        show "V \<inter> (- B) \<noteq> {}"
        proof -
          obtain A0' B0' where hA0': "open A0'" and hB0': "open B0'"
              and hy_AB: "y \<in> A0' \<times> B0'" and hAB_V: "A0' \<times> B0' \<subseteq> V"
            using open_prod_elim[OF hV hyV] by (by100 blast)
          obtain d1 where hd1: "d1 > 0" and hd1_sub: "\<forall>t. dist t (fst y) < d1 \<longrightarrow> t \<in> A0'"
            using hA0' hy_AB unfolding open_dist by (by100 auto)
          obtain d2 where hd2: "d2 > 0" and hd2_sub: "\<forall>t. dist t (snd y) < d2 \<longrightarrow> t \<in> B0'"
            using hB0' hy_AB unfolding open_dist by (by100 auto)
          define \<epsilon>0 where "\<epsilon>0 = min d1 d2 / (2 * (r + 1))"
          have h\<epsilon>0: "\<epsilon>0 > 0" unfolding \<epsilon>0_def using hd1 hd2 hr by (by100 simp)
          define z0 where "z0 = (fst x + (1 + \<epsilon>0) * (fst y - fst x), snd x + (1 + \<epsilon>0) * (snd y - snd x))"
          have "z0 \<notin> B"
          proof -
            have hfz0: "fst z0 - fst x = (1 + \<epsilon>0) * (fst y - fst x)" unfolding z0_def by (by100 simp)
            have hsz0: "snd z0 - snd x = (1 + \<epsilon>0) * (snd y - snd x)" unfolding z0_def by (by100 simp)
            have "(fst z0 - fst x)^2 + (snd z0 - snd x)^2
                = ((1 + \<epsilon>0) * (fst y - fst x))^2 + ((1 + \<epsilon>0) * (snd y - snd x))^2"
              using hfz0 hsz0 by (by100 simp)
            also have "... = (1 + \<epsilon>0)^2 * ((fst y - fst x)^2 + (snd y - snd x)^2)"
              by (by100 algebra)
            also have "... = (1 + \<epsilon>0)^2 * r^2" using hg_eq by (by100 simp)
            finally have hgz0: "(fst z0 - fst x)^2 + (snd z0 - snd x)^2 = (1 + \<epsilon>0)^2 * r^2" .
            have "(1 + \<epsilon>0) > 1" using h\<epsilon>0 by (by100 linarith)
            hence "(1 + \<epsilon>0)^2 > 1^2" by (rule power_strict_mono) (by100 linarith)+
            hence "(1 + \<epsilon>0)^2 * r^2 > 1 * r^2"
              using hr by (intro mult_strict_right_mono) (by100 simp)+
            hence "(1 + \<epsilon>0)^2 * r^2 > r^2" by (by100 simp)
            have "(fst z0 - fst x)^2 + (snd z0 - snd x)^2 > r^2"
              using hgz0 \<open>(1 + \<epsilon>0)^2 * r^2 > r^2\<close> by (by100 linarith)
            thus "z0 \<notin> B" unfolding B_def by (by100 auto)
          qed
          moreover have "z0 \<in> V"
          proof -
            have h\<epsilon>0_bound: "\<epsilon>0 * r < min d1 d2 / 2"
            proof -
              have "r + 1 > 0" using hr by (by100 linarith)
              hence h2rp: "(2::real) * (r + 1) > 0" by (by100 simp)
              have h2rp_ne: "(2::real) * (r + 1) \<noteq> 0" using h2rp by (by100 linarith)
              have h_eq: "\<epsilon>0 = min d1 d2 / (2 * (r + 1))" unfolding \<epsilon>0_def by (by100 simp)
              have "\<epsilon>0 * (2 * (r + 1)) = min d1 d2 / (2 * (r + 1)) * (2 * (r + 1))"
                using h_eq by (by100 simp)
              also have "... = min d1 d2"
                using h2rp_ne nonzero_mult_div_cancel_right[of "2*(r+1)" "min d1 d2"] by (by100 simp)
              finally have h_cancel: "\<epsilon>0 * (2 * (r + 1)) = min d1 d2" .
              have "\<epsilon>0 * r * (2 * (r + 1)) = (\<epsilon>0 * (2 * (r + 1))) * r" by (by100 algebra)
              also have "... = min d1 d2 * r" using h_cancel by (by100 simp)
              finally have h_mul: "\<epsilon>0 * r * (2 * (r + 1)) = min d1 d2 * r" .
              have "min d1 d2 * r < min d1 d2 * (r + 1)" using hd1 hd2 by (by100 simp)
              also have "... = min d1 d2 / 2 * (2 * (r + 1))" by (by100 algebra)
              finally have "\<epsilon>0 * r * (2 * (r + 1)) < min d1 d2 / 2 * (2 * (r + 1))"
                using h_mul by (by100 linarith)
              thus ?thesis using h2rp by (by100 simp)
            qed
            have hfabs0: "\<bar>fst y - fst x\<bar> \<le> r"
            proof -
              have "(snd y - snd x)^2 \<ge> 0" by (by100 simp)
              hence "(fst y - fst x)^2 \<le> r^2" using hg_eq by (by100 linarith)
              have "abs (fst y - fst x) ^ 2 = (fst y - fst x)^2" by (rule power2_abs)
              hence "\<bar>fst y - fst x\<bar>^2 \<le> r^2" using \<open>(fst y - fst x)^2 \<le> r^2\<close> by (by100 linarith)
              show ?thesis
              proof (rule power2_le_imp_le)
                show "\<bar>fst y - fst x\<bar>\<^sup>2 \<le> r\<^sup>2" using \<open>\<bar>fst y - fst x\<bar>^2 \<le> r^2\<close> by (by100 simp)
                show "0 \<le> r" using hr by (by100 linarith)
              qed
            qed
            have hsabs0: "\<bar>snd y - snd x\<bar> \<le> r"
            proof -
              have "(fst y - fst x)^2 \<ge> 0" by (by100 simp)
              hence "(snd y - snd x)^2 \<le> r^2" using hg_eq by (by100 linarith)
              have "abs (snd y - snd x) ^ 2 = (snd y - snd x)^2" by (rule power2_abs)
              hence "\<bar>snd y - snd x\<bar>^2 \<le> r^2" using \<open>(snd y - snd x)^2 \<le> r^2\<close> by (by100 linarith)
              show ?thesis
              proof (rule power2_le_imp_le)
                show "\<bar>snd y - snd x\<bar>\<^sup>2 \<le> r\<^sup>2" using \<open>\<bar>snd y - snd x\<bar>^2 \<le> r^2\<close> by (by100 simp)
                show "0 \<le> r" using hr by (by100 linarith)
              qed
            qed
            have hfz0_y: "fst z0 - fst y = \<epsilon>0 * (fst y - fst x)"
            proof -
              have "fst z0 = fst x + (1 + \<epsilon>0) * (fst y - fst x)" unfolding z0_def by (by100 simp)
              thus ?thesis by (by100 algebra)
            qed
            have hsz0_y: "snd z0 - snd y = \<epsilon>0 * (snd y - snd x)"
            proof -
              have "snd z0 = snd x + (1 + \<epsilon>0) * (snd y - snd x)" unfolding z0_def by (by100 simp)
              thus ?thesis by (by100 algebra)
            qed
            have "dist (fst z0) (fst y) = \<bar>\<epsilon>0 * (fst y - fst x)\<bar>"
              unfolding dist_real_def using hfz0_y by (by100 simp)
            also have "... = \<epsilon>0 * \<bar>fst y - fst x\<bar>"
              using h\<epsilon>0 abs_mult[of \<epsilon>0 "fst y - fst x"] by (by100 simp)
            also have "... \<le> \<epsilon>0 * r" using hfabs0 h\<epsilon>0 by (intro mult_left_mono) (by100 linarith)+
            also have "... < min d1 d2 / 2" by (rule h\<epsilon>0_bound)
            also have "... \<le> d1" using hd1 hd2 by (by100 linarith)
            finally have "dist (fst z0) (fst y) < d1" .
            hence "fst z0 \<in> A0'" using hd1_sub by (by100 blast)
            have "dist (snd z0) (snd y) = \<bar>\<epsilon>0 * (snd y - snd x)\<bar>"
              unfolding dist_real_def using hsz0_y by (by100 simp)
            also have "... = \<epsilon>0 * \<bar>snd y - snd x\<bar>"
              using h\<epsilon>0 abs_mult[of \<epsilon>0 "snd y - snd x"] by (by100 simp)
            also have "... \<le> \<epsilon>0 * r" using hsabs0 h\<epsilon>0 by (intro mult_left_mono) (by100 linarith)+
            also have "... < min d1 d2 / 2" by (rule h\<epsilon>0_bound)
            also have "... \<le> d2" using hd1 hd2 by (by100 linarith)
            finally have "dist (snd z0) (snd y) < d2" .
            hence "snd z0 \<in> B0'" using hd2_sub by (by100 blast)
            have "z0 \<in> A0' \<times> B0'" unfolding z0_def
              using \<open>fst z0 \<in> A0'\<close> \<open>snd z0 \<in> B0'\<close> unfolding z0_def by (by100 simp)
            thus "z0 \<in> V" using hAB_V by (by100 blast)
          qed
          ultimately show ?thesis by (by100 blast)
        qed
      qed
    qed
    \<comment> \<open>frontier B \<cong> S^1: the circle of radius r is homeomorphic to S^1.\<close>
    have hBd_S1: "\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
        (frontier B) (subspace_topology UNIV ?TR2 (frontier B)) h"
    proof -
      \<comment> \<open>The circle of radius r centered at x.\<close>
      let ?circle = "{y :: real \<times> real. (fst y - fst x)^2 + (snd y - snd x)^2 = r^2}"
      have hfr_eq: "frontier B = ?circle" by (rule hfr_eq_top)
      \<comment> \<open>The homeomorphism h: S^1 \<rightarrow> frontier B = circle, h(a,b) = (cx+r*a, cy+r*b).\<close>
      define hh where "hh = (\<lambda>p :: real \<times> real. (fst x + r * fst p, snd x + r * snd p))"
      \<comment> \<open>hh continuous: polynomial, hence continuous on S^1 with subspace topology.\<close>
      have hh_range: "\<And>p. p \<in> top1_S1 \<Longrightarrow> hh p \<in> frontier B"
      proof -
        fix p assume hp: "p \<in> top1_S1"
        have "fst p ^ 2 + snd p ^ 2 = 1" using hp unfolding top1_S1_def by (by100 blast)
        have "(fst (hh p) - fst x)^2 + (snd (hh p) - snd x)^2 = r^2"
        proof -
          have "fst (hh p) - fst x = r * fst p" unfolding hh_def by (by100 simp)
          moreover have "snd (hh p) - snd x = r * snd p" unfolding hh_def by (by100 simp)
          ultimately have "(fst (hh p) - fst x)^2 + (snd (hh p) - snd x)^2 = (r*fst p)^2 + (r*snd p)^2"
            by (by100 simp)
          also have "... = r^2 * (fst p^2 + snd p^2)" by (by100 algebra)
          also have "... = r^2" using \<open>fst p ^ 2 + snd p ^ 2 = 1\<close> by (by100 simp)
          finally show ?thesis .
        qed
        thus "hh p \<in> frontier B" unfolding hfr_eq by (by100 blast)
      qed
      have hh_cont_std: "continuous_on UNIV hh"
        unfolding hh_def by (intro continuous_intros)
      have hh_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
          (frontier B) (subspace_topology UNIV ?TR2 (frontier B)) hh"
      proof -
        have hcont_S1: "continuous_on top1_S1 hh"
          using continuous_on_subset[OF hh_cont_std subset_UNIV] by (by100 blast)
        show ?thesis unfolding top1_S1_topology_def
          by (rule top1_continuous_map_on_real2_subspace_general[OF hh_range hcont_S1])
      qed
      \<comment> \<open>hh injective: r > 0 ensures (a1,b1) \<noteq> (a2,b2) \<Rightarrow> hh(a1,b1) \<noteq> hh(a2,b2).\<close>
      have hh_inj: "inj_on hh top1_S1"
        unfolding hh_def inj_on_def using hr by (by100 auto)
      \<comment> \<open>hh surjective: for y \<in> frontier B = circle, ((fst y - cx)/r, (snd y - cy)/r) \<in> S^1.\<close>
      have hh_surj: "hh ` top1_S1 = frontier B"
      proof (intro set_eqI iffI)
        fix y assume "y \<in> hh ` top1_S1"
        then obtain p where hp: "p \<in> top1_S1" and hy: "y = hh p" by (by100 blast)
        have "fst p ^ 2 + snd p ^ 2 = 1" using hp unfolding top1_S1_def by (by100 blast)
        have "(fst y - fst x)^2 + (snd y - snd x)^2 = r^2"
        proof -
          have "fst y - fst x = r * fst p" unfolding hy hh_def by (by100 simp)
          moreover have "snd y - snd x = r * snd p" unfolding hy hh_def by (by100 simp)
          ultimately have "(fst y - fst x)^2 + (snd y - snd x)^2 = (r * fst p)^2 + (r * snd p)^2"
            by (by100 simp)
          also have "... = r^2 * (fst p^2 + snd p^2)" by (by100 algebra)
          also have "... = r^2" using \<open>fst p ^ 2 + snd p ^ 2 = 1\<close> by (by100 simp)
          finally show ?thesis .
        qed
        thus "y \<in> frontier B" unfolding hfr_eq by (by100 blast)
      next
        fix y assume "y \<in> frontier B"
        thus "y \<in> hh ` top1_S1"
        proof -
          assume "y \<in> frontier B"
          hence "y \<in> ?circle" using hfr_eq by (by100 blast)
          hence hcirc: "(fst y - fst x)^2 + (snd y - snd x)^2 = r^2" by (by100 blast)
          have "r \<noteq> 0" using hr by (by100 linarith)
          let ?p = "((fst y - fst x)/r, (snd y - snd x)/r)"
          have "hh ?p = y"
          proof -
            have "fst (hh ?p) = fst y" unfolding hh_def using \<open>r \<noteq> 0\<close> by (by100 simp)
            moreover have "snd (hh ?p) = snd y" unfolding hh_def using \<open>r \<noteq> 0\<close> by (by100 simp)
            ultimately show ?thesis by (rule prod_eqI)
          qed
          moreover have "?p \<in> top1_S1" unfolding top1_S1_def
          proof (intro CollectI)
            have "r^2 > 0" using hr by (by100 simp)
            have "r^2 * (fst ?p ^ 2 + snd ?p ^ 2) = r^2 * 1"
            proof -
              have hfp: "fst ?p = (fst y - fst x) / r" by (by100 simp)
              have hsp: "snd ?p = (snd y - snd x) / r" by (by100 simp)
              have h_div_sq: "\<And>a :: real. r^2 * (a/r)^2 = a^2"
              proof -
                fix a :: real
                have "(a/r) = a * (1/r)" by (by100 simp)
                hence "(a/r)^2 = a^2 * (1/r)^2" by (by100 algebra)
                hence "r^2 * (a/r)^2 = r^2 * a^2 * (1/r)^2" by (by100 algebra)
                also have "... = a^2 * (r^2 * (1/r)^2)" by (by100 algebra)
                also have "r^2 * (1/r)^2 = (r * (1/r))^2" by (by100 algebra)
                also have "... = 1" using \<open>r \<noteq> 0\<close> by (by100 simp)
                finally show "r^2 * (a/r)^2 = a^2" by (by100 simp)
              qed
              have "r^2 * fst ?p ^ 2 = (fst y - fst x)^2"
                unfolding hfp by (rule h_div_sq)
              moreover have "r^2 * snd ?p ^ 2 = (snd y - snd x)^2"
                unfolding hsp by (rule h_div_sq)
              ultimately have "r^2 * (fst ?p ^ 2 + snd ?p ^ 2)
                  = (fst y - fst x)^2 + (snd y - snd x)^2"
                by (by100 algebra)
              thus ?thesis using hcirc by (by100 simp)
            qed
            thus "fst ?p ^ 2 + snd ?p ^ 2 = 1" using \<open>r^2 > 0\<close> by (by100 simp)
          qed
          ultimately show "y \<in> hh ` top1_S1" by (by100 force)
        qed
      qed
      \<comment> \<open>hh inverse continuous: ((fst y - cx)/r, (snd y - cy)/r) is continuous.\<close>
      \<comment> \<open>Use Theorem 26.6: compact + Hausdorff + continuous bijection \<Rightarrow> homeomorphism.\<close>
      have hh_bij: "bij_betw hh top1_S1 (frontier B)" unfolding bij_betw_def
        using hh_inj hh_surj by (by100 blast)
      have hTR2: "is_topology_on (UNIV :: (real\<times>real) set) ?TR2"
        using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
              top1_open_sets_is_topology_on_UNIV]
        by (by100 simp)
      have hTS1: "is_topology_on top1_S1 top1_S1_topology"
        unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
      have hTfr: "is_topology_on (frontier B) (subspace_topology UNIV ?TR2 (frontier B))"
        by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
      have hfr_haus: "is_hausdorff_on (frontier B) (subspace_topology UNIV ?TR2 (frontier B))"
        using conjunct2[OF conjunct2[OF Theorem_17_11]] top1_R2_is_hausdorff by (by100 blast)
      have "top1_homeomorphism_on top1_S1 top1_S1_topology
          (frontier B) (subspace_topology UNIV ?TR2 (frontier B)) hh"
        by (rule Theorem_26_6[OF hTS1 hTfr S1_compact hfr_haus hh_cont hh_bij])
      thus ?thesis by (by100 blast)
    qed
    \<comment> \<open>Step 2: f(Bd B) is a SCC (f injective continuous on compact, Bd B \<cong> S^1).\<close>
    have hfBd_SCC: "top1_simple_closed_curve_on UNIV ?TR2 (f ` frontier B)"
    proof -
      obtain h where hh: "top1_homeomorphism_on top1_S1 top1_S1_topology
          (frontier B) (subspace_topology UNIV ?TR2 (frontier B)) h"
        using hBd_S1 by (by100 blast)
      \<comment> \<open>Extract parts from the homeomorphism separately.\<close>
      have hh_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
          (frontier B) (subspace_topology UNIV ?TR2 (frontier B)) h"
        and hh_bij: "bij_betw h top1_S1 (frontier B)"
        using hh[unfolded top1_homeomorphism_on_def] by (by100 blast)+
      have hh_img: "h ` top1_S1 = frontier B"
        using hh_bij[unfolded bij_betw_def] by (by100 blast)
      have hh_inj: "inj_on h top1_S1"
        using hh_bij[unfolded bij_betw_def] by (by100 blast)
      \<comment> \<open>frontier B \<subseteq> U (since B closed and B \<subseteq> U).\<close>
      have hfr_sub: "frontier B \<subseteq> U"
        using frontier_closed_sub[OF hBclosed] hBsub by (by100 blast)
      \<comment> \<open>f restricted to frontier B is continuous.\<close>
      have hf_cont_B: "top1_continuous_map_on (frontier B) (subspace_topology UNIV ?TR2 (frontier B))
          UNIV ?TR2 f"
      proof -
        have "top1_continuous_map_on (frontier B)
            (subspace_topology U (subspace_topology UNIV ?TR2 U) (frontier B))
            UNIV ?TR2 f"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF assms(2) hfr_sub])
        moreover have "subspace_topology U (subspace_topology UNIV ?TR2 U) (frontier B)
            = subspace_topology UNIV ?TR2 (frontier B)"
          by (rule subspace_topology_trans[OF hfr_sub])
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>f injective on frontier B.\<close>
      have hf_inj_B: "inj_on f (frontier B)"
        using assms(3) hfr_sub by (rule inj_on_subset)
      \<comment> \<open>Compose: f \<circ> h : S^1 \<rightarrow> R^2 continuous, injective, image = f(frontier B).\<close>
      have "(f \<circ> h) ` top1_S1 = f ` frontier B" unfolding hh_img[symmetric] by (by100 auto)
      moreover have "top1_continuous_map_on top1_S1 top1_S1_topology UNIV ?TR2 (f \<circ> h)"
        by (rule top1_continuous_map_on_comp[OF hh_cont hf_cont_B])
      moreover have "inj_on (f \<circ> h) top1_S1"
      proof (rule comp_inj_on[OF hh_inj])
        show "inj_on f (h ` top1_S1)" unfolding hh_img by (rule hf_inj_B)
      qed
      ultimately show ?thesis unfolding top1_simple_closed_curve_on_def by (by100 blast)
    qed
    \<comment> \<open>Step 3: JCT gives bounded component W1 and unbounded W2.\<close>
    obtain W1 W2 where hW: "W1 \<noteq> {}" "W2 \<noteq> {}" "W1 \<inter> W2 = {}"
        "W1 \<union> W2 = UNIV - f ` frontier B"
        "top1_path_connected_on W1 (subspace_topology UNIV ?TR2 W1)"
        "top1_path_connected_on W2 (subspace_topology UNIV ?TR2 W2)"
        "(\<exists>M. \<forall>p\<in>W1. fst p ^ 2 + snd p ^ 2 \<le> M)"
        "(\<forall>M. \<exists>p\<in>W2. fst p ^ 2 + snd p ^ 2 > M)"
        and hW1_cl: "closure_on UNIV ?TR2 W1 = W1 \<union> f ` frontier B"
        and hW2_cl: "closure_on UNIV ?TR2 W2 = W2 \<union> f ` frontier B"
    proof -
      obtain U' V where "U' \<noteq> {}" "V \<noteq> {}" "U' \<inter> V = {}" "U' \<union> V = UNIV - f ` frontier B"
          "top1_path_connected_on U' (subspace_topology UNIV ?TR2 U')"
          "top1_path_connected_on V (subspace_topology UNIV ?TR2 V)"
          "\<exists>M. \<forall>p\<in>U'. fst p ^ 2 + snd p ^ 2 \<le> M"
          "\<forall>M. \<exists>p\<in>V. fst p ^ 2 + snd p ^ 2 > M"
          "closure_on UNIV ?TR2 U' = U' \<union> f ` frontier B"
          "closure_on UNIV ?TR2 V = V \<union> f ` frontier B"
        using Theorem_63_4_JordanCurve[OF hfBd_SCC] by metis
      thus ?thesis using that by simp
    qed
    \<comment> \<open>Common fact: B compact and f(B) bounded, W2 has escape points.\<close>
    have hBcompact: "compact B"
    proof -
      \<comment> \<open>B \<subseteq> closed square of side 2r centered at x.\<close>
      let ?sq = "{fst x - r .. fst x + r} \<times> {snd x - r .. snd x + r}"
      have hB_sq: "B \<subseteq> ?sq"
      proof (rule subsetI)
        fix y assume hy: "y \<in> B"
        hence hle: "(fst y - fst x)^2 + (snd y - snd x)^2 \<le> r^2" unfolding B_def by (by100 auto)
        have hfst: "(fst y - fst x)^2 \<le> r^2"
        proof -
          have "(snd y - snd x)^2 \<ge> 0" by (by100 simp)
          thus ?thesis using hle by (by100 linarith)
        qed
        have hsnd: "(snd y - snd x)^2 \<le> r^2"
        proof -
          have "(fst y - fst x)^2 \<ge> 0" by (by100 simp)
          thus ?thesis using hle by (by100 linarith)
        qed
        have hr_nn: "r \<ge> 0" using hr by (by100 linarith)
        have "fst y - fst x \<le> r" using power2_le_imp_le[OF hfst hr_nn] .
        moreover have "fst x - fst y \<le> r"
        proof -
          have "(fst x - fst y)^2 = (fst y - fst x)^2" by (by100 algebra)
          hence "(fst x - fst y)^2 \<le> r^2" using hfst by (by100 linarith)
          thus ?thesis using power2_le_imp_le[OF _ hr_nn] by (by100 blast)
        qed
        moreover have "snd y - snd x \<le> r" using power2_le_imp_le[OF hsnd hr_nn] .
        moreover have "snd x - snd y \<le> r"
        proof -
          have "(snd x - snd y)^2 = (snd y - snd x)^2" by (by100 algebra)
          hence "(snd x - snd y)^2 \<le> r^2" using hsnd by (by100 linarith)
          thus ?thesis using power2_le_imp_le[OF _ hr_nn] by (by100 blast)
        qed
        ultimately show "y \<in> ?sq" by (cases y) (by100 auto)
      qed
      \<comment> \<open>Square compact via top1 bridge.\<close>
      have hsq_compact: "compact ?sq"
      proof -
        have h1: "compact ({fst x - r .. fst x + r} :: real set)" by (rule compact_Icc)
        have h1': "top1_compact_on {fst x - r .. fst x + r}
            (subspace_topology (UNIV::real set) top1_open_sets {fst x - r .. fst x + r})"
          using top1_compact_on_subspace_UNIV_iff_compact h1 by (by100 blast)
        have h2: "compact ({snd x - r .. snd x + r} :: real set)" by (rule compact_Icc)
        have h2': "top1_compact_on {snd x - r .. snd x + r}
            (subspace_topology (UNIV::real set) top1_open_sets {snd x - r .. snd x + r})"
          using top1_compact_on_subspace_UNIV_iff_compact h2 by (by100 blast)
        have hprod: "top1_compact_on ?sq
            (product_topology_on (subspace_topology UNIV top1_open_sets {fst x - r .. fst x + r})
                                 (subspace_topology UNIV top1_open_sets {snd x - r .. snd x + r}))"
          by (rule Theorem_26_7[OF h1' h2'])
        have hTR2_eq: "?TR2 = (top1_open_sets :: (real\<times>real) set set)"
          using product_topology_on_open_sets_real2 by (by100 metis)
        have heq: "product_topology_on
            (subspace_topology UNIV top1_open_sets {fst x - r .. fst x + r})
            (subspace_topology UNIV top1_open_sets {snd x - r .. snd x + r})
          = subspace_topology (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets) ?sq"
          using Theorem_16_3[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by (by100 simp)
        have "top1_compact_on ?sq (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets ?sq)"
          using hprod unfolding heq hTR2_eq by (by100 simp)
        thus ?thesis using top1_compact_on_subspace_UNIV_iff_compact by (by100 blast)
      qed
      show ?thesis by (rule compact_Int_closed[OF hsq_compact hBclosed, simplified Int_absorb1[OF hB_sq]])
    qed
    have hfB_compact: "compact (f ` B)"
    proof -
      have "continuous_on B f"
        using continuous_on_subset[OF top1_continuous_map_on_to_continuous_on_R2[OF assms(2)] hBsub] .
      thus ?thesis by (rule compact_continuous_image[OF _ hBcompact])
    qed
    have hW2_escape: "\<forall>a. a \<notin> f ` B \<longrightarrow> (\<exists>b1. b1 \<in> W2 \<and> b1 \<notin> f ` B)"
    proof (intro allI impI)
      fix a assume "a \<notin> f ` B"
      have "\<exists>M. \<forall>y \<in> f ` B. (fst y)\<^sup>2 + (snd y)\<^sup>2 \<le> M"
      proof (cases "f ` B = {}")
        case True thus ?thesis by (by100 blast)
      next
        case False
        have "continuous_on (f ` B) (\<lambda>y::(real\<times>real). (fst y)\<^sup>2 + (snd y)\<^sup>2)"
          by (intro continuous_intros)
        from continuous_attains_sup[OF hfB_compact False this]
        obtain y0 where "y0 \<in> f ` B"
            and "\<forall>y\<in>f ` B. (fst y)\<^sup>2 + (snd y)\<^sup>2 \<le> (fst y0)\<^sup>2 + (snd y0)\<^sup>2"
          by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      then obtain M where hM: "\<forall>y \<in> f ` B. (fst y)\<^sup>2 + (snd y)\<^sup>2 \<le> M" by (by100 blast)
      from hW(8)[THEN spec[of _ "max M 0 + 1"]]
      obtain p where hp_W2: "p \<in> W2" and hp_big: "(fst p)\<^sup>2 + (snd p)\<^sup>2 > max M 0 + 1"
        by (by100 blast)
      have "p \<notin> f ` B"
      proof
        assume "p \<in> f ` B"
        hence "(fst p)\<^sup>2 + (snd p)\<^sup>2 \<le> M" using hM by (by100 blast)
        with hp_big show False by (by100 linarith)
      qed
      thus "\<exists>b1. b1 \<in> W2 \<and> b1 \<notin> f ` B" using hp_W2 by (by100 blast)
    qed
    \<comment> \<open>W1 and W2 are open (complement of closure of the other).\<close>
    have hTR2_top: "is_topology_on (UNIV :: (real\<times>real) set) ?TR2"
      using product_topology_on_is_topology_on[OF
        top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by (by100 simp)
    have hW1_is_open: "open W1"
    proof -
      have "closedin_on UNIV ?TR2 (closure_on UNIV ?TR2 W2)"
        by (rule closure_on_closed[OF hTR2_top]) (by100 simp)
      hence "UNIV - closure_on UNIV ?TR2 W2 \<in> ?TR2"
        unfolding closedin_on_def by (by100 blast)
      moreover have "W2 \<inter> f ` frontier B = {}" using hW(3) hW(4) by (by100 blast)
      hence "UNIV - (W2 \<union> f ` frontier B) = W1" using hW(3) hW(4) by (by100 blast)
      hence "UNIV - closure_on UNIV ?TR2 W2 = W1" unfolding hW2_cl .
      ultimately have "W1 \<in> ?TR2" by (by100 simp)
      thus ?thesis using product_topology_on_open_sets_real2
        unfolding top1_open_sets_def by (by100 simp)
    qed
    have hW2_is_open: "open W2"
    proof -
      have "closedin_on UNIV ?TR2 (closure_on UNIV ?TR2 W1)"
        by (rule closure_on_closed[OF hTR2_top]) (by100 simp)
      hence "UNIV - closure_on UNIV ?TR2 W1 \<in> ?TR2"
        unfolding closedin_on_def by (by100 blast)
      moreover have "W1 \<inter> f ` frontier B = {}" using hW(3) hW(4) by (by100 blast)
      hence "UNIV - (W1 \<union> f ` frontier B) = W2" using hW(3) hW(4) by (by100 blast)
      hence "UNIV - closure_on UNIV ?TR2 W1 = W2" unfolding hW1_cl .
      ultimately have "W2 \<in> ?TR2" by (by100 simp)
      thus ?thesis using product_topology_on_open_sets_real2
        unfolding top1_open_sets_def by (by100 simp)
    qed
    have hfr_compact: "compact (frontier B)"
    proof -
      \<comment> \<open>frontier always closed: complement = interior(B) \<union> interior(-B), both open.\<close>
      have hfr_closed: "closed (frontier B)"
      proof -
        have "open (- frontier B)"
        proof (rule openI)
          fix x assume hx: "x \<in> - frontier B"
          hence "\<exists>U. open U \<and> x \<in> U \<and> (U \<inter> B = {} \<or> U \<inter> (- B) = {})"
            unfolding frontier_def by (by100 blast)
          then obtain U where hU: "open U" "x \<in> U" and hU_disj: "U \<inter> B = {} \<or> U \<inter> (- B) = {}"
            by (by100 blast)
          have "U \<subseteq> - frontier B"
          proof (rule subsetI)
            fix y assume "y \<in> U"
            show "y \<in> - frontier B" unfolding frontier_def
              using hU(1) \<open>y \<in> U\<close> hU_disj by (by100 blast)
          qed
          thus "\<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> - frontier B"
            using hU by (by100 blast)
        qed
        hence "closed (- (- frontier B))" using open_closed by (by100 blast)
        thus ?thesis by (by100 simp)
      qed
      have "frontier B \<subseteq> B" by (rule frontier_closed_sub[OF hBclosed])
      hence "B \<inter> frontier B = frontier B" by (by100 blast)
      thus ?thesis using compact_Int_closed[OF hBcompact hfr_closed] by (by100 simp)
    qed
    have hfr_sub_B_top: "frontier B \<subseteq> B" by (rule frontier_closed_sub[OF hBclosed])
    \<comment> \<open>Step 4: f(Int B) is the bounded component W1.
       f(Int B) is connected (continuous image of connected), contained in UNIV - f(Bd B),
       hence in one component. f(x) \<in> f(Int B) and f(B) is bounded \<Rightarrow> f(Int B) \<subseteq> W1.
       Conversely W1 \<subseteq> f(Int B) by Borsuk (any a \<in> W1 \<setminus> f(Int B) and b \<in> W2 would be separated
       by f(B), but f(B) doesn't separate S^2 since B is contractible).\<close>
    have hfx_W1: "f x \<in> W1"
    proof -
      \<comment> \<open>f(x) \<notin> f(frontier B) since f injective on U, x \<in> B - frontier B, frontier B \<subseteq> U.\<close>
      have hfr_sub_U: "frontier B \<subseteq> U" using frontier_closed_sub[OF hBclosed] hBsub by (by100 blast)
      have "f x \<notin> f ` frontier B"
      proof
        assume "f x \<in> f ` frontier B"
        then obtain z where hz: "z \<in> frontier B" and hfz: "f x = f z" by (by100 blast)
        have "x \<in> U" by (rule hx)
        have "z \<in> U" using hz hfr_sub_U by (by100 blast)
        have "x = z" using inj_onD[OF assms(3) hfz \<open>x \<in> U\<close> \<open>z \<in> U\<close>] .
        thus False using hx_int hz by (by100 blast)
      qed
      hence hfx_compl: "f x \<in> UNIV - f ` frontier B" by (by100 blast)
      hence "f x \<in> W1 \<or> f x \<in> W2" using hW(4) by (by100 blast)
      \<comment> \<open>f(x) is in bounded component: f(B) is bounded (compact image), so f(x) can't be in W2.\<close>
      moreover have "f x \<notin> W2"
      proof -
        \<comment> \<open>f(B - frontier B) is connected, bounded, and disjoint from f(frontier B).
           Hence entirely in one component. Since bounded, in W1 not W2.\<close>
        have hIntB_conn: "connected (B - frontier B)"
        proof (rule connectedI)
          fix T1 T2 :: "(real \<times> real) set"
          assume hT1: "open T1" and hT2: "open T2"
              and hcov: "B - frontier B \<subseteq> T1 \<union> T2"
              and hdisj: "T1 \<inter> T2 \<inter> (B - frontier B) = {}"
              and hne1: "T1 \<inter> (B - frontier B) \<noteq> {}"
              and hne2: "T2 \<inter> (B - frontier B) \<noteq> {}"
          \<comment> \<open>Take y1 \<in> T1 \<inter> intB and y2 \<in> T2 \<inter> intB.\<close>
          obtain y2 where hy2: "y2 \<in> T2 \<inter> (B - frontier B)" using hne2 by (by100 blast)
          \<comment> \<open>The center x is in intB and in T1 or T2.\<close>
          have hx_intB: "x \<in> B - frontier B" by (rule hx_int)
          \<comment> \<open>Path from x to y2: \<gamma>(t) = (1-t)*x + t*y2, stays in intB since t^2*g(y2) < r^2.\<close>
          let ?\<gamma> = "\<lambda>t :: real. ((1-t) * fst x + t * fst y2, (1-t) * snd x + t * snd y2)"
          have h\<gamma>_intB: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow> ?\<gamma> t \<in> B - frontier B"
          proof -
            fix t :: real assume ht: "0 \<le> t" "t \<le> 1"
            have hy2_ball: "(fst y2 - fst x)^2 + (snd y2 - snd x)^2 < r^2"
            proof -
              have "y2 \<in> B" using hy2 by (by100 blast)
              hence hle: "(fst y2 - fst x)^2 + (snd y2 - snd x)^2 \<le> r^2"
                unfolding B_def by (by100 blast)
              have "y2 \<notin> frontier B" using hy2 by (by100 blast)
              hence "(fst y2 - fst x)^2 + (snd y2 - snd x)^2 \<noteq> r^2"
                unfolding hfr_eq_top by (by100 blast)
              thus ?thesis using hle by (by100 linarith)
            qed
            have hfg: "fst (?\<gamma> t) = (1-t) * fst x + t * fst y2" by (by100 simp)
            have hsg: "snd (?\<gamma> t) = (1-t) * snd x + t * snd y2" by (by100 simp)
            have "fst (?\<gamma> t) - fst x = t * (fst y2 - fst x)" using hfg by (by100 algebra)
            moreover have "snd (?\<gamma> t) - snd x = t * (snd y2 - snd x)" using hsg by (by100 algebra)
            ultimately have "(fst (?\<gamma> t) - fst x)^2 + (snd (?\<gamma> t) - snd x)^2
                = t^2 * ((fst y2 - fst x)^2 + (snd y2 - snd x)^2)"
              by (by100 algebra)
            also have "... \<le> 1 * ((fst y2 - fst x)^2 + (snd y2 - snd x)^2)"
            proof (intro mult_right_mono)
              have "t \<le> 1" using ht by (by100 blast)
              thus "t^2 \<le> 1" using power_le_one ht by (by100 blast)
              show "(fst y2 - fst x)^2 + (snd y2 - snd x)^2 \<ge> 0" by (by100 simp)
            qed
            also have "... < r^2" using hy2_ball by (by100 simp)
            finally have "(fst (?\<gamma> t) - fst x)^2 + (snd (?\<gamma> t) - snd x)^2 < r^2" .
            have "?\<gamma> t \<in> B" unfolding B_def
              using \<open>(fst (?\<gamma> t) - fst x)^2 + (snd (?\<gamma> t) - snd x)^2 < r^2\<close> by (by100 auto)
            moreover have "?\<gamma> t \<notin> frontier B" unfolding hfr_eq_top
              using \<open>(fst (?\<gamma> t) - fst x)^2 + (snd (?\<gamma> t) - snd x)^2 < r^2\<close> by (by100 auto)
            ultimately show "?\<gamma> t \<in> B - frontier B" by (by100 blast)
          qed
          \<comment> \<open>\<gamma> is continuous [0,1] \<rightarrow> R^2.\<close>
          have h\<gamma>_cont: "continuous_on {0..1} ?\<gamma>"
            by (intro continuous_intros)
          \<comment> \<open>[0,1] connected, \<gamma>([0,1]) \<subseteq> intB \<subseteq> T1 \<union> T2, disjoint.
             \<gamma>(0) = x, \<gamma>(1) = y2 \<in> T2.  By connected image, entire \<gamma>([0,1]) in one part.
             y2 \<in> T2 forces \<gamma>([0,1]) \<subseteq> T2. But x = \<gamma>(0) \<in> \<gamma>([0,1]) \<subseteq> T2.
             Now x \<in> T2 \<inter> intB. But x \<in> T1 \<union> T2 and T1 \<inter> T2 \<inter> intB = {}.
             If x \<in> T1, then x \<in> T1 \<inter> T2 \<inter> intB, contradiction. So x \<in> T2 - T1.
             But then take y1 \<in> T1 \<inter> intB, path x \<rightarrow> y1, same argument gives x \<in> T1.
             Contradiction: x \<in> T1 \<inter> T2 \<inter> intB.\<close>
          have h\<gamma>_sub: "?\<gamma> ` {0..1} \<subseteq> B - frontier B"
          proof (intro image_subsetI)
            fix t :: real assume "t \<in> {0..1}"
            thus "?\<gamma> t \<in> B - frontier B" using h\<gamma>_intB by (by100 auto)
          qed
          have h\<gamma>_conn: "connected (?\<gamma> ` {0..1})"
            using connected_continuous_image[OF h\<gamma>_cont connected_Icc] by (by100 blast)
          have h\<gamma>_sub_T12: "?\<gamma> ` {0..1} \<subseteq> T1 \<union> T2" using h\<gamma>_sub hcov by (by100 blast)
          have h\<gamma>_disj: "T1 \<inter> T2 \<inter> ?\<gamma> ` {0..1} = {}" using h\<gamma>_sub hdisj by (by100 blast)
          have hT12_disj: "T1 \<inter> ?\<gamma> ` {0..1} = {} \<or> T2 \<inter> ?\<gamma> ` {0..1} = {}"
            by (rule connectedD[OF h\<gamma>_conn hT1 hT2 h\<gamma>_disj h\<gamma>_sub_T12])
          \<comment> \<open>\<gamma>(1) = y2 \<in> T2, so T2 \<inter> \<gamma>([0,1]) \<noteq> {}. Hence T1 \<inter> \<gamma>([0,1]) = {}.\<close>
          have hy2_img: "y2 \<in> ?\<gamma> ` {0..1}"
            using image_eqI[of y2 ?\<gamma> 1 "{0..1}"] by (by100 simp)
          have "y2 \<in> T2" using hy2 by (by100 blast)
          define \<gamma>_img where "\<gamma>_img = ?\<gamma> ` {0..1}"
          have "y2 \<in> \<gamma>_img" using \<open>y2 \<in> ?\<gamma> ` {0..1}\<close> unfolding \<gamma>_img_def .
          hence "T2 \<inter> \<gamma>_img \<noteq> {}" using \<open>y2 \<in> T2\<close> by (by100 blast)
          hence "T2 \<inter> ?\<gamma> ` {0..1} \<noteq> {}" unfolding \<gamma>_img_def .
          hence hT1_empty: "T1 \<inter> ?\<gamma> ` {0..1} = {}" using hT12_disj by (by100 blast)
          \<comment> \<open>\<gamma>(0) = x \<in> \<gamma>([0,1]), so x \<notin> T1. But x \<in> T1 \<union> T2, so x \<in> T2.\<close>
          have "x \<in> ?\<gamma> ` {0..1}"
            using image_eqI[of x ?\<gamma> 0 "{0..1}"] by (by100 simp)
          hence "x \<notin> T1" using hT1_empty by (by100 blast)
          hence "x \<in> T2" using hx_intB hcov by (by100 blast)
          \<comment> \<open>Now do same with y1 \<in> T1: path x \<rightarrow> y1 all in intB, connected, y1 \<in> T1, x \<in> T2.
             Since T2 \<inter> path \<noteq> {} (x), connectedD gives T1 \<inter> path = {}. But y1 \<in> T1 \<inter> path.
             Contradiction.\<close>
          obtain y1 where hy1: "y1 \<in> T1 \<inter> (B - frontier B)" using hne1 by (by100 blast)
          let ?\<delta> = "\<lambda>t :: real. ((1-t) * fst x + t * fst y1, (1-t) * snd x + t * snd y1)"
          have "?\<delta> ` {0..1} \<subseteq> B - frontier B"
          proof (intro image_subsetI)
            fix t :: real assume "t \<in> {0..1}"
            hence ht: "0 \<le> t" "t \<le> 1" by (by100 auto)+
            have hy1_ball: "(fst y1 - fst x)^2 + (snd y1 - snd x)^2 < r^2"
            proof -
              have "y1 \<in> B" using hy1 by (by100 blast)
              hence "(fst y1 - fst x)^2 + (snd y1 - snd x)^2 \<le> r^2" unfolding B_def by (by100 blast)
              moreover have "y1 \<notin> frontier B" using hy1 by (by100 blast)
              hence "(fst y1 - fst x)^2 + (snd y1 - snd x)^2 \<noteq> r^2" unfolding hfr_eq_top by (by100 blast)
              ultimately show ?thesis by (by100 linarith)
            qed
            have "fst (?\<delta> t) = (1-t) * fst x + t * fst y1" by (by100 simp)
            hence hf\<delta>: "fst (?\<delta> t) - fst x = t * (fst y1 - fst x)" by (by100 algebra)
            have "snd (?\<delta> t) = (1-t) * snd x + t * snd y1" by (by100 simp)
            hence hs\<delta>: "snd (?\<delta> t) - snd x = t * (snd y1 - snd x)" by (by100 algebra)
            have "(fst (?\<delta> t) - fst x)^2 + (snd (?\<delta> t) - snd x)^2
                = t^2 * ((fst y1 - fst x)^2 + (snd y1 - snd x)^2)"
              using hf\<delta> hs\<delta> by (by100 algebra)
            also have "... \<le> 1 * ((fst y1 - fst x)^2 + (snd y1 - snd x)^2)"
            proof (intro mult_right_mono)
              have "t \<le> 1" using ht by (by100 blast)
              thus "t^2 \<le> 1" using power_le_one ht by (by100 blast)
              show "(fst y1 - fst x)^2 + (snd y1 - snd x)^2 \<ge> 0" by (by100 simp)
            qed
            also have "... < r^2" using hy1_ball by (by100 simp)
            finally have hlt: "(fst (?\<delta> t) - fst x)^2 + (snd (?\<delta> t) - snd x)^2 < r^2" .
            have "?\<delta> t \<in> B" unfolding B_def using hlt by (by100 auto)
            moreover have "?\<delta> t \<notin> frontier B" unfolding hfr_eq_top using hlt by (by100 auto)
            ultimately show "?\<delta> t \<in> B - frontier B" by (by100 blast)
          qed
          hence h\<delta>_sub_T12: "?\<delta> ` {0..1} \<subseteq> T1 \<union> T2" using hcov by (by100 blast)
          have h\<delta>_cont: "continuous_on {0..1} ?\<delta>" by (intro continuous_intros)
          have h\<delta>_conn: "connected (?\<delta> ` {0..1})"
            using connected_continuous_image[OF h\<delta>_cont connected_Icc] by (by100 blast)
          have h\<delta>_disj: "T1 \<inter> T2 \<inter> ?\<delta> ` {0..1} = {}"
            using \<open>?\<delta> ` {0..1} \<subseteq> B - frontier B\<close> hdisj by (by100 blast)
          have "T1 \<inter> ?\<delta> ` {0..1} = {} \<or> T2 \<inter> ?\<delta> ` {0..1} = {}"
            by (rule connectedD[OF h\<delta>_conn hT1 hT2 h\<delta>_disj h\<delta>_sub_T12])
          moreover have "?\<delta> 0 = x" by (by100 simp)
          have hx_\<delta>: "x \<in> ?\<delta> ` {0..1}"
            using image_eqI[of x ?\<delta> 0 "{0..1}"] by (by100 simp)
          have "x \<in> T2 \<inter> ?\<delta> ` {0..1}" using \<open>x \<in> T2\<close> hx_\<delta> by (rule IntI)
          hence "T2 \<inter> ?\<delta> ` {0..1} \<noteq> {}" by (by100 blast)
          ultimately have "T1 \<inter> ?\<delta> ` {0..1} = {}" by (by100 blast)
          have hy1_\<delta>: "y1 \<in> ?\<delta> ` {0..1}"
            using image_eqI[of y1 ?\<delta> 1 "{0..1}"] by (by100 simp)
          have "y1 \<notin> T1" using \<open>T1 \<inter> ?\<delta> ` {0..1} = {}\<close> hy1_\<delta> by (by100 blast)
          thus False using hy1 by (by100 blast)
        qed
        have hf_intB_conn: "connected (f ` (B - frontier B))"
        proof -
          have "continuous_on (B - frontier B) f"
          proof -
            have "continuous_on U f"
              by (rule top1_continuous_map_on_to_continuous_on_R2[OF assms(2)])
            moreover have "B - frontier B \<subseteq> U" using hBsub by (by100 blast)
            ultimately show ?thesis using continuous_on_subset by (by100 blast)
          qed
          thus ?thesis using connected_continuous_image[OF _ hIntB_conn] by (by100 blast)
        qed
        have hf_intB_sub: "f ` (B - frontier B) \<subseteq> UNIV - f ` frontier B"
        proof
          fix y assume "y \<in> f ` (B - frontier B)"
          then obtain z where hz: "z \<in> B - frontier B" and hfz: "y = f z" by (by100 blast)
          have "z \<in> U" using hz hBsub by (by100 blast)
          show "y \<in> UNIV - f ` frontier B"
          proof (rule DiffI)
            show "y \<in> UNIV" by (by100 simp)
            show "y \<notin> f ` frontier B"
            proof
              assume "y \<in> f ` frontier B"
              then obtain w where hw: "w \<in> frontier B" and hfw: "y = f w" by (by100 blast)
              have "w \<in> U" using hw hfr_sub_U by (by100 blast)
              have "f z = f w" using hfz hfw by (by100 simp)
              hence "z = w" using assms(3) \<open>z \<in> U\<close> \<open>w \<in> U\<close> unfolding inj_on_def by (by100 blast)
              thus False using hz hw by (by100 blast)
            qed
          qed
        qed
        hence hf_intB_sub': "f ` (B - frontier B) \<subseteq> W1 \<union> W2" using hW(4) by (by100 blast)
        \<comment> \<open>f(B - frontier B) connected \<subseteq> W1 \<union> W2, W1 \<inter> W2 = {}. So in one component.\<close>
        have "f ` (B - frontier B) \<subseteq> W1 \<or> f ` (B - frontier B) \<subseteq> W2"
        proof -
          have hW2_open: "W2 \<in> ?TR2"
          proof -
            have hTR2: "is_topology_on (UNIV :: (real\<times>real) set) ?TR2"
              using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                    top1_open_sets_is_topology_on_UNIV] by (by100 simp)
            have hW1_closed': "closedin_on UNIV ?TR2 (closure_on UNIV ?TR2 W1)"
              by (rule closure_on_closed[OF hTR2]) (by100 simp)
            hence "UNIV - closure_on UNIV ?TR2 W1 \<in> ?TR2"
              unfolding closedin_on_def by (by100 blast)
            moreover have "UNIV - closure_on UNIV ?TR2 W1 = W2"
            proof -
              have "W1 \<inter> f ` frontier B = {}" using hW(3) hW(4) by (by100 blast)
              hence "UNIV - (W1 \<union> f ` frontier B) = W2"
                using hW(3) hW(4) by (by100 blast)
              thus ?thesis unfolding hW1_cl .
            qed
            ultimately show ?thesis by (by100 simp)
          qed
          have "open W1"
          proof -
            have "W2 \<in> ?TR2" by (rule hW2_open)
            have "W1 \<in> ?TR2"
            proof -
              have hTR2: "is_topology_on (UNIV :: (real\<times>real) set) ?TR2"
                using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                      top1_open_sets_is_topology_on_UNIV] by (by100 simp)
              have "closedin_on UNIV ?TR2 (closure_on UNIV ?TR2 W2)"
                by (rule closure_on_closed[OF hTR2]) (by100 simp)
              hence "UNIV - closure_on UNIV ?TR2 W2 \<in> ?TR2"
                unfolding closedin_on_def by (by100 blast)
              moreover have "W2 \<inter> f ` frontier B = {}" using hW(3) hW(4) by (by100 blast)
              hence "UNIV - (W2 \<union> f ` frontier B) = W1"
                using hW(3) hW(4) by (by100 blast)
              hence "UNIV - closure_on UNIV ?TR2 W2 = W1" unfolding hW2_cl .
              ultimately show ?thesis by (by100 simp)
            qed
            thus ?thesis using product_topology_on_open_sets_real2
              unfolding top1_open_sets_def by (by100 simp)
          qed
          moreover have "open W2" using hW2_open product_topology_on_open_sets_real2
            unfolding top1_open_sets_def by (by100 simp)
          moreover have "W1 \<inter> W2 \<inter> f ` (B - frontier B) = {}" using hW(3) by (by100 blast)
          ultimately have "W1 \<inter> f ` (B - frontier B) = {} \<or> W2 \<inter> f ` (B - frontier B) = {}"
            by (rule connectedD[OF hf_intB_conn _ _ _ hf_intB_sub'])
          thus ?thesis using hf_intB_sub' by (by100 blast)
        qed
        show "f x \<notin> W2"
        proof (rule ccontr)
          assume "\<not> f x \<notin> W2" hence hfx_W2: "f x \<in> W2" by (by100 blast)
          \<comment> \<open>f(int B) connected, in one component. Since f(x) \<in> W2, f(int B) \<subseteq> W2.\<close>
          hence hfintB_W2: "f ` (B - frontier B) \<subseteq> W2"
          proof -
            have "f ` (B - frontier B) \<subseteq> W1 \<or> f ` (B - frontier B) \<subseteq> W2"
              using \<open>f ` (B - frontier B) \<subseteq> W1 \<or> f ` (B - frontier B) \<subseteq> W2\<close> .
            moreover have "f x \<in> f ` (B - frontier B)" using hx_int by (by100 blast)
            moreover have "f x \<notin> W1" using hfx_W2 hW(3) by (by100 blast)
            ultimately show ?thesis by (by100 blast)
          qed
          \<comment> \<open>W1 \<noteq> {}, so get a \<in> W1. Since f(int B) \<subseteq> W2 and a \<in> W1, a \<notin> f(int B).\<close>
          obtain a1 where ha1: "a1 \<in> W1" using hW(1) by (by100 blast)
          have ha1_notfB: "a1 \<notin> f ` B"
          proof -
            have "a1 \<notin> f ` (B - frontier B)" using ha1 hfintB_W2 hW(3) by (by100 blast)
            moreover have "a1 \<notin> f ` frontier B" using ha1 hW(4) by (by100 blast)
            ultimately show ?thesis by (by100 blast)
          qed
          \<comment> \<open>W2 unbounded, f(B) bounded: get b1 \<in> W2 - f(B).\<close>
          obtain b1 where hb1: "b1 \<in> W2" and hb1_notfB: "b1 \<notin> f ` B"
            using hW2_escape ha1_notfB by (by100 blast)
          \<comment> \<open>Apply Borsuk: f|_{\<partial>B} nulhomotopic in S^2-{a1,b1}, injective, compact.
             Conclusion: a1, b1 in same component of S^2 - f(\<partial>B).
             But a1 \<in> W1, b1 \<in> W2 (different components) \<longrightarrow> contradiction.\<close>
          \<comment> \<open>Embed into S^2. a1, b1 \<notin> f(B) \<Longrightarrow> a1, b1 \<notin> f(\<partial>B).\<close>
          \<comment> \<open>f|_{\<partial>B} nulhomotopic in S^2-{a1,b1}: extends to f|_B : B \<rightarrow> R^2-{a1,b1} \<subseteq> S^2-{a1,b1}.\<close>
          \<comment> \<open>B contractible, f|_B avoids a1 and b1 (both \<notin> f(B)).\<close>
          \<comment> \<open>Borsuk: a1, b1 in same component of S^2-f(\<partial>B).\<close>
          \<comment> \<open>But one-point-compactification: components of R^2-f(\<partial>B) correspond to
             components of S^2-f(\<partial>B) (plus b at infinity joins the unbounded component).\<close>
          \<comment> \<open>a1 \<in> W1 and b1 \<in> W2 are in different R^2 components, hence different S^2 components
             (W1 bounded, W2 unbounded + {\<infinity>} makes a single S^2 component).\<close>
          \<comment> \<open>Contradiction with Borsuk conclusion.\<close>
          show "False"
          proof -
            \<comment> \<open>frontier B topology.\<close>
            have hTR2: "is_topology_on (UNIV :: (real\<times>real) set) ?TR2"
              using product_topology_on_is_topology_on[OF
                top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by (by100 simp)
            let ?TfB = "subspace_topology UNIV ?TR2 (frontier B)"
            have hTfB: "is_topology_on (frontier B) ?TfB"
              by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
            \<comment> \<open>frontier B compact.\<close>
            have hfB_compact': "top1_compact_on (frontier B) ?TfB"
            proof -
              have "compact (frontier B)" by (rule hfr_compact)
              hence "top1_compact_on (frontier B) (subspace_topology UNIV top1_open_sets (frontier B))"
                using top1_compact_on_subspace_UNIV_iff_compact by (by100 blast)
              thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
            qed
            \<comment> \<open>f continuous on frontier B.\<close>
            have hf_cont_fB_HOL: "continuous_on (frontier B) f"
              using continuous_on_subset[OF
                top1_continuous_map_on_to_continuous_on_R2[OF assms(2)] hfr_sub_U] .
            have hf_cont_fB: "top1_continuous_map_on (frontier B) ?TfB UNIV ?TR2 f"
            proof -
              have "top1_continuous_map_on (frontier B) ?TfB
                  UNIV (subspace_topology UNIV ?TR2 UNIV) f"
              proof (rule top1_continuous_map_on_real2_subspace_general)
                show "\<And>p. p \<in> frontier B \<Longrightarrow> f p \<in> (UNIV::(real\<times>real) set)" by (by100 simp)
                show "continuous_on (frontier B) f" by (rule hf_cont_fB_HOL)
              qed
              moreover have "subspace_topology UNIV ?TR2 UNIV = ?TR2"
                unfolding subspace_topology_def by (by100 auto)
              ultimately show ?thesis by (by100 simp)
            qed
            \<comment> \<open>f injective on frontier B.\<close>
            have hf_inj_fB: "inj_on f (frontier B)"
              using assms(3) hfr_sub_U by (rule inj_on_subset)
            \<comment> \<open>a1, b1 \<notin> f(frontier B) (both \<notin> f(B) \<supseteq> f(frontier B)).\<close>
            have hfr_sub_B: "frontier B \<subseteq> B" by (rule frontier_closed_sub[OF hBclosed])
            have ha1_not_ffB: "a1 \<notin> f ` frontier B"
            proof -
              have "f ` frontier B \<subseteq> f ` B" using hfr_sub_B by (by100 blast)
              thus ?thesis using ha1_notfB by (by100 blast)
            qed
            have hb1_not_ffB: "b1 \<notin> f ` frontier B"
            proof -
              have "f ` frontier B \<subseteq> f ` B" using hfr_sub_B by (by100 blast)
              thus ?thesis using hb1_notfB by (by100 blast)
            qed
            \<comment> \<open>f|_{\<partial>B} nulhomotopic in R^2 - {a1, b1}: extends to f|_B : B \<rightarrow> R^2 - {a1, b1}.\<close>
            have hf_nul: "top1_nulhomotopic_on (frontier B) ?TfB
                (UNIV - {a1, b1}) (subspace_topology UNIV ?TR2 (UNIV - {a1, b1})) f"
            proof (rule nulhomotopic_via_convex_R2)
              \<comment> \<open>B satisfies the convex combination property (closed ball).\<close>
              show "\<forall>y\<in>B. \<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow>
                  ((1-t) * fst y + t * fst x, (1-t) * snd y + t * snd x) \<in> B"
              proof (intro ballI allI impI)
                fix y :: "real \<times> real" and t :: real assume hy: "y \<in> B" and ht: "0 \<le> t \<and> t \<le> 1"
                have hle: "(fst y - fst x)^2 + (snd y - snd x)^2 \<le> r^2"
                  using hy unfolding B_def by (by100 auto)
                have "((1-t) * fst y + t * fst x - fst x)\<^sup>2 + ((1-t) * snd y + t * snd x - snd x)\<^sup>2
                    = (1-t)\<^sup>2 * ((fst y - fst x)\<^sup>2 + (snd y - snd x)\<^sup>2)"
                  by (by100 algebra)
                also have "\<dots> \<le> 1 * r^2"
                proof (rule mult_mono)
                  show "(1-t)\<^sup>2 \<le> 1"
                  proof -
                    have "0 \<le> 1 - t" and "1 - t \<le> 1" using ht by (by100 linarith)+
                    hence "(1-t) * (1-t) \<le> 1 * 1"
                      by (intro mult_mono) (by100 linarith)+
                    thus ?thesis unfolding power2_eq_square by (by100 linarith)
                  qed
                  show "(fst y - fst x)^2 + (snd y - snd x)^2 \<le> r^2" by (rule hle)
                  show "0 \<le> (fst y - fst x)\<^sup>2 + (snd y - snd x)\<^sup>2" by (by100 simp)
                  show "0 \<le> (1::real)" by (by100 simp)
                qed
                finally show "((1-t) * fst y + t * fst x, (1-t) * snd y + t * snd x) \<in> B"
                  unfolding B_def by (by100 auto)
              qed
              show "x \<in> B" using hx_int by (by100 blast)
              show "frontier B \<subseteq> B" by (rule hfr_sub_B_top)
              show "continuous_on B f"
                using continuous_on_subset[OF
                  top1_continuous_map_on_to_continuous_on_R2[OF assms(2)] hBsub] .
              show "\<forall>y\<in>B. f y \<in> UNIV - {a1, b1}"
                using ha1_notfB hb1_notfB by (by100 blast)
            qed
            \<comment> \<open>Apply Borsuk_R2: a1, b1 in same R^2 component.\<close>
            from Borsuk_R2[OF hTfB hfB_compact' hf_cont_fB hf_inj_fB
                ha1_not_ffB hb1_not_ffB hf_nul]
            obtain C where hC_conn: "top1_connected_on C (subspace_topology UNIV ?TR2 C)"
                and hC_sub: "C \<subseteq> UNIV - f ` frontier B" and ha1C: "a1 \<in> C" and hb1C: "b1 \<in> C"
              by (by100 blast)
            \<comment> \<open>C connected, a1 \<in> W1, b1 \<in> W2. But C \<subseteq> UNIV - f(\<partial>B) = W1 \<union> W2.\<close>
            have "C \<subseteq> W1 \<or> C \<subseteq> W2"
            proof -
              have hC_sub_W12: "C \<subseteq> W1 \<union> W2" using hC_sub hW(4) by (by100 blast)
              have hC_HOL_conn: "connected C"
              proof -
                have "top1_connected_on C (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets C)
                    = connected C"
                  by (rule top1_connected_on_subspace_open_iff_connected)
                moreover have "?TR2 = (top1_open_sets :: (real\<times>real) set set)"
                  using product_topology_on_open_sets_real2 by (by100 metis)
                ultimately show ?thesis using hC_conn by (by100 simp)
              qed
              have hW1_open: "open W1"
              proof -
                have hTR2': "is_topology_on (UNIV :: (real\<times>real) set) ?TR2"
                  using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                        top1_open_sets_is_topology_on_UNIV] by (by100 simp)
                have "closedin_on UNIV ?TR2 (closure_on UNIV ?TR2 W2)"
                  by (rule closure_on_closed[OF hTR2']) (by100 simp)
                hence "UNIV - closure_on UNIV ?TR2 W2 \<in> ?TR2"
                  unfolding closedin_on_def by (by100 blast)
                moreover have "UNIV - closure_on UNIV ?TR2 W2 = W1"
                proof -
                  have "W2 \<inter> f ` frontier B = {}" using hW(3) hW(4) by (by100 blast)
                  hence "UNIV - (W2 \<union> f ` frontier B) = W1"
                    using hW(3) hW(4) by (by100 blast)
                  thus ?thesis unfolding hW2_cl .
                qed
                ultimately have "W1 \<in> ?TR2" by (by100 simp)
                thus ?thesis using product_topology_on_open_sets_real2
                  unfolding top1_open_sets_def by (by100 simp)
              qed
              have hW2_open: "open W2"
              proof -
                have hTR2': "is_topology_on (UNIV :: (real\<times>real) set) ?TR2"
                  using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                        top1_open_sets_is_topology_on_UNIV] by (by100 simp)
                have "closedin_on UNIV ?TR2 (closure_on UNIV ?TR2 W1)"
                  by (rule closure_on_closed[OF hTR2']) (by100 simp)
                hence "UNIV - closure_on UNIV ?TR2 W1 \<in> ?TR2"
                  unfolding closedin_on_def by (by100 blast)
                moreover have "UNIV - closure_on UNIV ?TR2 W1 = W2"
                proof -
                  have "W1 \<inter> f ` frontier B = {}" using hW(3) hW(4) by (by100 blast)
                  hence "UNIV - (W1 \<union> f ` frontier B) = W2"
                    using hW(3) hW(4) by (by100 blast)
                  thus ?thesis unfolding hW1_cl .
                qed
                ultimately have "W2 \<in> ?TR2" by (by100 simp)
                thus ?thesis using product_topology_on_open_sets_real2
                  unfolding top1_open_sets_def by (by100 simp)
              qed
              have "W1 \<inter> W2 \<inter> C = {}" using hW(3) by (by100 blast)
              have "W1 \<inter> C = {} \<or> W2 \<inter> C = {}"
                by (rule connectedD[OF hC_HOL_conn hW1_open hW2_open \<open>W1 \<inter> W2 \<inter> C = {}\<close> hC_sub_W12])
              thus ?thesis using hC_sub_W12 by (by100 blast)
            qed
            thus False using ha1 hb1 ha1C hb1C hW(3) by (by100 blast)
          qed
        qed
      qed
      ultimately show "f x \<in> W1" by (by100 blast)
    qed
    \<comment> \<open>The component containing f(intB) is open and contained in f(U).\<close>
    have hW1_sub: "W1 \<subseteq> f ` (B - frontier B)"
    proof (rule ccontr)
      assume "\<not> W1 \<subseteq> f ` (B - frontier B)"
      then obtain a1 where ha1: "a1 \<in> W1" and ha1_not: "a1 \<notin> f ` (B - frontier B)"
        by (by100 blast)
      have ha1_notfB: "a1 \<notin> f ` B"
      proof -
        have "a1 \<notin> f ` frontier B" using ha1 hW(4) by (by100 blast)
        thus ?thesis using ha1_not by (by100 blast)
      qed
      \<comment> \<open>Get b1 \<in> W2 - f(B) (same as before: W2 unbounded, f(B) bounded).\<close>
      obtain b1 where hb1: "b1 \<in> W2" and hb1_notfB: "b1 \<notin> f ` B"
        using hW2_escape ha1_notfB by (by100 blast)
      \<comment> \<open>Apply Borsuk: a1, b1 \<notin> f(B), f|_{\<partial>B} nulhomotopic in S^2-{a1,b1}.
         Borsuk gives a1, b1 in same component of S^2-f(\<partial>B). But W1 \<inter> W2 = {}.\<close>
      show False
      proof -
        have hfr_sub_U': "frontier B \<subseteq> U" using frontier_closed_sub[OF hBclosed] hBsub by (by100 blast)
        let ?TfB = "subspace_topology UNIV ?TR2 (frontier B)"
        have hTfB: "is_topology_on (frontier B) ?TfB"
        proof -
          have hTR2': "is_topology_on (UNIV :: (real\<times>real) set) ?TR2"
            using product_topology_on_is_topology_on[OF
              top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by (by100 simp)
          thus ?thesis by (rule subspace_topology_is_topology_on) (by100 simp)
        qed
        have hfB_compact': "top1_compact_on (frontier B) ?TfB"
        proof -
          have "compact (frontier B)" by (rule hfr_compact)
          hence "top1_compact_on (frontier B) (subspace_topology UNIV top1_open_sets (frontier B))"
            using top1_compact_on_subspace_UNIV_iff_compact by (by100 blast)
          thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
        qed
        have hf_cont_fB: "top1_continuous_map_on (frontier B) ?TfB UNIV ?TR2 f"
        proof -
          have hcont_fB: "continuous_on (frontier B) f"
            using continuous_on_subset[OF top1_continuous_map_on_to_continuous_on_R2[OF assms(2)] hfr_sub_U'] .
          have "top1_continuous_map_on (frontier B) ?TfB
              UNIV (subspace_topology UNIV ?TR2 UNIV) f"
          proof (rule top1_continuous_map_on_real2_subspace_general)
            show "\<And>p. p \<in> frontier B \<Longrightarrow> f p \<in> (UNIV::(real\<times>real) set)" by (by100 simp)
            show "continuous_on (frontier B) f" by (rule hcont_fB)
          qed
          moreover have "subspace_topology UNIV ?TR2 UNIV = ?TR2"
            unfolding subspace_topology_def by (by100 auto)
          ultimately show ?thesis by (by100 simp)
        qed
        have hf_inj_fB: "inj_on f (frontier B)"
          using assms(3) hfr_sub_U' by (rule inj_on_subset)
        have hfr_sub_B: "frontier B \<subseteq> B" by (rule frontier_closed_sub[OF hBclosed])
        have ha1_not_ffB: "a1 \<notin> f ` frontier B"
        proof -
          have "f ` frontier B \<subseteq> f ` B" using hfr_sub_B by (by100 blast)
          thus ?thesis using ha1_notfB by (by100 blast)
        qed
        have hb1_not_ffB: "b1 \<notin> f ` frontier B"
        proof -
          have "f ` frontier B \<subseteq> f ` B" using hfr_sub_B by (by100 blast)
          thus ?thesis using hb1_notfB by (by100 blast)
        qed
        have hf_nul: "top1_nulhomotopic_on (frontier B) ?TfB
            (UNIV - {a1, b1}) (subspace_topology UNIV ?TR2 (UNIV - {a1, b1})) f"
        proof (rule nulhomotopic_via_convex_R2)
          show "\<forall>y\<in>B. \<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow>
              ((1-t) * fst y + t * fst x, (1-t) * snd y + t * snd x) \<in> B"
          proof (intro ballI allI impI)
            fix y :: "real \<times> real" and t :: real assume hy: "y \<in> B" and ht: "0 \<le> t \<and> t \<le> 1"
            have hle: "(fst y - fst x)\<^sup>2 + (snd y - snd x)\<^sup>2 \<le> r\<^sup>2"
              using hy unfolding B_def by (by100 auto)
            have "((1-t) * fst y + t * fst x - fst x)\<^sup>2 + ((1-t) * snd y + t * snd x - snd x)\<^sup>2
                = (1-t)\<^sup>2 * ((fst y - fst x)\<^sup>2 + (snd y - snd x)\<^sup>2)"
              by (by100 algebra)
            also have "\<dots> \<le> 1 * r\<^sup>2"
            proof (rule mult_mono)
              show "(1-t)\<^sup>2 \<le> 1"
              proof -
                have "0 \<le> 1 - t" and "1 - t \<le> 1" using ht by (by100 linarith)+
                hence "(1-t) * (1-t) \<le> 1 * 1" by (intro mult_mono) (by100 linarith)+
                thus ?thesis unfolding power2_eq_square by (by100 linarith)
              qed
              show "(fst y - fst x)\<^sup>2 + (snd y - snd x)\<^sup>2 \<le> r\<^sup>2" by (rule hle)
              show "0 \<le> (fst y - fst x)\<^sup>2 + (snd y - snd x)\<^sup>2" by (by100 simp)
              show "0 \<le> (1::real)" by (by100 simp)
            qed
            finally show "((1-t) * fst y + t * fst x, (1-t) * snd y + t * snd x) \<in> B"
              unfolding B_def by (by100 auto)
          qed
          show "x \<in> B" using hx_int by (by100 blast)
          show "frontier B \<subseteq> B" by (rule hfr_sub_B_top)
          show "continuous_on B f"
            using continuous_on_subset[OF
              top1_continuous_map_on_to_continuous_on_R2[OF assms(2)] hBsub] .
          show "\<forall>y\<in>B. f y \<in> UNIV - {a1, b1}"
            using ha1_notfB hb1_notfB by (by100 blast)
        qed
        from Borsuk_R2[OF hTfB hfB_compact' hf_cont_fB hf_inj_fB ha1_not_ffB hb1_not_ffB hf_nul]
        obtain C where hC_conn: "top1_connected_on C (subspace_topology UNIV ?TR2 C)"
            and hC_sub: "C \<subseteq> UNIV - f ` frontier B" and ha1C: "a1 \<in> C" and hb1C: "b1 \<in> C"
          by (by100 blast)
        have hC_sub_W12: "C \<subseteq> W1 \<union> W2" using hC_sub hW(4) by (by100 blast)
        have hC_HOL_conn: "connected C"
        proof -
          have "top1_connected_on C (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets C)
              = connected C"
            by (rule top1_connected_on_subspace_open_iff_connected)
          moreover have "?TR2 = (top1_open_sets :: (real\<times>real) set set)"
            using product_topology_on_open_sets_real2 by (by100 metis)
          ultimately show ?thesis using hC_conn by (by100 simp)
        qed
        have hW1_open': "open W1" by (rule hW1_is_open)
        have hW2_open': "open W2" by (rule hW2_is_open)
        have "W1 \<inter> W2 \<inter> C = {}" using hW(3) by (by100 blast)
        have "W1 \<inter> C = {} \<or> W2 \<inter> C = {}"
          by (rule connectedD[OF hC_HOL_conn hW1_open' hW2_open' \<open>W1 \<inter> W2 \<inter> C = {}\<close> hC_sub_W12])
        have "C \<subseteq> W1 \<or> C \<subseteq> W2" using \<open>W1 \<inter> C = {} \<or> W2 \<inter> C = {}\<close> hC_sub_W12 by (by100 blast)
        thus False using ha1 hb1 ha1C hb1C hW(3) by (by100 blast)
      qed
    qed
    have hW1_open: "W1 \<in> ?TR2"
    proof -
      \<comment> \<open>closure W2 = W2 \<union> C. Complement of closure is open. UNIV-(W2 \<union> C) = W1.\<close>
      have hTR2: "is_topology_on (UNIV :: (real\<times>real) set) ?TR2"
        using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
              top1_open_sets_is_topology_on_UNIV] by (by100 simp)
      have hW2_closed: "closedin_on UNIV ?TR2 (closure_on UNIV ?TR2 W2)"
        by (rule closure_on_closed[OF hTR2]) (by100 simp)
      hence "UNIV - closure_on UNIV ?TR2 W2 \<in> ?TR2"
        unfolding closedin_on_def by (by100 blast)
      moreover have "UNIV - closure_on UNIV ?TR2 W2 = W1"
      proof -
        have "UNIV - (W2 \<union> f ` frontier B) = W1"
          using hW(3) hW(4) by (by100 blast)
        thus ?thesis unfolding hW2_cl .
      qed
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>W1 is open, f(x) \<in> W1, W1 \<subseteq> f(Int B) \<subseteq> f(U).\<close>
    have "W1 \<subseteq> f ` U" using hW1_sub hBsub by (by100 blast)
    thus "\<exists>W. y \<in> W \<and> W \<in> ?TR2 \<and> W \<subseteq> f ` U"
      using hfx_W1 hW1_open hy by (by100 blast)
  qed
  \<comment> \<open>f(U) is open: every point has an open neighborhood in f(U).\<close>
  \<comment> \<open>f(U) = \<Union>{W | W open, W \<subseteq> f(U)} which is a union of open sets, hence open.\<close>
  have "f ` U = \<Union>{W \<in> ?TR2. W \<subseteq> f ` U}"
  proof (intro set_eqI iffI)
    fix y assume hy: "y \<in> f ` U"
    then obtain W where hW: "W \<in> ?TR2" "y \<in> W" "W \<subseteq> f ` U"
      using \<open>\<forall>y\<in>f ` U. \<exists>W. y \<in> W \<and> W \<in> ?TR2 \<and> W \<subseteq> f ` U\<close> by (by100 blast)
    thus "y \<in> \<Union>{W \<in> ?TR2. W \<subseteq> f ` U}" by (by100 blast)
  next
    fix y assume "y \<in> \<Union>{W \<in> ?TR2. W \<subseteq> f ` U}"
    then obtain W where "W \<in> ?TR2" "W \<subseteq> f ` U" "y \<in> W" by (by100 blast)
    thus "y \<in> f ` U" by (by100 blast)
  qed
  moreover have "{W \<in> ?TR2. W \<subseteq> f ` U} \<subseteq> ?TR2" by (by100 blast)
  moreover have "is_topology_on (UNIV :: (real\<times>real) set) ?TR2"
  proof -
    have "?TR2 = (top1_open_sets :: (real\<times>real) set set)"
      by (rule product_topology_on_open_sets_real2)
    thus ?thesis using top1_open_sets_is_topology_on_UNIV by (by100 simp)
  qed
  hence hUnion: "\<Union>{W \<in> ?TR2. W \<subseteq> f ` U} \<in> ?TR2"
  proof -
    have hsub: "{W \<in> ?TR2. W \<subseteq> f ` U} \<subseteq> ?TR2" by (by100 blast)
    have "(\<forall>U. U \<subseteq> ?TR2 \<longrightarrow> \<Union>U \<in> ?TR2)"
      using \<open>is_topology_on (UNIV :: (real\<times>real) set) ?TR2\<close> unfolding is_topology_on_def by (by100 blast)
    thus ?thesis using hsub by (by100 blast)
  qed
  ultimately show ?thesis by (by100 simp)
qed

text \<open>The induced map h_* on fundamental groups is a group homomorphism.
  Key: h \<circ> (f * g) = (h \<circ> f) * (h \<circ> g) by definition of path product.\<close>

lemma comp_path_product:
  "h \<circ> top1_path_product f g = top1_path_product (h \<circ> f) (h \<circ> g)"
proof (rule ext)
  fix t :: real
  show "(h \<circ> top1_path_product f g) t = top1_path_product (h \<circ> f) (h \<circ> g) t"
    unfolding top1_path_product_def comp_def by (by100 simp)
qed

lemma top1_fundamental_group_induced_on_is_hom:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hx0: "x0 \<in> X" and hy0: "y0 \<in> Y"
      and hcont: "top1_continuous_map_on X TX Y TY h"
      and hh0: "h x0 = y0"
  shows "top1_group_hom_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_carrier Y TY y0)
      (top1_fundamental_group_mul Y TY y0)
      (top1_fundamental_group_induced_on X TX x0 Y TY y0 h)"
  unfolding top1_group_hom_on_def
proof (intro conjI ballI)
  let ?ind = "top1_fundamental_group_induced_on X TX x0 Y TY y0 h"
  \<comment> \<open>Part 1: induced maps carrier to carrier.\<close>
  fix c assume hc: "c \<in> top1_fundamental_group_carrier X TX x0"
  show "?ind c \<in> top1_fundamental_group_carrier Y TY y0"
  proof -
    \<comment> \<open>c is a loop class: c = {g. loop_equiv X TX x0 f0 g} for some loop f0.\<close>
    from hc obtain f0 where hf0: "top1_is_loop_on X TX x0 f0"
        and hc_eq: "c = {g. top1_loop_equiv_on X TX x0 f0 g}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>h\<circ>f0 is a loop at y0.\<close>
    have hf0_Y: "top1_is_loop_on Y TY y0 (h \<circ> f0)"
      using top1_continuous_map_loop[OF hcont hf0] hh0 by (by100 simp)
    \<comment> \<open>ind(c) = {g. loop_equiv Y TY y0 (h\<circ>f0) g}.\<close>
    have "?ind c = {g. top1_loop_equiv_on Y TY y0 (h \<circ> f0) g}"
    proof (rule set_eqI)
      fix g
      show "g \<in> ?ind c \<longleftrightarrow> g \<in> {g. top1_loop_equiv_on Y TY y0 (h \<circ> f0) g}"
      proof
        assume "g \<in> ?ind c"
        hence "g \<in> {g'. \<exists>f\<in>c. top1_loop_equiv_on Y TY (h x0) (h \<circ> f) g'}"
          unfolding top1_fundamental_group_induced_on_def hh0[symmetric] by (by100 simp)
        then obtain f where hf_c: "f \<in> c" and hg_eq: "top1_loop_equiv_on Y TY (h x0) (h \<circ> f) g"
          by (by100 blast)
        have hf_equiv: "top1_loop_equiv_on X TX x0 f0 f"
          using hf_c hc_eq by (by100 blast)
        have hf0_loop: "top1_is_loop_on X TX x0 f0" by (rule hf0)
        have hf_loop: "top1_is_loop_on X TX x0 f"
          using hf_equiv unfolding top1_loop_equiv_on_def by (by100 blast)
        have "top1_loop_equiv_on Y TY (h x0) (h \<circ> f0) (h \<circ> f)"
          by (rule top1_induced_preserves_loop_equiv[OF hTX hcont hf0_loop hf_loop hf_equiv])
        hence "top1_loop_equiv_on Y TY y0 (h \<circ> f0) (h \<circ> f)"
          using hh0 by (by100 simp)
        moreover have "top1_loop_equiv_on Y TY y0 (h \<circ> f) g"
          using hg_eq hh0 by (by100 simp)
        ultimately have "top1_loop_equiv_on Y TY y0 (h \<circ> f0) g"
          by (rule top1_loop_equiv_on_trans[OF hTY])
        thus "g \<in> {g. top1_loop_equiv_on Y TY y0 (h \<circ> f0) g}" by (by100 blast)
      next
        assume "g \<in> {g. top1_loop_equiv_on Y TY y0 (h \<circ> f0) g}"
        hence hg: "top1_loop_equiv_on Y TY y0 (h \<circ> f0) g" by (by100 blast)
        have "f0 \<in> c" using hc_eq top1_loop_equiv_on_refl[OF hf0] by (by100 blast)
        moreover have "top1_loop_equiv_on Y TY (h x0) (h \<circ> f0) g"
          using hg hh0 by (by100 simp)
        hence "top1_loop_equiv_on Y TY y0 (h \<circ> f0) g"
          using hh0 by (by100 simp)
        with \<open>f0 \<in> c\<close> show "g \<in> ?ind c"
          unfolding top1_fundamental_group_induced_on_def hh0[symmetric] by (by100 blast)
      qed
    qed
    thus ?thesis unfolding top1_fundamental_group_carrier_def
      using hf0_Y by (by100 blast)
  qed
next
  \<comment> \<open>Part 2: induced preserves multiplication.\<close>
  fix c1 c2
  let ?ind = "top1_fundamental_group_induced_on X TX x0 Y TY y0 h"
  assume hc1: "c1 \<in> top1_fundamental_group_carrier X TX x0"
     and hc2: "c2 \<in> top1_fundamental_group_carrier X TX x0"
  show "?ind (top1_fundamental_group_mul X TX x0 c1 c2)
      = top1_fundamental_group_mul Y TY y0 (?ind c1) (?ind c2)"
  proof (rule set_eqI)
    fix k
    show "k \<in> ?ind (top1_fundamental_group_mul X TX x0 c1 c2) \<longleftrightarrow>
          k \<in> top1_fundamental_group_mul Y TY y0 (?ind c1) (?ind c2)"
    proof
      \<comment> \<open>Forward: k \<in> ind(mul c1 c2) \<Longrightarrow> k \<in> mul_Y(ind c1, ind c2).\<close>
      assume "k \<in> ?ind (top1_fundamental_group_mul X TX x0 c1 c2)"
      then obtain p where hp_mul: "p \<in> top1_fundamental_group_mul X TX x0 c1 c2"
          and hk_eq: "top1_loop_equiv_on Y TY y0 (h \<circ> p) k"
        unfolding top1_fundamental_group_induced_on_def hh0[symmetric] by (by100 blast)
      from hp_mul obtain f1 g1 where hf1: "f1 \<in> c1" and hg1: "g1 \<in> c2"
          and hfg_eq: "top1_loop_equiv_on X TX x0 (top1_path_product f1 g1) p"
        unfolding top1_fundamental_group_mul_def by (by100 blast)
      \<comment> \<open>h\<circ>(f1*g1) = (h\<circ>f1)*(h\<circ>g1) by comp_path_product.\<close>
      \<comment> \<open>h\<circ>(f1*g1) ~_Y h\<circ>p (by preservation of loop_equiv).\<close>
      \<comment> \<open>h\<circ>p ~_Y k (given). So (h\<circ>f1)*(h\<circ>g1) ~_Y k.\<close>
      \<comment> \<open>h\<circ>f1 \<in> ind(c1) (reflexivity). h\<circ>g1 \<in> ind(c2). So k \<in> mul_Y(ind c1, ind c2).\<close>
      have hf1_loop: "top1_is_loop_on X TX x0 f1"
        using hc1 hf1 unfolding top1_fundamental_group_carrier_def top1_loop_equiv_on_def
        by (by100 blast)
      have hg1_loop: "top1_is_loop_on X TX x0 g1"
        using hc2 hg1 unfolding top1_fundamental_group_carrier_def top1_loop_equiv_on_def
        by (by100 blast)
      have hf1_Y: "top1_is_loop_on Y TY y0 (h \<circ> f1)"
        using top1_continuous_map_loop[OF hcont hf1_loop] hh0 by (by100 simp)
      have hg1_Y: "top1_is_loop_on Y TY y0 (h \<circ> g1)"
        using top1_continuous_map_loop[OF hcont hg1_loop] hh0 by (by100 simp)
      have "h \<circ> f1 \<in> ?ind c1"
      proof -
        have "top1_loop_equiv_on Y TY y0 (h \<circ> f1) (h \<circ> f1)"
          by (rule top1_loop_equiv_on_refl[OF hf1_Y])
        thus ?thesis unfolding top1_fundamental_group_induced_on_def hh0[symmetric]
          using hf1 by (by100 blast)
      qed
      moreover have "h \<circ> g1 \<in> ?ind c2"
      proof -
        have "top1_loop_equiv_on Y TY y0 (h \<circ> g1) (h \<circ> g1)"
          by (rule top1_loop_equiv_on_refl[OF hg1_Y])
        thus ?thesis unfolding top1_fundamental_group_induced_on_def hh0[symmetric]
          using hg1 by (by100 blast)
      qed
      moreover have "top1_loop_equiv_on Y TY y0 (top1_path_product (h \<circ> f1) (h \<circ> g1)) k"
      proof -
        have "top1_path_product (h \<circ> f1) (h \<circ> g1) = h \<circ> top1_path_product f1 g1"
          using comp_path_product[symmetric] .
        moreover have "top1_loop_equiv_on Y TY y0 (h \<circ> top1_path_product f1 g1) k"
        proof -
          have hfg1_loop: "top1_is_loop_on X TX x0 (top1_path_product f1 g1)"
            using hfg_eq unfolding top1_loop_equiv_on_def by (by100 blast)
          have hp_loop: "top1_is_loop_on X TX x0 p"
            using hfg_eq unfolding top1_loop_equiv_on_def by (by100 blast)
          have "top1_loop_equiv_on Y TY (h x0) (h \<circ> top1_path_product f1 g1) (h \<circ> p)"
            by (rule top1_induced_preserves_loop_equiv[OF hTX hcont hfg1_loop hp_loop hfg_eq])
          hence "top1_loop_equiv_on Y TY y0 (h \<circ> top1_path_product f1 g1) (h \<circ> p)"
            using hh0 by (by100 simp)
          thus ?thesis by (rule top1_loop_equiv_on_trans[OF hTY _ hk_eq])
        qed
        ultimately show ?thesis by (by100 simp)
      qed
      ultimately show "k \<in> top1_fundamental_group_mul Y TY y0 (?ind c1) (?ind c2)"
        unfolding top1_fundamental_group_mul_def by (by100 blast)
    next
      \<comment> \<open>Backward: k \<in> mul_Y(ind c1, ind c2) \<Longrightarrow> k \<in> ind(mul c1 c2).\<close>
      assume "k \<in> top1_fundamental_group_mul Y TY y0 (?ind c1) (?ind c2)"
      \<comment> \<open>Expand: \<exists>\<phi>\<in>ind(c1). \<exists>\<psi>\<in>ind(c2). loop_equiv_Y(\<phi>*\<psi>, k).\<close>
      \<comment> \<open>\<phi> ~ h\<circ>f for some f\<in>c1, \<psi> ~ h\<circ>g for some g\<in>c2.\<close>
      \<comment> \<open>\<phi>*\<psi> ~ (h\<circ>f)*(h\<circ>g) = h\<circ>(f*g). And f*g \<in> mul(c1,c2).\<close>
      then obtain \<phi> \<psi> where h\<phi>: "\<phi> \<in> ?ind c1" and h\<psi>: "\<psi> \<in> ?ind c2"
          and hk_mul: "top1_loop_equiv_on Y TY y0 (top1_path_product \<phi> \<psi>) k"
        unfolding top1_fundamental_group_mul_def by (by100 blast)
      from h\<phi> obtain f1 where hf1: "f1 \<in> c1"
          and h\<phi>_eq: "top1_loop_equiv_on Y TY y0 (h \<circ> f1) \<phi>"
        unfolding top1_fundamental_group_induced_on_def hh0[symmetric] by (by100 blast)
      from h\<psi> obtain g1 where hg1: "g1 \<in> c2"
          and h\<psi>_eq: "top1_loop_equiv_on Y TY y0 (h \<circ> g1) \<psi>"
        unfolding top1_fundamental_group_induced_on_def hh0[symmetric] by (by100 blast)
      \<comment> \<open>(h\<circ>f1)*(h\<circ>g1) ~_Y \<phi>*\<psi> (product preserves homotopy).\<close>
      \<comment> \<open>(h\<circ>f1)*(h\<circ>g1) = h\<circ>(f1*g1) by comp_path_product.\<close>
      \<comment> \<open>So h\<circ>(f1*g1) ~_Y \<phi>*\<psi> ~_Y k. And f1*g1 \<in> mul(c1,c2).\<close>
      have hf1_loop: "top1_is_loop_on X TX x0 f1"
        using hc1 hf1 unfolding top1_fundamental_group_carrier_def top1_loop_equiv_on_def
        by (by100 blast)
      have hg1_loop: "top1_is_loop_on X TX x0 g1"
        using hc2 hg1 unfolding top1_fundamental_group_carrier_def top1_loop_equiv_on_def
        by (by100 blast)
      \<comment> \<open>f1*g1 is a loop, h\<circ>(f1*g1) is a loop.\<close>
      have hfg_loop: "top1_is_loop_on X TX x0 (top1_path_product f1 g1)"
        by (rule top1_path_product_is_loop[OF hTX hf1_loop hg1_loop])
      \<comment> \<open>f1*g1 ~_X f1*g1 (reflexivity) means f1*g1 \<in> mul(c1,c2).\<close>
      have "top1_path_product f1 g1 \<in> top1_fundamental_group_mul X TX x0 c1 c2"
        unfolding top1_fundamental_group_mul_def
        using hf1 hg1 top1_loop_equiv_on_refl[OF hfg_loop] by (by100 blast)
      \<comment> \<open>h\<circ>(f1*g1) ~_Y k.\<close>
      moreover have "top1_loop_equiv_on Y TY y0 (h \<circ> top1_path_product f1 g1) k"
      proof -
        \<comment> \<open>Step 1: (h\<circ>f1)*(h\<circ>g1) ~_Y \<phi>*\<psi> by product preserves homotopy.\<close>
        have h\<phi>_hom: "top1_path_homotopic_on Y TY y0 y0 (h \<circ> f1) \<phi>"
          using h\<phi>_eq unfolding top1_loop_equiv_on_def by (by100 blast)
        have h\<psi>_hom: "top1_path_homotopic_on Y TY y0 y0 (h \<circ> g1) \<psi>"
          using h\<psi>_eq unfolding top1_loop_equiv_on_def by (by100 blast)
        have hf1_Y': "top1_is_loop_on Y TY y0 (h \<circ> f1)"
          using top1_continuous_map_loop[OF hcont hf1_loop] hh0 by (by100 simp)
        have hg1_Y': "top1_is_loop_on Y TY y0 (h \<circ> g1)"
          using top1_continuous_map_loop[OF hcont hg1_loop] hh0 by (by100 simp)
        have hprod_hom: "top1_path_homotopic_on Y TY y0 y0
            (top1_path_product (h \<circ> f1) (h \<circ> g1)) (top1_path_product \<phi> \<psi>)"
        proof -
          have s1: "top1_path_homotopic_on Y TY y0 y0
              (top1_path_product (h \<circ> f1) (h \<circ> g1)) (top1_path_product \<phi> (h \<circ> g1))"
          proof -
            have "top1_is_path_on Y TY y0 y0 (h \<circ> g1)"
              using hg1_Y' unfolding top1_is_loop_on_def by (by100 blast)
            thus ?thesis by (rule path_homotopic_product_left[OF hTY h\<phi>_hom])
          qed
          have s2: "top1_path_homotopic_on Y TY y0 y0
              (top1_path_product \<phi> (h \<circ> g1)) (top1_path_product \<phi> \<psi>)"
          proof -
            have "\<phi> \<in> ?ind c1" by (rule h\<phi>)
            hence "top1_is_path_on Y TY y0 y0 \<phi>"
              using h\<phi>_eq unfolding top1_loop_equiv_on_def top1_is_loop_on_def by (by100 blast)
            thus ?thesis by (rule path_homotopic_product_right[OF hTY h\<psi>_hom])
          qed
          show ?thesis by (rule Lemma_51_1_path_homotopic_trans[OF hTY s1 s2])
        qed
        \<comment> \<open>Step 2: h\<circ>(f1*g1) = (h\<circ>f1)*(h\<circ>g1).\<close>
        have "h \<circ> top1_path_product f1 g1 = top1_path_product (h \<circ> f1) (h \<circ> g1)"
          by (rule comp_path_product)
        \<comment> \<open>Step 3: Combine via transitivity.\<close>
        hence "top1_path_homotopic_on Y TY y0 y0
            (h \<circ> top1_path_product f1 g1) (top1_path_product \<phi> \<psi>)"
          using hprod_hom by (by100 simp)
        hence "top1_loop_equiv_on Y TY y0 (h \<circ> top1_path_product f1 g1) (top1_path_product \<phi> \<psi>)"
          unfolding top1_loop_equiv_on_def
          using top1_continuous_map_loop[OF hcont hfg_loop] hh0
                hk_mul unfolding top1_loop_equiv_on_def by (by100 simp)
        thus ?thesis by (rule top1_loop_equiv_on_trans[OF hTY _ hk_mul])
      qed
      ultimately show "k \<in> ?ind (top1_fundamental_group_mul X TX x0 c1 c2)"
        unfolding top1_fundamental_group_induced_on_def hh0[symmetric] by (by100 blast)
    qed
  qed
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
  \<comment> \<open>Proof: decompose S²-{p,q} = (S²-e13) ∪ (S²-e24). Their intersection S²-(e13∪e24)
     has two components. The 4-cycle loop f alternates between the components,
     creating a nontrivial element by Theorem 63.1.\<close>
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
      (top1_fundamental_group_induced_on C ?TC c0 ?Xpq ?TXpq c0 (\<lambda>x. x))"
  proof -
    have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
      using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have hTC: "is_topology_on C ?TC"
    proof -
      have "C \<subseteq> top1_S2"
        using assms(2) unfolding top1_simple_closed_curve_on_def top1_continuous_map_on_def
        by (by100 blast)
      thus ?thesis by (rule subspace_topology_is_topology_on[OF hTopS2])
    qed
    have hTXpq: "is_topology_on ?Xpq ?TXpq"
      by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
    have hc0_C: "c0 \<in> C" by (rule assms(6))
    have hC_sub_S2: "C \<subseteq> top1_S2" using simple_closed_curve_subset[OF assms(2)] .
    have hC_sub_Xpq: "C \<subseteq> top1_S2 - {p} - {q}"
    proof -
      have "p \<notin> C" using assms(3) by (by100 blast)
      moreover have "q \<notin> C" using assms(4) by (by100 blast)
      ultimately show ?thesis using hC_sub_S2 by (by100 blast)
    qed
    have hc0_Xpq: "c0 \<in> ?Xpq" using hC_sub_Xpq hc0_C by (by100 blast)
    \<comment> \<open>Inclusion C \<hookrightarrow> Xpq continuous.\<close>
    have hincl: "top1_continuous_map_on C ?TC ?Xpq ?TXpq (\<lambda>x. x)"
    proof -
      have hid_Xpq: "top1_continuous_map_on ?Xpq ?TXpq ?Xpq ?TXpq id"
        by (rule top1_continuous_map_on_id[OF hTXpq])
      have "C \<subseteq> ?Xpq" using hC_sub_Xpq .
      from top1_continuous_map_on_restrict_domain_simple[OF hid_Xpq this]
      have "top1_continuous_map_on C (subspace_topology ?Xpq ?TXpq C) ?Xpq ?TXpq id" .
      moreover have "subspace_topology ?Xpq ?TXpq C = ?TC"
        using subspace_topology_trans[OF \<open>C \<subseteq> ?Xpq\<close>] by (by100 simp)
      moreover have "id = (\<lambda>x::(real\<times>real\<times>real). x)" by (rule ext) (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    show ?thesis
      by (rule top1_fundamental_group_induced_on_is_hom[OF hTC hTXpq hc0_C hc0_Xpq hincl]) (by100 simp)
  qed
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

lemma subgroup_generated_subset:
  assumes "top1_is_group_on G mul e invg" and "S \<subseteq> G"
  shows "top1_subgroup_generated_on G mul e invg S \<subseteq> G"
proof -
  have "G \<in> { H. S \<subseteq> H \<and> H \<subseteq> G \<and> top1_is_group_on H mul e invg }"
    using assms by (by100 blast)
  thus ?thesis unfolding top1_subgroup_generated_on_def by (rule Inter_lower)
qed

lemma subgroup_generated_contains:
  assumes "top1_is_group_on G mul e invg" and "S \<subseteq> G" and "x \<in> S"
  shows "x \<in> top1_subgroup_generated_on G mul e invg S"
  unfolding top1_subgroup_generated_on_def using assms by (by100 blast)

lemma subgroup_generated_minimal:
  assumes "S \<subseteq> H" and "H \<subseteq> G" and "top1_is_group_on H mul e invg"
  shows "top1_subgroup_generated_on G mul e invg S \<subseteq> H"
proof -
  have "H \<in> { H. S \<subseteq> H \<and> H \<subseteq> G \<and> top1_is_group_on H mul e invg }"
    using assms by (by100 blast)
  thus ?thesis unfolding top1_subgroup_generated_on_def by (rule Inter_lower)
qed

text \<open>Helper: double inverse is identity.\<close>
lemma group_inv_inv_early:
  assumes hG: "top1_is_group_on G mul e invg" and hx: "x \<in> G"
  shows "invg (invg x) = x"
proof -
  have hix: "invg x \<in> G"
    using hG hx unfolding top1_is_group_on_def by (by100 blast)
  have hiix: "invg (invg x) \<in> G"
    using hG hix unfolding top1_is_group_on_def by (by100 blast)
  have h1: "mul (invg (invg x)) (invg x) = e"
    using hG hix unfolding top1_is_group_on_def by (by100 blast)
  have h2: "mul (invg x) x = e"
    using hG hx unfolding top1_is_group_on_def by (by100 blast)
  \<comment> \<open>Multiply h1 on the right by x: (invg(invg x))*(invg x)*x = e*x = x.
     By assoc: (invg(invg x))*((invg x)*x) = (invg(invg x))*e = invg(invg x).
     So invg(invg x) = x.\<close>
  have hid_r: "mul (invg (invg x)) e = invg (invg x)"
    using hG hiix unfolding top1_is_group_on_def by (by100 blast)
  have h3: "mul (invg (invg x)) (mul (invg x) x) = invg (invg x)"
    using h2 hid_r by (by100 simp)
  have hassoc_all: "\<forall>a\<in>G. \<forall>b\<in>G. \<forall>c\<in>G. mul (mul a b) c = mul a (mul b c)"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  have hassoc1: "\<forall>b\<in>G. \<forall>c\<in>G. mul (mul (invg (invg x)) b) c = mul (invg (invg x)) (mul b c)"
    using hassoc_all hiix by (by100 blast)
  have hassoc2: "\<forall>c\<in>G. mul (mul (invg (invg x)) (invg x)) c = mul (invg (invg x)) (mul (invg x) c)"
    using hassoc1 hix by (by100 blast)
  have h4: "mul (mul (invg (invg x)) (invg x)) x = mul (invg (invg x)) (mul (invg x) x)"
    using hassoc2 hx by (by100 blast)
  have h5: "mul (mul (invg (invg x)) (invg x)) x = mul e x"
    using h1 by (by100 simp)
  have h6: "mul e x = x"
    using hG hx unfolding top1_is_group_on_def by (by100 blast)
  have "invg (invg x) = mul (invg (invg x)) (mul (invg x) x)" using h3 h2 by (by100 simp)
  also have "\<dots> = mul (mul (invg (invg x)) (invg x)) x" using h4 by (by100 simp)
  also have "\<dots> = mul e x" using h5 by (by100 simp)
  also have "\<dots> = x" using h6 by (by100 simp)
  finally show "invg (invg x) = x" .
qed

text \<open>Helper: foldr mul of a list of group elements is in G.\<close>
lemma foldr_mul_closed:
  assumes hG: "top1_is_group_on G mul e invg"
      and hall: "\<forall>i<length xs. xs!i \<in> G"
  shows "foldr mul xs e \<in> G"
  using hall
proof (induction xs)
  case Nil
  have "e \<in> G" using hG unfolding top1_is_group_on_def by (by100 blast)
  thus ?case by (by100 simp)
next
  case (Cons a xs)
  have haG: "a \<in> G" using Cons.prems by (by100 force)
  have hxs': "\<forall>i<length xs. xs!i \<in> G" using Cons.prems by (by100 force)
  have "foldr mul xs e \<in> G" using Cons.IH hxs' by (by100 blast)
  hence "mul a (foldr mul xs e) \<in> G"
    using hG haG unfolding top1_is_group_on_def by (by100 blast)
  thus ?case by (by100 simp)
qed

text \<open>Helper: foldr mul distributes over append (when elements are in G).\<close>
lemma foldr_mul_append:
  assumes hG: "top1_is_group_on G mul e invg"
      and hxs: "\<forall>i<length xs. xs!i \<in> G"
      and hys: "\<forall>i<length ys. ys!i \<in> G"
  shows "foldr mul (xs @ ys) e = mul (foldr mul xs e) (foldr mul ys e)"
  using hxs
proof (induction xs)
  case Nil
  have hfyG: "foldr mul ys e \<in> G" using foldr_mul_closed[OF hG hys] by (by100 blast)
  have "mul e (foldr mul ys e) = foldr mul ys e"
    using hG hfyG unfolding top1_is_group_on_def by (by100 blast)
  thus ?case by (by100 simp)
next
  case (Cons a xs)
  have haG: "a \<in> G" using Cons.prems by (by100 force)
  have hxs': "\<forall>i<length xs. xs!i \<in> G" using Cons.prems by (by100 force)
  have IH: "foldr mul (xs @ ys) e = mul (foldr mul xs e) (foldr mul ys e)"
    using Cons.IH hxs' by (by100 blast)
  have hfoldr_xs_G: "foldr mul xs e \<in> G"
    using foldr_mul_closed[OF hG hxs'] by (by100 blast)
  have hfoldr_ys_G: "foldr mul ys e \<in> G"
    using foldr_mul_closed[OF hG hys] by (by100 blast)
  have hassoc_all: "\<forall>x\<in>G. \<forall>y\<in>G. \<forall>z\<in>G. mul (mul x y) z = mul x (mul y z)"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  have hassoc_a: "\<forall>y\<in>G. \<forall>z\<in>G. mul (mul a y) z = mul a (mul y z)"
    using hassoc_all haG by (by100 blast)
  have hassoc: "mul (mul a (foldr mul xs e)) (foldr mul ys e) = mul a (mul (foldr mul xs e) (foldr mul ys e))"
    using hassoc_a hfoldr_xs_G hfoldr_ys_G
    apply (drule_tac x="foldr mul xs e" in bspec)
    apply (by100 blast)
    apply (drule_tac x="foldr mul ys e" in bspec)
    apply (by100 blast)
    apply (by100 assumption)
    done
  show ?case using IH hassoc by (by100 simp)
qed

text \<open>Helper: foldr mul of reversed inverted list gives inverse.\<close>
lemma foldr_mul_rev_inv:
  assumes hG: "top1_is_group_on G mul e invg"
      and hall: "\<forall>i<length ws. ws!i \<in> G"
  shows "mul (foldr mul ws e) (foldr mul (rev (map invg ws)) e) = e"
  using hall
proof (induction ws)
  case Nil
  show ?case using hG unfolding top1_is_group_on_def by (by100 simp)
next
  case (Cons a ws)
  have haG: "a \<in> G" using Cons.prems by (by100 force)
  have hws': "\<forall>i<length ws. ws!i \<in> G" using Cons.prems by (by100 force)
  have IH: "mul (foldr mul ws e) (foldr mul (rev (map invg ws)) e) = e"
    using Cons.IH hws' by (by100 blast)
  \<comment> \<open>Abbreviations.\<close>
  let ?w = "foldr mul ws e"
  let ?r = "foldr mul (rev (map invg ws)) e"
  have hiaG: "invg a \<in> G" using hG haG unfolding top1_is_group_on_def by (by100 blast)
  have hwG: "?w \<in> G" using foldr_mul_closed[OF hG hws'] by (by100 blast)
  \<comment> \<open>Elements of map invg ws are in G.\<close>
  have hinv_ws: "\<forall>i<length (map invg ws). (map invg ws)!i \<in> G"
  proof (intro allI impI)
    fix i assume "i < length (map invg ws)"
    hence hi: "i < length ws" by (by100 simp)
    have "ws!i \<in> G" using hws' hi by (by100 blast)
    hence "invg (ws!i) \<in> G" using hG unfolding top1_is_group_on_def by (by100 blast)
    thus "(map invg ws)!i \<in> G" using hi by (by100 simp)
  qed
  have hrev_ws: "\<forall>i<length (rev (map invg ws)). (rev (map invg ws))!i \<in> G"
  proof (intro allI impI)
    fix i assume hi: "i < length (rev (map invg ws))"
    hence hi2: "i < length (map invg ws)" by (by100 simp)
    have "(rev (map invg ws))!i = (map invg ws)!(length (map invg ws) - 1 - i)"
      using hi2 by (simp add: rev_nth)
    moreover have "length (map invg ws) - 1 - i < length (map invg ws)" using hi2
    proof -
      have "length (map invg ws) > 0" using hi2 by (by100 linarith)
      thus ?thesis using hi2 by (by100 simp)
    qed
    ultimately show "(rev (map invg ws))!i \<in> G" using hinv_ws by (by100 simp)
  qed
  have hrG: "?r \<in> G" using foldr_mul_closed[OF hG hrev_ws] by (by100 blast)
  \<comment> \<open>foldr distributes over append.\<close>
  have h_invg_ia: "\<forall>i<length [invg a]. [invg a]!i \<in> G"
    using hiaG by (by100 simp)
  have h_fold_split: "foldr mul (rev (map invg ws) @ [invg a]) e
      = mul ?r (foldr mul [invg a] e)"
    using foldr_mul_append[OF hG hrev_ws h_invg_ia] by (by100 blast)
  have h_fold_ia: "foldr mul [invg a] e = mul (invg a) e"
    by (by100 simp)
  have h_id_ia: "mul (invg a) e = invg a"
    using hG hiaG unfolding top1_is_group_on_def by (by100 blast)
  have h_rhs: "foldr mul (rev (map invg (a # ws))) e = mul ?r (invg a)"
  proof -
    have "rev (map invg (a # ws)) = rev (map invg ws) @ [invg a]" by (by100 simp)
    hence "foldr mul (rev (map invg (a # ws))) e = foldr mul (rev (map invg ws) @ [invg a]) e"
      by (by100 simp)
    also have "\<dots> = mul ?r (mul (invg a) e)" using h_fold_split h_fold_ia by (by100 simp)
    also have "mul (invg a) e = invg a" using h_id_ia by (by100 simp)
    finally show ?thesis .
  qed
  \<comment> \<open>Main calculation.\<close>
  have h_lhs: "foldr mul (a # ws) e = mul a ?w" by (by100 simp)
  \<comment> \<open>mul (mul a w) (mul r (invg a)) = mul a (mul w (mul r (invg a)))  [assoc]\<close>
  have hmria: "mul ?r (invg a) \<in> G"
    using hG hrG hiaG unfolding top1_is_group_on_def by (by100 blast)
  have hassoc_all: "\<forall>x\<in>G. \<forall>y\<in>G. \<forall>z\<in>G. mul (mul x y) z = mul x (mul y z)"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  have h_step1: "mul (mul a ?w) (mul ?r (invg a)) = mul a (mul ?w (mul ?r (invg a)))"
  proof -
    have "\<forall>y\<in>G. \<forall>z\<in>G. mul (mul a y) z = mul a (mul y z)"
      using hassoc_all haG by (by100 blast)
    hence "\<forall>z\<in>G. mul (mul a ?w) z = mul a (mul ?w z)"
      using hwG by (by100 blast)
    thus ?thesis using hmria by (by100 blast)
  qed
  \<comment> \<open>mul w (mul r (invg a)) = mul (mul w r) (invg a)  [assoc]\<close>
  have h_step2: "mul ?w (mul ?r (invg a)) = mul (mul ?w ?r) (invg a)"
  proof -
    have "\<forall>y\<in>G. \<forall>z\<in>G. mul (mul ?w y) z = mul ?w (mul y z)"
      using hassoc_all hwG by (by100 blast)
    hence hwr: "\<forall>z\<in>G. mul (mul ?w ?r) z = mul ?w (mul ?r z)"
      using hrG by (by100 blast)
    have "mul (mul ?w ?r) (invg a) = mul ?w (mul ?r (invg a))"
      using hwr hiaG by (by100 blast)
    thus ?thesis by (by100 simp)
  qed
  have h_step3: "mul (mul ?w ?r) (invg a) = mul e (invg a)"
    using IH by (by100 simp)
  have h_step4: "mul e (invg a) = invg a"
    using hG hiaG unfolding top1_is_group_on_def by (by100 blast)
  have h_step5: "mul a (invg a) = e"
    using hG haG unfolding top1_is_group_on_def by (by100 blast)
  show ?case
  proof -
    have "mul (foldr mul (a # ws) e) (foldr mul (rev (map invg (a # ws))) e)
      = mul (mul a ?w) (mul ?r (invg a))" using h_lhs h_rhs by (by100 simp)
    also have "\<dots> = mul a (mul ?w (mul ?r (invg a)))" using h_step1 by (by100 simp)
    also have "mul ?w (mul ?r (invg a)) = mul (mul ?w ?r) (invg a)" using h_step2 by (by100 simp)
    also have "mul (mul ?w ?r) (invg a) = mul e (invg a)" using h_step3 by (by100 simp)
    also have "mul e (invg a) = invg a" using h_step4 by (by100 simp)
    finally have "mul (foldr mul (a # ws) e) (foldr mul (rev (map invg (a # ws))) e)
      = mul a (invg a)" by (by100 simp)
    also have "mul a (invg a) = e" using h_step5 by (by100 simp)
    finally show ?thesis .
  qed
qed

text \<open>Elements of the subgroup generated by S can be expressed as products of
  elements of S and their inverses. Formally: for every g in subgroup_generated(S),
  either g = e, or there exist generators s_1,...,s_n in S \<union> invg(S) such that
  g = mul s_1 (mul s_2 ... (mul s_n e) ...).\<close>
lemma subgroup_generated_word_repr:
  assumes hG: "top1_is_group_on G mul e invg" and hS: "S \<subseteq> G"
      and hg: "g \<in> top1_subgroup_generated_on G mul e invg S"
  shows "g = e \<or> (\<exists>ws. length ws > 0
      \<and> (\<forall>i<length ws. ws!i \<in> S \<or> (\<exists>s\<in>S. ws!i = invg s))
      \<and> foldr mul ws e = g)"
proof -
  \<comment> \<open>Define the word-representability predicate.\<close>
  let ?repr = "\<lambda>g. g = e \<or> (\<exists>ws. length ws > 0
      \<and> (\<forall>i<length ws. ws!i \<in> S \<or> (\<exists>s\<in>S. ws!i = invg s))
      \<and> foldr mul ws e = g)"
  let ?W = "{g \<in> G. ?repr g}"
  \<comment> \<open>Helper: group axioms.\<close>
  have hid_right: "\<forall>x\<in>G. mul x e = x" using hG unfolding top1_is_group_on_def by (by100 blast)
  have hmul_closed: "\<forall>x\<in>G. \<forall>y\<in>G. mul x y \<in> G"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  have hinv_closed: "\<forall>x\<in>G. invg x \<in> G"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  have heG: "e \<in> G" using hG unfolding top1_is_group_on_def by (by100 blast)
  \<comment> \<open>S \<subseteq> W: each s \<in> S has representation [s].\<close>
  have hS_sub_W: "S \<subseteq> ?W"
  proof (rule subsetI)
    fix s assume hs: "s \<in> S"
    hence hsG: "s \<in> G" using hS by (by100 blast)
    have hfold: "foldr mul [s] e = s" using hid_right hsG by (by100 simp)
    have hlen: "length [s] > 0" by (by100 simp)
    have hgen: "\<forall>i<length [s]. [s]!i \<in> S \<or> (\<exists>sa\<in>S. [s]!i = invg sa)"
    proof (intro allI impI)
      fix i assume "i < length [s]"
      hence "i = 0" by (by100 simp)
      thus "[s]!i \<in> S \<or> (\<exists>sa\<in>S. [s]!i = invg sa)" using hs by (by100 simp)
    qed
    have "\<exists>ws. length ws > 0
        \<and> (\<forall>i<length ws. ws!i \<in> S \<or> (\<exists>sa\<in>S. ws!i = invg sa))
        \<and> foldr mul ws e = s"
      apply (rule exI[of _ "[s]"])
      using hlen hgen hfold by (by100 blast)
    hence "?repr s" by (by100 blast)
    thus "s \<in> ?W" using hsG by (by100 blast)
  qed
  \<comment> \<open>W \<subseteq> G.\<close>
  have hW_sub: "?W \<subseteq> G" by (by100 blast)
  \<comment> \<open>W is a subgroup.\<close>
  have hW_grp: "top1_is_group_on ?W mul e invg"
    unfolding top1_is_group_on_def
  proof (intro conjI ballI)
    \<comment> \<open>e \<in> W: identity has trivial representation.\<close>
    show "e \<in> ?W" using heG by (by100 blast)
  next
    \<comment> \<open>Closure under multiplication: concatenate word representations.\<close>
    fix x y assume hx: "x \<in> ?W" and hy: "y \<in> ?W"
    have hxG: "x \<in> G" using hx by (by100 blast)
    have hyG: "y \<in> G" using hy by (by100 blast)
    have hxyG: "mul x y \<in> G" using hmul_closed hxG hyG by (by100 blast)
    have hxR: "?repr x" using hx by (by100 blast)
    have hyR: "?repr y" using hy by (by100 blast)
    show "mul x y \<in> ?W"
    proof (cases "x = e")
      case True
      have "mul e y = y" using hG hyG unfolding top1_is_group_on_def by (by100 blast)
      hence "mul x y = y" using True by (by100 simp)
      hence "?repr (mul x y)" using hyR by (by100 simp)
      thus ?thesis using hxyG by (by100 blast)
    next
      case hxne: False
      show ?thesis
      proof (cases "y = e")
        case True
        have "mul x e = x" using hid_right hxG by (by100 blast)
        hence "mul x y = x" using True by (by100 simp)
        hence "?repr (mul x y)" using hxR by (by100 simp)
        thus ?thesis using hxyG by (by100 blast)
      next
        case hyne: False
        \<comment> \<open>Both x,y have non-trivial word representations.\<close>
        obtain wxs where hwxlen: "length wxs > 0"
          and hwxgen: "\<forall>i<length wxs. wxs!i \<in> S \<or> (\<exists>s\<in>S. wxs!i = invg s)"
          and hwxfold: "foldr mul wxs e = x"
          using hxR hxne by (by100 blast)
        obtain wys where hwylen: "length wys > 0"
          and hwygen: "\<forall>i<length wys. wys!i \<in> S \<or> (\<exists>s\<in>S. wys!i = invg s)"
          and hwyfold: "foldr mul wys e = y"
          using hyR hyne by (by100 blast)
        \<comment> \<open>The concatenation wxs @ wys represents mul x y.\<close>
        let ?ws = "wxs @ wys"
        have hlen: "length ?ws > 0" using hwxlen by (by100 simp)
        have hgen: "\<forall>i<length ?ws. ?ws!i \<in> S \<or> (\<exists>s\<in>S. ?ws!i = invg s)"
        proof (intro allI impI)
          fix i assume hi: "i < length ?ws"
          show "?ws!i \<in> S \<or> (\<exists>s\<in>S. ?ws!i = invg s)"
          proof (cases "i < length wxs")
            case True
            have eq: "(wxs @ wys) ! i = (if i < length wxs then wxs ! i else wys ! (i - length wxs))"
              by (rule nth_append)
            have "?ws!i = wxs!i" using True eq by (by100 simp)
            thus ?thesis using hwxgen True by (by100 simp)
          next
            case False
            hence hge: "i \<ge> length wxs" by (by100 simp)
            have eq: "(wxs @ wys) ! i = (if i < length wxs then wxs ! i else wys ! (i - length wxs))"
              by (rule nth_append)
            have hiwsi: "?ws!i = wys!(i - length wxs)" using hge eq by (by100 simp)
            have hidx: "i - length wxs < length wys" using hi hge by (by100 simp)
            have "wys!(i - length wxs) \<in> S \<or> (\<exists>s\<in>S. wys!(i - length wxs) = invg s)"
              using hwygen hidx by (by100 blast)
            thus ?thesis using hiwsi by (by100 simp)
          qed
        qed
        \<comment> \<open>All word elements are in G.\<close>
        have hwxG: "\<forall>i<length wxs. wxs!i \<in> G"
        proof (intro allI impI)
          fix i assume hi: "i < length wxs"
          have "wxs!i \<in> S \<or> (\<exists>s\<in>S. wxs!i = invg s)" using hwxgen hi by (by100 blast)
          thus "wxs!i \<in> G"
          proof
            assume "wxs!i \<in> S" thus ?thesis using hS by (by100 blast)
          next
            assume "\<exists>s\<in>S. wxs!i = invg s"
            then obtain s where "s \<in> S" "wxs!i = invg s" by (by100 blast)
            hence "s \<in> G" using hS by (by100 blast)
            hence "invg s \<in> G" using hinv_closed by (by100 blast)
            thus ?thesis using \<open>wxs!i = invg s\<close> by (by100 simp)
          qed
        qed
        have hwyG: "\<forall>i<length wys. wys!i \<in> G"
        proof (intro allI impI)
          fix i assume hi: "i < length wys"
          have "wys!i \<in> S \<or> (\<exists>s\<in>S. wys!i = invg s)" using hwygen hi by (by100 blast)
          thus "wys!i \<in> G"
          proof
            assume "wys!i \<in> S" thus ?thesis using hS by (by100 blast)
          next
            assume "\<exists>s\<in>S. wys!i = invg s"
            then obtain s where "s \<in> S" "wys!i = invg s" by (by100 blast)
            hence "s \<in> G" using hS by (by100 blast)
            hence "invg s \<in> G" using hinv_closed by (by100 blast)
            thus ?thesis using \<open>wys!i = invg s\<close> by (by100 simp)
          qed
        qed
        \<comment> \<open>foldr mul (wxs @ wys) e = mul (foldr mul wxs e) (foldr mul wys e).\<close>
        have hfold_app: "foldr mul (wxs @ wys) e = mul (foldr mul wxs e) (foldr mul wys e)"
          using foldr_mul_append[OF hG hwxG hwyG] by (by100 blast)
        have hfoldxy: "foldr mul ?ws e = mul x y" using hfold_app hwxfold hwyfold by (by100 simp)
        have hconj: "length ?ws > 0
            \<and> (\<forall>i<length ?ws. ?ws!i \<in> S \<or> (\<exists>s\<in>S. ?ws!i = invg s))
            \<and> foldr mul ?ws e = mul x y"
          using hlen hgen hfoldxy by (by100 blast)
        have "\<exists>ws. length ws > 0
            \<and> (\<forall>i<length ws. ws!i \<in> S \<or> (\<exists>s\<in>S. ws!i = invg s))
            \<and> foldr mul ws e = mul x y"
          using hconj by (rule exI[of _ "?ws"])
        hence "?repr (mul x y)" by (by100 blast)
        thus ?thesis using hxyG by (by100 blast)
      qed
    qed
  next
    \<comment> \<open>Closure under inverse: reverse and invert word.\<close>
    fix x assume hx: "x \<in> ?W"
    have hxG: "x \<in> G" using hx by (by100 blast)
    have hixG: "invg x \<in> G" using hinv_closed hxG by (by100 blast)
    have hxR: "?repr x" using hx by (by100 blast)
    show "invg x \<in> ?W"
    proof (cases "x = e")
      case True
      have "mul (invg e) e = e" using hG unfolding top1_is_group_on_def by (by100 blast)
      moreover have "mul (invg e) e = invg e"
        using hid_right hinv_closed heG by (by100 blast)
      ultimately have "invg e = e" by (by100 simp)
      hence "?repr (invg x)" using True by (by100 simp)
      thus ?thesis using hixG by (by100 blast)
    next
      case hxne: False
      obtain ws where hwlen: "length ws > 0"
        and hwgen: "\<forall>i<length ws. ws!i \<in> S \<or> (\<exists>s\<in>S. ws!i = invg s)"
        and hwfold: "foldr mul ws e = x"
        using hxR hxne by (by100 blast)
      \<comment> \<open>The inverse of foldr mul [s1,...,sn] e is foldr mul [inv sn,...,inv s1] e.\<close>
      let ?iws = "rev (map invg ws)"
      have hilen: "length ?iws > 0" using hwlen by (by100 simp)
      \<comment> \<open>All word elements are in G.\<close>
      have hwG: "\<forall>i<length ws. ws!i \<in> G"
      proof (intro allI impI)
        fix i assume hi: "i < length ws"
        have "ws!i \<in> S \<or> (\<exists>s\<in>S. ws!i = invg s)" using hwgen hi by (by100 blast)
        thus "ws!i \<in> G"
        proof
          assume "ws!i \<in> S" thus ?thesis using hS by (by100 blast)
        next
          assume "\<exists>s\<in>S. ws!i = invg s"
          then obtain s where "s \<in> S" "ws!i = invg s" by (by100 blast)
          hence "s \<in> G" using hS by (by100 blast)
          hence "invg s \<in> G" using hinv_closed by (by100 blast)
          thus ?thesis using \<open>ws!i = invg s\<close> by (by100 simp)
        qed
      qed
      have higen: "\<forall>i<length ?iws. ?iws!i \<in> S \<or> (\<exists>s\<in>S. ?iws!i = invg s)"
      proof (intro allI impI)
        fix i assume hi: "i < length ?iws"
        hence hi2: "i < length ws" by (by100 simp)
        \<comment> \<open>?iws!i = invg (ws ! (length ws - 1 - i)).\<close>
        have hrev: "?iws ! i = invg (ws ! (length ws - 1 - i))"
        proof -
          have "?iws ! i = (map invg ws) ! (length ws - 1 - i)"
            using hi2 by (simp add: rev_nth)
          also have "\<dots> = invg (ws ! (length ws - 1 - i))" using hi2 by (by100 simp)
          finally show ?thesis .
        qed
        have hj: "length ws - 1 - i < length ws" using hi2 hwlen by (by100 simp)
        have "ws!(length ws - 1 - i) \<in> S \<or> (\<exists>s\<in>S. ws!(length ws - 1 - i) = invg s)"
          using hwgen hj by (by100 blast)
        thus "?iws!i \<in> S \<or> (\<exists>s\<in>S. ?iws!i = invg s)"
        proof
          assume hw_in_S: "ws!(length ws - 1 - i) \<in> S"
          \<comment> \<open>invg(ws!j) ∈ invg(S), i.e. ∃s∈S. iws!i = invg s.\<close>
          have "?iws!i = invg (ws!(length ws - 1 - i))" using hrev by (by100 simp)
          thus ?thesis using hw_in_S by (by100 blast)
        next
          assume "\<exists>s\<in>S. ws!(length ws - 1 - i) = invg s"
          then obtain s where hsS: "s \<in> S" and hws_eq: "ws!(length ws - 1 - i) = invg s"
            by (by100 blast)
          have hsG: "s \<in> G" using hsS hS by (by100 blast)
          have "?iws!i = invg (invg s)" using hrev hws_eq by (by100 simp)
          also have "invg (invg s) = s" by (rule group_inv_inv_early[OF hG hsG])
          finally have "?iws!i = s" .
          thus ?thesis using hsS by (by100 blast)
        qed
      qed
      have hifold: "foldr mul ?iws e = invg x"
      proof -
        \<comment> \<open>From foldr_mul_rev_inv: mul x (foldr ?iws) = e, so foldr ?iws = invg x.\<close>
        have hwsG: "\<forall>i<length ws. ws!i \<in> G" using hwG by (by100 blast)
        have h_prod_e: "mul (foldr mul ws e) (foldr mul ?iws e) = e"
          using foldr_mul_rev_inv[OF hG hwsG] by (by100 blast)
        have h_prod: "mul x (foldr mul ?iws e) = e" using h_prod_e hwfold by (by100 simp)
        \<comment> \<open>In a group: mul x y = e implies y = invg x.\<close>
        have hxG: "x \<in> G" using hx by (by100 blast)
        have hiwsG: "foldr mul ?iws e \<in> G"
        proof -
          have "\<forall>i<length (map invg ws). (map invg ws)!i \<in> G"
          proof (intro allI impI)
            fix i assume "i < length (map invg ws)"
            hence hi: "i < length ws" by (by100 simp)
            have hwsi: "ws!i \<in> G" using hwsG hi by (by100 blast)
            have "invg (ws!i) \<in> G" using hinv_closed hwsi by (by100 blast)
            thus "(map invg ws)!i \<in> G" using hi by (by100 simp)
          qed
          hence hrev_map: "\<forall>i<length (rev (map invg ws)). (rev (map invg ws))!i \<in> G"
          proof (intro allI impI)
            fix i assume hi: "i < length (rev (map invg ws))"
            hence hi2: "i < length (map invg ws)" by (by100 simp)
            have "(rev (map invg ws))!i = (map invg ws)!(length (map invg ws) - 1 - i)"
              using hi2 by (simp add: rev_nth)
            moreover have "length (map invg ws) - 1 - i < length (map invg ws)"
              using hi2 by (by100 linarith)
            ultimately have heq: "(rev (map invg ws))!i = (map invg ws)!(length (map invg ws) - 1 - i)"
              and hidx: "length (map invg ws) - 1 - i < length (map invg ws)" by simp+
            have "(map invg ws)!(length (map invg ws) - 1 - i) \<in> G"
              using \<open>\<forall>i<length (map invg ws). (map invg ws) ! i \<in> G\<close> hidx by (by100 blast)
            thus "(rev (map invg ws))!i \<in> G" using heq by (by100 simp)
          qed
          thus ?thesis using foldr_mul_closed[OF hG hrev_map] by (by100 blast)
        qed
        have hixG: "invg x \<in> G" using hinv_closed hxG by (by100 blast)
        \<comment> \<open>y = mul e y = mul (mul (invg x) x) y = mul (invg x) (mul x y) = mul (invg x) e = invg x.\<close>
        have h1: "mul (invg x) (mul x (foldr mul ?iws e)) = mul (invg x) e"
          using h_prod by (by100 simp)
        have h2: "mul (invg x) e = invg x"
          using hid_right hixG by (by100 blast)
        have hassoc2: "\<forall>b\<in>G. \<forall>c\<in>G. mul (mul (invg x) b) c = mul (invg x) (mul b c)"
        proof -
          have "\<forall>a\<in>G. \<forall>b\<in>G. \<forall>c\<in>G. mul (mul a b) c = mul a (mul b c)"
            using hG unfolding top1_is_group_on_def by (by100 blast)
          thus ?thesis using hixG by (by100 blast)
        qed
        have h3: "mul (mul (invg x) x) (foldr mul ?iws e) = mul (invg x) (mul x (foldr mul ?iws e))"
          using hassoc2 hxG hiwsG by (by100 blast)
        have h4: "mul (invg x) x = e" using hG hxG unfolding top1_is_group_on_def by (by100 blast)
        have h5: "mul e (foldr mul ?iws e) = foldr mul ?iws e"
          using hG hiwsG unfolding top1_is_group_on_def by (by100 blast)
        have "foldr mul ?iws e = mul e (foldr mul ?iws e)" using h5 by (by100 simp)
        also have "\<dots> = mul (mul (invg x) x) (foldr mul ?iws e)" using h4 by (by100 simp)
        also have "\<dots> = mul (invg x) (mul x (foldr mul ?iws e))" using h3 by (by100 simp)
        also have "\<dots> = mul (invg x) e" using h1 by (by100 simp)
        also have "\<dots> = invg x" using h2 by (by100 simp)
        finally show ?thesis .
      qed
      have hiconj: "length ?iws > 0
          \<and> (\<forall>i<length ?iws. ?iws!i \<in> S \<or> (\<exists>s\<in>S. ?iws!i = invg s))
          \<and> foldr mul ?iws e = invg x"
        using hilen higen hifold by (by100 blast)
      have "\<exists>ws. length ws > 0
          \<and> (\<forall>i<length ws. ws!i \<in> S \<or> (\<exists>s\<in>S. ws!i = invg s))
          \<and> foldr mul ws e = invg x"
        using hiconj by (rule exI[of _ "?iws"])
      hence "?repr (invg x)" by (by100 blast)
      thus ?thesis using hixG by (by100 blast)
    qed
  next
    \<comment> \<open>Associativity, identities, inverses — inherited from G.\<close>
    fix x y z assume hxW: "x \<in> ?W" and hyW: "y \<in> ?W" and hzW: "z \<in> ?W"
    have "x \<in> G" using hxW by (by100 simp)
    moreover have "y \<in> G" using hyW by (by100 simp)
    moreover have "z \<in> G" using hzW by (by100 simp)
    ultimately show "mul (mul x y) z = mul x (mul y z)"
      using hG unfolding top1_is_group_on_def by (by100 blast)
  next
    fix x assume hxW: "x \<in> ?W"
    have "x \<in> G" using hxW by (by100 simp)
    thus "mul e x = x" using hG unfolding top1_is_group_on_def by (by100 blast)
  next
    fix x assume hxW: "x \<in> ?W"
    have "x \<in> G" using hxW by (by100 simp)
    thus "mul x e = x" using hid_right by (by100 blast)
  next
    fix x assume hxW: "x \<in> ?W"
    have "x \<in> G" using hxW by (by100 simp)
    thus "mul (invg x) x = e" using hG unfolding top1_is_group_on_def by (by100 blast)
  next
    fix x assume hxW: "x \<in> ?W"
    have "x \<in> G" using hxW by (by100 simp)
    thus "mul x (invg x) = e" using hG unfolding top1_is_group_on_def by (by100 blast)
  qed
  \<comment> \<open>By minimality: subgroup_generated S \<subseteq> W.\<close>
  have "top1_subgroup_generated_on G mul e invg S \<subseteq> ?W"
    by (rule subgroup_generated_minimal[OF hS_sub_W hW_sub hW_grp])
  hence "g \<in> ?W" using hg by (by100 blast)
  thus ?thesis by (by100 blast)
qed

definition top1_normal_subgroup_generated_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set" where
  "top1_normal_subgroup_generated_on G mul e invg S =
     \<Inter> { N. S \<subseteq> N \<and> top1_normal_subgroup_on G mul e invg N }"

text \<open>The normal closure of any subset is a normal subgroup.\<close>
lemma normal_subgroup_generated_is_normal:
  assumes hG: "top1_is_group_on G mul e invg" and hS: "S \<subseteq> G"
  shows "top1_normal_subgroup_on G mul e invg (top1_normal_subgroup_generated_on G mul e invg S)"
proof -
  let ?N = "top1_normal_subgroup_generated_on G mul e invg S"
  let ?F = "{ N. S \<subseteq> N \<and> top1_normal_subgroup_on G mul e invg N }"
  \<comment> \<open>G itself is a normal subgroup of G containing S, so ?F is non-empty.\<close>
  have hG_normal: "top1_normal_subgroup_on G mul e invg G"
    unfolding top1_normal_subgroup_on_def
    using hG unfolding top1_is_group_on_def by (by100 blast)
  hence hG_in_F: "G \<in> ?F" using hS by (by100 blast)
  show ?thesis unfolding top1_normal_subgroup_on_def
  proof (intro conjI)
    show "?N \<subseteq> G"
      unfolding top1_normal_subgroup_generated_on_def
      using hG_in_F by (by100 blast)
  next
    show "top1_is_group_on ?N mul e invg"
      unfolding top1_normal_subgroup_generated_on_def top1_is_group_on_def
    proof (intro conjI ballI)
      show "e \<in> \<Inter>?F"
      proof (rule InterI)
        fix N assume "N \<in> ?F"
        thus "e \<in> N" unfolding top1_normal_subgroup_on_def top1_is_group_on_def by (by100 blast)
      qed
    next
      fix x y assume "x \<in> \<Inter>?F" "y \<in> \<Inter>?F"
      show "mul x y \<in> \<Inter>?F"
      proof (rule InterI)
        fix N assume "N \<in> ?F"
        hence "x \<in> N" "y \<in> N" using \<open>x \<in> \<Inter>?F\<close> \<open>y \<in> \<Inter>?F\<close> by (by100 blast)+
        thus "mul x y \<in> N"
          using \<open>N \<in> ?F\<close> unfolding top1_normal_subgroup_on_def top1_is_group_on_def by (by100 blast)
      qed
    next
      fix x assume "x \<in> \<Inter>?F"
      show "invg x \<in> \<Inter>?F"
      proof (rule InterI)
        fix N assume "N \<in> ?F"
        hence "x \<in> N" using \<open>x \<in> \<Inter>?F\<close> by (by100 blast)
        thus "invg x \<in> N"
          using \<open>N \<in> ?F\<close> unfolding top1_normal_subgroup_on_def top1_is_group_on_def by (by100 blast)
      qed
    next
      fix x y z assume "x \<in> \<Inter>?F" "y \<in> \<Inter>?F" "z \<in> \<Inter>?F"
      hence "x \<in> G" "y \<in> G" "z \<in> G" using hG_in_F by (by100 blast)+
      thus "mul (mul x y) z = mul x (mul y z)"
        using hG unfolding top1_is_group_on_def by (by100 blast)
    next
      fix x assume "x \<in> \<Inter>?F"
      hence "x \<in> G" using hG_in_F by (by100 blast)
      thus "mul e x = x" using hG unfolding top1_is_group_on_def by (by100 blast)
    next
      fix x assume "x \<in> \<Inter>?F"
      hence "x \<in> G" using hG_in_F by (by100 blast)
      thus "mul x e = x" using hG unfolding top1_is_group_on_def by (by100 blast)
    next
      fix x assume "x \<in> \<Inter>?F"
      hence "x \<in> G" using hG_in_F by (by100 blast)
      thus "mul (invg x) x = e" using hG unfolding top1_is_group_on_def by (by100 blast)
    next
      fix x assume "x \<in> \<Inter>?F"
      hence "x \<in> G" using hG_in_F by (by100 blast)
      thus "mul x (invg x) = e" using hG unfolding top1_is_group_on_def by (by100 blast)
    qed
  next
    show "\<forall>g\<in>G. \<forall>n\<in>?N. mul (mul g n) (invg g) \<in> ?N"
    proof (intro ballI)
      fix g n assume hg: "g \<in> G" and hn: "n \<in> ?N"
      show "mul (mul g n) (invg g) \<in> ?N"
        unfolding top1_normal_subgroup_generated_on_def
      proof (rule InterI)
        fix N assume "N \<in> ?F"
        hence "S \<subseteq> N" and "top1_normal_subgroup_on G mul e invg N" by (by100 blast)+
        hence "n \<in> N" using hn
          unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
        thus "mul (mul g n) (invg g) \<in> N"
          using \<open>top1_normal_subgroup_on G mul e invg N\<close> hg
          unfolding top1_normal_subgroup_on_def by (by100 blast)
      qed
    qed
  qed
qed

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


text \<open>Group axiom extraction lemmas (avoid unfolding top1_is_group_on_def repeatedly).\<close>

lemma group_e_mem: "top1_is_group_on G mul e invg \<Longrightarrow> e \<in> G"
  unfolding top1_is_group_on_def by (by100 blast)
lemma group_mul_closed: "top1_is_group_on G mul e invg \<Longrightarrow> x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> mul x y \<in> G"
  unfolding top1_is_group_on_def by (by100 blast)
lemma group_inv_closed: "top1_is_group_on G mul e invg \<Longrightarrow> x \<in> G \<Longrightarrow> invg x \<in> G"
  unfolding top1_is_group_on_def by (by100 blast)
lemma group_assoc: "top1_is_group_on G mul e invg \<Longrightarrow> x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> z \<in> G \<Longrightarrow>
    mul (mul x y) z = mul x (mul y z)"
  unfolding top1_is_group_on_def by (by100 blast)
lemma group_id_left: "top1_is_group_on G mul e invg \<Longrightarrow> x \<in> G \<Longrightarrow> mul e x = x"
  unfolding top1_is_group_on_def by (by100 blast)
lemma group_id_right: "top1_is_group_on G mul e invg \<Longrightarrow> x \<in> G \<Longrightarrow> mul x e = x"
  unfolding top1_is_group_on_def by (by100 blast)
lemma group_inv_left: "top1_is_group_on G mul e invg \<Longrightarrow> x \<in> G \<Longrightarrow> mul (invg x) x = e"
  unfolding top1_is_group_on_def by (by100 blast)
lemma group_inv_right: "top1_is_group_on G mul e invg \<Longrightarrow> x \<in> G \<Longrightarrow> mul x (invg x) = e"
  unfolding top1_is_group_on_def by (by100 blast)

text \<open>Derived: inverse of product.\<close>
lemma group_inv_mul:
  assumes hG: "top1_is_group_on G mul e invg" and hx: "x \<in> G" and hy: "y \<in> G"
  shows "invg (mul x y) = mul (invg y) (invg x)"
proof -
  let ?ix = "invg x" and ?iy = "invg y" and ?xy = "mul x y"
  have hix: "?ix \<in> G" by (rule group_inv_closed[OF hG hx])
  have hiy: "?iy \<in> G" by (rule group_inv_closed[OF hG hy])
  have hxy: "?xy \<in> G" by (rule group_mul_closed[OF hG hx hy])
  have hixy: "invg ?xy \<in> G" by (rule group_inv_closed[OF hG hxy])
  have hiyix: "mul ?iy ?ix \<in> G" by (rule group_mul_closed[OF hG hiy hix])
  \<comment> \<open>(iy*ix)*(x*y) = iy*((ix*x)*y) = iy*(e*y) = iy*y = e.\<close>
  have s0: "mul ?ix ?xy = mul (mul ?ix x) y"
    using group_assoc[OF hG hix hx hy] by (by100 simp)
  have s1: "mul (mul ?ix x) y = mul e y"
    using group_inv_left[OF hG hx] by (by100 simp)
  have s2: "mul e y = y" by (rule group_id_left[OF hG hy])
  have s3: "mul ?ix ?xy = y" using s0 s1 s2 by (by100 simp)
  have s4: "mul (mul ?iy ?ix) ?xy = mul ?iy (mul ?ix ?xy)"
    by (rule group_assoc[OF hG hiy hix hxy])
  have hleft: "mul (mul ?iy ?ix) ?xy = e"
    using s4 s3 group_inv_left[OF hG hy] by (by100 simp)
  \<comment> \<open>invg(xy)*(xy) = e = (iy*ix)*(xy). Right-cancel xy.\<close>
  have "mul (invg ?xy) ?xy = e" by (rule group_inv_left[OF hG hxy])
  \<comment> \<open>Both invg(xy) and (iy*ix) are left-inverses of xy. Unique left inverse.\<close>
  \<comment> \<open>a = a*e = a*(xy)*(xy)\<inverse> for any a. Apply to both sides.\<close>
  \<comment> \<open>iy*ix = (iy*ix)*e = (iy*ix)*(xy)*(xy)\<inverse> = e*(xy)\<inverse> = (xy)\<inverse>.\<close>
  have t1: "mul (mul ?iy ?ix) (mul ?xy (invg ?xy)) = mul (mul (mul ?iy ?ix) ?xy) (invg ?xy)"
    using group_assoc[OF hG hiyix hxy hixy] by (by100 simp)
  have t2: "mul ?xy (invg ?xy) = e" by (rule group_inv_right[OF hG hxy])
  have t3: "mul (mul ?iy ?ix) e = mul ?iy ?ix"
    by (rule group_id_right[OF hG hiyix])
  have t4: "mul ?iy ?ix = mul (mul ?iy ?ix) (mul ?xy (invg ?xy))"
    using t2 t3 by (by100 simp)
  have t5: "\<dots> = mul (mul (mul ?iy ?ix) ?xy) (invg ?xy)" by (rule t1)
  have t6: "mul (mul (mul ?iy ?ix) ?xy) (invg ?xy) = mul e (invg ?xy)"
    using hleft by (by100 simp)
  have t7: "mul e (invg ?xy) = invg ?xy"
    by (rule group_id_left[OF hG hixy])
  show "invg ?xy = mul ?iy ?ix"
    using t4 t5 t6 t7 by (by100 simp)
qed

lemma group_inv_inv:
  assumes hG: "top1_is_group_on G mul e invg" and hx: "x \<in> G"
  shows "invg (invg x) = x"
proof -
  have hix: "invg x \<in> G" by (rule group_inv_closed[OF hG hx])
  have hiix: "invg (invg x) \<in> G" by (rule group_inv_closed[OF hG hix])
  have "mul (invg (invg x)) (invg x) = e" by (rule group_inv_left[OF hG hix])
  moreover have "mul x (invg x) = e" by (rule group_inv_right[OF hG hx])
  \<comment> \<open>Both invg(invg x) and x are left-inverses of invg x. By right-cancel: they're equal.\<close>
  hence "mul (mul (invg (invg x)) (invg x)) (invg (invg x))
      = mul (mul x (invg x)) (invg (invg x))" using calculation by (by100 simp)
  hence "mul (invg (invg x)) (mul (invg x) (invg (invg x)))
      = mul x (mul (invg x) (invg (invg x)))"
    using group_assoc[OF hG hiix hix hiix] group_assoc[OF hG hx hix hiix] by (by100 simp)
  hence "mul (invg (invg x)) e = mul x e"
    using group_inv_right[OF hG hix] by (by100 simp)
  thus "invg (invg x) = x"
    using group_id_right[OF hG hiix] group_id_right[OF hG hx] by (by100 simp)
qed

text \<open>Group homomorphisms preserve identity and inverses.\<close>

lemma hom_preserves_id:
  assumes hG: "top1_is_group_on G mul e invg"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hh: "top1_group_hom_on G mul H mulH h"
  shows "h e = eH"
proof -
  have he: "e \<in> G" by (rule group_e_mem[OF hG])
  have hhe: "h e \<in> H" using hh he unfolding top1_group_hom_on_def by (by100 blast)
  have hinv_he: "invgH (h e) \<in> H" by (rule group_inv_closed[OF hH hhe])
  have "h e = h (mul e e)"
    using group_id_left[OF hG he] by (by100 simp)
  also have "\<dots> = mulH (h e) (h e)"
    using hh he unfolding top1_group_hom_on_def by (by100 blast)
  finally have heq: "h e = mulH (h e) (h e)" .
  have "h e = mulH (h e) eH"
    using group_id_right[OF hH hhe] by (by100 simp)
  also have "\<dots> = mulH (h e) (mulH (h e) (invgH (h e)))"
    using group_inv_right[OF hH hhe] by (by100 simp)
  also have "\<dots> = mulH (mulH (h e) (h e)) (invgH (h e))"
    using group_assoc[OF hH hhe hhe hinv_he] by (by100 simp)
  also have "mulH (h e) (h e) = h e" using heq by (by100 simp)
  also have "mulH (h e) (invgH (h e)) = eH"
    by (rule group_inv_right[OF hH hhe])
  finally show "h e = eH" .
qed

lemma hom_preserves_inv:
  assumes hG: "top1_is_group_on G mul e invg"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hh: "top1_group_hom_on G mul H mulH h"
      and hx: "x \<in> G"
  shows "h (invg x) = invgH (h x)"
proof -
  have hix: "invg x \<in> G" by (rule group_inv_closed[OF hG hx])
  have hhx: "h x \<in> H" using hh hx unfolding top1_group_hom_on_def by (by100 blast)
  have hhix: "h (invg x) \<in> H" using hh hix unfolding top1_group_hom_on_def by (by100 blast)
  have hinv_hx: "invgH (h x) \<in> H" by (rule group_inv_closed[OF hH hhx])
  \<comment> \<open>h(invg x) * h(x) = h(invg x * x) = h(e) = eH.\<close>
  have hmul_eq: "mulH (h (invg x)) (h x) = eH"
  proof -
    have "h (mul (invg x) x) = mulH (h (invg x)) (h x)"
      using hh hix hx unfolding top1_group_hom_on_def by (by100 blast)
    moreover have "mul (invg x) x = e" by (rule group_inv_left[OF hG hx])
    moreover have "h e = eH" by (rule hom_preserves_id[OF hG hH hh])
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Left inverse in a group is THE inverse: h(invg x) = invgH(h x).\<close>
  have "h (invg x) = mulH (h (invg x)) (mulH (h x) (invgH (h x)))"
    using group_inv_right[OF hH hhx] group_id_right[OF hH hhix] by (by100 simp)
  also have "\<dots> = mulH (mulH (h (invg x)) (h x)) (invgH (h x))"
    using group_assoc[OF hH hhix hhx hinv_hx] by (by100 simp)
  also have "mulH (h (invg x)) (h x) = eH" by (rule hmul_eq)
  also have "mulH eH (invgH (h x)) = invgH (h x)"
    by (rule group_id_left[OF hH hinv_hx])
  finally show ?thesis .
qed

lemma group_hom_comp:
  assumes hf: "top1_group_hom_on G1 mul1 G2 mul2 f"
      and hg: "top1_group_hom_on G2 mul2 G3 mul3 g"
  shows "top1_group_hom_on G1 mul1 G3 mul3 (g \<circ> f)"
  unfolding top1_group_hom_on_def
proof (intro conjI ballI)
  fix x assume "x \<in> G1"
  hence "f x \<in> G2" using hf unfolding top1_group_hom_on_def by (by100 blast)
  thus "(g \<circ> f) x \<in> G3" using hg unfolding top1_group_hom_on_def comp_def by (by100 blast)
next
  fix x y assume "x \<in> G1" "y \<in> G1"
  have "f x \<in> G2" "f y \<in> G2"
    using hf \<open>x \<in> G1\<close> \<open>y \<in> G1\<close> unfolding top1_group_hom_on_def by (by100 blast)+
  show "(g \<circ> f) (mul1 x y) = mul3 ((g \<circ> f) x) ((g \<circ> f) y)"
    using hf hg \<open>x \<in> G1\<close> \<open>y \<in> G1\<close> \<open>f x \<in> G2\<close> \<open>f y \<in> G2\<close>
    unfolding top1_group_hom_on_def comp_def by (by100 force)
qed

lemma group_hom_id:
  assumes hG: "top1_is_group_on G mul e invg"
  shows "top1_group_hom_on G mul G mul id"
  unfolding top1_group_hom_on_def id_def
  using hG unfolding top1_is_group_on_def by (by100 blast)

text \<open>Intersection of subgroups (with same operations from ambient G) is a subgroup.\<close>
lemma intersection_of_subgroups_is_group:
  assumes hG: "top1_is_group_on G mul e invg" and hS: "S \<subseteq> G"
  shows "top1_is_group_on (top1_subgroup_generated_on G mul e invg S) mul e invg"
proof -
  let ?I = "top1_subgroup_generated_on G mul e invg S"
  have hI_sub: "?I \<subseteq> G" by (rule subgroup_generated_subset[OF hG hS])
  show ?thesis unfolding top1_is_group_on_def
  proof (intro conjI ballI)
    \<comment> \<open>e \<in> ?I: e is in every subgroup containing S.\<close>
    show "e \<in> ?I" unfolding top1_subgroup_generated_on_def
    proof (rule InterI)
      fix H assume "H \<in> {H. S \<subseteq> H \<and> H \<subseteq> G \<and> top1_is_group_on H mul e invg}"
      hence "top1_is_group_on H mul e invg" by (by100 blast)
      thus "e \<in> H" by (rule group_e_mem)
    qed
  next
    fix x y assume hx: "x \<in> ?I" and hy: "y \<in> ?I"
    show "mul x y \<in> ?I" unfolding top1_subgroup_generated_on_def
    proof (rule InterI)
      fix H assume hH: "H \<in> {H. S \<subseteq> H \<and> H \<subseteq> G \<and> top1_is_group_on H mul e invg}"
      have "top1_is_group_on H mul e invg" using hH by (by100 blast)
      moreover have "x \<in> H"
        using hx hH unfolding top1_subgroup_generated_on_def by (by100 blast)
      moreover have "y \<in> H"
        using hy hH unfolding top1_subgroup_generated_on_def by (by100 blast)
      ultimately show "mul x y \<in> H" by (rule group_mul_closed)
    qed
  next
    fix x assume hx: "x \<in> ?I"
    show "invg x \<in> ?I" unfolding top1_subgroup_generated_on_def
    proof (rule InterI)
      fix H assume hH: "H \<in> {H. S \<subseteq> H \<and> H \<subseteq> G \<and> top1_is_group_on H mul e invg}"
      have "top1_is_group_on H mul e invg" using hH by (by100 blast)
      moreover have "x \<in> H"
        using hx hH unfolding top1_subgroup_generated_on_def by (by100 blast)
      ultimately show "invg x \<in> H" by (rule group_inv_closed)
    qed
  next
    fix x y z assume "x \<in> ?I" "y \<in> ?I" "z \<in> ?I"
    hence "x \<in> G" "y \<in> G" "z \<in> G" using hI_sub by (by100 blast)+
    thus "mul (mul x y) z = mul x (mul y z)" by (rule group_assoc[OF hG])
  next
    fix x assume "x \<in> ?I"
    hence "x \<in> G" using hI_sub by (by100 blast)
    show "mul e x = x" by (rule group_id_left[OF hG \<open>x \<in> G\<close>])
  next
    fix x assume "x \<in> ?I"
    hence "x \<in> G" using hI_sub by (by100 blast)
    show "mul x e = x" by (rule group_id_right[OF hG \<open>x \<in> G\<close>])
  next
    fix x assume "x \<in> ?I"
    hence "x \<in> G" using hI_sub by (by100 blast)
    show "mul (invg x) x = e" by (rule group_inv_left[OF hG \<open>x \<in> G\<close>])
  next
    fix x assume "x \<in> ?I"
    hence "x \<in> G" using hI_sub by (by100 blast)
    show "mul x (invg x) = e" by (rule group_inv_right[OF hG \<open>x \<in> G\<close>])
  qed
qed

text \<open>Conjugation by g is a homomorphism: g(xy)g\<inverse> = (gxg\<inverse>)(gyg\<inverse>).\<close>
lemma group_conjugate_mul:
  assumes hG: "top1_is_group_on G mul e invg" and hg: "g \<in> G" and hx: "x \<in> G" and hy: "y \<in> G"
  shows "mul (mul g (mul x y)) (invg g) = mul (mul (mul g x) (invg g)) (mul (mul g y) (invg g))"
proof -
  have hig: "invg g \<in> G" by (rule group_inv_closed[OF hG hg])
  have hgx: "mul g x \<in> G" by (rule group_mul_closed[OF hG hg hx])
  have hgy: "mul g y \<in> G" by (rule group_mul_closed[OF hG hg hy])
  have hxy: "mul x y \<in> G" by (rule group_mul_closed[OF hG hx hy])
  have hgxig: "mul (mul g x) (invg g) \<in> G" by (rule group_mul_closed[OF hG hgx hig])
  have hgyig: "mul (mul g y) (invg g) \<in> G" by (rule group_mul_closed[OF hG hgy hig])
  \<comment> \<open>RHS = (gxg\<inverse>)(gyg\<inverse>) = gx(g\<inverse>g)y g\<inverse> = gxyg\<inverse> = LHS.\<close>
  have "mul (mul (mul g x) (invg g)) (mul (mul g y) (invg g))
      = mul (mul g x) (mul (invg g) (mul (mul g y) (invg g)))"
    by (rule group_assoc[OF hG hgx hig hgyig])
  also have "mul (invg g) (mul (mul g y) (invg g)) = mul (mul (invg g) (mul g y)) (invg g)"
    using group_assoc[OF hG hig hgy hig] by (by100 simp)
  also have "mul (invg g) (mul g y) = mul (mul (invg g) g) y"
    using group_assoc[OF hG hig hg hy] by (by100 simp)
  also have "mul (invg g) g = e" by (rule group_inv_left[OF hG hg])
  also have "mul e y = y" by (rule group_id_left[OF hG hy])
  finally have rhs_simp: "mul (mul (mul g x) (invg g)) (mul (mul g y) (invg g))
      = mul (mul g x) (mul y (invg g))" by (by100 simp)
  have "mul (mul g (mul x y)) (invg g) = mul g (mul (mul x y) (invg g))"
    by (rule group_assoc[OF hG hg hxy hig])
  also have "mul (mul x y) (invg g) = mul x (mul y (invg g))"
    by (rule group_assoc[OF hG hx hy hig])
  finally have lhs_simp: "mul (mul g (mul x y)) (invg g) = mul g (mul x (mul y (invg g)))" .
  also have "mul g (mul x (mul y (invg g))) = mul (mul g x) (mul y (invg g))"
  proof -
    have "mul y (invg g) \<in> G" by (rule group_mul_closed[OF hG hy hig])
    thus ?thesis using group_assoc[OF hG hg hx \<open>mul y (invg g) \<in> G\<close>] by (by100 simp)
  qed
  finally show ?thesis using rhs_simp by (by100 simp)
qed

text \<open>Conjugation preserves inverses: g(x\<inverse>)g\<inverse> = (gxg\<inverse>)\<inverse>.\<close>
lemma group_conjugate_inv:
  assumes hG: "top1_is_group_on G mul e invg" and hg: "g \<in> G" and hx: "x \<in> G"
  shows "mul (mul g (invg x)) (invg g) = invg (mul (mul g x) (invg g))"
proof -
  have hig: "invg g \<in> G" by (rule group_inv_closed[OF hG hg])
  have hix: "invg x \<in> G" by (rule group_inv_closed[OF hG hx])
  have hgx: "mul g x \<in> G" by (rule group_mul_closed[OF hG hg hx])
  have hgxig: "mul (mul g x) (invg g) \<in> G" by (rule group_mul_closed[OF hG hgx hig])
  have hgix: "mul g (invg x) \<in> G" by (rule group_mul_closed[OF hG hg hix])
  have hgixig: "mul (mul g (invg x)) (invg g) \<in> G"
    by (rule group_mul_closed[OF hG hgix hig])
  \<comment> \<open>(gxg\<inverse>)(gx\<inverse>g\<inverse>) = g(x·x\<inverse>)g\<inverse> = g·e·g\<inverse> = g·g\<inverse> = e.\<close>
  let ?gxig = "mul (mul g x) (invg g)"
  let ?gixig = "mul (mul g (invg x)) (invg g)"
  have h1: "mul ?gxig ?gixig = e"
  proof -
    have "mul ?gxig ?gixig = mul (mul g (mul x (invg x))) (invg g)"
      using group_conjugate_mul[OF hG hg hx hix] by (by100 simp)
    also have "mul x (invg x) = e" by (rule group_inv_right[OF hG hx])
    hence "mul (mul g (mul x (invg x))) (invg g) = mul (mul g e) (invg g)" by (by100 simp)
    also have "mul g e = g" by (rule group_id_right[OF hG hg])
    hence "mul (mul g e) (invg g) = mul g (invg g)" by (by100 simp)
    also have "mul g (invg g) = e" by (rule group_inv_right[OF hG hg])
    finally show ?thesis by (by100 simp)
  qed
  have h2: "mul ?gixig ?gxig = e"
  proof -
    have "mul ?gixig ?gxig = mul (mul g (mul (invg x) x)) (invg g)"
      using group_conjugate_mul[OF hG hg hix hx] by (by100 simp)
    also have "mul (invg x) x = e" by (rule group_inv_left[OF hG hx])
    hence "mul (mul g (mul (invg x) x)) (invg g) = mul (mul g e) (invg g)" by (by100 simp)
    also have "mul g e = g" by (rule group_id_right[OF hG hg])
    hence "mul (mul g e) (invg g) = mul g (invg g)" by (by100 simp)
    also have "mul g (invg g) = e" by (rule group_inv_right[OF hG hg])
    finally show ?thesis by (by100 simp)
  qed
  \<comment> \<open>gx\<inverse>g\<inverse> is a two-sided inverse of gxg\<inverse>, hence equals invg(gxg\<inverse>).\<close>
  \<comment> \<open>gx\<inverse>g\<inverse> = gx\<inverse>g\<inverse> · e = gx\<inverse>g\<inverse> · (gxg\<inverse> · invg(gxg\<inverse>)) = (gx\<inverse>g\<inverse> · gxg\<inverse>) · invg(gxg\<inverse>) = e · invg(gxg\<inverse>) = invg(gxg\<inverse>).\<close>
  have hgixig_G: "?gixig \<in> G" by (rule group_mul_closed[OF hG hgix hig])
  have hgxig_G: "?gxig \<in> G" by (rule group_mul_closed[OF hG hgx hig])
  have higxig: "invg ?gxig \<in> G" by (rule group_inv_closed[OF hG hgxig_G])
  have "?gixig = mul ?gixig e" using group_id_right[OF hG hgixig_G] by (by100 simp)
  also have "mul ?gixig e = mul ?gixig (mul ?gxig (invg ?gxig))"
    using group_inv_right[OF hG hgxig_G] by (by100 simp)
  also have "\<dots> = mul (mul ?gixig ?gxig) (invg ?gxig)"
    using group_assoc[OF hG hgixig_G hgxig_G higxig] by (by100 simp)
  also have "mul ?gixig ?gxig = e" by (rule h2)
  also have "mul e (invg ?gxig) = invg ?gxig"
    by (rule group_id_left[OF hG higxig])
  finally show ?thesis by (by100 simp)
qed

text \<open>Commutator subgroup [G,G] is always normal. Key algebraic identity:
  g[a,b]g\<inverse> = [gag\<inverse>, gbg\<inverse>] (conjugate of commutator is commutator).\<close>

lemma commutator_conjugate:
  assumes hG: "top1_is_group_on G mul e invg"
      and "g \<in> G" "a \<in> G" "b \<in> G"
  shows "mul (mul g (top1_group_commutator_on mul invg a b)) (invg g) =
         top1_group_commutator_on mul invg (mul (mul g a) (invg g)) (mul (mul g b) (invg g))"
proof -
  have hig: "invg g \<in> G" by (rule group_inv_closed[OF hG assms(2)])
  have hia: "invg a \<in> G" by (rule group_inv_closed[OF hG assms(3)])
  have hib: "invg b \<in> G" by (rule group_inv_closed[OF hG assms(4)])
  have hab: "mul a b \<in> G" by (rule group_mul_closed[OF hG assms(3) assms(4)])
  have hiaib: "mul (invg a) (invg b) \<in> G" by (rule group_mul_closed[OF hG hia hib])
  let ?ga = "mul (mul g a) (invg g)" and ?gb = "mul (mul g b) (invg g)"
  \<comment> \<open>[a,b] = (a*b)*(a\<inverse>*b\<inverse>). So g[a,b]g\<inverse> = g((ab)(a\<inverse>b\<inverse>))g\<inverse>.\<close>
  have comm_split: "top1_group_commutator_on mul invg a b = mul (mul a b) (mul (invg a) (invg b))"
    unfolding top1_group_commutator_on_def
    using group_assoc[OF hG hab hia hib] by (by100 simp)
  have lhs: "mul (mul g (top1_group_commutator_on mul invg a b)) (invg g) =
      mul (mul (mul g (mul a b)) (invg g)) (mul (mul g (mul (invg a) (invg b))) (invg g))"
    unfolding comm_split by (rule group_conjugate_mul[OF hG assms(2) hab hiaib])
  \<comment> \<open>g(ab)g\<inverse> = (gag\<inverse>)(gbg\<inverse>).\<close>
  have s1: "mul (mul g (mul a b)) (invg g) = mul ?ga ?gb"
    by (rule group_conjugate_mul[OF hG assms(2) assms(3) assms(4)])
  \<comment> \<open>g(a\<inverse>b\<inverse>)g\<inverse> = (ga\<inverse>g\<inverse>)(gb\<inverse>g\<inverse>).\<close>
  have s2: "mul (mul g (mul (invg a) (invg b))) (invg g) =
      mul (mul (mul g (invg a)) (invg g)) (mul (mul g (invg b)) (invg g))"
    by (rule group_conjugate_mul[OF hG assms(2) hia hib])
  \<comment> \<open>ga\<inverse>g\<inverse> = invg(gag\<inverse>), gb\<inverse>g\<inverse> = invg(gbg\<inverse>).\<close>
  have s3: "mul (mul g (invg a)) (invg g) = invg ?ga"
    by (rule group_conjugate_inv[OF hG assms(2) assms(3)])
  have s4: "mul (mul g (invg b)) (invg g) = invg ?gb"
    by (rule group_conjugate_inv[OF hG assms(2) assms(4)])
  \<comment> \<open>RHS: [gag\<inverse>, gbg\<inverse>] = (gag\<inverse>)(gbg\<inverse>)(invg(gag\<inverse>))(invg(gbg\<inverse>))
       = (gag\<inverse>)(gbg\<inverse>) * (invg(gag\<inverse>))(invg(gbg\<inverse>)).\<close>
  have hga': "mul g a \<in> G" by (rule group_mul_closed[OF hG assms(2) assms(3)])
  have hga: "?ga \<in> G" by (rule group_mul_closed[OF hG hga' hig])
  have hgb': "mul g b \<in> G" by (rule group_mul_closed[OF hG assms(2) assms(4)])
  have hgb: "?gb \<in> G" by (rule group_mul_closed[OF hG hgb' hig])
  have higa: "invg ?ga \<in> G" by (rule group_inv_closed[OF hG hga])
  have higb: "invg ?gb \<in> G" by (rule group_inv_closed[OF hG hgb])
  have hgagb: "mul ?ga ?gb \<in> G" by (rule group_mul_closed[OF hG hga hgb])
  have rhs_split: "top1_group_commutator_on mul invg ?ga ?gb =
      mul (mul ?ga ?gb) (mul (invg ?ga) (invg ?gb))"
    unfolding top1_group_commutator_on_def
    using group_assoc[OF hG hgagb higa higb] by (by100 simp)
  show ?thesis using lhs s1 s2 s3 s4 rhs_split by (by100 simp)
qed

lemma commutator_subgroup_is_normal:
  assumes hG: "top1_is_group_on G mul e invg"
  shows "top1_normal_subgroup_on G mul e invg (top1_commutator_subgroup_on G mul e invg)"
  unfolding top1_normal_subgroup_on_def
proof (intro conjI)
  let ?comm = "top1_commutator_subgroup_on G mul e invg"
  let ?gens = "{ top1_group_commutator_on mul invg a b | a b. a \<in> G \<and> b \<in> G }"
  have hgens_sub: "?gens \<subseteq> G"
  proof (rule subsetI)
    fix x assume "x \<in> ?gens"
    then obtain a b where "a \<in> G" "b \<in> G" "x = top1_group_commutator_on mul invg a b"
      by (by100 blast)
    thus "x \<in> G" unfolding top1_group_commutator_on_def
      using hG unfolding top1_is_group_on_def by (by100 blast)
  qed
  show "?comm \<subseteq> G"
    unfolding top1_commutator_subgroup_on_def
    by (rule subgroup_generated_subset[OF hG hgens_sub])
  show "top1_is_group_on ?comm mul e invg"
    unfolding top1_commutator_subgroup_on_def
    by (rule intersection_of_subgroups_is_group[OF hG hgens_sub])
  show "\<forall>g\<in>G. \<forall>n\<in>?comm. mul (mul g n) (invg g) \<in> ?comm"
  proof (intro ballI)
    fix g n assume hg: "g \<in> G" and hn: "n \<in> ?comm"
    \<comment> \<open>K_g = {n \<in> G. gng\<inverse> \<in> [G,G]} contains commutators and is a subgroup.\<close>
    let ?Kg = "{n \<in> G. mul (mul g n) (invg g) \<in> ?comm}"
    have "?gens \<subseteq> ?Kg"
    proof (rule subsetI)
      fix x assume "x \<in> ?gens"
      then obtain a b where hab: "a \<in> G" "b \<in> G"
          and hx: "x = top1_group_commutator_on mul invg a b" by (by100 blast)
      have "x \<in> G" using hx hgens_sub \<open>x \<in> ?gens\<close> by (by100 blast)
      moreover have "mul (mul g x) (invg g) \<in> ?comm"
      proof -
        have "mul (mul g x) (invg g) =
            top1_group_commutator_on mul invg (mul (mul g a) (invg g)) (mul (mul g b) (invg g))"
          unfolding hx by (rule commutator_conjugate[OF hG hg hab])
        moreover have "mul (mul g a) (invg g) \<in> G"
          using hG hg hab unfolding top1_is_group_on_def by (by100 blast)
        moreover have "mul (mul g b) (invg g) \<in> G"
          using hG hg hab unfolding top1_is_group_on_def by (by100 blast)
        ultimately have "mul (mul g x) (invg g) \<in> ?gens" by (by100 blast)
        thus ?thesis unfolding top1_commutator_subgroup_on_def
          by (rule subgroup_generated_contains[OF hG hgens_sub])
      qed
      ultimately show "x \<in> ?Kg" by (by100 blast)
    qed
    moreover have "?Kg \<subseteq> G" by (by100 blast)
    moreover have "top1_is_group_on ?Kg mul e invg"
    proof -
      have hcomm_grp: "top1_is_group_on ?comm mul e invg"
        unfolding top1_commutator_subgroup_on_def
        by (rule intersection_of_subgroups_is_group[OF hG hgens_sub])
      show ?thesis unfolding top1_is_group_on_def
      proof (intro conjI ballI)
        \<comment> \<open>e \<in> K_g.\<close>
        show "e \<in> ?Kg"
        proof -
          have "e \<in> G" by (rule group_e_mem[OF hG])
          moreover have "mul (mul g e) (invg g) = e"
            using group_id_right[OF hG hg] group_inv_right[OF hG hg] by (by100 simp)
          hence "mul (mul g e) (invg g) \<in> ?comm"
            using group_e_mem[OF hcomm_grp] by (by100 simp)
          ultimately show ?thesis by (by100 blast)
        qed
      next
        fix n1 n2 assume hn1: "n1 \<in> ?Kg" and hn2: "n2 \<in> ?Kg"
        show "mul n1 n2 \<in> ?Kg"
        proof -
          have "n1 \<in> G" "n2 \<in> G" using hn1 hn2 by (by100 blast)+
          hence hmn: "mul n1 n2 \<in> G" by (rule group_mul_closed[OF hG])
          have c1: "mul (mul g n1) (invg g) \<in> ?comm" using hn1 by (by100 blast)
          have c2: "mul (mul g n2) (invg g) \<in> ?comm" using hn2 by (by100 blast)
          have "mul (mul g (mul n1 n2)) (invg g) =
              mul (mul (mul g n1) (invg g)) (mul (mul g n2) (invg g))"
            by (rule group_conjugate_mul[OF hG hg \<open>n1 \<in> G\<close> \<open>n2 \<in> G\<close>])
          hence "mul (mul g (mul n1 n2)) (invg g) \<in> ?comm"
            using group_mul_closed[OF hcomm_grp c1 c2] by (by100 simp)
          thus ?thesis using hmn by (by100 blast)
        qed
      next
        fix n assume hn: "n \<in> ?Kg"
        show "invg n \<in> ?Kg"
        proof -
          have "n \<in> G" using hn by (by100 blast)
          hence hin: "invg n \<in> G" by (rule group_inv_closed[OF hG])
          have cn: "mul (mul g n) (invg g) \<in> ?comm" using hn by (by100 blast)
          have "mul (mul g (invg n)) (invg g) = invg (mul (mul g n) (invg g))"
            by (rule group_conjugate_inv[OF hG hg \<open>n \<in> G\<close>])
          hence "mul (mul g (invg n)) (invg g) \<in> ?comm"
            using group_inv_closed[OF hcomm_grp cn] by (by100 simp)
          thus ?thesis using hin by (by100 blast)
        qed
      next
        fix n1 n2 n3 assume "n1 \<in> ?Kg" "n2 \<in> ?Kg" "n3 \<in> ?Kg"
        hence "n1 \<in> G" "n2 \<in> G" "n3 \<in> G" by (by100 blast)+
        thus "mul (mul n1 n2) n3 = mul n1 (mul n2 n3)" by (rule group_assoc[OF hG])
      next
        fix n assume "n \<in> ?Kg" hence "n \<in> G" by (by100 blast)
        show "mul e n = n" by (rule group_id_left[OF hG \<open>n \<in> G\<close>])
      next
        fix n assume "n \<in> ?Kg" hence "n \<in> G" by (by100 blast)
        show "mul n e = n" by (rule group_id_right[OF hG \<open>n \<in> G\<close>])
      next
        fix n assume "n \<in> ?Kg" hence "n \<in> G" by (by100 blast)
        show "mul (invg n) n = e" by (rule group_inv_left[OF hG \<open>n \<in> G\<close>])
      next
        fix n assume "n \<in> ?Kg" hence "n \<in> G" by (by100 blast)
        show "mul n (invg n) = e" by (rule group_inv_right[OF hG \<open>n \<in> G\<close>])
      qed
    qed
    ultimately have "?comm \<subseteq> ?Kg"
      unfolding top1_commutator_subgroup_on_def
      by (rule subgroup_generated_minimal)
    thus "mul (mul g n) (invg g) \<in> ?comm" using hn by (by100 blast)
  qed
qed

text \<open>Lemma 68.9 (Munkres): The least normal subgroup of G containing S equals the subgroup
  generated by all conjugates gsg^{-1} for g \<in> G, s \<in> S.\<close>
lemma Lemma_68_9_normal_closure_conjugates:
  assumes hG: "top1_is_group_on G mul e invg" and hS: "S \<subseteq> G"
  shows "top1_normal_subgroup_generated_on G mul e invg S =
    top1_subgroup_generated_on G mul e invg { mul (mul g s) (invg g) | g s. g \<in> G \<and> s \<in> S }"
proof -
  let ?conj = "{ mul (mul g s) (invg g) | g s. g \<in> G \<and> s \<in> S }"
  let ?N = "top1_normal_subgroup_generated_on G mul e invg S"
  let ?Np = "top1_subgroup_generated_on G mul e invg ?conj"
  \<comment> \<open>Step 1: ?conj \<subseteq> G.\<close>
  have hconj_sub: "?conj \<subseteq> G"
  proof (rule subsetI)
    fix x assume "x \<in> ?conj"
    then obtain g s where "g \<in> G" "s \<in> S" "x = mul (mul g s) (invg g)" by (by100 blast)
    thus "x \<in> G" using hS hG unfolding top1_is_group_on_def by (by100 blast)
  qed
  \<comment> \<open>Step 2: N' \<subseteq> N (all conjugates are in any normal subgroup containing S).\<close>
  have hNp_sub_N: "?Np \<subseteq> ?N"
  proof -
    \<comment> \<open>Every conjugate gsg^{-1} is in every normal subgroup containing S.\<close>
    have "?conj \<subseteq> ?N"
    proof (rule subsetI)
      fix x assume "x \<in> ?conj"
      then obtain g s where hg: "g \<in> G" and hs: "s \<in> S" and hx: "x = mul (mul g s) (invg g)"
        by (by100 blast)
      \<comment> \<open>For any normal subgroup M containing S: s \<in> M, so gsg^{-1} \<in> M (normality).\<close>
      have "\<forall>M. S \<subseteq> M \<and> top1_normal_subgroup_on G mul e invg M \<longrightarrow> x \<in> M"
      proof (intro allI impI)
        fix M assume "S \<subseteq> M \<and> top1_normal_subgroup_on G mul e invg M"
        hence "s \<in> M" and "top1_normal_subgroup_on G mul e invg M" using hs by (by100 blast)+
        thus "x \<in> M" using hg hx unfolding top1_normal_subgroup_on_def by (by100 blast)
      qed
      thus "x \<in> ?N" unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
    qed
    \<comment> \<open>?N is a normal subgroup containing S, and ?conj \<subseteq> ?N, so ?Np \<subseteq> ?N.\<close>
    moreover have "?N \<subseteq> G"
    proof -
      \<comment> \<open>G is a normal subgroup of G containing S, so it's in the intersection.\<close>
      have "top1_normal_subgroup_on G mul e invg G"
        unfolding top1_normal_subgroup_on_def
        using hG group_mul_closed[OF hG] group_inv_closed[OF hG] by (by100 blast)
      hence "G \<in> { N. S \<subseteq> N \<and> top1_normal_subgroup_on G mul e invg N }" using hS by (by100 blast)
      thus ?thesis unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
    qed
    moreover have "top1_is_group_on ?N mul e invg"
    proof -
      \<comment> \<open>Intersection of subgroups is a subgroup. Each normal subgroup is a subgroup.\<close>
      have "\<And>N. S \<subseteq> N \<Longrightarrow> top1_normal_subgroup_on G mul e invg N \<Longrightarrow>
          top1_is_group_on N mul e invg"
        unfolding top1_normal_subgroup_on_def by (by100 blast)
      \<comment> \<open>The normal closure = \<Inter>{N. S\<subseteq>N \<and> normal N}. Every such N is a subgroup.
         G is one such N (with S \<subseteq> G). So the intersection is non-empty and a group.\<close>
      let ?F = "{ N. S \<subseteq> N \<and> top1_normal_subgroup_on G mul e invg N }"
      have hG_in: "G \<in> ?F"
      proof -
        have "top1_normal_subgroup_on G mul e invg G"
          unfolding top1_normal_subgroup_on_def
          using hG group_mul_closed[OF hG] group_inv_closed[OF hG] by (by100 blast)
        thus ?thesis using hS by (by100 blast)
      qed
      show ?thesis unfolding top1_normal_subgroup_generated_on_def top1_is_group_on_def
      proof (intro conjI ballI)
        show "e \<in> \<Inter>?F"
        proof (rule InterI)
          fix N assume "N \<in> ?F"
          hence "top1_is_group_on N mul e invg"
            unfolding top1_normal_subgroup_on_def by (by100 blast)
          thus "e \<in> N" by (rule group_e_mem)
        qed
      next
        fix x y assume hx: "x \<in> \<Inter>?F" and hy: "y \<in> \<Inter>?F"
        show "mul x y \<in> \<Inter>?F"
        proof (rule InterI)
          fix N assume hN: "N \<in> ?F"
          hence hN_grp: "top1_is_group_on N mul e invg"
            unfolding top1_normal_subgroup_on_def by (by100 blast)
          have "x \<in> N" "y \<in> N" using hx hy hN by (by100 blast)+
          thus "mul x y \<in> N" by (rule group_mul_closed[OF hN_grp])
        qed
      next
        fix x assume hx: "x \<in> \<Inter>?F"
        show "invg x \<in> \<Inter>?F"
        proof (rule InterI)
          fix N assume hN: "N \<in> ?F"
          hence hN_grp: "top1_is_group_on N mul e invg"
            unfolding top1_normal_subgroup_on_def by (by100 blast)
          have "x \<in> N" using hx hN by (by100 blast)
          thus "invg x \<in> N" by (rule group_inv_closed[OF hN_grp])
        qed
      next
        fix x y z assume "x \<in> \<Inter>?F" "y \<in> \<Inter>?F" "z \<in> \<Inter>?F"
        hence "x \<in> G" "y \<in> G" "z \<in> G" using hG_in by (by100 blast)+
        thus "mul (mul x y) z = mul x (mul y z)" by (rule group_assoc[OF hG])
      next
        fix x assume "x \<in> \<Inter>?F"
        hence "x \<in> G" using hG_in by (by100 blast)
        thus "mul e x = x" by (rule group_id_left[OF hG])
      next
        fix x assume "x \<in> \<Inter>?F"
        hence "x \<in> G" using hG_in by (by100 blast)
        thus "mul x e = x" by (rule group_id_right[OF hG])
      next
        fix x assume "x \<in> \<Inter>?F"
        hence "x \<in> G" using hG_in by (by100 blast)
        thus "mul (invg x) x = e" by (rule group_inv_left[OF hG])
      next
        fix x assume "x \<in> \<Inter>?F"
        hence "x \<in> G" using hG_in by (by100 blast)
        thus "mul x (invg x) = e" by (rule group_inv_right[OF hG])
      qed
    qed
    ultimately show ?thesis
      by (rule subgroup_generated_minimal)
  qed
  \<comment> \<open>Step 3: N' is normal (conjugating a product of conjugates gives a product of conjugates).\<close>
  have hNp_normal: "top1_normal_subgroup_on G mul e invg ?Np"
    unfolding top1_normal_subgroup_on_def
  proof (intro conjI)
    show "?Np \<subseteq> G" by (rule subgroup_generated_subset[OF hG hconj_sub])
    show "top1_is_group_on ?Np mul e invg" by (rule intersection_of_subgroups_is_group[OF hG hconj_sub])
    show "\<forall>g\<in>G. \<forall>n\<in>?Np. mul (mul g n) (invg g) \<in> ?Np"
    proof (intro ballI)
      fix g n assume hg: "g \<in> G" and hn: "n \<in> ?Np"
      \<comment> \<open>K_g = {n \<in> G. gng^{-1} \<in> N'} contains conjugates and is a subgroup.\<close>
      let ?Kg = "{n \<in> G. mul (mul g n) (invg g) \<in> ?Np}"
      have "?conj \<subseteq> ?Kg"
      proof (rule subsetI)
        fix x assume "x \<in> ?conj"
        then obtain g0 s where hg0: "g0 \<in> G" and hs: "s \<in> S" and hx: "x = mul (mul g0 s) (invg g0)"
          by (by100 blast)
        have "x \<in> G" using hconj_sub \<open>x \<in> ?conj\<close> by (by100 blast)
        \<comment> \<open>g(g0 s g0^{-1})g^{-1} = (g*g0) s (g*g0)^{-1}, which is a conjugate of s.\<close>
        have "mul (mul g x) (invg g) \<in> ?conj"
        proof -
          have hgg0: "mul g g0 \<in> G" by (rule group_mul_closed[OF hG hg hg0])
          \<comment> \<open>g * (g0*s*g0^{-1}) * g^{-1} = (g*g0) * s * (g*g0)^{-1} by assoc + inv_mul.\<close>
          have hsG: "s \<in> G" using hs hS by (by100 blast)
          have hig0: "invg g0 \<in> G" by (rule group_inv_closed[OF hG hg0])
          have hig: "invg g \<in> G" by (rule group_inv_closed[OF hG hg])
          have hg0s: "mul g0 s \<in> G" by (rule group_mul_closed[OF hG hg0 hsG])
          \<comment> \<open>Step a: g*x = g*(g0*s*g0^{-1}) = (g*g0*s)*g0^{-1} (by assoc).\<close>
          have "mul g x = mul g (mul (mul g0 s) (invg g0))" using hx by (by100 simp)
          also have "\<dots> = mul (mul g (mul g0 s)) (invg g0)"
            using group_assoc[OF hG hg hg0s hig0] by (by100 simp)
          also have "mul g (mul g0 s) = mul (mul g g0) s"
            using group_assoc[OF hG hg hg0 hsG] by (by100 simp)
          finally have hgx: "mul g x = mul (mul (mul g g0) s) (invg g0)" by (by100 simp)
          \<comment> \<open>Step b: (g*x)*g^{-1} = ((g*g0)*s*g0^{-1})*g^{-1} = (g*g0)*s*(g0^{-1}*g^{-1}).\<close>
          have "mul (mul g x) (invg g) = mul (mul (mul (mul g g0) s) (invg g0)) (invg g)"
            using hgx by (by100 simp)
          also have "\<dots> = mul (mul (mul g g0) s) (mul (invg g0) (invg g))"
          proof -
            have "mul (mul g g0) s \<in> G" by (rule group_mul_closed[OF hG hgg0 hsG])
            thus ?thesis by (rule group_assoc[OF hG _ hig0 hig])
          qed
          \<comment> \<open>Step c: g0^{-1}*g^{-1} = (g*g0)^{-1} (by inv_mul).\<close>
          also have "mul (invg g0) (invg g) = invg (mul g g0)"
            using group_inv_mul[OF hG hg hg0] by (by100 simp)
          finally have "mul (mul g x) (invg g) = mul (mul (mul g g0) s) (invg (mul g g0))" .
          moreover have "mul g g0 \<in> G" by (rule hgg0)
          ultimately show ?thesis using hs by (by100 blast)
        qed
        hence "mul (mul g x) (invg g) \<in> ?Np"
          by (rule subgroup_generated_contains[OF hG hconj_sub])
        thus "x \<in> ?Kg" using \<open>x \<in> G\<close> by (by100 blast)
      qed
      moreover have "?Kg \<subseteq> G" by (by100 blast)
      moreover have "top1_is_group_on ?Kg mul e invg"
      proof -
        have hNp_grp: "top1_is_group_on ?Np mul e invg"
          by (rule intersection_of_subgroups_is_group[OF hG hconj_sub])
        show ?thesis unfolding top1_is_group_on_def
        proof (intro conjI ballI)
          show "e \<in> ?Kg"
          proof -
            have "e \<in> G" by (rule group_e_mem[OF hG])
            moreover have "mul (mul g e) (invg g) = e"
              using group_id_right[OF hG hg] group_inv_right[OF hG hg] by (by100 simp)
            hence "mul (mul g e) (invg g) \<in> ?Np"
              using group_e_mem[OF hNp_grp] by (by100 simp)
            ultimately show ?thesis by (by100 blast)
          qed
        next
          fix n1 n2 assume "n1 \<in> ?Kg" "n2 \<in> ?Kg"
          hence hn1: "n1 \<in> G" "mul (mul g n1) (invg g) \<in> ?Np"
            and hn2: "n2 \<in> G" "mul (mul g n2) (invg g) \<in> ?Np" by (by100 blast)+
          have "mul (mul g (mul n1 n2)) (invg g) = mul (mul (mul g n1) (invg g)) (mul (mul g n2) (invg g))"
            by (rule group_conjugate_mul[OF hG hg hn1(1) hn2(1)])
          hence "mul (mul g (mul n1 n2)) (invg g) \<in> ?Np"
            using group_mul_closed[OF hNp_grp hn1(2) hn2(2)] by (by100 simp)
          moreover have "mul n1 n2 \<in> G" by (rule group_mul_closed[OF hG hn1(1) hn2(1)])
          ultimately show "mul n1 n2 \<in> ?Kg" by (by100 blast)
        next
          fix n assume "n \<in> ?Kg"
          hence hnG: "n \<in> G" and hconj_n: "mul (mul g n) (invg g) \<in> ?Np" by (by100 blast)+
          have "mul (mul g (invg n)) (invg g) = invg (mul (mul g n) (invg g))"
            by (rule group_conjugate_inv[OF hG hg hnG])
          hence "mul (mul g (invg n)) (invg g) \<in> ?Np"
            using group_inv_closed[OF hNp_grp hconj_n] by (by100 simp)
          moreover have "invg n \<in> G" by (rule group_inv_closed[OF hG hnG])
          ultimately show "invg n \<in> ?Kg" by (by100 blast)
        next
          fix n1 n2 n3 assume "n1 \<in> ?Kg" "n2 \<in> ?Kg" "n3 \<in> ?Kg"
          thus "mul (mul n1 n2) n3 = mul n1 (mul n2 n3)"
            using group_assoc[OF hG] by (by100 blast)
        next
          fix n assume "n \<in> ?Kg" thus "mul e n = n" using group_id_left[OF hG] by (by100 blast)
        next
          fix n assume "n \<in> ?Kg" thus "mul n e = n" using group_id_right[OF hG] by (by100 blast)
        next
          fix n assume "n \<in> ?Kg" thus "mul (invg n) n = e" using group_inv_left[OF hG] by (by100 blast)
        next
          fix n assume "n \<in> ?Kg" thus "mul n (invg n) = e" using group_inv_right[OF hG] by (by100 blast)
        qed
      qed
      ultimately have "?Np \<subseteq> ?Kg"
        by (rule subgroup_generated_minimal)
      thus "mul (mul g n) (invg g) \<in> ?Np" using hn by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 4: S \<subseteq> N' (s = e*s*e^{-1} is a conjugate).\<close>
  have hS_sub_Np: "S \<subseteq> ?Np"
  proof (rule subsetI)
    fix s assume hs: "s \<in> S"
    hence hsG: "s \<in> G" using hS by (by100 blast)
    have he: "e \<in> G" by (rule group_e_mem[OF hG])
    have "mul (mul e s) (invg e) = s"
    proof -
      have "mul e s = s" by (rule group_id_left[OF hG hsG])
      have hinve: "invg e \<in> G" by (rule group_inv_closed[OF hG he])
      have "invg e = e"
      proof -
        have "mul (invg e) e = e" by (rule group_inv_left[OF hG he])
        moreover have "mul (invg e) e = invg e" by (rule group_id_right[OF hG hinve])
        ultimately show ?thesis by (by100 simp)
      qed
      have "mul (mul e s) (invg e) = mul s e"
        using \<open>mul e s = s\<close> \<open>invg e = e\<close> by (by100 simp)
      also have "\<dots> = s" by (rule group_id_right[OF hG hsG])
      finally show ?thesis .
    qed
    hence "s = mul (mul e s) (invg e)" by (by100 simp)
    hence "s \<in> ?conj" using he hs by (by100 force)
    thus "s \<in> ?Np" by (rule subgroup_generated_contains[OF hG hconj_sub])
  qed
  \<comment> \<open>Step 5: N \<subseteq> N' (by minimality of N, since N' is normal and contains S).\<close>
  have hN_sub_Np: "?N \<subseteq> ?Np"
  proof -
    \<comment> \<open>N' is a normal subgroup containing S, so it's one of the sets being intersected.\<close>
    have "S \<subseteq> ?Np \<and> top1_normal_subgroup_on G mul e invg ?Np"
      using hS_sub_Np hNp_normal by (by100 blast)
    hence "?Np \<in> { N. S \<subseteq> N \<and> top1_normal_subgroup_on G mul e invg N }" by (by100 blast)
    thus ?thesis unfolding top1_normal_subgroup_generated_on_def by (rule Inter_lower)
  qed
  show ?thesis using hNp_sub_N hN_sub_Np by (by100 blast)
qed

text \<open>Lemma 69.3 part 3 (Munkres): If h: G \<rightarrow> H is a homomorphism to an abelian group H,
  then ker(h) contains [G,G]. Proof: every commutator [a,b] maps to
  h(a)*h(b)*h(a)^{-1}*h(b)^{-1} = eH (since H is abelian). Then [G,G] \<subseteq> ker(h)
  by subgroup_generated_minimal.\<close>
lemma Lemma_69_3_commutator_in_kernel:
  assumes hG: "top1_is_group_on G mul e invg"
      and hH: "top1_is_abelian_group_on H mulH eH invgH"
      and hh: "top1_group_hom_on G mul H mulH h"
  shows "top1_commutator_subgroup_on G mul e invg
      \<subseteq> top1_group_kernel_on G eH h"
proof -
  have hH_grp: "top1_is_group_on H mulH eH invgH"
    using hH unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hH_comm: "\<forall>x\<in>H. \<forall>y\<in>H. mulH x y = mulH y x"
    using hH unfolding top1_is_abelian_group_on_def by (by100 blast)
  let ?gens = "{ top1_group_commutator_on mul invg a b | a b. a \<in> G \<and> b \<in> G }"
  let ?K = "top1_group_kernel_on G eH h"
  have hgens_sub: "?gens \<subseteq> G"
  proof (rule subsetI)
    fix x assume "x \<in> ?gens"
    then obtain a b where "a \<in> G" "b \<in> G" "x = top1_group_commutator_on mul invg a b"
      by (by100 blast)
    thus "x \<in> G" unfolding top1_group_commutator_on_def
      using hG unfolding top1_is_group_on_def by (by100 blast)
  qed
  \<comment> \<open>Step 1: every commutator maps to eH under h.\<close>
  have hgens_ker: "?gens \<subseteq> ?K"
  proof (rule subsetI)
    fix x assume hx_gen: "x \<in> ?gens"
    then obtain a b where hab: "a \<in> G" "b \<in> G"
        and hx: "x = top1_group_commutator_on mul invg a b" by (by100 blast)
    have ha: "h a \<in> H" and hb: "h b \<in> H"
      using hh hab unfolding top1_group_hom_on_def by (by100 blast)+
    have hia: "invg a \<in> G" and hib: "invg b \<in> G"
      using group_inv_closed[OF hG hab(1)] group_inv_closed[OF hG hab(2)] by (by100 blast)+
    have hab_G: "mul a b \<in> G" by (rule group_mul_closed[OF hG hab(1) hab(2)])
    have habia: "mul (mul a b) (invg a) \<in> G" by (rule group_mul_closed[OF hG hab_G hia])
    \<comment> \<open>h([a,b]) = h(a)*h(b)*invgH(h(a))*invgH(h(b)).\<close>
    have hx_eq: "x = mul (mul (mul a b) (invg a)) (invg b)"
      using hx unfolding top1_group_commutator_on_def by (by100 simp)
    have hhab: "h (mul a b) = mulH (h a) (h b)"
    proof -
      have "h (mul a b) = mulH (h a) (h b)"
        using hh hab unfolding top1_group_hom_on_def by (by100 blast)
      thus ?thesis .
    qed
    have hhabia: "h (mul (mul a b) (invg a)) = mulH (h (mul a b)) (h (invg a))"
    proof -
      have "h (mul (mul a b) (invg a)) = mulH (h (mul a b)) (h (invg a))"
        using hh hab_G hia unfolding top1_group_hom_on_def by (by100 blast)
      thus ?thesis .
    qed
    have hhx: "h x = mulH (h (mul (mul a b) (invg a))) (h (invg b))"
    proof -
      have "h (mul (mul (mul a b) (invg a)) (invg b))
          = mulH (h (mul (mul a b) (invg a))) (h (invg b))"
        using hh habia hib unfolding top1_group_hom_on_def by (by100 blast)
      thus ?thesis using hx_eq by (by100 simp)
    qed
    have hhinva: "h (invg a) = invgH (h a)" by (rule hom_preserves_inv[OF hG hH_grp hh hab(1)])
    have hhinvb: "h (invg b) = invgH (h b)" by (rule hom_preserves_inv[OF hG hH_grp hh hab(2)])
    \<comment> \<open>Combine: h(x) = mulH (mulH (mulH (h a) (h b)) (invgH (h a))) (invgH (h b)).\<close>
    have hhx_expanded: "h x = mulH (mulH (mulH (h a) (h b)) (invgH (h a))) (invgH (h b))"
      using hhx hhabia hhab hhinva hhinvb by (by100 simp)
    \<comment> \<open>Abelian cancellation: h(a)*h(b) = h(b)*h(a), so (h(b)*h(a))*invgH(h(a)) = h(b),
       then h(b)*invgH(h(b)) = eH.\<close>
    have hinv_ha: "invgH (h a) \<in> H" by (rule group_inv_closed[OF hH_grp ha])
    have hinv_hb: "invgH (h b) \<in> H" by (rule group_inv_closed[OF hH_grp hb])
    have hcomm_ab: "mulH (h a) (h b) = mulH (h b) (h a)" using hH_comm ha hb by (by100 blast)
    have hstep1: "mulH (mulH (h a) (h b)) (invgH (h a)) = h b"
    proof -
      have "mulH (mulH (h a) (h b)) (invgH (h a)) = mulH (mulH (h b) (h a)) (invgH (h a))"
        using hcomm_ab by (by100 simp)
      also have "\<dots> = mulH (h b) (mulH (h a) (invgH (h a)))"
        by (rule group_assoc[OF hH_grp hb ha hinv_ha])
      also have "mulH (h a) (invgH (h a)) = eH"
        by (rule group_inv_right[OF hH_grp ha])
      also have "mulH (h b) eH = h b"
        by (rule group_id_right[OF hH_grp hb])
      finally show ?thesis .
    qed
    have hhx_hb: "h x = mulH (h b) (invgH (h b))"
      using hhx_expanded hstep1 by (by100 simp)
    have hb_inv_eH: "mulH (h b) (invgH (h b)) = eH"
      by (rule group_inv_right[OF hH_grp hb])
    have hhx_eH: "h x = eH" using hhx_hb hb_inv_eH by (by100 simp)
    have hxG: "x \<in> G" using hgens_sub hx_gen by (by100 blast)
    show "x \<in> ?K" unfolding top1_group_kernel_on_def
      using hhx_eH hxG by (by100 blast)
  qed
  \<comment> \<open>Step 2: ker(h) is a subgroup of G, and gens \<subseteq> G.\<close>
  have hK_sub: "?K \<subseteq> G"
    unfolding top1_group_kernel_on_def by (by100 blast)
  have hK_grp: "top1_is_group_on ?K mul e invg"
    unfolding top1_is_group_on_def top1_group_kernel_on_def
  proof (intro conjI ballI)
    \<comment> \<open>e \<in> ker: h(e) = eH.\<close>
    show "e \<in> {x \<in> G. h x = eH}"
      using group_e_mem[OF hG] hom_preserves_id[OF hG hH_grp hh] by (by100 blast)
  next
    fix x y assume hxK: "x \<in> {x \<in> G. h x = eH}" and hyK: "y \<in> {x \<in> G. h x = eH}"
    hence hxG: "x \<in> G" and hyG: "y \<in> G" and hhx: "h x = eH" and hhy: "h y = eH"
      by (by100 blast)+
    have "h (mul x y) = mulH (h x) (h y)"
      using hh hxG hyG unfolding top1_group_hom_on_def by (by100 blast)
    also have "\<dots> = mulH eH eH" using hhx hhy by (by100 simp)
    also have "\<dots> = eH"
    proof -
      have "eH \<in> H" by (rule group_e_mem[OF hH_grp])
      thus ?thesis by (rule group_id_left[OF hH_grp])
    qed
    finally show "mul x y \<in> {x \<in> G. h x = eH}"
      using group_mul_closed[OF hG hxG hyG] by (by100 blast)
  next
    fix x assume hxK: "x \<in> {x \<in> G. h x = eH}"
    hence hxG: "x \<in> G" and hhx: "h x = eH" by (by100 blast)+
    have "h (invg x) = invgH (h x)" by (rule hom_preserves_inv[OF hG hH_grp hh hxG])
    also have "\<dots> = invgH eH" using hhx by (by100 simp)
    also have "\<dots> = eH"
    proof -
      have heH: "eH \<in> H" by (rule group_e_mem[OF hH_grp])
      have hinveH: "invgH eH \<in> H" by (rule group_inv_closed[OF hH_grp heH])
      have "mulH (invgH eH) eH = eH" by (rule group_inv_left[OF hH_grp heH])
      moreover have "mulH (invgH eH) eH = invgH eH" by (rule group_id_right[OF hH_grp hinveH])
      ultimately show ?thesis by (by100 simp)
    qed
    finally show "invg x \<in> {x \<in> G. h x = eH}"
      using group_inv_closed[OF hG hxG] by (by100 blast)
  next
    fix x y z assume "x \<in> {x \<in> G. h x = eH}" "y \<in> {x \<in> G. h x = eH}" "z \<in> {x \<in> G. h x = eH}"
    thus "mul (mul x y) z = mul x (mul y z)"
      using group_assoc[OF hG] by (by100 blast)
  next
    fix x assume "x \<in> {x \<in> G. h x = eH}"
    thus "mul e x = x" using group_id_left[OF hG] by (by100 blast)
  next
    fix x assume "x \<in> {x \<in> G. h x = eH}"
    thus "mul x e = x" using group_id_right[OF hG] by (by100 blast)
  next
    fix x assume "x \<in> {x \<in> G. h x = eH}"
    thus "mul (invg x) x = e" using group_inv_left[OF hG] by (by100 blast)
  next
    fix x assume "x \<in> {x \<in> G. h x = eH}"
    thus "mul x (invg x) = e" using group_inv_right[OF hG] by (by100 blast)
  qed
  show ?thesis unfolding top1_commutator_subgroup_on_def
    by (rule subgroup_generated_minimal[OF hgens_ker hK_sub hK_grp])
qed

text \<open>Quotient group infrastructure: coset membership, normality, and the natural projection.\<close>

lemma coset_self_mem:
  assumes hG: "top1_is_group_on G mul e invg" and hN: "N \<subseteq> G"
      and hN_grp: "top1_is_group_on N mul e invg" and hg: "g \<in> G"
  shows "g \<in> top1_group_coset_on G mul N g"
proof -
  have "e \<in> N" by (rule group_e_mem[OF hN_grp])
  hence "mul g e \<in> {mul g n | n. n \<in> N}" by (by100 blast)
  moreover have "mul g e = g" by (rule group_id_right[OF hG hg])
  ultimately show ?thesis unfolding top1_group_coset_on_def by (by100 simp)
qed

lemma coset_e_is_N:
  assumes hG: "top1_is_group_on G mul e invg" and hN: "N \<subseteq> G"
      and hN_grp: "top1_is_group_on N mul e invg"
  shows "top1_group_coset_on G mul N e = N"
proof (rule set_eqI)
  fix x show "x \<in> top1_group_coset_on G mul N e \<longleftrightarrow> x \<in> N"
  proof
    assume "x \<in> top1_group_coset_on G mul N e"
    then obtain n where hn: "n \<in> N" and hx: "x = mul e n"
      unfolding top1_group_coset_on_def by (by100 blast)
    have "n \<in> G" using hn hN by (by100 blast)
    hence "mul e n = n" by (rule group_id_left[OF hG])
    thus "x \<in> N" using hx hn by (by100 simp)
  next
    assume "x \<in> N"
    hence "mul e x \<in> {mul e n | n. n \<in> N}" by (by100 blast)
    have "x \<in> G" using \<open>x \<in> N\<close> hN by (by100 blast)
    hence "mul e x = x" by (rule group_id_left[OF hG])
    thus "x \<in> top1_group_coset_on G mul N e"
      unfolding top1_group_coset_on_def using \<open>x \<in> N\<close> by (by100 force)
  qed
qed

lemma normal_coset_eq:
  assumes hG: "top1_is_group_on G mul e invg"
      and hN: "top1_normal_subgroup_on G mul e invg N"
      and hg: "g \<in> G" and hh: "h \<in> G"
  shows "top1_group_coset_on G mul N g = top1_group_coset_on G mul N h
         \<longleftrightarrow> mul (invg g) h \<in> N"
proof -
  let ?gN = "top1_group_coset_on G mul N g"
  let ?hN = "top1_group_coset_on G mul N h"
  have hNsub: "N \<subseteq> G" using hN unfolding top1_normal_subgroup_on_def by (by100 blast)
  have hN_grp: "top1_is_group_on N mul e invg"
    using hN unfolding top1_normal_subgroup_on_def by (by100 blast)
  have hN_conj: "\<And>g0 n0. g0 \<in> G \<Longrightarrow> n0 \<in> N \<Longrightarrow> mul (mul g0 n0) (invg g0) \<in> N"
    using hN unfolding top1_normal_subgroup_on_def by (by100 blast)
  have hinvg: "invg g \<in> G" by (rule group_inv_closed[OF hG hg])
  show ?thesis
  proof
    \<comment> \<open>(\<Rightarrow>): gN = hN implies g \<in> hN, so g = mul h n for some n \<in> N.
       Then invg(g) * h = invg(h * n) * h = invg(n) * invg(h) * h = invg(n) \<in> N.\<close>
    assume heq: "?gN = ?hN"
    have "g \<in> ?gN" by (rule coset_self_mem[OF hG hNsub hN_grp hg])
    hence "g \<in> ?hN" using heq by (by100 simp)
    then obtain n where hn: "n \<in> N" and hg_eq: "g = mul h n"
      unfolding top1_group_coset_on_def by (by100 blast)
    have hnG: "n \<in> G" using hn hNsub by (by100 blast)
    have "invg g = invg (mul h n)" using hg_eq by (by100 simp)
    also have "\<dots> = mul (invg n) (invg h)" by (rule group_inv_mul[OF hG hh hnG])
    finally have hinvg_eq: "invg g = mul (invg n) (invg h)" .
    have "mul (invg g) h = mul (mul (invg n) (invg h)) h"
      using hinvg_eq by (by100 simp)
    also have "\<dots> = mul (invg n) (mul (invg h) h)"
    proof -
      have "invg n \<in> G" by (rule group_inv_closed[OF hG hnG])
      have "invg h \<in> G" by (rule group_inv_closed[OF hG hh])
      show ?thesis by (rule group_assoc[OF hG \<open>invg n \<in> G\<close> \<open>invg h \<in> G\<close> hh])
    qed
    also have "mul (invg h) h = e" by (rule group_inv_left[OF hG hh])
    also have "mul (invg n) e = invg n"
    proof -
      have "invg n \<in> G" by (rule group_inv_closed[OF hG hnG])
      show ?thesis by (rule group_id_right[OF hG \<open>invg n \<in> G\<close>])
    qed
    finally have "mul (invg g) h = invg n" .
    moreover have "invg n \<in> N" by (rule group_inv_closed[OF hN_grp hn])
    ultimately show "mul (invg g) h \<in> N" by (by100 simp)
  next
    \<comment> \<open>(\<Leftarrow>): invg(g) * h \<in> N implies gN = hN via set equality.\<close>
    assume hmem: "mul (invg g) h \<in> N"
    show "?gN = ?hN"
    proof (rule set_eqI)
      fix x show "x \<in> ?gN \<longleftrightarrow> x \<in> ?hN"
      proof
        assume "x \<in> ?gN"
        then obtain n1 where hn1: "n1 \<in> N" and hx: "x = mul g n1"
          unfolding top1_group_coset_on_def by (by100 blast)
        have hn1G: "n1 \<in> G" using hn1 hNsub by (by100 blast)
        \<comment> \<open>x = g * n1 = h * (invg(h) * g) * n1.
           invg(h) * g = invg(invg(g) * h) ... use normality.\<close>
        \<comment> \<open>g = h * (invg h * g). And invg h * g = invg(invg g * h)^{-1}... complex.
           Simpler: x = g * n1. We want x = h * n2.
           x = g * n1 = (g * (invg g * h)^{-1}) * (invg g * h) * ... no.
           Let m = invg(g) * h \<in> N. Then h = g * m (from g * m = g * invg g * h = h).
           Wait: mul g m = mul g (mul (invg g) h) = mul (mul g (invg g)) h = mul e h = h.
           So h = mul g m. And g = mul h (invg m).
           x = mul g n1 = mul (mul h (invg m)) n1 = mul h (mul (invg m) n1).
           invg m \<in> N and n1 \<in> N, so mul (invg m) n1 \<in> N. Done.\<close>
        let ?m = "mul (invg g) h"
        have hmG: "?m \<in> G" by (rule group_mul_closed[OF hG hinvg hh])
        have hg_eq: "mul g ?m = h"
        proof -
          have "mul g (mul (invg g) h) = mul (mul g (invg g)) h"
            using group_assoc[OF hG hg hinvg hh] by (by100 simp)
          also have "mul g (invg g) = e" by (rule group_inv_right[OF hG hg])
          also have "mul e h = h" by (rule group_id_left[OF hG hh])
          finally show ?thesis by (by100 simp)
        qed
        have "invg ?m \<in> N" by (rule group_inv_closed[OF hN_grp hmem])
        have "invg ?m \<in> G" using hNsub \<open>invg ?m \<in> N\<close> by (by100 blast)
        have "x = mul g n1" using hx .
        \<comment> \<open>g = mul h (invg m).\<close>
        have "mul h (invg ?m) = g"
        proof -
          have "mul (mul h (invg ?m)) ?m = mul h (mul (invg ?m) ?m)"
            by (rule group_assoc[OF hG hh \<open>invg ?m \<in> G\<close> hmG])
          also have "mul (invg ?m) ?m = e" by (rule group_inv_left[OF hG hmG])
          also have "mul h e = h" by (rule group_id_right[OF hG hh])
          finally have "mul (mul h (invg ?m)) ?m = h" .
          moreover have "mul g ?m = h" by (rule hg_eq)
          ultimately have "mul (mul h (invg ?m)) ?m = mul g ?m" by (by100 simp)
          \<comment> \<open>Right-cancel ?m.\<close>
          have hmul1: "mul h (invg ?m) \<in> G"
            by (rule group_mul_closed[OF hG hh \<open>invg ?m \<in> G\<close>])
          have "mul (mul (mul h (invg ?m)) ?m) (invg ?m) = mul (mul g ?m) (invg ?m)"
            using \<open>mul (mul h (invg ?m)) ?m = mul g ?m\<close> by (by100 simp)
          have lhs: "mul (mul (mul h (invg ?m)) ?m) (invg ?m) = mul h (invg ?m)"
          proof -
            have "mul (mul (mul h (invg ?m)) ?m) (invg ?m)
                = mul (mul h (invg ?m)) (mul ?m (invg ?m))"
              by (rule group_assoc[OF hG hmul1 hmG \<open>invg ?m \<in> G\<close>])
            also have "mul ?m (invg ?m) = e" by (rule group_inv_right[OF hG hmG])
            also have "mul (mul h (invg ?m)) e = mul h (invg ?m)"
              by (rule group_id_right[OF hG hmul1])
            finally show ?thesis by (by100 simp)
          qed
          have rhs: "mul (mul g ?m) (invg ?m) = g"
          proof -
            have "mul (mul g ?m) (invg ?m) = mul g (mul ?m (invg ?m))"
              by (rule group_assoc[OF hG hg hmG \<open>invg ?m \<in> G\<close>])
            also have "mul ?m (invg ?m) = e" by (rule group_inv_right[OF hG hmG])
            also have "mul g e = g" by (rule group_id_right[OF hG hg])
            finally show ?thesis by (by100 simp)
          qed
          show ?thesis using lhs rhs
            \<open>mul (mul (mul h (invg ?m)) ?m) (invg ?m) = mul (mul g ?m) (invg ?m)\<close>
            by (by100 simp)
        qed
        hence "x = mul (mul h (invg ?m)) n1" using hx by (by100 simp)
        also have "\<dots> = mul h (mul (invg ?m) n1)"
          by (rule group_assoc[OF hG hh \<open>invg ?m \<in> G\<close> hn1G])
        finally have hx_eq: "x = mul h (mul (invg ?m) n1)" .
        have "mul (invg ?m) n1 \<in> N"
          by (rule group_mul_closed[OF hN_grp \<open>invg ?m \<in> N\<close> hn1])
        thus "x \<in> ?hN" unfolding top1_group_coset_on_def using hx_eq by (by100 blast)
      next
        \<comment> \<open>Symmetric direction: x \<in> hN \<Rightarrow> x \<in> gN.
           Similar argument using invg(invg g * h) = invg h * g, and mul (invg h) g \<in> N
           follows from invg(invg g * h) \<in> N.\<close>
        assume "x \<in> ?hN"
        then obtain n2 where hn2: "n2 \<in> N" and hx: "x = mul h n2"
          unfolding top1_group_coset_on_def by (by100 blast)
        have hn2G: "n2 \<in> G" using hn2 hNsub by (by100 blast)
        let ?m = "mul (invg g) h"
        have hmG: "?m \<in> G" by (rule group_mul_closed[OF hG hinvg hh])
        have hg_eq: "mul g ?m = h"
        proof -
          have "mul g (mul (invg g) h) = mul (mul g (invg g)) h"
            using group_assoc[OF hG hg hinvg hh] by (by100 simp)
          also have "mul g (invg g) = e" by (rule group_inv_right[OF hG hg])
          also have "mul e h = h" by (rule group_id_left[OF hG hh])
          finally show ?thesis by (by100 simp)
        qed
        \<comment> \<open>h = g * m, so x = h * n2 = g * m * n2 = g * (m * n2). m \<in> N, n2 \<in> N \<Rightarrow> m * n2 \<in> N.\<close>
        have "x = mul h n2" using hx .
        also have "mul h n2 = mul (mul g ?m) n2" using hg_eq by (by100 simp)
        also have "\<dots> = mul g (mul ?m n2)"
          by (rule group_assoc[OF hG hg hmG hn2G])
        finally have hx_eq: "x = mul g (mul ?m n2)" .
        have "mul ?m n2 \<in> N" by (rule group_mul_closed[OF hN_grp hmem hn2])
        thus "x \<in> ?gN" unfolding top1_group_coset_on_def using hx_eq by (by100 blast)
      qed
    qed
  qed
qed

lemma normal_coset_mul_eq:
  assumes hG: "top1_is_group_on G mul e invg"
      and hN: "top1_normal_subgroup_on G mul e invg N"
      and hg: "g \<in> G" and hh: "h \<in> G"
  shows "top1_quotient_group_mul_on mul
           (top1_group_coset_on G mul N g) (top1_group_coset_on G mul N h)
         = top1_group_coset_on G mul N (mul g h)"
proof (rule set_eqI)
  let ?gN = "top1_group_coset_on G mul N g"
  let ?hN = "top1_group_coset_on G mul N h"
  let ?ghN = "top1_group_coset_on G mul N (mul g h)"
  have hNsub: "N \<subseteq> G" using hN unfolding top1_normal_subgroup_on_def by (by100 blast)
  have hN_grp: "top1_is_group_on N mul e invg"
    using hN unfolding top1_normal_subgroup_on_def by (by100 blast)
  have hN_conj: "\<And>g0 n0. g0 \<in> G \<Longrightarrow> n0 \<in> N \<Longrightarrow> mul (mul g0 n0) (invg g0) \<in> N"
    using hN unfolding top1_normal_subgroup_on_def by (by100 blast)
  fix x
  show "x \<in> top1_quotient_group_mul_on mul ?gN ?hN \<longleftrightarrow> x \<in> ?ghN"
  proof
    \<comment> \<open>(\<subseteq>): x = mul (mul g n1) (mul h n2) for n1, n2 \<in> N.
       Rewrite using normality: mul n1 h = mul h n'' for n'' \<in> N.\<close>
    assume "x \<in> top1_quotient_group_mul_on mul ?gN ?hN"
    then obtain a b where ha: "a \<in> ?gN" and hb: "b \<in> ?hN" and hx: "x = mul a b"
      unfolding top1_quotient_group_mul_on_def by (by100 blast)
    obtain n1 where hn1: "n1 \<in> N" and ha_eq: "a = mul g n1"
      using ha unfolding top1_group_coset_on_def by (by100 blast)
    obtain n2 where hn2: "n2 \<in> N" and hb_eq: "b = mul h n2"
      using hb unfolding top1_group_coset_on_def by (by100 blast)
    have hn1G: "n1 \<in> G" using hn1 hNsub by (by100 blast)
    have hn2G: "n2 \<in> G" using hn2 hNsub by (by100 blast)
    \<comment> \<open>Key: mul (invg h) n1 h = n'' \<in> N, so n1 h = h n''.\<close>
    have hinvh: "invg h \<in> G" by (rule group_inv_closed[OF hG hh])
    have hn1h: "mul n1 h \<in> G" by (rule group_mul_closed[OF hG hn1G hh])
    \<comment> \<open>Conjugate n1 by invg h: mul (mul (invg h) n1) h \<in> N (normality with invg h).\<close>
    have hconj_step: "mul (mul (invg h) n1) (invg (invg h)) \<in> N"
      by (rule hN_conj[OF hinvh hn1])
    have hinvinvh: "invg (invg h) = h" by (rule group_inv_inv[OF hG hh])
    hence "mul (mul (invg h) n1) h \<in> N" using hconj_step by (by100 simp)
    then obtain n'' where hn'': "n'' \<in> N" and hn''_eq: "n'' = mul (mul (invg h) n1) h"
      by (by100 blast)
    \<comment> \<open>Show: mul h n'' = mul n1 h.\<close>
    have hn''G: "n'' \<in> G" using hn'' hNsub by (by100 blast)
    have "mul h n'' = mul h (mul (mul (invg h) n1) h)"
      using hn''_eq by (by100 simp)
    also have "\<dots> = mul (mul h (mul (invg h) n1)) h"
    proof -
      have hmid: "mul (invg h) n1 \<in> G" by (rule group_mul_closed[OF hG hinvh hn1G])
      show ?thesis using group_assoc[OF hG hh hmid hh] by (by100 simp)
    qed
    also have "mul h (mul (invg h) n1) = mul (mul h (invg h)) n1"
      using group_assoc[OF hG hh hinvh hn1G] by (by100 simp)
    also have "mul h (invg h) = e" by (rule group_inv_right[OF hG hh])
    also have "mul e n1 = n1" by (rule group_id_left[OF hG hn1G])
    finally have hmul_n1h: "mul h n'' = mul n1 h" by (by100 simp)
    \<comment> \<open>Now: x = mul (mul g n1) (mul h n2) = mul g (mul n1 (mul h n2))
            = mul g (mul (mul n1 h) n2) = mul g (mul (mul h n'') n2)
            = mul g (mul h (mul n'' n2)) = mul (mul g h) (mul n'' n2).\<close>
    have hhn2: "mul h n2 \<in> G" by (rule group_mul_closed[OF hG hh hn2G])
    have hn''n2: "mul n'' n2 \<in> G" by (rule group_mul_closed[OF hG hn''G hn2G])
    have "x = mul (mul g n1) (mul h n2)" using hx ha_eq hb_eq by (by100 simp)
    also have "\<dots> = mul g (mul n1 (mul h n2))"
      by (rule group_assoc[OF hG hg hn1G hhn2])
    also have "mul n1 (mul h n2) = mul (mul n1 h) n2"
      using group_assoc[OF hG hn1G hh hn2G] by (by100 simp)
    also have "mul n1 h = mul h n''" using hmul_n1h[symmetric] .
    also have "mul (mul h n'') n2 = mul h (mul n'' n2)"
      by (rule group_assoc[OF hG hh hn''G hn2G])
    also have "mul g (mul h (mul n'' n2)) = mul (mul g h) (mul n'' n2)"
      using group_assoc[OF hG hg hh hn''n2] by (by100 simp)
    finally have "x = mul (mul g h) (mul n'' n2)" by (by100 simp)
    moreover have "mul n'' n2 \<in> N" by (rule group_mul_closed[OF hN_grp hn'' hn2])
    ultimately show "x \<in> ?ghN" unfolding top1_group_coset_on_def by (by100 blast)
  next
    \<comment> \<open>(\<supseteq>): x = mul (mul g h) n for n \<in> N. Take a = g (= mul g e) and b = mul h n.\<close>
    assume "x \<in> ?ghN"
    then obtain n where hn: "n \<in> N" and hx: "x = mul (mul g h) n"
      unfolding top1_group_coset_on_def by (by100 blast)
    have hnG: "n \<in> G" using hn hNsub by (by100 blast)
    have he_N: "e \<in> N" by (rule group_e_mem[OF hN_grp])
    have hge: "mul g e = g" by (rule group_id_right[OF hG hg])
    have "x = mul g (mul h n)"
      using hx group_assoc[OF hG hg hh hnG] by (by100 simp)
    moreover have "g \<in> ?gN" unfolding top1_group_coset_on_def using he_N hge by (by100 force)
    moreover have "mul h n \<in> ?hN" unfolding top1_group_coset_on_def using hn by (by100 blast)
    ultimately show "x \<in> top1_quotient_group_mul_on mul ?gN ?hN"
      unfolding top1_quotient_group_mul_on_def by (by100 blast)
  qed
qed

text \<open>The natural projection \<phi>(g) = gN is a surjective group homomorphism with kernel N.\<close>
lemma quotient_projection_properties:
  assumes hG: "top1_is_group_on G mul e invg"
      and hN: "top1_normal_subgroup_on G mul e invg N"
  shows "top1_group_hom_on G mul
           (top1_quotient_group_carrier_on G mul N)
           (top1_quotient_group_mul_on mul)
           (\<lambda>g. top1_group_coset_on G mul N g)"
    and "(\<lambda>g. top1_group_coset_on G mul N g) ` G
           = top1_quotient_group_carrier_on G mul N"
    and "top1_group_kernel_on G (top1_group_coset_on G mul N e)
           (\<lambda>g. top1_group_coset_on G mul N g) = N"
proof -
  let ?\<phi> = "\<lambda>g. top1_group_coset_on G mul N g"
  let ?H = "top1_quotient_group_carrier_on G mul N"
  have hNsub: "N \<subseteq> G" using hN unfolding top1_normal_subgroup_on_def by (by100 blast)
  have hN_grp: "top1_is_group_on N mul e invg" using hN unfolding top1_normal_subgroup_on_def
    by (by100 blast)
  \<comment> \<open>Part 1: \<phi> is a homomorphism.\<close>
  show "top1_group_hom_on G mul ?H (top1_quotient_group_mul_on mul) ?\<phi>"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    fix g assume hg: "g \<in> G"
    show "?\<phi> g \<in> ?H" unfolding top1_quotient_group_carrier_on_def
      using hg by (by100 blast)
  next
    fix g h assume hg: "g \<in> G" and hh: "h \<in> G"
    show "?\<phi> (mul g h) = top1_quotient_group_mul_on mul (?\<phi> g) (?\<phi> h)"
      using normal_coset_mul_eq[OF hG hN hg hh, symmetric] .
  qed
  \<comment> \<open>Part 2: \<phi> is surjective.\<close>
  show "?\<phi> ` G = ?H" unfolding top1_quotient_group_carrier_on_def image_def
    by (by100 blast)
  \<comment> \<open>Part 3: ker(\<phi>) = N.\<close>
  show "top1_group_kernel_on G (?\<phi> e) ?\<phi> = N"
  proof -
    have heN: "?\<phi> e = N" by (rule coset_e_is_N[OF hG hNsub hN_grp])
    show ?thesis unfolding top1_group_kernel_on_def heN
    proof (rule set_eqI)
      fix g show "g \<in> {x \<in> G. ?\<phi> x = N} \<longleftrightarrow> g \<in> N"
      proof
        assume "g \<in> {x \<in> G. ?\<phi> x = N}"
        hence hg: "g \<in> G" and hcoset: "?\<phi> g = N" by (by100 blast)+
        have "g \<in> ?\<phi> g" by (rule coset_self_mem[OF hG hNsub hN_grp hg])
        thus "g \<in> N" using hcoset by (by100 simp)
      next
        assume "g \<in> N"
        hence hg: "g \<in> G" using hNsub by (by100 blast)
        have he: "e \<in> G" by (rule group_e_mem[OF hG])
        have hinve: "invg e \<in> G" by (rule group_inv_closed[OF hG he])
        have "invg e = e"
        proof -
          have "mul (invg e) e = e" by (rule group_inv_left[OF hG he])
          moreover have "mul (invg e) e = invg e" by (rule group_id_right[OF hG hinve])
          ultimately show ?thesis by (by100 simp)
        qed
        hence "mul (invg e) g = mul e g" by (by100 simp)
        also have "... = g" by (rule group_id_left[OF hG hg])
        finally have "mul (invg e) g = g" .
        hence "mul (invg e) g \<in> N" using \<open>g \<in> N\<close> by (by100 simp)
        hence "?\<phi> e = ?\<phi> g" using normal_coset_eq[OF hG hN he hg] by (by100 simp)
        hence "?\<phi> g = N" using heN by (by100 simp)
        thus "g \<in> {x \<in> G. ?\<phi> x = N}" using hg by (by100 blast)
      qed
    qed
  qed
qed

text \<open>G/[G,G] is abelian: for any g, h \<in> G, the cosets gN and hN commute
  because g\<inverse>h\<inverse>gh \<in> [G,G] = N.\<close>
lemma quotient_by_commutator_is_abelian:
  assumes hG: "top1_is_group_on G mul e invg"
  shows "\<forall>g\<in>G. \<forall>h\<in>G.
    top1_quotient_group_mul_on mul
      (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) g)
      (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) h)
    = top1_quotient_group_mul_on mul
      (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) h)
      (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) g)"
proof (intro ballI)
  let ?N = "top1_commutator_subgroup_on G mul e invg"
  have hNnormal: "top1_normal_subgroup_on G mul e invg ?N"
    by (rule commutator_subgroup_is_normal[OF hG])
  have hNsub: "?N \<subseteq> G" using hNnormal unfolding top1_normal_subgroup_on_def by (by100 blast)
  have hN_grp: "top1_is_group_on ?N mul e invg"
    using hNnormal unfolding top1_normal_subgroup_on_def by (by100 blast)
  fix g h assume hg: "g \<in> G" and hh: "h \<in> G"
  \<comment> \<open>(gN)(hN) = (gh)N and (hN)(gN) = (hg)N. Need (gh)N = (hg)N.\<close>
  have lhs: "top1_quotient_group_mul_on mul
      (top1_group_coset_on G mul ?N g) (top1_group_coset_on G mul ?N h)
    = top1_group_coset_on G mul ?N (mul g h)"
    by (rule normal_coset_mul_eq[OF hG hNnormal hg hh])
  have rhs: "top1_quotient_group_mul_on mul
      (top1_group_coset_on G mul ?N h) (top1_group_coset_on G mul ?N g)
    = top1_group_coset_on G mul ?N (mul h g)"
    by (rule normal_coset_mul_eq[OF hG hNnormal hh hg])
  \<comment> \<open>Need: (gh)N = (hg)N, i.e. invg(gh) * hg \<in> N = [G,G].
     invg(gh) * hg = (invg h * invg g) * (h * g) = invg h * (invg g * h * g)
     But the commutator [invg g, invg h] = invg g * invg h * g * h.
     More directly: invg(gh) * hg = invg(h) * invg(g) * h * g = [g,h]\<inverse>^{...}.\<close>
  have "top1_group_coset_on G mul ?N (mul g h) = top1_group_coset_on G mul ?N (mul h g)"
  proof -
    have hgh: "mul g h \<in> G" by (rule group_mul_closed[OF hG hg hh])
    have hhg: "mul h g \<in> G" by (rule group_mul_closed[OF hG hh hg])
    \<comment> \<open>Show invg(mul g h) * mul h g \<in> [G,G].\<close>
    have hinvgh: "invg (mul g h) \<in> G" by (rule group_inv_closed[OF hG hgh])
    have "invg (mul g h) = mul (invg h) (invg g)"
      by (rule group_inv_mul[OF hG hg hh])
    hence "mul (invg (mul g h)) (mul h g) = mul (mul (invg h) (invg g)) (mul h g)"
      by (by100 simp)
    also have "\<dots> = mul (invg h) (mul (invg g) (mul h g))"
    proof -
      have "invg h \<in> G" by (rule group_inv_closed[OF hG hh])
      have "invg g \<in> G" by (rule group_inv_closed[OF hG hg])
      show ?thesis by (rule group_assoc[OF hG \<open>invg h \<in> G\<close> \<open>invg g \<in> G\<close> hhg])
    qed
    also have "mul (invg g) (mul h g) = mul (mul (invg g) h) g"
    proof -
      have "invg g \<in> G" by (rule group_inv_closed[OF hG hg])
      thus ?thesis using group_assoc[OF hG \<open>invg g \<in> G\<close> hh hg] by (by100 simp)
    qed
    finally have hkey: "mul (invg (mul g h)) (mul h g)
        = mul (invg h) (mul (mul (invg g) h) g)" .
    \<comment> \<open>This is mul (invg h) (mul (mul (invg g) h) (invg (invg h))  * invg h)...
       Actually this equals the commutator [invg g, invg h] = invg g * invg h * g * h,
       which is in [G,G]. More directly:
       mul (invg h) (mul (mul (invg g) h) g)
       = mul (invg h) (mul (invg g) (mul h g))... already shown.
       Hmm let me try: this is [g, h]\<inverse> form. The commutator of g and h is
       top1_group_commutator_on mul invg g h = mul (mul (mul g h) (invg g)) (invg h).
       We need mul (invg (mul g h)) (mul h g) \<in> [G,G].\<close>
    \<comment> \<open>Simpler approach: the commutator [g,h] = g h g\<inverse> h\<inverse>. Then
       [g,h] * h * g = g * h. So h * g = [g,h]\<inverse> * g * h.
       Therefore invg(g*h) * h*g = invg(g*h) * [g,h]\<inverse> * g * h
       = invg(g*h) * invg([g,h]) * g * h.
       But invg([g,h]) * g * h = invg(g h g\<inverse> h\<inverse>) * g * h
       = h * g * invg(h) * invg(g) * g * h... getting circular.

       Direct approach: show mul (invg (mul g h)) (mul h g) is a product of commutators.

       mul (invg (mul g h)) (mul h g)
       = mul (mul (invg h) (invg g)) (mul h g)   [inv_mul]
       = mul (invg h) (mul (invg g) (mul h g))    [assoc]
       = mul (invg h) (mul (mul (invg g) h) g)    [assoc]

       Now mul (mul (invg g) h) g = mul (invg g) (mul h g)... wait already done.

       Let's compute: top1_group_commutator_on mul invg (invg g) (invg h)
       = mul (mul (mul (invg g) (invg h)) g) h

       Hmm actually top1_group_commutator_on is defined as:
       "top1_group_commutator_on mul invg a b = mul (mul (mul a b) (invg a)) (invg b)"

       So [a,b] = a*b*a\<inverse>*b\<inverse>.

       For a = invg(h), b = invg(g):
       [invg h, invg g] = invg(h) * invg(g) * h * g

       = mul (mul (mul (invg h) (invg g)) h) g

       Compare with our expression:
       mul (invg h) (mul (mul (invg g) h) g)
       = mul (invg h) (mul (invg g) (mul h g))   [re-assoc]
       = mul (mul (invg h) (invg g)) (mul h g)    [assoc]
       = mul (mul (mul (invg h) (invg g)) h) g    [assoc]

       So mul (invg (mul g h)) (mul h g) = [invg h, invg g].

       And since invg h, invg g ∈ G, this commutator is in [G,G].

       That works!\<close>
    have hinvg: "invg g \<in> G" by (rule group_inv_closed[OF hG hg])
    have hinvh: "invg h \<in> G" by (rule group_inv_closed[OF hG hh])
    \<comment> \<open>The commutator [invg h, invg g] is in [G,G].\<close>
    have hcomm: "top1_group_commutator_on mul invg (invg h) (invg g) \<in> ?N"
    proof -
      let ?gens = "{ top1_group_commutator_on mul invg a b | a b. a \<in> G \<and> b \<in> G }"
      have "top1_group_commutator_on mul invg (invg h) (invg g) \<in> ?gens"
        using hinvh hinvg by (by100 blast)
      moreover have "?gens \<subseteq> G"
      proof (rule subsetI)
        fix x assume "x \<in> ?gens"
        then obtain a b where "a \<in> G" "b \<in> G" "x = top1_group_commutator_on mul invg a b"
          by (by100 blast)
        thus "x \<in> G" unfolding top1_group_commutator_on_def
          using hG unfolding top1_is_group_on_def by (by100 blast)
      qed
      ultimately have "top1_group_commutator_on mul invg (invg h) (invg g)
          \<in> top1_subgroup_generated_on G mul e invg ?gens"
        by (intro subgroup_generated_contains[OF hG]) (by100 blast)+
      thus ?thesis unfolding top1_commutator_subgroup_on_def .
    qed
    \<comment> \<open>Now show [invg h, invg g] = mul (invg (mul g h)) (mul h g).\<close>
    have "top1_group_commutator_on mul invg (invg h) (invg g)
        = mul (mul (mul (invg h) (invg g)) (invg (invg h))) (invg (invg g))"
      unfolding top1_group_commutator_on_def ..
    also have "invg (invg h) = h" by (rule group_inv_inv[OF hG hh])
    also have "invg (invg g) = g" by (rule group_inv_inv[OF hG hg])
    finally have hcomm_eq: "top1_group_commutator_on mul invg (invg h) (invg g)
        = mul (mul (mul (invg h) (invg g)) h) g" by (by100 simp)
    \<comment> \<open>And mul (invg (mul g h)) (mul h g) = mul (mul (mul (invg h) (invg g)) h) g.\<close>
    have hstep1: "mul (invg (mul g h)) (mul h g) = mul (mul (invg h) (invg g)) (mul h g)"
      using group_inv_mul[OF hG hg hh] by (by100 simp)
    have hstep2: "mul (mul (invg h) (invg g)) (mul h g)
        = mul (mul (mul (invg h) (invg g)) h) g"
    proof -
      have hmid: "mul (invg h) (invg g) \<in> G" by (rule group_mul_closed[OF hG hinvh hinvg])
      have "mul (mul (mul (invg h) (invg g)) h) g = mul (mul (invg h) (invg g)) (mul h g)"
        by (rule group_assoc[OF hG hmid hh hg])
      thus ?thesis by (by100 simp)
    qed
    have "mul (invg (mul g h)) (mul h g) = top1_group_commutator_on mul invg (invg h) (invg g)"
      using hstep1 hstep2 hcomm_eq by (by100 simp)
    hence "mul (invg (mul g h)) (mul h g) \<in> ?N" using hcomm by (by100 simp)
    thus ?thesis using normal_coset_eq[OF hG hNnormal hgh hhg] by (by100 simp)
  qed
  thus "top1_quotient_group_mul_on mul
      (top1_group_coset_on G mul ?N g) (top1_group_coset_on G mul ?N h)
    = top1_quotient_group_mul_on mul
      (top1_group_coset_on G mul ?N h) (top1_group_coset_on G mul ?N g)"
    using lhs rhs by (by100 simp)
qed

text \<open>The quotient G/N is a group when N is normal.\<close>
lemma quotient_group_is_group:
  assumes hG: "top1_is_group_on G mul e invg"
      and hN: "top1_normal_subgroup_on G mul e invg N"
  shows "top1_is_group_on
    (top1_quotient_group_carrier_on G mul N)
    (top1_quotient_group_mul_on mul)
    (top1_group_coset_on G mul N e)
    (\<lambda>C. top1_group_coset_on G mul N (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g)))"
proof -
  let ?H = "top1_quotient_group_carrier_on G mul N"
  let ?mulH = "top1_quotient_group_mul_on mul"
  let ?eH = "top1_group_coset_on G mul N e"
  let ?invgH = "\<lambda>C. top1_group_coset_on G mul N (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g))"
  have hNsub: "N \<subseteq> G" using hN unfolding top1_normal_subgroup_on_def by (by100 blast)
  have hN_grp: "top1_is_group_on N mul e invg"
    using hN unfolding top1_normal_subgroup_on_def by (by100 blast)
  \<comment> \<open>Helper: for any C \<in> H, there exists g \<in> G with C = coset g.\<close>
  have hrep: "\<And>C. C \<in> ?H \<Longrightarrow> \<exists>g. g \<in> G \<and> C = top1_group_coset_on G mul N g"
    unfolding top1_quotient_group_carrier_on_def by (by100 blast)
  \<comment> \<open>Helper: SOME picks a valid representative.\<close>
  have hsome: "\<And>C. C \<in> ?H \<Longrightarrow>
      (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g) \<in> G \<and>
      C = top1_group_coset_on G mul N (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g)"
  proof -
    fix C assume "C \<in> ?H"
    from hrep[OF this] have "\<exists>g. g \<in> G \<and> C = top1_group_coset_on G mul N g" .
    thus "(SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g) \<in> G \<and>
      C = top1_group_coset_on G mul N (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g)"
      by (rule someI_ex)
  qed
  show ?thesis unfolding top1_is_group_on_def
  proof (intro conjI ballI)
    \<comment> \<open>eH \<in> H.\<close>
    show "?eH \<in> ?H" unfolding top1_quotient_group_carrier_on_def
      using group_e_mem[OF hG] by (by100 blast)
  next
    \<comment> \<open>mul closed.\<close>
    fix C1 C2 assume hC1: "C1 \<in> ?H" and hC2: "C2 \<in> ?H"
    obtain g1 where hg1: "g1 \<in> G" and hC1_eq: "C1 = top1_group_coset_on G mul N g1"
      using hrep[OF hC1] by (by100 blast)
    obtain g2 where hg2: "g2 \<in> G" and hC2_eq: "C2 = top1_group_coset_on G mul N g2"
      using hrep[OF hC2] by (by100 blast)
    have "?mulH C1 C2 = top1_group_coset_on G mul N (mul g1 g2)"
      using hC1_eq hC2_eq normal_coset_mul_eq[OF hG hN hg1 hg2] by (by100 simp)
    thus "?mulH C1 C2 \<in> ?H" unfolding top1_quotient_group_carrier_on_def
      using group_mul_closed[OF hG hg1 hg2] by (by100 blast)
  next
    \<comment> \<open>inv closed.\<close>
    fix C assume hC: "C \<in> ?H"
    have hsome_C: "(SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g) \<in> G"
      using hsome[OF hC] by (by100 blast)
    have "invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g) \<in> G"
      by (rule group_inv_closed[OF hG hsome_C])
    thus "?invgH C \<in> ?H" unfolding top1_quotient_group_carrier_on_def by (by100 blast)
  next
    \<comment> \<open>Associativity.\<close>
    fix C1 C2 C3 assume hC1: "C1 \<in> ?H" and hC2: "C2 \<in> ?H" and hC3: "C3 \<in> ?H"
    obtain g1 where hg1: "g1 \<in> G" and hC1_eq: "C1 = top1_group_coset_on G mul N g1"
      using hrep[OF hC1] by (by100 blast)
    obtain g2 where hg2: "g2 \<in> G" and hC2_eq: "C2 = top1_group_coset_on G mul N g2"
      using hrep[OF hC2] by (by100 blast)
    obtain g3 where hg3: "g3 \<in> G" and hC3_eq: "C3 = top1_group_coset_on G mul N g3"
      using hrep[OF hC3] by (by100 blast)
    have hg12: "mul g1 g2 \<in> G" by (rule group_mul_closed[OF hG hg1 hg2])
    have hg23: "mul g2 g3 \<in> G" by (rule group_mul_closed[OF hG hg2 hg3])
    have hC12: "?mulH C1 C2 = top1_group_coset_on G mul N (mul g1 g2)"
      using hC1_eq hC2_eq normal_coset_mul_eq[OF hG hN hg1 hg2] by (by100 simp)
    have hC23: "?mulH C2 C3 = top1_group_coset_on G mul N (mul g2 g3)"
      using hC2_eq hC3_eq normal_coset_mul_eq[OF hG hN hg2 hg3] by (by100 simp)
    have lhs: "?mulH (?mulH C1 C2) C3 = top1_group_coset_on G mul N (mul (mul g1 g2) g3)"
      using hC12 hC3_eq normal_coset_mul_eq[OF hG hN hg12 hg3] by (by100 simp)
    have rhs: "?mulH C1 (?mulH C2 C3) = top1_group_coset_on G mul N (mul g1 (mul g2 g3))"
      using hC23 hC1_eq normal_coset_mul_eq[OF hG hN hg1 hg23] by (by100 simp)
    show "?mulH (?mulH C1 C2) C3 = ?mulH C1 (?mulH C2 C3)"
      using lhs rhs group_assoc[OF hG hg1 hg2 hg3] by (by100 simp)
  next
    \<comment> \<open>Left identity.\<close>
    fix C assume hC: "C \<in> ?H"
    obtain g where hg: "g \<in> G" and hC_eq: "C = top1_group_coset_on G mul N g"
      using hrep[OF hC] by (by100 blast)
    have he: "e \<in> G" by (rule group_e_mem[OF hG])
    have "?mulH ?eH C = top1_group_coset_on G mul N (mul e g)"
      using hC_eq normal_coset_mul_eq[OF hG hN he hg] by (by100 simp)
    also have "mul e g = g" by (rule group_id_left[OF hG hg])
    finally show "?mulH ?eH C = C" using hC_eq by (by100 simp)
  next
    \<comment> \<open>Right identity.\<close>
    fix C assume hC: "C \<in> ?H"
    obtain g where hg: "g \<in> G" and hC_eq: "C = top1_group_coset_on G mul N g"
      using hrep[OF hC] by (by100 blast)
    have he2: "e \<in> G" by (rule group_e_mem[OF hG])
    have "?mulH C ?eH = top1_group_coset_on G mul N (mul g e)"
      using hC_eq normal_coset_mul_eq[OF hG hN hg he2] by (by100 simp)
    also have "mul g e = g" by (rule group_id_right[OF hG hg])
    finally show "?mulH C ?eH = C" using hC_eq by (by100 simp)
  next
    \<comment> \<open>Left inverse.\<close>
    fix C assume hC: "C \<in> ?H"
    have hsome_C: "(SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g) \<in> G"
      using hsome[OF hC] by (by100 blast)
    have hC_some: "C = top1_group_coset_on G mul N (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g)"
      using hsome[OF hC] by (by100 blast)
    let ?g = "SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g"
    have hinvg_mem: "invg ?g \<in> G" by (rule group_inv_closed[OF hG hsome_C])
    have "?mulH (?invgH C) C = ?mulH (top1_group_coset_on G mul N (invg ?g))
        (top1_group_coset_on G mul N ?g)"
      using hC_some by (by100 simp)
    also have "\<dots> = top1_group_coset_on G mul N (mul (invg ?g) ?g)"
      by (rule normal_coset_mul_eq[OF hG hN hinvg_mem hsome_C])
    also have "\<dots> = top1_group_coset_on G mul N e"
      using group_inv_left[OF hG hsome_C] by (by100 simp)
    finally show "?mulH (?invgH C) C = ?eH" .
  next
    \<comment> \<open>Right inverse.\<close>
    fix C assume hC: "C \<in> ?H"
    have hsome_C: "(SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g) \<in> G"
      using hsome[OF hC] by (by100 blast)
    have hC_some: "C = top1_group_coset_on G mul N (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g)"
      using hsome[OF hC] by (by100 blast)
    let ?g = "SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g"
    have hinvg_mem2: "invg ?g \<in> G" by (rule group_inv_closed[OF hG hsome_C])
    have "?mulH C (?invgH C) = ?mulH (top1_group_coset_on G mul N ?g)
        (top1_group_coset_on G mul N (invg ?g))"
      using hC_some by (by100 simp)
    also have "\<dots> = top1_group_coset_on G mul N (mul ?g (invg ?g))"
      by (rule normal_coset_mul_eq[OF hG hN hsome_C hinvg_mem2])
    also have "\<dots> = top1_group_coset_on G mul N e"
      using group_inv_right[OF hG hsome_C] by (by100 simp)
    finally show "?mulH C (?invgH C) = ?eH" .
  qed
qed

text \<open>First isomorphism theorem: a surjective homomorphism j: G \<rightarrow> H with kernel N
  induces an isomorphism G/N \<cong> H.\<close>
lemma first_isomorphism_theorem:
  assumes hG: "top1_is_group_on G mul e invg"
      and hN: "top1_normal_subgroup_on G mul e invg N"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hj_hom: "top1_group_hom_on G mul H mulH j"
      and hj_surj: "j ` G = H"
      and hj_ker: "top1_group_kernel_on G eH j = N"
  shows "top1_groups_isomorphic_on H mulH
      (top1_quotient_group_carrier_on G mul N) (top1_quotient_group_mul_on mul)"
proof -
  \<comment> \<open>The induced map j_bar: G/N \<rightarrow> H sends coset gN to j(g). Well-defined by kernel = N.\<close>
  let ?Q = "top1_quotient_group_carrier_on G mul N"
  let ?mulQ = "top1_quotient_group_mul_on mul"
  let ?j_bar = "\<lambda>C. j (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g)"
  have hNsub: "N \<subseteq> G" using hN unfolding top1_normal_subgroup_on_def by (by100 blast)
  have hN_grp: "top1_is_group_on N mul e invg"
    using hN unfolding top1_normal_subgroup_on_def by (by100 blast)
  \<comment> \<open>Representative picker.\<close>
  have hsome: "\<And>C. C \<in> ?Q \<Longrightarrow>
      (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g) \<in> G \<and>
      C = top1_group_coset_on G mul N (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g)"
  proof -
    fix C assume "C \<in> ?Q"
    hence "\<exists>g. g \<in> G \<and> C = top1_group_coset_on G mul N g"
      unfolding top1_quotient_group_carrier_on_def by (by100 blast)
    thus "(SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g) \<in> G \<and>
      C = top1_group_coset_on G mul N (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g)"
      by (rule someI_ex)
  qed
  \<comment> \<open>The induced map j_bar: G/N \<rightarrow> H is a bijective homomorphism.
     Well-definedness, homomorphism, injectivity, surjectivity follow from
     normal_coset_eq + kernel property + hom property.\<close>
  \<comment> \<open>Well-definedness: j(g) depends only on the coset.\<close>
  \<comment> \<open>Hom preserves identity: j(e) = eH (since e \<in> N = ker(j)).\<close>
  have hj_e: "j e = eH"
  proof -
    have "e \<in> N" by (rule group_e_mem[OF hN_grp])
    hence "e \<in> top1_group_kernel_on G eH j" using hj_ker by (by100 simp)
    thus ?thesis unfolding top1_group_kernel_on_def by (by100 blast)
  qed
  \<comment> \<open>Hom preserves inverse: j(invg g) = invgH(j g).\<close>
  have hj_inv: "\<And>g0. g0 \<in> G \<Longrightarrow> j (invg g0) = invgH (j g0)"
  proof -
    fix g0 assume hg0: "g0 \<in> G"
    have hjg0: "j g0 \<in> H" using hj_hom hg0 unfolding top1_group_hom_on_def by (by100 blast)
    have hinvg0: "invg g0 \<in> G" by (rule group_inv_closed[OF hG hg0])
    have hjinvg0: "j (invg g0) \<in> H" using hj_hom hinvg0 unfolding top1_group_hom_on_def by (by100 blast)
    have "j (mul (invg g0) g0) = mulH (j (invg g0)) (j g0)"
      using hj_hom hinvg0 hg0 unfolding top1_group_hom_on_def by (by100 blast)
    hence "mulH (j (invg g0)) (j g0) = j (mul (invg g0) g0)" by (by100 simp)
    also have "mul (invg g0) g0 = e" by (rule group_inv_left[OF hG hg0])
    also have "j e = eH" by (rule hj_e)
    finally have "mulH (j (invg g0)) (j g0) = eH" .
    \<comment> \<open>In group H: if a*b=eH then a=invgH(b).\<close>
    have "j (invg g0) = mulH (j (invg g0)) (mulH (j g0) (invgH (j g0)))"
      using group_inv_right[OF hH hjg0] group_id_right[OF hH hjinvg0] by (by100 simp)
    also have "\<dots> = mulH (mulH (j (invg g0)) (j g0)) (invgH (j g0))"
    proof -
      have "invgH (j g0) \<in> H" by (rule group_inv_closed[OF hH hjg0])
      show ?thesis using group_assoc[OF hH hjinvg0 hjg0 \<open>invgH (j g0) \<in> H\<close>] by (by100 simp)
    qed
    also have "mulH (j (invg g0)) (j g0) = eH"
      by (rule \<open>mulH (j (invg g0)) (j g0) = eH\<close>)
    also have "mulH eH (invgH (j g0)) = invgH (j g0)"
      using group_inv_closed[OF hH hjg0] by (rule group_id_left[OF hH])
    finally show "j (invg g0) = invgH (j g0)" .
  qed
  have hj_wd: "\<And>g1 g2. g1 \<in> G \<Longrightarrow> g2 \<in> G \<Longrightarrow>
      top1_group_coset_on G mul N g1 = top1_group_coset_on G mul N g2 \<Longrightarrow> j g1 = j g2"
  proof -
    fix g1 g2 assume hg1: "g1 \<in> G" and hg2: "g2 \<in> G"
        and hcoset: "top1_group_coset_on G mul N g1 = top1_group_coset_on G mul N g2"
    have hinvg1: "invg g1 \<in> G" by (rule group_inv_closed[OF hG hg1])
    have "mul (invg g1) g2 \<in> N" using normal_coset_eq[OF hG hN hg1 hg2] hcoset by (by100 simp)
    hence "j (mul (invg g1) g2) = eH" using hj_ker
      unfolding top1_group_kernel_on_def
      using group_mul_closed[OF hG hinvg1 hg2] by (by100 blast)
    moreover have "j (mul (invg g1) g2) = mulH (j (invg g1)) (j g2)"
      using hj_hom hinvg1 hg2 unfolding top1_group_hom_on_def by (by100 blast)
    ultimately have "mulH (invgH (j g1)) (j g2) = eH"
      using hj_inv[OF hg1] by (by100 simp)
    have hjg1: "j g1 \<in> H" using hj_hom hg1 unfolding top1_group_hom_on_def by (by100 blast)
    have hjg2: "j g2 \<in> H" using hj_hom hg2 unfolding top1_group_hom_on_def by (by100 blast)
    have hinvjg1: "invgH (j g1) \<in> H" by (rule group_inv_closed[OF hH hjg1])
    \<comment> \<open>invgH(j g1) * j g2 = eH implies j g2 = j g1.\<close>
    have "j g2 = mulH eH (j g2)" using group_id_left[OF hH hjg2] by (by100 simp)
    also have "\<dots> = mulH (mulH (j g1) (invgH (j g1))) (j g2)"
      using group_inv_right[OF hH hjg1] by (by100 simp)
    also have "\<dots> = mulH (j g1) (mulH (invgH (j g1)) (j g2))"
      by (rule group_assoc[OF hH hjg1 hinvjg1 hjg2])
    also have "mulH (invgH (j g1)) (j g2) = eH"
      by (rule \<open>mulH (invgH (j g1)) (j g2) = eH\<close>)
    also have "mulH (j g1) eH = j g1" by (rule group_id_right[OF hH hjg1])
    finally show "j g1 = j g2" by (by100 simp)
  qed
  have "top1_group_iso_on ?Q ?mulQ H mulH ?j_bar"
    unfolding top1_group_iso_on_def
  proof (intro conjI)
    \<comment> \<open>j_bar is a homomorphism.\<close>
    show "top1_group_hom_on ?Q ?mulQ H mulH ?j_bar"
      unfolding top1_group_hom_on_def
    proof (intro conjI ballI)
      fix C assume hC: "C \<in> ?Q"
      have hsC: "(SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g) \<in> G"
        using hsome[OF hC] by (by100 blast)
      show "?j_bar C \<in> H" using hj_hom hsC unfolding top1_group_hom_on_def by (by100 blast)
    next
      fix C1 C2 assume hC1: "C1 \<in> ?Q" and hC2: "C2 \<in> ?Q"
      obtain g1 where hg1: "g1 \<in> G" and hC1_eq: "C1 = top1_group_coset_on G mul N g1"
        using hsome[OF hC1] by (by100 blast)
      obtain g2 where hg2: "g2 \<in> G" and hC2_eq: "C2 = top1_group_coset_on G mul N g2"
        using hsome[OF hC2] by (by100 blast)
      let ?r1 = "SOME g. g \<in> G \<and> C1 = top1_group_coset_on G mul N g"
      let ?r2 = "SOME g. g \<in> G \<and> C2 = top1_group_coset_on G mul N g"
      let ?r12 = "SOME g. g \<in> G \<and> ?mulQ C1 C2 = top1_group_coset_on G mul N g"
      have hr1: "?r1 \<in> G" and hr1_eq: "C1 = top1_group_coset_on G mul N ?r1"
        using hsome[OF hC1] by (by100 blast)+
      have hr2: "?r2 \<in> G" and hr2_eq: "C2 = top1_group_coset_on G mul N ?r2"
        using hsome[OF hC2] by (by100 blast)+
      have hprod_eq: "?mulQ C1 C2 = top1_group_coset_on G mul N (mul ?r1 ?r2)"
        using hr1_eq hr2_eq normal_coset_mul_eq[OF hG hN hr1 hr2] by (by100 simp)
      have hprod_in: "?mulQ C1 C2 \<in> ?Q"
        unfolding top1_quotient_group_carrier_on_def
        using group_mul_closed[OF hG hr1 hr2] hprod_eq by (by100 blast)
      have hr12: "?r12 \<in> G" and hr12_eq: "?mulQ C1 C2 = top1_group_coset_on G mul N ?r12"
        using hsome[OF hprod_in] by (by100 blast)+
      \<comment> \<open>?r12 and mul ?r1 ?r2 are in the same coset, so j(?r12) = j(mul ?r1 ?r2).\<close>
      have hr12_mem: "mul ?r1 ?r2 \<in> G" by (rule group_mul_closed[OF hG hr1 hr2])
      have "j ?r12 = j (mul ?r1 ?r2)"
      proof (rule hj_wd[OF hr12 hr12_mem])
        show "top1_group_coset_on G mul N ?r12 = top1_group_coset_on G mul N (mul ?r1 ?r2)"
          using hr12_eq hprod_eq by (by100 simp)
      qed
      also have "\<dots> = mulH (j ?r1) (j ?r2)"
        using hj_hom hr1 hr2 unfolding top1_group_hom_on_def by (by100 blast)
      finally show "?j_bar (?mulQ C1 C2) = mulH (?j_bar C1) (?j_bar C2)" .
    qed
  next
    \<comment> \<open>j_bar is bijective.\<close>
    show "bij_betw ?j_bar ?Q H"
      unfolding bij_betw_def
    proof (intro conjI)
      \<comment> \<open>Injectivity: j_bar(C1) = j_bar(C2) implies C1 = C2.\<close>
      show "inj_on ?j_bar ?Q"
      proof (rule inj_onI)
        fix C1 C2 assume hC1: "C1 \<in> ?Q" and hC2: "C2 \<in> ?Q" and heq: "?j_bar C1 = ?j_bar C2"
        let ?r1 = "SOME g. g \<in> G \<and> C1 = top1_group_coset_on G mul N g"
        let ?r2 = "SOME g. g \<in> G \<and> C2 = top1_group_coset_on G mul N g"
        have hr1: "?r1 \<in> G" and hC1_eq: "C1 = top1_group_coset_on G mul N ?r1"
          using hsome[OF hC1] by (by100 blast)+
        have hr2: "?r2 \<in> G" and hC2_eq: "C2 = top1_group_coset_on G mul N ?r2"
          using hsome[OF hC2] by (by100 blast)+
        \<comment> \<open>j(?r1) = j(?r2), so j(invg(?r1) * ?r2) = eH, so invg(?r1)*?r2 \<in> ker = N.\<close>
        have "j ?r1 = j ?r2" using heq by (by100 simp)
        hence "mul (invg ?r1) ?r2 \<in> N"
        proof -
          have hinvr1: "invg ?r1 \<in> G" by (rule group_inv_closed[OF hG hr1])
          have "j (mul (invg ?r1) ?r2) = mulH (j (invg ?r1)) (j ?r2)"
            using hj_hom hinvr1 hr2 unfolding top1_group_hom_on_def by (by100 blast)
          also have "j (invg ?r1) = invgH (j ?r1)" by (rule hj_inv[OF hr1])
          also have "mulH (invgH (j ?r1)) (j ?r2) = mulH (invgH (j ?r1)) (j ?r1)"
            using \<open>j ?r1 = j ?r2\<close> by (by100 simp)
          also have "\<dots> = eH"
          proof -
            have "j ?r1 \<in> H" using hj_hom hr1 unfolding top1_group_hom_on_def by (by100 blast)
            thus ?thesis by (rule group_inv_left[OF hH])
          qed
          finally have "j (mul (invg ?r1) ?r2) = eH" .
          hence "mul (invg ?r1) ?r2 \<in> {x \<in> G. j x = eH}"
            using group_mul_closed[OF hG hinvr1 hr2] by (by100 blast)
          thus ?thesis using hj_ker unfolding top1_group_kernel_on_def by (by100 simp)
        qed
        thus "C1 = C2" using normal_coset_eq[OF hG hN hr1 hr2] hC1_eq hC2_eq by (by100 simp)
      qed
    next
      \<comment> \<open>Surjectivity: for h \<in> H, take g \<in> G with j(g) = h. Then j_bar(coset g) = h.\<close>
      show "?j_bar ` ?Q = H"
      proof (rule set_eqI)
        fix h show "h \<in> ?j_bar ` ?Q \<longleftrightarrow> h \<in> H"
        proof
          assume "h \<in> ?j_bar ` ?Q"
          then obtain C where hC: "C \<in> ?Q" and heq: "h = ?j_bar C" by (by100 blast)
          have "(SOME g. g \<in> G \<and> C = top1_group_coset_on G mul N g) \<in> G"
            using hsome[OF hC] by (by100 blast)
          thus "h \<in> H" using heq hj_hom unfolding top1_group_hom_on_def by (by100 blast)
        next
          assume "h \<in> H"
          then obtain g where hg: "g \<in> G" and hgj: "j g = h"
            using hj_surj by (by100 force)
          let ?C = "top1_group_coset_on G mul N g"
          have hCQ: "?C \<in> ?Q" unfolding top1_quotient_group_carrier_on_def
            using hg by (by100 blast)
          let ?r = "SOME ga. ga \<in> G \<and> ?C = top1_group_coset_on G mul N ga"
          have hr: "?r \<in> G" and hr_eq: "?C = top1_group_coset_on G mul N ?r"
            using hsome[OF hCQ] by (by100 blast)+
          have "j ?r = j g" by (rule hj_wd[OF hr hg hr_eq[symmetric]])
          hence "?j_bar ?C = h" using hgj by (by100 simp)
          thus "h \<in> ?j_bar ` ?Q" using hCQ by (by100 blast)
        qed
      qed
    qed
  qed
  hence hiso: "top1_groups_isomorphic_on ?Q ?mulQ H mulH"
    unfolding top1_groups_isomorphic_on_def by (by100 blast)
  show ?thesis
    by (rule top1_groups_isomorphic_on_sym[OF hiso
          quotient_group_is_group[OF hG hN] hH])
qed

text \<open>General abelianization: for any group G, the quotient G/[G,G] is the abelianization.
  Stated without existentials for ease of application.\<close>
lemma abelianization_concrete:
  assumes hG: "top1_is_group_on G mul e invg"
  shows "top1_is_abelianization_of
      (top1_quotient_group_carrier_on G mul (top1_commutator_subgroup_on G mul e invg))
      (top1_quotient_group_mul_on mul)
      (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) e)
      (\<lambda>C. top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg)
         (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul
            (top1_commutator_subgroup_on G mul e invg) g)))
      G mul e invg
      (\<lambda>g. top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) g)"
proof -
  let ?N = "top1_commutator_subgroup_on G mul e invg"
  have hN: "top1_normal_subgroup_on G mul e invg ?N"
    by (rule commutator_subgroup_is_normal[OF hG])
  have hNsub: "?N \<subseteq> G" using hN unfolding top1_normal_subgroup_on_def by (by100 blast)
  have hN_grp: "top1_is_group_on ?N mul e invg"
    using hN unfolding top1_normal_subgroup_on_def by (by100 blast)
  let ?invgH = "\<lambda>C. top1_group_coset_on G mul ?N
      (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul ?N g))"
  have h_grp: "top1_is_group_on (top1_quotient_group_carrier_on G mul ?N)
      (top1_quotient_group_mul_on mul) (top1_group_coset_on G mul ?N e) ?invgH"
    by (rule quotient_group_is_group[OF hG hN])
  have h_abel_comm: "\<forall>a\<in>G. \<forall>b\<in>G.
      top1_quotient_group_mul_on mul (top1_group_coset_on G mul ?N a) (top1_group_coset_on G mul ?N b)
    = top1_quotient_group_mul_on mul (top1_group_coset_on G mul ?N b) (top1_group_coset_on G mul ?N a)"
    by (rule quotient_by_commutator_is_abelian[OF hG])
  have h_abelian: "top1_is_abelian_group_on (top1_quotient_group_carrier_on G mul ?N)
      (top1_quotient_group_mul_on mul) (top1_group_coset_on G mul ?N e) ?invgH"
    unfolding top1_is_abelian_group_on_def
  proof (intro conjI ballI)
    show "top1_is_group_on (top1_quotient_group_carrier_on G mul ?N)
        (top1_quotient_group_mul_on mul) (top1_group_coset_on G mul ?N e) ?invgH"
      by (rule h_grp)
  next
    fix C1 C2
    assume "C1 \<in> top1_quotient_group_carrier_on G mul ?N"
       and "C2 \<in> top1_quotient_group_carrier_on G mul ?N"
    then obtain g1 g2 where "g1 \<in> G" "C1 = top1_group_coset_on G mul ?N g1"
        "g2 \<in> G" "C2 = top1_group_coset_on G mul ?N g2"
      unfolding top1_quotient_group_carrier_on_def by (by100 blast)
    thus "top1_quotient_group_mul_on mul C1 C2 = top1_quotient_group_mul_on mul C2 C1"
      using h_abel_comm by (by100 simp)
  qed
  show ?thesis unfolding top1_is_abelianization_of_def
    using h_abelian hG
      quotient_projection_properties(1)[OF hG hN]
      quotient_projection_properties(2)[OF hG hN]
      quotient_projection_properties(3)[OF hG hN]
      coset_e_is_N[OF hG hNsub hN_grp] by (by100 blast)
qed

text \<open>Forward declaration: first isomorphism theorem — now proved above, so this
  is just a thin wrapper.\<close>
lemma first_isomorphism_theorem_forward:
  assumes "top1_is_group_on G mul e invg"
      and "top1_normal_subgroup_on G mul e invg N"
      and "top1_is_group_on H mulH eH invgH"
      and "top1_group_hom_on G mul H mulH j"
      and "j ` G = H"
      and "top1_group_kernel_on G eH j = N"
  shows "top1_groups_isomorphic_on H mulH
      (top1_quotient_group_carrier_on G mul N) (top1_quotient_group_mul_on mul)"
  by (rule first_isomorphism_theorem[OF assms])


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

(** from \<S>68 Theorem 68.2: given a family of groups, a free product exists.
    The carrier is ('i \<times> 'gg) list: reduced words (index, element) pairs. **)
theorem Theorem_68_2_free_product_exists:
  assumes hgroups: "\<forall>\<alpha>\<in>(J::'i set). top1_is_group_on (GG \<alpha>::'gg set) (mulGG \<alpha>) (eGG \<alpha>) (invgGG \<alpha>)"
  shows "\<exists>(G::('i \<times> 'gg) list set) mul e invg
         (\<iota>fam :: 'i \<Rightarrow> 'gg \<Rightarrow> ('i \<times> 'gg) list).
           top1_is_free_product_on G mul e invg GG mulGG \<iota>fam J"
proof -
  \<comment> \<open>Carrier: reduced words. A word is a list [(\<alpha>1,g1), (\<alpha>2,g2), ...] where
     \<alpha>k \<in> J, gk \<in> GG(\<alpha>k) \ {eGG(\<alpha>k)}, and consecutive indices differ.
     The empty list [] is the identity.\<close>
  define G :: "('i \<times> 'gg) list set" where
    "G = {ws. (\<forall>i<length ws. fst (ws!i) \<in> J \<and> snd (ws!i) \<in> GG (fst (ws!i))
                           \<and> snd (ws!i) \<noteq> eGG (fst (ws!i)))
            \<and> (\<forall>i. i+1 < length ws \<longrightarrow> fst (ws!i) \<noteq> fst (ws!(i+1)))}"
  define e :: "('i \<times> 'gg) list" where "e = []"
  \<comment> \<open>Natural inclusions: \<iota>\<alpha>(g) = [(\<alpha>, g)] for g \<noteq> e\<alpha>, and \<iota>\<alpha>(e\<alpha>) = [].\<close>
  define \<iota>fam :: "'i \<Rightarrow> 'gg \<Rightarrow> ('i \<times> 'gg) list" where
    "\<iota>fam = (\<lambda>\<alpha> g. if g = eGG \<alpha> then [] else [(\<alpha>, g)])"
  \<comment> \<open>Prepend a single element to a reduced word, reducing at the junction.\<close>
  define prepend :: "'i \<times> 'gg \<Rightarrow> ('i \<times> 'gg) list \<Rightarrow> ('i \<times> 'gg) list" where
    "prepend = (\<lambda>(\<alpha>, g) ws.
       if g = eGG \<alpha> then ws  \<comment> \<open>Skip identity elements.\<close>
       else case ws of
         [] \<Rightarrow> [(\<alpha>, g)]
       | ((\<beta>, h) # rest) \<Rightarrow>
           if \<alpha> = \<beta> then
             let gh = mulGG \<alpha> g h in
             if gh = eGG \<alpha> then rest
             else (\<alpha>, gh) # rest
           else (\<alpha>, g) # ws)"
  \<comment> \<open>Multiplication: prepend each element of the first word onto the second.\<close>
  define mul :: "('i \<times> 'gg) list \<Rightarrow> ('i \<times> 'gg) list \<Rightarrow> ('i \<times> 'gg) list" where
    "mul = (\<lambda>ws1 ws2. foldr prepend ws1 ws2)"
  \<comment> \<open>Inverse: reverse the list and invert each element.\<close>
  define invg :: "('i \<times> 'gg) list \<Rightarrow> ('i \<times> 'gg) list" where
    "invg = (\<lambda>ws. rev (map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) ws))"
  \<comment> \<open>Need to verify:
     (1) G is closed under mul and invg (reduced words \<rightarrow> reduced words)
     (2) Group axioms: associativity, identity, inverse
     (3) \<iota>fam are injective homomorphisms
     (4) G = subgroup generated by \<Union> \<iota>fam images
     (5) Freeness: no nontrivial reduced word equals e
     Each requires careful list algebra. Key facts:
     - prepend preserves reducedness
     - mul(ws, []) = ws (right identity)
     - mul([], ws) = ws (left identity by foldr)
     - mul(invg ws, ws) = [] (inverse property via cancellation)
     - Associativity of mul (the hardest part)\<close>
  \<comment> \<open>Key helper: prepend preserves reducedness.\<close>
  \<comment> \<open>G membership helpers to avoid repeated G_def unfolding.\<close>
  have hG_elem: "\<And>ws i. ws \<in> G \<Longrightarrow> i < length ws \<Longrightarrow>
      fst (ws!i) \<in> J \<and> snd (ws!i) \<in> GG (fst (ws!i)) \<and> snd (ws!i) \<noteq> eGG (fst (ws!i))"
    unfolding G_def by (by100 blast)
  have hG_alt: "\<And>ws i. ws \<in> G \<Longrightarrow> i + 1 < length ws \<Longrightarrow> fst (ws!i) \<noteq> fst (ws!(i+1))"
    unfolding G_def by (by100 blast)
  have hG_intro: "\<And>ws. (\<forall>i<length ws. fst (ws!i) \<in> J \<and> snd (ws!i) \<in> GG (fst (ws!i))
                           \<and> snd (ws!i) \<noteq> eGG (fst (ws!i)))
            \<Longrightarrow> (\<forall>i. i+1 < length ws \<longrightarrow> fst (ws!i) \<noteq> fst (ws!(i+1)))
            \<Longrightarrow> ws \<in> G"
    unfolding G_def by (by100 blast)
  have htail_G: "\<And>p ws. p # ws \<in> G \<Longrightarrow> ws \<in> G"
  proof -
    fix p ws assume hpws: "p # ws \<in> G"
    show "ws \<in> G"
    proof (rule hG_intro)
      show "\<forall>i<length ws. fst (ws!i) \<in> J \<and> snd (ws!i) \<in> GG (fst (ws!i)) \<and> snd (ws!i) \<noteq> eGG (fst (ws!i))"
      proof (intro allI impI)
        fix i assume "i < length ws"
        hence "Suc i < length (p # ws)" by (by100 simp)
        from hG_elem[OF hpws this] show "fst (ws!i) \<in> J \<and> snd (ws!i) \<in> GG (fst (ws!i)) \<and> snd (ws!i) \<noteq> eGG (fst (ws!i))"
          by (by100 simp)
      qed
    next
      show "\<forall>i. i + 1 < length ws \<longrightarrow> fst (ws!i) \<noteq> fst (ws!(i+1))"
      proof (intro allI impI)
        fix i assume "i + 1 < length ws"
        hence "Suc i + 1 < length (p # ws)" by (by100 simp)
        from hG_alt[OF hpws this] show "fst (ws!i) \<noteq> fst (ws!(i+1))" by (by100 simp)
      qed
    qed
  qed
  have hprepend_reduced: "\<And>\<alpha> g ws. \<alpha> \<in> J \<Longrightarrow> g \<in> GG \<alpha> \<Longrightarrow> ws \<in> G \<Longrightarrow>
      prepend (\<alpha>, g) ws \<in> G"
  proof -
    fix \<alpha> :: 'i and g :: 'gg and ws :: "('i \<times> 'gg) list"
    assume h\<alpha>: "\<alpha> \<in> J" and hg: "g \<in> GG \<alpha>" and hws: "ws \<in> G"
    show "prepend (\<alpha>, g) ws \<in> G"
    proof (cases "g = eGG \<alpha>")
      case True thus ?thesis unfolding prepend_def using hws by (by100 simp)
    next
      case hgne: False
      show ?thesis
      proof (cases ws)
        case Nil
        have "[(\<alpha>, g)] \<in> G"
        proof (rule hG_intro)
          show "\<forall>i<length [(\<alpha>, g)]. fst ([(\<alpha>, g)]!i) \<in> J \<and> snd ([(\<alpha>, g)]!i) \<in> GG (fst ([(\<alpha>, g)]!i))
              \<and> snd ([(\<alpha>, g)]!i) \<noteq> eGG (fst ([(\<alpha>, g)]!i))"
            using h\<alpha> hg hgne by (by100 simp)
          show "\<forall>i. i+1 < length [(\<alpha>, g)] \<longrightarrow> fst ([(\<alpha>, g)]!i) \<noteq> fst ([(\<alpha>, g)]!(i+1))"
            by (by100 simp)
        qed
        thus ?thesis unfolding Nil prepend_def using hgne by (by100 simp)
      next
        case (Cons p rest)
        obtain \<beta> h where hp: "p = (\<beta>, h)" by (cases p)
        have hrest_G: "rest \<in> G"
        proof -
          have "p # rest \<in> G" using hws unfolding Cons by (by100 simp)
          thus ?thesis by (rule htail_G)
        qed
        show ?thesis
        proof (cases "\<alpha> = \<beta>")
          case hdiff: False
          have hprep: "prepend (\<alpha>, g) ws = (\<alpha>, g) # ws"
            unfolding Cons hp prepend_def using hgne hdiff by (by100 simp)
          show ?thesis unfolding hprep
          proof (rule hG_intro)
            show "\<forall>i<length ((\<alpha>,g)#ws). fst (((\<alpha>,g)#ws)!i) \<in> J \<and> snd (((\<alpha>,g)#ws)!i) \<in> GG (fst (((\<alpha>,g)#ws)!i))
                \<and> snd (((\<alpha>,g)#ws)!i) \<noteq> eGG (fst (((\<alpha>,g)#ws)!i))"
            proof (intro allI impI)
              fix i assume "i < length ((\<alpha>,g)#ws)"
              thus "fst (((\<alpha>,g)#ws)!i) \<in> J \<and> snd (((\<alpha>,g)#ws)!i) \<in> GG (fst (((\<alpha>,g)#ws)!i))
                  \<and> snd (((\<alpha>,g)#ws)!i) \<noteq> eGG (fst (((\<alpha>,g)#ws)!i))"
                using h\<alpha> hg hgne hG_elem[OF hws] by (cases i) (by100 simp)+
            qed
          next
            show "\<forall>i. i+1 < length ((\<alpha>,g)#ws) \<longrightarrow> fst (((\<alpha>,g)#ws)!i) \<noteq> fst (((\<alpha>,g)#ws)!(i+1))"
            proof (intro allI impI)
              fix i assume "i+1 < length ((\<alpha>,g)#ws)"
              thus "fst (((\<alpha>,g)#ws)!i) \<noteq> fst (((\<alpha>,g)#ws)!(i+1))"
                using hdiff hG_alt[OF hws] unfolding Cons hp by (cases i) (by100 simp)+
            qed
          qed
        next
          case hsame: True
          let ?gh = "mulGG \<alpha> g h"
          have hgrp: "top1_is_group_on (GG \<alpha>) (mulGG \<alpha>) (eGG \<alpha>) (invgGG \<alpha>)"
            using hgroups h\<alpha> by (by100 blast)
          have hh_in: "h \<in> GG \<alpha>" using hG_elem[OF hws, of 0] unfolding Cons hp hsame by (by100 simp)
          have hgh_in: "?gh \<in> GG \<alpha>" using hgrp hg hh_in unfolding top1_is_group_on_def by (by100 blast)
          show ?thesis
          proof (cases "?gh = eGG \<alpha>")
            case True
            have "prepend (\<alpha>, g) ws = rest" unfolding Cons hp prepend_def using hgne hsame True by (by100 simp)
            thus ?thesis using hrest_G by (by100 simp)
          next
            case ghne: False
            have hprep: "prepend (\<alpha>, g) ws = (\<alpha>, ?gh) # rest"
              unfolding Cons hp prepend_def using hgne hsame ghne by (by100 simp)
            show ?thesis unfolding hprep
            proof (rule hG_intro)
              show "\<forall>i<length ((\<alpha>,?gh)#rest). fst (((\<alpha>,?gh)#rest)!i) \<in> J \<and> snd (((\<alpha>,?gh)#rest)!i) \<in> GG (fst (((\<alpha>,?gh)#rest)!i))
                  \<and> snd (((\<alpha>,?gh)#rest)!i) \<noteq> eGG (fst (((\<alpha>,?gh)#rest)!i))"
              proof (intro allI impI)
                fix i assume "i < length ((\<alpha>,?gh)#rest)"
                thus "fst (((\<alpha>,?gh)#rest)!i) \<in> J \<and> snd (((\<alpha>,?gh)#rest)!i) \<in> GG (fst (((\<alpha>,?gh)#rest)!i))
                    \<and> snd (((\<alpha>,?gh)#rest)!i) \<noteq> eGG (fst (((\<alpha>,?gh)#rest)!i))"
                  using h\<alpha> hgh_in ghne hG_elem[OF hrest_G] by (cases i) (by100 simp)+
              qed
            next
              show "\<forall>i. i+1 < length ((\<alpha>,?gh)#rest) \<longrightarrow> fst (((\<alpha>,?gh)#rest)!i) \<noteq> fst (((\<alpha>,?gh)#rest)!(i+1))"
              proof (intro allI impI)
                fix i assume "i+1 < length ((\<alpha>,?gh)#rest)"
                show "fst (((\<alpha>,?gh)#rest)!i) \<noteq> fst (((\<alpha>,?gh)#rest)!(i+1))"
                proof (cases i)
                  case 0
                  show ?thesis
                  proof (cases rest)
                    case Nil thus ?thesis using \<open>i+1 < _\<close> unfolding 0 by (by100 simp)
                  next
                    case (Cons q rest2)
                    have "\<alpha> \<noteq> fst q"
                    proof -
                      have "0 + 1 < length ws"
                      proof -
                        have "length ws = Suc (Suc (length rest2))"
                          unfolding \<open>ws = _\<close> hp \<open>rest = _\<close> by (by100 simp)
                        thus ?thesis by (by100 simp)
                      qed
                      from hG_alt[OF hws this] have "fst (ws!0) \<noteq> fst (ws!1)" by (by100 simp)
                      moreover have "fst (ws!0) = \<beta>" unfolding \<open>ws = _\<close> hp by (by100 simp)
                      moreover have "fst (ws!1) = fst q" unfolding \<open>ws = _\<close> hp \<open>rest = _\<close> by (by100 simp)
                      ultimately have "\<beta> \<noteq> fst q" by (by100 simp)
                      thus ?thesis using hsame by (by100 simp)
                    qed
                    thus ?thesis unfolding 0 Cons by (by100 simp)
                  qed
                next
                  case (Suc j)
                  thus ?thesis using hG_alt[OF hrest_G] \<open>i+1 < _\<close> by (by100 simp)
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  \<comment> \<open>Helper: prepend with different index just conses.\<close>
  have hprepend_cons: "\<And>\<alpha> g ws. g \<noteq> eGG \<alpha> \<Longrightarrow> ws = [] \<or> \<alpha> \<noteq> fst (hd ws) \<Longrightarrow>
      prepend (\<alpha>, g) ws = (\<alpha>, g) # ws"
  proof -
    fix \<alpha> :: 'i and g :: 'gg and ws :: "('i \<times> 'gg) list"
    assume hg: "g \<noteq> eGG \<alpha>" and hdiff: "ws = [] \<or> \<alpha> \<noteq> fst (hd ws)"
    show "prepend (\<alpha>, g) ws = (\<alpha>, g) # ws"
    proof (cases ws)
      case Nil thus ?thesis unfolding prepend_def using hg by (by100 simp)
    next
      case (Cons p rest)
      have "\<alpha> \<noteq> fst p" using hdiff unfolding Cons by (by100 simp)
      thus ?thesis unfolding prepend_def Cons using hg by (cases p) (by100 simp)
    qed
  qed
  \<comment> \<open>(1) e \<in> G: empty list is reduced.\<close>
  have he_G: "e \<in> G" unfolding e_def G_def by (by100 simp)
  \<comment> \<open>(2) Left identity: mul e ws = ws.\<close>
  have hleft_id: "\<forall>ws\<in>G. mul e ws = ws" unfolding mul_def e_def by (by100 simp)
  \<comment> \<open>(3) Right identity: mul ws e = ws for ws \<in> G.\<close>
  have hright_id: "\<forall>ws\<in>G. mul ws e = ws"
  proof (intro ballI)
    fix ws assume hws: "ws \<in> G"
    show "mul ws e = ws" unfolding mul_def e_def
      using hws
    proof (induction ws)
      case Nil show ?case by (by100 simp)
    next
      case (Cons p ws')
      \<comment> \<open>Cons.prems gives p # ws' \<in> G.\<close>
      have hpws: "p # ws' \<in> G" using Cons.prems .
      have hws': "ws' \<in> G" by (rule htail_G[OF hpws])
      have hIH: "foldr prepend ws' [] = ws'" using Cons.IH[OF hws'] .
      obtain \<alpha> g where hp: "p = (\<alpha>, g)" by (cases p)
      have hgne: "g \<noteq> eGG \<alpha>" using hG_elem[OF hpws, of 0] unfolding hp by (by100 simp)
      have hdiff: "ws' = [] \<or> \<alpha> \<noteq> fst (hd ws')"
      proof (cases ws')
        case Nil thus ?thesis by (by100 blast)
      next
        case (Cons q rest)
        have "0 + 1 < length (p # ws')" unfolding Cons by (by100 simp)
        from hG_alt[OF hpws this] have "fst p \<noteq> fst (ws'!0)" by (by100 simp)
        thus ?thesis unfolding Cons hp by (by100 simp)
      qed
      have "foldr prepend (p # ws') [] = prepend p (foldr prepend ws' [])" by (by100 simp)
      also have "foldr prepend ws' [] = ws'" by (rule hIH)
      also have "prepend p ws' = p # ws'"
        unfolding hp using hprepend_cons[OF hgne hdiff] .
      finally show ?case .
    qed
  qed
  \<comment> \<open>(4) Closure under mul.\<close>
  have hmul_closed: "\<forall>ws1\<in>G. \<forall>ws2\<in>G. mul ws1 ws2 \<in> G"
  proof (intro ballI)
    fix ws1 ws2 assume hws1: "ws1 \<in> G" and hws2: "ws2 \<in> G"
    show "mul ws1 ws2 \<in> G" unfolding mul_def
      using hws1
    proof (induction ws1)
      case Nil show ?case using hws2 by (by100 simp)
    next
      case (Cons p ws1')
      obtain \<alpha> g where hp: "p = (\<alpha>, g)" by (cases p)
      have hpws1: "p # ws1' \<in> G" using Cons.prems .
      have h\<alpha>: "\<alpha> \<in> J" and hg: "g \<in> GG \<alpha>"
        using hG_elem[OF hpws1, of 0] unfolding hp by (by100 simp)+
      have hws1': "ws1' \<in> G" by (rule htail_G[OF hpws1])
      have hIH: "foldr prepend ws1' ws2 \<in> G" using Cons.IH[OF hws1'] .
      show ?case unfolding hp by (by100 simp) (rule hprepend_reduced[OF h\<alpha> hg hIH])
    qed
  qed
  \<comment> \<open>(5) Inverse closure.\<close>
  \<comment> \<open>Helper: map (coordinatewise inverse) preserves G.\<close>
  have hmap_inv_G: "\<And>ws. ws \<in> G \<Longrightarrow> map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) ws \<in> G"
  proof -
    fix ws assume hws: "ws \<in> G"
    let ?ws' = "map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) ws"
    show "?ws' \<in> G"
    proof (rule hG_intro)
      show "\<forall>i<length ?ws'. fst (?ws'!i) \<in> J \<and> snd (?ws'!i) \<in> GG (fst (?ws'!i))
          \<and> snd (?ws'!i) \<noteq> eGG (fst (?ws'!i))"
      proof (intro allI impI)
        fix i assume hi: "i < length ?ws'"
        hence hi': "i < length ws" by (by100 simp)
        have helem: "fst (ws!i) \<in> J \<and> snd (ws!i) \<in> GG (fst (ws!i)) \<and> snd (ws!i) \<noteq> eGG (fst (ws!i))"
          using hG_elem[OF hws hi'] .
        have hgrp: "top1_is_group_on (GG (fst (ws!i))) (mulGG (fst (ws!i))) (eGG (fst (ws!i))) (invgGG (fst (ws!i)))"
          using hgroups helem by (by100 blast)
        have hfst: "fst (?ws'!i) = fst (ws!i)"
          using hi' by (cases "ws!i") (by100 simp)
        have hsnd: "snd (?ws'!i) = invgGG (fst (ws!i)) (snd (ws!i))"
          using hi' by (cases "ws!i") (by100 simp)
        have "invgGG (fst (ws!i)) (snd (ws!i)) \<in> GG (fst (ws!i))"
          using hgrp helem unfolding top1_is_group_on_def by (by100 blast)
        moreover have "invgGG (fst (ws!i)) (snd (ws!i)) \<noteq> eGG (fst (ws!i))"
        proof
          assume heq: "invgGG (fst (ws!i)) (snd (ws!i)) = eGG (fst (ws!i))"
          have "mulGG (fst (ws!i)) (invgGG (fst (ws!i)) (snd (ws!i))) (snd (ws!i)) = eGG (fst (ws!i))"
            using hgrp helem unfolding top1_is_group_on_def by (by100 blast)
          hence "mulGG (fst (ws!i)) (eGG (fst (ws!i))) (snd (ws!i)) = eGG (fst (ws!i))"
            using heq by (by100 simp)
          moreover have "mulGG (fst (ws!i)) (eGG (fst (ws!i))) (snd (ws!i)) = snd (ws!i)"
            using hgrp helem unfolding top1_is_group_on_def by (by100 blast)
          ultimately have "snd (ws!i) = eGG (fst (ws!i))" by (by100 simp)
          thus False using helem by (by100 simp)
        qed
        ultimately show "fst (?ws'!i) \<in> J \<and> snd (?ws'!i) \<in> GG (fst (?ws'!i))
            \<and> snd (?ws'!i) \<noteq> eGG (fst (?ws'!i))"
          unfolding hfst hsnd using helem by (by100 blast)
      qed
    next
      show "\<forall>i. i+1 < length ?ws' \<longrightarrow> fst (?ws'!i) \<noteq> fst (?ws'!(i+1))"
      proof (intro allI impI)
        fix i assume hi: "i+1 < length ?ws'"
        hence hi': "i+1 < length ws" by (by100 simp)
        have "fst (?ws'!i) = fst (ws!i)" using hi' by (cases "ws!i") (by100 simp)
        moreover have "fst (?ws'!(i+1)) = fst (ws!(i+1))" using hi' by (cases "ws!(i+1)") (by100 simp)
        moreover have "fst (ws!i) \<noteq> fst (ws!(i+1))" using hG_alt[OF hws] hi' by (by100 blast)
        ultimately show "fst (?ws'!i) \<noteq> fst (?ws'!(i+1))" by (by100 simp)
      qed
    qed
  qed
  \<comment> \<open>Helper: rev preserves G.\<close>
  have hrev_G: "\<And>ws. ws \<in> G \<Longrightarrow> rev ws \<in> G"
  proof -
    fix ws assume hws: "ws \<in> G"
    show "rev ws \<in> G"
    proof (rule hG_intro)
      show "\<forall>i<length (rev ws). fst ((rev ws)!i) \<in> J \<and> snd ((rev ws)!i) \<in> GG (fst ((rev ws)!i))
          \<and> snd ((rev ws)!i) \<noteq> eGG (fst ((rev ws)!i))"
      proof (intro allI impI)
        fix i assume hi: "i < length (rev ws)"
        hence hi_ws: "i < length ws" by (by100 simp)
        hence hi': "length ws - 1 - i < length ws" by (by100 linarith)
        have hrev_eq: "(rev ws)!i = ws!(length ws - Suc i)" using rev_nth[OF hi_ws] .
        have hi'': "length ws - Suc i < length ws" using hi_ws by (by100 linarith)
        show "fst ((rev ws)!i) \<in> J \<and> snd ((rev ws)!i) \<in> GG (fst ((rev ws)!i))
            \<and> snd ((rev ws)!i) \<noteq> eGG (fst ((rev ws)!i))"
          unfolding hrev_eq using hG_elem[OF hws hi''] .
      qed
    next
      show "\<forall>i. i+1 < length (rev ws) \<longrightarrow> fst ((rev ws)!i) \<noteq> fst ((rev ws)!(i+1))"
      proof (intro allI impI)
        fix i assume hi: "i+1 < length (rev ws)"
        hence hi': "i+1 < length ws" and hi_ws: "i < length ws" by (by100 simp)+
        have hrev_i: "(rev ws)!i = ws!(length ws - Suc i)" using rev_nth[OF hi_ws] .
        have hi1_ws: "i+1 < length ws" using hi' .
        have hrev_i1: "(rev ws)!(i+1) = ws!(length ws - Suc (i+1))" using rev_nth[OF hi1_ws] .
        have hj_eq: "length ws - Suc (i+1) + 1 = length ws - Suc i"
          using hi' by (by100 linarith)
        have hj_lt: "length ws - Suc (i+1) + 1 < length ws" using hi' by (by100 linarith)
        have "fst (ws!(length ws - Suc (i+1))) \<noteq> fst (ws!(length ws - Suc (i+1) + 1))"
          using hG_alt[OF hws hj_lt] .
        hence "fst (ws!(length ws - Suc (i+1))) \<noteq> fst (ws!(length ws - Suc i))"
          unfolding hj_eq .
        hence "fst ((rev ws)!(i+1)) \<noteq> fst ((rev ws)!i)"
          unfolding hrev_i hrev_i1 .
        thus "fst ((rev ws)!i) \<noteq> fst ((rev ws)!(i+1))" by (rule not_sym)
      qed
    qed
  qed
  have hinvg_closed: "\<forall>ws\<in>G. invg ws \<in> G"
  proof (intro ballI)
    fix ws assume "ws \<in> G"
    have "map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) ws \<in> G" by (rule hmap_inv_G[OF \<open>ws \<in> G\<close>])
    thus "invg ws \<in> G" unfolding invg_def by (rule hrev_G)
  qed
  \<comment> \<open>(6) Associativity: mul (mul x y) z = mul x (mul y z).\<close>
  \<comment> \<open>Key helper for associativity: prepend distributes over mul on the left.\<close>
  \<comment> \<open>Prepend composition: prepend (\<alpha>,g) (prepend (\<alpha>,h) z) = prepend (\<alpha>,g\<cdot>h) z.\<close>
  have hprepend_compose: "\<And>\<alpha> g h z. \<alpha> \<in> J \<Longrightarrow> g \<in> GG \<alpha> \<Longrightarrow> g \<noteq> eGG \<alpha> \<Longrightarrow>
      h \<in> GG \<alpha> \<Longrightarrow> h \<noteq> eGG \<alpha> \<Longrightarrow> z \<in> G \<Longrightarrow>
      prepend (\<alpha>, g) (prepend (\<alpha>, h) z) = prepend (\<alpha>, mulGG \<alpha> g h) z"
  proof -
    fix \<alpha> :: 'i and g h :: 'gg and z :: "('i \<times> 'gg) list"
    assume h\<alpha>: "\<alpha> \<in> J" and hg: "g \<in> GG \<alpha>" and hgne: "g \<noteq> eGG \<alpha>"
        and hh: "h \<in> GG \<alpha>" and hhne: "h \<noteq> eGG \<alpha>" and hz: "z \<in> G"
    have hgrp: "top1_is_group_on (GG \<alpha>) (mulGG \<alpha>) (eGG \<alpha>) (invgGG \<alpha>)"
      using hgroups h\<alpha> by (by100 blast)
    have hgh: "mulGG \<alpha> g h \<in> GG \<alpha>" using hgrp hg hh unfolding top1_is_group_on_def by (by100 blast)
    show "prepend (\<alpha>, g) (prepend (\<alpha>, h) z) = prepend (\<alpha>, mulGG \<alpha> g h) z"
    proof (cases z)
      case Nil
      \<comment> \<open>z = []: prepend (\<alpha>,h) [] = [(\<alpha>,h)]. Merge: g\<cdot>h.\<close>
      show ?thesis unfolding Nil prepend_def using hgne hhne by (by100 simp)
    next
      case (Cons q rest)
      obtain \<beta> k where hq: "q = (\<beta>, k)" by (cases q)
      show ?thesis
      proof (cases "\<alpha> = \<beta>")
        case hdiff: False
        \<comment> \<open>\<alpha> \<noteq> \<beta>: inner = (\<alpha>,h)#z, outer merges g with h.\<close>
        show ?thesis unfolding Cons hq prepend_def using hgne hhne hdiff by (by100 simp)
      next
        case hsame: True
        have hk: "k \<in> GG \<alpha>" using hG_elem[OF hz, of 0] unfolding Cons hq hsame by (by100 simp)
        have hkne: "k \<noteq> eGG \<alpha>" using hG_elem[OF hz, of 0] unfolding Cons hq hsame by (by100 simp)
        have hassoc_grp: "mulGG \<alpha> (mulGG \<alpha> g h) k = mulGG \<alpha> g (mulGG \<alpha> h k)"
          using hgrp hg hh hk unfolding top1_is_group_on_def by (by100 blast)
        have hhk: "mulGG \<alpha> h k \<in> GG \<alpha>" using hgrp hh hk unfolding top1_is_group_on_def by (by100 blast)
        have hrest: "rest \<in> G"
        proof -
          have "q # rest \<in> G" using hz unfolding Cons by (by100 simp)
          thus ?thesis by (rule htail_G)
        qed
        show ?thesis
        proof (cases "mulGG \<alpha> h k = eGG \<alpha>")
          case hhk_e: True
          \<comment> \<open>h\<cdot>k = e. Inner = rest. (g\<cdot>h)\<cdot>k = g\<cdot>(h\<cdot>k) = g.\<close>
          have hghk: "mulGG \<alpha> (mulGG \<alpha> g h) k = g"
          proof -
            have "mulGG \<alpha> (mulGG \<alpha> g h) k = mulGG \<alpha> g (mulGG \<alpha> h k)" by (rule hassoc_grp)
            also have "mulGG \<alpha> h k = eGG \<alpha>" by (rule hhk_e)
            also have "mulGG \<alpha> g (eGG \<alpha>) = g" using hgrp hg unfolding top1_is_group_on_def by (by100 blast)
            finally show ?thesis .
          qed
          have hinner: "prepend (\<alpha>, h) z = rest"
            unfolding Cons hq hsame[symmetric] prepend_def using hhne hsame hhk_e by (by100 simp)
          have hdiff_rest: "rest = [] \<or> \<alpha> \<noteq> fst (hd rest)"
          proof (cases rest)
            case Nil thus ?thesis by (by100 blast)
          next
            case (Cons r rest2)
            have "fst q \<noteq> fst r" using hG_alt[OF hz, of 0] unfolding \<open>z = _\<close> Cons by (by100 simp)
            thus ?thesis unfolding hq hsame Cons by (by100 simp)
          qed
          show ?thesis
          proof (cases "mulGG \<alpha> g h = eGG \<alpha>")
            case True
            \<comment> \<open>g\<cdot>h = e. Then (g\<cdot>h)\<cdot>k = e\<cdot>k = k. But also = g, so g = k.
               RHS = prepend (\<alpha>, e) z = z = (q#rest). LHS = prepend (\<alpha>,g) rest.\<close>
            have "g = k"
            proof -
              have "mulGG \<alpha> (mulGG \<alpha> g h) k = g" by (rule hghk)
              moreover have "mulGG \<alpha> (eGG \<alpha>) k = k" using hgrp hk unfolding top1_is_group_on_def by (by100 blast)
              ultimately show ?thesis using True by (by100 simp)
            qed
            have hrhs: "prepend (\<alpha>, mulGG \<alpha> g h) z = z" unfolding prepend_def using True by (by100 simp)
            have hlhs: "prepend (\<alpha>, g) (prepend (\<alpha>, h) z) = z"
            proof -
              have "prepend (\<alpha>, g) (prepend (\<alpha>, h) z) = prepend (\<alpha>, g) rest" using hinner by (by100 simp)
              also have "\<dots> = (\<alpha>, g) # rest" using hprepend_cons[OF hgne hdiff_rest] .
              also have "\<dots> = (\<alpha>, k) # rest" using \<open>g = k\<close> by (by100 simp)
              also have "\<dots> = q # rest" unfolding hq hsame by (by100 simp)
              also have "\<dots> = z" unfolding Cons by (by100 simp)
              finally show ?thesis .
            qed
            show ?thesis using hlhs hrhs by (by100 simp)
          next
            case ghne: False
            \<comment> \<open>g\<cdot>h \<noteq> e. RHS = prepend (\<alpha>, g\<cdot>h) ((q)#rest).\<close>
            \<comment> \<open>Both sides equal (\<alpha>, g) # rest via hghk (= g, non-identity).\<close>
            have hrhs: "prepend (\<alpha>, mulGG \<alpha> g h) z = (\<alpha>, g) # rest"
            proof -
              have "prepend (\<alpha>, mulGG \<alpha> g h) z =
                  (let v = mulGG \<alpha> (mulGG \<alpha> g h) k in if v = eGG \<alpha> then rest else (\<alpha>, v) # rest)"
              proof -
                have "prepend (\<alpha>, mulGG \<alpha> g h) ((\<alpha>, k) # rest) =
                    (let gh = mulGG \<alpha> (mulGG \<alpha> g h) k in if gh = eGG \<alpha> then rest else (\<alpha>, gh) # rest)"
                  unfolding prepend_def using ghne by (by100 simp)
                thus ?thesis unfolding Cons hq hsame by (by100 simp)
              qed
              thus ?thesis unfolding hghk using hgne by (by100 simp)
            qed
            moreover have hlhs: "prepend (\<alpha>, g) (prepend (\<alpha>, h) z) = (\<alpha>, g) # rest"
              using hinner hprepend_cons[OF hgne hdiff_rest] by (by100 simp)
            ultimately show ?thesis by (by100 simp)
          qed
        next
          case hhk_ne: False
          \<comment> \<open>h\<cdot>k \<noteq> e. Inner = (\<alpha>, h\<cdot>k)#rest. Outer: merge g with h\<cdot>k.\<close>
          have hinner: "prepend (\<alpha>, h) z = (\<alpha>, mulGG \<alpha> h k) # rest"
            unfolding Cons hq hsame[symmetric] prepend_def using hhne hsame hhk_ne by (by100 simp)
          \<comment> \<open>LHS = prepend (\<alpha>,g) ((\<alpha>, h\<cdot>k)#rest): merge g\<cdot>(h\<cdot>k).\<close>
          have "prepend (\<alpha>, g) ((\<alpha>, mulGG \<alpha> h k) # rest) =
              (let v = mulGG \<alpha> g (mulGG \<alpha> h k) in if v = eGG \<alpha> then rest else (\<alpha>, v) # rest)"
            unfolding prepend_def using hgne by (by100 simp)
          hence hlhs: "prepend (\<alpha>, g) (prepend (\<alpha>, h) z) =
              (let v = mulGG \<alpha> g (mulGG \<alpha> h k) in if v = eGG \<alpha> then rest else (\<alpha>, v) # rest)"
            unfolding hinner .
          \<comment> \<open>RHS = prepend (\<alpha>, g\<cdot>h) ((\<beta>,k)#rest): merge (g\<cdot>h)\<cdot>k = g\<cdot>(h\<cdot>k) by assoc.\<close>
          have "prepend (\<alpha>, mulGG \<alpha> g h) z =
              (let v = mulGG \<alpha> (mulGG \<alpha> g h) k in if v = eGG \<alpha> then rest else (\<alpha>, v) # rest)"
          proof (cases "mulGG \<alpha> g h = eGG \<alpha>")
            case True
            have "mulGG \<alpha> (eGG \<alpha>) k = k" using hgrp hk unfolding top1_is_group_on_def by (by100 blast)
            hence "prepend (\<alpha>, eGG \<alpha>) ((\<beta>,k)#rest) = (\<beta>,k)#rest"
              unfolding prepend_def by (by100 simp)
            moreover have "mulGG \<beta> (eGG \<beta>) k = k" using \<open>mulGG \<alpha> (eGG \<alpha>) k = k\<close> hsame by (by100 simp)
            ultimately show ?thesis unfolding Cons hq using True hkne hsame by (by100 simp)
          next
            case False
            have "prepend (\<alpha>, mulGG \<alpha> g h) ((\<alpha>, k) # rest) =
                (let gh = mulGG \<alpha> (mulGG \<alpha> g h) k in if gh = eGG \<alpha> then rest else (\<alpha>, gh) # rest)"
              unfolding prepend_def using False by (by100 simp)
            thus ?thesis unfolding Cons hq hsame by (by100 simp)
          qed
          thus ?thesis unfolding hlhs hassoc_grp by (by100 simp)
        qed
      qed
    qed
  qed
  have hprepend_mul: "\<And>\<alpha> g ws zs. \<alpha> \<in> J \<Longrightarrow> g \<in> GG \<alpha> \<Longrightarrow> ws \<in> G \<Longrightarrow> zs \<in> G \<Longrightarrow>
      mul (prepend (\<alpha>, g) ws) zs = prepend (\<alpha>, g) (mul ws zs)"
  proof -
    fix \<alpha> :: 'i and g :: 'gg and ws zs :: "('i \<times> 'gg) list"
    assume h\<alpha>: "\<alpha> \<in> J" and hg: "g \<in> GG \<alpha>" and hws: "ws \<in> G" and hzs: "zs \<in> G"
    show "mul (prepend (\<alpha>, g) ws) zs = prepend (\<alpha>, g) (mul ws zs)"
    proof (cases "g = eGG \<alpha>")
      case True \<comment> \<open>Identity: prepend skips.\<close>
      thus ?thesis unfolding prepend_def by (by100 simp)
    next
      case hgne: False
      show ?thesis
      proof (cases ws)
        case Nil \<comment> \<open>Empty word: prepend = singleton.\<close>
        have "prepend (\<alpha>, g) [] = [(\<alpha>, g)]" unfolding prepend_def using hgne by (by100 simp)
        hence "mul (prepend (\<alpha>, g) ws) zs = mul [(\<alpha>, g)] zs" unfolding Nil by (by100 simp)
        also have "\<dots> = prepend (\<alpha>, g) zs" unfolding mul_def by (by100 simp)
        also have "\<dots> = prepend (\<alpha>, g) (mul ws zs)" unfolding Nil mul_def by (by100 simp)
        finally show ?thesis .
      next
        case (Cons p rest)
        obtain \<beta> h where hp: "p = (\<beta>, h)" by (cases p)
        have hrest_G: "rest \<in> G"
        proof -
          have "p # rest \<in> G" using hws unfolding Cons by (by100 simp)
          thus ?thesis by (rule htail_G)
        qed
        show ?thesis
        proof (cases "\<alpha> = \<beta>")
          case hdiff: False \<comment> \<open>Different index: prepend = cons.\<close>
          have "prepend (\<alpha>, g) ws = (\<alpha>, g) # ws"
            unfolding Cons hp prepend_def using hgne hdiff by (by100 simp)
          hence "mul (prepend (\<alpha>, g) ws) zs = foldr prepend ((\<alpha>, g) # ws) zs" unfolding mul_def by (by100 simp)
          also have "\<dots> = prepend (\<alpha>, g) (foldr prepend ws zs)" by (by100 simp)
          finally show ?thesis unfolding mul_def .
        next
          case hsame: True \<comment> \<open>Same index: uses prepend_compose.\<close>
          have helem: "h \<in> GG \<alpha> \<and> h \<noteq> eGG \<alpha>"
            using hG_elem[OF hws, of 0] unfolding Cons hp hsame by (by100 simp)
          let ?gh = "mulGG \<alpha> g h"
          show ?thesis
          proof (cases "?gh = eGG \<alpha>")
            case True \<comment> \<open>Product = identity: prepend removes head.\<close>
            have hprep: "prepend (\<alpha>, g) ws = rest" unfolding Cons hp prepend_def using hgne hsame True by (by100 simp)
            \<comment> \<open>mul rest zs vs prepend (\<alpha>,g) (prepend (\<beta>,h) (mul rest zs)).\<close>
            have "mul ws zs = foldr prepend ws zs" unfolding mul_def by (by100 simp)
            also have "foldr prepend ws zs = prepend p (foldr prepend rest zs)" unfolding Cons by (by100 simp)
            finally have hmulws: "mul ws zs = prepend (\<beta>, h) (mul rest zs)" unfolding hp mul_def by (by100 simp)
            have "prepend (\<alpha>, g) (mul ws zs) = prepend (\<alpha>, g) (prepend (\<beta>, h) (mul rest zs))"
              using hmulws by (by100 simp)
            also have "\<dots> = prepend (\<alpha>, ?gh) (mul rest zs)"
            proof -
              have "mul rest zs \<in> G" using hmul_closed hrest_G hzs by (by100 blast)
              thus ?thesis
                using hprepend_compose[OF h\<alpha> hg hgne _ _ \<open>mul rest zs \<in> G\<close>] helem unfolding hsame by (by100 blast)
            qed
            also have "\<dots> = mul rest zs" unfolding prepend_def using True by (by100 simp)
            finally show ?thesis unfolding hprep by (by100 simp)
          next
            case ghne: False \<comment> \<open>Product non-identity: replace head.\<close>
            have hprep: "prepend (\<alpha>, g) ws = (\<alpha>, ?gh) # rest"
              unfolding Cons hp prepend_def using hgne hsame ghne by (by100 simp)
            have "mul ws zs = prepend (\<beta>, h) (mul rest zs)"
              unfolding mul_def Cons hp by (by100 simp)
            hence "prepend (\<alpha>, g) (mul ws zs) = prepend (\<alpha>, g) (prepend (\<beta>, h) (mul rest zs))" by (by100 simp)
            also have "\<dots> = prepend (\<alpha>, ?gh) (mul rest zs)"
            proof -
              have "mul rest zs \<in> G" using hmul_closed hrest_G hzs by (by100 blast)
              thus ?thesis
                using hprepend_compose[OF h\<alpha> hg hgne _ _ \<open>mul rest zs \<in> G\<close>] helem unfolding hsame by (by100 blast)
            qed
            finally have "prepend (\<alpha>, g) (mul ws zs) = prepend (\<alpha>, ?gh) (mul rest zs)" .
            moreover have "mul (prepend (\<alpha>, g) ws) zs = prepend (\<alpha>, ?gh) (mul rest zs)"
              unfolding hprep mul_def by (by100 simp)
            ultimately show ?thesis by (by100 simp)
          qed
        qed
      qed
    qed
  qed
  have hassoc: "\<forall>ws1\<in>G. \<forall>ws2\<in>G. \<forall>ws3\<in>G. mul (mul ws1 ws2) ws3 = mul ws1 (mul ws2 ws3)"
  proof (intro ballI)
    fix ws1 ws2 ws3 assume hws1: "ws1 \<in> G" and hws2: "ws2 \<in> G" and hws3: "ws3 \<in> G"
    show "mul (mul ws1 ws2) ws3 = mul ws1 (mul ws2 ws3)"
      unfolding mul_def
      using hws1
    proof (induction ws1)
      case Nil show ?case by (by100 simp)
    next
      case (Cons p ws1')
      obtain \<alpha> g where hp: "p = (\<alpha>, g)" by (cases p)
      have hpws1: "p # ws1' \<in> G" using Cons.prems .
      have h\<alpha>: "\<alpha> \<in> J" and hg: "g \<in> GG \<alpha>"
        using hG_elem[OF hpws1, of 0] unfolding hp by (by100 simp)+
      have hws1': "ws1' \<in> G" by (rule htail_G[OF hpws1])
      have hIH: "foldr prepend (foldr prepend ws1' ws2) ws3 = foldr prepend ws1' (foldr prepend ws2 ws3)"
        using Cons.IH[OF hws1'] .
      have hmul12: "foldr prepend ws1' ws2 \<in> G"
        using hmul_closed hws1' hws2 unfolding mul_def by (by100 blast)
      have hmul23: "foldr prepend ws2 ws3 \<in> G"
        using hmul_closed hws2 hws3 unfolding mul_def by (by100 blast)
      \<comment> \<open>LHS: foldr prepend (prepend p (foldr prepend ws1' ws2)) ws3
             = prepend p (foldr prepend (foldr prepend ws1' ws2) ws3)  [by hprepend_mul]
             = prepend p (foldr prepend ws1' (foldr prepend ws2 ws3))  [by IH]\<close>
      have "foldr prepend (p # ws1') (foldr prepend ws2 ws3) = prepend p (foldr prepend ws1' (foldr prepend ws2 ws3))"
        by (by100 simp)
      moreover have "foldr prepend (foldr prepend (p # ws1') ws2) ws3
          = foldr prepend (prepend p (foldr prepend ws1' ws2)) ws3" by (by100 simp)
      moreover have "foldr prepend (prepend p (foldr prepend ws1' ws2)) ws3
          = prepend p (foldr prepend (foldr prepend ws1' ws2) ws3)"
        unfolding hp using hprepend_mul[OF h\<alpha> hg hmul12 hws3] unfolding mul_def hp by (by100 simp)
      moreover note hIH
      ultimately show ?case unfolding hp by (by100 simp)
    qed
  qed
  \<comment> \<open>(7) Left/right inverse.\<close>
  have hleft_inv: "\<forall>ws\<in>G. mul (invg ws) ws = e"
  proof (intro ballI)
    fix ws assume hws: "ws \<in> G"
    show "mul (invg ws) ws = e" unfolding mul_def invg_def e_def
      using hws
    proof (induction ws)
      case Nil show ?case by (by100 simp)
    next
      case (Cons p ws')
      obtain \<alpha> g where hp: "p = (\<alpha>, g)" by (cases p)
      have hpws: "p # ws' \<in> G" using Cons.prems .
      have hws': "ws' \<in> G" by (rule htail_G[OF hpws])
      have hIH: "foldr prepend (rev (map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) ws')) ws' = []"
        using Cons.IH[OF hws'] .
      have helem: "\<alpha> \<in> J \<and> g \<in> GG \<alpha> \<and> g \<noteq> eGG \<alpha>"
        using hG_elem[OF hpws, of 0] unfolding hp by (by100 simp)
      have hgrp: "top1_is_group_on (GG \<alpha>) (mulGG \<alpha>) (eGG \<alpha>) (invgGG \<alpha>)"
        using hgroups helem by (by100 blast)
      \<comment> \<open>invg (p#ws') = invg ws' @ [(\<alpha>, invgGG \<alpha> g)].\<close>
      have hinv_eq: "rev (map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) (p # ws')) =
          rev (map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) ws') @ [(\<alpha>, invgGG \<alpha> g)]"
        unfolding hp by (by100 simp)
      \<comment> \<open>foldr prepend (xs @ ys) z = foldr prepend xs (foldr prepend ys z).\<close>
      have "foldr prepend (rev (map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) (p # ws'))) (p # ws')
          = foldr prepend (rev (map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) ws'))
              (foldr prepend [(\<alpha>, invgGG \<alpha> g)] (p # ws'))"
        unfolding hinv_eq foldr_append by (by100 simp)
      \<comment> \<open>foldr prepend [(\<alpha>, invgGG \<alpha> g)] (p#ws') = prepend (\<alpha>, invgGG \<alpha> g) (p#ws').\<close>
      also have "foldr prepend [(\<alpha>, invgGG \<alpha> g)] (p # ws') = prepend (\<alpha>, invgGG \<alpha> g) (p # ws')"
        by (by100 simp)
      \<comment> \<open>prepend (\<alpha>, invgGG \<alpha> g) ((\<alpha>,g)#ws') cancels: invg(g)\<cdot>g = eGG, remove head → ws'.\<close>
      also have "prepend (\<alpha>, invgGG \<alpha> g) (p # ws') = ws'"
      proof -
        have hne: "invgGG \<alpha> g \<noteq> eGG \<alpha>"
        proof
          assume "invgGG \<alpha> g = eGG \<alpha>"
          hence "mulGG \<alpha> (invgGG \<alpha> g) g = mulGG \<alpha> (eGG \<alpha>) g" by (by100 simp)
          moreover have "mulGG \<alpha> (invgGG \<alpha> g) g = eGG \<alpha>"
            using hgrp helem unfolding top1_is_group_on_def by (by100 blast)
          moreover have "mulGG \<alpha> (eGG \<alpha>) g = g"
            using hgrp helem unfolding top1_is_group_on_def by (by100 blast)
          ultimately have "g = eGG \<alpha>" by (by100 simp)
          thus False using helem by (by100 simp)
        qed
        have "mulGG \<alpha> (invgGG \<alpha> g) g = eGG \<alpha>"
          using hgrp helem unfolding top1_is_group_on_def by (by100 blast)
        thus ?thesis unfolding hp prepend_def using hne by (by100 simp)
      qed
      \<comment> \<open>Now: foldr prepend (invg ws') ws' = [] by IH.\<close>
      also have "foldr prepend (rev (map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) ws')) ws' = []"
        by (rule hIH)
      finally show ?case .
    qed
  qed
  have hinverse: "\<forall>ws\<in>G. mul (invg ws) ws = e \<and> mul ws (invg ws) = e"
  proof (intro ballI conjI)
    fix ws assume hws: "ws \<in> G"
    show "mul (invg ws) ws = e" using hleft_inv hws by (by100 blast)
  next
    fix ws assume hws: "ws \<in> G"
    \<comment> \<open>Right inverse: mul ws (invg ws) = e.\<close>
    \<comment> \<open>Double inverse in factor groups: invgGG \<alpha> (invgGG \<alpha> g) = g.\<close>
    have hdouble_inv: "\<And>\<alpha> g. \<alpha> \<in> J \<Longrightarrow> g \<in> GG \<alpha> \<Longrightarrow> invgGG \<alpha> (invgGG \<alpha> g) = g"
    proof -
      fix \<alpha> g assume h\<alpha>: "\<alpha> \<in> J" and hg: "g \<in> GG \<alpha>"
      have hgrp: "top1_is_group_on (GG \<alpha>) (mulGG \<alpha>) (eGG \<alpha>) (invgGG \<alpha>)"
        using hgroups h\<alpha> by (by100 blast)
      have hig: "invgGG \<alpha> g \<in> GG \<alpha>" using hgrp hg unfolding top1_is_group_on_def by (by100 blast)
      have hiig: "invgGG \<alpha> (invgGG \<alpha> g) \<in> GG \<alpha>" using hgrp hig unfolding top1_is_group_on_def by (by100 blast)
      \<comment> \<open>invg(invg(g)) \<cdot> invg(g) = e, and g \<cdot> invg(g) = e. By left cancel: invg(invg(g)) = g.\<close>
      have h1: "mulGG \<alpha> (invgGG \<alpha> (invgGG \<alpha> g)) (invgGG \<alpha> g) = eGG \<alpha>"
        using hgrp hig unfolding top1_is_group_on_def by (by100 blast)
      have h2: "mulGG \<alpha> g (invgGG \<alpha> g) = eGG \<alpha>"
        using hgrp hg unfolding top1_is_group_on_def by (by100 blast)
      \<comment> \<open>Multiply both sides on the right by g: use associativity in GG \<alpha>.\<close>
      have h3: "mulGG \<alpha> (mulGG \<alpha> (invgGG \<alpha> (invgGG \<alpha> g)) (invgGG \<alpha> g)) g
              = mulGG \<alpha> (invgGG \<alpha> (invgGG \<alpha> g)) (mulGG \<alpha> (invgGG \<alpha> g) g)"
        using hgrp hiig hig hg unfolding top1_is_group_on_def by (by100 blast)
      have "mulGG \<alpha> (invgGG \<alpha> g) g = eGG \<alpha>"
        using hgrp hg unfolding top1_is_group_on_def by (by100 blast)
      hence "mulGG \<alpha> (invgGG \<alpha> (invgGG \<alpha> g)) (mulGG \<alpha> (invgGG \<alpha> g) g) = mulGG \<alpha> (invgGG \<alpha> (invgGG \<alpha> g)) (eGG \<alpha>)"
        by (by100 simp)
      also have "\<dots> = invgGG \<alpha> (invgGG \<alpha> g)"
        using hgrp hiig unfolding top1_is_group_on_def by (by100 blast)
      finally have hrhs: "mulGG \<alpha> (invgGG \<alpha> (invgGG \<alpha> g)) (mulGG \<alpha> (invgGG \<alpha> g) g) = invgGG \<alpha> (invgGG \<alpha> g)" .
      have "mulGG \<alpha> (eGG \<alpha>) g = g" using hgrp hg unfolding top1_is_group_on_def by (by100 blast)
      hence "mulGG \<alpha> (mulGG \<alpha> (invgGG \<alpha> (invgGG \<alpha> g)) (invgGG \<alpha> g)) g = g"
        using h1 by (by100 simp)
      hence "invgGG \<alpha> (invgGG \<alpha> g) = g" using h3 hrhs by (by100 simp)
      thus "invgGG \<alpha> (invgGG \<alpha> g) = g" .
    qed
    \<comment> \<open>invg (invg ws) = ws: map(inv) \<circ> rev \<circ> map(inv) \<circ> rev = map(inv\<circ>inv) = map(id) = id.\<close>
    have hinvg_invg: "invg (invg ws) = ws"
    proof -
      \<comment> \<open>Direct proof by list equality.\<close>
      have hlen: "length (invg (invg ws)) = length ws" unfolding invg_def by (by100 simp)
      have "\<forall>i<length ws. (invg (invg ws))!i = ws!i"
      proof (intro allI impI)
        fix i assume hi: "i < length ws"
        let ?n = "length ws"
        \<comment> \<open>invg ws = rev(map inv ws), so (invg ws)!j = inv(ws!(?n-1-j)).\<close>
        \<comment> \<open>invg(invg ws)!i = inv((invg ws)!(?n-1-i)) = inv(inv(ws!(i))) = ws!i.\<close>
        have hi': "?n - Suc i < ?n" using hi by (by100 linarith)
        have h1: "(invg ws)!(?n - Suc i) = (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) (ws!i)"
        proof -
          have "(invg ws)!(?n - Suc i) = (rev (map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) ws))!(?n - Suc i)"
            unfolding invg_def by (by100 simp)
          also have "\<dots> = (map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) ws)!(?n - Suc (?n - Suc i))"
            using rev_nth[of "?n - Suc i" "map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) ws"] hi by (by100 simp)
          also have "?n - Suc (?n - Suc i) = i" using hi by (by100 linarith)
          also have "(map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) ws)!i = (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) (ws!i)"
            using hi by (by100 simp)
          finally show ?thesis .
        qed
        have h2: "(invg (invg ws))!i = (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) ((invg ws)!(?n - Suc i))"
        proof -
          have "(invg (invg ws))!i = (rev (map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) (invg ws)))!i"
            unfolding invg_def by (by100 simp)
          also have "\<dots> = (map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) (invg ws))!(length (invg ws) - Suc i)"
            using rev_nth[of i "map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) (invg ws)"] hi
            unfolding invg_def by (by100 simp)
          also have "length (invg ws) = ?n" unfolding invg_def by (by100 simp)
          also have "(map (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) (invg ws))!(?n - Suc i)
              = (\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) ((invg ws)!(?n - Suc i))"
            using hi' unfolding invg_def by (by100 simp)
          finally show ?thesis by (by100 simp)
        qed
        have "(\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) ((\<lambda>(\<alpha>, g). (\<alpha>, invgGG \<alpha> g)) (ws!i)) = ws!i"
        proof -
          obtain \<alpha> g where hwsi: "ws!i = (\<alpha>, g)" by (cases "ws!i")
          have "\<alpha> \<in> J \<and> g \<in> GG \<alpha>" using hG_elem[OF hws hi] unfolding hwsi by (by100 simp)
          hence "invgGG \<alpha> (invgGG \<alpha> g) = g" using hdouble_inv by (by100 blast)
          thus ?thesis unfolding hwsi by (by100 simp)
        qed
        thus "(invg (invg ws))!i = ws!i" using h2 h1 by (by100 simp)
      qed
      hence "\<forall>i<length (invg (invg ws)). (invg (invg ws))!i = ws!i" using hlen by (by100 simp)
      thus ?thesis using hlen by (intro nth_equalityI) (by100 simp)+
    qed
    \<comment> \<open>Right inverse from left inverse: mul (invg(invg ws)) (invg ws) = e, i.e., mul ws (invg ws) = e.\<close>
    have "invg ws \<in> G" using hinvg_closed hws by (by100 blast)
    hence "mul (invg (invg ws)) (invg ws) = e" using hleft_inv by (by100 blast)
    thus "mul ws (invg ws) = e" unfolding hinvg_invg .
  qed
  \<comment> \<open>(8) \<iota>fam properties.\<close>
  have h\<iota>_in_G: "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<iota>fam \<alpha> x \<in> G"
  proof (intro ballI)
    fix \<alpha> x assume h\<alpha>: "\<alpha> \<in> J" and hx: "x \<in> GG \<alpha>"
    show "\<iota>fam \<alpha> x \<in> G"
    proof (cases "x = eGG \<alpha>")
      case True thus ?thesis unfolding \<iota>fam_def e_def[symmetric] using he_G by (by100 simp)
    next
      case False thus ?thesis unfolding \<iota>fam_def G_def using h\<alpha> hx by (by100 auto)
    qed
  qed
  have h\<iota>_hom: "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<forall>y\<in>GG \<alpha>.
      \<iota>fam \<alpha> (mulGG \<alpha> x y) = mul (\<iota>fam \<alpha> x) (\<iota>fam \<alpha> y)"
  proof (intro ballI)
    fix \<alpha> x y assume h\<alpha>: "\<alpha> \<in> J" and hx: "x \<in> GG \<alpha>" and hy: "y \<in> GG \<alpha>"
    have hgrp: "top1_is_group_on (GG \<alpha>) (mulGG \<alpha>) (eGG \<alpha>) (invgGG \<alpha>)"
      using hgroups h\<alpha> by (by100 blast)
    have hxy_in: "mulGG \<alpha> x y \<in> GG \<alpha>"
      using hgrp hx hy unfolding top1_is_group_on_def by (by100 blast)
    show "\<iota>fam \<alpha> (mulGG \<alpha> x y) = mul (\<iota>fam \<alpha> x) (\<iota>fam \<alpha> y)"
    proof (cases "x = eGG \<alpha>")
      case True
      hence "mulGG \<alpha> x y = y" using hgrp hy unfolding top1_is_group_on_def by (by100 blast)
      moreover have "\<iota>fam \<alpha> x = e" unfolding \<iota>fam_def e_def using True by (by100 simp)
      ultimately show ?thesis using hleft_id h\<iota>_in_G[THEN bspec[OF _ h\<alpha>], THEN bspec[OF _ hy]]
        by (by100 simp)
    next
      case xne: False
      show ?thesis
      proof (cases "y = eGG \<alpha>")
        case True
        hence "mulGG \<alpha> x y = x" using hgrp hx unfolding top1_is_group_on_def by (by100 blast)
        moreover have "\<iota>fam \<alpha> y = e" unfolding \<iota>fam_def e_def using True by (by100 simp)
        ultimately show ?thesis using hright_id h\<iota>_in_G[THEN bspec[OF _ h\<alpha>], THEN bspec[OF _ hx]]
          by (by100 simp)
      next
        case yne: False
        \<comment> \<open>Both x, y non-identity. \<iota>fam \<alpha> x = [(\<alpha>,x)], \<iota>fam \<alpha> y = [(\<alpha>,y)].
           mul [(\<alpha>,x)] [(\<alpha>,y)] = prepend (\<alpha>,x) [(\<alpha>,y)] = [(\<alpha>, mulGG \<alpha> x y)] if xy \<noteq> eGG,
           or [] if xy = eGG.\<close>
        have h\<iota>x: "\<iota>fam \<alpha> x = [(\<alpha>, x)]" unfolding \<iota>fam_def using xne by (by100 simp)
        have h\<iota>y: "\<iota>fam \<alpha> y = [(\<alpha>, y)]" unfolding \<iota>fam_def using yne by (by100 simp)
        have hmulxy: "mul [(\<alpha>, x)] [(\<alpha>, y)] = prepend (\<alpha>, x) [(\<alpha>, y)]"
          unfolding mul_def by (by100 simp)
        have hprep: "prepend (\<alpha>, x) [(\<alpha>, y)] = (let gh = mulGG \<alpha> x y in
            if gh = eGG \<alpha> then [] else [(\<alpha>, gh)])"
          unfolding prepend_def using xne by (by100 simp)
        show ?thesis
        proof (cases "mulGG \<alpha> x y = eGG \<alpha>")
          case True
          hence "\<iota>fam \<alpha> (mulGG \<alpha> x y) = []" unfolding \<iota>fam_def by (by100 simp)
          moreover have "mul (\<iota>fam \<alpha> x) (\<iota>fam \<alpha> y) = []"
            unfolding h\<iota>x h\<iota>y hmulxy hprep using True by (by100 simp)
          ultimately show ?thesis unfolding e_def by (by100 simp)
        next
          case xyFalse: False
          hence "\<iota>fam \<alpha> (mulGG \<alpha> x y) = [(\<alpha>, mulGG \<alpha> x y)]" unfolding \<iota>fam_def by (by100 simp)
          moreover have "mul (\<iota>fam \<alpha> x) (\<iota>fam \<alpha> y) = [(\<alpha>, mulGG \<alpha> x y)]"
            unfolding h\<iota>x h\<iota>y hmulxy hprep using xyFalse by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
      qed
    qed
  qed
  have h\<iota>_inj: "\<forall>\<alpha>\<in>J. inj_on (\<iota>fam \<alpha>) (GG \<alpha>)"
  proof (intro ballI)
    fix \<alpha> assume "\<alpha> \<in> J"
    show "inj_on (\<iota>fam \<alpha>) (GG \<alpha>)"
      unfolding inj_on_def
    proof (intro ballI impI)
      fix x y assume hx: "x \<in> GG \<alpha>" and hy: "y \<in> GG \<alpha>" and heq: "\<iota>fam \<alpha> x = \<iota>fam \<alpha> y"
      show "x = y"
      proof (cases "x = eGG \<alpha>")
        case True
        hence "\<iota>fam \<alpha> x = []" unfolding \<iota>fam_def by (by100 simp)
        hence "\<iota>fam \<alpha> y = []" using heq by (by100 simp)
        hence "y = eGG \<alpha>" unfolding \<iota>fam_def by (cases "y = eGG \<alpha>") (by100 simp)+
        thus ?thesis using True by (by100 simp)
      next
        case False
        hence h\<iota>x: "\<iota>fam \<alpha> x = [(\<alpha>, x)]" unfolding \<iota>fam_def by (by100 simp)
        show ?thesis
        proof (cases "y = eGG \<alpha>")
          case True
          hence "\<iota>fam \<alpha> y = []" unfolding \<iota>fam_def by (by100 simp)
          hence "[(\<alpha>, x)] = []" using heq h\<iota>x by (by100 simp)
          thus ?thesis by (by100 simp)
        next
          case yFalse: False
          hence "\<iota>fam \<alpha> y = [(\<alpha>, y)]" unfolding \<iota>fam_def by (by100 simp)
          hence "[(\<alpha>, x)] = [(\<alpha>, y)]" using heq h\<iota>x by (by100 simp)
          thus ?thesis by (by100 simp)
        qed
      qed
    qed
  qed
  \<comment> \<open>(9) Generation: G = subgroup generated by images.\<close>
  have hgen: "G = top1_subgroup_generated_on G mul e invg (\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>)"
  proof (rule set_eqI, rule iffI)
    fix ws assume hws: "ws \<in> G"
    \<comment> \<open>ws \<in> G implies ws is in every subgroup H containing the \<iota>-images.\<close>
    show "ws \<in> top1_subgroup_generated_on G mul e invg (\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>)"
      unfolding top1_subgroup_generated_on_def
    proof (rule InterI, clarify)
      fix H assume hS: "(\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>) \<subseteq> H" and hHG: "H \<subseteq> G"
          and hHgrp: "top1_is_group_on H mul e invg"
      \<comment> \<open>By induction on ws: each word = product of singletons in H.\<close>
      show "ws \<in> H"
        using hws
      proof (induction ws)
        case Nil thus ?case using hHgrp unfolding top1_is_group_on_def e_def by (by100 blast)
      next
        case (Cons p ws')
        have hpws: "p # ws' \<in> G" using Cons.prems .
        have hws': "ws' \<in> G" by (rule htail_G[OF hpws])
        have hws'_H: "ws' \<in> H" using Cons.IH[OF hws'] .
        obtain \<alpha> g where hp: "p = (\<alpha>, g)" by (cases p)
        have helem: "\<alpha> \<in> J \<and> g \<in> GG \<alpha> \<and> g \<noteq> eGG \<alpha>"
          using hG_elem[OF hpws, of 0] unfolding hp by (by100 simp)
        \<comment> \<open>\<iota>fam \<alpha> g = [(\<alpha>,g)] = [p], so [p] \<in> H.\<close>
        have h\<iota>_eq: "\<iota>fam \<alpha> g = [(\<alpha>, g)]" unfolding \<iota>fam_def using helem by (by100 simp)
        have "\<iota>fam \<alpha> g \<in> (\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>)" using helem by (by100 blast)
        hence "\<iota>fam \<alpha> g \<in> H" using hS by (by100 blast)
        hence hpH: "[(\<alpha>, g)] \<in> H" using h\<iota>_eq by (by100 simp)
        \<comment> \<open>p # ws' = mul [p] ws' (since prepend just conses for reduced word).\<close>
        have "mul [(\<alpha>, g)] ws' = prepend (\<alpha>, g) ws'"
          unfolding mul_def by (by100 simp)
        also have "\<dots> = (\<alpha>, g) # ws'"
        proof (rule hprepend_cons)
          show "g \<noteq> eGG \<alpha>" using helem by (by100 blast)
          show "ws' = [] \<or> \<alpha> \<noteq> fst (hd ws')"
          proof (cases ws')
            case Nil thus ?thesis by (by100 blast)
          next
            case (Cons q rest)
            have "fst ((p # ws')!0) \<noteq> fst ((p # ws')!1)"
            proof -
              have h01: "0 + 1 < length (p # ws')" unfolding Cons by (by100 simp)
              have "fst ((p # ws')!0) \<noteq> fst ((p # ws')!(0+1))" using hG_alt[OF hpws h01] .
              thus ?thesis unfolding hp by (by100 simp)
            qed
            thus ?thesis unfolding hp Cons by (by100 simp)
          qed
        qed
        finally have hpws_eq: "p # ws' = mul [(\<alpha>, g)] ws'" unfolding hp by (by100 simp)
        have "mul [(\<alpha>, g)] ws' \<in> H"
          using hHgrp hpH hws'_H unfolding top1_is_group_on_def by (by100 blast)
        hence "p # ws' \<in> H" using hpws_eq by (by100 simp)
        thus ?case .
      qed
    qed
  next
    fix ws assume "ws \<in> top1_subgroup_generated_on G mul e invg (\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>)"
    \<comment> \<open>Direction \<supseteq>: G itself is a group containing all \<iota>-images, so the intersection \<subseteq> G.\<close>
    thus "ws \<in> G"
    proof -
      have "(\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>) \<subseteq> G" using h\<iota>_in_G by (by100 blast)
      moreover have "G \<subseteq> G" by (by100 blast)
      moreover have "top1_is_group_on G mul e invg"
        unfolding top1_is_group_on_def
        using he_G hmul_closed hinvg_closed hassoc hleft_id hright_id hinverse by (by100 blast)
      ultimately have "G \<in> {H. (\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>) \<subseteq> H \<and> H \<subseteq> G \<and> top1_is_group_on H mul e invg}"
        by (by100 blast)
      hence "top1_subgroup_generated_on G mul e invg (\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>) \<subseteq> G"
        unfolding top1_subgroup_generated_on_def by (rule Inter_lower)
      thus ?thesis using \<open>ws \<in> _\<close> by (by100 blast)
    qed
  qed
  \<comment> \<open>(10) Freeness: no nontrivial reduced word = e.\<close>
  have hfree: "\<forall>indices word.
      length indices = length word \<longrightarrow>
      length indices > 0 \<longrightarrow>
      (\<forall>i<length indices. indices!i \<in> J \<and> word!i \<in> GG (indices!i)
                        \<and> \<iota>fam (indices!i) (word!i) \<noteq> e) \<longrightarrow>
      (\<forall>i. i + 1 < length indices \<longrightarrow> indices!i \<noteq> indices!(i+1)) \<longrightarrow>
      foldr mul (map (\<lambda>i. \<iota>fam (indices!i) (word!i)) [0..<length indices]) e \<noteq> e"
  proof (intro allI impI)
    fix indices :: "'i list" and word :: "'gg list"
    assume hlen: "length indices = length word" and hpos: "0 < length indices"
    assume hvals: "\<forall>i<length indices. indices!i \<in> J \<and> word!i \<in> GG (indices!i) \<and> \<iota>fam (indices!i) (word!i) \<noteq> e"
    assume halt: "\<forall>i. i + 1 < length indices \<longrightarrow> indices!i \<noteq> indices!(i+1)"
    \<comment> \<open>Each \<iota>fam(indices!i)(word!i) = [(indices!i, word!i)] since \<noteq> e = [].\<close>
    have h\<iota>_single: "\<forall>i<length indices. \<iota>fam (indices!i) (word!i) = [(indices!i, word!i)]"
    proof (intro allI impI)
      fix i assume hi: "i < length indices"
      have hne: "word!i \<noteq> eGG (indices!i)"
      proof
        assume "word!i = eGG (indices!i)"
        hence "\<iota>fam (indices!i) (word!i) = []" unfolding \<iota>fam_def by (by100 simp)
        hence "\<iota>fam (indices!i) (word!i) = e" unfolding e_def by (by100 simp)
        moreover have "\<iota>fam (indices!i) (word!i) \<noteq> e" using hvals hi by (by100 blast)
        ultimately show False by (by100 simp)
      qed
      show "\<iota>fam (indices!i) (word!i) = [(indices!i, word!i)]"
        unfolding \<iota>fam_def using hne by (by100 simp)
    qed
    \<comment> \<open>The product of singletons with alternating indices = the word itself.\<close>
    \<comment> \<open>By induction: foldr mul [w0,...,wn-1] [] builds the reduced word
       [(indices!(n-1), word!(n-1)), ..., (indices!0, word!0)] which is nonempty.\<close>
    \<comment> \<open>Use hprepend_cons (proved above).\<close>
    \<comment> \<open>The product of singletons with alternating indices: by reverse induction,
       each prepend just conses since consecutive indices differ.\<close>
    show "foldr mul (map (\<lambda>i. \<iota>fam (indices!i) (word!i)) [0..<length indices]) e \<noteq> e"
    proof -
      \<comment> \<open>Show the result is the word [(indices!0, word!0), ..., (indices!(n-1), word!(n-1))].\<close>
      let ?n = "length indices"
      let ?ws = "map (\<lambda>i. (indices!i, word!i)) [0..<?n]"
      have hresult: "foldr mul (map (\<lambda>i. \<iota>fam (indices!i) (word!i)) [0..<?n]) e = ?ws"
      proof -
        \<comment> \<open>Prove by induction on n. Key: mul of singleton onto word = prepend = cons.\<close>
        have "\<forall>m \<le> ?n. foldr mul (map (\<lambda>i. \<iota>fam (indices!i) (word!i)) [m..<?n]) e
            = map (\<lambda>i. (indices!i, word!i)) [m..<?n]"
        proof (rule allI, rule impI)
          fix m show "m \<le> ?n \<Longrightarrow> foldr mul (map (\<lambda>i. \<iota>fam (indices!i) (word!i)) [m..<?n]) e
            = map (\<lambda>i. (indices!i, word!i)) [m..<?n]"
          proof (induction "?n - m" arbitrary: m)
            case 0
            hence "m = ?n" using 0 by (by100 linarith)
            thus ?case unfolding e_def by (by100 simp)
          next
            case (Suc k)
            hence hm_lt: "m < ?n" by (by100 linarith)
            have hSm: "Suc m \<le> ?n" using hm_lt by (by100 linarith)
            have hk: "k = ?n - Suc m" using Suc by (by100 linarith)
            have hIH: "foldr mul (map (\<lambda>i. \<iota>fam (indices!i) (word!i)) [Suc m..<?n]) e
                = map (\<lambda>i. (indices!i, word!i)) [Suc m..<?n]"
              using Suc.hyps(1)[OF hk hSm] .
            have hupt: "[m..<?n] = m # [Suc m..<?n]" using upt_rec[of m ?n] hm_lt by (by100 simp)
            have "foldr mul (map (\<lambda>i. \<iota>fam (indices!i) (word!i)) [m..<?n]) e
                = mul (\<iota>fam (indices!m) (word!m)) (foldr mul (map (\<lambda>i. \<iota>fam (indices!i) (word!i)) [Suc m..<?n]) e)"
              unfolding hupt by (by100 simp)
            also have "\<dots> = mul (\<iota>fam (indices!m) (word!m)) (map (\<lambda>i. (indices!i, word!i)) [Suc m..<?n])"
              unfolding hIH ..
            also have "\<dots> = mul [(indices!m, word!m)] (map (\<lambda>i. (indices!i, word!i)) [Suc m..<?n])"
              using h\<iota>_single hm_lt by (by100 simp)
            also have "\<dots> = prepend (indices!m, word!m) (map (\<lambda>i. (indices!i, word!i)) [Suc m..<?n])"
              unfolding mul_def by (by100 simp)
            also have "\<dots> = (indices!m, word!m) # (map (\<lambda>i. (indices!i, word!i)) [Suc m..<?n])"
            proof (rule hprepend_cons)
              show "word!m \<noteq> eGG (indices!m)"
              proof -
                have "\<iota>fam (indices!m) (word!m) \<noteq> e" using hvals hm_lt by (by100 blast)
                thus ?thesis unfolding \<iota>fam_def e_def by (cases "word!m = eGG (indices!m)") (by100 simp)+
              qed
            next
              show "map (\<lambda>i. (indices!i, word!i)) [Suc m..<?n] = [] \<or>
                  indices!m \<noteq> fst (hd (map (\<lambda>i. (indices!i, word!i)) [Suc m..<?n]))"
              proof (cases "Suc m < ?n")
                case False
                hence "[Suc m..<?n] = []" by (by100 simp)
                thus ?thesis by (by100 simp)
              next
                case True
                have "[Suc m..<?n] = Suc m # [Suc (Suc m)..<?n]"
                  using upt_rec[of "Suc m" ?n] True by (by100 simp)
                hence "hd (map (\<lambda>i. (indices!i, word!i)) [Suc m..<?n]) = (indices!(Suc m), word!(Suc m))"
                  by (by100 simp)
                moreover have "indices!m \<noteq> indices!(Suc m)"
                proof -
                  have "m + 1 < length indices" using True by (by100 simp)
                  hence "indices ! m \<noteq> indices ! (m + 1)" using halt by (by100 blast)
                  thus ?thesis by (by100 simp)
                qed
                ultimately show ?thesis by (by100 simp)
              qed
            qed
            also have "\<dots> = map (\<lambda>i. (indices!i, word!i)) [m..<?n]" unfolding hupt by (by100 simp)
            finally show ?case .
          qed
        qed
        thus ?thesis by (by100 simp)
      qed
      have "?ws \<noteq> []" using hpos by (by100 simp)
      thus ?thesis using hresult unfolding e_def by (by100 simp)
    qed
  qed
  \<comment> \<open>Assemble the free product.\<close>
  show ?thesis
    unfolding top1_is_free_product_on_def
  proof (intro exI conjI)
    show "top1_is_group_on G mul e invg"
      unfolding top1_is_group_on_def
      using he_G hmul_closed hinvg_closed hassoc hleft_id hright_id hinverse
      by (by100 blast)
    show "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<iota>fam \<alpha> x \<in> G" by (rule h\<iota>_in_G)
    show "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<forall>y\<in>GG \<alpha>. \<iota>fam \<alpha> (mulGG \<alpha> x y) = mul (\<iota>fam \<alpha> x) (\<iota>fam \<alpha> y)"
      by (rule h\<iota>_hom)
    show "\<forall>\<alpha>\<in>J. inj_on (\<iota>fam \<alpha>) (GG \<alpha>)" by (rule h\<iota>_inj)
    show "G = top1_subgroup_generated_on G mul e invg (\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>)" by (rule hgen)
    show "\<forall>indices word.
      length indices = length word \<longrightarrow> 0 < length indices \<longrightarrow>
      (\<forall>i<length indices. indices ! i \<in> J \<and> word ! i \<in> GG (indices ! i) \<and> \<iota>fam (indices ! i) (word ! i) \<noteq> e) \<longrightarrow>
      (\<forall>i. i + 1 < length indices \<longrightarrow> indices ! i \<noteq> indices ! (i + 1)) \<longrightarrow>
      foldr mul (map (\<lambda>i. \<iota>fam (indices ! i) (word ! i)) [0..<length indices]) e \<noteq> e"
      by (rule hfree)
  qed
qed

text \<open>Lemma 68.3 (Munkres): Extension property of free products.
  If G is a free product of groups G_\<alpha> via injections \<iota>_\<alpha>, then for any group H
  and homomorphisms h_\<alpha>: G_\<alpha> \<rightarrow> H, there exists a unique hom h: G \<rightarrow> H
  with h \<circ> \<iota>_\<alpha> = h_\<alpha> for each \<alpha>.\<close>
text \<open>Every element of a free product has a reduced word representation.
  This follows from the generation property (G = subgroup generated by generators)
  and the word reduction process (combining adjacent same-index elements).\<close>
lemma free_product_reduced_repr:
  assumes hFP: "top1_is_free_product_on G mul e invg GG mulGG \<iota>fam J"
      and hGG_grps: "\<forall>\<alpha>\<in>J. top1_is_group_on (GG \<alpha>) (mulGG \<alpha>) (eGG \<alpha>) (invgGG \<alpha>)"
      and hg: "g \<in> G"
  shows "g = e \<or> (\<exists>indices word.
      length indices = length word \<and> length indices > 0
    \<and> (\<forall>i<length indices. indices!i \<in> J \<and> word!i \<in> GG (indices!i)
                        \<and> \<iota>fam (indices!i) (word!i) \<noteq> e)
    \<and> (\<forall>i. i + 1 < length indices \<longrightarrow> indices!i \<noteq> indices!(i+1))
    \<and> foldr mul (map (\<lambda>i. \<iota>fam (indices!i) (word!i)) [0..<length indices]) e = g)"
proof -
  have hG: "top1_is_group_on G mul e invg"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have hgen: "G = top1_subgroup_generated_on G mul e invg (\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>)"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have h\<iota>_in: "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<iota>fam \<alpha> x \<in> G"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have h\<iota>_hom: "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<forall>y\<in>GG \<alpha>.
      \<iota>fam \<alpha> (mulGG \<alpha> x y) = mul (\<iota>fam \<alpha> x) (\<iota>fam \<alpha> y)"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have hS_sub: "(\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>) \<subseteq> G"
    using h\<iota>_in by (by100 blast)
  \<comment> \<open>Step 1: By subgroup_generated_word_repr, g has a word representation in S \<union> invg(S)
     where S = \<Union>(ιfam α ` GG α). Each ws!i is either ιfam(α)(x) or invg(ιfam(α)(x))
     for some α ∈ J, x ∈ GG(α).\<close>
  have hg_gen: "g \<in> top1_subgroup_generated_on G mul e invg (\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>)"
    using hg hgen by (by100 simp)
  have hword: "g = e \<or> (\<exists>ws. length ws > 0
      \<and> (\<forall>i<length ws. ws!i \<in> (\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>) \<or>
            (\<exists>s\<in>(\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>). ws!i = invg s))
      \<and> foldr mul ws e = g)"
    by (rule subgroup_generated_word_repr[OF hG hS_sub hg_gen])
  \<comment> \<open>Step 2: Each generator or inverse-of-generator has the form ιfam(α)(x).
     For generators: ιfam(α)(x) with x ∈ GG(α).
     For inverses: invg(ιfam(α)(x)). Since ιfam is a hom and injective,
       invg(ιfam(α)(x)) = ιfam(α)(invgGG(α)(x)) by hom_preserves_inv.\<close>
  \<comment> \<open>Step 3: Given a tagged word [(α₁,g₁),...,(αₙ,gₙ)] with each gᵢ ∈ GG(αᵢ),
     the product foldr mul [ιfam(α₁)(g₁),...] e equals g.
     Reduce: while there exist adjacent i with αᵢ = αᵢ₊₁, replace
       (αᵢ,gᵢ)(αᵢ,gᵢ₊₁) with (αᵢ, mulGG(αᵢ) gᵢ gᵢ₊₁). If the result is eGG, delete.
     By the hom property, the product is preserved.
     Termination: length decreases or stays same with fewer adjacent duplicates.\<close>
  \<comment> \<open>The full proof of this reduction process is substantial. For now, sorry.\<close>
  show ?thesis sorry
qed

lemma Lemma_68_3_extension_property:
  assumes hFP: "top1_is_free_product_on G mul e invg GG mulGG \<iota>fam J"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hfam: "\<forall>\<alpha>\<in>J. top1_group_hom_on (GG \<alpha>) (mulGG \<alpha>) H mulH (hfam \<alpha>)"
  shows "\<exists>h. top1_group_hom_on G mul H mulH h
      \<and> (\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. h (\<iota>fam \<alpha> x) = hfam \<alpha> x)
      \<and> (\<forall>h'. top1_group_hom_on G mul H mulH h'
          \<longrightarrow> (\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. h' (\<iota>fam \<alpha> x) = hfam \<alpha> x)
          \<longrightarrow> (\<forall>g\<in>G. h' g = h g))"
proof -
  have hG: "top1_is_group_on G mul e invg"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have h\<iota>_in: "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<iota>fam \<alpha> x \<in> G"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have h\<iota>_hom: "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<forall>y\<in>GG \<alpha>.
      \<iota>fam \<alpha> (mulGG \<alpha> x y) = mul (\<iota>fam \<alpha> x) (\<iota>fam \<alpha> y)"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have h\<iota>_inj: "\<forall>\<alpha>\<in>J. inj_on (\<iota>fam \<alpha>) (GG \<alpha>)"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have hgen: "G = top1_subgroup_generated_on G mul e invg (\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>)"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have hreduced: "\<forall>indices word.
      length indices = length word \<longrightarrow>
      length indices > 0 \<longrightarrow>
      (\<forall>i<length indices. indices!i \<in> J \<and> word!i \<in> GG (indices!i)
                        \<and> \<iota>fam (indices!i) (word!i) \<noteq> e) \<longrightarrow>
      (\<forall>i. i + 1 < length indices \<longrightarrow> indices!i \<noteq> indices!(i+1)) \<longrightarrow>
      foldr mul (map (\<lambda>i. \<iota>fam (indices!i) (word!i)) [0..<length indices]) e \<noteq> e"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  \<comment> \<open>Existence: define h on generators and extend to G.
     Since G is generated by the \<iota>_\<alpha>(GG_\<alpha>), every element of G is a product of
     generators and their inverses. Define h by h(\<iota>_\<alpha>(x)) = hfam_\<alpha>(x) and extend
     multiplicatively. Well-defined by reduced-word uniqueness.

     Uniqueness: any hom h' with h' \<circ> \<iota>_\<alpha> = hfam_\<alpha> must satisfy h' = h on generators,
     hence h' = h on all of G (since G is generated by the images).\<close>
  \<comment> \<open>Define h by evaluating reduced words in H.\<close>
  \<comment> \<open>Since G is generated by \<iota>_\<alpha>(GG_\<alpha>), every x \<in> G can be written as a product
     of generators. Define h to map each generator \<iota>_\<alpha>(g) to hfam_\<alpha>(g) and extend
     multiplicatively. The reduced-word uniqueness guarantees well-definedness.\<close>
  \<comment> \<open>Existence: h on reduced words, h(x1...xn) = hfam(a1)(x1)*...*hfam(an)(xn).\<close>
  \<comment> \<open>For existence, we use the concrete word-list construction from Theorem 68.2.
     Build a concrete free product G' as word lists. Define h' on G' by word evaluation.
     Then transfer to abstract G via an isomorphism G \<cong> G'.

     But this is circular (68.4 uses 68.3). Instead, we prove existence directly:
     By the generation property, G = subgroup_generated by \<Union> \<iota>_\<alpha>(GG_\<alpha>).
     The reduced-word condition ensures unique evaluation.

     For now, we sorry this and rely on the mathematical validity.\<close>
  \<comment> \<open>Word evaluation function: given indices and word, evaluate in H.\<close>
  let ?eval_H = "\<lambda>indices word n. foldr mulH
      (map (\<lambda>i. hfam (indices!i) (word!i)) [0..<n]) eH"
  \<comment> \<open>Define h: for g = e, h(g) = eH. For g \<noteq> e, pick its reduced-word representation
     (exists by generation, unique by the reduced-word condition) and evaluate in H.\<close>
  let ?h = "\<lambda>g. if g = e then eH
    else let (indices, word) = (SOME (indices, word).
        length indices = length word \<and> length indices > 0
      \<and> (\<forall>i<length indices. indices!i \<in> J \<and> word!i \<in> GG (indices!i)
                          \<and> \<iota>fam (indices!i) (word!i) \<noteq> e)
      \<and> (\<forall>i. i + 1 < length indices \<longrightarrow> indices!i \<noteq> indices!(i+1))
      \<and> foldr mul (map (\<lambda>i. \<iota>fam (indices!i) (word!i)) [0..<length indices]) e = g)
    in ?eval_H (fst (indices, word)) (snd (indices, word)) (length (fst (indices, word)))"
  have hexists: "\<exists>h. top1_group_hom_on G mul H mulH h
      \<and> (\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. h (\<iota>fam \<alpha> x) = hfam \<alpha> x)"
  proof -
    \<comment> \<open>Every g ∈ G has a reduced-word representation. Define ?h by word evaluation:
       h(ιfam(α₁)(g₁) * ... * ιfam(αₙ)(gₙ)) = hfam(α₁)(g₁) * ... * hfam(αₙ)(gₙ).
       Well-defined by uniqueness of reduced words (hreduced).
       This h maps G to H, is a homomorphism, and agrees with hfam on generators.\<close>
    show ?thesis sorry
  qed
  \<comment> \<open>Uniqueness: any h' agreeing on generators agrees on all of G.\<close>
  have hunique: "\<And>h1 h2. top1_group_hom_on G mul H mulH h1 \<Longrightarrow>
      (\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. h1 (\<iota>fam \<alpha> x) = hfam \<alpha> x) \<Longrightarrow>
      top1_group_hom_on G mul H mulH h2 \<Longrightarrow>
      (\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. h2 (\<iota>fam \<alpha> x) = hfam \<alpha> x) \<Longrightarrow>
      \<forall>g\<in>G. h1 g = h2 g"
  proof -
    fix h1 h2
    assume hh1: "top1_group_hom_on G mul H mulH h1"
       and hext1: "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. h1 (\<iota>fam \<alpha> x) = hfam \<alpha> x"
       and hh2: "top1_group_hom_on G mul H mulH h2"
       and hext2: "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. h2 (\<iota>fam \<alpha> x) = hfam \<alpha> x"
    \<comment> \<open>h1 and h2 agree on all generators \<iota>_\<alpha>(x).\<close>
    have hagree_gen: "\<forall>g\<in>(\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>). h1 g = h2 g"
    proof (intro ballI)
      fix g assume "g \<in> (\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>)"
      then obtain \<alpha> x where h\<alpha>: "\<alpha> \<in> J" and hx: "x \<in> GG \<alpha>" and hg: "g = \<iota>fam \<alpha> x"
        by (by100 blast)
      have "h1 g = hfam \<alpha> x" using hg hext1 h\<alpha> hx by (by100 simp)
      also have "\<dots> = h2 g" using hg hext2 h\<alpha> hx by (by100 simp)
      finally show "h1 g = h2 g" .
    qed
    \<comment> \<open>The set K = {g \<in> G. h1 g = h2 g} contains the generators and is a subgroup.
       Since G = subgroup_generated by generators, K = G.\<close>
    let ?K = "{g \<in> G. h1 g = h2 g}"
    have hK_sub: "?K \<subseteq> G" by (by100 blast)
    have hK_grp: "top1_is_group_on ?K mul e invg"
    proof -
      have heG: "e \<in> G" using hG unfolding top1_is_group_on_def by (by100 blast)
      have hmul_closed: "\<forall>x\<in>G. \<forall>y\<in>G. mul x y \<in> G"
        using hG unfolding top1_is_group_on_def by (by100 blast)
      have hinv_closed: "\<forall>x\<in>G. invg x \<in> G"
        using hG unfolding top1_is_group_on_def by (by100 blast)
      have hassoc: "\<forall>x\<in>G. \<forall>y\<in>G. \<forall>z\<in>G. mul (mul x y) z = mul x (mul y z)"
        using hG unfolding top1_is_group_on_def by (by100 blast)
      have hid_left: "\<forall>x\<in>G. mul e x = x"
        using hG unfolding top1_is_group_on_def by (by100 blast)
      have hid_right: "\<forall>x\<in>G. mul x e = x"
        using hG unfolding top1_is_group_on_def by (by100 blast)
      have hinv_left: "\<forall>x\<in>G. mul (invg x) x = e"
        using hG unfolding top1_is_group_on_def by (by100 blast)
      have hinv_right: "\<forall>x\<in>G. mul x (invg x) = e"
        using hG unfolding top1_is_group_on_def by (by100 blast)
      \<comment> \<open>h1(e) = eH (inline hom_preserves_id logic): h1(e*e) = h1(e)*h1(e), so h1(e) = eH.\<close>
      \<comment> \<open>Inline hom_preserves_id: h(e*e)=h(e)*h(e) and e*e=e, so h(e)=h(e)*h(e).
         Multiply by invgH(h(e)) to get eH=h(e).\<close>
      have hh1_maps: "\<forall>x\<in>G. h1 x \<in> H" and hh1_mul: "\<forall>x\<in>G. \<forall>y\<in>G. h1 (mul x y) = mulH (h1 x) (h1 y)"
        using hh1 unfolding top1_group_hom_on_def by (by100 blast)+
      have hh2_maps: "\<forall>x\<in>G. h2 x \<in> H" and hh2_mul: "\<forall>x\<in>G. \<forall>y\<in>G. h2 (mul x y) = mulH (h2 x) (h2 y)"
        using hh2 unfolding top1_group_hom_on_def by (by100 blast)+
      \<comment> \<open>Extract H group axioms for use in h(e)=eH proof.\<close>
      have hH_inv_right: "\<forall>x\<in>H. mulH x (invgH x) = eH"
        using hH unfolding top1_is_group_on_def by (by100 blast)
      have hH_id_right: "\<forall>x\<in>H. mulH x eH = x"
        using hH unfolding top1_is_group_on_def by (by100 blast)
      have hH_inv_closed: "\<forall>x\<in>H. invgH x \<in> H"
        using hH unfolding top1_is_group_on_def by (by100 blast)
      have hH_assoc: "\<forall>x\<in>H. \<forall>y\<in>H. \<forall>z\<in>H. mulH (mulH x y) z = mulH x (mulH y z)"
        using hH unfolding top1_is_group_on_def by (by100 blast)
      have hh1e: "h1 e = eH"
      proof -
        have hh1eH: "h1 e \<in> H" using hh1_maps heG by (by100 blast)
        have hinvh1e: "invgH (h1 e) \<in> H" using hH_inv_closed hh1eH by (by100 blast)
        have "h1 e = mulH (h1 e) (h1 e)"
        proof -
          have "h1 (mul e e) = mulH (h1 e) (h1 e)" using hh1_mul heG by (by100 blast)
          moreover have "mul e e = e" using hid_left heG by (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
        have h1e_inv: "mulH (h1 e) (invgH (h1 e)) = eH"
          using hH_inv_right hh1eH by (by100 blast)
        have "eH = mulH (mulH (h1 e) (h1 e)) (invgH (h1 e))"
          using \<open>h1 e = mulH (h1 e) (h1 e)\<close> h1e_inv by (by100 simp)
        also have "\<dots> = mulH (h1 e) (mulH (h1 e) (invgH (h1 e)))"
          using hH_assoc hh1eH hinvh1e by (by100 blast)
        also have "mulH (h1 e) (invgH (h1 e)) = eH" using hH_inv_right hh1eH by (by100 blast)
        also have "mulH (h1 e) eH = h1 e" using hH_id_right hh1eH by (by100 blast)
        finally show "h1 e = eH" by (by100 simp)
      qed
      have hh2e: "h2 e = eH"
      proof -
        have hh2eH: "h2 e \<in> H" using hh2_maps heG by (by100 blast)
        have hinvh2e: "invgH (h2 e) \<in> H" using hH_inv_closed hh2eH by (by100 blast)
        have "h2 e = mulH (h2 e) (h2 e)"
        proof -
          have "h2 (mul e e) = mulH (h2 e) (h2 e)" using hh2_mul heG by (by100 blast)
          moreover have "mul e e = e" using hid_left heG by (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
        have h2e_inv: "mulH (h2 e) (invgH (h2 e)) = eH"
          using hH_inv_right hh2eH by (by100 blast)
        have "eH = mulH (mulH (h2 e) (h2 e)) (invgH (h2 e))"
          using \<open>h2 e = mulH (h2 e) (h2 e)\<close> h2e_inv by (by100 simp)
        also have "\<dots> = mulH (h2 e) (mulH (h2 e) (invgH (h2 e)))"
          using hH_assoc hh2eH hinvh2e by (by100 blast)
        also have "mulH (h2 e) (invgH (h2 e)) = eH" using hH_inv_right hh2eH by (by100 blast)
        also have "mulH (h2 e) eH = h2 e" using hH_id_right hh2eH by (by100 blast)
        finally show "h2 e = eH" by (by100 simp)
      qed
      have "h1 e = h2 e" using hh1e hh2e by (by100 simp)
      hence "e \<in> ?K" using heG by (by100 blast)
      \<comment> \<open>mul closed: h1(xy) = h1(x)*h1(y) = h2(x)*h2(y) = h2(xy).\<close>
      moreover have "\<forall>x\<in>?K. \<forall>y\<in>?K. mul x y \<in> ?K"
      proof (intro ballI)
        fix x y assume "x \<in> ?K" "y \<in> ?K"
        hence hxG: "x \<in> G" "h1 x = h2 x" and hyG: "y \<in> G" "h1 y = h2 y" by (by100 blast)+
        have "h1 (mul x y) = mulH (h1 x) (h1 y)"
          using hh1 hxG(1) hyG(1) unfolding top1_group_hom_on_def by (by100 blast)
        also have "\<dots> = mulH (h2 x) (h2 y)" using hxG(2) hyG(2) by (by100 simp)
        also have "\<dots> = h2 (mul x y)"
        proof -
          have "h2 (mul x y) = mulH (h2 x) (h2 y)"
            using hh2_mul hxG(1) hyG(1) by (by100 blast)
          thus ?thesis by (by100 simp)
        qed
        finally show "mul x y \<in> ?K" using hmul_closed hxG(1) hyG(1) by (by100 blast)
      qed
      \<comment> \<open>inv closed: h1(invg x) = invgH(h1 x) = invgH(h2 x) = h2(invg x).\<close>
      moreover have "\<forall>x\<in>?K. invg x \<in> ?K"
      proof (intro ballI)
        fix x assume "x \<in> ?K"
        hence hxG: "x \<in> G" "h1 x = h2 x" by (by100 blast)+
        \<comment> \<open>h1(invg x) = invgH(h1 x) = invgH(h2 x) = h2(invg x).\<close>
        have "h1 (invg x) = h2 (invg x)"
        proof -
          have hixG: "invg x \<in> G" using hinv_closed hxG(1) by (by100 blast)
          \<comment> \<open>h1(invg x) * h1(x) = h1(invg x * x) = h1(e) = eH.\<close>
          have "h1 (mul (invg x) x) = mulH (h1 (invg x)) (h1 x)"
            using hh1_mul hixG hxG(1) by (by100 blast)
          moreover have "mul (invg x) x = e" using hinv_left hxG(1) by (by100 blast)
          ultimately have h1inv_eq: "mulH (h1 (invg x)) (h1 x) = eH" using hh1e by (by100 simp)
          \<comment> \<open>Similarly for h2.\<close>
          have "h2 (mul (invg x) x) = mulH (h2 (invg x)) (h2 x)"
            using hh2_mul hixG hxG(1) by (by100 blast)
          hence h2inv_eq: "mulH (h2 (invg x)) (h2 x) = eH" using hh2e hinv_left hxG(1) by (by100 simp)
          \<comment> \<open>h1(invg x)*h1(x) = eH and h2(invg x)*h2(x) = eH with h1(x)=h2(x).
             Left inverse is unique in a group, so h1(invg x) = h2(invg x).\<close>
          have hh1ix: "h1 (invg x) \<in> H" using hh1_maps hixG by (by100 blast)
          have hh2ix: "h2 (invg x) \<in> H" using hh2_maps hixG by (by100 blast)
          have hhx: "h1 x \<in> H" using hh1_maps hxG(1) by (by100 blast)
          \<comment> \<open>From a*b=eH in a group: a = invgH(b). So h1(invg x) = invgH(h1 x) = invgH(h2 x) = h2(invg x).\<close>
          have "h1 (invg x) = mulH (h1 (invg x)) (mulH (h1 x) (invgH (h1 x)))"
            using hH_inv_right hhx hH_id_right hh1ix by (by100 force)
          also have "\<dots> = mulH (mulH (h1 (invg x)) (h1 x)) (invgH (h1 x))"
          proof -
            have "invgH (h1 x) \<in> H" using hH_inv_closed hhx by (by100 blast)
            thus ?thesis using hH_assoc hh1ix hhx by (by100 force)
          qed
          also have "mulH (h1 (invg x)) (h1 x) = eH" by (rule h1inv_eq)
          also have "mulH eH (invgH (h1 x)) = invgH (h1 x)"
            using hH hH_inv_closed hhx unfolding top1_is_group_on_def by (by100 blast)
          finally have "h1 (invg x) = invgH (h1 x)" .
          also have "\<dots> = invgH (h2 x)" using hxG(2) by (by100 simp)
          also have "\<dots> = h2 (invg x)"
          proof -
            \<comment> \<open>Same argument: h2(invg x) = invgH(h2 x).\<close>
            have hhx2: "h2 x \<in> H" using hh2_maps hxG(1) by (by100 blast)
            have "h2 (invg x) = mulH (h2 (invg x)) (mulH (h2 x) (invgH (h2 x)))"
              using hH_inv_right hhx2 hH_id_right hh2ix by (by100 force)
            also have "\<dots> = mulH (mulH (h2 (invg x)) (h2 x)) (invgH (h2 x))"
            proof -
              have "invgH (h2 x) \<in> H" using hH_inv_closed hhx2 by (by100 blast)
              thus ?thesis using hH_assoc hh2ix hhx2 by (by100 force)
            qed
            also have "mulH (h2 (invg x)) (h2 x) = eH"
              by (rule h2inv_eq)
            also have "mulH eH (invgH (h2 x)) = invgH (h2 x)"
              using hH hH_inv_closed hhx2 unfolding top1_is_group_on_def by (by100 blast)
            finally show ?thesis by (by100 simp)
          qed
          finally show ?thesis .
        qed
        thus "invg x \<in> ?K" using hinv_closed hxG(1) by (by100 blast)
      qed
      \<comment> \<open>Axioms: inherited from G.\<close>
      moreover have "\<forall>x\<in>?K. \<forall>y\<in>?K. \<forall>z\<in>?K. mul (mul x y) z = mul x (mul y z)"
        using hassoc by (by100 blast)
      moreover have "\<forall>x\<in>?K. mul e x = x" using hid_left by (by100 blast)
      moreover have "\<forall>x\<in>?K. mul x e = x" using hid_right by (by100 blast)
      moreover have "\<forall>x\<in>?K. mul (invg x) x = e" using hinv_left by (by100 blast)
      moreover have "\<forall>x\<in>?K. mul x (invg x) = e" using hinv_right by (by100 blast)
      ultimately show ?thesis unfolding top1_is_group_on_def by (by100 blast)
    qed
    have hgens_K: "(\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>) \<subseteq> ?K"
      using hagree_gen h\<iota>_in by (by100 blast)
    have "G \<subseteq> ?K"
      using hgen subgroup_generated_minimal[OF hgens_K hK_sub hK_grp] by (by100 simp)
    hence hagree: "\<forall>g\<in>G. h1 g = h2 g" by (by100 blast)
    \<comment> \<open>Extensionality: h1 and h2 are the same function.
       We can show h1 = h2 by choosing an arbitrary extension.
       Actually, for ∃!, we need h1 = h2 as functions, not just on G.
       Since the hom property constrains values on G only, and the extension
       is implicitly defined by the reduced-word map, two such extensions
       must agree on G. For values outside G, the hom property doesn't constrain them.
       We handle this by sorry-ing the extensionality step.\<close>
    show "\<forall>g\<in>G. h1 g = h2 g" by (rule hagree)
  qed
  show ?thesis
  proof -
    obtain h where hh_hom: "top1_group_hom_on G mul H mulH h"
        and hh_ext: "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. h (\<iota>fam \<alpha> x) = hfam \<alpha> x"
      using hexists by (by100 blast)
    have hh_unique: "\<forall>h'. top1_group_hom_on G mul H mulH h'
        \<longrightarrow> (\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. h' (\<iota>fam \<alpha> x) = hfam \<alpha> x)
        \<longrightarrow> (\<forall>g\<in>G. h' g = h g)"
      using hunique[OF _ _ hh_hom hh_ext] by (by100 blast)
    show ?thesis
      using hh_hom hh_ext hh_unique by (by100 blast)
  qed
qed

(** from \<S>68 Theorem 68.4: uniqueness of free product — any two
    free products of the same family are isomorphic. **)
theorem Theorem_68_4_free_product_unique:
  assumes hG1: "top1_is_free_product_on (G1::'g set) mul1 e1 invg1 GG mulGG \<iota>1 J"
      and hG2: "top1_is_free_product_on (G2::'g set) mul2 e2 invg2 GG mulGG \<iota>2 J"
  shows "top1_groups_isomorphic_on G1 mul1 G2 mul2"
proof -
  \<comment> \<open>Munkres 68.4: Use extension property (Lemma 68.3) to build \<phi>: G1 \<rightarrow> G2 and \<psi>: G2 \<rightarrow> G1.\<close>
  have hgrp1: "top1_is_group_on G1 mul1 e1 invg1"
    using hG1 unfolding top1_is_free_product_on_def by (by100 blast)
  have hgrp2: "top1_is_group_on G2 mul2 e2 invg2"
    using hG2 unfolding top1_is_free_product_on_def by (by100 blast)
  \<comment> \<open>Step 1: \<iota>2_\<alpha> : GG_\<alpha> \<rightarrow> G2 are hom. Apply 68.3 to G1 to get \<phi>: G1 \<rightarrow> G2.\<close>
  have h\<iota>2_hom: "\<forall>\<alpha>\<in>J. top1_group_hom_on (GG \<alpha>) (mulGG \<alpha>) G2 mul2 (\<iota>2 \<alpha>)"
  proof (intro ballI)
    fix \<alpha> assume h\<alpha>: "\<alpha> \<in> J"
    show "top1_group_hom_on (GG \<alpha>) (mulGG \<alpha>) G2 mul2 (\<iota>2 \<alpha>)"
      unfolding top1_group_hom_on_def
      using hG2 h\<alpha> unfolding top1_is_free_product_on_def by (by100 blast)
  qed
  obtain \<phi> where h\<phi>_hom: "top1_group_hom_on G1 mul1 G2 mul2 \<phi>"
      and h\<phi>_ext: "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<phi> (\<iota>1 \<alpha> x) = \<iota>2 \<alpha> x"
    using Lemma_68_3_extension_property[OF hG1 hgrp2 h\<iota>2_hom] by (by100 blast)
  \<comment> \<open>Step 2: Similarly \<psi>: G2 \<rightarrow> G1.\<close>
  have h\<iota>1_hom: "\<forall>\<alpha>\<in>J. top1_group_hom_on (GG \<alpha>) (mulGG \<alpha>) G1 mul1 (\<iota>1 \<alpha>)"
  proof (intro ballI)
    fix \<alpha> assume h\<alpha>: "\<alpha> \<in> J"
    show "top1_group_hom_on (GG \<alpha>) (mulGG \<alpha>) G1 mul1 (\<iota>1 \<alpha>)"
      unfolding top1_group_hom_on_def
      using hG1 h\<alpha> unfolding top1_is_free_product_on_def by (by100 blast)
  qed
  obtain \<psi> where h\<psi>_hom: "top1_group_hom_on G2 mul2 G1 mul1 \<psi>"
      and h\<psi>_ext: "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<psi> (\<iota>2 \<alpha> x) = \<iota>1 \<alpha> x"
    using Lemma_68_3_extension_property[OF hG2 hgrp1 h\<iota>1_hom] by (by100 blast)
  \<comment> \<open>Step 3: \<psi>\<circ>\<phi> extends id on generators of G1. By uniqueness, \<psi>\<circ>\<phi> = id on G1.\<close>
  \<comment> \<open>Step 3: \<psi>\<circ>\<phi> extends id on generators. id also extends id. By uniqueness, \<psi>\<circ>\<phi> = id.\<close>
  have h\<psi>\<phi>_ext: "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. (\<psi> \<circ> \<phi>) (\<iota>1 \<alpha> x) = \<iota>1 \<alpha> x"
  proof (intro ballI)
    fix \<alpha> x assume h\<alpha>: "\<alpha> \<in> J" and hx: "x \<in> GG \<alpha>"
    have "(\<psi> \<circ> \<phi>) (\<iota>1 \<alpha> x) = \<psi> (\<phi> (\<iota>1 \<alpha> x))" by (by100 simp)
    also have "\<phi> (\<iota>1 \<alpha> x) = \<iota>2 \<alpha> x" using h\<phi>_ext h\<alpha> hx by (by100 blast)
    also have "\<psi> (\<iota>2 \<alpha> x) = \<iota>1 \<alpha> x" using h\<psi>_ext h\<alpha> hx by (by100 blast)
    finally show "(\<psi> \<circ> \<phi>) (\<iota>1 \<alpha> x) = \<iota>1 \<alpha> x" .
  qed
  \<comment> \<open>id: G1 \<rightarrow> G1 also extends \<iota>1. By uniqueness (68.3 for G1 with H=G1), \<psi>\<circ>\<phi> = id.\<close>
  have h\<psi>\<phi>_id: "\<forall>x\<in>G1. \<psi> (\<phi> x) = x"
  proof -
    \<comment> \<open>\<psi>\<circ>\<phi> and id are both homs G1\<rightarrow>G1 agreeing on generators. By uniqueness, they're equal on G1.\<close>
    have hcomp_hom: "top1_group_hom_on G1 mul1 G1 mul1 (\<psi> \<circ> \<phi>)"
      unfolding top1_group_hom_on_def
    proof (intro conjI ballI)
      fix x assume "x \<in> G1"
      hence "\<phi> x \<in> G2" using h\<phi>_hom unfolding top1_group_hom_on_def by (by100 blast)
      thus "(\<psi> \<circ> \<phi>) x \<in> G1" using h\<psi>_hom unfolding top1_group_hom_on_def comp_def by (by100 blast)
    next
      fix x y assume "x \<in> G1" "y \<in> G1"
      have "\<phi> x \<in> G2" "\<phi> y \<in> G2"
        using h\<phi>_hom \<open>x \<in> G1\<close> \<open>y \<in> G1\<close> unfolding top1_group_hom_on_def by (by100 blast)+
      show "(\<psi> \<circ> \<phi>) (mul1 x y) = mul1 ((\<psi> \<circ> \<phi>) x) ((\<psi> \<circ> \<phi>) y)"
        using h\<phi>_hom h\<psi>_hom \<open>x \<in> G1\<close> \<open>y \<in> G1\<close> \<open>\<phi> x \<in> G2\<close> \<open>\<phi> y \<in> G2\<close>
        unfolding top1_group_hom_on_def comp_def by (by100 force)
    qed
    have hid_hom: "top1_group_hom_on G1 mul1 G1 mul1 id"
      unfolding top1_group_hom_on_def id_def
      using hG1 unfolding top1_is_free_product_on_def top1_is_group_on_def by (by100 blast)
    have hid_ext: "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. id (\<iota>1 \<alpha> x) = \<iota>1 \<alpha> x"
      by (by100 simp)
    \<comment> \<open>Apply 68.3 uniqueness to G1 with H=G1: both \<psi>\<circ>\<phi> and id agree on generators,
       so they agree on all of G1.\<close>
    obtain h_ref where href_hom: "top1_group_hom_on G1 mul1 G1 mul1 h_ref"
        and href_ext: "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. h_ref (\<iota>1 \<alpha> x) = \<iota>1 \<alpha> x"
        and href_u: "\<forall>h'. top1_group_hom_on G1 mul1 G1 mul1 h'
            \<longrightarrow> (\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. h' (\<iota>1 \<alpha> x) = \<iota>1 \<alpha> x)
            \<longrightarrow> (\<forall>g\<in>G1. h' g = h_ref g)"
      using Lemma_68_3_extension_property[OF hG1 hgrp1 h\<iota>1_hom] by (by100 blast)
    have "\<forall>g\<in>G1. (\<psi> \<circ> \<phi>) g = h_ref g"
      using href_u hcomp_hom h\<psi>\<phi>_ext by (by100 blast)
    moreover have "\<forall>g\<in>G1. id g = h_ref g"
      using href_u hid_hom hid_ext by (by100 blast)
    ultimately show ?thesis by (by100 force)
  qed
  \<comment> \<open>Step 4: Similarly \<phi>\<circ>\<psi> = id on G2.\<close>
  have h\<phi>\<psi>_id: "\<forall>x\<in>G2. \<phi> (\<psi> x) = x"
  proof -
    have hcomp_hom2: "top1_group_hom_on G2 mul2 G2 mul2 (\<phi> \<circ> \<psi>)"
      unfolding top1_group_hom_on_def
    proof (intro conjI ballI)
      fix x assume "x \<in> G2"
      hence "\<psi> x \<in> G1" using h\<psi>_hom unfolding top1_group_hom_on_def by (by100 blast)
      thus "(\<phi> \<circ> \<psi>) x \<in> G2" using h\<phi>_hom unfolding top1_group_hom_on_def comp_def by (by100 blast)
    next
      fix x y assume "x \<in> G2" "y \<in> G2"
      have "\<psi> x \<in> G1" "\<psi> y \<in> G1"
        using h\<psi>_hom \<open>x \<in> G2\<close> \<open>y \<in> G2\<close> unfolding top1_group_hom_on_def by (by100 blast)+
      show "(\<phi> \<circ> \<psi>) (mul2 x y) = mul2 ((\<phi> \<circ> \<psi>) x) ((\<phi> \<circ> \<psi>) y)"
        using h\<psi>_hom h\<phi>_hom \<open>x \<in> G2\<close> \<open>y \<in> G2\<close> \<open>\<psi> x \<in> G1\<close> \<open>\<psi> y \<in> G1\<close>
        unfolding top1_group_hom_on_def comp_def by (by100 force)
    qed
    have hid_hom2: "top1_group_hom_on G2 mul2 G2 mul2 id"
      unfolding top1_group_hom_on_def id_def
      using hG2 unfolding top1_is_free_product_on_def top1_is_group_on_def by (by100 blast)
    have hid_ext2: "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. id (\<iota>2 \<alpha> x) = \<iota>2 \<alpha> x"
      by (by100 simp)
    have h\<phi>\<psi>_ext: "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. (\<phi> \<circ> \<psi>) (\<iota>2 \<alpha> x) = \<iota>2 \<alpha> x"
    proof (intro ballI)
      fix \<alpha> x assume "\<alpha> \<in> J" "x \<in> GG \<alpha>"
      have "(\<phi> \<circ> \<psi>) (\<iota>2 \<alpha> x) = \<phi> (\<psi> (\<iota>2 \<alpha> x))" by (by100 simp)
      also have "\<psi> (\<iota>2 \<alpha> x) = \<iota>1 \<alpha> x" using h\<psi>_ext \<open>\<alpha> \<in> J\<close> \<open>x \<in> GG \<alpha>\<close> by (by100 blast)
      also have "\<phi> (\<iota>1 \<alpha> x) = \<iota>2 \<alpha> x" using h\<phi>_ext \<open>\<alpha> \<in> J\<close> \<open>x \<in> GG \<alpha>\<close> by (by100 blast)
      finally show "(\<phi> \<circ> \<psi>) (\<iota>2 \<alpha> x) = \<iota>2 \<alpha> x" .
    qed
    obtain h_ref2 where href2_hom: "top1_group_hom_on G2 mul2 G2 mul2 h_ref2"
        and href2_ext: "\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. h_ref2 (\<iota>2 \<alpha> x) = \<iota>2 \<alpha> x"
        and href2_u: "\<forall>h'. top1_group_hom_on G2 mul2 G2 mul2 h'
            \<longrightarrow> (\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. h' (\<iota>2 \<alpha> x) = \<iota>2 \<alpha> x)
            \<longrightarrow> (\<forall>g\<in>G2. h' g = h_ref2 g)"
      using Lemma_68_3_extension_property[OF hG2 hgrp2 h\<iota>2_hom] by (by100 blast)
    have "\<forall>g\<in>G2. (\<phi> \<circ> \<psi>) g = h_ref2 g"
      using href2_u hcomp_hom2 h\<phi>\<psi>_ext by (by100 blast)
    moreover have "\<forall>g\<in>G2. id g = h_ref2 g"
      using href2_u hid_hom2 hid_ext2 by (by100 blast)
    ultimately show ?thesis by (by100 force)
  qed
  \<comment> \<open>Step 5: \<phi> is bijective (has two-sided inverse \<psi>).\<close>
  have himg1: "\<phi> ` G1 \<subseteq> G2"
  proof (rule subsetI)
    fix y assume "y \<in> \<phi> ` G1"
    then obtain x where "x \<in> G1" "y = \<phi> x" by (by100 blast)
    thus "y \<in> G2" using h\<phi>_hom unfolding top1_group_hom_on_def by (by100 blast)
  qed
  have himg2: "\<psi> ` G2 \<subseteq> G1"
  proof (rule subsetI)
    fix y assume "y \<in> \<psi> ` G2"
    then obtain x where "x \<in> G2" "y = \<psi> x" by (by100 blast)
    thus "y \<in> G1" using h\<psi>_hom unfolding top1_group_hom_on_def by (by100 blast)
  qed
  have "bij_betw \<phi> G1 G2"
    unfolding bij_betw_def
  proof (intro conjI)
    show "inj_on \<phi> G1"
    proof (rule inj_onI)
      fix x y assume "x \<in> G1" "y \<in> G1" "\<phi> x = \<phi> y"
      hence "\<psi> (\<phi> x) = \<psi> (\<phi> y)" by (by100 simp)
      thus "x = y" using h\<psi>\<phi>_id \<open>x \<in> G1\<close> \<open>y \<in> G1\<close> by (by100 force)
    qed
    show "\<phi> ` G1 = G2"
    proof (rule set_eqI)
      fix y show "y \<in> \<phi> ` G1 \<longleftrightarrow> y \<in> G2"
      proof
        assume "y \<in> \<phi> ` G1" thus "y \<in> G2" using himg1 by (by100 blast)
      next
        assume "y \<in> G2"
        hence "\<psi> y \<in> G1" using himg2 by (by100 blast)
        moreover have "\<phi> (\<psi> y) = y" using h\<phi>\<psi>_id \<open>y \<in> G2\<close> by (by100 blast)
        ultimately show "y \<in> \<phi> ` G1" by (by100 force)
      qed
    qed
  qed
  thus ?thesis unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
    using h\<phi>_hom by (by100 blast)
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
  shows "\<exists>(FP :: (nat \<times> 'g) list set) mulFP eFP invgFP \<iota>fam12
          (FPQ :: (nat \<times> 'g set) list set) mulFPQ eFPQ invgFPQ \<iota>famQ.
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
  have hgroups: "\<forall>\<alpha>\<in>({0,1}::nat set). top1_is_group_on
      ((if \<alpha> = 0 then G1 else G2)::'g set)
      (if \<alpha> = 0 then mul1 else mul2)
      (if \<alpha> = 0 then e1 else e2)
      (if \<alpha> = 0 then invg1 else invg2)"
    using assms(1) assms(2) by (by100 auto)
  obtain FP :: "(nat \<times> 'g) list set" and mulFP eFP invgFP \<iota>fam12 where
      hFP: "top1_is_free_product_on FP mulFP eFP invgFP
        (\<lambda>i::nat. if i = 0 then G1 else G2) (\<lambda>i. if i = 0 then mul1 else mul2) \<iota>fam12 {0,1}"
  proof -
    from Theorem_68_2_free_product_exists[OF hgroups]
    show ?thesis using that by blast
  qed
  \<comment> \<open>Step 2: Build quotient groups G1/N1, G2/N2.\<close>
  have hQ1_grp: "top1_is_group_on
      (top1_quotient_group_carrier_on G1 mul1 N1)
      (top1_quotient_group_mul_on mul1)
      (top1_group_coset_on G1 mul1 N1 e1)
      (\<lambda>C. top1_group_coset_on G1 mul1 N1
                   (invg1 (SOME g. g \<in> G1 \<and> C = top1_group_coset_on G1 mul1 N1 g)))"
    by (rule quotient_group_is_group[OF assms(1) assms(3)])
  have hQ2_grp: "top1_is_group_on
      (top1_quotient_group_carrier_on G2 mul2 N2)
      (top1_quotient_group_mul_on mul2)
      (top1_group_coset_on G2 mul2 N2 e2)
      (\<lambda>C. top1_group_coset_on G2 mul2 N2
                   (invg2 (SOME g. g \<in> G2 \<and> C = top1_group_coset_on G2 mul2 N2 g)))"
    by (rule quotient_group_is_group[OF assms(2) assms(4)])
  have hQ_groups: "\<forall>\<alpha>\<in>({0,1}::nat set). top1_is_group_on
      ((if \<alpha> = 0 then top1_quotient_group_carrier_on G1 mul1 N1
                 else top1_quotient_group_carrier_on G2 mul2 N2) :: 'g set set)
      (top1_quotient_group_mul_on (if \<alpha> = 0 then mul1 else mul2))
      (if \<alpha> = 0 then top1_group_coset_on G1 mul1 N1 e1
                 else top1_group_coset_on G2 mul2 N2 e2)
      (if \<alpha> = 0 then (\<lambda>C. top1_group_coset_on G1 mul1 N1
                   (invg1 (SOME g. g \<in> G1 \<and> C = top1_group_coset_on G1 mul1 N1 g)))
                 else (\<lambda>C. top1_group_coset_on G2 mul2 N2
                   (invg2 (SOME g. g \<in> G2 \<and> C = top1_group_coset_on G2 mul2 N2 g))))"
    using hQ1_grp hQ2_grp by (by100 auto)
  \<comment> \<open>Step 3: Build FPQ = (G1/N1) * (G2/N2).\<close>
  obtain FPQ :: "(nat \<times> 'g set) list set" and mulFPQ eFPQ invgFPQ \<iota>famQ where
      hFPQ: "top1_is_free_product_on FPQ mulFPQ eFPQ invgFPQ
        (\<lambda>i::nat. if i = 0 then top1_quotient_group_carrier_on G1 mul1 N1
                   else top1_quotient_group_carrier_on G2 mul2 N2)
        (\<lambda>i::nat. top1_quotient_group_mul_on (if i = 0 then mul1 else mul2))
        \<iota>famQ {0, 1}"
  proof -
    from Theorem_68_2_free_product_exists[OF hQ_groups]
    show ?thesis using that by blast
  qed
  \<comment> \<open>Step 4: Define π: FP → FPQ by extending quotient projections. Show surjective hom.\<close>
  have hFP_grp: "top1_is_group_on FP mulFP eFP invgFP"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have hFPQ_grp: "top1_is_group_on FPQ mulFPQ eFPQ invgFPQ"
    using hFPQ unfolding top1_is_free_product_on_def by (by100 blast)
  let ?K = "top1_normal_subgroup_generated_on FP mulFP eFP invgFP
               (\<iota>fam12 0 ` N1 \<union> \<iota>fam12 1 ` N2)"
  have h_surj_hom: "\<exists>\<pi>. top1_group_hom_on FP mulFP FPQ mulFPQ \<pi> \<and> \<pi> ` FP = FPQ
      \<and> top1_group_kernel_on FP eFPQ \<pi> = ?K" sorry
  \<comment> \<open>Step 5: First isomorphism theorem: FP/?K ≅ FPQ.\<close>
  have hgens_sub: "\<iota>fam12 0 ` N1 \<union> \<iota>fam12 1 ` N2 \<subseteq> FP"
  proof -
    have h\<iota>_in: "\<forall>\<alpha>\<in>{0,1::nat}. \<forall>x\<in>(if \<alpha> = 0 then G1 else G2). \<iota>fam12 \<alpha> x \<in> FP"
      using hFP unfolding top1_is_free_product_on_def by (by100 blast)
    have hN1_sub: "N1 \<subseteq> G1" using assms(3) unfolding top1_normal_subgroup_on_def by (by100 blast)
    have hN2_sub: "N2 \<subseteq> G2" using assms(4) unfolding top1_normal_subgroup_on_def by (by100 blast)
    have "\<iota>fam12 0 ` N1 \<subseteq> FP"
    proof (rule image_subsetI)
      fix n assume "n \<in> N1"
      hence "n \<in> G1" using hN1_sub by (by100 blast)
      thus "\<iota>fam12 0 n \<in> FP" using h\<iota>_in by (by100 force)
    qed
    moreover have "\<iota>fam12 1 ` N2 \<subseteq> FP"
    proof (rule image_subsetI)
      fix n assume "n \<in> N2"
      hence "n \<in> G2" using hN2_sub by (by100 blast)
      thus "\<iota>fam12 1 n \<in> FP" using h\<iota>_in by (by100 force)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  have hK_normal: "top1_normal_subgroup_on FP mulFP eFP invgFP ?K"
    by (rule normal_subgroup_generated_is_normal[OF hFP_grp hgens_sub])
  \<comment> \<open>Step 6: Apply first isomorphism theorem.\<close>
  obtain \<pi> where h\<pi>_hom: "top1_group_hom_on FP mulFP FPQ mulFPQ \<pi>"
      and h\<pi>_surj: "\<pi> ` FP = FPQ"
      and h\<pi>_ker: "top1_group_kernel_on FP eFPQ \<pi> = ?K"
    using h_surj_hom by (by100 blast)
  have hiso: "top1_groups_isomorphic_on FPQ mulFPQ
      (top1_quotient_group_carrier_on FP mulFP ?K) (top1_quotient_group_mul_on mulFP)"
    by (rule first_isomorphism_theorem[OF hFP_grp hK_normal hFPQ_grp h\<pi>_hom h\<pi>_surj h\<pi>_ker])
  \<comment> \<open>Symmetry of isomorphism.\<close>
  have hQ_grp: "top1_is_group_on
      (top1_quotient_group_carrier_on FP mulFP ?K) (top1_quotient_group_mul_on mulFP)
      (top1_group_coset_on FP mulFP ?K eFP)
      (\<lambda>C. top1_group_coset_on FP mulFP ?K
         (invgFP (SOME g. g \<in> FP \<and> C = top1_group_coset_on FP mulFP ?K g)))"
    by (rule quotient_group_is_group[OF hFP_grp hK_normal])
  have hiso_sym: "top1_groups_isomorphic_on
      (top1_quotient_group_carrier_on FP mulFP ?K) (top1_quotient_group_mul_on mulFP)
      FPQ mulFPQ"
    by (rule top1_groups_isomorphic_on_sym[OF hiso hFPQ_grp hQ_grp])
  show ?thesis using hFP hFPQ hiso_sym by (by100 blast)
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
  shows "\<exists>(FP :: (nat \<times> 'g) list set) mulFP eFP invgFP \<iota>fam12 \<iota>S12.
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
  have hgroups: "\<forall>\<alpha>\<in>({0,1}::nat set). top1_is_group_on
      ((if \<alpha> = 0 then G1 else G2)::'g set) (if \<alpha> = 0 then mul1 else mul2)
      (if \<alpha> = 0 then e1 else e2) (if \<alpha> = 0 then invg1 else invg2)"
  proof (intro ballI)
    fix \<alpha> :: nat assume "\<alpha> \<in> {0, 1}"
    hence "\<alpha> = 0 \<or> \<alpha> = 1" by (by100 blast)
    thus "top1_is_group_on (if \<alpha> = 0 then G1 else G2) (if \<alpha> = 0 then mul1 else mul2)
        (if \<alpha> = 0 then e1 else e2) (if \<alpha> = 0 then invg1 else invg2)"
    proof
      assume "\<alpha> = 0"
      thus ?thesis using assms(1) unfolding top1_is_free_group_full_on_def by (by100 simp)
    next
      assume "\<alpha> = 1"
      thus ?thesis using assms(2) unfolding top1_is_free_group_full_on_def by (by100 simp)
    qed
  qed
  obtain FP :: "(nat \<times> 'g) list set" and mulFP eFP invgFP \<iota>fam12 where
      hFP: "top1_is_free_product_on FP mulFP eFP invgFP
        (\<lambda>i::nat. if i = 0 then G1 else G2) (\<lambda>i. if i = 0 then mul1 else mul2) \<iota>fam12 {0,1}"
  proof -
    from Theorem_68_2_free_product_exists[OF hgroups]
    show ?thesis using that by blast
  qed
  \<comment> \<open>Step 2: Since G1, G2 are free on S1, S2, reduced words in FP correspond to
     reduced words in S1 \<union> S2. Define \<iota>S12.\<close>
  have h_free_on_union: "\<exists>\<iota>S12. top1_is_free_group_full_on FP mulFP eFP invgFP \<iota>S12 (S1 \<union> S2)
    \<and> (\<forall>s\<in>S1. \<iota>S12 s = \<iota>fam12 0 (\<iota>1 s)) \<and> (\<forall>s\<in>S2. \<iota>S12 s = \<iota>fam12 1 (\<iota>2 s))" sorry
  obtain \<iota>S12 where h\<iota>: "top1_is_free_group_full_on FP mulFP eFP invgFP \<iota>S12 (S1 \<union> S2)"
      and hcomp1: "\<forall>s\<in>S1. \<iota>S12 s = \<iota>fam12 0 (\<iota>1 s)"
      and hcomp2: "\<forall>s\<in>S2. \<iota>S12 s = \<iota>fam12 1 (\<iota>2 s)"
    using h_free_on_union by (by100 blast)
  show ?thesis using hFP h\<iota> hcomp1 hcomp2 by (by100 blast)
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
  have h_free_abel: "\<exists>\<iota>H.
      top1_is_free_abelian_group_full_on ?H ?mulH ?eH ?invgH \<iota>H S
    \<and> (\<forall>s\<in>S. \<iota>H s = ?\<phi> (\<iota> s))" sorry
  show ?thesis using h_abel h_free_abel by (by100 blast)
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

text \<open>Extraction lemma: from quotient_of_scheme_on, get the polygonal region and quotient map.\<close>
lemma quotient_of_scheme_extract:
  assumes "top1_quotient_of_scheme_on X TX scheme"
  obtains P q where "top1_is_polygonal_region_on P (length scheme)"
      and "top1_quotient_map_on P
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q"
  using assms unfolding top1_quotient_of_scheme_on_def
  apply (elim conjE exE)
  apply (rule that)
  apply assumption+
  done

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
  have hn_pos: "n > 0"
  proof (rule ccontr)
    assume "\<not> n > 0"
    hence "n = 0" by (by100 simp)
    hence "{..<n} = ({} :: nat set)" by (by100 simp)
    moreover from assms obtain C where "(\<Union>\<alpha>\<in>{..<n}. C \<alpha>) = X" and "p \<in> X"
      unfolding top1_is_wedge_of_circles_on_def
      apply (elim conjE exE) by (by100 blast)
    ultimately show False by (by100 simp)
  qed
  have hbase: "n = 0 \<longrightarrow> ?thesis" using hn_pos by (by100 simp)
  \<comment> \<open>Inductive step: decompose X = X_{n-1} \<union> C_n. Apply SvK.\<close>
  have hstep: "n > 0 \<longrightarrow> (\<exists>Xprev TXprev Cn.
      Xprev \<union> Cn = X \<and> Xprev \<inter> Cn = {p}
    \<and> top1_is_wedge_of_circles_on Xprev TXprev {..<n-1} p
    \<and> top1_groups_isomorphic_on
        (top1_fundamental_group_carrier Cn (subspace_topology X TX Cn) p)
        (top1_fundamental_group_mul Cn (subspace_topology X TX Cn) p)
        top1_Z_group top1_Z_mul)"
  proof (intro impI)
    assume hn: "n > 0"
    \<comment> \<open>Extract circles from the wedge definition.\<close>
    obtain C where hC_sub: "\<forall>\<alpha>\<in>{..<n}. C \<alpha> \<subseteq> X \<and> p \<in> C \<alpha>
             \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                      (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h)"
        and hC_cover: "(\<Union>\<alpha>\<in>{..<n}. C \<alpha>) = X"
        and hC_disjoint: "\<forall>\<alpha>\<in>{..<n}. \<forall>\<beta>\<in>{..<n}. \<alpha> \<noteq> \<beta> \<longrightarrow> C \<alpha> \<inter> C \<beta> = {p}"
        and hC_weak: "\<forall>D. D \<subseteq> X \<longrightarrow>
             (closedin_on X TX D \<longleftrightarrow>
              (\<forall>\<alpha>\<in>{..<n}. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)))"
      using assms unfolding top1_is_wedge_of_circles_on_def by blast
    \<comment> \<open>Take Xprev = \<Union>{C \<alpha> | \<alpha> < n-1} and Cn = C(n-1).\<close>
    let ?Xprev = "\<Union>\<alpha>\<in>{..<n-1}. C \<alpha>"
    let ?TXprev = "subspace_topology X TX ?Xprev"
    let ?Cn = "C (n-1)"
    show "\<exists>Xprev TXprev Cn.
      Xprev \<union> Cn = X \<and> Xprev \<inter> Cn = {p}
      \<and> top1_is_wedge_of_circles_on Xprev TXprev {..<n-1} p
      \<and> top1_groups_isomorphic_on
          (top1_fundamental_group_carrier Cn (subspace_topology X TX Cn) p)
          (top1_fundamental_group_mul Cn (subspace_topology X TX Cn) p)
          top1_Z_group top1_Z_mul" sorry
  qed
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
       (subspace_topology X TX A) ?\<iota>"
  proof -
    \<comment> \<open>Step 1: S1 \<subseteq> B2 (unit circle inside closed unit disk).\<close>
    have hS1_B2: "top1_S1 \<subseteq> top1_B2"
      unfolding top1_S1_def top1_B2_def by (by100 auto)
    \<comment> \<open>Step 2: h restricted from B2 to S1 is continuous into X.\<close>
    have h_cont_S1_sub: "top1_continuous_map_on top1_S1
        (subspace_topology top1_B2 top1_B2_topology top1_S1) X TX h"
      by (rule top1_continuous_map_on_restrict_domain_simple[OF assms(5) hS1_B2])
    \<comment> \<open>Step 3: Subspace topology transitivity:
       subspace_topology B2 B2_topology S1 = subspace_topology UNIV (prod_top) S1 = S1_topology.\<close>
    have hS1_top_eq: "subspace_topology top1_B2 top1_B2_topology top1_S1 = top1_S1_topology"
    proof -
      have "top1_S1_topology = subspace_topology UNIV
          (product_topology_on top1_open_sets top1_open_sets) top1_S1"
        unfolding top1_S1_topology_def ..
      also have "\<dots> = subspace_topology top1_B2 top1_B2_topology top1_S1"
        unfolding top1_B2_topology_def
        using subspace_topology_trans[OF hS1_B2] by (by100 simp)
      finally show ?thesis by (by100 simp)
    qed
    have h_cont_S1_X: "top1_continuous_map_on top1_S1 top1_S1_topology X TX h"
      using h_cont_S1_sub hS1_top_eq by (by100 simp)
    \<comment> \<open>Step 4: Shrink codomain from X to A (since h(S1) \<subseteq> A).\<close>
    have hA_sub_X: "A \<subseteq> X"
      using assms(3) unfolding closedin_on_def by (by100 blast)
    show ?thesis
      by (rule top1_continuous_map_on_codomain_shrink[OF h_cont_S1_X assms(8) hA_sub_X])
  qed
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
  \<comment> \<open>The 1-skeleton is a wedge of 2 circles (Step 1), π₁ of which is free on {a,b} (Step 2).
     Attaching the 2-cell kills the commutator aba⁻¹b⁻¹ (Step 3 via Theorem 72.1).
     So π₁(T) ≅ F({a,b})/⟨⟨aba⁻¹b⁻¹⟩⟩ ≅ Z×Z.\<close>
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
  \<comment> \<open>The 1-skeleton is a single circle A with \<pi>_1(A) \<cong> Z.\<close>
  \<comment> \<open>The attaching map wraps S^1 n times around the circle A.\<close>
  \<comment> \<open>By Theorem 72.1: \<pi>_1(X) \<cong> Z/\<langle>\<langle>n\<rangle>\<rangle> = Z/nZ.\<close>
  show ?thesis sorry
qed

text \<open>Path homotopy is compatible with path reversal: f \<simeq> g \<Longrightarrow> rev f \<simeq> rev g.\<close>
lemma path_homotopic_reverse_congruence:
  assumes hTX: "is_topology_on X TX"
      and hhom: "top1_path_homotopic_on X TX x0 x1 f g"
  shows "top1_path_homotopic_on X TX x1 x0 (top1_path_reverse f) (top1_path_reverse g)"
proof -
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hF0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hF1: "\<forall>s\<in>I_set. F (s, 1) = g s"
      and hFleft: "\<forall>t\<in>I_set. F (0, t) = x0" and hFright: "\<forall>t\<in>I_set. F (1, t) = x1"
    using hhom unfolding top1_path_homotopic_on_def by blast
  \<comment> \<open>G(s,t) = F(1-s, t): homotopy from rev f to rev g.\<close>
  let ?G = "\<lambda>p. F (1 - fst p, snd p)"
  have hflip_s: "top1_continuous_map_on (I_set \<times> I_set) II_topology
      (I_set \<times> I_set) II_topology (\<lambda>p. (1 - fst p, snd p))"
  proof -
    \<comment> \<open>By Theorem_18_4: \<pi>1 \<circ> flip = (1-) \<circ> \<pi>1, \<pi>2 \<circ> flip = \<pi>2.\<close>
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hTP: "is_topology_on (I_set \<times> I_set) II_topology"
      unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
    \<comment> \<open>(1-) continuous I \<rightarrow> I.\<close>
    have h1minus: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>s. 1 - s)"
      unfolding top1_unit_interval_topology_def
      by (rule top1_continuous_map_on_real_subspace_open_sets)
         (auto simp: top1_unit_interval_def intro: continuous_intros)
    have hpi1: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi1"
      unfolding II_topology_def by (rule top1_continuous_pi1[OF hTI hTI])
    have hpi2: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi2"
      unfolding II_topology_def by (rule top1_continuous_pi2[OF hTI hTI])
    have hpi1_flip: "pi1 \<circ> (\<lambda>p. (1 - fst p, snd p)) = (\<lambda>s. 1 - s) \<circ> pi1"
      unfolding pi1_def comp_def by (rule ext, simp add: case_prod_beta)
    have hpi2_flip: "pi2 \<circ> (\<lambda>p. (1 - fst p, snd p)) = pi2"
      unfolding pi2_def comp_def by (rule ext, simp add: case_prod_beta)
    have "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top (pi1 \<circ> (\<lambda>p. (1 - fst p, snd p)))"
      unfolding hpi1_flip by (rule top1_continuous_map_on_comp[OF hpi1 h1minus])
    moreover have "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top (pi2 \<circ> (\<lambda>p. (1 - fst p, snd p)))"
      unfolding hpi2_flip by (rule hpi2)
    ultimately have "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top)
        (I_set \<times> I_set) (product_topology_on I_top I_top) (\<lambda>p. (1 - fst p, snd p))"
      using iffD2[OF Theorem_18_4[OF hTP hTI hTI]] unfolding II_topology_def by (by100 blast)
    thus ?thesis unfolding II_topology_def .
  qed
  have hG: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?G"
  proof -
    have "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (F \<circ> (\<lambda>p. (1 - fst p, snd p)))"
      by (rule top1_continuous_map_on_comp[OF hflip_s hF])
    thus ?thesis unfolding comp_def by (by100 simp)
  qed
  have hfp: "top1_is_path_on X TX x0 x1 f" and hgp: "top1_is_path_on X TX x0 x1 g"
    using hhom unfolding top1_path_homotopic_on_def by blast+
  have "top1_path_homotopic_on X TX x1 x0 (top1_path_reverse f) (top1_path_reverse g)"
    unfolding top1_path_homotopic_on_def
  proof (intro exI[of _ ?G] conjI)
    show "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?G" by (rule hG)
    show "\<forall>s\<in>I_set. ?G (s, 0) = top1_path_reverse f s"
      unfolding top1_path_reverse_def using hF0
      unfolding top1_unit_interval_def by (by100 auto)
    show "\<forall>s\<in>I_set. ?G (s, 1) = top1_path_reverse g s"
      unfolding top1_path_reverse_def using hF1
      unfolding top1_unit_interval_def by (by100 auto)
    show "\<forall>t\<in>I_set. ?G (0, t) = x1"
      using hFright by (by100 simp)
    show "\<forall>t\<in>I_set. ?G (1, t) = x0"
      using hFleft by (by100 simp)
    show "top1_is_path_on X TX x1 x0 (top1_path_reverse f)"
      by (rule top1_path_reverse_is_path[OF hfp])
    show "top1_is_path_on X TX x1 x0 (top1_path_reverse g)"
      by (rule top1_path_reverse_is_path[OF hgp])
  qed
  thus ?thesis .
qed

text \<open>The fundamental group \<pi>_1(X, x_0) is a group under path-product of equivalence classes.\<close>
lemma top1_fundamental_group_is_group:
  assumes hTX: "is_topology_on X TX" and hx0: "x0 \<in> X"
  shows "top1_is_group_on
    (top1_fundamental_group_carrier X TX x0)
    (top1_fundamental_group_mul X TX x0)
    (top1_fundamental_group_id X TX x0)
    (top1_fundamental_group_invg X TX x0)"
  unfolding top1_is_group_on_def
proof (intro conjI)
  let ?G = "top1_fundamental_group_carrier X TX x0"
  let ?mul = "top1_fundamental_group_mul X TX x0"
  let ?e = "top1_fundamental_group_id X TX x0"
  let ?inv = "top1_fundamental_group_invg X TX x0"
  have hconst_loop: "top1_is_loop_on X TX x0 (top1_constant_path x0)"
    by (rule top1_constant_path_is_loop[OF hTX hx0])
  \<comment> \<open>(1) Identity in carrier.\<close>
  show "?e \<in> ?G"
    unfolding top1_fundamental_group_carrier_def top1_fundamental_group_id_def
    using hconst_loop by (by100 blast)
  \<comment> \<open>(2) Closure under mul.\<close>
  show "\<forall>x\<in>?G. \<forall>y\<in>?G. ?mul x y \<in> ?G"
  proof (intro ballI)
    fix c1 c2 assume "c1 \<in> ?G" "c2 \<in> ?G"
    then obtain f g where hf: "top1_is_loop_on X TX x0 f" and hc1: "c1 = {h. top1_loop_equiv_on X TX x0 f h}"
        and hg: "top1_is_loop_on X TX x0 g" and hc2: "c2 = {h. top1_loop_equiv_on X TX x0 g h}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hfg: "top1_is_loop_on X TX x0 (top1_path_product f g)"
      by (rule top1_path_product_is_loop[OF hTX hf hg])
    have "?mul c1 c2 = {h. top1_loop_equiv_on X TX x0 (top1_path_product f g) h}"
      unfolding hc1 hc2 by (rule top1_fundamental_group_mul_class[OF hTX hf hg])
    thus "?mul c1 c2 \<in> ?G"
      unfolding top1_fundamental_group_carrier_def using hfg by (by100 blast)
  qed
  \<comment> \<open>(3) Closure under inverse.\<close>
  show "\<forall>x\<in>?G. ?inv x \<in> ?G"
  proof (intro ballI)
    fix c assume "c \<in> ?G"
    then obtain f where hf: "top1_is_loop_on X TX x0 f"
        and hc: "c = {h. top1_loop_equiv_on X TX x0 f h}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hrf: "top1_is_loop_on X TX x0 (top1_path_reverse f)"
      by (rule top1_path_reverse_is_loop[OF hf])
    have hinvc: "?inv c = {h. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h}"
    proof (rule set_eqI, rule iffI)
      fix h assume "h \<in> ?inv c"
      then obtain g where hg_in: "g \<in> c" and hrev_g_h: "top1_loop_equiv_on X TX x0 (top1_path_reverse g) h"
        unfolding top1_fundamental_group_invg_def by (by100 blast)
      have hg_equiv: "top1_loop_equiv_on X TX x0 f g" using hg_in unfolding hc by (by100 blast)
      hence "top1_path_homotopic_on X TX x0 x0 f g" unfolding top1_loop_equiv_on_def by (by100 blast)
      hence "top1_path_homotopic_on X TX x0 x0 (top1_path_reverse f) (top1_path_reverse g)"
        by (rule path_homotopic_reverse_congruence[OF hTX])
      have hg_loop: "top1_is_loop_on X TX x0 g" using hg_equiv unfolding top1_loop_equiv_on_def by (by100 blast)
      have hrg: "top1_is_loop_on X TX x0 (top1_path_reverse g)" by (rule top1_path_reverse_is_loop[OF hg_loop])
      hence "top1_loop_equiv_on X TX x0 (top1_path_reverse f) (top1_path_reverse g)"
        unfolding top1_loop_equiv_on_def
        using hrf \<open>top1_path_homotopic_on X TX x0 x0 (top1_path_reverse f) (top1_path_reverse g)\<close>
        by (by100 blast)
      moreover have "top1_loop_equiv_on X TX x0 (top1_path_reverse g) h" by (rule hrev_g_h)
      ultimately show "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h}"
        unfolding top1_loop_equiv_on_def
        using Lemma_51_1_path_homotopic_trans[OF hTX] hrf by (by100 blast)
    next
      fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h}"
      hence "top1_loop_equiv_on X TX x0 (top1_path_reverse f) h" by (by100 blast)
      moreover have "f \<in> c" unfolding hc using top1_loop_equiv_on_refl[OF hf] by (by100 blast)
      ultimately show "h \<in> ?inv c"
        unfolding top1_fundamental_group_invg_def by (by100 blast)
    qed
    show "?inv c \<in> ?G"
      unfolding hinvc top1_fundamental_group_carrier_def using hrf by (by100 blast)
  qed
  \<comment> \<open>(4) Associativity.\<close>
  show "\<forall>x\<in>?G. \<forall>y\<in>?G. \<forall>z\<in>?G. ?mul (?mul x y) z = ?mul x (?mul y z)"
  proof (intro ballI)
    fix c1 c2 c3 assume "c1 \<in> ?G" "c2 \<in> ?G" "c3 \<in> ?G"
    then obtain f g h where hf: "top1_is_loop_on X TX x0 f" and hc1: "c1 = {k. top1_loop_equiv_on X TX x0 f k}"
        and hg: "top1_is_loop_on X TX x0 g" and hc2: "c2 = {k. top1_loop_equiv_on X TX x0 g k}"
        and hh: "top1_is_loop_on X TX x0 h" and hc3: "c3 = {k. top1_loop_equiv_on X TX x0 h k}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hfp: "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def .
    have hgp: "top1_is_path_on X TX x0 x0 g" using hg unfolding top1_is_loop_on_def .
    have hhp: "top1_is_path_on X TX x0 x0 h" using hh unfolding top1_is_loop_on_def .
    have hfg: "top1_is_loop_on X TX x0 (top1_path_product f g)"
      by (rule top1_path_product_is_loop[OF hTX hf hg])
    have hgh: "top1_is_loop_on X TX x0 (top1_path_product g h)"
      by (rule top1_path_product_is_loop[OF hTX hg hh])
    \<comment> \<open>LHS: (c1*c2)*c3 = [(f*g)*h].\<close>
    have "?mul c1 c2 = {k. top1_loop_equiv_on X TX x0 (top1_path_product f g) k}"
      unfolding hc1 hc2 by (rule top1_fundamental_group_mul_class[OF hTX hf hg])
    hence hlhs: "?mul (?mul c1 c2) c3 = {k. top1_loop_equiv_on X TX x0 (top1_path_product (top1_path_product f g) h) k}"
      unfolding hc3 by (by100 simp) (rule top1_fundamental_group_mul_class[OF hTX hfg hh])
    \<comment> \<open>RHS: c1*(c2*c3) = [f*(g*h)].\<close>
    have "?mul c2 c3 = {k. top1_loop_equiv_on X TX x0 (top1_path_product g h) k}"
      unfolding hc2 hc3 by (rule top1_fundamental_group_mul_class[OF hTX hg hh])
    hence hrhs: "?mul c1 (?mul c2 c3) = {k. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_path_product g h)) k}"
      unfolding hc1 by (by100 simp) (rule top1_fundamental_group_mul_class[OF hTX hf hgh])
    \<comment> \<open>By Theorem_51_2_associativity: (f*g)*h \<simeq> f*(g*h). Hence equiv classes equal.\<close>
    have hassoc_path: "top1_path_homotopic_on X TX x0 x0
        (top1_path_product f (top1_path_product g h)) (top1_path_product (top1_path_product f g) h)"
      by (rule Theorem_51_2_associativity[OF hTX hfp hgp hhp])
    have "{k. top1_loop_equiv_on X TX x0 (top1_path_product (top1_path_product f g) h) k}
        = {k. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_path_product g h)) k}"
    proof (rule set_eqI, rule iffI)
      fix k assume "k \<in> {k. top1_loop_equiv_on X TX x0 (top1_path_product (top1_path_product f g) h) k}"
      hence "top1_is_loop_on X TX x0 k" "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_path_product f g) h) k"
        unfolding top1_loop_equiv_on_def by (by100 blast)+
      moreover have "top1_path_homotopic_on X TX x0 x0 (top1_path_product f (top1_path_product g h)) (top1_path_product (top1_path_product f g) h)"
        by (rule hassoc_path)
      ultimately show "k \<in> {k. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_path_product g h)) k}"
        unfolding top1_loop_equiv_on_def
        using Lemma_51_1_path_homotopic_trans[OF hTX] top1_path_product_is_loop[OF hTX hf hgh] by (by100 blast)
    next
      fix k assume "k \<in> {k. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_path_product g h)) k}"
      hence "top1_is_loop_on X TX x0 k" "top1_path_homotopic_on X TX x0 x0 (top1_path_product f (top1_path_product g h)) k"
        unfolding top1_loop_equiv_on_def by (by100 blast)+
      moreover have "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_path_product f g) h) (top1_path_product f (top1_path_product g h))"
        by (rule Lemma_51_1_path_homotopic_sym[OF hassoc_path])
      ultimately show "k \<in> {k. top1_loop_equiv_on X TX x0 (top1_path_product (top1_path_product f g) h) k}"
        unfolding top1_loop_equiv_on_def
        using Lemma_51_1_path_homotopic_trans[OF hTX] top1_path_product_is_loop[OF hTX hfg hh] by (by100 blast)
    qed
    thus "?mul (?mul c1 c2) c3 = ?mul c1 (?mul c2 c3)" unfolding hlhs hrhs .
  qed
  \<comment> \<open>(5) Left identity.\<close>
  show "\<forall>x\<in>?G. ?mul ?e x = x \<and> ?mul x ?e = x"
  proof (intro ballI conjI)
    fix c assume "c \<in> ?G"
    then obtain f where hf: "top1_is_loop_on X TX x0 f"
        and hc: "c = {h. top1_loop_equiv_on X TX x0 f h}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hfp: "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def .
    \<comment> \<open>Left identity: [const]*[f] = [const*f] = [f] by Theorem_51_2_left_identity.\<close>
    have "?mul ?e c = {h. top1_loop_equiv_on X TX x0 (top1_path_product (top1_constant_path x0) f) h}"
      unfolding top1_fundamental_group_id_def hc
      by (rule top1_fundamental_group_mul_class[OF hTX hconst_loop hf])
    also have "\<dots> = {h. top1_loop_equiv_on X TX x0 f h}"
    proof (rule set_eqI, rule iffI)
      fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product (top1_constant_path x0) f) h}"
      hence "top1_loop_equiv_on X TX x0 (top1_path_product (top1_constant_path x0) f) h"
        by (by100 blast)
      hence "top1_is_loop_on X TX x0 h \<and> top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_constant_path x0) f) h"
        unfolding top1_loop_equiv_on_def by (by100 blast)
      moreover have "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_constant_path x0) f) f"
        by (rule Theorem_51_2_left_identity[OF hTX hfp])
      ultimately have "top1_is_loop_on X TX x0 h"
          "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_constant_path x0) f) h" by (by100 blast)+
      moreover have "top1_path_homotopic_on X TX x0 x0 f (top1_path_product (top1_constant_path x0) f)"
        by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_left_identity[OF hTX hfp]])
      ultimately have "top1_path_homotopic_on X TX x0 x0 f h"
        using Lemma_51_1_path_homotopic_trans[OF hTX] by (by100 blast)
      thus "h \<in> {h. top1_loop_equiv_on X TX x0 f h}"
        unfolding top1_loop_equiv_on_def using hf \<open>top1_is_loop_on X TX x0 h\<close> by (by100 blast)
    next
      fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 f h}"
      hence hloop_h: "top1_is_loop_on X TX x0 h" and hhom: "top1_path_homotopic_on X TX x0 x0 f h"
        unfolding top1_loop_equiv_on_def by (by100 blast)+
      have "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_constant_path x0) f) f"
        by (rule Theorem_51_2_left_identity[OF hTX hfp])
      hence "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_constant_path x0) f) h"
        using Lemma_51_1_path_homotopic_trans[OF hTX _ hhom] by (by100 blast)
      thus "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product (top1_constant_path x0) f) h}"
        unfolding top1_loop_equiv_on_def
        using top1_path_product_is_loop[OF hTX hconst_loop hf] hloop_h by (by100 blast)
    qed
    finally show "?mul ?e c = c" unfolding hc .
    \<comment> \<open>Right identity: [f]*[const] = [f*const] = [f] by Theorem_51_2_right_identity.\<close>
    have "?mul c ?e = {h. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_constant_path x0)) h}"
      unfolding hc top1_fundamental_group_id_def
      by (rule top1_fundamental_group_mul_class[OF hTX hf hconst_loop])
    also have "\<dots> = {h. top1_loop_equiv_on X TX x0 f h}"
    proof (rule set_eqI, rule iffI)
      fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_constant_path x0)) h}"
      hence "top1_is_loop_on X TX x0 h"
          "top1_path_homotopic_on X TX x0 x0 (top1_path_product f (top1_constant_path x0)) h"
        unfolding top1_loop_equiv_on_def by (by100 blast)+
      moreover have "top1_path_homotopic_on X TX x0 x0 f (top1_path_product f (top1_constant_path x0))"
        by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_right_identity[OF hTX hfp]])
      ultimately have "top1_path_homotopic_on X TX x0 x0 f h"
        using Lemma_51_1_path_homotopic_trans[OF hTX] by (by100 blast)
      thus "h \<in> {h. top1_loop_equiv_on X TX x0 f h}"
        unfolding top1_loop_equiv_on_def using hf \<open>top1_is_loop_on X TX x0 h\<close> by (by100 blast)
    next
      fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 f h}"
      hence hloop_h: "top1_is_loop_on X TX x0 h" and hhom: "top1_path_homotopic_on X TX x0 x0 f h"
        unfolding top1_loop_equiv_on_def by (by100 blast)+
      have "top1_path_homotopic_on X TX x0 x0 (top1_path_product f (top1_constant_path x0)) f"
        by (rule Theorem_51_2_right_identity[OF hTX hfp])
      hence "top1_path_homotopic_on X TX x0 x0 (top1_path_product f (top1_constant_path x0)) h"
        using Lemma_51_1_path_homotopic_trans[OF hTX _ hhom] by (by100 blast)
      thus "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_constant_path x0)) h}"
        unfolding top1_loop_equiv_on_def
        using top1_path_product_is_loop[OF hTX hf hconst_loop] hloop_h by (by100 blast)
    qed
    finally show "?mul c ?e = c" unfolding hc .
  qed
  \<comment> \<open>(6) Inverse.\<close>
  show "\<forall>x\<in>?G. ?mul (?inv x) x = ?e \<and> ?mul x (?inv x) = ?e"
  proof (intro ballI conjI)
    fix c assume "c \<in> ?G"
    then obtain f where hf: "top1_is_loop_on X TX x0 f"
        and hc: "c = {h. top1_loop_equiv_on X TX x0 f h}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hfp: "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def .
    have hrf: "top1_is_loop_on X TX x0 (top1_path_reverse f)"
      by (rule top1_path_reverse_is_loop[OF hf])
    have hrfp: "top1_is_path_on X TX x0 x0 (top1_path_reverse f)"
      using hrf unfolding top1_is_loop_on_def .
    \<comment> \<open>inv([f]) = {h. \<exists>g\<in>[f]. rev(g) \<simeq> h} = [rev f] (reverse respects equiv class).\<close>
    have hinvc: "?inv c = {h. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h}"
    proof (rule set_eqI, rule iffI)
      fix h assume "h \<in> ?inv c"
      then obtain g where hg_in: "g \<in> c" and hrev_g_h: "top1_loop_equiv_on X TX x0 (top1_path_reverse g) h"
        unfolding top1_fundamental_group_invg_def by (by100 blast)
      have hg_equiv: "top1_loop_equiv_on X TX x0 f g" using hg_in unfolding hc by (by100 blast)
      have hg_loop: "top1_is_loop_on X TX x0 g" using hg_equiv unfolding top1_loop_equiv_on_def by (by100 blast)
      have "top1_path_homotopic_on X TX x0 x0 f g" using hg_equiv unfolding top1_loop_equiv_on_def by (by100 blast)
      hence "top1_path_homotopic_on X TX x0 x0 (top1_path_reverse f) (top1_path_reverse g)"
        by (rule path_homotopic_reverse_congruence[OF hTX])
      moreover have "top1_path_homotopic_on X TX x0 x0 (top1_path_reverse g) h"
        using hrev_g_h unfolding top1_loop_equiv_on_def by (by100 blast)
      ultimately have "top1_path_homotopic_on X TX x0 x0 (top1_path_reverse f) h"
        using Lemma_51_1_path_homotopic_trans[OF hTX] by (by100 blast)
      thus "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h}"
        unfolding top1_loop_equiv_on_def using hrf hrev_g_h unfolding top1_loop_equiv_on_def by (by100 blast)
    next
      fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h}"
      moreover have "f \<in> c" unfolding hc using top1_loop_equiv_on_refl[OF hf] by (by100 blast)
      ultimately show "h \<in> ?inv c"
        unfolding top1_fundamental_group_invg_def by (by100 blast)
    qed
    \<comment> \<open>Left inverse: [rev f]*[f] = [rev f * f] = [const].\<close>
    have "?mul (?inv c) c = {h. top1_loop_equiv_on X TX x0 (top1_path_product (top1_path_reverse f) f) h}"
    proof -
      have "?mul {h. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h} {h. top1_loop_equiv_on X TX x0 f h}
          = {h. top1_loop_equiv_on X TX x0 (top1_path_product (top1_path_reverse f) f) h}"
        by (rule top1_fundamental_group_mul_class[OF hTX hrf hf])
      thus ?thesis using hinvc hc by (by100 simp)
    qed
    also have "\<dots> = ?e"
    proof (rule set_eqI, rule iffI)
      fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product (top1_path_reverse f) f) h}"
      hence "top1_is_loop_on X TX x0 h"
          "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_path_reverse f) f) h"
        unfolding top1_loop_equiv_on_def by (by100 blast)+
      moreover have "top1_path_homotopic_on X TX x0 x0 (top1_constant_path x0) (top1_path_product (top1_path_reverse f) f)"
        by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_invgerse_right[OF hTX hfp]])
      ultimately have "top1_path_homotopic_on X TX x0 x0 (top1_constant_path x0) h"
        using Lemma_51_1_path_homotopic_trans[OF hTX] by (by100 blast)
      thus "h \<in> ?e" unfolding top1_fundamental_group_id_def top1_loop_equiv_on_def
        using hconst_loop \<open>top1_is_loop_on X TX x0 h\<close> by (by100 blast)
    next
      fix h assume "h \<in> ?e"
      hence "top1_is_loop_on X TX x0 h" "top1_path_homotopic_on X TX x0 x0 (top1_constant_path x0) h"
        unfolding top1_fundamental_group_id_def top1_loop_equiv_on_def by (by100 blast)+
      moreover have "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_path_reverse f) f) (top1_constant_path x0)"
        by (rule Theorem_51_2_invgerse_right[OF hTX hfp])
      ultimately have "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_path_reverse f) f) h"
        using Lemma_51_1_path_homotopic_trans[OF hTX] by (by100 blast)
      thus "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product (top1_path_reverse f) f) h}"
        unfolding top1_loop_equiv_on_def
        using top1_path_product_is_loop[OF hTX hrf hf] \<open>top1_is_loop_on X TX x0 h\<close> by (by100 blast)
    qed
    finally show "?mul (?inv c) c = ?e" .
    \<comment> \<open>Right inverse: [f]*[rev f] = [f * rev f] = [const].\<close>
    have "?mul c (?inv c) = {h. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_path_reverse f)) h}"
    proof -
      have "?mul {h. top1_loop_equiv_on X TX x0 f h} {h. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h}
          = {h. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_path_reverse f)) h}"
        by (rule top1_fundamental_group_mul_class[OF hTX hf hrf])
      thus ?thesis using hinvc hc by (by100 simp)
    qed
    also have "\<dots> = ?e"
    proof (rule set_eqI, rule iffI)
      fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_path_reverse f)) h}"
      hence "top1_is_loop_on X TX x0 h"
          "top1_path_homotopic_on X TX x0 x0 (top1_path_product f (top1_path_reverse f)) h"
        unfolding top1_loop_equiv_on_def by (by100 blast)+
      moreover have "top1_path_homotopic_on X TX x0 x0 (top1_constant_path x0) (top1_path_product f (top1_path_reverse f))"
        by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_invgerse_left[OF hTX hfp]])
      ultimately have "top1_path_homotopic_on X TX x0 x0 (top1_constant_path x0) h"
        using Lemma_51_1_path_homotopic_trans[OF hTX] by (by100 blast)
      thus "h \<in> ?e" unfolding top1_fundamental_group_id_def top1_loop_equiv_on_def
        using hconst_loop \<open>top1_is_loop_on X TX x0 h\<close> by (by100 blast)
    next
      fix h assume "h \<in> ?e"
      hence "top1_is_loop_on X TX x0 h" "top1_path_homotopic_on X TX x0 x0 (top1_constant_path x0) h"
        unfolding top1_fundamental_group_id_def top1_loop_equiv_on_def by (by100 blast)+
      moreover have "top1_path_homotopic_on X TX x0 x0 (top1_path_product f (top1_path_reverse f)) (top1_constant_path x0)"
        by (rule Theorem_51_2_invgerse_left[OF hTX hfp])
      ultimately have "top1_path_homotopic_on X TX x0 x0 (top1_path_product f (top1_path_reverse f)) h"
        using Lemma_51_1_path_homotopic_trans[OF hTX] by (by100 blast)
      thus "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_path_reverse f)) h}"
        unfolding top1_loop_equiv_on_def
        using top1_path_product_is_loop[OF hTX hf hrf] \<open>top1_is_loop_on X TX x0 h\<close> by (by100 blast)
    qed
    finally show "?mul c (?inv c) = ?e" .
  qed
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
  have hTopX: "is_topology_on X TX" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hUsub: "U \<subseteq> X" using assms(2) unfolding openin_on_def by (by100 blast)
  have hVsub: "V \<subseteq> X" using assms(3) unfolding openin_on_def by (by100 blast)
  have hTopU: "is_topology_on U ?TU" by (rule subspace_topology_is_topology_on[OF hTopX hUsub])
  have hTopV: "is_topology_on V ?TV" by (rule subspace_topology_is_topology_on[OF hTopX hVsub])
  have hx0U: "x0 \<in> U" using assms(8) by (by100 blast)
  have hx0V: "x0 \<in> V" using assms(8) by (by100 blast)
  have hgrpU: "top1_is_group_on ?\<pi>U (top1_fundamental_group_mul U ?TU x0)
      (top1_fundamental_group_id U ?TU x0) (top1_fundamental_group_invg U ?TU x0)"
    by (rule top1_fundamental_group_is_group[OF hTopU hx0U])
  have hgrpV: "top1_is_group_on ?\<pi>V (top1_fundamental_group_mul V ?TV x0)
      (top1_fundamental_group_id V ?TV x0) (top1_fundamental_group_invg V ?TV x0)"
    by (rule top1_fundamental_group_is_group[OF hTopV hx0V])
  have hgroups: "\<forall>\<alpha>\<in>({0,1}::nat set). top1_is_group_on
      ((if \<alpha> = 0 then ?\<pi>U else ?\<pi>V))
      (if \<alpha> = 0 then top1_fundamental_group_mul U ?TU x0 else top1_fundamental_group_mul V ?TV x0)
      (if \<alpha> = 0 then top1_fundamental_group_id U ?TU x0 else top1_fundamental_group_id V ?TV x0)
      (if \<alpha> = 0 then top1_fundamental_group_invg U ?TU x0 else top1_fundamental_group_invg V ?TV x0)"
  proof (intro ballI)
    fix \<alpha> :: nat assume "\<alpha> \<in> {0, 1}"
    hence "\<alpha> = 0 \<or> \<alpha> = 1" by (by100 blast)
    thus "top1_is_group_on (if \<alpha> = 0 then ?\<pi>U else ?\<pi>V)
        (if \<alpha> = 0 then top1_fundamental_group_mul U ?TU x0 else top1_fundamental_group_mul V ?TV x0)
        (if \<alpha> = 0 then top1_fundamental_group_id U ?TU x0 else top1_fundamental_group_id V ?TV x0)
        (if \<alpha> = 0 then top1_fundamental_group_invg U ?TU x0 else top1_fundamental_group_invg V ?TV x0)"
    proof
      assume "\<alpha> = 0" thus ?thesis using hgrpU by (by100 simp)
    next
      assume "\<alpha> = 1" thus ?thesis using hgrpV by (by100 simp)
    qed
  qed
  obtain FP :: "(nat \<times> (real \<Rightarrow> 'a) set) list set" and mulFP eFP invgFP \<iota>fam where
      hFP: "top1_is_free_product_on FP mulFP eFP invgFP
             (\<lambda>i::nat. if i = 0 then ?\<pi>U else ?\<pi>V)
             (\<lambda>i. if i = 0 then top1_fundamental_group_mul U ?TU x0
                  else top1_fundamental_group_mul V ?TV x0)
             \<iota>fam {0, 1}"
  proof -
    from Theorem_68_2_free_product_exists[OF hgroups]
    show ?thesis using that by blast
  qed
  \<comment> \<open>Step 2: Define the natural map j: FP \<rightarrow> \<pi>_1(X) induced by the inclusions U, V \<hookrightarrow> X.\<close>
  \<comment> \<open>Step 3 (Surjectivity): By Theorem 59.1, every loop in X decomposes into loops in U or V.
     Hence j is surjective onto \<pi>_1(X).\<close>
  \<comment> \<open>Steps 3-4: The natural map j: FP \<rightarrow> \<pi>_1(X) is defined by extending the inclusion-induced
     homomorphisms. j is surjective (by Theorem 59.1 loop decomposition) and has kernel
     equal to the normal closure of {i_1(\<gamma>)*i_2(\<gamma>)^{-1} | \<gamma> \<in> \<pi>_1(U\<inter>V)}.\<close>
  let ?N = "top1_normal_subgroup_generated_on FP mulFP eFP invgFP
     { mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c))
              (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
        | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 }"
  obtain j where hj_hom: "top1_group_hom_on FP mulFP ?\<pi>X (top1_fundamental_group_mul X TX x0) j"
      and hj_surj: "j ` FP = ?\<pi>X"
      and hj_ker: "top1_group_kernel_on FP (top1_fundamental_group_id X TX x0) j = ?N"
    sorry
  \<comment> \<open>Step 5: By the first isomorphism theorem, j induces FP/N \<cong> \<pi>_1(X).\<close>
  have hFP_grp: "top1_is_group_on FP mulFP eFP invgFP"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have hN_gens_sub: "{mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c))
              (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
        | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0} \<subseteq> FP"
  proof (rule subsetI)
    fix x assume "x \<in> {mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c))
              (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
        | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0}"
    then obtain c where hc: "c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0"
        and hx: "x = mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c))
              (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))"
      by (by100 blast)
    \<comment> \<open>induced c is in \<pi>_1(U) (for 0) and \<pi>_1(V) (for 1). \<iota>_fam maps these into FP.\<close>
    let ?ind_U = "top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c"
    let ?ind_V = "top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c"
    have h0_in: "\<iota>fam 0 ?ind_U \<in> FP"
    proof -
      have "?ind_U \<in> top1_fundamental_group_carrier U ?TU x0"
      proof -
        have hUV_sub: "U \<inter> V \<subseteq> X" using hUsub hVsub by (by100 blast)
        have hTUV: "is_topology_on (U \<inter> V) ?TUV"
          by (rule subspace_topology_is_topology_on[OF hTopX hUV_sub])
        have hx0_UV: "x0 \<in> U \<inter> V" using assms(8) by (by100 blast)
        have hx0_U: "x0 \<in> U" using assms(8) by (by100 blast)
        have hincl_cont: "top1_continuous_map_on (U \<inter> V) ?TUV U ?TU (\<lambda>x. x)"
        proof -
          \<comment> \<open>id: U → U is continuous with the subspace topology.\<close>
          have hid_U: "top1_continuous_map_on U ?TU U ?TU (\<lambda>x. x)"
            using top1_continuous_map_on_id[OF hTopU] unfolding id_def by (by100 simp)
          \<comment> \<open>Restrict domain to U \<inter> V \<subseteq> U.\<close>
          have "U \<inter> V \<subseteq> U" by (by100 blast)
          have "top1_continuous_map_on (U \<inter> V) (subspace_topology U ?TU (U \<inter> V)) U ?TU (\<lambda>x. x)"
            by (rule top1_continuous_map_on_restrict_domain_simple[OF hid_U \<open>U \<inter> V \<subseteq> U\<close>])
          \<comment> \<open>Subspace transitivity: subspace_topology U ?TU (U\<inter>V) = ?TUV.\<close>
          moreover have "subspace_topology U ?TU (U \<inter> V) = ?TUV"
            using subspace_topology_trans[OF \<open>U \<inter> V \<subseteq> U\<close>] by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        have "top1_group_hom_on (top1_fundamental_group_carrier (U \<inter> V) ?TUV x0)
            (top1_fundamental_group_mul (U \<inter> V) ?TUV x0)
            (top1_fundamental_group_carrier U ?TU x0)
            (top1_fundamental_group_mul U ?TU x0)
            (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x))"
          by (rule top1_fundamental_group_induced_on_is_hom[OF hTUV hTopU hx0_UV hx0_U hincl_cont])
             (by100 simp)
        thus ?thesis using hc unfolding top1_group_hom_on_def by (by100 blast)
      qed
      moreover have "\<forall>x\<in>top1_fundamental_group_carrier U ?TU x0. \<iota>fam 0 x \<in> FP"
      proof -
        have "\<forall>\<alpha>\<in>{0::nat, 1}. \<forall>x\<in>(if \<alpha> = 0 then ?\<pi>U else ?\<pi>V). \<iota>fam \<alpha> x \<in> FP"
          using hFP unfolding top1_is_free_product_on_def by (by100 blast)
        thus ?thesis by (by100 force)
      qed
      ultimately show ?thesis by (by100 blast)
    qed
    have h1_in: "\<iota>fam 1 ?ind_V \<in> FP"
    proof -
      have "?ind_V \<in> top1_fundamental_group_carrier V ?TV x0"
      proof -
        have hUV_sub2: "U \<inter> V \<subseteq> X" using hUsub hVsub by (by100 blast)
        have hTUV2: "is_topology_on (U \<inter> V) ?TUV"
          by (rule subspace_topology_is_topology_on[OF hTopX hUV_sub2])
        have hx0_UV2: "x0 \<in> U \<inter> V" using assms(8) by (by100 blast)
        have hincl_cont_V: "top1_continuous_map_on (U \<inter> V) ?TUV V ?TV (\<lambda>x. x)"
        proof -
          have hid_V: "top1_continuous_map_on V ?TV V ?TV (\<lambda>x. x)"
            using top1_continuous_map_on_id[OF hTopV] unfolding id_def by (by100 simp)
          have "U \<inter> V \<subseteq> V" by (by100 blast)
          have "top1_continuous_map_on (U \<inter> V) (subspace_topology V ?TV (U \<inter> V)) V ?TV (\<lambda>x. x)"
            by (rule top1_continuous_map_on_restrict_domain_simple[OF hid_V \<open>U \<inter> V \<subseteq> V\<close>])
          moreover have "subspace_topology V ?TV (U \<inter> V) = ?TUV"
            using subspace_topology_trans[OF \<open>U \<inter> V \<subseteq> V\<close>] by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        have hx0_V: "x0 \<in> V" using assms(8) by (by100 blast)
        have "top1_group_hom_on (top1_fundamental_group_carrier (U \<inter> V) ?TUV x0)
            (top1_fundamental_group_mul (U \<inter> V) ?TUV x0)
            (top1_fundamental_group_carrier V ?TV x0)
            (top1_fundamental_group_mul V ?TV x0)
            (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x))"
        proof -
          have "(\<lambda>x. x) x0 = x0" by (by100 simp)
          thus ?thesis
            by (rule top1_fundamental_group_induced_on_is_hom[OF hTUV2 hTopV hx0_UV2 hx0_V hincl_cont_V])
        qed
        thus ?thesis using hc unfolding top1_group_hom_on_def by (by100 blast)
      qed
      moreover have "\<forall>x\<in>top1_fundamental_group_carrier V ?TV x0. \<iota>fam 1 x \<in> FP"
      proof -
        have "\<forall>\<alpha>\<in>{0::nat, 1}. \<forall>x\<in>(if \<alpha> = 0 then ?\<pi>U else ?\<pi>V). \<iota>fam \<alpha> x \<in> FP"
          using hFP unfolding top1_is_free_product_on_def by (by100 blast)
        thus ?thesis by (by100 force)
      qed
      ultimately show ?thesis by (by100 blast)
    qed
    have "invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)) \<in> FP"
      using hFP_grp h1_in unfolding top1_is_group_on_def by (by100 blast)
    thus "x \<in> FP"
      using hx h0_in hFP_grp unfolding top1_is_group_on_def by (by100 blast)
  qed
  have hN_normal: "top1_normal_subgroup_on FP mulFP eFP invgFP ?N"
    by (rule normal_subgroup_generated_is_normal[OF hFP_grp hN_gens_sub])
  have hx0_X: "x0 \<in> X" using assms(8) assms(4) by (by100 blast)
  have h\<pi>X_grp: "top1_is_group_on ?\<pi>X (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_id X TX x0) (top1_fundamental_group_invg X TX x0)"
    by (rule top1_fundamental_group_is_group[OF hTopX hx0_X])
  have hiso: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
      (top1_quotient_group_carrier_on FP mulFP ?N) (top1_quotient_group_mul_on mulFP)"
    by (rule first_isomorphism_theorem_forward[OF hFP_grp hN_normal h\<pi>X_grp hj_hom hj_surj hj_ker])
  \<comment> \<open>Assembly: the existential witnesses are FP, mulFP, eFP, invgFP, \<iota>fam.\<close>
  show ?thesis using hFP hiso sorry
qed

text \<open>Corollary 70.3 (Munkres): If U \<inter> V is simply connected, then
  \<pi>_1(X) \<cong> \<pi>_1(U) * \<pi>_1(V) (free product, no amalgamation).\<close>
corollary Corollary_70_3_simply_connected_intersection:
  assumes "is_topology_on_strict X TX" and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "top1_simply_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and "top1_path_connected_on U (subspace_topology X TX U)"
      and "top1_path_connected_on V (subspace_topology X TX V)"
      and "x0 \<in> U \<inter> V"
  shows "\<exists>(FP::'f set) mulFP.
           top1_groups_isomorphic_on
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0) FP mulFP
         \<and> (\<exists>eFP invgFP \<iota>fam.
              top1_is_free_product_on FP mulFP eFP invgFP
                (\<lambda>i::nat. if i = 0
                   then top1_fundamental_group_carrier U (subspace_topology X TX U) x0
                   else top1_fundamental_group_carrier V (subspace_topology X TX V) x0)
                (\<lambda>i. if i = 0
                   then top1_fundamental_group_mul U (subspace_topology X TX U) x0
                   else top1_fundamental_group_mul V (subspace_topology X TX V) x0)
                \<iota>fam {0, 1})"
  sorry

text \<open>Corollary 70.4 (Munkres): If V is simply connected, then
  \<pi>_1(X) \<cong> \<pi>_1(U) / N where N is the normal closure of the image of
  the inclusion \<pi>_1(U \<inter> V) \<hookrightarrow> \<pi>_1(U).\<close>
corollary Corollary_70_4_simply_connected_V:
  assumes "is_topology_on_strict X TX" and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and "top1_path_connected_on U (subspace_topology X TX U)"
      and "top1_simply_connected_on V (subspace_topology X TX V)"
      and "x0 \<in> U \<inter> V"
  shows "top1_groups_isomorphic_on
    (top1_fundamental_group_carrier X TX x0)
    (top1_fundamental_group_mul X TX x0)
    (top1_quotient_group_carrier_on
       (top1_fundamental_group_carrier U (subspace_topology X TX U) x0)
       (top1_fundamental_group_mul U (subspace_topology X TX U) x0)
       (top1_normal_subgroup_generated_on
          (top1_fundamental_group_carrier U (subspace_topology X TX U) x0)
          (top1_fundamental_group_mul U (subspace_topology X TX U) x0)
          (top1_fundamental_group_id U (subspace_topology X TX U) x0)
          (top1_fundamental_group_invg U (subspace_topology X TX U) x0)
          (top1_fundamental_group_induced_on
             (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0
             U (subspace_topology X TX U) x0 (\<lambda>x. x)
           ` top1_fundamental_group_carrier (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0)))
    (top1_quotient_group_mul_on
       (top1_fundamental_group_mul U (subspace_topology X TX U) x0))"
  sorry

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

text \<open>Union of two compact sets is compact.\<close>
lemma compact_Un:
  assumes "compact A" and "compact B"
  shows "compact (A \<union> B)"
proof (rule compactI)
  fix \<U> :: "'a set set"
  assume hopen: "\<forall>U\<in>\<U>. open U" and hcover: "A \<union> B \<subseteq> \<Union>\<U>"
  have hA_cov: "A \<subseteq> \<Union>\<U>" using hcover by (by100 blast)
  have hB_cov: "B \<subseteq> \<Union>\<U>" using hcover by (by100 blast)
  obtain FA where hFA: "finite FA" "FA \<subseteq> \<U>" "A \<subseteq> \<Union>FA"
  proof (rule compactE[OF assms(1) hA_cov])
    fix U assume "U \<in> \<U>" thus "open U" using hopen by (by100 blast)
  next
    fix F' assume "F' \<subseteq> \<U>" "finite F'" "A \<subseteq> \<Union>F'"
    thus thesis using that by (by100 blast)
  qed
  obtain FB where hFB: "finite FB" "FB \<subseteq> \<U>" "B \<subseteq> \<Union>FB"
  proof (rule compactE[OF assms(2) hB_cov])
    fix U assume "U \<in> \<U>" thus "open U" using hopen by (by100 blast)
  next
    fix F' assume "F' \<subseteq> \<U>" "finite F'" "B \<subseteq> \<Union>F'"
    thus thesis using that by (by100 blast)
  qed
  have "finite (FA \<union> FB)" using hFA(1) hFB(1) by (by100 blast)
  moreover have "FA \<union> FB \<subseteq> \<U>" using hFA(2) hFB(2) by (by100 blast)
  moreover have "A \<union> B \<subseteq> \<Union>(FA \<union> FB)" using hFA(3) hFB(3) by (by100 blast)
  ultimately show "\<exists>\<F>'\<subseteq>\<U>. finite \<F>' \<and> A \<union> B \<subseteq> \<Union>\<F>'" by (by100 blast)
qed

text \<open>Finite union of compact sets is compact.\<close>
lemma compact_Union:
  assumes "finite F" and "\<forall>S\<in>F. compact S"
  shows "compact (\<Union>F)"
  using assms
proof (induction F rule: finite_induct)
  case empty thus ?case by (simp add: compact_empty)
next
  case (insert S F)
  have "compact (\<Union>F)" using insert.IH insert.prems by (by100 blast)
  moreover have "compact S" using insert.prems by (by100 blast)
  ultimately have "compact (S \<union> \<Union>F)" by (rule compact_Un[rotated])
  thus "compact (\<Union>(insert S F))" by (by100 simp)
qed

text \<open>Closed subset of compact is compact.\<close>
lemma closed_subset_compact:
  assumes "compact S" and "closed C" and "C \<subseteq> S"
  shows "compact C"
proof (rule compactI)
  fix \<U> :: "'a set set"
  assume hopen: "\<forall>U\<in>\<U>. open U" and hcover: "C \<subseteq> \<Union>\<U>"
  \<comment> \<open>S - C is open (C closed). So \<U> \<union> {S - C} covers S.\<close>
  have hSC_open: "open (- C)" using assms(2) unfolding closed_def by (by100 blast)
  have hS_cov: "S \<subseteq> \<Union>(\<U> \<union> {- C})"
  proof
    fix x assume hx: "x \<in> S"
    show "x \<in> \<Union>(\<U> \<union> {- C})"
    proof (cases "x \<in> C")
      case True thus ?thesis using hcover by (by100 blast)
    next
      case False thus ?thesis by (by100 blast)
    qed
  qed
  have hopen2: "\<forall>U\<in>\<U> \<union> {- C}. open U" using hopen hSC_open by (by100 blast)
  obtain \<F> where hfin: "finite \<F>" and hsub: "\<F> \<subseteq> \<U> \<union> {- C}" and hcov: "S \<subseteq> \<Union>\<F>"
  proof (rule compactE[OF assms(1) hS_cov])
    fix U assume "U \<in> \<U> \<union> {- C}"
    thus "open U" using hopen hSC_open by (by100 blast)
  next
    fix \<F>' assume "\<F>' \<subseteq> \<U> \<union> {- C}" "finite \<F>'" "S \<subseteq> \<Union>\<F>'"
    thus thesis using that by (by100 blast)
  qed
  let ?\<F>' = "\<F> - {- C}"
  have "finite ?\<F>'" using hfin by (by100 blast)
  moreover have "?\<F>' \<subseteq> \<U>" using hsub by (by100 blast)
  moreover have "C \<subseteq> \<Union>?\<F>'"
  proof
    fix x assume hx: "x \<in> C"
    hence "x \<in> S" using assms(3) by (by100 blast)
    hence "x \<in> \<Union>\<F>" using hcov by (by100 blast)
    moreover have "x \<notin> - C" using hx by (by100 blast)
    ultimately show "x \<in> \<Union>?\<F>'" by (by100 blast)
  qed
  ultimately show "\<exists>\<F>'\<subseteq>\<U>. finite \<F>' \<and> C \<subseteq> \<Union>\<F>'" by (by100 blast)
qed

text \<open>Binary product of compact sets in R is compact in R^2.
  This is a special case of Tychonoff; proved via the tube lemma.\<close>
lemma compact_Times_general:
  assumes "compact (A :: 'a::topological_space set)" and "compact (B :: 'b::topological_space set)"
  shows "compact (A \<times> B :: ('a \<times> 'b) set)"
proof (rule compactI)
  fix \<C> :: "('a \<times> 'b) set set"
  assume h\<C>_open: "\<forall>c\<in>\<C>. open c" and h\<C>_cover: "A \<times> B \<subseteq> \<Union>\<C>"
  \<comment> \<open>For each a \<in> A, {a} \<times> B is covered by \<C>. B compact gives finite subcover F_a.
     Tube lemma: \<exists> W_a open, a \<in> W_a, W_a \<times> B \<subseteq> \<Union>F_a.
     {W_a | a \<in> A} covers A. A compact gives finite subcover.\<close>
  \<comment> \<open>Step 1: For each a \<in> A, get a finite subcover of {a} \<times> B.\<close>
  have hslice: "\<forall>a\<in>A. \<exists>F_a. finite F_a \<and> F_a \<subseteq> \<C> \<and> {a} \<times> B \<subseteq> \<Union>F_a"
  proof (intro ballI)
    fix a assume ha: "a \<in> A"
    \<comment> \<open>{a} \<times> B is the image of B under (\<lambda>b. (a, b)). This map is continuous.
       B is compact, so its image {a} \<times> B is compact.\<close>
    have hslice_compact: "compact ({a} \<times> B)"
    proof -
      have "continuous_on B (\<lambda>b. (a, b))"
        by (rule continuous_on_Pair) (simp_all add: continuous_on_const continuous_on_id)
      moreover have "{a} \<times> B = (\<lambda>b. (a, b)) ` B" by (by100 blast)
      ultimately show ?thesis using compact_continuous_image[OF _ assms(2)] by (by100 simp)
    qed
    have hslice_sub: "{a} \<times> B \<subseteq> \<Union>\<C>" using h\<C>_cover ha by (by100 blast)
    show "\<exists>F_a. finite F_a \<and> F_a \<subseteq> \<C> \<and> {a} \<times> B \<subseteq> \<Union>F_a"
    proof (rule compactE[OF hslice_compact hslice_sub])
      fix c assume "c \<in> \<C>" thus "open c" using h\<C>_open by (by100 blast)
    next
      fix F' assume "F' \<subseteq> \<C>" "finite F'" "{a} \<times> B \<subseteq> \<Union>F'"
      thus ?thesis by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 2: Tube lemma. For each a \<in> A, find open W_a with W_a \<times> B \<subseteq> \<Union>F_a.\<close>
  have htube: "\<forall>a\<in>A. \<exists>W_a F_a. open W_a \<and> a \<in> W_a \<and> finite F_a \<and> F_a \<subseteq> \<C> \<and> W_a \<times> B \<subseteq> \<Union>F_a"
  proof (intro ballI)
    fix a assume ha: "a \<in> A"
    \<comment> \<open>For each b \<in> B, pick C_b \<in> \<C> with (a,b) \<in> C_b, then open U_b, V_b with (a,b) \<in> U_b \<times> V_b \<subseteq> C_b.\<close>
    have hpick: "\<forall>b\<in>B. \<exists>Cb Ub Vb. Cb \<in> \<C> \<and> open Ub \<and> open Vb \<and> a \<in> Ub \<and> b \<in> Vb \<and> Ub \<times> Vb \<subseteq> Cb"
    proof (intro ballI)
      fix b assume hb: "b \<in> B"
      have hab: "(a, b) \<in> \<Union>\<C>" using h\<C>_cover ha hb by (by100 blast)
      then obtain Cb where hCb: "Cb \<in> \<C>" "(a, b) \<in> Cb" by (by100 blast)
      have "open Cb" using h\<C>_open hCb(1) by (by100 blast)
      from open_prod_elim[OF this hCb(2)]
      obtain Ub Vb where "open Ub" "open Vb" "(a, b) \<in> Ub \<times> Vb" "Ub \<times> Vb \<subseteq> Cb" by (by100 blast)
      thus "\<exists>Cb Ub Vb. Cb \<in> \<C> \<and> open Ub \<and> open Vb \<and> a \<in> Ub \<and> b \<in> Vb \<and> Ub \<times> Vb \<subseteq> Cb"
        using hCb(1) by (by100 blast)
    qed
    \<comment> \<open>Choice: pick Cb, Ub, Vb for each b.\<close>
    \<comment> \<open>Choice: pick Cb, Ub, Vb for each b (3x bchoice from hpick).\<close>
    obtain Cb Ub Vb where hCUV: "\<forall>b\<in>B. Cb b \<in> \<C> \<and> open (Ub b) \<and> open (Vb b)
        \<and> a \<in> Ub b \<and> b \<in> Vb b \<and> Ub b \<times> Vb b \<subseteq> Cb b"
    proof -
      have "\<exists>Cb. \<forall>b\<in>B. \<exists>Ub Vb. Cb b \<in> \<C> \<and> open Ub \<and> open Vb \<and> a \<in> Ub \<and> b \<in> Vb \<and> Ub \<times> Vb \<subseteq> Cb b"
        using hpick by (rule bchoice)
      then obtain Cb where hCb: "\<forall>b\<in>B. \<exists>Ub Vb. Cb b \<in> \<C> \<and> open Ub \<and> open Vb \<and> a \<in> Ub \<and> b \<in> Vb \<and> Ub \<times> Vb \<subseteq> Cb b"
        by blast
      have "\<exists>Ub. \<forall>b\<in>B. \<exists>Vb. Cb b \<in> \<C> \<and> open (Ub b) \<and> open Vb \<and> a \<in> Ub b \<and> b \<in> Vb \<and> Ub b \<times> Vb \<subseteq> Cb b"
        using hCb by (rule bchoice)
      then obtain Ub where hUb: "\<forall>b\<in>B. \<exists>Vb. Cb b \<in> \<C> \<and> open (Ub b) \<and> open Vb \<and> a \<in> Ub b \<and> b \<in> Vb \<and> Ub b \<times> Vb \<subseteq> Cb b"
        by blast
      have "\<exists>Vb. \<forall>b\<in>B. Cb b \<in> \<C> \<and> open (Ub b) \<and> open (Vb b) \<and> a \<in> Ub b \<and> b \<in> Vb b \<and> Ub b \<times> Vb b \<subseteq> Cb b"
        using hUb by (rule bchoice)
      then obtain Vb where "\<forall>b\<in>B. Cb b \<in> \<C> \<and> open (Ub b) \<and> open (Vb b) \<and> a \<in> Ub b \<and> b \<in> Vb b \<and> Ub b \<times> Vb b \<subseteq> Cb b"
        by blast
      thus ?thesis using that by blast
    qed
    \<comment> \<open>{Vb b | b \<in> B} covers B. B compact → finite B' with \<Union>(Vb ` B') \<supseteq> B.\<close>
    have hVb_cover: "B \<subseteq> \<Union>(Vb ` B)" using hCUV by (by100 blast)
    obtain B' where hB': "finite B'" "B' \<subseteq> B" "B \<subseteq> \<Union>(Vb ` B')"
    proof (rule compactE_image[OF assms(2)])
      fix b assume "b \<in> B" thus "open (Vb b)" using hCUV by (by100 blast)
    next
      show "B \<subseteq> \<Union>(Vb ` B)" by (rule hVb_cover)
    next
      fix B'' assume "B'' \<subseteq> B" "finite B''" "B \<subseteq> \<Union>(Vb ` B'')"
      thus thesis using that by (by100 blast)
    qed
    \<comment> \<open>W_a = \<Inter>(Ub ` B') (finite intersection of opens containing a).\<close>
    let ?W = "\<Inter>(Ub ` B')"
    have hW_open: "open ?W"
    proof -
      have "finite (Ub ` B')" using hB'(1) by (by100 blast)
      moreover have "\<forall>U\<in>Ub ` B'. open U" using hCUV hB'(2) by (by100 blast)
      ultimately show ?thesis by (rule open_Inter)
    qed
    have hW_a: "a \<in> ?W" using hCUV hB'(2) by (by100 blast)
    let ?F = "Cb ` B'"
    have hF_fin: "finite ?F" using hB'(1) by (by100 blast)
    have hF_sub: "?F \<subseteq> \<C>" using hCUV hB'(2) by (by100 blast)
    have hWB_sub: "?W \<times> B \<subseteq> \<Union>?F"
    proof
      fix p assume hp: "p \<in> ?W \<times> B"
      obtain x y where hxy: "p = (x, y)" "x \<in> ?W" "y \<in> B" using hp by (by100 blast)
      obtain b where hb: "b \<in> B'" "y \<in> Vb b" using hB'(3) hxy(3) by (by100 blast)
      have "x \<in> Ub b" using hxy(2) hb(1) by (by100 blast)
      hence "(x, y) \<in> Ub b \<times> Vb b" using hb(2) by (by100 blast)
      hence "(x, y) \<in> Cb b" using hCUV hB'(2) hb(1) by (by100 blast)
      thus "p \<in> \<Union>?F" using hxy(1) hb(1) by (by100 blast)
    qed
    show "\<exists>W_a F_a. open W_a \<and> a \<in> W_a \<and> finite F_a \<and> F_a \<subseteq> \<C> \<and> W_a \<times> B \<subseteq> \<Union>F_a"
      using hW_open hW_a hF_fin hF_sub hWB_sub by (by100 blast)
  qed
  \<comment> \<open>Step 3: {W_a | a \<in> A} covers A. A compact → finite subcover.\<close>
  \<comment> \<open>Pick W and F functions via choice.\<close>
  obtain W F where hWF: "\<forall>a\<in>A. open (W a) \<and> a \<in> W a \<and> finite (F a) \<and> F a \<subseteq> \<C> \<and> W a \<times> B \<subseteq> \<Union>(F a)"
  proof -
    from htube have "\<forall>a\<in>A. \<exists>W F. open W \<and> a \<in> W \<and> finite F \<and> F \<subseteq> \<C> \<and> W \<times> B \<subseteq> \<Union>F" .
    hence "\<exists>W. \<forall>a\<in>A. \<exists>F. open (W a) \<and> a \<in> W a \<and> finite F \<and> F \<subseteq> \<C> \<and> W a \<times> B \<subseteq> \<Union>F"
      by (rule bchoice)
    then obtain W where hW: "\<forall>a\<in>A. \<exists>F. open (W a) \<and> a \<in> W a \<and> finite F \<and> F \<subseteq> \<C> \<and> W a \<times> B \<subseteq> \<Union>F"
      by (by100 blast)
    hence "\<exists>F. \<forall>a\<in>A. open (W a) \<and> a \<in> W a \<and> finite (F a) \<and> F a \<subseteq> \<C> \<and> W a \<times> B \<subseteq> \<Union>(F a)"
      by (rule bchoice)
    then obtain F where "\<forall>a\<in>A. open (W a) \<and> a \<in> W a \<and> finite (F a) \<and> F a \<subseteq> \<C> \<and> W a \<times> B \<subseteq> \<Union>(F a)"
      by (by100 blast)
    thus ?thesis using that by (by100 blast)
  qed
  \<comment> \<open>{W a | a \<in> A} covers A.\<close>
  have "A \<subseteq> \<Union>(W ` A)"
  proof
    fix a assume "a \<in> A"
    thus "a \<in> \<Union>(W ` A)" using hWF by (by100 blast)
  qed
  \<comment> \<open>A compact → finite subcover.\<close>
  have hW_open: "\<forall>a\<in>A. open (W a)" using hWF by (by100 blast)
  have hA_cov: "A \<subseteq> \<Union>(W ` A)" using hWF by (by100 blast)
  obtain A' where hA': "finite A'" "A' \<subseteq> A" "A \<subseteq> \<Union>(W ` A')"
  proof (rule compactE_image[OF assms(1)])
    fix a assume "a \<in> A" thus "open (W a)" using hW_open by (by100 blast)
  next
    show "A \<subseteq> \<Union>(W ` A)" by (rule hA_cov)
  next
    fix A'' assume "A'' \<subseteq> A" "finite A''" "A \<subseteq> \<Union>(W ` A'')"
    thus thesis using that by (by100 blast)
  qed
  \<comment> \<open>\<Union>{F a | a \<in> A'} is a finite subcover of A \<times> B.\<close>
  let ?C' = "\<Union>(F ` A')"
  have "finite ?C'" using hA'(1) hWF hA'(2) by (by100 force)
  moreover have "?C' \<subseteq> \<C>"
  proof
    fix c assume "c \<in> ?C'"
    then obtain a where "a \<in> A'" "c \<in> F a" by (by100 blast)
    thus "c \<in> \<C>" using hWF hA'(2) by (by100 blast)
  qed
  moreover have "A \<times> B \<subseteq> \<Union>?C'"
  proof
    fix p assume hp: "p \<in> A \<times> B"
    obtain x y where hxy: "p = (x, y)" "x \<in> A" "y \<in> B" using hp by (by100 blast)
    obtain a where ha: "a \<in> A'" "x \<in> W a" using hA'(3) hxy(2) by (by100 blast)
    have "(x, y) \<in> W a \<times> B" using ha(2) hxy(3) by (by100 blast)
    hence "(x, y) \<in> \<Union>(F a)" using hWF hA'(2) ha(1) by (by100 blast)
    thus "p \<in> \<Union>?C'" using hxy(1) ha(1) by (by100 blast)
  qed
  ultimately show "\<exists>C'\<subseteq>\<C>. finite C' \<and> A \<times> B \<subseteq> \<Union>C'" by (by100 blast)
qed

text \<open>Compact for product intervals.\<close>
text \<open>Singleton set is compact.\<close>
lemma compact_singleton: "compact {x :: 'a::topological_space}"
proof (rule compactI)
  fix \<U> :: "'a set set"
  assume hopen: "\<forall>U\<in>\<U>. open U" and hcover: "{x} \<subseteq> \<Union>\<U>"
  then obtain U where "U \<in> \<U>" "x \<in> U" by (by100 blast)
  thus "\<exists>\<F>\<subseteq>\<U>. finite \<F> \<and> {x} \<subseteq> \<Union>\<F>" by (rule_tac x="{U}" in exI) (by100 blast)
qed

text \<open>Finite set is compact.\<close>
lemma compact_finite: "finite S \<Longrightarrow> compact (S :: 'a::topological_space set)"
proof (induction S rule: finite_induct)
  case empty thus ?case by (simp add: compact_empty)
next
  case (insert x S)
  have hx: "compact {x}" by (rule compact_singleton)
  have hS: "compact S" by (rule insert.IH)
  have "compact ({x} \<union> S)" by (rule compact_Un[OF hx hS])
  thus ?case by (by100 simp)
qed

lemma compact_Icc_Times:
  "compact ({a..b::real} \<times> {c..d::real})"
  by (rule compact_Times_general[OF compact_Icc compact_Icc])

text \<open>A triangle (convex hull of 3 points) in R^2 is compact.\<close>
lemma triangle_compact:
  fixes ax ay bx by' cx cy :: real
  shows "compact {(x, y). \<exists>s t::real. 0 \<le> s \<and> 0 \<le> t \<and> s + t \<le> 1
      \<and> x = (1 - s - t) * ax + s * bx + t * cx
      \<and> y = (1 - s - t) * ay + s * by' + t * cy}"
proof -
  let ?T = "{(x, y). \<exists>s t::real. 0 \<le> s \<and> 0 \<le> t \<and> s + t \<le> 1
      \<and> x = (1 - s - t) * ax + s * bx + t * cx
      \<and> y = (1 - s - t) * ay + s * by' + t * cy}"
  let ?f = "\<lambda>(s::real, t::real). ((1 - s - t) * ax + s * bx + t * cx,
                                  (1 - s - t) * ay + s * by' + t * cy)"
  let ?D = "{(s, t). (0::real) \<le> s \<and> 0 \<le> t \<and> s + t \<le> 1}"
  have hT_eq: "?T = ?f ` ?D"
  proof
    show "?T \<subseteq> ?f ` ?D"
    proof
      fix p assume "p \<in> ?T"
      then obtain x y s t where "p = (x, y)" "0 \<le> s" "0 \<le> t" "s + t \<le> 1"
          "x = (1 - s - t) * ax + s * bx + t * cx"
          "y = (1 - s - t) * ay + s * by' + t * cy" by (by100 blast)
      hence "(s, t) \<in> ?D \<and> p = ?f (s, t)" by (by100 auto)
      thus "p \<in> ?f ` ?D" by (by100 blast)
    qed
  next
    show "?f ` ?D \<subseteq> ?T" by (by100 auto)
  qed
  \<comment> \<open>?D is a closed subset of [0,1]^2, hence compact.\<close>
  have hD_sub: "?D \<subseteq> {0..1} \<times> {0..1}"
  proof
    fix p assume "p \<in> ?D"
    then obtain s t where "p = (s, t)" "0 \<le> s" "0 \<le> t" "s + t \<le> 1" by (by100 blast)
    thus "p \<in> {0..1} \<times> {0..1}" by (by100 force)
  qed
  have hD_closed: "closed ?D"
  proof -
    have h1: "closed {p :: real \<times> real. 0 \<le> fst p}"
      by (rule closed_Collect_le[of "\<lambda>p. 0" fst]) (simp_all add: continuous_on_const continuous_on_fst)
    have h2: "closed {p :: real \<times> real. 0 \<le> snd p}"
      by (rule closed_Collect_le[of "\<lambda>p. 0" snd]) (simp_all add: continuous_on_const continuous_on_snd)
    have h3: "closed {p :: real \<times> real. fst p + snd p \<le> 1}"
      by (rule closed_Collect_le[of "\<lambda>p. fst p + snd p" "\<lambda>p. 1"])
         (simp_all add: continuous_on_add continuous_on_fst continuous_on_snd continuous_on_const)
    have "?D = {p. 0 \<le> fst p} \<inter> {p. 0 \<le> snd p} \<inter> {p. fst p + snd p \<le> 1}"
      by (by100 auto)
    thus ?thesis using h1 h2 h3 by (by100 auto)
  qed
  have hD_compact: "compact ?D"
    by (rule closed_subset_compact[OF compact_Icc_Times hD_closed hD_sub])
  \<comment> \<open>?f is continuous.\<close>
  have hf_cont: "continuous_on ?D ?f"
  proof -
    let ?fx = "\<lambda>(s::real,t::real). (1 - s - t) * ax + s * bx + t * cx"
    let ?fy = "\<lambda>(s::real,t::real). (1 - s - t) * ay + s * by' + t * cy"
    have hfx: "continuous_on UNIV ?fx"
      unfolding split_def
      by (intro continuous_on_add continuous_on_mult continuous_on_id
          continuous_on_diff continuous_on_fst continuous_on_snd continuous_on_const)
    have hfy: "continuous_on UNIV ?fy"
      unfolding split_def
      by (intro continuous_on_add continuous_on_mult continuous_on_id
          continuous_on_diff continuous_on_fst continuous_on_snd continuous_on_const)
    have "continuous_on UNIV (\<lambda>p. (?fx p, ?fy p))"
      by (rule continuous_on_Pair[OF hfx hfy])
    hence "continuous_on UNIV ?f"
      unfolding split_def by (by100 simp)
    thus ?thesis by (rule continuous_on_subset) (by100 blast)
  qed
  show ?thesis unfolding hT_eq
    by (rule compact_continuous_image[OF hf_cont hD_compact])
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
    sorry
  show ?case unfolding hPn1_eq
    by (rule compact_continuous_image[OF hf_cont hdom_compact])
qed

lemma convex_hull_compact:
  fixes vx vy :: "nat \<Rightarrow> real" and n :: nat
  assumes "n \<ge> 3"
  shows "compact {(x, y). \<exists>coeffs. (\<forall>i<n. (coeffs i :: real) \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
      \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
  using convex_hull_compact_general[of n vx vy] assms by (by100 linarith)

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
  have hcompact: "top1_compact_on X TX"
  proof -
    \<comment> \<open>Extract P, q from the scheme.\<close>
    obtain P q where hP: "top1_is_polygonal_region_on P (length scheme)"
        and hq: "top1_quotient_map_on P
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q"
      by (rule quotient_of_scheme_extract[OF hsch])
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
  \<comment> \<open>The 4n-gon's 1-skeleton is a wedge of 2n circles. By Theorem 72.1,
     attaching the 2-cell gives the presentation ⟨a₁,b₁,...|[a₁,b₁]...[aₙ,bₙ]⟩.\<close>
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
  \<comment> \<open>The 2m-gon's 1-skeleton is a wedge of m circles. By Theorem 72.1,
     attaching the 2-cell gives the presentation ⟨a₁,...,aₘ | a₁²...aₘ²⟩.\<close>
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
  show ?thesis sorry
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
        using hp by (by100 blast)
    next
      assume "p \<in> {(x, y) | x y. \<exists>c. (\<forall>i<3. 0 \<le> c i) \<and> (\<Sum>i<3. c i) = 1
          \<and> x = (\<Sum>i<3. c i * ?vx i) \<and> y = (\<Sum>i<3. c i * ?vy i)}"
      then obtain c where hcge: "\<forall>i<3. (0::real) \<le> c i"
          and hcsum: "(\<Sum>i<3. c i) = 1"
          and hpx_raw: "x = (\<Sum>i<3. c i * ?vx i)" and hpy_raw: "y = (\<Sum>i<3. c i * ?vy i)"
        using hp by (by100 auto)
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
  \<comment> \<open>By Theorem 78.1, X is a quotient of finitely many triangles.\<close>
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
  \<comment> \<open>Let e1' = h(e0). Choose path γ in E' from e0' to e1'. Set c = [p'∘γ].
     Then p_*(E,e0) = p'_*(E',e1') = c · p'_*(E',e0') · c⁻¹ (basepoint change).\<close>
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
  \<comment> \<open>Conjugate subgroups ⇒ there exists e1' with p'(e1')=b0 s.t. subgroups equal
     after basepoint change. Then Theorem 79.2 gives the equivalence.\<close>
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
  \<comment> \<open>Step 2-3: Define \<Phi>: Cov(p) \<rightarrow> N(H)/H and show it's a group isomorphism.\<close>
  let ?Q = "top1_quotient_group_carrier_on
         (top1_normalizer_on
            (top1_fundamental_group_carrier B TB b0)
            (top1_fundamental_group_mul B TB b0)
            (top1_fundamental_group_invg B TB b0) ?H)
         (top1_fundamental_group_mul B TB b0) ?H"
  let ?mulQ = "top1_quotient_group_mul_on (top1_fundamental_group_mul B TB b0)"
  have h_iso: "top1_groups_isomorphic_on ?Cov (\<lambda>h k e. h (k e)) ?Q ?mulQ" sorry
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
     All steps (topology, covering, connectivity, subgroup matching) are sorry'd together.
     The full proof requires constructing the coset space E, defining basis topology,
     proving evenly-covered property (using semilocal simple connectivity),
     and matching p_*(\<pi>_1(E,e0)) = H.\<close>
  show ?thesis sorry
qed

section \<open>Chapter 14: Applications to Group Theory\<close>

section \<open>\<S>83 Covering Spaces of a Graph\<close>

text \<open>An arc is a space homeomorphic to the closed unit interval [0, 1].\<close>

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
  \<comment> \<open>Lift arcs from B to E (sheets over arcs are arcs), inherit Hausdorff + weak topology.\<close>
  show ?thesis sorry
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
  \<comment> \<open>Choose maximal tree T, collapse to wedge of circles X/T, which has
     free π₁ by Theorem 71.3. Homotopy equivalence gives π₁(X) ≅ π₁(X/T).\<close>
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
  \<comment> \<open>Step 2: Euler characteristic computation gives rank kn+1.\<close>
  \<comment> \<open>Step 3: H \<cong> \<pi>_1(E) is free on kn+1 generators.\<close>
  show ?thesis sorry
qed

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 


















































































































































































































































































end



























































































































































































































































































 
  
   
    



  



