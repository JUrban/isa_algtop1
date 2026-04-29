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
      ultimately show ?thesis unfolding h_inv_def by (by100 simp)
    qed
    \<comment> \<open>Key: (1 + |h_inv y|) * (1 - |y|) = 1.\<close>
    have key: "(1 + \<bar>h_inv y\<bar>) * (1 - \<bar>y\<bar>) = 1"
    proof -
      have hd: "\<bar>y\<bar> / (1 - \<bar>y\<bar>) * (1 - \<bar>y\<bar>) = \<bar>y\<bar>"
        using hne by (by100 simp)
      have "(1 + \<bar>y\<bar> / (1 - \<bar>y\<bar>)) * (1 - \<bar>y\<bar>)
          = 1 * (1 - \<bar>y\<bar>) + \<bar>y\<bar> / (1 - \<bar>y\<bar>) * (1 - \<bar>y\<bar>)"
        using distrib_right[of 1 "\<bar>y\<bar> / (1 - \<bar>y\<bar>)" "1 - \<bar>y\<bar>"] by (by100 simp)
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
        ultimately show ?thesis by (by100 linarith)
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
      then obtain W where hW: "open W" and hfW: "W \<inter> ?OI = h_inv -` V \<inter> ?OI" by (by100 blast)
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

section \<open>*\<S>62 Invariance of Domain\<close>

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
  have hR2_claim: "\<exists>C0. C0 \<in> top1_components_on (UNIV - ?K) (subspace_topology UNIV ?TR2 (UNIV - ?K))
         \<and> ?origin \<in> C0
         \<and> (\<forall>R > 0. \<exists>x \<in> C0. (fst x)^2 + (snd x)^2 > R^2)"
    sorry \<comment> \<open>By contradiction: suppose ?origin in component C0 contained in some ball.
       Apply Lemma 62.1 to C0\<union>K, paste with id, large ball, retraction contradiction.
       Uses: K compact/closed, j nulhomotopic, Y open, Theorem_55_2_no_retraction.
       This is the core ~200 lines of the Borsuk lemma.\<close>
  \<comment> \<open>Transfer back to S^2 via h^{-1}.\<close>
  show ?thesis
    sorry \<comment> \<open>Transfer: unbounded component of R^2-K maps to component of S^2-f(A) containing both a and b.\<close>
qed

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
          sorry \<comment> \<open>f(intB) in one component. If in W2, then by Borsuk, W2 = f(intB),
             but W2 unbounded and f(B) bounded (compact image). Contradiction.
             Key: needs Borsuk Lemma or bounded/unbounded argument.\<close>
      qed
      ultimately show "f x \<in> W1" by (by100 blast)
    qed
    \<comment> \<open>The component containing f(intB) is open and contained in f(U).\<close>
    have hW1_sub: "W1 \<subseteq> f ` (B - frontier B)"
      sorry \<comment> \<open>Uses Borsuk: if a \<in> W1-f(intB), take b \<in> W2, then {a,b} separated by f(B)
         in S^2. But f(B) contractible (B convex), so it doesn't separate. Contradiction.\<close>
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
              sorry \<comment> \<open>Unfold prepend at z = (\<alpha>,k)#rest: compute (g\<cdot>h)\<cdot>k = g, check g \<noteq> eGG.\<close>
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
    sorry \<comment> \<open>Every reduced word is a product of singleton inclusions.\<close>
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
        sorry \<comment> \<open>By induction on n from the right: each mul singleton onto accumulator
           just prepends (consecutive indices differ). Result = the word list.\<close>
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



























































































































































































































































































 
  
   
    



  

