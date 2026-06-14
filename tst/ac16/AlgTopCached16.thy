theory AlgTopCached16
  imports "AlgTopCached15.AlgTopCached15"
begin
lemma homeomorphism_id:
  assumes "is_topology_on X TX"
  shows "top1_homeomorphism_on X TX X TX id"
proof -
  have hid_cont: "top1_continuous_map_on X TX X TX id"
    by (rule top1_continuous_map_on_id[OF assms])
  have hinv: "\<forall>x\<in>X. inv_into X id x = x"
  proof
    fix x assume "x \<in> X"
    have "inv_into X id (id x) = x" by (rule inv_into_f_f[OF inj_on_id \<open>x \<in> X\<close>])
    thus "inv_into X id x = x" by simp
  qed
  have "top1_continuous_map_on X TX X TX (inv_into X id)"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI allI impI)
    fix x assume "x \<in> X" thus "inv_into X id x \<in> X" using hinv by (by100 simp)
  next
    fix V assume hV: "V \<in> TX"
    have "{x \<in> X. inv_into X id x \<in> V} = {x \<in> X. id x \<in> V}"
      using hinv by (by100 auto)
    thus "{x \<in> X. inv_into X id x \<in> V} \<in> TX"
      using hid_cont hV unfolding top1_continuous_map_on_def by (by100 simp)
  qed
  thus ?thesis unfolding top1_homeomorphism_on_def using assms hid_cont by (by100 simp)
qed

\<comment> \<open>Flat intro for homeomorphic realization.\<close>
lemma homeo_realization_flat_introI:
  fixes X :: "'a set" and TX :: "'a set set" and Y :: "'a set" and TY :: "'a set set" and h :: "'a \<Rightarrow> 'a"
  assumes hq: "top1_quotient_of_scheme_on Y TY t"
      and hh: "top1_homeomorphism_on X TX Y TY h"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h' :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' t \<and>
    top1_homeomorphism_on X TX Y' TY' h'"
proof -
  have H0: "top1_quotient_of_scheme_on Y TY t \<and>
     top1_homeomorphism_on X TX Y TY h"
    using hq hh by (by100 blast)
  have H1: "\<exists>h'. top1_quotient_of_scheme_on Y TY t \<and>
        top1_homeomorphism_on X TX Y TY h'"
  proof (rule exI[where x = h])
    show "top1_quotient_of_scheme_on Y TY t \<and>
          top1_homeomorphism_on X TX Y TY h"
      using H0 .
  qed
  have H2: "\<exists>TY' h'. top1_quotient_of_scheme_on Y TY' t \<and>
            top1_homeomorphism_on X TX Y TY' h'"
  proof (rule exI[where x = TY])
    show "\<exists>h'. top1_quotient_of_scheme_on Y TY t \<and>
            top1_homeomorphism_on X TX Y TY h'"
      using H1 .
  qed
  show ?thesis
  proof (rule exI[where x = Y])
    show "\<exists>TY' h'. top1_quotient_of_scheme_on Y TY' t \<and>
                top1_homeomorphism_on X TX Y TY' h'"
      using H2 .
  qed
qed

lemma same_space_implies_homeo_realization:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "top1_quotient_of_scheme_on X TX t"
  shows "\<exists>(Y :: 'a set) (TY :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y TY t \<and>
    top1_homeomorphism_on X TX Y TY h"
proof -
  have "is_topology_on X TX"
    using assms unfolding top1_quotient_of_scheme_on_def is_topology_on_strict_def by (by100 blast)
  show ?thesis by (rule homeo_realization_flat_introI[OF assms homeomorphism_id[OF \<open>is_topology_on X TX\<close>]])
qed

\<comment> \<open>scheme\\_equiv\\_implies\\_homeo\\_realization: DELETED (old bridge, unused).\<close>


\<comment> \<open>=== Lemmas moved before valid\_op to break circular dependency potential ==\<close>

\<comment> \<open>A polygonal region is compact (continuous image of a compact simplex).\<close>
lemma polygonal_region_compact:
  assumes "top1_is_polygonal_region_on P n"
  shows "compact P"
proof -
  from assms obtain vx vy where hn: "n \<ge> 3"
      and hP: "P = {(x, y). \<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
                  \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
    unfolding top1_is_polygonal_region_on_def by (by5000 auto)
  \<comment> \<open>P is bounded: all coordinates are convex combinations of finitely many vertex coordinates.\<close>
  define M where "M = Max ((\<lambda>i. \<bar>vx i\<bar>) ` {..<n} \<union> (\<lambda>i. \<bar>vy i\<bar>) ` {..<n})"
  have hfin: "finite ((\<lambda>i. \<bar>vx i\<bar>) ` {..<n} \<union> (\<lambda>i. \<bar>vy i\<bar>) ` {..<n})"
    by simp
  have hne: "(\<lambda>i. \<bar>vx i\<bar>) ` {..<n} \<union> (\<lambda>i. \<bar>vy i\<bar>) ` {..<n} \<noteq> {}"
  proof -
    have "(0::nat) < n" using hn by simp
    hence "\<bar>vx 0\<bar> \<in> (\<lambda>i. \<bar>vx i\<bar>) ` {..<n}" by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  have hM_bound: "\<And>i. i < n \<Longrightarrow> \<bar>vx i\<bar> \<le> M \<and> \<bar>vy i\<bar> \<le> M"
  proof -
    fix i assume "i < n"
    have "\<bar>vx i\<bar> \<in> (\<lambda>i. \<bar>vx i\<bar>) ` {..<n}" using \<open>i < n\<close> by (by100 blast)
    hence "\<bar>vx i\<bar> \<le> M" unfolding M_def using hfin hne by (by100 auto)
    moreover have "\<bar>vy i\<bar> \<in> (\<lambda>i. \<bar>vy i\<bar>) ` {..<n}" using \<open>i < n\<close> by (by100 blast)
    hence "\<bar>vy i\<bar> \<le> M" unfolding M_def using hfin hne by (by100 auto)
    ultimately show "\<bar>vx i\<bar> \<le> M \<and> \<bar>vy i\<bar> \<le> M" by simp
  qed
  have hP_bounded: "P \<subseteq> {- M .. M} \<times> {- M .. M}"
  proof
    fix p assume "p \<in> P"
    then obtain x y coeffs where hp: "p = (x, y)"
        and hcoeffs: "\<forall>i<n. (0::real) \<le> coeffs i" "(\<Sum>i<n. coeffs i) = 1"
        and hx: "x = (\<Sum>i<n. coeffs i * vx i)" and hy: "y = (\<Sum>i<n. coeffs i * vy i)"
      unfolding hP by (by5000 auto)
    \<comment> \<open>|x| \\<le> \\<Sum> coeffs i * M = M. Similarly for y.\<close>
    have "\<bar>x\<bar> \<le> M"
    proof -
      have "\<bar>x\<bar> \<le> (\<Sum>i<n. \<bar>coeffs i * vx i\<bar>)" unfolding hx
        by (rule sum_abs)
      also have "\<dots> \<le> (\<Sum>i<n. coeffs i * M)"
      proof (rule sum_mono)
        fix i assume "i \<in> {..<n}" hence "i < n" by simp
        have "\<bar>coeffs i * vx i\<bar> = coeffs i * \<bar>vx i\<bar>"
          using hcoeffs(1) \<open>i < n\<close> by (simp add: abs_mult)
        also have "\<dots> \<le> coeffs i * M" using hM_bound[OF \<open>i < n\<close>] hcoeffs(1) \<open>i < n\<close>
          by (intro mult_left_mono) (by100 auto)+
        finally show "\<bar>coeffs i * vx i\<bar> \<le> coeffs i * M" .
      qed
      also have "\<dots> = M" using hcoeffs(2) by (simp add: sum_distrib_right[symmetric])
      finally show ?thesis .
    qed
    have "\<bar>y\<bar> \<le> M"
    proof -
      have "\<bar>y\<bar> \<le> (\<Sum>i<n. \<bar>coeffs i * vy i\<bar>)" unfolding hy
        by (rule sum_abs)
      also have "\<dots> \<le> (\<Sum>i<n. coeffs i * M)"
      proof (rule sum_mono)
        fix i assume "i \<in> {..<n}" hence "i < n" by simp
        have "\<bar>coeffs i * vy i\<bar> = coeffs i * \<bar>vy i\<bar>"
          using hcoeffs(1) \<open>i < n\<close> by (simp add: abs_mult)
        also have "\<dots> \<le> coeffs i * M" using hM_bound[OF \<open>i < n\<close>] hcoeffs(1) \<open>i < n\<close>
          by (intro mult_left_mono) (by100 auto)+
        finally show "\<bar>coeffs i * vy i\<bar> \<le> coeffs i * M" .
      qed
      also have "\<dots> = M" using hcoeffs(2) by (simp add: sum_distrib_right[symmetric])
      finally show ?thesis .
    qed
    show "p \<in> {- M..M} \<times> {- M..M}" using \<open>\<bar>x\<bar> \<le> M\<close> \<open>\<bar>y\<bar> \<le> M\<close> hp by (by100 auto)
  qed
  \<comment> \<open>P is closed: the set of convex combinations of finitely many fixed points is closed.
     (Limit of convergent sequence of convex combinations is a convex combination.)\<close>
  \<comment> \<open>Show P is compact directly via inductive convex hull argument.\<close>
  have hP_compact_direct: "compact P"
  proof -
    \<comment> \<open>Define partial convex hulls: Q k = conv({(vx i, vy i) | i \\<le> k}).\<close>
    define Q where "Q k = {(x::real, y::real). \<exists>coeffs.
        (\<forall>i\<le>k. 0 \<le> coeffs i) \<and> (\<Sum>i\<le>k. coeffs i) = 1
        \<and> x = (\<Sum>i\<le>k. coeffs i * vx i) \<and> y = (\<Sum>i\<le>k. coeffs i * vy i)}" for k
    \<comment> \<open>Base: Q 0 = {(vx 0, vy 0)} is compact (singleton).\<close>
    have hQ0_eq: "Q 0 = {(vx 0, vy 0)}"
    proof
      show "Q 0 \<subseteq> {(vx 0, vy 0)}"
        unfolding Q_def by (by5000 force)
      show "{(vx 0, vy 0)} \<subseteq> Q 0"
        unfolding Q_def
      proof
        fix p assume "p \<in> {(vx 0, vy 0)}"
        hence "p = (vx 0, vy 0)" by simp
        define coeffs :: "nat \<Rightarrow> real" where "coeffs = (\<lambda>_. 1)"
        have "(\<forall>i\<le>(0::nat). (0::real) \<le> coeffs i) \<and> (\<Sum>i\<le>0. coeffs i) = 1
            \<and> vx 0 = (\<Sum>i\<le>0. coeffs i * vx i) \<and> vy 0 = (\<Sum>i\<le>0. coeffs i * vy i)"
          unfolding coeffs_def by simp
        thus "p \<in> {(x, y). \<exists>coeffs. (\<forall>i\<le>0. 0 \<le> coeffs i) \<and> (\<Sum>i\<le>0. coeffs i) = 1
            \<and> x = (\<Sum>i\<le>0. coeffs i * vx i) \<and> y = (\<Sum>i\<le>0. coeffs i * vy i)}"
          unfolding \<open>p = (vx 0, vy 0)\<close> by (by100 blast)
      qed
    qed
    have hQ0: "compact (Q 0)"
      unfolding hQ0_eq
    proof (rule compactI)
      fix C :: "(real \<times> real) set set"
      assume "\<forall>c\<in>C. open c" and "{(vx 0, vy 0)} \<subseteq> \<Union>C"
      then obtain U where "U \<in> C" "(vx 0, vy 0) \<in> U" by (by100 blast)
      thus "\<exists>D\<subseteq>C. finite D \<and> {(vx 0, vy 0)} \<subseteq> \<Union>D"
        by (intro exI[of _ "{U}"]) (by100 auto)
    qed
    \<comment> \<open>Step: Q (Suc k) = {t*v\\_{k+1} + (1-t)*p | t \\<in> [0,1], p \\<in> Q k}.
       This is the continuous image of [0,1] \\<times> Q k, hence compact.\<close>
    have hQstep: "\<And>k. compact (Q k) \<Longrightarrow> compact (Q (Suc k))"
    proof -
      fix k assume hIH: "compact (Q k)"
      \<comment> \<open>Q(Suc k) = image of [0,1] \\<times> Q(k) under the affine combination map.\<close>
      define f where "f = (\<lambda>(t::real, p::real\<times>real). (t * vx (Suc k) + (1-t) * fst p, t * vy (Suc k) + (1-t) * snd p))"
      have hQ_eq: "Q (Suc k) = f ` ({0..1} \<times> Q k)"
      proof
        \<comment> \<open>(\\<subseteq>): every convex combo of k+2 points = t*v\\_{k+1} + (1-t)*(combo of first k+1).\<close>
        show "Q (Suc k) \<subseteq> f ` ({0..1} \<times> Q k)"
        proof
          fix q assume "q \<in> Q (Suc k)"
          then obtain coeffs where hc: "(\<forall>i\<le>Suc k. 0 \<le> coeffs i)" "(\<Sum>i\<le>Suc k. coeffs i) = 1"
              "fst q = (\<Sum>i\<le>Suc k. coeffs i * vx i)" "snd q = (\<Sum>i\<le>Suc k. coeffs i * vy i)"
            unfolding Q_def by (by5000 auto)
          define t where "t = coeffs (Suc k)"
          have ht: "t \<in> {0..1}"
          proof -
            have "0 \<le> t" using hc(1) unfolding t_def by simp
            moreover have "t \<le> 1"
            proof -
              have "(\<Sum>i\<le>k. coeffs i) \<ge> 0"
                using hc(1) by (intro sum_nonneg) (by100 auto)
              hence "t = 1 - (\<Sum>i\<le>k. coeffs i)" using hc(2) unfolding t_def by simp
              thus ?thesis using \<open>(\<Sum>i\<le>k. coeffs i) \<ge> 0\<close> by linarith
            qed
            ultimately show ?thesis by simp
          qed
          show "q \<in> f ` ({0..1} \<times> Q k)"
          proof (cases "t = 1")
            case True
            \<comment> \<open>If t=1: q = v\\_{k+1}. f(1,p) = v\\_{k+1} for any p. Need Q k nonempty.\<close>
            have "fst q = vx (Suc k) \<and> snd q = vy (Suc k)"
            proof -
              have hzero: "\<forall>i\<le>k. coeffs i = 0"
              proof (rule ccontr)
                assume "\<not> (\<forall>i\<le>k. coeffs i = 0)"
                then obtain j where "j \<le> k" "coeffs j \<noteq> 0" by (by100 blast)
                have "0 \<le> coeffs j" using hc(1) \<open>j \<le> k\<close> by simp
                hence "coeffs j > 0" using \<open>coeffs j \<noteq> 0\<close> by linarith
                hence "(\<Sum>i\<le>k. coeffs i) > 0"
                  using hc(1) \<open>j \<le> k\<close> by (intro sum_pos2[of "{..k}" j]) (by100 auto)+
                hence "1 - t > 0" using hc(2) unfolding t_def by simp
                thus False using True by simp
              qed
              hence "(\<Sum>i\<le>k. coeffs i * vx i) = 0" "(\<Sum>i\<le>k. coeffs i * vy i) = 0"
                by (simp_all add: sum.neutral)
              thus ?thesis using hc(3,4) True unfolding t_def by simp
            qed
            \<comment> \<open>Q k is nonempty: (vx 0, vy 0) \\<in> Q 0 \\<subseteq> Q k.\<close>
            have "(vx 0, vy 0) \<in> Q k"
            proof -
              define c0 :: "nat \<Rightarrow> real" where "c0 i = (if i = 0 then 1 else 0)" for i
              have "(\<forall>i\<le>k. 0 \<le> c0 i)" unfolding c0_def by simp
              moreover have "(\<Sum>i\<le>k. c0 i) = 1" unfolding c0_def by simp
              moreover have "vx 0 = (\<Sum>i\<le>k. c0 i * vx i)"
              proof -
                have "(\<Sum>i\<le>k. c0 i * vx i) = c0 0 * vx 0 + (\<Sum>i\<in>{..k}-{0}. c0 i * vx i)"
                  by (rule sum.remove) simp_all
                also have "(\<Sum>i\<in>{..k}-{0}. c0 i * vx i) = 0"
                  by (rule sum.neutral) (simp add: c0_def)
                finally show ?thesis unfolding c0_def by simp
              qed
              moreover have "vy 0 = (\<Sum>i\<le>k. c0 i * vy i)"
              proof -
                have "(\<Sum>i\<le>k. c0 i * vy i) = c0 0 * vy 0 + (\<Sum>i\<in>{..k}-{0}. c0 i * vy i)"
                  by (rule sum.remove) simp_all
                also have "(\<Sum>i\<in>{..k}-{0}. c0 i * vy i) = 0"
                  by (rule sum.neutral) (simp add: c0_def)
                finally show ?thesis unfolding c0_def by simp
              qed
              ultimately show ?thesis unfolding Q_def by (by100 auto)
            qed
            hence "(1::real, (vx 0, vy 0)) \<in> {0..1} \<times> Q k" by simp
            hence "f (1, (vx 0, vy 0)) \<in> f ` ({0..1} \<times> Q k)" by (by100 blast)
            moreover have "f (1, (vx 0, vy 0)) = (vx (Suc k), vy (Suc k))"
              unfolding f_def by simp
            ultimately have "(vx (Suc k), vy (Suc k)) \<in> f ` ({0..1} \<times> Q k)" by simp
            thus ?thesis using \<open>fst q = vx (Suc k) \<and> snd q = vy (Suc k)\<close>
              by (cases q) (by100 auto)
          next
            case False
            \<comment> \<open>t < 1: define \\<alpha> i = coeffs i / (1-t) for i \\<le> k.\<close>
            have ht_lt: "t < 1" using ht False by simp
            hence h1mt: "1 - t > 0" by simp
            define \<alpha> where "\<alpha> i = coeffs i / (1 - t)" for i
            have h\<alpha>_pos: "\<forall>i\<le>k. 0 \<le> \<alpha> i"
              using hc(1) h1mt unfolding \<alpha>_def by (by100 auto)
            have h\<alpha>_sum: "(\<Sum>i\<le>k. \<alpha> i) = 1"
            proof -
              have "(\<Sum>i\<le>k. \<alpha> i) = (\<Sum>i\<le>k. coeffs i) / (1-t)"
                unfolding \<alpha>_def by (simp add: sum_divide_distrib)
              also have "(\<Sum>i\<le>k. coeffs i) = 1 - t"
                using hc(2) unfolding t_def by simp
              finally show ?thesis using h1mt by simp
            qed
            define p where "p = ((\<Sum>i\<le>k. \<alpha> i * vx i), (\<Sum>i\<le>k. \<alpha> i * vy i))"
            have hp: "p \<in> Q k" unfolding Q_def p_def
              using h\<alpha>_pos h\<alpha>_sum by (by100 auto)
            have "q = f (t, p)"
            proof -
              \<comment> \<open>fst q = t*vx(k+1) + (1-t) * Σα_i*vx_i\<close>
              have hx: "fst q = t * vx (Suc k) + (1-t) * (\<Sum>i\<le>k. \<alpha> i * vx i)"
              proof -
                have "fst q = (\<Sum>i\<le>Suc k. coeffs i * vx i)" using hc(3) by simp
                also have "\<dots> = (\<Sum>i\<le>k. coeffs i * vx i) + coeffs (Suc k) * vx (Suc k)" by simp
                also have "(\<Sum>i\<le>k. coeffs i * vx i) = (1-t) * (\<Sum>i\<le>k. \<alpha> i * vx i)"
                  unfolding \<alpha>_def using h1mt
                  by (simp add: sum_distrib_left sum_divide_distrib)
                finally show ?thesis unfolding t_def by (simp add: algebra_simps)
              qed
              have hy: "snd q = t * vy (Suc k) + (1-t) * (\<Sum>i\<le>k. \<alpha> i * vy i)"
              proof -
                have "snd q = (\<Sum>i\<le>Suc k. coeffs i * vy i)" using hc(4) by simp
                also have "\<dots> = (\<Sum>i\<le>k. coeffs i * vy i) + coeffs (Suc k) * vy (Suc k)" by simp
                also have "(\<Sum>i\<le>k. coeffs i * vy i) = (1-t) * (\<Sum>i\<le>k. \<alpha> i * vy i)"
                  unfolding \<alpha>_def using h1mt
                  by (simp add: sum_distrib_left sum_divide_distrib)
                finally show ?thesis unfolding t_def by (simp add: algebra_simps)
              qed
              show ?thesis unfolding f_def p_def using hx hy by (cases q) simp
            qed
            thus ?thesis using ht hp by (by100 blast)
          qed
        qed
        \<comment> \<open>(\\<supseteq>): t*v\\_{k+1} + (1-t)*p where p \\<in> Q k is a convex combo of k+2 points.\<close>
        show "f ` ({0..1} \<times> Q k) \<subseteq> Q (Suc k)"
        proof
          fix q assume "q \<in> f ` ({0..1} \<times> Q k)"
          then obtain t p where ht: "t \<in> {0..1}" and hp: "p \<in> Q k" and hq: "q = f (t, p)"
            by (by100 blast)
          from hp obtain coeffs where hc: "(\<forall>i\<le>k. 0 \<le> coeffs i)" "(\<Sum>i\<le>k. coeffs i) = 1"
              "fst p = (\<Sum>i\<le>k. coeffs i * vx i)" "snd p = (\<Sum>i\<le>k. coeffs i * vy i)"
            unfolding Q_def by (by5000 auto)
          \<comment> \<open>New coefficients: \\<beta> i = (1-t)*coeffs i for i \\<le> k, \\<beta> (k+1) = t.\<close>
          define \<beta> where "\<beta> i = (if i = Suc k then t else (1-t) * coeffs i)" for i
          have h\<beta>_pos: "\<forall>i\<le>Suc k. 0 \<le> \<beta> i"
            using hc(1) ht unfolding \<beta>_def by (by100 auto)
          have h\<beta>_sum: "(\<Sum>i\<le>Suc k. \<beta> i) = 1"
          proof -
            have "(\<Sum>i\<le>Suc k. \<beta> i) = (\<Sum>i\<le>k. \<beta> i) + \<beta> (Suc k)" by simp
            also have "(\<Sum>i\<le>k. \<beta> i) = (\<Sum>i\<le>k. (1-t) * coeffs i)"
              by (rule sum.cong) (simp_all add: \<beta>_def)
            also have "\<dots> = (1-t) * (\<Sum>i\<le>k. coeffs i)"
              by (simp add: sum_distrib_left)
            also have "\<dots> = (1-t)" using hc(2) by simp
            also have "\<beta> (Suc k) = t" unfolding \<beta>_def by simp
            finally show ?thesis by simp
          qed
          have hx: "fst q = (\<Sum>i\<le>Suc k. \<beta> i * vx i)"
          proof -
            have "fst q = t * vx (Suc k) + (1-t) * fst p" using hq unfolding f_def by simp
            also have "\<dots> = t * vx (Suc k) + (1-t) * (\<Sum>i\<le>k. coeffs i * vx i)"
              using hc(3) by simp
            also have "(1-t) * (\<Sum>i\<le>k. coeffs i * vx i) = (\<Sum>i\<le>k. (1-t) * coeffs i * vx i)"
              by (simp add: sum_distrib_left mult.assoc)
            also have "(\<Sum>i\<le>k. (1-t) * coeffs i * vx i) = (\<Sum>i\<le>k. \<beta> i * vx i)"
              by (rule sum.cong) (simp_all add: \<beta>_def)
            finally have "fst q = \<beta> (Suc k) * vx (Suc k) + (\<Sum>i\<le>k. \<beta> i * vx i)"
              unfolding \<beta>_def by simp
            thus ?thesis by simp
          qed
          have hy: "snd q = (\<Sum>i\<le>Suc k. \<beta> i * vy i)"
          proof -
            have "snd q = t * vy (Suc k) + (1-t) * snd p" using hq unfolding f_def by simp
            also have "\<dots> = t * vy (Suc k) + (1-t) * (\<Sum>i\<le>k. coeffs i * vy i)"
              using hc(4) by simp
            also have "(1-t) * (\<Sum>i\<le>k. coeffs i * vy i) = (\<Sum>i\<le>k. (1-t) * coeffs i * vy i)"
              by (simp add: sum_distrib_left mult.assoc)
            also have "(\<Sum>i\<le>k. (1-t) * coeffs i * vy i) = (\<Sum>i\<le>k. \<beta> i * vy i)"
              by (rule sum.cong) (simp_all add: \<beta>_def)
            finally have "snd q = \<beta> (Suc k) * vy (Suc k) + (\<Sum>i\<le>k. \<beta> i * vy i)"
              unfolding \<beta>_def by simp
            thus ?thesis by simp
          qed
          show "q \<in> Q (Suc k)"
          proof -
            have "\<exists>coeffs. (\<forall>i\<le>Suc k. 0 \<le> coeffs i) \<and> (\<Sum>i\<le>Suc k. coeffs i) = 1
                \<and> fst q = (\<Sum>i\<le>Suc k. coeffs i * vx i) \<and> snd q = (\<Sum>i\<le>Suc k. coeffs i * vy i)"
              using h\<beta>_pos h\<beta>_sum hx hy by (by100 blast)
            thus ?thesis unfolding Q_def by auto
          qed
        qed
      qed
      have hf_cont: "continuous_on ({0..1} \<times> Q k) f"
      proof -
        have "f = (\<lambda>tp. (fst tp * vx (Suc k) + (1 - fst tp) * fst (snd tp),
                         fst tp * vy (Suc k) + (1 - fst tp) * snd (snd tp)))"
          unfolding f_def by (rule ext, simp add: case_prod_beta)
        moreover have "continuous_on ({0..1} \<times> Q k)
            (\<lambda>tp. (fst tp * vx (Suc k) + (1 - fst tp) * fst (snd tp),
                   fst tp * vy (Suc k) + (1 - fst tp) * snd (snd tp)))"
          by (intro continuous_intros)
        ultimately show ?thesis by simp
      qed
      have hdom_compact: "compact ({0..1::real} \<times> Q k)"
        by (rule compact_Times_general[OF compact_Icc hIH])
      show "compact (Q (Suc k))" unfolding hQ_eq
        by (rule compact_continuous_image[OF hf_cont hdom_compact])
    qed
    \<comment> \<open>By induction: Q k is compact for all k.\<close>
    have hQk: "\<And>k. compact (Q k)"
    proof -
      fix k show "compact (Q k)"
        by (induction k) (use hQ0 in simp, use hQstep in simp)
    qed
    \<comment> \<open>P = Q (n-1) (when n \\<ge> 3).\<close>
    have "P = Q (n - 1)"
    proof -
      have "{..<n} = {..n-1}" using hn by (by100 auto)
      hence "(\<forall>i<n. P_cond i) = (\<forall>i\<le>n-1. P_cond i)" for P_cond by (by100 auto)
      moreover have "(\<Sum>i<n. f i) = (\<Sum>i\<le>n-1. f i)" for f :: "nat \<Rightarrow> real"
        using \<open>{..<n} = {..n-1}\<close> by (by100 auto)
      ultimately show ?thesis unfolding hP Q_def by (by100 auto)
    qed
    thus ?thesis using hQk by simp
  qed
  have hP_closed: "closed P" by (rule compact_imp_closed[OF hP_compact_direct])
  \<comment> \<open>Closed subset of compact {-M..M}\\<times>{-M..M} is compact.\<close>
  show "compact P"
    by (rule closed_subset_compact[OF compact_Icc_Times hP_closed hP_bounded])
qed

\<comment> \<open>QUARANTINED: convex\\_polygon\\_homeomorphism is UNUSED and its barycentric/SOME approach
   is wrong for n > 3 (non-unique representations). The correct approach (using
   polygon\\_homeomorphic\\_to\\_disk\\_with\\_boundary) is now implemented directly inside
   scheme\\_quotient\\_uniqueness (per expert audit steps 4-7). This lemma can be deleted.\<close>
\<comment> \<open>convex\\_polygon\\_homeomorphism: REMOVED (unused, wrong barycentric approach for n>3).
   See scheme\\_quotient\\_uniqueness for the correct disk-homeomorphism approach.\<close>

\<comment> \<open>Interior preservation: if \\<phi> maps edge i of P1 to edge i of P2 bijectively,
   then \\<phi> also maps interior points (not on any edge) to interior points.\<close>
lemma edge_preserving_homeo_interior:
  assumes hbij: "bij_betw \<phi> P1 P2"
      and hedge: "\<forall>i<n. \<forall>t\<in>I_set.
          \<phi> ((1-t) * vx1 i + t * vx1 (Suc i mod n),
             (1-t) * vy1 i + t * vy1 (Suc i mod n))
          = ((1-t) * vx2 i + t * vx2 (Suc i mod n),
             (1-t) * vy2 i + t * vy2 (Suc i mod n))"
      and hn3: "n \<ge> 3"
      and hP1_hull: "P1 = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<n. coeffs i) = 1
                     \<and> x = (\<Sum>i<n. coeffs i * vx1 i)
                     \<and> y = (\<Sum>i<n. coeffs i * vy1 i)}"
      and hx: "x \<in> P1"
      and hint: "\<forall>i<n. \<forall>t\<in>I_set.
          x \<noteq> ((1-t) * vx1 i + t * vx1 (Suc i mod n),
                (1-t) * vy1 i + t * vy1 (Suc i mod n))"
  shows "\<forall>i<n. \<forall>t\<in>I_set.
      \<phi> x \<noteq> ((1-t) * vx2 i + t * vx2 (Suc i mod n),
            (1-t) * vy2 i + t * vy2 (Suc i mod n))"
proof (intro allI impI ballI notI)
  fix i t assume hi: "i < n" and ht: "t \<in> I_set"
  assume "(\<phi> x) = ((1-t) * vx2 i + t * vx2 (Suc i mod n),
            (1-t) * vy2 i + t * vy2 (Suc i mod n))"
  \<comment> \<open>But \\<phi>(edge1(i,t)) = edge2(i,t) by hedge. Since \\<phi> is injective, x = edge1(i,t).\<close>
  have h_edge_eq: "\<phi> ((1-t) * vx1 i + t * vx1 (Suc i mod n),
             (1-t) * vy1 i + t * vy1 (Suc i mod n))
        = ((1-t) * vx2 i + t * vx2 (Suc i mod n),
           (1-t) * vy2 i + t * vy2 (Suc i mod n))"
    using hedge[rule_format, OF hi ht] .
  hence "\<phi> x = \<phi> ((1-t) * vx1 i + t * vx1 (Suc i mod n),
                   (1-t) * vy1 i + t * vy1 (Suc i mod n))"
    using \<open>(\<phi> x) = _\<close> by (by100 simp)
  hence "x = ((1-t) * vx1 i + t * vx1 (Suc i mod n),
              (1-t) * vy1 i + t * vy1 (Suc i mod n))"
  proof -
    have "inj_on \<phi> P1" using bij_betw_imp_inj_on[OF hbij] .
    have "((1-t) * vx1 i + t * vx1 (Suc i mod n),
            (1-t) * vy1 i + t * vy1 (Suc i mod n)) \<in> P1"
      by (rule edge_point_in_polygon_witness[OF hn3 hi ht hP1_hull])
    from \<open>inj_on \<phi> P1\<close> hx this \<open>\<phi> x = \<phi> _\<close>
    show ?thesis unfolding inj_on_def by (by100 blast)
  qed
  thus False using hint hi ht by (by100 blast)
qed

lemma cancel_pair_prepend_proper:
  fixes a :: "nat \<times> bool" and w :: "(nat \<times> bool) list"
  assumes "\<forall>label. card {i. i < length w \<and> fst (w ! i) = label} \<in> {0, 2}"
      and "fst a \<notin> fst ` set w"
  shows "\<forall>label. card {i. i < length ([a, top1_inverse_edge a] @ w) \<and>
      fst (([a, top1_inverse_edge a] @ w) ! i) = label} \<in> {0, 2}"
proof (intro allI)
  fix label
  let ?s = "[a, top1_inverse_edge a] @ w"
  show "card {i. i < length ?s \<and> fst (?s ! i) = label} \<in> {0, 2}"
  proof (cases "label = fst a")
    case True
    have "{i. i < length ?s \<and> fst (?s ! i) = label} = {0, 1}"
    proof (rule set_eqI, rule iffI)
      fix i assume "i \<in> {i. i < length ?s \<and> fst (?s ! i) = label}"
      hence hi: "i < length ?s" and hlbl: "fst (?s ! i) = label" by (by100 auto)+
      show "i \<in> {0, 1}"
      proof (cases "i < 2")
        case True hence "i = 0 \<or> i = 1" by (by100 linarith) thus ?thesis by (by100 blast)
      next
        case False hence hi2: "i \<ge> 2" by (by100 linarith)
        define j where "j = i - 2"
        have hj: "i = j + 2" using hi2 j_def by (by100 linarith)
        have "?s ! (j + 2) = w ! j" by (by100 simp)
        hence "?s ! i = w ! j" using hj by (by100 simp)
        moreover have "j < length w" using hi hj by (by100 simp)
        hence "w ! j \<in> set w" by (by100 simp)
        ultimately have hsi_w: "fst (?s ! i) \<in> fst ` set w" by (by100 force)
        have "fst (?s ! i) \<noteq> fst a"
        proof
          assume "fst (?s ! i) = fst a"
          hence "fst a \<in> fst ` set w" using hsi_w by (by100 simp)
          thus False using assms(2) by (by100 blast)
        qed
        thus ?thesis using hlbl True by (by100 simp)
      qed
    next
      fix i assume "i \<in> {0::nat, 1}"
      hence "i = 0 \<or> i = 1" by (by100 blast)
      thus "i \<in> {i. i < length ?s \<and> fst (?s ! i) = label}"
      proof
        assume "i = 0" thus ?thesis using True by (by100 simp)
      next
        assume "i = 1" thus ?thesis using True unfolding top1_inverse_edge_def by (by100 simp)
      qed
    qed
    thus ?thesis by (by100 simp)
  next
    case False
    have "{i. i < length ?s \<and> fst (?s ! i) = label} = {i. \<exists>j<length w. i = j + 2 \<and> fst (w ! j) = label}"
    proof (rule set_eqI, rule iffI)
      fix i assume "i \<in> {i. i < length ?s \<and> fst (?s ! i) = label}"
      hence hi: "i < length ?s" and hlbl: "fst (?s ! i) = label" by (by100 auto)+
      have "i \<ge> 2"
      proof (rule ccontr)
        assume "\<not> i \<ge> 2" hence "i < 2" by (by100 linarith)
        hence "fst (?s ! i) = fst a"
        proof (cases "i = 0")
          case True thus ?thesis by (by100 simp)
        next
          case False2: False hence "i = 1" using \<open>i < 2\<close> by (by100 linarith)
          thus ?thesis unfolding top1_inverse_edge_def by (by100 simp)
        qed
        thus False using hlbl False by (by100 simp)
      qed
      define j where "j = i - 2"
      have "i = j + 2" using \<open>i \<ge> 2\<close> j_def by (by100 linarith)
      have "j < length w" using hi \<open>i = j + 2\<close> by (by100 simp)
      have "?s ! (j + 2) = w ! j" by (by100 simp)
      hence "fst (w ! j) = label" using hlbl \<open>i = j + 2\<close> by (by100 simp)
      show "i \<in> {i. \<exists>j<length w. i = j + 2 \<and> fst (w ! j) = label}"
        using \<open>j < length w\<close> \<open>i = j + 2\<close> \<open>fst (w ! j) = label\<close> by (by100 blast)
    next
      fix i assume "i \<in> {i. \<exists>j<length w. i = j + 2 \<and> fst (w ! j) = label}"
      then obtain j where hj: "j < length w" "i = j + 2" "fst (w ! j) = label" by (by100 blast)
      have "i < length ?s" using hj by (by100 simp)
      have "?s ! (j + 2) = w ! j" by (by100 simp)
      hence "fst (?s ! i) = label" using hj by (by100 simp)
      show "i \<in> {i. i < length ?s \<and> fst (?s ! i) = label}"
        using \<open>i < length ?s\<close> \<open>fst (?s ! i) = label\<close> by (by100 blast)
    qed
    moreover have "card {i. \<exists>j<length w. i = j + 2 \<and> fst (w ! j) = label}
        = card {j. j < length w \<and> fst (w ! j) = label}"
    proof -
      have "bij_betw (\<lambda>j. j + 2) {j. j < length w \<and> fst (w ! j) = label}
                                  {i. \<exists>j<length w. i = j + 2 \<and> fst (w ! j) = label}"
        unfolding bij_betw_def
      proof (intro conjI)
        show "inj_on (\<lambda>j. j + 2) {j. j < length w \<and> fst (w ! j) = label}"
          unfolding inj_on_def by (by100 simp)
        show "(\<lambda>j. j + 2) ` {j. j < length w \<and> fst (w ! j) = label}
            = {i. \<exists>j<length w. i = j + 2 \<and> fst (w ! j) = label}"
          by (by100 force)
      qed
      from bij_betw_same_card[OF this] show ?thesis by (by100 simp)
    qed
    moreover have "card {j. j < length w \<and> fst (w ! j) = label} \<in> {0, 2}"
      using assms(1) by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
qed
end
