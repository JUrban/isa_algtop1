theory AlgTopCached17
  imports "AlgTopCached16.AlgTopCached16"
begin

lemma sin_sum_minus_sin_add:
  fixes A B :: real
  shows "sin A + sin B - sin(A+B) = 4 * sin(A/2) * sin(B/2) * sin((A+B)/2)"
proof -
  have h1: "sin(A+B) = sin A * cos B + cos A * sin B" by (rule sin_add)
  have hA: "sin A = 2 * sin(A/2) * cos(A/2)"
    using sin_double[of "A/2"] by simp
  have hB: "sin B = 2 * sin(B/2) * cos(B/2)"
    using sin_double[of "B/2"] by simp
  have hcosB: "1 - cos B = 2 * (sin(B/2))^2"
  proof -
    from sin_cos_squared_add[of "B/2"]
    have hsc: "(cos(B/2))^2 = 1 - (sin(B/2))^2" by (simp add: power2_eq_square algebra_simps)
    from cos_double[of "B/2"]
    have "cos(B/2 + B/2) = (cos(B/2))^2 - (sin(B/2))^2" by simp
    hence "cos B = (1 - (sin(B/2))^2) - (sin(B/2))^2" using hsc by simp
    hence "cos B = 1 - 2 * (sin(B/2))^2" by (simp add: power2_eq_square algebra_simps)
    thus ?thesis by linarith
  qed
  have hcosA: "1 - cos A = 2 * (sin(A/2))^2"
  proof -
    from sin_cos_squared_add[of "A/2"]
    have hsc: "(cos(A/2))^2 = 1 - (sin(A/2))^2" by (simp add: power2_eq_square algebra_simps)
    from cos_double[of "A/2"]
    have "cos(A/2 + A/2) = (cos(A/2))^2 - (sin(A/2))^2" by simp
    hence "cos A = (1 - (sin(A/2))^2) - (sin(A/2))^2" using hsc by simp
    hence "cos A = 1 - 2 * (sin(A/2))^2" by (simp add: power2_eq_square algebra_simps)
    thus ?thesis by linarith
  qed
  have "sin A + sin B - sin(A+B) = sin A + sin B - (sin A * cos B + cos A * sin B)"
    using h1 by simp
  also have "\<dots> = sin A * (1 - cos B) + sin B * (1 - cos A)" by (simp add: algebra_simps)
  also have "\<dots> = sin A * (2 * (sin(B/2))^2) + sin B * (2 * (sin(A/2))^2)"
    using hcosB hcosA by simp
  also have "\<dots> = 2 * sin(A/2) * cos(A/2) * (2 * (sin(B/2))^2)
                + 2 * sin(B/2) * cos(B/2) * (2 * (sin(A/2))^2)"
    using hA hB by simp
  also have "\<dots> = 4 * sin(A/2) * sin(B/2) * (cos(A/2) * sin(B/2) + sin(A/2) * cos(B/2))"
    by (simp add: power2_eq_square algebra_simps)
  also have "cos(A/2) * sin(B/2) + sin(A/2) * cos(B/2) = sin(A/2 + B/2)"
    using sin_add[of "A/2" "B/2"] by simp
  also have "A/2 + B/2 = (A+B)/2" by simp
  finally show ?thesis by simp
qed

\<comment> \<open>Fan determinant for the regular polygon on the unit circle.
   For vertices at (cos(2\\<pi>k/n), sin(2\\<pi>k/n)), the determinant
   det(v\\_m-v\\_1, v\\_{n'}-v\\_1) = 4*sin(\\<pi>(m-1)/n)*sin(\\<pi>(n'-m)/n)*sin(\\<pi>(n'-1)/n) > 0.\<close>
lemma fan_det_pos_regular:
  fixes ne :: nat
  assumes hne: "ne \<ge> 5"
  shows "\<forall>m n'. 2 \<le> m \<longrightarrow> m < n' \<longrightarrow> n' < ne \<longrightarrow>
    (cos(2*pi*real m/real ne) - cos(2*pi/real ne)) *
    (sin(2*pi*real n'/real ne) - sin(2*pi/real ne))
  - (sin(2*pi*real m/real ne) - sin(2*pi/real ne)) *
    (cos(2*pi*real n'/real ne) - cos(2*pi/real ne)) > 0"
proof (intro allI impI)
  fix m n' :: nat assume hm: "2 \<le> m" and hmn: "m < n'" and hn: "n' < ne"
  let ?\<alpha> = "2*pi*real m/real ne"
  let ?\<beta> = "2*pi*real n'/real ne"
  let ?\<gamma> = "2*pi/real ne"
  have hdet_trig: "(cos ?\<alpha> - cos ?\<gamma>) * (sin ?\<beta> - sin ?\<gamma>) -
    (sin ?\<alpha> - sin ?\<gamma>) * (cos ?\<beta> - cos ?\<gamma>)
    = sin(?\<beta> - ?\<alpha>) + sin(?\<alpha> - ?\<gamma>) - sin(?\<beta> - ?\<gamma>)"
  proof -
    have "cos ?\<alpha> * sin ?\<beta> - sin ?\<alpha> * cos ?\<beta> = sin(?\<beta> - ?\<alpha>)"
      using sin_diff[of ?\<beta> ?\<alpha>] by (simp add: algebra_simps)
    moreover have "sin ?\<alpha> * cos ?\<gamma> - cos ?\<alpha> * sin ?\<gamma> = sin(?\<alpha> - ?\<gamma>)"
      using sin_diff[of ?\<alpha> ?\<gamma>] by (simp add: algebra_simps)
    moreover have "sin ?\<gamma> * cos ?\<beta> - cos ?\<gamma> * sin ?\<beta> = -sin(?\<beta> - ?\<gamma>)"
      using sin_diff[of ?\<beta> ?\<gamma>] by (simp add: algebra_simps)
    ultimately show ?thesis by (simp add: algebra_simps)
  qed
  let ?A = "?\<alpha> - ?\<gamma>"
  let ?B = "?\<beta> - ?\<alpha>"
  have hne_pos: "real ne > 0" using hne by simp
  have hm1_real: "real(m - 1) = real m - 1" using hm by simp
  have hnm_real: "real(n' - m) = real n' - real m" using hmn by simp
  have hn1_real: "real(n' - 1) = real n' - 1" using hm hmn by simp
  have hA_eq: "?A = 2*pi*real(m-1)/real ne"
    using hne_pos hm1_real by (simp add: field_simps)
  have hB_eq: "?B = 2*pi*real(n'-m)/real ne"
    using hne_pos hnm_real by (simp add: field_simps)
  have hAB_eq: "?A + ?B = ?\<beta> - ?\<gamma>" by simp
  have hAB_eq2: "?\<beta> - ?\<gamma> = 2*pi*real(n'-1)/real ne"
    using hne_pos hn1_real by (simp add: field_simps)
  have "sin ?A + sin ?B - sin(?A+?B) = 4 * sin(?A/2) * sin(?B/2) * sin((?A+?B)/2)"
    by (rule sin_sum_minus_sin_add)
  hence hprod: "sin(?\<alpha>-?\<gamma>) + sin(?\<beta>-?\<alpha>) - sin(?\<beta>-?\<gamma>)
    = 4 * sin(?A/2) * sin(?B/2) * sin((?A+?B)/2)" using hAB_eq by simp
  have hA2_eq: "?A/2 = pi*real(m-1)/real ne" using hA_eq by simp
  have hB2_eq: "?B/2 = pi*real(n'-m)/real ne" using hB_eq by simp
  have hAB2_eq: "(?A+?B)/2 = pi*real(n'-1)/real ne" using hAB_eq hAB_eq2 by simp
  have hsin1: "sin(?A/2) > 0"
  proof -
    have "real(m-1) \<ge> 1" using hm by simp
    hence "pi*real(m-1)/real ne > 0" using pi_gt_zero hne_pos
      by (intro divide_pos_pos mult_pos_pos) linarith+
    moreover have "real(m-1) < real ne" using hmn hn by simp
    hence "pi*real(m-1)/real ne < pi" using pi_gt_zero hne_pos
      by (simp add: field_simps)
    ultimately show ?thesis unfolding hA2_eq using sin_gt_zero by blast
  qed
  have hsin2: "sin(?B/2) > 0"
  proof -
    have "real(n'-m) \<ge> 1" using hmn by simp
    hence "pi*real(n'-m)/real ne > 0" using pi_gt_zero hne_pos
      by (intro divide_pos_pos mult_pos_pos) linarith+
    moreover have "real(n'-m) < real ne" using hn by simp
    hence "pi*real(n'-m)/real ne < pi" using pi_gt_zero hne_pos
      by (simp add: field_simps)
    ultimately show ?thesis unfolding hB2_eq using sin_gt_zero by blast
  qed
  have hsin3: "sin((?A+?B)/2) > 0"
  proof -
    have "real(n'-1) \<ge> 1" using hm hmn by simp
    hence "pi*real(n'-1)/real ne > 0" using pi_gt_zero hne_pos
      by (intro divide_pos_pos mult_pos_pos) linarith+
    moreover have "real(n'-1) < real ne" using hn by simp
    hence "pi*real(n'-1)/real ne < pi" using pi_gt_zero hne_pos
      by (simp add: field_simps)
    ultimately show ?thesis unfolding hAB2_eq using sin_gt_zero by blast
  qed
  from hprod hdet_trig have "(cos ?\<alpha> - cos ?\<gamma>) * (sin ?\<beta> - sin ?\<gamma>) -
    (sin ?\<alpha> - sin ?\<gamma>) * (cos ?\<beta> - cos ?\<gamma>)
    = 4 * sin(?A/2) * sin(?B/2) * sin((?A+?B)/2)" by simp
  moreover have "4 * sin(?A/2) * sin(?B/2) * sin((?A+?B)/2) > 0"
    using hsin1 hsin2 hsin3 by (simp add: mult_pos_pos)
  ultimately show "(cos(2*pi*real m/real ne) - cos(2*pi/real ne)) *
    (sin(2*pi*real n'/real ne) - sin(2*pi/real ne))
  - (sin(2*pi*real m/real ne) - sin(2*pi/real ne)) *
    (cos(2*pi*real n'/real ne) - cos(2*pi/real ne)) > 0"
    by linarith
qed

\<comment> \<open>fan\\_det\\_pos\\_from\\_vertex (general convex polygon version) REMOVED.
   The fan determinant positivity is now proved for the specific regular polygon
   in scheme\\_quotient\\_exists (AlgTopCached15) using the trig formula:
   det = 4*sin(\\<pi>(m-1)/n)*sin(\\<pi>(n'-m)/n)*sin(\\<pi>(n'-1)/n) > 0.
   The general C11-only proof was stuck for 14+ sessions.\<close>

\<comment> \<open>Sector uniqueness helper: if the cross product at direction m of an edge point
   decomposes as (1-t)*A + t*B with A \\<ge> 0, B > 0, t > 0, then the result > 0.\<close>
lemma cross_positive_from_det_bounds:
  fixes A B t :: real
  assumes "A \<ge> 0" "B > 0" "t > 0" "t \<le> 1"
  shows "(1-t)*A + t*B > 0"
proof -
  have "(1-t) \<ge> 0" using assms(4) by linarith
  from mult_nonneg_nonneg[OF this assms(1)] have "(1-t)*A \<ge> 0" .
  from mult_pos_pos[OF assms(3) assms(2)] have "t*B > 0" .
  thus ?thesis using \<open>(1-t)*A \<ge> 0\<close> by linarith
qed

\<comment> \<open>Dual: (1-t)*A + t*B < 0 when A \\<le> 0, B \\<le> 0, one strict, t \\<in> (0,1).\<close>
lemma cross_negative_from_det_bounds:
  fixes A B t :: real
  assumes "A < 0" "B \<le> 0" "t > 0" "t < 1"
  shows "(1-t)*A + t*B < 0"
proof -
  have "1-t > 0" using assms(4) by linarith
  from mult_pos_neg[OF this assms(1)] have "(1-t)*A < 0" .
  have "t*B \<le> 0" using assms(2,3) by (simp add: mult_nonneg_nonpos)
  thus ?thesis using \<open>(1-t)*A < 0\<close> by linarith
qed

\<comment> \<open>Cross-multiplication for fraction equality: a*d = c*b with b,d \\<noteq> 0 implies a/b = c/d.\<close>
lemma frac_eq_from_cross_mult:
  fixes a b c d :: real
  assumes "a * d = c * b" "b \<noteq> 0" "d \<noteq> 0"
  shows "a / b = c / d"
  using assms by (simp add: field_simps)

lemma cyclic_sign_change:
  fixes f :: "nat \<Rightarrow> real" and n :: nat
  assumes "n \<ge> 1"
      and "\<exists>j<n. f j > 0"
      and "\<exists>j<n. f j < 0"
  shows "\<exists>j<n. f j \<ge> 0 \<and> f (Suc j mod n) \<le> 0"
proof -
  define S where "S = {j. j < n \<and> f j \<ge> 0}"
  from assms(2) have "S \<noteq> {}" unfolding S_def by auto
  from assms(3) have hcompl: "{..<n} - S \<noteq> {}" unfolding S_def by auto
  have hS_sub: "S \<subseteq> {..<n}" unfolding S_def by auto
  show ?thesis
  proof (cases "\<exists>j\<in>S. Suc j mod n \<notin> S")
    case True
    then obtain j where "j \<in> S" "Suc j mod n \<notin> S" by auto
    from \<open>j \<in> S\<close> have "j < n" "f j \<ge> 0" unfolding S_def by auto
    from \<open>Suc j mod n \<notin> S\<close> have "f (Suc j mod n) < 0"
    proof -
      assume "Suc j mod n \<notin> S"
      hence "\<not>(Suc j mod n < n \<and> f (Suc j mod n) \<ge> 0)" unfolding S_def by auto
      moreover have "Suc j mod n < n" using assms(1) by simp
      ultimately show ?thesis by linarith
    qed
    from \<open>j < n\<close> \<open>f j \<ge> 0\<close> \<open>f (Suc j mod n) < 0\<close> show ?thesis by (intro exI[of _ j]) auto
  next
    case False
    hence hclosed: "\<forall>j\<in>S. Suc j mod n \<in> S" by auto
    \<comment> \<open>S is closed under Suc mod n and nonempty, so S = {..<n}.\<close>
    have "S = {..<n}"
    proof -
      from \<open>S \<noteq> {}\<close> obtain j0 where "j0 \<in> S" by auto
      hence "j0 < n" unfolding S_def by auto
      \<comment> \<open>Show: for all k < n, (j0 + k) mod n \\<in> S by induction on k.\<close>
      have "\<forall>k. (j0 + k) mod n \<in> S"
      proof
        fix k show "(j0 + k) mod n \<in> S"
        proof (induct k)
          case 0
          have "(j0 + 0) mod n = j0 mod n" by simp
          also have "\<dots> = j0" using \<open>j0 < n\<close> by simp
          finally show ?case using \<open>j0 \<in> S\<close> by simp
        next
          case (Suc k)
          hence hIH: "(j0 + k) mod n \<in> S" .
          have "(j0 + Suc k) mod n = Suc ((j0 + k) mod n) mod n"
            using mod_Suc_eq by (by100 simp)
          from hclosed[rule_format, OF hIH] have "Suc ((j0 + k) mod n) mod n \<in> S" .
          thus ?case using \<open>(j0 + Suc k) mod n = Suc ((j0 + k) mod n) mod n\<close> by simp
        qed
      qed
      hence "\<forall>j<n. j \<in> S"
      proof -
        assume h: "\<forall>k. (j0 + k) mod n \<in> S"
        show "\<forall>j<n. j \<in> S"
        proof (intro allI impI)
          fix j assume hj: "j < n"
          \<comment> \<open>k = (j - j0 + n) mod n gives (j0+k) mod n = j.\<close>
          define k where "k = (j + n - j0) mod n"
          have "j0 + k = j0 + ((j + n - j0) mod n)" unfolding k_def by simp
          \<comment> \<open>j + n - j0 \\<ge> 0 since j \\<ge> 0 and n > j0.\<close>
          have hjn: "j + n \<ge> j0" using \<open>j0 < n\<close> by linarith
          have "(j0 + (j + n - j0) mod n) mod n = (j0 + (j + n - j0)) mod n"
            by (simp add: mod_add_right_eq)
          also have "j0 + (j + n - j0) = j + n" using hjn by linarith
          also have "(j + n) mod n = j mod n" by simp
          also have "\<dots> = j" using hj by simp
          finally have "(j0 + k) mod n = j" unfolding k_def .
          from h[rule_format, of k] this show "j \<in> S" by simp
        qed
      qed
      with hS_sub show "S = {..<n}" by auto
    qed
    hence "{..<n} - S = {}" by simp
    with hcompl show ?thesis by simp
  qed
qed

\<comment> \<open>General lemma: edge cross product is strictly positive at interior points.
   If: (1) all vertex cross products \\<ge> 0 at edge i (from C11);
       (2) p = \\<Sum> \\<mu>\\_k * v\\_k is a convex combination;
       (3) not all nonzero \\<mu>\\_k have v\\_k on edge i (i.e., p is not on edge i);
   then: edge cross at p > 0.
   This abstracts the C11+linearity argument used in both source and target fans.\<close>
lemma convex_combo_edge_cross_strict:
  fixes n :: nat and vx vy :: "nat \<Rightarrow> real" and edge_i :: nat and coeffs :: "nat \<Rightarrow> real"
  assumes hn: "n \<ge> 3" and hi: "edge_i < n"
      and hnn: "\<forall>k<n. coeffs k \<ge> 0"
      and hsum1: "(\<Sum>k<n. coeffs k) = 1"
      and hedge: "\<forall>k<n. k \<noteq> edge_i \<longrightarrow> k \<noteq> Suc edge_i mod n \<longrightarrow>
          (vx(Suc edge_i mod n)-vx edge_i)*(vy k-vy edge_i)-
          (vy(Suc edge_i mod n)-vy edge_i)*(vx k-vx edge_i) > 0"
      and hstrict: "\<exists>k<n. k \<noteq> edge_i \<and> k \<noteq> Suc edge_i mod n \<and> coeffs k > 0"
  shows "(vx(Suc edge_i mod n)-vx edge_i)*((\<Sum>k<n. coeffs k * vy k)-vy edge_i)-
      (vy(Suc edge_i mod n)-vy edge_i)*((\<Sum>k<n. coeffs k * vx k)-vx edge_i) > 0"
proof -
  let ?dx_e = "vx(Suc edge_i mod n)-vx edge_i"
  let ?dy_e = "vy(Suc edge_i mod n)-vy edge_i"
  \<comment> \<open>Step 1: linearity. Edge cross at p = \\<Sum> \\<mu>\\_k * edge\\_cross(v\\_k).\<close>
  have hsy: "(\<Sum>k<n. coeffs k * vy k) - vy edge_i = (\<Sum>k<n. coeffs k * (vy k - vy edge_i))"
  proof -
    have "(\<Sum>k<n. coeffs k * (vy k - vy edge_i)) = (\<Sum>k<n. coeffs k * vy k) - (\<Sum>k<n. coeffs k * vy edge_i)"
    proof -
      have "\<And>k. coeffs k * (vy k - vy edge_i) = coeffs k * vy k - coeffs k * vy edge_i"
        by (by100 algebra)
      hence "(\<Sum>k<n. coeffs k * (vy k - vy edge_i)) = (\<Sum>k<n. (coeffs k * vy k - coeffs k * vy edge_i))" by simp
      also have "\<dots> = (\<Sum>k<n. coeffs k * vy k) - (\<Sum>k<n. coeffs k * vy edge_i)"
        by (rule sum_subtractf)
      finally show ?thesis .
    qed
    also have "(\<Sum>k<n. coeffs k * vy edge_i) = vy edge_i"
    proof -
      have "(\<Sum>k<n. coeffs k * vy edge_i) = (\<Sum>k<n. coeffs k) * vy edge_i"
        by (simp add: sum_distrib_right[symmetric])
      thus ?thesis using hsum1 by simp
    qed
    finally show ?thesis by simp
  qed
  have hsx: "(\<Sum>k<n. coeffs k * vx k) - vx edge_i = (\<Sum>k<n. coeffs k * (vx k - vx edge_i))"
  proof -
    have "(\<Sum>k<n. coeffs k * (vx k - vx edge_i)) = (\<Sum>k<n. coeffs k * vx k) - (\<Sum>k<n. coeffs k * vx edge_i)"
    proof -
      have "\<And>k. coeffs k * (vx k - vx edge_i) = coeffs k * vx k - coeffs k * vx edge_i"
        by (by100 algebra)
      hence "(\<Sum>k<n. coeffs k * (vx k - vx edge_i)) = (\<Sum>k<n. (coeffs k * vx k - coeffs k * vx edge_i))" by simp
      also have "\<dots> = (\<Sum>k<n. coeffs k * vx k) - (\<Sum>k<n. coeffs k * vx edge_i)"
        by (rule sum_subtractf)
      finally show ?thesis .
    qed
    also have "(\<Sum>k<n. coeffs k * vx edge_i) = vx edge_i"
    proof -
      have "(\<Sum>k<n. coeffs k * vx edge_i) = (\<Sum>k<n. coeffs k) * vx edge_i"
        by (simp add: sum_distrib_right[symmetric])
      thus ?thesis using hsum1 by simp
    qed
    finally show ?thesis by simp
  qed
  \<comment> \<open>edge\\_cross(p) = \\<Sum> \\<mu>\\_k * (dx\\_e*(vy k - vy edge\\_i) - dy\\_e*(vx k - vx edge\\_i)).\<close>
  have hlin: "?dx_e*((\<Sum>k<n. coeffs k * vy k)-vy edge_i)-?dy_e*((\<Sum>k<n. coeffs k * vx k)-vx edge_i)
    = (\<Sum>k<n. coeffs k * (?dx_e*(vy k-vy edge_i)-?dy_e*(vx k-vx edge_i)))"
  proof -
    have "?dx_e*(\<Sum>k<n. coeffs k * (vy k-vy edge_i)) = (\<Sum>k<n. ?dx_e*(coeffs k*(vy k-vy edge_i)))"
      by (rule sum_distrib_left)
    moreover have "?dy_e*(\<Sum>k<n. coeffs k * (vx k-vx edge_i)) = (\<Sum>k<n. ?dy_e*(coeffs k*(vx k-vx edge_i)))"
      by (rule sum_distrib_left)
    ultimately have "?dx_e*(\<Sum>k<n. coeffs k * (vy k-vy edge_i))-?dy_e*(\<Sum>k<n. coeffs k * (vx k-vx edge_i))
      = (\<Sum>k<n. ?dx_e*(coeffs k*(vy k-vy edge_i))) - (\<Sum>k<n. ?dy_e*(coeffs k*(vx k-vx edge_i)))" by simp
    also have "\<dots> = (\<Sum>k<n. (?dx_e*(coeffs k*(vy k-vy edge_i)) - ?dy_e*(coeffs k*(vx k-vx edge_i))))"
      by (rule sum_subtractf[symmetric])
    also have "\<dots> = (\<Sum>k<n. coeffs k * (?dx_e*(vy k-vy edge_i)-?dy_e*(vx k-vx edge_i)))"
    proof (rule sum.cong)
      fix k assume "k \<in> {..<n}"
      show "?dx_e*(coeffs k*(vy k-vy edge_i)) - ?dy_e*(coeffs k*(vx k-vx edge_i))
        = coeffs k * (?dx_e*(vy k-vy edge_i)-?dy_e*(vx k-vx edge_i))" by (by100 algebra)
    qed simp
    finally show ?thesis using hsy hsx by simp
  qed
  \<comment> \<open>Step 2: each term \\<ge> 0.\<close>
  have hterms_ge: "\<forall>k<n. coeffs k * (?dx_e*(vy k-vy edge_i)-?dy_e*(vx k-vx edge_i)) \<ge> 0"
  proof (intro allI impI)
    fix k assume hk: "k < n"
    show "coeffs k * (?dx_e*(vy k-vy edge_i)-?dy_e*(vx k-vx edge_i)) \<ge> 0"
    proof (cases "k = edge_i \<or> k = Suc edge_i mod n")
      case True thus ?thesis by (elim disjE) simp_all
    next
      case False hence "k \<noteq> edge_i" "k \<noteq> Suc edge_i mod n" by auto
      from hedge[rule_format, OF hk this]
      have "?dx_e*(vy k-vy edge_i)-?dy_e*(vx k-vx edge_i) > 0" .
      thus ?thesis using hnn[rule_format, OF hk] by (by100 simp)
    qed
  qed
  \<comment> \<open>Step 3: at least one term > 0 (from hstrict).\<close>
  from hstrict obtain k0 where hk0: "k0 < n" "k0 \<noteq> edge_i" "k0 \<noteq> Suc edge_i mod n" "coeffs k0 > 0"
    by auto
  have hk0_pos: "?dx_e*(vy k0-vy edge_i)-?dy_e*(vx k0-vx edge_i) > 0"
    using hedge[rule_format, OF hk0(1) hk0(2) hk0(3)] .
  have hk0_term: "coeffs k0 * (?dx_e*(vy k0-vy edge_i)-?dy_e*(vx k0-vx edge_i)) > 0"
    using hk0(4) hk0_pos by (by100 simp)
  \<comment> \<open>Step 4: sum > 0 (one term > 0, rest \\<ge> 0).\<close>
  have "(\<Sum>k<n. coeffs k * (?dx_e*(vy k-vy edge_i)-?dy_e*(vx k-vx edge_i))) > 0"
  proof -
    have "(\<Sum>k<n. coeffs k * (?dx_e*(vy k-vy edge_i)-?dy_e*(vx k-vx edge_i)))
      = coeffs k0 * (?dx_e*(vy k0-vy edge_i)-?dy_e*(vx k0-vx edge_i))
        + (\<Sum>k\<in>{..<n}-{k0}. coeffs k * (?dx_e*(vy k-vy edge_i)-?dy_e*(vx k-vx edge_i)))"
      using sum.remove[of "{..<n}" k0 "\<lambda>k. coeffs k * (?dx_e*(vy k-vy edge_i)-?dy_e*(vx k-vx edge_i))"]
        hk0(1) by simp
    moreover have "(\<Sum>k\<in>{..<n}-{k0}. coeffs k * (?dx_e*(vy k-vy edge_i)-?dy_e*(vx k-vx edge_i))) \<ge> 0"
      by (rule sum_nonneg) (use hterms_ge in auto)
    ultimately show ?thesis using hk0_term by linarith
  qed
  thus ?thesis using hlin by linarith
qed


end
