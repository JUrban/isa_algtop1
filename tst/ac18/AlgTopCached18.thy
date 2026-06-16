theory AlgTopCached18
  imports "AlgTopCached17.AlgTopCached17"
begin

lemma cramer_injective:
  fixes ex ey fx fy dx1 dy1 dx2 dy2 :: real
  assumes hdet: "ex*fy - ey*fx \<noteq> 0"
      and hs_eq: "(fy*dx1-fx*dy1)/(ex*fy-ey*fx) = (fy*dx2-fx*dy2)/(ex*fy-ey*fx)"
      and ht_eq: "(ex*dy1-ey*dx1)/(ex*fy-ey*fx) = (ex*dy2-ey*dx2)/(ex*fy-ey*fx)"
  shows "dx1 = dx2 \<and> dy1 = dy2"
proof -
  from hs_eq hdet have "fy*dx1-fx*dy1 = fy*dx2-fx*dy2" by simp
  hence heq1: "fy*(dx1-dx2) = fx*(dy1-dy2)" by (by100 algebra)
  from ht_eq hdet have "ex*dy1-ey*dx1 = ex*dy2-ey*dx2" by simp
  hence heq2: "ex*(dy1-dy2) = ey*(dx1-dx2)" by (by100 algebra)
  \<comment> \<open>2x2 system: fy*(dx1-dx2) = fx*(dy1-dy2) and ex*(dy1-dy2) = ey*(dx1-dx2).
     det \\<noteq> 0 \\<Rightarrow> (dx1-dx2, dy1-dy2) = (0, 0).\<close>
  define a where "a = dx1 - dx2"
  define b where "b = dy1 - dy2"
  from heq1 have h1: "fy*a = fx*b" unfolding a_def b_def .
  from heq2 have h2: "ex*b = ey*a" unfolding a_def b_def .
  have "(ex*fy-ey*fx)*a = ex*(fy*a) - ey*(fx*a)" by (by100 algebra)
  also have "ex*(fy*a) = ex*(fx*b)" using h1 by simp
  also have "ey*(fx*a) = fx*(ey*a)" by (by100 algebra)
  also have "fx*(ey*a) = fx*(ex*b)" using h2 by simp
  finally have "(ex*fy-ey*fx)*a = ex*fx*b - fx*ex*b" by (by100 algebra)
  hence "(ex*fy-ey*fx)*a = 0" by (by100 algebra)
  hence ha0: "a = 0" using hdet by simp
  from h1 ha0 have "fx*b = 0" by simp
  from h2 ha0 have "ex*b = 0" by simp
  have "b = 0"
  proof (rule ccontr)
    assume "b \<noteq> 0"
    from \<open>fx*b = 0\<close> \<open>b \<noteq> 0\<close> have "fx = 0" by simp
    from \<open>ex*b = 0\<close> \<open>b \<noteq> 0\<close> have "ex = 0" by simp
    hence "ex*fy - ey*fx = 0" using \<open>fx = 0\<close> by simp
    with hdet show False by simp
  qed
  from ha0 \<open>b = 0\<close> show ?thesis unfolding a_def b_def by auto
qed

lemma triangle_coords_injective:
  fixes ax ay bx by' cx cy sx tx sx' tx' :: real
  assumes hdet: "(ax-cx)*(by'-cy)-(ay-cy)*(bx-cx) \<noteq> 0"
      and hx: "(1-sx-tx)*cx + sx*ax + tx*bx = (1-sx'-tx')*cx + sx'*ax + tx'*bx"
      and hy: "(1-sx-tx)*cy + sx*ay + tx*by' = (1-sx'-tx')*cy + sx'*ay + tx'*by'"
  shows "sx = sx' \<and> tx = tx'"
proof -
  from hx have "(sx-sx')*(ax-cx) + (tx-tx')*(bx-cx) = 0" by (by100 algebra)
  from hy have "(sx-sx')*(ay-cy) + (tx-tx')*(by'-cy) = 0" by (by100 algebra)
  \<comment> \<open>2x2 system with det \\<noteq> 0 \\<Rightarrow> (sx-sx', tx-tx') = (0, 0).\<close>
  define a where "a = sx - sx'"
  define b where "b = tx - tx'"
  from \<open>(sx-sx')*(ax-cx) + (tx-tx')*(bx-cx) = 0\<close> have h1: "a*(ax-cx) + b*(bx-cx) = 0"
    unfolding a_def b_def .
  from \<open>(sx-sx')*(ay-cy) + (tx-tx')*(by'-cy) = 0\<close> have h2: "a*(ay-cy) + b*(by'-cy) = 0"
    unfolding a_def b_def .
  \<comment> \<open>Cramer: a*det = 0, b*det = 0.\<close>
  from h1 have ha_ax: "a*(ax-cx) = -(b*(bx-cx))" by linarith
  from h2 have ha_ay: "a*(ay-cy) = -(b*(by'-cy))" by linarith
  have "a*((ax-cx)*(by'-cy)-(ay-cy)*(bx-cx)) = (a*(ax-cx))*(by'-cy) - (a*(ay-cy))*(bx-cx)"
    by (by100 algebra)
  also have "\<dots> = (-(b*(bx-cx)))*(by'-cy) - (-(b*(by'-cy)))*(bx-cx)"
    using ha_ax ha_ay by simp
  also have "\<dots> = 0" by (by100 algebra)
  finally have "a*((ax-cx)*(by'-cy)-(ay-cy)*(bx-cx)) = 0" .
  hence "a = 0" using hdet by simp
  from h1 \<open>a = 0\<close> have "b*(bx-cx) = 0" by simp
  from h2 \<open>a = 0\<close> have "b*(by'-cy) = 0" by simp
  have "b = 0"
  proof (rule ccontr)
    assume "b \<noteq> 0"
    from \<open>b*(bx-cx) = 0\<close> \<open>b \<noteq> 0\<close> have "bx = cx" by simp
    from \<open>b*(by'-cy) = 0\<close> \<open>b \<noteq> 0\<close> have "by' = cy" by simp
    hence "(ax-cx)*(by'-cy)-(ay-cy)*(bx-cx) = 0" using \<open>bx = cx\<close> by simp
    with hdet show False by simp
  qed
  from \<open>a = 0\<close> \<open>b = 0\<close> show ?thesis unfolding a_def b_def by auto
qed

lemma same_sector_affine_injective:
  fixes ex ey fx fy cx cy ax ay bx by' :: real and x1 y1 x2 y2 :: real
  assumes hdet_s: "ex*fy - ey*fx \<noteq> 0"
      and hdet_t: "(ax-cx)*(by'-cy) - (ay-cy)*(bx-cx) \<noteq> 0"
      and hx_eq: "(let s1 = (fy*(x1-cx)-fx*(y1-cy))/(ex*fy-ey*fx);
                       t1 = (ex*(y1-cy)-ey*(x1-cx))/(ex*fy-ey*fx)
                   in (1-s1-t1)*cx + s1*ax + t1*bx)
                = (let s2 = (fy*(x2-cx)-fx*(y2-cy))/(ex*fy-ey*fx);
                       t2 = (ex*(y2-cy)-ey*(x2-cx))/(ex*fy-ey*fx)
                   in (1-s2-t2)*cx + s2*ax + t2*bx)"
      and hy_eq: "(let s1 = (fy*(x1-cx)-fx*(y1-cy))/(ex*fy-ey*fx);
                       t1 = (ex*(y1-cy)-ey*(x1-cx))/(ex*fy-ey*fx)
                   in (1-s1-t1)*cy + s1*ay + t1*by')
                = (let s2 = (fy*(x2-cx)-fx*(y2-cy))/(ex*fy-ey*fx);
                       t2 = (ex*(y2-cy)-ey*(x2-cx))/(ex*fy-ey*fx)
                   in (1-s2-t2)*cy + s2*ay + t2*by')"
  shows "x1 = x2 \<and> y1 = y2"
proof -
  define s1 where "s1 = (fy*(x1-cx)-fx*(y1-cy))/(ex*fy-ey*fx)"
  define t1 where "t1 = (ex*(y1-cy)-ey*(x1-cx))/(ex*fy-ey*fx)"
  define s2 where "s2 = (fy*(x2-cx)-fx*(y2-cy))/(ex*fy-ey*fx)"
  define t2 where "t2 = (ex*(y2-cy)-ey*(x2-cx))/(ex*fy-ey*fx)"
  from hx_eq have "(1-s1-t1)*cx + s1*ax + t1*bx = (1-s2-t2)*cx + s2*ax + t2*bx"
    unfolding Let_def s1_def t1_def s2_def t2_def by simp
  moreover from hy_eq have "(1-s1-t1)*cy + s1*ay + t1*by' = (1-s2-t2)*cy + s2*ay + t2*by'"
    unfolding Let_def s1_def t1_def s2_def t2_def by simp
  ultimately have "s1 = s2 \<and> t1 = t2"
    by (rule triangle_coords_injective[OF hdet_t])
  hence hs: "s1 = s2" and ht: "t1 = t2" by auto
  from hs have "(fy*(x1-cx)-fx*(y1-cy))/(ex*fy-ey*fx) = (fy*(x2-cx)-fx*(y2-cy))/(ex*fy-ey*fx)"
    unfolding s1_def s2_def .
  moreover from ht have "(ex*(y1-cy)-ey*(x1-cx))/(ex*fy-ey*fx) = (ex*(y2-cy)-ey*(x2-cx))/(ex*fy-ey*fx)"
    unfolding t1_def t2_def .
  ultimately have "(x1-cx) = (x2-cx) \<and> (y1-cy) = (y2-cy)"
    by (rule cramer_injective[OF hdet_s])
  thus ?thesis by auto
qed

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
  have h\<T>_fin: "finite ?\<T>"
  proof -
    have "?\<T> = (\<lambda>i. \<Delta>copy i) ` {..<?m}" by (by100 blast)
    thus ?thesis by simp
  qed
  have h\<T>_ne: "?\<T> \<noteq> {}"
  proof -
    have "\<Delta>copy 0 \<in> ?\<T>" using hm_pos by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  have h\<T>_poly: "\<forall>T \<in> ?\<T>. top1_is_polygonal_region_on T 3"
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
  \<comment> \<open>Infrastructure: disjointness, SOME resolution, inverse translation, h0 range.\<close>
  have h_fst_bound: "\<And>i p. p \<in> \<Delta>copy i \<Longrightarrow> 3 * real i \<le> fst p \<and> fst p \<le> 3 * real i + 1"
  proof -
    fix i :: nat and p :: "real \<times> real" assume "p \<in> \<Delta>copy i"
    then obtain x y where hxy: "(x, y) \<in> top1_standard_simplex" "p = (x + 3 * real i, y)"
      unfolding \<Delta>copy_def by (by100 force)
    have "x \<ge> 0" "x \<le> 1" using hxy(1) unfolding top1_standard_simplex_def by (by100 auto)+
    thus "3 * real i \<le> fst p \<and> fst p \<le> 3 * real i + 1" using hxy(2) by simp
  qed
  have h_disjoint: "\<And>i j. i \<noteq> j \<Longrightarrow> \<Delta>copy i \<inter> \<Delta>copy j = {}"
  proof -
    fix i j :: nat assume hij: "i \<noteq> j"
    show "\<Delta>copy i \<inter> \<Delta>copy j = {}"
    proof (rule ccontr)
      assume "\<Delta>copy i \<inter> \<Delta>copy j \<noteq> {}"
      then obtain p where hp: "p \<in> \<Delta>copy i" "p \<in> \<Delta>copy j" by (by100 blast)
      have "3 * real i \<le> fst p" "fst p \<le> 3 * real i + 1"
        using h_fst_bound[OF hp(1)] by (by100 auto)+
      have "3 * real j \<le> fst p" "fst p \<le> 3 * real j + 1"
        using h_fst_bound[OF hp(2)] by (by100 auto)+
      hence "3 * real i \<le> 3 * real j + 1" "3 * real j \<le> 3 * real i + 1"
        using \<open>3 * real i \<le> fst p\<close> \<open>fst p \<le> 3 * real j + 1\<close>
              \<open>3 * real j \<le> fst p\<close> \<open>fst p \<le> 3 * real i + 1\<close> by linarith+
      hence "real i \<le> real j + 1/3" "real j \<le> real i + 1/3" by linarith+
      hence "\<bar>real i - real j\<bar> \<le> 1/3" by linarith
      hence "i = j" by linarith
      thus False using hij by simp
    qed
  qed
  have h_SOME: "\<And>i p. i < ?m \<Longrightarrow> p \<in> \<Delta>copy i \<Longrightarrow> (SOME j. j < ?m \<and> p \<in> \<Delta>copy j) = i"
  proof -
    fix i :: nat and p assume hi: "i < ?m" and hp: "p \<in> \<Delta>copy i"
    have huniq: "\<And>j. j < ?m \<and> p \<in> \<Delta>copy j \<Longrightarrow> j = i"
    proof -
      fix j assume "j < ?m \<and> p \<in> \<Delta>copy j"
      hence "p \<in> \<Delta>copy j" by simp
      hence "\<Delta>copy i \<inter> \<Delta>copy j \<noteq> {}" using hp by (by100 blast)
      thus "j = i" using h_disjoint by (by100 blast)
    qed
    show "(SOME j. j < ?m \<and> p \<in> \<Delta>copy j) = i"
      by (rule some_equality) (use hi hp huniq in \<open>by100 blast\<close>)+
  qed
  have h_inv_trans: "\<And>i p. p \<in> \<Delta>copy i \<Longrightarrow> (fst p - 3 * real i, snd p) \<in> top1_standard_simplex"
  proof -
    fix i :: nat and p :: "real \<times> real" assume "p \<in> \<Delta>copy i"
    then obtain x y where hxy: "(x, y) \<in> top1_standard_simplex" "p = (x + 3 * real i, y)"
      unfolding \<Delta>copy_def by (by100 force)
    have "fst p - 3 * real i = x" "snd p = y" using hxy(2) by simp+
    thus "(fst p - 3 * real i, snd p) \<in> top1_standard_simplex" using hxy(1) by simp
  qed
  have h_h0_surj: "\<And>i. i < ?m \<Longrightarrow> h0 (tlist ! i) ` top1_standard_simplex = tlist ! i"
  proof -
    fix i assume "i < ?m"
    have "tlist ! i \<in> set tlist" using \<open>i < ?m\<close> by simp
    hence "tlist ! i \<in> \<T>0" using htlist(1) by simp
    hence "top1_homeomorphism_on top1_standard_simplex top1_standard_simplex_topology
        (tlist ! i) (subspace_topology X TX (tlist ! i)) (h0 (tlist ! i))"
      using h\<T>0(3) by (by100 blast)
    hence "bij_betw (h0 (tlist ! i)) top1_standard_simplex (tlist ! i)"
      unfolding top1_homeomorphism_on_def by (by100 blast)
    thus "h0 (tlist ! i) ` top1_standard_simplex = tlist ! i"
      unfolding bij_betw_def by simp
  qed
  have h_qmap_on_copy: "\<And>i p. i < ?m \<Longrightarrow> p \<in> \<Delta>copy i \<Longrightarrow>
      q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
  proof -
    fix i :: nat and p assume "i < ?m" "p \<in> \<Delta>copy i"
    have "(SOME j. j < ?m \<and> p \<in> \<Delta>copy j) = i" using h_SOME[OF \<open>i < ?m\<close> \<open>p \<in> \<Delta>copy i\<close>] .
    thus "q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
      unfolding q_map_def Let_def using \<open>(SOME j. j < ?m \<and> p \<in> \<Delta>copy j) = i\<close> by simp
  qed
  \<comment> \<open>Lift h0 continuity from subspace(X,TX,Ti) to TX.\<close>
  have h_h0_cont_X: "\<And>i. i < ?m \<Longrightarrow> top1_continuous_map_on
      top1_standard_simplex top1_standard_simplex_topology X TX (h0 (tlist ! i))"
  proof -
    fix i assume hi: "i < ?m"
    have "tlist ! i \<in> set tlist" using hi by simp
    hence "tlist ! i \<in> \<T>0" using htlist(1) by simp
    hence hTi_sub: "tlist ! i \<subseteq> X" using h\<T>0(2) by (by100 blast)
    have hhomeo: "top1_homeomorphism_on top1_standard_simplex top1_standard_simplex_topology
        (tlist ! i) (subspace_topology X TX (tlist ! i)) (h0 (tlist ! i))"
      using h\<T>0(3) \<open>tlist ! i \<in> \<T>0\<close> by (by100 blast)
    hence hcont_sub: "top1_continuous_map_on top1_standard_simplex top1_standard_simplex_topology
        (tlist ! i) (subspace_topology X TX (tlist ! i)) (h0 (tlist ! i))"
      unfolding top1_homeomorphism_on_def by (by100 blast)
    show "top1_continuous_map_on top1_standard_simplex top1_standard_simplex_topology X TX (h0 (tlist ! i))"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> top1_standard_simplex"
      have "h0 (tlist ! i) s \<in> tlist ! i"
        using hcont_sub \<open>s \<in> top1_standard_simplex\<close>
        unfolding top1_continuous_map_on_def by (by100 blast)
      thus "h0 (tlist ! i) s \<in> X" using hTi_sub by (by100 blast)
    next
      fix V assume hV: "V \<in> TX"
      have "V \<inter> tlist ! i \<in> subspace_topology X TX (tlist ! i)"
        unfolding subspace_topology_def using hV by (by100 blast)
      hence "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V \<inter> tlist ! i}
          \<in> top1_standard_simplex_topology"
        using hcont_sub unfolding top1_continuous_map_on_def by (by100 blast)
      moreover have "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}
          = {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V \<inter> tlist ! i}"
      proof
        show "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}
            \<subseteq> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V \<inter> tlist ! i}"
        proof
          fix s assume "s \<in> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}"
          hence "s \<in> top1_standard_simplex" "h0 (tlist ! i) s \<in> V" by (by100 auto)+
          moreover have "h0 (tlist ! i) s \<in> tlist ! i"
            using hcont_sub \<open>s \<in> top1_standard_simplex\<close>
            unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "s \<in> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V \<inter> tlist ! i}"
            by (by100 blast)
        qed
      next
        show "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V \<inter> tlist ! i}
            \<subseteq> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}" by (by100 blast)
      qed
      ultimately show "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}
          \<in> top1_standard_simplex_topology" by simp
    qed
  qed
  have h\<T>_cont: "\<forall>T \<in> ?\<T>. top1_continuous_map_on T
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) X TX q_map"
  proof (intro ballI)
    fix T assume "T \<in> ?\<T>"
    then obtain i where hi: "i < ?m" "T = \<Delta>copy i" by (by100 blast)
    show "top1_continuous_map_on T
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) X TX q_map"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix p assume hp: "p \<in> T"
      hence "p \<in> \<Delta>copy i" using hi(2) by simp
      have "q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
        using h_qmap_on_copy[OF hi(1) \<open>p \<in> \<Delta>copy i\<close>] .
      moreover have "(fst p - 3 * real i, snd p) \<in> top1_standard_simplex"
        using h_inv_trans[OF \<open>p \<in> \<Delta>copy i\<close>] .
      ultimately show "q_map p \<in> X"
        using continuous_map_maps_to[OF h_h0_cont_X[OF hi(1)]] by simp
    next
      fix V assume hV: "V \<in> TX"
      \<comment> \<open>Need: {p \\<in> T. q\\_map p \\<in> V} \\<in> subspace R² T.
         This equals {p \\<in> \\<Delta>copy i. h0(tlist!i)(invtrans(p)) \\<in> V}.
         From h0 continuity: {s \\<in> \\<Delta>. h0 s \\<in> V} \\<in> standard\\_simplex\\_topology.
         Translation preserves openness.\<close>
      have hpre_ss: "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}
          \<in> top1_standard_simplex_topology"
        using continuous_map_preimage_open[OF h_h0_cont_X[OF hi(1)] hV] .
      \<comment> \<open>This preimage in standard\\_simplex\\_topology = subspace R² standard\\_simplex.
         So there exists W open in R² with preimage = W \\<inter> standard\\_simplex.\<close>
      then obtain W where hW: "W \<in> product_topology_on top1_open_sets top1_open_sets"
          "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V} = W \<inter> top1_standard_simplex"
        unfolding top1_standard_simplex_topology_def subspace_topology_def by (by100 blast)
      \<comment> \<open>Translate W by (3*i, 0) to get W' open in R².\<close>
      define W' where "W' = (\<lambda>(x,y). (x + 3 * real i, y)) ` W"
      \<comment> \<open>Translation preserves openness in product\\_topology. This is the key step.\<close>
      have hW'_open: "W' \<in> product_topology_on top1_open_sets top1_open_sets"
        unfolding product_topology_on_def topology_generated_by_basis_def
      proof (intro CollectI conjI ballI)
        show "W' \<subseteq> UNIV" by simp
      next
        fix p assume "p \<in> W'"
        then obtain s where hs: "s \<in> W" "p = (\<lambda>(x,y). (x + 3 * real i, y)) s"
          unfolding W'_def by (by100 blast)
        have hW_open: "W \<in> topology_generated_by_basis UNIV (product_basis top1_open_sets top1_open_sets)"
          using hW(1) unfolding product_topology_on_def .
        hence "\<exists>b\<in>product_basis top1_open_sets top1_open_sets. s \<in> b \<and> b \<subseteq> W"
          using \<open>s \<in> W\<close> unfolding topology_generated_by_basis_def by (by100 blast)
        then obtain U0 V0 where hUV: "U0 \<in> top1_open_sets" "V0 \<in> top1_open_sets"
            "s \<in> U0 \<times> V0" "U0 \<times> V0 \<subseteq> W"
          unfolding product_basis_def by (by100 blast)
        define U' where "U' = (\<lambda>x. x + 3 * real i) ` U0"
        have hU'_open: "U' \<in> top1_open_sets"
        proof -
          have "open U0" using hUV(1) unfolding top1_open_sets_def by simp
          have "open ((\<lambda>x::real. x - 3 * real i) -` U0)"
            by (rule open_vimage[OF \<open>open U0\<close>]) (intro continuous_intros)
          moreover have "(\<lambda>x::real. x - 3 * real i) -` U0 = (\<lambda>x. x + 3 * real i) ` U0"
            by (by100 force)
          ultimately have "open ((\<lambda>x. 3 * real i + x) ` U0)"
            by (simp add: add.commute)
          moreover have "(\<lambda>x. 3 * real i + x) ` U0 = U'"
            unfolding U'_def by (by100 force)
          ultimately show ?thesis unfolding top1_open_sets_def by simp
        qed
        have "p \<in> U' \<times> V0"
          using hUV(3) hs(2) unfolding U'_def by (cases s) (by100 force)
        moreover have "U' \<times> V0 \<subseteq> W'"
        proof
          fix q assume "q \<in> U' \<times> V0"
          then obtain u v where "u \<in> U'" "v \<in> V0" "q = (u, v)" by (by100 blast)
          then obtain u0 where "u0 \<in> U0" "u = u0 + 3 * real i"
            unfolding U'_def by (by100 blast)
          hence "(u0, v) \<in> U0 \<times> V0" using \<open>v \<in> V0\<close> by simp
          hence "(u0, v) \<in> W" using hUV(4) by (by100 blast)
          have "q = (\<lambda>(x,y). (x + 3 * real i, y)) (u0, v)"
            using \<open>q = (u, v)\<close> \<open>u = u0 + 3 * real i\<close> by simp
          thus "q \<in> W'" unfolding W'_def using \<open>(u0, v) \<in> W\<close> by (by100 blast)
        qed
        moreover have hU'V0_basis: "U' \<times> V0 \<in> product_basis top1_open_sets top1_open_sets"
          unfolding product_basis_def using hU'_open hUV(2) by (by100 blast)
        ultimately show "\<exists>b\<in>product_basis top1_open_sets top1_open_sets. p \<in> b \<and> b \<subseteq> W'"
          apply (rule_tac bexI[of _ "U' \<times> V0"])
          apply (by100 blast)
          apply assumption
          done
      qed
      \<comment> \<open>{p \\<in> T. q\\_map p \\<in> V} = W' \\<inter> T.\<close>
      have hpre_eq: "{p \<in> T. q_map p \<in> V} = W' \<inter> T"
      proof
        show "{p \<in> T. q_map p \<in> V} \<subseteq> W' \<inter> T"
        proof
          fix p assume hp: "p \<in> {p \<in> T. q_map p \<in> V}"
          hence "p \<in> T" "q_map p \<in> V" by (by100 auto)+
          hence "p \<in> \<Delta>copy i" using hi(2) by simp
          have "(fst p - 3 * real i, snd p) \<in> top1_standard_simplex"
            using h_inv_trans[OF \<open>p \<in> \<Delta>copy i\<close>] .
          moreover have "h0 (tlist ! i) (fst p - 3 * real i, snd p) \<in> V"
            using h_qmap_on_copy[OF hi(1) \<open>p \<in> \<Delta>copy i\<close>] \<open>q_map p \<in> V\<close> by simp
          ultimately have "(fst p - 3 * real i, snd p) \<in> W"
            using hW(2) by (by100 blast)
          have "p = (\<lambda>(x,y). (x + 3 * real i, y)) (fst p - 3 * real i, snd p)" by simp
          hence "p \<in> W'" unfolding W'_def
            using \<open>(fst p - 3 * real i, snd p) \<in> W\<close> by (by100 blast)
          thus "p \<in> W' \<inter> T" using \<open>p \<in> T\<close> by (by100 blast)
        qed
      next
        show "W' \<inter> T \<subseteq> {p \<in> T. q_map p \<in> V}"
        proof
          fix p assume hp: "p \<in> W' \<inter> T"
          hence "p \<in> W'" "p \<in> T" by (by100 auto)+
          hence "p \<in> \<Delta>copy i" using hi(2) by simp
          from \<open>p \<in> W'\<close> obtain s where hs: "s \<in> W" "p = (\<lambda>(x,y). (x + 3 * real i, y)) s"
            unfolding W'_def by (by100 blast)
          have "fst p - 3 * real i = fst s" "snd p = snd s"
            using hs(2) by (cases s, simp)+
          hence hinv: "(fst p - 3 * real i, snd p) = s" by (cases s) simp
          have "s \<in> top1_standard_simplex"
            using h_inv_trans[OF \<open>p \<in> \<Delta>copy i\<close>] hinv by simp
          hence "s \<in> W \<inter> top1_standard_simplex" using \<open>s \<in> W\<close> by simp
          hence "h0 (tlist ! i) s \<in> V" using hW(2) by (by100 blast)
          hence "h0 (tlist ! i) (fst p - 3 * real i, snd p) \<in> V" using hinv by simp
          hence "q_map p \<in> V" using h_qmap_on_copy[OF hi(1) \<open>p \<in> \<Delta>copy i\<close>] by simp
          thus "p \<in> {p \<in> T. q_map p \<in> V}" using \<open>p \<in> T\<close> by (by100 blast)
        qed
      qed
      thus "{p \<in> T. q_map p \<in> V} \<in> subspace_topology UNIV
          (product_topology_on top1_open_sets top1_open_sets) T"
        unfolding subspace_topology_def using hW'_open by (by100 blast)
    qed
  qed
  have h\<T>_cov: "(\<Union>T\<in>?\<T>. q_map ` T) = X"
  proof
    show "(\<Union>T\<in>?\<T>. q_map ` T) \<subseteq> X"
    proof
      fix x assume "x \<in> (\<Union>T\<in>?\<T>. q_map ` T)"
      then obtain T p where hT: "T \<in> ?\<T>" and hp: "p \<in> T" and hx: "x = q_map p" by (by100 blast)
      from hT obtain i where hi: "i < ?m" "T = \<Delta>copy i" by (by100 blast)
      have "q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
        using h_qmap_on_copy[OF hi(1)] hp hi(2) by simp
      moreover have "(fst p - 3 * real i, snd p) \<in> top1_standard_simplex"
        using h_inv_trans hp hi(2) by simp
      ultimately have "x \<in> h0 (tlist ! i) ` top1_standard_simplex" using hx by (by100 blast)
      hence "x \<in> tlist ! i" using h_h0_surj[OF hi(1)] by simp
      moreover have "tlist ! i \<in> set tlist" using hi(1) by simp
      hence "tlist ! i \<in> \<T>0" using htlist(1) by simp
      hence "tlist ! i \<subseteq> X" using h\<T>0(2) by (by100 blast)
      ultimately show "x \<in> X" by (by100 blast)
    qed
  next
    show "X \<subseteq> (\<Union>T\<in>?\<T>. q_map ` T)"
    proof
      fix x assume "x \<in> X"
      hence "x \<in> \<Union>\<T>0" using h\<T>0(2) by simp
      then obtain T0i where hT0i: "T0i \<in> \<T>0" "x \<in> T0i" by (by100 blast)
      have "T0i \<in> set tlist" using hT0i(1) htlist(1) by simp
      then obtain i where hi: "i < ?m" "tlist ! i = T0i"
        by (metis in_set_conv_nth)
      have "x \<in> tlist ! i" using hT0i(2) hi(2) by simp
      hence "x \<in> h0 (tlist ! i) ` top1_standard_simplex" using h_h0_surj[OF hi(1)] by simp
      then obtain s where hs: "s \<in> top1_standard_simplex" "h0 (tlist ! i) s = x" by (by100 blast)
      define p where "p = (fst s + 3 * real i, snd s)"
      have hp_in: "p \<in> \<Delta>copy i"
      proof -
        have "p = (\<lambda>(x,y). (x + 3 * real i, y)) s" unfolding p_def by (cases s) simp
        thus ?thesis unfolding \<Delta>copy_def using hs(1) by (by100 blast)
      qed
      have "fst p - 3 * real i = fst s" "snd p = snd s"
        unfolding p_def by simp+
      hence "q_map p = h0 (tlist ! i) s"
        using h_qmap_on_copy[OF hi(1) hp_in] by simp
      hence "q_map p = x" using hs(2) by simp
      moreover have "\<Delta>copy i \<in> ?\<T>" using hi(1) by (by100 blast)
      ultimately show "x \<in> (\<Union>T\<in>?\<T>. q_map ` T)" using hp_in by (by100 blast)
    qed
  qed
  \<comment> \<open>Key bridge: h0 is an open map (homeomorphism maps opens to opens).\<close>
  have h_h0_open_map: "\<And>i Uo. i < ?m \<Longrightarrow>
      Uo \<in> top1_standard_simplex_topology \<Longrightarrow>
      h0 (tlist ! i) ` Uo \<in> subspace_topology X TX (tlist ! i)"
  proof -
    fix i Uo assume hi: "i < ?m" and hO: "Uo \<in> top1_standard_simplex_topology"
    have "tlist ! i \<in> set tlist" using hi by simp
    hence "tlist ! i \<in> \<T>0" using htlist(1) by simp
    have hhomeo: "top1_homeomorphism_on top1_standard_simplex top1_standard_simplex_topology
        (tlist ! i) (subspace_topology X TX (tlist ! i)) (h0 (tlist ! i))"
      using h\<T>0(3) \<open>tlist ! i \<in> \<T>0\<close> by (by100 blast)
    hence hinv_cont: "top1_continuous_map_on (tlist ! i) (subspace_topology X TX (tlist ! i))
        top1_standard_simplex top1_standard_simplex_topology (inv_into top1_standard_simplex (h0 (tlist ! i)))"
      unfolding top1_homeomorphism_on_def by (by100 blast)
    \<comment> \<open>h0(T) `` O = {b \\<in> T | inv\\_into(h0)(b) \\<in> O} (preimage under inverse).\<close>
    have hbij: "bij_betw (h0 (tlist ! i)) top1_standard_simplex (tlist ! i)"
      using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
    have hinj: "inj_on (h0 (tlist ! i)) top1_standard_simplex"
      using hbij unfolding bij_betw_def by simp
    have hrange: "h0 (tlist ! i) ` top1_standard_simplex = tlist ! i"
      using h_h0_surj[OF hi] .
    have heq: "h0 (tlist ! i) ` Uo = {b \<in> tlist ! i. inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo}"
    proof
      show "h0 (tlist ! i) ` Uo \<subseteq> {b \<in> tlist ! i. inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo}"
      proof
        fix b assume "b \<in> h0 (tlist ! i) ` Uo"
        then obtain s where hs: "s \<in> Uo" "b = h0 (tlist ! i) s" by (by100 blast)
        have "s \<in> top1_standard_simplex" using hO hs(1)
          unfolding top1_standard_simplex_topology_def subspace_topology_def by (by100 blast)
        hence "b \<in> tlist ! i" using hs(2) hrange by (by100 blast)
        moreover have "inv_into top1_standard_simplex (h0 (tlist ! i)) b = s"
          using inv_into_f_f[OF hinj \<open>s \<in> top1_standard_simplex\<close>] hs(2) by simp
        ultimately show "b \<in> {b \<in> tlist ! i. inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo}"
          using hs(1) by (by100 blast)
      qed
    next
      show "{b \<in> tlist ! i. inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo}
          \<subseteq> h0 (tlist ! i) ` Uo"
      proof
        fix b assume "b \<in> {b \<in> tlist ! i. inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo}"
        hence hb: "b \<in> tlist ! i" "inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo" by auto
        have "h0 (tlist ! i) (inv_into top1_standard_simplex (h0 (tlist ! i)) b) = b"
          using f_inv_into_f[of b "h0 (tlist ! i)" top1_standard_simplex] hb(1) hrange by (by100 blast)
        thus "b \<in> h0 (tlist ! i) ` Uo" using hb(2) by (by100 force)
      qed
    qed
    show "h0 (tlist ! i) ` Uo \<in> subspace_topology X TX (tlist ! i)"
      unfolding heq
      using continuous_map_preimage_open[OF hinv_cont hO] .
  qed
  \<comment> \<open>Backward: if preimages open in each \\<Delta>copy, then U \\<in> TX via finite closed cover.\<close>
  have h_X_strict: "is_topology_on_strict X TX"
    using assms(2) unfolding top1_is_triangulable_on_def by (by100 blast)
  have h_X_top: "is_topology_on X TX"
    using h_X_strict by (rule is_topology_on_strict_imp)
  have h\<T>_quot: "\<forall>U. U \<subseteq> X \<longrightarrow>
      (U \<in> TX \<longleftrightarrow> (\<forall>T\<in>?\<T>. {p\<in>T. q_map p \<in> U} \<in>
        subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T))"
  proof (intro allI impI iffI)
    fix U assume hU_sub: "U \<subseteq> X"
    \<comment> \<open>Forward: U \\<in> TX \\<Rightarrow> preimages open (from continuity).\<close>
    assume hU: "U \<in> TX"
    show "\<forall>T\<in>?\<T>. {p\<in>T. q_map p \<in> U} \<in>
        subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T"
      using h\<T>_cont hU unfolding top1_continuous_map_on_def by (by100 blast)
  next
    fix U assume hU_sub: "U \<subseteq> X"
    \<comment> \<open>Backward: preimages open \\<Rightarrow> U \\<in> TX via finite closed cover.\<close>
    assume hpre: "\<forall>T\<in>?\<T>. {p\<in>T. q_map p \<in> U} \<in>
        subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T"
    \<comment> \<open>Step 1: For each i, U \\<inter> tlist!i is open in subspace(X, TX, tlist!i).\<close>
    have hU_open_piece: "\<And>i. i < ?m \<Longrightarrow>
        U \<inter> tlist ! i \<in> subspace_topology X TX (tlist ! i)"
    proof -
      fix i assume hi: "i < ?m"
      have "\<Delta>copy i \<in> ?\<T>" using hi by (by100 blast)
      hence hpre_i: "{p \<in> \<Delta>copy i. q_map p \<in> U} \<in>
          subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (\<Delta>copy i)"
        using hpre by simp
      \<comment> \<open>Translate to standard simplex: {s \\<in> SS. h0(s) \\<in> U} is open in SS\\_top.\<close>
      have "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}
          \<in> top1_standard_simplex_topology"
      proof -
        \<comment> \<open>The preimage in \\<Delta>copy i is open: = W' \\<inter> \\<Delta>copy i for some W' open in R².\<close>
        from hpre_i obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
            "{p \<in> \<Delta>copy i. q_map p \<in> U} = W' \<inter> \<Delta>copy i"
          unfolding subspace_topology_def by (by100 blast)
        \<comment> \<open>Inverse-translate W' to get W open in R², such that preimage in SS = W \\<inter> SS.\<close>
        define W where "W = (\<lambda>(x,y). (x - 3 * real i, y)) ` W'"
        \<comment> \<open>W is open in R² (inverse translation preserves openness, same argument as forward).\<close>
        have hW_open: "W \<in> product_topology_on top1_open_sets top1_open_sets"
          unfolding product_topology_on_def topology_generated_by_basis_def
        proof (intro CollectI conjI ballI)
          show "W \<subseteq> UNIV" by simp
        next
          fix s assume "s \<in> W"
          then obtain p where hp: "p \<in> W'" "s = (\<lambda>(x,y). (x - 3 * real i, y)) p"
            unfolding W_def by (by100 blast)
          from hW'(1) have "W' \<in> topology_generated_by_basis UNIV (product_basis top1_open_sets top1_open_sets)"
            unfolding product_topology_on_def .
          hence "\<exists>b\<in>product_basis top1_open_sets top1_open_sets. p \<in> b \<and> b \<subseteq> W'"
            using hp(1) unfolding topology_generated_by_basis_def by (by100 blast)
          then obtain U0 V0 where hUV: "U0 \<in> top1_open_sets" "V0 \<in> top1_open_sets"
              "p \<in> U0 \<times> V0" "U0 \<times> V0 \<subseteq> W'"
            unfolding product_basis_def by (by100 blast)
          define U0' where "U0' = (\<lambda>x. x - 3 * real i) ` U0"
          have "open U0" using hUV(1) unfolding top1_open_sets_def by simp
          have "(\<lambda>x. x - 3 * real i) ` U0 = (\<lambda>y::real. y + 3 * real i) -` U0"
            by (by100 force)
          moreover have "open ((\<lambda>y::real. y + 3 * real i) -` U0)"
            by (rule open_vimage[OF \<open>open U0\<close>]) (intro continuous_intros)
          ultimately have "open U0'" unfolding U0'_def by simp
          hence hU0'_open: "U0' \<in> top1_open_sets" unfolding top1_open_sets_def by simp
          have "s \<in> U0' \<times> V0"
            using hUV(3) hp(2) unfolding U0'_def by (cases p) (by100 force)
          moreover have "U0' \<times> V0 \<subseteq> W"
          proof
            fix q assume "q \<in> U0' \<times> V0"
            then obtain u v where "u \<in> U0'" "v \<in> V0" "q = (u, v)" by (by100 blast)
            then obtain u0 where "u0 \<in> U0" "u = u0 - 3 * real i"
              unfolding U0'_def by (by100 blast)
            hence "(u0, v) \<in> U0 \<times> V0" using \<open>v \<in> V0\<close> by simp
            hence "(u0, v) \<in> W'" using hUV(4) by (by100 blast)
            have "q = (\<lambda>(x,y). (x - 3 * real i, y)) (u0, v)"
              using \<open>q = (u, v)\<close> \<open>u = u0 - 3 * real i\<close> by simp
            thus "q \<in> W" unfolding W_def using \<open>(u0, v) \<in> W'\<close> by (by100 blast)
          qed
          moreover have hU0'V0_basis: "U0' \<times> V0 \<in> product_basis top1_open_sets top1_open_sets"
            unfolding product_basis_def using hU0'_open hUV(2) by (by100 blast)
          ultimately show "\<exists>b\<in>product_basis top1_open_sets top1_open_sets. s \<in> b \<and> b \<subseteq> W"
            apply (rule_tac bexI[of _ "U0' \<times> V0"])
            apply (by100 blast)
            apply assumption
            done
        qed
        \<comment> \<open>Now: {s \\<in> SS. h0(s) \\<in> U} = W \\<inter> SS.\<close>
        have heq: "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U} = W \<inter> top1_standard_simplex"
        proof
          show "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U} \<subseteq> W \<inter> top1_standard_simplex"
          proof
            fix s assume hs: "s \<in> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}"
            hence "s \<in> top1_standard_simplex" "h0 (tlist ! i) s \<in> U" by auto
            define p where "p = (\<lambda>(x,y). (x + 3 * real i, y)) s"
            have "p \<in> \<Delta>copy i"
            proof -
              have "p = (\<lambda>(x,y). (x + 3 * real i, y)) s" unfolding p_def by simp
              thus ?thesis unfolding \<Delta>copy_def using \<open>s \<in> top1_standard_simplex\<close> by (by100 blast)
            qed
            have "q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
              using h_qmap_on_copy[OF hi \<open>p \<in> \<Delta>copy i\<close>] .
            also have "(fst p - 3 * real i, snd p) = s" unfolding p_def by (cases s) simp
            finally have "q_map p = h0 (tlist ! i) s" .
            hence "q_map p \<in> U" using \<open>h0 (tlist ! i) s \<in> U\<close> by simp
            hence "p \<in> {p \<in> \<Delta>copy i. q_map p \<in> U}" using \<open>p \<in> \<Delta>copy i\<close> by simp
            hence "p \<in> W' \<inter> \<Delta>copy i" using hW'(2) by simp
            hence "p \<in> W'" by simp
            have "s = (\<lambda>(x,y). (x - 3 * real i, y)) p" unfolding p_def by (cases s) simp
            hence "s \<in> W" unfolding W_def using \<open>p \<in> W'\<close> by (by100 blast)
            thus "s \<in> W \<inter> top1_standard_simplex" using \<open>s \<in> top1_standard_simplex\<close> by simp
          qed
        next
          show "W \<inter> top1_standard_simplex \<subseteq> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}"
          proof
            fix s assume hs: "s \<in> W \<inter> top1_standard_simplex"
            hence "s \<in> W" "s \<in> top1_standard_simplex" by auto
            from \<open>s \<in> W\<close> obtain p where hp: "p \<in> W'" "s = (\<lambda>(x,y). (x - 3 * real i, y)) p"
              unfolding W_def by (by100 blast)
            have "fst s + 3 * real i = fst p" "snd s = snd p" using hp(2) by (cases p, simp)+
            hence "p \<in> \<Delta>copy i"
            proof -
              have "p = (\<lambda>(x,y). (x + 3 * real i, y)) s" using hp(2) by (cases s, cases p) simp
              thus ?thesis unfolding \<Delta>copy_def using \<open>s \<in> top1_standard_simplex\<close> by (by100 blast)
            qed
            hence "p \<in> W' \<inter> \<Delta>copy i" using hp(1) by simp
            hence "p \<in> {p \<in> \<Delta>copy i. q_map p \<in> U}" using hW'(2) by simp
            hence "q_map p \<in> U" by simp
            have "q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
              using h_qmap_on_copy[OF hi \<open>p \<in> \<Delta>copy i\<close>] .
            also have "(fst p - 3 * real i, snd p) = s" using hp(2) by (cases p) simp
            finally have "h0 (tlist ! i) s = q_map p" by simp
            hence "h0 (tlist ! i) s \<in> U" using \<open>q_map p \<in> U\<close> by simp
            thus "s \<in> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}"
              using \<open>s \<in> top1_standard_simplex\<close> by simp
          qed
        qed
        show ?thesis unfolding heq top1_standard_simplex_topology_def subspace_topology_def
          using hW_open by (by100 blast)
      qed
      \<comment> \<open>h0 maps this open set to U \\<inter> tlist!i.\<close>
      moreover have "h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}
          = U \<inter> tlist ! i"
      proof
        show "h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}
            \<subseteq> U \<inter> tlist ! i"
          using h_h0_surj[OF hi] by (by100 blast)
      next
        show "U \<inter> tlist ! i
            \<subseteq> h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}"
        proof
          fix x assume "x \<in> U \<inter> tlist ! i"
          hence "x \<in> tlist ! i" "x \<in> U" by auto
          hence "x \<in> h0 (tlist ! i) ` top1_standard_simplex" using h_h0_surj[OF hi] by simp
          then obtain s where "s \<in> top1_standard_simplex" "h0 (tlist ! i) s = x" by (by100 blast)
          thus "x \<in> h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}"
            using \<open>x \<in> U\<close> by (by100 blast)
        qed
      qed
      ultimately show "U \<inter> tlist ! i \<in> subspace_topology X TX (tlist ! i)"
      proof -
        assume h1: "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U} \<in> top1_standard_simplex_topology"
        assume h2: "h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U} = U \<inter> tlist ! i"
        from h_h0_open_map[OF hi h1] have "h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}
            \<in> subspace_topology X TX (tlist ! i)" .
        thus ?thesis using h2 by simp
      qed
    qed
    \<comment> \<open>Step 2: Finite closed cover \\<Rightarrow> U \\<in> TX.\<close>
    \<comment> \<open>X - U is closed: each (tlist!i) - U = (tlist!i) \\<inter> (X-U) is closed in TX.\<close>
    have hcl: "\<And>i. i < ?m \<Longrightarrow> closedin_on X TX (tlist ! i \<inter> (X - U))"
    proof -
      fix i assume hi: "i < ?m"
      have "tlist ! i \<in> set tlist" using hi by simp
      hence "tlist ! i \<in> \<T>0" using htlist(1) by simp
      hence hTi_cl: "closedin_on X TX (tlist ! i)" using h\<T>0(3) by (by100 blast)
      \<comment> \<open>tlist!i - U is closed in subspace(X,TX,tlist!i).\<close>
      have "U \<inter> tlist ! i \<in> subspace_topology X TX (tlist ! i)"
        using hU_open_piece[OF hi] .
      then obtain V where hV: "V \<in> TX" "U \<inter> tlist ! i = V \<inter> tlist ! i"
        unfolding subspace_topology_def by (by100 blast)
      have "tlist ! i \<inter> (X - U) = tlist ! i \<inter> (X - V)"
        using hV(2) by (by100 blast)
      moreover have "closedin_on X TX (tlist ! i \<inter> (X - V))"
      proof -
        have hXV_cl: "closedin_on X TX (X - V)"
          unfolding closedin_on_def
        proof (intro conjI)
          show "X - V \<subseteq> X" by (by100 blast)
          show "X - (X - V) \<in> TX"
          proof -
            have "X - (X - V) = V \<inter> X"
              by (by100 blast)
            also have "V \<inter> X = V"
              using is_topology_on_strict_opens_sub[OF h_X_strict hV(1)] by (by100 blast)
            finally show ?thesis using hV(1) by simp
          qed
        qed
        have hsub: "tlist ! i \<inter> (X - V) \<subseteq> X" using hTi_cl unfolding closedin_on_def by (by100 blast)
        have hcomp: "X - (tlist ! i \<inter> (X - V)) \<in> TX"
        proof -
          have hV_sub: "V \<subseteq> X" using is_topology_on_strict_opens_sub[OF h_X_strict hV(1)] .
          have hXTi: "X - tlist ! i \<in> TX"
            using hTi_cl unfolding closedin_on_def by simp
          have "{X - tlist ! i, V} \<subseteq> TX" using hXTi hV(1) by (by100 blast)
          hence hUn: "\<Union>{X - tlist ! i, V} \<in> TX"
            using h_X_top unfolding is_topology_on_def by (by100 blast)
          have "(X - tlist ! i) \<union> V = X - (tlist ! i \<inter> (X - V))"
            using hV_sub by (by100 blast)
          thus ?thesis using hUn by simp
        qed
        show ?thesis unfolding closedin_on_def using hsub hcomp by (by100 blast)
      qed
      ultimately show "closedin_on X TX (tlist ! i \<inter> (X - U))" by simp
    qed
    have "X - U = (\<Union>i<?m. tlist ! i \<inter> (X - U))"
    proof
      show "X - U \<subseteq> (\<Union>i<length tlist. tlist ! i \<inter> (X - U))"
      proof
        fix x assume "x \<in> X - U"
        hence "x \<in> X" by simp
        hence "x \<in> \<Union>\<T>0" using h\<T>0(2) by simp
        then obtain T where "T \<in> \<T>0" "x \<in> T" by (by100 blast)
        have "T \<in> set tlist" using \<open>T \<in> \<T>0\<close> htlist(1) by simp
        then obtain i where "i < ?m" "tlist ! i = T" by (metis in_set_conv_nth)
        thus "x \<in> (\<Union>i<length tlist. tlist ! i \<inter> (X - U))"
          using \<open>x \<in> T\<close> \<open>x \<in> X - U\<close> by (by100 force)
      qed
    next
      show "(\<Union>i<length tlist. tlist ! i \<inter> (X - U)) \<subseteq> X - U"
        by (by100 blast)
    qed
    hence "closedin_on X TX (X - U)"
    proof -
      have "closedin_on X TX (\<Union>i<?m. tlist ! i \<inter> (X - U))"
      proof -
        have "finite {i. i < ?m}" by simp
        moreover have "\<And>i. i < ?m \<Longrightarrow> closedin_on X TX (tlist ! i \<inter> (X - U))"
          using hcl .
        ultimately have "closedin_on X TX (\<Union>((\<lambda>i. tlist ! i \<inter> (X - U)) ` {..<length tlist}))"
          using closedin_Union_finite[OF h_X_top, of "(\<lambda>i. tlist ! i \<inter> (X - U)) ` {..<length tlist}"]
          by (by100 auto)
        moreover have "(\<Union>((\<lambda>i. tlist ! i \<inter> (X - U)) ` {..<length tlist}))
            = (\<Union>i<?m. tlist ! i \<inter> (X - U))" by (by100 blast)
        ultimately show ?thesis by simp
      qed
      thus ?thesis using \<open>X - U = (\<Union>i<?m. tlist ! i \<inter> (X - U))\<close> by simp
    qed
    hence "X - (X - U) \<in> TX" unfolding closedin_on_def by simp
    moreover have "X - (X - U) = U" using hU_sub by (by100 blast)
    ultimately show "U \<in> TX" by simp
  qed
  show ?thesis
    apply (rule exI[of _ "?\<T>"])
    apply (rule exI[of _ q_map])
    using h\<T>_fin h\<T>_ne h\<T>_poly h\<T>_cont h\<T>_cov h\<T>_quot
    apply (intro conjI)
    apply assumption+
    done
qed

end
